import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_31373
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

def inputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000]
def graph : Sig := 0xfffffffffffffffefffefffefefeeca0fffffffffffffffefffefffefefeeca0fffffffffffffffefffefffefefeeca0fffffffffffffffefffefffefefeeca0
theorem graph_proper : proper graph := by unfold proper; decide +kernel
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

def poolCut (u : Bool) (d : Sig) (L k p : Nat) (pool ws : List Sig) :=
  decide (k+p < L+ws.countP (isMaskedConstant d)) && ws.all (availableB u d pool)

theorem poolCut_sound {u raw T d L} (slice : Slice u raw T d L) (cs : List Choice)
    {pool ws cap} (built : makePool u d raw cs = some pool)
    (nd : ws.Nodup) (cut : poolCut u d L cap cs.length pool ws = true) :
    Impossible u T cap ws.toFinset := by
  intro k hk h
  obtain ⟨f,roots,dom,base,nc,lo⟩ := slice
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) base cs built
  simp only [poolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
  obtain ⟨ineq,all⟩ := cut
  have coveredS : supply u bank ((ws.map observe).map (restrictRows f)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
    exact availableB_sound dom hs (List.all_eq_true.mp all a ha)
  have b := projected_bound f (list_run h ws nd rfl) nc hr coveredS lo
  have massLo := count_constants dom ws
  have hu := ineq
  simp only [Nat.zero_add] at b
  omega

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
  (x 0 &&& x 2) ||| (x 1 &&& x 3) ||| (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 2 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 2 &&& x 5) ||| (x 3 &&& x 5) ||| (x 0 &&& x 6) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 5 &&& x 6)
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
  | 0 => 0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001
  | 1 => 0x1000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001
  | 2 => 0x100000000000000010000000000000000000000000000000000000000000000010000000000000001
  | 3 => 0x10000000000000000000000000000000000000000000000000000000000000001
  | 4 => 0x1000000000000000100000000000000010000000000000001
  | 5 => 0x100000000000000000000000000000001
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

abbrev Bits := BitVec 583
abbrev Signals := Bits × Bits
abbrev Decor := Sig × Signals

def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def pairSig (r s : Fin 583 → Row) (a : Sig) : Signals := (ofRows r a,ofRows s a)
def properPairs (T : Sig) (r s : Fin 583 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 583 r s (pairSig r s) := by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩
def faithful (r s : Fin 583 → Row) (x : Decor) := x.2 = pairSig r s x.1
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

def asRow (cols : Nat → Bits) (i : Fin 583) : Row :=
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
theorem asRow_bit (cols : Nat → Bits) (i : Fin 583) (j : Fin 9) :
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
  (x 0 &&& x 2) ||| (x 1 &&& x 3) ||| (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 2 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 2 &&& x 5) ||| (x 3 &&& x 5) ||| (x 0 &&& x 6) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 5 &&& x 6)
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 583) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then v j.val else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · simpa [vertex,hh] using asRow_bit v i j
  · simp [vertex,hh,bit_zero]
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 583) :
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
    if (rs ||| column d z.2) != BitVec.allOnes 583 then true else
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
  have be : ((restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 583) = false := by
    simpa using sep
  change (if (restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 583 then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
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

def lookupWord (nb slots sw vw iw pw : Nat) (data : Nat → Nat) (h : Nat) : Option (Nat × Nat) :=
  let a := h % nb
  let sh := packedAt data (a*sw) sw
  let row := (h/nb+sh) % slots
  let word := packedAt data (nb*sw+row*vw) vw
  if (word >>> (iw+pw)) == h/(nb*slots) % 16 then
    some (word &&& ((1 <<< iw)-1),(word >>> iw) &&& ((1 <<< pw)-1))
  else none

def lookupShort (nb slots sw vw iw pw : Nat) (data : Nat → Nat) (h : Nat) : Option (Nat × Nat) :=
  let a := h % nb
  let sh := packedAt data (a*sw) sw
  let row := (h/nb+sh) % slots
  let word := packedAt data (nb*sw+row*vw) vw
  if (word >>> (iw+pw)) == h/(nb*slots) % 4 then
    some (word &&& ((1 <<< iw)-1),(word >>> iw) &&& ((1 <<< pw)-1))
  else none

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
theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 583) :
    bit (asRow v i) (chartGoal m) = (chartSamples m v).getLsbD i.val := by
  exact bit_liftGoal m v i
theorem chart_pairs {m : Nat} {p q : Nat → Bits}
    (hp : chartSamples m p = BitVec.allOnes 583) (hq : chartSamples m q = 0) :
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
  (chartSamples g.mask (fun j => (g.samples j).1) == BitVec.allOnes 583) &&
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
def g37Y : Array (Bits × Bits) := #[(0x3bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb, 0x7000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0),
    (0x0, 0x0),
    (0x5ddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd, 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00),
    (0x0, 0x0),
    (0x0, 0x0),
    (0x6eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee, 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000),
    (0x0, 0x0)]
def g37C : List ColumnInfo := []
def g37D3 (j : Nat) : Nat := if j = 0 then 0x7 else 0
def g37L : Nat → Packing
  | 3 => (1, 0, 1, 0, 0, 1, 0, g37D3)
  | _ => emptyPacking
def g37I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g37 : Forest := ⟨37, 3, fun i => (g37Y[i]?).getD (0,0), g37C, [[], [82], [32], [32, 82], [80, 82], [80]], g37L, g37I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g37P3n0 : block g37 3 0 1 = true := by decide +kernel
theorem g37B3 : block g37 3 0 1 = true := g37P3n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g37T : checkedTables g37 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g37 0 0 0 = true)
  · exact (rfl : block g37 1 0 0 = true)
  · exact (rfl : block g37 2 0 0 = true)
  · exact g37B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g37G : graphValid g37 (boundsBefore []) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low37 : Lower true (varsX 37) (graphGoal 37) 4 := lower_forest (g:=g37) (i:=0) (hints:=2) (before_sound [] baseKnown) g37G g37T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K37 := extendKnown [] 4 [(37,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V37 : Known true K37 := extend_ok (m:=37) baseKnown low37 (by decide +kernel)

def g42Y : Array (Bits × Bits) := #[(0x0, 0x0),
    (0x3bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb, 0x7000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0),
    (0x0, 0x0),
    (0x5ddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd, 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00),
    (0x0, 0x0),
    (0x6eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee, 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000),
    (0x0, 0x0)]
def g42C : List ColumnInfo := []
def g42D3 (j : Nat) : Nat := if j = 0 then 0x7 else 0
def g42L : Nat → Packing
  | 3 => (1, 0, 1, 0, 0, 1, 0, g42D3)
  | _ => emptyPacking
def g42I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g42 : Forest := ⟨42, 3, fun i => (g42Y[i]?).getD (0,0), g42C, [[], [83], [49], [49, 83], [81, 83], [81]], g42L, g42I⟩
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
theorem g42G : graphValid g42 (boundsBefore K37) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low42 : Lower true (varsX 42) (graphGoal 42) 4 := lower_forest (g:=g42) (i:=0) (hints:=1052720) (before_sound K37 V37) g42G g42T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K42 := extendKnown K37 4 [(42,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V42 : Known true K42 := extend_ok (m:=42) V37 low42 (by decide +kernel)

def g69Y : Array (Bits × Bits) := #[(0x3bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb, 0x7000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0),
    (0x0, 0x0),
    (0x5ddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd, 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00),
    (0x0, 0x0),
    (0x0, 0x0),
    (0x0, 0x0),
    (0x6eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee, 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000)]
def g69C : List ColumnInfo := []
def g69D3 (j : Nat) : Nat := if j = 0 then 0x7 else 0
def g69L : Nat → Packing
  | 3 => (1, 0, 1, 0, 0, 1, 0, g69D3)
  | _ => emptyPacking
def g69I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g69 : Forest := ⟨69, 3, fun i => (g69Y[i]?).getD (0,0), g69C, [[], [98], [32], [32, 98], [96, 98], [96]], g69L, g69I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g69P3n0 : block g69 3 0 1 = true := by decide +kernel
theorem g69B3 : block g69 3 0 1 = true := g69P3n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g69T : checkedTables g69 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g69 0 0 0 = true)
  · exact (rfl : block g69 1 0 0 = true)
  · exact (rfl : block g69 2 0 0 = true)
  · exact g69B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g69G : graphValid g69 (boundsBefore K42) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low69 : Lower true (varsX 69) (graphGoal 69) 4 := lower_forest (g:=g69) (i:=0) (hints:=2) (before_sound K42 V42) g69G g69T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K69 := extendKnown K42 4 [(69,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V69 : Known true K69 := extend_ok (m:=69) V42 low69 (by decide +kernel)

def g74Y : Array (Bits × Bits) := #[(0x0, 0x0),
    (0x3bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb, 0x7000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0),
    (0x0, 0x0),
    (0x5ddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd, 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00),
    (0x0, 0x0),
    (0x0, 0x0),
    (0x6eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee, 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000)]
def g74C : List ColumnInfo := []
def g74D3 (j : Nat) : Nat := if j = 0 then 0x7 else 0
def g74L : Nat → Packing
  | 3 => (1, 0, 1, 0, 0, 1, 0, g74D3)
  | _ => emptyPacking
def g74I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g74 : Forest := ⟨74, 3, fun i => (g74Y[i]?).getD (0,0), g74C, [[], [99], [49], [49, 99], [97, 99], [97]], g74L, g74I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g74P3n0 : block g74 3 0 1 = true := by decide +kernel
theorem g74B3 : block g74 3 0 1 = true := g74P3n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g74T : checkedTables g74 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g74 0 0 0 = true)
  · exact (rfl : block g74 1 0 0 = true)
  · exact (rfl : block g74 2 0 0 = true)
  · exact g74B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g74G : graphValid g74 (boundsBefore K69) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low74 : Lower true (varsX 74) (graphGoal 74) 4 := lower_forest (g:=g74) (i:=0) (hints:=16781360) (before_sound K69 V69) g74G g74T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K74 := extendKnown K69 4 [(74,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V74 : Known true K74 := extend_ok (m:=74) V69 low74 (by decide +kernel)

def g97Y : Array (Bits × Bits) := #[(0x3bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb, 0x7000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0),
    (0x0, 0x0),
    (0x0, 0x0),
    (0x0, 0x0),
    (0x0, 0x0),
    (0x5ddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd, 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00),
    (0x6eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee, 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000)]
def g97C : List ColumnInfo := []
def g97D3 (j : Nat) : Nat := if j = 0 then 0x7 else 0
def g97L : Nat → Packing
  | 3 => (1, 0, 1, 0, 0, 1, 0, g97D3)
  | _ => emptyPacking
def g97I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g97 : Forest := ⟨97, 3, fun i => (g97Y[i]?).getD (0,0), g97C, [[], [101], [80], [80, 101], [96, 101], [96]], g97L, g97I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g97P3n0 : block g97 3 0 1 = true := by decide +kernel
theorem g97B3 : block g97 3 0 1 = true := g97P3n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g97T : checkedTables g97 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g97 0 0 0 = true)
  · exact (rfl : block g97 1 0 0 = true)
  · exact (rfl : block g97 2 0 0 = true)
  · exact g97B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g97G : graphValid g97 (boundsBefore K74) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low97 : Lower true (varsX 97) (graphGoal 97) 4 := lower_forest (g:=g97) (i:=0) (hints:=5) (before_sound K74 V74) g97G g97T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K97 := extendKnown K74 4 [(97,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V97 : Known true K97 := extend_ok (m:=97) V74 low97 (by decide +kernel)

def g98Y : Array (Bits × Bits) := #[(0x0, 0x0),
    (0x3bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb, 0x7000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0),
    (0x0, 0x0),
    (0x0, 0x0),
    (0x0, 0x0),
    (0x5ddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd, 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00),
    (0x6eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee, 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000)]
def g98C : List ColumnInfo := []
def g98D3 (j : Nat) : Nat := if j = 0 then 0x7 else 0
def g98L : Nat → Packing
  | 3 => (1, 0, 1, 0, 0, 1, 0, g98D3)
  | _ => emptyPacking
def g98I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g98 : Forest := ⟨98, 3, fun i => (g98Y[i]?).getD (0,0), g98C, [[], [101], [81], [81, 101], [97, 101], [97]], g98L, g98I⟩
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
theorem g98G : graphValid g98 (boundsBefore K97) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low98 : Lower true (varsX 98) (graphGoal 98) 4 := lower_forest (g:=g98) (i:=0) (hints:=17825872) (before_sound K97 V97) g98G g98T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K98 := extendKnown K97 4 [(98,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V98 : Known true K98 := extend_ok (m:=98) V97 low98 (by decide +kernel)

def g100Y : Array (Bits × Bits) := #[(0x0, 0x0),
    (0x0, 0x0),
    (0x3bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb, 0x7000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0),
    (0x0, 0x0),
    (0x0, 0x0),
    (0x5ddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd, 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00),
    (0x6eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee, 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000)]
def g100C : List ColumnInfo := []
def g100D3 (j : Nat) : Nat := if j = 0 then 0x7 else 0
def g100L : Nat → Packing
  | 3 => (1, 0, 1, 0, 0, 1, 0, g100D3)
  | _ => emptyPacking
def g100I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g100 : Forest := ⟨100, 3, fun i => (g100Y[i]?).getD (0,0), g100C, [[], [101], [82], [82, 101], [98, 101], [98]], g100L, g100I⟩
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

def g104Y : Array (Bits × Bits) := #[(0x0, 0x0),
    (0x0, 0x0),
    (0x0, 0x0),
    (0x3bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb, 0x7000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0),
    (0x0, 0x0),
    (0x5ddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd, 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00),
    (0x6eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee, 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000)]
def g104C : List ColumnInfo := []
def g104D3 (j : Nat) : Nat := if j = 0 then 0x7 else 0
def g104L : Nat → Packing
  | 3 => (1, 0, 1, 0, 0, 1, 0, g104D3)
  | _ => emptyPacking
def g104I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g104 : Forest := ⟨104, 3, fun i => (g104Y[i]?).getD (0,0), g104C, [[], [101], [83], [83, 101], [99, 101], [99]], g104L, g104I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g104P3n0 : block g104 3 0 1 = true := by decide +kernel
theorem g104B3 : block g104 3 0 1 = true := g104P3n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g104T : checkedTables g104 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g104 0 0 0 = true)
  · exact (rfl : block g104 1 0 0 = true)
  · exact (rfl : block g104 2 0 0 = true)
  · exact g104B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g104G : graphValid g104 (boundsBefore K100) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low104 : Lower true (varsX 104) (graphGoal 104) 4 := lower_forest (g:=g104) (i:=0) (hints:=53497856) (before_sound K100 V100) g104G g104T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K104 := extendKnown K100 4 [(104,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V104 : Known true K104 := extend_ok (m:=104) V100 low104 (by decide +kernel)

def g39Y : Array (Bits × Bits) := #[(0x57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57, 0x7f000000000ff803fe000000001ff007fc000000003fe00ff8000000007fc01ff000000000ff803fe000000001ff007fc000000003fe00ff8000000007fc01ff000000000ff803fe00),
    (0x1acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359a, 0x3fe00ffffc0000007fc01ffff8000000ff803ffff0000001ff007fffe0000003fe00ffffc0000007fc01ffff8000000ff803ffff0000001ff007fffe0000003fe00ffffc0000),
    (0x63f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3, 0x3ffff000000000007fffe00000000000ffffc00000000001ffff800000000003ffff000000000007fffe00000000000ffffc00000000001ffff800000000003ffff000000000),
    (0x0, 0x0),
    (0x0, 0x0),
    (0x7cfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fc, 0x7fc0000000000000ff80000000000001ff00000000000003fe00000000000007fc0000000000000ff80000000000001ff00000000000003fe00000000000007fc0000000000000),
    (0x0, 0x0)]
def g39C : List ColumnInfo := [(2,0,37,0,4)]
def g39D4 (j : Nat) : Nat := if j = 0 then 0x2f else 0
def g39L : Nat → Packing
  | 4 => (1, 0, 1, 0, 0, 1, 0, g39D4)
  | _ => emptyPacking
def g39I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g39 : Forest := ⟨39, 4, fun i => (g39Y[i]?).getD (0,0), g39C, [[], [32]], g39L, g39I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g39P4n0 : block g39 4 0 1 = true := by decide +kernel
theorem g39B4 : block g39 4 0 1 = true := g39P4n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g39T : checkedTables g39 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g39 0 0 0 = true)
  · exact (rfl : block g39 1 0 0 = true)
  · exact (rfl : block g39 2 0 0 = true)
  · exact (rfl : block g39 3 0 0 = true)
  · exact g39B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g39G : graphValid g39 (boundsBefore K104) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low39 : Lower true (varsX 39) (graphGoal 39) 5 := lower_forest (g:=g39) (i:=0) (hints:=82) (before_sound K104 V104) g39G g39T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K39 := extendKnown K104 5 [(39,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V39 : Known true K39 := extend_ok (m:=39) V104 low39 (by decide +kernel)

def g43Y : Array (Bits × Bits) := #[(0x56ab55aad56ab55aad56ab55aad56ab55aad56ab55aad56ab55aad56ab55aad56ab55aad56ab55aad56ab55aad56ab55aad56ab55aad56ab55aad56ab55aad56ab55aad56ab55aad56, 0x7f00003fe00ff803fe00007fc01ff007fc0000ff803fe00ff80001ff007fc01ff00003fe00ff803fe00007fc01ff007fc0000ff803fe00ff80001ff007fc01ff00003fe00ff803fe00),
    (0x1bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379b, 0xffffc00000000001ffff800000000003ffff000000000007fffe00000000000ffffc00000000001ffff800000000003ffff000000000007fffe00000000000ffffc0000),
    (0x0, 0x0),
    (0x63f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3, 0x3ffff000000000007fffe00000000000ffffc00000000001ffff800000000003ffff000000000007fffe00000000000ffffc00000000001ffff800000000003ffff000000000),
    (0x0, 0x0),
    (0x7cfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fc, 0x7fc0000000000000ff80000000000001ff00000000000003fe00000000000007fc0000000000000ff80000000000001ff00000000000003fe00000000000007fc0000000000000),
    (0x0, 0x0)]
def g43C : List ColumnInfo := [(1,0,42,0,4)]
def g43D4 (j : Nat) : Nat := if j = 0 then 0x2f else 0
def g43L : Nat → Packing
  | 4 => (1, 0, 1, 0, 0, 1, 0, g43D4)
  | _ => emptyPacking
def g43I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g43 : Forest := ⟨43, 4, fun i => (g43Y[i]?).getD (0,0), g43C, [[], [49]], g43L, g43I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g43P4n0 : block g43 4 0 1 = true := by decide +kernel
theorem g43B4 : block g43 4 0 1 = true := g43P4n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g43T : checkedTables g43 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g43 0 0 0 = true)
  · exact (rfl : block g43 1 0 0 = true)
  · exact (rfl : block g43 2 0 0 = true)
  · exact (rfl : block g43 3 0 0 = true)
  · exact g43B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g43G : graphValid g43 (boundsBefore K39) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low43 : Lower true (varsX 43) (graphGoal 43) 5 := lower_forest (g:=g43) (i:=0) (hints:=4149) (before_sound K39 V39) g43G g43T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K43 := extendKnown K39 5 [(43,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V43 : Known true K43 := extend_ok (m:=43) V39 low43 (by decide +kernel)

def g45Y : Array (Bits × Bits) := #[(0x57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57, 0x7f0000001ff00003fe0000003fe00007fc0000007fc0000ff8000000ff80001ff0000001ff00003fe0000003fe00007fc0000007fc0000ff8000000ff80001ff0000001ff00003fe00),
    (0x0, 0x0),
    (0x1bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379b, 0x3fe00007fc0000007fc0000ff8000000ff80001ff0000001ff00003fe0000003fe00007fc0000007fc0000ff8000000ff80001ff0000001ff00003fe0000003fe00007fc0000),
    (0x62f178bc5e2f178bc5e2f178bc5e2f178bc5e2f178bc5e2f178bc5e2f178bc5e2f178bc5e2f178bc5e2f178bc5e2f178bc5e2f178bc5e2f178bc5e2f178bc5e2f178bc5e2f178bc5e2, 0x3ffffff8000000007ffffff000000000ffffffe000000001ffffffc000000003ffffff8000000007ffffff000000000ffffffe000000001ffffffc000000003ffffff8000000),
    (0x0, 0x0),
    (0x7cfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fc, 0x7fc0000000000000ff80000000000001ff00000000000003fe00000000000007fc0000000000000ff80000000000001ff00000000000003fe00000000000007fc0000000000000),
    (0x0, 0x0)]
def g45C : List ColumnInfo := [(8,0,37,0,4)]
def g45D4 (j : Nat) : Nat := if j = 0 then 0x2f else 0
def g45L : Nat → Packing
  | 4 => (1, 0, 1, 0, 0, 1, 0, g45D4)
  | _ => emptyPacking
def g45I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g45 : Forest := ⟨45, 4, fun i => (g45Y[i]?).getD (0,0), g45C, [[], [32]], g45L, g45I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g45P4n0 : block g45 4 0 1 = true := by decide +kernel
theorem g45B4 : block g45 4 0 1 = true := g45P4n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g45T : checkedTables g45 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g45 0 0 0 = true)
  · exact (rfl : block g45 1 0 0 = true)
  · exact (rfl : block g45 2 0 0 = true)
  · exact (rfl : block g45 3 0 0 = true)
  · exact g45B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g45G : graphValid g45 (boundsBefore K43) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low45 : Lower true (varsX 45) (graphGoal 45) 5 := lower_forest (g:=g45) (i:=0) (hints:=20482) (before_sound K43 V43) g45G g45T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K45 := extendKnown K43 5 [(45,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V45 : Known true K45 := extend_ok (m:=45) V43 low45 (by decide +kernel)

def g46Y : Array (Bits × Bits) := #[(0x0, 0x0),
    (0x57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57, 0x7f000000000ff803fe000000001ff007fc000000003fe00ff8000000007fc01ff000000000ff803fe000000001ff007fc000000003fe00ff8000000007fc01ff000000000ff803fe00),
    (0x1acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359a, 0x3fe00ffffc0000007fc01ffff8000000ff803ffff0000001ff007fffe0000003fe00ffffc0000007fc01ffff8000000ff803ffff0000001ff007fffe0000003fe00ffffc0000),
    (0x63f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3, 0x3ffff000000000007fffe00000000000ffffc00000000001ffff800000000003ffff000000000007fffe00000000000ffffc00000000001ffff800000000003ffff000000000),
    (0x0, 0x0),
    (0x7cfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fc, 0x7fc0000000000000ff80000000000001ff00000000000003fe00000000000007fc0000000000000ff80000000000001ff00000000000003fe00000000000007fc0000000000000),
    (0x0, 0x0)]
def g46C : List ColumnInfo := [(4,0,42,0,4)]
def g46D4 (j : Nat) : Nat := if j = 0 then 0x2f else 0
def g46L : Nat → Packing
  | 4 => (1, 0, 1, 0, 0, 1, 0, g46D4)
  | _ => emptyPacking
def g46I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g46 : Forest := ⟨46, 4, fun i => (g46Y[i]?).getD (0,0), g46C, [[], [49]], g46L, g46I⟩
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
theorem g46G : graphValid g46 (boundsBefore K45) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low46 : Lower true (varsX 46) (graphGoal 46) 5 := lower_forest (g:=g46) (i:=0) (hints:=1054000) (before_sound K45 V45) g46G g46T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K46 := extendKnown K45 5 [(46,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V46 : Known true K46 := extend_ok (m:=46) V45 low46 (by decide +kernel)

def g71Y : Array (Bits × Bits) := #[(0x57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57, 0x7f000000000ff803fe000000001ff007fc000000003fe00ff8000000007fc01ff000000000ff803fe000000001ff007fc000000003fe00ff8000000007fc01ff000000000ff803fe00),
    (0x1acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359a, 0x3fe00ffffc0000007fc01ffff8000000ff803ffff0000001ff007fffe0000003fe00ffffc0000007fc01ffff8000000ff803ffff0000001ff007fffe0000003fe00ffffc0000),
    (0x63f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3, 0x3ffff000000000007fffe00000000000ffffc00000000001ffff800000000003ffff000000000007fffe00000000000ffffc00000000001ffff800000000003ffff000000000),
    (0x0, 0x0),
    (0x0, 0x0),
    (0x0, 0x0),
    (0x7cfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fc, 0x7fc0000000000000ff80000000000001ff00000000000003fe00000000000007fc0000000000000ff80000000000001ff00000000000003fe00000000000007fc0000000000000)]
def g71C : List ColumnInfo := [(2,0,69,0,4)]
def g71D4 (j : Nat) : Nat := if j = 0 then 0x2f else 0
def g71L : Nat → Packing
  | 4 => (1, 0, 1, 0, 0, 1, 0, g71D4)
  | _ => emptyPacking
def g71I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g71 : Forest := ⟨71, 4, fun i => (g71Y[i]?).getD (0,0), g71C, [[], [32]], g71L, g71I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g71P4n0 : block g71 4 0 1 = true := by decide +kernel
theorem g71B4 : block g71 4 0 1 = true := g71P4n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g71T : checkedTables g71 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g71 0 0 0 = true)
  · exact (rfl : block g71 1 0 0 = true)
  · exact (rfl : block g71 2 0 0 = true)
  · exact (rfl : block g71 3 0 0 = true)
  · exact g71B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g71G : graphValid g71 (boundsBefore K46) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low71 : Lower true (varsX 71) (graphGoal 71) 5 := lower_forest (g:=g71) (i:=0) (hints:=98) (before_sound K46 V46) g71G g71T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K71 := extendKnown K46 5 [(71,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V71 : Known true K71 := extend_ok (m:=71) V46 low71 (by decide +kernel)

def g75Y : Array (Bits × Bits) := #[(0x56ab55aad56ab55aad56ab55aad56ab55aad56ab55aad56ab55aad56ab55aad56ab55aad56ab55aad56ab55aad56ab55aad56ab55aad56ab55aad56ab55aad56ab55aad56ab55aad56, 0x7f00003fe00ff803fe00007fc01ff007fc0000ff803fe00ff80001ff007fc01ff00003fe00ff803fe00007fc01ff007fc0000ff803fe00ff80001ff007fc01ff00003fe00ff803fe00),
    (0x1bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379b, 0xffffc00000000001ffff800000000003ffff000000000007fffe00000000000ffffc00000000001ffff800000000003ffff000000000007fffe00000000000ffffc0000),
    (0x0, 0x0),
    (0x63f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3, 0x3ffff000000000007fffe00000000000ffffc00000000001ffff800000000003ffff000000000007fffe00000000000ffffc00000000001ffff800000000003ffff000000000),
    (0x0, 0x0),
    (0x0, 0x0),
    (0x7cfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fc, 0x7fc0000000000000ff80000000000001ff00000000000003fe00000000000007fc0000000000000ff80000000000001ff00000000000003fe00000000000007fc0000000000000)]
def g75C : List ColumnInfo := [(1,0,74,0,4)]
def g75D4 (j : Nat) : Nat := if j = 0 then 0x2f else 0
def g75L : Nat → Packing
  | 4 => (1, 0, 1, 0, 0, 1, 0, g75D4)
  | _ => emptyPacking
def g75I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g75 : Forest := ⟨75, 4, fun i => (g75Y[i]?).getD (0,0), g75C, [[], [49]], g75L, g75I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g75P4n0 : block g75 4 0 1 = true := by decide +kernel
theorem g75B4 : block g75 4 0 1 = true := g75P4n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g75T : checkedTables g75 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g75 0 0 0 = true)
  · exact (rfl : block g75 1 0 0 = true)
  · exact (rfl : block g75 2 0 0 = true)
  · exact (rfl : block g75 3 0 0 = true)
  · exact g75B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g75G : graphValid g75 (boundsBefore K71) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low75 : Lower true (varsX 75) (graphGoal 75) 5 := lower_forest (g:=g75) (i:=0) (hints:=4150) (before_sound K71 V71) g75G g75T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K75 := extendKnown K71 5 [(75,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V75 : Known true K75 := extend_ok (m:=75) V71 low75 (by decide +kernel)

def g77Y : Array (Bits × Bits) := #[(0x57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57, 0x7f0000001ff00003fe0000003fe00007fc0000007fc0000ff8000000ff80001ff0000001ff00003fe0000003fe00007fc0000007fc0000ff8000000ff80001ff0000001ff00003fe00),
    (0x0, 0x0),
    (0x1bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379b, 0x3fe00007fc0000007fc0000ff8000000ff80001ff0000001ff00003fe0000003fe00007fc0000007fc0000ff8000000ff80001ff0000001ff00003fe0000003fe00007fc0000),
    (0x62f178bc5e2f178bc5e2f178bc5e2f178bc5e2f178bc5e2f178bc5e2f178bc5e2f178bc5e2f178bc5e2f178bc5e2f178bc5e2f178bc5e2f178bc5e2f178bc5e2f178bc5e2f178bc5e2, 0x3ffffff8000000007ffffff000000000ffffffe000000001ffffffc000000003ffffff8000000007ffffff000000000ffffffe000000001ffffffc000000003ffffff8000000),
    (0x0, 0x0),
    (0x0, 0x0),
    (0x7cfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fc, 0x7fc0000000000000ff80000000000001ff00000000000003fe00000000000007fc0000000000000ff80000000000001ff00000000000003fe00000000000007fc0000000000000)]
def g77C : List ColumnInfo := [(8,0,69,0,4)]
def g77D4 (j : Nat) : Nat := if j = 0 then 0x2f else 0
def g77L : Nat → Packing
  | 4 => (1, 0, 1, 0, 0, 1, 0, g77D4)
  | _ => emptyPacking
def g77I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g77 : Forest := ⟨77, 4, fun i => (g77Y[i]?).getD (0,0), g77C, [[], [32]], g77L, g77I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g77P4n0 : block g77 4 0 1 = true := by decide +kernel
theorem g77B4 : block g77 4 0 1 = true := g77P4n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g77T : checkedTables g77 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g77 0 0 0 = true)
  · exact (rfl : block g77 1 0 0 = true)
  · exact (rfl : block g77 2 0 0 = true)
  · exact (rfl : block g77 3 0 0 = true)
  · exact g77B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g77G : graphValid g77 (boundsBefore K75) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low77 : Lower true (varsX 77) (graphGoal 77) 5 := lower_forest (g:=g77) (i:=0) (hints:=24578) (before_sound K75 V75) g77G g77T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K77 := extendKnown K75 5 [(77,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V77 : Known true K77 := extend_ok (m:=77) V75 low77 (by decide +kernel)

def g78Y : Array (Bits × Bits) := #[(0x0, 0x0),
    (0x57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57, 0x7f000000000ff803fe000000001ff007fc000000003fe00ff8000000007fc01ff000000000ff803fe000000001ff007fc000000003fe00ff8000000007fc01ff000000000ff803fe00),
    (0x1acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359a, 0x3fe00ffffc0000007fc01ffff8000000ff803ffff0000001ff007fffe0000003fe00ffffc0000007fc01ffff8000000ff803ffff0000001ff007fffe0000003fe00ffffc0000),
    (0x63f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3, 0x3ffff000000000007fffe00000000000ffffc00000000001ffff800000000003ffff000000000007fffe00000000000ffffc00000000001ffff800000000003ffff000000000),
    (0x0, 0x0),
    (0x0, 0x0),
    (0x7cfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fc, 0x7fc0000000000000ff80000000000001ff00000000000003fe00000000000007fc0000000000000ff80000000000001ff00000000000003fe00000000000007fc0000000000000)]
def g78C : List ColumnInfo := [(4,0,74,0,4)]
def g78D4 (j : Nat) : Nat := if j = 0 then 0x2f else 0
def g78L : Nat → Packing
  | 4 => (1, 0, 1, 0, 0, 1, 0, g78D4)
  | _ => emptyPacking
def g78I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g78 : Forest := ⟨78, 4, fun i => (g78Y[i]?).getD (0,0), g78C, [[], [49]], g78L, g78I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g78P4n0 : block g78 4 0 1 = true := by decide +kernel
theorem g78B4 : block g78 4 0 1 = true := g78P4n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g78T : checkedTables g78 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g78 0 0 0 = true)
  · exact (rfl : block g78 1 0 0 = true)
  · exact (rfl : block g78 2 0 0 = true)
  · exact (rfl : block g78 3 0 0 = true)
  · exact g78B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g78G : graphValid g78 (boundsBefore K77) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low78 : Lower true (varsX 78) (graphGoal 78) 5 := lower_forest (g:=g78) (i:=0) (hints:=16782896) (before_sound K77 V77) g78G g78T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K78 := extendKnown K77 5 [(78,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V78 : Known true K78 := extend_ok (m:=78) V77 low78 (by decide +kernel)

def g101Y : Array (Bits × Bits) := #[(0x55bab756eadd5bab756eadd5bab756eadd5bab756eadd5bab756eadd5bab756eadd5bab756eadd5bab756eadd5bab756eadd5bab756eadd5bab756eadd5bab756eadd5bab756eadd5b, 0xffe00000000001ffc00000000003ff800000000007ff00000000000ffe00000000001ffc00000000003ff800000000007ff00000000000ffe00000000001ffc00000000003ff800),
    (0x0, 0x0),
    (0x66dcdb9b736e6dcdb9b736e6dcdb9b736e6dcdb9b736e6dcdb9b736e6dcdb9b736e6dcdb9b736e6dcdb9b736e6dcdb9b736e6dcdb9b736e6dcdb9b736e6dcdb9b736e6dcdb9b736e6d, 0x7ff00000000000ffe00000000001ffc00000000003ff800000000007ff00000000000ffe00000000001ffc00000000003ff800000000007ff00000000000ffe00000000001ffc00000),
    (0x0, 0x0),
    (0x0, 0x0),
    (0x78ef1de3bc778ef1de3bc778ef1de3bc778ef1de3bc778ef1de3bc778ef1de3bc778ef1de3bc778ef1de3bc778ef1de3bc778ef1de3bc778ef1de3bc778ef1de3bc778ef1de3bc778e, 0x7ff00000000000ffe00000000001ffc00000000003ff800000000007ff00000000000ffe00000000001ffc00000000003ff800000000007ff00000000000ffe00000000),
    (0x7f0fe1fc3f87f0fe1fc3f87f0fe1fc3f87f0fe1fc3f87f0fe1fc3f87f0fe1fc3f87f0fe1fc3f87f0fe1fc3f87f0fe1fc3f87f0fe1fc3f87f0fe1fc3f87f0fe1fc3f87f0fe1fc3f87f0, 0x3ff800000000007ff00000000000ffe00000000001ffc00000000003ff800000000007ff00000000000ffe00000000001ffc00000000003ff800000000007ff00000000000)]
def g101C : List ColumnInfo := [(1,0,100,0,4), (4,0,97,0,4), (32,0,69,0,4), (64,0,37,0,4)]
def g101D3 (j : Nat) : Nat := if j = 0 then 0x8028023ea6a1203e11240901 else 0
def g101D4 (j : Nat) : Nat := if j = 0 then 0x6090858702fd0901bd42407e40901 else 0
def g101D5 (j : Nat) : Nat := if j = 0 then 0x1a2047d01 else 0
def g101D6 (j : Nat) : Nat := if j = 0 then 0x7208f else 0
def g101L : Nat → Packing
  | 3 => (2, 3, 2, 0, 0, 5, 0, g101D3)
  | 4 => (3, 2, 2, 0, 0, 5, 0, g101D4)
  | 5 => (1, 1, 2, 0, 0, 1, 0, g101D5)
  | 6 => (1, 0, 2, 0, 0, 1, 0, g101D6)
  | _ => emptyPacking
def g101I : Nat → Nat → Option (Nat × Nat)
  | 4, tag => lookupShort 1 3 1 3 1 0 (fun j => if j=0 then 0x206 else 0) tag
  | 5, tag => lookupShort 4 13 1 7 2 3 (fun j => if j=0 then 0x3cca13100c1600c68 else 0) tag
  | 6, tag => lookupShort 3 13 2 8 1 5 (fun j => if j=0 then 0x3000383186800031000000000602 else 0) tag
  | _, _ => none
def g101 : Forest := ⟨101, 6, fun i => (g101Y[i]?).getD (0,0), g101C, [[], [101], [82], [82, 101], [98, 101], [98], [32], [32, 101], [32, 82], [32, 82, 101], [32, 98, 101], [32, 98], [80, 82], [80, 82, 101], [80], [80, 101], [80, 98], [80, 98, 101], [96, 98, 101], [96, 98], [96, 101], [96], [96, 82, 101], [96, 82]], g101L, g101I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g101P3n0 : block g101 3 0 2 = true := by decide +kernel
theorem g101B3 : block g101 3 0 2 = true := g101P3n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g101P4n0 : block g101 4 0 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g101P4n2 : block g101 4 2 1 = true := by decide +kernel
theorem g101B4 : block g101 4 0 3 = true := (@block_merge g101 4 0 2 1 g101P4n0 g101P4n2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g101P5n0 : block g101 5 0 1 = true := by decide +kernel
theorem g101B5 : block g101 5 0 1 = true := g101P5n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g101P6n0 : block g101 6 0 1 = true := by decide +kernel
theorem g101B6 : block g101 6 0 1 = true := g101P6n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g101T : checkedTables g101 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g101 0 0 0 = true)
  · exact (rfl : block g101 1 0 0 = true)
  · exact (rfl : block g101 2 0 0 = true)
  · exact g101B3
  · exact g101B4
  · exact g101B5
  · exact g101B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g101G : graphValid g101 (boundsBefore K78) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low101 : Lower true (varsX 101) (graphGoal 101) 7 := lower_forest (g:=g101) (i:=0) (hints:=2) (before_sound K78 V78) g101G g101T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K101 := extendKnown K78 7 [(101,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V101 : Known true K101 := extend_ok (m:=101) V78 low101 (by decide +kernel)

def g105Y : Array (Bits × Bits) := #[(0x5ab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6ad, 0xffc00ffc0000000ffc00ffc0000000ffc00ffc0000000ffc00ffc0000000ffc00ffc0000000ffc00ffc0000000ffc00ffc0000000ffc00ffc0000000ffc00ffc0000000ffc00ffc00),
    (0x0, 0x0),
    (0x0, 0x0),
    (0x6cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36, 0xfffff0000000000fffff0000000000fffff0000000000fffff0000000000fffff0000000000fffff0000000000fffff0000000000fffff0000000000fffff0000000000fffff00000),
    (0x0, 0x0),
    (0x7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7, 0x70000000000003ff0000000000003ff0000000000003ff0000000000003ff0000000000003ff0000000000003ff0000000000003ff0000000000003ff0000000000003ff0000000000),
    (0xfe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8, 0xffc000000000000ffc000000000000ffc000000000000ffc000000000000ffc000000000000ffc000000000000ffc000000000000ffc000000000000ffc000000000000)]
def g105C : List ColumnInfo := [(1,0,104,0,4)]
def g105D4 (j : Nat) : Nat := if j = 0 then 0x2f else 0
def g105L : Nat → Packing
  | 4 => (1, 0, 1, 0, 0, 1, 0, g105D4)
  | _ => emptyPacking
def g105I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g105 : Forest := ⟨105, 4, fun i => (g105Y[i]?).getD (0,0), g105C, [[], [101], [48], [48, 101]], g105L, g105I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g105P4n0 : block g105 4 0 1 = true := by decide +kernel
theorem g105B4 : block g105 4 0 1 = true := g105P4n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g105T : checkedTables g105 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g105 0 0 0 = true)
  · exact (rfl : block g105 1 0 0 = true)
  · exact (rfl : block g105 2 0 0 = true)
  · exact (rfl : block g105 3 0 0 = true)
  · exact g105B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g105G : graphValid g105 (boundsBefore K101) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low105 : Lower true (varsX 105) (graphGoal 105) 5 := lower_forest (g:=g105) (i:=0) (hints:=20485) (before_sound K101 V101) g105G g105T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K105 := extendKnown K101 5 [(105,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V105 : Known true K105 := extend_ok (m:=105) V101 low105 (by decide +kernel)

def g106Y : Array (Bits × Bits) := #[(0x0, 0x0),
    (0x55bab756eadd5bab756eadd5bab756eadd5bab756eadd5bab756eadd5bab756eadd5bab756eadd5bab756eadd5bab756eadd5bab756eadd5bab756eadd5bab756eadd5bab756eadd5b, 0xffe00000000001ffc00000000003ff800000000007ff00000000000ffe00000000001ffc00000000003ff800000000007ff00000000000ffe00000000001ffc00000000003ff800),
    (0x0, 0x0),
    (0x66dcdb9b736e6dcdb9b736e6dcdb9b736e6dcdb9b736e6dcdb9b736e6dcdb9b736e6dcdb9b736e6dcdb9b736e6dcdb9b736e6dcdb9b736e6dcdb9b736e6dcdb9b736e6dcdb9b736e6d, 0x7ff00000000000ffe00000000001ffc00000000003ff800000000007ff00000000000ffe00000000001ffc00000000003ff800000000007ff00000000000ffe00000000001ffc00000),
    (0x0, 0x0),
    (0x78ef1de3bc778ef1de3bc778ef1de3bc778ef1de3bc778ef1de3bc778ef1de3bc778ef1de3bc778ef1de3bc778ef1de3bc778ef1de3bc778ef1de3bc778ef1de3bc778ef1de3bc778e, 0x7ff00000000000ffe00000000001ffc00000000003ff800000000007ff00000000000ffe00000000001ffc00000000003ff800000000007ff00000000000ffe00000000),
    (0x7f0fe1fc3f87f0fe1fc3f87f0fe1fc3f87f0fe1fc3f87f0fe1fc3f87f0fe1fc3f87f0fe1fc3f87f0fe1fc3f87f0fe1fc3f87f0fe1fc3f87f0fe1fc3f87f0fe1fc3f87f0fe1fc3f87f0, 0x3ff800000000007ff00000000000ffe00000000001ffc00000000003ff800000000007ff00000000000ffe00000000001ffc00000000003ff800000000007ff00000000000)]
def g106C : List ColumnInfo := [(2,0,104,0,4), (8,0,98,0,4), (32,0,74,0,4), (64,0,42,0,4)]
def g106D3 (j : Nat) : Nat := if j = 0 then 0x8028023ea6a1203e11240901 else 0
def g106D4 (j : Nat) : Nat := if j = 0 then 0x6090858702fd0901bd42407e40901 else 0
def g106D5 (j : Nat) : Nat := if j = 0 then 0x1a2047d01 else 0
def g106D6 (j : Nat) : Nat := if j = 0 then 0x7208f else 0
def g106L : Nat → Packing
  | 3 => (2, 3, 2, 0, 0, 5, 0, g106D3)
  | 4 => (3, 2, 2, 0, 0, 5, 0, g106D4)
  | 5 => (1, 1, 2, 0, 0, 1, 0, g106D5)
  | 6 => (1, 0, 2, 0, 0, 1, 0, g106D6)
  | _ => emptyPacking
def g106I : Nat → Nat → Option (Nat × Nat)
  | 4, tag => lookupShort 1 3 1 3 1 0 (fun j => if j=0 then 0x180 else 0) tag
  | 5, tag => lookupShort 4 16 3 7 2 3 (fun j => if j=0 then 0xd09c00c3940000081e004800000a00 else 0) tag
  | 6, tag => lookupShort 3 9 1 8 1 5 (fun j => if j=0 then 0x70600c00432d00621 else 0) tag
  | _, _ => none
def g106 : Forest := ⟨106, 6, fun i => (g106Y[i]?).getD (0,0), g106C, [[], [101], [83], [83, 101], [99, 101], [99], [49], [49, 101], [49, 83], [49, 83, 101], [49, 99, 101], [49, 99], [81, 83], [81, 83, 101], [81], [81, 101], [81, 99], [81, 99, 101], [97, 99, 101], [97, 99], [97, 101], [97], [97, 83, 101], [97, 83]], g106L, g106I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g106P3n0 : block g106 3 0 2 = true := by decide +kernel
theorem g106B3 : block g106 3 0 2 = true := g106P3n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g106P4n0 : block g106 4 0 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g106P4n2 : block g106 4 2 1 = true := by decide +kernel
theorem g106B4 : block g106 4 0 3 = true := (@block_merge g106 4 0 2 1 g106P4n0 g106P4n2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g106P5n0 : block g106 5 0 1 = true := by decide +kernel
theorem g106B5 : block g106 5 0 1 = true := g106P5n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g106P6n0 : block g106 6 0 1 = true := by decide +kernel
theorem g106B6 : block g106 6 0 1 = true := g106P6n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g106T : checkedTables g106 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g106 0 0 0 = true)
  · exact (rfl : block g106 1 0 0 = true)
  · exact (rfl : block g106 2 0 0 = true)
  · exact g106B3
  · exact g106B4
  · exact g106B5
  · exact g106B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g106G : graphValid g106 (boundsBefore K105) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low106 : Lower true (varsX 106) (graphGoal 106) 7 := lower_forest (g:=g106) (i:=0) (hints:=17829936) (before_sound K105 V105) g106G g106T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K106 := extendKnown K105 7 [(106,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V106 : Known true K106 := extend_ok (m:=106) V105 low106 (by decide +kernel)

def g108Y : Array (Bits × Bits) := #[(0x0, 0x0),
    (0x0, 0x0),
    (0x5ab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6ad, 0xffc00ffc0000000ffc00ffc0000000ffc00ffc0000000ffc00ffc0000000ffc00ffc0000000ffc00ffc0000000ffc00ffc0000000ffc00ffc0000000ffc00ffc0000000ffc00ffc00),
    (0x6cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36, 0xfffff0000000000fffff0000000000fffff0000000000fffff0000000000fffff0000000000fffff0000000000fffff0000000000fffff0000000000fffff0000000000fffff00000),
    (0x0, 0x0),
    (0x7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7, 0x70000000000003ff0000000000003ff0000000000003ff0000000000003ff0000000000003ff0000000000003ff0000000000003ff0000000000003ff0000000000003ff0000000000),
    (0xfe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8, 0xffc000000000000ffc000000000000ffc000000000000ffc000000000000ffc000000000000ffc000000000000ffc000000000000ffc000000000000ffc000000000000)]
def g108C : List ColumnInfo := [(4,0,104,0,4)]
def g108D4 (j : Nat) : Nat := if j = 0 then 0x2f else 0
def g108L : Nat → Packing
  | 4 => (1, 0, 1, 0, 0, 1, 0, g108D4)
  | _ => emptyPacking
def g108I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g108 : Forest := ⟨108, 4, fun i => (g108Y[i]?).getD (0,0), g108C, [[], [101], [50], [50, 101]], g108L, g108I⟩
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

def g47Y : Array (Bits × Bits) := #[(0x2dbaaab6eaaadbaaab6eaaadbaaab6eaaadbaaab6eaaadbaaab6eaaadbaaab6eaaadbaaab6eaaadbaaab6eaaadbaaab6eaaadbaaab6eaaadbaaab6eaaadbaaab6eaaadbaaab6eaaadb, 0xfffffc00000fffffc0000000000000000fffffc0000000000000000fffffc00000fffffc0000000000000000fffffc0000000000000000fffffc00000fffffc00000),
    (0x36ecccdbb3336ecccdbb3336ecccdbb3336ecccdbb3336ecccdbb3336ecccdbb3336ecccdbb3336ecccdbb3336ecccdbb3336ecccdbb3336ecccdbb3336ecccdbb3336ecccdbb3336e, 0xfffffc00000fffffffffff000000000000000000000000000000000fffffc00000fffffffffff000000000000000000000000000000000fffffc00000fffffffffff00000000000),
    (0x473f0f1cfc3c73f0f1cfc3c73f0f1cfc3c73f0f1cfc3c73f0f1cfc3c73f0f1cfc3c73f0f1cfc3c73f0f1cfc3c73f0f1cfc3c73f0f1cfc3c73f0f1cfc3c73f0f1cfc3c73f0f1cfc3c73, 0xfffffffffff0000000000000000000000000003fffff00000000000fffffffffff0000000000000000000000000003fffff00000000000fffffffffff0000000000000000000000),
    (0x7cff01f3fc07cff01f3fc07cff01f3fc07cff01f3fc07cff01f3fc07cff01f3fc07cff01f3fc07cff01f3fc07cff01f3fc07cff01f3fc07cff01f3fc07cff01f3fc07cff01f3fc07c, 0x7ff000000000000000000000000000000000000003ffffffffffffffff000000000000000000000000000000000000003ffffffffffffffff000000000000000000000000000000000),
    (0x0, 0x0),
    (0x780fffe03fff80fffe03fff80fffe03fff80fffe03fff80fffe03fff80fffe03fff80fffe03fff80fffe03fff80fffe03fff80fffe03fff80fffe03fff80fffe03fff80fffe03fff80, 0xfffffc0000000000000000000000000000000000000000000000000fffffc0000000000000000000000000000000000000000000000000),
    (0x0, 0x0)]
def g47C : List ColumnInfo := [(1,0,46,0,5), (2,0,45,0,5), (4,0,43,0,5), (5,0,42,0,4), (8,0,39,0,5), (10,0,37,0,4)]
def g47D4 (j : Nat) : Nat := if j = 0 then 0x31825f63546049b899544066d6215101 else 0
def g47D5 (j : Nat) : Nat := if j = 0 then 0x202204002400800082088208045042db8ae568d01d2a2002faa3027b89504b712a097e15413f408825fd5101bf2a2037d54406f8a880fe41101 else 0
def g47D6 (j : Nat) : Nat := if j = 0 then 0x21d1080c864202ae21d1081101300fe04fd04fd01 else 0
def g47D7 (j : Nat) : Nat := if j = 0 then 0x2c68819f else 0
def g47L : Nat → Packing
  | 4 => (3, 3, 3, 0, 0, 4, 0, g47D4)
  | 5 => (10, 2, 3, 0, 0, 7, 0, g47D5)
  | 6 => (3, 1, 3, 0, 0, 7, 0, g47D6)
  | 7 => (1, 0, 3, 0, 0, 1, 0, g47D7)
  | _ => emptyPacking
def g47I : Nat → Nat → Option (Nat × Nat)
  | 5, tag => lookupShort 3 11 1 6 2 2 (fun j => if j=0 then 0x1800001c0003208010 else 0) tag
  | 6, tag => lookupShort 8 27 2 8 4 2 (fun j => if j=0 then 0x4200c45600d000830046000000121388000060c10000450700c9d90484 else 0) tag
  | 7, tag => lookupShort 6 21 3 7 2 3 (fun j => if j=0 then 0x1148010e99435a6e00c3900000300200003e00 else 0) tag
  | _, _ => none
def g47 : Forest := ⟨47, 7, fun i => (g47Y[i]?).getD (0,0), g47C, [[], [49], [16, 50], [16, 33, 50], [32], [32, 49], [48, 49, 50], [48, 33]], g47L, g47I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g47P4n0 : block g47 4 0 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g47P4n2 : block g47 4 2 1 = true := by decide +kernel
theorem g47B4 : block g47 4 0 3 = true := (@block_merge g47 4 0 2 1 g47P4n0 g47P4n2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g47P5n0 : block g47 5 0 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g47P5n2 : block g47 5 2 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g47P5n4 : block g47 5 4 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g47P5n6 : block g47 5 6 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g47P5n8 : block g47 5 8 2 = true := by decide +kernel
theorem g47B5 : block g47 5 0 10 = true := (@block_merge g47 5 0 4 6 (@block_merge g47 5 0 2 2 g47P5n0 g47P5n2) (@block_merge g47 5 4 2 4 g47P5n4 (@block_merge g47 5 6 2 2 g47P5n6 g47P5n8)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g47P6n0 : block g47 6 0 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g47P6n2 : block g47 6 2 1 = true := by decide +kernel
theorem g47B6 : block g47 6 0 3 = true := (@block_merge g47 6 0 2 1 g47P6n0 g47P6n2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g47P7n0 : block g47 7 0 1 = true := by decide +kernel
theorem g47B7 : block g47 7 0 1 = true := g47P7n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g47T : checkedTables g47 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g47 0 0 0 = true)
  · exact (rfl : block g47 1 0 0 = true)
  · exact (rfl : block g47 2 0 0 = true)
  · exact (rfl : block g47 3 0 0 = true)
  · exact g47B4
  · exact g47B5
  · exact g47B6
  · exact g47B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g47G : graphValid g47 (boundsBefore K108) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low47 : Lower true (varsX 47) (graphGoal 47) 8 := lower_forest (g:=g47) (i:=0) (hints:=4146) (before_sound K108 V108) g47G g47T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K47 := extendKnown K108 8 [(47,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V47 : Known true K47 := extend_ok (m:=47) V108 low47 (by decide +kernel)

def g79Y : Array (Bits × Bits) := #[(0x2dbaaab6eaaadbaaab6eaaadbaaab6eaaadbaaab6eaaadbaaab6eaaadbaaab6eaaadbaaab6eaaadbaaab6eaaadbaaab6eaaadbaaab6eaaadbaaab6eaaadbaaab6eaaadbaaab6eaaadb, 0xfffffc00000fffffc0000000000000000fffffc0000000000000000fffffc00000fffffc0000000000000000fffffc0000000000000000fffffc00000fffffc00000),
    (0x36ecccdbb3336ecccdbb3336ecccdbb3336ecccdbb3336ecccdbb3336ecccdbb3336ecccdbb3336ecccdbb3336ecccdbb3336ecccdbb3336ecccdbb3336ecccdbb3336ecccdbb3336e, 0xfffffc00000fffffffffff000000000000000000000000000000000fffffc00000fffffffffff000000000000000000000000000000000fffffc00000fffffffffff00000000000),
    (0x473f0f1cfc3c73f0f1cfc3c73f0f1cfc3c73f0f1cfc3c73f0f1cfc3c73f0f1cfc3c73f0f1cfc3c73f0f1cfc3c73f0f1cfc3c73f0f1cfc3c73f0f1cfc3c73f0f1cfc3c73f0f1cfc3c73, 0xfffffffffff0000000000000000000000000003fffff00000000000fffffffffff0000000000000000000000000003fffff00000000000fffffffffff0000000000000000000000),
    (0x7cff01f3fc07cff01f3fc07cff01f3fc07cff01f3fc07cff01f3fc07cff01f3fc07cff01f3fc07cff01f3fc07cff01f3fc07cff01f3fc07cff01f3fc07cff01f3fc07cff01f3fc07c, 0x7ff000000000000000000000000000000000000003ffffffffffffffff000000000000000000000000000000000000003ffffffffffffffff000000000000000000000000000000000),
    (0x0, 0x0),
    (0x0, 0x0),
    (0x780fffe03fff80fffe03fff80fffe03fff80fffe03fff80fffe03fff80fffe03fff80fffe03fff80fffe03fff80fffe03fff80fffe03fff80fffe03fff80fffe03fff80fffe03fff80, 0xfffffc0000000000000000000000000000000000000000000000000fffffc0000000000000000000000000000000000000000000000000)]
def g79C : List ColumnInfo := [(1,0,78,0,5), (2,0,77,0,5), (4,0,75,0,5), (5,0,74,0,4), (8,0,71,0,5), (10,0,69,0,4)]
def g79D4 (j : Nat) : Nat := if j = 0 then 0x31825f63546049b899544066d6215101 else 0
def g79D5 (j : Nat) : Nat := if j = 0 then 0x202204002400800082088208045042db8ae568d01d2a2002faa3027b89504b712a097e15413f408825fd5101bf2a2037d54406f8a880fe41101 else 0
def g79D6 (j : Nat) : Nat := if j = 0 then 0x21d1080c864202ae21d1081101300fe04fd04fd01 else 0
def g79D7 (j : Nat) : Nat := if j = 0 then 0x2c68819f else 0
def g79L : Nat → Packing
  | 4 => (3, 3, 3, 0, 0, 4, 0, g79D4)
  | 5 => (10, 2, 3, 0, 0, 7, 0, g79D5)
  | 6 => (3, 1, 3, 0, 0, 7, 0, g79D6)
  | 7 => (1, 0, 3, 0, 0, 1, 0, g79D7)
  | _ => emptyPacking
def g79I : Nat → Nat → Option (Nat × Nat)
  | 5, tag => lookupShort 3 8 1 6 2 2 (fun j => if j=0 then 0x2970c8081 else 0) tag
  | 6, tag => lookupShort 8 24 3 8 4 2 (fun j => if j=0 then 0x8200008352d3c08500c9190008004100c600d016c7e084143202 else 0) tag
  | 7, tag => lookupShort 6 19 2 7 2 3 (fun j => if j=0 then 0x1428804492a4d818402e000004a0003492903 else 0) tag
  | _, _ => none
def g79 : Forest := ⟨79, 7, fun i => (g79Y[i]?).getD (0,0), g79C, [[], [49], [16, 50], [16, 33, 50], [32], [32, 49], [48, 49, 50], [48, 33]], g79L, g79I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g79P4n0 : block g79 4 0 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g79P4n2 : block g79 4 2 1 = true := by decide +kernel
theorem g79B4 : block g79 4 0 3 = true := (@block_merge g79 4 0 2 1 g79P4n0 g79P4n2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g79P5n0 : block g79 5 0 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g79P5n2 : block g79 5 2 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g79P5n4 : block g79 5 4 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g79P5n6 : block g79 5 6 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g79P5n8 : block g79 5 8 2 = true := by decide +kernel
theorem g79B5 : block g79 5 0 10 = true := (@block_merge g79 5 0 4 6 (@block_merge g79 5 0 2 2 g79P5n0 g79P5n2) (@block_merge g79 5 4 2 4 g79P5n4 (@block_merge g79 5 6 2 2 g79P5n6 g79P5n8)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g79P6n0 : block g79 6 0 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g79P6n2 : block g79 6 2 1 = true := by decide +kernel
theorem g79B6 : block g79 6 0 3 = true := (@block_merge g79 6 0 2 1 g79P6n0 g79P6n2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g79P7n0 : block g79 7 0 1 = true := by decide +kernel
theorem g79B7 : block g79 7 0 1 = true := g79P7n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g79T : checkedTables g79 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g79 0 0 0 = true)
  · exact (rfl : block g79 1 0 0 = true)
  · exact (rfl : block g79 2 0 0 = true)
  · exact (rfl : block g79 3 0 0 = true)
  · exact g79B4
  · exact g79B5
  · exact g79B6
  · exact g79B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g79G : graphValid g79 (boundsBefore K47) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low79 : Lower true (varsX 79) (graphGoal 79) 8 := lower_forest (g:=g79) (i:=0) (hints:=4146) (before_sound K47 V47) g79G g79T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K79 := extendKnown K47 8 [(79,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V79 : Known true K79 := extend_ok (m:=79) V47 low79 (by decide +kernel)

def g103Y : Array (Bits × Bits) := #[(0x57aaab57aaab57aaab57aaab57aaab57aaab57aaab57aaab57aaab57aaab57aaab57aaab57aaab57aaab57aaab57aaab57aaab57aaab57aaab57aaab57aaab57aaab57aaab57aaab57, 0xffffff000000ffffff000000000000000000000000000000ffffff000000ffffff000000000000000000000000000000ffffff000000ffffff000000),
    (0x1acccd9acccd9acccd9acccd9acccd9acccd9acccd9acccd9acccd9acccd9acccd9acccd9acccd9acccd9acccd9acccd9acccd9acccd9acccd9acccd9acccd9acccd9acccd9acccd9a, 0xffffff000000ffffffffffff000000000000000000000000ffffff000000ffffffffffff000000000000000000000000ffffff000000ffffffffffff000000000000),
    (0x63f0f1e3f0f1e3f0f1e3f0f1e3f0f1e3f0f1e3f0f1e3f0f1e3f0f1e3f0f1e3f0f1e3f0f1e3f0f1e3f0f1e3f0f1e3f0f1e3f0f1e3f0f1e3f0f1e3f0f1e3f0f1e3f0f1e3f0f1e3f0f1e3, 0xffffffffffff000000000000000000000000000000000000ffffffffffff000000000000000000000000000000000000ffffffffffff000000000000000000000000),
    (0x0, 0x0),
    (0x0, 0x0),
    (0x7cff01fcff01fcff01fcff01fcff01fcff01fcff01fcff01fcff01fcff01fcff01fcff01fcff01fcff01fcff01fcff01fcff01fcff01fcff01fcff01fcff01fcff01fcff01fcff01fc, 0xffffff000000000000000000000000000000000000000000ffffff000000000000000000000000000000000000000000ffffff000000000000000000000000000000000000),
    (0xfffe00fffe00fffe00fffe00fffe00fffe00fffe00fffe00fffe00fffe00fffe00fffe00fffe00fffe00fffe00fffe00fffe00fffe00fffe00fffe00fffe00fffe00fffe00fffe00, 0xffffff000000000000000000000000000000000000000000ffffff000000000000000000000000000000000000000000ffffff000000000000000000000000000000000000000000)]
def g103C : List ColumnInfo := [(2,0,101,0,7)]
def g103D7 (j : Nat) : Nat := if j = 0 then 0x5f else 0
def g103L : Nat → Packing
  | 7 => (1, 0, 1, 0, 0, 1, 0, g103D7)
  | _ => emptyPacking
def g103I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g103 : Forest := ⟨103, 7, fun i => (g103Y[i]?).getD (0,0), g103C, [[], [101], [32], [32, 101]], g103L, g103I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g103P7n0 : block g103 7 0 1 = true := by decide +kernel
theorem g103B7 : block g103 7 0 1 = true := g103P7n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g103T : checkedTables g103 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g103 0 0 0 = true)
  · exact (rfl : block g103 1 0 0 = true)
  · exact (rfl : block g103 2 0 0 = true)
  · exact (rfl : block g103 3 0 0 = true)
  · exact (rfl : block g103 4 0 0 = true)
  · exact (rfl : block g103 5 0 0 = true)
  · exact (rfl : block g103 6 0 0 = true)
  · exact g103B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g103G : graphValid g103 (boundsBefore K79) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low103 : Lower true (varsX 103) (graphGoal 103) 8 := lower_forest (g:=g103) (i:=0) (hints:=82) (before_sound K79 V79) g103G g103T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K103 := extendKnown K79 8 [(103,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V103 : Known true K103 := extend_ok (m:=103) V79 low103 (by decide +kernel)

def g107Y : Array (Bits × Bits) := #[(0x56aaab56aaab56aaab56aaab56aaab56aaab56aaab56aaab56aaab56aaab56aaab56aaab56aaab56aaab56aaab56aaab56aaab56aaab56aaab56aaab56aaab56aaab56aaab56aaab56, 0xffffff000000ffffff000000ffffff000000000000000000ffffff000000ffffff000000ffffff000000000000000000ffffff000000ffffff000000ffffff000000),
    (0x1bcccd9bcccd9bcccd9bcccd9bcccd9bcccd9bcccd9bcccd9bcccd9bcccd9bcccd9bcccd9bcccd9bcccd9bcccd9bcccd9bcccd9bcccd9bcccd9bcccd9bcccd9bcccd9bcccd9bcccd9b, 0xffffffffffff000000000000000000000000000000000000ffffffffffff000000000000000000000000000000000000ffffffffffff000000000000),
    (0x0, 0x0),
    (0x63f0f1e3f0f1e3f0f1e3f0f1e3f0f1e3f0f1e3f0f1e3f0f1e3f0f1e3f0f1e3f0f1e3f0f1e3f0f1e3f0f1e3f0f1e3f0f1e3f0f1e3f0f1e3f0f1e3f0f1e3f0f1e3f0f1e3f0f1e3f0f1e3, 0xffffffffffff000000000000000000000000000000000000ffffffffffff000000000000000000000000000000000000ffffffffffff000000000000000000000000),
    (0x0, 0x0),
    (0x7cff01fcff01fcff01fcff01fcff01fcff01fcff01fcff01fcff01fcff01fcff01fcff01fcff01fcff01fcff01fcff01fcff01fcff01fcff01fcff01fcff01fcff01fcff01fcff01fc, 0xffffff000000000000000000000000000000000000000000ffffff000000000000000000000000000000000000000000ffffff000000000000000000000000000000000000),
    (0xfffe00fffe00fffe00fffe00fffe00fffe00fffe00fffe00fffe00fffe00fffe00fffe00fffe00fffe00fffe00fffe00fffe00fffe00fffe00fffe00fffe00fffe00fffe00fffe00, 0xffffff000000000000000000000000000000000000000000ffffff000000000000000000000000000000000000000000ffffff000000000000000000000000000000000000000000)]
def g107C : List ColumnInfo := [(1,0,106,0,7)]
def g107D7 (j : Nat) : Nat := if j = 0 then 0x5f else 0
def g107L : Nat → Packing
  | 7 => (1, 0, 1, 0, 0, 1, 0, g107D7)
  | _ => emptyPacking
def g107I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g107 : Forest := ⟨107, 7, fun i => (g107Y[i]?).getD (0,0), g107C, [[], [101], [49], [49, 101]], g107L, g107I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g107P7n0 : block g107 7 0 1 = true := by decide +kernel
theorem g107B7 : block g107 7 0 1 = true := g107P7n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g107T : checkedTables g107 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g107 0 0 0 = true)
  · exact (rfl : block g107 1 0 0 = true)
  · exact (rfl : block g107 2 0 0 = true)
  · exact (rfl : block g107 3 0 0 = true)
  · exact (rfl : block g107 4 0 0 = true)
  · exact (rfl : block g107 5 0 0 = true)
  · exact (rfl : block g107 6 0 0 = true)
  · exact g107B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g107G : graphValid g107 (boundsBefore K103) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low107 : Lower true (varsX 107) (graphGoal 107) 8 := lower_forest (g:=g107) (i:=0) (hints:=4149) (before_sound K103 V103) g107G g107T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K107 := extendKnown K103 8 [(107,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V107 : Known true K107 := extend_ok (m:=107) V103 low107 (by decide +kernel)

def g109Y : Array (Bits × Bits) := #[(0x57aaab57aaab57aaab57aaab57aaab57aaab57aaab57aaab57aaab57aaab57aaab57aaab57aaab57aaab57aaab57aaab57aaab57aaab57aaab57aaab57aaab57aaab57aaab57aaab57, 0xffffff000000000000ffffff000000000000000000000000ffffff000000000000ffffff000000000000000000000000ffffff000000000000ffffff000000),
    (0x0, 0x0),
    (0x1bcccd9bcccd9bcccd9bcccd9bcccd9bcccd9bcccd9bcccd9bcccd9bcccd9bcccd9bcccd9bcccd9bcccd9bcccd9bcccd9bcccd9bcccd9bcccd9bcccd9bcccd9bcccd9bcccd9bcccd9b, 0xffffff000000000000ffffff000000000000000000000000ffffff000000000000ffffff000000000000000000000000ffffff000000000000ffffff000000000000),
    (0x62f0f1e2f0f1e2f0f1e2f0f1e2f0f1e2f0f1e2f0f1e2f0f1e2f0f1e2f0f1e2f0f1e2f0f1e2f0f1e2f0f1e2f0f1e2f0f1e2f0f1e2f0f1e2f0f1e2f0f1e2f0f1e2f0f1e2f0f1e2f0f1e2, 0xffffffffffffffffff000000000000000000000000000000ffffffffffffffffff000000000000000000000000000000ffffffffffffffffff000000000000000000),
    (0x0, 0x0),
    (0x7cff01fcff01fcff01fcff01fcff01fcff01fcff01fcff01fcff01fcff01fcff01fcff01fcff01fcff01fcff01fcff01fcff01fcff01fcff01fcff01fcff01fcff01fcff01fcff01fc, 0xffffff000000000000000000000000000000000000000000ffffff000000000000000000000000000000000000000000ffffff000000000000000000000000000000000000),
    (0xfffe00fffe00fffe00fffe00fffe00fffe00fffe00fffe00fffe00fffe00fffe00fffe00fffe00fffe00fffe00fffe00fffe00fffe00fffe00fffe00fffe00fffe00fffe00fffe00, 0xffffff000000000000000000000000000000000000000000ffffff000000000000000000000000000000000000000000ffffff000000000000000000000000000000000000000000)]
def g109C : List ColumnInfo := [(8,0,101,0,7)]
def g109D7 (j : Nat) : Nat := if j = 0 then 0x5f else 0
def g109L : Nat → Packing
  | 7 => (1, 0, 1, 0, 0, 1, 0, g109D7)
  | _ => emptyPacking
def g109I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g109 : Forest := ⟨109, 7, fun i => (g109Y[i]?).getD (0,0), g109C, [[], [101], [32], [32, 101]], g109L, g109I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g109P7n0 : block g109 7 0 1 = true := by decide +kernel
theorem g109B7 : block g109 7 0 1 = true := g109P7n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g109T : checkedTables g109 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g109 0 0 0 = true)
  · exact (rfl : block g109 1 0 0 = true)
  · exact (rfl : block g109 2 0 0 = true)
  · exact (rfl : block g109 3 0 0 = true)
  · exact (rfl : block g109 4 0 0 = true)
  · exact (rfl : block g109 5 0 0 = true)
  · exact (rfl : block g109 6 0 0 = true)
  · exact g109B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g109G : graphValid g109 (boundsBefore K107) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low109 : Lower true (varsX 109) (graphGoal 109) 8 := lower_forest (g:=g109) (i:=0) (hints:=20482) (before_sound K107 V107) g109G g109T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K109 := extendKnown K107 8 [(109,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V109 : Known true K109 := extend_ok (m:=109) V107 low109 (by decide +kernel)

def g110Y : Array (Bits × Bits) := #[(0x0, 0x0),
    (0x57aaab57aaab57aaab57aaab57aaab57aaab57aaab57aaab57aaab57aaab57aaab57aaab57aaab57aaab57aaab57aaab57aaab57aaab57aaab57aaab57aaab57aaab57aaab57aaab57, 0xffffff000000ffffff000000000000000000000000000000ffffff000000ffffff000000000000000000000000000000ffffff000000ffffff000000),
    (0x1acccd9acccd9acccd9acccd9acccd9acccd9acccd9acccd9acccd9acccd9acccd9acccd9acccd9acccd9acccd9acccd9acccd9acccd9acccd9acccd9acccd9acccd9acccd9acccd9a, 0xffffff000000ffffffffffff000000000000000000000000ffffff000000ffffffffffff000000000000000000000000ffffff000000ffffffffffff000000000000),
    (0x63f0f1e3f0f1e3f0f1e3f0f1e3f0f1e3f0f1e3f0f1e3f0f1e3f0f1e3f0f1e3f0f1e3f0f1e3f0f1e3f0f1e3f0f1e3f0f1e3f0f1e3f0f1e3f0f1e3f0f1e3f0f1e3f0f1e3f0f1e3f0f1e3, 0xffffffffffff000000000000000000000000000000000000ffffffffffff000000000000000000000000000000000000ffffffffffff000000000000000000000000),
    (0x0, 0x0),
    (0x7cff01fcff01fcff01fcff01fcff01fcff01fcff01fcff01fcff01fcff01fcff01fcff01fcff01fcff01fcff01fcff01fcff01fcff01fcff01fcff01fcff01fcff01fcff01fcff01fc, 0xffffff000000000000000000000000000000000000000000ffffff000000000000000000000000000000000000000000ffffff000000000000000000000000000000000000),
    (0xfffe00fffe00fffe00fffe00fffe00fffe00fffe00fffe00fffe00fffe00fffe00fffe00fffe00fffe00fffe00fffe00fffe00fffe00fffe00fffe00fffe00fffe00fffe00fffe00, 0xffffff000000000000000000000000000000000000000000ffffff000000000000000000000000000000000000000000ffffff000000000000000000000000000000000000000000)]
def g110C : List ColumnInfo := [(4,0,106,0,7)]
def g110D7 (j : Nat) : Nat := if j = 0 then 0x5f else 0
def g110L : Nat → Packing
  | 7 => (1, 0, 1, 0, 0, 1, 0, g110D7)
  | _ => emptyPacking
def g110I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g110 : Forest := ⟨110, 7, fun i => (g110Y[i]?).getD (0,0), g110C, [[], [101], [49], [49, 101]], g110L, g110I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g110P7n0 : block g110 7 0 1 = true := by decide +kernel
theorem g110B7 : block g110 7 0 1 = true := g110P7n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g110T : checkedTables g110 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g110 0 0 0 = true)
  · exact (rfl : block g110 1 0 0 = true)
  · exact (rfl : block g110 2 0 0 = true)
  · exact (rfl : block g110 3 0 0 = true)
  · exact (rfl : block g110 4 0 0 = true)
  · exact (rfl : block g110 5 0 0 = true)
  · exact (rfl : block g110 6 0 0 = true)
  · exact g110B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g110G : graphValid g110 (boundsBefore K109) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low110 : Lower true (varsX 110) (graphGoal 110) 8 := lower_forest (g:=g110) (i:=0) (hints:=17831216) (before_sound K109 V109) g110G g110T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K110 := extendKnown K109 8 [(110,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V110 : Known true K110 := extend_ok (m:=110) V109 low110 (by decide +kernel)

def g111Y : Array (Bits × Bits) := #[(0x55555555aaab6eaaaaaaad555b755555556aaadbaaaaaaab5556dd5555555aaab6eaaaaaaad555b755555556aaadbaaaaaaab5556dd5555555aaab6eaaaaaaad555b755555556aaadb, 0xfffffffffffff8000000000000000000000000000000000000000fffffffffffff80000000000003ffffffffffffe0000000000000),
    (0x66666666cccdbb33333336666dd9999999b3336ecccccccd999b766666666cccdbb33333336666dd9999999b3336ecccccccd999b766666666cccdbb33333336666dd9999999b3336e, 0x3ffffffffffffe0000000000000ffffffffffffffffffffffffffc00000000000000000000000000),
    (0x78787878f0f1cfc3c3c3c7878e7e1e1e1e3c3c73f0f0f0f1e1e39f8787878f0f1cfc3c3c3c7878e7e1e1e1e3c3c73f0f0f0f1e1e39f8787878f0f1cfc3c3c3c7878e7e1e1e1e3c3c73, 0x1fffffffffffff000000000000000000000000003ffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000),
    (0x7f807f80ff01f3fc03fc07f80f9fe01fe03fc07cff00ff01fe03e7f807f80ff01f3fc03fc07f80f9fe01fe03fc07cff00ff01fe03e7f807f80ff01f3fc03fc07f80f9fe01fe03fc07c, 0x1fffffffffffffffffffffffffffffffffffffffc0000000000000000000000000000000000000000000000000000000000000000000000000000000),
    (0x0, 0x0),
    (0x7fff8000fffe03fffc0007fff01fffe0003fff80ffff0001fffc07fff8000fffe03fffc0007fff01fffe0003fff80ffff0001fffc07fff8000fffe03fffc0007fff01fffe0003fff80, 0x3ffffffffffffe00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    (0x7fffffff000003fffffff800001fffffffc00000fffffffe000007fffffff000003fffffff800001fffffffc00000fffffffe000007fffffff000003fffffff800001fffffffc00000, 0x7ffffffffffffc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)]
def g111C : List ColumnInfo := [(1,0,110,0,8), (2,0,109,0,8), (3,0,108,0,5), (4,0,107,0,8), (5,0,106,0,7), (6,0,105,0,5), (8,0,103,0,8), (10,0,101,0,7), (32,0,79,0,8), (33,0,78,0,5), (34,0,77,0,5), (64,0,47,0,8), (65,0,46,0,5), (66,0,45,0,5)]
def g111D4 (j : Nat) : Nat := if j = 0 then 0xbb03bb02058c0aa468c684614541101aa8688684614541101b88688695151541101 else 0
def g111D5 (j : Nat) : Nat := if j = 0 then 0xd20206201000d982b3040000bb020011b0f02f6d8ccaea296785a4e4236180c018ce3889d16419458edc9b0303aca82533e4d8189d6541319c7113a2eb2a092db9360607595049cdc9b0303a8a825c68e518515054121dc52c34cea2a030fa9819d0751501a6cc98ce83a8a80d3a6486741d4540719c71142eab2203699931a14541101b54c90d0a2a0880eac1a11851504407c64d2a2a2a82203e30695151541101 else 0
def g111D6 (j : Nat) : Nat := if j = 0 then 0x3a340233000800607afa3cf40402d814cb3330e801013126cccc401d810390103b10990002b60509ce802a4072f8020a04281000400108062c2e202040d0a88764014343025a35e93468080004000001000010b0a086c2824302046c2824a00b446080008180c2130009cc00208000b601d8e1e00ecc80276b32120100000011b18080010000100079c0c201900020b0a090f8410104013e10b10042c40420108400829d90030030600830204343160239f100b8480d09a7c40216df5a8b45652b7568ab54f297528a053f2774e89b5312574989051d22f4508850d2134187e4f11bf3706d4d91ab350684cb187300594ad14f2884e4971272304347d0f71e83b4710db1b0344650bf1782c45109b1282444307b0e81b4310530a01041d0170009df835c606516be6037181945adf835c60651737e0d71819458df835c6065173b89e1641945cee27459065177ae022759504dea2781d654127e6060759504eeb8089d654133be062759504ced8189d654133b89e1759504ade3845d65412bb8a11759504afa0845d654133b89d1759504eea2781d65412be6060759504b9e3845d45412ee8211751504bb98181d454126f61267455049f98099d15413ce8214545504f3a1851505413ce4614541504e3945416164126f92175459049de385d5164127b8a175459049fa085d516412bb8a16545904c7f75595164134fdd54545904f3545455164135edd50545904f394541516412af61367515018fd8699d454067e6026751501cf98099d45406af9216751501aee2859d45406bb6086751501cf86741d454077c45d07515019ee285d5644063f9a175591019fa085d5644078f5156559101abe485d564406bb8a17559101afa085d5644072f9217559101cee285d5644063b8a17559101cfa085d5644078fdd54559101bea285d504406be9a17541101bf2185d5044077a8a17541101cfa685d5044077c8617541101eba6851504407ae1a14541101fb11851504406ee9216541101f394559504407ae9216541101e394559504407cc5151541101 else 0
def g111D7 (j : Nat) : Nat := if j = 0 then 0x881a04000a345682cc40d020009620426cc4087af4370d539836340015324e82740599ae4e8eccf8d020609d0c4881a0400134c1100db5322068100038c13a299016d89d021b86c80d881c000c996e4931265b93a3b33e380816c48810028cb6252200035b13a0424e68001132dc9d1d9983e3809b7a3bf667c700f918814025bd0dfb06c80d881c000b6d919b10228cb627424e6800112c588638100c3658a6d8100d6c4c8109100c00d362c4a8115f251c050c362c4a811dfb44e7c6000346bb1625457c94701231d8b13a2ba4a280014ec4e8ae1b203a2070002dd8b1420151220401234b130cd8b674488119d9b14241514039b142410114d8a12a01511ac0200bb020161c035b1760467ec1b2730787019613230420bb021323c28702024609b0cf0a1003bbb023386c80c1610380018ec58a1360c08020092c4c2766c50910086362ec18102bb16284980485010eec08ce1b203c2070002dd8b6ccc47763386c80f0e021d8b1424c67c80b0e029d89b19fb44260b0818000c18259e14228c7626c67ed109e10300b7624c08cfda202c300016ec4d8119e202c3000143463bb0601411c68c7760467880b0c0286bb13613b6894c121030001bb69adfab7a819e999791b89185b7ed79b6e76a36275d55754f946f4013bd3172c52491e918912911d084fc2f38ea0dfad70d3acdac6cc1abbaba0b94b34a80a3c9b29448908067de77e72c6b060a5c654a4b23fe3ac3062601c815a0c2001bf85a06516feb8c0ca2eff7181945dfae30328b3f5c606517f713a0ca2dee2741945bfc2e8328bbf859065177e8b20ca2ffa06419459fae3b2a09fb89d65412f713aca825fe1759504ff40eb2a097e81d654137713aca824ee2759504dfc2eb2a093f85d654137e8baca826fa0759504f7c2ea2a09ef45d45413dd03a8a825fe6745504e7a8a8aa09ce515054135ea2c2c826f905859049faeb0b2097fdd516412febaa2c826fd6545904f7a8a8b209fd45516413fc82a2c826ff6751501bfccea2a03bf99d454067f33a8a80efd6751501df8cea2a03fe41d454067ebaec880dff7559101bfaeab2203ef515644077eb2ac880eff75591019feeab2203bf5d5644067ebaac880ebd4559101bf6ea82203fe5d504406fcbaa0880fb94541101df6ca82203fe595044077cb2a0880ff11541101 else 0
def g111D8 (j : Nat) : Nat := if j = 0 then 0xacba08d965334f145000dae8237d865330f105000d32b268d965334f145000d6c9a08df61a4cc3c4180038c6cb268d969334f146034c6c9a37d869330f106035b2c9237da4cf18002cd6cb2682179969234d106001031b2c9a08df6133c4033b2c9a17d869330d106000eedb289a17d969334c244180f6cb6089f69969338d30a1060011ecb627d869330c28418003bb6ca258227d969334c28603fb2ca2589f61a4cc30a180eec96089f61334c284100da69382464327bce29a12dc51c8d0ea16821c2b82a000ff81945bf81945ff41945bfd9504ff59504bf59504ef51504ff45504fe41504bf85904ff45904ff51501bfd9101ff59101bf59101fe41101 else 0
def g111D9 (j : Nat) : Nat := if j = 0 then 0x2d17b1a931c430019b5a517b18931c420376bc20f63126310406c723807f517fa09fd01 else 0
def g111D10 (j : Nat) : Nat := if j = 0 then 0x170ec862043f else 0
def g111L : Nat → Packing
  | 4 => (3, 6, 4, 0, 0, 5, 0, g111D4)
  | 5 => (17, 5, 4, 0, 0, 8, 0, g111D5)
  | 6 => (74, 4, 4, 0, 0, 11, 0, g111D6)
  | 7 => (63, 3, 4, 0, 0, 12, 0, g111D7)
  | 8 => (16, 2, 4, 0, 0, 11, 0, g111D8)
  | 9 => (3, 1, 4, 0, 0, 8, 0, g111D9)
  | 10 => (1, 0, 4, 0, 0, 1, 0, g111D10)
  | _ => emptyPacking
def g111I : Nat → Nat → Option (Nat × Nat)
  | 5, tag => lookupShort 4 13 2 7 2 3 (fun j => if j=0 then 0x560052ad200028c1000212080 else 0) tag
  | 6, tag => lookupShort 13 39 2 10 5 3 (fun j => if j=0 then 0xc12a2000000000041e89e102300000000000348280f0a00202e1c060032b04000000000010bc3900a900fc320902105c06060220 else 0) tag
  | 7, tag => lookupShort 73 219 4 12 7 3 (fun j => if j=0 then 0xc0121f944000409492416000000000006837bb5c1500008121c40a49ee1040883850182441fa0f00082d000000c3284583500000000050904668203d03a92d80f00000000008402600083300000083b000000c2fe09040000886000c1209500003184400000000003f434c1ee48c256878a390a41801400041a000000000607123000538617a20a14c000b3c29cad1a3683f35e85933140d2881b021000000e0500004800041700000002c81c53c000000c2000000000043c2430000112810000000225ad000000000036007000827000a1101d58100000088280c00053d000c4100000021ba1d00000080d28480bc3000043e000aa510700044900eeb0a8600082e13e90cc3900000000042aa068874436390a200040302352e136c2b0a7c02c19c28e13000eb5000c04143000eb4883000000d30442005619447e35e34c13000000d0d41012f0001425100a4600201620210a13104303200142022056000003120030200010010d111012003 else 0) tag
  | 8, tag => lookupShort 64 192 4 11 6 3 (fun j => if j=0 then 0x40ef6c002b38000000000000042c8f4000000000000055dc4c000000000000035d800c388970cc200018555f0006240010d0008098e8001048141071c8329395924c814c310e10eba60018c40000014d5078280000000151e2987819516ec1c6d0240882c8760000000044738259a48c2e910ad0a194f2106c8000180000000046810ba242f01be9f0f296a4c8fb40800a840000022e8490492c80bc0da511aa2181f8a22189d8362dd5869506e18000a0749c01654be628600093a30d560000028953784e006089540cf1162b000d9800000d7b2d65e42ae6d00e4900000000343000910000004270200000000000007d5d00016df9e502870002140000230126405190450523001000212314001013001331033400204002100d0092730 else 0) tag
  | 9, tag => lookupShort 25 76 5 10 4 4 (fun j => if j=0 then 0xc2333bcc41474513480e0002301800000df878000048109c94000000061600001c6c028c801b68000061800413870dc080000000027ed40000000001c50a00040a0009c0044209001c7c08ac81ba484c04549920000071312e9b006148140c00256304800004001000a00c0000000 else 0) tag
  | 10, tag => lookupShort 7 21 2 8 2 4 (fun j => if j=0 then 0x1840064a00000000000055596814402010915200377012 else 0) tag
  | _, _ => none
def g111 : Forest := ⟨111, 10, fun i => (g111Y[i]?).getD (0,0), g111C, [[], [101], [49], [49, 101], [16, 50], [16, 50, 101], [16, 33, 50], [16, 33, 50, 101], [32], [32, 101], [32, 49], [32, 49, 101], [48, 49, 50], [48, 49, 50, 101], [48, 33], [48, 33, 101]], g111L, g111I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P4n0 : block g111 4 0 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P4n2 : block g111 4 2 1 = true := by decide +kernel
theorem g111B4 : block g111 4 0 3 = true := (@block_merge g111 4 0 2 1 g111P4n0 g111P4n2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P5n0 : block g111 5 0 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P5n2 : block g111 5 2 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P5n4 : block g111 5 4 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P5n6 : block g111 5 6 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P5n8 : block g111 5 8 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P5n10 : block g111 5 10 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P5n12 : block g111 5 12 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P5n14 : block g111 5 14 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P5n16 : block g111 5 16 1 = true := by decide +kernel
theorem g111B5 : block g111 5 0 17 = true := (@block_merge g111 5 0 8 9 (@block_merge g111 5 0 4 4 (@block_merge g111 5 0 2 2 g111P5n0 g111P5n2) (@block_merge g111 5 4 2 2 g111P5n4 g111P5n6)) (@block_merge g111 5 8 4 5 (@block_merge g111 5 8 2 2 g111P5n8 g111P5n10) (@block_merge g111 5 12 2 3 g111P5n12 (@block_merge g111 5 14 2 1 g111P5n14 g111P5n16))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P6n0 : block g111 6 0 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P6n2 : block g111 6 2 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P6n4 : block g111 6 4 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P6n6 : block g111 6 6 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P6n8 : block g111 6 8 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P6n10 : block g111 6 10 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P6n12 : block g111 6 12 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P6n14 : block g111 6 14 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P6n16 : block g111 6 16 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P6n18 : block g111 6 18 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P6n20 : block g111 6 20 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P6n22 : block g111 6 22 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P6n24 : block g111 6 24 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P6n26 : block g111 6 26 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P6n28 : block g111 6 28 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P6n30 : block g111 6 30 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P6n32 : block g111 6 32 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P6n34 : block g111 6 34 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P6n36 : block g111 6 36 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P6n38 : block g111 6 38 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P6n40 : block g111 6 40 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P6n42 : block g111 6 42 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P6n44 : block g111 6 44 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P6n46 : block g111 6 46 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P6n48 : block g111 6 48 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P6n50 : block g111 6 50 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P6n52 : block g111 6 52 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P6n54 : block g111 6 54 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P6n56 : block g111 6 56 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P6n58 : block g111 6 58 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P6n60 : block g111 6 60 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P6n62 : block g111 6 62 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P6n64 : block g111 6 64 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P6n66 : block g111 6 66 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P6n68 : block g111 6 68 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P6n70 : block g111 6 70 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P6n72 : block g111 6 72 2 = true := by decide +kernel
theorem g111B6 : block g111 6 0 74 = true := (@block_merge g111 6 0 36 38 (@block_merge g111 6 0 18 18 (@block_merge g111 6 0 8 10 (@block_merge g111 6 0 4 4 (@block_merge g111 6 0 2 2 g111P6n0 g111P6n2) (@block_merge g111 6 4 2 2 g111P6n4 g111P6n6)) (@block_merge g111 6 8 4 6 (@block_merge g111 6 8 2 2 g111P6n8 g111P6n10) (@block_merge g111 6 12 2 4 g111P6n12 (@block_merge g111 6 14 2 2 g111P6n14 g111P6n16)))) (@block_merge g111 6 18 8 10 (@block_merge g111 6 18 4 4 (@block_merge g111 6 18 2 2 g111P6n18 g111P6n20) (@block_merge g111 6 22 2 2 g111P6n22 g111P6n24)) (@block_merge g111 6 26 4 6 (@block_merge g111 6 26 2 2 g111P6n26 g111P6n28) (@block_merge g111 6 30 2 4 g111P6n30 (@block_merge g111 6 32 2 2 g111P6n32 g111P6n34))))) (@block_merge g111 6 36 18 20 (@block_merge g111 6 36 8 10 (@block_merge g111 6 36 4 4 (@block_merge g111 6 36 2 2 g111P6n36 g111P6n38) (@block_merge g111 6 40 2 2 g111P6n40 g111P6n42)) (@block_merge g111 6 44 4 6 (@block_merge g111 6 44 2 2 g111P6n44 g111P6n46) (@block_merge g111 6 48 2 4 g111P6n48 (@block_merge g111 6 50 2 2 g111P6n50 g111P6n52)))) (@block_merge g111 6 54 10 10 (@block_merge g111 6 54 4 6 (@block_merge g111 6 54 2 2 g111P6n54 g111P6n56) (@block_merge g111 6 58 2 4 g111P6n58 (@block_merge g111 6 60 2 2 g111P6n60 g111P6n62))) (@block_merge g111 6 64 4 6 (@block_merge g111 6 64 2 2 g111P6n64 g111P6n66) (@block_merge g111 6 68 2 4 g111P6n68 (@block_merge g111 6 70 2 2 g111P6n70 g111P6n72))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P7n0 : block g111 7 0 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P7n2 : block g111 7 2 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P7n4 : block g111 7 4 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P7n6 : block g111 7 6 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P7n8 : block g111 7 8 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P7n10 : block g111 7 10 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P7n12 : block g111 7 12 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P7n14 : block g111 7 14 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P7n16 : block g111 7 16 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P7n18 : block g111 7 18 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P7n20 : block g111 7 20 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P7n22 : block g111 7 22 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P7n24 : block g111 7 24 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P7n26 : block g111 7 26 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P7n28 : block g111 7 28 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P7n30 : block g111 7 30 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P7n32 : block g111 7 32 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P7n34 : block g111 7 34 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P7n36 : block g111 7 36 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P7n38 : block g111 7 38 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P7n40 : block g111 7 40 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P7n42 : block g111 7 42 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P7n44 : block g111 7 44 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P7n46 : block g111 7 46 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P7n48 : block g111 7 48 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P7n50 : block g111 7 50 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P7n52 : block g111 7 52 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P7n54 : block g111 7 54 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P7n56 : block g111 7 56 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P7n58 : block g111 7 58 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P7n60 : block g111 7 60 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P7n62 : block g111 7 62 1 = true := by decide +kernel
theorem g111B7 : block g111 7 0 63 = true := (@block_merge g111 7 0 32 31 (@block_merge g111 7 0 16 16 (@block_merge g111 7 0 8 8 (@block_merge g111 7 0 4 4 (@block_merge g111 7 0 2 2 g111P7n0 g111P7n2) (@block_merge g111 7 4 2 2 g111P7n4 g111P7n6)) (@block_merge g111 7 8 4 4 (@block_merge g111 7 8 2 2 g111P7n8 g111P7n10) (@block_merge g111 7 12 2 2 g111P7n12 g111P7n14))) (@block_merge g111 7 16 8 8 (@block_merge g111 7 16 4 4 (@block_merge g111 7 16 2 2 g111P7n16 g111P7n18) (@block_merge g111 7 20 2 2 g111P7n20 g111P7n22)) (@block_merge g111 7 24 4 4 (@block_merge g111 7 24 2 2 g111P7n24 g111P7n26) (@block_merge g111 7 28 2 2 g111P7n28 g111P7n30)))) (@block_merge g111 7 32 16 15 (@block_merge g111 7 32 8 8 (@block_merge g111 7 32 4 4 (@block_merge g111 7 32 2 2 g111P7n32 g111P7n34) (@block_merge g111 7 36 2 2 g111P7n36 g111P7n38)) (@block_merge g111 7 40 4 4 (@block_merge g111 7 40 2 2 g111P7n40 g111P7n42) (@block_merge g111 7 44 2 2 g111P7n44 g111P7n46))) (@block_merge g111 7 48 8 7 (@block_merge g111 7 48 4 4 (@block_merge g111 7 48 2 2 g111P7n48 g111P7n50) (@block_merge g111 7 52 2 2 g111P7n52 g111P7n54)) (@block_merge g111 7 56 4 3 (@block_merge g111 7 56 2 2 g111P7n56 g111P7n58) (@block_merge g111 7 60 2 1 g111P7n60 g111P7n62)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P8n0 : block g111 8 0 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P8n2 : block g111 8 2 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P8n4 : block g111 8 4 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P8n6 : block g111 8 6 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P8n8 : block g111 8 8 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P8n10 : block g111 8 10 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P8n12 : block g111 8 12 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P8n14 : block g111 8 14 2 = true := by decide +kernel
theorem g111B8 : block g111 8 0 16 = true := (@block_merge g111 8 0 8 8 (@block_merge g111 8 0 4 4 (@block_merge g111 8 0 2 2 g111P8n0 g111P8n2) (@block_merge g111 8 4 2 2 g111P8n4 g111P8n6)) (@block_merge g111 8 8 4 4 (@block_merge g111 8 8 2 2 g111P8n8 g111P8n10) (@block_merge g111 8 12 2 2 g111P8n12 g111P8n14)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P9n0 : block g111 9 0 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P9n2 : block g111 9 2 1 = true := by decide +kernel
theorem g111B9 : block g111 9 0 3 = true := (@block_merge g111 9 0 2 1 g111P9n0 g111P9n2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P10n0 : block g111 10 0 1 = true := by decide +kernel
theorem g111B10 : block g111 10 0 1 = true := g111P10n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111T : checkedTables g111 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g111 0 0 0 = true)
  · exact (rfl : block g111 1 0 0 = true)
  · exact (rfl : block g111 2 0 0 = true)
  · exact (rfl : block g111 3 0 0 = true)
  · exact g111B4
  · exact g111B5
  · exact g111B6
  · exact g111B7
  · exact g111B8
  · exact g111B9
  · exact g111B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111G : graphValid g111 (boundsBefore K110) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low111 : Lower true (varsX 111) (graphGoal 111) 11 := lower_forest (g:=g111) (i:=0) (hints:=4146) (before_sound K110 V110) g111G g111T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
end ForestCore
open ForestCore

def graph (x : Fin 8 → Bool) : Bool := decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
def coding : Fin 8 → Nat := ![0, 1, 4, 2, 3, 7, 5, 6]
def roots : List Sig := List.ofFn (fun i : Fin 8 => inputs.getD (coding i) zero)
def codedGraph : Sig := 0xfffffffffffefffefffefffefffefefefffffffffffefffefffefffeffa0eca0fffffffffffefffefffefffefffefefefffffffffffefffefffefffeffa0eca0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wholeBound : Lower true roots codedGraph 13 := by
  have h := lift_ok (u := true) (ms := fixRows 144 0) (raw := roots) (T := codedGraph)
    (xs := [(inputs.getD 4 zero, 8, 24), (inputs.getD 7 zero, 1, 129)]) (by decide +kernel)
    (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low111
  have hcard : (([(inputs.getD 4 zero, 8, 24), (inputs.getD 7 zero, 1, 129)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by decide +kernel
  rw [hcard] at h
  exact h

def sampleInput (r : Row) (i : Fin 8) : Bool := bit r (inputs.getD (coding i) zero)

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
    (comp : ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = graph x) :
    13 ≤ C.gates.countP (fun g => !signedNot g) := by
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

def witness : List Gate := [⟨.and, [0, 3]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [9, 6]⟩, ⟨.or, [10, 7]⟩, ⟨.and, [4, 11]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [13, 3]⟩, ⟨.or, [5, 6]⟩, ⟨.or, [15, 7]⟩, ⟨.and, [14, 16]⟩, ⟨.and, [6, 7]⟩, ⟨.or, [8, 12]⟩, ⟨.or, [19, 17]⟩, ⟨.or, [20, 18]⟩]

theorem witnessBasis : ∀ g ∈ witness, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  simp [witness]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 12000000 in
theorem witnessCorrect : ∀ x : Fin 8 → Bool, Circuit.eval ⟨witness, 21⟩ (List.ofFn x) = graph x := by
  decide +kernel

end PEqualNP.Outside.L_meta_31373

open PEqualNP.Outside.L_meta_31373 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_31373 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates out legal _ computes
  by_cases hnot : ∃ g ∈ gates, g.op = GateOp.not
  · have fan : PEqualNP.MetaComplexity.FanInTwo ⟨gates, out⟩ := fun t ht => legal t ht
    have paid := binaryLower ⟨gates, out⟩ fan computes
    obtain ⟨g, hg, hgate⟩ := hnot
    have lt : gates.countP (fun t => !signedNot t) < gates.length := by
      apply Nat.lt_of_le_of_ne List.countP_le_length
      intro h
      have h' := List.countP_eq_length.mp h g hg
      simp [signedNot, hgate] at h'
    refine ⟨witness, 21, witnessBasis, ?_, witnessCorrect⟩
    change 14 ≤ gates.length
    change 13 ≤ gates.countP (fun t => !signedNot t) at paid
    omega
  · refine ⟨gates, out, ?_, le_rfl, computes⟩
    intro g hg
    obtain ⟨hop, hlen⟩ := legal g hg
    refine ⟨?_, hlen⟩
    rcases hop with ha | ho | hn
    · exact Or.inl ha
    · exact Or.inr ho
    · exact False.elim (hnot ⟨g, hg, hn⟩)

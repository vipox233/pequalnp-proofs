import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_29706

namespace Base

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

def inputs : List Sig := [((((((((0xaaaaaaaa <<< 60) ||| 0xaaaaaaaaaaaaaaa) <<< 60) ||| 0xaaaaaaaaaaaaaaa) <<< 120) ||| ((0xaaaaaaaaaaaaaaa <<< 60) ||| 0xaaaaaaaaaaaaaaa)) <<< 240) ||| ((((0xaaaaaaaaaaaaaaa <<< 60) ||| 0xaaaaaaaaaaaaaaa) <<< 120) ||| ((0xaaaaaaaaaaaaaaa <<< 60) ||| 0xaaaaaaaaaaaaaaa))),((((((((0xcccccccc <<< 60) ||| 0xccccccccccccccc) <<< 60) ||| 0xccccccccccccccc) <<< 120) ||| ((0xccccccccccccccc <<< 60) ||| 0xccccccccccccccc)) <<< 240) ||| ((((0xccccccccccccccc <<< 60) ||| 0xccccccccccccccc) <<< 120) ||| ((0xccccccccccccccc <<< 60) ||| 0xccccccccccccccc))),((((((((0xf0f0f0f0 <<< 60) ||| 0xf0f0f0f0f0f0f0f) <<< 60) ||| 0xf0f0f0f0f0f0f0) <<< 120) ||| ((0xf0f0f0f0f0f0f0f <<< 60) ||| 0xf0f0f0f0f0f0f0)) <<< 240) ||| ((((0xf0f0f0f0f0f0f0f <<< 60) ||| 0xf0f0f0f0f0f0f0) <<< 120) ||| ((0xf0f0f0f0f0f0f0f <<< 60) ||| 0xf0f0f0f0f0f0f0))),((((((((0xff00ff00 <<< 60) ||| 0xff00ff00ff00ff0) <<< 60) ||| 0xff00ff00ff00ff) <<< 120) ||| ((0xff00ff00ff00f <<< 60) ||| 0xf00ff00ff00ff00)) <<< 240) ||| ((((0xff00ff00ff00ff0 <<< 60) ||| 0xff00ff00ff00ff) <<< 120) ||| ((0xff00ff00ff00f <<< 60) ||| 0xf00ff00ff00ff00))),((((((((0xffff0000 <<< 60) ||| 0xffff0000ffff000) <<< 60) ||| 0xffff0000ffff00) <<< 120) ||| ((0xffff0000ffff0 <<< 60) ||| 0xffff0000ffff)) <<< 240) ||| ((((0xffff0000fff <<< 60) ||| 0xf0000ffff0000ff) <<< 120) ||| ((0xff0000ffff0000f <<< 60) ||| 0xfff0000ffff0000))),((((((((0xffffffff <<< 60) ||| 0xfffffff) <<< 60) ||| 0xf00000000ffffff) <<< 120) ||| ((0xff00000000fffff <<< 60) ||| 0xfff00000000ffff)) <<< 240) ||| ((((0xffff00000000fff <<< 60) ||| 0xfffff00000000ff) <<< 120) ||| ((0xffffff00000000f <<< 60) ||| 0xfffffff00000000))),((((((((0xffffffff <<< 60) ||| 0xffffffff0000000) <<< 60) ||| 0xffffff) <<< 120) ||| ((0xffffffffff00000 <<< 60) ||| 0xffff)) <<< 240) ||| ((((0xffffffffffff000 <<< 60) ||| 0xff) <<< 120) ||| ((0xffffffffffffff0 <<< 60) ||| 0x0))),((((((((0xffffffff <<< 60) ||| 0xfffffffffffffff) <<< 60) ||| 0xfffffffff000000) <<< 120) ||| ((0x0 <<< 60) ||| 0xffff)) <<< 240) ||| ((((0xfffffffffffffff <<< 60) ||| 0xfffffffffffff00) <<< 120) ||| ((0x0 <<< 60) ||| 0x0))),((((((((0xffffffff <<< 60) ||| 0xfffffffffffffff) <<< 60) ||| 0xfffffffffffffff) <<< 120) ||| ((0xfffffffffffffff <<< 60) ||| 0xfffffffffff0000)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)))]
def graph : Sig := ((((((((0xfffffffe <<< 60) ||| 0xfffffffafffeffe) <<< 60) ||| 0xefefeaa00ffffff) <<< 120) ||| ((0xfefffffffafffef <<< 60) ||| 0xfeefefeaa00ffff)) <<< 240) ||| ((((0xfffefffffffafff <<< 60) ||| 0xeffeefefeaa00ff) <<< 120) ||| ((0xfffffefffffffaf <<< 60) ||| 0xffeffeefefeaa00)))
def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 4) || (x 2 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 3 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 4 && x 6)
theorem edge_table : ∀ r : Row, bit r graph = edge (sample r) := by decide +kernel
theorem graph_proper : proper graph := by unfold proper; decide +kernel
theorem input_list : List.ofFn (fun j : Fin 9 => inputs.getD j.val zero) = inputs := rfl
theorem sampled (r : Row) : List.ofFn (sample r) = inputs.map (bit r) := by
  rw [←input_list]
  rw [List.map_ofFn]
  rfl

theorem table_eval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates inputs).getD i zero) =
      (C.wires (List.ofFn (sample r))).getD i false := by
  rw [←b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),sampled]
  rfl

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
  (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 2 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 3 &&& x 5) ||| (x 0 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6)
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

abbrev Bits := BitVec 152
abbrev Signals := Bits × Bits
abbrev Decor := Sig × Signals

def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def pairSig (r s : Fin 152 → Row) (a : Sig) : Signals := (ofRows r a,ofRows s a)
def properPairs (T : Sig) (r s : Fin 152 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 152 r s (pairSig r s) := by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩
def faithful (r s : Fin 152 → Row) (x : Decor) := x.2 = pairSig r s x.1
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

def asRow (cols : Nat → Bits) (i : Fin 152) : Row :=
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
theorem asRow_bit (cols : Nat → Bits) (i : Fin 152) (j : Fin 9) :
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
  (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 2 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 3 &&& x 5) ||| (x 0 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6)
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 152) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then v j.val else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · simpa [vertex,hh] using asRow_bit v i j
  · simp [vertex,hh,bit_zero]
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 152) :
    bit (asRow v i) (graphGoal m) = (liftGoal m v).getLsbD i.val := by
  have pos (j : Nat) (hj : j<9) : (vertex m j).getLsbD (asRow v i).val = ((if m.testBit j then v j else 0) : Bits).getLsbD i.val := bit_vertex m v i ⟨j,hj⟩
  simp only [bit,graphGoal,liftGoal,BitVec.getLsbD_and,BitVec.getLsbD_or]
  simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide),pos 6 (by decide),pos 7 (by decide),pos 8 (by decide)]
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
  let n := v.toNat % 2305843009213693951
  (n*(n+971)) % 2305843009213693951
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
    if (rs ||| column d z.2) != BitVec.allOnes 152 then true else
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
  have be : ((restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 152) = false := by
    simpa using sep
  change (if (restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 152 then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
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
theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 152) :
    bit (asRow v i) (chartGoal m) = (chartSamples m v).getLsbD i.val := by
  exact bit_liftGoal m v i
theorem chart_pairs {m : Nat} {p q : Nat → Bits}
    (hp : chartSamples m p = BitVec.allOnes 152) (hq : chartSamples m q = 0) :
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
  (chartSamples g.mask (fun j => (g.samples j).1) == BitVec.allOnes 152) &&
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
theorem known_down {u es} (h : Known true es) : Known u es := fun e he => lower_down (h e he)
def lanePlace (v : Nat) (upper : Nat) := 2^153*upper+v
def combineLanes {α : Type} (f : α → Bits) : List α → Nat
  | [] => 0
  | x::xs => lanePlace (f x).toNat (combineLanes f xs)
def units : Nat → Nat
  | 0 => 0
  | n+1 => lanePlace 1 (units n)
theorem laneSmall (x : Bits) : x.toNat < 2^153 :=
  lt_trans x.isLt (by decide +kernel)
theorem place_and (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u &&& lanePlace b.toNat v = lanePlace (a &&& b).toNat (u &&& v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_and,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<153 <;> simp only [h,ite_true,ite_false,BitVec.toNat_and,Nat.testBit_and]
theorem place_or (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ||| lanePlace b.toNat v = lanePlace (a ||| b).toNat (u ||| v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_or,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<153 <;> simp only [h,ite_true,ite_false,BitVec.toNat_or,Nat.testBit_or]
theorem place_xor (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ^^^ lanePlace b.toNat v = lanePlace (a ^^^ b).toNat (u ^^^ v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_xor,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<153 <;> simp only [h,ite_true,ite_false,BitVec.toNat_xor,Nat.testBit_xor]
theorem lanes_and {α} (f g : α → Bits) (xs) :
    combineLanes f xs &&& combineLanes g xs = combineLanes (fun x => f x &&& g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_and,ih]
theorem lanes_or {α} (f g : α → Bits) (xs) :
    combineLanes f xs ||| combineLanes g xs = combineLanes (fun x => f x ||| g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_or,ih]
theorem lanes_xor {α} (f g : α → Bits) (xs) :
    combineLanes f xs ^^^ combineLanes g xs = combineLanes (fun x => f x ^^^ g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_xor,ih]
def fullMarks (r packed : Nat) := ((packed+r) >>> 152) &&& r
theorem unit_bit (n i : Nat) (hi : i<n) : (units n).testBit (153*i) = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [units,lanePlace,Nat.testBit_two_pow_mul_add _ (by decide +kernel : 1 < 2^153)]
    cases i with
    | zero => simp
    | succ i =>
      have di : 153*(i+1)-153=153*i := by omega
      have ge : ¬153*(i+1)<153 := by omega
      simp only [ge,ite_false,di]
      exact ih _ (by omega)
set_option maxRecDepth 8192 in
theorem guardBit (a : Bits) : (a.toNat+1).testBit 152 = (a==BitVec.allOnes 152) := by
  by_cases h : a=BitVec.allOnes 152
  · subst a
    decide +kernel
  · have lim := a.isLt
    have ne : a.toNat ≠ 2^152-1 := by
      intro eq
      apply h
      apply BitVec.eq_of_toNat_eq
      simpa only [BitVec.toNat_allOnes] using eq
    have lt : a.toNat+1<2^152 := by omega
    rw [Nat.testBit_eq_false_of_lt lt]
    exact (beq_eq_false_iff_ne.mpr h).symm

set_option maxRecDepth 8192 in
theorem mark_at {α} (f : α → Bits) (xs : List α) (i : Nat) (hi : i<xs.length) :
    (fullMarks (units xs.length) (combineLanes f xs)).testBit (153*i) =
      (f xs[i]==BitVec.allOnes 152) := by
  simp only [fullMarks,Nat.testBit_and,Nat.testBit_shiftRight,unit_bit _ _ hi,Bool.and_true]
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    simp only [combineLanes,List.length_cons,units,lanePlace]
    have sum (u v x : Nat) : 2^153*u+x+(2^153*v+1)=2^153*(u+v)+(x+1) := by omega
    rw [sum,Nat.testBit_two_pow_mul_add _ (show (f a).toNat+1<2^153 from by have := (f a).isLt; omega)]
    have hi' : i < xs.length+1 := hi
    cases i with
    | zero => simpa using guardBit (f a)
    | succ i =>
      have ge : ¬153*(i+1)+152<153 := by omega
      have di : 153*(i+1)+152-153=153*i+152 := by omega
      simp only [ge,ite_false,di,List.getElem_cons_succ]
      apply ih i (by omega)

abbrev PackedSig := Nat × Nat
abbrev PackedCov := Nat × Nat × Nat

def packedSig {α} (s : α → Signals) (xs : List α) : PackedSig :=
  (combineLanes (fun x => (s x).1) xs,combineLanes (fun x => (s x).2) xs)
def packedCov {α} (c : α → Cov) (xs : List α) : PackedCov :=
  (combineLanes (fun x => (c x).1) xs,combineLanes (fun x => (c x).2.1) xs,
   combineLanes (fun x => (c x).2.2) xs)
def packedColumn (d : Bool) (a : PackedSig) :=
  if d then a.1 ^^^ (a.1 &&& a.2) else a.1 ^^^ a.2

theorem xor_meet (a b : Bits) : a ^^^ (a &&& b) = a &&& ~~~b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> rfl

theorem packed_column {α} (s : α → Signals) (xs : List α) (d : Bool) :
    packedColumn d (packedSig s xs) = combineLanes (fun x => column d (s x)) xs := by
  cases d <;> simp only [packedColumn,packedSig,column,Bool.false_eq_true,ite_false,ite_true,lanes_and,lanes_xor,xor_meet]

def packedOp (op : Nat) (a b : PackedSig) : PackedSig :=
  if op=0 then (a.1 &&& b.1,a.2 &&& b.2) else if op=1 then (a.1 ||| b.1,a.2 ||| b.2)
  else if op=2 then (a.1 ^^^ (a.1 &&& b.1),a.2 ^^^ (a.2 &&& b.2))
  else (b.1 ^^^ (b.1 &&& a.1),b.2 ^^^ (b.2 &&& a.2))
theorem packed_op {α} (a b : α → Decor) (xs : List α) (op : Nat) :
    packedOp op (packedSig (fun x => (a x).2) xs) (packedSig (fun x => (b x).2) xs) =
    packedSig (fun x => (dbin op (a x) (b x)).2) xs := by
  by_cases h0 : op=0
  · simp only [packedOp,h0,ite_true,packedSig,lanes_and,dbin,bv]
  by_cases h1 : op=1
  · simp [packedOp,h1,packedSig,lanes_or,dbin,bv]
  by_cases h2 : op=2
  · simp [packedOp,h2,packedSig,lanes_and,lanes_xor,xor_meet,dbin,bv]
  · have e (x y : Bits) : ~~~x &&& y = y &&& ~~~x := BitVec.and_comm _ _
    simp only [packedOp,h0,h1,h2,ite_false,packedSig,lanes_and,lanes_xor,xor_meet,dbin,bv,e]

def takePacked (c : PackedCov) (a b : Nat) (ka kb : Bool) :=
  let without1 := fun w => c.1 ^^^ (c.1 &&& (c.2.1 &&& w))
  let without2 := c.1 ^^^ (c.1 &&& ((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b))))
  if ka then (if kb then c.1 else without1 b)
  else if kb then without1 a else without2

theorem takePacked_ok {α} (c : α → Cov) (a b : α → Bits) (xs : List α) (ka kb : Bool) :
    takePacked (packedCov c xs) (combineLanes a xs) (combineLanes b xs) ka kb =
    combineLanes (fun x => restCov (c x) (a x) (b x) ka kb) xs := by
  cases ka <;> cases kb <;>
    simp only [takePacked,packedCov,lanes_and,lanes_or,lanes_xor,xor_meet,restCov,takeOne,takeTwo,
      Bool.false_eq_true,ite_false,ite_true]

def contextWire (c : NodeContext) (i : Nat) := c.2.2.1.getD i defaultDecor
def checkAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let a := contextWire c i
  let b := contextWire c j
  evalMove c op a b (dbin op a b) ka kb
def combField (c : NodeContext) (d ka kb : Bool) (op i j : Nat) :=
  let a := contextWire c i
  let b := contextWire c j
  restCov c.2.2.2.1.1 (column d a.2) (column d b.2) ka kb |||
    column d (dbin op a b).2

def onMarks {α : Type} (f : α → Bool) (mask : Nat) : List α → Bool
  | [] => true
  | x::xs => if mask=0 then true else
    ((mask &&& 1 == 0) || f x) && onMarks f (mask >>> 153) xs
theorem marked_ok {α} (f : α → Bool) (mask : Nat) (xs : List α) (i : Nat) (hi : i<xs.length)
    (bitOn : mask.testBit (153*i)=true) (ok : onMarks f mask xs=true) : f xs[i]=true := by
  induction xs generalizing mask i with
  | nil => simp at hi
  | cons x xs ih =>
    have ne : mask≠0 := by intro e; simp [e] at bitOn
    simp only [onMarks,ne,ite_false,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
    cases i with
    | zero =>
      have nonzero : mask &&& 1 ≠ 0 := by
        intro he
        have at0 := congrArg (fun n : Nat => n.testBit 0) he
        simp only [Nat.testBit_and] at at0
        change mask.testBit 0=true at bitOn
        simp [bitOn] at at0
      exact ok.1.resolve_left nonzero
    | succ i =>
      apply ih (mask:=mask >>> 153) (i:=i) (by simpa using hi) _ ok.2
      simpa only [Nat.testBit_shiftRight,Nat.mul_succ,Nat.add_comm] using bitOn

abbrev Batch := Nat × Nat × Nat × List PackedSig × PackedCov
def makeBatch (k n : Nat) (xs : List NodeContext) : Batch :=
  (k,n,units xs.length,(List.range n).map (fun i => packedSig (fun c => (contextWire c i).2) xs),
    packedCov (fun c => c.2.2.2.1.1) xs)
def laneWire (b : Batch) (i : Nat) := b.2.2.2.1.getD i (0,0)
theorem laneWire_at (k n) (xs) {i : Nat} (h : i<n) :
    laneWire (makeBatch k n xs) i = packedSig (fun c => (contextWire c i).2) xs := by
  simp [laneWire,makeBatch,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range,h]

theorem masked_comp (d x : Sig) : masked d (neg x) = d ^^^ masked d x := by
  apply bit_ext
  intro r
  simp only [masked,neg,bit,BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_xor,r.isLt,decide_true,Bool.true_and]
  cases d.getLsbD r.val <;> cases x.getLsbD r.val <;> rfl
def constantLoss (p : Decor → Bool) (a : Decor) (keep : Bool) :=
  if keep then 0 else (p a).toNat
theorem lossBound (p : Decor → Bool) (ws : List Decor) (a : Decor) (keep : Bool) :
    ws.countP p ≤ (delOne ws a keep).countP p + constantLoss p a keep := by
  cases keep
  · simp only [delOne,Bool.false_eq_true,ite_false,constantLoss,List.countP_erase]
    split
    next h => simp [h.2]; omega
    next => omega
  · simp [delOne,constantLoss]

theorem keptCount (p : Decor → Bool) (ws : List Decor) (a b : Decor) (ka kb : Bool) :
    ws.countP p - constantLoss p a ka - constantLoss p b kb ≤
    (delTwo ws a b ka kb).countP p := by
  have h1 := lossBound p ws a ka
  have h2 := lossBound p (delOne ws a ka) b kb
  simp only [delTwo]
  omega

noncomputable def force {β : Type} (n : Nat) (f : Nat → β) : β := Nat.rec (f 0) (fun k _ => f (Nat.succ k)) n
theorem force_eq {β : Type} (n : Nat) (f : Nat → β) : force n f = f n := by cases n <;> rfl
noncomputable def forceMap {α β : Type} (f : α → Nat) (l : List α) : (List Nat → β) → β :=
  List.rec (fun k => k []) (fun a _ ih k => force (f a) fun x => ih fun xs => k (x::xs)) l
theorem forceMap_eq {α β : Type} (f : α → Nat) (l : List α) (k : List Nat → β) : forceMap f l k = k (l.map f) := by
  induction l generalizing k with
  | nil => rfl
  | cons a l ih =>
    change force (f a) (fun x => forceMap f l fun xs => k (x::xs)) = _
    rw [force_eq,ih]
    rfl
def nmask (d : Nat) (a : Sig) : Nat := Nat.land a.toNat d
noncomputable def anyEq (m : Nat) (l : List Nat) : Bool := List.rec false (fun v _ ih => or (Nat.beq m v) ih) l
def nconst (d m : Nat) : Bool := or (Nat.beq m 0) (Nat.beq m d)
noncomputable def navail (u : Bool) (d : Nat) (pm : List Nat) (m : Nat) : Bool :=
  or (or (nconst d m) (anyEq m pm)) (and u (anyEq (Nat.xor d m) pm))
theorem nmask_eq (d a : Sig) : nmask d.toNat a = (masked d a).toNat := (BitVec.toNat_and _ _).symm
theorem beq_toNat (a b : Sig) : Nat.beq a.toNat b.toNat = (a==b) := by
  rw [Bool.eq_iff_iff,Nat.beq_eq,beq_iff_eq]
  exact BitVec.toNat_inj
theorem nconst_eq (d a : Sig) : nconst d.toNat (nmask d.toNat a) = isMaskedConstant d a := by
  rw [nmask_eq]
  have e : Nat.beq (masked d a).toNat 0 = (masked d a == zero) := by
    have z0 : zero.toNat=0 := by simp [zero]
    rw [←beq_toNat,z0]
  rw [nconst,e,beq_toNat]
  rfl
theorem anyEq_eq (x d : Sig) (pool : List Sig) : anyEq x.toNat (pool.map (nmask d.toNat)) = (pool.map (masked d)).any (fun v => v==x) := by
  induction pool with
  | nil => rfl
  | cons a l ih =>
    change or (Nat.beq x.toNat (nmask d.toNat a)) (anyEq x.toNat (l.map (nmask d.toNat))) = _
    rw [ih,nmask_eq,beq_toNat,List.map_cons,List.any_cons,Bool.beq_comm]
theorem navail_eq (u : Bool) (d a : Sig) (pool : List Sig) :
    navail u d.toNat (pool.map (nmask d.toNat)) (nmask d.toNat a) = availableB u d pool a := by
  have x : Nat.xor d.toNat (masked d a).toNat = (masked d (neg a)).toNat := by
    rw [masked_comp]
    exact (BitVec.toNat_xor _ _).symm
  rw [navail,nconst_eq,nmask_eq,x,anyEq_eq,anyEq_eq]
  simp only [availableB,isMaskedConstant]
def unav (u : Bool) (p : BoundPool) (w : Decor) : Nat := cond (availableB u p.domain p.wires w.1) 0 1
def slowCost (u : Bool) (p : BoundPool) (ws : List Decor) (k : Nat) (a b : Decor) (op : Nat) (ka kb : Bool) : Bool :=
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let z := bin op a.1 b.1
  let cm := ws.countP const - constantLoss const a ka - constantLoss const b kb + (isMaskedConstant p.domain z).toNat
  (((ws.map (unav u p)).sum == cond ka 0 (unav u p a) + cond kb 0 (unav u p b)) &&
    decide (k+p.paid+(!availableB u p.domain p.wires z).toNat < p.bound+cm)) &&
    (availableB u p.domain p.wires z || (availableB u p.domain p.wires a.1 && availableB u p.domain p.wires b.1))
def zN (op x y : Nat) : Nat := cond (Nat.beq op 0) (Nat.land x y) (cond (Nat.beq op 1) (Nat.lor x y)
  (cond (Nat.beq op 2) (Nat.xor x (Nat.land x y)) (Nat.xor y (Nat.land x y))))
theorem zN_eq (op : Nat) (d a b : Sig) : zN op (nmask d.toNat a) (nmask d.toNat b) = nmask d.toNat (bin op a b) := by
  have tn (x y : Sig) : Nat.land x.toNat y.toNat = (x &&& y).toNat := (BitVec.toNat_and x y).symm
  have tx (x y : Sig) : Nat.xor x.toNat y.toNat = (x ^^^ y).toNat := (BitVec.toNat_xor x y).symm
  have tor (x y : Sig) : Nat.lor x.toNat y.toNat = (x ||| y).toNat := (BitVec.toNat_or x y).symm
  simp only [nmask_eq]
  unfold zN
  by_cases h0 : op=0
  · subst h0
    change Nat.land _ _ = _
    rw [tn]
    congr 1
    apply bit_ext
    intro r
    simp only [masked,bin,bit,ite_true,BitVec.getLsbD_and]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  by_cases h1 : op=1
  · subst h1
    change Nat.lor _ _ = _
    rw [tor]
    congr 1
    apply bit_ext
    intro r
    simp only [masked,bin,bit,Nat.one_ne_zero,ite_true,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_or]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  have e0 : Nat.beq op 0=false := Bool.eq_false_iff.mpr (fun h => h0 (Nat.eq_of_beq_eq_true h))
  have e1 : Nat.beq op 1=false := Bool.eq_false_iff.mpr (fun h => h1 (Nat.eq_of_beq_eq_true h))
  by_cases h2 : op=2
  · subst h2
    change Nat.xor _ (Nat.land _ _) = _
    rw [tn,tx]
    congr 1
    apply bit_ext
    intro r
    simp only [masked,bin,bit,OfNat.ofNat_ne_zero,OfNat.ofNat_ne_one,ite_true,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_xor,BitVec.getLsbD_not,r.isLt,decide_true,Bool.true_and]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  have e2 : Nat.beq op 2=false := Bool.eq_false_iff.mpr (fun h => h2 (Nat.eq_of_beq_eq_true h))
  rw [e0,e1,e2]
  change Nat.xor _ (Nat.land _ _) = _
  rw [tn,tx]
  congr 1
  apply bit_ext
  intro r
  simp only [masked,bin,bit,h0,h1,h2,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_xor,BitVec.getLsbD_not,r.isLt,decide_true,Bool.true_and]
  cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
def nloss (d x : Nat) (keep : Bool) : Nat := cond keep 0 (cond (nconst d x) 1 0)
theorem nloss_eq (d : Sig) (a : Decor) (keep : Bool) :
    nloss d.toNat (nmask d.toNat a.1) keep = constantLoss (fun w : Decor => isMaskedConstant d w.1) a keep := by
  rw [nloss,nconst_eq,constantLoss]
  cases keep
  · cases isMaskedConstant d a.1 <;> rfl
  · rfl
abbrev QS := Nat × Nat × Nat × Nat × Nat × List Nat × List Nat × Bool
noncomputable def quickSpec (u : Bool) (k : Nat) (ws : List Decor) (p : BoundPool) : QS :=
  let d := p.domain.toNat
  let ms := ws.map (fun w : Decor => nmask d w.1)
  (d,ms.countP (nconst d),p.bound,Nat.add k p.paid,(ms.map fun m => cond (navail u d (p.wires.map (nmask d)) m) 0 1).sum,ms,p.wires.map (nmask d),u)
noncomputable def forceBool {β : Type} (b : Bool) (f : Bool → β) : β := Bool.rec (f false) (f true) b
noncomputable def forcePool {β : Type} (u : Bool) (k : Nat) (ws : List Decor) (p : BoundPool) (f : QS → β) : β :=
  force p.domain.toNat fun d => forceMap (nmask d) p.wires fun pm => forceMap (fun w : Decor => nmask d w.1) ws fun ms =>
  force (ms.countP (nconst d)) fun c => force p.bound fun l => force (Nat.add k p.paid) fun t =>
  force (ms.map fun m => cond (navail u d pm m) 0 1).sum fun v => forceBool u fun u => f (d,c,l,t,v,ms,pm,u)
theorem forcePool_eq {β : Type} (u k ws p) (f : QS → β) : forcePool u k ws p f = f (quickSpec u k ws p) := by
  have e (b : Bool) (f : Bool → β) : forceBool b f = f b := by cases b <;> rfl
  simp only [forcePool,force_eq,forceMap_eq,e]
  rfl
noncomputable def forcePools {β : Type} (u : Bool) (k : Nat) (ws : List Decor) (ps : List BoundPool) : (List QS → β) → β :=
  List.rec (fun f => f []) (fun p _ ih f => forcePool u k ws p fun q => ih fun qs => f (q::qs)) ps
theorem forcePools_eq {β : Type} (u k ws ps) (f : List QS → β) : forcePools u k ws ps f = f (ps.map (quickSpec u k ws)) := by
  induction ps generalizing f with
  | nil => rfl
  | cons p ps ih =>
    change forcePool u k ws p (fun q => forcePools u k ws ps fun qs => f (q::qs)) = _
    rw [forcePool_eq,ih]
    rfl
def kwN (v : Nat) : Nat :=
  let n := v % 2305843009213693951
  (n*(n+971)) % 2305843009213693951
abbrev Lane := NodeContext × Nat × Nat × List QS × List Nat × Nat
noncomputable def laneOf (c : NodeContext) : Lane :=
  let ws := c.2.2.1.map (fun w : Decor => w.1.toNat)
  (c,c.2.2.1.length,cond c.2.2.2.1.2 4 2,c.2.2.2.2.1.map (quickSpec c.2.2.2.1.2 (c.1-1) c.2.2.1),ws,(ws.map kwN).sum)
noncomputable def forceLanes {β : Type} (cs : List NodeContext) : (List Lane → β) → β :=
  List.rec (fun f => f []) (fun c _ ih f => force c.2.2.1.length fun n => force (cond c.2.2.2.1.2 4 2) fun l =>
    forceMap (fun w : Decor => w.1.toNat) c.2.2.1 fun ws => force (ws.map kwN).sum fun t =>
    forcePools c.2.2.2.1.2 (c.1-1) c.2.2.1 c.2.2.2.2.1 fun qs => ih fun ys => f ((c,n,l,qs,ws,t)::ys)) cs
theorem forceLanes_eq {β : Type} (cs) (f : List Lane → β) : forceLanes cs f = f (cs.map laneOf) := by
  induction cs generalizing f with
  | nil => rfl
  | cons c cs ih =>
    change force c.2.2.1.length (fun n => force (cond c.2.2.2.1.2 4 2) fun l =>
      forceMap (fun w : Decor => w.1.toNat) c.2.2.1 fun ws => force (ws.map kwN).sum fun t =>
      forcePools c.2.2.2.1.2 (c.1-1) c.2.2.1 c.2.2.2.2.1 fun qs => forceLanes cs fun ys => f ((c,n,l,qs,ws,t)::ys)) = _
    rw [force_eq,force_eq,forceMap_eq,force_eq,forcePools_eq,ih]
    rfl
noncomputable def fastCost (s : QS) (i j op : Nat) (ka kb : Bool) : Bool :=
  force (s.2.2.2.2.2.1.getD i 0) fun x => force (s.2.2.2.2.2.1.getD j 0) fun y =>
  let av := navail s.2.2.2.2.2.2.2 s.1 s.2.2.2.2.2.2.1
  let hi := Nat.add s.2.2.1 (Nat.sub (Nat.sub s.2.1 (nloss s.1 x ka)) (nloss s.1 y kb))
  let lo := s.2.2.2.1
  and (Nat.beq s.2.2.2.2.1 (Nat.add (cond ka 0 (cond (av x) 0 1)) (cond kb 0 (cond (av y) 0 1))))
  (cond (Nat.ble (Nat.succ lo) hi)
    (force (zN op x y) fun z => or (av z) (and (Nat.ble (Nat.add lo 2) hi) (and (av x) (av y))))
    (cond (Nat.ble lo hi) (nconst s.1 (zN op x y)) false))
theorem spec_get {d : Nat} (ws : List Decor) (i : Nat) (hd : nmask d zero=0) :
    (ws.map (fun w : Decor => nmask d w.1)).getD i 0 = nmask d (ws.getD i defaultDecor).1 := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases ws[i]? with
  | none => exact hd.symm
  | some v => rfl
theorem fast_slow {u k p ws i j op ka kb} (h : fastCost (quickSpec u k ws p) i j op ka kb=true) :
    slowCost u p ws k (ws.getD i defaultDecor) (ws.getD j defaultDecor) op ka kb=true := by
  have z0 : nmask p.domain.toNat zero=0 := by
    have : zero.toNat=0 := by simp [zero]
    simp [nmask,this]
  have su : (((ws.map (fun w : Decor => nmask p.domain.toNat w.1)).map fun m => cond (navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat)) m) 0 1).sum) =
      (ws.map (unav u p)).sum := by
    rw [List.map_map]
    refine congrArg List.sum (List.map_congr_left ?_)
    intro w _
    change cond (navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat)) (nmask p.domain.toNat w.1)) 0 1 = _
    rw [navail_eq]
    rfl
  simp only [fastCost,quickSpec,force_eq,spec_get _ _ z0,su,List.countP_map,Function.comp_def,nconst_eq] at h
  generalize ws.getD i defaultDecor=a at h ⊢
  generalize ws.getD j defaultDecor=b at h ⊢
  replace h : and (Nat.beq (ws.map (unav u p)).sum (Nat.add (cond ka 0 (cond ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat a.1)) 0 1)) (cond kb 0 (cond ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat b.1)) 0 1))))
   (cond (Nat.ble (Nat.succ (Nat.add k p.paid)) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w : Decor => isMaskedConstant p.domain w.1)) (nloss p.domain.toNat (nmask p.domain.toNat a.1) ka)) (nloss p.domain.toNat (nmask p.domain.toNat b.1) kb))))
    (or ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (zN op (nmask p.domain.toNat a.1) (nmask p.domain.toNat b.1))) (and (Nat.ble (Nat.add (Nat.add k p.paid) 2) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w : Decor => isMaskedConstant p.domain w.1)) (nloss p.domain.toNat (nmask p.domain.toNat a.1) ka)) (nloss p.domain.toNat (nmask p.domain.toNat b.1) kb)))) (and ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat a.1)) ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat b.1)))))
    (cond (Nat.ble (Nat.add k p.paid) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w : Decor => isMaskedConstant p.domain w.1)) (nloss p.domain.toNat (nmask p.domain.toNat a.1) ka)) (nloss p.domain.toNat (nmask p.domain.toNat b.1) kb)))) (nconst p.domain.toNat (zN op (nmask p.domain.toNat a.1) (nmask p.domain.toNat b.1))) false)) = true := h
  rw [zN_eq,nconst_eq,navail_eq,navail_eq,navail_eq,nloss_eq,nloss_eq] at h
  have ca : isMaskedConstant p.domain (bin op a.1 b.1)=true → availableB u p.domain p.wires (bin op a.1 b.1)=true := by
    intro zc
    simp only [availableB,isMaskedConstant,Bool.or_eq_true] at zc ⊢
    exact Or.inl (Or.inl zc)
  simp only [Nat.add_eq,Nat.sub_eq,Nat.succ_eq_add_one,Bool.and_eq_true,Nat.beq_eq] at h
  obtain ⟨hu,h⟩ := h
  simp only [slowCost,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq]
  refine ⟨⟨hu,?_⟩,?_⟩
  all_goals
    generalize ws.countP (fun w => isMaskedConstant p.domain w.1) - constantLoss (fun w : Decor => isMaskedConstant p.domain w.1) a ka -
      constantLoss (fun w : Decor => isMaskedConstant p.domain w.1) b kb = c at h ⊢
    generalize isMaskedConstant p.domain (bin op a.1 b.1)=r at h ca ⊢
    generalize availableB u p.domain p.wires (bin op a.1 b.1)=q at h ca ⊢
    cases h1 : Nat.ble (k+p.paid+1) (p.bound+c)
    · rw [h1] at h
      cases h2 : Nat.ble (k+p.paid) (p.bound+c)
      · simp [h2] at h
      · have := Nat.ble_eq.mp h2
        simp only [h2,cond_true,cond_false] at h
        subst h
        rw [ca rfl]
        simp <;> omega
    · rw [h1] at h
      have l1 := Nat.ble_eq.mp h1
      simp only [cond_true,Bool.or_eq_true,Bool.and_eq_true,Nat.ble_eq] at h
      rcases h with rfl | ⟨l2,ha,hb⟩
      · simp <;> omega
      · first
        | (have : (!q).toNat ≤ 1 := Bool.toNat_le _
           omega)
        | simp [ha,hb]

theorem anyEq_iff (m : Nat) (l : List Nat) : anyEq m l=true ↔ m ∈ l := by
  induction l with
  | nil => simp [anyEq]
  | cons a l ih =>
    change or (Nat.beq m a) (anyEq m l)=true ↔ _
    rw [Bool.or_eq_true,ih,Nat.beq_eq,List.mem_cons]
noncomputable def linkAt (fl : Nat → Option (List Nat)) (l : Lane) (i j op : Nat) (ka kb : Bool) : Bool :=
  force (l.2.2.2.2.1.getD i 0) fun x => force (l.2.2.2.2.1.getD j 0) fun y => force (zN op x y) fun z =>
  Option.rec false (fun ys => forceMap (fun v => v) ys fun ys =>
    and (anyEq z ys) (and (l.2.2.2.2.1.all fun v => or (and (not ka) (Nat.beq v x)) (or (and (not kb) (Nat.beq v y)) (anyEq v ys)))
      (ys.all fun v => or (Nat.beq v z) (and (and (or ka (not (Nat.beq v x))) (or kb (not (Nat.beq v y)))) (anyEq v l.2.2.2.2.1)))))
    (fl (Nat.add (kwN z) (Nat.sub (Nat.sub l.2.2.2.2.2 (cond ka 0 (kwN x))) (cond kb 0 (kwN y)))))
theorem keySet_sum (xs : List Sig) : keySet xs = (xs.map keyWord).sum := by
  have go (a : Nat) : xs.foldl (fun v x => v+keyWord x) a = a+(xs.map keyWord).sum := by
    induction xs generalizing a with
    | nil => rfl
    | cons x xs ih => rw [List.foldl_cons,ih,List.map_cons,List.sum_cons,Nat.add_assoc]
  exact (go 0).trans (Nat.zero_add _)
theorem delTwo_sum (f : Decor → Nat) {ws : List Decor} {a b : Decor} (ha : a ∈ ws) (hb : b ∈ ws) (ne : a≠b) (ka kb : Bool) :
    ((delTwo ws a b ka kb).map f).sum = (ws.map f).sum - (cond ka 0 (f a)) - (cond kb 0 (f b)) := by
  have er {l : List Decor} {x : Decor} (hx : x ∈ l) : (l.map f).sum = f x + ((l.erase x).map f).sum := by
    have := ((List.perm_cons_erase hx).map f).sum_eq
    rwa [List.map_cons,List.sum_cons] at this
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm ne)).mpr hb
  have e1 := er ha
  have e2 := er hb
  have e3 := er hm
  cases ka <;> cases kb <;> simp only [delTwo,delOne,Bool.false_eq_true,ite_true,ite_false,cond_true,cond_false] <;> omega
theorem fastCost_good {u p k ws a b op ka kb} (ha : a∈ws) (hb : b∈ws) (ne : a≠b) (al : allowedB u op=true)
    (h : slowCost u p ws k a b op ka kb=true) :
    scalarPoolCut u p k ((delTwo ws a b ka kb).map Prod.fst) (movedChoice op a b)=true := by
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let z := bin op a.1 b.1
  let rest := delTwo ws a b ka kb
  have ck := keptCount const ws a b ka kb
  change ws.countP const - constantLoss const a ka - constantLoss const b kb ≤ rest.countP const at ck
  simp only [slowCost,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at h
  obtain ⟨⟨hu,hc⟩,hz⟩ := h
  have sum := delTwo_sum (unav u p) ha hb ne ka kb
  rw [hu] at sum
  have zs : ((delTwo ws a b ka kb).map (unav u p)).sum=0 := by omega
  have hs : (rest.map Prod.fst).all (availableB u p.domain p.wires)=true := by
    apply List.all_eq_true.mpr
    intro _ hm
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hm
    have v := List.sum_eq_zero_iff.mp zs _ (List.mem_map_of_mem hw)
    cases e : availableB u p.domain p.wires w.1
    · simp [unav,e] at v
    · rfl
  have opOK : (!(!availableB u p.domain p.wires z) || choiceOK u p.domain p.wires (movedChoice op a b))=true := by
    simp only [Bool.or_eq_true,Bool.and_eq_true] at hz
    rcases hz with hz | ⟨x,y⟩
    · simp [z,hz]
    · simp [choiceOK,movedChoice,x,y,al]
  change k+p.paid+(!availableB u p.domain p.wires z).toNat < p.bound+(ws.countP const - constantLoss const a ka -
        constantLoss const b kb+(isMaskedConstant p.domain z).toNat) at hc
  dsimp only [rest] at hs
  have ez : choiceVal (movedChoice op a b)=z := rfl
  simp only [scalarPoolCut,ez,hs,opOK,Bool.and_true,decide_eq_true_eq,List.countP_cons,
      List.countP_map,Function.comp_def]
  change k+p.paid+(!availableB u p.domain p.wires z).toNat <
      p.bound+(rest.countP const + if isMaskedConstant p.domain z then 1 else 0)
  cases hc' : isMaskedConstant p.domain z <;> simp [hc'] at hc ⊢ <;> omega

theorem zN_full (op : Nat) (a b : Sig) : zN op a.toNat b.toNat = (bin op a b).toNat := by
  have e (v : Sig) : nmask one.toNat v = v.toNat := by
    rw [nmask_eq]
    congr 1
    exact BitVec.and_allOnes
  have := zN_eq op one a b
  rwa [e,e,e] at this
theorem getW (ws : List Decor) (i : Nat) :
    (ws.map (fun w : Decor => w.1.toNat)).getD i 0 = (ws.getD i defaultDecor).1.toNat := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases ws[i]? with
  | none =>
    have z0 : zero.toNat=0 := by simp [zero]
    exact z0.symm
  | some v => rfl
theorem wire_ne {c : NodeContext} {i j} (nd : (c.2.2.1.map Prod.fst).Nodup)
    (hi : i<c.2.2.1.length) (hj : j<c.2.2.1.length) (hij : i≠j) : (contextWire c i).1 ≠ (contextWire c j).1 := by
  have gi : contextWire c i = c.2.2.1[i] := by simp [contextWire,List.getD_eq_getElem?_getD,hi]
  have gj : contextWire c j = c.2.2.1[j] := by simp [contextWire,List.getD_eq_getElem?_getD,hj]
  rw [gi,gj]
  intro e
  apply hij
  apply (List.Nodup.getElem_inj_iff nd (hi:=by simpa using hi) (hj:=by simpa using hj)).mp
  simpa using e
theorem link_sound {c : NodeContext} {fl i j op ka kb} (nd : (c.2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ xs ∈ c.2.2.2.2.2 tag, ys=xs.map BitVec.toNat)
    (hi : i<c.2.2.1.length) (hj : j<c.2.2.1.length) (hij : i≠j) (h : linkAt fl (laneOf c) i j op ka kb=true) :
    (c.2.2.2.2.2 (keySet (choiceVal (movedChoice op (contextWire c i) (contextWire c j)) ::
      (delTwo c.2.2.1 (contextWire c i) (contextWire c j) ka kb).map Prod.fst))).any (sameWords
      (choiceVal (movedChoice op (contextWire c i) (contextWire c j)) ::
      (delTwo c.2.2.1 (contextWire c i) (contextWire c j) ka kb).map Prod.fst))=true := by
  have mem (t) (ht : t<c.2.2.1.length) : contextWire c t ∈ c.2.2.1 := by
    simp [contextWire,List.getD_eq_getElem?_getD,ht]
  have hne := wire_ne nd hi hj hij
  have ha := mem i hi
  have hb := mem j hj
  have hab : contextWire c i ≠ contextWire c j := fun e => hne (congrArg Prod.fst e)
  have kv (v : Sig) := kept_value nd ha hb ka kb v
  have sum := delTwo_sum (fun w : Decor => keyWord w.1) ha hb hab ka kb
  have wi : contextWire c i = c.2.2.1.getD i defaultDecor := rfl
  have wj : contextWire c j = c.2.2.1.getD j defaultDecor := rfl
  simp only [linkAt,laneOf,force_eq,getW,←wi,←wj,zN_full] at h
  generalize contextWire c i=a at *
  generalize contextWire c j=b at *
  change Option.rec false _ (fl (keyWord (bin op a.1 b.1)+(((c.2.2.1.map (fun w : Decor => w.1.toNat)).map kwN).sum -
    (cond ka 0 (keyWord a.1)) - (cond kb 0 (keyWord b.1)))))=true at h
  have tot : ((c.2.2.1.map (fun w : Decor => w.1.toNat)).map kwN).sum = (c.2.2.1.map (fun w : Decor => keyWord w.1)).sum := by
    rw [List.map_map]
    rfl
  rw [tot,←sum] at h
  have tag : keySet (choiceVal (movedChoice op a b) :: (delTwo c.2.2.1 a b ka kb).map Prod.fst) =
      keyWord (bin op a.1 b.1)+((delTwo c.2.2.1 a b ka kb).map (fun w : Decor => keyWord w.1)).sum := by
    rw [keySet_sum,List.map_cons,List.sum_cons,List.map_map]
    rfl
  rw [←tag] at h
  generalize keySet (choiceVal (movedChoice op a b) :: (delTwo c.2.2.1 a b ka kb).map Prod.fst)=t at h ⊢
  cases hf : fl t with
  | none => simp [hf] at h
  | some ys =>
    obtain ⟨xs,hx,rfl⟩ := hfl t ys hf
    rw [hf] at h
    simp only [forceMap_eq,List.map_id',Bool.and_eq_true,List.all_eq_true,Bool.or_eq_true,anyEq_iff,Nat.beq_eq,Bool.not_eq_true'] at h
    obtain ⟨h1,h2,h3⟩ := h
    have back {v : Sig} (hv : v.toNat ∈ xs.map BitVec.toNat) : v ∈ xs := by
      obtain ⟨w,hw,e⟩ := List.mem_map.mp hv
      exact BitVec.toNat_inj.mp e ▸ hw
    apply List.any_eq_true.mpr
    refine ⟨xs,hx,?_⟩
    simp only [sameWords,Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq]
    constructor
    · intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact back h1
      · obtain ⟨hw,va,vb⟩ := (kv v).mp hv
        obtain ⟨w,hm,rfl⟩ := List.mem_map.mp hw
        rcases h2 _ (List.mem_map_of_mem hm) with ⟨x,y⟩ | ⟨x,y⟩ | x
        · rcases va with va | va
          · exact absurd (BitVec.toNat_inj.mp y) va
          · simp [va] at x
        · rcases vb with vb | vb
          · exact absurd (BitVec.toNat_inj.mp y) vb
          · simp [vb] at x
        · exact back x
    · intro v hv
      rcases h3 _ (List.mem_map_of_mem hv) with x | ⟨⟨x,y⟩,m⟩
      · exact List.mem_cons.mpr (Or.inl (BitVec.toNat_inj.mp x))
      · refine List.mem_cons_of_mem _ ((kv v).mpr ⟨?_,?_,?_⟩)
        · obtain ⟨w,hw,e⟩ := List.mem_map.mp m
          exact BitVec.toNat_inj.mp e ▸ List.mem_map_of_mem hw
        · rcases x with x | x
          · exact Or.inr x
          · refine Or.inl fun e => ?_
            subst e
            simp at x
        · rcases y with x | x
          · exact Or.inr x
          · refine Or.inl fun e => ?_
            subst e
            simp at x
noncomputable def fallbackAt (fl : Nat → Option (List Nat)) (l : Lane) (i j op : Nat) (ka kb : Bool) : Bool :=
  or (and (and (Nat.ble (Nat.succ i) l.2.1) (and (Nat.ble (Nat.succ j) l.2.1) (and (Nat.ble (Nat.succ op) l.2.2.1) (not (Nat.beq i j)))))
    (or (l.2.2.2.1.any fun s => fastCost s i j op ka kb) (linkAt fl l i j op ka kb))) (checkAt l.1 i j op ka kb)
theorem fallback_sound {c : NodeContext} {fl i j op ka kb} (nd : (c.2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ xs ∈ c.2.2.2.2.2 tag, ys=xs.map BitVec.toNat)
    (h : fallbackAt fl (laneOf c) i j op ka kb=true) :
    checkAt c i j op ka kb=true := by
  simp only [fallbackAt,Bool.or_eq_true,Bool.and_eq_true] at h
  rcases h with ⟨⟨hi,hj,ho,hn⟩,h | h⟩ | h
  · have hi := Nat.ble_eq.mp hi
    have hj := Nat.ble_eq.mp hj
    have ho := Nat.ble_eq.mp ho
    change Nat.succ i ≤ c.2.2.1.length at hi
    change Nat.succ j ≤ c.2.2.1.length at hj
    change Nat.succ op ≤ cond c.2.2.2.1.2 4 2 at ho
    have al : allowedB c.2.2.2.1.2 op=true := by
      cases hu : c.2.2.2.1.2 <;> simp [hu] at ho <;> simp [allowedB] <;> omega
    have mem (t) (ht : t<c.2.2.1.length) : contextWire c t ∈ c.2.2.1 := by
      simp [contextWire,List.getD_eq_getElem?_getD,ht]
    obtain ⟨_,hm,ok⟩ := List.any_eq_true.mp h
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm
    have hne := wire_ne nd hi hj (fun e => by simp [e] at hn)
    have closed := fastCost_good (mem i hi) (mem j hj) (fun e => hne (congrArg Prod.fst e)) al (fast_slow ok)
    have cut : c.2.2.2.2.1.any (fun p => scalarPoolCut c.2.2.2.1.2 p (c.1-1)
        ((delTwo c.2.2.1 (contextWire c i) (contextWire c j) ka kb).map Prod.fst)
        (movedChoice op (contextWire c i) (contextWire c j)))=true :=
      List.any_eq_true.mpr ⟨p,hp,closed⟩
    simp only [checkAt,evalMove,closeChild,cut,Bool.or_true]
    repeat' split
    all_goals rfl
  · have cut := link_sound nd hfl (Nat.ble_eq.mp hi) (Nat.ble_eq.mp hj) (fun e => by simp [e] at hn) h
    simp only [checkAt,evalMove,closeChild,cut,Bool.true_or]
    repeat' split
    all_goals rfl
  · exact h
def swapIdx (v t : Nat) : Nat := cond (Nat.beq t (v &&& 15)) (v >>> 4) (cond (Nat.beq t (v >>> 4)) (v &&& 15) t)
def validSwap (v : Nat) : Bool := and (Nat.ble ((v &&& 15)+1) (v >>> 4)) (Nat.ble ((v >>> 4)+1) 9)
set_option maxRecDepth 8192 in
theorem swap_table : ∀ v : Fin 144, validSwap v.val=true → ∀ t : Fin 9, swapIdx v.val t.val<9 ∧
    wordMove (swapRows v.val) (inputs.getD t.val zero) = inputs.getD (swapIdx v.val t.val) zero := by decide +kernel
theorem swap_input {v t : Nat} (hv : validSwap v=true) (ht : t<9) : swapIdx v t<9 ∧
    wordMove (swapRows v) (inputs.getD t zero) = inputs.getD (swapIdx v t) zero := by
  have lt : v<144 := by
    simp only [validSwap,Bool.and_eq_true,Nat.ble_eq,Nat.shiftRight_eq_div_pow] at hv
    omega
  exact swap_table ⟨v,lt⟩ hv ⟨t,ht⟩
def idxOf (perm : List Nat) (t : Nat) : Nat := perm.foldl (fun t v => swapIdx v t) t
theorem idx_move {perm : List Nat} (ok : perm.all validSwap=true) {t : Nat} (ht : t<9) :
    movedWord (perm.map swapRows).reverse (inputs.getD t zero) = inputs.getD (idxOf perm t) zero := by
  rw [movedWord,List.foldr_reverse,List.foldl_map]
  induction perm generalizing t with
  | nil => rfl
  | cons v perm ih =>
    simp only [List.all_cons,Bool.and_eq_true] at ok
    obtain ⟨lt,e⟩ := swap_input ok.1 ht
    rw [List.foldl_cons,e,ih ok.2 lt]
    rfl
noncomputable def decodeN : Nat → Nat → List Nat → List Nat
  | 0,_,ws => ws
  | n+1,bits,ws => force (zN ((bits >>> 8) &&& 3) (ws.getD (bits &&& 15) 0) (ws.getD ((bits >>> 4) &&& 15) 0))
      fun z => decodeN n (bits >>> 10) (ws++[z])
theorem decodeN_eq (F : Sig → Nat) (F0 : F zero=0) (Fb : ∀ op a b, F (bin op a b)=zN op (F a) (F b))
    (n bits : Nat) (ds : List Decor) :
    (decodeBank n bits ds).map (fun w => F w.1) = decodeN n bits (ds.map fun w => F w.1) := by
  have gd (ds : List Decor) (i : Nat) : (ds.map fun w => F w.1).getD i 0 = F (ds.getD i defaultDecor).1 := by
    simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
    cases ds[i]? with
    | none => exact F0.symm
    | some v => rfl
  induction n generalizing bits ds with
  | zero => rfl
  | succ n ih =>
    rw [decodeN,force_eq,decodeBank,ih,gd,gd,←Fb,List.map_append]
    rfl
theorem selectLive_map {α β : Type} (f : α → β) (bits : Nat) (ws : List α) :
    (selectLive bits ws).map f = selectLive bits (ws.map f) := by
  induction ws generalizing bits with
  | nil => rfl
  | cons w ws ih =>
    rw [List.map_cons,selectLive,selectLive]
    split
    · rw [List.map_cons,ih]
    · exact ih _
noncomputable def fastState (g : Forest) (k i : Nat) (perm : List Nat) : List Nat :=
  let raw := (selected g.mask).map fun e => (inputs.getD (idxOf perm e.1) zero).toNat
  let (_,depth,_,_,_,_,_,data) := g.levels k
  let len := 10*depth
  force (forestRecord (g.levels k) (selected g.mask).length i) fun rec =>
  selectLive (rec >>> len) (decodeN depth (rec &&& ((1 <<< len)-1)) raw)
theorem fastState_eq (g : Forest) (k i : Nat) {perm : List Nat} (ok : perm.all validSwap=true) :
    fastState g k i perm = ((stateSet g k i).map (movedWord (perm.map swapRows).reverse)).map BitVec.toNat := by
  let ms := (perm.map swapRows).reverse
  let F (a : Sig) : Nat := (movedWord ms a).toNat
  have F0 : F zero=0 := by
    change (movedWord ms zero).toNat=0
    rw [moved_eq_rename,(rename_constants _).1]
    simp [zero]
  have Fb (op a b) : F (bin op a b)=zN op (F a) (F b) := by
    change (movedWord ms (bin op a b)).toNat = zN op (movedWord ms a).toNat (movedWord ms b).toNat
    rw [zN_full,moved_eq_rename,rename_bin,moved_eq_rename,moved_eq_rename]
  have raw : (wiresOf g).map (fun w => F w.1) = (selected g.mask).map fun e => (inputs.getD (idxOf perm e.1) zero).toNat := by
    simp only [wiresOf,rawDecor,List.map_map]
    apply List.map_congr_left
    rintro ⟨j,a⟩ hm
    obtain ⟨hj,rfl⟩ := selected_entry hm
    exact congrArg BitVec.toNat (idx_move ok hj)
  have len : (wiresOf g).length = (selected g.mask).length := by simp [wiresOf,rawDecor]
  unfold fastState stateSet readNode
  rcases g.levels k with ⟨a,depth,b,c,d,e,f,data⟩
  simp only [force_eq,storedDepth,len]
  rw [List.map_map,List.map_map,selectLive_map,←raw,←decodeN_eq F F0 Fb]
  rfl
noncomputable def linkedFast (g : Forest) (k : Nat) (pair : Nat × Nat) : Option (List Nat) :=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.autos[pair.2]?).bind fun perm => cond (perm.all validSwap) (some (fastState g k pair.1 perm)) none
noncomputable def flOf (g : Forest) (k : Nat) : Nat → Option (List Nat) := fun tag => (g.index k tag).bind (linkedFast g (k-1))
noncomputable def batchMove (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) (i j op : Nat) (ka kb : Bool) :=
  let (k,n,r,_,cov) := b
  let len := 1+(n-(if ka then 0 else 1)-(if kb then 0 else 1))
  if len>k then true else
    let a := laneWire b i
    let b' := laneWire b j
    let z := packedOp op a b'
    let mask := fullMarks r (takePacked cov (packedColumn (!u) a) (packedColumn (!u) b') ka kb ||| packedColumn (!u) z)
    onMarks (fun c => fallbackAt fl c i j op ka kb) mask xs

theorem batchMove_at {fl u} (k n) (xs : List NodeContext) {i j op : Nat} {ka kb}
    (hi : i<n) (hj : j<n) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (mode : xs[q].2.2.2.1.2=u) (nd : (xs[q].2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat)
    (pass : batchMove fl u (makeBatch k n xs) (xs.map laneOf) i j op ka kb=true) :
    checkAt xs[q] i j op ka kb=true := by
  let len := 1+(n-(if ka then 0 else 1)-(if kb then 0 else 1))
  have eval : checkAt xs[q] i j op ka kb =
      if len>k then true else if combField xs[q] (!u) ka kb op i j != BitVec.allOnes 152 then true
      else if !properB (dbin op (contextWire xs[q] i) (contextWire xs[q] j)).1 ||
        xs[q].2.2.1.any (fun v => v.1==(dbin op (contextWire xs[q] i) (contextWire xs[q] j)).1)
      then true else closeChild u xs[q].2.2.2.2.1 xs[q].2.2.2.2.2 (k-1)
        ((delTwo xs[q].2.2.1 (contextWire xs[q] i) (contextWire xs[q] j) ka kb).map Prod.fst)
        (movedChoice op (contextWire xs[q] i) (contextWire xs[q] j)) := by
    simp only [checkAt,evalMove,budget,arity,mode,len,combField] <;> rfl
  by_cases small : len>k
  · simp [eval,small]
  · let r := units xs.length
    let a := laneWire (makeBatch k n xs) i
    let b := laneWire (makeBatch k n xs) j
    let cov := packedCov (fun c : NodeContext => c.2.2.2.1.1) xs
    change (if len>k then true else onMarks _ (fullMarks r
       (takePacked cov (packedColumn (!u) a) (packedColumn (!u) b) ka kb |||
        packedColumn (!u) (packedOp op a b))) (xs.map laneOf)) = true at pass
    rw [if_neg small] at pass
    have ca : a = _ := laneWire_at k n xs hi
    have cb : b = _ := laneWire_at k n xs hj
    dsimp only [r,cov] at pass
    rw [ca,cb,packed_op,packed_column,packed_column,packed_column,takePacked_ok,lanes_or] at pass
    by_cases hit : combField xs[q] (!u) ka kb op i j = BitVec.allOnes 152
    · apply fallback_sound nd hfl
      have m := marked_ok _ _ _ q (by simpa using hq) (by
        rw [mark_at _ _ _ hq]
        exact beq_iff_eq.mpr hit) pass
      simpa only [List.getElem_map] using m
    · rw [eval,if_neg small,if_pos (bne_iff_ne.mpr hit)]

noncomputable def batchPair (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) (i j op : Nat) :=
  let f := batchMove fl u b xs i j op
  f false false && f true false && f false true && f true true
noncomputable def batchRow (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) (i : Nat) (js : List Nat) :=
    js.all (fun j => (opsOf u).all (batchPair fl u b xs i j))
noncomputable def batchRows (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) : List Nat → Bool
  | [] => true
  | i::js => batchRow fl u b xs i js && batchRows fl u b xs js

theorem batchRows_at {fl u} (k n) (xs : List NodeContext) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (mode : xs[q].2.2.2.1.2=u) (nd : (xs[q].2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat)
    (js : List Nat)
    (bounds : ∀ j ∈ js, j<n) (allRows : batchRows fl u (makeBatch k n xs) (xs.map laneOf) js=true) :
    testAll xs[q] (js.map (contextWire xs[q])) = true := by
  induction js with
  | nil => rfl
  | cons i js ih =>
    simp only [batchRows,Bool.and_eq_true,batchRow,List.all_eq_true] at allRows
    simp only [List.map_cons,testAll,testRow,Bool.and_eq_true,List.all_eq_true,List.mem_map]
    have hi := bounds i List.mem_cons_self
    refine ⟨?_,ih (fun j hj => bounds j (List.mem_cons_of_mem _ hj)) allRows.2⟩
    rintro _ ⟨j,hj,rfl⟩ op hop
    have hj' := bounds j (List.mem_cons_of_mem _ hj)
    rw [mode] at hop
    have pass := allRows.1 j hj op hop
    have check := @batchMove_at fl u k n xs i j op
    simp only [batchPair,Bool.and_eq_true] at pass
    simp only [testPair,Bool.and_eq_true]
    exact ⟨⟨⟨check hi hj' hq budget arity mode nd hfl pass.1.1.1,check hi hj' hq budget arity mode nd hfl pass.1.1.2⟩,
      check hi hj' hq budget arity mode nd hfl pass.1.2⟩,check hi hj' hq budget arity mode nd hfl pass.2⟩

noncomputable def runBatch (fl : Nat → Option (List Nat)) (u : Bool) (k n : Nat) (xs : List NodeContext) :=
    batchRows fl u (makeBatch k n xs) (xs.map laneOf) (List.range n)
theorem runBatch_at {fl u k n} {xs : List NodeContext} {q} (hq : q<xs.length)
    (hb : xs[q].1=k) (ha : xs[q].2.1=n) (hm : xs[q].2.2.2.1.2=u) (nd : (xs[q].2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat)
    (hn : xs[q].2.2.1.length=n)
    (pass : runBatch fl u k n xs=true) : testAll xs[q] xs[q].2.2.1=true := by
  have all := batchRows_at k n xs hq hb ha hm nd hfl (List.range n) (fun _ => List.mem_range.mp) pass
  have eq : (List.range n).map (contextWire xs[q]) = xs[q].2.2.1 := by
    apply List.ext_getElem
    · simp [hn]
    · intro i h1 h2
      simp [contextWire,List.getD_eq_getElem?_getD,h2]
  rwa [eq] at all

def contextOf (g : Forest) (k i : Nat) : NodeContext :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let rules := (forestHints (g.levels k) raw.length i).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  (k,ws.length,ws,preCov g.mode ws,rules,ls)

theorem flOf_ok (g : Forest) (k i tag : Nat) (ys) (h : flOf g k tag=some ys) :
    ∃ xs ∈ (contextOf g k i).2.2.2.2.2 tag, ys=xs.map BitVec.toNat := by
  change ∃ xs ∈ ((g.index k tag).bind (linkedSet g (k-1))).toList, _
  unfold flOf at h
  cases hp : g.index k tag with
  | none => simp [hp] at h
  | some pair =>
    simp only [hp,Option.bind_some,linkedFast] at h
    simp only [Option.bind_some,linkedSet]
    split at h
    · contradiction
    next v =>
      cases ha : g.autos[pair.2]? with
      | none => simp [ha] at h
      | some perm =>
        simp only [ha,Option.bind_some] at h
        cases hv : perm.all validSwap with
        | false => simp [hv] at h
        | true =>
          simp only [hv,cond_true,Option.some.injEq] at h
          refine ⟨(stateSet g (k-1) pair.1).map (movedWord (perm.map swapRows).reverse),?_,?_⟩
          · simp [v]
          · exact h.symm.trans (fastState_eq g _ _ hv)

def prelim (T : Sig) (c : NodeContext) :=
  let ws := c.2.2.1.map Prod.fst
  decide ws.Nodup && !(ws.contains T)
theorem from_context (g : Forest) (k i : Nat) :
    nodeVerified g k i = (prelim (targetOf g) (contextOf g k i) &&
      (if k=0 then true else testAll (contextOf g k i) (contextOf g k i).2.2.1)) := rfl

theorem makeBlock {g k start n} (h : ∀ (i : Nat), start ≤ i → i < start + n → nodeVerified g k i = true) :
    block g k start n=true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [block,Bool.and_eq_true]
    exact ⟨h _ (by omega) (by omega),ih (fun i le lt => h i le (by omega))⟩

def contexts (g : Forest) (k start n : Nat) :=
  ((List.range n).map (start+·)).map (contextOf g k)
def header (g : Forest) (k start n ar : Nat) :=
  (contexts g k start n).all (fun c => c.2.1==ar && prelim (targetOf g) c)
noncomputable def rowCut (g : Forest) (k start n ar lo len : Nat) :=
  let xs := contexts g k start n
  let b := makeBatch k ar xs
  forceLanes xs fun ys => (List.range len).all (fun d =>
    let i := lo+d
    batchRow (flOf g k) g.mode b ys i (List.range' (i+1) (ar-(i+1))))
theorem rowCut_at {g k start n ar lo len} (h : rowCut g k start n ar lo len=true)
    (i : Nat) (l : lo ≤ i) (r : i < lo+len) :
    batchRow (flOf g k) g.mode (makeBatch k ar (contexts g k start n)) ((contexts g k start n).map laneOf)
      i (List.range' (i+1) (ar-(i+1)))=true := by
  simp only [rowCut,forceLanes_eq] at h
  have ha := List.all_eq_true.mp h (i-lo) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le l] using ha

theorem rowCut_merge {g k start n ar lo a b}
    (h : rowCut g k start n ar lo a=true) (t : rowCut g k start n ar (lo+a) b=true) :
    rowCut g k start n ar lo (a+b)=true := by
  simp only [rowCut,forceLanes_eq]
  apply List.all_eq_true.mpr
  intro j hj
  have jlt := List.mem_range.mp hj
  by_cases first : j<a
  · exact rowCut_at h (lo+j) (by omega) (by omega)
  · exact rowCut_at t (lo+j) (by omega) (by omega)

theorem cutsRun {g k start n ar} (h : rowCut g k start n ar 0 ar=true) :
    runBatch (flOf g k) g.mode k ar (contexts g k start n)=true := by
  let xs := contexts g k start n
  have go (lo num : Nat) (eq : lo+num=ar) :
      batchRows (flOf g k) g.mode (makeBatch k ar xs) (xs.map laneOf) (List.range' lo num)=true := by
    induction num generalizing lo with
    | zero => rfl
    | succ num ih =>
      simp only [List.range'_succ,batchRows,Bool.and_eq_true]
      refine ⟨?_,ih (lo+1) (by omega)⟩
      have ok := rowCut_at h lo (by omega) (by omega)
      simpa only [show ar-(lo+1)=num by omega] using ok
  unfold runBatch
  rw [List.range_eq_range']
  exact go 0 ar (by omega)

theorem cutsBlock {g k start n ar} (hd : header g k start n ar=true)
    (h : rowCut g k start n ar 0 ar=true) : block g k start n=true := by
  apply makeBlock
  intro i lo hi
  let xs := contexts g k start n
  have hm : contextOf g k i ∈ xs := by
    apply List.mem_map.mpr
    exact ⟨i,List.mem_map.mpr ⟨i-start,List.mem_range.mpr (by omega),by omega⟩,rfl⟩
  obtain ⟨q,hq,e⟩ := List.getElem_of_mem hm
  have one := List.all_eq_true.mp hd _ hm
  simp only [Bool.and_eq_true,beq_iff_eq] at one
  have hb : xs[q].1=k := by rw [e]; rfl
  have ha : xs[q].2.1=ar := e ▸ one.1
  have nd : (xs[q].2.2.1.map Prod.fst).Nodup := by
    have p := one.2
    simp only [prelim,Bool.and_eq_true,decide_eq_true_eq] at p
    rw [e]
    exact p.1
  have hfl : ∀ tag ys, flOf g k tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat := by
    rw [e]
    exact fun tag ys h => flOf_ok g k i tag ys h
  have hm : xs[q].2.2.2.1.2=g.mode := by rw [e]; rfl
  have hn : xs[q].2.2.1.length=ar := by rw [e]; exact one.1
  rw [from_context,Bool.and_eq_true]
  refine ⟨one.2,?_⟩
  split
  · rfl
  · exact e ▸ runBatch_at hq hb ha hm nd hfl hn (cutsRun h)

def boxes (g : Forest) (k start n ar lo num : Nat) : Nat → Prop
  | 0 => rowCut g k start n ar lo num=true
  | d+1 => boxes g k start n ar lo (num/2) d ∧ boxes g k start n ar (lo+num/2) (num-num/2) d
theorem boxesCut {g k start n ar lo num d} (h : boxes g k start n ar lo num d) :
    rowCut g k start n ar lo num=true := by
  induction d generalizing lo num with
  | zero => exact h
  | succ d ih =>
    have v := rowCut_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self num 2)] using v

def cells (g : Forest) (k start n ar rows : Nat) : Nat → Prop
  | 0 => header g k start n ar=true ∧ boxes g k start n ar 0 ar rows
  | d+1 => cells g k start (n/2) ar rows d ∧ cells g k (start+n/2) (n-n/2) ar rows d
theorem cellsBlock {g k start n ar rows d} (h : cells g k start n ar rows d) :
    block g k start n=true := by
  induction d generalizing start n with
  | zero => exact cutsBlock h.1 (boxesCut h.2)
  | succ d ih =>
    have v := block_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self n 2)] using v

def listPieces {α} (f : α → Bool) (xs : List α) : Nat → Prop
  | 0 => xs.all f=true
  | d+1 => listPieces f (xs.take (xs.length/2)) d ∧ listPieces f (xs.drop (xs.length/2)) d
theorem pieces_all {α f xs d} (h : @listPieces α f xs d) : xs.all f=true := by
  induction d generalizing xs with
  | zero => exact h
  | succ d ih =>
    have ap : ((xs.take (xs.length/2)) ++ (xs.drop (xs.length/2))).all f=true := by
      simp only [List.all_append,ih h.1,ih h.2,Bool.and_self]
    simpa only [List.take_append_drop] using ap
theorem slice_self {u} {raw : List Sig} {T : Sig} {L : Nat} (pT : proper T) (h : Lower u raw T L) :
    Slice u raw T one L := by
  refine ⟨id,raw,fun r => bit_one r,fun a ha => ?_,observe_proper pT,h⟩
  exact Or.inl (List.mem_map_of_mem ha)

theorem plainA {u} {m q cap : Nat} {prior : Nat → Nat} (low : ∀ q, Lower u (varsX q) (graphGoal q) (prior q))
    (e : (graphGoal q == graphGoal m && (varsX q == vars m) && (prior q == cap+1) && properB (graphGoal m) &&
      decide (vars m).Nodup && poolCut u one (cap+1) cap 0 (vars m) (vars m)) = true) :
    Impossible u (graphGoal m) cap (vars m).toFinset := by
  simp only [Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at e
  obtain ⟨⟨⟨⟨⟨e1,e2⟩,e3⟩,e4⟩,e5⟩,e6⟩ := e
  have h := low q
  rw [e1,e2,e3] at h
  exact poolCut_sound (slice_self (proper_of _ e4) h) [] rfl e5 e6

theorem cut_root {u} {m cap : Nat} {prior : Nat → Nat} {ws : List Sig}
    (low : ∀ q, Lower u (varsX q) (graphGoal q) (prior q)) (ci : ColumnInfo)
    (ok : colCheck m ci prior = true)
    (cut : (decide ws.Nodup && poolCut u (subcube ci.1 ci.2.1) ci.2.2.2.2 cap 0 (varsX (rawMask m ci)) ws)=true) :
    Impossible u (graphGoal m) cap ws.toFinset := by
  simp only [Bool.and_eq_true,decide_eq_true_eq] at cut
  exact poolCut_sound (col_sound ci prior low ok) [] rfl cut.1 cut.2

theorem index_root {u} {g : Forest} {m cap i : Nat} {prior : Nat → Nat} {ws : List Sig}
    (hm : g.mask=m) (hu : g.mode=u) (low : ∀ q, Lower u (varsX q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g cap)
    (idx : indexedRoot g cap i ws = true) : Impossible u (graphGoal m) cap ws.toFinset := by
  subst hm
  subst hu
  exact root_index low geom blocks (Nat.le_refl _) idx

def essOK (m hints : Nat) : Bool :=
  let xs := graphPairs m hints
  properB (graphGoal m) && checkEssential (graphGoal m) (vars m) xs && (xs.map Prod.fst == vars m)
theorem plain_low {u} {m hints cap : Nat} (ok : essOK m hints = true)
    (a : Impossible u (graphGoal m) cap (vars m).toFinset) : Lower u (vars m) (graphGoal m) (cap+1) := by
  simp only [essOK,Bool.and_eq_true,beq_iff_eq] at ok
  apply lower_impossible (proper_of _ ok.1.1) (essential_plain ok.1.2).1 (essential_plain ok.1.2).2 _ a
  intro v hv
  apply essential_ok ok.1.2 v
  rw [ok.2]
  exact List.mem_toFinset.mpr hv

def nineInputs : List Sig := vars 127
def sampleNine (r : Row) (i : Fin 7) : Bool := bit r (nineInputs.getD i.val zero)
def nineEdge (x : Fin 7 → Bool) := (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 4) || (x 2 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 3 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 4 && x 6)

theorem nineTable : ∀ r : Row, bit r graph = nineEdge (sampleNine r) := by decide +kernel
theorem nineList : List.ofFn (fun i : Fin 7 => nineInputs.getD i.val zero) = nineInputs := rfl
theorem nineSampled (r : Row) : List.ofFn (sampleNine r) = nineInputs.map (bit r) := by
  rw [← nineList, List.map_ofFn]
  rfl

theorem nineEval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates nineInputs).getD i zero) =
      (C.wires (List.ofFn (sampleNine r))).getD i false := by
  rw [← b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),nineSampled]
  rfl
def neighborRow (i : Fin 7) : Nat := [3,4,4,0,0,0,0].getD i.val 0
def absentRowRow (i : Fin 7) : Row := Fin.ofNat 512 (1 <<< neighborRow i)
def presentRowRow (i : Fin 7) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< neighborRow i))

set_option maxHeartbeats 1000000 in
theorem requiredInputs :
    (∀ i : Fin 7, bit (absentRowRow i) graph ≠ bit (presentRowRow i) graph) ∧
    (∀ i j : Fin 7, i ≠ j →
      bit (absentRowRow i) (nineInputs.getD j.val zero) =
      bit (presentRowRow i) (nineInputs.getD j.val zero)) := by decide +kernel

theorem binaryLower (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : PEqualNP.MetaComplexity.circuitFun 7 C = nineEdge)
    (no : ∀ k, k ≤ 11 → ¬Live true graph k nineInputs.toFinset) :
    12 ≤ C.gates.countP (fun g => !isNot g) := by
  have goalEq : (execute C.gates nineInputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (nineEval C legal C.output r).trans ((congrFun computes (sampleNine r)).trans (nineTable r).symm)
  have out := get_rep (u:=true) (execute C.gates nineInputs) C.output
  rw [goalEq] at out
  unfold Repr at out
  have pg : bit 0 graph = false := by decide +kernel
  rw [nrm_id pg] at out
  obtain ⟨k,S,hk,run,sub⟩ := extract C.gates nineInputs legal (by simp) graph_proper
    (out.resolve_right (fun h => h graph_proper))
  have ns : nineInputs.all plainWord = true := by decide +kernel
  rw [nrm_map ns] at sub
  have idx (a : Sig) (ha : a ∈ nineInputs) : ∃ i : Fin 7, nineInputs.getD i.val zero = a := by
    rw [←nineList] at ha
    exact List.mem_ofFn.mp ha
  have eq : S = nineInputs.toFinset := by
    ext a
    constructor
    · exact fun h => List.mem_toFinset.mpr (sub a h)
    · intro ha
      obtain ⟨i,rfl⟩ := idx a (List.mem_toFinset.mp ha)
      apply raw_required run nineInputs (nineInputs.getD i.val zero) sub (absentRowRow i) (presentRowRow i)
        (requiredInputs.1 i)
      intro v hv hn
      obtain ⟨j,rfl⟩ := idx v hv
      apply requiredInputs.2 i j
      rintro rfl
      exact hn rfl
  by_contra! small
  exact no k (by omega) (eq ▸ run)

def g41Y : Array (Bits × Bits) := #[(((((0xffffffff <<< 60) ||| 0xfffffffffffffff) <<< 60) ||| 0xfffffffffffffdd),((((0xffffffff <<< 60) ||| 0xfffffffffffffff) <<< 60) ||| 0xfffffffffffffd1)),(0x0,0x0),(0x0,0x0),(((((0xffffffff <<< 60) ||| 0xfffffffffffffff) <<< 60) ||| 0xfffffffffffffe7),0x24),(0x0,0x0),(0x3a,0xa),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g41C : List ColumnInfo := []
def g41A : List (List Nat) := [[]]
def g41D3 (j : Nat) : Nat := 0x7
def g41L : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,g41D3)
  | _ => emptyPacking
def g41I (_ _ : Nat) : Option (Nat × Nat) := none
def g41 : Forest := ⟨41,3,fun i => g41Y[i]?.getD (0,0),g41C,g41A,g41L,g41I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g41P3_0 : block g41 3 0 1=true := by
  apply cellsBlock (ar:=3) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g41B3 : block g41 3 0 1=true := g41P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g41T : checkedTables g41 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g41 0 0 0 = true)
  · exact (rfl : block g41 1 0 0 = true)
  · exact (rfl : block g41 2 0 0 = true)
  · exact g41B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g41G : graphValid g41 (boundsBefore []) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low41 : Lower true (varsX 41) (graphGoal 41) 4 := lower_forest (g:=g41) (i:=0) (hints:=3) (before_sound [] baseKnown) g41G g41T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K41 := extendKnown [] 4 [(41,[]),(73,[101]),(81,[101,67]),(84,[101,67,32])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V41 : Known true K41 := extend_ok (m:=41) baseKnown low41 (by decide +kernel)
def g27Y : Array (Bits × Bits) := #[(((((0xffffffff <<< 60) ||| 0xfffffffffffffff) <<< 60) ||| 0xffffffffffd87f7),((((0xffffffff <<< 60) ||| 0xfffffffffffffff) <<< 60) ||| 0xffffffffffc8215)),(0x2f838,0x9ab8),(0x0,0x0),(((((0xffffffff <<< 60) ||| 0xfffffffffffffff) <<< 60) ||| 0xfffffffffff01bb),0x355aa),(0x3fe4c,0x36540),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g27C : List ColumnInfo := []
def g27A : List (List Nat) := [[]]
def g27D3 (j : Nat) : Nat := 0xf
def g27L : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,g27D3)
  | _ => emptyPacking
def g27I (_ _ : Nat) : Option (Nat × Nat) := none
def g27 : Forest := ⟨27,3,fun i => g27Y[i]?.getD (0,0),g27C,g27A,g27L,g27I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g27P3_0 : block g27 3 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g27B3 : block g27 3 0 1=true := g27P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g27T : checkedTables g27 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g27 0 0 0 = true)
  · exact (rfl : block g27 1 0 0 = true)
  · exact (rfl : block g27 2 0 0 = true)
  · exact g27B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g27G : graphValid g27 (boundsBefore K41) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low27 : Lower true (varsX 27) (graphGoal 27) 4 := lower_forest (g:=g27) (i:=0) (hints:=67) (before_sound K41 V41) g27G g27T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K27 := extendKnown K41 4 [(27,[]),(29,[33]),(53,[83,33]),(54,[83,16,32]),(58,[67,49,16,80]),(90,[96]),(99,[67,100,83]),(101,[100,83,33]),(106,[67,100,48,80]),(108,[100,48,16,81,32]),(114,[49,99,16,80]),(120,[65,48,97,80])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V27 : Known true K27 := extend_ok (m:=27) V41 low27 (by decide +kernel)
def g61Y : Array (Bits × Bits) := #[(((((0xffffffff <<< 60) ||| 0xfffffffffffffff) <<< 60) ||| 0xfffffe0fc7f2971),((((0xffffffff <<< 60) ||| 0xfffffffffffffff) <<< 60) ||| 0xfffffc014280111)),(0x0,0x0),(0x10079816da,0x1445b82658),(0x1f081ee3ac,0x11081560ac),(((((0xffffffff <<< 60) ||| 0xfffffffffffffff) <<< 60) ||| 0xfffffe00fe3dc8b),0x298a47d882),(0x3ff002d654,0x2ee3429640),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g61C : List ColumnInfo := [(32,0,29,0,4),(16,4,41,0,4),(20,0,41,0,4),(8,0,53,0,4)]
def g61A : List (List Nat) := [[],[83]]
def g61D4 (j : Nat) : Nat := 0x4fd5120
def g61D5 (j : Nat) : Nat := 0x88401090fd42fe20fd20
def g61H5 (j : Nat) : Nat := 0x600000000000
def g61D6 (j : Nat) : Nat := 0x5889f
def g61H6 (j : Nat) : Nat := ((0x28a200900000368 <<< 60) ||| 0xa00)
def g61L : Nat → Packing
  | 4 => (1,2,2,0,0,0,0,g61D4)
  | 5 => (3,1,2,0,0,4,0,g61D5)
  | 6 => (1,0,2,0,0,0,0,g61D6)
  | _ => emptyPacking
def g61I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 8 0 6 1 1 g61H5
  | 6 => lookupWord 1 17 0 7 2 1 g61H6
  | _ => fun _ => none
def g61 : Forest := ⟨61,6,fun i => g61Y[i]?.getD (0,0),g61C,g61A,g61L,g61I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g61P4_0 : block g61 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g61B4 : block g61 4 0 1=true := g61P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g61P5_0 : block g61 5 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g61B5 : block g61 5 0 3=true := g61P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g61P6_0 : block g61 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g61B6 : block g61 6 0 1=true := g61P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g61T : checkedTables g61 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g61 0 0 0 = true)
  · exact (rfl : block g61 1 0 0 = true)
  · exact (rfl : block g61 2 0 0 = true)
  · exact (rfl : block g61 3 0 0 = true)
  · exact g61B4
  · exact g61B5
  · exact g61B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g61G : graphValid g61 (boundsBefore K27) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low61 : Lower true (varsX 61) (graphGoal 61) 7 := lower_forest (g:=g61) (i:=0) (hints:=1027) (before_sound K27 V27) g61G g61T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K61 := extendKnown K27 7 [(61,[]),(118,[82,98,50,64,16]),(124,[82,66,50,96])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V61 : Known true K61 := extend_ok (m:=61) V27 low61 (by decide +kernel)
def g91Y : Array (Bits × Bits) := #[(((((0xffffffff <<< 60) ||| 0xfffffffffffffff) <<< 60) ||| 0xffffff00787e4cb),((((0xffffffff <<< 60) ||| 0xfffffffffffffff) <<< 60) ||| 0xffffff00282200b)),(0x406fa09b4,0x696da61b0),(0x0,0x0),(((((0xffffffff <<< 60) ||| 0xfffffffffffffff) <<< 60) ||| 0xffffff8f90389b1),0x939358990),(0xf01fc1e16,0x921251c04),(0x0,0x0),(0xffe007368,0x6c4404260),(0x0,0x0),(0x0,0x0)]
def g91C : List ColumnInfo := [(16,2,73,0,4),(64,0,27,0,4),(10,0,81,0,4),(1,0,90,0,4)]
def g91A : List (List Nat) := [[]]
def g91D4 (j : Nat) : Nat := 0x5bd4940
def g91D5 (j : Nat) : Nat := 0x1083fd40
def g91H5 (j : Nat) : Nat := 0x28000000000
def g91D6 (j : Nat) : Nat := 0x6c09f
def g91H6 (j : Nat) : Nat := 0x0
def g91L : Nat → Packing
  | 4 => (1,2,2,0,0,0,0,g91D4)
  | 5 => (1,1,2,0,0,0,0,g91D5)
  | 6 => (1,0,2,0,0,0,0,g91D6)
  | _ => emptyPacking
def g91I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 8 0 6 1 1 g91H5
  | 6 => lookupWord 1 8 0 6 1 1 g91H6
  | _ => fun _ => none
def g91 : Forest := ⟨91,6,fun i => g91Y[i]?.getD (0,0),g91C,g91A,g91L,g91I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g91P4_0 : block g91 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g91B4 : block g91 4 0 1=true := g91P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g91P5_0 : block g91 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g91B5 : block g91 5 0 1=true := g91P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g91P6_0 : block g91 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g91B6 : block g91 6 0 1=true := g91P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g91T : checkedTables g91 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g91 0 0 0 = true)
  · exact (rfl : block g91 1 0 0 = true)
  · exact (rfl : block g91 2 0 0 = true)
  · exact (rfl : block g91 3 0 0 = true)
  · exact g91B4
  · exact g91B5
  · exact g91B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g91G : graphValid g91 (boundsBefore K61) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low91 : Lower true (varsX 91) (graphGoal 91) 7 := lower_forest (g:=g91) (i:=0) (hints:=67) (before_sound K61 V61) g91G g91T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K91 := extendKnown K61 7 [(91,[]),(107,[84,99]),(109,[67,84,99,33]),(117,[81,49,33,64])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V91 : Known true K91 := extend_ok (m:=91) V61 low91 (by decide +kernel)
def g93Y : Array (Bits × Bits) := #[(((((0xffffffff <<< 60) ||| 0xfffffffffffffff) <<< 60) ||| 0xfffffffc2c74c97),((((0xffffffff <<< 60) ||| 0xfffffffffffffff) <<< 60) ||| 0xfffffffc2400415)),(0x0,0x0),(0x3782d68,0x3590c60),(((((0xffffffff <<< 60) ||| 0xfffffffffffffff) <<< 60) ||| 0xfffffffec832e63),0x3cb72862),(0x30fcb0ac,0x38a63088),(0x0,0x0),(0x3f00d350,0xc300),(0x0,0x0),(0x0,0x0)]
def g93C : List ColumnInfo := [(20,0,73,0,4),(9,0,84,0,4)]
def g93A : List (List Nat) := [[]]
def g93D6 (j : Nat) : Nat := 0x105f
def g93L : Nat → Packing
  | 6 => (1,0,1,0,0,0,0,g93D6)
  | _ => emptyPacking
def g93I (_ _ : Nat) : Option (Nat × Nat) := none
def g93 : Forest := ⟨93,6,fun i => g93Y[i]?.getD (0,0),g93C,g93A,g93L,g93I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g93P6_0 : block g93 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g93B6 : block g93 6 0 1=true := g93P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g93T : checkedTables g93 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g93 0 0 0 = true)
  · exact (rfl : block g93 1 0 0 = true)
  · exact (rfl : block g93 2 0 0 = true)
  · exact (rfl : block g93 3 0 0 = true)
  · exact (rfl : block g93 4 0 0 = true)
  · exact (rfl : block g93 5 0 0 = true)
  · exact g93B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g93G : graphValid g93 (boundsBefore K91) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low93 : Lower true (varsX 93) (graphGoal 93) 7 := lower_forest (g:=g93) (i:=0) (hints:=1027) (before_sound K91 V91) g93G g93T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K93 := extendKnown K91 7 [(93,[]),(121,[67,66,48,82,96])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V93 : Known true K93 := extend_ok (m:=93) V91 low93 (by decide +kernel)
def g122Y : Array (Bits × Bits) := #[(0x0,0x0),(((((0xffffffff <<< 60) ||| 0xfffffffffffffff) <<< 60) ||| 0xfffffc80cfe4c9d),((((0xffffffff <<< 60) ||| 0xfffffffffffffff) <<< 60) ||| 0xfffffc81453cc0d)),(0x0,0x0),(0x307700bd5a,0x1014021c52),(0x1f881f0b74,0x11890c0170),(((((0xffffffff <<< 60) ||| 0xfffffffffffffff) <<< 60) ||| 0xfffffe00fe073e1),0x254ba823a0),(0x3ff001c6aa,0x2e62d1c288),(0x0,0x0),(0x0,0x0)]
def g122C : List ColumnInfo := [(32,0,90,0,4),(64,0,58,0,4),(16,0,106,0,4),(8,0,114,0,4),(2,0,120,0,4)]
def g122A : List (List Nat) := [[],[99,84],[49,100],[65,101],[81,67],[97,83]]
def g122D4 (j : Nat) : Nat := 0x57d4d10
def g122D5 (j : Nat) : Nat := 0x1a0fd20fd10
def g122H5 (j : Nat) : Nat := 0x80
def g122D6 (j : Nat) : Nat := 0x23440bf
def g122H6 (j : Nat) : Nat := ((((0x2080 <<< 60) ||| 0x68000000000000) <<< 120) ||| ((0x22402e294008 <<< 60) ||| 0x344020c0001eed9))
def g122L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g122D4)
  | 5 => (2,1,3,0,0,4,0,g122D5)
  | 6 => (1,0,3,0,0,0,0,g122D6)
  | _ => emptyPacking
def g122I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 8 0 8 1 3 g122H5
  | 6 => lookupWord 2 27 1 8 1 3 g122H6
  | _ => fun _ => none
def g122 : Forest := ⟨122,6,fun i => g122Y[i]?.getD (0,0),g122C,g122A,g122L,g122I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g122P4_0 : block g122 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g122B4 : block g122 4 0 1=true := g122P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g122P5_0 : block g122 5 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g122B5 : block g122 5 0 2=true := g122P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g122P6_0 : block g122 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g122B6 : block g122 6 0 1=true := g122P6_0
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
theorem g122G : graphValid g122 (boundsBefore K93) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low122 : Lower true (varsX 122) (graphGoal 122) 7 := lower_forest (g:=g122) (i:=0) (hints:=51466304) (before_sound K93 V93) g122G g122T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K122 := extendKnown K93 7 [(122,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V122 : Known true K122 := extend_ok (m:=122) V93 low122 (by decide +kernel)
def g95Y : Array (Bits × Bits) := #[(((0x10e0e7d3 <<< 60) ||| 0xdfff0552631aa4),0x66c30cd990008620884),(((((0xffffffff <<< 60) ||| 0xfffffffe281061c) <<< 60) ||| 0xe0784aa88d6a8f),((((0xffffffff <<< 60) ||| 0xffffffffbf5dfbe) <<< 60) ||| 0x4cb7d4aa88d2a8d)),(((((0xffffffff <<< 60) ||| 0xfffffffe301f82f) <<< 60) ||| 0xf0380d02d0188bd),((0x3a16cff <<< 60) ||| 0x78fd7502c0188ac)),(((0x3fe0030 <<< 60) ||| 0x3ff65d429a17e),((0x7ae0838 <<< 60) ||| 0xe3266477409a13a)),(((0x1c00003f <<< 60) ||| 0xffc006e11dcdd1a),((0x4080000 <<< 60) ||| 0x830002451105112)),(0x0,0x0),(((((0xffffffff <<< 60) ||| 0xfffffffffffffc0) <<< 60) ||| 0xf4ae1627c1),((((0xffffffff <<< 60) ||| 0xffffffff8509100) <<< 60) ||| 0x8082840641)),(0x0,0x0),(0x0,0x0)]
def g95C : List ColumnInfo := [(20,2,73,0,4),(11,0,84,0,4),(68,0,27,0,4),(5,0,90,0,4),(2,0,93,0,7),(14,0,81,0,4),(66,0,29,0,4),(4,0,91,0,7)]
def g95A : List (List Nat) := [[]]
def g95D4 (j : Nat) : Nat := ((((((((((0x41ddd <<< 60) ||| 0xdddddddd0ddddd0) <<< 60) ||| 0xb0d821955450ec6) <<< 120) ||| ((0x60065551438e580 <<< 60) ||| 0xdc965d0639e0976)) <<< 240) ||| ((((0xd4f418e7825db41 <<< 60) ||| 0xd4239e0976d0550) <<< 120) ||| ((0x8d587d8f4154266 <<< 60) ||| 0x21d4354140c6775))) <<< 480) ||| ((((((0x9956148239e1975 <<< 60) ||| 0xd05209e3855c341) <<< 120) ||| ((0x4827221d4354120 <<< 60) ||| 0xf095450d50482d8)) <<< 240) ||| ((((0xe1561541209e187 <<< 60) ||| 0xd0550482d861741) <<< 120) ||| ((0x54120d8b7550d40 <<< 60) ||| 0x483625d54350120))))
def g95D5 (j : Nat) : Nat := ((((((((((((0x30 <<< 60) ||| 0x431420410050400) <<< 120) ||| ((0x4004254a952a54a <<< 60) ||| 0x952a54a952a5448)) <<< 180) ||| ((((0x91254a952a54a95 <<< 60) ||| 0x1254a952a54c093) <<< 60) ||| 0x54a952a54a952a)) <<< 420) ||| ((((((0x604891260a982a2 <<< 60) ||| 0x4c0f30244953055) <<< 120) ||| ((0x3982a60f1830547 <<< 60) ||| 0x891224026fb9ac1)) <<< 180) ||| ((((0xaa4ed70d89549de <<< 60) ||| 0xe4b26a73bdc9655) <<< 60) ||| 0xe7db82caa1e5f6))) <<< 840) ||| ((((((((0x5d4d43cbecb32a8 <<< 60) ||| 0x7675d26550ecfba) <<< 120) ||| ((0x2caa1dcf7259543 <<< 60) ||| 0xbb6e0b2a87735c8)) <<< 180) ||| ((((0x6550eecb80caa1f <<< 60) ||| 0x1f6555143e38caa) <<< 60) ||| 0xa287e3dc95450ec)) <<< 420) ||| ((((((0xfb82a8a1ee77259 <<< 60) ||| 0x7419eee0b2e833d) <<< 120) ||| ((0x5db53d067bbaac1 <<< 60) ||| 0xa0cef7259350d3a)) <<< 180) ||| ((((0xc8a1ea1c755143d <<< 60) ||| 0x427abb683a85757) <<< 60) ||| 0x5d07509bae9b1aa)))) <<< 1680) ||| ((((((((((0x1b55c7635426f3b <<< 60) ||| 0x286a84dc7650d50) <<< 120) ||| ((0xe3aa8a1aa1b5d8d <<< 60) ||| 0x615436bb1aa2a84)) <<< 180) ||| ((((0xf576d0550aeaeba <<< 60) ||| 0xaa1b5d8f41542f) <<< 60) ||| 0x8b8682a84df7359)) <<< 420) ||| ((((((0x5409dee4b2a81a7 <<< 60) ||| 0xd95435034eb2a86) <<< 120) ||| ((0xa079b7050d40e72 <<< 60) ||| 0xa8a8281e650d505)) <<< 180) ||| ((((0x2f4b84ca905cf7 <<< 60) ||| 0x359520bd2e1aa24) <<< 60) ||| 0x13bdd954483c6aa))) <<< 840) ||| ((((((((0x286907cb7050d20 <<< 60) ||| 0xbceeab0a41b9995) <<< 120) ||| ((0x61482f3bb2a2905 <<< 60) ||| 0xe576d0520bcaeba)) <<< 180) ||| ((((0xa417add150483b <<< 60) ||| 0x5aa2a0907695454) <<< 60) ||| 0x120f96e6a8241f2)) <<< 420) ||| ((((((0x50d50483f0b8aa0 <<< 60) ||| 0x907e16154120fc2) <<< 120) ||| ((0xa2a8241f8d05504 <<< 60) ||| 0x82f5baa80905e97)) <<< 180) ||| ((((0x550120f52a8a024 <<< 60) ||| 0x139dc965d06f0b8) <<< 60) ||| 0x682907894350120)))))
def g95H5 (j : Nat) : Nat := ((((((((0x71e000 <<< 60) ||| 0x1a680000000001) <<< 120) ||| ((0x840038b87694000 <<< 60) ||| 0x500000)) <<< 180) ||| ((((0x58f60d <<< 60) ||| 0x880000000000c88) <<< 60) ||| 0x1c80)) <<< 360) ||| ((((((0x2 <<< 60) ||| 0x60000000000000) <<< 60) ||| 0x14480000000000) <<< 180) ||| ((((0x0 <<< 60) ||| 0x499c5800000) <<< 60) ||| 0xe300000510001)))
def g95D6 (j : Nat) : Nat := ((((((((((((0x10 <<< 60) ||| 0x4c1080508620044) <<< 60) ||| 0xe0020f00198200c) <<< 120) ||| ((0xfc21002114610 <<< 60) ||| 0x81004308430803)) <<< 300) ||| ((((((0xf94ff9a42525252 <<< 60) ||| 0x5254f256f252525) <<< 60) ||| 0x254f4ff96ff9256) <<< 120) ||| ((0xf256f4f6f6fee25 <<< 60) ||| 0xdede2525ce256f0))) <<< 540) ||| ((((((((0xb4252500a48f7a <<< 60) ||| 0x6f255f4f4f35252) <<< 60) ||| 0x51500bf58f54bf5) <<< 120) ||| ((0x8354bfd8d54fbd8 <<< 60) ||| 0x954bfd8154bf593)) <<< 240) ||| ((((0x53bfd9153bfd954 <<< 60) ||| 0x3bf59543ef55143) <<< 120) ||| ((0xf7d4d43f754d43f <<< 60) ||| 0x7d9543f799543f7)))) <<< 1140) ||| ((((((((((0x59543f719543f7d <<< 60) ||| 0x8143f758143fd54) <<< 60) ||| 0xd51fdd4f41fd54f) <<< 120) ||| ((0x41bf59350df5535 <<< 60) ||| 0xf750f50fdd0750)) <<< 300) ||| ((((((0xbfd9150dfd5150d <<< 60) ||| 0xf55150f7d8d50f7) <<< 60) ||| 0x50d50fd58550fd5) <<< 120) ||| ((0x4550fdd0550bfd9 <<< 60) ||| 0x540bf59540ef551))) <<< 540) ||| ((((((((0x40fe54140fb9952 <<< 60) ||| 0xfb59520fb59120) <<< 60) ||| 0xfbd5120fb55120b) <<< 120) ||| ((0xbd8954e755143bd <<< 60) ||| 0xd8151bd59741bd5)) <<< 240) ||| ((((0x8341b7d8d50e750 <<< 60) ||| 0xd40f350d20f9585) <<< 120) ||| ((0x20f954520f9d052 <<< 60) ||| 0xfa54120fa50120)))))
def g95H6 (j : Nat) : Nat := ((((((((((0x4fe4eb07402f46 <<< 60) ||| 0xf48d071c5d4cfcf) <<< 120) ||| ((0xa89400000000204 <<< 60) ||| 0x15118b80034c800)) <<< 240) ||| ((((0x19140000024a68d <<< 60) ||| 0xa03800241d001c9) <<< 120) ||| ((0x28490780014c000 <<< 60) ||| 0x241000107))) <<< 420) ||| ((((((0xc0000030f000000 <<< 60) ||| 0x86a10800) <<< 120) ||| ((0x43f49 <<< 60) ||| 0xc00040c00000204)) <<< 180) ||| ((((0xc8f4001cac00041 <<< 60) ||| 0x400088900400000) <<< 60) ||| 0xc980000000a))) <<< 900) ||| ((((((((0x94d00000000008e <<< 60) ||| 0x45) <<< 120) ||| ((0x88688000 <<< 60) ||| 0x143683000000)) <<< 240) ||| ((((0x4bc0000014c400 <<< 60) ||| 0x1d0c00000045) <<< 120) ||| ((0x40008640010d40e <<< 60) ||| 0xdc08000418001cb))) <<< 420) ||| ((((((0x826ca305 <<< 60) ||| 0xb10400000000000) <<< 120) ||| ((0x1c4400000000000 <<< 60) ||| 0x20e400042000000)) <<< 180) ||| ((((0x3c280015024dc00 <<< 60) ||| 0x10b5c6000000002) <<< 60) ||| 0x1d0acc0204c1))))
def g95D7 (j : Nat) : Nat := ((((((((0x58032c101080 <<< 60) ||| 0x430210c83c44010) <<< 60) ||| 0xb04032100cc0431) <<< 120) ||| ((0xa8a31a149e9a1 <<< 60) ||| 0x488110c88000380)) <<< 240) ||| ((((0x3fea9fd54ffa9ff <<< 60) ||| 0x54ffa87ff50fea8) <<< 120) ||| ((0x7f503bc87dd43fa <<< 60) ||| 0xa8fdd07da41f510)))
def g95H7 (j : Nat) : Nat := ((((((((((0x244 <<< 60) ||| 0xfa5000000000007) <<< 120) ||| ((0x46000007a800000 <<< 60) ||| 0x30bf24828000)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x6b30be0dd00000) <<< 120) ||| ((0x106c0000 <<< 60) ||| 0x357693001))) <<< 480) ||| ((((((0xcc4005030000000 <<< 60) ||| 0x0) <<< 120) ||| ((0xf0e0 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x148000480000 <<< 60) ||| 0x7400301040ac) <<< 120) ||| ((0x7 <<< 60) ||| 0x98001e5800000d0)))) <<< 960) ||| ((((((((0x405400000842000 <<< 60) ||| 0x9a0004d70600) <<< 120) ||| ((0xa2366400000000 <<< 60) ||| 0x21c0000)) <<< 240) ||| ((((0x71c66c00242800 <<< 60) ||| 0x2220004) <<< 120) ||| ((0xc91339e31141a02 <<< 60) ||| 0x0))) <<< 480) ||| ((((((0x28000000000000a <<< 60) ||| 0xd5500033e002da0) <<< 120) ||| ((0x94e0000000000 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x72da520000013 <<< 60) ||| 0x30000000020f000) <<< 120) ||| ((0x35e0000 <<< 60) ||| 0x30421000b20)))))
def g95D8 (j : Nat) : Nat := 0x9c813f
def g95H8 (j : Nat) : Nat := ((((((0x8180 <<< 60) ||| 0xd8000020800000) <<< 120) ||| ((0x4a <<< 60) ||| 0x6200000007410)) <<< 240) ||| ((((0x400000000192005 <<< 60) ||| 0x960000002da) <<< 120) ||| ((0x29 <<< 60) ||| 0xc016600000012a8)))
def g95L : Nat → Packing
  | 4 => (18,4,3,0,0,4,0,g95D4)
  | 5 => (70,3,3,0,0,7,0,g95D5)
  | 6 => (55,2,3,0,0,8,0,g95D6)
  | 7 => (14,1,3,0,0,8,0,g95D7)
  | 8 => (1,0,3,0,0,0,0,g95D8)
  | _ => emptyPacking
def g95I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 3 79 1 10 5 1 g95H5
  | 6 => lookupWord 14 147 5 12 7 1 g95H6
  | 7 => lookupWord 11 172 4 11 6 1 g95H7
  | 8 => lookupWord 2 49 2 9 4 1 g95H8
  | _ => fun _ => none
def g95 : Forest := ⟨95,8,fun i => g95Y[i]?.getD (0,0),g95C,g95A,g95L,g95I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P4_0 : block g95 4 0 18=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g95B4 : block g95 4 0 18=true := g95P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P5_0 : block g95 5 0 3=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P5_3 : block g95 5 3 48=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P5_51 : block g95 5 51 19=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g95B5 : block g95 5 0 70=true := (@block_merge g95 5 0 3 67 g95P5_0 (@block_merge g95 5 3 48 19 g95P5_3 g95P5_51))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P6_0 : block g95 6 0 13=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P6_13 : block g95 6 13 42=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g95B6 : block g95 6 0 55=true := (@block_merge g95 6 0 13 42 g95P6_0 g95P6_13)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P7_0 : block g95 7 0 6=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P7_6 : block g95 7 6 8=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g95B7 : block g95 7 0 14=true := (@block_merge g95 7 0 6 8 g95P7_0 g95P7_6)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P8_0 : block g95 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g95B8 : block g95 8 0 1=true := g95P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95T : checkedTables g95 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g95 0 0 0 = true)
  · exact (rfl : block g95 1 0 0 = true)
  · exact (rfl : block g95 2 0 0 = true)
  · exact (rfl : block g95 3 0 0 = true)
  · exact g95B4
  · exact g95B5
  · exact g95B6
  · exact g95B7
  · exact g95B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95G : graphValid g95 (boundsBefore K122) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low95 : Lower true (varsX 95) (graphGoal 95) 9 := lower_forest (g:=g95) (i:=0) (hints:=1091) (before_sound K122 V122) g95G g95T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K95 := extendKnown K122 9 [(95,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V95 : Known true K95 := extend_ok (m:=95) V122 low95 (by decide +kernel)
def g119Y : Array (Bits × Bits) := #[(((((0xffffffff <<< 60) ||| 0xfffffffffff4410) <<< 60) ||| 0x79b0741614cd215),0x1040b0040214cc204),(0x82042df886815466ba,0x12450f488201544698),(0xb03f84e00f81ca5b348,0x3180e11d80945b300),(0x0,0x0),(((((0xffffffff <<< 60) ||| 0xfffffffffff3fc0) <<< 60) ||| 0x7000ff3f964d43),((((0xffffffff <<< 60) ||| 0xfffffffffff9040) <<< 60) ||| 0x30222506800843)),(0xc00007fff00dc23b9e4,0xfe49270b735dc233960),(0xfffff8000001e6b0eb8,0x6f8e3c0c400103204b8),(0x0,0x0),(0x0,0x0)]
def g119C : List ColumnInfo := [(38,0,81,0,4),(20,0,99,0,4),(3,32,84,0,4),(1,0,118,0,7),(66,0,53,0,4),(65,0,54,0,4),(2,0,117,0,7),(35,0,84,0,4)]
def g119A : List (List Nat) := [[]]
def g119D5 (j : Nat) : Nat := ((((((0x17a5c0625 <<< 60) ||| 0x4ed7b92a7a1daf7) <<< 60) ||| 0x254d43d3ec6a1aa) <<< 120) ||| ((0x5d354f52cca77b9 <<< 60) ||| 0x2ca9974d5354932))
def g119D6 (j : Nat) : Nat := ((((((((((0x10 <<< 60) ||| 0x83b076108250a0b) <<< 60) ||| 0x682da0ab6d055c1) <<< 120) ||| ((0x6d060c16cae0b68 <<< 60) ||| 0x305b2b4000800bf)) <<< 240) ||| ((((0x58b53bf59653bfd <<< 60) ||| 0x8953fbd8953fb18) <<< 120) ||| ((0x953efd4f43ef54f <<< 60) ||| 0x43efd4d43ef54d4))) <<< 480) ||| ((((((0x3bf58f52df54f52 <<< 60) ||| 0xef50f52bfd8d52d) <<< 120) ||| ((0xfd4d52df54d52ef <<< 60) ||| 0x50d52bf59732f75)) <<< 240) ||| ((((0x4f32fbd4b32bf59 <<< 60) ||| 0x532f754d32fb549) <<< 120) ||| ((0x32bbd8953bb5885 <<< 60) ||| 0x3bd58453be58053))))
def g119H6 (j : Nat) : Nat := ((((((0x44000000 <<< 60) ||| 0xb10000000) <<< 60) ||| 0xa600009300) <<< 120) ||| ((0xa2000000000 <<< 60) ||| 0xa5000000))
def g119D7 (j : Nat) : Nat := ((((((((0x85 <<< 60) ||| 0x145e420b118b90) <<< 60) ||| 0x42c642105144143) <<< 120) ||| ((0x41b0110ac0454b0 <<< 60) ||| 0x110841c40120f5a)) <<< 240) ||| ((((0xe26a01b960f8a04 <<< 60) ||| 0x803fea7fe53fea9) <<< 120) ||| ((0xff14ffea5fd52ff <<< 60) ||| 0x997f4cb7e87bd43)))
def g119H7 (j : Nat) : Nat := ((((((((((0x14a00000 <<< 60) ||| 0x238000000000000) <<< 60) ||| 0x90e4b7055463c00) <<< 120) ||| ((0x3990000000008 <<< 60) ||| 0x0)) <<< 300) ||| ((((((0x1d200189 <<< 60) ||| 0xf18008400094c00) <<< 60) ||| 0x0) <<< 120) ||| ((0x256c089700000 <<< 60) ||| 0x51c0000185b4400))) <<< 540) ||| ((((((((0x1d800000 <<< 60) ||| 0x0) <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0xe10000000000000)) <<< 240) ||| ((((0x95400 <<< 60) ||| 0x630c000000) <<< 120) ||| ((0xcd <<< 60) ||| 0x80))))
def g119D8 (j : Nat) : Nat := 0xc9813f
def g119H8 (j : Nat) : Nat := ((((((0x840000000000124 <<< 60) ||| 0x7880000a2b180) <<< 60) ||| 0x248) <<< 120) ||| ((0x7a14e63 <<< 60) ||| 0x160000024))
def g119L : Nat → Packing
  | 5 => (7,3,3,0,0,0,0,g119D5)
  | 6 => (26,2,3,0,0,7,0,g119D6)
  | 7 => (10,1,3,0,0,8,0,g119D7)
  | 8 => (1,0,3,0,0,0,0,g119D8)
  | _ => emptyPacking
def g119I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 35 0 8 3 1 g119H6
  | 7 => lookupWord 5 111 4 10 5 1 g119H7
  | 8 => lookupWord 3 37 2 9 4 1 g119H8
  | _ => fun _ => none
def g119 : Forest := ⟨119,8,fun i => g119Y[i]?.getD (0,0),g119C,g119A,g119L,g119I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P5_0 : block g119 5 0 7=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g119B5 : block g119 5 0 7=true := g119P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P6_0 : block g119 6 0 4=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P6_4 : block g119 6 4 22=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g119B6 : block g119 6 0 26=true := (@block_merge g119 6 0 4 22 g119P6_0 g119P6_4)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P7_0 : block g119 7 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P7_2 : block g119 7 2 8=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g119B7 : block g119 7 0 10=true := (@block_merge g119 7 0 2 8 g119P7_0 g119P7_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P8_0 : block g119 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g119B8 : block g119 8 0 1=true := g119P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119T : checkedTables g119 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g119 0 0 0 = true)
  · exact (rfl : block g119 1 0 0 = true)
  · exact (rfl : block g119 2 0 0 = true)
  · exact (rfl : block g119 3 0 0 = true)
  · exact (rfl : block g119 4 0 0 = true)
  · exact g119B5
  · exact g119B6
  · exact g119B7
  · exact g119B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119G : graphValid g119 (boundsBefore K95) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low119 : Lower true (varsX 119) (graphGoal 119) 9 := lower_forest (g:=g119) (i:=0) (hints:=1092) (before_sound K95 V95) g119G g119T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K119 := extendKnown K95 9 [(119,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V119 : Known true K119 := extend_ok (m:=119) V95 low119 (by decide +kernel)
def g123Y : Array (Bits × Bits) := #[(((0x2913f8f7 <<< 60) ||| 0x8c82cc053253d20),0x448c0008112003900),(((((0xffffffff <<< 60) ||| 0xfffffffc2002328) <<< 60) ||| 0x24d2898cdb1f19),((0x8890065 <<< 60) ||| 0x88052898c991d18)),(0x0,0x0),(((0x341c7c33 <<< 60) ||| 0xe15035622994a6e),0x4000331080460589022e),(((0x7e0403c <<< 60) ||| 0x72a9c291d4492ee),((0x10240d9a <<< 60) ||| 0x3288c2201448266)),(((((0xffffffff <<< 60) ||| 0xffffffff8007fc0) <<< 60) ||| 0x63c6382e0a6e0d3),((((0xffffffff <<< 60) ||| 0xffffffff7327f98) <<< 60) ||| 0x42e29106026c0c1)),(((0x3fff8000 <<< 60) ||| 0x7cf023c401ac594),((0x2fdbf220 <<< 60) ||| 0x407721860124490)),(0x0,0x0),(0x0,0x0)]
def g123C : List ColumnInfo := [(82,0,41,0,4),(48,2,73,0,4),(42,0,81,0,4),(1,0,122,0,7),(9,0,114,0,4),(24,0,99,0,4),(17,0,106,0,4),(16,0,107,0,7),(65,0,58,0,4),(3,0,120,0,4),(33,0,90,0,4),(2,0,121,0,7),(96,0,27,0,4),(50,0,73,0,4),(32,0,91,0,7)]
def g123A : List (List Nat) := [[],[99,84]]
def g123D5 (j : Nat) : Nat := ((((((((((((0x14000430 <<< 60) ||| 0x204041030400000) <<< 60) ||| 0x300000000000000) <<< 120) ||| ((0x60000000 <<< 60) ||| 0x221940000000000)) <<< 300) ||| ((((((0x18002a7 <<< 60) ||| 0x61b5350e428fb80) <<< 60) ||| 0x5d9544cb1bd9772) <<< 120) ||| ((0x55132f0d5450d52 <<< 60) ||| 0x4ca9b60b6594930))) <<< 600) ||| ((((((((0xc5f655ce524c21f <<< 60) ||| 0xe157690930e4f65) <<< 60) ||| 0x949324c21fe1573) <<< 120) ||| ((0xd912087f855d953 <<< 60) ||| 0x4821fe157650d20)) <<< 300) ||| ((((((0xb6980d5152482da <<< 60) ||| 0x6165254120b6b83) <<< 60) ||| 0x549504839ad8d52) <<< 120) ||| ((0x54120b698590950 <<< 60) ||| 0x482da6163254120)))) <<< 1200) ||| ((((((((((0xb69854c950483d2 <<< 60) ||| 0x54d3254120d6975) <<< 60) ||| 0x54940483ca55152) <<< 120) ||| ((0x50120ba98550940 <<< 60) ||| 0x4836add54250120)) <<< 300) ||| ((((((0xda97550940482ea <<< 60) ||| 0x6113250120f8943) <<< 60) ||| 0x4c9404827ce0175) <<< 120) ||| ((0x949109f183dc152 <<< 60) ||| 0x4427ce017590910))) <<< 600) ||| ((((((((0x9f3805d632442f8 <<< 60) ||| 0xe01528c9109f380) <<< 60) ||| 0x5d532442f8e0152) <<< 120) ||| ((0x4c910bd1839c930 <<< 60) ||| 0x442dce15724c110)) <<< 300) ||| ((((((0xbd183949304427c <<< 60) ||| 0xe1d524c110bd385) <<< 60) ||| 0x4c930442f461532) <<< 120) ||| ((0x4c110fc2524c930 <<< 60) ||| 0x443f0549324c110)))))
def g123D6 (j : Nat) : Nat := (if j<1 then ((((((((((((((((0x20882256 <<< 60) ||| 0x822708214082256) <<< 60) ||| 0x820ae8222e85208) <<< 120) ||| ((0x852148521482208 <<< 60) ||| 0x850ae82140781aa)) <<< 240) ||| ((((0x5d0ae5694021926 <<< 60) ||| 0x3c0c8218ae21886) <<< 120) ||| ((0x2185e0a0013fdc1 <<< 60) ||| 0x6594a7eba6c6a94))) <<< 540) ||| ((((((((0xfd70d8d529fceca <<< 60) ||| 0x1aa5b7d8d4354af) <<< 60) ||| 0xbb8a86a94fd73d8) <<< 120) ||| ((0x1529fee6b2c853f <<< 60) ||| 0xdc16590a7ebb6a7)) <<< 240) ||| ((((0x216bd6550e42f3e <<< 60) ||| 0xa6a1c85af50d609) <<< 120) ||| ((0xa7ebb6a6a15bd7 <<< 60) ||| 0x4d4d429fee0b2c6)))) <<< 1020) ||| ((((((((((0x57bdc1528cb76a9 <<< 60) ||| 0x2c1194fd74d9532) <<< 60) ||| 0x9fae1b2a653fdd1) <<< 120) ||| ((0x654cb6fb9aca994 <<< 60) ||| 0xff70595329faebb)) <<< 240) ||| ((((0x22653f5c3644ca7 <<< 60) ||| 0xfbaac8994ff7059) <<< 120) ||| ((0x1329faecaa2657b <<< 60) ||| 0xdc9544caeebaa86))) <<< 480) ||| ((((((0x9979d5450d32bda <<< 60) ||| 0xe12926577dcd524) <<< 120) ||| ((0xcbb6aa2a4997cf7 <<< 60) ||| 0x354932f9a86a926)) <<< 240) ||| ((((0x57bdc1524ca7eba <<< 60) ||| 0xec0994fd74d8132) <<< 120) ||| ((0xdbaa7b0265b750f <<< 60) ||| 0x604cb76a96c0995))))) <<< 2040) ||| ((((((((((((0x7f75581329fee0b <<< 60) ||| 0x2e433f5d3654c27) <<< 60) ||| 0xeb96ca984fd75d9) <<< 120) ||| ((0x1309fae5b22613f <<< 60) ||| 0xdc9644c33fb2aa8)) <<< 240) ||| ((((0x985dd7550d30f3a <<< 60) ||| 0xa8a1a613f5d7624) <<< 120) ||| ((0xc27eba6c4986dd5 <<< 60) ||| 0x3d8930dba87b126))) <<< 480) ||| ((((((0x13f5da624c2eeb9 <<< 60) ||| 0xcc4985f97098930) <<< 120) ||| ((0xafeeab12613f5da <<< 60) ||| 0x524c33fb2ca4985)) <<< 240) ||| ((((0xdd73949309feeca <<< 60) ||| 0x92613f5da424c2e) <<< 120) ||| ((0xeb9c849879d4390 <<< 60) ||| 0x930bbeea9926177)))) <<< 1020) ||| ((((((((((0x5d5324c36fb2a64 <<< 60) ||| 0x985df744c930bba) <<< 60) ||| 0xe899261b7d91324) <<< 120) ||| ((0xc36eb2264987ce5 <<< 60) ||| 0x24c930f9aa49926)) <<< 240) ||| ((((0x13fdcd65c827ebb <<< 60) ||| 0x6a7905ed72d4f20) <<< 120) ||| ((0x9faeca9e41b758d <<< 60) ||| 0x53c82f7b9aa5906))) <<< 480) ||| ((((((0xed6354b20bdaea9 <<< 60) ||| 0x9641bb59532c83e) <<< 120) ||| ((0x6a9a65904fd74d9 <<< 60) ||| 0x5209fae7b2a417b)) <<< 240) ||| ((((0x5ca654827fb9aca <<< 60) ||| 0x906fb70595209fa) <<< 120) ||| ((0xebb22413f5cf644 <<< 60) ||| 0x827fbaac8904ff7)))))) <<< 4080) ||| ((((((((((((((0x3591209faedaa24 <<< 60) ||| 0x17b5cb54482fab8) <<< 60) ||| 0xea8905f970d5120) <<< 120) ||| ((0xd7ac8aa2413f5d7 <<< 60) ||| 0x634827eba6c6905)) <<< 240) ||| ((((0x7f7558d20af8eab <<< 60) ||| 0x1a413fdd5634833) <<< 120) ||| ((0xfbaac69067c7558 <<< 60) ||| 0xd209fee8b1a413f))) <<< 480) ||| ((((((0x5db53482f6b96a6 <<< 60) ||| 0x905f970d4d209fa) <<< 120) ||| ((0xeca9a41b758d534 <<< 60) ||| 0x827ebb286906bf6)) <<< 240) ||| ((((0x450d20dbac6a1a4 <<< 60) ||| 0x17ddc5434827ebb) <<< 120) ||| ((0x6a4905f970d4920 <<< 60) ||| 0xbdaeb292417b5ce)))) <<< 1020) ||| ((((((((((0x5248376b1ca4905 <<< 60) ||| 0xfb7054920bdee8a) <<< 60) ||| 0x9241dbd5152483b) <<< 120) ||| ((0x6aa2a4905ef7354 <<< 60) ||| 0x920ddec6a9241bb)) <<< 240) ||| ((((0x58d52483f5b82a4 <<< 60) ||| 0x905ed7590920bda) <<< 120) ||| ((0xe721241eb50e424 <<< 60) ||| 0x82f6baa84907ad5))) <<< 480) ||| ((((((0x450920bdaeb1924 <<< 60) ||| 0x1bb59632482f7ba) <<< 120) ||| ((0xa64905ed754c920 <<< 60) ||| 0xddeca99241bb595)) <<< 240) ||| ((((0x32482f7ba264905 <<< 60) ||| 0xed744c920f9aa69) <<< 120) ||| ((0x9241f350d32482d <<< 60) ||| 0xfba2c2904fd76d4))))) <<< 2040) ||| ((((((((((((0x520cfecba8a416f <<< 60) ||| 0x5d351482f6b96a2) <<< 60) ||| 0x905f970d4520cfe) <<< 120) ||| ((0xcaa8a41bed8d504 <<< 60) ||| 0x83f5292a0907e95)) <<< 240) ||| ((((0x254120fd484a824 <<< 60) ||| 0x1fa50950483f519) <<< 120) ||| ((0x2a0907e93254120 <<< 60) ||| 0xbf6eaa02417e5d5))) <<< 480) ||| ((((((0x40483dcaa280907 <<< 60) ||| 0xb94350120fd2a4a) <<< 120) ||| ((0x241fa4c9404827 <<< 60) ||| 0xebaec4885fb7054)) <<< 240) ||| ((((0x910beaebb12217d <<< 60) ||| 0x5d462442fabaca4) <<< 120) ||| ((0x885f57394910bee <<< 60) ||| 0xe6a9221fcdc1524)))) <<< 1020) ||| ((((((((((0x42fabac84885f57 <<< 60) ||| 0x58c910fcaa51922) <<< 60) ||| 0x17ddd532442faba) <<< 120) ||| ((0xa64887d5534c910 <<< 60) ||| 0xfcca499221f9549)) <<< 240) ||| ((((0x32443f8baa60887 <<< 60) ||| 0xf2724c110fe2e49) <<< 120) ||| ((0x8221fc94930443f <<< 60) ||| 0x8a9260884f570d8))) <<< 480) ||| ((((((0x543de2e2b00a51f <<< 60) ||| 0xdd563483b4a92a0) <<< 120) ||| ((0x907a94250120ece <<< 60) ||| 0xa5292217cdc1524)) <<< 240) ||| ((((0x427b3b0a4885d57 <<< 60) ||| 0x314910be2e02922) <<< 120) ||| ((0x13d9da32443e8a9 <<< 60) ||| 0xa60887d1324c110))))))) else ((((((((((((0x198204 <<< 60) ||| 0x48414004140840c) <<< 60) ||| 0x840008404104dc) <<< 120) ||| ((0x110081001020210 <<< 60) ||| 0xc042035c1040850)) <<< 240) ||| ((((0x418008182008001 <<< 60) ||| 0x6000430c100061) <<< 120) ||| ((0x81020e304100861 <<< 60) ||| 0x830410004100080))) <<< 540) ||| ((((((((0x840800602186021 <<< 60) ||| 0x20850208e114082) <<< 60) ||| 0x208822088214082) <<< 120) ||| ((0x208822708220882 <<< 60) ||| 0x38513208ff20850)) <<< 240) ||| ((((0x20882385091409c <<< 60) ||| 0x3fc82256f5208e1) <<< 120) ||| ((0x208823848220882 <<< 60) ||| 0x208823848214082)))) <<< 1080) ||| ((((((((((0x208503ace120882 <<< 60) ||| 0x208500ae502d882) <<< 60) ||| 0x20882270820aeb6) <<< 120) ||| ((0x14049a1482140b6 <<< 60) ||| 0x2d8d72088220882)) <<< 240) ||| ((((0x208820ae8220882 <<< 60) ||| 0x20882208d094082) <<< 120) ||| ((0x328820ae8220882 <<< 60) ||| 0xae820ae2ba0850))) <<< 540) ||| ((((((((0x208822082ba0882 <<< 60) ||| 0x2082b8ae820aec0) <<< 60) ||| 0x2d8afa08821402b) <<< 120) ||| ((0xa142b9408220882 <<< 60) ||| 0x208820ae9c20885)) <<< 240) ||| ((((0x208852a48220849 <<< 60) ||| 0xa14a29408521482) <<< 120) ||| ((0x270820ae8220850 <<< 60) ||| 0x1402ba082b8ae82))))))
def g123H6 (j : Nat) : Nat := ((((((((((((0x6000a6a391 <<< 60) ||| 0x200099a0018f000) <<< 60) ||| 0x34611bdb7b) <<< 120) ||| ((0x400070231ee408b <<< 60) ||| 0x710000008)) <<< 240) ||| ((((0x1b2840031900000 <<< 60) ||| 0xf95898000) <<< 120) ||| ((0x0 <<< 60) ||| 0x529b65))) <<< 540) ||| ((((((((0x4580060a0000035 <<< 60) ||| 0x800000000000001) <<< 60) ||| 0x740061c10c002e) <<< 120) ||| ((0xab070000000015d <<< 60) ||| 0x29c000000000)) <<< 240) ||| ((((0x1ca800000a8c00 <<< 60) ||| 0x79f000002c90006) <<< 120) ||| ((0xb40000000000000 <<< 60) ||| 0x0)))) <<< 1020) ||| ((((((((((0xc180000 <<< 60) ||| 0x0) <<< 60) ||| 0x18b80) <<< 120) ||| ((0x59aeac <<< 60) ||| 0x0)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x1a8800509a400) <<< 120) ||| ((0x191000002a9 <<< 60) ||| 0x0))) <<< 480) ||| ((((((0xe290c648000a1 <<< 60) ||| 0x6a0000) <<< 120) ||| ((0x31280000 <<< 60) ||| 0xfa8000)) <<< 240) ||| ((((0x14040000 <<< 60) ||| 0x2a89d7000) <<< 120) ||| ((0x68800013d4 <<< 60) ||| 0x980040c40038420)))))
def g123D7 (j : Nat) : Nat := ((((((((((((((0x400 <<< 60) ||| 0x420810030804c32) <<< 120) ||| ((0x44c30010831400 <<< 60) ||| 0x850810cc1410c61)) <<< 240) ||| ((((0x440131481800ca1 <<< 60) ||| 0x8004418c0431401) <<< 120) ||| ((0x841060800c21820 <<< 60) ||| 0x811830050840481))) <<< 420) ||| ((((((0x22840833040861 <<< 60) ||| 0x440d70040c40021) <<< 120) ||| ((0x20430040a30021 <<< 60) ||| 0x48c51032410830)) <<< 180) ||| ((((0x801030400830800 <<< 60) ||| 0xc50c00842800820) <<< 60) ||| 0x14c40440801060))) <<< 840) ||| ((((((((0x820481421020420 <<< 60) ||| 0x40830c00830020) <<< 120) ||| ((0x80067084141cc01 <<< 60) ||| 0x4414a0030881411)) <<< 180) ||| ((((0x52010840450031 <<< 60) ||| 0x400811050800c00) <<< 60) ||| 0x531440030421001)) <<< 420) ||| ((((((0x10840801830800 <<< 60) ||| 0x4610a18d0800461) <<< 120) ||| ((0xa30031808c11000 <<< 60) ||| 0x460c51820631418)) <<< 180) ||| ((((0xc20c01630842230 <<< 60) ||| 0x831630830370441) <<< 60) ||| 0x81008c114a1230)))) <<< 1740) ||| ((((((((((0x21570011041441 <<< 60) ||| 0x978c10070021030) <<< 120) ||| ((0x801231040821230 <<< 60) ||| 0x835c21031440425)) <<< 240) ||| ((((0xe31802040ca1030 <<< 60) ||| 0x848c20030012432) <<< 120) ||| ((0x410230852410808 <<< 60) ||| 0xc52630420050040))) <<< 420) ||| ((((((0x430230421020230 <<< 60) ||| 0x44cc20011020010) <<< 120) ||| ((0xc2002cc00811031 <<< 60) ||| 0x800449428be9306)) <<< 180) ||| ((((0x7e9189008e87aa8 <<< 60) ||| 0xd003c8be8a688e4) <<< 60) ||| 0x9286a85283481c3))) <<< 840) ||| ((((((((0x8a7fe7e67d47bc7 <<< 60) ||| 0xbc7aa03c79e78c7) <<< 120) ||| ((0x7469076274a7327 <<< 60) ||| 0x207086f66d86c06)) <<< 180) ||| ((((0xa869067e67e1446 <<< 60) ||| 0x666482346366185) <<< 60) ||| 0xfa5e85ca5b85a05)) <<< 420) ||| ((((((0x8857655253451c4 <<< 60) ||| 0xfe4e04c84aa4924) <<< 120) ||| ((0x924744564384204 <<< 60) ||| 0x23d83c03a238a3)) <<< 180) ||| ((((0x6634e3303183002 <<< 60) ||| 0xe22be23429a27c2) <<< 60) ||| 0x4c2342162041ec1))))) <<< 3420) ||| ((((((((((((0xd41aa19217415c1 <<< 60) ||| 0x5c1441441441200) <<< 120) ||| ((0xfc0d80c00a20a20 <<< 60) ||| 0x8406603c03c04e0)) <<< 240) ||| ((((0x3c01e01e000ffd8 <<< 60) ||| 0xd52ff58d52ff50d) <<< 120) ||| ((0x52ffd8552ff5855 <<< 60) ||| 0x2ffd8152ff58152))) <<< 420) ||| ((((((0xffd4e42ffd4d42f <<< 60) ||| 0xf54d42ff59532ff) <<< 120) ||| ((0x59132ff55132ff5 <<< 60) ||| 0x4932ff58132ff59)) <<< 180) ||| ((((0x530ff59130ff551 <<< 60) ||| 0x30ff98930ff5893) <<< 60) ||| 0xff94930ff54930))) <<< 840) ||| ((((((((0xff90930ff50930f <<< 60) ||| 0xfd4f20ff54f20ff) <<< 120) ||| ((0x99520ff59520ff5 <<< 60) ||| 0x9120ffd5120ff55)) <<< 180) ||| ((((0x120ff58d20ffd4d <<< 60) ||| 0x20ff54d20ff50d2) <<< 60) ||| 0xffd4920ff54920)) <<< 420) ||| ((((((0xff4c920ff58520f <<< 60) ||| 0xfd4520ff54520ff) <<< 120) ||| ((0x4c520ff54910bf5 <<< 60) ||| 0x9652bf58e52bf58)) <<< 180) ||| ((((0x252bfd8d52bfd81 <<< 60) ||| 0x52bf58052bf5964) <<< 60) ||| 0x2bf58e42ef50e42)))) <<< 1680) ||| ((((((((((0xbf58242bf59632f <<< 60) ||| 0xb54a32bf58232bf) <<< 120) ||| ((0xd9532bf59532bfd <<< 60) ||| 0x9132bf59132f754)) <<< 180) ||| ((((0xd32f750d32fb949 <<< 60) ||| 0x32fb54932bfd813) <<< 60) ||| 0x2bf59721bf58321)) <<< 420) ||| ((((((0xbfd9530bfd9130b <<< 60) ||| 0xf59130f754d30f7) <<< 120) ||| ((0x50d30bfd8930f74 <<< 60) ||| 0xc930bf59720bf58)) <<< 180) ||| ((((0xf20fb54b20fb4cb <<< 60) ||| 0x20bfd9520bf5952) <<< 60) ||| 0xbfd9120bf59120))) <<< 840) ||| ((((((((0xbfd8d20bf58d20f <<< 60) ||| 0xb94920fb54920fb) <<< 120) ||| ((0x90920fb50920fb8 <<< 60) ||| 0xc920fb4c920fe54)) <<< 180) ||| ((((0x120fe50120fd54b <<< 60) ||| 0x10fd4cb10bfd891) <<< 60) ||| 0xfdd8910fd18910)) <<< 420) ||| ((((((0xfd94910fd54910f <<< 60) ||| 0xd14910fd90910fd) <<< 120) ||| ((0x50910fd8c910fd4 <<< 60) ||| 0xc910bdd8543dbd4)) <<< 180) ||| ((((0xa52b758c52bd584 <<< 60) ||| 0x52be58052bd5863) <<< 60) ||| 0x2b758f21fc4c110))))))
def g123H7 (j : Nat) : Nat := ((((((((((((((0x16ad6277c49f5 <<< 60) ||| 0x3e90f0500000016) <<< 120) ||| ((0xbd41d8000001c7d <<< 60) ||| 0x4170000000f0)) <<< 240) ||| ((((0x69a900000000007 <<< 60) ||| 0x5291120000005d4) <<< 120) ||| ((0x0 <<< 60) ||| 0xa190000000))) <<< 420) ||| ((((((0x2d4600 <<< 60) ||| 0xf45e) <<< 120) ||| ((0x6010720ff452000 <<< 60) ||| 0x0)) <<< 180) ||| ((((0x157b909 <<< 60) ||| 0x12a00000018060f) <<< 60) ||| 0xb3680000000))) <<< 900) ||| ((((((((0x42c8000000 <<< 60) ||| 0xd62800000184820) <<< 120) ||| ((0x280000000000000 <<< 60) ||| 0x2a56000000000)) <<< 240) ||| ((((0x391d86749500030 <<< 60) ||| 0xc00000000000000) <<< 120) ||| ((0x11cc90600 <<< 60) ||| 0x8))) <<< 420) ||| ((((((0xd89f8000491000 <<< 60) ||| 0x0) <<< 120) ||| ((0x395107a5a48002 <<< 60) ||| 0xce200095d000000)) <<< 180) ||| ((((0xa3c9c974bfe <<< 60) ||| 0x9ea027a6c000000) <<< 60) ||| 0x209642c00)))) <<< 1800) ||| ((((((((((0x1053a9d0006 <<< 60) ||| 0x8c000061e607800) <<< 120) ||| ((0x315280900000008 <<< 60) ||| 0x83a260000000070)) <<< 240) ||| ((((0xe55b5b5d1600 <<< 60) ||| 0xe1010000000000d) <<< 120) ||| ((0x4552c394e91b4a6 <<< 60) ||| 0x69ec00145b00000))) <<< 420) ||| ((((((0x608000bbe8000 <<< 60) ||| 0x0) <<< 120) ||| ((0x21f00000006 <<< 60) ||| 0x8172aea840006b1)) <<< 180) ||| ((((0xe8afc9200698772 <<< 60) ||| 0x2d9b00000000000) <<< 60) ||| 0x104000))) <<< 900) ||| ((((((((0x1afc0 <<< 60) ||| 0xbb2b0d4000) <<< 120) ||| ((0x7dcd23000000 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x14d016d4173ad <<< 60) ||| 0x24e562800050) <<< 120) ||| ((0xf78220005cb42cc <<< 60) ||| 0x3a4800))) <<< 420) ||| ((((((0xa1180000000 <<< 60) ||| 0x30d0000001a2f) <<< 120) ||| ((0xd30800182c00000 <<< 60) ||| 0x6c040000000000)) <<< 180) ||| ((((0x1820000000000 <<< 60) ||| 0x1c6d22e44b80000) <<< 60) ||| 0x18b90000000c5b))))) <<< 3600) ||| ((((((((((((0x23aa3accb050095 <<< 60) ||| 0x25a08003a810200) <<< 120) ||| ((0x29e000000 <<< 60) ||| 0x4554000d0d00050)) <<< 240) ||| ((((0xcc6600007530000 <<< 60) ||| 0x64dc1f64b50878f) <<< 120) ||| ((0x91290003a8996f6 <<< 60) ||| 0x69c49b6a993ed66))) <<< 420) ||| ((((((0x618e0a80006c310 <<< 60) ||| 0x96af0c8fb271120) <<< 120) ||| ((0x3934559d12800 <<< 60) ||| 0x34a600000000035)) <<< 180) ||| ((((0x4f7800049d0000 <<< 60) ||| 0x491fe8c00044) <<< 60) ||| 0xa31100004008c4e))) <<< 900) ||| ((((((((0x1a0000d7cb3169f <<< 60) ||| 0x59190dd4b4947fb) <<< 120) ||| ((0x6928b320060002 <<< 60) ||| 0x6c62a5000000000)) <<< 240) ||| ((((0x36100000000 <<< 60) ||| 0xf378ab38c7364) <<< 120) ||| ((0xa5a00000 <<< 60) ||| 0x1a18000c570000))) <<< 420) ||| ((((((0x136d239905fcb <<< 60) ||| 0x8001c8500044208) <<< 120) ||| ((0xc000000745ecb2 <<< 60) ||| 0x94000000)) <<< 180) ||| ((((0x4 <<< 60) ||| 0xca0000000000000) <<< 60) ||| 0x49de4ca000e2c79)))) <<< 1800) ||| ((((((((((0xac0000000000000 <<< 60) ||| 0xd6a000e57000390) <<< 120) ||| ((0xe00000000000000 <<< 60) ||| 0x6abaa63d10000)) <<< 240) ||| ((((0x14787b800 <<< 60) ||| 0x0) <<< 120) ||| ((0x2954000a94000 <<< 60) ||| 0x1b4b027c9038))) <<< 420) ||| ((((((0x6e8517b38000000 <<< 60) ||| 0xf384198001a8) <<< 120) ||| ((0xd20982640000000 <<< 60) ||| 0x1427c26)) <<< 180) ||| ((((0x8000000000715b0 <<< 60) ||| 0xfc57164cb32201c) <<< 60) ||| 0x888c4310a800000))) <<< 900) ||| ((((((((0x149c00000022740 <<< 60) ||| 0x8400049a1629414) <<< 120) ||| ((0x263212400181d00 <<< 60) ||| 0x16440000000)) <<< 240) ||| ((((0x8ac000 <<< 60) ||| 0x11d80) <<< 120) ||| ((0x9c200000010b5 <<< 60) ||| 0x5420c5e4c38085))) <<< 420) ||| ((((((0x69504174001c190 <<< 60) ||| 0x71780000005d1) <<< 120) ||| ((0x71aa4c56bb403e2 <<< 60) ||| 0x404000088e10820)) <<< 180) ||| ((((0x130811844710001 <<< 60) ||| 0x40400004c1230e5) <<< 60) ||| 0x50cad0146da0062))))))
def g123D8 (j : Nat) : Nat := ((((((((0x1ab98 <<< 60) ||| 0x8011a6010619880) <<< 120) ||| ((0x239671880302611 <<< 60) ||| 0x8b3cc0214a7980)) <<< 240) ||| ((((0x411a6208043cc02 <<< 60) ||| 0x8b30082208c718) <<< 120) ||| ((0x2302e31081012e <<< 60) ||| 0x310c202c6115ab1))) <<< 480) ||| ((((((0x8802ac610f71a3c <<< 60) ||| 0x4d96974b96421dc) <<< 120) ||| ((0xcf5aa44ee531a05 <<< 60) ||| 0x401fd43ff297f54)) <<< 240) ||| ((((0xbf8a5fe42fea17f <<< 60) ||| 0x8cbfa65fd31ff90) <<< 120) ||| ((0xff487fa61ff20fe <<< 60) ||| 0x907f443ee21f510))))
def g123H8 (j : Nat) : Nat := (if j<1 then ((((((((((((((((0xf8e000 <<< 60) ||| 0x23e) <<< 60) ||| 0x0) <<< 120) ||| ((0x5cb000000 <<< 60) ||| 0x0)) <<< 240) ||| ((((0xeef000d68000000 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x394000000000))) <<< 540) ||| ((((((((0x0 <<< 60) ||| 0x0) <<< 60) ||| 0x10b) <<< 120) ||| ((0x819 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x890444000000000 <<< 60) ||| 0x0) <<< 120) ||| ((0x180000000 <<< 60) ||| 0x0)))) <<< 1020) ||| ((((((((((0x0 <<< 60) ||| 0x0) <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0xb300008de000)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0xda9 <<< 60) ||| 0x0))) <<< 480) ||| ((((((0x75846b000cd6 <<< 60) ||| 0x5b000000) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0xb61000000))))) <<< 2040) ||| ((((((((((((0x0 <<< 60) ||| 0x0) <<< 60) ||| 0x12f906000000000) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0x75fccd000000000 <<< 60) ||| 0x0))) <<< 480) ||| ((((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0x1da <<< 60) ||| 0x7b4f594d7000000)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0x44e000000000 <<< 60) ||| 0x246737)))) <<< 1020) ||| ((((((((((0x0 <<< 60) ||| 0x2b000000) <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x653000000000000)) <<< 240) ||| ((((0x603000a45000 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x934000000000))) <<< 480) ||| ((((((0x0 <<< 60) ||| 0xf8f000) <<< 120) ||| ((0x15000000a47 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x292000436000 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0xf3f000000)))))) <<< 4080) ||| ((((((((((((((0x0 <<< 60) ||| 0x0) <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0xa35142000000000)) <<< 240) ||| ((((0xb5c000 <<< 60) ||| 0xa56000000463000) <<< 120) ||| ((0x0 <<< 60) ||| 0xc89000412000000))) <<< 480) ||| ((((((0x2269b3 <<< 60) ||| 0x8b9000541000000) <<< 120) ||| ((0x688000 <<< 60) ||| 0x0)) <<< 240) ||| ((((0xcee2b0000 <<< 60) ||| 0x110) <<< 120) ||| ((0x0 <<< 60) ||| 0xd40000000000000)))) <<< 1020) ||| ((((((((((0xd9e000000000000 <<< 60) ||| 0x0) <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)) <<< 240) ||| ((((0xa4c00068b000000 <<< 60) ||| 0x808) <<< 120) ||| ((0xf16 <<< 60) ||| 0x69000000000))) <<< 480) ||| ((((((0x0 <<< 60) ||| 0xf3a000000) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x0 <<< 60) ||| 0xde20bc000000000) <<< 120) ||| ((0xd13232 <<< 60) ||| 0x966000000000000))))) <<< 2040) ||| ((((((((((((0x0 <<< 60) ||| 0xa1d000000000000) <<< 60) ||| 0x0) <<< 120) ||| ((0xc14000 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0xf1e000000 <<< 60) ||| 0xc38000000))) <<< 480) ||| ((((((0xf62000000000 <<< 60) ||| 0xfd2000) <<< 120) ||| ((0x0 <<< 60) ||| 0x45e)) <<< 240) ||| ((((0xf55000000 <<< 60) ||| 0x10d000000000000) <<< 120) ||| ((0x81a249000522000 <<< 60) ||| 0x0)))) <<< 1020) ||| ((((((((((0x0 <<< 60) ||| 0x1e7000f00) <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x721000000000000 <<< 60) ||| 0xece000000000) <<< 120) ||| ((0x2d7cc000b0f000 <<< 60) ||| 0x0))) <<< 480) ||| ((((((0x850000 <<< 60) ||| 0xbc1) <<< 120) ||| ((0x0 <<< 60) ||| 0x327000000000)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0x5049a3000 <<< 60) ||| 0x5004444000c1008))))))) else ((((((((((((((0x7 <<< 60) ||| 0xc70000000001280) <<< 120) ||| ((0xd230000 <<< 60) ||| 0x0)) <<< 180) ||| ((((0x0 <<< 60) ||| 0x5cf0) <<< 60) ||| 0xc310000000)) <<< 420) ||| ((((((0x4240000000000 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)) <<< 180) ||| ((((0xc2a00012c0 <<< 60) ||| 0xe5a0000000000) <<< 60) ||| 0x3330000000000))) <<< 780) ||| ((((((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0xd <<< 60) ||| 0x390000000000003)) <<< 180) ||| ((((0x64000b91f070000 <<< 60) ||| 0x0) <<< 60) ||| 0x0)) <<< 360) ||| ((((((0x0 <<< 60) ||| 0x41f000e) <<< 60) ||| 0x650000000000000) <<< 180) ||| ((((0x3540 <<< 60) ||| 0x1010000) <<< 60) ||| 0x6)))) <<< 1620) ||| ((((((((((0x520000000000000 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0xc0000510000)) <<< 180) ||| ((((0x3020000000000 <<< 60) ||| 0x0) <<< 60) ||| 0x23c0)) <<< 420) ||| ((((((0x0 <<< 60) ||| 0xe6d0000000000) <<< 120) ||| ((0x4850000000000 <<< 60) ||| 0x0)) <<< 180) ||| ((((0x0 <<< 60) ||| 0x0) <<< 60) ||| 0x0))) <<< 780) ||| ((((((((0x4f0000000 <<< 60) ||| 0x24a0) <<< 120) ||| ((0x1c0 <<< 60) ||| 0x0)) <<< 180) ||| ((((0x0 <<< 60) ||| 0x3250000000) <<< 60) ||| 0xf3b0000007)) <<< 360) ||| ((((((0x6e0000000000000 <<< 60) ||| 0xba80000) <<< 60) ||| 0x0) <<< 180) ||| ((((0x0 <<< 60) ||| 0x0) <<< 60) ||| 0x3290000000))))) <<< 3240) ||| ((((((((((((0xa3d0000 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)) <<< 180) ||| ((((0x0 <<< 60) ||| 0x0) <<< 60) ||| 0x0)) <<< 420) ||| ((((((0x86f0000 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)) <<< 180) ||| ((((0x0 <<< 60) ||| 0x657000b4be6c0) <<< 60) ||| 0x6a8b698a0000))) <<< 780) ||| ((((((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)) <<< 180) ||| ((((0x0 <<< 60) ||| 0x0) <<< 60) ||| 0x0)) <<< 360) ||| ((((((0x0 <<< 60) ||| 0x0) <<< 60) ||| 0x0) <<< 180) ||| ((((0x105000000e <<< 60) ||| 0x48000c200000000) <<< 60) ||| 0x0)))) <<< 1620) ||| ((((((((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x7600000000)) <<< 180) ||| ((((0xc2e0000 <<< 60) ||| 0xcd1a) <<< 60) ||| 0x900095d0001170)) <<< 420) ||| ((((((0xc84110000000000 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)) <<< 180) ||| ((((0x5670000 <<< 60) ||| 0xa9a0) <<< 60) ||| 0x0))) <<< 780) ||| ((((((((0x0 <<< 60) ||| 0x1430000000) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)) <<< 180) ||| ((((0x90a0000000000 <<< 60) ||| 0x1820e0) <<< 60) ||| 0x91b0000)) <<< 360) ||| ((((((0x7b20000 <<< 60) ||| 0x0) <<< 60) ||| 0x0) <<< 180) ||| ((((0x0 <<< 60) ||| 0x24d0000000000) <<< 60) ||| 0x0)))))))
def g123D9 (j : Nat) : Nat := 0xeb7313f
def g123H9 (j : Nat) : Nat := ((((((((((0x30900000 <<< 60) ||| 0x0) <<< 120) ||| ((0x994000028200000 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x30005212f001eb <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x2d00000000000))) <<< 420) ||| ((((((0x1ea <<< 60) ||| 0x1280000000000) <<< 120) ||| ((0x38d <<< 60) ||| 0xd100000000)) <<< 180) ||| ((((0x0 <<< 60) ||| 0x804ac) <<< 60) ||| 0x891a7))) <<< 840) ||| ((((((((0x30500000003ce <<< 60) ||| 0x0) <<< 120) ||| ((0xba40000000 <<< 60) ||| 0x243000000038a)) <<< 180) ||| ((((0x0 <<< 60) ||| 0xf9800) <<< 60) ||| 0x0)) <<< 420) ||| ((((((0x63c00 <<< 60) ||| 0x21c000000000000) <<< 120) ||| ((0x0 <<< 60) ||| 0x3e30000000000)) <<< 180) ||| ((((0x20b4184000000 <<< 60) ||| 0x0) <<< 60) ||| 0x25))))
def g123L : Nat → Packing
  | 5 => (41,4,4,0,0,6,0,g123D5)
  | 6 => (199,3,4,0,0,10,0,g123D6)
  | 7 => (112,2,4,0,0,12,0,g123D7)
  | 8 => (17,1,4,0,0,9,0,g123D8)
  | 9 => (1,0,4,0,0,0,0,g123D9)
  | _ => emptyPacking
def g123I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 11 184 5 11 6 1 g123H6
  | 7 => lookupWord 52 533 5 13 8 1 g123H7
  | 8 => lookupWord 30 1239 2 12 7 1 g123H8
  | 9 => lookupWord 5 175 2 10 5 1 g123H9
  | _ => fun _ => none
def g123 : Forest := ⟨123,9,fun i => g123Y[i]?.getD (0,0),g123C,g123A,g123L,g123I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P5_0 : block g123 5 0 41=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g123B5 : block g123 5 0 41=true := g123P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P6_0 : block g123 6 0 13=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P6_13 : block g123 6 13 48=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P6_61 : block g123 6 61 48=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P6_109 : block g123 6 109 48=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P6_157 : block g123 6 157 42=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g123B6 : block g123 6 0 199=true := (@block_merge g123 6 0 61 138 (@block_merge g123 6 0 13 48 g123P6_0 g123P6_13) (@block_merge g123 6 61 48 90 g123P6_61 (@block_merge g123 6 109 48 42 g123P6_109 g123P6_157)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P7_0 : block g123 7 0 8=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P7_8 : block g123 7 8 48=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P7_56 : block g123 7 56 13=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P7_69 : block g123 7 69 43=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g123B7 : block g123 7 0 112=true := (@block_merge g123 7 0 56 56 (@block_merge g123 7 0 8 48 g123P7_0 g123P7_8) (@block_merge g123 7 56 13 43 g123P7_56 g123P7_69))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P8_0 : block g123 8 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P8_2 : block g123 8 2 15=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g123B8 : block g123 8 0 17=true := (@block_merge g123 8 0 2 15 g123P8_0 g123P8_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P9_0 : block g123 9 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g123B9 : block g123 9 0 1=true := g123P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123T : checkedTables g123 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g123 0 0 0 = true)
  · exact (rfl : block g123 1 0 0 = true)
  · exact (rfl : block g123 2 0 0 = true)
  · exact (rfl : block g123 3 0 0 = true)
  · exact (rfl : block g123 4 0 0 = true)
  · exact g123B5
  · exact g123B6
  · exact g123B7
  · exact g123B8
  · exact g123B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123G : graphValid g123 (boundsBefore K119) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low123 : Lower true (varsX 123) (graphGoal 123) 10 := lower_forest (g:=g123) (i:=0) (hints:=67) (before_sound K119 V119) g123G g123T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K123 := extendKnown K119 10 [(123,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V123 : Known true K123 := extend_ok (m:=123) V119 low123 (by decide +kernel)
def g125Y : Array (Bits × Bits) := #[(((((0xffffffff <<< 60) ||| 0xfffffffffffc018) <<< 60) ||| 0x1f0cc7b1f091f11),((((0xffffffff <<< 60) ||| 0xfffffffffff8020) <<< 60) ||| 0x20041947000a11)),(0x0,0x0),(((((0xffffffff <<< 60) ||| 0xfffffffffff80e0) <<< 60) ||| 0xf3281c0d7891f),((((0xffffffff <<< 60) ||| 0xfffffffffffc06a) <<< 60) ||| 0x4b92c19c0d58915)),(0x107e104f24215439e6,0x400e144922801411a6),(0x3e0801f904bc0aa52e6,0xe04906d042002a10e2),(((((0xffffffff <<< 60) ||| 0xfffffffffffc00f) <<< 60) ||| 0xfe002042aefc469),0x69df1c8124428ebc448),(0x7ff000023903430e498,0x3190000028438006408),(0x0,0x0),(0x0,0x0)]
def g125C : List ColumnInfo := [(9,32,84,0,4),(80,4,41,0,4),(32,0,93,0,7),(4,0,121,0,7),(17,0,108,0,4),(41,0,84,0,4),(24,0,101,0,4),(64,0,61,0,7),(52,0,73,0,4),(16,0,109,0,7),(1,0,124,0,7),(84,0,41,0,4),(72,0,53,0,4),(44,0,81,0,4),(8,0,117,0,7)]
def g125A : List (List Nat) := [[],[96,82,67]]
def g125D5 (j : Nat) : Nat := ((((((0x20c080000014 <<< 60) ||| 0x303d25493254130) <<< 120) ||| ((0xcb764dc553482da <<< 60) ||| 0xe0d5254120e6963)) <<< 180) ||| ((((0x54950482da61532 <<< 60) ||| 0x54120f49534c950) <<< 60) ||| 0x483d8dc95254110))
def g125D6 (j : Nat) : Nat := ((((((((((((0x1810820 <<< 60) ||| 0x108082302800c10) <<< 60) ||| 0x8080101e20400) <<< 120) ||| ((0x8099e20800c0026 <<< 60) ||| 0x400200080021040)) <<< 240) ||| ((((0x43020028f478f <<< 60) ||| 0xce851e1fafd001) <<< 120) ||| ((0xc8678219e1c4ce <<< 60) ||| 0x59a98f0002190d2))) <<< 540) ||| ((((((((0x47e3c1e00078219 <<< 60) ||| 0x9086502810c002f) <<< 60) ||| 0xa0027ebaec0994) <<< 120) ||| ((0xfd73d89509fcec9 <<< 60) ||| 0x92a13f5cb654c2e)) <<< 240) ||| ((((0xfb9aca984fd75d8 <<< 60) ||| 0x930bbeea99261b7) <<< 120) ||| ((0xd95324c3e6a9264 <<< 60) ||| 0x987db7354130df6)))) <<< 1080) ||| ((((((((((0xc4a8261de549504 <<< 60) ||| 0xc3ec992a0984ff7) <<< 60) ||| 0x359520ddee4b2a4) <<< 120) ||| ((0x13fdd5634827ebb <<< 60) ||| 0x2a6905f77154d20)) <<< 240) ||| ((((0xbdee6a9241bb58d <<< 60) ||| 0x52482f7baa64905) <<< 120) ||| ((0xed754c920ddaca9 <<< 60) ||| 0x9241f354d324835))) <<< 540) ||| ((((((((0xfb22a2906bf644c <<< 60) ||| 0x520df2c6a8241de) <<< 60) ||| 0x54d50483f5b92a0) <<< 120) ||| ((0x907e93254120fe6 <<< 60) ||| 0xe4a8221fc5c9504)) <<< 240) ||| ((((0x43f8b9260884bd7 <<< 60) ||| 0x5d9120ed2a4a824) <<< 120) ||| ((0x1dc54950443e899 <<< 60) ||| 0x260887315454110)))))
def g125H6 (j : Nat) : Nat := ((((0x200000002 <<< 60) ||| 0xf15802a80001c98) <<< 60) ||| 0xfec9485d0600010)
def g125D7 (j : Nat) : Nat := ((((((((((((0x31200304018314 <<< 60) ||| 0x844c10c611200) <<< 60) ||| 0x43010041174e204) <<< 120) ||| ((0x1622c10c120214 <<< 60) ||| 0x30460059c304010)) <<< 240) ||| ((((0x200404414304010 <<< 60) ||| 0x518416304018400) <<< 120) ||| ((0x10cc14120015918 <<< 60) ||| 0x40c50401cc05700))) <<< 540) ||| ((((((((0x4185ce205900705 <<< 60) ||| 0x70032c00802c200) <<< 60) ||| 0x10b9df30042c508) <<< 120) ||| ((0x50420400b20010c <<< 60) ||| 0x4c80044ab036c32)) <<< 240) ||| ((((0xf4b8acaab28e9aa <<< 60) ||| 0x529021c7f9e06f1) <<< 120) ||| ((0x925e95649908360 <<< 60) ||| 0xc02b89c2288a0d8)))) <<< 1020) ||| ((((((((((0x8a1b05a12036078 <<< 60) ||| 0xff58132ffd895) <<< 60) ||| 0xff58950ff4c950) <<< 120) ||| ((0xff54540ff59530f <<< 60) ||| 0xf58930ff54930ff)) <<< 240) ||| ((((0x54d20ff54520ff4 <<< 60) ||| 0xc520bfd8132bfd8) <<< 120) ||| ((0x950bfd9530bfd89 <<< 60) ||| 0x30f74c930fe5413))) <<< 480) ||| ((((((0xbf59520bf58d20 <<< 60) ||| 0xfb54920fb4c920f) <<< 120) ||| ((0xe54120fd54b10fd <<< 60) ||| 0x4cb10bfd8910fdd)) <<< 240) ||| ((((0x8910fd54910fd4c <<< 60) ||| 0x910afd9120ed953) <<< 120) ||| ((0x10ed95110ed5511 <<< 60) ||| 0xfc54110fc4c110)))))
def g125H7 (j : Nat) : Nat := ((((((((((((((0xc0000006912400 <<< 60) ||| 0x154c) <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x2280018)) <<< 300) ||| ((((((0x68000000014a800 <<< 60) ||| 0x13400000000e2c0) <<< 60) ||| 0x0) <<< 120) ||| ((0x396000000000 <<< 60) ||| 0x0))) <<< 540) ||| ((((((((0x7170000038c0 <<< 60) ||| 0x18f00) <<< 60) ||| 0x168000000000) <<< 120) ||| ((0x18180 <<< 60) ||| 0xe3800000000)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x43200000000) <<< 120) ||| ((0x3090000000 <<< 60) ||| 0x0)))) <<< 1140) ||| ((((((((((0x0 <<< 60) ||| 0x22300000) <<< 60) ||| 0x3a8800000000000) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)) <<< 300) ||| ((((((0x0 <<< 60) ||| 0x34400000000000) <<< 60) ||| 0xb7c0) <<< 120) ||| ((0x383800 <<< 60) ||| 0x0))) <<< 540) ||| ((((((((0x2 <<< 60) ||| 0x0) <<< 60) ||| 0x0) <<< 120) ||| ((0x6 <<< 60) ||| 0x250000000000000)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x6220000))))) <<< 2280) ||| ((((((((((((0x0 <<< 60) ||| 0x0) <<< 60) ||| 0x34f) <<< 120) ||| ((0x74f000018000000 <<< 60) ||| 0x0)) <<< 300) ||| ((((((0x3 <<< 60) ||| 0xd40000000000000) <<< 60) ||| 0x200000) <<< 120) ||| ((0x0 <<< 60) ||| 0x710714))) <<< 540) ||| ((((((((0x361800001c808 <<< 60) ||| 0xe80000000000000) <<< 60) ||| 0x437b) <<< 120) ||| ((0x200000000000000 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x1f70000) <<< 120) ||| ((0x48200 <<< 60) ||| 0x4b2000)))) <<< 1140) ||| ((((((((((0x0 <<< 60) ||| 0x0) <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x1e2c00000c120)) <<< 300) ||| ((((((0x0 <<< 60) ||| 0x110000000000) <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0xa3e0000000000))) <<< 540) ||| ((((((((0x2e81000000 <<< 60) ||| 0x0) <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)) <<< 240) ||| ((((0xb84000000000010 <<< 60) ||| 0x700000000048400) <<< 120) ||| ((0x1098000 <<< 60) ||| 0x3005))))))
def g125D8 (j : Nat) : Nat := ((((((((0x999 <<< 60) ||| 0xc94040384013748) <<< 60) ||| 0x88d084a3ce4100) <<< 180) ||| ((((0xd72a002112a4040 <<< 60) ||| 0x31441cde601c430) <<< 60) ||| 0x449286b00a3928)) <<< 300) ||| ((((((0x20163b0d79b8d7e <<< 60) ||| 0xa5409607c1f007f) <<< 60) ||| 0x4cbfa83fd31fe90) <<< 120) ||| ((0xff543fa81fd30fe <<< 60) ||| 0x907f443ee21f510)))
def g125H8 (j : Nat) : Nat := ((((((((((0x5c6001218 <<< 60) ||| 0x0) <<< 120) ||| ((0xc3e8a000425 <<< 60) ||| 0x470000000000038)) <<< 240) ||| ((((0xc800d9c63400604 <<< 60) ||| 0x6120018bcc30000) <<< 120) ||| ((0x19a00000 <<< 60) ||| 0x593000000000000))) <<< 480) ||| ((((((0x420d2a00 <<< 60) ||| 0x3b0000007) <<< 120) ||| ((0x80000014c00000 <<< 60) ||| 0x587001e04)) <<< 240) ||| ((((0xa60000007840000 <<< 60) ||| 0x2c60006ac) <<< 120) ||| ((0x0 <<< 60) ||| 0x147000)))) <<< 900) ||| ((((((((0xa3a00000000d061 <<< 60) ||| 0x7c002d0a0400000) <<< 120) ||| ((0x186c000000 <<< 60) ||| 0x24500000000)) <<< 240) ||| ((((0x84000 <<< 60) ||| 0x174400000dc) <<< 120) ||| ((0xaaa9f935443 <<< 60) ||| 0x488000000000000))) <<< 420) ||| ((((((0x10140054f000 <<< 60) ||| 0x1a780) <<< 120) ||| ((0xd2c00000000 <<< 60) ||| 0x1506e90000017)) <<< 180) ||| ((((0x2c00000a0111c00 <<< 60) ||| 0xb) <<< 60) ||| 0x17f2800000d0100))))
def g125D9 (j : Nat) : Nat := 0xea97321bf
def g125H9 (j : Nat) : Nat := ((((((((0x4140000 <<< 60) ||| 0x4cc0000000000) <<< 120) ||| ((0x290000000b8000 <<< 60) ||| 0xe00)) <<< 180) ||| ((((0x1880000000000 <<< 60) ||| 0x680032a00a08) <<< 60) ||| 0x3e463ea0000000)) <<< 360) ||| ((((((0x588000000000000 <<< 60) ||| 0x0) <<< 60) ||| 0x120e50000000) <<< 180) ||| ((((0xae88000000 <<< 60) ||| 0x84000) <<< 60) ||| 0x24c000000001c0)))
def g125L : Nat → Packing
  | 5 => (7,4,4,0,0,5,0,g125D5)
  | 6 => (38,3,4,0,0,9,0,g125D6)
  | 7 => (34,2,4,0,0,10,0,g125D7)
  | 8 => (11,1,4,0,0,9,0,g125D8)
  | 9 => (1,0,4,0,0,0,0,g125D9)
  | _ => emptyPacking
def g125I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 2 18 5 8 3 1 g125H6
  | 7 => lookupWord 10 415 2 11 6 1 g125H7
  | 8 => lookupWord 10 166 2 11 6 1 g125H8
  | 9 => lookupWord 3 83 3 9 4 1 g125H9
  | _ => fun _ => none
def g125 : Forest := ⟨125,9,fun i => g125Y[i]?.getD (0,0),g125C,g125A,g125L,g125I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P5_0 : block g125 5 0 7=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g125B5 : block g125 5 0 7=true := g125P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P6_0 : block g125 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P6_1 : block g125 6 1 4=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P6_5 : block g125 6 5 33=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g125B6 : block g125 6 0 38=true := (@block_merge g125 6 0 1 37 g125P6_0 (@block_merge g125 6 1 4 33 g125P6_1 g125P6_5))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P7_0 : block g125 7 0 6=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P7_6 : block g125 7 6 17=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P7_23 : block g125 7 23 11=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g125B7 : block g125 7 0 34=true := (@block_merge g125 7 0 6 28 g125P7_0 (@block_merge g125 7 6 17 11 g125P7_6 g125P7_23))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P8_0 : block g125 8 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P8_2 : block g125 8 2 9=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g125B8 : block g125 8 0 11=true := (@block_merge g125 8 0 2 9 g125P8_0 g125P8_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P9_0 : block g125 9 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g125B9 : block g125 9 0 1=true := g125P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125T : checkedTables g125 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g125 0 0 0 = true)
  · exact (rfl : block g125 1 0 0 = true)
  · exact (rfl : block g125 2 0 0 = true)
  · exact (rfl : block g125 3 0 0 = true)
  · exact (rfl : block g125 4 0 0 = true)
  · exact g125B5
  · exact g125B6
  · exact g125B7
  · exact g125B8
  · exact g125B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125G : graphValid g125 (boundsBefore K123) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low125 : Lower true (varsX 125) (graphGoal 125) 10 := lower_forest (g:=g125) (i:=0) (hints:=1027) (before_sound K123 V123) g125G g125T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K125 := extendKnown K123 10 [(125,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V125 : Known true K125 := extend_ok (m:=125) V123 low125 (by decide +kernel)
def g126Y : Array (Bits × Bits) := #[(0x0,0x0),(((((0xffffffff <<< 60) ||| 0xfffffffffffffe0) <<< 60) ||| 0x201b0fed41e65c3),0x2244b04654162542),(0x830ec00739b1c258,0x300e21739b04210),(0x103f0ff040a2cb124,0x310f1040a0ca020),(((((0xffffffff <<< 60) ||| 0xfffffffffffffe7) <<< 60) ||| 0xc010007ef4d9e29),((((0xffffffff <<< 60) ||| 0xfffffffffffffe0) <<< 60) ||| 0xc01042082099829)),(0x18001fff821f358a6,0x1c8890eb9a1e15884),(0x1fffe000032c22dd0,0x1f0ee08c0044205c0),(0x0,0x0),(0x0,0x0)]
def g126C : List ColumnInfo := [(20,0,106,0,4),(10,32,84,0,4),(72,0,54,0,4),(42,0,84,0,4),(2,0,124,0,7),(8,0,118,0,7),(4,0,122,0,7)]
def g126A : List (List Nat) := [[],[49,100]]
def g126D5 (j : Nat) : Nat := 0x4f77159653
def g126D6 (j : Nat) : Nat := ((((0x100 <<< 60) ||| 0x2002006d60bf596) <<< 120) ||| ((0x53fdd8553bdd855 <<< 60) ||| 0x3bd58453be58053))
def g126H6 (j : Nat) : Nat := 0x800000000
def g126D7 (j : Nat) : Nat := ((((0xb0f44063d2c <<< 60) ||| 0x1e1db0c8406807) <<< 60) ||| 0x807f94ffaa7fc53)
def g126H7 (j : Nat) : Nat := ((((0x62000000000 <<< 60) ||| 0xe10000) <<< 120) ||| ((0x1400d3007 <<< 60) ||| 0x800006000000000))
def g126D8 (j : Nat) : Nat := 0x58f117f
def g126H8 (j : Nat) : Nat := ((((0x1380 <<< 60) ||| 0x3a000000) <<< 60) ||| 0x184000f000000)
def g126L : Nat → Packing
  | 5 => (1,3,3,0,0,0,0,g126D5)
  | 6 => (5,2,3,0,0,5,0,g126D6)
  | 7 => (3,1,3,0,0,7,0,g126D7)
  | 8 => (1,0,3,0,0,0,0,g126D8)
  | _ => emptyPacking
def g126I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 8 0 6 1 1 g126H6
  | 7 => lookupWord 1 31 0 8 3 1 g126H7
  | 8 => lookupWord 1 19 0 7 2 1 g126H8
  | _ => fun _ => none
def g126 : Forest := ⟨126,8,fun i => g126Y[i]?.getD (0,0),g126C,g126A,g126L,g126I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P5_0 : block g126 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g126B5 : block g126 5 0 1=true := g126P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6_0 : block g126 6 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6_3 : block g126 6 3 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g126B6 : block g126 6 0 5=true := (@block_merge g126 6 0 3 2 g126P6_0 g126P6_3)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7_0 : block g126 7 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g126B7 : block g126 7 0 3=true := g126P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P8_0 : block g126 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g126B8 : block g126 8 0 1=true := g126P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126T : checkedTables g126 8 := by
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
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126G : graphValid g126 (boundsBefore K125) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low126 : Lower true (varsX 126) (graphGoal 126) 9 := lower_forest (g:=g126) (i:=0) (hints:=34690112) (before_sound K125 V125) g126G g126T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K126 := extendKnown K125 9 [(126,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V126 : Known true K126 := extend_ok (m:=126) V125 low126 (by decide +kernel)
def g127Y : Array (Bits × Bits) := #[(((((0x64ce3fc <<< 60) ||| 0xe03c39b9ffe0415) <<< 60) ||| 0x41d01c1c4095d20),((((0x6188 <<< 60) ||| 0x3c01981b00000) <<< 60) ||| 0x4008140004c20)),(((((0xe0710381 <<< 60) ||| 0x144fc63e0710890) <<< 60) ||| 0x840043e08d34fa3),((((0xe573c9a8 <<< 60) ||| 0x546d0f38d750090) <<< 60) ||| 0x840043608434da1)),(((((0xe081fc02 <<< 60) ||| 0x18700bc07800067) <<< 60) ||| 0x24e1032ed4cb1),((((0xe16108 <<< 60) ||| 0x36786fd07e40047) <<< 60) ||| 0x461032cd4ca0)),(((((0x18fe0004 <<< 60) ||| 0x1f800c007fe3718) <<< 60) ||| 0xe092e038619acc),((((0x8f40000 <<< 60) ||| 0x15800c026464030) <<< 60) ||| 0xd08670106112c4)),(((((0x19000007 <<< 60) ||| 0xe0000fff801d869) <<< 60) ||| 0xf13623ec32072dc),((((0x1a040000 <<< 60) ||| 0x10080060004920) <<< 60) ||| 0x51ba0488120125c)),(((((0x1e000007 <<< 60) ||| 0xfffff0000011f8d) <<< 60) ||| 0x6c4900b79ea03e),((((0x12081247 <<< 60) ||| 0xaa02f0050081f4d) <<< 60) ||| 0x3295900a79ca01a)),(((((0xfffffff8 <<< 60) ||| 0x1e00e) <<< 60) ||| 0x380fc030d56a541),((((0xe50a9e77 <<< 60) ||| 0xc8030021809b608) <<< 60) ||| 0x20019060c12a101)),(0x0,0x0),(0x0,0x0)]
def g127C : List ColumnInfo := [(82,4,41,0,4),(11,32,84,0,4),(52,2,73,0,4),(73,0,54,0,4),(9,0,118,0,7),(32,0,95,0,9),(4,0,123,0,10),(21,0,106,0,4),(43,0,84,0,4),(28,0,99,0,4),(66,0,61,0,7),(20,0,107,0,7),(2,0,125,0,10),(1,0,126,0,9),(8,0,119,0,9),(100,0,27,0,4),(5,0,122,0,7),(3,0,124,0,7),(46,0,81,0,4),(69,0,58,0,4),(19,0,108,0,4),(26,0,101,0,4),(37,0,90,0,4),(36,0,91,0,7),(18,0,109,0,7),(74,0,53,0,4),(10,0,117,0,7),(86,0,41,0,4),(13,0,114,0,4),(54,0,73,0,4),(34,0,93,0,7),(6,0,121,0,7)]
def g127A : List (List Nat) := [[]]
def g127D5 (j : Nat) : Nat := ((((((0x20f5d <<< 60) ||| 0x835343f04b22a7c) <<< 120) ||| ((0x2c5d994645801d9 <<< 60) ||| 0x43cd2348d0b203b)) <<< 240) ||| ((((0x2c6a1e4a8a7e999 <<< 60) ||| 0x650d40482d50d91) <<< 120) ||| ((0xcc2ac8a02211ac <<< 60) ||| 0xee9962594350110)))
def g127D6 (j : Nat) : Nat := (if j<1 then ((((((((((((((((0x20c3b25f <<< 60) ||| 0x9661943482bcba3) <<< 60) ||| 0x6178458120af2e8) <<< 120) ||| ((0xd95e11604826e9a <<< 60) ||| 0x3e598458120af86)) <<< 240) ||| ((((0x878561160482bcb <<< 60) ||| 0xa361584581209ba) <<< 120) ||| ((0xea585d9160482ec <<< 60) ||| 0xba36176458120bb))) <<< 540) ||| ((((((((0x86878559160482e <<< 60) ||| 0xaba46156458120b) <<< 60) ||| 0xb2e8d8559160482) <<< 120) ||| ((0xecba36116358120 <<< 60) ||| 0xbb26938358d6048)) <<< 240) ||| ((((0x26e9a6e61435812 <<< 60) ||| 0x9bae999850d604) <<< 120) ||| ((0x834e8a765943581 <<< 60) ||| 0x20baae998450d60)))) <<< 1020) ||| ((((((((((0x483b898460d4358 <<< 60) ||| 0x120fa25918350d6) <<< 60) ||| 0x483e898458d435) <<< 120) ||| ((0x8120af8e8595e19 <<< 60) ||| 0x40482baba465586)) <<< 240) ||| ((((0x50120af2e8d9561 <<< 60) ||| 0x940482be3a16558) <<< 120) ||| ((0x650120eaae5b946 <<< 60) ||| 0x19404832eb96619))) <<< 480) ||| ((((((0x8550120cf8e1b91 <<< 60) ||| 0x615404833e186e4) <<< 120) ||| ((0x585501209eaea58 <<< 60) ||| 0x599140482eaba66)) <<< 240) ||| ((((0x156450120be8e85 <<< 60) ||| 0x85591404832eb96) <<< 120) ||| ((0x6198350120daae5 <<< 60) ||| 0x96460d40483aab8))))) <<< 2040) ||| ((((((((((((0x659183501209ea6 <<< 60) ||| 0x939858d40482eab) <<< 60) ||| 0xa66516350120d6a) <<< 120) ||| ((0x29d9650d404836a <<< 60) ||| 0xba66594350120be)) <<< 240) ||| ((((0x2e8d8650d40483a <<< 60) ||| 0xaba66194350120e) <<< 120) ||| ((0xe2e8d8650d40482 <<< 60) ||| 0xf89a6e0d4350120))) <<< 480) ||| ((((((0xee261b8350d4048 <<< 60) ||| 0x3e8b9658d435012) <<< 120) ||| ((0xaf8e8183e09644 <<< 60) ||| 0x42be3a064f82591)) <<< 240) ||| ((((0x108fc6a684e0163 <<< 60) ||| 0x442af1a6a138058) <<< 120) ||| ((0xd10af8e8984e016 <<< 60) ||| 0x3442bd3a35db805)))) <<< 1020) ||| ((((((((((0x8d10abc69a94e01 <<< 60) ||| 0x63442bd1a3a5380) <<< 60) ||| 0x58d10af8e8994e0) <<< 120) ||| ((0x1634433e3a26538 <<< 60) ||| 0x58d108fc6a674e)) <<< 240) ||| ((((0x163442bd1a39d3 <<< 60) ||| 0x8058d108fc6a664) <<< 120) ||| ((0xe0163442bd1a399 <<< 60) ||| 0x38058d10af8e896))) <<< 480) ||| ((((((0x4e01634433e392e <<< 60) ||| 0x418650d10cf8e8b) <<< 120) ||| ((0x90619434422f7a9 <<< 60) ||| 0x6188650d10cbc61)) <<< 240) ||| ((((0x990219434423f3a <<< 60) ||| 0x6636450d109f4e) <<< 120) ||| ((0x8193d9143442ea5 <<< 60) ||| 0xa22196450d10bac)))))) <<< 4080) ||| ((((((((((((((0x6808659143442ed <<< 60) ||| 0x1a02196350d10be) <<< 60) ||| 0x46826458d434437) <<< 120) ||| ((0x9264e416350d10d <<< 60) ||| 0xe45939058d43442)) <<< 240) ||| ((((0xf33a45956454110 <<< 60) ||| 0xdd8657925915044) <<< 120) ||| ((0x3761a5e49645411 <<< 60) ||| 0xdd859792591504))) <<< 480) ||| ((((((0x427e3a265363541 <<< 60) ||| 0x10bd8e896454d50) <<< 120) ||| ((0x4427e3a26594354 <<< 60) ||| 0x110de8e53926194)) <<< 240) ||| ((((0x4432f3a9618865 <<< 60) ||| 0x110de469193219) <<< 120) ||| ((0x40442be3a261b85 <<< 60) ||| 0x50110cbce5a8661)))) <<< 1020) ||| ((((((((((0x540442be3a26198 <<< 60) ||| 0x550110af468c866) <<< 60) ||| 0x1540442be1a2219) <<< 120) ||| ((0x8550110bace9985 <<< 60) ||| 0x59140443ab08661)) <<< 240) ||| ((((0x56450110fa8e1b9 <<< 60) ||| 0x2591404437a195e) <<< 120) ||| ((0x496450110de864f <<< 60) ||| 0x92591404427b3a9))) <<< 480) ||| ((((((0x61a5450110de461 <<< 60) ||| 0x99395140442fa3a) <<< 120) ||| ((0x26195450110eac6 <<< 60) ||| 0x188655140442f91)) <<< 240) ||| ((((0xa32195450110be8 <<< 60) ||| 0x68886551404436b) <<< 120) ||| ((0x3965918350110ea <<< 60) ||| 0xce196460d404427))))) <<< 2040) ||| ((((((((((((0xb1a4e6163501108 <<< 60) ||| 0xfc6939858d40442) <<< 60) ||| 0xeb1a6a516350110) <<< 120) ||| ((0xbace999458d4044 <<< 60) ||| 0x2f91a3991635011)) <<< 240) ||| ((((0xdcc61995d0d404 <<< 60) ||| 0x436b396d9143501) <<< 120) ||| ((0x10dace596450d40 <<< 60) ||| 0x442fa3a25914350))) <<< 480) ||| ((((((0x1109ec6a69650d4 <<< 60) ||| 0x4436b396a59435) <<< 120) ||| ((0x110be468e9650d <<< 60) ||| 0x40442fa3a265943)) <<< 240) ||| ((((0x50110dace999650 <<< 60) ||| 0xd404437a3a26594) <<< 120) ||| ((0x3501109ecaa4965 <<< 60) ||| 0xd40442bb2a8259)))) <<< 1020) ||| ((((((((((0x4350110dac65896 <<< 60) ||| 0x50d40442fa1a225) <<< 60) ||| 0x943501109ec6a68) <<< 120) ||| ((0x650d40443ab386a <<< 60) ||| 0x194350110be468e)) <<< 240) ||| ((((0x8650d40442f93a3 <<< 60) ||| 0x6194350110be8e8) <<< 120) ||| ((0x98650d404427b2a <<< 60) ||| 0x92194350110be46))) <<< 480) ||| ((((((0x8c8650d40442fa1 <<< 60) ||| 0xa22194350110be4) <<< 120) ||| ((0x69b8350d40443b9 <<< 60) ||| 0x186e0d4350110fa)) <<< 240) ||| ((((0x4e596350d40443e <<< 60) ||| 0x909658d43501108) <<< 120) ||| ((0xbcea58621940442 <<< 60) ||| 0xea1a22196450110))))))) else (if j<2 then ((((((((((((((((0xa0d068a0 <<< 60) ||| 0x400d068341a0d06) <<< 60) ||| 0x8341a0d06860300) <<< 120) ||| ((0xd06834200d0025e <<< 60) ||| 0x5a0e4575dc964a7)) <<< 240) ||| ((((0x9e8575603725929 <<< 60) ||| 0xeba05d580dc964c) <<< 120) ||| ((0xabe5b9460372592 <<< 60) ||| 0x9eba05cd80dc964))) <<< 540) ||| ((((((((0x979683916177259 <<< 60) ||| 0x29e7a161583dc96) <<< 60) ||| 0x4a79e8585603725) <<< 120) ||| ((0x929cfa365580dc9 <<< 60) ||| 0x64a79e859560372)) <<< 240) ||| ((((0x5929eba065580dc <<< 60) ||| 0x964a7ae81936037) <<< 120) ||| ((0x25925e5a0e4964d <<< 60) ||| 0xc554a79e8964603)))) <<< 1020) ||| ((((((((((0x715521eda9a1f82 <<< 60) ||| 0x59153a7ae8187e0) <<< 60) ||| 0x96454e9eba065f8) <<< 120) ||| ((0x259153cd6655936 <<< 60) ||| 0x6454f1ea97649)) <<< 240) ||| ((((0x8019153a79e8585 <<< 60) ||| 0xe097650e9eba061) <<< 120) ||| ((0x7825d943a7a6839 <<< 60) ||| 0x2e017650f8b9766))) <<< 480) ||| ((((((0x51801d943e365d9 <<< 60) ||| 0x936007650f8f176) <<< 120) ||| ((0x645801d943cec65 <<< 60) ||| 0x1916007650e9e7a)) <<< 240) ||| ((((0x25db815d543a796 <<< 60) ||| 0x8876e057550e9f1) <<< 120) ||| ((0xa01db815d543da6 <<< 60) ||| 0x68d901d96450f6b))))) <<< 2040) ||| ((((((((((((0x1a16407659143b2 <<< 60) ||| 0xb688765d56450ec) <<< 60) ||| 0xb9a01d97559143d) <<< 120) ||| ((0x2e5d9901d95450f <<< 60) ||| 0x699a46407658d43)) <<< 240) ||| ((((0xdb4685901d96350 <<< 60) ||| 0xee99a01d95458d4) <<< 120) ||| ((0x3b2b68876591705 <<< 60) ||| 0xecb5a11d9645c1))) <<< 480) ||| ((((((0x43a7968775e0974 <<< 60) ||| 0x5829cfa35d7825d) <<< 120) ||| ((0x160877ea57560c7 <<< 60) ||| 0x458389d655d1831)) <<< 240) ||| ((((0xd160a73e8d75608 <<< 60) ||| 0x745829d7a35d581) <<< 120) ||| ((0x1d160d275d5931d <<< 60) ||| 0x1645834ad756487)))) <<< 1020) ||| ((((((((((0x459160da6593905 <<< 60) ||| 0x8d43582e99a09d1) <<< 60) ||| 0x6350d60aae69286) <<< 120) ||| ((0x601435821eda9a1 <<< 60) ||| 0xf8259150a73e8d8)) <<< 240) ||| ((((0x7e09645429cfa36 <<< 60) ||| 0x5f8259150a73e8d) <<< 120) ||| ((0x76e096454335995 <<< 60) ||| 0x6418319150a73e8))) <<< 480) ||| ((((((0x984dcf635429cfa <<< 60) ||| 0x3617825d940a79e) <<< 120) ||| ((0x8585e09765029e7 <<< 60) ||| 0xa25db815d540a75)) <<< 240) ||| ((((0x68c76e05755029e <<< 60) ||| 0x5a21db815d540b2) <<< 120) ||| ((0xb688765d5645022 <<< 60) ||| 0xbfa96188650d40c)))))) <<< 4080) ||| ((((((((((((((0xae6199021943502 <<< 60) ||| 0xe99a02196350d40) <<< 60) ||| 0xda6691931d96050) <<< 120) ||| ((0x36996564c845814 <<< 60) ||| 0xbac68487591605)) <<< 240) ||| ((((0x2eb3a165564581 <<< 60) ||| 0x40bac6878559160) <<< 120) ||| ((0x502e9ba36156458 <<< 60) ||| 0x140bace85755916))) <<< 480) ||| ((((((0x5036a995e49645 <<< 60) ||| 0x8140daa64f92591) <<< 120) ||| ((0x605036b164e4554 <<< 60) ||| 0x58140ba668c7655)) <<< 240) ||| ((((0x160502cb9a69937 <<< 60) ||| 0x358140f2ae8964d) <<< 120) ||| ((0xcd60502e99a3a51 <<< 60) ||| 0x6358140f2659373)))) <<< 1020) ||| ((((((((((0x50d605026b9a9a5 <<< 60) ||| 0x94358140ba668e9) <<< 60) ||| 0x650d605036aba26) <<< 120) ||| ((0x594358140ba668c <<< 60) ||| 0x7650d605020ffa9)) <<< 240) ||| ((((0x618865d130c37e5 <<< 60) ||| 0xb9361d644c31db9) <<< 120) ||| ((0x3e418759130b2b6 <<< 60) ||| 0x88965d1644c2cb5))) <<< 480) ||| ((((((0xa12597459130d66 <<< 60) ||| 0xe4f905d1644c22d) <<< 120) ||| ((0xfa96188650d30cb <<< 60) ||| 0x661990219434c2e)) <<< 240) ||| ((((0x8da22196450d30b <<< 60) ||| 0xa568486591434c2) <<< 120) ||| ((0xe99a02196450d30 <<< 60) ||| 0xd365d193d91604c))))) <<< 2040) ||| ((((((((((((0x34b9965d2645813 <<< 60) ||| 0xe2e2a174591604) <<< 60) ||| 0xc3c9ba35d164581) <<< 120) ||| ((0x30f2a5d39259160 <<< 60) ||| 0x4c36c993e496458)) <<< 240) ||| ((((0x130f265d26458d6 <<< 60) ||| 0x4c3c9974591635) <<< 120) ||| ((0x8130bb2e896458d <<< 60) ||| 0x604c2ad9a8a5163))) <<< 480) ||| ((((((0x58130bb2e899458 <<< 60) ||| 0xd604c26d9a9a116) <<< 120) ||| ((0x358130b3669e845 <<< 60) ||| 0x8d604c2ecba2611)) <<< 240) ||| ((((0x6358130d362a574 <<< 60) ||| 0x58d604c38d8a85d) <<< 120) ||| ((0x16358130ba66929 <<< 60) ||| 0x650d604c36cba26)))) <<< 1020) ||| ((((((((((0x594358130ba669a <<< 60) ||| 0x8450d604c2e9ba6) <<< 60) ||| 0x61143581309b66a) <<< 120) ||| ((0x76450d604c2e99a <<< 60) ||| 0x69914358130fa2e)) <<< 240) ||| ((((0x896450d604c2f4b <<< 60) ||| 0xa25915354130b56) <<< 120) ||| ((0x69c6454d504c2f4 <<< 60) ||| 0x9a21915354130bd))) <<< 480) ||| ((((((0x46846454d504c2b <<< 60) ||| 0xcba3655809d920a) <<< 120) ||| ((0xf2e8d9560364482 <<< 60) ||| 0xbcba06558319120)) <<< 240) ||| ((((0xa7ae9d64e015348 <<< 60) ||| 0x29e9a71938054d2) <<< 120) ||| ((0xaf268c64e01534 <<< 60) ||| 0x82be1a11938054d))))))) else ((((((((((((0x2a0e8 <<< 60) ||| 0xc0f8c0d16080e0b) <<< 60) ||| 0x2201040102c882c) <<< 180) ||| ((((0x2020100010000e0 <<< 60) ||| 0x808060802080038) <<< 60) ||| 0x1068341a28068)) <<< 300) ||| ((((((0x341a0d068341a0d <<< 60) ||| 0x68341a0d068341) <<< 60) ||| 0xa0d06834500d068) <<< 120) ||| ((0x341a0d068341a82 <<< 60) ||| 0x41034500d068341))) <<< 600) ||| ((((((((0xa0d06834500d068 <<< 60) ||| 0x341a0d068341a0d) <<< 60) ||| 0x68341a0d068341) <<< 120) ||| ((0xa0d06834500d068 <<< 60) ||| 0x341a28068341a0d)) <<< 300) ||| ((((((0x1e8f41a18068341 <<< 60) ||| 0xa0d06834400d068) <<< 60) ||| 0x341a0d068341a0d) <<< 120) ||| ((0x68341a0d068341 <<< 60) ||| 0xa281e8341a28068)))) <<< 1200) ||| ((((((((((0xa01a0d068341a0d <<< 60) ||| 0x100341a10068341) <<< 60) ||| 0xa0d068341a0d068) <<< 120) ||| ((0x341a0d068341a0d <<< 60) ||| 0x6934f40d068341)) <<< 300) ||| ((((((0xa0d068a01a0d068 <<< 60) ||| 0x343028080341a72) <<< 60) ||| 0x269881a0d268341) <<< 120) ||| ((0xa0d350341a0d068 <<< 60) ||| 0x34500d06834c40d))) <<< 600) ||| ((((((((0x68341a0d068341 <<< 60) ||| 0xa0d068341a0d068) <<< 60) ||| 0x341a0d068341a0d) <<< 120) ||| ((0x68341a0d068341 <<< 60) ||| 0xa0d069548a0d068)) <<< 300) ||| ((((((0x341a0d140601a0d <<< 60) ||| 0x140a0500d268348) <<< 60) ||| 0xa3d068c01a0d068) <<< 120) ||| ((0x341a0d068341a0d <<< 60) ||| 0x68c01a28068401)))))))
def g127H6 (j : Nat) : Nat := ((((0xd015f30000 <<< 60) ||| 0x3) <<< 60) ||| 0x4b2000000f10000)
def g127D7 (j : Nat) : Nat := (if j<5 then (if j<2 then (if j<1 then ((((((((((((((((0x95450110 <<< 60) ||| 0xfd9432a8a0221fb) <<< 60) ||| 0x18655140443f610) <<< 120) ||| ((0xcaa280885fc65b8 <<< 60) ||| 0x350110df8c3706a)) <<< 240) ||| ((((0x221fb164e0d404 <<< 60) ||| 0x42fe72cc1a80886) <<< 120) ||| ((0xfce198350110df8 <<< 60) ||| 0xc3306a0221fb264))) <<< 540) ||| ((((((((0x60d40443f62c8c1 <<< 60) ||| 0xa80885fc6636350) <<< 60) ||| 0x110bf9cc2c6a022) <<< 120) ||| ((0x17f19858d40442f <<< 60) ||| 0xe728b1a80887eca)) <<< 240) ||| ((((0x516350110fd8ca2 <<< 60) ||| 0xc6a0221fb26458d) <<< 120) ||| ((0x40443f62c8b1a80 <<< 60) ||| 0x887f460d6350110)))) <<< 1020) ||| ((((((((((0xfd8b22a6a0221fb <<< 60) ||| 0x186d0d40442fe72) <<< 60) ||| 0xca1a80885fc6594) <<< 120) ||| ((0x350110fd9b2286a <<< 60) ||| 0x221fb16450d404)) <<< 240) ||| ((((0x43fa2c6a1a80887 <<< 60) ||| 0xece594350110fd9) <<< 120) ||| ((0x4b286a0221fb196 <<< 60) ||| 0x50d40443f612ca1))) <<< 480) ||| ((((((0xa80887ece194350 <<< 60) ||| 0x110fd943286a022) <<< 120) ||| ((0x1fb18650d40443f <<< 60) ||| 0x610ca1a808847b6)) <<< 240) ||| ((((0x43825da64af3c8a <<< 60) ||| 0xebb92c95e791617) <<< 120) ||| ((0x725933cb04c0ae0 <<< 60) ||| 0x32778609815c064))))) <<< 2040) ||| ((((((((((((0xaf3c92c9b8aa91e <<< 60) ||| 0xd90e0974d8e37f3) <<< 60) ||| 0xba0e8b1c7b6438) <<< 120) ||| ((0x25d94387fcc2ec3 <<< 60) ||| 0xb2878f976600765)) <<< 240) ||| ((((0xed5b243b2c8a1d <<< 60) ||| 0xad6447659143b5c) <<< 120) ||| ((0xc80ecb228765d95 <<< 60) ||| 0x1d96350edb3203b))) <<< 480) ||| ((((((0x2c6a1ce7a625458 <<< 60) ||| 0xd438dfcc2e83a2c) <<< 120) ||| ((0x199d7460c74582d <<< 60) ||| 0x3b263a2c8b05ab6)) <<< 240) ||| ((((0x487459160d5cb23 <<< 60) ||| 0x1a1ac10ff985d8) <<< 120) ||| ((0x76502d5b243b2c8 <<< 60) ||| 0xa05ad6447659140)))) <<< 1020) ||| ((((((((((0xb3cca8ecb02816d <<< 60) ||| 0x9931d960502d732) <<< 60) ||| 0x9b2ac0a053e25d6) <<< 120) ||| ((0x558140b9cca908b <<< 60) ||| 0x28179993211605)) <<< 240) ||| ((((0x2d732d322c0a05 <<< 60) ||| 0xaee4d6458140f55) <<< 120) ||| ((0xc92c8b02816b996 <<< 60) ||| 0x95160502f33272a))) <<< 480) ||| ((((((0x2c0a072e5937358 <<< 60) ||| 0x140b5cca6c6b028) <<< 120) ||| ((0x16b996d0d60502e <<< 60) ||| 0x732ba1ac0a05ae6)) <<< 240) ||| ((((0x594358140f4cb1a <<< 60) ||| 0x86b02819db83e01) <<< 120) ||| ((0x764c33b707c02e8 <<< 60) ||| 0x985b664f6458130)))))) <<< 4080) ||| ((((((((((((((0xe5cba2c8b02616d <<< 60) ||| 0xb9458d604c39b2e) <<< 60) ||| 0x8b1ac0984f62614) <<< 120) ||| ((0x358130b6ccb286b <<< 60) ||| 0x261e996450d604)) <<< 240) ||| ((((0xc37c322c00c8905 <<< 60) ||| 0xea6426450d20bf0) <<< 120) ||| ((0xc8f0ab02417cb93 <<< 60) ||| 0x61560482dd728b2))) <<< 480) ||| ((((((0xac0905bae598458 <<< 60) ||| 0x120b754c6c8b024) <<< 120) ||| ((0x16e993d9160483d <<< 60) ||| 0x5708b22c0905f8e)) <<< 240) ||| ((((0x455458120b75ca2 <<< 60) ||| 0xc6b0241ecb8358d) <<< 120) ||| ((0x60482dd32ca1ac0 <<< 60) ||| 0x907aa5914358120)))) <<< 1020) ||| ((((((((((0xf64b1a86b02417a <<< 60) ||| 0xb94619404835d72) <<< 60) ||| 0xcc3280906eae518) <<< 120) ||| ((0x650120bf1c8b0aa <<< 60) ||| 0x2417aa98991404)) <<< 240) ||| ((((0x82f532732280907 <<< 60) ||| 0xaae196450120bf1) <<< 120) ||| ((0xc8aa8a02417ab96 <<< 60) ||| 0x55140482f572ca1))) <<< 480) ||| ((((((0xa80905ea6594350 <<< 60) ||| 0x120dd5c3286a024) <<< 120) ||| ((0x1ba98650d40483f <<< 60) ||| 0x1706a1a80907e25)) <<< 240) ||| ((((0x8d43501209f3c93 <<< 60) ||| 0xd3a2213f39060f) <<< 120) ||| ((0x644427cf24c34c8 <<< 60) ||| 0x886f86498019110))))) <<< 2040) ||| ((((((((((((0x9f3c9309b1a213f <<< 60) ||| 0x194e0163443762c) <<< 60) ||| 0x8c0686884f9e498) <<< 120) ||| ((0x650d109f9c830ca <<< 60) ||| 0x1a217b190991434)) <<< 240) ||| ((((0x42fa720b1a86885 <<< 60) ||| 0xdce516554110db8) <<< 120) ||| ((0xb2f08a82217e392 <<< 60) ||| 0x591504435e70d43))) <<< 480) ||| ((((((0x280885ec6528650 <<< 60) ||| 0x110bd9ca30ca022) <<< 120) ||| ((0x17e392619404435 <<< 60) ||| 0xe30c43280885dc6)) <<< 240) ||| ((((0x548650110be8c99 <<< 60) ||| 0xca02217e192219) <<< 120) ||| ((0x40442f6329b2a80 <<< 60) ||| 0x885eca626450110)))) <<< 1020) ||| ((((((((((0xbd8cb4c8a02217b <<< 60) ||| 0x19399140442fc72) <<< 60) ||| 0x4b2280887ace196) <<< 120) ||| ((0x450110f58432c8a <<< 60) ||| 0x2217b393591404)) <<< 240) ||| ((((0x43f4724b2280885 <<< 60) ||| 0xec65a5450110bd8) <<< 120) ||| ((0xca6c6a02213f398 <<< 60) ||| 0x58d404427e130b1))) <<< 480) ||| ((((((0xa80885ec65b4350 <<< 60) ||| 0x110bd9cb286a022) <<< 120) ||| ((0x17b19650d40443f <<< 60) ||| 0x2706a1a80887e45)) <<< 240) ||| ((((0x8d4350110bc4c9c <<< 60) ||| 0xa8a024172995d0d) <<< 120) ||| ((0x40482f23272a280 <<< 60) ||| 0x885cc6574350110))))))) else ((((((((((((((((0x905fae6 <<< 60) ||| 0x15458120bf4ca70) <<< 60) ||| 0x6b0241be984e0d6) <<< 120) ||| ((0x483dd2c9c1ac09 <<< 60) ||| 0x6fa6118358120f)) <<< 240) ||| ((((0x74b2306b0241ee9 <<< 60) ||| 0x9458d60483dd308) <<< 120) ||| ((0xb1ac0906fae1153 <<< 60) ||| 0x58120f75b22a6b0))) <<< 540) ||| ((((((((0x241ee96454d6048 <<< 60) ||| 0x2fd730a1ac0905f) <<< 60) ||| 0xa6614358120f74c) <<< 120) ||| ((0xb286b0241fa9845 <<< 60) ||| 0xd60483f9306a1a)) <<< 240) ||| ((((0xc0905fa64f86501 <<< 60) ||| 0x20df4caf0ca0241) <<< 120) ||| ((0xbe993e1940483f5 <<< 60) ||| 0x728c3280905fae4)))) <<< 1020) ||| ((((((((((0xd8650120df5cab0 <<< 60) ||| 0xca0241be9956194) <<< 60) ||| 0x4837d726c32809) <<< 120) ||| ((0x6fa64d8650120b <<< 60) ||| 0xf4cb70aa0241be9)) <<< 240) ||| ((((0x86e1540482fd72c <<< 60) ||| 0xc2a80906fae1985) <<< 120) ||| ((0x50120df4c330aa0 <<< 60) ||| 0x2417eb985954048))) <<< 480) ||| ((((((0x3f530b32280907e <<< 60) ||| 0xae156450120fd4c) <<< 120) ||| ((0x2ac8a0241fab865 <<< 60) ||| 0x5140483f530caa2)) <<< 240) ||| ((((0x80905fa65b83501 <<< 60) ||| 0x20df4c3706a0241) <<< 120) ||| ((0xfa964e0d40482fd <<< 60) ||| 0x72cc1a80906fae1))))) <<< 2040) ||| ((((((((((((0x98350120df4c330 <<< 60) ||| 0x6a0241faa6460d4) <<< 60) ||| 0x483f52c8c1a809) <<< 120) ||| ((0x5fae616350120b <<< 60) ||| 0xf4cc2c6a0241fa9)) <<< 240) ||| ((((0x9458d40483f9306 <<< 60) ||| 0xb1a80906fae1953) <<< 120) ||| ((0x50120df4c32a6a0 <<< 60) ||| 0x241faa6454d4048))) <<< 480) ||| ((((((0x3f52c8a9a80907e <<< 60) ||| 0xae594350120fd4c) <<< 120) ||| ((0xb286a0241fab865 <<< 60) ||| 0xd40483f530ca1a)) <<< 240) ||| ((((0x80904fde59839d1 <<< 60) ||| 0x10df8cb3013a221) <<< 120) ||| ((0xbf193602744427e <<< 60) ||| 0xb27c32e8884fd65)))) <<< 1020) ||| ((((((((((0xb835d110df8cb30 <<< 60) ||| 0x132221bf1936026) <<< 60) ||| 0x4442f6f28b2ac88) <<< 120) ||| ((0x85fce418359110d <<< 60) ||| 0xf2c2f04b2221be5)) <<< 240) ||| ((((0x83e09644437cb2b <<< 60) ||| 0xc12c8886f959782) <<< 120) ||| ((0x59110df2c9f04b2 <<< 60) ||| 0x2217d7935d96344))) <<< 480) ||| ((((((0x2deb2d422c6885f <<< 60) ||| 0xc6428458d10b7bc) <<< 120) ||| ((0xb308b1a217e7926 <<< 60) ||| 0x1163442fe720c22)) <<< 240) ||| ((((0xc6884fd6627458d <<< 60) ||| 0x10beac9ce8b1a21) <<< 120) ||| ((0x7f1909d163442fa <<< 60) ||| 0xb27322c6885fc64)))))) <<< 4080) ||| ((((((((((((((0x26458d10bf3c92c <<< 60) ||| 0x8b1a217f194e016) <<< 60) ||| 0x34437e509c02c68) <<< 120) ||| ((0x86fc6138058d10d <<< 60) ||| 0xf8cbf00b1a21bf1)) <<< 240) ||| ((((0x76e01634437e529 <<< 60) ||| 0xc02c6886fc65380) <<< 120) ||| ((0x58d10df93a700b1 <<< 60) ||| 0xa21bf174e016344))) <<< 480) ||| ((((((0x37e4c9c02c6886f <<< 60) ||| 0xc5938058d10bf3c) <<< 120) ||| ((0x92c8a9a21bf1966 <<< 60) ||| 0x3434435ef0d432)) <<< 240) ||| ((((0x86885ed6528650d <<< 60) ||| 0x10bf3c930ca1a21) <<< 120) ||| ((0x7f390619434435e <<< 60) ||| 0xf2cc3286886f9e4)))) <<< 1020) ||| ((((((((((0x98650d10df9c830 <<< 60) ||| 0xca1a213f6982194) <<< 60) ||| 0x34435eb0c432868) <<< 120) ||| ((0x85f96488650d10b <<< 60) ||| 0xf8c810ca1a213f5)) <<< 240) ||| ((((0x98d91434435ef0d <<< 60) ||| 0xb2286885f564f64) <<< 120) ||| ((0x50d10bdacb4c8a1 <<< 60) ||| 0xa21af7865914344))) <<< 480) ||| ((((((0x2fcf24b2286887a <<< 60) ||| 0xde196450d10f5a4) <<< 120) ||| ((0x32c8a1a21fa7925 <<< 60) ||| 0x9143443daf0cb1a)) <<< 240) ||| ((((0x86887b52196350d <<< 60) ||| 0x10fcb322c6a1a21) <<< 120) ||| ((0xf956458d43443fa <<< 60) ||| 0x720b1a86885fc64))))) <<< 2040) ||| ((((((((((((0xf6454110fb8caac <<< 60) ||| 0x8a8221f71655915) <<< 60) ||| 0x442fe726b22a08) <<< 120) ||| ((0x87f8e496454110b <<< 60) ||| 0xf8ca6c6a82217f3)) <<< 240) ||| ((((0x9458d50443ee6c8 <<< 60) ||| 0xa9aa0887dc59153) <<< 120) ||| ((0x54110bf9cb286a8 <<< 60) ||| 0x2217f19650d5044))) <<< 480) ||| ((((((0x3f62c8a1aa0887f <<< 60) ||| 0x458d4354110bf8c) <<< 120) ||| ((0x9f0ca02217f193a <<< 60) ||| 0x1940442fe728c32)) <<< 240) ||| ((((0x80887ece5186501 <<< 60) ||| 0x10bf9c9b0ca0221) <<< 120) ||| ((0xfe39261940442fe <<< 60) ||| 0x32643280885fc65)))) <<< 1020) ||| ((((((((((0xb8550110df94370 <<< 60) ||| 0xaa0221bf186e154) <<< 60) ||| 0x442fe72cc2a808) <<< 120) ||| ((0x86fce198550110d <<< 60) ||| 0xf94330aa0221bf1)) <<< 240) ||| ((((0x86615404437e10c <<< 60) ||| 0xc2a80885fc66365) <<< 120) ||| ((0x50110bf9cc2caa0 <<< 60) ||| 0x2217f198d914044))) <<< 480) ||| ((((((0x2fe327b2280887e <<< 60) ||| 0xc61a6450110fd9c) <<< 120) ||| ((0x32c8a0221fb1955 <<< 60) ||| 0x9140443f670ab22)) <<< 240) ||| ((((0x80887ec61564501 <<< 60) ||| 0x10fd8b2ac8a0221) <<< 120) ||| ((0xfb19359140443f6 <<< 60) ||| 0x30d2a280887ece1)))))))) else (if j<3 then ((((((((((((((((0xdb0fc12c <<< 60) ||| 0x89876b5d3825913) <<< 60) ||| 0xde6c1f04b22619) <<< 120) ||| ((0xed97e09644c33da <<< 60) ||| 0xedc12c89867b5d7)) <<< 240) ||| ((((0x8259130cf6ba704 <<< 60) ||| 0xb2261bcd93e0964) <<< 120) ||| ((0x4c33baeac18c898 <<< 60) ||| 0x67b5d58219130cf))) <<< 540) ||| ((((((((0xabab02322619f97 <<< 60) ||| 0x5600644c2dbb2d4) <<< 60) ||| 0x22c6985f6642845) <<< 120) ||| ((0x8d30b6fcb308b1a <<< 60) ||| 0x617cf92611634c2)) <<< 240) ||| ((((0xfb720c22c698677 <<< 60) ||| 0x2617458d30e6fcb) <<< 120) ||| ((0x2e8b1a61cdc965d <<< 60) ||| 0x1634c3bb720ba2c)))) <<< 1020) ||| ((((((((((0x69857765e6458d3 <<< 60) ||| 0xeceba4c8b1a61d) <<< 60) ||| 0x9d74591634c2f9f) <<< 120) ||| ((0x24b22c6986f6613 <<< 60) ||| 0x8058d30becc86c8)) <<< 240) ||| ((((0xa9a617cf9259153 <<< 60) ||| 0x4c2bbb2e322a698) <<< 120) ||| ((0x5f36486454d30be <<< 60) ||| 0xac88c8a9a617d99))) <<< 480) ||| ((((((0x191534c35bf0d4 <<< 60) ||| 0x3286985e7652865) <<< 120) ||| ((0xd30becc850ca1a <<< 60) ||| 0x617cf92619434c2)) <<< 240) ||| ((((0xfb720c3286986b7 <<< 60) ||| 0xe598650d30de7c9) <<< 120) ||| ((0x30ca1a61bdb9061 <<< 60) ||| 0x9434c27bd304328))))) <<< 2040) ||| ((((((((((((0x6986b76188650d3 <<< 60) ||| 0xbe6c910ca1a617) <<< 60) ||| 0xd591219434c2fb3) <<< 120) ||| ((0x204328698776e41 <<< 60) ||| 0x7650d309eecc6c8)) <<< 240) ||| ((((0xa1a615dd97d9143 <<< 60) ||| 0x4c35bf0db228698) <<< 120) ||| ((0x5f66436450d30bc <<< 60) ||| 0xecb4c8a1a61d9d7))) <<< 480) ||| ((((((0x6991434c35bf0cb <<< 60) ||| 0x2286985f3e49645) <<< 120) ||| ((0xd30f4fc32c8a1a <<< 60) ||| 0x61e9c86591434c3)) <<< 240) ||| ((((0xb3aecb2286987e3 <<< 60) ||| 0xe496450d30beccb) <<< 120) ||| ((0x700a1a61bd986e0 <<< 60) ||| 0x1434c3f32c9c028)))) <<< 1020) ||| ((((((((((0x6985be65a845813 <<< 60) ||| 0xbecc9d08b02616) <<< 60) ||| 0xfb96611604c2fb7) <<< 120) ||| ((0x26c22c0985fae49 <<< 60) ||| 0x8458130cfc4c2e8)) <<< 240) ||| ((((0xb0261cfb965d160 <<< 60) ||| 0x4c39f12cba2c098) <<< 120) ||| ((0x776e4d7458130e7 <<< 60) ||| 0xcba6c8b02615f99))) <<< 480) ||| ((((((0x7991604c2df32d3 <<< 60) ||| 0x22c09876e5d2645) <<< 120) ||| ((0x8130becc9cc8b02 <<< 60) ||| 0x61db974591604c2)) <<< 240) ||| ((((0xfd724b22c09873e <<< 60) ||| 0x5d16458130f6cc9) <<< 120) ||| ((0xac8b0261eeb9259 <<< 60) ||| 0x1604c2fb329c1ac)))))) <<< 4080) ||| ((((((((((((((0x987b6593835813 <<< 60) ||| 0xeecba2c6b0261e) <<< 60) ||| 0xda6458d604c3db2) <<< 120) ||| ((0xc8b1ac0987b6a51 <<< 60) ||| 0x6358130f6cca2c6)) <<< 240) ||| ((((0xb0261eda8458d60 <<< 60) ||| 0x4c3db308b1ac098) <<< 120) ||| ((0x7b6d915358130f6 <<< 60) ||| 0xcb22a6b02617db9))) <<< 480) ||| ((((((0x650d604c3db52ca <<< 60) ||| 0x1ac0985f6659435) <<< 120) ||| ((0x8130f6ccb286b02 <<< 60) ||| 0x61f9a8450d604c3)) <<< 240) ||| ((((0xf3308a1ac0987b6 <<< 60) ||| 0xd914358130fcd32) <<< 120) ||| ((0x286b0261ed96450 <<< 60) ||| 0xd604c3f32c8a1ac)))) <<< 1020) ||| ((((((((((0x985f664f645413 <<< 60) ||| 0xbecc9cc8a82617) <<< 60) ||| 0xeb92591504c2bf3) <<< 120) ||| ((0x2e322a0985f664c <<< 60) ||| 0x6454130bf4c90c8)) <<< 240) ||| ((((0xa82617f19119150 <<< 60) ||| 0x4c2fb728b1aa098) <<< 120) ||| ((0x7d6d915354130fa <<< 60) ||| 0xd322a6a8261f596))) <<< 480) ||| ((((((0x454d504c3eb0c8a <<< 60) ||| 0x9aa0985f6e59435) <<< 120) ||| ((0x4130beccb286a82 <<< 60) ||| 0x61f9a6450d504c3)) <<< 240) ||| ((((0xf32c8a1aa0986fa <<< 60) ||| 0x655809d920df4ca) <<< 120) ||| ((0xb013a241be99360 <<< 60) ||| 0x2744837d32ac06c))))) <<< 2040) ||| ((((((((((((0x8906fa655809912 <<< 60) ||| 0xdf4c9b0132241b) <<< 60) ||| 0xcd9560c644837d3) <<< 120) ||| ((0x2ac00c8905bbe59 <<< 60) ||| 0x8458d20bf4c84ec)) <<< 240) ||| ((((0xa9a417eb905d953 <<< 60) ||| 0x482fd3213a2a690) <<< 120) ||| ((0x5fa6436454d20bf <<< 60) ||| 0x4c84c8a9a415ef9))) <<< 480) ||| ((((((0x759153482bdb2e3 <<< 60) ||| 0x22a6905f364c645) <<< 120) ||| ((0x4d20bf2c88c8a9a <<< 60) ||| 0x417e99019153483)) <<< 240) ||| ((((0x7d4edc02a6906fa <<< 60) ||| 0x5db8054d20df53a) <<< 120) ||| ((0x700a9a41be974e0 <<< 60) ||| 0x1534837d6c9c02a)))) <<< 1020) ||| ((((((((((0x6906fa9938054d2 <<< 60) ||| 0xdf4b2700a9a41b) <<< 60) ||| 0xe864e01534833d9) <<< 120) ||| ((0x2ec3286906bbe59 <<< 60) ||| 0x8650d20f57c32c8)) <<< 240) ||| ((((0xa1a41ecf8658d43 <<< 60) ||| 0x482fd329c2ac090) <<< 120) ||| ((0x5fae518558120df <<< 60) ||| 0x4c2f08b0241ee96))) <<< 480) ||| ((((((0x5e11604837d32bc <<< 60) ||| 0x22c0907bae59845) <<< 120) ||| ((0x8120df5c2b08b02 <<< 60) ||| 0x41be98561160483)) <<< 240) ||| ((((0xdd2cac22c0905fa <<< 60) ||| 0xe4d8458120f74c2) <<< 120) ||| ((0xec8b0241eeb8559 <<< 60) ||| 0x160483dd30ab22c))))))) else (if j<4 then ((((((((((((((((0x1163502f <<< 60) ||| 0x3b27322c6a057be) <<< 60) ||| 0x497654d40d9ebb3) <<< 120) ||| ((0xba1a813fb90619 <<< 60) ||| 0x43502bbf26bb286)) <<< 240) ||| ((((0xa06afe1b6450d40 <<< 60) ||| 0xe5fbb6c8a1a81ab) <<< 120) ||| ((0xf865914350397ee <<< 60) ||| 0xcb2286a05ebe496))) <<< 540) ||| ((((((((0x450d40aeecb6e6a <<< 60) ||| 0x1a81d9d64dcd435) <<< 60) ||| 0x27f32dc0286a06) <<< 120) ||| ((0xee5938050d40dec <<< 60) ||| 0xb1f00a1a813bd98)) <<< 240) ||| ((((0xa1943502b7b2f43 <<< 60) ||| 0x286a06afe1a8650) <<< 120) ||| ((0xd40bcec9d0ca1a8 <<< 60) ||| 0x17b990a1943502f)))) <<< 1020) ||| ((((((((((0x5f24c3286a05eee <<< 60) ||| 0x418650d40d5fcb3) <<< 60) ||| 0xca1a81baf92619) <<< 120) ||| ((0x4350377720c3286 <<< 60) ||| 0xa04efa608650d40)) <<< 240) ||| ((((0xadf4b90ca1a81ab <<< 60) ||| 0xd8621943502f5b2) <<< 120) ||| ((0x443286a05ed6448 <<< 60) ||| 0x650d40bdcc810ca))) <<< 480) ||| ((((((0x1a813bd989d9435 <<< 60) ||| 0x2b7b2f3b286a07) <<< 120) ||| ((0x2fdda7650d40bce <<< 60) ||| 0xc9ceca1a817b990)) <<< 240) ||| ((((0x9d943502f3f26bb <<< 60) ||| 0x286a05ebe497650) <<< 120) ||| ((0xd40e5fcb2eca1a8 <<< 60) ||| 0x1d9f935d943503b))))) <<< 2040) ||| ((((((((((((0x5f24bb286a04efa <<< 60) ||| 0x607650d40adf4b8) <<< 60) ||| 0xeca1a8179d931d9) <<< 120) ||| ((0x43502f5b243b286 <<< 60) ||| 0xa05ed6447650d40)) <<< 240) ||| ((((0xbcecb6e6a1a81d9 <<< 60) ||| 0xd76dcd43503d3f0) <<< 120) ||| ((0xcb1a86a07a72196 <<< 60) ||| 0x350d40ecfbb2c6a))) <<< 480) ||| ((((((0x1a81d9d7658d435 <<< 60) ||| 0x2f732dc0286a06) <<< 120) ||| ((0xee61b8050d40fcd <<< 60) ||| 0xb9f00a1a81f9963)) <<< 240) ||| ((((0xe0143502fe32243 <<< 60) ||| 0xac0a05be64f7658) <<< 120) ||| ((0x140b7d4c0ecb028 <<< 60) ||| 0x16f9931d960502f)))) <<< 1020) ||| ((((((((((0xe323c2ac0a05eee <<< 60) ||| 0x518558140bedc9b) <<< 60) ||| 0xab02816fb965d5) <<< 120) ||| ((0x60502fe722baac0 <<< 60) ||| 0xa05bee516558140)) <<< 240) ||| ((((0xf5dbb708b0281eb <<< 60) ||| 0x965e1160502f752) <<< 120) ||| ((0xe422c0a07ae5948 <<< 60) ||| 0x458140b7cc9ec8b))) <<< 480) ||| ((((((0x281eb965991605 <<< 60) ||| 0x2f7327322c0a07) <<< 120) ||| ((0xaee116458140f5d <<< 60) ||| 0xbb2c8b0281eb965)) <<< 240) ||| ((((0x59160503d710eb2 <<< 60) ||| 0x2c0a07ae6556458) <<< 120) ||| ((0x140f5dc2ac8b028 <<< 60) ||| 0x1eb98559160503d)))))) <<< 4080) ||| ((((((((((((((0x76eab22c0a07ae5 <<< 60) ||| 0xd56458140f5cc9a) <<< 60) ||| 0xc8b0281ebb64551) <<< 120) ||| ((0x60503d72c8aa2c0 <<< 60) ||| 0xa05fce455458140)) <<< 240) ||| ((((0xbddcb2a8b0281eb <<< 60) ||| 0xb7655160503d70e) <<< 120) ||| ((0xcaa2c0a07ae5938 <<< 60) ||| 0x358140f5cb2306b))) <<< 480) ||| ((((((0x281eb964dcd605 <<< 60) ||| 0x39f6c9b9ac0a07) <<< 120) ||| ((0x6e9937358140e7c <<< 60) ||| 0xb26e6b0281db964)) <<< 240) ||| ((((0xdcd60502df72cb9 <<< 60) ||| 0xac0a073edd97358) <<< 120) ||| ((0x140e7c3b2e6b028 <<< 60) ||| 0x1eb9645cd60503d)))) <<< 1020) ||| ((((((((((0x74c8b1ac0a07ae5 <<< 60) ||| 0x916358140b7dca2) <<< 60) ||| 0xc6b0281eba9458d) <<< 120) ||| ((0x60503d7328b1ac0 <<< 60) ||| 0xa07b6e0d6358140)) <<< 240) ||| ((((0xf6cb9ac6b0281eb <<< 60) ||| 0x96454d60502df32) <<< 120) ||| ((0xca1ac0a07aed914 <<< 60) ||| 0x358140f5cb2286b))) <<< 480) ||| ((((((0x281ddb7350d605 <<< 60) ||| 0x3db2c6a1ac0a05) <<< 120) ||| ((0xeee594358140f5d <<< 60) ||| 0x4b286b02817b996)) <<< 240) ||| ((((0x50d60503d732ca1 <<< 60) ||| 0xac0a07aedd94358) <<< 120) ||| ((0x140f5c3b286b028 <<< 60) ||| 0x1f998350d60503f))))) <<< 2040) ||| ((((((((((((0x36e6a1ac0a07e65 <<< 60) ||| 0x8d4358140a7ecb5) <<< 60) ||| 0x8bb2615dd93a11) <<< 120) ||| ((0x764c2bf321422ec <<< 60) ||| 0x9853fe59845d930)) <<< 240) ||| ((((0xaefc9b08bb2615e <<< 60) ||| 0xf92611764c2bf72) <<< 120) ||| ((0xc22ec985776538 <<< 60) ||| 0x35d930c7fc350cb))) <<< 480) ||| ((((((0xa2615bd94a19744 <<< 60) ||| 0xc2bbb27432e8985) <<< 120) ||| ((0x7e642865d130aef <<< 60) ||| 0xc9b0cba2615ef92)) <<< 240) ||| ((((0x619744c2bf720c3 <<< 60) ||| 0x2e89863f618865d) <<< 120) ||| ((0x130af6c910cba26 <<< 60) ||| 0x15f591219744c2b)))) <<< 1020) ||| ((((((((((0xbb2dc1ae89857e6 <<< 60) ||| 0x5b805d130eedc1f) <<< 60) ||| 0xba2614ff965d3) <<< 120) ||| ((0x644c33bae8c1ec8 <<< 60) ||| 0x9867e5d180d9130)) <<< 240) ||| ((((0x9f7c930d322611f <<< 60) ||| 0xd985da644c337b0) <<< 120) ||| ((0xcba4c8986775d98 <<< 60) ||| 0x3991308ffcb30eb))) <<< 480) ||| ((((((0x22618ff9661d644 <<< 60) ||| 0xc33bf26c3ac8986) <<< 120) ||| ((0x7be498759130cfd <<< 60) ||| 0xc830eb22614ff96)) <<< 240) ||| ((((0x5d1644c397f2cba <<< 60) ||| 0x2c89872f2597459) <<< 120) ||| ((0x130ecfc9ae8b226 <<< 60) ||| 0x1dbb905d1644c33))))))) else ((((((((((((((((0xc11fd94a <<< 60) ||| 0x1d435825ff2cc3a) <<< 60) ||| 0x86b04fe6438650d) <<< 120) ||| ((0x60b5eca50ca1ac1 <<< 60) ||| 0x3fb90619435835d)) <<< 240) ||| ((((0xf24c3286b06bee4 <<< 60) ||| 0x18650d60aeec9ee) <<< 120) ||| ((0x8a1ac16bd969d14 <<< 60) ||| 0x3582d7f2cba286b))) <<< 540) ||| ((((((((0x4bf6636450d60b <<< 60) ||| 0x6ec9ec8a1ac16bd) <<< 60) ||| 0x9699143582f7321) <<< 120) ||| ((0x32286b07abe4964 <<< 60) ||| 0x50d60ecf3a2e6a1)) <<< 240) ||| ((((0xac1d9d745cd4358 <<< 60) ||| 0x3d3ac8b9a86b07a) <<< 120) ||| ((0x79916350d60f4eb <<< 60) ||| 0x22c6a1ac17db905)))) <<< 1020) ||| ((((((((((0x8d43583d3ce8b1a <<< 60) ||| 0x86b07a75d16350d) <<< 60) ||| 0x60f6dc82c6a1ac1) <<< 120) ||| ((0xafa86601435835f <<< 60) ||| 0x30cc0286b07ae59)) <<< 240) ||| ((((0x18050d60f6cb1b0 <<< 60) ||| 0xa1ac14fd96dd36) <<< 120) ||| ((0x45427df24c34c8a <<< 60) ||| 0x856f6537699150a))) <<< 480) ||| ((((((0xdfca2ed322a15df <<< 60) ||| 0x935da64542e7f28) <<< 120) ||| ((0xb2cc8a8577e4d87 <<< 60) ||| 0x59150adeca6ecb2)) <<< 240) ||| ((((0x2a15bf945d96454 <<< 60) ||| 0x2bbf26bb2c8a85c) <<< 120) ||| ((0xfe516559150a7ec <<< 60) ||| 0xb6e8b22a19ee87e))))) <<< 2040) ||| ((((((((((((0x9645433db0fc12 <<< 60) ||| 0xc8a86db61782591) <<< 60) ||| 0x50cf74bf04b22a1) <<< 120) ||| ((0x9ed97e09645433d <<< 60) ||| 0xeedc12c8a867b5d)) <<< 240) ||| ((((0xb8259150db6caf0 <<< 60) ||| 0x4b22a1b6d65e096) <<< 120) ||| ((0x45433dee9c12c8a <<< 60) ||| 0x8677a5d8319150c))) <<< 480) ||| ((((((0xeecbb06322a1b5d <<< 60) ||| 0x9560c645437b320) <<< 120) ||| ((0xc18c8a84fee4d80 <<< 60) ||| 0x19150df4c930032)) <<< 240) ||| ((((0x2a176f925915454 <<< 60) ||| 0x2bbb27326e6a857) <<< 120) ||| ((0x7e4d64dcd50af7c <<< 60) ||| 0x92c9b9aa15dd931)))) <<< 1020) ||| ((((((((((0x9373542bdb24326 <<< 60) ||| 0xe6a857d64464dcd) <<< 60) ||| 0x50afcc80c9b9aa1) <<< 120) ||| ((0x3ef92613635433b <<< 60) ||| 0xb09b9ec6a85dbe4)) <<< 240) ||| ((((0x96454d50baec98c <<< 60) ||| 0x8a9aa176d921915) <<< 120) ||| ((0x3542eeb22322a6a <<< 60) ||| 0x85de6406454d509))) <<< 480) ||| ((((((0xf7c930ca1aa1d9e <<< 60) ||| 0x64dcd43543b3ac9) <<< 120) ||| ((0xb9a86a857be4976 <<< 60) ||| 0x54f40afbc8b0bbb)) <<< 240) ||| ((((0x281baf84e097650 <<< 60) ||| 0x2b7f28c2aeca057) <<< 120) ||| ((0x7e4d855d940afbc <<< 60) ||| 0x8b0abb2815fb906)))))) <<< 4080) ||| ((((((((((((((0x157650397f0dc22 <<< 60) ||| 0xeca057ee41835d9) <<< 60) ||| 0x40e77c3704bb281) <<< 120) ||| ((0x9ef85e09765033d <<< 60) ||| 0xb0bc12eca076be1)) <<< 240) ||| ((((0x3825d940cf7c1f0 <<< 60) ||| 0x4bb2819ed83e097) <<< 120) ||| ((0x65023fb27438eca <<< 60) ||| 0x63fe61761d940d))) <<< 480) ||| ((((((0xceca3063b2811fd <<< 60) ||| 0x989db75502bdf24) <<< 120) ||| ((0xbb6eaa063fe1a76 <<< 60) ||| 0x5d540c7fc32ecba)) <<< 240) ||| ((((0xa815ef925d97550 <<< 60) ||| 0x23fd303b2eaa057) <<< 120) ||| ((0x764c765d540af6c <<< 60) ||| 0x90ecbaa819f776e)))) <<< 1020) ||| ((((((((((0x5755033ecedc0a <<< 60) ||| 0xeaa067d5db815d5) <<< 60) ||| 0x40cfa3b702baa81) <<< 120) ||| ((0x3f990e11655023f <<< 60) ||| 0xf26c3ec8a047f66)) <<< 240) ||| ((((0x375d9140a7fcb2e <<< 60) ||| 0xbb22813bf985d66) <<< 120) ||| ((0x45029ff2cbaac8a <<< 60) ||| 0x67bdd78259140c))) <<< 480) ||| ((((((0xf6baf04b22817b7 <<< 60) ||| 0x9161564502f7720) <<< 120) ||| ((0xc2ac8a05afe5975 <<< 60) ||| 0x59140e5e3b2eab2)) <<< 240) ||| ((((0x2817b7915d56450 <<< 60) ||| 0x2f7720c1ac8a07a) <<< 120) ||| ((0xbddb8259140dd6c <<< 60) ||| 0x2f04b2281bad83e))))) <<< 2040) ||| ((((((((((((0x96450277f30bb4 <<< 60) ||| 0xa8a06e75d983951) <<< 60) ||| 0x40bd7c92c8aa281) <<< 120) ||| ((0x9f776e05545033e <<< 60) ||| 0xaedc0aa8a06ed59)) <<< 240) ||| ((((0x38155140bdcc84e <<< 60) ||| 0xcaa2817af925d95) <<< 120) ||| ((0x450397aec3b2a8a <<< 60) ||| 0x5e764c7655140b))) <<< 480) ||| ((((((0xd6c90ecaa2811fd <<< 60) ||| 0x989db73502b7b29) <<< 120) ||| ((0x3b6e6a057be4976 <<< 60) ||| 0xdcd40adeca50db9)) <<< 240) ||| ((((0xa815f990a1b7350 <<< 60) ||| 0x23fb31b26e6a057) <<< 120) ||| ((0xe64364dcd40adec <<< 60) ||| 0xb4c9b9a815ef925)))) <<< 1020) ||| ((((((((((0x9373503b5f24b26 <<< 60) ||| 0xe6a063fe1a765cd) <<< 60) ||| 0x40adeca4ecb9a81) <<< 120) ||| ((0x8ff865d973502bd <<< 60) ||| 0xf24bb2e6a047fa6)) <<< 240) ||| ((((0x765cd40af6c90e <<< 60) ||| 0xcb9a815f5911d97) <<< 120) ||| ((0x350357f0cb22e6a <<< 60) ||| 0x72fdd9645cd409))) <<< 480) ||| ((((((0xdeca70eb1a811fd <<< 60) ||| 0x94e1d635029fb2d) <<< 120) ||| ((0x43ac6a047f65a87 <<< 60) ||| 0x58d40a7fcb30eb1)) <<< 240) ||| ((((0xa815dd93dd96350 <<< 60) ||| 0x2bbf26bb2c6a04f) <<< 120) ||| ((0xe6438458d40b5ec <<< 60) ||| 0xb508b1a816bf966)))))))))) else (if j<7 then (if j<6 then ((((((((((((((((0xc86edb22 <<< 60) ||| 0x871fd98dd76450e) <<< 60) ||| 0x9ff2cbaec8a1cf7) <<< 120) ||| ((0xe4183d91439dfcc <<< 60) ||| 0x2eb3228779f9359)) <<< 240) ||| ((((0x66450e9fb21bb2c <<< 60) ||| 0x8a1d3fe59755914) <<< 120) ||| ((0x3cf7baf04b22879 <<< 60) ||| 0xed75e096450e7db))) <<< 540) ||| ((((((((0x21c12c8a1daf643 <<< 60) ||| 0x7659143b5ec80ec) <<< 60) ||| 0xb228779f9361564) <<< 120) ||| ((0x50ef6f22c2ac8a1 <<< 60) ||| 0xdafe597559143e5)) <<< 240) ||| ((((0xe3b2eab22877b79 <<< 60) ||| 0x15d56450ef3f26b) <<< 120) ||| ((0x2ac8a1fabddb825 <<< 60) ||| 0x9143dd6c2f04b22)))) <<< 1020) ||| ((((((((((0x877ad90e096450e <<< 60) ||| 0xf3f26c02c8a1eeb) <<< 60) ||| 0xe0980591439dfcc) <<< 120) ||| ((0x2ed2a2877af9259 <<< 60) ||| 0x15450f3eeedc0aa)) <<< 240) ||| ((((0x8a1e7d5db815514 <<< 60) ||| 0x3ddab2702aa2877) <<< 120) ||| ((0x9d939d95450ef5f <<< 60) ||| 0x24bb2a8a1f2f5d8))) <<< 480) ||| ((((((0x7655143bd6c90ec <<< 60) ||| 0xaa2877b9901d954) <<< 120) ||| ((0x50edbb21bb2c6a1 <<< 60) ||| 0xdb7a607658d43b6)) <<< 240) ||| ((((0xec80ecb1a8779f9 <<< 60) ||| 0x46156350e7bd31b) <<< 120) ||| ((0xaac6a1db7e59755 <<< 60) ||| 0x8d43bebc8aeab1a))))) <<< 2040) ||| ((((((((((((0x87e9f76e116350f <<< 60) ||| 0xd3acbc22c6a1de7) <<< 60) ||| 0xa5c8458d43f4eb2) <<< 120) ||| ((0x908b1a87e9d6599 <<< 60) ||| 0x16350ef3b21322c)) <<< 240) ||| ((((0x6a1fa7dd96458d4 <<< 60) ||| 0x3f4eb2ac8b1a877) <<< 120) ||| ((0xd7915516350ef3f <<< 60) ||| 0x2caa2c6a1fa7dd9))) <<< 480) ||| ((((((0x5458d43f4e3b2a8 <<< 60) ||| 0xb1a87b9e64e0163) <<< 120) ||| ((0x50f73ac9c02c6a1 <<< 60) ||| 0xc7f66276dc143ad)) <<< 240) ||| ((((0xeca4edb82875ef9 <<< 60) ||| 0x25db7050eb7b294) <<< 120) ||| ((0x36e0a1d7764e86d <<< 60) ||| 0xc143af7c930db82)))) <<< 1020) ||| ((((((((((0x879ef9261b7050e <<< 60) ||| 0x3fb31b26e0a1d77) <<< 60) ||| 0x64f64dc143adecb) <<< 120) ||| ((0x4c9b82875ef9259 <<< 60) ||| 0x37050fb5f24b26e)) <<< 240) ||| ((((0xa1f6799163dc14 <<< 60) ||| 0x3eceb22c7b82878) <<< 120) ||| ((0xff869d97050eb7b <<< 60) ||| 0x293b2e0a1e3fe19))) <<< 480) ||| ((((((0x765c143af7c92ec <<< 60) ||| 0xb82871fe981d970) <<< 120) ||| ((0x50ebdb243b2e0a1 <<< 60) ||| 0xd7d644765c143d5)) <<< 240) ||| ((((0xfc32c8b8287cbf7 <<< 60) ||| 0x65917050f978ecb) <<< 120) ||| ((0x22e0a1eb7e19635 <<< 60) ||| 0xc143e6fbb2c6b82)))))) <<< 4080) ||| ((((((((((((((0x87cdc7658d7050e <<< 60) ||| 0x9ff2ec22c7b057b) <<< 60) ||| 0xe497454f60c7fcb) <<< 120) ||| ((0xb0ca1ec15df935d <<< 60) ||| 0x774582bbf26c2ee)) <<< 240) ||| ((((0x8b047f663759d16 <<< 60) ||| 0xadfca2eb3a2c15) <<< 120) ||| ((0xdf935d6745825fb <<< 60) ||| 0x27c32e8b057d647))) <<< 480) ||| ((((((0x755d160aefc9aea <<< 60) ||| 0xba2c12fe98d9574) <<< 120) ||| ((0x5835df0dc12e8b0 <<< 60) ||| 0x67bdd7825d160cf)) <<< 240) ||| ((((0x6baf04ba2c1aed6 <<< 60) ||| 0x5e09745823ff30b) <<< 120) ||| ((0xa8e8b0577e4d751 <<< 60) ||| 0xd16097fcc2ca3a2)))) <<< 1020) ||| ((((((((((0xc19bf985d074583 <<< 60) ||| 0x97acaba0e8b0677) <<< 60) ||| 0x5d5831d160d6eb2) <<< 120) ||| ((0xb063a2c19ed7560 <<< 60) ||| 0x8745835dacac10e)) <<< 240) ||| ((((0x8b067d5d5811d16 <<< 60) ||| 0xd7ab2b023a2c12) <<< 120) ||| ((0xff985d764582dbf <<< 60) ||| 0x26baec8b047f663))) <<< 480) ||| ((((((0x7599160b5fca2cb <<< 60) ||| 0x322c1af96560264) <<< 120) ||| ((0x5827f726c04c8b0 <<< 60) ||| 0x67bdd78259160d7)) <<< 240) ||| ((((0x6b2f04b22c16bf9 <<< 60) ||| 0x461564582def22c) <<< 120) ||| ((0x2ac8b05bee41855 <<< 60) ||| 0x9160b7ac8eeab22))))) <<< 2040) ||| ((((((((((((0xc16bf945d564582 <<< 60) ||| 0xdbf26baac8b05be) <<< 60) ||| 0xe417559160e5eba) <<< 120) ||| ((0x8e8b22c16fb9060 <<< 60) ||| 0xd645835db0bc12c)) <<< 240) ||| ((((0x8b07abdd3825916 <<< 60) ||| 0xd76c1f04b22c13) <<< 120) ||| ((0xf990e19545833ee <<< 60) ||| 0xe9c0aa8b06bdd93))) <<< 480) ||| ((((((0x8155160d7ab2702 <<< 60) ||| 0xaa2c11fd989d373) <<< 120) ||| ((0x582bdf24ba6e6b0 <<< 60) ||| 0x57be4984dcd60cf)) <<< 240) ||| ((((0x7c9309b9ac11fd9 <<< 60) ||| 0x899373582bdf24b) <<< 120) ||| ((0x26e6b057be49745 <<< 60) ||| 0xcd6097fcc2e9b1a)))) <<< 1020) ||| ((((((((((0xc16ef9259163582 <<< 60) ||| 0xbbb29b9ac6b04fe) <<< 60) ||| 0x6538058d60d7cb2) <<< 120) ||| ((0x700b1ac14fd97a1 <<< 60) ||| 0x163582dbb27422c)) <<< 240) ||| ((((0x6b05be6428458d6 <<< 60) ||| 0xb77c9308b1ac16) <<< 120) ||| ((0xfb90611635825fb <<< 60) ||| 0x313a2c6b05b764e))) <<< 480) ||| ((((((0x7458d60b7cc84e8 <<< 60) ||| 0xb1ac16df935d163) <<< 120) ||| ((0x582ddf24ba2c6b0 <<< 60) ||| 0x5b76537358d60b7)) <<< 240) ||| ((((0xcca700b1ac1af98 <<< 60) ||| 0x4e01635825fb2dc) <<< 120) ||| ((0x3a86b047f65b875 <<< 60) ||| 0xd60adeca50ea1a))))))) else ((((((((((((((((0x5cd64d5f <<< 60) ||| 0xc3708b9ac9daf94) <<< 60) ||| 0x5d772592bdf26ba) <<< 120) ||| ((0xee4b2779e4575dc <<< 60) ||| 0x964af7c82ebb92c)) <<< 240) ||| ((((0x99ef985cf725939 <<< 60) ||| 0xdf2cb9ee4b257be) <<< 120) ||| ((0x5573dc964ed7ca2 <<< 60) ||| 0xe7b92c95ef905cf))) <<< 540) ||| ((((((((0x725935df2cc06e4 <<< 60) ||| 0xb267b5d580dc964) <<< 60) ||| 0xdd7ca301b92c99e) <<< 120) ||| ((0xd7360372592bdf2 <<< 60) ||| 0x6c2ee4b2779e458)) <<< 240) ||| ((((0x5dc964af7c830bb <<< 60) ||| 0x92c95ef93597725) <<< 120) ||| ((0x92bdf20b2ee4b25 <<< 60) ||| 0x7be5583dc964cf6)))) <<< 1020) ||| ((((((((((0xc2b07b92c95ef90 <<< 60) ||| 0x60f72592bdf2ac0) <<< 60) ||| 0x6e4b267b61580dc) <<< 120) ||| ((0x964af7c9b01b92c <<< 60) ||| 0x99ed83603725933)) <<< 240) ||| ((((0xdf2cc06e4b267be <<< 60) ||| 0x5580dc964cf6cab) <<< 120) ||| ((0x1b92c99ed65603 <<< 60) ||| 0x725933df28c06e4))) <<< 480) ||| ((((((0xb267be4d80dc964 <<< 60) ||| 0xcf6c9b01b92c95f) <<< 120) ||| ((0x7915d57059357f0 <<< 60) ||| 0xdc22e0b273be1b7)) <<< 240) ||| ((((0x25c164cf7c2ee4b <<< 60) ||| 0x82c9daf84dc9705) <<< 120) ||| ((0x933df07b92e0b25 <<< 60) ||| 0x77e41855cc64aee))))) <<< 2040) ||| ((((((((((((0xcaf00b98c99dd85 <<< 60) ||| 0xe01731933bb0ac0) <<< 60) ||| 0x2e63267b615825c) <<< 120) ||| ((0x64afdc9b0ab80c <<< 60) ||| 0x95f995e0d701933)) <<< 240) ||| ((((0xf30bc1ae03267e6 <<< 60) ||| 0x15835c064ef4c2b) <<< 120) ||| ((0x4b80c93ed90e09 <<< 60) ||| 0x64552beb27b26e2))) <<< 480) ||| ((((((0xaa57d64364dc554 <<< 60) ||| 0xcfbb2301b8aa99f) <<< 120) ||| ((0x56460371552bbf2 <<< 60) ||| 0x6c2ee8b1d77e4d6)) <<< 240) ||| ((((0x5dd1638fecc6eb3 <<< 60) ||| 0xa2c75bf945d6745) <<< 120) ||| ((0x8e5fb21c32e8b1c <<< 60) ||| 0xbfa63655d163d77)))) <<< 1020) ||| ((((((((((0xc3704ba2c79ef75 <<< 60) ||| 0xe097458f3daebc1) <<< 60) ||| 0x2e8b1ebb597825d) <<< 120) ||| ((0x1639f6c8704ba2c <<< 60) ||| 0x71ff985d47458f3)) <<< 240) ||| ((((0x7f30ba0e8b1f2f5 <<< 60) ||| 0x95741d1638fecc6) <<< 120) ||| ((0xeb322c76bf94596 <<< 60) ||| 0x6458f5bacac1cc8))) <<< 480) ||| ((((((0xb1cf7e418399163 <<< 60) ||| 0xcf7baf04b22c7ae) <<< 120) ||| ((0xd65e096458e7db2 <<< 60) ||| 0x1c12c8b1cf764f8)) <<< 240) ||| ((((0x655163cfbba702a <<< 60) ||| 0xa2c71fd989d3705) <<< 120) ||| ((0x8e9fb2d3a6e0b1d <<< 60) ||| 0x7be4974dc163a7e)))))) <<< 4080) ||| ((((((((((((((0xcb509b82c75dd93 <<< 60) ||| 0xa137058ebdf24c2) <<< 60) ||| 0x6e0b1e7be4984dc) <<< 120) ||| ((0x1638fecc4c9b82c <<< 60) ||| 0x75dd939937058eb)) <<< 240) ||| ((((0xdf24b26e0b1d3f6 <<< 60) ||| 0x5a745c163af7c92) <<< 120) ||| ((0xe8b82c74fd96dd3 <<< 60) ||| 0x6454e7df24c34c8))) <<< 480) ||| ((((((0xa9d6f6537699153 <<< 60) ||| 0xadfca2ed322a75f) <<< 120) ||| ((0xb9061d6454eb7b2 <<< 60) ||| 0x9bb2c8a9d6fe517)) <<< 240) ||| ((((0x659153a7ecb6e8b <<< 60) ||| 0x22a79ee87e09645) <<< 120) ||| ((0x4f3db0fc12c8a9e <<< 60) ||| 0x7ba5f8259153cf6)))) <<< 1020) ||| ((((((((((0xcbf04b22a79ef76 <<< 60) ||| 0xe096454f3daedc1) <<< 60) ||| 0x2c8a9edb5978259) <<< 120) ||| ((0x153cf7ba704b22a <<< 60) ||| 0x73ed90e096454e7)) <<< 240) ||| ((((0xbf20c18c8a9e7ea <<< 60) ||| 0x5d8019153cfccbb) <<< 120) ||| ((0x322a7b7995600 <<< 60) ||| 0x6454f7b326c00c8))) <<< 480) ||| ((((((0xa9efa6498019153 <<< 60) ||| 0xaf7c92c9b82a75f) <<< 120) ||| ((0xb905937054ebbb2 <<< 60) ||| 0x6326e0a9d7b6486)) <<< 240) ||| ((((0x4dc153afac88c9b <<< 60) ||| 0x82a75f990193705) <<< 120) ||| ((0x4ebef22c2eeca1d <<< 60) ||| 0x3f643769d943dd7))))) <<< 2040) ||| ((((((((((((0xc2704bb2873ed90 <<< 60) ||| 0xe097650e9fb21c3) <<< 60) ||| 0x2eca1d6fe51855d) <<< 120) ||| ((0x943aefc9b0abb28 <<< 60) ||| 0x75f7916157650eb)) <<< 240) ||| ((((0xf720c2aeca1f2fe <<< 60) ||| 0x1b845d943e77c37) <<< 120) ||| ((0x4bb2879ef85e09 <<< 60) ||| 0x7650f3db0bc12ec))) <<< 480) ||| ((((((0xa1f6be13825d943 <<< 60) ||| 0xaf6c8704bb2879e) <<< 120) ||| ((0xf82e017650f3df2 <<< 60) ||| 0x5c02eca1d77e4d8)) <<< 240) ||| ((((0x5d943cf7c1300b <<< 60) ||| 0xb2871fd90a1c765) <<< 120) ||| ((0xf1ff30bb0eca1e <<< 60) ||| 0x3f5d9801d9439ee)))) <<< 1020) ||| ((((((((((0xc9b003b287bb994 <<< 60) ||| 0x6007650f7b326c0) <<< 60) ||| 0xeca1efc645801d) <<< 120) ||| ((0x9438fecc4edbaa8 <<< 60) ||| 0x75ef925db7550f1)) <<< 240) ||| ((((0xff0d3b2eaa1e3fe <<< 60) ||| 0x19765d543af7c92) <<< 120) ||| ((0xecbaa871fe981d9 <<< 60) ||| 0x7550ebdb243b2ea))) <<< 480) ||| ((((((0xa1d7e640765d543 <<< 60) ||| 0xcfbbb702baa879f) <<< 120) ||| ((0x676e057550f3eae <<< 60) ||| 0xdc0aeaa1e7d1db8)) <<< 240) ||| ((((0x15d5439eec9f08b <<< 60) ||| 0x2a879df76e0d655) <<< 120) ||| ((0xf3baedc1acaa1c <<< 60) ||| 0x7fe4187d9143a7e)))))))) else (if j<8 then ((((((((((((((((0x6abd564b <<< 60) ||| 0x3b3010b66c042a6) <<< 60) ||| 0x59d9cece766bc79) <<< 120) ||| ((0xcdaf1d71cd5c792 <<< 60) ||| 0x54e5e48d5c4232f)) <<< 240) ||| ((((0x1d08caf54232c96 <<< 60) ||| 0x736b255e3abd6a4) <<< 120) ||| ((0x2cbaa772a56976a <<< 60) ||| 0xf5a4d519d08d446))) <<< 540) ||| ((((((((0x6cda11908c3635e <<< 60) ||| 0x3af1d08cb25592a) <<< 60) ||| 0xb99b3684657aa11) <<< 120) ||| ((0xa84ab255d32c950 <<< 60) ||| 0x8ca955e3ae3908c)) <<< 240) ||| ((((0x846592d09564b41 <<< 60) ||| 0x6592ac9508d3fe5) <<< 120) ||| ((0x7aa11827caf5592 <<< 60) ||| 0xa11908c8464232f)))) <<< 1020) ||| ((((((((((0x1d64a846592ac95 <<< 60) ||| 0x8c846423211964) <<< 60) ||| 0xa8469f7ac9564ab) <<< 120) ||| ((0x25592a11964a846 <<< 60) ||| 0x4232c952f084642)) <<< 240) ||| ((((0x32c967c0bc76ae2 <<< 60) ||| 0x11a7a33b3592ac9) <<< 120) ||| ((0x67673c26cdbb4d6 <<< 60) ||| 0x4ab25592ac95d58))) <<< 480) ||| ((((((0xd9b592ac95b36b2 <<< 60) ||| 0x5592cecdb373b35) <<< 120) ||| ((0x92cecd08d3b3423 <<< 60) ||| 0x366db36d9b57aa1)) <<< 240) ||| ((((0x19ab8d5c6ae3570 <<< 60) ||| 0x696b25592a119d3) <<< 120) ||| ((0xa8469d9ba7505c8 <<< 60) ||| 0x46592af1d78ebc7))))) <<< 2040) ||| ((((((((((((0x592a11908cb2542 <<< 60) ||| 0x32c95b36b2574ec) <<< 60) ||| 0xecd64ad9b592cec) <<< 120) ||| ((0xe5873b3592ac955 <<< 60) ||| 0xeaaf56cdac96736)) <<< 240) ||| ((((0x84657ab66d08cb2 <<< 60) ||| 0x56cda11a706d9b6) <<< 120) ||| ((0xcdcd65b36af55e3 <<< 60) ||| 0xb66d78f32f982cb))) <<< 480) ||| ((((((0x6e5872994232119 <<< 60) ||| 0x8cbc74234a0578) <<< 120) ||| ((0xebc75e3af1e4d2b <<< 60) ||| 0xc74234945ab8d5c)) <<< 240) ||| ((((0x1a5b571ab88466f <<< 60) ||| 0xdb7edbc72306fdb) <<< 120) ||| ((0x7ec69634b5e38ef <<< 60) ||| 0x55eabc71deabd57)))) <<< 1020) ||| ((((((((((0x8ed5c4233c91e48 <<< 60) ||| 0xf247923c91d3abc) <<< 60) ||| 0x75e3af1de4920f8) <<< 120) ||| ((0x9d483dab8dfb6fd <<< 60) ||| 0xc83e41ed9b6cdac)) <<< 240) ||| ((((0x9564afb77cfaf1d <<< 60) ||| 0x78ebc715047de3a) <<< 120) ||| ((0xd1ac8ca2f1c0431 <<< 60) ||| 0x734234526274bc7))) <<< 480) ||| ((((((0x8912f1e2030d779 <<< 60) ||| 0x2211908cb2585f9) <<< 120) ||| ((0x9d614e13e655b4d <<< 60) ||| 0x55eb086837415a0)) <<< 240) ||| ((((0x5900b7f0beddab8 <<< 60) ||| 0xf9f69aa5e108c97) <<< 120) ||| ((0x84233e7d5eaf757 <<< 60) ||| 0xaa0c6d5eaae6423)))))) <<< 4080) ||| ((((((((((((((0x3ccd81ebf7592ad <<< 60) ||| 0xb5b36b8e7923c55) <<< 60) ||| 0x8c8466cdb2e95e) <<< 120) ||| ((0xaeeb592a5e108cb <<< 60) ||| 0x25592adb55ea846)) <<< 240) ||| ((((0x715baedda6ebb59 <<< 60) ||| 0x2bab1ab88464232) <<< 120) ||| ((0x119d3a8464c8366 <<< 60) ||| 0xd78e8464233a757))) <<< 480) ||| ((((((0x8ee5b73e37ed08c <<< 60) ||| 0xe5b721af1db36bc) <<< 120) ||| ((0x7721ac95b36b254 <<< 60) ||| 0x232c9578ed9b199)) <<< 240) ||| ((((0xb8ad64ab2559280 <<< 60) ||| 0x85320b254232119) <<< 120) ||| ((0xb36b25592b571b3 <<< 60) ||| 0x6b25423366db36b)))) <<< 1020) ||| ((((((((((0xc76fdb84dab834b <<< 60) ||| 0x6ae309dbf6dfb6f) <<< 60) ||| 0x18d2db9634b6d53) <<< 120) ||| ((0x2ad956d9b6c18d8 <<< 60) ||| 0xd2f0d6b3572c95a)) <<< 240) ||| ((((0xb8d4469ab4519e6 <<< 60) ||| 0xcd24232119974ca) <<< 120) ||| ((0xb1fb1339914af56 <<< 60) ||| 0x34a11987e97857a))) <<< 480) ||| ((((((0x8d2d84e34b1b1af <<< 60) ||| 0x1d5eaae61b18085) <<< 120) ||| ((0x81ebf75b6ac957a <<< 60) ||| 0xcbc709f2a5552ab)) <<< 240) ||| ((((0xa65c721196daae6 <<< 60) ||| 0x5a62119656af501) <<< 120) ||| ((0xac9560834b57aa <<< 60) ||| 0xb9958aac5556a5e))))) <<< 2040) ||| ((((((((((((0x12f03f61fb25e14 <<< 60) ||| 0xfaa9553ea995404) <<< 60) ||| 0xa23522288c6c6a0) <<< 120) ||| ((0x24f0a7253506753 <<< 60) ||| 0x3aa1d932031b4bc)) <<< 240) ||| ((((0x24b529c92d4860b <<< 60) ||| 0xe85404ce4758e95) <<< 120) ||| ((0x1942fa44ba1d82a <<< 60) ||| 0xc2fa3ba215508c8))) <<< 480) ||| ((((((0x2e32a1fecca87d1 <<< 60) ||| 0x3d81dd0e823f639) <<< 120) ||| ((0x1c20de06cf3571 <<< 60) ||| 0xa34ab6675267156)) <<< 240) ||| ((((0xcca8633300177cb <<< 60) ||| 0x7c31b2ce95f0ab6) <<< 120) ||| ((0x53118d9338a204e <<< 60) ||| 0x626712b48f406c2)))) <<< 1020) ||| ((((((((((0x2810e027c4171fb <<< 60) ||| 0xe947aa3bd1d28d) <<< 60) ||| 0xec4383631a58d2c) <<< 120) ||| ((0x66631b17d0b6458 <<< 60) ||| 0x22a001089fc4fe0)) <<< 240) ||| ((((0x2113388f44381fb <<< 60) ||| 0xed06e433017700) <<< 120) ||| ((0x55827c11d0750 <<< 60) ||| 0x30011a06c01c808))) <<< 480) ||| ((((((0x4042000000577e4 <<< 60) ||| 0xd855c3649dec9f0) <<< 120) ||| ((0x8b2cc93bd90e116 <<< 60) ||| 0x5992bbf26b2ae73)) <<< 240) ||| ((((0x26ede13815d5649 <<< 60) ||| 0xfac8702baac93bd) <<< 120) ||| ((0x93e116559277b21 <<< 60) ||| 0xc22cab257de4575))))))) else (if j<9 then ((((((((((((((((0x50007c6f <<< 60) ||| 0x280e08001402070) <<< 60) ||| 0x40004c88082e680) <<< 120) ||| ((0x800180806000fcc <<< 60) ||| 0x30086000105840)) <<< 240) ||| ((((0x5e64200c02200 <<< 60) ||| 0xc02100802161004) <<< 120) ||| ((0x101c00101c02000 <<< 60) ||| 0xc0e030087910004))) <<< 540) ||| ((((((((0x70180030180028 <<< 60) ||| 0x180806101c04010) <<< 60) ||| 0x884038083c200) <<< 120) ||| ((0x418080e000c04 <<< 60) ||| 0x140006840080030)) <<< 240) ||| ((((0x1644001c1002000 <<< 60) ||| 0xc02030806010a06) <<< 120) ||| ((0x70141002001406 <<< 60) ||| 0xc104f341006)))) <<< 1020) ||| ((((((((((0x8a020081c30 <<< 60) ||| 0x380c0002008a000) <<< 60) ||| 0x8407000043592a) <<< 120) ||| ((0xc9564a846423357 <<< 60) ||| 0x164ab254bc29952)) <<< 240) ||| ((((0xf0b25c1e25e1b36 <<< 60) ||| 0xd9b592b66d4cad9) <<< 120) ||| ((0xbbfa366f048b256 <<< 60) ||| 0xcda5e164ab25592))) <<< 480) ||| ((((((0xe031b377b5bfa5f <<< 60) ||| 0x12f88d9b592df4d) <<< 120) ||| ((0x64ad9b592df112f <<< 60) ||| 0x31b6cdac95b36b)) <<< 240) ||| ((((0x25592ac9564ad5c <<< 60) ||| 0x6ae2c9564ad5c6a) <<< 120) ||| ((0xe3571b36b256cda <<< 60) ||| 0xc95ab8b25592b66))))) <<< 2040) ||| ((((((((((((0xd08cb25592b66d6 <<< 60) ||| 0x4ab25bdaac9564b) <<< 60) ||| 0x66e592ac9564ad5) <<< 120) ||| ((0xc592ac95ab8b256 <<< 60) ||| 0xae2c952f0b25592)) <<< 240) ||| ((((0xac9564ab256ae25 <<< 60) ||| 0xe164ab254232c95) <<< 120) ||| ((0x64ab25592ac967c <<< 60) ||| 0x846423211964b7))) <<< 480) ||| ((((((0x94592ddf164ab25 <<< 60) ||| 0x7562c9564ab2559) <<< 120) ||| ((0x2ac96b80d5c5e3a <<< 60) ||| 0xc9508cb25592ac9)) <<< 240) ||| ((((0x508cb25592b66d6 <<< 60) ||| 0x4ab254232119ab9) <<< 120) ||| ((0x3e0532b66d64b59 <<< 60) ||| 0xf6cddd92eaad5c4)))) <<< 1020) ||| ((((((((((0x232bd564aa65532 <<< 60) ||| 0xaf1cceabc76cdac) <<< 60) ||| 0x96dccb25423366d) <<< 120) ||| ((0x2f1746ba32c9564 <<< 60) ||| 0xad5c1a5b66d64a8)) <<< 240) ||| ((((0x464bc2c9564ab25 <<< 60) ||| 0x592b57164ab2542) <<< 120) ||| ((0x335712f0b259d9d <<< 60) ||| 0xc9564a846592dc3))) <<< 480) ||| ((((((0x508cb25592bab1b <<< 60) ||| 0x36b25b7aa119ab8) <<< 120) ||| ((0xb254bc2119ab96e <<< 60) ||| 0x6592db9adcd3b36)) <<< 240) ||| ((((0xcda996dae021592 <<< 60) ||| 0xb57178ebc76cda1) <<< 120) ||| ((0x18696d9b6cddad9 <<< 60) ||| 0xb36d5c423211964)))))) <<< 4080) ||| ((((((((((((((0xab254bc2c9564ab <<< 60) ||| 0x25592ac95ab8978) <<< 60) ||| 0x592ac9564ab2559) <<< 120) ||| ((0x2ac9564a846ab02 <<< 60) ||| 0xc9508cb25592ac9)) <<< 240) ||| ((((0x6766b25592cecd0 <<< 60) ||| 0x8cb25592da9d64a) <<< 120) ||| ((0xb25592ac9564ab2 <<< 60) ||| 0x56ae58a5b36d9b6))) <<< 480) ||| ((((((0xcdbab2b0ebc7b43 <<< 60) ||| 0x86cdcd9b5e3aa) <<< 120) ||| ((0x5578ea955e3aa55 <<< 60) ||| 0x64ab25592b66de4)) <<< 240) ||| ((((0x8b254bc561ecacd <<< 60) ||| 0x9bb2b211ac8e846) <<< 120) ||| ((0xb23d8e0ceb5876c <<< 60) ||| 0xdd61d08cd9b6cdb)))) <<< 1020) ||| ((((((((((0x66d2f0b25592b57 <<< 60) ||| 0x12f0b25592b66ea) <<< 60) ||| 0x90d9b6cdaf1c042) <<< 120) ||| ((0xd9b592d521b3602 <<< 60) ||| 0x16cdac95b363a56)) <<< 240) ||| ((((0xcd99d578e8464bc <<< 60) ||| 0x21192f084642336) <<< 120) ||| ((0x6db3754833aa119 <<< 60) ||| 0xb36b25010b66db3))) <<< 480) ||| ((((((0x6b256cdb66d78ed <<< 60) ||| 0x9b6cdb66d64ad9b) <<< 120) ||| ((0x10af1db373b39d <<< 60) ||| 0x9c94564ad5c592a)) <<< 240) ||| ((((0xc9564ad5c9f0211 <<< 60) ||| 0x908d629592a1196) <<< 120) ||| ((0x4b608af82c96bb0 <<< 60) ||| 0xb2575629f5b36d5))))) <<< 2040) ||| ((((((((((((0xc592ac96b80d5c6 <<< 60) ||| 0xae3571ab8846423) <<< 60) ||| 0x2c9508cb25592ac) <<< 120) ||| ((0x95d3ab2574ed702 <<< 60) ||| 0xb815c0ae02c9564)) <<< 240) ||| ((((0xa846592ac95b368 <<< 60) ||| 0x469f0357004231b) <<< 120) ||| ((0x6cdb66d64b59f6c <<< 60) ||| 0xdac96766b2518d9))) <<< 480) ||| ((((((0x9d564ab25592a11 <<< 60) ||| 0x9b369786cdb66d6) <<< 120) ||| ((0x4ab256ae0d2d08c <<< 60) ||| 0xb25592ac95ab884)) <<< 240) ||| ((((0x66ae0ef52f03bd6 <<< 60) ||| 0xae3570696a656cd) <<< 120) ||| ((0xd61eb0ed9b4bc0e <<< 60) ||| 0xf5b369784bc2c96)))) <<< 1020) ||| ((((((((((0xaded9b33a99d564 <<< 60) ||| 0xab25592ac9564ab) <<< 60) ||| 0x25592ac9564ab25) <<< 120) ||| ((0x592a11aac0b2542 <<< 60) ||| 0x32c9564b3b3592a)) <<< 240) ||| ((((0x1192f0846592a11 <<< 60) ||| 0x908c846423366d6) <<< 120) ||| ((0x4ad9b592a5e1b36 <<< 60) ||| 0x8466cdb66d4cad9))) <<< 480) ||| ((((((0xbaa42c9564ad9b9 <<< 60) ||| 0xd9ac940420216cd) <<< 120) ||| ((0xb66d64b5486cda9 <<< 60) ||| 0x96a90a656cdb66d)) <<< 240) ||| ((((0xb366755b6adb404 <<< 60) ||| 0x2021592b66d64ab) <<< 120) ||| ((0x251d2ac9564a3a5 <<< 60) ||| 0x6cdb66ccea6755b))))))) else ((((((((((((((0x74104 <<< 60) ||| 0x9902320082011c4) <<< 60) ||| 0x232394001990172) <<< 180) ||| ((((0x821201344301344 <<< 60) ||| 0x26212c273021504) <<< 60) ||| 0x4090006020a854)) <<< 300) ||| ((((((0x40005a506ca083c <<< 60) ||| 0x4000c360e2a6e0) <<< 60) ||| 0x10c5600081e0008) <<< 120) ||| ((0x1e0c281d3021601 <<< 60) ||| 0x368301310201368))) <<< 600) ||| ((((((((0x201808262008001 <<< 60) ||| 0x80188169400152c) <<< 60) ||| 0x1006102c5020f00) <<< 120) ||| ((0x840ff3009200014 <<< 60) ||| 0x1e8404428002820)) <<< 300) ||| ((((((0x4000fcc0901a40 <<< 60) ||| 0x280802000c120) <<< 60) ||| 0x82060404000909) <<< 120) ||| ((0x560f98195821c04 <<< 60) ||| 0x12081c021210001)))) <<< 1260) ||| ((((((((((0x79908030008e682 <<< 60) ||| 0xc002024100300) <<< 60) ||| 0x88e604800062024) <<< 180) ||| ((((0x613980e0000880 <<< 60) ||| 0x304850404840104) <<< 60) ||| 0x84e604004328020)) <<< 300) ||| ((((((0x21d18001210005 <<< 60) ||| 0x70e8c0000b94403) <<< 60) ||| 0xa10242020001c10) <<< 120) ||| ((0xe13000813058c0 <<< 60) ||| 0x30920030006c603))) <<< 600) ||| ((((((((0x80208212c001410 <<< 60) ||| 0x617180e000c068) <<< 60) ||| 0x40b8ce50908e5e3) <<< 120) ||| ((0x4e300d081a10 <<< 60) ||| 0x600e3080701806)) <<< 300) ||| ((((((0xca2020001594000 <<< 60) ||| 0x101080701c10345) <<< 60) ||| 0x800021820109020) <<< 120) ||| ((0xb01802082049881 <<< 60) ||| 0x3440413101c202e))))) <<< 2520) ||| ((((((((((((0x60380c30400c021 <<< 60) ||| 0xb98061798061244) <<< 60) ||| 0x41020021004241) <<< 180) ||| ((((0x42c102004010c <<< 60) ||| 0x84c0e12100e1) <<< 60) ||| 0x810400820a020)) <<< 300) ||| ((((((0x808300808001 <<< 60) ||| 0x80004010d200009) <<< 60) ||| 0x80a4400020c040) <<< 120) ||| ((0x800068401f98002 <<< 60) ||| 0x404101c061002))) <<< 600) ||| ((((((((0x8100800030c060 <<< 60) ||| 0xc1006000c020708) <<< 60) ||| 0x6020006030001c) <<< 120) ||| ((0x382008001800300 <<< 60) ||| 0x240303830404060)) <<< 300) ||| ((((((0x20086ed00040001 <<< 60) ||| 0x84c400040900040) <<< 60) ||| 0x9010003f2824001) <<< 120) ||| ((0x80c12000c136501 <<< 60) ||| 0x860009840709800)))) <<< 1260) ||| ((((((((((0x30001c2010002f2 <<< 60) ||| 0x80c000710060000) <<< 60) ||| 0x8603b2804342000) <<< 180) ||| ((((0x2182000010fcd0 <<< 60) ||| 0x401804002806080) <<< 60) ||| 0xc0e0901860104)) <<< 300) ||| ((((((0x12010bcc8404804 <<< 60) ||| 0x281c120100080) <<< 60) ||| 0x90080c3f3024060) <<< 120) ||| ((0xc106f3024060 <<< 60) ||| 0x8a0701000300))) <<< 600) ||| ((((((((0x84c2c800420004c <<< 60) ||| 0x2180c02070c020) <<< 60) ||| 0x303860300040000) <<< 120) ||| ((0x80c301804001c10 <<< 60) ||| 0x3e50180050080c)) <<< 300) ||| ((((((0x18040e030f8c0 <<< 60) ||| 0x300079000808300) <<< 60) ||| 0x800061808020700) <<< 120) ||| ((0x8000380438201c <<< 60) ||| 0x200100200080fe))))))))))
def g127H7 (j : Nat) : Nat := (if j<1 then ((((((((((((((((0x4860 <<< 60) ||| 0x203200) <<< 60) ||| 0x0) <<< 120) ||| ((0x1cb30000 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x1821) <<< 120) ||| ((0x923c02000024b53 <<< 60) ||| 0x3d0000000306fd1))) <<< 480) ||| ((((((0x740410002c8e000 <<< 60) ||| 0x34d800000000000) <<< 120) ||| ((0x88570c400000000 <<< 60) ||| 0x3c26000185)) <<< 240) ||| ((((0xac40c0000003c4e <<< 60) ||| 0xf24800000000004) <<< 120) ||| ((0x1000013c800052 <<< 60) ||| 0x424d10002cd7000)))) <<< 1020) ||| ((((((((((0x0 <<< 60) ||| 0x0) <<< 60) ||| 0xf151463000000) <<< 120) ||| ((0x2494302ccf6 <<< 60) ||| 0x1e880200000000)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x40698a3000) <<< 120) ||| ((0x51ec0000000 <<< 60) ||| 0x11b0000c1624))) <<< 480) ||| ((((((0x84c1c84730001c4 <<< 60) ||| 0xcaa0003439) <<< 120) ||| ((0x81580000 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x283b235 <<< 60) ||| 0x440fd19800042ff) <<< 120) ||| ((0x80000201d00000 <<< 60) ||| 0x0))))) <<< 2040) ||| ((((((((((((0xf2c4000 <<< 60) ||| 0x1263ca00002c5e0) <<< 60) ||| 0x20d4427800000) <<< 120) ||| ((0x611648d000 <<< 60) ||| 0x28f70003c4a0000)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x43268b2000000) <<< 120) ||| ((0x30ab4960000000 <<< 60) ||| 0x24300001011f))) <<< 480) ||| ((((((0x3c0000000190110 <<< 60) ||| 0x40000b244000e39) <<< 120) ||| ((0x800000030dd0001 <<< 60) ||| 0x6873ac00000038)) <<< 240) ||| ((((0xd0a1350c6000000 <<< 60) ||| 0x0) <<< 120) ||| ((0xc0900000000 <<< 60) ||| 0x28fca08c00000)))) <<< 1020) ||| ((((((((((0x0 <<< 60) ||| 0xf3480000002) <<< 60) ||| 0x79000000000000) <<< 120) ||| ((0x282b0002ca <<< 60) ||| 0x6000000002ec000)) <<< 240) ||| ((((0x1cad0000000c <<< 60) ||| 0x154000000000000) <<< 120) ||| ((0x14f50000000000 <<< 60) ||| 0x281f03ec0000001))) <<< 480) ||| ((((((0xcbed33548300034 <<< 60) ||| 0x9353a005c000000) <<< 120) ||| ((0x14e1 <<< 60) ||| 0xb1b7835c)) <<< 240) ||| ((((0x2d0000000000000 <<< 60) ||| 0x62dcc62000) <<< 120) ||| ((0x346100000000000 <<< 60) ||| 0x0)))))) <<< 4080) ||| ((((((((((((((0xc5f000000 <<< 60) ||| 0x73380000000000) <<< 60) ||| 0x0) <<< 120) ||| ((0x105b43e00 <<< 60) ||| 0x22e10ecf37)) <<< 240) ||| ((((0x72e80001166 <<< 60) ||| 0x874d39cc8700000) <<< 120) ||| ((0x76f209c1 <<< 60) ||| 0xe0000000326c000))) <<< 480) ||| ((((((0xe <<< 60) ||| 0x148000000000033) <<< 120) ||| ((0x6ac6b0000000000 <<< 60) ||| 0x40b80000000)) <<< 240) ||| ((((0x30ea09900000 <<< 60) ||| 0x0) <<< 120) ||| ((0x4a98204847 <<< 60) ||| 0xb0cc00000000000)))) <<< 1020) ||| ((((((((((0xf1 <<< 60) ||| 0xc0000000425e01) <<< 60) ||| 0x8000b023071f12c) <<< 120) ||| ((0x28a200000 <<< 60) ||| 0x0)) <<< 240) ||| ((((0xa394c51 <<< 60) ||| 0x5051460000249df) <<< 120) ||| ((0x340000000cc400 <<< 60) ||| 0x0))) <<< 480) ||| ((((((0x7229 <<< 60) ||| 0xc1c000000000000) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x303000000000000 <<< 60) ||| 0x0) <<< 120) ||| ((0x34650000000000 <<< 60) ||| 0x32b3))))) <<< 2040) ||| ((((((((((((0xce00000ced00000 <<< 60) ||| 0x2314000000000) <<< 60) ||| 0x0) <<< 120) ||| ((0x7402c1800000000 <<< 60) ||| 0x1838000000000)) <<< 240) ||| ((((0x20cb0000000000 <<< 60) ||| 0xc500000) <<< 120) ||| ((0x42700 <<< 60) ||| 0x100242400034d))) <<< 480) ||| ((((((0xbf108cd30002c01 <<< 60) ||| 0xcbd00038e36) <<< 120) ||| ((0x2f0000000000000 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x34d90000000e1d5 <<< 60) ||| 0x4150002c3400035) <<< 120) ||| ((0x40000000000000 <<< 60) ||| 0x0)))) <<< 1020) ||| ((((((((((0xd <<< 60) ||| 0x3fc00000038ea00) <<< 60) ||| 0xa1f) <<< 120) ||| ((0x72200000003 <<< 60) ||| 0xcf300004c000000)) <<< 240) ||| ((((0x10c7000000 <<< 60) ||| 0x2694df0000000) <<< 120) ||| ((0xb3280000 <<< 60) ||| 0xe0))) <<< 480) ||| ((((((0xa000031f4000000 <<< 60) ||| 0x18670001ccf0002) <<< 120) ||| ((0xfe000044f12b80 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x4221303 <<< 60) ||| 0x100010731050a2) <<< 120) ||| ((0x600600211010 <<< 60) ||| 0x143091000001001))))))) else ((((((((((((0x2be <<< 60) ||| 0x80ef0f007800000) <<< 120) ||| ((0x3c4c002800 <<< 60) ||| 0xb3580000000c36)) <<< 180) ||| ((((0x1 <<< 60) ||| 0x294000000000000) <<< 60) ||| 0x8198306405a22)) <<< 360) ||| ((((((0x6cab00000000000 <<< 60) ||| 0x82f00000) <<< 60) ||| 0x0) <<< 180) ||| ((((0x1c95 <<< 60) ||| 0x0) <<< 60) ||| 0x3c3d133000000))) <<< 780) ||| ((((((((0x2022000006e000 <<< 60) ||| 0x30ef00000000000) <<< 120) ||| ((0x8f8c01e0de00000 <<< 60) ||| 0xdc000000147)) <<< 180) ||| ((((0xf00024f90000000 <<< 60) ||| 0x50fc069127c0000) <<< 60) ||| 0x20fdf00c00000)) <<< 360) ||| ((((((0x30640000000000 <<< 60) ||| 0x24537048000f120) <<< 60) ||| 0x0) <<< 180) ||| ((((0xd30c000000000 <<< 60) ||| 0x92a00000000000) <<< 60) ||| 0xb400000000000)))) <<< 1560) ||| ((((((((((0x207000 <<< 60) ||| 0x88b00034fa000) <<< 120) ||| ((0x428501b0001 <<< 60) ||| 0x6a000381300000)) <<< 180) ||| ((((0x38c2000000 <<< 60) ||| 0x532000033a4000) <<< 60) ||| 0x0)) <<< 360) ||| ((((((0x62 <<< 60) ||| 0xc2046000000092d) <<< 60) ||| 0x8c7700034290002) <<< 180) ||| ((((0x497f124000515c0 <<< 60) ||| 0xa4000248c30b000) <<< 60) ||| 0x0))) <<< 780) ||| ((((((((0x0 <<< 60) ||| 0x14e200) <<< 120) ||| ((0x2ce4116c000000 <<< 60) ||| 0x0)) <<< 180) ||| ((((0x0 <<< 60) ||| 0x2417d29f0f) <<< 60) ||| 0x11112d02000207e)) <<< 360) ||| ((((((0x0 <<< 60) ||| 0x0) <<< 60) ||| 0x0) <<< 180) ||| ((((0xe09c <<< 60) ||| 0xb2e400000000) <<< 60) ||| 0x43b8000000000))))))
def g127D8 (j : Nat) : Nat := (if j<5 then (if j<2 then (if j<1 then ((((((((((((((((0xb805d130 <<< 60) ||| 0x9fd87d9130bdd83) <<< 60) ||| 0xd9130bf980d9130) <<< 120) ||| ((0x9fd8799130dbd74 <<< 60) ||| 0x99130bdd8399130)) <<< 240) ||| ((((0x9fd8759130dbd74 <<< 60) ||| 0x59130bef8259130) <<< 120) ||| ((0x9fd8719130bdd83 <<< 60) ||| 0x19130bed8219130))) <<< 540) ||| ((((((((0xbf58119130bf980 <<< 60) ||| 0x19130bdf8458d30) <<< 60) ||| 0xddd7458d30fdb80) <<< 120) ||| ((0x58d30bdf8650d30 <<< 60) ||| 0xbdd8650d30ddd76)) <<< 240) ||| ((((0x50d30f9e6450d30 <<< 60) ||| 0xf9d6450d30fdb80) <<< 120) ||| ((0x50d30df97458130 <<< 60) ||| 0xefb6458130ef964)))) <<< 1020) ||| ((((((((((0x58130fdb8358130 <<< 60) ||| 0xfd96358130fd953) <<< 60) ||| 0x58130fd94358130) <<< 120) ||| ((0xfd96354130fd943 <<< 60) ||| 0x54130bed839d920)) <<< 240) ||| ((((0xbef835d920bef84 <<< 60) ||| 0x59520bed839d120) <<< 120) ||| ((0xbef835d120bed83 <<< 60) ||| 0xd9120bed8399120))) <<< 480) ||| ((((((0xbed8319120bef86 <<< 60) ||| 0x55120bef8458d20) <<< 120) ||| ((0xbef8650d20bed86 <<< 60) ||| 0x50d20fae6450d20)) <<< 240) ||| ((((0xfad6450d20fcd63 <<< 60) ||| 0x50d20feb8558120) <<< 120) ||| ((0xfe98558120fe965 <<< 60) ||| 0x58120feb8458120))))) <<< 2040) ||| ((((((((((((0xfe98458120fe954 <<< 60) ||| 0x58120feb8358120) <<< 60) ||| 0xfe98358120fe963) <<< 120) ||| ((0x58120fe95358120 <<< 60) ||| 0xfe94358120feb86)) <<< 240) ||| ((((0x50120fe98650120 <<< 60) ||| 0xfeb8550120fe985) <<< 120) ||| ((0x50120fe96550120 <<< 60) ||| 0xfe95450120feb83))) <<< 480) ||| ((((((0x50120fe98350120 <<< 60) ||| 0xfe96350120fe953) <<< 120) ||| ((0x50120fe94350120 <<< 60) ||| 0xbf5839d910bf783)) <<< 240) ||| ((((0x5d910bf584d9510 <<< 60) ||| 0xbf78459510bf586) <<< 120) ||| ((0x9d110bf5839d110 <<< 60) ||| 0xbf7865d110bf783)))) <<< 1020) ||| ((((((((((0x5d110bf583d9110 <<< 60) ||| 0xbf58699110bf583) <<< 60) ||| 0x99110bf78359110) <<< 120) ||| ((0xfe78259110bf583 <<< 60) ||| 0x19110bf58695110)) <<< 240) ||| ((((0xbf584d8d10bf784 <<< 60) ||| 0x58d10ff38058d10) <<< 120) ||| ((0xbf586d0d10fb564 <<< 60) ||| 0xd0d10bf78650d10))) <<< 480) ||| ((((((0xbf58650d10fb664 <<< 60) ||| 0x50d10fb56450d10) <<< 120) ||| ((0xfd56350d10ff364 <<< 60) ||| 0x54110ff16454110)) <<< 240) ||| ((((0xff36354110ff163 <<< 60) ||| 0x54110ff14354110) <<< 120) ||| ((0xff38650110ff286 <<< 60) ||| 0x50110ff18650110)))))) <<< 4080) ||| ((((((((((((((0xff08650110ff385 <<< 60) ||| 0x50110ff18550110) <<< 60) ||| 0xff36550110ff165) <<< 120) ||| ((0x50110ff36450110 <<< 60) ||| 0xff16450110ff383)) <<< 240) ||| ((((0x50110ff18350110 <<< 60) ||| 0xff36350110ff163) <<< 120) ||| ((0x50110ff15350110 <<< 60) ||| 0xff143501109ef82))) <<< 480) ||| ((((((0x5da649f7815d664 <<< 60) ||| 0x9ed80dc964de982) <<< 120) ||| ((0x5c064df1815c064 <<< 60) ||| 0x9ef825d9549f781)) <<< 240) ||| ((((0x5d9549f580dc554 <<< 60) ||| 0x9ef825d3639ef82) <<< 120) ||| ((0x5d9439f7815d543 <<< 60) ||| 0x9ef825d3609f581)))) <<< 1020) ||| ((((((((((0xdd5609df835d950 <<< 60) ||| 0x9ef825db409f781) <<< 60) ||| 0x5d7409ef825d940) <<< 120) ||| ((0x9f7815d540b9d83 <<< 60) ||| 0x95140b3d85d0d40)) <<< 240) ||| ((((0xeb96458140ed963 <<< 60) ||| 0x58130f595354130) <<< 120) ||| ((0xbe9809d920beb80 <<< 60) ||| 0x5d920be581d9520))) <<< 480) ||| ((((((0xbe980d9520be980 <<< 60) ||| 0x9d120be980d9120) <<< 120) ||| ((0xbe980991209ef87 <<< 60) ||| 0x591209ed8719120)) <<< 240) ||| ((((0xb6d8519120bcd83 <<< 60) ||| 0x19120be58119120) <<< 120) ||| ((0xbe98019120bcd83 <<< 60) ||| 0x95120be98095120))))) <<< 2040) ||| ((((((((((((0xbe78155120beb80 <<< 60) ||| 0x5cd20be980d8d20) <<< 60) ||| 0xbeb8054d20b6d85) <<< 120) ||| ((0xd0d20be980d0d20 <<< 60) ||| 0xeeb6558120ee965)) <<< 240) ||| ((((0x58120beb8458120 <<< 60) ||| 0xeeb6458120ee964) <<< 120) ||| ((0x58120eeb6358120 <<< 60) ||| 0xee96358120beb86))) <<< 480) ||| ((((((0x50120be98650120 <<< 60) ||| 0xfaa6450120fa964) <<< 120) ||| ((0x50120faa5450120 <<< 60) ||| 0xfa95450120fab43)) <<< 240) ||| ((((0x50120fa94350120 <<< 60) ||| 0xb75859d910bf180) <<< 120) ||| ((0x9d9109f587d9510 <<< 60) ||| 0xbf1809d110bf180)))) <<< 1020) ||| ((((((((((0x99110be78259110 <<< 60) ||| 0x9f58719110b7585) <<< 60) ||| 0x19110bd58319110) <<< 120) ||| ((0xbe58219110bf180 <<< 60) ||| 0x19110bd58395110)) <<< 240) ||| ((((0xbf180951109f787 <<< 60) ||| 0x55110b77855cd10) <<< 120) ||| ((0xbf38058d10b7585 <<< 60) ||| 0xd0d10bf180d0d10))) <<< 480) ||| ((((((0xf716554110bf384 <<< 60) ||| 0x54110f715454110) <<< 120) ||| ((0xf715354110bf385 <<< 60) ||| 0x50110bf18550110)) <<< 240) ||| ((((0xfb26450110fb164 <<< 60) ||| 0x50110fb25450110) <<< 120) ||| ((0xfb15450110fb343 <<< 60) ||| 0x50110fb14350110))))))) else ((((((((((((((((0x759543bd <<< 60) ||| 0xf83595439fd87d9) <<< 60) ||| 0x143cff76d9143bd) <<< 120) ||| ((0xd83d9143bbe8799 <<< 60) ||| 0x143bbd8699143bb)) <<< 240) ||| ((((0xd8099143cff7659 <<< 60) ||| 0x143bef8259143eb) <<< 120) ||| ((0xf7659143ebc7659 <<< 60) ||| 0x143faf8259143bb))) <<< 540) ||| ((((((((0xf8059143bbd8695 <<< 60) ||| 0x143bf78155143bb) <<< 60) ||| 0xf8655143edf7658) <<< 120) ||| ((0xd43edc7658d43ed <<< 60) ||| 0xf6558d43edd6558)) <<< 240) ||| ((((0xd43f9f8458d43f9 <<< 60) ||| 0xc8458d43f9e6458) <<< 120) ||| ((0xd43f9d6458d43f9 <<< 60) ||| 0xe5458d43f9d5458)))) <<< 1020) ||| ((((((((((0xd43bdf8058d439f <<< 60) ||| 0xd86dc143dbe64dc) <<< 60) ||| 0x143dbd64dc143dd) <<< 120) ||| ((0xd63dc1439ff845d <<< 60) ||| 0x760aff8459760bf)) <<< 240) ||| ((((0x781553609ff845c <<< 60) ||| 0xf60aff8458f609f) <<< 120) ||| ((0xf8750f609fd8750 <<< 60) ||| 0xf60afd8650f60db))) <<< 480) ||| ((((((0xd7450f60ebd6450 <<< 60) ||| 0xf60ddd7350f60ed) <<< 120) ||| ((0xd6350f60bf581dd <<< 60) ||| 0x5609fd84dd560bd)) <<< 240) ||| ((((0xf835d560afd84d9 <<< 60) ||| 0x560bfb8059560af) <<< 120) ||| ((0xf84595609fd83dd <<< 60) ||| 0x160afd869d160db))))) <<< 2040) ||| ((((((((((((0xf749d160aff865d <<< 60) ||| 0x160bef825d160b7) <<< 60) ||| 0xd851d160dbd741d) <<< 120) ||| ((0x160bdd831d160be <<< 60) ||| 0xd821d160bf5811d)) <<< 240) ||| ((((0x160afe87d9160af <<< 60) ||| 0xd83d9160afd8699) <<< 120) ||| ((0x160dbf7499160bf <<< 60) ||| 0x98099160dbf7459))) <<< 480) ||| ((((((0x160bef8259160eb <<< 60) ||| 0xf7459160ebc7459) <<< 120) ||| ((0x160aff8359160ee <<< 60) ||| 0xf82591609fe8795)) <<< 240) ||| ((((0x1609fd8795160af <<< 60) ||| 0xd8695160bdd8395) <<< 120) ||| ((0x160bf98095160bf <<< 60) ||| 0x781551609fd84dc)))) <<< 1020) ||| ((((((((((0xd60afd84d8d60dd <<< 60) ||| 0xf7358d60bfb8058) <<< 60) ||| 0xd60aff8458d60ed) <<< 120) ||| ((0xf7358d60efb8058 <<< 60) ||| 0xd609fe87d0d609f)) <<< 240) ||| ((((0xd87d0d60afd86d0 <<< 60) ||| 0xd60b7d85d0d60eb) <<< 120) ||| ((0xd64d0d60bf980d0 <<< 60) ||| 0xd609ff8750d609f))) <<< 480) ||| ((((((0xe8750d609fc8750 <<< 60) ||| 0xd60afd8650d60eb) <<< 120) ||| ((0xd6450d60edd6350 <<< 60) ||| 0xd609fd84dd9509f)) <<< 240) ||| ((((0xf845d950b7f8459 <<< 60) ||| 0x5509fd86dd150d7) <<< 120) ||| ((0xd65dd150bef8259 <<< 60) ||| 0x150bdd8319150be)))))) <<< 4080) ||| ((((((((((((((0xd8219150bf58119 <<< 60) ||| 0x150bf98019150b7) <<< 60) ||| 0xf8655150d7f7655) <<< 120) ||| ((0x150ddf73d8d50dd <<< 60) ||| 0xf7350d509ff8759)) <<< 240) ||| ((((0x7409ff865cf40db <<< 60) ||| 0xd645cf409ff8758) <<< 120) ||| ((0xf409fd8758f40dd <<< 60) ||| 0xd7358f40bbf8650))) <<< 480) ||| ((((((0xf40bbd8650f40db <<< 60) ||| 0xd7650f40f9d6350) <<< 120) ||| ((0xf409fd83dd940cf <<< 60) ||| 0xf769d940bbd849d)) <<< 240) ||| ((((0x940bbf845d940be <<< 60) ||| 0xf825d940cff865d) <<< 120) ||| ((0x9409ff845d940db <<< 60) ||| 0xf845d9409ff835d)))) <<< 1020) ||| ((((((((((0x940def825d9409f <<< 60) ||| 0xe871d940cfd761d) <<< 60) ||| 0x940b7d851d940bd) <<< 120) ||| ((0xd831d940bed821d <<< 60) ||| 0x940bf5811d9409f)) <<< 240) ||| ((((0xd86dd540bf7815d <<< 60) ||| 0x5409ff865d5409f) <<< 120) ||| ((0xe87d95409fd87d9 <<< 60) ||| 0x540bbd84d9540bf))) <<< 480) ||| ((((((0x581d9540bf980d9 <<< 60) ||| 0x5409ff87595409f) <<< 120) ||| ((0xc87595409fd87d9 <<< 60) ||| 0x140cff76d9140bf)) <<< 240) ||| ((((0x980d9140bbe8799 <<< 60) ||| 0x140bbd8699140bb) <<< 120) ||| ((0xd8399140cff7659 <<< 60) ||| 0x140bef8259140eb))))) <<< 2040) ||| ((((((((((((0xf7659140ebc7659 <<< 60) ||| 0x140bbf8359140fa) <<< 60) ||| 0xf8259140bbd8695) <<< 120) ||| ((0x140bf78155140bb <<< 60) ||| 0xf86551409fd86dc)) <<< 240) ||| ((((0xd40dbe64dcd40db <<< 60) ||| 0xd64dcd409fe87d8) <<< 120) ||| ((0xd409fd87d8d40bb <<< 60) ||| 0xd84d8d40bf980d8))) <<< 480) ||| ((((((0xd409ff8758d409f <<< 60) ||| 0xe8758d409fc8758) <<< 120) ||| ((0xd40bbd86d0d40db <<< 60) ||| 0xf76d0d40dbd76d0)) <<< 240) ||| ((((0xd40ddf7350d40bf <<< 60) ||| 0xb8050d40bbf8650) <<< 120) ||| ((0xd40bbd8650d40db <<< 60) ||| 0xf7650d40dbd7650)))) <<< 1020) ||| ((((((((((0xd40f9f7350d40f9 <<< 60) ||| 0xd6350d40fbb8050) <<< 60) ||| 0xd40efb7658140ef) <<< 120) ||| ((0x87658140efb6558 <<< 60) ||| 0x140ef96558140fb)) <<< 240) ||| ((((0xb8458140fb88458 <<< 60) ||| 0x140efb6458140fb) <<< 120) ||| ((0xa6458140ef96458 <<< 60) ||| 0x140fb96458140fb))) <<< 480) ||| ((((((0xa5458140fb95458 <<< 60) ||| 0x140dfb7358140ef) <<< 120) ||| ((0xb6358140ef96358 <<< 60) ||| 0x140fbb4358140fb)) <<< 240) ||| ((((0x943581409ff845d <<< 60) ||| 0x930ddf835d930df) <<< 120) ||| ((0xb805d9309ff865d <<< 60) ||| 0x130ddf835d130df)))))))) else (if j<3 then ((((((((((((((((0x8d40dff7 <<< 60) ||| 0x654d40dfd7654d4) <<< 60) ||| 0xfbe6454d40fbd6) <<< 120) ||| ((0x454d40fbd76d0d4 <<< 60) ||| 0xbff8650d40bfd8)) <<< 240) ||| ((((0x650d40dff7650d4 <<< 60) ||| 0xdfd7650d40fbf6) <<< 120) ||| ((0x450d40fbd6450d4 <<< 60) ||| 0xfdd6350d40fbf8))) <<< 540) ||| ((((((((0x650d40fbe8650d4 <<< 60) ||| 0xfbd8650d40fbc8) <<< 60) ||| 0x650d40fbf7650d4) <<< 120) ||| ((0xfbe7650d40fbd7 <<< 60) ||| 0x650d40fbc7650d4)) <<< 240) ||| ((((0xff88758140ffb7 <<< 60) ||| 0x658140ffb855814) <<< 120) ||| ((0xff98558140ffb7 <<< 60) ||| 0x558140ff9755814)))) <<< 1020) ||| ((((((((((0xff96558140ffb8 <<< 60) ||| 0x458140ff9845814) <<< 60) ||| 0xff95458140ffb8) <<< 120) ||| ((0x358140ff9835814 <<< 60) ||| 0xffb7358140ff97)) <<< 240) ||| ((((0x358140ff9635814 <<< 60) ||| 0xff95358140ff94) <<< 120) ||| ((0x358140dfe845d93 <<< 60) ||| 0xdfd845d930dff8))) <<< 480) ||| ((((((0x65d130dfe865d13 <<< 60) ||| 0xdfd865d130dfc8) <<< 120) ||| ((0x65d130dfd75d913 <<< 60) ||| 0xdfd74d9130bfd8)) <<< 240) ||| ((((0x699130dfd769913 <<< 60) ||| 0xdfd7599130dfd8) <<< 120) ||| ((0x759130dfd765913 <<< 60) ||| 0xdfd7559130dfd7))))) <<< 2040) ||| ((((((((((((0x459130fdd835913 <<< 60) ||| 0xfef8259130dfd7) <<< 60) ||| 0x519130fde8458d3) <<< 120) ||| ((0xfdd8458d30fde6 <<< 60) ||| 0x458d30fdd6458d3)) <<< 240) ||| ((((0xfdf6454d30fde6 <<< 60) ||| 0x454d30fdd6454d3) <<< 120) ||| ((0xfdc6454d30fdf8 <<< 60) ||| 0x650d30fde8650d3))) <<< 480) ||| ((((((0xfdd8650d30fdc8 <<< 60) ||| 0x650d30fdf6450d3) <<< 120) ||| ((0xfdd6450d30ffa8 <<< 60) ||| 0x458130ff9845813)) <<< 240) ||| ((((0xffa6458130ff96 <<< 60) ||| 0x458130ffb645413) <<< 120) ||| ((0xffa6454130ff96 <<< 60) ||| 0x454130ff8645413)))) <<< 1020) ||| ((((((((((0xfed8458d20fee7 <<< 60) ||| 0x654d20fed7654d2) <<< 60) ||| 0xfee7454d20fed7) <<< 120) ||| ((0x454d20fef6454d2 <<< 60) ||| 0xfee6454d20fed6)) <<< 240) ||| ((((0x454d20fec6454d2 <<< 60) ||| 0xfef8650d20fed8) <<< 120) ||| ((0x650d20ff5855911 <<< 60) ||| 0xff56559110ff58))) <<< 480) ||| ((((((0x359110ff574d8d1 <<< 60) ||| 0xff58758d10ff57) <<< 120) ||| ((0x658d10ff68458d1 <<< 60) ||| 0xff58458d10ff67)) <<< 240) ||| ((((0x458d10ff57458d1 <<< 60) ||| 0xff66458d10ff56) <<< 120) ||| ((0x458d10ff76454d1 <<< 60) ||| 0xff56454d10ff78)))))) <<< 4080) ||| ((((((((((((((0x650d10ff68650d1 <<< 60) ||| 0xff58650d10ff48) <<< 60) ||| 0x650d10ff76450d1) <<< 120) ||| ((0xff56450d109fd8 <<< 60) ||| 0x3dd1659fd80dd16)) <<< 240) ||| ((((0x59ff805cf649ff8 <<< 60) ||| 0x35c364bbf845966) <<< 120) ||| ((0x49ff805ce649ff8 <<< 60) ||| 0x35c264bf7815d56))) <<< 480) ||| ((((((0x4bbf84595649fd8 <<< 60) ||| 0xdcd64ded75dc96) <<< 120) ||| ((0x4ded73dc964bed8 <<< 60) ||| 0xdc964ded85dc96)) <<< 240) ||| ((((0x4ded65dc964ded8 <<< 60) ||| 0x3dc964ded80dc96) <<< 120) ||| ((0x49fd83dc164def7 <<< 60) ||| 0x25c1649ff805cc6)))) <<< 1020) ||| ((((((((((0x4ddf855cc64ddd8 <<< 60) ||| 0x55cc64ddf805cc6) <<< 60) ||| 0x4ddd805cc649ff8) <<< 120) ||| ((0x35c064ded825c06 <<< 60) ||| 0x4df5815c064dfb8)) <<< 240) ||| ((((0x55c064df9855c06 <<< 60) ||| 0x4dfb835c064df98) <<< 120) ||| ((0x35c064ddd865ce5 <<< 60) ||| 0x49fd83dd9549fd8))) <<< 480) ||| ((((((0xdd9549ff845d95 <<< 60) ||| 0x4bef8259154df76) <<< 120) ||| ((0x4dc554df564dc55 <<< 60) ||| 0x49ff845d763bf78)) <<< 240) ||| ((((0x1553639ff845c36 <<< 60) ||| 0x39fd84dd563bdf8) <<< 120) ||| ((0x3595639fd80dd16 <<< 60) ||| 0x3afd869d163b7d8))))) <<< 2040) ||| ((((((((((((0x59d163dbf749d16 <<< 60) ||| 0x3aff865d163bef8) <<< 60) ||| 0x25d163dbd741d16) <<< 120) ||| ((0x3dbf7499163bdd8 <<< 60) ||| 0x399163dbf745916)) <<< 240) ||| ((((0x3bef82591639fe8 <<< 60) ||| 0x7951639fd879516) <<< 120) ||| ((0x3bdd8395163bf78 <<< 60) ||| 0x1551639fd84dc16))) <<< 480) ||| ((((((0x39fd84dd9539ff8 <<< 60) ||| 0x45d9539fd86dd15) <<< 120) ||| ((0x3d7d65dd153bef8 <<< 60) ||| 0x259153bdd831915)) <<< 240) ||| ((((0x3bed8219153bf58 <<< 60) ||| 0x119153bf9801915) <<< 120) ||| ((0x39ff87597439ff8 <<< 60) ||| 0x65c343dbd645c34)))) <<< 1020) ||| ((((((((((0x39fd80dd943cff7 <<< 60) ||| 0x69d943bbd849d94) <<< 60) ||| 0x3bbf845d943bef8) <<< 120) ||| ((0x25d943cff865d94 <<< 60) ||| 0x39ff845d943dbf8)) <<< 240) ||| ((((0x45d943def825d94 <<< 60) ||| 0x39ff805d9439fe8) <<< 120) ||| ((0x71d943cfd761d94 <<< 60) ||| 0x3b7d851d943bed8))) <<< 480) ||| ((((((0x21d943bf5811d94 <<< 60) ||| 0x3bf9801d9439fd8) <<< 120) ||| ((0x6dd543bf7815d54 <<< 60) ||| 0x39ff865d5439fe8)) <<< 240) ||| ((((0x7d95439fd87d954 <<< 60) ||| 0x3bbd84d9543bdd8) <<< 120) ||| ((0x3d9543bf581d954 <<< 60) ||| 0x39ff87595439fc8))))))) else (if j<4 then ((((((((((((((((0x60efd865 <<< 60) ||| 0xf60bfd84dd560b) <<< 60) ||| 0xff845d560bff845) <<< 120) ||| ((0x9560dfd75dd160e <<< 60) ||| 0xfd65dd160dfd85d)) <<< 240) ||| ((((0xd160dfd65dd160d <<< 60) ||| 0xff759d160dfd759) <<< 120) ||| ((0xd160efd659d160b <<< 60) ||| 0xfd839d160bff865))) <<< 540) ||| ((((((((0xd160eff865d160d <<< 60) ||| 0xff755d160dfd755) <<< 60) ||| 0xd160eff655d160e) <<< 120) ||| ((0xfd655d160bff835 <<< 60) ||| 0xd160fef825d160d)) <<< 240) ||| ((((0xfd751d160efd651 <<< 60) ||| 0xd160efd75d9160e) <<< 120) ||| ((0xfd74d9160bfd879 <<< 60) ||| 0x9160dff7599160e)))) <<< 1020) ||| ((((((((((0xfd6599160bfd839 <<< 60) ||| 0x9160dff7559160e) <<< 60) ||| 0xfd6559160efd855) <<< 120) ||| ((0x9160eff7559160e <<< 60) ||| 0xfd7559160eff745)) <<< 240) ||| ((((0x9160efd8359160b <<< 60) ||| 0xfd8795160bff875) <<< 120) ||| ((0x5160bff8655160d <<< 60) ||| 0xff7455160eff645))) <<< 480) ||| ((((((0x5160efd6455160b <<< 60) ||| 0xfd84dcd60dfe74d) <<< 120) ||| ((0xcd60dfd74dcd60e <<< 60) ||| 0xfd64dcd60dfe84d)) <<< 240) ||| ((((0xcd60dfd84dcd60d <<< 60) ||| 0xfe64dcd60dfd64d) <<< 120) ||| ((0xcd60dfe745cd60d <<< 60) ||| 0xfd745cd60efd645))))) <<< 2040) ||| ((((((((((((0xcd60efd74d8d60e <<< 60) ||| 0xfe6458d60efd645) <<< 60) ||| 0x8d60efe8458d60e) <<< 120) ||| ((0xfd8458d60efe745 <<< 60) ||| 0x8d60efd7458d60d)) <<< 240) ||| ((((0xff7454d60eff645 <<< 60) ||| 0x4d60efd6454d60b) <<< 120) ||| ((0xfd87d0d60fbd74d <<< 60) ||| 0xd60bff8750d60d))) <<< 480) ||| ((((((0xfe8750d60bfd875 <<< 60) ||| 0xd60dfd8750d60b) <<< 120) ||| ((0xff8650d60efe865 <<< 60) ||| 0xd60bfd8650d60e)) <<< 240) ||| ((((0xfd8650d60dff745 <<< 60) ||| 0xd60fbe7450d60f) <<< 120) ||| ((0xbd7450d60eff645 <<< 60) ||| 0xd60fbe6450d60e)))) <<< 1020) ||| ((((((((((0xfd6450d60fbd645 <<< 60) ||| 0xd60fdd7350d60f) <<< 60) ||| 0xdd6350d60ff9805) <<< 120) ||| ((0xd60dff74d9150b <<< 60) ||| 0xfd83d9150bfd869)) <<< 240) ||| ((((0x9150dff7699150d <<< 60) ||| 0xfd7699150f7d659) <<< 120) ||| ((0x9150bfd8399150d <<< 60) ||| 0xfe8759150dfd875))) <<< 480) ||| ((((((0x9150dff7659150d <<< 60) ||| 0xfd7659150f7d855) <<< 120) ||| ((0x9150f7d6559150d <<< 60) ||| 0xff7459150bff835)) <<< 240) ||| ((((0x9150fef8259150b <<< 60) ||| 0xfd8319150f7f645) <<< 120) ||| ((0x5150f7d6455150d <<< 60) ||| 0xff64dcd50dfe64d)))))) <<< 4080) ||| ((((((((((((((0xcd50dfd64dcd50d <<< 60) ||| 0xfc64dcd50bfd84d) <<< 60) ||| 0x8d50bff8458d50f) <<< 120) ||| ((0x7f6454d50f7e645 <<< 60) ||| 0x4d50f7d6454d50f)) <<< 240) ||| ((((0x7c6454d50bfd86d <<< 60) ||| 0xd50fbd64d0d50b) <<< 120) ||| ((0xff8650d50bfd865 <<< 60) ||| 0xd50fbe6450d50f))) <<< 480) ||| ((((((0xbd6450d50fdd635 <<< 60) ||| 0xd50dfd865cf40d) <<< 120) ||| ((0xfd8758f40fbd845 <<< 60) ||| 0x8f40dfd7654f40f)) <<< 240) ||| ((((0xbd6454f40fbd865 <<< 60) ||| 0xf40bfd83dd940d) <<< 120) ||| ((0xfd85dd940dfd83d <<< 60) ||| 0xd940bfd839d940b)))) <<< 1020) ||| ((((((((((0xff845d940fbf845 <<< 60) ||| 0xd940bff835d940f) <<< 60) ||| 0xef825d940dff865) <<< 120) ||| ((0xd940dff855d940d <<< 60) ||| 0xfd855d940dff845)) <<< 240) ||| ((((0xd940dff835d940d <<< 60) ||| 0xfd835d940bfd831) <<< 120) ||| ((0xd940bfd86dd540d <<< 60) ||| 0xfe76dd540dfd76d))) <<< 480) ||| ((((((0xd540bff865d540d <<< 60) ||| 0xff765d540dfe765) <<< 120) ||| ((0xd540dfd765d540d <<< 60) ||| 0xfc765d540bfd87d)) <<< 240) ||| ((((0x9540bff8759540d <<< 60) ||| 0xff7659540dfd765) <<< 120) ||| ((0x9540bff8459540b <<< 60) ||| 0xfd87d9140dff75d))))) <<< 2040) ||| ((((((((((((0x9140dfd75d9140b <<< 60) ||| 0xfd83d9140fbd769) <<< 60) ||| 0x9140fbd7599140f) <<< 120) ||| ((0xbd6599140dff755 <<< 60) ||| 0x9140dfd7559140f)) <<< 240) ||| ((((0xbf7659140fbd855 <<< 60) ||| 0x9140fbf7559140f) <<< 120) ||| ((0xbd7559140fbd655 <<< 60) ||| 0x9140fbd8359140f))) <<< 480) ||| ((((((0xbd7695140dff765 <<< 60) ||| 0x5140dfd7655140f) <<< 120) ||| ((0xbf6455140fbd645 <<< 60) ||| 0x5140fbf7655140f)) <<< 240) ||| ((((0xbe7655140fbd765 <<< 60) ||| 0x5140fbc7655140b) <<< 120) ||| ((0xfd86dcd40dfe76d <<< 60) ||| 0xcd40dfd76dcd40f)))) <<< 1020) ||| ((((((((((0xbd64dcd40dfe86d <<< 60) ||| 0xcd40dfd86dcd40d) <<< 60) ||| 0xff64dcd40dfd64d) <<< 120) ||| ((0xcd40bff865cd40d <<< 60) ||| 0xff765cd40dfe765)) <<< 240) ||| ((((0xcd40dfd765cd40d <<< 60) ||| 0xfc765cd40fbe645) <<< 120) ||| ((0xcd40fbd645cd40f <<< 60) ||| 0xfb805cd40bfd87d))) <<< 480) ||| ((((((0x8d40bff8758d40d <<< 60) ||| 0xfe8758d40bfd875) <<< 120) ||| ((0x8d40dfd8758d40d <<< 60) ||| 0xff7658d40dfd765)) <<< 240) ||| ((((0x8d40bff8458d40f <<< 60) ||| 0xbe8458d40fbd845) <<< 120) ||| ((0x8d40fbe6458d40f <<< 60) ||| 0xbd6458d40fdd735))))))) else ((((((((((((((((0x4a028904 <<< 60) ||| 0xec099c12e024903) <<< 60) ||| 0x2405fc11d022703) <<< 120) ||| ((0x4208400f881de03 <<< 60) ||| 0x9606d00d0819202)) <<< 240) ||| ((((0xfe05b00a8802602 <<< 60) ||| 0x8c0098099812002) <<< 120) ||| ((0x1203e801300e701 <<< 60) ||| 0xce036001300cd00))) <<< 540) ||| ((((((((0x4c009805b002600 <<< 60) ||| 0x26028c04c002601) <<< 60) ||| 0xa009803b006300) <<< 120) ||| ((0x8800c4013001300 <<< 60) ||| 0xdfd83dd165dfd)) <<< 240) ||| ((((0x80dd165dfd855cf <<< 60) ||| 0x64dfd845cf64dfd) <<< 120) ||| ((0x855c364dfd845c3 <<< 60) ||| 0x64bff8359664bff)))) <<< 1020) ||| ((((((((((0x8059664dfd865ce <<< 60) ||| 0x64dfd855ce64dfd) <<< 60) ||| 0x655ce64dfd805ce) <<< 120) ||| ((0x64dfd865c264dfd <<< 60) ||| 0x855c264dfd655c2)) <<< 240) ||| ((((0x64dfd835c264fbf <<< 60) ||| 0x845d564bff835d5) <<< 120) ||| ((0x64ff7815d564bff <<< 60) ||| 0x805d564bff83595))) <<< 480) ||| ((((((0x64bff8059564eff <<< 60) ||| 0x865cd64bff855cd) <<< 120) ||| ((0x64dfd755cd64fbf <<< 60) ||| 0x845cd64bff805cd)) <<< 240) ||| ((((0x64eff865c164bff <<< 60) ||| 0x855c164dfd755c1) <<< 120) ||| ((0x64fbf845c164bff <<< 60) ||| 0x835c164dfd735c1))))) <<< 2040) ||| ((((((((((((0x64dfd855cc64dfd <<< 60) ||| 0x855c064bfd83d91) <<< 60) ||| 0x54bfd80d9154dfd) <<< 120) ||| ((0x845c363bfd84dd5 <<< 60) ||| 0x63bff845d563bff)) <<< 240) ||| ((((0x8459563dfd75dd1 <<< 60) ||| 0x63efd65dd163dfd) <<< 120) ||| ((0x85dd163dfd65dd1 <<< 60) ||| 0x63dff759d163dfd))) <<< 480) ||| ((((((0x759d163efd659d1 <<< 60) ||| 0x63bfd809d163bff) <<< 120) ||| ((0x865d163eff865d1 <<< 60) ||| 0x63dff755d163dfd)) <<< 240) ||| ((((0x755d163eff655d1 <<< 60) ||| 0x63efd655d163fef) <<< 120) ||| ((0x825d163bff805d1 <<< 60) ||| 0x63dfd751d163efd)))) <<< 1020) ||| ((((((((((0x651d163bfd87991 <<< 60) ||| 0x63dff7599163efd) <<< 60) ||| 0x6599163bfd80991) <<< 120) ||| ((0x63dff7559163efd <<< 60) ||| 0x6559163bfd87951)) <<< 240) ||| ((((0x63bff8755163bff <<< 60) ||| 0x8655163dff74551) <<< 120) ||| ((0x63bfd84dc163dfe <<< 60) ||| 0x74dc163dfd74dc1))) <<< 480) ||| ((((((0x63dfe84dc163dfd <<< 60) ||| 0x84dc163dfe64dc1) <<< 120) ||| ((0x63dfd64dc163dfe <<< 60) ||| 0x745c163dfd745c1)) <<< 240) ||| ((((0x63dff74d9153bfd <<< 60) ||| 0x80d9153bfd86991) <<< 120) ||| ((0x53dff7699153dfd <<< 60) ||| 0x7699153f7d65991)))))) <<< 4080) ||| ((((((((((((((0x53bfd8099153dfe <<< 60) ||| 0x8759153dfd87591) <<< 60) ||| 0x53dff7659153dfd) <<< 120) ||| ((0x7659153f7d65591 <<< 60) ||| 0x53dff7459153fef)) <<< 240) ||| ((((0x8259153bff80591 <<< 60) ||| 0x53bfd8019153dff) <<< 120) ||| ((0x64dc153dfe64dc1 <<< 60) ||| 0x53dfd64dc153dfc))) <<< 480) ||| ((((((0x64dc153dfd865c3 <<< 60) ||| 0x43bfd80dd943dfd) <<< 120) ||| ((0x85dd943dfd80dd9 <<< 60) ||| 0x43bfd809d943bff)) <<< 240) ||| ((((0x845d943fbf845d9 <<< 60) ||| 0x43fef825d943bff) <<< 120) ||| ((0x805d943dff865d9 <<< 60) ||| 0x43dff855d943dfd)))) <<< 1020) ||| ((((((((((0x855d943dff845d9 <<< 60) ||| 0x43dff805d943dfd) <<< 60) ||| 0x805d943bfd801d9) <<< 120) ||| ((0x43bfd86dd543dfe <<< 60) ||| 0x76dd543dfd76dd5)) <<< 240) ||| ((((0x43bff865d543dff <<< 60) ||| 0x765d543dfe765d5) <<< 120) ||| ((0x43dfd765d543dfc <<< 60) ||| 0x765d543bfd87d95))) <<< 480) ||| ((((((0x43bff8759543dff <<< 60) ||| 0x7659543dfd76595) <<< 120) ||| ((0x43bff8459543bfd <<< 60) ||| 0x87d9143dff75d91)) <<< 240) ||| ((((0x43dfd75d9143bfd <<< 60) ||| 0x80d9143fbd76991) <<< 120) ||| ((0x43fbd7599143fbd <<< 60) ||| 0x6599143dff75591))))) <<< 2040) ||| ((((((((((((0x43dfd7559143fbf <<< 60) ||| 0x7659143fbd85591) <<< 60) ||| 0x43fbf7559143fbd) <<< 120) ||| ((0x7559143fbd65591 <<< 60) ||| 0x43fbd8059143fbd)) <<< 240) ||| ((((0x7695143dff76551 <<< 60) ||| 0x43dfd7655143fbf) <<< 120) ||| ((0x6455143fbd64551 <<< 60) ||| 0x43fbf7655143fbe))) <<< 480) ||| ((((((0x7655143fbd76551 <<< 60) ||| 0x43fbc7655143fdc) <<< 120) ||| ((0x8758d43fdf7658d <<< 60) ||| 0x43fdf8558d43fdd)) <<< 240) ||| ((((0x8558d43fdf7558d <<< 60) ||| 0x43fdd7558d43fdd) <<< 120) ||| ((0x6558d43fdf8458d <<< 60) ||| 0x43fdd8458d43fdd)))) <<< 1020) ||| ((((((((((0x5458d43fdf8058d <<< 60) ||| 0x43fdd8058d43bfd) <<< 60) ||| 0x86dc143dfe76dc1) <<< 120) ||| ((0x43dfd76dc143fbd <<< 60) ||| 0x64dc143fdd63dc1)) <<< 240) ||| ((((0x43dfe86dc143dfd <<< 60) ||| 0x86dc143dff64dc1) <<< 120) ||| ((0x43dfd64dc143bff <<< 60) ||| 0x865c143dff765c1))) <<< 480) ||| ((((((0x43dfe765c143dfd <<< 60) ||| 0x765c143dfc765c1) <<< 120) ||| ((0x43fbe645c143fbd <<< 60) ||| 0x645c143fdf835c1)) <<< 240) ||| ((((0x43fdd635c143dfd <<< 60) ||| 0x845cf60efd8458f) <<< 120) ||| ((0x60dfd7454f60efd <<< 60) ||| 0x6454f60dfd8750f)))))))))) else (if j<7 then (if j<6 then ((((((((((((((((0x5d27ab0f <<< 60) ||| 0x4a9e823c562070f) <<< 60) ||| 0x339e583c8a78d8f) <<< 120) ||| ((0x159e140e647824e <<< 60) ||| 0xff1df33bc04ed80)) <<< 240) ||| ((((0x131dd13b8473cce <<< 60) ||| 0xd79ae23b4876444) <<< 120) ||| ((0xbd9d823aee4f044 <<< 60) ||| 0xbd9d683aaa7454e))) <<< 540) ||| ((((((((0xa31d333a487454e <<< 60) ||| 0x811cf3278273801) <<< 60) ||| 0xef9cd138527308e) <<< 120) ||| ((0x5b9cb0393a7228e <<< 60) ||| 0x3f9c7038ca71589)) <<< 240) ||| ((((0xe09c4307be70e0e <<< 60) ||| 0x149c16370e701cd) <<< 120) ||| ((0xfe1be937b46f2cd <<< 60) ||| 0xde1ba9372c0a8cd)))) <<< 1020) ||| ((((((((((0xc39b78019a6d94d <<< 60) ||| 0xab1b4305286cc0d) <<< 60) ||| 0x8e94360d066c48d) <<< 120) ||| ((0x7f897b35e86ba4d <<< 60) ||| 0x711ad30d426b102)) <<< 240) ||| ((((0xf99aad35346a0cd <<< 60) ||| 0x341a59348c68ccc) <<< 120) ||| ((0x561a28342a6808c <<< 60) ||| 0xf599d8339266e8c))) <<< 480) ||| ((((((0xd3999432fa6598c <<< 60) ||| 0xa7994431f064b4c) <<< 120) ||| ((0x67191627dc641cc <<< 60) ||| 0x8398f831c263381)) <<< 240) ||| ((((0x2e0026004c0970c <<< 60) ||| 0x5d98ac315809701) <<< 120) ||| ((0x2e107931323eb05 <<< 60) ||| 0xae188204b84f04c))))) <<< 2040) ||| ((((((((((((0x35838f30b04f04c <<< 60) ||| 0x2093b6305c09701) <<< 60) ||| 0x2e025c0528602c9) <<< 120) ||| ((0x10169524405ff0b <<< 60) ||| 0xf091c52f765f38b)) <<< 240) ||| ((((0xdd825c1d4c39f05 <<< 60) ||| 0x87960c2f405e14b) <<< 120) ||| ((0xb9176312125d50b <<< 60) ||| 0x9e97162e065bd01))) <<< 480) ||| ((((((0x2e16e12d9c5aecb <<< 60) ||| 0x5200262d2a09701) <<< 120) ||| ((0x2e025c04b809707 <<< 60) ||| 0xdb8fac052859e8b)) <<< 240) ||| ((((0x20966316b859305 <<< 60) ||| 0xa096412c5c586cb) <<< 120) ||| ((0x615fd2bd4576c3 <<< 60) ||| 0x508ef32b9056d4a)))) <<< 1020) ||| ((((((((((0x97959e2b0e55e0a <<< 60) ||| 0xae95462a5e30b8a) <<< 60) ||| 0x8814f1228e5358a) <<< 120) ||| ((0x5f825c04b809704 <<< 60) ||| 0x84933023183a2ca)) <<< 240) ||| ((((0x5408b129222268a <<< 60) ||| 0x3d146728a85114a) <<< 120) ||| ((0x1b0fac28462d709 <<< 60) ||| 0xe613c128200b409))) <<< 480) ||| ((((((0x9813fd27dc4fb89 <<< 60) ||| 0xf713df26604f309) <<< 120) ||| ((0xe09021276c0db49 <<< 60) ||| 0xd193901e1a3c081)) <<< 240) ||| ((((0x2e025c04b809701 <<< 60) ||| 0x51829426d24bcc9) <<< 120) ||| ((0xa9133f26604c749 <<< 60) ||| 0x8e8909260c39f01)))))) <<< 4080) ||| ((((((((((((((0x2e12f325c04b349 <<< 60) ||| 0x59129724f849649) <<< 60) ||| 0x2112201f8448cc9) <<< 120) ||| ((0x10121123f4479c8 <<< 60) ||| 0xf391d4238a00980)) <<< 240) ||| ((((0xc911b6234609708 <<< 60) ||| 0xc61115121245c48) <<< 120) ||| ((0xad1147225844548 <<< 60) ||| 0x7d10e321b043148))) <<< 480) ||| ((((((0x57109b212041e48 <<< 60) ||| 0x351047206025088) <<< 120) ||| ((0x108cf5201c3fec7 <<< 60) ||| 0xf40fd5004c3f081)) <<< 240) ||| ((((0x2e025c05461cc83 <<< 60) ||| 0x990fb71f583e447) <<< 120) ||| ((0xa68f8212123dcc7 <<< 60) ||| 0xac0f4d1e743cac7)))) <<< 1020) ||| ((((((((((0x8e0f0d1e040d783 <<< 60) ||| 0x508ef31db038087) <<< 60) ||| 0x5e8ea61d1639f07) <<< 120) ||| ((0x348e521c7e38a07 <<< 60) ||| 0xa8e021bce37506)) <<< 240) ||| ((((0xe08da61b1635b06 <<< 60) ||| 0xa68d3a1a2e34106) <<< 120) ||| ((0x7a8cda188a330c6 <<< 60) ||| 0x580c99190c31cc6))) <<< 480) ||| ((((((0x2e0c5c188a30b86 <<< 60) ||| 0xb8c0017d22f485) <<< 120) ||| ((0xd78b5c17382e345 <<< 60) ||| 0xbd0b6f13e82d704)) <<< 240) ||| ((((0xe909d216822c985 <<< 60) ||| 0x878af415b22b285) <<< 120) ||| ((0x5b8a8d15482a905 <<< 60) ||| 0x4689d214f426c05))))) <<< 2040) ||| ((((((((((((0x338a50147228784 <<< 60) ||| 0xff89f413c227484) <<< 60) ||| 0xdd89b0133225ec4) <<< 120) ||| ((0xc3097b07be25a04 <<< 60) ||| 0xaa825c125e25084)) <<< 240) ||| ((((0x84892f123809704 <<< 60) ||| 0x8488f611b623104) <<< 120) ||| ((0x58889a110e21b04 <<< 60) ||| 0x2e884a105e20703))) <<< 480) ||| ((((((0xfe87da0f8e1b683 <<< 60) ||| 0xd807990efc1dac3) <<< 120) ||| ((0xaa07410e641c6c3 <<< 60) ||| 0x8006e90db41b0c3)) <<< 240) ||| ((((0x50802604b800983 <<< 60) ||| 0x5806a10d241a0c3) <<< 120) ||| ((0xa86700cca19483 <<< 60) ||| 0x1d814604b818a03)))) <<< 1020) ||| ((((((((((0xa86020be617cc2 <<< 60) ||| 0xf005c50b6c167c2) <<< 60) ||| 0xc405710ab4150c2) <<< 120) ||| ((0x96051d0a1413bc2 <<< 60) ||| 0x6804b10944122c2)) <<< 240) ||| ((((0x3a046500c611382 <<< 60) ||| 0x1b842008120fb81) <<< 120) ||| ((0xef8013079809701 <<< 60) ||| 0xd882ae01b009701))) <<< 480) ||| ((((((0x2e03a2071e0e3c0 <<< 60) ||| 0x1302d0004c0e001) <<< 120) ||| ((0xb6825c05a000981 <<< 60) ||| 0xaf035e066e0c601)) <<< 240) ||| ((((0x84823a05ec0a8c1 <<< 60) ||| 0x5182e304740b8c1) <<< 120) ||| ((0x6802bd05460af41 <<< 60) ||| 0x5e82ae04b80a8c1))))))) else ((((((((((((((((0xa0e06080 <<< 60) ||| 0x40002301040087d) <<< 60) ||| 0xbdc040025336f67) <<< 120) ||| ((0x2b2000dcc04021e <<< 60) ||| 0x772e2000955cc02)) <<< 240) ||| ((((0x1e2016680080e00 <<< 60) ||| 0x21858500c6f2f3) <<< 120) ||| ((0x7642001201d8100 <<< 60) ||| 0x807cc0238473008))) <<< 540) ||| ((((((((0x636881e00222038 <<< 60) ||| 0x1000989cb9a0020) <<< 60) ||| 0x181668008040600) <<< 120) ||| ((0x180800404000218 <<< 60) ||| 0x900041006020020)) <<< 240) ||| ((((0x428008600021020 <<< 60) ||| 0x1008009ca060018) <<< 120) ||| ((0xf2818008081006 <<< 60) ||| 0x2002f604024801)))) <<< 1020) ||| ((((((((((0x80800f080fca002 <<< 60) ||| 0x634272800803080) <<< 60) ||| 0xe0400280f2c2000) <<< 120) ||| ((0x81000021c832800 <<< 60) ||| 0x88040802002764)) <<< 240) ||| ((((0x8728082000c0604 <<< 60) ||| 0x103800081080e00) <<< 120) ||| ((0x8804268e2668100 <<< 60) ||| 0xb9a06041e68501))) <<< 480) ||| ((((((0x810814060418081 <<< 60) ||| 0x4081007cc022f3) <<< 120) ||| ((0x250100881004173 <<< 60) ||| 0x40100881404021)) <<< 240) ||| ((((0xc203800108031bc <<< 60) ||| 0xd09220004384038) <<< 120) ||| ((0x880402103800 <<< 60) ||| 0x20109cc08040221))))) <<< 2040) ||| ((((((((((((0xf583eb125f262e4 <<< 60) ||| 0x97c85987db8fb72) <<< 60) ||| 0xde8aba556b2ac02) <<< 120) ||| ((0x42ab2d1792ac05 <<< 60) ||| 0x562aa89055aa8b1)) <<< 240) ||| ((((0xf6ea9f0b20a14c5 <<< 60) ||| 0x4caa8c15270f4d4) <<< 120) ||| ((0x298a8ed5182a215 <<< 60) ||| 0x42405194ff86a10))) <<< 480) ||| ((((((0xd42a7d14f0a9ce5 <<< 60) ||| 0x376a6d04e919445) <<< 120) ||| ((0x34a25ed4cb298b4 <<< 60) ||| 0x16c4ed8b7a1c295)) <<< 240) ||| ((((0x2f094914bc24f35 <<< 60) ||| 0x2caa5794a7a93c0) <<< 120) ||| ((0x324a4b505b291a4 <<< 60) ||| 0xa5e0a8c01300264)))) <<< 1020) ||| ((((((((((0x286160ee129033 <<< 60) ||| 0xb8473cc9e09c435) <<< 60) ||| 0x1e06c75179097b3) <<< 120) ||| ((0x5e8a37546723050 <<< 60) ||| 0x7be8b8d16628ac5)) <<< 240) ||| ((((0x158a2ed45620325 <<< 60) ||| 0x13aa2084bd897b5) <<< 120) ||| ((0xeea1dc7a6a8685 <<< 60) ||| 0xba8d2505b16415))) <<< 480) ||| ((((((0x9480c941ba18f4 <<< 60) ||| 0x29884d50cf28204) <<< 120) ||| ((0x226a0353fd27f34 <<< 60) ||| 0xfc8835d3eca0143)) <<< 240) ||| ((((0x1589f2812e1f384 <<< 60) ||| 0xf769ea0f9c16f40) <<< 120) ||| ((0xe649e5505b218f4 <<< 60) ||| 0x1569e093b99e452)))))) <<< 4080) ||| ((((((((((((((0xc829d713a8a73e4 <<< 60) ||| 0xe569c61384a6fa4) <<< 60) ||| 0x4603353759ebf4) <<< 120) ||| ((0xdc09b3535f26ab4 <<< 60) ||| 0xd409a4533d26674)) <<< 240) ||| ((((0xca89904d71262e4 <<< 60) ||| 0x467824eff239f4) <<< 120) ||| ((0xc1a987d2f9a6144 <<< 60) ||| 0xc1a980930125f34))) <<< 480) ||| ((((((0xbc89754d749fab3 <<< 60) ||| 0xf389718d74a5bb4) <<< 120) ||| ((0xb5096652cc9af43 <<< 60) ||| 0xe707dcd0c7a5824)) <<< 240) ||| ((((0xae69580ca209d23 <<< 60) ||| 0x2881a8501925514) <<< 120) ||| ((0xa7c82d89db10214 <<< 60) ||| 0xa5e9435292250d4)))) <<< 1020) ||| ((((((((((0x9fc93cd27024c94 <<< 60) ||| 0x97c92bcd6987324) <<< 60) ||| 0x93882d9244a4764) <<< 120) ||| ((0x8c64f0522a13b64 <<< 60) ||| 0x87a0a8cf9c025c4)) <<< 240) ||| ((((0x280a50c56242a4 <<< 60) ||| 0x812907d1c0a4093) <<< 120) ||| ((0x7f84f0520813c13 <<< 60) ||| 0x63a90251ff23903))) <<< 480) ||| ((((((0x5fe54bd1f3a3904 <<< 60) ||| 0x7a825ecf9c1f381) <<< 120) ||| ((0xe9a3e08fb81f704 <<< 60) ||| 0x78a4fb8d74a3904)) <<< 240) ||| ((((0x7648e7cd74a3904 <<< 60) ||| 0x702863d0c7a3724) <<< 120) ||| ((0x6c677f91aa23494 <<< 60) ||| 0x66c25ed193a3144))))) <<< 2040) ||| ((((((((((((0x60a8bc90fe22e34 <<< 60) ||| 0x5988af5151228f4) <<< 60) ||| 0x4f87915136a25e4) <<< 120) ||| ((0x48e88e1011a2291 <<< 60) ||| 0x2f6887910f220f1)) <<< 240) ||| ((((0x2f66f2d0fe21ed4 <<< 60) ||| 0x3ac0f7c013097b4) <<< 120) ||| ((0x39686f10d683df2 <<< 60) ||| 0xc8286790c79af43))) <<< 480) ||| ((((((0xe705bd10c021751 <<< 60) ||| 0x6de82d87a6a1664) <<< 120) ||| ((0x2b680c87c1214c4 <<< 60) ||| 0x26a7d8509321134)) <<< 240) ||| ((((0x20883c4fb820e64 <<< 60) ||| 0x1ae833039918ac0) <<< 120) ||| ((0xd420a8cf9c20144 <<< 60) ||| 0x460a50810a0c13)))) <<< 1020) ||| ((((((((((0xc8a82d87c120ab4 <<< 60) ||| 0x1308214f228f4d4) <<< 60) ||| 0xdc7f9d02fa0504) <<< 120) ||| ((0x7a80c828520234 <<< 60) ||| 0x4662b067aa0144)) <<< 240) ||| ((((0x27fb8f891f701 <<< 60) ||| 0xf047f9cff390902) <<< 120) ||| ((0x1207f60fe49fba3 <<< 60) ||| 0x5d27eacfce1f8d3))) <<< 480) ||| ((((((0x5d27e08fb99f703 <<< 60) ||| 0xee04fb8fb09ae93) <<< 120) ||| ((0xe9c6ba44e913c12 <<< 60) ||| 0x76c7cfc5b7897b3)) <<< 240) ||| ((((0x5e80098f9c10213 <<< 60) ||| 0xe4a7c48f7f9eec3) <<< 120) ||| ((0x5d27b74f671ebf3 <<< 60) ||| 0x5d27ab0f4a8cf53)))))))) else (if j<8 then ((((((((((((((((0x38180080 <<< 60) ||| 0x400061808381860) <<< 60) ||| 0x6039a0020001840) <<< 120) ||| ((0x600176018009881 <<< 60) ||| 0x40600262767303f)) <<< 240) ||| ((((0x281808001421211 <<< 60) ||| 0x140002062c50000) <<< 120) ||| ((0x81880200061f300 <<< 60) ||| 0x8001880e0403080))) <<< 540) ||| ((((((((0x28180c200080e0 <<< 60) ||| 0x2080020100c2048) <<< 60) ||| 0x9d9ca0002040637) <<< 120) ||| ((0x28a800081018dcc <<< 60) ||| 0x120602010837372)) <<< 240) ||| ((((0x848180f60042101 <<< 60) ||| 0x200020608280040) <<< 120) ||| ((0x86040200102008 <<< 60) ||| 0x40788058a019a)))) <<< 1020) ||| ((((((((((0x2e6819501099a54 <<< 60) ||| 0x604201950107cd) <<< 60) ||| 0x54021f355040088) <<< 120) ||| ((0x4020108122a584 <<< 60) ||| 0x808142000c12040)) <<< 240) ||| ((((0x2080028000c2048 <<< 60) ||| 0x916120602010830) <<< 120) ||| ((0x48100c2000a1206 <<< 60) ||| 0x40208003038000))) <<< 480) ||| ((((((0x81220a002810380 <<< 60) ||| 0xe68009d80e02000) <<< 120) ||| ((0x62e6f2e20008000 <<< 60) ||| 0xe101810080098a0)) <<< 240) ||| ((((0x600261f603f2818 <<< 60) ||| 0x8122119b89ca) <<< 120) ||| ((0xcc00281838007ca <<< 60) ||| 0x6000e272818380))))) <<< 2040) ||| ((((((((((((0x80e06040025289 <<< 60) ||| 0x800088102c00022) <<< 60) ||| 0x87841e0214583) <<< 120) ||| ((0x80e689000c0e060 <<< 60) ||| 0x180e68006120e0)) <<< 240) ||| ((((0x2048830380059 <<< 60) ||| 0xa05880027600038) <<< 120) ||| ((0x6160e00180a2000 <<< 60) ||| 0x79a001018100860))) <<< 480) ||| ((((((0x60e000205083760 <<< 60) ||| 0x380f300420c0403) <<< 120) ||| ((0x8000e2f3018081 <<< 60) ||| 0x42000c030800181)) <<< 240) ||| ((((0x80820009d800020 <<< 60) ||| 0x4062c2010083880) <<< 120) ||| ((0x40002280628380c <<< 60) ||| 0x200090800020e24)))) <<< 1020) ||| ((((((((((0x5838180c2000c12 <<< 60) ||| 0x4020e203810084) <<< 60) ||| 0x89d812060201083) <<< 120) ||| ((0x7673018080420dd <<< 60) ||| 0x80fca060201083f)) <<< 240) ||| ((((0x67372818080420f <<< 60) ||| 0xd804020e2760583) <<< 120) ||| ((0x818100800211cbd <<< 60) ||| 0x802122000083860))) <<< 480) ||| ((((((0x9ca0602000e3038 <<< 60) ||| 0x50032808bd80200) <<< 120) ||| ((0x6202038080018a <<< 60) ||| 0xe031a0020180c6)) <<< 240) ||| ((((0x80091bca0308002 <<< 60) ||| 0x83840180008a060) <<< 120) ||| ((0x400ca0228381800 <<< 60) ||| 0x820a0e06020800)))))) <<< 4080) ||| ((((((((((((((0x283800081820a0e <<< 60) ||| 0x6080200285f284) <<< 60) ||| 0x81f600800211d81) <<< 120) ||| ((0x206276008187c <<< 60) ||| 0xc02050820083840)) <<< 240) ||| ((((0x2040620384800 <<< 60) ||| 0x81220c0e120206) <<< 120) ||| ((0x568830480008122 <<< 60) ||| 0xbcc06020088043))) <<< 480) ||| ((((((0x761580f300220c0 <<< 60) ||| 0x401881810095818) <<< 120) ||| ((0x800045606200008 <<< 60) ||| 0x115818a0e020008)) <<< 240) ||| ((((0x2048000c209cc06 <<< 60) ||| 0x308280018081) <<< 120) ||| ((0x20a12060204570 <<< 60) ||| 0x830076158081734)))) <<< 1020) ||| ((((((((((0x20e120210482000 <<< 60) ||| 0x8800020618000f) <<< 60) ||| 0x301c20a06021047) <<< 120) ||| ((0x30095018a120600 <<< 60) ||| 0x22040084040206)) <<< 240) ||| ((((0x200f280098804 <<< 60) ||| 0x2000e200812200) <<< 120) ||| ((0x80204060020100 <<< 60) ||| 0x800188040308002))) <<< 480) ||| ((((((0x8018100c2000c0 <<< 60) ||| 0x6040308002f280c) <<< 120) ||| ((0x200080604020800 <<< 60) ||| 0x2b2800980880810)) <<< 240) ||| ((((0xcb20023328080 <<< 60) ||| 0x7ca02000626301) <<< 120) ||| ((0x80f2c2000cca060 <<< 60) ||| 0x2202767280098))))) <<< 2040) ||| ((((((((((((0x818f21d8081001 <<< 60) ||| 0x8c0206404008180) <<< 60) ||| 0x80807ca02002c2) <<< 120) ||| ((0x728080038b8c0e0 <<< 60) ||| 0x3cb080033280038)) <<< 240) ||| ((((0x881000cb200228 <<< 60) ||| 0x3b2800088040200) <<< 120) ||| ((0x180010200838b20 <<< 60) ||| 0x804000e0230203))) <<< 480) ||| ((((((0x8100800b2010021 <<< 60) ||| 0x8380f282000a020) <<< 120) ||| ((0x122042000100860 <<< 60) ||| 0x20428180010a060)) <<< 240) ||| ((((0x39a040022201040 <<< 60) ||| 0x4028800268e2016) <<< 120) ||| ((0x6800a0205080020 <<< 60) ||| 0x10000818811cc02)))) <<< 1020) ||| ((((((((((0x62014200060002 <<< 60) ||| 0x50827301808001) <<< 60) ||| 0x420c070804180f3) <<< 120) ||| ((0x100420a0602040 <<< 60) ||| 0x82840180a5010)) <<< 240) ||| ((((0xb08109402042f30 <<< 60) ||| 0x40125008a9405cc) <<< 120) ||| ((0x10022a501008604 <<< 60) ||| 0x228248838100))) <<< 480) ||| ((((((0xc2000d1bcc0e032 <<< 60) ||| 0x204003888180820) <<< 120) ||| ((0x10a0e000e021a <<< 60) ||| 0x6040001008a220e)) <<< 240) ||| ((((0x402283810087 <<< 60) ||| 0x1a0f08000428100) <<< 120) ||| ((0x820a0a0e00080 <<< 60) ||| 0x402283820100800))))))) else (if j<9 then ((((((((((((((((0x2cc00133 <<< 60) ||| 0x48042018acc0e0) <<< 60) ||| 0x108215848006561) <<< 120) ||| ((0x201082420180048 <<< 60) ||| 0x81200061c200018)) <<< 240) ||| ((((0x6130800181c2000 <<< 60) ||| 0x608060018084841) <<< 120) ||| ((0x402201008b0 <<< 60) ||| 0x654001002204008))) <<< 540) ||| ((((((((0x486040010022000 <<< 60) ||| 0xf307cc88100400) <<< 60) ||| 0x2808b00074c8810) <<< 120) ||| ((0x540200373220100 <<< 60) ||| 0x94c548a0022204)) <<< 240) ||| ((((0x878a04001e684 <<< 60) ||| 0x181008a1002041) <<< 120) ||| ((0xb50400862c02142 <<< 60) ||| 0x8b06121004022)))) <<< 1020) ||| ((((((((((0x42008906cc06041 <<< 60) ||| 0x22808b0412040) <<< 60) ||| 0x21c262808696120) <<< 120) ||| ((0x184818006120e8 <<< 60) ||| 0x81810a040e26001)) <<< 240) ||| ((((0x81a205cc02ca1a2 <<< 60) ||| 0xf332800bcc068) <<< 120) ||| ((0x81a200730188008 <<< 60) ||| 0x80e1838180d2881))) <<< 480) ||| ((((((0xe041040100061e2 <<< 60) ||| 0x810166840088100) <<< 120) ||| ((0x10404001e02201 <<< 60) ||| 0x2203881fcc04a)) <<< 240) ||| ((((0x281040006021 <<< 60) ||| 0xe001f301a800080) <<< 120) ||| ((0x400100008106000 <<< 60) ||| 0x34a1d2800081080))))) <<< 2040) ||| ((((((((((((0x600040220382000 <<< 60) ||| 0xf081848042060e0) <<< 60) ||| 0x7081a5804206109) <<< 120) ||| ((0x6021848183860e0 <<< 60) ||| 0x810181000602583)) <<< 240) ||| ((((0x8006960e0108242 <<< 60) ||| 0x18006020848180) <<< 120) ||| ((0x42090806000e203 <<< 60) ||| 0x818042080604010))) <<< 480) ||| ((((((0x8205804206080e0 <<< 60) ||| 0x18000848616060) <<< 120) ||| ((0x108204018005808 <<< 60) ||| 0xa0e062000207820)) <<< 240) ||| ((((0x44500800cca0402 <<< 60) ||| 0x184008100081e02) <<< 120) ||| ((0x1c680051a960e <<< 60) ||| 0x60028201840206)))) <<< 1020) ||| ((((((((((0x102038516120800 <<< 60) ||| 0x202048006100206) <<< 60) ||| 0x183848042085606) <<< 120) ||| ((0x104001580885600 <<< 60) ||| 0x881800e0401cc06)) <<< 240) ||| ((((0x1d3220001888856 <<< 60) ||| 0x1f30180220857) <<< 120) ||| ((0x88001d304008610 <<< 60) ||| 0x60308233000186))) <<< 480) ||| ((((((0xcc0601082040100 <<< 60) ||| 0x860424021c20485) <<< 120) ||| ((0x80958180420810 <<< 60) ||| 0x65602215c20400)) <<< 240) ||| ((((0x5708181c204cc02 <<< 60) ||| 0x1b3420180094a) <<< 120) ||| ((0x2101008906cc04 <<< 60) ||| 0x100222804008600)))))) <<< 4080) ||| ((((((((((((((0x261280400838804 <<< 60) ||| 0xe1818400860e) <<< 60) ||| 0x10021a842040088) <<< 120) ||| ((0xa00610022280180 <<< 60) ||| 0x6a200041a27301)) <<< 240) ||| ((((0x800828040018c84 <<< 60) ||| 0x100880e1002062) <<< 120) ||| ((0x33420001880e061 <<< 60) ||| 0x3301c2000802241))) <<< 480) ||| ((((((0x420400081a800 <<< 60) ||| 0x6040108187e289) <<< 120) ||| ((0x8a10001e022 <<< 60) ||| 0x45000081018bcb1)) <<< 240) ||| ((((0x400020406301000 <<< 60) ||| 0x786040248122120) <<< 120) ||| ((0x10083881e001010 <<< 60) ||| 0x920008ca04c800)))) <<< 1020) ||| ((((((((((0x209373201000ac9 <<< 60) ||| 0xcada00232b20006) <<< 60) ||| 0xc8ca001b7013200) <<< 120) ||| ((0x8dbcac80027300 <<< 60) ||| 0x8112000a615b480)) <<< 240) ||| ((((0x4002b68100c5818 <<< 60) ||| 0xa04061368001048) <<< 120) ||| ((0x18adc0002040628 <<< 60) ||| 0x101860714041b))) <<< 480) ||| ((((((0x7038001018a0005 <<< 60) ||| 0x160627762000108) <<< 120) ||| ((0x204001d2848000 <<< 60) ||| 0x899c560602002f6)) <<< 240) ||| ((((0x18000848a56120 <<< 60) ||| 0x6215818481000) <<< 120) ||| ((0xb9c058800276730 <<< 60) ||| 0x481808001421000))))) <<< 2040) ||| ((((((((((((0x2101f66762e200 <<< 60) ||| 0x10d9c540604267) <<< 60) ||| 0x1950109cc13ca0) <<< 120) ||| ((0x39c0037604f2808 <<< 60) ||| 0x18d9d89ca0027)) <<< 240) ||| ((((0x6000487cc00061e <<< 60) ||| 0x76225f2800bd9cc) <<< 120) ||| ((0x13ca06020004884 <<< 60) ||| 0x810080048806120))) <<< 480) ||| ((((((0x181f2848008061 <<< 60) ||| 0x20400201f280048) <<< 120) ||| ((0x8074a0400022890 <<< 60) ||| 0x86139d160402)) <<< 240) ||| ((((0x345848181000a <<< 60) ||| 0x1604039c0028480) <<< 120) ||| ((0x59d88040027280 <<< 60) ||| 0x760489ca12001f2)))) <<< 1020) ||| ((((((((((0xe70007ca0288002 <<< 60) ||| 0x4800087d802001) <<< 60) ||| 0x220180800488121) <<< 120) ||| ((0x400ca022f672808 <<< 60) ||| 0x18a0212061a58)) <<< 240) ||| ((((0x1808147000dcd08 <<< 60) ||| 0x40200284840180) <<< 120) ||| ((0x8bd8120600020 <<< 60) ||| 0x4083f3018480800))) <<< 480) ||| ((((((0x1420fd803cc1201 <<< 60) ||| 0x8304818000820b) <<< 120) ||| ((0xcc06020108284f2 <<< 60) ||| 0x80c2000a1206020)) <<< 240) ||| ((((0x800281730081894 <<< 60) ||| 0xa0e000226573008) <<< 120) ||| ((0x606000218781800 <<< 60) ||| 0x880600020e2158))))))) else ((((((((((((0xa8104120410022 <<< 60) ||| 0xa01040e1210173) <<< 120) ||| ((0x7cc1edc187f3 <<< 60) ||| 0x81000a00021e1)) <<< 240) ||| ((((0x92258000810a120 <<< 60) ||| 0x601cc4829800810) <<< 120) ||| ((0x9cc0017301920 <<< 60) ||| 0x7cc00481c501808))) <<< 420) ||| ((((((0x108260010480800 <<< 60) ||| 0x1881e00034a2078) <<< 120) ||| ((0x180d28804081008 <<< 60) ||| 0x1860002ca180b28)) <<< 180) ||| ((((0x54c0002ca215848 <<< 60) ||| 0x22091408532808) <<< 60) ||| 0x656120600201008))) <<< 900) ||| ((((((((0x406880002242334 <<< 60) ||| 0x20381800a100002) <<< 120) ||| ((0x62041500800810 <<< 60) ||| 0x2001d322150008)) <<< 240) ||| ((((0x224001a2008907 <<< 60) ||| 0x9c1054060204309) <<< 120) ||| ((0x840e12881810a <<< 60) ||| 0x85cc12060020181))) <<< 420) ||| ((((((0x22081207cc008 <<< 60) ||| 0x828122000488120) <<< 120) ||| ((0x6034a252821e054 <<< 60) ||| 0xa1878a842a04021)) <<< 180) ||| ((((0x8480d2870800020 <<< 60) ||| 0x4204010080081e0) <<< 60) ||| 0x412022000167061)))) <<< 1740) ||| ((((((((((0xe05cc88002b2848 <<< 60) ||| 0x4ca041000222328) <<< 120) ||| ((0x7808807cc880024 <<< 60) ||| 0x201000604022a18)) <<< 240) ||| ((((0x800106034a1010 <<< 60) ||| 0xd2894a040218) <<< 120) ||| ((0x4818080091c0010 <<< 60) ||| 0x1b280861ecb1410))) <<< 420) ||| ((((((0x2b28100008810 <<< 60) ||| 0x20004207808100) <<< 120) ||| ((0x896120600201c2 <<< 60) ||| 0x48608121048200)) <<< 180) ||| ((((0x121004204860e01 <<< 60) ||| 0x818481c2060e06) <<< 60) ||| 0x121848204960e08))) <<< 840) ||| ((((((((0x2330180060f4a <<< 60) ||| 0x206287840006) <<< 120) ||| ((0x6001f4a20480b2 <<< 60) ||| 0x860e0002ca25301)) <<< 180) ||| ((((0x74c001532200 <<< 60) ||| 0xb28a0e0088195) <<< 60) ||| 0x800514066e02205)) <<< 420) ||| ((((((0x1b81808a1e061 <<< 60) ||| 0x98380060e00ca0) <<< 120) ||| ((0x2201098066894c8 <<< 60) ||| 0x8ca002730128000)) <<< 180) ||| ((((0x88800101f30481a <<< 60) ||| 0x8000b080e002620) <<< 60) ||| 0x489840108261818)))))))))
def g127H8 (j : Nat) : Nat := (if j<7 then (if j<3 then (if j<1 then ((((((((((((((((0xbdc00000 <<< 60) ||| 0x38cf4) <<< 60) ||| 0x0) <<< 120) ||| ((0x142a000 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x28cd800000002c))) <<< 540) ||| ((((((((0xf948572c4900000 <<< 60) ||| 0x0) <<< 60) ||| 0x34e0c0000000000) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x14d7 <<< 60) ||| 0xc00000000000000) <<< 120) ||| ((0x1c12800000 <<< 60) ||| 0x0)))) <<< 1020) ||| ((((((((((0x8e240000000 <<< 60) ||| 0x28a380001479800) <<< 60) ||| 0x3119800000) <<< 120) ||| ((0x0 <<< 60) ||| 0xc8ec0000000)) <<< 240) ||| ((((0xc5f000 <<< 60) ||| 0x0) <<< 120) ||| ((0x3c2540000 <<< 60) ||| 0x343700000000))) <<< 480) ||| ((((((0x30d140000000000 <<< 60) ||| 0x14f880) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0x29064 <<< 60) ||| 0x0))))) <<< 2040) ||| ((((((((((((0x0 <<< 60) ||| 0x386fc000000000) <<< 60) ||| 0x899e8a500000) <<< 120) ||| ((0x205df8c9 <<< 60) ||| 0x400000000000000)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x208f00bf542bc) <<< 120) ||| ((0x34da <<< 60) ||| 0x0))) <<< 480) ||| ((((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0x1417c0000000 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x2cdf80 <<< 60) ||| 0x206d40000) <<< 120) ||| ((0x0 <<< 60) ||| 0x187fc000000)))) <<< 1020) ||| ((((((((((0x3116000000 <<< 60) ||| 0x24c2000000000) <<< 60) ||| 0x304040000000) <<< 120) ||| ((0x1d1868a7c00 <<< 60) ||| 0x2cb880)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x2c0bc000000000))) <<< 480) ||| ((((((0x9800000000 <<< 60) ||| 0x471) <<< 120) ||| ((0xc00000000901ec6 <<< 60) ||| 0xb80000000000000)) <<< 240) ||| ((((0x384c4 <<< 60) ||| 0x0) <<< 120) ||| ((0x289bc000000 <<< 60) ||| 0x0)))))) <<< 4080) ||| ((((((((((((((0x1c36400000000 <<< 60) ||| 0x210d3071) <<< 60) ||| 0x400004c7c000000) <<< 120) ||| ((0x38 <<< 60) ||| 0x870000000000000)) <<< 240) ||| ((((0x24d1c0002c46 <<< 60) ||| 0x3d0) <<< 120) ||| ((0x980000000000000 <<< 60) ||| 0x8068))) <<< 480) ||| ((((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0xad00 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0x191a0000000000 <<< 60) ||| 0x0)))) <<< 1020) ||| ((((((((((0x38ee4000 <<< 60) ||| 0x141940000000000) <<< 60) ||| 0x0) <<< 120) ||| ((0x183d400000000 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x2491408 <<< 60) ||| 0xd00000000000000) <<< 120) ||| ((0x0 <<< 60) ||| 0x0))) <<< 480) ||| ((((((0x14f6301d8c45000 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x46c800000000000)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x0))))) <<< 2040) ||| ((((((((((((0x0 <<< 60) ||| 0x0) <<< 60) ||| 0x10a7800000000) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x3) <<< 120) ||| ((0x111c00000000000 <<< 60) ||| 0xe))) <<< 480) ||| ((((((0xe00000000000034 <<< 60) ||| 0x6c48b800000000) <<< 120) ||| ((0x2c9f <<< 60) ||| 0xc00000000000000)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x2cbb0) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)))) <<< 1020) ||| ((((((((((0x0 <<< 60) ||| 0x0) <<< 60) ||| 0x10cc8000) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x948 <<< 60) ||| 0x11200241240) <<< 120) ||| ((0x45000000000000 <<< 60) ||| 0x10400402240052))) <<< 480) ||| ((((((0x208001000008041 <<< 60) ||| 0x601000080880201) <<< 120) ||| ((0x140189200000000 <<< 60) ||| 0x8001025104b080)) <<< 240) ||| ((((0x21200000824020b <<< 60) ||| 0x88039001400240) <<< 120) ||| ((0x80008440200008 <<< 60) ||| 0x202000001048000))))))) else (if j<2 then ((((((((((((((((0x2cb30 <<< 60) ||| 0x0) <<< 60) ||| 0x5c2c96800) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x3c83800) <<< 120) ||| ((0x0 <<< 60) ||| 0x0))) <<< 480) ||| ((((((0x0 <<< 60) ||| 0x1c854000000) <<< 120) ||| ((0x1c5bc00000 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)))) <<< 1020) ||| ((((((((((0x0 <<< 60) ||| 0x111) <<< 60) ||| 0x32cc5ac79785340) <<< 120) ||| ((0x0 <<< 60) ||| 0xc1a2cac)) <<< 240) ||| ((((0x800000000426800 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x3cba80000000))) <<< 480) ||| ((((((0x287800000000000 <<< 60) ||| 0x8144000000000) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x341 <<< 60) ||| 0xb80001015800000) <<< 120) ||| ((0x0 <<< 60) ||| 0x0))))) <<< 2040) ||| ((((((((((((0x282480000000000 <<< 60) ||| 0x0) <<< 60) ||| 0x0) <<< 120) ||| ((0x390cf0992c45 <<< 60) ||| 0x400000000000000)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x0))) <<< 480) ||| ((((((0x2cc4800000003c <<< 60) ||| 0x9b0000000000003) <<< 120) ||| ((0xd0c00000000000 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x201400000) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)))) <<< 1020) ||| ((((((((((0x30000107ac0 <<< 60) ||| 0x0) <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0xa20000000000)) <<< 240) ||| ((((0x28ae400000000 <<< 60) ||| 0x3cb480000000) <<< 120) ||| ((0x0 <<< 60) ||| 0x147700))) <<< 480) ||| ((((((0x73000020db00001 <<< 60) ||| 0x912800014eafc70) <<< 120) ||| ((0x800000000000000 <<< 60) ||| 0x146680c3400000)) <<< 240) ||| ((((0x310b4 <<< 60) ||| 0x0) <<< 120) ||| ((0xcdc100 <<< 60) ||| 0x500000000000000)))))) <<< 4080) ||| ((((((((((((((0x0 <<< 60) ||| 0x80540000000) <<< 60) ||| 0x31158000000) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x10ad <<< 60) ||| 0xc00000000000000) <<< 120) ||| ((0x2c1a8c <<< 60) ||| 0x6c10af08cf00000))) <<< 480) ||| ((((((0x20b9c0000515 <<< 60) ||| 0x1c3ac0001cd0000) <<< 120) ||| ((0x4a0c0 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x109b40000000 <<< 60) ||| 0x3cf58000000) <<< 120) ||| ((0x0 <<< 60) ||| 0x38f5c00000000)))) <<< 1020) ||| ((((((((((0x0 <<< 60) ||| 0x43) <<< 60) ||| 0x900000000000000) <<< 120) ||| ((0xcd2c <<< 60) ||| 0x205000000000)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x1c8290a340) <<< 120) ||| ((0x3c6ac00000000 <<< 60) ||| 0x0))) <<< 480) ||| ((((((0x3407800 <<< 60) ||| 0x3c290d0a40) <<< 120) ||| ((0x0 <<< 60) ||| 0x4e00000)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x0))))) <<< 2040) ||| ((((((((((((0x0 <<< 60) ||| 0x2c7dc000000000) <<< 60) ||| 0x8a0506dc) <<< 120) ||| ((0x0 <<< 60) ||| 0x14f0800)) <<< 240) ||| ((((0x301b40001c8e40 <<< 60) ||| 0x0) <<< 120) ||| ((0x14984000008b <<< 60) ||| 0xc00000000000000))) <<< 480) ||| ((((((0x0 <<< 60) ||| 0x3c5ec00000000) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x0 <<< 60) ||| 0xc9f0) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)))) <<< 1020) ||| ((((((((((0xe580 <<< 60) ||| 0x0) <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x905c1780002 <<< 60) ||| 0x40e8000000020fe) <<< 120) ||| ((0x2036e4b70000000 <<< 60) ||| 0x30))) <<< 480) ||| ((((((0xd7400028c640000 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x1c))))))) else ((((((((((((((((0x14c540000000 <<< 60) ||| 0x0) <<< 60) ||| 0x0) <<< 120) ||| ((0xc31000000000 <<< 60) ||| 0x185e00000000)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0x503c00000000 <<< 60) ||| 0x0))) <<< 480) ||| ((((((0x200d400 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x183 <<< 60) ||| 0x8c0000000000000) <<< 120) ||| ((0x4e9c00000000 <<< 60) ||| 0x0)))) <<< 1020) ||| ((((((((((0x0 <<< 60) ||| 0x0) <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x340)) <<< 240) ||| ((((0x1c0000000000000 <<< 60) ||| 0x30a5400000000) <<< 120) ||| ((0x0 <<< 60) ||| 0x0))) <<< 480) ||| ((((((0x40dc000000000 <<< 60) ||| 0x187a8) <<< 120) ||| ((0x349a40003cf3 <<< 60) ||| 0x90e40908000000)) <<< 240) ||| ((((0x4 <<< 60) ||| 0xfdd001800000000) <<< 120) ||| ((0x0 <<< 60) ||| 0x0))))) <<< 2040) ||| ((((((((((((0x14784000000034 <<< 60) ||| 0x468000000024d56) <<< 60) ||| 0x82c0003012c000) <<< 120) ||| ((0x0 <<< 60) ||| 0x3cb340)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x34b6bc71) <<< 120) ||| ((0x0 <<< 60) ||| 0x0))) <<< 480) ||| ((((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0x206 <<< 60) ||| 0x71844c0003c8180)) <<< 240) ||| ((((0xce1c00000000 <<< 60) ||| 0x4d4) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)))) <<< 1020) ||| ((((((((((0x4d8400000000 <<< 60) ||| 0x0) <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0x282e4000000000 <<< 60) ||| 0x0))) <<< 480) ||| ((((((0xc594000302f <<< 60) ||| 0x8dce0550000047) <<< 120) ||| ((0x6c0000000000000 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x2c20089a800) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)))))) <<< 4020) ||| ((((((((((((((0x0 <<< 60) ||| 0x0) <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x10df4000)) <<< 240) ||| ((((0x38c240000000000 <<< 60) ||| 0x0) <<< 120) ||| ((0x874c0000 <<< 60) ||| 0x47bc0000000))) <<< 480) ||| ((((((0x1c522486c000000 <<< 60) ||| 0x2822f104645d40) <<< 120) ||| ((0xd800000000 <<< 60) ||| 0x34ec40000000)) <<< 240) ||| ((((0x2d04800 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x861c00000000000)))) <<< 1020) ||| ((((((((((0x0 <<< 60) ||| 0x0) <<< 60) ||| 0x0) <<< 120) ||| ((0x4c440000000 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x2042000000 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x0))) <<< 480) ||| ((((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x38a334a8000)) <<< 240) ||| ((((0x0 <<< 60) ||| 0xde8000000000000) <<< 120) ||| ((0x0 <<< 60) ||| 0x14d))))) <<< 1980) ||| ((((((((((((0x300000000000000 <<< 60) ||| 0x381d400000000) <<< 60) ||| 0x24b78000) <<< 120) ||| ((0x3cc <<< 60) ||| 0x400000000000000)) <<< 240) ||| ((((0x309980000 <<< 60) ||| 0x2c47c0000000) <<< 120) ||| ((0x0 <<< 60) ||| 0x0))) <<< 480) ||| ((((((0x2cff4 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0x3cd04000000 <<< 60) ||| 0x38cde0)))) <<< 960) ||| ((((((((0xe4000000001cea8 <<< 60) ||| 0x390d68134000) <<< 120) ||| ((0x41a40000000000 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x289c) <<< 120) ||| ((0x4080c0000000000 <<< 60) ||| 0x0))) <<< 480) ||| ((((((0x3456d8440 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x20840 <<< 60) ||| 0x14fa60557004) <<< 120) ||| ((0x800000000000000 <<< 60) ||| 0x0))))))))) else (if j<5 then (if j<4 then ((((((((((((((((0x110ec <<< 60) ||| 0x0) <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x3002400000000)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x307) <<< 120) ||| ((0xd0000000000000d <<< 60) ||| 0x140000000203d0))) <<< 480) ||| ((((((0x0 <<< 60) ||| 0x345640000000000) <<< 120) ||| ((0x4ad800000 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0x912c00000 <<< 60) ||| 0x0)))) <<< 1020) ||| ((((((((((0x0 <<< 60) ||| 0x24b2c00) <<< 60) ||| 0x108d58) <<< 120) ||| ((0xbc400014fb80000 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x387b4000000 <<< 60) ||| 0x18) <<< 120) ||| ((0x950000000000000 <<< 60) ||| 0x11800000000))) <<< 480) ||| ((((((0x28e <<< 60) ||| 0x168088000000024) <<< 120) ||| ((0x33680a000020344 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0x1c5cc <<< 60) ||| 0x10ca8000))))) <<< 2040) ||| ((((((((((((0xec80000000000 <<< 60) ||| 0x0) <<< 60) ||| 0x2ccea40c40000) <<< 120) ||| ((0x0 <<< 60) ||| 0x1cf84000000)) <<< 240) ||| ((((0x2c38000000 <<< 60) ||| 0x2) <<< 120) ||| ((0x2340c600000000 <<< 60) ||| 0x0))) <<< 480) ||| ((((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0xc00000000 <<< 60) ||| 0x634000000)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0x90c4000 <<< 60) ||| 0x0)))) <<< 1020) ||| ((((((((((0x3c66c000000000 <<< 60) ||| 0x0) <<< 60) ||| 0x3430c0000000) <<< 120) ||| ((0x8680000000000 <<< 60) ||| 0x8c9c0)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x3c4f80000000) <<< 120) ||| ((0x28bd24c <<< 60) ||| 0xe00000000282980))) <<< 480) ||| ((((((0x246a90398ca58 <<< 60) ||| 0xc64) <<< 120) ||| ((0x490340000000000 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)))))) <<< 4080) ||| ((((((((((((((0x291a4 <<< 60) ||| 0x0) <<< 60) ||| 0x0) <<< 120) ||| ((0x18 <<< 60) ||| 0x2b4000109640000)) <<< 240) ||| ((((0x3cc98000 <<< 60) ||| 0x0) <<< 120) ||| ((0x4db80 <<< 60) ||| 0x0))) <<< 480) ||| ((((((0x0 <<< 60) ||| 0x281800000000000) <<< 120) ||| ((0x149d5c4280 <<< 60) ||| 0x342e80000)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0x18a8800000 <<< 60) ||| 0x1081589240000)))) <<< 1020) ||| ((((((((((0x0 <<< 60) ||| 0x2cf37cc) <<< 60) ||| 0x300000000000000) <<< 120) ||| ((0x30b1c0002 <<< 60) ||| 0x4cac00000000000)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0x1 <<< 60) ||| 0x843400030218000))) <<< 480) ||| ((((((0x0 <<< 60) ||| 0x305f4000000009) <<< 120) ||| ((0x104000000000000 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x5040000105 <<< 60) ||| 0xf84bd4000000000) <<< 120) ||| ((0x0 <<< 60) ||| 0x0))))) <<< 2040) ||| ((((((((((((0x0 <<< 60) ||| 0x1c) <<< 60) ||| 0x5d0000000000002) <<< 120) ||| ((0x59b81380000000 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x18f0c0000000000))) <<< 480) ||| ((((((0x41fc0 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x106f0000000)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)))) <<< 1020) ||| ((((((((((0x10 <<< 60) ||| 0xb0c000000000000) <<< 60) ||| 0x2cbf) <<< 120) ||| ((0x80000820c000000 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x3cb6) <<< 120) ||| ((0xc00000000000000 <<< 60) ||| 0x286140))) <<< 480) ||| ((((((0x43380000 <<< 60) ||| 0x0) <<< 120) ||| ((0x30fd8000000 <<< 60) ||| 0x2cf000002c)) <<< 240) ||| ((((0xc68000000000000 <<< 60) ||| 0x34e700000000) <<< 120) ||| ((0x4acc00000e55ca <<< 60) ||| 0xe80000000000000))))))) else ((((((((((((((((0x14fc00 <<< 60) ||| 0x380204577) <<< 60) ||| 0x44e800000000000) <<< 120) ||| ((0x18a4c87 <<< 60) ||| 0x480000000000000)) <<< 240) ||| ((((0x3ec00000000 <<< 60) ||| 0x1885) <<< 120) ||| ((0xc000000000001c5 <<< 60) ||| 0xa103a0000000000))) <<< 540) ||| ((((((((0x0 <<< 60) ||| 0x0) <<< 60) ||| 0x0) <<< 120) ||| ((0x38 <<< 60) ||| 0x6d8000000000000)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x183f80000000000) <<< 120) ||| ((0x3917000000 <<< 60) ||| 0x4dc00000000)))) <<< 1020) ||| ((((((((((0x0 <<< 60) ||| 0x46f40003ced70b) <<< 60) ||| 0xda455c000000000) <<< 120) ||| ((0xa5c0001 <<< 60) ||| 0x4b1800014fb4000)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x24ffccd3c00000) <<< 120) ||| ((0x1 <<< 60) ||| 0xce3800000000000))) <<< 480) ||| ((((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x3cea40000000)) <<< 240) ||| ((((0x30dcac9e400 <<< 60) ||| 0x247b80) <<< 120) ||| ((0x2900800000000 <<< 60) ||| 0x0))))) <<< 2040) ||| ((((((((((((0x0 <<< 60) ||| 0x110b0000000000) <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x18ea000)) <<< 240) ||| ((((0xcb14000181200 <<< 60) ||| 0x0) <<< 120) ||| ((0x145380000000 <<< 60) ||| 0x0))) <<< 480) ||| ((((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x9800000) <<< 120) ||| ((0xd11848940000000 <<< 60) ||| 0x2809c00)))) <<< 1020) ||| ((((((((((0x0 <<< 60) ||| 0x1) <<< 60) ||| 0x8f908f5444ccc75) <<< 120) ||| ((0x400000000000000 <<< 60) ||| 0x186f80)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x0))) <<< 480) ||| ((((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0x2106c000000 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x3 <<< 60) ||| 0xc63e0aff4778000) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)))))) <<< 4080) ||| ((((((((((((((0x0 <<< 60) ||| 0xc3b400000000000) <<< 60) ||| 0x20790000080e400) <<< 120) ||| ((0x3093000000 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x1cb7c0000000 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x0))) <<< 480) ||| ((((((0x0 <<< 60) ||| 0x14d9a82) <<< 120) ||| ((0x880000000000000 <<< 60) ||| 0x2)) <<< 240) ||| ((((0x465c00000000000 <<< 60) ||| 0x2cd4c0000000000) <<< 120) ||| ((0x0 <<< 60) ||| 0x864c00000003)))) <<< 1020) ||| ((((((((((0x4e7800000000000 <<< 60) ||| 0x0) <<< 60) ||| 0x1c) <<< 120) ||| ((0x8d88e3c00020ddc <<< 60) ||| 0x0)) <<< 240) ||| ((((0x3cf4946 <<< 60) ||| 0xc40000ccb000000) <<< 120) ||| ((0x250fc00000000 <<< 60) ||| 0x3850c0000000))) <<< 480) ||| ((((((0x20e52cf18000000 <<< 60) ||| 0x3cb4c00000) <<< 120) ||| ((0x1 <<< 60) ||| 0x918800000000000)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0x340ec0000 <<< 60) ||| 0x0))))) <<< 2040) ||| ((((((((((((0x0 <<< 60) ||| 0x144f48f140) <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x40a80 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x872c0000000000))) <<< 480) ||| ((((((0x0 <<< 60) ||| 0x103bc) <<< 120) ||| ((0x1c6600000000 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x31024000281cc) <<< 120) ||| ((0x0 <<< 60) ||| 0x19120000000)))) <<< 1020) ||| ((((((((((0x21 <<< 60) ||| 0xbc00010e5c0000) <<< 60) ||| 0x18b840000000) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x45d80000000) <<< 120) ||| ((0x342 <<< 60) ||| 0xa40002cc8000000))) <<< 480) ||| ((((((0x251940000 <<< 60) ||| 0x0) <<< 120) ||| ((0x20a3c0000000000 <<< 60) ||| 0x183fc00000)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x341000)))))))) else (if j<6 then ((((((((((((((((0x282c60a74 <<< 60) ||| 0x0) <<< 60) ||| 0x0) <<< 120) ||| ((0x3c6e9c4740 <<< 60) ||| 0x209480000d09c)) <<< 240) ||| ((((0x184100002031 <<< 60) ||| 0x64084000081f400) <<< 120) ||| ((0x0 <<< 60) ||| 0x0))) <<< 480) ||| ((((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x1c110000 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)))) <<< 1020) ||| ((((((((((0x0 <<< 60) ||| 0x0) <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x4e7c0002469400 <<< 60) ||| 0x85a800000) <<< 120) ||| ((0x185e9 <<< 60) ||| 0x4d1800010a68000))) <<< 480) ||| ((((((0x0 <<< 60) ||| 0x188640) <<< 120) ||| ((0x2 <<< 60) ||| 0xd00c00000001cf3)) <<< 240) ||| ((((0x80000000000024a <<< 60) ||| 0xf80000000000000) <<< 120) ||| ((0x0 <<< 60) ||| 0x0))))) <<< 2040) ||| ((((((((((((0x0 <<< 60) ||| 0x2caac000000000) <<< 60) ||| 0x0) <<< 120) ||| ((0x2c74 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x106ec) <<< 120) ||| ((0x0 <<< 60) ||| 0xecc000000))) <<< 480) ||| ((((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0xc24400)) <<< 240) ||| ((((0x38f2c000000000 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)))) <<< 1020) ||| ((((((((((0x0 <<< 60) ||| 0x10824) <<< 60) ||| 0x0) <<< 120) ||| ((0x204e000 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x14f248b740000 <<< 60) ||| 0xd08) <<< 120) ||| ((0xc00000000000000 <<< 60) ||| 0x0))) <<< 480) ||| ((((((0x0 <<< 60) ||| 0x3c7a) <<< 120) ||| ((0x400000000000000 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x2895c00000000 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x24fd78)))))) <<< 4080) ||| ((((((((((((((0x944454800000003 <<< 60) ||| 0x49e000000000000) <<< 60) ||| 0x341) <<< 120) ||| ((0x6d0c18000000000 <<< 60) ||| 0x2)) <<< 240) ||| ((((0xca1c00020ef0000 <<< 60) ||| 0x0) <<< 120) ||| ((0x2432dc <<< 60) ||| 0xa24000000000000))) <<< 480) ||| ((((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0xc7e000000 <<< 60) ||| 0x288340000)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x386e000) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)))) <<< 1020) ||| ((((((((((0x0 <<< 60) ||| 0x11) <<< 60) ||| 0xb0000185ac00000) <<< 120) ||| ((0x47d40000 <<< 60) ||| 0x2c7ed0a10000)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x1407c00000) <<< 120) ||| ((0x0 <<< 60) ||| 0x3c1180000000))) <<< 480) ||| ((((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x4a80000000)) <<< 240) ||| ((((0x383f4000000 <<< 60) ||| 0x0) <<< 120) ||| ((0x24d500001 <<< 60) ||| 0xc2b000000000000))))) <<< 2040) ||| ((((((((((((0x38f47474400 <<< 60) ||| 0x34ca4000000000) <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x28226105c00)) <<< 240) ||| ((((0x286180 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x38c91cf))) <<< 480) ||| ((((((0xa80002489147cc0 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x3cb41484800004 <<< 60) ||| 0x220000000010c39) <<< 120) ||| ((0x8a8c46118300000 <<< 60) ||| 0x14d600000000000)))) <<< 1020) ||| ((((((((((0x0 <<< 60) ||| 0x0) <<< 60) ||| 0xcc1000000000000) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x1434c <<< 60) ||| 0x0) <<< 120) ||| ((0x2c2 <<< 60) ||| 0x7b07d80001814e0))) <<< 480) ||| ((((((0xcc00000113c0000 <<< 60) ||| 0x0) <<< 120) ||| ((0x388a000 <<< 60) ||| 0x34bf0000000000)) <<< 240) ||| ((((0x1852c00000000 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x3ce60000000000))))))) else ((((((((((((((((0x109540 <<< 60) ||| 0x0) <<< 60) ||| 0xc3680000000) <<< 120) ||| ((0x0 <<< 60) ||| 0x1c8b4000000000)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x182d0000000000))) <<< 540) ||| ((((((((0x1 <<< 60) ||| 0x8fed0d900bb6835) <<< 60) ||| 0x800000000000000) <<< 120) ||| ((0x0 <<< 60) ||| 0x209368524)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x184968a2c000000) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)))) <<< 1020) ||| ((((((((((0x0 <<< 60) ||| 0x0) <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x10a44000000 <<< 60) ||| 0x28240000000018) <<< 120) ||| ((0x920000303b846a6 <<< 60) ||| 0x10100000000004e))) <<< 480) ||| ((((((0xc000145b0000000 <<< 60) ||| 0x0) <<< 120) ||| ((0x86300000 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x34bb80000000))))) <<< 2040) ||| ((((((((((((0x0 <<< 60) ||| 0x0) <<< 60) ||| 0x0) <<< 120) ||| ((0x34f3c0000000 <<< 60) ||| 0x5c4000000)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x11190) <<< 120) ||| ((0x0 <<< 60) ||| 0x243b000))) <<< 480) ||| ((((((0x14f8c000000000 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x2cfe4000000)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)))) <<< 1020) ||| ((((((((((0x0 <<< 60) ||| 0x0) <<< 60) ||| 0x0) <<< 120) ||| ((0x2caa80000000000 <<< 60) ||| 0x283880)) <<< 240) ||| ((((0x2 <<< 60) ||| 0xc85000000000c3c) <<< 120) ||| ((0x8c890c78000000 <<< 60) ||| 0x0))) <<< 480) ||| ((((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x1cb200)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x149c) <<< 120) ||| ((0xc00000000000000 <<< 60) ||| 0x20b500)))))) <<< 4080) ||| ((((((((((((((0x0 <<< 60) ||| 0x0) <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x151380000000 <<< 60) ||| 0x4ba0000000) <<< 120) ||| ((0x28 <<< 60) ||| 0x4a7caf641140000))) <<< 480) ||| ((((((0x0 <<< 60) ||| 0x2ca280002401400) <<< 120) ||| ((0x28 <<< 60) ||| 0xa18000000000000)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x202cb8d) <<< 120) ||| ((0x5c0000000000031 <<< 60) ||| 0xc0000000000000)))) <<< 1020) ||| ((((((((((0x0 <<< 60) ||| 0x0) <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x0))) <<< 480) ||| ((((((0x0 <<< 60) ||| 0x14) <<< 120) ||| ((0xf7c00000001831f <<< 60) ||| 0xc52800000000000)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x0))))) <<< 2040) ||| ((((((((((((0x0 <<< 60) ||| 0x0) <<< 60) ||| 0x1034800000000) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0x457ecb014abc000 <<< 60) ||| 0x34d))) <<< 480) ||| ((((((0xf0000000034e180 <<< 60) ||| 0x188a8) <<< 120) ||| ((0x0 <<< 60) ||| 0xc18c00)) <<< 240) ||| ((((0x3cbbc0 <<< 60) ||| 0x284f000000000) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)))) <<< 1020) ||| ((((((((((0x1c15c000000000 <<< 60) ||| 0x0) <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0x283c8000000 <<< 60) ||| 0x83cc000000000))) <<< 480) ||| ((((((0x0 <<< 60) ||| 0x2070c000) <<< 120) ||| ((0x2c1 <<< 60) ||| 0xe400020fac00000)) <<< 240) ||| ((((0xc330 <<< 60) ||| 0x28384000) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)))))))))) else (if j<10 then (if j<8 then ((((((((((((((((0x82a <<< 60) ||| 0x800028c1c000000) <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x2ce8c000)) <<< 240) ||| ((((0x206a00000000000 <<< 60) ||| 0x24) <<< 120) ||| ((0x9e9c91c00000003 <<< 60) ||| 0xe1000000000000))) <<< 480) ||| ((((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0x387b000000000 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x110 <<< 60) ||| 0x7e0f23c7f000000) <<< 120) ||| ((0x0 <<< 60) ||| 0x151af4d8)))) <<< 1020) ||| ((((((((((0xc000000000003c5 <<< 60) ||| 0x1000000000849c0) <<< 60) ||| 0x18a700003) <<< 120) ||| ((0xc93b89de025a09f <<< 60) ||| 0x44f1c0000000000)) <<< 240) ||| ((((0x384e4000000000 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x1004000000))) <<< 480) ||| ((((((0x0 <<< 60) ||| 0x2467f41f34718) <<< 120) ||| ((0x0 <<< 60) ||| 0x38558000000)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x0))))) <<< 2040) ||| ((((((((((((0x0 <<< 60) ||| 0x20940000181c7) <<< 60) ||| 0xc9c000034f74000) <<< 120) ||| ((0x24c080000000000 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x0))) <<< 480) ||| ((((((0x0 <<< 60) ||| 0x38698000) <<< 120) ||| ((0x0 <<< 60) ||| 0x117c0)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)))) <<< 1020) ||| ((((((((((0x2489c <<< 60) ||| 0x3d154000) <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x428c0000000 <<< 60) ||| 0x0) <<< 120) ||| ((0x1cdfc000000000 <<< 60) ||| 0x3819dca940000))) <<< 480) ||| ((((((0x4e84000 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0x4 <<< 60) ||| 0x174000000000000)))))) <<< 4020) ||| ((((((((((((((0x1c87 <<< 60) ||| 0x400000000000000) <<< 60) ||| 0x2c820000000028) <<< 120) ||| ((0x4c8000000000000 <<< 60) ||| 0x0)) <<< 240) ||| ((((0xc8 <<< 60) ||| 0x440000000000000) <<< 120) ||| ((0x0 <<< 60) ||| 0x0))) <<< 480) ||| ((((((0x0 <<< 60) ||| 0x35100000000000) <<< 120) ||| ((0x0 <<< 60) ||| 0x18e4)) <<< 240) ||| ((((0xc000000004d2000 <<< 60) ||| 0x1c5a6408c0) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)))) <<< 1020) ||| ((((((((((0x3ce88000000 <<< 60) ||| 0x281eb87c800000) <<< 60) ||| 0x2) <<< 120) ||| ((0x840800000000000 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x140b5c <<< 60) ||| 0xe8000000001cb80) <<< 120) ||| ((0x10b0 <<< 60) ||| 0x80001c6d0000000))) <<< 480) ||| ((((((0x10 <<< 60) ||| 0x498000000000003) <<< 120) ||| ((0x413000000000000 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x0 <<< 60) ||| 0xd0c8) <<< 120) ||| ((0x0 <<< 60) ||| 0x0))))) <<< 1980) ||| ((((((((((((0xc <<< 60) ||| 0xfc4000000000000) <<< 60) ||| 0x8d480000000) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x0 <<< 60) ||| 0xc8b0000) <<< 120) ||| ((0x0 <<< 60) ||| 0x0))) <<< 480) ||| ((((((0x10ac40000 <<< 60) ||| 0x20c1) <<< 120) ||| ((0x400000000000000 <<< 60) ||| 0x18)) <<< 240) ||| ((((0xf80000000000002 <<< 60) ||| 0x81bc00000000000) <<< 120) ||| ((0x1cf780000000000 <<< 60) ||| 0x0)))) <<< 960) ||| ((((((((0x38090 <<< 60) ||| 0x4eb4000) <<< 120) ||| ((0x305 <<< 60) ||| 0x8c0000000208f80)) <<< 240) ||| ((((0x2c5b800000000 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x0))) <<< 480) ||| ((((((0x208000002d178 <<< 60) ||| 0x3073) <<< 120) ||| ((0x400000000000000 <<< 60) ||| 0x24aba0b2800028)) <<< 240) ||| ((((0xda8000000000000 <<< 60) ||| 0x0) <<< 120) ||| ((0x340640000000000 <<< 60) ||| 0x0))))))) else (if j<9 then ((((((((((((((((0xc1dc000242ba <<< 60) ||| 0xcc2c0002062c000) <<< 60) ||| 0x3c1) <<< 120) ||| ((0xc800000000cb640 <<< 60) ||| 0x1)) <<< 240) ||| ((((0x44b800000000000 <<< 60) ||| 0x50e80002ce) <<< 120) ||| ((0xd18f70000000000 <<< 60) ||| 0x24ec00000))) <<< 480) ||| ((((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0x100cc8 <<< 60) ||| 0x4000090180000)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)))) <<< 1020) ||| ((((((((((0x2c62000028c5 <<< 60) ||| 0xc0001c2524d9c00) <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x18e2800000) <<< 120) ||| ((0x3 <<< 60) ||| 0x854c00000000000))) <<< 480) ||| ((((((0x18d0800 <<< 60) ||| 0x0) <<< 120) ||| ((0x1913400000000 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x3cebcc) <<< 120) ||| ((0x8c4000000000000 <<< 60) ||| 0x0))))) <<< 2040) ||| ((((((((((((0x0 <<< 60) ||| 0x30ca1c8050) <<< 60) ||| 0x458000000000000) <<< 120) ||| ((0x0 <<< 60) ||| 0x24a)) <<< 240) ||| ((((0xc00000810742100 <<< 60) ||| 0x1c0340000) <<< 120) ||| ((0x209a00000000 <<< 60) ||| 0x3c6))) <<< 480) ||| ((((((0xb000000001c9580 <<< 60) ||| 0x28884) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0x10208000 <<< 60) ||| 0x3c9c8000000)))) <<< 1020) ||| ((((((((((0x30b380 <<< 60) ||| 0x28c6c0000) <<< 60) ||| 0x478d8758870) <<< 120) ||| ((0x3060fcd <<< 60) ||| 0xa40000000107c30)) <<< 240) ||| ((((0x41c000000000000 <<< 60) ||| 0x4074000) <<< 120) ||| ((0x0 <<< 60) ||| 0x0))) <<< 480) ||| ((((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0x2425c0000000000 <<< 60) ||| 0x1490c000000000)))))) <<< 4080) ||| ((((((((((((((0x14c3cd074 <<< 60) ||| 0x0) <<< 60) ||| 0x0) <<< 120) ||| ((0x81724b8e8 <<< 60) ||| 0x2f40dd9cbe3102c)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x0))) <<< 480) ||| ((((((0x3ca000000000 <<< 60) ||| 0x20eec000000) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x14de6)))) <<< 1020) ||| ((((((((((0x839400000000000 <<< 60) ||| 0x0) <<< 60) ||| 0x188dc00038fbc0) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x1cb580000000))) <<< 480) ||| ((((((0x3494c00 <<< 60) ||| 0x1c97400000) <<< 120) ||| ((0x1083e0 <<< 60) ||| 0x464800000000000)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x28ad4000))))) <<< 2040) ||| ((((((((((((0x1859c00 <<< 60) ||| 0x0) <<< 60) ||| 0x640) <<< 120) ||| ((0x10a1 <<< 60) ||| 0x400000000000000)) <<< 240) ||| ((((0x34cff0e2000000 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x0))) <<< 480) ||| ((((((0x230000000000 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x383a400)) <<< 240) ||| ((((0x8 <<< 60) ||| 0xed800000000514a) <<< 120) ||| ((0x3e80000492c000 <<< 60) ||| 0x0)))) <<< 1020) ||| ((((((((((0x0 <<< 60) ||| 0x3cb1000000000) <<< 60) ||| 0x3c3a) <<< 120) ||| ((0x800000003416400 <<< 60) ||| 0x350300)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x0))) <<< 480) ||| ((((((0x3 <<< 60) ||| 0x43f00000000300e) <<< 120) ||| ((0x0 <<< 60) ||| 0x20)) <<< 240) ||| ((((0x13c000000000000 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x0))))))) else ((((((((((((((((0x19800030 <<< 60) ||| 0x2e010e000000002) <<< 60) ||| 0x862a8ce70ef5cf9) <<< 120) ||| ((0xc000306bc000000 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x4a840000 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x290a8000000000))) <<< 540) ||| ((((((((0x10a6c <<< 60) ||| 0x0) <<< 60) ||| 0x304495124000000) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x1448c0000000000) <<< 120) ||| ((0x3d0880 <<< 60) ||| 0x0)))) <<< 1020) ||| ((((((((((0x0 <<< 60) ||| 0x1c76800) <<< 60) ||| 0x0) <<< 120) ||| ((0x1 <<< 60) ||| 0x458280280000000)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0x1 <<< 60) ||| 0x421f800c0000000))) <<< 480) ||| ((((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0x3477c09700000 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x8fb000 <<< 60) ||| 0x3460000000) <<< 120) ||| ((0x18760 <<< 60) ||| 0x2c228000))))) <<< 2040) ||| ((((((((((((0x0 <<< 60) ||| 0x108ac000000000) <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x1c3400000000000)) <<< 240) ||| ((((0x3c <<< 60) ||| 0xbcc000000000588) <<< 120) ||| ((0x0 <<< 60) ||| 0x0))) <<< 480) ||| ((((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x20d780000000000)) <<< 240) ||| ((((0x2d0d8000000000 <<< 60) ||| 0x0) <<< 120) ||| ((0x18608000 <<< 60) ||| 0x3c9024b97036000)))) <<< 1020) ||| ((((((((((0x244a108800 <<< 60) ||| 0x3) <<< 60) ||| 0x48a400024430000) <<< 120) ||| ((0x18a600000000000 <<< 60) ||| 0x8)) <<< 240) ||| ((((0xcc4000000001000 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x0))) <<< 480) ||| ((((((0x210dc00000000 <<< 60) ||| 0x0) <<< 120) ||| ((0x42c000000 <<< 60) ||| 0x15108000000000)) <<< 240) ||| ((((0x2c26fcd2540b9 <<< 60) ||| 0x810c00000001451) <<< 120) ||| ((0xd06880000000000 <<< 60) ||| 0x0)))))) <<< 4080) ||| ((((((((((((((0x0 <<< 60) ||| 0x0) <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x8f) <<< 120) ||| ((0xf00000000000000 <<< 60) ||| 0x1))) <<< 480) ||| ((((((0x4dac00038044000 <<< 60) ||| 0x0) <<< 120) ||| ((0x1445c00018ef80 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x280000 <<< 60) ||| 0x0) <<< 120) ||| ((0x3818b406000000 <<< 60) ||| 0x288080000)))) <<< 1020) ||| ((((((((((0x0 <<< 60) ||| 0x0) <<< 60) ||| 0x4) <<< 120) ||| ((0x2c000000000000 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x0))) <<< 480) ||| ((((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x14cec0000000)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x0))))) <<< 2040) ||| ((((((((((((0x0 <<< 60) ||| 0x0) <<< 60) ||| 0x0) <<< 120) ||| ((0x2c3238bc3073 <<< 60) ||| 0xfcb631084000240)) <<< 240) ||| ((((0xf8000104840aec0 <<< 60) ||| 0x0) <<< 120) ||| ((0x4678000 <<< 60) ||| 0x300b00000000000))) <<< 480) ||| ((((((0x0 <<< 60) ||| 0x2c0400000) <<< 120) ||| ((0x19164000 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x148f4) <<< 120) ||| ((0xc4d400000000000 <<< 60) ||| 0x0)))) <<< 1020) ||| ((((((((((0x18d8800000 <<< 60) ||| 0x0) <<< 60) ||| 0x0) <<< 120) ||| ((0x3ca <<< 60) ||| 0x400000000000000)) <<< 240) ||| ((((0x304440000 <<< 60) ||| 0x0) <<< 120) ||| ((0x3c4bd80aec7 <<< 60) ||| 0x240000000000000))) <<< 480) ||| ((((((0x3 <<< 60) ||| 0xc4185090035e816) <<< 120) ||| ((0xcefc0657c40000 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x23f8a480000000) <<< 120) ||| ((0x91800 <<< 60) ||| 0x0))))))))) else (if j<12 then (if j<11 then ((((((((((((((((0x110a00 <<< 60) ||| 0x0) <<< 60) ||| 0x1d0f) <<< 120) ||| ((0x908cc41ec000000 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x3102) <<< 120) ||| ((0x304c00000000000 <<< 60) ||| 0x301080))) <<< 540) ||| ((((((((0x14059c2078dc4 <<< 60) ||| 0x0) <<< 60) ||| 0x4704000000) <<< 120) ||| ((0x390b800000 <<< 60) ||| 0x91000000000)) <<< 240) ||| ((((0x204b4000 <<< 60) ||| 0x0) <<< 120) ||| ((0x10 <<< 60) ||| 0x878000000000000)))) <<< 1020) ||| ((((((((((0x8c7 <<< 60) ||| 0x400000000000000) <<< 60) ||| 0xc) <<< 120) ||| ((0x56800000002ccfa <<< 60) ||| 0xc9bb47c40000000)) <<< 240) ||| ((((0x283dc000000 <<< 60) ||| 0x0) <<< 120) ||| ((0x1 <<< 60) ||| 0x8ee843080000000))) <<< 480) ||| ((((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0xf400002009)) <<< 240) ||| ((((0x400039174000000 <<< 60) ||| 0xd470ff80) <<< 120) ||| ((0x0 <<< 60) ||| 0x0))))) <<< 2040) ||| ((((((((((((0x10ab5498c0002cf <<< 60) ||| 0x68000000000003c) <<< 60) ||| 0x9600002c04c0000) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x4238000000000 <<< 60) ||| 0x28dd400000000) <<< 120) ||| ((0x0 <<< 60) ||| 0x0))) <<< 480) ||| ((((((0x1898b421400024 <<< 60) ||| 0x63800004d380000) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)))) <<< 1020) ||| ((((((((((0xc53c00000 <<< 60) ||| 0x0) <<< 60) ||| 0x1914) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x0))) <<< 480) ||| ((((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)))))) <<< 4080) ||| ((((((((((((((0x0 <<< 60) ||| 0x0) <<< 60) ||| 0x18190000000) <<< 120) ||| ((0x20 <<< 60) ||| 0x728000000000000)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x385) <<< 120) ||| ((0x1b4658000000000 <<< 60) ||| 0xcc840001c46c))) <<< 480) ||| ((((((0x811c00000000000 <<< 60) ||| 0x146) <<< 120) ||| ((0x50ce9accbb10700 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x202fc)))) <<< 1020) ||| ((((((((((0x0 <<< 60) ||| 0x0) <<< 60) ||| 0x0) <<< 120) ||| ((0x1915c0000 <<< 60) ||| 0xd8000000000000)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x3c438000000000) <<< 120) ||| ((0x14665 <<< 60) ||| 0x45fc00000000000))) <<< 480) ||| ((((((0x3c2fb047800 <<< 60) ||| 0x34318000000000) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x42d8000))))) <<< 2040) ||| ((((((((((((0x28154000000 <<< 60) ||| 0x8e48000000000) <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x2cc2800000000) <<< 120) ||| ((0x2cd340000000 <<< 60) ||| 0x347))) <<< 480) ||| ((((((0xf6c0f00002c5080 <<< 60) ||| 0x1c28400000000) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)) <<< 240) ||| ((((0xbe800000 <<< 60) ||| 0xcbc0000) <<< 120) ||| ((0x0 <<< 60) ||| 0x8e69840c000000)))) <<< 1020) ||| ((((((((((0x0 <<< 60) ||| 0x10c0c0000) <<< 60) ||| 0x0) <<< 120) ||| ((0x1c5300000000000 <<< 60) ||| 0xcfcc0001519e8)) <<< 240) ||| ((((0x69c0002cfc80000 <<< 60) ||| 0x0) <<< 120) ||| ((0x1c0d00000000000 <<< 60) ||| 0x1827c0ba400000))) <<< 480) ||| ((((((0x14c8c00000000 <<< 60) ||| 0x2ec0000000) <<< 120) ||| ((0x0 <<< 60) ||| 0x34)) <<< 240) ||| ((((0x5c8000000000000 <<< 60) ||| 0x0) <<< 120) ||| ((0x38fd000 <<< 60) ||| 0x20929c))))))) else ((((((((((((((((0x1076400000000 <<< 60) ||| 0x342958e7) <<< 60) ||| 0x400000000000000) <<< 120) ||| ((0x0 <<< 60) ||| 0x2c008)) <<< 240) ||| ((((0x4f0 <<< 60) ||| 0x4433c0000000000) <<< 120) ||| ((0x0 <<< 60) ||| 0x2cf6c00000000))) <<< 480) ||| ((((((0x0 <<< 60) ||| 0x28d28000000) <<< 120) ||| ((0x348c800000 <<< 60) ||| 0x4d580000)) <<< 240) ||| ((((0x208e00000000 <<< 60) ||| 0x188990267412400) <<< 120) ||| ((0x30a98000286e5d <<< 60) ||| 0x80000000000000)))) <<< 1020) ||| ((((((((((0xc07000000000027 <<< 60) ||| 0x282de86) <<< 60) ||| 0x85cb98000000000) <<< 120) ||| ((0x2473800000000 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x3c7 <<< 60) ||| 0xfb8674000000000) <<< 120) ||| ((0x2462446cc <<< 60) ||| 0x105e))) <<< 480) ||| ((((((0x400000000000000 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x2cb0400 <<< 60) ||| 0x0) <<< 120) ||| ((0x3cedc00000000 <<< 60) ||| 0x0))))) <<< 2040) ||| ((((((((((((0x0 <<< 60) ||| 0x290adcded85900) <<< 60) ||| 0x10d70) <<< 120) ||| ((0x3c32a4dd <<< 60) ||| 0xb3c00)) <<< 240) ||| ((((0x1c5140 <<< 60) ||| 0x2cbe7) <<< 120) ||| ((0x3800000000000 <<< 60) ||| 0x14168000000))) <<< 480) ||| ((((((0x0 <<< 60) ||| 0x184d800000000) <<< 120) ||| ((0x0 <<< 60) ||| 0xd)) <<< 240) ||| ((((0xbc000000034d100 <<< 60) ||| 0x0) <<< 120) ||| ((0x3c30400038c0 <<< 60) ||| 0x0)))) <<< 1020) ||| ((((((((((0x0 <<< 60) ||| 0x0) <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x29c000000000720 <<< 60) ||| 0x0) <<< 120) ||| ((0x3881c0000000000 <<< 60) ||| 0x0))) <<< 480) ||| ((((((0x3037400000000 <<< 60) ||| 0x97acf51c184000) <<< 120) ||| ((0x0 <<< 60) ||| 0x38b5c00000)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)))))) <<< 4080) ||| ((((((((((((((0x0 <<< 60) ||| 0x1469) <<< 60) ||| 0x2c9) <<< 120) ||| ((0xf80000000141fac <<< 60) ||| 0x414000000000001)) <<< 240) ||| ((((0x4607c88acb4540c <<< 60) ||| 0x80000000000018d) <<< 120) ||| ((0x680003904c00000 <<< 60) ||| 0x1))) <<< 480) ||| ((((((0xc88c000000018cc <<< 60) ||| 0xc00000000000000) <<< 120) ||| ((0x0 <<< 60) ||| 0x1c00000)) <<< 240) ||| ((((0x0 <<< 60) ||| 0xc2) <<< 120) ||| ((0xcc000000024bfc0 <<< 60) ||| 0x0)))) <<< 1020) ||| ((((((((((0x5094000 <<< 60) ||| 0x8e800) <<< 60) ||| 0x108c0000000000) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x499400 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x34e94000))) <<< 480) ||| ((((((0x34aa00000000000 <<< 60) ||| 0x1d0f0000000000) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x10) <<< 120) ||| ((0x9ec000000010b54 <<< 60) ||| 0x0))))) <<< 2040) ||| ((((((((((((0x0 <<< 60) ||| 0x3d) <<< 60) ||| 0x16c000000000000) <<< 120) ||| ((0x1ccb4116 <<< 60) ||| 0x800000000000000)) <<< 240) ||| ((((0x185440 <<< 60) ||| 0x344adc0a40000) <<< 120) ||| ((0x0 <<< 60) ||| 0x0))) <<< 480) ||| ((((((0x0 <<< 60) ||| 0x3) <<< 120) ||| ((0xcae000000000000 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x3) <<< 120) ||| ((0x4c7000000000000 <<< 60) ||| 0x2c6b60f)))) <<< 1020) ||| ((((((((((0x640000000082ac0 <<< 60) ||| 0x4e6c) <<< 60) ||| 0x105040000000) <<< 120) ||| ((0x1c8fc000389 <<< 60) ||| 0xd8000000034e364)) <<< 240) ||| ((((0x1b0000000000000 <<< 60) ||| 0x35115cf4c000) <<< 120) ||| ((0x0 <<< 60) ||| 0x91a8000201e3c))) <<< 480) ||| ((((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x384d0000000000)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0x43c000000 <<< 60) ||| 0x0)))))))) else (if j<13 then ((((((((((((((((0x2c <<< 60) ||| 0x3e4000000000000) <<< 60) ||| 0x3837c000) <<< 120) ||| ((0x8b90000000 <<< 60) ||| 0x2878b4d6c00000)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0x1ca6400 <<< 60) ||| 0x1856000000))) <<< 540) ||| ((((((((0x18eb80000 <<< 60) ||| 0x1096c0000000) <<< 60) ||| 0x3ce0800) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x2448000) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)))) <<< 1020) ||| ((((((((((0x0 <<< 60) ||| 0x0) <<< 60) ||| 0x150f40) <<< 120) ||| ((0x247a1c4ff8260 <<< 60) ||| 0x8e2dc27)) <<< 240) ||| ((((0x40002514c000000 <<< 60) ||| 0x241500) <<< 120) ||| ((0x3 <<< 60) ||| 0x3c400000000000))) <<< 480) ||| ((((((0x311 <<< 60) ||| 0x440000046400000) <<< 120) ||| ((0xce440000 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x30472cfeb0db58) <<< 120) ||| ((0x4b0000000000000 <<< 60) ||| 0x0))))) <<< 2040) ||| ((((((((((((0x2105000 <<< 60) ||| 0x0) <<< 60) ||| 0x34354) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x90780003cd640 <<< 60) ||| 0x1824c0000) <<< 120) ||| ((0x0 <<< 60) ||| 0x0))) <<< 480) ||| ((((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x147e80 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)))) <<< 1020) ||| ((((((((((0x20 <<< 60) ||| 0x5d457800000000) <<< 60) ||| 0x803c00018810000) <<< 120) ||| ((0x181d00000000000 <<< 60) ||| 0x4aa4000000000)) <<< 240) ||| ((((0x14e30 <<< 60) ||| 0x830000) <<< 120) ||| ((0x3518c0000000000 <<< 60) ||| 0x0))) <<< 480) ||| ((((((0x1477400000000 <<< 60) ||| 0x0) <<< 120) ||| ((0x3ca08000000 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x80fc <<< 60) ||| 0x51100000000) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)))))) <<< 4080) ||| ((((((((((((((0x0 <<< 60) ||| 0x0) <<< 60) ||| 0x38bc80003c8) <<< 120) ||| ((0x580000000000000 <<< 60) ||| 0x0)) <<< 240) ||| ((((0xeb20540000 <<< 60) ||| 0x0) <<< 120) ||| ((0xc <<< 60) ||| 0x9d0000000000000))) <<< 480) ||| ((((((0x0 <<< 60) ||| 0x2468c0000000000) <<< 120) ||| ((0x3c86000000 <<< 60) ||| 0x39c)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x8a9c00) <<< 120) ||| ((0x1c58400000 <<< 60) ||| 0x0)))) <<< 1020) ||| ((((((((((0x442400000002505 <<< 60) ||| 0x400000000000000) <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0x39058 <<< 60) ||| 0x0))) <<< 480) ||| ((((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x1102)) <<< 240) ||| ((((0x8000000028bec00 <<< 60) ||| 0x0) <<< 120) ||| ((0x1 <<< 60) ||| 0xf9800000000000))))) <<< 2040) ||| ((((((((((((0x0 <<< 60) ||| 0x282d400000) <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x143)) <<< 240) ||| ((((0x2400000001879c0 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x20e0690))) <<< 480) ||| ((((((0x380000000000000 <<< 60) ||| 0x0) <<< 120) ||| ((0x1093 <<< 60) ||| 0xc00000000000000)) <<< 240) ||| ((((0x2c148000000000 <<< 60) ||| 0x0) <<< 120) ||| ((0xfa00000000 <<< 60) ||| 0x0)))) <<< 1020) ||| ((((((((((0x0 <<< 60) ||| 0x14e9000000000) <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x103500)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x0))) <<< 480) ||| ((((((0x3cde000000000 <<< 60) ||| 0x18c040000000) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)) <<< 240) ||| ((((0xf4000000000000 <<< 60) ||| 0x384880000000) <<< 120) ||| ((0x0 <<< 60) ||| 0x87e400000))))))) else ((((((((((((0x484e83d80000000 <<< 60) ||| 0x45b4000000) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)) <<< 180) ||| ((((0x8f28c68 <<< 60) ||| 0x0) <<< 60) ||| 0x0)) <<< 360) ||| ((((((0x382c000000000 <<< 60) ||| 0x0) <<< 60) ||| 0x0) <<< 180) ||| ((((0x0 <<< 60) ||| 0x0) <<< 60) ||| 0x0))) <<< 780) ||| ((((((((0x0 <<< 60) ||| 0x4) <<< 120) ||| ((0x9ac000000024378 <<< 60) ||| 0x10f1)) <<< 180) ||| ((((0x0 <<< 60) ||| 0x0) <<< 60) ||| 0x0)) <<< 360) ||| ((((((0xe640000000 <<< 60) ||| 0x0) <<< 60) ||| 0x30) <<< 180) ||| ((((0xcd4000000000000 <<< 60) ||| 0x0) <<< 60) ||| 0x200800000000000)))) <<< 1500) ||| ((((((((((0x2475000000 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x1c83c0000000000)) <<< 180) ||| ((((0x3110c000000000 <<< 60) ||| 0x30a92cc4c0002) <<< 60) ||| 0x90680002497d4d9)) <<< 360) ||| ((((((0x601ac0000000000 <<< 60) ||| 0x18c5000000) <<< 60) ||| 0x3c75c0001) <<< 180) ||| ((((0x906000000000000 <<< 60) ||| 0x0) <<< 60) ||| 0x0))) <<< 720) ||| ((((((((0x0 <<< 60) ||| 0x0) <<< 60) ||| 0x3cb) <<< 180) ||| ((((0x240000000000000 <<< 60) ||| 0x2c87c0000) <<< 60) ||| 0x0)) <<< 360) ||| ((((((0x28bac0000000000 <<< 60) ||| 0x28cd000000) <<< 60) ||| 0x0) <<< 180) ||| ((((0x0 <<< 60) ||| 0x8ab0000000) <<< 60) ||| 0x0)))))))))
def g127D9 (j : Nat) : Nat := (if j<1 then ((((((((((((((((0x84dd1306 <<< 60) ||| 0x4a99246476116a4) <<< 60) ||| 0x4d10c63fe0fb441) <<< 120) ||| ((0x98ff83ed0f62394 <<< 60) ||| 0x8f2c3bd8ea43948)) <<< 240) ||| ((((0xdf23680d4e33b8c <<< 60) ||| 0x6430b8bce2e28b8) <<< 120) ||| ((0xa2c38abc29e0a0a <<< 60) ||| 0x26e097424c08d02))) <<< 540) ||| ((((((((0x1f882c1f6876c1c <<< 60) ||| 0xa06ac18f85fa171) <<< 60) ||| 0x58014484a41180) <<< 120) ||| ((0x41c0ef036a0c602 <<< 60) ||| 0xe20a4023008c01d)) <<< 240) ||| ((((0xe063015603d80a4 <<< 60) ||| 0x2900440007ff74) <<< 120) ||| ((0x597fe3a2cbff596 <<< 60) ||| 0x64ffaeab27fd655)))) <<< 1020) ||| ((((((((((0x93feb9ac9ff5c16 <<< 60) ||| 0x4ffec8aa7fd6455) <<< 60) ||| 0x3feaa6c7ffdd563) <<< 120) ||| ((0xffaeab1ffd6558f <<< 60) ||| 0xffba2c7ff9d163f)) <<< 240) ||| ((((0xfae8b1ffc7458ff <<< 60) ||| 0xf322c7ff59163ff) <<< 120) ||| ((0xca8b1ffd5458fff <<< 60) ||| 0xb82c7ff5c163ffe))) <<< 480) ||| ((((((0xc8a9ffe6454ffeb <<< 60) ||| 0x22a7ff19153ffac) <<< 120) ||| ((0xba1fff7650fff3b <<< 60) ||| 0x287ff5d943ff8ec)) <<< 240) ||| ((((0xa1fff7550ffebaa <<< 60) ||| 0x87ffd9543ffacaa) <<< 120) ||| ((0x1fff6450ffeb228 <<< 60) ||| 0x7ff55143ffee0a1))))) <<< 2040) ||| ((((((((((((0xffd7050ffeaa6c1 <<< 60) ||| 0xff54f60ffa87b07) <<< 60) ||| 0xff75583febaac1f) <<< 120) ||| ((0xf59560ffee8b07f <<< 60) ||| 0xe74583feba2c1ff)) <<< 240) ||| ((((0x1d160ffcc8b07fd <<< 60) ||| 0x64583ff2a2c1ff5) <<< 120) ||| ((0x5160ffee6b07fd7 <<< 60) ||| 0x3583feb1ac1ff54))) <<< 480) ||| ((((((0xd60ffe86b07fd43 <<< 60) ||| 0x583ffb22a1ff991) <<< 120) ||| ((0x50ffac8a87fc645 <<< 60) ||| 0x43ffb1aa1ff58d5)) <<< 240) ||| ((((0xffe86a87fd4354 <<< 60) ||| 0x3feb2e81ff58f40) <<< 120) ||| ((0xffaa7a07ff76503 <<< 60) ||| 0xff3b281ff5d940f)))) <<< 1020) ||| ((((((((((0xf8eca07ff75503f <<< 60) ||| 0xebaa81ffd9540ff) <<< 60) ||| 0xacaa07ff64503fe) <<< 120) ||| ((0xb2281ff55140ffe <<< 60) ||| 0xe6a07fd73503ffb)) <<< 240) ||| ((((0x1a81ff58d40ffaa <<< 60) ||| 0x6a07fd43503ffb2) <<< 120) ||| ((0x261ff99130ffac8 <<< 60) ||| 0x987fc644c2feba6))) <<< 480) ||| ((((((0xcb7f5cf65bfae1b <<< 60) ||| 0x2dff74596ffb9ac) <<< 120) ||| ((0xb7fdc165bfaebb2 <<< 60) ||| 0x5fd73d92feb86c9)) <<< 240) ||| ((((0x7f5da64bfaeb325 <<< 60) ||| 0xfd73992feb84c97) <<< 120) ||| ((0xfdd564bfee6b27e <<< 60) ||| 0xf72592ffb82c97f)))))) <<< 4080) ||| ((((((((((((((0x5d464bfae6325fd <<< 60) ||| 0x70192febb4a97f5) <<< 60) ||| 0xce54bfae12a5ff7) <<< 120) ||| ((0x6552febb2a9df59 <<< 60) ||| 0x554bfee6aa7f771)) <<< 240) ||| ((((0x552ffb82a97f5d7 <<< 60) ||| 0x63dfacbb1dfd74d) <<< 120) ||| ((0x8efeb86c77fdd56 <<< 60) ||| 0x3dfecab1efd6558))) <<< 480) ||| ((((((0xeffba2c77fdc163 <<< 60) ||| 0xbfeeca9dfd7654f) <<< 120) ||| ((0xbeb2aa77fdd153b <<< 60) ||| 0xfee0a9dfd76d0ef)) <<< 240) ||| ((((0xebae87ef59343f7 <<< 60) ||| 0xaa9a1dfd70d0eff) <<< 120) ||| ((0xbb2877f5d943bfe <<< 60) ||| 0xeaa1dfd7550fdf3)))) <<< 1020) ||| ((((((((((0x2287ef59143f7ca <<< 60) ||| 0x8a1fbd5450feeb1) <<< 60) ||| 0xa877fdc143bfaeb) <<< 120) ||| ((0xb06fd65d82feba6 <<< 60) ||| 0xc1bf59360bfae7b)) <<< 240) ||| ((((0x6fd63d82ffbaac <<< 60) ||| 0x1bfd9560dfacab0) <<< 120) ||| ((0x5ff745837fb22c1 <<< 60) ||| 0xbf59160bfee6b06))) <<< 480) ||| ((((((0xff635837eb1ac17 <<< 60) ||| 0xfdd950bfaeca877) <<< 120) ||| ((0xd65542ffba2a1df <<< 60) ||| 0x55150bfee6a877d)) <<< 240) ||| ((((0x53542febb6817f5 <<< 60) ||| 0xd740f7ac9a07bd5) <<< 120) ||| ((0x4d02feb9e81ef50 <<< 60) ||| 0xf40bfeeca05fd76))))) <<< 2040) ||| ((((((((((((0x502ffbaa817f5d5 <<< 60) ||| 0x40f7cc8a07bd645) <<< 60) ||| 0x3df2a281ef5514) <<< 120) ||| ((0xbfee6a07bf4350 <<< 60) ||| 0x3dea1a81fe58140)) <<< 240) ||| ((((0xbfaec985fd754c2 <<< 60) ||| 0xfeba261f758d30f) <<< 120) ||| ((0xbaa6987dd434c3f <<< 60) ||| 0xcb0261fe54130fd))) <<< 480) ||| ((((((0xcec907ed76483f6 <<< 60) ||| 0xbaa41fbd9520fda) <<< 120) ||| ((0xca907ee74483f6b <<< 60) ||| 0xa241fbd9120fdcc)) <<< 240) ||| ((((0x8907ed64483f632 <<< 60) ||| 0x241fb95120fdaa8) <<< 120) ||| ((0x907ed73483f7b1a <<< 60) ||| 0x41fb58d20fdaa69)))) <<< 1020) ||| ((((((((((0x7ef43483f6a1a4 <<< 60) ||| 0x1fd9d910feaec88) <<< 60) ||| 0x7f575443fbb2a21) <<< 120) ||| ((0xfd59510fece8887 <<< 60) ||| 0xf574443fbb2221f)) <<< 240) ||| ((((0xd99110feac8887f <<< 60) ||| 0x464443fb2a221fd) <<< 120) ||| ((0x55110feae6887f7 <<< 60) ||| 0x63443fab1a21fd5))) <<< 480) ||| ((((((0x4d10fee86887f54 <<< 60) ||| 0x3442fab8ecb7bdc) <<< 120) ||| ((0x964afaea325dd73 <<< 60) ||| 0x192f6b90c97d5c4)) <<< 240) ||| ((((0x64bf2e0325dd739 <<< 60) ||| 0x52fbb8aa95f5d74) <<< 120) ||| ((0x3fd2c0907e94048 <<< 60) ||| 0x3f8a8221fc50110))))))) else (if j<2 then ((((((((((((((((0x2f2ad140 <<< 60) ||| 0xc00e045eddc0800) <<< 60) ||| 0xdb0481169170004) <<< 120) ||| ((0x407022d22d04007 <<< 60) ||| 0x42cc05765480)) <<< 240) ||| ((((0x617b7765002a41 <<< 60) ||| 0x6072ad0036d1604) <<< 120) ||| ((0x5035c08011b8082 <<< 60) ||| 0x5a0c58a1c582020))) <<< 540) ||| ((((((((0x4002c087b00010 <<< 60) ||| 0x42023e000881450) <<< 60) ||| 0x222e040438998) <<< 120) ||| ((0xe59c006000d2e6 <<< 60) ||| 0x22832400088292)) <<< 240) ||| ((((0xe602201d99b2ce0 <<< 60) ||| 0x6007d820119cc04) <<< 120) ||| ((0x20e2002acc04510 <<< 60) ||| 0x115660229202144)))) <<< 1020) ||| ((((((((((0x160414e00305040 <<< 60) ||| 0x430e2c082001060) <<< 60) ||| 0x39b644ca2670020) <<< 120) ||| ((0xced99734400380 <<< 60) ||| 0xcc9410117601131)) <<< 240) ||| ((((0x5ce04008160626 <<< 60) ||| 0x5d99a7002020812) <<< 120) ||| ((0x8a2c566d9942 <<< 60) ||| 0x1c06c11984810))) <<< 480) ||| ((((((0x83a504000889450 <<< 60) ||| 0x2203cc2840100) <<< 120) ||| ((0x107cc28c8802002 <<< 60) ||| 0xe612cacc045104)) <<< 240) ||| ((((0xc0011020a4b9808 <<< 60) ||| 0xa0762bcb341801c) <<< 120) ||| ((0xabcb345030038a <<< 60) ||| 0x3132eccd340100))))) <<< 2040) ||| ((((((((((((0x1eccb980841c40 <<< 60) ||| 0xa26040041856c10) <<< 60) ||| 0xf3010838002ab3) <<< 120) ||| ((0x81424510015660 <<< 60) ||| 0x238814ab3011400)) <<< 240) ||| ((((0x1059840a2c46604 <<< 60) ||| 0x4508233011220b) <<< 120) ||| ((0x20a68018502021 <<< 60) ||| 0xc4020a680141010))) <<< 480) ||| ((((((0x858902002021848 <<< 60) ||| 0xb020010418101d9) <<< 120) ||| ((0x132879a00803376 <<< 60) ||| 0x65cd1000e012e60)) <<< 240) ||| ((((0x40454a20502cc04 <<< 60) ||| 0x6021e20b9a0800e) <<< 120) ||| ((0x2c0c4cbb334d004 <<< 60) ||| 0x80e00088092e60)))) <<< 1020) ||| ((((((((((0x2200d8233070210 <<< 60) ||| 0x70e001041604617) <<< 60) ||| 0x9766602106162a5) <<< 120) ||| ((0xecca1000fb04020 <<< 60) ||| 0x6133011c466021a)) <<< 240) ||| ((((0xb01b0404cc04757 <<< 60) ||| 0xb32e60210601b04) <<< 120) ||| ((0x3cc0420e144660 <<< 60) ||| 0x2203039480014b8))) <<< 480) ||| ((((((0x100191000432119 <<< 60) ||| 0x280022c40394800) <<< 120) ||| ((0x1620b0396680181 <<< 60) ||| 0x81cb3400b100e59)) <<< 240) ||| ((((0xa00521100e59a00 <<< 60) ||| 0x620b022506072cd) <<< 120) ||| ((0x4840004320b01 <<< 60) ||| 0x250004610042001)))))) <<< 4080) ||| ((((((((((((((0x2303a1b04010010 <<< 60) ||| 0x88c12808022a502) <<< 60) ||| 0x100082e86cca040) <<< 120) ||| ((0x41d281064410a2 <<< 60) ||| 0x80910421e100808)) <<< 240) ||| ((((0x84730a040008c94 <<< 60) ||| 0x566040451400091) <<< 120) ||| ((0x42981404882168 <<< 60) ||| 0x81cd12682143c41))) <<< 480) ||| ((((((0x534108045518998 <<< 60) ||| 0x4d044114c9420a) <<< 120) ||| ((0x9a0871410101108 <<< 60) ||| 0x820219a4a041082)) <<< 240) ||| ((((0x2cc1008a1c50 <<< 60) ||| 0x8040f301083e610) <<< 120) ||| ((0x8088945040424c <<< 60) ||| 0x159808208366140)))) <<< 1020) ||| ((((((((((0x80011766ddd9400 <<< 60) ||| 0xa285810f68b1408) <<< 60) ||| 0xbb770b140800d) <<< 120) ||| ((0xb858a04005d8080 <<< 60) ||| 0xb022e604043d93)) <<< 240) ||| ((((0x810016046d81329 <<< 60) ||| 0x291cc2128104) <<< 120) ||| ((0x3660844109425b7 <<< 60) ||| 0x4540dcfd73da4f1))) <<< 480) ||| ((((((0x73b14e733884237 <<< 60) ||| 0x373cd6f0194d013) <<< 120) ||| ((0x214c092ea4b2d2a <<< 60) ||| 0xfca7b283499ef09)) <<< 240) ||| ((((0xc92322d481d1ef3 <<< 60) ||| 0x7451d3c6e119945) <<< 120) ||| ((0xdb165c529135c47 <<< 60) ||| 0x7102439b0d5c2e9))))) <<< 2040) ||| ((((((((((((0x9b423707941850 <<< 60) ||| 0x4cc0c50193ff6fe) <<< 60) ||| 0x5bf1afa7be30f6d) <<< 120) ||| ((0x3d62f40bc94f09b <<< 60) ||| 0xbb8c0fbb4aeacba)) <<< 240) ||| ((((0x36e75b94ce37b87 <<< 60) ||| 0xee0b37e8ddeb744) <<< 120) ||| ((0xdbcb6aed9035e0d <<< 60) ||| 0x55b4ccd22341acf))) <<< 480) ||| ((((((0x23376cc2329ac95 <<< 60) ||| 0xb1f6c5eb11ac243) <<< 120) ||| ((0x3ebf0af54bb9ae <<< 60) ||| 0x6ab7f2db8b5d2d7)) <<< 240) ||| ((((0x4b41acc2b1c2c2c <<< 60) ||| 0xaefab50abc17bca) <<< 120) ||| ((0x9d2a06a77a97ea4 <<< 60) ||| 0xb28cc5d0a8509f8)))) <<< 1020) ||| ((((((((((0xa79e9da27689c92 <<< 60) ||| 0x6e09a726665ef17) <<< 60) ||| 0xbc7ba1ea49819e3) <<< 120) ||| ((0x696d257094b24be <<< 60) ||| 0x91419fa8ffa3ac6)) <<< 240) ||| ((((0x3a23848c917428c <<< 60) ||| 0x922ee8a3a212869) <<< 120) ||| ((0x2152539a0d6816a <<< 60) ||| 0x84dd1f9a7cb1e))) <<< 480) ||| ((((((0xe87a90df23539e3 <<< 60) ||| 0x67721d7674c9ce0) <<< 120) ||| ((0x71c9c046e21b1a6 <<< 60) ||| 0xae9a4c67e998c64)) <<< 240) ||| ((((0xe98e86259134614 <<< 60) ||| 0x97f25ef176a5d09) <<< 120) ||| ((0x6e25a0960656615 <<< 60) ||| 0x4653994784ff13b))))))) else ((((((((((((((0x2801 <<< 60) ||| 0xe0441e092014a00) <<< 60) ||| 0x64a07324040061e) <<< 120) ||| ((0x2b301489400ebb2 <<< 60) ||| 0xe648005cc932ad0)) <<< 300) ||| ((((((0x2ee06040021774 <<< 60) ||| 0x4020010a012e606) <<< 60) ||| 0x450096508cc046) <<< 120) ||| ((0x80762bca0018ea <<< 60) ||| 0xd283033b2c40044))) <<< 600) ||| ((((((((0xe03941eccd10010 <<< 60) ||| 0x10501ca0018cac5) <<< 60) ||| 0x303132ce004030) <<< 120) ||| ((0x39a2659c007080c <<< 60) ||| 0x11158a0694100)) <<< 300) ||| ((((((0x238801b0266020 <<< 60) ||| 0xc78b38401cd1012) <<< 60) ||| 0xa23608033954404) <<< 120) ||| ((0x3ec8914008553b3 <<< 60) ||| 0x10454e240d5010)))) <<< 1200) ||| ((((((((((0x43449d94001d824 <<< 60) ||| 0x7cc240ce899400f) <<< 60) ||| 0x10481cbb334e004) <<< 120) ||| ((0x2c4a0c08bca1000 <<< 60) ||| 0x924025120445800)) <<< 300) ||| ((((((0x4664a0808e10498 <<< 60) ||| 0x450824125000) <<< 60) ||| 0x4612045c4053800) <<< 120) ||| ((0xe2408b89967001d <<< 60) ||| 0x6000208401b3282))) <<< 600) ||| ((((((((0x21048f2c480d99 <<< 60) ||| 0x73010840200043c) <<< 60) ||| 0xc0844a0228b1394) <<< 120) ||| ((0x840030a0094981 <<< 60) ||| 0x1420011292e6023)) <<< 300) ||| ((((((0x8414012e602301d <<< 60) ||| 0x8af2cd000c70606) <<< 60) ||| 0x2659a0068807665) <<< 120) ||| ((0xcc0e68021302029 <<< 60) ||| 0x420a000c8140c0c))))) <<< 2400) ||| ((((((((((((0x4cb3400e9818115 <<< 60) ||| 0x132cd0040a06100) <<< 60) ||| 0x1145134a080011) <<< 120) ||| ((0x806c09973010638 <<< 60) ||| 0x401b0466020c700)) <<< 300) ||| ((((((0x20084cc2818e945 <<< 60) ||| 0x310042001c58a1) <<< 60) ||| 0x3b329304040042a) <<< 120) ||| ((0x28311980829aa88 <<< 60) ||| 0x12215019a086880))) <<< 600) ||| ((((((((0x228855980cd044a <<< 60) ||| 0x606226aa02087cc) <<< 60) ||| 0x1012a10046540b3) <<< 120) ||| ((0x8022aa10080881 <<< 60) ||| 0x22aa05984011c28)) <<< 300) ||| ((((((0x2183100420016 <<< 60) ||| 0x5080404489372ec) <<< 60) ||| 0x20038e1c0cdcb1) <<< 120) ||| ((0xd132eccc1c08 <<< 60) ||| 0x29a00959941814a)))) <<< 1200) ||| ((((((((((0x2c2000e4804a1c0 <<< 60) ||| 0x88b00084b981011) <<< 60) ||| 0xc587220008a1d28) <<< 120) ||| ((0x200045161c0c405 <<< 60) ||| 0x3400e1c08b89966)) <<< 300) ||| ((((((0x801cc0002084002 <<< 60) ||| 0x3604021c6961c00) <<< 60) ||| 0x8d9980842058710) <<< 120) ||| ((0x42001858707b09 <<< 60) ||| 0x20200213281661))) <<< 600) ||| ((((((((0x450e24001cbb0 <<< 60) ||| 0x58421588040732a) <<< 60) ||| 0x63ec100412a571) <<< 120) ||| ((0x7039406c56ab34 <<< 60) ||| 0x42130210a80ab06)) <<< 300) ||| ((((((0x3e6040400808500 <<< 60) ||| 0x226ccc3e280040) <<< 60) ||| 0x47052b301122829) <<< 120) ||| ((0x59808a092800220 <<< 60) ||| 0x15d9730a0600703))))))))
def g127H9 (j : Nat) : Nat := (if j<3 then (if j<1 then ((((((((((((((((0x3024fa86 <<< 60) ||| 0x8d9bb53040000e8) <<< 60) ||| 0x10cf400000000ca) <<< 120) ||| ((0x80d970000000000 <<< 60) ||| 0x201fa077000083)) <<< 240) ||| ((((0x6b9e90000b23200 <<< 60) ||| 0x25ee00) <<< 120) ||| ((0x485a000000 <<< 60) ||| 0x0))) <<< 540) ||| ((((((((0x706d0000e0 <<< 60) ||| 0xac000000023fe00) <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x49e1000086)) <<< 240) ||| ((((0x7a8588000000000 <<< 60) ||| 0x1ae800061456b) <<< 120) ||| ((0xb80000000000000 <<< 60) ||| 0x78caa68b46)))) <<< 1020) ||| ((((((((((0x51c0800085a600 <<< 60) ||| 0xb78000b28800) <<< 60) ||| 0x0) <<< 120) ||| ((0x396a9853000000 <<< 60) ||| 0xf29000)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x9) <<< 120) ||| ((0x388b48000000000 <<< 60) ||| 0x3b6000000))) <<< 480) ||| ((((((0xa61600 <<< 60) ||| 0x34e13235015400) <<< 120) ||| ((0x1e9 <<< 60) ||| 0x80000000000144)) <<< 240) ||| ((((0x9c0000000000000 <<< 60) ||| 0x19516e5e9) <<< 120) ||| ((0x600000000276aa4 <<< 60) ||| 0xcc0006205000000))))) <<< 2040) ||| ((((((((((((0x1cd <<< 60) ||| 0x800006118942200) <<< 60) ||| 0x14f49b12000040) <<< 120) ||| ((0x40000000095a000 <<< 60) ||| 0x784a000000)) <<< 240) ||| ((((0x294d91860001ef <<< 60) ||| 0x7c877000000006c) <<< 120) ||| ((0x8c00012f500006d <<< 60) ||| 0xd400000000000a4))) <<< 480) ||| ((((((0xac00000000001a6 <<< 60) ||| 0x300000000000049) <<< 120) ||| ((0x900004130000000 <<< 60) ||| 0x1a79d69400)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0x1c35094d000000 <<< 60) ||| 0xb4ea00)))) <<< 1020) ||| ((((((((((0x0 <<< 60) ||| 0x6252000000) <<< 60) ||| 0xa63c00) <<< 120) ||| ((0x802c00 <<< 60) ||| 0xf3fc04)) <<< 240) ||| ((((0xd40000000000000 <<< 60) ||| 0x1efcf) <<< 120) ||| ((0x58000614c000000 <<< 60) ||| 0x45fb9ecf0de00))) <<< 480) ||| ((((((0x707800 <<< 60) ||| 0x0) <<< 120) ||| ((0xf72204 <<< 60) ||| 0x740007218c30800)) <<< 240) ||| ((((0x5a38000853e00 <<< 60) ||| 0x1074000045) <<< 120) ||| ((0x600000000000000 <<< 60) ||| 0x31e28361900800)))))) <<< 4080) ||| ((((((((((((((0x0 <<< 60) ||| 0x0) <<< 60) ||| 0x7b1ba546eb) <<< 120) ||| ((0xe9da959a5000000 <<< 60) ||| 0x13e00)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x48fe000000) <<< 120) ||| ((0x4a <<< 60) ||| 0x559197114253240))) <<< 480) ||| ((((((0x940000000000000 <<< 60) ||| 0x0) <<< 120) ||| ((0xab <<< 60) ||| 0x900000000255000)) <<< 240) ||| ((((0x29ad5023000000 <<< 60) ||| 0x84e200) <<< 120) ||| ((0x0 <<< 60) ||| 0x1832a1f7e1562e)))) <<< 1020) ||| ((((((((((0x32196ca60000000 <<< 60) ||| 0x0) <<< 60) ||| 0x23a600) <<< 120) ||| ((0x0 <<< 60) ||| 0x20b342a4915c00)) <<< 240) ||| ((((0x3c6c8000000000 <<< 60) ||| 0x126d27d000) <<< 120) ||| ((0x39cb8000000000 <<< 60) ||| 0x24fc8e))) <<< 480) ||| ((((((0x7c000000000012c <<< 60) ||| 0x200005268319800) <<< 120) ||| ((0x180e0000000000 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x2acc000000 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0xd52400))))) <<< 2040) ||| ((((((((((((0xe36800 <<< 60) ||| 0x94e8000000087) <<< 60) ||| 0xcc000000000008b) <<< 120) ||| ((0x8dd6e8000000000 <<< 60) ||| 0x140)) <<< 240) ||| ((((0x200005294121265 <<< 60) ||| 0x4b5ea8000335600) <<< 120) ||| ((0x59b00001eb <<< 60) ||| 0x28000000071c189))) <<< 480) ||| ((((((0x3c0000000044000 <<< 60) ||| 0x217c1055000000) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x49b1000000 <<< 60) ||| 0x35bfd0b2000000) <<< 120) ||| ((0x1246000000 <<< 60) ||| 0x5203e771a8)))) <<< 1020) ||| ((((((((((0xac0003ad8f1f466 <<< 60) ||| 0xfc000788b000000) <<< 60) ||| 0x24db8000303eab) <<< 120) ||| ((0x6812ab081710510 <<< 60) ||| 0x20019030104451)) <<< 240) ||| ((((0x4100110624059 <<< 60) ||| 0x110240707114911) <<< 120) ||| ((0x100310000301022 <<< 60) ||| 0x1000000583))) <<< 480) ||| ((((((0x700001107032370 <<< 60) ||| 0x500001021090042) <<< 120) ||| ((0x102004001071002 <<< 60) ||| 0x103013001900104)) <<< 240) ||| ((((0x63100130011000 <<< 60) ||| 0x100100000100020) <<< 120) ||| ((0x25013000360011 <<< 60) ||| 0x744ec400041004))))))) else (if j<2 then ((((((((((((((((0xa <<< 60) ||| 0x720000000000018) <<< 60) ||| 0xd20000000181c68) <<< 120) ||| ((0x3a0001aaab16e00 <<< 60) ||| 0x1a)) <<< 240) ||| ((((0x2900006a6800010 <<< 60) ||| 0xbb0000000000000) <<< 120) ||| ((0x0 <<< 60) ||| 0x68))) <<< 480) ||| ((((((0x9e0001aa894db7a <<< 60) ||| 0x8e0000ae6f16262) <<< 120) ||| ((0xe90000000197680 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x10ec80 <<< 60) ||| 0x4612000000000) <<< 120) ||| ((0xc4ec0006a <<< 60) ||| 0x270000000000000)))) <<< 1020) ||| ((((((((((0x704400011d3b0 <<< 60) ||| 0xe60000c31800000) <<< 60) ||| 0x1a) <<< 120) ||| ((0x8b000000031ed80 <<< 60) ||| 0x1250c00000)) <<< 240) ||| ((((0x48a80 <<< 60) ||| 0x11000000) <<< 120) ||| ((0x356452 <<< 60) ||| 0x23e3f2000000000))) <<< 480) ||| ((((((0x0 <<< 60) ||| 0x5d400000) <<< 120) ||| ((0x419c000000053 <<< 60) ||| 0xaff58e000000000)) <<< 240) ||| ((((0x1560e99c00000 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x0))))) <<< 2040) ||| ((((((((((((0x2596000000019 <<< 60) ||| 0x8d000008a800000) <<< 60) ||| 0x0) <<< 120) ||| ((0x8 <<< 60) ||| 0x560000000000000)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x1a38400022) <<< 120) ||| ((0xd7848e000000000 <<< 60) ||| 0x72e6a60000000))) <<< 480) ||| ((((((0xea3400000 <<< 60) ||| 0x1820000058) <<< 120) ||| ((0xed52e000000000 <<< 60) ||| 0xb)) <<< 240) ||| ((((0x4057886cd000000 <<< 60) ||| 0xacfc00000) <<< 120) ||| ((0x0 <<< 60) ||| 0x381890)))) <<< 1020) ||| ((((((((((0x4d0000000000013 <<< 60) ||| 0x530000ed9800000) <<< 60) ||| 0x96b2000000000) <<< 120) ||| ((0x82bc00000003a <<< 60) ||| 0x222ee0002d8371)) <<< 240) ||| ((((0xa0000045800000 <<< 60) ||| 0x1df65b) <<< 120) ||| ((0x70000000014300 <<< 60) ||| 0x695000000))) <<< 480) ||| ((((((0x11 <<< 60) ||| 0x2f4666000095780) <<< 120) ||| ((0xa79b08700 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x3a <<< 60) ||| 0xc06c6000000023) <<< 120) ||| ((0xce0000ef8e8c180 <<< 60) ||| 0x129200031e080)))))) <<< 4080) ||| ((((((((((((((0x0 <<< 60) ||| 0x0) <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x105c80)) <<< 240) ||| ((((0x1865c00000 <<< 60) ||| 0x243e63230228a) <<< 120) ||| ((0xfd547e00000004a <<< 60) ||| 0xb80000000000069))) <<< 480) ||| ((((((0x1b866decd400000 <<< 60) ||| 0x0) <<< 120) ||| ((0x23b559800 <<< 60) ||| 0x107c9d5f80)) <<< 240) ||| ((((0x18f7000030 <<< 60) ||| 0x830000000099150) <<< 120) ||| ((0x4ca2c8000040e80 <<< 60) ||| 0x0)))) <<< 1020) ||| ((((((((((0x4ea80 <<< 60) ||| 0xb) <<< 60) ||| 0x180000000000043) <<< 120) ||| ((0x1900012e4c0001a <<< 60) ||| 0x87000000000003a)) <<< 240) ||| ((((0x8c000000000000a <<< 60) ||| 0x248211c0a5001e8) <<< 120) ||| ((0x6742ba000099f00 <<< 60) ||| 0x50288eec0004b))) <<< 480) ||| ((((((0x6d0000000086222 <<< 60) ||| 0x6a0000000297508) <<< 120) ||| ((0x590000cd6000000 <<< 60) ||| 0xe46e00021a100)) <<< 240) ||| ((((0x60 <<< 60) ||| 0xd9772000000000) <<< 120) ||| ((0x0 <<< 60) ||| 0x0))))) <<< 2040) ||| ((((((((((((0x0 <<< 60) ||| 0x812328f400000) <<< 60) ||| 0xc65e000000000) <<< 120) ||| ((0x8dc147480 <<< 60) ||| 0x1cae80006b)) <<< 240) ||| ((((0x540000000000000 <<< 60) ||| 0x96bc000000001) <<< 120) ||| ((0x980000000000008 <<< 60) ||| 0xe20000000053d80))) <<< 480) ||| ((((((0xb1e868ec00009 <<< 60) ||| 0xe0000143601d1fa) <<< 120) ||| ((0x76139185e74ad80 <<< 60) ||| 0xd38e00000007b)) <<< 240) ||| ((((0x3a00000003483ba <<< 60) ||| 0xb0000000000000) <<< 120) ||| ((0x41e60001d2080 <<< 60) ||| 0x22)))) <<< 1020) ||| ((((((((((0x78434000000000 <<< 60) ||| 0xe42c000000040) <<< 60) ||| 0x2d0000450a53980) <<< 120) ||| ((0x21cd00 <<< 60) ||| 0x12)) <<< 240) ||| ((((0x5912fc847000000 <<< 60) ||| 0x825c000000000) <<< 120) ||| ((0x0 <<< 60) ||| 0x28e000))) <<< 480) ||| ((((((0x249a00 <<< 60) ||| 0x22c6a1c800000) <<< 120) ||| ((0x44780 <<< 60) ||| 0x14b9400000)) <<< 240) ||| ((((0x0 <<< 60) ||| 0xe099d4f00) <<< 120) ||| ((0x1497400069 <<< 60) ||| 0x7a000145d000032))))))) else ((((((((((((((((0x2d2b800000010 <<< 60) ||| 0xd040000000e3160) <<< 60) ||| 0x90a000000000) <<< 120) ||| ((0x0 <<< 60) ||| 0x49de00000)) <<< 240) ||| ((((0x1c <<< 60) ||| 0x1c40001155471f6) <<< 120) ||| ((0x92c000221797840 <<< 60) ||| 0x4))) <<< 480) ||| ((((((0x58797e02ac00000 <<< 60) ||| 0x0) <<< 120) ||| ((0x726c00000 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x0 <<< 60) ||| 0xf6e82) <<< 120) ||| ((0x3ac00022d900014 <<< 60) ||| 0x26c00022be00002)))) <<< 1020) ||| ((((((((((0xa04000000000000 <<< 60) ||| 0x72e08) <<< 60) ||| 0xc0cd3f800026972) <<< 120) ||| ((0x24c000000000000 <<< 60) ||| 0x398a800000000)) <<< 240) ||| ((((0x1d61800000000 <<< 60) ||| 0x158b729c81580) <<< 120) ||| ((0x1b0d53942 <<< 60) ||| 0x16000059fd00000))) <<< 480) ||| ((((((0x3461a3bd12be0 <<< 60) ||| 0x23e500000) <<< 120) ||| ((0x4b5c00000 <<< 60) ||| 0x1176000000000)) <<< 240) ||| ((((0x298620a900016 <<< 60) ||| 0x8d000000000000a) <<< 120) ||| ((0x6a4000000000000 <<< 60) ||| 0xc56a0))))) <<< 1980) ||| ((((((((((((0x0 <<< 60) ||| 0x2d0f000000010) <<< 60) ||| 0x5db4b4000000004) <<< 120) ||| ((0x5b4000000000002 <<< 60) ||| 0x688000718800004)) <<< 240) ||| ((((0x84000000000000 <<< 60) ||| 0x18) <<< 120) ||| ((0x3f1839800000018 <<< 60) ||| 0x94c00071900001e))) <<< 480) ||| ((((((0x21c0002bd000000 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x2817000000018)) <<< 240) ||| ((((0x4a0000000032e34 <<< 60) ||| 0x714000706c00000) <<< 120) ||| ((0x27040 <<< 60) ||| 0xb4b40)))) <<< 960) ||| ((((((((0x0 <<< 60) ||| 0xa4f44) <<< 120) ||| ((0xe79d240000472c6 <<< 60) ||| 0xae400000000001a)) <<< 240) ||| ((((0x31400000000001c <<< 60) ||| 0xdea4ed2b9400000) <<< 120) ||| ((0x203dc4940 <<< 60) ||| 0x25cc000000000))) <<< 480) ||| ((((((0x2cf8000000000 <<< 60) ||| 0x39d580000000c) <<< 120) ||| ((0x2d0000000000016 <<< 60) ||| 0xaec00000000000a)) <<< 240) ||| ((((0xcb1461380600000 <<< 60) ||| 0x366e0) <<< 120) ||| ((0x607a00000 <<< 60) ||| 0xdbc8000a6152)))))) <<< 4020) ||| ((((((((((((((0xe9400000000000a <<< 60) ||| 0x5b2460800000014) <<< 60) ||| 0xa240000000e620a) <<< 120) ||| ((0xc6800022b400000 <<< 60) ||| 0x2d7dfb1100000)) <<< 240) ||| ((((0x39e6000000012 <<< 60) ||| 0xa429778000f5560) <<< 120) ||| ((0x1833000000000 <<< 60) ||| 0x31420))) <<< 480) ||| ((((((0x8e7000000000 <<< 60) ||| 0x35c20) <<< 120) ||| ((0x63250001a <<< 60) ||| 0xe1b05f000000000)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x34e6000000000) <<< 120) ||| ((0x0 <<< 60) ||| 0xa3320)))) <<< 1020) ||| ((((((((((0x1cbe000000000 <<< 60) ||| 0x535a0) <<< 60) ||| 0x18a5418e60160) <<< 120) ||| ((0x243f000000000 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x1b1388800000 <<< 60) ||| 0x31ba00000) <<< 120) ||| ((0x0 <<< 60) ||| 0x0))) <<< 480) ||| ((((((0x594b0001c <<< 60) ||| 0xaccd9043a000000) <<< 120) ||| ((0x83c000000000000 <<< 60) ||| 0x6249941a0)) <<< 240) ||| ((((0x8e6800000000 <<< 60) ||| 0x4) <<< 120) ||| ((0x650000000024be0 <<< 60) ||| 0x184e00003761e))))) <<< 1980) ||| ((((((((((((0x150d59000077862 <<< 60) ||| 0xb000000000001a) <<< 60) ||| 0x2c0000000000000) <<< 120) ||| ((0x0 <<< 60) ||| 0x2080)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x10c480000000a) <<< 120) ||| ((0x4a4000000047920 <<< 60) ||| 0x1fcd7a609500000))) <<< 480) ||| ((((((0x90640 <<< 60) ||| 0x87d2e) <<< 120) ||| ((0x72c000000000000 <<< 60) ||| 0x1a)) <<< 240) ||| ((((0x2d6f000000000 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x193c510600000)))) <<< 960) ||| ((((((((0x9498000a76e0 <<< 60) ||| 0x0) <<< 120) ||| ((0x13be30b90 <<< 60) ||| 0x9d0000000000000)) <<< 240) ||| ((((0x10 <<< 60) ||| 0x888000628300000) <<< 120) ||| ((0x0 <<< 60) ||| 0x8))) <<< 480) ||| ((((((0xc7c00011b500000 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x24b28000d1ec0)) <<< 240) ||| ((((0x102580000000e <<< 60) ||| 0x74400011b900014) <<< 120) ||| ((0x144804800000000 <<< 60) ||| 0x963000036f60))))))))) else (if j<4 then ((((((((((((((((0x4 <<< 60) ||| 0x8b3a37600000005) <<< 60) ||| 0xa910001e0574760) <<< 120) ||| ((0x1c5ff52f0 <<< 60) ||| 0xb6ad4a000003)) <<< 240) ||| ((((0x884000000000000 <<< 60) ||| 0x0) <<< 120) ||| ((0x61e40003 <<< 60) ||| 0xb0e000000000000))) <<< 540) ||| ((((((((0xb7a600000000 <<< 60) ||| 0x128bc0000) <<< 60) ||| 0x0) <<< 120) ||| ((0x1c7d8 <<< 60) ||| 0xabc00003)) <<< 240) ||| ((((0xbb273c600000000 <<< 60) ||| 0x2027e4f79be0) <<< 120) ||| ((0x3d1c0 <<< 60) ||| 0x1ef500000)))) <<< 1020) ||| ((((((((((0x7670000191f0 <<< 60) ||| 0x2) <<< 60) ||| 0x849469166cc0000) <<< 120) ||| ((0x0 <<< 60) ||| 0x2ded0)) <<< 240) ||| ((((0x10bd8 <<< 60) ||| 0x32a600000000) <<< 120) ||| ((0xa4e6880d <<< 60) ||| 0xba482228240cf38))) <<< 480) ||| ((((((0x35988 <<< 60) ||| 0x1) <<< 120) ||| ((0x2a6000188e80003 <<< 60) ||| 0x923000000000000)) <<< 240) ||| ((((0x451f08840000 <<< 60) ||| 0x0) <<< 120) ||| ((0xf57800000001 <<< 60) ||| 0x3430001a64a9ce8))))) <<< 2040) ||| ((((((((((((0x1a7400000 <<< 60) ||| 0x212ce1e00000) <<< 60) ||| 0x0) <<< 120) ||| ((0x49700000 <<< 60) ||| 0x3ad714dc10c0000)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x18088) <<< 120) ||| ((0x0 <<< 60) ||| 0xb46000000000002))) <<< 480) ||| ((((((0xf802b800000000 <<< 60) ||| 0x8382070c0007) <<< 120) ||| ((0x17863d400000000 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x201f0) <<< 120) ||| ((0x516acdad532a <<< 60) ||| 0x8f0b38cce200000)))) <<< 1020) ||| ((((((((((0xe4028995 <<< 60) ||| 0x85793ec00000006) <<< 60) ||| 0x802c3c800000006) <<< 120) ||| ((0xa63000167d018a3 <<< 60) ||| 0xacf00000003d548)) <<< 240) ||| ((((0x4f9b45e8 <<< 60) ||| 0x3cf908c0f2c0000) <<< 120) ||| ((0x1847c0000 <<< 60) ||| 0x14d60))) <<< 480) ||| ((((((0x0 <<< 60) ||| 0x47ec0000) <<< 120) ||| ((0xc29c00000000 <<< 60) ||| 0x147940000)) <<< 240) ||| ((((0xd341ccf40002 <<< 60) ||| 0x19bb03def880003) <<< 120) ||| ((0x8190204000182e8 <<< 60) ||| 0x0)))))) <<< 4080) ||| ((((((((((((((0x1eb170300 <<< 60) ||| 0x26ae23c80000) <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x374400000000)) <<< 240) ||| ((((0x112b0 <<< 60) ||| 0x669e635dc720) <<< 120) ||| ((0x6 <<< 60) ||| 0x3995aca0db03a8))) <<< 480) ||| ((((((0x225808a00000 <<< 60) ||| 0x270b43540000) <<< 120) ||| ((0x103780004 <<< 60) ||| 0x39c000000000004)) <<< 240) ||| ((((0x812000000000000 <<< 60) ||| 0x9ca8) <<< 120) ||| ((0x34de00000000 <<< 60) ||| 0x5)))) <<< 1020) ||| ((((((((((0x377000000000000 <<< 60) ||| 0xd2b200000000) <<< 60) ||| 0x86e783f40005) <<< 120) ||| ((0x2c1000000030b5e <<< 60) ||| 0x244000000000000)) <<< 240) ||| ((((0x34b38 <<< 60) ||| 0xf800000006) <<< 120) ||| ((0x863000000000005 <<< 60) ||| 0x956000000000000))) <<< 480) ||| ((((((0x0 <<< 60) ||| 0x142a046b5) <<< 120) ||| ((0x91a570000000007 <<< 60) ||| 0x2a0000e1b80002)) <<< 240) ||| ((((0x1fc000000000000 <<< 60) ||| 0x25648) <<< 120) ||| ((0xd27e00000000 <<< 60) ||| 0x775800000000))))) <<< 2040) ||| ((((((((((((0xd77fc77c0000 <<< 60) ||| 0x1e53fc278) <<< 60) ||| 0x18ea7d3b8) <<< 120) ||| ((0x2 <<< 60) ||| 0xbb386a0a8b78ce8)) <<< 240) ||| ((((0xa40243240000 <<< 60) ||| 0x6) <<< 120) ||| ((0xbb10001e1480000 <<< 60) ||| 0x1cba303da))) <<< 480) ||| ((((((0x85b1124000198b8 <<< 60) ||| 0x1c7700000) <<< 120) ||| ((0xe2dc0007 <<< 60) ||| 0xbe4349800000003)) <<< 240) ||| ((((0x3e1000000000000 <<< 60) ||| 0x347c8) <<< 120) ||| ((0x1 <<< 60) ||| 0xa269800000000)))) <<< 1020) ||| ((((((((((0x324a00000000 <<< 60) ||| 0x186bb5710) <<< 60) ||| 0xd6df865b8740) <<< 120) ||| ((0x210aa187995b <<< 60) ||| 0x34d0001e4780000)) <<< 240) ||| ((((0x439e00000000 <<< 60) ||| 0x0) <<< 120) ||| ((0x4ea0 <<< 60) ||| 0x0))) <<< 480) ||| ((((((0x3 <<< 60) ||| 0x2a1000000000000) <<< 120) ||| ((0x0 <<< 60) ||| 0xf1bb67d40000)) <<< 240) ||| ((((0x350a00000000 <<< 60) ||| 0x1c0a00005) <<< 120) ||| ((0xa43000000000000 <<< 60) ||| 0x38120))))))) else (if j<5 then ((((((((((((((((0x48f5b040 <<< 60) ||| 0xe06800000005134) <<< 60) ||| 0x5ac20392) <<< 120) ||| ((0x1d1300000000 <<< 60) ||| 0x34b100000000)) <<< 240) ||| ((((0xe87000000000000 <<< 60) ||| 0xca400000000000) <<< 120) ||| ((0xd9c80000000 <<< 60) ||| 0x730a))) <<< 540) ||| ((((((((0xe8400000000000 <<< 60) ||| 0x1) <<< 60) ||| 0x860800013890000) <<< 120) ||| ((0xe580000283b0001 <<< 60) ||| 0xa49ad5280000000)) <<< 240) ||| ((((0x52000000 <<< 60) ||| 0x208a2750) <<< 120) ||| ((0x150a80007370 <<< 60) ||| 0xe78800000000000)))) <<< 1020) ||| ((((((((((0x2573b37e956e <<< 60) ||| 0x0) <<< 60) ||| 0x3d3480000000) <<< 120) ||| ((0x0 <<< 60) ||| 0x91ce)) <<< 240) ||| ((((0x22b6333e <<< 60) ||| 0x63d10000) <<< 120) ||| ((0x31b8 <<< 60) ||| 0x99800000000000))) <<< 480) ||| ((((((0x2b441b3a8efc323 <<< 60) ||| 0x6848000005034c2) <<< 120) ||| ((0x51db0000 <<< 60) ||| 0xca2abae0000)) <<< 240) ||| ((((0x4901c1a00000000 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x0))))) <<< 2040) ||| ((((((((((((0x119380000000 <<< 60) ||| 0x651800000000000) <<< 60) ||| 0x53c70000) <<< 120) ||| ((0x1cd380000000 <<< 60) ||| 0xa8414c51bcd0000)) <<< 240) ||| ((((0xeb8000000000000 <<< 60) ||| 0x3056f0a5f6f1) <<< 120) ||| ((0x62395ef0000f224 <<< 60) ||| 0x1))) <<< 480) ||| ((((((0xe81800000000000 <<< 60) ||| 0x34be80000000) <<< 120) ||| ((0x1 <<< 60) ||| 0xe8f111280000000)) <<< 240) ||| ((((0x289de5be <<< 60) ||| 0x44b80000000) <<< 120) ||| ((0x299a0000 <<< 60) ||| 0xabf905b00000000)))) <<< 1020) ||| ((((((((((0x21c000072a79688 <<< 60) ||| 0x6bd96133) <<< 60) ||| 0x864c00000000000) <<< 120) ||| ((0x389d00000000 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x15790000019e <<< 60) ||| 0x42130000) <<< 120) ||| ((0x8568000000026d0 <<< 60) ||| 0x2c02931c61d4))) <<< 480) ||| ((((((0x18890001 <<< 60) ||| 0xc9448e200000000) <<< 120) ||| ((0xd50000a692 <<< 60) ||| 0x0)) <<< 240) ||| ((((0x2bd800018e50000 <<< 60) ||| 0x0) <<< 120) ||| ((0x20f880000000 <<< 60) ||| 0xced0caa60d4a504)))))) <<< 4080) ||| ((((((((((((((0x0 <<< 60) ||| 0x4dc400000000000) <<< 60) ||| 0x35c380000000) <<< 120) ||| ((0x62340006ba62412 <<< 60) ||| 0x3ae623d6)) <<< 240) ||| ((((0x690b0000 <<< 60) ||| 0x6d2) <<< 120) ||| ((0x0 <<< 60) ||| 0x6e36c5c2af90000))) <<< 480) ||| ((((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0x60df0000 <<< 60) ||| 0xd706)) <<< 240) ||| ((((0x46d8000f0c4 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x300380000001)))) <<< 1020) ||| ((((((((((0x84c40000000b4d6 <<< 60) ||| 0x0) <<< 60) ||| 0x6b8b0000) <<< 120) ||| ((0x159400000000 <<< 60) ||| 0x63ddb147)) <<< 240) ||| ((((0x8caac9500000001 <<< 60) ||| 0xc9b800000006130) <<< 120) ||| ((0x0 <<< 60) ||| 0x58100000000))) <<< 480) ||| ((((((0x606000060a00000 <<< 60) ||| 0x1) <<< 120) ||| ((0xc6bc00051bd0000 <<< 60) ||| 0x13920001)) <<< 240) ||| ((((0xe108980aa3920d2 <<< 60) ||| 0x10008000c082) <<< 120) ||| ((0x2f5c00000000000 <<< 60) ||| 0x42f293c23f0))))) <<< 2040) ||| ((((((((((((0x96b6 <<< 60) ||| 0x84b780780000000) <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0xa44c000038e508e)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x434400000000000) <<< 120) ||| ((0x1 <<< 60) ||| 0x877d1600000000))) <<< 480) ||| ((((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0x250700000000 <<< 60) ||| 0x390ca036)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x396dd9dd0000) <<< 120) ||| ((0x19d562848196 <<< 60) ||| 0x3c460000e3ac)))) <<< 1020) ||| ((((((((((0x4957b6aa <<< 60) ||| 0x4bac0000ab1022e) <<< 60) ||| 0xcee8000000023dc) <<< 120) ||| ((0x286980000000 <<< 60) ||| 0x9b562980000)) <<< 240) ||| ((((0xe91400000000000 <<< 60) ||| 0x0) <<< 120) ||| ((0x1 <<< 60) ||| 0x24d800000000000))) <<< 480) ||| ((((((0x337d0000 <<< 60) ||| 0x5440000000b410) <<< 120) ||| ((0x19f000000000 <<< 60) ||| 0x610546c8)) <<< 240) ||| ((((0x482fe242 <<< 60) ||| 0x2df580000001) <<< 120) ||| ((0xa50685e7a360000 <<< 60) ||| 0xecf000028860000))))))) else ((((((((((((((0x3989 <<< 60) ||| 0xdad47643076309c) <<< 60) ||| 0x0) <<< 180) ||| ((((0x735f00000000000 <<< 60) ||| 0x0) <<< 60) ||| 0x732400000000000)) <<< 300) ||| ((((((0x0 <<< 60) ||| 0xacd0001ee10000) <<< 60) ||| 0x62bd00000000000) <<< 120) ||| ((0x0 <<< 60) ||| 0x22ff00004f20000))) <<< 660) ||| ((((((((0x796e00000000000 <<< 60) ||| 0x2903460000010de) <<< 60) ||| 0x160c0000) <<< 180) ||| ((((0x2bc000 <<< 60) ||| 0x731d0000e748000) <<< 60) ||| 0xa63c000)) <<< 300) ||| ((((((0x481700000001441 <<< 60) ||| 0x84e67140000000) <<< 60) ||| 0xa26f44839e3) <<< 120) ||| ((0x15a40003119 <<< 60) ||| 0x800000000000000)))) <<< 1320) ||| ((((((((((0x60ff404e00024f6 <<< 60) ||| 0x800000000000000) <<< 60) ||| 0x0) <<< 180) ||| ((((0x3b05e55a0000000 <<< 60) ||| 0x336c33ae8828000) <<< 60) ||| 0x6a8a00000002193)) <<< 300) ||| ((((((0x0 <<< 60) ||| 0x0) <<< 60) ||| 0x496c000) <<< 120) ||| ((0x5b9900000000000 <<< 60) ||| 0x486800000000000))) <<< 660) ||| ((((((((0x0 <<< 60) ||| 0x0) <<< 60) ||| 0x327050fa0002187) <<< 180) ||| ((((0xa93e0001c684000 <<< 60) ||| 0x800000000) <<< 60) ||| 0xd06e00038d3)) <<< 300) ||| ((((((0x20c700000691491 <<< 60) ||| 0x70c000000000000) <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x8a466ca0000000))))) <<< 2580) ||| ((((((((((((0x0 <<< 60) ||| 0x2af300000000000) <<< 60) ||| 0x6dceb38000) <<< 180) ||| ((((0xe2d40000000 <<< 60) ||| 0x0) <<< 60) ||| 0x78e300000000000)) <<< 300) ||| ((((((0x480c0001212001a <<< 60) ||| 0x800000000000000) <<< 60) ||| 0x978) <<< 120) ||| ((0x890d000047e8000 <<< 60) ||| 0x1ac077cfe940000))) <<< 660) ||| ((((((((0x43decf02053 <<< 60) ||| 0x8000000188c4000) <<< 60) ||| 0x16760000000) <<< 180) ||| ((((0x7b4e62e40000000 <<< 60) ||| 0x0) <<< 60) ||| 0x1288c0bf28b8000)) <<< 300) ||| ((((((0x521b20c80000000 <<< 60) ||| 0x0) <<< 60) ||| 0x49be00000000000) <<< 120) ||| ((0xf28e0000000 <<< 60) ||| 0x0)))) <<< 1260) ||| ((((((((((0x29e5 <<< 60) ||| 0x87780000000) <<< 60) ||| 0x0) <<< 180) ||| ((((0x142e8000 <<< 60) ||| 0x255c0000000) <<< 60) ||| 0x11e20000000)) <<< 300) ||| ((((((0x22190001e500000 <<< 60) ||| 0x11a800000000000) <<< 60) ||| 0xc33694b) <<< 120) ||| ((0xc671035 <<< 60) ||| 0x800000014988d99))) <<< 600) ||| ((((((((0x187000080cd44a <<< 60) ||| 0x90f0000e1d8000) <<< 60) ||| 0x71500000a6c8000) <<< 120) ||| ((0x73eaf7b00000000 <<< 60) ||| 0x10d44000)) <<< 300) ||| ((((((0x0 <<< 60) ||| 0x4f80002126) <<< 60) ||| 0xd91000000000000) <<< 120) ||| ((0x10e40000 <<< 60) ||| 0x612400000003068)))))))))
def g127D10 (j : Nat) : Nat := ((((((((((0xc2c4005 <<< 60) ||| 0x9812882c4b052a6) <<< 120) ||| ((0x47b6e2e598a1ad <<< 60) ||| 0xba52ac2c62cab6e)) <<< 180) ||| ((((0x96c98020d306385 <<< 60) ||| 0xb6e94b28a38a100) <<< 60) ||| 0x14b05822e2ca12c)) <<< 420) ||| ((((((0x98508124b00e944 <<< 60) ||| 0x98a1cb3a5b042a6) <<< 120) ||| ((0x1c42ca20eb05981 <<< 60) ||| 0x2452803a512c2c8)) <<< 180) ||| ((((0x28b125b263872c0 <<< 60) ||| 0x12598d2872ca125) <<< 60) ||| 0xb2634710b288b05))) <<< 840) ||| ((((((((0x366049280125b0d <<< 60) ||| 0x2c728b125b26347) <<< 120) ||| ((0x2ca065b26107190 <<< 60) ||| 0x125b0d18c444966)) <<< 180) ||| ((((0x346fc3c0e5b6ccd <<< 60) ||| 0xaf4afa8294a2279) <<< 60) ||| 0x9b060150480e42d)) <<< 420) ||| ((((((0x841502a003ff65 <<< 60) ||| 0xff597ff64ff993f) <<< 120) ||| ((0xd64ff193fe54ff5 <<< 60) ||| 0x53ff63ff58ffd53)) <<< 180) ||| ((((0xffd0ffd43ffd83f <<< 60) ||| 0xd60ff543ff40ff5) <<< 60) ||| 0x3fd30fb483f510))))
def g127H10 (j : Nat) : Nat := (if j<1 then ((((((((((((((((0x1cfc00 <<< 60) ||| 0x46230c80000000) <<< 60) ||| 0x0) <<< 120) ||| ((0x55ca1 <<< 60) ||| 0xa0d9e00091b8000)) <<< 240) ||| ((((0x2e8000000000 <<< 60) ||| 0x350e0) <<< 120) ||| ((0x9390000000685 <<< 60) ||| 0x0))) <<< 540) ||| ((((((((0x12740000 <<< 60) ||| 0x1cb702f83e) <<< 60) ||| 0x304c00000000008) <<< 120) ||| ((0xc0000000003dee <<< 60) ||| 0x745000000000)) <<< 240) ||| ((((0x4012118000000a <<< 60) ||| 0x600000000000000) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)))) <<< 1020) ||| ((((((((((0x1a4a000000000 <<< 60) ||| 0x7a00000000) <<< 60) ||| 0x20fa000) <<< 120) ||| ((0x0 <<< 60) ||| 0xd3364d9128)) <<< 240) ||| ((((0x2075a8 <<< 60) ||| 0x800000000051900) <<< 120) ||| ((0x12bc0000000000 <<< 60) ||| 0x668800000000))) <<< 480) ||| ((((((0xc4e0000001a9a0 <<< 60) ||| 0x0) <<< 120) ||| ((0x1f80 <<< 60) ||| 0x845a04000524c)) <<< 240) ||| ((((0xcf <<< 60) ||| 0x4000d71623c0000) <<< 120) ||| ((0x315da0a <<< 60) ||| 0x0))))) <<< 2040) ||| ((((((((((((0x0 <<< 60) ||| 0x0) <<< 60) ||| 0x1c50000d1d80000) <<< 120) ||| ((0x1c1c0003aac000 <<< 60) ||| 0x0)) <<< 240) ||| ((((0xc6803280000000 <<< 60) ||| 0x4c6000) <<< 120) ||| ((0x0 <<< 60) ||| 0x0))) <<< 480) ||| ((((((0x74168ac00 <<< 60) ||| 0x1ca8a6ba853d306) <<< 120) ||| ((0x380000000000000 <<< 60) ||| 0x8da00)) <<< 240) ||| ((((0x50e95200000000 <<< 60) ||| 0x0) <<< 120) ||| ((0x1c66000c1f00000 <<< 60) ||| 0x4570000000000)))) <<< 1020) ||| ((((((((((0xb5000000 <<< 60) ||| 0x0) <<< 60) ||| 0x518000000) <<< 120) ||| ((0x0 <<< 60) ||| 0x4608000)) <<< 240) ||| ((((0x16e4120800000 <<< 60) ||| 0xb32d92c0000) <<< 120) ||| ((0x35b58408188a3 <<< 60) ||| 0x84))) <<< 480) ||| ((((((0x45b720bb80dd238 <<< 60) ||| 0x6ab) <<< 120) ||| ((0x400000033fa19c0 <<< 60) ||| 0x1c8e0000000000)) <<< 240) ||| ((((0x721e92400000 <<< 60) ||| 0x17380000000000) <<< 120) ||| ((0x85b000 <<< 60) ||| 0x518c00000000000)))))) <<< 4080) ||| ((((((((((((((0x1b24 <<< 60) ||| 0x0) <<< 60) ||| 0xa3480000000) <<< 120) ||| ((0x0 <<< 60) ||| 0x3ba686a00000)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x1))) <<< 480) ||| ((((((0x8090000000000e2 <<< 60) ||| 0x1f1e11be40bc860) <<< 120) ||| ((0x74f <<< 60) ||| 0xe364ca200034580)) <<< 240) ||| ((((0x3 <<< 60) ||| 0x122aa147c800000) <<< 120) ||| ((0x0 <<< 60) ||| 0x72980018a9)))) <<< 1020) ||| ((((((((((0x185c00000000 <<< 60) ||| 0x0) <<< 60) ||| 0x10c800) <<< 120) ||| ((0xa5500000 <<< 60) ||| 0x413c000)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x169318953d22ec) <<< 120) ||| ((0x610003daa62f33b <<< 60) ||| 0x80000000b10006a))) <<< 480) ||| ((((((0xfc000000c4b8000 <<< 60) ||| 0xd6b000000) <<< 120) ||| ((0x7b00000000002 <<< 60) ||| 0x160002114000873)) <<< 240) ||| ((((0x8f400000000 <<< 60) ||| 0xad4001ca4a13a) <<< 120) ||| ((0x844000853000000 <<< 60) ||| 0x98b8ea72d00000))))) <<< 2040) ||| ((((((((((((0x1862 <<< 60) ||| 0x830d87515800) <<< 60) ||| 0x93580000000000) <<< 120) ||| ((0x39bc000161 <<< 60) ||| 0x80000016f600000)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x431c00) <<< 120) ||| ((0xc0d80000000 <<< 60) ||| 0x76c3a760ec000))) <<< 480) ||| ((((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0xd58008 <<< 60) ||| 0xc9e400000000024)) <<< 240) ||| ((((0xb000086dbb38000 <<< 60) ||| 0x3cc42600) <<< 120) ||| ((0x6c7 <<< 60) ||| 0x2cc01c000000000)))) <<< 1020) ||| ((((((((((0x1c000000045da2 <<< 60) ||| 0x57966c7c42001e0) <<< 60) ||| 0xd77000001) <<< 120) ||| ((0x6000000000083f8 <<< 60) ||| 0xf5000000097a000)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x1e710000) <<< 120) ||| ((0x1489683000000 <<< 60) ||| 0x502e66e4b00000))) <<< 480) ||| ((((((0x10e10004a9c000 <<< 60) ||| 0x8e6000595400000) <<< 120) ||| ((0x41e59a6cef9 <<< 60) ||| 0x6eb38d424000e52)) <<< 240) ||| ((((0x800046c05c10103 <<< 60) ||| 0x111000210401102) <<< 120) ||| ((0x200001142100083 <<< 60) ||| 0x31100221040004))))))) else ((((((((((0x500c <<< 60) ||| 0x574000000000000) <<< 120) ||| ((0x2d080 <<< 60) ||| 0xab8)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x1ab5d60000000) <<< 120) ||| ((0x1a0f000000 <<< 60) ||| 0xc2d5701bc00))) <<< 480) ||| ((((((0x146086438ab5ca <<< 60) ||| 0x46e926694800000) <<< 120) ||| ((0x2be0 <<< 60) ||| 0x2200000a2c000)) <<< 240) ||| ((((0x207800000000000 <<< 60) ||| 0x4150000000) <<< 120) ||| ((0x310000000 <<< 60) ||| 0x18a000000000002)))) <<< 960) ||| ((((((((0x7547d28e5ca8850 <<< 60) ||| 0x4a6c00000034) <<< 120) ||| ((0xa2bb40000000000 <<< 60) ||| 0x104000)) <<< 240) ||| ((((0x145200080c58d00 <<< 60) ||| 0x6178c35) <<< 120) ||| ((0x92176000000000 <<< 60) ||| 0x91200000004cd0))) <<< 480) ||| ((((((0x16af565 <<< 60) ||| 0x800359800000000) <<< 120) ||| ((0x1c03e300000000 <<< 60) ||| 0x68900051215b)) <<< 240) ||| ((((0xe000378aac80014 <<< 60) ||| 0x561213ad0000000) <<< 120) ||| ((0x5a34000000a2 <<< 60) ||| 0x7000000046d0000))))))
def g127D11 (j : Nat) : Nat := 0x1ae2b0c2ff
def g127H11 (j : Nat) : Nat := ((((((((0x81400000 <<< 60) ||| 0x0) <<< 60) ||| 0x7480000000000) <<< 180) ||| ((((0x0 <<< 60) ||| 0x53a340000308001) <<< 60) ||| 0x875040000000040)) <<< 360) ||| ((((((0x0 <<< 60) ||| 0x14430000b0a) <<< 60) ||| 0x5162c00139c6002) <<< 180) ||| ((((0xca00149000cc000 <<< 60) ||| 0x450) <<< 60) ||| 0x2830030f02c)))
def g127L : Nat → Packing
  | 5 => (6,6,5,0,0,0,0,g127D5)
  | 6 => (261,5,5,0,0,9,0,g127D6)
  | 7 => (1133,4,5,0,0,13,0,g127D7)
  | 8 => (1005,3,5,0,0,15,0,g127D8)
  | 9 => (251,2,5,0,0,14,0,g127D9)
  | 10 => (21,1,5,0,0,10,0,g127D10)
  | 11 => (1,0,5,0,0,0,0,g127D11)
  | _ => emptyPacking
def g127I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 25 0 8 3 1 g127H6
  | 7 => lookupWord 52 790 4 14 9 1 g127H7
  | 8 => lookupWord 226 6805 3 16 11 1 g127H8
  | 9 => lookupWord 201 3022 4 15 10 1 g127H9
  | 10 => lookupWord 50 760 4 13 8 1 g127H10
  | 11 => lookupWord 4 70 3 10 5 1 g127H11
  | _ => fun _ => none
def g127 : Forest := ⟨127,11,fun i => g127Y[i]?.getD (0,0),g127C,g127A,g127L,g127I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P5_0 : block g127 5 0 6=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B5 : block g127 5 0 6=true := g127P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P6_0 : block g127 6 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P6_2 : block g127 6 2 48=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P6_50 : block g127 6 50 48=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P6_98 : block g127 6 98 48=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P6_146 : block g127 6 146 48=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P6_194 : block g127 6 194 48=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P6_242 : block g127 6 242 19=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B6 : block g127 6 0 261=true := (@block_merge g127 6 0 98 163 (@block_merge g127 6 0 2 96 g127P6_0 (@block_merge g127 6 2 48 48 g127P6_2 g127P6_50)) (@block_merge g127 6 98 96 67 (@block_merge g127 6 98 48 48 g127P6_98 g127P6_146) (@block_merge g127 6 194 48 19 g127P6_194 g127P6_242)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_0 : block g127 7 0 4=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_4 : block g127 7 4 48=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_52 : block g127 7 52 48=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_100 : block g127 7 100 25=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_125 : block g127 7 125 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_173 : block g127 7 173 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_221 : block g127 7 221 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_269 : block g127 7 269 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_317 : block g127 7 317 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_365 : block g127 7 365 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_413 : block g127 7 413 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_461 : block g127 7 461 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_509 : block g127 7 509 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_557 : block g127 7 557 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_605 : block g127 7 605 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_653 : block g127 7 653 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_701 : block g127 7 701 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_749 : block g127 7 749 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_797 : block g127 7 797 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_845 : block g127 7 845 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_893 : block g127 7 893 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_941 : block g127 7 941 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_989 : block g127 7 989 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_1037 : block g127 7 1037 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_1085 : block g127 7 1085 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B7 : block g127 7 0 1133=true := (@block_merge g127 7 0 509 624 (@block_merge g127 7 0 221 288 (@block_merge g127 7 0 100 121 (@block_merge g127 7 0 4 96 g127P7_0 (@block_merge g127 7 4 48 48 g127P7_4 g127P7_52)) (@block_merge g127 7 100 25 96 g127P7_100 (@block_merge g127 7 125 48 48 g127P7_125 g127P7_173))) (@block_merge g127 7 221 144 144 (@block_merge g127 7 221 48 96 g127P7_221 (@block_merge g127 7 269 48 48 g127P7_269 g127P7_317)) (@block_merge g127 7 365 48 96 g127P7_365 (@block_merge g127 7 413 48 48 g127P7_413 g127P7_461)))) (@block_merge g127 7 509 288 336 (@block_merge g127 7 509 144 144 (@block_merge g127 7 509 48 96 g127P7_509 (@block_merge g127 7 557 48 48 g127P7_557 g127P7_605)) (@block_merge g127 7 653 48 96 g127P7_653 (@block_merge g127 7 701 48 48 g127P7_701 g127P7_749))) (@block_merge g127 7 797 144 192 (@block_merge g127 7 797 48 96 g127P7_797 (@block_merge g127 7 845 48 48 g127P7_845 g127P7_893)) (@block_merge g127 7 941 96 96 (@block_merge g127 7 941 48 48 g127P7_941 g127P7_989) (@block_merge g127 7 1037 48 48 g127P7_1037 g127P7_1085)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_0 : block g127 8 0 48=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_48 : block g127 8 48 41=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_89 : block g127 8 89 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_137 : block g127 8 137 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_185 : block g127 8 185 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_233 : block g127 8 233 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_281 : block g127 8 281 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_329 : block g127 8 329 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_377 : block g127 8 377 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_425 : block g127 8 425 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_473 : block g127 8 473 33=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_506 : block g127 8 506 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_554 : block g127 8 554 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_602 : block g127 8 602 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_650 : block g127 8 650 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_698 : block g127 8 698 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_746 : block g127 8 746 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_794 : block g127 8 794 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_842 : block g127 8 842 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_890 : block g127 8 890 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_938 : block g127 8 938 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_986 : block g127 8 986 19=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B8 : block g127 8 0 1005=true := (@block_merge g127 8 0 506 499 (@block_merge g127 8 0 233 273 (@block_merge g127 8 0 89 144 (@block_merge g127 8 0 48 41 g127P8_0 g127P8_48) (@block_merge g127 8 89 48 96 g127P8_89 (@block_merge g127 8 137 48 48 g127P8_137 g127P8_185))) (@block_merge g127 8 233 144 129 (@block_merge g127 8 233 48 96 g127P8_233 (@block_merge g127 8 281 48 48 g127P8_281 g127P8_329)) (@block_merge g127 8 377 48 81 g127P8_377 (@block_merge g127 8 425 48 33 g127P8_425 g127P8_473)))) (@block_merge g127 8 506 240 259 (@block_merge g127 8 506 96 144 (@block_merge g127 8 506 48 48 g127P8_506 g127P8_554) (@block_merge g127 8 602 48 96 g127P8_602 (@block_merge g127 8 650 48 48 g127P8_650 g127P8_698))) (@block_merge g127 8 746 144 115 (@block_merge g127 8 746 48 96 g127P8_746 (@block_merge g127 8 794 48 48 g127P8_794 g127P8_842)) (@block_merge g127 8 890 48 67 g127P8_890 (@block_merge g127 8 938 48 19 g127P8_938 g127P8_986)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P9_0 : block g127 9 0 14=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P9_14 : block g127 9 14 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P9_62 : block g127 9 62 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P9_110 : block g127 9 110 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P9_158 : block g127 9 158 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P9_206 : block g127 9 206 45=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B9 : block g127 9 0 251=true := (@block_merge g127 9 0 110 141 (@block_merge g127 9 0 14 96 g127P9_0 (@block_merge g127 9 14 48 48 g127P9_14 g127P9_62)) (@block_merge g127 9 110 48 93 g127P9_110 (@block_merge g127 9 158 48 45 g127P9_158 g127P9_206)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P10_0 : block g127 10 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P10_2 : block g127 10 2 19=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B10 : block g127 10 0 21=true := (@block_merge g127 10 0 2 19 g127P10_0 g127P10_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P11_0 : block g127 11 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B11 : block g127 11 0 1=true := g127P11_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127T : checkedTables g127 11 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g127 0 0 0 = true)
  · exact (rfl : block g127 1 0 0 = true)
  · exact (rfl : block g127 2 0 0 = true)
  · exact (rfl : block g127 3 0 0 = true)
  · exact (rfl : block g127 4 0 0 = true)
  · exact g127B5
  · exact g127B6
  · exact g127B7
  · exact g127B8
  · exact g127B9
  · exact g127B10
  · exact g127B11
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127G : graphValid g127 (boundsBefore K126) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127R : Impossible true graph 11 nineInputs.toFinset := by
  rw [show graph = targetOf g127 by decide +kernel]
  exact root_index (g:=g127) (top:=11) (i:=0) (before_sound K126 V126) g127G g127T (by decide) (by decide +kernel)

def flatValue (x : Fin 7 → Bool) : Bool := decide (∃ i < ([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem flat_correct : ∀ x : Fin 7 → Bool, nineEdge x = flatValue x := by decide +kernel

def monoWitness : List Gate := [⟨.or, [0, 1]⟩, ⟨.or, [7, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [0, 2]⟩, ⟨.or, [10, 3]⟩, ⟨.or, [11, 4]⟩, ⟨.and, [0, 3]⟩, ⟨.and, [8, 4]⟩, ⟨.and, [9, 5]⟩, ⟨.and, [12, 6]⟩, ⟨.or, [13, 14]⟩, ⟨.or, [15, 16]⟩, ⟨.or, [17, 18]⟩]

theorem monoWitnessBasis : ∀ g ∈ monoWitness,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [monoWitness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem monoWitnessCorrect : ∀ x : Fin 7 → Bool,
    Circuit.eval ⟨monoWitness, 19⟩ (List.ofFn x) = flatValue x := by
  decide +kernel

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

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def graph (x : Fin 8 → Bool) : Bool := (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 0 && x 7) || (x 1 && x 5) || (x 1 && x 6) || (x 2 && x 5) || (x 2 && x 7) || (x 3 && x 6) || (x 4 && x 6) || (x 4 && x 7) || (x 5 && x 7)
def projection : Fin 8 → Fin 8 := ![0, 1, 2, 7, 3, 4, 5, 6]
def mon : List Gate := [⟨.or, [0, 1]⟩, ⟨.or, [8, 3]⟩, ⟨.and, [9, 6]⟩, ⟨.or, [1, 7]⟩, ⟨.and, [5, 11]⟩, ⟨.or, [0, 2]⟩, ⟨.or, [5, 7]⟩, ⟨.and, [13, 14]⟩, ⟨.or, [0, 6]⟩, ⟨.or, [16, 7]⟩, ⟨.and, [4, 17]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [19, 15]⟩, ⟨.or, [20, 18]⟩]

theorem baseBound (D : Circuit) (fit : FanInTwo D)
    (ev : ∀ x, D.eval (List.ofFn x) = Base.flatValue x) : 12 ≤ Transfer.binaryCount D.gates := by
  have low := Base.binaryLower D fit (funext fun x => (ev x).trans (Base.flat_correct x).symm) Base.g127R
  change 12 ≤ D.gates.countP (fun g => !Base.isNot g) at low
  have eq : (fun g => !Base.isNot g) = Transfer.isBinaryGate := by
    funext g;cases g with | mk op l => cases op <;> rfl
  rw [eq] at low;exact low

theorem bound (C : Circuit) (fit : FanInTwo C)
    (unique : ∀ i j : Fin C.gates.length, (C.gates.get i).op = .not → (C.gates.get j).op = .not → i = j)
    (has : ∃ g ∈ C.gates, g.op = .not) (ev : ∀ x, C.eval (List.ofFn x) = graph x) :
    14 ≤ C.gates.length := by
  apply Transfer.liftBinaryLower projection graph Base.flatValue 12 _ _ _ baseBound C fit unique has ev
  · exact ⟨![false,false,false,false,false,true,false],by decide +kernel⟩
  · exact ⟨![false,false,false,false,false,false,false],![true,false,false,false,false,false,true],by decide +kernel⟩
  · decide +kernel

set_option maxRecDepth 8192 in
theorem spec : ∀ x : Fin 8 → Bool, graph x = decide (∃ i < ([0, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by decide +kernel
set_option maxRecDepth 8192 in
theorem witness : ∀ x : Fin 8 → Bool, (⟨mon,21⟩ : Circuit).eval (List.ofFn x) = graph x := by decide +kernel
theorem basis : ∀ g ∈ mon, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mon,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
end PEqualNP.Outside.L_meta_29706

open PEqualNP.Outside.L_meta_29706 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_29706 : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) := by
  intro gates o fit uniq computes
  by_cases has : ∃ g ∈ gates, g.op = GateOp.not
  · have low := bound ⟨gates,o⟩ fit uniq has (fun x => (computes x).trans (spec x).symm)
    exact ⟨mon,21,basis,(show mon.length ≤ 14 by decide).trans low,fun x => (witness x).trans (spec x)⟩
  · refine ⟨gates,o,?_,le_rfl,computes⟩
    intro g hg
    obtain ⟨op,l⟩ := fit g hg
    exact ⟨op.imp_right (fun p => p.resolve_right (fun h => has ⟨g,hg,h⟩)),l⟩

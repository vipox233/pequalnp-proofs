import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_31673

-- Signed-circuit checker adapted from L_meta_10698. The projected graph and its certificates are specific to this instance.
-- The circuit semantics and the live wire restriction lemmas are adapted from
-- L_meta_10802 and its predecessors L_meta_1674, L_meta_670 and L_meta_1667.
-- Signals are truth tables on the 256 assignments to the eight inputs.

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
lemma get_rep {u} (w : List Sig) (i : Nat) : Repr u (w.map (nrm u)) (w.getD i zero) := by
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

-- Remove a last computed signal from a backward derivation. A gate whose value
-- is already available, or is unused by the suffix, needs no entry in the plan.
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

lemma extract {u target} (gs : List Gate) (w : List Sig)
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

lemma b_read (i) (w : List Sig) (j : Nat) :
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

lemma execute_bits (gs : List Gate) (i) (w : List Sig)
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
  if h : r.val < 256-d.val then ⟨d.val+r.val,by omega⟩ else ⟨r.val-(256-d.val),by omega⟩
def backwards (d : Row) : Row := Fin.ofNat 256 (256-d.val)
def rowMove (m : Move) (r : Row) : Row :=
  if bit r m.1 then shifted m.2.2 r else if bit r m.2.1 then shifted (backwards m.2.2) r else r
def mux (m a b : Sig) := (m &&& a) ||| (~~~m &&& b)
def wordMove (m : Move) (a : Sig) :=
  mux m.1 (a.rotateRight m.2.2.val) (mux m.2.1 (a.rotateRight (backwards m.2.2).val) a)

theorem bit_shift (d r : Row) (a : Sig) : bit r (a.rotateRight d.val) = bit (shifted d r) a := by
  unfold bit
  rw [BitVec.getLsbD_rotateRight_of_lt d.isLt]
  by_cases h : r.val < 256-d.val <;> simp [shifted,h,r.isLt]

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

-- A restriction is stored with its lower bound and the restricted signals
-- available at the stated cost. Constants among the live wires save gates.
abbrev Cut := Sig × Nat × List Sig

def cutTest (c : Cut) (k : Nat) (ws : List Sig) : Bool :=
  decide (k < c.2.1 + ws.countP (isMaskedConstant c.1)) &&
    ws.all fun w => masked c.1 w == zero || c.2.2.contains (masked c.1 w)

def CutGood (T : Sig) (c : Cut) : Prop :=
  ∀ k ws, ws.Nodup → cutTest c k ws = true → Impossible true T k ws.toFinset

theorem cut_good {T d raw L} (s : Slice true raw T d L) (cs : List Choice)
    {pool} (hp : makePool true d raw cs = some pool) (afford : cs.length ≤ L) :
    CutGood T (d,L-cs.length,pool.map (masked d)) := by
  intro k ws nd checked
  simp only [cutTest,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at checked
  apply poolCut_sound s cs hp nd
  apply Bool.and_eq_true_iff.mpr
  refine ⟨decide_eq_true (by omega),List.all_eq_true.mpr ?_⟩
  intro w hw
  rcases Bool.or_eq_true_iff.mp (checked.2 w hw) with hz | hm
  · simp [availableB,hz]
  · have mem := List.contains_iff_mem.mp hm
    obtain ⟨v,hv,eq⟩ := List.mem_map.mp mem
    have yes : ((pool.map (masked d)).any fun z => z == masked d w) = true :=
      List.any_eq_true.mpr ⟨masked d v,List.mem_map_of_mem hv,beq_iff_eq.mpr eq⟩
    simp [availableB,yes]

def properB (w : Sig) := w != zero && w != one
theorem proper_of (w : Sig) (h : properB w = true) : proper w := by
  simpa only [properB,proper,Bool.and_eq_true,bne_iff_ne] using h

def bothFlags : List Bool := [false,true]
theorem has_flag (b : Bool) : b ∈ bothFlags := by cases b <;> decide

def moves (ws : List Sig) (k : Nat) (a b : Sig) : List (List Sig) :=
  ([0,1,2,3] : List Nat).flatMap fun d =>
    let z := bin d a b
    if properB z && !ws.contains z then
      bothFlags.flatMap fun ka =>
        (bothFlags.map fun kb => childTwo ws a b d ka kb).filter fun v => decide (v.length ≤ k)
    else []

def children (ws : List Sig) (k : Nat) : List (List Sig) :=
  ws.flatMap fun a => ws.flatMap fun b => if a < b then moves ws k a b else []

theorem listed {ws : List Sig} {k a b d ka kb} (ha : a ∈ ws) (hb : b ∈ ws)
    (ab : a < b) (legal : allowed true d) (fresh : bin d a b ∉ ws) (pr : proper (bin d a b))
    (short : (childTwo ws a b d ka kb).length ≤ k) : childTwo ws a b d ka kb ∈ children ws k := by
  apply List.mem_flatMap.mpr
  refine ⟨a,ha,List.mem_flatMap.mpr ⟨b,hb,?_⟩⟩
  rw [if_pos ab]
  have dm : d ∈ ([0,1,2,3] : List Nat) := by
    rcases allowed_four legal with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> decide
  apply List.mem_flatMap.mpr
  refine ⟨d,dm,?_⟩
  have ready : (properB (bin d a b) && !ws.contains (bin d a b)) = true := by
    simp [properB,pr.1,pr.2,fresh]
  dsimp only
  rw [if_pos ready]
  exact List.mem_flatMap.mpr ⟨ka,has_flag ka,List.mem_filter.mpr
    ⟨List.mem_map_of_mem (f:=fun kb => childTwo ws a b d ka kb) (has_flag kb),decide_eq_true short⟩⟩

theorem swapped {ws : List Sig} {a b d} (h : allowed true d) (ka kb : Bool) :
    (childTwo ws a b d ka kb).Perm (childTwo ws b a (flipOp d) kb ka) := by
  unfold childTwo
  rw [bin_flip h a b,List.erase_comm a b]
  apply List.Perm.cons
  cases ka <;> cases kb <;> simp [kept,List.Perm.swap]

theorem by_children {T k ws} (nd : ws.Nodup) (absent : T ∉ ws)
    (h : ∀ w ∈ children ws k, Impossible true T (k-1) w.toFinset) : Impossible true T k ws.toFinset := by
  apply enum_step nd absent
  intro a ha b hb d leg ka kb ne fresh pr short
  rcases lt_or_gt_of_ne (show a.toNat ≠ b.toNat from fun e => ne (BitVec.eq_of_toNat_eq e)) with ab | ba
  · exact h _ (listed ha hb ab leg fresh pr short)
  · have p := swapped leg (ws:=ws) (a:=a) (b:=b) ka kb
    have e := bin_flip leg a b
    have other := listed hb ha ba (flip_flip leg).1 (e ▸ fresh) (e ▸ pr)
      (ka:=kb) (kb:=ka) (p.length_eq ▸ short)
    have eq : (childTwo ws a b d ka kb).toFinset = (childTwo ws b a (flipOp d) kb ka).toFinset := by
      ext w
      simpa only [List.mem_toFinset] using (p.mem_iff (a:=w))
    rw [eq]
    exact h _ other

def sameWires (ws vs : List Sig) := ws.all vs.contains && vs.all ws.contains
theorem same_wires {ws vs} (ok : sameWires ws vs = true) : ws.toFinset = vs.toFinset := by
  obtain ⟨l,r⟩ := Bool.and_eq_true_iff.mp ok
  ext a
  simp only [List.mem_toFinset]
  exact ⟨fun ha => List.contains_iff_mem.mp (List.all_eq_true.mp l _ ha),
    fun ha => List.contains_iff_mem.mp (List.all_eq_true.mp r _ ha)⟩

abbrev Cuts (T : Sig) := List {c : Cut // CutGood T c}
abbrev Links (T : Sig) (k : Nat) := List {ws : List Sig // Impossible true T k ws.toFinset}

-- Each child has one of three witnesses. Two rows can disagree on the target
-- and agree on every live wire. A restriction can exceed the remaining gate
-- budget. A previously checked state can have exactly the same live wires.
def closeCase (T : Sig) (k : Nat) (cuts : Cuts T) (links : Links T k) (ws : List Sig) (code : Nat) :=
  if code < 65536 then
    let r := Fin.ofNat 256 (code % 256)
    let s := Fin.ofNat 256 (code / 256)
    (bit r T != bit s T) && ws.all (fun w => bit r w == bit s w)
  else if code < 131072 then
    match cuts[code-65536]? with
    | none => false
    | some c => decide ws.Nodup && cutTest c.val k ws
  else
    match links[code-131072]? with
    | none => false
    | some v => sameWires ws v.val

theorem close_ok {T k cuts links ws code} (ok : closeCase T k cuts links ws code = true) :
    Impossible true T k ws.toFinset := by
  unfold closeCase at ok
  split at ok
  · simp only [Bool.and_eq_true,bne_iff_ne,List.all_eq_true,beq_iff_eq] at ok
    intro n _ run
    obtain ⟨w,hw,ne⟩ := live_row_difference run ok.1
    exact ne (ok.2 w (List.mem_toFinset.mp hw))
  · split at ok
    · split at ok
      · contradiction
      · rename_i c _
        obtain ⟨nd,good⟩ := Bool.and_eq_true_iff.mp ok
        exact c.property k ws (of_decide_eq_true nd) good
    · split at ok
      · contradiction
      · rename_i v _
        rw [same_wires ok]
        exact v.property

def checkMoves (T : Sig) (k : Nat) (cuts : Cuts T) (links : Links T k) :
    List (List Sig) → Nat → Bool
  | [],_ => true
  | ws::rest,data => closeCase T k cuts links ws (data % 262144) &&
      checkMoves T k cuts links rest (data / 262144)

theorem moves_ok {T k cuts links vs data} (ok : checkMoves T k cuts links vs data = true) :
    ∀ w ∈ vs, Impossible true T k w.toFinset := by
  induction vs generalizing data with
  | nil => simp
  | cons v vs ih =>
    obtain ⟨closed,tail⟩ := Bool.and_eq_true_iff.mp ok
    intro w hw
    rcases List.mem_cons.mp hw with rfl | hm
    · exact close_ok closed
    · exact ih tail _ hm

def checkNode (T : Sig) (k : Nat) (ws : List Sig) (cuts : Cuts T) (links : Links T (k-1)) (data : Nat) :=
  (decide ws.Nodup && !ws.contains T) && checkMoves T (k-1) cuts links (children ws k) data

theorem node_ok {T k ws} (cuts : Cuts T) (links : Links T (k-1)) (data : Nat)
    (ok : checkNode T k ws cuts links data = true) : Impossible true T k ws.toFinset := by
  obtain ⟨head,tail⟩ := Bool.and_eq_true_iff.mp ok
  obtain ⟨hn,hm⟩ := Bool.and_eq_true_iff.mp head
  exact by_children (of_decide_eq_true hn) (by simpa using hm) (moves_ok tail)

def inputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00, 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000, 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000, 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000, 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000]
def input (i : Nat) := inputs.getD i zero
def selected (m : Nat) := (List.range 8).filter (fun i => m.testBit i)
def roots (m : Nat) := (selected m).map input

-- Setting the missing vertices to zero gives the induced subgraph.
def goalAt (m : Nat) : Sig :=
  let x := fun i => if m.testBit i then input i else zero
  (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 2 &&& x 5) ||| (x 0 &&& x 6) ||| (x 1 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 0 &&& x 7) ||| (x 2 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7)

def fixes (q : Nat) : List Move :=
  ((List.range 8).filter fun i => !(q.testBit i)).map fun i =>
    (zero,input i,Fin.ofNat 256 (1 <<< i))

def domain (q : Nat) : Sig :=
  ((List.range 8).filter fun i => !(q.testBit i)).foldl (fun d i => d &&& neg (input i)) one

def tests (m hints : Nat) : List (Sig × Row × Row) :=
  (selected m).map fun i =>
    let r := 1 <<< ((hints >>> (4*i)) % 16)
    (input i,Fin.ofNat 256 r,Fin.ofNat 256 (r ||| (1 <<< i)))

def Claim (m L : Nat) : Prop := Lower true (roots m) (goalAt m) L

def essTest (m hints : Nat) :=
  (properB (goalAt m) && checkEssential (goalAt m) (roots m) (tests m hints)) &&
    ((tests m hints).map Prod.fst == roots m)

theorem fromSearch {m k} (hints : Nat) (checked : essTest m hints = true)
    (no : Impossible true (goalAt m) k (roots m).toFinset) : Claim m (k+1) := by
  simp only [essTest,Bool.and_eq_true,beq_iff_eq] at checked
  have ok := checked.1.2
  apply lower_impossible (proper_of _ checked.1.1) (essential_plain ok).1 (essential_plain ok).2 _ no
  intro w hw
  apply essential_ok ok w
  rw [checked.2]
  exact List.mem_toFinset.mpr hw

def liftTest (m q a b e hints : Nat) :=
  ((checkLift (fixes q) (goalAt m) (roots m) (roots q) (goalAt q) (tests e hints) &&
    properB (goalAt m)) && properB (goalAt q)) &&
      decide (b ≤ a+((tests e hints).map Prod.fst).toFinset.card)

theorem fromLift {m q a} (b e hints : Nat) (lower : Claim q a)
    (ok : liftTest m q a b e hints = true) : Claim m b := by
  simp only [liftTest,Bool.and_eq_true,decide_eq_true_eq] at ok
  have lb := lift_ok ok.1.1.1 (proper_of _ ok.1.1.2) (proper_of _ ok.1.2) lower
  exact fun p bank hr ha => ok.2.trans (lb p bank hr ha)

def poolFor (q : Nat) (extra : Option Choice) : List Sig :=
  match extra with
  | none => roots q
  | some c => choiceVal c :: roots q

def ruleTest (m q L : Nat) (e : Option Choice) : Bool :=
  (((checkMap (fixes q) (roots q) (goalAt m) (roots q) (goalAt q) &&
    (movedWord (fixes q) (domain q) == one)) && properB (goalAt q)) &&
    (makePool true (domain q) (roots q) e.toList == some (poolFor q e))) &&
    decide (e.toList.length ≤ L)

def ruleFor (m : Nat) {q L} (lo : Claim q L) (e : Option Choice)
    (ok : ruleTest m q L e = true) : {c : Cut // CutGood (goalAt m) c} := by
  refine ⟨(domain q,L-e.toList.length,(poolFor q e).map (masked (domain q))),?_⟩
  simp only [ruleTest,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at ok
  exact cut_good (slice_correct ok.1.1.1.1 ok.1.1.1.2 (proper_of _ ok.1.1.2) lo)
    e.toList ok.1.2 ok.2



def cuts178 : Cuts (goalAt 178) := []

def state178_0 : List Sig := roots 178
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude178_0 : Impossible true (goalAt 178) 3 state178_0.toFinset :=
  node_ok cuts178 [] 0x8808a202240c0220224000900024040120204808220224280120204840901008a801210088002200088081210048001200048082220 (by decide +kernel)

theorem lower178 : Claim 178 4 :=
  fromSearch 1074856000 (by decide +kernel) exclude178_0

def cuts150 : Cuts (goalAt 150) := []

def state150_0 : List Sig := roots 150
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude150_0 : Impossible true (goalAt 150) 3 state150_0.toFinset :=
  node_ok cuts150 [] 0x240009000240401202210008400210109010058081202048181202218108404210188404048001200048089080048401610048501210 (by decide +kernel)

theorem lower150 : Claim 150 4 :=
  fromSearch 536938304 (by decide +kernel) exclude150_0

def cuts180 : Cuts (goalAt 180) := []

def state180_0 : List Sig := roots 180
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude180_0 : Impossible true (goalAt 180) 3 state180_0.toFinset :=
  node_ok cuts180 [] 0x90108404240c024042400090002404084040d0102404090502404210008400210109010090002400090108480090803420090c02420 (by decide +kernel)

theorem lower180 : Claim 180 4 :=
  fromSearch 539428096 (by decide +kernel) exclude180_0

def cuts166 : Cuts (goalAt 166) := []

def state166_0 : List Sig := roots 166
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude166_0 : Impossible true (goalAt 166) 3 state166_0.toFinset :=
  node_ok cuts166 [] 0x8808a20208a082202210008400210102420090002400090102202218108404210188404088002200088082404088802420212082220 (by decide +kernel)

theorem lower166 : Claim 166 4 :=
  fromSearch 537920848 (by decide +kernel) exclude166_0

def cuts54 : Cuts (goalAt 54) := []

def state54_0 : List Sig := roots 54
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude54_0 : Impossible true (goalAt 54) 3 state54_0.toFinset :=
  node_ok cuts54 [] 0x48082202090501202090002400090102202058081202048181202088002200088082404048001200048082220048401610048501210 (by decide +kernel)

theorem lower54 : Claim 54 4 :=
  fromSearch 1115456 (by decide +kernel) exclude54_0

def rule182_0 : {c : Cut // CutGood (goalAt 182) c} :=
  ruleFor 182 lower178 none (by decide +kernel)

def rule182_1 : {c : Cut // CutGood (goalAt 182) c} :=
  ruleFor 182 lower150 none (by decide +kernel)

def rule182_2 : {c : Cut // CutGood (goalAt 182) c} :=
  ruleFor 182 lower180 none (by decide +kernel)

def rule182_3 : {c : Cut // CutGood (goalAt 182) c} :=
  ruleFor 182 lower166 none (by decide +kernel)

def rule182_4 : {c : Cut // CutGood (goalAt 182) c} :=
  ruleFor 182 lower54 none (by decide +kernel)

def cuts182 : Cuts (goalAt 182) := [rule182_0,rule182_1,rule182_2,rule182_3,rule182_4]

def state182_0 : List Sig := [0xfcfcfcfc00000000fcfcfcfc00000000fcfcfcfc00000000fcfcfcfc,input 1,input 2,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude182_0 : Impossible true (goalAt 182) 4 state182_0.toFinset :=
  node_ok cuts182 [] 0x24000900024040120209000a40021010240009000340004818240008800a200210182200088003200048082200088002400048502200088089010288082202048082414048082202088082400098082400090102200088082200 (by decide +kernel)

def state182_1 : List Sig := [0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc,input 1,input 2,input 4,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude182_1 : Impossible true (goalAt 182) 5 state182_1.toFinset :=
  node_ok cuts182 [⟨state182_0,exclude182_0⟩] 0x220228808903008808900024000901004808120208808241404808860221808840424040260208808240408808160204808120604808242021810840421018840408808240408808240404808160404808908021a0816140485012102101090102101090100880a0000088090001048089080048089080 (by decide +kernel)

def state182_2 : List Sig := [0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc,input 1,input 4,input 2,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude182_2 : Impossible true (goalAt 182) 5 state182_2.toFinset :=
  node_ok cuts182 [] 0x22022880890300880884002100084042404024000900024040880816020480812060480824200d0c03430090801202248089010048081202088083414048089080218188404218188404088082404088082404048401610048501210048081210088c02220218188404218188404088082404088082404 (by decide +kernel)

def state182_3 : List Sig := [0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 1,input 5,input 2,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude182_3 : Impossible true (goalAt 182) 5 state182_3.toFinset :=
  node_ok cuts182 [] 0x900024000901004808120208808b0a004808908004808120224200840021000840424040160204808120604808260208808220608808848009080242021200220228808b03008808240421818840421818840404808322004808222008880242021a082220088082220090181210218188404218188404 (by decide +kernel)

def state182_4 : List Sig := [0xffff0000ffff0000ffff0000ffff0000cccc0000cccc0000cccc0000cccc,input 1,input 7,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude182_4 : Impossible true (goalAt 182) 4 state182_4.toFinset :=
  node_ok cuts182 [] 0x2c0009000240809000090002400090102202250009000240109000048003200088081200048001600048101200048009000210181200048082404088081202048081206058081202048089000248089000088801200048081200 (by decide +kernel)

def state182_5 : List Sig := [0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 1,input 7,input 2,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude182_5 : Impossible true (goalAt 182) 5 state182_5.toFinset :=
  node_ok cuts182 [⟨state182_4,exclude182_4⟩] 0x22022880822820880824040880822020901012020880824140480812022480890800480a00000480812024000c240009000240408808160204808120604808860221808860609080242021200848009080840408808240408808240404808908004808908021a00242021208242021818a2a0210181210 (by decide +kernel)

def state182_6 : List Sig := [0xfffff0f0fffff0f0fffff0f0fffff0f0,input 2,input 4,input 1,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude182_6 : Impossible true (goalAt 182) 4 state182_6.toFinset :=
  node_ok cuts182 [] 0x8800220008808240424800900024008900021800840021008840024000b00009050900021000a400090108400210009000048188400090102202090102202210108406218108404048089000250109000240408400210108400 (by decide +kernel)

def state182_7 : List Sig := [0xfffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0,input 2,input 4,input 1,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude182_7 : Impossible true (goalAt 182) 5 state182_7.toFinset :=
  node_ok cuts182 [⟨state182_6,exclude182_6⟩] 0x2202288089030088088604210108406210102200088002202090101604058101606088801210058401214048402220048401210088809404210109010210103404088082414088081202210109010210109010090102202090102202058183430048182420210120000210110004090102202090102202 (by decide +kernel)

def state182_8 : List Sig := [0xfffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0,input 2,input 5,input 1,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude182_8 : Impossible true (goalAt 182) 5 state182_8.toFinset :=
  node_ok cuts182 [] 0x900024000901004808120209010241404808120205818160604808860421010840621010120004800120208880260409010240609010121005850161404840121005850161404840240421010b030090102202210109010210109010058181202058181202090102420088188480210109010210109010 (by decide +kernel)

def state182_9 : List Sig := [0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 2,input 7,input 1,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude182_9 : Impossible true (goalAt 182) 5 state182_9.toFinset :=
  node_ok cuts182 [] 0x220221010a282088082202090102404088081202088082414048081202210108414048081202058181606048082200088002202090101200048001202088808604210108406210101210058501614048401210058501614048409010090102202090102202058181202058181202210108480240502420 (by decide +kernel)

def state182_10 : List Sig := [0x3333333333330000333333333333000033333333333300003333333333330000,input 4,input 5,input 2,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude182_10 : Impossible true (goalAt 182) 4 state182_10.toFinset :=
  node_ok cuts182 [] 0x21000840021010901009800220008810220005800120004810120008800a200240c022000480092002404012000480022000905012000484084042404084040484012140584012100901022000c8402200088801200048401200 (by decide +kernel)

def state182_11 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,input 5,input 1,input 2,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude182_11 : Impossible true (goalAt 182) 5 state182_11.toFinset :=
  node_ok cuts182 [⟨state182_10,exclude182_10⟩] 0x84002100084042404034100d04034142120024200d08024300908084800908024202120086042101084062101012100584012140484012100c840222004840222004840121008882000004840121040008b0102101090302101022022404084042404084040d050b0a0090501202240408404240408404 (by decide +kernel)

def state182_12 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 4,input 7,input 1,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude182_12 : Impossible true (goalAt 182) 5 state182_12.toFinset :=
  node_ok cuts182 [] 0x22022404090300880822020d05034140880824000900024040880894102404090142404024200d0c034300908024200d0c0343009080220008800220209010121005840121404840121024040a2a00484022200484012100888022200484012100888084040d05022020d0502202240409080210501202 (by decide +kernel)

def state182_13 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f00000000,input 5,input 7,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude182_13 : Impossible true (goalAt 182) 4 state182_13.toFinset :=
  node_ok cuts182 [] 0x2500084002104084000d0002400090402400048001200048082220218008400210088400098002400090082400090008400240c024000908012020d0801202088801210088801210240408400290808400088082400090802400 (by decide +kernel)

def state182_14 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,input 7,input 1,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude182_14 : Impossible true (goalAt 182) 5 state182_14.toFinset :=
  node_ok cuts182 [⟨state182_13,exclude182_13⟩] 0x12022c080b0300480812022c20090a00480812022420090800480816020480812060480824202908084800908084800908024202120200000908024204000012000480012020888012100584012140484012102888022a00484012100888022200484012100888022200484084042c0c0a282240c02202 (by decide +kernel)

def state182_15 : List Sig := roots 182
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude182_15 : Impossible true (goalAt 182) 6 state182_15.toFinset :=
  node_ok cuts182 [⟨state182_1,exclude182_1⟩,⟨state182_2,exclude182_2⟩,⟨state182_3,exclude182_3⟩,⟨state182_5,exclude182_5⟩,⟨state182_7,exclude182_7⟩,⟨state182_8,exclude182_8⟩,⟨state182_9,exclude182_9⟩,⟨state182_11,exclude182_11⟩,⟨state182_12,exclude182_12⟩,⟨state182_14,exclude182_14⟩] 0x40010b03008808220240004840428a08a20280024b03028a0890304001084040880822024001090100480890004000c84042420090008002090102420090104001084040480812024000434140480812024000c22022c28022028001c34142c28024144000422020480812024001084040908084004000090102120084008001884042120084044001090100908090104000424042120024004000022020908024008001424040908024044000422022120022024000c16060908016024000012020d0c012028001016060d0c012064000c120209080120240010860604840860440008840428a8084048000c860628a8084064001084040484084044000422020484022004000824040888022008000822020888022024000424040484024044000c12020888012004000890800484012008000412020484012024000c9080088802220400008682048401210400082420058501610800008682058501214400002420048401210 (by decide +kernel)

theorem lower182 : Claim 182 7 :=
  fromSearch 537986368 (by decide +kernel) exclude182_15

def cuts145 : Cuts (goalAt 145) := []

def state145_0 : List Sig := roots 145
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude145_0 : Impossible true (goalAt 145) 3 state145_0.toFinset :=
  node_ok cuts145 [] 0x240401101240008101242009000240409080240408101044041101204041110204009010206008100204048180204049010044401110044048180044009080044401100044041110044049080206008180 (by decide +kernel)

theorem lower145 : Claim 145 4 :=
  fromSearch 4 (by decide +kernel) exclude145_0

theorem lower177 : Claim 177 5 :=
  fromLift 5 32 4 lower145 (by decide +kernel)


theorem lower179 : Claim 179 6 :=
  fromLift 6 2 68 lower177 (by decide +kernel)


theorem lower181 : Claim 181 6 :=
  fromLift 6 4 1284 lower177 (by decide +kernel)


theorem lower149 : Claim 149 5 :=
  fromLift 5 4 1796 lower145 (by decide +kernel)


theorem lower151 : Claim 151 6 :=
  fromLift 6 2 1860 lower149 (by decide +kernel)


theorem lower55 : Claim 55 5 :=
  fromLift 5 1 1348 lower54 (by decide +kernel)


theorem lower167 : Claim 167 5 :=
  fromLift 5 1 1365 lower166 (by decide +kernel)


def cuts53 : Cuts (goalAt 53) := []

def state53_0 : List Sig := roots 53
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude53_0 : Impossible true (goalAt 53) 3 state53_0.toFinset :=
  node_ok cuts53 [] 0x44042101090501101090002400090102101054041101044141101084002100084042404044001100044042120044401510044501110 (by decide +kernel)

theorem lower53 : Claim 53 4 :=
  fromSearch 1284 (by decide +kernel) exclude53_0

theorem lower147 : Claim 147 5 :=
  fromLift 5 2 68 lower145 (by decide +kernel)


def cuts163 : Cuts (goalAt 163) := []

def state163_0 : List Sig := roots 163
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude163_0 : Impossible true (goalAt 163) 3 state163_0.toFinset :=
  node_ok cuts163 [] 0x8404810108a08210120c0481012040c8101088002200088082101204008100204042120084002100084042202084802220206082120 (by decide +kernel)

theorem lower163 : Claim 163 4 :=
  fromSearch 85 (by decide +kernel) exclude163_0

def rule183_0 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower182 none (by decide +kernel)

def rule183_1 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower179 none (by decide +kernel)

def rule183_2 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower177 none (by decide +kernel)

def rule183_3 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower181 none (by decide +kernel)

def rule183_4 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower151 none (by decide +kernel)

def rule183_5 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower149 none (by decide +kernel)

def rule183_6 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower55 none (by decide +kernel)

def rule183_7 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower167 none (by decide +kernel)

def rule183_8 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower182 (some (3,input 1,input 4)) (by decide +kernel)

def rule183_9 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower182 (some (2,input 1,input 4)) (by decide +kernel)

def rule183_10 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower182 (some (1,input 1,input 4)) (by decide +kernel)

def rule183_11 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower182 (some (0,input 1,input 4)) (by decide +kernel)

def rule183_12 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower151 (some (3,input 1,input 4)) (by decide +kernel)

def rule183_13 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower182 (some (3,input 1,input 7)) (by decide +kernel)

def rule183_14 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower151 (some (1,input 1,input 7)) (by decide +kernel)

def rule183_15 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower182 (some (2,input 1,input 7)) (by decide +kernel)

def rule183_16 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower182 (some (1,input 1,input 7)) (by decide +kernel)

def rule183_17 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower53 none (by decide +kernel)

def rule183_18 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower182 (some (0,input 1,input 7)) (by decide +kernel)

def rule183_19 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower54 none (by decide +kernel)

def rule183_20 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower181 (some (1,input 5,input 7)) (by decide +kernel)

def rule183_21 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower177 (some (1,input 5,input 7)) (by decide +kernel)

def rule183_22 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower147 none (by decide +kernel)

def rule183_23 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower163 none (by decide +kernel)

def rule183_24 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower182 (some (3,input 2,input 4)) (by decide +kernel)

def rule183_25 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower151 (some (1,input 2,input 4)) (by decide +kernel)

def rule183_26 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower182 (some (2,input 2,input 4)) (by decide +kernel)

def rule183_27 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower182 (some (1,input 2,input 4)) (by decide +kernel)

def rule183_28 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower182 (some (0,input 2,input 4)) (by decide +kernel)

def rule183_29 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower166 none (by decide +kernel)

def rule183_30 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower179 (some (1,input 4,input 5)) (by decide +kernel)

def rule183_31 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower177 (some (1,input 4,input 5)) (by decide +kernel)

def rule183_32 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower182 (some (3,input 2,input 7)) (by decide +kernel)

def rule183_33 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower182 (some (2,input 2,input 7)) (by decide +kernel)

def rule183_34 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower182 (some (1,input 2,input 7)) (by decide +kernel)

def rule183_35 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower182 (some (0,input 2,input 7)) (by decide +kernel)

def rule183_36 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower151 (some (3,input 2,input 7)) (by decide +kernel)

def rule183_37 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower182 (some (3,input 4,input 5)) (by decide +kernel)

def rule183_38 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower182 (some (2,input 4,input 5)) (by decide +kernel)

def rule183_39 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower182 (some (1,input 4,input 5)) (by decide +kernel)

def rule183_40 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower147 (some (3,input 1,input 4)) (by decide +kernel)

def rule183_41 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower151 (some (0,input 1,input 4)) (by decide +kernel)

def rule183_42 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower182 (some (0,input 4,input 5)) (by decide +kernel)

def rule183_43 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower149 (some (1,input 2,input 4)) (by decide +kernel)

def rule183_44 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower182 (some (2,input 4,input 7)) (by decide +kernel)

def rule183_45 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower182 (some (3,input 4,input 7)) (by decide +kernel)

def rule183_46 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower182 (some (0,input 4,input 7)) (by decide +kernel)

def rule183_47 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower182 (some (1,input 4,input 7)) (by decide +kernel)

def rule183_48 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower182 (some (3,input 5,input 7)) (by decide +kernel)

def rule183_49 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower182 (some (2,input 5,input 7)) (by decide +kernel)

def rule183_50 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower182 (some (1,input 5,input 7)) (by decide +kernel)

def rule183_51 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower149 (some (3,input 2,input 7)) (by decide +kernel)

def rule183_52 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower151 (some (0,input 2,input 7)) (by decide +kernel)

def rule183_53 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower182 (some (0,input 5,input 7)) (by decide +kernel)

def rule183_54 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower147 (some (1,input 1,input 7)) (by decide +kernel)

def cuts183 : Cuts (goalAt 183) := [rule183_0,rule183_1,rule183_2,rule183_3,rule183_4,rule183_5,rule183_6,rule183_7,rule183_8,rule183_9,rule183_10,rule183_11,rule183_12,rule183_13,rule183_14,rule183_15,rule183_16,rule183_17,rule183_18,rule183_19,rule183_20,rule183_21,rule183_22,rule183_23,rule183_24,rule183_25,rule183_26,rule183_27,rule183_28,rule183_29,rule183_30,rule183_31,rule183_32,rule183_33,rule183_34,rule183_35,rule183_36,rule183_37,rule183_38,rule183_39,rule183_40,rule183_41,rule183_42,rule183_43,rule183_44,rule183_45,rule183_46,rule183_47,rule183_48,rule183_49,rule183_50,rule183_51,rule183_52,rule183_53,rule183_54]

def state183_0 : List Sig := [0xffffffffffffffffffffffffffffffffffffccccffffccccffffccccffffcccc,input 7,input 1,input 4,input 0,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_0 : Impossible true (goalAt 183) 6 state183_0.toFinset :=
  node_ok cuts183 [] 0x210128808903008404210108808220208404240009000240408404160204808120604808860221808860620c0c24200d0c0343009080210008400210108808111005440111404440130204808120304808111004840818204440830220c08830321818212004440111008480120208404341408404120224808901004808110108808210108808210104840161004850121004808121004808110320c0c90102040c8103088808101 (by decide +kernel)

def state183_1 : List Sig := [0xffffccccffffccccffffccccffffcccc,input 7,input 1,input 4,input 0,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_1 : Impossible true (goalAt 183) 6 state183_1.toFinset :=
  node_ok cuts183 [] 0x210120404a2820840424000900024040840416020480812060480884002100084042040421000840021010880811100544011140444013020480812030480811100484081820444081002040081012101012020840434140840490002400090802040422020840422020840412100584012140484012020484012020440c830120404a2a020404220208404220208404343009080343009080111008480111008480110104404120224200121008880121028a808303 (by decide +kernel)

def state183_2 : List Sig := [0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 7,0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc,input 4,input 0,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_2 : Impossible true (goalAt 183) 6 state183_2.toFinset :=
  node_ok cuts183 [] 0x8404a20208a0821010840422020880821010900024000901021010580812020481812020908034300d0c0242021808860221818830305840121004850121008400210008404220204440151004450111004c0812020480c120208480111004440212020c08830220c0c86060444012102060011100480821010d05021010440412022400812820480812100480812020440c220208404220208404830328a8081032040c1210088801210400188101 (by decide +kernel)

def state183_3 : List Sig := [0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc,input 1,input 4,input 0,input 2,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_3 : Impossible true (goalAt 183) 7 state183_3.toFinset :=
  node_ok cuts183 [⟨state183_0,exclude183_0⟩,⟨state183_1,exclude183_1⟩,⟨state183_2,exclude183_2⟩] 0xb03008404210120404a28220404b03028a0890302040421010840484040908084002040484802100084042120084042040424202040424042120024000840424200900024040908024040840484800840416060908016020480834300480816060d0c012060480824200480900020908024204000434300d0c100020d0c0343040004242009080810104440810021010818020400810120600810121010111021010210104440210008808212008400210108480210108808111008809000a04440111009080151405441000a05450111409080111004440130308480130204808111004808130304440120304808212004809000a04440111004840838204841000a20e08838204840111004441000a08480212040000111004441000a04440111040000212008480901004808120220404928220404901024a0890102040412022040434140480812020840500050840434144001434140840412020840500094000c110120c0c121020c0c81014000c810120c0e000220c0c81010484081010880812100880821010c8c0210108808323008808210104840210121a08121004840242005850161021a0816140485024200484012100480900070480900030484012104000d00030440d00084001c222020c0d000620c0c810180004810120c0e000020c0c8101400188101088090004088082101400142101088090005088082101400102101 (by decide +kernel)

def state183_4 : List Sig := [0xffffffffffffffffffffffffffffffff33330000333300003333000033330000,input 7,input 1,input 4,input 0,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_4 : Impossible true (goalAt 183) 6 state183_4.toFinset :=
  node_ok cuts183 [] 0x21012404090300840421010d05034140840424000900024040840416020480812060480894102404090142404024200d0c0343009080210008400210108808111005440111404440130204808120304808111008880818204440111024040818004440212004440111008480120208404341408404120224200901004808110104404908004808220008800220208404222009080848208880120004800120208880921024040a2a024040222028a801210048408101 (by decide +kernel)

def state183_5 : List Sig := [0x3333000033330000333300003333000033330000333300003333000033330000,input 1,input 4,input 0,input 2,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_5 : Impossible true (goalAt 183) 7 state183_5.toFinset :=
  node_ok cuts183 [⟨state183_4,exclude183_4⟩] 0xb03008404210120404a28220404b03028a0890302040421010840484040908084002040484802100084042120084042040424202040424042120024000840424200900024040908024040840484800840416060908016020480834300480816060d0c0120604808242004808810104440810021010818020400810120600810121010111021010210104440210008808212008400210108480210108808111008809000804440111009080151405441000805450111409080111004440130308480130204808111004808130304440120304808212004809000804440111008880838208881000820e08818208880111004440901004808120220404928220404901024a08901020404120220404341404808120208405000508404341440014341408404120208404830308880830120404a2a020404830328a80810320404222020404220240030220008404222008800220208880220208405000c0840486820888022200908100030908086824000884820908022200888100034000c12000480900070480900030888022202404100062404081014001c81012404200002404081014001881010d05100040d05021014001421010d05100050d05021014001021010d0c100010d0c024204000824200d0c100020d0c024204000424200444100000444021204002021200444100080444021204000021204000d000b044050007400281210 (by decide +kernel)

def state183_6 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 4,0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 1,input 0,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_6 : Impossible true (goalAt 183) 6 state183_6.toFinset :=
  node_ok cuts183 [] 0x8404220208808210108404a2020d05021010900024000901021012504090102405090100908034300d0c0242021808860221818830308400210008404220204440151004450111004440838020608111004440901020600111008480111004440212020c08830220c0c860608808210108808210121a00242021208242004840128004a00128224200830328a8081032040c81012040483034000c3414084043414084049010242009010210501101 (by decide +kernel)

def state183_7 : List Sig := [0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 1,input 7,input 0,input 2,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_7 : Impossible true (goalAt 183) 7 state183_7.toFinset :=
  node_ok cuts183 [⟨state183_2,exclude183_2⟩,⟨state183_0,exclude183_0⟩,⟨state183_6,exclude183_6⟩] 0x1000508404210120c0ca28228809000528a08228220c0c210108405000508404210140010220208809000508808220240010210108404341404404110108404b0a00840434142c280241408404110104405001104404110120c0c90802480a000224200908020c0c11010440500110440411014001c12020480a00010480812024001c11010440424042120024000840424200900024040908024040840484800840415050908015010440434300440415050d0c0110504404242004404860609080860220c0c848021808860621200860620c0c242020c0d000209080242040004848021201000221200848040004242009080210104440210008808212008400210108480210108808111008808110108480110004808111004400110104440110104808212004809001004440111009080151405441001005450111409080111004440830304440830221818818020c08830320600830321818111021819001004440111028a80838220e01001020e08818228a80111004441001004440111040000818020601001020600818040000111004441000f4000c810108809000e08808210128a80210108808a2a008808210140038210104808a2a00480811014000c11010480a000004808110128a80110121a08a2a021a0024204000c242021a09000221208242028a80242020c0d000620c0d000328a80a2a04000d00032040d000d400181210 (by decide +kernel)

def state183_8 : List Sig := [0xffff3333ffff3333ffff3333ffff3333ffff0000ffff0000ffff0000ffff0000,input 4,input 1,input 7,input 0,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_8 : Impossible true (goalAt 183) 6 state183_8.toFinset :=
  node_ok cuts183 [] 0x210128808903008404240009000240408404860221808860620c0c24200d0c034300908024200d0c0343009080210008400210108808111005440111404440830220c08830321818111004840838204440212004440111008480212004440111008480220008800220208404121005840121404840830120c04830304840222004840121008880222004840121008880341408404341408404901020c0c901020c0c11010d05021010d0502101204048101240408303 (by decide +kernel)

def state183_9 : List Sig := [0xffffffff33333333ffffffff33333333ffffffff00000000ffffffff00000000,input 1,input 7,input 0,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_9 : Impossible true (goalAt 183) 6 state183_9.toFinset :=
  node_ok cuts183 [] 0x240c01101044048303242009202240c09080240c083030440411010d05011010440421012420021010d05090800905021010440411010541424200540411010d0c0110105414343004414110109080110121818242021808830321200860221818848021818830309080830309010868209000210109080240009010242009010210121a0821010440421200440012020444011000440411100440412020848012024005411100444024200545015104004c151404450242004440111020c0c111020c08860620600830220c0c818020c0c860604440860640050111004440121020e0812104004c838220e08121004440111008404111008400220208480210008404212008404220204440220204808222004800110104840120004808121004808110108880110121a08121004840242005850161021a08161404850242004840121020c0c121020c04903028a00830120c0ca28020c0c9030048401210088081210088002101088802200088082220088082101048402101240c0210108404830328a088101240c0a282240c08303084042101 (by decide +kernel)

def state183_10 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 4,0x3333333333333333333333333333333300000000000000000000000000000000,input 1,input 0,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_10 : Impossible true (goalAt 183) 6 state183_10.toFinset :=
  node_ok cuts183 [] 0x21012880834140840424000900024040840424200d0c0343009080860221808860620c0c210008400210108808111005440111404440111004840838204440212004440111008480830220c08830321818220008800220208404121005840121404840222004840121021850830120c04830308880901008404903008404901025040901424040901004440818004440a2a0242009010240408414204043414084043414084041101 (by decide +kernel)

def state183_11 : List Sig := [0x3333333333333333333333333333333300000000000000000000000000000000,input 1,input 7,input 0,input 2,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_11 : Impossible true (goalAt 183) 7 state183_11.toFinset :=
  node_ok cuts183 [⟨state183_8,exclude183_8⟩,⟨state183_9,exclude183_9⟩,⟨state183_10,exclude183_10⟩] 0x1000508404210120c0ca28228809000528a08228220c0c210108404341404404110108404b0a00840434142c280241408404110104405000604404110120c0c90802480a000224200908020c0c11010440424042120024000840424200900024040908024040840484800840415050908015010440434300440415050d0c0110504404242004404860609080860220c0c848021808860621200860620c0c242020c0c210104440210008808212008400210108480210108808111008808110108480110004808111004400110104440110104808212004809000d04440111009080151405441000d05450111409080111004440830304440830221818818020c08830320600830321818111021819000d04440111004840838204841000d20e0883820484011100444022020484022000840422200880022020888022020840412100840412020888012000440412100480012020484012020440422200440486820484012100908016140584086820585012140908012100484100034000c830120c0d000620c0d000304840121040015000440010210140014210140019000580004210140010210124201000724200110140018110124202000024200110140018110121201000121200242040008242021201000221200242040004242020601000020600111040034111020601000d2060011104000011104000d001220405000640040a2a0 (by decide +kernel)

def state183_12 : List Sig := [0xfffffffffffffffffffffffffffffffffffff0f0fffff0f0fffff0f0fffff0f0,input 7,input 2,input 4,input 0,input 1,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_12 : Impossible true (goalAt 183) 6 state183_12.toFinset :=
  node_ok cuts183 [] 0x2101210109030084042101090102404084042200088002202084041604058101606054141210058401214048408604210108406210102220048401210088802100084002101088081110048408182044401504054101505058181110054401114044408504210108405210102120044401110084803404084042414084049404210109010210101101090102101090102101054143430044141105210109010210108105090808101 (by decide +kernel)

def state183_13 : List Sig := [0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 7,0xfffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0,input 4,input 0,input 1,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_13 : Impossible true (goalAt 183) 6 state183_13.toFinset :=
  node_ok cuts183 [] 0x8404840428a0821010840424040901021010880022000880821010581016040581815050888012100484022202181084042101884040484016100485012100840021000840422020444012102060811100541015040541416060848011100444021202141084042101484040444015100445011100d0102101090502101044049004210108414210103430054141105044142404084042404084048404212008404204142420090803430400188101 (by decide +kernel)

def state183_14 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 7,0xfffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0,input 2,input 0,input 1,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_14 : Impossible true (goalAt 183) 6 state183_14.toFinset :=
  node_ok cuts183 [] 0x84049010240c0210108404340409050210108800220008808210104840161004850121008880121004840222004840901028a8012100581016040581815050840021000840422020444012102060811100444015100445011100848011100444021200444090102060011100541015040541416060901021010901021010908084102104084142404015050d0c0110504414240408404240408404901024200901004a081101044041505400048101 (by decide +kernel)

def state183_15 : List Sig := [0xfffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0,input 2,input 4,input 0,input 1,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_15 : Impossible true (goalAt 183) 7 state183_15.toFinset :=
  node_ok cuts183 [⟨state183_12,exclude183_12⟩,⟨state183_13,exclude183_13⟩,⟨state183_14,exclude183_14⟩] 0xb03008404210120404a28220404b03028a08903020404210108404830304840830120404a2a020404830328a8081032040412102040422020484022000840422200880022020888022020840412100840416060888016040541412100581016060484016060541422200541500010484012100d0c016140584100020585012140d0c012100484100020888022204000c12100484100020484012104000c222008880810104440810021010818020400810120600810121010111021010210104440210008808212008400210108480210108808111008809001b04440111004840838204841001b20e08818204840111004440150508480150405818111005410150504440150505818212005819001b0444011100d0c0151405441001b0545011140d0c0111004441001b08480212040000111004441001b04440111040000212008480901005414940420405001720404901080008901020404150520404341405414340408405001608404341440058241408404150508405001a4000411012101034302101081014000481012101200012101081010d0c081010901100190901021010d0c021010901034300901021014006421010541500070541500010d0c034304000500010441500184001c24202101100062101081014005c8101210120000210108101400188101090110004090102101400582101090110016090102101400102101 (by decide +kernel)

def state183_16 : List Sig := [0xffffffff0f0f0000ffffffff0f0f0000ffffffff0f0f0000ffffffff0f0f0000,input 2,input 4,input 0,input 1,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_16 : Impossible true (goalAt 183) 6 state183_16.toFinset :=
  node_ok cuts183 [] 0x20c0c121020c04810128a80810120c0ca2a02040c810104840810105818222005810150504840160405818121005818150508880150521a08121004840341005850341021a0816140585034100484012100880816140880021010484022000880812100880821010585021012040411102040084042060081002040481802040484040444084044007c111004440121020e0812104007483822060812100444011100541421200541016060444015040541411100541416060848016064007811100444034100545034104007415140545034100444011100840415140840022020444021000840411100840422020545022022404015052501081012428081012404090a02404081010541481010d05015050440421012428011010d05090a00905021010541421012101034102100081012120084002101084802101081010d04081010541424200540490a00d04015010541434100541490a00908024100901084800900021010d040240009010341009010210121200210124040210108404810128a08810124040a282240408101084042101 (by decide +kernel)

def state183_17 : List Sig := [0xffffffffffffffffffffffffffffffff0f0f00000f0f00000f0f00000f0f0000,input 7,input 2,input 4,input 0,input 1,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_17 : Impossible true (goalAt 183) 6 state183_17.toFinset :=
  node_ok cuts183 [] 0x210124040903008404210128a08a28208404220008800220208404160405810160605414121005850161404840121024040a2a0048401614048401210058502100084002101088081110048408182044401504054101505058181110054501514044401110240408180044401514044401110054503404084042414084041505242009010054141101044049080054142400090002404084041501054041505090809410240408480240402420212003430090808101 (by decide +kernel)

def state183_18 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 7,0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000,input 2,input 0,input 1,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_18 : Impossible true (goalAt 183) 6 state183_18.toFinset :=
  node_ok cuts183 [] 0x21012404090300840421010d010241408404220008800220208404121005850161404840121024040a2a00484016040581016060541421000840021010880811100484081820444011100545015140444011102404081800444015040541015050581824000900024040840484142404084142404015010540415050908090800840490a0084041210058501210058501110054501110054503430240408414240408414044048101 (by decide +kernel)

def state183_19 : List Sig := [0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000,input 2,input 4,input 0,input 1,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_19 : Impossible true (goalAt 183) 7 state183_19.toFinset :=
  node_ok cuts183 [⟨state183_16,exclude183_16⟩,⟨state183_17,exclude183_17⟩,⟨state183_18,exclude183_18⟩] 0xb03008404210120404a28220404b03028a08903020404210108404830304840830120404a2a020404830328a80810320404121020404220204840220008404222008800220208880220208404121008404160608880160405414121005810160604840160605414222005414868204840121009080161405850868205850161409080121004840810104440810021010818020400810120600810121010111021010210104440210008808212008400210108480210108808111008809001804440111004840838204841001820e0881820484011100444015050848015040581811100541015050444015050581821200581900180444011100908015140545100180545015140908011100444090100541494042040500072040490108000890102040415052040434140541434040840500160840434144005824140840415050840484040908084002040484802100084042120084042040424202040424042120024000840424200900024040908024040840484800840500014000415010541500070541500010908024202404100062404081014001c81012404200012404081014001881014005900044001021014005821014001d00168000021014001021010484100030484016144000816140484100020484016144000c161404441000004440151440060151404441001804440151440000151440005001c0440500074006c3430 (by decide +kernel)

def state183_20 : List Sig := [0xffff0000ffff0000ffff0000ffff0000f0f00000f0f00000f0f00000f0f0,input 4,input 2,input 7,input 0,input 1,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_20 : Impossible true (goalAt 183) 6 state183_20.toFinset :=
  node_ok cuts183 [] 0x210121010903008404220008800220208404860421010840621010121005840121404840120004800120204404210008400210108808111004840818204440850421010840521010111005440111404440110004400110104808240408404240408404840424040840420414150104404343004404110108404341404404900024000901004404240408404240408404a2a004840a2a00484081800444081800444081012040484042404024200908084800d0c01505 (by decide +kernel)

def state183_21 : List Sig := [0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 2,input 7,input 0,input 1,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_21 : Impossible true (goalAt 183) 7 state183_21.toFinset :=
  node_ok cuts183 [⟨state183_13,exclude183_13⟩,⟨state183_12,exclude183_12⟩,⟨state183_20,exclude183_20⟩] 0x1001608404210121010a28221011001628a08a28221010210108405001608404210140010240409011001609010240440010210108404341404404110108404b0a00840434142c28024140840411010440494140440411012101090802101094142420084142101011010440600020440411014001c15050541600010541415054001c110104404220204840220008404222008800220208880220208404121008404120208880120004404121004800120204840120204404222004404860604840860421010a2a021010860628a8084062101012102101086820484012102120016140585086820585016142120012100484100020484012104000c16140585100020585016144000c121004840210104440210008808212008400210108480210108808111008808110108480110004808111004400110104440110104808212004809002204440111004840838204841002220e08818204840111004440850504440850421010818021010850520600840521010111021011002204440111021200151405451002205450151421200111004441002204440111040000151405451002205450151440000111004441002140004810109010848009010210129280210109010a4a0090102101212002101054148480054141101400041101054160000054141101212001101210110006210110001212008480400050001204150020400182420 (by decide +kernel)

def state183_22 : List Sig := [0xffff0f0fffff0f0fffff0f0fffff0f0fffff0000ffff0000ffff0000ffff0000,input 4,input 2,input 7,input 0,input 1,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_22 : Impossible true (goalAt 183) 6 state183_22.toFinset :=
  node_ok cuts183 [] 0x21012101090300840422000880022020840486042101084062101012100584012140484022200484012100888022200484012100888021000840021010880811100484081820444085042101084052101011100544011140444021200444011100848021200444011100848024000900024040840484002100084042404024200d0c034300908024200d0c034300908034140840434140840490102101090102101011010d05021010d0502101204048101240408404 (by decide +kernel)

def state183_23 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000000000000000000,input 2,input 7,input 0,input 1,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_23 : Impossible true (goalAt 183) 7 state183_23.toFinset :=
  node_ok cuts183 [⟨state183_22,exclude183_22⟩] 0x1001608404210121010a28221011001628a08a28221010210108404341404404110108404b0a00840434142c280241408404110104404941404404110121010908021010941424200841421010110104404220204840220008404222008800220208880220208404121008404120208880120004404121004800120204840120204404222004404860604840860421010a2a021010860628a80840621010121021011000104840121009080161405841000205850121409080121004840210104440210008808212008400210108480210108808111008808110108480110004808111004400110104440110104808212004809002004440111004840838204841002020e0881820484011100444085050444085042101081802101085052060084052101011102101100200444011100908015140544100200545011140908011100444024044009024000840424200900024040908024040840500240840415050908015010440434300440415050d0c0110504404242004405000140004840021011000621011000109080242028a09000428a08210140058210128a09001628a08210140010210124201000724200110140018110124202000024200110140018110128a81000328a80121040008121028a81000228a8012104000c1210206010000206001110400801110206010020206001110400001110400050023204050006400888480 (by decide +kernel)

def state183_24 : List Sig := [0x5555555555555555555555555555555555555555555500005555555555550000,input 7,input 4,input 5,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_24 : Impossible true (goalAt 183) 5 state183_24.toFinset :=
  node_ok cuts183 [] 0x9400210008410210005400110004410110021400810020410810004840161004850121008c00210008408210004c00110004408110020c008100204088100084008100240c021000440021000905011000440081002404011000444011140544011100444081820484011100880821000c4402100048081100044401100210108100240408100 (by decide +kernel)

def state183_25 : List Sig := [0x3333333333333333333333333333333333333333333300003333333333330000,input 7,input 4,input 5,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_25 : Impossible true (goalAt 183) 5 state183_25.toFinset :=
  node_ok cuts183 [] 0x9800220008810220005800120004810120021800860021810830104440151004450111008c00220008804220004c00120004804120020c00830020c04860408800a200240c022000480022000905012000480092002404012000484012140584012100444081820444012100840422000c8402200044041200048401200204048101240408301 (by decide +kernel)

def state183_26 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0f0f0f0f0000,input 7,input 4,input 5,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_26 : Impossible true (goalAt 183) 5 state183_26.toFinset :=
  node_ok cuts183 [] 0x98002400090082400058001600058081501218008400210088400044401210206081110094002400090042400054001500054041602214008400210048400090008400240c024000d00024000905024002500084002404084000484012140484016100444011140444015100840424000d04024000440411010d0801501204048400240408400 (by decide +kernel)

def state183_27 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffff0000ffffffffffff0000,input 7,input 4,input 5,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_27 : Impossible true (goalAt 183) 6 state183_27.toFinset :=
  node_ok cuts183 [⟨state183_24,exclude183_24⟩,⟨state183_25,exclude183_25⟩,⟨state183_26,exclude183_26⟩] 0x34100d04034142120024200d08024300908094102404090142404200020908024204000412100584012140484012100c84022200484022200484012100888012102404022a00484200010484012104000c11100544011140444011100484081820444011100c440212004440212004440111008480111024040818004442000004440111040000b0102404090302404021010d050b08009050241424040b020240408414044048101 (by decide +kernel)

def state183_28 : List Sig := [0xffffffffffff0000ffffffffffff0000,input 7,input 4,input 5,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_28 : Impossible true (goalAt 183) 6 state183_28.toFinset :=
  node_ok cuts183 [] 0x34100d04034142120024200d08024300908084002100084042040412100584012140484012100c84022200484022200484012100888083012040481032040411100544011140444011100484081820444011100c440212004440212004440111008480810020400810121010a10120404a2822040434142c200241409050900024000908020404242021200242021200121028a80121028a80111020600111020600210108404341428a081101044050004242009010 (by decide +kernel)

def state183_29 : List Sig := [0xffffaaaaffffaaaaffffaaaaffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_29 : Impossible true (goalAt 183) 4 state183_29.toFinset :=
  node_ok cuts183 [] 0x5404110104414110121000840021010810105440111004450111004840161004850121004800120004808110120c0481012040c8101048401110206081110044042101090501101044001100044041202204008100204048404 (by decide +kernel)

def state183_30 : List Sig := [0xffffccccffffccccffffccccffffcccccccccccccccccccccccccccccccccccc,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_30 : Impossible true (goalAt 183) 4 state183_30.toFinset :=
  node_ok cuts183 [] 0x5404110104414110121000840021010810105840121004850121004440151004450111004400110004404120220400810020404840404440121020608111004404210109050110104800120004808110120c0481012040c8101 (by decide +kernel)

def state183_31 : List Sig := [0xfffff0f0fffff0f0fffff0f0fffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_31 : Impossible true (goalAt 183) 4 state183_31.toFinset :=
  node_ok cuts183 [] 0x4800120004808110120c0481012040c8101048401610048501210044401210206081110044001100044041202204008100204048404044401510044501110044042101090501101054041101044141101210008400210108101 (by decide +kernel)

def state183_32 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,0xffff0000ffff0000ffff0000ffff000000000000000000000000000000000000,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_32 : Impossible true (goalAt 183) 5 state183_32.toFinset :=
  node_ok cuts183 [⟨state183_29,exclude183_29⟩,⟨state183_30,exclude183_30⟩,⟨state183_31,exclude183_31⟩] 0x5404110104414110109080902080008242021000840021010810104840161004850121004800120004808110104840902080004121020c0481012040c8101044401510044501110044401210206081110044001100044041202044409020800001110204008100204048404044042101090501101242009010 (by decide +kernel)

def state183_33 : List Sig := [0xffffaaaaffffaaaaffffaaaaffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 7,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 5,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_33 : Impossible true (goalAt 183) 5 state183_33.toFinset :=
  node_ok cuts183 [⟨state183_29,exclude183_29⟩] 0x2410090402414212001501044041105044048400210008404204041510044401114044401210058401214048401210088401220048401200048001202044048301204048103204041210044408182044402101090508101800008101044048101210501101044402110044801110044001100044041202204008100204048404 (by decide +kernel)

def state183_34 : List Sig := [0xffffccccffffccccffffccccffffcccccccccccccccccccccccccccccccccccc,input 7,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 5,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_34 : Impossible true (goalAt 183) 5 state183_34.toFinset :=
  node_ok cuts183 [⟨state183_30,exclude183_30⟩] 0x241009040241421200150104404110504404840021000840420404161004840121404840111005440111404440111008440112004440110004400110104808810020400810121010111004840818204440210109050810180000810104404810121050110104840221004880121004800120004808110120c0481012040c8101 (by decide +kernel)

def state183_35 : List Sig := [0xfffff0f0fffff0f0fffff0f0fffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 7,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 5,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_35 : Impossible true (goalAt 183) 5 state183_35.toFinset :=
  node_ok cuts183 [⟨state183_31,exclude183_31⟩] 0x1210088401220048401200048001202044048301204048103204041210058401214048401110048408182044401110084401120044401100044001101048088100204008101210101110054401114044402101090508101800008101044048101210501101090402410090508480054041101044141101210008400210108101 (by decide +kernel)

def state183_36 : List Sig := [0xffff0000ffff0000ffff0000ffff000000000000000000000000000000000000,input 7,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 5,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_36 : Impossible true (goalAt 183) 6 state183_36.toFinset :=
  node_ok cuts183 [⟨state183_32,exclude183_32⟩,⟨state183_33,exclude183_33⟩,⟨state183_34,exclude183_34⟩,⟨state183_35,exclude183_35⟩] 0x24100904024142120015010440411050440484002100084042040424202c28200030908012100584012140484012100884012200484012000480012020440483012040481032040412102c28200020484011100544011140444011100484081820444011100844011200444011000440011010480881002040081012101011102c2820001044402101090508101800008101044048101210501101400102414242802414242009010 (by decide +kernel)

def state183_37 : List Sig := [0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000,input 7,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 5,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_37 : Impossible true (goalAt 183) 6 state183_37.toFinset :=
  node_ok cuts183 [] 0x9040241009050848005404110104414110125040901024050901004840161004850121004840221004880121004800120004808110104840901028a80121004440151004450111004440121020608111004440211004480111004400110004404120204440901020600111008404b01024040902024040900024000901004404848009080848009080a2a004840a2a00484081800444081800444090a009050b0a0090510004044049080044048101 (by decide +kernel)

def state183_38 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 7,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_38 : Impossible true (goalAt 183) 6 state183_38.toFinset :=
  node_ok cuts183 [⟨state183_32,exclude183_32⟩] 0x90803420090c0242021200242009080848009080a4202120024200d04034100d051001e04840161004850121008880121004840222028a00121004841001404840a22008a80121004840321008880121004440151004450111004440121020608111008480111004440212020600111004440818004440a12020600111004440311008480111004404902024080903080000341424280241409050903028a08903008a082101084043414400188101 (by decide +kernel)

def state183_39 : List Sig := [0xbbbbbbbbbbbbaaaabbbbbbbbbbbbaaaabbbbbbbbbbbbaaaabbbbbbbbbbbbaaaa,input 0,input 4,input 5,input 2,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_39 : Impossible true (goalAt 183) 5 state183_39.toFinset :=
  node_ok cuts183 [] 0x8400210008404204042600088002204088001600048001204048002200288009030088001200248009010048001200088002414048008101210108101210101110054401114044402101088002101088001101048001101048008180204048404204048404048401214058401210084042200084042200044041200044041200 (by decide +kernel)

def state183_40 : List Sig := [0xfafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafa,0x1111111111110000111111111111000011111111111100001111111111110000,input 4,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_40 : Impossible true (goalAt 183) 4 state183_40.toFinset :=
  node_ok cuts183 [] 0x8800a200240c022000480092002404012000480022000905012000484081012404081010900422000c8402200088801200048401200048401114044401110204008100204049010084002100084042200044001100044041200 (by decide +kernel)

def state183_41 : List Sig := [0x1111111111110000111111111111000011111111111100001111111111110000,input 0,input 4,input 5,input 2,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_41 : Impossible true (goalAt 183) 5 state183_41.toFinset :=
  node_ok cuts183 [⟨state183_40,exclude183_40⟩] 0x8400210008404204042600088002204088001600048001204048002200288009030088001200248009010048001200088002414048008100204008101210108180090820000090802100084002101088001100044001101048001210204049010204041210048501610048402404088003210088002220048001210048001110 (by decide +kernel)

def state183_42 : List Sig := [0xfafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafa,input 0,0x3333333333330000333333333333000033333333333300003333333333330000,input 4,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_42 : Impossible true (goalAt 183) 5 state183_42.toFinset :=
  node_ok cuts183 [⟨state183_40,exclude183_40⟩] 0x220028800903008800120024800901004800120008800241404800121020404901020404210108800321008800110104800121004800121080000111404840121004850161004840810120410810121004230108800230108800130104800130104800111021000840020404901009800220008c04220005800120004c041200 (by decide +kernel)

def state183_43 : List Sig := [0x3333333333330000333333333333000033333333333300003333333333330000,input 4,input 5,input 0,input 2,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_43 : Impossible true (goalAt 183) 6 state183_43.toFinset :=
  node_ok cuts183 [⟨state183_39,exclude183_39⟩,⟨state183_41,exclude183_41⟩,⟨state183_42,exclude183_42⟩] 0x2101024202100081012120084002101084802101081010908081010981084800980022000908022000981024200881022002120022000581024200580012000d0c01200058103430048101200090801200204041110204008404206008100204048180204048404044408404400a0111004440242005450151080008151404450242004440111008c04111008c00220008480220008c04212008804220004440220004c04212004c00120004440120004c0411100480412000848012002c0c0220008800810128a00a2002c0c0a280240c0810108800220024040120004800810124a0092002404092802404081010480012000d05012000480022002c28022000d050b0a009050220004800120024040121004840810128a80810124040a2a02404081010484081010908012100484084800585012140908016140584084800484012100444012100444081808000481800444200000444081800484012100d05012100840422000888022000d05022200c84022000484022002c28022200440412000484012002c2801210048401200088801200 (by decide +kernel)

def state183_44 : List Sig := [0x3333333333330000333333333333000033333333333300003333333333330000,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,input 5,input 0,input 2,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_44 : Impossible true (goalAt 183) 6 state183_44.toFinset :=
  node_ok cuts183 [] 0x2100084002101081010d04034100d0508480090803420090c024202120024200908084802040081002040484040444015100445011100444031100848011100848011100444021202060011100444081802c0408101240c081010880090102040490102040434142c2802414048009010204049010204041210204049010204041210048501610048401110206001110048401210088803210048402220048401210088810029 (by decide +kernel)

def state183_45 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,input 5,input 0,input 1,input 2,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_45 : Impossible true (goalAt 183) 7 state183_45.toFinset :=
  node_ok cuts183 [⟨state183_27,exclude183_27⟩,⟨state183_28,exclude183_28⟩,⟨state183_36,exclude183_36⟩,⟨state183_37,exclude183_37⟩,⟨state183_38,exclude183_38⟩,⟨state183_43,exclude183_43⟩,⟨state183_44,exclude183_44⟩] 0x84040908084002040484802100084042120084042040424202040434142120034104007824200d04034140908034144001084802120100160908024202c28034300d08100160d0c024302c280242009081001621200848040004242009081001609080242040004848021200830304840830120404a2a020404830328a8081032040412102040486820484012100908016140584086820585012140908012100484100040484012100d05022200c84100050888022200d05012100484100050888022202c28012100484100050484012102c28022200888100058001a00054000c12100484100050484012104000d00054000c810104440810021010818020400810120600810121010111021011002704440111009080151405441002705450111409080111004441002704440111004840838204841002720e0881820484011100444100270444011100d05021200c44100270848021200d05011100444100270848021202c28011100444100270444011102c280212008481002720600818040000111004441002704440111040000818020600b0300d050b01020405000420404b0308001090302040434142040500264001c21012404200032404081012c280810124040b0a02404081018000881010d05100040d05100072c280b0a0400110004090510025400101101240410006240408101800048101240420000240408101400188101 (by decide +kernel)

def state183_46 : List Sig := [0xf0f0f0f0fffff0f0f0f0f0f0fffff0f0f0f0f0f0fffff0f0f0f0f0f0fffff0f0,input 4,input 5,input 0,input 1,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_46 : Impossible true (goalAt 183) 6 state183_46.toFinset :=
  node_ok cuts183 [] 0x20c0c121020c04810128a80810120c0ca2a02040c810104840810108808121008800210108880220008808222008808210104840210104818222004810110504840120404818121004818110508880110521a08222008880242004840121021a081210048402420088802220204041110204008404206008100204048180204048404044408404400ac111004440121020e0812104007483822060812100444011100840411100840022020848021000840421200840422020444022020441421200441012060444011040441411100441412060848012064005c21200848024200444011104007411100444024200848021202c0c0210108404810128a0881012c0c0a2822c0c081010840421012404011052401081012c280810124040b0a02104081010441481010d04011050c40421012c28021010d040b0a009040210104414210121010242021000810121200840021010848021010810109080810109010848009000210109080240009010242009010210121200210104414242004404b0a00d0c0110104414343004414b0a0090802420 (by decide +kernel)

def state183_47 : List Sig := [0xffffffffffffffffffffffffffffffff00000000ffff000000000000ffff0000,input 7,input 4,input 5,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_47 : Impossible true (goalAt 183) 6 state183_47.toFinset :=
  node_ok cuts183 [] 0x24000900024040840424200d080243009080941024040901424040242021200848009080121005840121404840220008800220208404222004840121008880121024040a2a004840222004840121008880111005440111404440111004840818204440210008400210108808212004440111008480111024040818004440212004440111008480210124040a28208404210128a0834140840431010840490a0084049010242009010210501101044049080400108101 (by decide +kernel)

def state183_48 : List Sig := [0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000,input 7,0xffff000000000000ffff000000000000ffff000000000000ffff0000,input 5,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_48 : Impossible true (goalAt 183) 6 state183_48.toFinset :=
  node_ok cuts183 [] 0x240009000240408404941024040901424040121005840121404840220008800220208404121024040a2a004840111005440111404440111004840818204440210008400210108808111024040818004440b0002c000b02008404110105404110504404120004800120204404110004400110104808241424000900024040110124200848009080848009080a2a004840a2a004840818004440818004440a28208404b080084048101 (by decide +kernel)

def state183_49 : List Sig := [0xffff000000000000ffff000000000000ffff000000000000ffff0000,input 4,input 5,input 0,input 1,input 2,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_49 : Impossible true (goalAt 183) 7 state183_49.toFinset :=
  node_ok cuts183 [⟨state183_46,exclude183_46⟩,⟨state183_47,exclude183_47⟩,⟨state183_48,exclude183_48⟩] 0x84040908084002040484802100084042120084042040424202040424042120024000840424200900024040908024040840484800840500160908024202c28034300d08100160d0c024302c280242009080830304840830120404a2a020404830328a8081032040412102040486820484012100908016140584086820585012140908012100484022020484022000840422200880022020888022020840412100840500050888022202c28012100484100050484012102c280222008880810104440810021010818020400810120600810121010111021011002604440111009080151405441002605450111409080111004441002604440111004840838204841002620e0881820484011100444021010444021000880821200840021010848021010880811100880900260848021202c28011100444100260444011102c280212008480b03008404210120404a28220404b03028a08b03020404210108404901080008901020404b0a02040490102c28090102040500072040500044001031014001cb0a02c28021014001021012404100062404081014001c81012404200012404081014001881014005900014000424204005824204001d00168000024204000424200484100030484022204001422200484100050484022204000c22200444100000444021204009821200444100260444021204000021204001d00270d0510004400a81101 (by decide +kernel)

def state183_50 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffff00000000ffffffff00000000,input 4,input 7,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_50 : Impossible true (goalAt 183) 6 state183_50.toFinset :=
  node_ok cuts183 [] 0x2101024202100081012120084002101084802101081010908081010541424200540411010d0c0110105414343004414110109080110109010848009000210109080240009010242009010210121200210121a08121004840242005850161021a08161404850242004840121020c0c121020c04810128a80810120c0ca2a02040c81010484081010480822200480011010484012000480812100480811010888011010880812100880021010888022000880822200880821010484021014004c11100444024200545015104004c151404450242004440111040044111004440121020e0812104004c8382206081210044401110204041110204008404206008100204048180204048404044408404044042120044001202044401100044041110044041202084801202084041110084002202084802100084042120084042202044402202240c01101044048101242808101240c090a02105081010440411010d05011010440421012428021010d05090a0090502101044041101240c0210108404810128a088101240c0a282240c08101084042101 (by decide +kernel)

def state183_51 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffff00000000ffffffff00000000,input 5,input 4,input 7,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_51 : Impossible true (goalAt 183) 6 state183_51.toFinset :=
  node_ok cuts183 [] 0x84002100084042040415010440411050440484800908024202120084800908024202120012100584012140484083012040481032040412000480012020440412100888022200484012100888022200484011100544011140444011100484081820444081002040081012101011000440011010480811100848021200444011100848021200444011012040484140440411012c28090a004404110124200b0a004404b0302040490302040421012404081012c0c08101 (by decide +kernel)

def state183_52 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,0xffffaaaaffffaaaaffffaaaaffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 4,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_52 : Impossible true (goalAt 183) 5 state183_52.toFinset :=
  node_ok cuts183 [⟨state183_29,exclude183_29⟩] 0x150104404110504404151004440111404440248009080242021080840021000840420404121005840121404840120004800120204404121004440818204440121008880222004840830120404810320404110004400110104808110108a0a0000044041101204048414044041110084802120044408100204008101210102101 (by decide +kernel)

def state183_53 : List Sig := [0xffffaaaaffffaaaaffffaaaaffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 4,input 7,input 1,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_53 : Impossible true (goalAt 183) 6 state183_53.toFinset :=
  node_ok cuts183 [⟨state183_33,exclude183_33⟩,⟨state183_52,exclude183_52⟩] 0x40018210108404810128a08810180004a28208a0881010840421010901084800900021010908024000901024200901021012120021012101024202100081012120084002101084802101081010908081010541424200540411010d0c011010541434300441411010908011010545024200544011104004c111005451001304450111009080111008808121008800210108880220008808222008808210104840210121a08121004840242005850161021a08161404850242004840121020c0c121020c04810128a80810120c0ca2a02040c810104840810104808222004800110104840120004808121004808110108880110120e08121004840111040044111020e0900132060811100484011100d05011010440421014001c21010d05200000905021010440411014001811010440481014001881014001d0006210508101044041101044401202044002120044041100044401101044042120048081202084041110084002202084802100084042120084042202044402202204041110204008404206008100204048180204048404044408404 (by decide +kernel)

def state183_54 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,0xffffccccffffccccffffccccffffcccccccccccccccccccccccccccccccccccc,input 4,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_54 : Impossible true (goalAt 183) 5 state183_54.toFinset :=
  node_ok cuts183 [⟨state183_30,exclude183_30⟩] 0x150104404110504404161004840121404840248009080242021080840021000840420404111005440111404440110004400110104808111004840818204440111008480212004440810020400810121010120004800120204404110108a0a0000044041101204048414044041210088802220048408301204048103204042101 (by decide +kernel)

def state183_55 : List Sig := [0xffffccccffffccccffffccccffffcccccccccccccccccccccccccccccccccccc,input 4,input 7,input 0,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_55 : Impossible true (goalAt 183) 6 state183_55.toFinset :=
  node_ok cuts183 [⟨state183_34,exclude183_34⟩,⟨state183_54,exclude183_54⟩] 0x40018210108404810128a08810180004a28208a0881010840421010901084800900021010908024000901024200901021012120021012101024202100081012120084002101084802101081010908081010541424200540411010d0c0110105414343004414110109080110105850242005840121021a0812100585086820485012100908012100840411100840022020848021000840421200840422020444022024004c11100444024200545015104004c151404450242004440111020404111020400840420600810020404818020404840404440840404404212004400120204440110004404111004404120208480120240044111004440121020e0812104004c83822060812100444011100d05011010440421014001c21010d05200000905021010440411014001811010440481012420881014001c908221050810104404110104840110104800222004808120004840120204808222004404110108808121008800210108880220008808222008808210104840210120c0c121020c04810128a80810120c0ca2a02040c8101048408101 (by decide +kernel)

def state183_56 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,0xfffff0f0fffff0f0fffff0f0fffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 4,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_56 : Impossible true (goalAt 183) 5 state183_56.toFinset :=
  node_ok cuts183 [⟨state183_31,exclude183_31⟩] 0x120004800120204404121005840121404840121008880222004840830120404810320404111004840818204440110004400110104808111005440111404440111008480212004440810020400810121010110105404110504404110108a0a0000044041101204048414044042480090802420210808400210008404204042101 (by decide +kernel)

def state183_57 : List Sig := [0xfffff0f0fffff0f0fffff0f0fffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 4,input 7,input 0,input 1,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_57 : Impossible true (goalAt 183) 6 state183_57.toFinset :=
  node_ok cuts183 [⟨state183_35,exclude183_35⟩,⟨state183_56,exclude183_56⟩] 0x40018210108404810128a08810180004a28208a08810108404210108808121008800210108880220008808222008808210104840210120c0c121020c04810128a80810120c0ca2a02040c810104840810104808222004800110104840120004808121004808110108880110121a08121004840242005850161021a08161404850242004840121008404111008400220208480210008404212008404220204440220240044111004440121020e0812104004c83822060812100444011102040411102040084042060081002040481802040484040444084040440421200440012020444011000440411100440412020848012024004c11100444024200545015104004c15140445024200444011100d05011010440421014001c21010d05200000905021010440411012405011010440481014001881012405100062105081010440411010d0c011010440424200541415010d0c01505044142420044041101090108480090002101090802400090102420090102101212002101210102420210008101212008400210108480210108101090808101 (by decide +kernel)

def state183_58 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,0xffff0000ffff0000ffff0000ffff000000000000000000000000000000000000,input 4,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_58 : Impossible true (goalAt 183) 6 state183_58.toFinset :=
  node_ok cuts183 [⟨state183_32,exclude183_32⟩,⟨state183_52,exclude183_52⟩,⟨state183_54,exclude183_54⟩,⟨state183_56,exclude183_56⟩] 0x15010440411050440424202c0c200030908024800908024202108084002100084042040412100584012140484012000480012020440412102c0c200020484012100888022200484083012040481032040411100544011140444011100484081820444011000440011010480811102c0c2000104440111008480212004440810020400810121010110108a0a000004404110120404841404404b02040010b030240c09030240402101 (by decide +kernel)

def state183_59 : List Sig := [0xffff0000ffff0000ffff0000ffff000000000000000000000000000000000000,input 4,input 7,input 0,input 1,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_59 : Impossible true (goalAt 183) 7 state183_59.toFinset :=
  node_ok cuts183 [⟨state183_50,exclude183_50⟩,⟨state183_51,exclude183_51⟩,⟨state183_36,exclude183_36⟩,⟨state183_53,exclude183_53⟩,⟨state183_55,exclude183_55⟩,⟨state183_57,exclude183_57⟩,⟨state183_58,exclude183_58⟩] 0x1000608404210120404a28220406000628a0822822040421010840424042120024000840424200900024040908024040840484800840484040908084002040484802100084042120084042040424202040415050908015010440434300440415050d0c011050440424200440500060908024204000500064000500174001a000540004242009080220204840220008404222008800220208880220208404121008404868204840121009080161405840868205850121409080121004840830304840830120404a2a020404830328a8081032040412102040412020888012000440412100480012020484012020440422200440500060484012104000d00064000d00114001a00044000c121004840210104440210008808212008400210108480210108808111008809002e04440111009080151405441002e05450111409080111004441002e04440111004840838204841002e20e08818204840111004440810104440810021010818020400810120600810121010111021010110108480110004808111004400110104440110104808212004809002e04440111040001002e40001002e4001a00034000011100444034140440411010840500070840434148000824140840411010440500060440411012040500062040500074001884144001900044001021014001821014001a000180000210140010210140019002d240410006400b09080 (by decide +kernel)

def state183_60 : List Sig := [0x3333333333333333333333333333333333330000333300003333000033330000,input 1,input 4,input 7,input 0,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_60 : Impossible true (goalAt 183) 6 state183_60.toFinset :=
  node_ok cuts183 [] 0x210128808903008404240009000240408404860221808860620c0c160204808120604808210008400210108808111005440111404440830220c08830321818130204808120304808111008880838204440120208404341408404120224808901004808220008800220208404222009080868208880830120c04830324040120004800120208880341408404341408404343009080343009080111008480111008480810120404901020c0c1101044049080048081210 (by decide +kernel)

def state183_61 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f00000f0f00000f0f0000,input 2,input 4,input 7,input 0,input 1,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_61 : Impossible true (goalAt 183) 6 state183_61.toFinset :=
  node_ok cuts183 [] 0x210121010903008404220008800220208404860421010840621010160405810160605414121005850161404840210008400210108808111004840818204440850421010840521010150405410150505818111005450151404440340408404241408404940421010901021010240009000240408404840021000840424040150105404150509080a28208404a282084041210058501210058501110054501110054508101204049010210101101044049080054143430 (by decide +kernel)

def state183_62 : List Sig := [0xffffffff00000000ffffffff00000000ffff000000000000ffff0000,input 5,input 4,input 7,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_62 : Impossible true (goalAt 183) 6 state183_62.toFinset :=
  node_ok cuts183 [] 0x94102404090142404024200d08024300908024000900024040840412100584012140484012102404022a00484022200484012100888022000880022020840411100544011140444011100484081820444011102404081800444021200444011100848021000840021010880890102c080901021050310108404b0a008404210128404b0300840484800908084800908012100888012100888011100848011100848081012040490102c0c011010440490802c2803414 (by decide +kernel)

def state183_63 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 4,input 7,input 0,input 1,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_63 : Impossible true (goalAt 183) 7 state183_63.toFinset :=
  node_ok cuts183 [⟨state183_0,exclude183_0⟩,⟨state183_60,exclude183_60⟩,⟨state183_6,exclude183_6⟩,⟨state183_10,exclude183_10⟩,⟨state183_12,exclude183_12⟩,⟨state183_61,exclude183_61⟩,⟨state183_14,exclude183_14⟩,⟨state183_18,exclude183_18⟩,⟨state183_27,exclude183_27⟩,⟨state183_62,exclude183_62⟩] 0xb03008404210124040a28224040b03028a0890302404021010840600090840421014001034140d05200080d05034144001021010840424042120024000840424200900024040908024040840484800840494140908094102404084802404094142120090142404024202404200070908024202420034300d0c200060d0c034302420024200908200050908024204000434300d0c200040d0c0343040004242009080220204840220008404222008800220208880220208404121008404868204840121009080161405840868205850121409080121004842000304840121024040a2a024042000228a80a2a02404012100484092820888022202420012100484092820484012102420022200888200010888022204000c12100484200000484012104000c222008880210104440210008808212008400210108480210108808111008809002f04440111009080151405441002f05450111409080111004441002f04440111004840838204841002f20e08818204840111004441002f04440111024040818024041002f20600818024040111004441002f08480212024200111004441002f04440111024200212008481002f08480212040000111004441002f04440111040000212008481002c4001c81010d05090800d05021012c28021010d050b0a00d05021012420021012404100062404100072420090804001d000621051002d400181101 (by decide +kernel)

def state183_64 : List Sig := [0xccccccccccccccccccccccccccccccccffffccccffffccccffffccccffffcccc,input 1,input 4,input 7,input 0,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_64 : Impossible true (goalAt 183) 6 state183_64.toFinset :=
  node_ok cuts183 [] 0x21012040422820840424000900024040840484002100084042040416020480812060480821000840021010880811100544011140444081002040081012101013020480812030480811100484083820444021200444011100848012020840434140840490002400090802040422020840422020840412100584012140484083032040483032040412020484012020440c22200880821010880821010d0c024200d0c0242020c0c810120c0c8101044041101048089080 (by decide +kernel)

def state183_65 : List Sig := [0x3333333300000000333333330000000033333333333300003333333333330000,input 5,input 4,input 7,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_65 : Impossible true (goalAt 183) 5 state183_65.toFinset :=
  node_ok cuts183 [] 0x21000840021010810105800120004810120009800220008810220004440151004450111020400810020404840404c00120004804120008c0022000880422000480090002c0c0120004800220009050120008800a2002c0c022000484012140584012100444081800444012100484081012404081010440412000484012000840422000c8402200 (by decide +kernel)

def state183_66 : List Sig := [0xffffffff00000000ffffffff00000000ffffffffffff0000ffffffffffff0000,input 5,input 4,input 7,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_66 : Impossible true (goalAt 183) 6 state183_66.toFinset :=
  node_ok cuts183 [⟨state183_65,exclude183_65⟩] 0x84002100084042040424200d08024300908034100d04034142120084800908024202120012100584012140484083012040481032040422200484012100888012100c84022200484200000484012104000c11100544011140444011100484081820444081002040081012101021200444011100848011100c440212004440818004440111020600900024000b0302040434142c280241409050110104404b0a024200b01020404b0302040421012c0c08101240408101 (by decide +kernel)

def state183_67 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,0xffff0000ffff0000ffff0000ffff0000,input 4,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_67 : Impossible true (goalAt 183) 6 state183_67.toFinset :=
  node_ok cuts183 [] 0x9080b0200d0c0242009200242009080842021000840021010810104840161004850121008880121004840222004840222008880121020c0481012040c810104440151004450111004440121020608111008480111004440212004440212008480111020400810020404840424200b0202408090202400090002c08081010d0c024200d0c02420048402220048402220044402120044402120044049030240c0b03008a090004204049010204042101 (by decide +kernel)

def state183_68 : List Sig := [0xffffffff00000000ffffffff00000000000000000000000000000000,input 5,0xffff0000ffff0000ffff0000ffff0000,input 4,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_68 : Impossible true (goalAt 183) 6 state183_68.toFinset :=
  node_ok cuts183 [] 0x24202c080343009080240009000240408404121005840121404840222004840121008880220008800220208404111005440111404440111004840818204440212004440111008480210008400210108808b0002c00034140840434300908034300908012100888012100888011100848011100848011010d05021012c040210124040840021000840420404810120c048103204048100204008101210109000240009080204042282 (by decide +kernel)

def state183_69 : List Sig := [0xffff0000ffff0000ffff0000ffff0000,input 4,input 7,input 0,input 1,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_69 : Impossible true (goalAt 183) 7 state183_69.toFinset :=
  node_ok cuts183 [⟨state183_64,exclude183_64⟩,⟨state183_66,exclude183_66⟩,⟨state183_67,exclude183_67⟩,⟨state183_68,exclude183_68⟩] 0x2000308404210120404a28220406000228a0822822040421010840424042120024000840424200900024040908024040840484800840484040908084002040484802100084042120084042040424202040500070908024202420034300d0c100170d0c0343024200242009080220204840220008404222008800220208880220208404121008404868204840121009080161405840868205850121409080121004840830304840830120404a2a020404830328a80810320404121020404928208880222024200121004840928204840121024200222008880210104440210008808212008400210108480210108808111008809002c04440111009080151405441002c05450111409080111004441002c04440111004840838204841002c20e08818204840111004440810104440810021010818020400810120600810121010111021011002c08480212024200111004441002c04440111024200212008480341424200341408404b0a00840434142c28034140840490800840500074001890004001c90802420081014001881010d05100040d05021014001c21010d05200010d05021014001021010d0c100010d0c024204001c24200d0c100170d0c024204000424200484100030484022204001c22200484200000484022204000c2220044410000044402120400b0212004441002c0444021204000021204001d002f240410006400b81101 (by decide +kernel)

def state183_70 : List Sig := [0xf0f0fffff0f0fffff0f0fffff0f0fffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 2,input 4,input 7,input 0,input 1,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_70 : Impossible true (goalAt 183) 6 state183_70.toFinset :=
  node_ok cuts183 [] 0x2101210109030084042200088002202084048604210108406210101200048001202044041210058501614048401210058501614048402100084002101088081110048408182044408504210108405210101100044001101048081110054501514044401110054501514044401101084042414044049000240009010044042404084042404084048404240408404204141505044041505044042420090102101090102101204048101210109010054141101054141101 (by decide +kernel)

def state183_71 : List Sig := [0xf0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f000000000f0f0f0f00000000,input 5,input 4,input 7,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_71 : Impossible true (goalAt 183) 5 state183_71.toFinset :=
  node_ok cuts183 [] 0x2180084002100884000480012000480811010980024000900824000444012102060811102140084002100484000440011000440412020940024000900424002400084002104084000d00024000904024000900084002c0c024000888012100888012100848011100848011102040484002908084000908011010d0801101084042400090802400 (by decide +kernel)

def state183_72 : List Sig := [0xffffffff0000ffffffffffff0000ffffffffffff00000000ffffffff00000000,input 5,input 4,input 7,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_72 : Impossible true (goalAt 183) 6 state183_72.toFinset :=
  node_ok cuts183 [⟨state183_71,exclude183_71⟩] 0x94102404090142404015010440411050440484800908024202120200000908024204000412100584012140484012102404022a00484012000480012020440412100888022200484012100888022200484011100544011140444011100484081820444011102404081800444011000440011010480811100848021200444011100848021200444090002400090100440411012c200b0a00440411012c280908004404b03024040b0302404021012040481012c0c09010 (by decide +kernel)

def state183_73 : List Sig := [0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000,input 4,input 7,input 0,input 1,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_73 : Impossible true (goalAt 183) 7 state183_73.toFinset :=
  node_ok cuts183 [⟨state183_70,exclude183_70⟩,⟨state183_72,exclude183_72⟩,⟨state183_37,exclude183_37⟩,⟨state183_48,exclude183_48⟩] 0xb03008404210124040a28224040b03028a0890302404021010840424042120024000840424200900024040908024040840484800840494140908094102404084802404094142120090142404024202404015050908015010440434300440415050d0c0110504404242004404220204840220008404222008800220208880220208404121008404868204840121009080161405840868205850121409080121004841000604840121024040a2a024041001128a80a2a024040121004840120208880120004404121004800120204840120204404222004404210104440210008808212008400210108480210108808111008809002d04440111009080151405441002d05450111409080111004441002d04440111004840838204841002d20e08818204840111004441002d04440111024040818024041002d20600818024040111004440110108480110004808111004400110104440110104808212004808341404404110108406000308404341480008241408404110104405000740018900024041000624041000604404110128a09000428a08210140018210128a0a000128a08210140010210121201000121200242040018242021202000021200242040004242028a81000328a80121040018121028a81001128a8012104000c1210206010000206001110400b4111020601002d20600111040000111040019002e204050006400bc9080 (by decide +kernel)

def state183_74 : List Sig := [0xafafafafafafafafafafafafafafafafafafafafaaaaaaaaafafafafaaaaaaaa,input 0,input 5,input 7,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_74 : Impossible true (goalAt 183) 5 state183_74.toFinset :=
  node_ok cuts183 [] 0x9400210008410210003400090002410090001200048001202044048600210008402210002600090002402090002400210009030090001101048081101048082120048408182048408101210008101210002101090002101090001110044041202044041202088801210088801210204048400204048400084042400084042400 (by decide +kernel)

def state183_75 : List Sig := [0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,0x505050505050505050505050505050505050505000000000505050500000000,input 5,input 7,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_75 : Impossible true (goalAt 183) 4 state183_75.toFinset :=
  node_ok cuts183 [] 0x2500084002104084000d0002400090402400090008400240c024000908011010d0801101240408400290808400088042400090802400088801110084801110044001100044042220204008100204048400084002100084042400 (by decide +kernel)

def state183_76 : List Sig := [0x505050505050505050505050505050505050505000000000505050500000000,input 0,input 5,input 7,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_76 : Impossible true (goalAt 183) 5 state183_76.toFinset :=
  node_ok cuts183 [⟨state183_75,exclude183_75⟩] 0x940021000841021000340009000241009000120004800120204404860021000840221000260009000240209000240021000903009000110004400110104808111004842000004440810020400810121000210008400210109000242004404342004404222004840222004840901021000a420210002202090002420090002120 (by decide +kernel)

def state183_77 : List Sig := [0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f00000000,input 5,input 7,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_77 : Impossible true (goalAt 183) 5 state183_77.toFinset :=
  node_ok cuts183 [⟨state183_75,exclude183_75⟩] 0x940021000841021000340009000241009000240021000903009000242004404342004404810121000a420210002101090002420090002420800008182090802220048402220048401101044081101048048501210008501210002501090002501090001110048001200044042220218008400214048400098002400094042400 (by decide +kernel)

def state183_78 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f00000000,input 5,input 7,input 0,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_78 : Impossible true (goalAt 183) 6 state183_78.toFinset :=
  node_ok cuts183 [⟨state183_74,exclude183_74⟩,⟨state183_76,exclude183_76⟩,⟨state183_77,exclude183_77⟩] 0x2504011012500084002420084002504090802104084000440484000d04011010d00024002c28024000d040b0a009040240004404240004808222004800110104840120004808121004808110108880110121808121021800840028a80840021808a2a0210088400048408400098081210098002400088802400098082220090082400048402400044042120044001202044401100044041110044041202084801202400cc111004440121020e0812108000883822060812100444011102140411102140084002060084002140481802100484000444084000940411100940024000848024000940421200900424000444024002c0c0240009000840028a0884002c0c0a282240c084000900024002420024200908011010d0c011012420034300d080110109080110108880242008880121021a0812100888086820888012100908012100848024200848011108000411100848200000848011100908011102c0c024202040484002120084002c0c0848029080840009080840028a08848008404240009080240028a082420090802400212002400 (by decide +kernel)

def state183_79 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f00000000,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,input 7,input 0,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_79 : Impossible true (goalAt 183) 6 state183_79.toFinset :=
  node_ok cuts183 [] 0x4404b0202c0c0110104404b08024280110104404908024200110104800120004808110104840a22008a80121004840222008880121004840222008880121004400110004404120204440121020608111004440a12020600111004440212008480111004440212008480111021000b03028a08903009000242004404342004404222004840222004840212004440212004440242021200a420090808480090802420212010034 (by decide +kernel)

def state183_80 : List Sig := [0xffff0000ffff0000ffff0000ffff0000ffff000000000000ffff00000000,input 4,input 5,input 7,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_80 : Impossible true (goalAt 183) 6 state183_80.toFinset :=
  node_ok cuts183 [] 0x94102404090142404034100d04034142120015010440411050440412100584012140484012102404022a00484012100c84022200484012000480012020440411100544011140444011100484081820444011102404081800444011100c440212004440110004400110104808b0102404090302404090002400090100440411010c40434140440424200d0c024200d0c0222004840222004840212004440212004440810120405000424040210108404a2820d0509080 (by decide +kernel)

def state183_81 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,input 7,input 0,input 1,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_81 : Impossible true (goalAt 183) 7 state183_81.toFinset :=
  node_ok cuts183 [⟨state183_78,exclude183_78⟩,⟨state183_79,exclude183_79⟩,⟨state183_27,exclude183_27⟩,⟨state183_80,exclude183_80⟩,⟨state183_38,exclude183_38⟩,⟨state183_58,exclude183_58⟩,⟨state183_67,exclude183_67⟩] 0xb0300440411018001890802c080b03024200b03080014110104405000404404110128a08b0a02c20200042c28090a028a0811010440600030440411014001c90802420200022420090804001c11010440415050908015010440434300440415050d0c011050440424200440500160908024202c0c084802908100162120084802c0c0242009081000421200848028a08242009081001609080242028a0884802120100168000600004000424200908100160908024204000500164000412020888012000440412100480012020484012020440422200440486820484012100908016140584086820585012140908012100484100050484012102c0c0a2a028881000528a8022a02c0c0121004840a28204840121040050222008880a2820888022204001012100484100050484012104000c22200888100050888022204000c121004840110108480110004808111004400110104440110104808212004809003204440111009080151405441003205450111409080111004441003204440111004840838204841003220e0881820484011100444100320444011102c0c081802848100322060081802c0c0111004441003204440111028a08212008481003208480212028a0811100444100320444011104000021200848100320848021204000011100444100314001081012c0c100062c0c1000428a08a282400110004240c10030400182101 (by decide +kernel)

def state183_82 : List Sig := [0xccccccccffffffffccccccccffffffffcccccccccccccccccccccccccccccccc,input 5,input 7,input 0,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_82 : Impossible true (goalAt 183) 6 state183_82.toFinset :=
  node_ok cuts183 [] 0x2c0c011010440481032420090022c0c090802c0c081030440411010d05011010440421012c28021010d050b0a00905021010440411010541424200540411010d0c01101054143430044141101090801101210182420210088103212008402210188480210188103090808103090108480090002101090802400090102420090102101212002101044042120044001202044401100044041110044041202084801202400d811100444024200545015104004c15140445024200444011102040c11102040884062060081022040c81802040c84060444084060840411100840022020848021000840421200840422020444022024004411100444012102060012104004c81802060012100444011102c0c0210108404810328a00a1012c0c0a2802c0c081030840421010480822200480011010484012000480812100480811010888011012120012100484024200585016102120016140485024200484012102040c121020404b03028a8081012040ca2a02040cb030048401210088081210088002101088802200088082220088082101048402101 (by decide +kernel)

def state183_83 : List Sig := [0xffff0000ffffffffffff0000ffffffffffff0000ffff0000ffff0000ffff0000,input 4,input 5,input 7,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_83 : Impossible true (goalAt 183) 6 state183_83.toFinset :=
  node_ok cuts183 [] 0x94102404090142404024000900024040840424200d0c034300908024200d0c034300908012100584012140484012102404022a00484022000880022020840422200484012100888022200484012100888011100544011140444011100484081820444011102404081800444021000840021010880821200444011100848021200444011100848021012840490300840490102420090102105034140840434140840411012040481012404100040d05021010d0502101 (by decide +kernel)

def state183_84 : List Sig := [0xffffffff00000000ffffffff00000000000000000000000000000000,input 5,input 7,input 0,input 1,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_84 : Impossible true (goalAt 183) 7 state183_84.toFinset :=
  node_ok cuts183 [⟨state183_82,exclude183_82⟩,⟨state183_83,exclude183_83⟩,⟨state183_68,exclude183_68⟩] 0xb0300440411018000890802c080b03024200b03040018110104404341404404110108404b0a00840434142c28024140840411010440415050908015010440434300440415050d0c011050440424200440500160908024202c0c084802908100162120084802c0c024200908024042120024000840424200900024040908024040840484800840412020888012000440412100480012020484012020440422200440486820484012100908016140584086820585012140908012100484100050484012102c0c0a2a028881000528a8022a02c0c0121004840220204840220008404222008800220208880220208404121008404110108480110004808111004400110104440110104808212004809003004440111009080151405441003005450111409080111004441003004440111004840838204841003020e0881820484011100444100300444011102c0c081802848100302060081802c0c0111004440210104440210008808212008400210108480210108808111008809000440010a1012c0c100062c0c100040840421012420100072420011014001811012420200012420011014001811012120100012120024204005824202120100162120024204000424204001500034000c12104001412104001900058000012104000c1210206010000206001110400c01110206010030206001110400001110400110035204050006400c8a282 (by decide +kernel)

def state183_85 : List Sig := roots 183
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_85 : Impossible true (goalAt 183) 8 state183_85.toFinset :=
  node_ok cuts183 [⟨state183_3,exclude183_3⟩,⟨state183_5,exclude183_5⟩,⟨state183_7,exclude183_7⟩,⟨state183_11,exclude183_11⟩,⟨state183_15,exclude183_15⟩,⟨state183_19,exclude183_19⟩,⟨state183_21,exclude183_21⟩,⟨state183_23,exclude183_23⟩,⟨state183_45,exclude183_45⟩,⟨state183_49,exclude183_49⟩,⟨state183_59,exclude183_59⟩,⟨state183_63,exclude183_63⟩,⟨state183_69,exclude183_69⟩,⟨state183_73,exclude183_73⟩,⟨state183_81,exclude183_81⟩,⟨state183_84,exclude183_84⟩] 0x8003cb03008404210140010810128a08810180038b03028a0890304001081010840421018003490100440490008003081012420090008002c90102420090108002881010440411014001034140440411018002421012c28021018002034142c28024144001021010440411018001c84040908084004000481012120084008001884042120084044000481010908081014001024042120024004000421010908024004005824040908024044001021012120021018001415050908015014000411010d0c011018001015050d0c011054000411010908011018000c83030484083014000c810128a80810180008830328a8081034000c81010484081014001022020484022004000c21010888022004001422020888022024001021010484021018000412020888012004000c11010484012008000012020484012024000c11010888011014000486820484012104000c242005850161040008868205850121440004242004840121040000810104440810040000840420600810040000810120600810140000840404440840440000210104440210040000220208480210040000210108480210140000220204440220240000110108480110040000120204440110040000110104440110140000120208480120240001000004440111040000242005450151040001000005450111440000242004440111040001000004440111040000121020e08121040001000020e088182400001210044401110 (by decide +kernel)

theorem lower183 : Claim 183 9 :=
  fromSearch 1348 (by decide +kernel) exclude183_85

open PEqualNP.CircuitLowerBounds

def graph : Sig := goalAt 255
theorem graph_proper : proper graph := by unfold proper; decide +kernel

def edgeList : List Nat := [0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7]
def target (x : Fin 8 → Bool) : Bool :=
  decide (∃ i < edgeList.length / 2,
    (List.ofFn x).getD (edgeList.getD (2*i) 0) false = true ∧
    (List.ofFn x).getD (edgeList.getD (2*i+1) 0) false = true)

-- The conjunctions cover all of the posted edges.
def smallCircuit : Circuit := ⟨[⟨.or,[0,1]⟩, ⟨.or,[0,3]⟩, ⟨.or,[4,5]⟩, ⟨.or,[4,9]⟩, ⟨.or,[5,7]⟩, ⟨.or,[6,7]⟩, ⟨.or,[6,10]⟩, ⟨.and,[8,14]⟩, ⟨.and,[2,12]⟩, ⟨.and,[11,13]⟩, ⟨.or,[15,16]⟩, ⟨.or,[18,17]⟩],19⟩

theorem witnessMonotone : ∀ g ∈ smallCircuit.gates,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [smallCircuit,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ⟨Or.inl rfl,by decide⟩ | exact ⟨Or.inr rfl,by decide⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem witnessCorrect : ∀ x : Fin 8 → Bool, smallCircuit.eval (List.ofFn x) = target x := by
  decide +kernel

theorem witnessSize : smallCircuit.gates.length = 12 := rfl

theorem noNotReuse {gates : List Gate} (fit : ∀ g ∈ gates,
    (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (h : ∀ g ∈ gates, g.op ≠ GateOp.not) :
    ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  obtain ⟨ops,arity⟩ := fit g hg
  refine ⟨?_,arity⟩
  rcases ops with a | b | c
  · exact Or.inl a
  · exact Or.inr b
  · exact (h g hg c).elim


def eightInputs : List Sig := roots 255
def sampleEight (r : Row) (i : Fin 8) : Bool := bit r (eightInputs.getD i.val zero)
theorem eightList : List.ofFn (fun i : Fin 8 => eightInputs.getD i.val zero) = eightInputs := rfl
theorem eightSampled (r : Row) : List.ofFn (sampleEight r) = eightInputs.map (bit r) := by
  rw [←eightList,List.map_ofFn]
  rfl

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem eightTable : ∀ r : Row, bit r graph = target (sampleEight r) := by decide +kernel

theorem eightEval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates eightInputs).getD i zero) =
      (C.wires (List.ofFn (sampleEight r))).getD i false := by
  rw [←b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),eightSampled]
  rfl

def lowRow (i : Fin 8) : Row := Fin.ofNat 256 (1 <<< ([4, 4, 5, 6, 0, 0, 0, 0] : List Nat).getD i.val 0)
def highRow (i : Fin 8) : Row := Fin.ofNat 256 ((1 <<< i.val) ||| (1 <<< ([4, 4, 5, 6, 0, 0, 0, 0] : List Nat).getD i.val 0))

set_option maxHeartbeats 1000000 in
theorem allEightRequired :
    (∀ i : Fin 8, bit (lowRow i) graph ≠ bit (highRow i) graph) ∧
    (∀ i j : Fin 8, i ≠ j →
      bit (lowRow i) (eightInputs.getD j.val zero) =
      bit (highRow i) (eightInputs.getD j.val zero)) := by decide +kernel

theorem physicalSigned (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x : Fin 8 → Bool, C.eval (List.ofFn x)=target x) :
    ∃ k, k ≤ C.gates.countP (fun g => !isNot g) ∧ Live true graph k eightInputs.toFinset := by
  have goalEq : (execute C.gates eightInputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (eightEval C legal C.output r).trans ((computes (sampleEight r)).trans (eightTable r).symm)
  have out := get_rep (u:=true) (execute C.gates eightInputs) C.output
  rw [goalEq] at out
  unfold Repr at out
  have pg : bit 0 graph = false := by decide +kernel
  rw [nrm_id pg] at out
  obtain ⟨k,S,hk,run,sub⟩ := extract (u:=true) C.gates eightInputs legal (by simp) graph_proper
    (out.resolve_right (fun h => h graph_proper))
  have ns : eightInputs.all plainWord = true := by decide +kernel
  rw [nrm_map ns] at sub
  have idx (a : Sig) (ha : a ∈ eightInputs) : ∃ i : Fin 8, eightInputs.getD i.val zero = a := by
    rw [←eightList] at ha
    exact List.mem_ofFn.mp ha
  have eq : S = eightInputs.toFinset := by
    ext a
    constructor
    · exact fun h => List.mem_toFinset.mpr (sub a h)
    · intro ha
      obtain ⟨i,rfl⟩ := idx a (List.mem_toFinset.mp ha)
      apply raw_required run eightInputs (eightInputs.getD i.val zero) sub (lowRow i) (highRow i)
        (allEightRequired.1 i)
      intro v hv hn
      obtain ⟨j,rfl⟩ := idx v hv
      apply allEightRequired.2 i j
      rintro rfl
      exact hn rfl
  exact ⟨k,hk,eq ▸ run⟩

theorem replaceShort
    (lower : Impossible true graph 10 eightInputs.toFinset) (gates : List Gate) (o : Nat)
    (fit : ∀ g ∈ gates, (g.op=GateOp.and ∨ g.op=GateOp.or ∨ g.op=GateOp.not) ∧ g.inputs.length≤2)
    (correct : ∀ x : Fin 8 → Bool, (Circuit.mk gates o).eval (List.ofFn x)=target x) :
    ∃ (gs : List Gate) (out : Nat), (∀ g ∈ gs, (g.op=GateOp.and ∨ g.op=GateOp.or) ∧ g.inputs.length≤2) ∧
       gs.length≤gates.length ∧ ∀ x : Fin 8 → Bool, (Circuit.mk gs out).eval (List.ofFn x)=target x := by
  classical
  by_cases big : 12 ≤ gates.length
  · exact ⟨smallCircuit.gates,smallCircuit.output,witnessMonotone,(by simpa only [witnessSize] using big),witnessCorrect⟩
  by_cases mono : ∀ g ∈ gates, g.op ≠ GateOp.not
  · exact ⟨gates,o,noNotReuse fit mono,Nat.le_refl _,correct⟩
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
  exact (lower k (by omega) run).elim



-- Every omitted vertex is essential before setting it to zero.
theorem lowerGraph : Impossible true graph 10 eightInputs.toFinset :=
  (ruleFor 255 lower183 none (by decide +kernel)).property 10 eightInputs
    (by decide +kernel) (by decide +kernel)


end PEqualNP.Outside.L_meta_31673

open PEqualNP.Outside.L_meta_31673 in
theorem PEqualNP.Outside.L_meta_31673 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o fit _ correct
  exact replaceShort lowerGraph gates o fit correct

import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29152

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
  (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 2 &&& x 5) ||| (x 0 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 2 &&& x 7) ||| (x 3 &&& x 7) ||| (x 6 &&& x 7)

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



-- Each dictionary stores the original 18-bit case witnesses, in order of frequency.
-- The certificate checker still verifies each expanded witness.
def unpackCases (table bits : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | count+1, word =>
    let index := word % (2^bits)
    let witness := (table >>> (18*index)) % 262144
    witness + ((unpackCases table bits count (word >>> bits)) <<< 18)

def unpackShort (table bits short : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | count+1, word =>
    let width := if word % 2 = 0 then short else bits
    let index := (word >>> 1) % (2^width)
    let witness := (table >>> (18*index)) % 262144
    witness + ((unpackShort table bits short count (word >>> (1+width))) <<< 18)

def certify (m k : Nat) (bank : List Sig) (cuts : Cuts (goalAt m))
    (links : Links (goalAt m) (k-1)) (data : Nat)
    (ok : checkNode (goalAt m) k bank cuts links data = true := by decide +kernel) :
    {v : List Sig // Impossible true (goalAt m) k v.toFinset} :=
  ⟨bank,node_ok cuts links data ok⟩


def i0 : Sig := input 0

def i1 : Sig := input 1

def i2 : Sig := input 2

def i3 : Sig := input 3

def i4 : Sig := input 4

def i5 : Sig := input 5

def i6 : Sig := input 6

def i7 : Sig := input 7

def cs193 : Cuts (goalAt 193) := []

def dict193 : Nat := 0xc000204004100302008101301004140206004101

def d193 := unpackCases dict193 4

def u193 := unpackShort dict193 4

def s0 := certify 193 3 (roots 193) cs193 [] (d193 36 0x308458353400427317414322016526020511)

theorem lower193 : Claim 193 4 := fromSearch 6 (by decide +kernel) s0.property

theorem lower225 : Claim 225 5 := fromLift 5 32 5 lower193 (by decide +kernel)

def cs200 : Cuts (goalAt 200) := []

def dict200 : Nat := 0xc000220004800302008808301004840222004808

def d200 := unpackCases dict200 4

def u200 := unpackShort dict200 4

def s1 := certify 200 3 (roots 200) cs200 [] (d200 36 0x308458353400427317414322016526020511)

theorem lower200 : Claim 200 4 := fromSearch 855662592 (by decide +kernel) s1.property

theorem lower201 : Claim 201 5 := fromLift 5 1 24582 lower200 (by decide +kernel)

def cs105 : Cuts (goalAt 105) := []

def dict105 : Nat := 0x48280a4042109105002920084a04800104004808084002120104042101

def d105 := unpackCases dict105 4

def u105 := unpackShort dict105 4

def s2 := certify 105 3 (roots 105) cs105 [] (d105 24 0x1c06641b0a0551433092872)

theorem lower105 : Claim 105 4 := fromSearch 24581 (by decide +kernel) s2.property

def cs169 : Cuts (goalAt 169) := []

def dict169 : Nat := 0x88280a4042109206002920084a08800204008808084002120204042101

def d169 := unpackCases dict169 4

def u169 := unpackShort dict169 4

def s3 := certify 169 3 (roots 169) cs169 [] (d169 24 0x1c06641b0a0551433092872)

theorem lower169 : Claim 169 4 := fromSearch 28677 (by decide +kernel) s3.property

def c233_0 := ruleFor 233 lower225 none (by decide +kernel)

def c233_1 := ruleFor 233 lower200 none (by decide +kernel)

def c233_2 := ruleFor 233 lower201 none (by decide +kernel)

def c233_3 := ruleFor 233 lower225 (some (1,i5,i6)) (by decide +kernel)

def c233_4 := ruleFor 233 lower225 (some (1,i5,i7)) (by decide +kernel)

def c233_5 := ruleFor 233 lower105 none (by decide +kernel)

def c233_6 := ruleFor 233 lower169 none (by decide +kernel)

def cs233 : Cuts (goalAt 233) := [c233_0,c233_1,c233_2,c233_3,c233_4,c233_5,c233_6]

def dict233 : Nat := 0x1000680008a8001a00089002200449001200468404001100034001441200850081200860068281a18200012a0a2000030080c0a03018041000a424292820400c000302004820220802901084242920084a08180220008828400004800120208808301004828084008880105010001400088101104044840084802101

def d233 := unpackCases dict233 6

def u233 := unpackShort dict233 6

def w8 : Sig := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000

def s4 := certify 233 4 ([w8,i7,i6,i0,i3]) cs233 [] (u233 1 34 0xc589522bd7a10ab4564a53d55a75467c4c98361c32e54389)

def w9 : Sig := 0xffffffffffffffffffffffff00000000

def s5 := certify 233 4 ([w9,i7,i6,i0,i3]) cs233 [] (d233 37 0x1860a21144c101513041aa905b6c431a6991005950092404800ca010)

def w10 : Sig := 0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000

def s6 := certify 233 5 ([w10,i6,i0,i3,i7]) cs233 [s4,s5] (u233 3 111 0x194470451992266120a916305189542b04891764568203b456044209b994ade12c1923364891ca9c729d08b088af55cea654881293c2260418952972b0e20c17825e0ac553470089311e2a1800)

def w11 : Sig := 0xffffffffffffffff0000000000000000ffffffff00000000

def s7 := certify 233 4 ([w11,i6,i7,i0,i3]) cs233 [] (u233 2 37 0x2f5e861d3a6f2529d2a33d3d7b8db56a5f05aac1326078128415)

def w12 : Sig := 0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000

def s8 := certify 233 5 ([w12,i7,i0,i3,i6]) cs233 [s4,s7] (u233 2 111 0xff642ce1bf66fd0ed276134459a54606c89dd0e9b86f11c862f7e457a12285fc8ee2d12c3b96ac4193d363dee1f8da376d28e548d729e24352429688d4b3d0a407931a8984068f1e2c589)

def w13 : Sig := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000000000

def s9 := certify 233 4 ([w13,i6,i7,i0,i5]) cs233 [] (d233 40 0xd115d1cce60e249007c91c51c0ebce3912ce080b801c11c11112d10ce08e)

def w14 : Sig := 0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000

def s10 := certify 233 5 ([w14,i6,i7,i0,i3,i5]) cs233 [s9,s4] (u233 2 53 0x2efc06704017242d0ac42e4611908c590f932607a529d22e9521e3d21e3d092ecebe)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s11 := certify 233 6 (roots 233) cs233 [s6,s8,s10] (u233 3 160 0x2b9766bb619b5d65d997af0cd51c02a2a2a3c9435001534029a9aa6c52b4c007cca233f04519f3244c9f8483e6c89d3ec874f9b4367d88b53b45b412c29dcb574081904df0ca56f909630c919c627b86f9ee37361b23741c4eb089d01055771f3e447d1ca93f8e539f422)

theorem lower233 : Claim 233 7 := fromSearch 24581 (by decide +kernel) s11.property

theorem lower249 : Claim 249 8 := fromLift 8 16 24580 lower233 (by decide +kernel)

def cs196 : Cuts (goalAt 196) := []

def dict196 : Nat := 0xc000210004400302008404301004440212004404

def d196 := unpackCases dict196 4

def u196 := unpackShort dict196 4

def s12 := certify 196 3 (roots 196) cs196 [] (d196 36 0x308458353400427317414322016526020511)

theorem lower196 : Claim 196 4 := fromSearch 570426880 (by decide +kernel) s12.property

theorem lower228 : Claim 228 5 := fromLift 5 32 572523776 lower196 (by decide +kernel)

theorem lower204 : Claim 204 5 := fromLift 5 4 570451456 lower200 (by decide +kernel)

def cs108 : Cuts (goalAt 108) := []

def dict108 : Nat := 0x48280b010240c111002c20090a04800110004808090002420110102404

def d108 := unpackCases dict108 4

def u108 := unpackShort dict108 4

def s13 := certify 108 3 (roots 108) cs108 [] (d108 24 0x1c06641b0a0551433092872)

theorem lower108 : Claim 108 4 := fromSearch 35677440 (by decide +kernel) s13.property

def cs172 : Cuts (goalAt 172) := []

def dict172 : Nat := 0x88280b010240c212002c20090a08800210008808090002420210102404

def d172 := unpackCases dict172 4

def u172 := unpackShort dict172 4

def s14 := certify 172 3 (roots 172) cs172 [] (d172 24 0x1c06641b0a0551433092872)

theorem lower172 : Claim 172 4 := fromSearch 538998016 (by decide +kernel) s14.property

def c236_0 := ruleFor 236 lower228 none (by decide +kernel)

def c236_1 := ruleFor 236 lower200 none (by decide +kernel)

def c236_2 := ruleFor 236 lower204 none (by decide +kernel)

def c236_3 := ruleFor 236 lower228 (some (1,i5,i6)) (by decide +kernel)

def c236_4 := ruleFor 236 lower228 (some (1,i5,i7)) (by decide +kernel)

def c236_5 := ruleFor 236 lower108 none (by decide +kernel)

def c236_6 := ruleFor 236 lower172 none (by decide +kernel)

def cs236 : Cuts (goalAt 236) := [c236_0,c236_1,c236_2,c236_3,c236_4,c236_5,c236_6]

def dict236 : Nat := 0x1000680008a8001a0008c00220104c001201068404001100034001444200910084200920068281a18200012a0a2000030080c0a03018044000b0302c2821000c000302004820220802c04090302c20090a08480220008828400004800120208808301004828090008880111010001400088404110104840090802404

def d236 := unpackCases dict236 6

def u236 := unpackShort dict236 6

def s15 := certify 236 4 ([w8,i7,i6,i2,i3]) cs236 [] (u236 1 34 0xc589522bd7a10ab4564a53d55a75467c4c98361c32e54389)

def s16 := certify 236 4 ([w9,i7,i6,i2,i3]) cs236 [] (d236 37 0x1860a21144c101513041aa905b6c431a6991005950092404800ca010)

def s17 := certify 236 5 ([w10,i6,i2,i3,i7]) cs236 [s15,s16] (u236 3 111 0x194470451992266120a916305189542b04891764568203b456044209b994ade12c1923364891ca9c729d08b088af55cea654881293c2260418952972b0e20c17825e0ac553470089311e2a1800)

def s18 := certify 236 4 ([w11,i6,i7,i2,i3]) cs236 [] (u236 2 37 0x2f5e861d3a6f2529d2a33d3d7b8db56a5f05aac1326078128415)

def s19 := certify 236 5 ([w12,i7,i2,i3,i6]) cs236 [s15,s18] (u236 2 111 0xff642ce1bf66fd0ed276134459a54606c89dd0e9b86f11c862f7e457a12285fc8ee2d12c3b96ac4193d363dee1f8da376d28e548d729e24352429688d4b3d0a407931a8984068f1e2c589)

def s20 := certify 236 4 ([w13,i6,i7,i2,i5]) cs236 [] (d236 40 0xd115d1cce60e249007c91c51c0ebce3912ce080b801c11c11112d10ce08e)

def s21 := certify 236 5 ([w14,i6,i7,i2,i3,i5]) cs236 [s20,s15] (u236 2 53 0x2efc06704017242d0ac42e4611908c590f932607a529d22e9521e3d21e3d092ecebe)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s22 := certify 236 6 (roots 236) cs236 [s17,s19,s21] (u236 3 160 0x2b9766bb619b5d65d997af0cd51c02a2a2a3c9435001534029a9aa6c52b4c007cca233f04519f3244c9f8483e6c89d3ec874f9b4367d88b53b45b412c29dcb574081904df0ca56f909630c919c627b86f9ee37361b23741c4eb089d01055771f3e447d1ca93f8e539f422)

theorem lower236 : Claim 236 7 := fromSearch 572548352 (by decide +kernel) s22.property

theorem lower209 : Claim 209 5 := fromLift 5 16 4 lower193 (by decide +kernel)

theorem lower197 : Claim 197 5 := fromLift 5 1 1542 lower196 (by decide +kernel)

def cs85 : Cuts (goalAt 85) := []

def dict85 : Nat := 0x4414054041105105001510044504400104004404044001110104041101

def d85 := unpackCases dict85 4

def u85 := unpackShort dict85 4

def s23 := certify 85 3 (roots 85) cs85 [] (d85 24 0x1c06641b0a0551433092872)

theorem lower85 : Claim 85 4 := fromSearch 1540 (by decide +kernel) s23.property

def cs149 : Cuts (goalAt 149) := []

def dict149 : Nat := 0x8414054041105206001510044508400204008404044001110204041101

def d149 := unpackCases dict149 4

def u149 := unpackShort dict149 4

def s24 := certify 149 3 (roots 149) cs149 [] (d149 24 0x1c06641b0a0551433092872)

theorem lower149 : Claim 149 4 := fromSearch 1796 (by decide +kernel) s24.property

def c213_0 := ruleFor 213 lower209 none (by decide +kernel)

def c213_1 := ruleFor 213 lower196 none (by decide +kernel)

def c213_2 := ruleFor 213 lower197 none (by decide +kernel)

def c213_3 := ruleFor 213 lower209 (some (1,i4,i6)) (by decide +kernel)

def c213_4 := ruleFor 213 lower209 (some (1,i4,i7)) (by decide +kernel)

def c213_5 := ruleFor 213 lower85 none (by decide +kernel)

def c213_6 := ruleFor 213 lower149 none (by decide +kernel)

def cs213 : Cuts (goalAt 213) := [c213_0,c213_1,c213_2,c213_3,c213_4,c213_5,c213_6]

def dict213 : Nat := 0x1000680008940015000850021004450011004544040011000340014411004500811004600541415142000125052000030040c09030140410005414151420400c000302004410210401501044141510044508180210008414400004400110108404301004414044008480105010001400088101104044440044401101

def d213 := unpackCases dict213 6

def u213 := unpackShort dict213 6

def w15 : Sig := 0xffffffffffffffffffffffffffffffffffffffffffffffffffff0000ffff0000

def s25 := certify 213 4 ([w15,i7,i6,i0,i2]) cs213 [] (u213 1 34 0xc589522bd7a10ab4564a53d55a75467c4c98361c32e54389)

def w16 : Sig := 0xffffffffffffffffffff0000ffff0000

def s26 := certify 213 4 ([w16,i7,i6,i0,i2]) cs213 [] (d213 37 0x1860a21144c101513041aa905b6c431a6991005950092404800ca010)

def w17 : Sig := 0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000

def s27 := certify 213 5 ([w17,i6,i0,i2,i7]) cs213 [s25,s26] (u213 3 111 0x194470451992266120a916305189542b04891764568203b456044209b994ade12c1923364891ca9c729d08b088af55cea654881293c2260418952972b0e20c17825e0ac553470089311e2a1800)

def w18 : Sig := 0xffffffffffffffff0000000000000000ffff0000ffff0000

def s28 := certify 213 4 ([w18,i6,i7,i0,i2]) cs213 [] (u213 2 37 0x2f5e861d3a6f2529d2a33d3d7b8db56a5f05aac1326078128415)

def w19 : Sig := 0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000

def s29 := certify 213 5 ([w19,i7,i0,i2,i6]) cs213 [s25,s28] (u213 2 111 0xff642ce1bf66fd0ed276134459a54606c89dd0e9b86f11c862f7e457a12285fc8ee2d12c3b96ac4193d363dee1f8da376d28e548d729e24352429688d4b3d0a407931a8984068f1e2c589)

def w20 : Sig := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0000000000000000

def s30 := certify 213 4 ([w20,i6,i7,i0,i4]) cs213 [] (d213 40 0xd115d1cce60e249007c91c51c0ebce3912ce080b801c11c11112d10ce08e)

def s31 := certify 213 5 ([w14,i6,i7,i0,i2,i4]) cs213 [s30,s25] (u213 2 53 0x2efc06704017242d0ac42e4611908c590f932607a529d22e9521e3d21e3d092ecebe)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s32 := certify 213 6 (roots 213) cs213 [s27,s29,s31] (u213 3 160 0x2b9766bb619b5d65d997af0cd51c02a2a2a3c9435001534029a9aa6c52b4c007cca233f04519f3244c9f8483e6c89d3ec874f9b4367d88b53b45b412c29dcb574081904df0ca56f909630c919c627b86f9ee37361b23741c4eb089d01055771f3e447d1ca93f8e539f422)

theorem lower213 : Claim 213 7 := fromSearch 1540 (by decide +kernel) s32.property

theorem lower245 : Claim 245 8 := fromLift 8 32 1284 lower213 (by decide +kernel)

theorem lower237 : Claim 237 8 := fromLift 8 1 25861 lower236 (by decide +kernel)

def cs89 : Cuts (goalAt 89) := []

def dict89 : Nat := 0x4818064041109105001910044604800104004808044001110104041101

def d89 := unpackCases dict89 4

def u89 := unpackShort dict89 4

def s33 := certify 89 3 (roots 89) cs89 [] (d89 24 0x1c06641b0a0551433092872)

theorem lower89 : Claim 89 4 := fromSearch 24580 (by decide +kernel) s33.property

def cs153 : Cuts (goalAt 153) := []

def dict153 : Nat := 0x8818064041109206001910044608800204008808044001110204041101

def d153 := unpackCases dict153 4

def u153 := unpackShort dict153 4

def s34 := certify 153 3 (roots 153) cs153 [] (d153 24 0x1c06641b0a0551433092872)

theorem lower153 : Claim 153 4 := fromSearch 28676 (by decide +kernel) s34.property

def c217_0 := ruleFor 217 lower209 none (by decide +kernel)

def c217_1 := ruleFor 217 lower200 none (by decide +kernel)

def c217_2 := ruleFor 217 lower201 none (by decide +kernel)

def c217_3 := ruleFor 217 lower209 (some (1,i4,i6)) (by decide +kernel)

def c217_4 := ruleFor 217 lower209 (some (1,i4,i7)) (by decide +kernel)

def c217_5 := ruleFor 217 lower89 none (by decide +kernel)

def c217_6 := ruleFor 217 lower153 none (by decide +kernel)

def cs217 : Cuts (goalAt 217) := [c217_0,c217_1,c217_2,c217_3,c217_4,c217_5,c217_6]

def dict217 : Nat := 0x1000680008980016000890022004490012004584040011000340014411004500811004600581816142000126062000030040c09030140410006424191820400c000302004810220401901044241910044608180220008818400004800120208808301004818044008880105010001400088101104044840044401101

def d217 := unpackCases dict217 6

def u217 := unpackShort dict217 6

def s35 := certify 217 4 ([w15,i7,i6,i0,i3]) cs217 [] (u217 1 34 0xc589522bd7a10ab4564a53d55a75467c4c98361c32e54389)

def s36 := certify 217 4 ([w16,i7,i6,i0,i3]) cs217 [] (d217 37 0x1860a21144c101513041aa905b6c431a6991005950092404800ca010)

def s37 := certify 217 5 ([w17,i6,i0,i3,i7]) cs217 [s35,s36] (u217 3 111 0x194470451992266120a916305189542b04891764568203b456044209b994ade12c1923364891ca9c729d08b088af55cea654881293c2260418952972b0e20c17825e0ac553470089311e2a1800)

def s38 := certify 217 4 ([w18,i6,i7,i0,i3]) cs217 [] (u217 2 37 0x2f5e861d3a6f2529d2a33d3d7b8db56a5f05aac1326078128415)

def s39 := certify 217 5 ([w19,i7,i0,i3,i6]) cs217 [s35,s38] (u217 2 111 0xff642ce1bf66fd0ed276134459a54606c89dd0e9b86f11c862f7e457a12285fc8ee2d12c3b96ac4193d363dee1f8da376d28e548d729e24352429688d4b3d0a407931a8984068f1e2c589)

def s40 := certify 217 4 ([w13,i6,i7,i0,i4]) cs217 [] (d217 40 0xd115d1cce60e249007c91c51c0ebce3912ce080b801c11c11112d10ce08e)

def s41 := certify 217 5 ([w14,i6,i7,i0,i3,i4]) cs217 [s40,s35] (u217 2 53 0x2efc06704017242d0ac42e4611908c590f932607a529d22e9521e3d21e3d092ecebe)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s42 := certify 217 6 (roots 217) cs217 [s37,s39,s41] (u217 3 160 0x2b9766bb619b5d65d997af0cd51c02a2a2a3c9435001534029a9aa6c52b4c007cca233f04519f3244c9f8483e6c89d3ec874f9b4367d88b53b45b412c29dcb574081904df0ca56f909630c919c627b86f9ee37361b23741c4eb089d01055771f3e447d1ca93f8e539f422)

theorem lower217 : Claim 217 7 := fromSearch 24580 (by decide +kernel) s42.property

theorem lower221 : Claim 221 8 := fromLift 8 4 26116 lower217 (by decide +kernel)

theorem lower121 : Claim 121 5 := fromLift 5 16 24580 lower105 (by decide +kernel)

theorem lower117 : Claim 117 5 := fromLift 5 32 1284 lower85 (by decide +kernel)

theorem lower109 : Claim 109 5 := fromLift 5 1 25861 lower108 (by decide +kernel)

def cs53 : Cuts (goalAt 53) := []

def dict53 : Nat := 0x2414054041105084801510044502400084002404044001110084041101

def d53 := unpackCases dict53 4

def u53 := unpackShort dict53 4

def s43 := certify 53 3 (roots 53) cs53 [] (d53 24 0x1c06641b0a0551433092872)

theorem lower53 : Claim 53 4 := fromSearch 1284 (by decide +kernel) s43.property

theorem lower93 : Claim 93 5 := fromLift 5 4 26116 lower89 (by decide +kernel)

def c125_0 := ruleFor 125 lower108 none (by decide +kernel)

def c125_1 := ruleFor 125 lower121 none (by decide +kernel)

def c125_2 := ruleFor 125 lower117 none (by decide +kernel)

def c125_3 := ruleFor 125 lower109 none (by decide +kernel)

def c125_4 := ruleFor 125 lower53 none (by decide +kernel)

def c125_5 := ruleFor 125 lower93 none (by decide +kernel)

def cs125 : Cuts (goalAt 125) := [c125_0,c125_1,c125_2,c125_3,c125_4,c125_5]

def dict125 : Nat := 0x48281105024140a40421090640411090540411050b08024280644011180544011141a0a054140d05048000a42468600642458501100024000541434300b0a04100105002100044010003064610001054510005400104808400090000111002120110102404121002420044404101084041101

def d125 := unpackCases dict125 6

def u125 := unpackShort dict125 6

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s44 := certify 125 6 (roots 125) cs125 [] (u125 3 180 0x472243a91cde54228a00895229bc68010c008e9433b84800c9b829504cd1942e8feaf93d27ef6e9513bab60e41db9b2141d0dd09b7e27c90984da9435c8c2264ce2b831066c6a8401788a5f4d0afa35108cb795ad4569cdc4ca708a922258d804539564e0c0948912ecd48e79547369990b341f9654fc9866)

theorem lower125 : Claim 125 7 := fromSearch 25860 (by decide +kernel) s44.property

theorem lower173 : Claim 173 5 := fromLift 5 1 29957 lower172 (by decide +kernel)

theorem lower185 : Claim 185 5 := fromLift 5 16 28676 lower169 (by decide +kernel)

theorem lower181 : Claim 181 5 := fromLift 5 32 1284 lower149 (by decide +kernel)

theorem lower157 : Claim 157 5 := fromLift 5 4 30468 lower153 (by decide +kernel)

def c189_0 := ruleFor 189 lower172 none (by decide +kernel)

def c189_1 := ruleFor 189 lower185 none (by decide +kernel)

def c189_2 := ruleFor 189 lower181 none (by decide +kernel)

def c189_3 := ruleFor 189 lower173 none (by decide +kernel)

def c189_4 := ruleFor 189 lower53 none (by decide +kernel)

def c189_5 := ruleFor 189 lower157 none (by decide +kernel)

def cs189 : Cuts (goalAt 189) := [c189_0,c189_1,c189_2,c189_3,c189_4,c189_5]

def dict189 : Nat := 0x88282105024140a40421090640411090540411050b08024280644011180544011142a0a094140d05088000a424a8a00642498902100024000541434300b0a08100206002100044010003064610001054510005400108808400090000212002120210102404222002420044408101084041101

def d189 := unpackCases dict189 6

def u189 := unpackShort dict189 6

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s45 := certify 189 6 (roots 189) cs189 [] (u189 3 180 0x472243a91cde54228a00895229bc68010c008e9433b84800c9b829504cd1942e8feaf93d27ef6e9513bab60e41db9b2141d0dd09b7e27c90984da9435c8c2264ce2b831066c6a8401788a5f4d0afa35108cb795ad4569cdc4ca708a922258d804539564e0c0948912ecd48e79547369990b341f9654fc9866)

theorem lower189 : Claim 189 7 := fromSearch 29956 (by decide +kernel) s45.property

theorem lower205 : Claim 205 6 := fromLift 6 1 26118 lower204 (by decide +kernel)

def c253_0 := ruleFor 253 lower249 none (by decide +kernel)

def c253_1 := ruleFor 253 lower236 none (by decide +kernel)

def c253_2 := ruleFor 253 lower245 none (by decide +kernel)

def c253_3 := ruleFor 253 lower237 none (by decide +kernel)

def c253_4 := ruleFor 253 lower221 none (by decide +kernel)

def c253_5 := ruleFor 253 lower125 (some (1,i4,i6)) (by decide +kernel)

def c253_6 := ruleFor 253 lower173 none (by decide +kernel)

def c253_7 := ruleFor 253 lower237 (some (2,i6,i7)) (by decide +kernel)

def c253_8 := ruleFor 253 lower109 none (by decide +kernel)

def c253_9 := ruleFor 253 lower237 (some (3,i6,i7)) (by decide +kernel)

def c253_10 := ruleFor 253 lower236 (some (1,i6,i7)) (by decide +kernel)

def c253_11 := ruleFor 253 lower233 (some (1,i6,i7)) (by decide +kernel)

def c253_12 := ruleFor 253 lower53 none (by decide +kernel)

def c253_13 := ruleFor 253 lower189 (some (1,i4,i7)) (by decide +kernel)

def c253_14 := ruleFor 253 lower245 (some (1,i4,i6)) (by decide +kernel)

def c253_15 := ruleFor 253 lower237 (some (1,i6,i7)) (by decide +kernel)

def c253_16 := ruleFor 253 lower189 (some (2,i4,i7)) (by decide +kernel)

def c253_17 := ruleFor 253 lower236 (some (2,i6,i7)) (by decide +kernel)

def c253_18 := ruleFor 253 lower233 (some (2,i6,i7)) (by decide +kernel)

def c253_19 := ruleFor 253 lower221 (some (2,i4,i6)) (by decide +kernel)

def c253_20 := ruleFor 253 lower189 none (by decide +kernel)

def c253_21 := ruleFor 253 lower249 (some (1,i4,i6)) (by decide +kernel)

def c253_22 := ruleFor 253 lower221 (some (1,i4,i6)) (by decide +kernel)

def c253_23 := ruleFor 253 lower236 (some (1,i5,i7)) (by decide +kernel)

def c253_24 := ruleFor 253 lower189 (some (1,i5,i7)) (by decide +kernel)

def c253_25 := ruleFor 253 lower237 (some (1,i5,i7)) (by decide +kernel)

def c253_26 := ruleFor 253 lower217 (some (1,i4,i6)) (by decide +kernel)

def c253_27 := ruleFor 253 lower213 (some (1,i4,i6)) (by decide +kernel)

def c253_28 := ruleFor 253 lower221 (some (2,i4,i7)) (by decide +kernel)

def c253_29 := ruleFor 253 lower249 (some (1,i4,i7)) (by decide +kernel)

def c253_30 := ruleFor 253 lower245 (some (1,i4,i7)) (by decide +kernel)

def c253_31 := ruleFor 253 lower221 (some (1,i4,i7)) (by decide +kernel)

def c253_32 := ruleFor 253 lower125 none (by decide +kernel)

def c253_33 := ruleFor 253 lower236 (some (1,i5,i6)) (by decide +kernel)

def c253_34 := ruleFor 253 lower125 (some (1,i5,i6)) (by decide +kernel)

def c253_35 := ruleFor 253 lower237 (some (1,i5,i6)) (by decide +kernel)

def c253_36 := ruleFor 253 lower217 (some (1,i4,i7)) (by decide +kernel)

def c253_37 := ruleFor 253 lower213 (some (1,i4,i7)) (by decide +kernel)

def c253_38 := ruleFor 253 lower125 (some (2,i4,i6)) (by decide +kernel)

def c253_39 := ruleFor 253 lower236 (some (3,i6,i7)) (by decide +kernel)

def c253_40 := ruleFor 253 lower233 (some (3,i6,i7)) (by decide +kernel)

def c253_41 := ruleFor 253 lower157 none (by decide +kernel)

def c253_42 := ruleFor 253 lower221 (some (2,i6,i7)) (by decide +kernel)

def c253_43 := ruleFor 253 lower93 none (by decide +kernel)

def c253_44 := ruleFor 253 lower221 (some (3,i6,i7)) (by decide +kernel)

def c253_45 := ruleFor 253 lower200 none (by decide +kernel)

def c253_46 := ruleFor 253 lower217 (some (1,i6,i7)) (by decide +kernel)

def c253_47 := ruleFor 253 lower213 (some (1,i6,i7)) (by decide +kernel)

def c253_48 := ruleFor 253 lower249 (some (1,i5,i6)) (by decide +kernel)

def c253_49 := ruleFor 253 lower245 (some (1,i5,i6)) (by decide +kernel)

def c253_50 := ruleFor 253 lower221 (some (1,i6,i7)) (by decide +kernel)

def c253_51 := ruleFor 253 lower189 (some (2,i5,i7)) (by decide +kernel)

def c253_52 := ruleFor 253 lower217 (some (2,i6,i7)) (by decide +kernel)

def c253_53 := ruleFor 253 lower213 (some (2,i6,i7)) (by decide +kernel)

def c253_54 := ruleFor 253 lower205 none (by decide +kernel)

def c253_55 := ruleFor 253 lower249 (some (1,i5,i7)) (by decide +kernel)

def c253_56 := ruleFor 253 lower245 (some (1,i5,i7)) (by decide +kernel)

def c253_57 := ruleFor 253 lower125 (some (2,i5,i6)) (by decide +kernel)

def c253_58 := ruleFor 253 lower217 (some (3,i6,i7)) (by decide +kernel)

def c253_59 := ruleFor 253 lower213 (some (3,i6,i7)) (by decide +kernel)

def c253_60 := ruleFor 253 lower249 (some (1,i6,i7)) (by decide +kernel)

def c253_61 := ruleFor 253 lower245 (some (1,i6,i7)) (by decide +kernel)

def c253_62 := ruleFor 253 lower189 (some (3,i3,i7)) (by decide +kernel)

def c253_63 := ruleFor 253 lower125 (some (3,i3,i6)) (by decide +kernel)

def cs253 : Cuts (goalAt 253) := [c253_0,c253_1,c253_2,c253_3,c253_4,c253_5,c253_6,c253_7,c253_8,c253_9,c253_10,c253_11,c253_12,c253_13,c253_14,c253_15,c253_16,c253_17,c253_18,c253_19,c253_20,c253_21,c253_22,c253_23,c253_24,c253_25,c253_26,c253_27,c253_28,c253_29,c253_30,c253_31,c253_32,c253_33,c253_34,c253_35,c253_36,c253_37,c253_38,c253_39,c253_40,c253_41,c253_42,c253_43,c253_44,c253_45,c253_46,c253_47,c253_48,c253_49,c253_50,c253_51,c253_52,c253_53,c253_54,c253_55,c253_56,c253_57,c253_58,c253_59,c253_60,c253_61,c253_62,c253_63]

def dict253 : Nat := 0x90c0410412180612015000440811400542020410a1202508094002102085008002600088001e00060b040241809030511024440e0a034140d090230104c0414501003b144006420160810036400d4910026080a420800144128204a029401202488091214054101606094102606100094001d003f400f8440121005002c400a83400090202500400a1001240040e0604002c1d0106415003a0b0710034400cc91201448015204009900254006c61012840500391a080a8200c60098284009c5810400710013400449810400210006300042900064801128400b4582830240890112405002e400ad00290b0103140054601914400f1002f16001000f26001000d400f500320b00031000841058384006098381a0e0a83840032000405401002430141001440069000509004342012011002222010241c084404900161008900044709414064001108150504c0012004c0a02300088010b05100001a101000a1044081108000ca8280a481001d4005468280441100201a000a800300410002400dd0030161406860046010038400c5001e30181000e120e08838084a011408000829091104084104008d00194007c4100400588100064242c280646100214005d00030904041202048200010860015050545048102204044201202084202202100040910024800850034302060088180d050481805440191021200112011000840040004c08008424440421010c020800002901054041105300004140044601114044242c20090a0444006404482022080841408400441409050c040222008828090004828090108800084808101104041100120004840090801110084041101

def d253 := unpackCases dict253 9

def u253 := unpackShort dict253 9

def w21 : Sig := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000000ff0000

def s46 := certify 253 6 ([w21,w15,i7,i6,i0,i2,i5]) cs253 [] (u253 6 75 0x92166081282c41025d8971a3458114e53a4c05294aa32332b9975c993022c12f380810e32b4204384bf087d9f6b8919665a04828a6205881680da03047412e24c1f3e28c9ebd00)

def w22 : Sig := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000

def s47 := certify 253 6 ([w22,i5,i7,i6,i0,i2,i3]) cs253 [] (u253 5 75 0x7d1f461907b1ec65a0eb89098ae036006d3218a729e4184a529681948b22e2c0430041004177a10417f810438cad104384bf10441c5910c30014ccb32e090e4229188a2a1c882)

def w23 : Sig := 0xffffffff00000000ffffffff00000000ffffffff00000000ffff0000

def s48 := certify 253 6 ([w23,i5,i7,i6,i0,i2,i3]) cs253 [] (u253 5 81 0x7d1f461907b1ec65a045084f086d3218a729e4184a52968195a696084177a10417f810438cad104384bf12698258cb32e0902604d50825fcdd080bb600010c4100c3004803a4000428022)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s49 := certify 253 7 ([w15,i7,i6,i0,i2,i3,i5]) cs253 [s46,s47,s48] (u253 5 234 0x49c20a44e6449d392ce408249420a84568495152c680822ac208018c0214638800802a48114230422a4c113c2202185e1f64207d184818647a419481ee8787b195e196822825c47b8020025c8d8048c05b068219a586582c0266c6188257466c95c8818690629c61c0a793090611861a062946516ca5a05ba0651865204610c01a402046910401800849964a6092096116394410824c5d39493e8810466c41061fc5f3947fe061043944124f0e3397c2b64104394412819ce1394672fe8104012305310c004005349282432e8144cb80518289246e56739b75950)

def s50 := certify 253 6 ([w21,w17,i7,i6,i0,i2,i5]) cs253 [] (u253 5 81 0x290b308cd52a502b863b9a69608a729e4184ef510b5199b997ba698258417f810438cad110150ed50fb3eee48cb52050a4ed4a1418c218c21a461a4613a105d90611f47d4145a5400022e)

def s51 := certify 253 7 ([w15,w17,i7,i6,i0,i2,i3,i5]) cs253 [s50] (u253 5 99 0x290b30823f52908218c6308218c630845084f087d1f46191695a5bb3f5e20878472082d5a696086d3218a729e4185bd6f4fd6ec61a4691861a4691a6982584177a10417f810438cad1047bc6711210449210448cb32e090516e503f565a00)

def w24 : Sig := 0xffffffff00000000ffffffff00000000ffffffffffffffffffffffffffff0000

def s52 := certify 253 6 ([w24,i5,i7,i6,i0,i2,i3]) cs253 [] (u253 5 81 0x7d1f461914507340eb89098ae036006d3218a729e4184551544b408b22e2c0430041004177a10417f810438cad1099265012c441c5910c30019fef99d4229188a240dd40200e900010a00)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s53 := certify 253 7 ([w16,i7,i6,i0,i2,i3,i5]) cs253 [s52] (u253 5 243 0x127082919f912767cb390208dd082411540dd455c40208a9204508c108a93044f0880861787d9081f461206191e907321441e50737873408416c1a0866961960b009a11862095d1a125722061a418a7187029e4c2418461844b1855405b1544b16c4b406402126592982482584596b10420931756b24fa20411a1104187f17d6b1ff8184116b10493c38d6bf0ad904110109912c67265019d012c412d1593e4051f99f1445142440630000965086311e20800080007897b8825f67800069000188110c692044118000414cc48030400048534a40001448d3a42364144001654f68)

def w25 : Sig := 0xffffffffffffffffffffffffffff0000

def s54 := certify 253 5 ([w25,w12,i6,i0,i2,i3]) cs253 [] (u253 5 60 0x1f47d18645141cd01b4c8629ca790611545512d0105de84105fe0410e32b4426499404bfbe61002ed800043104030c008700e900002880)

def s55 := certify 253 6 ([w22,w12,i7,i6,i0,i2,i3]) cs253 [s54] (u253 5 72 0x1f47d1864aaa7083ae24262b80d801b4c8629ca7906118751b4622c8b8b010c01040105de84105fe0410e32b44108720c41107164430c008f90492de49226223a811c2)

def w26 : Sig := 0xffffffffffffffffffffffffffffffff00000000ffffffff00000000ffff0000

def s56 := certify 253 5 ([w26,w12,i6,i0,i2,i3]) cs253 [] (u253 5 60 0x1f47d1864114213c2b80d801b4c8629ca7906169a58210c01040105de84105fe0410e32b449a609630c01260423542380900002880)

def w27 : Sig := 0xffffffff00000000ffff0000

def s57 := certify 253 6 ([w27,w12,i7,i6,i0,i2,i3]) cs253 [s56] (u253 5 75 0x7d1f46192aa9c2045084f086d3218a729e418461d46d19a696084177a10417f810438cad10421c831269825a4124b7918108d509002ed800043104030c01200e90011e2)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s58 := certify 253 7 ([w12,i7,w17,i6,i0,i2,i3]) cs253 [s55,s57] (u253 5 234 0x185e1f64207d184818647a425deb8020025c8d80780708a8b77aa71e70b72082a48114230422a4c113c220260c6188257445c95c8818690629c61c0a793090611861204610c01a4020469104018045c619c16c7545c5b1b5c1865b068219a586582c0260c410824c5d23c93e8810445c41061fc5f23c7fe0610423c4124f0e323fc2b64104012308f10c004008f49223c411c19c8723c6720dc1040849964a60920961165b4a138b7924715770b755cb7724912b9240927092b49cb30a4092900071157129454b170000630000885086311e2080009b26d0)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s59 := certify 253 8 ([w17,i6,i0,i2,i3,i5,i7]) cs253 [s49,s51,s53,s58] (u253 6 324 0x9b37410226c8136409b374df384d9004089b49c10226d2136909b49d192cc9b480811364d82044d80c4009b26f12226c002005af21050b52078a16bc8f722d4808204d95222213608c1044d95260ce26c108045ae03df0b54823e16b804602d521e485a92e79716a004002d49710d8b5007801af2835435c85aa86bcab528d7201881365981a26c106344d960c589b04c0116a5a860c5a88255a16a6b92ac8b5101831ae90314e6be060539ae9182435f006c06b9021a11ae0340035c81d100d70018052201099a52b313348866214a504944d8208989b2c4931360890226cb042c5a96a10216a2093b85ad224dd16a2020435cd70810d70dfaf1af4bf3835c304094a904094923c38e9527856d248102520048652a4106520010052a448922a8121968c9055c82328157408a9048408d5b48d1c8a9fa0002ca40ab20429fb19422a40000)

def w28 : Sig := 0xffffffffffffffff0000000000000000ffffffffffff0000

def s60 := certify 253 5 ([w28,w10,i7,i0,i2,i3]) cs253 [] (u253 5 60 0x1ec7b196828a1dce1b4c86294a5a06515c57134e105de84105fe0410e12fc42749d384dfbe70e02ed800043104030c0089010a00002880)

def s61 := certify 253 6 ([w22,w10,i6,i7,i0,i2,i3]) cs253 [s60] (u253 5 72 0x1ec7b1968b2c61e3ae24262b80d801b4c86294a5a06518791bc622c8b885b10c01040105de84105fe0410e12fc410891ac41107164430c00914049a20a2411e2a1c882)

def w29 : Sig := 0xffffffffffffffff00000000ffffffffffffffffffffffff00000000ffff0000

def s62 := certify 253 5 ([w29,w10,i7,i0,i2,i3]) cs253 [] (u253 5 60 0x1ec7b1968114213c2b80d801b4c86294a5a06569a58210c01040105de84105fe0410e12fc49a609630c012097f3742010a00002880)

def w30 : Sig := 0xffffffff000000000000000000000000ffff0000

def s63 := certify 253 6 ([w30,w10,i6,i7,i0,i2,i3]) cs253 [s62] (u253 5 75 0x7b1ec65a2cb187845084f086d3218a5296819461e46f19a696084177a10417f8104384bf1042246b1269825849a20a0e097f374202ed800043104030c012010a0011e2)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s64 := certify 253 7 ([w10,i6,w19,i7,i0,i2,i3]) cs253 [s61,s63] (u253 4 234 0xca81ec29f0f632f8650a501492e80bc061809730c3702018f05a78a02dc23078fbc54f845120454a04f1784c298c825435474950cd06305262946516ca50a45b0a46530ca40984300d202046910406023a6360311e51d0c46fc18d616f4236ac6b085b130a4220931749124c3b41088e90861fc5f2447f0e4c4212242052339c2488ce5f85242024c2448c010048ca44890980f4892443d1af04208813da4138a42b12cb7947046f180a4f10a51b3c51b0a7014a738c012d0272969660c009f27dc9288414a1a14a4a869621488442884018c0238c6118040)

def s65 := certify 253 6 ([w21,i6,w19,i7,i0,i2,i5]) cs253 [] (u253 5 81 0x2a0b1082b863b8cf2ac29a69608a5296819599b997b8f5290f2a698258417f8104384bf10fb3eee490528f329428cb46ca293f90a18c218c21a461a4613a105da0651ec7b00040ee38a5c4a)

def s66 := certify 253 7 ([w15,i6,w19,i7,i0,i2,i3,i5]) cs253 [s65] (u253 5 99 0x2a0b108218c630823dd2d08218c630845084f087b1ec65a0840dc321715c5bf3dc472082e5a696086d3218a5296819461a46919c1704f76fc61a4691a6982584177a10417f8104384bf1121044847c7c1121044a06dc032ccb46cf759cf790e)

def w31 : Sig := 0xffffffff00000000ffffffffffffffffffffffff00000000ffffffffffff0000

def s67 := certify 253 6 ([w31,i5,i6,i7,i0,i2,i3]) cs253 [] (u253 5 81 0x7b1ec65a0a287738eb89098ae036006d3218a529681945715c4d388b22e2c0430041004177a10417f8104384bf109d274e134441c5910c300f3efa03a2a1c8a238d5382010a0000e900)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s68 := certify 253 7 ([w18,i6,i7,i0,i2,i3,i5]) cs253 [s67] (u253 5 243 0x125082a187a12561cb1a0208d5082393938d54e5838208a9204508c108a93044f0880865207ba1e1ec657865a08a07778a3882877207739e396c1a0866961960b009a31862095d1a325722061a818a51945b296816e819461944d18573b015c4dc04d386382126592982482584597310420931757324fa20411a3104187f17d731ff81841173104a0673857319cbfa0410e109d137c274ef0e134413603bea187fa061e0a0e38630000967086311e208001e0002097b9e25f62000069000188110c692044118000414cc48030400048534a8000808d428236880001674f64)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s69 := certify 253 8 ([w19,i7,i0,i2,i3,i5,i6]) cs253 [s64,s49,s66,s68] (u253 3 324 0xd146fb8d10a45132cd146c5146cd10a7b96737fb93903dc0ab214f7095390e027cd52227f89fe27cd511c1927f8889f494889f0a49f0a49f494d12c49f0a4889f27c889f018c09f27c6308c9f0202e47707e8b9e8a2e47781dcb9e07f89f2a604527c8c1227ca93044f27ca08b919607b2e42907c7b2e46507c652e42980a4b925e02f2e40c302e49730c372e4200d913585736783115cd913431134d9e6e27c170c41b27c981b27c17605c9f20c48b92e598b98254352e4d9254332e6198d90a58a53646516ca53642916c29364656194d92058433640690364811a44136418053e4274531343d27453e0f785313504d27c902727c1704c2727c813227c17405cb92e510b9824c5d2e45324c3b2e6110d936510d961fc5f364531fc393659105314d10530a4673845314c672fc530a51053004f05314d305304014c5304c132356f23411)

def w32 : Sig := 0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa

def w33 : Sig := 0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa

def s70 := certify 253 5 ([w32,w33,w8,i2,i3,i4]) cs253 [] (u253 4 60 0x208c0ba801c56400c05e00dc022884f105615f06b0b42dc106218041018350ccdad58461d46d318791bcc2b0ac2b0ac420d78)

def w34 : Sig := 0xfafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafa

def s71 := certify 253 5 ([w34,w33,w8,i6,i3,i4]) cs253 [] (u253 5 57 0x60b30000a200d300072e03602cb187845084f0945e0ffe0e1278838092f091301110061b4c8618791bc669a09c5104e06)

def w35 : Sig := 0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa

def s72 := certify 253 5 ([w35,w33,w8,i6,i2,i4]) cs253 [] (u253 5 57 0x60b30000a200f90002bc4300410061e46f19a6960947e8ffe86d3218e127a83a0960960103008b2c6083096096104e88)

def s73 := certify 253 6 ([w33,i0,w8,i6,i2,i3,i4]) cs253 [s70,s71,s72] (u253 4 78 0x60b300041181750038178037005a16e3c22884f105615f10218041018350ccc61e46f36b56118751b4ce12449087005dc04190682ad04198853107811f02b0ac415856)

def s74 := certify 253 5 ([w34,w32,w8,i7,i3,i4]) cs253 [] (u253 5 57 0x70b10000a200d300062e03602aa9c2045084f0945e0ffe10e049838092f091301110061b4c8618751b4669a09c7104e06)

def s75 := certify 253 5 ([w35,w32,w8,i7,i2,i4]) cs253 [] (u253 5 57 0x70b10000a200f90002bc4300410061d46d19a6960947e8ffe86d32190e84983a0960960149006baaa706b096096104e9e)

def s76 := certify 253 6 ([w32,i0,w8,i7,i2,i3,i4]) cs253 [s70,s74,s75] (u253 4 78 0x1c2c4001046056400c05e00dc015857c408a213c41685b8f0860104060d433318751b4dad58461e46f3400a4806b1adc92ac6b1acc42986be08fc15856209224843815856)

def w36 : Sig := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffaaaa0000

def s77 := certify 253 4 ([w36,w34,i7,i6,i3]) cs253 [] (u253 6 34 0x2c5860f2a547042e00d80489080c0e21615f576c58224adb160872fec0c18015b)

def w37 : Sig := 0xffffffffffffffffffffffffffffffffaaaa0000aaaa0000aaaa0000aaaa0000

def s78 := certify 253 4 ([w37,w34,w8,i6,i3]) cs253 [] (u253 4 37 0xb42dc7845109e20bc01b81c248021048db2be522246b904e1388bf6301200b80)

def w38 : Sig := 0xffffffffffffffffaaaa0000aaaa0000ffffffffffffffffaaaa0000aaaa0000

def s79 := certify 253 4 ([w38,w34,w8,i7,i3]) cs253 [] (u253 4 37 0xac2be2045109e20bc01b821236caf9488720e41384e22b58c048024842000b00)

def w39 : Sig := 0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000

def s80 := certify 253 5 ([w39,w34,w8,i7,i6,i3]) cs253 [s77,s78,s79] (u253 5 51 0x2cb187aaa9c2045084f0849126060e41236caf4922246b49221c834a698256c0bb600060ab0007085000084700c)

def s81 := certify 253 6 ([w34,i0,w8,i7,i6,i3,i4]) cs253 [s71,s74,s80] (u253 5 75 0x60b300070b10000a202e03602cb187aaa9c2045084f0849126060e40034c02af8514ffe386085e387047e024bc244c401110061b4c8618791bc618751b4669a095b)

def s82 := certify 253 6 ([w35,i0,w8,i7,i6,i2,i4]) cs253 [s72,s75] (u253 5 75 0x60b300070b10000a2004300410061e46f1861d46d19a696086d321849126060e4003e402bfa51cffeba73485eba72c47e825825840103008b2c61eaaa708096096)

def s83 := certify 253 5 ([w36,i0,i7,i6,i2,i3]) cs253 [s77] (u253 6 54 0x2c5860f2a547042e00d800668c8306f1b8306e9b031a34580489080c0e21615f576c58626358b04495b62c10e5fd81830016)

def s84 := certify 253 5 ([w37,i0,w8,i6,i2,i3]) cs253 [s78] (u253 4 57 0x2d0b71e114427882f006e0306a1998c3c8de6d6ac210c02081c248021048db2be52308f2911235c82709c566301200b80)

def s85 := certify 253 5 ([w38,i0,w8,i7,i2,i3]) cs253 [s79] (u253 4 57 0x2b0af88114427882f006e0306a1998c3a8da6d6ac210c020821236caf948c23ca443907209c271598c048024842000b00)

def s86 := certify 253 6 ([w39,i0,w8,i7,i6,i2,i3]) cs253 [s83,s84,s85,s80] (u253 4 75 0x2d0b71e0ac2be2045109e2306a1998c3c8de630ea369b5ab084912421c3a1236caf948c6fca4448d72910e41c82709c56005e1b800218820060ab003842800211c0c)

def w40 : Sig := 0xffffffffffffffffffffffffffffffff0000aaaa0000aaaa0000aaaa0000aaaa

def s87 := certify 253 5 ([w40,i0,w8,i6,i2,i3]) cs253 [] (u253 4 57 0x2d0b71e1144278837005e0306a1998c3c8de6d6ac210402181c248021030fb3e58c47cd36318b5258c4c44c6480c05840)

def w41 : Sig := 0xffffffffffffffff0000aaaa0000aaaaffffffffffffffff0000aaaa0000aaaa

def s88 := certify 253 5 ([w41,i0,w8,i7,i2,i3]) cs253 [] (u253 4 57 0x2b0af881144278837005e0306a1998c3a8da6d6ac2104021820c3ecf96311f34d8c635776313113192030024842005840)

def w42 : Sig := 0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa

def s89 := certify 253 6 ([w42,i0,w8,i7,i6,i2,i3]) cs253 [s87,s88] (u253 4 75 0x1685b8f05615f1022884f118350ccc61e46f318751b4dad5842489210e1d061f67cb188f9a6c6316a4b18c6aeec62622600370bc0010443003042801c11c00b0812)

def w43 : Sig := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000

def s90 := certify 253 6 ([w43,w8,i7,i6,i0,i3,i4]) cs253 [] (u253 4 75 0x3059801c2c40d4e88bd05e00dc01685b8f05615f1099e9a7d31809105d0ec842246b2108720c8d2e913d09224843815c5530111018330d4d2248861bc793186d1d4c2)

def w44 : Sig := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00000000

def s91 := certify 253 6 ([w44,w8,i7,i6,i0,i2,i4]) cs253 [] (u253 4 75 0xc1660070b1000453ac0218041018791bcc61d46d326699a9622b1809105f0e4842246b2108720c8b0ac222a962489210e1544010301833306b22489ec05a16a38158562)

def s92 := certify 253 5 ([w25,w8,i6,i0,i2,i3]) cs253 [] (u253 5 57 0x2cb187945073406d321861e46f18551544b404177a10417f81042246b1099265012fe02ed800043104030c00870201240002880)

def s93 := certify 253 5 ([w28,w8,i7,i0,i2,i3]) cs253 [] (u253 3 57 0x2b0ac1d8aa1df98350cd98751b585715c4de41743b4417c394421c8342749de1343f00bc370010c410cc0224021124008230)

def w45 : Sig := 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0000

def s94 := certify 253 5 ([w45,w8,i7,i6,i2,i3]) cs253 [] (u253 5 54 0xb2c61eaaa70852d67cd61b4c8618791bc618751b4669a595b124498181344b30fb3e4c311f34cc30891acc308720cc326164c)

def w46 : Sig := 0xfafafafafafafafafafafafafafafafafafafafafafafafafafafafaaaaaaaaa

def s95 := certify 253 4 ([w46,w22,i7,i6,i3]) cs253 [] (u253 3 34 0x7d1f46107c7b1ec6580bc037032ccb08461e04505d0ed10e32b510e12fd33015b)

def w47 : Sig := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000

def s96 := certify 253 5 ([w47,w22,i7,i6,i0,i3]) cs253 [s95] (u253 6 51 0x7cf980f7af59042e00d8004b8e820438cad0810e12fc20c18015b0845c608659968300e2045beefa9164594fb88b22ca5d8459a)

def s97 := certify 253 6 ([w22,w8,i7,i6,i0,i2,i3]) cs253 [s92,s93,s94,s96] (u253 5 69 0x2cb187aaa9c20eb89098ae036006d321861e46f1861d46d188b22e237c430041004177a10417f81042246b10421c8310441c5910c3002ac491260624216811c2)

def w48 : Sig := 0xffffffffffffffffffffffffffffffff000000000000000000000000ffff0000

def s98 := certify 253 5 ([w48,w8,i6,i0,i2,i3]) cs253 [] (u253 5 57 0x2cb187845084f0ae036006d321861e46f19a69608430041004177a10417f81042246b12698258c30048e1240800002880)

def w49 : Sig := 0xffffffffffffffff0000000000000000ffffffffffffffff00000000ffff0000

def s99 := certify 253 5 ([w49,w8,i7,i0,i2,i3]) cs253 [] (u253 5 57 0x2aa9c2045084f0ae036006d321861d46d19a69608430041004177a10417f810421c8312698258c3004900049800002880)

def w50 : Sig := 0xffff0000

def s100 := certify 253 6 ([w50,w8,i7,i6,i0,i2,i3]) cs253 [s98,s99] (u253 5 69 0x2cb187aaa9c2045084f086d321861e46f1861d46d19a696084177a10417f81042246b10421c831269825849126060e400bb600010c4100c300488511e2)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s101 := certify 253 7 ([w8,i7,i6,i0,i2,i3,i4]) cs253 [s73,s76,s81,s82,s86,s89,s90,s91,s97,s100] (u253 4 234 0x12d003095e12d4acb3c00094801c437894a1a58f00018c0013fe218dfd08c40012e80bc061809730c3702018f05a28a02dc23028fbdc405610f82be7b810a1054bf62289022a502789411102610c03480811a4410180a098c825435544950cd0632a26360311e5510c46fc18ca898dc16c755445b1b786359f9d08dab1ac254440931cf23004024329282422093174df24c3b4108a890861fc5f2ac7f0e4c4225642603d224850f46bc10886909c19c8711c6720f84208813da4138a42b12c10e049e0a22484228843cc61ad53dcd5a9b0)

def s102 := certify 253 6 ([w43,w10,i7,i6,i0,i3,i4]) cs253 [] (u253 4 81 0x182cc1028aa528aad4e88bd05e00dc01685b8f1de2ac062aa67a69f4c602441743b210891ac9008aad78aad2e913d0922a8422a8afa1579a30111018330d4d2248861bc793405574455168da)

def s103 := certify 253 6 ([w44,w10,i7,i6,i0,i2,i4]) cs253 [] (u253 4 81 0x60b3027741ee80114eb00860104061e46f31df442e899a66a588ac6024417c39210891ac880d0eda2c2b088aa589340868a3369ca2008180c19983591244f602d0b6145e68212045)

def w51 : Sig := 0xffffffffffffffffffffffffffff0000ffffffffffffffffffffffffffff0000

def s104 := certify 253 6 ([w51,w8,i7,i6,i0,i2,i3]) cs253 [s92] (u253 5 75 0x2cb1879d374d7520eb89098ae036006d321861e46f18681c5b188b22e245c430041004177a10417f81042246b1046346710441c5910c30019c49126062414500047700002880)

def w52 : Sig := 0xffff0000000000000000000000000000ffff0000

def s105 := certify 253 6 ([w52,w8,i7,i6,i0,i2,i3]) cs253 [s98] (u253 5 75 0x2cb187aaa9c2045084f086d321861e46f1861d46d19a696084177a10417f81042246b10421c831269825849126060e400bb600010c4100c300495701c11c0002880)

def s106 := certify 253 7 ([w8,w10,i7,i6,i0,i2,i3,i4]) cs253 [s102,s103,s61,s104,s105] (u253 4 99 0x182cc00375250012137c0028cab005e00dc01685b8f2f2bc9ba8f211e215082ec4300820306a1998c3c8de633a22d985b3185b11cc63158c04882e876420be1c908448d642412339092910929104912421c0a2d6c0dd53782)

def s107 := certify 253 5 ([w34,w32,w9,i7,i3,i4]) cs253 [] (u253 5 57 0x42800d300062e03601450734145e0ffe020220021144f09c4bc2091369a09c7fbe41af01110061b4c86154554163104e06)

def s108 := certify 253 5 ([w35,w32,w9,i7,i2,i4]) cs253 [] (u253 5 57 0x42800f90002bc43004100551544b4147e8ffe86d3218202201a69609c582096582096fbe40ed0149006b5144163104e9e)

def s109 := certify 253 6 ([w32,i0,w9,i7,i2,i3,i4]) cs253 [s107,s108] (u253 4 78 0x100a40ac80180bc01b82941ce01685b8f0860104060d43330aa2a897030f237984008c021144f16b56172c215ac21580a4806b1adc92146b1acc239a025c163207e1fc04b)

def s110 := certify 253 4 ([w37,w34,w9,i6,i3]) cs253 [] (u253 4 40 0xb42dc7a941cc01f87e288042289e213b0209c27117e20701236caf948891ae4c60073)

def s111 := certify 253 4 ([w38,w34,w9,i7,i3]) cs253 [] (u253 5 37 0x14507342e0360021144f09c9a608ad08060048db2bd226499407330c012fbe1440)

def w53 : Sig := 0xaaaa0000aaaa0000aaaa0000aaaa0000ffffffffffffffffffffffffaaaa0000

def s112 := certify 253 4 ([w53,w34,i7,i6,i3]) cs253 [] (u253 4 40 0xb42dc7a941ce01f87e28c05957d5d16459224ad16499266039802f0dc00760008700c60067)

def s113 := certify 253 5 ([w39,w34,w9,i7,i6,i3]) cs253 [s110,s111,s112] (u253 4 54 0x1685b8f52839c03f0fc518084513c427605c09c2710ce20156091b657ca4448d722649980e600bc37003042801011c0c)

def s114 := certify 253 6 ([w34,i0,w9,i7,i6,i3,i4]) cs253 [s107,s113] (u253 5 78 0x182cc0010a00b80d80b2c61e5141cd0fbe1450080880084513c208e602712f08244da68216c034c02178514ffe386047e1082d06bc401110061b4c8618791bc6154554073)

def s115 := certify 253 6 ([w35,i0,w9,i7,i6,i2,i4]) cs253 [s108] (u253 4 78 0xc16600402900860104061e46f30aa2a8970306a19983f0fc51808011835ab084ec0b9610ad610ac03e4057876a39fe1d876e688e1dc04b81da402060405a16e3d4a404b)

def s116 := certify 253 5 ([w37,i0,w9,i6,i2,i3]) cs253 [s110] (u253 4 60 0x5a16e3d4a0e60306a1998c3c8de61545512c01f87e288042289e2d6ac213b0209c2715840e0246d95f291847948891ae4c6004b)

def s117 := certify 253 5 ([w38,i0,w9,i7,i2,i3]) cs253 [s111] (u253 4 57 0xa5073805e00dc060d43330aa2a897010c0208042289e2d6ac2e04e138ac20601236caf948c23c899266025b180907e1f8a20)

def s118 := certify 253 5 ([w53,i0,i7,i6,i2,i3]) cs253 [s112] (u253 6 60 0xb16183c50a722019a320c1bc6e0d52a4a20f9f5021615f576c58626358b04495b609926484a00b9b003468b000038c000040e001830016)

def s119 := certify 253 6 ([w39,i0,w9,i7,i6,i2,i3]) cs253 [s116,s117,s113,s118] (u253 4 78 0x2d0b71ea5073818350ccc61e46f30aa2a89700fc3f146021144f16b56109d81702709c56100df048db2be5231572911235c899266025802f0dc0010c41003042801011c0c)

def s120 := certify 253 5 ([w41,i0,w9,i7,i2,i3]) cs253 [] (u253 4 57 0x14a0e700dc01780c1a86661545512e02080430084513c5ad585c4c58265802030fb3e58c47cd3631d5831920303f0fe00)

def s121 := certify 253 6 ([w42,i0,w9,i7,i6,i2,i3]) cs253 [s120] (u253 4 78 0x5a16e3d4a0e70306a1998c3c8de61545512e01f87e28c042289e2d6ac213b02e262c132c010187d9f2c623e69b18c5a92c63ab0600370bc001044300302380025c012)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s122 := certify 253 7 ([w9,i7,i6,i0,i2,i3,i4]) cs253 [s109,s114,s115,s119,s121] (u253 4 243 0x4b400c31f84b58f2cf0001fa00410d81fa86853000097405e030c04b9861b8100c782d145016e118147de1cd1487a839f873822040984300d20204691040603ae6320950d59125433418cc898d80c479644311bf063096615602d8aa258b625c0d00498909180200df949d72110498ba559261da0846448430fe2f90a3f87262118f21301e9122387a35e0848109912c67266033c04b209686e03f80a21fb1e288a30c414d108031814d18c230080810bc5488a82a44ff08461685bb68d6b0b6214ac1390413c84225ad8108511c5d81c7028884a6a6bc)

def s123 := certify 253 6 ([w25,i7,w10,i6,i0,i2,i3]) cs253 [s92] (u253 5 78 0xb2c61e3ae242625141cd01b4c8618791bc622c8b885b1545512d0105de84105fe0410891ac41107164426499404b91840f1417f4047400bb600010c4100c30019c03c580000a2028)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s124 := certify 253 7 ([w51,w10,i6,i0,i2,i3,i7]) cs253 [s61,s123,s104] (u253 5 225 0x7321441e507378734084187ac3c48b182183c5e799378eb8888993210989e88977ae008009723601e004b1855405b1544b16c4b40641831862095d117257220619171866301e517c06f6061a216c8b45c622e21a245c5b16c8116c4300600811841005b010109912c67265019d012c412d8310420931749124fa2041117104187f17c911ff8184109110463c22491f06b604109110489241c91485988410019cc24443001002446719e0604940f14203c60418409b26e45b5d95b4dd8a2414d40dd2ad75422416d28c23f4001021503f447a10000)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s125 := certify 253 8 ([w10,i6,i0,i2,i3,i4,i7]) cs253 [s101,s106,s122,s124,s64] (u253 4 324 0x519fa00147028e0519fa9085251c00028d2d000a3c147828d2d464b328f000146318005188a31146319be119462000bb1cd142ee1ea17639f8732ee0881464ba02f28c06180a325cc30dca302005de3c1697678a02d2ef08c17678fbc5d953e114bb12045d952813cbb1784628966154c580b62a98a258b62598b0340a3204c2194601a4051902348825180c02ecbb318bb412a1a9766292a199768318c5314c63170188f26298a188de62e0c6316c2de8c511b462d8d631442d8891810992444b19c99246033c09112c8259460930a32448c28c04014651ca45d97642176824c5d2ec9124c3b2ed04218a6290862987f17cc52447f0e4c53108489224212380f489244910f46b2470421222204e48da413922290891b12c8684381251981e30464213c4214361880e2388e2e434dd1094d81570214dd11f886c042)

def s126 := certify 253 6 ([w28,i6,w12,i7,i0,i2,i3]) cs253 [s93] (u253 5 78 0xaaa7083ae2426228a1dce1b4c8618751b4622c8b8b015c57134e105de84105fe04108720c4110716442749d384da0e70b738e60447380bb600010c4100c300f002ddc0000a2024)

def w54 : Sig := 0xffffffffffffffffffffffffffffffffffffffffffff0000ffffffffffff0000

def s127 := certify 253 6 ([w8,i6,w54,i7,i0,i2,i3]) cs253 [s93] (u253 5 75 0x2aa9c22e03601db76d5978eb8909886d321861d46d184300410068370188b22e24744177a10417f810421c8310c300f0462fc10441c59120a000a200491251b5644701800e)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s128 := certify 253 7 ([w54,w12,i7,i0,i2,i3,i6]) cs253 [s55,s126,s127] (u253 5 225 0xb738e7051124b7144b770e394f38e88d588ab3555988e388538e00f700473de400e007778a3882877207739e39c22a2ddea9c79c2dc8219320eb88c1899330509888889722e00c3009730f6008004d18573b015c4dc04d38639851862095d11d2572206191d186705b1d51d16c6d7061a2c08b474622e21a24770c081c0430060081184103000e109d137c274ef0e13441358510420931748f24fa204111d104187f17c8f1ff8184108f104706721c8f19c83704108f10489241c8f4859884100f0c23c430010023fcf09f27e85bdd95bd6f2842)

def s129 := certify 253 6 ([w43,i6,w12,i7,i0,i3,i4]) cs253 [] (u253 4 81 0x1c2c40d4e88bd4262b94e2b85e00dc015857c4267a69f47a8af088aec602441743b2108720c8d2e913d41e2bb622b8aa2b8925b8ae2beb1a30111018330d4d2248861b47530b46d385777457)

def s130 := certify 253 6 ([w44,i6,w12,i7,i0,i2,i4]) cs253 [] (u253 3 81 0x1d2c400453ac13fa1f6843010418751b59334cd4b114f5a43eb30013417c394421c834585611154b4168f3a0568492dea8cf066a0103060cd83504d013480742b0ac88e7117a97ba)

def w55 : Sig := 0xffff000000000000ffff0000

def s131 := certify 253 6 ([w55,w8,i6,i7,i0,i2,i3]) cs253 [s99] (u253 5 75 0x2aa9c22cb187845084f086d321861d46d1861e46f19a696084177a10417f810421c831042246b12698259012449818380bb600010c4100c300491b01811c0002880)

def s132 := certify 253 7 ([w8,i6,w12,i7,i0,i2,i3,i4]) cs253 [s129,s130,s55,s127,s131] (u253 3 99 0x1d2c4012137c00d549c00a12ac02f00dc02b0ac1d8839e1785ed7b3541f21620bd10c041060d433661d46d60c59831677431611d98c7cc004d05d0ed105f0e5108720d101304d12150f5101304d0216ac849124b73554f35419e)

def s133 := certify 253 5 ([w34,w33,w11,i6,i3,i4]) cs253 [] (u253 5 57 0x3a400d300072e03600a28773945e0ffe3ef8e6c420220021144f0984bc2091369a09c501110061b4c8615c573963104e06)

def s134 := certify 253 5 ([w35,w33,w11,i6,i2,i4]) cs253 [] (u253 4 57 0xe09407c80057886010402b8ae26b9470ecff0ecc1a86660fc3f71e6200460d6ac2c5842b5842b01030214a72c6420768)

def s135 := certify 253 6 ([w33,i0,w11,i6,i2,i3,i4]) cs253 [s133,s134] (u253 4 78 0x382502ea00702f006e052877705615f10218041018350ccc2b8ae26b8c3a8da60fc3f709a200460108a278b5ab0b1610ad610ac05dc041906821504198473384d72c64)

def s136 := certify 253 4 ([w38,w34,w11,i7,i3]) cs253 [] (u253 4 40 0xac2be214a1dc021144f10a1c104e1388ad1030091b657ca443907263003b87e1f8420)

def s137 := certify 253 4 ([w37,w34,w11,i6,i3]) cs253 [] (u253 5 37 0xa28773ae03603efa00021144f0989a60bc08070048db2bd22749d387730c012)

def w56 : Sig := 0xaaaa0000aaaa0000ffffffffffffffffaaaa0000aaaa0000ffffffffaaaa0000

def s138 := certify 253 4 ([w56,w34,i6,i7,i3]) cs253 [] (u253 5 40 0xaaa70828a1dcefbe80e1655f57459164872fc592749d387702ed8001070000e60030c03c)

def s139 := certify 253 5 ([w39,w34,w11,i6,i7,i3]) cs253 [s136,s137,s138] (u253 5 54 0xaaa70828a1dcefbe80e084513c2090702626982f0200ab01236caf49221c83489d274e1dc0bb60007085000384700c)

def s140 := certify 253 6 ([w34,i0,w11,i6,i7,i3,i4]) cs253 [s133,s139] (u253 5 78 0x1c2c4000e900b80d80aaa70828a1dcefbe80e080880084513c2090702612f08244da682c0034c02178514ffe387047e0e864e6c4401110061b4c8618751b4615c573877)

def s141 := certify 253 6 ([w35,i0,w11,i6,i7,i2,i4]) cs253 [s134] (u253 5 78 0x1c2c4000e90010c0104018751b4615c57134e1b4c86fbe80e08088069a5820907026160825960825803e402bfa51cffeba72c47e8e134e3cc40103008aaa70828a384d)

def s142 := certify 253 5 ([w38,i0,w11,i7,i2,i3]) cs253 [s136] (u253 4 60 0x5615f10a50ee0306a1998c3a8da615c57134021144f16b5610a1c104e138ac20601236caf948c23ca443907263002687e1f8420)

def s143 := certify 253 5 ([w37,i0,w11,i6,i2,i3]) cs253 [s137] (u253 5 57 0xa28773ae036006d32185715c4d3843004103efa00021144f09a6960989a609608070048db2bd248611d22749d384d30c012)

def s144 := certify 253 5 ([w56,i0,i6,i7,i2,i3]) cs253 [s138] (u253 6 60 0xa951c10285761c19a320c1ba6c0d5ab4c1cf9f201d615f576c58626358b04397f609d27474c00b9b003468b000040e000038c001830016)

def s145 := certify 253 6 ([w39,i0,w11,i6,i7,i2,i3]) cs253 [s142,s143,s139,s144] (u253 4 78 0x2b0af8852877718350ccc61d46d30ae2b89ae0fc3f085c21144f16b5610a1c1602709c56100df048db2be5231572910e41c89d275c26802f0dc0010c41003842800e11c0c)

def s146 := certify 253 5 ([w40,i0,w11,i6,i2,i3]) cs253 [] (u253 3 57 0xaa1df83700bc18350cd85715c4de10404300fc3fe021144f206c1b05c8194c70b017020c3ecf9cc47cd3cc77fb30130c)

def s147 := certify 253 6 ([w42,i0,w11,i6,i7,i2,i3]) cs253 [s146] (u253 4 78 0x5615f10a50eee306a1998c3a8da615c57135c1f87e10b842289e2d6ac214382c262c132c010187d9f2c623e69b18c6aeec63bee600370bc001044300382380026b812)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s148 := certify 253 7 ([w11,i6,i7,i0,i2,i3,i4]) cs253 [s135,s140,s141,s145,s147] (u253 4 243 0x4a400e2fbc4a57d2c78001ee00392b71ee9584ae00097405e030c04b9861b8100e202b087c15f3dc085081dfca72143ba077779c40984300d20204691040603c26320950d59525433418cca98dc16c756545b1b786309a615dc188ae2686226b8ce0498909180200df949e12110498ba559261da0846548430fe2f90a3f87262117d21383390e238ce41f0847109d1343d275c1eb84d209a10b83fe2fa1f842be843c7394f108031814f18c230081e10905488be2a44f4084616831b68d6b062214ac1390413c84225adc108211c61c1c7810884a7a6b8)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s149 := certify 253 8 ([w12,i7,i0,i2,i3,i4,i6]) cs253 [s128,s58,s101,s132,s148] (u253 4 324 0x1a25bb9c68f051124d12dc512dcd1e39ca7a42e7256235446f9566ae12b1384509ee00142e285c509ee4284a50b80028529000a1e143c28529344b1287800142318005088a111423188e119422000bd1dfca2f5c8517a3ba0772f5de71424ba02f28406180a125cc30dca102005ef101597a5bf82b2f79ee17a5ba105e9528114bd118222f4a93044f2f448118e26985731dc188ae6389a1889a63b8ce2848130865080690142408d2209420300bd2f4c62f504a86a5e98e4a8665ea0c631cc7318c7e0b63a98e638b63698fc318c7b063a31c46d18f6358c71062223dc42748f1343d2748f707ae23c4d209a50824c2848f230a10100509432917a5e9085ea093174bd23c930ecbd41086398e4218e61fc5f31c8f1fc3931cc4211e4790847f06721c8f23c6720c8fe108478881391f6904e478a4223ec4b0e2388e30)

def w57 : Sig := 0xaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaaaaaaaaaaaaaaa

def s150 := certify 253 5 ([w34,w57,i6,i7,i4,i5]) cs253 [] (u253 4 60 0xcda057433d416a80208c09dd07ba27ea1f54aa042a125e244c0698110a428e5394420726d6841e8111018efa4287aa9ca)

def s151 := certify 253 6 ([w57,i0,i6,i7,i2,i4,i5]) cs253 [s150] (u253 4 81 0x336815d0cf505aa00823027741ee89fa87d56b5610860104077d10ba1eaa43d4aa042a1585603c600f43d308e685214729ca20ac2b01c3020313062685214729ca)

def w58 : Sig := 0xf0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0f0f0f0f0f0f0f0

def s152 := certify 253 6 ([w58,i2,i6,i7,i0,i4,i5]) cs253 [] (u253 4 81 0x19b40ae867a82d500411813ba0f744fd43ea82709c5663012406876d10551e6a20fe3f9083f8fe4550215585611020204025d04ba09aa13546b0ac2204040821412e8e509aa)

def s153 := certify 253 4 ([w38,w34,w13,i7,i5]) cs253 [] (u253 5 40 0x3354a9433cab0a20239c2414814f122b5238a20a9a60bc40543b5430c00a29480a)

def s154 := certify 253 4 ([w37,w34,w13,i6,i5]) cs253 [] (u253 5 40 0x33cab0a3354a9429480a20239c238a20af12f124148149a60bc414a3cca30c014)

def w59 : Sig := 0xffffffffaaaa0000ffffffffaaaa0000ffffffffaaaa0000ffffffffaaaa0000

def s155 := certify 253 4 ([w59,w34,w13,i6,i7]) cs253 [] (u253 5 40 0x29480a41481438a20af059f05920039c040543b54414a3cca30c03c3354a9433cab0a)

def w60 : Sig := 0xaaff00ffaaff00ffaaff00ffaaff00ffaaff00ffaaff00ffaaaa0000aaaa0000

def s156 := certify 253 4 ([w60,w34,i6,i7,i5]) cs253 [] (u253 4 40 0xcda057433d416a95408541384e20f501a1db4415479a80239c00a04340290a63012)

def s157 := certify 253 5 ([w39,w34,w13,i6,i7,i5]) cs253 [s153,s154,s155,s156] (u253 4 57 0x66d02ba19ea0b54aa042a408e7142810d1ca4283d907b2400df004e13883d406876d10551e6a008ab002842d00a11d4c)

def s158 := certify 253 6 ([w34,i0,w13,i6,i7,i4,i5]) cs253 [s157,s150] (u253 4 81 0x66d02ba19ea0b540104604ee83dd13f50faa55021520473890040c10a04347290a4072428721898313092f1226034c023aab45568a9a9535135a10620444063be8aad0f552a6a)

def w61 : Sig := 0x5050505050505050505050505050505050505050505050505050505050505050

def s159 := certify 253 6 ([w61,i0,w13,i6,i7,i4,i5]) cs253 [] (u253 4 81 0xcda057433d416a80208c09dd07ba27ea1f54aa042a408e712008182140868e52141e903d206260c4c1384e2b3180920343b6882a8f356b5611810d80efa21743d5487a839)

def s160 := certify 253 5 ([w38,i0,w13,i7,i2,i5]) cs253 [s153] (u253 4 60 0x336815d0cf505aad6ac23be885d0f5521ea408e7106260c4d0a04340f6456c9ca4282709c5691847920343b68c6014aa042a)

def s161 := certify 253 5 ([w37,i0,w13,i6,i2,i5]) cs253 [s154] (u253 4 60 0x33d416a8cda0574d6ac23d5487a8efa2174550215204738831306267290a0f641eca1408681384e2b48c23c90551e6a63014)

def s162 := certify 253 5 ([w59,i0,w13,i6,i7,i2]) cs253 [s155] (u253 4 60 0x77d10ba1eaa43d5ad580aa042a0c4c189a140868e52141e8b21e8b2801ce01658911c59406876d10551e6a63016336815d0cf505aa)

def s163 := certify 253 5 ([w60,i0,i6,i7,i2,i5]) cs253 [s156] (u253 4 60 0x336815d0cf505aad6ac23be885d0f5521ea55021504e138ad2308f2406876d10551e6a63012008e70004310400a04340290a)

def s164 := certify 253 6 ([w39,i0,w13,i6,i7,i2,i5]) cs253 [s160,s161,s162,s157,s163] (u253 4 81 0x66d02ba19ea0b55ad58477d10ba1eaa43d4aa042a408e7106260c4d0a04347290a0f641ec90048401384e2b48c6fc901a1db4415479a8022ac0010c41002842d00a11d4c)

def w62 : Sig := 0xffaaff00ffaaff00ffaaff00ffaaff00ffaaff00ffaaff0000aaaa0000aaaa

def s165 := certify 253 5 ([w62,i0,i6,i7,i2,i5]) cs253 [] (u253 4 60 0xcda057433d416ab5ab08efa21743d5487a9540854c4c44c623e69b1948318a73016100020886005214029ca9300c)

def s166 := certify 253 6 ([w42,i0,w13,i6,i7,i2,i5]) cs253 [s165] (u253 4 81 0x66d02ba19ea0b55ad58477d10ba1eaa43d4aa042a408e7106260c4d0a04347290a431e36313113188f9a6c651556314a9b016100020886005155a014a9a80811c12)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s167 := certify 253 7 ([w13,i6,i7,i0,i2,i4,i5]) cs253 [s151,s152,s158,s159,s164,s166] (u253 4 252 0x2f223368a0d1796d42ba0a8bd88cf5282a5edb30b54250c600094110c6a0846200169027746d68b4b6a3dd0145c409fa9b352e2d98faa02ac18e846d58d610622204c2180690102348820301e731df416e8f38b685d0d4794c7aa83153ca18a1ea3284409ed209c52158960498e7918020121948df210c3f8be558fe1c9884554880d067a2aa339db425153220aa0f54a987a79a88a0854aa0a34084510868a52828408c11246609ce240923420061812330d03020018a031324660c4850c4c8307a80f4891903d11c3d220810a214f5021f043445051f394850a2842bca)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s168 := certify 253 8 ([w14,i6,i7,i0,i2,i3,i4,i5]) cs253 [s167,s49,s101] (u253 5 315 0x19d0828135819d344b780209ed08214535145ed464f1144209350821c5351c53548cab1c420863000093508634d6208001eb000813d81eb3451b80001e90001453d145e9465571440013d0002353d2353d48c85234000a9204508c108a93044f088089722e00c3009730f6008013720881e813779e808213779e14482137208145e793748c4732482137208325373256c1a0866961960b008811843006900811a44100601371862095d14325722061943186805b814316c5b80619431861470c143c30144619431863a70c143c303a4618212659298248258458048c39443001004f5249371042093174e524fa2041143104187f17ce51ff818410e5104806780e519c6780410e5104147cf0e5f3c144410e510414fcf0e5f3c14c411ab465080d1811914451344d1345ad344e)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s169 := certify 253 9 (roots 253) cs253 [s59,s69,s125,s149,s168] (u253 6 336 0x34500e7c8c90a0f921414101a24070ee06e8205c087021c0dd37ce702008170354102e03b80ee06a9566380e04088d3f4000234811a408d3f48550469000008d3dc000234711a388d3de32423470001c310001c017005c317045c01000064f21050c92078a193c8f723248082064f63c28c91c205193d847632471e1dc0a911138023041702a4c19dc0108044692e21711a00c3004692e61b62340080074ca0d50e9216aa1d32ad4a3a48062074cc0d58e91cc2b1d33184c3a47061dc0b3035c010635c0b062dc013004469021a111a0340023481d1008d0018019264860c6488255a1927492ac8c91018352201099a52b313348866214a504954870427694c784ed21cf0752981267004113702c4937004481702c10b11a0090c23690418468008008d234912324c90810c91049dc3269126e8c9101021d27484087486fd78e9a5f9c1d218204)

theorem lower253 : Claim 253 10 := fromSearch 25860 (by decide +kernel) s169.property

theorem lower202 : Claim 202 5 := fromLift 5 2 318791792 lower200 (by decide +kernel)

def cs170 : Cuts (goalAt 170) := []

def dict170 : Nat := 0x88280a808220a20a002a20088a08800208008808088002220208082202

def d170 := unpackCases dict170 4

def u170 := unpackShort dict170 4

def s170 := certify 170 3 (roots 170) cs170 [] (d170 24 0x1c06641b0a0551433092872)

theorem lower170 : Claim 170 4 := fromSearch 269512784 (by decide +kernel) s170.property

def cs226 : Cuts (goalAt 226) := []

def dict226 : Nat := 0xc040301806202089086220089808280300008200088008202088802202

def d226 := unpackCases dict226 4

def u226 := unpackShort dict226 4

def s171 := certify 226 3 (roots 226) cs226 [] (d226 24 0x55c202b00a90442118713306)

theorem lower226 : Claim 226 4 := fromSearch 386924624 (by decide +kernel) s171.property

def c234_0 := ruleFor 234 lower200 none (by decide +kernel)

def c234_1 := ruleFor 234 lower202 none (by decide +kernel)

def c234_2 := ruleFor 234 lower170 none (by decide +kernel)

def c234_3 := ruleFor 234 lower226 none (by decide +kernel)

def c234_4 := ruleFor 234 lower202 (some (0,i1,i7)) (by decide +kernel)

def cs234 : Cuts (goalAt 234) := [c234_0,c234_1,c234_2,c234_3,c234_4]

def dict234 : Nat := 0x8001600048000e00028000482422a00048202280088021a1004a40188002a0008820622040010a88020828e00030800c0021a020a82808a004a0012008680030108822022820880a3008100031a1804a0a1290868282080200004000888200a808220a188086242189802a20088a04828301804a08120288800300002a280a828882830100c08020a010000400048880088008808208084800121002220120202202

def d234 := unpackCases dict234 7

def u234 := unpackShort dict234 7

def w63 : Sig := 0xffffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00

def s172 := certify 234 5 ([w63,i3,i6,i1,i5,i7]) cs234 [] (u234 3 53 0xa1d0022d001f1f04343acee0172922724212144212142a1ba19caca1f01f0263f11caca)

def w64 : Sig := 0xffffffffffffffff0000000000000000ff00ff00ff00ff00

def s173 := certify 234 4 ([w64,i3,i7,i1,i5]) cs234 [] (u234 3 40 0x69234f23ee017672365235d85b88591f8823c820630227292a23c2311828)

def w65 : Sig := 0xffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00

def s174 := certify 234 5 ([w65,i3,i7,i1,i5,i6]) cs234 [s173] (u234 3 53 0x2c19241223f0372d00c1d001f1f0292272ee01753c51c421214421214a2192111f01f0c116b6)

def w66 : Sig := 0xffffffff00ff00ffffffffff00ff00ffffffffff00000000ffffffff00000000

def s175 := certify 234 4 ([w66,i3,i7,i1,i6]) cs234 [] (u234 3 40 0x2c2b229227253c51c4312f4ee0158826d2525c63b03900372d00a1d0)

def w67 : Sig := 0xff00ff00ff00ff00ff00ff00ff00ff00000000000000000000000000000000

def s176 := certify 234 5 ([w67,i3,i7,i1,i5,i6]) cs234 [s175] (u234 3 53 0x2c1920372d00c1d0292272ee01753c51c4312f4882193b039025c6192192130410174174a11)

def w68 : Sig := 0x3333333333333333333333333333333333333333000000003333333300000000

def s177 := certify 234 4 ([w68,w12,i7,i3,i6]) cs234 [] (u234 3 34 0x24f2b277e45e882113d3d1d675e73e434271242f31445f5546f)

def s178 := certify 234 5 ([w12,i7,i1,i3,i6]) cs234 [s177] (u234 4 111 0xac42e613caf057c108d446e04501aa2968040141183204616210e18f4ae07bc870acc6f18ec0960f259c80c04921488cc492664e22091c8431098a390979884a109cb2ad2cbfc210082ea11c020294a4a4a)

def s179 := certify 234 4 ([w13,i6,i7,i1,i5]) cs234 [] (u234 3 40 0x83253d25598818ee0177f257d255d85b88251b8607b064794a251b2511868)

def s180 := certify 234 5 ([w14,i6,i7,i1,i3,i5]) cs234 [s179] (u234 2 53 0x365601a9a806a6a0ec1c8c362384761141d9343c3c0bc312f906d5e4333390ccce058d8cc2a)

def w69 : Sig := 0xffffffff00000000ffffffffffffffffffffffff00000000ffffffff00000000

def s181 := certify 234 4 ([w69,i6,i7,i1,i3]) cs234 [] (u234 3 40 0x3d3d1d6882113b03904312f4455574292272ee01523231b20a1d00372d0)

def w70 : Sig := 0xffffffffffffffff00000000000000000000000000000000

def s182 := certify 234 5 ([w70,i6,i7,i1,i3,i5]) cs234 [s181] (u234 4 53 0xd158006e5a03b01c80da81908141ce0588625e42695c852227111e852020820681ac4b1158)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s183 := certify 234 6 (roots 234) cs234 [s172,s174,s176,s178,s180,s182] (u234 4 160 0x11fa1119fab0471bac68fd42549840092a4a930c5f24a00248a004846a6f245352d9080089618953550258764189aa328fc50426e0c84111847f88425e31dc809609792ce6403028a221d19643a2acaa308ca2490a6823315124cc9e8220a40b3a5423a4020252b5a88e4250c4263447212fa1884)

theorem lower234 : Claim 234 7 := fromSearch 319840336 (by decide +kernel) s183.property

theorem lower206 : Claim 206 6 := fromLift 6 2 302016112 lower204 (by decide +kernel)

theorem lower198 : Claim 198 5 := fromLift 5 2 301991536 lower196 (by decide +kernel)

theorem lower230 : Claim 230 6 := fromLift 6 2 303039824 lower228 (by decide +kernel)

theorem lower110 : Claim 110 5 := fromLift 5 2 34628944 lower108 (by decide +kernel)

theorem lower174 : Claim 174 5 := fromLift 5 2 269514064 lower172 (by decide +kernel)

def cs102 : Cuts (goalAt 102) := []

def dict102 : Nat := 0x6202089084604110184442110002400088002404090802220110102202

def d102 := unpackCases dict102 4

def u102 := unpackShort dict102 4

def s184 := certify 102 3 (roots 102) cs102 [] (d102 24 0xcb077136640a19155042382)

theorem lower102 : Claim 102 4 := fromSearch 34604368 (by decide +kernel) s184.property

def c238_0 := ruleFor 238 lower234 none (by decide +kernel)

def c238_1 := ruleFor 238 lower236 none (by decide +kernel)

def c238_2 := ruleFor 238 lower206 none (by decide +kernel)

def c238_3 := ruleFor 238 lower198 none (by decide +kernel)

def c238_4 := ruleFor 238 lower230 none (by decide +kernel)

def c238_5 := ruleFor 238 lower110 none (by decide +kernel)

def c238_6 := ruleFor 238 lower174 none (by decide +kernel)

def c238_7 := ruleFor 238 lower234 (some (3,i3,i6)) (by decide +kernel)

def c238_8 := ruleFor 238 lower234 (some (2,i3,i6)) (by decide +kernel)

def c238_9 := ruleFor 238 lower236 (some (1,i3,i6)) (by decide +kernel)

def c238_10 := ruleFor 238 lower234 (some (1,i3,i6)) (by decide +kernel)

def c238_11 := ruleFor 238 lower234 (some (0,i3,i6)) (by decide +kernel)

def c238_12 := ruleFor 238 lower236 (some (3,i3,i6)) (by decide +kernel)

def c238_13 := ruleFor 238 lower234 (some (3,i3,i7)) (by decide +kernel)

def c238_14 := ruleFor 238 lower234 (some (2,i3,i7)) (by decide +kernel)

def c238_15 := ruleFor 238 lower236 (some (1,i3,i7)) (by decide +kernel)

def c238_16 := ruleFor 238 lower234 (some (1,i3,i7)) (by decide +kernel)

def c238_17 := ruleFor 238 lower102 none (by decide +kernel)

def c238_18 := ruleFor 238 lower234 (some (0,i3,i7)) (by decide +kernel)

def c238_19 := ruleFor 238 lower236 (some (3,i3,i7)) (by decide +kernel)

def c238_20 := ruleFor 238 lower234 (some (1,i5,i7)) (by decide +kernel)

def c238_21 := ruleFor 238 lower234 (some (2,i5,i7)) (by decide +kernel)

def c238_22 := ruleFor 238 lower228 (some (1,i5,i7)) (by decide +kernel)

def c238_23 := ruleFor 238 lower200 none (by decide +kernel)

def c238_24 := ruleFor 238 lower230 (some (1,i5,i7)) (by decide +kernel)

def c238_25 := ruleFor 238 lower234 (some (3,i5,i6)) (by decide +kernel)

def c238_26 := ruleFor 238 lower236 (some (1,i5,i6)) (by decide +kernel)

def c238_27 := ruleFor 238 lower234 (some (2,i5,i6)) (by decide +kernel)

def c238_28 := ruleFor 238 lower234 (some (1,i5,i6)) (by decide +kernel)

def c238_29 := ruleFor 238 lower234 (some (0,i5,i6)) (by decide +kernel)

def c238_30 := ruleFor 238 lower202 (some (1,i1,i6)) (by decide +kernel)

def c238_31 := ruleFor 238 lower206 (some (1,i1,i6)) (by decide +kernel)

def c238_32 := ruleFor 238 lower198 (some (1,i1,i6)) (by decide +kernel)

def c238_33 := ruleFor 238 lower236 (some (3,i5,i6)) (by decide +kernel)

def c238_34 := ruleFor 238 lower236 (some (1,i5,i7)) (by decide +kernel)

def c238_35 := ruleFor 238 lower206 (some (3,i1,i7)) (by decide +kernel)

def c238_36 := ruleFor 238 lower202 (some (0,i1,i7)) (by decide +kernel)

def c238_37 := ruleFor 238 lower234 (some (3,i5,i7)) (by decide +kernel)

def c238_38 := ruleFor 238 lower202 (some (3,i1,i7)) (by decide +kernel)

def c238_39 := ruleFor 238 lower198 (some (3,i1,i7)) (by decide +kernel)

def c238_40 := ruleFor 238 lower236 (some (2,i5,i7)) (by decide +kernel)

def c238_41 := ruleFor 238 lower230 (some (2,i5,i7)) (by decide +kernel)

def c238_42 := ruleFor 238 lower234 (some (0,i5,i7)) (by decide +kernel)

def c238_43 := ruleFor 238 lower236 (some (3,i5,i7)) (by decide +kernel)

def c238_44 := ruleFor 238 lower234 (some (2,i6,i7)) (by decide +kernel)

def c238_45 := ruleFor 238 lower234 (some (3,i6,i7)) (by decide +kernel)

def c238_46 := ruleFor 238 lower170 none (by decide +kernel)

def c238_47 := ruleFor 238 lower108 none (by decide +kernel)

def c238_48 := ruleFor 238 lower236 (some (0,i6,i7)) (by decide +kernel)

def c238_49 := ruleFor 238 lower234 (some (0,i6,i7)) (by decide +kernel)

def c238_50 := ruleFor 238 lower236 (some (1,i6,i7)) (by decide +kernel)

def c238_51 := ruleFor 238 lower234 (some (1,i6,i7)) (by decide +kernel)

def c238_52 := ruleFor 238 lower236 (some (2,i6,i7)) (by decide +kernel)

def c238_53 := ruleFor 238 lower236 (some (3,i6,i7)) (by decide +kernel)

def cs238 : Cuts (goalAt 238) := [c238_0,c238_1,c238_2,c238_3,c238_4,c238_5,c238_6,c238_7,c238_8,c238_9,c238_10,c238_11,c238_12,c238_13,c238_14,c238_15,c238_16,c238_17,c238_18,c238_19,c238_20,c238_21,c238_22,c238_23,c238_24,c238_25,c238_26,c238_27,c238_28,c238_29,c238_30,c238_31,c238_32,c238_33,c238_34,c238_35,c238_36,c238_37,c238_38,c238_39,c238_40,c238_41,c238_42,c238_43,c238_44,c238_45,c238_46,c238_47,c238_48,c238_49,c238_50,c238_51,c238_52,c238_53]

def dict238 : Nat := 0x2000d230084c02128104842400a9002709101001d40081001f4006c8408400488e04230188c0a22831000e4002c4c8040021003538202000c8002c4c04228084a0230280c24021810240c0a810220c110802240191806808210a0c00209020840230801001340058c88032101000922100c004400c100268002a0009800220007800188240400788208400d10032400ac2c080b03100242880886004005c8a044003d000c130304a0a400a5002340084820412200820a30909002f0b0102c00118008c0c22828a8a0400688c0440041000d2a202000540029000723001002e110202402400c500250a821001912180a80022009002d400b0a42040062000423020880a110308804400704c00400cc260438080a220098010011220308a08228004a400898044020882200031a000e0a018900642013020480c120810028209084804381820002128004802188004a080a800a8201a100c0421202884200881100031a08062201181a000140055000609200c02008a0046041880900221290882200882846424005100013000044064001100000a8088400800010002120a02c203018024280a881000511108c080088a068602a0a08820208004400212002a0a210102c280a8a06260189086828220a0828009000880022020c040222004800090104440088004808208084840110102202090802220

def d238 := unpackCases dict238 8

def u238 := unpackShort dict238 8

def s185 := certify 238 5 ([w13,i7,i6,i1,i2,i5]) cs238 [] (u238 4 60 0x59d14f474f073cf7a4468d14347df1abc738920088604dd13345ff1cfca73144111e480a024017a0351145731c)

def w71 : Sig := 0xffffffffffffffffffffffffffffffffffffffffffffffffff00ff00ff00ff00

def s186 := certify 238 6 ([w71,i7,i3,i6,i1,i2,i5]) cs238 [s185] (u238 4 75 0x1184f213423210623127bd222ad8a96085a2d136f4c3d085a2d139c4900443025588b600562b03074d9d00562b03358618624189188635f58d474a6a)

def w72 : Sig := 0xffffffffffffffffff00ff00ff00ff00

def s187 := certify 238 5 ([w12,w72,i3,i6,i1,i2]) cs238 [] (u238 5 60 0xab3152605c5813cf24200110c04a988b300e2a00e38448be5f3a8861d4c6bb8e6025815815405400c318752388b8c04684)

def s188 := certify 238 6 ([w72,i7,i3,i6,i1,i2,i5]) cs238 [s187] (u238 3 81 0x4c27a2514d03e1f09a2af153842d169154aa2faee4098110c12b88bc0158ac06e37a1797cbe41a18a0c53231ae1d0e85e86283141690b485602b066c20c05e02e1b)

def s189 := certify 238 5 ([w14,w65,w63,i1,i2,i5]) cs238 [] (u238 3 60 0x10623144188c51309e81f0f84d085a2d22168b49578a9cee4098110c00562b00158ac12b88bc88fc28d9b23b558d7)

def s190 := certify 238 6 ([w65,i7,w63,i6,i1,i2,i5]) cs238 [s189] (u238 4 78 0x8c279083118909a11908311893de91156c54b042d1689b7a61e842d1689ce2480221812ac45b002b158183a6ce802b1580ccd14d88631afab6a3a8b208aa)

def s191 := certify 238 6 ([w14,i7,w63,i3,i1,i2,i5]) cs238 [s189] (u238 3 78 0x83118a2064968984f40f87c26842d16910b45a44191992af1539dc8130221800ac56002b15800651a095c45e0c50628178ad94e3231ae192086546cd85ba)

def w73 : Sig := 0xffffffffffffffff0000000000000000

def s192 := certify 238 6 ([w73,i7,w63,i3,i1,i2,i5]) cs238 [] (u238 5 75 0x986020854423cf242056581056581154ab71471c22400443000aaa000aaa036d8abb013011668a68a2f97da28c109e218ab5498625516610618d7198)

def s193 := certify 238 6 ([w12,i7,w63,i3,i6,i1,i2]) cs238 [s187] (u238 3 74 0xabc54e10b45a442d1691224ee41f0f84d00886095c45e00ac56002b15801a4e61dc8136c1192f3109e990d70b88c9623818a0c50465311914628314a)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s194 := certify 238 7 ([w63,i3,i6,i1,i2,i5,i7]) cs238 [s186,s188,s190,s191,s192,s193] (u238 5 231 0x742085214aea0311420920821931924c4f304110a20851c3042e18144412e08aa56455bb2b8a08a49078409e4824844049584ab310325682a4c08c7f84111658ffb2c20209fe10459b2c7fd96164208a036ba0d8a80ab80b8480e4803840044a048ca00013fc232bfc8610004a404a9941929a11660061ac0008aaa35d55100015d00030d55576aa8c2000c18614dd2985ab0518564cb6334434516ca693ad14415811809e0987980840861e4c2d90416cb6d77e9e56688ad147d29a29b45114a)

def w74 : Sig := 0xffffffffffffffffffffffffffffffff00ff00ff00ff00ff0000000000000000

def s195 := certify 238 6 ([w74,i7,i3,i6,i1,i2,i5]) cs238 [s185] (u238 4 81 0x4613c84c12c841389c9ef488ab62a5822692442c0cc428404e71240110c095622d80238fc00c23400148a40c20e1863105857219c94a32d5fc5b053b210a)

def w75 : Sig := 0xff00ff00ff00ff000000000000000000ff00ff00ff00ff0000000000000000

def s196 := certify 238 5 ([w14,w67,w75,i1,i2,i5]) cs238 [] (u238 4 54 0x167453d3de911a3450d1ce2480221813744cd104479202809005e8111fc20d8212c9816545802340a)

def s197 := certify 238 6 ([w67,i7,w75,i6,i1,i2,i5]) cs238 [s185,s196] (u238 4 78 0x167453d1d3c1cf3de911a3450d1f7c6af1ce2480221813744cd17fc73f29c3ed104479202809005e80c8e57f88b14d16240c83310cc421008416a5868a)

def s198 := certify 238 6 ([w14,i7,w75,i3,i1,i2,i5]) cs238 [s196] (u238 4 75 0x1304b21184f27bd22089a4910b03312ad8a9639c49004430008e3f00308d025588b615c867214f11fc528c2d89c8272405010a4029023041c28cca)

def s199 := certify 238 6 ([w12,i7,w75,i3,i6,i1,i2]) cs238 [] (u238 3 74 0x1578a9c22692489127720f87c268044304ae22f008e3f00349cc3b902782325e6213d02b8171c8e4464b2ba19d02241121480a41a096232588c4e8274a)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s200 := certify 238 7 ([w75,i3,i6,i1,i2,i5,i7]) cs238 [s195,s197,s198,s199] (u238 4 231 0xec84521543b5a88d44209484609d8251393d8420bc45550ccaa2f198bd4254a1e20bd21489024ac4ab64192b82a58263f442b0b49afd16926c2128037178846ea10a85e0179042e901c401242191940013f44657e90c4004a409560a592914a2d8064b400b0ac8f2d158fec00618c51e5584ee14c568fbc55b9ab6945b50c6c5724348318699c96216cb7461e585bb5b045c28f2ac14f0a22a84e5113910a413a144e42892059809fa283f6022c88526114825a014cb45203080b79731e5fe8)

def s201 := certify 238 6 ([w14,i6,w65,i3,i1,i2,i5]) cs238 [s189] (u238 4 78 0x831189082713909a1193de91042d168842d168850809b7a61e9ce24802218002b158002b1580029148183a6ce8624189111f8f94edab6a3aa568b7820e1466)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s202 := certify 238 7 ([w65,i3,i7,i1,i2,i5,i6]) cs238 [s190,s186,s201] (u238 4 231 0x314c6d10749d20907463314c63cb187d630f26309484309cde251393cc420ec84d21743b6288f44221484288c46285188c4a242184356406a68198264a1e20bd21489024444dbd0cf51119b0f42d41c42b0b45b07168b6c2141c422c8b45b07168b4b2211fc07130a4c7f14974c031042e901c4012421919400141c4658390c40043c0c1d08750f10b6740d4bc00b0ac572f158aec004bc00308ac572f158acc200664b6a659862d9985361ac618d86248690630d1892c4d11745bb58b65b8ec148a8)

def w76 : Sig := 0x3333333300330033333333330033003333333333000000003333333300000000

def s203 := certify 238 5 ([w76,w66,i3,i7,i2,i6]) cs238 [] (u238 4 57 0x6d12cc351a998dbd30f42269244c7721dd4a30dce6909372ddce4b895ce1b8edc03204c080800d1a7401f91c12)

def w77 : Sig := 0xfff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0

def w78 : Sig := 0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc

def s204 := certify 238 4 ([w77,w78,w66,i7,i6]) cs238 [] (u238 3 40 0xd3125b21bc9e89423467bb286621b6ab57b9266043f00a855a061d0ecc61ea8874)

def s205 := certify 238 5 ([w78,i2,w66,i3,i7,i6]) cs238 [s204] (u238 4 57 0x6d12cd4a30dce69057219c843793c84508c8b95c9999dd66f443414d0f5221c82330cc60e9b3a011c7e0738933)

def s206 := certify 238 5 ([w77,i2,w66,i7,i1,i6]) cs238 [s204] (u238 4 57 0x68492cc713174da184e7e12e712402494c00238fc043793c84508c867b994309d355ab224882a50d03e721282b9244)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s207 := certify 238 6 ([w66,i3,i7,i1,i2,i6]) cs238 [s203,s205,s206] (u238 4 180 0x2598da20e8964125e8c63086ac80d4d03304c8889b7a19ea223361e85a6f8848169353a2d24a042943c417a42912043f80e261498fe292e9806328002b188ca7d218800878183a10ea1e216ce81a3580081591cd62b1fa000214dd20388024ac72640e864518861a066d2384b81f3503d12d0818a0ae41e90623d339104129086139bc4a272798841d909a3da8766311e884)

def w79 : Sig := 0xffffffffffffffff00ff00ff00ff00ffffffffffffffffff0000000000000000

def s208 := certify 238 6 ([w79,i6,i3,i7,i1,i2,i5]) cs238 [s185] (u238 4 81 0x4d08c841389c841389c9ef488dbd30f422692442840428404e71240110c0c1d36740238fc00148a400148a4057219c9ce691614208253422d8d634652b1a)

def s209 := certify 238 6 ([w14,i6,w67,i3,i1,i2,i5]) cs238 [s196] (u238 4 75 0x104e2721342327bd22089a4910a10136f4c3d39c49004430008e3f000522903074d9d15c867214d08adf39a2de084b26043316008d058838c28d46)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s210 := certify 238 7 ([w67,i3,i7,i1,i2,i5,i6]) cs238 [s207,s208,s197,s209] (u238 4 231 0x114c6d1074b52090746309484309cde251393cc420ec84d21743b2288f442184356406a68198264a1e20bd21489024444dbd0cf51119b0f42d4144240b49b05169250211fc07130a4c7f14974c031042e901c401242191940014144658290c40043c0c1d08750f10b6740d1ac0040ac8e6b158fd000313b43228c430c5b30c505720f48311e99c88216cb7cd11745b420827920988a6209f482622990a5128910a422a14a6428906659198a0a219c146622c8842611082ca010d944203080b7a351160f6)

def w80 : Sig := 0x3333333333333333333333333333333333333333333333333333333300000000

def s211 := certify 238 5 ([w80,i7,i5,i6,i2,i3]) cs238 [] (u238 3 60 0x4da6d2a7149f2df97e37a28dc89a49289c4ce29563f21fa6a37908dece370c8df92e4fee1b88f807e4700219033204e213e0e178dd9237)

def s212 := certify 238 5 ([w43,i7,i5,i6,i1,i3]) cs238 [] (u238 5 60 0xd1d1efa455eb5bcfb2ae94aa011fe0227a2e7463bcf57a6a55b495742ab1a3da13de78ab13c11249a1004300233456e823c13c5155c255)

def s213 := certify 238 5 ([w44,i7,i5,i6,i1,i2]) cs238 [] (u238 4 60 0x68d14348ac562e577df1abc0088604dd133449a4caf175ff1cfca731459d09f474f047c112444d00fc0473510742111e5757123c)

def s214 := certify 238 6 ([w8,i7,i5,i6,i1,i2,i3]) cs238 [s211,s212,s213] (u238 1 75 0x106831285c128f7582522911d8253a090496e2692695a118234119c2338fb45908e3f08860815d8af0108c946853030b2d96191281c4a272793c76191188c0a0b)

def s215 := certify 238 5 ([w12,w9,i6,i1,i2,i3]) cs238 [] (u238 3 60 0x20d06250b8743a1ba226924895a1122a9545f40471f80110c0102bb01b8de85e5f2f93ea046391c91dc912073034b31d4ea8823a)

def s216 := certify 238 6 ([w9,i7,i5,i6,i1,i2,i3]) cs238 [s215] (u238 5 81 0x20d0722c423dd6438e345044d248412b5009008240aa55b8a008ff000044300040aec05780041b6c55c5f2f904a9262793e6e514ca2162160b20b2020020186908220931efa)

def s217 := certify 238 6 ([w12,i7,w10,i6,i1,i2,i3]) cs238 [s215] (u238 1 78 0x83418942e17048242e91488ec120947bac13134934ad08c33a19ce119c11a088471f8443040aec1080846488457842c0e753a92c4a271293c9e3b2988c46050289c8a0b)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s218 := certify 238 7 ([w10,i5,i6,i1,i2,i3,i7]) cs238 [s214,s216,s217] (u238 5 231 0x1a21c29671a59a2882a45906b1210721122c5658a24113788f42f8eb988210ab2c5b2084290416d65ae08aa56455bb2b8a08a69841116135a761248082698414882b5a6821204134d0426082698414c820d3cb22c84134c208b3964501b5d06c54055c05c6b00022a239aeaf880003280004d308cad321840010b00092840c2e85dc8001340af858004c0010b82085c1018400216000618206246594b129858b0548569ca23753745144ae93bd1531521e6428cd3144a24f769e44e88bd147d2ba29f45114a)

def w81 : Sig := 0xccccccccffffffffccccccccccccccccccccccccffffffffcccccccccccccccc

def s219 := certify 238 5 ([w12,i7,w81,i6,i2,i3]) cs238 [] (u238 2 57 0x994ca2cba391c88c1257867889a494b95c975169127741f0f84e175969f2e9be0960238fc04111b1740349cc03c1f0260b)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s220 := certify 238 6 ([w81,i5,i6,i2,i3,i7]) cs238 [s219] (u238 5 180 0xd10e14b38d2cd144148b59325d21328b21165d58bb8105713c130f0ce21025c1154ac8ab765714115ab08222c26d1ec24901045d09728b41725d40ba8b0916920f0813c904908808c176da52c4a61634928ba57420856a4ae8a711420920821755e6f915f2174410a036ba0d8a80ab80b88000f2a239157de00020000151c2428e8040005d00692818bb4176400012039200e100112812)

def w82 : Sig := 0xffffffffffffffffffffffffffffffff00000000ffffffff0000000000000000

def s221 := certify 238 5 ([w12,w82,i6,i1,i2,i3]) cs238 [] (u238 2 60 0x106831285c7239118f4af0cf11349292b42292242283e1f09c0471f8088602057601a4e601e0f813d8962537c12c05c11c)

def s222 := certify 238 6 ([w82,i7,i5,i6,i1,i2,i3]) cs238 [s221] (u238 4 81 0x8341896c57219c88c5903d4207a2269244256c05ef4882c0cc4284040238fc00110c0040aec0e71240c234001088402520e04a631044a43789484c14c843d89c8a)

def w83 : Sig := 0xffffffff000000000000000000000000ffffffff0000000000000000

def s223 := certify 238 6 ([w12,i7,w83,i6,i1,i2,i3]) cs238 [s221,s219] (u238 3 78 0x41a0c4a171c8e447057433a11349244ad0891224ee41f0f84d008e3f002218020576006939877204d96cb4f894de825481ec0f42241123681f41896232988c8a8274a)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s224 := certify 238 7 ([w83,i5,i6,i1,i2,i3,i7]) cs238 [s220,s222,s223] (u238 5 231 0xd10e14b38d2cd1441522c835890839089162b2d8105713c130f0ce21025c1154ac8ab765714114ed08222c26bb6c2490104ed08291056bb5042408249078409e482484404280dae8362a02ae02e3580011511cd757c400019400027684657690c2000918004942064742ee400012039200e1001128126246594b129858b05485742085144ae93b11420851289be43cc851104608ac14792983eb05114a20b647885f084291e16fc40b2804ed09076a01164291984c2048c03cc8ca60184028eb463cb4e6)

def w84 : Sig := 0xf3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f0f0f0f0f3f3f3f3f0f0f0f0

def s225 := certify 238 5 ([w84,i2,w12,i7,i3,i6]) cs238 [] (u238 3 54 0xc7525b25f84bc150ae30e47223849f2df86ed8d844d2491224ee413e09f045b1b007e4700399a4027c13e)

def w85 : Sig := 0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0

def w86 : Sig := 0x303030303030303030303030303030303030303000000000303030300000000

def s226 := certify 238 4 ([w85,w86,w12,i3,i6]) cs238 [] (u238 4 37 0x977095c351a9994a30c9372ddc391c88e003204c01f91c0c304040f390ee)

def s227 := certify 238 4 ([w77,w86,w12,i7,i6]) cs238 [] (u238 5 34 0x18ea4b192e74876c00c81180399a409c81f04069a0cb71c4483c721ce)

def s228 := certify 238 5 ([w86,i2,w12,i7,i3,i6]) cs238 [s226,s227] (u238 5 51 0x31d496325ce90e514306e38888499cb73b6d3418c4083ea08445389e390e7003204603e238001ccd204e42)

def s229 := certify 238 4 ([w77,w85,w68,w12,i6]) cs238 [] (u238 3 37 0x12fc25e7bb32841902c130399a4007e4701bf33782a1563ba4f99bc44498)

def s230 := certify 238 5 ([w85,i2,w68,w12,i3,i6]) cs238 [s229,s226] (u238 3 54 0x25f84bd8cd8150ae324f96fc391c88e01902c03f23804c0fa7700399a41b1b0ef053866f337886fccde)

def w87 : Sig := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000000000000000000

def s231 := certify 238 5 ([w87,i2,w68,w12,i3,i6]) cs238 [] (u238 3 51 0x12fc25e0a8571927cb7e0640b00fc8e013008900d46ad844d24931f90fc75625b0e4722381b9cc0d2077)

def s232 := certify 238 5 ([w77,i2,w68,w12,i7,i6]) cs238 [s229,s227] (u238 3 51 0xc7525b25f84bc370640b01ccd201303e924007e47067bb284936f299259bccde20a85582e391c88e127ccde)

def w88 : Sig := 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00

def s233 := certify 238 5 ([w88,i2,w68,w12,i7,i6]) cs238 [] (u238 3 51 0x18ea4b64bf09786e0c8160399a4026011201a8d5b091277263f21f82a15c61c8e447093e5bf0fc08e049)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s234 := certify 238 6 ([w68,w12,i7,i2,i3,i6]) cs238 [s225,s228,s230,s231,s232,s233] (u238 3 162 0x12d9846413a92c824b11b32bd92fc25e578944bcdd8170ab405723182ec2381c92c2e391185c464b8877c24f87bcef1eadfa39886b8111ab045b0b2024502d26b745a498225a9108c66894e8ccee2322668458fc5ccd243f047a4b251b89401852c2514a058187a0102b1f8f45647800200089f4224532088008c024a213988c426936801b4da13)

def w89 : Sig := 0x3333333333333333333333333333333333333333330033003333333333003300

def s235 := certify 238 5 ([w89,i3,w12,i7,i2,i6]) cs238 [] (u238 3 57 0x63a92d92fc4fe1a8d5b091277263f21f889a4921ba6d378c391c88d7a93e33f63630044800e669009f3bf807e470)

def w90 : Sig := 0xffffffffffffffffffffffffffffffffffffffffff00ff00ffffffffff00ff00

def s236 := certify 238 6 ([w90,i3,w12,i7,i1,i2,i6]) cs238 [s235] (u238 3 71 0x18ea4b66b893d9b3186a356c2449dca7b3d9d8c489a4920891044e2c5d60221801a4e60ef778c6760471f814c00da1b42a63630e472231e8c47a678)

def w91 : Sig := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000ff00ff00000000

def s237 := certify 238 6 ([w91,i3,w12,i7,i1,i2,i6]) cs238 [] (u238 2 74 0x31d497b5c49f86a35c0d4893ba9ecf6763142d16a38e2ee088601a4e61deef18cec0ac56036150a83708c96230495c620920e20e42d42d02b02b2588c962383d)

def w92 : Sig := 0xffffffffffffffff0000000000000000ffffffff000000000000000000000000

def s238 := certify 238 6 ([w92,i6,w12,i7,i1,i2,i3]) cs238 [] (u238 3 74 0xe4722382ba19d02a15c681e8f6089a4922449dc83e1f09a0d46ad8573b99011c7e0044300349cc3b90267162eb00a45214c2325b3213c96232588c4e25)

def s239 := certify 238 5 ([w80,i6,w12,i7,i2,i3]) cs238 [] (u238 3 57 0x723911c24f96fc9b4da54e244d2491224ee4c7e43f44e26714a8dce275259c52fc4fe01f91c00864007334804f839990271)

def w93 : Sig := 0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcf0f0f0f0fcfcfcfcf0f0f0f0

def s240 := certify 238 4 ([w93,w8,i6,i7,i3]) cs238 [] (u238 3 34 0x1c8e4470a75393c2f7b43de50f213a9d4324f60238fc00d27300bbdd43b90f39)

def w94 : Sig := 0xcccccccccccccccccccccccccccccccccccccccc00000000cccccccc00000000

def s241 := certify 238 5 ([w94,w8,i6,i7,i2,i3]) cs238 [s240] (u238 1 51 0x7239118254ea72785e2e13be84e2692691277abbebe0f87c2739179d4ea192781c238fc22981a4e6081ba80f)

def s242 := certify 238 5 ([w43,i6,w12,i7,i1,i3]) cs238 [] (u238 5 57 0x1c71111157ad6f34747be8011fe000349cc063bcf57a27a2e742ae87525e9a3c4f782249342008600411dd12108f04f19a2b74)

def s243 := certify 238 5 ([w44,i6,w12,i7,i1,i2]) cs238 [] (u238 4 57 0x2449dc5158ac5caed1a28680110c00349cc0934995e2e9ba2669ca1d4974a2cc9f4112444d00fc047408c72392111e57351074)

def s244 := certify 238 6 ([w8,i6,w12,i7,i1,i2,i3]) cs238 [s215,s239,s241,s242,s243] (u238 1 71 0x723911824128f7582506831285dba0904b7e269269127782341195a1196b46308e3f0886069398af04e8815d87d036864a6053a9d49625138949e07)

def w95 : Sig := 0xccccccccccccccccccccccccccccccccccccccccffffffffcccccccccccccccc

def s245 := certify 238 5 ([w95,i6,w12,i7,i2,i3]) cs238 [] (u238 2 57 0x391c88c12578678994ca2cba89a4949127741f0f84e2e5725d4582cba7525974df04b011c7e020880693980783e04f62e8)

def w96 : Sig := 0xffffffff0000000000000000

def s246 := certify 238 6 ([w96,i6,w12,i7,i1,i2,i3]) cs238 [s221,s245] (u238 4 71 0xe47223415c867220d0625b089a49109127717bd22095b01008e3f000443000d273039c490102bb028ea7525894de252207a81ec05011b407d014c4e6)

def s247 := certify 238 4 ([w93,w11,i6,i7,i3]) cs238 [] (u238 5 37 0xe388885143062f97d8190f7bbca1d0f21890e4f38e43a0011fe000349cc0d3418c)

def s248 := certify 238 5 ([w94,w11,i6,i7,i2,i3]) cs238 [s247] (u238 4 57 0x391c88d14a30c22692442449dc4351a9985f2fe0d28bdf65ef4a121788e44f73812011c7e0008a6001a4e604ba5d5e6)

def s249 := certify 238 6 ([w11,i6,w12,i7,i1,i2,i3]) cs238 [s248] (u238 4 74 0x723911a108f75a29461844d24884893b8a021406a353300471f8002218006939815e0014ce262e9b061192cc6f139ac8b205014002900a4464b1192c825)

def s250 := certify 238 5 ([w13,i6,i7,w12,i1,i2]) cs238 [] (u238 4 57 0x1ef48821c8cc4d1a28680110c0e712401c88409ba2669ca2cd4f4a0e497480a024017a04111e440e4963935114)

def s251 := certify 238 6 ([w14,i6,i7,w12,i1,i2,i3]) cs238 [s250] (u238 4 74 0xae4339104bb22c8458a68437c44d248bde91044b198850808508080471f80022181ce24804b108002914800291480827139302313904e4259048a6)

def s252 := certify 238 6 ([w73,i6,i7,w12,i1,i2,i3]) cs238 [] (u238 4 74 0xae43390723911a2c845844d248bde9104893b88508080471f80022181ce24806939800291481427209c8752088d1645a0280852014804e41390966)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s253 := certify 238 7 ([w12,i7,i1,i2,i3,i6]) cs238 [s234,s236,s237,s193,s199,s238,s244,s246,s249,s251,s252] (u238 6 228 0x224a0c1aa68a074a8ca812a2220c1a9e9836ea6844812969924e80840c11ba30b146f8610516a3040c6f862c1a22210e1bf28b3862a22c89bf284084eb01159be11e04f8c1e666f84101310604d310c20d3106201b10c0433162040b10859331625923108040b162040b1226489c589976c488102c44881ec41011ec448112c410804d9f8070d819406d9f945cd818006d9a8000d821546d9a953ed820000c590000c40b102c593142c408000d9b0000d889068d9b1072d888000d81290ed84800ed810004d84b612a1ea80a)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s254 := certify 238 6 ([w68,i5,i7,i2,i3,i6]) cs238 [] (u238 5 180 0x302359f620ed8120d2761b63165062143083065866090bfd96d982b51762367790933bc39dfe2dce20e182d0c43419018c08cd8841116136ab61248082bf8535db2daff948760b666a0c7382399a121ce40e90e38657a5e457c831c77471db4976e8db16c71d20000d40d250811801bc00022afbca88e400004000855500aaa120001d0176d06dd40c9d80d8db02470071b4000e80e)

def s255 := certify 238 6 ([w68,w12,i5,i7,i2,i3,i6]) cs238 [] (u238 5 74 0x19969f18692419450c192291e8823cf0823cf08d3418c089a4908270e412010482010486d20d20dd49623801902301f11c0010080020648100004061)

def s256 := certify 238 6 ([w11,i6,i5,i7,i1,i2,i3]) cs238 [] (u238 4 81 0x91488ed0847bad14a30c22692442708cc5010a0351a9980238fc00110c0064a340af00042713174c3bc08c466f3789cc5f2fe0d64590280a00148052a50ef0421144e25)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s257 := certify 238 7 ([w12,i5,i7,i1,i2,i3,i6]) cs238 [s217,s223,s254,s255,s214,s256] (u238 5 231 0x4f8c3744165a7c829fe861a0230c799246ec921e4618c59418850c20c1961ba21229f5923d2dd27c820a2410dff3c42f9e1448210a4105bf3c42f9e16c82060b4310d0640630230c61044584d31d84920208c6105d64e131e5974104634103184118c208c6820634102c84118c208b28207f00e235031fe82e8c00c6b00022a239aeaf8800032800046308ca6321840006d000ea0649b6083a00036c101b4000da0006d82036ad53a6100036800184da613d944a90fb20c511a429c831446e88bd144a251289462789144)

def w97 : Sig := 0xffffffff00000000ffffffff00000000

def s258 := certify 238 5 ([w13,i6,i7,w97,i1,i2]) cs238 [] (u238 4 57 0xfbe3578d1a28680110c0bfe39f89ba2669ef488e71243959d14f42211e4a731480a024017a05731c35114)

def s259 := certify 238 6 ([w14,i6,i7,w97,i1,i2,i3]) cs238 [s258] (u238 4 74 0x118b22c8458a68449c44d248858198850808508080471f80022180184680029148002914808573393de911ce2489641389c841389c8ac105466)

def s260 := certify 238 6 ([w73,i6,i7,w97,i1,i2,i3]) cs238 [] (u238 4 74 0x39cd2ac845844d2488aa5517a8508080471f800221806e3750bc02914808573393de911ce2484641389c841389c85f20a91645a02808520148306)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s261 := certify 238 7 ([w97,i7,i1,i2,i3,i6]) cs238 [s259,s260] (u238 4 228 0x22e0c5f3ea8825f29e083822a8ca42b2d493991442b10c939ac642e91c93aadc42eada93a90a3d984353db20353d9a063db04c3d9ec423da05a4d3d9ec5a493da0423d8bc4553da866553d8bc662f3da84a529fc0715298526529fc525d529806529ac0052a05647529ac563f52a0003d994003d88f623d994f6433d880052a8037528bc423752a842a528bc02f288948428984e6f288944e4f289884288f48428a06257288f4626728a0843d889e3dc25e3d8a523dc08452824e528848e528084528865228944c623)

def w98 : Sig := 0xffffffffffffffff00000000ffffffffffffffffffffffff0000000000000000

def s262 := certify 238 6 ([w98,i6,i5,i7,i1,i2,i3]) cs238 [] (u238 4 81 0x91488ed057219c96422d0d4221a22692442708cc5ef48828404284040238fc00110c0064a340e71240148a400148a4049b8ec841389c841389c981de076652b03b)

def w99 : Sig := 0xffffffff00000000ffffffff00000000000000000000000000000000

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s263 := certify 238 7 ([w99,i5,i7,i1,i2,i3,i6]) cs238 [s262] (u238 3 231 0x4fb30ec82cb4f9053e3b66c0b855a02b918c1761dc2453e17488ec2e3b4fc40c60ae83d4188f4ce908c435c088d5822d858f122816935e22d24c113c488763370bc466331d9104c221f420f84c82681143f81c5852c7f14975818d60102b239ac563f800328013c48caf1219004fc00762164cfc42211d8020878261c808131084c4a88c27378944e4f644289466e3b228eca288413c90588ac412990588ac172d85e10b0174285e0b70332c8cc9e2433788cc8b24213088427e0219f8840c2051d9d114c663)

def w100 : Sig := 0xffffffffffffffffcccccccccccccccccccccccccccccccccccccccccccccccc

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s264 := certify 238 6 ([w100,i6,i7,i2,i3,i5]) cs238 [] (u238 3 180 0xed1288b43b2288e9104a88c27378944e4f644009f085381104213098c60ae83d4188f4ce9081b80ed05c3a1b0b86ea2b02e15680ae46305d85704703580acd63f080098443e841f09904d0228c522816935f22d24c110bc8ab4332a8bc662fa2a621ae0446ac116c2c8c9101941f26521810235adb445a46915474d4296603f9c4527f2e833500dc5e211bd08685e02f)

def w101 : Sig := 0xfffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s265 := certify 238 6 ([w101,i6,i7,i1,i3,i5]) cs238 [] (u238 3 180 0x7689445a1d9144748825446139bc4a2727b221207c22130f904c26114418c15d07a8311e99d2103701da0b87436170dd45605c2ad015c8c60bb0b609a4c5216be492504821e098720204c4213358040ac8e6b158fe002806e2f108de84342f0179fc0e2c2963f8a4bac0c650028c9195f24320022b351168f24551d3504706a4c3508b31660bc8ab4332a8bc662fa2a)

def w102 : Sig := 0xffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s266 := certify 238 6 ([w102,i6,i7,i1,i2,i5]) cs238 [] (u238 3 180 0x7689445a1d9144748825446139bc4a2727b220f512062571e8c4cf088130887d083e13209a04505e455a199545e3317d15310d702235608b6163148a05a4d7c8b493044821e098720204c4213328014648caf921900500dc5e211bd08685e02f3f81c5852c7f14975818d60102b239ac563f80022b351168f24551d35430542f8158cc0bb306e03b4170e86c2e1ba8a)

def w103 : Sig := 0xffffffffffffffffffffffff00000000ffffffff00000000ffffffff00000000

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s267 := certify 238 6 ([w103,i6,i7,i1,i2,i3]) cs238 [] (u238 3 180 0x3701da0b87436170dd45605c2ad015c8c60bb0c60ae83d4188f4ce908c522816935f22d24c110bc8ab4332a8bc662fa2a621ae0446ac116c2c098443e841f09904d02286b0081591cd62b1fc0019400a324657c90c802806e2f108de84342f0179fc0e2c2963f8a4bac0c821e098720204c421325b3560e8978351d3509d8de8254138949e8c83b44a3dd0ecc623a44)

def s268 := certify 238 6 ([w103,i5,i6,i7,i1,i2,i3]) cs238 [] (u238 5 81 0xe38d14a2860c479e10479e101134921154ab715a68318804120804120011fe000088606db1571c462e8d000041000040314a32869241ba2ba2a41a4184e8ae8a)

def w104 : Sig := 0xffffffffffffffff000000000000000000000000000000000000000000000000

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s269 := certify 238 7 ([w104,i6,i7,i1,i2,i3,i5]) cs238 [s264,s265,s266,s267,s268] (u238 3 231 0x1da251168764511d220951184e6f1289c9ec88454428914a2dd22ad4a2883182ba0f50623d33a4206e03b4170e86c2e1ba8ac0b855a02b918c17622c416c8a5b629153a5b88098443e841f09904d0228f322816935e62d24c110bc8ab4332a8bc662fa2a621ae0446ac116c2c7991165e65979914fa5922410f04c390102621099ac0205647358ac7f00065002799195e643200a01b8bc4237a10d0bc05e7f038b0a58fe292eb0355c00c35730d5c8a5330801159a88b47922a8c8ae50c915c641)

def w105 : Sig := 0xfff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0f0f0f0f0f0f0f0f0

def s270 := certify 238 5 ([w105,w14,i6,i7,i1,i5]) cs238 [] (u238 4 53 0x4c12c841389c841389c8e71240c23400148a400148a400110c0ac105466f7a441606621420214202)

def w106 : Sig := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000000000000000000

def s271 := certify 238 6 ([w106,w14,i6,i7,i1,i2,i5]) cs238 [s185,s270] (u238 4 74 0x98259082713908271393de9105819885080850808483e89ce2480221801846800291480029148008da815820a8cc823ac88c5916422c53)

def s272 := certify 238 5 ([w58,i2,i6,i7,i1,i5]) cs238 [] (u238 4 57 0xe9e0e78b3a29e8e7124bfe39f89ba26680810c0042f414e629224882fe0bf86a1a82912445705fc350d4)

def w107 : Sig := 0xf000f000f000f000f000f000f000f000f000f000f000f0000000000000000

def s273 := certify 238 4 ([w78,w107,i6,i7,i5]) cs238 [] (u238 4 40 0x74f073c59d14f4a73144111e45731cb5114402007388212a956d3c1a8d5734)

def s274 := certify 238 5 ([w107,i2,i6,i7,i1,i5]) cs238 [s273] (u238 4 57 0xe9e0e78b3a29e8e7124bfe39f89ba26680114c14e629ef488552a8bf8351a9a88223c8802f40ae6396a2290)

def s275 := certify 238 5 ([w78,i2,w13,i6,i7,i5]) cs238 [s273] (u238 4 57 0xe9e0e78b3a29e94e6288223c8ae6386a22882990d0802f40f5221c9bbe4c79b9a6de827388215ff1cfc4dd1334)

def w108 : Sig := 0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c

def s276 := certify 238 5 ([w108,i2,w13,i6,i7,i5]) cs238 [] (u238 4 57 0xe9e0e78b3a29e94e6288223c8ae6386a22901404802f41ef488fbe3578d1a2868e7124bfe39f89ba266843)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s277 := certify 238 6 ([w13,i6,i7,i1,i2,i5]) cs238 [s272,s274,s275,s276,s250,s258] (u238 4 180 0x4891d3c80f122dd1cf09c419167413d1062753d094943c417a42912048489f7c19f212336af05cc489a3485313050d0542085d2038802484323280025a88ca9d218800c3817fc10f30e2173f01cc28137414d30a294cd014c529c20f3041c729413a1041e904e3d479104822023e8a0538090214a1003580526b5e8100c215cb7316c711c20d8d4450828452d4)

def s278 := certify 238 6 ([w13,w14,i6,i7,i1,i2,i5]) cs238 [] (u238 4 74 0x98259082713908271393de9105819885080850809ce248022180184680029148002914839820a8e88223c901404802f408b6116422c5b)

def s279 := certify 238 6 ([w13,i3,i6,i7,i1,i2,i5]) cs238 [] (u238 4 81 0x4d08c84613c9ef488dbd30f4ab62a582269244e71240110c0c1d367495622d80238fc0cd61857219c9ce6b14a308227209c9014042900a40a56346310588)

def w109 : Sig := 0xffffffff00000000ffffffff00000000ffffffff0000000000000000

def s280 := certify 238 6 ([w109,i5,i6,i7,i1,i2,i3]) cs238 [] (u238 4 81 0x91488ed08341896c57219c822692442708cc4256c05ef4880238fc00110c0064a340040aec0e7124cb65e04a49b8ec8437894881ea07b014042100840a56076631044a27)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s281 := certify 238 7 ([w14,i6,i7,i1,i2,i3,i5]) cs238 [s271,s186,s277,s278,s279,s191,s198,s201,s209,s214,s280,s251,s259] (u238 4 231 0x27c84c63709fc592f0422c4842089c4eb11389c824254c842889c4f511389ca2420c505720f48311e99c88253d08c5b14db5b08452ed620a1101420836b3756a9d2da107d420b6532dca1e20bd214890233c4240b49acf1692502133c42c0cf0cf198cf02133c4220c20cf840822133c422cc20cf840b2211042e901c401242191ac0040ac8e6b158fd00019400133c4656790c40046c00c08711b10a3700050400208a45341148a4820050400308a45341148a4c20038cf2ac11707920904f24551b948a6)

def w110 : Sig := 0xff00ff00ff00ff00ff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00

def s282 := certify 238 6 ([w110,i3,i6,i7,i1,i2,i5]) cs238 [] (u238 3 81 0x2508d1309e81f0f84d0aa5517d2af153842d16910b45a5dc813022180dc6f42f4ae22f00562b00158ac0be5f20d0c506281ba0dd64635c2e31418a06e8374cd841)

def w111 : Sig := 0xffffffff00000000ffffffff00000000ffffffffffffffffffffffff00000000

def s283 := certify 238 6 ([w111,i5,i6,i7,i1,i2,i3]) cs238 [] (u238 5 81 0x1c71a290683916211eeb2162085822692422a956e28256a012010486410590047f800022181b6c55c02057602bc00208000202f97d3e574574549313c9e27457450c34841)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s284 := certify 238 7 ([w73,i6,i7,i1,i2,i3,i5]) cs238 [s282,s283,s192,s252,s260] (u238 4 231 0xec84537543b5a88d4422c4842089c4eb11389c82420c505720f48311e99c882691c55b9ab694851e6d620a109d420836b4a1e20bd214890238c4240b49ae3169250210bc45550ccaa2f198bd42538c4220c20e384082211042e901c401242191ac0040ac8e6b158fd00019400138c4657190c40028037178846ea10a85e017d0c00208a45343148a482001e48a5f3c90482a22a84e511390f24139f44e4289105b458f36414d162dda059809c62838e022c885261148286014d0c5203080f2cfc115e66)

def w112 : Sig := 0x3333333300000000333333333333333333333333000000003333333300000000

def s285 := certify 238 5 ([w112,w69,i6,i7,i2,i3]) cs238 [] (u238 3 57 0x391c88e02a15c649f2df889a4922449dc86a356c63f21f8be5f0cb70dc47dc9712f00fc8e00112000c9a401902c13)

def s286 := certify 238 4 ([w85,w78,w69,i6,i3]) cs238 [] (u238 3 40 0x2a15c62ba19d0723911c17cbed886f27a23d50e80471f8363567b918604430)

def s287 := certify 238 4 ([w77,w78,w69,i6,i7]) cs238 [] (u238 3 40 0x2f97c32c9423443793d00d28d067bb287b9266043f01c8e4470150ab05dea8874)

def s288 := certify 238 5 ([w78,i2,w69,i6,i7,i3]) cs238 [s286,s287] (u238 3 57 0x1c8e4470150ae315d0ce85f2f86592846886f27a10e0fb0431194c46b95cb63d510e840471f801a51a0d8d9dc933)

def s289 := certify 238 4 ([w77,w85,w69,i6,i1]) cs238 [] (u238 2 40 0xe38bb81e0f8130694680471f82f97f2861bc9f202c2702a15d592bc09c489209)

def s290 := certify 238 5 ([w85,i2,w69,i6,i1,i3]) cs238 [s289,s286] (u238 3 57 0x2a15c62ba19d0723911c011c7e07162eb77204c0ee7d0034a340be5f6c43793d12826877829c3635642681342)

def s291 := certify 238 5 ([w77,i2,w69,i6,i7,i1]) cs238 [s289,s287] (u238 4 57 0x34a340713174ce71240249f400238fc05f2fe0c4508c843793c849b794c9267b99432248821c8e4468a50d62b9244)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s292 := certify 238 6 ([w69,i6,i7,i1,i2,i3]) cs238 [s285,s288,s290,s291] (u238 4 180 0x11a0738b0e447611e10865a864518861ac618a0ae41e90623d339104628848169356a2d24a042228842319a253a333b88c423086ac80d4d03304c943c417a42912043580081591cd62b1fa0003280028c88ca7d2188008d80023109a636214688c003f80e261498fe292e9806214dd20388024a332c18be23c797f18fc08cc61190983da8466311e084129086139bc4a27279884)

def s293 := certify 238 5 ([w112,i5,i6,i7,i2,i3]) cs238 [] (u238 5 60 0x5fed45d9450c192672dce089a490a6bb4876d3418c639c8738bfb52763b688e392f21c07c4700040202ed993b003204648e00e)

def s294 := certify 238 6 ([w69,i5,i6,i7,i1,i2,i3]) cs238 [s293] (u238 5 81 0x24523d10a2860c479e10479e10113492104e1c82d3418c402090402090008ff000044300064a340388c5d1a000080a6000612f97d81ba6228a41a418428ae98906906)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s295 := certify 238 7 ([w70,i6,i7,i1,i2,i3,i5]) cs238 [s292,s294] (u238 4 231 0x27c84c11709f2292f04209484309cde251393cc420c505720f48311e99c88211508c5b0c5b5b08432d43228c430d634a1e20bd21489023944240b49ae51692502139442c0cf0e5198cf021184356406a68198261042e901c401242191ac0040ac8e6b158fd0001940013944657290c40046c00c08711b10a370001fc07130a4c7f14974c031e48a5fc1170453188a5128908a4229f4a642892c5bb208a8b316c82da066591989ca219b946622c884261108322010e4442030808af351159e41)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s296 := certify 238 8 (roots 238) cs238 [s194,s200,s202,s210,s218,s224,s253,s257,s261,s263,s269,s281,s284,s295] (u238 4 240 0xdee0c5fc6a8825fc5e0838a9a8caa88ec8428aa9eaa68ee962328a884808948428984e6f6e8944e4f2898845ae91c2daadc4eeada2da90a3eb2d42d991429b10c2d9ac6288c50572d907a4428c47a672891042c8bc4552ca866552c8bc662f2ca84a2c984352cb20352c9a062cb04c2cca1e2c905e2cc8522c92042c964422ca05a4d2c9645a492ca04230a8037308bc423730a842a308bc02f309fc0713098526309fc525d309806309042e30c80e30900430c8432309ac0030a05647309ac563f30a0002c994002c88b222c994b2432c8800)

theorem lower238 : Claim 238 9 := fromSearch 303064400 (by decide +kernel) s296.property

theorem lower254 : Claim 254 10 := fromLift 10 16 303129920 lower238 (by decide +kernel)

theorem lower203 : Claim 203 6 := fromLift 6 1 24694 lower202 (by decide +kernel)

theorem lower195 : Claim 195 5 := fromLift 5 2 118 lower193 (by decide +kernel)

theorem lower227 : Claim 227 6 := fromLift 6 2 85 lower225 (by decide +kernel)

theorem lower107 : Claim 107 5 := fromLift 5 2 24661 lower105 (by decide +kernel)

theorem lower171 : Claim 171 5 := fromLift 5 1 28757 lower170 (by decide +kernel)

def cs99 : Cuts (goalAt 99) := []

def dict99 : Nat := 0x890843011040c2220105082200104002100088082120104042101

def d99 := unpackCases dict99 4

def u99 := unpackShort dict99 4

def s297 := certify 99 3 (roots 99) cs99 [] (d99 24 0x1b0a1916630551244032872)

theorem lower99 : Claim 99 4 := fromSearch 85 (by decide +kernel) s297.property

def c235_0 := ruleFor 235 lower233 none (by decide +kernel)

def c235_1 := ruleFor 235 lower234 none (by decide +kernel)

def c235_2 := ruleFor 235 lower203 none (by decide +kernel)

def c235_3 := ruleFor 235 lower195 none (by decide +kernel)

def c235_4 := ruleFor 235 lower227 none (by decide +kernel)

def c235_5 := ruleFor 235 lower107 none (by decide +kernel)

def c235_6 := ruleFor 235 lower171 none (by decide +kernel)

def c235_7 := ruleFor 235 lower233 (some (3,i3,i6)) (by decide +kernel)

def c235_8 := ruleFor 235 lower233 (some (2,i3,i6)) (by decide +kernel)

def c235_9 := ruleFor 235 lower234 (some (1,i3,i6)) (by decide +kernel)

def c235_10 := ruleFor 235 lower233 (some (1,i3,i6)) (by decide +kernel)

def c235_11 := ruleFor 235 lower233 (some (0,i3,i6)) (by decide +kernel)

def c235_12 := ruleFor 235 lower234 (some (3,i3,i6)) (by decide +kernel)

def c235_13 := ruleFor 235 lower233 (some (3,i3,i7)) (by decide +kernel)

def c235_14 := ruleFor 235 lower233 (some (2,i3,i7)) (by decide +kernel)

def c235_15 := ruleFor 235 lower234 (some (1,i3,i7)) (by decide +kernel)

def c235_16 := ruleFor 235 lower233 (some (1,i3,i7)) (by decide +kernel)

def c235_17 := ruleFor 235 lower99 none (by decide +kernel)

def c235_18 := ruleFor 235 lower233 (some (0,i3,i7)) (by decide +kernel)

def c235_19 := ruleFor 235 lower234 (some (3,i3,i7)) (by decide +kernel)

def c235_20 := ruleFor 235 lower233 (some (1,i5,i7)) (by decide +kernel)

def c235_21 := ruleFor 235 lower233 (some (2,i5,i7)) (by decide +kernel)

def c235_22 := ruleFor 235 lower200 none (by decide +kernel)

def c235_23 := ruleFor 235 lower227 (some (1,i5,i7)) (by decide +kernel)

def c235_24 := ruleFor 235 lower225 (some (1,i5,i7)) (by decide +kernel)

def c235_25 := ruleFor 235 lower233 (some (3,i5,i6)) (by decide +kernel)

def c235_26 := ruleFor 235 lower233 (some (1,i5,i6)) (by decide +kernel)

def c235_27 := ruleFor 235 lower233 (some (2,i5,i6)) (by decide +kernel)

def c235_28 := ruleFor 235 lower234 (some (1,i5,i6)) (by decide +kernel)

def c235_29 := ruleFor 235 lower233 (some (0,i5,i6)) (by decide +kernel)

def c235_30 := ruleFor 235 lower234 (some (3,i5,i6)) (by decide +kernel)

def c235_31 := ruleFor 235 lower203 (some (1,i1,i6)) (by decide +kernel)

def c235_32 := ruleFor 235 lower202 (some (1,i1,i6)) (by decide +kernel)

def c235_33 := ruleFor 235 lower195 (some (1,i1,i6)) (by decide +kernel)

def c235_34 := ruleFor 235 lower234 (some (1,i5,i7)) (by decide +kernel)

def c235_35 := ruleFor 235 lower203 (some (3,i1,i7)) (by decide +kernel)

def c235_36 := ruleFor 235 lower202 (some (0,i1,i7)) (by decide +kernel)

def c235_37 := ruleFor 235 lower233 (some (3,i5,i7)) (by decide +kernel)

def c235_38 := ruleFor 235 lower202 (some (3,i1,i7)) (by decide +kernel)

def c235_39 := ruleFor 235 lower195 (some (3,i1,i7)) (by decide +kernel)

def c235_40 := ruleFor 235 lower234 (some (2,i5,i7)) (by decide +kernel)

def c235_41 := ruleFor 235 lower227 (some (2,i5,i7)) (by decide +kernel)

def c235_42 := ruleFor 235 lower233 (some (0,i5,i7)) (by decide +kernel)

def c235_43 := ruleFor 235 lower234 (some (3,i5,i7)) (by decide +kernel)

def c235_44 := ruleFor 235 lower233 (some (2,i6,i7)) (by decide +kernel)

def c235_45 := ruleFor 235 lower233 (some (3,i6,i7)) (by decide +kernel)

def c235_46 := ruleFor 235 lower170 none (by decide +kernel)

def c235_47 := ruleFor 235 lower105 none (by decide +kernel)

def c235_48 := ruleFor 235 lower234 (some (0,i6,i7)) (by decide +kernel)

def c235_49 := ruleFor 235 lower233 (some (0,i6,i7)) (by decide +kernel)

def c235_50 := ruleFor 235 lower234 (some (1,i6,i7)) (by decide +kernel)

def c235_51 := ruleFor 235 lower233 (some (1,i6,i7)) (by decide +kernel)

def c235_52 := ruleFor 235 lower234 (some (2,i6,i7)) (by decide +kernel)

def c235_53 := ruleFor 235 lower234 (some (3,i6,i7)) (by decide +kernel)

def cs235 : Cuts (goalAt 235) := [c235_0,c235_1,c235_2,c235_3,c235_4,c235_5,c235_6,c235_7,c235_8,c235_9,c235_10,c235_11,c235_12,c235_13,c235_14,c235_15,c235_16,c235_17,c235_18,c235_19,c235_20,c235_21,c235_22,c235_23,c235_24,c235_25,c235_26,c235_27,c235_28,c235_29,c235_30,c235_31,c235_32,c235_33,c235_34,c235_35,c235_36,c235_37,c235_38,c235_39,c235_40,c235_41,c235_42,c235_43,c235_44,c235_45,c235_46,c235_47,c235_48,c235_49,c235_50,c235_51,c235_52,c235_53]

def dict235 : Nat := 0x800344842400a9002708901001d40084c0024007d001b204208102400488b012240d000e4002c498040020e08080032000b228084a0230280c24020c0441200850061601a020812830800210840060c8803210088403000500268002a00098002200078001900202090082080a4202a0a40090a1010a808820120c010016400344a0a40028490912405002d400a500234004d000f400310009122008109309090031400c1002f40094290010c008a0a40040a8a04001d0035400d10033400b1002b4007900192a202000522401002e0840841082200900320a821001c40068486022424880a2a000a1204005c410280010890810424880118404490008c04e020288802300400448a08220248a001290022600882089018000c6800382806240184804908120244820088048242120044802381820002128010028188004a080a800a8201a100c0421202900152048100031a080622010c0e000108a010006300810022086004301208804a4210d0900013000021091040d00044005100000a4048100800010002120a02920301802a20088a021284001441423020068602a0a088202080041002060082020a4242a280a4a06260189086828220a0828022000210022020c040222002202120004140088004808204044840104042101088802120

def d235 := unpackCases dict235 8

def u235 := unpackShort dict235 8

def s298 := certify 235 5 ([w13,i7,i6,i0,i1,i5]) cs235 [] (u235 4 60 0x58c94b26ff873e73a844bc93b25ef9dfee709400882066c93f27bf9a3e97b12411164409762802003491257b1e)

def s299 := certify 235 6 ([w71,i7,i3,i6,i0,i1,i5]) cs235 [s298] (u235 4 75 0x1184f2134232105e2f239d422458876085a2d13074e1d085a2d17384a0044102a58a7600562b03574bfd00562b033586185e4179188634f58d484a6a)

def s300 := certify 235 5 ([w12,w72,i3,i6,i0,i1]) cs235 [] (u235 5 60 0x91310e605c5811c728200110405498a7300e2a01c70450c663398861ccc69bcf5c25815815405400c318732388b8b84684)

def s301 := certify 235 6 ([w72,i7,i3,i6,i0,i1,i5]) cs235 [s300] (u235 5 81 0x4309e208514c438e504489887302b2c0b6db029c704500088202a4c5398055500552a95818cc7f15709708610634de7962ae12e12c0ac0aa02a00618cf8858859a)

def s302 := certify 235 5 ([w14,w65,w63,i0,i1,i5]) cs235 [] (u235 3 60 0x105e2f44178bd1309e9dc1542168b4885a2d248e21f03a1d40a8110400562b00158ac1538a7c891c2859b243558d3)

def s303 := certify 235 6 ([w65,i7,w63,i6,i0,i1,i5]) cs235 [s302] (u235 4 78 0x8c279082f17909a119082f1791cea1122c43b042d168983a70e842d168b9c25002208152c53b002b1581aba5fe802b1580ccd14d88631a7ab6a428b2086a)

def s304 := certify 235 6 ([w14,i7,w63,i3,i0,i1,i5]) cs235 [s302] (u235 3 78 0x82f17a2064968984f4ee0aa10b45a442d169106512491c43e0743a8150220800ac56002b1580064660a9c53e0bd05e8178b094e3231a6191f86542cd85da)

def s305 := certify 235 6 ([w73,i7,w63,i3,i0,i1,i5]) cs235 [] (u235 5 75 0x975c20854421c72820565810565816db60538e08a001104002aa8002aa802a954ac2e12e11668a68a3198da28c109e21891439862a54e610618d3198)

def s306 := certify 235 6 ([w12,i7,w63,i3,i6,i0,i1]) cs235 [s300] (u235 3 74 0x91c43e10b45a442d16911acee5dc154022082a714f802b15800ac5600833780743a8156c1192f3109e990d30b88c9623817a0bd046531190c5e82f4a)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s307 := certify 235 7 ([w63,i3,i6,i0,i1,i5,i7]) cs235 [s299,s301,s303,s304,s305,s306] (u235 5 231 0x742085204ae9f311420920821931924c4f304110220851bae40dd714441300b62a0db083028229480e10239409412012721244ca0c9cd08730230d210445961a6cb080829b841166cb26f658590822802ae19154ac8ac00c0441c500704004510526e000119c29299c8210004d40549881935414e60064940008aaa92d55100012500032d55496aa8ca000c18614d729859b0518561cba3344345174a6932d14415711709e0977970840861d4c2e904174bad3859d566886d147929a29b4510ca)

def s308 := certify 235 6 ([w74,i7,i3,i6,i0,i1,i5]) cs235 [s298] (u235 4 81 0x4613c84c12c841389c8e750891621d822491c42c22442148a45ce128011040a9629d802691400c0cc008400c1fe18630fd857218492932d63c5b053b210a)

def s309 := certify 235 5 ([w14,w67,w75,i0,i1,i5]) cs235 [] (u235 4 54 0x163252c9cea112f24ecb9c2500220819b24fc9044591025d8a00801123c20d8212c9812245806240a)

def s310 := certify 235 6 ([w67,i7,w75,i6,i0,i1,i5]) cs235 [s298,s309] (u235 4 78 0x163252c9bfe1cf9cea112f24ec97be77fb9c2500220819b24fc9efe68fa5e3cc9044591025d8a00800c8f58fc8b14d1623ec821108443300cc1695964a)

def s311 := certify 235 6 ([w14,i7,w75,i3,i0,i1,i5]) cs235 [s309] (u235 4 75 0x1304b21184f239d4208924710b089124588767384a004410009a4500303302a58a7615c861214f123c4a4c2e89c82720a44291401002303fc284ca)

def s312 := certify 235 6 ([w12,i7,w75,i3,i6,i0,i1]) cs235 [] (u235 3 74 0x123887c22491c88d6772ee0aa011041538a7c02691401066f00e87502b82325e6213d0278171c8e4464b2ba18505242920880441a096232588c4e8274a)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s313 := certify 235 7 ([w75,i3,i6,i0,i1,i5,i7]) cs235 [s308,s310,s311,s312] (u235 4 231 0xec84520543b5988d44209484609d8251393d8420c443750846e31108c54255042e209d415082124e449160a593914a1d82642c42b0b4930b1691ec2128055188ccaaa19a862018921ca038401290a42c00119c527339044004d40a9641935829d80649c00b0ac9b2715916c00618c51d5584ce14c568f3e55bdab6945d50bec57243482f86984962174bb261d585db5b043c28eaac14f0a21a84e51139102413a044e428905259148a16214c2c5222c8a0658024e0849e003280bb8b31d66e8)

def s314 := certify 235 6 ([w14,i6,w65,i3,i0,i1,i5]) cs235 [s302] (u235 5 78 0x25d70824d30823510871ca08159604159604151404c169c2d38e08a001104002aa8002aa800104006ab4bf6ae12e10891c8ca6b34b352128a68bac7cc2846)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s315 := certify 235 7 ([w65,i3,i7,i0,i1,i5,i6]) cs235 [s303,s299,s314] (u235 4 231 0x30cc6d0ff4991f8ff46330cc63ab1879630ea6309484309cc251393cc420ec84d20743b6188f44220484288bc5e81178bca2421ec46d30a4c7b1497cc235042e209d415082124444c1d08751110b8742d43c42b0b45b0f168b6c2143c422c8b45b0f168b4b221180356406a6819806121ca038401290a43c00119c5293390440038c0d5d0cf4e319aff40d4a400b0ac5729158aec004a400328ac5729158acca00634baa659862e9985361ac617d85e486905f0d1792c4d10f45db58ba5d90cec868)

def w113 : Sig := 0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee

def s316 := certify 235 4 ([w113,w35,w66,i7,i6]) cs235 [] (u235 3 40 0x65a92d9189e8942340984d9f61f0fad611e68a3678b27d6a1b68b47b927a00452)

def s317 := certify 235 5 ([w35,i0,w66,i7,i1,i6]) cs235 [s316] (u235 4 57 0x65a92cc6d317cd915ae3d6ae750822491c44313c84508c8678993e45114c4b5d345a24a1280948cfbf796a825094)

def s318 := certify 235 5 ([w113,i0,w66,i3,i7,i6]) cs235 [s316] (u235 4 57 0x6d12cd2930def69057218484313c84508c866c998e3d38f441414d047991460330cc60e9c7a11248e273893d)

def s319 := certify 235 5 ([w76,w66,i3,i7,i0,i6]) cs235 [] (u235 4 57 0x6d12cc351a998d5d2ff40269140c5728dd2930def6908f72ddce49895ce1b8edc231f4c080042d1af422392444)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s320 := certify 235 6 ([w66,i3,i7,i0,i1,i6]) cs235 [s317,s318,s319] (u235 4 180 0x2598da1fe8963f25e8c63d88da61498f6292f9846888983a10ea222170e85a34884816924d22d23a042a265c413a82a12ce43006ac80d4d03300cb380023388f2672088007181aba19e9c6335fe81a6d800815934a62b22a00024394070802521463ee4644988619f66d23c4b7dfb4fbd12d0817a0ae41e905e3d30910412908613984a272798841d909a42a8765b11e884)

def s321 := certify 235 6 ([w79,i6,i3,i7,i0,i1,i5]) cs235 [s298] (u235 4 81 0x4d08c841389c841389c8e7508c1d387422491c42148a442148a45ce128011040d5d2ff4026914008400084005721849ef691654207e53422d8d634652b1a)

def s322 := certify 235 6 ([w14,i6,w67,i3,i0,i1,i5]) cs235 [s309] (u235 4 75 0x104e27213423239d42089247108522913074e1d7384a004410009a450021003574bfd15c861214d08b0fbda2ee084b2604891600330587f8c28546)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s323 := certify 235 7 ([w67,i3,i7,i0,i1,i5,i6]) cs235 [s320,s321,s310,s322] (u235 4 231 0x10cc6d0ff4b31f8ff46309484309cc251393cc420ec84d20743b2188f4421ec46d30a4c7b1497cc235042e209d415082124444c1d08751110b8742d1a44240b492691691d021180356406a6819806121ca038401290a4ec00119c52b3390440038c0d5d0cf4e319aff40d4ac0040ac9b2b15915000313323224c430c5d30bd05720f482f1e984882174bbed10f45d4207e751f988661f9e47e621990251289102421a04a6428904259108a76210cec4222c886665198256019cac6603280bb93510e1f6)

def w114 : Sig := 0x5555555555555555555555555555555555555555555555555555555500000000

def s324 := certify 235 5 ([w114,i7,i5,i6,i1,i3]) cs235 [] (u235 5 60 0x66e8f1d22ae5a5c7b9572e550892470a27a367462b8f3727e55ca95742ab1a39a13dc70ab13801149a0004108033455e8a380398155ba55)

def s325 := certify 235 5 ([w80,i7,i5,i6,i0,i3]) cs235 [] (u235 3 60 0x12e97489b51fcb7e5e8de9a370269142271336a458bca3e9f8de8237b58dc3237e4993fb86e23e223924808204cc7d36a71750dd8e37)

def s326 := certify 235 5 ([w44,i7,i5,i6,i0,i1]) cs235 [] (u235 4 60 0x4bc93b247a3e86575ef9dfe00882066c93f28ac54af437bf9a3e97b1258c89f26ff847e111c449011404d348ff221116575791be)

def s327 := certify 235 6 ([w8,i7,i5,i6,i0,i1,i3]) cs235 [s324,s325,s326] (u235 1 75 0xfe7f1285c128b728251a8d1d8253209049762491e8fab995b42198e898f345909a4508820ab088110088dd19853032b2592191281c4a272793c76191188c0a0b)

def s328 := certify 235 5 ([w12,w9,i6,i0,i1,i3]) cs235 [] (u235 3 60 0x1fcfe250b87c3e1ba22491c88fab921b8dc63404d2280110401561102a956862633193ea046391c91dc8d606f041b31cce68823a)

def s329 := certify 235 6 ([w9,i7,i5,i6,i0,i1,i3]) cs235 [s328] (u235 5 81 0x3f9fe458845b94879e68a0892470823eae425684141b6d81401348a000110400156800800020552a95818cc7f1524c4f27d14a299442c42c14014006406430d27c2093217a)

def s330 := certify 235 6 ([w12,i7,w10,i6,i0,i1,i3]) cs235 [s328] (u235 1 78 0x7f3f8942e17048242e8d468ec120945b94131248f47d5cc21a10cc710cada7384d2284410558441980cc6e8cc0880440e733992c4a271293c9e3b2988c46050289c860b)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s331 := certify 235 7 ([w10,i5,i6,i0,i1,i3,i7]) cs235 [s327,s329,s330] (u235 5 231 0xd10f14b3cd2cd1441522c7f57907f908915eb2c512089bc45a07c72cc410815962e904204820bab2d805b1506d8418141146908222c249a6c2390104e70829283eb9e85cc8105340ad738414c104e782073c10164209ce104598202802ae19154ac8ac00c1d20004544d74d44520001ce000119c27499c8210003a400244156e941090001d282130003a4002641074e59194001d200065cb26246494af29857b05485664a23753745144ae933d1531521d6428cd3144a24f7e9d44e887d14792ba29f4510ca)

def s332 := certify 235 5 ([w12,i7,w81,i6,i0,i3]) cs235 [] (u235 2 57 0x9d4ea1cbe391c88c1257861809a450d96c97d0e10440419bc0743b02a5f64a6cbecf8258892475b17d2359dd03c1e1580b)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s333 := certify 235 6 ([w81,i5,i6,i0,i3,i7]) cs235 [s332] (u235 4 180 0xd23cab7b56d290a43d93a5f42750e84397ec5f17a0ae41e905e3d309104500aa311995543350c4031cf800815936a22b22a0002f81b2878364bf02fa1c087243940708025214a8800280aa3080800c17f3aa57ab0afa7a8bea1d908acda8765311a884129085f56b3c4aad1297c8418886ea108dc622118a84a40843d1692502d238f4422f88c251498be292f89442a085c413a82a10424)

def s334 := certify 235 5 ([w12,w82,i6,i0,i1,i3]) cs235 [] (u235 2 60 0xfe7f1285c7239118f4af0c311248e91f57291acee81e0f0ac04d228088202ac22020c2203a1d815d8962567c12c05c11c)

def s335 := certify 235 6 ([w82,i7,i5,i6,i0,i1,i3]) cs235 [s334] (u235 4 81 0x7f3f896c57218488c5903d4207a22491c423eae44e75082c224421088440269140011040055c01ce1280c0cc008400251fe04a630fc4a46789484c14c844289c8a)

def s336 := certify 235 6 ([w12,i7,w83,i6,i0,i1,i3]) cs235 [s334,s332] (u235 2 78 0xfe7f1285c723911824af0c311248e91f57291acee81e0f0ac04d228088202ac22020cde03a1d81564b25362567c12c048f4123d2da3ca088088c4b1194c464382780b)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s337 := certify 235 7 ([w83,i5,i6,i0,i1,i3,i7]) cs235 [s333,s335,s336] (u235 5 231 0x68878a59e69668a20a9163fabc83fc8448af596b882b89e09778611081300b62a0db083028228d21044584934d84720209fa1052507d7ed0b990209480e10239409412010a00ab864552b22b00307f800115135ff511480007e800046709fe672084000ff00091055bfd042400011071401c1001144146246494af29857b05485742085144ae9331142085128b3e43ac8511046086c14752983cb0510ca20ba47881f084091e177c7e964b213f423abf4a61164240ca800ff0107fa00194028e8463ab9e6)

def w115 : Sig := 0xbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbaaaaaaaabbbbbbbbaaaaaaaa

def s338 := certify 235 5 ([w115,i0,w12,i7,i3,i6]) cs235 [] (u235 3 54 0xc7325b24f84bc1309e30e47223847f2df86ed8d804d228020cde09c9c116c6c22392488ee6b24e4e)

def w116 : Sig := 0x1111111111111111111111111111111111111111000000001111111100000000

def s339 := certify 235 4 ([w33,w116,w12,i3,i6]) cs235 [] (u235 4 37 0x937095c351a9992930c8f72ddc391c88e0231f4c2239244bf14000e708e)

def s340 := certify 235 4 ([w35,w116,w12,i7,i6]) cs235 [] (u235 4 34 0xc73259926e12b86e231f4c23b9ac5471114001a8d4d61c8e4470e708e)

def s341 := certify 235 5 ([w116,i0,w12,i7,i3,i6]) cs235 [s339,s340] (u235 4 51 0x18e64b324dc2574a4c30e47223423dcb770dc6a35332083cc20232988f9c238463e984472488477358a8e0)

def s342 := certify 235 4 ([w35,w33,w68,w12,i6]) cs235 [] (u235 3 37 0x93e12f3c5993e4c7d6423b9ac888e4921bf32f82613637a3f997c00458)

def s343 := certify 235 5 ([w33,i0,w68,w12,i3,i6]) cs235 [s342,s339] (u235 3 54 0x127c25ec66c0984f191fcb7e1c8e44704c7d6223924908f26f223b9ac9b1b0df053865f32f806fccbe)

def w117 : Sig := 0x5555555555555555555555555555555500000000000000000000000000000000

def s344 := certify 235 5 ([w117,i0,w68,w12,i3,i6]) cs235 [] (u235 3 51 0x93e12f04c278c8fe5bf131f5888e49240088111dcd64351ab601348a0c5e51f1cd896c391c88e06e6f)

def s345 := certify 235 5 ([w35,i0,w68,w12,i7,i6]) cs235 [s342,s340] (u235 3 51 0x63992d927c25e1b931f588ee6b2423c914888e492678b27c8b6d2991597ccbe00984d82e391c88e11fccbe)

def w118 : Sig := 0x5500550055005500550055005500550055005500550055005500550055005500

def s346 := certify 235 5 ([w118,i0,w68,w12,i7,i6]) cs235 [] (u235 3 51 0xc7325b24f84bc37263eb11dcd6480110222392486a356c0419bc18bca3e0984f18723911c23f96fc45)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s347 := certify 235 6 ([w68,w12,i7,i0,i3,i6]) cs235 [s338,s341,s343,s344,s345,s346] (u235 3 162 0x96cc231f9cc963f2588d995ac93e12f2b44a25e6ec0b84da027918c17611c0e496171c88c2e2325c43ae11fc3de758f56fd1cc035c088d5822d818f900815935ae2b22c002cc00463341a64666f118032c22c5e0e65828f823d2d968dc4a44c296128a4fac4c3d2281691c7a2d24c11010044f21102980448846452d109dc46213596c88b65b4)

def s348 := certify 235 5 ([w89,i3,w12,i7,i0,i6]) cs235 [] (u235 3 57 0x31cc96c93e27f0d46ad8083378317947c04d2280dd2e97c61c8e446bb47f187b1b1802204477359273af888e492)

def s349 := certify 235 6 ([w90,i3,w12,i7,i0,i1,i6]) cs235 [s348] (u235 3 71 0x18e64b66b793d9b318dac5f62359dc9d6eba48bc892472299116c6a356c02208020cde14ba58be9204d22804400221b40a63630e472231e8bc7a618)

def s350 := certify 235 6 ([w91,i3,w12,i7,i0,i1,i6]) cs235 [] (u235 5 74 0xc73258c35bc9e31b462f8c11acee13add749b82b2c0b4d0630008820008337814ba5dd4902aa8069248c1a225c4415ee23e1be182b02b00a80a897112e213c)

def s351 := certify 235 6 ([w92,i6,w12,i7,i0,i1,i3]) cs235 [] (u235 3 74 0xe4722382ba18502613c681e8f608924722359dcbb82a86d62fb10a452404d2280110401066f00e87502a351ab605c6e214c2325b3213c96232588c4e25)

def s352 := certify 235 5 ([w114,i6,w12,i7,i1,i3]) cs235 [] (u235 5 57 0xe388888ab969719ba3c74089247082359dc262b8f37227a36742ae87325e9a384f700229340008210001bd06028e00e19a2af4)

def s353 := certify 235 5 ([w80,i6,w12,i7,i0,i3]) cs235 [] (u235 3 57 0x391c88e11fcb7e4ba5d226d02691401066f062f28fa271336a446e6d3992cda93e27f111c9240410223b9ac938b998fa6d)

def w119 : Sig := 0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeaaaaaaaaeeeeeeeeaaaaaaaa

def s354 := certify 235 4 ([w119,w8,i6,i7,i3]) cs235 [] (u235 4 34 0x723911a14aa527d8ae4309147339e09e601348a0020cde005d6e60e70947)

def s355 := certify 235 5 ([w94,w8,i6,i7,i0,i3]) cs235 [s354] (u235 2 51 0x391c88c12a55293c2e57861809a4501066f02eb7301d0eca3845300b399cc324fc8924748d67748fba340f)

def s356 := certify 235 5 ([w44,i6,w12,i7,i0,i1]) cs235 [] (u235 4 57 0x2359dc48f47d0cae97927640110400419bc1158a95e86cd927e5e91cc97292c49f2111c449011404d408c72392111657348ff2)

def s357 := certify 235 6 ([w8,i6,w12,i7,i0,i1,i3]) cs235 [s328,s352,s353,s355,s356] (u235 1 71 0x723911824128b72824fe7f1285dae0904b6e2491e8d67795b4b38fab993345b09a450882083378110088ab08879038864a605399cc9625138949e07)

def s358 := certify 235 5 ([w95,i6,w12,i7,i0,i3]) cs235 [] (u235 2 57 0x391c88c125786189d4ea1cbe09a4501066f01d0ec0ab65b25f43841100b2f9cc965f67c12c44923a46b3ba0783c2b362fa)

def s359 := certify 235 6 ([w96,i6,w12,i7,i0,i1,i3]) cs235 [s334,s358] (u235 4 71 0xe47223415c86121fcfe25b089247108d677139d4208fab91009a45000441001066f07384a01570028e673258959e252207a81e96c47914010014c4e6)

def s360 := certify 235 4 ([w119,w11,i6,i7,i3]) cs235 [] (u235 4 37 0x391c88d12930c6331e0c42b98484508c84fe709001348a0020cde01a8d4cc)

def s361 := certify 235 5 ([w94,w11,i6,i7,i0,i3]) cs235 [s360] (u235 3 57 0x391c88e02613c602691401066f01a8d5b008a60633186590ae6140e8750229423427f71211248e446b3b924d26ad6)

def s362 := certify 235 6 ([w11,i6,w12,i7,i0,i1,i3]) cs235 [s361] (u235 4 74 0x723911a108b72a252618449238846b3b895a2114cda62f9804d22800220800833782000406a35333061192cccf139ac8b2042910a410040464b1192c825)

def s363 := certify 235 5 ([w13,i6,i7,w12,i0,i1]) cs235 [] (u235 4 57 0xe750821c88449792764011041ce12801c8cc0cd927e5e92c54b290e49724097628020041116440e4963934912)

def s364 := certify 235 6 ([w14,i6,i7,w12,i0,i1,i3]) cs235 [s363] (u235 4 74 0xae4309104bb22c8458a68436c4492389cea1044b10884291488429148804d22800220839c25004b19801080010800827139302313904e4258fc866)

def s365 := certify 235 6 ([w73,i6,i7,w12,i0,i1,i3]) cs235 [] (u235 4 74 0xae43090723911a2c84584492389cea1046b3b88429148804d22800220839c250083378010801427209c8731f88d16458522148a008004e41390966)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s366 := certify 235 7 ([w12,i7,i0,i1,i3,i6]) cs235 [s347,s349,s350,s306,s312,s351,s357,s359,s362,s364,s365] (u235 6 228 0x8528306ada27dcab329f4a8488306aba60c1aaa11204a9a64939f2103046b8c2c49b618412598c1031b618b0684884386dca2ce18688b226dca102132b84566d847813c2e7981b610404b5e816cb419406b5e945eb418106b5a0102b421648b5a1646b420102b568102b48906ab569076b488102b45290eb41010eb450114b412d04e018034e030834e018806e03000ce1c0000e02154ce1c1544e020000b568000b40b302b5c3340b408000e1c0000e089920f87065bb82200038042073814007380400138142052821680a)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s367 := certify 235 6 ([w68,i5,i7,i0,i3,i6]) cs235 [] (u235 5 180 0x5e46b5edf6d79fa9fb0db18b2431091841832c330485eecb6cc15a9bb11b3ac8479de1cebf16e71070c068621a0c80c60066940008a89b5da88a40005dc09fed96d77ca83b01b32d0629c01ccb014672074871c32b52722b6418e3ba38eda5bb745b8b638e902086a069283e8c10de04111611fcb0924041001008575002ba020105d0456d06dd40c7d82d8b7008704716c208e80e)

def s368 := certify 235 6 ([w68,w12,i5,i7,i0,i3,i6]) cs235 [] (u235 5 74 0xcc94d8c34920c92460c8d46f4411e78411e78469a0c6004d228003772010000410000436906906ea5b11c10c7d1822392420100020a0638500414059)

def s369 := certify 235 6 ([w11,i6,i5,i7,i0,i1,i3]) cs235 [] (u235 4 81 0x8d468ed0845b9512930c22491c4263a244ad108426d317cc026914001104006e8cc100020351a9983bc08c46cf309cc6331e0d64590214885208020a50ef04210c4e25)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s370 := certify 235 7 ([w12,i5,i7,i0,i1,i3,i6]) cs235 [s330,s336,s367,s368,s327,s369] (u235 5 231 0x9b186ebe64a6fe4df430cf91863ac9235e490ea30c62c90c42461060cb0dd108d4dac8de96e936410512086df9e207cf0a2410812082ef9e207cf0ba4107b08da35031ee82f8c10c6908222c249a6c23901045b082ea06396e083a0822dc1016c208b61045b8202dacd32590822d841164b659180d0c43419018c00c38800115134e3511480002d800046708e267208400071000eb26e9c72cba00038a081c4000e20007141038a08194000e20006541042944a90f320c511a429c831446e887d144a2512894628b90c4)

def s371 := certify 235 5 ([w13,i6,i7,w97,i0,i1]) cs235 [] (u235 4 57 0xbdf3bfc9792764011040f7f347ccd927e4e7509ce1283958c94b222116497b124097628020057b1e34912)

def s372 := certify 235 6 ([w14,i6,i7,w97,i0,i1,i3]) cs235 [s371] (u235 4 74 0x118b22c8458a6844bc44923885844884291488429148804d228002208018198010800108008573091cea139c2509641389c841389c8ac0fd426)

def s373 := certify 235 6 ([w73,i6,i7,w97,i0,i1,i3]) cs235 [] (u235 4 74 0x3ded2ac845844923886e3718a8429148804d2280022080aa5550c4108008573091cea139c2504641389c841389c8631fa916458522148a0080306)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s374 := certify 235 7 ([w97,i7,i0,i1,i3,i6]) cs235 [s372,s373] (u235 4 228 0x21e0c633ca87e6329e07f821a8c640b2d297991240b10c979ac640e91e97aade40eada97a90a429ec46d4298526429ec525f429846429a44242a05a49429a45a4742a042428c443742a84237428c4423142a84a4a980354ab20354a9a064ab00c4aa54004aa0564d4aa5456454aa00042a14004288ce242a54ce414288004aa80554a8c466554aa866a4a8c4031288948428984e6288944e4f289884288f48428a05e57288f45e6128a08442888e428868e428a9442884844a829c4ac09c4a80844ac29428944b623)

def s375 := certify 235 6 ([w98,i6,i5,i7,i0,i1,i3]) cs235 [] (u235 4 81 0x8d468ed057218496422d0d4221a22491c4263a244e75082148a442148a44026914001104006e8cc1ce12808400084004a28ec841389c841389c981de076652b03b)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s376 := certify 235 7 ([w99,i5,i7,i0,i1,i3,i6]) cs235 [s375] (u235 5 231 0x13630dd7cc94dfc9be8618c59218848c20c1961ba211a9b591bd2dd26c822e20ae27825de18442043d846d1a818f7417c608634841116124d3611c80828b84175031e2f041d0412901c20472812824020c068621a0c80c60064040008a89b01a88a400045c00023385013390420008080075937603965d00008838a00e08008a20a4820834c349313c6104289468bd10fa288827c75f86218df14fe188632c5d5884090b205620ba440598028b85045e008b216465c8080819407200ca01474e510cb65b)

def w120 : Sig := 0xffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s377 := certify 235 6 ([w120,i6,i7,i1,i3,i5]) cs235 [] (u235 3 180 0x3b44a21d0ec8623a4412a2309d84a2727b2200543a1140e8220442a1517c15d07a82f1e9852103701fa0b87c36170dd45605c26d013c8c60bb0ae09a0c3015bd48a1001510f21705482a8214349140b492691691e08862437a108dc622118d151ec8dac2963d8a4bec4c672208c819dea4102021b3510e8ea4350d3304706a0c3508b30665015462332ad0ce862031)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s378 := certify 235 6 ([w100,i6,i7,i0,i3,i5]) cs235 [] (u235 3 180 0x3b44a21d0ec8623a4412a2309d84a2727b221270842bc4150a885105f05741ea0bc7a614840dc07e82e1f0d85c3751581709b404f23182ec2d82491a485a692394120443a1500ea020542215618040ac9af51591600280aa3119956867431018b00d702235608b606464008ce4f53390480112cd443a4490d434cc296623d9b4527b2f9330c486f4211b8c44231a2a)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s379 := certify 235 6 ([w102,i6,i7,i0,i1,i5]) cs235 [] (u235 3 180 0x3b44a21d0ec8623a4412a2309d84a2727b220f51205e571e8bcc30881510f21705482a82141890de8423718884634547b236b0a58f6292fb131a48a05a49348b48f0448110e85403a8081508856320046727a99c824014055188ccab433a1880c5806b8111ab045b031860102b26bd4564580021b3510e8ea4350d334304c2f8138cc0bb306e03f4170f86c2e1ba8a)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s380 := certify 235 6 ([w103,i6,i7,i0,i1,i3]) cs235 [] (u235 3 180 0x1b80fd05c3e1b0b86ea2b02e136809e46305d85f05741ea0bc7a61484349140b492691691e08862437a108dc622118d151ec8dac2963d8a4bec4c1510f21705482a8214618040ac9af515916002320046727a99c824014055188ccab433a1880c5806b8111ab045b0310221d0a80750102a110a92d9aaf744bbda869984ecc8254138949e8c83b44a42d0ecb623a44)

def s381 := certify 235 6 ([w103,i5,i6,i7,i0,i1,i3]) cs235 [] (u235 5 81 0x79e68a49230623cf0823cf080892470b6db028da317c68020a08020a0009a4500008820154aa561a68318800020800020314a11869241ba2ba2a41a4184e8ae8a)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s382 := certify 235 7 ([w104,i6,i7,i0,i1,i3,i5]) cs235 [s377,s378,s379,s380,s381] (u235 3 231 0xed1288743b2188e9104a88c2761289c9ec8843442890ca2d721acca2882f82ba0f505e3d30a4206e03f4170f86c2e1ba8ac0b84da027918c17621c4174865d6190d325d880a88790b82a415410a1a48a05a49348b48f0443121bd0846e31108c68a8f646d614b1ec525f6268e911663a598e90cf259224088742a01d4040a8442b1b00815936362b22c00474008ce51b3390480280aa3119956867431018b00d702235608b60646c00cb1b32c6c8653328010d9a88747521a8487310c90e063f)

def w121 : Sig := 0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaaaaaaaaaaaaaaaaa

def s383 := certify 235 5 ([w121,w14,i6,i7,i1,i5]) cs235 [] (u235 4 53 0x4c12c841389c841389c8e75082c22442148a442148a44201040ac0fd426e70940606600420004200)

def s384 := certify 235 6 ([w106,w14,i6,i7,i0,i1,i5]) cs235 [s298,s383] (u235 4 74 0x98259082713908271391cea105844884291488429148848d48b9c2500220801819801080010800083c81581fa84c8239488c5916422c53)

def s385 := certify 235 5 ([w57,i0,i6,i7,i1,i5]) cs235 [] (u235 4 57 0xdff0e7cb192964e7508bdf3bfc97927652f6244a129011044af2bc691a40250944097625795e348d2)

def w122 : Sig := 0x55005500550055005500550055005500550055005500550000000000000000

def s386 := certify 235 4 ([w113,w122,i6,i7,i5]) cs235 [] (u235 4 40 0x6ff873e58c94b297b12411164a0fb1eb491240200e708212a9555e1a8d4d2)

def s387 := certify 235 5 ([w122,i0,i6,i7,i1,i5]) cs235 [s386] (u235 4 57 0xdff0e7cb192964e7508bdf3bfc97927652f625ce1280114c0552aabc351a9a48222c8812ec431f63d692250)

def s388 := certify 235 5 ([w113,i0,w13,i6,i7,i5]) cs235 [s386] (u235 4 57 0xdff0e7cb1929652f6248222c8af63c692248299050812ec44799146b5f2d7d3394ce407388215ef96be4bca672)

def w123 : Sig := 0x4444444444444444444444444444444444444444444444444444444444444444

def s389 := certify 235 5 ([w123,i0,w13,i6,i7,i5]) cs235 [] (u235 4 57 0xdff0e7cb1929652f6248222c8af63c6922500400812ec5ce128f7f347ccd927e4e7508bdf3bfc979276441)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s390 := certify 235 6 ([w13,i6,i7,i0,i1,i5]) cs235 [s385,s387,s388,s389,s363,s371] (u235 4 180 0x4691bfe7cf91ad71cf89e3f9163213c8fe2752c892a085c413a82a10424bf897be10fafe2177f85ebe892f214cafa294ec852243940708025214598002338932672088005a81efe19f96a3368f81e99819b284a6704fc812c4a5e1ffb03fc7a5213a1041e904e3d45910414a102348852695d8902822003c8205380100c215eb7b16c791e1fd8d24487e844ad2)

def s391 := certify 235 6 ([w13,w14,i6,i7,i0,i1,i5]) cs235 [] (u235 4 74 0x98259082713908271391cea105844884291488429148b9c2500220801819801080010803d81fa8648222c8812ec5004008b6116422c5d)

def s392 := certify 235 6 ([w13,i3,i6,i7,i0,i1,i5]) cs235 [] (u235 4 81 0x4d08c84613c8e7508c1d387491621d822491c5ce128011040d5d2ff4a9629d80269140cd6185721849ef6b129307e27209c82910a4500400a5634630fd88)

def s393 := certify 235 6 ([w109,i5,i6,i7,i0,i1,i3]) cs235 [] (u235 4 81 0x8d468ed07f3f896c572184822491c4263a24423eae44e7508026914001104006e8cc0055c01ce128c964e04a4a28ec8467894881ea07a211084500400a56076630fc4a27)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s394 := certify 235 7 ([w14,i6,i7,i0,i1,i3,i5]) cs235 [s384,s299,s390,s391,s392,s304,s311,s314,s322,s327,s393,s364,s372] (u235 4 231 0x26c84c60f09bc092f0422bc841f89c4eaf1389c7e4256c842889c4f591389ca2420bd05720f482f1e98488255d08c5b155b5b08454ed61fa10f94207f6b35d66992ea1079420ba532ed042e209d415082121a44240b492691691d02147c42c08711f10a27021414421f8a45305148a47e21414422c8a45305148a4b221121ca038401290a3b40040ac9aed1591500041400119c4ed339044003b400c0cf0ed198cf0003b4001fc20ed8407e003b40032c20ed840ca0040ceaac10f0751f8fcea4350cc4866)

def s395 := certify 235 6 ([w110,i3,i6,i7,i0,i1,i5]) cs235 [] (u235 5 81 0x8544208613c438e504db6c0a489887302b2c082b2c09c70450008820154aa560a9314e601554001554018cc7f15709708d14d14610634d6b84b8468a68a18633e)

def s396 := certify 235 6 ([w111,i5,i6,i7,i0,i1,i3]) cs235 [] (u235 5 81 0x1e79a28fe7f9162116e52162085822491c2db6c0a08fab9095a1050401050004d22800044100aa552b001568008000219000646331a6cae8ae8a9262793c4e8ae8a18693e)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s397 := certify 235 7 ([w73,i6,i7,i0,i1,i3,i5]) cs235 [s395,s396,s305,s365,s373] (u235 5 231 0x3a10429ae574b388a104578827d34caf9a6f8412e20ae27825de184420468878a59e69668a20a3aacb7c41099208f9659480e10239409412010d21044584934d8472020b00b62a0db08302822a06105f51440e8a3e08211071401c100114414838001151360f511480008180004670a0e67208400050055c322a95915801841c003e41083a087c000752198cebf7c510ca98a3308751263ccc2144420ba42c755882990b1756a0b3405030a881d01164240ca8010701083a0019403ac15821c746)

def s398 := certify 235 4 ([w113,w33,w69,i6,i3]) cs235 [] (u235 3 40 0x1309e315d0c28391c88e0c6636c4627a3cd114644923936357fb917e00412)

def s399 := certify 235 4 ([w35,w33,w69,i6,i1]) cs235 [] (u235 4 40 0x3698be673a8411ad12211248e23198cc9f2189e4a1094948d5f250940008a8)

def s400 := certify 235 5 ([w33,i0,w69,i6,i1,i3]) cs235 [s398,s399] (u235 3 57 0x2613c62ba1850723911c11248e46d62fb7705508d68923198db1189e815440a9be0f306f229936357d02a8150)

def s401 := certify 235 4 ([w35,w113,w69,i6,i7]) cs235 [] (u235 2 40 0xc6630ce80b11c989f11ad12b3c727c1e0f93d008a87239118242613c178f38a3)

def s402 := certify 235 5 ([w113,i0,w69,i6,i7,i3]) cs235 [s398,s401] (u235 3 57 0x723911c04c278c57430a18cc61964a11a2313d08307982088ca62366cb623cd146044923911ad124d8d9dc93d)

def s403 := certify 235 5 ([w35,i0,w69,i6,i7,i1]) cs235 [s399,s401] (u235 4 57 0x235a2446d317cce750822491c46331e0c4508c84313c84511e4445b694c8a678993e4a12801c8e4468948d625094)

def s404 := certify 235 5 ([w112,w69,i6,i7,i0,i3]) cs235 [] (u235 3 57 0x1c8e44701309e323f96fc04d228020cde0351ab6317947c6331865b86e23ee49897888e492008811064d644c7d64)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s405 := certify 235 6 ([w69,i6,i7,i0,i1,i3]) cs235 [s400,s402,s403,s404] (u235 4 180 0x11a0738b0e447611e10865a464498861ac617a0ae41e905e3d30910434884816924d22d23a0428f88423109ae3e214488c423d88da61498f6292f9846a2cdc413a82a1232461800815935322b22a0008c80023388f267208800218002319a0ca6333788c003006ac80d4d03300c243940708025214c18c623c298f185c08cc611909842a8465b11e08412908613984a27279884)

def s406 := certify 235 5 ([w112,i5,i6,i7,i0,i3]) cs235 [] (u235 3 60 0xbd1bd346e1309e323f96fc04d2284fc6f411b8d46ad8c5e51f18c6f4f1bf0dc47dc9312f111c92401102a1bb1c6e4c7d64e2e)

def s407 := certify 235 6 ([w69,i5,i6,i7,i0,i1,i3]) cs235 [s406] (u235 5 81 0x11a8de8849230623cf0823cf0808924708263a242368c5f1a008280a610459009a450000882000ddc80d3418c4000104000103198d81ba6228a41a418428ae98906906)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s408 := certify 235 7 ([w70,i6,i7,i0,i1,i3,i5]) cs235 [s405,s407] (u235 4 231 0x26c84c10f09b2192f04209484309cc251393cc420bd05720f482f1e98488210d08c5b0c3b5b08432d23224c430d635042e209d415082121a44240b492691691d02147c42c08711f10a270211ec46d30a4c7b1497cc23121ca038401290a4240040ac9b09159150004c400119c5093390440042400c0cf109198cf000180356406a68198061d48663c10f04331886512890864219e4a642892c5db20868b30ec82ea04259108a62210cc44222c886665198212019c246603280871d510e0a3f)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s409 := certify 235 8 (roots 235) cs235 [s307,s313,s315,s323,s331,s337,s366,s370,s374,s376,s382,s394,s397,s408] (u235 4 240 0xd5e0c63c1a87e63c0e07f8ada8c6ac8ec8428aaaeaaa8eea62328a8847c8948428984e66b8944e4f28988459e91e2eaade4ceada2ea90a3cb2d22e991229b10c2e9ac6288bd0572e907a4408bc7a612891042c8c44372ca842372c8c442312ca84a2c9ec46d2c985262c9ec525f2c98462cd042e2c904e2cd0542c904242c9a4422ca05a492c9a45a472ca04232a8055328c4665532a866a328c4031329803532b2035329a0632b00c32921c32d01c32900432d214329940032a0564d32994564532a0002c964002c88ce22c994ce412c8800)

theorem lower235 : Claim 235 9 := fromSearch 24661 (by decide +kernel) s409.property

theorem lower251 : Claim 251 10 := fromLift 10 16 24644 lower235 (by decide +kernel)

def cs150 : Cuts (goalAt 150) := []

def dict150 : Nat := 0x841405808120620a001610048508400208008404048001210208081202

def d150 := unpackCases dict150 4

def u150 := unpackShort dict150 4

def s410 := certify 150 3 (roots 150) cs150 [] (d150 24 0x1c06641b0a0551433092872)

theorem lower150 : Claim 150 4 := fromSearch 268502848 (by decide +kernel) s410.property

def cs210 : Cuts (goalAt 210) := []

def dict210 : Nat := 0xc040301405202049085210049408280300008200048008202048401202

def d210 := unpackCases dict210 4

def u210 := unpackShort dict210 4

def s411 := certify 210 3 (roots 210) cs210 [] (d210 24 0x55c202b00a90442118713306)

theorem lower210 : Claim 210 4 := fromSearch 385941568 (by decide +kernel) s411.property

def c214_0 := ruleFor 214 lower196 none (by decide +kernel)

def c214_1 := ruleFor 214 lower198 none (by decide +kernel)

def c214_2 := ruleFor 214 lower150 none (by decide +kernel)

def c214_3 := ruleFor 214 lower210 none (by decide +kernel)

def c214_4 := ruleFor 214 lower198 (some (0,i1,i7)) (by decide +kernel)

def cs214 : Cuts (goalAt 214) := [c214_0,c214_1,c214_2,c214_3,c214_4]

def dict214 : Nat := 0x8001600048000e000280004824225000441021800840215100464014800160004810521040010948020818d00030800c00215010941404a00460011008540030108821021810840630041000315140460611908541420802000040008841005808120614808524214940161004850441430140460411018840030000161405818841430100c08020a010000400048480048008404208084400111001210110101202

def d214 := unpackCases dict214 7

def u214 := unpackShort dict214 7

def w124 : Sig := 0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0

def s412 := certify 214 5 ([w124,i2,i6,i1,i4,i7]) cs214 [] (u214 3 53 0xa1d0022d001f1f04343acee0172922724212144212142a1ba19caca1f01f0263f11caca)

def w125 : Sig := 0xffffffffffffffff0000000000000000f0f0f0f0f0f0f0f0

def s413 := certify 214 4 ([w125,i2,i7,i1,i4]) cs214 [] (u214 3 40 0x69234f23ee017672365235d85b88591f8823c820630227292a23c2311828)

def s414 := certify 214 5 ([w85,i2,i7,i1,i4,i6]) cs214 [s413] (u214 3 53 0x2c19241223f0372d00c1d001f1f0292272ee01753c51c421214421214a2192111f01f0c116b6)

def w126 : Sig := 0xffff0f0fffff0f0fffff0f0fffff0f0fffff0000ffff0000ffff0000ffff0000

def s415 := certify 214 4 ([w126,i2,i7,i1,i6]) cs214 [] (u214 3 40 0x2c2b229227253c51c4312f4ee0158826d2525c63b03900372d00a1d0)

def s416 := certify 214 5 ([w87,i2,i7,i1,i4,i6]) cs214 [s415] (u214 3 53 0x2c1920372d00c1d0292272ee01753c51c4312f4882193b039025c6192192130410174174a11)

def w127 : Sig := 0x3333333333333333333333333333333333330000333300003333000033330000

def s417 := certify 214 4 ([w127,w19,i7,i2,i6]) cs214 [] (u214 3 34 0x24f2b277e45e882113d3d1d675e73e434271242f31445f5546f)

def s418 := certify 214 5 ([w19,i7,i1,i2,i6]) cs214 [s417] (u214 4 111 0xac42e613caf057c108d446e04501aa2968040141183204616210e18f4ae07bc870acc6f18ec0960f259c80c04921488cc492664e22091c8431098a390979884a109cb2ad2cbfc210082ea11c020294a4a4a)

def s419 := certify 214 4 ([w20,i6,i7,i1,i4]) cs214 [] (u214 3 40 0x83253d25598818ee0177f257d255d85b88251b8607b064794a251b2511868)

def s420 := certify 214 5 ([w14,i6,i7,i1,i2,i4]) cs214 [s419] (u214 2 53 0x365601a9a806a6a0ec1c8c362384761141d9343c3c0bc312f906d5e4333390ccce058d8cc2a)

def w128 : Sig := 0xffff0000ffff0000ffffffffffffffffffff0000ffff0000ffff0000ffff0000

def s421 := certify 214 4 ([w128,i6,i7,i1,i2]) cs214 [] (u214 3 40 0x3d3d1d6882113b03904312f4455574292272ee01523231b20a1d00372d0)

def s422 := certify 214 5 ([w70,i6,i7,i1,i2,i4]) cs214 [s421] (u214 4 53 0xd158006e5a03b01c80da81908141ce0588625e42695c852227111e852020820681ac4b1158)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s423 := certify 214 6 (roots 214) cs214 [s412,s414,s416,s418,s420,s422] (u214 4 160 0x11fa1119fab0471bac68fd42549840092a4a930c5f24a00248a004846a6f245352d9080089618953550258764189aa328fc50426e0c84111847f88425e31dc809609792ce6403028a221d19643a2acaa308ca2490a6823315124cc9e8220a40b3a5423a4020252b5a88e4250c4263447212fa1884)

theorem lower214 : Claim 214 7 := fromSearch 302057024 (by decide +kernel) s423.property

theorem lower199 : Claim 199 6 := fromLift 6 1 1654 lower198 (by decide +kernel)

theorem lower211 : Claim 211 6 := fromLift 6 2 68 lower209 (by decide +kernel)

theorem lower87 : Claim 87 5 := fromLift 5 2 1604 lower85 (by decide +kernel)

theorem lower151 : Claim 151 5 := fromLift 5 1 1860 lower150 (by decide +kernel)

def cs83 : Cuts (goalAt 83) := []

def dict83 : Nat := 0x490843011040c1210105081200104001100048081110104041101

def d83 := unpackCases dict83 4

def u83 := unpackShort dict83 4

def s424 := certify 83 3 (roots 83) cs83 [] (d83 24 0x1b0a1916630551244032872)

theorem lower83 : Claim 83 4 := fromSearch 68 (by decide +kernel) s424.property

def c215_0 := ruleFor 215 lower213 none (by decide +kernel)

def c215_1 := ruleFor 215 lower214 none (by decide +kernel)

def c215_2 := ruleFor 215 lower199 none (by decide +kernel)

def c215_3 := ruleFor 215 lower195 none (by decide +kernel)

def c215_4 := ruleFor 215 lower211 none (by decide +kernel)

def c215_5 := ruleFor 215 lower87 none (by decide +kernel)

def c215_6 := ruleFor 215 lower151 none (by decide +kernel)

def c215_7 := ruleFor 215 lower213 (some (3,i2,i6)) (by decide +kernel)

def c215_8 := ruleFor 215 lower213 (some (2,i2,i6)) (by decide +kernel)

def c215_9 := ruleFor 215 lower214 (some (1,i2,i6)) (by decide +kernel)

def c215_10 := ruleFor 215 lower213 (some (1,i2,i6)) (by decide +kernel)

def c215_11 := ruleFor 215 lower213 (some (0,i2,i6)) (by decide +kernel)

def c215_12 := ruleFor 215 lower214 (some (3,i2,i6)) (by decide +kernel)

def c215_13 := ruleFor 215 lower213 (some (3,i2,i7)) (by decide +kernel)

def c215_14 := ruleFor 215 lower213 (some (2,i2,i7)) (by decide +kernel)

def c215_15 := ruleFor 215 lower214 (some (1,i2,i7)) (by decide +kernel)

def c215_16 := ruleFor 215 lower213 (some (1,i2,i7)) (by decide +kernel)

def c215_17 := ruleFor 215 lower83 none (by decide +kernel)

def c215_18 := ruleFor 215 lower213 (some (0,i2,i7)) (by decide +kernel)

def c215_19 := ruleFor 215 lower214 (some (3,i2,i7)) (by decide +kernel)

def c215_20 := ruleFor 215 lower213 (some (1,i4,i7)) (by decide +kernel)

def c215_21 := ruleFor 215 lower213 (some (2,i4,i7)) (by decide +kernel)

def c215_22 := ruleFor 215 lower196 none (by decide +kernel)

def c215_23 := ruleFor 215 lower211 (some (1,i4,i7)) (by decide +kernel)

def c215_24 := ruleFor 215 lower209 (some (1,i4,i7)) (by decide +kernel)

def c215_25 := ruleFor 215 lower213 (some (3,i4,i6)) (by decide +kernel)

def c215_26 := ruleFor 215 lower213 (some (1,i4,i6)) (by decide +kernel)

def c215_27 := ruleFor 215 lower213 (some (2,i4,i6)) (by decide +kernel)

def c215_28 := ruleFor 215 lower214 (some (1,i4,i6)) (by decide +kernel)

def c215_29 := ruleFor 215 lower213 (some (0,i4,i6)) (by decide +kernel)

def c215_30 := ruleFor 215 lower214 (some (3,i4,i6)) (by decide +kernel)

def c215_31 := ruleFor 215 lower199 (some (1,i1,i6)) (by decide +kernel)

def c215_32 := ruleFor 215 lower198 (some (1,i1,i6)) (by decide +kernel)

def c215_33 := ruleFor 215 lower195 (some (1,i1,i6)) (by decide +kernel)

def c215_34 := ruleFor 215 lower214 (some (1,i4,i7)) (by decide +kernel)

def c215_35 := ruleFor 215 lower199 (some (3,i1,i7)) (by decide +kernel)

def c215_36 := ruleFor 215 lower198 (some (0,i1,i7)) (by decide +kernel)

def c215_37 := ruleFor 215 lower213 (some (3,i4,i7)) (by decide +kernel)

def c215_38 := ruleFor 215 lower198 (some (3,i1,i7)) (by decide +kernel)

def c215_39 := ruleFor 215 lower195 (some (3,i1,i7)) (by decide +kernel)

def c215_40 := ruleFor 215 lower214 (some (2,i4,i7)) (by decide +kernel)

def c215_41 := ruleFor 215 lower211 (some (2,i4,i7)) (by decide +kernel)

def c215_42 := ruleFor 215 lower213 (some (0,i4,i7)) (by decide +kernel)

def c215_43 := ruleFor 215 lower214 (some (3,i4,i7)) (by decide +kernel)

def c215_44 := ruleFor 215 lower213 (some (2,i6,i7)) (by decide +kernel)

def c215_45 := ruleFor 215 lower213 (some (3,i6,i7)) (by decide +kernel)

def c215_46 := ruleFor 215 lower150 none (by decide +kernel)

def c215_47 := ruleFor 215 lower85 none (by decide +kernel)

def c215_48 := ruleFor 215 lower214 (some (0,i6,i7)) (by decide +kernel)

def c215_49 := ruleFor 215 lower213 (some (0,i6,i7)) (by decide +kernel)

def c215_50 := ruleFor 215 lower214 (some (1,i6,i7)) (by decide +kernel)

def c215_51 := ruleFor 215 lower213 (some (1,i6,i7)) (by decide +kernel)

def c215_52 := ruleFor 215 lower214 (some (2,i6,i7)) (by decide +kernel)

def c215_53 := ruleFor 215 lower214 (some (3,i6,i7)) (by decide +kernel)

def cs215 : Cuts (goalAt 215) := [c215_0,c215_1,c215_2,c215_3,c215_4,c215_5,c215_6,c215_7,c215_8,c215_9,c215_10,c215_11,c215_12,c215_13,c215_14,c215_15,c215_16,c215_17,c215_18,c215_19,c215_20,c215_21,c215_22,c215_23,c215_24,c215_25,c215_26,c215_27,c215_28,c215_29,c215_30,c215_31,c215_32,c215_33,c215_34,c215_35,c215_36,c215_37,c215_38,c215_39,c215_40,c215_41,c215_42,c215_43,c215_44,c215_45,c215_46,c215_47,c215_48,c215_49,c215_50,c215_51,c215_52,c215_53]

def dict215 : Nat := 0x800344442400a9002704901001d40084c0024007d001b2041081024004887012140d000e4002c458040020d08080032000b21808460230240c24020c04411004500515015010811430800110440060c4803110084403000500268002a000980022000780019002020900820405410160640090910105808820120c01001640034460640028450511405002d400a500234004d000f400310009112008105309090031400c1002f40094150010c0086064004094904001d0035400d10033400b1002b40079001925202000521401002e04408410421009003205811001c4006844502141484062500091104005c410280010850410414840114404450004c04d0102484013004004486042101486001190012500481085018000c540034240524014440450411014441004804824211004440234142000211801002814800460405800941015100c04211019001520441000315040521010c0e000104a01000630041002204600430120840464210d0900013000011051040d000440051000005404810080001000211050151030140161004850111440014414230200545025050841020800410020600820205414161405450525014908541421050828021000110021010c040212001202110004140048004404204044440104041101048401110

def d215 := unpackCases dict215 8

def u215 := unpackShort dict215 8

def s425 := certify 215 5 ([w20,i7,i6,i0,i1,i4]) cs215 [] (u215 4 60 0x58c94b26ff873e73a844bc93b25ef9dfee709400882066c93f27bf9a3e97b12411164409762802003491257b1e)

def w129 : Sig := 0xfffffffffffffffffffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0

def s426 := certify 215 6 ([w129,i7,i2,i6,i0,i1,i4]) cs215 [s425] (u215 4 75 0x1184f2134232105e2f239d422458876085a2d13074e1d085a2d17384a0044102a58a7600562b03574bfd00562b033586185e4179188634f58d484a6a)

def w130 : Sig := 0xfffffffffffffffff0f0f0f0f0f0f0f0

def s427 := certify 215 5 ([w19,w130,i2,i6,i0,i1]) cs215 [] (u215 5 60 0x91310e605c5811c728200110405498a7300e2a01c70450c663398861ccc69bcf5c25815815405400c318732388b8b84684)

def s428 := certify 215 6 ([w130,i7,i2,i6,i0,i1,i4]) cs215 [s427] (u215 5 81 0x4309e208514c438e504489887302b2c0b6db029c704500088202a4c5398055500552a95818cc7f15709708610634de7962ae12e12c0ac0aa02a00618cf8858859a)

def s429 := certify 215 5 ([w14,w85,w124,i0,i1,i4]) cs215 [] (u215 3 60 0x105e2f44178bd1309e9dc1542168b4885a2d248e21f03a1d40a8110400562b00158ac1538a7c891c2859b243558d3)

def s430 := certify 215 6 ([w85,i7,w124,i6,i0,i1,i4]) cs215 [s429] (u215 4 78 0x8c279082f17909a119082f1791cea1122c43b042d168983a70e842d168b9c25002208152c53b002b1581aba5fe802b1580ccd14d88631a7ab6a428b2086a)

def s431 := certify 215 6 ([w14,i7,w124,i2,i0,i1,i4]) cs215 [s429] (u215 3 78 0x82f17a2064968984f4ee0aa10b45a442d169106512491c43e0743a8150220800ac56002b1580064660a9c53e0bd05e8178b094e3231a6191f86542cd85da)

def s432 := certify 215 6 ([w73,i7,w124,i2,i0,i1,i4]) cs215 [] (u215 5 75 0x975c20854421c72820565810565816db60538e08a001104002aa8002aa802a954ac2e12e11668a68a3198da28c109e21891439862a54e610618d3198)

def s433 := certify 215 6 ([w19,i7,w124,i2,i6,i0,i1]) cs215 [s427] (u215 3 74 0x91c43e10b45a442d16911acee5dc154022082a714f802b15800ac5600833780743a8156c1192f3109e990d30b88c9623817a0bd046531190c5e82f4a)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s434 := certify 215 7 ([w124,i2,i6,i0,i1,i4,i7]) cs215 [s426,s428,s430,s431,s432,s433] (u215 5 231 0x742085204ae9f311420920821931924c4f304110220851bae40dd714441300b62a0db083028229480e10239409412012721244ca0c9cd08730230d210445961a6cb080829b841166cb26f658590822802ae19154ac8ac00c0441c500704004510526e000119c29299c8210004d40549881935414e60064940008aaa92d55100012500032d55496aa8ca000c18614d729859b0518561cba3344345174a6932d14415711709e0977970840861d4c2e904174bad3859d566886d147929a29b4510ca)

def w131 : Sig := 0xffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0000000000000000

def s435 := certify 215 6 ([w131,i7,i2,i6,i0,i1,i4]) cs215 [s425] (u215 4 81 0x4613c84c12c841389c8e750891621d822491c42c22442148a45ce128011040a9629d802691400c0cc008400c1fe18630fd857218492932d63c5b053b210a)

def w132 : Sig := 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0000000000000000

def s436 := certify 215 5 ([w14,w87,w132,i0,i1,i4]) cs215 [] (u215 4 54 0x163252c9cea112f24ecb9c2500220819b24fc9044591025d8a00801123c20d8212c9812245806240a)

def s437 := certify 215 6 ([w87,i7,w132,i6,i0,i1,i4]) cs215 [s425,s436] (u215 4 78 0x163252c9bfe1cf9cea112f24ec97be77fb9c2500220819b24fc9efe68fa5e3cc9044591025d8a00800c8f58fc8b14d1623ec821108443300cc1695964a)

def s438 := certify 215 6 ([w14,i7,w132,i2,i0,i1,i4]) cs215 [s436] (u215 4 75 0x1304b21184f239d4208924710b089124588767384a004410009a4500303302a58a7615c861214f123c4a4c2e89c82720a44291401002303fc284ca)

def s439 := certify 215 6 ([w19,i7,w132,i2,i6,i0,i1]) cs215 [] (u215 3 74 0x123887c22491c88d6772ee0aa011041538a7c02691401066f00e87502b82325e6213d0278171c8e4464b2ba18505242920880441a096232588c4e8274a)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s440 := certify 215 7 ([w132,i2,i6,i0,i1,i4,i7]) cs215 [s435,s437,s438,s439] (u215 4 231 0xec84520543b5988d44209484609d8251393d8420c443750846e31108c54255042e209d415082124e449160a593914a1d82642c42b0b4930b1691ec2128055188ccaaa19a862018921ca038401290a42c00119c527339044004d40a9641935829d80649c00b0ac9b2715916c00618c51d5584ce14c568f3e55bdab6945d50bec57243482f86984962174bb261d585db5b043c28eaac14f0a21a84e51139102413a044e428905259148a16214c2c5222c8a0658024e0849e003280bb8b31d66e8)

def s441 := certify 215 6 ([w14,i6,w85,i2,i0,i1,i4]) cs215 [s429] (u215 5 78 0x25d70824d30823510871ca08159604159604151404c169c2d38e08a001104002aa8002aa800104006ab4bf6ae12e10891c8ca6b34b352128a68bac7cc2846)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s442 := certify 215 7 ([w85,i2,i7,i0,i1,i4,i6]) cs215 [s430,s426,s441] (u215 4 231 0x30cc6d0ff4991f8ff46330cc63ab1879630ea6309484309cc251393cc420ec84d20743b6188f44220484288bc5e81178bca2421ec46d30a4c7b1497cc235042e209d415082124444c1d08751110b8742d43c42b0b45b0f168b6c2143c422c8b45b0f168b4b221180356406a6819806121ca038401290a43c00119c5293390440038c0d5d0cf4e319aff40d4a400b0ac5729158aec004a400328ac5729158acca00634baa659862e9985361ac617d85e486905f0d1792c4d10f45db58ba5d90cec868)

def s443 := certify 215 4 ([w113,w34,w126,i7,i6]) cs215 [] (u215 3 40 0x65a92d9189e8942340984d9f61f0fad611e68a3678b27d6a1b68b47b927a00452)

def s444 := certify 215 5 ([w34,i0,w126,i7,i1,i6]) cs215 [s443] (u215 4 57 0x65a92cc6d317cd915ae3d6ae750822491c44313c84508c8678993e45114c4b5d345a24a1280948cfbf796a825094)

def s445 := certify 215 5 ([w113,i0,w126,i2,i7,i6]) cs215 [s443] (u215 4 57 0x6d12cd2930def69057218484313c84508c866c998e3d38f441414d047991460330cc60e9c7a11248e273893d)

def w133 : Sig := 0x3333030333330303333303033333030333330000333300003333000033330000

def s446 := certify 215 5 ([w133,w126,i2,i7,i0,i6]) cs215 [] (u215 4 57 0x6d12cc351a998d5d2ff40269140c5728dd2930def6908f72ddce49895ce1b8edc231f4c080042d1af422392444)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s447 := certify 215 6 ([w126,i2,i7,i0,i1,i6]) cs215 [s444,s445,s446] (u215 4 180 0x2598da1fe8963f25e8c63d88da61498f6292f9846888983a10ea222170e85a34884816924d22d23a042a265c413a82a12ce43006ac80d4d03300cb380023388f2672088007181aba19e9c6335fe81a6d800815934a62b22a00024394070802521463ee4644988619f66d23c4b7dfb4fbd12d0817a0ae41e905e3d30910412908613984a272798841d909a42a8765b11e884)

def w134 : Sig := 0xffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0000000000000000

def s448 := certify 215 6 ([w134,i6,i2,i7,i0,i1,i4]) cs215 [s425] (u215 4 81 0x4d08c841389c841389c8e7508c1d387422491c42148a442148a45ce128011040d5d2ff4026914008400084005721849ef691654207e53422d8d634652b1a)

def s449 := certify 215 6 ([w14,i6,w87,i2,i0,i1,i4]) cs215 [s436] (u215 4 75 0x104e27213423239d42089247108522913074e1d7384a004410009a450021003574bfd15c861214d08b0fbda2ee084b2604891600330587f8c28546)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s450 := certify 215 7 ([w87,i2,i7,i0,i1,i4,i6]) cs215 [s447,s448,s437,s449] (u215 4 231 0x10cc6d0ff4b31f8ff46309484309cc251393cc420ec84d20743b2188f4421ec46d30a4c7b1497cc235042e209d415082124444c1d08751110b8742d1a44240b492691691d021180356406a6819806121ca038401290a4ec00119c52b3390440038c0d5d0cf4e319aff40d4ac0040ac9b2b15915000313323224c430c5d30bd05720f482f1e984882174bbed10f45d4207e751f988661f9e47e621990251289102421a04a6428904259108a76210cec4222c886665198256019cac6603280bb93510e1f6)

def w135 : Sig := 0x5555555555555555555555555555555555555555555555555555000055550000

def s451 := certify 215 5 ([w135,i7,i4,i6,i1,i2]) cs215 [] (u215 5 60 0x66e8f1d22ae5a5c7b9572e550892470a27a367462b8f3727e55ca95742ab1a39a13dc70ab13801149a0004108033455e8a380398155ba55)

def w136 : Sig := 0x3333333333333333333333333333333333333333333333333333000033330000

def s452 := certify 215 5 ([w136,i7,i4,i6,i0,i2]) cs215 [] (u215 3 60 0x12e97489b51fcb7e5e8de9a370269142271336a458bca3e9f8de8237b58dc3237e4993fb86e23e223924808204cc7d36a71750dd8e37)

def w137 : Sig := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0000

def s453 := certify 215 5 ([w137,i7,i4,i6,i0,i1]) cs215 [] (u215 4 60 0x4bc93b247a3e86575ef9dfe00882066c93f28ac54af437bf9a3e97b1258c89f26ff847e111c449011404d348ff221116575791be)

def s454 := certify 215 6 ([w15,i7,i4,i6,i0,i1,i2]) cs215 [s451,s452,s453] (u215 1 75 0xfe7f1285c128b728251a8d1d8253209049762491e8fab995b42198e898f345909a4508820ab088110088dd19853032b2592191281c4a272793c76191188c0a0b)

def s455 := certify 215 5 ([w19,w16,i6,i0,i1,i2]) cs215 [] (u215 3 60 0x1fcfe250b87c3e1ba22491c88fab921b8dc63404d2280110401561102a956862633193ea046391c91dc8d606f041b31cce68823a)

def s456 := certify 215 6 ([w16,i7,i4,i6,i0,i1,i2]) cs215 [s455] (u215 5 81 0x3f9fe458845b94879e68a0892470823eae425684141b6d81401348a000110400156800800020552a95818cc7f1524c4f27d14a299442c42c14014006406430d27c2093217a)

def s457 := certify 215 6 ([w19,i7,w17,i6,i0,i1,i2]) cs215 [s455] (u215 1 78 0x7f3f8942e17048242e8d468ec120945b94131248f47d5cc21a10cc710cada7384d2284410558441980cc6e8cc0880440e733992c4a271293c9e3b2988c46050289c860b)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s458 := certify 215 7 ([w17,i4,i6,i0,i1,i2,i7]) cs215 [s454,s456,s457] (u215 5 231 0xd10f14b3cd2cd1441522c7f57907f908915eb2c512089bc45a07c72cc410815962e904204820bab2d805b1506d8418141146908222c249a6c2390104e70829283eb9e85cc8105340ad738414c104e782073c10164209ce104598202802ae19154ac8ac00c1d20004544d74d44520001ce000119c27499c8210003a400244156e941090001d282130003a4002641074e59194001d200065cb26246494af29857b05485664a23753745144ae933d1531521d6428cd3144a24f7e9d44e887d14792ba29f4510ca)

def w138 : Sig := 0xccccffffccccffffccccccccccccccccccccffffccccffffcccccccccccccccc

def s459 := certify 215 5 ([w19,i7,w138,i6,i0,i2]) cs215 [] (u215 2 57 0x9d4ea1cbe391c88c1257861809a450d96c97d0e10440419bc0743b02a5f64a6cbecf8258892475b17d2359dd03c1e1580b)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s460 := certify 215 6 ([w138,i4,i6,i0,i2,i7]) cs215 [s459] (u215 4 180 0xd23cab7b56d290a43d93a5f42750e84397ec5f17a0ae41e905e3d309104500aa311995543350c4031cf800815936a22b22a0002f81b2878364bf02fa1c087243940708025214a8800280aa3080800c17f3aa57ab0afa7a8bea1d908acda8765311a884129085f56b3c4aad1297c8418886ea108dc622118a84a40843d1692502d238f4422f88c251498be292f89442a085c413a82a10424)

def w139 : Sig := 0xffffffffffffffffffffffffffffffff0000ffff0000ffff0000000000000000

def s461 := certify 215 5 ([w19,w139,i6,i0,i1,i2]) cs215 [] (u215 2 60 0xfe7f1285c7239118f4af0c311248e91f57291acee81e0f0ac04d228088202ac22020c2203a1d815d8962567c12c05c11c)

def s462 := certify 215 6 ([w139,i7,i4,i6,i0,i1,i2]) cs215 [s461] (u215 4 81 0x7f3f896c57218488c5903d4207a22491c423eae44e75082c224421088440269140011040055c01ce1280c0cc008400251fe04a630fc4a46789484c14c844289c8a)

def w140 : Sig := 0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000

def s463 := certify 215 6 ([w19,i7,w140,i6,i0,i1,i2]) cs215 [s461,s459] (u215 2 78 0xfe7f1285c723911824af0c311248e91f57291acee81e0f0ac04d228088202ac22020cde03a1d81564b25362567c12c048f4123d2da3ca088088c4b1194c464382780b)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s464 := certify 215 7 ([w140,i4,i6,i0,i1,i2,i7]) cs215 [s460,s462,s463] (u215 5 231 0x68878a59e69668a20a9163fabc83fc8448af596b882b89e09778611081300b62a0db083028228d21044584934d84720209fa1052507d7ed0b990209480e10239409412010a00ab864552b22b00307f800115135ff511480007e800046709fe672084000ff00091055bfd042400011071401c1001144146246494af29857b05485742085144ae9331142085128b3e43ac8511046086c14752983cb0510ca20ba47881f084091e177c7e964b213f423abf4a61164240ca800ff0107fa00194028e8463ab9e6)

def w141 : Sig := 0xbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbaaaabbbbaaaabbbbaaaabbbbaaaa

def s465 := certify 215 5 ([w141,i0,w19,i7,i2,i6]) cs215 [] (u215 3 54 0xc7325b24f84bc1309e30e47223847f2df86ed8d804d228020cde09c9c116c6c22392488ee6b24e4e)

def w142 : Sig := 0x1111111111111111111111111111111111110000111100001111000011110000

def s466 := certify 215 4 ([w33,w142,w19,i2,i6]) cs215 [] (u215 4 37 0x937095c351a9992930c8f72ddc391c88e0231f4c2239244bf14000e708e)

def s467 := certify 215 4 ([w34,w142,w19,i7,i6]) cs215 [] (u215 4 34 0xc73259926e12b86e231f4c23b9ac5471114001a8d4d61c8e4470e708e)

def s468 := certify 215 5 ([w142,i0,w19,i7,i2,i6]) cs215 [s466,s467] (u215 4 51 0x18e64b324dc2574a4c30e47223423dcb770dc6a35332083cc20232988f9c238463e984472488477358a8e0)

def s469 := certify 215 4 ([w34,w33,w127,w19,i6]) cs215 [] (u215 3 37 0x93e12f3c5993e4c7d6423b9ac888e4921bf32f82613637a3f997c00458)

def s470 := certify 215 5 ([w33,i0,w127,w19,i2,i6]) cs215 [s469,s466] (u215 3 54 0x127c25ec66c0984f191fcb7e1c8e44704c7d6223924908f26f223b9ac9b1b0df053865f32f806fccbe)

def s471 := certify 215 5 ([w117,i0,w127,w19,i2,i6]) cs215 [] (u215 3 51 0x93e12f04c278c8fe5bf131f5888e49240088111dcd64351ab601348a0c5e51f1cd896c391c88e06e6f)

def s472 := certify 215 5 ([w34,i0,w127,w19,i7,i6]) cs215 [s469,s467] (u215 3 51 0x63992d927c25e1b931f588ee6b2423c914888e492678b27c8b6d2991597ccbe00984d82e391c88e11fccbe)

def s473 := certify 215 5 ([w61,i0,w127,w19,i7,i6]) cs215 [] (u215 3 51 0xc7325b24f84bc37263eb11dcd6480110222392486a356c0419bc18bca3e0984f18723911c23f96fc45)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s474 := certify 215 6 ([w127,w19,i7,i0,i2,i6]) cs215 [s465,s468,s470,s471,s472,s473] (u215 3 162 0x96cc231f9cc963f2588d995ac93e12f2b44a25e6ec0b84da027918c17611c0e496171c88c2e2325c43ae11fc3de758f56fd1cc035c088d5822d818f900815935ae2b22c002cc00463341a64666f118032c22c5e0e65828f823d2d968dc4a44c296128a4fac4c3d2281691c7a2d24c11010044f21102980448846452d109dc46213596c88b65b4)

def w143 : Sig := 0x3333333333333333333333333333333333333030333330303333303033333030

def s475 := certify 215 5 ([w143,i2,w19,i7,i0,i6]) cs215 [] (u215 3 57 0x31cc96c93e27f0d46ad8083378317947c04d2280dd2e97c61c8e446bb47f187b1b1802204477359273af888e492)

def w144 : Sig := 0xfffffffffffffffffffffffffffffffffffff0f0fffff0f0fffff0f0fffff0f0

def s476 := certify 215 6 ([w144,i2,w19,i7,i0,i1,i6]) cs215 [s475] (u215 3 71 0x18e64b66b793d9b318dac5f62359dc9d6eba48bc892472299116c6a356c02208020cde14ba58be9204d22804400221b40a63630e472231e8bc7a618)

def w145 : Sig := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f00000f0f00000f0f0000

def s477 := certify 215 6 ([w145,i2,w19,i7,i0,i1,i6]) cs215 [] (u215 5 74 0xc73258c35bc9e31b462f8c11acee13add749b82b2c0b4d0630008820008337814ba5dd4902aa8069248c1a225c4415ee23e1be182b02b00a80a897112e213c)

def w146 : Sig := 0xffffffffffffffff0000000000000000ffff0000ffff00000000000000000000

def s478 := certify 215 6 ([w146,i6,w19,i7,i0,i1,i2]) cs215 [] (u215 3 74 0xe4722382ba18502613c681e8f608924722359dcbb82a86d62fb10a452404d2280110401066f00e87502a351ab605c6e214c2325b3213c96232588c4e25)

def s479 := certify 215 5 ([w135,i6,w19,i7,i1,i2]) cs215 [] (u215 5 57 0xe388888ab969719ba3c74089247082359dc262b8f37227a36742ae87325e9a384f700229340008210001bd06028e00e19a2af4)

def s480 := certify 215 5 ([w136,i6,w19,i7,i0,i2]) cs215 [] (u215 3 57 0x391c88e11fcb7e4ba5d226d02691401066f062f28fa271336a446e6d3992cda93e27f111c9240410223b9ac938b998fa6d)

def w147 : Sig := 0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeaaaaeeeeaaaaeeeeaaaaeeeeaaaa

def s481 := certify 215 4 ([w147,w15,i6,i7,i2]) cs215 [] (u215 4 34 0x723911a14aa527d8ae4309147339e09e601348a0020cde005d6e60e70947)

def w148 : Sig := 0xcccccccccccccccccccccccccccccccccccc0000cccc0000cccc0000cccc0000

def s482 := certify 215 5 ([w148,w15,i6,i7,i0,i2]) cs215 [s481] (u215 2 51 0x391c88c12a55293c2e57861809a4501066f02eb7301d0eca3845300b399cc324fc8924748d67748fba340f)

def s483 := certify 215 5 ([w137,i6,w19,i7,i0,i1]) cs215 [] (u215 4 57 0x2359dc48f47d0cae97927640110400419bc1158a95e86cd927e5e91cc97292c49f2111c449011404d408c72392111657348ff2)

def s484 := certify 215 6 ([w15,i6,w19,i7,i0,i1,i2]) cs215 [s455,s479,s480,s482,s483] (u215 1 71 0x723911824128b72824fe7f1285dae0904b6e2491e8d67795b4b38fab993345b09a450882083378110088ab08879038864a605399cc9625138949e07)

def w149 : Sig := 0xccccccccccccccccccccccccccccccccccccffffccccffffcccccccccccccccc

def s485 := certify 215 5 ([w149,i6,w19,i7,i0,i2]) cs215 [] (u215 2 57 0x391c88c125786189d4ea1cbe09a4501066f01d0ec0ab65b25f43841100b2f9cc965f67c12c44923a46b3ba0783c2b362fa)

def w150 : Sig := 0xffff0000ffff0000000000000000

def s486 := certify 215 6 ([w150,i6,w19,i7,i0,i1,i2]) cs215 [s461,s485] (u215 4 71 0xe47223415c86121fcfe25b089247108d677139d4208fab91009a45000441001066f07384a01570028e673258959e252207a81e96c47914010014c4e6)

def s487 := certify 215 4 ([w147,w18,i6,i7,i2]) cs215 [] (u215 4 37 0x391c88d12930c6331e0c42b98484508c84fe709001348a0020cde01a8d4cc)

def s488 := certify 215 5 ([w148,w18,i6,i7,i0,i2]) cs215 [s487] (u215 3 57 0x391c88e02613c602691401066f01a8d5b008a60633186590ae6140e8750229423427f71211248e446b3b924d26ad6)

def s489 := certify 215 6 ([w18,i6,w19,i7,i0,i1,i2]) cs215 [s488] (u215 4 74 0x723911a108b72a252618449238846b3b895a2114cda62f9804d22800220800833782000406a35333061192cccf139ac8b2042910a410040464b1192c825)

def s490 := certify 215 5 ([w20,i6,i7,w19,i0,i1]) cs215 [] (u215 4 57 0xe750821c88449792764011041ce12801c8cc0cd927e5e92c54b290e49724097628020041116440e4963934912)

def s491 := certify 215 6 ([w14,i6,i7,w19,i0,i1,i2]) cs215 [s490] (u215 4 74 0xae4309104bb22c8458a68436c4492389cea1044b10884291488429148804d22800220839c25004b19801080010800827139302313904e4258fc866)

def s492 := certify 215 6 ([w73,i6,i7,w19,i0,i1,i2]) cs215 [] (u215 4 74 0xae43090723911a2c84584492389cea1046b3b88429148804d22800220839c250083378010801427209c8731f88d16458522148a008004e41390966)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s493 := certify 215 7 ([w19,i7,i0,i1,i2,i6]) cs215 [s474,s476,s477,s433,s439,s478,s484,s486,s489,s491,s492] (u215 6 228 0x8528306ada27dcab329f4a8488306aba60c1aaa11204a9a64939f2103046b8c2c49b618412598c1031b618b0684884386dca2ce18688b226dca102132b84566d847813c2e7981b610404b5e816cb419406b5e945eb418106b5a0102b421648b5a1646b420102b568102b48906ab569076b488102b45290eb41010eb450114b412d04e018034e030834e018806e03000ce1c0000e02154ce1c1544e020000b568000b40b302b5c3340b408000e1c0000e089920f87065bb82200038042073814007380400138142052821680a)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s494 := certify 215 6 ([w127,i4,i7,i0,i2,i6]) cs215 [] (u215 5 180 0x5e46b5edf6d79fa9fb0db18b2431091841832c330485eecb6cc15a9bb11b3ac8479de1cebf16e71070c068621a0c80c60066940008a89b5da88a40005dc09fed96d77ca83b01b32d0629c01ccb014672074871c32b52722b6418e3ba38eda5bb745b8b638e902086a069283e8c10de04111611fcb0924041001008575002ba020105d0456d06dd40c7d82d8b7008704716c208e80e)

def s495 := certify 215 6 ([w127,w19,i4,i7,i0,i2,i6]) cs215 [] (u215 5 74 0xcc94d8c34920c92460c8d46f4411e78411e78469a0c6004d228003772010000410000436906906ea5b11c10c7d1822392420100020a0638500414059)

def s496 := certify 215 6 ([w18,i6,i4,i7,i0,i1,i2]) cs215 [] (u215 4 81 0x8d468ed0845b9512930c22491c4263a244ad108426d317cc026914001104006e8cc100020351a9983bc08c46cf309cc6331e0d64590214885208020a50ef04210c4e25)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s497 := certify 215 7 ([w19,i4,i7,i0,i1,i2,i6]) cs215 [s457,s463,s494,s495,s454,s496] (u215 5 231 0x9b186ebe64a6fe4df430cf91863ac9235e490ea30c62c90c42461060cb0dd108d4dac8de96e936410512086df9e207cf0a2410812082ef9e207cf0ba4107b08da35031ee82f8c10c6908222c249a6c23901045b082ea06396e083a0822dc1016c208b61045b8202dacd32590822d841164b659180d0c43419018c00c38800115134e3511480002d800046708e267208400071000eb26e9c72cba00038a081c4000e20007141038a08194000e20006541042944a90f320c511a429c831446e887d144a2512894628b90c4)

def w151 : Sig := 0xffff0000ffff0000ffff0000ffff0000

def s498 := certify 215 5 ([w20,i6,i7,w151,i0,i1]) cs215 [] (u215 4 57 0xbdf3bfc9792764011040f7f347ccd927e4e7509ce1283958c94b222116497b124097628020057b1e34912)

def s499 := certify 215 6 ([w14,i6,i7,w151,i0,i1,i2]) cs215 [s498] (u215 4 74 0x118b22c8458a6844bc44923885844884291488429148804d228002208018198010800108008573091cea139c2509641389c841389c8ac0fd426)

def s500 := certify 215 6 ([w73,i6,i7,w151,i0,i1,i2]) cs215 [] (u215 4 74 0x3ded2ac845844923886e3718a8429148804d2280022080aa5550c4108008573091cea139c2504641389c841389c8631fa916458522148a0080306)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s501 := certify 215 7 ([w151,i7,i0,i1,i2,i6]) cs215 [s499,s500] (u215 4 228 0x21e0c633ca87e6329e07f821a8c640b2d297991240b10c979ac640e91e97aade40eada97a90a429ec46d4298526429ec525f429846429a44242a05a49429a45a4742a042428c443742a84237428c4423142a84a4a980354ab20354a9a064ab00c4aa54004aa0564d4aa5456454aa00042a14004288ce242a54ce414288004aa80554a8c466554aa866a4a8c4031288948428984e6288944e4f289884288f48428a05e57288f45e6128a08442888e428868e428a9442884844a829c4ac09c4a80844ac29428944b623)

def w152 : Sig := 0xffffffffffffffff0000ffff0000ffffffffffffffffffff0000000000000000

def s502 := certify 215 6 ([w152,i6,i4,i7,i0,i1,i2]) cs215 [] (u215 4 81 0x8d468ed057218496422d0d4221a22491c4263a244e75082148a442148a44026914001104006e8cc1ce12808400084004a28ec841389c841389c981de076652b03b)

def w153 : Sig := 0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s503 := certify 215 7 ([w153,i4,i7,i0,i1,i2,i6]) cs215 [s502] (u215 5 231 0x13630dd7cc94dfc9be8618c59218848c20c1961ba211a9b591bd2dd26c822e20ae27825de18442043d846d1a818f7417c608634841116124d3611c80828b84175031e2f041d0412901c20472812824020c068621a0c80c60064040008a89b01a88a400045c00023385013390420008080075937603965d00008838a00e08008a20a4820834c349313c6104289468bd10fa288827c75f86218df14fe188632c5d5884090b205620ba440598028b85045e008b216465c8080819407200ca01474e510cb65b)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s504 := certify 215 6 ([w120,i6,i7,i1,i2,i4]) cs215 [] (u215 3 180 0x3b44a21d0ec8623a4412a2309d84a2727b2200543a1140e8220442a1517c15d07a82f1e9852103701fa0b87c36170dd45605c26d013c8c60bb0ae09a0c3015bd48a1001510f21705482a8214349140b492691691e08862437a108dc622118d151ec8dac2963d8a4bec4c672208c819dea4102021b3510e8ea4350d3304706a0c3508b30665015462332ad0ce862031)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s505 := certify 215 6 ([w100,i6,i7,i0,i2,i4]) cs215 [] (u215 3 180 0x3b44a21d0ec8623a4412a2309d84a2727b221270842bc4150a885105f05741ea0bc7a614840dc07e82e1f0d85c3751581709b404f23182ec2d82491a485a692394120443a1500ea020542215618040ac9af51591600280aa3119956867431018b00d702235608b606464008ce4f53390480112cd443a4490d434cc296623d9b4527b2f9330c486f4211b8c44231a2a)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s506 := certify 215 6 ([w101,i6,i7,i0,i1,i4]) cs215 [] (u215 3 180 0x3b44a21d0ec8623a4412a2309d84a2727b220f51205e571e8bcc30881510f21705482a82141890de8423718884634547b236b0a58f6292fb131a48a05a49348b48f0448110e85403a8081508856320046727a99c824014055188ccab433a1880c5806b8111ab045b031860102b26bd4564580021b3510e8ea4350d334304c2f8138cc0bb306e03f4170f86c2e1ba8a)

def w154 : Sig := 0xffffffffffffffffffff0000ffff0000ffff0000ffff0000ffff0000ffff0000

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s507 := certify 215 6 ([w154,i6,i7,i0,i1,i2]) cs215 [] (u215 3 180 0x1b80fd05c3e1b0b86ea2b02e136809e46305d85f05741ea0bc7a61484349140b492691691e08862437a108dc622118d151ec8dac2963d8a4bec4c1510f21705482a8214618040ac9af515916002320046727a99c824014055188ccab433a1880c5806b8111ab045b0310221d0a80750102a110a92d9aaf744bbda869984ecc8254138949e8c83b44a42d0ecb623a44)

def s508 := certify 215 6 ([w154,i4,i6,i7,i0,i1,i2]) cs215 [] (u215 5 81 0x79e68a49230623cf0823cf080892470b6db028da317c68020a08020a0009a4500008820154aa561a68318800020800020314a11869241ba2ba2a41a4184e8ae8a)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s509 := certify 215 7 ([w104,i6,i7,i0,i1,i2,i4]) cs215 [s504,s505,s506,s507,s508] (u215 3 231 0xed1288743b2188e9104a88c2761289c9ec8843442890ca2d721acca2882f82ba0f505e3d30a4206e03f4170f86c2e1ba8ac0b84da027918c17621c4174865d6190d325d880a88790b82a415410a1a48a05a49348b48f0443121bd0846e31108c68a8f646d614b1ec525f6268e911663a598e90cf259224088742a01d4040a8442b1b00815936362b22c00474008ce51b3390480280aa3119956867431018b00d702235608b60646c00cb1b32c6c8653328010d9a88747521a8487310c90e063f)

def w155 : Sig := 0xfafafafafafafafafafafafafafafafafafafafafafafafaaaaaaaaaaaaaaaaa

def s510 := certify 215 5 ([w155,w14,i6,i7,i1,i4]) cs215 [] (u215 4 53 0x4c12c841389c841389c8e75082c22442148a442148a44201040ac0fd426e70940606600420004200)

def w156 : Sig := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000

def s511 := certify 215 6 ([w156,w14,i6,i7,i0,i1,i4]) cs215 [s425,s510] (u215 4 74 0x98259082713908271391cea105844884291488429148848d48b9c2500220801819801080010800083c81581fa84c8239488c5916422c53)

def w157 : Sig := 0xafafafafafafafafafafafafafafafafafafafafafafafafaaaaaaaaaaaaaaaa

def s512 := certify 215 5 ([w157,i0,i6,i7,i1,i4]) cs215 [] (u215 4 57 0xdff0e7cb192964e7508bdf3bfc97927652f6244a129011044af2bc691a40250944097625795e348d2)

def w158 : Sig := 0x505050505050505050505050505050505050505050505050000000000000000

def s513 := certify 215 4 ([w113,w158,i6,i7,i4]) cs215 [] (u215 4 40 0x6ff873e58c94b297b12411164a0fb1eb491240200e708212a9555e1a8d4d2)

def s514 := certify 215 5 ([w158,i0,i6,i7,i1,i4]) cs215 [s513] (u215 4 57 0xdff0e7cb192964e7508bdf3bfc97927652f625ce1280114c0552aabc351a9a48222c8812ec431f63d692250)

def s515 := certify 215 5 ([w113,i0,w20,i6,i7,i4]) cs215 [s513] (u215 4 57 0xdff0e7cb1929652f6248222c8af63c692248299050812ec44799146b5f2d7d3394ce407388215ef96be4bca672)

def s516 := certify 215 5 ([w123,i0,w20,i6,i7,i4]) cs215 [] (u215 4 57 0xdff0e7cb1929652f6248222c8af63c6922500400812ec5ce128f7f347ccd927e4e7508bdf3bfc979276441)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s517 := certify 215 6 ([w20,i6,i7,i0,i1,i4]) cs215 [s512,s514,s515,s516,s490,s498] (u215 4 180 0x4691bfe7cf91ad71cf89e3f9163213c8fe2752c892a085c413a82a10424bf897be10fafe2177f85ebe892f214cafa294ec852243940708025214598002338932672088005a81efe19f96a3368f81e99819b284a6704fc812c4a5e1ffb03fc7a5213a1041e904e3d45910414a102348852695d8902822003c8205380100c215eb7b16c791e1fd8d24487e844ad2)

def s518 := certify 215 6 ([w20,w14,i6,i7,i0,i1,i4]) cs215 [] (u215 4 74 0x98259082713908271391cea105844884291488429148b9c2500220801819801080010803d81fa8648222c8812ec5004008b6116422c5d)

def s519 := certify 215 6 ([w20,i2,i6,i7,i0,i1,i4]) cs215 [] (u215 4 81 0x4d08c84613c8e7508c1d387491621d822491c5ce128011040d5d2ff4a9629d80269140cd6185721849ef6b129307e27209c82910a4500400a5634630fd88)

def w159 : Sig := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000

def s520 := certify 215 6 ([w159,i4,i6,i7,i0,i1,i2]) cs215 [] (u215 4 81 0x8d468ed07f3f896c572184822491c4263a24423eae44e7508026914001104006e8cc0055c01ce128c964e04a4a28ec8467894881ea07a211084500400a56076630fc4a27)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s521 := certify 215 7 ([w14,i6,i7,i0,i1,i2,i4]) cs215 [s511,s426,s517,s518,s519,s431,s438,s441,s449,s454,s520,s491,s499] (u215 4 231 0x26c84c60f09bc092f0422bc841f89c4eaf1389c7e4256c842889c4f591389ca2420bd05720f482f1e98488255d08c5b155b5b08454ed61fa10f94207f6b35d66992ea1079420ba532ed042e209d415082121a44240b492691691d02147c42c08711f10a27021414421f8a45305148a47e21414422c8a45305148a4b221121ca038401290a3b40040ac9aed1591500041400119c4ed339044003b400c0cf0ed198cf0003b4001fc20ed8407e003b40032c20ed840ca0040ceaac10f0751f8fcea4350cc4866)

def w160 : Sig := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0

def s522 := certify 215 6 ([w160,i2,i6,i7,i0,i1,i4]) cs215 [] (u215 5 81 0x8544208613c438e504db6c0a489887302b2c082b2c09c70450008820154aa560a9314e601554001554018cc7f15709708d14d14610634d6b84b8468a68a18633e)

def w161 : Sig := 0xffff0000ffff0000ffff0000ffff0000ffffffffffffffffffff0000ffff0000

def s523 := certify 215 6 ([w161,i4,i6,i7,i0,i1,i2]) cs215 [] (u215 5 81 0x1e79a28fe7f9162116e52162085822491c2db6c0a08fab9095a1050401050004d22800044100aa552b001568008000219000646331a6cae8ae8a9262793c4e8ae8a18693e)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s524 := certify 215 7 ([w73,i6,i7,i0,i1,i2,i4]) cs215 [s522,s523,s432,s492,s500] (u215 5 231 0x3a10429ae574b388a104578827d34caf9a6f8412e20ae27825de184420468878a59e69668a20a3aacb7c41099208f9659480e10239409412010d21044584934d8472020b00b62a0db08302822a06105f51440e8a3e08211071401c100114414838001151360f511480008180004670a0e67208400050055c322a95915801841c003e41083a087c000752198cebf7c510ca98a3308751263ccc2144420ba42c755882990b1756a0b3405030a881d01164240ca8010701083a0019403ac15821c746)

def s525 := certify 215 4 ([w113,w33,w128,i6,i2]) cs215 [] (u215 3 40 0x1309e315d0c28391c88e0c6636c4627a3cd114644923936357fb917e00412)

def s526 := certify 215 4 ([w34,w33,w128,i6,i1]) cs215 [] (u215 4 40 0x3698be673a8411ad12211248e23198cc9f2189e4a1094948d5f250940008a8)

def s527 := certify 215 5 ([w33,i0,w128,i6,i1,i2]) cs215 [s525,s526] (u215 3 57 0x2613c62ba1850723911c11248e46d62fb7705508d68923198db1189e815440a9be0f306f229936357d02a8150)

def s528 := certify 215 4 ([w34,w113,w128,i6,i7]) cs215 [] (u215 2 40 0xc6630ce80b11c989f11ad12b3c727c1e0f93d008a87239118242613c178f38a3)

def s529 := certify 215 5 ([w113,i0,w128,i6,i7,i2]) cs215 [s525,s528] (u215 3 57 0x723911c04c278c57430a18cc61964a11a2313d08307982088ca62366cb623cd146044923911ad124d8d9dc93d)

def s530 := certify 215 5 ([w34,i0,w128,i6,i7,i1]) cs215 [s526,s528] (u215 4 57 0x235a2446d317cce750822491c46331e0c4508c84313c84511e4445b694c8a678993e4a12801c8e4468948d625094)

def w162 : Sig := 0x3333000033330000333333333333333333330000333300003333000033330000

def s531 := certify 215 5 ([w162,w128,i6,i7,i0,i2]) cs215 [] (u215 3 57 0x1c8e44701309e323f96fc04d228020cde0351ab6317947c6331865b86e23ee49897888e492008811064d644c7d64)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s532 := certify 215 6 ([w128,i6,i7,i0,i1,i2]) cs215 [s527,s529,s530,s531] (u215 4 180 0x11a0738b0e447611e10865a464498861ac617a0ae41e905e3d30910434884816924d22d23a0428f88423109ae3e214488c423d88da61498f6292f9846a2cdc413a82a1232461800815935322b22a0008c80023388f267208800218002319a0ca6333788c003006ac80d4d03300c243940708025214c18c623c298f185c08cc611909842a8465b11e08412908613984a27279884)

def s533 := certify 215 5 ([w162,i4,i6,i7,i0,i2]) cs215 [] (u215 3 60 0xbd1bd346e1309e323f96fc04d2284fc6f411b8d46ad8c5e51f18c6f4f1bf0dc47dc9312f111c92401102a1bb1c6e4c7d64e2e)

def s534 := certify 215 6 ([w128,i4,i6,i7,i0,i1,i2]) cs215 [s533] (u215 5 81 0x11a8de8849230623cf0823cf0808924708263a242368c5f1a008280a610459009a450000882000ddc80d3418c4000104000103198d81ba6228a41a418428ae98906906)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s535 := certify 215 7 ([w70,i6,i7,i0,i1,i2,i4]) cs215 [s532,s534] (u215 4 231 0x26c84c10f09b2192f04209484309cc251393cc420bd05720f482f1e98488210d08c5b0c3b5b08432d23224c430d635042e209d415082121a44240b492691691d02147c42c08711f10a270211ec46d30a4c7b1497cc23121ca038401290a4240040ac9b09159150004c400119c5093390440042400c0cf109198cf000180356406a68198061d48663c10f04331886512890864219e4a642892c5db20868b30ec82ea04259108a62210cc44222c886665198212019c246603280871d510e0a3f)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s536 := certify 215 8 (roots 215) cs215 [s434,s440,s442,s450,s458,s464,s493,s497,s501,s503,s509,s521,s524,s535] (u215 4 240 0xd5e0c63c1a87e63c0e07f8ada8c6ac8ec8428aaaeaaa8eea62328a8847c8948428984e66b8944e4f28988459e91e2eaade4ceada2ea90a3cb2d22e991229b10c2e9ac6288bd0572e907a4408bc7a612891042c8c44372ca842372c8c442312ca84a2c9ec46d2c985262c9ec525f2c98462cd042e2c904e2cd0542c904242c9a4422ca05a492c9a45a472ca04232a8055328c4665532a866a328c4031329803532b2035329a0632b00c32921c32d01c32900432d214329940032a0564d32994564532a0002c964002c88ce22c994ce412c8800)

theorem lower215 : Claim 215 9 := fromSearch 1604 (by decide +kernel) s536.property

theorem lower247 : Claim 247 10 := fromLift 10 32 1348 lower215 (by decide +kernel)

theorem lower239 : Claim 239 10 := fromLift 10 1 25941 lower238 (by decide +kernel)

def cs154 : Cuts (goalAt 154) := []

def dict154 : Nat := 0x881806808120a20a001a10048608800208008808048001210208081202

def d154 := unpackCases dict154 4

def u154 := unpackShort dict154 4

def s537 := certify 154 3 (roots 154) cs154 [] (d154 24 0x1c06641b0a0551433092872)

theorem lower154 : Claim 154 4 := fromSearch 268529728 (by decide +kernel) s537.property

def c218_0 := ruleFor 218 lower200 none (by decide +kernel)

def c218_1 := ruleFor 218 lower202 none (by decide +kernel)

def c218_2 := ruleFor 218 lower154 none (by decide +kernel)

def c218_3 := ruleFor 218 lower210 none (by decide +kernel)

def c218_4 := ruleFor 218 lower202 (some (0,i1,i7)) (by decide +kernel)

def cs218 : Cuts (goalAt 218) := [c218_0,c218_1,c218_2,c218_3,c218_4]

def dict218 : Nat := 0x8001600048000e0002800048242260004810228008802161004a40148001a0004820521040010988020828d00030800c00216020981804a004a0012008580030108821022820880a300410003161404a0a12908581820802000040008881006808120a148085242149401a10048604818301404a08120288800300001a1806828881830100c08020a010000400048880048008808208084800121001210120201202

def d218 := unpackCases dict218 7

def u218 := unpackShort dict218 7

def s538 := certify 218 5 ([w63,i3,i6,i1,i4,i7]) cs218 [] (u218 3 53 0xa1d0022d001f1f04343acee0172922724212144212142a1ba19caca1f01f0263f11caca)

def s539 := certify 218 4 ([w64,i3,i7,i1,i4]) cs218 [] (u218 3 40 0x69234f23ee017672365235d85b88591f8823c820630227292a23c2311828)

def s540 := certify 218 5 ([w65,i3,i7,i1,i4,i6]) cs218 [s539] (u218 3 53 0x2c19241223f0372d00c1d001f1f0292272ee01753c51c421214421214a2192111f01f0c116b6)

def w163 : Sig := 0xffff00ffffff00ffffff00ffffff00ffffff0000ffff0000ffff0000ffff0000

def s541 := certify 218 4 ([w163,i3,i7,i1,i6]) cs218 [] (u218 3 40 0x2c2b229227253c51c4312f4ee0158826d2525c63b03900372d00a1d0)

def s542 := certify 218 5 ([w67,i3,i7,i1,i4,i6]) cs218 [s541] (u218 3 53 0x2c1920372d00c1d0292272ee01753c51c4312f4882193b039025c6192192130410174174a11)

def s543 := certify 218 4 ([w127,w19,i7,i3,i6]) cs218 [] (u218 3 34 0x24f2b277e45e882113d3d1d675e73e434271242f31445f5546f)

def s544 := certify 218 5 ([w19,i7,i1,i3,i6]) cs218 [s543] (u218 4 111 0xac42e613caf057c108d446e04501aa2968040141183204616210e18f4ae07bc870acc6f18ec0960f259c80c04921488cc492664e22091c8431098a390979884a109cb2ad2cbfc210082ea11c020294a4a4a)

def s545 := certify 218 4 ([w13,i6,i7,i1,i4]) cs218 [] (u218 3 40 0x83253d25598818ee0177f257d255d85b88251b8607b064794a251b2511868)

def s546 := certify 218 5 ([w14,i6,i7,i1,i3,i4]) cs218 [s545] (u218 2 53 0x365601a9a806a6a0ec1c8c362384761141d9343c3c0bc312f906d5e4333390ccce058d8cc2a)

def s547 := certify 218 4 ([w128,i6,i7,i1,i3]) cs218 [] (u218 3 40 0x3d3d1d6882113b03904312f4455574292272ee01523231b20a1d00372d0)

def s548 := certify 218 5 ([w70,i6,i7,i1,i3,i4]) cs218 [s547] (u218 4 53 0xd158006e5a03b01c80da81908141ce0588625e42695c852227111e852020820681ac4b1158)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s549 := certify 218 6 (roots 218) cs218 [s538,s540,s542,s544,s546,s548] (u218 4 160 0x11fa1119fab0471bac68fd42549840092a4a930c5f24a00248a004846a6f245352d9080089618953550258764189aa328fc50426e0c84111847f88425e31dc809609792ce6403028a221d19643a2acaa308ca2490a6823315124cc9e8220a40b3a5423a4020252b5a88e4250c4263447212fa1884)

theorem lower218 : Claim 218 7 := fromSearch 318857280 (by decide +kernel) s549.property

theorem lower91 : Claim 91 5 := fromLift 5 2 24644 lower89 (by decide +kernel)

theorem lower155 : Claim 155 5 := fromLift 5 1 28740 lower154 (by decide +kernel)

def c219_0 := ruleFor 219 lower217 none (by decide +kernel)

def c219_1 := ruleFor 219 lower218 none (by decide +kernel)

def c219_2 := ruleFor 219 lower203 none (by decide +kernel)

def c219_3 := ruleFor 219 lower195 none (by decide +kernel)

def c219_4 := ruleFor 219 lower211 none (by decide +kernel)

def c219_5 := ruleFor 219 lower91 none (by decide +kernel)

def c219_6 := ruleFor 219 lower155 none (by decide +kernel)

def c219_7 := ruleFor 219 lower217 (some (3,i3,i6)) (by decide +kernel)

def c219_8 := ruleFor 219 lower217 (some (2,i3,i6)) (by decide +kernel)

def c219_9 := ruleFor 219 lower218 (some (1,i3,i6)) (by decide +kernel)

def c219_10 := ruleFor 219 lower217 (some (1,i3,i6)) (by decide +kernel)

def c219_11 := ruleFor 219 lower217 (some (0,i3,i6)) (by decide +kernel)

def c219_12 := ruleFor 219 lower218 (some (3,i3,i6)) (by decide +kernel)

def c219_13 := ruleFor 219 lower217 (some (3,i3,i7)) (by decide +kernel)

def c219_14 := ruleFor 219 lower217 (some (2,i3,i7)) (by decide +kernel)

def c219_15 := ruleFor 219 lower218 (some (1,i3,i7)) (by decide +kernel)

def c219_16 := ruleFor 219 lower217 (some (1,i3,i7)) (by decide +kernel)

def c219_17 := ruleFor 219 lower83 none (by decide +kernel)

def c219_18 := ruleFor 219 lower217 (some (0,i3,i7)) (by decide +kernel)

def c219_19 := ruleFor 219 lower218 (some (3,i3,i7)) (by decide +kernel)

def c219_20 := ruleFor 219 lower217 (some (1,i4,i7)) (by decide +kernel)

def c219_21 := ruleFor 219 lower217 (some (2,i4,i7)) (by decide +kernel)

def c219_22 := ruleFor 219 lower200 none (by decide +kernel)

def c219_23 := ruleFor 219 lower211 (some (1,i4,i7)) (by decide +kernel)

def c219_24 := ruleFor 219 lower209 (some (1,i4,i7)) (by decide +kernel)

def c219_25 := ruleFor 219 lower217 (some (3,i4,i6)) (by decide +kernel)

def c219_26 := ruleFor 219 lower217 (some (1,i4,i6)) (by decide +kernel)

def c219_27 := ruleFor 219 lower217 (some (2,i4,i6)) (by decide +kernel)

def c219_28 := ruleFor 219 lower218 (some (1,i4,i6)) (by decide +kernel)

def c219_29 := ruleFor 219 lower217 (some (0,i4,i6)) (by decide +kernel)

def c219_30 := ruleFor 219 lower218 (some (3,i4,i6)) (by decide +kernel)

def c219_31 := ruleFor 219 lower203 (some (1,i1,i6)) (by decide +kernel)

def c219_32 := ruleFor 219 lower202 (some (1,i1,i6)) (by decide +kernel)

def c219_33 := ruleFor 219 lower195 (some (1,i1,i6)) (by decide +kernel)

def c219_34 := ruleFor 219 lower218 (some (1,i4,i7)) (by decide +kernel)

def c219_35 := ruleFor 219 lower203 (some (3,i1,i7)) (by decide +kernel)

def c219_36 := ruleFor 219 lower202 (some (0,i1,i7)) (by decide +kernel)

def c219_37 := ruleFor 219 lower217 (some (3,i4,i7)) (by decide +kernel)

def c219_38 := ruleFor 219 lower202 (some (3,i1,i7)) (by decide +kernel)

def c219_39 := ruleFor 219 lower195 (some (3,i1,i7)) (by decide +kernel)

def c219_40 := ruleFor 219 lower218 (some (2,i4,i7)) (by decide +kernel)

def c219_41 := ruleFor 219 lower211 (some (2,i4,i7)) (by decide +kernel)

def c219_42 := ruleFor 219 lower217 (some (0,i4,i7)) (by decide +kernel)

def c219_43 := ruleFor 219 lower218 (some (3,i4,i7)) (by decide +kernel)

def c219_44 := ruleFor 219 lower217 (some (2,i6,i7)) (by decide +kernel)

def c219_45 := ruleFor 219 lower217 (some (3,i6,i7)) (by decide +kernel)

def c219_46 := ruleFor 219 lower154 none (by decide +kernel)

def c219_47 := ruleFor 219 lower89 none (by decide +kernel)

def c219_48 := ruleFor 219 lower218 (some (0,i6,i7)) (by decide +kernel)

def c219_49 := ruleFor 219 lower217 (some (0,i6,i7)) (by decide +kernel)

def c219_50 := ruleFor 219 lower218 (some (1,i6,i7)) (by decide +kernel)

def c219_51 := ruleFor 219 lower217 (some (1,i6,i7)) (by decide +kernel)

def c219_52 := ruleFor 219 lower218 (some (2,i6,i7)) (by decide +kernel)

def c219_53 := ruleFor 219 lower218 (some (3,i6,i7)) (by decide +kernel)

def cs219 : Cuts (goalAt 219) := [c219_0,c219_1,c219_2,c219_3,c219_4,c219_5,c219_6,c219_7,c219_8,c219_9,c219_10,c219_11,c219_12,c219_13,c219_14,c219_15,c219_16,c219_17,c219_18,c219_19,c219_20,c219_21,c219_22,c219_23,c219_24,c219_25,c219_26,c219_27,c219_28,c219_29,c219_30,c219_31,c219_32,c219_33,c219_34,c219_35,c219_36,c219_37,c219_38,c219_39,c219_40,c219_41,c219_42,c219_43,c219_44,c219_45,c219_46,c219_47,c219_48,c219_49,c219_50,c219_51,c219_52,c219_53]

def dict219 : Nat := 0x800344842400a9002704901001d40084c0024007d001b204208102400488b012240d000e4002c498040020d08080032000b228084a0230240c24020c04411004500515016020811830800110840060c8803210088403000500268002a0009800220007800190020209008208064201a0a40090910106808820120c010016400344a0a40028490912405002d400a500234004d000f400310009122008109309090031400c1002f40094190010c008a0a4004098904001d0035400d10033400b1002b40079001926202000522401002e04408410822009003206821001c40068485022424880a2600091104005c410280010890810424880114404490004c04d010248401300400448a08220248a001290012500482089018000c5800342405240144404908120244810048048242120044802341420002128010028148004a0806800981016100c04212029001520441000316040521010c0e000104a010006300410022046004301208404a4210d0900013000011091040d0004400510000064048100800010002120601910301401a10048601118400144142302005850260608810208004100206008202064241a1806460525014908581822060828022000110022020c040222001202120004140048004808204044840104041101048401110

def d219 := unpackCases dict219 8

def u219 := unpackShort dict219 8

def s550 := certify 219 5 ([w13,i7,i6,i0,i1,i4]) cs219 [] (u219 4 60 0x58c94b26ff873e73a844bc93b25ef9dfee709400882066c93f27bf9a3e97b12411164409762802003491257b1e)

def s551 := certify 219 6 ([w71,i7,i3,i6,i0,i1,i4]) cs219 [s550] (u219 4 75 0x1184f2134232105e2f239d422458876085a2d13074e1d085a2d17384a0044102a58a7600562b03574bfd00562b033586185e4179188634f58d484a6a)

def s552 := certify 219 5 ([w19,w72,i3,i6,i0,i1]) cs219 [] (u219 5 60 0x91310e605c5811c728200110405498a7300e2a01c70450c663398861ccc69bcf5c25815815405400c318732388b8b84684)

def s553 := certify 219 6 ([w72,i7,i3,i6,i0,i1,i4]) cs219 [s552] (u219 5 81 0x4309e208514c438e504489887302b2c0b6db029c704500088202a4c5398055500552a95818cc7f15709708610634de7962ae12e12c0ac0aa02a00618cf8858859a)

def s554 := certify 219 5 ([w14,w65,w63,i0,i1,i4]) cs219 [] (u219 3 60 0x105e2f44178bd1309e9dc1542168b4885a2d248e21f03a1d40a8110400562b00158ac1538a7c891c2859b243558d3)

def s555 := certify 219 6 ([w65,i7,w63,i6,i0,i1,i4]) cs219 [s554] (u219 4 78 0x8c279082f17909a119082f1791cea1122c43b042d168983a70e842d168b9c25002208152c53b002b1581aba5fe802b1580ccd14d88631a7ab6a428b2086a)

def s556 := certify 219 6 ([w14,i7,w63,i3,i0,i1,i4]) cs219 [s554] (u219 3 78 0x82f17a2064968984f4ee0aa10b45a442d169106512491c43e0743a8150220800ac56002b1580064660a9c53e0bd05e8178b094e3231a6191f86542cd85da)

def s557 := certify 219 6 ([w73,i7,w63,i3,i0,i1,i4]) cs219 [] (u219 5 75 0x975c20854421c72820565810565816db60538e08a001104002aa8002aa802a954ac2e12e11668a68a3198da28c109e21891439862a54e610618d3198)

def s558 := certify 219 6 ([w19,i7,w63,i3,i6,i0,i1]) cs219 [s552] (u219 3 74 0x91c43e10b45a442d16911acee5dc154022082a714f802b15800ac5600833780743a8156c1192f3109e990d30b88c9623817a0bd046531190c5e82f4a)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s559 := certify 219 7 ([w63,i3,i6,i0,i1,i4,i7]) cs219 [s551,s553,s555,s556,s557,s558] (u219 5 231 0x742085204ae9f311420920821931924c4f304110220851bae40dd714441300b62a0db083028229480e10239409412012721244ca0c9cd08730230d210445961a6cb080829b841166cb26f658590822802ae19154ac8ac00c0441c500704004510526e000119c29299c8210004d40549881935414e60064940008aaa92d55100012500032d55496aa8ca000c18614d729859b0518561cba3344345174a6932d14415711709e0977970840861d4c2e904174bad3859d566886d147929a29b4510ca)

def s560 := certify 219 6 ([w74,i7,i3,i6,i0,i1,i4]) cs219 [s550] (u219 4 81 0x4613c84c12c841389c8e750891621d822491c42c22442148a45ce128011040a9629d802691400c0cc008400c1fe18630fd857218492932d63c5b053b210a)

def s561 := certify 219 5 ([w14,w67,w75,i0,i1,i4]) cs219 [] (u219 4 54 0x163252c9cea112f24ecb9c2500220819b24fc9044591025d8a00801123c20d8212c9812245806240a)

def s562 := certify 219 6 ([w67,i7,w75,i6,i0,i1,i4]) cs219 [s550,s561] (u219 4 78 0x163252c9bfe1cf9cea112f24ec97be77fb9c2500220819b24fc9efe68fa5e3cc9044591025d8a00800c8f58fc8b14d1623ec821108443300cc1695964a)

def s563 := certify 219 6 ([w14,i7,w75,i3,i0,i1,i4]) cs219 [s561] (u219 4 75 0x1304b21184f239d4208924710b089124588767384a004410009a4500303302a58a7615c861214f123c4a4c2e89c82720a44291401002303fc284ca)

def s564 := certify 219 6 ([w19,i7,w75,i3,i6,i0,i1]) cs219 [] (u219 3 74 0x123887c22491c88d6772ee0aa011041538a7c02691401066f00e87502b82325e6213d0278171c8e4464b2ba18505242920880441a096232588c4e8274a)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s565 := certify 219 7 ([w75,i3,i6,i0,i1,i4,i7]) cs219 [s560,s562,s563,s564] (u219 4 231 0xec84520543b5988d44209484609d8251393d8420c443750846e31108c54255042e209d415082124e449160a593914a1d82642c42b0b4930b1691ec2128055188ccaaa19a862018921ca038401290a42c00119c527339044004d40a9641935829d80649c00b0ac9b2715916c00618c51d5584ce14c568f3e55bdab6945d50bec57243482f86984962174bb261d585db5b043c28eaac14f0a21a84e51139102413a044e428905259148a16214c2c5222c8a0658024e0849e003280bb8b31d66e8)

def s566 := certify 219 6 ([w14,i6,w65,i3,i0,i1,i4]) cs219 [s554] (u219 5 78 0x25d70824d30823510871ca08159604159604151404c169c2d38e08a001104002aa8002aa800104006ab4bf6ae12e10891c8ca6b34b352128a68bac7cc2846)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s567 := certify 219 7 ([w65,i3,i7,i0,i1,i4,i6]) cs219 [s555,s551,s566] (u219 4 231 0x30cc6d0ff4991f8ff46330cc63ab1879630ea6309484309cc251393cc420ec84d20743b6188f44220484288bc5e81178bca2421ec46d30a4c7b1497cc235042e209d415082124444c1d08751110b8742d43c42b0b45b0f168b6c2143c422c8b45b0f168b4b221180356406a6819806121ca038401290a43c00119c5293390440038c0d5d0cf4e319aff40d4a400b0ac5729158aec004a400328ac5729158acca00634baa659862e9985361ac617d85e486905f0d1792c4d10f45db58ba5d90cec868)

def s568 := certify 219 4 ([w113,w35,w163,i7,i6]) cs219 [] (u219 3 40 0x65a92d9189e8942340984d9f61f0fad611e68a3678b27d6a1b68b47b927a00452)

def s569 := certify 219 5 ([w35,i0,w163,i7,i1,i6]) cs219 [s568] (u219 4 57 0x65a92cc6d317cd915ae3d6ae750822491c44313c84508c8678993e45114c4b5d345a24a1280948cfbf796a825094)

def s570 := certify 219 5 ([w113,i0,w163,i3,i7,i6]) cs219 [s568] (u219 4 57 0x6d12cd2930def69057218484313c84508c866c998e3d38f441414d047991460330cc60e9c7a11248e273893d)

def w164 : Sig := 0x3333003333330033333300333333003333330000333300003333000033330000

def s571 := certify 219 5 ([w164,w163,i3,i7,i0,i6]) cs219 [] (u219 4 57 0x6d12cc351a998d5d2ff40269140c5728dd2930def6908f72ddce49895ce1b8edc231f4c080042d1af422392444)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s572 := certify 219 6 ([w163,i3,i7,i0,i1,i6]) cs219 [s569,s570,s571] (u219 4 180 0x2598da1fe8963f25e8c63d88da61498f6292f9846888983a10ea222170e85a34884816924d22d23a042a265c413a82a12ce43006ac80d4d03300cb380023388f2672088007181aba19e9c6335fe81a6d800815934a62b22a00024394070802521463ee4644988619f66d23c4b7dfb4fbd12d0817a0ae41e905e3d30910412908613984a272798841d909a42a8765b11e884)

def s573 := certify 219 6 ([w79,i6,i3,i7,i0,i1,i4]) cs219 [s550] (u219 4 81 0x4d08c841389c841389c8e7508c1d387422491c42148a442148a45ce128011040d5d2ff4026914008400084005721849ef691654207e53422d8d634652b1a)

def s574 := certify 219 6 ([w14,i6,w67,i3,i0,i1,i4]) cs219 [s561] (u219 4 75 0x104e27213423239d42089247108522913074e1d7384a004410009a450021003574bfd15c861214d08b0fbda2ee084b2604891600330587f8c28546)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s575 := certify 219 7 ([w67,i3,i7,i0,i1,i4,i6]) cs219 [s572,s573,s562,s574] (u219 4 231 0x10cc6d0ff4b31f8ff46309484309cc251393cc420ec84d20743b2188f4421ec46d30a4c7b1497cc235042e209d415082124444c1d08751110b8742d1a44240b492691691d021180356406a6819806121ca038401290a4ec00119c52b3390440038c0d5d0cf4e319aff40d4ac0040ac9b2b15915000313323224c430c5d30bd05720f482f1e984882174bbed10f45d4207e751f988661f9e47e621990251289102421a04a6428904259108a76210cec4222c886665198256019cac6603280bb93510e1f6)

def s576 := certify 219 5 ([w135,i7,i4,i6,i1,i3]) cs219 [] (u219 5 60 0x66e8f1d22ae5a5c7b9572e550892470a27a367462b8f3727e55ca95742ab1a39a13dc70ab13801149a0004108033455e8a380398155ba55)

def s577 := certify 219 5 ([w136,i7,i4,i6,i0,i3]) cs219 [] (u219 3 60 0x12e97489b51fcb7e5e8de9a370269142271336a458bca3e9f8de8237b58dc3237e4993fb86e23e223924808204cc7d36a71750dd8e37)

def s578 := certify 219 5 ([w21,i7,i4,i6,i0,i1]) cs219 [] (u219 4 60 0x4bc93b247a3e86575ef9dfe00882066c93f28ac54af437bf9a3e97b1258c89f26ff847e111c449011404d348ff221116575791be)

def s579 := certify 219 6 ([w15,i7,i4,i6,i0,i1,i3]) cs219 [s576,s577,s578] (u219 1 75 0xfe7f1285c128b728251a8d1d8253209049762491e8fab995b42198e898f345909a4508820ab088110088dd19853032b2592191281c4a272793c76191188c0a0b)

def s580 := certify 219 5 ([w19,w16,i6,i0,i1,i3]) cs219 [] (u219 3 60 0x1fcfe250b87c3e1ba22491c88fab921b8dc63404d2280110401561102a956862633193ea046391c91dc8d606f041b31cce68823a)

def s581 := certify 219 6 ([w16,i7,i4,i6,i0,i1,i3]) cs219 [s580] (u219 5 81 0x3f9fe458845b94879e68a0892470823eae425684141b6d81401348a000110400156800800020552a95818cc7f1524c4f27d14a299442c42c14014006406430d27c2093217a)

def s582 := certify 219 6 ([w19,i7,w17,i6,i0,i1,i3]) cs219 [s580] (u219 1 78 0x7f3f8942e17048242e8d468ec120945b94131248f47d5cc21a10cc710cada7384d2284410558441980cc6e8cc0880440e733992c4a271293c9e3b2988c46050289c860b)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s583 := certify 219 7 ([w17,i4,i6,i0,i1,i3,i7]) cs219 [s579,s581,s582] (u219 5 231 0xd10f14b3cd2cd1441522c7f57907f908915eb2c512089bc45a07c72cc410815962e904204820bab2d805b1506d8418141146908222c249a6c2390104e70829283eb9e85cc8105340ad738414c104e782073c10164209ce104598202802ae19154ac8ac00c1d20004544d74d44520001ce000119c27499c8210003a400244156e941090001d282130003a4002641074e59194001d200065cb26246494af29857b05485664a23753745144ae933d1531521d6428cd3144a24f7e9d44e887d14792ba29f4510ca)

def s584 := certify 219 5 ([w19,i7,w138,i6,i0,i3]) cs219 [] (u219 2 57 0x9d4ea1cbe391c88c1257861809a450d96c97d0e10440419bc0743b02a5f64a6cbecf8258892475b17d2359dd03c1e1580b)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s585 := certify 219 6 ([w138,i4,i6,i0,i3,i7]) cs219 [s584] (u219 4 180 0xd23cab7b56d290a43d93a5f42750e84397ec5f17a0ae41e905e3d309104500aa311995543350c4031cf800815936a22b22a0002f81b2878364bf02fa1c087243940708025214a8800280aa3080800c17f3aa57ab0afa7a8bea1d908acda8765311a884129085f56b3c4aad1297c8418886ea108dc622118a84a40843d1692502d238f4422f88c251498be292f89442a085c413a82a10424)

def s586 := certify 219 5 ([w19,w139,i6,i0,i1,i3]) cs219 [] (u219 2 60 0xfe7f1285c7239118f4af0c311248e91f57291acee81e0f0ac04d228088202ac22020c2203a1d815d8962567c12c05c11c)

def s587 := certify 219 6 ([w139,i7,i4,i6,i0,i1,i3]) cs219 [s586] (u219 4 81 0x7f3f896c57218488c5903d4207a22491c423eae44e75082c224421088440269140011040055c01ce1280c0cc008400251fe04a630fc4a46789484c14c844289c8a)

def s588 := certify 219 6 ([w19,i7,w140,i6,i0,i1,i3]) cs219 [s586,s584] (u219 2 78 0xfe7f1285c723911824af0c311248e91f57291acee81e0f0ac04d228088202ac22020cde03a1d81564b25362567c12c048f4123d2da3ca088088c4b1194c464382780b)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s589 := certify 219 7 ([w140,i4,i6,i0,i1,i3,i7]) cs219 [s585,s587,s588] (u219 5 231 0x68878a59e69668a20a9163fabc83fc8448af596b882b89e09778611081300b62a0db083028228d21044584934d84720209fa1052507d7ed0b990209480e10239409412010a00ab864552b22b00307f800115135ff511480007e800046709fe672084000ff00091055bfd042400011071401c1001144146246494af29857b05485742085144ae9331142085128b3e43ac8511046086c14752983cb0510ca20ba47881f084091e177c7e964b213f423abf4a61164240ca800ff0107fa00194028e8463ab9e6)

def s590 := certify 219 5 ([w141,i0,w19,i7,i3,i6]) cs219 [] (u219 3 54 0xc7325b24f84bc1309e30e47223847f2df86ed8d804d228020cde09c9c116c6c22392488ee6b24e4e)

def s591 := certify 219 4 ([w33,w142,w19,i3,i6]) cs219 [] (u219 4 37 0x937095c351a9992930c8f72ddc391c88e0231f4c2239244bf14000e708e)

def s592 := certify 219 4 ([w35,w142,w19,i7,i6]) cs219 [] (u219 4 34 0xc73259926e12b86e231f4c23b9ac5471114001a8d4d61c8e4470e708e)

def s593 := certify 219 5 ([w142,i0,w19,i7,i3,i6]) cs219 [s591,s592] (u219 4 51 0x18e64b324dc2574a4c30e47223423dcb770dc6a35332083cc20232988f9c238463e984472488477358a8e0)

def s594 := certify 219 4 ([w35,w33,w127,w19,i6]) cs219 [] (u219 3 37 0x93e12f3c5993e4c7d6423b9ac888e4921bf32f82613637a3f997c00458)

def s595 := certify 219 5 ([w33,i0,w127,w19,i3,i6]) cs219 [s594,s591] (u219 3 54 0x127c25ec66c0984f191fcb7e1c8e44704c7d6223924908f26f223b9ac9b1b0df053865f32f806fccbe)

def s596 := certify 219 5 ([w117,i0,w127,w19,i3,i6]) cs219 [] (u219 3 51 0x93e12f04c278c8fe5bf131f5888e49240088111dcd64351ab601348a0c5e51f1cd896c391c88e06e6f)

def s597 := certify 219 5 ([w35,i0,w127,w19,i7,i6]) cs219 [s594,s592] (u219 3 51 0x63992d927c25e1b931f588ee6b2423c914888e492678b27c8b6d2991597ccbe00984d82e391c88e11fccbe)

def s598 := certify 219 5 ([w118,i0,w127,w19,i7,i6]) cs219 [] (u219 3 51 0xc7325b24f84bc37263eb11dcd6480110222392486a356c0419bc18bca3e0984f18723911c23f96fc45)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s599 := certify 219 6 ([w127,w19,i7,i0,i3,i6]) cs219 [s590,s593,s595,s596,s597,s598] (u219 3 162 0x96cc231f9cc963f2588d995ac93e12f2b44a25e6ec0b84da027918c17611c0e496171c88c2e2325c43ae11fc3de758f56fd1cc035c088d5822d818f900815935ae2b22c002cc00463341a64666f118032c22c5e0e65828f823d2d968dc4a44c296128a4fac4c3d2281691c7a2d24c11010044f21102980448846452d109dc46213596c88b65b4)

def w165 : Sig := 0x3333333333333333333333333333333333333300333333003333330033333300

def s600 := certify 219 5 ([w165,i3,w19,i7,i0,i6]) cs219 [] (u219 3 57 0x31cc96c93e27f0d46ad8083378317947c04d2280dd2e97c61c8e446bb47f187b1b1802204477359273af888e492)

def w166 : Sig := 0xffffffffffffffffffffffffffffffffffffff00ffffff00ffffff00ffffff00

def s601 := certify 219 6 ([w166,i3,w19,i7,i0,i1,i6]) cs219 [s600] (u219 3 71 0x18e64b66b793d9b318dac5f62359dc9d6eba48bc892472299116c6a356c02208020cde14ba58be9204d22804400221b40a63630e472231e8bc7a618)

def w167 : Sig := 0xff00ff00ff00ff00ff00ff00ff00ff00ff000000ff000000ff000000ff0000

def s602 := certify 219 6 ([w167,i3,w19,i7,i0,i1,i6]) cs219 [] (u219 5 74 0xc73258c35bc9e31b462f8c11acee13add749b82b2c0b4d0630008820008337814ba5dd4902aa8069248c1a225c4415ee23e1be182b02b00a80a897112e213c)

def s603 := certify 219 6 ([w146,i6,w19,i7,i0,i1,i3]) cs219 [] (u219 3 74 0xe4722382ba18502613c681e8f608924722359dcbb82a86d62fb10a452404d2280110401066f00e87502a351ab605c6e214c2325b3213c96232588c4e25)

def s604 := certify 219 5 ([w135,i6,w19,i7,i1,i3]) cs219 [] (u219 5 57 0xe388888ab969719ba3c74089247082359dc262b8f37227a36742ae87325e9a384f700229340008210001bd06028e00e19a2af4)

def s605 := certify 219 5 ([w136,i6,w19,i7,i0,i3]) cs219 [] (u219 3 57 0x391c88e11fcb7e4ba5d226d02691401066f062f28fa271336a446e6d3992cda93e27f111c9240410223b9ac938b998fa6d)

def s606 := certify 219 4 ([w147,w15,i6,i7,i3]) cs219 [] (u219 4 34 0x723911a14aa527d8ae4309147339e09e601348a0020cde005d6e60e70947)

def s607 := certify 219 5 ([w148,w15,i6,i7,i0,i3]) cs219 [s606] (u219 2 51 0x391c88c12a55293c2e57861809a4501066f02eb7301d0eca3845300b399cc324fc8924748d67748fba340f)

def s608 := certify 219 5 ([w21,i6,w19,i7,i0,i1]) cs219 [] (u219 4 57 0x2359dc48f47d0cae97927640110400419bc1158a95e86cd927e5e91cc97292c49f2111c449011404d408c72392111657348ff2)

def s609 := certify 219 6 ([w15,i6,w19,i7,i0,i1,i3]) cs219 [s580,s604,s605,s607,s608] (u219 1 71 0x723911824128b72824fe7f1285dae0904b6e2491e8d67795b4b38fab993345b09a450882083378110088ab08879038864a605399cc9625138949e07)

def s610 := certify 219 5 ([w149,i6,w19,i7,i0,i3]) cs219 [] (u219 2 57 0x391c88c125786189d4ea1cbe09a4501066f01d0ec0ab65b25f43841100b2f9cc965f67c12c44923a46b3ba0783c2b362fa)

def s611 := certify 219 6 ([w150,i6,w19,i7,i0,i1,i3]) cs219 [s586,s610] (u219 4 71 0xe47223415c86121fcfe25b089247108d677139d4208fab91009a45000441001066f07384a01570028e673258959e252207a81e96c47914010014c4e6)

def s612 := certify 219 4 ([w147,w18,i6,i7,i3]) cs219 [] (u219 4 37 0x391c88d12930c6331e0c42b98484508c84fe709001348a0020cde01a8d4cc)

def s613 := certify 219 5 ([w148,w18,i6,i7,i0,i3]) cs219 [s612] (u219 3 57 0x391c88e02613c602691401066f01a8d5b008a60633186590ae6140e8750229423427f71211248e446b3b924d26ad6)

def s614 := certify 219 6 ([w18,i6,w19,i7,i0,i1,i3]) cs219 [s613] (u219 4 74 0x723911a108b72a252618449238846b3b895a2114cda62f9804d22800220800833782000406a35333061192cccf139ac8b2042910a410040464b1192c825)

def s615 := certify 219 5 ([w13,i6,i7,w19,i0,i1]) cs219 [] (u219 4 57 0xe750821c88449792764011041ce12801c8cc0cd927e5e92c54b290e49724097628020041116440e4963934912)

def s616 := certify 219 6 ([w14,i6,i7,w19,i0,i1,i3]) cs219 [s615] (u219 4 74 0xae4309104bb22c8458a68436c4492389cea1044b10884291488429148804d22800220839c25004b19801080010800827139302313904e4258fc866)

def s617 := certify 219 6 ([w73,i6,i7,w19,i0,i1,i3]) cs219 [] (u219 4 74 0xae43090723911a2c84584492389cea1046b3b88429148804d22800220839c250083378010801427209c8731f88d16458522148a008004e41390966)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s618 := certify 219 7 ([w19,i7,i0,i1,i3,i6]) cs219 [s599,s601,s602,s558,s564,s603,s609,s611,s614,s616,s617] (u219 6 228 0x8528306ada27dcab329f4a8488306aba60c1aaa11204a9a64939f2103046b8c2c49b618412598c1031b618b0684884386dca2ce18688b226dca102132b84566d847813c2e7981b610404b5e816cb419406b5e945eb418106b5a0102b421648b5a1646b420102b568102b48906ab569076b488102b45290eb41010eb450114b412d04e018034e030834e018806e03000ce1c0000e02154ce1c1544e020000b568000b40b302b5c3340b408000e1c0000e089920f87065bb82200038042073814007380400138142052821680a)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s619 := certify 219 6 ([w127,i4,i7,i0,i3,i6]) cs219 [] (u219 5 180 0x5e46b5edf6d79fa9fb0db18b2431091841832c330485eecb6cc15a9bb11b3ac8479de1cebf16e71070c068621a0c80c60066940008a89b5da88a40005dc09fed96d77ca83b01b32d0629c01ccb014672074871c32b52722b6418e3ba38eda5bb745b8b638e902086a069283e8c10de04111611fcb0924041001008575002ba020105d0456d06dd40c7d82d8b7008704716c208e80e)

def s620 := certify 219 6 ([w127,w19,i4,i7,i0,i3,i6]) cs219 [] (u219 5 74 0xcc94d8c34920c92460c8d46f4411e78411e78469a0c6004d228003772010000410000436906906ea5b11c10c7d1822392420100020a0638500414059)

def s621 := certify 219 6 ([w18,i6,i4,i7,i0,i1,i3]) cs219 [] (u219 4 81 0x8d468ed0845b9512930c22491c4263a244ad108426d317cc026914001104006e8cc100020351a9983bc08c46cf309cc6331e0d64590214885208020a50ef04210c4e25)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s622 := certify 219 7 ([w19,i4,i7,i0,i1,i3,i6]) cs219 [s582,s588,s619,s620,s579,s621] (u219 5 231 0x9b186ebe64a6fe4df430cf91863ac9235e490ea30c62c90c42461060cb0dd108d4dac8de96e936410512086df9e207cf0a2410812082ef9e207cf0ba4107b08da35031ee82f8c10c6908222c249a6c23901045b082ea06396e083a0822dc1016c208b61045b8202dacd32590822d841164b659180d0c43419018c00c38800115134e3511480002d800046708e267208400071000eb26e9c72cba00038a081c4000e20007141038a08194000e20006541042944a90f320c511a429c831446e887d144a2512894628b90c4)

def s623 := certify 219 5 ([w13,i6,i7,w151,i0,i1]) cs219 [] (u219 4 57 0xbdf3bfc9792764011040f7f347ccd927e4e7509ce1283958c94b222116497b124097628020057b1e34912)

def s624 := certify 219 6 ([w14,i6,i7,w151,i0,i1,i3]) cs219 [s623] (u219 4 74 0x118b22c8458a6844bc44923885844884291488429148804d228002208018198010800108008573091cea139c2509641389c841389c8ac0fd426)

def s625 := certify 219 6 ([w73,i6,i7,w151,i0,i1,i3]) cs219 [] (u219 4 74 0x3ded2ac845844923886e3718a8429148804d2280022080aa5550c4108008573091cea139c2504641389c841389c8631fa916458522148a0080306)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s626 := certify 219 7 ([w151,i7,i0,i1,i3,i6]) cs219 [s624,s625] (u219 4 228 0x21e0c633ca87e6329e07f821a8c640b2d297991240b10c979ac640e91e97aade40eada97a90a429ec46d4298526429ec525f429846429a44242a05a49429a45a4742a042428c443742a84237428c4423142a84a4a980354ab20354a9a064ab00c4aa54004aa0564d4aa5456454aa00042a14004288ce242a54ce414288004aa80554a8c466554aa866a4a8c4031288948428984e6288944e4f289884288f48428a05e57288f45e6128a08442888e428868e428a9442884844a829c4ac09c4a80844ac29428944b623)

def s627 := certify 219 6 ([w152,i6,i4,i7,i0,i1,i3]) cs219 [] (u219 4 81 0x8d468ed057218496422d0d4221a22491c4263a244e75082148a442148a44026914001104006e8cc1ce12808400084004a28ec841389c841389c981de076652b03b)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s628 := certify 219 7 ([w153,i4,i7,i0,i1,i3,i6]) cs219 [s627] (u219 5 231 0x13630dd7cc94dfc9be8618c59218848c20c1961ba211a9b591bd2dd26c822e20ae27825de18442043d846d1a818f7417c608634841116124d3611c80828b84175031e2f041d0412901c20472812824020c068621a0c80c60064040008a89b01a88a400045c00023385013390420008080075937603965d00008838a00e08008a20a4820834c349313c6104289468bd10fa288827c75f86218df14fe188632c5d5884090b205620ba440598028b85045e008b216465c8080819407200ca01474e510cb65b)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s629 := certify 219 6 ([w120,i6,i7,i1,i3,i4]) cs219 [] (u219 3 180 0x3b44a21d0ec8623a4412a2309d84a2727b2200543a1140e8220442a1517c15d07a82f1e9852103701fa0b87c36170dd45605c26d013c8c60bb0ae09a0c3015bd48a1001510f21705482a8214349140b492691691e08862437a108dc622118d151ec8dac2963d8a4bec4c672208c819dea4102021b3510e8ea4350d3304706a0c3508b30665015462332ad0ce862031)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s630 := certify 219 6 ([w100,i6,i7,i0,i3,i4]) cs219 [] (u219 3 180 0x3b44a21d0ec8623a4412a2309d84a2727b221270842bc4150a885105f05741ea0bc7a614840dc07e82e1f0d85c3751581709b404f23182ec2d82491a485a692394120443a1500ea020542215618040ac9af51591600280aa3119956867431018b00d702235608b606464008ce4f53390480112cd443a4490d434cc296623d9b4527b2f9330c486f4211b8c44231a2a)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s631 := certify 219 6 ([w102,i6,i7,i0,i1,i4]) cs219 [] (u219 3 180 0x3b44a21d0ec8623a4412a2309d84a2727b220f51205e571e8bcc30881510f21705482a82141890de8423718884634547b236b0a58f6292fb131a48a05a49348b48f0448110e85403a8081508856320046727a99c824014055188ccab433a1880c5806b8111ab045b031860102b26bd4564580021b3510e8ea4350d334304c2f8138cc0bb306e03f4170f86c2e1ba8a)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s632 := certify 219 6 ([w154,i6,i7,i0,i1,i3]) cs219 [] (u219 3 180 0x1b80fd05c3e1b0b86ea2b02e136809e46305d85f05741ea0bc7a61484349140b492691691e08862437a108dc622118d151ec8dac2963d8a4bec4c1510f21705482a8214618040ac9af515916002320046727a99c824014055188ccab433a1880c5806b8111ab045b0310221d0a80750102a110a92d9aaf744bbda869984ecc8254138949e8c83b44a42d0ecb623a44)

def s633 := certify 219 6 ([w154,i4,i6,i7,i0,i1,i3]) cs219 [] (u219 5 81 0x79e68a49230623cf0823cf080892470b6db028da317c68020a08020a0009a4500008820154aa561a68318800020800020314a11869241ba2ba2a41a4184e8ae8a)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s634 := certify 219 7 ([w104,i6,i7,i0,i1,i3,i4]) cs219 [s629,s630,s631,s632,s633] (u219 3 231 0xed1288743b2188e9104a88c2761289c9ec8843442890ca2d721acca2882f82ba0f505e3d30a4206e03f4170f86c2e1ba8ac0b84da027918c17621c4174865d6190d325d880a88790b82a415410a1a48a05a49348b48f0443121bd0846e31108c68a8f646d614b1ec525f6268e911663a598e90cf259224088742a01d4040a8442b1b00815936362b22c00474008ce51b3390480280aa3119956867431018b00d702235608b60646c00cb1b32c6c8653328010d9a88747521a8487310c90e063f)

def s635 := certify 219 5 ([w121,w14,i6,i7,i1,i4]) cs219 [] (u219 4 53 0x4c12c841389c841389c8e75082c22442148a442148a44201040ac0fd426e70940606600420004200)

def s636 := certify 219 6 ([w106,w14,i6,i7,i0,i1,i4]) cs219 [s550,s635] (u219 4 74 0x98259082713908271391cea105844884291488429148848d48b9c2500220801819801080010800083c81581fa84c8239488c5916422c53)

def s637 := certify 219 5 ([w57,i0,i6,i7,i1,i4]) cs219 [] (u219 4 57 0xdff0e7cb192964e7508bdf3bfc97927652f6244a129011044af2bc691a40250944097625795e348d2)

def s638 := certify 219 4 ([w113,w122,i6,i7,i4]) cs219 [] (u219 4 40 0x6ff873e58c94b297b12411164a0fb1eb491240200e708212a9555e1a8d4d2)

def s639 := certify 219 5 ([w122,i0,i6,i7,i1,i4]) cs219 [s638] (u219 4 57 0xdff0e7cb192964e7508bdf3bfc97927652f625ce1280114c0552aabc351a9a48222c8812ec431f63d692250)

def s640 := certify 219 5 ([w113,i0,w13,i6,i7,i4]) cs219 [s638] (u219 4 57 0xdff0e7cb1929652f6248222c8af63c692248299050812ec44799146b5f2d7d3394ce407388215ef96be4bca672)

def s641 := certify 219 5 ([w123,i0,w13,i6,i7,i4]) cs219 [] (u219 4 57 0xdff0e7cb1929652f6248222c8af63c6922500400812ec5ce128f7f347ccd927e4e7508bdf3bfc979276441)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s642 := certify 219 6 ([w13,i6,i7,i0,i1,i4]) cs219 [s637,s639,s640,s641,s615,s623] (u219 4 180 0x4691bfe7cf91ad71cf89e3f9163213c8fe2752c892a085c413a82a10424bf897be10fafe2177f85ebe892f214cafa294ec852243940708025214598002338932672088005a81efe19f96a3368f81e99819b284a6704fc812c4a5e1ffb03fc7a5213a1041e904e3d45910414a102348852695d8902822003c8205380100c215eb7b16c791e1fd8d24487e844ad2)

def s643 := certify 219 6 ([w13,w14,i6,i7,i0,i1,i4]) cs219 [] (u219 4 74 0x98259082713908271391cea105844884291488429148b9c2500220801819801080010803d81fa8648222c8812ec5004008b6116422c5d)

def s644 := certify 219 6 ([w13,i3,i6,i7,i0,i1,i4]) cs219 [] (u219 4 81 0x4d08c84613c8e7508c1d387491621d822491c5ce128011040d5d2ff4a9629d80269140cd6185721849ef6b129307e27209c82910a4500400a5634630fd88)

def s645 := certify 219 6 ([w159,i4,i6,i7,i0,i1,i3]) cs219 [] (u219 4 81 0x8d468ed07f3f896c572184822491c4263a24423eae44e7508026914001104006e8cc0055c01ce128c964e04a4a28ec8467894881ea07a211084500400a56076630fc4a27)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s646 := certify 219 7 ([w14,i6,i7,i0,i1,i3,i4]) cs219 [s636,s551,s642,s643,s644,s556,s563,s566,s574,s579,s645,s616,s624] (u219 4 231 0x26c84c60f09bc092f0422bc841f89c4eaf1389c7e4256c842889c4f591389ca2420bd05720f482f1e98488255d08c5b155b5b08454ed61fa10f94207f6b35d66992ea1079420ba532ed042e209d415082121a44240b492691691d02147c42c08711f10a27021414421f8a45305148a47e21414422c8a45305148a4b221121ca038401290a3b40040ac9aed1591500041400119c4ed339044003b400c0cf0ed198cf0003b4001fc20ed8407e003b40032c20ed840ca0040ceaac10f0751f8fcea4350cc4866)

def s647 := certify 219 6 ([w110,i3,i6,i7,i0,i1,i4]) cs219 [] (u219 5 81 0x8544208613c438e504db6c0a489887302b2c082b2c09c70450008820154aa560a9314e601554001554018cc7f15709708d14d14610634d6b84b8468a68a18633e)

def s648 := certify 219 6 ([w161,i4,i6,i7,i0,i1,i3]) cs219 [] (u219 5 81 0x1e79a28fe7f9162116e52162085822491c2db6c0a08fab9095a1050401050004d22800044100aa552b001568008000219000646331a6cae8ae8a9262793c4e8ae8a18693e)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s649 := certify 219 7 ([w73,i6,i7,i0,i1,i3,i4]) cs219 [s647,s648,s557,s617,s625] (u219 5 231 0x3a10429ae574b388a104578827d34caf9a6f8412e20ae27825de184420468878a59e69668a20a3aacb7c41099208f9659480e10239409412010d21044584934d8472020b00b62a0db08302822a06105f51440e8a3e08211071401c100114414838001151360f511480008180004670a0e67208400050055c322a95915801841c003e41083a087c000752198cebf7c510ca98a3308751263ccc2144420ba42c755882990b1756a0b3405030a881d01164240ca8010701083a0019403ac15821c746)

def s650 := certify 219 4 ([w113,w33,w128,i6,i3]) cs219 [] (u219 3 40 0x1309e315d0c28391c88e0c6636c4627a3cd114644923936357fb917e00412)

def s651 := certify 219 4 ([w35,w33,w128,i6,i1]) cs219 [] (u219 4 40 0x3698be673a8411ad12211248e23198cc9f2189e4a1094948d5f250940008a8)

def s652 := certify 219 5 ([w33,i0,w128,i6,i1,i3]) cs219 [s650,s651] (u219 3 57 0x2613c62ba1850723911c11248e46d62fb7705508d68923198db1189e815440a9be0f306f229936357d02a8150)

def s653 := certify 219 4 ([w35,w113,w128,i6,i7]) cs219 [] (u219 2 40 0xc6630ce80b11c989f11ad12b3c727c1e0f93d008a87239118242613c178f38a3)

def s654 := certify 219 5 ([w113,i0,w128,i6,i7,i3]) cs219 [s650,s653] (u219 3 57 0x723911c04c278c57430a18cc61964a11a2313d08307982088ca62366cb623cd146044923911ad124d8d9dc93d)

def s655 := certify 219 5 ([w35,i0,w128,i6,i7,i1]) cs219 [s651,s653] (u219 4 57 0x235a2446d317cce750822491c46331e0c4508c84313c84511e4445b694c8a678993e4a12801c8e4468948d625094)

def s656 := certify 219 5 ([w162,w128,i6,i7,i0,i3]) cs219 [] (u219 3 57 0x1c8e44701309e323f96fc04d228020cde0351ab6317947c6331865b86e23ee49897888e492008811064d644c7d64)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s657 := certify 219 6 ([w128,i6,i7,i0,i1,i3]) cs219 [s652,s654,s655,s656] (u219 4 180 0x11a0738b0e447611e10865a464498861ac617a0ae41e905e3d30910434884816924d22d23a0428f88423109ae3e214488c423d88da61498f6292f9846a2cdc413a82a1232461800815935322b22a0008c80023388f267208800218002319a0ca6333788c003006ac80d4d03300c243940708025214c18c623c298f185c08cc611909842a8465b11e08412908613984a27279884)

def s658 := certify 219 5 ([w162,i4,i6,i7,i0,i3]) cs219 [] (u219 3 60 0xbd1bd346e1309e323f96fc04d2284fc6f411b8d46ad8c5e51f18c6f4f1bf0dc47dc9312f111c92401102a1bb1c6e4c7d64e2e)

def s659 := certify 219 6 ([w128,i4,i6,i7,i0,i1,i3]) cs219 [s658] (u219 5 81 0x11a8de8849230623cf0823cf0808924708263a242368c5f1a008280a610459009a450000882000ddc80d3418c4000104000103198d81ba6228a41a418428ae98906906)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s660 := certify 219 7 ([w70,i6,i7,i0,i1,i3,i4]) cs219 [s657,s659] (u219 4 231 0x26c84c10f09b2192f04209484309cc251393cc420bd05720f482f1e98488210d08c5b0c3b5b08432d23224c430d635042e209d415082121a44240b492691691d02147c42c08711f10a270211ec46d30a4c7b1497cc23121ca038401290a4240040ac9b09159150004c400119c5093390440042400c0cf109198cf000180356406a68198061d48663c10f04331886512890864219e4a642892c5db20868b30ec82ea04259108a62210cc44222c886665198212019c246603280871d510e0a3f)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s661 := certify 219 8 (roots 219) cs219 [s559,s565,s567,s575,s583,s589,s618,s622,s626,s628,s634,s646,s649,s660] (u219 4 240 0xd5e0c63c1a87e63c0e07f8ada8c6ac8ec8428aaaeaaa8eea62328a8847c8948428984e66b8944e4f28988459e91e2eaade4ceada2ea90a3cb2d22e991229b10c2e9ac6288bd0572e907a4408bc7a612891042c8c44372ca842372c8c442312ca84a2c9ec46d2c985262c9ec525f2c98462cd042e2c904e2cd0542c904242c9a4422ca05a492c9a45a472ca04232a8055328c4665532a866a328c4031329803532b2035329a0632b00c32921c32d01c32900432d214329940032a0564d32994564532a0002c964002c88ce22c994ce412c8800)

theorem lower219 : Claim 219 9 := fromSearch 24644 (by decide +kernel) s661.property

theorem lower223 : Claim 223 10 := fromLift 10 4 26180 lower219 (by decide +kernel)

def cs54 : Cuts (goalAt 54) := []

def dict54 : Nat := 0x2414058081206088801610048502400088002404048001210088081202

def d54 := unpackCases dict54 4

def u54 := unpackShort dict54 4

def s662 := certify 54 3 (roots 54) cs54 [] (d54 24 0x1c06641b0a0551433092872)

theorem lower54 : Claim 54 4 := fromSearch 1115456 (by decide +kernel) s662.property

theorem lower118 : Claim 118 5 := fromLift 5 16 34669888 lower102 (by decide +kernel)

def c126_0 := ruleFor 126 lower110 none (by decide +kernel)

def c126_1 := ruleFor 126 lower108 none (by decide +kernel)

def c126_2 := ruleFor 126 lower54 none (by decide +kernel)

def c126_3 := ruleFor 126 lower118 none (by decide +kernel)

def cs126 : Cuts (goalAt 126) := [c126_0,c126_1,c126_2,c126_3]

def dict126 : Nat := 0x80004220a800002c140907022100488058281102048041a0a062421505052420d0502a0a1a1801a0a1614024000d0c100030b0a04606149410000129081a1811908120a0b0802428090401602048181218058401214400046202120a100020a8085202110504604110181a10068084400088004440058501606090501200088804800120204840090102420048404404088081202

def d126 := unpackCases dict126 7

def u126 := unpackShort dict126 7

def s663 := certify 126 5 ([w77,i2,i1,i4,i5,i6]) cs126 [] (u126 4 57 0x23533100b4ac0015805242727bc25528091b5a318974623991c54250b00c0110810c4bc4a1118300)

def w168 : Sig := 0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000

def s664 := certify 126 5 ([w168,i5,i1,i2,i3,i6]) cs126 [] (u126 2 57 0x11110f8fa2ef62e461241090c0f094745094343171d4107e0a613cc4a7bb1d9cecf2ef854541b8bc758816958)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s665 := certify 126 6 (roots 126) cs126 [s663,s664] (u126 3 180 0x6f2246d356f6d334226b004692d6b692b40067002512678317200e31114c11ece459465c2f26326563812c261c2305f0615f490c04821e1d2141d4e8ea1d5d285da8a21d21984105b0195b3f0805988c57477f5745c88556294534555327464261fa131f2132a6a01315376150605113134f66c4d254f4d3dc664b6681b3b4b1b39866)

theorem lower126 : Claim 126 7 := fromSearch 34694464 (by decide +kernel) s665.property

theorem lower115 : Claim 115 5 := fromLift 5 16 68 lower99 (by decide +kernel)

theorem lower55 : Claim 55 5 := fromLift 5 1 1348 lower54 (by decide +kernel)

def c119_0 := ruleFor 119 lower118 none (by decide +kernel)

def c119_1 := ruleFor 119 lower117 none (by decide +kernel)

def c119_2 := ruleFor 119 lower115 none (by decide +kernel)

def c119_3 := ruleFor 119 lower87 none (by decide +kernel)

def c119_4 := ruleFor 119 lower55 none (by decide +kernel)

def cs119 : Cuts (goalAt 119) := [c119_0,c119_1,c119_2,c119_3,c119_4]

def dict119 : Nat := 0x40010224211050241405404110510c0441030584012144000815100445100011050862421505052420d05044000900015050d0c043031494022000480046420585041001050021000440015144000043424000c2404111002220084804404088081202090801210044404101084041101

def d119 := unpackCases dict119 6

def u119 := unpackShort dict119 6

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s666 := certify 119 6 (roots 119) cs119 [] (u119 3 180 0x632248a86e2e1422860090521c1be800fc008d93f37748008d3d42ef48972294864bbb2a76668c91727356c1b8396f64281ac574668d59d5484e8624558f15e282c2abc217e4601505b114ae9ad5746a21194914ea513a116224c9789a52265cdc04d1e323060c2793d9a90cd3e865d33496683b07cec7866)

theorem lower119 : Claim 119 7 := fromSearch 1348 (by decide +kernel) s666.property

theorem lower95 : Claim 95 6 := fromLift 6 2 26180 lower93 (by decide +kernel)

theorem lower123 : Claim 123 6 := fromLift 6 2 24644 lower121 (by decide +kernel)

theorem lower111 : Claim 111 6 := fromLift 6 1 25941 lower110 (by decide +kernel)

def c127_0 := ruleFor 127 lower125 none (by decide +kernel)

def c127_1 := ruleFor 127 lower126 none (by decide +kernel)

def c127_2 := ruleFor 127 lower119 none (by decide +kernel)

def c127_3 := ruleFor 127 lower55 none (by decide +kernel)

def c127_4 := ruleFor 127 lower95 (some (1,i2,i3)) (by decide +kernel)

def c127_5 := ruleFor 127 lower123 none (by decide +kernel)

def c127_6 := ruleFor 127 lower126 (some (1,i2,i3)) (by decide +kernel)

def c127_7 := ruleFor 127 lower125 (some (1,i2,i3)) (by decide +kernel)

def c127_8 := ruleFor 127 lower91 none (by decide +kernel)

def c127_9 := ruleFor 127 lower111 none (by decide +kernel)

def c127_10 := ruleFor 127 lower107 none (by decide +kernel)

def c127_11 := ruleFor 127 lower95 none (by decide +kernel)

def c127_12 := ruleFor 127 lower126 (some (3,i3,i6)) (by decide +kernel)

def c127_13 := ruleFor 127 lower125 (some (3,i3,i6)) (by decide +kernel)

def c127_14 := ruleFor 127 lower119 (some (2,i4,i5)) (by decide +kernel)

def c127_15 := ruleFor 127 lower123 (some (1,i4,i5)) (by decide +kernel)

def c127_16 := ruleFor 127 lower87 none (by decide +kernel)

def c127_17 := ruleFor 127 lower126 (some (1,i4,i5)) (by decide +kernel)

def c127_18 := ruleFor 127 lower125 (some (1,i4,i5)) (by decide +kernel)

def c127_19 := ruleFor 127 lower119 (some (1,i4,i5)) (by decide +kernel)

def c127_20 := ruleFor 127 lower126 (some (2,i4,i5)) (by decide +kernel)

def c127_21 := ruleFor 127 lower125 (some (2,i4,i5)) (by decide +kernel)

def c127_22 := ruleFor 127 lower119 (some (1,i5,i6)) (by decide +kernel)

def cs127 : Cuts (goalAt 127) := [c127_0,c127_1,c127_2,c127_3,c127_4,c127_5,c127_6,c127_7,c127_8,c127_9,c127_10,c127_11,c127_12,c127_13,c127_14,c127_15,c127_16,c127_17,c127_18,c127_19,c127_20,c127_21,c127_22]

def dict127 : Nat := 0x200078001a00058001200034002868384005848601888061200b0105400110403400110202408118004402090084500110042500090045838121401250144401905400543c140d07024300c440220808810230008804620040040542014880225014481000d1a1406810110301e100744029000a8086420150405818064001a021514034100d08026000c8402c1c0482016000481013000480452004003c4a02124041d01400103438118104406114104405104142a00148405828090704a40160804c044001c290940051001340049000e068002c1480008684008840122008440112008424682016041000c120120001120802c004002043011040d0006064242c280686019184004458401a00048104001500030442458001280048021240048011300048284002d00091190843031105024100540411058000034301290843421a1802901120201218044602c201a0a05250058401214054401114104005850189081a100644052420640454140d0504142400050000084002428110002400105001614054501505044002220084802404088010002090502202111001200048084404121004800090804101084041101048401110

def d127 := unpackCases dict127 8

def u127 := unpackShort dict127 8

def s667 := certify 127 6 ([w124,i6,w77,i0,i1,i4,i5]) cs127 [] (u127 5 81 0xc812c61a08061066841103b88251408f3cc0ca289081126c09de83b500acb02db61989a6112002f00008f500eb41d280155401946806218940882c839ca2b4708)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s668 := certify 127 7 ([w77,i2,i0,i1,i4,i5,i6]) cs127 [s667] (u127 5 243 0xb630c412c82d92d0240c31044108229041229dc8104f84106558df2ada18410f212a482c90792ca9c808860278691e6246060864a45040944824849046b84169658d7b2cd0208d61047584935d961c1044004f42e279171080080c06cc45b0d10cc00c0914c901308008944935c00023484a534f810002940034aaa52d5568000a50003aa23a96aa8e000434408499081bd023422079c0368341a4033cc6a34a04788943c6813411c70a412261071881c8109122038ca319c680cf00c70d41c43109a2504da04384)

def w169 : Sig := 0xff00ff00ff00ff00f000f000f000f000ff00ff00ff00ff00f000f000f000f0

def s669 := certify 127 6 ([w169,i2,i6,i0,i1,i4,i5]) cs127 [] (u127 4 84 0x4bb15ec21b4446b12acf7b06a524445b112c14945a21b8dcd81389c920087a043b10ac048c56056ab44267a9052441b20c1098426149052416885a215805604320c52ac5d)

def s670 := certify 127 7 ([w124,i2,i6,i0,i1,i3,i4,i5]) cs127 [s667,s669] (u127 4 105 0x6812cc610884c43688481dc84148a486532ecc43223c8d9849e0b173b9ef60d4a4882249844ef83b602168b442168b44371b9b0271392402397c0010f40eb83a600158ac00158ac0810984261490524b38df6859cea)

def w170 : Sig := 0xf0fff0fff0fff0fff0f0f0f0f0f0f0f0f0fff0fff0fff0fff0f0f0f0f0f0f0f0

def s671 := certify 127 6 ([w170,i2,i6,i0,i1,i4,i5]) cs127 [] (u127 5 81 0x12e62bcc10668446989531e79819451211166224c0acb020acb02db61989a6112002f00439885300aaa000aaa0201a01a812811031030a806806a04a0420c40c)

def s672 := certify 127 6 ([w168,i5,w75,i6,i0,i1,i2]) cs127 [] (u127 3 78 0x41e2cf0ea750d85ce6871422b954917889c261b0482a1509a014ca20043d043e217017ebd01389d02617a0bd7137485e02f08e0dcac37c899494e36f191b895c)

def w171 : Sig := 0xffff000000000000ffff000000000000ffff000000000000ffff0000

def s673 := certify 127 6 ([w171,i5,w75,i6,i0,i1,i2]) cs127 [] (u127 4 78 0x106c59b0623110984572a8916c44b3dec180532880021e810ec42b06e37362cab29c26e885e017810e3314c9762bd84399c494a48827139248d62558472649a)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s674 := certify 127 7 ([w75,i6,i0,i1,i2,i4,i5]) cs127 [s671,s672,s673] (u127 3 243 0x172c97c25e2e496afc6c1fa2331d87eb10db222dd11b845c5b9152b898210b8c5a86221a10b05d853473436a0a4da714a46cd20f02f8d90bacf2b03241f61287c32250cb1304c4a15420a84c82682543d9150b4ae7b16956889f248bc2ce3e4b289c2c601b8644637611b0640328231384c04e808131184d6a0142b29ad45651a00968011a496a691e9003dc10f82fc7b8bd0b8184bee633b12ccec56e622f7213508a4d4ca7205f82f491a0b9bc2f5d459ee2359164d6dd2e217f0bc16a02f5a8bc3803a1d8)

def s675 := certify 127 6 ([w10,i6,w168,i0,i1,i2,i3]) cs127 [] (u127 2 81 0x4388f8db6db866ec90db7c360b2e8d4167387180b9a85c16753a86df68926148ae554150a84e299cc5261b0502397c029944043d02713c098978bc05faf4422a064c1b809)

def w172 : Sig := 0x3333333333330000333333333333000033333333333300003333333333330000

def s676 := certify 127 6 ([w172,w168,i5,i0,i2,i3,i6]) cs127 [] (u127 4 78 0x18c31a193a6fe997483d0663382145d1aa8ea75d5a0b481d09e4f4400472f8005328800bf5e820347fd34870a3d47e90682438d0230924422a95c4017804260b0c44)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s677 := certify 127 7 ([w168,i5,i0,i1,i2,i3,i6]) cs127 [s675,s676,s672] (u127 4 243 0x18d8ec439863718d0d14425cc9d19f50933b7f4ed28dc4321348a326a3c8e241433458670b410a43454a7284baab508d5ca56ac757da8eba568ff6b0a6c7322882951c49621e44a941650792ca9d0241ac42727c926b4f985c211ec4250b4ae7b1695542133c42d09586cf12b074214963420a921488cf22004f80bc9e817a20083440072748e9b4e97dc0026c0050aca69b1594540033c0011a449b348f440026c00d08d7e9b11af7400105e279004e401242f916f5a41fd05b37b851a4334fa620908822a082453ba084)

def s678 := certify 127 6 ([w172,i4,i5,i0,i2,i3,i6]) cs127 [] (u127 4 84 0x630c6872fa83e65d20f4198ce0851746aa86fa7fe82d20742793d10011cbe0014ca209efa77e80d1ff4f4e4b7ea3f4834a7b54121c6811849221154ae200bc0237a17e25054)

def s679 := certify 127 7 ([w168,i4,i5,i0,i1,i2,i3,i6]) cs127 [s678] (u127 3 105 0x198638a48fe8e3fe26937b89a4de198cc23145d1ad446223f0bd43e8b417aa0baa614f0449309115caa450b129094884a6f221c93c9f01102397c00a6510021e8050c4602300118bc005e3f82dc310608303f3e86d0830418)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s680 := certify 127 7 ([w171,i5,i0,i1,i2,i3,i6]) cs127 [s673] (u127 3 243 0xc66fc8ec31f18e19b0d5e32b19d9aa675db73046867017198442e118a866d57284baab508d7aa8421718b50c44342160bb1e495305983c9654f0506b22e4f924d69f30f111ec8a85a573d8b4ab4441920fb0943e191286589a009e111793e05f011008b340393a4769a74bfc00d300a1594da62b28d0052c008d24d3348f4801806e19118dd846c1900c96d9a09705b25a061988289045820914ef0884d44e5190c9aa347f2244d1285273898a4e348848151284c2a41309895100262711a09c1104613099f5a21b)

def w173 : Sig := 0xff00ff00ff00ff00ff000000ff000000ff00ff00ff00ff00ff000000ff0000

def s681 := certify 127 6 ([w173,i4,i6,i0,i1,i2,i5]) cs127 [] (u127 3 84 0x12f8afc188c442c83c59e3d4874d2187c3e19622b954917889c65b2e2a431b8dd832053288010f410f885c8bc5c871521b0fc868dc3be0fd87ec6da36d118489205f023c62df1113243)

def s682 := certify 127 7 ([w17,i4,i6,i0,i1,i2,i3,i5]) cs127 [s681] (u127 3 105 0x3106aacc3f1fb195976cb75bc6483c99a9f1bfb83a3118885a8ba35a8dc6c8319a369b6a8da6da0f87c32c449309115caa44e3a89094884a2522128dc6ec1902397c00a6510021e8053c5e023001188c004703f61fb1048a774)

def w174 : Sig := 0xf0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f0f0f0f0f0f0f0f0f00000000

def s683 := certify 127 6 ([w174,i5,i6,i0,i1,i3,i4]) cs127 [] (u127 5 84 0x2db95af2b4e075c086223c441e567c95b859705144840892610ac79587286e15fc269844802397c0002f00aee55bcab3855f0c3240e05090f10ad0ba548148144044011947721b02b0)

def w175 : Sig := 0xff00ff00ff00ff00ff00ff0000000000ff00ff00ff00ff00ff00ff00000000

def s684 := certify 127 6 ([w175,i5,i6,i0,i1,i2,i4]) cs127 [] (u127 3 84 0x23712b886564a1cd0e2883c59e2b55b6f328542a13422b954917889c72b963e651389d026053288010f410f885c90c84cb1f4be207391329435a2e89484a4230118462e71998a65)

def s685 := certify 127 7 ([w10,i5,i6,i0,i1,i2,i3,i4]) cs127 [s683,s684,s675] (u127 3 105 0x42dde51096c7442291508688f45cae4b777e62dd7963dc1d39a1c528ba35aa8e85e82f541737d524c2a1509a1124c244572a915ccb2442512910944a42713a04c08e5f00299440087a0171178008c460023118416c96816)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s686 := certify 127 8 (roots 127) cs127 [s668,s670,s674,s677,s679,s680,s682,s685] (u127 5 336 0x1225b1863f904b230a5b25a04fe40c3244822087d208a460c82453b9f481043ffc2087d1b0235ffebeb47f18411c31b1cc70838c70c6718dc21c21c6a9c65706338ce354cebb7063867146710dc109a238a326a3dc10e1122815924c85b258a0b209320a20ff02d824c62b055c05407f19618fb4147349886d12f741b4e27d10a11c70a29c39425d70dea1d1c38a2b83c84a9e082c91c1e4b2a7e08088e1809ee0691ee18918e06086e12914e04094e12092e0490470d6104e1c9f24b86b4f985c3820b83d8417055857e0f7615782820ba20027f485c4fe88b88e90010e86036e988b6e86886e98018e848a6e92026e84004e9289271c00070e4e91dce93a5f70e000eba000e8aa8a7d755147a280038e0003808d2171d1a7ce02000)

theorem lower127 : Claim 127 9 := fromSearch 25924 (by decide +kernel) s686.property

theorem lower186 : Claim 186 5 := fromLift 5 16 269578304 lower170 (by decide +kernel)

theorem lower182 : Claim 182 5 := fromLift 5 32 269550912 lower150 (by decide +kernel)

theorem lower158 : Claim 158 5 := fromLift 5 4 268531520 lower154 (by decide +kernel)

def c190_0 := ruleFor 190 lower172 none (by decide +kernel)

def c190_1 := ruleFor 190 lower186 none (by decide +kernel)

def c190_2 := ruleFor 190 lower182 none (by decide +kernel)

def c190_3 := ruleFor 190 lower174 none (by decide +kernel)

def c190_4 := ruleFor 190 lower54 none (by decide +kernel)

def c190_5 := ruleFor 190 lower158 none (by decide +kernel)

def cs190 : Cuts (goalAt 190) := [c190_0,c190_1,c190_2,c190_3,c190_4,c190_5]

def dict190 : Nat := 0x88282105024140a808220a06808120a0580812060b08024280684012180584012142a0a094140d05088000a828a8a00682898902100024000581834300b0a0820020a002200048010003068610001058510005400108808400090000212002220210102404222002420048408202088081202

def d190 := unpackCases dict190 6

def u190 := unpackShort dict190 6

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s687 := certify 190 6 (roots 190) cs190 [] (u190 3 180 0x472243a91cde54228a00895229bc68010c008e9433b84800c9b829504cd1942e8feaf93d27ef6e9513bab60e41db9b2141d0dd09b7e27c90984da9435c8c2264ce2b831066c6a8401788a5f4d0afa35108cb795ad4569cdc4ca708a922258d804539564e0c0948912ecd48e79547369990b341f9654fc9866)

theorem lower190 : Claim 190 7 := fromSearch 269579584 (by decide +kernel) s687.property

theorem lower191 : Claim 191 8 := fromLift 8 1 30020 lower190 (by decide +kernel)

theorem lower103 : Claim 103 5 := fromLift 5 1 1365 lower102 (by decide +kernel)

theorem lower207 : Claim 207 7 := fromLift 7 1 26230 lower206 (by decide +kernel)

theorem lower222 : Claim 222 8 := fromLift 8 4 302081600 lower218 (by decide +kernel)

theorem lower250 : Claim 250 8 := fromLift 8 16 319905856 lower234 (by decide +kernel)

theorem lower246 : Claim 246 8 := fromLift 8 32 303105344 lower214 (by decide +kernel)

theorem lower241 : Claim 241 6 := fromLift 6 16 4 lower225 (by decide +kernel)

theorem lower243 : Claim 243 7 := fromLift 7 2 68 lower241 (by decide +kernel)

theorem lower231 : Claim 231 7 := fromLift 7 1 1365 lower230 (by decide +kernel)

def c255_0 := ruleFor 255 lower253 none (by decide +kernel)

def c255_1 := ruleFor 255 lower254 none (by decide +kernel)

def c255_2 := ruleFor 255 lower251 none (by decide +kernel)

def c255_3 := ruleFor 255 lower247 none (by decide +kernel)

def c255_4 := ruleFor 255 lower239 none (by decide +kernel)

def c255_5 := ruleFor 255 lower223 none (by decide +kernel)

def c255_6 := ruleFor 255 lower223 (some (2,i4,i7)) (by decide +kernel)

def c255_7 := ruleFor 255 lower254 (some (1,i4,i7)) (by decide +kernel)

def c255_8 := ruleFor 255 lower253 (some (1,i4,i7)) (by decide +kernel)

def c255_9 := ruleFor 255 lower251 (some (1,i4,i7)) (by decide +kernel)

def c255_10 := ruleFor 255 lower247 (some (1,i4,i7)) (by decide +kernel)

def c255_11 := ruleFor 255 lower223 (some (1,i4,i7)) (by decide +kernel)

def c255_12 := ruleFor 255 lower127 none (by decide +kernel)

def c255_13 := ruleFor 255 lower239 (some (2,i6,i7)) (by decide +kernel)

def c255_14 := ruleFor 255 lower191 (some (1,i4,i7)) (by decide +kernel)

def c255_15 := ruleFor 255 lower239 (some (3,i6,i7)) (by decide +kernel)

def c255_16 := ruleFor 255 lower239 (some (0,i6,i7)) (by decide +kernel)

def c255_17 := ruleFor 255 lower111 none (by decide +kernel)

def c255_18 := ruleFor 255 lower127 (some (0,i4,i6)) (by decide +kernel)

def c255_19 := ruleFor 255 lower238 (some (0,i6,i7)) (by decide +kernel)

def c255_20 := ruleFor 255 lower235 (some (0,i6,i7)) (by decide +kernel)

def c255_21 := ruleFor 255 lower189 (some (1,i4,i7)) (by decide +kernel)

def c255_22 := ruleFor 255 lower55 none (by decide +kernel)

def c255_23 := ruleFor 255 lower239 (some (1,i5,i7)) (by decide +kernel)

def c255_24 := ruleFor 255 lower239 (some (2,i5,i7)) (by decide +kernel)

def c255_25 := ruleFor 255 lower191 (some (2,i4,i7)) (by decide +kernel)

def c255_26 := ruleFor 255 lower190 (some (1,i4,i7)) (by decide +kernel)

def c255_27 := ruleFor 255 lower107 none (by decide +kernel)

def c255_28 := ruleFor 255 lower239 (some (1,i6,i7)) (by decide +kernel)

def c255_29 := ruleFor 255 lower238 (some (1,i6,i7)) (by decide +kernel)

def c255_30 := ruleFor 255 lower235 (some (1,i6,i7)) (by decide +kernel)

def c255_31 := ruleFor 255 lower237 (some (2,i6,i7)) (by decide +kernel)

def c255_32 := ruleFor 255 lower237 (some (1,i6,i7)) (by decide +kernel)

def c255_33 := ruleFor 255 lower239 (some (3,i1,i7)) (by decide +kernel)

def c255_34 := ruleFor 255 lower245 (some (1,i4,i7)) (by decide +kernel)

def c255_35 := ruleFor 255 lower127 (some (1,i4,i6)) (by decide +kernel)

def c255_36 := ruleFor 255 lower215 (some (1,i4,i7)) (by decide +kernel)

def c255_37 := ruleFor 255 lower238 (some (2,i6,i7)) (by decide +kernel)

def c255_38 := ruleFor 255 lower235 (some (2,i6,i7)) (by decide +kernel)

def c255_39 := ruleFor 255 lower127 (some (3,i4,i6)) (by decide +kernel)

def c255_40 := ruleFor 255 lower238 (some (3,i6,i7)) (by decide +kernel)

def c255_41 := ruleFor 255 lower109 none (by decide +kernel)

def c255_42 := ruleFor 255 lower235 (some (3,i6,i7)) (by decide +kernel)

def c255_43 := ruleFor 255 lower103 none (by decide +kernel)

def c255_44 := ruleFor 255 lower127 (some (2,i4,i6)) (by decide +kernel)

def c255_45 := ruleFor 255 lower237 (some (3,i6,i7)) (by decide +kernel)

def c255_46 := ruleFor 255 lower254 (some (1,i5,i7)) (by decide +kernel)

def c255_47 := ruleFor 255 lower253 (some (1,i5,i7)) (by decide +kernel)

def c255_48 := ruleFor 255 lower251 (some (1,i5,i7)) (by decide +kernel)

def c255_49 := ruleFor 255 lower247 (some (1,i5,i7)) (by decide +kernel)

def c255_50 := ruleFor 255 lower127 (some (1,i4,i5)) (by decide +kernel)

def c255_51 := ruleFor 255 lower207 none (by decide +kernel)

def c255_52 := ruleFor 255 lower206 none (by decide +kernel)

def c255_53 := ruleFor 255 lower205 none (by decide +kernel)

def c255_54 := ruleFor 255 lower203 none (by decide +kernel)

def c255_55 := ruleFor 255 lower222 (some (2,i4,i7)) (by decide +kernel)

def c255_56 := ruleFor 255 lower199 none (by decide +kernel)

def c255_57 := ruleFor 255 lower221 (some (2,i4,i7)) (by decide +kernel)

def c255_58 := ruleFor 255 lower206 (some (3,i1,i7)) (by decide +kernel)

def c255_59 := ruleFor 255 lower203 (some (3,i1,i7)) (by decide +kernel)

def c255_60 := ruleFor 255 lower199 (some (3,i1,i7)) (by decide +kernel)

def c255_61 := ruleFor 255 lower219 (some (2,i4,i7)) (by decide +kernel)

def c255_62 := ruleFor 255 lower215 (some (2,i4,i7)) (by decide +kernel)

def c255_63 := ruleFor 255 lower238 (some (1,i5,i7)) (by decide +kernel)

def c255_64 := ruleFor 255 lower219 (some (1,i4,i7)) (by decide +kernel)

def c255_65 := ruleFor 255 lower207 (some (3,i1,i7)) (by decide +kernel)

def c255_66 := ruleFor 255 lower221 (some (1,i4,i7)) (by decide +kernel)

def c255_67 := ruleFor 255 lower237 (some (1,i5,i7)) (by decide +kernel)

def c255_68 := ruleFor 255 lower236 (some (1,i5,i7)) (by decide +kernel)

def c255_69 := ruleFor 255 lower217 (some (1,i4,i7)) (by decide +kernel)

def c255_70 := ruleFor 255 lower213 (some (1,i4,i7)) (by decide +kernel)

def c255_71 := ruleFor 255 lower93 none (by decide +kernel)

def c255_72 := ruleFor 255 lower95 none (by decide +kernel)

def c255_73 := ruleFor 255 lower125 (some (1,i4,i5)) (by decide +kernel)

def c255_74 := ruleFor 255 lower127 (some (2,i4,i5)) (by decide +kernel)

def c255_75 := ruleFor 255 lower218 (some (1,i4,i7)) (by decide +kernel)

def c255_76 := ruleFor 255 lower202 (some (0,i1,i7)) (by decide +kernel)

def c255_77 := ruleFor 255 lower211 (some (1,i4,i7)) (by decide +kernel)

def c255_78 := ruleFor 255 lower91 none (by decide +kernel)

def c255_79 := ruleFor 255 lower87 none (by decide +kernel)

def c255_80 := ruleFor 255 lower223 (some (2,i6,i7)) (by decide +kernel)

def c255_81 := ruleFor 255 lower191 (some (1,i5,i7)) (by decide +kernel)

def c255_82 := ruleFor 255 lower223 (some (3,i6,i7)) (by decide +kernel)

def c255_83 := ruleFor 255 lower223 (some (0,i6,i7)) (by decide +kernel)

def c255_84 := ruleFor 255 lower127 (some (0,i5,i6)) (by decide +kernel)

def c255_85 := ruleFor 255 lower190 (some (1,i5,i7)) (by decide +kernel)

def c255_86 := ruleFor 255 lower189 (some (1,i5,i7)) (by decide +kernel)

def c255_87 := ruleFor 255 lower219 (some (0,i6,i7)) (by decide +kernel)

def c255_88 := ruleFor 255 lower215 (some (0,i6,i7)) (by decide +kernel)

def c255_89 := ruleFor 255 lower191 (some (2,i5,i7)) (by decide +kernel)

def c255_90 := ruleFor 255 lower219 (some (2,i6,i7)) (by decide +kernel)

def c255_91 := ruleFor 255 lower215 (some (2,i6,i7)) (by decide +kernel)

def c255_92 := ruleFor 255 lower223 (some (1,i6,i7)) (by decide +kernel)

def c255_93 := ruleFor 255 lower222 (some (2,i6,i7)) (by decide +kernel)

def c255_94 := ruleFor 255 lower223 (some (3,i0,i7)) (by decide +kernel)

def c255_95 := ruleFor 255 lower250 (some (1,i5,i7)) (by decide +kernel)

def c255_96 := ruleFor 255 lower246 (some (1,i5,i7)) (by decide +kernel)

def c255_97 := ruleFor 255 lower219 (some (1,i0,i7)) (by decide +kernel)

def c255_98 := ruleFor 255 lower215 (some (1,i0,i7)) (by decide +kernel)

def c255_99 := ruleFor 255 lower127 (some (1,i5,i6)) (by decide +kernel)

def c255_100 := ruleFor 255 lower219 (some (1,i0,i1)) (by decide +kernel)

def c255_101 := ruleFor 255 lower215 (some (1,i0,i1)) (by decide +kernel)

def c255_102 := ruleFor 255 lower221 (some (2,i6,i7)) (by decide +kernel)

def c255_103 := ruleFor 255 lower219 (some (3,i0,i1)) (by decide +kernel)

def c255_104 := ruleFor 255 lower215 (some (3,i0,i1)) (by decide +kernel)

def c255_105 := ruleFor 255 lower215 (some (1,i0,i2)) (by decide +kernel)

def c255_106 := ruleFor 255 lower219 (some (1,i6,i7)) (by decide +kernel)

def c255_107 := ruleFor 255 lower219 (some (1,i0,i3)) (by decide +kernel)

def c255_108 := ruleFor 255 lower215 (some (1,i6,i7)) (by decide +kernel)

def c255_109 := ruleFor 255 lower221 (some (1,i6,i7)) (by decide +kernel)

def c255_110 := ruleFor 255 lower223 (some (3,i1,i7)) (by decide +kernel)

def c255_111 := ruleFor 255 lower219 (some (1,i1,i7)) (by decide +kernel)

def c255_112 := ruleFor 255 lower215 (some (1,i1,i7)) (by decide +kernel)

def c255_113 := ruleFor 255 lower219 (some (3,i4,i7)) (by decide +kernel)

def c255_114 := ruleFor 255 lower127 (some (3,i5,i6)) (by decide +kernel)

def c255_115 := ruleFor 255 lower219 (some (3,i6,i7)) (by decide +kernel)

def c255_116 := ruleFor 255 lower215 (some (3,i6,i7)) (by decide +kernel)

def c255_117 := ruleFor 255 lower127 (some (2,i5,i6)) (by decide +kernel)

def c255_118 := ruleFor 255 lower235 (some (1,i5,i7)) (by decide +kernel)

def c255_119 := ruleFor 255 lower221 (some (3,i6,i7)) (by decide +kernel)

def c255_120 := ruleFor 255 lower191 none (by decide +kernel)

def c255_121 := ruleFor 255 lower254 (some (1,i6,i7)) (by decide +kernel)

def c255_122 := ruleFor 255 lower253 (some (1,i6,i7)) (by decide +kernel)

def c255_123 := ruleFor 255 lower251 (some (1,i6,i7)) (by decide +kernel)

def c255_124 := ruleFor 255 lower247 (some (1,i6,i7)) (by decide +kernel)

def c255_125 := ruleFor 255 lower127 (some (3,i3,i6)) (by decide +kernel)

def c255_126 := ruleFor 255 lower246 (some (1,i6,i7)) (by decide +kernel)

def c255_127 := ruleFor 255 lower54 none (by decide +kernel)

def c255_128 := ruleFor 255 lower126 (some (3,i3,i6)) (by decide +kernel)

def c255_129 := ruleFor 255 lower214 (some (1,i6,i7)) (by decide +kernel)

def c255_130 := ruleFor 255 lower190 (some (3,i3,i7)) (by decide +kernel)

def c255_131 := ruleFor 255 lower55 (some (1,i0,i1)) (by decide +kernel)

def c255_132 := ruleFor 255 lower53 none (by decide +kernel)

def c255_133 := ruleFor 255 lower245 (some (1,i6,i7)) (by decide +kernel)

def c255_134 := ruleFor 255 lower191 (some (3,i3,i7)) (by decide +kernel)

def c255_135 := ruleFor 255 lower189 (some (3,i3,i7)) (by decide +kernel)

def c255_136 := ruleFor 255 lower125 (some (3,i3,i6)) (by decide +kernel)

def c255_137 := ruleFor 255 lower213 (some (1,i6,i7)) (by decide +kernel)

def c255_138 := ruleFor 255 lower243 none (by decide +kernel)

def c255_139 := ruleFor 255 lower231 none (by decide +kernel)

def c255_140 := ruleFor 255 lower254 (some (2,i6,i7)) (by decide +kernel)

def c255_141 := ruleFor 255 lower253 (some (2,i6,i7)) (by decide +kernel)

def c255_142 := ruleFor 255 lower251 (some (2,i6,i7)) (by decide +kernel)

def c255_143 := ruleFor 255 lower247 (some (2,i6,i7)) (by decide +kernel)

def cs255 : Cuts (goalAt 255) := [c255_0,c255_1,c255_2,c255_3,c255_4,c255_5,c255_6,c255_7,c255_8,c255_9,c255_10,c255_11,c255_12,c255_13,c255_14,c255_15,c255_16,c255_17,c255_18,c255_19,c255_20,c255_21,c255_22,c255_23,c255_24,c255_25,c255_26,c255_27,c255_28,c255_29,c255_30,c255_31,c255_32,c255_33,c255_34,c255_35,c255_36,c255_37,c255_38,c255_39,c255_40,c255_41,c255_42,c255_43,c255_44,c255_45,c255_46,c255_47,c255_48,c255_49,c255_50,c255_51,c255_52,c255_53,c255_54,c255_55,c255_56,c255_57,c255_58,c255_59,c255_60,c255_61,c255_62,c255_63,c255_64,c255_65,c255_66,c255_67,c255_68,c255_69,c255_70,c255_71,c255_72,c255_73,c255_74,c255_75,c255_76,c255_77,c255_78,c255_79,c255_80,c255_81,c255_82,c255_83,c255_84,c255_85,c255_86,c255_87,c255_88,c255_89,c255_90,c255_91,c255_92,c255_93,c255_94,c255_95,c255_96,c255_97,c255_98,c255_99,c255_100,c255_101,c255_102,c255_103,c255_104,c255_105,c255_106,c255_107,c255_108,c255_109,c255_110,c255_111,c255_112,c255_113,c255_114,c255_115,c255_116,c255_117,c255_118,c255_119,c255_120,c255_121,c255_122,c255_123,c255_124,c255_125,c255_126,c255_127,c255_128,c255_129,c255_130,c255_131,c255_132,c255_133,c255_134,c255_135,c255_136,c255_137,c255_138,c255_139,c255_140,c255_141,c255_142,c255_143]

def dict255 : Nat := 0x98302704098144022c844013201008a230088a0412810311419100a42013100160505418d010401d90071244043c00170004c100b8002c02138002d00134006428401c1006f401b89220068501618401ac6128401a500684019d006540190290240189006124481005e3100100598008e00228008600208007e001e800745428144a04180091402150401282a804012452802042081021c4044450078081a062106100221185100211e141001b400650018230508e04230188d04230149890160c05c10160503404270505c14230048904124108b0112c05008719140a8102608051400c400d0800c9406240130082c080d0a01e10145081d10302406414800702a100a4402409068a0c200228208208218108204400ad0029088206200084201d0506408881416020c8000f0c03438302804480270105c04238084e024022500880c800160304c5100824020c8501401dc4c010a80421601850868108006e001a8006600188005e001611030412840130240c14980122822071003721020810420c01002d4009c78284008c22042840484300d2008230204c0c030301c01a01120304908401e0c242130504e04130184d04130148d01134046203401c90063401b4220a08818230240161004f1141088098005600148004e0012161808428104401140401050038400f0150908c004838068801d090643500204013416201a141003e400ec8301400b100260442041080ca0031800c404811413020480a10d0048420a88022284007d001440048e0a0342401504401d5007434080c10108909006640181005f4016d005718581005409100241805481003d30900e0600440d00104003cd050191810053401482c0111081002a400782104800444a0812025001a401cd004e089008128084510034400d844061e0e08830064201a0a400542140260a1004b2090900332080600108003e000e80036000c06480c0420490812400482813024004d00864016900564010e000b80028120325001003a400a100252a0a200094021026020880c29201101424054001854401181043000682012062505021050b041001d04410341c14541006a0840d005d4011d00461048100322100848188002032100c4406202400042301400d48500090c021020f05011282180015181190052024000100851490015008001d005521004510110408583840231003906414160605812000615141008d401e90079401fc4105088050011400082408094004109220206260058081d010b072000506450240210411008e4020444082a0804442128290007402001300401ec61200d001000e2a0e100032280900514023c983809800212804c050009400bc341040020610112141000c0b011002440010512004941003f04821000d401f5002e1a0e0120480010342004471001c0a4250030114005110300010031188810045400282501114045420110090005150005200090050050089402900401f1005c12180190004408880411040522020809006c40110160011800440108425001610c0846064005c8c00401fa0003401210040118088900260008100129001a182044082000a80100424002c82102301012010a8086420148401918260408802046001a020b0a0880104a005818064245410224048a002060082801301048043004084800b0008404128081a002a000211080008490016080686012040480111908410310d084820120085840160004a42088404301220e0241c302004c001a10049011a0804a00210406800800042c14301401120160404414220605850204801220086004303120201109120a084000a4048220160a052500d0c0150522040110509200624206440228080000151421080150110400682805440161430080c060048601a10084005242222003414090408101048501610150502c20090101118090a02200105081901301008414044504404088084140084801100090008820088804400111008828090501202048008800121004101084044800090801110044041210

def d255 := unpackCases dict255 10

def u255 := unpackShort dict255 10

def w176 : Sig := 0xffffffffffffffffffffffff00000000ffffffffffff0000ffffffff00000000

def s688 := certify 255 7 ([w54,w176,i6,i7,i0,i1,i2,i3]) cs255 [] (u255 5 106 0x1dc3b897c08204598285616ab681089086083d0c29c53e025dc72c302584b59a0ca10750800aa15c0002284700022a3ec017260c930017624404925021037f820817ee10403610423e40c40c618ccb041b2274492409409266027cc3160fe6181099096c1858a)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s689 := certify 255 8 ([w176,i6,w19,i7,i0,i1,i2,i3]) cs255 [s688] (u255 5 327 0x4b9c1df009e1dc4b84f12f81d80f73b4084a843dc4a88908e084584f20c388116708b30279860ce106509528c189527e51c513d186387f8418f23ffa3861b018538971ca29f01cb8097184b8791832841ec20f21ec3a8430560ce18d39635618319f35114345f0df14d142f4000e2421545e9210ae70000cb000182e845196174238c000afc00301da4555f8ed1f7800028f2410092802813c108d005c981f4c11a1f46498019501c14f7153d514014b64410e2121bd6c909f0e1045b220830690beb6434dc30822bf104006380b6463ec00822d9104c07791f5b23bc81e020814d22824810812932860818eca031994196096142053aa60a654c5542551dcfc84913e6198403c04fc0313f81861c530c090a847150a89908c083898614184a0e2184439461470ca2b08eb81c326e2df028a3f2514104d083584d582282)

def s690 := certify 255 8 ([w176,i5,i6,w19,i7,i0,i1,i2,i3]) cs255 [s688] (u255 5 138 0xee1dc4be1a04224220811661d1ec689c709512a70c107a18538a7c04b865083a84e39618d0c334d0c33400550ae000114238001151f602492810b930649803cf0003cf00206ff04102fdc20806c20847c818924812818c319960934c20934c204933013e618109908c086184c38781c3c0fc841ac20c2606130a38781c3c0288445c2)

def s691 := certify 255 8 ([w54,i5,w146,i6,i7,i0,i1,i2,i3]) cs255 [s688] (u255 6 132 0xedd84bb01020458c1c2544a8e142585a96680844820d01d0614e29d8097387160c0c81d03869528b1ac80ba020152b000112300004547d8017230648c01f3e00002ec48802448a0209b9e0409797040801b040847c8184c58862c0896d2d84083644e8448901149031809f183010990427d809f610a8166060b16198061622fa8b0a)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s692 := certify 255 9 ([w146,i6,w19,i7,i0,i1,i2,i3,i5]) cs255 [s689,s690,s691] (u255 5 402 0xe194560c8f0386c8c5be05147e4a28209a10d709ab04504184a28c0e260610e221cc28a38a51445ce29171467143591728a306708328689460c6893f28e284b9c1df009e1dc4b84f12f81d80f73b4084a843dc4a88908e084584f20c388116708b302798714e38b989512a4f44a8952e671df35114345f0df14d14c94618e1fe105928ffe8e186c0614e25c728a7c072e025c612e1e460ca107b083c87b0ea10c158338634e58d5860c632518636281d03b2540e81cd88c35407053dc54f5450050bd000389085517a4842b9c00032c00060ba1146585d08e3000323000c07691557e3b47de0000a3c904024a00a04f042340172607d304687d19260061c50003561f43eabf0fa1f4d5800142053aa60a654c554254a6c410e2121bd4d909f0e10464a20830690bea6c34dc308229b104006380a6c63ec008229b104c07791f5363bc81e020814d22824810812932860818eca03199419609629b1043a296d2da9b4b696ce88822f55ea1244f98660c8f013ec8c4fe0618714c30238a11c53f22644faf313f819fc04f99f13f82f5c0e2af30a2714ca843)

def w177 : Sig := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000000ff000000

def s693 := certify 255 7 ([w177,w16,i6,w19,i0,i1,i2,i5]) cs255 [] (u255 6 112 0x152260a15090a8a4489f0a10a21470c81ea3d610f90d01e028670e150a011230023a474a5c80042ccd800152b00a54852a09797040801b0424a496414b085f540409b9e042f65ec4cc8982a60a12ec0538a7007801150898211f04098481830738e76025fb76466292e8a2040d3c813626c7cc2)

def s694 := certify 255 7 ([w21,w16,i6,w19,i0,i1,i2,i5]) cs255 [] (u255 6 112 0x1b64261015090a8a4489f0a26a40a8901ea3d610f970e150a01123001e24082900042ccd80a54852a09797040801b04252407e90085f5404812404c90982a60a12ec0538a7007801150898211f68418101020738e7edd98097982a60af41bd06015805408f026e90406090843e44d89b)

def s695 := certify 255 8 ([w16,w15,i6,w19,i0,i1,i2,i3,i5]) cs255 [s693,s694] (u255 6 133 0xa993050a8485450a99305083144fc50e18269c709b1363e610a31c3b52244f850680e8306f5e830f51eb087c86f5e833870a8500a958000891801e0000f0021666c01e0000f52a429504dcf0204bcb820400d822608113042faa02260811348a1084c9f9982a60a6025fb7612ec0538a7007801150898211fa0c194213e39c73917)

def w178 : Sig := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00cc00ff00cc

def s696 := certify 255 7 ([w178,i1,i6,w19,i7,i0,i2,i5]) cs255 [] (u255 5 109 0x5602dca2b409ba0a5206291145f1429c53e025cf4e883f416240e920298532aa102fdc20847c8188554aae8a0d5206690201b0881039c4f9040bf132411b237514004508e0004547d803746ea9a0a92064915155141ec60f6309e081bf012e1dc3b84129a1840df2000ae0055)

def w179 : Sig := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffccccffffcccc

def s697 := certify 255 8 ([w179,i1,i6,w19,i7,i0,i2,i3,i5]) cs255 [s696] (u255 5 129 0xac05b94528134a2920a1528aaaa2841944fca0ee1dc4be0405453ea0df1be74c4686b38e2e7145f143041e8614e29f012e7ad44d2a12b2564e4468c1ec3d8c14c29955081bfc1040bf708211f206229d5146a84ec9d88d272201b0930824c52d93842347389f11a8a54132a1951551400550ae000114238001151f6028028bdc4690b192325e)

def w180 : Sig := 0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc

def s698 := certify 255 7 ([w180,w136,i6,w19,i0,i2,i3,i5]) cs255 [] (u255 5 112 0x14a04d28a482854ae38a8a106513f2880a8a7d41be37ce988d0ee1dc4be1145f143041e863d6a269509592b272234538a7c04b8530a6554206ff04102fdc229d5146a84ec9d88d272211f18e2229504ca82e45c88d086134a09a51c2f4e17a1ec60f630930930410fb50c302188dc1e00049251e)

def s699 := certify 255 8 ([w136,i1,i6,w19,i7,i0,i2,i3,i5]) cs255 [s698] (u255 5 138 0x2b016e514a04d28a482854a106513f283b87712f8101514fa837c6f9d311b145f143041e8614e29f012e7ad44d2a12b2564e4468530a6554206ff04102fdc20847c8188a75451aa13b2762349c88f0c710a588d1ce27c46a29504ca9c71514f32b652f3c30cb79ec035e0924a3c2e45c88d086134a09a51c2f4e17a1ec60f6309309360c9f08fa104d45430c0862340)

def w181 : Sig := 0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc

def s700 := certify 255 7 ([w180,w181,w15,w19,i0,i2,i3,i5]) cs255 [] (u255 6 109 0xa993050a4833050a54a850a54a85083144fc50e18269c70df1be74c4689b1363e6176ec25d82244f850680e8306f5e8312b2564e4468f51eb087c8a714ec04bd2a429504dcf0204bcb82260811313b2762349c842faa020423ed8202547084c8991830469ab0000cdc2542c181ed11ac0648c9)

def s701 := certify 255 8 ([w181,i1,w15,w19,i7,i0,i2,i3,i5]) cs255 [s700] (u255 7 132 0x14616c141498981414905302828a8a82a08289f853b3b4b1807601a70edede3a7193535f08444447c140c80740d4d4c612c0cf4f40c4ac959398cf4f442f852520a2a046e3c04045e2e040423e40c10981010989d93b8c27208cbcd81010be940219327022a0a2a0a2461ccb43915831d50633660d460a8550aa33db1866f2320039b9a790951a14c4c0606461ab)

def w182 : Sig := 0x3333333333333333000000000000000033333333333333330000000000000000

def s702 := certify 255 8 ([w182,i1,w15,w19,i7,i0,i2,i3,i5]) cs255 [] (u255 6 129 0xa602dc50a993050a483305083144fc576ec25d80e18269c70df1be74c46a244f850680e830a714ec04b86f5e8312b2564e446d2a429504dcf0204bcb820423e40c2260811313b2762349c840031c23264e09c385428054ac000448c0001151f600f00011fc5c8b911a7a10a42a284d89b1f3087a8f5843e4be845010738e713f08fcc2132264619b)

def s703 := certify 255 7 ([w21,w180,i1,i6,w19,i0,i2,i5]) cs255 [] (u255 5 109 0x15a04dd0529031482aaa8a8a2f8a3d3a20fd058903a4814e29f012e14c299550817ee10aa955d0808d520669020c718e20847c638840bf13241037c6f9151551432c61963101d080e837c81be400820407409a504d283d8c1ec613c10378410c1d0c204d9070bd17a76025c3b877)

def s704 := certify 255 8 ([w180,i1,w15,i6,w19,i0,i2,i3,i5]) cs255 [s698,s700,s703] (u255 6 134 0x54c982854242a2854c982852a5428418a27e2870c134e384d89b1f3086b8e1d207b7612ec11227c28340741837af4187a8f5843e437af418538a76025e95214a826e781025e5c113040898217d5011304089820c718e10211f18e101508426460e71ce27e12a14a850bd1c2f470cb0c32c3501f741528fb8428e16a1f63ecd58064c1818564ec181ab)

def s705 := certify 255 7 ([w21,i6,w19,i7,i0,i1,i2,i5]) cs255 [] (u255 5 109 0x2b016e515a04dd0529031488a2f8a14e29f012e7a7441fa0b1207491c71514004508e0004547d803746e901d0549030c80a614caa840bf708201b08211f20621552aba1011aa40cd210207389f20817e264809a504d283d8c1ec6002b801544f040df80970ee1dc20860e861026c8)

def s706 := certify 255 8 ([w177,w15,i6,w19,i7,i0,i1,i2,i5]) cs255 [s705,s693] (u255 6 128 0x14c05b8a153260a15090a8a153260a4489f0a14e29d80970debd061ea3d610f90debd060d01e028670e150a0112300004547d803c0001e0042ccd803c0001e0152b00a54852a09797040801b040847c81844c10226085f54044c1022609b9e046428c10e71ce27e15084264623314974576ec25d80e18269c709b1363e616a)

def w183 : Sig := 0xffffffffffffffffffffff00ffffff00

def s707 := certify 255 7 ([w183,i3,i6,w19,i0,i1,i2,i5]) cs255 [] (u255 7 112 0x292130282a2a18288888f82a1213812199c539f8a06fefe0638382a0a0044460023a474a5a42dd8a6631400a8ac00a4a4145408bc5c0808006c0849492a414b73b14b6e2811b8f010bd97b98483061460c28404221222a6a28f89830a306152c614d4c003c004541098108f81011ef480c0c8ae630967676)

def w184 : Sig := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffff00ffffff00

def s708 := certify 255 8 ([w184,i3,i6,w19,i7,i0,i1,i2,i5]) cs255 [s705,s707] (u255 7 129 0xa30b60a0af64c0a0a8a860a0a30660c288888f82a9a98c259aafb353f666714e7e281bfbf8181bfbf818e0e0a82801111800008afd0026b4d6b07d96ec53318a005456001e00001e52520a2a045e2e04040036040423e40c1161ac3f6582e76296dc502371e02130202131efa2028ae69e8a8a81731141860c28c1853b3b4b187b604444454d451f16a)

def w185 : Sig := 0xaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaaaaaffaaaa

def s709 := certify 255 7 ([w185,i0,i6,w19,i7,i1,i2,i5]) cs255 [] (u255 3 106 0x140c45bd5104d214b031601182307f429c5383112e19483a90b181d300e41c82ba008a11c008a8fb01ba3748090a98187004607389f8817e2662815d02b40be0bd1001ba211f20684404880e46403da05740ac3db07b600ae0154188970ee1dc80a9101c8c8)

def w186 : Sig := 0x55005500550055005500550055005500550055005500550055000000550000

def s710 := certify 255 6 ([w33,w186,i6,w19,i1,i2,i5]) cs255 [] (u255 6 84 0x140a60214a206288a54852a4489f0ac80ba0216220748814e29d83c70e150a01123001ba3748082152206188004547d80102fc4c88c588608982a60af41bd0601580542808608258204d8860f020448901101)

def s711 := certify 255 6 ([w113,w186,i6,w19,i7,i2,i5]) cs255 [] (u255 6 81 0xa602dc50a053010a51031442244f850a714ec04be405d010b1103a44101039c4f88102fc4c88982a60af41bd066025fb7622208608258204d8800f0204a54853e0112300004547d804890126c588608)

def s712 := certify 255 7 ([w186,i0,i6,w19,i7,i1,i2,i5]) cs255 [s710,s711] (u255 6 106 0x53016e285029808528818a211227c28538a76025f202e80858881d221c3854280448c0001151f6006e8dd202085488186208081ce27c40817e264452a42953c45a61de3c0028c03c61a9824480880e2c43044c153057a0de8300ac02a3012fdbb140430412c1026c404)

def w187 : Sig := 0xf0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0f0f0fff0f0

def s713 := certify 255 7 ([w187,i2,i6,w19,i7,i0,i1,i5]) cs255 [] (u255 5 106 0xac05b94568b68294818a471c545004547d803746e901d0549030c80022847002b8000550a614caa8403610423e40c42aa5574202354819a40817ee13c1040de81039c4f9040bf13247c57c50a714f80970f3a075d2c22c206f8af8ac04b8770ee1041e74308b08)

def w188 : Sig := 0xf000f000f000f000f000f000f000f000f000f000f000f000f0000000f0000

def s714 := certify 255 7 ([w188,i2,i6,w19,i7,i0,i1,i5]) cs255 [] (u255 5 106 0xac05b94568b68294818a471c545004547d803746e901d0549030c8002e85d00298532aa100d84108f90310aa955d0808d520669020690d222040e713e4102fc4c91145f158483c2068650ca1e7471cb0838a15e50017400aa206910379d80770ee1043074308136407b)

def s715 := certify 255 7 ([w151,w19,w21,i6,i0,i1,i2,i5]) cs255 [] (u255 6 109 0xa51031440db213082244f850b1103a441352054483870a8500891800a91030c40f120414852a429504bcb820400d820d5103344129203f4808210844c153057a0de8300ac02a04781370c1026c44820c884c153050976029c53803c008a844c108fc21039c476ecc04bb4)

def s716 := certify 255 7 ([w151,i7,w21,i6,i0,i1,i2,i5]) cs255 [] (u255 5 109 0xa520629036d08108a2f8a16240e9209aa05450e38a8a002284700549030c81e2810540298532aa102fdc20806c20d52066904a501fa810864404d2826941ec60f630015c00aa278206f30813640494324342826e9a1e941fa0dd1ba40742aa55742022fc813240410c1d30)

def s717 := certify 255 6 ([w113,w33,w21,i6,w19,i2,i5]) cs255 [] (u255 5 84 0x15a04dd05290314846a5147ee28be28f4e883f416240e920538a7c04b902fc4c9040ad15a404d2826941ec60f630410c1d0c204d9180970ee1dc00ae0055410d1d0f1c15f0011423803746ee83f454902b48104d80)

def s718 := certify 255 6 ([w34,w33,w21,i6,w19,i1,i5]) cs255 [] (u255 5 84 0xad026e8294818a45451458f8e2a286e8dd203a0a920619001151f6000114238040bf1324102b45690134a09a50015c00aa104307430813645c25c3b8770f6307b190434203144555a101d07e8b12056902097097)

def s719 := certify 255 7 ([w33,i0,w21,i6,w19,i1,i2,i5]) cs255 [s717,s718,s710] (u255 5 109 0x15a04dd052903148a8a2aa8a2f8a3d3a20fd058903a4814e29f012fc71514004508e00dd1ba407415240c320022a3ec0205f89920815a2b4809a504d283d8c1ec6002b8015420860e861026c8386b9033b012e1dc3b95515510318518c40c00d606840741fa2b4815a408821a101)

def s720 := certify 255 7 ([w117,i0,w21,i6,w19,i1,i2,i5]) cs255 [] (u255 5 106 0x568137414a40c52228be28f4e883f416240e9238e2a28008a11c01ba37480e82a481864102fc4c90134a09a507b183d8c0057002a8410c1d0c204d90278206fc04b8770ee14c299550817ee10403610aa955d0808d52066918142dca14e29f012e45401f602039c813e4103)

def s721 := certify 255 6 ([w34,w113,w21,i6,w19,i7,i5]) cs255 [] (u255 5 81 0x2b016e515a04dd0529031484081ce27c8205f899202694134ac04b8770ee104307430813640015c00aa1ec60f6371c1458c022a3ec01ba37747854902b48104b808a228fd8a714f8097d207e8e8458902b48)

def s722 := certify 255 7 ([w113,i0,w21,i6,w19,i7,i2,i5]) cs255 [s717,s721,s711] (u255 5 106 0x1580b728ad026e8294818a44517c50a714f80973d3a20fd058903a484081ce27c8205f899202694134a0f6307b1b012e1dc3b8410c1d0c204d9070d7d8e002b80154a46a51fbd8614636d806bc3481fa3a115a40ad204e382be002284700022a3ec01ba37747854902b48)

def s723 := certify 255 7 ([w123,i0,w21,i6,w19,i7,i2,i5]) cs255 [] (u255 5 106 0xac05b94568137414a40c52228be28538a7c04b9e9d107e82c481d242040e713e4102fc4c90134a09a507b183d8d80970ee1dc20860e861026c813c10378015c00aa14c299550817ee10423e40c42aa5574202354819a471c54500114238001151f600dd1ba407415240c3236)

def s724 := certify 255 7 ([w34,i0,w21,i6,w19,i7,i1,i5]) cs255 [s718,s721] (u255 5 106 0x5602dca2b409ba0a5206291c7151401151f600dd1ba407415240c320008a11c04081ce27c8205f899202694134a002b80157012e1dc3b8410c1d0c204d917187b8f187b183d8c5545163b8014605ccd435dda101d0808ad20569024511550a714f8097d080e840458902b48)

def s725 := certify 255 7 ([w61,i0,w21,i6,w19,i7,i1,i5]) cs255 [] (u255 5 106 0x5602dca2b409ba0a5206291c7151401151f600dd1ba407415240c3210207389f20817e264809a504d2800ae0055c04b8770ee1043074308136409e081bc3d8c1ec60a614caa8403610423e40c42aa5574202354819a44517c504500238029c53e025e43e9217416240e922e)

def w189 : Sig := 0x3333333333333333333333333333333300000000000000000000000000000000

def s726 := certify 255 7 ([w189,i1,w21,i6,w19,i0,i2,i5]) cs255 [] (u255 5 106 0x568137414a40c52228be28f4e883f416240e920298532aa102fdc21552aba1011aa40cd20403610817e264809a504d283d8c1ec613c10378410c1d0c204d900057002ae025c3b877e38a8a0022847006e8dd203a0a92061918142dca14e29f012e47c420622039c813e40fb)

def s727 := certify 255 7 ([w54,i5,w21,i6,i7,i0,i1,i2]) cs255 [] (u255 5 106 0xa714f809716240e920d69ad09ad1e9d107e8004508e0004547d802a48186400915ab803746e901d040bf708201b08211f20620d5206690224354e21552aba1014081ce27c8205f89920c48c8dc6002b801544f040df80970ee1dcc204d901345aacb0410c1d026e1004d09a40d320a)

def w190 : Sig := 0xffffffff00000000ffffffff00000000ffff000000000000ffff0000

def s728 := certify 255 7 ([w190,i5,w21,i6,i7,i0,i1,i2]) cs255 [] (u255 5 109 0x538a7c04b8b1207491145f14004508e0004547d802a48186471c5450817ee10403610423e40c41aa40cd20298532aa207389f20c48c8dc6002b801544f040df80970ee1dcc204d90cdca15e50db1b675ca14a40c52343d283f41ba37480e8554aae84050430d05f902648082183a04d)

def s729 := certify 255 7 ([w12,i7,w21,i6,w19,i0,i1,i2]) cs255 [] (u255 5 106 0x3d3a20fd058903a4819d6bab1a28be28008a11c01ba37480e82a48186400ea59d81c71514205fb84100d842aa5574202354819a408e9d9c8814c2995568504dd0817e264821d2ba320814a31480f6307b1800ae005513c10378410c1d0c204d9070b758ab142694134a830)

def s730 := certify 255 7 ([w97,i7,w21,i6,w19,i0,i1,i2]) cs255 [] (u255 5 106 0xf4e883f416240e920538a7c04b8011423803746e901d0549030c8008a8fb0040bf708201b08554aae84046a903348108f90310817e2648207389f203d8c1ec6002b801544f040de104307430813646025c3b8774228be2b8e2a28298532aa2b409ba0a5206290504d09a50b7)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s731 := certify 255 8 ([w21,i6,w19,i7,i0,i1,i2,i5]) cs255 [s709,s712,s713,s714,s715,s716,s719,s720,s722,s723,s724,s725,s703,s726,s727,s728,s729,s730] (u255 5 327 0xe194560b7f0386ac45be0514abca2b409ba2ad09a13742b415650a52038902ac388c520a23e6a22868be1be29a2b018538971ca29f01cb8097184bc1118f4e81ef48221ed07e83683ac616243440eb687490311501c14f7153d51401432c00060ba1146585d08e30002ab000c0769155523b47de0000405e1bba00374808040747b41be00a9203e9037c3e8c320020a1029d530532a62aa12a52220830690bea3c34dc308228110400638091c63ec008221f104c07791f4123bc81e0209a4c55480885574134203310115a20d52282056d033481083ca62d013e41180b31ce27c5989fc0820289046810c5f851086267420809a704d2868941346884d28e283d9c1ec6262307b1ae1ec638600e00908bd0ae00bd00909c154438421228fc103588424e0df81d809709e25f009e1dc4b9c1dc289c16825420a225460e876810c279841c4043384d9013c8)

def s732 := certify 255 8 ([w21,w15,i6,w19,i7,i0,i1,i2,i5]) cs255 [s694] (u255 6 128 0x14c05b8a153260a15090a8a153260a4489f0a14e29d80970debd061ea3d610f90debd0670e150a0112300004547d803c0001e0042ccd803c0001ea54852a09797040801b040847c81844c10226085f54044c1022665a9a0e71ce27e1508426444c153057a0de8300ac02a04781373012fdbb0e34e3047421f226c4d973)

def s733 := certify 255 8 ([w21,i3,i6,w19,i7,i0,i1,i2,i5]) cs255 [] (u255 7 138 0xa30b60a0af64c0a0a8a860a22223e0aa6a630966abecd4fd999c539f8a06403a0638382a0a004446000022bf4009ad35ac1f65bb14cc62800909210052520a2a045e2e04040036040423e40c1161ac3f6582e76296dc502109212087be2b9a7a2a2a05cc45410513f0a963096303434f65008088a424c0a4c0a7a067a06002420048410848210930963096020250f60c0c428a0e)

def s734 := certify 255 8 ([w166,i3,w15,i6,i7,i0,i1,i2,i5]) cs255 [] (u255 7 132 0xa30b60a0a426b21415ec98141460cc18511111f055353184b7a7a212496abecd4fd81bfbf8181bfbf818e0e0a82801111800008afd000010b336009ad35ac1f6005456001e00001e52520a2a045e2e04040036040423e40c1010be94022c3587ecb0411b8f01098101098f79973734f210628214c4c1830a30614eced2c619d9c9250bd8d3c4440701017b173)

def s735 := certify 255 8 ([w167,i3,w15,i6,i7,i0,i1,i2,i5]) cs255 [] (u255 6 132 0x14c05b8a1509ac8a143de60a4489f0a14e29d80971ea3d612496aa3dda98f70d01d0670e150a0112300004547d800042ccd804d69ad608f7004849080a54852a09797040801b040847c8184085f5404586b0c7bac10842484843de39c7389f8430418a27e284bb012ec124c249309a341ee5ce60a982bd06f41801210048421090842580976025e124913226411a7)

def s736 := certify 255 7 ([w25,i5,i6,w19,i0,i1,i2,i3]) cs255 [] (u255 6 112 0x2040f7c813626c7cc2467312ecc0d01d0610a21470c81ea3d610f935a6b661a0152b00011230023a474a5c80042ccd8000914f0009b9e0409797040801b0424a496414b085f54040890d3042f65ec4cc875f20b48990843cc6025fb7612ec0538a7003ec01150840c211f04098481830738e7142a630)

def w191 : Sig := 0x5555555555555555555555555555555555555555555555555555555555550000

def s737 := certify 255 7 ([w191,i5,i6,w19,i7,i1,i2,i3]) cs255 [] (u255 6 109 0x76ec25d815548cfd20d5c4cf7115da504e90680e830a714ec04ba214897d217fc477f11f3a4b86900a958000891800022a3ec01cd4854d226dc485f135ba48d69125c439c4fe2c4904ca4a4c05bd2a490b24a58843d208f370408baf0408d80040840c8f8428902245988bee2554921d2)

def w192 : Sig := 0x3333333333333333333333333333333333333333333333333333333333330000

def s738 := certify 255 7 ([w192,i5,i6,w19,i7,i0,i2,i3]) cs255 [] (u255 5 109 0xee1dc4be0375232e90a9152b745c91be20bf03041e8614e29f012e515231a91432869bc5c9b7e1d8f0206ff04102fdc20847c81887352222926d4da2e537b5be0fdf04745c8e713e2e4b2a42652e3016fc7092c97105443f000570aa00011c228026c20000fb22a004900918610b1725709178)

def w193 : Sig := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0000

def s739 := certify 255 7 ([w193,i5,i6,w19,i7,i0,i1,i3]) cs255 [] (u255 5 109 0x770ee25f03d2195ae865162e1d97071c47d62002a85700022a3ec028a514f5865286e16b70dbc478621037f820806c20847c8188885108653d65fdc282e1f388b1c4215c1ce27dc70b3899722c05bc511c75a289c10f10dd04118008e004512e102f897c0538a7082312194c707ab85446b62)

def w194 : Sig := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000

def s740 := certify 255 7 ([w194,i5,i6,w19,i7,i0,i1,i2]) cs255 [] (u255 7 109 0xa6a630963d26883cd2c023a0238b88d1c10022230000115fa00dcdc202695011841046c8d90f82045e2e04040036040423e40c10aa95534203a8119810574aec110f1008e69e0808be98088230b68282341634a4088608063a064000560054043c046e309676760202c0340c089a080a0a4c82)

def s741 := certify 255 8 ([w22,i5,i6,w19,i7,i0,i1,i2,i3]) cs255 [s736,s737,s738,s739,s740] (u255 6 129 0x76ec25d80e18269c709b1363e6123398976618b1c38b98680e830a714ec04b863128dc30f51eb087c9ad35b30d1310c18d880a958000891800022a3ec01e0000f0021666c00048a7800d70000d584dcf0204bcb820400d820423e40c22608113042faa02044869820a30810e8a83d408738e713f0b04213226464c602de6709858b4c8421e60a)

def s742 := certify 255 7 ([w54,w23,i6,i7,i0,i1,i2,i3]) cs255 [] (u255 6 109 0x76ec25d809b1363e61083144fc50680e830a714ec04b8f51eb087ca244f8500a958000891800022a3ec00021666c03870a8504dcf0204bcb820400d820423e40c2042faa0252a42953af1ce39c4fc2352284c8a2c2d45096345a54a0024400bb0827420d92c6181618321160408b0a)

def s743 := certify 255 8 ([w23,i5,i6,w19,i7,i0,i1,i2,i3]) cs255 [s742] (u255 6 138 0x3b7612ec070c134e384d89b1f308418a27e283407418538a76025c318946e187a8f5843e51227c28054ac000448c0001151f600f000078010b33601c38542826e781025e5c102006c10211f206113040898217d501295214a9418e71ce27e160842644c8a6070c50a66fa850a3538050e1a238689a0c683003c00f044c11330386c0e18205408b8c190b04c)

def s744 := certify 255 8 ([w54,i5,w15,i6,i7,i0,i1,i2,i3]) cs255 [s742,s727] (u255 6 132 0xedd84bb013626c7cc21463871a1467312ecc1c304d38e0d01d0614e29d80971ea3d610f90c6251b8635a6b661a341831a0152b000112300004547d800042ccd803c0001e00914f0044600035109b9e0409797040801b040847c8184085f54044c102260890d3045010228506c8738e713f08650842644ccc602de64c8485666a9858b0a040a8117)

def s745 := certify 255 8 ([w190,i5,w15,i6,i7,i0,i1,i2,i3]) cs255 [s728] (u255 5 132 0x1dc3b897c04d89b1f210c359c71a1106513f286083d0c29c53e025c7a8f50863e463128dc68a2f8a002a85700008a11c0008a8fb00021666c078001ee38a8a1037f820817ee10403610423e40c410bed024c20930530a6554a0c738e713e10cc2b038651410dac9453370e250c138d39c9c46912300f00f0930936070f038610cc7899132104d)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s746 := certify 255 9 ([w15,i6,w19,i7,i0,i1,i2,i3,i5]) cs255 [s695,s697,s699,s701,s702,s704,s706,s708,s731,s732,s733,s734,s735,s741,s743,s744,s745] (u255 6 393 0x1c3142983b36070dd98b7602852b1142a84c98abe64ca02852c7142a17084b1f8215842852ad14288bcc98aae64c22e2851831c20c50d11460c6893f143850971dd984eec25e7097603982a91c3a8095182a444a9a7a03870f99c26e10e1363e470f9853a128f50291cb98e1c87c70e2e6824b9be348850644f833e146852e30c1870ff80b8c7fba1c183300c29c4b8e514ec072b012e184bae30c1a87af4b8fd7aa0183420c3d47c9a1eb08d421f2187cae30c18d8faf4b8fd7a3621832a00e051e70a8f2a140050bd00007121a82f490d61c0000cb000035c8832ee460c0003b3000180ed22a794768fb60000503c79a88001400006a278f18b000217c2164c7e19b840000d73c78d5800028c00035678f0a0949526a42930a5411526108107109dc98484bc1c1022e30810368bc98742e0c102261081000c70098463b600102261081180ef23e98477903601022614c9a80408984204a099326108121282fa985428841022614c98e884089842043a299318530ac8caea32a654e28213f0873b016639c4f8b313ec2142a07e681c58508e29f9132bccfc8c)

def w195 : Sig := 0xffffffff00000000ffffffff00000000ffffffff0000ffffffffffff00000000

def s747 := certify 255 7 ([w54,w195,i6,i7,i0,i1,i2,i3]) cs255 [] (u255 6 109 0x76ec25d809b1363e610a12c2d4b340422410680e830a714ec04b8f51eb087cca945903e405d0100a958000891800022a3ec00021666c0001762440122450104dcf0204bcb820400d820423e40c2042faa02041b22742244808a481ce39c4fc24320a1022cc0c161833f161408b02)

def s748 := certify 255 8 ([w195,i5,i6,w19,i7,i0,i1,i2,i3]) cs255 [s747] (u255 6 138 0x3b7612ec1a02112084d89b1f30870af2ae384a8e1c2543407418538a76025f202e8087a8f5843e4d060c6903860c81c054ac000448c0001151f6009122808010b3360001e3c0001e3c0026e781025e5c102006c10211f206112240450217d50102264c102264c1240e71ce27e1219050811c36070d87005a81608421e10a386c0e1b022e0a8021833042)

def s749 := certify 255 8 ([w54,i5,w150,i6,i7,i0,i1,i2,i3]) cs255 [s747] (u255 6 132 0xedd84bb013626c7cc2142585a96680844820d01d0614e29d80971ea3d610f99528b1ac80ba020152b000112300004547d800042ccd80002ec48802448a0209b9e0409797040801b040847c8184085f5404083644e8448901149039c7389f8486414204384a8e12a6831a0c7b401ed00a022808be461172da8b11705401166060b1685f8b0a)

def s750 := certify 255 8 ([w190,i5,w150,i6,i7,i0,i1,i2,i3]) cs255 [] (u255 6 132 0xedd84bb013626c7cc2106289f8a0d01d0614e29d80971ea3d610f94489f0a0152b000112300004547d800042ccd8070e150a09b9e0409797040801b040847c8184085f5404a54852a1ce39c4fc21c25470953418d063da00f68050114045f23380ae02a80a75ea0c50a916ed450268224102c9d011224501244808a0290c010243308116)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s751 := certify 255 9 ([w150,i6,w19,i7,i0,i1,i2,i3,i5]) cs255 [s748,s749,s750] (u255 6 393 0x1c3142983b76070ddb8b7602850d7142814c0428e616042812c7142a17084b1f8215842851831c20c50d11460c6893f143850971dd984eec25e7097603980f71cd01095043dc4a889043810f99c26e10e1363e470f9853a13e348850644f833e146853410c1870ff80d047fba1c183300c29c4b8e514ec072b012e184bf80d9017a05e3d7404181420c3d47c9a1eb08d421f2187caa00e051e70a8f2a140050bd00007121a82f490d61c0000cb000035c8832ee460c0003b7000180ed22aafc768fb60000143c481002450014047811c5000217c216affe19b840000a0949526a42930a5411528508107109dca1484bc1c1023410810368bca1742e0c102285081000c700a1463b600102285081180ef23ea147790360102024c90a0448082022898a28508121282faa154288410219532b204fc21cec0598e713e2cc4fb08508e29f94327161420471417022fc051c515c35701445c50e2e6384a9c512a389e8e12a5cc4a9a3626833410c69a09a0c6c431ed3567b401c5007b55f9ed006ac0283a2a0228508a142a80874421c530a614e2985a07157a8c)

def s752 := certify 255 8 ([w31,i5,i6,w19,i7,i0,i1,i2,i3]) cs255 [] (u255 6 138 0x3b7612ec070c134e384081163119cc4bb3070d11a2383407418538a76025c318946e18e1c5830d69ad9868d060c68054ac000448c0001151f600f0000785c8c1923002453c03e0001f026e781025e5c102006c10211f20611304089b16218b022434c1140408a1418c6027c60c43263c64c602de61f99858b4c198060a6027d809f04088bd0c03210c)

def s753 := certify 255 8 ([w54,i5,w18,i6,i7,i0,i1,i2,i3]) cs255 [] (u255 6 132 0xedd84bb01020458c467312ecc1c304d38e0d01d0614e29d8097387160c35a6b661a341831a0152b000112300004547d8017230648c00914f004460003b909b9e0409797040801b040847c8184c58862c0890d30450102286431809f18310ce0193874e1c62432370c00f003c113044cc141b013f0a61f92c5814c602de64c19f860a)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s754 := certify 255 9 ([w18,i6,w19,i7,i0,i1,i2,i3,i5]) cs255 [s752,s753] (u255 6 402 0xe18a14c1a1b0386d0c5bb01428fc8a154264c14732650142b00a143380cc1c0438c1428c18e10628688a3063449f8a1c284b8eecc277612f384bb01cc0fc8e1d404a8c1836254d3d01c3845ce103070811638458c9c31f1a44283227c19f0a342972860c387fc05ca3fdd0e0c1980614e25c728a76039580970c25d72860d43d7a5cbebd500c196063830d1c586960c0c315007028f38547950a00285e80003890d417a486b0e00006580001ae44197723060001a18000c0769158323b47db0000281e3cee4000a00003b93c78468017233e0c11bf0648c0030504a4a9352149852a08a94384083884ee50e425e0e08117284081b45e50fa1706081143840800638050e31db000811438408c07791f50e3bc81b0081143a64d4020450e102504c98604c4b146218a062c08b179af36427c60c60d0d809f68627d80c18714fca19a07e681c5183261179828fc8a99aa60a22e2a71739c38fc8e9d06e70e2e63bd1b1f4197286f4b97d063621801ab0078fc9e0106401e3567821d1089943a608a1c2263a29982f56027ccf89f6067d809f5e627ce2af5047e4c2c2)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s755 := certify 255 10 ([w19,i7,i0,i1,i2,i3,i5,i6]) cs255 [s692,s746,s751,s754] (u255 5 436 0xd289f30c34b80b31ce6944f8b313e697030c262144c306b8410c2146144218990d611811170c251445cc0e261170c21c44391730a288b9c328a22f8117c08b9c334a2dc8be051445c8b94511708268445c8b84d588b845045cc4584f20b9987105cc459c22cb99813cc22e60ce10645ca1a251173063449f91728e28b9897383b973c0278772e625c278972e781d81731ee7685cc212a11731ee2544497308e08d8d83386c4c69c36363561b1306308bfcd4445ca1a222ff0df11729a28b99731862e670ff0825ccd88ffe8b99c30c6c7018539b112e394539b1c072e06c44b8c25cd887918329b1083d846c43c87b0ea6c4218235623401726acc0fa61ab11a1f4649ab300308bd407045ca7b822f53d511728028b98bd0002e671210aa5cc5e9210ae5cce00036232c000d88c174229b1196174239b118000d59ab00035780ed22a6acd58ed1f66af0000356a3c91ab08048d5a80286ac27823a260818ce8d940633a265061d1b04b08b94205322f54c14c8b9531445ea12a2e65cc410b99c424379733a2427c2e670821b13622086c460d217cd89d10d371b118410d59ab10435600c700d59d118fb1ab00410e89d11043a380ef23e744e88ef20674701043a214d21d150490e884204745499433e9cccf849)

def w196 : Sig := 0x3333333333333333333333333333333333333333333300003333333333330000

def w197 : Sig := 0xffffffffffff0000ffffffffffff0000

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s756 := certify 255 7 ([w196,w197,w12,i0,i2,i3,i6]) cs255 [] (u255 4 252 0x5f6c84a4743091d5f61843f91d611d11613d0c72045b845b027b211b87891d1a2476118d1842475c474169b8cd7016e816b0cc6be63387f84168e3fc1db8c683fa45e474c4760f9a0e91dd11d6103182d05218d80a580b480b5af908e2121bd4490907ae211a390860d217d4486905e6211a291dd91d04e475a2827566474847421ca4c44659421a23086c9484aca4e4d63744aa6b32ee948d296905945320b31ba94892902936673486cc8882994ad2911dc039b62c4765204a43b70206003b65208600303eb02187d216c0304a800e24215c4a9210aae000c00682e847305d08ba0008020295120a48a2480a400b002491df11db785d91d011d)

def s757 := certify 255 7 ([w196,w54,w197,w12,i0,i2,i3,i6]) cs255 [] (u255 6 102 0x616fc30642843040811630509616a58709512a38e1c5830340741a54a2c68d060c6b16218b026e781025e5c1020d913a1140408a08ec2190860953081006341b3045010499630c0900102036001842c600ad500008d1000450100001222ec0211)

def w198 : Sig := 0xffffffffffffffff0000000000000000ffffffffffff00000000000000000000

def s758 := certify 255 7 ([w198,i6,w197,w12,i0,i1,i2,i3]) cs255 [] (u255 6 109 0x10207be4081022c60e12a25470680e8308510a38641c38b060640e81c300a9580008918011d23a52e40b918324600f9f0004dcf0204bcb820400d8212524b20a5e2c4316044b696c20268224102c9d011224501244808a02145810218264102a16010c90adc63290ad6442)

def s759 := certify 255 6 ([w191,i6,w197,w12,i1,i2,i3]) cs255 [] (u255 6 84 0x252496479251ab899ee20d01d06472495de9252ff88efe20152b000112300776496469254db890be2485559fa4488852fa448734a9a44948b2449884ca44850224c4497f6208f370408baf0408d80042964946c9255988bee2)

def s760 := certify 255 6 ([w192,i6,w197,w12,i0,i2,i3]) cs255 [] (u255 4 84 0x1e24761091d1522a56e8b93041076645e4760e91d28650d378b9206f07a4205f05e47764755991d4da9b45ca6f90dd32f2914531b291cd22329039b4a45944cca4204a1291d0fe474015c2a80011c228080dc800924745d91d630858b9)

def s761 := certify 255 6 ([w193,i6,w197,w12,i0,i1,i3]) cs255 [] (u255 6 84 0x26a215df88516270ec9c0152b0045e2152588528670b59c09b9e040801b044722150d8852fe70a09cc87a5aee428a514f5e444288721eb4488b0852ce704c9c040836438217f1c0cea006011804408b825e90216508518707a9c)

def s762 := certify 255 6 ([w194,i6,w197,w12,i0,i1,i2]) cs255 [] (u255 5 84 0x4d502a280b1207490004508e00f14082a02a4818640817ee1040361094a03f501aa40cd2343d283f41ba37480e8554aae84074416405f902648082183a10807f206e860820057002a89e081bc24a0b2061026c8)

def s763 := certify 255 7 ([w22,i6,w197,w12,i0,i1,i2,i3]) cs255 [s759,s760,s761,s762] (u255 6 103 0x284b0b52c26c4d8f9844c470e6921a03a0d2a516343d47ac21f235c3065fa02a56000224600005d89100008599b0028c0004221373c0812f2e081003608106c89d0810bea809a8204783206098408031a0d980223002042280824cb182cc21501322641422df8b0c)

def w199 : Sig := 0xccccccccccccccccccccccccccccccccccccccccccccffffcccccccccccccccc

def s764 := certify 255 6 ([w199,i6,w197,w12,i0,i2,i3]) cs255 [] (u255 6 84 0x2040f7c818630d988c90d01d0610a21470c82d65ad648c909b9e04097970424a496414b42e85c64ac9080140404d044820593a0248901140428b02048661022448a022f65eff480152b00011230023a474a5c818306480)

def w200 : Sig := 0xffff0000000000000000

def s765 := certify 255 7 ([w200,i6,w197,w12,i0,i1,i2,i3]) cs255 [s764] (u255 6 103 0x4081ef9026c4d8f9841a03a0c214428e1903d47ac21f202a560002246004748e94b90008599b001373c0812f2e08100360849492c829610bea80809a089040b27404489140491202280851604090cc2045ecbdfe90384a8e12a6831a0c84406a00a022808ca80c)

def s766 := certify 255 7 ([w28,i6,w197,w12,i0,i1,i2,i3]) cs255 [] (u255 6 109 0xa12c2d4b081022c60680e834a9458d1c38b0600a958000891800017624400b918324604dcf0204bcb820400d82041b2274262c43160c13081006341b300446004084501049963059821919406020462817b2f6c864e1d387063418d00f803e0450114489059942)

def s767 := certify 255 7 ([w8,i6,w197,w54,i0,i1,i2,i3]) cs255 [] (u255 6 106 0x73212a38698d3fd38509616a583407418d060c68316d341a54a2cb2c054ac000448c017d8000c8014d2be0000bb1220026e781025e5c102006c1140408a0219d501020d913a124482cad44a98408031a0d9806c002042280824c17e13f6ad163059832fdf95b8c)

def s768 := certify 255 7 ([w11,i6,w197,w54,i0,i1,i2,i3]) cs255 [] (u255 5 103 0x3b212a710408b306083d0cd0c334e3961800550ae0001142380bec003217260c93040dfe08205fb84100d84a041280c618ccb04ab104033430670036802044a041261043307398b30b605ecbd8433161422d5609612d6685d8024401b2209d102487f)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s769 := certify 255 8 ([w197,w54,w12,i0,i1,i2,i3,i6]) cs255 [s756,s757,s758,s763,s765,s766,s767,s768] (u255 4 315 0x87d8cb061b2090c21fecc61e5630c58430864c4218431aec608b09e8639022dc22d813d879dc286c346c79c688b5b3acd85ce6922544ab6112a255a4b9c0b4dc66b80b740b5866361319c3fc20acb1fe0edc635b412d659825d8d6597ad2cbd697e98cb2cc65fbad08d00b9607d608d0fa3258060bd001c4842a8bd24215dc000cb000c174228cb0ba11cc0023b002de1768efc246c0023b1461ad088008ec004228ed08b0818c168290c6c052c05a405ad848471090deb348483d7108b2c8430690beb343482f31088ec8400c702cd18e0dc0422cd212c09c6cacd04e276c422cd0520a5e0908b34847820a414a7356a12421e021b02cb021859086cc304a85912aec604ae010b82c821360da56ba32cb36b019c1800ed56a1b408ec03b7020498202956a0a48b3480a7024ec45ecad71849a45c18a7322e2)

def s770 := certify 255 7 ([w196,w54,w12,i7,i0,i2,i3,i6]) cs255 [] (u255 6 100 0x196ac0c185bf0c2ca4a1121020458c4080c0e142585a961ba48cb92387160c0d01d060d9b9069528b1a28a48c692c58862c09b9e0409797040824c4784083644e8439a48889260d8dc001842c600ad500008d100045010000d82040001222ec002)

def w201 : Sig := 0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeaaaaeeeeeeeeeeeeaaaa

def s771 := certify 255 5 ([w25,i6,w201,w12,i2,i3]) cs255 [] (u255 6 60 0x2040f7c819e33d248990d01d0610a21470c829e53c4ca4909b9e04097970424a49640e108d9db2842f65ec43c804d044820593a020428b024890109304304c82)

def s772 := certify 255 6 ([w22,i6,w201,w12,i7,i2,i3]) cs255 [s771] (u255 6 72 0x4080c0e142585a9619e33d24899680844820d01d060d9b9069528b1a29e53c4ca49c80ba0261a8504dcf0204bcb820412623c2041b22742046ced942244808a3899b5604c8992c21cb0c)

def s773 := certify 255 5 ([w8,w28,w201,i7,i2,i3]) cs255 [] (u255 5 57 0x208183882045983041e86183387319c72c30bd881bfc1040bf708209311e20630c665816822420832875082c82d85248124f08a582)

def s774 := certify 255 6 ([w28,i6,w201,w12,i7,i2,i3]) cs255 [s773] (u255 5 78 0x82060e142b0b55882045983041e861833873182584b59a71cb0cc040dfe08205fb84104988f1041b227440c618ccb0c602c9861a90d6605a0890820ca1d42082cb010452c1492054099)

def s775 := certify 255 6 ([w8,i6,w201,w54,i7,i2,i3]) cs255 [s773] (u255 6 75 0x810181cd010890434c69fe9c284b0b52c1a03a0c1b3720d901740418b69a0d2a5162eac98021458104dcf0204bcb820412623c224480940433aa02041b227425ab427ff6a0421c10c)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s776 := certify 255 7 ([w201,w54,w12,i7,i2,i3,i6]) cs255 [s772,s774,s775] (u255 4 225 0x1658cc0b30b616459859c31894d8cb061b0d70c21fecc60a3630410c41ac21899130422c27a18e408b708b604f661c0842c84f043809f80b2e71e770a1b0d1b1e71a22d6ceb0f77035109510f712a2244e102d3719ae02dd02d6198944c670ff0825d47f83b718c5d4c6c0e50ce5d472873c18d6d04b2ea60976358baeb41e74194461079307516844648c8314228ed08a11526a6103182d05218d80a580b480b528908e2121bca390907ae210ba90860d217ca386905e6210a390981de24ca38ef11f8210a3909604e364a382713b621040a4129472025110451c14829)

def w202 : Sig := 0xcccccccccccccccccccccccccccccccccccccccccccc0000cccccccccccc0000

def s777 := certify 255 6 ([w25,i6,w202,w12,i0,i2,i3]) cs255 [s771] (u255 2 84 0x22044f784919e33d24899c1041de10a2147084929e53c4ca4981bc1ec817c17c24a494248e18035c8d9db2c01542b8011423823a47448849042d5082f65ec4384940d444a41943aa04a095093402c0ba02604c240344ca)

def s778 := certify 255 7 ([w22,i6,w202,w12,i7,i0,i2,i3]) cs255 [s777,s772] (u255 6 97 0x20406070a12c2d4b0cf19e9244cb40422410680e8306cdc834a9458d14f29e26524e405d0104dcf0204bcb820412623c2041b22742040028c2046ced942244808a3b0d428054ac000448c000081d80000bb12200010b542009099b5604c8992c21cb0c)

def s779 := certify 255 6 ([w8,w28,w202,i7,i0,i2,i3]) cs255 [s773] (u255 6 81 0x2040607081022c60680e8306cdc831c38b0604dcf0204bcb820412623c20401a8262c431617b0152b000112300002076002ca594488c04d044820593a024890124f04cad0224480020428b02)

def s780 := certify 255 7 ([w28,i6,w202,w12,i7,i0,i2,i3]) cs255 [s779,s774] (u255 6 106 0x10203038509616a58408116303407418366e41a54a2c68e1c583026e781025e5c10209311e1020d913a102001461316218b1800a9580008918000103b000017624401652ca88c60c316060c353a860268224102c9d01244809402b060102145811224001099)

def s781 := certify 255 7 ([w8,i6,w202,w54,i7,i0,i2,i3]) cs255 [s779,s775] (u255 6 100 0x4080c0e680844821a634ff4e142585a960d01d060d9b906c80ba020c5b4d069528b17509b9e0409797040824c478448901280800518408675404083644e8464c010a2c08054ac000448c000081d80090029a57c00017624405ab427ff6a0421c10c)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s782 := certify 255 8 ([w202,w54,w12,i7,i0,i2,i3,i6]) cs255 [s770,s776,s778,s780,s781] (u255 4 300 0xb2c6605985b0b22cc2ce18c4a6c65830d8c58610ff663098b18208621ae10c4c898211613d0c72045b845b027b30e04216427821c04fc059738f3b850d868d8f38d116b67587bb81a884a887b8951122708169b8cd7016e816b0cc4a263387f8412ea3fc1db8c62ea6360728672ea39439e0c6b6825975304bb1ac5d75a0f3a0ca23083c983a8b426103182d05218d80a580b480b528908e2121bca390907ae210ba90860d217ca386905e6210a390981de24ca38ef11f8210a3909604e364a382713b621040a4129472025110451c1482923242008c80a391914602108c9190628451da11422a4d446400607d61190fa66d806119001c4842a91924215dc00119000c174229190ba11cc0011900303b4409191da1b7000119002de176467c246c001190d72)

def w203 : Sig := 0xffffffffffffffffffffffffffffffffffffffffffffccccffffffffffffcccc

def s783 := certify 255 8 ([w203,i1,w54,w12,i7,i0,i2,i3,i6]) cs255 [s770] (u255 4 122 0x605b0b2c6583fb194086c608d11ac42045b010821c3850d85ad880d14fd1c2f45ebb9c05ac3041076630670e6609612eda3d744d34d18da0c618d80b481bc1e90817c1790824c479083644e914ed146d08018e4052420290628ed1d82b526211ac11ac00550ae0004508e000810da000bb1220a017b86b)

def s784 := certify 255 7 ([w68,w196,w54,i7,i0,i2,i3,i6]) cs255 [] (u255 4 100 0x605b0b2c2cb2087242045b010821c386ec8cbcb9c05ac3041076630670e6628b231b20c618d80b481bc1e90817c1790824c4790e6c888c88e81842d800ae1540008e114040524001b191500acc0fecb0a116b609612eda1b2413a4b031c5949891)

def s785 := certify 255 7 ([w189,w196,w54,w12,i0,i2,i3,i6]) cs255 [] (u255 6 97 0xc2df8616525089081022c60a12c2d4b0dd2465c91c38b060680e834a9458d14524634962c431604dcf0204bcb82041b227421cd244449380030858c015aa00011a20008a0200002445d80056865818810181d983720c24c208f08c11dec)

def w204 : Sig := 0x33333333333300003333333333330000

def s786 := certify 255 7 ([w204,w196,w54,w12,i0,i2,i3,i6]) cs255 [] (u255 5 100 0xc583f985952086910408b3050ac2d561ba919749c72c306083d0c12c25acd14548c6a418c31996081bfc1040bf70820d913a21cd4888a5c043302198254e12a70cd0cd0940942c3ed66c6844219810cc12ac4100cd0c19c4a04126b30b604640)

def w205 : Sig := 0xbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbaaaabbbbbbbbbbbbaaaa

def s787 := certify 255 7 ([w205,i0,w54,w12,i7,i2,i3,i6]) cs255 [] (u255 5 100 0x302d85930c583f985952086910408b3208183850ac2d561ba919749c72c306083d0c30670e6304b096b34515231a960a27832c32c1037f820817ee10412623c4106c89d1024824a832c32c002b85500008e114000368810001222ec0092092)

def w206 : Sig := 0xffffffffffffffffffffffffffffffffffffffffaaaaaaaaffffffffaaaaaaaa

def w207 : Sig := 0x1111111111111111111111111111111111111111111100001111111111110000

def s788 := certify 255 6 ([w206,w207,w54,i7,i2,i3,i6]) cs255 [] (u255 6 75 0x32d5818594942258b10c5820408b18810181c374919724284b0b52c70e2c181a03a0c1b3720c514918d252a51651218001842c600ad500008d1000020624c0275002742044890112)

def s789 := certify 255 6 ([w33,w207,w54,w12,i2,i3,i6]) cs255 [] (u255 5 78 0x62c1fcc2ca9043483186332c20811660a1585aac375232e941031438e5860c107a182584b59a28a918d4860ce1cc6e0030859800570aa00011c228000911760147028104c16616924092)

def s790 := certify 255 6 ([w34,w207,w54,w12,i7,i3,i6]) cs255 [] (u255 6 72 0x196ac0c185bf0c2ca4a1121020458c4080c0e142585a961ba48cb9260a25c001842c600ad50000d82040001222ec014700b8204c588608b0d01d060d9b9069528b284890112)

def s791 := certify 255 6 ([w35,w207,w54,w12,i7,i2,i6]) cs255 [] (u255 6 72 0x196ac0c185bf0c2ca4a112387160c0d9b9069528b1a28a48c6920d01d0660a25c001842c6008d10000d82040001222ec014700f0204c58862c4080c28142585a964890112)

def s792 := certify 255 7 ([w207,i0,w54,w12,i7,i2,i3,i6]) cs255 [s788,s789,s790,s791] (u255 6 97 0xcb56060c2df8616525089081022c620406070a12c2d4b0dd2465c91c38b060680e8306cdc834a9458d14524634930512e316218b140e262a14061ae1941814661416d459224044800c21630056a800046880006c10200009117600a384)

def s793 := certify 255 7 ([w197,i7,w196,w12,i0,i2,i3,i6]) cs255 [] (u255 4 105 0xcb07f630598b3621022d8286c2d6ce09e13ddce02d6182083b304b0976d18728e530630c6c05a40de0f4840be0bc841b2274841de3bc80610b6002b855000238450101490001222ec001da3b40476459421ca4374cbca4514c6ca473488c81cda5210258)

def s794 := certify 255 6 ([w34,w206,w196,w54,i7,i3,i6]) cs255 [] (u255 4 75 0x302d8596165904391df630a0a1022d808410e1c376465e478c1798705ed159a81842d800ae154000da2040200911760004708a007323672e71822c4eaa74622744e893206274a2c8d9c88405fa)

def s795 := certify 255 7 ([w206,i0,w196,w54,i7,i2,i3,i6]) cs255 [s794,s788] (u255 5 100 0x1816c2c985952086958619610408b320818386ea465d2142b0b559c72c306083d0c30670e6314548c6a412c25acd345c0030859800570aa00011c2280006d10200400a313a0002445d8065865827553a3113a2757f86b13a2744990313a6cd2366909c246cd2)

def w208 : Sig := 0x5555555555555555555555555555555555555555000000005555555500000000

def s796 := certify 255 6 ([w33,w208,w196,w54,i2,i3,i6]) cs255 [] (u255 4 78 0xb2c821c831863602d42045b06ec8cbc837901e939c05ac3041076628b231b20be405e403085b0015c2a80011c2280401222ec04052405981fd961422d6c12c25db40e6c413a439b22232)

def s797 := certify 255 7 ([w208,i0,w196,w54,i7,i2,i3,i6]) cs255 [s796] (u255 6 100 0x196ac0c2ca4a1121020458c4080c0e1ba48cb92387160c0d01d060d9b90628a48c69268a00610b1802b540002344000360810008228080000911760316218b026e781025e5c10211fd410e69222248b0cfc30b0a116a5a54a2c68b303059c09d)

def s798 := certify 255 6 ([w34,w33,w196,w54,w12,i3,i6]) cs255 [] (u255 4 78 0x6583fb0b2c821c8efb1850508116c143616b61bb232f23c60bcc382f0720610b6002b855000488bb00801b41780011c228017acfc02f36723672e71822cc1041d982584bb68a2c8d9c88405e6)

def s799 := certify 255 6 ([w35,w33,w196,w54,w12,i2,i6]) cs255 [] (u255 5 78 0xc583f985952086958618335c72c302584b59a28a918d4916f861fc1820f437001842cc00238450001222ec00800dbe0000570aa060b23158d9a46cd220832c142b0b5586ea46cd2104f0e)

def s800 := certify 255 7 ([w33,i0,w196,w54,w12,i2,i3,i6]) cs255 [s796,s798,s799,s789] (u255 4 103 0x32c1fd8596410e40b58c05a8408b60a1b0b5b0dd91979021043877380b5860820ecc12c25db45164636460ce1ccc0e40c216c00570aa0004708a0009117601009888f0003688103016b01688f70d7708f30a3306bb103b1b391b391018db1636723672)

def s801 := certify 255 7 ([w117,i0,w196,w54,w12,i2,i3,i6]) cs255 [] (u255 6 97 0xc2df8616525089081022c60a12c2d4b0dd2465c91c38b060680e834a9458d145246349380030858c015aa00011a200002445d80041140400036081018b10c581373c0812f2e08106c89d087349111256865818810181d983720cc14488f)

def s802 := certify 255 7 ([w34,i0,w196,w54,w12,i7,i3,i6]) cs255 [s794,s798,s790] (u255 6 97 0xcb56060c2df8616525089081022c620406070a12c2d4b0dd2465c930512e000c21630056a80006c102000091176001001aeb80008d1000c3be30a0ae3c661d72e3028d72e59fa971b3246cc9043870608b0d01d060d9b9069528b1a28a48d992)

def s803 := certify 255 7 ([w61,i0,w196,w54,w12,i7,i3,i6]) cs255 [] (u255 6 97 0xcb56060c2df8616525089081022c620406070a12c2d4b0dd2465c93068ee000c21630056a80006c1020000911760010450100008d10062c431604dcf020412623c2041b227421cd2444491c38b060680e8306cdc834a9458d1452463492e)

def s804 := certify 255 7 ([w35,i0,w196,w54,w12,i7,i2,i6]) cs255 [s799,s791] (u255 5 97 0x605b0b2618b07f30b2a410d271cb0c1833873182584b59a28a918d486083d0d8289e00308598004708a0001b44080009117600400a3f00002b85500cb0c19be22d30fe78b4435f9e2c8c5636691b348420832c82060e142b0b5586ea46cd2)

def s805 := certify 255 7 ([w118,i0,w196,w54,w12,i7,i2,i6]) cs255 [] (u255 6 97 0xcb56060c2df86165250891c38b0606cdc834a9458d145246349306bee000c21630046880006c102000091176001045010000ad50062c431604bcb820412623c2041b227421cd244449081022c6400ce8320406070a12c2d4b0dd2465c93c)

def s806 := certify 255 6 ([w77,w85,w196,w54,w12,i0,i6]) cs255 [] (u255 4 78 0x1960fec2cb20872602d05ac0c618d80b483644e90e6c888c881a4349081bc34901c81842d840524000488bb00801742e8001742a82cc06c94505c905c90805acb34bb386ec905c8c6076e)

def s807 := certify 255 7 ([w85,i2,w196,w54,w12,i0,i3,i6]) cs255 [s806] (u255 6 103 0x30b7e18594942243162c1820408b18284b0b52c374919724810181d8b10c581373c08106c89d0873491112413468081346808e000c21630056a8002280800009117600100b970000b97002c18b06721da8716e459e1a0b2482c9062c25cb119416490592)

def s808 := certify 255 7 ([w87,i2,w196,w54,w12,i0,i3,i6]) cs255 [] (u255 6 97 0xc2df8616525089081022c60a12c2d4b0dd2465c962c431604dcf02041b227421cd24444904bcb82380030858c015aa0008a0200002445d8004023440070e2c181a03a0d2a51634514918d256865818810181c24c208f0825da3ec00204072)

def s809 := certify 255 7 ([w77,i2,w196,w54,w12,i7,i0,i6]) cs255 [s806] (u255 6 97 0xcb56060c2df861652508962c43160412623c2041b227421cd24444904d1a0204dda023068ee000c21630228080006c10200009117600100b970000b95002c18b063a6d3a9d1660258baa0b2482c906102160c4080c0e2cd2cb0e1ba490592)

def s810 := certify 255 7 ([w88,i2,w196,w54,w12,i7,i0,i6]) cs255 [] (u255 6 97 0xcb56060c2df861652508962c43160412623c2041b227421cd24444904bcb82306bee000c21630228080006c102000091176001008d1001c38b0606cdc834a9458d145246349081022c66e08f0220406070e2cdacb0dd2465c956015003a)

def s811 := certify 255 7 ([w8,i6,w196,w54,i7,i0,i2,i3]) cs255 [] (u255 6 100 0x4080c0e1ba48cb921a634ff4e142585a960d01d060d9b90628a48c6920c5b4d069528b17509b9e0409797040824c478439a48889208675404083644e845f6c09382c48056a8000468800228080006c102001002be5340001222ec05ab427ff22325f890c)

def s812 := certify 255 7 ([w11,i6,w196,w54,i7,i0,i2,i3]) cs255 [] (u255 4 100 0x10821c386ec8cbc908116c3041076630670e6628b231b2e7016b081bc1e90817c1790824c4790e6c888c831863602d5f600ae1540008e114040524000368810080c216c60e713ec2cb20872b0a116b609612eda1b2413a4b031c581c89100bb007f)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s813 := certify 255 8 ([w196,w54,w12,i7,i0,i2,i3,i6]) cs255 [s784,s785,s786,s787,s792,s756,s757,s793,s795,s797,s800,s801,s802,s803,s804,s805,s807,s808,s809,s810,s811,s812] (u255 4 300 0x2cb19816616c2c8b30b38631b9b1960c366e21843fd98c446c2cb2087244610c21c99211613d0c72045b845b027b30e04216427821c04fc059738f3b850d868d8f38d116b675935b86ec84ac93589532f2748169b8cd7016e816b0cc6de63387f8416da3fc1db8c65be63607286756239439e0c6b6825975304bb1ac5d75a417a28b23490598c6cb526103182d05218d80a580b480b557908e2121bd5690907ae2115590860d217d5486905e62114890981de24d478ef11f821140909604e3652382713b6210d982939b2248d99088c814c88c91906287d049e5526a4c1c84300181f5810c3e90b60182540071210ae2549085570006003417423982e845d00040101498b052426240520060001ae3b436e076881146005800527e1236f0bb0d6001192322)

def w209 : Sig := 0xffffffffffffffffffffffffffffffffffffffffccccccccffffffffcccccccc

def s814 := certify 255 7 ([w209,w196,w54,i7,i0,i2,i3,i6]) cs255 [] (u255 4 103 0xc0b61658ca0436305c8c9621022d808410e1c4068a7e8286c2d6dce02d6182083b3183387331eba269a04b0976d0630c6c05a40de0f4840be0bc8412623c8a768a36841b2274852c188436043609178ad5c48891d34d122405241222447d8811222b09100252a119)

def s815 := certify 255 7 ([w180,w196,w54,w12,i0,i2,i3,i6]) cs255 [] (u255 4 106 0x6583fb194086c60b9192c42045b050d85ad880d14fd010821c3b9c05ac3041076609612eda3d744d3430673aa60c618d80b481bc1e90817c179083644e914ed146d0824c1b901584360436095709571b46d10149014d87dd88c8b01b4000636c5a52a119)

def s816 := certify 255 8 ([w196,i1,w54,w12,i7,i0,i2,i3,i6]) cs255 [s814,s784,s815,s785] (u255 4 128 0x1816c2cb1960fec65021b108116c0420870e143616b6203453f4e7016b0c1041d98c19c39982584bb68f5d134d031863602d206f07a4205f05e4209311e420d913a453b451b4232f06e40628ec158b960c96123732d722b31d53131c0d7c0a3b06bb4a846421b021b04ab84ab8da36880a480a70ad70936c4dec46440)

def w210 : Sig := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffcccccccc

def s817 := certify 255 7 ([w210,i6,i1,w54,i7,i0,i2,i3]) cs255 [] (u255 7 100 0x4040301c68051005bdbc74e32805ad0581900e8181999c8199009d0089592b2731894942c4b411b8f0101178b810124a3810909008501240d8109d93b8c27209b1380852cc00828500a41abbc5909069a756424203ea405008500a30a6e46400462d4f462290286020c)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s818 := certify 255 8 ([w209,i1,w54,i7,i0,i2,i3,i6]) cs255 [s814,s817] (u255 4 309 0x1658cc0b30b616459859c3181458c104310510862644c1253632c234468a311a236cc608b09e8639022dc22d813d9870210b213c10e027e02cb9c3ddc0d4425443dc4a889138479dc286c2f6c79c5e8b5b3ac0b4dc66b80b740b5866251319c3fc209751fe0edc6317531b0394339751ca1cf063079d06511841e4c1d45a15b412c969825d8d625bad30818c168290c6c052c05a405a9448471090de51c8483d71085d48430690be51c3482f310851c84c0ef12651c7788fc10820520968404a220a80a684648412231c4894718e31c4890851c84b0271b251c1389db1088451d94b2324641888d1222358f1d8235e388d609160bd122245d09dab8bd84ef15c244488cb122244c465a68cb2ea32cc2444891912224703b4409191da3ef024448d035d042445412341119111925e0a13750ac2a5a8226e2)

def w211 : Sig := 0xffffffffffffffff3333333333333333ffffffffffffffff3333333300000000

def s819 := certify 255 6 ([w180,w211,i6,w54,i0,i2,i3]) cs255 [] (u255 4 81 0xd44224434c6987f922286c2d6c154015c060820ecc19441d4462dba304b09761f6114011c040de0f4840be0bc8094128a8433a0a4841b227484003720511087130a6803e8142b0ac0122094a82)

def s820 := certify 255 7 ([w211,i6,i1,w54,i7,i0,i2,i3]) cs255 [s819] (u255 6 106 0x10203039a0211208698d3fd38509616a583407418366e41b202e808316d341a54a2c4b426e781025e5c10209311e1122404502006c10219d501020d913a10a580a958000891800022ba8012245010029bf00002c24405ab427ff500421c10c2cc0c161408b02)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s821 := certify 255 7 ([w180,w68,w54,i0,i2,i3,i6]) cs255 [s819] (u255 4 243 0x1458c104310510862644c107d63002345c87d11a3240c608b09e8639022dc22d813d83ddc0d4425443dc4a8891384485c15402f404845e85703800b4dc66b80b740b5866251319c3fc209751fe0edc63079d06511841e4c1d45a105d304500cb005d19611c06030818c168290c6c052c05a405a9448471090de51c8483d71085d48430690be51c3482f310820520968404a220a80a6851c8400c7014718e0dc042061b5984bd81843587f6598346d671e7142344f38b575ac61f612f560966b5b43ef409ec364851c809ca389d258884549ab16b007d8303ec4882c0a36390812a02822322)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s822 := certify 255 8 ([w68,i1,w54,i7,i0,i2,i3,i6]) cs255 [s820,s784,s821] (u255 4 309 0x5963302cc2d8591661670c6051630410c414421899130422c27a18e408b708b604f661c0842c84f043809f80b2e70f77035109510f712a2244e102d3719ae02dd02d6198944c670ff0825d47f83b718c5d4c6c0e50ce5d472873c18c1e7419446107930751684c206305a0a431b014b0169016a51211c424379472120f5c42175210c1a42f9470d20bcc4214721303bc499471de23f0420814825a10128882a029a119210031c051c6383701088451d94b11a0172c0fac11a1f464b00c17a00389085517a4842bb80019600182e84519617423980023200608c91523324c6be000a0a390812a028223220c36b3097b03086b0fecb3068dace3ce284689e716aeb58c4b425eac12cd6b6896e813d86c90a3901394713a4b1316b11922e0c7045f0466d6422a4d44bc8c891)

def s823 := certify 255 6 ([w8,w181,w180,w54,i0,i2,i3]) cs255 [] (u255 5 84 0x1a04224282060e1a634c3f86d1be37ce988d1820f43065083a8430673aa30c5b5a189592b27223440dfe08205fb849240941049ec2086768109d93b11a4e422960940940846ac32464a8128100015f0fe6182356)

def s824 := certify 255 7 ([w181,i6,w180,w54,w12,i0,i2,i3]) cs255 [s823] (u255 5 106 0x285616ab6810890a0818386f8df3a62364a9c706d1820f4304b096b3419420ea10c19cea8c4ac9593911a334d0c206ff04102fdc2083644e892481282093d842764ec46939128a042b05985940940846ac1ac46a290951841f4468c9192612f587daca04a040001f58)

def s825 := certify 255 6 ([w80,i6,w180,w54,i0,i2,i3]) cs255 [] (u255 4 84 0x6a211220aa00ae01be37ce988d304107660ca20ea208a008e02564ac9c88d206f07a4205f05e404a0945420063909d93b11a4e652a09148843885c8b911a0b0a116b609612ec32c6c904e9142b0ac012206303f88d)

def s826 := certify 255 7 ([w8,i6,w180,i1,w54,i0,i2,i3]) cs255 [s825,s823] (u255 4 106 0x6a211220420870e1a634c3f84f143616b6304107660ca20ea230671966316dd182584bb175206f07a4205f05e404a0945420c718e4209318e4219d052420d913a412ac217ae17ae19661966a0a82006d0fe28c3f86bb0fbb50541031b62c144421c416c2d89f0fec)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s827 := certify 255 8 ([w180,i1,w54,w12,i0,i2,i3,i6]) cs255 [s815,s821,s824,s826] (u255 4 318 0x129b1960c362621843fd98c0a2c60821882884313226082cb19811a2342c88d11b86304584f431c8116e116c09ec3cee14361a363ce3445ad9d61eee06a212a21ee2544489c2c381085917a08702f70165ce05a6e335c05ba05ac3312898ce1fe104ba8ff076e31ada0965d4c12ec6b175d683ce83288c20f260ea2d08ba98d819619cba8cb1978319840c60b4148636029602d202d4a242388486f28e4241eb8842ea42183485f28e1a417988428e4258138d928e09c4ed884102904b420251105405342324206d18e31ca38c718e1b48428e42606389328e31c63e08492ea4d42343688d6119608d1ae23581b582f4368bd711970bd4a22f5c1b5c32c368cb311930cb2ea32cc1b4c464978a3b06db1190da3eec466d40d74106d15036d04464493526808c9170636c588ce31622f6a2b5a0b02a62822322)

def s828 := certify 255 7 ([w8,w181,i1,w54,i7,i0,i2,i3]) cs255 [s823] (u255 5 103 0x1040c1da0422421a634c3f84f1be37ce988d1820f430c19c398c19420ea10c5b5a189592b27223440dfe08205fb84104988f12490250465fb08219da042764ec46939cb008a582246732d39158c75462bec06b61409408011ab0c919216c2d89f0fea04a046182356)

def s829 := certify 255 8 ([w181,i1,i6,w54,w12,i7,i0,i2,i3]) cs255 [s817,s824,s828] (u255 4 128 0x10821c3850d85ad81a8844886f8df3a623427b9c13cc1041d98c19c39982584bb6832883a889592b272234dad1881bc1e90817c1790824c479083644e90128251509d93b11a4e48cbc1b9080a4149018a11508dc05911a236c35c46a2912a313091b996b91598ea983ee051e03ed9e3da82a084687d19200b380b3825f60d76a0a82)

def w212 : Sig := 0xffffffffffff3333ffffffffffff0000

def s830 := certify 255 6 ([w212,i1,i6,w12,i0,i2,i3]) cs255 [] (u255 6 84 0x2040f7c81be37ce988d0d01d0610a21470c82564ac9c88d09b9e04097970424a496414b2764ec46939080063842f65ec43c80152b00011230023a474a5c81722e4468004d044820593a0248901140428b0204304c822448a02)

def w213 : Sig := 0xffffffffffffffffffffffffffffffffffffffffffff3333ffffffffffff0000

def s831 := certify 255 7 ([w213,i1,i6,w12,i7,i0,i2,i3]) cs255 [s830] (u255 7 103 0x4040301d402d682dbdbc74e30d00a20081900e8181999c819292858689592b27318c804e80408dc780808bc5c0809251c0809b138084ec9dc61390400c60424240214306a0a8c5a588c8c16868c0c029802005456000044460000806c0000ba9000b8b88c0012121402)

def w214 : Sig := 0xccccccccccccccccffffffffffffffffcccccccccccc0000ffffffffffff0000

def s832 := certify 255 6 ([w8,w214,i1,i7,i0,i2,i3]) cs255 [] (u255 5 81 0x1040c1c41022cc1820f430c19c398ce39618206ff04102fdc20824c4788201b0924812818c3199617b002a85700008a11c00040aa5012494085c98324c0b41121041943a8416416c208a582)

def s833 := certify 255 7 ([w214,i1,i6,w12,i7,i0,i2,i3]) cs255 [s832] (u255 4 109 0x8410e1c286c2d6c8408b6182083b31833873304b0976d7380b5840de0f4840be0bc8412623c841b2274818c31b0169000dc8094128a80c5980b2c61a90d6c00550ae0004508e000810da000bb1220172c192c94a821035112210650ea21059c084ab084c1322)

def w215 : Sig := 0xffffffffffffffffffffffffffffffffffffffff33333333ffffffff00000000

def s834 := certify 255 7 ([w215,i1,i6,w54,i7,i0,i2,i3]) cs255 [] (u255 7 106 0x2020180e34028802dede3a719402d682c0c80740c0ccce40cc804e8044ac959398c4a4a16ca046e3c04045e2e0404928e04242402142764ee309c82006302026c4e021918462d4f462290286020c0c7e8c005456000044460000806c0012121402b8b88c0000ba90000a021602)

def s835 := certify 255 7 ([w8,w182,i1,w54,i7,i0,i2,i3]) cs255 [s832] (u255 6 100 0x4080c0e680844821be37ce988d0d01d060d9b906c80ba022564ac9c88d09b9e0409797040824c47844890114080063842764ec4693964c010a2c08054ac000448c000081d80091228085c8b911a00698d3fc2f4b6863418ce845012d5a13ffb50210e08af8c)

def s836 := certify 255 8 ([w182,i1,i6,w54,w12,i7,i0,i2,i3]) cs255 [s831,s833,s834,s835] (u255 4 128 0x420870e143616b606a211221be37ce988d3041076630670e6609612eda0ca20ea22564ac9c88d206f07a4205f05e4209311e420d913a404a094542764ec46939200639018a11508dc05911a236c4c446a2912a31002a857000228470004086d0005d89104a5410b911a070bd70bdd1b46052405240b380b3825f61af614620d62607d)

def s837 := certify 255 7 ([w8,w198,w54,i7,i0,i1,i2,i3]) cs255 [] (u255 6 100 0x4080c0e680844821a634ff0e1020458c0d01d060d9b906c80ba020c5b64d86387160c0152b000112300002076002448a0200534af8017230648c09b9e0409797040801b040824c47844890114086764c84c58862c56ec010a2c0ad5a13ffa842)

def s838 := certify 255 8 ([w198,i6,w54,w12,i7,i0,i1,i2,i3]) cs255 [s837,s758] (u255 6 128 0x4080c0e142585a96680844821020458c1c2544a8e0d01d060d9b9069528b1ac80ba02387160c0c81d03860152b00011230000207600002ec48802448a0217230648c01f3e0009b9e0409797040801b040824c4784083644e844890114c58862c0896d2d846028c50c316060c2da860c04266c18b060979626e5a842)

def s839 := certify 255 7 ([w27,i6,w54,i7,i0,i1,i2,i3]) cs255 [] (u255 6 106 0x10203038418a27e284d89b1f3083407418366e4191227c287a8f5843e4054ac000448c000081d801c385428010b3360026e781025e5c102006c10209311e1295214a8217d5012442b56211a91426451616a284b1a2d2a500122005d8413a106cb00408b0a1832116)

def s840 := certify 255 7 ([w25,i6,w54,w12,i0,i1,i2,i3]) cs255 [s777] (u255 6 109 0xa12c2d4b0e18269c709b1363e610680e834a9458d1a0c18d0f51eb087c80a95800089180001762440223000350021666c004dcf0204bcb820400d82041b227422808114042faa0248845bf16a1084c8991c610200dc836601b000810823c20932c60b300408c273183215a)

def s841 := certify 255 7 ([w191,i6,w54,w12,i7,i1,i2,i3]) cs255 [s759] (u255 6 103 0x810181c284b0b52c555233f48357133dc41a03a0c1b3720d2a51634885225f485ff11dfc402a560002246000040ec00005d891007352153489b71217c4c3552c56ac62c45bf62c4904ca408f370408baf0408d80040823c4984082746c8428902245988bee2)

def s842 := certify 255 7 ([w192,i6,w54,w12,i7,i0,i2,i3]) cs255 [s760] (u255 6 103 0x810181c284b0b52c3749197242a454add1721a03a0c1b3720d2a51634514918d2450ca1a6f1721373c0812f2e08104988f08106c89d087349111249b5368b94dec35381736ac0b91725bf0b92ca484c92015aa00011a20008d820001b04080002445d8004480121830858b9)

def s843 := certify 255 7 ([w193,i6,w54,w12,i7,i0,i1,i3]) cs255 [s761] (u255 6 103 0x810181c284b0b52c7a7235dc82c4e1d93802a56000040ec00005d89100514a29ebc850ce16b381373c081003608104988f08106c89d0888510e43d65fce14138c3522396ac1c385bf1c3859c4c9c0cea006011804408b825e0dcb306345a54a040836418707a9c)

def s844 := certify 255 7 ([w194,i6,w54,w12,i7,i0,i1,i2]) cs255 [s762] (u255 6 103 0x1b3720d2a516347a5a20f682c440e91002246000040ec00005d891003746e901682a440c31012f2e081003608104988f08106c89d08554aab420235440cd10c35083116ac08105bf08102fc4c880ce8340015805408f026e1c610202c2d4b0a1040860b418204d88)

def s845 := certify 255 8 ([w22,i6,w54,w12,i7,i0,i1,i2,i3]) cs255 [s839,s840,s763,s841,s842,s778,s843,s844] (u255 6 122 0x10203038509616a5870c134e384d89b1f3090f8e1c6843407418366e41a54a2c68d060c687a8f5843e504860c4b4054ac000448c000081d80000bb12201118000794010b33600c5800046426e781025e5c102006c10209311e1020d913a1140408a0217d501098840866580d7147c3502856ac42845bf16a1084c8c)

def w216 : Sig := 0xffffffffffffffffffffffffffffffffffffffff0000ffffffffffff00000000

def s846 := certify 255 7 ([w216,i6,w54,i7,i0,i1,i2,i3]) cs255 [] (u255 6 106 0x10203039a02112084d89b1f308509616a583407418366e41b202e8087a8f5843e654a2c81c054ac000448c000081d8009122808010b3360000bb1220026e781025e5c102006c10209311e112240450217d501020d913a11930856ac424320a1021833f161408b02)

def w217 : Sig := 0xffffffffffffffffffffffffffffffff000000000000ffff0000000000000000

def s847 := certify 255 7 ([w217,i6,w54,w12,i0,i1,i2,i3]) cs255 [] (u255 6 109 0xa12c2d4b3404224109b1363e612040604a8680e834a9458d6405d010f51eb087c86cc68300a9580008918000176244012245010021666c000103b0004dcf0204bcb820400d82041b22742244808a042faa0204126a020a845bf164320a1021832c426058c164e608c02)

def s848 := certify 255 7 ([w199,i6,w54,w12,i7,i0,i2,i3]) cs255 [s764] (u255 6 103 0x810181c284b0b52cd010890430c61b311921a03a0c1b3720d2a5163590174045acb5ac91921373c0812f2e08104988f08106c89d08912022885d0b8c95921002808c350a1936ac0c91925bf0c94320a1020152b00011230000207600002ec48802448a0218306480)

def s849 := certify 255 8 ([w200,i6,w54,w12,i7,i0,i1,i2,i3]) cs255 [s846,s847,s848,s765] (u255 6 122 0x10203038509616a59a02112084d89b1f3083407418366e41a54a2c6b202e8087a8f5843e4054ac000448c000081d80000bb122009122808010b3360026e781025e5c102006c10209311e1020d913a112240450217d50118131150ad588508b7e2c8661021c25470953418d06232006b805011404147aa80c)

def s850 := certify 255 7 ([w8,w28,w54,i7,i0,i1,i2,i3]) cs255 [s779] (u255 6 103 0x810181c38609a71c20408b181a03a0c1b3720c683063470e2c1802a560002246000040ec0088c000d42e460c9181373c0812f2e081003608104988f08a0204518b10c58c98219185864efc34c69863418b6802be00a6845010cefe13f6ad022c30b0c)

def s851 := certify 255 8 ([w28,i6,w54,w12,i7,i0,i1,i2,i3]) cs255 [s850,s766,s780] (u255 6 128 0x4080c0e142585a961c304d38e1020458c0d01d060d9b9069528b1a341831a387160c0152b00011230000207600002ec48804460000d717230648c09b9e0409797040801b040824c4784083644e845010228c58862c6028f80c316060c2da86219a03270e9c3831a0c6807c01f022808a0c583160b1372c4bc142)

def s852 := certify 255 7 ([w9,w8,i6,w54,i0,i1,i2,i3]) cs255 [] (u255 6 106 0x1a0211208698d3fd3bb7612ec0340741b202e808316d3418538a76025c054ac000448c009122808014d2be0001153c0026e781025e5c102006c112240450219d5010211f4c10148600a80210e08738e3081006e41b31e00780260898250046017e13f6ad16)

def s853 := certify 255 7 ([w9,i7,i6,w54,i0,i1,i2,i3]) cs255 [] (u255 6 106 0x1a0211208698d3fd3bb7612ec0340741b202e808316d3418538a76025c054ac000448c009122808014d2be0001151f60026e781025e5c102006c112240450219d5010211f2061280210e08738e7166c24161422d4b4a9458728bb0024400d90827420a045810c19f8b18)

def s854 := certify 255 7 ([w197,i7,w8,i6,i0,i1,i2,i3]) cs255 [] (u255 6 103 0x34c69fe9c284b0b52c3994e1c1a03a0c18b69a0d2a5165fa1990e50c02a5600022460000a695f00005d891000192a5001373c0812f2e08100360810cea808106c89d081190ef0833f0b365fa40268224102c9d011224501244808a02a021c1021458118)

def w218 : Sig := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffaaaaaaaa

def s855 := certify 255 6 ([w34,w218,i6,w54,i7,i1,i3]) cs255 [] (u255 4 75 0x2104387035108910ad61f161e305e61c17802a8570004086d04a5410b960c96005d89100022847004966b410a8c0b627d8c108711df13aa9d1889d13a24c8189d15054619d62db2101792d)

def s856 := certify 255 7 ([w218,i0,i6,w54,i7,i1,i2,i3]) cs255 [s855] (u255 4 100 0x10821c381a88448856b0f8b050d85ad8c1041d98c19c399832883a88b7b0feb02584bb12d00550ae0004508e000810da094a82172c192c00bb12200920c682151816c4fb18210e205a27553a3113a2757f86b13a27400dc02744990313a2a0a8c33ac4ee4)

def s857 := certify 255 6 ([w33,w114,i6,w54,i1,i2,i3]) cs255 [] (u255 4 84 0x1a88448856b0f8b037901e90c1041d9832883a88b7b0feb02f90179001542b800114238252a085cb064b0040da4608438831863612c2845ad82584bb103176012200562b0816b03fb2c413a404a09454)

def w219 : Sig := 0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee0000eeeeeeeeeeee0000

def s858 := certify 255 5 ([w219,w114,i6,i7,i2,i3]) cs255 [] (u255 6 60 0x4080c0e1ab899ee20d01d060d9b9062ff88efe2c5699627c68de4be4489f287c384c3e7d8927e270904ea4485559fa4488852fa448497624498969a4)

def s859 := certify 255 6 ([w113,w114,i6,w54,i7,i2,i3]) cs255 [s858] (u255 6 81 0x2040607340422410ad187c460680e8306cdc836405d0116f187f464819684f8c180843822c2845a969528b362cc0c163f608b025833f0c176104e8409b9e0409797040847f604489016ac588604)

def s860 := certify 255 7 ([w114,i0,i6,w54,i7,i1,i2,i3]) cs255 [s857,s859] (u255 6 106 0x10203039a0211208568c3e2303407418366e41b202e808b78c3fa30054ac000448c000081d80091228085c8c1923240cb427c60c0421c104dcf0204bcb82040028c20423fa82244808a62c4302161422d4b4a9458968bb002440166060b2a045812c19f8609d)

def s861 := certify 255 6 ([w33,w32,w8,w54,i1,i2,i3]) cs255 [] (u255 4 84 0x6a2112215ac3e2c1a634c3f88f04208700a4c1041d9832883a88b7b0feb0c5b74630670e6600550ae0004508e094a82172c192c014d2be0008106e012ac215054602d658840521fc54151966277)

def s862 := certify 255 6 ([w34,w32,w8,w54,i7,i1,i3]) cs255 [] (u255 5 78 0x208183b40844842b4c3e261e3b8c3dc00550ae0002043680924a042e4c192601715f00008a11c0cb008a582b82d89fb8250250c3be65c3041e86183387318250250c09662db104b86)

def s863 := certify 255 6 ([w35,w32,w8,w54,i7,i1,i2]) cs255 [] (u255 5 78 0x60ce1cc60ca107508b7987f4c45be187f06083d0c004508e0002043680924a042e4c192601e15f0000aa15c0cb008a582f02d89ff0250250cb0c5a0818a0250250c58c4ee209e04f)

def s864 := certify 255 7 ([w32,i0,w8,w54,i7,i1,i2,i3]) cs255 [s861,s862,s863] (u255 5 103 0x4103076810890856987c4c1a634c3f84f1820f430c19c398c19420ea116f30fe98316d686002a85700008a11c0004086d012494085c98324c00a695f032c022960a8386bd140c28c6a00d80a180d6c04a04a18b189dc40b616c4f87f09409432c316)

def w220 : Sig := 0x5555555555555555000000000000000055555555555555550000000000000000

def s865 := certify 255 6 ([w113,w220,w8,w54,i7,i2,i3]) cs255 [] (u255 6 75 0x810181cd01089042b461f1181a03a0c1b3720d90174045bc61fd18c9802145810d31a7f9b16d0c6835ab427ff360421c12c29a1140409b9e0409797040824c47844890124fc588604)

def s866 := certify 255 7 ([w220,i0,w8,w54,i7,i1,i2,i3]) cs255 [s865] (u255 6 100 0x4080c0e6808448215a30f88c0d01d060d9b906c80ba022de30fe8c0152b000112300002076002448a0217230648c64c010a2c0826e781025e5c10200d410209311e1122404531621810698d3fd38b6863418a6802be02d5a13ffa80210e09628)

def s867 := certify 255 5 ([w219,w33,w8,i6,i2,i3]) cs255 [] (u255 5 57 0xc518a21e4e8fd1fadd7e8206281820f430cb9d818d145f375183387318c49e93e810e387e4ebf24374cba4914531a92453569a49702452924092)

def s868 := certify 255 6 ([w113,w33,w8,i6,w54,i2,i3]) cs255 [s867] (u255 6 81 0x340422410d31a7fa70a12c2d4b20406070680e836405d01062da6834a94595c86cdc830214581500421c10cb569b7e0454c11116058c160152b000112300244816a00534af80002ec48800811b00)

def s869 := certify 255 6 ([w34,w33,w8,i6,w54,i1,i3]) cs255 [] (u255 4 81 0xd44224434c6987f09e286c2d6c78c1798705e00aa15c129504029a57c001762440005e1b40008a11c025584144421c4c0b60bc4f82f1505405eb3f00bcc1041d9854150c5b74609612ec40c8405e6)

def s870 := certify 255 6 ([w35,w33,w8,i6,w54,i1,i2]) cs255 [] (u255 4 81 0x651075118b6e8c12c25d95ca2d07a61c1e982083b3002284704a54100a695f0005d8910001e86d0002a85700956105110871302d83d13e0f45415018d918d854150698d30fe23c50d85ad88407ae)

def s871 := certify 255 7 ([w33,i0,w8,i6,w54,i1,i2,i3]) cs255 [s857,s861,s868,s869,s870] (u255 4 106 0x6a211221a634c3f84f143616b60420870e304107660ca20ea2316dd182584bb2b930670e6600550ae0004508e094a82014d2be000bb122000810da012ac20a2210e2605b0b627c3f88f718b708f3131308f00d700a82a08f0fe28c3f86bb103b105415018db16)

def s872 := certify 255 7 ([w117,i0,w8,i6,w54,i1,i2,i3]) cs255 [] (u255 6 100 0x680844821a634ff4e142585a960d01d06c80ba020c5b4d069528b2b90152b0001123002448a0200534af80002ec48800428b02a0084382181373c0812f2e081003608912022810cea808106c89d08810181d983720c20406c00cad5a13ff9808f)

def s873 := certify 255 5 ([w34,w219,w8,i6,i7,i3]) cs255 [] (u255 5 54 0x2081838628c510e13d7496385258d0d85b0b790873121ba65d2484086d49229ab4d24b812294920490c107a1860ce1cc61927b031a288b1bcb)

def s874 := certify 255 5 ([w35,w219,w8,i6,i7,i2]) cs255 [] (u255 5 54 0xc19c398c32e760634517cf2c6083d0c3f42d85bc9e698914531a92420436a4914d5a6925c0914a49024a0818a127a4f79a13cd1fc9d7e)

def s875 := certify 255 6 ([w219,i0,w8,i6,i7,i2,i3]) cs255 [s858,s867,s873,s874] (u255 5 78 0x1040c1c3146288709e68fe793f0c107a1860ce1cc61973b031a28be7963842d85bc8439941c4c68a061ae350c0a36127a4fa04386bf93afd24812490dd32e924514c6a490810da92453569a49702452)

def s876 := certify 255 6 ([w34,w113,w8,i6,w54,i7,i3]) cs255 [s873] (u255 6 75 0x810181cd010890434c69fe9c284b0b52cc9802145815ab427ff500421c10c0152b0000207600244816a00534af80002ec488008117000d01d060d9b9060454c11110c5b4d069528b2b9)

def s877 := certify 255 6 ([w35,w113,w8,i6,w54,i7,i2]) cs255 [s874] (u255 6 75 0x1b3720d901740418b69a0d2a5165721a03a0cc9802145815ab427ff500421c10c011230000207600244816a00534af80002ec48800811e004080c0e0454c11111a634ff4e142585a96)

def s878 := certify 255 7 ([w113,i0,w8,i6,w54,i7,i2,i3]) cs255 [s875,s859,s865,s868,s876,s877] (u255 6 100 0x4080c0e680844821a634ff4e142585a960d01d060d9b906c80ba020c5b4d069528b17564c010a2c0ad5a13ffa80210e086361c7947360c62c336304c4c022a608888d7fcdbf0a32cd8b040152b00011230000207600244816a00534af80002ec4880)

def s879 := certify 255 7 ([w123,i0,w8,i6,w54,i7,i2,i3]) cs255 [] (u255 6 100 0x4080c0e680844821a634ff4e142585a960d01d060d9b906c80ba020c5b4d069528b17564c010a2c0ad5a13ffa80210e08604dcf0204bcb820412623c2244808a0433aa02041b2274200a9580008918000103b0012245010029a57c000176244036)

def s880 := certify 255 7 ([w34,i0,w8,i6,w54,i7,i1,i3]) cs255 [s855,s862,s869,s876] (u255 6 100 0x4080c0e680844821a634ff4e142585a960152b00002076002448a0200534af80002ec4880011230064c010a2c0ad5a13ffa80210e0862e3c661d72e004c402e3035d7022808a2efc28d72e59fa97040d01d060d9b90604501140c5b4d069528b2b9)

def s881 := certify 255 7 ([w61,i0,w8,i6,w54,i7,i1,i3]) cs255 [] (u255 6 100 0x4080c0e680844821a634ff4e142585a960152b00002076002448a0200534af80002ec488064c010a2c0ad5a13ffa80210e08604dcf020400d820412623c2244808a0433aa02041b227420680e83440118006cdc831eb049a41062da6834a945896ae)

def s882 := certify 255 7 ([w35,i0,w8,i6,w54,i7,i1,i2]) cs255 [s863,s870,s877] (u255 6 100 0xd9b906c80ba020c5b4d069528b2b90d01d060112300002076002448a0200534af80002ec48800152b0064c010a2c0ad5a13ffa80210e0863c45a61de3c0035c03c5a228de022808a3c93fa9e3c2c8c4b044080c0e04501141a634ff4e142585a96)

def s883 := certify 255 7 ([w118,i0,w8,i6,w54,i7,i1,i2]) cs255 [] (u255 6 100 0xd9b906c80ba020c5b4d069528b2b90112300002076002448a0200534af80002ec488064c010a2c0ad5a13ffa80210e08604bcb820400d820412623c2244808a0433aa02041b22742400ce835401580204060710104a7c10d31a7fa70a12c2d4b3c)

def s884 := certify 255 7 ([w80,i1,i6,w54,i7,i0,i2,i3]) cs255 [s825] (u255 4 106 0x10821c381a8844886f8df3a6234c1041d98c19c399832883a889592b27223481bc1e90817c1790824c4790128251509d93b11a4e48018e42962342d89f11a8a4421c400aa15c0008a11c0022a1ac1295042e45c88d058508b5b04b09761963648274960638b285613181fc46891)

def s885 := certify 255 7 ([w189,i1,w8,i6,w54,i0,i2,i3]) cs255 [] (u255 6 100 0x680844821a634ff4e142585a960d01d06c80ba020c5b4d069528b17509b9e040979704489011408675404083644e840801b040428b02a00843821802a56000224600489140400a695f00005d89100810181d983720c24c208f08cad5a13ff986c)

def s886 := certify 255 5 ([w44,w46,i6,w54,i7,i1]) cs255 [] (u255 4 57 0xee1b41295042a5030d00203724101dc4fa102fc67a081dc4790128251506aa066a05d804881c1dc108775086089881a681b2413a4)

def s887 := certify 255 6 ([w46,w8,i6,w54,i7,i1,i3]) cs255 [s886] (u255 6 75 0x810181cd010890434c69fe9da870e69e02a56000040ec00489140400a695f00005d891000023608c84b82154015ab427ff500421c10c09b9e040824c4784489011408675404083644e84)

def s888 := certify 255 6 ([w44,w47,i6,w54,i7,i0,i1]) cs255 [s886] (u255 3 81 0x770da004c098152153030e01319d504006e881dc47a02504a40546ac0cd844c61ad008c07713f102fc67c2630ee1cd318e31c698c858c01b8176024406ca09d4e0ee0843bd10c12c81a7012c25b263)

def s889 := certify 255 7 ([w47,w8,i6,w54,i7,i0,i1,i3]) cs255 [s887,s888] (u255 2 100 0x420840c80f06a844a1a634c3f84f14603c07b4f01542b8020436802604c0aa0534af802ec48818ea881bc1ec801bc824c47c04a095015867414c83644ec9835c06625d00b0a282d85b13e1fc28a10e806e0820ef60ce1cf01b5962da06f04b)

def s890 := certify 255 7 ([w43,w8,i6,w54,i7,i0,i1,i3]) cs255 [] (u255 6 100 0x4080c0e680844821a634ff4e4c72980ca0152b00002076002448a0200534af800128f0009b9e040801b040824c478448901140867540409293046429d122940ad5a13ffa80210e08e06750031e00780260898206e59831a0418106345b4312d)

def s891 := certify 255 6 ([w85,w124,w8,w54,i0,i1,i3]) cs255 [] (u255 6 84 0x680844821d6b1e7ac1a634ff724080c1a0152b002448a024deb164ac0172e000172e0009b9e040801b0448901146eeb13bac09a340409a34040428b02f00bc02183163c30c18d7ef00bc025825d61fd)

def s892 := certify 255 6 ([w77,w124,w8,w54,i7,i0,i1]) cs255 [] (u255 6 78 0x81d800912280937ac592b005cb800054b8002006c10209311e112240451bbac4eeb0268d01026ed0119300428b02b5684fbaf00bc021831612d4080c1a680bc02586961fd0c19d4e)

def s893 := certify 255 7 ([w124,i2,w8,w54,i7,i0,i1,i3]) cs255 [s891,s892] (u255 6 103 0x810181cd01089043ad63cf5834c69fe9c02a56000040ec0048914049bd62c95802e5c0002e5c001373c081003608104988f089120228ddd62775813468081346808c9802145811a1c28cd1a31a8c7805e012c34b0fe86b5684ffef00bc021831612d)

def s894 := certify 255 7 ([w132,i2,w8,w54,i7,i0,i1,i3]) cs255 [] (u255 6 100 0x4080c0e680844821d6b1e7ac0152b00002076002448a024deb164ac011230009b9e040801b040824c478448901146eeb13bac097970464c010a2c083407418366e41b202e808e1c584b4698d3fd38a6802be00ce845012d5a13ffa80210e0861a)

def s895 := certify 255 6 ([w77,w85,w8,i6,w54,i0,i1]) cs255 [] (u255 6 81 0x12245010029a57c000176244000b970000a97000400d82244808a0433aa02041b2274204d1a0204dda020214581500421c10cb5684fbaf00bc022cc04b12d680bc021a634ff722c38b34f0c19d0e)

def s896 := certify 255 7 ([w85,i2,w8,i6,w54,i0,i1,i3]) cs255 [s891,s895] (u255 6 106 0x1a0211208698d3fd38509616a590203038054ac009122808014d2be0000bb1220005cb80005cb80026e78102006c112240450219d501020d913a10268d010268d01010a2c0a80210e0865ab427ff721c28c77805e0172fdabf16e459e186f00bc022c25cb12d)

def s897 := certify 255 7 ([w87,i2,w8,i6,w54,i0,i1,i3]) cs255 [] (u255 6 100 0x680844821a634ff4e142585a960152b002448a0200534af80002ec4880011230009b9e040801b04489011408675404083644e8409797040428b02a0084382181a03a0d901740418b69a0d2a51625a810181c20406c0024c208f08cad5a13ff84bf2)

def s898 := certify 255 7 ([w77,i2,w8,i6,w54,i7,i0,i1]) cs255 [s892,s895] (u255 6 100 0x2076002448a0200534af80002ec48800172e000152e000801b040824c4784489011408675404083644e8409a340409bb40464c010a2c0ad5a13ffa80210e0863a6d228dd7805e013a943a9d166025896864080c0e680bc021a634ff4e2c38b34f)

def w221 : Sig := 0xf0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0ff00000000

def s899 := certify 255 6 ([w221,i2,i6,w54,i7,i0,i1]) cs255 [] (u255 4 81 0x3b86d04a5410a940c3400228470005d89101000dc840ee23c8094128a83550335040be0bc841b227490407713e840bf19e8307781a1dc32883a88c81d2809612eceb0770421dd42b09881a68)

def s900 := certify 255 7 ([w88,i2,w8,i6,w54,i7,i0,i1]) cs255 [s899] (u255 6 100 0x2076002448a0200534af80002ec488001123000801b040824c4784489011408675404083644e84097970464c010a2c0ad5a13ffa80210e08606cdc836405d01062da6834a945896d4015806e08f022040607340422410d31a7fa76a2c38b3a)

def w222 : Sig := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000

def s901 := certify 255 7 ([w222,w8,i6,w54,i7,i0,i1,i2]) cs255 [] (u255 6 100 0xd9b906c80ba020c5b4d069528b34f0d01d060112300002076002448a0200534af80002ec488000cad948009797040801b040824c4784489011408675404083644e84089e4da8464c010a2c0ad5a13ffa80210e08620406070e0469c10d31a7fa70a1)

def s902 := certify 255 7 ([w44,w8,i6,w54,i7,i0,i1,i2]) cs255 [s888] (u255 6 100 0xd9b906c80ba020c5b4d064c698c50ea0112300002076002448a0200534af80010b4f0009797040801b040824c4784489011408675404090ad30465d810831420ad5a13ffa80210e08406741a01e0078026089820e308100e0430414efc34c6996)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s903 := certify 255 8 ([w8,i6,w54,i7,i0,i1,i2,i3]) cs255 [s837,s850,s852,s853,s767,s854,s856,s860,s864,s866,s871,s872,s878,s879,s880,s881,s882,s883,s817,s884,s828,s835,s781,s811,s826,s885,s889,s890,s893,s894,s896,s897,s898,s900,s901,s902] (u255 4 309 0x61c0844f84f043809f813ee70f77035109510f712a2244e107f09e34c59b86987f707f16613c279e795e286ceb1e770b5b4adb4ab319c3fc20ca91fe0edc634a731b039433ca51ca1cf063079d06511841e4c1d45a14a33183fe8b6c2fd683f98d67b612c969825d8d625af64968bd001c4842a8bd24215dc000cb000c174228cb0ba11cc003d700303b440bd51da1b700051e9c8409501413d113730003f87d29adc43e95f0fe0036f002de176db7c246c002df211c42437ab12120f5c422af210c1a42faad0d20bcc422ab210031c0aa4638370108a4484c0ef126a3c7788fc10820520968404a220a80a68a04840fe0a4cea470520a43f90887c84b0271b28241389db108794c583326235c18d84226e145560a3626e2109f0fe16f02cc2d89f16627f01fc3f85114614441fc41443f887106b112f25ec)

def s904 := certify 255 7 ([w9,i6,w12,w54,i0,i1,i2,i3]) cs255 [] (u255 6 109 0x3404224176ec25d80ab1578270680e836405d010a714ec04b8621a68300a9580008918012245010022a780002eff0004dcf0204bcb820400d82244808a0423e98204392a0248a00b0021ce39ff301c610200dc83663c00f004c11304a008c022c58c301832d5a)

def s905 := certify 255 6 ([w43,w197,i6,w12,i0,i1,i3]) cs255 [] (u255 5 84 0x9a88577e21458b8765c002a8570117885496214a1b85adc1037f820806c223910a86c4297f70a0b8e0850fee05a0890924940a490252288258852cee14f7020ce3043741046780780984984092214610a638435c)

def s906 := certify 255 6 ([w44,w197,i6,w12,i0,i1,i2]) cs255 [] (u255 4 84 0x26b02a3016281d28004508e01e3020b015281868205f05e42001b9094c07ec06aa066a1100fe810650ea294a8204a094541403bc05fa067a040846088c0ecc107c0f001390139024c019c1881568)

def s907 := certify 255 7 ([w197,w8,i6,w12,i0,i1,i2,i3]) cs255 [s905,s906] (u255 5 105 0xec9b59c2ac5586109e28ce39a48c107a19a18668621ad0c1ac6197e801542b80004508e000f3c0005dc3e8003cf00206ff04102fdc20806c20934c20872681049a61024e41843f98168224208328750924940a49025026180820a216c2098602)

def s908 := certify 255 7 ([w43,i6,w12,w54,i7,i0,i1,i3]) cs255 [s905] (u255 6 103 0x810181cd010890498e5301942c4e1d93802a56000040ec0048914040251e0050ce16b381373c081003608104988f08912022812526085fce14139a853a2396ac1c3859ca79c392bf1c0cea0063c00f004c113040dcb3063408302352834a1870869c)

def s909 := certify 255 7 ([w44,i6,w12,w54,i7,i0,i1,i2]) cs255 [s906] (u255 4 103 0x18338733065107512634c628742c503a50008a11c001021b4129504085be00a940c34102f82f21000dc8412623c8094128a8485609c8355033501ac3b883405b0b2840bf19e843dd0fe8303b3041f03c004e404e476010821708608ad6696285881568)

def s910 := certify 255 8 ([w8,i6,w12,w54,i7,i0,i1,i2,i3]) cs255 [s904,s907,s908,s909] (u255 6 125 0x2040607340422410e696dac70ab1578271311c38d08680e8306cdc836405d011a0c18d0621a6830d70c189680a9580008918000103b001224501003c780002eff00003c78004dcf0204bcb820400d820412623c2244808a044c98204392a02044c9820a313fa8150a00b816b56ac60a00b00225f83f0c)

def s911 := certify 255 7 ([w8,i6,w54,i7,i0,i1,i2,i3]) cs255 [] (u255 6 103 0x810181cd010890434c69fe9c284b0b52c1a03a0c1b3720d901740418b69a0d2a51625a02a560002246000040ec00489140400a695f00005d891001373c0812f2e081003608104988f08912022810cea808106c89d08c9802145815ab427ff500421c10c)

def s912 := certify 255 7 ([w82,i6,w12,w54,i0,i1,i2,i3]) cs255 [] (u255 6 109 0x340422410a12c2d4b0ab157827204060688680e836405d014a9458d0621a68306cc68300a958000891801224501001762440002eff0000103f0004dcf0204bcb820400d82244808a041b2274204392a0204126a020aa00b0028625b0161832c60a008c026058c16)

def s913 := certify 255 7 ([w197,w96,i6,w12,i0,i1,i2,i3]) cs255 [] (u255 6 105 0x10207be40ab1578270680e8308510a38640621a68300a9580008918011d23a52e4002eff0004dcf0204bcb820400d8212524b20a584392a0217bc12070d11c344d06341be00f801404501190ca00a80204d044820593a022448a0248901140428b020542d02)

def s914 := certify 255 8 ([w96,i6,w12,w54,i7,i0,i1,i2,i3]) cs255 [s911,s912,s913] (u255 6 125 0x2040607340422410a12c2d4b0ab1578270680e8306cdc836405d014a9458d0621a68300a9580008918000103b001224501001762440002eff0004dcf0204bcb820400d820412623c2244808a041b2274204392a020d7602ad5ab182802c00a18e02c38688e1a26831a0df007c00a02280828e802a00b50c)

def w223 : Sig := 0xffffffffffffffff0000000000000000ffffffffffff000000000000ffff0000

def s915 := certify 255 7 ([w223,w54,i6,i7,i0,i1,i2,i3]) cs255 [] (u255 6 106 0x1020303840811630418a27e285a96142583407418366e418e1c58311227c28b2079528054ac000448c000081d8005c8c19231c3854284880002ec26e781025e5c102006c10209311e1316218b295214a84e840836640c1ce27c60c150851630c0b161908602)

def w224 : Sig := 0xaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaaffffffffaaaaaaaa

def s916 := certify 255 6 ([w113,w224,i6,w54,i7,i2,i3]) cs255 [] (u255 4 81 0x21043870351089121022d860820ecc60ce1ccc19441d45ce02d604960e713ec6084c8ac2845ad82584bb6ac0c716115311116217602d2104e8001542b8001142380024c8182521275602d602d)

def s917 := certify 255 6 ([w34,w224,i6,w54,i7,i1,i3]) cs255 [] (u255 4 81 0x8410e1c0d4422448408b6002a8570004086d04a5410b960c960022847004960e713ec6084c88179e330e0bc5d80488017b35c02f1505461df614121017e84eaa74622744e893206274541539c608b)

def s918 := certify 255 7 ([w224,i0,i6,w54,i7,i1,i2,i3]) cs255 [s916,s917] (u255 4 106 0x420870e06a2112242045b0c1041d98c19c399832883a8b9c05ac00550ae0004508e000810da094a82172c192c092c1ce27d8c1099109d54e8c44e89d5fe28c4e89d006b009d12640c4e8a82a3016b01692c2845ad82584bb685d804882c0c71615054602d602d)

def s919 := certify 255 5 ([w219,w33,w11,i6,i2,i3]) cs255 [] (u255 5 57 0x8204599040c503041e8671cb0c1833873183186332c1fa3f5bafd145f37510ff0e14ebf7090914921ba65d248a298d4922caa852924092)

def s920 := certify 255 6 ([w113,w33,w11,i6,w54,i2,i3]) cs255 [s919] (u255 4 78 0x6a2112242045b010821c38c1041d9832883a8b9c05ac30670e666084c890bb180b6c2845ad82584bb6941fec0c716176012201153111100550ae0004508e094841ad80b580b48406e0)

def s921 := certify 255 6 ([w34,w33,w11,i6,w54,i1,i3]) cs255 [] (u255 4 78 0x1a88448908116c3c60bcc382f00550ae094a82172c192c002f0da0004508e06084c88efb18506c2845ad85d80488141fd6782fc02f09612eda150543041076615054e71822c8405e6)

def s922 := certify 255 6 ([w35,w33,w11,i6,w54,i1,i2]) cs255 [] (u255 4 78 0xca20ea2e7016b11683d30e0f4c1041d980114238252a085cb064b000f4368001542b8182132205ac60cd09612eda17601220507fb0314636b0a116b6150541505442180b48407ae)

def s923 := certify 255 7 ([w33,i0,w11,i6,w54,i1,i2,i3]) cs255 [s920,s921,s922] (u255 4 103 0xd4422448408b602104387182083b3065107517380b5860ce1ccc00aa15c0008a11c1295042e58325801021b40c1099102d63016d8508b5b04b0976d0bb00910283fd897903b5818e2c23dc35dc23cc28cc23c01ac02a0a8c05ac05a415054)

def s924 := certify 255 5 ([w34,w219,w11,i6,i7,i3]) cs255 [] (u255 5 57 0x41030710408b30bd97bc8c2c6ba6149632c686d82c621f84848a514458e8486e9974921021b5248b2aa14a4902486083d0c30670e630630c6608b)

def s925 := certify 255 5 ([w35,w219,w11,i6,i7,i2]) cs255 [] (u255 5 57 0x30670e6338e5860c107a18bd97bc8c8a2f9a1fa3f58f9e6f090914be3469d7e48a298d4921021b5248b2aa14a49024a0818a03186332c)

def s926 := certify 255 6 ([w219,i0,w11,i6,i7,i2,i3]) cs255 [s919,s924,s925] (u255 5 81 0x41030710408b306083d0c30670e6338e58617b2f7919f1a3793f4517cd7c3858f843fd4275fb84848a541c35e8a06146350c06b603186332c924092486e99749228a6352484086d4922caa852)

def s927 := certify 255 6 ([w34,w113,w11,i6,w54,i7,i3]) cs255 [s924] (u255 4 75 0x21043870351089121022d80cd839c4fb1821322b0a116b6b031c5941fc5d8048802584bb6801542b800204368252106b61df61412101780c1041d98c19c3998454c44479c608b)

def s928 := certify 255 6 ([w35,w113,w11,i6,w54,i7,i2]) cs255 [s925] (u255 5 75 0x30670e63065083a84e396183041e86c8c1ce27cc302132104b096b34b60c2c507f17600910161422d5600228470001021b40492083599618334413c0208183822a6111120832c)

def s929 := certify 255 7 ([w113,i0,w11,i6,w54,i7,i2,i3]) cs255 [s926,s920,s927,s928,s916] (u255 5 100 0x4103076810890882045983041e8618338731832841d4271cb0cc8c1ce27cc30213212c2845aac12c25acd2d830b141fd6d8c5ac2ec012206c71313b6186b8db3028d808a984444c42e6582001542b80004508e0002043680924106b32c32c)

def s930 := certify 255 7 ([w34,i0,w11,i6,w54,i7,i1,i3]) cs255 [s921,s927,s917] (u255 5 100 0x82060ed02112110408b3000aa15c0004086d012494085c98324c0022847032307389f30c084c84b0a116ab0bb004880b60c2c507f59f70d7b82584b59ab8f1987bae0051817301aee09409430ef9850441820f430c19c398c128128e38608b)

def s931 := certify 255 7 ([w35,i0,w11,i6,w54,i7,i1,i2]) cs255 [s922,s928] (u255 5 100 0x60ce1cc60ca107509c72c306083d0c004508e0002043680924a042e4c1926001542b8191839c4f98604264209612d6685d8024405b0616283fade2315961422d56f116987f3c005181e2d10d7e04a04a19618334482060e09409420832c)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s932 := certify 255 8 ([w11,i6,w54,i7,i0,i1,i2,i3]) cs255 [s911,s915,s918,s768,s923,s929,s930,s931,s812] (u255 4 309 0x18702113e13c10e027e04fb9c3ddc0d4425443dc4a889138422c27a18e408b708b604f6379319c3fc20ad51fe0edc6312f31b039433ad51ca1cf063079d06511841e4c1d45a102d3719ae02dd02d61982f40071210aa2f490857700032c00305d08a32c2e84730004bc00c0ed10294c7686dc001448f210254050494c423402e581f582343e8c96018de48471090de87c8483d7108b548430690be8243482f310894c8400c701e518e0dc04212f21303bc4998b1de23f0420814825a10128882a029a30818c168290c6c052c05a405a4bc9883313ec660978e713e4bc4fe18c0a2c608218828843132260827dace3ce284279e716aeb58c4b425eac12cd6b6896ebd6176025e0f2531220b0013d86c909790138d713a4b1316b09f22e0c7045f027ed625e28d44bc3587f)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s933 := certify 255 9 ([w54,w12,i7,i0,i1,i2,i3,i6]) cs255 [s769,s782,s783,s813,s816,s818,s822,s827,s829,s836,s838,s845,s849,s851,s903,s910,s914,s932] (u255 4 412 0x12685963126e05985b49a1645985949b863097adf63158d830d957aad0c21fc97d98c5561458c552208625221442189951e2608d088b09e8342c720d088b708b342c09ec3438702134216427821343809f8342165ce34279dc284d0d868d8d09e71a22d4d0d9d63423ddc0d4d0884a88d08f712a224d089c225a0b4dc25acd709682dd02d25ac330d09a1318d0b87f8413424b47f83b342e3189692d31896e07286725a4b47287325b831896db412c9692d304b25b63589692dd6896879d06525a230896879307525a2d094088d00b9232c0fac48e2343e8c9232c030d08bd000d0b8908553422f490857342e000968cb00096982e84525a32c2e84725a600126a4d00126e07688149a87c7686d49b800097a090008cdbc2ed299e5f0912336000c5d098c88c88121af40508c885188ccb0818ccc82d05218cccb014b0cc82d202d34268484342e2121bcd09992120f4d0b88425a4b48425a60d217c969990d20bc96988433266484332018e0332664638373320210cc999210cce0778933326647788f3338210cc999210ccd8138d93326641389d3336210cc8814825333420253322208ccd014d08b91722e0c526a730d69cc9ba7326ea)

def w225 : Sig := 0xffffffffffffffffffff0000ffff0000ffffffffffff0000ffff0000ffff0000

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s934 := certify 255 8 ([w225,i6,w12,i7,i0,i1,i2,i3]) cs255 [] (u255 4 327 0x61c0842c84f043809f80b2e7183708350d151831a24fd4e508b09e8639022dc22d813d83ddc0d4425443dc4a88913844f4c670ff082b547f83b718c4bcc6c0e50ceb5472873c18c0ff408d460460fcc0fd5a502d3719ae02dd02d61981e4c19441ec41e43d87511842f40071210aa2f490857700032c00305d08a32c2e8473000a5400c0ed102a547686dc0000ac00e55e0720afc0ad40508d00b9607d608d0fa32580653d2102540505e121d211c42437a1d2120f5c4221d210c1a42fa1d0d20bcc42295210031c087463837010887484c0ef1268747788fc108a205305609c29a813a8159015b0818c168290c6c052c05a405a204e0968404a220a809e92c4978490b2c66219e02cc330b38630deb18a31ea37a63c43a98a0a2c6082188288431322608dc88584e7837245c5be04209a212939a826917b2842)

def s935 := certify 255 8 ([w225,i4,i6,w12,i7,i0,i1,i2,i3]) cs255 [] (u255 6 138 0x10203038418a27e2840811630709512a38709512a383407418366e4191227c28e1c583037af41837af418054ac000448c000081d801c3854285c8c19230f000078f00007826e781025e5c102006c10209311e1295214ab16218b13040899304089a40c316060c1421c50c850861b9306e4c4c1530542190860237260dc98982a60a)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s936 := certify 255 9 ([w92,i6,w12,i7,i0,i1,i2,i3,i4]) cs255 [s934,s935] (u255 4 402 0xdc885860b8372c145be04209a212897a82692fb2842086213028b021851132c108de8844dcde9371466f4359371087bb81a884a887b895112270b0e04216427821c04fc059738c1b841a868a8c18d127ea7284584f431c8116e116c09ec6f6e71791a2345bd8d11a25e5ce0f260ca20f620f21ec3a88c26f663387f8416123fc1db8c661263607286761239439e0c607fa046a302307e607ead28169b8cd7016e816b0cc612631815debbd84aef5de604c6a7a4204a80a0bc217a00389085517a4842bb80019600182e84519617423980060a00607688152a3b436e0000560072af039057e056a02846805cb03eb04687d192c030de8006bcf69ed52a7b4f69af000409c12d080944415013d1bd908e2121bd0e90907ae2118490860d217d0e86905e62114a908018e043a31c1b808460a42607789343a3bc47e0845102982b04e14d409d40ac80ad840c60b4148636029602d202d37a4219160ec1d0eb0760e644845dabb4248596330c17016582859c3186f58c51bd51bd25e21c2caeb0b382d380b25a42ce176e0deaeb0e26f4b0861)

def s937 := certify 255 7 ([w43,w9,i6,w12,i0,i1,i3,i4]) cs255 [] (u255 5 112 0xa2c428a710a106131e1681089089a88577e214558ab0c213d24940800aa15c045e2152588500bb87d0249025040dfe08201b088e442a1b10a21c9a049662144388560257611cc4103c03c04c24c245130215c702d85b18338c1cc608c4843741046780780984984092214610a3344346)

def s938 := certify 255 7 ([w44,w9,i6,w12,i0,i1,i2,i4]) cs255 [] (u255 4 112 0x93c03bc04184c78832883a889ac0a8c0c4374694a82004508e01e3020b001770fa004a09454205f05e42001b9094c07ec08724149204c043c302576230733067f03c004e404e41070c41080b616c10821761c21822303b3041f03c004e404e4093015f009e184558ab)

def s939 := certify 255 8 ([w9,w8,i6,w12,i0,i1,i2,i3,i4]) cs255 [s937,s938,s852] (u255 6 133 0x2e035c102c063c102a1401340422410e15e55c70ab1578270a31c3985e405d010680e831a0c18d0621a6836a0c194b922450100a95800089180003c780002eff00003c780244808a04dcf0204bcb820400d82044c98204392a02044c98248e1804392f30095d821c610200dc83663c00f004c11304e061960b16ad169)

def s940 := certify 255 7 ([w34,w218,i6,w12,i7,i1,i3,i4]) cs255 [s855] (u255 5 100 0x2605b841141ac208c31e128104a6810890a08183841944fca15a61f130f1dc61ee492502002a8570001021b4047a5257285c98324c02e78000228470024a55a8c0b6164c30a10e51df094094993c9b59a612623e62a6293d98724c5b62097181)

def w226 : Sig := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0a0a0a0a

def s941 := certify 255 7 ([w226,i0,i6,w12,i7,i1,i3,i4]) cs255 [] (u255 5 109 0x2605b8471e2097116770a7b9a04224282060e1c711f58858b8765c492502002a8570001021b4036f11e188a1b85adc10ae05b0b2e3910878910a210940bf0d51685f0be06c005f12623c2f9f388a88bfb863812810651ba08233c03c00c1cc338c544544638638209305f)

def w227 : Sig := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00aa00aa

def s942 := certify 255 7 ([w227,i0,i6,w12,i7,i1,i2,i4]) cs255 [] (u255 4 109 0xb02dc4250a110bf40cf406510751183387330e31c668d42c503a5129504008a11c001021b4046c8d90f50a940c3441016c2ca1029443a0aa95515037c353c61bc37801b803789311e1bcae95d510f1aa8620541035303b3041f03c076010821502b5083621882101386f)

def s943 := certify 255 8 ([w218,i0,i6,w12,i7,i1,i2,i3,i4]) cs255 [s940,s941,s942,s856] (u255 5 129 0x2605b841144c4208c31e128104a6810890a08183841944fca15a61f1306b9c71790ca1075086083d0c30670e631712932945bcc3fa60a3186302924a0400550ae000114238000810da023d292b942e4c192600f3c00494ab51816c2c9861421cab025025264f26d669860d734c06c04c24c47cc54c527b30e4989dc4)

def w228 : Sig := 0x505050505050505050505050505050505050505050505050505050500000000

def s944 := certify 255 6 ([w33,w228,i6,w12,i1,i3,i4]) cs255 [] (u255 5 84 0xe3c412e22cee14f72490253408448438e23eb10b170ecb81bc4f04492502002a85700dbc47862286e16b700103688e4421e20c618cc70608c4843741046780780aa21a2116e10d70612610298532a2)

def s945 := certify 255 6 ([w113,w228,i6,w12,i7,i3,i4]) cs255 [] (u255 5 81 0x2605b8471e2097116770a7b9a04224282060e1c711f58858b8765c10ae05b0b2e39108788608c4843741046183986718fdc434422dc21ae3c24c249204f081bfc1041021b440a614ca883186331c)

def s946 := certify 255 7 ([w228,i0,i6,w12,i7,i1,i3,i4]) cs255 [s944,s945] (u255 5 106 0x4c0b708e3c412e22cee14f734084485040c1c38e23eb10b170ecb8924a0400550ae00020436806de23c3114370b5b8215c0b6165c72210f149204a081bfc1040051882301ac40a614ca883186331c18231210dd04119e01e0060e619c6aa21a2116e10d726)

def w229 : Sig := 0x55005500550055005500550055005500550055005500550055005500000000

def s947 := certify 255 6 ([w33,w229,i6,w12,i1,i2,i4]) cs255 [] (u255 3 84 0x5428485fc0cf804a09480a86520ea438c719a3a16303a602fa02f402604c0a9004508e046c8d90fa153030e01036a40a510f018c31e4710c126076c1040f801f005742be816c0ab8e404e814c29d10f)

def s948 := certify 255 6 ([w113,w229,i6,w12,i7,i2,i4]) cs255 [] (u255 3 81 0x40645b9150a1217f033e0329075260ce1cd8718e334742c6074c01180b616620528878e21824c0ed820f019042084fdd0afa05b02ae00fa027404a09480fa05f05e8820436a0530a7468c31863c8)

def s949 := certify 255 7 ([w229,i0,i6,w12,i7,i1,i2,i4]) cs255 [s947,s948] (u255 4 106 0x5816e212850885fa067a032883a88c19c3998718e3346a16281d2894a82004508e000810da023646c87a854a061a2080b61650814a21d0094128a840be0bc8400a32116886b20530a6a21e18c31b10e10c11181d9820f81e03b00841082b50af502d40ab4027)

def s950 := certify 255 7 ([w33,w114,i6,w12,i1,i2,i3,i4]) cs255 [s944,s947,s857] (u255 3 112 0xa86b91618f204a09480a8352112420e89fd0adc3e381bd01ea06520ea4c1041db171a4cb45bf0fee05f405e804c09815200aa15c0022847047b495e85ce0c9c040da99421e831863c40a24144b851f08f60d6c23c0f801f005741c6816e061c032809d029853a4)

def s951 := certify 255 7 ([w113,w114,i6,w12,i7,i2,i3,i4]) cs255 [s945,s948,s859] (u255 3 109 0x20322dc8a86b91618f206a4224810821033c20e89fd0adc3e3819483a93041076cc19c39b171a4cb45bf0fee049c0b616732843d037286e5c28f81bb06b606e0652a81906e7ee9efd02dc0c3807d013a02504a407d03783d440be0bd104086d40a614e9031863c4)

def s952 := certify 255 8 ([w114,i0,i6,w12,i7,i1,i2,i3,i4]) cs255 [s946,s949,s950,s951,s860] (u255 3 138 0x40645b91518b22c31e40d48449021042067841d13fa15b87c70329075260820ed983387362e349968b7e1fdc02604c0a900550ae0011423800810da08f692bd0b9c193812702d859cca10f409412901540de0f5102f82f440262880646ba0530a74818c31e205120a25c28f8bcb06b630207c00f80194aa0665a82ba0e340b7030e027)

def s953 := certify 255 7 ([w33,w32,w8,w12,i1,i2,i3,i4]) cs255 [s861] (u255 4 109 0x20e21ac42605115042a5042a03510891385795770ad61f160ab15618447821043805219441d4460820ecda31b45bd87f58621ba3183387334a541002a85700022847003de00b960c9600bb87d000408370283886110e21d80b58644840521855ee300a5986277)

def s954 := certify 255 7 ([w34,w32,w8,w12,i7,i1,i3,i4]) cs255 [s862] (u255 5 103 0x1302dc2083886b082302884a04129a04224282060e38579573856987c4c3c77187b924940800aa15c0004086d00079e005c98324c02e0fa000114238192552ae0b6166eb830887b8c3be65c1281283041e861833873195e8c35060c62db104b86)

def s955 := certify 255 7 ([w35,w32,w8,w12,i7,i1,i2,i4]) cs255 [s863] (u255 5 103 0x2605b8410710d610460510940825032841d42183387319a18668b7987f4c45be187f06083d0c924a04004508e000204368003cf002e4c192601e07d0000aa15c0c92a95e05b0b3e786d4daf8658678128129040c50af55ebe1a0ca0c4ee209e04f)

def s956 := certify 255 8 ([w32,i0,w8,w12,i7,i1,i2,i3,i4]) cs255 [s953,s954,s955,s864] (u255 6 132 0x4605b8205c0988204328022808114680844824080c0e1c2bcab8e15a30f88c1562af04ec80ba020d01d060d9b906341831a2de30fe8c0c434d062448a020152b000112300002076000078f0017230648c005dfe00649545022808a281c35d4280c28c32800d802831a8c2bd57af8540c50313b84b56ac60e1804388718b06191)

def s957 := certify 255 7 ([w113,w220,w8,w12,i7,i2,i3,i4]) cs255 [s865] (u255 6 100 0x4605b8205c35020432802680844824080c0e1c2bcab8e15a30f88cc80ba020d01d060d9b906341831a2de30fe8c649545600463c10ab15781b10d0c6835ab563036c021c43ac2ee11404489012609b9e0409797040824c47840899304c588604)

def s958 := certify 255 8 ([w220,i0,w8,w12,i7,i1,i2,i3,i4]) cs255 [s957,s866] (u255 6 129 0x2302dc102e028c102194013404224120406070e15e55c70ad187c466405d010680e8306cdc831a0c18d16f187f46122450100a9580008918000103b00003c7800b9183246324aa29224045026e781025e5c10200d410209311e102264c13162181300231e08558abc13886863418bb80f802d5ab18386010e21d628)

def s959 := certify 255 7 ([w113,w206,w8,i6,i7,i2,i3,i4]) cs255 [] (u255 6 103 0x8c0b7040b018f04085500454c102222d0108904810181c2ac55e09c20c513f1438579571d90174041a03a0c1b3720c18869a0c5c452651468306352195ab56300c6d8043887148d4519124481260152b0001123000024c47800093fe00149852750811300)

def s960 := certify 255 7 ([w34,w206,w8,i6,i7,i1,i3,i4]) cs255 [] (u255 5 103 0x2605b84106131e1045051094082534084485040c1c2ac5586109e20ca27e51e3b8c3dc924a0400550ae000204368001770fa023d292b9405cf00004508e0049c82d85b0b2184c0e37087b8aa8ab825025264f26d66984988f9a649ed4c54c527b104b9a)

def s961 := certify 255 8 ([w206,i0,w8,i6,i7,i1,i2,i3,i4]) cs255 [s959,s960] (u255 6 132 0x4605b820580c782042a8022808114680844824080c0e1562af04e106289f8a1c2bcab8ec80ba020d01d060d9b9060c434d062e229328a341831a2448a020152b00011230000207600005dfe0047a292b8a0078f0090cad5ab180670c021c43822808a264f26d53260c28d32601a802612623d32649ef8530a4c293d8414a85191)

def w230 : Sig := 0xffff5555ffff5555ffff5555ffff5555ffff5555ffff0000ffff5555ffff0000

def s962 := certify 255 7 ([w230,i0,w8,i6,i7,i1,i2,i3]) cs255 [] (u255 6 106 0x10203038698d3fd38418a27e29a02112083407418366e418316d3418b88a4ca2b202e808054ac000448c000081d800014d2be011e8a4ae28912280a45ab427ff0c09b9e0409797040801b04092dd9c84086755e84a548504489011404c8c02054043820428b02)

def s963 := certify 255 7 ([w33,w208,w8,i6,i1,i2,i3,i4]) cs255 [] (u255 4 106 0x106131e21282888128251501a884488558ab0c213c41a89fa837901e9032883a88c1041d98c437462e2a4caa0be405e494a8200550ae0004508e001770fa047aa4aea0101b91816c8af481c44ce442bdc55dc6d1b5e07801843888710e0af0404e40a614d44)

def s964 := certify 255 8 ([w208,i0,w8,i6,i7,i1,i2,i3,i4]) cs255 [s962,s963] (u255 6 132 0x4605b820580c782042a802680844824080c0e1562af04e106289f8ac80ba020d01d060d9b9060c434d062e229328a2448a020152b00011230000207600005dfe0047a292b8a916ad58c031224045026e781025e5c102006c102181461026057a129521413802d408578e2ae3831a0c68f003c00c3231c307010e21d526)

def s965 := certify 255 6 ([w43,w113,w33,i6,w12,i3,i4]) cs255 [] (u255 5 84 0x1c78825c459dc29ee153082223a0422421c711f58858b8765c82060e72210f1385bcb7b821622e3124904f001542b806de22e3114370b7b8209b0030462421ba08231510d118e10d7060e619c6780780)

def s966 := certify 255 6 ([w44,w113,w33,i6,w12,i2,i4]) cs255 [] (u255 4 84 0x420c50885fa067a0a988444432883a88718e334620c58a074a0c19c3999029443a102b456a210106f8e52178011423808d91b1063f454a056a08406e07086088c0ecc1054a15e20d88156876010821f03c0)

def s967 := certify 255 7 ([w113,w33,w8,i6,w12,i2,i3,i4]) cs255 [s965,s966,s868] (u255 6 105 0x2e035c102c063c102a1401153040888b40422410e15e55c70ab1578270a31c3987a0406076405d010680e831a0c18d0621a6836a0c198686cdc830ae180438cb569b606460c364aa60c191244811e0152b0001123000078f00005dfe000078f000811b00)

def s968 := certify 255 6 ([w44,w34,w33,i6,w12,i1,i4]) cs255 [] (u255 4 84 0x1083142217e819e8a085494a8223646c8788315281868002f0da0004508e040a510e840ad15a884041ae9150541c638c418fd162815a82101799c21822f03c05285788362055a1c0bc1082f303b3041)

def s969 := certify 255 7 ([w34,w33,w8,i6,w12,i1,i3,i4]) cs255 [s944,s968,s869] (u255 4 105 0x8388d71083098f1082885115042a03510891385795770ab156184278a3739879e305e61c17ca541002a857003de000bb87d003de0001786d000228470283886110ec0b60bc2c82f05f8c02f05f8c02f1505430410766d18da310dd183598cc348405e6)

def s970 := certify 255 6 ([w43,w35,w33,i6,w12,i1,i4]) cs255 [] (u255 5 84 0x38f104b88b3b853dc50209449250236f11e188a1b85adc03c0da0001542b80e4421e270b796f7042c45c620940941c711718858b85bdc104f0e18231213c03c01510d118e10d706f033f83741046)

def s971 := certify 255 7 ([w35,w33,w8,i6,w12,i1,i2,i4]) cs255 [s947,s970,s870] (u255 6 105 0x2e035c102c063c102a1401140408a6405d011a0c18d0621a6830a30c1986a2d7861de0680e8312245010089180003c780002eff00003c7800079b0000a95800ae180438cb4f2c3c786d4dabc786d4dabc04501141c2bcab8e1562af008fd438730f0811e0e)

def s972 := certify 255 7 ([w43,w33,i0,i6,w12,i1,i3,i4]) cs255 [s944,s965,s970] (u255 5 109 0x1c78825c459dc29ee28104a6810890871c47d62162e1d97208183924940800aa15c036f11e188a1b85adc004086d01c8843c4e16f2dee04a04a08f386b9c23c0146017188b8c45bdc2dee0821622e310c1189086e8208cf00f00544344638435c183588f1860e619c6)

def s973 := certify 255 7 ([w44,w33,i0,i6,w12,i1,i2,i4]) cs255 [s947,s966,s968] (u255 4 109 0x210628442fd033d1410a819441d4438c719a31062c503a5060ce1ccd29504008a11c046c8d90f1062a5030d001021b40814a21d0815a2b502a0a823cc35cc23c028c020c878831fa2b502b5048404190f7086088c0ecc107c0f014a15e20d881568706b11ee76010821)

def s974 := certify 255 8 ([w33,i0,w8,i6,w12,i1,i2,i3,i4]) cs255 [s950,s953,s963,s967,s969,s971,s972,s973,s871] (u255 4 134 0x41c523884184c7884144288a821501a884489c2bcabb8558ab0c213d0fb9d2ec10821c3832883a88c1041d9b46368c43746412634b930670e6694a8200550ae0004508e007bc001770fa007bc000810da050710c221d816c2d8590c22a0a823dc795c23cc62cc23c04c4035c3888f0e223c308a30c21ac4788f32240678c0714ab8c191)

def s975 := certify 255 6 ([w44,w34,w113,i6,w12,i7,i4]) cs255 [] (u255 4 81 0x2c0b7108418a110bf40cf441016c2ca1029443a252178020436808d91b106ba454a056a08405e01153111130670e661c638c41be3162815a87086089d80420854a15e20d881568f03c0303b3041)

def s976 := certify 255 7 ([w34,w113,w8,i6,w12,i7,i3,i4]) cs255 [s945,s975,s876] (u255 4 99 0xb02dc420e235c420c263c420a214440d44224408410e1ce15e55dc2ac5586109e28dce61e0cd2aa82d85b0b21843886110ec9485e00550ae000810da007bc001770fa007bc02101780454c4444c1041d98c19c399b46368c437460d66330d)

def s977 := certify 255 6 ([w43,w35,w113,i6,w12,i7,i4]) cs255 [] (u255 5 81 0x9816e11c78825c459dc29ee085702d85971c8843c492413c00810da01b788b8c450dc2dee0827800454c2223040c1c38e22e310b170b7b83046242183986718a88688c7086b8f00f003741046)

def s978 := certify 255 7 ([w35,w113,w8,i6,w12,i7,i2,i4]) cs255 [s948,s977,s877] (u255 4 99 0xb02dc420e235c420c263c420a2144419441d4460ce1ccda31b4621ba30a331986982083b30334aaa0b616c2c8610e218443b25217801142380020436801ef0005dc3e801ef008407a0115311110420870e70af2aee1562ac3084f0d6e730f)

def s979 := certify 255 7 ([w43,w113,i0,i6,w12,i7,i3,i4]) cs255 [s945,s965,s977] (u255 5 106 0x9816e11c78825c459dc29ee6810890a08183871c47d62162e1d97042b816c2cb8e4421e208a9844476386b9db3028d82e3117188b7b85bdc1124827800aa15c0004086d00dbc45c62286e16f70608c4843741046183986718a88688c7086b8306bd86780780)

def s980 := certify 255 7 ([w44,w113,i0,i6,w12,i7,i2,i4]) cs255 [s948,s966,s975] (u255 4 106 0x1605b88420c50885fa067a032883a88c19c3998718e334620c58a074a2080b61650814a21d022a622220dcc35cc0df028f020e5e8837c62b502b5049485e004508e000810da023646c419a3152815a87086088c0ecc105d80420854a15e20d881568706b06eef03c0)

def s981 := certify 255 8 ([w113,i0,w8,i6,w12,i7,i2,i3,i4]) cs255 [s951,s957,s959,s967,s976,s978,s979,s980,s878] (u255 6 128 0x4605b8205c123820580c7820542802680844824080c0e1c2bcab8e1562af04e43e3874c1c80ba020d01d060d9b906341831a0c434d064121834bf6495455ab563070c021c6022a60888b61c7947360c62c336304c4c367be35db0a3c0db06a6cd8c884244811e0152b000112300002076000078f00005dfe000078f00)

def s982 := certify 255 7 ([w43,w123,i0,i6,w12,i7,i3,i4]) cs255 [] (u255 5 106 0x2605b8471e2097116770a7b9a04224282060e1c711f58858b8765c10ae05b0b2e3910878a49025040dfe08209311e21f388b1c45fdc282e249281001542b8000810da01b788f0c450dc2d6e6c30462421ba08230c1cc338c544344638435c984984780780)

def s983 := certify 255 7 ([w44,w123,i0,i6,w12,i7,i2,i4]) cs255 [] (u255 4 106 0x5816e21083142217e819e80ca20ea230670e661c638cd188316281d288202d85942052887402504a2a102f82f2104988f215d2ba20c878d540cd44a54100228470004086d011b23643c418a940c340377086088c0ecc105d80420854a15e20d88156804e404e4f03c0)

def s984 := certify 255 8 ([w123,i0,w8,i6,w12,i7,i2,i3,i4]) cs255 [s982,s983,s879] (u255 6 128 0x4605b8205c06b820580c7820542802680844824080c0e1c2bcab8e1562af04e1463874c5c80ba020d01d060d9b906341831a0c434d06d41834c364c4455ab563070c021c6244808a04dcf0204bcb820412623c2044c98204392a02044c982122450100a9580008918000103b00003c780002eff00003c78036)

def w231 : Sig := 0xaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaaaaaaa

def s985 := certify 255 6 ([w231,w34,i6,w12,i7,i1,i4]) cs255 [] (u255 4 81 0xb02dc4250a110bf40cf44a541004086d011b23643d42a5030d0008a11c10405b0b2840a510e81505404e24c478271c638d443c58a1881505405e0f0017e01082f502b52e96218821017841)

def s986 := certify 255 7 ([w44,w34,i0,i6,w12,i7,i1,i4]) cs255 [s985,s968,s975] (u255 4 106 0x1605b88420c50885fa067a252a08020436808d91b21e20c54a061a001142382080b61650814a21d02a0a80bc035c00bf028c1788321e20d748ad40ad41054150c19c3998718e310643c58a056a1c21822f03c0760108215285788362055a1c0bc3582f303b3041)

def s987 := certify 255 8 ([w34,i0,w8,i6,w12,i7,i1,i3,i4]) cs255 [s946,s940,s954,s960,s969,s976,s986,s880] (u255 6 128 0x4605b8205c10f820580c7820542802680844824080c0e1c2bcab8e1562af04e4123874c72448a020152b00002076000078f00005dfe000078f00011230064a5c55ab563070c021c6022808a2e3c661d72e0079402e3062d72ee04c572ec035d72e32228d70404501140d01d060d9b906341831a0c434d06d418330d)

def s988 := certify 255 7 ([w43,w35,i0,i6,w12,i7,i1,i4]) cs255 [s970,s977] (u255 5 106 0x2605b8471e2097116770a7b8924a0400810da01b788f0c450dc2d6e001542b80215c0b6165c72210f104a04a7800a303c5a21afc2e3117188b7b85bdc1025025208183871c45c62162e16f70608c484f00f0030730ce31510d118e10d706f0daf83741046)

def s989 := certify 255 8 ([w35,i0,w8,i6,w12,i7,i1,i2,i4]) cs255 [s949,s955,s971,s978,s988,s882] (u255 6 128 0x4605b8205c0f2820580c7820542802c80ba020d9b906341831a0c434d063161834cb0d01d062448a020112300002076000078f00005dfe000078f000152b0064c2c55ab563070c021c6022808a3c45a61de3c004c403c5a235de3c36a6d5e3c99228de3c36a6d5e0404501144080c0e1c2bcab8e1562af04ed438730f)

def w232 : Sig := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0c0c0c0c

def s990 := certify 255 7 ([w232,i1,i6,w12,i7,i0,i3,i4]) cs255 [] (u255 5 109 0x2605b8471e2097116770a7b9a04224282060e1c711f58858b8765c9240941037f820824c47887ce22c7117f70a0b82045d8410ae05b0b2e39108788a294550208b0e66684508a2043684536f15511437064b8a04a043741046984984183986718a8aa88c7095b8000f045)

def w233 : Sig := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00cc00cc

def s991 := certify 255 7 ([w233,i1,i6,w12,i7,i0,i2,i4]) cs255 [] (u255 5 109 0x1302dc208418a1085f9033c80ca10750860ce1cc61c638cd188316240e92249025040bf708209311e215d2ba20ea1aa40cd2040abb0881016c2c9040a510e40dd1baa041561cccf0aa1544086d0aa46c8dd420c549032485025021ba1820cc24c21cc4101455420cc206f90000f055)

def s992 := certify 255 8 ([w210,i1,i6,w12,i7,i0,i2,i3,i4]) cs255 [s990,s991,s817] (u255 5 129 0x9816e10550d708245263c2094502d02112141030710fa9c0d437c6f9d311a28ce38bc865083a843041e861833873193ed4dfea2564ac9c88d0d630c60649025040dfe08205fb84104988f11bed49eea2764ec4693911ed84126984296c44a11a16c2c88d4835087a8c5025027995b2979e18eabcf0810daf54f5495c469771923240)

def w234 : Sig := 0xffff3333ffff3333ffff3333ffff0000

def s993 := certify 255 6 ([w234,i1,i6,w12,i0,i2,i3]) cs255 [] (u255 6 84 0x2040f7c81be37ce988d0d01d0610a21470c82564ac9c88d09b9e04097970424a49642a2764ec46939080063842f65ec43c80152b00011230070e15481722e4468004d044820593a0248901140428b0204304c822448a02)

def w235 : Sig := 0xffff3333ffff3333ffff3333ffff3333ffff3333ffff3333ffff3333ffff0000

def s994 := certify 255 7 ([w235,i1,i6,w12,i7,i0,i2,i3]) cs255 [s993] (u255 5 109 0x1040c1c43ea70350df1be74c46e81089086083d0c30670e6327da9bfd44ac9593911a19420ea1081bfc1040bf708209311e237da93dd44ec9d88d27220031c49240942962342d85911a906a10f5001542b80004508e0013459d81c715002e45c88d0124940820d6c04114b041182642)

def s995 := certify 255 7 ([w180,w80,i6,w12,i0,i2,i3,i4]) cs255 [s825] (u255 5 112 0x2a83584122931e12492816810890887d4e06a1be37ce988d0aa00570032841d421820f4327da9bfd44ac9593911a114008e049204a081bfc1040bf708df6a4f7513b2762349c8800c71120d421ea1722e446801b4267611c2f4e17a30cb1865cc24c214506da8c303088d600780e38a80)

def s996 := certify 255 8 ([w80,i1,i6,w12,i7,i0,i2,i3,i4]) cs255 [s994,s995,s884] (u255 5 138 0x4c0b7082a86b84122931e16810890a08183887d4e06a1be37ce988d0ca1075086083d0c30670e6327da9bfd44ac9593911b248128206ff04102fdc20824c4788df6a4f7513b2762349c8800c710a588d0b616446a41a843d4924a0400550ae000114238003028c0e38a801722e446804dc20d611c2f4e17a30cb1865cc24c230c4589a6514e0ea30c0c2235e)

def s997 := certify 255 7 ([w180,w181,w8,w12,i0,i2,i3,i4]) cs255 [s823] (u255 5 109 0x98986b082452a8c2094502094502d0211211c2bcab9c37c6f9d311a2ac558610db040c1c19420ea10c107a19a186689592b272234621ad0c30673aa349204a081bfc1040bf70824d3084ec9d88d27221c9a041049ec214c4c3088710e618234d780007d0c2b4d8603e88d60648c9)

def s998 := certify 255 8 ([w181,i1,w8,w12,i7,i0,i2,i3,i4]) cs255 [s997,s828] (u255 6 132 0x4605b8204c4c5182048a551820450a02680844824080c0e1c2bcab8e1be37ce988d1562af04ec80ba020d01d060d9b906341831a2564ac9c88d0c434d06489011409b9e0409797040824c478408993042764ec4693908cbdb040872540464c44514045011231ccb4722b0c75437c31a8c2d35a6c4fe08df83246480b56ac6062780438871830469af)

def s999 := certify 255 8 ([w182,i1,w8,w12,i7,i0,i2,i3,i4]) cs255 [s835] (u255 6 129 0x2302dc102627a8102452a8c13404224120406070e15e55c70df1be74c46e405d010680e8306cdc831a0c18d12b2564e446a44808a04dcf0204bcb820412623c2044c98213b2762349c840031c232622289122808054ac000448c000081d80001e3c005c8b911a0300231e08558abc02f486863418e4845012d5ab18097e010e21c67c)

def s1000 := certify 255 7 ([w43,w180,i1,i6,w12,i0,i3,i4]) cs255 [] (u255 5 109 0xe3c412e22cee14f7025140b408448438e23eb10b170ecb9040c1d248128206ff043e7116388bfb8505c10638c710412631c472210f1384ac95b8a04a042f4e17a727d893ec44adc256e0021624fb10c1189086e8208d309308544344638435c18658cb18619619c6)

def s1001 := certify 255 7 ([w44,w180,i1,i6,w12,i0,i2,i4]) cs255 [] (u255 3 109 0x8418a1217f033e080a81520ca41d48718e334620c58c0e9860ce32d812825202a817c17a15d2ba20c878d5819b0831c63a209318e9029443c40df1bf005480a90cb6196c43c4190f10637e06fc001102243c41f10c126076c10413a0274aa15e20f2055c70bd17bdc06410821)

def s1002 := certify 255 8 ([w180,i1,w8,i6,w12,i0,i2,i3,i4]) cs255 [s995,s997,s1000,s1001,s826] (u255 6 134 0x1703160816031e08150a0081142809a021120870af2ae38558abc138988e1d35d020303b202e8083407418d060c68310d34186b860d35436619619224045026e781025e5c102264c1021c950102264c1020c718e10209318e10570c021c65ab563014045010bd1c2f470cb0c32c370d9c152ecc028f06ad9b0d7806460c15962260c1af)

def w236 : Sig := 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f00000000

def w237 : Sig := 0xf0f0f0f0f0f0f0f0f0f0f0f00000000

def s1003 := certify 255 6 ([w236,w237,i6,w12,i0,i1,i4]) cs255 [] (u255 5 84 0x71e2097116770a7b8924a046de23c3114370b5b9248128201b087ce22c7117f70a0b8e4421e2e8287613c03c04c24c20838ba888702db830c774704304278078098498409310af8839b82adc)

def s1004 := certify 255 7 ([w237,w43,i6,w12,i0,i1,i3,i4]) cs255 [s1003] (u255 5 109 0x1c78825c459dc29ee6810890871c47d62162e1d97124940800aa15c036f11e188a1b85adc9240941037f820806c21f388b1c45fdc282e391087882884144238359c1cde01e0261261024c41c620c2e061718095d84731040f00f013093081c626220c2e05b706)

def w238 : Sig := 0xafafafafafafafafafafafafafafafafafafafafafafafafafafafafaaaaaaaa

def s1005 := certify 255 7 ([w238,i0,i6,w12,i7,i1,i3,i4]) cs255 [] (u255 5 106 0x1302dc238f104b88b3b853dcd0211214103070e388fac42c5c3b2e249281001542b8000810da01b788f0c450dc2d6e085702d85971c8843c4128129327936b34c06c04c24c47cc544544638638204a04a0dd04119e01e0060e619c62a22a231c31c)

def w239 : Sig := 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f0000000000

def s1006 := certify 255 7 ([w239,w43,i6,w12,i7,i0,i1,i4]) cs255 [] (u255 5 106 0x1302dc238f104b88b3b853dc492502004086d00dbc47862286e16b72490250403610412623c43e7116388bfb8505c10ae05b0b2e39108788608c484f00f0130930830730ce31510d118e10d70e08d384cac0652027910da89040c1c74455e2156e06173a)

def s1007 := certify 255 7 ([w236,w43,i6,w12,i7,i0,i1,i4]) cs255 [s1003] (u255 5 106 0x2605b8471e2097116770a7b8924a0400810da01b788f0c450dc2d6e49204a0806c20824c47887ce22c7117f70a0b8215c0b6165c72210f174143b09e01e02612613a0d6da7a107175110e4d970e086084f00f013093087310407442be209ee0ab706)

def s1008 := certify 255 7 ([w117,i0,w43,i6,w12,i1,i3,i4]) cs255 [] (u255 5 106 0x71e2097116770a7b9a0422421c711f58858b8765c492502002a85700dbc47862286e16b71c8843c430462421ba08233c03c01510d118e10d7261261060e619c69240941037f820806c21f388b1c45fdc282e3010b70a08183840801b4010a16dc0b2e08f)

def s1009 := certify 255 7 ([w118,i0,w43,i6,w12,i7,i1,i4]) cs255 [] (u255 5 106 0x2605b8471e2097116770a7b8924a0400810da01b788f0c450dc2d6e085702d85971c8843c43046242780780183986718a88688c7086b93093083741046924094100d84104988f10f9c458e22fee141708084a7c20aa00570208183871c47d62162e1d973c)

def s1010 := certify 255 7 ([w189,i1,w43,i6,w12,i0,i3,i4]) cs255 [] (u255 5 106 0x71e2097116770a7b9a0422421c711f58858b8765c9240941037f821f388b1c45fdc282e0806c239108788608c48437410469849842a21a231c21ae3c03c00c1cc338c924a0400550ae01b788f0c450dc2d6e3010b70a081838498823c410a16dc0b2e06d)

def w240 : Sig := 0xffffffffffffffffffffffffffffffff00000000ffff000000000000ffff0000

def s1011 := certify 255 6 ([w240,w12,w43,i6,i0,i1,i3]) cs255 [] (u255 5 84 0x162e1d97071c47d62d021121001542b8050dc2d6e1b788f0c4924a04206ff04100d842fee14170f9c458e292409472210f13859ca7b8374104678078098498431c21ae1510d10c10670842c412e2)

def s1012 := certify 255 7 ([w55,w12,w43,i6,i7,i0,i1,i3]) cs255 [s1011] (u255 5 103 0x4103070b170ecb838e23eb1001542b8000810da014370b5b86de23c31081bfc10403610412623c42fee14170f9c458e210ae05b0b2e391087886e8208cf00f0130930830730ce318e10d70a886882d04484924a052481281acb3b853dc0864e2104b)

def s1013 := certify 255 7 ([w19,i7,w43,i6,w12,i0,i1,i3]) cs255 [] (u255 5 106 0x1c711f58858b8765c58ab145b9da042242002a85700dbc47862286e16b700752cec04925021037f820806c21f388b1c45fdc282e08e9d9c89248128e4421e271d2ba371c2ce53dc1ba08233c03c04c24c21510d118e10d706756eb4618231210a760e3c412e2)

def s1014 := certify 255 7 ([w151,i7,w43,i6,w12,i0,i1,i3]) cs255 [] (u255 5 106 0x71c47d62162e1d97208183800aa15c036f11e188a1b85adc004086d0040dfe08201b087ce22c7117f70a0b8209311e239108789c0b6165c1ba08233c03c04c24c21510d118e10d7060e619c610a168224249250292409438f104b88b3b853dc08631210b7)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s1015 := certify 255 8 ([w43,i6,w12,i7,i0,i1,i3,i4]) cs255 [s1004,s1005,s946,s1006,s1007,s972,s1008,s979,s982,s988,s1009,s1000,s1010,s908,s1012,s1013,s1014] (u255 5 327 0x372104c2b160dcaaf16ec0411ad08e3c4ab6235aaac25c41443d422cee051707a85129ee04e0f73b4084a843dc4a88908e0983a00b213e06027b0164e3a1e9c38e21a3143d1a27d623a266613c58b8738ccce3b2e04f71479208049401409e085e8001c4842a8bd24215ce000552000c0ed102a447686d600013e806de27a24faf1e188088958050dc0fae12b0fa5adc01c0a691412408409499451e20871090dea0484f8708224710400638087c63ec008220910460778933ca3bc47b02085c443e714d117198b1c42445bc42fee50e16fa0a0b82389652c8850b2e38c0b30b61645985961c7038b8e4418620e218443c4e4414461820f610510f6624218238618c58ffe8e1fe104988c33c33c00cb01e196f0030130d30835c49851cc20c23030c1ac7287360728674b230c1c5a2a21a20e230d135106118c71a7030b4435c19c)

def s1016 := certify 255 7 ([w222,w43,i6,w12,i7,i0,i1,i4]) cs255 [] (u255 5 109 0x1302dc238f104b88b3b853dc492502004086d00dbc47862286e16b700656ca40924094100d84104988f10f9c458e22fee1417044f26d4410ae05b0b2e39108788608c484f00f0130930830730ce31510d118e10d706e8208c70469c282060e1c711578858b8185c)

def s1017 := certify 255 7 ([w44,w43,i6,w12,i7,i0,i1,i4]) cs255 [] (u255 5 109 0x2605b853a471a631c739c58ce5162924a0400810da04e31c738471cdf1630fc58c9204a0806c20824c478937471ae91c736c58be51624d45885b0b22c4588e310e38c608c484f00f0130930830730ce30831c630e320821a2c4e086084f00f013093087310411442bc71b8e0ab16230411ba)

def s1018 := certify 255 8 ([w43,w8,i6,w12,i7,i0,i1,i3,i4]) cs255 [s937,s1016,s1017,s890] (u255 5 128 0x9816e1041c49884106131e1041442885a04224282060e385795738558ab0c213c6b9c70a3492502002a8570001021b4001e78000bb87d00079e0249025040dfe08201b08209311e20934c20872681049a61320d7105b0b6164308710c221dc18231210dd04119e01e0261261060e619c668619a19a21a3181)

def s1019 := certify 255 7 ([w231,i0,i6,w12,i7,i1,i2,i4]) cs255 [s985] (u255 4 106 0x1605b884a142217e819e80ca20ea230670e661c638cd1a858a074a252a0801142380020436808d91b21ea152818688202d8594205288740a82a027306b04e09c00dc009c4988f04ea21ea21ec4310415054303b3041f03c076010821502b510f62188)

def w241 : Sig := 0xf0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0f0f0f0

def s1020 := certify 255 7 ([w241,i2,i6,w12,i7,i0,i1,i4]) cs255 [] (u255 6 106 0x11816e0810832c085f8819e2091228080081d8008d91b21e20c54881862005cb80005cb80122404502006c10209311e10ae95d10643c6a8819a20268d010268d010808b56040814a21c47805e0106cdc833e106f841ac10b043af00bc021c610201429f0831821608)

def s1021 := certify 255 6 ([w85,w236,i6,w12,i0,i1,i4]) cs255 [] (u255 5 84 0x420d6085f9033c80832875092494088d91b21e20c549030c8002284702490250403610ae95d10643c6a903348102fdc2102944390e39610704304278078098498428a15e20cc20559077430d145f083)

def s1022 := certify 255 7 ([w236,i2,i6,w12,i7,i0,i1,i4]) cs255 [s1021] (u255 5 106 0x9816e10420d6085f9033c8492502004086d008d91b21e20c549030c8002284702490250403610412623c42ba5744190f1aa40cd2040bf70881016c2c9040a510e4065083a85d3690d7d4517c20dc72c20e086084f00f013093087310405142bc419840ab206)

def s1023 := certify 255 7 ([w117,i0,w44,i6,w12,i1,i2,i4]) cs255 [] (u255 4 106 0x1083142217e819e80ca20ea21c638cd188316281d2894a82004508e023646c878831528186840a510e87086088c0ecc107c0f014a15e20d88156804e404e47601082104a09454205f05e42001b90ae95d10643c6aa066a30216e20ce60e6610200da0805b4059408f)

def s1024 := certify 255 7 ([w61,i0,w44,i6,w12,i7,i1,i4]) cs255 [] (u255 4 106 0x1605b88420c50885fa067a252a08020436808d91b21e20c54a061a2080b61650814a21d0e10c11781e03b008410a942bc41b102ad009c809c860766082094128a8400372104988f215d2ba20c878d540cd41eb1269104500470183387330e31c668c418b140e9402f)

def s1025 := certify 255 7 ([w189,i1,w44,i6,w12,i0,i2,i4]) cs255 [] (u255 4 106 0x1083142217e819e80ca20ea21c638cd188316281d2804a09454205f05e42ba5744190f1aa819a82001b91029443a1c21822303b304104e404e45285788362055a3c0f01d804208652a08011423808d91b21e20c54a061a30216e20ce60e66126411e4805b4059406d)

def s1026 := certify 255 7 ([w85,i2,w44,i6,w12,i0,i1,i4]) cs255 [s1021] (u255 4 109 0x8418a110bf40cf4083c87914a54111b23643c418a940c34002e85d0002e85d002504a2a1000dc8574ae88321e3550335040d21a4840d21a48814a21d081d63ad0e10c11781e0027202722942bc41b102ad0e0d61cdcec0210421e441e4468c419a31063ad03ad06840d1883)

def s1027 := certify 255 7 ([w87,i2,w44,i6,w12,i0,i1,i4]) cs255 [] (u255 4 106 0x1083142217e819e894a8223646c8788315281868004508e004a094542001b90ae95d10643c6aa066a0817c1791029443a1c21822f03c004e404e45285788362055a0c0ecc105d804208432883a88718e334620c58a074a30216e210200da0126411e4805b40594073)

def s1028 := certify 255 6 ([w240,w12,w44,i6,i0,i1,i2]) cs255 [] (u255 4 84 0x16281d281c638cd18830ca20ea2004508e01528186823646c8788394a82205f05e42001b906aa066a0ae95d10643c12825151029443a102fc67a0c0ecc107c0f001390139188156852857883708108a100ee2)

def s1029 := certify 255 7 ([w55,w12,w44,i6,i7,i0,i1,i2]) cs255 [s1028] (u255 4 103 0x60ce1ccc2c503a5038c719a3106008a11c001021b402a5030d046c8d90f10640be0bc8400372104988f20d540cd415d2ba20c87c1016c2ca1029443a0c0ecc107c0f0013901391d80420858815685285788310650ea294a8204a094540d62fd033d0270c110a1)

def s1030 := certify 255 7 ([w19,i7,w44,i6,w12,i0,i1,i2]) cs255 [] (u255 3 106 0x1c638cd188316303a619d6bab60ca41d48022847023646c87883153030e01d4b3b002604c0a9205f05e8800dd0ae95d10643c6ac0cd8474ece5012825202b029443c43a5747102fc67c303b608207c00f8027404e9542bc41e40ab8e16eb1562f10c120ee0648418a12)

def s1031 := certify 255 7 ([w151,i7,w44,i6,w12,i0,i1,i2]) cs255 [] (u255 4 106 0x718e334620c58a074a0c19c3998011423808d91b21e20c54a061a002043680817c17908006e42ba5744190f1aa819a8209311e440a510e8405b0b28303b3041f03c004e404e45285788362055a1d8042086020ca1d4529504094128a8210628442fd033d0270c110b7)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s1032 := certify 255 8 ([w44,i6,w12,i7,i0,i1,i2,i4]) cs255 [s1019,s949,s1020,s1022,s973,s1023,s980,s983,s986,s1024,s1001,s1025,s1026,s1027,s909,s1029,s1030,s1031] (u255 4 327 0x1b910b0b7f06e5588b7c0848cc42106abc41a3355a2844188426c42fd0145026c288cf40901e4c19441ec41e43d8751184aacc6c0e50ceaa472873c18c68f438c4198719a331a3107a1063acc2c51a40ebd0e941914f484095014178432c00305d08a32c2e8473000a4400c0ed102a3c7686dc00043c046c41f88d90ff10f106010637c02a501f5037c3e8c34010204e0968404a220a809e8a048430690be91c3482f310887c8400c7020918e0dc0421e521303bc4998b1de23f042083215d21e09cae88304e20c8790878ad20d5402940ad05233504414929300b284605985b0b22cc2ce1080e2840830c22943886110e20d080a2e7084a88288951822708ce30ff2620ecc35cc3fdc107cef005e83c2f7c070013b8139051901386b04e47102cb9d809f80b213c10e1c08438b9420c68a8388d115e20dc20c5984f621c8166e156809e8)

def s1033 := certify 255 6 ([w46,w44,i6,w12,i7,i1,i4]) cs255 [s886] (u255 4 81 0x2c0b71084186b10bf40cf44a541004086d011b23643c418a940c340080dc90405b0b2840a510e8708608bc0f01d80420854a15e20d88156804e404e404a09454209311e42ba5744190f1aa819a8)

def s1034 := certify 255 7 ([w47,w44,i6,w12,i7,i0,i1,i4]) cs255 [s1033,s888] (u255 4 109 0xb02dc4210628c42fd033d12950401021b4046c8d90f1062a5030d0031d5002504a2a1000dc8412623c8574ae88321e355033504306b241016c2ca1029443a1c21822f03c004e404e4760108215285788362055a0c0ecc104c246e230670e661c638cc20c58a348)

def s1035 := certify 255 8 ([w44,w8,i6,w12,i7,i0,i1,i2,i4]) cs255 [s938,s1034,s1017,s902] (u255 6 128 0x4605b8205c098820580c7820542802c80ba020d9b906341831a0c434d061ae1830a32448a020112300002076000078f00005dfe000078f00489011409797040801b040824c4784089930408725404089930465a841dab563070c021c40e04304106741a01e0078026089820e308100e2ae2bc74ec02ac55979)

def s1036 := certify 255 7 ([w25,i4,i6,w12,i0,i1,i2,i3]) cs255 [] (u255 6 112 0x2040f7c813626c7cc21c304d38e0d01d0610a21470c81ea3d610f90c6251b860152b00011230023a474a5c80042ccd803c0001e09b9e0409797040801b0424a496414b085f54044c102262f65ec43c89d720b4885804c8991c610200dc836601b000810823c2093142a648183215a04095d98)

def s1037 := certify 255 7 ([w191,i4,i6,w12,i7,i1,i2,i3]) cs255 [] (u255 6 109 0x204060715da504e90d5c4cf7115548cfd20680e8306cdc831f3a4b86917fc477f12214897d200a9580008918000103b0035ba48d6926dc485f11cd4854d2125c56ac62c54843d248605ba44948b2449884ca408f370408baf0408d80040823c4984554921d25988bee22890224)

def s1038 := certify 255 7 ([w192,i4,i6,w12,i7,i0,i2,i3]) cs255 [] (u255 5 109 0x82060e237c417e0548a95ba2e46ea465d21820f430c19c398c6df8763c1432869bc5c94548c6a4206ff04102fdc20824c4788d6f83f7c26d4da2e5379cd4888a44745c85b0b22e60af021f849816e925c2c9245944ca400570aa00011c228026c200006d102015c245e0c30858b9092012)

def s1039 := certify 255 7 ([w193,i4,i6,w12,i7,i0,i1,i3]) cs255 [] (u255 6 109 0x20406070e3447d510b138764e1e9c8d77200a958000103b001b7447851143385ace14528a7af204dcf020400d820412623c21f34458d117f38504e22144390f5885396ac1c388843a2c8605be438e88b222ce704c9c0cea006011804408b825e0dcb3061488d6a218707a9c0408c4e4)

def s1040 := certify 255 7 ([w194,i4,i6,w12,i7,i0,i1,i2]) cs255 [] (u255 5 109 0x30670e630e31c668c418b12074907a7441fa00114238000810da011b23643c418a92061903746e901d040bf708201b08209311e215d2ba20c878d5206690554aae84050202d85920814a21c8d1816fa6820d6d05f9026481ba18208015c00aa278206f39882028a09a20cc204d901043074)

def s1041 := certify 255 8 ([w22,i4,i6,w12,i7,i0,i1,i2,i3]) cs255 [s1036,s1037,s1038,s1039,s1040] (u255 6 129 0x204060723398976609b1363e610e18269c718b1c38bc8680e8306cdc831ad35b30d0f51eb087c863128dc31310c18c080a9580008918000103b000048a7800021666c01e0000f0d70000d784dcf0204bcb820400d820412623c204486982042faa0226081130a30810c8a67d42a15ab10a14c10f3062bb302dcc4ce058b42c02644c82)

def w242 : Sig := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff00000000

def s1042 := certify 255 8 ([w242,i4,i6,w12,i7,i0,i1,i2,i3]) cs255 [] (u255 6 138 0x1020303919cc4bb304d89b1f309a02112083407418366e418d69ad98687a8f5843e7202e808054ac000448c000081d80002453c00010b33600912280826e781025e5c102006c10209311e1022434c10217d5011224045133c2b5621429821e602306e410266f301024330810e12a384a86f41bd1e0078026089821837260dc8a15c260c1982150)

def s1043 := certify 255 8 ([w54,i4,w8,i6,i7,i0,i1,i2,i3]) cs255 [] (u255 6 132 0x4080c0e1562af04e467312ecc1c2544a8e1c2bc4a8e0d01d060d9b9060c434d0635a6b6612d0c6251b86341831a0152b00011230000207600005de218000914f003c0001e88200038309b9e0409797040801b040824c4784087254040890d3044c1022650102284cecad5a5e380670c021c43abb302dcc7efc85704c26e58b02142a6137)

def s1044 := certify 255 7 ([w240,w12,w8,i6,i0,i1,i2,i3]) cs255 [s1011,s1028] (u255 4 105 0xab156184278a3738d0b857957703510891182083b31886e8c1acc625ba31b419441d4400aa15c0008a11c002ee1f400f7800f7812950440de0f4840be0bc840037210e48292101382721013827202504a2a303886110e16c41444a1630216302)

def s1045 := certify 255 7 ([w9,w55,w12,i6,i0,i1,i2,i3]) cs255 [] (u255 6 109 0xab15782710207be40680e830621a68308510a386400a95800089180002eff0011d23a52e404dcf0204bcb820400d8204392a0212524b20a597b2f621e40268224102c9d011224501244808a02c14013004628021c610200dc83663c00f004c113041832d5a1428c48)

def s1046 := certify 255 8 ([w55,w12,w8,i6,i7,i0,i1,i2,i3]) cs255 [s911,s1044,s1045,s1012,s1029] (u255 6 125 0x20406070ab15782718b1c39a48e15e55c70680e8306cdc830621a6831310c197e9a0c18d00a9580008918000103b00002eff00003c780003c78004dcf0204bcb820400d820412623c204392a02044c982044c9820d7656ad58c03386010e2813411208164e808912280922404505182c140102a14016a)

def w243 : Sig := 0xffff0000ffff0000ffff0000ffff0000ffff000000000000ffff00000000

def s1047 := certify 255 8 ([w243,i4,w8,i6,i7,i0,i1,i2,i3]) cs255 [s911] (u255 6 132 0x4080c0e1562af04e467312ecc680844820d01d060d9b9060c434d0635a6b664edc80ba020152b00011230000207600005de218000914f002448a0209b9e0409797040801b040824c4784087254040890d30448901144cf6ad2f1c030118372081606b20813379808578e2ae3837a0de8f003c013044c10c1b9306e7021510e21c56a)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s1048 := certify 255 9 ([w8,i6,w12,i7,i0,i1,i2,i3,i4]) cs255 [s939,s943,s952,s956,s958,s961,s964,s974,s981,s984,s987,s989,s992,s996,s998,s999,s1002,s1015,s1018,s1032,s1035,s1041,s1042,s903,s910,s1043,s1046,s1047] (u255 6 393 0x1b90408c385306e5c28b7300813db040b83d9e0f5deabd3e00812c7040b050c0b1e818fc00813d104089bd0a0dce85026e0810f71cd01095043dc4a88904381181c82c4e4062718b03871491c3b80d115e52468957e0387609c2ac598e157807601673a71496e2dbcbc8e1c52470e2f2524bcf80d9017a05e3d74041811490c1870ff809647fba1c1832590c18c0e5cc96472f230183259346b8060c964306e068d2590c1b01a21a964d1ac01832596dab7cc0860c964306302964c0943c481002450014047810bd00007121a82f490d61c0000cb000035c8832ee460c0003850000c0ed102ac476ec30000700001c19e3dc0f1e7060002af000307c2eeab7e7cc00002ab0000d79e3caa4f1e35e000024c90a0448082022898a14908107109dca4484bc1c1022590810368bca3f42e0c102281081000c70091c63b6001023850810c0ef12687c7788f3010220908138264c795326e010218b08130283924c5428c01020d70810c8a64c28d3263221021592b2c8b0ea2c2584de8ab182d181676ac0b3b063060e04bf81bdc180de92f10ebac978c)

def w244 : Sig := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffffffffffff0000ffff0000

def s1049 := certify 255 8 ([w244,i4,i6,w12,i7,i0,i1,i2,i3]) cs255 [] (u255 6 138 0x10203038418a27e284d89b1f30870c134e38688e1c3443407418366e4191227c287a8f5843e437af41837af418054ac000448c000081d801c385428010b33600f000078f00007826e781025e5c102006c10209311e1295214a8217d50113040899304089a442b56211a9158051b9306e4c4c1530542c02644c8237260dc98982a60a1832160)

def s1050 := certify 255 7 ([w240,w12,w96,i6,i0,i1,i2,i3]) cs255 [] (u255 6 105 0xab157827083144fc5340422410680e830621a6832244f856405d0100a95800089180002eff003870a85122450104dcf0204bcb820400d8204392a0252a4295244808a1a9c02ad02a00870d11c344d06341be00f8014045010670a00a8020428b02)

def s1051 := certify 255 7 ([w82,w55,w12,i6,i0,i1,i2,i3]) cs255 [] (u255 6 109 0xab157827083144fc5204060688680e830621a6832244f8506cc68300a95800089180002eff003870a8500103f0004dcf0204bcb820400d8204392a0252a429504126a021a9158050c196300268224102c9d011224501244808a02c14011604628029028c0a)

def s1052 := certify 255 8 ([w55,w12,w96,i6,i7,i0,i1,i2,i3]) cs255 [s1050,s1051] (u255 6 125 0x20406070ab157827083144fc50680e8306cdc830621a6832244f8500a9580008918000103b00002eff003870a8504dcf0204bcb820400d820412623c204392a0252a429548b56ac603538050e1a238689a0c6837c01f002808a020a319c013411208164e80891228092240453502c140102a140116)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s1053 := certify 255 9 ([w96,i6,w12,i7,i0,i1,i2,i3,i4]) cs255 [s1049,s914,s1052] (u255 6 393 0x1b90408c387306e5c38b7300814c040850d715305196140812c7040b050c0b1e818fc00810f71cd01095043dc4a88904381181c82c4e4062718b03871831c20c50d11460c6893f14385609c2ac598e157807601673a7780d9017a05e3d740418130b0c1870ff80a5c7fba1c1832970c18c0e5cca5c72f2301833e348850644f833e146852970c1b01a21aa5cd1ac0183143c481002450014047810bd00007121a82f490d61c0000cb000035c8832ee460c0003870000c0ed102a5476ec300002a00e051e70a8f2a140051bd000307c2eea57e7cc0000024c90a0448082022898a30b08107109dc87484bc1c1022970810368bc87742e0c102295081000c70087463b6001023870810c0ef1268747788f301020a0949526a42930a541151bd0813028392875428c01021612c322c60b46059dab02cec18c180de92f3526f7060146f455026f4011bd0543550044dc10e2f23868b0b1a239858e1a25e4689a3026832970c694b9a0c60437c35ff001bd01f14afc006bc028322a021bd08a10ea80864421bd2b2564de959e06f5768c)

def s1054 := certify 255 7 ([w113,w224,i6,w12,i7,i2,i3,i4]) cs255 [s916] (u255 5 109 0x9816e104506b082304c85a04224282060e106513f28820459819420ea10c107a1860ce1cc62e2526529c72c302498c05930c28389411530888ec704f3866866980b2c6c52352b6310b9960824c0249053001542b80004508e00024c478054c527532c32c)

def s1055 := certify 255 7 ([w34,w224,i6,w12,i7,i1,i3,i4]) cs255 [s917] (u255 5 109 0x1302dc208a0d610460990b4084485040c1c20ca27e510408b3124940800aa15c0004086d011e9495ca17260c930008a11c0092630164c30a0e2504a04a5c78cc3dd700f01705962e2aa2ae30ef98504412e6825025264f26d66984988f98a98a4f6e38608b)

def s1056 := certify 255 8 ([w224,i0,i6,w12,i7,i1,i2,i3,i4]) cs255 [s1054,s1055,s918] (u255 5 138 0x4c0b7082286b841182642d021121410307083289f9441022cc0ca1075086083d0c30670e63171293294e39618924a0400550ae000114238000810da023d292b942e4c19260493180b261850712825025264f26d6698614734c006b02612623e62a6293d9961960812812813ce09e70cd0cd3c03c03016580b2554507132c32c)

def w245 : Sig := 0xffff0000ffff0000ffffffffffffffffffff0000ffff0000ffffffffffff0000

def s1057 := certify 255 6 ([w113,w206,w245,i6,i7,i2,i3]) cs255 [] (u255 4 81 0x210438721022d80d442244286c2d6c60820ecc60ce1ccdce02d60651075104b0976d03163150b2c42ec602d1049c084c13222a62111100550ae0004508e000932060602d602d94849d48413a0)

def s1058 := certify 255 6 ([w34,w206,w245,i6,i7,i1,i3]) cs255 [] (u255 4 81 0x8410e1c8408b6035108911e305e61c17802a8570004086d00b960c964a541005d89100022847033563150b2c482c61411049c084c1322a085413aa9d1889d13a24c8189de718e24541508405fa)

def s1059 := certify 255 7 ([w206,i0,w245,i6,i7,i1,i2,i3]) cs255 [s1057,s1058] (u255 4 106 0x420870e42045b01a88448850d85ad8c1041d98c19c399b9c05ac0ca20ea209612eda00550ae0004508e000810da0172c192c94a8200bb1220062c62a16589058c05a2093810982645410a827553a3113a2757f8a313a27401ac02744990313ac05ac7122a0a84)

def s1060 := certify 255 6 ([w113,w33,w245,i6,w12,i2,i3]) cs255 [] (u255 4 84 0x143616b642045b01a88448810821c38c1041d982584bb6b9c05ac0ca20ea230670e6661a90fec42ec602d12ac21304c88a988444418db1600550ae0004508e000bb1220602d602d94847b48406e0)

def s1061 := certify 255 6 ([w34,w33,w245,i6,w12,i1,i3]) cs255 [] (u255 4 84 0x50d85ad908116c06a211223c60bcc382f00550ae000bb1220172c192c94a82002f0da0004508e061a90fec3bec614112ac21304c8a8215017acfc02f3041076609612edae71822c541508405e6)

def s1062 := certify 255 6 ([w35,w33,w245,i6,w12,i1,i2]) cs255 [] (u255 4 84 0x9612edae7016b032883a891683d30e0f4c1041d980114238002ec48805cb064b252a0800f4368001542b8186a43fb016b183344ab084c1322a085406364636143616b642180b4541508407ae)

def s1063 := certify 255 7 ([w33,i0,w245,i6,w12,i1,i2,i3]) cs255 [s1060,s1061,s1062] (u255 4 109 0x286c2d6c8408b60351089102104387182083b304b0976d7380b5819441d4460ce1ccc00aa15c0008a11c0017624402e5832592950401021b40c3521fd80b58c05a255842609915042a08f70d7708f30a3308f006b012fb103b3016b0168a82a1018db16)

def s1064 := certify 255 6 ([w34,w113,w245,i6,w12,i7,i3]) cs255 [] (u255 4 81 0x21043870a1b0b5b21022d80d4422440c58c5c2cb186a43fb041670212ac21304c8801542b800204368002ec4881877d85065211ed2101780c1041d98c19c39982584bb6b9c608b11531111)

def s1065 := certify 255 6 ([w35,w113,w245,i6,w12,i7,i2]) cs255 [] (u255 4 81 0x1833873304b0976d7380b5819441d4460820ecc0c58c5c2cb186a43fb041670212ac21304c88011423800204368002ec488180b583365211ed2101e8010821c3850d85ad908602d11531111)

def s1066 := certify 255 7 ([w113,i0,w245,i6,w12,i7,i2,i3]) cs255 [s1057,s1060,s1064,s1065] (u255 4 106 0x10821c3850d85ad908116c06a211223041076630670e6609612edae7016b032883a8818b18b859630d487f6082ce04255842609910377131703730d73037c0a3c037b06bb310bb01688a988889001542b80011423800204368002ec488180b580b65211ed)

def s1067 := certify 255 7 ([w34,i0,w245,i6,w12,i7,i1,i3]) cs255 [s1058,s1061,s1064] (u255 4 106 0x10821c3850d85ad908116c06a2112200550ae000810da000bb1220172c192c94a82004508e0062c62e1658c3521fd820b3810956109826440bcf198705e0bc035c00bf028c1782f59e1ac17b0efb0a08a82a10c1041d98c19c39982584bb6b9c608b15054)

def s1068 := certify 255 7 ([w35,i0,w245,i6,w12,i7,i1,i2]) cs255 [s1062,s1065] (u255 5 106 0x1833873182584b59a71cb0c0ca1075086083d0c004508e000204368000bb12200b9306498924a0400550ae06063170b26186a43f98105960208a58208c1321788b4c3f9e0028c0f16886bf3c5918ac65860cd0940941208183850ac2d5620832c094094)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s1069 := certify 255 8 ([w245,i6,w12,i7,i0,i1,i2,i3]) cs255 [s1059,s1063,s1066,s1067,s1068] (u255 4 327 0x1870210b213c10e027e02cb9c79dc286c346c79c688b5b3ac22c27a18e408b708b604f60f77035109510f712a2244e1379319c3fc20ad51fe0edc6312f31b039433ad51ca1cf0635b412c389825d8d60e3ad02d3719ae02dd02d61981e74194461079307516842f40071210aa2f490857700032c00305d08a32c2e84730004bc00c0ed10294c7686dc0001c400b785d871f091b00023402e581f582343e8c9601943db21025405047b44de48471090de62c8483d7108b548430690be4c43482f310894c8400c700d718e0dc04212f21303bc498a31de23f04212f212c09c6c86b04e276c4230818c168290c6c052c05a405a20520968404a220a80a684bc978310b2c66222b170b31142ce18c0e2c659da9a90e2ed43fd98cc08416539859c117c05910ac210714e6ab117b07110821884c0a2c0861444cb042)

def s1070 := certify 255 8 ([w245,i4,i6,w12,i7,i0,i1,i2,i3]) cs255 [] (u255 6 138 0x1020303919cc4bb3040811630709512a38709512a383407418366e418d69ad9868e1c5830318946e18d060c68054ac000448c000081d80002453c005c8c19230f000078f680007b426e781025e5c102006c10209311e1022434c1316218b1304089940408a1338c316060c35285462bb302dcc4ce058b4219086023160c58142a670843210c)

def s1071 := certify 255 7 ([w113,w206,w11,i6,i7,i2,i3,i4]) cs255 [s1057] (u255 4 103 0x2c0b71098264454c422220d44224408410e1c8408b63857957706510751182083b3183387337380b59a31b40cd8c542cb10bb180b5420d62508327ea51714caa5049c2830a3504ea5275948409c01542b8001142380024c478180b580b48404e0)

def s1072 := certify 255 7 ([w34,w206,w11,i6,i7,i1,i3,i4]) cs255 [s1058] (u255 5 103 0x1302dc208c132128104a6810890a081838820459878ee30f7249281001542b8000810da00b930649805cf00004508e06463150b2624130c2825041ac2284193f28a47a95ca2824b05061aa628a4f6128129327936b34c24c47cce386389104b9a)

def s1073 := certify 255 8 ([w206,i0,w11,i6,i7,i1,i2,i3,i4]) cs255 [s1071,s1072,s1059] (u255 5 132 0x4c0b7082304c84a04129a04224282060e20811661c2bcab9c19420ea10c107a1860ce1cc671cb0c68619a492502002a85700008a11c0004086d005c98324c01e780c8c62a164c48261961410d708a1064fca28b8a6528a47a95ca2824b0506198a293dd4128129327936b34c30a39a6003581309311f319618e244)

def s1074 := certify 255 7 ([w113,w33,w11,i6,w12,i2,i3,i4]) cs255 [s1060,s920] (u255 4 105 0x8388a31098264454c422220d442244e15e55dc8408b60210438706510751182083b368c6d7380b5860ce1ccc6a438b10bb180b4cc88358827b827b8da369418700df00dfc0f0019e300de5217801542b80011423801ef0180b580b48406e0)

def s1075 := certify 255 7 ([w34,w33,w11,i6,w12,i1,i3,i4]) cs255 [s1061,s921] (u255 4 105 0x8388a310982645410a80d442244e15e55dc8408b61e305e61c17ca541002a857003de00b960c96001786d0002284701a90e2c3bec614133220d6209ee09eef03c05061c02fc02f368da05f8c02f1505430410766d18dae71822c8405e6)

def s1076 := certify 255 7 ([w35,w33,w11,i6,w12,i1,i2,i4]) cs255 [s1062,s922] (u255 4 105 0x8388a310982645410a819441d45a31b5ce02d622d07a61c1e982083b34a5410022847003de00b960c96001e86d0002a85701a90e2c05ac60cd33220d62368daf03c0506136a0f4da83d11ee11ee07a6d4da83d1505470af2aee42180b48407ae)

def s1077 := certify 255 8 ([w33,i0,w11,i6,w12,i1,i2,i3,i4]) cs255 [s1074,s1075,s1076,s1063,s923] (u255 4 134 0x41c4c5884c1322a085406a2112270af2aee42045b010821c3832883a88c1041d9b4636b9c05ac30670e6694a8200550ae0004508e007bc0172c192c00810da03521c580b58c05a66444c4413dc13dc6d1b5e0780a0c223c9788f32380b380b22a0a823dc35dc23cc28cc23c01ac04bc3888f0e2c05ac05a40678c071)

def s1078 := certify 255 7 ([w34,w113,w11,i6,w12,i7,i3,i4]) cs255 [s1064,s927] (u255 4 102 0x5816e2107114621304c881a88448810821c39c2bcabb908116c066cc05961a90e2c33220d6209ee09eec059c0595061f03c0368da9485e00550ae000810da007bc061df61412101780454c4444c1041d98c19c399b4636b9c608b)

def s1079 := certify 255 7 ([w35,w113,w11,i6,w12,i7,i2,i4]) cs255 [s1065,s928] (u255 4 102 0x5816e2107114621304c8832883a88c19c399b4636b9c05ac30410766066cc05961a90e2c33220d62368dac059c0595061f03c009ee09ee9485e004508e000810da007bc0602d60cd2101e80454c444410821c39c2bcabb908602d)

def s1080 := certify 255 8 ([w113,i0,w11,i6,w12,i7,i2,i3,i4]) cs255 [s1071,s1074,s1078,s1079,s1054,s1066,s929] (u255 5 131 0x1302dc20838a09082304c85a04224282060e385795738820459819420ea10c107a1860ce1cc668619a71cb0cc8c602c986a4389866423ca104f38279c334334c059602c94184c8ec62f678078008a984447638989db0c35c6d98146c6cf7c35ec621732c1124827800aa15c000228470001021b4001e78032c32c)

def s1081 := certify 255 8 ([w34,i0,w11,i6,w12,i7,i1,i3,i4]) cs255 [s1072,s1075,s1078,s1055,s1067,s930] (u255 4 131 0xb02dc420e2794426099103510891021043873857957721022d92950400aa15c001021b400f7802e583258008a11c00cd980b2c3521c593bc462c413dc13dde078180b380b2a0c26441793105e6d1b42a0a80bcf198705e0bc035c00bf028c1782f0e21ac17b0efb0a09054150c1041d98c19c399b4636b9c608b)

def s1082 := certify 255 8 ([w35,i0,w11,i6,w12,i7,i1,i2,i4]) cs255 [s1076,s1079,s1068,s931] (u255 5 131 0x1302dc20838931082304c8419420ea10c19c398cd0c334e396183041e8649250200228470001021b4001e78017260c93000aa15c0c8c602c986a4389866421ae10cd0cd3c03c03016580b2506136be1b5f0279c13ce094094f116987f3c005181e2d10d7e786d4daf865860cd10250252081838e15e55ce20832c)

def s1083 := certify 255 8 ([w54,i4,w11,i6,i7,i0,i1,i2,i3]) cs255 [] (u255 6 132 0x4080c0e1020458c1c2544a8e1c2bc4a8e0d01d060d9b906387160c0c6251b86341831a0152b0001123000020760017230648c3c0001e8820003e709b9e0409797040801b040824c4784c58862c4c102265010228643278af11830d4c2193119a5d986b4d6cc3491401e0090c2260931339899809bcc2c5852bb302dcc421908602)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s1084 := certify 255 9 ([w11,i6,w12,i7,i0,i1,i2,i3,i4]) cs255 [s1056,s1069,s1070,s1073,s1077,s1080,s1081,s1082,s932,s1083] (u255 4 402 0xdc88586378372c6c5be04225e2107125e1c54092f48e1c442086213028b021851132c1087bb81a884a887b895112270b0e04216427821c04fc0597398cb9c1c4688af632344ab8717384584f431c8116e116c09ec0f260ca20f620f21ec3a88c263263387f8415ae3fc1db8c65ae6360728675ae39439e0c65afad0713196b98c1c75a05a6e335c05ba05ac3329e90812a0282f085e800e2421545e9210aee0006580060ba1146585d08e60018d80181da205298ed0db800038800f9fde0e3ef3e700046805cb03eb04687d192c030409c12d080944415013d18c908e2121bd0f90907ae2116b90860d217d0486905e621129908018e03ca31c1b80846364260778933163bc47e08425e4207104e09c9882704e1c4846103182d05218d80a580b480b575aeb0661658cc31bc0596361670c61bd25e6a43892f0e26f58c25e4dc9b889788978d7146226e209e5e427b98cb827b1909ee2f2e31813696be8cb5cda303af1aff009783c94fc035e004e644139097901386b04e43224c2edc0592d216705a701657585937abb544bcac861)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s1085 := certify 255 10 ([w12,i7,i0,i1,i2,i3,i4,i6]) cs255 [s933,s936,s1048,s1053,s1084] (u255 4 436 0x34a1658c34b816616cd2859166164d2e18c3161c58c262a0c2a1ae1c430887146a6289b8431089bb028b09b8430a22649bb04226e6e44226f826f826e6e4d28b726f81089b84d1089ba89ba89b84d0d7626ea108bc88b09e82f2c720bc88b708b2f2c09ec26e3ddc0d49b884a889b8f712a2249b89c22f3870212f2164278212f3809f82f2165ce2f260dc20cbca868a8bc9831a24fcbca9ca3020b4dc302cd70c082dd02d302c3309b879306526e20f6226e1e43d87526e2308bc979318bcb87f8412f26047f83b2f2e318c0981318c0e072867302604728733038318c083fd023302a30233020fcc0fcc0ab4a35e23402e4d7b03eb0d788d0fa324d7b00c26f4f489b881226f40509b8bc22f22f4002f2e242154bc8bd24215cbcb80030232c0030260ba114c08cb0ba11cc0980035e6bc0035f81da204d79af1da1b4d7e00035e0ac00e4d7abc0e4d782bf02b35ea028c8b0818cc882d05218cc8b014b0c882d202d26e204e0949bd080949b888226f404f42f25e4842f2e2121bcbc9912120f4bcb8843026048430260d217cc09910d20bcc0988435e6bc8435e018e035e6446383735e0210c8991210c8e0778933226447788f3238210c8a8814cc882b04e14cc8a813a8c882b202b2d25a4b4849)

def w246 : Sig := 0xfafffafffafffafffafffafffafffafffafffafffafffafffafafafafafafafa

def s1086 := certify 255 7 ([w246,i2,i0,i6,i7,i1,i4,i5]) cs255 [] (u255 5 106 0xdb420405290314808a58224e8077405f9033c8e38a8a4925021e2810540549030c8002e85d0000ba1740210c882aa2aa0940940d206c00494024a06106114069bae10b895f1419420ea13e94070a05bc8b0818aa8aa825025024a01250308308)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s1087 := certify 255 7 ([w34,w57,i6,i7,i1,i4,i5]) cs255 [] (u255 5 252 0xeb9436d03b681d739f0205202aca14a4071205587118a414404d08228ed94134edac50411070893a073d020e73c3ba012026c217e4051204d85119e40445407053dc54f54500528f2410092802813c11bf0078a03b5037e3b482a002037c0152407d206f87d18640040c7000182e84518e174238c0019104202cd0c859e481041571550d1a8a1a2555716308e094b940ae0943940fb75c00bd003e8bd24605c0049b824a013d009213c24a172065c61071061c61171141c20d70945d70c70c55115434450c55545410c1281ed4083d84a0ca049189aa03bd00923bc24a032060c2c48a08328308188)

def s1088 := certify 255 7 ([w34,i2,w57,i6,i7,i1,i4,i5]) cs255 [] (u255 4 109 0x36e00860295031502558449e01de02fd033d00e41c82b54a5410f1810580a940c34002e85d0002e85d02200cd0a056a0562a0a81a4048c012601260c4310e0d20bc179081a5c5c540fd419441d4486e044e050503ad06502b502b150540930093062188)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s1089 := certify 255 8 ([w57,i0,i6,i7,i1,i2,i4,i5]) cs255 [s1086,s1087,s1088] (u255 4 327 0x1d750db81db81d739e0860a80ab50a5407140ab0e23150a404d109476d4134edd9421107112781cf810739e1de02809b10bf4051409b0a233d02403fd0235181183f303f56941e4c19441ec41e43d875118444cc4d60396044c7295181a03acc2c51a40ebd0e941900ac00e55e0720afc0ad40553d2102540505e10cb000c174228cb0ba11cc001bf00f180ed81bf1da4160080df00a9407d40df0fa30d00403342202ce00cc598338210a052a056c1c15a983a81582905620522a25ba092d8a80a684cc14829313331331ae28cc0a4c4cc1482900c7013318e0dc00a401241484980ef80491de12600a60c1dec402943014b103bd04cc9e914e502b1a20ad434540adc0ac4e1504ad04254547534ed18ff9b41af467183eb9c017a00fa2f49181c0092e093009f009213c24c1d0604f621c86398809e8)

def w247 : Sig := 0xf0f5f0f5f0f5f0f5f0f5f0f5f0f5f0f5f0f5f0f5f0f5f0f5f0f0f0f0f0f0f0f0

def s1090 := certify 255 6 ([w113,w247,i2,i6,i7,i4,i5]) cs255 [] (u255 6 81 0xdb208080a5103144021458112721d880bf1033c40820c843e14f857805e010e12038482c10b04067c29f0af00bc025664070905821608a54853e489012624a496410c58860809a340409a3404)

def s1091 := certify 255 7 ([w247,i2,i0,i6,i7,i1,i4,i5]) cs255 [s1090] (u255 6 109 0xdb208080a5103144021458112721d880bf1033c43870a8512245010f12041480a91030c400b970000b97000820c8452a4295244808a0401a8212524b20862c430404d1a0204d1a023e14f857805e010e12038482c10b04067c29f0af00bc022964070905821608)

def w248 : Sig := 0xffffffffffffffffffffffffffffffffeeee0000eeee0000eeee0000eeee0000

def s1092 := certify 255 5 ([w248,w113,w122,i6,i2,i5]) cs255 [] (u255 5 60 0x529031481b684084517c50b12074904d502a281086441c50af29a19a1ac20e20e9a89959a192014c2995f4c31d59831863308924090)

def w249 : Sig := 0xffffffffeeee0000ffffffffeeee0000ffffffffeeee0000ffffffffeeee0000

def s1093 := certify 255 5 ([w249,w113,w122,i6,i7,i2]) cs255 [] (u255 5 60 0x26a81514058903a488a2f82210c8868668656686485841c41c276813a7042bc213abfcea89d24a49424a018c3198449205f0db4204052903148)

def w250 : Sig := 0xeeee0000eeee0000eeee0000eeee0000eeee0000eeee0000eeee0000eeee0000

def s1094 := certify 255 6 ([w250,w113,w122,i6,i7,i2,i5]) cs255 [s1092,s1093] (u255 5 81 0x36d081014a40c52228be289aa0545016240e920843220e285794d0cd0cacd0c90b083883a6a2638286e10530a657d30c756624a49424a018c319840450a30820ca1d420900d68044051224)

def w251 : Sig := 0xeeee0000eeee0000eeee0000eeee0000eeee0000eeee0000eeee0000eeee

def s1095 := certify 255 6 ([w251,w113,w122,i6,i7,i2,i5]) cs255 [] (u255 5 81 0xdb42040529031488a2f8a26a81514058903a48210c8838a15e53433432b343242c20e20e9224c924472a49110a5f9244024c921064817c50410750ca104804940220c2023b60a6)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s1096 := certify 255 7 ([w113,w122,i6,i7,i2,i4,i5]) cs255 [s1094,s1095,s1090] (u255 4 252 0xeba86dc0edc0eb9cf043054055a852a038a05587118a852026884a3b6a09a76eca108838893c0e7c0839cf0ef01404d885fa028a04d85119e81201fe811a8c08c1f981fab4a0f260ca20f620f21ec3a88c2226626b01cb0226394a8c0d01d661628d2075e874a0c8066844059c0198b3067042038b9ca1a2a0e234457a9ca0a2e7084a8828895182270b4ed19f59b435f4671819b959c027c01984f06707405984f05a872059b9c809e80fae7101b903e8370524711440a60fc138535027503f203f102704a28c809444106b04e09c6590860d217c6586905e6210249092c0769250923b424c09061031a03e863607d62088)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s1097 := certify 255 8 ([w122,i0,i6,i7,i1,i2,i4,i5]) cs255 [s1091,s1096] (u255 4 327 0x75d436e076e075ce782182a02ad429501c502ac388c542901344251db504d3b76508441c449e073e041ce787780a026c42fd0145026c288cf40900ff408d460460fcc0fd5a50793065107b10790f61d4461113313580e581131ca5460680eb30b146903af43a506402b00395781c82bf02b50154f484095014178432c00305d08a32c2e84730006fc03c603b606fc76905802037c02a501f5037c3e8c340100cd0880b380331660ce08428814c158270a6a04ea0564056204e0968404a220a809e84cc8430690be4cc3482f31084cc84013301334fe28c0420492125813324a124e78498120c206341330c6c7dac41101c5ce50d150711a22bd4e5051738425441444a8c11385a768c4f4da0d7a338c1f5ce00bd007d17a48c0e0033714b804f803309e0ce0e80b309e0b50e40b3739013d04f499829)

def w252 : Sig := 0x5055505550555055505550555055505550555055505550555050505050505050

def s1098 := certify 255 6 ([w34,w252,i6,i7,i1,i4,i5]) cs255 [] (u255 5 84 0x1b684080a5206290114b0449d00ee80bf206791c71514924a043c5020a80a92061900081744210c882c652e129f88497c2b807de021b41dea050483be40c25c20530a6555248128494928494031863308)

def s1099 := certify 255 6 ([w113,w252,i2,i6,i7,i4,i5]) cs255 [] (u255 5 84 0x1b684080a5206290114b0449d00ee80bf2067904219105c4af8a0ca107509f4a038502de45847c57c54f50a7984acd01c285845840c334705d10348814c2995f49205312524a12500c618cc2040be1744)

def s1100 := certify 255 7 ([w252,i0,i2,i6,i7,i1,i4,i5]) cs255 [s1098,s1099] (u255 5 109 0x6da1020294818a40452c1127403ba02fc819e471c5452492810f14082a02a481864001742e804219105c4af8a0ca107509f4a038502de45840530a655524812820028c424a49424a018c319840817c3589f15f14834241a105d002e8052d01c285845840c3347069)

def s1101 := certify 255 6 ([w113,w34,w58,i6,i7,i4,i5]) cs255 [] (u255 4 84 0x1b70043014a818a812ac224f00ef017e819e844019a0b8a81fa832883a8824c070c18805a831b4e523551fb115311111e701e7015a815a80720e540fe5217878c079c054a056a001a41780840d20)

def s1102 := certify 255 7 ([w34,i0,w58,i6,i7,i1,i4,i5]) cs255 [s1098,s1101] (u255 4 109 0xdb802180a540c5409561127807780bf40cf40390720ad5295043c6041602a5030d000ba174000ba1740880334171503f50651075104980e183100b506369ca056a0562a0a81a4028c03ce03ce02b502b501ac3482f05e4502b502b150541e701e7015a815a8)

def s1103 := certify 255 7 ([w61,i0,w58,i6,i7,i1,i4,i5]) cs255 [] (u255 5 106 0x1b684080a5206290114b0449d00ee80bf206791c71514924a043c5020a80a9206190005d0ba01086441712be2832841d4209280e140c22c20298532aa924094100d8425280fd406a903348102fd027c57c520d09068417400ba00e14070a16116103069)

def s1104 := certify 255 7 ([w113,i0,w58,i2,i6,i7,i4,i5]) cs255 [s1099,s1101] (u255 5 106 0x36d081014a40c52022960893a01dd017e40cf20843223e2be283c841e421c280e142c22c206f8af8a0f210790824a03850308b08291a947ec22a611111e680f34056902b48d9a146d06b3b6384e382be49209e1e280f34054902b48002e85d0000ba1740)

def s1105 := certify 255 7 ([w123,i0,w58,i2,i6,i7,i4,i5]) cs255 [] (u255 5 106 0x36d081014a40c52022960893a01dd017e40cf20843223e2be283c841e421c280e142c22c206f8af8a0f210790824a03850308b080a614caaa49025094a03f501aa40cd2040d21a441034869138e2a2924940878a0415015240c32000ba1740002e85d036)

def s1106 := certify 255 7 ([w19,i7,w58,i2,i6,i0,i1,i5]) cs255 [] (u255 6 106 0x528818a2057658a285022c09c38542854881862005cb80005cb8000761da00912280a95214a82006c106a8819a20268d010268d0102761de11224045047613e2040bf19e21f0a7c296085820330ecc3b7805e013e14f850c10b0430ecc3b7805e0110)

def s1107 := certify 255 7 ([w151,i7,w58,i2,i6,i0,i1,i5]) cs255 [] (u255 5 106 0x14a40c5206da1021c715142a481864001742e80005d0ba00f14082a014c299550806c20d520669020690d22081a434884a501fa81086447c57c55845840c38501c287c57c51845840494070a0114b04924a052481282fc819e4041e43c8410790f21077)

def s1108 := certify 255 7 ([w168,i5,w58,i2,i6,i7,i0,i1]) cs255 [] (u255 4 106 0x1e3020b015281868005d0ba0005d0ba000bb122094a822001b9094c07ec06aa066a081a4349081a4349083644e90128251511006681c301c3005a805a835a27db41e441e4412603860c402d459b5d9c1e441e45136112e0f75034d0a24f00ef017e819e8)

def s1109 := certify 255 7 ([w171,i5,w58,i2,i6,i7,i0,i1]) cs255 [] (u255 5 106 0x3c5020a80a9206190005d0ba0001742e81c71514201b084a501fa80d520669020690d22081a4348814c299551086440e14070a161161037c57c50494070a0611611f15f1436d081014a40c52124940a49025093a01dd017e40cf2020f21e42083c879096)

def s1110 := certify 255 7 ([w12,i7,w58,i2,i6,i0,i1,i4]) cs255 [] (u255 5 106 0x17e40cf202816284114b04924a042a481864001742e80005d0ba00100ed038e2a2a4902504036106a90334810348691040d21a441201de20530a6554440164820528c5203c841e42b08b0819a8039c1f15f141e420f211845841d005983e2be290)

def s1111 := certify 255 7 ([w97,i7,w58,i2,i6,i0,i1,i4]) cs255 [] (u255 5 106 0x17e40cf2093a01dd049250215240c32000ba1740002e85d0078a04150924094100d841aa40cd2040d21a4410348691094a03f50210c880f210790ac22c2061c280e1403c841e42308b0809280e140a0960b8e2a28298532aa14a40c520afbe28afbe2a0)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s1112 := certify 255 8 ([w58,i2,i6,i7,i0,i1,i4,i5]) cs255 [s1086,s1100,s1102,s1103,s1104,s1105,s1106,s1107,s1108,s1109,s1110,s1111] (u255 5 327 0x75ca1b6829140eba8f81029015650a52038902ac388c520a202684114a04a09a91d628208838449d043e81074121dd009013610bf20289026c288cf20222a03829ee2a7aa28029479208049401409e08df803c501da81bf1da41500101be00a9203e9037c3e8c32002065800341742e8cb0ba175a00017a000705d0ba2f42e85d38000a1029d530532a62aa12a0a69141240840949943ca20800c700c58c7d801041e621294077a03cc778fd4044056883548a0815b40cd2042098882341a4348d70d21a5a10414620870690d21ac348693841322084059a190b3c90208f9af8a5de57cbbfe29a283cb41e4240e107940e1e426821c2d0e14072a0384728e141a42c1cb610d11635610394827a4f46f8ef8a1a257c347e28e283c9c1e4212a107912a1e423821c270494027a0384278e140e42c09e61071161d61013c8)

def s1113 := certify 255 8 ([w58,w13,i2,i6,i7,i0,i1,i4,i5]) cs255 [] (u255 5 137 0x36d081014a40c52022960893a01dd017e40cf238e2a2924940878a0415015240c32000ba1740002e85d00298532aa924094100d8425280fd406a90334810348691040d21a44210c88f8af8a0f210790889a044d01d640eb2060e2507128288414420fa007d0281281070a19216102cc8689ecf73be2be283c841e4222681134075903ac8)

def s1114 := certify 255 7 ([w58,i2,i6,i7,i0,i1,i4,i5]) cs255 [] (u255 5 109 0xdb420405290314808a58224e8077405f9033c8e38a8a4925021e2810540549030c8002e85d0000ba17400a614caaa49025040361094a03f501aa40cd2040d21a44103486910843223e2be283c841e421c280e142c22c206f8af8a0f210790824a03850308b08)

def w253 : Sig := 0xfffffffffffffffff0f0f0f000000000fffffffffffffffff0f0f0f000000000

def s1115 := certify 255 5 ([w168,w253,w107,i7,i0,i1]) cs255 [] (u255 5 60 0x22f10a92c4294370b5b8924a04201b088e442a1b10a5fdc282e49204a34022b0281281024885c84298e34e34130309c10b938a2c428a710b14412dc)

def s1116 := certify 255 6 ([w253,i5,w107,i7,i0,i1,i4]) cs255 [s1115] (u255 5 84 0x5162145388508a0d6116770a7b8924a048bc42a4b10bc7151450dc2d6e49204a0806c223910a86c428530a65545fdc282e34127109a01158140940812442e4215a298194638d3836c4286710b144338e085c9c)

def w254 : Sig := 0xfffffffffffffffffffffffffffffffff0f0f0f000000000f0f0f0f000000000

def s1117 := certify 255 5 ([w168,w254,w107,i6,i0,i1]) cs255 [] (u255 5 60 0xa1b85adc45e21525885492502100d842fee141711c885436216490251c10b938d008ac0a04a0431c69c092217210ad049c422cee14f7228825885)

def s1118 := certify 255 6 ([w254,i5,w107,i6,i0,i1,i4]) cs255 [s1117] (u255 5 84 0x16770a7b81141ac251621453885492502286e16b738e2a2917885496216490250403610bfb8505c0a614caa91c885436215c10b938d049c42680456050250218e34e3450af2824885c8428a57173b91443085)

def w255 : Sig := 0xfafafafaaaaaaaaafafafafaaaaaaaaafafafafaaaaaaaaafafafafaaaaaaaaa

def s1119 := certify 255 5 ([w168,w255,w107,i6,i7,i1]) cs255 [] (u255 5 60 0x45e21525885286e16b70013611249409c10b938d008ac0092217210a638d39409408d049c424722150d8852fee141724902514588514e214b3b853dc)

def s1120 := certify 255 6 ([w255,i5,w107,i6,i7,i1,i4]) cs255 [s1119] (u255 5 84 0x14588514e214b3b853dc08a0d6124928122f10a92c4294370b5b9c71514009b08e085c9c6824e2134022b0024885c84298e34e3450af2a8128106d8850ce21452b8b9dc9240944722150d8852fee14170298532aa)

def w256 : Sig := 0xfcfcfcfcccccccccfcfcfcfcccccccccfcfcfcfcccccccccfcfcfcfccccccccc

def s1121 := certify 255 5 ([w168,w256,w107,i6,i7,i0]) cs255 [] (u255 5 60 0x4722150d8852fee14170403612490251c10b93940940812442e4214c71a71a011580d049c4245e21525885286e16b712494094588514e214b3b853dc)

def s1122 := certify 255 6 ([w256,i5,w107,i6,i7,i0,i4]) cs255 [s1121] (u255 5 84 0x14588514e214b3b853dc08a0d6149204a23910a86c4297f70a0b814c299550806c238217271a09388540940812442e4214c71a71a285794d008ac01b62143388514ae2e77124940917885496214a1b85adce38a8a)

def w257 : Sig := 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000

def s1123 := certify 255 6 ([w168,w257,w107,i6,i7,i0,i1]) cs255 [s1115,s1117,s1119,s1121] (u255 5 78 0x22f10a92c4294370b5b8004b26202492810806c223910a86c4297f70a0b8204b1ae249204a38217271a01158140940812442e4214c71a7227b41271082588514621425b81adc894588514e214b3b853dc)

def s1124 := certify 255 7 ([w257,i5,w107,i6,i7,i0,i1,i4]) cs255 [s1116,s1118,s1120,s1122,s1123] (u255 5 106 0x14588514e214b3b853dc08a316124928122f10a92c4294370b5b9c7151400c4c40924094100d844722150d8852fee14170298532aa1061ae238217271a093884d008ac0a04a04092217210a638d38d142bca5de36c4286710a295c5cee0c123708610a28c428ce06b722)

def w258 : Sig := 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000

def s1125 := certify 255 7 ([w258,i5,w107,i6,i7,i0,i1,i4]) cs255 [] (u255 5 109 0x14588514e214b3b853dc38f104b8924940917885496214a1b85adc36f11e18a4902504036111c885436214bfb8505c3e7116389c10b938d049c42680456050250204910b908531c69c6a29f713430d11a210a75e289c15710c118909e01e02612610610b3e4428ce10d70a)

def s1126 := certify 255 7 ([w168,i5,w107,i2,i6,i7,i0,i1]) cs255 [s1123] (u255 4 106 0x78c082c054a061a00114238002ec488252a088006e425301fb01aa819a8205f05e420d913a404a0945444019a0428851c30e7016a02584bb06b0ca20ea270091801490149024c019c1887234eb34bb3843045136112e0f75034d0a24f00ef017e819e8)

def s1127 := certify 255 7 ([w171,i5,w107,i2,i6,i7,i0,i1]) cs255 [] (u255 5 106 0x3c5020a80a9206190004508e071c5450806c2129407ea0354819a40817ee10298532aa210c8810a21470a0e39611145f1470048c0a04a0409286481841c4347142bca1b684080a5206290924a0524812849d00ee80bf20679010650ea10470c1096)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s1128 := certify 255 8 ([w107,i2,i6,i7,i0,i1,i4,i5]) cs255 [s1114,s1124,s1125,s1126,s1127] (u255 5 327 0x75ca1b6813d40eb93d81029015650a52038902ac388c520a20268411462ca09a4c5628208838449d027a810727a1dd009013610bf20289026c288cf20222a03829ee2a7aa28029479208049401409e08df803c501da81bf1da41500101be00a9203e9037c3e8c3200213f8000c17422a7f0ba11c60002840a754c14ca98aa84a829a4504902102526513f8820031c03fe31f60041079884a501de80f31de3f5011015a20d52282056d033481083fe20830690be7fc34dc30826441080b3432167920411f0d788a1a2f86f8a14650791832841ec20f21ec3a84304384610a813d10a3849e8e140642c19c209eb9613db081880e271c50d128388d115e51c505138e084a841444a8c108e083e9c7002f400fa2f4918070141d4084f44a0ffd021c26470494027a1904fc9039016613cc20e20599c71013c827a1ada)

def w259 : Sig := 0xf000f000f000f000f000f000f000f000f000f000f000f000f0f0f0f0f0f0f0f0

def s1129 := certify 255 8 ([w259,w13,i2,i6,i7,i0,i1,i4,i5]) cs255 [s1114] (u255 4 137 0xdb802180a540c5409561127807780bf40cf40390720ad5295043c6041602a5030d000ba174000ba174014c29a81582504a2a1000dc84a603f603550335040d21a4840d21a4888033403f503f507910791113811380eb40eb43942bd4e10c1138048c00a480a4812600ce0c43904f74e0d60fd40fd41e441e4444e044e03ad03ad06)

def w260 : Sig := 0xffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff0000ffff0000

def s1130 := certify 255 8 ([w260,w13,i4,i6,i7,i0,i1,i2,i5]) cs255 [] (u255 5 137 0x1b684080a5206291145f144d502a280b1207490307b0f630c1ec3d8dc71514004508e00f14082a02a4818643c000f3c000f0530a6554205fb84100d8425280fd406a903348984126984126210c8809a504d2883a041d0136409b2020e2507129a19a183e801f40a04a044ce8648043204a901444a8c1382694134a20e8107404d9026c8)

def w261 : Sig := 0xff000000ff000000ff000000ff000000ff000000ff000000ffff0000ffff0000

def s1131 := certify 255 8 ([w261,w13,i4,i6,i7,i0,i1,i2,i5]) cs255 [] (u255 5 137 0x1b684080a5206291145f144d502a280b1207490307b0f630c1ec3d8dc71514004508e00f14082a02a4818643c000f3c000f0530a6554205fb84100d8425280fd406a903348984126984126210c8809a504d2883a041d0136409b20e285794d0cd0c70048c0a04a0409286481841c41a70a2709509a504d2883a041d0136409b202)

def s1132 := certify 255 5 ([w34,w248,w113,w13,i6,i5]) cs255 [] (u255 5 60 0x294818a40db42040843220e28579461071073c48de092864834334371c1458c54902b484920909a6d9e8a228fd8b12056904d50090)

def s1133 := certify 255 6 ([w248,w113,i0,w13,i6,i2,i5]) cs255 [s1132,s1092] (u255 5 81 0x294818a40db4204228be2858903a4826a815140843220e285794d0cd0c61071070a3d8e39e246f04943240a46a51fbd860d630ad205691304804871c15f3c31d57854902b48492090)

def s1134 := certify 255 5 ([w34,w249,w113,w13,i6,i7]) cs255 [] (u255 4 60 0x110066809300670621c87091246245c215e2d1b461e301e70152815a8948458c4e89d06e2446dc010c052a062a09ac079c058a056a0118231111)

def s1135 := certify 255 6 ([w249,w113,i0,w13,i6,i7,i2]) cs255 [s1134,s1093] (u255 4 81 0x4d6054602c503a5008c1183f12200cd1a368c12600ce0c4390e1460ddce12248c48b842bc40dcc1acc3ce03ce02b502b50274454c444448b4d3aa24478c079c054a056a252103f1b70043014a818a8)

def s1136 := certify 255 6 ([w34,w250,w113,w13,i6,i7,i5]) cs255 [s1132,s1134] (u255 4 81 0x36e00860295031508803343942bd412600ce0c4390ef123f3841445a368c0e41ca8b18f180f380a940ad402704e0dfc250a310a01ae024051448a98844441182351fb26b01e70162815a8)

def s1137 := certify 255 7 ([w250,w113,i0,w13,i6,i7,i2,i5]) cs255 [s1133,s1135,s1136,s1094] (u255 4 106 0x1b70043014a818a804608c1fa89ac0a8c058a074a110066872857ab46d1824c019c188721c4c41bb9de247e708288948d547ec1b986b9879c079c056a056a01388a98888839072a07fe31d5f0f180f380a940ad409428c420ca1d442806b809014512)

def s1138 := certify 255 6 ([w34,w251,w113,w13,i6,i7,i5]) cs255 [] (u255 4 81 0x36e00860295031508803343942bd412600ce0c4390e9223968da349f9aa5280f394902b6409412a5f9081fa84280f380902b50270bd1788888454c1182351fb26b01e70162815a8)

def s1139 := certify 255 7 ([w251,w113,i0,w13,i6,i7,i2,i5]) cs255 [s1138,s1095] (u255 4 106 0x6dc010c052a062a01182307ea26b02a3016281d2844019a1ca15ead1b4609300670621c870a306ee74911c948d547ec1b98359879c079c056a056a012c9f9aa5228a6365280f394902b64207ea1083a86510a03ce0240ad409c2f44444422a7e)

def s1140 := certify 255 6 ([w246,w34,w113,i6,i7,i4,i5]) cs255 [] (u255 5 81 0x36d081014a40c52022960893a01dd017e40cf208432238e0a2c692413c3c5009280a920c200bae000bae00aa8aa825025024a0125030830818aa8aa825025024a01250308308)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s1141 := certify 255 7 ([w34,w113,w13,i6,i7,i4,i5]) cs255 [s1136,s1138,s1140] (u255 4 252 0xeba86dc0edc0eb9cf043054055a852a038a05587118a852026884a3b6a09a76eca108838893c0e7c0839cf0ef01404d885fa028a04d85119e812019a11016700662cc19c1080e2e72868a8388d115ea72828b9c212a20a22546089c2066e093009f006613c19c1d016613d8872059b9c809e80fae7005e803e8bd24607034ed18ff9b435f46719400720ffc0e55e503f016317a428c1210041afde1e601e301db01e63b479c01015a015280fa815a1f456a00806e021817901b82f05e60015a0460acc08d46502bd1fb118540f654c41ec5431111e6626b01cb01e639479c0d015a61628d2056e856a0c8)

def s1142 := certify 255 7 ([w34,i2,w113,w13,i6,i7,i4,i5]) cs255 [s1101] (u255 4 109 0x36e00860295031502558449e01de02fd033d08803343942bd4e10c1104980338310e438048c0e3fe1adce7d60ddc0e41ca81fca42f0f180f380a940ad4003482f01081a405c540fd419441d44e36044e0e2d03ad06523551fb115311111e701e7015a815a8)

def w262 : Sig := 0xffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaa

def s1143 := certify 255 7 ([w262,i4,w113,w13,i6,i7,i2,i5]) cs255 [] (u255 4 109 0xdb802180a540c540230460fd44d6054602c503a5019441d4460f61ecc8803343942bd5a368c12600ce0c4390e212323842544e12a0ddc0e41ca81f902f82f20f180f380a940ad40882f027213c2504d10a041e02409b4153523551fb1e701e7015a815a8)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s1144 := certify 255 8 ([w113,i0,w13,i6,i7,i2,i4,i5]) cs255 [s1137,s1139,s1141,s1142,s1143,s1096,s1104] (u255 4 327 0x1d750db81db81d739e0860a80ab50a5407140ab0e23150a404d109476d4134edd9421107112781cf810739e1de02809b10bf4051409b0a233d02403fd0235181183f303f56941e4c19441ec41e43d875118444cc4d60396044c7295181a03acc2c51a40ebd0e941900cd0880b380331660ce084071739434541c4688af5394145ce1095105112a3044e169da31ff36904e8ce30337049804f803309e0ce0e80b309ec43902cdce404f4037739f59333ca0dc99837266e707d73802f401f45e9230380a06ea0564cd1aa8eda8158373f6206e2a1332a623162a0372224cc1b8373133313326235cc0dcc3cc1b8f3813380f339e3ce00de02b6288ad403740ad06e2b504cd08951291400720ffc0e55e503f003f17a428c1210041afde19600182e8451961742398001e601e301db01e63b479c01015a015280fa815a1f456a008)

def s1145 := certify 255 5 ([w34,w248,i1,w13,i6,i5]) cs255 [] (u255 5 60 0x14a40c5206da10204219107142bca30838839e246f0494324289a89b8e2a28549030c84925107a6da60a614caa86a903348924090)

def s1146 := certify 255 6 ([w248,i0,i1,w13,i6,i2,i5]) cs255 [s1145] (u255 5 84 0x529031481b684084517c50b12074904d502a281086441c50af29a19a18c20e20e7891bd44d44c1250c90e38a8a7863aaf0a9206190924a2014c299554c306b986a90334899eda6924090)

def s1147 := certify 255 5 ([w34,w249,i1,w13,i6,i7]) cs255 [] (u255 5 60 0x4219101250c9030838838489231227042bc2a04ed027478a0415015240c3212494084889dd84e8db420405290314825280fd406a903348924094)

def s1148 := certify 255 6 ([w249,i0,i1,w13,i6,i7,i2]) cs255 [s1147] (u255 5 84 0x4d502a280b1207491145f04421910d0cd0c1250c903083883848923123409da04e9c10af0848b4d3aa24478a0415015240c3212494084eaff0d627494a03f501aa40cd204e891d84ec9204a0db4204052903148)

def s1149 := certify 255 6 ([w34,w250,i1,w13,i6,i7,i5]) cs255 [s1145,s1147] (u255 5 84 0x1b684080a52062904219107142bca09286481841c41cf12378e08288544d44dc715143c5020a80a9206190924a04f4db4c11428c20900d6804405122490250298532aa25280fd406a903348)

def s1150 := certify 255 7 ([w250,i0,i1,w13,i6,i7,i2,i5]) cs255 [s1146,s1148,s1149] (u255 5 112 0x1b684080a5206291145f144d502a280b12074904219107142bca68668609286481841c41cf1237a89a898e082885c71514f0c755e1e2810540549030c84925020a614caaa6186bcc4a501fa80d520669133db4d24812811428c208328750824035a01101448)

def s1151 := certify 255 7 ([w251,i0,i1,w13,i6,i7,i2,i5]) cs255 [] (u255 5 112 0xdb42040529031488a2f8a26a81514058903a48210c8838a15e534334304943240c20e20e4911a4749126449f9d4924514c6a49206fd24881be94911ca92444297e49101e724840ad9244b6902f8a0820ea19420901e680440ad202385e841246cd25240a4)

def s1152 := certify 255 7 ([w34,w113,i1,w13,i6,i7,i4,i5]) cs255 [s1149] (u255 4 109 0xdb802180a540c5409561127807780bf40cf42200cd0e50af5384304412600ce0c4390e17a2f5ce05e2f417e8da323d502b51b3150515606fe114d037d0018e606e652e15163125f106b1e701e7015a815a8210179811823502b1505426b01e70162815a8)

def s1153 := certify 255 8 ([w113,i0,i1,w13,i6,i7,i2,i4,i5]) cs255 [s1150,s1151,s1152] (u255 4 137 0x36e00860295031502558449e01de02fd033d008c1183f506510751135815180b140e942200cd0e50af53843045a368c12600ce0c4390e17a2f5ce4fe31dce17a2f5c8f540ad46cc5410cb30cb345581bf845340df40140ad40ac5415063986b9879c079c056a056a1128c706e4503f503f10a3106b196619661e701e7015a815a8)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s1154 := certify 255 8 ([w123,i0,w13,i6,i7,i2,i4,i5]) cs255 [s1105] (u255 4 327 0x1d750db83f781d77ea0860a80ab50a5407140ab0e23150a404d1094fdd4135fbd9421107112783f581077ea1de02809b10bf4051409b0a233d02403fd0235181183f303f56941e4c19441ec41e43d875118444cc4d60396044c7295181a03acc2c51a40ebd0e941900cd0880b380331660ce084071739434541c4688af5394145ce1095105112a3044e169da327f36835e8ce30337049804f803309e0ce0e80b309ec43902cdce404f40297029213320292660a48e207d73802f401f45e9230380a205305609c29a813a81590158813825a10128882a027a133210c1a42f9330d20bcc420f3212980ef80f31de3f60480ad20d5402940ad05233504402b00395781c82bf02b50154f484095014178432c00305d08a32c2e84730006fc03c603b606fc76905802037c02a501f5037c3e8c3401089499837)

def w263 : Sig := 0x50ff50ff50ff50ff50ff50ff50ff50ff50ff50ff50ff50ff5050505050505050

def s1155 := certify 255 6 ([w263,w34,i6,i7,i1,i4,i5]) cs255 [] (u255 5 84 0x6da1020294818a40452c1127403ba02fc819e471c5452492810f14082a02a48186400205d10843220298532aa92409425280fd406a9033482c652e129f88497c2b807de004941dea061077c8184b84)

def s1156 := certify 255 7 ([w61,w34,w13,i6,i7,i1,i4,i5]) cs255 [s1155] (u255 5 109 0x6da1020294818a40452c1127403ba02fc819e471c5452492810f14082a02a48186400205d10843220e2857947043042380246004943240c20e22812810eb835dc14c2995549204a129407ea0354819a4163297094fc424be15c03ef022da116507ca4457206)

def w264 : Sig := 0x5555000055550000555500005555000055550000555500005555000055550000

def s1157 := certify 255 7 ([w264,i4,w34,w13,i6,i7,i1,i5]) cs255 [] (u255 5 109 0x36d081014a40c5238e2a2878a0415015240c320008a11c036612f708843220e28579470048c009286481841c45135131c109508eb84adc14c29955129407ea0354819a449205304504d0824083a011026c8b8a9fa500f0171074083a026c8136407bb84114)

def s1158 := certify 255 7 ([w246,w34,i0,i6,i7,i1,i4,i5]) cs255 [s1098,s1140] (u255 4 103 0xdb802180a540c5409561127807780bf40cf40390720ad5295043c6041602a5030d000ba174000ba17408803342815a8b18a82a02f00a3004980498310c40290d6a056a0562a0a812601260c43106502b502b150540930093062188)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s1159 := certify 255 8 ([w34,i0,w13,i6,i7,i1,i4,i5]) cs255 [s1156,s1141,s1152,s1157,s1158,s1087] (u255 4 327 0x75d436e076e075ce782182a02ad429501c502ac388c542901344251db504d3b76508441c449e073e041ce787780a026c42fd0145026c288cf40900ac00e55e0720afc0ad40553d2102540505e11bf00f180ed81bf1da4160080df00a9407d40df0fa30d0040cb000c174228cb0ba11cc0003342202ce00cc5983382101c5ce50d150711a22bd4e5051738425441444a8c113841f5ce00bd007d17a48c0e00337049804f803309e0ce0e80b309ec43902cdce404f41337381793305e7fc999e505ee05fa768c7fcda317a338ca05ea0564cc15a8eda81582f2c622622a02fa08178a84ce84cc1782f013301331ae28c00bc03cc178f3813380f339e3ce00be02b4178ad413340ad7da2b500bd04cc35915a0460acc08d46502bd02b118540f74107b150d41e6626b01cb01e639479c0d015a61628d2056e856a0c8)

def s1160 := certify 255 8 ([w34,i0,i2,w13,i6,i7,i1,i4,i5]) cs255 [s1156,s1142,s1086,s1088,s1102] (u255 4 137 0xdb802180a540c5409561127807780bf40cf40390720ad5295043c6041602a5030d000ba174000ba17408803343942bd4e10c1138048c012600ce0c4390e3fe62dce0d24c434b89e8d77171503f50651075138d8113838b40eb41940ad40ac541503480518079c079c056a056a03586905e4502b502b150541e701e7015a815a8)

def s1161 := certify 255 7 ([w263,w61,i0,i6,i7,i1,i4,i5]) cs255 [s1155] (u255 5 106 0x6da1020294818a40452c1127403ba02fc819e471c5452492810f14082a02a4818641086440530a6555248128201b084a501fa80d5206691f15f14834241a105d002e8038501c2858458406b1be2be29068483420ba005d0024a03850308b08a04a04)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s1162 := certify 255 8 ([w61,i0,w13,i6,i7,i1,i4,i5]) cs255 [s1156,s1161] (u255 4 327 0x75d436e076e075ce782182a02ad429501c502ac388c542901344251db504d3b76508441c449e073e041ce787780a026c42fd0145026c288cf40900ac00e55e0720afc0ad40553d2102540505e11bf00f180ed81bf1da4160080df00a9407d40df0fa30d00403342202ce00cc5983382101c5ce50d150711a22bd4e5051738425441444a8c113841f5ce00bd007d17a48c0e00337049804f803309e0ce0e80b309ec43902cdce404f40297029213320292660a48e269da31ff36851e8ce328814c158270a6a04ea0564056204e0968404a220a809e84cc8400c7013318e0dc0420f3212980ef80f31de3f60480ad20d5402940ad05233504403fd0235181183f303f5694834c7ac41ec48343da691184174c114032c017465847018044cc4d60396044c7295181a03acc2c51a40ebd0e941901ac9982f)

def s1163 := certify 255 7 ([w263,i0,i2,i6,i7,i1,i4,i5]) cs255 [s1155] (u255 5 112 0x6da1020294818a40452c1127403ba02fc819e471c5452492810f14082a02a481864001742e804219105c4af8a0ca107509c6a0385071645840530a6555248128201b084a501fa80d5206690205f0d627c57c520d09068417400ba00494070a061161030cd1d4081a44)

def s1164 := certify 255 8 ([w61,i0,i2,w13,i6,i7,i1,i4,i5]) cs255 [s1156,s1163,s1103] (u255 4 137 0x36e00860295031502558449e01de02fd033d00e41c82b54a5410f1810580a940c34002e85d02200cd0e50af53843044e0123004980338310e438ff8d7702920292389e8a37171503f50651075138d8113838b40eb40530a6a056094128a840037212980fd80d540cd405f0d6407ea07ea41a241a20ba00ba0227022701d681d683069)

def s1165 := certify 255 8 ([w262,i0,i4,w13,i6,i7,i1,i2,i5]) cs255 [s1143] (u255 4 137 0xdb802180a540c540230460fd44d6054602c503a5019441d4460f61ecc0e41c82b5002284700f1810580a940c341b312f717800f2200cd0e50af568da338048c012600ce0c4390e1095138896c8e12a255c2504d10a041e02409b45140ad40ac817c1790800d641e701e7015a815a811146827502b502b1e701e7015a815a8)

def s1166 := certify 255 8 ([w264,i0,i4,w13,i6,i7,i1,i2,i5]) cs255 [s1157] (u255 5 137 0xdb42040529031488a2f8a26a81514058903a480ca10750b8e2a28008a11c01e2810540549030c836612f708843220e285794d0cd0c70048c009286481841c41c10950a89a898e12a254e08a09a1048107402204d9014c299554c306b9a60360094a03f501aa40cd2240a609a504d283d8c1ec601e01e20e8107404d9026c8504)

def s1167 := certify 255 8 ([w78,i1,i2,w13,i6,i7,i0,i4,i5]) cs255 [] (u255 4 137 0x36e00860295031502558449e01de02fd033d014c29a81582504a2a12980fd80d540cd410348692102e8c72103486922200cd0e50af538430440a480a4812600ce0c4390e4fe32dce0ba2f42eb85e8bd727d503f51eb107913fb811383f940eb41815a815aa82a08dfc0dfc06fa06fa06585d08e0056a056aa0a8237f037f01be81be8)

def w265 : Sig := 0x30ff30ff30ff30ff30ff30ff30ff30ff30ff30ff30ff30ff3030303030303030

def s1168 := certify 255 7 ([w265,i1,i2,i6,i7,i0,i4,i5]) cs255 [] (u255 5 112 0x6da1020294818a40452c1127403ba02fc819e40530a65552481284a501fa80d520669020690d220806c210864427d2be28f5841e427f680e141fc91611c71514924a043c5020a80a920619000453aa07c57c5079083c841a440d220494070a061161030cd1c7001740)

def w266 : Sig := 0x3030303030303030303030303030303030303030303030303030303030303030

def s1169 := certify 255 8 ([w266,i1,i2,w13,i6,i7,i0,i4,i5]) cs255 [s1168] (u255 4 137 0x36e00860295031502558449e01de02fd033d014c29a81582504a2a12980fd80d540cd4103486921000dc88803343942bd4e10c110292029204980338310e4393f8cb738048c0e27a1adc9f540fd47ac41e44fee044e0fe503ad00e41c82b54a5410f1810580a940c34045196007ea07ea0f220f220d240d24227022701d681d68305d)

def w267 : Sig := 0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc

def s1170 := certify 255 8 ([w267,i1,i4,w13,i6,i7,i0,i2,i5]) cs255 [] (u255 4 137 0xdb802180a540c540230460fd44d6054602c503a507ae89a6860f61ecc14c29a815902f82f212980fd80d540cd429da28da10031c809c8404e8803343942bd5a368c0a480a4812600ce0c4390ea051a3802f40e17a2f5d4504d552041e14409b40815a815a801142380dfc0dfc06fa06fa2805efe056a056a37f037f01be81be8)

def w268 : Sig := 0x3333000033330000333300003333000033330000333300003333000033330000

def s1171 := certify 255 8 ([w268,i1,i4,w13,i6,i7,i0,i2,i5]) cs255 [] (u255 4 137 0x36e008602950315008c1183f5135815180b140e941eba269a0530a6a05640be0bc84a603f6035503350a768a3684f03722200cd0e50af568da30292029204980338310e43a81468ef123f384a8957514135548107851026d00e41c82b578c757c3c6041602a5030d12a7826a826a83d983d98809c809c83c083c04da04da040)

def s1172 := certify 255 8 ([w124,i2,i6,w13,i7,i0,i1,i4,i5]) cs255 [] (u255 5 137 0x6da102050eb0e2515f7c50452c1127403ba010eb72e1041e43c85c71514924a043c5020a83951d6e4c75801742e80005d0ba00530a6555248128201b084a501fa83911d6e3c75881a4348820690d221c50af28e08608470048c0a04a0409286485961c3ada27ad1c13ce38278eb432408f8af8a0f210790889a044d01d6d0e91889a044d0)

def w269 : Sig := 0xff00ff00ff00fff0fff0fff0fff0ff00ff00ff00ff00fff0f0f0f0f0f0f0f0

def s1173 := certify 255 7 ([w269,i2,i6,i7,i0,i1,i4,i5]) cs255 [] (u255 5 112 0x6da1020294818a40452c1127403ba02fc819e471c5452492810f14082a02a481864001742e8014c2995549204a0806c2129407ea0354819a4081a43488421911f15f141e420f210e14070a02c48b08f8af8a0f21079082e8017400d220691024a03850308b0818668e)

def w270 : Sig := 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0

def s1174 := certify 255 8 ([w270,i2,i6,w13,i7,i0,i1,i4,i5]) cs255 [s1173] (u255 4 137 0x36e00860295031502558449e01de02fd033d00e41c82b54a5410f1810580a940c34002e85d00530a6a056094128a840037212980fd80d540cd4103486923942bd4e10c1138048c00a480a4812600ce0c4391a27ba72200cd00fd40fd41e441e4444e044e02c74807ea07ea0f220f220ba00ba00d240d2422702270326e0d6e1d66)

def w271 : Sig := 0xf0ff00fff0ff00fff0ff00fff0ff00fff0ff00fff0ff00fff0f00000f0f00000

def s1175 := certify 255 7 ([w271,i2,i4,i6,i7,i0,i1,i5]) cs255 [] (u255 4 112 0x6dc010c052a062a01c839056a1e3020b01528186894a82005d0ba0005d0ba00a614d40ac8006e425301fb01aa819a804a0945420690d2420690d2444019a04a09a224f00ef017e819e804608c1fa89ac0a8c058a074a0c20ea2307bd1826a826a824c133c18808680f221822)

def w272 : Sig := 0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000

def s1176 := certify 255 8 ([w272,i2,i4,w13,i6,i7,i0,i1,i5]) cs255 [s1175] (u255 4 137 0x36e00860295031500e41c82b50f1810580a940c344a541002e85d0002e85d00530a6a05640037212980fd80d540cd402504a2a10348692103486922200cd0e50af538048c00a480a4812600ce0c4390e10c1168da3389e86b7094134449e01de02fd033d008c1183f5135815180b140e941841d426a826aa2fc22fc22ea22ea03c87b)

def w273 : Sig := 0xfffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0

def s1177 := certify 255 8 ([w273,i2,i4,w13,i6,i7,i0,i1,i5]) cs255 [] (u255 5 137 0x36d081014a40c5238e2a2878a0415015240c32105a0b41a1e4008a11c078001e0a614caa840361094a03f501aa40cd218eb1d0f283440bf70930824c4219107142bca380246050250204943240c20e20e0f22543c9c1ed0387b384a8953a3094b14ffd020e83fd204d9017c57c51134089a03ac81d640790f61d46f8af8a22681134075903ac8)

def w274 : Sig := 0xfff0ff00fff0ff00fff0ff00fff0ff00fff0ff00fff0ff0000f0f00000f0f0

def s1178 := certify 255 7 ([w274,i2,i4,i6,i7,i0,i1,i5]) cs255 [] (u255 5 112 0x6da1020294818a471c5450f14082a02a48186424928100114238014c299550806c2129407ea0354819a449204a0817ee10843220228268449d00ee80bf206791f15f1438501c28584584065083d85f15f1470048c0a04a0409280e140c22c20e083c8430cd07b)

def w275 : Sig := 0xaaaafafaaaaafafaaaaafafaaaaafafaaaaafafaaaaafafaaaaafafaaaaafafa

def s1179 := certify 255 7 ([w275,i2,i4,w13,i6,i7,i1,i5]) cs255 [] (u255 4 112 0x6dc010c052a062a01c839056a1e3020b01528186894a82004508e044019a1ca15ea700918024c019c188721c21822707b40e1ec149014904a09a224f00ef017e819e82c6a5c2a8b708b307ca88ae80ca24be20a614d40ac8006e425301fb01aa819a804a09454205f05e4)

def w276 : Sig := 0xccccfcfcccccfcfcccccfcfcccccfcfcccccfcfcccccfcfcccccfcfcccccfcfc

def s1180 := certify 255 7 ([w276,i2,i4,w13,i6,i7,i0,i5]) cs255 [] (u255 4 112 0x6dc010c052a062a029853502b25301fb01aa819a804a09454205f05e42001b9110066872857a81490149024c019c188721c21822707b3aa1edc02460128268893c03bc05fa067a0f0a9d8aa81c280c21fa27fa03288c6881c839056a1e3020b01528186894a82004508e0)

def w277 : Sig := 0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0

def s1181 := certify 255 8 ([w277,i2,i4,w13,i6,i7,i0,i1,i5]) cs255 [s1178,s1179,s1180] (u255 5 137 0xdb4204052903148e38a8a1e2810540549030c8492502002284700298532aa100d8425280fd406a903348924094102fdc21086441c50af28e0091814094081250c9030838838218211c1ed0387b08a09a1127403ba02fc819e47c57c51134089a03ac81d640650f617c57c5225006b804cc414621134089a03ac81d6413d38359c1e46)

def w278 : Sig := 0xffffffff0f0f0000ffffffff0f0f0000ffffffff0f0f0000ffffffff0f0f0000

def s1182 := certify 255 7 ([w278,i2,i4,w13,i6,i7,i0,i1]) cs255 [] (u255 5 112 0x78a0415015240c32105a0b41a1e4035a1740e38a8a100d8425280fd406a90334863ac743ca0d10d686910298532aa210c88380246050250204943240c20e20e0f22543cb46b5a35a7142bca7fe810741fe9026c808258a26a81514058903a480ca1943c84b8a2f8a1b6810740529026c8)

def w279 : Sig := 0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000

def s1183 := certify 255 8 ([w279,i2,i4,w13,i6,i7,i0,i1,i5]) cs255 [s1182] (u255 4 137 0x36e00860295031500e41c82b50f1810580a940c3420b4168343c802e85d00530a6a05640037212980fd80d540cd431d63a1e506903486922200cd0e50af538048c00a480a4812600ce0c4390e0f22543ce8da3384a89574615594ffe041e0ff5026d008c1183f5135815180b140e940650f26292a0d6a005d005d2069206920f020f013681368107b)

def s1184 := certify 255 8 ([w17,i4,i6,w13,i7,i0,i1,i2,i5]) cs255 [] (u255 5 137 0x36d0810284dc6728a09a134a8a2f8a26a8151423289b8c626c60f61ec6183d87b1b8e2a28008a11c01e281054001361f4078001e78001e0a614caa840bf708201b084a501fa80826e81261049a610498e285794d0cd0c70048c0a04a040928648043136709b38d38c138279c704f136864810134a09a51074083a026c288cf0883a041d0)

def w280 : Sig := 0xffff0000ffff00000000000000000000ffff0000ffff0000

def s1185 := certify 255 8 ([w280,i4,i6,w13,i7,i0,i1,i2,i5]) cs255 [] (u255 5 137 0x1b684080a5206291145f144d502a280b1207490307b0f6371c5450011423803c5020a80a9206190f0003c14c299550817ee1040361094a03f501aa40cd22610498e285794d0cd0c70048c0a04a0409286481841c41c69c609c421910134a09a51074083a02fc2890134a09a507b183d8c03c03c24c24c41d020e84693a349c26c2)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s1186 := certify 255 9 ([w13,i6,i7,i0,i1,i2,i4,i5]) cs255 [s1089,s1097,s1112,s1113,s1128,s1129,s1130,s1131,s1144,s1153,s1154,s1159,s1160,s1162,s1164,s1165,s1166,s1167,s1169,s1170,s1171,s1172,s1174,s1176,s1177,s1181,s1183,s1184,s1185] (u255 4 448 0x29275d436ca4c0a4c0a49d7326084a4c1502922ad4294a4a038a0a48ab0e2314a4a14829213442292a292a292134a4d8a4a84232641c449cc9c0c9c0c99073261dcc9c05053226c42fe17a028a1ed89b0a233d4ca0482920ff408ca4a8c08ca483f303f292ad29ec87930657ae20f627aa1e43d8757a62308c9913313532701cb032644c7295132703414c8eb30b17a28d21b98ebd0e95328320a482b0039292af0392920afc0aca4a80a6e34f491288126df4051128bc26da32c0044a60ba1156f8cb0ba11d1298003266fc03c4c9c076c0c99bf1da414c9c01053237c02a512a03ea2288df0fa30d12a008292a20532920ac13853292a04ea2920ac80ad5888138252674202555e220899d013d156aab21099983485f552a443482f266621112a8f2109980638140a4718e0dd1280843263cc84a4c9c077c0c98f31de3f4c9c0905322b4835499a014a1f68ad05233499a0883260cd08327016702b60cc598333270420a4871738a4a868a8a48711a22bca4a9ca43e145ce27a212a24121444a8c127a2708f2e9da27a63166263a1afa27a67191287d7389e805e813f87d17a48d1281c02660a5c0a49e905190ff8290d60a49991c42b60cdc124c9c027c0ad83309e0ccadc1d02b62cc27b0c9a1c82b62cdce2b6809e8)

def s1187 := certify 255 8 ([w58,i2,w14,i6,i7,i0,i1,i4,i5]) cs255 [] (u255 6 134 0x532b028570e028570e02810a2c0813213e08150a008150a009c385428912280803254a0007cf80007cf80005cb80005cb80295214a922404502006c102321de1022850102285010268d010268d010832166adc43e14f857805e011a64394d0e534687293d34689e867c29f0af00bc021d3990e9c3874e38238715b)

def s1188 := certify 255 8 ([w129,i2,w13,i6,i7,i0,i1,i4,i5]) cs255 [] (u255 5 132 0x288985928a1d61c4a2bef8a08a5820889c730821d6e5c2083c8790b8e2a2924940a389138de44dca8eb7263ac00ba1740002e85d00298532aa924094100d848da44e359137223adc78eb10348691040d21a444075913c875907142bca38218211c012302812810708e1c889d961c3ada27ad1d417e2be283c841e4222791512a23ada1d23a46)

def w281 : Sig := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00fff0f0f0f0f0f0f0f0

def s1189 := certify 255 7 ([w281,i2,i6,i7,i0,i1,i4,i5]) cs255 [] (u255 5 112 0x6da1020294818a40452c1127403ba02fc819e471c5452492810f14082a02a481864001742e8014c2995549204a0806c2129407ea0354819a4081a43488421911f15f141e420f211354070a02c48b08f8af8a0f21079082e8017400d220691024a03850308b0818668e)

def w282 : Sig := 0xf0f0f0f0f0f0f0f0

def s1190 := certify 255 8 ([w282,i2,w13,i6,i7,i0,i1,i4,i5]) cs255 [s1189] (u255 5 132 0x1b684080a5206290114b0449d00ee80bf206791c71514924a043c5020a80a9206190005d0ba00530a6555248128201b084a501fa80d520669020690d221086441c50af28e08608470048c0a04a0409286481841c4344f5a3be2be283c841e4226a80e5405890d11f15f141e420f2105d002e801a440d221131d61ac6)

def s1191 := certify 255 7 ([w85,w124,w13,w14,i0,i1,i4,i5]) cs255 [] (u255 5 109 0x143ac389457df1457df14114b0410eb72e1041e43c8410790f2171c5452492813951d6e4c75801742e80005d0ba00530a6555248128201b08e4475b8f1d620690d22081a434887142bca38218211c012302812812c80271d41da09ed1c4103aca88c334add040748e9)

def s1192 := certify 255 8 ([w124,i2,w13,w14,i7,i0,i1,i4,i5]) cs255 [s1191] (u255 5 135 0x2b20b25143ac389457df14114b0416427c20875b970820f21e42e38a8a49250203254a03951d6e4c75801742e80005d0ba00530a6555248128201b082643bc47223adc78eb10348691040d21a4440e285794704304238024605025021c13f23ac689eb4704f38e09ff15f141e420f213542435b43ada1d23a46c859e4adc82075993)

def s1193 := certify 255 8 ([w85,i2,w13,w14,i6,i0,i1,i4,i5]) cs255 [s1191] (u255 6 135 0x2b870142889f01429f3e1408516040a850040889c73040bc7804e1c2a14489140403e7c011c489c6f22602e5c0002e5c014a90a549120228100360811428091b489c6b226134680813468082190b364adc70a15e287021820870024601404501270e1d38708e27a39470e9cc873e14f857805e01401803a8729131ca544a886204089a99)

def s1194 := certify 255 8 ([w15,i4,w13,i6,i7,i0,i1,i2,i5]) cs255 [] (u255 5 132 0x5107a2251426e3394504d09a54517c550f20f43483c6513718c4d8c1ec3d8c307b0f6371c545001142380010754a00026c3e80f0003cf0003c14c299550817ee10403610420e3bc4104dd024c20934c20932026c83e426c838a15e53433431c01230281281133907c883843136709b38d38c13a8584d28269441f20ee1dc4d85119e33c2)

def w283 : Sig := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ffffff0000ffff0000

def s1195 := certify 255 7 ([w283,i4,i6,i7,i0,i1,i2,i5]) cs255 [] (u255 5 112 0xdb42040529031488a2f8a26a81514058903a48183d87b1b8e2a28008a11c01e2810540549030c878001e0a614caa840bf708201b084a501fa80d520669130824c421910134a09a5127430405f90264809a504d283d8c1ec601e01e126126092810740c204d90104304e)

def w284 : Sig := 0xffff0000ffff0000

def s1196 := certify 255 8 ([w284,i4,w13,i6,i7,i0,i1,i2,i5]) cs255 [s1195] (u255 5 132 0x1b684080a5206291145f144d502a280b1207490307b0f6371c5450011423803c5020a80a9206190f0003c14c299550817ee1040361094a03f501aa40cd22610498843220e285794d0cd0c70048c0a04a0409286481841c41c69c609c134a09a5127404fa02fc80a2404d2826941ec60f6300f00f0930931071361ac2)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s1197 := certify 255 9 ([w13,w14,i6,i7,i0,i1,i2,i4,i5]) cs255 [s1187,s1188,s1190,s1192,s1193,s1194,s1196] (u255 5 402 0x17c9456452725f264c2ce4514c84a28598710e2c8438871166514524a28a48710e252438871292514134208a292504d292b14104bc420b232792f132627f208263e1042cc2885163e144288b308227a104824288513ca1442893d082f9a88a1a2f86f8a68a0f23065083d841e43d87508608c98c364397231639472e430c4f461859b4d13169a16630c4f46186bb4d0a369a27a30d501c14f7153d514014a3c904024a00a04f0432c00060ba1146585d08e3000399000c876e4e6476aa5c80009e8000b30fa1f53f87d0fa2cc0009e8002250fa1f53f87d0fa894000a1029d530532a62aa12a0a69141240840949943fe20830690be7fc34dc308227f1040063807fc63ec0082193104c877e47fc778efc84109e8820b3a283ff4502cc4109e882133a283ff4504cc410c9a9943232792991662ccc999356e64cc9901c4e38a1a250711a22bca38a0a271c1095082889518211c134734313d19a0d6d0c70c1f4e38017a007d17a48c0380a0ea0427a2507fe810e13238e53213c27e413f22b671c2cc2784f32671c2cce38ad84f09e56cad9c1)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s1198 := certify 255 10 ([w14,i6,i7,i0,i1,i2,i3,i4,i5]) cs255 [s1186,s1197] (u255 5 548 0x5657c945159c8ace45657c9a50b2567228a2b2c84a28ac8b30e21c4acb210e21c4ac8b328a2b2564a28ac9690e21c4ac9590e21c4ac96928a2b2134208ac94564a2b2134acac564a08230abc4208c2e4617230abc4d289f30b904118563e104614598510a26158f8510a26145984118530a104614cf8510a2614c28510a2614cf84115930670832b250d128ac9831a24fcac947146147b9da185084a846147b89511261423822b656ce38ade413f22b656c2784f2b791c715b2b613c2795b16671c56cad9c715b16613c2795b2b628c3595b38271c56cad9c715b38256ce0959f9a88ac94344567e1be2b253451850f2306530a107b08c28790f61d4c28430456cad8c315b387f8412b672c7ff456ce18639672c618e5e4397239672c728e539790c31cb39630c72c59b4d1cb396d3472c598c31cb39630c72cfbb4d1cb396d3472cfb8c3159a80e0ac94f70566a7aa2b2500518551e48c284024615401430a13c115b17a00056ce242154ad8bd24215cad9c00072c658001cb182e84539632c2e847396300020373200080f21db92037323b552a03c800101a030004062cc3e87d40680c3e87d4062cc00101a0300040689c3e87d40680c3e87d40689c000ac9420532b354c14cac95314566a12a30a14d218550490c28420461549942b656c410ad9c4243795b402427c2b670821cb39620872c60d217ce5a010d371cb1841101a0310440600c70101a0118fb2030041100a0110440390efc900a011de3bd00e42088050088220116745080500d142011662088050088220147f45080500d1420147e208694b0b9b092697234b91a57362cc599a534a6955b9a55d6694c)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s1199 := certify 255 10 ([w73,i6,i7,i0,i1,i2,i3,i4,i5]) cs255 [] (u255 6 548 0x2c2a0c50a2c320b0c82c2a0cd2982c32050a2c2c8450a2c22cf8702c2c878702c22cc50a2c3301022c228b08a2c330b0962c22810232a99c10232b20cac832a99cd2b032b2010232ac7c10232a2ce85032ac7e85032a2cc1022c260c70832c228688a2c260c6893f2c22870a32a3dc73432a084a8232a3dc4a88932a087023767bc710377227103767be71ef377207483766ee74e3762cc70e3766ec70e3762ce74e2c2f8d222c2283222c2f833e2c228d0a32be036432a0bd0232be3d7432a083023766ec306376387fc03767747fba376383063ba38430853bb20728853ba384728e13bb203483ba7743063ba2ccd1a3ba774d1a3ba2cc3062c2a80382c228f382c2a8f2a2c22800a32a50f1232a0801232a5001432a08f023762f40003763890d43762f490d6376380003ba32c0003ba1ae443ba32ee463ba1800040a52c011d40b207691d40a52c7694b40b2004840a81400040a2cfe7c40a817e7c40a2cc0002c2282522c2a93522c22930a2c2a822a32a0932432a5022432a0820232a513143766ec2043763884ee37684c84bc376382043ba7742043ba1b45e3ba84f42e3ba1820440a81420440a00638040a84c63b640a0020442720212542652c779254272077c842652c214b42684c2044262cd42842684d4284262cc20434a694d297b34ae6c598b334b20d2c82c3c0b4f02c228b08a2c3c0b0f02c228b48a32b40cfd032a08ca8232b40cad032a08cf8237638e08e37738ddce37638dd8e37738e0ce3ba68fb9a3ba18ee863ba68ee9a3ba18fb8640bf113fc40a01028040bf102fc40a011380426a11fa8426110984426a109a8426111f8434ae6cacb234a695768c)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s1200 := certify 255 11 (roots 255) cs255 [s755,s1085,s1198,s1199] (u255 6 448 0x34ac8617b263205997b1aec859b234b2060c2d2a0c50a2d320b4c82d2a0c51982d32050a2d38050a2d23380c2d38380872d23050a33e99c10233f20cfc833e99f53033f2010233f0810233e3280c33f0a809933e301022d3301022d228b48a2d330b4962d2281023827bc710383227103827be71ef3832074838222e7083823070838222c708b3823270c2d260c70832d228688a2d260c6893f2d22870a33e3dc73433e084a8233e3dc4a88933e087023ee38430853ef20728853ee384728e13ef203483eeb031c3ee30d1c3eeb0d2c3ee3030c2d2f8d222d2283222d2f833e2d228d0a33fe036433e0bd0233fe3d7433e08302382704306382387fc03827dc7fba3823830644e52c011d44f207691d44e52c7694b44f2004844e23400b944e33e0c44e237e0c944e3000c2d2a80382d228f382d2a8f2a2d22800a33e50f1233e0801233e5001433e08f023822f40003823890d43822f490d6382380003ee32c0003ee1ae443ee32ee463ee1800047f20212547e52c7792547f2077c847e52c214b47e3026247eb146247e3140c47eb022c2d2282522d2a93522d22930a2d2a822a33e0932433e5022433e0820233e513143827042043823884ee3828fc84bc382382043ee7dc2043ee1b45e3ee8ff42e3ee1820444e89c20444e00638044e8fc63b644e00204)

theorem lower255 : Claim 255 12 := fromSearch 25924 (by decide +kernel) s1200.property

open PEqualNP.CircuitLowerBounds

def graph : Sig := goalAt 255
theorem graph_proper : proper graph := by unfold proper; decide +kernel

def edgeList : List Nat := [0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 6, 7]
def target (x : Fin 8 → Bool) : Bool :=
  decide (∃ i < edgeList.length / 2,
    (List.ofFn x).getD (edgeList.getD (2*i) 0) false = true ∧
    (List.ofFn x).getD (edgeList.getD (2*i+1) 0) false = true)

-- Four conjunctions cover the posted edges.
def smallCircuit : Circuit := ⟨[⟨.or,[0,1]⟩, ⟨.or,[0,2]⟩, ⟨.or,[3,9]⟩, ⟨.or,[4,5]⟩, ⟨.or,[6,7]⟩, ⟨.or,[7,11]⟩, ⟨.and,[8,13]⟩, ⟨.and,[2,5]⟩, ⟨.and,[10,12]⟩, ⟨.and,[6,7]⟩, ⟨.or,[14,15]⟩, ⟨.or,[18,16]⟩, ⟨.or,[19,17]⟩],20⟩

theorem witnessMonotone : ∀ g ∈ smallCircuit.gates,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [smallCircuit,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ⟨Or.inl rfl,by decide⟩ | exact ⟨Or.inr rfl,by decide⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem witnessCorrect : ∀ x : Fin 8 → Bool, smallCircuit.eval (List.ofFn x) = target x := by
  decide +kernel

theorem witnessSize : smallCircuit.gates.length = 13 := rfl

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
    (lower : Impossible true graph 11 eightInputs.toFinset) (gates : List Gate) (o : Nat)
    (fit : ∀ g ∈ gates, (g.op=GateOp.and ∨ g.op=GateOp.or ∨ g.op=GateOp.not) ∧ g.inputs.length≤2)
    (correct : ∀ x : Fin 8 → Bool, (Circuit.mk gates o).eval (List.ofFn x)=target x) :
    ∃ (gs : List Gate) (out : Nat), (∀ g ∈ gs, (g.op=GateOp.and ∨ g.op=GateOp.or) ∧ g.inputs.length≤2) ∧
       gs.length≤gates.length ∧ ∀ x : Fin 8 → Bool, (Circuit.mk gs out).eval (List.ofFn x)=target x := by
  classical
  by_cases big : 13 ≤ gates.length
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



-- Apply the full eight-input lower bound to the initial wire bank.
theorem lowerGraph : Impossible true graph 11 eightInputs.toFinset :=
  (ruleFor 255 lower255 none (by decide +kernel)).property 11 eightInputs
    (by decide +kernel) (by decide +kernel)


end PEqualNP.Outside.L_meta_29152

open PEqualNP.Outside.L_meta_29152 in
theorem PEqualNP.Outside.L_meta_29152 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o fit _ correct
  exact replaceShort lowerGraph gates o fit correct

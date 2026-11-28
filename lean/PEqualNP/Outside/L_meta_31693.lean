import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_31693

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
  (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 2 &&& x 5) ||| (x 0 &&& x 6) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 0 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)

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



def cuts193 : Cuts (goalAt 193) := []

def state193_0 : List Sig := roots 193
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude193_0 : Impossible true (goalAt 193) 3 state193_0.toFinset :=
  node_ok cuts193 [] 0x30100410130000810130200c00030100c08030100810110404410120404414020400c04020600810020404818020404c04010500414010404818010400c08010500410010404414010404c080206008180 (by decide +kernel)

theorem lower193 : Claim 193 4 :=
  fromSearch 6 (by decide +kernel) exclude193_0

theorem lower209 : Claim 209 5 :=
  fromLift 5 16 4 lower193 (by decide +kernel)


def cuts200 : Cuts (goalAt 200) := []

def state200_0 : List Sig := roots 200
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude200_0 : Impossible true (goalAt 200) 3 state200_0.toFinset :=
  node_ok cuts200 [] 0x30100480830000880830200c00030100c08030100880812020480822020484022000c04022200880022020888022020c04012100484012020888012000c08012100480012020484012020c080222008880 (by decide +kernel)

theorem lower200 : Claim 200 4 :=
  fromSearch 855662592 (by decide +kernel) exclude200_0

theorem lower216 : Claim 216 5 :=
  fromLift 5 16 856121344 lower200 (by decide +kernel)


theorem lower201 : Claim 201 5 :=
  fromLift 5 1 24582 lower200 (by decide +kernel)


def cuts145 : Cuts (goalAt 145) := []

def state145_0 : List Sig := roots 145
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude145_0 : Impossible true (goalAt 145) 3 state145_0.toFinset :=
  node_ok cuts145 [] 0x240401101240008101242009000240409080240408101044041101204041110204009010206008100204048180204049010044401110044048180044009080044401100044041110044049080206008180 (by decide +kernel)

theorem lower145 : Claim 145 4 :=
  fromSearch 4 (by decide +kernel) exclude145_0

theorem lower153 : Claim 153 5 :=
  fromLift 5 8 28676 lower145 (by decide +kernel)


def rule217_0 : {c : Cut // CutGood (goalAt 217) c} :=
  ruleFor 217 lower209 none (by decide +kernel)

def rule217_1 : {c : Cut // CutGood (goalAt 217) c} :=
  ruleFor 217 lower216 none (by decide +kernel)

def rule217_2 : {c : Cut // CutGood (goalAt 217) c} :=
  ruleFor 217 lower201 none (by decide +kernel)

def rule217_3 : {c : Cut // CutGood (goalAt 217) c} :=
  ruleFor 217 lower153 none (by decide +kernel)

def cuts217 : Cuts (goalAt 217) := [rule217_0,rule217_1,rule217_2,rule217_3]

def state217_0 : List Sig := roots 217
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude217_0 : Impossible true (goalAt 217) 6 state217_0.toFinset :=
  node_ok cuts217 [] 0x4000cc04010404c0004000c810130200c0004000cc04030200c0404000c81011040441014000890100440490004000881012420090004000890102420090104000881010440411014000c58180440411014000c41014000c41014000c58184000c48184000c41010440411014000088081210088004000081012220088004000088082220088084000081011210081014000c48082220048004000c41011210048004000c48081210048084000c41012220041014000819091210019014000811011614011014000819091614011094000811011210011014000481010444081004000488082060081004000481012060081014000488080444088084000c41010444041004000c48081050041004000c41011050041014000c4808044404808400081101105001100400089080044401100400081101044401101400089080105004140400010000044401110400004840064601910400010001064601118400004840044401110 (by decide +kernel)

theorem lower217 : Claim 217 7 :=
  fromSearch 24580 (by decide +kernel) exclude217_0

theorem lower197 : Claim 197 5 :=
  fromLift 5 4 1542 lower193 (by decide +kernel)


def cuts85 : Cuts (goalAt 85) := []

def state85_0 : List Sig := roots 85
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude85_0 : Impossible true (goalAt 85) 3 state85_0.toFinset :=
  node_ok cuts85 [] 0x44044101110501101110004400110104101054041101044141101104004100104044404044001100044044140044401510044501110 (by decide +kernel)

theorem lower85 : Claim 85 4 :=
  fromSearch 1540 (by decide +kernel) exclude85_0

def cuts212 : Cuts (goalAt 212) := []

def state212_0 : List Sig := roots 212
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude212_0 : Impossible true (goalAt 212) 3 state212_0.toFinset :=
  node_ok cuts212 [] 0x30000c00030100440424000900024040c04015010440411050440425040901024050901011000440011010c080111005440111404440 (by decide +kernel)

theorem lower212 : Claim 212 4 :=
  fromSearch 1107756544 (by decide +kernel) exclude212_0

def rule213_0 : {c : Cut // CutGood (goalAt 213) c} :=
  ruleFor 213 lower209 none (by decide +kernel)

def rule213_1 : {c : Cut // CutGood (goalAt 213) c} :=
  ruleFor 213 lower145 none (by decide +kernel)

def rule213_2 : {c : Cut // CutGood (goalAt 213) c} :=
  ruleFor 213 lower197 (some (3,input 0,input 2)) (by decide +kernel)

def rule213_3 : {c : Cut // CutGood (goalAt 213) c} :=
  ruleFor 213 lower197 (some (1,input 0,input 2)) (by decide +kernel)

def rule213_4 : {c : Cut // CutGood (goalAt 213) c} :=
  ruleFor 213 lower197 none (by decide +kernel)

def rule213_5 : {c : Cut // CutGood (goalAt 213) c} :=
  ruleFor 213 lower85 none (by decide +kernel)

def rule213_6 : {c : Cut // CutGood (goalAt 213) c} :=
  ruleFor 213 lower212 none (by decide +kernel)

def rule213_7 : {c : Cut // CutGood (goalAt 213) c} :=
  ruleFor 213 lower197 (some (2,input 2,input 7)) (by decide +kernel)

def rule213_8 : {c : Cut // CutGood (goalAt 213) c} :=
  ruleFor 213 lower197 (some (1,input 2,input 7)) (by decide +kernel)

def cuts213 : Cuts (goalAt 213) := [rule213_0,rule213_1,rule213_2,rule213_3,rule213_4,rule213_5,rule213_6,rule213_7,rule213_8]

def state213_0 : List Sig := [0xfffffffffffffffffffffffffffffffffafafafafafafafafafafafafafafafa,input 7,input 0,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude213_0 : Impossible true (goalAt 213) 4 state213_0.toFinset :=
  node_ok cuts213 [] 0x104048101112004101110004400104050001044044101110501101044048101240501101151001101044044440104044104104044401044041104044048180204048104204041114044409010 (by decide +kernel)

def state213_1 : List Sig := [0xfafafafafafafafafafafafafafafafa,input 7,input 0,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude213_1 : Impossible true (goalAt 213) 4 state213_1.toFinset :=
  node_ok cuts213 [] 0xc00030000c040104041101104044414044049000240009010044044101104104101110041101044101101206008100204008180240404400110004101302001101151001101111001110044401114111008101 (by decide +kernel)

def state213_2 : List Sig := [0xfafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafa,input 0,input 4,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude213_2 : Impossible true (goalAt 213) 5 state213_2.toFinset :=
  node_ok cuts213 [⟨state213_0,exclude213_0⟩,⟨state213_1,exclude213_1⟩] 0xc04010404c00020404c08030000c04030200c04020404410110404901004404900020404908024000901024200901020404110104404541404404110110405000310404541440004441410404110104404810104450810124040818420410810120610810124040111424040410104450410111011000110410410140004410111010111411004110120610110124200111404410110104450110124200818424201000240000111020404444020404901080004901020406000020404901011100901010405000111000c08011100440010404444010404c08040004c080044044440044049080151405440044045450044049080111004440 (by decide +kernel)

def state213_3 : List Sig := [0xffff0000ffff0000ffff0000ffff0000aaaa0000aaaa0000aaaa0000aaaa,input 0,input 7,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude213_3 : Impossible true (goalAt 213) 4 state213_3.toFinset :=
  node_ok cuts213 [] 0x340009000241009000110004400110104101250009000240109000044005100104041100044001500044101100044009000204041100044044404104041101044041105054041101044049000204049000105001100044041100 (by decide +kernel)

def state213_4 : List Sig := [0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 0,input 7,input 2,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude213_4 : Impossible true (goalAt 213) 5 state213_4.toFinset :=
  node_ok cuts213 [⟨state213_0,exclude213_0⟩,⟨state213_3,exclude213_3⟩] 0x410120404c080104044404104044101110101101104044414044041101204049080044060001044041101400104400110004404104041501044041105044048501204048105204044440400020000111009010104044404104044404044049080044048180206004440206104440204048180400141110 (by decide +kernel)

def state213_5 : List Sig := [0x5555555555555555555555555555555550505050505050505050505050505050,input 0,input 7,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude213_5 : Impossible true (goalAt 213) 4 state213_5.toFinset :=
  node_ok cuts213 [] 0x4101204044480104041101104044414044041101204049014044044100104004101110101100044001101105008100204008101044404400110004404104044440044044450044049010204049014204041114 (by decide +kernel)

def state213_6 : List Sig := [0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 7,input 0,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude213_6 : Impossible true (goalAt 213) 5 state213_6.toFinset :=
  node_ok cuts213 [⟨state213_0,exclude213_0⟩,⟨state213_5,exclude213_5⟩] 0x1000110404410120414c080300110001302004480204144101104044440104044400400044404110004440110104404400044101104045414044041101104050008104045414400044414104041101044049014044041101204149080240109014242009014204141101044045450044041101111001505054045450054141105111001101044044101044404100110104140104004101105004101110101110110101101105001100242001110044001101044401101242004140105008105044408104240508180204108105206008105240501110044420001044401110111001514054420000054501114111001110044410007400008101 (by decide +kernel)

def state213_7 : List Sig := roots 213
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude213_7 : Impossible true (goalAt 213) 6 state213_7.toFinset :=
  node_ok cuts213 [⟨state213_2,exclude213_2⟩,⟨state213_4,exclude213_4⟩,⟨state213_6,exclude213_6⟩] 0x40004c04010404c00040004810130200c00040004c04030200c040400048101104044101400109010044049000400108101242009000400109010242009010400108101044041101400105414044041101400104101400104101400105414400044414400104101044041101400008505111008501400008101400008101400008505800088105400008101111008101400004404400044400400004101111004400400004404111004404400004101400004101400101505111001501400101101151401101400101505151401105400101101111001101400148101044408100400189010206008100800048101206008101400149010044401110400044101044404100400044404105004100400044101105004101400044404044404404400101101105001100400109080044401100400101101044401101400109080105004140400010000044401110400004440054501510400020000054501114400004440044401110 (by decide +kernel)

theorem lower213 : Claim 213 7 :=
  fromSearch 1540 (by decide +kernel) exclude213_7

theorem lower204 : Claim 204 5 :=
  fromLift 5 4 838886912 lower200 (by decide +kernel)


theorem lower205 : Claim 205 6 :=
  fromLift 6 1 26118 lower204 (by decide +kernel)


def cuts89 : Cuts (goalAt 89) := []

def state89_0 : List Sig := roots 89
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude89_0 : Impossible true (goalAt 89) 3 state89_0.toFinset :=
  node_ok cuts89 [] 0x44044101120601101120004800120204101064041101044241101104004100104044808044001100044044140044401910044601110 (by decide +kernel)

theorem lower89 : Claim 89 4 :=
  fromSearch 24580 (by decide +kernel) exclude89_0

theorem lower220 : Claim 220 6 :=
  fromLift 6 4 839345664 lower216 (by decide +kernel)


theorem lower93 : Claim 93 5 :=
  fromLift 5 4 26116 lower89 (by decide +kernel)


def rule221_0 : {c : Cut // CutGood (goalAt 221) c} :=
  ruleFor 221 lower217 none (by decide +kernel)

def rule221_1 : {c : Cut // CutGood (goalAt 221) c} :=
  ruleFor 221 lower213 (some (1,input 0,input 2)) (by decide +kernel)

def rule221_2 : {c : Cut // CutGood (goalAt 221) c} :=
  ruleFor 221 lower205 (some (1,input 0,input 2)) (by decide +kernel)

def rule221_3 : {c : Cut // CutGood (goalAt 221) c} :=
  ruleFor 221 lower204 none (by decide +kernel)

def rule221_4 : {c : Cut // CutGood (goalAt 221) c} :=
  ruleFor 221 lower153 none (by decide +kernel)

def rule221_5 : {c : Cut // CutGood (goalAt 221) c} :=
  ruleFor 221 lower216 none (by decide +kernel)

def rule221_6 : {c : Cut // CutGood (goalAt 221) c} :=
  ruleFor 221 lower217 (some (2,input 0,input 7)) (by decide +kernel)

def rule221_7 : {c : Cut // CutGood (goalAt 221) c} :=
  ruleFor 221 lower89 none (by decide +kernel)

def rule221_8 : {c : Cut // CutGood (goalAt 221) c} :=
  ruleFor 221 lower217 (some (3,input 0,input 7)) (by decide +kernel)

def rule221_9 : {c : Cut // CutGood (goalAt 221) c} :=
  ruleFor 221 lower220 (some (1,input 2,input 7)) (by decide +kernel)

def rule221_10 : {c : Cut // CutGood (goalAt 221) c} :=
  ruleFor 221 lower204 (some (1,input 2,input 7)) (by decide +kernel)

def rule221_11 : {c : Cut // CutGood (goalAt 221) c} :=
  ruleFor 221 lower213 (some (3,input 0,input 2)) (by decide +kernel)

def rule221_12 : {c : Cut // CutGood (goalAt 221) c} :=
  ruleFor 221 lower220 none (by decide +kernel)

def rule221_13 : {c : Cut // CutGood (goalAt 221) c} :=
  ruleFor 221 lower217 (some (2,input 0,input 6)) (by decide +kernel)

def rule221_14 : {c : Cut // CutGood (goalAt 221) c} :=
  ruleFor 221 lower217 (some (1,input 0,input 6)) (by decide +kernel)

def rule221_15 : {c : Cut // CutGood (goalAt 221) c} :=
  ruleFor 221 lower145 none (by decide +kernel)

def rule221_16 : {c : Cut // CutGood (goalAt 221) c} :=
  ruleFor 221 lower216 (some (1,input 4,input 6)) (by decide +kernel)

def rule221_17 : {c : Cut // CutGood (goalAt 221) c} :=
  ruleFor 221 lower217 (some (2,input 4,input 6)) (by decide +kernel)

def rule221_18 : {c : Cut // CutGood (goalAt 221) c} :=
  ruleFor 221 lower220 (some (1,input 4,input 6)) (by decide +kernel)

def rule221_19 : {c : Cut // CutGood (goalAt 221) c} :=
  ruleFor 221 lower217 (some (1,input 4,input 6)) (by decide +kernel)

def rule221_20 : {c : Cut // CutGood (goalAt 221) c} :=
  ruleFor 221 lower213 none (by decide +kernel)

def rule221_21 : {c : Cut // CutGood (goalAt 221) c} :=
  ruleFor 221 lower205 (some (1,input 0,input 3)) (by decide +kernel)

def rule221_22 : {c : Cut // CutGood (goalAt 221) c} :=
  ruleFor 221 lower153 (some (1,input 0,input 3)) (by decide +kernel)

def rule221_23 : {c : Cut // CutGood (goalAt 221) c} :=
  ruleFor 221 lower213 (some (3,input 0,input 6)) (by decide +kernel)

def rule221_24 : {c : Cut // CutGood (goalAt 221) c} :=
  ruleFor 221 lower217 (some (1,input 0,input 3)) (by decide +kernel)

def rule221_25 : {c : Cut // CutGood (goalAt 221) c} :=
  ruleFor 221 lower212 none (by decide +kernel)

def rule221_26 : {c : Cut // CutGood (goalAt 221) c} :=
  ruleFor 221 lower213 (some (3,input 0,input 7)) (by decide +kernel)

def rule221_27 : {c : Cut // CutGood (goalAt 221) c} :=
  ruleFor 221 lower213 (some (1,input 0,input 7)) (by decide +kernel)

def rule221_28 : {c : Cut // CutGood (goalAt 221) c} :=
  ruleFor 221 lower213 (some (2,input 0,input 6)) (by decide +kernel)

def rule221_29 : {c : Cut // CutGood (goalAt 221) c} :=
  ruleFor 221 lower213 (some (2,input 0,input 7)) (by decide +kernel)

def rule221_30 : {c : Cut // CutGood (goalAt 221) c} :=
  ruleFor 221 lower220 (some (2,input 2,input 7)) (by decide +kernel)

def rule221_31 : {c : Cut // CutGood (goalAt 221) c} :=
  ruleFor 221 lower197 (some (1,input 2,input 7)) (by decide +kernel)

def rule221_32 : {c : Cut // CutGood (goalAt 221) c} :=
  ruleFor 221 lower209 none (by decide +kernel)

def rule221_33 : {c : Cut // CutGood (goalAt 221) c} :=
  ruleFor 221 lower197 (some (1,input 0,input 2)) (by decide +kernel)

def rule221_34 : {c : Cut // CutGood (goalAt 221) c} :=
  ruleFor 221 lower197 (some (3,input 2,input 6)) (by decide +kernel)

def rule221_35 : {c : Cut // CutGood (goalAt 221) c} :=
  ruleFor 221 lower204 (some (1,input 2,input 3)) (by decide +kernel)

def rule221_36 : {c : Cut // CutGood (goalAt 221) c} :=
  ruleFor 221 lower220 (some (1,input 2,input 3)) (by decide +kernel)

def rule221_37 : {c : Cut // CutGood (goalAt 221) c} :=
  ruleFor 221 lower209 (some (1,input 4,input 6)) (by decide +kernel)

def rule221_38 : {c : Cut // CutGood (goalAt 221) c} :=
  ruleFor 221 lower213 (some (0,input 2,input 6)) (by decide +kernel)

def rule221_39 : {c : Cut // CutGood (goalAt 221) c} :=
  ruleFor 221 lower220 (some (3,input 2,input 6)) (by decide +kernel)

def rule221_40 : {c : Cut // CutGood (goalAt 221) c} :=
  ruleFor 221 lower213 (some (3,input 2,input 6)) (by decide +kernel)

def rule221_41 : {c : Cut // CutGood (goalAt 221) c} :=
  ruleFor 221 lower213 (some (2,input 2,input 7)) (by decide +kernel)

def rule221_42 : {c : Cut // CutGood (goalAt 221) c} :=
  ruleFor 221 lower213 (some (1,input 2,input 7)) (by decide +kernel)

def rule221_43 : {c : Cut // CutGood (goalAt 221) c} :=
  ruleFor 221 lower213 (some (2,input 4,input 6)) (by decide +kernel)

def rule221_44 : {c : Cut // CutGood (goalAt 221) c} :=
  ruleFor 221 lower213 (some (1,input 4,input 6)) (by decide +kernel)

def rule221_45 : {c : Cut // CutGood (goalAt 221) c} :=
  ruleFor 221 lower205 none (by decide +kernel)

def rule221_46 : {c : Cut // CutGood (goalAt 221) c} :=
  ruleFor 221 lower93 none (by decide +kernel)

def rule221_47 : {c : Cut // CutGood (goalAt 221) c} :=
  ruleFor 221 lower213 (some (1,input 0,input 6)) (by decide +kernel)

def rule221_48 : {c : Cut // CutGood (goalAt 221) c} :=
  ruleFor 221 lower217 (some (3,input 0,input 6)) (by decide +kernel)

def rule221_49 : {c : Cut // CutGood (goalAt 221) c} :=
  ruleFor 221 lower217 (some (1,input 0,input 7)) (by decide +kernel)

def rule221_50 : {c : Cut // CutGood (goalAt 221) c} :=
  ruleFor 221 lower201 none (by decide +kernel)

def rule221_51 : {c : Cut // CutGood (goalAt 221) c} :=
  ruleFor 221 lower205 (some (1,input 2,input 7)) (by decide +kernel)

def rule221_52 : {c : Cut // CutGood (goalAt 221) c} :=
  ruleFor 221 lower205 (some (3,input 2,input 6)) (by decide +kernel)

def rule221_53 : {c : Cut // CutGood (goalAt 221) c} :=
  ruleFor 221 lower216 (some (3,input 4,input 7)) (by decide +kernel)

def rule221_54 : {c : Cut // CutGood (goalAt 221) c} :=
  ruleFor 221 lower220 (some (3,input 4,input 7)) (by decide +kernel)

def rule221_55 : {c : Cut // CutGood (goalAt 221) c} :=
  ruleFor 221 lower213 (some (0,input 0,input 7)) (by decide +kernel)

def rule221_56 : {c : Cut // CutGood (goalAt 221) c} :=
  ruleFor 221 lower85 none (by decide +kernel)

def rule221_57 : {c : Cut // CutGood (goalAt 221) c} :=
  ruleFor 221 lower217 (some (2,input 6,input 7)) (by decide +kernel)

def rule221_58 : {c : Cut // CutGood (goalAt 221) c} :=
  ruleFor 221 lower153 (some (3,input 3,input 7)) (by decide +kernel)

def rule221_59 : {c : Cut // CutGood (goalAt 221) c} :=
  ruleFor 221 lower204 (some (3,input 2,input 6)) (by decide +kernel)

def rule221_60 : {c : Cut // CutGood (goalAt 221) c} :=
  ruleFor 221 lower217 (some (2,input 4,input 7)) (by decide +kernel)

def rule221_61 : {c : Cut // CutGood (goalAt 221) c} :=
  ruleFor 221 lower217 (some (3,input 6,input 7)) (by decide +kernel)

def rule221_62 : {c : Cut // CutGood (goalAt 221) c} :=
  ruleFor 221 lower217 (some (1,input 6,input 7)) (by decide +kernel)

def rule221_63 : {c : Cut // CutGood (goalAt 221) c} :=
  ruleFor 221 lower217 (some (0,input 6,input 7)) (by decide +kernel)

def rule221_64 : {c : Cut // CutGood (goalAt 221) c} :=
  ruleFor 221 lower213 (some (3,input 4,input 6)) (by decide +kernel)

def rule221_65 : {c : Cut // CutGood (goalAt 221) c} :=
  ruleFor 221 lower220 (some (2,input 4,input 6)) (by decide +kernel)

def rule221_66 : {c : Cut // CutGood (goalAt 221) c} :=
  ruleFor 221 lower213 (some (3,input 4,input 7)) (by decide +kernel)

def rule221_67 : {c : Cut // CutGood (goalAt 221) c} :=
  ruleFor 221 lower213 (some (2,input 4,input 7)) (by decide +kernel)

def rule221_68 : {c : Cut // CutGood (goalAt 221) c} :=
  ruleFor 221 lower217 (some (1,input 4,input 7)) (by decide +kernel)

def rule221_69 : {c : Cut // CutGood (goalAt 221) c} :=
  ruleFor 221 lower213 (some (1,input 4,input 7)) (by decide +kernel)

def rule221_70 : {c : Cut // CutGood (goalAt 221) c} :=
  ruleFor 221 lower213 (some (0,input 4,input 7)) (by decide +kernel)

def rule221_71 : {c : Cut // CutGood (goalAt 221) c} :=
  ruleFor 221 lower217 (some (3,input 4,input 7)) (by decide +kernel)

def rule221_72 : {c : Cut // CutGood (goalAt 221) c} :=
  ruleFor 221 lower213 (some (3,input 6,input 7)) (by decide +kernel)

def rule221_73 : {c : Cut // CutGood (goalAt 221) c} :=
  ruleFor 221 lower213 (some (2,input 6,input 7)) (by decide +kernel)

def rule221_74 : {c : Cut // CutGood (goalAt 221) c} :=
  ruleFor 221 lower213 (some (1,input 6,input 7)) (by decide +kernel)

def rule221_75 : {c : Cut // CutGood (goalAt 221) c} :=
  ruleFor 221 lower213 (some (0,input 6,input 7)) (by decide +kernel)

def cuts221 : Cuts (goalAt 221) := [rule221_0,rule221_1,rule221_2,rule221_3,rule221_4,rule221_5,rule221_6,rule221_7,rule221_8,rule221_9,rule221_10,rule221_11,rule221_12,rule221_13,rule221_14,rule221_15,rule221_16,rule221_17,rule221_18,rule221_19,rule221_20,rule221_21,rule221_22,rule221_23,rule221_24,rule221_25,rule221_26,rule221_27,rule221_28,rule221_29,rule221_30,rule221_31,rule221_32,rule221_33,rule221_34,rule221_35,rule221_36,rule221_37,rule221_38,rule221_39,rule221_40,rule221_41,rule221_42,rule221_43,rule221_44,rule221_45,rule221_46,rule221_47,rule221_48,rule221_49,rule221_50,rule221_51,rule221_52,rule221_53,rule221_54,rule221_55,rule221_56,rule221_57,rule221_58,rule221_59,rule221_60,rule221_61,rule221_62,rule221_63,rule221_64,rule221_65,rule221_66,rule221_67,rule221_68,rule221_69,rule221_70,rule221_71,rule221_72,rule221_73,rule221_74,rule221_75]

def state221_0 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa,0xfffffffffffffffffffffffffffffffffafafafafafafafafafafafafafafafa,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_0 : Impossible true (goalAt 221) 4 state221_0.toFinset :=
  node_ok cuts221 [] 0x145001101044044140044101101044044180044044101240501101064041101044241101121004140222004140064501114044701114124044101104244101104048808104044809044401110044509050104044104104048809 (by decide +kernel)

def state221_1 : List Sig := [0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa,0xfffffffffffffffffffffffffffffffffafafafafafafafafafafafafafafafa,input 7,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_1 : Impossible true (goalAt 221) 4 state221_1.toFinset :=
  node_ok cuts221 [] 0x8901204048109204041940045008880045004810120404818044501901044041109044048808204048104204048809044401110044504818044041104044048180044048101240501101045001101044044809 (by decide +kernel)

def state221_2 : List Sig := [0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa,input 6,0xfffffffffffffffffffffffffffffffffafafafafafafafafafafafafafafafa,input 7,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_2 : Impossible true (goalAt 221) 5 state221_2.toFinset :=
  node_ok cuts221 [⟨state221_0,exclude221_0⟩,⟨state221_1,exclude221_1⟩] 0x44048101240501101145001101044044140044044101800041101044101101044048180064041101044241101224048101204248101121004140222004140124044101104244101064501114044701114220204101204060000104044140104044101120244104204048104204048809044401110044510004 (by decide +kernel)

def state221_3 : List Sig := [0xfffffffffffffffffffffffffffffffffffafffafffafffafffafffafffafffa,input 3,input 7,input 0,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_3 : Impossible true (goalAt 221) 5 state221_3.toFinset :=
  node_ok cuts221 [] 0x4101204044480104044400110004101400101101104044414044041101204049014044045440044041101111004101104104101110041101044101101206008101204108101220201114064501118044501110240404901104044408104041901044041109044048901204048808204044840 (by decide +kernel)

def state221_4 : List Sig := [0xff00ff00ff00ff00ff00ff00ff00ff00fa00fa00fa00fa00fa00fa00fa00fa,input 3,input 7,input 0,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_4 : Impossible true (goalAt 221) 5 state221_4.toFinset :=
  node_ok cuts221 [] 0x4101204044480104041101104044414044041101204049014044044101104104101110041101044101101206008101204108101220201910064401918044504800120004808104041909044041909044048800220008808204044400110004101120201101064241101064241110044401114064608101220208101220208880 (by decide +kernel)

def state221_5 : List Sig := [0xffff0000ffff0000ffff0000ffff0000fafa0000fafa0000fafa0000fafa,0xfffffffffffffffffffffffffffffffffafafafafafafafafafafafafafafafa,input 7,input 0,input 3,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_5 : Impossible true (goalAt 221) 5 state221_5.toFinset :=
  node_ok cuts221 [] 0x410120404448010404540015000410112020480012000480810404890120404810920404484015100888012100410110410410111004111406450111c044508101204108101220241100240001101120204101044041101044241901044048180044041101044101101240508101044044440 (by decide +kernel)

def state221_6 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000fafafafafafafafafafa0000fafa0000,input 0,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_6 : Impossible true (goalAt 221) 3 state221_6.toFinset :=
  node_ok cuts221 [] 0x64041101044241101120004800120208101044501914044701114044001100044044440204008100204044808110004400110501101 (by decide +kernel)

def state221_7 : List Sig := [0xffffffffffffffffffff0000ffff0000fafafafafafafafafafa0000fafa0000,input 6,input 7,input 0,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_7 : Impossible true (goalAt 221) 4 state221_7.toFinset :=
  node_ok cuts221 [⟨state221_6,exclude221_6⟩] 0x220008800220208101120004800120204414064041101044241101044501914044701114204008100204048808044504808120244808044001100044044440120208101800008101110004400110501101240009000240501101 (by decide +kernel)

def state221_8 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,0xfffffffffffffffffffffffffffffffffafafafafafafafafafafafafafafafa,input 0,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_8 : Impossible true (goalAt 221) 4 state221_8.toFinset :=
  node_ok cuts221 [⟨state221_6,exclude221_6⟩] 0x484011100888011100190104404110904404890120404810920404111406450111c044501110044041104044044480204048104204048809204048808204044818111001101044060000044044101110501101 (by decide +kernel)

def state221_9 : List Sig := [0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 6,0xfffffffffffffffffffffffffffffffffafafafafafafafafafafafafafafafa,input 7,input 0,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_9 : Impossible true (goalAt 221) 5 state221_9.toFinset :=
  node_ok cuts221 [⟨state221_7,exclude221_7⟩,⟨state221_8,exclude221_8⟩,⟨state221_1,exclude221_1⟩] 0x890120404810920404484011100888011100481012040481811050190104404110904404111406450111c044508101204108101220241110044504114800081114044041104044048180220204414204060001204044410110404414120604101044048101240501101111001101044060000 (by decide +kernel)

def state221_10 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,0xfffffffffffffffffffffffffffffffffafafafafafafafafafafafafafafafa,input 0,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_10 : Impossible true (goalAt 221) 5 state221_10.toFinset :=
  node_ok cuts221 [⟨state221_0,exclude221_0⟩,⟨state221_8,exclude221_8⟩] 0x151001101044044440044044480800041101044048101240501101064041101044241101121004440222004440132004840121004480224048101204248101044041104044048180044501914044701114044401114106020000044508101204108101220248101220208101400104440112004440241404101 (by decide +kernel)

def state221_11 : List Sig := [0xffffffffffffffff00000000000000000000000000000000,input 6,0xfffffffffffffffffffffffffffffffffafafafafafafafafafafafafafafafa,input 0,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_11 : Impossible true (goalAt 221) 5 state221_11.toFinset :=
  node_ok cuts221 [] 0x544004404110111100110110404441404404190104404110904404484011100888011100480012000480810404110104410110120600111406450111c044501110104044104104044401110004400104044808204041101240501101204048901204248101204108101204048809220204480 (by decide +kernel)

def state221_12 : List Sig := [0xfffffffffffffffffffffffffffffffffafafafafafafafafafafafafafafafa,input 7,input 0,input 3,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_12 : Impossible true (goalAt 221) 6 state221_12.toFinset :=
  node_ok cuts221 [⟨state221_2,exclude221_2⟩,⟨state221_3,exclude221_3⟩,⟨state221_4,exclude221_4⟩,⟨state221_5,exclude221_5⟩,⟨state221_9,exclude221_9⟩,⟨state221_10,exclude221_10⟩,⟨state221_11,exclude221_11⟩] 0x80018410110404810130200810180014c08011200810110404410111100480811001000410404440011100410110405000412020480815050110104404410140028410115052000411050410104404110124050110104404810124200810124050908024050810104404110115142000315100444004404110115140110104404444040028444012020888012000410112100480012020484012020410122200410106424484006404110116140110106424585004424110112100110122424484022404810122200810122424888020424810112100810180008484012100444022200444080004888022200444012100444010404111410404440440024410410406000010404440404450440104404818004404908004450110404404111404404908020600818040024111404450484006470191440024191c04470484004450111420404111420404880c20600810420404818020404880c044508809400210007044410006400148808 (by decide +kernel)

def state221_13 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa,0xfafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafa,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_13 : Impossible true (goalAt 221) 5 state221_13.toFinset :=
  node_ok cuts221 [⟨state221_0,exclude221_0⟩] 0x110404404110124200110130100c05004404110110404908004404190104404110904404191404450111c04450484030100888012100490110404410910404110114500110110500414012100888410500111004440111430200414020502000010500410110500410112024111430200c040044504101104104101044508101 (by decide +kernel)

def state221_14 : List Sig := [0x505050505050505050500000505000005050505050505050505000005050000,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa,input 3,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_14 : Impossible true (goalAt 221) 4 state221_14.toFinset :=
  node_ok cuts221 [] 0x8800220008808204044810120404818044501901044041109044048100204008101220201100044001101206009400250009010044049010204049010204041140222001940045004818044501110044404809 (by decide +kernel)

def state221_15 : List Sig := [0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa,0xfafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafa,input 3,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_15 : Impossible true (goalAt 221) 5 state221_15.toFinset :=
  node_ok cuts221 [⟨state221_14,exclude221_14⟩,⟨state221_1,exclude221_1⟩] 0x22020484022000810122200880022020888022020810112100810112060888012040111412100481012060484012060111422200111406424888006404110112100110106424484004424110122200110120404114020404880840040880820406000120404880804500880823210114004500484040040194023211000f222104840045001140044510004044404818045001110044501140044504818400104818044060000044049080045001140044041140044049080400404809204041114204048808206108104204048184204048808044508808044048184044049080044501104044041114044049080206109080240401101240008101242009000240409080240408101044041101 (by decide +kernel)

def state221_16 : List Sig := [0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa,input 6,0xfafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafa,input 3,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_16 : Impossible true (goalAt 221) 6 state221_16.toFinset :=
  node_ok cuts221 [⟨state221_13,exclude221_13⟩,⟨state221_2,exclude221_2⟩,⟨state221_15,exclude221_15⟩] 0x901004404900020404908024000901024200901020404110104405000404404110110405000410405000340012000210404110104404111424200110420610110104404111404404110120610908024200880812100880020404888022000880822200880820404484020404190912100190104404585004404190916140110904404484004404490922200490110404484010404490912100410910404888010404191c22200191404450484004450191c12100111c044508880044508101105008101220210005220208101800048101220204140220201101105001101242005150145001101145401101242004140105008c84105004140121010005121008c844003c888412100414010500410140010410140014414010500410110500410140011000412024111440010111040000414004440111410500111440001000e40000c04010404410120405000420404c04080000c04020404410110405000d400304104204041114204048808206108104204048184204048808044508808 (by decide +kernel)

def state221_17 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,0xfafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafa,input 0,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_17 : Impossible true (goalAt 221) 5 state221_17.toFinset :=
  node_ok cuts221 [⟨state221_8,exclude221_8⟩] 0x64041101044241101121009040222004840120404810120604414044501914044701114044401101044101101242001114241008184044501114104508184044504440121008884111001101111001101242004440241020000111004410110404414120601101242009040044041101104044414044048101 (by decide +kernel)

def state221_18 : List Sig := [0x505050505050505050500000505000005050505050505050505000005050000,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 6,input 0,input 3,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_18 : Impossible true (goalAt 221) 5 state221_18.toFinset :=
  node_ok cuts221 [⟨state221_14,exclude221_14⟩] 0x880022000880820404481012040481811050190104404110904404810020400810122020111406450111c04450111410452000004450110004400110120600c010204049040204044400250009400240401101240408101240408101111008880121004440044404818110504410110409080 (by decide +kernel)

def state221_19 : List Sig := [0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 6,0xfafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafa,input 0,input 3,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_19 : Impossible true (goalAt 221) 6 state221_19.toFinset :=
  node_ok cuts221 [⟨state221_17,exclude221_17⟩,⟨state221_18,exclude221_18⟩,⟨state221_9,exclude221_9⟩,⟨state221_15,exclude221_15⟩] 0x22020484022000810122200880022020888022020810112100810112060888012040441412100481012060484012060441422200441406424888006404110112100110106424484004424110122200110120404111420404880820610810420404818420404880804450880840048111404450484006470191440048191c0447048400445011144004d0013044410012044501114110510012104510012400120003110501114044501101206101101242001114044101101044501101242008184242008101111008101220210010220208101800088101220204440220208c84111004440121010010121008c844003c888412100444011100441440010441012060444011040441411100441412061000412060110180004110124200444011100110111100110124201001024200c04011050c01020405000420404c040800009040204044414204050011400084101240401101240008101242009000240409080240408101044041101 (by decide +kernel)

def state221_20 : List Sig := [0x505050505050505050505050505050505050505050505050000000000000000,input 6,input 7,input 0,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_20 : Impossible true (goalAt 221) 5 state221_20.toFinset :=
  node_ok cuts221 [] 0x9400250009410044045400110004410110001901044041109044048c00230008c08204044c0011000440811000110004400110124200111006440111804440810020400810123020410010400410111000440031000c040110004440044045440044044440222104840111004140220208101301008101120204400111004400 (by decide +kernel)

def state221_21 : List Sig := [0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000000000,input 6,input 7,0xfafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafa,input 0,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_21 : Impossible true (goalAt 221) 5 state221_21.toFinset :=
  node_ok cuts221 [] 0x9800220008810220005800120004810120001101044101101242001110224048800224048800124044800124044800044045440044044440230008800224048800130004800124044800120008800301004800121001101161001101121001114206101114111008884111004840204048800301008800104044800121004800 (by decide +kernel)

def state221_22 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,input 7,0xfafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafa,input 0,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_22 : Impossible true (goalAt 221) 6 state221_22.toFinset :=
  node_ok cuts221 [⟨state221_20,exclude221_20⟩,⟨state221_10,exclude221_10⟩,⟨state221_13,exclude221_13⟩,⟨state221_21,exclude221_21⟩,⟨state221_17,exclude221_17⟩] 0x4404c04030140110104404c08080010110104404908024200110106404110104424110112100c0402220048402220048401210088808000c484012101000104404110404404908004450191404470111404440111430100818404450111430202000204450111420610818404450110115100110111100444012100888411100444030102000111100c48011100444030202000011100444040014810130100c080241404101 (by decide +kernel)

def state221_23 : List Sig := [0xfafafafafafafafafffffffffffffffffafafafafafafafafafafafafafafafa,input 6,input 7,input 0,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_23 : Impossible true (goalAt 221) 5 state221_23.toFinset :=
  node_ok cuts221 [] 0x110120404901404404110110404441404404190104404110904404890120404810920404480012000480810404110104410110120600111406450111c04450810120410810122024410110410410111004111030000c000301004101044045440044044440111004840222004440204048808204044440110004400104044808 (by decide +kernel)

def state221_24 : List Sig := [0xffffffffffffffff00000000000000000000000000000000,input 6,input 7,0xfafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafa,input 0,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_24 : Impossible true (goalAt 221) 6 state221_24.toFinset :=
  node_ok cuts221 [⟨state221_23,exclude221_23⟩,⟨state221_11,exclude221_11⟩] 0x4404c04030140110104404410111050110106404110104424110112100c04022200484012000480012020410104404110404404908004450191404470111404440111430100818404450410110410410111004110115100110111100444012100888411100444030102000111100440011000410112020c00030100410124200110124200110122200484022200484020610111420610111440014444080000444020404c080 (by decide +kernel)

def state221_25 : List Sig := [0xfafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafa,input 0,input 3,input 4,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_25 : Impossible true (goalAt 221) 7 state221_25.toFinset :=
  node_ok cuts221 [⟨state221_12,exclude221_12⟩,⟨state221_16,exclude221_16⟩,⟨state221_19,exclude221_19⟩,⟨state221_22,exclude221_22⟩,⟨state221_24,exclude221_24⟩] 0x80010c04010404c00040010810130200c0008000cc04030200c0404001081011040441014000c90100440490004000881012420090004000c90102420090104000881010440411014001054140440411014000841014000c41014000c541480008441440008410104404110140004880812100880040004810122200880040004880822200880840004810112100810140004480822200480040004410112100480040004480812100480840004410122200410140004190912100190140004110116140110140004190916140110940004110112100110140030810104450810140030880820610810440030810120610810140030880804450880840030410104450410140030440440030410440030410180004410140030440404450440140008110120610110140030908004450110440030110104450110140008908020610908040005000104450111440004484006470191440005000c06470111c40004484004450111440001000b4000011104001481011110081014001488084001488084001481018000081014001488081110088084001041014001044004001448081110044004001441011110041014001048084001048084000811011110011014000c90801514054404000c1101151401101400089080111004440400048c84111004440400044840400044840400048c84400048884400044840111004440 (by decide +kernel)

def state221_26 : List Sig := [0xf0f0f0f0f0f0f0f0f0a0f0a0f0a0f0a0f0f0f0f0f0f0f0f0f0a0f0a0f0a0f0a,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 6,input 0,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_26 : Impossible true (goalAt 221) 5 state221_26.toFinset :=
  node_ok cuts221 [] 0x900024000901004404540011000441011000810120420810122004110104420110124200410111000410111000151011000c400301004400230008c0020404901004404584004404484013000440010404440020404810520404850104404110504404150104460111c044601518104044400104044400111008880121004440 (by decide +kernel)

def state221_27 : List Sig := [0xfffafffafffafffafffafffafffafffafffafffafffafffafffafffafffafffa,0xffffffffffffffffffaaffaaffaaffaaffffffffffffffffffaaffaaffaaffaa,input 6,input 0,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_27 : Impossible true (goalAt 221) 5 state221_27.toFinset :=
  node_ok cuts221 [] 0x900024000901004404110110404441804404908004404110124200810120420810122004110104420110124200410110420410111004111410500410120404c040104044404204048804204049010204049010204049010044045440044044440104044440104050016222004440111010018 (by decide +kernel)

def state221_28 : List Sig := [0xffffffffffffffffffaaffaaffaaffaaffffffffffffffffffaaffaaffaaffaa,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 6,input 0,input 2,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_28 : Impossible true (goalAt 221) 6 state221_28.toFinset :=
  node_ok cuts221 [⟨state221_26,exclude221_26⟩,⟨state221_27,exclude221_27⟩] 0x900024000901004404110110404481804404908004404110124200850120404810520404150104404110504404450110404410510404444012102000111102000011100444040060810120420810122004110104420110124200111805460111c0446041011042041011200441404005c410120404c040104044404204049010204049010044045840044044840104044840110308880204049010204049010 (by decide +kernel)

def state221_29 : List Sig := [0x5555555555555555555555555555555555505550555055505550555055505550,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 7,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_29 : Impossible true (goalAt 221) 4 state221_29.toFinset :=
  node_ok cuts221 [] 0x104048101112004101044044101110501101044048101240501101104004100104044404044001100044044140204008100204041110110004400110104101111001101044201101220048101204208101111001110044501110 (by decide +kernel)

def state221_30 : List Sig := [0xfffffffffffffffffffffffffffffffffffafffafffafffafffafffafffafffa,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 7,input 0,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_30 : Impossible true (goalAt 221) 5 state221_30.toFinset :=
  node_ok cuts221 [⟨state221_29,exclude221_29⟩] 0x104048101112004101110004400104050016044044101110501101044048101240501101151001101044044440104044404104044801044041108044049080204048108204048801044520000240404101110104101110101101242001101222008101220108101240504840 (by decide +kernel)

def state221_31 : List Sig := [0xffff0000ffff0000ffff0000ffff0000ffaa0000ffaa0000ffaa0000ffaa,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 7,input 0,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_31 : Impossible true (goalAt 221) 5 state221_31.toFinset :=
  node_ok cuts221 [] 0xd00024000904024000440011000440410404940024000900424000444016100888411100410111010410112004111805460111c044608101240008101240001100160005800104044404260009000204049000044044404104041101044041105054041101242001101044041108044049000204049000121001101044045840 (by decide +kernel)

def state221_32 : List Sig := [0xffffffffffffffffffffffffffffffffffaaffaaffaaffaaffaaffaaffaaffaa,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 7,input 0,input 2,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_32 : Impossible true (goalAt 221) 6 state221_32.toFinset :=
  node_ok cuts221 [⟨state221_30,exclude221_30⟩,⟨state221_31,exclude221_31⟩] 0x410120404c08010404440410404410111010110110404441404404110120404881804406000104404110140054440011000440410404150104404110504404850120404810520404444022200888411100444040062000011100410111010410112004110104420110124200111805460111c044608101204208101220048180400689010104044404104044404044049080044048880204048880240604840 (by decide +kernel)

def state221_33 : List Sig := [0xf0f5f0f5f0f5f0f5f0f5f0f5f0f5f0f5f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 7,input 0,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_33 : Impossible true (goalAt 221) 5 state221_33.toFinset :=
  node_ok cuts221 [] 0x4101204044480104041101104044414044041101204049014044044101110104101120041101044201101242008101204208101220041110044601518044701118120004800104044404044045840044044840220008800204049014110004400110104101054041101044141101214048101204148101111004840222004440 (by decide +kernel)

def state221_34 : List Sig := [0xfffafffafffafffafffafffafffafffafffafffafffafffafffafffafffafffa,0x55005500550055005500550055005500000000000000000000000000000000,input 7,input 0,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_34 : Impossible true (goalAt 221) 5 state221_34.toFinset :=
  node_ok cuts221 [] 0x410120404c08010404110110404441404404110120404881404404410110410410111004110104410110124200810120410810122004111030200410130200410124200110124200110120610901040060444022200444011000440010404c080044045440044044440220008800204044440 (by decide +kernel)

def state221_35 : List Sig := [0x55005500550055005500550055005500000000000000000000000000000000,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 7,input 0,input 2,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_35 : Impossible true (goalAt 221) 6 state221_35.toFinset :=
  node_ok cuts221 [⟨state221_33,exclude221_33⟩,⟨state221_34,exclude221_34⟩] 0x410120404c08010404110110404441404404110120404881804404440011000440410404150104404110504404850120404810520404444012102000111100410111010410112004110104420110124200111805460111c04460810120420810122004111012000480010404440404404584004404484022000810112100c08010404c08010404908004404908004405001811102000011101001b240408880 (by decide +kernel)

def state221_36 : List Sig := [0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,0xffffffffffffffffffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaa,input 7,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_36 : Impossible true (goalAt 221) 4 state221_36.toFinset :=
  node_ok cuts221 [] 0x1540045008184045008501204048105204044410110404414044601501044041105044048101241008101045001110044401118110501101045001101110148108044048101241001101110101101044050015 (by decide +kernel)

def state221_37 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaa,input 7,input 6,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_37 : Impossible true (goalAt 221) 5 state221_37.toFinset :=
  node_ok cuts221 [⟨state221_36,exclude221_36⟩] 0x4404410180000110104404810130140110104420110104405001505404110104414110111100414020610414011404410110414410121404810120414810105460111804470111804404514004404414010404414010404440520404c040204044140044401110044610014104048101301004101110108108 (by decide +kernel)

def state221_38 : List Sig := [0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,0xffffffffffffffffaaaaaaaaaaaaaaaa,input 7,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_38 : Impossible true (goalAt 221) 4 state221_38.toFinset :=
  node_ok cuts221 [] 0x154004500818404500850820420810c204201501044041105044048100204008108240401101045001101110144410110404414044601110044401118110508101044044404044049080240009000240401101 (by decide +kernel)

def state221_39 : List Sig := [0xffffffffffffffffaaaaaaaaaaaaaaaa,input 7,input 6,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_39 : Impossible true (goalAt 221) 5 state221_39.toFinset :=
  node_ok cuts221 [⟨state221_38,exclude221_38⟩] 0x110110406000004404900024000901004404150104404110504404444010500818410500450110404410510404850820420810c20420110114500110110500410110500410111014810020400810824040c00030000c08010404110104420110124200111805460111c044601110044401118206004101110104101044608101 (by decide +kernel)

def state221_40 : List Sig := [0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_40 : Impossible true (goalAt 221) 4 state221_40.toFinset :=
  node_ok cuts221 [] 0x44201101044044480044044101240501101044041501044141101044045140044044140044401110044604480104048804104044405105004440222004140104044404104048805044601518044701118114044101104144101 (by decide +kernel)

def state221_41 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_41 : Impossible true (goalAt 221) 5 state221_41.toFinset :=
  node_ok cuts221 [⟨state221_40,exclude221_40⟩] 0x110804404110124200110130100c05004404110110404908004404150104404110504404444010500888410500151804460111c04460444030102000011100450110404410510404110114500110110500111004440111822200414020500888010500410110500410111014111830200c040044604101110104101044608101 (by decide +kernel)

def state221_42 : List Sig := [0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,0xf0f0f0f0f0f0f0f0a0a0a0a0a0a0a0a0f0f0f0f0f0f0f0f0a0a0a0a0a0a0a0a,0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_42 : Impossible true (goalAt 221) 4 state221_42.toFinset :=
  node_ok cuts221 [] 0x8800220008101240401510054401518110401101045001101110148101214208101220144400110001101242008101204148101214041140222001140055001118044041105044041501240009000240401101 (by decide +kernel)

def state221_43 : List Sig := [0xf0f0f0f0f0f0f0f0a0a0a0a0a0a0a0a0f0f0f0f0f0f0f0f0a0a0a0a0a0a0a0a,0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa,input 6,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_43 : Impossible true (goalAt 221) 5 state221_43.toFinset :=
  node_ok cuts221 [⟨state221_42,exclude221_42⟩] 0x240009000240401101044044101800001101054201101044049080220008800204049010044045140044044140104044140104044405054401510054608880104048101301004101110008101214208101220148101204148101214041101044141101054044140222004140111004101104144101114041118 (by decide +kernel)

def state221_44 : List Sig := [0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,0xfffafffafffafffafffafffafffafffafffafffafffafffafffafffafffafffa,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_44 : Impossible true (goalAt 221) 4 state221_44.toFinset :=
  node_ok cuts221 [] 0x8101204208101220041101110101101242008101220108101240401114044501118110501140044049080044044401204049010204049010110404410110510016044044440044049080240009000240401101 (by decide +kernel)

def state221_45 : List Sig := [0xfffafffafffafffafffafffafffafffafffafffafffafffafffafffafffafffa,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa,input 6,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_45 : Impossible true (goalAt 221) 5 state221_45.toFinset :=
  node_ok cuts221 [⟨state221_44,exclude221_44⟩] 0x240009000240401101044044101800001101044201101044049080104048101301004101110108101204208101220048101220108101240401101242001101242004101400644101110041114044501118222104140204049010204049010044045440044044440104044440104050016044604440044610016 (by decide +kernel)

def state221_46 : List Sig := [0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 7,0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_46 : Impossible true (goalAt 221) 4 state221_46.toFinset :=
  node_ok cuts221 [] 0x1110044401118110508804220108105240501140055008880045001101045001101110148105204308105220144410110404414044601101110101101242008101044049004240501101044041501044141101 (by decide +kernel)

def state221_47 : List Sig := [0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 7,0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa,input 6,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_47 : Impossible true (goalAt 221) 5 state221_47.toFinset :=
  node_ok cuts221 [⟨state221_40,exclude221_40⟩,⟨state221_46,exclude221_46⟩] 0x4404410180004110104420110104404908004404900424050110104404150104414110104404514004404414010404414010404440504440111004460888022010880420414901410500444022200414011010410120416000010404410111404410510404810520430810522014111805460111c044608101 (by decide +kernel)

def state221_48 : List Sig := [0xf0f0f0f0f0f0f0f0f0f00000f0f00000f0f0f0f0f0f0f0f0f0f00000f0f0000,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_48 : Impossible true (goalAt 221) 4 state221_48.toFinset :=
  node_ok cuts221 [] 0x8800220008101240401110044401118110501501045001501110048101204208101220044400110001501252009400250009010054049010204049010204041140222001140055001118110504410110401101 (by decide +kernel)

def state221_49 : List Sig := [0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 2,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_49 : Impossible true (goalAt 221) 5 state221_49.toFinset :=
  node_ok cuts221 [⟨state221_36,exclude221_36⟩,⟨state221_38,exclude221_38⟩,⟨state221_48,exclude221_48⟩,⟨state221_42,exclude221_42⟩,⟨state221_44,exclude221_44⟩,⟨state221_46,exclude221_46⟩] 0x214144440214048101400588101214160005204148101111008101232104440055001140400581140232120004222101140111001140110520003110401118111004410110504440110501118400581118054160002054041101111001101054144440044141101400581101204041140220009010222008800204048880204049010045009010044608880044404414045001110044601140044604414222004414044048880044049080045001140044041140044049080222004405204044414204048808800048108204060000204048808110508801044050015044049080110504404044044414044049080400549080240401101240008101242009000240409080240408101044041101 (by decide +kernel)

def state221_50 : List Sig := [0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa,input 6,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 2,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_50 : Impossible true (goalAt 221) 6 state221_50.toFinset :=
  node_ok cuts221 [⟨state221_37,exclude221_37⟩,⟨state221_39,exclude221_39⟩,⟨state221_41,exclude221_41⟩,⟨state221_43,exclude221_43⟩,⟨state221_45,exclude221_45⟩,⟨state221_47,exclude221_47⟩,⟨state221_49,exclude221_49⟩] 0x90100440490002040490802400090102420090102040411010440500160440411011040500161040500034005a0006104041101044041118242001108400541101044041118044041101400549080242008505111008501204050016204048505800148105204044440204041505111001501044045450044041505151401105044044440044048c84111004440105010016105008c8480010888410500444010500450540058450110404444010404450511100410510405001610404151c8000c151804460444004460151c11100111c04461001604460810110500880024040888022000810122200810124040414024040110110500110124200515014500110114540110124200414010500410122200410140064414010500410110500410140058888011014111822200111040050414004440111810500111840050888022200c04010404410120405001620404c04080008c04020404410110405001c400304404204041118204048808800048108204060000204048808044608801 (by decide +kernel)

def state221_51 : List Sig := [0xfffffffffffffffffffffffffffffffffafafafafafafafafafafafafafafafa,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 7,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_51 : Impossible true (goalAt 221) 5 state221_51.toFinset :=
  node_ok cuts221 [] 0x410120404c08010404440410404410113004440011000410112020110110404441404404110120404908004404110c04404110140028544004404110111100480012000410111010110116100110112100810120600810112100111404450111c12100484011100818011100810c400781118 (by decide +kernel)

def state221_52 : List Sig := [0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 7,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_52 : Impossible true (goalAt 221) 5 state221_52.toFinset :=
  node_ok cuts221 [] 0x11010410110404480110404810530200410111000440011010410104404410111050110104420110104405001f044048105242001101044041501044141101120004800104044404044045840044044840044401110044604840204148180204144840121004440206004440044601518044701118204308101 (by decide +kernel)

def state221_53 : List Sig := [0xfffafffafffafffafffafffafffafffa,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_53 : Impossible true (goalAt 221) 4 state221_53.toFinset :=
  node_ok cuts221 [] 0x30000c00010404480104404410111050110124000900004404c040104044404104044404044049080044048180204008100044609010110004400104048101044045440044048101044608101204048108111008101204044440 (by decide +kernel)

def state221_54 : List Sig := [0xfffafffafffafffafffafffafffafffafffafffafffafffafffafffafffafffa,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 7,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_54 : Impossible true (goalAt 221) 5 state221_54.toFinset :=
  node_ok cuts221 [⟨state221_53,exclude221_53⟩] 0x10404810130200410111010410110404480104404410111050110104404810124200110104420110104405002120420410111010410111010110124200110124200810120610810140064111404450111840004484011000440010404c080044045440044044440204060000204044440044610020044604440 (by decide +kernel)

def state221_55 : List Sig := [0xffffffffffffffffffffffffffffffffafafafafafafafafaaaaaaaaaaaaaaaa,input 6,input 7,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_55 : Impossible true (goalAt 221) 4 state221_55.toFinset :=
  node_ok cuts221 [] 0x110120404c050044045400110004410110001108044041101111001101145001101105008101301008101105004c00110004101110001110044401118111008108110008101301004400110004101104044400 (by decide +kernel)

def state221_56 : List Sig := [0xffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0000000000000000,input 6,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_56 : Impossible true (goalAt 221) 4 state221_56.toFinset :=
  node_ok cuts221 [] 0x4420110104404c040150004400110404400044048101151001101044045840044044840044401110044604840130004400114044400204044440204044440110004501114044400110004101111004400204208101204041118 (by decide +kernel)

def state221_57 : List Sig := [0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0000000000000000,input 6,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 7,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_57 : Impossible true (goalAt 221) 5 state221_57.toFinset :=
  node_ok cuts221 [⟨state221_55,exclude221_55⟩,⟨state221_56,exclude221_56⟩] 0x4404810124200110104420110104405002215000440011040440004404584004404484020404818020404484004440111004460484013000440011404440020420440020404c480110004400114044501110004440044045440044044440206004840111004440204060001204044440044620000044604101 (by decide +kernel)

def state221_58 : List Sig := [0xffff0000ffff0000ffff0000ffff0000aaaa0000aaaa0000aaaa0000aaaa,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 7,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_58 : Impossible true (goalAt 221) 5 state221_58.toFinset :=
  node_ok cuts221 [] 0x104048101302004101110104101104044404110004400110104101111004840206104440214048101204148101054201108044301108120004800104044404204048180204044840044001100044204840240001101110104101044041101044141501044048180044041101121001101242008101044050015 (by decide +kernel)

def state221_59 : List Sig := [0xffffffffffffffffffff0000ffff0000aaaaaaaaaaaaaaaaaaaa0000aaaa0000,input 6,input 7,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_59 : Impossible true (goalAt 221) 4 state221_59.toFinset :=
  node_ok cuts221 [] 0x111004840206104440214048101204148101110004400110104801054041101044141101204008100204044840120004800120044404044001100044044840120048101112104801104041101400541101240009000242001101 (by decide +kernel)

def state221_60 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_60 : Impossible true (goalAt 221) 4 state221_60.toFinset :=
  node_ok cuts221 [] 0x111004840206104440054601118044701118054041101044141101214048101204148101044401110044604840044044840044048180204044810204044414204048108204044414044201101044044484044044101110501101 (by decide +kernel)

def state221_61 : List Sig := [0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 6,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 7,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_61 : Impossible true (goalAt 221) 5 state221_61.toFinset :=
  node_ok cuts221 [⟨state221_59,exclude221_59⟩,⟨state221_36,exclude221_36⟩,⟨state221_60,exclude221_60⟩] 0x111004840206104440214048101204148101054601118044701118110404410110504818054041101044141101204048180204044840044401110044604840120404810120604414044044840044048180204204414204060002204044414044620001110504101044048101242001101044201101044060000 (by decide +kernel)

def state221_62 : List Sig := [0xffffffffffffffff0000000000000000aaaaaaaaaaaaaaaa,input 6,input 7,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_62 : Impossible true (goalAt 221) 5 state221_62.toFinset :=
  node_ok cuts221 [] 0x110120404c05004404110111010441404404150104404110504404444010500818410500850120404810520404440011000440410420110114500110110500810130100810110500410010400410811010c00030000c04020404110104420110140054111805460111c044601110044401118105008101204208101044604101 (by decide +kernel)

def state221_63 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_63 : Impossible true (goalAt 221) 5 state221_63.toFinset :=
  node_ok cuts221 [⟨state221_60,exclude221_60⟩] 0x110804404110130100110130202000004404110120404908004404150104404110504404444012100818411100151804460111c04460c48011100444030200850120404810520404110116100110112100111004440111812100418012100484020600810112100810140064810120420810104460c04004460c040044604101 (by decide +kernel)

def state221_64 : List Sig := [0xffffffffffffffff00000000000000000000000000000000,input 6,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_64 : Impossible true (goalAt 221) 5 state221_64.toFinset :=
  node_ok cuts221 [] 0x4420110104404c04004404410111050110105404110104414110111100484020610444005460111804470111811000440011010410104404584004404484004440111004460484012000480010404c00130000c00010404480120404110124200110120404850120414810120600810120404484020420c080 (by decide +kernel)

def state221_65 : List Sig := [0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 7,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 2,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_65 : Impossible true (goalAt 221) 6 state221_65.toFinset :=
  node_ok cuts221 [⟨state221_51,exclude221_51⟩,⟨state221_52,exclude221_52⟩,⟨state221_54,exclude221_54⟩,⟨state221_57,exclude221_57⟩,⟨state221_58,exclude221_58⟩,⟨state221_61,exclude221_61⟩,⟨state221_37,exclude221_37⟩,⟨state221_62,exclude221_62⟩,⟨state221_63,exclude221_63⟩,⟨state221_64,exclude221_64⟩] 0x2000910404410120404c08020406000830200c0802040441011040600071101044040446041011040600061040441010446044041200454140440411011040500031040454148001444141040411010440500030440411012040490802040500032420090802040411010440411188001011084005411010440411180440411014005500034005444048000c440010404444011000440411100440410405000510404150511100150104404545004404150515140110504404444004404858411100444012101000512100858480008818412100444011100850511100850120405000520404850580004810520404444020404151c11100151804461000504460151c80000111c04460444004460410120600480011010484012000410112100410111010818011010110112100110124200585016100110116140110124200484012100810112100810140064818020600810120600810140064484012100111812100111040050818004440111820600111840050484012101001d400308108 (by decide +kernel)

def state221_66 : List Sig := [0xfffafffafffafffafffafffafffafffa,input 7,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 0,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_66 : Impossible true (goalAt 221) 5 state221_66.toFinset :=
  node_ok cuts221 [⟨state221_53,exclude221_53⟩] 0x30000c000301004101044044101110501101240009000240401101104044404104044801044041108044049080044501118240420000240404101110104101110101101242001101222008800220008880240404400110004101302001101151001101111001118400801118111004440121010018111008101 (by decide +kernel)

def state221_67 : List Sig := [0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 6,0xfffafffafffafffafffafffafffafffafffafffafffafffafffafffafffafffa,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 0,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_67 : Impossible true (goalAt 221) 5 state221_67.toFinset :=
  node_ok cuts221 [⟨state221_44,exclude221_44⟩] 0x20404810820404880104451002504460441480000441404404110804404908020404880420404901012100481411050441811050110124200110124200810124040810124040441011040441440058110111100110124200c010204049040204044101240009000240401101 (by decide +kernel)

def state221_68 : List Sig := [0xfffafffafffafffafffafffafffafffafffafffafffafffafffafffafffafffa,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 0,input 4,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_68 : Impossible true (goalAt 221) 6 state221_68.toFinset :=
  node_ok cuts221 [⟨state221_30,exclude221_30⟩,⟨state221_66,exclude221_66⟩,⟨state221_27,exclude221_27⟩,⟨state221_34,exclude221_34⟩,⟨state221_45,exclude221_45⟩,⟨state221_54,exclude221_54⟩,⟨state221_67,exclude221_67⟩] 0xc04010404c00020404c08030000c04030200c0402040441011040490100440490002040490802400090102420090102040411010440454140440411011040500231040454148001844141040411010440481010446081012202100242042081018001481012202011182200441010446041011101100241101041018001041011101011181200411014008411012420011180442011010446011012420100242420100014000411144002d00204002c81018000c81012404088842201081012221081012404100192404041012221041011101100191101041018000841011101088841101011012221011012420100232420011014008c110124200888424201000b40060484020404444020404901080004901020406000020404901011100901010405001611000c08011100440010404444010404c08040058c080044044440044049080151405440044045450044049080111004440 (by decide +kernel)

def state221_69 : List Sig := [0xffafffafffafffafffaaffaaffaaffaaffafffafffafffafffaaffaaffaaffaa,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 6,input 0,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_69 : Impossible true (goalAt 221) 5 state221_69.toFinset :=
  node_ok cuts221 [] 0x90002400090100440454001100044101100081012042081012200411010442011012420041011100041011100041404003c440031000c040110008101240408101240401101161001101121004101110004101110008880204049010204049010044044450044044440104044400104044400 (by decide +kernel)

def state221_70 : List Sig := [0xafafafafafafafafaaaaaaaaaaaaaaaa,input 7,input 6,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_70 : Impossible true (goalAt 221) 4 state221_70.toFinset :=
  node_ok cuts221 [] 0x5400110004410110009000240009010044041101145001101105004c00110004101110008100204008108240404400300004480110001101044201101111001110044401118111004101110004101110008101 (by decide +kernel)

def state221_71 : List Sig := [0xafafafafafafafafaaaaaaaaaaaaaaaaafafafafafafafafaaaaaaaaaaaaaaaa,input 6,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_71 : Impossible true (goalAt 221) 5 state221_71.toFinset :=
  node_ok cuts221 [⟨state221_55,exclude221_55⟩,⟨state221_70,exclude221_70⟩] 0x24040110124000810124200900024040908024040810104404110115040110115000440040058440015041001611040440004404440020404414022000901022200880020404888020404901010500901004404414004404908014540514004404515004404908010500414010404888013000440010500440010404414010404440022200440030100440011000810131200c40030100c480301008101110004400204041118204048808800048108204060000204048808044608801044044440044049080044601108044041118044049080111004440105004440044408880044601110105001118044608880111004440104041118104044400111004400104044440104044400044604400 (by decide +kernel)

def state221_72 : List Sig := [0x55005500550055005500550055005500050005000500050000000000000000,input 7,input 6,input 0,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_72 : Impossible true (goalAt 221) 4 state221_72.toFinset :=
  node_ok cuts221 [] 0x540011000441011000980022000881022000110004400110124200410010400410111000810020400810122000440022000c040110004440044045440044044140222004400111004400240408800301008800 (by decide +kernel)

def state221_73 : List Sig := [0xffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0000000000000000,input 7,input 6,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 0,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_73 : Impossible true (goalAt 221) 5 state221_73.toFinset :=
  node_ok cuts221 [⟨state221_72,exclude221_72⟩,⟨state221_55,exclude221_55⟩,⟨state221_56,exclude221_56⟩] 0x15000440011040440004404c040301401101044044440151001101044041108044049080044404501110004501110001118301020002044601118111020001044601101161001101121004c0011000450111000484030100888012102000011100484011100440030200c040110004400104044440110008101 (by decide +kernel)

def state221_74 : List Sig := [0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0000000000000000,input 6,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 0,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_74 : Impossible true (goalAt 221) 6 state221_74.toFinset :=
  node_ok cuts221 [⟨state221_69,exclude221_69⟩,⟨state221_71,exclude221_71⟩,⟨state221_73,exclude221_73⟩,⟨state221_57,exclude221_57⟩] 0x2404011012400081012420090002404090802404081010440411011504011011500044004005844001504100161104044000440444002040411182040488084009c81082040600032040488080446088010440500220440490800446011080440411180440490804009c9080400a10028044404501044604501110010027110004501400584501110001118110008101121008800240408880220008101222008101240404840240401101121001101242005850161001101161401101242004840121004501222004c0011000484011000450112100450111000888011000c04011000440020404c48031000c04031200c04020404440011000c04011100444020405001620404c04080008c0402040444402040500161110044400440454500440500161514054400440444400440500271110044400446100270446100164009e0001044604440044604840111004440222010016222004840800004840222004440111010018400984101 (by decide +kernel)

def state221_75 : List Sig := [0xaaffaaffaaffaaffaaffaaffaaffaaffaafaaafaaafaaafaaafaaafaaafaaafa,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 7,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_75 : Impossible true (goalAt 221) 4 state221_75.toFinset :=
  node_ok cuts221 [] 0x104048101112004101044044101110501101044048101240501101120004800104044401044041104044044840220008800204041114110004400104044801044041108044044440204048108204048801044401110044504440 (by decide +kernel)

def state221_76 : List Sig := [0x55005500550055005500550055005500500050005000500050005000500050,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 7,input 0,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_76 : Impossible true (goalAt 221) 5 state221_76.toFinset :=
  node_ok cuts221 [⟨state221_75,exclude221_75⟩] 0x4101204044480104041101104044414044041101204049014044044101110104101120041101044201101242008101204208101220041110120004800104044404044045840044044840220008800204049014110004400110104101111001101111401101800009010204049014204048880 (by decide +kernel)

def state221_77 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_77 : Impossible true (goalAt 221) 4 state221_77.toFinset :=
  node_ok cuts221 [] 0x111004460151804470111804404110804404448020414810c204148805121004440222004440044044840044044480220108804204144414204048101204144818044041501044141101044044101110501101 (by decide +kernel)

def state221_78 : List Sig := [0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 6,0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 7,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_78 : Impossible true (goalAt 221) 5 state221_78.toFinset :=
  node_ok cuts221 [⟨state221_77,exclude221_77⟩,⟨state221_46,exclude221_46⟩] 0x111020414810c204148805044601518044701118044604414800044414044041108044049080220108804204149014121004440222004440120404810120604414044044840044048880204044414204160000204144410110404414120604101044049004240501101044041501044141101 (by decide +kernel)

def state221_79 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 0,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_79 : Impossible true (goalAt 221) 5 state221_79.toFinset :=
  node_ok cuts221 [⟨state221_40,exclude221_40⟩,⟨state221_77,exclude221_77⟩] 0x4404150104414110104404448080004110104404900424050110104404110804404908004440111805460111c044601118112020000044608105204308105220141101161001101121004840111008880111004c80121004840112008804220108105240508101204048105400604440112004440241404101 (by decide +kernel)

def state221_80 : List Sig := [0xffffffffffffffff00000000000000000000000000000000,input 6,0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 0,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_80 : Impossible true (goalAt 221) 5 state221_80.toFinset :=
  node_ok cuts221 [] 0x1101054041105044041101104044414044041101044201101242001110044601518044701118104044404104044801044045840044044840121004440222004440120004800104044404110004400110104101240101101240501101204308105204148805220108804204149014204044480 (by decide +kernel)

def state221_81 : List Sig := [0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 7,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 0,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_81 : Impossible true (goalAt 221) 6 state221_81.toFinset :=
  node_ok cuts221 [⟨state221_30,exclude221_30⟩,⟨state221_76,exclude221_76⟩,⟨state221_52,exclude221_52⟩,⟨state221_47,exclude221_47⟩,⟨state221_78,exclude221_78⟩,⟨state221_79,exclude221_79⟩,⟨state221_80,exclude221_80⟩] 0x80018410110404810530200c00480014c08011200810510404410111100410111001001611010440011100440411011001610404410115050110104404410140028410115052000411050410104404110124050110104404810524200900424050908024050810504404110115140110104404444005414150115140150504414444004404110110404111810404440440024440410406000310404440404460480104405001f044049080044601108044041118044049080400249080400a9002a04440810504460810522031000920430810580008810522030111822015000904460111811100151c05461000905470111c111001118044604101222004800110104840120004101121004101110108880110101101121001101242005850161001101161401101242004840121008105121008804240508880220108105222008105240504840240520001121004840111008880111020000222008880111004840111010029400608101 (by decide +kernel)

def state221_82 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_82 : Impossible true (goalAt 221) 5 state221_82.toFinset :=
  node_ok cuts221 [⟨state221_36,exclude221_36⟩,⟨state221_60,exclude221_60⟩,⟨state221_77,exclude221_77⟩] 0x111004840222104440054041101044141101111009040800084440110404410110504818044601518044701118044401101044201101242001118241020001044601118110520000110501101121001101222004840241008880121004810120404818110501101242009040044041101104044414044048101 (by decide +kernel)

def state221_83 : List Sig := [0x5555555555555555555500005555000055555555555555555555000055550000,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 6,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 2,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_83 : Impossible true (goalAt 221) 5 state221_83.toFinset :=
  node_ok cuts221 [] 0x214048101204148101111004840206104440110404410110504818054041101044141101204008100204049010120404810120604414044001100044048180300408101241008101104041101204049010044049010204049010204041118044701518044604840044601110044404414400544414044609080 (by decide +kernel)

def state221_84 : List Sig := [0xf0f0f0f0f0f0f0f0f0f00000f0f00000f0f0f0f0f0f0f0f0f0f00000f0f0000,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 6,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 0,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_84 : Impossible true (goalAt 221) 5 state221_84.toFinset :=
  node_ok cuts221 [⟨state221_48,exclude221_48⟩] 0x8101204208101220041110044604414800004414054041508054049480220008800204049010120404810120604414054044840054048880300408101241008101110009400250009010054049010204049010204041118044701118054604440222004840111004818110504410110401101 (by decide +kernel)

def state221_85 : List Sig := [0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 6,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 0,input 2,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_85 : Impossible true (goalAt 221) 6 state221_85.toFinset :=
  node_ok cuts221 [⟨state221_82,exclude221_82⟩,⟨state221_83,exclude221_83⟩,⟨state221_49,exclude221_49⟩,⟨state221_61,exclude221_61⟩,⟨state221_84,exclude221_84⟩,⟨state221_67,exclude221_67⟩,⟨state221_78,exclude221_78⟩] 0x21414444021404810140058810121416000620414810111100810123210444011100484040058484023212000522210484011100444011051001611040481811100441011050444011050481840058481805416000405404110111100110105414444004414110140058110120404111820404880840048810820406000320404880804460880140048111804460444005470151840048151c044704440044601118400b1002c0444100120446011181105100121105100124005a000211050111811050110180004110124200111804420110104460110124201001224200810112100880024040888022000810122200810124040484024040481822200481011050484012040481812100481811050888011050110122200110124200484012100110112100110124200888022200c04011050c01020405001620404c04080000904020404441420405002b400544101240401101240008101242009000240409080240408101044041101 (by decide +kernel)

def state221_86 : List Sig := [0x55005500550055005500550055005500550055005500550000000000000000,input 6,input 7,input 0,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_86 : Impossible true (goalAt 221) 5 state221_86.toFinset :=
  node_ok cuts221 [] 0x9800220008810220005800120004810120001501044041105044048c00220008804220004c0012000480412000110004400110124200111005440111404440810020400810122000410010400410112000480022000c040120004840044045840044044440222104440121004140240408800301008800110104800121004800 (by decide +kernel)

def state221_87 : List Sig := [0xafafafafafafafafafafafafafafafafafafafafafafafafaaaaaaaaaaaaaaaa,input 6,input 7,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_87 : Impossible true (goalAt 221) 4 state221_87.toFinset :=
  node_ok cuts221 [] 0x250009400250401101150004400110404400044045140044044140230008c0020404941013000440010404440011000c400301004400044041108044044440044401110044604440204048108204048c01104044400104044400 (by decide +kernel)

def state221_88 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0000000000000000,input 6,input 7,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 0,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_88 : Impossible true (goalAt 221) 5 state221_88.toFinset :=
  node_ok cuts221 [⟨state221_87,exclude221_87⟩] 0x9400250009410044045400110004410110001101044201101242001110214048508214048c01114044400114044400044045840044044840230008c0021404941013000440011404440011000c400301004400111001101151001101111001118800001118111008884121004440204048101301008501104044400111004400 (by decide +kernel)

def state221_89 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,input 7,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 0,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_89 : Impossible true (goalAt 221) 6 state221_89.toFinset :=
  node_ok cuts221 [⟨state221_86,exclude221_86⟩,⟨state221_37,exclude221_37⟩,⟨state221_41,exclude221_41⟩,⟨state221_63,exclude221_63⟩,⟨state221_88,exclude221_88⟩,⟨state221_79,exclude221_79⟩,⟨state221_82,exclude221_82⟩] 0x4404c04030140110104404c08080018110104404908024200110105404110104414110111100484022210444011100c04080014444031200444011100c08080010444011101001804404110804404908004460151804470111804440111830102000304460111830202000204460111840032000104460110116100110112100484030100888012100888012100484022202000012100484040064810130100c080241404101 (by decide +kernel)

def state221_90 : List Sig := [0xaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 6,input 7,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_90 : Impossible true (goalAt 221) 5 state221_90.toFinset :=
  node_ok cuts221 [] 0x4404810130140110104404410111050110105404110104414110111100484020610444021404810120414810111000440011010410104404584004404484020404c04020404484012000480010404440430000c000301004101044041108044050015044601518044701118044401110044604840204048108204041118104044404104044801 (by decide +kernel)

def state221_91 : List Sig := [0xf0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 6,input 7,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 0,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_91 : Impossible true (goalAt 221) 5 state221_91.toFinset :=
  node_ok cuts221 [] 0x110124010901404404110110404441404404110104420110124200111020414810c20414880510404440410404480104460151804470111804404584004404484022010880420414901412000480010404440430000c000301004101054041101044141101111004840222004440204048101204144440110004400110104101 (by decide +kernel)

def state221_92 : List Sig := [0xffffffffffffffff00000000000000000000000000000000,input 6,input 7,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 0,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_92 : Impossible true (goalAt 221) 6 state221_92.toFinset :=
  node_ok cuts221 [⟨state221_90,exclude221_90⟩,⟨state221_91,exclude221_91⟩,⟨state221_64,exclude221_64⟩,⟨state221_80,exclude221_80⟩] 0x4404c04030140110104404410111050110105404110104414110111100484022210444011100c0408000c444011000440011010410104404110804404908004460151804470111804440111830102000204460410111010410112004110116100110112100484030100888012100480012000410111010c00030100410124200110124200110140060444080004444040030111880000111822200484022200484020404c080 (by decide +kernel)

def state221_93 : List Sig := [0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 0,input 2,input 4,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_93 : Impossible true (goalAt 221) 7 state221_93.toFinset :=
  node_ok cuts221 [⟨state221_28,exclude221_28⟩,⟨state221_32,exclude221_32⟩,⟨state221_35,exclude221_35⟩,⟨state221_50,exclude221_50⟩,⟨state221_65,exclude221_65⟩,⟨state221_68,exclude221_68⟩,⟨state221_74,exclude221_74⟩,⟨state221_81,exclude221_81⟩,⟨state221_85,exclude221_85⟩,⟨state221_89,exclude221_89⟩,⟨state221_92,exclude221_92⟩] 0x80028c04010404c00040058810130200c00080024c04030200c0404005881011040441014000c90100440490004005481012420090004000c90102420090104005481010440411014005854140440411014005441014000c41014000c54148002044144005441010440411014006085051110085014006081014006081014006085058001c8105400608101111008101400604404800184400400604101111004400400604404111004404400604101400604101400601505111001501400601101151401101400601505151401105400601101111001101400608c84111004440400604840400604840400608c848001488844006048401110044404003081010446081014003088084003081084003081018001081014003088080446088014003041010446041014003044044003044044003041018000c410140030440404460480140054110140054110140030908004460110840030110104460110140054908040054908040061001804460111840060444005470151840061000c05470111c4006044400446011184005100144005011108000881011210088004006490102220088008000481012220081014006490101210090104005841012220048004006444041210048008000041011210041014005844042220044044005411011210011014000c90801614058404000c1101161401101400549080121004840 (by decide +kernel)

def state221_94 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0a0a0a0a0a0a0a0a,input 7,input 0,input 6,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_94 : Impossible true (goalAt 221) 5 state221_94.toFinset :=
  node_ok cuts221 [] 0x150004400110404400250009400250401101064041101044241101130004400110204400230008c0023020810111000c400301004400054001500044044140054401d10054601510114004400104044400214008500204048c08044041105044041501111008884121004440104044400104044400044401110105001510204048105204048501 (by decide +kernel)

def state221_95 : List Sig := [0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00aa00aa00aa00aa,input 7,input 0,input 6,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_95 : Impossible true (goalAt 221) 5 state221_95.toFinset :=
  node_ok cuts221 [] 0x160004800120404800260008800220408800054041101044141101130004800120104800230008800220108800120008800301004800064001900044044140064401d10064501910124004800104044800224008800204048800044041109044041901111008884111004840104044800104044800044401110105001910204048800204048800 (by decide +kernel)

def state221_96 : List Sig := [0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000aaaa0000aaaa,input 7,input 0,input 6,input 2,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_96 : Impossible true (goalAt 221) 5 state221_96.toFinset :=
  node_ok cuts221 [] 0x160005800160204101260009000240209000111004840222104440150005400150104101250009000240109000340009000301009000044001900044201100044001500044101100044005100104041100044009000204041100044041109064041101044041105054041101044044404104041101105001100044041100044049000204049000 (by decide +kernel)

def state221_97 : List Sig := [0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,0xffffffffffffffffffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaa,input 7,input 0,input 2,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_97 : Impossible true (goalAt 221) 5 state221_97.toFinset :=
  node_ok cuts221 [⟨state221_36,exclude221_36⟩] 0x22404810120424810112040481012060441406404110104424110111100484022210444021404810120414810111040441011050481805404110104414110104500194080000114004500154020610114020404904020404880904440110104500110111014880804404810124100110111010110104405002d (by decide +kernel)

def state221_98 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaa,input 7,input 0,input 6,input 2,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_98 : Impossible true (goalAt 221) 6 state221_98.toFinset :=
  node_ok cuts221 [⟨state221_37,exclude221_37⟩,⟨state221_94,exclude221_94⟩,⟨state221_95,exclude221_95⟩,⟨state221_96,exclude221_96⟩,⟨state221_97,exclude221_97⟩] 0x110110406000404404110120404c050044060003044041101400b4190104404110904404490110404410910404890120404810920406000212100484040050150104404110504404444012100888411100450110404410510404850120404810520406000111100444040000410120404c04010404440404404514004404414010500484080000414010500444020610414010404414010404440520404c040204048809044408808 (by decide +kernel)

def state221_99 : List Sig := [0xf0f0f0f0f0f0f0f0a0a0a0a0a0a0a0a,input 7,input 0,input 6,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_99 : Impossible true (goalAt 221) 5 state221_99.toFinset :=
  node_ok cuts221 [] 0x5400110004410110009000240009010044041901044041109044044c00110004408110008800220008808204144400300004480110001500054001101105001510074401518054404500110004101110008100204008105220201101044141101054044440222004840111004101110004101110001110044404140054408101 (by decide +kernel)

def state221_100 : List Sig := [0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,0xffffffffffffffffaaaaaaaaaaaaaaaa,input 7,input 0,input 2,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_100 : Impossible true (goalAt 221) 5 state221_100.toFinset :=
  node_ok cuts221 [⟨state221_38,exclude221_38⟩] 0x8800220008808240401901044041109044044440121008884111008c0822020880c220201501044041105044041140065020000045001140055008184045008100204008180220201101045001101110144810120404818110504410110404414120601110044401140110508101044044404044049080240009000240401101 (by decide +kernel)

def state221_101 : List Sig := [0xffffffffffffffffaaaaaaaaaaaaaaaa,input 7,input 0,input 6,input 2,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_101 : Impossible true (goalAt 221) 6 state221_101.toFinset :=
  node_ok cuts221 [⟨state221_99,exclude221_99⟩,⟨state221_39,exclude221_39⟩,⟨state221_100,exclude221_100⟩] 0x1101104060002044049000240009010044041901044041109044044901104044109104048800220008808240401501044041105044044440121008884111004501104044105104048c0822020880c22020c00030000c080104041101145001101105004140121020001105004140111008184105004101105004101110148100204008180220201101242001101242004840222004840222004440800004440400004101110104101302001110044404140206008101 (by decide +kernel)

def state221_102 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa,input 2,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_102 : Impossible true (goalAt 221) 5 state221_102.toFinset :=
  node_ok cuts221 [⟨state221_0,exclude221_0⟩] 0x146001101044044180145001101044044140044044101242001101064041101044241101126004840121004180121004140222004140124044101104244101054041101044141101111004840222104440116004440111004180111004140800004140114044101104144101044401110105009050104044404104048809104048808104044405 (by decide +kernel)

def state221_103 : List Sig := [0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 7,0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa,input 2,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_103 : Impossible true (goalAt 221) 5 state221_103.toFinset :=
  node_ok cuts221 [⟨state221_1,exclude221_1⟩] 0x4810120404818110508901204048109204041940045008880045001901044041109044044440121008884111004410110404414120608501204048105204041540045020000045001501044041105044048101206008101220241110044401140110501101110101101206008808044048101242001101045001101044044405 (by decide +kernel)

def state221_104 : List Sig := [0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 7,0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa,input 6,input 2,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_104 : Impossible true (goalAt 221) 6 state221_104.toFinset :=
  node_ok cuts221 [⟨state221_102,exclude221_102⟩,⟨state221_2,exclude221_2⟩,⟨state221_103,exclude221_103⟩] 0x44044101800081101242001101044048180044048101242001101145001101044044140064041101044241101124044101104244101222004840121008180224048101204248101121004140222004140054041101044141101111004840222104440114044101104144101216004440111008180214048101204148101111004140800044140110104101204060000104044140104044101110148101206008101220241110044404140400108808 (by decide +kernel)

def state221_105 : List Sig := [0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa,input 0,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_105 : Impossible true (goalAt 221) 5 state221_105.toFinset :=
  node_ok cuts221 [⟨state221_0,exclude221_0⟩,⟨state221_40,exclude221_40⟩] 0x5480044041101112001101104049014044041101054041105044041901044041109044044c8012100484011200490110404410910404484011100888011100110114500110110500414012102000110500111010404880c10404440510500444080000414010404440410404880c111004480111009050114044101104144101 (by decide +kernel)

def state221_106 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa,input 0,input 2,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_106 : Impossible true (goalAt 221) 6 state221_106.toFinset :=
  node_ok cuts221 [⟨state221_102,exclude221_102⟩,⟨state221_13,exclude221_13⟩,⟨state221_41,exclude221_41⟩,⟨state221_105,exclude221_105⟩] 0x24200110104404908004404c04030140110104404410124200110106404110104424110122200484012100888012100c04022200484012404410110424410105404110104414110111100484022210444031200444011100c08011100c0408000c444011404410110414410104404514004404414010500484080008414010500444080004414004440414020502000010500410110500410111014c04030200c040241404101110104101400308101 (by decide +kernel)

def state221_107 : List Sig := [0xff00ff00ff00ff00ff00ff00ff00ff000f000f000f000f000a000a000a000a,input 7,input 0,input 6,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_107 : Impossible true (goalAt 221) 4 state221_107.toFinset :=
  node_ok cuts221 [] 0x150004400110404400260008800220408800110008800301004400054001500044044140114004400104044400224008800204048800044041105044041501104044400104044400044401110105001510204048800204048800 (by decide +kernel)

def state221_108 : List Sig := [0xffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0a0a0a0a0a0a0a0a,input 7,input 0,input 6,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_108 : Impossible true (goalAt 221) 5 state221_108.toFinset :=
  node_ok cuts221 [⟨state221_107,exclude221_107⟩] 0x540011000441011000110120404c050044041105044041101054041901044041109044044c0011000440811000890120404810920406000011100484011100440020404c040110004400104044101110001500054001101105001510074401518054404500110004101110008101301008101220241110044404140054408105 (by decide +kernel)

def state221_109 : List Sig := [0xf0f0f0f0f0f0f0f0a0a0a0a0a0a0a0a0f0f0f0f0f0f0f0f0a0a0a0a0a0a0a0a,input 0,input 6,input 3,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_109 : Impossible true (goalAt 221) 6 state221_109.toFinset :=
  node_ok cuts221 [⟨state221_108,exclude221_108⟩,⟨state221_99,exclude221_99⟩] 0x24040110124000810124200900024040908024040810104404110115040110115000440040010440015041000411040440004404440022020484022000810122200880022020888022020810112100810106424484006404110116140110106424585004424110112100110113020888013000440012100440013020484011020440022200440030100440011000810131200c40030100c4803010081011100044002040415102140088082160085002040485802040488080544088080440441400540090800544015000440415100440490801050041404009c1510054404840074601d104009c1d180546048400544015101040415101140044001050044001040441401040444000544044002040444402040485058000481052040600002040485051110085010440444400440415051514011050440454500440415051110015011210044401110088804003c888012101000f121008880111004440104050026104044400111004400104044440104044400400a04400105004440044401510400c0111010501000e105001510111001510 (by decide +kernel)

def state221_110 : List Sig := [0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,0xf0f0f0f0f0f0f0f0a0a0a0a0a0a0a0a0f0f0f0f0f0f0f0f0a0a0a0a0a0a0a0a,0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa,input 0,input 3,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_110 : Impossible true (goalAt 221) 5 state221_110.toFinset :=
  node_ok cuts221 [⟨state221_42,exclude221_42⟩] 0x220008800220208101130404410110604410064041101044241101204048808204048808045001940800001140054401101045001101110148101220208101220204400110001101242008101204148101214044440222004840111001140400101140055004818044041105044041501240009000240401101 (by decide +kernel)

def state221_111 : List Sig := [0xf0f0f0f0f0f0f0f0a0a0a0a0a0a0a0a0f0f0f0f0f0f0f0f0a0a0a0a0a0a0a0a,0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa,input 0,input 6,input 3,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_111 : Impossible true (goalAt 221) 6 state221_111.toFinset :=
  node_ok cuts221 [⟨state221_43,exclude221_43⟩,⟨state221_110,exclude221_110⟩] 0x240009000240401101044044101800041101242001101044049080220008800220208101064041101044241101124044101104244101222004840121008880104048101301004101110008101220208101220201101145001101105004140121020000105004101105004405054408101220208101220208101204148101214041101044141101054044440222004840111004101104144101114044140400104140111010000 (by decide +kernel)

def state221_112 : List Sig := [0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 7,0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa,input 0,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_112 : Impossible true (goalAt 221) 5 state221_112.toFinset :=
  node_ok cuts221 [⟨state221_1,exclude221_1⟩,⟨state221_46,exclude221_46⟩] 0x120404810120604414220108804220308105121004440222004440064041101044241101045001940800041140044408105220308105220301140055020000045001101045001101110148105220308105220304410110404414120601101110101101242008101044049004240501101044041501044141101 (by decide +kernel)

def state221_113 : List Sig := [0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 7,0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa,input 0,input 6,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_113 : Impossible true (goalAt 221) 6 state221_113.toFinset :=
  node_ok cuts221 [⟨state221_99,exclude221_99⟩,⟨state221_2,exclude221_2⟩,⟨state221_47,exclude221_47⟩,⟨state221_105,exclude221_105⟩,⟨state221_112,exclude221_112⟩] 0x440441018001011012420011010440490800440490042405011010440415010441411010640411010442411011240441011042441012220048401210088802201088042203081051210044402220044401101041012041600031040441011140441051040411011450011011050041401210200021050041011050044050444081052203081052203041401110200011050081052203081052203044408000044404001c8101 (by decide +kernel)

def state221_114 : List Sig := [0x5555555555555555555500005555000055555555555555555555000055550000,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa,input 2,input 3,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_114 : Impossible true (goalAt 221) 5 state221_114.toFinset :=
  node_ok cuts221 [⟨state221_14,exclude221_14⟩] 0x8800220008808204044810120404818110501901044041109044048501204048105204044440121008884111004410110404414120601501044041105044048100204008101220201100044001101206001101204049010044049010204049010204041140222001940045001140800001540045004414045001110044404405 (by decide +kernel)

def state221_115 : List Sig := [0xf0f0f0f0f0f0f0f0f0f00000f0f00000f0f0f0f0f0f0f0f0f0f00000f0f0000,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa,input 0,input 3,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_115 : Impossible true (goalAt 221) 5 state221_115.toFinset :=
  node_ok cuts221 [⟨state221_14,exclude221_14⟩,⟨state221_48,exclude221_48⟩] 0x220008800220208101120404810120604414074041501054241501204048808204048808045001940800041140044401501045001501110048101220208101220204400110001501252009400250009010054049010204049010204044440222004840111001140800001140055004818110504410110401101 (by decide +kernel)

def state221_116 : List Sig := [0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa,input 0,input 2,input 3,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_116 : Impossible true (goalAt 221) 6 state221_116.toFinset :=
  node_ok cuts221 [⟨state221_97,exclude221_97⟩,⟨state221_100,exclude221_100⟩,⟨state221_114,exclude221_114⟩,⟨state221_15,exclude221_15⟩,⟨state221_49,exclude221_49⟩,⟨state221_103,exclude221_103⟩,⟨state221_115,exclude221_115⟩,⟨state221_110,exclude221_110⟩,⟨state221_112,exclude221_112⟩] 0x8808121008800204048880220008808222008808204044840204044818222004810110504840120404818121004818110508880110501909222001901044044840044041909121001109044048880044048505111008501204050004204048505800208105204044440204048c84111004440121010004121008c844003c88841210044401110044148001c44101206044401104044141110044141206100041206015058001815010440444400440415051110011050440500040440481010450081012202100122202081018001481012202011402202100120450011401210100120650100124003e000412100114004501001204500114011101001205501001240012000311100114004501001240010111004406000204404908004500114004404114004404908040048440520404441420404880880004880820406000020404880811050880804405002d044049080110504404044044414044049080400b49080240401101240008101242009000240409080240408101044041101 (by decide +kernel)

def state221_117 : List Sig := [0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa,input 0,input 6,input 2,input 3,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_117 : Impossible true (goalAt 221) 7 state221_117.toFinset :=
  node_ok cuts221 [⟨state221_98,exclude221_98⟩,⟨state221_101,exclude221_101⟩,⟨state221_16,exclude221_16⟩,⟨state221_50,exclude221_50⟩,⟨state221_104,exclude221_104⟩,⟨state221_106,exclude221_106⟩,⟨state221_109,exclude221_109⟩,⟨state221_111,exclude221_111⟩,⟨state221_113,exclude221_113⟩,⟨state221_116,exclude221_116⟩] 0x9010044049000204049080240009010242009010204041101044050004044041101104050004104050003400120009104041101044050003242009080400b41101044050003044041101400b4908024200880812100880020404888022000880822200880820404484020404190912100190104404585004404190916140110904404484004404490922200490110404484010404490912100410910404888010405002f22200888040050484012101002f12100484040050888022200850511100850120405000e204048505800208105204044440204041505111001501044045450044041505151401105044044440044048c8411100444012101002f121008c84400bc888412100444011100450540010450110404444010404450511100410510405000e10405000e8001e000640000444011101000e11100444040001000e40000c04010404410120405000420404c04080014c04020404410110405001c400304404204044140204048808400308808204060004204048808105008808044044140044049080145405140044045150044049080105004140400bc4140105004840400bc484040031002f8000c484010500414040038414010500444040038444040031000e80008444010500414010405000410405000c10500414040031000c11015001740010111020405002e204048808800048808204060000204048808400b88808 (by decide +kernel)

def state221_118 : List Sig := [0xffff0000ffff0000ffff0000ffff0000aaaa0000aaaa0000aaaa0000aaaa,0xfffffffffffffffffffffffffffffffffafafafafafafafafafafafafafafafa,input 0,input 7,input 3,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_118 : Impossible true (goalAt 221) 5 state221_118.toFinset :=
  node_ok cuts221 [] 0x410120404c080104044400110004101120204800120004808104048901204048109204044840111008880111009000104044404104041104044101904044301104204049004204041104044001101110104101044041101044241901044041101240108101044048180044041101044110032 (by decide +kernel)

def state221_119 : List Sig := [0xfffffffffffffffffffffffffffffffffafafafafafafafafafafafafafafafa,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 0,input 7,input 3,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_119 : Impossible true (goalAt 221) 6 state221_119.toFinset :=
  node_ok cuts221 [⟨state221_51,exclude221_51⟩,⟨state221_118,exclude221_118⟩] 0x10404810130200410111010410110404440411000440010404480804404410111050110104404810124200110180004110104405000a15100110104404444012000480012020410106404110104424110122404810120424810112100888022200484012100444022200444022031001e1040444041040444040440490800440481802060048408000048402040481802202411144001d0000 (by decide +kernel)

def state221_120 : List Sig := [0xffff0000ffff0000ffff0000ffff0000aaaa0000aaaa0000aaaa0000aaaa,0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 7,input 0,input 3,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_120 : Impossible true (goalAt 221) 5 state221_120.toFinset :=
  node_ok cuts221 [] 0x410124010c08010404440011000440410404480012000480810404980424010900c240104840111008880111001100144004101044001100064001108044001100240108105044001100054001104044009000044044404104041101044041109064041101105001100044041100044049004204141101044041105054041101 (by decide +kernel)

def state221_121 : List Sig := [0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 7,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 0,input 3,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_121 : Impossible true (goalAt 221) 6 state221_121.toFinset :=
  node_ok cuts221 [⟨state221_52,exclude221_52⟩,⟨state221_120,exclude221_120⟩] 0x11010410110404440410404810530200410111000440011010410104404410111050110180004110104405003304404810524200110104404150104414110112000480012020410106404110104424110112100888022200484022414810520434810512100444022200444010404440410404440404404908004404818020600484080000484004440810520600880d4001c4440206004440400004440400c44440220308101 (by decide +kernel)

def state221_122 : List Sig := [0xff00ff00ff00ff00ff00ff00ff00ff00af00af00af00af00aa00aa00aa00aa,input 6,input 0,input 7,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_122 : Impossible true (goalAt 221) 4 state221_122.toFinset :=
  node_ok cuts221 [] 0x260008800220408800150004400110404400064001900044044140224008800204048800124004400104044400110008800301004400044041109044041901204048800204048800044401110105001910104044400104044400 (by decide +kernel)

def state221_123 : List Sig := [0xffffffffffffffffffffffffffffffffafafafafafafafafaaaaaaaaaaaaaaaa,input 6,input 0,input 7,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_123 : Impossible true (goalAt 221) 5 state221_123.toFinset :=
  node_ok cuts221 [⟨state221_55,exclude221_55⟩,⟨state221_122,exclude221_122⟩] 0x44048101301401101150004400110404400111401101044044440064041101044241101224048101204248101130004400110204400800044440121004440220201101145001101105004140121020000105008101301008101220244101110004101110001110110008101301004400110004101104044400 (by decide +kernel)

def state221_124 : List Sig := [0xafafafafafafafafaaaaaaaaaaaaaaaaafafafafafafafafaaaaaaaaaaaaaaaa,input 6,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 7,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_124 : Impossible true (goalAt 221) 5 state221_124.toFinset :=
  node_ok cuts221 [] 0x1101204049080044045140044041101105005400110004410110001901044041109044048901204048109204044840105008880105004c00110004408110008808110008101312004400110004101104044400044044450044044440111008880121004440204048180204048809044401110105004440104044400104044400 (by decide +kernel)

def state221_125 : List Sig := [0xffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0000000000000000,input 6,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 0,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_125 : Impossible true (goalAt 221) 5 state221_125.toFinset :=
  node_ok cuts221 [⟨state221_56,exclude221_56⟩] 0xd040044041101301005400110004410110001101204045440044041901044041109044044840301008880121004c00110004408110008901204048109204041101242001101206008180121020000121001110114044400114044400204044440204048809110004501114044400110004101111004400220208101204044440 (by decide +kernel)

def state221_126 : List Sig := [0xf0fffff0f0fffff0000ffff0000ffff0f0fafaf0f0fafaf0000aaaa0000aaaa,input 6,input 0,input 7,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_126 : Impossible true (goalAt 221) 4 state221_126.toFinset :=
  node_ok cuts221 [] 0x260009000240209000130004400110204400044001900044201100044009000204041100044004400104041100110009000301004400044041109064041101044049000204049000105001100044041100044044400104044400 (by decide +kernel)

def state221_127 : List Sig := [0xffff0000ffff0000ffff0000ffff0000aaaa0000aaaa0000aaaa0000aaaa,0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0000000000000000,input 6,input 0,input 7,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_127 : Impossible true (goalAt 221) 5 state221_127.toFinset :=
  node_ok cuts221 [⟨state221_126,exclude221_126⟩] 0x9800240009008240004c0011000440811000110006400110804400110024000810104400110011000450104400440024000d04011000444022200484011100444024000d040240004440044005140044004101044041109064041101044049000204049000105001100044041100044044400114044400044044440800001101 (by decide +kernel)

def state221_128 : List Sig := [0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0000000000000000,input 6,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 0,input 7,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_128 : Impossible true (goalAt 221) 6 state221_128.toFinset :=
  node_ok cuts221 [⟨state221_123,exclude221_123⟩,⟨state221_124,exclude221_124⟩,⟨state221_125,exclude221_125⟩,⟨state221_57,exclude221_57⟩,⟨state221_127,exclude221_127⟩] 0x4404810124200110180010110104405003415000440011040440006404110104424110122404810120424810112100888022200484013000440011020440022020110124200110120600818012102000312100810120600880904440450111000450111000440020404c480110004400114044501110004440044045440044044440222004840111004440204060002204044440206020001111004440400120000111004101 (by decide +kernel)

def state221_129 : List Sig := [0xf0f0fffff0f0fffff0f0fffff0f0fffff0f0fafaf0f0fafaf0f0fafaf0f0fafa,0xffff0000ffff0000ffff0000ffff0000aaaa0000aaaa0000aaaa0000aaaa,input 0,input 7,input 3,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_129 : Impossible true (goalAt 221) 5 state221_129.toFinset :=
  node_ok cuts221 [] 0xd000240009040240004800120004808104049800240009008240001100144004101044001100064001108044001100240008101044001100054001104044001501110104101054041501054241d01054041501240008101240008180044001501044001101110004400104044808111004840222004440250009000204049000 (by decide +kernel)

def state221_130 : List Sig := [0xffffffffffffffff0000ffff0000ffffffffffffffffffff0000aaaa0000aaaa,input 6,input 0,input 7,input 2,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_130 : Impossible true (goalAt 221) 5 state221_130.toFinset :=
  node_ok cuts221 [] 0x980024000900824000490110404410910404110904404190104404444012100888411100940024000900424000450110404410510404110504404150104404110006400110804400110005400110404400110024000810104400110010500410104400110010500110104400410124000c040240004404044049000204049000 (by decide +kernel)

def state221_131 : List Sig := [0xffff0000ffff00000000000000000000aaaa0000aaaa,input 6,input 0,input 7,input 2,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_131 : Impossible true (goalAt 221) 5 state221_131.toFinset :=
  node_ok cuts221 [] 0x980024000900824000480012000480811010444012100888411100940024000900424000440011000440412020110006400110804400110005400110404400110024000810104400110010400114004400c000240009040240001101044241901044041101044141501044041101240008101240008180044001101044004101 (by decide +kernel)

def state221_132 : List Sig := [0xfff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0,input 3,0xffff0000ffff0000ffff0000ffff0000aaaa0000aaaa0000aaaa0000aaaa,input 0,input 7,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_132 : Impossible true (goalAt 221) 5 state221_132.toFinset :=
  node_ok cuts221 [] 0xd000240009040240001100144004101044001100240008101044001100064101508044001100054001104044001101110104101044041101240008101240004140044001101044001101054241905044041101044141501044044804104044408104049804240009408240004840110004400110104101250009000240109000 (by decide +kernel)

def state221_133 : List Sig := [0xffff0000ffff0000ffff0000ffff0000aaaa0000aaaa0000aaaa0000aaaa,input 0,input 7,input 2,input 3,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_133 : Impossible true (goalAt 221) 6 state221_133.toFinset :=
  node_ok cuts221 [⟨state221_129,exclude221_129⟩,⟨state221_130,exclude221_130⟩,⟨state221_131,exclude221_131⟩,⟨state221_120,exclude221_120⟩,⟨state221_132,exclude221_132⟩,⟨state221_127,exclude221_127⟩] 0x34100410134000900030200900034100c080241009000104049000120208880120004101121004800120204840120204101222004101260204840260009000222009000260208880240209000121009000110120005110004101111004400110104440110104101400d44101232104440111004840400d44840232120004222104840111004440250104440250009000400d49000250120003240109000111009000104041100044004404145005100104045140104044404044001100400d81100044004840064201900400d81908044204840044001100400d81100044004440054101500400d81504044104440044001100204041100044009000206009000204048180204049000044001100104041101044044404800084404104060001104044404044041101222001101044044840064241109222001909064044840044041101400d41101044044440054141105800001505054044440044041101204041101044049000242009000204049080204049000044049000206009080105001100044041100206001101044041100242001100 (by decide +kernel)

def state221_134 : List Sig := [0xffff0000ffff0000ffff0000ffff0000aaaa0000aaaa0000aaaa0000aaaa,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 0,input 7,input 2,input 3,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_134 : Impossible true (goalAt 221) 6 state221_134.toFinset :=
  node_ok cuts221 [⟨state221_58,exclude221_58⟩,⟨state221_118,exclude221_118⟩] 0x10404810130200410111010410110404440412000480012020410122404810120424810112100888022200484011000440011010410111100484022210444021404810120414810111101003580004444024000410111010410111010818012102000012100818011100818411100810120600880904400110111010410104404110104424190104404110104414150104404110124200810104404818004404110124201002d (by decide +kernel)

def state221_135 : List Sig := [0xffffffffffffffffffff0000ffff0000aaaaaaaaaaaaaaaaaaaa0000aaaa0000,input 6,input 0,input 7,input 2,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_135 : Impossible true (goalAt 221) 5 state221_135.toFinset :=
  node_ok cuts221 [⟨state221_59,exclude221_59⟩] 0x220008800220208101120004800120204404064041101044241101111004840222104440214048101204148101110004400110104808054041101044141101206004840800004840206004440206104440204008100204048808206004404110144404044001100044048180110108101112108101104041101400b41101240009000242001101 (by decide +kernel)

def state221_136 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 0,input 2,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_136 : Impossible true (goalAt 221) 5 state221_136.toFinset :=
  node_ok cuts221 [⟨state221_60,exclude221_60⟩,⟨state221_8,exclude221_8⟩] 0x4840241008880121001901044041109044048901204048109204044440121008884111004440241020001111001501044041105044048501204048105204048180121020000121008180111008184111001110044044180044048180204044414204048809204048808204044414241001101044044484044044101110501101 (by decide +kernel)

def state221_137 : List Sig := [0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 6,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 0,input 7,input 2,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_137 : Impossible true (goalAt 221) 6 state221_137.toFinset :=
  node_ok cuts221 [⟨state221_135,exclude221_135⟩,⟨state221_131,exclude221_131⟩,⟨state221_97,exclude221_97⟩,⟨state221_136,exclude221_136⟩,⟨state221_103,exclude221_103⟩,⟨state221_61,exclude221_61⟩,⟨state221_9,exclude221_9⟩] 0x224048101204248101121008880222004840120404810120604414064041101044241101111004840222104440214048101204148101111010013800184440110404410110504818054041101044141101220208180121020005121008180111008184111008101206008809044408180110520004110501101242001101206004414204060003204044414400120002110504101044048101242001101800041101044060000 (by decide +kernel)

def state221_138 : List Sig := [0xf0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0fafafafafafafafa,input 6,input 0,input 7,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_138 : Impossible true (goalAt 221) 5 state221_138.toFinset :=
  node_ok cuts221 [] 0x4404810124050110104404450111050110106404110104424110122404810120424810112000480012020450104404110404404414004450191404470111420404810420404880910400410011004440104440111004450414030000c000301004501044045440044044440111004840222004440204048808204044440110004400104044101 (by decide +kernel)

def state221_139 : List Sig := [0xffffffffffffffff0000000000000000aaaaaaaaaaaaaaaa,input 6,input 0,input 7,input 2,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_139 : Impossible true (goalAt 221) 6 state221_139.toFinset :=
  node_ok cuts221 [⟨state221_138,exclude221_138⟩,⟨state221_131,exclude221_131⟩,⟨state221_62,exclude221_62⟩] 0x110120404c05004404110111010441404404190104404110904404890120404810920404480012000480811010150104404110504404444012100888411100850120404810520404440011000440412020110114500110110500414012102000210500414011100818410500810130100810122024410010400414011010c00030000c040204041101800041101400b48880121008880121010000111020000111008101220208101301001110044408180105004101 (by decide +kernel)

def state221_140 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 0,input 2,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_140 : Impossible true (goalAt 221) 6 state221_140.toFinset :=
  node_ok cuts221 [⟨state221_102,exclude221_102⟩,⟨state221_63,exclude221_63⟩,⟨state221_10,exclude221_10⟩,⟨state221_136,exclude221_136⟩] 0x34100110104404c04004404c0808000c110104404810124200110106404110104424110112100c04022200484022200484012100888022404810120424810105404110104414110111100484022210444011100c04080008444031200444011100c08021404810120414810104404908004404818020600484080004484020600444020610444004440418010602000020600810120600810122024810122020810140030c04030200c040241404101 (by decide +kernel)

def state221_141 : List Sig := [0xffffffffffffffff00000000000000000000000000000000,input 6,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 0,input 2,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_141 : Impossible true (goalAt 221) 6 state221_141.toFinset :=
  node_ok cuts221 [⟨state221_64,exclude221_64⟩,⟨state221_11,exclude221_11⟩] 0xd04004404110130100110110404441404404190104404110904404484030100888012100480012000480810404150104404110504404444012100888411100444030102000111100440011000440410404110124200110120600818012102000012100818011100818411100111010404440410404c00130000c00010404440420404110124200110120404890120424810120404850120414810120600810120404880922020c080 (by decide +kernel)

def state221_142 : List Sig := [0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 0,input 7,input 2,input 3,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_142 : Impossible true (goalAt 221) 7 state221_142.toFinset :=
  node_ok cuts221 [⟨state221_65,exclude221_65⟩,⟨state221_104,exclude221_104⟩,⟨state221_12,exclude221_12⟩,⟨state221_119,exclude221_119⟩,⟨state221_121,exclude221_121⟩,⟨state221_128,exclude221_128⟩,⟨state221_133,exclude221_133⟩,⟨state221_134,exclude221_134⟩,⟨state221_137,exclude221_137⟩,⟨state221_98,exclude221_98⟩,⟨state221_139,exclude221_139⟩,⟨state221_140,exclude221_140⟩,⟨state221_141,exclude221_141⟩] 0x2000c10404410120404c08020406000b30200c08020404410110406000a1101044044001041011040600091040441014001044041101054140440411011040500031040454148002044141040411010440500030440411012040490802040500032420090802040411010440500038001e0006400b41101044050003044041101400b50003400b4480822200480010404484012000480812100480810404888010404190912100190104404585004404190916140110904404484004404890912100890120404888020404890922200810920404484020405001b12100484040050888022201001b222008880400504840121004404800144400104044440110004404111004404104050031104041505111001501044045450044041505151401105044044440044048c8411100444012101001b121008c844006c88841210044401110085051110085012040500312040485058001081052040444402040500311110044404000100314000100318000e000240000444011101001d4003088081040481801040444044003044041040600011040444042060044040440481800440490804003090800440500030440490802060081804006c81802060048404006c484040031001b800004840206004840400c4818020600444021610444040030858420610444020600444020405002e20405000c20600818040031000c22025001a400b81110 (by decide +kernel)

def state221_143 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,0xf5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 0,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_143 : Impossible true (goalAt 221) 4 state221_143.toFinset :=
  node_ok cuts221 [] 0x6404110104424110122404810120424810104440191004460111004440151004450111004400110004404814020400810020404880c111004840222004440054041101044141101214048101204148101044044101110501101 (by decide +kernel)

def state221_144 : List Sig := [0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 6,0xf5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 0,input 7,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_144 : Impossible true (goalAt 221) 5 state221_144.toFinset :=
  node_ok cuts221 [⟨state221_143,exclude221_143⟩] 0x8901204048109204044810120404818110501901044041109044041110064401118044408100204008101220301110054401114044401110104401140044401100044001101216004440121008880111008501204048105204044410110404414120601501044041105044044414204060000204044101044048101240501101 (by decide +kernel)

def state221_145 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,0xf5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 0,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_145 : Impossible true (goalAt 221) 5 state221_145.toFinset :=
  node_ok cuts221 [⟨state221_143,exclude221_143⟩] 0x1101112020000044041101204049014044041901044041109044044c80121004840112008901204048109204041100044001101105001110064401118044401110054401114044401110105004140044408100204008101220301501044041105044044440121008880111004480111004440241408501204048105204044101 (by decide +kernel)

def state221_146 : List Sig := [0xf5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 0,input 7,input 3,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_146 : Impossible true (goalAt 221) 6 state221_146.toFinset :=
  node_ok cuts221 [⟨state221_144,exclude221_144⟩,⟨state221_145,exclude221_145⟩] 0x400b8410110404810130200810180004c08011200810110404410115050110104404410140028410115052000011050410104404110124050110104404810124200810124050908024050810104404110112020888012000410112100480012020484012020410122200410106424484006404110116140110106424585004424110112100110122424484022404810122200810122424888020424810112100810110404111010400440410500410010404414010404440404440440404404414004400908004440110004404111004404908010500414040024111004440484006460191040024191804460484004440111020404111020400880c21600810020404858020404880c04440880c400201110044404440054501510400c41514044504440044401110110110004110004101111004400110104440110104101400104101054144440054041101151401101054145450044141101111001101222004440111004840400e04840222010038222004840111004440214144440214048101400a4810121415002a204148101111008101 (by decide +kernel)

def state221_147 : List Sig := [0xf0f0f0f0f0f0f0f05050505050505050f0f0f0f0f0f0f0f0000000000000000,input 6,input 0,input 7,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_147 : Impossible true (goalAt 221) 5 state221_147.toFinset :=
  node_ok cuts221 [] 0x250009400250401101150004400110404400064041101044241101230008c00230208101130004400110204400044001100044044140044401910044601110204008100204048c0811400440011004440011000c400301004400111001101151001101111008884121004440220208101301008101105001110105001110104044400111004400 (by decide +kernel)

def state221_148 : List Sig := [0xff00ff00ff00ff005500550055005500ff00ff00ff00ff0000000000000000,input 6,input 0,input 7,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_148 : Impossible true (goalAt 221) 5 state221_148.toFinset :=
  node_ok cuts221 [] 0x260008800220408800160004800120404800054041101044141101230008800220108800130004800120104800044001100044044140044401510044501110204008100204048800124004800120044800120008800301004800121001101161001101111008884111004840240408800301008800105001110105001110104044800121004800 (by decide +kernel)

def state221_149 : List Sig := [0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,0xffffffffffffffff5555555555555555ffffffffffffffff0000000000000000,input 0,input 7,input 2,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_149 : Impossible true (goalAt 221) 5 state221_149.toFinset :=
  node_ok cuts221 [] 0x224048101204248101120404810120604414064041101044241101111004840222104440214048101204148101110404410110504818054041101044141101044401910044601110044401510044501110204008100204041110044404110045001110044001100044049080220208101241008101104041101110501101044048101241001101 (by decide +kernel)

def state221_150 : List Sig := [0xffffffffffffffff5555555555555555ffffffffffffffff0000000000000000,input 6,input 0,input 7,input 2,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_150 : Impossible true (goalAt 221) 6 state221_150.toFinset :=
  node_ok cuts221 [⟨state221_147,exclude221_147⟩,⟨state221_148,exclude221_148⟩,⟨state221_149,exclude221_149⟩] 0x110120404c05004404110130202000204404110124200908004404190104404110904404890120404810920404888012100484022202000112100484040050150104404110504404444012100888411100850120404810520404c48011100444030202000011100444040000110004400110110500111006440111804440111005440111404440810020400810104440111010500414004440111010500414004440c04020404c040204044101220208101301008101 (by decide +kernel)

def state221_151 : List Sig := [0x5f005f005f005f0055005500550055000f000f000f000f0000000000000000,input 6,input 0,input 7,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_151 : Impossible true (goalAt 221) 4 state221_151.toFinset :=
  node_ok cuts221 [] 0x260008800220408800150004400110404400044001100044044140204008100204048800114004400110044400110008800301004400111001101151001101240408800301008800105001110105001110104044400111004400 (by decide +kernel)

def state221_152 : List Sig := [0x5f5f5f5f5f5f5f5f55555555555555550f0f0f0f0f0f0f0f0000000000000000,input 6,input 0,input 7,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_152 : Impossible true (goalAt 221) 5 state221_152.toFinset :=
  node_ok cuts221 [⟨state221_151,exclude221_151⟩] 0x44048101301401101150004400110404400064041101044241101224048101204248101130004400110204400044001100044044140044401910044601110204008100204041110114004400110044400110008101301004400111001101151001101111020000121004440220208101301008101105001110105001110104044400111004400 (by decide +kernel)

def state221_153 : List Sig := [0xffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0000000000000000,input 6,0x5555555555555555555555555555555500000000000000000000000000000000,input 0,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_153 : Impossible true (goalAt 221) 5 state221_153.toFinset :=
  node_ok cuts221 [] 0x15000440011040440004404810115100110106404110104424110113000440011020440022404810120424810104400110004404414004440191004460111011400440011004440020400810020404111030100110130140110130100484022200484020600c08011000c040110008808110004101111004400 (by decide +kernel)

def state221_154 : List Sig := [0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0000000000000000,input 6,0x5555555555555555555555555555555500000000000000000000000000000000,input 0,input 7,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_154 : Impossible true (goalAt 221) 6 state221_154.toFinset :=
  node_ok cuts221 [⟨state221_152,exclude221_152⟩,⟨state221_153,exclude221_153⟩] 0x4404810124200110115000440011040440006404110104424110122404810120424810113000440011020440004400110004404414004440191004460111020400810104440450011000440111000908004404908004404888012100888012100880820600c48011000c48011000440020404c480110004440044045440044044440222004840111004440204060001204044140044404140044404440400120000111004101 (by decide +kernel)

def state221_155 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,0x5555555555555555555555555555555500000000000000000000000000000000,input 0,input 2,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_155 : Impossible true (goalAt 221) 5 state221_155.toFinset :=
  node_ok cuts221 [⟨state221_143,exclude221_143⟩] 0x64041101044241101224048101204248101111004840222104440054041101044141101214048101204148101044401910044601110044401510044501110044001100044048140204008100204041110241004840222004840241004440800004440206009080044049040044048808044044101110501101 (by decide +kernel)

def state221_156 : List Sig := [0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 6,0x5555555555555555555555555555555500000000000000000000000000000000,input 0,input 7,input 2,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_156 : Impossible true (goalAt 221) 6 state221_156.toFinset :=
  node_ok cuts221 [⟨state221_155,exclude221_155⟩,⟨state221_149,exclude221_149⟩,⟨state221_144,exclude221_144⟩] 0x224048101204248101120404810120604414064041101044241101111004840222104440214048101204148101110404410110504818054041101044141101044401910044601110044401510044501110204008101044401110104401140044401100044001101242008880121008880121010013111020002111008808206010004110520001110509080044049080044044414204060000204044101044048101242001101 (by decide +kernel)

def state221_157 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,0x5555555555555555555555555555555500000000000000000000000000000000,input 0,input 2,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_157 : Impossible true (goalAt 221) 6 state221_157.toFinset :=
  node_ok cuts221 [⟨state221_145,exclude221_145⟩,⟨state221_155,exclude221_155⟩] 0x110130202000104404110120404908004404190104404110904404888012100484022200890120404810920404150104404110504404444012100888411100c48011100444030200850120404810520404110004400110110500111006440111804440111005440111404440111010500414004440810020400810104440c04004404c05004404c04012100888012100c04011102000011100818030200c040301009050220204101 (by decide +kernel)

def state221_158 : List Sig := [0x5555555555555555555555555555555500000000000000000000000000000000,input 0,input 7,input 2,input 3,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_158 : Impossible true (goalAt 221) 7 state221_158.toFinset :=
  node_ok cuts221 [⟨state221_146,exclude221_146⟩,⟨state221_150,exclude221_150⟩,⟨state221_154,exclude221_154⟩,⟨state221_156,exclude221_156⟩,⟨state221_157,exclude221_157⟩] 0x1002e10404410120404c08020406000430200c0802040441011040454140440411011040500031040454148000c4414104041101044050003044041101204049080204050003242009080204041101044044808222004800104044840120004808121004808104048880104041909121001901044045850044041909161401109044044840044048909121008901204048880204048909222008109204044840204044404800084400104044440110004404111004404104050008104041505111001501044045450044041505151401105044044440044048c8411100444012101001a121008c84400688884121004440111008505111008501204050008204048505400b8810520404444020404410104440410011010414010400410110500410111010111011010110110500110024200111004400110104440110124200414010501001a04440111012100191806441000c06460111812100111004441000804440111011100151405441000c05450111411100111004441000c40030810020405002e20405000c044401110302010004302004101400b8410130202000130200410140010410124201002d2420011014000c1101242010003242001101400b4110122201001422200484040068484022201001a222004840400504840400210000400004440400204440400b9000880000444040000444040031003722021002e4006c8180 (by decide +kernel)

def state221_159 : List Sig := [0xafafafafafafafafaaaaaaaaaaaaaaaa,input 7,input 0,input 6,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_159 : Impossible true (goalAt 221) 5 state221_159.toFinset :=
  node_ok cuts221 [⟨state221_70,exclude221_70⟩] 0x5400110004410110009000240009010044041901044041109044044c00110004408110008800220008808240404400300004480110001101145001101105004140121020000105004101110004101110008100204008180220201101111401101111004440222004840111004101110004101110001110044404140111008101 (by decide +kernel)

def state221_160 : List Sig := [0xafafafafafafafafaaaaaaaaaaaaaaaaafafafafafafafafaaaaaaaaaaaaaaaa,input 0,input 6,input 3,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_160 : Impossible true (goalAt 221) 6 state221_160.toFinset :=
  node_ok cuts221 [⟨state221_123,exclude221_123⟩,⟨state221_159,exclude221_159⟩,⟨state221_71,exclude221_71⟩,⟨state221_124,exclude221_124⟩] 0x9010044049000204049080240009010242009010204041101044045410044045400110010004110005410400104410110001101110008808121008800204048880220008808222008808204044840204041909121001901044045850044041909161401109044044840044044c08222004c00110004840110004c0812100440811000888011000c04011000440020404c48031000c04031200c0402040444001100081011050081012202100272202081018000c81012202041402202011011050011012420051501450011011454011012420041401050100271050041401210100271210100274003e00021210041401050041014001041011100041401100041011050041011100100271100100304001011102040444402040488088000488082040600002040488081110088080440444400440490801514044500440454500440490801110044401210044401110088804003c888012101000f121008880111004440104050000104044400111004400104044440104044400400004400 (by decide +kernel)

def state221_161 : List Sig := [0x5555555555555555555555555555555505050505050505050000000000000000,input 0,input 7,input 6,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_161 : Impossible true (goalAt 221) 5 state221_161.toFinset :=
  node_ok cuts221 [⟨state221_72,exclude221_72⟩] 0x540011000441011000110120404c050044041901044041109044044c0011000440811000890120404810920404440020404c04011000110004400110124200111006440111804440410010400410111000810020400810104440444004404544004404444080000484011100480811000444011000880820404c040204044140 (by decide +kernel)

def state221_162 : List Sig := [0xaaffaaffaaffaaffaaffaaffaaffaaffaaafaaafaaafaaafaaaaaaaaaaaaaaaa,input 0,input 7,input 6,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_162 : Impossible true (goalAt 221) 4 state221_162.toFinset :=
  node_ok cuts221 [] 0x540011000441011000980022000881022000440022000c040110001101145001101105004101110004101110008101220008101220001110044044450044044440104044400104044400204048800204048800 (by decide +kernel)

def state221_163 : List Sig := [0xff00ff00ff00ff00ff00ff00ff00ff000f000f000f000f0000000000000000,input 7,input 6,input 0,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_163 : Impossible true (goalAt 221) 5 state221_163.toFinset :=
  node_ok cuts221 [⟨state221_162,exclude221_162⟩,⟨state221_72,exclude221_72⟩] 0x150401101150004400400e8440015041003a11040440004404440026040110126000880024200880026040908022040880004404880004404414004400908004440110004404111004404908010500414011404111011400440010500440011404414011004440004440440022404111022400880020600880022404818022004880004440880030100440011000880030200880030100c080301008800110004400242004440111001101151401101242005450151001101111001101105004440105001110800041110105020000105001110111001110302008880104044400111004400302004440111004400222004400301004440204048800222008800301008880301008800111008800 (by decide +kernel)

def state221_164 : List Sig := [0xff00ff00ff00ff00ff00ff00ff00ff000f000f000f000f0000000000000000,0xffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0000000000000000,input 7,input 6,input 0,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_164 : Impossible true (goalAt 221) 5 state221_164.toFinset :=
  node_ok cuts221 [] 0x15000440011040440004404c04030140110104404908024200110104400110004404414011400440011004440004440c04020600111004440414010500111011000c08030100440011000480030200440022000484004404584004404414004440414004440888011000484011000484022200c040121004440 (by decide +kernel)

def state221_165 : List Sig := [0xffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0000000000000000,input 7,input 6,input 0,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_165 : Impossible true (goalAt 221) 6 state221_165.toFinset :=
  node_ok cuts221 [⟨state221_123,exclude221_123⟩,⟨state221_161,exclude221_161⟩,⟨state221_125,exclude221_125⟩,⟨state221_153,exclude221_153⟩,⟨state221_73,exclude221_73⟩,⟨state221_163,exclude221_163⟩,⟨state221_164,exclude221_164⟩] 0x541004404540011001000411000541040010441011000110111000d05004404110130100908030100d05024200c050301001101044045450044041101111009080111005450242005440111001101044041909121001901044045850044041909161401109044044840044044c08222004c00110004840110004c0812100440811000888011001000f12100484030100888030101000f22200888030100484012101000f8001a000511100484011101000f12100484011101000f11100110110500110024200111004400110104440110124200414010501000f04440111012100191806442000406460111812100111004440450104440450011000414011000450110500440111000111011002000304440111030100818030102000220600818030100111004442000104440111011100414010502000010500414011100111004440c04011000440040010c08030200c04030200c04040010440011000444011000440040000c080104044440302004440400004400110010039400108101 (by decide +kernel)

def state221_166 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 4,input 7,0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0000000000000000,input 6,input 0,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_166 : Impossible true (goalAt 221) 6 state221_166.toFinset :=
  node_ok cuts221 [] 0x13000440011020440026040901024060901012100585016140484012100585016140484004440191004460111011400440011004440004440901020600111010500111004440414010500111004440414011000901034140440011000541015040440011100888012100444010500111010500111010404444024040d050240404440151405450111004440151405450111008101150404400150404400240409080220601101 (by decide +kernel)

def state221_167 : List Sig := [0xf00ff000f00ff000000ff000000ff000f000f000f000f0000000000000000,input 4,input 7,input 6,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_167 : Impossible true (goalAt 221) 4 state221_167.toFinset :=
  node_ok cuts221 [] 0x114004400110044400224008800220048800044001100044044140110008800301004400150004400110404400240008800220408800105001110105001110104044400111004400204048800301008800111001101151001101 (by decide +kernel)

def state221_168 : List Sig := [0xf0fffff0f0fffff0000ffff0000ffff0f0f0f0f0f0f0f0f0000000000000000,input 4,input 7,input 6,input 0,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_168 : Impossible true (goalAt 221) 5 state221_168.toFinset :=
  node_ok cuts221 [⟨state221_167,exclude221_167⟩] 0x130004400110204400260409010240609010064041101044241101044401910044601110114004400110044400044409010206001110044001100044044140110009010301004400150004400110404400240009000240401101111020000121004440105001110105001110104044400111004400204048101301009010111001101151001101 (by decide +kernel)

def state221_169 : List Sig := [0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000,input 4,input 7,0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0000000000000000,input 6,input 0,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_169 : Impossible true (goalAt 221) 6 state221_169.toFinset :=
  node_ok cuts221 [⟨state221_168,exclude221_168⟩] 0x13000440011020440026040901024060901006404110104424110104440191004460111011400440011004440004440901020600111004400110004404414011000901034140440011100888012100444010500111010500111010404444024040d050240404440044045440044045400110004410110009000240401101222004840222004840206001110206001110312004400312004400400104440800004440204049080 (by decide +kernel)

def state221_170 : List Sig := [0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0000000000000000,input 6,input 0,input 3,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_170 : Impossible true (goalAt 221) 7 state221_170.toFinset :=
  node_ok cuts221 [⟨state221_160,exclude221_160⟩,⟨state221_165,exclude221_165⟩,⟨state221_74,exclude221_74⟩,⟨state221_128,exclude221_128⟩,⟨state221_154,exclude221_154⟩,⟨state221_166,exclude221_166⟩,⟨state221_169,exclude221_169⟩] 0x800189010044049000400d08101242009000800149010242009010400d08101044041101400105410044045400400d04400400104400400105410400104410400d04400044044400400a08808121008800400a08101222008800400a08808222008808400a08101121008101400a01909121001901400a01101161401101400a01909161401109400a01101121001101400a04c08222004c00400a04400121004400400a04c08121004408400a044002220044008001081010444081004009c88082060081008000c81012060081014009c8808044408808400d011011050011004009c9080044401100400ec1101044401101400d09080105004140400a10028044401110400a04840064601910400a20002064601118400a048400444011104001045010444045004009c44001050044004001045011050044014009c440004440440040010c04011000440040010810131200c40040010c04031200c04040010810111000440040010c04011100444040010810140010810140010c04080004c040400108101111008101400d10004111004440400101101151401101400110004151405440400d01101111001101400a04840111004440400a08880400a08880400a04840400a04840400a088801110044404009c41401110041404001011104001011104001041408000041404009c1110111001110400010000400984101 (by decide +kernel)

def state221_171 : List Sig := [0xffff0000ffff0000ffff0000ffff0000fafa0000fafa0000fafa0000fafa,input 0,0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 7,input 3,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_171 : Impossible true (goalAt 221) 5 state221_171.toFinset :=
  node_ok cuts221 [] 0x410130010448010404540015000440410404480012000480810404880422010880c204144840151008880121009000044005100104041100044001900044201100044008104204141100044001500044501100044044808104041101044041109064041101044049014240101101044041105054041101105001100044041100 (by decide +kernel)

def state221_172 : List Sig := [0xfffffffffffffffffffffffffffffffffafafafafafafafafafafafafafafafa,input 0,0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 7,input 3,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_172 : Impossible true (goalAt 221) 6 state221_172.toFinset :=
  node_ok cuts221 [⟨state221_171,exclude221_171⟩] 0x4101300104480104044101114044404104044808104044101120201101104044414044041101240109014044041101054041105044060000044041101400cc480012000480810404190104404110904404880422010880c204144840222008880121004840222008880121008101400184440104044404104044404044041504044048180054501d1405470151420410810420414880c4001c1514044501110 (by decide +kernel)

def state221_173 : List Sig := [0xff55ff55ff55ff55ff55ff55ff55ff55ff50ff50ff50ff50ff50ff50ff50ff50,input 3,input 0,input 7,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_173 : Impossible true (goalAt 221) 5 state221_173.toFinset :=
  node_ok cuts221 [] 0x4101204044480104041101104044414044041101204049014044044100104004101110101100044001101105008100204008101220201110064501918044401110064601114044404804104044408104041909044041909044048804204048808204044840110004400110104101064241101064241101220208101220208101 (by decide +kernel)

def state221_174 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,0x5555555555555555555555555555555550505050505050505050505050505050,input 0,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_174 : Impossible true (goalAt 221) 4 state221_174.toFinset :=
  node_ok cuts221 [] 0x1901044041109044048901204048109204041110064401118044401100044001101205008100204008101220304440121008880111001114112001101111001101220208101220308101044044101110501101 (by decide +kernel)

def state221_175 : List Sig := [0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 6,0x5555555555555555555555555555555550505050505050505050505050505050,input 0,input 7,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_175 : Impossible true (goalAt 221) 5 state221_175.toFinset :=
  node_ok cuts221 [⟨state221_174,exclude221_174⟩] 0x22404810120424810112040481012060441406404110104424110104440191004460111020400810020404880c044404110045001110044001100044049080111004840222004440220208101220308101044504410110404414120609080044044440044044414204060000204044101044048101240501101 (by decide +kernel)

def state221_176 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,0x5555555555555555555555555555555550505050505050505050505050505050,input 0,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_176 : Impossible true (goalAt 221) 5 state221_176.toFinset :=
  node_ok cuts221 [⟨state221_174,exclude221_174⟩] 0x4404448080000110104404810124050110106404110104424110113200484012100448022404810120424810104400110004404414004440191004460111004440414010500111020400810020404880c11100110111140110111100484022200444004450448011100444024140880820404880c204044101 (by decide +kernel)

def state221_177 : List Sig := [0x5555555555555555555555555555555550505050505050505050505050505050,input 0,input 7,input 3,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_177 : Impossible true (goalAt 221) 6 state221_177.toFinset :=
  node_ok cuts221 [⟨state221_173,exclude221_173⟩,⟨state221_175,exclude221_175⟩,⟨state221_176,exclude221_176⟩] 0x1000710404410120404c08020406000230200448020404410110404541404404110110405000a1040454148000444141040411010440490140440411012040490802040490142420090142040411010440448082220048001040448401200048081210048081040488801040419091210019010440458500440419091614011090440448400440489091210089012040488802040489092220081092040448402040441010444041001101041401040041011050041011101011101101011011050011002420011100440011010444011012420041401050100090444011101210019180644100090646011181210011100444081010444081002203100092040081014001c810122030111022030440440010440010404444011000440411100440410405000410404908011100444004404545004404908015140445004404444004404888011100444012101000712100888080000888012100444011100880c11100880820405000020404880c40000880c204044440204050007400c41114 (by decide +kernel)

def state221_178 : List Sig := [0xfffffffffffffffffffffffffffffffffffff0f0fffff0f0fffff0f0fffff0f0,input 4,0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 7,input 0,input 3,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_178 : Impossible true (goalAt 221) 6 state221_178.toFinset :=
  node_ok cuts221 [] 0x410130010448010404410111010440410404410111010440410404480012000480810404880422010880c204144840151408880121001d0505414150d054144840161405850121004100104004101110101110064401118044408104204108105220301110054401114044401504054101505105004140044401110105009010400f04440150104101110504101240109004240501505151401505044141101 (by decide +kernel)

def state221_179 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 4,input 7,0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 0,input 3,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_179 : Impossible true (goalAt 221) 6 state221_179.toFinset :=
  node_ok cuts221 [] 0x110004400110104101104049014302004101104045414150504101120004800120204101121004440222004440260509014240709014121005850161404840121005850161404840104004100104044404044401910044601110044401510044501110044409014206001110105001110044404140105001110044404140111005450151404440240408105150504101150504101151404440151404440240509080220701101 (by decide +kernel)

def state221_180 : List Sig := [0xffffffffffffffffffffff00ffffff00fff0fff0fff0fff0fff0ff00fff0ff00,0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_180 : Impossible true (goalAt 221) 3 state221_180.toFinset :=
  node_ok cuts221 [] 0x44001100044048140204008100204048808044401510044501110044044101110501101044041501044241101220008800220208101 (by decide +kernel)

def state221_181 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000f0f0f0f0f0f0f0f0f0f00000f0f00000,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 0,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_181 : Impossible true (goalAt 221) 4 state221_181.toFinset :=
  node_ok cuts221 [⟨state221_180,exclude221_180⟩] 0x1901044041109044044840111020000111008800220008808204041110064401118044401100044001101205001110054401114044408100204008101220201101104044414044041501110408101110508101 (by decide +kernel)

def state221_182 : List Sig := [0xffffffffffffffffffffff00ffffff00fff0fff0fff0fff0fff0ff00fff0ff00,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 6,input 7,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_182 : Impossible true (goalAt 221) 4 state221_182.toFinset :=
  node_ok cuts221 [⟨state221_180,exclude221_180⟩] 0x8100204008101220201110104401140044401100044001101206001110054401114044404414204060000204044101110404410110508880044048101220501101044041501044241101220008800220208101 (by decide +kernel)

def state221_183 : List Sig := [0xffffffffffffffffffff0000ffff0000f0f0f0f0f0f0f0f0f0f00000f0f00000,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 6,input 7,input 0,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_183 : Impossible true (goalAt 221) 5 state221_183.toFinset :=
  node_ok cuts221 [⟨state221_181,exclude221_181⟩,⟨state221_182,exclude221_182⟩] 0x220008800220208101120404810120604414064041101044241101121004440800044440044401910044601110204008100204048808044404110045001110044001100044048180044401510044501110110508101800008101104044410110404414120601101204049014044049010204049014204041501 (by decide +kernel)

def state221_184 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,0xf0f0f0f0f0f0f0f0f0f00000f0f0000,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 0,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_184 : Impossible true (goalAt 221) 4 state221_184.toFinset :=
  node_ok cuts221 [] 0x1d01054041509054048800220008808204041110064401118044401500054001501112008100204008101220204400110004414054044440222004840111001110044501110054401101120608101110408101 (by decide +kernel)

def state221_185 : List Sig := [0xf0f0f0f0f0f0f0f0f0f00000f0f0000,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 6,input 7,input 0,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_185 : Impossible true (goalAt 221) 5 state221_185.toFinset :=
  node_ok cuts221 [⟨state221_184,exclude221_184⟩] 0x8800220008808204044810120404818110501d01054041509054041110064401118044408100204008101220201110104401140044401500054001501206004414204060000204044400240009000240501501111008880121004440044401114044401510240404818110504410110401101 (by decide +kernel)

def state221_186 : List Sig := [0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_186 : Impossible true (goalAt 221) 4 state221_186.toFinset :=
  node_ok cuts221 [] 0x1110054401114044401100044001101112008904220108805220108800220008804120401101054041105044044800120004810044044140044404140044404440222004440121004480044044840044048105 (by decide +kernel)

def state221_187 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 0,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_187 : Impossible true (goalAt 221) 5 state221_187.toFinset :=
  node_ok cuts221 [⟨state221_181,exclude221_181⟩,⟨state221_184,exclude221_184⟩,⟨state221_8,exclude221_8⟩,⟨state221_174,exclude221_174⟩,⟨state221_77,exclude221_77⟩,⟨state221_186,exclude221_186⟩] 0x4003c48401210044402220044404003c88802220044401210044400642488800640411011210011010642448400442411012220011012203200052201081051210088042203048402203081054003c81054003c11100444048400646019108001019180446048400444011108000c111004440444005450151080008151404450444004440111004404818004400448004440110004404111004404448020600448020414111020410880c10500810420414414020414880c04440880c204150004204044818111008101204144440204144818400104818111001101044060001054141501111001505044160000044041101110501101044048105112004101110504480110508105044041101 (by decide +kernel)

def state221_188 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 0,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_188 : Impossible true (goalAt 221) 5 state221_188.toFinset :=
  node_ok cuts221 [] 0x121004440222004440064041101044241101121008880222004840120404810120604414044401910044601110044401510044501110044001100044048180044408180206001110044404110045001110110404410110504818044041501044141101044049080112001101044044101110501101241008105 (by decide +kernel)

def state221_189 : List Sig := [0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 6,0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 7,input 0,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_189 : Impossible true (goalAt 221) 6 state221_189.toFinset :=
  node_ok cuts221 [⟨state221_183,exclude221_183⟩,⟨state221_185,exclude221_185⟩,⟨state221_187,exclude221_187⟩,⟨state221_188,exclude221_188⟩,⟨state221_112,exclude221_112⟩,⟨state221_9,exclude221_9⟩,⟨state221_175,exclude221_175⟩,⟨state221_78,exclude221_78⟩] 0x2203048402201081052220088042203088802203081051210081054003c48401210044402220044404003c88802220044401210044401206088801204044141210048101206048401206044142220044140642488800640411011210011010642448400442411012220011014003c11100444048400646019108001c191804460484004440111020414111020410880c20600810420414818020414880c04440880c8001811100444044400545015108001415140445044400444011104001011100444044141050041108001041400450044140444011100440481800440090800444011000440411100440490802060081804004d00132040500041105044142041500042041500048000e0002204144414204144440120604410400104414110404440110504414400104818120610011400cc4101240501101044048105242009004240509080240508105044041101111001101044060001054141501111001505044160000044041101 (by decide +kernel)

def state221_190 : List Sig := [0xf0f0f0f0f0f0f0f0f0f00000f0f0000,input 4,input 6,input 7,input 0,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_190 : Impossible true (goalAt 221) 5 state221_190.toFinset :=
  node_ok cuts221 [] 0x8800220008808204044c00110004408110001d01054041509054041110064401118044408100204008101220204500110004401110001500054001501105004400300004480110009000240009014054045400110004414110004440222004840111001110044501110054409010104044400150404400044041101151001501 (by decide +kernel)

def state221_191 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 4,0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 0,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_191 : Impossible true (goalAt 221) 5 state221_191.toFinset :=
  node_ok cuts221 [] 0x4840111008880111004840161004850121004c8012100484011200880422010880c204141110064401118044401110054401114044404140044401110105004580044401110112008104204108105220308101204048105160605440111004450111001101150508105110508105111004480111010007104044101150508105 (by decide +kernel)

def state221_192 : List Sig := [0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 4,input 6,0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 7,input 0,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_192 : Impossible true (goalAt 221) 6 state221_192.toFinset :=
  node_ok cuts221 [⟨state221_190,exclude221_190⟩,⟨state221_191,exclude221_191⟩] 0x22010880422030810512100444022200444016040581016060541412100584012140484022200484012100888004440191004460111020410810420414880c044401510044501110044405110105001110105001110044404140206001110044408180204045414204160001204145410150405414160604101240508105240508105151004440111404440150510033110501101240508105240508105111020000111010007 (by decide +kernel)

def state221_193 : List Sig := [0xffff0000ffff00000000000000000000ffff0000ffff0000,input 6,0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 7,input 0,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_193 : Impossible true (goalAt 221) 6 state221_193.toFinset :=
  node_ok cuts221 [] 0x2203048402201081052220088042203088802203081051210081054007c48401210044402220044404007c88802220044401210044401202088801200041011210048001202048401202041012220041014007c111004440484006460191040028191804460484004440111020414111020410880c20600810420414818020414880c04440880c40028111004440444005450151040028151404450444004440111010404111010400440410500410010404414010404440404440440440045001120405000410404410120414c0803001100043020044802041441011040444401040444004001044041100044401101044044001041011040500330440411011210019090640500330642411091210011010440411102420011001050011010440011100440411011050090801050090140440411012041490802401090142420090142041411010440500330440411011110015050540500330541411051110011010440500334004c4414 (by decide +kernel)

def state221_194 : List Sig := [0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00f000f000f000f0,input 6,0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 7,input 0,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_194 : Impossible true (goalAt 221) 5 state221_194.toFinset :=
  node_ok cuts221 [] 0x110124010901404404110107404150504404580012000481012000110004400110110500810420410810522030111007440151404440490012000480112000880012000c004112004800120004c0011010480005414110105414110105450111005450111020414880c220108804111008880111004840104044800110104800 (by decide +kernel)

def state221_195 : List Sig := [0xfffffffffffffffffffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0,input 6,0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 7,input 0,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_195 : Impossible true (goalAt 221) 6 state221_195.toFinset :=
  node_ok cuts221 [⟨state221_194,exclude221_194⟩] 0x110124010901404404110105414150504404110111010441404404110105414150504404190104404110904404880422010880c204144840111008880111004c0411010440c110120000121004840400a8110004400110110500111006440111804440810420410810522030111005450151404440450411010440511010111005450151404440c040400e5003911010c004112004404111004404104144101 (by decide +kernel)

def state221_196 : List Sig := [0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 0,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_196 : Impossible true (goalAt 221) 5 state221_196.toFinset :=
  node_ok cuts221 [⟨state221_186,exclude221_186⟩] 0x4404150104414110104404448080000110104404880422050110104400110004404414004440151004450111004440414010500111022410880422014880422000880022011003a111004480111009050120004840044045840044044140044404140044404440222004440121004480121004840132008105 (by decide +kernel)

def state221_197 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 0,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_197 : Impossible true (goalAt 221) 6 state221_197.toFinset :=
  node_ok cuts221 [⟨state221_105,exclude221_105⟩,⟨state221_10,exclude221_10⟩,⟨state221_176,exclude221_176⟩,⟨state221_79,exclude221_79⟩,⟨state221_196,exclude221_196⟩,⟨state221_187,exclude221_187⟩,⟨state221_191,exclude221_191⟩] 0x545004404110111100150505404545005414110511100110104405000404404110111201000411202000640012000511200110104404901404404110120414908024010901424200901420414110104404190912100190104404585004404190916140110904404484004405000f12100484011100888011101000f222008880111004840111010004222004c8011200484012101000f12100484011200888011200880c80010880420414484022010880c12100880c20415000f20414110110500110024200111004400110104440110124200414010501000f04440111012100191806442000306460111812100111004442000204440111011100151405442000105450111411100111004441000404440111011200414010502000010500414011200111004440810504440810422030414020410810510500810522030111022030810540010810140000444020404810511100810540001003e4000044404001c444040010448011200444011200444040011000424141003d400b84101 (by decide +kernel)

def state221_198 : List Sig := [0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000000000,input 6,input 7,0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 0,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_198 : Impossible true (goalAt 221) 5 state221_198.toFinset :=
  node_ok cuts221 [] 0x1101054041105044041101220108814044045800120004810120001100044001101105001110054401114044408904220108805220104900120004801120008800120004c00120104800120008804112004800121001101161001101105001110105001110111008880111004840204148804222008804104044800121004800 (by decide +kernel)

def state221_199 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,input 7,0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 0,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_199 : Impossible true (goalAt 221) 6 state221_199.toFinset :=
  node_ok cuts221 [⟨state221_198,exclude221_198⟩,⟨state221_188,exclude221_188⟩] 0x4404150104414110104404908024200110104404c08080004110104404908024200110106404110104424110112100444022200444012100888022200484022200484012100888080000484012101002a044001100044044140044401910044601110044401510044501110044408180206001110044404140105001110044404140105001110400e4444011101000030100810511100c080111010004400b8c080112004101 (by decide +kernel)

def state221_200 : List Sig := [0xffffffffffffffff00000000000000000000000000000000,input 6,0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 0,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_200 : Impossible true (goalAt 221) 6 state221_200.toFinset :=
  node_ok cuts221 [⟨state221_11,exclude221_11⟩,⟨state221_80,exclude221_80⟩] 0x1514011010440444400541415011514015050441444400440411011505011010440441014001041011505100041105041010440411010642448400640411011614011010642458500442411011210011014003c48401210044402220044404003c88802220044401210044401202088801200041011210048001202048401202041012220041010440441400440090800444011000440411100440490801050041404003c11100444048400646019108000419180446048400444011104001c111004440444005450151080000151404450444004440111010404111010400440410500410010404414010404440404440440411100410111001000411010440011100440411011000410404410124200810524010110124050110124200901424050110120414110122200810522010484022030880422200880c22030484020414810520600880c20410111020414810420600810520414111022030880c40011003f20405002e400f84480 (by decide +kernel)

def state221_201 : List Sig := [0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 7,input 0,input 3,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_201 : Impossible true (goalAt 221) 7 state221_201.toFinset :=
  node_ok cuts221 [⟨state221_12,exclude221_12⟩,⟨state221_172,exclude221_172⟩,⟨state221_177,exclude221_177⟩,⟨state221_121,exclude221_121⟩,⟨state221_81,exclude221_81⟩,⟨state221_113,exclude221_113⟩,⟨state221_178,exclude221_178⟩,⟨state221_179,exclude221_179⟩,⟨state221_189,exclude221_189⟩,⟨state221_192,exclude221_192⟩,⟨state221_193,exclude221_193⟩,⟨state221_195,exclude221_195⟩,⟨state221_197,exclude221_197⟩,⟨state221_199,exclude221_199⟩,⟨state221_200,exclude221_200⟩] 0x400ba000e10404410140010810530200c00480036000c3020044804001081051040441014001c44401040444004001100041101044008002c4440110104404400110004104044101400105414044041101400cc4101800284101800245414800204414400cc4101044041101400b89014044041101400cc81052420090048001c9014242009014400cc81050440411014001c5450044041101400cc4440054141501800185450054141105400cc4440044041101400a84808222004800400a84101121004800400a84808121004808400a84101222004101400a81909121001901400a81101161401101400a81909161401109400a81101121001101400a8880c121008804400a88105222008804400a8880c22200880c400a88105121008105400a9002a121004840400a84440222004440400a9002a222008880400a84440121004440400104101044404100400244404105004100800144101105004101400244404044404404400cc1101105001100400249080044401100400281101044401101400cc9080105004140400a9002a044401110400a84840064601910400aa0004064601118400a84840044401110400b8810504440810440024880c2060081048000c810520600810540024880c04440880c4001e0002044401110400244440054501510800060000054501114400244440044401110400010029400008101 (by decide +kernel)

def state221_202 : List Sig := [0xffffffffffffffffffffaaaaffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 2,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_202 : Impossible true (goalAt 221) 4 state221_202.toFinset :=
  node_ok cuts221 [] 0x64041101044241101220008800220208101064401110044601110111004840222104440054041101044141101214048101204148101054401110044501110044044101110501101044001100044048140204008100204048808 (by decide +kernel)

def state221_203 : List Sig := [0xfffffffffffffffffffff0f0fffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 0,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_203 : Impossible true (goalAt 221) 4 state221_203.toFinset :=
  node_ok cuts221 [] 0x64041101044241101220008800220208101121004440222104440044401910044601110044001100044048140204008100204048808044401510044501110044044101110501101044041501044141101214048101204148101 (by decide +kernel)

def state221_204 : List Sig := [0xffffffffffffffffffffff00ffffff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_204 : Impossible true (goalAt 221) 4 state221_204.toFinset :=
  node_ok cuts221 [] 0x54041101044141101214048101204148101111004840222104440044401510044501110044001100044048140204008100204048808044401910044601110044044101110501101044041901044241101220008800220208101 (by decide +kernel)

def state221_205 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff000000000000000000000000000000000000,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 0,input 2,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_205 : Impossible true (goalAt 221) 5 state221_205.toFinset :=
  node_ok cuts221 [⟨state221_202,exclude221_202⟩,⟨state221_203,exclude221_203⟩,⟨state221_204,exclude221_204⟩] 0x64041101044241101121009040800084840220008800220208101111004840222104440054041101044141101111009040800044440214048101204148101044401910044601110044401510044501110044001100044048140044409040800001110204008100204048808044044101110501101242009010 (by decide +kernel)

def state221_206 : List Sig := [0xffffffffffffffffffffaaaaffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 7,input 6,input 2,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_206 : Impossible true (goalAt 221) 5 state221_206.toFinset :=
  node_ok cuts221 [⟨state221_202,exclude221_202⟩] 0x4810120404818110508800220008808204041901044041109044041910044401118044404440121008884111004410110404414120608501204048105204041501044041105044041510044401114044404414204060000204044101104401110045001110044048101220601101044001100044048180204008100204048808 (by decide +kernel)

def state221_207 : List Sig := [0xfffffffffffffffffffff0f0fffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 7,input 6,input 0,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_207 : Impossible true (goalAt 221) 5 state221_207.toFinset :=
  node_ok cuts221 [⟨state221_203,exclude221_203⟩] 0x4810120404818110508800220008808204041901044041109044044840111008884111001110064401118044401110104401140044408100204008101220201100044001101206001110054401114044404414204060000204044101110404410110504818044048101240501101044041501044141101214048101204148101 (by decide +kernel)

def state221_208 : List Sig := [0xffffffffffffffffffffff00ffffff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 7,input 6,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_208 : Impossible true (goalAt 221) 5 state221_208.toFinset :=
  node_ok cuts221 [⟨state221_204,exclude221_204⟩] 0x4410110404414120608501204048105204041501044041105044044440121008884111001110054401114044401110104401140044408100204008101220201100044001101206001110064401118044404414204060000204044101120404810120604414044048101220601101044041901044241101220008800220208101 (by decide +kernel)

def state221_209 : List Sig := [0xffffffffffffffffffff0000ffff000000000000000000000000000000000000,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 7,input 6,input 0,input 2,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_209 : Impossible true (goalAt 221) 6 state221_209.toFinset :=
  node_ok cuts221 [⟨state221_205,exclude221_205⟩,⟨state221_206,exclude221_206⟩,⟨state221_207,exclude221_207⟩,⟨state221_208,exclude221_208⟩] 0x12040481012060441422000880022020810106404110104424110112101002c8000c484011100484022210444011040441011050481821404810120414810105404110104414110111101001380008444004440191004460111004440151004450111004440411004500111020400810020404880804400110004404818004441001280004111011050810180000810110404441440011002d110501101204048818240409080 (by decide +kernel)

def state221_210 : List Sig := [0xffffffffffffffff0000000000000000ffff0000ffff0000,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 7,input 0,input 2,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_210 : Impossible true (goalAt 221) 5 state221_210.toFinset :=
  node_ok cuts221 [] 0x26040901024060901012000480012020410111100484022210444025040901024050901011000440011010410104440191004460111004440151004450111004440901020600111010400410010404440430000c00024040410111050481812040481012060441411040441004440114004440411020404810124040c010044041101110504101 (by decide +kernel)

def state221_211 : List Sig := [0x5555555555555555555555555555555555555555555555555555000055550000,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 7,input 6,input 2,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_211 : Impossible true (goalAt 221) 5 state221_211.toFinset :=
  node_ok cuts221 [] 0x481012040481811050890020400810820400190004400110804400444012100888411100441011040441412060850020400810420400150004400110404400c010204009040204004100044008100240401100044401118064401110044401114054401110044401140104401110220208100240408100206001100044401100 (by decide +kernel)

def state221_212 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0000,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 7,input 6,input 0,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_212 : Impossible true (goalAt 221) 5 state221_212.toFinset :=
  node_ok cuts221 [] 0x4810120404818110508c00230008c08214041d0105404150905404111006440111804440111010440114004440850021400850123020150005400150120600c010214049040214044400250009400240401501111008884121004440044401114044401510120604414110404410204048101240408501044041101111001501 (by decide +kernel)

def state221_213 : List Sig := [0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000000ff0000,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 7,input 6,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_213 : Impossible true (goalAt 221) 5 state221_213.toFinset :=
  node_ok cuts221 [] 0x4410110404414120608c00220008804220001d0106404190506404111005440111404440111010440114004440890022000880122000190006400190120600c010220009040220004800260008800240408800111008884111004840044401118044401910110504818120404810204048800240408800044041101121001901 (by decide +kernel)

def state221_214 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffffffff0000ffff0000,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 7,input 6,input 0,input 2,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_214 : Impossible true (goalAt 221) 6 state221_214.toFinset :=
  node_ok cuts221 [⟨state221_210,exclude221_210⟩,⟨state221_211,exclude221_211⟩,⟨state221_212,exclude221_212⟩,⟨state221_213,exclude221_213⟩] 0x4810120404818110509810240409018240408880121004840222020003121004840400b044401210088841110044101104044141206094102404090142404094801110044402420200021110044404004c111006440111804440111005440111404440111010440114004440111024040818004440818004440111020602000104440111040048c01024040904024040c080800008101240409080220601101 (by decide +kernel)

def state221_215 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 0,input 2,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_215 : Impossible true (goalAt 221) 5 state221_215.toFinset :=
  node_ok cuts221 [⟨state221_184,exclude221_184⟩] 0x8880121004840222008800220008808204044440121008884111009480111004440242008501204048105204041110064401118044401110054401114044408180044401110206008100204008101220209000240004414204044840222004840241004440800004440241001110206001110241001101110508101240408101 (by decide +kernel)

def state221_216 : List Sig := [0xffffffffffffffffffff0000ffff0000,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 7,input 6,input 0,input 2,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_216 : Impossible true (goalAt 221) 6 state221_216.toFinset :=
  node_ok cuts221 [⟨state221_185,exclude221_185⟩,⟨state221_215,exclude221_215⟩] 0x12040481012060441422000880022020810122200484012100888011100484022210444011040441011050481821404810120414810125200444011100908004440191004460111004440151004450111004440411004500111020400810020404880820600111004440818011050810180004810130200900024200810112100888012100888011102000011101001304440818004440818011051002d110510004240401101 (by decide +kernel)

def state221_217 : List Sig := [0xffffffffffffffff0000ffff0000ffffffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 7,input 0,input 2,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_217 : Impossible true (goalAt 221) 5 state221_217.toFinset :=
  node_ok cuts221 [] 0x260409010240609010064041101044241101120404810120604414111004840222104440250409010240509010054041101044141101110404410110504818044401910044601110044401510044501110044409010206001110044001100044048180044404110045001110240009000240401101204048101241009010104041101110501101 (by decide +kernel)

def state221_218 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0fffff0f0fffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 7,input 6,input 0,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_218 : Impossible true (goalAt 221) 5 state221_218.toFinset :=
  node_ok cuts221 [] 0x481012040481811050880422010880c20414190104404110904404111006440111804440111010440114004440810420410810522030110004400110120600111005440111404440c010204149040204144101240009000240401101111004840222004440110404410110504818204048101204149010054041101044141101 (by decide +kernel)

def state221_219 : List Sig := [0xffff0000ffff00000000000000000000000000000000,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 7,input 6,input 0,input 2,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_219 : Impossible true (goalAt 221) 6 state221_219.toFinset :=
  node_ok cuts221 [⟨state221_217,exclude221_217⟩,⟨state221_218,exclude221_218⟩] 0x481012040481811050981024040901824040190104404110904404444012100888411100441011040441412060941024040901424040150104404110504404111006440111804440111005440111404440111010440114004440111024040818004440110004400110120600c010240409040240404101240009010044048880121008880121010013111020001111008180044408180044420000204049080 (by decide +kernel)

def state221_220 : List Sig := [0x5555555555555555555555555555555555555555555555550000000000000000,input 0,input 7,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 2,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_220 : Impossible true (goalAt 221) 5 state221_220.toFinset :=
  node_ok cuts221 [] 0x1901044041109044048901204048109204044440121008884111001501044041105044048501204048105204041101204049040044041110064401118044401110054401114044401100044001101242008100204008101044404810120404818110504410110404414120604404044044414044048808204049040204041140 (by decide +kernel)

def state221_221 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 0,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_221 : Impossible true (goalAt 221) 5 state221_221.toFinset :=
  node_ok cuts221 [] 0x64041101044241101121009040222004840130404410110604410044401910044601110044001100044048180044409040206001110044404410105001110044049080241001101110004400110401101214044440222104840111004140044404140044409080044044440044044440400109040111004818 (by decide +kernel)

def state221_222 : List Sig := [0xf0f0f0f0f0f0f0f0f0f00000f0f00000f0f0f0f0f0f0f0f0f0f00000f0f0000,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,input 0,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_222 : Impossible true (goalAt 221) 5 state221_222.toFinset :=
  node_ok cuts221 [⟨state221_184,exclude221_184⟩] 0x121009040222004840120404810120604414074041501054241501044401910044601110044409040206001110044404110045001110054001500054048180204041501252009040054044400110004414054044440222004840111001110044501110054404440800009040111004818110504410110401101 (by decide +kernel)

def state221_223 : List Sig := [0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_223 : Impossible true (goalAt 221) 5 state221_223.toFinset :=
  node_ok cuts221 [⟨state221_186,exclude221_186⟩] 0x54041101044141101111009040800004440130404810120504810044401510044501110044001100044048180044409040206001110044404810105001110044049080241001101120004800120401101220004440222104440121004140044404140044408880044044840044044840222009040121004414 (by decide +kernel)

def state221_224 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 0,input 2,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_224 : Impossible true (goalAt 221) 6 state221_224.toFinset :=
  node_ok cuts221 [⟨state221_205,exclude221_205⟩,⟨state221_215,exclude221_215⟩,⟨state221_97,exclude221_97⟩,⟨state221_220,exclude221_220⟩,⟨state221_136,exclude221_136⟩,⟨state221_155,exclude221_155⟩,⟨state221_17,exclude221_17⟩,⟨state221_82,exclude221_82⟩,⟨state221_221,exclude221_221⟩,⟨state221_187,exclude221_187⟩,⟨state221_188,exclude221_188⟩,⟨state221_222,exclude221_222⟩,⟨state221_223,exclude221_223⟩] 0x190922200190104404484004404190912100110904404888004405000f12100484024100888024101000f22200888024100484012100481880030481011050484012040481812100481811051000f110508c84111004440121010004121008c844003c88841210044401110015058002c15010440444400440415051110011050440500040440500041110044402410100042410100048002a000924100444011100441480020441012060444011040441411100441412061000412061000f044401110121001918064420007064601118121001110044410004044401110111001514054420006054501114111001110044401101206001100242001110044001101044401101242008180206020005044401110241008180241020004206008180241001110044420003044401110110504140104420002105001140110501110044409040044041101800049080242009040242009040800001101044044414044041101400b49080104044414242004414400b41101044050004400108101 (by decide +kernel)

def state221_225 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0a0a0f0f0a0a0f0f0f0f0f0f0f0f0f0f0a0a0f0f0a0a,input 0,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 6,input 3,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_225 : Impossible true (goalAt 221) 5 state221_225.toFinset :=
  node_ok cuts221 [] 0x880022000880820404481012040481811050190104404110904404c010204049040204044400250009400240401101214008500204048808044401910044601110044404110045001110054001500044048580204048105204048501111008880121004440120604414110404410044041105044041501044401114044401510 (by decide +kernel)

def state221_226 : List Sig := [0xffffffffffffffffffffaaaaffffaaaaffffffffffffffffffffaaaaffffaaaa,input 0,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 6,input 2,input 3,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_226 : Impossible true (goalAt 221) 6 state221_226.toFinset :=
  node_ok cuts221 [⟨state221_225,exclude221_225⟩] 0x88002200088082040448101204048181105019010440411090440488801210048402220085012040481052040444401210088841110044101104044141206015010440411050440600001110044404004cc0102040490402040441014000c1101204049010044049080204048808204048808044401910044601110044401510044501110044404110045001110044041110400488180204048808204048808 (by decide +kernel)

def state221_227 : List Sig := [0x5555555555555555555500005555000055555555555555555555000055550000,input 0,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 6,input 2,input 3,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_227 : Impossible true (goalAt 221) 6 state221_227.toFinset :=
  node_ok cuts221 [⟨state221_18,exclude221_18⟩,⟨state221_114,exclude221_114⟩,⟨state221_83,exclude221_83⟩] 0x22000880022020810112040481012060441406404110104424110121404810120414810111100484022210444011040441011050481805404110104414110130040810124100810110404110120404901004404810020400810122020818012102000212100818011100818411100818011052000111050110004404818024040810124040810112100888012100888011102000011101001311051002d110510012242001110 (by decide +kernel)

def state221_228 : List Sig := [0xafafafafafafafafafafaaaaafafaaaaafafafafafafafafafafaaaaafafaaaa,input 0,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 6,input 3,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_228 : Impossible true (goalAt 221) 5 state221_228.toFinset :=
  node_ok cuts221 [] 0x220008800220208101120404810120604414064041101044241101300408101241008101110009400250009010044048101220208101220201110064401118044401110104401140044401101044401101252001114204048808204048808111008880121004440120604414110404410044044440044049480 (by decide +kernel)

def state221_229 : List Sig := [0xff00ff00ff00ff00ff00ff00ff00ff000f000f000f000f000f0000000f0000,input 7,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 6,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_229 : Impossible true (goalAt 221) 4 state221_229.toFinset :=
  node_ok cuts221 [] 0x1110104401140044401500054001501206008900220008801220004400300408800241008800260008800240408800044401114044401510222004414110404410044041101111001501204048800240408800 (by decide +kernel)

def state221_230 : List Sig := [0xffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f00000f0f0000,input 7,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 6,input 0,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_230 : Impossible true (goalAt 221) 5 state221_230.toFinset :=
  node_ok cuts221 [⟨state221_229,exclude221_229⟩] 0x12040481012060441407404150105424150126040901024060901080000444012100444004440191004460111004440411004500111005400150005404818004440901020600111004450111004440151011000c010240409040240404414120604410110401501242009010054041101044044440054048101 (by decide +kernel)

def state221_231 : List Sig := [0xf0f0f0f0f0f0f0f0f0f00000f0f00000f0f0f0f0f0f0f0f0f0f00000f0f0000,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 6,input 0,input 3,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_231 : Impossible true (goalAt 221) 6 state221_231.toFinset :=
  node_ok cuts221 [⟨state221_228,exclude221_228⟩,⟨state221_18,exclude221_18⟩,⟨state221_230,exclude221_230⟩,⟨state221_185,exclude221_185⟩,⟨state221_222,exclude221_222⟩,⟨state221_115,exclude221_115⟩,⟨state221_84,exclude221_84⟩] 0x2202048402200081012220088002202088802202081011210081011206088801204044141210048101206048401206044142220044140742488800740415011210015010742448400542415012220015012040411102040088082060081002040481802040488080444088084003c1110044404840064601910800181918044604840044401110400101110044404414105004110800144140045004414044401110054048180054009480044401500054041110054049480206008180301004414300408101400108101301020004241008101110508101400d1003411000901005404940020404948025000901025200901020404150105404901011100901020406000320404901080008901020404444020404484011100444022201000f2220048404003c48402220044401110011101110011100545200010445011108000011100545044400544048184004c48181105044401105048181110044101105100131104100134004c1101 (by decide +kernel)

def state221_232 : List Sig := [0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 6,input 0,input 2,input 3,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_232 : Impossible true (goalAt 221) 7 state221_232.toFinset :=
  node_ok cuts221 [⟨state221_209,exclude221_209⟩,⟨state221_214,exclude221_214⟩,⟨state221_216,exclude221_216⟩,⟨state221_219,exclude221_219⟩,⟨state221_224,exclude221_224⟩,⟨state221_226,exclude221_226⟩,⟨state221_227,exclude221_227⟩,⟨state221_116,exclude221_116⟩,⟨state221_19,exclude221_19⟩,⟨state221_85,exclude221_85⟩,⟨state221_137,exclude221_137⟩,⟨state221_156,exclude221_156⟩,⟨state221_231,exclude221_231⟩,⟨state221_189,exclude221_189⟩] 0x400b08808121008800400b08101222008800400b08808222008808400b08101121008101400b04818222004810400b04414121004810400b04818121004818400b04414222004414400b01909222001901400b01101121001101400b01909121001109400b011012220011014004c85051110085014004c81014004c81014004c85058003481054004c8101111008101400b08c84111004440400b04840400b04840400b08c84400b08884400b048401110044404004c44144001044104004c48181110044104004c44141110044144004c48184004c48184004c15058003015014004c11011110011014004c15051110011054004c11014004c11018002c8101044408100400488808206008100800288101206008101400488808044408808400b1002c044401110400b04840064601910400b20009064601118400b048400444011104004d00130444011104004c44400545015104004e00080545011144004c444004440111040011000404440111040048441410500411040012000710500114040048441404440111080018110120600110040048908004440110080014110104440110140048908020600818040010c04011050c01040010810140010810140010c040800109040400108101110508101400b5002b400b441018000c9010044049000800088101242009000800049010242009010800008101044041101 (by decide +kernel)

def state221_233 : List Sig := [0x5555555555555555555555555555555555555555555555555555000055550000,input 7,input 4,input 6,input 2,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_233 : Impossible true (goalAt 221) 5 state221_233.toFinset :=
  node_ok cuts221 [] 0x124004100104204100064001100044201100224008100204208100111004840222104440114004100104104100054001100044101100214008100204108100104008100301004100044004100110501100044008100240401100044401118064401110044401114054401110110104100144404100105001100044401100220208100240408100 (by decide +kernel)

def state221_234 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0000,input 7,input 4,input 6,input 0,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_234 : Impossible true (goalAt 221) 5 state221_234.toFinset :=
  node_ok cuts221 [] 0x130004400110204400074041501054241501230008c00230208501044401910044601110114004400110044400054001500054044140214008500214048c0811000c400301004400150004400110504400250009400240401501111008884121004440044401114044401510104044400150404400044041101151001501204048101240408501 (by decide +kernel)

def state221_235 : List Sig := [0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000000ff0000,input 7,input 4,input 6,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_235 : Impossible true (goalAt 221) 5 state221_235.toFinset :=
  node_ok cuts221 [] 0x130004800120104800074041901064141901230008800220108800044401510044501110124004800120044800064001900064044140224008800220048800120008800301004800160004800110504800260008800240408800111008884111004840044401118044401910104044800160404800044041101161001901204048800240408800 (by decide +kernel)

def state221_236 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffffffff0000ffff0000,input 7,input 4,input 6,input 0,input 2,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_236 : Impossible true (goalAt 221) 6 state221_236.toFinset :=
  node_ok cuts221 [⟨state221_233,exclude221_233⟩,⟨state221_234,exclude221_234⟩,⟨state221_235,exclude221_235⟩] 0x581016040581815050484016100485012100981024040901824042000212100484040050444012100888411100541015040541416060444015100445011100941024040901424042000111100444040000111006440111804440111005440111404440111014440414004440414004440111010500111024040818004442000004440111040030d01024040c04024040410115050c08011050441424040c040240408818044048101 (by decide +kernel)

def state221_237 : List Sig := [0xffffffffffffffffffff0000ffff0000,input 7,input 4,input 6,input 0,input 2,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_237 : Impossible true (goalAt 221) 6 state221_237.toFinset :=
  node_ok cuts221 [⟨state221_190,exclude221_190⟩] 0x581016040581815050484016100485012100880022000880820404444012100888411100541015040541416060444015100445011100850120404810520404111006440111804440111005440111404440111014440414004440414004440111010500810020400810122020c00030000c080204045414302004414110509000240009080204044840222004840222004440800004440400001110206001110206004101104045414302001101044050004242009010 (by decide +kernel)

def state221_238 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 7,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 6,input 0,input 2,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_238 : Impossible true (goalAt 221) 6 state221_238.toFinset :=
  node_ok cuts221 [⟨state221_210,exclude221_210⟩] 0x16040581016060541422200484012100888026040901024060901012100584012140484011100484022210444015040541015050581825200444011100908025040901024050901011100544011140444004440191004460111004440151004450111004440511010500111020600111004440818004440901020600111010500111004440414010404c010240409050240420000150504414110509010242009010220601101044049080400108101 (by decide +kernel)

def state221_239 : List Sig := [0xf0f0fffff0f0fffff0f0fffff0f0fffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 7,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 6,input 0,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_239 : Impossible true (goalAt 221) 5 state221_239.toFinset :=
  node_ok cuts221 [] 0x481012040481811050190104404110904404880422010880c204141110064401118044401110104401140044401100044001101206008104204108105220301110054401114044404101340408105241008105240009000240401101111004840222004440110404410110504818054041101044141101204048101204149010 (by decide +kernel)

def state221_240 : List Sig := [0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000,input 7,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 6,input 0,input 2,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_240 : Impossible true (goalAt 221) 6 state221_240.toFinset :=
  node_ok cuts221 [⟨state221_217,exclude221_217⟩,⟨state221_239,exclude221_239⟩] 0x12040481012060441406404110104424110126040901024060901011100484022210444011040441011050481805404110104414110125040901024050901004440191004460111004440151004450111004440411004500111004400110004404818004440901020600111010404d010240409040240409000240009010044048880121008880121010013111020001111008180044408180044410004110520000110510004044049080044048101 (by decide +kernel)

def state221_241 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 4,input 0,input 2,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_241 : Impossible true (goalAt 221) 6 state221_241.toFinset :=
  node_ok cuts221 [⟨state221_191,exclude221_191⟩] 0x12100584012140484022200484012100888012100c04022200484016040581016060541411100484022210444011100544011140444031200444011100c08011100c04080000444015040541015050581804440191004460111004440151004450111010500111004440414020600111004440818004440c040206001110044405110105001110044049040241009050301005414400b4441411050c04030200c040112104101104045414400b48101 (by decide +kernel)

def state221_242 : List Sig := [0xff00ff00ff00ff00ff00ff00ff00ff000f000f000f000f000f0000000f0000,input 7,input 4,input 6,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_242 : Impossible true (goalAt 221) 4 state221_242.toFinset :=
  node_ok cuts221 [] 0x114004400110044400054001500054044140224008800220048800110008800301004400150004400110504400260008800240408800044401114044401510104044400150404400044041101151001501204048800240408800 (by decide +kernel)

def state221_243 : List Sig := [0xffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f00000f0f0000,input 7,input 4,input 6,input 0,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_243 : Impossible true (goalAt 221) 5 state221_243.toFinset :=
  node_ok cuts221 [⟨state221_242,exclude221_242⟩] 0x4c00110004408110001d0105404150905404981024040901824042000011100484011100111006440111804440450011000440111000150005400150110500111024040818004440111404440111005440440024040c040110004400104045410110005400110004414110001501301009010054041101044045440054048101 (by decide +kernel)

def state221_244 : List Sig := [0xf0f0f0f0f0f0f0f0f0f00000f0f00000f0f0f0f0f0f0f0f0f0f00000f0f0000,input 4,input 6,input 0,input 3,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_244 : Impossible true (goalAt 221) 6 state221_244.toFinset :=
  node_ok cuts221 [⟨state221_243,exclude221_243⟩,⟨state221_190,exclude221_190⟩] 0x220204840220008101222008800220208880220208101121008101130208880130004400121004400130204840110204400222004400074244840074041501161401501074245850054241501121001501204041110204008808206008100204048180204048808044408808400881110044404840064601910400ec191804460484004440111011404111011400440010500440011404414011004440004440440005404414005400948004440150005404111005404948010500414030100440011000810131200c40030100c480301008101110004400240401501250008101252009400240409480240408101054041501150501501150004400400d04400150510013110504400054044400240404440240408101800048101240420000240408101111008101121004440111008880400888880121010022121008880111004440044404440044401514400ec111404441003b044401514111001510160610026104044400111004400160604440150404400400a044004004c44400440415011514011014004c5450151001501111001501 (by decide +kernel)

def state221_245 : List Sig := [0xf0f0f0f0f0f0f0f0f0f00000f0f00000f0f0f0f0f0f0f0f0f0f00000f0f0000,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 4,input 6,input 0,input 3,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_245 : Impossible true (goalAt 221) 6 state221_245.toFinset :=
  node_ok cuts221 [] 0x220008800220208101160405810160605414121005840121404840222004840121008880204008100204048808044401910044601110044405110105001110105001110044404140206001110044408180340408101301008101110009010204049010204045414400d04414054049010204049010204049010204049010204044440222004840111001110044501110054405818150505410150404440111405440111010000 (by decide +kernel)

def state221_246 : List Sig := [0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 4,input 6,input 0,input 2,input 3,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_246 : Impossible true (goalAt 221) 7 state221_246.toFinset :=
  node_ok cuts221 [⟨state221_236,exclude221_236⟩,⟨state221_237,exclude221_237⟩,⟨state221_238,exclude221_238⟩,⟨state221_240,exclude221_240⟩,⟨state221_241,exclude221_241⟩,⟨state221_244,exclude221_244⟩,⟨state221_245,exclude221_245⟩,⟨state221_192,exclude221_192⟩] 0x880812100880020404888022000880822200880820404484020404581822200581015050484016040581812100581815050888015051002c121004840400b0585016101002c161404850400b0484012101002c22200888040050484012101002c1210048404005088802220085051110085012040500132040485058001c8105204044440204048c8411100444012101002c121008c84400b088841210044401110054144001054101606044401504054141110054141606100131606100131110044404004c54501510100131514044504004c44401110100138001a000540000444011101001311100444040001001340000810104440810022020818020400810120600810122020111022021002c04440111012100191806441000306460111812100111004441001304440111011100151405441000305450111411100111004441000404440111015050414014441000310500414015050111004441002d105004140400481110044410003044401110400b4414010501000320600818040030111004441000304440111040030818020600c04015050d01020405000420404c04080010c04020404541420405002b400b44101240420003240408101400b48101240420002240408101400b4810115051000415051002d400b5002d400b5002d11051004040010110124041002e240408101800048101240420000240408101400b88101 (by decide +kernel)

def state221_247 : List Sig := [0xffff0000ffff00000000000000000000ffff0000ffff0000,input 6,input 0,input 2,input 3,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_247 : Impossible true (goalAt 221) 7 state221_247.toFinset :=
  node_ok cuts221 [⟨state221_193,exclude221_193⟩] 0x400ac8808121008800400ac8101222008800400ac8808222008808400ac8101121008101400ac4808222004800400ac4101121004800400ac4808121004808400ac4101222004101400448505111008501400448101400448101400448505800008105400448101111008101400ac8c84111004440400ac4840400ac4840400ac8c84400ac8884400ac48401110044404004444044001044004004441011110044004004444041110044044004441014004441014000c81010444081004010488082060081004000c8101206008101401048808044408808400ad002b044401110400ac4840064601910400ad0003064601118400ac484004440111040045001104440111040044444005450151040045000305450111440044444004440111040010410104440410040104440410500410040010410110500410140104440404440440440010c04010404c00040010810130200c00040010c04030200c040400108101104044101400b49010044049000400b48101242009000400b49010242009010400b48101044041101400ad002b044041101400ac4840064241901400ad002d064241109400ac484004404110140045001104404110140044444005414150140045002d054141105400444440044041101400b41110242001100400b44140044041100400b41110044041101400b44140242004140400b5002d400b04414 (by decide +kernel)

def state221_248 : List Sig := [0xf0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0fffff0f0fffff0f0,input 6,input 4,input 7,input 0,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_248 : Impossible true (goalAt 221) 5 state221_248.toFinset :=
  node_ok cuts221 [] 0x22010880422030810506414110504434110512000480012020410104440191004460111020410810420414880c04410110404414414010400410010404440410500111004440414024010900424040110514404410111040410130000c000301004101111004840222004440204048101204144440044041101044144440110004400110104101 (by decide +kernel)

def state221_249 : List Sig := [0xffffffffffffffff0000000000000000ffff0000ffff0000,input 6,input 4,input 7,input 0,input 2,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_249 : Impossible true (goalAt 221) 6 state221_249.toFinset :=
  node_ok cuts221 [⟨state221_248,exclude221_248⟩,⟨state221_210,exclude221_210⟩] 0x981024040901824040484016100485012100480012000480810404444012100888411100941024040901424040444015100445011100440011000440410404111006440111804440111005440111404440111024040818004440414004440111010500410010400410111010901030100901022060510110406000110404c00030000c040104048880121008880121010000111020000111001110105001110105008101204049010301001101044049080400ac5414 (by decide +kernel)

def state221_250 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 4,input 7,input 0,input 2,input 3,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_250 : Impossible true (goalAt 221) 7 state221_250.toFinset :=
  node_ok cuts221 [⟨state221_238,exclude221_238⟩,⟨state221_179,exclude221_179⟩,⟨state221_166,exclude221_166⟩,⟨state221_236,exclude221_236⟩,⟨state221_249,exclude221_249⟩] 0xd05010404410124040c08024040d050302009050240404101104060004104044101400105414150520003150505414400104101104044808222004800104044840120004808121004808104048880104049818121009810240408880240409818222009018240404840240410045121004840242005850161410045161405850242004840121010045121004840400505850161410045161405850400504840121004404800084400104044440110004404111004404104050044104048c84111004440121010045121008c8440114888412100444011100941411100941024041004424040941480004901424040444024040948411100444024200545015140948415140545024200444011101004411100444040000545015141004415140545040000444011100410104440410011010414010400410110500410111010111011011004504440111012100191806441000306460111812100111004441004404440111011100151405441000305450111411100111004441000304440111024040818024041000320600818024040111004441002d105004140242001110044410003044401110242004140105010003105004140400301110044410003044401110400304140105010043400b48101150509080150504101400b4410115052000015050410124200410124041002e24041002d242009080400b5002d220610042400b81101 (by decide +kernel)

def state221_251 : List Sig := [0xf0f0fffff0f0fffff0f0fffff0f0fffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 4,input 7,input 0,input 3,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_251 : Impossible true (goalAt 221) 6 state221_251.toFinset :=
  node_ok cuts221 [⟨state221_239,exclude221_239⟩] 0x34140410110404810530200c00434140c0802414081051040441011202088801200041011210048001202048401202041012220041012203048402201081052220088042203088802203081051210081050642448400640411011614011010642458500442411011210011011040411101040044041050041001040441401040444040444044044007c111004440484006460191040028191804460484004440111020414111020410880c20600810420414818020414880c04440880c044044140044009480044401100044041110044049480105004140400281110044404440054501510400281514044504440044401110150501101044044101400cc41011505200001105041010440411012404011012400081052520090002404094802404081050440411011101100041100041011110044001101044401101041014001041012220044401110048404007c484022201001f222004840111004440204144440204049010400a4810120415002a204149010111009010054144440054041101151401101054145450044141101111001101 (by decide +kernel)

def state221_252 : List Sig := [0xf0f0f0f0f0f0f0f00000f0f00000f0f0f0f0f0f0f0f0f0f0000000000000000,input 6,input 4,input 7,input 0,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_252 : Impossible true (goalAt 221) 5 state221_252.toFinset :=
  node_ok cuts221 [] 0x230008c00230208501064041101044241101130004400110204400044401910044601110214008500214048c0804400110004404414011400440011004440024000900024040110115000440011040440011000c400301004400111008884121004440105001110105001110204048101301008501111001101151001101104044400111004400 (by decide +kernel)

def state221_253 : List Sig := [0xff00ff00ff00ff000000ff000000ff00ff00ff00ff00ff0000000000000000,input 6,input 4,input 7,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_253 : Impossible true (goalAt 221) 5 state221_253.toFinset :=
  node_ok cuts221 [] 0x230008800220108800054041101044141101130004800120104800044401510044501110224008800220048800044001100044044140124004800120044800240008800220408800160004800120404800120008800301004800111008884111004840105001110105001110204048800301008800121001101161001101104044800121004800 (by decide +kernel)

def state221_254 : List Sig := [0xffffffffffffffff0000ffff0000ffffffffffffffffffff0000000000000000,input 6,input 4,input 7,input 0,input 2,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_254 : Impossible true (goalAt 221) 6 state221_254.toFinset :=
  node_ok cuts221 [⟨state221_217,exclude221_217⟩,⟨state221_252,exclude221_252⟩,⟨state221_253,exclude221_253⟩] 0x981024040901824040190104404110904404888012100484022202000212100484040050444012100888411100941024040901424040150104404110504404c480111004440302020001111004440400001110064401118044401110054401114044401110240408180044401100044001101105001110105004140044401110105004140044409000240009010044041101302020000044041101400ac908004404c04024040c040240404101204048101301009010 (by decide +kernel)

def state221_255 : List Sig := [0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000,input 4,input 7,input 0,input 2,input 3,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_255 : Impossible true (goalAt 221) 7 state221_255.toFinset :=
  node_ok cuts221 [⟨state221_251,exclude221_251⟩,⟨state221_254,exclude221_254⟩,⟨state221_240,exclude221_240⟩,⟨state221_169,exclude221_169⟩] 0xd05010404410124040c08024040d0503020090502404041011040448082220048001040448401200048081210048081040488801040498181210098102404088802404098182220090182404048402404019091210019010440458500440419091614011090440448400440444048000c4400104044440110004404111004404104050047104048c84111004440121010042121008c84401088884121004440111009414111009410240410047240409414400b89014240404440240401505111001501044045450044041505151401105044044440044044101044404100110104140104004101105004101110101110110110042044401110121001918064410003064601118121001110044410047044401110111001514054410003054501114111001110044410003044401110240408180240410003206008180240401110044401101105001100400d81110044001101044401101400b4414010500541404404110110405002d10404541480008441410404110104405002d400b4900024041002e24041002d044041101302010004302004101400b841013020200013020041014001041012220100142220048404010848402220100422220048404005048404011d00004000044404011c4440400b9004780000444040000444020601000c2060011104000c1110206010003206001110400301110400b5004620405002e401149080 (by decide +kernel)

def state221_256 : List Sig := [0x5555555555555555555555555555555555555555555555550000000000000000,input 0,input 6,input 7,input 2,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_256 : Impossible true (goalAt 221) 6 state221_256.toFinset :=
  node_ok cuts221 [⟨state221_20,exclude221_20⟩,⟨state221_86,exclude221_86⟩,⟨state221_220,exclude221_220⟩] 0x110120404c05004404110110406000204404190104404110904404890120404810920404490110404410910404150104404110504404444012100888411100850120404810520404450110404410510404410120404c04010404110004400110124200111006440111804440111005440111404440810020400810104440410010400410104440908004404908004404484080004484040050444080000444040000880820404c04020404440410404c080104044140 (by decide +kernel)

def state221_257 : List Sig := [0xafafafafafafafafafafafafafafafafafafafafafafafafaaaaaaaaaaaaaaaa,input 0,input 6,input 7,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_257 : Impossible true (goalAt 221) 5 state221_257.toFinset :=
  node_ok cuts221 [⟨state221_87,exclude221_87⟩] 0x9400250009410044045400110004410110001901044041109044048c00230008c08204044c0011000440811000440031000c040110001101145001101105004140121020000105008101230208101230204101110004101110001110044044450044044440111008884121004440204048808204048c08104044400104044400 (by decide +kernel)

def state221_258 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0000000000000000,input 6,input 7,input 0,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_258 : Impossible true (goalAt 221) 6 state221_258.toFinset :=
  node_ok cuts221 [⟨state221_257,exclude221_257⟩,⟨state221_20,exclude221_20⟩,⟨state221_88,exclude221_88⟩] 0x250401101250008501242009400250409080250408501044041101150401101150004400400104400150410004110404400044044400064244840064041101161401101064245850044241101121001101230204840230008501222008c002302088802302085011210085011302088801300044001210044001302048401102044002220044000440441400440090800444011000440411100440490801050041404003c1110044404840064601910800081918044604840044401110214041110214008c08206008500214048180214048c08044408c0811404111011400440010500440011404414011004440004440440030100440011000850130200c40030100c080301008501110004400242004440111001101151401101242005450151001101111001101121004440111008c844003c888412101000f121008c84111004440105004440105001110800041110105020000105001110111001110301004440204048501400e4810130101003e301008501111008501302010026104044400111004400302004440111004400400a04400 (by decide +kernel)

def state221_259 : List Sig := [0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000000000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0000000000000000,input 6,input 7,input 0,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_259 : Impossible true (goalAt 221) 5 state221_259.toFinset :=
  node_ok cuts221 [] 0x270008c00230408c00170004c00130404c00044001100044044140234008c00230048c00134004c00130044c00130008c00301004c00111001101151001101105001110105001110220008800301008c00120004800111004c00121001101161001101105001110105001110214048c00301008c00110004400121004c00111004840111008884 (by decide +kernel)

def state221_260 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,input 7,input 0,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_260 : Impossible true (goalAt 221) 6 state221_260.toFinset :=
  node_ok cuts221 [⟨state221_259,exclude221_259⟩,⟨state221_221,exclude221_221⟩] 0x4404c04030140110104404c08080004110104404908024200110106404110104424110112100c04022200484022200484012100888080000484012101000f04400110004404414004440191004460111004440c04020600111004440414010500111004440414010500111021404c04030200905011000444004404544004404444022210484011100414004440414004440444040010c04011100c080111004440312010000 (by decide +kernel)

def state221_261 : List Sig := [0xaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaaaaaaaaaaaaaaa,input 0,input 6,input 7,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_261 : Impossible true (goalAt 221) 5 state221_261.toFinset :=
  node_ok cuts221 [] 0x9800220008810220005800120004810120001501044041105044048c00220008804220004c0012000480412000480022000c040120001101145001101105004140111008184105008101220008101220004101120004101120001110044044850044044840111008884111004840204048800204048800104044800104044800 (by decide +kernel)

def state221_262 : List Sig := [0xf000f000f000f000f000f000f000f000f000f000f000f0000000000000000,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000000000,input 6,input 7,input 0,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_262 : Impossible true (goalAt 221) 5 state221_262.toFinset :=
  node_ok cuts221 [] 0x980022000881022000580012000481012000110004400110110500890022000880122000490012000480112000480022000c04012000908004404908004404414004440414004440850122000c04022000440011000c08012000444004404544004404414004440414004440444022000c04022000c080120004440120004840 (by decide +kernel)

def state221_263 : List Sig := [0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000000000,input 6,input 7,input 0,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_263 : Impossible true (goalAt 221) 6 state221_263.toFinset :=
  node_ok cuts221 [⟨state221_261,exclude221_261⟩,⟨state221_86,exclude221_86⟩,⟨state221_262,exclude221_262⟩,⟨state221_21,exclude221_21⟩,⟨state221_198,exclude221_198⟩] 0x260401101260008800242008800260409080220408800044048800160401101160004800400e8480016041003a120404800044044800054144440054041101151401101054145450044141101111001101230104440230008800400e8880023012000422010880011100880013011003a130004800111004800130104440120104800400e84800044044140044009080044401100044041110044049080105004140400e811100444044400545015108000c151404450444004440111022404111022400880020600880022404818022004880004440880012404111012400480010500480012404414012004480004440480030100480012000880030200880030100c080301008800120004800242004840121001101161401101242005850161001101121001101111004840111020002232108884111008c8411101003a121004840105004840105001110800041110105020000105001110121001110301004840204048800222008800301008880301008800121008800302008880104044800121004800302004840121004800222004800 (by decide +kernel)

def state221_264 : List Sig := [0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,input 7,input 0,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_264 : Impossible true (goalAt 221) 6 state221_264.toFinset :=
  node_ok cuts221 [⟨state221_259,exclude221_259⟩,⟨state221_196,exclude221_196⟩,⟨state221_223,exclude221_223⟩] 0x4404c04030140110104404c08080008110104404908024200110105404110104414110111100c04080004444031200444011100c08080000444011101003a04400110004404414004440151004450111004440c04020600111004440414010500111004440414010500111022000c04030200905012000484004404584004404444022210444012100414004440414004440484022200c040121008880121004840222010014 (by decide +kernel)

def state221_265 : List Sig := [0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000,input 4,input 6,input 7,input 0,input 2,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_265 : Impossible true (goalAt 221) 6 state221_265.toFinset :=
  node_ok cuts221 [] 0x981024040901824040581016040581815050190104404110904404444012100888411100941024040901424040541015040541416060150104404110504404111006440111804440111005440111404440111024040818004440111014440414004440110004400110110500d01024040c04024040900024000901004404110114404541404404484016140484016140444015140444015140414004440414004440810120404c04024040410110404c080150509080 (by decide +kernel)

def state221_266 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,input 7,input 0,input 2,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_266 : Impossible true (goalAt 221) 7 state221_266.toFinset :=
  node_ok cuts221 [⟨state221_98,exclude221_98⟩,⟨state221_256,exclude221_256⟩,⟨state221_106,exclude221_106⟩,⟨state221_140,exclude221_140⟩,⟨state221_157,exclude221_157⟩,⟨state221_22,exclude221_22⟩,⟨state221_89,exclude221_89⟩,⟨state221_258,exclude221_258⟩,⟨state221_260,exclude221_260⟩,⟨state221_197,exclude221_197⟩,⟨state221_199,exclude221_199⟩,⟨state221_263,exclude221_263⟩,⟨state221_264,exclude221_264⟩,⟨state221_236,exclude221_236⟩,⟨state221_265,exclude221_265⟩,⟨state221_224,exclude221_224⟩,⟨state221_241,exclude221_241⟩] 0xd05004404110130100908030100d05024200c05030100110104405000404404110130201000430202001040012000f30200110104406000e044041101400b4908024202000d242009080400b4110104404190912100190104404585004404190916140110904404484004405004a12100484030100888030101004a22200888030100484012101004a22200888030200484012101004a12100484030200888022201004a80032000b40050484012101004a12100484040051004a400501505111001501044045450044041505151401105044044440044048c8411100444012101004a121008c8440128888412100444011101003e11100444030101003e30101003e8002a000930100444011100c48440010c48030200444011100c48411100444030201003e30201003e80022000740000444011101003e11100444040001003e40000110110500110024200111004400110104440110124200414010501004a04440111012100191806442000606460111812100111004441003e04440111011100151405442000505450111411100111004442000404440111030100818030102000320600818030100111004441000404440111030200414010502000210500414030200111004442000104440111040030414010502000010500414040030111004441004940010810130101002e30101000430200c080400110004241410048400b84101 (by decide +kernel)

def state221_267 : List Sig := [0xaaaa0000aaaa0000ffff0000ffff0000aaaa0000aaaa0000aaaa0000aaaa,input 0,input 6,input 7,input 2,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_267 : Impossible true (goalAt 221) 5 state221_267.toFinset :=
  node_ok cuts221 [] 0x260009000240209000120004800120204101111004840222104440250009000240109000110004400110104101300009000241009000044001900044201100044001500044101100044009000204041100044005100104041100044041109064041101044041105054041101044049000204049000044044404104041101105001100044041100 (by decide +kernel)

def state221_268 : List Sig := [0xaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 0,input 6,input 7,input 2,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_268 : Impossible true (goalAt 221) 6 state221_268.toFinset :=
  node_ok cuts221 [⟨state221_23,exclude221_23⟩,⟨state221_267,exclude221_267⟩,⟨state221_90,exclude221_90⟩] 0x110120404c05004404110110404441404404190104404110904404890120404810920404480012000480810404150104404110504404444012100888411100850120404810520404440011000440410404c00030000c04010404110124200110120600818012102000212100818011100818411100810130100810122024410111010410111010111004406000104405002d22200484022200484040000444080000444020404880820404c040104044404104044404 (by decide +kernel)

def state221_269 : List Sig := [0xf0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 6,input 7,input 0,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_269 : Impossible true (goalAt 221) 6 state221_269.toFinset :=
  node_ok cuts221 [⟨state221_23,exclude221_23⟩,⟨state221_91,exclude221_91⟩] 0x2405011010440481052420090042405090802405081050440411011505011010440441014001041011505100041105041010440411010642448400640411011614011010642458500442411011210011012203048402201081052220088042203088802203081051210081051202088801200041011210048001202048401202041012220041010440441400440090800444011000440411100440490801050041404003c111004440484006460191080004191804460484004440111020414111020410880c20600810420414818020414880c04440880c1040411101040044041050041001040441401040444040444044044001c111004440444005450151080000151404450444004440111030100410130000810531200c00030100c4803010081051040441010541444400540411011514011010541454500441411011110011012220044401110048404003c484022201000f22200484011100444020414444020404c040400a4810120415002a20414c040111004440110110028110004101111004400110104440110104101400984101 (by decide +kernel)

def state221_270 : List Sig := [0xffff0000ffff0000ffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 4,input 6,input 7,input 0,input 2,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_270 : Impossible true (goalAt 221) 6 state221_270.toFinset :=
  node_ok cuts221 [] 0x981024040901824040480012000480810404484016140585012100484016140585012100444012100888411100941024040901424040440011000440410404444015140545011100444015140545011100111006440111804440111005440111404440111024040818004440410010400410111010414004440111010500414004440111010500c00030000c04010404901030100901022060541410404541410404110120404810124040c040150504101150504101 (by decide +kernel)

def state221_271 : List Sig := [0xffffffffffffffff00000000000000000000000000000000,input 6,input 7,input 0,input 2,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_271 : Impossible true (goalAt 221) 7 state221_271.toFinset :=
  node_ok cuts221 [⟨state221_268,exclude221_268⟩,⟨state221_269,exclude221_269⟩,⟨state221_270,exclude221_270⟩,⟨state221_141,exclude221_141⟩,⟨state221_24,exclude221_24⟩,⟨state221_92,exclude221_92⟩,⟨state221_200,exclude221_200⟩] 0xd05004404110130100908030100d05024200c050301001101044045414044041101104050004104045414400104414104041101044041909121001901044045850044041909161401109044044840044050048121004840301008880301010048222008880301004840121004808222004800104044840120004808121004808104048880104041505111001501044045450044041505151401105044044440044048c84111004440121010048121008c8440120888412100444011101003d11100444030101003d30101003d400ba000630100444011100440440010440010404444011000440411100440410405003d10404110110500110024200111004400110104440110124200414010501004804440111012100191806442000506460111812100111004441003d04440111011100151405442000405450111411100111004441002e04440111030100818030102000320600818030100111004440410104440410011010414010400410110500410111010111011011000440010c00030101002e30101000410404410124201002d242001101400b81101242020002242001101400b41101222010014222004840401204840222010048222004840400504840400f50000400004440400f44440400b9003d80004444040000444020601000c206001110400b8111020602000020600111040030111040011004b20405002e40128c080 (by decide +kernel)

def state221_272 : List Sig := roots 221
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude221_272 : Impossible true (goalAt 221) 8 state221_272.toFinset :=
  node_ok cuts221 [⟨state221_25,exclude221_25⟩,⟨state221_93,exclude221_93⟩,⟨state221_117,exclude221_117⟩,⟨state221_142,exclude221_142⟩,⟨state221_158,exclude221_158⟩,⟨state221_170,exclude221_170⟩,⟨state221_201,exclude221_201⟩,⟨state221_232,exclude221_232⟩,⟨state221_246,exclude221_246⟩,⟨state221_247,exclude221_247⟩,⟨state221_250,exclude221_250⟩,⟨state221_255,exclude221_255⟩,⟨state221_266,exclude221_266⟩,⟨state221_271,exclude221_271⟩] 0x80034c04010404c00040010810130200c00080030c04030200c0404001081011040441018002c9010044049000400b48101242009000800289010242009010400b48101044041101400105414044041101400b441018002441018002054148001c4414400b44101044041101400508808121008800400508101222008800400508808222008808400508101121008101400504808222004800400504101121004800400504808121004808400504101222004101400501909121001901400501101161401101400501909161401109400501101121001101400008505111008501400008101400008101400008505800188105400008101111008101400004404800144400400004101111004400400004404111004404400004101400004101400001505111001501400001101151401101400001505151401105400001101111001101400508c84111004440400504840400504840400508c844005088844005048401110044408001081010444081004003088082060081008000c8101206008101400308808044408808400104101044404100400304404105004100800084101105004101400304404044404404400b411011050011004003090800444011004000c1101044401101400b49080105004140400510014044401110400504840064601910400520001064601118400504840044401110400010000044401110400004440054501510400020000054501114400004440044401110 (by decide +kernel)

theorem lower221 : Claim 221 9 :=
  fromSearch 26116 (by decide +kernel) exclude221_272

open PEqualNP.CircuitLowerBounds

def graph : Sig := goalAt 255
theorem graph_proper : proper graph := by unfold proper; decide +kernel

def edgeList : List Nat := [0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 3, 7, 4, 7, 5, 7, 6, 7]
def target (x : Fin 8 → Bool) : Bool :=
  decide (∃ i < edgeList.length / 2,
    (List.ofFn x).getD (edgeList.getD (2*i) 0) false = true ∧
    (List.ofFn x).getD (edgeList.getD (2*i+1) 0) false = true)

-- The conjunctions cover all of the posted edges.
def smallCircuit : Circuit := ⟨[⟨.or,[0,7]⟩, ⟨.or,[0,3]⟩, ⟨.or,[1,8]⟩, ⟨.or,[2,8]⟩, ⟨.or,[4,6]⟩, ⟨.or,[5,6]⟩, ⟨.or,[6,7]⟩, ⟨.and,[12,10]⟩, ⟨.and,[13,11]⟩, ⟨.and,[9,14]⟩, ⟨.or,[15,16]⟩, ⟨.or,[18,17]⟩],19⟩

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
  (ruleFor 255 lower221 none (by decide +kernel)).property 10 eightInputs
    (by decide +kernel) (by decide +kernel)


end PEqualNP.Outside.L_meta_31693

open PEqualNP.Outside.L_meta_31693 in
theorem PEqualNP.Outside.L_meta_31693 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o fit _ correct
  exact replaceShort lowerGraph gates o fit correct

import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_28970

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
  (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 2 &&& x 5) ||| (x 1 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 5 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7)

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



def cuts161 : Cuts (goalAt 161) := []

def state161_0 : List Sig := roots 161
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude161_0 : Impossible true (goalAt 161) 3 state161_0.toFinset :=
  node_ok cuts161 [] 0x28080210128000810128200a00028080a08028080810108404210120404212020400a02020600810020404818020404a02008480212008404818008400a08008480210008404212008404a080206008180 (by decide +kernel)

theorem lower161 : Claim 161 4 :=
  fromSearch 5 (by decide +kernel) exclude161_0

theorem lower177 : Claim 177 5 :=
  fromLift 5 16 4 lower161 (by decide +kernel)


def cuts145 : Cuts (goalAt 145) := []

def state145_0 : List Sig := roots 145
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude145_0 : Impossible true (goalAt 145) 3 state145_0.toFinset :=
  node_ok cuts145 [] 0x240401101240008101242009000240409080240408101044041101204041110204009010206008100204048180204049010044401110044048180044009080044401100044041110044049080206008180 (by decide +kernel)

theorem lower145 : Claim 145 4 :=
  fromSearch 4 (by decide +kernel) exclude145_0

theorem lower165 : Claim 165 5 :=
  fromLift 5 4 1285 lower161 (by decide +kernel)


def cuts53 : Cuts (goalAt 53) := []

def state53_0 : List Sig := roots 53
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude53_0 : Impossible true (goalAt 53) 3 state53_0.toFinset :=
  node_ok cuts53 [] 0x44042101090501101090002400090102101054041101044141101084002100084042404044001100044042120044401510044501110 (by decide +kernel)

theorem lower53 : Claim 53 4 :=
  fromSearch 1284 (by decide +kernel) exclude53_0

def cuts180 : Cuts (goalAt 180) := []

def state180_0 : List Sig := roots 180
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude180_0 : Impossible true (goalAt 180) 3 state180_0.toFinset :=
  node_ok cuts180 [] 0x28000a00028080240424000900024040a0200d010240409050240425040901024050901009000240009010a080090803420090c02420 (by decide +kernel)

theorem lower180 : Claim 180 4 :=
  fromSearch 1076299008 (by decide +kernel) exclude180_0

def rule181_0 : {c : Cut // CutGood (goalAt 181) c} :=
  ruleFor 181 lower177 none (by decide +kernel)

def rule181_1 : {c : Cut // CutGood (goalAt 181) c} :=
  ruleFor 181 lower145 none (by decide +kernel)

def rule181_2 : {c : Cut // CutGood (goalAt 181) c} :=
  ruleFor 181 lower165 (some (3,input 0,input 2)) (by decide +kernel)

def rule181_3 : {c : Cut // CutGood (goalAt 181) c} :=
  ruleFor 181 lower165 (some (1,input 0,input 2)) (by decide +kernel)

def rule181_4 : {c : Cut // CutGood (goalAt 181) c} :=
  ruleFor 181 lower165 none (by decide +kernel)

def rule181_5 : {c : Cut // CutGood (goalAt 181) c} :=
  ruleFor 181 lower53 none (by decide +kernel)

def rule181_6 : {c : Cut // CutGood (goalAt 181) c} :=
  ruleFor 181 lower180 none (by decide +kernel)

def rule181_7 : {c : Cut // CutGood (goalAt 181) c} :=
  ruleFor 181 lower165 (some (2,input 2,input 7)) (by decide +kernel)

def rule181_8 : {c : Cut // CutGood (goalAt 181) c} :=
  ruleFor 181 lower165 (some (1,input 2,input 7)) (by decide +kernel)

def cuts181 : Cuts (goalAt 181) := [rule181_0,rule181_1,rule181_2,rule181_3,rule181_4,rule181_5,rule181_6,rule181_7,rule181_8]

def state181_0 : List Sig := [0xfffffffffffffffffffffffffffffffffafafafafafafafafafafafafafafafa,input 7,input 0,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude181_0 : Impossible true (goalAt 181) 4 state181_0.toFinset :=
  node_ok cuts181 [] 0x840481010920021010900024000840500010440421010905011010440481012405011010d0801101044042420084042104084042401044041104044048180204048104204041114044409010 (by decide +kernel)

def state181_1 : List Sig := [0xfafafafafafafafafafafafafafafafa,input 7,input 0,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude181_1 : Impossible true (goalAt 181) 4 state181_1.toFinset :=
  node_ok cuts181 [] 0xa00028000a0200840411010840424140440490002400090100440421010841021010900411010441011012060081002040081802404024000900021012820011010d0801101090801110044401114090808101 (by decide +kernel)

def state181_2 : List Sig := [0xfafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafa,input 0,input 4,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude181_2 : Impossible true (goalAt 181) 5 state181_2.toFinset :=
  node_ok cuts181 [⟨state181_0,exclude181_0⟩,⟨state181_1,exclude181_1⟩] 0xa02008404a00020404a08028000a02028200a02020404210108404901004404900020404908024000901024200901020404110104404341404404110108405000308404341440004241408404110104404810104450810124040818420410810120610810124040111424040210104450210109011000108410210140004210109010111409004110120610110124200111404410110104450110124200818424201000240000111020404242020404901080004901020406000020404901009080901008405000109000a08009080240008404242008404a08040004a0800440424200440490800d0c03420044043430044049080090802420 (by decide +kernel)

def state181_3 : List Sig := [0xffff0000ffff0000ffff0000ffff0000aaaa0000aaaa0000aaaa0000aaaa,input 0,input 7,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude181_3 : Impossible true (goalAt 181) 4 state181_3.toFinset :=
  node_ok cuts181 [] 0x2c0009000240809000090002400090102101250009000240109000044003100084041100044001500044101100044009000204041100044042404084041101044041105054041101044049000204049000084801100044041100 (by decide +kernel)

def state181_4 : List Sig := [0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 0,input 7,input 2,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude181_4 : Impossible true (goalAt 181) 5 state181_4.toFinset :=
  node_ok cuts181 [⟨state181_0,exclude181_0⟩,⟨state181_3,exclude181_3⟩] 0x210120404a080084042404084042101090101101084042414044041101204049080044060001044041101400102400090002404084041501044041105044048501204048105204042420400020000090809010084042404084042404044049080044048180206002420206102420204048180400141110 (by decide +kernel)

def state181_5 : List Sig := [0x5555555555555555555555555555555550505050505050505050505050505050,input 0,input 7,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude181_5 : Impossible true (goalAt 181) 4 state181_5.toFinset :=
  node_ok cuts181 [] 0x2101204042480084041101084042414044041101204049014044042100084002101090101100044001101084808100204008101044402400090002404084042420044042430044049010204049014204041114 (by decide +kernel)

def state181_6 : List Sig := [0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 7,input 0,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude181_6 : Impossible true (goalAt 181) 5 state181_6.toFinset :=
  node_ok cuts181 [⟨state181_0,exclude181_0⟩,⟨state181_5,exclude181_5⟩] 0x1000108404210120414a080280110001282002480204142101084042420084042400400042404090002420090102404400042101084043414044041101084050008084043414400042414084041101044049014044041101204149080240109014242009014204141101044043430044041101090801505054043430054141105090801101044042101044402100090102120084002101084802101090101110090101101084801100242001110044001101044401101242002120084808105044408104240508180204108105206008105240501110044420001044401110090801514054420000054501114090801110044410007400008101 (by decide +kernel)

def state181_7 : List Sig := roots 181
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude181_7 : Impossible true (goalAt 181) 6 state181_7.toFinset :=
  node_ok cuts181 [⟨state181_2,exclude181_2⟩,⟨state181_4,exclude181_4⟩,⟨state181_6,exclude181_6⟩] 0x40004a02008404a00040004810128200a00040004a02028200a0204000481010840421014001090100440490004001081012420090004001090102420090104001081010440411014001034140440411014001021014001021014001034144000424144001021010440411014000085050908085014000081014000081014000085058000881054000081010908081014000024044000424004000021010908024004000024040908024044000021014000021014001015050908015014001011010d0c011014001015050d0c01105400101101090801101400148101044408100400189010206008100800048101206008101400149010044401110400042101044402100400042404084802100400042101084802101400042404044402404400101101084801100400109080044401100400101101044401101400109080084802120400010000044401110400002420054501510400020000054501114400002420044401110 (by decide +kernel)

theorem lower181 : Claim 181 7 :=
  fromSearch 1284 (by decide +kernel) exclude181_7

def cuts146 : Cuts (goalAt 146) := []

def state146_0 : List Sig := roots 146
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude146_0 : Impossible true (goalAt 146) 3 state146_0.toFinset :=
  node_ok cuts146 [] 0x24040120224000820224200900024040908024040820204808120220808121020800901020a00820020808828020808901004840121004808828004800908004840120004808121004808908020a008280 (by decide +kernel)

theorem lower146 : Claim 146 4 :=
  fromSearch 268501056 (by decide +kernel) exclude146_0

theorem lower178 : Claim 178 5 :=
  fromLift 5 32 275841088 lower146 (by decide +kernel)


def cuts166 : Cuts (goalAt 166) := []

def state166_0 : List Sig := roots 166
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude166_0 : Impossible true (goalAt 166) 3 state166_0.toFinset :=
  node_ok cuts166 [] 0x28000a00028080820221808820220818820209000240009010a08020800820020808a020098102404090182404098802420090882420 (by decide +kernel)

theorem lower166 : Claim 166 4 :=
  fromSearch 270534000 (by decide +kernel) exclude166_0

def rule182_0 : {c : Cut // CutGood (goalAt 182) c} :=
  ruleFor 182 lower178 none (by decide +kernel)

def rule182_1 : {c : Cut // CutGood (goalAt 182) c} :=
  ruleFor 182 lower166 none (by decide +kernel)

def rule182_2 : {c : Cut // CutGood (goalAt 182) c} :=
  ruleFor 182 lower180 none (by decide +kernel)

def rule182_3 : {c : Cut // CutGood (goalAt 182) c} :=
  ruleFor 182 lower146 none (by decide +kernel)

def rule182_4 : {c : Cut // CutGood (goalAt 182) c} :=
  ruleFor 182 lower178 (some (0,input 5,input 7)) (by decide +kernel)

def cuts182 : Cuts (goalAt 182) := [rule182_0,rule182_1,rule182_2,rule182_3,rule182_4]

def state182_0 : List Sig := [0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc,input 1,input 4,input 2,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude182_0 : Impossible true (goalAt 182) 5 state182_0.toFinset :=
  node_ok cuts182 [] 0xa00028000a0202080886022080882062080824000900024042820016020480812060480824200988826220908012022080890100480812020c808341404808908020808901020808121009818240409818240404840161004850121004808121040004828020808a02020808a020098182404098182404 (by decide +kernel)

def state182_1 : List Sig := [0xffff0000ffff0000ffff0000ffff0000cccc0000cccc0000cccc0000cccc,input 1,input 7,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude182_1 : Impossible true (goalAt 182) 4 state182_1.toFinset :=
  node_ok cuts182 [] 0x2c000900024080900009000240009010a0802500090002401090000480032000981812000480016000481012000480090002080812000480824040c808120204808120605808120204808900020808900020a001200048081200 (by decide +kernel)

def state182_2 : List Sig := [0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 1,input 7,input 2,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude182_2 : Impossible true (goalAt 182) 5 state182_2.toFinset :=
  node_ok cuts182 [⟨state182_1,exclude182_1⟩] 0xa2022080882222080824040981826060901012020c80824140480812022080890800480a0000048081202400042400090002404282001602048081206048088602208088206208082420098882622090809010098182404098182404048089080048088280098882420098882420208088280280881210 (by decide +kernel)

def state182_3 : List Sig := [0xf3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 1,input 7,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude182_3 : Impossible true (goalAt 182) 4 state182_3.toFinset :=
  node_ok cuts182 [] 0x288088202208888202048083202090501202048088202240501202098102404090182404048001200048088680208008200208081210048401610048501210090002400090110003058081202048181202218088202208188202 (by decide +kernel)

def state182_4 : List Sig := [0x3333333333333333333333333333333300000000000000000000000000000000,input 1,input 7,input 2,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude182_4 : Impossible true (goalAt 182) 5 state182_4.toFinset :=
  node_ok cuts182 [⟨state182_3,exclude182_3⟩] 0xa2022080882222080812020c8082414048081202208089080048082400090002404282001602048081206048088602208088206208082604090102406090101200048001202242001210058401214048408200208081210282002404282002404242001202242001202400002420800002420240408280 (by decide +kernel)

def state182_5 : List Sig := [0xffffffff00000000ffffffff00000000f0f0f0f000000000f0f0f0f0,0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 7,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude182_5 : Impossible true (goalAt 182) 4 state182_5.toFinset :=
  node_ok cuts182 [] 0x480890042405012020d000240005818240004800120004808828020810820420818121009800240009008240028000240404808340404808240409018260409010240409200a004090110004 (by decide +kernel)

def state182_6 : List Sig := [0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 7,input 1,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude182_6 : Impossible true (goalAt 182) 5 state182_6.toFinset :=
  node_ok cuts182 [⟨state182_5,exclude182_5⟩] 0x1000309010240420818a0802801100032820024802081824040901024208000024004000c24040900024200901024044000d00034000c34140480812020901032220c80834140c88824140901012020480890140480812022081890802401090142420090142081812020480834300480812020908016060580834300581812060908012020480826060484026040901032300901026060c8c0240609010121009010120220a00120024200121004800120204840120224200828020a00820604840820424050828020810820620a008206240501210048402622048401210090801614058402622058501214090801210048410000400008202 (by decide +kernel)

def state182_7 : List Sig := [0x3333333333333333333333333333333333330000333300003333000033330000,input 4,input 7,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude182_7 : Impossible true (goalAt 182) 4 state182_7.toFinset :=
  node_ok cuts182 [] 0x28800820020880820009000240009010a0802180082002081082000580012000481012000480032000d05012000480082002404012000484024040c840240404840121405840121004840820024040820020a001200048401200 (by decide +kernel)

def state182_8 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 4,input 7,input 1,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude182_8 : Impossible true (goalAt 182) 5 state182_8.toFinset :=
  node_ok cuts182 [⟨state182_7,exclude182_7⟩] 0x24042404090300901024040d05034140901024000900024042820094102404090142404024200d0c034300908024200d0c0343009080260409010240609010121005840121404840121024040828004840828004840121020a0200000484012104000882020d05024040d0502404240409080280c01202 (by decide +kernel)

def state182_9 : List Sig := [0xf0f0fffff0f0fffff0f0fffff0f0fffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 4,input 7,input 1,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude182_9 : Impossible true (goalAt 182) 4 state182_9.toFinset :=
  node_ok cuts182 [] 0x9010a004240c02404098102404090182404208108204208181210048001200048088280048401610048501210048083202090501202240009000240401202090002400090110003208088202208189010058081202048181202 (by decide +kernel)

def state182_10 : List Sig := [0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000,input 4,input 7,input 1,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude182_10 : Impossible true (goalAt 182) 5 state182_10.toFinset :=
  node_ok cuts182 [⟨state182_9,exclude182_9⟩] 0x240424040903009010240009000240428200941024040901424040160204808120604808260409010240609010121005840121404840121024040828004840120004800120220a0012020c808241404808900024040120228200240428200240440000242080000242020a00121020a001210208089080 (by decide +kernel)

def state182_11 : List Sig := roots 182
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude182_11 : Impossible true (goalAt 182) 6 state182_11.toFinset :=
  node_ok cuts182 [⟨state182_0,exclude182_0⟩,⟨state182_2,exclude182_2⟩,⟨state182_4,exclude182_4⟩,⟨state182_6,exclude182_6⟩,⟨state182_8,exclude182_8⟩,⟨state182_10,exclude182_10⟩] 0x4000ca02009010a0004000c820228200a0004000ca02028200a0204000c82020901082028001490100480890004000482022420090008001090102420090104000482020480812024000c34140480812024000c24040c88832024000c34140c88824144000c24040480812024000086060908086024000082024000082024000086068000c82064000082020908082024000024044000c240040000a08009080240040000240409080240440000a08040000a0804000016060908016024000012020d0c012024000016060d0c0120640000120209080120280008820204840820040008901020a00820080004820220a0082024000890100484012104000c26060484026044000c24040c8c024044000c26060c8c024064000c240404840240440004120220a00120040008908004840120080000120204840120240004908020a008280400002622048401210400002420058501610400002622058501214400002420048401210 (by decide +kernel)

theorem lower182 : Claim 182 7 :=
  fromSearch 270599488 (by decide +kernel) exclude182_11

theorem lower163 : Claim 163 5 :=
  fromLift 5 2 117 lower161 (by decide +kernel)


theorem lower147 : Claim 147 5 :=
  fromLift 5 1 68 lower146 (by decide +kernel)


def rule179_0 : {c : Cut // CutGood (goalAt 179) c} :=
  ruleFor 179 lower177 none (by decide +kernel)

def rule179_1 : {c : Cut // CutGood (goalAt 179) c} :=
  ruleFor 179 lower178 none (by decide +kernel)

def rule179_2 : {c : Cut // CutGood (goalAt 179) c} :=
  ruleFor 179 lower163 none (by decide +kernel)

def rule179_3 : {c : Cut // CutGood (goalAt 179) c} :=
  ruleFor 179 lower147 none (by decide +kernel)

def cuts179 : Cuts (goalAt 179) := [rule179_0,rule179_1,rule179_2,rule179_3]

def state179_0 : List Sig := roots 179
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_0 : Impossible true (goalAt 179) 6 state179_0.toFinset :=
  node_ok cuts179 [] 0x4000ca02008404a0004000c810128200a0004000ca02028200a0204000c81010840421014000890100440490004000881012420090004000890102420090104000881010440411014000d00030440411014000c21010c88821014000d00020c88812224000c210104404110140000820204840820040000810120a00820040000820220a0082024000081010484081014000c23030484023014000c21010c8c021014000c23030c8c021034000c210104840210140008120220a00120040008110104840120040008120204840120240008110120a0011014000481010444081004000482022060081004000481012060081014000482020444082024000c21010444021004000ca0800848021004000c21010848021014000ca08004440111040008110108480110040008120204440110040008110104440110140008120208480120240001000004440111040000121008c88121040001000108c882122400001210044401110 (by decide +kernel)

theorem lower179 : Claim 179 7 :=
  fromSearch 68 (by decide +kernel) exclude179_0

theorem lower167 : Claim 167 6 :=
  fromLift 6 2 1397 lower165 (by decide +kernel)


def cuts51 : Cuts (goalAt 51) := []

def state51_0 : List Sig := roots 51
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude51_0 : Impossible true (goalAt 51) 3 state51_0.toFinset :=
  node_ok cuts51 [] 0x4404210104888110108c0421010840c2101048001200048081101084002100084041110044001100044041202044401210084881110 (by decide +kernel)

theorem lower51 : Claim 51 4 :=
  fromSearch 68 (by decide +kernel) exclude51_0

theorem lower55 : Claim 55 5 :=
  fromLift 5 2 1348 lower53 (by decide +kernel)


def rule183_0 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower181 none (by decide +kernel)

def rule183_1 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower182 none (by decide +kernel)

def rule183_2 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower179 none (by decide +kernel)

def rule183_3 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower182 (some (3,input 2,input 5)) (by decide +kernel)

def rule183_4 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower181 (some (3,input 2,input 5)) (by decide +kernel)

def rule183_5 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower167 (some (3,input 2,input 5)) (by decide +kernel)

def rule183_6 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower147 none (by decide +kernel)

def rule183_7 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower179 (some (2,input 5,input 7)) (by decide +kernel)

def rule183_8 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower146 none (by decide +kernel)

def rule183_9 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower145 none (by decide +kernel)

def rule183_10 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower182 (some (1,input 2,input 7)) (by decide +kernel)

def rule183_11 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower181 (some (1,input 2,input 7)) (by decide +kernel)

def rule183_12 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower167 (some (1,input 2,input 7)) (by decide +kernel)

def rule183_13 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower179 (some (2,input 4,input 7)) (by decide +kernel)

def rule183_14 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower51 none (by decide +kernel)

def rule183_15 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower55 none (by decide +kernel)

def rule183_16 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower179 (some (1,input 4,input 5)) (by decide +kernel)

def rule183_17 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower179 (some (3,input 5,input 7)) (by decide +kernel)

def rule183_18 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower179 (some (1,input 5,input 7)) (by decide +kernel)

def rule183_19 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower179 (some (0,input 5,input 7)) (by decide +kernel)

def rule183_20 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower167 none (by decide +kernel)

def rule183_21 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower179 (some (3,input 4,input 5)) (by decide +kernel)

def rule183_22 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower181 (some (1,input 4,input 5)) (by decide +kernel)

def rule183_23 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower163 none (by decide +kernel)

def rule183_24 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower179 (some (2,input 4,input 5)) (by decide +kernel)

def rule183_25 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower182 (some (1,input 4,input 5)) (by decide +kernel)

def rule183_26 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower165 (some (3,input 2,input 5)) (by decide +kernel)

def rule183_27 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower179 (some (3,input 4,input 7)) (by decide +kernel)

def rule183_28 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower182 (some (1,input 4,input 7)) (by decide +kernel)

def rule183_29 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower181 (some (1,input 4,input 7)) (by decide +kernel)

def rule183_30 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower179 (some (1,input 4,input 7)) (by decide +kernel)

def rule183_31 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower163 (some (3,input 1,input 7)) (by decide +kernel)

def rule183_32 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower179 (some (0,input 4,input 7)) (by decide +kernel)

def rule183_33 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower182 (some (3,input 4,input 7)) (by decide +kernel)

def rule183_34 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower181 (some (3,input 4,input 7)) (by decide +kernel)

def rule183_35 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower147 (some (1,input 0,input 1)) (by decide +kernel)

def rule183_36 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower165 (some (1,input 2,input 7)) (by decide +kernel)

def rule183_37 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower182 (some (1,input 5,input 7)) (by decide +kernel)

def rule183_38 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower181 (some (1,input 5,input 7)) (by decide +kernel)

def rule183_39 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower182 (some (3,input 5,input 7)) (by decide +kernel)

def rule183_40 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower181 (some (3,input 5,input 7)) (by decide +kernel)

def cuts183 : Cuts (goalAt 183) := [rule183_0,rule183_1,rule183_2,rule183_3,rule183_4,rule183_5,rule183_6,rule183_7,rule183_8,rule183_9,rule183_10,rule183_11,rule183_12,rule183_13,rule183_14,rule183_15,rule183_16,rule183_17,rule183_18,rule183_19,rule183_20,rule183_21,rule183_22,rule183_23,rule183_24,rule183_25,rule183_26,rule183_27,rule183_28,rule183_29,rule183_30,rule183_31,rule183_32,rule183_33,rule183_34,rule183_35,rule183_36,rule183_37,rule183_38,rule183_39,rule183_40]

def state183_0 : List Sig := [0xffffffffffffffffffffffffffffffff0f0f0f0f000000000f0f0f0f00000000,input 7,input 5,input 0,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_0 : Impossible true (goalAt 183) 6 state183_0.toFinset :=
  node_ok cuts183 [] 0x34100440434000900032220900034100c888241009000110109000b03004404110128080908028080b03024200a0302808011010440434300440411010908032220908034300c888342009080110104404120220a0012000440412100480012020484012020440482800440426020484026000900032300900026020c8c0240209000121009000a22204840121028080828028080a22220a00a0222808012100484026220484012100908032300908026220c8c0262009080121004840110108480110004808111004400110104440110104808212004809000904440111004840232204841000808c88212204840111004440250104440250009000212009000250108480240109000111009001000804440111028080818028081000820600818028080111004441000804440111009080212008481000808480212009080111004440a02009000240040018a08028200a02028200a02040018240009000242009000240040008a080084042420282002420400082400090010007400188101 (by decide +kernel)

def state183_1 : List Sig := [0x3333333333333333333333333333333333330000333300003333000033330000,input 4,input 7,0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000,input 5,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_1 : Impossible true (goalAt 183) 5 state183_1.toFinset :=
  node_ok cuts183 [] 0x250009000240109000830020800820120800130004800120104800240020800a2200900021200444021200444021010908082002888082000908012000c88012000908012100c8c012100480024000d04012000480082002404012000444021200444012100484024000d0402400204048200240408200044041200048401200 (by decide +kernel)

def state183_2 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 4,input 7,0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000,input 5,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_2 : Impossible true (goalAt 183) 6 state183_2.toFinset :=
  node_ok cuts183 [⟨state183_1,exclude183_1⟩] 0x9800240009008240004840901020a00121020a0012100484082808000012100484100040444012100848811100940024000900424000444090102060011100848011100444021200848011100444021200900090102c0c024000900034100d040240009080121009880121008480111008480111008404242024040b0302404024200d0c034300908024200d0c034300908081010d04024000d0402400240409080280c01101 (by decide +kernel)

def state183_3 : List Sig := [0xf0fffff0000ffff0f0fffff0000ffff0f0f0f0f000000000f0f0f0f00000000,input 4,input 7,input 5,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_3 : Impossible true (goalAt 183) 5 state183_3.toFinset :=
  node_ok cuts183 [] 0x980024000900824000484090102808812100480012000480811010444012100848811100940024000900424000444090102060011100440011000440412020900090102808024000d00024000904024002400090002404011010908012100988012100848011100848011100840424000908024002040481012808090100908011010d0801101 (by decide +kernel)

def state183_4 : List Sig := [0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000,input 4,input 7,0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000,input 5,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_4 : Impossible true (goalAt 183) 6 state183_4.toFinset :=
  node_ok cuts183 [⟨state183_3,exclude183_3⟩] 0x9800240009008240004840901020a0012100480012000480811010444012100848811100940024000900424000444090102060011100440011000440412020900090102c0c0240009080121009880121008480111008480111008404242024040b03024040242004404342004404340009000241009000900024040110120a00121020a001210206001110206001110292002400292002400400182420800002420204049080 (by decide +kernel)

def state183_5 : List Sig := [0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000,input 5,input 0,input 1,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_5 : Impossible true (goalAt 183) 7 state183_5.toFinset :=
  node_ok cuts183 [⟨state183_0,exclude183_0⟩,⟨state183_2,exclude183_2⟩,⟨state183_4,exclude183_4⟩] 0x8000890100440490004001481012420090008000490102420090104001481010440411014001834100440434004001424000c88824004001834100c888241040014240004404240040010820204840820040010810120a00820040010820220a00820240010810104840810140010120220a00120040010110104840120040010120204840120240010110120a0011014001026020484026004001024000c8c024004001026020c8c024024001024000484024004000c81010444081004000c82022060081004000c81012060081014000c82020444082024000c11010848011004000c12020444011004000c11010444011014000c120208480120240011000404440111040010121008c88121040011000308c8821224001012100444011104000c25010444025004000c24000848024004000c25010848024014000c240004440240040018a02009000240040018810129200a40040018a02029200a02040018810109000240040018a02009080242040018810140018810140018a02080000a0204001881010908081014001432220908024204001811010d0c011014001832220d0c034204001411010908011014001032300908024204001012100988812104001032300988826204001012100908012104000c21200908021204000c11104000c11104000c21204000c21204000c1110090801110400090002400082101 (by decide +kernel)

def state183_6 : List Sig := [0x3333333333333333333333333333333333333030333330303333303033333030,input 4,0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 7,input 0,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_6 : Impossible true (goalAt 183) 5 state183_6.toFinset :=
  node_ok cuts183 [] 0x2101280102480084042600098002404084042100084002101090108104204108105208181110054401114044401300048001201048008200048003200090501200048009004240501200048001600044141200090102101090102101044402120044401210204148206208108204048401214058401210044041200058101200 (by decide +kernel)

def state183_7 : List Sig := [0xfffffffffffffffffffffffffffffffffffff0f0fffff0f0fffff0f0fffff0f0,input 4,0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 7,input 0,input 1,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_7 : Impossible true (goalAt 183) 6 state183_7.toFinset :=
  node_ok cuts183 [⟨state183_6,exclude183_6⟩] 0x21012801024800840421010901024040840421010901024040840423010840421030840482042081082062041412100584012140484016040581016060541600000484012104002c21000840021010901011100484021220444081042041081052081811100544011140444015040541015050581821200444011100848090104003424200d01021010905021012401090042405015050d0c01505044141101 (by decide +kernel)

def state183_8 : List Sig := [0x3333333333333333333333333333333333330000333300003333000033330000,input 4,input 7,0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 0,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_8 : Impossible true (goalAt 183) 5 state183_8.toFinset :=
  node_ok cuts183 [] 0x240009000240408404210120810a0800840421000840021010901011100544011140444083042081082052081013000480012010480082000480032000d05012000480016000481012000480082042405012000484021010c8402101044402120044401210048401214058401210204148204240508204044041200048401200 (by decide +kernel)

def state183_9 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 4,input 7,0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 0,input 1,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_9 : Impossible true (goalAt 183) 6 state183_9.toFinset :=
  node_ok cuts183 [⟨state183_8,exclude183_8⟩] 0x900024000901021010840490142820021010840434140d050210108c0421010840c210104840161004850121004840901420a00121020a00121004840828080000121004841000b0840021000840424040444012100848811100444015100445011100444090142060011100848011100444021200848011100444021200908034300d0c024202404081050d05021010d05021010d0c024200d0c02420240509080400301101 (by decide +kernel)

def state183_10 : List Sig := [0xf0f0f0f0f0f00000f0f0f0f0f0f0000,input 4,input 5,input 7,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_10 : Impossible true (goalAt 183) 5 state183_10.toFinset :=
  node_ok cuts183 [] 0x82002080082022040426000900024020900016000580016020540411100484021220444081002040081012080825000900024010900015000540015010580824002800024800900090002400090140540434000900024140900012100485012100584011100445011100544090100840424000d04024000440411010d0801501 (by decide +kernel)

def state183_11 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_11 : Impossible true (goalAt 183) 5 state183_11.toFinset :=
  node_ok cuts183 [] 0x121005840121404840322004840121020a0026800484012100920082042081082062041411100484021220444011100544011140444021200444011100848025800444011100920081042041081052081881012040481054004034200908024300908011010d05081050905081050908024800908082220840421010d0508105 (by decide +kernel)

def state183_12 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,input 5,0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 7,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_12 : Impossible true (goalAt 183) 6 state183_12.toFinset :=
  node_ok cuts183 [⟨state183_10,exclude183_10⟩,⟨state183_11,exclude183_11⟩] 0x208108204208188105048401610048501210048403210048c012100c880121004840828020a0012100484082800444012100848811102041081042041482060444015100445011100444031100848011100848011100444021202060011100444081802040434142041600012041434100d04034144001821012405081052405081050d0802420090c024200d050322209050110124050810524050810509082000009081000e (by decide +kernel)

def state183_13 : List Sig := [0xfffffffffffffffffffffffffffffffffffffffff0f0f0f0fffffffff0f0f0f0,input 5,0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 7,input 0,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_13 : Impossible true (goalAt 183) 6 state183_13.toFinset :=
  node_ok cuts183 [] 0x110124010901404404110105414150504404110109010241404404110105414150504404120004800120204404820420810820620414121005850161404840260409010240609010121005850161404840110004400110104808111004840212204440810420410810520818111005450151404440250409010240509010111005450151404440a0204001d000709010a004092002404090802404084142101 (by decide +kernel)

def state183_14 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 0,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_14 : Impossible true (goalAt 183) 6 state183_14.toFinset :=
  node_ok cuts183 [⟨state183_11,exclude183_11⟩] 0x34300440411010908015050540434300541411050908011010440500060440411010920032220c88a00000c88832220920011010440490140440411012041432222401090140c888901420414110104404120220a0012000440412100480012020484012020440482800440426220484012100908016140584026220585012140908012100484100060484012100920032300c8c100090c8c032300920012100484082060484082042041432302081082060c8c0820620414121020414110108480110004808111004400110104440110104808212004809000904440111004840232204841000808c8821220484011100444100080444011100908015140544100080545011140908011100444100060444011100920021200848100080848021200920011100444081050444081042081821202041081050848081052081811102081881054001881014000824202040481050908081054000900124000824204003824204001824800920024200920024204001900062088900114003c2101 (by decide +kernel)

def state183_15 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,input 7,0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 0,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_15 : Impossible true (goalAt 183) 6 state183_15.toFinset :=
  node_ok cuts183 [] 0x440415010441411010440490802420011010440432220c88811010440432220c888110104800120004808110104840161004850121004840828020a0012100484032300c8c012100484032300c8c012100440011000440412020444012100848811100444015100445011100444081802060011100444021200848011100444021200848011104001c242009081000228080810509080a0800908100064003ca080092002101 (by decide +kernel)

def state183_16 : List Sig := [0xffffffff00000000ffffffff00000000000000000000000000000000,input 5,0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 0,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_16 : Impossible true (goalAt 183) 6 state183_16.toFinset :=
  node_ok cuts183 [] 0xd0c011010440424200541415010d0c015050441424200440411010d05011010440421010c88821010d050322209050210104404110104808828004800110104840120004808121004808110120a00110109888121004840242005850161009888161404850242004840121008c0c121008c0421010c8c0210108c0c32300840c210104840210104404212004400120204440110004404111004404120208480120240024111004440121008c88121040020232208488121004440111040020111004440242005450151040020151404450242004440111008404111008400240408480210008404212008404240404440240409080210109001000609010240009080240409011000608404210124200810524010110124050110124200901424050110120414110120a00810520810121020818820420a00820620818121020414810520600820620410111020414810420600810520414111020818820640019001320405000f400482480 (by decide +kernel)

def state183_17 : List Sig := [0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 7,input 0,input 1,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_17 : Impossible true (goalAt 183) 7 state183_17.toFinset :=
  node_ok cuts183 [⟨state183_7,exclude183_7⟩,⟨state183_9,exclude183_9⟩,⟨state183_12,exclude183_12⟩,⟨state183_13,exclude183_13⟩,⟨state183_14,exclude183_14⟩,⟨state183_15,exclude183_15⟩,⟨state183_16,exclude183_16⟩] 0x4003e000608404210140018810528200a0048001600042820024804001881050840421014003824200840424004001900060901024008000c24200901024044001900060840421014001834140440411014003021010c88821018000834140c88824144003021010440411014003c90140440411014003081052420090048000490142420090144003081050440411014003834300440411014003024200541415018000034300541411054003024200440411014002c23030484023014002c21010c8c021014002c23030c8c021034002c21010484021014002c120220a0012004002c11010484012004002c12020484012024002c110120a0011014002c82060484082044002c810520a0082044002c820620a0082064002c81050484081054002c26220484012104002c24200585016104002c26220585012144002c24200484012104002821010444021004002824040848021004002821010848021014002824040444024044002811010848011004002812020444011004002811010444011014002812020848012024002d000b0444011104002c121008c8812104002d000a08c8821224002c121004440111040028810504440810440028820620600810440028810520600810540028820604440820640029000a04440111040028242005450151040029000a054501114400282420044401110400090002400088101 (by decide +kernel)

def state183_18 : List Sig := [0x5555555555555555555555555555555555555555555500005555555555550000,input 7,input 4,input 5,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_18 : Impossible true (goalAt 183) 5 state183_18.toFinset :=
  node_ok cuts183 [] 0x9400210008410210005400110004410110021400810020410810004840161004850121008c00210008408210004c00110004408110020c0081002040881000840081002808021000440021000905011000440081002404011000444011140544011100444021220484011100901021000c4402100048081100044401100208088100240408100 (by decide +kernel)

def state183_19 : List Sig := [0x3333333333333333333333333333333333333333333300003333333333330000,input 7,input 4,input 5,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_19 : Impossible true (goalAt 183) 5 state183_19.toFinset :=
  node_ok cuts183 [] 0x9800260009810230105800120004810120021800820020810820004440151004450111008c00230008c04260404c00120004804120020c0082002080482002880082002808082000480032000905012000480082002404012000484012140584012100444021220444012100840421010c8402301044041200048401200204048200240408200 (by decide +kernel)

def state183_20 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0f0f0f0f0000,input 7,input 4,input 5,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_20 : Impossible true (goalAt 183) 5 state183_20.toFinset :=
  node_ok cuts183 [] 0x9800240009008240005800160005808150121800860021808850104440121008488111009400240009004240005400150005404160221400850021404860209000a4002808024000d00024000905024002500094002404015010484012140484016100444011140444015100840424000d04024000440411010d0801501204048101240408501 (by decide +kernel)

def state183_21 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffff0000ffffffffffff0000,input 7,input 4,input 5,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_21 : Impossible true (goalAt 183) 6 state183_21.toFinset :=
  node_ok cuts183 [⟨state183_18,exclude183_18⟩,⟨state183_19,exclude183_19⟩,⟨state183_20,exclude183_20⟩] 0x34100d04034142820024200d08024300908094102404090142404200020908024204000812100584012140484012100c840123004840322004840121020a00121024040a0220484200010484012104000011100544011140444011100484021220444011100c440212004440212004440111008480111024040818004442000004440111040004b01024040a0202404021010d050322209050241424040a02024040a020044048101 (by decide +kernel)

def state183_22 : List Sig := [0xffffffffffff0000ffffffffffff0000,input 7,input 4,input 5,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_22 : Impossible true (goalAt 183) 6 state183_22.toFinset :=
  node_ok cuts183 [⟨state183_10,exclude183_10⟩] 0x34100d04034142820024200d08024300908085012040481052040412100584012140484012100c840123004840322004840121020a0082002080082022040411100544011140444011100484021220444011100c440212004440212004440111008480810020400810120808a00028000a0802040434140c888241409050900024000908020404242080000242040008121020a00121020a001110206001110206002101084043414282001101044043222242009010 (by decide +kernel)

def state183_23 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 7,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 5,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_23 : Impossible true (goalAt 183) 6 state183_23.toFinset :=
  node_ok cuts183 [] 0xd04034100d0510017252002420090809080250409010240509010090803420090c02420048401610048501210048403210048c0121020a00121004840828004840901020a0012100c880121004841001604440151004450111004440121008488111004440311008480111020600111004440818004440901020600111008480111004440212008404a0102404090302404032220d05024140905090102420090104003c1101044043222400188101 (by decide +kernel)

def state183_24 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 7,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_24 : Impossible true (goalAt 183) 6 state183_24.toFinset :=
  node_ok cuts183 [⟨state183_11,exclude183_11⟩] 0x90803420090c0242029200242009080a08009080a0208000024200d04034100d05100100484016100485012100c880121004840828020a00121004840828004840a020280881210048403210048c0121004440151004450111004440121008488111008480111004440212020600111004440818004440a0202060011100444031100848011100440490202408090302808034140c888241409050a02028200a020208882101084043414400508101 (by decide +kernel)

def state183_25 : List Sig := [0xffffffffffffffffffffffffffffffff0f0f0f0f0f0f00000f0f0f0f0f0f0000,input 7,input 4,input 5,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_25 : Impossible true (goalAt 183) 5 state183_25.toFinset :=
  node_ok cuts183 [] 0x260009000240209000160005800160205404121024040a02204840121404840121005840111004840212204440250009000240109000150005400150105808111024040818004440111404440111005440240024040a020090002400084043410090003400090002414090001501280809010054041101044043420054048101 (by decide +kernel)

def state183_26 : List Sig := [0xf0f0f0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f0000,input 4,input 5,input 0,input 1,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_26 : Impossible true (goalAt 183) 6 state183_26.toFinset :=
  node_ok cuts183 [⟨state183_25,exclude183_25⟩,⟨state183_10,exclude183_10⟩] 0x20808121020800810120a0082002080882802080881010484081010980812100980024000c8c0240009808323009008240004840240005808828005800150104840160005808121005808150120a00150120404111020400820220600810020404818020404820204440820240068111004440121008c88121040020232208488121004440111009404111009400240008480240009404212009004240004440240005404212005400160204440150005404111005404160208480160228080240009000810129200a40028080a4802808081010900024002404015012500081012520094002404094802404081010540415010d05015010d00024000c88824000d05032220905024000540424002404024202404081018000481012404200002404081010908081010484024200484016140988812140484026220484016140908016100444024200444015144002011140444100080444015140908015104004100020840424000908024004004024200d04024004000824000c88824200440415010d0c011010c88834300d0801501090801501 (by decide +kernel)

def state183_27 : List Sig := [0xf0f0f0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f0000,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,input 5,input 0,input 1,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_27 : Impossible true (goalAt 183) 6 state183_27.toFinset :=
  node_ok cuts183 [] 0x208008200208088101048403210048c012100c880121004840828020a0012100484082802040081002040482020444012100848811100444031100848011100848011100444021202060011100444081802c04081012808081010900090102040490102040434140c88824140540490102040490102040490102040490102040412100485012100584011100445011100544100100d05034100d0402420090c03420090810002 (by decide +kernel)

def state183_28 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,input 5,input 0,input 1,input 2,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_28 : Impossible true (goalAt 183) 7 state183_28.toFinset :=
  node_ok cuts183 [⟨state183_21,exclude183_21⟩,⟨state183_22,exclude183_22⟩,⟨state183_23,exclude183_23⟩,⟨state183_24,exclude183_24⟩,⟨state183_26,exclude183_26⟩,⟨state183_27,exclude183_27⟩,⟨state183_12,exclude183_12⟩] 0x85050908085012040500102040485058001881052040424202040434144001834104004024200d04034140908034144004100104004100100908024200c88834300d08100100d0c024300c888242009081001080016000440008242009081001009080242040009001040008820204840820020404828020800820220a0082022040412102040426220484012100908016140584026220585012140908012100484100160484012100d05032300c84100160c8c012300d050121004840322220a00322040058121004840322204840121040058828020a01001620a00828040000121004841001604840121040000828020a00810104440810020808818020400810120600810120808111020809001004440111009080151405441001905450111409080111004441001604440111004840232204841001908c8821220484011100444100190444011100d05021200c44100190848021200d05011100444100190848021200c88811100444100190444011100c888212008481001920600818040004111004441001904440111040004818020600a0200d050b01020405000620404a0208000ca0202040434142040500184005021012404032222404081014005081012404200022404081010c88881010d05100060d05100140c888322240051001409051001540018110124041000f2404081018000481012404200002404081014003c8101 (by decide +kernel)

def state183_29 : List Sig := [0xbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbaaaabbbbaaaabbbbaaaabbbbaaaa,input 0,input 4,input 7,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_29 : Impossible true (goalAt 183) 5 state183_29.toFinset :=
  node_ok cuts183 [] 0xa2002080082202080024000900024040840486002080082042080016000480012040480012000c8003414048001200208009010048002101090102101090101110054401114044408101208008101208001101048001101048002120084042404084042404048401214058401210204048200204048200044041200044041200 (by decide +kernel)

def state183_30 : List Sig := [0xfafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafa,0x1111111111111111111111111111111111110000111100001111000011110000,input 4,input 7,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_30 : Impossible true (goalAt 183) 4 state183_30.toFinset :=
  node_ok cuts183 [] 0x2880082002088082000480032000d05012000480082002404012000484021010c840210104840820024040820020a00120004840120004840111404440111008400210008404a080204008100204048200044001100044041200 (by decide +kernel)

def state183_31 : List Sig := [0x1111111111111111111111111111111111110000111100001111000011110000,input 0,input 4,input 7,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_31 : Impossible true (goalAt 183) 5 state183_31.toFinset :=
  node_ok cuts183 [⟨state183_30,exclude183_30⟩] 0xa2002080082202080024000900024040840486002080082042080016000480012040480012000c8003414048001200208009010048002100084002101090102120090820000084808100204008101208001100044001101048001210084043210084041210048501610048401210208009010208008280048001210048001110 (by decide +kernel)

def state183_32 : List Sig := [0xfafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafa,input 0,0x3333333333333333333333333333333333330000333300003333000033330000,input 4,input 7,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_32 : Impossible true (goalAt 183) 5 state183_32.toFinset :=
  node_ok cuts183 [⟨state183_30,exclude183_30⟩] 0xa2002080082202080012000c800341404800120020800901004800121008404321008404810120800901020800110104800121004800121080000111404840121004850161004840210108410210109004830120800830120800130104800130104800111009000240008404a08021800820020c04820005800120004c041200 (by decide +kernel)

def state183_33 : List Sig := [0x3333333333333333333333333333333333330000333300003333000033330000,input 4,input 7,input 0,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_33 : Impossible true (goalAt 183) 6 state183_33.toFinset :=
  node_ok cuts183 [⟨state183_29,exclude183_29⟩,⟨state183_31,exclude183_31⟩,⟨state183_32,exclude183_32⟩,⟨state183_8,exclude183_8⟩,⟨state183_1,exclude183_1⟩] 0x28880210128800820028200820028880a0802088082000840482000901200040900021010908024000901024200901021014007c21012181024202180082004007c82002181200032081082000908082000581024200580012000d0c012000581034300481012000908012000840411100840024040848021000840421200840424040444024044007c111004440242005450151080008151404450242004440111020c04111020c00820020600820020c04818020804820004440820004c04212004c00120004440120004c0411100480412000848012000d05012000480021010c88032000d05032200d05021010480012002404012000480082002420082002404090802404082000480012000d05012100484021010c8c021010d05032300c84021010484021010d0c012100484024200585012140d0c0161405840242004840121004440121004440212080004212004442000004440212004840121024040121020404820020a00820024040828024040820004840820024200828004404120004840120024200121004840120020a001200 (by decide +kernel)

def state183_34 : List Sig := [0x3333333333333333333333333333333333330000333300003333000033330000,0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 4,input 7,input 0,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_34 : Impossible true (goalAt 183) 6 state183_34.toFinset :=
  node_ok cuts183 [] 0x84049010240c021010840434140d05021010900024000901021012504090102405090100908034300d0c024200908034300d0c0242008400210008404240404440151004450111004440901020600111008480111004440212008480111004440212020800341408404341408404901024200a03004800121008404321008404121004850161004840111008480111004840121020a00901004840828004840121020a010000 (by decide +kernel)

def state183_35 : List Sig := [0xf0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffff0f0f0f0f0f0fffff0f0,input 5,input 4,input 7,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_35 : Impossible true (goalAt 183) 5 state183_35.toFinset :=
  node_ok cuts183 [] 0x20810820420818810504810120404818110508c0421010840c21010988012100484024200444012100848811102041081042041482060441011040441412060840021000840424040848011100444021202401090042404011050c404210109040210128000a000280802101204048101204142420044041101044142420090002400090102101 (by decide +kernel)

def state183_36 : List Sig := [0xffffffff00000000ffffffff00000000ffff000000000000ffff0000,input 5,input 4,input 7,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_36 : Impossible true (goalAt 183) 6 state183_36.toFinset :=
  node_ok cuts183 [⟨state183_35,exclude183_35⟩] 0x94102404090142404024200d080243009080240009000240408404121005840121404840121024040a02204840322004840121020a00230108404210308404111005440111404440111004840212204440111024040818004440212004440111008480210008400210109010901028080901028080310108404322208404a00028000a0200840500020908200000908012100c8c012100c8c011100848011100848081012040490102808011010440490800c8883414 (by decide +kernel)

def state183_37 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 4,input 7,input 0,input 1,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_37 : Impossible true (goalAt 183) 7 state183_37.toFinset :=
  node_ok cuts183 [⟨state183_23,exclude183_23⟩,⟨state183_33,exclude183_33⟩,⟨state183_34,exclude183_34⟩,⟨state183_9,exclude183_9⟩,⟨state183_2,exclude183_2⟩,⟨state183_21,exclude183_21⟩,⟨state183_36,exclude183_36⟩] 0xb03008404210124040a08024040b0302820090302404021010840600060840421014001834140d05200050d050341440018210108404240480010240008404242009000240409080240408405001e08404941409080941024041001e2404094148000c90142404024202404094840908024202420034300d0c094840d0c0343024200242009081001e0908024204000834300d0c1001e0d0c034304000824200908023030484023010840432300840423030c8c0210308404121008404262204840121009080161405840262205850121409080121004841001d04840121024040828024041001d20a00828024040121004841001d20a00828024200121004841001d04840121024200828020a01001d8000a000140000121004841001d04840121040001001d40000210104440210009010212008400210108480210109010111009011001e04440111009080151405441001c05450111409080111004441001d04440111004840232204841001c08c88212204840111004441001c04440111024040818024041001c20600818024040111004441001c08480212024200111004441001c04440111024200212008481001c08480212040004111004441001c04440111040004212008481000d4005081010d05090800d05021014005021010d05200000d050210124200210124041000f240410014242009080400510014280c1001b4003c1101 (by decide +kernel)

def state183_38 : List Sig := [0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,0xfafafffffafafffffafafffffafafffffafafafafafafafafafafafafafafafa,input 4,input 7,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_38 : Impossible true (goalAt 183) 4 state183_38.toFinset :=
  node_ok cuts183 [] 0x84048101240c02101044042101090501101240009000240401101090002400084050023204048102204049010044041102044041201084042104084042401204048104204041210048001200044048180044401110044501210 (by decide +kernel)

def state183_39 : List Sig := [0xfafafffffafafffffafafffffafafffffafafafafafafafafafafafafafafafa,input 0,input 4,input 7,input 1,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_39 : Impossible true (goalAt 183) 5 state183_39.toFinset :=
  node_ok cuts183 [⟨state183_38,exclude183_38⟩] 0x21012040490300840423010840421030840483012040481032040412000480012020440412100584012140484011010840424140440490002400090100440421010841021010900411140484200000484081012041081012080c1101048081101048081110090002400084050006204048202204049010044041202044041202 (by decide +kernel)

def state183_40 : List Sig := [0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 0,0xf0f0fffff0f0fffff0f0fffff0f0fffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 4,input 7,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_40 : Impossible true (goalAt 183) 5 state183_40.toFinset :=
  node_ok cuts183 [⟨state183_38,exclude183_38⟩] 0x2101280109030084041101084042414044049000240009010044042400090002404084048101204048105240401501044041105044042101084082101090108105204188105208141101044081101048042122090820000090801110084042404084042404208108204204141210048001200044048280048401610048501210 (by decide +kernel)

def state183_41 : List Sig := [0xf0f0fffff0f0fffff0f0fffff0f0fffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 4,input 7,input 0,input 1,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_41 : Impossible true (goalAt 183) 6 state183_41.toFinset :=
  node_ok cuts183 [⟨state183_39,exclude183_39⟩,⟨state183_40,exclude183_40⟩] 0x2c0c0210108404810528200a0042c0c0a080240c0810508404210108c0c121008c0421010c8c0210108c0c32300840c210104840210120818121020810810520a00820420818828020818810504840810504808828004800110104840120004808121004808110120a00110109888121004840242005850161009888161404850242004840121008404111008400240408480210008404212008404240404440240440090111004440121008c8812108000423220848812100444011102041411102041082062060081042041481802041482060444082060440421200440012020444011000440411100440412020848012024003811100444024200545015108000015140445024200444011100d05011010440421010c88821010d05032220905021010440411012404011012400081052520090002404094802404081050440411010901100060900021010908024000901024200901021014001821012041424202040490104000881012041500022041490100908090100541424200540411010d0c01101054143430044141101090801101 (by decide +kernel)

def state183_42 : List Sig := [0xf0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f000000000f0f0f0f00000000,input 5,input 4,input 7,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_42 : Impossible true (goalAt 183) 5 state183_42.toFinset :=
  node_ok cuts183 [] 0x2180086002180885010480012000480811010980024000900824000444012100848811102140085002140486020440011000440412020940024000900424002400090002404011010d000240009040240009000a4002808024000908012100988012100848011100848011102040481012808085010908011010d0801101084042400090802400 (by decide +kernel)

def state183_43 : List Sig := [0xffffffff0000ffffffffffff0000ffffffffffff00000000ffffffff00000000,input 5,input 4,input 7,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_43 : Impossible true (goalAt 183) 6 state183_43.toFinset :=
  node_ok cuts183 [⟨state183_42,exclude183_42⟩] 0x941024040901424040150104404110504404a48009080242028202000009080242040008121005840121404840121024040a0220484012000480012020440412100c8c032300484012100c8c032300484011100544011140444011100484021220444011102404081800444011000440011010480811100848021200444011100848021200444090002400090100440411010c88832220440411010c888322204404a02024040a020240402101204048101280809010 (by decide +kernel)

def state183_44 : List Sig := [0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000,input 4,input 7,input 0,input 1,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_44 : Impossible true (goalAt 183) 7 state183_44.toFinset :=
  node_ok cuts183 [⟨state183_41,exclude183_41⟩,⟨state183_43,exclude183_43⟩,⟨state183_4,exclude183_4⟩] 0xb03008404210124040a08024040b03028200903024040210108404240480008240008404242009000240409080240408405001b08404941409080941024041001b2404094144003c90142404024202404015050908015010440434300440415050d0c011050440424200440423030484023010840432300840423030c8c0210308404121008404262204840121009080161405840262205850121409080121004841002204840121024040828024041002220a00828024040121004840120220a00120004404121004800120204840120204404828004404210104440210009010212008400210108480210109010111009011001b04440111009080151405441002105450111409080111004441002204440111004840232204841002108c8821220484011100444100210444011102404081802404100212060081802404011100444011010848011000480811100440011010444011010480821200480834140440411010840432220840434140c888241408404110104405001440050900024041000f2404100140440411012820100062820021014003c21012820200012820021014001821014006d00024000824204006c24204003d001b80000242040008242020a01000020a00121040088121020a01002220a00121040000121020601000120600111040084111020601002120600111040004111040051002020405000f400789080 (by decide +kernel)

def state183_45 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f00000000,input 5,input 7,input 0,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_45 : Impossible true (goalAt 183) 6 state183_45.toFinset :=
  node_ok cuts183 [] 0x2504011012500085012420094002504090802504085010440411010d04011010d00024000c88824000d040322209040240004404240004808828004800110104840120004808121004808110120a00110121808121021800850120a0086002180882802180885010484085010980812100980024000c8c0240009808323009008240004840240004404212004400120204440110004404111004404120208480120240024111004440121008c88121040020232208488121004440111021404111021400860220600850021404818021404860204440860209404111009400240008480240009404212009004240004440240028080240009000850128200a40028080a0802808085010900024000c88824200908011010d0c011010c88834300d08011010908011010c8c024200908012100988812100c8c026220988012100908012100848024200848011104002011100848100080848011100908011102808024202040485014001c8101280810012280808501090808501282010002084042400090802400282002420090802400400082400 (by decide +kernel)

def state183_46 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f00000000,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,input 7,input 0,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_46 : Impossible true (goalAt 183) 6 state183_46.toFinset :=
  node_ok cuts183 [] 0x4404a020280c011010440432220c88811010440432220c888110104800120004808110104840a0202808812100484032300c8c012100484032300c8c0121004400110004404120204440121008488111004440a02020600111004440212008480111004440212008480111021404a02028200822209000242004404342004404242004840262004840212004440212004440242040018a02009080a080090802420292010002 (by decide +kernel)

def state183_47 : List Sig := [0xffff0000ffff0000ffff0000ffff0000ffff000000000000ffff00000000,input 4,input 5,input 7,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_47 : Impossible true (goalAt 183) 6 state183_47.toFinset :=
  node_ok cuts183 [] 0x94102404090142404034100d040341428200150104404110504404121005840121404840121024040a0220484012100c84012300484012000480012020440411100544011140444011100484021220444011102404081800444011100c440212004440110004400110104808b01024040a0202404090002400090100440411010c40434140440424200d0c024200d0c0828004840828004840212004440212004440810120404a02024040210108404a0800d0503222 (by decide +kernel)

def state183_48 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,input 7,input 0,input 1,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_48 : Impossible true (goalAt 183) 7 state183_48.toFinset :=
  node_ok cuts183 [⟨state183_45,exclude183_45⟩,⟨state183_46,exclude183_46⟩,⟨state183_14,exclude183_14⟩,⟨state183_15,exclude183_15⟩,⟨state183_21,exclude183_21⟩,⟨state183_47,exclude183_47⟩,⟨state183_24,exclude183_24⟩] 0xb03004404110128080908028080b03024200a0302808011010440500060440411012820032220c88a00060c88832222820011010440600050440411014005032220c88a00040c88832224005011010440415050908015010440434300440415050d0c011050440424200440500120908024202808100122808100128000e000228080242009080a48440018a48028200242009080a48409080242028201001228201001280006000040008242009081001209080242040009001240008120220a00120004404121004800120204840120204404828004404262204840121009080161405840262205850121409080121004840a22204840121028080828028080a22220a00a0222808012100484100260484012102820032300c8c100260c8c032302820012100484100260484012104000032300c8c100260c8c0323040000121004840110108480110004808111004400110104440110104808212004809001204440111009080151405441002505450111409080111004441002604440111004840232204841002508c88212204840111004441002504440111028080818028081002520600818028080111004441002504440111028200212008481002508480212028200111004441002504440111040004212008481002508480212040004111004441000740018810128081000f28081000628200a0804001900062088900114003c2101 (by decide +kernel)

def state183_49 : List Sig := [0xf0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 5,input 7,input 0,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_49 : Impossible true (goalAt 183) 6 state183_49.toFinset :=
  node_ok cuts183 [] 0x2405011010440481052420090042405090802405081050440411010d05011010440421010c88821010d050322209050210104404110104808828004800110104840120004808121004808110120a00110120818121020810810520a00820420818828020818810504840810508c0c121008c0421010c8c0210108c0c32300840c210104840210109888121004840242005850161009888161404850242004840121004404212004400120204440110004404111004404120208480120240024111004440121008c88121040020232208488121004440111020414111020410820620600810420414818020414820604440820608404111008400240408480210008404212008404240404440240440020111004440242005450151040020151404450242004440111028080210128000810529200a00028080a4802808081050840421010541424200540411010d0c0110105414343004414110109080110120414242020404a02040008810120415000220414a020090802420090110002090002101090802400090102420090102101400082101 (by decide +kernel)

def state183_50 : List Sig := [0x3333000033333333333300003333333333330000333300003333000033330000,input 4,input 5,input 7,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_50 : Impossible true (goalAt 183) 5 state183_50.toFinset :=
  node_ok cuts183 [] 0x21800820020810820009000240009010210105800120004810120004440151004450111020c00820020804820008400210008404240404c0012000480412002800082002088082000480082002404012000480032000d05012000484012140584012100444021200444012102040482002404082000484021010c8402101044041200048401200 (by decide +kernel)

def state183_51 : List Sig := [0xffff0000ffffffffffff0000ffffffffffff0000ffff0000ffff0000ffff0000,input 4,input 5,input 7,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_51 : Impossible true (goalAt 183) 6 state183_51.toFinset :=
  node_ok cuts183 [⟨state183_50,exclude183_50⟩] 0x94102404090142404024000900024040840424200d0c034300908024200d0c0343009080121005840121404840121024040a02204840230108404210308404828004840121020a02000004840121040000111005440111404440111004840212204440111024040818004440210008400210109010212004440111008480212004440111008480a00028000a02008404901028080901028080341408404341408404110120404810124040a0200d05021010d0502101 (by decide +kernel)

def state183_52 : List Sig := [0xffffffff00000000ffffffff00000000000000000000000000000000,input 5,input 7,input 0,input 1,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_52 : Impossible true (goalAt 183) 7 state183_52.toFinset :=
  node_ok cuts183 [⟨state183_49,exclude183_49⟩,⟨state183_51,exclude183_51⟩,⟨state183_16,exclude183_16⟩] 0xb03004404110128080908028080b03024200a0302808011010440434140440411010840432220840434140c88824140840411010440415050908015010440434300440415050d0c011050440424200440500110908024202808100112808100114003e000228080242009080240440018240008404242009000240409080240408405001108404120220a00120004404121004800120204840120204404828004404262204840121009080161405840262205850121409080121004840a22204840121028080828028080a22220a00a0222808012100484023030484023010840432300840423030c8c0210308404121008404110108480110004808111004400110104440110104808212004809001104440111009080151405441002705450111409080111004441002804440111004840232204841002708c88212204840111004441002704440111028080818028081002720600818028080111004440210104440210009010212008400210108480210109010111009011000640018a00028081000f2808100060840421012420100142420011014003c11012420200012420011014005011014004500024000824204004424204003d001180000242040008242020a01000020a001210400a0121020a01002820a0012104000012102060100012060011104009c111020601002720600111040004111040019001320405000f40048a080 (by decide +kernel)

def state183_53 : List Sig := roots 183
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_53 : Impossible true (goalAt 183) 8 state183_53.toFinset :=
  node_ok cuts183 [⟨state183_5,exclude183_5⟩,⟨state183_17,exclude183_17⟩,⟨state183_28,exclude183_28⟩,⟨state183_37,exclude183_37⟩,⟨state183_44,exclude183_44⟩,⟨state183_48,exclude183_48⟩,⟨state183_52,exclude183_52⟩] 0x80018a02008404a00040018810128200a00080014a02028200a0204001881010840421018001090100440490004005081012420090008000c90102420090104005081010440411014001834140440411014005021010c88821018000834140c88824144005021010440411014000885050908085014000881014000881014000885058000481054000881010908081014000824048000024004000821010908024004000824040908024044000821014000821014000815050908015014000811010d0c011014000815050d0c0110540008110109080110140000820204840820040000810120a00820040000820220a0082024000081010484081014000023030484023014000021010c8c021014000023030c8c0210340000210104840210140000120220a00120040000110104840120040000120204840120240000110120a00110140008262204840121040008242005850161040008262205850121440008242004840121040004810104440810040004820220600810040004810120600810140004820204440820240004210104440210040004240408480210040004210108480210140004240404440240440004110108480110040004120204440110040004110104440110140004120208480120240009000204440111040008242005450151040009000105450111440008242004440111040001000004440111040000121008c88121040001000108c882122400001210044401110 (by decide +kernel)

theorem lower183 : Claim 183 9 :=
  fromSearch 1348 (by decide +kernel) exclude183_53

open PEqualNP.CircuitLowerBounds

def graph : Sig := goalAt 255
theorem graph_proper : proper graph := by unfold proper; decide +kernel

def edgeList : List Nat := [0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7]
def target (x : Fin 8 → Bool) : Bool :=
  decide (∃ i < edgeList.length / 2,
    (List.ofFn x).getD (edgeList.getD (2*i) 0) false = true ∧
    (List.ofFn x).getD (edgeList.getD (2*i+1) 0) false = true)

-- The three products cover the posted edges.
def smallCircuit : Circuit := ⟨[⟨.or,[0,1]⟩, ⟨.or,[0,2]⟩, ⟨.or,[1,3]⟩, ⟨.or,[4,5]⟩, ⟨.or,[4,7]⟩, ⟨.or,[6,7]⟩, ⟨.or,[10,11]⟩, ⟨.and,[8,12]⟩, ⟨.and,[9,5]⟩, ⟨.and,[14,13]⟩, ⟨.or,[15,16]⟩, ⟨.or,[18,17]⟩],19⟩

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

def lowRow (i : Fin 8) : Row := Fin.ofNat 256 (1 <<< ([4, 4, 5, 6, 0, 0, 1, 0] : List Nat).getD i.val 0)
def highRow (i : Fin 8) : Row := Fin.ofNat 256 ((1 <<< i.val) ||| (1 <<< ([4, 4, 5, 6, 0, 0, 1, 0] : List Nat).getD i.val 0))

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



-- Pin the two omitted vertices to zero. Both are essential before restriction.
theorem lowerGraph : Impossible true graph 10 eightInputs.toFinset :=
  (ruleFor 255 lower183 none (by decide +kernel)).property 10 eightInputs
    (by decide +kernel) (by decide +kernel)


end PEqualNP.Outside.L_meta_28970

open PEqualNP.Outside.L_meta_28970 in
theorem PEqualNP.Outside.L_meta_28970 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o fit _ correct
  exact replaceShort lowerGraph gates o fit correct

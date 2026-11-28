import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_32343

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
  (x 0 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 2 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)

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

def cs161 : Cuts (goalAt 161) := []

def dict161 : Nat := 0xa000204002100282008101280802120206002101

def d161 := unpackCases dict161 4

def u161 := unpackShort dict161 4

def s0 := certify 161 3 (roots 161) cs161 [] (d161 36 0x308458353400427317414322016526020511)

theorem lower161 : Claim 161 4 := fromSearch 5 (by decide +kernel) s0.property

theorem lower225 : Claim 225 5 := fromLift 5 64 117440517 lower161 (by decide +kernel)

def cs208 : Cuts (goalAt 208) := []

def dict208 : Nat := 0xc000240005000302009010301005040242005010

def d208 := unpackCases dict208 4

def u208 := unpackShort dict208 4

def s1 := certify 208 3 (roots 208) cs208 [] (d208 36 0x308458353400427317414322016526020511)

theorem lower208 : Claim 208 4 := fromSearch 1141243904 (by decide +kernel) s1.property

theorem lower209 : Claim 209 5 := fromLift 5 1 67108868 lower208 (by decide +kernel)

theorem lower177 : Claim 177 5 := fromLift 5 16 4 lower161 (by decide +kernel)

theorem lower240 : Claim 240 5 := fromLift 5 32 1148583936 lower208 (by decide +kernel)

def c241_0 := ruleFor 241 lower225 none (by decide +kernel)

def c241_1 := ruleFor 241 lower209 none (by decide +kernel)

def c241_2 := ruleFor 241 lower177 none (by decide +kernel)

def c241_3 := ruleFor 241 lower240 none (by decide +kernel)

def cs241 : Cuts (goalAt 241) := [c241_0,c241_1,c241_2,c241_3]

def dict241 : Nat := 0x6101140c0506008580c0002800070301850490002420050001c180810020600616008400110030100a02030200a0801410090104000c2120400008101140401110084050001044050002

def d241 := unpackCases dict241 6

def u241 := unpackShort dict241 6

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s2 := certify 241 6 (roots 241) cs241 [] (u241 3 160 0x7e9c861b7207cd9f0cac43acdd30cb743a64ea633035660a67041ab37e14cdc5498f62f63c55795ec220a25a06cbad0a2f406c891089195b272b7a8c444f214932a9d493c4f84cac400440525a02695d854423423432451a311643311c4450f17843c505c5c891)

theorem lower241 : Claim 241 7 := fromSearch 67108868 (by decide +kernel) s2.property

def cs194 : Cuts (goalAt 194) := []

def dict194 : Nat := 0xc00020800420030200820230100424020a004202

def d194 := unpackCases dict194 4

def u194 := unpackShort dict194 4

def s3 := certify 194 3 (roots 194) cs194 [] (d194 36 0x308458353400427317414322016526020511)

theorem lower194 : Claim 194 4 := fromSearch 285212768 (by decide +kernel) s3.property

theorem lower195 : Claim 195 5 := fromLift 5 1 16777319 lower194 (by decide +kernel)

def cs162 : Cuts (goalAt 162) := []

def dict162 : Nat := 0xa00020800220028200820228080222020a002202

def d162 := unpackCases dict162 4

def u162 := unpackShort dict162 4

def s4 := certify 162 3 (roots 162) cs162 [] (d162 36 0x308458353400427317414322016526020511)

theorem lower162 : Claim 162 4 := fromSearch 269484112 (by decide +kernel) s4.property

theorem lower163 : Claim 163 5 := fromLift 5 1 85 lower162 (by decide +kernel)

theorem lower226 : Claim 226 5 := fromLift 5 32 286261328 lower194 (by decide +kernel)

def c227_0 := ruleFor 227 lower225 none (by decide +kernel)

def c227_1 := ruleFor 227 lower195 none (by decide +kernel)

def c227_2 := ruleFor 227 lower163 none (by decide +kernel)

def c227_3 := ruleFor 227 lower226 none (by decide +kernel)

def cs227 : Cuts (goalAt 227) := [c227_0,c227_1,c227_2,c227_3]

def dict227 : Nat := 0x18404214110c08420310904c00028000a08018504820020a00420008800810010c0c616008400434130100a0203020042404000c8180208082202400002220084808101108082101400050002

def d227 := unpackCases dict227 6

def u227 := unpackShort dict227 6

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s5 := certify 227 6 (roots 227) cs227 [] (u227 3 160 0x1f672106dc81f367c21a08ea37286adc8eb53a508800880cce18133820c89c4f18f42f63c4d793e8c806c5a06ccad0632c06f30889956498ac88e11243285e29497265549782b05c9d1304f4fc192b0274af41a9890aa322348c9290889523c86abb3b390f3becaa)

theorem lower227 : Claim 227 7 := fromSearch 16777301 (by decide +kernel) s5.property

def cs145 : Cuts (goalAt 145) := []

def dict145 : Nat := 0x9000204001100242008101240401110206001101

def d145 := unpackCases dict145 4

def u145 := unpackShort dict145 4

def s6 := certify 145 3 (roots 145) cs145 [] (d145 36 0x308458353400427317414322016526020511)

theorem lower145 : Claim 145 4 := fromSearch 4 (by decide +kernel) s6.property

theorem lower147 : Claim 147 5 := fromLift 5 2 116 lower145 (by decide +kernel)

theorem lower210 : Claim 210 5 := fromLift 5 2 285605984 lower208 (by decide +kernel)

def c211_0 := ruleFor 211 lower209 none (by decide +kernel)

def c211_1 := ruleFor 211 lower195 none (by decide +kernel)

def c211_2 := ruleFor 211 lower147 none (by decide +kernel)

def c211_3 := ruleFor 211 lower210 none (by decide +kernel)

def cs211 : Cuts (goalAt 211) := [c211_0,c211_1,c211_2,c211_3]

def dict211 : Nat := 0x13010440c43021080c131004448c00030200900024200500020800420004c0c810010c0c110010d04131230100901020a010003206005040140408202400004240044408101108081101400050002

def d211 := unpackCases dict211 6

def u211 := unpackShort dict211 6

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s7 := certify 211 6 (roots 211) cs211 [] (u211 3 160 0x7d9c84377207db9f086823a8d4a19b523acce94220134620c5588132a4c191388e2fe836bf889b23d1900c6d6813c5a0d8c04cd9325791490909594324c43314a4c912ea4cc178324688827a820c0c09c1f835312174a4569292521152e5791d576217bc8d0bbecaa)

theorem lower211 : Claim 211 7 := fromSearch 16777316 (by decide +kernel) s7.property

theorem lower178 : Claim 178 5 := fromLift 5 16 269942864 lower162 (by decide +kernel)

def c179_0 := ruleFor 179 lower177 none (by decide +kernel)

def c179_1 := ruleFor 179 lower178 none (by decide +kernel)

def c179_2 := ruleFor 179 lower163 none (by decide +kernel)

def c179_3 := ruleFor 179 lower147 none (by decide +kernel)

def cs179 : Cuts (goalAt 179) := [c179_0,c179_1,c179_2,c179_3]

def dict179 : Nat := 0x884813010440c131004448a0002820090000c84882000880013030c8c0810020600210004400131228080901020a009080084810001208082202088810000204041110084050002044050003

def d179 := unpackCases dict179 6

def u179 := unpackShort dict179 6

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s8 := certify 179 6 (roots 179) cs179 [] (u179 3 160 0x7d9c85377207db9f0a6643a4d528cb543a64ea51103322060606610c188b09f31ca36c7099b2795d4044daf06e5e04788831b645bd05095922d56fd0b88ad4292a4d3a92b49e8a938260d09408974a0c5d808c11422e8d0cc2342824325cbe64467217b8550bbce88)

theorem lower179 : Claim 179 7 := fromSearch 84 (by decide +kernel) s8.property

def cs113 : Cuts (goalAt 113) := []

def dict113 : Nat := 0x184045030141802160084805000140402100044001110084041101

def d113 := unpackCases dict113 4

def u113 := unpackShort dict113 4

def s9 := certify 113 3 (roots 113) cs113 [] (d113 24 0x1ba166500190258244123307)

theorem lower113 : Claim 113 4 := fromSearch 67108868 (by decide +kernel) s9.property

def cs83 : Cuts (goalAt 83) := []

def dict83 : Nat := 0x4c04110310c084203141001310044485000108005010044001110108081101

def d83 := unpackCases dict83 4

def u83 := unpackShort dict83 4

def s10 := certify 83 3 (roots 83) cs83 [] (d83 24 0x66405514d0c0b1a133092872)

theorem lower83 : Claim 83 4 := fromSearch 16777316 (by decide +kernel) s10.property

def cs114 : Cuts (goalAt 114) := []

def dict114 : Nat := 0x50300c8082212109003220088c05000108005010088002220108082202

def d114 := unpackCases dict114 4

def u114 := unpackShort dict114 4

def s11 := certify 114 3 (roots 114) cs114 [] (d114 24 0x1c06641b0a0551433092872)

theorem lower114 : Claim 114 4 := fromSearch 18219088 (by decide +kernel) s11.property

def cs99 : Cuts (goalAt 99) := []

def dict99 : Nat := 0x61010850443021080c4241108002200084002202088802120108082101

def d99 := unpackCases dict99 4

def u99 := unpackShort dict99 4

def s12 := certify 99 3 (roots 99) cs99 [] (d99 24 0xcb077136640a19155042382)

theorem lower99 : Claim 99 4 := fromSearch 16777301 (by decide +kernel) s12.property

def cs51 : Cuts (goalAt 51) := []

def dict51 : Nat := 0x221204c041103084801310044482200084002202044001110084041101

def d51 := unpackCases dict51 4

def u51 := unpackShort dict51 4

def s13 := certify 51 3 (roots 51) cs51 [] (d51 24 0x1c06641b0a0551433092872)

theorem lower51 : Claim 51 4 := fromSearch 84 (by decide +kernel) s13.property

def c115_0 := ruleFor 115 lower113 none (by decide +kernel)

def c115_1 := ruleFor 115 lower83 none (by decide +kernel)

def c115_2 := ruleFor 115 lower114 none (by decide +kernel)

def c115_3 := ruleFor 115 lower99 none (by decide +kernel)

def c115_4 := ruleFor 115 lower51 none (by decide +kernel)

def cs115 : Cuts (goalAt 115) := [c115_0,c115_1,c115_2,c115_3,c115_4]

def dict115 : Nat := 0x8002600088001e00068001600048000e00028000470201c1005060184802160108402210088045210088c070100840823020c8085001085044340109045020140083120084c062200c840322008c0031101084850121440043001080452021c000520004c0011020840c220318800320018400310014404130208c04614118580706010c0443414000900001c0c200004000c131004c0443021840500014001032300c84850300444811031080c221204c48130310c0c4240141005000108002200084001100084802220140402202044404202084041101

def d115 := unpackCases dict115 7

def u115 := unpackShort dict115 7

def w8 : Sig := 0xeeeeeeee00000000eeeeeeee00000000eeeeeeee00000000eeeeeeee

def s14 := certify 115 4 ([w8,i0,i1,i4,i6]) cs115 [] (u115 4 40 0x3185028be4a5174a6925b279496412950ae4251b8804a010a8a7444852)

def w9 : Sig := 0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee

def s15 := certify 115 5 ([w9,i0,i1,i4,i5,i6]) cs115 [s14] (u115 3 53 0x2372d21919a0022504b4b4a532823b0290c394274282805501b49232b64a4a24123501b01b)

def w10 : Sig := 0xffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaa

def s16 := certify 115 5 ([w10,i0,i4,i1,i5,i6]) cs115 [] (u115 3 53 0x2372d217174a1515823b0290c3131c057a0022f01b1f41f4282863d2b60683e1f41f42828)

def w11 : Sig := 0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa

def s17 := certify 115 5 ([w11,i0,i5,i1,i4,i6]) cs115 [] (u115 4 53 0x630a00049a0d001ab588a3b014814c4c62e319c11ba1891e2788085039cc49709cc26f13c4)

def w12 : Sig := 0xffff0000ffff0000aaaa0000aaaa0000ffff0000ffff0000aaaa0000aaaa

def s18 := certify 115 4 ([w12,i0,i6,i1,i5]) cs115 [] (u115 4 40 0xd7889c5288134e21f10591420cecb08609e0040800293b0030af874010)

def w13 : Sig := 0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa

def s19 := certify 115 5 ([w13,i0,i6,i1,i4,i5]) cs115 [s18] (u115 3 53 0x2378f28228022500571b041003f1515823b02904b4b1fcc1d1dc4282801b01b8dc8bc1f4f276)

def w14 : Sig := 0xffffccccffffcccc0000000000000000ffffccccffffcccc

def s20 := certify 115 4 ([w14,i1,i4,i0,i5]) cs115 [] (u115 4 40 0x129090e7891c38d9bed86b25c597d16b60a6c81204427392030db855896)

def w15 : Sig := 0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc

def s21 := certify 115 5 ([w15,i1,i4,i0,i5,i6]) cs115 [s20] (u115 3 53 0x2372d2394274131328555521e63d2b6e66e6d4a493225204a4a8282213129c4414338282)

def w16 : Sig := 0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc

def s22 := certify 115 5 ([w16,i1,i5,i0,i4,i6]) cs115 [] (u115 3 53 0x1919a00825002121039427411110e9586186232366232368443824a4a2102108c631d4a4a)

def w17 : Sig := 0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc

def s23 := certify 115 5 ([w17,i1,i6,i0,i4,i5]) cs115 [] (u115 3 53 0x245122882022500477002121013132811110e394274623236623236a828221021041d75c)

def w18 : Sig := 0x5555555555550000555555555555000055555555555500005555555555550000

def s24 := certify 115 4 ([w18,i4,i5,i1,i6]) cs115 [] (u115 4 40 0x16b114f7297933c196125b2d941cd508489606228862b3d3224f32740d0)

def w19 : Sig := 0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000

def s25 := certify 115 5 ([w19,i4,i5,i0,i1,i6]) cs115 [s24] (u115 3 53 0x17174a7f7f2f1dc7d9bc1dcc1d39427463d2b6679e6e66e4166479942d42a4a42f4d250a4a4)

def w20 : Sig := 0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000

def s26 := certify 115 5 ([w20,i4,i6,i0,i1,i5]) cs115 [] (u115 3 53 0x2a2d222f2f21515829da75ac3131cc3131c13132863d2b66a4f6e66ee66e42f22f2a1b770)

def w21 : Sig := 0x3333333333333333333333330000000033333333333333333333333300000000

def s27 := certify 115 4 ([w21,i5,i6,i0,i4]) cs115 [] (u115 4 40 0xd36a3b2ed28690801ce366fb3dd27e94b16d1807d038ce32ad03615194)

def w22 : Sig := 0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000

def s28 := certify 115 5 ([w22,i5,i6,i0,i1,i4]) cs115 [s27] (u115 3 53 0xad4300aba9001b1b03b0290c811dc1dcc1d41cc4511110e63d2b66a7a566ee66ee6443512d2)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s29 := certify 115 6 (roots 115) cs115 [s15,s16,s17,s19,s21,s22,s23,s25,s26,s28] (u115 3 160 0x3343223545137bf43512d3342233a0193f41b19bda1ba33400352f003f24d2bb2f4d2535200334c1745a1d17b941d433aca3581d15452c15b78c83521d23f21c3b450310b52131293f0c0331f6394744f4b31f4f2733464352613478e13b12e2358683f0e11471b611af0603f1bee45496647c233d4149232b45c66)

theorem lower115 : Claim 115 7 := fromSearch 16777300 (by decide +kernel) s29.property

def c242_0 := ruleFor 242 lower226 none (by decide +kernel)

def c242_1 := ruleFor 242 lower240 none (by decide +kernel)

def c242_2 := ruleFor 242 lower210 none (by decide +kernel)

def c242_3 := ruleFor 242 lower178 none (by decide +kernel)

def cs242 : Cuts (goalAt 242) := [c242_0,c242_1,c242_2,c242_3]

def dict242 : Nat := 0x140c03202088483220088c0c00030200a0001c0c090001400032121c180820020a00420008800323030100a02024200a080109010001240405010141010000208082220108090002088090003

def d242 := unpackCases dict242 6

def u242 := unpackShort dict242 6

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s30 := certify 242 6 (roots 242) cs242 [] (u242 3 160 0x7d9c85377207db9f0a6643a4d528cb543a64ea51103322060606610c188b09f31ca36c7099b2795d4044daf06e5e04788831b645bd05095922d56fd0b88ad4292a4d3a92b49e8a938260d09408974a0c5d808c11422e8d0cc2342824325cbe64467217b8550bbce88)

theorem lower242 : Claim 242 7 := fromSearch 286654544 (by decide +kernel) s30.property

def c243_0 := ruleFor 243 lower241 none (by decide +kernel)

def c243_1 := ruleFor 243 lower227 none (by decide +kernel)

def c243_2 := ruleFor 243 lower227 (some (1,i0,i1)) (by decide +kernel)

def c243_3 := ruleFor 243 lower211 none (by decide +kernel)

def c243_4 := ruleFor 243 lower194 none (by decide +kernel)

def c243_5 := ruleFor 243 lower179 none (by decide +kernel)

def c243_6 := ruleFor 243 lower161 none (by decide +kernel)

def c243_7 := ruleFor 243 lower115 none (by decide +kernel)

def c243_8 := ruleFor 243 lower240 none (by decide +kernel)

def c243_9 := ruleFor 243 lower225 none (by decide +kernel)

def c243_10 := ruleFor 243 lower227 (some (3,i0,i1)) (by decide +kernel)

def c243_11 := ruleFor 243 lower242 (some (1,i1,i4)) (by decide +kernel)

def c243_12 := ruleFor 243 lower226 none (by decide +kernel)

def c243_13 := ruleFor 243 lower227 (some (2,i0,i1)) (by decide +kernel)

def c243_14 := ruleFor 243 lower241 (some (1,i0,i4)) (by decide +kernel)

def c243_15 := ruleFor 243 lower211 (some (1,i0,i1)) (by decide +kernel)

def c243_16 := ruleFor 243 lower208 none (by decide +kernel)

def c243_17 := ruleFor 243 lower179 (some (1,i0,i1)) (by decide +kernel)

def c243_18 := ruleFor 243 lower177 none (by decide +kernel)

def c243_19 := ruleFor 243 lower179 (some (3,i0,i1)) (by decide +kernel)

def c243_20 := ruleFor 243 lower242 (some (1,i1,i6)) (by decide +kernel)

def c243_21 := ruleFor 243 lower178 none (by decide +kernel)

def c243_22 := ruleFor 243 lower179 (some (2,i0,i1)) (by decide +kernel)

def c243_23 := ruleFor 243 lower241 (some (1,i0,i6)) (by decide +kernel)

def c243_24 := ruleFor 243 lower145 none (by decide +kernel)

def c243_25 := ruleFor 243 lower115 (some (1,i0,i1)) (by decide +kernel)

def c243_26 := ruleFor 243 lower113 none (by decide +kernel)

def c243_27 := ruleFor 243 lower115 (some (3,i0,i1)) (by decide +kernel)

def c243_28 := ruleFor 243 lower242 (some (1,i1,i7)) (by decide +kernel)

def c243_29 := ruleFor 243 lower211 (some (1,i0,i6)) (by decide +kernel)

def c243_30 := ruleFor 243 lower114 none (by decide +kernel)

def c243_31 := ruleFor 243 lower115 (some (2,i0,i1)) (by decide +kernel)

def c243_32 := ruleFor 243 lower211 (some (1,i1,i4)) (by decide +kernel)

def c243_33 := ruleFor 243 lower241 (some (1,i0,i7)) (by decide +kernel)

def c243_34 := ruleFor 243 lower242 none (by decide +kernel)

def c243_35 := ruleFor 243 lower99 none (by decide +kernel)

def c243_36 := ruleFor 243 lower51 none (by decide +kernel)

def c243_37 := ruleFor 243 lower211 (some (1,i0,i4)) (by decide +kernel)

def c243_38 := ruleFor 243 lower179 (some (1,i0,i4)) (by decide +kernel)

def c243_39 := ruleFor 243 lower162 none (by decide +kernel)

def c243_40 := ruleFor 243 lower115 (some (1,i0,i4)) (by decide +kernel)

def c243_41 := ruleFor 243 lower115 (some (3,i0,i4)) (by decide +kernel)

def c243_42 := ruleFor 243 lower242 (some (1,i4,i7)) (by decide +kernel)

def c243_43 := ruleFor 243 lower115 (some (2,i0,i4)) (by decide +kernel)

def c243_44 := ruleFor 243 lower227 (some (1,i0,i7)) (by decide +kernel)

def c243_45 := ruleFor 243 lower179 (some (1,i0,i5)) (by decide +kernel)

def c243_46 := ruleFor 243 lower210 none (by decide +kernel)

def c243_47 := ruleFor 243 lower147 none (by decide +kernel)

def c243_48 := ruleFor 243 lower179 (some (3,i0,i5)) (by decide +kernel)

def c243_49 := ruleFor 243 lower242 (some (1,i5,i6)) (by decide +kernel)

def c243_50 := ruleFor 243 lower179 (some (2,i0,i5)) (by decide +kernel)

def c243_51 := ruleFor 243 lower115 (some (1,i0,i5)) (by decide +kernel)

def c243_52 := ruleFor 243 lower83 none (by decide +kernel)

def c243_53 := ruleFor 243 lower115 (some (3,i0,i5)) (by decide +kernel)

def c243_54 := ruleFor 243 lower242 (some (1,i5,i7)) (by decide +kernel)

def c243_55 := ruleFor 243 lower115 (some (2,i0,i5)) (by decide +kernel)

def c243_56 := ruleFor 243 lower211 (some (1,i0,i7)) (by decide +kernel)

def c243_57 := ruleFor 243 lower241 (some (1,i0,i5)) (by decide +kernel)

def c243_58 := ruleFor 243 lower227 (some (1,i0,i5)) (by decide +kernel)

def c243_59 := ruleFor 243 lower115 (some (1,i0,i6)) (by decide +kernel)

def c243_60 := ruleFor 243 lower115 (some (3,i0,i6)) (by decide +kernel)

def c243_61 := ruleFor 243 lower242 (some (1,i6,i7)) (by decide +kernel)

def c243_62 := ruleFor 243 lower115 (some (2,i0,i6)) (by decide +kernel)

def c243_63 := ruleFor 243 lower179 (some (1,i0,i7)) (by decide +kernel)

def c243_64 := ruleFor 243 lower227 (some (1,i5,i6)) (by decide +kernel)

def c243_65 := ruleFor 243 lower227 (some (1,i0,i6)) (by decide +kernel)

def c243_66 := ruleFor 243 lower242 (some (2,i1,i7)) (by decide +kernel)

def c243_67 := ruleFor 243 lower115 (some (0,i0,i1)) (by decide +kernel)

def c243_68 := ruleFor 243 lower242 (some (3,i1,i7)) (by decide +kernel)

def c243_69 := ruleFor 243 lower242 (some (2,i4,i7)) (by decide +kernel)

def c243_70 := ruleFor 243 lower115 (some (0,i0,i4)) (by decide +kernel)

def c243_71 := ruleFor 243 lower178 (some (3,i4,i7)) (by decide +kernel)

def c243_72 := ruleFor 243 lower242 (some (3,i4,i7)) (by decide +kernel)

def c243_73 := ruleFor 243 lower242 (some (2,i5,i7)) (by decide +kernel)

def c243_74 := ruleFor 243 lower115 (some (0,i0,i5)) (by decide +kernel)

def c243_75 := ruleFor 243 lower242 (some (3,i5,i7)) (by decide +kernel)

def c243_76 := ruleFor 243 lower240 (some (3,i5,i7)) (by decide +kernel)

def c243_77 := ruleFor 243 lower242 (some (2,i6,i7)) (by decide +kernel)

def c243_78 := ruleFor 243 lower115 (some (0,i0,i6)) (by decide +kernel)

def c243_79 := ruleFor 243 lower242 (some (3,i6,i7)) (by decide +kernel)

def c243_80 := ruleFor 243 lower195 none (by decide +kernel)

def c243_81 := ruleFor 243 lower211 (some (3,i1,i4)) (by decide +kernel)

def c243_82 := ruleFor 243 lower241 (some (1,i4,i5)) (by decide +kernel)

def c243_83 := ruleFor 243 lower209 none (by decide +kernel)

def c243_84 := ruleFor 243 lower211 (some (2,i1,i4)) (by decide +kernel)

def c243_85 := ruleFor 243 lower227 (some (1,i1,i5)) (by decide +kernel)

def c243_86 := ruleFor 243 lower179 (some (1,i1,i4)) (by decide +kernel)

def c243_87 := ruleFor 243 lower115 (some (1,i1,i4)) (by decide +kernel)

def c243_88 := ruleFor 243 lower115 (some (3,i1,i4)) (by decide +kernel)

def c243_89 := ruleFor 243 lower241 (some (1,i4,i7)) (by decide +kernel)

def c243_90 := ruleFor 243 lower115 (some (2,i1,i4)) (by decide +kernel)

def c243_91 := ruleFor 243 lower179 (some (1,i4,i5)) (by decide +kernel)

def c243_92 := ruleFor 243 lower227 (some (1,i1,i7)) (by decide +kernel)

def c243_93 := ruleFor 243 lower179 (some (1,i1,i5)) (by decide +kernel)

def c243_94 := ruleFor 243 lower115 (some (1,i1,i5)) (by decide +kernel)

def c243_95 := ruleFor 243 lower115 (some (3,i1,i5)) (by decide +kernel)

def c243_96 := ruleFor 243 lower115 (some (2,i1,i5)) (by decide +kernel)

def c243_97 := ruleFor 243 lower211 (some (1,i1,i7)) (by decide +kernel)

def c243_98 := ruleFor 243 lower241 (some (1,i5,i7)) (by decide +kernel)

def c243_99 := ruleFor 243 lower242 (some (1,i1,i5)) (by decide +kernel)

def c243_100 := ruleFor 243 lower115 (some (1,i1,i6)) (by decide +kernel)

def c243_101 := ruleFor 243 lower115 (some (3,i1,i6)) (by decide +kernel)

def c243_102 := ruleFor 243 lower241 (some (1,i6,i7)) (by decide +kernel)

def c243_103 := ruleFor 243 lower115 (some (2,i1,i6)) (by decide +kernel)

def c243_104 := ruleFor 243 lower179 (some (1,i1,i7)) (by decide +kernel)

def c243_105 := ruleFor 243 lower227 (some (1,i1,i6)) (by decide +kernel)

def c243_106 := ruleFor 243 lower211 (some (1,i1,i6)) (by decide +kernel)

def c243_107 := ruleFor 243 lower241 (some (2,i0,i7)) (by decide +kernel)

def c243_108 := ruleFor 243 lower241 (some (3,i0,i7)) (by decide +kernel)

def c243_109 := ruleFor 243 lower241 (some (2,i4,i7)) (by decide +kernel)

def c243_110 := ruleFor 243 lower115 (some (0,i1,i4)) (by decide +kernel)

def c243_111 := ruleFor 243 lower241 (some (3,i4,i7)) (by decide +kernel)

def c243_112 := ruleFor 243 lower241 (some (2,i5,i7)) (by decide +kernel)

def c243_113 := ruleFor 243 lower115 (some (0,i1,i5)) (by decide +kernel)

def c243_114 := ruleFor 243 lower241 (some (3,i5,i7)) (by decide +kernel)

def c243_115 := ruleFor 243 lower241 (some (2,i6,i7)) (by decide +kernel)

def c243_116 := ruleFor 243 lower115 (some (0,i1,i6)) (by decide +kernel)

def c243_117 := ruleFor 243 lower241 (some (3,i6,i7)) (by decide +kernel)

def c243_118 := ruleFor 243 lower225 (some (3,i6,i7)) (by decide +kernel)

def c243_119 := ruleFor 243 lower179 (some (3,i4,i5)) (by decide +kernel)

def c243_120 := ruleFor 243 lower163 none (by decide +kernel)

def c243_121 := ruleFor 243 lower179 (some (2,i4,i5)) (by decide +kernel)

def c243_122 := ruleFor 243 lower211 (some (1,i4,i6)) (by decide +kernel)

def c243_123 := ruleFor 243 lower115 (some (1,i4,i5)) (by decide +kernel)

def c243_124 := ruleFor 243 lower115 (some (3,i4,i5)) (by decide +kernel)

def c243_125 := ruleFor 243 lower115 (some (2,i4,i5)) (by decide +kernel)

def c243_126 := ruleFor 243 lower211 (some (1,i4,i7)) (by decide +kernel)

def c243_127 := ruleFor 243 lower227 (some (1,i5,i7)) (by decide +kernel)

def c243_128 := ruleFor 243 lower242 (some (1,i4,i5)) (by decide +kernel)

def c243_129 := ruleFor 243 lower115 (some (1,i4,i6)) (by decide +kernel)

def c243_130 := ruleFor 243 lower115 (some (3,i4,i6)) (by decide +kernel)

def c243_131 := ruleFor 243 lower115 (some (2,i4,i6)) (by decide +kernel)

def c243_132 := ruleFor 243 lower179 (some (1,i4,i7)) (by decide +kernel)

def c243_133 := ruleFor 243 lower227 (some (1,i6,i7)) (by decide +kernel)

def c243_134 := ruleFor 243 lower242 (some (1,i4,i6)) (by decide +kernel)

def c243_135 := ruleFor 243 lower241 (some (1,i4,i6)) (by decide +kernel)

def c243_136 := ruleFor 243 lower227 (some (2,i0,i7)) (by decide +kernel)

def c243_137 := ruleFor 243 lower227 (some (3,i0,i7)) (by decide +kernel)

def c243_138 := ruleFor 243 lower195 (some (3,i0,i7)) (by decide +kernel)

def c243_139 := ruleFor 243 lower227 (some (2,i1,i7)) (by decide +kernel)

def c243_140 := ruleFor 243 lower227 (some (3,i1,i7)) (by decide +kernel)

def c243_141 := ruleFor 243 lower227 (some (2,i5,i7)) (by decide +kernel)

def c243_142 := ruleFor 243 lower115 (some (0,i4,i5)) (by decide +kernel)

def c243_143 := ruleFor 243 lower227 (some (3,i5,i7)) (by decide +kernel)

def c243_144 := ruleFor 243 lower227 (some (2,i6,i7)) (by decide +kernel)

def c243_145 := ruleFor 243 lower115 (some (0,i4,i6)) (by decide +kernel)

def c243_146 := ruleFor 243 lower227 (some (3,i6,i7)) (by decide +kernel)

def c243_147 := ruleFor 243 lower115 (some (1,i5,i6)) (by decide +kernel)

def c243_148 := ruleFor 243 lower115 (some (3,i5,i6)) (by decide +kernel)

def c243_149 := ruleFor 243 lower115 (some (2,i5,i6)) (by decide +kernel)

def c243_150 := ruleFor 243 lower179 (some (1,i5,i7)) (by decide +kernel)

def c243_151 := ruleFor 243 lower211 (some (1,i6,i7)) (by decide +kernel)

def c243_152 := ruleFor 243 lower241 (some (1,i5,i6)) (by decide +kernel)

def c243_153 := ruleFor 243 lower211 (some (2,i0,i7)) (by decide +kernel)

def c243_154 := ruleFor 243 lower211 (some (3,i0,i7)) (by decide +kernel)

def c243_155 := ruleFor 243 lower211 (some (2,i1,i7)) (by decide +kernel)

def c243_156 := ruleFor 243 lower211 (some (3,i1,i7)) (by decide +kernel)

def c243_157 := ruleFor 243 lower147 (some (3,i1,i7)) (by decide +kernel)

def c243_158 := ruleFor 243 lower211 (some (2,i4,i7)) (by decide +kernel)

def c243_159 := ruleFor 243 lower211 (some (3,i4,i7)) (by decide +kernel)

def c243_160 := ruleFor 243 lower211 (some (2,i6,i7)) (by decide +kernel)

def c243_161 := ruleFor 243 lower115 (some (0,i5,i6)) (by decide +kernel)

def c243_162 := ruleFor 243 lower211 (some (3,i6,i7)) (by decide +kernel)

def c243_163 := ruleFor 243 lower179 (some (2,i0,i7)) (by decide +kernel)

def c243_164 := ruleFor 243 lower179 (some (3,i0,i7)) (by decide +kernel)

def c243_165 := ruleFor 243 lower179 (some (2,i1,i7)) (by decide +kernel)

def c243_166 := ruleFor 243 lower179 (some (3,i1,i7)) (by decide +kernel)

def c243_167 := ruleFor 243 lower179 (some (2,i4,i7)) (by decide +kernel)

def c243_168 := ruleFor 243 lower179 (some (3,i4,i7)) (by decide +kernel)

def c243_169 := ruleFor 243 lower179 (some (2,i5,i7)) (by decide +kernel)

def c243_170 := ruleFor 243 lower179 (some (3,i5,i7)) (by decide +kernel)

def cs243 : Cuts (goalAt 243) := [c243_0,c243_1,c243_2,c243_3,c243_4,c243_5,c243_6,c243_7,c243_8,c243_9,c243_10,c243_11,c243_12,c243_13,c243_14,c243_15,c243_16,c243_17,c243_18,c243_19,c243_20,c243_21,c243_22,c243_23,c243_24,c243_25,c243_26,c243_27,c243_28,c243_29,c243_30,c243_31,c243_32,c243_33,c243_34,c243_35,c243_36,c243_37,c243_38,c243_39,c243_40,c243_41,c243_42,c243_43,c243_44,c243_45,c243_46,c243_47,c243_48,c243_49,c243_50,c243_51,c243_52,c243_53,c243_54,c243_55,c243_56,c243_57,c243_58,c243_59,c243_60,c243_61,c243_62,c243_63,c243_64,c243_65,c243_66,c243_67,c243_68,c243_69,c243_70,c243_71,c243_72,c243_73,c243_74,c243_75,c243_76,c243_77,c243_78,c243_79,c243_80,c243_81,c243_82,c243_83,c243_84,c243_85,c243_86,c243_87,c243_88,c243_89,c243_90,c243_91,c243_92,c243_93,c243_94,c243_95,c243_96,c243_97,c243_98,c243_99,c243_100,c243_101,c243_102,c243_103,c243_104,c243_105,c243_106,c243_107,c243_108,c243_109,c243_110,c243_111,c243_112,c243_113,c243_114,c243_115,c243_116,c243_117,c243_118,c243_119,c243_120,c243_121,c243_122,c243_123,c243_124,c243_125,c243_126,c243_127,c243_128,c243_129,c243_130,c243_131,c243_132,c243_133,c243_134,c243_135,c243_136,c243_137,c243_138,c243_139,c243_140,c243_141,c243_142,c243_143,c243_144,c243_145,c243_146,c243_147,c243_148,c243_149,c243_150,c243_151,c243_152,c243_153,c243_154,c243_155,c243_156,c243_157,c243_158,c243_159,c243_160,c243_161,c243_162,c243_163,c243_164,c243_165,c243_166,c243_167,c243_168,c243_169,c243_170]

def dict243 : Nat := 0x402a500a74029500a340281009e4026d009940241008d4022d0088401cd0070401b5006b08c81004d401250045401086202400c900302400c81123000c511040285009d40249009140239008a145010079401dc9040401d90075401d10072401c42110401b9005440144822040139004c4012d004a10880224040121004740119004304500812008e00624040059001320900628014a01000d400288110146003180402a100a640289009c40269008f40224c140401bd004f0448100443810100aa40291009f40231006c4021900804018e00148004e00128004600108003d00984021e000e80036000c8002e000a80024500114008220140050b020400e4421008409006940105003a20c00920040038c10038000b0004020d0082401a900674019500604017d0055400dd0035400ad002930081009540251007d401f1007a401690058400f9003c08c0100254003d001f4006c90022804052001440062000c401005d401590026800203101400f4214040070c001208050059400b5007f4025d002120500a040401720007800181300084c043000c80061001c001007e40258508008a00e020400fd003608601002a1850042802408011804019900621408081022084100850884100314002d00521484023024010031204005c704010d00612024808b010400b07010401e100614014d0038400b8110240049000c40211006808c0c32021484862600c4c051414024d007b4015d003b400644201402050064401790034400cd002840091002340079001a18881001d40141002f4005500094002200054000821030880d00201084850124016d001124840c060301047020280c083020c44052022404a00040c882000328180e06014180424108580223008504c1412c0c2000224848c10120c04814120c0d0010144042301240c082030c84082124009d000640010810380004130240060c00020800900028000810004c40430204c0461018000043014008850304000011120440c42030884900014000c500040014420008800210004400706018504616010d04703030200a08024200323020a0081804001c321230100131210c0c1303280804240141009010084808202140402202204042220044404202084041101

def d243 := unpackCases dict243 9

def u243 := unpackShort dict243 9

def w23 : Sig := 0xffffffff00000000ffffffff00000000ffffeeee00000000ffffeeee

def s31 := certify 243 5 ([w23,i7,i4,i0,i1,i6]) cs243 [] (u243 6 60 0x1e3d4beea84d08485096fa50a16a210a02db42040855204067c04081a85405ad6b1c01e1d453502b1801028444c21900140013800205a856a)

def w24 : Sig := 0xffffffffffffffff0000000000000000ffffeeeeffffeeee

def s32 := certify 243 5 ([w24,i7,i4,i0,i1,i5]) cs243 [] (u243 6 60 0x3c7c1c7e111a11912248a51227021116d5b410c5c625488d1c80121e5e02b8485ae74891c0a4805601601d12e440943204012004815c0570)

def w25 : Sig := 0xffffffffffffffffffffffffffffffffffffeeeeffffeeeeffffeeeeffffeeee

def s33 := certify 243 6 ([w25,i7,i4,i0,i1,i5,i6]) cs243 [s31,s32] (u243 3 72 0x256891a1dd104721845922a21c85f2212c5d17538892c218c053024e811a819505142c2c619c55601d4173a04681104c08be00213c02815005c1b)

def w26 : Sig := 0xffffeeeeffffeeeeffffeeeeffffeeee

def s34 := certify 243 6 ([w26,i7,i4,i0,i1,i5,i6]) cs243 [] (u243 3 81 0x711c423421845921ac6b06c85d17538892c218c05301bc6f0ac1b19505142c2c619c55601d41731a4690a5808be00213c06d1b42f040cd03320c4831880b42b604d829005c02fa)

def w27 : Sig := 0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa

def w28 : Sig := 0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000

def w29 : Sig := 0xffffeeeeffffeeeeffffeeeeffffeeeeffffeeeeffffeeeeffffeeeeffffeeee

def s35 := certify 243 5 ([w27,w28,w29,i1,i5,i6]) cs243 [] (u243 3 57 0x8b0e0419451421845922013c308b05d17538892c2818c053019d8556492d1512924951005c0bf604d8bb01d4173)

def s36 := certify 243 6 ([w28,i7,w29,i0,i1,i5,i6]) cs243 [s35] (u243 3 75 0x405433422c380861164881521c8804f01745d4e224b0a14751c8105463014c06541450b0b186715581369345f601d417340cd02f20c482f0542f054bb005c027a)

def s37 := certify 243 6 ([w27,i7,w29,i4,i1,i5,i6]) cs243 [s35] (u243 3 75 0x95a246906514508611648a8312c22c1745d4e224b0863014c218ba1e68676155808be00213c0170a17c075005cd03340a483120a6829a2fd813609c11)

def w30 : Sig := 0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc

def s38 := certify 243 6 ([w30,i7,w29,i4,i0,i5,i6]) cs243 [] (u243 4 75 0x2403320ba2e91c21845910a01888444b04329051209826007502e72525491e60619c553008b7000213c16040810006314c040cc8158831105700ae013a101684ea)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s39 := certify 243 7 ([w29,i4,i0,i1,i5,i6,i7]) cs243 [s33,s34,s36,s37,s38] (u243 5 225 0x2210712b21c62ca228429a086b2b01adac1a2820b408213a1874e859102090b09329e72902c502ac284b05d3b61744d843ac38cd8890ac08cb0c0b609cd86302c01cb053036025145482862904fd028ad29019078619444fc4787d144418408608c41cc090708c18cd861ac8067da0156c18600d3013f187500600d334d7393cd949400028d3294265428000e000110522ce414e10002400008d30a41ec4f08000d335d62a629a1dda285f29a99a10471321f72107d13211f2084b0b01ef0087b0b012f0)

def w31 : Sig := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000eeee0000eeee

def s40 := certify 243 5 ([w31,i7,i6,i0,i1,i5]) cs243 [] (u243 6 60 0xb5c852e43c3b153d8b7ade30134b202487a7610d8f99f04f9f2eb51f3e9141f3ed829f48d88a4009c08000a5880127c01f009045c801b056c)

def w32 : Sig := 0xffffffff00000000ffffffff00000000ffffffff00000000eeeeeeee

def s41 := certify 243 5 ([w32,i7,i6,i0,i1,i4]) cs243 [] (u243 6 60 0xb5ad69280787534faa12df4a14268424285a884280cf80810215481016da10206a1501e3d48b5009c001028444c21900140043b00205a856a)

def w33 : Sig := 0xffffffffffffffffffffffffffffffffffffffffffffffffeeeeeeeeeeeeeeee

def s42 := certify 243 6 ([w33,i7,i6,i0,i1,i4,i5]) cs243 [s40,s41] (u243 3 72 0x21849f22a3048772212c084f0022ccb00a20405f00134892c218c05301745d432493a046a0b0b0075005d2f084551546541452811a045895a08eb815)

def w34 : Sig := 0xffffffffffffffffeeeeeeeeeeeeeeee

def s43 := certify 243 6 ([w34,i7,i6,i0,i1,i4,i5]) cs243 [] (u243 6 81 0xb013e0b56a34080029c0001166580d9b0a0022410c05880520172e0432776e545010c043007400592f4152a640940268d0a0a70e0c820260098005c0170810615060c814041c1190a)

def w35 : Sig := 0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000

def w36 : Sig := 0xffffffffffffffffeeeeeeeeeeeeeeeeffffffffffffffffeeeeeeeeeeeeeeee

def s44 := certify 243 5 ([w30,w35,w36,i0,i4,i5]) cs243 [] (u243 3 57 0x954895521849f2222708084f094c0155022ccb0018c5302c2c01d4017619505144bc21154554e42ce20192ac5d1750c9)

def s45 := certify 243 6 ([w35,i7,w36,i0,i1,i4,i5]) cs243 [s44] (u243 3 75 0xc48831208cc1221849f20213c02f000bc0230bc008b32c0892c218c053080665717c191745d4324b0b0075005d2f084551558215fc910846541450230cc232ad39027a)

def s46 := certify 243 6 ([w27,i7,w36,i6,i1,i4,i5]) cs243 [] (u243 3 75 0x21849f20c488292a0c4b08b0084f0022ccb00bc00290a0bc0750005c892c218c05301745d432618ba1e68214bc5515798da24690651452829a09d982109c11)

def s47 := certify 243 6 ([w30,i7,w36,i6,i0,i4,i5]) cs243 [s44] (u243 4 75 0x43093e20c4420ac500c442225820084f0008b32c0178001582040800318a601304c00ea0b0ca414486525491e60978422a8aae2405f20ba2e90c9805702cd08c04ea)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s48 := certify 243 7 ([w36,i6,i0,i1,i4,i5,i7]) cs243 [s42,s43,s45,s46,s47] (u243 5 225 0x1a086b2b01adac1a28208c508213a18473e89f1020873c3012c2087308212f0c14006d2ae1b54b942800240000bc0a4f04f080010b00011622d0b58cb100007dbae1340007d000136eb90609329332902c5029828c6089090908c424c09809c6063013301c1f4530180043145d4cd81744604314c53265b36c82a02907ed028ad2908100a008ce0c0b808c80c0380168075020016e16db84bd8820da01558e0557a01944e047b81444804965171a2109528c52a2266228428c535ce2a62941dd4285f294994)

def w37 : Sig := 0xffffffffffffffffffffffffffffffffeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee

def s49 := certify 243 6 ([w13,i6,w37,i7,i1,i4,i5]) cs243 [] (u243 3 75 0xa831255c88e121849f2c22c0213c02881005c0017022c1701d40029224b0863014c093a046a0f93e4510ac212945515415636891a0e451144a34a0468116608447)

def s50 := certify 243 6 ([w15,i4,w37,i7,i0,i5,i6]) cs243 [] (u243 3 75 0x95a246b91388611648a831220c88cd19505142c2ca04681164651914c290dc55154a5054b54e443484f26a6881a0b45314ca101745d40ac892c224e811a880b44d)

def w38 : Sig := 0xffff0000ffff0000ffff0000ffff0000eeee0000eeee0000eeee0000eeee

def s51 := certify 243 6 ([w38,i4,i7,i0,i1,i5,i6]) cs243 [] (u243 4 81 0x955122a10c22c884a21c42e8ba4711226089354145795e16d86520a241304c30ce2a99505403f0fcd61244971025104a21b46da288e2384128825420370b6460a4caa2a80)

def w39 : Sig := 0xffffffff00000000ffffffff00000000eeeeeeee00000000eeeeeeee

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s52 := certify 243 6 ([w39,i7,i0,i1,i4,i6]) cs243 [] (u243 6 180 0x45e11e3d4cb545ec97dd41350e01202169038b0e0800025201e1d4bb5252b9a7d403504850874bad08497420e8508e428400835bce107480428442142d4ab5105443542847a04008abada7957a01204001020162dd9f005b802d02036810212084d9054850200a8103528d42940ad502004040873a1c11d601c081000400b249c012002c08136040a10c84d8611308142403064005010020500640140816a61a853015a816a)

def s53 := certify 243 6 ([w39,w37,i7,i0,i1,i4,i6]) cs243 [] (u243 3 72 0x95a246b913849127802881005c00171745d4e18c053024e811a10c6541450075005c3708455156811a044411acb8612013c08b0892c22c20c6884b)

def w40 : Sig := 0xffffffffffffffff0000000000000000eeeeeeeeeeeeeeee

def s54 := certify 243 6 ([w40,i6,i7,i0,i1,i4,i5]) cs243 [] (u243 3 81 0xa8c122e1648084f00a20404912780892c218c053024e811a114450678b0b0075005d2f08455156811a046a1e0e78711c423a20ec83b005c017880ac196608439a0568234)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s55 := certify 243 7 ([w37,i7,i0,i1,i4,i5,i6]) cs243 [s49,s50,s33,s51,s52,s53,s42,s54] (u243 5 225 0x9d10952b2289dc891284297938e11c4117710411ce3b408213a1874e85910208fb0822b0288dc30282088d354b112c2088d08212c8d12ce0049116124e58e1000240000bc0a4f04f08000970002ae2897b88128000ad596134000990001356584a85d3b61744d843aa38cd889098108c234c0b609cd863018101c1dc53036010d8932aa290a902b629ad39c87a0194463c4785f14448040a008c63cc088d08c80c0280168075020016a16da8daa820da0156aa0552a0290a102a82908106ace518fb35d4)

def w41 : Sig := 0xffffffffffffffffffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaa

def s56 := certify 243 6 ([w41,i7,i6,w9,i1,i4,i5]) cs243 [] (u243 3 75 0x86127c8a8c12c22c0213c008b05c0282f01d400d3224b0863014c20f93e4510cd8ba1e68212945515495720a4017005c510e45128e823a08d982115c95a08e9011)

def s57 := certify 243 5 ([w30,w35,w13,w9,i4,i5]) cs243 [] (u243 3 60 0xc22c21849f2222708084f01d4002f022c810018c530255c82b005c017660842b04439046a38829423441441108c21154553e4f9044c5)

def s58 := certify 243 6 ([w35,i7,w13,w9,i1,i4,i5]) cs243 [s57] (u243 5 78 0x30208c0a23042086127c200213c01d4002e022b80008b580224230218c014c022029455154a5885f88f93e4514cc255c2c005805861a0c97f5fc918851e05128e0ca2804105180a)

def s59 := certify 243 6 ([w30,i7,w13,i6,w9,i4,i5]) cs243 [s57] (u243 4 78 0x43093e26084c14031108896080213c0022ec01d4000bc102040018c530095710560b02c28872289466304215c02b81668414a1c905180bf03e4f9144c5525491e60528422a8aaa)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s60 := certify 243 7 ([w13,i6,w9,i1,i4,i5,i7]) cs243 [s56,s58,s49,s59] (u243 5 234 0x6821acac06b6b068a08231420851e8611cfa27c5108236cc3200821cc20a030c5001b4ab86d52e50a000900002f0293c13c200031400051588b1f56585100082e1d4d300080000d3bae40a524ca4cca40ad40a294a30a522424cc23073302294270a518c04cc0707d14c0294096c5b2051314f94cca53e45129451314c5316036e015ca529602945515d33154ae0a50d750a264a5385023842c3855c2e02c0e1c00e0058d75801f405b8585111c5135f8e051e0513144728e011c615f81a0e203144711e21449528c52a21de2285128c516c42a029036d0285f290810)

def s61 := certify 243 5 ([w28,w15,w27,w9,i5,i6]) cs243 [] (u243 3 60 0x1065145095aea2184592c22c2a13c9393888320a59855056202d0a682daa9e919a34c5d17502f224b08150dc15a940053a)

def s62 := certify 243 6 ([w15,i4,w27,i7,w9,i5,i6]) cs243 [s61] (u243 3 78 0x95a246906514508611648a8312c22c4e4e220c829a0a682d661542d14c2d14ca1880b429044b54e443484f214e85fa4651914cd301745d40cc892c262e879a15437154a5)

def s63 := certify 243 6 ([w28,i4,w27,w9,i1,i5,i6]) cs243 [s35,s61] (u243 3 78 0x1065145095aea2184592c22c2a09485d17538892c2808415154150dc2f1dc3762e879a4e4e20c482966084155455117c29a0a68bfa0468d3e4e409482520542f054810)

def w42 : Sig := 0xffffffffffffffff0000000000000000aaaaaaaaaaaaaaaa

def s64 := certify 243 6 ([w42,i6,i7,w9,i1,i4,i5]) cs243 [] (u243 3 78 0xa8c12241648084f00a0bc04912780892c218c0530862e879a4e4e255c829005c017a08e8234e4e1c47108e8b0b0075005c570845515598210e6811a08451)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s65 := certify 243 7 ([w27,i7,w9,i1,i4,i5,i6]) cs243 [s37,s46,s62,s63,s56,s64] (u243 5 234 0x2744254ac8a2772244a10a354412078652c5e1460104d02084e861d3a16440823ec208ac0a2370c0a082234c32008223420a030c38012445849396384000900002f0293c13c20003ec000ab8a2b6eb8a0008161d4d300080000d359610db174ed85d13610e604e33622426042308d302d8273618c06040709914c0d806b45b2085d98b28fb28853ec792b62a039e015f6da0d85515d811544a0438d73841dc43a8382a02c0d7c022342c28a00a0058d758017c05a858a98a35e8a0aa0a3ee62fe098615e81a0a203ee698fb16d0)

def w43 : Sig := 0xffffffffffffffffffffffffffffffffffffccccffffccccffffccccffffcccc

def s66 := certify 243 6 ([w43,i7,i4,w9,i0,i5,i6]) cs243 [] (u243 4 75 0x2403320ba2e90c510c22c885021c4222582194828904c130c8ca322985ea4a923cc037154552948e238441882b14c2d14ca1852144202d16cb5238886884f12570a400a)

def s67 := certify 243 6 ([w28,i7,w15,w9,i0,i5,i6]) cs243 [s61] (u243 4 78 0x25033210b57104308b22150871090d13c432905120982618371545529455a0bf44651914d3f2388e110620c5080b42f51d4720682985a299422e8ba40bc89130540be85d8002986ea)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s68 := certify 243 7 ([w15,i4,w9,i0,i5,i6,i7]) cs243 [s66,s67,s50,s62] (u243 6 234 0x441380a65c1132442820a340b50a61a8d30342810268081047581a3ab01010215505104fc80a2b4510a840f54c8113f087be500950202a808627e3017a0432a0c93eb06a469a329fd4466954a4699a669b6365b5aa951b54a9693f29452c1450d7282899145161408b020e35c704f81072c1c08cd04c16106096026066b0a53291aeb16525948d39850b69822d2c10d962c34e64c29492b14698a29d8a0aa4287522d421a61077c1c1290449490d04698249ea702a408d3ac0083624c51b22885e2029b0a0862dc64dae046c11918ac863622411b20867a1809b02)

def w44 : Sig := 0xffff0000ffff0000ffff0000ffff0000cccc0000cccc0000cccc0000cccc

def s69 := certify 243 6 ([w44,i4,i7,w9,i0,i5,i6]) cs243 [] (u243 4 78 0x900cc821845910a043886520a241304c3292a48f3000aa0b11c47088310570a42802bc1612449700020940368db400ba2e91c44898216c5529455420370b54a85053)

def s70 := certify 243 6 ([w35,i6,w30,w9,i0,i4,i5]) cs243 [s44,s57] (u243 5 78 0x8893020bae82090e8200213c0006314c0016580010204008c08c00750161b680551560c877814952479402c02a8058058823689555545fa90a902cca2903162ca22444)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s71 := certify 243 7 ([w30,i7,w9,i0,i4,i5,i6]) cs243 [s38,s47,s59,s66,s69,s70] (u243 5 234 0x3ec4110c903572c90104d8e174c5105dd8410c538ed02084e861d3a16440823ec2090c102370c1008223420b63089234c33608238012445849396384000900002f0293c13c200025c0010b9025ee20500002c4003670632b5c14f60007a0194463c4789914448040a008c63cc088d08c80c00d9016807502001663d66ac571879814940fb524793ec79420436397616e0836805516d8f1544a8438d73841dc43aa382a82c0d7c022342c2aa80a8058d758017c05aa59099035eaa90a903ee62cf698816ea236ab63ee698fb15ca)

def w45 : Sig := 0x5555555555555555555555555555555555550000555500005555000055550000

def s72 := certify 243 6 ([w45,i4,i7,w9,i1,i5,i6]) cs243 [] (u243 3 81 0x95a24688611648a88723e4f94e7f49f32824e949a18c11904e4e1044120c4691a68150fc3f004c08be002094028150e4e4084825215455084a515c2166046815a05c0210)

def s73 := certify 243 7 ([w28,i4,i7,w9,i0,i1,i5,i6]) cs243 [s33,s36,s72,s63,s66,s67] (u243 5 98 0x114c8410e3840861164209421c20a49021745d10e224230220975097536b8d5db615cb1d865105110230233680551a050ad50d3820b89982016c4384382c02c0975097504db877b8e935c5f35ca38438490290252e2040)

def w46 : Sig := 0x3333333333333333333333333333333333333333333333330000000000000000

def s74 := certify 243 6 ([w46,i6,i7,w9,i0,i4,i5]) cs243 [] (u243 3 81 0x893304885d0ec8084f0024c8100174cb027cc9fd0464017624c1162d8b1750f93e44310c83102bc206f1bc9381144517605d24c231743720ec817005c0a5154371545b80662a82324f85d0dc5d)

def s75 := certify 243 7 ([w35,i6,i7,w9,i0,i1,i4,i5]) cs243 [s42,s45,s56,s58,s74,s70] (u243 5 98 0xa230420bae820bae8200213c0022b80016580016580224230218c014c023688d588c5db6c8b1db615c23023001d405b680551a0889d820c8ad82016c99802c02c00580589d889d8847c877c8eb35c5f35ca8b22444)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s76 := certify 243 8 ([w9,i0,i1,i4,i5,i6,i7]) cs243 [s39,s48,s55,s60,s65,s68,s71,s73,s75] (u243 6 308 0x7da209c0c514cb832e899223ec504147d9a05a9af14c3511a6981a3ec5020462b40409af08eb07268eac18a101023eca00d8698a5db17928b8a1f6280003147009069842d23e0e2c38c50800035e9000034c13c05e923c9cd7820000fb20d893ac2ab0aac4177207d8a6c28c50862dcac39b5cac11b04314718a39af18d889ac0ab02ac308d18d7826c08d338db1560158056386ad234c036015ab5a107d8a402ad10b442d0a2c451f641010314f20c96825a0968f15b40c50880235e09002b432d0cb4088d04d78c4030d3006980b459074b40100034cb1a65ab36acdab5a4082b56ad52b56ac18fb149851ae50d7286b8a26451f651314314246086b8e35c71ae13b043147461cd7829408d7606bb035c111a09af612981a60260035cb1ae58d7017801a65a616)

def w47 : Sig := 0x3333333333333333333333333333333333332222333322223333222233332222

def s77 := certify 243 6 ([w47,i1,i7,i0,i4,i5,i6]) cs243 [] (u243 3 81 0x256891a21845922a21c808be00213c02815019505142c2c01d4173a0468116084216114454e10c43c207401d01bc6f046b9390b0b001d00758216086811a0442d)

def w48 : Sig := 0xffffffffffffffffffffffffffffffffffffaaaaffffaaaaffffaaaaffffaaaa

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s78 := certify 243 7 ([w48,i7,i0,i4,i1,i5,i6]) cs243 [s33,s77] (u243 3 225 0x275095a0ce89d0cc91a4a1fd104707c1f1fc1f07c47440d48903b184350ec5942226c8a831a26c3121e8887bcc12c887b2212f312045e0644540653a3b01910ca043c8c206481d818c02d00742d14c2008f824e82ba23c2b1e6a28778815c2d0b45f0b42d15e2380110522f905e4000940092720947b0948001500a0be8150bc15a0072ce705c1f607d159407c7f07d19098b107c241cb1b037668084670dc2115619802900bd981802f0a573a6a05429056829a055885724e904ced45411)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s79 := certify 243 6 ([w28,w27,w10,i1,i5,i6]) cs243 [s35] (u243 3 180 0x1fd1181f07c7f07c1f64441508b0e0417b8100352240ec610d43b16508907cc62241c89b307b22009407b09425020481178191150194e8ec064432810f230819245621510b42d17c2d0b5518808606760dd8210dc5568607606300b401d0b45308007d5107d115407c7f07d15142544b115c21ecb151c609d84d5441365458ed09c81009c05b5441705440ed09c85013405b60441812713573)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s80 := certify 243 7 ([w27,i7,w10,i4,i1,i5,i6]) cs243 [s79,s37] (u243 3 234 0x9d4256833a274332469287f44607c1f1fc1f07d910352240ec610d43b165088ed22a0c687b0c431a2241f3188907226cc481178191150194e8ec064432810f230819207606300b401d0b45308045620290b42d1dc2d0b4298823e093a0ae88f0ac79a8a08606760dd8210dc55686e0044148be41790002500249c8251ec2520072c5b05ced00a3b69273b45fa00639d84d00600135275cc1f0a41f445501f1fc1f40a508292c457087b2c0a72827a454290a6829a3b42721582761342904d82963b42709ced16c11)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s81 := certify 243 7 ([w28,i7,w10,i0,i1,i5,i6]) cs243 [s79,s36] (u243 5 234 0x3b44114c941ff2c94104414422c0380414e380100d02084e861d3a164408226c2094c1426f021d40821ec20809001ee4900080108114e604511810e20e31810c22043308302602454822eb2c1decb2e20825c830d4a9425ea2cd421470818c0b0072c14c02007867845644787f78418408608c41cc090708c18cd861888067da015481867244d48ed18650ed935593b45f5061803a4016c618018016d595cdeb9e111511e1fde12e102b8231153021ec232e314994456eb94b943b66204098016ee580b803b6698ed134a)

def s82 := certify 243 7 ([w30,i1,i7,w10,i0,i4,i5,i6]) cs243 [s38,s33] (u243 4 98 0x2403323884708611644280622131820116e00041282c0812e007380f13c41304c01973911f023e060842131821084de27882609847c08f81ca8a8ee8aa88e2398260b80e002b15c5f0ae0158f28)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s83 := certify 243 8 ([w10,i0,i4,i1,i5,i6,i7]) cs243 [s78,s80,s81,s39,s82] (u243 4 308 0x7684641c5995066388fe11866119daa228edd086b6c54188d63de831d1daa109990d4426c481d8c23f86a1d8b2cc90423b6081bde750563796300ae076a90a66488115e7760451f4982332e439b16604379c4810c7b6218d88b021378818c4d005a01378168a626810045515421e715c2d0b5152b42d0b5e715d083b680009aa135426d099a1daa00199700026910522c4d720ae6648003621280026884d109a128f612b6220004d1345bb1daa3285b80b7016d43ba8ed81a0ccf8de16c82d905bf0ffe66486236223085b620ec16c48389b16198f386e630b680846716c370845579d06309a01340268b66309a2689ab989a2689b23b5413a915822b045542fa8ed804f0667c23f915222a4457c3ff999208e46c44258915622ac45443d89b16096c)

def w49 : Sig := 0x3333333333333333333333333333333333333333333333333333333322222222

def s84 := certify 243 5 ([w49,i7,i6,i0,i5,i4]) cs243 [] (u243 6 60 0xb7c250e134b11f588f4ee51f7428962142dc6a12eaba8024d9c2050971894223d7b856e89b9144014806205081420c189661d12e4415b856e)

def w50 : Sig := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000aaaa

def s85 := certify 243 5 ([w50,i7,i6,i0,i5,i1]) cs243 [] (u243 6 60 0x2deb7a1a09a590ffc87a76353b16b916243c3b0d6c7cbaa32f9f33e09f3e9141f3ed829f48d88a400a58800018080127c01f009045c801b056c)

def w51 : Sig := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffaaaaaaaa

def s86 := certify 243 6 ([w51,i7,i6,i0,i5,i1,i4]) cs243 [s84,s85] (u243 4 72 0x4538004586a0028bb00ee0009a3180530112234442e8bbe4126a1e542fa102b8861164425684c026a0949052c852119fe4b4511455a510a6255411a890)

def w52 : Sig := 0xffffffffffffffffffffffffaaaaaaaa

def s87 := certify 243 6 ([w52,i7,i6,i0,i5,i1,i4]) cs243 [] (u243 5 81 0x8a700022f4006d1b5400630053008908d1085d175e206f1bd050218459086b1af00804d4049220a548248233de4b451144691a6840711c72400b80b88a88a82302c06192a0411ec8a)

def w53 : Sig := 0xffffffffffffffffffffffffaaaaaaaaffffffffffffffffffffffffaaaaaaaa

def s88 := certify 243 6 ([w35,i7,w53,i0,i5,i1,i4]) cs243 [] (u243 5 75 0x8a702e000b808ae00022f400630053008908d10aa208a888aa205d175e20c097d2ac2086116420135012488295209208cf1925fc9149e4b4511462ca298411e98a)

def w54 : Sig := 0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000

def s89 := certify 243 5 ([w54,w27,w53,i6,i1,i4]) cs243 [] (u243 4 57 0x1161a82490015b4d400900453806300a601745df225f4215b448a591122344444b7c288a2308859118d221c4c110a2808cf)

def s90 := certify 243 6 ([w27,i7,w53,i6,i5,i1,i4]) cs243 [s89] (u243 4 75 0x114e001161a802f000290282f026a00486300a60224468885d177c80ad080a49350f2a448a5908611644c1285f1484233c8c6a891525be144515052a214c6904f0)

def s91 := certify 243 6 ([w54,i7,w53,i6,i0,i1,i4]) cs243 [s89] (u243 4 75 0x1161a802f0002f068bb000453806300a601745df202b4202b4682b41122344404d412920a59792d1445134a6117e42908cf27b455f86110b22d063a21c4c104ea)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s92 := certify 243 7 ([w53,i6,i0,i5,i1,i4,i7]) cs243 [s86,s87,s88,s90,s91] (u243 5 225 0x14006d2ae1b54b9428000e10000bc087ff0a708003400079622f45b4780007fbae1340007f000136eb90206f2aa1bd0a9028829c206302c01cb053008010f6089088090f20d109809e205dd18175e61ed082073aaa15c8207320815eaa9a08228e129a2c5a2820b40827ba1874e8597820aab36cc292290505028ad29049001201641d350107016492d924885048d873294849208e1094149209208e1384cf7927b4e12d7b814744851aa4dd1a2789529872a2266229e298746c42a62901dd0285f290990)

def w55 : Sig := 0xffffffffffffffff0000000000000000ffffffffaaaaaaaa

def s93 := certify 243 6 ([w55,i6,i7,i0,i5,i1,i4]) cs243 [] (u243 4 81 0x229c0051760124497006300a60224468889350f2a114452384ad08440ec404d412920a590a4233d5a510a32903920e238846a058164611813041d98d20e5505047e)

def w56 : Sig := 0xffffffffffffffffffffffffffffffffffffffffaaaaaaaaffffffffaaaaaaaa

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s94 := certify 243 7 ([w56,i7,i0,i5,i1,i4,i6]) cs243 [s86,s93] (u243 4 225 0x13a4255419a89d0cc9151143b90823fbc2ffbc23908e00924b092eb3880023a00083d10f61e87a20009b001417a89b0bcbb50003ddac268003d80026dac4408aec08a4c11c8771031802d0702d14c08021f822448121e834458111e824d415a88f0ac79521446e302ba1046a102be301a88440ec610d43b0d482168425062ad063a5084e79cecf4bc40e49e0e7c491012059074d408382d2906f29215d406e4686e894841488319485210621499ea92b414e9414ab52215cd3c4c77a370)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s95 := certify 243 6 ([w54,w27,w11,i1,i4,i6]) cs243 [s89] (u243 4 180 0xe48497bc1cfbd22103b20c220d441d86a1a88827004925849759c40011bb595b0007b0015bb5907b26b2001070025690f600083d10f61e87a200088115d8114982390ee2063005a0e05a29810046f1856d082350856f1823508906f2234370de48921f822448121e8344581795bf111b2785ff115b248273096ad9a4adc8ef09c87104e216d5b6095b11de1390a212c42dca029091d12ccf)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s96 := certify 243 7 ([w27,i7,w11,i5,i1,i4,i6]) cs243 [s90,s95] (u243 5 234 0x2744254ac8a2772244a10ae0411279ee1e792104380124458493963840004740002f021efcf0200046d65a80001ec00285963bc000ab8a1eeeb8a00041d64d5200041c0012592108114e604511810e20e70818c0b0072c14c020043d8224220243c8344260246d8628208234822861823c824caa8a23ea1e4a20a2348212d922376d92212d02084e861d3ad0408273c5b30ef08228ef291d3bc7728209239d212c209208212d1d33dea1e111b11e17de12810a98a46e8a0aa0a3be6215298612e8192a123be698ef16d0)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s97 := certify 243 7 ([w54,i7,w11,i0,i1,i4,i6]) cs243 [s91,s95] (u243 5 234 0x2a4411ac9a2a722ada104e841842d02eb4d021023801244584939638400046d65b00001ec003059626c001ab9a26ee2eda0001ec0002f021efcf02000108114e604511810e20e70818c0b0072c14c020046d863020823482306183bc821aa9a236aa9a20843d8224220243c83442602792784e047b878448401201641d350107016492d924885748d88dd884927344b18ef49268ef9855d3bc776924823c4216d248248216d5d33dec1e111b11e17de13011a99a46f0c1ac1a3be621c298216f0302c023be698ef12ca)

def s98 := certify 243 7 ([w35,i6,i7,w11,i0,i5,i1,i4]) cs243 [s86,s88] (u243 5 98 0x2f00580016022b8001658001658018c014c022423442608218222a8821860821860830288a9082eba082eba0804d4049223648248cf192889d492e38492e38489d889d8847c877c8eb46c5f46ca8b22444)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s99 := certify 243 8 ([w11,i0,i5,i1,i4,i6,i7]) cs243 [s92,s94,s96,s97,s98] (u243 4 308 0xef08c838b0ea0cc712c4230cc233bd4451df400daf6a82f1b47ba05f43bd40030ee0092f692c248feeb39872000258960009620f44258f61e87a25880046d1bb59ed1340046c7b001ed136d63be081bdf750563791b00ae077a90a61c88115f7760451cc98230ee439ede20637dc016807be05a29bda04004b43f04489624084b43d0688962c091b46f187dc574211b235087dc57c60efd08425a84b5097a2b7477a84261c351084b2076308961a8761ab0e41084b12c5b61dea9285b80b7016d44ca8ef84a0c3fa5e16c81c905bf073e61c9223da09005bb20e9a8b6041c0f6da527dc379485b40b6816c37234377dd129096212c4258b72909625896678962589663bd413a91b8237046d43ba8ef804f061fc23f91b2236446fc2ff987208e4)

def w57 : Sig := 0x3333333333333333333333333333333333333333333333332222222222222222

def s100 := certify 243 6 ([w57,i1,i7,i0,i6,i4,i5]) cs243 [] (u243 4 81 0x21849f109460880213c0022ccb00144080955046a1304c00ea0b0ca41448a82a0338ce10a04310d82e0380114452206f1be0a1304c0701c71033218c1c842a82a18)

def w58 : Sig := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000aaaa0000aaaa

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s101 := certify 243 6 ([w58,i7,i0,i6,i1,i5]) cs243 [] (u243 6 180 0xbd04b5c87520bd74a5c80521f904f0ec61b1f960a9ec05b0618840844218206023008b510d2c83120b530ffc811212b10f4ec55b12b54d4ec11b114891b196c44c916c912013e7c313567c126a0863e7cd9f3e11d1756dd11910f9f1e7cfa4389079c5090f9f0a7cfb628d82940ad8f9f02000063c1809e021800018000041ca460e62100001e00024169078b11720048705893e00f9c0000f8b3e140006c5db052e15b006c)

def s102 := certify 243 6 ([w58,w41,i7,i0,i6,i1,i5]) cs243 [] (u243 3 72 0x86127c8a8c12c22c10c43c21745d07e093a1e6a019066095a08e8492c2c4be0a5807c3914451a08e8850fc6d0c20014c630005c8b005c001700be804d)

def w59 : Sig := 0xffffffff00000000ffffffff00000000ffffffff00000000aaaaaaaa

def s103 := certify 243 6 ([w59,i5,i7,i0,i6,i1,i4]) cs243 [] (u243 4 81 0x8b0d400517600304f00c6014c02e8bbe4126a1e5421886cc12aa08d404d412920a59792d1445156944288220c98cab43560d635e9400f401ee1184109e0d4c60a64a82b42)

def s104 := certify 243 6 ([w22,i5,w41,i7,i0,i1,i4]) cs243 [] (u243 4 75 0x505e02f4004dc09894e00117600c6014c049a879520e3c23084605d177c1582c0b25e82950a08d44299916449f0a7c518a228c17d5156a0d49f16459112aa08d442784b)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s105 := certify 243 7 ([w41,i7,i0,i6,i1,i4,i5]) cs243 [s56,s42,s100,s101,s102,s86,s103,s104] (u243 5 225 0x15f0827ba18579e89f78208a90822b028a9c0c1282097730c12c208d508212cc3240000bc0a4f04f080015f00079622c7f59678000fd0002ae287fbae280007f2c4ad1340007f0001347f134c604308810cc20c09809c206302c01cb05300801e205dc98175e61ec88208f20932aa288fa879288289920815d8607761815c822278952b22a2ca229e29b739c40a808ce0c0b808ca0c03801664d6007f016e16db84bc864c8d85f2948e087a87b2e387b81472a0512b82a2a222a82a2e0856d4eb18fd36d0)

def w60 : Sig := 0x3333333333333333333333333333333322222222222222222222222222222222

def s106 := certify 243 6 ([w60,i1,i7,w13,i6,i4,i5]) cs243 [] (u243 4 78 0x10c24f89821304a0c440109e00117600ea00052051020231aa2454a82a021886c1701c00a381450338ce10a06f1be0a1304c0701c11c5128c513183908550540a5)

def s107 := certify 243 5 ([w22,w54,w27,w13,i1,i4]) cs243 [] (u243 4 60 0xbd000297e400d0145380045d80318053020e3c211a295049a87950ba2ef82b318a3d2835510a427829541470ebc288a22113ea)

def s108 := certify 243 6 ([w54,i5,w27,w13,i6,i1,i4]) cs243 [s89,s107] (u243 4 78 0x22ec00bc000a5f9003400f43d00141e806300a601745df2118c211a29518423049a87951039f0a228b1aa245463073a5052a2155051c218f877f2b6ad8be14e831d10e2)

def s109 := certify 243 6 ([w22,i5,w27,i7,w13,i1,i4]) cs243 [s107] (u243 4 78 0xbd000290282f05800b013129c0022ec018c02981071e1049a8795212f2951842302e8bbe0ad414a885318a30d484f05300d49f1645927d42fa9916449f3844c6a8915147e14451)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s110 := certify 243 7 ([w27,i7,w13,i6,i1,i4,i5]) cs243 [s49,s106,s46,s108,s90,s109] (u243 5 234 0x57c209ee861357a27de08236cc3280822c420a830c3f4208ac0a2b70c0a082e0c30e1082e0208e130c900002f0293c13c200057c001e588b1fd659e00036eeba80001fc0028ba83f4000ab8a1feeb8a0001fd65b80001fc003859631810c2204330830260270818c0b0072c14c0200788174d7605d798795f20836c8228618265862820823c824caa8a23ea1e4a20a1dc8238d92f17f629782086dc5b10bf798d28fd28bf3f49129e2b839f811de7b8785111d5f144a98a36e8a0aa0a3f66217898611e81b8a383f6698fd16d0)

def s111 := certify 243 6 ([w30,i1,w35,w13,i0,i4,i5]) cs243 [s44,s57] (u243 4 78 0xc109821849f1098c100427802f0002f011640801ce004c13016058de80a300e42b1dc395fd7f24423213d008c3308cab60982e03805555517c2b805701e50a54047)

def w61 : Sig := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000

def s112 := certify 243 6 ([w61,i5,i7,w13,i0,i1,i4]) cs243 [] (u243 4 75 0x2f4000bc1a2ec004c4a70008bb006300a6041c78423415a3084605d177c9982c0b25e8295065ff448e9916449f0c7c518a228ac3a08f442785b506a4f8b22ce823d10e2)

def w62 : Sig := 0xffffffff00000000ffffffff00000000ffffffff0000000000000000

def s113 := certify 243 6 ([w62,i5,i7,w13,i0,i1,i4]) cs243 [] (u243 4 78 0x5e800178345d800213c0318053020e3c211a0ad021886c102c0b25e8295065ff448e84c13161d047a6084c1ac6bd088b05802e8bbe40b7e14451213c1aa9411f89f)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s114 := certify 243 7 ([w35,i7,w13,i0,i1,i4,i5]) cs243 [s58,s111,s45,s112,s113,s88] (u243 5 234 0x36cc33208235420b230c2a420a2c222a7030620822c4209ee8612b7a27de082900002f0293c13c200036eebb20001fc0032bae3f40022ba21feeba20001fc001e588b1fd659e00031810c2204330830260270818c0b0072c14c020036c823261826586322083f48222aa21deaaa220878817533605d798793320808dd08ce0c0b808c64cc03801664d6007f016e16db84bc864c8d85f2948e086d4471891e17f88fd5fc913f4918b889e3ade16f8e1ee05116d9314629a236f2ca2ca23f662ade98416f211ec9e3f6698fd11ca)

def w63 : Sig := 0xffffffffffffffff0000000000000000cccccccccccccccc

def s115 := certify 243 6 ([w63,i1,i7,w13,i0,i4,i5]) cs243 [] (u243 4 81 0x30426089530440109e012449005e0254810098260263040262560c6b1a2ee0f93e4711c49580ba26085d07002288a2eb85d25602eb04c1701c00a228f8a316fc42295025502ef85d)

def s116 := certify 243 7 ([w30,i1,i7,w13,i0,i6,i4,i5]) cs243 [s47,s42,s49,s59,s115,s111] (u243 4 98 0x86127c4c1098280622131820084f0008bb002f0002f040810039c013d0356058fbc238982602c0b7839144c47c08f80721595a1c8722d9321c91f023e0729b63b9b6a60982e0380f267e0ac2b15c5f0ae0158f28)

def s117 := certify 243 6 ([w54,i7,w22,w13,i0,i1,i4]) cs243 [s107] (u243 4 78 0x17a0005e022ec0068bb0013129c0318053020e3c205d177c15a3415a308460160592f414a8378a31445128f42fe9916449f50484f062e3e8abd13e1a8b22cf831d784227fca)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s118 := certify 243 7 ([w22,i5,w13,i0,i1,i4,i7]) cs243 [s112,s117,s104,s109] (u243 4 234 0xa006d505e36d02fa28000d42f2f53700035001370bc2f3840027c3d4c47f0f4a727c0037400f588b1fed6f001040dea0ac6f805705215c40c600b41c0b45302006da101ae0e31cf180d5083871827d081cd0827f18f0562ea668177c8f26615856a28d505060a2b55028e0028c16506c01fc1628ec1b94697a141406e3994a828d02388e627ce16454128d9127ca327ce1384e1f1bbe16ca328fc518a22da8228a835540db82899540358784b20b61a93c1af8e112c4bd13fa51c2ad0efa513ea0d4db0d44b27c9f0d49f1644b3845911c4716bc4aa8dd5685fd2bca)

def w64 : Sig := 0x5555555555555555555555555555555555555555000000005555555500000000

def s119 := certify 243 6 ([w64,i5,i7,w13,i6,i1,i4]) cs243 [] (u243 3 81 0x8066300fc3f00bc28bb0020f4063014c0f93e451819d855624e879a2248d12425697fa1a469a6218591210441262a06c83900f420198064a31443914447604d811a06eb08392)

def s120 := certify 243 7 ([w54,i5,i7,w13,i0,i6,i1,i4]) cs243 [s91,s117,s86,s119,s108,s112] (u243 5 98 0x8b580b8002e01a2ec003cf0003cf0018c014c01745d78821860821aa8860821860821811e68a979e11cd5780580592f20a521ee0511b868b168e1e38c0ade3816ca968a968f136c9936cac1e1ddec04b17f06b021c2)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s121 := certify 243 8 ([w13,i0,i6,i1,i4,i5,i7]) cs243 [s105,s60,s110,s114,s48,s116,s92,s118,s120] (u243 6 308 0x7e9a05a8e114c3532e6981a3f4502051a3020518f3ac11979744fc63c0811b66d8c1870ca0408db5dc10238650c187e9401b1ef14bb67e28b8a1fa2800038520000f782780bf247938e104000468c000463c588b8df8b168c7800036cdb5cb9ef980001b7f80007be62e5c7e9011b93314ab71aa415103f450814708c3109330422172182061c208c027bce08c499805803e1c5949ef00200463c22e464ccc5c8c78c1e8d1840836cdb102133ac60c1b658983099d61020fd4478958c2a30a8c88ad447e8a3c2a346b410fd14e055a216885a144c8a3f483820708238415a18e065a04e011c230e118f7807002d16b45ad00fc01ef2ce0b266d9c25f6845a1169b762953310e04463d18f46b4e1c468d1a8468d1831fa2930a36c81b640db157851fa41310)

def s122 := certify 243 6 ([w39,i1,w27,i0,i7,i4,i6]) cs243 [] (u243 4 77 0x955122a27bc4124497000a0bc16002c35f89e202c0b2829214410dc430dc4310da1208621ade2988621a87910c430dc3710c4e1844013c021062a13042630426084322443)

def s123 := certify 243 7 ([w37,i1,w27,i0,i7,i4,i5,i6]) cs243 [s122] (u243 4 92 0x12aa24544f788e211c21845910941889821305f1091d124497000213c00505e0b0016b0016855fe2788260980b02ca0a485084370ac370a5ab6ac5d1748e2244c10c6014c049a87951ce1bb028)

def w65 : Sig := 0xffff3333ffff3333ffff3333ffff3333ffff2222ffff2222ffff2222ffff2222

def s124 := certify 243 6 ([w65,i4,i1,i0,i7,i5,i6]) cs243 [] (u243 3 81 0x95a24688611648a887219505142c2ca046811619c5560605cc136694445115384310f086f1bc11a18c02d080b42d8022f80082500a05401de4e42c2ca046811)

def w66 : Sig := 0xffffffffffffffff3333333333333333ffffffffffffffff2222222222222222

def s125 := certify 243 6 ([w66,i6,i1,i0,i7,i4,i5]) cs243 [] (u243 4 81 0x25182210c24f89821300213c00510200117607000e098260075059505406719c2140421c9461098c1c84221886c1701c00de37c142e8bb842318412aa08d4454150)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s126 := certify 243 7 ([w60,i1,i0,i7,i4,i5,i6]) cs243 [s124,s125,s106] (u243 5 243 0x9d10952b2289dc8912842b408213a1874e85910209ad0822b0288dc3028208e0049116124e58e1000240000bc0a4f04f08000970002ae2897b88128001e8065123111e2645112010280232313022342320300a005a01d408005a858a80a42840aa0a4204181a06722019e318202282042045398114460438838c604308810cc20c09809c21c02c01cb1c008010206f29ad1bd06b502882b211f210e71321df2104710212c2308d3022342304b300134070e770017c0704d70a98a41ad40a6b4a42642899468261a89a881ad80e73ef6)

def w67 : Sig := 0xffff0000ffff0000ffff0000ffff0000aaaa0000aaaa0000aaaa0000aaaa

def s127 := certify 243 6 ([w67,w15,i1,i0,i7,i5,i6]) cs243 [] (u243 4 81 0x955122a10c22c884a21c43a93c3a89821d5495a87530ea8ca321f87e3ad88fa91ff609824ad4d4a902489240cd826086d1b52b5709e2098262a0a4ae43af07514c53e1422bf000)

def s128 := certify 243 6 ([w28,w15,i1,w27,i0,i5,i6]) cs243 [s35,s61] (u243 4 78 0x4f7884aa9ca10c22c89821304a13c5e27882609860a42d1dc2d5455117c295052a21550509a4711cc1304a3a8e40d11c50a6a206640bd8260a817d0bb0038a)

def s129 := certify 243 7 ([w15,i1,i4,w27,i0,i7,i5,i6]) cs243 [s33,s50,s127,s128,s37,s62] (u243 4 98 0x4aa891513de2086116442506226084c8789e2098262829214dc4ff814852169aa168522d9621496a47110d109e2e28ad5133ce09a02388e6098223d447a82d15c770b78168a68206640cd826088f511ea39cd917cd9)

def s130 := certify 243 7 ([w17,i1,i6,w27,i0,i7,i4,i5]) cs243 [s42,s46] (u243 4 98 0x94188982130440ec4263040109e00282f05800b00865801ce020260980b02ca0a4853789e206f80df0148b63b8524513aa27bc47304c1701c011ea23d580dc37c13064a08f511ea39d1717d17)

def s131 := certify 243 7 ([w48,i4,w27,i0,i7,i1,i5,i6]) cs243 [] (u243 3 92 0x95a246901f07d101f07d08611648a8312c22cc22c114454e10c43c224e879a80dc37818c053080b42d8056b107d01f42c2c0de0378a0a485600bc029725c9022f80082500a0bc0e7049c17)

def w68 : Sig := 0xccccffff00000000ccccffff00000000cccceeee00000000cccceeee

def s132 := certify 243 5 ([w68,i1,i4,i0,i7,i6]) cs243 [] (u243 6 60 0x1e3d4beea80b6d0810350a80f9f1c8102120812240e09b3614d509a1090a16a210a12de721021d80102d42b50c800a0029c000028444c2)

def w69 : Sig := 0xccccffffccccffffccccffffccccffffcccceeeecccceeeecccceeeecccceeee

def s133 := certify 243 6 ([w69,i1,i4,i0,i7,i5,i6]) cs243 [s132] (u243 4 81 0x255448a84308b221288710ca4144826098a82a01f87fcb1821084c608421309224b8886884f10da36d142e8ba471122608935414318c7cb208e23842f884b55154e5800)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s134 := certify 243 7 ([w67,i4,i0,i7,i1,i5,i6]) cs243 [s133,s127] (u243 4 243 0x9d212aa0cd44e86648a88a0d44220763086a1d8b241089b109418a89b0c48750844408aec08a4c11c873302189021b10c160447a0935056a23c2b1e548524e84582d2bc770b4a1b211e37893593c3ff886208c2620ec120e261981b98c8084670dc2115506328caa05345052aa188549c290fec60fe6b31ac14d9d348924b092eb388939025b21a20f441287a278ac2a586d539636d1cba2acaf08fe20fe4f0ffe208e41096260f6c10f626096c0dc570dd073a03717c3740ae8504eaa39705396aa04f40a66791827305213852672cc739da0)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s135 := certify 243 7 ([w28,i4,w27,i0,i1,i5,i6]) cs243 [s79,s63,s128] (u243 5 234 0x1fc411479e1fde7941042744254a38a274e38a10ad02084e861d3a164408226cc31408226c209430c1ec208a90a1ee490a082108114e604511810e20e31810c2204330830260225c830d4d9425f62cd421449c822eb2c266cb2e20823c824cab0a23ec1e4a20a7a87845644787f784a040a808c564c087b08ca0cda8d885648d877d88a089a61927a151b9275455949c5fba8a0a3a4a16e8a0aa0a16d59214a134a16d440a50a49c4d134eb8e112710e1fce12e124ba409270a41ee40ae09439d4136eb94b94135272066980)

def s136 := certify 243 7 ([w56,i5,w27,i0,i7,i1,i4,i6]) cs243 [] (u243 4 92 0x955122a27bc427bc4124497000a0bc16002c0107a0b0016114452386300a6024d43ca901b86e82244688b08463559f89e202c0b06e80dd0a0a485908311052e6b9a21843510941888e7123ac)

def w70 : Sig := 0xffff0000ffff000000000000ffff0000ffff0000ffff000000000000aaaa

def s137 := certify 243 5 ([w70,i6,i5,i0,i7,i1]) cs243 [] (u243 6 60 0xf4ec6a76428430c34b21ff90f975465f3ed829f3e8119be7d2283ed5b153d8b5c852e448d88a400a588000d82b6167c01f0018080009045c8)

def w71 : Sig := 0xffffffffffffffff00000000ffffffffffffffffffffffff00000000aaaaaaaa

def s138 := certify 243 6 ([w71,i6,i5,i0,i7,i1,i4]) cs243 [s137] (u243 4 81 0x145d800c13c0022ec017c001346300a6024d43ca84310d981745df2118c2009a8252414b256944288220c99e0e451144c60e64358d7a50c230876c60762112aa08d445415a)

def w72 : Sig := 0xffffffff00000000ffffffff00000000aaaaaaaa00000000aaaaaaaa

def s139 := certify 243 6 ([w22,i6,w72,i0,i7,i1,i4]) cs243 [] (u243 4 81 0x5176002962c800c13c03180530126a1e5489be6d408621b02b026a094901bc95a510b24b591908220c980b02c1ba03742a0ad18c1dc89f1643b164476084b0a97d5106b1af4a)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s140 := certify 243 7 ([w72,i5,i0,i7,i1,i4,i6]) cs243 [s138,s139] (u243 4 243 0x9d212aa0cd44e86648a88a7004925849759c40009b001417a89b0bcbb500012800c0f581287a27b00022045760452608e43b8818c016838168a604008f4126a0ad4478563ca90a660439d5021b10c47718f4bc40e49e0e7c491012059074d408382d2906f292273406e4686e89495256829d282956a442a3a14882c908339ca4c0a581ab18447481a8ee2c918cd306b539e35e9cfd298af08fe21ce4f0bfe208e4009a0b0f7600f60b09b60dc570dd046a0372343740ae8504ead39f0539ead04fa0a67134827305213853273e4739de2)

def s141 := certify 243 6 ([w22,i6,w54,w27,i0,i1,i4]) cs243 [s89,s107] (u243 5 78 0x7e4001a00a29c000bdd0001658018c014c021ad8824ca1e4a20e3608a8822a016016d88d8818aa0a2168d077d15b56c5fa0a40a12dc768ab6ba28592846b06887082e8a)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s142 := certify 243 7 ([w54,i5,w27,i0,i1,i4,i6]) cs243 [s141,s95,s108] (u243 5 234 0x2a4411a79e2a5e79a1042744254ad0a2774d0a10a3801244584939638400026d67e5a00026c001a59a4740030f3c1efcf300001ec000af0a1efcf0a000108114e604511810e20e70818c0b0072c14c0200234821ad9a2376d9a2084758630208234823061823d824ca20a23c81e4a60a7a878457447899784a040280165756007b016a16da8d885748d88dd88a089a6191da15bc11d56d5d47477c28a0a3c4a16e8a0aa0a16d5d214a12ca16da40a68a4744b12f4c34111d13417f413011a39da12f0c1ac1a12d1d21e6982)

def s143 := certify 243 7 ([w22,i5,i6,w27,i0,i7,i1,i4]) cs243 [s86,s139,s141,s104,s90,s109] (u243 5 98 0xab8058001600bdd00013129c001658018c014c024ca1e4a236d8820e3608608218a8822a4005805b623620aa0851a8d0d5d3a507aa2816cb1a34289d2b411cadd04e8a264a1dfae84bd3a1642274a274a39cdd17cdd)

def s144 := certify 243 6 ([w58,i6,w27,i0,i7,i1,i5]) cs243 [] (u243 4 77 0x941889821316b1254b1244310d8224d43ca901b86e8694497fc491b44c13037406e850524287fe127c24892a24449127de1240c1000298c60005ea05800b5800b004922c49)

def s145 := certify 243 7 ([w41,i6,w27,i0,i7,i1,i4,i5]) cs243 [s144] (u243 4 92 0x2506226084c10c24f89821300213c00505e0b00160117600be0024e21886c10c6014c049a879520370dd02e8bbe4231840475a8982602c0b06e80dd0a0a4850e7c19f8296d5b5255448a8e7f2be4)

def w73 : Sig := 0xccccccccccccccccffffffffffffffffcccccccccccccccceeeeeeeeeeeeeeee

def s146 := certify 243 6 ([w73,i1,i6,i0,i7,i4,i5]) cs243 [] (u243 3 81 0x2a3048905920213c02881012449e02c2c01d4017a04681119505140e4211545566084391c47108e8892c218c053024e811a1745d4e820ec83b005c017a0568234e4e)

def w74 : Sig := 0xffffffff00000000ffffffffffffffffffffffff00000000ffffffffaaaaaaaa

def s147 := certify 243 6 ([w74,i5,i6,i0,i7,i1,i4]) cs243 [] (u243 4 81 0x145d8049125c00083d05800b0c6014c049a879508a2291c4488d116108c013504a482964ad28851948519052119e6348471c47108d4256842184351315050461a93c4)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s148 := certify 243 7 ([w42,i6,i0,i7,i1,i4,i5]) cs243 [s146,s147,s64] (u243 5 243 0xa90822b028a9c0c12820b408213a134e8591020a40000bc0a4f04f08001b70002ae287fbae28000e0049116124e58e10000c604308810cc20c09809c206302c01cb053008008f20932aa288fa87928828420453981144604388382a02338302e02328300e005a355801fc05b85b6e12f2235236264a523820ae0a8a888aa0a8b82155fa0651381235e38128122107129b71c626de228428212c230e73021dc2304b3001340587f5801fc0584d5aa15ea20e722a17ea205720a98a89b740a6dca8a68a89dc6e261a89a8e1b7e0e73f5e)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s149 := certify 243 8 ([w27,i0,i7,i1,i4,i5,i6]) cs243 [s65,s80,s96,s110,s55,s123,s126,s129,s130,s78,s131,s134,s135,s94,s136,s140,s142,s143,s105,s145,s148] (u243 5 308 0x989d109598ac8a989dc89198a10a39e1d10457c4779e86e1979e57c4710457f40824744e86185f4e85957c40829a608298ac0a9a15c3098a08239e1330c4744b0828360b0824744b30c57ce004949c458491fce58e57c4000476400049c2f021ee4f04f47420009a600098ab8a9a09bae98a00039e0759649c4d0008160300049c4d59657c42045604e604565c460457ce20e474c604360422043234c20c474260249dc20636040b005e5cb05349c0200988f209398aa8a988fa87998a20a39d7720860457db6354b1db6604572089a616d057dea1e16c416c416de2b5e57c4a044742a0216cc16cc16c22642474ca0c49c0a0016d616d616c01dc049d6a166076a3616c816c816f617f66048a0898a98a985ba289a698859a6986)

def w75 : Sig := 0x5555555555555555555555555555555555555555555544445555555555554444

def s150 := certify 243 5 ([w75,i7,i5,i1,i4,i6]) cs243 [] (u243 6 60 0x3cba17fd0f9a31cf9f409cf9f6828f9715c420e5d5f527cd9c01901ebd0434405b6c4081a0d40094026424fba3e0d53306190064021a0868)

def w76 : Sig := 0xffffffffffffffff0000000000000000ffffffffffffcccc

def s151 := certify 243 5 ([w76,i7,i5,i1,i4,i0]) cs243 [] (u243 6 60 0x68e44032171887cc45b56dc031e5e0c6f090b5ce912381491124528911a119122702111e3e06b804a190200905ac81d10244040866015c0870)

def w77 : Sig := 0xffffffffffffffffffffffffffffffffffffffffffffccccffffffffffffcccc

def s152 := certify 243 6 ([w77,i7,i5,i1,i4,i0,i6]) cs243 [s150,s151] (u243 4 72 0x902ac83b908238ca414483a8ebc91867154c9cb0cf6173021602f98c2d96a47110d609ec4ae148008e23b8578a629b08361a30a4079c3082cb190d304a)

def w78 : Sig := 0xffffffffffffccccffffffffffffcccc

def s153 := certify 243 6 ([w78,i7,i5,i1,i4,i0,i6]) cs243 [] (u243 3 81 0x1c47108e86541450751d41d04d867155939c33f0691a698b54e443704fc1b46d0be939381d2bc5314f083c3446f1bc2bac416706b1ac31a40cd03360a5829000742f806602b22c0c411)

def w79 : Sig := 0xffffffffffffccccffffffffffffccccffffffffffffccccffffffffffffcccc

def s154 := certify 243 5 ([w30,w54,w79,i4,i0,i6]) cs243 [] (u243 3 57 0x4c167391386541450751d41d04e5f6658d39c33f18671558b54e4043704fc2bc1d14c53495516322c1e60198306ab0d1)

def s155 := certify 243 6 ([w54,i7,w79,i1,i4,i0,i6]) cs243 [s154] (u243 4 75 0x4d15642305960ca414483a8ebc91867154c1498c149b4149939619ec2d48e2038a990fc435827b08e23b8578a629e113c8be86106c3448199031d063a30442604ea)

def s156 := certify 243 6 ([w30,i7,w79,i5,i4,i0,i6]) cs243 [s154] (u243 4 75 0x4806647108e19482890751d7924e5867b029318292e6042c0c338aa62d48e221ac13d806a6040c0afe0a629b082cb04c80bec20d8c344819902b805701e518404ea)

def s157 := certify 243 6 ([w28,i7,w79,i5,i1,i0,i6]) cs243 [] (u243 4 75 0x4a0664216ae20ca41448619c553272c33d81498c149a81498751d7922388e6106c3470a3a8e40d38578a629b082cb04ca10ec621a27b0819902fa05f409c00e04ea)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s158 := certify 243 7 ([w79,i5,i1,i4,i0,i6,i7]) cs243 [s152,s153,s155,s156,s157] (u243 4 225 0x8c838a8331c4230cc235114a30d300a4695052a81a1e30ca40e49e0e4512189c90ea1e9875e1b81eca49e98c8084671ec2115506321e64e592621f233d8660f6148522d98c3d98c2d85214d3895a9d1550b1a2b8a770b5207a4707ae270812f10d607ac0943d13d9c64fa8f82088293d540ad8290a2208e425c44248e43b88e07a1695fc0b4530f5029b0cd627a820d88619a669a33d9bf8d318a3355a2674a6283563086690351cc592318669b22804f050eea80bf0504ea208e40cc730cc839903311c33)

def s159 := certify 243 6 ([w19,i5,w43,i7,i1,i0,i6]) cs243 [] (u243 4 75 0x1201990bd210c719482890c338aa62e6042c246348c5bc8c3a8ebc0a48e23a1480f2850d4313c2be142298a6a49482c91a7810f00f44f13ca7116a47112b852000704b)

def w80 : Sig := 0x5555555555555555555555555555555555554444555544445555444455554444

def s160 := certify 243 6 ([w80,i0,i7,i1,i4,i5,i6]) cs243 [] (u243 4 81 0x4aa8915086116442510e20116e000427800aa005d1748e2244c10c6014c049aa0af13c4104411303f0fc12956e1bc8691a5502789e60982b002f02101686f054146)

def w81 : Sig := 0xffffffff00000000ffffffff00000000ffffcccc00000000ffffcccc

def s161 := certify 243 6 ([w81,i5,i7,i1,i4,i0,i6]) cs243 [] (u243 4 81 0x902ac832905120ea3af24619c55317302160208822316a47112b8520ca883d111c4770af14c5385203c88621a0421843510d635e8440d481a9a469001c0f7080ad0a5434c)

def w82 : Sig := 0xffffffffffffffff0000000000000000ffffccccffffcccc

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s162 := certify 243 6 ([w82,i7,i1,i4,i0,i5]) cs243 [] (u243 6 180 0x2c209e3e0c382c2c1c7e00b8020d0061280089021818611649a3901a41161a01904a45c0cb8c44112e203e6206884a86797828e04aa8637806e092448045ead690bd9c0a44829224705dc0a2e29c2448191220238da118718c051221c891242c90716529112210891382ae041510e11220c08301340431a0c0410106081091ea018f64241021c080240e9070716b20248583874409116040910744201057065c083221c0270)

def s163 := certify 243 6 ([w82,w43,i7,i1,i4,i0,i5]) cs243 [] (u243 4 72 0x140871098c1082208983a8ebc91867154c5cc085848c6921a213c495c2901258260b8168a629c2901e4451c5826088288ca4238b5238847103381047)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s164 := certify 243 7 ([w43,i7,i1,i4,i0,i5,i6]) cs243 [s159,s33,s160,s66,s152,s161,s162,s163] (u243 5 225 0xff104432407dcb2404107d5e57711c4107d10411c7d11f408213a1874e859102089b082430409bc08740208d508212cc30b130c12c209e186513811ee0511061021841312104248230631c4875b861d5c19cb924989186b2019cad8055b06188f18b9428408fa085406409949216c6187718616d248e70b5117b10e1f4e11c124710d097b0a417c4f09c094712b42e414b9441c41bb394012c10e624e107d10eb0e32a302b0232c302a8272a72eb2c72c14eea85342c414a9442a414b0796e4e920ff364a)

def s165 := certify 243 5 ([w54,w19,w30,w15,i0,i6]) cs243 [] (u243 4 60 0xe211c480b241948289246348c338aa61d475e0525cc085810bd205684143a003815c03d80f2a540cd2d48e26b8298a62109f0)

def s166 := certify 243 6 ([w19,i5,w30,i7,w15,i0,i6]) cs243 [s165] (u243 4 78 0x900cc8e211c329051248c6917302160619c55318b7918751d781490bd205700ae03ca105087a2787a2794e00702b524a4164827c05f8286a189e6688b52388d4c0818143c14c53)

def w83 : Sig := 0x5555555555555555555555555555555544444444444444444444444444444444

def s167 := certify 243 6 ([w83,i0,i7,w15,i4,i5,i6]) cs243 [] (u243 4 78 0x955122a10c22c884a0c445a91c4434427880d4a88150ba2e902b2244c1126a82bc4f10411044c14cc29ca46348691a5502789e6098213453284534202d0de0a82855)

def s168 := certify 243 6 ([w54,i5,w30,w15,i4,i0,i6]) cs243 [s154,s165] (u243 4 78 0xe211c4806a419482890751d792918d230ce2a98d2918b9810b02d48e2002de0a629f0311df8d4c0818103320568405ba58d6317c2b805701e54a819a1a903526831d10e2)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s169 := certify 243 7 ([w30,i7,w15,i4,i0,i5,i6]) cs243 [s156,s166,s50,s167,s38,s168] (u243 5 234 0x3fc4110c901f72c901041f4e3ac1041f4412c38ed02084e861d3a16440823fc2090c103570c10082b0208cd30cb0c30cd0827861944e047b81444184086104c484109208c18c7121d4d71875706717b49236524aa1862c461aa49223c62e50a1023e821501902b461ac80672660156c18639c2d445ec4387d38470491c43425ec2907713c27026ec5700b371a940ff40b33fc8141c42c396c135c72c70531357b14c4a84c8d9c841f44caaa8ca8c08d908c17cc0aa090990366aa90a903fe61e6c988136a22caac3fe698ff15ca)

def w84 : Sig := 0xffffffffffffffffffffffffffffffffffffffffffff0000ffffffffffff0000

def s170 := certify 243 6 ([w84,i7,i5,w15,i1,i0,i6]) cs243 [] (u243 4 75 0x942ac842d5c419482890c338aa6918d2316f231a81498751d789f91c47214350c4f0c54751c81a70a114c53217a40bc4f0f44f29e9aa6800e0ae92905922534d504a)

def s171 := certify 243 6 ([w54,i7,w19,w15,i1,i0,i6]) cs243 [s165] (u243 4 78 0x268ab21125164832905121867154d231a43a8ebc0a4da0a4c62de462388e470a114c5328742fe94350c4f4f485e9033003818aa6a990fa13c3d13ca72d48e27031d704213f8a)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s172 := certify 243 7 ([w19,i5,w15,i1,i0,i6,i7]) cs243 [s170,s171,s159,s166] (u243 5 234 0x8841c4ac8718b288a10a2861a50a0692a82901907861944e047b814441844f4618a180671ee0154a118636524bc1861ec61bc4923346184f48b71ed2484f1867281d53f1875706713fa2840a140a4f4a40ad40a284a10a110e4f4e107310e284e9ec4d204f335434f4a150c4f2844f334cd335c37dc15ca1285c2845315d3d14d0f1028d929026502bc28431c4cbc2f44f04c8c7c84f12c4f367cf04ff04f3344b29dc12c015fc01cf1c3344b12da13d2928cd29a1dda284f2b413d2510cd1341cc59104f10cd134251c4aca37ca505f50a70a39c2d4437c43873384704)

def w85 : Sig := 0xffffffff00000000ffffffff00000000ffff000000000000ffff0000

def s173 := certify 243 6 ([w85,i5,i7,w15,i1,i0,i6]) cs243 [] (u243 4 78 0x250ab20ca41448619c55348c691a81498411044c2388e428ea3903460982217a40be9aa6995130421843510d635e845a91c41d475e4857e0a629801c0f54aa704f)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s174 := certify 243 7 ([w28,i7,w15,i1,i0,i5,i6]) cs243 [s157,s128,s36,s67,s170,s173] (u243 5 234 0x3fc4114c941f72c941041f4411c38b51f4e39c104d02084e861d3a164408226c2094c1426f021d4082354209c910d2c6413dc0827861944e047b81444184086104c484109208c18c62461ac80672b60156c18636524ae18626461ae4923fc6194a141de8a141867121d53f1875706713f49212c10e624e107d10eb0e30df302b0232c30262426e44d2081b14750ff51c813fc8152c51c3a5c15ecb1cb05315d8914c4b84c8d9c841f44caeb8cb8c08d908c17cc0ae094994366eb94b943fe62edc98015ee01cb9c3fe698ff134a)

def w86 : Sig := 0x3333333333333333333333333333333333333333000000003333333300000000

def s175 := certify 243 6 ([w86,i5,i7,w15,i4,i0,i6]) cs243 [] (u243 4 81 0x902ac832905122328c8a72918d22e6042c139619ec7fc8fa90095c147821ac50d82288a40cc6f1be1a10c43661840d58c8698169035248d231422985a2989a16a10a56a02105ac)

def s176 := certify 243 7 ([w54,i5,i7,w15,i1,i4,i0,i6]) cs243 [s152,s155,s175,s168,s170,s171] (u243 5 98 0x11a2ac4134d04194414441d4757121867154648619219aa061924861924862d4438401c689b71cc0d571c134b170438439cb05322c68ad68cdb2cc099b2c15c4c84c89b689b684bc077c0f13645f364ad04d046b021c2)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s177 := certify 243 8 ([w15,i1,i4,i0,i5,i6,i7]) cs243 [s158,s164,s169,s172,s174,s39,s68,s129,s176] (u243 6 308 0x7fa209c19b14cb87c44c911fe2820a3fcd02d4668a61a99734c0d1fe2810266da02046684758393475619b080811fe283684fc828d0bc8a5028ff20188336783644fc23809f0f38a0cd840c10cd041a027e30940f4089023346061930e12e9313f0dd261c0c7264c244ab560c1ab2c419ab2ee82a56581831b26c92249fda0c18d93543064fed12247f943895cc153054c2858943fc51c14cd8e385acc093024c1df0733610e0433521c436602980a6242b6719a08e029932b003fc82c21585561558813240ff14b0533611604ac3ab0eac13e0466c72c1c668c33465604b015618b0619a08cd0530e4c3932b2c593264ca53264c107f904c40d9146c8a364876207f8a4c299b091821b2c8d9646c84f8119b6519919a3250c36411b208d91978619a0a502)

def w87 : Sig := 0xffff0000ffff0000ffff0000ffff0000ffff0000cccc0000ffff0000cccc

def s178 := certify 243 6 ([w87,i4,i7,i1,i5,i0,i6]) cs243 [] (u243 4 81 0x12055906520a244e5867b0c338aa62e6042c03f0fc12610596321a611c47308361a30a407918c0168049125c0032a12806d1b6802388e91a46109812a02d405aa5429c)

def w88 : Sig := 0xffffffffffffffffffffffffffffffffffffffffccccccccffffffffcccccccc

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s179 := certify 243 7 ([w88,i7,i1,i5,i0,i4,i6]) cs243 [s152,s178] (u243 4 225 0x5490900ce05486655c0841cdce11c841cc8411dce7004925849759c40002500181eb0250f44f60004b80100be04b85e40c0001dc001379c17f9c13400f186520724f0722890c40483fb183f018169490f3272c9310f919ec3314d3190108424684210a0c623cc5cc029811e1490b03408d3185b08421234210845b3183563089090351cc352319a632018c3418ea0c63aa72888823909711092390ee23800b41c0b780401815b031421886062159a30443415ea015c3481e5d33c7079a3ea)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s180 := certify 243 6 ([w54,w30,w16,i0,i4,i6]) cs243 [s154] (u243 4 180 0x212e7208442484439c39908c0d583986a1ab08c7004925849759c40011f00163e705fe71630002d0011ce05bce200009400607ac0943d13d80078c329039278391448620241fd8c1f80c0b4a48f98cb18421091a10842b198c4698c8084212342108506321e64e592621f233d86611632391f7107323963720274096b1e10b1a0f309c87604e215d631316361e6138f2c12d42ba14c4312112cd1)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s181 := certify 243 7 ([w30,i7,w16,i5,i0,i4,i6]) cs243 [s180,s156] (u243 5 234 0x3cc4110c901cf2c90104424e388104424410838e3801244584939638400090000cf0c93c13cc00047c002a71c1ddc72a00025c0010b9025ee2050000b0000871cb1c7080007861944e047b81444184012f961be00601649243c64e4c48c43d233cc18c47c61aa820236082a18623c62e50a1023e8215019023461888202360808186d0c3044844d073d0430c7545708f330c40f341213cc5f40c308394812cc30830c12d213444a84391f3841cc43aa39099047eaa90a903ce61e4898812ea608a883ce698f315ca)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s182 := certify 243 7 ([w54,i7,w16,i1,i0,i4,i6]) cs243 [s180,s155] (u243 5 234 0x2a4411ac9a2a722ada1041cc410cd0c1cf4d0c10c3801244584939638400047c003071c1ddc73000026c001ab9a26ee2eda00090000cf0c93c13cc0007861944e047b81444184012f961be0060164925346188820236080818647c61b082023608301863cc619aa1a2368a1a18643c64e4c48c43d233cc18c10810e424e110910e20e708700b0072c70020074c4b60f320868f39e54d3cc5f68820c3c4c15c820c20c15d4d3444c04391f3841cc43b039a99a47f0c1ac1a3ce621cc98215f008cc0c3ce698f312ca)

def s183 := certify 243 7 ([w28,i4,i7,w16,i1,i5,i0,i6]) cs243 [s157,s152] (u243 5 98 0x114c8410e384194414444e4c33cc1a08061a0806194a06486192486192304d0c08c509b30c92430438438c20d160975097508b2c208b2c2043843897509750e947c7747ca38438490c90cb84d17ee52e2040)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s184 := certify 243 8 ([w16,i1,i5,i0,i4,i6,i7]) cs243 [s179,s181,s182,s158,s183] (u243 4 308 0x7984641c59d5066388e611866119e6a228f3a006d7454178da58d02fa1e6a0019d700497449612473759cce900012c250004b607ac12c250f44f12d80023e8f800e889bce23e56f38e889a001e6a30d30fc0291a48d5052a3ce06833be30cb0f903920e7e0e4516748623a20907f0fd8c1f8f60301d1b4a425a1e64e44b649825a1f233c4b61982b8ae630ae80842115c8d0842115d06323e8f98d0f8b6108428f91a108430f8b6631e7a6304b5096a12f44ce8f35314ce86ac6096412c82586a3986ace918c12c4b15c479c11015d42ba85780ef03cd48533a4410577212e15c884919d721ce8f11c15c0168057e05bc744080096c12d8258ae8409625896688962589783ce013c11f523ea47e02fc0f3504ea674823911f723ee47c839919d708ee)

def w89 : Sig := 0x5555555555555555555555555555555555555555555555554444444444444444

def s185 := certify 243 6 ([w89,i0,i7,i1,i6,i4,i5]) cs243 [] (u243 4 81 0x86127c42518220084f0008b32c0051020255411a889130431805300ba2e90c924d505082208981f87e09789e218670dcc348d2a8304c15816013c4f21180de0a82821)

def w90 : Sig := 0xffffffffffffffffffffffffffffffffffffffffffffffffcccccccccccccccc

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s186 := certify 243 7 ([w90,i7,i1,i6,i0,i4,i5]) cs243 [s42,s185] (u243 5 225 0x11108213a1073eba10208a908243040a9c0c1402087308212cc307330c12c20a40000bc0a4f04f080010b000116110b58cb100009700042e4097b881400007d000135c707d71c1340002184131210424823063004be586f8018059249e186513811ee051106136186620836820606188f18b9428408fa085406407718616e0805f82016c61a2104432422ca240411d9394e3183024242310930260271870053c0707d70060012a132618118132a8c9418422aa242a422607975ceb20f545ca)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s187 := certify 243 6 ([w35,w30,w17,i0,i4,i5]) cs243 [s44] (u243 4 180 0x1171095563073631551090910b0c6212c660421cc42207641cc3b0ec82104a00083d104a1e89e20011700155e707de71550007d0031ce0fbce600042c00258885d8cb200023082c908229098660241fd8c1f80c0b4a48b98caa842108be10842aa98c1b98d8084210dc2108706378c329039278391448626027408eaaa30aae0f509c91204e415d557115521ea138f2411d42be144c111111cc9)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s188 := certify 243 7 ([w30,i7,w17,i6,i0,i4,i5]) cs243 [s187,s47] (u243 5 234 0x4442084e841cfae8408245c20aa30c1ccc32a0823d42090c101cf0c10082424209830c424c318082900002f0293c13c200042c000458442d632c400045c002a71c1f5c72a00025c0010b9025ee20500001f4001871c1f5c718000086104c484109208c18c012f961be0060164927861944e047b8144418445c61aa8201de082a18623c62e50a1023e82150190d86198820da08181867645738f510440f541113d45f404118395811c411810411d11325099045eaa90a903d661e5898811ea218a983d6698f515ca)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s189 := certify 243 7 ([w35,i7,w17,i1,i0,i4,i5]) cs243 [s187,s45] (u243 5 234 0x45c20b230c1ccc3320822a420a2c222a7030620821cc2084e841cfae84082900002f0293c13c200045c003271c1f5c7320003d40022ba21f6eba200042c000458442d632c4000086104c484109208c18c012f961be006016492d86198820da081818645c61b28201de083218627461a2a2227682fe21867861944e047b814441843183024242310930260271870053c0707d70060075c4720f561888f595d4f3d45f8986043ac415d860460415d4f32629a245f2ca2ca23d66244498415f2384c843d6698f511ca)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s190 := certify 243 8 ([w17,i1,i6,i0,i4,i5,i7]) cs243 [s186,s188,s189,s48,s130] (u243 4 308 0x3d7421addb5062358e7a0c747aa84211c47108472076411c730ec3b11c82122e8b884ed896c622e39b18ed896211eb400daf8a82f1b47da05f43d54003b612800f8883d10e61287a27bb620004742c0011c96208e85d8cb11c80022e8b800f889bce22e3ef38f889a001eaa30d2fdc0291a4b15052a3d60683b623082fdb24208e62909db6198f88241fbf76307e3e80c07c6d2908fe30ca239039208fe0e45111c8620ae1b98c2be021084570dc2108457c18c8ba2e633f62d84210a2e5684210bf62d98c7a8464208ea11d4238464c8467aa88a11c4715dc7ac31015d42ba85780ef03d55853b6cc30571212215d884b1db1604f8f31c15c02b8057e0fbc7c418008e411c8238af8c08e2388e6488e2388e83d6013c117522ea45e02fc0f5504ea)

def s191 := certify 243 6 ([w39,i0,w30,i1,i7,i4,i6]) cs243 [] (u243 4 77 0x2403323884709224b80081020073801ac8e23b80e020158f221882b68a220882cf804110604288220842108822084210882270c22009e0108318084c6084c6098208841)

def s192 := certify 243 7 ([w37,i0,w30,i1,i7,i4,i5,i6]) cs243 [s191] (u243 4 92 0x2403323884738847086116442806221318217c4248449125c00084f002040801ce02c005955c91c47304c1701c0402b1e4376b5ad194828904c13003a82c5cc085805210842149ca10b1e6)

def w91 : Sig := 0xffff5555ffff5555ffff5555ffff5555ffff4444ffff4444ffff4444ffff4444

def s193 := certify 243 6 ([w91,i4,i0,i1,i7,i5,i6]) cs243 [] (u243 4 81 0x255448a84308b221288710ba2e91c44898224d50506e1694250a101686fe278820882260d234aa0619c5530ea3a9a5231a45a91c4434427892b551402789e6098282a0a)

def w92 : Sig := 0xffffffffffffffff5555555555555555ffffffffffffffff4444444444444444

def s194 := certify 243 6 ([w92,i6,i0,i1,i7,i4,i5]) cs243 [] (u243 4 81 0x2518221103b1098c100427800a204002196005ac02244c10c6014c049aa0a260864a118964411044c0fc3f048691a55030ce52986520724307210988a08d5e82a0a)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s195 := certify 243 7 ([w83,i0,i1,i7,i4,i5,i6]) cs243 [s193,s194,s167] (u243 5 243 0x9d10952b2289dc8912842b408213a1874e85910209ab0822b0288dc3028208e0049116124e58e1000240000bc0a4f04f08000970002ae2897b881280004a85d3b61744d843aa38cd8890a2508c234c0b609cd863022501c26453036010d8932aa290a902b629e19e13811ee1e106102184131210424823063004be586f8018059248a186941ab1a4a6aca406436186aa2519f68976a8618411c478e57841dc4784778c12cc088d08c234c084b0ae136e00e502e17ee004d01099029ab2906ad02a62aa9948da622a9aad9abd8e53ee0)

def s196 := certify 243 6 ([w82,i4,w30,i1,i7,i0,i5]) cs243 [] (u243 4 77 0xa018884c608411044c2e6042c0c10842630421099a312601124716098280563c88bc127824892b589e248930204491279c125826088288ca4206702388473884700492d449)

def s197 := certify 243 7 ([w43,i4,w30,i1,i7,i0,i5,i6]) cs243 [s196] (u243 4 92 0x4806647108e17c844444308b22140311098c1098c10ca4144820882261730216060842131821084c3a8ebc948c6952bb2388e6098280563c85bc0bf815b72dc96a47110d109e24ae040c0e5e2f60)

def w93 : Sig := 0xaaaaffffaaaaffffaaaaffffaaaaffffaaaaeeeeaaaaeeeeaaaaeeeeaaaaeeee

def s198 := certify 243 6 ([w93,i0,i4,i1,i7,i5,i6]) cs243 [] (u243 3 81 0x256891a21845922a21c85d17538892c224e811a18c053012449e00209406d1b415019505142c2ca0468110dc2d2942d01d401764e4e2094825a056815880dc2d005c017)

def w94 : Sig := 0xffffffff0000ffffffffffff0000ffffffffffff0000ccccffffffff0000cccc

def s199 := certify 243 6 ([w94,i5,i4,i1,i7,i0,i6]) cs243 [] (u243 4 81 0x240ab20ca414485cc08581867154c1f87e09272c33d86948c4711d0a407918c050818861a384227d124497006d1b6800303d0003de01840d58c869822388e52a14)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s200 := certify 243 7 ([w44,i4,i1,i7,i0,i5,i6]) cs243 [s198,s199,s69] (u243 5 243 0x1bb104432407dcb240413408213a1874e859102089b082430409bc08740209e186513811ee05110610218413121042482306308f18b9428408fa0854064237186b2019c998055b061804be586f80180592484b043a373841f443ac38ca8c0ac08cb0c0aa090b1052a510a9052c1e57ba86302c0237b2c02a00e0049116124e58e1000240000bc0a4f24080014006d41bb1b546ed440000411c4387d3841f44384738c12cc08e508c1dcc084b0a816e818e51a817e8185b19098a51bb2906ed052652a9fc8b2622a9aab1bbb0e53fdc)

def w95 : Sig := 0xffffffff00000000ffffffff00000000cccccccc00000000cccccccc

def s201 := certify 243 6 ([w95,w19,i4,i1,i7,i0,i6]) cs243 [] (u243 4 81 0x12055906520a242e6042c0c4184268ccc6a044110441491c420e094c0794106a1a86218864189c471129834f0008617086b1ad29111c470426084ca54129c106129062789e1294e268982)

def s202 := certify 243 6 ([w54,w19,i4,w30,i1,i0,i6]) cs243 [s154,s165] (u243 5 78 0x38410e1101644194414441a08061a0806486192a061a82e50215010e10e22af077f16358c5fa90a901e4a29012ce10e115354c8768091013d03843846b068c1082910)

def s203 := certify 243 7 ([w19,i4,i5,w30,i1,i7,i0,i6]) cs243 [s152,s159,s201,s202,s156,s166] (u243 5 98 0x110c8438410e194414442e5021501a08061a080618b7486486192a061a8284384390a8792244f64aaaf0d5f2a15cb1a925105912440ad409992412c238438425d025d0f04d1dfc93c13c038438425d025d0394df17cdf)

def s204 := certify 243 7 ([w88,i5,w30,i1,i7,i0,i4,i6]) cs243 [] (u243 4 92 0x900cc8e211ce211c24892e002040801ce000c13c00e700329051207e1f8245cc08581821084c6084213272c33d860842136abd2388ee038080563ca1818b02b74dd361035632018b0e562422)

def w96 : Sig := 0xffff0000ffffffff0000000000000000ffff0000ffffcccc

def s205 := certify 243 5 ([w96,i4,i5,i1,i7,i0]) cs243 [] (u243 6 60 0x797831bc171887cc4810010668e44032227021121424912248a51356a35c2470292242d692404a19020ae04380e88122040430100905ac8)

def w97 : Sig := 0xffff0000ffffffffffff0000ffffffffffff0000ffffccccffff0000ffffcccc

def s206 := certify 243 6 ([w97,i4,i5,i1,i7,i0,i6]) cs243 [s205] (u243 4 81 0x240ab20ca414485cc08581867154c20882230ea3af25231a44711d0a407910c430945c0b45314d01685a810c22c886b1af422d48e22570a410d104a20105f208ea5434128982)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s207 := certify 243 7 ([w95,i5,i1,i7,i0,i4,i6]) cs243 [s206,s201] (u243 4 243 0xa9212019c0a90ccab8108e00924b092eb3880012e00402f812e1790300012100041e88770f4a71001e30ca40e49e0e45121880907f6307e0302d2911e62e6014c08f0a48581a14298c8084212342108506308c20ceb21045212426311047212e22124721dc47001683816f00804110d057a80570d20794842b10c4810e85420415883510881d8c21a8762c9042d086b83aa35e9d5d4042208e470e6e20e64708eee09bc01ca0e0bfc009a00845b084c4698212342130b66804ead3aaa83ab0d04fa0ae83c202740561385687550729e6c)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s208 := certify 243 7 ([w54,i5,w30,i1,i0,i4,i6]) cs243 [s180,s168,s202] (u243 5 234 0x2a4e39a1042a4411a38e1cc4110d101cf4d101043801244584939638400026c001a71c26dc71a0004840030f3c267cf3000025c0010f1025fc20500007861944e047b81444184012f961be00601649253461aa820236082a186234619a820236081a18648461b049223524b018623c62e5049023d2215019012a10e534e107310ea8e72a70053407077700a809a62121a963c12158d4d4845fc2aa903c5015eaa90a9015d4d1e5012ca15da2906904844b12f4c3411211341cf413011a395a12f0c1ac1a12d2121e6982)

def s209 := certify 243 7 ([w90,i6,w30,i1,i7,i0,i4,i5]) cs243 [] (u243 4 92 0x500c4426304220762131820084f002040801ce000432c00e700208822607e1f8245cc08581821084c60842130ca4144860842130475fb04c1701c0402b1e7040cc815baeeb9201990e52222e)

def w98 : Sig := 0xaaaaaaaa00000000ffffffff00000000aaaaaaaa00000000eeeeeeee

def s210 := certify 243 5 ([w98,i0,i6,i1,i7,i4]) cs243 [] (u243 6 60 0xf0ea69f54890380425be94285a88428510f42e1a97dd5019f010206a1502042a90202da7a0009c00102d42b5028444c2043b0021900140)

def w99 : Sig := 0xaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaaeeeeeeeeeeeeeeee

def s211 := certify 243 6 ([w99,i0,i6,i1,i7,i4,i5]) cs243 [s210] (u243 4 81 0x128c11086116440109e002881009224b8044898218c029809354142288be70e238846a1304c00ea0b2a0a806e108aa2a8ca32f9c610be212c160595450468406f8f3884)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s212 := certify 243 7 ([w63,i6,i1,i7,i0,i4,i5]) cs243 [s211,s115] (u243 5 243 0xa908243040a9c0c14020b40823ba1874e8593820a40000bc0a4f04f080009700042e4097b88140000e0049a2d6124e58e4440002184131210424823063004be586f80180592488f18b9428408fa08540643618662083682060619111863b83877e0a338618c60c090908c424c09809c61c028901c1f5c0180106108aa890a908981e511a845398116896183aa3a2387141d91c62766240e40c12cc087308c1ccc084b09c135c007d01c1f5c004d02016e018e51a017e0185b19098a89d929076508a68aaa1c862622a9aa61d960e53d44)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s213 := certify 243 7 ([w35,i6,w30,i1,i0,i4,i5]) cs243 [s187,s111,s70] (u243 5 234 0x2a420a230c2a4c32208244420b2eba1cfaeb20821cc2090e901cfae90082900002f0293c13c20001f4002271c1f5c72200044400325961f565b200025c001059025d62050000086104c484109208c18c012f961be00601649253c61aa820266082a18627461a2820276082218644461b2e381df8e3218623c62e50e1023f8215019032a30253c23073302a8272a70053c0707d700a809a62111a955c9115554f4445fcaaa903ad015eaa90a9015d4f1e5011ca15e22908904444711e2396211f2ca2ca211d112466984)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s214 := certify 243 8 ([w30,i1,i7,i0,i4,i5,i6]) cs243 [s169,s181,s188,s55,s192,s195,s71,s82,s116,s164,s197,s200,s203,s179,s204,s207,s208,s186,s209,s212,s213] (u243 5 308 0x9a6104990c909a1dcb29901043961b38e44447104866171044444738e44740824844e8611cf4e85944440829a6082990c109a15c30990082396130824844b30c8360b30c4844b082444e00495ec458491f4e58e444400048640005ec2f028264f04f48420009897000990b909897b881990000396070005ec4d71c8160371c5ec4d000445e186563c4e0465dee05144441844842184163cc48412342482484c18c5ec04be63d61be5e401805ed6492988f18b9990a10988fa08599019015c5718615ea82015d7782015ea186394d518663c5b8202c4ad82063c5b1869a615ca4444a8415ce15ce15c42644444ea8e484ca8c15c215c215cc1dcc4842a825edca9c15c015c015dc17dc5ec0a809909909857aaa9a698799a6988)

def w100 : Sig := 0x5555555555555555555555555555555555555555555555555555555555550000

def s215 := certify 243 5 ([w100,i7,i6,i4,i5,i1]) cs243 [] (u243 6 60 0x6ce03e701757c8cbe5c571c839ebd0a4e880b6d8810341a80fa04e7cf9a31cf9f6828f9e5d08b406a99830c805bc024f833e081076421a0a68)

def w101 : Sig := 0x3333333333333333333333333333333333333333333333333333333333330000

def s216 := certify 243 5 ([w101,i7,i6,i4,i5,i0]) cs243 [] (u243 6 60 0x36709fd84baaeb8892e310f988f5ee62f7428962142dc6a12df0a74269620e88f4ee29ba26e45103540d9814220e1000057e21d1074415b8a6e)

def w102 : Sig := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000

def s217 := certify 243 6 ([w102,i7,i6,i4,i5,i0,i1]) cs243 [s215,s216] (u243 4 72 0x4190612e105794284edc64b8c3a16741dd0815cc338aa6316f2348c6919c5198d42fcc2f98c2da4ae165c94d354104a9889e27b8bd71974d508103a811b88a)

def w103 : Sig := 0xffffffffffffffffffffffffffff0000

def s218 := certify 243 6 ([w103,i7,i6,i4,i5,i0,i1]) cs243 [] (u243 5 81 0x8320e46082bca1213b38c9386f1bd028619c551862dd219218648638a318691a4a41253859386b1af02a44c44f13ce2f4e32c6d1b6e28711c72288a88a86a06a020a4c00016b8410ec94)

def w104 : Sig := 0xffffffffffffffffffffffffffff0000ffffffffffffffffffffffffffff0000

def s219 := certify 243 5 ([w28,w35,w104,i5,i0,i1]) cs243 [] (u243 3 57 0x8320c2506653885953be327a0af286186715598b704da4b66595b8a3604d98132497859e4c42513c4f44e2040017246ab8cb)

def s220 := certify 243 6 ([w35,i7,w104,i4,i5,i0,i1]) cs243 [s219] (u243 5 75 0x8320e46082bca122a208a888aa213b38c938619c551862dd21921864a8186a0688bf18638a3182917d2ae4494e164e913113c4f016a345f58e2f4e32e2ca2244410e98a)

def s221 := certify 243 6 ([w28,i7,w104,i6,i5,i0,i1]) cs243 [s219] (u243 4 75 0x1064184b84edc64b82b4202b30e859d1057942830ce2a98c5bc8c6714660a4c60a4d40a4d231a492b859709a7a10f44c42513c4f23a82fb8bd738cba05f420400b04ea)

def s222 := certify 243 6 ([w54,i7,w104,i6,i4,i0,i1]) cs243 [] (u243 5 75 0x82bca1213b38c93aa208a886aa208320e460619c5519218648638a31a8186a066a81862dd218e2f4e32c054d5321da913113c4f10e68ab38e4945939ac1a9820a498a)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s223 := certify 243 7 ([w104,i6,i4,i5,i0,i1,i7]) cs243 [s217,s218,s220,s221,s222] (u243 5 225 0x10206f2aa1bd0a902882a46083e8820e4224e9861372085ac2bc73b0a1588210b213b398390b60c93883873aaa15c8207320815eaa8a18694281a4aa0a40643618622019f680552061ba1869122dfa4929061905492586190518659248c71863b8387fe0a3386187fa2816c6187f18616e8a1a912929bd29a2c5a2a42b491253ba3b4e8593a43a9148c251650a4dca50ad50a58a91693af13193c13fa584f38c7393758bd39638c731ccba3cdd02238e28c72a2266228e28c737c452650a1dca505f50a98a)

def s224 := certify 243 6 ([w22,i6,w84,i7,i4,i0,i1]) cs243 [] (u243 4 75 0x1057942830e859d308461071e104190612856619c55348c691a814995731941325a5198c5bc8d4d50810296a58b21784a5389e27a9c7a15740ec591649f22534d504209447)

def w105 : Sig := 0x5555555555555555555555555555555555555555555500005555555555550000

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s225 := certify 243 6 ([w105,i7,i4,i5,i1,i6]) cs243 [] (u243 6 180 0x47211e5d0cb4472c97fd01340411107188810c041c20727261b38022027221f3806207410babe58fba2c465f087c5c887af42ad05caa527408d0d204008abadad157b012040350206861a0d3035a20401cf9f04a4da31d498e08f9f247cfa03c8091e4e80f9f147cfb42ed051714d0f9f0e0c182380839c0e08182080c18c20a82106630183240c320128090916f00340784893e0cf9e060cf893e281886851a0a2829a0368)

def s226 := certify 243 6 ([w105,w84,i7,i4,i5,i1,i6]) cs243 [] (u243 4 72 0x942ac8473882288a471064184b8415e50a0c3a1674c211849482c9129a6a820b88e204a1e89e27d3542043f1a4c4710c2a8ce6348b7348c691829a185b)

def w106 : Sig := 0x3333333333333333333333333333333333333333333300003333333333330000

def s227 := certify 243 6 ([w106,i1,i7,i4,i5,i0,i6]) cs243 [] (u243 4 81 0x4815641948289139619ec1d475e48b9810b030421099841658c86985a91c4435827b12b85202288a4708621b30318c7cc0de37c28e23886084c1088418b0000f78a55208)

def w107 : Sig := 0xffffffffffffffff0000000000000000ffffffffffff0000

def s228 := certify 243 6 ([w107,i6,i7,i4,i5,i0,i1]) cs243 [] (u243 4 81 0x20c83097082bca1418742ce82288a441867154c62de46918d2350bf30ca4144894d354184610ec812a622789f4d508112449b10711c42322308c183930722104a1d80017d94aa046e)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s229 := certify 243 7 ([w84,i7,i4,i5,i0,i1,i6]) cs243 [s224,s225,s226,s152,s227,s170,s217,s228] (u243 5 225 0xa910453250a9c8ab504117910411ce397738e11c4104204539811446043883a46083c0820e4224c186185208f2c2bcd5b0a1f08209720c352a5097a8b350850b161815c820ad20815d861e186513811ee05110613618622019f6805520619691869122dc7b4929061985492f06187b186f124901186528507ba28506187b2647716c6187b18616c7b16f49125116913417c5912411a912953051ac1a52451c13a423ae384f043bc384b8492e930f3c93c13f0b84f53c51ab9a52e51af0816fcf1010137ca)

def s230 := certify 243 5 ([w35,w22,w28,w19,i0,i1]) cs243 [] (u243 5 60 0x60821820af284820c8392a30d42cd41867154655c61a848619218b748619428c600029e208292e53a508128a50c78a413c4f1041654)

def s231 := certify 243 6 ([w22,i6,w28,i7,w19,i0,i1]) cs243 [s230] (u243 5 78 0x60821830d42cd420af284820e360820c8392a1867154655c61a8194a06486192192d28c618b748652e508100029fa167a1649f08292e2859505f514b52c5931c469d421d429e413c4f)

def w108 : Sig := 0x3333333333333333333333333333333333330000333300003333000033330000

def s232 := certify 243 6 ([w108,i1,i7,w19,i5,i0,i6]) cs243 [] (u243 4 78 0x12019906520a24316f230ea3af0292e6042c0c10842649482c904d3c087816a47112b85202288a4709e813f0318c7cc0de37c28e23886084c108962794e278001ef14aa40a1)

def s233 := certify 243 6 ([w35,i6,w28,w19,i5,i0,i1]) cs243 [s219,s230] (u243 5 78 0x20c8391860821820af284821860830d42cd41867154618b7486a061a84861921b8e06194e060bc904f13e4c87791a7508750003c89655945fb94b94204a29431e2ca22444)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s234 := certify 243 7 ([w28,i7,w19,i5,i0,i1,i6]) cs243 [s221,s231,s159,s232,s157,s233] (u243 5 234 0x4044114c943572c94104f0410c738ef0e38c7104108114e604511810e20e91820cd92083908916961837d862e2082c4822e61825c830d4a9425ea2cd42142b4823cb0af266c287c2087861944e047b81444184d861888067da015481865a461a448b71ed24a418637e8a2e1861ec61aea284046194a141ee8a141861ed24bc1861ec61bc492d2449445a44d07716449047044d08bb91a7510150bb4048752453c3a7c12e493c904f12d6913ceb8e10df10e17ce12e11499437eeb94b944066207c98012ee03cbbc40669901134a)

def s235 := certify 243 6 ([w61,i7,i6,w19,i4,i0,i1]) cs243 [] (u243 5 75 0x82bca121820860838d82086aa208320e44f4619c551921864957186a064b4a318668bf1862dd218052d4b167254d5321da90a713c4f167a1649f6a26a2082904d585a89a10a)

def s236 := certify 243 6 ([w35,i7,w22,w19,i4,i0,i1]) cs243 [s230] (u243 5 78 0x20af284860821820c8392a222a8820e36081867154648619255c61a818b74861a22fc6192d28c602429c4f13ca7885f894b52c594dc20a4c97d5f4ab8859e85927e4ca2904105990a)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s237 := certify 243 7 ([w22,i6,w19,i4,i0,i1,i7]) cs243 [s235,s236,s224,s231] (u243 5 234 0x4081bcaa86f42a40a20a4dc820a7b0af1cec284a720837d863a2081cc823a61831c8205960e31cd8605920892a20d3d2083908913daaa2861a50a0692a8290190d861888067da015481864dd248a71861fc618a7492ea855d41186e861941a2831c61859e12d1ff828c5918637461a448b71fd24a418650a750a4dca50ad50a29caa3c4b005931d4b4dca752c5929c5931cc731e43764134a729e429c4f1353713d4e9428df29426542ba285911c5937fae859e85931c4727e411c2137a0a4ea431c4711e21656128c72a21de2285928c712c46a44a4a374a685f68a90a)

def w109 : Sig := 0xffffffffffffffff0000000000000000ffffffff00000000

def s238 := certify 243 6 ([w109,i6,i7,w19,i4,i0,i1]) cs243 [] (u243 4 78 0x415e50a3084611a0ad02288a471867154d231a4ab98c149b45f986520a2402a6a990fa711c4d047a08c61185c41c47108c84190612e0b7348c2684a2789e2104a1da95a09459)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s239 := certify 243 7 ([w54,i7,w19,i4,i0,i1,i6]) cs243 [s222,s202,s155,s171,s235,s238] (u243 5 234 0x2a4411ac9a2a722ada1043544124d1252c741664104108114e604511810e20e614823cb0af2b6c287c20837d86302082648230618404821aa9a1deaa9a20891820d3d2083908913d6187861944e047b81444184d861888067da0154818661524bc1861ec61bc49237e8a301861ec61b0a28404619aa1a1ee8a1a1861ec61a448b71ed24a418638dd384f043bc38461446fc4b0087f153690154c87404876bc6a43c64137cf24f04f1358513cec0e10df10e17ce13011a99a37f0c1ac1a4066306498213700a4c244066990112ca)

def w110 : Sig := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000

def s240 := certify 243 6 ([w110,i6,i7,w19,i5,i0,i1]) cs243 [] (u243 4 81 0xa1a8627e06300a6030e859d13b7192e30ce2a98d40c6660fc3f00526a17e63383930929a2a74495ca5b86d1b68012449701d408dd846101c9839314e2787a278960b014a08e84207ae)

def s241 := certify 243 7 ([w35,i6,i7,w19,i4,i5,i0,i1]) cs243 [s217,s220,s240,s233,s235,s236] (u243 5 98 0x20c8391820af2848608218222a882186082186081867154618b7486486192a061a81a22fc61b8e061b8e060a488a9924c8d592412cb1924f04f03c88ad88c7f3cc899f3c134a988a98847c877c8eb37c5f37ca8b22444)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s242 := certify 243 8 ([w19,i4,i5,i0,i1,i6,i7]) cs243 [s223,s229,s234,s237,s239,s158,s172,s203,s241] (u243 6 308 0x80a209c0c714cb832e8992240450414809011b93d14ab72f24151040450814638411113d1c622720860218e3840e9490c107293d1041ca482124a9460c4c982044c78b0af98bbac28663c1020df37cc184f6b08106f9aa20427b58c18404506d1109051a3d0a5029012018818e7836488423809f8f38a063840c113d6c18344221066f4d90544f44060d2a5060d292122de57a244a5240c1a64c244a63c0c1a67a0c1a63c2448df37d428886d060c6ffa0c1a21b4a142026922532854a1528d16269011490518ed1224b2824a0929a15b60c7089024a9530120251e14982a60a98509928808a7828c71c638e9811e049839e0e31c218e12524949254c78f254a953a54a9401012898a1be28df146f94ec51011498518e3a30e37c21be10df1d78718e12304)

def w111 : Sig := 0xffffffff00000000ffffffff00000000ffffffff00000000ffff0000

def s243 := certify 243 6 ([w111,i5,i7,i4,i6,i0,i1]) cs243 [] (u243 4 81 0x4edc64b9057942830e859d04310d8230ce2a98ce28cd231a46a17e610441131d408dce2f5c65d35420595107a210c21a886b1af42c2308348d2211c1a80160f54aa6825)

def w112 : Sig := 0xffffffffffffffffffffffffffffffffffffffffffffffffffff0000ffff0000

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s244 := certify 243 7 ([w112,i7,i4,i6,i0,i1,i5]) cs243 [s217,s243] (u243 5 225 0x340823ba3b4e859382089b082530509bc087502087708212e4905f92412c208c604308810cc20c098090b213b398390b60c938839452085acb07db2c588209720c352a5097a8b3508507d20815ecb07db2c15c82021841312104248230633618622019f6805520619131863b8387fe3838619054925861905186592489d186528509da0bf506187f49216c6187f18616d24a238e532522ca250e39df3a44916902f0293c9025823ae3b25963963b2b8cb516522ba252e5225881774eb00f748ca)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s245 := certify 243 6 ([w35,w28,w20,i0,i1,i5]) cs243 [s219] (u243 5 180 0x48c2096592417e49165082f02096924f24916082d0208ee8ed3a164e08231810c2204330830260248c82165b2c1f6cb1652081f48216b2c1f6cb1620842c84ece60e42d8324e20e086104c484109208c18cd861888067da0154818648d249651861fc61965492415249618641461964921fc618ee0e1ff8e0e1865a600475940596558f798913a6104d5944396538f798813847284d58a396391311ccb)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s246 := certify 243 7 ([w28,i7,w20,i6,i0,i1,i5]) cs243 [s245,s221] (u243 5 234 0xd0208ee8ed3a164e08248c20ae9241de492e08226c2094c1426f021d4082f02096924f2491608231810c2204330830260242c84ece60e42d8324e20e48c822eb2c1f6cb2e20825c830d4a9425ea2cd42141f48216b2c1f6cb16208086104c484109208c18cd861888067da0154818644c618ee0e1ff8e0e18648d24ae1861fc61ae4923dc6194a141fe8a141864152496186414619649277c4d10f738e50f751133dc5f50e3963a5611ce39638e11d1332d499448eeb94b943de6205698011ee016b963de698f7134a)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s247 := certify 243 7 ([w35,i7,w20,i4,i0,i1,i5]) cs243 [s245,s220] (u243 5 234 0x48c20b29241de49320822a420a2c222a703062082d0208ee8ed3a164e08231810c220433083026025148216b2c1f6cb1620848c8232b2c1f6cb322083dc8222aa21f6aaa220842c84ece60e42d8324e20e086104c484109208c18cd861888067da015481864152496186414619649248d24b21861fc61b249227461a2a2227682fe21861fc618ee0e1ff8e0e186916902f0293c9025827744700f759688f7a35453dc5f89658e3ace135658e58e1354532e29a248f2ca2ca23de6244e984137210ec8e3de698f711ca)

def s248 := certify 243 7 ([w54,i5,i7,w20,i4,i6,i0,i1]) cs243 [s222,s217] (u243 5 98 0x4ece324e22cb0822cb0821aa886082186082181867154618ee0648619248619219aa0619248619248610e68a938ed3438e58cb009b689b696f3c596f3c589b689b68f148c7748cad0ed0ec04b17f06b021c2)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s249 := certify 243 8 ([w20,i4,i6,i0,i1,i5,i7]) cs243 [s244,s246,s247,s223,s248] (u243 6 308 0xf7340b537a2986a2c4d30347b8a040a334040a30e743a334756230e04092348c1026f6524489195a91237b281023dc808dd078a55bbe105440f71420537a30c4283c10885c860818de82300a3216213b8c38c0e8c859832630e103a64c102261658b267c58b261610212348c40883eb2c5891fc58b20fac2041ee2836888c828d1f8528147b900c41bd041a044630940fc089026f46061907b60c1a23108337c6c82a41e203068d183068c39c0e8df9c388c383069882922530b060d31050c1a61624492348c91288ed060c91fe0c1a23b44891ee8870e8c2a30a8c8899447b8a1c2a3469810f72858a4c153054c29d8a1ee28b0a6f5216493013c053123c48de822c0a30e8c3a34c2c5a3468c65c68d1801ee5131448c524629232978a1ee2930a)

def s250 := certify 243 7 ([w48,i0,w28,i4,i7,i1,i5,i6]) cs243 [] (u243 4 92 0x25033211ce213de2086116442a10e2104a128982130451148e10c43608c3a1674405a16a101685a8405a16a1560b88e204a2094540bc810396e5f89e2098261867154c6a05260a4c60a4e932b32)

def w113 : Sig := 0xdddddddddddddddd0000000000000000ddddccccddddcccc

def s251 := certify 243 5 ([w113,i1,i0,i4,i7,i5]) cs243 [] (u243 6 60 0xf1f071f8485ae74891c0a48810010cd1a05707cf80485c621f312234232244e042244907220c0430104e043804905ac809432041d10244)

def w114 : Sig := 0xddddddddddddddddddddddddddddddddddddccccddddccccddddccccddddcccc

def s252 := certify 243 6 ([w114,i1,i0,i4,i7,i5,i6]) cs243 [s251] (u243 4 81 0x955122a10c22c884a21c4022dc00084f0015400ca4144820882260d234aa01f87e090ce33843290426311c47304c141505701c02082f90476098282a0ae0380)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s253 := certify 243 7 ([w45,i0,i4,i7,i1,i5,i6]) cs243 [s252,s72] (u243 5 243 0x9d10952b2289dc8912842b408213a1874e859102089b0822b0289bc0872820842045398114460438838c604308810cc20c098088f20932aa288fa87928829c206302c01cb05300800e000110522ce414e1000240000a3b0a41ee40800140002ae294b9428001e486513811ee051112102a54413121042482315933649221592361dca521248a486951c91a4a724a5125004beba3bf808ec0b9248e11ce107f10e1fce104712412e4087b0a41ee4084b0ac15ec20e922c17ec205721499029c929472542a62ae99d602602e9ae01c900e93b46)

def s254 := certify 243 6 ([w82,i1,w28,i4,i7,i0,i5]) cs243 [] (u243 6 77 0x8a10e08124480a040043031450189060c489060c4971887cc4e09012404517103222342322442859c488b164488b16441808602094320408c8a04083870408387041d10244)

def s255 := certify 243 7 ([w43,i1,w28,i4,i7,i0,i5,i6]) cs243 [s254] (u243 4 92 0x12819908e7105f2111310c22c885421c42094251098c10ca4144820882261a8149a4634a46348c338aa6918d28586e23881288251502f2078ddb764711cc130461d0b3a0561685a159d216b128)

def w115 : Sig := 0xbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbaaaabbbbaaaabbbbaaaabbbbaaaa

def s256 := certify 243 6 ([w115,i0,i1,i4,i7,i5,i6]) cs243 [] (u243 4 81 0x12aa245421845910944388045b800109e002a80114452384310d821bc6f8286300a60f13c41304c541500180b998670dcc10f89e2098262a0a802c013437405a8)

def w116 : Sig := 0xffffffff33333333ffffffff33333333ffffffff33330000ffffffff33330000

def s257 := certify 243 6 ([w116,i5,i1,i4,i7,i0,i6]) cs243 [] (u243 4 81 0x48156419482890b9810b01d475e48c108426316f23042630425a91c44ae148703d29f80007bc114452386f1be1418c63e208320d18c211849482c912986a02711c452a90)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s258 := certify 243 7 ([w108,i1,i4,i7,i0,i5,i6]) cs243 [s256,s257,s232] (u243 5 243 0x1b9104432407dcb240413408213a1874e859102089b082430409bc08740209e186513811ee05110610218413121042482306308f18b9428408fa08540641c4875b861d5c19cb924b618622083682020618e70b5122710e1f4e11c124710d0a270a42644f09c094712b42e414b9441c4042045398114460438838c604308810cc20c098090206f51b91bd06e5050851c2063ba2718dc89dcb8820e11ce107d10e1f4e104713012f008e90b01df0084b08616c680e980617c6805b81498a41b92946e5442642e9fc072602e9ae71b970e93fec)

def s259 := certify 243 6 ([w105,i5,w28,i4,i7,i1,i6]) cs243 [] (u243 6 77 0x428c82041c382448810718650b3282162c102162c10d9c07ce0681c1070428b8817c9202481016db10201421e04048920060838206a99830650503120c189120c1890c805bc0)

def s260 := certify 243 7 ([w84,i5,w28,i4,i7,i0,i1,i6]) cs243 [s259] (u243 4 92 0x4a0664239c4239c411445238c3a1674405a16a101685a820c8309718423032905121867154c6a0526918d2918d2316f230be632b3ab15c47128179021e84a1884a17b7edfa4a4164894d087a1d212ad22)

def w117 : Sig := 0xccccccccffffffffccccccccffffffffccccccccffffccccccccccccffffcccc

def s261 := certify 243 6 ([w117,i1,i5,i4,i7,i0,i6]) cs243 [] (u243 4 81 0x12055906520a242e6042c0751d79210441130c338aa6918d22d48e22570a4195109e210c21a886b1af422388e85203cf03d14c536098241035206aa543400703d60982)

def w118 : Sig := 0xffffffffffffffff00000000ffffffffffffffffffffffff00000000ffff0000

def s262 := certify 243 6 ([w118,i6,i5,i4,i7,i0,i1]) cs243 [] (u243 4 81 0xc3a1674415e50a04310d824edc64b918c20c338aa6350bf348c6908220898670726918d2a6a840b2a229c4eb38cb002d488d635e8427076210761289d408dc452a9a)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s263 := certify 243 7 ([w85,i5,i4,i7,i0,i1,i6]) cs243 [s261,s262,s173] (u243 5 243 0xa910453250a9c8ab50410420453981144604388389720c352a5097a8b3508523d208f2c2bc99b0a1f0820c604308810cc20c09809e186513811ee05110613618622019f6805520619c1186528507ba285061a3d492f06187b186f124821841312104248230630eb8e13c10ef0e12e114f146ae694b946bc20569b9950bc0a3df3c0ae0b408213a1874eb410209a086b51c11ada705a50208e11ce10e910e1dce104712a15ea20e922a17ea205720616c6487b4861ec6485b49498a69c129470546a66aea5c0f2602e9aef1c1f0e94064)

def w119 : Sig := 0xffffffffffffffff0000000000000000ffff0000ffff0000

def s264 := certify 243 6 ([w119,w22,i5,i4,i7,i0,i1]) cs243 [] (u243 4 81 0xc3a1674417a16a26d4226f114452056619c5531a85f9a46348d29186520a24a2c34206c5ea96a58922497a45868e3d04388e2b0902d405a8348d252a8b08001a97a2c8b21a93e2591c4)

def s265 := certify 243 6 ([w35,w22,i5,w28,i4,i0,i1]) cs243 [s219,s230] (u243 5 78 0x22cb0822cb08608218a8822a30d42cd41867154648619248619219248619248619428c602ee877e9655945fb94b94204a29411d7d5f4ab882d1416548b28891104d14)

def s266 := certify 243 7 ([w22,i5,i6,w28,i4,i7,i0,i1]) cs243 [s217,s224,s264,s265,s221,s231] (u243 5 98 0x30d42cd422cb0822cb0820e3608608218a8822a18671546194a06486192486192192d28c6192486192486294b8810344df4baee8d5eae134b1bb450ad5099d3411c426d426d4e84b1dfad3a164226d426d43a4dd17cdd)

def s267 := certify 243 7 ([w112,i6,w28,i4,i7,i0,i1,i5]) cs243 [] (u243 5 92 0x9421c20a490208e16420a490210c4330230d42cd422cb0822cb084ece324e22cb081044108c18671546194a0648619248619218ee064861928ac790290252e20563b23ae775dd394c8e3a4e44c4)

def w120 : Sig := 0x5555555500000000555555555555555555555555000000005555555555550000

def s268 := certify 243 5 ([w120,i5,i6,i4,i7,i1]) cs243 [] (u243 6 60 0x3d7a149d0babe465f448810436701f380fb4147cfa4347cfa04e7dc342ffa2068350202dad2006a998310d0534127c19f06083820c805bc0)

def w121 : Sig := 0xffffffff00000000ffffffffffffffffffffffff00000000ffffffffffff0000

def s269 := certify 243 6 ([w121,i5,i6,i4,i7,i0,i1]) cs243 [s268] (u243 4 81 0x18742ce882bca1408a229104190612e308460c338aa6350bf348c690ca4144862de4617cc616e9aa102248921a90250f44f13c000f6c388e2119129a6a89290352094aa0461a91c4)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s270 := certify 243 7 ([w119,i6,i4,i7,i0,i1,i5]) cs243 [s269,s264] (u243 5 243 0x9b082530509bc087502091308213a18477e89f10208c604308810cc20c098089720c352a5097a8b3508529b2085acb07db2c5882042045a2d8114460444c82021841312104248230633618622019f68055206189d186528509da0bf5061905492586190518659249e186513811ee0511061245a40bc0a4f240960945948ae894b9489620513b8491161269b59612e122107151df1c6277e250412412e408e90a417e4084b0ac15ec207d22c1f6c205720616c6487f4861fc6485b49498a89df29477d48a68aea6405a602e9ae59df58e93dce)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s271 := certify 243 7 ([w35,i6,w28,i4,i0,i1,i5]) cs243 [s245,s233,s265] (u243 5 234 0x2a420a29242a6492208244c20b2eba267aeb208226c2094e9426fa21d408231810c22043308302602514822eb2c1f6cb2e2081f48222b2c1f6cb2220844c82326181f5863220825c830d461425d82cd4214086104c484109208c18cd861888067da0154818651524ae1861fc61ae49227524a218627461a249244c61b2e381ff8e321861fc6194e141ff8e1418692e90251429077902b829a60113b965c9135954544c5fcaeb943ad4136eb94b9413545205411ca136229489444c4711e23a6211f2ca2ca211d132466984)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s272 := certify 243 8 ([w28,i4,i7,i0,i1,i5,i6]) cs243 [s234,s246,s78,s250,s253,s81,s135,s73,s164,s255,s258,s174,s183,s229,s260,s263,s266,s244,s267,s270,s271] (u243 5 308 0x9a6104994c949a1dcb29941043a61b10444c4738e8661738e44c4710444f40825a44e8618574e85944c4082989b082994c14989bc0879940823a6130825a44b9248360b9245a44b08244c42045624e60451f4460444ce20e5a4c604362422043824c20c5a42602989720c3994a949897a8b39942141344d208136eb2c13607b2c136e2083a60520862457b2c80d97b2c6245720844de18655644e041fdee05144c41845a421841564c48411ec24825a4c18c6276186564880675e76805562481869a6186994a149977a289941861344d492136e186134d5186136e4923a4b14925645b1862b4991865645b4929a6134a44ceb8e13441344134e1dce44c4b845a64ba413421342136417e45a42b82994994984dbae9a698819a6980)

def w122 : Sig := 0x5555555555555555555555555555555555555555555555555555555500000000

def s273 := certify 243 6 ([w122,i0,i7,i5,i6,i1,i4]) cs243 [] (u243 4 81 0x8b0d400114e0028bb00c6014c02e8bbe41122344449a879512aa08d42184591095a107e1f82c619c5530ca32f8c20882230d234a8d6058080dd01b9081af9820c45056952)

def w123 : Sig := 0x3333333333333333333333333333333333333333333333333333333300000000

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s274 := certify 243 6 ([w123,i7,i5,i6,i0,i4]) cs243 [] (u243 6 180 0x4ec034b10b444ecb3eb1004420c02df09e4220de2870804230c03d3b976e30d728fb806e0049f160cf80060058912b8197188e225c707cc40d10890cd9c225088924fec20d08930cf5ee51b89350c5ee0db914489b996e44c916e8911a428511d4468eac448508d4285b986e34c0d6e8508b0810016002cb0af002001210483360c49b120c20334103a21888d0c1c71044474601421109d081108c42342056e55b8d2a35b846e)

def s275 := certify 243 6 ([w123,w61,i7,i5,i6,i0,i4]) cs243 [] (u243 4 72 0x2f4350013129c00d176005ac00fc3f048c96946634a46368bf31a5232c3a08f42286a1d8b22ce823d10e218de8015e091a46460e346108c202bd2057)

def w124 : Sig := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff00000000

def s276 := certify 243 6 ([w124,i4,i7,i5,i6,i0,i1]) cs243 [] (u243 4 81 0x4edc64b88320c25c18742ce831805301867154c671466316f231a85f983f0fc1275023724ae165c94d354124497000ca84a01b46da01016a02d91a462103370841d84aa56a96)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s277 := certify 243 7 ([w61,i7,i5,i6,i0,i1,i4]) cs243 [s86,s273,s112,s274,s275,s217,s276,s235] (u243 5 225 0x34000c962f745b4c800183000ebc4c579f0a7e80009b0006ae689bb8bb6800177000135658d5596134001c206302c01cb0530080167208d1838c73618d082183618e882073208e9861032086aa6873aaa68820732c4ad15c8207320815c7315c04be586f801805924b618622019f680552061967186d384b499e0a3d061ba186c124ba492c06189d1866a8689da0bf686187718616d2485f49216c61a2d1616b26a2ca26b469c53c44d30d32ebad3a1672c0596ba6a2c226b06a2e88770ceb0903374a)

def w125 : Sig := 0xffff0000ffff0000ffff0000ffff0000ffff000000000000ffff00000000

def s278 := certify 243 6 ([w125,i4,i7,w22,i6,i0,i1]) cs243 [] (u243 4 78 0x41c7841064184a1598742ce831805301867154c64b4a3318b7918d40a4c1f87e0911c7a15744a69aa02c2c800ca84a01b46da01016a02d91a4611c5927c591083b0954ad50a7)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s279 := certify 243 7 ([w54,i7,w22,i6,i0,i1,i4]) cs243 [s141,s91,s117,s224,s278,s222] (u243 5 234 0xd0000df58bdd16d167000374003059635565b000026c001ab9a26ee2eda0002c4003af1312b7c29fa00070818c0b0072c14c020059c823460e31cd8634208376aab02081cc8230aaa40c821aa9a1ceaa9a2081cd863a2081cc823a618012f961be006016492d861888067da0154818659c61b4e12d267828f418637461b04921dd24b018640c619aa1a17e8a1a186e861941492e9249411867144b10c1d1c7690368c140cab6b46ba3c7a11f4d3ad05911d67165a99a3770c1ac1a40e621fa98211f00bac3a40e6990312ca)

def w126 : Sig := 0x5555555555555555555555555555555555555555555555550000000000000000

def s280 := certify 243 6 ([w126,i0,i7,w22,i5,i1,i4]) cs243 [] (u243 4 78 0x13129c0022ec00282f00c6014c1842302e8bbe0ac9350f2a12faa2ad44aa823507e1f824619c5531a5230ca32f8c348d2a317a00d4071a30812c351645921035f41411a8a3)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s281 := certify 243 7 ([w35,i7,w22,i5,i0,i1,i4]) cs243 [s104,s280,s88,s265,s220,s236] (u243 5 234 0x60c003af131357c29fa00037400325962c565b200040c0022ba22b6eba2000d00013758bdd16d13700070818c0b0072c14c020060d863a2081cc823a618376aab22081cc8232aaa40c8222aa21ceaaa22081cc823460e31cd8634208012f961be006016492d861888067da01548186e8618db492e92498318637461b249226524b218627461a2a2227682fe21861dc61b4e12d17f828f418670c4708abe97d89035f4ab40cab8ba8b43af412faeb4e85912d8316629a23772ca2ca240e6247498412f2134cb440e6990311ca)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s282 := certify 243 8 ([w22,i5,i6,i0,i1,i4,i7]) cs243 [s277,s279,s281,s92,s118,s143,s223,s237,s266] (u243 6 308 0x1032803626e2976c65ca2e28818a00023340002326e58bd8cd0b348d18000952800094e9e26329797853ca740001ba6e80009bcc2c58dd5dcb164de60000819011ba1114ab77220a882062840a4dce08c50880580391c59493700200468c204466860e38dc8c188cd04089528c1894e840895c840894e8c18374dd54aa11ac2041bbc8408846b2a54818a0da14120a341aa2940a40c806209b8024f9412c19f7e0018026e58912845b060ca088419b93641521110183468c1834668e12d8c58b828e3340c1a53a0c1a52824894a744894a941831ba6e860ca0da2448dd2b4912506d060c81a268b0c61518546444ca240c534151a34a08819a746a50a942a51aec690314e85466919a4694e9d468d1ac468d1812066931a37451ba28dd3578d2062930a)

def s283 := certify 243 7 ([w56,i0,w54,i5,i7,i1,i4,i6]) cs243 [] (u243 4 92 0x4d1564206a1a909ef1049125c0068bb0003d0f4000f43d05800b08a2291c318053023415a308463084630846156486a40d49a0c487139ee7f89e2013504a480de52d05320a6520a4f192ba6)

def w127 : Sig := 0x3333333333333333111111111111111133333333333333331111111100000000

def s284 := certify 243 5 ([w127,i6,i0,i5,i7,i4]) cs243 [] (u243 6 60 0x1e9dca3ee5be128709a588fac485b8d428512c427cf8016d1a056e81001425c621f31226e45104002bc014dc6b71884221080c4830e8871c4)

def w128 : Sig := 0xffffffffffffffff5555555555555555ffffffffffffffff5555555500000000

def s285 := certify 243 6 ([w128,i6,i0,i5,i7,i1,i4]) cs243 [s284] (u243 3 81 0x28bb00229c00bd0d4001705c063014c093a1e68892344a0e306605f8815ca81b220ec5922c0ec83f0fc017619c5561a469a6104412664b439660e4136586823a404681ba)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s286 := certify 243 7 ([w64,i0,i5,i7,i1,i4,i6]) cs243 [s285,s119] (u243 5 243 0x9d10952b2289dc89128428e0049116124e58e100009b0002ae289bb8bb280023f0000bc087bf3c0800042045398114460438839c206302c01cb053008008f20932aa288fa879288290f6089088090f20d10980b408213a1874eb410209a0822b029ac1a28209e1865115d11e1dc51106100a57e586f80180595d5b618622019f6805520618a186969cd1a4a734a6861821841c23f10428fc2c061b411f410f113417f4104713c137c007b03c1efc004d00815c8608d6082348605761a99029cd29a735a2a62b09c4c0a60b09b009cd08f13bd2)

def s287 := certify 243 7 ([w88,i1,w54,i5,i7,i0,i4,i6]) cs243 [] (u243 5 92 0x11a2ac4134d0438410e1244938001a2ec003cf0003cf0001c70019441444fbe01219aa061924861924861a08061a080642cbd04d046b021cc755d510e10e70070021aa88a8822a3c485358)

def w129 : Sig := 0x5555111155551111555511115555111155551111555500005555111155550000

def s288 := certify 243 5 ([w129,i4,i1,i5,i7,i6]) cs243 [] (u243 6 60 0x3cba17fd1016db1020683502244083b76852744280f9c05d5f232f9f34639f3ed051f3e8091f060838206d053406805bc00d5330624f833e)

def w130 : Sig := 0xffff3333ffff3333ffff3333ffff3333ffff3333ffff0000ffff3333ffff0000

def s289 := certify 243 6 ([w130,i4,i1,i5,i7,i0,i6]) cs243 [s288] (u243 4 81 0x902ac83290512173021609cb0cf61867154d231a42f98c2db082cb190d30451148e1bc6f8504310d982bcaf0b7180b508711c4a4290095812b00e2388a55202104ac)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s290 := certify 243 7 ([w86,i1,i5,i7,i0,i4,i6]) cs243 [s289,s175] (u243 5 243 0xa910443240a9c8ab40410e0049116124e58e100009700042e4097b88140002400033c324f04f30001e186513811ee0511061004be586f80180592488f18b9428408fa085406410f1939312310f48cf30633618662019f680556061b430c12411341cf410c31a30c43041ac1a40c304a74453981144604394d39c6063014d01c1dc53018010606f69d31bd074d069868c6043c24110cc904cc1863411f410731341cf4104713c137c00f103c17fc004d01216d2188d1922352185b19a98a41d329a74da426430a0c23260b09b031d330f13cc8)

def s291 := certify 243 6 ([w105,i4,w54,i5,i7,i1,i6]) cs243 [] (u243 5 77 0x468ab104d34104511443886aa2182086182086175f919f869d04d046b021c41f9a33bef9a2efefbcf3efbcf3e184384185519c61a86861924861924864be1be)

def s292 := certify 243 7 ([w84,i4,w54,i5,i7,i0,i1,i6]) cs243 [s291] (u243 4 92 0x268ab210350d48473882288a4723415a308463084610579428c211819482890c338aa63682931a5231a52348c690be632bb4b3435206a4d0624384ae0b82e2388fce8bbd05e1e87a179e21eb0a0)

def w131 : Sig := 0xccccffffccccffffccccffffccccffffccccffffccccccccccccffffcccccccc

def s293 := certify 243 6 ([w131,i1,i4,i5,i7,i0,i6]) cs243 [] (u243 4 81 0x48156419482890b9810b04e5867b03f0fc1230421098c108426610596321a609224b80368db40019513c04711d0a4079621868f01c005a4711ca542821304be0380)

def w132 : Sig := 0xffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff00000000

def s294 := certify 243 6 ([w132,i6,i4,i5,i7,i0,i1]) cs243 [] (u243 4 81 0x61d0b3a1064184b818c02981071e1016a10169867154c6a17e6316f2307e1f82464b4a331a5232534d50250ec9f094420ec251b46da000ca84a0017b6002d602c3408e8452b54)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s295 := certify 243 7 ([w125,i4,i5,i7,i0,i1,i6]) cs243 [s293,s294,s278] (u243 5 243 0xa910453250a9c8ab50410420453981144604388389720c352a5097a8b35085246083c0820e4224c1861c206302c01cb05300801e186513811ee05110613618622019f6805520619bf186528507ba285061a291869122dc7b4929061804be586f801805924b4912512291342645912411a912953051ac1a52450e0049116124e58e100014006d69bf1b546fd4680024000c22965648a64c0003211f210f11321df2104710815c8b0f1b0817c8b057b1216d2187b1921ed2185b19a98a51bf29a6fda526530a5c29260b09b091bf90f1407c)

def s296 := certify 243 6 ([w123,i6,w54,i5,i7,i0,i4]) cs243 [] (u243 5 77 0x68bb000f3c000f3c01a5115f5117ef804866a81864921864921971114f91146f6b021c43d045d045115a2ac451174d0452002bc048648622a688608218608218384538c45)

def s297 := certify 243 7 ([w61,i6,w54,i5,i7,i0,i1,i4]) cs243 [s296] (u243 5 92 0x1a2ec003cf0003cf0000bdd0001658018c014c021aa8860821860821820e360817c8214dfbe0121867154619aa06192486192486192d28c61924868acf6b021fad32d3070dc3585a2ada3c7459c4)

def w133 : Sig := 0xaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaaffffffffaaaaaaaa

def s298 := certify 243 6 ([w133,i0,i6,i5,i7,i1,i4]) cs243 [] (u243 4 81 0x28bb0004538049125c018c029809350f2a22446888451148e12b4210c24f88711c4235013504a480de4ad2885148467f89e2181605918461505046260847f13c4)

def w134 : Sig := 0xffff0000ffff0000ffffffffffffffffffff0000ffff0000ffffffffffff0000

def s299 := certify 243 6 ([w134,i4,i6,i5,i7,i0,i1]) cs243 [] (u243 4 81 0x61d0b3a1064184b8114452390579428c211830ce2a98d42fcc62de46194828924634839318394a69aa0c2308b241c47108c94d50810943b13c4f711c40295408c420943b711c4)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s300 := certify 243 7 ([w109,i6,i5,i7,i0,i1,i4]) cs243 [s298,s299,s238] (u243 5 243 0x9b0006ae689bb8bb6800243000ebc4c499f0a7e8000e0049116124e58e10001c206302c01cb05300801c52086aa6873aaa6882243618e882073208e98604204539811446043883804be586f801805924b618622019f68055206189d1866a8689da0bf6861ba186c124ba492c0619e186513811ee05110611ae9a8b089ac1a8ba21d67c06113a18643eba130122107169c51c62716268412e136e00f102e1dee004d00815c860736081cc8605761216d218f119217d2185b19a98a89c529a715a8a68b0a7c2ea60b09b0e9c5e8f140f4)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s301 := certify 243 8 ([w54,i5,i7,i0,i1,i4,i6]) cs243 [s279,s94,s283,s286,s97,s142,s120,s179,s287,s290,s182,s208,s176,s229,s292,s295,s239,s248,s277,s297,s300] (u243 5 308 0x98a910499ac9a98a9c8ab99a1043c61d10459c47d3486e19d3459c4710459ce00496144584985ce58e59c4000989b00099ab9a989bb8bb99a00012c4b00012f0f3c12e15f3c12f00003c6130006144df3c8360bf3c6144d00059c42045534e60451cc460459ce20e615c20635340b00825cb05361402009a620899aa9a9a07aaa99a20812c4b61812f020812e0520812f06183c6036185345720865d792085345761859de18655744e045ddee05159c418461404be57561be1ec018061564925376186574880672376805553481869a618699aa1a98d5a2899a18612c4b18612f049212cb149212f01863c4ad1865745b492264774925745b1869a612ca59f4c3412c412c412f417f459c4c0499a99a984bc309a698879a6982)

def s302 := certify 243 6 ([w58,i0,w35,i6,i7,i1,i5]) cs243 [] (u243 5 77 0x288c1082eba082eba084310cc0888aa208618208618206d8b224449f99f0bef975467efa22ffefb8e3efb8e3e00c080005318c002e8800165800165804be03e)

def s303 := certify 243 7 ([w41,i0,w35,i6,i7,i1,i4,i5]) cs243 [s302] (u243 5 92 0xa230420bae820bae8230208c00213c0022b8001658001658017c0014510c4330218c014c0222a882186082186082186082ad18b2245e6ddb708c08c0160164bc829488e622fe2a38e283af864c6)

def w135 : Sig := 0xddddddddddddddddddddddddddddddddddddddddddddddddcccccccccccccccc

def s304 := certify 243 6 ([w135,i1,i0,i6,i7,i4,i5]) cs243 [] (u243 4 81 0x128c11086127c40109e0028810008b32c04aa8235082208981f87e090d234aa032905121821084c6084213304c1701c04150513043250c1305c070105414471047)

def w136 : Sig := 0xffffffff55555555ffffffff55555555ffffffff55555555ffffffff00000000

def s305 := certify 243 6 ([w136,i5,i0,i6,i7,i1,i4]) cs243 [] (u243 4 81 0x145d8004586a00262538016b006300a6024d43ca85d177c8c21180dd080dc955046a0fc3f048c338aa61a46951865197c634a4634a46d2b4a0d7c2cf85056944206be)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s306 := certify 243 7 ([w126,i0,i6,i7,i1,i4,i5]) cs243 [s304,s305,s280] (u243 5 243 0xa90822b028a9c0c12820a2b0827ba18499e89f7820a40000bc0a4f04f08001b50002ae287fbae280022b00079622c7f59678000c604308810cc20c09809c206302c01cb053008008f20932aa288fa87928829e205dc98175e61ec8822278952b22a2ca229e282184131210424823063004be586f801805924b618622019f6805520618a186989b51a4a6d4a88619e1865ca2b195e8adec861b012f008eb0b01df0084b0961356007f0161fd6004d01815d820eb21817d8205722299029b52a26d622a62b29dc47a61329b279b578eb3f78)

def s307 := certify 243 7 ([w90,i1,w35,i6,i7,i0,i4,i5]) cs243 [] (u243 5 92 0xa230420bae820bae8208c30200213c0022b8001658001658001c7001044108cfbe0121a22fc61b8e061b8e061a08061a080642d38b22444765d9302302700700622a98a9862a3ad853c8)

def w137 : Sig := 0xbbbb0000bbbb0000bbbb0000bbbb0000bbbb0000bbbb0000aaaa0000aaaa

def s308 := certify 243 5 ([w137,i0,i1,i6,i7,i5]) cs243 [] (u243 6 60 0x78762a7b16b90a5c891b11488508602ddb886c89102487ccf827cfb60a7cfa41e7cf975465f001808000d82b6009045c8014b10024f803e)

def w138 : Sig := 0xbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbaaaaaaaaaaaaaaaa

def s309 := certify 243 6 ([w138,i0,i1,i6,i7,i4,i5]) cs243 [s308] (u243 4 81 0x94608843093e20084f001440800459960255411a84310d8218c029806f1be0a114452204c1301605950543c4f112f406e8309826005f009aa82a1e27881ba308)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s310 := certify 243 7 ([w46,i1,i6,i7,i0,i4,i5]) cs243 [s309,s74] (u243 5 243 0xa908243040a9c0c14020a4508213a1073eba1020a40000bc0a4f04f080009700042e4097b881400010b000116110b58cb100002184131210424823063004be586f80180592488f18b9428408fa08540641e186513811ee051106114f18622019c7780552061a2104432422ca240410ca744308810cc20c094f09c206302c01cb053008010206f89d71bd075d08882042045ca4511449144c8823a12fa08730ba1cfa084b0961356007d0161f56004d03816f818eb1b817f8185b1a298a41d72a275e2426432a1ce1261329b211d710eb3d58)

def s311 := certify 243 7 ([w112,i4,w35,i6,i7,i0,i1,i5]) cs243 [] (u243 5 92 0xa230420bae820bae820a490210c43302222a8821860821860822cb0822cb081044108c186715461a22fc61b8e061b8e0648619248619252d58b2244e77ddf9029025a2b96b965ae3ad65140)

def w139 : Sig := 0x3333333300003333333333330000333333333333000033333333333300000000

def s312 := certify 243 5 ([w139,i5,i4,i6,i7,i0]) cs243 [] (u243 6 60 0x7af7317b971887cc47cf80126ce13fb0a26e451366e51f74888fac45be12870a16e350a1446908906241856e35b844438e2080057800508442)

def w140 : Sig := 0xffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff00000000

def s313 := certify 243 6 ([w140,i5,i4,i6,i7,i0,i1]) cs243 [s312] (u243 4 81 0xc3a16744edc64b86300a60c211817d0815cc338aa6350bf319c51983f0fc1234a4634a467502370da36d0024892e001310f4000f6c0d53540d5c1ab84a56a84206ae)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s314 := certify 243 7 ([w110,i4,i6,i7,i0,i1,i5]) cs243 [s313,s240] (u243 5 243 0x9b082530509bc0875020b40823ba3b4e85938208c604308810cc20c098089720c352a5097a8b3508510b213b398390b60c938839c206302c01cb0530080021841312104248230633618622019f68055206189d186528509da0bf5061a471863b8387fe383861804be9a46f8018051524a238e532522ca250e3a400009450a41dc4f080014006d89dd1b54775488000e0049ca47124e91cec8003a12fa08eb0ba17fa084b09815d8207d2181f58205723816f8187f1b81ff8185b1a298a51dd2a27762526532a6443a61329b239dd38eb3dd6)

def s315 := certify 243 6 ([w123,i5,w35,i6,i7,i0,i4]) cs243 [] (u243 5 77 0x8ae000596000596016f10d4310fef8048688bf186e38186e3819b310dfd10c6f8b22444510e23044310fae84310fae8432002bc048648622a88821860821860808432043)

def s316 := certify 243 7 ([w61,i5,w35,i6,i7,i0,i1,i4]) cs243 [s315] (u243 5 92 0x22b80016580016580013129c001658018c014c0222a8821860821860860821817c8214ffbe012186715461a22fc61b8e061b8e061924861924866ad78b22474715c58be23062c3aeb03afa60c2)

def w141 : Sig := 0xaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaaaaaaaaa

def s317 := certify 243 6 ([w141,i0,i5,i6,i7,i1,i4]) cs243 [] (u243 4 81 0x28bb0008b0d400109e018c029809350f2a1745df204310d82255411a86b1af4210c21a88160592f414a8569442f835144511304c3003d007b84610a82b44278351304c)

def w142 : Sig := 0xffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffff0000

def s318 := certify 243 6 ([w142,i4,i5,i6,i7,i0,i1]) cs243 [] (u243 4 81 0x61d0b3a276e325c21886c1202d0b5080b42d41867154c6a17e6338a3308220899231a5231a4ea046e1ac6bd084308b22a6a840bace32c25104a202954d108e11c25104a2)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s319 := certify 243 7 ([w62,i5,i6,i7,i0,i1,i4]) cs243 [s317,s318,s113] (u243 5 243 0x9b0006ae689bb8bb680034000c962f745b4c800240000bc0a4f04f08001c206302c01cb05300801c32086aa6873aaa688222d208d1838c73618d0820c604308810cc20c0980804be586f801805924b618622019f68055206189d1866a8689da0bf6861a2d186d384b499e0a3d0618218413121042482306322d1616b26a2ca26b469a086b89c31ada70da8820b4082ca2d18748b74c82096135600eb0161dd6004d01815d820732181cd8205722816e818eb1a817e8185b1a298a69c32a270e26a66b2a7c4d261329b2d1c3d0eb40fa)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s320 := certify 243 8 ([w35,i6,i7,i0,i1,i4,i5]) cs243 [s105,s303,s306,s114,s75,s98,s186,s307,s310,s189,s213,s244,s311,s314,s247,s271,s241,s277,s316,s319,s281] (u243 5 308 0x98a90829a2c2298a9c0c19a208211c4708211f2eba11e1deba11f20823ae1b08260c4beba86617eba60c4b08260e40005142f028564f04f60c20009a60009a2ba29a13bae9a200011c4700011f259611e0d59611f20003ae0b0005144d596826075965144d00060cc604353c220431ccc20c60c2602515c206353c0b001f5cb05351402009a62089a2aa29a05aaa9a220811c4720811f261811e0361811f22083ad9720853c576185e57761853c5720860c2184164cc4841354248260cc18c51404be64d61be1fc0180515649253f618664c880672c76805553c8186989d1869a2a22989da0bf9a218611c4718611f2e3811cade3811f21863ac9918664c5be381dc5fe3864c5b1869a611ca9a29a29847cb29a698919a6984)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def s321 := certify 243 9 (roots 243) cs243 [s76,s83,s99,s121,s149,s177,s184,s190,s214,s242,s249,s272,s282,s301,s320] (u243 6 240 0x26441384614cb841a899224c2820a4c6816a942986a82cd3034985020519a02052823ac104b47562304040931401b260a5db20728b8a2614000461c0244c085a440a38b0e8c1000094900009809e0280d23c9d281000098808dd5852adccb90544130a102a3041112b0e31117908602461c2074a1862156042212ee3040c9408c029870462ac01600354e2ca5300080098506d168828d0588a50293100c4231e0d92d047010ad3ce2846081824a041a05a184a013208902943030c980093eb45833eec003009858912acd8306b421066bcd9054ac20306)

theorem lower243 : Claim 243 10 := fromSearch 16777300 (by decide +kernel) s321.property

open PEqualNP.CircuitLowerBounds

def graph : Sig := goalAt 255
theorem graph_proper : proper graph := by unfold proper; decide +kernel

def edgeList : List Nat := [0, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7]
def target (x : Fin 8 → Bool) : Bool :=
  decide (∃ i < edgeList.length / 2,
    (List.ofFn x).getD (edgeList.getD (2*i) 0) false = true ∧
    (List.ofFn x).getD (edgeList.getD (2*i+1) 0) false = true)

-- The conjunctions cover all of the posted edges.
def smallCircuit : Circuit := ⟨[⟨.or,[1,2]⟩, ⟨.or,[1,3]⟩, ⟨.or,[4,5]⟩, ⟨.or,[4,9]⟩, ⟨.or,[5,6]⟩, ⟨.or,[6,7]⟩, ⟨.or,[7,8]⟩, ⟨.or,[7,10]⟩, ⟨.and,[0,15]⟩, ⟨.and,[12,14]⟩, ⟨.and,[11,13]⟩, ⟨.or,[16,17]⟩, ⟨.or,[19,18]⟩],20⟩

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

def lowRow (i : Fin 8) : Row := Fin.ofNat 256 (1 <<< ([4, 5, 5, 6, 0, 0, 1, 0] : List Nat).getD i.val 0)
def highRow (i : Fin 8) : Row := Fin.ofNat 256 ((1 <<< i.val) ||| (1 <<< ([4, 5, 5, 6, 0, 0, 1, 0] : List Nat).getD i.val 0))

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



-- Every omitted vertex is essential before setting it to zero.
theorem lowerGraph : Impossible true graph 11 eightInputs.toFinset :=
  (ruleFor 255 lower243 none (by decide +kernel)).property 11 eightInputs
    (by decide +kernel) (by decide +kernel)


end PEqualNP.Outside.L_meta_32343

open PEqualNP.Outside.L_meta_32343 in
theorem PEqualNP.Outside.L_meta_32343 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o fit _ correct
  exact replaceShort lowerGraph gates o fit correct

import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_28862

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
  (x 0 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 2 &&& x 5) ||| (x 0 &&& x 6) ||| (x 1 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 1 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)

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



def cuts194 : Cuts (goalAt 194) := []

def state194_0 : List Sig := roots 194
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude194_0 : Impossible true (goalAt 194) 3 state194_0.toFinset :=
  node_ok cuts194 [] 0x30100420230000820230200c00030100c08030100820210808420220808424020800c04020a00820020808828020808c04010900424010808828010800c08010900420010808424010808c08020a008280 (by decide +kernel)

theorem lower194 : Claim 194 4 :=
  fromSearch 285212768 (by decide +kernel) exclude194_0

theorem lower226 : Claim 226 5 :=
  fromLift 5 32 286261328 lower194 (by decide +kernel)


def cuts200 : Cuts (goalAt 200) := []

def state200_0 : List Sig := roots 200
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude200_0 : Impossible true (goalAt 200) 3 state200_0.toFinset :=
  node_ok cuts200 [] 0x30100480830000880830200c00030100c08030100880812020480822020484022000c04022200880022020888022020c04012100484012020888012000c08012100480012020484012020c080222008880 (by decide +kernel)

theorem lower200 : Claim 200 4 :=
  fromSearch 855662592 (by decide +kernel) exclude200_0

theorem lower232 : Claim 232 5 :=
  fromLift 5 32 863002624 lower200 (by decide +kernel)


theorem lower202 : Claim 202 5 :=
  fromLift 5 2 285237344 lower200 (by decide +kernel)


def cuts162 : Cuts (goalAt 162) := []

def state162_0 : List Sig := roots 162
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude162_0 : Impossible true (goalAt 162) 3 state162_0.toFinset :=
  node_ok cuts162 [] 0x28080220228000820228200a00028080a08028080820208808220220808222020800a02020a00820020808828020808a02008880222008808828008800a08008880220008808222008808a08020a008280 (by decide +kernel)

theorem lower162 : Claim 162 4 :=
  fromSearch 269484112 (by decide +kernel) exclude162_0

theorem lower170 : Claim 170 5 :=
  fromLift 5 8 269512784 lower162 (by decide +kernel)


def rule234_0 : {c : Cut // CutGood (goalAt 234) c} :=
  ruleFor 234 lower226 none (by decide +kernel)

def rule234_1 : {c : Cut // CutGood (goalAt 234) c} :=
  ruleFor 234 lower232 none (by decide +kernel)

def rule234_2 : {c : Cut // CutGood (goalAt 234) c} :=
  ruleFor 234 lower202 none (by decide +kernel)

def rule234_3 : {c : Cut // CutGood (goalAt 234) c} :=
  ruleFor 234 lower170 none (by decide +kernel)

def cuts234 : Cuts (goalAt 234) := [rule234_0,rule234_1,rule234_2,rule234_3]

def state234_0 : List Sig := roots 234
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude234_0 : Impossible true (goalAt 234) 6 state234_0.toFinset :=
  node_ok cuts234 [] 0x4000cc04010808c0004000c820230200c0004000cc04030200c0404000c820210808420240008a02008808a00040008820228200a00040008a02028200a0204000882020880822024000c68280880822024000c42024000c42024000c68284000c48284000c42020880822024000088081210088004000082022220088004000088082220088084000082021210082024000c48082220048004000c42021210048004000c48081210048084000c4202222004202400082a0a121002a024000822021a1802202400082a0a1a180220a40008220212100220240004820208880820040004880820a00820040004820220a0082024000488080888088084000c42020888042004000c48081090042004000c42021090042024000c480808880480840008220210900220040008a08008880220040008220208880220240008a0801090042404000100000888022204000048400a8a02a204000100010a8a02228400004840088802220 (by decide +kernel)

theorem lower234 : Claim 234 7 :=
  fromSearch 286285904 (by decide +kernel) exclude234_0

def cuts172 : Cuts (goalAt 172) := []

def state172_0 : List Sig := roots 172
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude172_0 : Impossible true (goalAt 172) 3 state172_0.toFinset :=
  node_ok cuts172 [] 0x28000a00028080240422000880022020a0200b010240409030240423020880822030880809000240009010a080090802c20090a02420 (by decide +kernel)

theorem lower172 : Claim 172 4 :=
  fromSearch 807433472 (by decide +kernel) exclude172_0

def cuts228 : Cuts (goalAt 228) := []

def state228_0 : List Sig := roots 228
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude228_0 : Impossible true (goalAt 228) 3 state228_0.toFinset :=
  node_ok cuts228 [] 0x30000c00030100a02028000a00028080240409010640409110240409080a02030110242009080642009180242009000240009010a080 (by decide +kernel)

theorem lower228 : Claim 228 4 :=
  fromSearch 1461716224 (by decide +kernel) exclude228_0

def rule236_0 : {c : Cut // CutGood (goalAt 236) c} :=
  ruleFor 236 lower232 none (by decide +kernel)

def rule236_1 : {c : Cut // CutGood (goalAt 236) c} :=
  ruleFor 236 lower200 none (by decide +kernel)

def rule236_2 : {c : Cut // CutGood (goalAt 236) c} :=
  ruleFor 236 lower232 (some (0,input 5,input 7)) (by decide +kernel)

def rule236_3 : {c : Cut // CutGood (goalAt 236) c} :=
  ruleFor 236 lower172 none (by decide +kernel)

def rule236_4 : {c : Cut // CutGood (goalAt 236) c} :=
  ruleFor 236 lower228 none (by decide +kernel)

def cuts236 : Cuts (goalAt 236) := [rule236_0,rule236_1,rule236_2,rule236_3,rule236_4]

def state236_0 : List Sig := [0xffffffff00000000ffffffff00000000f0f0f0f000000000f0f0f0f0,0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 7,input 3,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude236_0 : Impossible true (goalAt 236) 4 state236_0.toFinset :=
  node_ok cuts236 [] 0x30010c0043011048081900024001303024001200048001202088802201088042203048400b0002400090202400280002404120206404090102404090302c0409010240409200a004090110002 (by decide +kernel)

def state236_1 : List Sig := [0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 7,input 3,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude236_1 : Impossible true (goalAt 236) 5 state236_1.toFinset :=
  node_ok cuts236 [⟨state236_0,exclude236_0⟩] 0xc04412020c00422030c08030010c04430200c044220304808120206460120204808090804c0c13020646013030480c09080480812020682809010240412020644419010682819110482812020240409011000109010240422030a080280110001282002480220302404090102420800002400400042404090002420090102404400050001400044808222004800302004840120004808121004808302008880222002c0c121002c04090106860090102c0c1a180240c09010484009010880c12100880430110888022010880c22200880c301104840121002c28121002c20090804c44090802c28131102428090804840090810000400008808 (by decide +kernel)

def state236_2 : List Sig := [0xffffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00,input 3,input 6,input 2,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude236_2 : Impossible true (goalAt 236) 5 state236_2.toFinset :=
  node_ok cuts236 [] 0xa00028000a0200901024041202048280901024040b0302c0c090108c0822020880c220202400090002404282004c0812020480c1202024200b0a02c280908024200b0a02c2809080480822020c04012020c08022020a02022020a0200b03024040b03024041202048404000c888022020a02022020a020 (by decide +kernel)

def state236_3 : List Sig := [0xffffffffffffffff0000000000000000ff00ff00ff00ff00,input 3,input 7,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude236_3 : Impossible true (goalAt 236) 4 state236_3.toFinset :=
  node_ok cuts236 [] 0x38000c00030080c00009000240009010a08031000c00030010c0001300048001201048001200068000b030480012000c0002202048001202024041a020240412020480c13020480812020c00022020c000222004800120204800 (by decide +kernel)

def state236_4 : List Sig := [0xffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00,input 3,input 7,input 2,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude236_4 : Impossible true (goalAt 236) 5 state236_4.toFinset :=
  node_ok cuts236 [⟨state236_3,exclude236_3⟩] 0x480822020c0801202200001202048084000c24041901048280901024042202088280901024040b0302c0c090104c0812020480c120202400090002404282008c0822020880c2202024200b0a02c280908024200b0a02c2809080a02012020c0801202088800b03024040b0302404220208880280a04840 (by decide +kernel)

def state236_5 : List Sig := [0xf0fff0fff0fff0fff0fff0fff0fff0fff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 3,input 7,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude236_5 : Impossible true (goalAt 236) 4 state236_5.toFinset :=
  node_ok cuts236 [] 0x30010c004301104808090106404120a0240409010a004220a02404120004800120208c800b0102404090302404220008800220204840130204808120304808090002400090110001230208808220308808090802c20090a02420 (by decide +kernel)

def state236_6 : List Sig := [0xff00ff00ff00ff00ff00ff00ff00ff00000000000000000000000000000000,input 3,input 7,input 2,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude236_6 : Impossible true (goalAt 236) 5 state236_6.toFinset :=
  node_ok cuts236 [⟨state236_5,exclude236_5⟩] 0x480822020c080120202404190104828090102404220208828090104c0812020480c120202400090002404282008c0822020880c2202024200b0802428090804800120004808302002c0409010240c090108800220204840302004808302004808282002404282002404400002420800002420280808880 (by decide +kernel)

def state236_7 : List Sig := [0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000000000,input 6,input 7,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude236_7 : Impossible true (goalAt 236) 4 state236_7.toFinset :=
  node_ok cuts236 [] 0x2a00088002208088001a000480012080480009000240009010a0802300088002201088001300048001201048001200088003010048001210024041a1002404121002420131002420280808800301008800222004800121004800 (by decide +kernel)

def state236_8 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,input 7,input 2,input 3,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude236_8 : Impossible true (goalAt 236) 5 state236_8.toFinset :=
  node_ok cuts236 [⟨state236_7,exclude236_7⟩] 0x240430100c060090102404191106444090102404191106444090102c0409010240c0901048403010088801210088801210048402220200001210048404001024000900024042820024200b080242809080242030100c04409080242019180646009080242019180646009080880830100c080281804808 (by decide +kernel)

def state236_9 : List Sig := [0xf0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 6,input 7,input 3,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude236_9 : Impossible true (goalAt 236) 4 state236_9.toFinset :=
  node_ok cuts236 [] 0x9010a004301802404090106404120a024040b010240409030240422010880422030484012000480012020888030000c000301004808090002400090110001090802c20090a02420220208808220302420130204808120304808 (by decide +kernel)

def state236_10 : List Sig := [0xffffffffffffffff00000000000000000000000000000000,input 6,input 7,input 2,input 3,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude236_10 : Impossible true (goalAt 236) 5 state236_10.toFinset :=
  node_ok cuts236 [⟨state236_9,exclude236_9⟩] 0x240430100c060090102404190104828090102c0409010240c0901048403010088801210048001200048082220024000900024042820024200b080242809080242030100c044090804c0812020480c12020c00030100480828200240428200240422200484022200484040000242080000242022020c080 (by decide +kernel)

def state236_11 : List Sig := roots 236
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude236_11 : Impossible true (goalAt 236) 6 state236_11.toFinset :=
  node_ok cuts236 [⟨state236_1,exclude236_1⟩,⟨state236_2,exclude236_2⟩,⟨state236_4,exclude236_4⟩,⟨state236_6,exclude236_6⟩,⟨state236_8,exclude236_8⟩,⟨state236_10,exclude236_10⟩] 0x80014c04012020c0004000c880830200c00080010c04030200c0404000c880812020480840004a02009010a00040004880828200a00040004a02028200a0204000488080901024044000468280901024044000448081911064044000468281911048284000448080901024048000c880812100880040010a02022200880080008880822200880840010a02012100a0204000c480822200480040010c0801210048008000448081210048084000cc080222008880400042c0c121002c044000424041a1802404400042c0c1a180240c400042404121002404400008c0c090808c08400008808400008808400008c0c80000880c400008808090808808400004c0c090804c08400004808191804808400004c0c19180480c40000480809080480840000240440004240040000a08009080240040000240409080240440000a08040000a080400004c440908024204000048400b0a02c20400004c440b0a02428400004840090802420 (by decide +kernel)

theorem lower236 : Claim 236 7 :=
  fromSearch 857761024 (by decide +kernel) exclude236_11

theorem lower166 : Claim 166 5 :=
  fromLift 5 4 269485392 lower162 (by decide +kernel)


def cuts102 : Cuts (goalAt 102) := []

def state102_0 : List Sig := roots 102
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude102_0 : Impossible true (goalAt 102) 3 state102_0.toFinset :=
  node_ok cuts102 [] 0x88084202091102202118084202108184202090002400090102202108004200108082220088002200088082404088802420109102220 (by decide +kernel)

theorem lower102 : Claim 102 4 :=
  fromSearch 17827152 (by decide +kernel) exclude102_0

def rule230_0 : {c : Cut // CutGood (goalAt 230) c} :=
  ruleFor 230 lower226 none (by decide +kernel)

def rule230_1 : {c : Cut // CutGood (goalAt 230) c} :=
  ruleFor 230 lower194 none (by decide +kernel)

def rule230_2 : {c : Cut // CutGood (goalAt 230) c} :=
  ruleFor 230 lower166 (some (3,input 1,input 2)) (by decide +kernel)

def rule230_3 : {c : Cut // CutGood (goalAt 230) c} :=
  ruleFor 230 lower166 (some (1,input 1,input 2)) (by decide +kernel)

def rule230_4 : {c : Cut // CutGood (goalAt 230) c} :=
  ruleFor 230 lower166 none (by decide +kernel)

def rule230_5 : {c : Cut // CutGood (goalAt 230) c} :=
  ruleFor 230 lower102 none (by decide +kernel)

def rule230_6 : {c : Cut // CutGood (goalAt 230) c} :=
  ruleFor 230 lower228 none (by decide +kernel)

def rule230_7 : {c : Cut // CutGood (goalAt 230) c} :=
  ruleFor 230 lower166 (some (2,input 2,input 7)) (by decide +kernel)

def rule230_8 : {c : Cut // CutGood (goalAt 230) c} :=
  ruleFor 230 lower166 (some (1,input 2,input 7)) (by decide +kernel)

def cuts230 : Cuts (goalAt 230) := [rule230_0,rule230_1,rule230_2,rule230_3,rule230_4,rule230_5,rule230_6,rule230_7,rule230_8]

def state230_0 : List Sig := [0xfffffffffffffffffffffffffffffffffcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc,input 7,input 1,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude230_0 : Impossible true (goalAt 230) 4 state230_0.toFinset :=
  node_ok cuts230 [] 0x10808820230110420219080420210808242008808420209110220208808820209200220209000240008809000110808420410808828008808220408808240220808820420808424408880a020 (by decide +kernel)

def state230_1 : List Sig := [0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc,input 7,input 1,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude230_1 : Impossible true (goalAt 230) 4 state230_1.toFinset :=
  node_ok cuts230 [] 0xc00030000c04010808220210808244408808a00028000a02008808420210810420220a002202088102202090088200208008280280804202190804202090802400090002202282002220088804244090808202 (by decide +kernel)

def state230_2 : List Sig := [0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc,input 1,input 5,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude230_2 : Impossible true (goalAt 230) 5 state230_2.toFinset :=
  node_ok cuts230 [⟨state230_0,exclude230_0⟩,⟨state230_1,exclude230_1⟩] 0xc04010808c00020808c08030000c04030200c04020808420210808a02008808a00020808a08028000a02028200a02020808220208809000308808220210808644410809000119110244410808220208808820210910820228080828420810820220a10820228080424428080420220a10420230200424410810420210910420230200828430200220210910220209011000108810220240004220209010424409009000240000222020808242020808a02080004a0202080a000020808a02009080242010808242010808c08019180642010808646010808c08009080242008809000109000a08009080240008808242008808a08040004a080 (by decide +kernel)

def state230_3 : List Sig := [0xffffffffffffffff0000000000000000cccccccccccccccc,input 1,input 7,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude230_3 : Impossible true (goalAt 230) 4 state230_3.toFinset :=
  node_ok cuts230 [] 0x38000c00030080c00009000240009010220231000c00030010c00010800620008808420010800460010810420010800c00020808420008808240408808420210808420611808420210808c00020808c000088804200108084200 (by decide +kernel)

def state230_4 : List Sig := [0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 1,input 7,input 2,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude230_4 : Impossible true (goalAt 230) 5 state230_4.toFinset :=
  node_ok cuts230 [⟨state230_0,exclude230_0⟩,⟨state230_3,exclude230_3⟩] 0x420220808c0801080a000110808420240010220210808244408808220220808a08008808240408808220209010460210808420610808240009000240408808860220808820620808242040002000009080a02010808c08010808828008808240408808240420a00242020a102420208088280400142220 (by decide +kernel)

def state230_5 : List Sig := [0x3333333333333333333333333333333330303030303030303030303030303030,input 1,input 7,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude230_5 : Impossible true (goalAt 230) 4 state230_5.toFinset :=
  node_ok cuts230 [] 0x420220808c04410808220210808244408808220220808248008808420010800420208880220008800220209010820020800820208880242010808246010808240009000240408808242020808c044208084244 (by decide +kernel)

def state230_6 : List Sig := [0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 7,input 1,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude230_6 : Impossible true (goalAt 230) 5 state230_6.toFinset :=
  node_ok cuts230 [⟨state230_0,exclude230_0⟩,⟨state230_5,exclude230_5⟩] 0xc04410808420220818c08030010c04430200c04420818420210808646010808420209080460611808646011818420609080420210809000808808220210808644410809000119110244410808220208809000108808220220818a08028011000128200248020818220208808242008808240040004240409000242009010240440004220208808420208880420030200424010800420210900420230200222008880220210900220009010222008800220208880220209010424009010820608880820430110828020810820620a008206301102220088820001088802220090804644090820000119104244090802220088810007400008202 (by decide +kernel)

def state230_7 : List Sig := roots 230
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude230_7 : Impossible true (goalAt 230) 6 state230_7.toFinset :=
  node_ok cuts230 [⟨state230_2,exclude230_2⟩,⟨state230_4,exclude230_4⟩,⟨state230_6,exclude230_6⟩] 0x40010c04010808c00040010820230200c00040010c04030200c04040010820210808420240004a02008808a00040004820228200a00040004a02028200a02040004820208808220240011000408808220240010420219110420240011000119110244440010420208808220240000860609080860240000820240000820240000860680008820640000820209080820240010460609080460240010420219180420240010460619180420640010420209080420240000240440004240040000220209080240040000240409080240440000220240000220240014820208880820040018a02020a00820080004820220a00820240014a02008880222040010420208880420040010c08010900420040010420210900420240010c080088802220400042202109002200400042404088802200400042202088802202400042404109002404400010000088802220400002420119102420400020000119104244400002420088802220 (by decide +kernel)

theorem lower230 : Claim 230 7 :=
  fromSearch 286262608 (by decide +kernel) exclude230_7

theorem lower174 : Claim 174 6 :=
  fromLift 6 4 269514064 lower170 (by decide +kernel)


def cuts106 : Cuts (goalAt 106) := []

def state106_0 : List Sig := roots 106
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude106_0 : Impossible true (goalAt 106) 3 state106_0.toFinset :=
  node_ok cuts106 [] 0x88084202120a022021200048001202042020a8082202088282202108004200108084808088002200088084240088802a20088a02220 (by decide +kernel)

theorem lower106 : Claim 106 4 :=
  fromSearch 17850448 (by decide +kernel) exclude106_0

theorem lower110 : Claim 110 5 :=
  fromLift 5 4 17851728 lower106 (by decide +kernel)


def rule238_0 : {c : Cut // CutGood (goalAt 238) c} :=
  ruleFor 238 lower234 none (by decide +kernel)

def rule238_1 : {c : Cut // CutGood (goalAt 238) c} :=
  ruleFor 238 lower236 none (by decide +kernel)

def rule238_2 : {c : Cut // CutGood (goalAt 238) c} :=
  ruleFor 238 lower230 none (by decide +kernel)

def rule238_3 : {c : Cut // CutGood (goalAt 238) c} :=
  ruleFor 238 lower230 (some (0,input 2,input 5)) (by decide +kernel)

def rule238_4 : {c : Cut // CutGood (goalAt 238) c} :=
  ruleFor 238 lower236 (some (3,input 2,input 5)) (by decide +kernel)

def rule238_5 : {c : Cut // CutGood (goalAt 238) c} :=
  ruleFor 238 lower230 (some (3,input 2,input 5)) (by decide +kernel)

def rule238_6 : {c : Cut // CutGood (goalAt 238) c} :=
  ruleFor 238 lower174 (some (3,input 2,input 5)) (by decide +kernel)

def rule238_7 : {c : Cut // CutGood (goalAt 238) c} :=
  ruleFor 238 lower202 none (by decide +kernel)

def rule238_8 : {c : Cut // CutGood (goalAt 238) c} :=
  ruleFor 238 lower234 (some (2,input 5,input 7)) (by decide +kernel)

def rule238_9 : {c : Cut // CutGood (goalAt 238) c} :=
  ruleFor 238 lower200 none (by decide +kernel)

def rule238_10 : {c : Cut // CutGood (goalAt 238) c} :=
  ruleFor 238 lower194 none (by decide +kernel)

def rule238_11 : {c : Cut // CutGood (goalAt 238) c} :=
  ruleFor 238 lower230 (some (2,input 2,input 7)) (by decide +kernel)

def rule238_12 : {c : Cut // CutGood (goalAt 238) c} :=
  ruleFor 238 lower236 (some (1,input 2,input 7)) (by decide +kernel)

def rule238_13 : {c : Cut // CutGood (goalAt 238) c} :=
  ruleFor 238 lower230 (some (1,input 2,input 7)) (by decide +kernel)

def rule238_14 : {c : Cut // CutGood (goalAt 238) c} :=
  ruleFor 238 lower106 none (by decide +kernel)

def rule238_15 : {c : Cut // CutGood (goalAt 238) c} :=
  ruleFor 238 lower110 none (by decide +kernel)

def rule238_16 : {c : Cut // CutGood (goalAt 238) c} :=
  ruleFor 238 lower234 (some (3,input 5,input 7)) (by decide +kernel)

def rule238_17 : {c : Cut // CutGood (goalAt 238) c} :=
  ruleFor 238 lower234 (some (1,input 5,input 6)) (by decide +kernel)

def rule238_18 : {c : Cut // CutGood (goalAt 238) c} :=
  ruleFor 238 lower234 (some (1,input 5,input 7)) (by decide +kernel)

def rule238_19 : {c : Cut // CutGood (goalAt 238) c} :=
  ruleFor 238 lower234 (some (0,input 5,input 7)) (by decide +kernel)

def rule238_20 : {c : Cut // CutGood (goalAt 238) c} :=
  ruleFor 238 lower174 (some (1,input 2,input 7)) (by decide +kernel)

def rule238_21 : {c : Cut // CutGood (goalAt 238) c} :=
  ruleFor 238 lower234 (some (2,input 6,input 7)) (by decide +kernel)

def rule238_22 : {c : Cut // CutGood (goalAt 238) c} :=
  ruleFor 238 lower174 none (by decide +kernel)

def rule238_23 : {c : Cut // CutGood (goalAt 238) c} :=
  ruleFor 238 lower230 (some (3,input 5,input 6)) (by decide +kernel)

def rule238_24 : {c : Cut // CutGood (goalAt 238) c} :=
  ruleFor 238 lower230 (some (2,input 5,input 6)) (by decide +kernel)

def rule238_25 : {c : Cut // CutGood (goalAt 238) c} :=
  ruleFor 238 lower170 none (by decide +kernel)

def rule238_26 : {c : Cut // CutGood (goalAt 238) c} :=
  ruleFor 238 lower230 (some (1,input 5,input 6)) (by decide +kernel)

def rule238_27 : {c : Cut // CutGood (goalAt 238) c} :=
  ruleFor 238 lower236 (some (1,input 5,input 6)) (by decide +kernel)

def rule238_28 : {c : Cut // CutGood (goalAt 238) c} :=
  ruleFor 238 lower166 (some (3,input 2,input 5)) (by decide +kernel)

def rule238_29 : {c : Cut // CutGood (goalAt 238) c} :=
  ruleFor 238 lower230 (some (3,input 5,input 7)) (by decide +kernel)

def rule238_30 : {c : Cut // CutGood (goalAt 238) c} :=
  ruleFor 238 lower230 (some (2,input 5,input 7)) (by decide +kernel)

def rule238_31 : {c : Cut // CutGood (goalAt 238) c} :=
  ruleFor 238 lower236 (some (1,input 5,input 7)) (by decide +kernel)

def rule238_32 : {c : Cut // CutGood (goalAt 238) c} :=
  ruleFor 238 lower230 (some (1,input 5,input 7)) (by decide +kernel)

def rule238_33 : {c : Cut // CutGood (goalAt 238) c} :=
  ruleFor 238 lower230 (some (0,input 5,input 7)) (by decide +kernel)

def rule238_34 : {c : Cut // CutGood (goalAt 238) c} :=
  ruleFor 238 lower236 (some (3,input 5,input 7)) (by decide +kernel)

def rule238_35 : {c : Cut // CutGood (goalAt 238) c} :=
  ruleFor 238 lower230 (some (3,input 6,input 7)) (by decide +kernel)

def rule238_36 : {c : Cut // CutGood (goalAt 238) c} :=
  ruleFor 238 lower230 (some (2,input 6,input 7)) (by decide +kernel)

def rule238_37 : {c : Cut // CutGood (goalAt 238) c} :=
  ruleFor 238 lower236 (some (1,input 6,input 7)) (by decide +kernel)

def rule238_38 : {c : Cut // CutGood (goalAt 238) c} :=
  ruleFor 238 lower234 (some (1,input 6,input 7)) (by decide +kernel)

def rule238_39 : {c : Cut // CutGood (goalAt 238) c} :=
  ruleFor 238 lower230 (some (1,input 6,input 7)) (by decide +kernel)

def rule238_40 : {c : Cut // CutGood (goalAt 238) c} :=
  ruleFor 238 lower170 (some (3,input 3,input 7)) (by decide +kernel)

def rule238_41 : {c : Cut // CutGood (goalAt 238) c} :=
  ruleFor 238 lower230 (some (0,input 6,input 7)) (by decide +kernel)

def rule238_42 : {c : Cut // CutGood (goalAt 238) c} :=
  ruleFor 238 lower236 (some (3,input 6,input 7)) (by decide +kernel)

def rule238_43 : {c : Cut // CutGood (goalAt 238) c} :=
  ruleFor 238 lower202 (some (1,input 1,input 3)) (by decide +kernel)

def rule238_44 : {c : Cut // CutGood (goalAt 238) c} :=
  ruleFor 238 lower166 (some (1,input 2,input 7)) (by decide +kernel)

def rule238_45 : {c : Cut // CutGood (goalAt 238) c} :=
  ruleFor 238 lower234 (some (3,input 6,input 7)) (by decide +kernel)

def cuts238 : Cuts (goalAt 238) := [rule238_0,rule238_1,rule238_2,rule238_3,rule238_4,rule238_5,rule238_6,rule238_7,rule238_8,rule238_9,rule238_10,rule238_11,rule238_12,rule238_13,rule238_14,rule238_15,rule238_16,rule238_17,rule238_18,rule238_19,rule238_20,rule238_21,rule238_22,rule238_23,rule238_24,rule238_25,rule238_26,rule238_27,rule238_28,rule238_29,rule238_30,rule238_31,rule238_32,rule238_33,rule238_34,rule238_35,rule238_36,rule238_37,rule238_38,rule238_39,rule238_40,rule238_41,rule238_42,rule238_43,rule238_44,rule238_45]

def state238_0 : List Sig := [0xffffffffffffffffffffffffffffffff0f0f0f0f000000000f0f0f0f00000000,input 7,input 5,input 1,input 3,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude238_0 : Impossible true (goalAt 238) 6 state238_0.toFinset :=
  node_ok cuts238 [] 0xe06010808420228080c08028080e06030200a0602808042021080864601080842020908068280908064601a0a06420090804202108084808222004800108084840120004808121004808108088880108082c08121002c00090006860090002c081a180240809000484009000a82812100a82028080888028080a82822200a028280804840280802c28121002428090806860090802c281a1802c2009080484009080420208880420012020424010800420210900420212020222012021000a088802220121002a280a88100090a8a0222812100222008880260210900260009000222009000260208880240209000424009001000908880222028080828028081000920a00828028080222008881000910900424009080222008881000908880222009080424009080682809000240010808644019000682819100682810808240009000a0200900024004001ca08028200a02028200a0204001c240009000242009000240040000a0800880824202820024204000024000900100084001c8202 (by decide +kernel)

def state238_1 : List Sig := [0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000000000,input 6,input 7,0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000,input 5,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude238_1 : Impossible true (goalAt 238) 5 state238_1.toFinset :=
  node_ok cuts238 [] 0x2600090002402090008a00220008802220004a0012000480212000240022000a8200900024001200068200900022201090022200908022020908088002a08088000908048001a0804800120008800301004800109002220109002220121002400191002400121002420191802420208088800301008800108084800121004800 (by decide +kernel)

def state238_2 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,input 7,0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000,input 5,input 1,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude238_2 : Impossible true (goalAt 238) 6 state238_2.toFinset :=
  node_ok cuts238 [⟨state238_1,exclude238_1⟩] 0xb000240009020240012100c040222004840222004840121008880800004840121010005088802a20088a0222009800240009008240008880c04020a00222008880424010900222008880424010900222009000c0403818024000900064401910024000900064401910024000908024280b080242008880424008880242008808242030100e06009080242019180646009080242019180646009080820230100c080281804202 (by decide +kernel)

def state238_3 : List Sig := [0xf0f0f0f00000000ffffffffffffffff0f0f0f0f000000000f0f0f0f00000000,input 6,input 7,input 5,input 1,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude238_3 : Impossible true (goalAt 238) 5 state238_3.toFinset :=
  node_ok cuts238 [] 0xb00024000902024002a080a020280a0a020120004800120204202088802a20088a0222009800240009008240008880a02020a00222010800420010808480809000c0402808024000900064001a0a0240030000c0003010042020908024280b0802420088804240088802420088082400090802400208088202280802420090804202190804202 (by decide +kernel)

def state238_4 : List Sig := [0xffffffffffffffff00000000000000000000000000000000,input 6,input 7,0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000,input 5,input 1,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude238_4 : Impossible true (goalAt 238) 6 state238_4.toFinset :=
  node_ok cuts238 [⟨state238_3,exclude238_3⟩] 0xb000240009020240012100c040222004840120004800120204202088802a20088a0222009800240009008240008880c04020a00222010800420010808480809000c0403818024000900064001a0a024000908024280b080242008880424008880242008808242030100e06009080242010808642010808c00030100420222200484022200484020a00222020a0022202920024002920024004001c242080000242020808c080 (by decide +kernel)

def state238_5 : List Sig := [0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000,input 5,input 1,input 3,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude238_5 : Impossible true (goalAt 238) 7 state238_5.toFinset :=
  node_ok cuts238 [⟨state238_0,exclude238_0⟩,⟨state238_2,exclude238_2⟩,⟨state238_4,exclude238_4⟩] 0x80008c04010808c00040018820230200c00080004c04030200c040400188202108084202400148808121008800400148202222008800400148808222008808400148202121008202400144808222004800400144202121004800400144808121004808400144202222004202400142c08121002c004001424001a1802400400142c081a180240840014240012100240040010820208880820040010880820a00820040010820220a0082024001088080888088084001042020888042004001048081090042004001042021090042024001048080888048084001500050888022204001448400a8a02a204001500040a8a022284001448400888022204001026021090026004001024000888024004001026020888024024001024001090024004001ca0200900024004001c820229200a4004001ca02029200a0204001c82020900024004001868280900024004001c42021910064004001c68281910068284001842020900024004001ca0200908024204001c82024001c82024001ca02080000a0204001c82020908082024001868280908024204001c42021918042024001c68281918064204001842020908042024001468600908024204001448400b0a024284001468600b0a02c204001448400908024204001022200908022204001042404001042404001022204001022204001042400908024204000100004000c2202 (by decide +kernel)

def state238_6 : List Sig := [0xfffffffffffffffffffffffffffffffffffffffff0f0f0f0fffffffff0f0f0f0,input 5,0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 7,input 1,input 3,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude238_6 : Impossible true (goalAt 238) 6 state238_6.toFinset :=
  node_ok cuts238 [] 0x420230010c04410808420211818460610808420211818460610808480012000480810808880422010880c208182c20090802428090802c0409010240c090104840131104c441210042001080042021202022200a880222808880820420810820622030222009080464408880260409010240609010424008880222010900a0204002100080901042021a0a0420209010a004092002404090802404088182202 (by decide +kernel)

def state238_7 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 6,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 1,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude238_7 : Impossible true (goalAt 238) 5 state238_7.toFinset :=
  node_ok cuts238 [] 0x2c2009080242809080880422010880c2081868201a0806828222002c801210048400920022200a8802228088802220090804244088808204208108206220302220188804240088802680088802220092008202208088206400446420090802460090806444208184828208184202090802480090808828088082202191108206 (by decide +kernel)

def state238_8 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 1,input 3,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude238_8 : Impossible true (goalAt 238) 6 state238_8.toFinset :=
  node_ok cuts238 [⟨state238_7,exclude238_7⟩] 0x646010808420209080460611808646011818420609080420210808c04410808420220818682830010c0441a0a06828208184202108084808222004800108084840120004808121004808108088880108082c28121002c20090804c44090802c281311024280908048400908100071210048400920068601a181000a1a180686009200484012100880c12100880420818686022010880c1a180880c20818484020818420208880420012020424010800420210900420212020222012021000a088802220121002a280a88100090a8a022281210022200888100090888022200908046440908100091191042440908022200888100071090042400920022200888100090888022200920042401090082061090082042203022202081082060888082062203042402203082064001c82024000024202080882060908082064000100124000068280920068281080900071080868288000068281080824801080824204003824204001c24800920024200920024204001d0007220a100104003c2202 (by decide +kernel)

def state238_9 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,input 7,0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 1,input 3,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude238_9 : Impossible true (goalAt 238) 6 state238_9.toFinset :=
  node_ok cuts238 [] 0x10808460210818420210808c0803020042021080868281a0a042021200048001202042020b0802420090a024201210088802220048401210068601a18048401210068601a1804840108004200108084808088802a20088a0222008880242010910222008880828020a0022201090022200888042401090022200888042404002024200908100002808082061a0a042021a0a0420209080a0800908100074003ca080092002202 (by decide +kernel)

def state238_10 : List Sig := [0xffffffff00000000ffffffff00000000000000000000000000000000,input 5,0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 1,input 3,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude238_10 : Impossible true (goalAt 238) 6 state238_10.toFinset :=
  node_ok cuts238 [] 0x1918042021080824201181846021918046061081824201080842021202088801200042021210048001202048401202042022220042020b0a048400b08024201311024200b0a04c44090a024201210024200a82848400a80822021a18022020a82868600882822021210022021080822201080048081090042001080842401080848080888048084002822200888048400a8a02a20400242a28088a048400888022204002422200888024201191024204002446441091024200888022200880842400880024040888022000880822200880824041090024041a0a022020880842021911042021a0a06444120a0420208808220209080220209001000709010240009080240409011000708808220230200820630010420230110420230200c04430110420220818420222200820622010484022030880422200880c22030484020818820620a00880c20810222020818820420a00820620818222022030880c4001d001320809000f400482480 (by decide +kernel)

def state238_11 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f00000000,input 5,input 6,input 7,input 1,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude238_11 : Impossible true (goalAt 238) 5 state238_11.toFinset :=
  node_ok cuts238 [] 0x8800220008808208084c00130004c08118082c000900024080900022200a880222808880820020800820222020460011800460213020260009000240209000c00030000c044118082400280002480090002400190004828090002420090a02c2009080222010910222009080a020108084202190804602088082400090802400 (by decide +kernel)

def state238_12 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 5,input 6,0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 7,input 1,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude238_12 : Impossible true (goalAt 238) 6 state238_12.toFinset :=
  node_ok cuts238 [⟨state238_11,exclude238_11⟩,⟨state238_7,exclude238_7⟩] 0x2201088042203082060b0802420090a024201a08068201a0a08880121006840121804840222004840121008880088802a20088a0222020810820420818880c08880242010910222008880622010900222010900222008880424020a00222008880828020808682820818c0442081864200908024600908042021911082068000482060908064400908100071a0a06444120a0220230110820630110820609082000009081000e (by decide +kernel)

def state238_13 : List Sig := [0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00f000f000f000f0,input 6,0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 7,input 1,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude238_13 : Impossible true (goalAt 238) 5 state238_13.toFinset :=
  node_ok cuts238 [] 0x2202280102480088082c000b00024040880868001200048201200022000880022020901082042081082062203022200b0804244088804a0012000480212000880012000c004301104800120004c0010818480009010220209010220210900222010900222020818880c220108804090802420131002c20108084800130104800 (by decide +kernel)

def state238_14 : List Sig := [0xfffffffffffffffffffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0,input 6,0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 7,input 1,input 3,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude238_14 : Impossible true (goalAt 238) 6 state238_14.toFinset :=
  node_ok cuts238 [⟨state238_13,exclude238_13⟩] 0x2202280102480088082202090102404088082202190102444088082202090102404088082a0208808220a08808880422010880c208184840131004844121004c04130104c0c1181a00001210048404003422000880022020901022200a880222808880820420810820622030222011900424408880460411810460613030222010900424008880c04040054242030010c004301104606191804606108184202 (by decide +kernel)

def state238_15 : List Sig := [0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000000000,input 6,input 7,0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 1,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude238_15 : Impossible true (goalAt 238) 5 state238_15.toFinset :=
  node_ok cuts238 [] 0x240009000240408808220222010a080088086800120004820120002200088002202090102220090804244088808a04220108806220104a00120004802120008800120004c001201048001200088043011048001210022021a1002202109002220109002220121002420131002420208188804301108804108084800121004800 (by decide +kernel)

def state238_16 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,input 7,0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 1,input 3,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude238_16 : Impossible true (goalAt 238) 6 state238_16.toFinset :=
  node_ok cuts238 [⟨state238_15,exclude238_15⟩] 0x9000240009010220208808c0442820022020880864441911022020880864441911022020a80822020882822020b0802420090a0242012100c04422200484022200484012100888080000484012101000d088002200088082404088802a20088a0222008880242010910222008880c04420a00222008880424010900222008880424010900222009080646019180242030100820619180242019180242030110c080400504202 (by decide +kernel)

def state238_17 : List Sig := [0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 7,input 1,input 3,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude238_17 : Impossible true (goalAt 238) 7 state238_17.toFinset :=
  node_ok cuts238 [⟨state238_6,exclude238_6⟩,⟨state238_8,exclude238_8⟩,⟨state238_9,exclude238_9⟩,⟨state238_10,exclude238_10⟩,⟨state238_12,exclude238_12⟩,⟨state238_14,exclude238_14⟩,⟨state238_16,exclude238_16⟩] 0x4003cc04410808420240050820630200c00480018c04430200c0444005082061080842024003864601080842024005024201181846028001464601181842064005024201080842024005068280880822024001c42021911042028001068281911048284005042020880822024003e00030880822024001c820628200a0048000a00012820024804001c82060880822024003824200880824004001d00070901024008000024200901024044001d0007088082202400344808222004800400344202121004800400344808121004808400344202222004202400342a0a121002a024003422021a1802202400342a0a1a180220a40034220212100220240034880c12100880440034820622200880440034880c22200880c400348206121008206400342c28121002c20400342420131102420400342c2813110242840034242012100242040030420208880420040030480810900420040030420210900420240030480808880480840030220210900220040030240408880220040030220208880220240030240410900240440035000d0888022204003448400a8a02a2040035000c0a8a0222840034484008880222040030820608880820440030880c20a00820440030820620a00820640030880c08880880c40031000c08880222040030242011910242040031000c11910424440030242008880222040001000b400008202 (by decide +kernel)

def state238_18 : List Sig := [0x3333333333333333333333333333333333333333333333333333333300000000,input 7,input 5,input 6,input 2,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude238_18 : Impossible true (goalAt 238) 5 state238_18.toFinset :=
  node_ok cuts238 [] 0x1280042001082042000a8002200088202200228008200208208200090802c20090a02420118004200108104200098002200088102200218008200208108200108008200301004200088004200120a022000880082002808022000888022280a8802220088804244090802220120204200188804200090102200088802200220208200280808200 (by decide +kernel)

def state238_19 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000,input 7,input 5,input 6,input 1,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude238_19 : Impossible true (goalAt 238) 5 state238_19.toFinset :=
  node_ok cuts238 [] 0x130004c001302046020b0002400090202400230008c00230208602088802a20088a02220118004600118084c08098002400090082400218008600218088c0831000c400301004602090006400120a0240009000a4002808024000908024280b0802420088804244088802420108084202190804602088082400090802400208088202280808602 (by decide +kernel)

def state238_20 : List Sig := [0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00000000,input 7,input 5,input 6,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude238_20 : Impossible true (goalAt 238) 5 state238_20.toFinset :=
  node_ok cuts238 [] 0x1300048001201048000b0002c000b0102a022300088002201088000888024201091022201280048001200848000a8002a000a8082c042280088002200888001200088003010048001a0004800120a048002a0008800280808800090802428090802c20088802228088802a201080848001a08048000880822021a1002a02208088800280808800 (by decide +kernel)

def state238_21 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000,input 7,input 5,input 6,input 1,input 2,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude238_21 : Impossible true (goalAt 238) 6 state238_21.toFinset :=
  node_ok cuts238 [⟨state238_18,exclude238_18⟩,⟨state238_19,exclude238_19⟩,⟨state238_20,exclude238_20⟩] 0x68201a08068282220048401a100486012100a82028080a0282808200021210048404000824200b080242809080242019080246009080644009080242028200242028080c0440908200010908024204000022200a880222808880222009080424408880222018880424008880424008880222010900222028080828008882000008880222040004e02028080c0402808042021a0a06444120a0482828080c040280808828088088202 (by decide +kernel)

def state238_22 : List Sig := [0xffffffffffffffffffffffff00000000,input 7,input 5,input 6,input 1,input 2,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude238_22 : Impossible true (goalAt 238) 6 state238_22.toFinset :=
  node_ok cuts238 [⟨state238_11,exclude238_11⟩] 0x68201a08068282220048401a10048601210088002200088082080824200b08024280908024201908024600908064400908024202820086022080882062080822200a880222808880222009080424408880222018880424008880424008880222010900820020800820222020c00030000c080208086828191104828120a0a00028000a08020808484022200484022200242080000242040000222020a00222020a00420210808682830200220208808644428200a020 (by decide +kernel)

def state238_23 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 7,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 6,input 1,input 2,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude238_23 : Impossible true (goalAt 238) 6 state238_23.toFinset :=
  node_ok cuts238 [⟨state238_7,exclude238_7⟩] 0x1a08068201a0a088802220048401210088802a080a020280a0a020121006840121804840090802c20090a0242009080642009180242029200242009080a08009080a020800002420191002420090810011088802a20088a0222008880242010910222008880622010900222020a00222008880828008880a02020a00222010900222008880424010808c02028080a0602808064441a0a04828120a0a02028200a020220a02202088086444400588202 (by decide +kernel)

def state238_24 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 5,input 1,input 2,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude238_24 : Impossible true (goalAt 238) 6 state238_24.toFinset :=
  node_ok cuts238 [] 0x12100684012180484022200484012100888012100c0402220048401a08068201a0a1001a090802c20090a0242019100242009081001931200242009080c08009080c040301102420090806420091802420088802a20088a0222008880242010910222010900222008880424020a00222008880828008880c04020a00222008880622010900222008808a04028100a060301006828191104828120a0c04030200c0404003c42021080868284001c8202 (by decide +kernel)

def state238_25 : List Sig := [0xffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f00000000,input 7,input 5,input 6,input 1,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude238_25 : Impossible true (goalAt 238) 5 state238_25.toFinset :=
  node_ok cuts238 [] 0x4c00130004c08118082c0009000240809000a82028080a028280802428090802c200908022200a880222808880460011800460213020260009000240209000222028080828008880424408880222009080460228080c04011808420210808642011808240019000482809000240030100a020090002400088082420090008202 (by decide +kernel)

def state238_26 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f0f0f0f0f0f0f0f0f00000000,input 5,input 6,input 1,input 3,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude238_26 : Impossible true (goalAt 238) 6 state238_26.toFinset :=
  node_ok cuts238 [⟨state238_25,exclude238_25⟩,⟨state238_11,exclude238_11⟩] 0x220204840220008202222008800220208880220208202121008202130208880130004602121004c001302048401302046022220046020b02048400b00024001a18024000b020686009020240012100240020808222020800880820a0082002080882802080888080888088084007022200888048400a8a02a20400242a28088a04840088802220118082220118004c08109004600118084240118084c08088804c0809808424009800240008880240009808222009008240010900240030100460231000820231200c40030100c48030100820211808460228080240009000820229200a40028080a4802808082020900024001a0a024000900046021911064001a0a06444120a04602090002400280802420090808202800048202280820000280808202090808202121002420090804c440b0a02428121002c280b0804c440908024200888024200888046444002442440888100090888046440908024201a0a024201080846021918042021a0a06460190804602090804602400450003088082400090802400400442420090802400400142400 (by decide +kernel)

def state238_27 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f0f0f0f0f0f0f0f0f00000000,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 5,input 6,input 1,input 3,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude238_27 : Impossible true (goalAt 238) 6 state238_27.toFinset :=
  node_ok cuts238 [] 0x2200088002202082021a08068201a0a08880121006840121804840222004840121008880208008200208088808088802a20088a0222008880622010900222010900222008880424020a00222008880828038080820230100820211808a02020808a02020808682819110482809000a02020808a02020808242020808a020208082420090a02c20090802220109102220090802420091806420090810011090802420191010000 (by decide +kernel)

def state238_28 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 5,input 6,input 1,input 2,input 3,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude238_28 : Impossible true (goalAt 238) 7 state238_28.toFinset :=
  node_ok cuts238 [⟨state238_21,exclude238_21⟩,⟨state238_22,exclude238_22⟩,⟨state238_23,exclude238_23⟩,⟨state238_24,exclude238_24⟩,⟨state238_26,exclude238_26⟩,⟨state238_27,exclude238_27⟩,⟨state238_12,exclude238_12⟩] 0x88081210088002080888802200088082220088082080848402080868282220068204006848401a080682812100682840068888022201001a1210048401911068601a101001a1a180486019110484012101001a22200888040008484012101001a121004840400088880222008606090808602208090011208088606800188206208082420208084c44090802420121002c280b0804c440b0a024281210024200908100110908024201a0a064601908100111918024601a0a024200908064444001c644040044242009080644409080242040045001140045001180016000440000242009081001109080242040001001140000820208880820022020828020800820220a00820222020222022021001a088802220121002a280a881001b0a8a0222812100222008881001108880222009080464409081001b11910424409080222008881001b0888022201a0a0424018881001b1090042401a0a0222008881001b10900424019110222008881001b08880222019110424010901001b20a00828040004222008881001b08880222040004828020a00c0401a0a0e02020809001620808c0408000cc0402080868282080900184001c42022808064442808082024001c82022808200022808082021911082021a0a100161a0a10007191106444400590016120a1001740058220228081000f2808082028000482022808200002808082024003c8202 (by decide +kernel)

def state238_29 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f00000000,input 5,input 7,input 1,input 3,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude238_29 : Impossible true (goalAt 238) 6 state238_29.toFinset :=
  node_ok cuts238 [] 0x31100420231000860230200c40031100c080311008602108084202120208880120004202121004800120204840120204202222004202230204840230008602222008c002302088802302086021210086020b02048400b00024001a18024000b02068600902024001210024001080822201080048081090042001080842401080848080888048084002822200888048400a8a02a20400242a28088a04840088802220218082220218008c0820a008600218088280218088c08088808c080980842400980024000888024000980822200900824001090024001a0a024000900042021910064001a0a064401a0a0420209000240028080240009000860228200a40028080a0802808086020900024001a0a024200908042021918042021a0a064601908042020908042021a18024200908048400b0a024281a1802c280b0804840090802420088802420088804240400244240088810009088804240090802420280802420208088602400208202280810012280808602090808602282010003088082400090802400282002420090802400400142400 (by decide +kernel)

def state238_30 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f00000000,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,input 7,input 1,input 3,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude238_30 : Impossible true (goalAt 238) 6 state238_30.toFinset :=
  node_ok cuts238 [] 0x10808a0202818042021080868281a0a042021200048001202042022a080a020280a0a0201210068601a18048401210068601a1804840108004200108084808088802a20088a0222008880a02020a00222010900222008880424010900222008880424021808682810808682810808a020282008828090002420108086420108082420090a02c200908022201090022200908024204001ca02009080a080090802420292010000 (by decide +kernel)

def state238_31 : List Sig := [0xffffffffffffffff0000000000000000ffffffff00000000,input 6,input 5,input 7,input 1,input 2,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude238_31 : Impossible true (goalAt 238) 6 state238_31.toFinset :=
  node_ok cuts238 [] 0xa82028080a0282808048401a10048601210048001200048081080824200b080242809080242028080c0440908064400908024202820046021080842061080822200a880222808880222009080424408880222028080828008880424008880222010900420010800420212020a02030100a020220a0620210808644410808c00030000c04010808888012100888012100242019180242019180222010900222010900820220808a02030100220208808a080191106828 (by decide +kernel)

def state238_32 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,input 7,input 1,input 2,input 3,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude238_32 : Impossible true (goalAt 238) 7 state238_32.toFinset :=
  node_ok cuts238 [⟨state238_23,exclude238_23⟩,⟨state238_29,exclude238_29⟩,⟨state238_30,exclude238_30⟩,⟨state238_8,exclude238_8⟩,⟨state238_9,exclude238_9⟩,⟨state238_21,exclude238_21⟩,⟨state238_31,exclude238_31⟩] 0xe06010808420228080c08028080e06030200a0602808042021080a00061080842024005868281a0a200051a0a0682840058420210808480822200480010808484012000480812100480810808888010808a82812100a82028080888028080a82822200a0282808048402808100201210048402820068601a18100201a18068602820048401210100201210048404000868601a18100201a1806860400084840121004606090804602108086460108084606191804206108082420108084c44090802420121002c280b0804c440b0a0242812100242009081001209080242028081001228081001280012000328080242009080a4844001ca48028200242009080a4840908024202820100122820100128000a0001400002420090810012090802420400010012400004202088804200120204240108004202109004202120202220120210020088802220121002a280a881001f0a8a0222812100222008881001208880222009080464409081001f11910424409080222008881001f08880222028080828028081001f20a00828028080222008881001f10900424028200222008881001f08880222028200424010901001f10900424040004222008881001f08880222040004424010901001e4001c82021a0a0a0801a0a042024001c42021a0a200001a0a0420228200420228081000f28081000728200a0804001d0007220a1001d4003c2202 (by decide +kernel)

def state238_33 : List Sig := [0xf0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 5,input 7,input 1,input 3,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude238_33 : Impossible true (goalAt 238) 6 state238_33.toFinset :=
  node_ok cuts238 [] 0x30110420210808820630200c00430110c0803011082061080842021202088801200042021210048001202048401202042022220042022203048402201082062220088042203088802203082061210082060a82848400a80822021a18022020a82868600882822021210022021080822201080048081090042001080842401080848080888048084002822200888048400a8a02a20400242a28088a0484008880222020818222020810880c20a00820420818828020818880c08880880c0880842400880024040888022000880822200880824041090024044002422200888024201191024204002446441091024200888022201a0a022020880842021911042021a0a06444120a0420208808220228080220228000820629200a00028080a4802808082060880822021181824201180842021918042021181864601081842020908042021311024200908048400b0a02c20131102c28090a0484009080242020818242020808a0204002c820220819000d20818a0200908024200901100050900022020908024000901024200901022024000c2202 (by decide +kernel)

def state238_34 : List Sig := [0xff00ff00ff00ff0000000000ff00ff00ff00ff00ff00ff0000000000000000,input 6,input 5,input 7,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude238_34 : Impossible true (goalAt 238) 5 state238_34.toFinset :=
  node_ok cuts238 [] 0x2300088002201088000900024000901022021300048001201048000888024201091022202280088002200888000880022000880824041280048001200848002800088002208088001a00048001208048001200088003010048001210024201310024201090022201090022202080888003010088001210022021a1002202108084800121004800 (by decide +kernel)

def state238_35 : List Sig := [0xffffffffffffffff00000000ffffffffffffffffffffffff0000000000000000,input 6,input 5,input 7,input 1,input 2,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude238_35 : Impossible true (goalAt 238) 6 state238_35.toFinset :=
  node_ok cuts238 [⟨state238_34,exclude238_34⟩] 0xa82028080a028280802a0208808220a0880888801210048402220200001210048404000824200b080242809080242028080c0440908024000900024040880824201918064600908024201918064600908022200a880222808880222009080424408880222028080828008880220008800220209010222010900424008880222010900424008880a00028000a02008808220219110644408808220219110644408808c04028080c04028080420220808820230100a020 (by decide +kernel)

def state238_36 : List Sig := [0xffffffff00000000ffffffff00000000000000000000000000000000,input 5,input 7,input 1,input 2,input 3,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude238_36 : Impossible true (goalAt 238) 7 state238_36.toFinset :=
  node_ok cuts238 [⟨state238_33,exclude238_33⟩,⟨state238_35,exclude238_35⟩,⟨state238_10,exclude238_10⟩] 0xe06010808420228080c08028080e06030200a06028080420210808480822200480010808484012000480812100480810808888010808a82812100a82028080888028080a82822200a028280804840280802a0a121002a02088086860088082a0a1a180220a088084840088084606090804602108086460108084606191804206108082420108084c44090802420121002c280b0804c440b0a024281210024200908100100908024202808100102808100104003e00022808024200908024044001c240008808242009000240409080240408809001008808420208880420012020424010800420210900420212020222012021001d088802220121002a280a88100220a8a0222812100222008881001008880222009080464409081002211910424409080222008881002208880222028080828028081002220a0082802808022200888022021090022000901022200880022020888022020901042400901068280880822021080864441080868281911048281080822020880900074001ca00028081000f2808100070880822023020100163020042024003c420230202000130200420240058420222201000222200484040074484022201001d2220048404000848404004100004000024204004024204003d001080000242040000242020a01000120a00222040088222020a01002220a0022204000422204001d002120809000f40080a080 (by decide +kernel)

def state238_37 : List Sig := [0xccffccffccffccffccffccffccffccffccffccffccffccffcccccccccccccccc,input 1,input 6,input 7,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude238_37 : Impossible true (goalAt 238) 5 state238_37.toFinset :=
  node_ok cuts238 [] 0xa800220008820220006800120004820120002400090002404088088c00220008804220004c0012000480412000480022000c040120002202090102202090104240090804244090808202220008202220004202120004202120002220088082404088082404121002420131002420208088800208088800108084800108084800 (by decide +kernel)

def state238_38 : List Sig := [0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc,0x33003300330033003300330033003300330033003300330000000000000000,input 6,input 7,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude238_38 : Impossible true (goalAt 238) 4 state238_38.toFinset :=
  node_ok cuts238 [] 0x2a00088002208088001a00048001208048001200088003010048001210022021a100220228080880030100880022200480012100480012100222010900222008800220008808a080208008200208088800108004200108084800 (by decide +kernel)

def state238_39 : List Sig := [0x33003300330033003300330033003300330033003300330000000000000000,input 1,input 6,input 7,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude238_39 : Impossible true (goalAt 238) 5 state238_39.toFinset :=
  node_ok cuts238 [⟨state238_38,exclude238_38⟩] 0xa800220008820220006800120004820120002400090002404088088c00220008804220004c0012000480412000480022000c040120002200088002202090102220090820000088808200208008202220004200108004202120004840088086840088084840090804c4009080a02022000c040220008880120004840120004240 (by decide +kernel)

def state238_40 : List Sig := [0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc,input 1,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000000000,input 6,input 7,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude238_40 : Impossible true (goalAt 238) 5 state238_40.toFinset :=
  node_ok cuts238 [⟨state238_38,exclude238_38⟩] 0xa80022000882022000680012000482012000480022000c04012000484008808684008808820222000c040220004202120004840120004840800004244121004840090804c40090802202088102202090088a02220008a02220004a02120004a0212000222009000240008808a080230008800228088800130004800128084800 (by decide +kernel)

def state238_41 : List Sig := [0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000000000,input 6,input 7,input 1,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude238_41 : Impossible true (goalAt 238) 6 state238_41.toFinset :=
  node_ok cuts238 [⟨state238_37,exclude238_37⟩,⟨state238_39,exclude238_39⟩,⟨state238_40,exclude238_40⟩,⟨state238_15,exclude238_15⟩,⟨state238_1,exclude238_1⟩] 0x2a08022022a00088002820088002a080a0802208088000880888001a08022021a00048001911048001a0806444120804800088084800090120004090002202090802400090102420090102202400a02202230102420230008800400a08800230120003220108800090808800130102420130004800191804800130106460120104800090804800088084240088002404088802200088082220088082404109002404400a0222008880242011910242080008464410910242008880222022808222022800880020a00880022808828022008880008880880012808222012800480010900480012808424012008480008880480030100480012000880030200880030100c0803010088001200048001911048401210022021a18022021911068601a1002202121002202191804840121002420131102420191804c44131002420121002420109004840109002220800042220109020000109002220121002220301004840208088800222008800301008880301008800121008800302008880108084800121004800302004840121004800222004800 (by decide +kernel)

def state238_42 : List Sig := [0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,input 7,input 1,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude238_42 : Impossible true (goalAt 238) 6 state238_42.toFinset :=
  node_ok cuts238 [] 0x8808c04030180220208808644419110220208808644419110220209000240009010220209080c04030110242009080646019180242009080646019180242008800220008808240408880242010910222008880c04020a00222008880424010900222008880424010900222022000c04030200a060120004840088086840088084840090804c4009080424008880424008880484022200c040121008880121004840222010002 (by decide +kernel)

def state238_43 : List Sig := [0xf0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0f0f0f0f0,input 5,input 6,input 7,input 1,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude238_43 : Impossible true (goalAt 238) 5 state238_43.toFinset :=
  node_ok cuts238 [] 0x2201088042203082061201048041203042060a8082202088282202088802a20088a0222020810820420818880c10810420410818480c08800220008808240408880242010900222030010c00430100420628000a0002808022020880862021a0a02202090802c20090a02420208088202208182420108084202108182420090002400090102202 (by decide +kernel)

def state238_44 : List Sig := [0xffffffff00000000ffffffff00000000ffffffff0000000000000000,input 5,input 6,input 7,input 1,input 2,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude238_44 : Impossible true (goalAt 238) 6 state238_44.toFinset :=
  node_ok cuts238 [⟨state238_43,exclude238_43⟩] 0xa82028080a0282808068201a0806828222002a0208808220a0880824200b080242809080242028080c0440908024201908024600908024000900024040880822200a880222808880222009080424408880222028080828008880222018880424008880220008800220209010e02028080c04028080a00028000a0200880822021880868280880848401a18048401a181000009082000009080424008880424008880820220808c04028080420210808c0801a0a06444 (by decide +kernel)

def state238_45 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,input 7,input 1,input 2,input 3,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude238_45 : Impossible true (goalAt 238) 7 state238_45.toFinset :=
  node_ok cuts238 [⟨state238_16,exclude238_16⟩,⟨state238_2,exclude238_2⟩,⟨state238_41,exclude238_41⟩,⟨state238_42,exclude238_42⟩,⟨state238_21,exclude238_21⟩,⟨state238_44,exclude238_44⟩,⟨state238_24,exclude238_24⟩] 0xe06008808220230100a08030100e06028200c0603010022020880900160880822023020064441911200061911064443020022020880a00050880822024001c64441911200041911064444001c2202088082a0a121002a02088086860088082a0a1a180220a0880848400880900271210048403010088803010100272220088803010048401210100272220088803020048401210100271210048403020088802220100278000e0002400084840121010027121004840400090027400082404800042400088082420090002404090802404088090026088084c44090802420121002c280b0804c440b0a0242812100242009080c44409080242030101002630100c44480000c04430100242009080c48409080242030200646019180c484191806460302002420090810026090802420400006460191810026191806460400002420090802202109002200090102220088002202088802202090104240090110027088802220121002a280a88100250a8a0222812100222008881002608880222009080464409081002511910424409080222008881002508880222030100828030101002520a00828030100222008881002508880222030200424010901002510900424030200222008881002508880222040004424010901002510900424040004222008881002440058820230101000f30101001630200c0804005900162818100234003c4202 (by decide +kernel)

def state238_46 : List Sig := [0xffccffccffccffccffccffccffccffccffccffccffccffccffccffccffccffcc,0xfcfcfcfcfcfcfcfcfffffffffffffffffcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc,input 6,input 7,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude238_46 : Impossible true (goalAt 238) 4 state238_46.toFinset :=
  node_ok cuts238 [] 0x88088202301802202088084202120a0220230000c00030100420209000240008809002b208088208208082420108084208108084802088802220088a02420088082204088082402208088204208084840120004800108088280 (by decide +kernel)

def state238_47 : List Sig := [0xfcfcfcfcfcfcfcfcfffffffffffffffffcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc,input 1,input 6,input 7,input 3,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude238_47 : Impossible true (goalAt 238) 5 state238_47.toFinset :=
  node_ok cuts238 [⟨state238_46,exclude238_46⟩] 0x220220808c060088082202108084828088082a0208808220a088088a0220808820a20808480012000480810808c00030000c040108082202088102202090084244121020000121008202208108202220284202108104202120202220090002400088090007090802c20090a02420208088808208082420108084808108084808 (by decide +kernel)

def state238_48 : List Sig := [0xffccffccffccffccffccffccffccffccffccffccffccffccffccffccffccffcc,input 1,0xf0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 6,input 7,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude238_48 : Impossible true (goalAt 238) 5 state238_48.toFinset :=
  node_ok cuts238 [⟨state238_46,exclude238_46⟩] 0x220228010c06008808220210808482808808c00030000c0401080824000900024040880882022080882060908046021080842061080824200b0802428090802202090102202090108206208308206220184202108204202120082228090820000090802220088082404088082404220108804208184840120004800108088880 (by decide +kernel)

def state238_49 : List Sig := [0xf0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 6,input 7,input 1,input 3,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude238_49 : Impossible true (goalAt 238) 6 state238_49.toFinset :=
  node_ok cuts238 [⟨state238_47,exclude238_47⟩,⟨state238_48,exclude238_48⟩] 0x38180220208808820628200a00438180a0803018082060880822021a0a022020880842021911042021a0a06444120a042020880822020a82848400a80822021a18022020a8286860088282202121002202220304840220108206222008804220308880220308206121008206120208880120004202121004800120204840120204202222004202088084240088002404088802200088082220088082404109002404400b022200888048400a8a02a20800042a28088a0484008880222020818222020810880c20a00820420818828020818880c08880880c10808222010800480810900420010808424010808480808880480840038222008880242011910242080000464410910242008880222030100420230000820631200c00030100c4803010082061080842020901100070900022020908024000901024200901022024001c22021311024200908048400b0a02c20131102c28090a0484009080242020818242020808c0404002c820220819000d20818c040090802420118182420118084202191804202118186460108184202090804202 (by decide +kernel)

def state238_50 : List Sig := [0xf0f0f0f000000000f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f00000000,input 5,input 6,input 7,input 1,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude238_50 : Impossible true (goalAt 238) 5 state238_50.toFinset :=
  node_ok cuts238 [] 0x230008c002302086021200048001202042020b0002400090202400088802a20088a02220218008600218088c0810800420010808480809800240009008240030000c00030100420209000a4002808024000900064001a0a024000908024280b0802420088804240088802420208088202280808602090804202190804202088082400090802400 (by decide +kernel)

def state238_51 : List Sig := [0xffffffff00000000ffffffffffffffffffffffff00000000ffffffff00000000,input 5,input 6,input 7,input 1,input 2,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude238_51 : Impossible true (goalAt 238) 6 state238_51.toFinset :=
  node_ok cuts238 [⟨state238_50,exclude238_50⟩] 0xa82028080a0282808048001200048081080848401a18068601210048401a18068601210024200b080242809080242028080c04409080460210808420610808a4800908024202820200000908024204000022200a880222808880222009080424408880222028080828008880420010800420212020424008880222010900424008880222010900c00030000c04010808a02030100a020220a0682810808682810808220220808820228080c0401a0a042021a0a04202 (by decide +kernel)

def state238_52 : List Sig := [0xffffffffffffffff00000000000000000000000000000000,input 6,input 7,input 1,input 2,input 3,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude238_52 : Impossible true (goalAt 238) 7 state238_52.toFinset :=
  node_ok cuts238 [⟨state238_49,exclude238_49⟩,⟨state238_51,exclude238_51⟩,⟨state238_4,exclude238_4⟩] 0xe06008808220230100a08030100e06028200c060301002202088086828088082202108086444108086828191104828108082202088082a0a121002a02088086860088082a0a1a180220a08808484008809002312100484030100888030101002322200888030100484012100480822200480010808484012000480812100480810808888010808240480008240008808242009000240409080240408809002d088084c44090802420121002c280b0804c440b0a0242812100242009080c44409080242030101002d30100c4444003cc044301002420090804606090804602108086460108084606191804206108082420108082202109002200090102220088002202088802202090104240090110023088802220121002a280a881002a0a8a0222812100222008881002d08880222009080464409081002a11910424409080222008881002a08880222030100828030101002a20a00828030100222008880420208880420012020424010800420210900420212020222012021001640058c00030101000f3010100161080842022820100072820022024003c22022820200012820022024001c22022220100022220048404008c4840222010023222004840400084840400b50000400002420400b424204003d002d80000242040000242020a01000120a002220400a8222020a01002a20a00222040004222040059002920809000f4009cc080 (by decide +kernel)

def state238_53 : List Sig := roots 238
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude238_53 : Impossible true (goalAt 238) 8 state238_53.toFinset :=
  node_ok cuts238 [⟨state238_5,exclude238_5⟩,⟨state238_17,exclude238_17⟩,⟨state238_28,exclude238_28⟩,⟨state238_32,exclude238_32⟩,⟨state238_36,exclude238_36⟩,⟨state238_45,exclude238_45⟩,⟨state238_52,exclude238_52⟩] 0x80018c04010808c00040058820230200c00080014c04030200c04040058820210808420280010a02008808a0004001c820228200a0008000ca02028200a0204001c82020880822024005868280880822024001c4202191104202800086828191104828400584202088082202400088808121008800400088202222008800400088808222008808400088202121008202400084808222004800400084202121004800400084808121004808400084202222004202400082a0a121002a024000822021a1802202400082a0a1a180220a400082202121002202400008606090808602400008202400008202400008606800048206400008202090808202400004606090804602400004202191804202400004606191804206400004202090804202400002404800002400400002202090802400400002404090802404400002202400002202400084c440908024204000848400b0a02c20400084c440b0a0242840008484009080242040004820208880820040004880820a00820040004820220a0082024000488080888088084000442020888042004000448081090042004000442021090042024000448080888048084000422021090022004000424040888022004000422020888022024000424041090024044000900020888022204000848400a8a02a204000900010a8a02228400084840088802220400010000088802220400002420119102420400010001119104244400002420088802220 (by decide +kernel)

theorem lower238 : Claim 238 9 :=
  fromSearch 286287184 (by decide +kernel) exclude238_53

open PEqualNP.CircuitLowerBounds

def graph : Sig := goalAt 255
theorem graph_proper : proper graph := by unfold proper; decide +kernel

def edgeList : List Nat := [0, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7]
def target (x : Fin 8 → Bool) : Bool :=
  decide (∃ i < edgeList.length / 2,
    (List.ofFn x).getD (edgeList.getD (2*i) 0) false = true ∧
    (List.ofFn x).getD (edgeList.getD (2*i+1) 0) false = true)

-- The three products cover the posted edges.
def smallCircuit : Circuit := ⟨[⟨.or,[0,7]⟩, ⟨.or,[1,2]⟩, ⟨.or,[1,3]⟩, ⟨.or,[4,5]⟩, ⟨.or,[4,10]⟩, ⟨.or,[6,7]⟩, ⟨.or,[6,11]⟩, ⟨.and,[14,8]⟩, ⟨.and,[9,5]⟩, ⟨.and,[12,13]⟩, ⟨.or,[15,16]⟩, ⟨.or,[18,17]⟩],19⟩

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

def lowRow (i : Fin 8) : Row := Fin.ofNat 256 (1 <<< ([4, 5, 5, 6, 0, 0, 0, 1] : List Nat).getD i.val 0)
def highRow (i : Fin 8) : Row := Fin.ofNat 256 ((1 <<< i.val) ||| (1 <<< ([4, 5, 5, 6, 0, 0, 0, 1] : List Nat).getD i.val 0))

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
  (ruleFor 255 lower238 none (by decide +kernel)).property 10 eightInputs
    (by decide +kernel) (by decide +kernel)


end PEqualNP.Outside.L_meta_28862

open PEqualNP.Outside.L_meta_28862 in
theorem PEqualNP.Outside.L_meta_28862 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o fit _ correct
  exact replaceShort lowerGraph gates o fit correct

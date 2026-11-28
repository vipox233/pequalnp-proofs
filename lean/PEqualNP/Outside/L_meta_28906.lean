import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_28906

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
  (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 2 &&& x 5) ||| (x 0 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 0 &&& x 7) ||| (x 2 &&& x 7) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)

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


def cuts196 : Cuts (goalAt 196) := []

def state196_0 : List Sig := roots 196
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude196_0 : Impossible true (goalAt 196) 3 state196_0.toFinset :=
  node_ok cuts196 [] 0x30100440430000840430200c00030100c08030100840411010440421010444021000c04021200840021010848021010c04011100444011010848011000c08011100440011010444011010c080212008480 (by decide +kernel)

theorem lower196 : Claim 196 4 :=
  fromSearch 570426880 (by decide +kernel) exclude196_0

theorem lower212 : Claim 212 5 :=
  fromLift 5 16 570885632 lower196 (by decide +kernel)


theorem lower197 : Claim 197 5 :=
  fromLift 5 1 1542 lower196 (by decide +kernel)


def cuts145 : Cuts (goalAt 145) := []

def state145_0 : List Sig := roots 145
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude145_0 : Impossible true (goalAt 145) 3 state145_0.toFinset :=
  node_ok cuts145 [] 0x240401101240008101242009000240409080240408101044041101204041110204009010206008100204048180204049010044401110044048180044009080044401100044041110044049080206008180 (by decide +kernel)

theorem lower145 : Claim 145 4 :=
  fromSearch 4 (by decide +kernel) exclude145_0

theorem lower149 : Claim 149 5 :=
  fromLift 5 4 1796 lower145 (by decide +kernel)


def rule213_0 : {c : Cut // CutGood (goalAt 213) c} :=
  ruleFor 213 lower209 none (by decide +kernel)

def rule213_1 : {c : Cut // CutGood (goalAt 213) c} :=
  ruleFor 213 lower212 none (by decide +kernel)

def rule213_2 : {c : Cut // CutGood (goalAt 213) c} :=
  ruleFor 213 lower197 none (by decide +kernel)

def rule213_3 : {c : Cut // CutGood (goalAt 213) c} :=
  ruleFor 213 lower149 none (by decide +kernel)

def cuts213 : Cuts (goalAt 213) := [rule213_0,rule213_1,rule213_2,rule213_3]

def state213_0 : List Sig := roots 213
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude213_0 : Impossible true (goalAt 213) 6 state213_0.toFinset :=
  node_ok cuts213 [] 0x4000cc04010404c0004000c810130200c0004000cc04030200c0404000c81011040441014000890100440490004000881012420090004000890102420090104000881010440411014000c54140440411014000c41014000c41014000c54144000c44144000c41010440411014000084041110084004000081012120084004000084042120084044000081011110081014000c44042120044004000c41011110044004000c44041110044044000c41012120041014000815051110015014000811011514011014000815051514011054000811011110011014000481010444081004000484042060081004000481012060081014000484040444084044000c41010444041004000c44041050041004000c41011050041014000c4404044404404400081101105001100400089080044401100400081101044401101400089080105004140400010000044401110400004440054501510400010001054501114400004440044401110 (by decide +kernel)

theorem lower213 : Claim 213 7 :=
  fromSearch 1540 (by decide +kernel) exclude213_0

def cuts150 : Cuts (goalAt 150) := []

def state150_0 : List Sig := roots 150
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude150_0 : Impossible true (goalAt 150) 3 state150_0.toFinset :=
  node_ok cuts150 [] 0x240009000240401202210008400210109010058081202048181202218108404210188404048001200048089080048401610048501210 (by decide +kernel)

theorem lower150 : Claim 150 4 :=
  fromSearch 536938304 (by decide +kernel) exclude150_0

def cuts210 : Cuts (goalAt 210) := []

def state210_0 : List Sig := roots 210
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude210_0 : Impossible true (goalAt 210) 3 state210_0.toFinset :=
  node_ok cuts210 [] 0x30000c000301009010240009000240401202048085202049081202048409010301081210048405210049401210048001200048089080 (by decide +kernel)

theorem lower210 : Claim 210 4 :=
  fromSearch 1191247936 (by decide +kernel) exclude210_0

def rule214_0 : {c : Cut // CutGood (goalAt 214) c} :=
  ruleFor 214 lower212 none (by decide +kernel)

def rule214_1 : {c : Cut // CutGood (goalAt 214) c} :=
  ruleFor 214 lower196 none (by decide +kernel)

def rule214_2 : {c : Cut // CutGood (goalAt 214) c} :=
  ruleFor 214 lower212 (some (0,input 4,input 7)) (by decide +kernel)

def rule214_3 : {c : Cut // CutGood (goalAt 214) c} :=
  ruleFor 214 lower150 none (by decide +kernel)

def rule214_4 : {c : Cut // CutGood (goalAt 214) c} :=
  ruleFor 214 lower210 none (by decide +kernel)

def cuts214 : Cuts (goalAt 214) := [rule214_0,rule214_1,rule214_2,rule214_3,rule214_4]

def state214_0 : List Sig := [0xffff0000ffff0000ffff0000ffff0000cccc0000cccc0000cccc0000cccc,0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 7,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude214_0 : Impossible true (goalAt 214) 4 state214_0.toFinset :=
  node_ok cuts214 [] 0x30008c00230108440414800120011818120011000440011010848021008840221018444005800120004810120024000120211010520204808120204818160204808120204a009002048090002 (by decide +kernel)

def state214_1 : List Sig := [0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 7,input 2,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude214_1 : Impossible true (goalAt 214) 5 state214_1.toFinset :=
  node_ok cuts214 [⟨state214_0,exclude214_0⟩] 0xc04211010c00221018c08030008c04230200c042210184404110105250110104404048404606118105250118184406048404404110105414048081202110105242148085414149084414110101202048090001048081202210189080240090001242001280210181202048081210800001200400041202048001210048081202400050001400044404212004400302004440110004404111004404302008480212001606111001602048085450048081606151401206048084440048088406111008402301088480210088406212008406301084440111001614111001610048404642048401614119081214048404440048410000400008404 (by decide +kernel)

def state214_2 : List Sig := [0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0,input 2,input 6,input 1,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude214_2 : Impossible true (goalAt 214) 5 state214_2.toFinset :=
  node_ok cuts214 [] 0x900024000901004808120211010441404808120205818160604808860421010840621010120004800120224200460411010440611010121005850161404840121005850161404840440421010c04011010c0802101090102101090100581812020581812021101044404000c8480210109010210109010 (by decide +kernel)

def state214_3 : List Sig := [0xffffffffffffffff0000000000000000f0f0f0f0f0f0f0f0,input 2,input 7,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude214_3 : Impossible true (goalAt 214) 4 state214_3.toFinset :=
  node_ok cuts214 [] 0x34000c00030040c00004800120004808908030800c00030008c00011800440011008440011000540005818440011000c00021010440011010120215010120211010440611810440411010c00021010c000212004400110104400 (by decide +kernel)

def state214_4 : List Sig := [0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 2,input 7,input 1,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude214_4 : Impossible true (goalAt 214) 5 state214_4.toFinset :=
  node_ok cuts214 [⟨state214_3,exclude214_3⟩] 0x440421010c0801101200001101044044000c120214808441404808120221010841404808120205818160604808460411010440611010120004800120224200860421010840621010121005850161404840121005850161404840901011010c080110108480058181202058181202210108480240504440 (by decide +kernel)

def state214_5 : List Sig := [0xcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcccccccccccccccccccccccccccccccc,input 2,input 7,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude214_5 : Impossible true (goalAt 214) 4 state214_5.toFinset :=
  node_ok cuts214 [] 0x30008c002301084404048085202110501202048089002210501202110004400110108680058081202048181202210008400210104440118104404110184404048001200048090001218108404210188404048401610048501210 (by decide +kernel)

def state214_6 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000000000000000000,input 2,input 7,input 1,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude214_6 : Impossible true (goalAt 214) 5 state214_6.toFinset :=
  node_ok cuts214 [⟨state214_5,exclude214_5⟩] 0x440421010c080110101202148084414048081202210108414048084604110104406110101200048001202242008604210108406210101210058401214048404400110004404302001602048081206048088400210104440302004404302004404242001202242001202400001210800001210240408480 (by decide +kernel)

def state214_7 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0000000000000000,input 6,input 7,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude214_7 : Impossible true (goalAt 214) 4 state214_7.toFinset :=
  node_ok cuts214 [] 0x250008400210408400150004400110404400048001200048089080218008400210088400118004400110084400110008400301004400111001202151001202111001210119001210240408400301008400212004400111004400 (by decide +kernel)

def state214_8 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,input 7,input 1,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude214_8 : Impossible true (goalAt 214) 5 state214_8.toFinset :=
  node_ok cuts214 [⟨state214_7,exclude214_7⟩] 0x120230100c05004808120214908524204808120214908524204808160204808120604808444030100848011100848011100444021202000011100444040010120004800120224200121005840121404840121030100c04204840121014940525004840121014940525004840840430100c080241404404 (by decide +kernel)

def state214_9 : List Sig := [0xccccccccccccccccffffffffffffffffcccccccccccccccccccccccccccccccc,input 6,input 7,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude214_9 : Impossible true (goalAt 214) 4 state214_9.toFinset :=
  node_ok cuts214 [] 0x4808900230140120204808520211050120205808120204818120221008840221018444011000440011010848030000c000301004404048001200048090001048401610048501210210108404210181210118104404110184404 (by decide +kernel)

def state214_10 : List Sig := [0xffffffffffffffff00000000000000000000000000000000,input 6,input 7,input 1,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude214_10 : Impossible true (goalAt 214) 5 state214_10.toFinset :=
  node_ok cuts214 [⟨state214_9,exclude214_9⟩] 0x120230100c05004808120214808441404808160204808120604808444030100848011100440011000440421200120004800120224200121005840121404840121030100c04204840460411010440611010c00030100440424200120224200120221200444021200444040000121080000121021010c080 (by decide +kernel)

def state214_11 : List Sig := roots 214
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude214_11 : Impossible true (goalAt 214) 6 state214_11.toFinset :=
  node_ok cuts214 [⟨state214_1,exclude214_1⟩,⟨state214_2,exclude214_2⟩,⟨state214_4,exclude214_4⟩,⟨state214_6,exclude214_6⟩,⟨state214_8,exclude214_8⟩,⟨state214_10,exclude214_10⟩] 0x80014c04011010c0004000c840430200c00080010c04030200c0404000c84041101044044000490100480890004000484042420090004000490102420090104000484040480812024000454140480812024000444041490852024000454141490844144000444040480812028000c84041110084004001090102120084008000884042120084044001090101110090104000c440421200440040010c0801110044008000444041110044044000cc080212008480400041606111001602400041202151401202400041606151401206400041202111001202400008606048408604400008404400008404400008606800008406400008404048408404400004606048404604400004404149404404400004606149404406400004404048404404400001202400041200400009080048401200400001202048401202400009080400009080400004642048401210400004440058501610400004642058501214400004440048401210 (by decide +kernel)

theorem lower214 : Claim 214 7 :=
  fromSearch 570492480 (by decide +kernel) exclude214_11

theorem lower147 : Claim 147 5 :=
  fromLift 5 2 68 lower145 (by decide +kernel)


def cuts83 : Cuts (goalAt 83) := []

def state83_0 : List Sig := roots 83
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude83_0 : Impossible true (goalAt 83) 3 state83_0.toFinset :=
  node_ok cuts83 [] 0x4404410104908110110c0441011040c4101048001200048081101104004100104041110044001100044041202044401210105081110 (by decide +kernel)

theorem lower83 : Claim 83 4 :=
  fromSearch 68 (by decide +kernel) exclude83_0

def rule211_0 : {c : Cut // CutGood (goalAt 211) c} :=
  ruleFor 211 lower209 none (by decide +kernel)

def rule211_1 : {c : Cut // CutGood (goalAt 211) c} :=
  ruleFor 211 lower193 none (by decide +kernel)

def rule211_2 : {c : Cut // CutGood (goalAt 211) c} :=
  ruleFor 211 lower147 (some (3,input 0,input 1)) (by decide +kernel)

def rule211_3 : {c : Cut // CutGood (goalAt 211) c} :=
  ruleFor 211 lower147 (some (1,input 0,input 1)) (by decide +kernel)

def rule211_4 : {c : Cut // CutGood (goalAt 211) c} :=
  ruleFor 211 lower147 none (by decide +kernel)

def rule211_5 : {c : Cut // CutGood (goalAt 211) c} :=
  ruleFor 211 lower83 none (by decide +kernel)

def rule211_6 : {c : Cut // CutGood (goalAt 211) c} :=
  ruleFor 211 lower210 none (by decide +kernel)

def rule211_7 : {c : Cut // CutGood (goalAt 211) c} :=
  ruleFor 211 lower147 (some (2,input 1,input 7)) (by decide +kernel)

def rule211_8 : {c : Cut // CutGood (goalAt 211) c} :=
  ruleFor 211 lower147 (some (1,input 1,input 7)) (by decide +kernel)

def cuts211 : Cuts (goalAt 211) := [rule211_0,rule211_1,rule211_2,rule211_3,rule211_4,rule211_5,rule211_6,rule211_7,rule211_8]

def state211_0 : List Sig := [0xffffffffffffffffffffffffffffffffeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 7,input 0,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude211_0 : Impossible true (goalAt 211) 4 state211_0.toFinset :=
  node_ok cuts211 [] 0x10404810130108410114840410110404121004404410104908110104404810104a001101048001200044050001104044102104048180044041102044041201204048102204044142044409010 (by decide +kernel)

def state211_1 : List Sig := [0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 7,input 0,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude211_1 : Impossible true (goalAt 211) 4 state211_1.toFinset :=
  node_ok cuts211 [] 0xc00030000c040104041101104041242044049000240009010044044101104084101206001101044081101048048100204008180240404101148404101048401200048001101242001110044404142048408101 (by decide +kernel)

def state211_2 : List Sig := [0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 0,input 4,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude211_2 : Impossible true (goalAt 211) 5 state211_2.toFinset :=
  node_ok cuts211 [⟨state211_0,exclude211_0⟩,⟨state211_1,exclude211_1⟩] 0xc04010404c00020404c08030000c04030200c04020404410110404901004404900020404908024000901024200901020404110104405000304404110110404524210405000114908124210404110104404810110508810124040818220408810120608810124040414224040410120608410130200414210408410110508410130200818230200110110508110104809000104408110140004110104808414204805000240000111020404121020404901080004901020406000020404901004840121010404121010404c08014940521010404525010404c080048401210044050001048009080048401200044041210044049080400049080 (by decide +kernel)

def state211_3 : List Sig := [0xffffffffffffffff0000000000000000aaaaaaaaaaaaaaaa,input 0,input 7,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude211_3 : Impossible true (goalAt 211) 4 state211_3.toFinset :=
  node_ok cuts211 [] 0x34000c00030040c00004800120004808110130800c00030008c00010400510004404410010400430010408410010400c00020404410004404120204404410110404410310c04410110404c00020404c000044404100104044100 (by decide +kernel)

def state211_4 : List Sig := [0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 0,input 7,input 1,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude211_4 : Impossible true (goalAt 211) 5 state211_4.toFinset :=
  node_ok cuts211 [⟨state211_0,exclude211_0⟩,⟨state211_3,exclude211_3⟩] 0x410120404c08010406000110404410140010110110404124204404110120404908004404120204404110104808430110404410310404120004800120204404830120404810320404121040002000004840901010404c080104048180044041202044041202206001210206081210204048180400141110 (by decide +kernel)

def state211_5 : List Sig := [0x5555555555555555555555555555555544444444444444444444444444444444,input 0,input 7,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude211_5 : Impossible true (goalAt 211) 4 state211_5.toFinset :=
  node_ok cuts211 [] 0x410120404c04210404110110404124204404110120404128004404410010400410104440110004400110104808810020400810104440121010404125010404120004800120204404121020404c042204044142 (by decide +kernel)

def state211_6 : List Sig := [0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 7,input 0,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude211_6 : Impossible true (goalAt 211) 5 state211_6.toFinset :=
  node_ok cuts211 [⟨state211_0,exclude211_0⟩,⟨state211_5,exclude211_5⟩] 0xc0421040441012040cc08030008c04230200c0422040c410110404525010404410104840430310c04525010c0c41030484041011040500080440411011040452421040500011490812421040411010440500010440411012040c90802400900012420012802040c110104404121004404120040004120204800121004808120240004110104404410104440410030200414010400410110500410130200111004440110110500110004808111004400110104440110104808414004808810304440810230108818020408810320600810330108111004442000104440111004840434204842000010d084142048401110044410007400008101 (by decide +kernel)

def state211_7 : List Sig := roots 211
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude211_7 : Impossible true (goalAt 211) 6 state211_7.toFinset :=
  node_ok cuts211 [⟨state211_2,exclude211_2⟩,⟨state211_4,exclude211_4⟩,⟨state211_6,exclude211_6⟩] 0x40010c04010404c00040010810130200c00040010c04030200c04040010810110404410140004901004404900040004810124200900040004901024200901040004810104404110140011000404404110140010410114908410140011000114908124240010410104404110140000830304840830140000810140000810140000830380008810340000810104840810140010430304840430140010410114940410140010430314940410340010410104840410140000120240004120040000110104840120040000120204840120240000110140000110140014810104440810040018901020600810080004810120600810140014901004440111040010410104440410040010c08010500410040010410110500410140010c08004440111040004110110500110040004120204440110040004110104440110140004120210500120240001000004440111040000121010d08121040002000010d084142400001210044401110 (by decide +kernel)

theorem lower211 : Claim 211 7 :=
  fromSearch 68 (by decide +kernel) exclude211_7

theorem lower151 : Claim 151 6 :=
  fromLift 6 2 1860 lower149 (by decide +kernel)


def cuts85 : Cuts (goalAt 85) := []

def state85_0 : List Sig := roots 85
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude85_0 : Impossible true (goalAt 85) 3 state85_0.toFinset :=
  node_ok cuts85 [] 0x44044101110501101110004400110104101054041101044141101104004100104044404044001100044044140044401510044501110 (by decide +kernel)

theorem lower85 : Claim 85 4 :=
  fromSearch 1540 (by decide +kernel) exclude85_0

theorem lower87 : Claim 87 5 :=
  fromLift 5 2 1604 lower85 (by decide +kernel)


def rule215_0 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower213 none (by decide +kernel)

def rule215_1 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower214 none (by decide +kernel)

def rule215_2 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower211 none (by decide +kernel)

def rule215_3 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower211 (some (0,input 1,input 4)) (by decide +kernel)

def rule215_4 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower214 (some (3,input 1,input 4)) (by decide +kernel)

def rule215_5 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower211 (some (3,input 1,input 4)) (by decide +kernel)

def rule215_6 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower151 (some (3,input 1,input 4)) (by decide +kernel)

def rule215_7 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower197 none (by decide +kernel)

def rule215_8 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower213 (some (2,input 4,input 7)) (by decide +kernel)

def rule215_9 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower196 none (by decide +kernel)

def rule215_10 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower193 none (by decide +kernel)

def rule215_11 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower211 (some (2,input 1,input 7)) (by decide +kernel)

def rule215_12 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower214 (some (1,input 1,input 7)) (by decide +kernel)

def rule215_13 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower211 (some (1,input 1,input 7)) (by decide +kernel)

def rule215_14 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower85 none (by decide +kernel)

def rule215_15 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower87 none (by decide +kernel)

def rule215_16 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower213 (some (3,input 4,input 7)) (by decide +kernel)

def rule215_17 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower213 (some (1,input 4,input 6)) (by decide +kernel)

def rule215_18 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower213 (some (1,input 4,input 7)) (by decide +kernel)

def rule215_19 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower213 (some (0,input 4,input 7)) (by decide +kernel)

def rule215_20 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower151 (some (1,input 1,input 7)) (by decide +kernel)

def rule215_21 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower213 (some (2,input 6,input 7)) (by decide +kernel)

def rule215_22 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower151 none (by decide +kernel)

def rule215_23 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower211 (some (3,input 4,input 6)) (by decide +kernel)

def rule215_24 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower211 (some (2,input 4,input 6)) (by decide +kernel)

def rule215_25 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower149 none (by decide +kernel)

def rule215_26 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower211 (some (1,input 4,input 6)) (by decide +kernel)

def rule215_27 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower214 (some (1,input 4,input 6)) (by decide +kernel)

def rule215_28 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower147 (some (3,input 1,input 4)) (by decide +kernel)

def rule215_29 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower211 (some (3,input 4,input 7)) (by decide +kernel)

def rule215_30 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower211 (some (2,input 4,input 7)) (by decide +kernel)

def rule215_31 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower214 (some (1,input 4,input 7)) (by decide +kernel)

def rule215_32 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower211 (some (1,input 4,input 7)) (by decide +kernel)

def rule215_33 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower211 (some (0,input 4,input 7)) (by decide +kernel)

def rule215_34 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower214 (some (3,input 4,input 7)) (by decide +kernel)

def rule215_35 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower211 (some (3,input 6,input 7)) (by decide +kernel)

def rule215_36 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower211 (some (2,input 6,input 7)) (by decide +kernel)

def rule215_37 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower214 (some (1,input 6,input 7)) (by decide +kernel)

def rule215_38 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower213 (some (1,input 6,input 7)) (by decide +kernel)

def rule215_39 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower211 (some (1,input 6,input 7)) (by decide +kernel)

def rule215_40 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower149 (some (3,input 2,input 7)) (by decide +kernel)

def rule215_41 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower211 (some (0,input 6,input 7)) (by decide +kernel)

def rule215_42 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower214 (some (3,input 6,input 7)) (by decide +kernel)

def rule215_43 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower197 (some (1,input 0,input 2)) (by decide +kernel)

def rule215_44 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower147 (some (1,input 1,input 7)) (by decide +kernel)

def rule215_45 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower213 (some (3,input 6,input 7)) (by decide +kernel)

def cuts215 : Cuts (goalAt 215) := [rule215_0,rule215_1,rule215_2,rule215_3,rule215_4,rule215_5,rule215_6,rule215_7,rule215_8,rule215_9,rule215_10,rule215_11,rule215_12,rule215_13,rule215_14,rule215_15,rule215_16,rule215_17,rule215_18,rule215_19,rule215_20,rule215_21,rule215_22,rule215_23,rule215_24,rule215_25,rule215_26,rule215_27,rule215_28,rule215_29,rule215_30,rule215_31,rule215_32,rule215_33,rule215_34,rule215_35,rule215_36,rule215_37,rule215_38,rule215_39,rule215_40,rule215_41,rule215_42,rule215_43,rule215_44,rule215_45]

def state215_0 : List Sig := [0xffffffffffffffffffffffffffffffff33330000333300003333000033330000,input 7,input 4,input 0,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_0 : Impossible true (goalAt 215) 6 state215_0.toFinset :=
  node_ok cuts215 [] 0xd05010404410124040c08024040d05030200905024040410110404525010404410104840541404840525015050521004840410110404440421200440010404444011000440411100440410404848010404160411100160004800545004800160415140120404800444004800941411100941024040848024040941421200901424040444024040161411100121404840545004840161415140161004840444004840410104440410011010414010400410110500410111010111011011000a0444011101110015140544100090545011141110011100444013011050013000480011100480013010444012010480041400480100090444011102404081802404100092060081802404011100444100091050041400484011100444100090444011100484041400484054140480012001040452401480054141490054141040412000480090100480012004001c90802420090102420090104001c12000480012100480012004000090800440412102420012104000012000480100084001c8101 (by decide +kernel)

def state215_1 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0000000000000000,input 6,input 7,0x3333000033330000333300003333000033330000333300003333000033330000,input 4,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_1 : Impossible true (goalAt 215) 5 state215_1.toFinset :=
  node_ok cuts215 [] 0x1300048001201048008500210008401210004500110004401110001200210009410048001200110005410048001110105001110048401101048408400250408400048404400150404400110008400301004400105001110105001110111001200149001200111001210149401210204048400301008400104044400111004400 (by decide +kernel)

def state215_2 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,input 7,0x3333000033330000333300003333000033330000333300003333000033330000,input 4,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_2 : Impossible true (goalAt 215) 6 state215_2.toFinset :=
  node_ok cuts215 [⟨state215_1,exclude215_1⟩] 0x5800120004810120011100c04021200444021200444011100848080000444011101000504440151004450111004c00120004804120004440c04020600111004440414010500111004440414010500111004800c04034140120004800524014900120004800524014900120004840121405840121004440414004440121004404121030100d05004840121014940525004840121014940525004840810130100c080241404101 (by decide +kernel)

def state215_3 : List Sig := [0x3333000033330000ffffffffffffffff33330000333300003333000033330000,input 6,input 7,input 4,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_3 : Impossible true (goalAt 215) 5 state215_3.toFinset :=
  node_ok cuts215 [] 0x5800120004810120025040901024050901011000440011010410104440151004450111004c00120004804120004440901020600111010400410010404440404800c04024040120004800520015050120030000c000301004101048401214058401210044404140044401210044041200048401200204048101240401210048404101148404101 (by decide +kernel)

def state215_4 : List Sig := [0xffffffffffffffff00000000000000000000000000000000,input 6,input 7,0x3333000033330000333300003333000033330000333300003333000033330000,input 4,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_4 : Impossible true (goalAt 215) 6 state215_4.toFinset :=
  node_ok cuts215 [⟨state215_3,exclude215_3⟩] 0x5800120004810120011100c04021200444011000440011010410104440151004450111004c00120004804120004440c04020600111010400410010404440404800c04034140120004800520015050120004840121405840121004440414004440121004404121030100d05004840121010404521010404c00030100410121200444021200444020600111020600111024a00120024a0012004001c121080000121020404c080 (by decide +kernel)

def state215_5 : List Sig := [0x3333000033330000333300003333000033330000333300003333000033330000,input 4,input 0,input 2,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_5 : Impossible true (goalAt 215) 7 state215_5.toFinset :=
  node_ok cuts215 [⟨state215_0,exclude215_0⟩,⟨state215_2,exclude215_2⟩,⟨state215_4,exclude215_4⟩] 0x80008c04010404c00040018810130200c00080004c04030200c0404001881011040441014001484041110084004001481012120084004001484042120084044001481011110081014001444042120044004001441011110044004001444041110044044001441012120041014001416041110016004001412001514012004001416041514012044001412001110012004001081010444081004001084042060081004001081012060081014001084040444084044001041010444041004001044041050041004001041011050041014001044040444044044001500050444011104001444400545015104001500040545011144001444400444011104001013011050013004001012000444012004001013010444012014001012001050012004001c90100480012004001c810124a0092004001c901024a0090104001c81010480012004001854140480012004001c41011490052004001c54141490054144001841010480012004001c90100484012104001c81014001c81014001c90108000090104001c81010484081014001854140484012104001c41011494041014001c54141494052104001841010484041014001454500484012104001444400585012144001454500585016104001444400484012104001011100484011104001041404001041404001011104001011104001041400484012104000100004000c1101 (by decide +kernel)

def state215_6 : List Sig := [0xffffffffffffffffffffffffffffffffffffccccffffccccffffccccffffcccc,input 4,0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 7,input 0,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_6 : Impossible true (goalAt 215) 6 state215_6.toFinset :=
  node_ok cuts215 [] 0x410130008c04210404410110c0c430310404410110c0c43031040444001100044041040484022100884062040c161004840121404840160204808120604808444011908464211100410010400410111010111005440111404440810220408810321018111004840434204440130204808120304808414004440111010500901040021000804808410115050410104808900204a0012020484012020440c1101 (by decide +kernel)

def state215_7 : List Sig := [0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 6,0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_7 : Impossible true (goalAt 215) 5 state215_7.toFinset :=
  node_ok cuts215 [] 0x16100484012140484084022100884062040c541015040541421200168011100444004a00111005440111404440111004840414204440810220408810321018111014440414004440138004440111004a0081012040481034004452100484012500484052422040c44142040c4101048401280048408414044041101149088103 (by decide +kernel)

def state215_8 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 4,0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 0,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_8 : Impossible true (goalAt 215) 6 state215_8.toFinset :=
  node_ok cuts215 [⟨state215_7,exclude215_7⟩] 0x525010404410104840430310c04525010c0c410304840410110404c0421040441012040c541430008c0421505054142040c410110404440421200440010404444011000440411100440410404848010404161411100161004840464204840161411908121404840444004841000711100444004a00545015141000a15140545004a0044401110084061110084022040c54502100884061514084062040c44402040c410104440410011010414010400410110500410111010111011011000a04440111011100151405441000905450111411100111004441000904440111004840434204841000910d08414204840111004441000710500414004a00111004441000904440111004a0041401050081031050081022101811102040881030444081032101841402101881034001c810140000121020404810304840810340001001240000541404a0054141040500071040454148000054141040412801040412104003812104001c128004a00121004a0012104001d00072105100104003c1101 (by decide +kernel)

def state215_9 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 4,input 7,0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 0,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_9 : Impossible true (goalAt 215) 6 state215_9.toFinset :=
  node_ok cuts215 [] 0x1040443011040c410110404c0803020041011040454141505041011100044001101041010584012100485012101110084802120044401110054501514044401110054501514044401040041001040444040444015100445011100444012101050811100444081802060011101050011100444041401050011100444041404002012100484100002404081031505041011505041010484090800484100074003c908004a001101 (by decide +kernel)

def state215_10 : List Sig := [0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000,input 4,0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 0,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_10 : Impossible true (goalAt 215) 6 state215_10.toFinset :=
  node_ok cuts215 [] 0x14940410110404121010c0c43011494043031040c121010404410111010848011000410111100440011010444011010410121200410105850444005840121011908121005850464204850121011100121005414444005404110115140110105414545004414110111100110110404111010400440410500410010404414010404440404440440440028111004440444005450151040024151404450444004440111040024111004440121010d08121040024434210508121004440111004404414004400120204440110004404111004404120210500120215050110104404410114908410115050524211050410104404110104840110104801000704808120004840120204809000704404110130200810330008410130108410130200c0423010841012040c41012120081032100844402101884022120084062101844402040c81032060084062040811102040c81022060081032040c11102101884064001d001320405000f400481280 (by decide +kernel)

def state215_11 : List Sig := [0x33333333333333333333000033330000,input 4,input 6,input 7,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_11 : Impossible true (goalAt 215) 5 state215_11.toFinset :=
  node_ok cuts215 [] 0x840021000840420404460011800460410c04160004800120404800111005440111404440810020400810121010430010c00430111810130004800120104800c00030000c04210c041200240001280048001200148004414048001210048501610048401110105081110048409010104044101148404301044041200048401200 (by decide +kernel)

def state215_12 : List Sig := [0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 4,input 6,0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 7,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_12 : Impossible true (goalAt 215) 6 state215_12.toFinset :=
  node_ok cuts215 [⟨state215_11,exclude215_11⟩,⟨state215_7,exclude215_7⟩] 0x2100884022101881030584012100485012101504054101505084801110054401114044402120044401110084800444015100445011102040881022040c84060444012101050811100444051101050011101050011100444041402060011100444081802040454142040cc0422040c521004840125004840410114908810380004810304840524004841000715050524211050110130108810330108810304842000004841000e (by decide +kernel)

def state215_13 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0c0c0c0c0c0c0c0c,input 6,0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 7,input 0,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_13 : Impossible true (goalAt 215) 5 state215_13.toFinset :=
  node_ok cuts215 [] 0x110124008128004404160005800120204404540011000441011000110004400110104808810220408810321018111005840414204440450011000440111000840011000c0023010844001100046001040c44000480811010480811011050011101050011102040c8406210088402048401210119001610104044400118084400 (by decide +kernel)

def state215_14 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffffcccccccccccccccc,input 6,0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 7,input 0,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_14 : Impossible true (goalAt 215) 6 state215_14.toFinset :=
  node_ok cuts215 [⟨state215_13,exclude215_13⟩] 0x11012400812800440411010480812020440411011480812420440411010480812020440415010440411050440484022100884062040c444011900444211100460211808460610c0e000011100444040034110004400110104808111005440111404440810220408810321018111010d00414204440430210c08430311818111010500414004440c04040054121030008c0023010843031494043031040c4101 (by decide +kernel)

def state215_15 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0000000000000000,input 6,input 7,0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 0,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_15 : Impossible true (goalAt 215) 5 state215_15.toFinset :=
  node_ok cuts215 [] 0x12000480012020440411012100890800440454001100044101100011000440011010480811100484041420444085022100884032100845001100044011100084001100046001100844001100084023010844001110011011510011011050011101050011101110012101190012102040c8402301088402104044400111004400 (by decide +kernel)

def state215_16 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,input 7,0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 0,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_16 : Impossible true (goalAt 215) 6 state215_16.toFinset :=
  node_ok cuts215 [⟨state215_15,exclude215_15⟩] 0x4800120004808110104404c04224200110104404524214908110104404524214908110105404110104414110105840121004850121011100c04221200444021200444011100848080000444011101000d04400110004404120204440151004450111004440121010508111004440c04220600111004440414010500111004440414010500111004840525014940121030100810314940121014940121030108c080400504101 (by decide +kernel)

def state215_17 : List Sig := [0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 7,input 0,input 2,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_17 : Impossible true (goalAt 215) 7 state215_17.toFinset :=
  node_ok cuts215 [⟨state215_6,exclude215_6⟩,⟨state215_8,exclude215_8⟩,⟨state215_9,exclude215_9⟩,⟨state215_10,exclude215_10⟩,⟨state215_12,exclude215_12⟩,⟨state215_14,exclude215_14⟩,⟨state215_16,exclude215_16⟩] 0x4003cc04210404410140050810330200c00280018c04230200c04240050810310404410140038525010404410140050121010c0c430180014525010c0c41034005012101040441014005054140440411014001c41011490841018001054141490844144005041010440411014003e00030440411014001c81032420090028000a00012420012804001c81030440411014003812100440412004001d00070480812008000012100480812024001d000704404110140034440421200440040034410111100440040034440411100440440034410121200410140034150511100150140034110115140110140034150515140110540034110111100110140034840611100840240034810321200840240034840621200840640034810311100810340034161411100161040034121011908121040034161411908121440034121011100121040030410104440410040030440410500410040030410110500410140030440404440440440030110110500110040030120204440110040030110104440110140030120210500120240035000d04440111040034444005450151040035000c05450111440034444004440111040030810304440810240030840620600810240030810320600810340030840604440840640031000c04440111040030121010d08121040031000c10d08414240030121004440111040001000b400008101 (by decide +kernel)

def state215_18 : List Sig := [0x5555555555555555555555555555555555555555555555555555000055550000,input 7,input 4,input 6,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_18 : Impossible true (goalAt 215) 5 state215_18.toFinset :=
  node_ok cuts215 [] 0x11400410010410410005400110004410110021400810020410810004840161004850121010c00410010408410004c00110004408110020c008100204088100104008100301004100044004100110501100044008100240401100044401114054401110044404142048401110110104100144404100048081100044401100210108100240408100 (by decide +kernel)

def state215_19 : List Sig := [0x3333333333333333333333333333333333333333333333333333000033330000,input 7,input 4,input 6,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_19 : Impossible true (goalAt 215) 5 state215_19.toFinset :=
  node_ok cuts215 [] 0x11800460011810430105800120004810120021800860021810830104440151004450111010c00430010c04460404c00120004804120020c00830020c04860430800c200301004301048005200110501200048009200240401200048401214058401210044404142044401210104044101148404301044041200048401200204048101240408301 (by decide +kernel)

def state215_20 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0000,input 7,input 4,input 6,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_20 : Impossible true (goalAt 215) 5 state215_20.toFinset :=
  node_ok cuts215 [] 0x118004400110084400058001600058081501218008400210088400044401210105081110114004400110044400054001500054041602214008400210048400110008400301004400150004400110504400250008400240408400048401214048401610044401114044401510104044400150404400044041101151001501204048400240408400 (by decide +kernel)

def state215_21 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffffffff0000ffff0000,input 7,input 4,input 6,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_21 : Impossible true (goalAt 215) 6 state215_21.toFinset :=
  node_ok cuts215 [⟨state215_18,exclude215_18⟩,⟨state215_19,exclude215_19⟩,⟨state215_20,exclude215_20⟩] 0x541015040541421200444015100445011100941024040901424042000211100444040008121005840121404840121014840125004840524004840121024200121024040c04204842000104840121040000111005440111404440111004840414204440111014440414004440414004440111010500111024040818004442000004440111040004d01024040c04024040410115050524211050441424040c040240408414044048101 (by decide +kernel)

def state215_22 : List Sig := [0xffffffffffffffffffff0000ffff0000,input 7,input 4,input 6,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_22 : Impossible true (goalAt 215) 6 state215_22.toFinset :=
  node_ok cuts215 [⟨state215_11,exclude215_11⟩] 0x541015040541421200444015100445011100840021000840420404121005840121404840121014840125004840524004840121024200830120404810320404111005440111404440111004840414204440111014440414004440414004440111010500810020400810121010c00030000c080204045414149084414110509000240009080204044440212004440212001210800001210400001110206001110206004101104045414302001101044045242242009010 (by decide +kernel)

def state215_23 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 7,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 6,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_23 : Impossible true (goalAt 215) 6 state215_23.toFinset :=
  node_ok cuts215 [⟨state215_7,exclude215_7⟩] 0x15040541015050848021200444011100848025040901024050901011100544011140444004840161004850121004840521004940121024a00121004840908004840901080000121014900121004841001104440151004450111004440121010508111004440511010500111020600111004440818004440901020600111010500111004440414010404c010240409050240405242150504414110509010242009010210501101044045242400588101 (by decide +kernel)

def state215_24 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 4,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_24 : Impossible true (goalAt 215) 6 state215_24.toFinset :=
  node_ok cuts215 [] 0x11100544011140444021200444011100848011100c04021200444015040541015051001a04840161004850121014900121004841001930a00121004840c08004840c04030108121004840521004940121004440151004450111004440121010508111010500111004440414020600111004440818004440c04020600111004440511010500111004404904024100905030100541414908441411050c04030200c0404003c41011040454144001c8101 (by decide +kernel)

def state215_25 : List Sig := [0xffffffffffffffffffffffffffffffff33333333333333333333000033330000,input 7,input 4,input 6,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_25 : Impossible true (goalAt 215) 5 state215_25.toFinset :=
  node_ok cuts215 [] 0x460011800460410c04160004800120404800941024040901424040121404840161004840111005440111404440430010c00430111810130004800120104800111024040818004440414204440111004840430124040c04010c04410110404521010c041200148004414048001200301009010048001200044041210048008101 (by decide +kernel)

def state215_26 : List Sig := [0x3333333333333333333300003333000033333333333333333333000033330000,input 4,input 6,input 0,input 2,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_26 : Impossible true (goalAt 215) 6 state215_26.toFinset :=
  node_ok cuts215 [⟨state215_25,exclude215_25⟩,⟨state215_11,exclude215_11⟩] 0x21010444021000810121200840021010848021010810111100810111810848011800430111100460011810444011810430121200430105810444005800120015140120005810545004810120011100120020404111020400840420600810020404818020404840404440840440070111004440444005450151040024151404450444004440111010c04111010c00460410500430010c04414010c04460404440460404c04414004c00120004440120004c04111004804120010500120030100430130800810130a00c20030100c28030100810110c04430124040120004800810124a009200240409280240408101048001200150501200048004301149085200150505242110504301048001200240401210048408101800048101240420000240408101048408101111001210048404642058501214111001614058404642048401210044401210044404342400244142044410009044404342048401210150501210104044301149404101150505250148404301048404301400450003044041200048401200400441210048401200400141200 (by decide +kernel)

def state215_27 : List Sig := [0x3333333333333333333300003333000033333333333333333333000033330000,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 4,input 6,input 0,input 2,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_27 : Impossible true (goalAt 215) 6 state215_27.toFinset :=
  node_ok cuts215 [] 0x21000840021010810115040541015050848011100544011140444021200444011100848020400810020404840404440151004450111004440511010500111010500111004440414020600111004440818034040810130100810110c049010204049010204045414149084414048009010204049010204041210204049010204041210048501610048401110105081110048401210049405210048410011048401210149010000 (by decide +kernel)

def state215_28 : List Sig := [0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 4,input 6,input 0,input 1,input 2,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_28 : Impossible true (goalAt 215) 7 state215_28.toFinset :=
  node_ok cuts215 [⟨state215_21,exclude215_21⟩,⟨state215_22,exclude215_22⟩,⟨state215_23,exclude215_23⟩,⟨state215_24,exclude215_24⟩,⟨state215_26,exclude215_26⟩,⟨state215_27,exclude215_27⟩,⟨state215_12,exclude215_12⟩] 0x840411100840020404848021000840421200840420404444020404541421200541040068444015040541411100541440068848021201001a11100444014908545015101001a15140445014908444011101001a21200848040008444011101001a1110044404000884802120083030484083012040500112040483038001881032040412102040446420484012101110016140584046420585012141110012100484100110484012101505052501484100111494012501505012100484052424001c524040044121004840524204840121040045001140045001180016000440000121004841001104840121040001001140000810104440810021010818020400810120600810121010111021011001a04440111011100151405441001b05450111411100111004441001104440111004840434204841001b10d08414204840111004441001b04440111015050414014441001b10500414015050111004441001b10500414014908111004441001b04440111014908414010501001b20600818040004111004441001b04440111040004818020600c04015050d01020405001620404c0408000cc0402040454142040500184001c41012404052422404081014001c810124042000224040810114908810115051001615051000714908524240059001611051001740058110124041000f2404081018000481012404200002404081014003c8101 (by decide +kernel)

def state215_29 : List Sig := [0x3333333333333333333333333333333333330000333300003333000033330000,input 4,input 7,input 0,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_29 : Impossible true (goalAt 215) 6 state215_29.toFinset :=
  node_ok cuts215 [] 0x30900410130800830130200c20030900c08030900830110404410111010848011000410111100440011010444011010410121200410121810444021800830121200860021810848021810830111100830105810444005800120015140120005810545004810120011100120010404111010400440410500410010404414010404440404440440440028111004440444005450151040024151404450444004440111020c04111020c00860420600830020c04818020c04860404440860404c04414004c00120004440120004c041110048041200105001200150501200048004101149005200150505240150504101048001200240401200048008301242009200240409080240408301048001200150501210048404101149404101150505250148404101048404101151401210048404440058501214151401614058404440048401210044401210044404140400244140044410009044404140048401210240401210204048301400208101240410012240408301048408301242010003044041200048401200242001210048401200400141200 (by decide +kernel)

def state215_30 : List Sig := [0x3333333333333333333333333333333333330000333300003333000033330000,0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 4,input 7,input 0,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_30 : Impossible true (goalAt 215) 6 state215_30.toFinset :=
  node_ok cuts215 [] 0x10404901024140410110404541415050410111000440011010410125040901024050901011100545015140444011100545015140444010400410010404440404440151004450111004440901020600111010500111004440414010500111004440414020c0454141040454141040490102420084140480012101040452101040412100485016100484011101050011100484012104001c901004840908004840121024a010000 (by decide +kernel)

def state215_31 : List Sig := [0xffffffffffffffff0000000000000000ffff0000ffff0000,input 6,input 4,input 7,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_31 : Impossible true (goalAt 215) 6 state215_31.toFinset :=
  node_ok cuts215 [] 0x941024040901424040444015100445011100440011000440410404121005840121404840121024040c04204840524004840121024200430110404410310404111005440111404440111004840414204440111024040818004440414004440111010500410010400410111010901030100901021050510110404524210404c00030000c040104048480111008480111001210149401210149401110105001110105008101204049010301001101044049080149085414 (by decide +kernel)

def state215_32 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 4,input 7,input 0,input 1,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_32 : Impossible true (goalAt 215) 7 state215_32.toFinset :=
  node_ok cuts215 [⟨state215_23,exclude215_23⟩,⟨state215_29,exclude215_29⟩,⟨state215_30,exclude215_30⟩,⟨state215_8,exclude215_8⟩,⟨state215_9,exclude215_9⟩,⟨state215_21,exclude215_21⟩,⟨state215_31,exclude215_31⟩] 0xd05010404410124040c08024040d0503020090502404041011040600061040441014005854141505200051505054144005841011040444042120044001040444401100044041110044041040484801040494141110094102404084802404094142120090142404044402404100201110044402420054501514100201514054502420044401110100201110044404000854501514100201514054504000844401110043030484043011040452501040443031494041031040412101040446420484012101110016140584046420585012141110012100484100120484012102404100122404100128001200032404012100484092824001c92802420012100484092820484012102420100122420100128000a000140000121004841001204840121040001001240000410104440410011010414010400410110500410111010111011011002004440111011100151405441001f05450111411100111004441001204440111004840434204841001f10d08414204840111004441001f04440111024040818024041001f20600818024040111004441001f10500414024200111004441001f04440111024200414010501001f10500414040004111004441001f04440111040004414010501001e4001c81011505090801505041014001c410115052000015050410124200410124041000f2404100072420090804001d000721051001d4003c1101 (by decide +kernel)

def state215_33 : List Sig := [0xccccffffccccffffccccffffccccffffcccccccccccccccccccccccccccccccc,input 4,input 7,input 0,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_33 : Impossible true (goalAt 215) 6 state215_33.toFinset :=
  node_ok cuts215 [] 0x30108410110404810330200c00230108c0803010881031040441011101084801100041011110044001101044401101041012120041012101844402100881032120084022101884802101881031110081030541444400540411011514011010541454500441411011110011011040411101040044041050041001040441401040444040444044044002811100444044400545015104002415140445044400444011102040c11102040884062060081022040c81802040c840604440840604404414004400120204440110004404111004404120210500120240024111004440121010d08121040024434210508121004440111015050110104404410114908410115050524211050410104404110124040110124000810324a00900024040928024040810304404110110c0c121010c04410114940410110c0c52501040c41010484041011190812100484044400585016101190816140485044400484012102040c12102040490104002c81012040d000d2040c90100484012100480900050480011010484012000480812100480811014000c1101 (by decide +kernel)

def state215_34 : List Sig := [0xf0f0f0f0f0f0f0f00000f0f00000f0f0f0f0f0f0f0f0f0f0000000000000000,input 6,input 4,input 7,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_34 : Impossible true (goalAt 215) 5 state215_34.toFinset :=
  node_ok cuts215 [] 0x218008400210088400048001200048081101118004400110084400044401210105081110214008400210048400044001100044041202114004400110044400240008400210408400150004400110404400110008400301004400111001210119001210105001110105001110204048400301008400111001101151001101104044400111004400 (by decide +kernel)

def state215_35 : List Sig := [0xffffffffffffffff0000ffff0000ffffffffffffffffffff0000000000000000,input 6,input 4,input 7,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_35 : Impossible true (goalAt 215) 6 state215_35.toFinset :=
  node_ok cuts215 [⟨state215_34,exclude215_34⟩] 0x941024040901424040150104404110504404848011100444021202000011100444040008121005840121404840121024040c04204840120004800120204404121014940525004840121014940525004840111005440111404440111004840414204440111024040818004440110004400110104808111010500414004440111010500414004440900024000901004404110114908524204404110114908524204404c04024040c040240404101204048101301009010 (by decide +kernel)

def state215_36 : List Sig := [0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000,input 4,input 7,input 0,input 1,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_36 : Impossible true (goalAt 215) 7 state215_36.toFinset :=
  node_ok cuts215 [⟨state215_33,exclude215_33⟩,⟨state215_35,exclude215_35⟩,⟨state215_10,exclude215_10⟩] 0xd05010404410124040c08024040d0503020090502404041011040444042120044001040444401100044041110044041040484801040494141110094102404084802404094142120090142404044402404015051110015010440454500440415051514011050440444400440443030484043011040452501040443031494041031040412101040446420484012101110016140584046420585012141110012100484100100484012102404100102404100104003e00022404012100484012024001c120004404121004800120204840120204405001004404410104440410011010414010400410110500410111010111011011001d04440111011100151405441002205450111411100111004441001004440111004840434204841002210d0841420484011100444100220444011102404081802404100222060081802404011100444011011050011000480811100440011010444011010480841400480854140440411011040452421040454141490844141040411010440500074001c900024041000f2404100070440411013020100163020041014003c410130202000130200410140058410121201000221200444040074444021201001d2120044404000844404004100004000012104004012104003d00108000012104000012102060100012060011104008811102060100222060011104000411104001d002120405000f400809080 (by decide +kernel)

def state215_37 : List Sig := [0xafafafafafafafafafafafafafafafafafafafafafafafafaaaaaaaaaaaaaaaa,input 0,input 6,input 7,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_37 : Impossible true (goalAt 215) 5 state215_37.toFinset :=
  node_ok cuts215 [] 0x940021000841021000540011000441011000120004800120204404860021000840221000460011000440211000440021000c040110001101048081101048084140048404142048408101210008101210004101110004101110001110044041202044041202111001210119001210204048400204048400104044400104044400 (by decide +kernel)

def state215_38 : List Sig := [0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,0x505050505050505050505050505050505050505050505050000000000000000,input 6,input 7,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_38 : Impossible true (goalAt 215) 4 state215_38.toFinset :=
  node_ok cuts215 [] 0x250008400210408400150004400110404400110008400301004400111001101151001101240408400301008400212004400111004400111001110105001110044001100044049080204008100204048400104004100104044400 (by decide +kernel)

def state215_39 : List Sig := [0x505050505050505050505050505050505050505050505050000000000000000,input 0,input 6,input 7,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_39 : Impossible true (goalAt 215) 5 state215_39.toFinset :=
  node_ok cuts215 [⟨state215_38,exclude215_38⟩] 0x940021000841021000540011000441011000120004800120204404860021000840221000460011000440211000440021000c04011000110004400110104808111004842000004440810020400810121000410010400410111000444004404544004404444004840464004840901021000c040210008480110004440110004140 (by decide +kernel)

def state215_40 : List Sig := [0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0000000000000000,input 6,input 7,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_40 : Impossible true (goalAt 215) 5 state215_40.toFinset :=
  node_ok cuts215 [⟨state215_38,exclude215_38⟩] 0x940021000841021000540011000441011000440021000c04011000444004404544004404810121000c040210004101110004440110004440800004142111004440048404640048401101044081101048048501210008501210004501110004501110001110048001200044049080218008400214048400118004400114044400 (by decide +kernel)

def state215_41 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0000000000000000,input 6,input 7,input 0,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_41 : Impossible true (goalAt 215) 6 state215_41.toFinset :=
  node_ok cuts215 [⟨state215_37,exclude215_37⟩,⟨state215_39,exclude215_39⟩,⟨state215_40,exclude215_40⟩,⟨state215_15,exclude215_15⟩,⟨state215_1,exclude215_1⟩] 0x2504011012500084002420084002504090802104084000440484001504011011500044001490844001504052421104044000440444000480a0004048001101048401200048081210048081101400a01101218081210218008400400a084002180a0003210088400048408400118081210118004400149404400118085250110084400048404400044044140044001202044401100044041110044041202105001202400a0111004440121010d08121080008434210508121004440111021404111021400840020600840021404818021004840004440840011404111011400440010500440011404414011004440004440440030100440011000840030200840030100c080301008400110004400149084440111001101151401101149085450151001101111001101149404440111001210119081210149404642119001210111001210105004440105001110800041110105020000105001110111001110301004440204048400212008400301008480301008400111008400302008480104044400111004400302004440111004400212004400 (by decide +kernel)

def state215_42 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,input 7,input 0,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_42 : Impossible true (goalAt 215) 6 state215_42.toFinset :=
  node_ok cuts215 [] 0x4404c04030140110104404524214908110104404524214908110104800120004808110104840c04030108121004840525014940121004840525014940121004400110004404120204440121010508111004440c04020600111004440414010500111004440414010500111021000c04030200905011000444004404544004404444004840464004840414004440414004440444021200c040111008480111004440212010002 (by decide +kernel)

def state215_43 : List Sig := [0xccccffffccccffffccccffffccccffffccccffffccccffffcccccccccccccccc,input 4,input 6,input 7,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_43 : Impossible true (goalAt 215) 5 state215_43.toFinset :=
  node_ok cuts215 [] 0x2100884022101881031100844021101841030540411010441411010444015100445011102040881022040c84061040841021040c440604400110004404120204440121010500111030008c0023010041032400090002404011010440451011505011010484016100485012102040481012040c12101040441011040c1210048001200048081101 (by decide +kernel)

def state215_44 : List Sig := [0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000,input 4,input 6,input 7,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_44 : Impossible true (goalAt 215) 6 state215_44.toFinset :=
  node_ok cuts215 [⟨state215_43,exclude215_43⟩] 0x941024040901424040541015040541421200150104404110504404121005840121404840121024040c04204840121014840125004840120004800120204404111005440111404440111004840414204440111024040818004440111014440414004440110004400110104808d01024040c04024040900024000901004404110114404541404404444015140444015141000004842000004840414004440414004440810120404c04024040410110404c080150505242 (by decide +kernel)

def state215_45 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,input 7,input 0,input 1,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_45 : Impossible true (goalAt 215) 7 state215_45.toFinset :=
  node_ok cuts215 [⟨state215_16,exclude215_16⟩,⟨state215_2,exclude215_2⟩,⟨state215_41,exclude215_41⟩,⟨state215_42,exclude215_42⟩,⟨state215_21,exclude215_21⟩,⟨state215_44,exclude215_44⟩,⟨state215_24,exclude215_24⟩] 0xd05004404110130100908030100d05024200c0503010011010440500160440411013020052421490a00061490852423020011010440600050440411014001c52421490a00041490852424001c11010440415051110015010440454500440415051514011050440444400440500271110044403010084803010100272120084803010044401110100272120084803020044401110100271110044403020084802120100278000e000240008444011101002711100444040009002740008120280004120004404121004800120204840120204405002604404464204840121011100161405840464205850121411100121004840c24204840121030101002630100c24280000c04230100121004840c28204840121030200525014940c28214940525030200121004841002604840121040000525014941002614940525040000121004840110110500110004808111004400110104440110104808414004809002704440111011100151405441002505450111411100111004441002604440111004840434204841002510d08414204840111004441002504440111030100818030101002520600818030100111004441002504440111030200414010501002510500414030200111004441002504440111040004414010501002510500414040004111004441002440058810130101000f30101001630200c0804005900162414100234003c4101 (by decide +kernel)

def state215_46 : List Sig := [0xfafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafa,0xeeeeeeeeeeeeeeeeffffffffffffffffeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 6,input 7,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_46 : Impossible true (goalAt 215) 4 state215_46.toFinset :=
  node_ok cuts215 [] 0x4404810130140110104404410111050110130000c00030100410104800120004405002b204048104204041210104044104104044401044401110044501210044041102044041201204048102204044440110004400104048180 (by decide +kernel)

def state215_47 : List Sig := [0xeeeeeeeeeeeeeeeeffffffffffffffffeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 0,input 6,input 7,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_47 : Impossible true (goalAt 215) 5 state215_47.toFinset :=
  node_ok cuts215 [⟨state215_46,exclude215_46⟩] 0x110120404c05004404110110404441404404150104404110504404850120404810520404440011000440410404c00030000c040104041101044081101048044142111020000111008101204088101210144101104084101110101110048001200044050007048401610048501210204048404204041210104044404104044404 (by decide +kernel)

def state215_48 : List Sig := [0xfafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafa,input 0,0xccccccccccccccccffffffffffffffffcccccccccccccccccccccccccccccccc,input 6,input 7,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_48 : Impossible true (goalAt 215) 5 state215_48.toFinset :=
  node_ok cuts215 [⟨state215_46,exclude215_46⟩] 0x110124008c05004404110110404441404404c00030000c0401040412000480012020440481012040481030484043011040441031040412100584012140484011010480811010480881032041881032100c41011041041011100411140484200000484011100440412020440412022100884022040c4440110004400104048480 (by decide +kernel)

def state215_49 : List Sig := [0xccccccccccccccccffffffffffffffffcccccccccccccccccccccccccccccccc,input 6,input 7,input 0,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_49 : Impossible true (goalAt 215) 6 state215_49.toFinset :=
  node_ok cuts215 [⟨state215_47,exclude215_47⟩,⟨state215_48,exclude215_48⟩] 0x341401101044048103242009002341409080301408103044041101150501101044044101149084101150505242110504101044041101054144440054041101151401101054145450044141101111001101210184440210088103212008402210188480210188103111008103110108480110004101111004400110104440110104101212004101044044140044001202044401100044041110044041202105001202400b011100444044400545015108000415140445044400444011102040c11102040884062060081022040c81802040c840604440840610404111010400440410500410010404414010404440404440440440038111004440121010d08121080000434210508121004440111030100410130000810330a00c00030100c2803010081031040441010480900070480011010484012000480812100480811014001c11011190812100484044400585016101190816140485044400484012102040c121020404c0404002c81012040d000d2040cc04004840121010c0c121010c04410114940410110c0c52501040c4101048404101 (by decide +kernel)

def state215_50 : List Sig := [0x3333000033330000333333333333333333330000333300003333000033330000,input 4,input 6,input 7,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_50 : Impossible true (goalAt 215) 5 state215_50.toFinset :=
  node_ok cuts215 [] 0x21800860021810830111000440011010410105800120004810120004440151004450111020c00830020c04860410400410010404440404c00120004804120030000c000301004101048009200240401200048005200150501200048401214058401210044404140044401210204048101240408301048404101148404101044041200048401200 (by decide +kernel)

def state215_51 : List Sig := [0xffff0000ffff0000ffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 4,input 6,input 7,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_51 : Impossible true (goalAt 215) 6 state215_51.toFinset :=
  node_ok cuts215 [⟨state215_50,exclude215_50⟩] 0x941024040901424040440011000440410404444015140545011100444015140545011100121005840121404840121024040c04204840430110404410310404928004840121024202000004840121040000111005440111404440111004840414204440111024040818004440410010400410111010414004440111010500414004440111010500c00030000c04010404901030100901021050541410404541410404110120404810124040c040150504101150504101 (by decide +kernel)

def state215_52 : List Sig := [0xffffffffffffffff00000000000000000000000000000000,input 6,input 7,input 0,input 1,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_52 : Impossible true (goalAt 215) 7 state215_52.toFinset :=
  node_ok cuts215 [⟨state215_49,exclude215_49⟩,⟨state215_51,exclude215_51⟩,⟨state215_4,exclude215_4⟩] 0xd05004404110130100908030100d05024200c05030100110104404541404404110110404524210404541414908441410404110104404150511100150104404545004404150515140110504404444004405002311100444030100848030101002321200848030100444011100440421200440010404444011000440411100440410404848010404120280008120004404121004800120204840120204405002d04404464204840121011100161405840464205850121411100121004840c24204840121030101002d30100c2424003cc04230100121004840430304840430110404525010404430314940410310404121010404110110500110004808111004400110104440110104808414004809002304440111011100151405441002a05450111411100111004441002d04440111004840434204841002a10d08414204840111004441002a04440111030100818030101002a20600818030100111004440410104440410011010414010400410110500410111010111011011001640058c00030101000f3010100161040441012420100072420011014003c11012420200012420011014001c11012120100022120044404008c4440212010023212004440400084440400b50000400001210400b412104003d002d800001210400001210206010001206001110400a8111020601002a20600111040004111040059002920405000f4009cc080 (by decide +kernel)

def state215_53 : List Sig := roots 215
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_53 : Impossible true (goalAt 215) 8 state215_53.toFinset :=
  node_ok cuts215 [⟨state215_5,exclude215_5⟩,⟨state215_17,exclude215_17⟩,⟨state215_28,exclude215_28⟩,⟨state215_32,exclude215_32⟩,⟨state215_36,exclude215_36⟩,⟨state215_45,exclude215_45⟩,⟨state215_52,exclude215_52⟩] 0x80018c04010404c00040058810130200c00080014c04030200c0404005881011040441018001090100440490004001c81012420090008000c90102420090104001c81010440411014005854140440411014001c410114908410180008541414908441440058410104404110140008840411100840040008810121200840040008840421200840440008810111100810140008440421200440040008410111100440040008440411100440440008410121200410140008150511100150140008110115140110140008150515140110540008110111100110140000830304840830140000810140000810140000830380004810340000810104840810140000430304840430140000410114940410140000430314940410340000410104840410140000120280000120040000110104840120040000120204840120240000110140000110140008464204840121040008444005850161040008464205850121440008444004840121040004810104440810040004840420600810040004810120600810140004840404440840440004410104440410040004440410500410040004410110500410140004440404440440440004110110500110040004120204440110040004110104440110140004120210500120240009000204440111040008444005450151040009000105450111440008444004440111040001000004440111040000121010d08121040001000110d084142400001210044401110 (by decide +kernel)

theorem lower215 : Claim 215 9 :=
  fromSearch 1604 (by decide +kernel) exclude215_53

open PEqualNP.CircuitLowerBounds

def graph : Sig := goalAt 255
theorem graph_proper : proper graph := by unfold proper; decide +kernel

def edgeList : List Nat := [0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 2, 7, 4, 7, 5, 7, 6, 7]
def target (x : Fin 8 → Bool) : Bool :=
  decide (∃ i < edgeList.length / 2,
    (List.ofFn x).getD (edgeList.getD (2*i) 0) false = true ∧
    (List.ofFn x).getD (edgeList.getD (2*i+1) 0) false = true)

-- The three products cover the posted edges.
def smallCircuit : Circuit := ⟨[⟨.or,[0,1]⟩, ⟨.or,[0,2]⟩, ⟨.or,[3,7]⟩, ⟨.or,[4,5]⟩, ⟨.or,[5,6]⟩, ⟨.or,[7,8]⟩, ⟨.or,[7,12]⟩, ⟨.and,[11,13]⟩, ⟨.and,[9,14]⟩, ⟨.and,[6,10]⟩, ⟨.or,[15,16]⟩, ⟨.or,[18,17]⟩],19⟩

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



-- Pin the two omitted vertices to zero. Both are essential before restriction.
theorem lowerGraph : Impossible true graph 10 eightInputs.toFinset :=
  (ruleFor 255 lower215 none (by decide +kernel)).property 10 eightInputs
    (by decide +kernel) (by decide +kernel)


end PEqualNP.Outside.L_meta_28906

open PEqualNP.Outside.L_meta_28906 in
theorem PEqualNP.Outside.L_meta_28906 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o fit _ correct
  exact replaceShort lowerGraph gates o fit correct

import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_28958

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
  (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 2 &&& x 5) ||| (x 0 &&& x 6) ||| (x 1 &&& x 6) ||| (x 3 &&& x 6) ||| (x 5 &&& x 6) ||| (x 1 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)

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



def cuts224 : Cuts (goalAt 224) := []

def state224_0 : List Sig := roots 224
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude224_0 : Impossible true (goalAt 224) 3 state224_0.toFinset :=
  node_ok cuts224 [] 0x30100602030000a02030200c00030100c08030100a02018080602028080604028000c04028200a00028080a08028080c04018100604018080a08018000c08018100600018080604018080c08028200a080 (by decide +kernel)

theorem lower224 : Claim 224 4 :=
  fromSearch 1432354816 (by decide +kernel) exclude224_0

theorem lower226 : Claim 226 5 :=
  fromLift 5 2 291504224 lower224 (by decide +kernel)


theorem lower228 : Claim 228 5 :=
  fromLift 5 4 1428161792 lower224 (by decide +kernel)


def cuts194 : Cuts (goalAt 194) := []

def state194_0 : List Sig := roots 194
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude194_0 : Impossible true (goalAt 194) 3 state194_0.toFinset :=
  node_ok cuts194 [] 0x30100420230000820230200c00030100c08030100820210808420220808424020800c04020a00820020808828020808c04010900424010808828010800c08010900420010808424010808c08020a008280 (by decide +kernel)

theorem lower194 : Claim 194 4 :=
  fromSearch 285212768 (by decide +kernel) exclude194_0

def cuts102 : Cuts (goalAt 102) := []

def state102_0 : List Sig := roots 102
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude102_0 : Impossible true (goalAt 102) 3 state102_0.toFinset :=
  node_ok cuts102 [] 0x180006000180804202118084202108184202090002400090106040108004200108086020098102404090182404098802420090882420 (by decide +kernel)

theorem lower102 : Claim 102 4 :=
  fromSearch 18875744 (by decide +kernel) exclude102_0

def cuts166 : Cuts (goalAt 166) := []

def state166_0 : List Sig := roots 166
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude166_0 : Impossible true (goalAt 166) 3 state166_0.toFinset :=
  node_ok cuts166 [] 0x28000a00028080820221808820220818820209000240009010a08020800820020808a020098102404090182404098802420090882420 (by decide +kernel)

theorem lower166 : Claim 166 4 :=
  fromSearch 270534000 (by decide +kernel) exclude166_0

def rule230_0 : {c : Cut // CutGood (goalAt 230) c} :=
  ruleFor 230 lower226 none (by decide +kernel)

def rule230_1 : {c : Cut // CutGood (goalAt 230) c} :=
  ruleFor 230 lower228 none (by decide +kernel)

def rule230_2 : {c : Cut // CutGood (goalAt 230) c} :=
  ruleFor 230 lower194 none (by decide +kernel)

def rule230_3 : {c : Cut // CutGood (goalAt 230) c} :=
  ruleFor 230 lower228 (some (1,input 2,input 6)) (by decide +kernel)

def rule230_4 : {c : Cut // CutGood (goalAt 230) c} :=
  ruleFor 230 lower228 (some (1,input 2,input 7)) (by decide +kernel)

def rule230_5 : {c : Cut // CutGood (goalAt 230) c} :=
  ruleFor 230 lower102 none (by decide +kernel)

def rule230_6 : {c : Cut // CutGood (goalAt 230) c} :=
  ruleFor 230 lower166 none (by decide +kernel)

def cuts230 : Cuts (goalAt 230) := [rule230_0,rule230_1,rule230_2,rule230_3,rule230_4,rule230_5,rule230_6]

def state230_0 : List Sig := [0xfffffffffffffffffffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0,input 7,input 6,input 1,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude230_0 : Impossible true (goalAt 230) 4 state230_0.toFinset :=
  node_ok cuts230 [] 0x9010600409100240409010a00409200240409000240009011000209810240409018240410810420410818828020810820420818424009880242009088242030010c004301004206108088202 (by decide +kernel)

def state230_1 : List Sig := [0xfffffffffffffffff0f0f0f0f0f0f0f0,input 7,input 6,input 1,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude230_1 : Impossible true (goalAt 230) 4 state230_1.toFinset :=
  node_ok cuts230 [] 0x240418010244009010a00028000a02020808260409010240609010420410810420620a00820020800820228080c00030000c080208082400090002404282002420098802422090804202108084206090808206 (by decide +kernel)

def state230_2 : List Sig := [0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0,input 6,input 1,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude230_2 : Impossible true (goalAt 230) 5 state230_2.toFinset :=
  node_ok cuts230 [⟨state230_0,exclude230_0⟩,⟨state230_1,exclude230_1⟩] 0xa02009010a00020808a08028000a02028200a02020808240420809000209010240410818604018011000218100244010818240409010242028200240040008240409000242009010240440008a08028200820210900820028080828020800820220a00820228080424028080260610900260409011000309010260640008240609010424009010420620a00420430210424010810420610900420630210828020a00262220a00262009080424009080262210900242209080828009080c04010818c00420808c08420808c04030210c0402080842062080900004000042022181824202180882028000482022181a0000208188202090808202 (by decide +kernel)

def state230_3 : List Sig := [0xffffffffffffffff0000000000000000f0f0f0f0f0f0f0f0,input 6,input 7,input 1,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude230_3 : Impossible true (goalAt 230) 4 state230_3.toFinset :=
  node_ok cuts230 [] 0x240428010248009010600018000602010808260409010240609010820420810820610900420010800420218080c00030000c040108082400090002404181002420098802422090808202208088206090804206 (by decide +kernel)

def state230_4 : List Sig := [0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 7,input 1,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude230_4 : Impossible true (goalAt 230) 5 state230_4.toFinset :=
  node_ok cuts230 [⟨state230_0,exclude230_0⟩,⟨state230_3,exclude230_3⟩] 0xc04410808420220818c08030010c04430200c0442081842021080a00011080842020908046061180a000011818420609080420210808602009010600010808604018000602018100602010808240410809000209010240420818a08028011000228200248020818240409010242018100240040008240409000242009010240440008604018100420220a00420018080424010800420210900420218080828018080260610900260409011000409010260640008240609010424009010820610900820430110828020810820620a008206301104240109002622109002620090804644090802622119102422090804240090810000400008202 (by decide +kernel)

def state230_5 : List Sig := [0x3333333333333333333333333333333333333333333333330000000000000000,input 6,input 7,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude230_5 : Impossible true (goalAt 230) 4 state230_5.toFinset :=
  node_ok cuts230 [] 0x288008200208808200188004200108804200090002400090106040218008200208108200118004200108104200108008200301004200109002404181002404109002420119002420280808200301008200180804200109004200 (by decide +kernel)

def state230_6 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,input 7,input 1,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude230_6 : Impossible true (goalAt 230) 5 state230_6.toFinset :=
  node_ok cuts230 [⟨state230_5,exclude230_5⟩,⟨state230_0,exclude230_0⟩] 0x240430100a08009010240418100604009010240418100604009010240009000240418100242030100c04409080242030200c08409080242040002000109080260409010240609010262009080242209080424030100828010900828010900424020a02000010900424040004820230100c080400144202 (by decide +kernel)

def state230_7 : List Sig := roots 230
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude230_7 : Impossible true (goalAt 230) 6 state230_7.toFinset :=
  node_ok cuts230 [⟨state230_2,exclude230_2⟩,⟨state230_4,exclude230_4⟩,⟨state230_6,exclude230_6⟩] 0x40014c04010808c00040018820230200c00080008c04030200c04040014820210808420240008a02009010a00040008820228200a00040008a02028200a02040008820209010820240008602009010600040008420218100600040008602018100602040008420209010420240000860609080860240000820240000820240000860680004820640000820209080820240000460609080460240000420240000420240000460680000420640000420209080420240000240440008240040000604009080240040000240409080240440000604040000604040004820210900820040004a02020a00820040004820220a00820240004a02010900a02040004420220a00420040004602010900420040004420210900420240004602020a006020400042606109002604400042404400042404400042606400082406400042404109002404400002622109002620400002420119102420400002622119102422400002420109002420 (by decide +kernel)

theorem lower230 : Claim 230 7 :=
  fromSearch 287311200 (by decide +kernel) exclude230_7

theorem lower225 : Claim 225 5 :=
  fromLift 5 1 1342177285 lower224 (by decide +kernel)


theorem lower195 : Claim 195 5 :=
  fromLift 5 1 268435558 lower194 (by decide +kernel)


def cuts97 : Cuts (goalAt 97) := []

def state97_0 : List Sig := roots 97
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude97_0 : Impossible true (goalAt 97) 3 state97_0.toFinset :=
  node_ok cuts97 [] 0x180802101180004101181006000180806040180804101084042101104042120104006020105004100104044140104046020084802120084044140084006040084802100084042120084046040105004140 (by decide +kernel)

theorem lower97 : Claim 97 4 :=
  fromSearch 5 (by decide +kernel) exclude97_0

theorem lower99 : Claim 99 5 :=
  fromLift 5 2 101 lower97 (by decide +kernel)


def rule227_0 : {c : Cut // CutGood (goalAt 227) c} :=
  ruleFor 227 lower225 none (by decide +kernel)

def rule227_1 : {c : Cut // CutGood (goalAt 227) c} :=
  ruleFor 227 lower195 none (by decide +kernel)

def rule227_2 : {c : Cut // CutGood (goalAt 227) c} :=
  ruleFor 227 lower226 none (by decide +kernel)

def rule227_3 : {c : Cut // CutGood (goalAt 227) c} :=
  ruleFor 227 lower99 none (by decide +kernel)

def cuts227 : Cuts (goalAt 227) := [rule227_0,rule227_1,rule227_2,rule227_3]

def state227_0 : List Sig := roots 227
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_0 : Impossible true (goalAt 227) 6 state227_0.toFinset :=
  node_ok cuts227 [] 0x4000cc04010404c0004000c820230200c0004000cc04030200c0404000c82021040441014000ca02008404a0004000c820228200a0004000ca02028200a0204000c82020840421014000460200840460004000441011810060004000460201810060204000441010840421014000c82021090082004000ca02020a0082004000c820220a0082024000ca02010900a02040000420220a00420040000410110900420040000420210900420240000410120a0041014000423031090023014000421014000421014000423034000421034000421011090021014000c83030848083024000c82024000c82024000c83034000c82034000c820208480820240008410108480410040008420210500410040008410110500410140008420208480420240004210110500210040004604008480210040004210108480210140004604010500414040000838108480212040000424008c88232040000838108c882122400004240084802120 (by decide +kernel)

theorem lower227 : Claim 227 7 :=
  fromSearch 268435557 (by decide +kernel) exclude227_0

theorem lower229 : Claim 229 6 :=
  fromLift 6 1 1342178565 lower228 (by decide +kernel)


theorem lower101 : Claim 101 5 :=
  fromLift 5 4 1285 lower97 (by decide +kernel)


theorem lower103 : Claim 103 6 :=
  fromLift 6 2 1381 lower101 (by decide +kernel)


theorem lower167 : Claim 167 5 :=
  fromLift 5 1 268436853 lower166 (by decide +kernel)


def cuts163 : Cuts (goalAt 163) := []

def state163_0 : List Sig := roots 163
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude163_0 : Impossible true (goalAt 163) 3 state163_0.toFinset :=
  node_ok cuts163 [] 0x28000a00028080210120800820020808a02008c0421010840c210120c0882022080c820208400210008404a080084802320084882120 (by decide +kernel)

theorem lower163 : Claim 163 4 :=
  fromSearch 268435573 (by decide +kernel) exclude163_0

def rule231_0 : {c : Cut // CutGood (goalAt 231) c} :=
  ruleFor 231 lower230 none (by decide +kernel)

def rule231_1 : {c : Cut // CutGood (goalAt 231) c} :=
  ruleFor 231 lower227 none (by decide +kernel)

def rule231_2 : {c : Cut // CutGood (goalAt 231) c} :=
  ruleFor 231 lower227 (some (2,input 0,input 7)) (by decide +kernel)

def rule231_3 : {c : Cut // CutGood (goalAt 231) c} :=
  ruleFor 231 lower229 (some (1,input 0,input 7)) (by decide +kernel)

def rule231_4 : {c : Cut // CutGood (goalAt 231) c} :=
  ruleFor 231 lower101 none (by decide +kernel)

def rule231_5 : {c : Cut // CutGood (goalAt 231) c} :=
  ruleFor 231 lower103 none (by decide +kernel)

def rule231_6 : {c : Cut // CutGood (goalAt 231) c} :=
  ruleFor 231 lower227 (some (1,input 0,input 7)) (by decide +kernel)

def rule231_7 : {c : Cut // CutGood (goalAt 231) c} :=
  ruleFor 231 lower103 (some (1,input 1,input 5)) (by decide +kernel)

def rule231_8 : {c : Cut // CutGood (goalAt 231) c} :=
  ruleFor 231 lower230 (some (2,input 1,input 5)) (by decide +kernel)

def rule231_9 : {c : Cut // CutGood (goalAt 231) c} :=
  ruleFor 231 lower99 (some (1,input 1,input 5)) (by decide +kernel)

def rule231_10 : {c : Cut // CutGood (goalAt 231) c} :=
  ruleFor 231 lower195 (some (1,input 0,input 7)) (by decide +kernel)

def rule231_11 : {c : Cut // CutGood (goalAt 231) c} :=
  ruleFor 231 lower230 (some (1,input 1,input 5)) (by decide +kernel)

def rule231_12 : {c : Cut // CutGood (goalAt 231) c} :=
  ruleFor 231 lower226 (some (1,input 1,input 5)) (by decide +kernel)

def rule231_13 : {c : Cut // CutGood (goalAt 231) c} :=
  ruleFor 231 lower230 (some (2,input 2,input 7)) (by decide +kernel)

def rule231_14 : {c : Cut // CutGood (goalAt 231) c} :=
  ruleFor 231 lower226 none (by decide +kernel)

def rule231_15 : {c : Cut // CutGood (goalAt 231) c} :=
  ruleFor 231 lower230 (some (1,input 2,input 7)) (by decide +kernel)

def rule231_16 : {c : Cut // CutGood (goalAt 231) c} :=
  ruleFor 231 lower101 (some (1,input 0,input 2)) (by decide +kernel)

def rule231_17 : {c : Cut // CutGood (goalAt 231) c} :=
  ruleFor 231 lower103 (some (1,input 0,input 2)) (by decide +kernel)

def rule231_18 : {c : Cut // CutGood (goalAt 231) c} :=
  ruleFor 231 lower102 none (by decide +kernel)

def rule231_19 : {c : Cut // CutGood (goalAt 231) c} :=
  ruleFor 231 lower194 none (by decide +kernel)

def rule231_20 : {c : Cut // CutGood (goalAt 231) c} :=
  ruleFor 231 lower101 (some (3,input 2,input 5)) (by decide +kernel)

def rule231_21 : {c : Cut // CutGood (goalAt 231) c} :=
  ruleFor 231 lower103 (some (3,input 2,input 5)) (by decide +kernel)

def rule231_22 : {c : Cut // CutGood (goalAt 231) c} :=
  ruleFor 231 lower230 (some (3,input 2,input 5)) (by decide +kernel)

def rule231_23 : {c : Cut // CutGood (goalAt 231) c} :=
  ruleFor 231 lower103 (some (1,input 2,input 6)) (by decide +kernel)

def rule231_24 : {c : Cut // CutGood (goalAt 231) c} :=
  ruleFor 231 lower101 (some (1,input 2,input 6)) (by decide +kernel)

def rule231_25 : {c : Cut // CutGood (goalAt 231) c} :=
  ruleFor 231 lower230 (some (1,input 2,input 6)) (by decide +kernel)

def rule231_26 : {c : Cut // CutGood (goalAt 231) c} :=
  ruleFor 231 lower230 (some (2,input 5,input 7)) (by decide +kernel)

def rule231_27 : {c : Cut // CutGood (goalAt 231) c} :=
  ruleFor 231 lower230 (some (3,input 5,input 7)) (by decide +kernel)

def rule231_28 : {c : Cut // CutGood (goalAt 231) c} :=
  ruleFor 231 lower99 none (by decide +kernel)

def rule231_29 : {c : Cut // CutGood (goalAt 231) c} :=
  ruleFor 231 lower230 (some (2,input 6,input 7)) (by decide +kernel)

def rule231_30 : {c : Cut // CutGood (goalAt 231) c} :=
  ruleFor 231 lower230 (some (1,input 6,input 7)) (by decide +kernel)

def rule231_31 : {c : Cut // CutGood (goalAt 231) c} :=
  ruleFor 231 lower230 (some (3,input 6,input 7)) (by decide +kernel)

def rule231_32 : {c : Cut // CutGood (goalAt 231) c} :=
  ruleFor 231 lower103 (some (0,input 1,input 6)) (by decide +kernel)

def rule231_33 : {c : Cut // CutGood (goalAt 231) c} :=
  ruleFor 231 lower103 (some (2,input 2,input 6)) (by decide +kernel)

def rule231_34 : {c : Cut // CutGood (goalAt 231) c} :=
  ruleFor 231 lower229 none (by decide +kernel)

def rule231_35 : {c : Cut // CutGood (goalAt 231) c} :=
  ruleFor 231 lower195 none (by decide +kernel)

def rule231_36 : {c : Cut // CutGood (goalAt 231) c} :=
  ruleFor 231 lower227 (some (1,input 1,input 5)) (by decide +kernel)

def rule231_37 : {c : Cut // CutGood (goalAt 231) c} :=
  ruleFor 231 lower227 (some (2,input 1,input 5)) (by decide +kernel)

def rule231_38 : {c : Cut // CutGood (goalAt 231) c} :=
  ruleFor 231 lower229 (some (3,input 2,input 5)) (by decide +kernel)

def rule231_39 : {c : Cut // CutGood (goalAt 231) c} :=
  ruleFor 231 lower229 (some (1,input 2,input 6)) (by decide +kernel)

def rule231_40 : {c : Cut // CutGood (goalAt 231) c} :=
  ruleFor 231 lower229 (some (1,input 2,input 7)) (by decide +kernel)

def rule231_41 : {c : Cut // CutGood (goalAt 231) c} :=
  ruleFor 231 lower167 none (by decide +kernel)

def rule231_42 : {c : Cut // CutGood (goalAt 231) c} :=
  ruleFor 231 lower227 (some (3,input 1,input 5)) (by decide +kernel)

def rule231_43 : {c : Cut // CutGood (goalAt 231) c} :=
  ruleFor 231 lower163 none (by decide +kernel)

def rule231_44 : {c : Cut // CutGood (goalAt 231) c} :=
  ruleFor 231 lower228 (some (3,input 2,input 5)) (by decide +kernel)

def rule231_45 : {c : Cut // CutGood (goalAt 231) c} :=
  ruleFor 231 lower103 (some (2,input 1,input 5)) (by decide +kernel)

def rule231_46 : {c : Cut // CutGood (goalAt 231) c} :=
  ruleFor 231 lower228 (some (1,input 2,input 6)) (by decide +kernel)

def rule231_47 : {c : Cut // CutGood (goalAt 231) c} :=
  ruleFor 231 lower227 (some (3,input 1,input 6)) (by decide +kernel)

def rule231_48 : {c : Cut // CutGood (goalAt 231) c} :=
  ruleFor 231 lower227 (some (2,input 1,input 6)) (by decide +kernel)

def rule231_49 : {c : Cut // CutGood (goalAt 231) c} :=
  ruleFor 231 lower230 (some (1,input 1,input 6)) (by decide +kernel)

def rule231_50 : {c : Cut // CutGood (goalAt 231) c} :=
  ruleFor 231 lower227 (some (1,input 1,input 6)) (by decide +kernel)

def rule231_51 : {c : Cut // CutGood (goalAt 231) c} :=
  ruleFor 231 lower227 (some (0,input 1,input 6)) (by decide +kernel)

def rule231_52 : {c : Cut // CutGood (goalAt 231) c} :=
  ruleFor 231 lower230 (some (3,input 1,input 6)) (by decide +kernel)

def rule231_53 : {c : Cut // CutGood (goalAt 231) c} :=
  ruleFor 231 lower103 (some (3,input 1,input 6)) (by decide +kernel)

def rule231_54 : {c : Cut // CutGood (goalAt 231) c} :=
  ruleFor 231 lower227 (some (2,input 5,input 6)) (by decide +kernel)

def rule231_55 : {c : Cut // CutGood (goalAt 231) c} :=
  ruleFor 231 lower195 (some (3,input 0,input 6)) (by decide +kernel)

def rule231_56 : {c : Cut // CutGood (goalAt 231) c} :=
  ruleFor 231 lower227 (some (2,input 5,input 7)) (by decide +kernel)

def rule231_57 : {c : Cut // CutGood (goalAt 231) c} :=
  ruleFor 231 lower227 (some (2,input 6,input 7)) (by decide +kernel)

def rule231_58 : {c : Cut // CutGood (goalAt 231) c} :=
  ruleFor 231 lower227 (some (3,input 6,input 7)) (by decide +kernel)

def rule231_59 : {c : Cut // CutGood (goalAt 231) c} :=
  ruleFor 231 lower227 (some (1,input 6,input 7)) (by decide +kernel)

def rule231_60 : {c : Cut // CutGood (goalAt 231) c} :=
  ruleFor 231 lower227 (some (3,input 5,input 6)) (by decide +kernel)

def rule231_61 : {c : Cut // CutGood (goalAt 231) c} :=
  ruleFor 231 lower227 (some (1,input 5,input 6)) (by decide +kernel)

def rule231_62 : {c : Cut // CutGood (goalAt 231) c} :=
  ruleFor 231 lower227 (some (0,input 5,input 6)) (by decide +kernel)

def rule231_63 : {c : Cut // CutGood (goalAt 231) c} :=
  ruleFor 231 lower227 (some (3,input 5,input 7)) (by decide +kernel)

def rule231_64 : {c : Cut // CutGood (goalAt 231) c} :=
  ruleFor 231 lower227 (some (1,input 5,input 7)) (by decide +kernel)

def rule231_65 : {c : Cut // CutGood (goalAt 231) c} :=
  ruleFor 231 lower230 (some (1,input 5,input 6)) (by decide +kernel)

def rule231_66 : {c : Cut // CutGood (goalAt 231) c} :=
  ruleFor 231 lower230 (some (3,input 5,input 6)) (by decide +kernel)

def rule231_67 : {c : Cut // CutGood (goalAt 231) c} :=
  ruleFor 231 lower230 (some (1,input 5,input 7)) (by decide +kernel)

def rule231_68 : {c : Cut // CutGood (goalAt 231) c} :=
  ruleFor 231 lower99 (some (3,input 1,input 6)) (by decide +kernel)

def rule231_69 : {c : Cut // CutGood (goalAt 231) c} :=
  ruleFor 231 lower99 (some (0,input 1,input 6)) (by decide +kernel)

def rule231_70 : {c : Cut // CutGood (goalAt 231) c} :=
  ruleFor 231 lower227 (some (0,input 6,input 7)) (by decide +kernel)

def rule231_71 : {c : Cut // CutGood (goalAt 231) c} :=
  ruleFor 231 lower166 none (by decide +kernel)

def cuts231 : Cuts (goalAt 231) := [rule231_0,rule231_1,rule231_2,rule231_3,rule231_4,rule231_5,rule231_6,rule231_7,rule231_8,rule231_9,rule231_10,rule231_11,rule231_12,rule231_13,rule231_14,rule231_15,rule231_16,rule231_17,rule231_18,rule231_19,rule231_20,rule231_21,rule231_22,rule231_23,rule231_24,rule231_25,rule231_26,rule231_27,rule231_28,rule231_29,rule231_30,rule231_31,rule231_32,rule231_33,rule231_34,rule231_35,rule231_36,rule231_37,rule231_38,rule231_39,rule231_40,rule231_41,rule231_42,rule231_43,rule231_44,rule231_45,rule231_46,rule231_47,rule231_48,rule231_49,rule231_50,rule231_51,rule231_52,rule231_53,rule231_54,rule231_55,rule231_56,rule231_57,rule231_58,rule231_59,rule231_60,rule231_61,rule231_62,rule231_63,rule231_64,rule231_65,rule231_66,rule231_67,rule231_68,rule231_69,rule231_70,rule231_71]

def state231_0 : List Sig := [0xffffffffccccccccffffffffcccccccc,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 5,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_0 : Impossible true (goalAt 231) 5 state231_0.toFinset :=
  node_ok cuts231 [] 0x1040041001040442021140441011041441010908021201051021200900824020901821032180482012081482011800841011088041010840821020840c24062800482011040442021040482002080082011050042021040442021040482032081c86032080c21202080c82022080821034000c21032080c4240 (by decide +kernel)

def state231_1 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f00000000,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_1 : Impossible true (goalAt 231) 4 state231_1.toFinset :=
  node_ok cuts231 [] 0x4100104004101108084101310046020104042502090082403090084200108004202104042120105002120105002400090002402109002420104046020104042120105002120090802180090802420109002103 (by decide +kernel)

def state231_2 : List Sig := [0xf0f0f0f0c0c0c0c0f0f0f0f0c0c0c0c0f0f0f0f0c0c0c0c0f0f0f0f0c0c0c0c,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_2 : Impossible true (goalAt 231) 4 state231_2.toFinset :=
  node_ok cuts231 [] 0x4100104004101108084101300044220104042102084082103090184600118004202104042120105002120105002400090002103119004202104044202104042120105002120090802103090182402090084240 (by decide +kernel)

def state231_3 : List Sig := [0xfffffffffffffffffffffffffffffffffafafafafafafafafafafafafafafafa,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_3 : Impossible true (goalAt 231) 4 state231_3.toFinset :=
  node_ok cuts231 [] 0x41013000442201040442021040441011080842021040441011080842001080042021040421010840421031090042401051021801090024201190024201090021030841821030900c21200900824020840d000a (by decide +kernel)

def state231_4 : List Sig := [0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0,input 6,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_4 : Impossible true (goalAt 231) 4 state231_4.toFinset :=
  node_ok cuts231 [] 0x21020840821030901821201050021201050021010840421031090042041081042061041424201090024200860041041041041051081841050840c41840840c4101090802120105002120090082402090182103 (by decide +kernel)

def state231_5 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000,input 6,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_5 : Impossible true (goalAt 231) 4 state231_5.toFinset :=
  node_ok cuts231 [] 0x24200848041440848046400908024201090024201088041840908024020900824060840c21020840821030901821201050021201050042201090042200911021010840421034000c4220084804140084804101 (by decide +kernel)

def state231_6 : List Sig := [0xffffffffffffffff0000000000000000ffffffff00000000,input 6,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_6 : Impossible true (goalAt 231) 4 state231_6.toFinset :=
  node_ok cuts231 [] 0x24200848041440848046400908024201090045011040441051040421201050021201050042001080042021040441001040041011080824020900824060840c2102084082103090182101084042103109004220 (by decide +kernel)

def state231_7 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_7 : Impossible true (goalAt 231) 5 state231_7.toFinset :=
  node_ok cuts231 [⟨state231_1,exclude231_1⟩,⟨state231_2,exclude231_2⟩,⟨state231_3,exclude231_3⟩,⟨state231_4,exclude231_4⟩,⟨state231_5,exclude231_5⟩,⟨state231_6,exclude231_6⟩] 0x10500420210400212010404410010500410110404212010808420280014410110404210318080c0018001060201088021031040441011141424201140441014002441011141600031041441010908041011151024200908021204002421201151200021051021200908021201191200011190042400908024201191024200908042404002442400901a00000900821030908024020901824200901821034002421030840c41400840824060848021020840c21200840c24061050024061080821801080041011090042001080842401080841010860041010848042400848041400860041400848021800848041401090041400840c42400840500030860021010840c21800840d0007109004240 (by decide +kernel)

def state231_8 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_8 : Impossible true (goalAt 231) 4 state231_8.toFinset :=
  node_ok cuts231 [] 0x908021201051021201190024200908042400900824020901821032180c82032081c82032080882022080c21200848041400848041400840421010840c41802080482012080c24440840821020840c2406104044101108802103 (by decide +kernel)

def state231_9 : List Sig := [0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_9 : Impossible true (goalAt 231) 4 state231_9.toFinset :=
  node_ok cuts231 [] 0x82022080482012080c24400848025400848024400840421010840c41050908024400908082800840c82031061021030840821020840c24062180c82032081c8203090802120105002120104044101104142103 (by decide +kernel)

def state231_10 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 6,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 7,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_10 : Impossible true (goalAt 231) 5 state231_10.toFinset :=
  node_ok cuts231 [⟨state231_5,exclude231_5⟩,⟨state231_8,exclude231_8⟩,⟨state231_9,exclude231_9⟩] 0x2180c82032081c820309080212010510212011900242009080424009080422080008242009008240209018210320808820120804820310900212010500212010500422010900422009110210108404210320a0042202080e00012080c42200848041400848041010840c82038000021030840821020840c2406 (by decide +kernel)

def state231_11 : List Sig := [0xf0f0f0f0c0c0c0c0f0f0f0f0c0c0c0c0f0f0f0f0c0c0c0c0f0f0f0f0c0c0c0c,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 5,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 7,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_11 : Impossible true (goalAt 231) 5 state231_11.toFinset :=
  node_ok cuts231 [⟨state231_2,exclude231_2⟩] 0x41013000441801040441001040041011080882021800841011088041010840c82038000021030840821020840c24060900046001180042021040486012180482031190021201050021201050042021040442021040482032081c82032180c2120105002120090802103090182402090084240 (by decide +kernel)

def state231_12 : List Sig := [0xfffffffffffffffffffffffffffffffffafafafafafafafafafafafafafafafa,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 5,input 7,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_12 : Impossible true (goalAt 231) 5 state231_12.toFinset :=
  node_ok cuts231 [⟨state231_3,exclude231_3⟩] 0x10404c00110600410110808410110404420210808410110404420220819000c1800841011088041010840c82038000021030840421060840c21030900c2402090082103400284200108004202104048201208048203109004240105108280109002420119002420109002120 (by decide +kernel)

def state231_13 : List Sig := [0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0,input 6,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 5,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_13 : Impossible true (goalAt 231) 5 state231_13.toFinset :=
  node_ok cuts231 [⟨state231_9,exclude231_9⟩,⟨state231_4,exclude231_4⟩] 0x82020840c82038000421030840821020840c24060840421031041600000840c24020900824060840c820120804820310900212010500212010500420410810420610414242010900242020a0041052080c41842080c41041041041051081841012180c82032081c8203090802120105002120 (by decide +kernel)

def state231_14 : List Sig := [0xffffffffccccccccffffffffccccccccffffffffcccccccc0000000000000000,input 6,input 5,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_14 : Impossible true (goalAt 231) 4 state231_14.toFinset :=
  node_ok cuts231 [] 0x908021201051021200900024000901021011140441011041441012180482012081482010840021000840424040840441010911021010840482014000c2101104004100104042120208008200208042120108004200109004101 (by decide +kernel)

def state231_15 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 5,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_15 : Impossible true (goalAt 231) 5 state231_15.toFinset :=
  node_ok cuts231 [⟨state231_14,exclude231_14⟩,⟨state231_5,exclude231_5⟩,⟨state231_8,exclude231_8⟩] 0x908021201051021200900824020901821031190024200908042400908041801061024202180c82032081c82032080882022080c21200840821020840c24060840421031060200020840c21032080e00010840c2120105002120105004380109004240106008201208048203800004140084804140084804101 (by decide +kernel)

def state231_16 : List Sig := [0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 5,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 7,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_16 : Impossible true (goalAt 231) 6 state231_16.toFinset :=
  node_ok cuts231 [⟨state231_0,exclude231_0⟩,⟨state231_7,exclude231_7⟩,⟨state231_10,exclude231_10⟩,⟨state231_11,exclude231_11⟩,⟨state231_12,exclude231_12⟩,⟨state231_13,exclude231_13⟩,⟨state231_15,exclude231_15⟩] 0x4001c410110404820330200c00180018c0801060082031040441011050042021040021201040441001050041011040421201080842021141424201140441014002441011141600051041441010908041012181c24202180c82034001c82032181d00072081c820309080820311510242009080212040024212011512000410510212009080212009019000a0900821030908024020901824200901821034002421031191200031190042400908024201191024200908042404002442404002d000b2080860200840c600210405000a1040460208000842201040421031040500070840c21032080d00072080d000a4001e00012080c21030840c21200901821021050021030840821200840c21031050024060901900084000c210110808828010800410110900420010808424010808410120a0041012080c424020806000020a0082012080c82802080d000710900424008480424008480414020a004140084808280084804140109004140 (by decide +kernel)

def state231_17 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffaaaaaaaaffffffffaaaaaaaa,input 5,0xfffffffffffffffffffffffffffffffffafafafafafafafafafafafafafafafa,input 7,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_17 : Impossible true (goalAt 231) 5 state231_17.toFinset :=
  node_ok cuts231 [] 0x410130004418010404420210404410110808420210404410110808420010800420210404820120804820310900232008480212208480230108404210308404424010510828010900a020208184140084802120400182101104046020084042101280042180084042120084042101400282104 (by decide +kernel)

def state231_18 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,0xfffffffffffffffffffffffffffffffffafafafafafafafafafafafafafafafa,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_18 : Impossible true (goalAt 231) 5 state231_18.toFinset :=
  node_ok cuts231 [⟨state231_3,exclude231_3⟩] 0x10808410110404420210808410110404420210404c00118080410110800420010808410110900414420a0042400988024200908824201090021808000042402080482012080c4240084808203208188203105108203090808203400286020104046020104050012105102180105102420086002420400282101 (by decide +kernel)

def state231_19 : List Sig := [0xfffffffffffffffffafafafafafafafa,input 6,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 1,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_19 : Impossible true (goalAt 231) 4 state231_19.toFinset :=
  node_ok cuts231 [] 0x28000a00008404240108404410109100210108c0421010840c210120800820020808a02010c0441011040c410130000c00010404820209000240008404a0010908082032080482010848082022080c820210404420210404c001 (by decide +kernel)

def state231_20 : List Sig := [0xfffffffffffffffffffffffffffffffffffffffffffffffffafafafafafafafa,input 6,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 7,input 1,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_20 : Impossible true (goalAt 231) 5 state231_20.toFinset :=
  node_ok cuts231 [⟨state231_19,exclude231_19⟩] 0x8404a00108600210108410210108404240108404410109100210109000240008405000a08c0421010840c21012080482012080c424010900414020a00414010c0441011040c41010988024200908824202081a00000848041013000441801040441041040441011080c4202 (by decide +kernel)

def state231_21 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,0xffffffffffffffff0000000000000000fafafafafafafafa,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 1,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_21 : Impossible true (goalAt 231) 4 state231_21.toFinset :=
  node_ok cuts231 [] 0x8410210108404240118000600018080210108c0421010840c210110900414020a0041401080042001080860201040041002080c42020900024000840460400908026200908824200848021201060024202080c4202104044101 (by decide +kernel)

def state231_22 : List Sig := [0xffffffffffffffff0000000000000000fafafafafafafafa,input 6,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 7,input 1,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_22 : Impossible true (goalAt 231) 5 state231_22.toFinset :=
  node_ok cuts231 [⟨state231_21,exclude231_21⟩] 0x8404a00108600210108410210108404240118000600018080210108c0421010840c21012080482012080c424010900414020a0041401080042001080860202081842022080e0000108084100104004140108082400090002101181002420098802422090808203400388203090802120084810006090804101 (by decide +kernel)

def state231_23 : List Sig := [0x55555555555555550000000000000000,input 6,0xfffffffffffffffffffffffffffffffffafafafafafafafafafafafafafafafa,input 7,input 1,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_23 : Impossible true (goalAt 231) 5 state231_23.toFinset :=
  node_ok cuts231 [] 0x210128004218008404210008400210118100210110404604008404230108404210308404820120804820310900232008480212208480430110404410310404820210404c001106004101104004100104042120181002101181002101109008280109004144301110006084804140084804202 (by decide +kernel)

def state231_24 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,0xfffffffffffffffffffffffffffffffffafafafafafafafafafafafafafafafa,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 1,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_24 : Impossible true (goalAt 231) 5 state231_24.toFinset :=
  node_ok cuts231 [⟨state231_21,exclude231_21⟩] 0x8410210108404240109000240008404604008404604018100210108404a00118100210108c0421010840c210110900414420a00424009880242009088242010e0042401090041802080482012080d00100848082032081882034003c82034003882030908041441060041444004a0000090804180090804101 (by decide +kernel)

def state231_25 : List Sig := [0xfffffffffffffffffffffffffffffffffafafafafafafafafafafafafafafafa,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 7,input 1,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_25 : Impossible true (goalAt 231) 6 state231_25.toFinset :=
  node_ok cuts231 [⟨state231_12,exclude231_12⟩,⟨state231_17,exclude231_17⟩,⟨state231_18,exclude231_18⟩,⟨state231_20,exclude231_20⟩,⟨state231_22,exclude231_22⟩,⟨state231_23,exclude231_23⟩,⟨state231_24,exclude231_24⟩] 0x100111040441012080cc0803000600063020041802080c41011040441441080842028001441011040441441040441014004842021080a00041080842020908041011040600031040441010908042021080860200840460001040460401800060201810060201040421010840500110840421012080ca0802800600022820021802080c210108405001209010210410510210108406000108404210110510240409004242018100240040028210109000242008404210140028604018100420220a00420010404424010800420210900420210404828010404230310900230108405001008404230380000210308404424008404820310900820140040828020804820320a00820340044424010901001010900424010510828010511001020a00828010510424010900262210900262009080464409080262211910242209080424009081000f4003c820640035000e400350006400182120 (by decide +kernel)

def state231_26 : List Sig := [0xffffffffffffffffffffffffffffffffafafafafaaaaaaaaafafafafaaaaaaaa,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 5,input 7,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_26 : Impossible true (goalAt 231) 5 state231_26.toFinset :=
  node_ok cuts231 [] 0x410130004418010404420210404410110808420210404410110808420010800420210404820120804820310900260009000240209000232008480212208480242209080262009080a0204004c2400190006020090002400280042180090002400084042101090002400084042101090004140 (by decide +kernel)

def state231_27 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0f0f0f0f00000000,input 6,input 5,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_27 : Impossible true (goalAt 231) 4 state231_27.toFinset :=
  node_ok cuts231 [] 0x2320084802122084802600090002402090006220180806022180808201208048203090808202208088203090802400094002401090002400181006020090002400084042420090006020084804140084804101 (by decide +kernel)

def state231_28 : List Sig := [0xffffffffffffffff00000000000000000f0f0f0f00000000,input 6,input 5,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_28 : Impossible true (goalAt 231) 4 state231_28.toFinset :=
  node_ok cuts231 [] 0x2320084802122084802600090002402090004200108004202104042400094002401090002400180002440090004100104004101108088201208048203090808202208088203090802101090002420090006020 (by decide +kernel)

def state231_29 : List Sig := [0xffffffffffffffffffffffffffffffff0f0f0f0f000000000f0f0f0f00000000,input 5,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_29 : Impossible true (goalAt 231) 5 state231_29.toFinset :=
  node_ok cuts231 [⟨state231_27,exclude231_27⟩,⟨state231_28,exclude231_28⟩] 0x10500420210400212010404410010500410110404212010808420280004410110404820318080c00180000602018080820310404410110808828010800410110900420010808424010808410120a00410108c88424008c80212020a00212008c88828008488212010900212009808424009800240040050240009809000a0900824001090024002080c424020804242020a0082012080c82802080c24201090024201808024000900041011910064001808064401808041010900024000848024000900041400940425000848025010900441400900024000908024000900082030860021010908021800908082030900024000848024202080841402080c82020848082032080c4140090802420 (by decide +kernel)

def state231_30 : List Sig := [0x55555555555555550505050500000000,input 6,input 5,input 7,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_30 : Impossible true (goalAt 231) 4 state231_30.toFinset :=
  node_ok cuts231 [] 0x820020800820210900230008400210208400430010400410210400210028000218008400210010400602008400410030000418010400212008488232008480a020105002100084802100108084100180804100 (by decide +kernel)

def state231_31 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,0xffffffffffffffff0f0f0f0f00000000ffffffffffffffff0f0f0f0f00000000,input 5,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_31 : Impossible true (goalAt 231) 4 state231_31.toFinset :=
  node_ok cuts231 [] 0x8c8021200848821200980024000900824000908824200988024202080482012080c60202080882022080c212009000250009004240009000210109080240009000a401180802400084804180084802420104044101180808203 (by decide +kernel)

def state231_32 : List Sig := [0xffffffffffffffff0f0f0f0f00000000ffffffffffffffff0f0f0f0f00000000,input 6,input 5,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 7,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_32 : Impossible true (goalAt 231) 5 state231_32.toFinset :=
  node_ok cuts231 [⟨state231_30,exclude231_30⟩,⟨state231_27,exclude231_27⟩,⟨state231_31,exclude231_31⟩] 0x2080482012080c424008c8021200848821200980024000900824001888060201808860200908824200988024202080824002900425800900024000940024010900024001810060200900024000840424200900060202080e00022080c6020084804140084804101090808203800048203084820000084802420 (by decide +kernel)

def state231_33 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000,input 5,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_33 : Impossible true (goalAt 231) 5 state231_33.toFinset :=
  node_ok cuts231 [⟨state231_27,exclude231_27⟩,⟨state231_31,exclude231_31⟩] 0x8c80212008488212009800240009008240010e0042401090041802080482012080d00142080882022080c212009000250009004240009000644019100240009000a4011910024000908024220988024200848041400848024200840424201060200010908024202080e00002080c4140084804140084804101 (by decide +kernel)

def state231_34 : List Sig := [0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000,input 5,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 7,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_34 : Impossible true (goalAt 231) 6 state231_34.toFinset :=
  node_ok cuts231 [⟨state231_26,exclude231_26⟩,⟨state231_29,exclude231_29⟩,⟨state231_32,exclude231_32⟩,⟨state231_33,exclude231_33⟩] 0x40054410110404820330200c0018000cc08010600820310404410110500420210400212010404410010500410110404212010808420210808828010800410110900420010808424010808410120a0041012080c424020805001420a0082012080c82802080d001510900424008c88424008c80212020a00212008c88828008488212010900212009808424009800240040050240009809000a0900824001090024004000900162080860200900024001040464401900060201910060201040424000900100150900024002080ca48029005000a2920025802080c240009000212009000240010500250109400212009404240110500240009000602009080242010405000a10404602080008602010404242010405001409080242010900262209089000a0988826201090024200908100150908024202080d00152080d000a4005600012080c24202080c212009080212010501000a105002120800002120105002420090810006400182101 (by decide +kernel)

def state231_35 : List Sig := [0xffffffffffffffffffffffffffffffff55555555555555555050505050505050,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 6,input 1,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_35 : Impossible true (goalAt 231) 4 state231_35.toFinset :=
  node_ok cuts231 [] 0x8404410109100210108400210008404240409000240009010210108c0421010840c210110c0441011040c41012081082042081821202080482012080c242010400410010404420610404c0011081841012080882022080c2120 (by decide +kernel)

def state231_36 : List Sig := [0x55555555555555555050505050505050,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 6,input 7,input 1,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_36 : Impossible true (goalAt 231) 5 state231_36.toFinset :=
  node_ok cuts231 [⟨state231_35,exclude231_35⟩] 0x210128004218008404210110404244008404210008400210109010230108404210308404820120804820310900430110404410310404232008480212208480820210404c001106004101104004100104044206090002400090102101090802620090882420800004202104044206104044140 (by decide +kernel)

def state231_37 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 1,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_37 : Impossible true (goalAt 231) 5 state231_37.toFinset :=
  node_ok cuts231 [] 0x8400210008404240409000240009010210108404604018100210108404a00118100210108c0421010840c210108c80212008488212009880242009088242020a0042401090082802080482012080d00182080882022080c21200908021201050021202180c82032081c8203105002120105002120106004105 (by decide +kernel)

def state231_38 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_38 : Impossible true (goalAt 231) 4 state231_38.toFinset :=
  node_ok cuts231 [] 0x8c8021200848821200988024200908824201081042041081841052080482012080c24402080882022080c24400908021201050021201040441011041421802180c82032081c8203104104104104144206084042101091008203 (by decide +kernel)

def state231_39 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 5,0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 7,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_39 : Impossible true (goalAt 231) 5 state231_39.toFinset :=
  node_ok cuts231 [⟨state231_38,exclude231_38⟩,⟨state231_9,exclude231_9⟩] 0x2080482012080c424008c8021200848821200988024200908824200990024408000424401081042041081841052080886032080c82072080c24200848041400848041011040441054001824402080e00002080c2120095002120091002420091002420108882101104148203106108203104104104104144206 (by decide +kernel)

def state231_40 : List Sig := [0xffffffff000000000000000000000000ffffffff0000000000000000,input 5,0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 7,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_40 : Impossible true (goalAt 231) 5 state231_40.toFinset :=
  node_ok cuts231 [] 0x82012080482031090023200848021220848026200908024220908023010840421030840482022180c82032081c820309080212010500212008404a001086002101084002100084042404090002400090102101108104204108184105104148203106108203104104104104144206104042440 (by decide +kernel)

def state231_41 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0,input 6,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_41 : Impossible true (goalAt 231) 5 state231_41.toFinset :=
  node_ok cuts231 [⟨state231_38,exclude231_38⟩,⟨state231_4,exclude231_4⟩] 0x8c8021200848821201081042041081841050988024200908824201090021808000442402080482012080c42402080882022080c41401041041041041442061040441052080c41842080c24200848041400848086032080c82072080c2120105002120208882180104160000104142420096002420086002101 (by decide +kernel)

def state231_42 : List Sig := [0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0,input 6,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 7,input 1,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_42 : Impossible true (goalAt 231) 6 state231_42.toFinset :=
  node_ok cuts231 [⟨state231_20,exclude231_20⟩,⟨state231_36,exclude231_36⟩,⟨state231_37,exclude231_37⟩,⟨state231_13,exclude231_13⟩,⟨state231_39,exclude231_39⟩,⟨state231_40,exclude231_40⟩,⟨state231_41,exclude231_41⟩] 0x4005c210108404820328200a00180018a08008600820308404210108480240408400414008404210008480210108404414009010240480014210108404410518100600480010604009100410508404210109080210109001000a09010240009080240409011000a08404210108c0c424008c04210140060210108c0e00030840c21011090021012080c424020805001820a0082012080c82802080d001710900424008c88424008c80212020a00212008c88828008488212010900212010818828010810410510900420410818424010818410520a00410509888828009880242010900242009888424009088242020a0024204000900192080900171041441052080cc0842080e00023021041842080c41052080c41401081841040848041051041041401041441050848042061081900064001841012181c24202180c82034005c82032181d00172081c8203090808203105002420090802120800042120105020000105002120090802120 (by decide +kernel)

def state231_43 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0a0a0a0a0f0f0f0f0a0a0a0a,input 5,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 7,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_43 : Impossible true (goalAt 231) 5 state231_43.toFinset :=
  node_ok cuts231 [] 0x410130004418010404450011400410110808420010800420210404820120804820310900232008480212208480260009000240209000860209000640018080240009000a0010860024000900025000840424001040442021040445010908024220988024202080c82072080c8603084804140084802420084042400084042400 (by decide +kernel)

def state231_44 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffaaaaaaaaffffffffaaaaaaaa,input 5,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 7,input 1,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_44 : Impossible true (goalAt 231) 6 state231_44.toFinset :=
  node_ok cuts231 [⟨state231_43,exclude231_43⟩,⟨state231_17,exclude231_17⟩] 0x41013000441801040442021040441011080842021040441011080845011040441051040486032080c82072080c242008482000108480250108404210508406000009080242040018420010800420210404262009080242209080820120804820310900232008480212208480230108404210308404424020a00828010900a02040068414008404410118080210108404a001086002101084802101090142404 (by decide +kernel)

def state231_45 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 6,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_45 : Impossible true (goalAt 231) 5 state231_45.toFinset :=
  node_ok cuts231 [⟨state231_38,exclude231_38⟩] 0x24200848041440848086032080c82072080c24201808200000908025800908024200860026200908024220908023200848021220848082012080482031090062201808060221808023801090042400860082022080882031050060200848041400848060402080c60202080c4101084802180084808222084042101181008203 (by decide +kernel)

def state231_46 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f00000000,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_46 : Impossible true (goalAt 231) 5 state231_46.toFinset :=
  node_ok cuts231 [⟨state231_1,exclude231_1⟩] 0x10400410010404420210404c40118080410110800420010808410108c8021200848821201090021808000042402180486012180c42402180886022180c4140180804101180804101084804140084808222090002420104046020104042420090882620090802120105002120090802180090802420096008203 (by decide +kernel)

def state231_47 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000,input 6,input 5,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_47 : Impossible true (goalAt 231) 5 state231_47.toFinset :=
  node_ok cuts231 [⟨state231_5,exclude231_5⟩] 0x908021201051021201910024200908060400908060201061024202180c82032081c820309880242009088242008c8021200848821201090060408000042401888060201808860202080482012080d00032080882022080d0000084804140084808222180806040180804222084046020084804140084804101 (by decide +kernel)

def state231_48 : List Sig := [0xffffffffffffffff0000000000000000ffffffff00000000,input 6,input 5,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_48 : Impossible true (goalAt 231) 5 state231_48.toFinset :=
  node_ok cuts231 [⟨state231_6,exclude231_6⟩] 0x24200848041440848064400908024201810045011040441051040426200908024220908023200848021220848042401810200001090042001080042021040421201050021202088860001800060401040441001040041011080882032180c82072080c82012080482031090082022080882031050021010840421802080c6020 (by decide +kernel)

def state231_49 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 1,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_49 : Impossible true (goalAt 231) 6 state231_49.toFinset :=
  node_ok cuts231 [⟨state231_45,exclude231_45⟩,⟨state231_7,exclude231_7⟩,⟨state231_46,exclude231_46⟩,⟨state231_18,exclude231_18⟩,⟨state231_41,exclude231_41⟩,⟨state231_47,exclude231_47⟩,⟨state231_48,exclude231_48⟩] 0x41401080841000848041011040041401040441010848042021080a00061040441012080c60203000600051808060202080c410110404450509080450110405001c10404450580010410510404242010404454409080242008481001c0848045448000c414408480242008480258440028258008600242009080258409080242008601001c0860086078000886032080c24202080c86070908082072080d001c2080c420220a00420010404424010800420210900420210404828010404262210900262009080464409080262211910242209080424009080232210900232008480828008480232220a0021220848042400848100041090042400860100040860100044002a00010860042401090082031090082014000c828020804820320a0082034000c424010900820310500820240000212020808820308480820340000414010500602008600602010405000a10404602080000602010404218010404212040048212010500218010500212008600212010501000a20889001b400142101 (by decide +kernel)

def state231_50 : List Sig := [0x55555555555555555555555500000000,input 5,input 6,input 7,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_50 : Impossible true (goalAt 231) 5 state231_50.toFinset :=
  node_ok cuts231 [] 0x860220808820620808450010400410410400250008400210408400262009080242209080820020800820210900430010400410210400230008400210208400410030000418010400210028000218008400210010400602008400212010510242008480212008488232008480a020108084100180804100090102100084802100 (by decide +kernel)

def state231_51 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 5,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_51 : Impossible true (goalAt 231) 5 state231_51.toFinset :=
  node_ok cuts231 [⟨state231_8,exclude231_8⟩] 0x24200848041440848064400908024201810045800908024201060086032080c82072080c2620090802422090802320084802122084804240181020000109004380109004240106008201208048203180808202208088203084802120105002120105002101180808203180808203084804180084810012104044101180808203 (by decide +kernel)

def state231_52 : List Sig := [0xffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f00000000,input 5,input 6,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_52 : Impossible true (goalAt 231) 4 state231_52.toFinset :=
  node_ok cuts231 [] 0x8c8021200848821201180046001180845010980024000900824002080482012080c24201140045001140446021040441011808045010900025000900424000900064001808024000900021010908024002080882022080c2420 (by decide +kernel)

def state231_53 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f0f0f0f0f0f0f0f0f00000000,input 5,input 6,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 7,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_53 : Impossible true (goalAt 231) 5 state231_53.toFinset :=
  node_ok cuts231 [⟨state231_52,exclude231_52⟩] 0x820120804820310900232008480212208480460011800460211404260009000240209000820211404c40111600450111400450011404460209000a401096002400090002500090042400090006400180802400090802422098802420090808203800008203084804144084802420104044101180804501084042400090802400 (by decide +kernel)

def state231_54 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 5,input 6,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 7,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_54 : Impossible true (goalAt 231) 6 state231_54.toFinset :=
  node_ok cuts231 [⟨state231_50,exclude231_50⟩,⟨state231_47,exclude231_47⟩,⟨state231_45,exclude231_45⟩,⟨state231_51,exclude231_51⟩,⟨state231_10,exclude231_10⟩,⟨state231_53,exclude231_53⟩,⟨state231_39,exclude231_39⟩] 0x2180c82032081c82030908021201051021200908060208001824201910024200908060408001424200908100060988024200908824202080482012080c424008c80212008488212018880602018088602010900604080010424020a0042401090082802080860202080e00032080c6020084804140084804101181008203800088203084804140084804140180806040108882101400148203800048203084820000084810012 (by decide +kernel)

def state231_55 : List Sig := [0xffffffffffffffffffffffffffffffff00000000ffffffff0000000000000000,input 5,input 6,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_55 : Impossible true (goalAt 231) 5 state231_55.toFinset :=
  node_ok cuts231 [] 0x908021201051021200908060201061024200900024000901021012180c82032081c820309880242009088242008c80212008488212018880602018088602008c0421010840c21012080482012080d000318080212010500212010404410110600820308400210008404240418000600018080210108404a0011810021012080882022080c2120 (by decide +kernel)

def state231_56 : List Sig := [0xf0f0f0f0fffffffff0f0f0f0f0f0f0f0f0f0f0f0fffffffff0f0f0f0f0f0f0f0,input 5,input 6,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 7,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_56 : Impossible true (goalAt 231) 5 state231_56.toFinset :=
  node_ok cuts231 [] 0x820120804820310900232008480212208480420410810420610414230108404210308404262009080242209080820210414820310610820310410410410414420608404a0010860021010840021000840424041800060001808021012180c82032081c8203090802120105002120104044101104142420090002400090102101 (by decide +kernel)

def state231_57 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,0xffffffff000000000000000000000000ffffffff0000000000000000,input 5,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_57 : Impossible true (goalAt 231) 5 state231_57.toFinset :=
  node_ok cuts231 [] 0x908021201051021200900024000901021012180c82032081c820309880242009088242008c80212008488212008c0421010840c21012080482012080c60202080882022080c2120084002100084042404180006000180802101106002420106102420109004380109004180105002120105002120181004101 (by decide +kernel)

def state231_58 : List Sig := [0xffffffff000000000000000000000000ffffffff0000000000000000,input 5,input 6,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 7,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_58 : Impossible true (goalAt 231) 6 state231_58.toFinset :=
  node_ok cuts231 [⟨state231_55,exclude231_55⟩,⟨state231_56,exclude231_56⟩,⟨state231_57,exclude231_57⟩,⟨state231_40,exclude231_40⟩] 0x2180c82032081c82030908021201051021200908060208000c24200900024000901021010988024200908824202080482012080c424008c80212008488212018880602018088602008c0421010840c21012080860202080e00022080c6020084804140084802101280042180084042100084002101090106000180802101400182420800042420109008280109008280400148203800008203105002120105002120104046040 (by decide +kernel)

def state231_59 : List Sig := [0x3333333333333333333333333333333333333333333333332222222222222222,input 6,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 7,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_59 : Impossible true (goalAt 231) 5 state231_59.toFinset :=
  node_ok cuts231 [] 0x210128004218008404230008c0021010901062001080042201080024000900024040840486032080c82072080c242008c80414408c80460010800420410800820010800c001106004200108004300104044200084042103084042301109002420119002420109008203208048201084802120105002320104044200104044200 (by decide +kernel)

def state231_60 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaa,input 6,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 7,input 1,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_60 : Impossible true (goalAt 231) 6 state231_60.toFinset :=
  node_ok cuts231 [⟨state231_59,exclude231_59⟩,⟨state231_20,exclude231_20⟩] 0x21012800421800840424040840421010901021011040460400840424040840421010901024000900024040840486032080c82072080c24201050041440908045011040441051040424204001a00010908023010840421030840426200908024220908082012080482031090042401050082801050043011040441031040600001090042404000cc04040074212010404c0011060041011050041011080c4202 (by decide +kernel)

def state231_61 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f5f5f5f5f5f5f5f5f0f0f0f0f0f0f0f0,input 6,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 7,input 1,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_61 : Impossible true (goalAt 231) 5 state231_61.toFinset :=
  node_ok cuts231 [] 0x210128004218008404210008400210109010210110404244008404230108404210308404820120804820310900232008480212208480430110404410310404262009080242209080820210404c0011060041011040041001040442060900024000901021012180c82032081c8203090802120105002120114044101104144101 (by decide +kernel)

def state231_62 : List Sig := [0x55555555555555550000000000000000,input 6,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 7,input 1,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_62 : Impossible true (goalAt 231) 6 state231_62.toFinset :=
  node_ok cuts231 [⟨state231_61,exclude231_61⟩,⟨state231_23,exclude231_23⟩] 0x21012800421800840421000840021010901021011040460400840424000900024040840486032080c82072080c242008482000108480450110404410510404230108404210308404262009080242209080820120804820310900232008480212208480430110404410310404820210404c00110600410110400410108480604008404604008405000609082000009080424020a00424020a01001e105004202 (by decide +kernel)

def state231_63 : List Sig := [0x3333333333333333333333333333333333333333333333330000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_63 : Impossible true (goalAt 231) 5 state231_63.toFinset :=
  node_ok cuts231 [] 0x8400210008404240408404604018100210108404820118100210109000240009010210109080212010510212009080418010610242021804820120814820120800820020804212010500212010500212010800424008404604008404424009080464009080414008480414008480418010900424010e010020 (by decide +kernel)

def state231_64 : List Sig := [0xfffffffffffffffffffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 1,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_64 : Impossible true (goalAt 231) 5 state231_64.toFinset :=
  node_ok cuts231 [] 0x2100084002101090102101181006040084042101280146040084042400090002404084042301084042103084042320084802122084804380109004240106008205208148207400602620090802422090808206208188207084802120090804140084804140084804140084804105400848203 (by decide +kernel)

def state231_65 : List Sig := [0xffffffff00000000ffffffff00000000ffffffff0000000000000000,input 5,input 6,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_65 : Impossible true (goalAt 231) 5 state231_65.toFinset :=
  node_ok cuts231 [] 0x24200848041440848024201808041840908024000900024040840426200908024220908023200848021220848062201808060221808023010840421030840460200848041400848021000840021010901060001800060200840482032180c82072080c82012080482034000c82022080882030848041011040441802080c6040 (by decide +kernel)

def state231_66 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 1,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_66 : Impossible true (goalAt 231) 6 state231_66.toFinset :=
  node_ok cuts231 [⟨state231_63,exclude231_63⟩,⟨state231_15,exclude231_15⟩,⟨state231_64,exclude231_64⟩,⟨state231_37,exclude231_37⟩,⟨state231_24,exclude231_24⟩,⟨state231_33,exclude231_33⟩,⟨state231_47,exclude231_47⟩,⟨state231_65,exclude231_65⟩,⟨state231_51,exclude231_51⟩,⟨state231_57,exclude231_57⟩] 0x21200901021001050021010840021200840421011050024040901200090840421011060060401810200081810060401060021010840600070840421012080c60402800600061810060402080c210108404240480014240008404242009000240409080240408405001c08404454409080242008481001c08480454480010414408480242008480458409080242010601001c1060045848000c41841060024200908086070908086032080d001c2080c86078000882072080c24202080c230310900230108405000408404230380004210308404424008404262210900262009080464409080262211910242209080424009080232210900232008480828008480232220a00212208480424008481000420a0043801060042401090100041090042401060082801060082038000082014000c42402080482031090082034000d00044000c820308480820240000414020808820310500820340000212008480414040048414008480418008480414010600414008481001208481001f400144101 (by decide +kernel)

def state231_67 : List Sig := [0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 7,input 1,input 2,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_67 : Impossible true (goalAt 231) 7 state231_67.toFinset :=
  node_ok cuts231 [⟨state231_16,exclude231_16⟩,⟨state231_25,exclude231_25⟩,⟨state231_34,exclude231_34⟩,⟨state231_42,exclude231_42⟩,⟨state231_44,exclude231_44⟩,⟨state231_49,exclude231_49⟩,⟨state231_54,exclude231_54⟩,⟨state231_58,exclude231_58⟩,⟨state231_60,exclude231_60⟩,⟨state231_62,exclude231_62⟩,⟨state231_66,exclude231_66⟩] 0x40015000510404410140014820330200c00140016000a3020041804001482031040441014004841401080841008002421201040441008002041401040441014004821201080842028001c602008404600040028410118100600080018602018100602040028410108404210140015000508404210140014820328200a0014001600052820021804001482030840421014004821200901021004002841400840421008001021200840421014002841400901024044001845050908045014001841014001841014001845058000c410540018410109080410140018240480008240040018210109080240040018240409080240440018210140018210140018860709080860340018820340018820340018860740014820740018820309080820340018454409080242040018212040018212040018454480004414440018212009080212040010420220a0042004000c41011090042004001042021090042024000c410120a0041014001023031090023014000c21014001021014001023038000021034000c210110900210140018262210900262040018242011910242040018262211910242240018242010900242040014820310900820140015000320a00820140014820320a0082034001500051090042404001023221090023204000c212020a00212040010232220a0021224000c2120109002120400010002400008202 (by decide +kernel)

def state231_68 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,0xffffffffffffffffffffffffffffffffffffffffcccccccc0000000000000000,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_68 : Impossible true (goalAt 231) 4 state231_68.toFinset :=
  node_ok cuts231 [] 0x9100242009080828021808820220818820211404410110414410108480242010510212008500212008480412020c0882022080c820210400410010404240620800820020808c0200840421010840c410130000c000108804101 (by decide +kernel)

def state231_69 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffcccccccc0000000000000000,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 6,input 5,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_69 : Impossible true (goalAt 231) 5 state231_69.toFinset :=
  node_ok cuts231 [⟨state231_68,exclude231_68⟩] 0x24020900824060840c450110404410510404868009080242020a00860220808820620808212009080414408480210208408210309018410010400410108480414008480212010500830220808820320808210310406000010404210128008820220880820230000c00030100410110a0041011040c410120800820020808c040 (by decide +kernel)

def state231_70 : List Sig := [0xffffffffeeeeeeeeaaaaaaaaaaaaaaaaffffffffeeeeeeeeaaaaaaaaaaaaaaaa,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 2,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_70 : Impossible true (goalAt 231) 4 state231_70.toFinset :=
  node_ok cuts231 [] 0x21808820220818820209100242009080828011404410110414410109080212010510212020800820020808c0200840421010840c410108480214008480412030000c00020880410120c0882022080c8202104004100104042406 (by decide +kernel)

def state231_71 : List Sig := [0xfffffffffcfcfcfcf0f0f0f0f0f0f0f0fffffffffcfcfcfcf0f0f0f0f0f0f0f0,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 0,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_71 : Impossible true (goalAt 231) 4 state231_71.toFinset :=
  node_ok cuts231 [] 0x20c0882022080c820208500212008480412010400410010404240608480242010510212020800820020808c0200840421010840c410109080244009080828030000c000208804101218088202208188202114044101104144101 (by decide +kernel)

def state231_72 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,0xffffffffcccccccc0000000000000000ffffffffcccccccc0000000000000000,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 0,input 2,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_72 : Impossible true (goalAt 231) 5 state231_72.toFinset :=
  node_ok cuts231 [⟨state231_68,exclude231_68⟩,⟨state231_70,exclude231_70⟩,⟨state231_71,exclude231_71⟩] 0x21808820220818820209100242009080828009080422080008242011404410110414410120c0882022080c820208480242010510212008500212008480412008480422080004212010400410010404240620800820020808c0200840421010840c410110880820280000820210900420230000c000208804101 (by decide +kernel)

def state231_73 : List Sig := [0xffffffffeeeeeeeeaaaaaaaaaaaaaaaaffffffffeeeeeeeeaaaaaaaaaaaaaaaa,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 6,input 5,input 2,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_73 : Impossible true (goalAt 231) 5 state231_73.toFinset :=
  node_ok cuts231 [⟨state231_70,exclude231_70⟩] 0x86022080882062080824020900824060840c450110404410510404868009080242020a00242008480414408480a0022080882202080821031040600001040421010840821020840c240630000c00030100410120800820020808c0401080441011040c410108480414008480414020c0882022080c8202104004100104042120 (by decide +kernel)

def state231_74 : List Sig := [0xfffffffffcfcfcfcf0f0f0f0f0f0f0f0fffffffffcfcfcfcf0f0f0f0f0f0f0f0,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 6,input 5,input 0,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_74 : Impossible true (goalAt 231) 5 state231_74.toFinset :=
  node_ok cuts231 [⟨state231_71,exclude231_71⟩] 0x830220808820320808210208408210309018410010400410110818414008480212010500212009080414408480a00220808822020808210310406000010404210109008240209018210330000c00030100410120800820020808c0401081041011040c4101090804240090808280218088202208188202114044101104144101 (by decide +kernel)

def state231_75 : List Sig := [0xffffffffcccccccc0000000000000000ffffffffcccccccc0000000000000000,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 6,input 5,input 0,input 2,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_75 : Impossible true (goalAt 231) 6 state231_75.toFinset :=
  node_ok cuts231 [⟨state231_69,exclude231_69⟩,⟨state231_72,exclude231_72⟩,⟨state231_73,exclude231_73⟩,⟨state231_74,exclude231_74⟩] 0x21808820220818820209008240209018210311404410110414410121a0024200908082800908100248000c242020c0882022080c82020848024201051021200840821020840c240610400410010404212010500212008480414008481000b8000821202800882022088082020840c41018000441010840421034008d00220840cc00030000c0401040482002080082023010082801040441034001c8202800008202108084240 (by decide +kernel)

def state231_76 : List Sig := [0xffffffffffffffffffffffffcccccccc,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 6,input 5,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_76 : Impossible true (goalAt 231) 5 state231_76.toFinset :=
  node_ok cuts231 [] 0x24020900824060840cc40030000c00430000860020800820420800212009080414408480210208408210309018c10030000c00130000830020800820120800600230000422030000a00020800c00010808820020808820621808820220808820320c08820220808822028008820210404c00010808c000109008200208088200 (by decide +kernel)

def state231_77 : List Sig := [0xffffffff00000000cccccccc00000000ffffffff00000000cccccccc,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 6,input 0,input 2,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_77 : Impossible true (goalAt 231) 5 state231_77.toFinset :=
  node_ok cuts231 [] 0x21808820220818820211808420210818420209000240009010210120c0882022080c820208480242010510212010c0842021080c420208400210008404240410808820230100420228000a00020808210118000600010808210120808822020808a0020840c24060900824020901821030840821021040441011080860021090021010840c2101 (by decide +kernel)

def state231_78 : List Sig := [0x5555555555555555555555554444444455555555555555555555555544444444,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 6,input 5,input 2,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_78 : Impossible true (goalAt 231) 5 state231_78.toFinset :=
  node_ok cuts231 [] 0x86022080882062080824020900824060840c450010400410410400464009080242010900a00220808822020808600210400422010400210010400c10030100410020c00830020808424010c004100108084100208088203208088302084804144090802120090182103084082102108084100108084100105002120084804140 (by decide +kernel)

def state231_79 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0c0c0c0c0f0f0f0f0f0f0f0f0f0f0f0f0c0c0c0c,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 6,input 5,input 0,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_79 : Impossible true (goalAt 231) 5 state231_79.toFinset :=
  node_ok cuts231 [] 0x830220808820320808210208408210309018450011400450110808414008480212010500a00220808822020808600211404422011404240031000c4003010045012180086002080842401180046001080845012080882062080886020848041440848024200840c2406090082402104044101108084501109002420090804640 (by decide +kernel)

def state231_80 : List Sig := [0xffffffffffffffffffffffffccccccccffffffffffffffffffffffffcccccccc,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 6,input 5,input 0,input 2,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_80 : Impossible true (goalAt 231) 6 state231_80.toFinset :=
  node_ok cuts231 [⟨state231_76,exclude231_76⟩,⟨state231_77,exclude231_77⟩,⟨state231_78,exclude231_78⟩,⟨state231_79,exclude231_79⟩] 0x86022080882062080824020900824060840c46021080842061080846400908024201090200030908024204009083022080882032080821200908041440848021020840821030901843021080842031080841400848021201050200020848021204002ca00220808822020808600210808422010808604080004420220808c04010808410120808c0402080842401080842401040c82802080a0000208090007 (by decide +kernel)

def state231_81 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,0xf0f0f0f0c0c0c0c00000000000000000f0f0f0f0c0c0c0c,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 0,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_81 : Impossible true (goalAt 231) 4 state231_81.toFinset :=
  node_ok cuts231 [] 0x83022080882032080825400848021200910041001040041010901886002180082020910024000900021031040482022081882022180821201050021200908082800840c410109008410130000c000208804101 (by decide +kernel)

def state231_82 : List Sig := [0xf0f0f0f0c0c0c0c00000000000000000f0f0f0f0c0c0c0c,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 6,input 5,input 0,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_82 : Impossible true (goalAt 231) 5 state231_82.toFinset :=
  node_ok cuts231 [⟨state231_81,exclude231_81⟩] 0x830220808820320808210208408210309018410010400410110818414008480212010500a00220808822020808210310406000010404240030000c0003010041012180086002080842401080042001081841012080882062080886020848041400848024200840c2406090082402108088280 (by decide +kernel)

def state231_83 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,0xffffffffcccccccc0000000000000000ffffffffcccccccc,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 0,input 2,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_83 : Impossible true (goalAt 231) 5 state231_83.toFinset :=
  node_ok cuts231 [⟨state231_81,exclude231_81⟩] 0x86022080882062080846400908024201090045011040441051040483022080882032080821200908041440848041400848021201050041001040041010901882023010082021090042001080021031040482023010082021088024208000024201088021201050021201088024440840c410110808410130000c000208804101 (by decide +kernel)

def state231_84 : List Sig := [0xffffffffcccccccc0000000000000000ffffffffcccccccc,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 6,input 5,input 0,input 2,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_84 : Impossible true (goalAt 231) 6 state231_84.toFinset :=
  node_ok cuts231 [⟨state231_82,exclude231_82⟩,⟨state231_83,exclude231_83⟩] 0x21808820220818820209008240209018210311404410110414410111900242009080424020c0882022080c82020848024201051021200840821020840c24061040041001040421201050021200848041402800882022088082020840c410180004410118100c00030000c04010404820230100820210900420010900410120808c04020808c0400908200000908100240848041400848041400840d00220840d0023108088280 (by decide +kernel)

def state231_85 : List Sig := [0xffffffff33333333ffffffff00000000ffffffff33333333ffffffff00000000,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 6,input 0,input 2,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_85 : Impossible true (goalAt 231) 5 state231_85.toFinset :=
  node_ok cuts231 [] 0x21808820220818820211808420210818420219100242009080604009008240209018210320c0882022080c820208480242010510212010c0842021080c42021050021200848041400840821020840c24061080882023010042022080082002080860401080042001080824442800882022088082021040441011088042020840421010840c4240 (by decide +kernel)

def state231_86 : List Sig := [0xf0f0f0f0f3f3f3f3f0f0f0f0f0f0f0f0f0f0f0f0f3f3f3f3f0f0f0f0f0f0f0f0,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 6,input 5,input 0,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_86 : Impossible true (goalAt 231) 5 state231_86.toFinset :=
  node_ok cuts231 [] 0x830220808820320808210208408210309018430210808420310808414008480212010500212009080414008480a002208088220208086002108084220108082101108088202301004202208008200208084640108004200108084105218088202208188202090082402090182103104044101104144202119002420090804240 (by decide +kernel)

def state231_87 : List Sig := [0x33333333000000000000000000000000333333330000000000000000,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 6,input 5,input 0,input 2,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_87 : Impossible true (goalAt 231) 6 state231_87.toFinset :=
  node_ok cuts231 [⟨state231_85,exclude231_85⟩,⟨state231_86,exclude231_86⟩] 0x86022080882062080824020900824060840c460210808420610808868009080242020a00830220808820320808212009080414408480210208408210309018430210808420310808414008480212010500a00220808822020808600210808422010808210110808820230100420220800820020808c04010800420220a00c04020808c040208090024090820001090804140084804140084820000104044240 (by decide +kernel)

def state231_88 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0c0c0c0c0f0f0f0f0c0c0c0c,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 7,input 5,input 0,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_88 : Impossible true (goalAt 231) 5 state231_88.toFinset :=
  node_ok cuts231 [] 0xc40031000c44010404410010400410110808210208408210309018830220808820320808414008480212010500600210404422010404a0022080882202080824001180046001080841012180086002080846401080841011080841010848041400848024200840c2406090082402208088206208088602109002420090804640 (by decide +kernel)

def state231_89 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffccccccccffffffffcccccccc,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 7,input 5,input 0,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_89 : Impossible true (goalAt 231) 6 state231_89.toFinset :=
  node_ok cuts231 [⟨state231_88,exclude231_88⟩] 0x410120808c0801040441011080842021040445011040441051040424020900824060840c860220808820620808868009080242020a02000009080242040090410010400410110808212009080414408480210208408210309018830220808820320808414008480212010500414008480212010500600210404422010404a00220808822020808a08040010c0401080841011080841012080882804001c4240 (by decide +kernel)

def state231_90 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,0xf0f0f0f0c0c0c0c0f0f0f0f0c0c0c0c,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 0,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_90 : Impossible true (goalAt 231) 4 state231_90.toFinset :=
  node_ok cuts231 [] 0xc0003000042201040441001040041011080841400848021201050021020840821030901846001180042021040424000900021031190042021040442021040421201050021200908042400840c2406090082402 (by decide +kernel)

def state231_91 : List Sig := [0xf0f0f0f0c0c0c0c0f0f0f0f0c0c0c0c,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 7,input 5,input 0,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_91 : Impossible true (goalAt 231) 5 state231_91.toFinset :=
  node_ok cuts231 [⟨state231_90,exclude231_90⟩] 0xc00030000c0401040441001040041011080821020840821030901883062081882072081841400848021201050060021040442201040421032081a00000840c24001180046001080841012080082002081846401080841011080841010848041400848024200840c2406090082402208084240 (by decide +kernel)

def state231_92 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,0xffffffffccccccccffffffffcccccccc,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 0,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_92 : Impossible true (goalAt 231) 5 state231_92.toFinset :=
  node_ok cuts231 [⟨state231_90,exclude231_90⟩] 0xc00030000422010404450110404410510404868009080242020a0024020900824060840c41001040041011080821200908041440848041400848021201050021020840821030901842021040442021040482002080021033010042021040442021040424208000024202088021201050021202088042400840c8220208088202 (by decide +kernel)

def state231_93 : List Sig := [0xffffffffccccccccffffffffcccccccc,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 7,input 5,input 0,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_93 : Impossible true (goalAt 231) 6 state231_93.toFinset :=
  node_ok cuts231 [⟨state231_91,exclude231_91⟩,⟨state231_92,exclude231_92⟩,⟨state231_0,exclude231_0⟩] 0x30000c00030100410111404410110414410109008240209018210309080c04030110242021a0024200908082801040041001040442020848024201051021200840821020840c240608480c0408000821201050021200848041401800841011088041010840cc04080004210328200420210404420210404820020a00c0401080841011080841010908200000908100240848041400848041400840d00220840d0007208084240 (by decide +kernel)

def state231_94 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000,input 7,input 6,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_94 : Impossible true (goalAt 231) 5 state231_94.toFinset :=
  node_ok cuts231 [⟨state231_5,exclude231_5⟩] 0x1190024200908042400908042203021024200908082203011024200900824020901821030848024201051021201050021200848041400848042201050021200848082208000021200840821020840c240610880424010880244420880c0402088042400840421010840d0022108808220301004220104048202 (by decide +kernel)

def state231_95 : List Sig := [0xffffffffffffffffffffffff00000000,input 7,input 6,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_95 : Impossible true (goalAt 231) 5 state231_95.toFinset :=
  node_ok cuts231 [] 0x464009080242010900242010880c08409080860220808820620808212009080414408480414008480212010500212010880414008480830220808820320808422010900422009110820020800820210900c00030000c0802080824020900824060840c210208408210309018210108404210320a0041011040442200840c8220 (by decide +kernel)

def state231_96 : List Sig := [0xffffffffccccccccffffffffccccccccffffffffccccccccf0f0f0f0c0c0c0c0,input 7,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_96 : Impossible true (goalAt 231) 3 state231_96.toFinset :=
  node_ok cuts231 [] 0x8400210008404240620c1882062081c820608480242020a04212030000c000300802101090002400090182101208008200208182420 (by decide +kernel)

def state231_97 : List Sig := [0xfffffffffffffffffffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0,input 7,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_97 : Impossible true (goalAt 231) 4 state231_97.toFinset :=
  node_ok cuts231 [⟨state231_96,exclude231_96⟩] 0x254008480212009100210208408210309018830620818820720818212009080414008480210108404210310414820420810820609100242009100242080000210330010c0400840c41011040441050840c8202 (by decide +kernel)

def state231_98 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_98 : Impossible true (goalAt 231) 5 state231_98.toFinset :=
  node_ok cuts231 [⟨state231_8,exclude231_8⟩,⟨state231_97,exclude231_97⟩] 0x46400908024201090024020900824060840c242030100c04409080242010882000109080212009080414408480414008480212010500210208408210309018212030102000008480212010880414008480210108404210320a00424028100828010900422010900422009110210330200c0400840c41011040442200840c8202 (by decide +kernel)

def state231_99 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0,input 7,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_99 : Impossible true (goalAt 231) 4 state231_99.toFinset :=
  node_ok cuts231 [] 0x950021200848024400840821020840c240620c0882022080c82020848024201050021200840421010840c410520800820020808c02030000c000208808202091002420090808280104044101104142103218088202208188202 (by decide +kernel)

def state231_100 : List Sig := [0xffffffffffffffff0000000000000000,input 7,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_100 : Impossible true (goalAt 231) 5 state231_100.toFinset :=
  node_ok cuts231 [⟨state231_99,exclude231_99⟩] 0x1190024200908042400900824020901821032180882022081882020848024201051021201050021200848041400840821020840c240620c0882022080c82020840421010840c828020800820020808c02030000c00020880820210880242080000242010880212010500212010900422010880244410404c040 (by decide +kernel)

def state231_101 : List Sig := [0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0,0x5555555555555555555555550000000055555555555555555555555500000000,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_101 : Impossible true (goalAt 231) 4 state231_101.toFinset :=
  node_ok cuts231 [] 0x820020800820209100210008400210210410242009100242020a00210220808a02008408212020808a020208082440084802120095002406084804140090802120218088202208188202104004100104102102 (by decide +kernel)

def state231_102 : List Sig := [0x5555555555555555555555550000000055555555555555555555555500000000,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 6,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 2,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_102 : Impossible true (goalAt 231) 5 state231_102.toFinset :=
  node_ok cuts231 [⟨state231_101,exclude231_101⟩] 0x21808820220818820211900242009080424009080422080000242009408210208418210220800820020808424010880424010880244408400210008408828010880820230100820210400210220808a02008408212020808a020208082120105102420084804140084802120105002120105004220084802406 (by decide +kernel)

def state231_103 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f0f0f0f0f0f0f0f0f00000000,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 6,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 0,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_103 : Impossible true (goalAt 231) 5 state231_103.toFinset :=
  node_ok cuts231 [] 0x20c0882022080c82021050021200848041400848042201050021200940824020900c240220800820020808424010880424010880244409000240009008828010880820230100820211404240220808a02009008242020808a0202080821201051021200908042400908024201190024204008c4220090802103 (by decide +kernel)

def state231_104 : List Sig := [0xfffffffffffffffff0f0f0f0f0f0f0f0,input 7,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_104 : Impossible true (goalAt 231) 4 state231_104.toFinset :=
  node_ok cuts231 [] 0x254008480212009100210208408210309018830220808820320808210108404210310414820020800820230080c00030000822020808242008480414008480244009080242020a0041011040441050840c8206 (by decide +kernel)

def state231_105 : List Sig := [0xffffffffeeeeeeeefafafafaeaeaeaeaffffffffeeeeeeeefafafafaeaeaeaea,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_105 : Impossible true (goalAt 231) 3 state231_105.toFinset :=
  node_ok cuts231 [] 0x30000c00020880410120800820020808c0200840421010840c410108480214008480412020c0882022080c820210400410010404c080 (by decide +kernel)

def state231_106 : List Sig := [0xffffffffccccccccf0f0f0f0c0c0c0c0ffffffffccccccccf0f0f0f0c0c0c0c0,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 0,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_106 : Impossible true (goalAt 231) 4 state231_106.toFinset :=
  node_ok cuts231 [⟨state231_105,exclude231_105⟩] 0x830220808820320808410010400410109018214008480212010480212009082000008480c000300008220104048200208008202300802101084042103104048602208088206208082402104042406104042440 (by decide +kernel)

def state231_107 : List Sig := [0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 0,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_107 : Impossible true (goalAt 231) 5 state231_107.toFinset :=
  node_ok cuts231 [⟨state231_97,exclude231_97⟩,⟨state231_104,exclude231_104⟩,⟨state231_106,exclude231_106⟩,⟨state231_81,exclude231_81⟩,⟨state231_101,exclude231_101⟩,⟨state231_9,exclude231_9⟩] 0x20c0c212020c0882024004c820220c0e00052080c820208480820220e04414009500244008480212020e0421200848024401050024400840e00040840824060848021020840c21200840c24064004c24064004c21200848024201050024204004c414010500242008480212020808244020800c04020a00820020808828020808c0400910024400840c82800840441050910021010840c24400840c410520a00410509080828009082000309100244009080244009082000220a00828028080210328008820230210820228080c0842088082020840c82022181824202180882028000482022181a00002081882020908082021041500231040421030908041011041424201041421034008c2103 (by decide +kernel)

def state231_108 : List Sig := [0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0,input 6,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 0,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_108 : Impossible true (goalAt 231) 5 state231_108.toFinset :=
  node_ok cuts231 [] 0x20c0882022080c82021050021200848041400840821020840c24060848041401050021200848024201050021202080082002080842400840421010840c828020a004240091002440090804240090808280280088202208808202301008202301008202104144220218088202208188202090082402090182103 (by decide +kernel)

def state231_109 : List Sig := [0xf0f0f0f0c0c0c0c0f0f0f0f0c0c0c0c0f0f0f0f0c0c0c0c0f0f0f0f0c0c0c0c,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 6,input 0,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_109 : Impossible true (goalAt 231) 5 state231_109.toFinset :=
  node_ok cuts231 [⟨state231_81,exclude231_81⟩] 0x20c0882022080c82020848042201050021200840821020840c240610500212008480414010880820230100820210404a00220808822020808860021800820211900422011900422009100240009000210321a008202208188202218082120105002120090802420800004220090802103090182402090084240 (by decide +kernel)

def state231_110 : List Sig := [0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 7,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 6,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_110 : Impossible true (goalAt 231) 5 state231_110.toFinset :=
  node_ok cuts231 [⟨state231_97,exclude231_97⟩] 0x1050021200848041400848042201050021200840821020840c240620c1882062081c82060848024201051021201088042401088024440840421010840c828020810820420818424009080464009080424010404422020818c04420818422009082000009080210320818c0440840c24020900824060840c8202 (by decide +kernel)

def state231_111 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 6,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 0,input 2,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_111 : Impossible true (goalAt 231) 6 state231_111.toFinset :=
  node_ok cuts231 [⟨state231_94,exclude231_94⟩,⟨state231_95,exclude231_95⟩,⟨state231_98,exclude231_98⟩,⟨state231_100,exclude231_100⟩,⟨state231_72,exclude231_72⟩,⟨state231_83,exclude231_83⟩,⟨state231_102,exclude231_102⟩,⟨state231_10,exclude231_10⟩,⟨state231_103,exclude231_103⟩,⟨state231_107,exclude231_107⟩,⟨state231_108,exclude231_108⟩,⟨state231_109,exclude231_109⟩,⟨state231_110,exclude231_110⟩] 0x86060908086022080900232080886068003082062080824202080846448002c46401090024200908046440908024201090100231090100230908024201088100231088100238002a00091088024200908024068002024020840c24200900824060908024060840d00230840c83030848083022080900132080883038001c820320808212020809002308480212009080454409081001311510414409080212008480838110500414010900212008480838108480212010900414010501001308480212010880414010881001310500414010880212008480210380018210209018212008408210308480210309019001309018820210900820030100828020800820220a00820230100424010900422020a00422080014424010900422010900422080010828009110210320a00210140088424008404210310900210340088828020a00c0401088042202080a000320808c04080008c0402080842202080900234008c41012808021032800882028000482022808200002088082020840c8202 (by decide +kernel)

def state231_112 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f00000000,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 7,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 0,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_112 : Impossible true (goalAt 231) 5 state231_112.toFinset :=
  node_ok cuts231 [⟨state231_1,exclude231_1⟩] 0x1040482203020041011040424021808041011040041001040442021050021200848041400848082208000021200940824020900c24021080042001080841012088082802088042400900024000900842402180824201040460201040421201050021200908082800908024201090024204008c8220090802103 (by decide +kernel)

def state231_113 : List Sig := [0xfffffffffffffffffffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0,input 6,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_113 : Impossible true (goalAt 231) 4 state231_113.toFinset :=
  node_ok cuts231 [] 0x41400848021201050021020840821030901841041041041051081821200908041400848021010840421031090042041081042061041424201090024200860424020900824060840cc0040840cc0400840c4101 (by decide +kernel)

def state231_114 : List Sig := [0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 0,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_114 : Impossible true (goalAt 231) 5 state231_114.toFinset :=
  node_ok cuts231 [⟨state231_90,exclude231_90⟩,⟨state231_113,exclude231_113⟩] 0x3011041011040421031808060023011060201088021031040441014002441011040424201141445018000445051041424201040441011040421201040042021050041001040441401040442020848042020960441401050042400848021200960421200848042401050041400840c41400840824060848021020840c21200840c24061050024064002421200848024201151024204004c45441051024200848021201080824801080041011090042001080842401080841010920041010840c424008404c0440920021010840c24800840cc044109004240090804240090820000119104640090804644090810009109004240090190023090082103090802402090182420090182103400242103 (by decide +kernel)

def state231_115 : List Sig := [0xf0f0f0f0c0c0c0c0f0f0f0f0c0c0c0c0f0f0f0f0c0c0c0c0f0f0f0f0c0c0c0c,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 7,input 0,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_115 : Impossible true (goalAt 231) 5 state231_115.toFinset :=
  node_ok cuts231 [⟨state231_90,exclude231_90⟩,⟨state231_2,exclude231_2⟩] 0x1040482203020041011040460021088041011040041001040442020848082208000421200840821020840c240610500212008480414020808460011800420210404822021a008220119002400090002103119004202104044202104042120105002120090802420800008220090802103090182402090084240 (by decide +kernel)

def state231_116 : List Sig := [0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0,input 6,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 7,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_116 : Impossible true (goalAt 231) 5 state231_116.toFinset :=
  node_ok cuts231 [⟨state231_113,exclude231_113⟩,⟨state231_4,exclude231_4⟩] 0x1050021200848041400848082208000421200840821020840c24061041041041041442060848024201050021202088082802088042400840421010840c424010810420410818410509080424009080828020808410520880c0841041441050840cc0840840c4101090808220800002420090082402090182103 (by decide +kernel)

def state231_117 : List Sig := [0xffffffffffffffff0000000000000000ffffffff00000000,input 6,input 7,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_117 : Impossible true (goalAt 231) 5 state231_117.toFinset :=
  node_ok cuts231 [⟨state231_6,exclude231_6⟩] 0x464009080242010900242020880c04409080450110404410510404212009080414408480414008480212010500212020882000008480410010400410110808822030100822010900420010800420210404c00030000c0401040424020900824060840c21020840821030901821010840421031090082022080882200840c4220 (by decide +kernel)

def state231_118 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_118 : Impossible true (goalAt 231) 5 state231_118.toFinset :=
  node_ok cuts231 [⟨state231_113,exclude231_113⟩] 0x46400908024201090024020900824060840c242030200c08409080242020882000009080212009080414408480414008480212010500210208408210309018212010500414008480212020880414008480210108404210310900608010900424020a0082201090082200860482022080882200840cc0400840cc0400840c4101 (by decide +kernel)

def state231_119 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 7,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 0,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_119 : Impossible true (goalAt 231) 6 state231_119.toFinset :=
  node_ok cuts231 [⟨state231_92,exclude231_92⟩,⟨state231_7,exclude231_7⟩,⟨state231_112,exclude231_112⟩,⟨state231_114,exclude231_114⟩,⟨state231_115,exclude231_115⟩,⟨state231_116,exclude231_116⟩,⟨state231_94,exclude231_94⟩,⟨state231_117,exclude231_117⟩,⟨state231_118,exclude231_118⟩] 0x1000710404410120880c08020882000830200c0802088041011040600071040441010840c60201800a00061808042200840c41011040445050908045011040500091040445058001441051040424201040446448001046401090024200908046440908024201090100091090100070908024202088100072088100094001e00032088024200908024068000824020840c24200900824060908024060840d00090840c41010848041001080841401040041011050041011080821201080900090848021200908045440908100131151041440908021200848083811050041401090021200848083810848021201090041401050100070848021202088100072088100134001e000120880212008480210310500210209018212008408210308480210309018414009018420220a00420010404424010800420210900420210404828010404822010900822080000828020a00822020a0082204001c424010900210310900210140088828008404210320a0021034001c42401090100074008c8202 (by decide +kernel)

def state231_120 : List Sig := [0x5555555555555555050505050404040455555555555555550505050504040404,input 6,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_120 : Impossible true (goalAt 231) 4 state231_120.toFinset :=
  node_ok cuts231 [] 0xa00220808822020808210018008410010880410020c00830020808424010c00410010808410010400c100301004100208088203208088302105002103084082102105002120084804140108084100108084100 (by decide +kernel)

def state231_121 : List Sig := [0xffffffffffffffff0f0f0f0f0c0c0c0cffffffffffffffff0f0f0f0f0c0c0c0c,input 6,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 5,input 0,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_121 : Impossible true (goalAt 231) 5 state231_121.toFinset :=
  node_ok cuts231 [⟨state231_120,exclude231_120⟩] 0x20c0882022080c82020840821020840c240610500212008480414010c0842021080c42028000021200848024202800882022088082020900060021080842201080824060840c24020900886002180082021090042021090042021040c242010900242021a00420220808c040108084101208088206208088602 (by decide +kernel)

def state231_122 : List Sig := [0xffffffffffffffffffffffffffffffff0f0f0f0f0c0c0c0c0f0f0f0f0c0c0c0c,input 7,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 5,input 0,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_122 : Impossible true (goalAt 231) 5 state231_122.toFinset :=
  node_ok cuts231 [] 0x1040482023020041011040442021080841011040041001040442020840821020840c240610500212008480414020c0882022080c820210500212008480242018008410110880410109000a0022080882202080824060840c240209008460011800420210404820220a008202119002420109002420119008206 (by decide +kernel)

def state231_123 : List Sig := [0xf0f0f0f0c0c0c0c0f0f0f0f0c0c0c0c0f0f0f0f0c0c0c0c0f0f0f0f0c0c0c0c,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 5,input 0,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_123 : Impossible true (goalAt 231) 6 state231_123.toFinset :=
  node_ok cuts231 [⟨state231_121,exclude231_121⟩,⟨state231_82,exclude231_82⟩,⟨state231_122,exclude231_122⟩,⟨state231_91,exclude231_91⟩,⟨state231_109,exclude231_109⟩,⟨state231_115,exclude231_115⟩,⟨state231_11,exclude231_11⟩] 0x30100410130000820230200c00030100c08030100820210404410120c0c212020c0882024004c820220c0e00062080c82020848082021040421201040042021050041001040441401040442020848042020840c41400840824060848021020840c21200840c240610500240621e04414010500464008480212021e0421200848046401050041402808021032800882024008c82022808200052088082020840c82021808021031800841014008c41011808200041088041010840c410140099002609000820211900860030100868021800820221a00820230100464011900420221a0046001040446401180042021190042021040486801040482020908082022181a00032081882028000882022181824202180842020908042021040600011040442028000042021040424201040421200908021201050100131050021204004c2120105002420090802103400902103090182420090182103090802402090190024090090024400904240 (by decide +kernel)

def state231_124 : List Sig := [0xffffffffccccccccffffffffccccccccffffffffccccccccf0f0f0f0c0c0c0c0,input 7,input 6,input 5,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_124 : Impossible true (goalAt 231) 4 state231_124.toFinset :=
  node_ok cuts231 [⟨state231_96,exclude231_96⟩] 0x8400210008404240610400410010404420620c1882062081c820608480242020a04212008404410180000210108404820608604210109000240009018210130000c000301004101108004200108184101208008200208182420 (by decide +kernel)

def state231_125 : List Sig := [0xfffffffffffffffffffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0,input 7,input 6,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 5,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_125 : Impossible true (goalAt 231) 5 state231_125.toFinset :=
  node_ok cuts231 [⟨state231_124,exclude231_124⟩,⟨state231_113,exclude231_113⟩,⟨state231_97,exclude231_97⟩] 0x21020840821030901841400848021201050041041041041051081883062081882072081821200908041400848021010840c41058000821030840c820680004210309008240209018210310810420410818410520810820420818424009080424009082000030010c004301004105104048202 (by decide +kernel)

def state231_126 : List Sig := [0xfffffffffffffffff0f0f0f0f0f0f0f0,input 7,input 6,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 5,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_126 : Impossible true (goalAt 231) 5 state231_126.toFinset :=
  node_ok cuts231 [⟨state231_104,exclude231_104⟩] 0x840821020840c240610500212008480414010410410410414420620c0882022080c82020840421031041600000840ca00220808822020808420410810420610414820020800820210900c00030000c0802080824200848041400848024020900824060840c424009080242020a004101104044105090808206 (by decide +kernel)

def state231_127 : List Sig := [0xffffffffeeeeeeeefafafafaeaeaeaeaffffffffeeeeeeeefafafafaeaeaeaea,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 6,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_127 : Impossible true (goalAt 231) 4 state231_127.toFinset :=
  node_ok cuts231 [⟨state231_105,exclude231_105⟩] 0xa0022080882202080821031040600001040421010840821020840c414030000c00030100410120800820020808c0401080441011040c410108480414008480414020c0882022080c8202104004100104042120 (by decide +kernel)

def state231_128 : List Sig := [0xffffffffccccccccf0f0f0f0c0c0c0c0ffffffffccccccccf0f0f0f0c0c0c0c0,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 6,input 5,input 0,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_128 : Impossible true (goalAt 231) 5 state231_128.toFinset :=
  node_ok cuts231 [⟨state231_106,exclude231_106⟩,⟨state231_127,exclude231_127⟩] 0x20c0882022080c82020840821020840c24061040041001040442061050021200848041400848024208000421202800882022088082020840c41018000041010840424020900824060840cc00030000c040104048200208008202301004206104044103104048602208088206208084202104044206104044240 (by decide +kernel)

def state231_129 : List Sig := [0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0,input 6,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 5,input 0,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_129 : Impossible true (goalAt 231) 6 state231_129.toFinset :=
  node_ok cuts231 [⟨state231_125,exclude231_125⟩,⟨state231_126,exclude231_126⟩,⟨state231_128,exclude231_128⟩,⟨state231_82,exclude231_82⟩,⟨state231_107,exclude231_107⟩,⟨state231_108,exclude231_108⟩,⟨state231_116,exclude231_116⟩,⟨state231_13,exclude231_13⟩] 0x20c0c212020c0882024004c820220c0e00072080c82020848082020840c41400840824060848021020840c21200840c240610500240620e04414010500424008480212020e0421200848042401050041401041421201041042061050041041041441401041442060848042064004c21200848024201050024204004c41401050024200848021202808021032800882024008c82022808200062088082020840c82024009500270840500230840c21031041500231041500238001600041041421030840c24200840c24024008c24060900824200901824064008c21030840c820210900820030100828020800820220a00820230100424010900420620a00420410414424010810420610900420610414828010414242020a0024208000c424010900242010900242080008828020a00c04010414c00420808c08420808c04030210c0402080841052080900244009041012181824202180882028000482022181a0000208188202090808202 (by decide +kernel)

def state231_130 : List Sig := [0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 7,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 5,input 0,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_130 : Impossible true (goalAt 231) 6 state231_130.toFinset :=
  node_ok cuts231 [⟨state231_91,exclude231_91⟩,⟨state231_114,exclude231_114⟩,⟨state231_110,exclude231_110⟩,⟨state231_125,exclude231_125⟩] 0x30110410110404820630200c00430110c0803011082061040441014002441011040424201141445018000c45051041424201040441011040421201040042021050041001040441401040442020848042020840c41400840824060848021020840c21200840c240610500240620e04414010500424008480212020e04212008480424010500414020c1c212020c1882064001c820620c1d00072081c82060848082064002421200848024201151024204004c45441051024200848021201808021031800841014008c41011808200021088041010840c41014009500280840500070840c21032081900072081900234001e00012081821030840c24200840c24024008c24060900824200901824064002421030840c420220a00420010404424010800420210900420210404828010404820610900820430110828020810820620a008206301104240109002420109002420800004644119002420119102420400244240109010024400908202 (by decide +kernel)

def state231_131 : List Sig := [0xffffffffccccccccffffffffccccccccffffffffcccccccc0000000000000000,input 6,input 7,input 5,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_131 : Impossible true (goalAt 231) 5 state231_131.toFinset :=
  node_ok cuts231 [⟨state231_14,exclude231_14⟩] 0x9000240009010210109080c04030110242011404410110414410109080424010910242008480242010510212008400210008404240408480c04080000212010400410010404212008480424020a04212008404c04008604210108404410109110210108404424040088210130000c00030100410120800820020a004240108004200109004101 (by decide +kernel)

def state231_132 : List Sig := [0x33333333000000003333333300000000333333330000000000000000,input 6,input 7,input 5,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_132 : Impossible true (goalAt 231) 5 state231_132.toFinset :=
  node_ok cuts231 [] 0x240009000240408404860020800820420800460010800420410800212009080414408480210008400210109010830020800820120800430010800420110800a00020800822020800600010800422010800420020800c040108004240090804640090804140084804140084806040109008200301008200104044200109004200 (by decide +kernel)

def state231_133 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,input 7,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 5,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_133 : Impossible true (goalAt 231) 6 state231_133.toFinset :=
  node_ok cuts231 [⟨state231_131,exclude231_131⟩,⟨state231_132,exclude231_132⟩,⟨state231_94,exclude231_94⟩,⟨state231_98,exclude231_98⟩,⟨state231_118,exclude231_118⟩,⟨state231_15,exclude231_15⟩,⟨state231_125,exclude231_125⟩] 0x9008240209018210311900242009080424009080c04030110242009080c0803021024200908100248001824200848024201051021200840821020840c240610500212008480414008480c0408001421200848041401050021200848041401050021200840421033010200040840c21033020200030840c21034008e00020840c424030100828010900828010900424020a02000110900424080000820230100c080106044101 (by decide +kernel)

def state231_134 : List Sig := [0xffffffff00000000ffffffff00000000ffffffffffffffffffffffff00000000,input 6,input 7,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_134 : Impossible true (goalAt 231) 5 state231_134.toFinset :=
  node_ok cuts231 [] 0x11900242009080424021808820220818820209080422030210242009008240209018210308480242010510212010500212008480414020c0882022080c82020848042201050021200840821020840c240620800820020808424010880424010880244430000c0003020082020840421010840c8280280088202208808202104044101108802103 (by decide +kernel)

def state231_135 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0,input 6,input 7,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 5,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_135 : Impossible true (goalAt 231) 5 state231_135.toFinset :=
  node_ok cuts231 [⟨state231_99,exclude231_99⟩] 0x21020840821030901841400848021201050083022080882032080841041041041051081821200908041400848021012800882022088082020840c410580000210320800820020808424010810420410818410530000c000311008202090082402090182103109002420090808280218088202208188202104044101104142420 (by decide +kernel)

def state231_136 : List Sig := [0xffffffffffffffff0000000000000000,input 6,input 7,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 5,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_136 : Impossible true (goalAt 231) 6 state231_136.toFinset :=
  node_ok cuts231 [⟨state231_134,exclude231_134⟩,⟨state231_135,exclude231_135⟩,⟨state231_100,exclude231_100⟩] 0x9008240209018210311900242009080424021808820220818820209080c0803021024200848024201051021200840821020840c240610500212008480414020c0882022080c820208480414010500212008404a0022080882202080821033020200020840c820020800820210900828010900424020a00c0003020082024009024208000424201050021201050021204008c2103800002103109008280109008280301004101 (by decide +kernel)

def state231_137 : List Sig := [0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 5,input 0,input 2,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_137 : Impossible true (goalAt 231) 7 state231_137.toFinset :=
  node_ok cuts231 [⟨state231_75,exclude231_75⟩,⟨state231_80,exclude231_80⟩,⟨state231_84,exclude231_84⟩,⟨state231_87,exclude231_87⟩,⟨state231_89,exclude231_89⟩,⟨state231_93,exclude231_93⟩,⟨state231_111,exclude231_111⟩,⟨state231_119,exclude231_119⟩,⟨state231_16,exclude231_16⟩,⟨state231_123,exclude231_123⟩,⟨state231_129,exclude231_129⟩,⟨state231_130,exclude231_130⟩,⟨state231_133,exclude231_133⟩,⟨state231_136,exclude231_136⟩] 0x4001cc04010404c00080034820230200c00080030c04030200c0404001c82021040441014009086060908086024009082024009082024009086068002c82064009082020908082024009045050908045014009041014009041014009045058002841054009041010908041014009024064008c24024009021030908024024009024060908024064009021034009021034009046448002446404009042400908024204009046440908024204009042404009042404002c83030848083024002c82024002c82024002c83038002082034002c82020848082024002c41010848041004002c42021050041004002c41011050041014002c420208480420240091002408480212040090242011510242040091000b1151041444009024200848021204002c21031050021024002c24060848021024002c21030848021034002c24061050024064002c83811050041404002c42400848021204002c83810848021204002c42401050041404001ca0200840ca0024008c82024008c82024008ca0208001c82204001c82020840c82024008c60200840c60024008c41014008c41014008c60208001842204008c41010840c41014008900254008821014001c820210900820080014c04020a00820080010820220a0082024001cc0401090042408000c420220a00420080008410110900420080004420210900420280000410120a004101 (by decide +kernel)

def state231_138 : List Sig := [0xffffffffffffffffffffffffcccccccc,input 6,input 1,input 5,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_138 : Impossible true (goalAt 231) 5 state231_138.toFinset :=
  node_ok cuts231 [] 0x29000a00028010a00031000c00030010c00008480242010510212028400a00028004a00020c00820020804820030400c00030004c00028000c00018080a00020800860020810820020800a0000840c820020800c00010808820020808820621808820220808820320c08820208404a00028808a00028080820020808820010404c00010808c000 (by decide +kernel)

def state231_139 : List Sig := [0x5555555555555555555555554444444455555555555555555555555544444444,input 6,input 1,input 5,input 2,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_139 : Impossible true (goalAt 231) 5 state231_139.toFinset :=
  node_ok cuts231 [] 0x21808820220818820209400210008410210011400410010410410008400a10028080210008400410018080210020c00830020808a02009880242009088242008c0021000840c210010c00410010808410010400c10030100410020808820320808830208480414409080212009010210008c08210008480212208c802120108084100108084100 (by decide +kernel)

def state231_140 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0c0c0c0c0f0f0f0f0f0f0f0f0f0f0f0f0c0c0c0c,input 6,input 1,input 5,input 0,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_140 : Impossible true (goalAt 231) 5 state231_140.toFinset :=
  node_ok cuts231 [] 0x20c0882022080c820209400240009004240008480232008488212011400450011404420209000a40028080240009000640018080240021800860020808a0200980024000840c240011800460010808450131000c400301004501208088206208088602084804144084802420084042400098082400090802422098802420104044101108084501 (by decide +kernel)

def state231_141 : List Sig := [0xffffffffffffffffffffffffccccccccffffffffffffffffffffffffcccccccc,input 6,input 1,input 5,input 0,input 2,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_141 : Impossible true (goalAt 231) 6 state231_141.toFinset :=
  node_ok cuts231 [⟨state231_138,exclude231_138⟩,⟨state231_139,exclude231_139⟩,⟨state231_140,exclude231_140⟩] 0x860220808820620808260209808260608c0c46021080842061080a000209080242040004830220808820320808212009080414408480230208c08230309818212008c8021220848043021080842031080a000108480212040000a20220808a02020808620210808602010808210120808a02020808a02009880242009088242008c0c60400840c210310808602010808410320a00420220808c0401080841012080a0000208090005 (by decide +kernel)

def state231_142 : List Sig := [0xf0f0f0f0c0c0c0c00000000000000000f0f0f0f0c0c0c0c,input 6,input 1,input 5,input 0,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_142 : Impossible true (goalAt 231) 5 state231_142.toFinset :=
  node_ok cuts231 [] 0x830220808820320808250009000240109000212008c80212208480410010400410110818240029000a02009000240018000244009000860021800820228080260009000210309000420010800420610404c00030000c040104048202208188202218082120105002120090802101090002602090002420090882620090804202 (by decide +kernel)

def state231_143 : List Sig := [0xffffffffcccccccc0000000000000000ffffffffcccccccc,input 6,input 1,input 5,input 0,input 2,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_143 : Impossible true (goalAt 231) 6 state231_143.toFinset :=
  node_ok cuts231 [⟨state231_142,exclude231_142⟩] 0x860220808820620808260209808260608c0c450110404410510404830220808820320808212009080414408480230208c08230309818212008c80212208480410010400410108480a20220808a0202080860001800060401040482022808082022808026200908024220908023031810021030840c420010800424010404c00030000c040104048202301008202301002420800002420400042120105002120105002101084042303181008280109010023109004202 (by decide +kernel)

def state231_144 : List Sig := [0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,input 6,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 5,input 0,input 2,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_144 : Impossible true (goalAt 231) 6 state231_144.toFinset :=
  node_ok cuts231 [⟨state231_77,exclude231_77⟩] 0x21808820220818820209808260209818230311900242009080424011808420210818420209080262009088242020c0882022080c820208480242010510212008c08230208c0c260610500212008480414010c0842021080c42020848023200848821202880882022808082020840460021080842221080a000008c0c21030840c82023010082021090042021090042021040c82801090042404008c420220808c04010808410120808a02020808a020 (by decide +kernel)

def state231_145 : List Sig := [0xf3f3f3f3f3f3f3f3f0f0f0f0f0f0f0f0f3f3f3f3f3f3f3f3f0f0f0f0f0f0f0f0,input 6,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 5,input 0,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_145 : Impossible true (goalAt 231) 5 state231_145.toFinset :=
  node_ok cuts231 [] 0x830220808820320808210208408210309018414008480212010500430210808420310808212009080414008480a002208088220208082101188084202108804202208008200208084640108004200108084105108088202301004202218088202208188202090082402090182103119002420090804240104044101104144202 (by decide +kernel)

def state231_146 : List Sig := [0x3333333333333333000000000000000033333333333333330000000000000000,input 6,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 5,input 0,input 2,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_146 : Impossible true (goalAt 231) 6 state231_146.toFinset :=
  node_ok cuts231 [⟨state231_85,exclude231_85⟩,⟨state231_145,exclude231_145⟩] 0x21808820220818820209008240209018210321a00242009080828011808420210818420220c0882022080c82020848024201051021200840821020840c240610500212008480414010c0842021080c420228008820220880820208404620210808422010808820020800820230100420010800420220a00420220808c04010808c04020808c0402080900240908200010908041400848041400848100230840e00000840d002320a004240109004101 (by decide +kernel)

def state231_147 : List Sig := [0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 1,input 0,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_147 : Impossible true (goalAt 231) 5 state231_147.toFinset :=
  node_ok cuts231 [] 0x830220808820320808212008c80212208480254008480212009100230208c08230309818212009080414008480820228080820228080264008c0c41050840c210309880242009088242020808a44020808244008404210108c0c410509080244009081002b288088202280808202218088202208188202104044101104142303 (by decide +kernel)

def state231_148 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 6,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 1,input 0,input 2,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_148 : Impossible true (goalAt 231) 6 state231_148.toFinset :=
  node_ok cuts231 [⟨state231_147,exclude231_147⟩] 0x21808820220818820219100242009080604009080602080000242009808260209818230320c0882022080c820208480242010510212008480232008488212010500212008480414008480602010500212008c08230208c0c260620808a02020808a0200988024200908824201090042201088042221808023034008821030840c820230100820218100602018100602009110210108404230340088602020808c040208084101288088202280808202 (by decide +kernel)

def state231_149 : List Sig := [0x5555555555555555050505050404040455555555555555550505050504040404,input 6,input 1,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_149 : Impossible true (goalAt 231) 4 state231_149.toFinset :=
  node_ok cuts231 [] 0x8400a10028080210008400410018080210020c00830020808a02008c0021000840c210010c00410010808410010400c10030100410020808820320808830210500210008c08210008480212208c802120108084100108084100 (by decide +kernel)

def state231_150 : List Sig := [0xffffffffffffffff0f0f0f0f0c0c0c0cffffffffffffffff0f0f0f0f0c0c0c0c,input 6,input 1,input 5,input 0,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_150 : Impossible true (goalAt 231) 5 state231_150.toFinset :=
  node_ok cuts231 [⟨state231_149,exclude231_149⟩] 0x830220808820320808250009000240109000212008c8021220848043021080842031080a000008480212009080240029000a0200900024001080860200900024000840426020900086002180082022808026000900021030900042021808042021040c242209080262009080420220808c040108084101208088206208088602 (by decide +kernel)

def state231_151 : List Sig := [0xf0f0f0f0c0c0c0c0f0f0f0f0c0c0c0c0f0f0f0f0c0c0c0c0f0f0f0f0c0c0c0c,input 1,input 5,input 0,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_151 : Impossible true (goalAt 231) 6 state231_151.toFinset :=
  node_ok cuts231 [⟨state231_150,exclude231_150⟩,⟨state231_142,exclude231_142⟩] 0x30100410130000820230200c00030100c08030100820210404410120c0c212020c08820240050820220c0d00142080c820208480820210404212010400420210500410010404414010404420208480420209404414009400240008480240009404212009004240010500240021e04212008480464008c88232021e04232208488464008480212028080240009000820229200a40028080a48028080820209000240018080240009000410119100640018080644018080410109000240020808464021800a02021a00860020808868020808a02011900a02010808868011800410111900460010808464010808410121a00410108c0c464009800240040098240008c0d00240840c24001190024002080824202080886064005082062080900142080886060908086021080824201080841018000441011080a0000108084101090804101084802420084804140400b0414008481002c08480414009080242008c0d000108404240009080240008c0c2420098082400400042400400902420090804640098882422400902622098804640090802420 (by decide +kernel)

def state231_152 : List Sig := [0xf0f0f0f0c0c0c0c0f0f0f0f0c0c0c0c0f0f0f0f0c0c0c0c0f0f0f0f0c0c0c0c,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 1,input 5,input 0,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_152 : Impossible true (goalAt 231) 6 state231_152.toFinset :=
  node_ok cuts231 [] 0x30000c00030100410120c0882022080c820210400410010404420208c08230208c0c2606084802320084882120105002120084804140288088202280808202188084101180804101090008202280808202280804202104044202104042303400982103119008202301008202301004202104044202104048202208188202218084202104044202104042120105002120090802303098182602098082420090882620090810001 (by decide +kernel)

def state231_153 : List Sig := [0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0,input 6,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 1,input 5,input 0,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_153 : Impossible true (goalAt 231) 6 state231_153.toFinset :=
  node_ok cuts231 [⟨state231_142,exclude231_142⟩,⟨state231_147,exclude231_147⟩] 0x20c0882022080c820208c08230208c0c260608480232008488212010500212008480414010410410410414420608480242010500212028808820228080820208404230310416000108c0c260209808260608c0c82022808082022808023034009c2103109004206104144206104142620090802422090808202301008202301004206104144206104142420800002420400acc00420808c040208084101218088202208188202 (by decide +kernel)

def state231_154 : List Sig := [0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 1,input 5,input 0,input 2,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_154 : Impossible true (goalAt 231) 7 state231_154.toFinset :=
  node_ok cuts231 [⟨state231_141,exclude231_141⟩,⟨state231_143,exclude231_143⟩,⟨state231_144,exclude231_144⟩,⟨state231_146,exclude231_146⟩,⟨state231_148,exclude231_148⟩,⟨state231_151,exclude231_151⟩,⟨state231_152,exclude231_152⟩,⟨state231_153,exclude231_153⟩] 0xc04010404c00020808c08030000c04030200c0402080841011040486060908086022080900242080886064001082062080824202080845050908045011040500241040445058001c41051040424201040426064008c260208c0c242009808260609080260608c0d002408c0d00248001a000540004242009081002409080242040005002440004830308480830220809000b20808830340010820320808212020808410108480410010808414010400410110500410110808212010809002408480212009080454409081000b11510414409080212008480230310500230209818212008c08230308480230309818414009819000b0848021204002c232208c81000b08c8821224002c212008481000b10500414040000212008481000b08480212040000414010500a02008c0ca20220809000420808a02040010a02020808230320808602008c0c620210405002310404602080010602010404230310405002540088210120809000720808a02040088a02020809000420808a0204001ca0201080a00031080841014008841011080a000210808410140088410109889002409880242040090242009889002409088242040090242008c0d002308c0d00224008900224008900220840d002a4008c424020809000520808c04040010c04020809000420808c04040014c0401080900291080841018000441011080a0000108084101400a44101 (by decide +kernel)

def state231_155 : List Sig := [0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0,input 6,0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,input 5,input 0,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_155 : Impossible true (goalAt 231) 6 state231_155.toFinset :=
  node_ok cuts231 [] 0x20c0c212020c08820240060820220c0d00182080c8202084808202084044140084002404084802100084042120084042404105002404104142120104104206105004104104144140104144206084804206400b82120084802420105002420400b8414010500242008480212028080210128000820228200a00028080a0802808082020840421014008c21010840441051810060044008c604009100410508404210109080210109001002309010240009080240409011002308404210120808424020800a02020a00820020808828020808a02010900a0204009c424010900212020e0421204009c838120a0421201090021204009d00240840c420620a00420410414424010810420610900420610414828010415002720a00828009080424009081002710900424009080828009080c04010414c00420808c08420808c04030210c040208084105208090025400944101218182420218088202400608202218190018208188202090808202 (by decide +kernel)

def state231_156 : List Sig := [0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,input 5,input 0,input 2,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_156 : Impossible true (goalAt 231) 7 state231_156.toFinset :=
  node_ok cuts231 [⟨state231_155,exclude231_155⟩] 0x400b4c04010404c00040010820230200c00040010c04030200c040400b482021040441014009486060908086024009482024009482024009486064001082064009482020908082024009445050908045014009441014009441014009445058000041054009441010908041014009424044008c2400400942101090802400400942404090802404400942101400942101400208303084808302400208202400208202400208303400108203400208202084808202400204101084804100400204202105004100400204101105004101400204202084804202400950025084802120400942420115102420400950008115104144400942420084802120400202101105002100400202404084802100400202101084802101400202404105002404400b4a02008404a00040010820228200a00040010a02028200a020400b482020840421014008c60200840460004008c41011810060004008c60201810060204008c4101084042101400b4820210900820040088a02020a00820040088820220a008202400b4a02010900a02040088420220a00420040088410110900420040088420210900420240088410120a00410140095002510900424040094242011910242040095002211910424440094242010900242040021000810900424040020212020e04212040021002220e048281400202120109002120400890022400902103 (by decide +kernel)

def state231_157 : List Sig := [0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0,input 6,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,input 1,input 0,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_157 : Impossible true (goalAt 231) 6 state231_157.toFinset :=
  node_ok cuts231 [] 0x28000a00028080210108404230308c0c210108404420618100210109000240009010210120c0882022080c820208400210008404240408480232208c88212008480232208c88212010c1842061081c420608480242010500212020808a02020808a02008c0c210108c0c210120a00420610900410709888242009888242020808a02020808a020098882420098882420108188202301008202104144202218088202208188202 (by decide +kernel)

def state231_158 : List Sig := [0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000,input 5,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,input 1,input 6,input 0,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_158 : Impossible true (goalAt 231) 6 state231_158.toFinset :=
  node_ok cuts231 [] 0x20c0882022080c820210c0842021080c420208480232208c88212008480232208c88212009400240009004240010808820230100420210404820228080820228080420210900410320a00260209000260209000820228080820228080240029000a02009000240010808622209000240009808260209000242020808a020208082120105002120090802420108086222108082420098882622090802420098882622090802101 (by decide +kernel)

def state231_159 : List Sig := [0xf0f0f0f0fffffffff0f0f0f0fcfcfcfcf0f0f0f0fffffffff0f0f0f0fcfcfcfc,input 5,input 1,input 6,input 0,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_159 : Impossible true (goalAt 231) 5 state231_159.toFinset :=
  node_ok cuts231 [] 0x20c0882022080c820210c0842021080c420208480232008488212008400210008404260208480242010500212010808820230100420220808820420808a02010808420410808410308c04210109008210109880242009088242028000a00028080210118000600018080210120808a020208082420104044101108082420090002400098082101 (by decide +kernel)

def state231_160 : List Sig := [0xffffffff00000000cccccccc00000000ffffffff00000000cccccccc,input 5,input 1,input 6,input 0,input 2,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_160 : Impossible true (goalAt 231) 6 state231_160.toFinset :=
  node_ok cuts231 [⟨state231_159,exclude231_159⟩,⟨state231_77,exclude231_77⟩] 0x860220808820620808460210808420610808240009000240408404830220808820320808212009080414408480430210808420310808212008c80212208480210008400210109010420220808c0401080882022808082022808026200908024220908042021808042021040c230108406000108404a00028000a02008404600018000602008404820228080820228081000109082000009080414008480414008480410110404420218080424020a004240400942303 (by decide +kernel)

def state231_161 : List Sig := [0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,input 1,input 6,input 0,input 2,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_161 : Impossible true (goalAt 231) 7 state231_161.toFinset :=
  node_ok cuts231 [⟨state231_144,exclude231_144⟩,⟨state231_157,exclude231_157⟩,⟨state231_158,exclude231_158⟩,⟨state231_141,exclude231_141⟩,⟨state231_160,exclude231_160⟩] 0xa02008404a00020808a08028000a02028200a0202080821010840462220840421011080860401080862221810042221080821010840600040840421014008c230308c0e000308c0c23034008c210108404860609080860220809003220808860640010820620808242020808240480008240008404242009000240409080240408405003208404460609080460210809003210808460680004420610808242010809003209080242040004262209889003209888262240004242009080830308480830220809003120808830340010820320808212020808210110500210009010212008400210108480210109010414009011003208480212009080454409081003111510414409080212008480430308480430210808414010808430310500420310808212010809003108480212010900232208c89003108c88232210900212008481003108480212040000232208c89003108c88232240000212008480c04010808420220809000420808c04040010c04020808420210809003040088410120808424020808a02040088a02020809000420808a02010900a02008c0c424008c0c210140088210108c0e000008c0c21011090021010988842400988824201191024200988846440988824201090024201080900291080900221090042404008900221040d002f400a4828020809000520808a02040010a02020809000420808a02040014a020 (by decide +kernel)

def state231_162 : List Sig := [0xf3f3f3f3f3f3f3f3f0f0f0f0f0f0f0f0f3f3f3f3f3f3f3f3f0f0f0f0f0f0f0f0,input 1,input 6,input 0,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_162 : Impossible true (goalAt 231) 6 state231_162.toFinset :=
  node_ok cuts231 [⟨state231_145,exclude231_145⟩] 0x28080210128000820228200a00028080a08028080820208404210118888210108404420218100420218888604010888420208404210120c0c212020c08820240060820220c0d00182080c820208480820208404414008400240408480210008404212008404240410500240410c0c212010c08420210500420210c0c41401080c420208480420220e04212008480464008c88232020e042322084884640084802120400b82120084802420105002420400b8414010500242008480212030100420210808820230210820230100c08430100820210808420220808464020800a02020a00820020808828020808a02011900a02008c0c464008c0421014009c210108c0e00000840c210111900210110808828010800410511900420010808464010808410520a00410509888828009880242011900242009888464009088242020a0024202181824202180882024006082022181900182081882020908082020901100230900021010908024000901024200901021014008c2101104142420104044202400044101104150001104144202090804202 (by decide +kernel)

def state231_163 : List Sig := [0x5555555511111111555555550000000055555555111111115555555500000000,input 5,input 1,input 6,input 2,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_163 : Impossible true (goalAt 231) 5 state231_163.toFinset :=
  node_ok cuts231 [] 0x21808820220818820211400410010410410009400210008410210010400c10030100410020800820020808a02009880242009088242010800410010408410008c00210008408210008400a10028080210008400410018080210008480820228080820208480414409080212008480410018080410008480212208c802120090102100084802100 (by decide +kernel)

def state231_164 : List Sig := [0xf0f0f0f030303030f0f0f0f000000000f0f0f0f030303030f0f0f0f00000000,input 5,input 1,input 6,input 0,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_164 : Impossible true (goalAt 231) 5 state231_164.toFinset :=
  node_ok cuts231 [] 0x20c0882022080c820211400450011404420208480232008488212009400240009004240031000c40030100450120800820020808a02010800420010808450109800240009008240009000a400280802400090006400180802400090808202280808202084804144084802420104044101180804501090802422098802420084042400090802400 (by decide +kernel)

def state231_165 : List Sig := [0xffffffff33333333ffffffff00000000ffffffff33333333ffffffff00000000,input 5,input 1,input 6,input 0,input 2,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_165 : Impossible true (goalAt 231) 6 state231_165.toFinset :=
  node_ok cuts231 [⟨state231_85,exclude231_85⟩,⟨state231_163,exclude231_163⟩,⟨state231_164,exclude231_164⟩] 0x860220808820620808460210808420610808644009080242018102000209080242040004830220808820320808212009080414408480430210808420310808212008c80212208480414008480212010502000108480212040000420220808c04010808820020800820228080262009080242209080420010800420218080624018102000018100828040094424010900a02020808a020208086020108086020108082101280808202280808202104044101180804202 (by decide +kernel)

def state231_166 : List Sig := [0x1515151511111111050505050000000015151515111111110505050500000000,input 5,input 1,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_166 : Impossible true (goalAt 231) 4 state231_166.toFinset :=
  node_ok cuts231 [] 0x10400c10030100410020800820020808a02010800410010408410008c00210008408210008400a10028080210008400410018080210008480820228080820208480410018080410008480212208c802120105002100084802100 (by decide +kernel)

def state231_167 : List Sig := [0x3f3f3f3f333333330f0f0f0f000000003f3f3f3f333333330f0f0f0f00000000,input 5,input 1,input 6,input 0,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_167 : Impossible true (goalAt 231) 5 state231_167.toFinset :=
  node_ok cuts231 [⟨state231_166,exclude231_166⟩] 0x20c0882022080c820210c0842021080c420208480232008488212009400240009004240010808820230100420220800820020808a02010800420010808602009800240009008240009000a400280802400090004202180802400090808202280808202084820000084802420104044101180804202090802422098802420084042400090802400 (by decide +kernel)

def state231_168 : List Sig := [0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000,input 5,0x3333333333333333000000000000000033333333333333330000000000000000,input 1,input 6,input 0,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_168 : Impossible true (goalAt 231) 6 state231_168.toFinset :=
  node_ok cuts231 [⟨state231_167,exclude231_167⟩] 0x20c0882022080c820210c0842021080c420208480232008488212009400240009004240010808820230100420220800820020808a02010800420220a00260009000240209000c04020808c04020808414008480414008480410110900644009000644009000240029000a02009000240010808622209000242020808a0202080821201050021200908024201080862221080824200908826200908024204008e0000090802101 (by decide +kernel)

def state231_169 : List Sig := [0x3333333333333333000000000000000033333333333333330000000000000000,input 1,input 6,input 0,input 2,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_169 : Impossible true (goalAt 231) 7 state231_169.toFinset :=
  node_ok cuts231 [⟨state231_162,exclude231_162⟩,⟨state231_165,exclude231_165⟩,⟨state231_146,exclude231_146⟩,⟨state231_168,exclude231_168⟩] 0xa02008404a00020808a08028000a02028200a02020808210108404622208404210110808604010808622218100422210808210108404860609080860220809002f2080886064001082062080824202080824048000c240008404242009000240409080240408405002f08404460609080460210809002f108084606400a4420610808242010808830308480830220809003420808830340010820320808212020808210110500210009010212008400210108480210109010414009011002f08480212009080454409081003411510414409080212008480430308480430210808414010808430310500420310808212010808838108480212020a00232208c80838108c88212220a00212008480c04010808420220809000420808c04040010c040208084202108088202400d4820028080828020800820220a00820228081003528080230320a00230108405002208404230380008210308404828008404262220a00262009080868409080262221a10242209080828009081002240088420010809002910809002220a008280301010005301008202400108202301010004301008202400148202181010023181002101400a421011810200011810021014008c2101400bd0001400042420400bc2420400a5002f800002420400042420105010000105002120400d02120105010034105002120400002120400890033104050029400c84240 (by decide +kernel)

def state231_170 : List Sig := [0x5555555555555555555555555555555555555555555555550505050500000000,input 7,input 6,input 5,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_170 : Impossible true (goalAt 231) 4 state231_170.toFinset :=
  node_ok cuts231 [] 0x8c00210008408210010c00410010408410020c00830020c08a02008400410018080210008400a10028080210010400c10030100410008480212208c802120105002100084802100108084100180804100208088202280808302 (by decide +kernel)

def state231_171 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0f0f0f0f00000000,input 7,input 6,input 5,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_171 : Impossible true (goalAt 231) 5 state231_171.toFinset :=
  node_ok cuts231 [⟨state231_170,exclude231_170⟩,⟨state231_27,exclude231_27⟩] 0x9800240009008240018880602018088602028880a02028088a02009088242009880242008480232008488212009400240009004240008480602010500212008480a02080004212080000212008480242009000604018080240009000c04028080240009000210109080240018080a020301006020104048202 (by decide +kernel)

def state231_172 : List Sig := [0xffffffffffffffff0f0f0f0f00000000,input 7,input 6,input 5,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_172 : Impossible true (goalAt 231) 5 state231_172.toFinset :=
  node_ok cuts231 [⟨state231_30,exclude231_30⟩] 0x260009000240209000622018080602218080820020800820210900212008c80212208480250009000240109000212018080414008480830220808820320808240018100602009000240028000248009000c00030000c08020808242009088262009080212080000212009080210109000242009000410110404602009080a020 (by decide +kernel)

def state231_173 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,0xffffffffffffffff0f0f0f0f00000000ffffffffffffffff0f0f0f0f00000000,input 5,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_173 : Impossible true (goalAt 231) 5 state231_173.toFinset :=
  node_ok cuts231 [⟨state231_31,exclude231_31⟩] 0x260009000240209000242209080262009080424030100828010900622018080602218080212008c80212208480250009000240109000c18008480212009080212030102000008480212018080414008480240008404242009000240028100a48009000240018100602009000242030200c040090804101104046020090808202 (by decide +kernel)

def state231_174 : List Sig := [0xffffffffffffffff0000000000000000,input 7,0xffffffffffffffff0f0f0f0f00000000ffffffffffffffff0f0f0f0f00000000,input 5,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_174 : Impossible true (goalAt 231) 5 state231_174.toFinset :=
  node_ok cuts231 [] 0x9800240009008240009088242009880242020800820020808a02008480232008488212009400240009004240030600212008480242020c0882022080c820209000210109080240009000a40028080240030000c00028080820218080622018088602018080212010500212018100240018080240010404c040 (by decide +kernel)

def state231_175 : List Sig := [0xffffffffffffffffffffffffffffffff55555555555555550505050500000000,input 7,input 6,input 5,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_175 : Impossible true (goalAt 231) 4 state231_175.toFinset :=
  node_ok cuts231 [] 0x230008400210208400430010400410210400a22028080a02228080212208480232008480210010400602008400210030100a02008400210010500212008400410028080c040104004100108086020104008202 (by decide +kernel)

def state231_176 : List Sig := [0x5555555555555555050505050000000055555555555555550505050500000000,input 6,input 5,input 1,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_176 : Impossible true (goalAt 231) 5 state231_176.toFinset :=
  node_ok cuts231 [⟨state231_175,exclude231_175⟩,⟨state231_30,exclude231_30⟩] 0x20808424020800a02020a00820020808828020808a02010900a02008c08424008c002100400dc210008c09003708408210010900210010c08828010c00410010900410010c08424010408410020a00410028080210008400820228600a10028080a18028080820208400210018080210008400410018100410018080604018080410008400210030100410010400820230600c10030100c18030100820210400410028080212008480820280004820228082000028080820208480820210900212008480828008c88212210900232208c808280084802120181004140105002100084802100181002120084802100105002100180802120108084100105004100180804140180804100084804100 (by decide +kernel)

def state231_177 : List Sig := [0x5555555555555555050505050000000055555555555555550505050500000000,0xffffffffffffffff0f0f0f0f00000000ffffffffffffffff0f0f0f0f00000000,input 6,input 5,input 1,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_177 : Impossible true (goalAt 231) 5 state231_177.toFinset :=
  node_ok cuts231 [] 0x20800820020808a02009800240009008240018880602018088602020a00424010900828009000a40028080240009000604018080240008400210018100240018080820230100820210400a02020808a02020808212020808a020208082120084882320084804140090002120090002120105006020084802420 (by decide +kernel)

def state231_178 : List Sig := [0xffffffffffffffff0f0f0f0f00000000ffffffffffffffff0f0f0f0f00000000,input 6,input 5,input 0,input 1,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_178 : Impossible true (goalAt 231) 6 state231_178.toFinset :=
  node_ok cuts231 [⟨state231_171,exclude231_171⟩,⟨state231_172,exclude231_172⟩,⟨state231_173,exclude231_173⟩,⟨state231_174,exclude231_174⟩,⟨state231_176,exclude231_176⟩,⟨state231_177,exclude231_177⟩,⟨state231_32,exclude231_32⟩] 0x820210900820028080828020800820220a0082022808042402808026021090026000900100230900026024008c240209000424009000622220a00622018080424018080622210900602218080828018080262220a00242209080424009080262210900262009080828009080830308480830220809001320808830380018820320808212020808838108480212010900232208c80838108c88212210900212008480250110500250009000212009000250108480240109000414009001001308480212018080414018081001310500414018080212008481001380016000409080212008481001308480212009081001309080a02009000240020808a48029000a02029200a0202080824000900060200900024004008c60401810060201810060204008c240009000242009000240040004604008404242018100242040004240009000c0401808060202080a000320808c04080008c0402080860202080900364008c4101280802420090808202800048202280820000280808202090808202 (by decide +kernel)

def state231_179 : List Sig := [0xffffffffffffffff00000000000000000f0f0f0f00000000,input 6,input 7,input 5,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_179 : Impossible true (goalAt 231) 5 state231_179.toFinset :=
  node_ok cuts231 [⟨state231_28,exclude231_28⟩] 0x260009000240209000a22028080a02228080420010800420210404212008c80212208480250009000240109000212028082000008480410010400410110808240030100a02009000240018000244009000c00030000c04010404242009088262009080212010500212009080210109000242009000820220808a020090806020 (by decide +kernel)

def state231_180 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,0xffffffffffffffffffffffffffffffff0f0f0f0f000000000f0f0f0f00000000,input 5,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_180 : Impossible true (goalAt 231) 5 state231_180.toFinset :=
  node_ok cuts231 [] 0x260009000240209000242209080262009080828010900424020a00a22028080a02228080212008c80212208480250009000240109000414008480212009080212010500414008480212028080414008480240008404242009000240019100644009000240019100a02009000820220808a02009080c04009080c040090804101 (by decide +kernel)

def state231_181 : List Sig := [0xffffffffffffffffffffffffffffffff0f0f0f0f000000000f0f0f0f00000000,input 7,input 5,input 0,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_181 : Impossible true (goalAt 231) 6 state231_181.toFinset :=
  node_ok cuts231 [⟨state231_29,exclude231_29⟩,⟨state231_171,exclude231_171⟩,⟨state231_179,exclude231_179⟩,⟨state231_180,exclude231_180⟩] 0x1001510404410128080c08028082000330200c08028080410110406000210404410109080602009082000118080602009080410110404420220a0042001040442401080042021090042021040482801040426021090026000900100140900026024008c240209000424009000a22210900a22028080828028080a22220a00a02228080424028080262210900242209080828009080262220a00262009080424009080410108480410010808414010400410110500410110808212010808838108480212010900232208c80838108c88212210900212008480250110500250009000212009000250108480240109000414009001001508480212028081001528081001340056000028080212008481001310500414009080212008481001308480212009080414009080602009000240010404644019000602019100602010404240009000a0200900024004008ca08028200a02028200a02040054240009000242009000240040004a0800840424202820024204000424000900100384008c8202 (by decide +kernel)

def state231_182 : List Sig := [0x3f3f3f3f333333333f3f3f3f333333333f3f3f3f333333330f0f0f0f00000000,input 6,input 7,input 5,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_182 : Impossible true (goalAt 231) 4 state231_182.toFinset :=
  node_ok cuts231 [] 0x9400240009004240020c00820020804820010c004200108044200090008200280802400090004200180802400108008200301004200084808281084802420084042400090802400090808200280808200104044200180804200 (by decide +kernel)

def state231_183 : List Sig := [0x3333333333333333333333333333333333333333333333330000000000000000,input 6,input 7,0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000,input 5,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_183 : Impossible true (goalAt 231) 5 state231_183.toFinset :=
  node_ok cuts231 [⟨state231_182,exclude231_182⟩] 0x250009000240109000830020800820120800430010800420110800240020800a220090002400108006220090002120105002120090802101090808200288808200090804200188804200090804240800002420108008200301004200105002120105002120109002400191002400280808200301008200104044200109004200 (by decide +kernel)

def state231_184 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,input 7,0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000,input 5,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_184 : Impossible true (goalAt 231) 6 state231_184.toFinset :=
  node_ok cuts231 [⟨state231_171,exclude231_171⟩,⟨state231_173,exclude231_173⟩,⟨state231_180,exclude231_180⟩,⟨state231_33,exclude231_33⟩,⟨state231_183,exclude231_183⟩] 0x9800240009008240010900c04020a00424020a00424010900828080010424010901002608480232008488212009400240009004240008480c0408000c212008480414010500212008480414010500212009000c0402920024000900064401910024000900064401910024000908024220988024200848041400848024200840424203010200020908024203020200010908024204008e000009080820230100c080106044101 (by decide +kernel)

def state231_185 : List Sig := [0x505050500000000050505050000000055555555555555550505050500000000,input 6,input 7,input 5,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_185 : Impossible true (goalAt 231) 4 state231_185.toFinset :=
  node_ok cuts231 [] 0x8c00210008408210020800820020808a02010c00410010408410008400a10028080210008400410018080210010400c00010600410008480212208c802120105002100084802100084808202280808202108084100180804100 (by decide +kernel)

def state231_186 : List Sig := [0xf0f0f0f000000000f0f0f0f00000000ffffffffffffffff0f0f0f0f00000000,input 6,input 7,input 5,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_186 : Impossible true (goalAt 231) 5 state231_186.toFinset :=
  node_ok cuts231 [⟨state231_185,exclude231_185⟩] 0x9800240009008240020800820020808a02018880602018088602008480232008488212009400240009004240020c0882022080c820208480602010500212009000a40028080240009000604018080240030000c000302008202090802422098802420084820000084802420084042400090802400090808202280808202104044101180802420 (by decide +kernel)

def state231_187 : List Sig := [0xffffffffffffffff0000000000000000,input 6,input 7,0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000,input 5,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_187 : Impossible true (goalAt 231) 6 state231_187.toFinset :=
  node_ok cuts231 [⟨state231_186,exclude231_186⟩,⟨state231_174,exclude231_174⟩] 0x9800240009008240020800820020808a02020a00424010900828008480232008488212009400240009004240020c0882022080c820208480414010500212009000a40028080240009000644019100240009080242209880242008480414008480242008404242020808a02020808242030202000109080c0003020082021090082801090082801050021201050021201910024001910024004008c2420800002420301004101 (by decide +kernel)

def state231_188 : List Sig := [0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000,input 5,input 0,input 1,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_188 : Impossible true (goalAt 231) 7 state231_188.toFinset :=
  node_ok cuts231 [⟨state231_178,exclude231_178⟩,⟨state231_181,exclude231_181⟩,⟨state231_34,exclude231_34⟩,⟨state231_158,exclude231_158⟩,⟨state231_168,exclude231_168⟩,⟨state231_184,exclude231_184⟩,⟨state231_187,exclude231_187⟩] 0x40054c04010404c00080018820230200c00080014c04030200c04040054820210404410140054820210900820040098a02020a00820040050820220a00820240054a02010900a02080010420220a0042004009841011090042008000c420210900420240098410120a0041014008c26021090026004009824004008c24004008c26024008c240240098240010900240040058830308480830240058820240058820240058830380008820340058820208480820240058410108480410040058420210500410040058410110500410140058420208480420240058838108480212040058424008c88232040058838108c88212240058424008480212040058250110500250040058240008480240040058250108480240140058240010500240040054a0200900024004008c820229200a4004008ca02029200a0204005482020900024004008c60200900024004008c41011910064004008c60201910060204008c410109000240040054a0200908024204008c82024008c82024008ca02080004a0204005482020908082024008c60200908024204008c41014008c41014008c60208000060204008c41010908041014009900230908024204008c42400988824224008d0023098882620400984240090802420400582120090802120400584140400584140400582120400582120400584140090802420400050001400042101 (by decide +kernel)

def state231_189 : List Sig := [0xfffffffffffffffffffffffffffffffffffffffffffffffffafafafafafafafa,input 0,input 7,input 6,input 1,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_189 : Impossible true (goalAt 231) 5 state231_189.toFinset :=
  node_ok cuts231 [] 0x21011040424400840421012840424800840424000900021014008c230108404210308404430110404410310404830120c04830310900262009080242209080410130404c0401040442022080821010841021010900441401090082811050041011041041011080c83032081882032080c2120 (by decide +kernel)

def state231_190 : List Sig := [0x5555555555555555555555555555555555555555555555555050505050505050,input 0,input 7,input 6,input 1,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_190 : Impossible true (goalAt 231) 5 state231_190.toFinset :=
  node_ok cuts231 [] 0x210110404244008404210128404248008404230108404210308404430110404410310404830120c04830310900410130404c04010404210008400210109010212008c80212208480410010400410110818830220c08830320818240009000240408404242009880242209080420210404420610404820220808820620c0c4140 (by decide +kernel)

def state231_191 : List Sig := [0x3333333333333333333333333333333333333333333333333030303030303030,0xfffffffffffffffffffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0,input 7,input 6,input 0,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_191 : Impossible true (goalAt 231) 5 state231_191.toFinset :=
  node_ok cuts231 [] 0x210118010244008404210128010248008404260009800240408404210008400210109010410410410410510818830620818820720818212009880414008480c00430010c040104144200208002404084042404084044140084804140084804105108184204108104240208188204208102420 (by decide +kernel)

def state231_192 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,0xfffffffffffffffffffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_192 : Impossible true (goalAt 231) 4 state231_192.toFinset :=
  node_ok cuts231 [] 0x9880242009088242020810820420818244010810420410818410508480232008488212008480242010500212020c1882062081c8206104104104104144206208088202208184222104044101104148222084042101091004105 (by decide +kernel)

def state231_193 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,0xfffffffffffffffffffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0,input 6,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_193 : Impossible true (goalAt 231) 5 state231_193.toFinset :=
  node_ok cuts231 [⟨state231_192,exclude231_192⟩,⟨state231_113,exclude231_113⟩] 0x10810420410818410509880242009088242010900248080004424020810820420818424008480232008488212010410410410414420608480242010500212010500212008480414020c1882062081c820610404c00430010c040104142480104160000104142420092002420208882101208088202208190023 (by decide +kernel)

def state231_194 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 5,0xfffffffffffffffffffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0,input 7,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_194 : Impossible true (goalAt 231) 5 state231_194.toFinset :=
  node_ok cuts231 [⟨state231_192,exclude231_192⟩,⟨state231_97,exclude231_97⟩] 0x20810820420818424009880242009088242009900244080004244010810420410818410508480232008488212020c1882062081c82060848024201050021200950021200848024401041041041041442062080824402081a000020818242009100242010888210130010c00430100410510404410110415001c (by decide +kernel)

def state231_195 : List Sig := [0xffffffff000000000000000000000000ffffffff0000000000000000,input 5,0xfffffffffffffffffffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0,input 7,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_195 : Impossible true (goalAt 231) 5 state231_195.toFinset :=
  node_ok cuts231 [] 0x820420810820610900262009080242209080230108404210308404212008c80212208480830620818820720818212009080414008480210008400210109010820208404a00409200210109000240009010210110810420410818410510410410410414420630010c004301004105104042440 (by decide +kernel)

def state231_196 : List Sig := [0xfffffffffffffffffffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0,input 7,input 6,input 0,input 1,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_196 : Impossible true (goalAt 231) 6 state231_196.toFinset :=
  node_ok cuts231 [⟨state231_189,exclude231_189⟩,⟨state231_190,exclude231_190⟩,⟨state231_191,exclude231_191⟩,⟨state231_125,exclude231_125⟩,⟨state231_193,exclude231_193⟩,⟨state231_194,exclude231_194⟩,⟨state231_195,exclude231_195⟩] 0x8001821010840441051810060048001460400910041050840421014005c210108404820628200a00480010a08009200820608404210109080210109001002309010240009080240409011002308404210108c0c424008c04210140060210108c0e00030840c210110900210110818828010810410510900420410818424010818410520a00410520818424020810c04020a00820420818828020818c0401090042400988a000209880242010900242009888424009088242040060242008404414008400240408480210008404212008404240410500240420e04212008480424008c88232020e04232208488424008480212010414212010410420610500410410414414010414420608480420620c1c212020c1882064005c820620c1d00172081c820608480820680004212008480242010500242080000414010500242008480212030100410530010820630200c00430100c080301008206104144105400e9001c104050039400ac8202 (by decide +kernel)

def state231_197 : List Sig := [0x3333333333333333333333333333333333333333333333333030303030303030,0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0,input 7,input 6,input 0,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_197 : Impossible true (goalAt 231) 5 state231_197.toFinset :=
  node_ok cuts231 [] 0x210118010244008404a20020800822020800260009800240408404210008400210109010410410410410510818830020800820120800212009880414008480c00420800c040208004200218008200208188200090102101090102101105002120105002120104144206108104204280808200218108200090802420109002620 (by decide +kernel)

def state231_198 : List Sig := [0xfffffffffffffffffffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0,0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0,input 7,input 6,input 0,input 1,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_198 : Impossible true (goalAt 231) 6 state231_198.toFinset :=
  node_ok cuts231 [⟨state231_197,exclude231_197⟩] 0x210118010244008404210129010a08008404210109010240408404210109010240408404230108404210308404420410810420610414860421810860610900828010900424020a0200001090042404009c210008400210109010212008c80212208480410410410410510818870621818860721818212010500414008480212010500414008480c00430010c04010414c080400e8820221819002b208182420 (by decide +kernel)

def state231_199 : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaafffffffffffffffffafafafafafafafa,input 0,input 7,input 6,input 1,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_199 : Impossible true (goalAt 231) 5 state231_199.toFinset :=
  node_ok cuts231 [] 0x210110404244008404a00028000a02008404230108404210308404430110404410310404820020800820228080c00030000c0801040421010841021010900441401090083811050041011041041011080c830320808830320808212009000240008404a08009080262009088242010404420210404242020c0c820220c0c8202 (by decide +kernel)

def state231_200 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 5,0xfffffffffffffffff0f0f0f0f0f0f0f0,input 7,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_200 : Impossible true (goalAt 231) 5 state231_200.toFinset :=
  node_ok cuts231 [⟨state231_104,exclude231_104⟩] 0x20800820020808a02009900244080000244010810420410818410508480232008488212020c0882022080c820209500212008480244010410410410414420609080262009088242009080212010500212020818244009080242010888410110404410530200a02020808a02020808210130000c000280808202 (by decide +kernel)

def state231_201 : List Sig := [0xfffffffffffffffff0f0f0f0f0f0f0f0,input 7,input 6,input 0,input 1,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_201 : Impossible true (goalAt 231) 6 state231_201.toFinset :=
  node_ok cuts231 [⟨state231_199,exclude231_199⟩,⟨state231_126,exclude231_126⟩,⟨state231_200,exclude231_200⟩] 0x1002b08404210110414604018012000218100244010414210108404a02008404a00020808a08028000a02028200a02020808210108404230310900230108405001808404230380004210308404424008404420620a00420410414424010810420610900420610414828010414820210900820028080828020800820220a00820228080424028080210110500210009010212008400210108480210109010414009010838108480212010900232208c80838108c8821221090021200848041050848041041081841401041041051050041051081821201081883030848083022080900172080883034005c820320808212020809001710414c00020808c08030001002b30200c0802080841052080824044008c240008404242009000240409080240408405002308404424009080242020a00262209880424009888242220a00242009080414009080242008481002b08480414080000414008480242008480410509080410130201000110404410540004410530200242009081002b400ec8206 (by decide +kernel)

def state231_202 : List Sig := [0x3333333333333333333333333333333333333333333333330000000000000000,input 6,input 7,0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0,input 0,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_202 : Impossible true (goalAt 231) 5 state231_202.toFinset :=
  node_ok cuts231 [] 0x240009000240408404a20020800822020800210110810604008404210008400210109010212009080414008480830020800820120800430410810420510810860020800820420800420010810820030100820010900210118100210110500212010500212020a002420109002420280808200301008200104144204109004204 (by decide +kernel)

def state231_203 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,input 7,0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0,input 0,input 1,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_203 : Impossible true (goalAt 231) 6 state231_203.toFinset :=
  node_ok cuts231 [⟨state231_37,exclude231_37⟩,⟨state231_202,exclude231_202⟩] 0x9000240009010210108404c04028200210108404604018100210108404604018100210108c0421010840c210109880242009088242010900c04020a00424020a00424010900828080004424010901002708400210008404240408480232008488212008480242010500212008480c04080000212008480414010500212008480414010500212009081002b301002420090810001400ec242020808c08030100c084106144105 (by decide +kernel)

def state231_204 : List Sig := [0xfffffffffffffffffcfcfcfcfcfcfcfcfffffffffffffffffcfcfcfcfcfcfcfc,input 1,0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0,input 6,input 0,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_204 : Impossible true (goalAt 231) 6 state231_204.toFinset :=
  node_ok cuts231 [] 0xa00028000a02008404210118010244008404210109808240408404210108c0c230308404830220808820320808210008400210109010410410410410510818212009888414008480212008c88232208480212008c88232208480c00420808c040208084202400c0860220808820620808242020808860420808a02008c0c210108c0c210110810420410818410509888424009088828020808a02020808a020 (by decide +kernel)

def state231_205 : List Sig := [0x5555555555555555555555555050505055555555555555555555555550505050,input 5,0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0,input 6,input 1,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_205 : Impossible true (goalAt 231) 5 state231_205.toFinset :=
  node_ok cuts231 [] 0x820020800820228080420410810420610414262009080242209080230008400210208400c00420808c04020808410021c08820221818820208400a10028080210008400600409100210008400250009010210021818820221818820208480212208c802120108184105104104104084804140090802120090102100090102100 (by decide +kernel)

def state231_206 : List Sig := [0xfffffffffffffffffffffffff0f0f0f0fffffffffffffffffffffffff0f0f0f0,input 5,0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0,input 6,input 0,input 1,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_206 : Impossible true (goalAt 231) 6 state231_206.toFinset :=
  node_ok cuts231 [⟨state231_205,exclude231_205⟩] 0x820020800820228080420410810420610414262009080242209080260409010240609010828010900424020a00830220808820320808212008c80212208480410410410410510818212009080414008480250409010240509012000008480212040064c00420808c040208086020400d88606208088606208090036090108202280808202090106004091002404090802404084142101218188202218188202 (by decide +kernel)

def state231_207 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 7,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_207 : Impossible true (goalAt 231) 5 state231_207.toFinset :=
  node_ok cuts231 [⟨state231_192,exclude231_192⟩,⟨state231_38,exclude231_38⟩] 0x262009080242209080420410810420610414a22028080a02228080264009100828009100212008c80212208480212009080414008480410410410410510818212028082000108480254008480212009100410110404410528200242028082000009080244009080242010888410528200a020104142101084042440104148202 (by decide +kernel)

def state231_208 : List Sig := [0x5555555555555555555555550000000055555555555555555555555500000000,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 5,0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0,input 1,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_208 : Impossible true (goalAt 231) 5 state231_208.toFinset :=
  node_ok cuts231 [⟨state231_101,exclude231_101⟩] 0x20800820020808a02009880242009088242009900244080000244010c10410410418410421808820220818820210400410010411003728080820228080820209080244009080422208400410420808a02020808212020808a020208082120084882320084802120105002420084802440084802120095004206 (by decide +kernel)

def state231_209 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 5,0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0,input 0,input 1,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_209 : Impossible true (goalAt 231) 6 state231_209.toFinset :=
  node_ok cuts231 [⟨state231_207,exclude231_207⟩,⟨state231_194,exclude231_194⟩,⟨state231_200,exclude231_200⟩,⟨state231_208,exclude231_208⟩,⟨state231_39,exclude231_39⟩,⟨state231_107,exclude231_107⟩,⟨state231_147,exclude231_147⟩] 0x820210900820028080828020800820220a00820228080424028080262220a0026200908042400908026221090024220908082800908100231090026400910100230910200064008e000509100424009100420620a00420410414424010810420610900420610414828010414830308480830220809001320808830380010820320808212020808838108480212010900232208c80838108c8821221090021200848100130848021200908041400908100131050041400908021200848100231050025400910021200848100130848021200910041400910041058000c41041081821201041041050848041051081900131081886060908086022080a00022080886068000482062080824202080841054008c410140004242010404410509080410540005003d40004a02009100a02020809002320808a02080000a020208082440208082420400ac24204008c24400910024200910024204008d002310889003c400a4210128080410530010820230210820228080c084280808202104148202 (by decide +kernel)

def state231_210 : List Sig := [0x5555555555555555555555550000000055555555555555555555555500000000,input 5,input 6,0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0,input 1,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_210 : Impossible true (goalAt 231) 5 state231_210.toFinset :=
  node_ok cuts231 [] 0x820020800820228080262009080242209080430410410410610410230008400210208400860220808820620808410420808c04020808410008400a10028080210008400250008410210008400410409100210008480820228080820208480212208c802120084804140090802120108184104105004104090102100084802100 (by decide +kernel)

def state231_211 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 5,input 6,0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0,input 0,input 1,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_211 : Impossible true (goalAt 231) 6 state231_211.toFinset :=
  node_ok cuts231 [⟨state231_210,exclude231_210⟩,⟨state231_108,exclude231_108⟩] 0x20800820020808a02009880242009088242020a00424010900828010900604080004424020a00424010900828020c0882022080c8202084802320084882120084802420105002120084804140105002120105002120084804140800002120084810019218088202208188202400d82420090810001301008202301008202180804105280808202280808202090806040090810023400a46040091002101280808202280808202 (by decide +kernel)

def state231_212 : List Sig := [0xffffffff000000000000000000000000ffffffff0000000000000000,input 5,0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0,input 0,input 1,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_212 : Impossible true (goalAt 231) 6 state231_212.toFinset :=
  node_ok cuts231 [⟨state231_195,exclude231_195⟩,⟨state231_40,exclude231_40⟩] 0x20808424020800a02020a00820020808828020808a02010900a02009888828009880242010900242009888424009088242020a00242008c0c424008c0421014008c210108c0d00230840c210110900210120c0c212020c0882024004c820220c0e00012080c820208480820220e04212008480424008c88232020e0423220848842400848021204004c21200848024201050024204004c4140105002420084802120084044140084002404084802100084042120084042404105002404218182420218088202400ac82022181a000020818820209080820228080210128000820228200a00028080a08028080820208404210109080210109001002309010240009080240409011002308404210130100410530010820230210820230100c0843010082021041482021090041051081082801081842041090042061081882801041441051050042061041021201041441041050041051041421201081842064008d003e104050029400f42440 (by decide +kernel)

def state231_213 : List Sig := [0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f00000000,input 5,input 7,input 6,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_213 : Impossible true (goalAt 231) 5 state231_213.toFinset :=
  node_ok cuts231 [] 0x420010800420210404860021800860228080260009000240209000212008c80212208480410010400410110808870221808860321808250009000240109000c00030000c04010404240018000244009000240029000a020090002420090882620090802120105002120090806020208088202280808602084042400090802400 (by decide +kernel)

def state231_214 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,input 7,0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0,input 6,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_214 : Impossible true (goalAt 231) 6 state231_214.toFinset :=
  node_ok cuts231 [⟨state231_207,exclude231_207⟩,⟨state231_213,exclude231_213⟩,⟨state231_193,exclude231_193⟩,⟨state231_41,exclude231_41⟩,⟨state231_116,exclude231_116⟩] 0x10810420410818410509880242009088242028880a02028088a02010900a08080010424010900828020a00424008480232008488212010410410410414420608480242010500212008480a0208000c212010500212008480414010500212008480414010404410528080c08410414410530210c084104142420280820002090820001090802420400ac820228200410580000410509080a48009080a08028080a080208882101 (by decide +kernel)

def state231_215 : List Sig := [0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0,input 6,input 0,input 1,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_215 : Impossible true (goalAt 231) 7 state231_215.toFinset :=
  node_ok cuts231 [⟨state231_196,exclude231_196⟩,⟨state231_198,exclude231_198⟩,⟨state231_201,exclude231_201⟩,⟨state231_203,exclude231_203⟩,⟨state231_42,exclude231_42⟩,⟨state231_204,exclude231_204⟩,⟨state231_157,exclude231_157⟩,⟨state231_129,exclude231_129⟩,⟨state231_153,exclude231_153⟩,⟨state231_155,exclude231_155⟩,⟨state231_206,exclude231_206⟩,⟨state231_209,exclude231_209⟩,⟨state231_211,exclude231_211⟩,⟨state231_212,exclude231_212⟩,⟨state231_214,exclude231_214⟩] 0x4005ca02008404a0004008c820228200a00080038a02028200a0204005c8202084042101400a6000d0840421014008c410518100600480032000b1810024404008c4105084042101400ac24200840424004008d00230901024008002824200901024044008d00230840421014005c82021090082004009ca02020a00820040060820220a0082024005ca02010900a0204008c23031090023014009c21018002421018002023038001c21034009c2101109002101400a4420620a0042044009c41051090042048001842061090042064009c410520a004105400ac262220a0026204009c24201090024208001426221090024224009c242020a00242040064830308480830240064820240064820240064830380010820340064820208480820240064210110500210040064240408480210040064210108480210140064240410500240440064838108480212040064424008c88232040064838108c8821224006442400848021204006441050848041044006442061050041044006441051050041054006442060848042064006500190848021204006424201050024204006500191050041404006424200848021204005cc04010414c004400a482023021082028000cc04030210c0404005c82021041482024000500014000441014005c8606090808602400ac82028000882028000486068000082064005c8202090808202 (by decide +kernel)

def state231_216 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 6,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_216 : Impossible true (goalAt 231) 5 state231_216.toFinset :=
  node_ok cuts231 [⟨state231_192,exclude231_192⟩] 0x262009080242209080820420810820610900622018080602218080268010900424009200212008c802122084802120090804144084808306208188207208182120180804140084802580084802120092008202208088206181006020090820000090806040208186020208184101090802480090808222084042101181008206 (by decide +kernel)

def state231_217 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 0,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_217 : Impossible true (goalAt 231) 6 state231_217.toFinset :=
  node_ok cuts231 [⟨state231_216,exclude231_216⟩,⟨state231_114,exclude231_114⟩,⟨state231_193,exclude231_193⟩] 0x1001c10404410109080450511406000211414410509080410110404c04410404410120818602030010c04418080602020818410110404420220a0042001040442401080042021090042021040482801040426221090026200908046440908026221191024220908042400908100041090042400920100040920100044008e000109200424010900820610900820430110828020810820620a00820630110424010900410108480410010808414010400410110500410110808212010808838108480212010900232208c80838108c88212210900212008481001c0848021200908045440908100131151041440908021200848025811050041400920021200848025810848021200920041401050083071050083062081821202081883070848082072081841402081882064008c82024000424202080882060908082064000500404000460200920060201040500231040460208000060201040424801040424204007024204008c248009200242009200242040071001c20889003f400142101 (by decide +kernel)

def state231_218 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f00000000,input 5,input 6,input 7,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_218 : Impossible true (goalAt 231) 5 state231_218.toFinset :=
  node_ok cuts231 [] 0x820020800820210900460011800460211404260009000240209000212008c80212208480830220808820320808450011400450111808250009000240109000c00030000c04411404240028000248009000240019000602009000242009088262009080212010510212009080a020104044101180804501084042400090802400 (by decide +kernel)

def state231_219 : List Sig := [0x5555555555555555555555550000000055555555555555555555555500000000,input 5,input 6,0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 7,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_219 : Impossible true (goalAt 231) 5 state231_219.toFinset :=
  node_ok cuts231 [] 0x820420810820610900262009080242209080430010400410210400230008400210208400820210400c10430110410010400450010410410008400a10409600210008400250008410210008400410018080210008480212208c802120084808206301108206084804144090802120108084100180804100090102100084802100 (by decide +kernel)

def state231_220 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 5,input 6,0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 7,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_220 : Impossible true (goalAt 231) 6 state231_220.toFinset :=
  node_ok cuts231 [⟨state231_218,exclude231_218⟩,⟨state231_216,exclude231_216⟩,⟨state231_194,exclude231_194⟩,⟨state231_219,exclude231_219⟩,⟨state231_110,exclude231_110⟩] 0x20810820420818424009880242009088242018880602018088602010900604080010424020a00424010900828008480232008488212020c1882062081c82060848024201051021200848060201050021201050021200848041408000c212008481000f20808602020818c04420818602009082000209080410118100820680004820609080644009080604018080604010888210130110820630110820609082000009081001c (by decide +kernel)

def state231_221 : List Sig := [0xfffffffffffffffffffffffffffffffff0f0f0f0fffffffff0f0f0f0f0f0f0f0,input 5,input 6,input 7,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_221 : Impossible true (goalAt 231) 5 state231_221.toFinset :=
  node_ok cuts231 [] 0x820420810820610900420410810420610414230108404210308404262009080242209080212008c80212208480830620818820720818410410410410510818210008400210109010212009080414008480820230010c00430100410510404410110414242008404a004092002101180006000180802101090002400090102101 (by decide +kernel)

def state231_222 : List Sig := [0xffffffff000000000000000000000000ffffffff0000000000000000,input 5,input 6,0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 7,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_222 : Impossible true (goalAt 231) 6 state231_222.toFinset :=
  node_ok cuts231 [⟨state231_221,exclude231_221⟩,⟨state231_195,exclude231_195⟩] 0x20810820420818424009880242009088242018880602018088602008c0421010840c210108480232008488212020c1882062081c820608480242010510212008480602010500212008400210008404240420808602020818c044208186020090820001090802101280102480084042400090002404084046000180802101109008280109008280105002120105002120301108206301108206400702420800002420104046040 (by decide +kernel)

def state231_223 : List Sig := [0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 7,input 0,input 1,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_223 : Impossible true (goalAt 231) 7 state231_223.toFinset :=
  node_ok cuts231 [⟨state231_130,exclude231_130⟩,⟨state231_217,exclude231_217⟩,⟨state231_220,exclude231_220⟩,⟨state231_222,exclude231_222⟩,⟨state231_196,exclude231_196⟩] 0x40014c04410404410140014820630200c00440014c04430200c04440014820610404410140071001c1040441014007024201141445014007200041141441054007024201040441018000c60200840460004008c41011810060008000860201810060204008c410108404210140015000508404210140014820628200a00440016000128200248040014820608404210140070242008404240040071002309010240040070242009010240440071001c08404210140010420220a004200400a04101109004200400104202109004202400a0410120a004101400102303109002301400a02101400102101400102303800002103400a0210110900210140014820610900820440014c04420a00820440014820620a00820640014c044109004240400702622109002620400a02420119102420400702622119102422400a024201090024204003c41010848041004003c42021050041004003c41011050041014003c42020848042024003c21011050021004003c24040848021004003c21010848021014003c24041050024044003c83810848021204003c424008c8823204003c838108c8821224003c42400848021204003c83070848083064003c82064003c82064003c83074001482074003c82060848082064003d000f0848021204003c24201151024204003d000f1151041444003c2420084802120400050001400048202 (by decide +kernel)

def state231_224 : List Sig := [0x5555555555555555555555555555555555555555555555555555555500000000,input 7,input 5,input 6,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_224 : Impossible true (goalAt 231) 5 state231_224.toFinset :=
  node_ok cuts231 [] 0x11400410010410410009400210008410210021c08830220c18830209880242009088242010c00410010408410008c00210008408210020c00830020c08a02010400c10030100410008400410018080210008400a10028080210008480414409080212008480212208c802120108084100180804100090102100084802100208088202280808302 (by decide +kernel)

def state231_225 : List Sig := [0x3333333333333333333333333333333333333333333333333333333300000000,input 7,input 5,input 6,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_225 : Impossible true (goalAt 231) 5 state231_225.toFinset :=
  node_ok cuts231 [] 0x11800420010810420009800260009810230121800820020810820008480242010510212010c00420010804420008c00230008c04260420c008200208048200108008200301004200188004200180804200288008200280808200090802422090802620084802122084802320104044200180804200084042101181002301280808200280808200 (by decide +kernel)

def state231_226 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000,input 7,input 5,input 6,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_226 : Impossible true (goalAt 231) 5 state231_226.toFinset :=
  node_ok cuts231 [] 0x11800460011808450109800240009008240021800860021808a02008480232008488212011400450011404460209400240009004240021c0886022180c860231000c40030100450109000640018080240009000a400280802400090802422098802420084804144084802420104044101180804501084042400090802400208088202280808602 (by decide +kernel)

def state231_227 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000,input 7,input 5,input 6,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_227 : Impossible true (goalAt 231) 6 state231_227.toFinset :=
  node_ok cuts231 [⟨state231_224,exclude231_224⟩,⟨state231_47,exclude231_47⟩,⟨state231_225,exclude231_225⟩,⟨state231_94,exclude231_94⟩,⟨state231_226,exclude231_226⟩] 0x242018080c08409080644009080242018100242028080c04409082000409080242040004262009080242209080622018080602218080424018102000310900a22028080a02228082000210900424040088212009080414408480212008c80212208480212018080414008480414008480212010500212028082000108482000008480212040000602028080c04018080410118080604018080422228080c040280808222084048202 (by decide +kernel)

def state231_228 : List Sig := [0xffffffffffffffffffffffff00000000,input 7,input 5,input 6,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_228 : Impossible true (goalAt 231) 6 state231_228.toFinset :=
  node_ok cuts231 [⟨state231_50,exclude231_50⟩,⟨state231_218,exclude231_218⟩,⟨state231_95,exclude231_95⟩] 0x242018080c08409080644009080242018100860220808820620808262009080242209080622018080602218080424018102000210900820020800820210900212009080414408480212008c80212208480212018080414008480414008480212010500830220808820320808c00030000c08020808602018100602010888a00028000a08020808242080004242040004424020a00424020a00212080000212040000410110404602030200210108404604028200a020 (by decide +kernel)

def state231_229 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_229 : Impossible true (goalAt 231) 5 state231_229.toFinset :=
  node_ok cuts231 [⟨state231_192,exclude231_192⟩] 0x19200242009080608019100242009080604009080602080000242009880242009088242018a00424010900608010900604020a004240188806020180886020084802420105102120084802320084882120186002120084806080105002120084804140084806020105002120084042101181004181104044101180808222208088202180804222 (by decide +kernel)

def state231_230 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 7,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 6,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_230 : Impossible true (goalAt 231) 6 state231_230.toFinset :=
  node_ok cuts231 [⟨state231_229,exclude231_229⟩,⟨state231_45,exclude231_45⟩,⟨state231_216,exclude231_216⟩,⟨state231_207,exclude231_207⟩] 0x908060208000c242029200242009080a08009080a02080008242019100242009080604009880242009088242018880602018088602020a00424010900828028880a02028088a02010900604020a00424008480242010510212008480232008488212008480602010500212028600212008480a08008480a02080004212010500212008480414010404602028082000018080604018080602010888a02028200a020208882101084046040400148202 (by decide +kernel)

def state231_231 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 5,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_231 : Impossible true (goalAt 231) 6 state231_231.toFinset :=
  node_ok cuts231 [⟨state231_229,exclude231_229⟩,⟨state231_51,exclude231_51⟩,⟨state231_98,exclude231_98⟩,⟨state231_194,exclude231_194⟩] 0x19100242009080604031200242009080c08009080c0403011024200908060208000c242009880242009088242010900604080008424020a00424010900828010900c04020a00424018880602018088602008480242010510212008480232008488212010500212008480414030600212008480c08008480c04080004212008480602010500212008404604028102000018100602018100602010888c04030200c040106044101104046020400148202 (by decide +kernel)

def state231_232 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0,input 7,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 5,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_232 : Impossible true (goalAt 231) 5 state231_232.toFinset :=
  node_ok cuts231 [⟨state231_99,exclude231_99⟩] 0x264009102000009100420410810420610414820020800820228080262009080242209080212008c80212208480254008480212009100410410410410510818830220808820320808212009080414008480210128080820228080820230000c00028080820209100242009080422210404410110414c080218088202208188202 (by decide +kernel)

def state231_233 : List Sig := [0xffffffffffffffff0000000000000000,input 7,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 5,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_233 : Impossible true (goalAt 231) 6 state231_233.toFinset :=
  node_ok cuts231 [⟨state231_232,exclude231_232⟩,⟨state231_100,exclude231_100⟩] 0x644009080242018100c48009080242030200860220808820620808262009080242209080424018102000110900828010900424020a00820020800820228080212009080414408480212008c80212208480414008480212010500c18008480212030200830220808820320808210128080820228080820230000c00028080820218080242080000242018080622018088602018080212010500212018100602018080422210404c040 (by decide +kernel)

def state231_234 : List Sig := [0x505050505050505050505050000000005050505050505050505050500000000,0x5555555555555555555555550000000055555555555555555555555500000000,input 5,input 6,input 1,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_234 : Impossible true (goalAt 231) 5 state231_234.toFinset :=
  node_ok cuts231 [] 0x820020800820228080430010400410210400230008400210208400410030400c04010400210028400a02008400210010400602008400a02020808a02020808424020a00424010510460210400602010400240008400604008400242020808a020208082420090882620090802420104006020104006040084002420084002120 (by decide +kernel)

def state231_235 : List Sig := [0xffffffffffffffffffffffffffffffff55555555555555555555555500000000,input 7,input 5,input 6,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_235 : Impossible true (goalAt 231) 5 state231_235.toFinset :=
  node_ok cuts231 [] 0x450010400410410400250008400210408400242028080c04409080414408480242008480262009080242209080430010400410210400230008400210208400a22028080a02228080212208480232008480410028080c04010400410010808602010400210010400602008400210030100a020084002100090102120084008202 (by decide +kernel)

def state231_236 : List Sig := [0x5555555555555555555555550000000055555555555555555555555500000000,input 5,input 6,input 1,input 2,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_236 : Impossible true (goalAt 231) 6 state231_236.toFinset :=
  node_ok cuts231 [⟨state231_234,exclude231_234⟩,⟨state231_235,exclude231_235⟩,⟨state231_50,exclude231_50⟩,⟨state231_210,exclude231_210⟩,⟨state231_219,exclude231_219⟩] 0x218182420218088202400dc82022181a0004208188202090808202114102420114004100400dc4100114120003104104100090804100094110037094002100090802100094102420084102100400dc210020808424020800a02020a00820020808828020808a02010900a02009888424009880242011910242009888464409088242010900242010c08828010c00410010900410010c08424010408410020a00410008c08424008c002100400dc210008c09003708408210010900210030100410010400820230600c10030100c18030100820210400410028080210008400820228600a10028080a18028080820208400210018080210008400410018100410018080604018080410008400210028080212008480820280008820228082000128080820208480820209080212008482000011510414409080454409081003708480212010900212008480828008c88212210900232208c808280084802120180802120108084100105004100180804140180804100084804100181004140090102100084802100181002120084802100105002100 (by decide +kernel)

def state231_237 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f0f0f0f0f0f0f0f0f00000000,0x5555555555555555555555550000000055555555555555555555555500000000,input 5,input 6,input 1,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_237 : Impossible true (goalAt 231) 5 state231_237.toFinset :=
  node_ok cuts231 [] 0x20800820020808a02011c00450011408450009c00250009408250011400c50030100450009400a50028080250009400450018080250008480820228080820208480212208c802120118084500180804500090002400084802500090808202280808202090802422098802420104004100180804500084002100090802500084802420084804144 (by decide +kernel)

def state231_238 : List Sig := [0x5555555555555555555555550000000055555555555555555555555500000000,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 5,input 6,input 1,input 2,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_238 : Impossible true (goalAt 231) 6 state231_238.toFinset :=
  node_ok cuts231 [⟨state231_102,exclude231_102⟩,⟨state231_237,exclude231_237⟩,⟨state231_208,exclude231_208⟩] 0x21808820220818820209080602080008242019100242009080604080004242009081003720800820020808a02009880242009088242018880602018088602010900604080000424020a00424010900828018080820230100820210400a02020808a02020808602018100422208400a02020808a02020808212020808a020208082120105102420084802120084882320084802120105006020084804140084802120105010000 (by decide +kernel)

def state231_239 : List Sig := [0x3333333333333333333333330000000033333333333333333333333300000000,input 1,input 5,input 6,input 0,input 2,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_239 : Impossible true (goalAt 231) 6 state231_239.toFinset :=
  node_ok cuts231 [] 0x860220808820620808460210808420610808260209808260608c0c830220808820320808212009080414408480430210808420310808230208c08230309818212008c88232208480420220808c04010808a20220808a02020808620210808602010808820020800820228080262209080262209080420010800420218080230108c04230318100a02020808a02020808242009888242009888212008c88212008c88410110404602010808210108404604008c0c4240 (by decide +kernel)

def state231_240 : List Sig := [0xffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f00000000,input 7,input 5,input 6,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_240 : Impossible true (goalAt 231) 5 state231_240.toFinset :=
  node_ok cuts231 [⟨state231_52,exclude231_52⟩] 0x460011800460211404260009000240209000a22028080a02228080242209080262009080212008c80212208480450011400450111808250009000240109000212028082000008480414408480212009080450128080c04011404410110404602011404240019000602009000240030100a020090002400084042420090008202 (by decide +kernel)

def state231_241 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f0f0f0f0f0f0f0f0f00000000,input 5,input 6,input 0,input 1,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_241 : Impossible true (goalAt 231) 6 state231_241.toFinset :=
  node_ok cuts231 [⟨state231_240,exclude231_240⟩,⟨state231_218,exclude231_218⟩,⟨state231_53,exclude231_53⟩] 0x20808424020800a02020a00820020808828020808a02010900a02011808828011800450110900460011808424011808450120a0045010980842400980024004008c240009809002309008240010900240020c0c212020c0882024004c820220c0e00022080c820208480820220e04212008480424008c88232020e04232208488424008480212011404212011400460210500450011404414011404460208480460209404414009400240008480240009404212009004240010500240030100450131000820231200c40030100c48030100820211404450128080240009000820229200a40028080a4802808082020900024001808024000900045011810064001808060401808045010900024002808024200908082028000482022808200002808082020908082021090024200908046440988824221090026220988046440908024200848024200848045444004c4144084810013084804544090802420180802420104044501400d8410118081003d180804501090804501181010001084042400090802400181002420090802400400042400 (by decide +kernel)

def state231_242 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f0f0f0f0f0f0f0f0f00000000,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 5,input 6,input 0,input 1,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_242 : Impossible true (goalAt 231) 6 state231_242.toFinset :=
  node_ok cuts231 [⟨state231_237,exclude231_237⟩,⟨state231_103,exclude231_103⟩] 0x20800820020808a02018880602018088602010900604080004424020a00424010900828020c0882022080c820208480232008488212008480602010500212010500212008480414080000212008481001318080820230100820211404a02020808a02020808602018100422209000a02020808a02020808242020808a0202080824200908826200908021201051021200908024204008c6020090806040090802420191010001 (by decide +kernel)

def state231_243 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 5,input 6,input 0,input 1,input 2,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_243 : Impossible true (goalAt 231) 7 state231_243.toFinset :=
  node_ok cuts231 [⟨state231_227,exclude231_227⟩,⟨state231_228,exclude231_228⟩,⟨state231_230,exclude231_230⟩,⟨state231_231,exclude231_231⟩,⟨state231_233,exclude231_233⟩,⟨state231_236,exclude231_236⟩,⟨state231_238,exclude231_238⟩,⟨state231_54,exclude231_54⟩,⟨state231_141,exclude231_141⟩,⟨state231_239,exclude231_239⟩,⟨state231_111,exclude231_111⟩,⟨state231_148,exclude231_148⟩,⟨state231_241,exclude231_241⟩,⟨state231_242,exclude231_242⟩,⟨state231_209,exclude231_209⟩,⟨state231_211,exclude231_211⟩,⟨state231_220,exclude231_220⟩] 0x860609080860220809003d20808860680040820620808242020809003d09080242018081003d18081003d8003e000e1808024200908064444008c644018100242009080644409080242018101003d18101003d80036000c40004242009081003d09080242040005003d40004820210900820028080828020800820220a00820228080424028080262210900262009080464409080262211910242209080424009080622220a00622018080424018080622210900602218080828018081002310900424018101002318102000b4008e000a18100424010902000920a00828040088424010902000810900424040088828020a0083030848083022080900412080883038001c820320808212020809003d08480212009080454409081004111510414409080212008480838108480212010900232208c80838108c8821221090021200848100410848021201808041401808100411050041401808021200848100411050041401810021200848100410848021201810041401050100418001a000540000212008481004108480212040001004140000c0401808060202080a000420808c0408000cc0402080860202080900364008c41012808060402808082024008c82022808200022808082021810082021808100291808100231810060404008d002310889003c400a42101280810005280808202800048202280820000280808202400148202 (by decide +kernel)

def state231_244 : List Sig := [0xccccccccffffffffccccccccccccccccccccccccffffffffcccccccccccccccc,input 1,input 5,input 6,input 0,input 2,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_244 : Impossible true (goalAt 231) 6 state231_244.toFinset :=
  node_ok cuts231 [] 0x860220808820620808460210808420610808240009000240408404830220808820320808212009080414408480430210808420310808210008400210109010212008c88232208480212008c88232208480420220808c04010808a00028000a0200840460001800060200840482022808082022808026220908026220908042021808042021040c230308404230308404828020808a02020808a02009888242009888242010404410110808602008c0c210108c0c2101 (by decide +kernel)

def state231_245 : List Sig := [0xf0f0f0f0fffffffff0f0f0f0f0f0f0f0f0f0f0f0fffffffff0f0f0f0f0f0f0f0,input 5,input 6,input 0,input 1,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_245 : Impossible true (goalAt 231) 6 state231_245.toFinset :=
  node_ok cuts231 [⟨state231_221,exclude231_221⟩,⟨state231_56,exclude231_56⟩] 0x20808424020800a02020a00820020808828020808a02010900a02010818828010810410510900420410818424010818410520a00410508c0c424008c0421014008c210108c0d00230840c210110900210109888828009880242010900242009888424009088242020a00242020c0c212020c0882024004c820220c0e00012080c820208480820220e04212008480424008c88232020e0423220848842400848021201041421201041042061050041041041441401041442060848042060840441400840024040848021000840421200840424041050024044004c21200848024201050024204004c414010500242008480212030100410530010820230210820230100c08430100820210414820228080210128000820228200a00028080a080280808202084042101180802101180004105191006000180806440180804105084042101218182420218088202400ac82022181a0000208188202090808202104142420104046020400044101104150001104146020090802420090110001090002101090802400090102420090102101400042101 (by decide +kernel)

def state231_246 : List Sig := [0x3333333333333333333333333333333300000000333333330000000000000000,input 7,input 5,input 6,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_246 : Impossible true (goalAt 231) 5 state231_246.toFinset :=
  node_ok cuts231 [] 0x11800420010810420009000240009010210121800820020810820008480242010510212010c00420010804420008400210008404240420c008200208048200108008200301004200180004200108804200288008200208808200109002420119002420105002120105002120104044200109004200109002101181002101280808200301008200 (by decide +kernel)

def state231_247 : List Sig := [0xffffffffffffffffffffffffffffffff00000000ffffffff0000000000000000,input 7,input 5,input 6,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_247 : Impossible true (goalAt 231) 6 state231_247.toFinset :=
  node_ok cuts231 [⟨state231_55,exclude231_55⟩,⟨state231_246,exclude231_246⟩,⟨state231_221,exclude231_221⟩] 0x242018080c08409080240009000240408404242030100c04409080242040006000209080262009080242209080622018080602218080230108404210308404424030100828010902000110900424040088212009080414408480212008c80212208480212018080414008480210008400210109010212030102000008480212010500414008480602030200c04018080410110404c08018080600018000602008404210130100a080084042101282006040084048202 (by decide +kernel)

def state231_248 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,0xffffffff000000000000000000000000ffffffff0000000000000000,input 5,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_248 : Impossible true (goalAt 231) 6 state231_248.toFinset :=
  node_ok cuts231 [⟨state231_57,exclude231_57⟩,⟨state231_195,exclude231_195⟩] 0x240009000240408404242030100c04409080242018082000109080262009080242209080230108404210308404424030100828010900622018080602218080212009080414408480212008c80212208480210008400210109010212030102000008480212018080414008480210130100608008404600018000602008404c08009080c08409080424020a00424020a00414008480414008480604030100c080301004181104048202 (by decide +kernel)

def state231_249 : List Sig := [0xffffffff000000000000000000000000ffffffff0000000000000000,input 5,input 6,input 0,input 1,input 2,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_249 : Impossible true (goalAt 231) 7 state231_249.toFinset :=
  node_ok cuts231 [⟨state231_244,exclude231_244⟩,⟨state231_245,exclude231_245⟩,⟨state231_247,exclude231_247⟩,⟨state231_248,exclude231_248⟩,⟨state231_58,exclude231_58⟩,⟨state231_212,exclude231_212⟩,⟨state231_222,exclude231_222⟩] 0x860609080860220809003c20808860680018820620808242020809003c09080242018081003c18081003c400a600051808024200908024044008c240008404242009000240409080240408405003c08404820210900820028080828020800820220a00820228080424028080262210900262009080464409080262211910242209080424009080622220a0062201808042401808062221090060221808082801808023031090023010840500230840423034008c210308404424008404830308480830220809004220808830380010820320808212020809003c08480212009080454409081004211510414409080212008480838108480212010900232208c80838108c88212210900212008481004208480212018080414018081004210500414018080212008480210110500210009010212008400210108480210109010414009010c04018080602020809002920808c0408000cc04020808602020808a02008404a00020808a08028000a02028200a0202080821010840500234008c6000180810029180810023084042101301010005301008202400a48202301020002301008202400148202400f10001400042420400f02420400a5003c800042420400042420109010022109008280400a482801090200001090082804008882801050100001050021204010821201050100421050021204000021204008d003e104050029400f46040 (by decide +kernel)

def state231_250 : List Sig := [0x5555555555555555050505050505050555555555555555550505050500000000,input 6,input 5,input 7,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_250 : Impossible true (goalAt 231) 4 state231_250.toFinset :=
  node_ok cuts231 [] 0x20c00830020c08a02008c00210008408210010c00410010408410008400a10028080210008400410018080210010400c10030100410008480212208c802120208088202280808302105002100084802100108084100180804100 (by decide +kernel)

def state231_251 : List Sig := [0xffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f00000000,input 6,input 5,input 7,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_251 : Impossible true (goalAt 231) 5 state231_251.toFinset :=
  node_ok cuts231 [⟨state231_250,exclude231_250⟩] 0x860021800860228080260009000240209000622018080602218080242209080262009080212008c80212208480870221808860321808250009000240109000212018080414008482000008480212009080240029000a02009000240018100602009000240008404242009000602021808c040218084101208088202280808602 (by decide +kernel)

def state231_252 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f00000000,input 5,input 7,input 0,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_252 : Impossible true (goalAt 231) 6 state231_252.toFinset :=
  node_ok cuts231 [⟨state231_251,exclude231_251⟩,⟨state231_213,exclude231_213⟩] 0x31100410131000860230200c40031100c08031100860210404410110808828010800410110900420010808424010808410120a00410121808424021800a02020a00860021808828021808a02010900a02009808424009800240040050240009809002309008240010900240010404212010400420210500410010404414010404420208480420220e04212008480424008c88232020e04232208488424008480212021c0c212021c08860240054860221c0d00152180c860208480860209404414009400240008480240009404212009004240010500240018080240009000410119100640018080644018080410109000240028080240009000860228200a40028080a08028080860209000240018080242009080410180004410118082000018080410109080410120a00242009080424009888242220a0026220988042400908024200848024200848041404004c4140084810013084804140090802420280802420208088602400e08202280810040280808602090808602282010001084042400090802400282002420090802400400042400 (by decide +kernel)

def state231_253 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f00000000,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,input 7,input 0,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_253 : Impossible true (goalAt 231) 6 state231_253.toFinset :=
  node_ok cuts231 [⟨state231_46,exclude231_46⟩,⟨state231_112,exclude231_112⟩] 0x10404a02030200410110404602018080410110800420010808410128880a02028088a02010900a08080004424010900828020a00424010400410010404420208480232008488212008480a02080000212010500212008480414010500212008480414021808602010404602010404a0202820082220900024201040460201040424200908826200908021201050021200908024204008ca02009080a080090802420292010001 (by decide +kernel)

def state231_254 : List Sig := [0xffffffffffffffff0000000000000000ffffffff00000000,input 6,input 5,input 7,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_254 : Impossible true (goalAt 231) 6 state231_254.toFinset :=
  node_ok cuts231 [⟨state231_213,exclude231_213⟩,⟨state231_48,exclude231_48⟩,⟨state231_117,exclude231_117⟩] 0x242028080c04409080644009080242018100450110404410510404262009080242209080a22028080a02228080424018102000210900420010800420210404212009080414408480212008c80212208480212028082000108480414008480212010500410010400410110808a02030100a02020888600018000604010404c00030000c04010404242080000242040004828010900828010900212010500212010500820220808a02030100210108404a080181006020 (by decide +kernel)

def state231_255 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_255 : Impossible true (goalAt 231) 6 state231_255.toFinset :=
  node_ok cuts231 [⟨state231_229,exclude231_229⟩,⟨state231_118,exclude231_118⟩,⟨state231_193,exclude231_193⟩] 0x29200242009080a08031100242009080c04009080c08030210242009080a02080008242009880242009088242010900a08080004424010900c04020a00424020a00424010900828028880a02028088a02008480242010510212008480232008488212010500212008480414010500212008480414008480414010500212008480a02010500212008404608018202000028200a02028200a02020888820220808a0204008cc04030200c040106044101 (by decide +kernel)

def state231_256 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,input 7,input 0,input 1,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_256 : Impossible true (goalAt 231) 7 state231_256.toFinset :=
  node_ok cuts231 [⟨state231_230,exclude231_230⟩,⟨state231_49,exclude231_49⟩,⟨state231_119,exclude231_119⟩,⟨state231_252,exclude231_252⟩,⟨state231_253,exclude231_253⟩,⟨state231_217,exclude231_217⟩,⟨state231_214,exclude231_214⟩,⟨state231_227,exclude231_227⟩,⟨state231_254,exclude231_254⟩,⟨state231_255,exclude231_255⟩] 0x1000510404410128080c08028082000930200c080280804101104060008104044101400a46020180820007180806020400a4410110404450509080450110405004010404450580018410510404242010405004009080242028081004028081004040016000528080242009080a4844008ca48028200242009080a48409080242028201004028201004080012000340004242009081004009080242040005004040004420220a00420010404424010800420210900420210404828010404262210900262009080464409080262211910242209080424009080a22210900a22028080828028080a22220a00a0222808042402808100041090042402820100042820100044008e000228200424010901000410900424040088828020a01000420a00828040088424010900410108480410010808414010400410110500410110808212010809004008480212009080454409081004311510414409080212008480838108480212010900232208c80838108c88212210900212008481004308480212028081004328081004340016000128080212008480a18110500414028200212008480a1810848021202820041401050100431050041404000021200848100430848021204000041401050100384008c820218080a0801808041014008c410118082000018080410128200410128081000528081002328200a08040015000520889003f400142101 (by decide +kernel)

def state231_257 : List Sig := [0xf3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f0f0f0f0f0f0f0f0,0x3333333333333333333333333333333333333333333333330000000000000000,input 6,input 7,input 0,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_257 : Impossible true (goalAt 231) 5 state231_257.toFinset :=
  node_ok cuts231 [] 0xa20020800822020800620010800422010800210008400210109010830020800820120800430010800420110800212009080414008480420020800c04010800464008404604008404414008480414008480464020800c040208004105108004640108004240090002400090102101218008200208108200118004200108104200 (by decide +kernel)

def state231_258 : List Sig := [0xffffffff33333333ffffffff33333333ffffffff33333333ffffffff00000000,input 5,input 6,input 7,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_258 : Impossible true (goalAt 231) 5 state231_258.toFinset :=
  node_ok cuts231 [] 0x860020800820420800460010800420410800644009080242018100424409080242010900212009080414408480830020800820120800430010800420110800414008480212010500828108480212010900420020800c04010800a02020800a020208006020108006020108002101280808200280808200104044200180804200 (by decide +kernel)

def state231_259 : List Sig := [0xfafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafa,input 0,0x3333333333333333333333333333333333333333333333330000000000000000,input 6,input 7,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_259 : Impossible true (goalAt 231) 5 state231_259.toFinset :=
  node_ok cuts231 [] 0xa20020800822020800620010800422010800420020800c04010800424008404604008404a02020800c04020800410110800424010800424020e04414410900424009080464009080210108410210109004830120800830120800430110800430110800212009000240008404604021800820020c04820011800420010c044200 (by decide +kernel)

def state231_260 : List Sig := [0x3333333333333333333333333333333333333333333333330000000000000000,input 6,input 7,input 0,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_260 : Impossible true (goalAt 231) 6 state231_260.toFinset :=
  node_ok cuts231 [⟨state231_257,exclude231_257⟩,⟨state231_258,exclude231_258⟩,⟨state231_132,exclude231_132⟩,⟨state231_259,exclude231_259⟩,⟨state231_202,exclude231_202⟩,⟨state231_183,exclude231_183⟩] 0x28880210128800820028200820028880a080208808200084048200188802101188004200181004200188806040108804200084044200090120005090002101090802400090102420090102101401102101218102420218008200400d482002181100352081082000908082001181024201180042004011042001181200041081042000908042000840441400840024040848021000840421200840424041050024044011021200848024201151024208000c454410510242008480212020c04212020c008200400d4820020c05003520804820008480820010c04212010c00420010500420010c04414010804420008480420030100420010800820030200820030100c08030100820010800420018100424010900210180008210118102000118100210110900210140110424010900242011910242080000464411900242010900242010500424010500212020e04212010500838110500212010900212030100424028080820020a00820030100828030100820010900820030200828010404420010900420030200424010900420020a004200 (by decide +kernel)

def state231_261 : List Sig := [0xfffffffffffffffffffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0,0x3333333333333333333333333333333333333333333333330000000000000000,input 6,input 7,input 0,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_261 : Impossible true (goalAt 231) 5 state231_261.toFinset :=
  node_ok cuts231 [] 0x210120810a08008404210110810604008404240009000240408404210008400210109010830420810820520810430410810420510810212009080414008480820010810820430100420410800424008404604008404414008480414008480424020810c040208104105108104240108110045 (by decide +kernel)

def state231_262 : List Sig := [0x3333333333333333333333333333333333333333333333330000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,input 7,input 0,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_262 : Impossible true (goalAt 231) 6 state231_262.toFinset :=
  node_ok cuts231 [⟨state231_63,exclude231_63⟩,⟨state231_261,exclude231_261⟩] 0x8404c04028200210108404604018100210108404604018100210109000240009010210109080c04030110242009080c08030210242009081004480004242008400210008404240408480242010510212008480c04080000212008480414010500212008480414010500212020800c04030200418110800424008404604008404424009080464009080414008480414008480424020a00c04010900828010900424020a010020 (by decide +kernel)

def state231_263 : List Sig := [0xfffffffffffffffffffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,input 7,input 0,input 1,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_263 : Impossible true (goalAt 231) 6 state231_263.toFinset :=
  node_ok cuts231 [⟨state231_64,exclude231_64⟩,⟨state231_261,exclude231_261⟩] 0x8404c04028200210108404604018100210108404604018100210109000240009010210108c0421010840c210110900c04020a00424020a00424010900828080004424010901001809880242009088242008400210008404240408480232008488212008480c04080000212008480414010500212008480414010500212008480242010500212020819002b30100c080106044105400850001 (by decide +kernel)

def state231_264 : List Sig := [0xf0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0f0f0f0f0,input 5,input 6,input 7,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_264 : Impossible true (goalAt 231) 5 state231_264.toFinset :=
  node_ok cuts231 [] 0x20810820420818a02010810420410818410508c0421010840c210109880242009088242008480232008488212020c1882062081c820610410410410414420608400210008404240408480242010500212030010c00430100410528000a000280802101180006000180802101208088202208182420104044101104142420090002400090102101 (by decide +kernel)

def state231_265 : List Sig := [0xffffffff00000000ffffffff00000000ffffffff0000000000000000,input 5,input 6,input 7,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_265 : Impossible true (goalAt 231) 6 state231_265.toFinset :=
  node_ok cuts231 [⟨state231_132,exclude231_132⟩,⟨state231_264,exclude231_264⟩,⟨state231_65,exclude231_65⟩] 0x242028080c04409080242018080c08409080240009000240408404262009080242209080a22028080a02228080622018080602218080230108404210308404212009080414408480212008c80212208480212028082000208480212018080414008480210008400210109010602028080c04018080a00028000a02008404600018000602008405000109082000109080424080000424040088414008480414008480820220808c04028080410110404c080180806040 (by decide +kernel)

def state231_266 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,input 7,input 0,input 1,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_266 : Impossible true (goalAt 231) 7 state231_266.toFinset :=
  node_ok cuts231 [⟨state231_66,exclude231_66⟩,⟨state231_260,exclude231_260⟩,⟨state231_262,exclude231_262⟩,⟨state231_133,exclude231_133⟩,⟨state231_196,exclude231_196⟩,⟨state231_263,exclude231_263⟩,⟨state231_203,exclude231_203⟩,⟨state231_184,exclude231_184⟩,⟨state231_227,exclude231_227⟩,⟨state231_265,exclude231_265⟩,⟨state231_231,exclude231_231⟩,⟨state231_248,exclude231_248⟩,⟨state231_255,exclude231_255⟩] 0x1000508404210130100a08030102000c28200a08030100210108406000b08404210130200604018102000a1810060403020021010840600090840421014008c60401810200081810060404008c21010840424048001c240008404242009000240409080240408405003b08404c44409080242030101003b30100c44440014c04430100242009080c48409080242030201003b30200c48480018c08430200242009081003b09080242040005003b40005003b8001600044000424200908023031090023010840500040840423038000c210308404424008404262210900262009080464409080262211910242209080424009081000510900424030100828030101000420a00828030100424010901000420a00828030200424010901000410900424030200828020a0100048000a000140088424010901000410900424040089000440088210110500210009010212008400210108480210109010414009011003b08480212009080454409081001e11510414409080212008480838108480212010900232208c80838108c88212210900212008481001e08480212030101001e30101001e40016000030100212008480c18108480212030200414010500c18110500414030200212008481001e08480212040000414010501001e105004140400002120084810039400a4820230101000530101002930200c08040015000510605003a400144101 (by decide +kernel)

def state231_267 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0,input 6,input 7,input 0,input 1,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_267 : Impossible true (goalAt 231) 6 state231_267.toFinset :=
  node_ok cuts231 [⟨state231_135,exclude231_135⟩,⟨state231_232,exclude231_232⟩] 0x28080210128000820228200a00028080a080280808202084042101400a4210108404410518100600480004604009100410508404210108c0c424008c04210140060210108c0e00000840c210110900210120808424020800a02020a00820020808828020808a02010900a02010818828010810410510900420410818424010818410520a00410509888828009880242010900242009888424009088242020a00242008404414008400240408480210008404212008404240410500240420e04212008480424008c88232020e04232208488424008480212020c0c212020c0882024005c820220c0d00172080c8202084808202104142120104104206105004104104144140104144206084804206400ac21200848024201050024204011c414010500242008480212031100410530000820230200c00031100c0803110082021041482020901100230900021010908024000901024200901021014008c2101218182420218088202400e4820221819003b20818820209080820210414242010404c08040004410110415000110414c080090802420 (by decide +kernel)

def state231_268 : List Sig := [0x5555555500000000555555550000000055555555555555555555555500000000,input 5,input 6,input 7,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_268 : Impossible true (goalAt 231) 5 state231_268.toFinset :=
  node_ok cuts231 [] 0x21808820220818820211400410010410410009400210008410210009880242009088242020800820020808a02010c00410010408410008c00210008408210010400c00010600410008400a10028080210008400410018080210008480414409080212008480212208c802120084808202280808202108084100180804100090102100084802100 (by decide +kernel)

def state231_269 : List Sig := [0xf0f0f0f000000000f0f0f0f000000000f0f0f0f0f0f0f0f0f0f0f0f00000000,input 5,input 6,input 7,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_269 : Impossible true (goalAt 231) 5 state231_269.toFinset :=
  node_ok cuts231 [] 0x20800820020808a02011800460011808450109800240009008240008480232008488212020c0882022080c820211400450011404460209400240009004240030000c00030110450109000a400280802400090006400180802400090802422098802420084804144084802420090808202280808202104044101180804501084042400090802400 (by decide +kernel)

def state231_270 : List Sig := [0xffffffff00000000ffffffff00000000ffffffffffffffffffffffff00000000,input 5,input 6,input 7,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_270 : Impossible true (goalAt 231) 6 state231_270.toFinset :=
  node_ok cuts231 [⟨state231_268,exclude231_268⟩,⟨state231_134,exclude231_134⟩,⟨state231_269,exclude231_269⟩] 0x860220808820620808242018080c08409080644009080242018102000209080242040004262009080242209080820020800820228080622018080602218080424018102000110900828010900424020a00212009080414408480212008c80212208480830220808820320808212018080414008480414008480212010502000008480212040000c00030000c08020808a02020808a02020808602018100602010888210128080820228080820210404410118080c080 (by decide +kernel)

def state231_271 : List Sig := [0xffffffffffffffff0000000000000000,input 6,input 7,input 0,input 1,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_271 : Impossible true (goalAt 231) 7 state231_271.toFinset :=
  node_ok cuts231 [⟨state231_267,exclude231_267⟩,⟨state231_270,exclude231_270⟩,⟨state231_136,exclude231_136⟩,⟨state231_187,exclude231_187⟩,⟨state231_233,exclude231_233⟩] 0xa02008404a00020808a08028000a02028200a0202080821010840500290840421013020060401810200041810060403020021010840424048000c240008404242009000240409080240408405003908404860609080860220809003920808860640014820620808242020808c48409080242030201003930200c484400a4c08430200242009080230310900230108405000408404230380008210308404424008404262210900262009080464409080262211910242209080424009080820210900820028080828020800820220a00820228080424028081000420a00828030200424010901000410900424030200828020a00210110500210009010212008400210108480210109010414009011003908480212009080454409081001d11510414409080212008480838108480212010900232208c80838108c88212210900212008480830308480830220809001d20808830340014820320808212020808c18108480212030200414010500c18110500414030200212008481000540014c000400a4c080302008202400148202181010023181002101400a421011810200011810021014008c2101400e50001400042420400e42420400a5003980000242040004242010901002210900828040010828010901000410900828040088828010501000010500212040074212010501001d105002120400002120400a5003b301010005401184101 (by decide +kernel)

def state231_272 : List Sig := roots 231
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude231_272 : Impossible true (goalAt 231) 8 state231_272.toFinset :=
  node_ok cuts231 [⟨state231_67,exclude231_67⟩,⟨state231_137,exclude231_137⟩,⟨state231_154,exclude231_154⟩,⟨state231_156,exclude231_156⟩,⟨state231_161,exclude231_161⟩,⟨state231_169,exclude231_169⟩,⟨state231_188,exclude231_188⟩,⟨state231_215,exclude231_215⟩,⟨state231_223,exclude231_223⟩,⟨state231_243,exclude231_243⟩,⟨state231_249,exclude231_249⟩,⟨state231_256,exclude231_256⟩,⟨state231_266,exclude231_266⟩,⟨state231_271,exclude231_271⟩] 0x40014c04010404c00080034820230200c00080030c04030200c04040014820210404410140014a02008404a0004008c820228200a0008002ca02028200a0204001482020840421018002860200840460004008c41011810060008002460201810060204008c41010840421014000486060908086024000482024000482024000486068002082064000482020908082024000445050908045014000441014000441014000445058001c410540004410109080410140004240480018240040004210109080240040004240409080240440004210140004210140014820210900820040088a02020a00820040010820220a00820240014a02010900a02080014420220a00420040088410110900420080010420210900420240088410120a0041014008c23031090023014008821018000c210180008230380004210340088210110900210140004262210900262040004242011910242040004262211910242240004242010900242040000830308480830240000820240000820240000830380000820340000820208480820240000410108480410040000420210500410040000410110500410140000420208480420240000210110500210040000240408480210040000210108480210140000240410500240440005000108480212040004242011510242040005000011510414440004242008480212040000838108480212040000424008c88232040000838108c882122400004240084802120 (by decide +kernel)

theorem lower231 : Claim 231 9 :=
  fromSearch 268436837 (by decide +kernel) exclude231_272

open PEqualNP.CircuitLowerBounds

def graph : Sig := goalAt 255
theorem graph_proper : proper graph := by unfold proper; decide +kernel

def edgeList : List Nat := [0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7]
def target (x : Fin 8 → Bool) : Bool :=
  decide (∃ i < edgeList.length / 2,
    (List.ofFn x).getD (edgeList.getD (2*i) 0) false = true ∧
    (List.ofFn x).getD (edgeList.getD (2*i+1) 0) false = true)

-- The three products cover the posted edges.
def smallCircuit : Circuit := ⟨[⟨.or,[0,1]⟩, ⟨.or,[0,2]⟩, ⟨.or,[1,3]⟩, ⟨.or,[4,6]⟩, ⟨.or,[5,10]⟩, ⟨.or,[6,7]⟩, ⟨.or,[7,8]⟩, ⟨.and,[11,14]⟩, ⟨.and,[9,5]⟩, ⟨.and,[12,13]⟩, ⟨.or,[15,16]⟩, ⟨.or,[18,17]⟩],19⟩

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

def lowRow (i : Fin 8) : Row := Fin.ofNat 256 (1 <<< ([4, 4, 5, 6, 0, 0, 0, 1] : List Nat).getD i.val 0)
def highRow (i : Fin 8) : Row := Fin.ofNat 256 ((1 <<< i.val) ||| (1 <<< ([4, 4, 5, 6, 0, 0, 0, 1] : List Nat).getD i.val 0))

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
  (ruleFor 255 lower231 none (by decide +kernel)).property 10 eightInputs
    (by decide +kernel) (by decide +kernel)


end PEqualNP.Outside.L_meta_28958

open PEqualNP.Outside.L_meta_28958 in
theorem PEqualNP.Outside.L_meta_28958 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o fit _ correct
  exact replaceShort lowerGraph gates o fit correct

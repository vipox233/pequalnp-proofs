import PEqualNP.Defs

-- The displayed monotone circuit uses 12 gates. For the lower bound, complements
-- are free: a circuit for the target still needs 11 binary gates, so a circuit
-- with one NOT gate has at least 12 gates. The search checks the necessary live
-- wires, restrictions to cliques and the symmetries of the graph.
-- The framework, the clique bounds and the certificate checker are taken from the
-- merged project proof L_meta_10454, which adapts L_meta_8449 and L_meta_8724
-- (Apache-2.0); the target, symmetries and certificate data are new.

namespace PEqualNP.Outside.L_meta_26245.LiveCircuits
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
lemma bit_zero (i) : bit i zero = false := by simp [bit,zero]
lemma bit_one (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
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
def graph : Sig := 0xffffffffffffffffffffffffffeaeae8fffefefcfffafaf8ffeeeeecffeaeae8ffffffffffffffffffffffffffeaeae8fffefefcfffafaf8ffeeeeecffeaeae8
def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 4) || (x 5 && x 7) || (x 6 && x 7)
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




end PEqualNP.Outside.L_meta_26245.LiveCircuits

namespace PEqualNP.Outside.L_meta_26245.FiveInputBounds

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Build: the goal is reached from the available wires in k binary steps. Live: the same,
-- keeping only the wires still needed, so a search may range over small sets.
section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero =>
    exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

theorem live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

theorem live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

theorem first_live {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal (k + 1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, tail⟩
      · exact .inl done
      · exact .inr ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, Or.inl tail⟩
    · exact .inr step

end Live

-- The upper and lower halves represent opposite target labels on 256 pairs of assignments.
abbrev W := BitVec 512
-- Free complementation leaves four binary choices up to output polarity.
def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 256 := ((x >>> 256) ^^^ x).setWidth 256
def cuts (ws : List W) : BitVec 256 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 256) ++ (0 : BitVec 256)
def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

theorem pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

theorem pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_,
          (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))

abbrev basicOps (a b : W) : Finset W := (ops a b).toFinset

def differs (i : Fin 256) (w : W) : Prop :=
  w.getLsbD (256+i.val) ≠ w.getLsbD i.val

theorem ops_differs (i : Fin 256) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 256+i.val < 512 := by omega
  have hi' : i.val < 512 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

theorem cuts_spec (ws : List W) (i : Fin 256) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have bx (p q : Bool) : Bool.xor p q = true ↔ p ≠ q := by cases p <;> cases q <;> decide
    simp [sep, i.isLt, differs, Nat.add_comm, bx]

theorem cuts_full {g : W} (hg : g = goal ∨ g = ~~~goal) {k : ℕ} {ws : List W}
    (h : live basicOps g k ws.toFinset) : cuts ws = -1 := by
  have hd : ∀ i, differs i g := by rcases hg with rfl | rfl <;> unfold differs <;> decide +kernel
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (hd ⟨j,hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 256)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto

-- The search: pick two live wires, apply one of the four operations, and keep each operand
-- only if it is still needed; every live run is found, so a false search rules out a build.
def keepChoices (a b : W) (r : List W) : List (List W) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept {ws r : List W} {a b : W} {needed : Finset W}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

theorem singleton_list {goal : W} {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

def dispatch (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) : Bool :=
  let base := cuts r
  (ops a b).any fun w =>
    let v := sep w ||| base
    ((v == -1) && next extra (w :: r)) ||
    ((extra != 0) && (((v ||| sep a == -1) && next (extra - 1) (w :: a :: r)) ||
                       ((v ||| sep b == -1) && next (extra - 1) (w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra - 2) (w :: a :: b :: r))

def optimized : ℕ → ℕ → List W → Bool
  | 0, _, ws => (ws == [goal] || ws == [~~~goal])
  | k + 1, extra, ws => (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a, b, r) => dispatch extra (optimized k) a b r)

theorem dispatch_complete {k extra : ℕ} {a b z : W} {r kept : List W}
    (next : ℕ → List W → Bool)
    (hz : z ∈ basicOps a b) (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts (z :: kept) = -1) (ht : next (k - kept.length) (z :: kept) = true) :
    dispatch extra next a b r = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
  simp [keepChoices] at hk
  rcases hk with rfl | rfl | rfl | rfl <;>
    simp only [cuts, List.foldr_cons] at hc ⊢ <;>
    (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  · left; left; exact ⟨hc, by convert ht using 2; omega⟩
  · left; right; exact ⟨by omega, .inl ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · left; right; exact ⟨by omega, .inr ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · right; exact ⟨⟨by omega, by convert hc using 1; ac_rfl⟩, by convert ht using 2; omega⟩

theorem optimized_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (ws : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n + 1) (h : live basicOps g n ws.toFinset) :
    optimized n extra ws = true := by
  induction n generalizing ws extra with
  | zero => rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn h]
  | succ k ih =>
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : W} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatch extra (optimized k) a b r = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live basicOps g k (z :: kept).toFinset := by
          simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        apply dispatch_complete (k := k) (extra := extra) (optimized k) hop hk (by omega) (by omega) (cuts_full hg hl)
        apply ih _ _ hnd _ hl
        simp; omega
      simp only [optimized, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

def search (n : ℕ) (inputs : List W) : Bool :=
  inputs.sublists.any fun ws =>
    decide (ws.length ≤ n+1) && (cuts ws == -1) && optimized n (n+1-ws.length) ws

theorem search_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (inputs : List W)
    (hn : inputs.Nodup) (h : build basicOps g n inputs.toFinset) : search n inputs = true := by
  classical
  obtain ⟨s,hs,hl⟩ := compress h
  let ws := inputs.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hnd : ws.Nodup := hn.filter _
  have hl' : live basicOps g n ws.toFinset := eq.symm ▸ hl
  have sz := live_card hl'
  rw [List.toFinset_card_of_nodup hnd] at sz
  exact List.any_eq_true.mpr ⟨ws,List.mem_sublists.mpr (List.filter_sublist ..),
    by simp [sz, cuts_full hg hl', optimized_complete hg n ws _ hnd (by omega : n+1-ws.length+ws.length=n+1) hl']⟩

-- Wires held up to complement, and what one binary gate reaches from them.
def holds (av : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

theorem holds_mono {av av' : Finset W} (sub : av ⊆ av') {x : W} (h : holds av x) :
    holds av' x :=
  h.imp_right (Or.imp_right fun ⟨a,ha,e⟩ => ⟨a,sub ha,e⟩)

theorem holds_not {av : Finset W} {z : W} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl|rfl|⟨a,ha,he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he|he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset W) (z : W) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

theorem reachable_not {av : Finset W} {z : W} (h : reachable av z) : reachable av (~~~z) := by
  rcases h with h|⟨a,ha,b,hb,ne,w,hop,hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a,ha,b,hb,ne,w,hop,holds_not hw⟩

set_option maxRecDepth 5000 in
theorem and_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x &&& y) := by
  have const : holds av (0 : W) := .inl rfl
  have oldx := hx
  rcases hx with rfl|rfl|⟨a,ha,ea⟩
  · rw [show (0 : W) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · change reachable av (BitVec.allOnes 512 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 512)
    rw [BitVec.and_allOnes]; exact .inl oldx
  by_cases h : a = b
  · subst b
    rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb] <;>
      simp only [BitVec.and_self, BitVec.and_not_self, BitVec.not_and_self] <;>
      first | exact .inl const | exact .inl (.inr (.inr ⟨a,ha,.inl rfl⟩)) |
        exact .inl (.inr (.inr ⟨a,ha,.inr rfl⟩))
  have add (w : W) (hw : w ∈ basicOps a b) (z : W) (hz : z = w ∨ z = ~~~w) :
      reachable av z :=
    .inr ⟨a,ha,b,hb,h,w,hw,.inr (.inr ⟨w,Finset.mem_insert_self ..,hz⟩)⟩
  rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb]
  · exact add _ (by simp [basicOps,ops] : a &&& b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : a &&& ~~~b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : b &&& ~~~a ∈ basicOps a b) _ (.inl (BitVec.and_comm ..))
  · exact add _ (by simp [basicOps,ops] : a ||| b ∈ basicOps a b) _ (.inr BitVec.not_or.symm)

theorem or_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))

end PEqualNP.Outside.L_meta_26245.FiveInputBounds

namespace PEqualNP.Outside.L_meta_26245.GraphTarget
open PEqualNP.Outside.L_meta_26245.LiveCircuits

def cols7 : List Sig := inputs.take 8
def full : Sig := 0xfffffffffffffffffffffffffefefcfcfffefffeffeeffeefefefcfcaaaa0000fffffffffffffffffffffffffefefcfcfffefffeffeeffeefefefcfcaaaa0000

end PEqualNP.Outside.L_meta_26245.GraphTarget

namespace PEqualNP.Outside.L_meta_26245.ExplicitCircuit
open PEqualNP.CircuitLowerBounds

def upper : Circuit :=
  ⟨[⟨.and, [7, 5]⟩,
    ⟨.or, [4, 6]⟩,
    ⟨.and, [9, 0]⟩,
    ⟨.or, [5, 7]⟩,
    ⟨.or, [1, 2]⟩,
    ⟨.and, [11, 12]⟩,
    ⟨.or, [1, 3]⟩,
    ⟨.or, [14, 7]⟩,
    ⟨.and, [15, 6]⟩,
    ⟨.or, [8, 10]⟩,
    ⟨.or, [17, 13]⟩,
    ⟨.or, [18, 16]⟩], 19⟩

def target (x : Fin 8 → Bool) : Bool :=
  decide (∃ i < ([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 1, 7, 2, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 1, 7, 2, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 1, 7, 2, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
theorem upperComputes : ∀ x : Fin 8 → Bool, upper.eval (List.ofFn x) = target x := by decide +kernel

theorem upperLegal : ∀ g ∈ upper.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [upper, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h|h|h|h|h|h|h|h|h|h|h|h <;> subst g <;> simp

theorem upperSize : upper.gates.length = 12 := rfl
end PEqualNP.Outside.L_meta_26245.ExplicitCircuit

namespace PEqualNP.Outside.L_meta_26245.CliqueBounds
open PEqualNP.Outside.L_meta_26245.LiveCircuits
open PEqualNP.Outside.L_meta_26245.FiveInputBounds

theorem convert {T : Sig} {k : Nat} {S : Finset Sig}
    (h : Live true T k S) {av : Finset Sig} (sub : S ⊆ av) : build basicOps T k av := by
  induction h using Live.ind generalizing av with
  | stop hp => exact sub (Finset.mem_singleton_self T)
  | @binary k U a b d hd ha hb hab hf ht ih =>
    have op : bin d a b ∈ basicOps a b := by
      rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;>
        simp [bin,basicOps,ops,BitVec.and_comm]
    apply Or.inr
    refine ⟨a,sub (by simp),b,sub (by simp),hab,bin d a b,op,ih ?_⟩
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact Finset.mem_insert_self ..
    · exact Finset.mem_insert_of_mem (sub (by simp [hw]))

theorem buildLift {T : Sig} {A : Finset Sig} {k l : Nat} (h : k ≤ l)
    (g : build basicOps T k A) : build basicOps T l A := by
  induction h with
  | refl => exact g
  | step _ ih => exact Or.inl ih

end PEqualNP.Outside.L_meta_26245.CliqueBounds

namespace PEqualNP.Outside.L_meta_26245.GraphTarget
open PEqualNP.Outside.L_meta_26245.LiveCircuits PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def sample7 (r : Row) (j : Fin 8) := bit r (cols7.getD j.val zero)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem sevenTable : ∀ r : Row, bit r full = PEqualNP.Outside.L_meta_26245.ExplicitCircuit.target (sample7 r) := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem sevenList : List.ofFn (fun i : Fin 8 => cols7.getD i.val zero) = cols7 := rfl
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem sevenSampled (r : Row) : List.ofFn (sample7 r) = cols7.map (bit r) := by
  rw [←sevenList,List.map_ofFn]; rfl
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem eval7 (C : Circuit) (h : FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates cols7).getD i zero) =
      (C.wires (List.ofFn (sample7 r))).getD i false := by
  rw [← b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),sevenSampled]
  rfl

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem binaryLower (low : Lower true cols7 full 11) (C : Circuit) (legal : FanInTwo C)
    (computes : ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = PEqualNP.Outside.L_meta_26245.ExplicitCircuit.target x) :
    11 ≤ C.gates.countP (fun g => !isNot g) := by
  classical
  have goalEq : (execute C.gates cols7).getD C.output zero = full := by
    apply bit_ext
    intro r
    exact (eval7 C legal C.output r).trans ((computes (sample7 r)).trans (sevenTable r).symm)
  have rep := get_rep (u:=true) (execute C.gates cols7) C.output
  rw [goalEq] at rep
  unfold PEqualNP.Outside.L_meta_26245.LiveCircuits.Repr at rep
  have pg : bit 0 full = false := by decide +kernel
  have pfull : proper full := by unfold proper; decide +kernel
  rw [nrm_id pg] at rep
  obtain ⟨k,S,hk,run,sub⟩ := extract C.gates cols7 legal (by simp) pfull (rep.resolve_right (fun h => h pfull))
  have plain : cols7.all plainWord = true := by decide +kernel
  rw [nrm_map plain] at sub
  have rs := list_run run S.toList (Finset.nodup_toList _) (Finset.toList_toFinset _)
  have hs : supply true (cols7.map observe) ((S.toList.map observe).map (restrictRows (id : Row → Row))) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
    exact Or.inl (List.mem_map_of_mem (sub _ (Finset.mem_toList.mp ha)))
  have b := projected_bound (id : Row → Row) rs (observe_proper pfull) Reach.start hs (L:=11) low
  omega
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem gateLower (low : Lower true cols7 full 11) (C : Circuit) (legal : FanInTwo C)
    (negUsed : ∃ g ∈ C.gates, g.op = GateOp.not)
    (computes : ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = PEqualNP.Outside.L_meta_26245.ExplicitCircuit.target x) :
    12 ≤ C.gates.length := by
  obtain ⟨g,hg,ng⟩ := negUsed
  have hc := binaryLower low C legal computes
  by_contra! h
  have all := (List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length (by omega : C.gates.length ≤ C.gates.countP (fun g => !isNot g)))) g hg
  simp [isNot,ng] at all


theorem finish (low : Lower true cols7 full 11) : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 1, 7, 2, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 1, 7, 2, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 1, 7, 2, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 1, 7, 2, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 1, 7, 2, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 1, 7, 2, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o legal _uniq computes
  change ∀ x : Fin 8 → Bool, (Circuit.mk gates o).eval (List.ofFn x) = PEqualNP.Outside.L_meta_26245.ExplicitCircuit.target x at computes
  by_cases hn : ∃ g ∈ gates, g.op = GateOp.not
  · have hl : FanInTwo ⟨gates,o⟩ := by
      intro g hg
      obtain ⟨ht,hw⟩ := legal g hg
      exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using ht, hw⟩
    have hs := gateLower low ⟨gates,o⟩ hl hn computes
    refine ⟨PEqualNP.Outside.L_meta_26245.ExplicitCircuit.upper.gates, PEqualNP.Outside.L_meta_26245.ExplicitCircuit.upper.output, PEqualNP.Outside.L_meta_26245.ExplicitCircuit.upperLegal, ?_, ?_⟩
    · exact hs
    · intro x
      exact PEqualNP.Outside.L_meta_26245.ExplicitCircuit.upperComputes x
  · refine ⟨gates,o,?_,Nat.le_refl _,computes⟩
    intro g hg
    obtain ⟨hor,hw⟩ := legal g hg
    rcases hor with ha | ho | hnot
    · exact ⟨Or.inl ha,hw⟩
    · exact ⟨Or.inr ho,hw⟩
    · exact (hn ⟨g,hg,hnot⟩).elim
end PEqualNP.Outside.L_meta_26245.GraphTarget

namespace PEqualNP.Outside.L_meta_26245.GraphSymmetry
open PEqualNP.Outside.L_meta_26245.LiveCircuits
abbrev T := PEqualNP.Outside.L_meta_26245.GraphTarget.full
abbrev ws0 := PEqualNP.Outside.L_meta_26245.GraphTarget.cols7
def low (s : Fin 1) : Sig :=
  match s.val with
  | _ => 0x0
def high (s : Fin 1) : Sig :=
  match s.val with
  | _ => 0x0
def shiftN (s : Fin 1) : Nat :=
  match s.val with
  | _ => 0
def plan (p : Fin 1) : List (Fin 1) :=
  match p.val with
  | _ => []

def stepWord (s : Fin 1) (w : Sig) : Sig :=
  (w &&& ~~~(low s ||| high s)) ||| ((w >>> shiftN s) &&& low s) |||
    ((w <<< shiftN s) &&& high s)

def stepRow (s : Fin 1) (r : Row) : Row :=
  if bit r (low s) then ⟨(shiftN s + r.val) % 512, Nat.mod_lt _ (by decide)⟩
  else if bit r (high s) then ⟨r.val - shiftN s, by have := r.isLt; omega⟩ else r

def permWord (p : Fin 1) (w : Sig) : Sig :=
  (plan p).foldl (fun v s => stepWord s v) w

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem stepChecks : ∀ s : Fin 1, ∀ r : Row,
    (bit r (low s) = true → bit r (high s) = false ∧ shiftN s + r.val < 512) ∧
    (bit r (high s) = true → shiftN s ≤ r.val) ∧ stepRow s (stepRow s r) = r := by
  decide +kernel

theorem stepEq (s : Fin 1) (w : Sig) : stepWord s w = rename (stepRow s) w := by
  apply bit_ext
  intro r
  rw [bit_rename]
  obtain ⟨safeL,safeH,inv⟩ := stepChecks s r
  cases hL : bit r (low s)
  · cases hH : bit r (high s)
    · simp [bit] at hL hH
      simp only [bit]
      simp [stepWord,stepRow,bit,hL,hH,r.isLt, BitVec.getLsbD_or, BitVec.getLsbD_and]
    · have cut := safeH hH
      have left : r.val - shiftN s < 512 := Nat.lt_of_le_of_lt (Nat.sub_le ..) r.isLt
      simp [bit] at hL hH
      simp only [bit]
      simp [stepWord,stepRow,bit,hL,hH,r.isLt, Nat.not_lt.mpr cut, left, BitVec.getLsbD_or, BitVec.getLsbD_and]
  · obtain ⟨hH,lt⟩ := safeL hL
    simp [bit] at hL hH
    simp only [bit]
    simp [stepWord,stepRow,bit,hL,hH,lt,r.isLt,Nat.mod_eq_of_lt lt, BitVec.getLsbD_or, BitVec.getLsbD_and]

set_option maxRecDepth 2000 in
theorem stepTarget : ∀ s : Fin 1, stepWord s T = T := by decide +kernel

theorem stepLive {k ws} (s : Fin 1) (h : Live true T k (List.toFinset ws)) :
    Live true T k (ws.map (stepWord s)).toFinset := by
  have hr := live_rename h (stepRow s) (fun y => ⟨stepRow s y,(stepChecks s y).2.2⟩)
  have e : rename (stepRow s) = stepWord s := funext (fun w => (stepEq s w).symm)
  rw [e,stepTarget] at hr
  have he : ws.toFinset.image (stepWord s) = (ws.map (stepWord s)).toFinset := by
    ext t
    simp
  exact he ▸ hr

theorem planLive {k : Nat} (ss : List (Fin 1)) {ws : List Sig} (h : Live true T k ws.toFinset) :
    Live true T k (ws.map fun w => ss.foldl (fun v s => stepWord s v) w).toFinset := by
  induction ss generalizing ws with
  | nil => simpa using h
  | cons s ss ih =>
    have v := ih (stepLive s h)
    simpa only [List.map_map,List.foldl_cons,Function.comp_def] using v

theorem isoTransfer (p : Fin 1) (ws : List Sig) (k : Nat)
    (h : Impossible true T k (ws.map (permWord p)).toFinset) : Impossible true T k ws.toFinset := by
  intro n hn bad
  exact h n hn (planLive (plan p) bad)

theorem isoTransferOf (p : Fin 1) (ws rep : List Sig) (k : Nat)
    (equal : (ws.map (permWord p)).toFinset = rep.toFinset)
    (h : Impossible true T k rep.toFinset) : Impossible true T k ws.toFinset :=
  isoTransfer p ws k (equal.symm ▸ h)

end PEqualNP.Outside.L_meta_26245.GraphSymmetry

namespace PEqualNP.Outside.L_meta_26245.CliqueRestrictions
open PEqualNP.Outside.L_meta_26245.LiveCircuits
def masks : List Nat := [162, 164, 194]
def cliqueDomain : Nat → Sig
  | 162 => 0x500000005000000000000000000000005000000050000000000000000000000050000000500000000000000000000000500000005
  | 164 => 0x1100000011000000000000000000000011000000110000000000000000000000110000001100000000000000000000001100000011
  | 194 => 0x50000000000000005000000000000000500000000000000050000000000000005000000000000000500000000000000050000000000000005
  | _ => 0
def cliqueSize : Nat → Nat
  | 162 => 3
  | 164 => 3
  | 194 => 3
  | _ => 0
def cliqueBound (m : Nat) := match cliqueSize m with | 5 => 9 | 4 => 7 | 3 => 4 | _ => 0
def embeds : Nat → List Row
  | 162 => [0, 2, 32, 34, 128, 130, 160, 162, 0, 2, 32, 34, 128, 130, 160, 162, 0, 2, 32, 34, 128, 130, 160, 162, 0, 2, 32, 34, 128, 130, 160, 162]
  | 164 => [0, 4, 32, 36, 128, 132, 160, 164, 0, 4, 32, 36, 128, 132, 160, 164, 0, 4, 32, 36, 128, 132, 160, 164, 0, 4, 32, 36, 128, 132, 160, 164]
  | 194 => [0, 2, 64, 66, 128, 130, 192, 194, 0, 2, 64, 66, 128, 130, 192, 194, 0, 2, 64, 66, 128, 130, 192, 194, 0, 2, 64, 66, 128, 130, 192, 194]
  | _ => []
def ranks : Nat → List Nat
  | 162 => [7, 0, 7, 7, 7, 1, 7, 2]
  | 164 => [7, 7, 0, 7, 7, 1, 7, 2]
  | 194 => [7, 0, 7, 7, 7, 7, 1, 2]
  | _ => []
def k4 : Sig := 0xfee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8
def k3 : Sig := 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8
def k5 : Sig := 0xfffefee8fffefee8fffefee8fffefee8fffefee8fffefee8fffefee8fffefee8fffefee8fffefee8fffefee8fffefee8fffefee8fffefee8fffefee8fffefee8
def standard : Nat → Sig | 5 => k5 | 4 => k4 | _ => k3
def embed (m : Nat) (r : Fin 32) : Row := (embeds m).getD r.val 0
def arg (m : Nat) (i : Fin 8) := (inputs.take (cliqueSize m)).getD ((ranks m).getD i.val 7) zero
def low (r : Row) : Fin 32 := ⟨r.val % 32,Nat.mod_lt _ (by decide)⟩
def toRow (j : Fin 32) : Row := ⟨j.val,by omega⟩
def ref (m : Nat) (r : Row) : Row := embed m (low r)

def cert (m : Nat) : Bool := decide (∀ j : Fin 32,
  bit (embed m j) (cliqueDomain m) = true ∧
    bit (embed m j) PEqualNP.Outside.L_meta_26245.GraphTarget.full = bit (toRow j) (standard (cliqueSize m)) ∧
    ∀ i : Fin 8, bit (embed m j) (PEqualNP.Outside.L_meta_26245.GraphTarget.cols7.getD i.val zero) = bit (toRow j) (arg m i))

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8192 in
theorem certs : masks.all cert = true := by decide +kernel

end PEqualNP.Outside.L_meta_26245.CliqueRestrictions

namespace PEqualNP.Outside.L_meta_26245.CliqueRestrictions
open PEqualNP.Outside.L_meta_26245.LiveCircuits
def smalls := zero :: k3 :: k4 :: k5 :: inputs.take 5
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem periods : smalls.all (fun w => decide (∀ r : Row, bit (toRow (low r)) w = bit r w)) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem facts : masks.all (fun m => decide (
    cliqueSize m=3 ∧ standard (cliqueSize m) ∈ smalls ∧
    ∀ i : Fin 8, arg m i ∈ smalls)) = true := by decide +kernel

theorem fromWord {xs : List Sig} (j : Nat) :
    Available true (xs.map observe) (observe (xs.getD j zero)) := by
  by_cases h : j < xs.length
  · apply Or.inl
    apply List.mem_map_of_mem
    simpa [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem h] using (List.getElem_mem h)
  · have hz : xs.getD j zero = zero := by simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none (by omega : xs.length ≤ j)]
    rw [hz]; exact Or.inr (Or.inl ⟨false,funext bit_zero⟩)

set_option maxHeartbeats 12000000 in
set_option maxRecDepth 8192 in
theorem validParam (m : Nat) (hm : m ∈ masks)
    (lower : Lower true (inputs.take (cliqueSize m)) (standard (cliqueSize m)) (cliqueBound m)) :
    Slice true PEqualNP.Outside.L_meta_26245.GraphTarget.cols7 PEqualNP.Outside.L_meta_26245.GraphTarget.full (cliqueDomain m) (cliqueBound m) := by
  have tbl0 := List.all_eq_true.mp certs m hm
  unfold cert at tbl0
  have tbl := of_decide_eq_true tbl0
  have info := of_decide_eq_true (List.all_eq_true.mp facts m hm)
  have periodic (x : Sig) (hx : x ∈ smalls) : ∀ r, bit (toRow (low r)) x = bit r x :=
    of_decide_eq_true (List.all_eq_true.mp periods x hx)
  have tgt : restrictRows (ref m) (observe PEqualNP.Outside.L_meta_26245.GraphTarget.full) = observe (standard (cliqueSize m)) :=
    funext fun r => ((tbl (low r)).2.1).trans (periodic _ info.2.1 r)
  refine ⟨ref m,inputs.take (cliqueSize m),fun r => (tbl (low r)).1,?_,?_,?_⟩
  · intro a ha
    obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp ha
    let i : Fin 8 := ⟨j,by exact hj⟩
    have eq : restrictRows (ref m) (observe (PEqualNP.Outside.L_meta_26245.GraphTarget.cols7.getD i.val zero)) = observe (arg m i) :=
      funext fun r => ((tbl (low r)).2.2 i).trans (periodic _ (info.2.2 i) r)
    have same : PEqualNP.Outside.L_meta_26245.GraphTarget.cols7.getD i.val zero = PEqualNP.Outside.L_meta_26245.GraphTarget.cols7[j] := by
      simp [i,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj]
    rw [← same,eq]; exact fromWord _
  · rw [tgt]
    apply observe_proper
    rw [info.1]; unfold proper; decide +kernel
  · rw [tgt]; exact lower
end PEqualNP.Outside.L_meta_26245.CliqueRestrictions

namespace PEqualNP.Outside.L_meta_26245.TriangleBound
open PEqualNP.Outside.L_meta_26245.LiveCircuits PEqualNP.Outside.L_meta_26245.CliqueBounds PEqualNP.Outside.L_meta_26245.FiveInputBounds

def k3 : Sig := 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8

def blocked (T : Sig) : Nat → List Sig → Bool
  | 0, ws => !ws.contains T
  | k+1, ws => !ws.contains T && ws.all fun a => ws.all fun b =>
      (ops a b).all fun z => blocked T k (z::ws)

theorem blockedSound (T : Sig) (k) (ws : List Sig) (h : blocked T k ws = true) :
    ∀ l ≤ k, ¬build basicOps T l ws.toFinset := by
  induction k generalizing ws with
  | zero =>
    intro l hl; have e : l=0 := by omega
    subst l
    simpa [blocked,build] using h
  | succ k ih =>
    simp only [blocked,Bool.and_eq_true,List.all_eq_true] at h
    intro l le
    induction l with
    | zero => simpa [build] using h.1
    | succ l hl =>
      rintro (prev|⟨a,ha,b,hb,_,z,hz,htail⟩)
      · exact hl (by omega) prev
      · have v := h.2 a (List.mem_toFinset.mp ha) b (List.mem_toFinset.mp hb) z (List.mem_toFinset.mp hz)
        exact ih (z::ws) v l (by omega) (by simpa using htail)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
theorem standardLower3 : Lower true (inputs.take 3) k3 4 := by
  intro p bank h hit
  have pT : proper k3 := by unfold proper; decide +kernel
  have gT : plainWord k3 = true := by decide +kernel
  have pR : (inputs.take 3).all plainWord=true := by decide +kernel
  obtain ⟨k,S,hk,run,sub⟩ := reach_live pT gT pR h hit
  by_contra! bad
  have no := blockedSound k3 3 (inputs.take 3) (by decide +kernel) k (by omega)
  exact no (convert run (fun w hw => List.mem_toFinset.mpr (sub w hw)))

end PEqualNP.Outside.L_meta_26245.TriangleBound

namespace PEqualNP.Outside.L_meta_26245.CliqueRestrictions
open PEqualNP.Outside.L_meta_26245.LiveCircuits

theorem valid (m : Nat) (hm : m ∈ masks) :
    Slice true PEqualNP.Outside.L_meta_26245.GraphTarget.cols7 PEqualNP.Outside.L_meta_26245.GraphTarget.full (cliqueDomain m) (cliqueBound m) := by
  apply validParam m hm
  have info := of_decide_eq_true (List.all_eq_true.mp facts m hm)
  unfold cliqueBound
  rw [info.1]
  exact PEqualNP.Outside.L_meta_26245.TriangleBound.standardLower3
end PEqualNP.Outside.L_meta_26245.CliqueRestrictions

namespace PEqualNP.Outside.L_meta_26245.Certificate
open PEqualNP.Outside.L_meta_26245.LiveCircuits PEqualNP.Outside.L_meta_26245.GraphTarget

abbrev Entry := Nat × List Nat × Nat × List Nat
def Entry.cap (x : Entry) : Nat := x.1
def Entry.program (x : Entry) : List Nat := x.2.1
def Entry.livingMask (x : Entry) : Nat := x.2.2.1
def Entry.codes (x : Entry) : List Nat := x.2.2.2

def unpackGates (ws : List Sig) : List Nat → List Choice
  | [] => []
  | g :: gs =>
    let c : Choice := (g / 256, ws.getD (g % 16) 0, ws.getD ((g/16) % 16) 0)
    c :: unpackGates (ws ++ [choiceVal c]) gs

def selectMask {α : Type} (m : Nat) (ws : List α) : List α :=
  (ws.zipIdx.filter fun p => m.testBit p.2).map Prod.fst

def choicesOf (e : Entry) := unpackGates cols7 e.program

def stateOf (e : Entry) : List Sig :=
  selectMask e.livingMask (cols7 ++ (choicesOf e).map choiceVal)

def negativeRows : List Row := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,18,20,22,24,26,28,30,32,33,40,41,48,56,64,68,80,84,96,112,128,129,136,137,144,152]

def candidates (r : Row) : List Sig → Sig
  | [] => full
  | w :: ws => (if bit r w then w else ~~~w) &&& candidates r ws

def indist (ws : List Sig) := negativeRows.any fun r => candidates r ws != 0

def pop (x : Nat) : Nat := (BitVec.ofNat 16 x).cpop.toNat

def readCode (e : Entry) (ws : List Sig) (a b : Sig) (d : Nat) (ka kb : Bool) : Nat :=
  let ia := ws.idxOf a
  let ib := ws.idxOf b
  let lo := min ia ib
  let hi := max ia ib
  let block := e.codes.getD (hi*(hi-1)/2+lo) 0
  let dir := ia < ib
  let slot := 4 * (if dir then d else flipOp d) +
    (if dir then ka.toNat + 2*kb.toNat else kb.toNat + 2*ka.toNat)
  if block.testBit slot then
    let rank := pop (block % (2^slot))
    (block >>> (16+20*rank)) % (2^20)
  else 0

theorem candBit (r s : Row) (ws : List Sig) :
    bit s (candidates r ws) = true ↔ bit s full = true ∧ ∀ w ∈ ws, bit r w = bit s w := by
  induction ws with
  | nil => simp [candidates]
  | cons a ws ih =>
    have ba (x y : Sig) : bit s (x &&& y) = (bit s x && bit s y) := BitVec.getLsbD_and
    have bn (x : Sig) : bit s (~~~x) = !bit s x := by
      simp only [bit,BitVec.getLsbD_not,s.isLt,decide_true,Bool.true_and]
    cases hr : bit r a <;> cases hs : bit s a <;>
      simp only [candidates,hr,Bool.false_eq_true,ite_false,ite_true,ba,bn,hs,Bool.and_eq_true,
        ih,List.forall_mem_cons] <;> simp_all

set_option maxRecDepth 8192 in
theorem indistSound {ws : List Sig} (bad : indist ws = true) (k : Nat) :
    Impossible true full k ws.toFinset := by
  obtain ⟨s,hs,hbad⟩ := List.any_eq_true.mp bad
  have hn : bit s full = false := (by decide +kernel : ∀ r ∈ negativeRows, bit r full = false) s hs
  intro l _ run
  have z : candidates s ws = 0 := by
    apply bit_ext
    intro r
    cases e : bit r (candidates s ws)
    · exact (bit_zero _).symm
    · obtain ⟨yes,all⟩ := (candBit _ _ _).mp e
      obtain ⟨w,hw,sep⟩ := live_row_difference run (show bit r full ≠ bit s full by simp [yes,hn])
      exact False.elim (sep (all w (List.mem_toFinset.mp hw)).symm)
  simp [z] at hbad
end PEqualNP.Outside.L_meta_26245.Certificate

namespace PEqualNP.Outside.L_meta_26245.GraphTarget
open PEqualNP.Outside.L_meta_26245.LiveCircuits

theorem childSwap {u : Bool} {d : Nat} (hd : allowed u d) (ws : List Sig)
    (a b : Sig) (ka kb : Bool) :
    (childTwo ws a b d ka kb).Perm (childTwo ws b a (flipOp d) kb ka) := by
  unfold childTwo
  rw [bin_flip hd a b, List.erase_comm a b]
  apply List.Perm.cons
  cases ka <;> cases kb <;> simp only [kept, Bool.false_eq_true, ↓reduceIte]
  all_goals first | exact List.Perm.refl _ | exact List.Perm.swap _ _ _

theorem enumStepOrdered {u} {T : Sig} {cap : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (twoStep : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d, allowed u d → ∀ ka kb, a.toNat < b.toNat → bin d a b ∉ ws →
      proper (bin d a b) → (childTwo ws a b d ka kb).length ≤ cap →
      Impossible u T (cap-1) (childTwo ws a b d ka kb).toFinset) :
    Impossible u T cap ws.toFinset := by
  apply enum_step hn out
  intro a ha b hb d hd ka kb ne fresh pr sz
  rcases lt_or_gt_of_ne (fun eq => ne (BitVec.toNat_inj.mp eq)) with lt | gt
  · exact twoStep a ha b hb d hd ka kb lt fresh pr sz
  · have eq := bin_flip hd a b
    have perm := childSwap hd ws a b ka kb
    have hs := twoStep b hb a ha (flipOp d) (flip_flip hd).1 kb ka gt
      (eq ▸ fresh) (eq ▸ pr) (perm.length_eq ▸ sz)
    have eqSet : (childTwo ws a b d ka kb).toFinset = (childTwo ws b a (flipOp d) kb ka).toFinset := by
      ext x
      simpa only [List.mem_toFinset] using (perm.mem_iff : x ∈ _ ↔ x ∈ _)
    exact eqSet.symm ▸ hs

end PEqualNP.Outside.L_meta_26245.GraphTarget

namespace PEqualNP.Outside.L_meta_26245.Certificate
open PEqualNP.Outside.L_meta_26245.LiveCircuits PEqualNP.Outside.L_meta_26245.GraphTarget PEqualNP.Outside.L_meta_26245.CliqueRestrictions PEqualNP.Outside.L_meta_26245.GraphSymmetry

def verifyCut (cap : Nat) (cs : List Choice) (ch : List Sig) (code : Nat) : Bool :=
  let m := (code-1)/256
  let witness := selectMask ((code-1) % 256) cs
  let mask := cliqueDomain m
  masks.contains m &&
    match makePool true mask cols7 witness with
    | none => false
    | some pool => poolCut true mask (cliqueBound m) cap witness.length pool ch

def verifyIso (db : Array Entry) (cap : Nat) (ch : List Sig) (code : Nat) : Bool :=
  let key := code-65536
  let j := key/1
  let p : Fin 1 := Fin.ofNat 1 (key % 1)
  let dest := db[j]?.getD default
  decide (j < db.size) && (dest.cap==cap) &&
    decide ((ch.map (permWord p)).toFinset = (stateOf dest).toFinset)

def verifyChild (db : Array Entry) (e : Entry) (steps : List Choice) (ws : List Sig)
    (a b : Sig) (d : Nat) (ka kb : Bool) : Bool :=
  let y := bin d a b
  let ch := childTwo ws a b d ka kb
  if b.toNat ≤ a.toNat then true else
  if a == b || ws.contains y || y == zero || y == one || decide (e.cap < ch.length) then true
  else if indist ch then true
  else
    let code := readCode e ws a b d ka kb
    if code==0 then false else if 65536 ≤ code then verifyIso db (e.cap-1) ch code
      else verifyCut (e.cap-1) (steps++[(d,a,b)]) ch code

def verify (db : Array Entry) (e : Entry) : Bool :=
  let ws := stateOf e
  let cs := choicesOf e
  decide (0 < e.cap) && decide ws.Nodup && !ws.contains full &&
    ws.all fun a => ws.all fun b => [0,1,2,3].all fun d =>
      [false,true].all fun ka => [false,true].all fun kb => verifyChild db e cs ws a b d ka kb
end PEqualNP.Outside.L_meta_26245.Certificate

namespace PEqualNP.Outside.L_meta_26245.Certificate
def n0 : Entry := ⟨10, [], 255, [0xa4010a2010a4010a2018888,0xa2010a2010a2010a2018888,0xa201100840a4011006c1002f0a201a8a8,0xa2011000a0a2010a201100010a201a8a8,0xa201100910a4010a401100860a201a8a8,0xa2010a2010a2010a2018888,0xa2010a2011001a0a2010a2011000c8a8a,0xa2010a4010a4010a2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xc2010a2010c2010a2018888,0xc2010a401100930a4018888,0xc2010a2010c2010a2018888,0xc2010a2010c2010a2018888,0xc2010a2010c2010a2018888,0xa2010a2010a2010a2018888,0xa2010a4010a4010a2018888,0xa2010a2010a2010a2018888,0xa201100c60a2010a2010a201100c1c88c,0xa2010a201100fe0a201100f80a2018cc8,0xa2010c201101080a2018888,0x100270a2011001c0a2018888,0x100ae0a401100a30a4018888,0x100bb0a201100b70a2018888,0x100f70a201100f5100f3100cc0a2018cc8,0x101010a201100ff0a2018888,0x101260c2011011e0c2018888,0x101320a2011012d0a2018888]⟩
def n1 : Entry := ⟨9, [304], 503, [0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2010a4010a201a8a8,0xa2010a2010a2010a2010a2010a2010a2010a20110002ca8f,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa4010a4010a4010a4018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2010a2010a2018cc8,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2010a2010a2018cc8,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa4010a4010a4010a4018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xc2010c2010c2010c2018888,0xa2010a2010a2010a2018888,0xa2010a2010a201e000,0xa2010a2010a2010a2010a4010a201a8a8,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2010a2010a201c88c,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2010a2010a2018a8a,0xa2010a2010a2010a201100070a201a8a8]⟩
def n2 : Entry := ⟨8, [304,64], 998, [0xa2010a2010a2010a2010a4010a201a8a8,0xa4010a4010a4010a4018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa4010a4010a4010a4018888,0xa2010a2010a2010a2018888,0xc2010c2010c2010c2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2010a4010a201a8a8,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2010a2010a2018a8a,0xa2010a2010a2010a201100030a201a8a8,0xa2010a2010a2010a2010a2010a2018cc8,0xa2010a2010a2010a2010a2010a2018cc8,0xa2010a2010a2010a2010a2010a2018cc8,0xa2010a2010a2010a2010a2010a2010a201100060a201acf8,0xa2010a2010a2010a2010a2010a2018cc8,0xa2010a2010a2010e00]⟩
def n3 : Entry := ⟨7, [304,64,376], 1766, [0xa2010a4012020,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa2010a2012020,0xa2010a2010440,0xa2010a2010440,0xa2010a2010440,0xa2010a2010a2010a201100042470,0xa2010a2010440,0xa4010a4012020,0x0,0x0,0xa2010a2010202,0xa2010a2016000,0x100050a2016000]⟩
def n4 : Entry := ⟨6, [304,64,376,361], 3238, [0xa2010a4012020,0x0,0x0,0x0,0x0,0x0,0xa4010a4012020,0x0,0x0,0xa2010a2016000,0x0,0x0,0x0,0xa2010a2010440,0xa2010a2014004]⟩
def n5 : Entry := ⟨6, [304,64,376,937], 3302, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n6 : Entry := ⟨7, [304,64,361], 1446, [0xa2010a2010a2010a2010a4010a201a8a8,0xa4010a4010a4010a4018888,0xa2010a2010a2010a2018888,0xa4010a4010a4010a4018888,0xa2010a2010a2010a2018888,0xc2010c2010c2010c2018888,0xa2010a2010a2010a2010a4010a201a8a8,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a201100040a201a8a8,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2010a2010a201c88c]⟩
def n7 : Entry := ⟨8, [304,376], 759, [0x0,0x0,0xa2010a4012020,0xa2010a2010a2010a201100034207,0x0,0x0,0x0,0x0,0x0,0x0,0xa2010a2010440,0x0,0x0,0xa2010a2010440,0x0,0x0,0x0,0x0,0x0,0x0,0xa2010a2012020,0x100080a2016000,0xa4010a4012020,0x0,0x100090a2014004,0x0,0xa2010a2010202,0xa2010a2016000]⟩
def n8 : Entry := ⟨7, [304,376,912], 1782, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa2010100,0x0,0x0,0x0,0x0]⟩
def n9 : Entry := ⟨7, [304,376,916], 1767, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa2010100,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n10 : Entry := ⟨9, [816], 503, [0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2010a4010a201a8a8,0xa2010a2010a2010a2010a2010a2018a8a,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa4010a4010a4010a4018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2010a2010a2018cc8,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa4010a4010a4010a4018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xc2010c2010c2010c2018888,0xa2010a2010a2010a2018888,0xa2010a2010a20100e0,0xa2010a2010a2010a2010a4010a201a8a8,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2010a2010a2018cc8,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2010a2010a2018a8a,0xa2010a2010a2010a2011000b0a201a8a8]⟩
def n11 : Entry := ⟨8, [816,376], 759, [0x0,0x0,0xa2010a4012020,0xa2010a2010202,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa2010a2010440,0x0,0xa2010a2012020,0x0,0x0,0x0,0x0,0xa2010a2012020,0xa2010a2012020,0xa4010a4012020,0x0,0x0,0x0,0xa2010a2010202,0xa2010a2016000]⟩
def n12 : Entry := ⟨9, [64], 495, [0xa2010a2010a2010a2010a4010a2018cc8,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2010a4010a201a8a8,0xa2010a2010a2010a2010a2010a2010a201100020a201acf8,0xa2010a2010a2010a2010a4010a201a8a8,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa4010a4010a4010a4018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2010a2010a201c88c,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2010a2010a201c88c,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2011000d0a2018cc8,0xa4010a4010a4010a4018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a201100150a2018cc8,0xc2010c2010c2010c2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010e00,0xa2010a2010a2010a2010a2010a2018cc8,0xa2010a2010a2010a2010a2010a2018cc8,0xa2010a2010a2010a2010a2010a2018cc8,0xa2010a2010a2010a2010a2010a2018cc8,0xa2010a2010a2010a2010a2010a2010a201100190a201acf8,0xa2010a2010a2010a2010a2010a2018cc8]⟩
def n13 : Entry := ⟨8, [64,368], 1006, [0xa2010a4012020,0xa2010a4012020,0x0,0x0,0x0,0x0,0x0,0x0,0xa2010a2014004,0x0,0x0,0x0,0xa2011000e0440,0x0,0xa2010a2012020,0xa2010a2010440,0xa2010a2010440,0xa2010a2010440,0xa2010a2010440,0xa2010a2010a2010a201100132470,0xa2010a2010440,0xa4010a4012020,0x0,0xa2010a201100100a201100032470,0x0,0xa2010a2010202,0xa2010a2016000,0x100140a2016000]⟩
def n14 : Entry := ⟨7, [64,368,371], 2022, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1000f0010,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa2010010]⟩
def n15 : Entry := ⟨6, [64,368,371,360], 3750, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa2010010,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n16 : Entry := ⟨7, [64,368,403], 2022, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x100110010,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa2011000,0x100121000,0x0]⟩
def n17 : Entry := ⟨6, [64,368,403,360], 3750, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa2011000,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n18 : Entry := ⟨6, [64,368,403,936], 2790, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n19 : Entry := ⟨7, [64,368,360], 1710, [0xa2010a4012020,0xa2010a4012020,0x0,0x0,0x0,0x0,0x0,0x0,0xa2011000f0440,0x0,0xa4010a4012020,0x0,0xa2010a201100110a201100042470,0x0,0xa2010a2016000,0x0,0x0,0xa2010a2014004,0x0,0xa2010a2010440,0xa2010a2014004]⟩
def n20 : Entry := ⟨7, [64,368,920], 1774, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n21 : Entry := ⟨8, [64,371], 999, [0xa2010a4010440,0x0,0xa2010a4012020,0x0,0x0,0x0,0xa2010a2014004,0x0,0x0,0x0,0xa2011000e0440,0x0,0x0,0x0,0xa2010a2012020,0xa2010a2010600,0xa2010a2010440,0xa2010a2010440,0xa2010a2010440,0xa2010a2010a2010a201100182470,0xa2010a2010440,0xa2010a201100160a201100032470,0xa4010a4012020,0x0,0x0,0xa2010a2010202,0xa2010a2016000,0xa2010a2012020]⟩
def n22 : Entry := ⟨7, [64,371,400], 2022, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x100170010,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa2011000,0x0,0x0]⟩
def n23 : Entry := ⟨6, [64,371,400,360], 3750, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa2011000,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n24 : Entry := ⟨7, [64,371,360], 1703, [0xa2010a4010440,0x0,0xa2010a4012020,0x0,0x0,0x0,0xa2011000f0440,0x0,0x0,0x0,0xa2010a201100170a201100042470,0xa4010a4012020,0x0,0x0,0xa2010a2016000,0xa2010a2014004,0x0,0x0,0x0,0xa2010a2010440,0xa2010a2014004]⟩
def n25 : Entry := ⟨8, [64,360], 687, [0xa2010a2010a2010a2010a4010a2018cc8,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2010a4010a201a8a8,0xa2010a2010a2010a2010a2010a2010a201100060a201acf8,0xa2010a2010a2010a2010a4010a201a8a8,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa4010a4010a4010a4018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a201100130a2018cc8,0xa4010a4010a4010a4018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a201100180a2018cc8,0xc2010c2010c2010c2018888,0xa2010a2010a2010a2010a2010a201c88c,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2010a2010a201c88c,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888]⟩
def n26 : Entry := ⟨9, [576], 495, [0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2010a4010a201a8a8,0xa2010a2010a2010a2010a2010a201a8a8,0xa2010a2010a2010a2010a4010a201a8a8,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa4010a4010a4010a4018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2010a2010a201c88c,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa4010a4010a4010a4018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2011001b0a2018cc8,0xc2010c2010c2010c2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010e00,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2010a2010a2018cc8,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2010a2010a201a8a8,0xa2010a2010a2010a2018888]⟩
def n27 : Entry := ⟨8, [576,371], 999, [0x0,0x0,0xa2010a4012020,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa2010a2012020,0xa2010a2010600,0x0,0x0,0x0,0xa2010a2012020,0x0,0xa2010a2012020,0xa4010a4012020,0x0,0x0,0xa2010a2010202,0xa2010a2016000,0xa2010a2012020]⟩
def n28 : Entry := ⟨9, [368], 511, [0xa2010a4010440,0xa2010a2010440,0xa2010a4012020,0xa2010a2012020,0xa2010a4012020,0x0,0xa2010a2010a2010a2011000d4207,0x0,0x0,0x0,0xa2010c2010440,0x0,0x0,0x0,0x0,0xa2010a2010440,0x0,0x0,0xa2010a2014004,0xa2010a2010440,0x0,0x1001d0a2010a2010a2014206,0x0,0x0,0xa2011001e0440,0xa2010a2012020,0x0,0xa2010a2012020,0x1001d0a2016000,0xa4010a4010a4010a4012222,0xa2010a2010a2010a2012222,0xa2010a2010a2010a201100210a201100070a2012772,0x100260a201100230a2010a2010a2010a2010a2017227,0xc2010c2010c2010c2012222,0xa2010a2010a2010a2012222,0xa2010a2016000]⟩
def n29 : Entry := ⟨8, [368,880], 1022, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa2010100,0x0,0x0,0x0,0xa2010100]⟩
def n30 : Entry := ⟨8, [368,371], 1015, [0x0,0x0,0x0,0x1000e0001,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x100200a2011001,0x0,0x0,0x0,0x1001f1000,0x0,0x0,0x0,0x0,0x0,0x0,0xa2010a2011010]⟩
def n31 : Entry := ⟨7, [368,371,912], 1526, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n32 : Entry := ⟨7, [368,371,900], 1767, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n33 : Entry := ⟨8, [368,387], 1015, [0x0,0x0,0x0,0x100100001,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x100220a2011001,0x0,0x0,0x0,0x1001f1000,0x0,0x0,0x0,0x0,0x0,0xa2011000,0xa2011000]⟩
def n34 : Entry := ⟨7, [368,387,900], 1767, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa2010100,0x0,0x0,0x0,0x0,0x0,0xa2010100]⟩
def n35 : Entry := ⟨8, [368,900], 751, [0x0,0x0,0xa2010a4012020,0xa2010a2012020,0xa2010a4012020,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa2010a2014004,0x0,0x0,0x0,0x0,0xa201100200440,0x0,0x0,0xa2010a201100240a2010642,0x0,0x0,0xa201100250440,0x0,0xa2010a2012020,0x0]⟩
def n36 : Entry := ⟨7, [368,900,265], 1774, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n37 : Entry := ⟨7, [368,900,313], 1767, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa2010100,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n38 : Entry := ⟨8, [368,900], 1007, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa201100220110,0x0,0x0,0x0,0xa2010100,0x0,0x0,0x0,0x0,0x0,0x0,0xa2010100]⟩
def n39 : Entry := ⟨9, [880], 511, [0x0,0x0,0xa2010a4012020,0xa2010a2012020,0xa2010a4012020,0x0,0xa2010a2010202,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa2010a2014004,0xa2010a2010440,0x0,0xa2010a2011001d0a2010642,0x0,0x0,0xa201100280440,0xa2010a2012020,0x0,0xa2010a2012020,0x1001d0a2010060,0xa4010a4010a4010a4012222,0xa2010a2010a2010a2012222,0xa2010a2010a2010a2011002b0a2011002a0a2012772,0xa2010a2010a2010a2011002e0a2011002d0a2012772,0xc2010c2010c2010c2012222,0xa2010a2010a2010a2012222,0xa2010a2010600]⟩
def n40 : Entry := ⟨8, [880,371], 1015, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa201100290110,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa2011000]⟩
def n41 : Entry := ⟨7, [880,371,328], 1767, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n42 : Entry := ⟨8, [880,312], 759, [0x0,0x0,0xa2010a4012020,0xa2010a2010202,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa2010a2010440,0x0,0x0,0x0,0x0,0x0,0x0,0xa2010a2012020,0xa2010a2012020,0xa4010a4012020,0x0,0x0,0x0,0xa2010a2010202,0xa2010a2012020]⟩
def n43 : Entry := ⟨8, [880,312], 1015, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa2011002c0110,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa2011000]⟩
def n44 : Entry := ⟨7, [880,312,328], 1767, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n45 : Entry := ⟨8, [880,328], 751, [0x0,0x0,0xa2010a4012020,0xa2010a2012020,0xa2010a4012020,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa2010a2014004,0x0,0x0,0x0,0x0,0xa201100290440,0x0,0x0,0xa2010a2010202,0x0,0x0,0x0,0x0,0xa2010a2012020,0x0]⟩
def n46 : Entry := ⟨8, [880,328], 1007, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa2011002c0110,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa2011000]⟩
def n47 : Entry := ⟨9, [289], 507, [0xa4010a4010a2010a4010a4010a201a8a8,0xa2010a4010a2010a2010a4010a201a8a8,0xa2010a4010a4010a4010a4010a4010a401100300a201acf8,0xa2010a2010a4010a2010a2010a4018a8a,0xa2010a4010a4010a2018888,0xa2010a2010a2010a2018888,0xa4010a2010a4010a2018888,0xa4010a4010a4010a401100430a4018cc8,0xa4010a2010a4010a2018888,0xa4010a2010a4010a2018888,0xa2010a2010a2010a2018888,0xa2010a2010a4010a4010a2010a201c88c,0xa2010a4010a2010a2010a2010a401c88c,0xa2010a2010a4010a2010a4010a2018cc8,0xa2010a4010a4010a2018888,0xa4010a2010a4010a2018888,0xa4010a4010a4010a401100490a4018cc8,0xa4010a2010a4010a401100550a2018cc8,0xa4010a2010a4010a2018888,0x1005a0c201100570c2018888,0xa4010a2010a4010a2018888,0xa4010a2010a4010a2018888,0xa2010a2010a201e000,0xa4010a2010a4010a2018888,0xa4010a2010a4010a2018888,0x1005e0c2011005d0c2018888,0xa4010a2010a4010a2018888,0x1006810069100651005f8888]⟩
def n48 : Entry := ⟨8, [289,305], 1009, [0xa2010a2010a4010a2010a2010a4018a8a,0xa4010a2010a4010a2018888,0xa4010a2010a4010a2018888,0xa2010a2010a2010a2018888,0xa2010a2010a4010a2010a4010a2018cc8,0xa2010a4010a4010a2018888,0xa4010a2010a4010a2018888,0xa4010a2010a4010a2018888,0x100340c201100310c2018888,0xa4010a2010a4010a2018888,0xa4010a2010a4010a2018888,0xa4010a2010a4010a2018888,0x100370c201100360c2018888,0xa4010a2010a4010a2018888,0x1003f100401003d100388888,0xa4010a4010a2010a4010a4010a201a8a8,0xa4010a2010a4010a2018888,0xa4010a4010a4010a4018888,0xa4010a2010a2010a4010a2010a2018a8a,0xa4010a4010a4010a401100420a401a8a8,0xa2010a2010a4010a4018888]⟩
def n49 : Entry := ⟨7, [289,305,373], 2033, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x10033100321001,0x0]⟩
def n50 : Entry := ⟨6, [289,305,373,168], 2801, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n51 : Entry := ⟨6, [289,305,373,936], 2801, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n52 : Entry := ⟨7, [289,305,885], 2033, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa401100350110]⟩
def n53 : Entry := ⟨6, [289,305,885,410], 2545, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n54 : Entry := ⟨7, [289,305,344], 2033, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xc2010001,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n55 : Entry := ⟨7, [289,305,600], 2033, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n56 : Entry := ⟨7, [289,305,120], 2033, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa201100390110,0xa2011003a0110,0xc2011003b0110,0xa2011003c0110,0x0,0x0,0xa4010a2010110]⟩
def n57 : Entry := ⟨6, [289,305,120,416], 3056, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n58 : Entry := ⟨6, [289,305,120,330], 3041, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n59 : Entry := ⟨6, [289,305,120,346], 3025, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n60 : Entry := ⟨6, [289,305,120,362], 2993, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n61 : Entry := ⟨7, [289,305,376], 2033, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1003e0c2011001,0x0,0x0,0x0,0x0]⟩
def n62 : Entry := ⟨6, [289,305,376,933], 3025, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n63 : Entry := ⟨7, [289,305,632], 2033, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n64 : Entry := ⟨7, [289,305,888], 2033, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa201100410110]⟩
def n65 : Entry := ⟨6, [289,305,888,410], 2545, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n66 : Entry := ⟨7, [289,305,377], 1521, [0xa4010a4010202,0x0,0x0,0x0,0xa4010a4010440,0x0,0x0,0x0,0x0,0xa4010a4012020,0x0,0x0,0x0,0x0,0x0,0xa4010a4012020,0x0,0x0,0xa2010a2010202,0xa4010a4016000,0x0]⟩
def n67 : Entry := ⟨8, [289,337], 1017, [0xa4010a4012020,0xa4010a4010202,0x0,0x0,0x0,0x0,0x0,0xa4010a4014004,0xa4010a4010440,0xa4010a4010440,0x0,0xa401100440440,0x0,0xc201100450440,0x0,0x0,0x0,0x0,0x100460c2014004,0x0,0x0,0xa4010a4012020,0xa4010a4012020,0x0,0xa4010a4016000,0xa2010a2010202,0x10048100472020,0xa2010a2010202]⟩
def n68 : Entry := ⟨7, [289,337,371], 2033, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n69 : Entry := ⟨7, [289,337,373], 2009, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n70 : Entry := ⟨7, [289,337,600], 2009, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n71 : Entry := ⟨7, [289,337,377], 1529, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa2010001]⟩
def n72 : Entry := ⟨7, [289,337,633], 1529, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n73 : Entry := ⟨8, [289,369], 1017, [0xa4010a4012020,0xa4010a4010202,0x0,0x0,0x0,0x0,0x0,0xa4010a4014004,0xa4010a4010440,0x0,0x0,0xa4011004a0440,0x0,0x1004e1004c2020,0xa4010a4012020,0x0,0x0,0x0,0x0,0x0,0x10054100514004,0xa4010a4012020,0xa4010a4011004b0a401100422470,0x0,0x1004f100472020,0xa2010a2010202,0xa4010a4016000,0xa2010a2010202]⟩
def n74 : Entry := ⟨7, [289,369,371], 2033, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa4010010]⟩
def n75 : Entry := ⟨7, [289,369,403], 2033, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa4011000,0x0,0x0]⟩
def n76 : Entry := ⟨7, [289,369,373], 1913, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1004d0001,0x0]⟩
def n77 : Entry := ⟨6, [289,369,373,168], 2681, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n78 : Entry := ⟨7, [289,369,885], 1913, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n79 : Entry := ⟨7, [289,369,917], 1529, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x100500010,0x0,0x0,0x0,0x0,0x0]⟩
def n80 : Entry := ⟨6, [289,369,917,314], 2545, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n81 : Entry := ⟨7, [289,369,120], 1913, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x100520010,0x100530010,0x0,0x0]⟩
def n82 : Entry := ⟨6, [289,369,120,346], 2905, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n83 : Entry := ⟨6, [289,369,120,362], 2873, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n84 : Entry := ⟨7, [289,369,632], 1913, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n85 : Entry := ⟨8, [289,371], 1011, [0xa4010a4012020,0xa4010a4010202,0x0,0x0,0xa401100440440,0x0,0x0,0xa2010a2014004,0xa4010a4010440,0x0,0x0,0xa4011004a0440,0x0,0x0,0xa4010a4012020,0x0,0xa2010a2016000,0x0,0x0,0x0,0x0,0xa4010a4012020,0xa4010a401100560a401100422470,0x0,0x0,0xa2010a2010202,0xa2010a2016000,0x0]⟩
def n86 : Entry := ⟨7, [289,371,401], 2033, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa4011000,0x0,0x0]⟩
def n87 : Entry := ⟨8, [289,373], 1019, [0x0,0x0,0x100310010,0x0,0x0,0x0,0x0,0x100450010,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1004c0010,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa401100470110,0x0,0x0,0x0,0x0,0x0,0x10059100581001]⟩
def n88 : Entry := ⟨7, [289,373,152], 1275, [0x0,0x0,0x100320010,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1004d0010,0x0,0x0,0x0,0x0,0x0,0xa2010010,0x0,0x0,0x0,0x0,0x0]⟩
def n89 : Entry := ⟨7, [289,373,920], 1275, [0x0,0x0,0x100330010,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n90 : Entry := ⟨8, [289,885], 1019, [0x0,0x0,0x100340010,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1004e0010,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa4011005b0110,0xa2011005c0110,0x0,0x0,0x0,0x0,0x0]⟩
def n91 : Entry := ⟨7, [289,885,281], 1529, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x100350010,0x0,0x0,0x0,0x0,0x0]⟩
def n92 : Entry := ⟨7, [289,885,313], 1523, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x100350010,0x0,0x0,0x0,0x0,0x0]⟩
def n93 : Entry := ⟨8, [289,344], 1019, [0x0,0x0,0x100360010,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xc2010001,0x0,0x0,0x0,0xc2011000,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n94 : Entry := ⟨8, [289,600], 1019, [0x0,0x0,0x100370010,0x0,0x0,0x0,0x0,0x100460010,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa2010a4011001,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n95 : Entry := ⟨8, [289,120], 1019, [0x0,0x0,0x100380010,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x100510010,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa201100600110,0xa4010a2010110,0xa201100610110,0xa201100620110,0xc201100630110,0xa201100640110,0x0,0x0]⟩
def n96 : Entry := ⟨7, [289,120,400], 1530, [0x100390010,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n97 : Entry := ⟨7, [289,120,313], 1523, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa2010010,0x0,0x0,0x0,0x0,0x0]⟩
def n98 : Entry := ⟨7, [289,120,329], 1515, [0x0,0x0,0x1003a0010,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n99 : Entry := ⟨7, [289,120,345], 1499, [0x0,0x0,0x1003b0010,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x100520010,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n100 : Entry := ⟨7, [289,120,361], 1467, [0x0,0x0,0x1003c0010,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x100530010,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n101 : Entry := ⟨8, [289,376], 1019, [0x0,0x0,0x1003d0010,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x100661000,0x0,0x0,0x100670c2011001,0x0,0x0,0x0]⟩
def n102 : Entry := ⟨7, [289,376,913], 1529, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n103 : Entry := ⟨7, [289,376,917], 1499, [0x0,0x0,0x1003e0010,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n104 : Entry := ⟨8, [289,632], 1019, [0x0,0x0,0x1003f0010,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x100540010,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa2010a4011001,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n105 : Entry := ⟨8, [289,888], 1019, [0x0,0x0,0x100400010,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1006a0010,0xa2011006b0110,0x0,0x0,0x0,0x0,0x0]⟩
def n106 : Entry := ⟨7, [289,888,281], 1529, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x100410010,0x0,0x0,0x0,0x0,0x0]⟩
def n107 : Entry := ⟨7, [289,888,313], 1523, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x100410010,0x0,0x0,0x0,0x0,0x0]⟩
def n108 : Entry := ⟨9, [289], 511, [0xa2010a2012020,0xa2010a2010a2010a2012222,0xa2010a2010a2010a4010a2010a2017206,0xa2010a2012020,0xa2010a2010a2010a4011006d2470,0xa2010a2010a2010a2014444,0xa2010a2010202,0x0,0xa2010a2010a2010a2014444,0x0,0x0,0xa4010c2010440,0xc2010a2010c2010a2014444,0x0,0x0,0x0,0xa2010a2014004,0xa2010a2010a2010a2014444,0xa2010a2014004,0xa2010a2010440,0x0,0x0,0xa401100710440,0x100760a201100750a2014444,0xa201100780440,0x0,0x0,0x0,0xa2010a2010a2010a2012222,0xa2010a2016000,0xa4010a2016000,0xa2010a2010a2010a2012222,0xa2010a2010a2010a2012222,0xc2010c2010c2010c2012222,0xa2010a2010a2010a2012222,0x10081100821007f100792222]⟩
def n109 : Entry := ⟨8, [289,305], 1013, [0xa2010a2010a2010a2012222,0xa2010a2010202,0xa2010a2010a2010a2014444,0x0,0xc2010a2010c2010a2014444,0x0,0x0,0xa2010a2010a2010a2014444,0xa2010a2010440,0x0,0x0,0x1006f0a2011006e0a2014444,0x0,0x0,0x0,0x0,0xa4010a2016000,0x0,0x0,0xa2010a2012020,0x0,0xa2010a2012020,0xa4010a2010a4010a2014444,0x0,0x0,0xa2010a2010202,0xa401100702020,0xa2010a2014004]⟩
def n110 : Entry := ⟨7, [289,305,370], 2033, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n111 : Entry := ⟨7, [289,305,882], 2033, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa401100410110]⟩
def n112 : Entry := ⟨7, [289,305,377], 1525, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n113 : Entry := ⟨8, [289,369], 1021, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x100720001,0x0,0xa2010100,0x100700010,0x0,0x0,0x0,0x0,0xa2010001]⟩
def n114 : Entry := ⟨7, [289,369,120], 1661, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x100730010,0x100740010,0x0]⟩
def n115 : Entry := ⟨6, [289,369,120,346], 2653, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n116 : Entry := ⟨6, [289,369,120,362], 2621, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n117 : Entry := ⟨8, [289,370], 1019, [0x0,0x0,0x1006e0010,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x100661000,0x0,0x0,0x0,0x0,0x0,0xa4010001]⟩
def n118 : Entry := ⟨8, [289,882], 1019, [0x0,0x0,0x1006f0010,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa4011006a0110,0xa201100770110,0x0,0x0,0x0,0x0,0xa4010100]⟩
def n119 : Entry := ⟨7, [289,882,313], 1523, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x100410010,0x0,0x0,0x0,0x0,0x0]⟩
def n120 : Entry := ⟨8, [289,371], 1015, [0x0,0x0,0xa2011000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x100700010,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n121 : Entry := ⟨8, [289,120], 767, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x100720010,0x0,0x0,0x0,0x0,0x0,0xa2011007a0110,0xa2010010,0xa4010010,0xa2011007b0110,0xa2011007c0110,0xc2011007d0110,0xa2011007e0110,0x0]⟩
def n122 : Entry := ⟨7, [289,120,400], 1278, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n123 : Entry := ⟨7, [289,120,313], 1271, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n124 : Entry := ⟨7, [289,120,329], 1263, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n125 : Entry := ⟨7, [289,120,345], 1247, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x100730010,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n126 : Entry := ⟨7, [289,120,361], 1215, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x100740010,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n127 : Entry := ⟨8, [289,376], 767, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x100800c2011001,0x0,0x0]⟩
def n128 : Entry := ⟨7, [289,376,917], 1247, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n129 : Entry := ⟨8, [289,632], 767, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa4010010,0x0,0x0,0x0,0x0,0x0]⟩
def n130 : Entry := ⟨8, [289,888], 767, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa201100830110,0x0,0x0,0x0,0x0]⟩
def n131 : Entry := ⟨7, [289,888,313], 1271, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n132 : Entry := ⟨9, [801], 507, [0xa2010a2010a2010a2018888,0xa2010a2010a2010a2010a2010a201a8a8,0xa2010a2010a2010a2010a4010a201a8a8,0xa2010a2010a2010a2010a2010a2018a8a,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa4010a4010a4010a4018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2010a2010a201c88c,0xa2010a2010a2010a2010a2010a2018cc8,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa4010a4010a4010a4018888,0xa2010a2010a2010a201100850a2018cc8,0xa2010a2010a2010a2018888,0xc2010c2010c2010c2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa2010a2010a40100e0,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888]⟩
def n133 : Entry := ⟨8, [801,371], 1011, [0x0,0xa2010a2010202,0x0,0x0,0x0,0x0,0x0,0x0,0xa2010a2010440,0x0,0x0,0x0,0x0,0x0,0xa2010a2012020,0x0,0xa2010a4010060,0x0,0x0,0x0,0x0,0xa2010a2012020,0xa4010a4012020,0x0,0x0,0xa2010a2010202,0xa2010a2016000,0x0]⟩
def n134 : Entry := ⟨9, [305], 503, [0xa4010a2010a4010a2018888,0xa2010a2010a2010a2018888,0xa2010a4010a4010a4010a4011006d0a401100300a201acf8,0xa2010a2010a4010a2010a2010a4018a8a,0xa2010a4010a4010a2018888,0xa2010a2010a2010a2018888,0xa4010a2010a4010a2018888,0xa4010a4010a4010a4018888,0xc2010a2010c2010a2018888,0xa4010a2010a4010a2018888,0xa2010a2010a2010a2018888,0xa2010a4010a4010a4010a4010a2018cc8,0xa2010a2010a2010a2018888,0xa2010a2010a4010a2010a4010a2018cc8,0xa2010a4010a4010a2018888,0xa4010a2010a4010a2018888,0xa4010a4010a4010a4018888,0x100880a201100870a2018888,0xa4010a2010a4010a2018888,0x1008d0c2011008a0c2018888,0xa4010a2010a4010a2018888,0xa4010a4010a2010a4010a4010a201a8a8,0xa2010a2010a201e000,0xa4010a2010a4010a2018888,0xa4010a2010a4010a2018888,0xa4010a4010a4010a4018888,0xa4010a2010a2010a4010a2010a2018a8a,0xa4010a4010a4010a4011008f0a401a8a8]⟩
def n135 : Entry := ⟨8, [305,370], 1015, [0x0,0x0,0x1006e0010,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n136 : Entry := ⟨8, [305,882], 1015, [0x0,0x0,0x1006f0010,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa401100890110]⟩
def n137 : Entry := ⟨7, [305,882,393], 1271, [0x0,0x0,0x100410010,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n138 : Entry := ⟨8, [305,373], 1015, [0x0,0x0,0x100310010,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1008b0a4011001,0x1008c0a2011001,0x0,0x0,0x0,0x0,0x0]⟩
def n139 : Entry := ⟨7, [305,373,913], 1525, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x100331000,0x0,0x0,0x0,0x0,0x0]⟩
def n140 : Entry := ⟨7, [305,373,914], 1523, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x100331000,0x0,0x0,0x0,0x0,0x0]⟩
def n141 : Entry := ⟨8, [305,885], 1015, [0x0,0x0,0x100340010,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa4011008e0110]⟩
def n142 : Entry := ⟨7, [305,885,393], 1271, [0x0,0x0,0x100350010,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n143 : Entry := ⟨8, [305,376], 759, [0x0,0x0,0xa4010a401100700a401100422470,0xa4010a4010202,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa4010a4010440,0x0,0xa4010a4010440,0x0,0x0,0x0,0x0,0x0,0x0,0xa4010a4012020,0xa4010a4012020,0x100900a4016000,0x0,0x0,0x0,0xa2010a2010202,0xa4010a4016000]⟩
def n144 : Entry := ⟨7, [305,376,913], 1781, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n145 : Entry := ⟨9, [817], 503, [0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2010a4010a201a8a8,0xa2010a2010a2010a2010a2010a2018a8a,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa4010a4010a4010a4018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2010a2010a2018cc8,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa4010a4010a4010a4018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xc2010c2010c2010c2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2010a2010a201a8a8,0xa2010a2010a40100e0,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2010a2010a2018a8a,0xa2010a2010a2010a201100920a201a8a8]⟩
def n146 : Entry := ⟨8, [817,376], 759, [0x0,0x0,0xa2010a4012020,0xa2010a2010202,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa2010a2010440,0x0,0x0,0xa4010a4012020,0x0,0x0,0x0,0xa2010a2012020,0xa2010a2012020,0xa4010a4012020,0x0,0x0,0x0,0xa2010a2010202,0xa2010a2016000]⟩
def n147 : Entry := ⟨9, [337], 511, [0x0,0x0,0xa4010a4010c2010a401100432470,0xa4010a4012020,0xa4010a4012020,0x0,0xa4010a4010202,0x0,0x0,0x0,0x0,0xc2010a4010a4010a4014206,0x0,0x0,0x0,0x0,0x0,0x0,0xa4010a4014004,0xa4010a4010440,0xa4010a4010440,0x0,0xa401100940440,0x0,0xa401100960440,0x0,0xc201100970440,0x0,0xa4010a2010a4010a2012222,0xc2010a4016000,0xc2010a2010c2010a2012222,0xa4010a2010a4010a2012222,0xa4010a2010a4010a2012222,0xa4010a4016000,0xa4010a2010a4010a2012222,0x100a0100a11009e100982222]⟩
def n148 : Entry := ⟨8, [337,369], 1021, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x100950010,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xc2010001]⟩
def n149 : Entry := ⟨7, [337,369,373], 1885, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n150 : Entry := ⟨8, [337,371], 1015, [0x0,0x0,0x100440010,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n151 : Entry := ⟨8, [337,373], 991, [0x0,0x0,0x100450010,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x100950010,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa4010001]⟩
def n152 : Entry := ⟨8, [337,120], 767, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa201100990110,0xc2010010,0xa2011009a0110,0xa2011009b0110,0xa2011009c0110,0xa4010010,0xa2011009d0110,0x0]⟩
def n153 : Entry := ⟨7, [337,120,400], 1278, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n154 : Entry := ⟨7, [337,120,402], 1275, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n155 : Entry := ⟨7, [337,120,403], 1271, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n156 : Entry := ⟨7, [337,120,404], 1263, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n157 : Entry := ⟨7, [337,120,361], 1215, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n158 : Entry := ⟨8, [337,376], 767, [0x0,0x0,0x100470010,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1009f0a2011001,0x0,0x0,0x0,0x0,0x0]⟩
def n159 : Entry := ⟨7, [337,376,914], 1275, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n160 : Entry := ⟨8, [337,632], 767, [0x0,0x0,0x100480010,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n161 : Entry := ⟨8, [337,888], 767, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa201100a20110,0x0,0x0,0x0,0x0]⟩
def n162 : Entry := ⟨7, [337,888,313], 1271, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n163 : Entry := ⟨9, [369], 511, [0x0,0x0,0xa4010a401100710a401100492470,0xa4010a4012020,0xa4010a4012020,0x0,0xa4010a4010202,0x0,0x0,0x0,0x0,0xa401100940440,0x0,0x0,0x0,0x0,0xa4010a4010440,0x0,0xa4010a4014004,0xa4010a4010440,0x0,0x0,0x100a40a4010a4010a4014206,0x0,0xa401100a70440,0x0,0x100ab100aa2020,0xa4010a4012020,0xa4010a2010a4010a2012222,0x100a40a4016000,0x100a50a2011007f0a2012222,0xa4010a4010a2010a201100a90a4011008f0a2012772,0xa4010a2010a4010a2012222,0x100ac0c2011009e0c2012222,0xa4010a2010a4010a2012222,0xa4010a4016000]⟩
def n164 : Entry := ⟨8, [369,881], 1021, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa2010100]⟩
def n165 : Entry := ⟨8, [369,898], 767, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa201100a60110,0x0,0x0,0x0,0x0]⟩
def n166 : Entry := ⟨7, [369,898,313], 1271, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n167 : Entry := ⟨8, [369,371], 1015, [0x0,0x0,0x1004a0010,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x100a81000,0x0,0x0,0x0,0x0,0x0,0xa2010a4011010]⟩
def n168 : Entry := ⟨7, [369,371,913], 1525, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n169 : Entry := ⟨8, [369,387], 1015, [0x0,0x0,0x1004b0010,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x100a81000,0x0,0x0,0x0,0x0,0xa4011000,0xa2011000]⟩
def n170 : Entry := ⟨8, [369,373], 895, [0x0,0x0,0x1004c0010,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x100950010,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa4010001]⟩
def n171 : Entry := ⟨8, [369,885], 895, [0x0,0x0,0x1004e0010,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n172 : Entry := ⟨8, [369,901], 767, [0x0,0x0,0x1004f0010,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa201100ad0110,0x0,0x0,0x0,0x0]⟩
def n173 : Entry := ⟨7, [369,901,313], 1271, [0x0,0x0,0x100500010,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n174 : Entry := ⟨9, [881], 511, [0x0,0x0,0xa4010a4012020,0xa4010a4012020,0xa4010a4012020,0x0,0xa4010a4010202,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa4010a4014004,0xa4010a4010440,0x0,0x0,0xa4010a401100a40a4010642,0x0,0xa401100af0440,0x0,0x100b1100b02020,0xa4010a4012020,0xa4010a2010a4010a2012222,0x100a40a4010060,0x100820a201100b20a2012222,0xa4010a4010a2010a201100b40a401100b30a2012772,0xa4010a2010a4010a2012222,0x100a10c201100b50c2012222,0xa4010a2010a4010a2012222,0xa4010a4010600]⟩
def n175 : Entry := ⟨8, [881,371], 1015, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa4011000]⟩
def n176 : Entry := ⟨8, [881,373], 895, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n177 : Entry := ⟨8, [881,885], 895, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa4010010]⟩
def n178 : Entry := ⟨8, [881,296], 767, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n179 : Entry := ⟨8, [881,312], 759, [0x0,0x0,0xa4010a4012020,0xa4010a4010202,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa4010a4010440,0x0,0x0,0x0,0x0,0x0,0x0,0xa4010a4012020,0xa4010a4012020,0xa4010a4012020,0x0,0x0,0x0,0xa2010a2010202,0xa2010a2012020]⟩
def n180 : Entry := ⟨8, [881,312], 1015, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa2011000]⟩
def n181 : Entry := ⟨8, [881,344], 767, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x100b60a2011001,0x0,0x0,0x0,0x0,0x0]⟩
def n182 : Entry := ⟨7, [881,344,914], 1275, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n183 : Entry := ⟨9, [370], 511, [0x0,0x0,0xa201100752020,0xa2010a2012020,0xa201100872020,0x0,0xa2010a2010202,0x0,0x0,0x0,0x0,0x0,0xa2010c2010440,0x0,0x0,0x0,0x0,0xa2010a2010440,0xa2010a2014004,0xa2010a2010440,0x0,0x0,0x0,0x100b90a2010a2010a2014206,0xa201100ba0440,0x0,0xc2010c2012020,0x0,0xa2010a2010a2010a2012222,0x100b80a4011007f0a4012222,0x100b90a2016000,0xa2010a2010a2010a2012222,0xa2010a2010a2010a2012222,0xc2010c2010c2010c2012222,0xa2010a2010a2010a2012222,0xa2010a2016000]⟩
def n184 : Entry := ⟨8, [370,897], 767, [0x0,0x0,0x100660010,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa2010001,0x0,0x0,0x0,0x0,0x0]⟩
def n185 : Entry := ⟨8, [370,882], 1019, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa2010100]⟩
def n186 : Entry := ⟨8, [370,371], 1015, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n187 : Entry := ⟨9, [882], 511, [0x0,0x0,0xa201100762020,0xa2010a2012020,0xa201100882020,0x0,0xa2010a2010202,0x0,0x0,0x0,0x0,0x0,0xc2010a2014004,0x0,0x0,0x0,0x0,0x0,0xa2010a2014004,0xa2010a2010440,0x0,0x0,0x0,0xa2010a201100b90a2010642,0xa201100bc0440,0x0,0xc2010c2012020,0x0,0xa2010a2010a2010a2012222,0x100820a401100bd0a4012222,0x100b90a2010060,0xa2010a2010a2010a201100c00a201100be0a2012772,0xa2010a2010a2010a2012222,0xc2010c2010c2010c2012222,0xa2010a2010a2010a2012222,0xa2010a2010600]⟩
def n188 : Entry := ⟨8, [882,371], 1015, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa2011000]⟩
def n189 : Entry := ⟨8, [882,280], 767, [0x0,0x0,0x1006a0010,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa2010100,0xa201100890110,0x0,0x0,0x0,0x0]⟩
def n190 : Entry := ⟨8, [882,312], 759, [0x0,0x0,0xa201100772020,0xa2010a2010202,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa2010a2010440,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa2010a2012020,0x100bf100892020,0x0,0x0,0x0,0xa2010a2010202,0xa2010a2012020]⟩
def n191 : Entry := ⟨7, [882,312,913], 1271, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n192 : Entry := ⟨8, [882,312], 1015, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa2011000]⟩
def n193 : Entry := ⟨9, [99], 503, [0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2010a4010a201a8a8,0xa2010a2010a2010a2010a2010a2018a8a,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa4010a4010a4010a4018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2010a2010a2018cc8,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa4010a4010a4010a4018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xc2010c2010c2010c2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2010a2010a2010a201100c20a201acf8,0xa2010a2010a2010a2010a2010a2010a401100c30a201acf8,0xa2010a2010a2010a2010a2010a2018cc8,0xa2010a2010a2010a2010a2010a2018cc8,0xa2010a2010a2010a2010a2010a2018cc8,0xa2010a2010a2010e00,0xa2010a2010a2010a2010a2010a201100c5100c40a201acf8]⟩
def n194 : Entry := ⟨8, [99,384], 758, [0xa2010a2010a2010a2010a4010a201a8a8,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa4010a4010a4010a4018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2010a2010a2018cc8,0xa2010a2010a2010a2018888,0xa4010a4010a4010a4018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xc2010c2010c2010c2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2010a2010a201c88c,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888]⟩
def n195 : Entry := ⟨8, [99,385], 757, [0xa2010a2010a2010a2018888,0xa2010a2010a2010a2010a2010a2018a8a,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2010a2010a2018cc8,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xc2010c2010c2010c2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2010a4010a2018cc8,0xa2010a2010a2010a2018888,0xa4010a4010a4010a4018888,0xa2010a2010a2010a2018888,0xa4010a4010a4010a4018888]⟩
def n196 : Entry := ⟨8, [99,376], 631, [0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2010a4010a201a8a8,0xa2010a2010a2010a2010a2010a2018a8a,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa4010a4010a4010a4018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2010a2010a2018cc8,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa4010a4010a4010a4018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xc2010c2010c2010c2018888,0xa2010a2010a2010a2018888]⟩
def n197 : Entry := ⟨8, [99,376], 759, [0x0,0x0,0xa2010a4012020,0xa2010a2010202,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa2010a2010440,0x0,0xa2010a2010a2010a2012222,0xa4010a4010a4010a4012222,0xa2010a2010a2010a2012222,0xa2010a2010a2010a2012222,0xc2010c2010c2010c2012222,0xa2010a2010a2010a2012222,0xa2010a2012020,0xa4010a4012020,0x0,0x0,0x0,0xa2010a2010202,0xa2010a2016000]⟩
def n198 : Entry := ⟨9, [867], 503, [0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2010a4010a201a8a8,0xa2010a2010a2010a2010a2010a2018a8a,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa4010a4010a4010a4018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2010a2010a2018cc8,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa4010a4010a4010a4018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0x100c90c201100c70c2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2010a2010a201a8a8,0xa2010a2010a2010a2010a4010a201a8a8,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2010a2010a2018cc8,0xa2010a2010a2010a2018888,0xa2010a2010a2010e00,0xa2010a2010a2010a201100cb0a201a8a8]⟩
def n199 : Entry := ⟨8, [867,373], 1015, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x100c80a2011001,0x0,0x0,0x0,0x0,0x0]⟩
def n200 : Entry := ⟨7, [867,373,914], 1523, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n201 : Entry := ⟨8, [867,885], 1015, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa201100ca0110]⟩
def n202 : Entry := ⟨7, [867,885,393], 1271, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n203 : Entry := ⟨8, [867,376], 759, [0x0,0x0,0xa2010a4012020,0xa2010a2010202,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa2010a2010440,0x0,0xa2010a2012020,0xa4010a4012020,0x0,0x0,0x0,0xa2010a2010202,0xa2010a2012020,0xa4010a4012020,0x0,0x0,0x0,0xa2010a2010202,0xa2010a2016000]⟩
def n204 : Entry := ⟨9, [371], 503, [0xa4010a2010a4010a2018888,0xa2010a2010a2010a2018888,0xa201100850a40110078100550a201a8a8,0xa2010a2011001b0a2010a201100158a8a,0xa2010a4010a4010a2018888,0xa2010a2010a2010a2018888,0xc2010a2010c2010a2018888,0xc2010a401100960a4018888,0xc2010a2010c2010a2018888,0xc2010a2010c2010a2018888,0xa2010a2010a2010a2018888,0xa2010a4010a4010a2018888,0xa2010a2010a2010a2018888,0xa2010a201100da0a201100d80a2018cc8,0xa2010c201100e10a2018888,0x100280a2011001e0a2018888,0x100af0a401100a70a4018888,0x100bc0a201100ba0a2018888,0x100dc0a201100db0a2018888,0x100e70c201100e50c2018888,0x100f0100ef0a201100ee100eb0a201a8a8,0x100d1100cf0a201100cd100070a201a8a8,0x100d5100d40a401100d31008f0a401a8a8,0x100d70a201100d60a2018888,0x100df0a201100de0a2018888,0x100ea0c201100e80c2018888,0x100f20a2010a201100f10a2010a2018a8a,0xa2010a2010a201e000]⟩
def n205 : Entry := ⟨8, [371,384], 1015, [0x0,0x0,0x0,0x100160001,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x100081000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x100ce0a2011001,0x0,0x0,0xa2011000,0x0]⟩
def n206 : Entry := ⟨7, [371,384,916], 1511, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n207 : Entry := ⟨8, [371,896], 759, [0x0,0x0,0xa2010a4012020,0xa2010a2010202,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa2010a2010440,0x0,0xa2011001f0440,0x0,0x0,0x0,0x0,0xa2010a2012020,0x100080a2010060,0xa4010a4012020,0x0,0xa201100d00440,0x0,0xa2010a2010202,0xa2010a2012020]⟩
def n208 : Entry := ⟨7, [371,896,329], 1767, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n209 : Entry := ⟨8, [371,896], 1015, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x100080010,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa201100d20110,0x0,0x0,0x0,0x0]⟩
def n210 : Entry := ⟨7, [371,896,329], 1511, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n211 : Entry := ⟨8, [371,385], 1015, [0x0,0x0,0x100560010,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x100901000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa4011000,0x0]⟩
def n212 : Entry := ⟨8, [371,897], 759, [0x0,0x0,0xa4010a4012020,0xa4010a4010202,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa4010a4010440,0x0,0x0,0xa401100a80440,0x0,0x0,0x0,0xa4010a4012020,0xa4010a4012020,0x100900a4010060,0x0,0x0,0x0,0xa2010a2010202,0xa2010a2012020]⟩
def n213 : Entry := ⟨8, [371,897], 1015, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x100900010,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n214 : Entry := ⟨8, [371,386], 1015, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa2011000,0x0]⟩
def n215 : Entry := ⟨8, [371,898], 1015, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n216 : Entry := ⟨8, [371,356], 999, [0x0,0x0,0xa2010a4012020,0x0,0x0,0x0,0xa2010a2012020,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa2010a2012020,0xa2010a2012020,0xa4010a4012020,0x0,0x0,0xa2010a2010202,0xa2010a2016000,0xa2010a2010a2010a201100d94207,0x0,0x0,0x0,0xa2010a2016000,0x0,0xa2010a2014004]⟩
def n217 : Entry := ⟨7, [371,356,144], 1510, [0xa2010a4012020,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa2010a2012020,0xa4010a4012020,0x0,0x0,0xa2010a2010202,0xa2010a2016000,0xa2010a2010440,0xa2010a2010440,0xa2010a2010440,0xa2010a2010440,0xa2010a2010440,0xa2010a2010440]⟩
def n218 : Entry := ⟨8, [371,612], 999, [0x0,0x0,0xa2010a4012020,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa2010a2012020,0xa2010a2012020,0xa4010a4012020,0x0,0x0,0xa2010a2010202,0xa2010a2016000,0xa2010a2010202,0x0,0x0,0x0,0xa2010a2010060,0x0,0xa2010a2010440]⟩
def n219 : Entry := ⟨8, [371,372], 1015, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n220 : Entry := ⟨8, [371,884], 1015, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa201100dd0110,0x0,0x0,0x0,0x0,0x0,0x0,0xa2010100]⟩
def n221 : Entry := ⟨7, [371,884,265], 1526, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n222 : Entry := ⟨8, [371,388], 1015, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa2011000,0x0]⟩
def n223 : Entry := ⟨8, [371,900], 1015, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa201100e00110,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n224 : Entry := ⟨7, [371,900,265], 1526, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n225 : Entry := ⟨8, [371,357], 1015, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x100e20010,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x100e4100e31001]⟩
def n226 : Entry := ⟨7, [371,357,374], 1847, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n227 : Entry := ⟨7, [371,357,137], 1271, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n228 : Entry := ⟨7, [371,357,649], 1271, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n229 : Entry := ⟨8, [371,373], 1015, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xc2010001,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x100e60a2011001,0x0,0x0,0x0,0x0,0x0]⟩
def n230 : Entry := ⟨7, [371,373,914], 1523, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n231 : Entry := ⟨8, [371,885], 1015, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xc2010100]⟩
def n232 : Entry := ⟨8, [371,389], 1015, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x100e90a2011001,0x0,0x0,0x0,0xc2011000,0x0]⟩
def n233 : Entry := ⟨7, [371,389,914], 1523, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n234 : Entry := ⟨8, [371,901], 1015, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n235 : Entry := ⟨8, [371,374], 887, [0x0,0x0,0xa2010a4012020,0xa2010a2010202,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa2010a4012020,0xa2010a2012020,0xa2010a2010440,0xa201100e22020,0xa2010a2012020,0xa4010a4012020,0x0,0x0,0x0,0x100ec0a2010a2010a2014206,0x0,0x0,0x0,0x0,0x0,0x100ed0a2016000,0xa2010a2010a2010a2010a2014207]⟩
def n236 : Entry := ⟨7, [371,374,902], 1847, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n237 : Entry := ⟨7, [371,374,918], 1847, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n238 : Entry := ⟨8, [371,374], 1015, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x100ed1000,0x0,0x0,0x0,0x0,0x0,0xa2010001,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa2010a2011001]⟩
def n239 : Entry := ⟨8, [371,886], 887, [0x0,0x0,0xa2010a4012020,0xa2010a2010202,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa2010a2010440,0x0,0xa2010a2012020,0xa4010a4012020,0x0,0x0,0x0,0xa2010a2010202,0x0,0x0,0x0,0x0,0x0,0x100ed0a2010060,0xa2010a2010600]⟩
def n240 : Entry := ⟨8, [371,886], 1015, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x100ed0010,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa2010100]⟩
def n241 : Entry := ⟨8, [371,390], 1015, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa2011000,0xa2011000]⟩
def n242 : Entry := ⟨8, [371,902], 1015, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x100ec0010,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa2010a2011001,0xa2010100]⟩
def n243 : Entry := ⟨9, [371], 511, [0x0,0x0,0xa2010a4012020,0xa2010a2010a2010a2012222,0xa2010a4010a4010a2012222,0xa2010a2010a2010a2012222,0xa2010a2010202,0x0,0x0,0xa2010a2010a2010a2014444,0x0,0x0,0x0,0xc2010a2010c2010a2014444,0x0,0x0,0x0,0x0,0xa2010a2010a2010a2014444,0xa2010a2010440,0x0,0x0,0x0,0x0,0x100f40a2010a2010a2010a2010a2014706,0x0,0x0,0xa2010a2012020,0xa2010a2010a2010a2012222,0xa4010a4010a4010a4012222,0xa2010a2010a2010a2012222,0x100f40a2016000,0xa2010a2010a2010a2012222,0xc2010c2010c2010c2012222,0xa2010a2010a2010a2012222,0xa2010a2016000]⟩
def n244 : Entry := ⟨8, [371,883], 1015, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa2010100]⟩
def n245 : Entry := ⟨9, [627], 503, [0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2010a4010a201a8a8,0xa2010a2010a2010a2010a2010a2018a8a,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa4010a4010a4010a4018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2010a2010a2018cc8,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa4010a4010a4010a4018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xc2010c2010c2010c2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2010a2010a201a8a8,0xa2010a2010a2010a2010a4010a201a8a8,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2010a2010a2018a8a,0xa2010a201100f600e0]⟩
def n246 : Entry := ⟨8, [627,376], 759, [0x0,0x0,0xa2010a4012020,0xa2010a2010202,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa2010a2010440,0x0,0x0,0x0,0x0,0x0,0x0,0xa2010a2012020,0xa2010a2012020,0xa4010a4012020,0x0,0x0,0x0,0xa2010a2010202,0xa2010a2016000]⟩
def n247 : Entry := ⟨9, [883], 511, [0x0,0x0,0xa2010a4012020,0xa2010a2012020,0xa2010a4012020,0x0,0xa2010a2010202,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa2010a2014004,0xa2010a2010440,0x0,0x0,0x0,0x0,0xa2010a201100f40a2010642,0x0,0x0,0xa2010a2012020,0xa2010a2010a2010a2012222,0xa4010a4010a4010a4012222,0xa2010a2010a2010a2012222,0x100f40a201100f60070,0xa2010a2010a2010a2012222,0xc2010c2010c2010c2012222,0xa2010a2010a2010a2012222,0xa2010a2010600]⟩
def n248 : Entry := ⟨9, [356], 495, [0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2010a4010a201a8a8,0xa2010a2010a2010a2010a2010a201a8a8,0xa2010a2010a2010a2010a4010a201a8a8,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa4010a4010a4010a4018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2010a2010a201a8a8,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2010a2010a201c88c,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa4010a4010a4010a4018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a201100d80a2018cc8,0x100fc0c201100fa0c2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2010a2010a2010a2010a201100f9ca8f,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2010a2010a201c88c,0xa2010a2010a2010a2018888,0xa2010a2010a201e000,0xa2010a2010a2010a2018888]⟩
def n249 : Entry := ⟨8, [356,128], 750, [0xa2010a2010a2010a2010a4010a201a8a8,0xa2010a2010a2010a2010a4010a201a8a8,0xa2010a2010a2010a2018888,0xa4010a4010a4010a4018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2010a2010a201c88c,0xa2010a2010a2010a2018888,0xa4010a4010a4010a4018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a201100d90a2018cc8,0xc2010c2010c2010c2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2010a2010a2018cc8,0xa2010a2010a2010a2010a2010a2018cc8,0xa2010a2010a2010a2010a2010a2018cc8,0xa2010a2010a2010a2010a2010a2018cc8,0xa2010a2010a2010a2010a2010a2018cc8,0xa2010a2010a2010a2010a2010a2018cc8]⟩
def n250 : Entry := ⟨8, [356,373], 1007, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xc2010001,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x100fb0a2011001,0x0,0x0,0x0,0x0,0x0]⟩
def n251 : Entry := ⟨7, [356,373,914], 1515, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xc2010001,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n252 : Entry := ⟨8, [356,885], 1007, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xc2010001,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa201100fd0110,0x0,0x0,0x0,0x0]⟩
def n253 : Entry := ⟨7, [356,885,313], 1511, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xc2010001,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n254 : Entry := ⟨9, [612], 495, [0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2010a4010a201a8a8,0xa2010a2010a2010a2010a2010a201a8a8,0xa2010a2010a2010a2010a4010a201a8a8,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa4010a4010a4010a4018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2010a2010a201c88c,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa4010a4010a4010a4018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a201100da0a2018cc8,0xc2010c2010c2010c2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2010a2010a2018a8a,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2018888,0xa2010a2010a2010a2010a2010a2018cc8,0xa2010a2010a2010a2018888,0xa2010a2010a20100e0,0xa2010a2010a2010a2018888]⟩
def n255 : Entry := ⟨9, [372], 511, [0x0,0x0,0xa2010a4012020,0xa2010a2012020,0xa2010a4012020,0x0,0xa2010a2010202,0xa2010a4012020,0xa2010a2012020,0x0,0x0,0x0,0x0,0x0,0xa2010c2010440,0x0,0x0,0x0,0xa2010a2014004,0xa2010a2010440,0x0,0xa2010a2012020,0x0,0x0,0xa201100db0440,0x101000a2010a2010a2014206,0x0,0x0,0xa2010a2010a2010a2012222,0xa4010a4010a4010a4012222,0xa2010a2010a2010a2012222,0xa2010a2010a2010a2012222,0x101000a2016000,0xc2010c2010c2010c2012222,0xa2010a2010a2010a2012222,0xa2010a2016000]⟩
def n256 : Entry := ⟨8, [372,884], 1007, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa2010100,0x0,0x0,0x0,0x0,0x0,0x0,0xa2010100]⟩
def n257 : Entry := ⟨9, [884], 511, [0x0,0x0,0xa2010a4012020,0xa2010a2012020,0xa2010a4012020,0x0,0xa2010a2010202,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa2010a2014004,0xa2010a2010440,0x0,0xa2010a2012020,0x0,0x0,0xa201100dc0440,0xa2010a201101000a2010642,0x0,0x0,0xa2010a2010a2010a201101040a201101020a2012772,0xa4010a4010a4010a4012222,0xa2010a2010a2010a2012222,0xa2010a2010a2010a201101070a201101060a2012772,0x101000a2010060,0xc2010c2010c2010c2012222,0xa2010a2010a2010a2012222,0xa2010a2010600]⟩
def n258 : Entry := ⟨8, [884,264], 766, [0xa2010a4012020,0xa2010a4012020,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa2010a2014004,0xa2010a2010440,0x0,0x0,0x0,0xa201100dd0440,0x0,0x0,0x0,0x0,0x0,0xa201101030440,0x100240a2014004,0x0,0x0,0x0]⟩
def n259 : Entry := ⟨7, [884,264,313], 1782, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa2010001,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n260 : Entry := ⟨8, [884,264], 1022, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa201101050110,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa2011000]⟩
def n261 : Entry := ⟨7, [884,264,312], 1782, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n262 : Entry := ⟨8, [884,312], 759, [0x0,0x0,0xa2010a4012020,0xa2010a2010202,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa2010a2010440,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa2010a2012020,0xa4010a4012020,0x0,0x0,0x0,0xa2010a2010202,0xa2010a2012020]⟩
def n263 : Entry := ⟨8, [884,312], 1015, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa201101050110,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa2011000]⟩
def n264 : Entry := ⟨9, [357], 511, [0x0,0x0,0xa2010a4012020,0xa2010a2012020,0xa2010a4012020,0x0,0xa2010a2010202,0x0,0x0,0x0,0xa2010a2012020,0xa4010a4012020,0xa2010a2010202,0xa2010a2012020,0x0,0x0,0xa2010a4012020,0xa2010a2012020,0xa2010a2014004,0xa2010a2010440,0xa2010c2010a2010a2014206,0x0,0x0,0x0,0xa201100e10440,0x0,0xc2011010c0440,0xa201101100440,0xa2010a2010a2010a2012222,0xa4010a4010a4010a4012222,0xa2010a2010a2010a2012222,0x1010b0a201101090a2010a2010a2010a2010a2017227,0xa2010a2010a2010a2012222,0xa2010a2016000,0xc2010a2016000,0x1011b1011c10117101112222]⟩
def n265 : Entry := ⟨8, [357,899], 759, [0x0,0x0,0xa2010a4012020,0xa2010a2010202,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa2010a2010440,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa2010a2012020,0xa4010a4012020,0x0,0x0,0x0,0xa2010a2010202,0x100e41010a2020]⟩
def n266 : Entry := ⟨7, [357,899,377], 1271, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n267 : Entry := ⟨8, [357,899], 1015, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa2010100]⟩
def n268 : Entry := ⟨8, [357,373], 991, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1010d0001,0x0,0x0,0xa2010001,0x0,0x0,0x0,0x0,0xa2010001]⟩
def n269 : Entry := ⟨7, [357,373,120], 1631, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1010e0010,0x1010f0010,0x0,0x0,0x0,0x0]⟩
def n270 : Entry := ⟨6, [357,373,120,417], 2653, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n271 : Entry := ⟨6, [357,373,120,418], 2651, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n272 : Entry := ⟨8, [357,374], 959, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x100e20010,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xc2010001]⟩
def n273 : Entry := ⟨8, [357,120], 767, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1010d0010,0x0,0xa201101120110,0xa401101130110,0xa201101140110,0xa201101150110,0xa201101160110,0xa2010010,0xc2010010,0x0]⟩
def n274 : Entry := ⟨7, [357,120,400], 1278, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n275 : Entry := ⟨7, [357,120,401], 1277, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1010e0010,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n276 : Entry := ⟨7, [357,120,402], 1275, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1010f0010,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n277 : Entry := ⟨7, [357,120,403], 1271, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n278 : Entry := ⟨7, [357,120,404], 1263, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n279 : Entry := ⟨8, [357,376], 767, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x101180a4011001,0x101190a2011001,0x1011a0a2011001,0x0,0x0,0x0,0x0]⟩
def n280 : Entry := ⟨7, [357,376,913], 1277, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n281 : Entry := ⟨7, [357,376,914], 1275, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n282 : Entry := ⟨7, [357,376,915], 1271, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n283 : Entry := ⟨8, [357,632], 767, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x100e40a2011001,0x0,0x0,0x0,0x0]⟩
def n284 : Entry := ⟨8, [357,888], 767, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa2011011d0110,0x0,0x0,0x0,0x0]⟩
def n285 : Entry := ⟨7, [357,888,313], 1271, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n286 : Entry := ⟨9, [373], 511, [0x0,0x0,0xc201100572020,0xc2010c2012020,0xc2011008a2020,0x0,0xc2010c2010202,0x0,0x0,0x0,0x0,0xc201100972020,0xc2010c2012020,0x0,0x0,0x0,0x0,0x0,0x100c70c2014004,0xc201100fa0440,0xc2011010c0440,0x0,0x100b0100aa2020,0xc2010c2012020,0xc201100e50440,0x0,0x101230c2010c2010c2014206,0x0,0xc2010a2010c2010a2012222,0x1011f0a4011009e0a4012222,0x101220c201101200a2010c2010c2010a2010a2017227,0xc2010a2010c2010a2012222,0xc2010a2010c2010a2012222,0x101230c2016000,0x101240a201101170a2012222,0xc2010c2016000]⟩
def n287 : Entry := ⟨8, [373,897], 767, [0x0,0x0,0x0,0x0,0x1008b0010,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x100590a2011001,0x0,0x0,0x0,0x0,0x0]⟩
def n288 : Entry := ⟨8, [373,898], 763, [0x0,0xc2010c2012020,0xc2011008c2020,0xc2010c2010202,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x100c80c2014004,0xc201100fb0440,0x0,0x0,0x0,0xc201100e60440,0x0,0x0,0x0,0x0,0x10059101212020,0x0,0x0,0x0,0x0,0x0]⟩
def n289 : Entry := ⟨7, [373,898,281], 1275, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n290 : Entry := ⟨8, [373,898], 1019, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa2010100]⟩
def n291 : Entry := ⟨8, [373,885], 991, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa2010100]⟩
def n292 : Entry := ⟨8, [373,902], 767, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa201101250110,0x0,0x0,0x0,0x0]⟩
def n293 : Entry := ⟨7, [373,902,313], 1271, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n294 : Entry := ⟨9, [885], 511, [0x0,0x0,0xc2011005a2020,0xc2010c2012020,0xc2011008d2020,0x0,0xc2010c2010202,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x100c90c2014004,0xc201100fc0440,0x0,0x0,0x100b1100ab2020,0xc2010c2012020,0xc201100e70440,0x0,0xc2010c201101230c2010642,0x0,0xc2010a2010c2010a2012222,0x100a10a401101270a4012222,0xc2010a2010c2010a2012222,0xc2010c2010a2010a2011012a0c201101280a2012772,0xc2010a2010c2010a2012222,0x101230c2010060,0x1011c0a2011012b0a2012222,0xc2010c2010600]⟩
def n295 : Entry := ⟨8, [885,280], 767, [0x0,0x0,0x1005b0010,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa2011008e0110,0x0,0x0,0x0,0x0]⟩
def n296 : Entry := ⟨8, [885,312], 759, [0x0,0x0,0xc2011005c2020,0xc2010c2010202,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xc201100fd0440,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xc2010c2012020,0x101291008e2020,0x0,0x0,0x0,0xa2010a2010202,0xa2010a2012020]⟩
def n297 : Entry := ⟨7, [885,312,913], 1271, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n298 : Entry := ⟨8, [885,312], 1015, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa2011000]⟩
def n299 : Entry := ⟨8, [885,360], 767, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1012c0a2011001,0x0,0x0,0x0,0x0]⟩
def n300 : Entry := ⟨7, [885,360,915], 1271, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n301 : Entry := ⟨9, [374], 511, [0x0,0x0,0xa2010a4012020,0xa2010a2012020,0xa2010a4012020,0x0,0xa2010a2010202,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa2010a4012020,0xa2010a2012020,0xa2010a2014004,0xa2010a2010440,0xa201101102020,0xa2010a2012020,0xa4010a4012020,0x0,0xa2010a201100ee0a201100eb2470,0x0,0x0,0x101310a2010a2010a2014206,0xa2010a2010a2010a2012222,0xa4010a4010a4010a4012222,0xa2010a2010a2010a2012222,0x1012f0a2011012e0a2010a2010a2010a2010a2017227,0xa2010a2010a2010a2012222,0x101300c201101170c2012222,0x101310a2016000,0xa2010a2016000]⟩
def n302 : Entry := ⟨8, [374,899], 759, [0x0,0x0,0xa2010a4012020,0xa2010a2010202,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa2010a2010440,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa2010a2012020,0xa4010a4012020,0x0,0x0,0x0,0xa2010a2010202,0xa2010a2012020]⟩
def n303 : Entry := ⟨8, [374,899], 1015, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa2011000,0xa2010100]⟩
def n304 : Entry := ⟨8, [374,901], 767, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def n305 : Entry := ⟨8, [374,886], 959, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x100ed0010,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa2010100]⟩
def n306 : Entry := ⟨9, [886], 511, [0x0,0x0,0xa2010a4012020,0xa2010a2012020,0xa2010a4012020,0x0,0xa2010a2010202,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa2010a2014004,0xa2010a2010440,0x0,0xa2010a2012020,0xa4010a4012020,0x0,0xa2010a201100f00a201100ef2470,0x0,0x0,0xa2010a201101310a2010642,0xa2010a2010a2010a2012222,0xa4010a4010a4010a4012222,0xa2010a2010a2010a2012222,0xa2010a2010a2010a201101340a201101330a2012772,0xa2010a2010a2010a2012222,0x1011c0c201101350c2012222,0x101310a2010060,0xa2010a2010600]⟩
def n307 : Entry := ⟨8, [886,312], 759, [0x0,0x0,0xa2010a4012020,0xa2010a2010202,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa2010a2010440,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa2010a2012020,0xa4010a4012020,0x0,0x0,0x0,0xa2010a2010202,0xa2010a2012020]⟩
def n308 : Entry := ⟨8, [886,312], 1015, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa2010010,0xa2011000]⟩
def n309 : Entry := ⟨8, [886,344], 767, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x101360a2011001,0x0,0x0,0x0,0x0,0x0]⟩
def n310 : Entry := ⟨7, [886,344,914], 1275, [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩
def nodes : Array Entry := #[n0,n1,n2,n3,n4,n5,n6,n7,n8,n9,n10,n11,n12,n13,n14,n15,n16,n17,n18,n19,n20,n21,n22,n23,n24,n25,n26,n27,n28,n29,n30,n31,n32,n33,n34,n35,n36,n37,n38,n39,n40,n41,n42,n43,n44,n45,n46,n47,n48,n49,n50,n51,n52,n53,n54,n55,n56,n57,n58,n59,n60,n61,n62,n63,n64,n65,n66,n67,n68,n69,n70,n71,n72,n73,n74,n75,n76,n77,n78,n79,n80,n81,n82,n83,n84,n85,n86,n87,n88,n89,n90,n91,n92,n93,n94,n95,n96,n97,n98,n99,n100,n101,n102,n103,n104,n105,n106,n107,n108,n109,n110,n111,n112,n113,n114,n115,n116,n117,n118,n119,n120,n121,n122,n123,n124,n125,n126,n127,n128,n129,n130,n131,n132,n133,n134,n135,n136,n137,n138,n139,n140,n141,n142,n143,n144,n145,n146,n147,n148,n149,n150,n151,n152,n153,n154,n155,n156,n157,n158,n159,n160,n161,n162,n163,n164,n165,n166,n167,n168,n169,n170,n171,n172,n173,n174,n175,n176,n177,n178,n179,n180,n181,n182,n183,n184,n185,n186,n187,n188,n189,n190,n191,n192,n193,n194,n195,n196,n197,n198,n199,n200,n201,n202,n203,n204,n205,n206,n207,n208,n209,n210,n211,n212,n213,n214,n215,n216,n217,n218,n219,n220,n221,n222,n223,n224,n225,n226,n227,n228,n229,n230,n231,n232,n233,n234,n235,n236,n237,n238,n239,n240,n241,n242,n243,n244,n245,n246,n247,n248,n249,n250,n251,n252,n253,n254,n255,n256,n257,n258,n259,n260,n261,n262,n263,n264,n265,n266,n267,n268,n269,n270,n271,n272,n273,n274,n275,n276,n277,n278,n279,n280,n281,n282,n283,n284,n285,n286,n287,n288,n289,n290,n291,n292,n293,n294,n295,n296,n297,n298,n299,n300,n301,n302,n303,n304,n305,n306,n307,n308,n309,n310]
end PEqualNP.Outside.L_meta_26245.Certificate

namespace PEqualNP.Outside.L_meta_26245.Certificate
open PEqualNP.Outside.L_meta_26245.LiveCircuits PEqualNP.Outside.L_meta_26245.GraphTarget PEqualNP.Outside.L_meta_26245.CliqueRestrictions PEqualNP.Outside.L_meta_26245.GraphSymmetry

theorem verifiedCut {cap cs ch code} (validSlice : ∀ m ∈ masks, Slice true cols7 full (cliqueDomain m) (cliqueBound m))
    (nd : ch.Nodup) (ok : verifyCut cap cs ch code = true) : Impossible true full cap ch.toFinset := by
  let m := (code-1)/256
  let witness := selectMask ((code-1) % 256) cs
  unfold verifyCut at ok
  simp only [Bool.and_eq_true,List.contains_iff_mem] at ok
  obtain ⟨hm,h⟩ := ok
  change (match makePool true (cliqueDomain m) cols7 witness with
    | none => false
    | some pool => poolCut true (cliqueDomain m) (cliqueBound m) cap witness.length pool ch) = true at h
  cases hp : makePool true (cliqueDomain m) cols7 witness with
  | none => rw [hp] at h; contradiction
  | some pool =>
    apply poolCut_sound (validSlice m hm) witness hp nd
    rw [hp] at h
    exact h

theorem verifiedIso {db cap ch code} (ok : verifyIso db cap ch code = true)
    (prev : ∀ j, j < db.size →
      (db[j]?.getD default).cap = cap →
      Impossible true full (db[j]?.getD default).cap (stateOf (db[j]?.getD default)).toFinset) :
    Impossible true full cap ch.toFinset := by
  let j := (code-65536)/1
  let p : Fin 1 := Fin.ofNat 1 ((code-65536) % 1)
  let dest := db[j]?.getD default
  simp only [verifyIso,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at ok
  obtain ⟨⟨hj,hcap⟩,eq⟩ := ok
  apply isoTransferOf p ch (stateOf dest) cap eq
  exact hcap ▸ prev j hj hcap

set_option maxRecDepth 8192 in
theorem nodeSound {db e}
    (slices : ∀ m ∈ masks, Slice true cols7 full (cliqueDomain m) (cliqueBound m))
    (ok : verify db e = true)
    (prev : ∀ j, j < db.size → (db[j]?.getD default).cap < e.cap →
      Impossible true full (db[j]?.getD default).cap (stateOf (db[j]?.getD default)).toFinset) :
    Impossible true full e.cap (stateOf e).toFinset := by
  let ws := stateOf e
  let cs := choicesOf e
  simp only [verify,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.all_eq_true] at ok
  obtain ⟨⟨⟨pos,nd⟩,notout⟩,all⟩ := ok
  apply enumStepOrdered nd (by simpa using notout)
  intro a ha b hb d hd ka kb lt fresh prop len
  have reverse : ¬b.toNat ≤ a.toNat := Nat.not_le.mpr lt
  have ne : a ≠ b := fun eq => (Nat.lt_irrefl _) (eq ▸ lt)
  have op : d ∈ [0,1,2,3] := by rcases allowed_four hd with h|h|h|h <;> simp_all
  have ka' : ka ∈ [false,true] := by cases ka <;> simp
  have kb' : kb ∈ [false,true] := by cases kb <;> simp
  have chk := all a ha b hb d op ka ka' kb kb'
  have nz := prop.1
  have no := prop.2
  simp only [verifyChild,beq_iff_eq,List.contains_iff_mem,Bool.or_eq_true,decide_eq_true_eq,
    reverse,ne,fresh,nz,no,Nat.not_lt.mpr len,or_self,ite_false] at chk
  split at chk
  next bad => exact indistSound bad _
  next =>
    split at chk
    next => contradiction
    next =>
      split at chk
      next =>
        have dec : e.cap-1 < e.cap := by omega
        exact verifiedIso chk (fun j hj heq => prev j hj (heq.trans_lt dec))
      next =>
        apply verifiedCut slices _ chk
        unfold childTwo kept
        have nodup := nd
        have rn : ((ws.erase a).erase b).Nodup := (nodup.erase a).erase b
        have notA : a ∉ (ws.erase a).erase b := fun h => ((nodup.mem_erase_iff).mp (List.mem_of_mem_erase h)).1 rfl
        have notB : b ∉ (ws.erase a).erase b := fun h => (((nodup.erase a).mem_erase_iff).mp h).1 rfl
        have old : ∀ x ∈ (ws.erase a).erase b, x ∈ ws := fun _ h => List.mem_of_mem_erase (List.mem_of_mem_erase h)
        have ya : bin d a b ≠ a := by intro eq; apply fresh; rw [eq]; exact ha
        have yb : bin d a b ≠ b := by intro eq; apply fresh; rw [eq]; exact hb
        have yr : bin d a b ∉ (ws.erase a).erase b := fun h => fresh (old _ h)
        change (bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))).Nodup
        cases ka <;> cases kb <;> simp [kept,ya,yb,yr,notA,notB,rn,ne]


theorem forestSound (db : Array Entry)
    (slices : ∀ m ∈ masks, Slice true cols7 full (cliqueDomain m) (cliqueBound m))
    (good : ∀ j, j < db.size → verify db (db[j]?.getD default) = true)
    (j : Nat) (hj : j < db.size) :
    Impossible true full (db[j]?.getD default).cap (stateOf (db[j]?.getD default)).toFinset := by
  suffices ∀ k i, i < db.size → (db[i]?.getD default).cap = k →
      Impossible true full (db[i]?.getD default).cap (stateOf (db[i]?.getD default)).toFinset from this _ j hj rfl
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro i hi hc
    apply nodeSound slices (good i hi)
    intro j hj lt
    exact ih _ (hc ▸ lt) j hj rfl
end PEqualNP.Outside.L_meta_26245.Certificate

namespace PEqualNP.Outside.L_meta_26245.Certificate
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok0 : verify nodes n0 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok1 : verify nodes n1 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok2 : verify nodes n2 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok3 : verify nodes n3 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok4 : verify nodes n4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok5 : verify nodes n5 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok6 : verify nodes n6 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok7 : verify nodes n7 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok8 : verify nodes n8 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok9 : verify nodes n9 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok10 : verify nodes n10 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok11 : verify nodes n11 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok12 : verify nodes n12 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok13 : verify nodes n13 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok14 : verify nodes n14 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok15 : verify nodes n15 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok16 : verify nodes n16 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok17 : verify nodes n17 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok18 : verify nodes n18 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok19 : verify nodes n19 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok20 : verify nodes n20 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok21 : verify nodes n21 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok22 : verify nodes n22 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok23 : verify nodes n23 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok24 : verify nodes n24 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok25 : verify nodes n25 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok26 : verify nodes n26 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok27 : verify nodes n27 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok28 : verify nodes n28 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok29 : verify nodes n29 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok30 : verify nodes n30 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok31 : verify nodes n31 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok32 : verify nodes n32 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok33 : verify nodes n33 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok34 : verify nodes n34 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok35 : verify nodes n35 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok36 : verify nodes n36 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok37 : verify nodes n37 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok38 : verify nodes n38 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok39 : verify nodes n39 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok40 : verify nodes n40 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok41 : verify nodes n41 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok42 : verify nodes n42 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok43 : verify nodes n43 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok44 : verify nodes n44 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok45 : verify nodes n45 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok46 : verify nodes n46 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok47 : verify nodes n47 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok48 : verify nodes n48 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok49 : verify nodes n49 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok50 : verify nodes n50 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok51 : verify nodes n51 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok52 : verify nodes n52 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok53 : verify nodes n53 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok54 : verify nodes n54 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok55 : verify nodes n55 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok56 : verify nodes n56 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok57 : verify nodes n57 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok58 : verify nodes n58 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok59 : verify nodes n59 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok60 : verify nodes n60 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok61 : verify nodes n61 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok62 : verify nodes n62 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok63 : verify nodes n63 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok64 : verify nodes n64 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok65 : verify nodes n65 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok66 : verify nodes n66 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok67 : verify nodes n67 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok68 : verify nodes n68 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok69 : verify nodes n69 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok70 : verify nodes n70 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok71 : verify nodes n71 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok72 : verify nodes n72 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok73 : verify nodes n73 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok74 : verify nodes n74 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok75 : verify nodes n75 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok76 : verify nodes n76 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok77 : verify nodes n77 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok78 : verify nodes n78 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok79 : verify nodes n79 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok80 : verify nodes n80 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok81 : verify nodes n81 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok82 : verify nodes n82 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok83 : verify nodes n83 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok84 : verify nodes n84 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok85 : verify nodes n85 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok86 : verify nodes n86 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok87 : verify nodes n87 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok88 : verify nodes n88 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok89 : verify nodes n89 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok90 : verify nodes n90 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok91 : verify nodes n91 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok92 : verify nodes n92 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok93 : verify nodes n93 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok94 : verify nodes n94 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok95 : verify nodes n95 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok96 : verify nodes n96 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok97 : verify nodes n97 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok98 : verify nodes n98 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok99 : verify nodes n99 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok100 : verify nodes n100 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok101 : verify nodes n101 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok102 : verify nodes n102 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok103 : verify nodes n103 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok104 : verify nodes n104 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok105 : verify nodes n105 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok106 : verify nodes n106 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok107 : verify nodes n107 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok108 : verify nodes n108 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok109 : verify nodes n109 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok110 : verify nodes n110 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok111 : verify nodes n111 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok112 : verify nodes n112 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok113 : verify nodes n113 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok114 : verify nodes n114 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok115 : verify nodes n115 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok116 : verify nodes n116 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok117 : verify nodes n117 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok118 : verify nodes n118 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok119 : verify nodes n119 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok120 : verify nodes n120 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok121 : verify nodes n121 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok122 : verify nodes n122 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok123 : verify nodes n123 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok124 : verify nodes n124 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok125 : verify nodes n125 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok126 : verify nodes n126 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok127 : verify nodes n127 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok128 : verify nodes n128 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok129 : verify nodes n129 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok130 : verify nodes n130 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok131 : verify nodes n131 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok132 : verify nodes n132 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok133 : verify nodes n133 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok134 : verify nodes n134 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok135 : verify nodes n135 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok136 : verify nodes n136 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok137 : verify nodes n137 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok138 : verify nodes n138 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok139 : verify nodes n139 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok140 : verify nodes n140 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok141 : verify nodes n141 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok142 : verify nodes n142 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok143 : verify nodes n143 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok144 : verify nodes n144 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok145 : verify nodes n145 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok146 : verify nodes n146 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok147 : verify nodes n147 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok148 : verify nodes n148 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok149 : verify nodes n149 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok150 : verify nodes n150 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok151 : verify nodes n151 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok152 : verify nodes n152 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok153 : verify nodes n153 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok154 : verify nodes n154 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok155 : verify nodes n155 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok156 : verify nodes n156 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok157 : verify nodes n157 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok158 : verify nodes n158 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok159 : verify nodes n159 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok160 : verify nodes n160 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok161 : verify nodes n161 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok162 : verify nodes n162 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok163 : verify nodes n163 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok164 : verify nodes n164 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok165 : verify nodes n165 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok166 : verify nodes n166 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok167 : verify nodes n167 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok168 : verify nodes n168 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok169 : verify nodes n169 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok170 : verify nodes n170 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok171 : verify nodes n171 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok172 : verify nodes n172 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok173 : verify nodes n173 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok174 : verify nodes n174 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok175 : verify nodes n175 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok176 : verify nodes n176 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok177 : verify nodes n177 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok178 : verify nodes n178 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok179 : verify nodes n179 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok180 : verify nodes n180 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok181 : verify nodes n181 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok182 : verify nodes n182 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok183 : verify nodes n183 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok184 : verify nodes n184 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok185 : verify nodes n185 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok186 : verify nodes n186 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok187 : verify nodes n187 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok188 : verify nodes n188 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok189 : verify nodes n189 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok190 : verify nodes n190 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok191 : verify nodes n191 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok192 : verify nodes n192 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok193 : verify nodes n193 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok194 : verify nodes n194 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok195 : verify nodes n195 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok196 : verify nodes n196 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok197 : verify nodes n197 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok198 : verify nodes n198 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok199 : verify nodes n199 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok200 : verify nodes n200 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok201 : verify nodes n201 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok202 : verify nodes n202 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok203 : verify nodes n203 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok204 : verify nodes n204 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok205 : verify nodes n205 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok206 : verify nodes n206 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok207 : verify nodes n207 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok208 : verify nodes n208 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok209 : verify nodes n209 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok210 : verify nodes n210 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok211 : verify nodes n211 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok212 : verify nodes n212 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok213 : verify nodes n213 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok214 : verify nodes n214 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok215 : verify nodes n215 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok216 : verify nodes n216 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok217 : verify nodes n217 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok218 : verify nodes n218 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok219 : verify nodes n219 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok220 : verify nodes n220 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok221 : verify nodes n221 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok222 : verify nodes n222 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok223 : verify nodes n223 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok224 : verify nodes n224 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok225 : verify nodes n225 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok226 : verify nodes n226 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok227 : verify nodes n227 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok228 : verify nodes n228 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok229 : verify nodes n229 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok230 : verify nodes n230 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok231 : verify nodes n231 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok232 : verify nodes n232 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok233 : verify nodes n233 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok234 : verify nodes n234 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok235 : verify nodes n235 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok236 : verify nodes n236 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok237 : verify nodes n237 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok238 : verify nodes n238 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok239 : verify nodes n239 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok240 : verify nodes n240 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok241 : verify nodes n241 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok242 : verify nodes n242 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok243 : verify nodes n243 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok244 : verify nodes n244 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok245 : verify nodes n245 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok246 : verify nodes n246 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok247 : verify nodes n247 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok248 : verify nodes n248 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok249 : verify nodes n249 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok250 : verify nodes n250 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok251 : verify nodes n251 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok252 : verify nodes n252 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok253 : verify nodes n253 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok254 : verify nodes n254 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok255 : verify nodes n255 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok256 : verify nodes n256 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok257 : verify nodes n257 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok258 : verify nodes n258 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok259 : verify nodes n259 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok260 : verify nodes n260 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok261 : verify nodes n261 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok262 : verify nodes n262 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok263 : verify nodes n263 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok264 : verify nodes n264 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok265 : verify nodes n265 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok266 : verify nodes n266 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok267 : verify nodes n267 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok268 : verify nodes n268 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok269 : verify nodes n269 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok270 : verify nodes n270 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok271 : verify nodes n271 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok272 : verify nodes n272 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok273 : verify nodes n273 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok274 : verify nodes n274 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok275 : verify nodes n275 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok276 : verify nodes n276 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok277 : verify nodes n277 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok278 : verify nodes n278 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok279 : verify nodes n279 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok280 : verify nodes n280 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok281 : verify nodes n281 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok282 : verify nodes n282 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok283 : verify nodes n283 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok284 : verify nodes n284 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok285 : verify nodes n285 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok286 : verify nodes n286 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok287 : verify nodes n287 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok288 : verify nodes n288 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok289 : verify nodes n289 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok290 : verify nodes n290 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok291 : verify nodes n291 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok292 : verify nodes n292 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok293 : verify nodes n293 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok294 : verify nodes n294 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok295 : verify nodes n295 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok296 : verify nodes n296 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok297 : verify nodes n297 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok298 : verify nodes n298 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok299 : verify nodes n299 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok300 : verify nodes n300 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok301 : verify nodes n301 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok302 : verify nodes n302 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok303 : verify nodes n303 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok304 : verify nodes n304 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok305 : verify nodes n305 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok306 : verify nodes n306 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok307 : verify nodes n307 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok308 : verify nodes n308 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok309 : verify nodes n309 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok310 : verify nodes n310 = true := by decide +kernel
end PEqualNP.Outside.L_meta_26245.Certificate

namespace PEqualNP.Outside.L_meta_26245.Certificate
open PEqualNP.Outside.L_meta_26245.LiveCircuits PEqualNP.Outside.L_meta_26245.GraphTarget
set_option maxRecDepth 200000 in
set_option maxHeartbeats 1000000000 in
theorem allChecks : ∀ j : Nat, j < nodes.size → verify nodes (nodes[j]?.getD default) = true
  | 0, _ => ok0
  | 1, _ => ok1
  | 2, _ => ok2
  | 3, _ => ok3
  | 4, _ => ok4
  | 5, _ => ok5
  | 6, _ => ok6
  | 7, _ => ok7
  | 8, _ => ok8
  | 9, _ => ok9
  | 10, _ => ok10
  | 11, _ => ok11
  | 12, _ => ok12
  | 13, _ => ok13
  | 14, _ => ok14
  | 15, _ => ok15
  | 16, _ => ok16
  | 17, _ => ok17
  | 18, _ => ok18
  | 19, _ => ok19
  | 20, _ => ok20
  | 21, _ => ok21
  | 22, _ => ok22
  | 23, _ => ok23
  | 24, _ => ok24
  | 25, _ => ok25
  | 26, _ => ok26
  | 27, _ => ok27
  | 28, _ => ok28
  | 29, _ => ok29
  | 30, _ => ok30
  | 31, _ => ok31
  | 32, _ => ok32
  | 33, _ => ok33
  | 34, _ => ok34
  | 35, _ => ok35
  | 36, _ => ok36
  | 37, _ => ok37
  | 38, _ => ok38
  | 39, _ => ok39
  | 40, _ => ok40
  | 41, _ => ok41
  | 42, _ => ok42
  | 43, _ => ok43
  | 44, _ => ok44
  | 45, _ => ok45
  | 46, _ => ok46
  | 47, _ => ok47
  | 48, _ => ok48
  | 49, _ => ok49
  | 50, _ => ok50
  | 51, _ => ok51
  | 52, _ => ok52
  | 53, _ => ok53
  | 54, _ => ok54
  | 55, _ => ok55
  | 56, _ => ok56
  | 57, _ => ok57
  | 58, _ => ok58
  | 59, _ => ok59
  | 60, _ => ok60
  | 61, _ => ok61
  | 62, _ => ok62
  | 63, _ => ok63
  | 64, _ => ok64
  | 65, _ => ok65
  | 66, _ => ok66
  | 67, _ => ok67
  | 68, _ => ok68
  | 69, _ => ok69
  | 70, _ => ok70
  | 71, _ => ok71
  | 72, _ => ok72
  | 73, _ => ok73
  | 74, _ => ok74
  | 75, _ => ok75
  | 76, _ => ok76
  | 77, _ => ok77
  | 78, _ => ok78
  | 79, _ => ok79
  | 80, _ => ok80
  | 81, _ => ok81
  | 82, _ => ok82
  | 83, _ => ok83
  | 84, _ => ok84
  | 85, _ => ok85
  | 86, _ => ok86
  | 87, _ => ok87
  | 88, _ => ok88
  | 89, _ => ok89
  | 90, _ => ok90
  | 91, _ => ok91
  | 92, _ => ok92
  | 93, _ => ok93
  | 94, _ => ok94
  | 95, _ => ok95
  | 96, _ => ok96
  | 97, _ => ok97
  | 98, _ => ok98
  | 99, _ => ok99
  | 100, _ => ok100
  | 101, _ => ok101
  | 102, _ => ok102
  | 103, _ => ok103
  | 104, _ => ok104
  | 105, _ => ok105
  | 106, _ => ok106
  | 107, _ => ok107
  | 108, _ => ok108
  | 109, _ => ok109
  | 110, _ => ok110
  | 111, _ => ok111
  | 112, _ => ok112
  | 113, _ => ok113
  | 114, _ => ok114
  | 115, _ => ok115
  | 116, _ => ok116
  | 117, _ => ok117
  | 118, _ => ok118
  | 119, _ => ok119
  | 120, _ => ok120
  | 121, _ => ok121
  | 122, _ => ok122
  | 123, _ => ok123
  | 124, _ => ok124
  | 125, _ => ok125
  | 126, _ => ok126
  | 127, _ => ok127
  | 128, _ => ok128
  | 129, _ => ok129
  | 130, _ => ok130
  | 131, _ => ok131
  | 132, _ => ok132
  | 133, _ => ok133
  | 134, _ => ok134
  | 135, _ => ok135
  | 136, _ => ok136
  | 137, _ => ok137
  | 138, _ => ok138
  | 139, _ => ok139
  | 140, _ => ok140
  | 141, _ => ok141
  | 142, _ => ok142
  | 143, _ => ok143
  | 144, _ => ok144
  | 145, _ => ok145
  | 146, _ => ok146
  | 147, _ => ok147
  | 148, _ => ok148
  | 149, _ => ok149
  | 150, _ => ok150
  | 151, _ => ok151
  | 152, _ => ok152
  | 153, _ => ok153
  | 154, _ => ok154
  | 155, _ => ok155
  | 156, _ => ok156
  | 157, _ => ok157
  | 158, _ => ok158
  | 159, _ => ok159
  | 160, _ => ok160
  | 161, _ => ok161
  | 162, _ => ok162
  | 163, _ => ok163
  | 164, _ => ok164
  | 165, _ => ok165
  | 166, _ => ok166
  | 167, _ => ok167
  | 168, _ => ok168
  | 169, _ => ok169
  | 170, _ => ok170
  | 171, _ => ok171
  | 172, _ => ok172
  | 173, _ => ok173
  | 174, _ => ok174
  | 175, _ => ok175
  | 176, _ => ok176
  | 177, _ => ok177
  | 178, _ => ok178
  | 179, _ => ok179
  | 180, _ => ok180
  | 181, _ => ok181
  | 182, _ => ok182
  | 183, _ => ok183
  | 184, _ => ok184
  | 185, _ => ok185
  | 186, _ => ok186
  | 187, _ => ok187
  | 188, _ => ok188
  | 189, _ => ok189
  | 190, _ => ok190
  | 191, _ => ok191
  | 192, _ => ok192
  | 193, _ => ok193
  | 194, _ => ok194
  | 195, _ => ok195
  | 196, _ => ok196
  | 197, _ => ok197
  | 198, _ => ok198
  | 199, _ => ok199
  | 200, _ => ok200
  | 201, _ => ok201
  | 202, _ => ok202
  | 203, _ => ok203
  | 204, _ => ok204
  | 205, _ => ok205
  | 206, _ => ok206
  | 207, _ => ok207
  | 208, _ => ok208
  | 209, _ => ok209
  | 210, _ => ok210
  | 211, _ => ok211
  | 212, _ => ok212
  | 213, _ => ok213
  | 214, _ => ok214
  | 215, _ => ok215
  | 216, _ => ok216
  | 217, _ => ok217
  | 218, _ => ok218
  | 219, _ => ok219
  | 220, _ => ok220
  | 221, _ => ok221
  | 222, _ => ok222
  | 223, _ => ok223
  | 224, _ => ok224
  | 225, _ => ok225
  | 226, _ => ok226
  | 227, _ => ok227
  | 228, _ => ok228
  | 229, _ => ok229
  | 230, _ => ok230
  | 231, _ => ok231
  | 232, _ => ok232
  | 233, _ => ok233
  | 234, _ => ok234
  | 235, _ => ok235
  | 236, _ => ok236
  | 237, _ => ok237
  | 238, _ => ok238
  | 239, _ => ok239
  | 240, _ => ok240
  | 241, _ => ok241
  | 242, _ => ok242
  | 243, _ => ok243
  | 244, _ => ok244
  | 245, _ => ok245
  | 246, _ => ok246
  | 247, _ => ok247
  | 248, _ => ok248
  | 249, _ => ok249
  | 250, _ => ok250
  | 251, _ => ok251
  | 252, _ => ok252
  | 253, _ => ok253
  | 254, _ => ok254
  | 255, _ => ok255
  | 256, _ => ok256
  | 257, _ => ok257
  | 258, _ => ok258
  | 259, _ => ok259
  | 260, _ => ok260
  | 261, _ => ok261
  | 262, _ => ok262
  | 263, _ => ok263
  | 264, _ => ok264
  | 265, _ => ok265
  | 266, _ => ok266
  | 267, _ => ok267
  | 268, _ => ok268
  | 269, _ => ok269
  | 270, _ => ok270
  | 271, _ => ok271
  | 272, _ => ok272
  | 273, _ => ok273
  | 274, _ => ok274
  | 275, _ => ok275
  | 276, _ => ok276
  | 277, _ => ok277
  | 278, _ => ok278
  | 279, _ => ok279
  | 280, _ => ok280
  | 281, _ => ok281
  | 282, _ => ok282
  | 283, _ => ok283
  | 284, _ => ok284
  | 285, _ => ok285
  | 286, _ => ok286
  | 287, _ => ok287
  | 288, _ => ok288
  | 289, _ => ok289
  | 290, _ => ok290
  | 291, _ => ok291
  | 292, _ => ok292
  | 293, _ => ok293
  | 294, _ => ok294
  | 295, _ => ok295
  | 296, _ => ok296
  | 297, _ => ok297
  | 298, _ => ok298
  | 299, _ => ok299
  | 300, _ => ok300
  | 301, _ => ok301
  | 302, _ => ok302
  | 303, _ => ok303
  | 304, _ => ok304
  | 305, _ => ok305
  | 306, _ => ok306
  | 307, _ => ok307
  | 308, _ => ok308
  | 309, _ => ok309
  | 310, _ => ok310
  | j+311,h => by change j+311 < 311 at h; omega

set_option maxRecDepth 16384 in
theorem complete : Lower true cols7 full 11 := by
  have impossible := forestSound nodes PEqualNP.Outside.L_meta_26245.CliqueRestrictions.valid allChecks 0 (by decide +kernel)
  have home : stateOf n0 = cols7 := by decide +kernel
  change Impossible true full 10 (stateOf n0).toFinset at impossible
  rw [home] at impossible
  let xs : List (Sig × Row × Row) := [
    (cols7.getD 0 zero,16,17),
    (cols7.getD 1 zero,32,34),
    (cols7.getD 2 zero,32,36),
    (cols7.getD 3 zero,64,72),
    (cols7.getD 4 zero,1,17),
    (cols7.getD 5 zero,2,34),
    (cols7.getD 6 zero,1,65),
    (cols7.getD 7 zero,2,130)]
  have er := essential_ok (T:=full) (raw:=cols7) (xs:=xs) (by decide +kernel)
  have eq : (xs.map Prod.fst).toFinset = cols7.toFinset := by decide +kernel
  rw [eq] at er
  exact lower_impossible (by unfold proper; decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun a h => er a (List.mem_toFinset.mpr h)) impossible
end PEqualNP.Outside.L_meta_26245.Certificate


theorem PEqualNP.Outside.L_meta_26245 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 1, 7, 2, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 1, 7, 2, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 1, 7, 2, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 1, 7, 2, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 1, 7, 2, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 1, 7, 2, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) :=
  PEqualNP.Outside.L_meta_26245.GraphTarget.finish PEqualNP.Outside.L_meta_26245.Certificate.complete

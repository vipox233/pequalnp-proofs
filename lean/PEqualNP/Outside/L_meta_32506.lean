import PEqualNP.Defs

-- The two-mode live-state and cofactor checker follows L_meta_1674 and L_meta_670.
-- The graph, restrictions and all search certificates below are for L_meta_32506.

-- Shared forest and cofactor certificates from L_meta_1674 and PR 11111 for L_meta_1677.
-- The original credit line is retained below. The two root certificates here cover the unpinned graph.

-- The checker and the bound certificates are adapted from PEqualNP/Outside/L_meta_1667.lean (Apache-2.0).
-- Two modes: u=false are monotone runs (AND, OR); u=true are runs up to complement, where negation is free.
namespace PEqualNP.Outside.L_meta_32506
open PEqualNP.CircuitLowerBounds
private def word80 (xs : List Nat) : Nat :=
  xs.foldl (fun a b => (a <<< 80) ||| b) 0

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

def inputs : List Sig := [(BitVec.ofNat 512 (word80 [0xaaaaaaaa,0xaaaaaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaaaaaa])),(BitVec.ofNat 512 (word80 [0xcccccccc,0xcccccccccccccccccccc,0xcccccccccccccccccccc,0xcccccccccccccccccccc,0xcccccccccccccccccccc,0xcccccccccccccccccccc,0xcccccccccccccccccccc])),(BitVec.ofNat 512 (word80 [0xf0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0])),(BitVec.ofNat 512 (word80 [0xff00ff00,0xff00ff00ff00ff00ff00,0xff00ff00ff00ff00ff00,0xff00ff00ff00ff00ff00,0xff00ff00ff00ff00ff00,0xff00ff00ff00ff00ff00,0xff00ff00ff00ff00ff00])),(BitVec.ofNat 512 (word80 [0xffff0000,0xffff0000ffff0000ffff,0xffff0000ffff0000,0xffff0000ffff0000ffff,0xffff0000ffff0000,0xffff0000ffff0000ffff,0xffff0000ffff0000])),(BitVec.ofNat 512 (word80 [0xffffffff,0xffffffff0000,0xffffffff00000000,0xffffffff00000000ffff,0xffff00000000ffffffff,0xffffffff0000,0xffffffff00000000])),(BitVec.ofNat 512 (word80 [0xffffffff,0xffffffff000000000000,0xffffffffffffffff,0xffff,0xffffffffffff00000000,0xffffffffffff,0xffff0000000000000000])),(BitVec.ofNat 512 (word80 [0xffffffff,0xffffffffffffffffffff,0xffff0000000000000000,0xffff,0xffffffffffffffffffff,0xffffffff000000000000,0])),(BitVec.ofNat 512 (word80 [0xffffffff,0xffffffffffffffffffff,0xffffffffffffffffffff,0xffffffffffffffff0000,0,0,0]))]
def graph : Sig := (BitVec.ofNat 512 (word80 [0xffffffff,0xfffffffffffffffeffff,0xfffefffffffffffefffc,0xfffefffaeeeeaa00ffff,0xfffffffffffffffffffe,0xfffffffefffffffffffe,0xfffcfffefffaeeeeaa00]))
def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 4) || (x 0 && x 5) || (x 2 && x 5) || (x 3 && x 5) || (x 1 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 5 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 2 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 6 && x 7)
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
  (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 2 &&& x 5) ||| (x 3 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 5 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 2 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7) ||| (x 6 &&& x 7)
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
  | 0 => (word80 [0x1000000000000,0x10000000000000001,0x10000,0x100000000,0x1000000000000,0x10000000000000001])
  | 1 => (word80 [0x10000000000000000,0x10000,0,0x1000000000000,1])
  | 2 => (word80 [1,0x10000,0,0,0x10000000000000001])
  | 3 => (word80 [0x10000,0,0,1])
  | 4 => (word80 [0x100000000,0x1000000000000,0x10000000000000001])
  | 5 => (word80 [0x1000000000000,1])
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
  (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 2 &&& x 5) ||| (x 3 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 5 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 2 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7) ||| (x 6 &&& x 7)
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
  let n := v.toNat % 2305843009213693921
  (n*(n+971)) % 2305843009213693921
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
private def limbs80 (pages : Array (Array Nat)) (i : Nat) : Nat :=
  ((pages[i/32]?).getD #[])[i%32]?.getD 0

def packedAt (word : Nat → Nat) (pos len : Nat) :=
  let i := pos/80
  let shift := pos % 80
  let lo := word i >>> shift
  if shift+len ≤ 80 then lo &&& ((1 <<< len)-1)
  else (lo ||| (word (i+1) <<< (80-shift))) &&& ((1 <<< len)-1)


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
  let n := v % 2305843009213693921
  (n*(n+971)) % 2305843009213693921
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



def target (x : Fin 8 → Bool) : Bool := decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
def smallCircuit : Circuit := ⟨[⟨.or,[5,7]⟩,⟨.or,[2,3]⟩,⟨.or,[0,6]⟩,⟨.or,[0,1]⟩,⟨.or,[7,11]⟩,⟨.or,[3,8]⟩,⟨.or,[6,7]⟩,⟨.or,[6,8]⟩,⟨.and,[12,4]⟩,⟨.and,[13,10]⟩,⟨.and,[15,9]⟩,⟨.and,[14,1]⟩,⟨.or,[16,17]⟩,⟨.or,[20,18]⟩,⟨.or,[21,19]⟩], 22⟩

theorem witnessMonotone : ∀ g ∈ smallCircuit.gates,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [smallCircuit,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ⟨Or.inl rfl,by decide⟩ | exact ⟨Or.inr rfl,by decide⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem witnessCorrect : ∀ x : Fin 8 → Bool, smallCircuit.eval (List.ofFn x) = target x := by
  decide +kernel

theorem witnessSize : smallCircuit.gates.length = 15 := rfl

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


def sevenInputs : List Sig := vars 255
def sampleSeven (r : Row) (i : Fin 8) : Bool := bit r (sevenInputs.getD i.val zero)
theorem sevenList : List.ofFn (fun i : Fin 8 => sevenInputs.getD i.val zero) = sevenInputs := rfl
theorem sevenSampled (r : Row) : List.ofFn (sampleSeven r) = sevenInputs.map (bit r) := by
  rw [←sevenList,List.map_ofFn]
  rfl

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem sevenTable : ∀ r : Row, bit r graph = target (sampleSeven r) := by decide +kernel

theorem sevenEval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates sevenInputs).getD i zero) =
      (C.wires (List.ofFn (sampleSeven r))).getD i false := by
  rw [←b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),sevenSampled]
  rfl

def lowRow (i : Fin 8) : Row := Fin.ofNat 512 (1 <<< ([3, 4, 5, 0, 0, 0, 1, 0] : List Nat).getD i.val 0)
def highRow (i : Fin 8) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< ([3, 4, 5, 0, 0, 0, 1, 0] : List Nat).getD i.val 0))

set_option maxHeartbeats 1000000 in
theorem allSevenRequired :
    (∀ i : Fin 8, bit (lowRow i) graph ≠ bit (highRow i) graph) ∧
    (∀ i j : Fin 8, i ≠ j →
      bit (lowRow i) (sevenInputs.getD j.val zero) =
      bit (highRow i) (sevenInputs.getD j.val zero)) := by decide +kernel

theorem physicalSigned (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x : Fin 8 → Bool, C.eval (List.ofFn x)=target x) :
    ∃ k, k ≤ C.gates.countP (fun g => !isNot g) ∧ Live true graph k sevenInputs.toFinset := by
  have goalEq : (execute C.gates sevenInputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (sevenEval C legal C.output r).trans ((computes (sampleSeven r)).trans (sevenTable r).symm)
  have out := get_rep (u:=true) (execute C.gates sevenInputs) C.output
  rw [goalEq] at out
  unfold Repr at out
  have pg : bit 0 graph = false := by decide +kernel
  rw [nrm_id pg] at out
  obtain ⟨k,S,hk,run,sub⟩ := extract (u:=true) C.gates sevenInputs legal (by simp) graph_proper
    (out.resolve_right (fun h => h graph_proper))
  have ns : sevenInputs.all plainWord = true := by decide +kernel
  rw [nrm_map ns] at sub
  have idx (a : Sig) (ha : a ∈ sevenInputs) : ∃ i : Fin 8, sevenInputs.getD i.val zero = a := by
    rw [←sevenList] at ha
    exact List.mem_ofFn.mp ha
  have eq : S = sevenInputs.toFinset := by
    ext a
    constructor
    · exact fun h => List.mem_toFinset.mpr (sub a h)
    · intro ha
      obtain ⟨i,rfl⟩ := idx a (List.mem_toFinset.mp ha)
      apply raw_required run sevenInputs (sevenInputs.getD i.val zero) sub (lowRow i) (highRow i)
        (allSevenRequired.1 i)
      intro v hv hn
      obtain ⟨j,rfl⟩ := idx v hv
      apply allSevenRequired.2 i j
      rintro rfl
      exact hn rfl
  exact ⟨k,hk,eq ▸ run⟩

theorem replaceShort 
    (lower : Impossible true graph 13 sevenInputs.toFinset) (gates : List Gate) (o : Nat)
    (fit : ∀ g ∈ gates, (g.op=GateOp.and ∨ g.op=GateOp.or ∨ g.op=GateOp.not) ∧ g.inputs.length≤2)
    (correct : ∀ x : Fin 8 → Bool, (Circuit.mk gates o).eval (List.ofFn x)=target x) :
    ∃ (gs : List Gate) (out : Nat), (∀ g ∈ gs, (g.op=GateOp.and ∨ g.op=GateOp.or) ∧ g.inputs.length≤2) ∧
       gs.length≤gates.length ∧ ∀ x : Fin 8 → Bool, (Circuit.mk gs out).eval (List.ofFn x)=target x := by
  classical
  by_cases big : 15 ≤ gates.length
  · exact ⟨smallCircuit.gates,smallCircuit.output,witnessMonotone,witnessSize.symm ▸ big,witnessCorrect⟩
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
def g41Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3ff63ff63ff63ff63f,0xf63ff63ff63ff63ff63f])),(BitVec.ofNat 152 (word80 [0x492049204920492049,0x20492049204920492049]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xc7fbc7fbc7fbc7fbc7,0xfbc7fbc7fbc7fbc7fbc7])),(BitVec.ofNat 152 (word80 [0x924092409240924092,0x40924092409240924092]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xf8fdf8fdf8fdf8fdf8,0xfdf8fdf8fdf8fdf8fdf8])),(BitVec.ofNat 152 (word80 [0x248124812481248124,0x81248124812481248124]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g41C : List ColumnInfo := []
def g41A : List (List Nat) := [[],[83],[48],[48,80],[80,48],[80]]
def g41D3 (j : Nat) := if j=0 then 0x7 else 0
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
def K41 := extendKnown [] 4 [(41,[]),(100,[32,16,83,67,100]),(104,[48,16,33,82,66,100]),(137,[117,101]),(145,[67,117,101]),(146,[16,67,117,101]),(194,[16,99,67,117]),(196,[32,16,99,67,117]),(200,[48,16,33,98,66,117])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V41 : Known true K41 := extend_ok (m:=41) baseKnown low41 (by decide +kernel)
def g27Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xe6de3fff03fff1ffe6,0xde3fff03fff1ffe6de3f])),(BitVec.ofNat 152 (word80 [0x648490a2850240206,0x48490a28502402064849]))),((BitVec.ofNat 152 (word80 [0x19e9c0fffc07fe3f19,0xe9c0fffc07fe3f19e9c0])),(BitVec.ofNat 152 (word80 [0x50e8db2c3161408450,0xe8db2c3161408450e8db]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xece607fffff8003fec,0xe607fffff8003fece607])),(BitVec.ofNat 152 (word80 [0x8a7b6b04185892808,0xa7b6b04185892808a7b6]))),((BitVec.ofNat 152 (word80 [0x1b3df8ffffffffc01b,0x3df8ffffffffc01b3df8])),(BitVec.ofNat 152 (word80 [0x891524c08206003089,0x1524c082060030891524]))),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g27C : List ColumnInfo := []
def g27A : List (List Nat) := [[],[64,49]]
def g27D3 (j : Nat) := if j=0 then 0xf else 0
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
def K27 := extendKnown K41 4 [(27,[]),(51,[83]),(53,[33,67,83]),(75,[96,16,49,67,84]),(77,[96,16,33,50,67,84]),(83,[16,99,83]),(86,[16,32,67,99,83]),(89,[48,65,33,96,32,82]),(90,[16,48,32,66,98,82]),(99,[96,16,49,84,67]),(113,[80,65,33,99,32]),(114,[96,65,32,83,50]),(163,[83,116,100]),(166,[32,83,116,100]),(170,[48,32,82,116,100]),(240,[96,65,32,83,113,49])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V27 : Known true K27 := extend_ok (m:=27) V41 low27 (by decide +kernel)
def g45Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfdf00fff81fc7e3ffb,0xe01fff03f8fc7ff7c03f])),(BitVec.ofNat 152 (word80 [0x45c09245142904808b,0x81248a28520901170249]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xe6a8703ffe007fc7cd,0x50e07ffc00ff8f9aa1c0])),(BitVec.ofNat 152 (word80 [0x96a9b6d618b228112d,0x536dac316450225aa6db]))),((BitVec.ofNat 152 (word80 [0xfbb781ffffff8007f7,0x6f03ffffff000feede07])),(BitVec.ofNat 152 (word80 [0x235249820c0312204,0x6a49304180624408d492]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x64ffe3ffffffff80c,0x9ffc7ffffffff0193ff8])),(BitVec.ofNat 152 (word80 [0x249204100400400,0x4924082008008000924]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g45C : List ColumnInfo := [(4,0,41,0,4)]
def g45A : List (List Nat) := [[],[48]]
def g45D4 (j : Nat) := if j=0 then 0x1f else 0
def g45L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g45D4)
  | _ => emptyPacking
def g45I (_ _ : Nat) : Option (Nat × Nat) := none
def g45 : Forest := ⟨45,4,fun i => g45Y[i]?.getD (0,0),g45C,g45A,g45L,g45I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g45P4_0 : block g45 4 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g45B4 : block g45 4 0 1=true := g45P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g45T : checkedTables g45 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g45 0 0 0 = true)
  · exact (rfl : block g45 1 0 0 = true)
  · exact (rfl : block g45 2 0 0 = true)
  · exact (rfl : block g45 3 0 0 = true)
  · exact g45B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g45G : graphValid g45 (boundsBefore K27) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low45 : Lower true (varsX 45) (graphGoal 45) 5 := lower_forest (g:=g45) (i:=0) (hints:=1283) (before_sound K27 V27) g45G g45T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K45 := extendKnown K27 5 [(45,[]),(57,[48,66,80]),(101,[32,99,67]),(102,[32,16,83,67,100]),(106,[48,16,33,82,66,100]),(139,[33,117,101]),(141,[117,101]),(149,[67,117,101]),(150,[16,67,117,101]),(154,[16,50,66,117,101]),(177,[64,82,115,32,99]),(195,[16,32,99,67,117]),(197,[32,99,67,117]),(209,[98,67,50,117]),(212,[32,16,65,99,117]),(216,[48,16,66,97,33,117]),(226,[16,82,115,66,100,67])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V45 : Known true K45 := extend_ok (m:=45) V27 low45 (by decide +kernel)
def g105Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xf1fe003ffc0f9f3f1f,0xe003ffc0f9f3f1fe003f])),(BitVec.ofNat 152 (word80 [0x241e49248a2142a241,0xe49248a2142a241e4924]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfe750fc7fff01fffe7,0x50fc7fff01fffe750fc7])),(BitVec.ofNat 152 (word80 [0x400012491042040400,0x1249104204040001249]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xff8af1f8ffffe03ff8,0xaf1f8ffffe03ff8af1f8])),(BitVec.ofNat 152 (word80 [0x800024922084080800,0x2492208408080002492]))),((BitVec.ofNat 152 (word80 [0x19fe00ffffffc001,0x9fe00ffffffc0019fe00])),(BitVec.ofNat 152 (word80 [0x959c924c308103095,0x9c924c3081030959c924]))),(0x0,0x0),(0x0,0x0)]
def g105C : List ColumnInfo := [(1,0,104,0,4)]
def g105A : List (List Nat) := [[],[83],[96],[96,83]]
def g105D4 (j : Nat) := if j=0 then 0x1f else 0
def g105L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g105D4)
  | _ => emptyPacking
def g105I (_ _ : Nat) : Option (Nat × Nat) := none
def g105 : Forest := ⟨105,4,fun i => g105Y[i]?.getD (0,0),g105C,g105A,g105L,g105I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g105P4_0 : block g105 4 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g105B4 : block g105 4 0 1=true := g105P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g105T : checkedTables g105 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g105 0 0 0 = true)
  · exact (rfl : block g105 1 0 0 = true)
  · exact (rfl : block g105 2 0 0 = true)
  · exact (rfl : block g105 3 0 0 = true)
  · exact g105B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g105G : graphValid g105 (boundsBefore K45) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low105 : Lower true (varsX 105) (graphGoal 105) 5 := lower_forest (g:=g105) (i:=0) (hints:=50331651) (before_sound K45 V45) g105G g105T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K105 := extendKnown K45 5 [(105,[]),(108,[32,16,83,99]),(147,[33,49,65,81,113,97]),(153,[48,84,116,100]),(169,[80,48,118]),(198,[16,50,98,117]),(201,[117]),(202,[16,99,117]),(204,[32,16,99,117]),(210,[64,16,49,117]),(232,[80,16,33,66,100,116])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V105 : Known true K105 := extend_ok (m:=105) V45 low105 (by decide +kernel)
def g55Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xe003ffc07ffffffe00,0x3fffff80ffd386b20f0f])),(BitVec.ofNat 152 (word80 [0x41a8128d052280541a,0x82502916291304a21111]))),((BitVec.ofNat 152 (word80 [0xfffc00007ff01fffff,0xc007ffff01a37d4800f0])),(BitVec.ofNat 152 (word80 [0x81311b160644c89893,0x136232244d835c485555]))),((BitVec.ofNat 152 (word80 [0xffffffff80001fffff,0xfff80000003f407df000])),(BitVec.ofNat 152 (word80 [0x5c05c18178702e01c,0x380bc38703340753333]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1fffff,0xfffffffffe663f7600ff])),(BitVec.ofNat 152 (word80 [0x160260205808130120,0x2404c00000642314aaaa]))),((BitVec.ofNat 152 (word80 [0xffffffffffffe00000,0x19dd38dff00])),(BitVec.ofNat 152 (word80 [0x1803800060001c01c0,0x38070040808c9308cccc]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g55C : List ColumnInfo := []
def g55A : List (List Nat) := [[],[33,84]]
def g55D4 (j : Nat) := if j=0 then 0x1f else 0
def g55L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g55D4)
  | _ => emptyPacking
def g55I (_ _ : Nat) : Option (Nat × Nat) := none
def g55 : Forest := ⟨55,4,fun i => g55Y[i]?.getD (0,0),g55C,g55A,g55L,g55I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g55P4_0 : block g55 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g55B4 : block g55 4 0 1=true := g55P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g55T : checkedTables g55 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g55 0 0 0 = true)
  · exact (rfl : block g55 1 0 0 = true)
  · exact (rfl : block g55 2 0 0 = true)
  · exact (rfl : block g55 3 0 0 = true)
  · exact g55B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g55G : graphValid g55 (boundsBefore K105) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low55 : Lower true (varsX 55) (graphGoal 55) 5 := lower_forest (g:=g55) (i:=0) (hints:=1348) (before_sound K105 V105) g55G g55T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K55 := extendKnown K105 5 [(55,[]),(87,[16,101]),(93,[48,33,65,16,96,80])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V55 : Known true K55 := extend_ok (m:=55) V105 low55 (by decide +kernel)
def g59Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xf007ff0ffffff007ff,0xff87ffffd45c460f83ff])),(BitVec.ofNat 152 (word80 [0xa0500a201000a05014,0x1100082401806108421]))),((BitVec.ofNat 152 (word80 [0xfff8000ff87ffff801,0xfff87fc05373b2007c00])),(BitVec.ofNat 152 (word80 [0xc0622c40a122c46258,0x8a012108527132b5ad6b]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffff0007ffffffe,0x7ffcafd11df0001f])),(BitVec.ofNat 152 (word80 [0x280b002c20b008060,0x2c220a00a541186318c6]))),((BitVec.ofNat 152 (word80 [0x7fffffff,0xffff80004d2fe8007fe0])),(BitVec.ofNat 152 (word80 [0xb04c08b044c090481,0x30004c100d06c94a5294]))),((BitVec.ofNat 152 (word80 [0xffffffffff80000000,0x33aa61bff8000])),(BitVec.ofNat 152 (word80 [0xc07000c00700e0701,0xc04470211aa6018c6318]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g59C : List ColumnInfo := [(0,2,41,16,5),(2,0,57,0,5),(8,0,51,0,4),(16,2,41,0,4),(32,0,27,0,4)]
def g59A : List (List Nat) := [[],[83]]
def g59D4 (j : Nat) := if j=0 then 0x4fd5120 else 0
def g59D5 := limbs80 #[#[0x480e140fd42fe20fd20,0x4088]]
def g59H5 (j : Nat) := if j=0 then 0x20 else 0
def g59D6 (j : Nat) := if j=0 then 0x18989f else 0
def g59H6 := limbs80 #[#[0x6e900000000000000,0x0,0x600200000000,0xc80000000000000]]
def g59L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g59D4)
  | 5 => (3,1,3,0,0,5,0,g59D5)
  | 6 => (1,0,3,0,0,0,0,g59D6)
  | _ => emptyPacking
def g59I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 4 0 0 g59H5
  | 6 => lookupWord 1 43 0 7 2 1 g59H6
  | _ => fun _ => none
def g59 : Forest := ⟨59,6,fun i => g59Y[i]?.getD (0,0),g59C,g59A,g59L,g59I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59P4_0 : block g59 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g59B4 : block g59 4 0 1=true := g59P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59P5_0 : block g59 5 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g59B5 : block g59 5 0 3=true := g59P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59P6_0 : block g59 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g59B6 : block g59 6 0 1=true := g59P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59T : checkedTables g59 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g59 0 0 0 = true)
  · exact (rfl : block g59 1 0 0 = true)
  · exact (rfl : block g59 2 0 0 = true)
  · exact (rfl : block g59 3 0 0 = true)
  · exact g59B4
  · exact g59B5
  · exact g59B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59G : graphValid g59 (boundsBefore K55) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low59 : Lower true (varsX 59) (graphGoal 59) 7 := lower_forest (g:=g59) (i:=0) (hints:=67) (before_sound K55 V55) g59G g59T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K59 := extendKnown K55 7 [(59,[]),(117,[80,65,33,50,48,99]),(118,[96,65,32,50]),(122,[96,65,32]),(182,[112,81,32,49,66,67,99]),(186,[112,81,32,49,67,98])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V59 : Known true K59 := extend_ok (m:=59) V55 low59 (by decide +kernel)
def g61Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xc007ff80ffe03fffff,0xffffffffff98eb9d81ff])),(BitVec.ofNat 152 (word80 [0x8050050200408000a0,0x14010000800003899249]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfff80000ffffc07ff0,0x1ff80ffc0619e0e8e00])),(BitVec.ofNat 152 (word80 [0xa61562c2a8a150ac3,0x584a1a290b419a0eb6db]))),((BitVec.ofNat 152 (word80 [0xffffffff0000007fff,0xfe0000ffff9f8a637007])),(BitVec.ofNat 152 (word80 [0xc8198483313261302,0x606c2c32121b88422492]))),((BitVec.ofNat 152 (word80 [0x7fff,0xffffff000009f56c0038])),(BitVec.ofNat 152 (word80 [0x2f05e070bc1c385c0b,0x817030bc1c09f4646db6]))),((BitVec.ofNat 152 (word80 [0xffffffffffffff8000,0x6754f2ffc0])),(BitVec.ofNat 152 (word80 [0x30060000c00000600c,0x18040c0202444304924]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g61C : List ColumnInfo := [(4,0,57,0,5)]
def g61A : List (List Nat) := [[],[80,66]]
def g61D5 (j : Nat) := if j=0 then 0x3f else 0
def g61L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g61D5)
  | _ => emptyPacking
def g61I (_ _ : Nat) : Option (Nat × Nat) := none
def g61 : Forest := ⟨61,5,fun i => g61Y[i]?.getD (0,0),g61C,g61A,g61L,g61I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g61P5_0 : block g61 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g61B5 : block g61 5 0 1=true := g61P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g61T : checkedTables g61 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g61 0 0 0 = true)
  · exact (rfl : block g61 1 0 0 = true)
  · exact (rfl : block g61 2 0 0 = true)
  · exact (rfl : block g61 3 0 0 = true)
  · exact (rfl : block g61 4 0 0 = true)
  · exact g61B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g61G : graphValid g61 (boundsBefore K59) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low61 : Lower true (varsX 61) (graphGoal 61) 6 := lower_forest (g:=g61) (i:=0) (hints:=1283) (before_sound K59 V59) g61G g61T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K61 := extendKnown K59 6 [(61,[]),(103,[96,49,32,33,65])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V61 : Known true K61 := extend_ok (m:=61) V59 low61 (by decide +kernel)
def g79Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x1fff0007ff803ffc01,0xfffffffffff245f3f007])),(BitVec.ofNat 152 (word80 [0x502a8350250681482d,0x550950a414040f37b6d]))),((BitVec.ofNat 152 (word80 [0x1ffffff800003fffff,0xffe001ffe001b15bc038])),(BitVec.ofNat 152 (word80 [0x854c2a62b62b159148,0x2986d84c8661a159c6db]))),((BitVec.ofNat 152 (word80 [0x1fffffffffffc00001,0xfffffe00000ce425d1c0])),(BitVec.ofNat 152 (word80 [0x6703383384c19e270,0x4e04e06f0b88a425d6db]))),((BitVec.ofNat 152 (word80 [0xe00000000000000001,0xfffffffffff22fedae07])),(BitVec.ofNat 152 (word80 [0x7803c03c0701e0380,0x700700700c022d0c8492]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffffffffffffe,0xdfa9e5ff8])),(BitVec.ofNat 152 (word80 [0x1800c0040000200001,0x80180180100452820924]))),(0x0,0x0),(0x0,0x0)]
def g79C : List ColumnInfo := [(2,0,77,0,4)]
def g79A : List (List Nat) := [[],[33]]
def g79D4 (j : Nat) := if j=0 then 0x3f else 0
def g79L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g79D4)
  | _ => emptyPacking
def g79I (_ _ : Nat) : Option (Nat × Nat) := none
def g79 : Forest := ⟨79,4,fun i => g79Y[i]?.getD (0,0),g79C,g79A,g79L,g79I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g79P4_0 : block g79 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g79B4 : block g79 4 0 1=true := g79P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g79T : checkedTables g79 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g79 0 0 0 = true)
  · exact (rfl : block g79 1 0 0 = true)
  · exact (rfl : block g79 2 0 0 = true)
  · exact (rfl : block g79 3 0 0 = true)
  · exact g79B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g79G : graphValid g79 (boundsBefore K61) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low79 : Lower true (varsX 79) (graphGoal 79) 5 := lower_forest (g:=g79) (i:=0) (hints:=16778851) (before_sound K61 V61) g79G g79T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K79 := extendKnown K61 5 [(79,[]),(94,[64,33,49])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V79 : Known true K79 := extend_ok (m:=79) V61 low79 (by decide +kernel)
def g91Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xf003ff0ff87ff007ff,0xff87fffcd47c560003ff])),(BitVec.ofNat 152 (word80 [0xa4280a201120a45214,0x81102080501c1694a529]))),((BitVec.ofNat 152 (word80 [0xfffc000ffffffff801,0xfff87fc35353a20ffc00])),(BitVec.ofNat 152 (word80 [0xc0302c40a002c06058,0xa01010a425122318c63]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffff0007ffffffe,0x7ffcafd11df0001f])),(BitVec.ofNat 152 (word80 [0x140b002c20b008060,0x2c220a00a741086318c6]))),((BitVec.ofNat 152 (word80 [0x7fffffff,0xffff80004d2fe8007fe0])),(BitVec.ofNat 152 (word80 [0x982c08b044c090481,0x30004c100d22c94a5294]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffff80000000,0x33aa61bff8000])),(BitVec.ofNat 152 (word80 [0xe03000c00700e0701,0xc044702118a6118c6318]))),(0x0,0x0),(0x0,0x0)]
def g91C : List ColumnInfo := [(1,0,90,0,4),(2,0,89,0,4),(8,0,83,0,4),(16,0,75,0,4),(64,0,27,0,4)]
def g91A : List (List Nat) := [[],[97,67],[16,99],[16,48,64,96],[48,100],[48,65,96,16],[64,49],[64,97,48,49],[96,16,49,67],[96,65]]
def g91D4 (j : Nat) := if j=0 then 0x57d4d10 else 0
def g91D5 (j : Nat) := if j=0 then 0xc1a0fd20fd10 else 0
def g91H5 (j : Nat) := if j=0 then 0x20 else 0
def g91D6 (j : Nat) := if j=0 then 0x23440bf else 0
def g91H6 := limbs80 #[#[0x65aa00510000000000b6,0x63000000e29e0000,0xc00037000000008b]]
def g91L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g91D4)
  | 5 => (2,1,3,0,0,4,0,g91D5)
  | 6 => (1,0,3,0,0,0,0,g91D6)
  | _ => emptyPacking
def g91I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 4 0 0 g91H5
  | 6 => lookupWord 2 29 0 8 1 3 g91H6
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
theorem g91P5_0 : block g91 5 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g91B5 : block g91 5 0 2=true := g91P5_0
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
theorem g91G : graphValid g91 (boundsBefore K79) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low91 : Lower true (varsX 91) (graphGoal 91) 7 := lower_forest (g:=g91) (i:=0) (hints:=16777283) (before_sound K79 V79) g91G g91T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K91 := extendKnown K79 7 [(91,[]),(115,[97,67,83])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V91 : Known true K91 := extend_ok (m:=91) V79 low91 (by decide +kernel)
def g107Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffc01ff0ff0ffc03f,0xf0ffffff24d65b0000ff])),(BitVec.ofNat 152 (word80 [0x282a140a202282a2a0,0xa2820820048653999999]))),((BitVec.ofNat 152 (word80 [0xffffe000fffffffc0,0xff0ff0c6353900f000])),(BitVec.ofNat 152 (word80 [0x42b098ac45402b030a,0xc4142242823539777777]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffff000ffffff,0xff000fff39b5260f0f0f])),(BitVec.ofNat 152 (word80 [0x80c0203001840c0403,0x184080383100222222]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xf00000000000ffffff,0xfffff000134bf8f00ff0])),(BitVec.ofNat 152 (word80 [0x300c0c0860830080c,0x200304034828444444]))),((BitVec.ofNat 152 (word80 [0xffffffffffff000000,0xcea8c5fff000])),(BitVec.ofNat 152 (word80 [0xc0301000800c03030,0x8c08c084480c4888888]))),(0x0,0x0),(0x0,0x0)]
def g107C : List ColumnInfo := [(0,2,41,64,5),(1,0,106,0,5),(2,0,105,0,5),(8,0,99,0,4),(32,0,75,0,4),(64,2,41,0,4)]
def g107A : List (List Nat) := [[],[83]]
def g107D4 (j : Nat) := if j=0 then 0x5ed4132 else 0
def g107D5 (j : Nat) := if j=0 then 0xc8404fd32 else 0
def g107H5 (j : Nat) := if j=0 then 0x90 else 0
def g107D6 (j : Nat) := if j=0 then 0x23468bf else 0
def g107H6 (j : Nat) := if j=0 then 0xc else 0
def g107L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g107D4)
  | 5 => (1,1,3,0,0,0,0,g107D5)
  | 6 => (1,0,3,0,0,0,0,g107D6)
  | _ => emptyPacking
def g107I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 4 0 0 g107H5
  | 6 => lookupWord 1 2 0 4 0 0 g107H6
  | _ => fun _ => none
def g107 : Forest := ⟨107,6,fun i => g107Y[i]?.getD (0,0),g107C,g107A,g107L,g107I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g107P4_0 : block g107 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g107B4 : block g107 4 0 1=true := g107P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g107P5_0 : block g107 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g107B5 : block g107 5 0 1=true := g107P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g107P6_0 : block g107 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g107B6 : block g107 6 0 1=true := g107P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g107T : checkedTables g107 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g107 0 0 0 = true)
  · exact (rfl : block g107 1 0 0 = true)
  · exact (rfl : block g107 2 0 0 = true)
  · exact (rfl : block g107 3 0 0 = true)
  · exact g107B4
  · exact g107B5
  · exact g107B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g107G : graphValid g107 (boundsBefore K91) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low107 : Lower true (varsX 107) (graphGoal 107) 7 := lower_forest (g:=g107) (i:=0) (hints:=16777315) (before_sound K91 V91) g107G g107T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K107 := extendKnown K91 7 [(107,[]),(121,[96,65,33]),(171,[80,48,118]),(179,[16,80,67,112,96]),(242,[64,81,32,49,115]),(248,[80,65,32,98,114])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V107 : Known true K107 := extend_ok (m:=107) V91 low107 (by decide +kernel)
def g109Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfe1ff00ff1fc7fc03f,0xe1fe1fffd599a00000ff])),(BitVec.ofNat 152 (word80 [0x1450a8a0a40942a2a1,0x450441084589a9999999]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1ffff001ffffffc0,0x1ffe1fc493e300f0f00])),(BitVec.ofNat 152 (word80 [0x5882c0c2c8500b0305,0x88280411093a33333333]))),((BitVec.ofNat 152 (word80 [0x1ffffffe007fffff,0xfe0001ffbe1b40f0f00f])),(BitVec.ofNat 152 (word80 [0x6103010300620c0406,0x3088203a1202222222]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffe0000000007fffff,0xfffffe000be08f00fff0])),(BitVec.ofNat 152 (word80 [0x800402040080100808,0x400040000004444444]))),((BitVec.ofNat 152 (word80 [0xffffffffffff800000,0x6446ffff0000])),(BitVec.ofNat 152 (word80 [0x180c080100603030,0x118111824444c8888888]))),(0x0,0x0),(0x0,0x0)]
def g109C : List ColumnInfo := [(1,0,108,0,5),(4,0,105,0,5),(8,0,101,0,5),(64,0,45,0,5)]
def g109A : List (List Nat) := [[],[32,99]]
def g109D6 (j : Nat) := if j=0 then 0x2709f else 0
def g109L : Nat → Packing
  | 6 => (1,0,2,0,0,0,0,g109D6)
  | _ => emptyPacking
def g109I (_ _ : Nat) : Option (Nat × Nat) := none
def g109 : Forest := ⟨109,6,fun i => g109Y[i]?.getD (0,0),g109C,g109A,g109L,g109I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g109P6_0 : block g109 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g109B6 : block g109 6 0 1=true := g109P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g109T : checkedTables g109 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g109 0 0 0 = true)
  · exact (rfl : block g109 1 0 0 = true)
  · exact (rfl : block g109 2 0 0 = true)
  · exact (rfl : block g109 3 0 0 = true)
  · exact (rfl : block g109 4 0 0 = true)
  · exact (rfl : block g109 5 0 0 = true)
  · exact g109B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g109G : graphValid g109 (boundsBefore K107) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low109 : Lower true (varsX 109) (graphGoal 109) 7 := lower_forest (g:=g109) (i:=0) (hints:=33555715) (before_sound K107 V107) g109G g109T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K109 := extendKnown K107 7 [(109,[]),(155,[16,32,48,64,80,112,96]),(185,[64,82,115,32,99]),(203,[33,117]),(205,[117]),(211,[33,97,67,117]),(214,[32,16,65,99,49,117]),(217,[64,98,48,50,117]),(218,[48,16,66,97,117]),(230,[16,82,115,67,98]),(234,[16,82,115,66,100,67])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V109 : Known true K109 := extend_ok (m:=109) V107 low109 (by decide +kernel)
def g110Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffc00ffc07fe03fff,0xe007fc0ff810c7b401c0])),(BitVec.ofNat 152 (word80 [0xa4a96a528d2a458a25,0x4b5129a292d0c7b5b6db]))),((BitVec.ofNat 152 (word80 [0xfffff00007fffc07f,0xfff8000ffff706cc0e07])),(BitVec.ofNat 152 (word80 [0xc1304c1b160c891309,0x8261b2c3249302cc9249]))),((BitVec.ofNat 152 (word80 [0xfffffffff8000007f,0xfffffff0000be8947038])),(BitVec.ofNat 152 (word80 [0x1c0701c180f0e1c0e,0x381c303c70b60949249]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xf0000000000000007f,0xffffffffffe6fe67803f])),(BitVec.ofNat 152 (word80 [0x60180602030102030,0xc02000400049c212492]))),((BitVec.ofNat 152 (word80 [0xffffffffffffffff80,0x1911bbffc0])),(BitVec.ofNat 152 (word80 [0x80200800040000040,0x10040008000000024924]))),(0x0,0x0),(0x0,0x0)]
def g110C : List ColumnInfo := [(2,0,108,0,5)]
def g110A : List (List Nat) := [[],[50]]
def g110D5 (j : Nat) := if j=0 then 0x3f else 0
def g110L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g110D5)
  | _ => emptyPacking
def g110I (_ _ : Nat) : Option (Nat × Nat) := none
def g110 : Forest := ⟨110,5,fun i => g110Y[i]?.getD (0,0),g110C,g110A,g110L,g110I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g110P5_0 : block g110 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g110B5 : block g110 5 0 1=true := g110P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g110T : checkedTables g110 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g110 0 0 0 = true)
  · exact (rfl : block g110 1 0 0 = true)
  · exact (rfl : block g110 2 0 0 = true)
  · exact (rfl : block g110 3 0 0 = true)
  · exact (rfl : block g110 4 0 0 = true)
  · exact g110B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g110G : graphValid g110 (boundsBefore K109) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low110 : Lower true (varsX 110) (graphGoal 110) 6 := lower_forest (g:=g110) (i:=0) (hints:=18896224) (before_sound K109 V109) g110G g110T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K110 := extendKnown K109 6 [(110,[]),(151,[48,33,16,84,118]),(157,[16,32,48,64,80,118]),(199,[48,16,33,101,117])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V110 : Known true K110 := extend_ok (m:=110) V109 low110 (by decide +kernel)
def g143Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3ffc003ffc01ffe00f,0xfffffffffffeddea003f])),(BitVec.ofNat 152 (word80 [0x80a81a8128340a4160,0xa02a094148524c6a1249]))),((BitVec.ofNat 152 (word80 [0x3fffffc00001fffff0,0x7ff001ffc0118f681c0])),(BitVec.ofNat 152 (word80 [0x15315315b158ac8a45,0x314c6d89919918f6b6db]))),((BitVec.ofNat 152 (word80 [0x3ffffffffffe000000,0x7ffffe000031f070e00])),(BitVec.ofNat 152 (word80 [0x19c19c19c260cf1389,0xc2704e0de2e31f0736db]))),((BitVec.ofNat 152 (word80 [0xc00000000000000000,0x7fffffffffcbfdc7007])),(BitVec.ofNat 152 (word80 [0x1e01e01e0380f01c0e,0x380700e0300b3942492]))),(0x0,0x0),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffffffff,0xf800000000036237fff8])),(BitVec.ofNat 152 (word80 [0x200200200001000000,0x4008010000000004924]))),(0x0,0x0)]
def g143C : List ColumnInfo := [(2,0,141,0,5)]
def g143A : List (List Nat) := [[],[33],[48],[48,33]]
def g143D5 (j : Nat) := if j=0 then 0x3f else 0
def g143L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g143D5)
  | _ => emptyPacking
def g143I (_ _ : Nat) : Option (Nat × Nat) := none
def g143 : Forest := ⟨143,5,fun i => g143Y[i]?.getD (0,0),g143C,g143A,g143L,g143I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g143P5_0 : block g143 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g143B5 : block g143 5 0 1=true := g143P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g143T : checkedTables g143 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g143 0 0 0 = true)
  · exact (rfl : block g143 1 0 0 = true)
  · exact (rfl : block g143 2 0 0 = true)
  · exact (rfl : block g143 3 0 0 = true)
  · exact (rfl : block g143 4 0 0 = true)
  · exact g143B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g143G : graphValid g143 (boundsBefore K110) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low143 : Lower true (varsX 143) (graphGoal 143) 6 := lower_forest (g:=g143) (i:=0) (hints:=1907) (before_sound K110 V110) g143G g143T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K143 := extendKnown K110 6 [(143,[]),(158,[16,32,48,64])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V143 : Known true K143 := extend_ok (m:=143) V110 low143 (by decide +kernel)
def g167Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xe003ff80ffe03ffff0,0x3ff80ffff909e9b81c7])),(BitVec.ofNat 152 (word80 [0x41a8251a0a458a02a1,0xa8251a148a00928b9249]))),((BitVec.ofNat 152 (word80 [0xfffc0000ffffc07fff,0xfc0000ffc068da648e00])),(BitVec.ofNat 152 (word80 [0x8530b62c2c891314c1,0x30b62c191348da44b6db]))),((BitVec.ofNat 152 (word80 [0xffffffff0000007fff,0xffffff00000ff10e7038])),(BitVec.ofNat 152 (word80 [0x1c038300f0e1c0701,0xc038301e1c02d10e1249]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x7fff,0xffffffffff99af6d003f])),(BitVec.ofNat 152 (word80 [0x1602c040b01020580a,0x2c000a000192c606db6]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffff8000,0x6754f2ffc0])),(BitVec.ofNat 152 (word80 [0x18030000c00000600c,0x30040c0202504304924]))),(0x0,0x0)]
def g167C : List ColumnInfo := [(1,0,166,0,4)]
def g167A : List (List Nat) := [[],[32]]
def g167D4 (j : Nat) := if j=0 then 0x3f else 0
def g167L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g167D4)
  | _ => emptyPacking
def g167I (_ _ : Nat) : Option (Nat × Nat) := none
def g167 : Forest := ⟨167,4,fun i => g167Y[i]?.getD (0,0),g167C,g167A,g167L,g167I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g167P4_0 : block g167 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g167B4 : block g167 4 0 1=true := g167P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g167T : checkedTables g167 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g167 0 0 0 = true)
  · exact (rfl : block g167 1 0 0 = true)
  · exact (rfl : block g167 2 0 0 = true)
  · exact (rfl : block g167 3 0 0 = true)
  · exact g167B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g167G : graphValid g167 (boundsBefore K143) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low167 : Lower true (varsX 167) (graphGoal 167) 5 := lower_forest (g:=g167) (i:=0) (hints:=1397) (before_sound K143 V143) g167G g167T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K167 := extendKnown K143 5 [(167,[]),(174,[32,48]),(188,[32,65,48])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V167 : Known true K167 := extend_ok (m:=167) V143 low167 (by decide +kernel)
def g173Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfffc03fe1fe1fff00f,0xf87f87ffff856420703f])),(BitVec.ofNat 152 (word80 [0x50282814404400a0a0,0x51011002098064049249]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x7fffc001ffe1ffff0,0x7ff87f01c9c9c381c0])),(BitVec.ofNat 152 (word80 [0x60b03058828042c0c1,0x620a01042181c98db6db]))),((BitVec.ofNat 152 (word80 [0x7ffffffe0001fffff,0xff80007ff233d69c0e07])),(BitVec.ofNat 152 (word80 [0x80c040600308830101,0x800c2208021380892492]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xf800000000001fffff,0xffffff80013c2ae00ff8])),(BitVec.ofNat 152 (word80 [0x50282811411140a0a,0x500050402c02724924]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffe00000,0xce2917ff000])),(BitVec.ofNat 152 (word80 [0x60303001800180c0c,0x4604460846010724924]))),(0x0,0x0)]
def g173C : List ColumnInfo := [(4,0,169,0,5)]
def g173A : List (List Nat) := [[],[117],[48],[48,117]]
def g173D5 (j : Nat) := if j=0 then 0x3f else 0
def g173L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g173D5)
  | _ => emptyPacking
def g173I (_ _ : Nat) : Option (Nat × Nat) := none
def g173 : Forest := ⟨173,5,fun i => g173Y[i]?.getD (0,0),g173C,g173A,g173L,g173I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g173P5_0 : block g173 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g173B5 : block g173 5 0 1=true := g173P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g173T : checkedTables g173 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g173 0 0 0 = true)
  · exact (rfl : block g173 1 0 0 = true)
  · exact (rfl : block g173 2 0 0 = true)
  · exact (rfl : block g173 3 0 0 = true)
  · exact (rfl : block g173 4 0 0 = true)
  · exact g173B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g173G : graphValid g173 (boundsBefore K167) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low173 : Lower true (varsX 173) (graphGoal 173) 6 := lower_forest (g:=g173) (i:=0) (hints:=1283) (before_sound K167 V167) g173G g173T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K173 := extendKnown K167 6 [(173,[]),(229,[32,99,67])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V173 : Known true K173 := extend_ok (m:=173) V167 low173 (by decide +kernel)
def g181Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xff007fe1ff0fffc03f,0xfff0fffff95e0200f0ff])),(BitVec.ofNat 152 (word80 [0xa0501440220028281,0x40220020980602111111]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffff8001fff0ffffc0,0x1fff0ff01c35b90f0f00])),(BitVec.ofNat 152 (word80 [0x2c06058814020b0305,0x81402042183511333333]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffe0000ffffff,0xe0000fff23b566f0000f])),(BitVec.ofNat 152 (word80 [0xb028160058442c0406,0x5844280213164666666]))),((BitVec.ofNat 152 (word80 [0xffffff,0xfffff000134bf8000ff0])),(BitVec.ofNat 152 (word80 [0xc0b058116088b02828,0x16000b040348e8cccccc]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffff000000,0xcea8c5fff000])),(BitVec.ofNat 152 (word80 [0xc060018000c03030,0x18088c08468880888888]))),(0x0,0x0)]
def g181C : List ColumnInfo := [(4,0,177,0,5)]
def g181A : List (List Nat) := [[],[112,82]]
def g181D5 (j : Nat) := if j=0 then 0x3f else 0
def g181L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g181D5)
  | _ => emptyPacking
def g181I (_ _ : Nat) : Option (Nat × Nat) := none
def g181 : Forest := ⟨181,5,fun i => g181Y[i]?.getD (0,0),g181C,g181A,g181L,g181I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g181P5_0 : block g181 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g181B5 : block g181 5 0 1=true := g181P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g181T : checkedTables g181 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g181 0 0 0 = true)
  · exact (rfl : block g181 1 0 0 = true)
  · exact (rfl : block g181 2 0 0 = true)
  · exact (rfl : block g181 3 0 0 = true)
  · exact (rfl : block g181 4 0 0 = true)
  · exact g181B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g181G : graphValid g181 (boundsBefore K173) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low181 : Lower true (varsX 181) (graphGoal 181) 6 := lower_forest (g:=g181) (i:=0) (hints:=1284) (before_sound K173 V173) g181G g181T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K181 := extendKnown K173 6 [(181,[]),(227,[96,33,16,65]),(241,[112,82,50,99])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V181 : Known true K181 := extend_ok (m:=181) V173 low181 (by decide +kernel)
def g206Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0xc07fc01ff03fe07fff,0x7fc0ff81fed6800e07])),(BitVec.ofNat 152 (word80 [0x950a8d44a68a4b282a,0x35129a292ca6d6849249]))),((BitVec.ofNat 152 (word80 [0x7fffe0003fff81ff,0xff8000fffe0725a07038])),(BitVec.ofNat 152 (word80 [0x26130986cb0c924c4c,0x261b2c32493725a49249]))),((BitVec.ofNat 152 (word80 [0x7fffffffc00001ff,0xffffff0000074b4381c0])),(BitVec.ofNat 152 (word80 [0x381c0e070c0f1c7070,0x381c303c71c74b449249]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xff80000000000001ff,0xfffffffffffacd3c01ff])),(BitVec.ofNat 152 (word80 [0x2010080010000080,0x40200040000000092492]))),((BitVec.ofNat 152 (word80 [0xfffffffffffffffe00,0x532dffe00])),(BitVec.ofNat 152 (word80 [0x4020100020000100,0x80400080000000124924]))),(0x0,0x0)]
def g206C : List ColumnInfo := [(2,0,204,0,5)]
def g206A : List (List Nat) := [[],[118],[50],[50,118],[33],[33,118],[33,49],[33,49,118],[49,33],[49,33,118],[49],[49,118]]
def g206D5 (j : Nat) := if j=0 then 0x3f else 0
def g206L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g206D5)
  | _ => emptyPacking
def g206I (_ _ : Nat) : Option (Nat × Nat) := none
def g206 : Forest := ⟨206,5,fun i => g206Y[i]?.getD (0,0),g206C,g206A,g206L,g206I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g206P5_0 : block g206 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g206B5 : block g206 5 0 1=true := g206P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g206T : checkedTables g206 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g206 0 0 0 = true)
  · exact (rfl : block g206 1 0 0 = true)
  · exact (rfl : block g206 2 0 0 = true)
  · exact (rfl : block g206 3 0 0 = true)
  · exact (rfl : block g206 4 0 0 = true)
  · exact g206B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g206G : graphValid g206 (boundsBefore K181) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low206 : Lower true (varsX 206) (graphGoal 206) 6 := lower_forest (g:=g206) (i:=0) (hints:=285238880) (before_sound K181 V181) g206G g206T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K206 := extendKnown K181 6 [(206,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V206 : Known true K206 := extend_ok (m:=206) V181 low206 (by decide +kernel)
def g213Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffc01ff87fc3fff00,0xffff1ffed2e680007c1f])),(BitVec.ofNat 152 (word80 [0x222894451108808a4a,0xa02444252268a5294a5]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffe0007ffc3ffff,0xffffe11773400f83e0])),(BitVec.ofNat 152 (word80 [0x40b018162050082c0c,0x2c140089146346318c63]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffff80003ffff,0xff001ffce8f541f0001f])),(BitVec.ofNat 152 (word80 [0x84c120980261113010,0x30588900a8d154a5294a]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xf0000000000003ffff,0xffffe0005f98fe0003e0])),(BitVec.ofNat 152 (word80 [0x701c0e0438221c060,0x40600e104b9898c6318c]))),((BitVec.ofNat 152 (word80 [0xfffffffffffffc0000,0x3280bbffffc00])),(BitVec.ofNat 152 (word80 [0x80201000400020080,0x80801000000021084210]))),(0x0,0x0)]
def g213C : List ColumnInfo := [(1,0,212,0,5),(4,0,209,0,5),(16,0,197,0,5),(64,0,149,0,5),(17,0,196,0,4),(68,0,145,0,4)]
def g213A : List (List Nat) := [[],[98],[32,100],[32,64,96],[64],[64,98],[96,32,66],[96,66]]
def g213D4 := limbs80 #[#[0x9bd89544426d6215110,0x31825f635474]]
def g213D5 := limbs80 #[#[0x7c54443f280885bd4940,0xfea8885f95110beaa221,0xbd4940bfa8a81fb40502,0xcc8d018160c02faa3a07,0x882188201141080d176b,0xc110204810001]]
def g213H5 (j : Nat) := if j=0 then 0x49006820528100 else 0
def g213D6 := limbs80 #[#[0x540a0380ff40fd40fd10,0x3140cc503]]
def g213H6 := limbs80 #[#[0x100345c1e144454201a0,0xd230,0x4d5c000000031a136640,0x143a2400a0000684c]]
def g213D7 (j : Nat) := if j=0 then 0x1605f else 0
def g213H7 := limbs80 #[#[0x4000075700980000002c,0x6c87439d4c4401541228,0xe1]]
def g213L : Nat → Packing
  | 4 => (3,3,3,0,0,4,0,g213D4)
  | 5 => (10,2,3,0,0,7,0,g213D5)
  | 6 => (3,1,3,0,0,6,0,g213D6)
  | 7 => (1,0,3,0,0,0,0,g213D7)
  | _ => emptyPacking
def g213I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 11 0 8 2 2 g213H5
  | 6 => lookupWord 4 29 4 10 4 2 g213H6
  | 7 => lookupWord 3 19 2 9 2 3 g213H7
  | _ => fun _ => none
def g213 : Forest := ⟨213,7,fun i => g213Y[i]?.getD (0,0),g213C,g213A,g213L,g213I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g213P4_0 : block g213 4 0 3=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g213B4 : block g213 4 0 3=true := g213P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g213P5_0 : block g213 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g213P5_1 : block g213 5 1 9=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g213B5 : block g213 5 0 10=true := (@block_merge g213 5 0 1 9 g213P5_0 g213P5_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g213P6_0 : block g213 6 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g213B6 : block g213 6 0 3=true := g213P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g213P7_0 : block g213 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g213B7 : block g213 7 0 1=true := g213P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g213T : checkedTables g213 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g213 0 0 0 = true)
  · exact (rfl : block g213 1 0 0 = true)
  · exact (rfl : block g213 2 0 0 = true)
  · exact (rfl : block g213 3 0 0 = true)
  · exact g213B4
  · exact g213B5
  · exact g213B6
  · exact g213B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g213G : graphValid g213 (boundsBefore K206) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low213 : Lower true (varsX 213) (graphGoal 213) 8 := lower_forest (g:=g213) (i:=0) (hints:=33555972) (before_sound K206 V206) g213G g213T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K213 := extendKnown K206 8 [(213,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V213 : Known true K213 := extend_ok (m:=213) V206 low213 (by decide +kernel)
def g233Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x1fc7f80fffe1ffc03,0xf8fe1fe1fea15e03803f])),(BitVec.ofNat 152 (word80 [0x440911224444408888,0x1204444400a10e492492]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfe007fff01ffe3fffc,0xfffffe3d41851c0fc7])),(BitVec.ofNat 152 (word80 [0x81002040808001010,0x20080080000000249249]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x7ffffe0003ffff,0xff001fffc3ba900071f8])),(BitVec.ofNat 152 (word80 [0x1122440811108a2222,0x409091000b0a90924924]))),((BitVec.ofNat 152 (word80 [0xffff8000000003ffff,0xffffe000007f28e07e00])),(BitVec.ofNat 152 (word80 [0x60401830606110c0c0,0x80200608907508492492]))),((BitVec.ofNat 152 (word80 [0xfffffffffffffc0000,0x3066bff8000])),(BitVec.ofNat 152 (word80 [0x818060408180030303,0x4c11811230261924924]))),(0x0,0x0)]
def g233C : List ColumnInfo := [(1,0,232,0,5)]
def g233A : List (List Nat) := [[],[117],[80,118],[80,96,112],[96],[96,117],[112,80,101],[112,101]]
def g233D5 (j : Nat) := if j=0 then 0x3f else 0
def g233L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g233D5)
  | _ => emptyPacking
def g233I (_ _ : Nat) : Option (Nat × Nat) := none
def g233 : Forest := ⟨233,5,fun i => g233Y[i]?.getD (0,0),g233C,g233A,g233L,g233I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g233P5_0 : block g233 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g233B5 : block g233 5 0 1=true := g233P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g233T : checkedTables g233 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g233 0 0 0 = true)
  · exact (rfl : block g233 1 0 0 = true)
  · exact (rfl : block g233 2 0 0 = true)
  · exact (rfl : block g233 3 0 0 = true)
  · exact (rfl : block g233 4 0 0 = true)
  · exact g233B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g233G : graphValid g233 (boundsBefore K213) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low233 : Lower true (varsX 233) (graphGoal 233) 6 := lower_forest (g:=g233) (i:=0) (hints:=50331651) (before_sound K213 V213) g233G g233T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K233 := extendKnown K213 6 [(233,[]),(236,[32,16,99])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V233 : Known true K233 := extend_ok (m:=233) V213 low233 (by decide +kernel)
def g63Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffffffffffffffffff,0xf8a5b238c872c00f83ff])),(BitVec.ofNat 152 (word80 [0x28002a00250014805,0x38252220002282108421]))),((BitVec.ofNat 152 (word80 [0x1ffff00007fffc00,0x1f582a4bb06d80007c00])),(BitVec.ofNat 152 (word80 [0x14c814c41b62099019,0x9b582a4b806196b5ad6b]))),((BitVec.ofNat 152 (word80 [0x1ffffffff8000000,0x73623e14bd881f00000])),(BitVec.ofNat 152 (word80 [0x6702a7015380ade0ae,0x53623614ad88e739ce7]))),((BitVec.ofNat 152 (word80 [0x1fffffffffffffff,0xc858e56c4e4f7e00001f])),(BitVec.ofNat 152 (word80 [0xb80338019c00ce0130,0x50c14c4a4d4c6318c6]))),((BitVec.ofNat 152 (word80 [0xffe000000000000000,0x4579a17773c00007fe0])),(BitVec.ofNat 152 (word80 [0xc013c009e004f001c0,0x4029014771c294a5294]))),(0x33aa5dc49781bfff8000,(BitVec.ofNat 152 (word80 [0x1c000e0007000200,0x2881c809500318c6318]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g63C : List ColumnInfo := [(4,0,59,0,7)]
def g63A : List (List Nat) := [[]]
def g63D7 (j : Nat) := if j=0 then 0x7f else 0
def g63L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g63D7)
  | _ => emptyPacking
def g63I (_ _ : Nat) : Option (Nat × Nat) := none
def g63 : Forest := ⟨63,7,fun i => g63Y[i]?.getD (0,0),g63C,g63A,g63L,g63I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7_0 : block g63 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g63B7 : block g63 7 0 1=true := g63P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63T : checkedTables g63 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g63 0 0 0 = true)
  · exact (rfl : block g63 1 0 0 = true)
  · exact (rfl : block g63 2 0 0 = true)
  · exact (rfl : block g63 3 0 0 = true)
  · exact (rfl : block g63 4 0 0 = true)
  · exact (rfl : block g63 5 0 0 = true)
  · exact (rfl : block g63 6 0 0 = true)
  · exact g63B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63G : graphValid g63 (boundsBefore K233) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low63 : Lower true (varsX 63) (graphGoal 63) 8 := lower_forest (g:=g63) (i:=0) (hints:=1347) (before_sound K233 V233) g63G g63T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K63 := extendKnown K233 8 [(63,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V63 : Known true K63 := extend_ok (m:=63) V233 low63 (by decide +kernel)
def g95Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffffffffffffffffff,0xd925ba38c873c00003ff])),(BitVec.ofNat 152 (word80 [0x28802a40252014805,0x1925322080239294a529]))),((BitVec.ofNat 152 (word80 [0x1ffff00007fffc00,0x3ed8224bb06c800ffc00])),(BitVec.ofNat 152 (word80 [0x14c014c01b60099019,0xba58224b006086318c63]))),((BitVec.ofNat 152 (word80 [0x1ffffffff8000000,0x73623e14bd881f00000])),(BitVec.ofNat 152 (word80 [0x6702a7015380ade0ae,0x63623614ad88e739ce7]))),((BitVec.ofNat 152 (word80 [0x1fffffffffffffff,0xc858e56c4e4f7e00001f])),(BitVec.ofNat 152 (word80 [0xb80338019c00ce0130,0x58c14c4a4c4c6318c6]))),((BitVec.ofNat 152 (word80 [0xffe000000000000000,0x4579a17773c00007fe0])),(BitVec.ofNat 152 (word80 [0xc013c009e004f001c0,0x4028814771c294a5294]))),(0x0,0x0),(0x33aa5dc49781bfff8000,(BitVec.ofNat 152 (word80 [0x1c000e0007000200,0x1801c809501318c6318]))),(0x0,0x0),(0x0,0x0)]
def g95C : List ColumnInfo := [(4,0,91,0,7)]
def g95A : List (List Nat) := [[],[64,49]]
def g95D7 (j : Nat) := if j=0 then 0x7f else 0
def g95L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g95D7)
  | _ => emptyPacking
def g95I (_ _ : Nat) : Option (Nat × Nat) := none
def g95 : Forest := ⟨95,7,fun i => g95Y[i]?.getD (0,0),g95C,g95A,g95L,g95I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P7_0 : block g95 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g95B7 : block g95 7 0 1=true := g95P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95T : checkedTables g95 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g95 0 0 0 = true)
  · exact (rfl : block g95 1 0 0 = true)
  · exact (rfl : block g95 2 0 0 = true)
  · exact (rfl : block g95 3 0 0 = true)
  · exact (rfl : block g95 4 0 0 = true)
  · exact (rfl : block g95 5 0 0 = true)
  · exact (rfl : block g95 6 0 0 = true)
  · exact g95B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95G : graphValid g95 (boundsBefore K63) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low95 : Lower true (varsX 95) (graphGoal 95) 8 := lower_forest (g:=g95) (i:=0) (hints:=16778819) (before_sound K63 V63) g95G g95T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K95 := extendKnown K63 8 [(95,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V95 : Known true K95 := extend_ok (m:=95) V63 low95 (by decide +kernel)
def g111Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffffffffffffffffff,0xf648eca538cb000000ff])),(BitVec.ofNat 152 (word80 [0x81481480aa04a81481,0x4648a4a5084999999999]))),((BitVec.ofNat 152 (word80 [0xfffc00fffc000fffc0,0xfa11a858ab3000f0000])),(BitVec.ofNat 152 (word80 [0x1590a62530b6c29906,0x6f811a818ab377777777]))),((BitVec.ofNat 152 (word80 [0xfffffff00000,0x1cf2190dcd100f00f00])),(BitVec.ofNat 152 (word80 [0x19e13809c02700de0b,0x808d2180dcd133333333]))),((BitVec.ofNat 152 (word80 [0xffffffffffff,0xf2152f483bb80f00f00f])),(BitVec.ofNat 152 (word80 [0x1e01c00e003800e00c,0x50b4031b022222222]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffff000000000000,0x116d0a38776f000fff0])),(BitVec.ofNat 152 (word80 [0x2000003000c0030010,0x1125000020644444444]))),(0xce9177e4005ffff0000,(BitVec.ofNat 152 (word80 [0xc00200c003000c0020,0x60043e000088888888]))),(0x0,0x0),(0x0,0x0)]
def g111C : List ColumnInfo := [(2,0,109,0,7),(4,0,107,0,7),(0,2,45,64,6),(1,0,110,0,6),(8,0,103,0,6),(3,0,108,0,5),(4,2,41,64,5),(6,0,105,0,5),(9,0,102,0,5),(10,0,101,0,5),(32,0,79,0,5),(64,0,45,0,5),(64,2,45,0,5),(12,0,99,0,4),(34,0,77,0,4),(36,0,75,0,4),(68,0,41,0,4)]
def g111A : List (List Nat) := [[]]
def g111D4 := limbs80 #[#[0x50d3254239e0976d4740,0x542d2615434c950f0954,0xe11534c950ac88650d32,0x55150c587654d43542d2,0xb198319154542ca60864,0x50d32d47265917319150,0xd46b1619434cb51e8564,0xe1d644cb51ac78458d32,0x50f518f186dc143d4639,0x8e7825db43d4639e0976,0x50d614ca3960f7259351,0xc0329dd26458532d8774,0x6aa4e9109e3660a8d8c0,0x3048608007ef1cb666c1,0x4]]
def g111D5 := limbs80 #[#[0x762b1a65a8f49534c950,0xcf6caa828139dc964d4,0x26fb9acaa04ef725954,0x409eaeda8e819e59550d,0x543e4a1a64a84ef72597,0xd50ed2a8992a1f2d8d32,0x35439caa286a87595350,0xd509f0eca1aa15e5d54,0x435439caa686a84fb765,0x54d50eb6c6a9aa15e5d7,0xd54543b5b92a8a857b74,0x455150e70c8aa2a15edc,0xcc64542f4b90c8a873b6,0x7259150d72c8322a1765,0x50d32506edb9ac8a85eb,0x37050d41dccec99283f1,0x959132d47e2a1a65a8df,0xf37050f51dcaec996a3b,0xad59143d476ab1a87a8d,0xeb564d0f519eaeca1ea3,0x33ddd163d467abb687a8,0x94f77359351dcee4b26a,0x65b9991614cbe2a1ac29,0x997cb7050d32bcee8b0a,0xa65e3551434cbe2b8a86,0x6995cd7550d32f1ca8a1,0x9a65d3551534cae7baa8,0xa8994ef7655132b9ee8a,0x322657adc1644cae6b9c,0xec0a1ef161d8143b9ae7,0x8a9a873e5d76050f78b8,0x92caa1cfb7059543e3aa],#[0xe7b12a93bdc965d0e77b,0x1603c004fb7058e549da,0x320bc2c0a42608c20074,0x6617c5c1544e11c400e4,0x8e22c841f47a1cc701a4,0xb22aca82849a25c94244,0xce32cc8314c22fcbc2d4,0x63ecf43b4e635cd4344,0x364bd2c4a52246d10435,0x5e56d585354a51d404e5,0x4582960a1a6700764585,0x102980a1820000000000,0x4081440800608183440d,0x3102c408118080c,0xc080c60800c0b18200,0x1ac60e18000000000000,0x6821310111820e09002,0x46080016024609180840,0x9841000028246080]]
def g111H5 := limbs80 #[#[0x8000b0c7801500088801,0x19364a49c880000e1002,0xe910000f0b26618e54a0,0x3092]]
def g111D6 := limbs80 #[#[0xe55150de54d50fa4c950,0x4cb51bdd8d41f94c941d,0x8532bd59351bd58f51f9,0x143f354d32f350d32f95,0x40fe54140bbd8954bed8,0xbf59540fdd4540fd505,0xfdd4740fe54340bfd954,0xfd9150df55150bf59740,0x58d50fed0d50fe50d50b,0x9150fe19150fed8d50fe,0xd41fed9150fe99150fe5,0x32fdd0f51fd50f51fd50,0x2fb59132fb95132fb551,0xfed8143fb59532fb9913,0xf55143f754d43fd58543,0xd9543bf59543ef95143e,0x5153bf59743ef55343bf,0x954bfd8154bfd9153df5,0x54bf58254bfd8d54fbd8,0xc0960e814814800bf58e,0x7c2c24fc921021dc34c5,0x4107b4e91b0354690c81,0xeb15552884cc92d1ba15,0xc9cf38a6ded359cb175c,0x3b45b881096053e879ae,0xd179f93be6a4b293d22a,0x260b606bdd60a8b4fe95,0x18203c380624161a1c09,0x8e1822180a26080f0e0,0x11616116a0342a258693,0xb041b804061e40d5826,0xc50582605862600c6e01],#[0xc1820018404040080002,0xc20608080101030a00b0,0x82d2224020b04003180,0xd120111201018b48890,0x24280416901a24280648,0x7003160d120111200922,0xd00d581a4041230410e4,0xa24018f46890081102c0,0x90243880f0064102c0c6,0x20484142081421410e,0x400708106080060c101,0x704c0c0040020830204,0xc1000c00404006]]
def g111H6 := limbs80 #[#[0x118e1781b2881a026431,0x496bbc5db4d820,0x1e88,0x4000001400000000011e,0x5400251800c3ca1595c4,0xa3d8a1c396c6e78549ce,0xb468a8123cd416c2c711,0x790e4ba980048762730,0x900d08000014f80,0x74e0000050e406000000,0xe47f8cc12e74ec650000,0x13409b0e3bacddbe1867,0x1000e7000344995001e,0x5bb5340000000007be5f,0xa0c4a597a8c32d06f99]]
def g111D7 := limbs80 #[#[0x751faa0fd4c7f4a1f950,0x87fd50ffa07f503da65f,0x3fca9fd54fea9ffd0ffa,0x439c8c04e210c0421200,0xe0921305ea6ab0d5c99,0x2130526120c12084c204,0x504db20205a212c300aa,0x14b0a180a2062ca86020,0x8608b2a180818a821308,0xc18a82120c14b0a18082,0x40e084a3062840e084]]
def g111H7 := limbs80 #[#[0x57e21008042846a0107c,0x1cc8000013da,0xa6569200078496007ac0,0x1843a492c18a29b8c,0x55cc000bfd6668ac0000,0x7dd10880000000001e5f,0xa9da8b84e00000170008,0x1001cacdfe86e70018d7,0x3460e988a1c6d148014,0x68000000000000208340,0xdb9200040001a600000e,0x21c63cc4000c2000008]]
def g111D8 (j : Nat) := if j=0 then 0x6202013f else 0
def g111H8 := limbs80 #[#[0xf300dd00000000615a,0xd70000007600180489,0xcabb2000000a000,0xd50000]]
def g111L : Nat → Packing
  | 4 => (19,4,5,0,0,7,0,g111D4)
  | 5 => (69,3,5,0,0,10,0,g111D5)
  | 6 => (55,2,5,0,0,11,0,g111D6)
  | 7 => (14,1,5,0,0,9,0,g111D7)
  | 8 => (1,0,5,0,0,0,0,g111D8)
  | _ => emptyPacking
def g111I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 4 29 5 9 5 0 g111H5
  | 6 => lookupWord 17 103 5 11 7 0 g111H6
  | 7 => lookupWord 13 89 5 10 6 0 g111H7
  | 8 => lookupWord 3 37 0 8 4 0 g111H8
  | _ => fun _ => none
def g111 : Forest := ⟨111,8,fun i => g111Y[i]?.getD (0,0),g111C,g111A,g111L,g111I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P4_0 : block g111 4 0 19=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g111B4 : block g111 4 0 19=true := g111P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P5_0 : block g111 5 0 3=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P5_3 : block g111 5 3 66=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g111B5 : block g111 5 0 69=true := (@block_merge g111 5 0 3 66 g111P5_0 g111P5_3)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P6_0 : block g111 6 0 13=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P6_13 : block g111 6 13 42=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g111B6 : block g111 6 0 55=true := (@block_merge g111 6 0 13 42 g111P6_0 g111P6_13)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P7_0 : block g111 7 0 6=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P7_6 : block g111 7 6 8=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g111B7 : block g111 7 0 14=true := (@block_merge g111 7 0 6 8 g111P7_0 g111P7_6)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P8_0 : block g111 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g111B8 : block g111 8 0 1=true := g111P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111T : checkedTables g111 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g111 0 0 0 = true)
  · exact (rfl : block g111 1 0 0 = true)
  · exact (rfl : block g111 2 0 0 = true)
  · exact (rfl : block g111 3 0 0 = true)
  · exact g111B4
  · exact g111B5
  · exact g111B6
  · exact g111B7
  · exact g111B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111G : graphValid g111 (boundsBefore K95) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low111 : Lower true (varsX 111) (graphGoal 111) 9 := lower_forest (g:=g111) (i:=0) (hints:=16778595) (before_sound K95 V95) g111G g111T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K111 := extendKnown K95 9 [(111,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V111 : Known true K111 := extend_ok (m:=111) V95 low111 (by decide +kernel)
def g119Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xf8001fffffff00ff1d,0x200797b23c000003f03f])),(BitVec.ofNat 152 (word80 [0x520d4825205216141d,0x390b2391451451451]))),((BitVec.ofNat 152 (word80 [0xffffe0007fffff0063,0x6e8ba06688003f000fc0])),(BitVec.ofNat 152 (word80 [0x604981360464242623,0x2609a066085145145145]))),((BitVec.ofNat 152 (word80 [0xffffffff800000009d,0x8e68c9a5400fc0fc0000])),(BitVec.ofNat 152 (word80 [0x800e00380178383815,0xa48c1a54030c30c30c3]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffffffa0,0x49e585ccf40000000fff])),(BitVec.ofNat 152 (word80 [0x49012404980000080,0x49e40508c6aaaaaaaaaa]))),((BitVec.ofNat 152 (word80 [0x91,0x75183e5b43f000fff000])),(BitVec.ofNat 152 (word80 [0xe003800e00404080,0x64102e4800c30c30c30c]))),((BitVec.ofNat 152 (word80 [0x4e,0x937660389bffff000000])),(BitVec.ofNat 152 (word80 [0x7001c007000808048,0x91260010930c30c30c30]))),(0x0,0x0),(0x0,0x0)]
def g119C : List ColumnInfo := [(1,0,118,0,7),(2,0,117,0,7),(4,0,115,0,7),(0,16,100,3,6),(16,0,103,0,6),(32,0,87,0,5),(64,0,55,0,5)]
def g119A : List (List Nat) := [[],[16,101]]
def g119D5 (j : Nat) := if j=0 then 0x4ef7259654 else 0
def g119D6 := limbs80 #[#[0xbd8954bb58854be58054,0x59654fbd8954cfd5254b,0x4018a1141f3185b2c0bf,0x81102628]]
def g119H6 (j : Nat) := if j=0 then 0x9 else 0
def g119D7 := limbs80 #[#[0x47888807f953faa9fc54,0x2a547436598a1d90ea61,0x190e]]
def g119H7 := limbs80 #[#[0x92000080c8007564,0x610000000023]]
def g119D8 (j : Nat) := if j=0 then 0x468817f else 0
def g119H8 (j : Nat) := if j=0 then 0x128c808cc0000 else 0
def g119L : Nat → Packing
  | 5 => (1,3,3,0,0,0,0,g119D5)
  | 6 => (6,2,3,0,0,6,0,g119D6)
  | 7 => (3,1,3,0,0,7,0,g119D7)
  | 8 => (1,0,3,0,0,0,0,g119D8)
  | _ => emptyPacking
def g119I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 2 0 4 0 0 g119H6
  | 7 => lookupWord 1 19 0 8 3 1 g119H7
  | 8 => lookupWord 1 11 0 7 2 1 g119H8
  | _ => fun _ => none
def g119 : Forest := ⟨119,8,fun i => g119Y[i]?.getD (0,0),g119C,g119A,g119L,g119I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P5_0 : block g119 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g119B5 : block g119 5 0 1=true := g119P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P6_0 : block g119 6 0 4=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P6_4 : block g119 6 4 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g119B6 : block g119 6 0 6=true := (@block_merge g119 6 0 4 2 g119P6_0 g119P6_4)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P7_0 : block g119 7 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g119B7 : block g119 7 0 3=true := g119P7_0
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
theorem g119G : graphValid g119 (boundsBefore K111) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low119 : Lower true (varsX 119) (graphGoal 119) 9 := lower_forest (g:=g119) (i:=0) (hints:=16778564) (before_sound K111 V111) g119G g119T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K119 := extendKnown K111 9 [(119,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V119 : Known true K119 := extend_ok (m:=119) V111 low119 (by decide +kernel)
def g123Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffffff83fffff242e8,0x44f46d0000000fe03fff])),(BitVec.ofNat 152 (word80 [0x80a4010808040240a0,0x4444d42850a142850a1]))),((BitVec.ofNat 152 (word80 [0xffffc1ffe06b488,0xfcbc20003f8001fc000])),(BitVec.ofNat 152 (word80 [0x12c08a00410822b088,0x78b40162c58b162c58b]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfff000001ffffbd84e,0x91211a01fc07f000007f])),(BitVec.ofNat 152 (word80 [0x3002c10805001804c,0x1121120c183060c18306]))),((BitVec.ofNat 152 (word80 [0xffffffffe0000804f6,0x691ab3000000001fff80])),(BitVec.ofNat 152 (word80 [0x240930001260480456,0x6810b2a952a54a952a54]))),((BitVec.ofNat 152 (word80 [0x91711,0xa28774fe0007ffe00000])),(BitVec.ofNat 152 (word80 [0x3801c0210380881601,0xa282203060c183060c18]))),((BitVec.ofNat 152 (word80 [0x4e917,0x7e4005fffff800000000])),(BitVec.ofNat 152 (word80 [0xc00e00421c01044912,0x484005c183060c183060]))),(0x0,0x0),(0x0,0x0)]
def g123C : List ColumnInfo := [(1,0,122,0,7),(2,0,121,0,7),(8,0,115,0,7),(16,0,107,0,7),(32,0,91,0,7),(64,0,59,0,7),(0,2,41,80,6),(0,16,104,3,6),(1,16,104,2,5),(2,16,104,1,5),(17,0,106,0,5),(18,0,105,0,5),(64,2,41,16,5),(66,0,57,0,5),(3,0,104,0,4),(3,16,104,0,4),(9,0,114,0,4),(10,0,113,0,4),(33,0,90,0,4),(34,0,89,0,4),(40,0,83,0,4),(72,0,51,0,4),(96,0,27,0,4)]
def g123A : List (List Nat) := [[],[83],[96,65],[96,65,83]]
def g123D5 := limbs80 #[#[0x50940483aa5954250120,0x483ca5514254120eab65,0x1d372595208ef825d954,0x10185b54f032b]]
def g123D6 := limbs80 #[#[0x25fba2ca907a94250120,0xdbec6a12217edc14244,0x837db2a80906f9655012,0x20fd6e4a8241fa509504,0x4837cb22a09077954541,0x520bf6e8a8241bed9150,0x2483d6aa284906bf6450,0x5120ddecaa1241bb5954,0x644827fbaac8904fd765,0x59520bdee4b2a413f5d7,0x16548377b92ca905bf74,0x459520d7ee8b2a41af1d,0xd9425427eba6ca904ff7,0x74d8950b7ee8b12a13f9,0x5c3644867eba6c090cfd,0xf75585429faebb02853f,0x1a8c85e2810858260057,0x6c32978ae50249087638,0x2e9446a2906803c9c8de,0x1084b458ab956a450a69,0x101a2070c042019c120,0x4041c206941050400000,0x10059410000404101100,0x1028810000404010040,0x3081000019]]
def g123H6 := limbs80 #[#[0xf17a9c00000121000005,0x6000d172000440008]]
def g123D7 := limbs80 #[#[0xe54120fe50120b7d8d10,0xd9120bf59120fb50920f,0x8950bfd9520bf59520bf,0x142bfd9121bfd8121bfd,0x20ff50520ff50910bfd8,0xff55120ff58520ff545,0xff50930ff59520ff5912,0xfd8950ff58950ff50950,0x58542ff58142ff50931f,0xd47f0b911214814800ff,0x50a7f49087cfb1b83024,0x36c6a2cbd86af9592ad5,0x1e00c1607be6796ec1c7,0x84b0872440424842e4c4,0x94209c14048310c31a18,0x40728488070c14181804,0x7080c0085070c0c0e548,0x4a1018120395201c3250,0x5801c30303922a220386,0xc383003088a101a81844,0x44187081c305038d0141,0x203234230d0c10626143,0x2885091048216201111c,0xa880141110a0e1952091,0xc306140220ca90488840,0x4b0908c5091084805442,0x4c886]]
def g123H7 := limbs80 #[#[0x8c112,0x438000000002814000,0x18640000038440000,0x43d41c00000087400000,0x2a13b1800000221d,0x105c0000000000000000,0x3c4000,0x281b618000,0x30580000000000,0x1d1400000000000000,0xc20000002070,0x0,0x0,0x0,0x0,0x824000000000538e2400,0x0,0x0,0x1400000000c4c00,0x68000000000003c7c000,0x1c,0x384800000191000000,0x0,0xc00000102c0000028040,0x312,0x2c50000000,0x0,0x42800000000000000,0x478000000000002c60,0x32c0000000,0x0,0x2080000000000000],#[0x303300880ec540000000,0x2034c6e51800141000]]
def g123D8 := limbs80 #[#[0xd21fea87f4c3fa41fd10,0xd210c024007f50bfa63f,0x10882640e230f161cea5,0x2259222891464009648e,0x98c23071648a3221300,0x18040899222cc2059018,0x1c65258e]]
def g123H8 := limbs80 #[#[0x44800000001d8ac1280,0x528180032c0000000000,0x1a5c002130018,0x40100000000000000000,0x4f51e40001d800000000,0xa18c00000784000001c,0x5ce001c44000009,0x287000d04000c3000000,0xb00000122c0000064600,0x2e5800a1ec995,0x92a0240000031a000000,0x14c001e6000143,0x3c278a0000000000000,0xccfd9c116b6e9e35e0e0,0xf4400000000000001,0xedc00000000518002b1]]
def g123D9 (j : Nat) := if j=0 then 0xa4188201bf else 0
def g123H9 := limbs80 #[#[0x86b86100014005,0x78800dc0000000000,0xa000000025d900227460,0xa00036200000030,0x158006080]]
def g123L : Nat → Packing
  | 5 => (5,4,5,0,0,6,0,g123D5)
  | 6 => (33,3,5,0,0,9,0,g123D6)
  | 7 => (26,2,5,0,0,11,0,g123D7)
  | 8 => (7,1,5,0,0,9,0,g123D8)
  | 9 => (1,0,5,0,0,0,0,g123D9)
  | _ => emptyPacking
def g123I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 2 17 3 9 3 2 g123H6
  | 7 => lookupWord 11 227 2 12 6 2 g123H7
  | 8 => lookupWord 11 113 3 11 5 2 g123H8
  | 9 => lookupWord 3 41 1 9 3 2 g123H9
  | _ => fun _ => none
def g123 : Forest := ⟨123,9,fun i => g123Y[i]?.getD (0,0),g123C,g123A,g123L,g123I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P5_0 : block g123 5 0 5=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g123B5 : block g123 5 0 5=true := g123P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P6_0 : block g123 6 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P6_2 : block g123 6 2 31=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g123B6 : block g123 6 0 33=true := (@block_merge g123 6 0 2 31 g123P6_0 g123P6_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P7_0 : block g123 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P7_1 : block g123 7 1 11=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P7_12 : block g123 7 12 14=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g123B7 : block g123 7 0 26=true := (@block_merge g123 7 0 1 25 g123P7_0 (@block_merge g123 7 1 11 14 g123P7_1 g123P7_12))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P8_0 : block g123 8 0 7=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g123B8 : block g123 8 0 7=true := g123P8_0
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
theorem low123 : Lower true (varsX 123) (graphGoal 123) 10 := lower_forest (g:=g123) (i:=0) (hints:=16777283) (before_sound K119 V119) g123G g123T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K123 := extendKnown K119 10 [(123,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V123 : Known true K123 := extend_ok (m:=123) V119 low123 (by decide +kernel)
def g125Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfffffffffffffffff6,0x88e80739cb0000007fff])),(BitVec.ofNat 152 (word80 [0xa402900400802006,0x88200708484a5294a529]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfff0003ffe01fff00e,0x7249cc0cf0003e0f8000])),(BitVec.ofNat 152 (word80 [0xac06b0128340a416e,0x5049c00cd018c6318c63]))),((BitVec.ofNat 152 (word80 [0xffffffc00001fffff3,0x4ccf90e21807c1f0001f])),(BitVec.ofNat 152 (word80 [0x13004c01b0580c8240,0x40cd80e2101084210842]))),((BitVec.ofNat 152 (word80 [0xfffffffffffe000000,0x94f7681bb100000003e0])),(BitVec.ofNat 152 (word80 [0x5c097025c0612f0380,0x14d76813b1b5ad6b5ad6]))),((BitVec.ofNat 152 (word80 [1,0x1710a38776f801fffc00])),(BitVec.ofNat 152 (word80 [0x600180060080300401,0x7002001222108421084]))),((BitVec.ofNat 152 (word80 [0xc,0xe9177e4005fffe000000])),(BitVec.ofNat 152 (word80 [0x800e00380101c00800,0xa8121e0005c6318c6318]))),(0x0,0x0),(0x0,0x0)]
def g125C : List ColumnInfo := [(4,0,121,0,7),(8,0,117,0,7),(16,0,109,0,7),(0,16,108,1,6),(64,0,61,0,6),(1,0,108,0,5),(1,16,108,0,5),(32,0,93,0,5)]
def g125A : List (List Nat) := [[]]
def g125D5 := limbs80 #[#[0x26ebb4a9185d77155230,0x9dee4b2a813ddc56550,0x2ebb8aa8a1cf7715974,0xf624c3]]
def g125D6 := limbs80 #[#[0x755230bdd8554b759230,0x59540fe54140f795230f,0x5150bf59740bfd9540bf,0x154f755143bfd9150df5,0xbf58254fdd8554bfd8,0xa0907b706a503b2b2010,0x61201d6422e42cbc0b0,0xe18010062080431241b,0xc41001188262021882d2]]
def g125H6 := limbs80 #[#[0x9af900da0000000a4000,0x6000000007]]
def g125D7 := limbs80 #[#[0xd50ffa07f503ba87de30,0x38291a0b007f953faa9f,0x2c339644b0d912a25647,0xce9512c32144bb0ce951,0xa69152e3bad2448]]
def g125H7 := limbs80 #[#[0x2dd34d5c60077005b508,0x86900003ceaf300f100f,0xb]]
def g125D8 (j : Nat) := if j=0 then 0x681117f else 0
def g125H8 := limbs80 #[#[0x0,0x36800,0x6e0000000000000100,0x5000000000000,0x0,0x0,0x1c00000000,0x0,0x3580000000000000000,0x540000000000000000]]
def g125L : Nat → Packing
  | 5 => (6,3,3,0,0,5,0,g125D5)
  | 6 => (14,2,3,0,0,8,0,g125D6)
  | 7 => (7,1,3,0,0,8,0,g125D7)
  | 8 => (1,0,3,0,0,0,0,g125D8)
  | _ => emptyPacking
def g125I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 17 0 7 3 0 g125H6
  | 7 => lookupWord 3 19 4 8 4 0 g125H7
  | 8 => lookupWord 1 113 0 7 3 0 g125H8
  | _ => fun _ => none
def g125 : Forest := ⟨125,8,fun i => g125Y[i]?.getD (0,0),g125C,g125A,g125L,g125I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P5_0 : block g125 5 0 6=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g125B5 : block g125 5 0 6=true := g125P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P6_0 : block g125 6 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P6_2 : block g125 6 2 12=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g125B6 : block g125 6 0 14=true := (@block_merge g125 6 0 2 12 g125P6_0 g125P6_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P7_0 : block g125 7 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P7_2 : block g125 7 2 5=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g125B7 : block g125 7 0 7=true := (@block_merge g125 7 0 2 5 g125P7_0 g125P7_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P8_0 : block g125 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g125B8 : block g125 8 0 1=true := g125P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125T : checkedTables g125 8 := by
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
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125G : graphValid g125 (boundsBefore K123) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low125 : Lower true (varsX 125) (graphGoal 125) 9 := lower_forest (g:=g125) (i:=0) (hints:=33555715) (before_sound K123 V123) g125G g125T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K125 := extendKnown K123 9 [(125,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V125 : Known true K125 := extend_ok (m:=125) V123 low125 (by decide +kernel)
def g126Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfc00fffffffffffffe,0xd60912f74a68000f801f])),(BitVec.ofNat 152 (word80 [0x481610542128429028,0x540812f642414a5294a5]))),((BitVec.ofNat 152 (word80 [0xfffffffe0003fff801,0x60153daec91001f003e0])),(BitVec.ofNat 152 (word80 [0x90a402980db01320cd,0x601538aa4810c6318c63]))),((BitVec.ofNat 152 (word80 [0xfffffffc000001,0x39c4f2134e803e007c00])),(BitVec.ofNat 152 (word80 [0xe13804e009c01bc171,0x3184b2034e00c6318c63]))),((BitVec.ofNat 152 (word80 [0xffffffffffffff,0x428bea0b99e80000001f])),(BitVec.ofNat 152 (word80 [0x1c0a7014e029c0181,0x283e80999aeb5ad6b5a]))),((BitVec.ofNat 152 (word80 [0xffff00000000000001,0x22fa117cb687c0007fe0])),(BitVec.ofNat 152 (word80 [0x38007000e00200,0x2680154908318c6318c]))),(0x9d26ecc07137ffff8000,(BitVec.ofNat 152 (word80 [0x200c0018003000400,0x88024400212421084210]))),(0x0,0x0),(0x0,0x0)]
def g126C : List ColumnInfo := [(4,0,122,0,7)]
def g126A : List (List Nat) := [[],[50]]
def g126D7 (j : Nat) := if j=0 then 0x7f else 0
def g126L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g126D7)
  | _ => emptyPacking
def g126I (_ _ : Nat) : Option (Nat × Nat) := none
def g126 : Forest := ⟨126,7,fun i => g126Y[i]?.getD (0,0),g126C,g126A,g126L,g126I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7_0 : block g126 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g126B7 : block g126 7 0 1=true := g126P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126T : checkedTables g126 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g126 0 0 0 = true)
  · exact (rfl : block g126 1 0 0 = true)
  · exact (rfl : block g126 2 0 0 = true)
  · exact (rfl : block g126 3 0 0 = true)
  · exact (rfl : block g126 4 0 0 = true)
  · exact (rfl : block g126 5 0 0 = true)
  · exact (rfl : block g126 6 0 0 = true)
  · exact g126B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126G : graphValid g126 (boundsBefore K125) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low126 : Lower true (varsX 126) (graphGoal 126) 8 := lower_forest (g:=g126) (i:=0) (hints:=18961728) (before_sound K125 V125) g126G g126T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K126 := extendKnown K125 8 [(126,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V126 : Known true K126 := extend_ok (m:=126) V125 low126 (by decide +kernel)
def g159Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xe003ffffffffffffff,0xfff04daced850000f0ff])),(BitVec.ofNat 152 (word80 [0x40580a002a00940148,0xa70450c410511111111]))),((BitVec.ofNat 152 (word80 [0xfffc007fff0001fffc,0x3df427164c000f0f00])),(BitVec.ofNat 152 (word80 [0x829053014c06d80990,0x3335e426144c33333333]))),((BitVec.ofNat 152 (word80 [0x7ffffffe0000,0x86557cdf800f00000])),(BitVec.ofNat 152 (word80 [0xce19c2a7054e0ade1,0x5c086557cdf877777777]))),((BitVec.ofNat 152 (word80 [0x7fffffffffff,0xff968d73ae0b0f00000f])),(BitVec.ofNat 152 (word80 [0x1702e033806700ce02,0x60068873ae0a66666666]))),((BitVec.ofNat 152 (word80 [0xffffff800000000000,0x8bacf93a6f0000ff0])),(BitVec.ofNat 152 (word80 [0x1803003c007800f003,0x80081ac182a244444444]))),(0x0,0x0),(0x0,0x0),(0x674250407afffff000,(BitVec.ofNat 152 (word80 [0x400080010000,0x88888888]))),(0x0,0x0)]
def g159C : List ColumnInfo := [(4,0,155,0,7),(1,0,158,0,6),(2,0,157,0,6),(8,0,151,0,6),(16,0,143,0,6),(0,4,27,128,5),(5,0,154,0,5),(6,0,153,0,5),(9,0,150,0,5),(10,0,149,0,5),(18,0,141,0,5),(20,0,139,0,5),(22,0,137,0,4),(128,0,27,0,4),(128,4,27,0,4)]
def g159A : List (List Nat) := [[],[64,49]]
def g159D3 := limbs80 #[#[0xa82219818750f5250110,0x85589504426832642ac4,0x6304c8650]]
def g159D4 := limbs80 #[#[0x5c752442786027548510,0x44233e0d76d49109e380,0x50f52501108af845db52,0x50110ba184d4940443e0,0xf8143589404427861f52,0x5c940442e8e116250110,0x443645d54350110f8143,0x5514254110d937550d40,0x54110e636558950443c8,0xf115450d50442d821562,0x195504427421d4354110,0x442cc6106554110b5183,0x6027550910aa48655142,0xd4910dc1435c35244278,0x9e3845c35244370e0d70,0x5db5244239e1974d4910,0x44269e1176d49109c783,0x60c7558910d877450d62,0x551109a5841d56244271,0xc35655d0654427860372,0x5d2654821de1d6519510,0x54239e0576d49408e781,0xe0d70995218e7815d362,0x583528cf835c36254633,0xf060240c030023361373,0xc33180b4441f0e054240,0x4a44f261248c431e0e46,0x1c4dc6b34184bc5b2c15,0x10c83401f4f4773a,0x9a1040010e0800000,0x98200000,0x8e08000]]
def g159H4 (j : Nat) := if j=0 then 0x16000f25000000 else 0
def g159D5 := limbs80 #[#[0xaf0b86a4887914350110,0xfc242a822133dcd60d4,0x4373b2a42886e5654851,0x10be6e0a8a21799d5214,0x442f8b86a2885e772545,0x910bd2e1a92219dd9751,0x544276bb6a4885e571d4,0x11097ee8b2a2137dcd6,0x40443f0b1280887e3525,0x50110f62a8a0221f85c9,0x540442f8baa80887b364,0x254110fc284a82217cdd,0xc950443f0b12a0887e35,0x7354110fa286a8221f8d,0xd5150443b8aa2a0887d3,0x6554110be6e8a8221dc,0x955142443b9b2aa08877,0xe67550910f4ec8a1221e,0xf85c352442f2bb284885,0x5e574d4910f8a87a9221,0x179ddb52442f2bb6a488,0x85e77458910f8a86b122,0x21b9d956244372b2ac48,0x887d37050d10bc8eab12,0x2213d1d954442f3b92a8,0x8885f170d51109eeecaa,0x2a21795c865442f2b96c,0xca885b57419510baae63,0xb2a2179dc9654433ab28,0xcca885b77459510baee6,0x6a8241795cb654433bb2,0x8aa8907695454120f96e],#[0xe932a413b5c665482f3b,0xb86a4a073954541409da,0xee2b2a813b5db52502f4,0x7b1ea4a86cf63485509e,0xdae3b12a1b3d8f625436,0x67b96c6a84ed74d89509,0x9eee2b26a1375d363543,0x676b84ca90de77054521,0x29bee6b06a33b5c36254,0x4a77b8ac1a95cf735835,0x529dee8b06a5b3dcd60d,0x2106a14036004ef70587,0x439023d8dc340c42e0ac,0x6297e5914a4f9324991a,0x96a4e8d20c791ca6f996,0xbcad8afab2a9a8ca0274,0xe2b62d5b4acfb32c62fe,0xfc330640cfcbd8f33a4,0x2ecaf28c9722c7f1cc59,0x515394b52141ced34cc7,0x6cda766d8f60d775ad5f,0x88615825fd78dd772dbf,0xa01270b807946458e62d,0x60800000240015306882,0xc0870400000000002,0x7a6106a6153040260820,0x1000260800130409008,0x8000001982301008024,0x130438203420107063b4,0x3824c1001020,0x80000381c0087040000,0x400000000000000001c],#[0x6]]
def g159H5 := limbs80 #[#[0x0,0x0,0x0,0x1140,0x187000,0x6000000000000000000,0xe4800000000000000006,0xc2c00000001,0x0,0x0,0x0,0x28400000,0x0,0x0,0x28b800000000,0x0,0x0,0x0,0x40000000000000000000,0x183,0x0,0x390000000000000,0x0,0x0,0x460000000024dc890000,0x36c000000003,0x93a00000,0x0,0x0,0x1c2800000,0x0,0x0],#[0x0,0xc5000000,0x0,0x0,0x1618001c5000000,0x1500000000,0x0,0x1350000000,0x0,0x3000000000000000000,0x4bc000000000000000,0x0,0x0,0x0,0x1040000000000,0x0,0x0,0x0,0x1870000,0x3d2800000,0x129,0x0,0x0,0x41c0000000000000599,0x2e20000000000000,0x11000001e7f020000000,0x23da4400000000003,0x0,0x0,0x63c00000a34000000000,0x44c63000123800514,0x0],#[0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x8100024c000000000000,0x6,0x0,0x2100000000000,0x0,0x0,0x4b,0x0,0x0,0x6d500000000000000,0x0,0x0,0x0,0x0,0x0,0x0,0x918,0x0,0x0,0x0,0xf4c],#[0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x28c000000000000,0x1810]]
def g159D6 := limbs80 #[#[0xc50110bb58910f948510,0xd4910f950910fc54110f,0x4b10f550d10f958910f9,0x520bb59120fa54120f9d,0x21b7d8d50bbd8950bb99,0x2bbd8951bb99521f9545,0xfe54110bb58752bb5835,0xbd4910fdd4510fd54510,0xd9510bf59510fb58910f,0x9110fdd5110fd55110bf,0x510fd19510fdd9110fd5,0x20fdd9510fd99510fd59,0xfe54140fb55120fb545,0xbf59540fb58940fbd494,0xfd8550fb48550bfd9540,0xd8d50fbd8950fbd4950b,0x9150dfd5150df55150f7,0x151bf59350bf58750bfd,0x51fbd8951fbd4951bfd8,0xfb58752fb58352bf583,0x5c2583f06609c0c00c00,0x558a212c234408750d21,0xff1ec39c6d8d21862dc,0x629a5049a92923444484,0x4e66cc91863005d0b115,0x7a4f01d43966f0d99ad3,0x518a2843885906a013ea,0x3d01cec9b52f2524928f,0x6040616042825151c194,0xba0f407121407150d861,0x40c7068515069c582908,0xe01002d01d0684d50706],#[0x200b50949b5067143870,0x1261607086b2d066b015,0x8020c3842c412008481c,0x2806a028062820062881,0x9840a02840a01a0504a0,0x1c1040a01a00a89a01a8,0x2163042827023247063,0x28014670e18a00428610,0x841c38066814066c6306,0x70601c10a18019c0880,0x21b10019a38428200610,0xa0a628418201c]]
def g159H6 := limbs80 #[#[0x2482a80a27384a90ca6,0x4840002c000110080c66,0xe801a28624800000000,0x59380a389800423d,0x50580000061680000000,0x39330dc4a896000,0x7b2b80000001500059c0,0x992d2114b58138068630,0x306f998003a701d,0xff8f2103a40006970000,0x8000000000003a500009,0x85000317f088cb8a0a00,0xe80000008b80000021a9,0xea6ed9b25aac00000054,0x2a8003292e3e0879f0a1,0x70928e000554284a,0x19200038ca9800,0x28c2027582cd800,0xa000000460b1b00041e8,0x8000001072e0319483c5,0x6288b1520006a32a7994,0x38a91d19e0a9ba8ed5e,0xd1469080000f898e1b80,0xaa2a05a2000282e1a41c,0xb4918837497a60110d16,0x5a2f8d6483d8e15bc9d2]]
def g159D7 := limbs80 #[#[0xf52f690fb483ee21f510,0xa3ff50fea87f503fa21e,0x87341245e1a007fd47fa,0x83152081230f96d2ed42,0x815d14a8e2bb48309042,0xae829023a0850990375,0x14c14290504385710504,0x14c14e15c]]
def g159H7 := limbs80 #[#[0x5600203402210216500a,0xa14576b6060380575020,0x3246d287b1814a000006,0xc24404dacd5fa9a69701,0x14a200026a001580d6d1,0xe7a2ab5c001bc000b66f,0x432001857851db000520,0xba3627c004860d6f0b82,0x20cd80040d5c7e9d7bec,0x2680009935124f0a5b10,0x9d7df48c003d1001,0xb800b05421cb70300e00,0xfc80000021cf40ea4c,0x1a7892000c0b3d1ed0,0x20be6fa8800000]]
def g159D8 (j : Nat) := if j=0 then 0x9a8013f else 0
def g159H8 := limbs80 #[#[0xc80137f3000018899100,0x79400ca005112a67289,0x58f426951003f0590,0x5e800000004f20e]]
def g159L : Nat → Packing
  | 3 => (3,5,4,0,0,4,0,g159D3)
  | 4 => (39,4,4,0,0,9,0,g159D4)
  | 5 => (89,3,4,0,0,10,0,g159D5)
  | 6 => (57,2,4,0,0,11,0,g159D6)
  | 7 => (11,1,4,0,0,9,0,g159D7)
  | 8 => (1,0,4,0,0,0,0,g159D8)
  | _ => emptyPacking
def g159I : Nat → Nat → Option (Nat × Nat)
  | 4 => lookupWord 1 11 0 6 2 0 g159H4
  | 5 => lookupWord 12 797 0 11 6 1 g159H5
  | 6 => lookupWord 27 163 5 12 7 1 g159H6
  | 7 => lookupWord 18 97 6 11 6 1 g159H7
  | 8 => lookupWord 5 31 4 9 4 1 g159H8
  | _ => fun _ => none
def g159 : Forest := ⟨159,8,fun i => g159Y[i]?.getD (0,0),g159C,g159A,g159L,g159I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g159P3_0 : block g159 3 0 3=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g159B3 : block g159 3 0 3=true := g159P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g159P4_0 : block g159 4 0 39=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g159B4 : block g159 4 0 39=true := g159P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g159P5_0 : block g159 5 0 3=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g159P5_3 : block g159 5 3 86=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g159B5 : block g159 5 0 89=true := (@block_merge g159 5 0 3 86 g159P5_0 g159P5_3)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g159P6_0 : block g159 6 0 19=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g159P6_19 : block g159 6 19 38=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g159B6 : block g159 6 0 57=true := (@block_merge g159 6 0 19 38 g159P6_0 g159P6_19)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g159P7_0 : block g159 7 0 5=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g159P7_5 : block g159 7 5 6=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g159B7 : block g159 7 0 11=true := (@block_merge g159 7 0 5 6 g159P7_0 g159P7_5)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g159P8_0 : block g159 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g159B8 : block g159 8 0 1=true := g159P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g159T : checkedTables g159 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g159 0 0 0 = true)
  · exact (rfl : block g159 1 0 0 = true)
  · exact (rfl : block g159 2 0 0 = true)
  · exact g159B3
  · exact g159B4
  · exact g159B5
  · exact g159B6
  · exact g159B7
  · exact g159B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g159G : graphValid g159 (boundsBefore K126) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low159 : Lower true (varsX 159) (graphGoal 159) 9 := lower_forest (g:=g159) (i:=0) (hints:=1859) (before_sound K126 V126) g159G g159T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K159 := extendKnown K126 9 [(159,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V159 : Known true K159 := extend_ok (m:=159) V126 low159 (by decide +kernel)
def g175Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffffffffffffffffff,0xfa61e88178cb000f00ff])),(BitVec.ofNat 152 (word80 [0x1481400a804a01481,0x4a40a081484911111111]))),((BitVec.ofNat 152 (word80 [0xfffc00fffc000fffc0,0x7800d87cab700f00000])),(BitVec.ofNat 152 (word80 [0x1590a62530b6c29906,0x67800d81cab777777777]))),((BitVec.ofNat 152 (word80 [0xfffffff00000,0x1ce23b09cd10f000f00])),(BitVec.ofNat 152 (word80 [0x19e13809c02700de0b,0x80c423909cd133333333]))),((BitVec.ofNat 152 (word80 [0xffffffffffff,0xf2143f483bb8f000f00f])),(BitVec.ofNat 152 (word80 [0x1e01c00e003800e00c,0x40f4031b022222222]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffff000000000000,0x117d0a387760000fff0])),(BitVec.ofNat 152 (word80 [0xa00000b002c00b0010,0x11350220206cccccccc]))),(0x0,0x0),(0xce9177e4005ffff0000,(BitVec.ofNat 152 (word80 [0xc00200c003000c0020,0x29102e000088888888]))),(0x0,0x0)]
def g175C : List ColumnInfo := [(4,0,171,0,7)]
def g175A : List (List Nat) := [[],[48]]
def g175D7 (j : Nat) := if j=0 then 0x7f else 0
def g175L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g175D7)
  | _ => emptyPacking
def g175I (_ _ : Nat) : Option (Nat × Nat) := none
def g175 : Forest := ⟨175,7,fun i => g175Y[i]?.getD (0,0),g175C,g175A,g175L,g175I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175P7_0 : block g175 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g175B7 : block g175 7 0 1=true := g175P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175T : checkedTables g175 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g175 0 0 0 = true)
  · exact (rfl : block g175 1 0 0 = true)
  · exact (rfl : block g175 2 0 0 = true)
  · exact (rfl : block g175 3 0 0 = true)
  · exact (rfl : block g175 4 0 0 = true)
  · exact (rfl : block g175 5 0 0 = true)
  · exact (rfl : block g175 6 0 0 = true)
  · exact g175B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175G : graphValid g175 (boundsBefore K159) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low175 : Lower true (varsX 175) (graphGoal 175) 8 := lower_forest (g:=g175) (i:=0) (hints:=1395) (before_sound K159 V159) g175G g175T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K175 := extendKnown K159 8 [(175,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V175 : Known true K175 := extend_ok (m:=175) V159 low175 (by decide +kernel)
def g183Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfff0007ffffff00ff5,0xb261513c2a0001f07c1f])),(BitVec.ofNat 152 (word80 [0x2a035012805216141,0xb0605114080842108421]))),((BitVec.ofNat 152 (word80 [0xffffff8003fffff002,0x17e8d44785003e0003e0])),(BitVec.ofNat 152 (word80 [0x44c12609b046424262,0x1360d40781294a5294a5]))),((BitVec.ofNat 152 (word80 [0xfffffffffc00000009,0xd8c2c299d107c00f8000])),(BitVec.ofNat 152 (word80 [0x17003801c017838381,0x98c2c018d118c6318c63]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffffffffffffa,0x4fe283ab8f8000003ff])),(BitVec.ofNat 152 (word80 [0x980240120098000008,0x48a2828305294a5294a]))),((BitVec.ofNat 152 (word80 [9,0x1711a3877600000ffc00])),(BitVec.ofNat 152 (word80 [0xe00b805c02e0040408,0x711228326e739ce739c]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [4,0xe9177e4005fffff00000])),(BitVec.ofNat 152 (word80 [0xc00600300080804,0x40150240048421084210]))),(0x0,0x0)]
def g183C : List ColumnInfo := [(1,0,182,0,7),(4,0,179,0,7),(0,32,146,5,6),(2,0,181,0,6),(32,0,151,0,6),(16,0,167,0,5),(34,0,149,0,5),(128,0,55,0,5),(17,0,166,0,4),(130,0,53,0,4)]
def g183A : List (List Nat) := [[]]
def g183D5 := limbs80 #[#[0x71fb2aa898f555354531,0x1eaaa7a8e633ddc5654c,0x4f3ab2ea398dd573d473,0x53d6aa9b0aa77c5c0615,0xe35cafb299a06b654d85,0x183b]]
def g183D6 := limbs80 #[#[0xb58853bd58453be58053,0x54531d7d4e53bdd8553b,0x5131f794d31f754d31fd,0x731bfd9531bf59531ef5,0x31ef55331f754f31fdd4,0x1df54f51df54d51bf597,0xfdd8553fd18553bf58f5,0xf95153ef55153bfd8553,0x95253ef55253bf58653e,0x481e0a82400bf59653ef,0x509c4b241147e3c1b0c0,0xf1d4e46c34998c05a2b9,0x2e0386390149a350e843,0x608e08a3e01e008f804,0x60860800060800003820,0x38204608f18400608000,0x182382]]
def g183H6 := limbs80 #[#[0x90006700e423822500,0x98d10026]]
def g183D7 := limbs80 #[#[0xd51ff98ff4c77ca9bd54,0xa7fe53fea9ff14ffea3f,0xd0bf4d9f0ba3e0f803fe,0x478c0c291228c059d445,0x82453c60628a72c60614,0x828c1239451818e314d1,0x8a3028e410ce58c07194,0xa41460918e41]]
def g183H7 := limbs80 #[#[0x45187661c0340880,0xd200d3800014242803b2,0x132c00fa80000f39beae,0x78e350702d636c1f1496,0xad700298000058400009,0x4]]
def g183D8 (j : Nat) := if j=0 then 0x3421017f else 0
def g183H8 := limbs80 #[#[0x330068000086f00089a2,0x1100000000a500000000,0x4a7000000000000]]
def g183L : Nat → Packing
  | 5 => (9,3,4,0,0,6,0,g183D5)
  | 6 => (27,2,4,0,0,9,0,g183D6)
  | 7 => (10,1,4,0,0,9,0,g183D7)
  | 8 => (1,0,4,0,0,0,0,g183D8)
  | _ => emptyPacking
def g183I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 2 17 0 8 4 0 g183H6
  | 7 => lookupWord 6 41 6 9 5 0 g183H7
  | 8 => lookupWord 2 29 0 8 4 0 g183H8
  | _ => fun _ => none
def g183 : Forest := ⟨183,8,fun i => g183Y[i]?.getD (0,0),g183C,g183A,g183L,g183I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183P5_0 : block g183 5 0 9=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g183B5 : block g183 5 0 9=true := g183P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183P6_0 : block g183 6 0 5=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183P6_5 : block g183 6 5 22=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g183B6 : block g183 6 0 27=true := (@block_merge g183 6 0 5 22 g183P6_0 g183P6_5)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183P7_0 : block g183 7 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183P7_2 : block g183 7 2 8=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g183B7 : block g183 7 0 10=true := (@block_merge g183 7 0 2 8 g183P7_0 g183P7_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183P8_0 : block g183 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g183B8 : block g183 8 0 1=true := g183P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183T : checkedTables g183 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g183 0 0 0 = true)
  · exact (rfl : block g183 1 0 0 = true)
  · exact (rfl : block g183 2 0 0 = true)
  · exact (rfl : block g183 3 0 0 = true)
  · exact (rfl : block g183 4 0 0 = true)
  · exact g183B5
  · exact g183B6
  · exact g183B7
  · exact g183B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183G : graphValid g183 (boundsBefore K175) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low183 : Lower true (varsX 183) (graphGoal 183) 9 := lower_forest (g:=g183) (i:=0) (hints:=1348) (before_sound K175 V175) g183G g183T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K183 := extendKnown K175 9 [(183,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V183 : Known true K183 := extend_ok (m:=183) V175 low183 (by decide +kernel)
def g187Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3fffffc1fffff622e,0xa02d1a40000fc0fc0fff])),(BitVec.ofNat 152 (word80 [0x28028008400040220a,0x20011201041041041041]))),((BitVec.ofNat 152 (word80 [0xfc003fffe0ffe02952,0xa662f48003f00003f000])),(BitVec.ofNat 152 (word80 [0x304b04500210822902,0xa462d40b2cb2cb2cb2cb]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffc00000ffffbd84,0x91d84280fc003f00003f])),(BitVec.ofNat 152 (word80 [0x400c01608405001884,0x81584086186186186186]))),((BitVec.ofNat 152 (word80 [0xffffffffff0000804d,0x6956a9bf00000003ffc0])),(BitVec.ofNat 152 (word80 [0x809009800026048044,0x9142994514514514514]))),((BitVec.ofNat 152 (word80 [0x9171,0x18b1dc4000003ffc0000])),(BitVec.ofNat 152 (word80 [0x2e02e0108b8088171,0x18a08c78e38e38e38e38]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x4e93,0x4f80057fffffc0000000])),(BitVec.ofNat 152 (word80 [0x300300210c0104411,0x42800060820820820820]))),(0x0,0x0)]
def g187C : List ColumnInfo := [(1,0,186,0,7),(2,0,185,0,7),(8,0,179,0,7),(16,0,171,0,7),(32,0,155,0,7),(128,0,59,0,7),(0,2,41,144,6),(0,32,146,9,6),(1,32,146,8,5),(8,32,146,1,5),(10,0,177,0,5),(16,2,41,128,5),(18,0,169,0,5),(33,0,154,0,5),(34,0,153,0,5),(128,2,41,16,5),(130,0,57,0,5),(9,0,146,0,4),(9,32,146,0,4),(17,0,170,0,4),(24,0,163,0,4),(41,0,146,0,4),(50,0,137,0,4),(136,0,51,0,4),(144,0,41,0,4),(144,2,41,0,4),(146,0,41,0,4)]
def g187A : List (List Nat) := [[],[112,81,67]]
def g187D5 := limbs80 #[#[0x4c950483d8dc95254110,0x482da6153254120f4953,0xe0d5254120e696354950,0x54130cb764dc553482da,0xb6785b30603d254932,0x10]]
def g187D6 := limbs80 #[#[0x3e899260887315454110,0xed2a4a8241dc5495044,0x43f8b9260884bd75d912,0x20fe6e4a8221fc5c9504,0x483f5b92a0907e932541,0x520df2c6a8241de54d50,0x24835fb22a2906bf644c,0xc920ddaca99241f354d3,0x52482f7baa64905ed754,0x54d20bdee6a9241bb58d,0x5634827ebb2a6905f771,0x359520ddee4b2a413fdd,0x49504c3ec992a0984ff7,0x7354130df6c4a8261de5,0xd95324c3e6a9264987db,0xd75d8930bbeea99261b7,0xf5cb654c2efb9aca984f,0xfd73d89509fcec992a13,0x5a0d0160027ebaec0994,0x23f0ee360ca2d08e1e0,0x8a5d1665613a4911e461,0xa811f67c1da7119e641,0x8a9d25e9624a8f226862,0x104c4864319120aa6a42,0x7c00b181448362670019,0x84816412084421918840,0x8000481420048114120,0x8001000449100c3c461,0x81c1810044c40401205,0x44810048100544820704,0x4c200641190464482000,0x18042060108007040864]]
def g187H6 := limbs80 #[#[0x1440000000000d400005,0xf5803d3a820700,0x3adc002080000000]]
def g187D7 := limbs80 #[#[0xd55110fc54110fc4c110,0xd9120ed95310ed95110e,0x4910fd4c910bfd8910af,0xb10fd4cb10fdd8910fd5,0x20fb4c920fe54120fd54,0xbf59520bf58d20fb549,0xbfd8930f74c930fe5413,0xfd8132bfd8950bfd9530,0x54d20ff54520ff4c520b,0x9530ff58930ff54930ff,0x950ff4c950ff54540ff5,0xff58132ffd8950ff58,0x1dc2f8470730be12c148,0x4700c496e2b45188b102,0xc984ae0560a01282203c,0x13c0c7b8ee9cc37d6c4c,0xc59041916464788bb10a,0x54c84649058b20832213,0x6cb8f0c20f0064b04a86,0x2482246420e1200b823c,0x8224682488a40b803c63,0x8d130a3243c64a483344,0x2812a4882f1929210a94,0x8b860604a9218a134618,0x2704592189c64c221a51,0xc9314a860a0491318a94,0x84860d14181242870808,0x100c1c4181832a182812,0x18c97244c48884c11122,0x3064d0990ca132221222,0x208ba424199245031a1c,0xa1322252201829]]
def g187H7 := limbs80 #[#[0xd5065c08323804402101,0x3c870f00000028d00002,0x50714001c9f4200000,0xd3f2e0000f000c0f4240,0xc914611d000a466fb,0x24918528685000000,0x6400000000839a400000,0xc6c15a45860e9000001a,0xd40b3c000a5416003,0x92dc0c00000b37f6400,0x6735080000527c0000,0x41b8205c0460000021a0]]
def g187D8 := limbs80 #[#[0xd30fe907f443ee21f510,0x83fd31fe90ff543fa81f,0xf05a210a82a007f4cbfa,0x89220191b558cb75121c,0x402cf1c892204068604,0xc02551849638521c8922,0x89563491130e58a19082,0x80b28f1a38a13e420500,0x893892c812280f584264,0x50396090984b0]]
def g187H8 := limbs80 #[#[0x56742544268040340202,0xe3781000798ac1e6,0xd0512000000000012540,0x7c0061a426d44004,0xa0000000052d93c00005,0x8386ec30011074968389,0x40921b1717f8ea4e1212,0x78e09400063f02000003,0xa02fb200000000000286,0x161f088000015546b50,0x92e4e7d8c11a3d690000,0x61129930c370093d]]
def g187D9 (j : Nat) := if j=0 then 0xa4188201bf else 0
def g187H9 := limbs80 #[#[0x6000001d304000000002,0x73c140000388000075,0x1030000000,0xa8000000000000000000,0x10004800000000000006,0x690000149f,0x1c6db800000000604000,0x6a0022,0x5e]]
def g187L : Nat → Packing
  | 5 => (7,4,5,0,0,6,0,g187D5)
  | 6 => (38,3,5,0,0,10,0,g187D6)
  | 7 => (34,2,5,0,0,11,0,g187D7)
  | 8 => (11,1,5,0,0,9,0,g187D8)
  | 9 => (1,0,5,0,0,0,0,g187D9)
  | _ => emptyPacking
def g187I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 2 29 3 8 3 1 g187H6
  | 7 => lookupWord 12 83 4 11 6 1 g187H7
  | 8 => lookupWord 13 79 6 11 6 1 g187H8
  | 9 => lookupWord 4 71 2 9 4 1 g187H9
  | _ => fun _ => none
def g187 : Forest := ⟨187,9,fun i => g187Y[i]?.getD (0,0),g187C,g187A,g187L,g187I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P5_0 : block g187 5 0 7=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g187B5 : block g187 5 0 7=true := g187P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P6_0 : block g187 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P6_1 : block g187 6 1 4=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P6_5 : block g187 6 5 33=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g187B6 : block g187 6 0 38=true := (@block_merge g187 6 0 1 37 g187P6_0 (@block_merge g187 6 1 4 33 g187P6_1 g187P6_5))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P7_0 : block g187 7 0 6=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P7_6 : block g187 7 6 17=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P7_23 : block g187 7 23 11=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g187B7 : block g187 7 0 34=true := (@block_merge g187 7 0 6 28 g187P7_0 (@block_merge g187 7 6 17 11 g187P7_6 g187P7_23))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P8_0 : block g187 8 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P8_2 : block g187 8 2 9=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g187B8 : block g187 8 0 11=true := (@block_merge g187 8 0 2 9 g187P8_0 g187P8_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P9_0 : block g187 9 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g187B9 : block g187 9 0 1=true := g187P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187T : checkedTables g187 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g187 0 0 0 = true)
  · exact (rfl : block g187 1 0 0 = true)
  · exact (rfl : block g187 2 0 0 = true)
  · exact (rfl : block g187 3 0 0 = true)
  · exact (rfl : block g187 4 0 0 = true)
  · exact g187B5
  · exact g187B6
  · exact g187B7
  · exact g187B8
  · exact g187B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187G : graphValid g187 (boundsBefore K183) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low187 : Lower true (varsX 187) (graphGoal 187) 10 := lower_forest (g:=g187) (i:=0) (hints:=67) (before_sound K183 V183) g187G g187T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K187 := extendKnown K183 10 [(187,[]),(246,[96,65,32,50]),(250,[96,65,32])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V187 : Known true K187 := extend_ok (m:=187) V183 low187 (by decide +kernel)
def g189Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffffffffffffffffff,0xe88328939da000f00fff])),(BitVec.ofNat 152 (word80 [0x50028008000080,0x28020090848111111111]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfff8003ffc03ffc0,0x194d3584ce100f00f000])),(BitVec.ofNat 152 (word80 [0x2a05606b0250682905,0x99413484cc1333333333]))),((BitVec.ofNat 152 (word80 [0xffffffc00003ffff,0xcd31ac6e2090f00f000f])),(BitVec.ofNat 152 (word80 [0x4c09804c0360b03209,0x101ac4e201222222222]))),((BitVec.ofNat 152 (word80 [0xfffffffffffc0000,0x2535a45ba5f000000f0])),(BitVec.ofNat 152 (word80 [0x702e01700b80c0bc0e,0x2511a453a1666666666]))),((BitVec.ofNat 152 (word80 [0xff0000000000000000,0x45c463c7720000fff00])),(BitVec.ofNat 152 (word80 [0xb005802c0102c010,0x41c4220132ccccccccc]))),(0x0,0x0),(0x33a4d3e0015ffff00000,(BitVec.ofNat 152 (word80 [0x80c006003002030020,0xa44120014888888888]))),(0x0,0x0)]
def g189C : List ColumnInfo := [(4,0,185,0,7)]
def g189A : List (List Nat) := [[]]
def g189D7 (j : Nat) := if j=0 then 0x7f else 0
def g189L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g189D7)
  | _ => emptyPacking
def g189I (_ _ : Nat) : Option (Nat × Nat) := none
def g189 : Forest := ⟨189,7,fun i => g189Y[i]?.getD (0,0),g189C,g189A,g189L,g189I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g189P7_0 : block g189 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g189B7 : block g189 7 0 1=true := g189P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g189T : checkedTables g189 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g189 0 0 0 = true)
  · exact (rfl : block g189 1 0 0 = true)
  · exact (rfl : block g189 2 0 0 = true)
  · exact (rfl : block g189 3 0 0 = true)
  · exact (rfl : block g189 4 0 0 = true)
  · exact (rfl : block g189 5 0 0 = true)
  · exact (rfl : block g189 6 0 0 = true)
  · exact g189B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g189G : graphValid g189 (boundsBefore K187) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low189 : Lower true (varsX 189) (graphGoal 189) 8 := lower_forest (g:=g189) (i:=0) (hints:=1283) (before_sound K187 V187) g189G g189T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K189 := extendKnown K187 8 [(189,[]),(231,[96,49,32,33,65])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V189 : Known true K189 := extend_ok (m:=189) V187 low189 (by decide +kernel)
def g190Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfc00fffffffffffffe,0xd62932b74a48000f801f])),(BitVec.ofNat 152 (word80 [0x481610542128429028,0x540832b642414a5294a5]))),((BitVec.ofNat 152 (word80 [0xfffffffe0003fff801,0x601555aee91001f003e0])),(BitVec.ofNat 152 (word80 [0x90a402980db01320cd,0x601550aa4910c6318c63]))),((BitVec.ofNat 152 (word80 [0xfffffffc000001,0x39c4d2534e803e007c00])),(BitVec.ofNat 152 (word80 [0xe13804e009c01bc171,0x3184d2034e00c6318c63]))),((BitVec.ofNat 152 (word80 [0xffffffffffffff,0x428bca0b99efc000001f])),(BitVec.ofNat 152 (word80 [0x1c027004e009c0181,0x281c00999aa94a5294a]))),((BitVec.ofNat 152 (word80 [0xffff00000000000001,0x22fa317cb68000007fe0])),(BitVec.ofNat 152 (word80 [0xb8017002e00200,0x26a2154b08739ce739c]))),(0x0,0x0),(0x9d26ecc07137ffff8000,(BitVec.ofNat 152 (word80 [0x200c0018003000400,0x88220c40200421084210]))),(0x0,0x0)]
def g190C : List ColumnInfo := [(4,0,186,0,7)]
def g190A : List (List Nat) := [[],[50],[65],[65,50]]
def g190D7 (j : Nat) := if j=0 then 0x7f else 0
def g190L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g190D7)
  | _ => emptyPacking
def g190I (_ _ : Nat) : Option (Nat × Nat) := none
def g190 : Forest := ⟨190,7,fun i => g190Y[i]?.getD (0,0),g190C,g190A,g190L,g190I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g190P7_0 : block g190 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g190B7 : block g190 7 0 1=true := g190P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g190T : checkedTables g190 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g190 0 0 0 = true)
  · exact (rfl : block g190 1 0 0 = true)
  · exact (rfl : block g190 2 0 0 = true)
  · exact (rfl : block g190 3 0 0 = true)
  · exact (rfl : block g190 4 0 0 = true)
  · exact (rfl : block g190 5 0 0 = true)
  · exact (rfl : block g190 6 0 0 = true)
  · exact g190B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g190G : graphValid g190 (boundsBefore K189) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low190 : Lower true (varsX 190) (graphGoal 190) 8 := lower_forest (g:=g190) (i:=0) (hints:=270619968) (before_sound K189 V189) g190G g190T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K190 := extendKnown K189 8 [(190,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V190 : Known true K190 := extend_ok (m:=190) V189 low190 (by decide +kernel)
def g207Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x7ffc01ffffffffff,0xffc035677a50000f000f])),(BitVec.ofNat 152 (word80 [0xd01482c82a4252148,0x29c035454a5555555555]))),((BitVec.ofNat 152 (word80 [0x7ffffffff0007ffc,0xf354385e8000f000f0])),(BitVec.ofNat 152 (word80 [0x5615914814c1b60990,0xccf304385e8333333333]))),((BitVec.ofNat 152 (word80 [0xff800001ffffff8000,0x26278cbf400f000f00])),(BitVec.ofNat 152 (word80 [0x9819e2702701380de1,0x7026078c3f4333333333]))),((BitVec.ofNat 152 (word80 [0x1ffffffffff,0xfe580f6a35b0f000f00f])),(BitVec.ofNat 152 (word80 [0xe01e03803801c00e01,0x80180a2a358222222222]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffe0000000000,0x24f859c3ef0000fff0])),(BitVec.ofNat 152 (word80 [0x200000c006003002,0xf041802444444444]))),(0x19b82850c0fffff0000,(BitVec.ofNat 152 (word80 [0x4000010008004000,0x888888888]))),(0x0,0x0)]
def g207C : List ColumnInfo := [(2,0,205,0,7)]
def g207A : List (List Nat) := [[],[33]]
def g207D7 (j : Nat) := if j=0 then 0x7f else 0
def g207L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g207D7)
  | _ => emptyPacking
def g207I (_ _ : Nat) : Option (Nat × Nat) := none
def g207 : Forest := ⟨207,7,fun i => g207Y[i]?.getD (0,0),g207C,g207A,g207L,g207I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g207P7_0 : block g207 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g207B7 : block g207 7 0 1=true := g207P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g207T : checkedTables g207 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g207 0 0 0 = true)
  · exact (rfl : block g207 1 0 0 = true)
  · exact (rfl : block g207 2 0 0 = true)
  · exact (rfl : block g207 3 0 0 = true)
  · exact (rfl : block g207 4 0 0 = true)
  · exact (rfl : block g207 5 0 0 = true)
  · exact (rfl : block g207 6 0 0 = true)
  · exact g207B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g207G : graphValid g207 (boundsBefore K190) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low207 : Lower true (varsX 207) (graphGoal 207) 8 := lower_forest (g:=g207) (i:=0) (hints:=16778851) (before_sound K190 V190) g207G g207T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K207 := extendKnown K190 8 [(207,[]),(222,[64,33,49])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V207 : Known true K207 := extend_ok (m:=207) V190 low207 (by decide +kernel)
def g215Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3ffe001ffffff01fc,0x5f8b8545600001f0001f])),(BitVec.ofNat 152 (word80 [0x588544d44944522c50,0x5f83814465294a5294a5]))),((BitVec.ofNat 152 (word80 [0xfffffffe001ffffe01,0x98b361b240003e007fe0])),(BitVec.ofNat 152 (word80 [0x900980980d80644899,0x989300b0410842108421]))),((BitVec.ofNat 152 (word80 [0x3ffffffffe0000002,0x54dc3874c007c00f8000])),(BitVec.ofNat 152 (word80 [0xe02e00e00e017870e0,0x549c3870c318c6318c63]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x3fffffffffffffffe,0xa08ef66320f8000003ff])),(BitVec.ofNat 152 (word80 [0x13009009009800002,0x200c76030a5294a5294a]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfc0000000000000002,0x4970938fdf00000ffc00])),(BitVec.ofNat 152 (word80 [0x1c00e00e00e008102,0x160830f0c6318c6318c]))),((BitVec.ofNat 152 (word80 [1,0x37050a181ffffff00000])),(BitVec.ofNat 152 (word80 [0x20010010010000000,0x108421084210]))),(0x0,0x0)]
def g215C : List ColumnInfo := [(2,0,213,0,8),(1,0,214,0,7),(4,0,211,0,7),(16,0,199,0,6),(64,0,151,0,6),(5,0,210,0,5),(17,0,198,0,5),(18,0,197,0,5),(20,0,195,0,5),(65,0,150,0,5),(68,0,147,0,5),(128,0,87,0,5),(19,0,196,0,4),(21,0,194,0,4),(69,0,146,0,4),(129,0,86,0,4),(132,0,83,0,4)]
def g215A : List (List Nat) := [[],[32,100]]
def g215D4 := limbs80 #[#[0x32a87993746047054d43,0x80dc56550f1c304c02e2,0x73c8b0db92a921e38e0b,0x2a74e39259171181538,0xf624c3021e730b22e23]]
def g215D5 := limbs80 #[#[0x5d9544c3965915354130,0x4c23de0576551308fb80,0xe0176d51308ef825d954,0x503308ef825d2654c23e,0x9eb825d350cc27660e75,0xdc154cc27660f7055330,0xcc23de057655330cb964,0xe0974997308ef825d954,0xd4d40f195350d505023b,0xa9f8654d43d023be0976,0xdc153d033658f7054f40,0xd03275d163d4f409b984,0xe095458f40a5f8558f53,0x58f40ad9801d563d03a3,0xacd821d563d02b560475,0x9d563d02b6e017558f40,0x5427ae0974d4150c5f75,0x54f7050f508ef825d363,0x50f50cd963dc143d4356,0x97985dc143d432e59370,0x5d943d423de057650f50,0x50f0fd977454d438ef82,0x6046554d43a798019553,0x54d438f7815d95350e9d,0xd9b741c15350ef460470,0x1955350f361db7054d43,0x50ed56046554d43b5980,0xe1d6519543c75655c465,0x59543cf1805c46550e1f,0xceb721c16550f3cdc470,0xdc16550f3cdc77059543,0x50f3c2037159543ceb72],#[0xdd37359543cf380dc565,0x58a43ecb8054d6290f27,0x8ed86dc95490eb360f54,0x5516014f36e1d5358053,0x14fb4e015358453aeb82,0xe015358853ae78255161,0x54c538ef875516214fb2,0xcdb76dc15314fa659370,0x5c46054f36e037654c53,0x54f3cd917118153cf164,0xe096418153af38159060,0xd81538fb875906054eba,0xaeb825936054ebce0564,0x5d36054e3de0574d8153,0x54ebae0954d81538ef82,0x60c74d8153e3b5495360,0xd8153cb9741d36054eb6,0xaeb825d36054ebce0574,0x5906454e73e0974d4d53,0x94e73e0974d4e538bf87,0xe0176d4e53b4f825d353,0x3c00ae5811c964d4f96,0xfc390cc2d09c2106c15,0x1e0721b06615c5112c45,0x2a0a2270962408a2107e,0x360d2330c6300ba2d0ae,0x4450b414f63c0ea390de,0x5053b4d52f4a52347517,0x5c56b5955f5655353547,0x6859b6558f625835f577,0x7b1e6781da751ce721b9,0x872168420a811fe7e1f2],#[0x2418d22e8a222,0x1020800000000000,0x0,0x90400000000000,0x0,0xe2300400000000000000,0x6182]]
def g215H5 := limbs80 #[#[0x15000000400034cb,0x2000000000000000320]]
set_option maxRecDepth 16000 in
def g215D6 := limbs80 #[#[0x27db82ca987595354130,0xbb2e7a8661d654f50cc,0x277b92caa067965d433,0x439dee4b26a1a755163d,0x50e7ab88caa1cf970195,0xa439eee2b2a873edc165,0x114f6ca9ac029ecd5358,0x4c53d9aa6b10a7b554d6,0x6054e6fbb2a629e9d645,0x59353cbaeda9ca77c5c4,0xd504c3f4a92a0904ef72,0x54d30df2c8a8261f654,0xc9544c36eb22a6987db7,0x7655130d7ac8aa2617bd,0x5c3544c27fbb2a8984fd,0xd76d5130bbae7aa2617e,0xfdd5644c37db82c8984f,0xff7459530df6e0b2a613,0xf654d40cc27eba4ca984,0x6f96550330f72a8a0661,0x1f654f50cc2fd3aa8198,0x85f974d4330fb2e7a866,0x61be5db50cc37cb2ea19,0x986dd6454f30fb6e0a9e,0x6617bdc954cc2fdb82a9,0x9984fd7655330d7ac8aa,0xa661775cf54cc27fbb2a,0xcb984ff75593309faeda,0x32e613fdd165cc37db82,0xaa0a07b943541409fae9,0x8a8281ded4d50503bca9,0x9a86a07bb7050d40f72a],#[0xeaa1a81af59543503cea,0xb82a6a05bf7550d40b7a,0x2e1a9a813fdd953502fd,0xebb6a6a05bd74d4d40bf,0x5ee4aa281eedc1545027,0x7db82caa05bf7355140f,0x9fee6b2a81bbdc965503,0x3cea9a87a04fd7399540,0xb7aeaa1e81af59543d0,0x2fdb82a7a05bf7550f4,0x409faeca9e81b758d53d,0xd036eb1ea7a04ff7654f,0xf409faeda9e816f5d353,0x3d027fbaac7a06bd5458,0x8f40dbaeab1e81b71d56,0x54d036fbaac7a06de755,0x59740b7ee6aa681ebdc9,0xf505427eb9ccba04ff73,0x4d4150bf2e7a82a1de54,0x8d43543aea9a86a85f97,0x7054d509feeca1aa1b7d,0x5d363543bdb82a6a85fb,0xf7255150bf6e0aa2a13f,0xf5cf64542f7b92c8a85e,0x5d5350f50bf6e0a1ea13,0xaf59143d436eb1a87a87,0x4ff7650f509faeca1ea1,0x1bedc163d43bdb82a7a8,0x85ef72553509fee8b1ea,0xa1bbdc964d42f7b92c9a,0xa1edd53d81439fee6b26,0xa873f5d76050f5eaa6c0],#[0x6a1dbf7454d43bf6e0a9,0x9a879fd955350f3e32aa,0xa6a1fd87054d439faeca,0xa9a8777dc95350fedb82,0x2a6a1f9e5454d43f3aa8,0xaa9a87e7dd15350fce3a,0xb2a6a1f5f6554d43eb8c,0xeb29a87e79525350f6e3,0xba6a6a1dde7694d43bba,0x2e032a879fd975350ede,0xeb28caa1df57119543bf,0xf6e0b2a873f9d86550f3,0x3fb2acaa1df77159543b,0xdf6e0b2a87be1c16550f,0xf7bb8acaa1cff7059543,0x39fee6b2a87b7dcd6550,0xe7eb9ccaa1e7f659954,0x43ddaa8b14873f5c3655,0x90fedb82a721eef5458a,0x243bdee4aa487b7dd953,0x490f3eb2aa921ddf7355,0x5243bbae7aa4879f9955,0x6014f7caa2c029e7d65d,0x58453deaa8b08a7be951,0x16214f76aa2c429ef654,0x454c53fb6e0a98a7bb95,0xc95414f6fbb2a629edd6,0x64950539feecaa0a77bd,0x5906054e7ebb4a829ebd,0xa7618153df6c8302a7be,0xed8b6054f7cb16c0a9df,0xfb63d8153fb6a7b02a7b],#[0xbe1936054fedb9ec0a9e,0xefa64d8153df2c9b02a7,0x73f5d36054f7db26c0a9,0x9efb72d8153df2e5b02a,0xa7be5536054f7db9ec0a,0xa9efb54d8153df4a9b02,0x2a7be5d36054f7c3a6c0,0x4a9efb74d8153df4e9b0,0x9aa73f5d36254efdb82c,0xa8a9ddf7355153bbae9a,0x2a2a7cfd525454eeeb9c,0x2c8a9ebd6419153d7ec9,0x4b22a77ddc56454efdb8,0x24c8a9df97099153bdee,0xe5b22a73f5c36454f5fb,0xba6a729f5e54d4e539fa,0xce9a9ca7d75d35394eee,0x7b92c9a9ddd7395253eb,0xd8e4b26a73fdc164d4ef,0x7fb92c9a9eef7259353d,0x101d81801280b0078002,0x83c03a83703182c02682,0x6685d05785204c847041,0x508187c07887506f86c0,0x89809489108f88a08688,0xaa8a70a38a209e89d099,0xf0bb8ba0b68b30b18b00,0x8d40ce8cd0cb8c80c28b,0xe68e50e18e00de8db0d9,0xf0fb8f80f48f10ed8ea0,0x91210e90d1099081048f,0x2a92712191e11a919115],#[0xd13993813493112d92c1,0x95415094f14b94614293,0x6c96b169966162959155,0x317f97e17897316f96e1,0x99a19699318d98a18698,0xb09a91a59a21a099d19b,0x71c39c01be9bb1b79b61,0x9d81d69d51d19ce1ca9c,0xf29ef1eb9e81e09dd1db,0x9205a04202a011ff9fa1,0xa2021ea1b217a1220ca0,0x32a2d229a28226a25223,0x7243a42240a3d239a382,0xa5c258a55251a4c248a4,0x74a7126da6a264a6325f,0x9285a84282a7f27ba782,0xaa62a2a9d299a98292a8,0xbcabb2b5ab22aeaad2a9,0x32cface2ccac72c5ac42,0xae42e2add2d9ad82d6ad,0xf6af32efaec2eaae92e5,0x7305b02300aff2fbafa2,0xb1a316b1330fb0c30ab0,0xe00d0f27b24322b1f31d,0x83f8020f06e00f8010b,0xb078020ae00b80106e0,0x6e0080e004403c2e00b,0xe0081b8020607081b802,0x8020f090d0c101b80206,0x82c10b0408042e0041b,0x400200082c1002410341,0x81001810018100041030],#[0x4106040001004209040,0x81043d042810418102,0x10400200080e8820,0x10904241230408101041,0x41034209041410424,0x4100081010410100101,0x504100002043c2420107,0x4104810a0c100041030,0x101000c100101030108,0x4105041046260061,0x41002d0c20b430804100,0x2042d042830410104050,0xc1014104001040003c10,0x10418100080020342c10,0x21040410207041c10404,0x4003000400004002841,0x8a842c30404841090408,0x20b0424100000004a109,0x4003048810321081084,0x80205e0080010000000b,0x10004100000040010007,0x6101030484144030820,0x588104040c8420000103,0xb048810b058810b0,0xc0828442c1c010181,0x14160050c16260080c1,0x89803010c84243050c10,0x20418100002000800025,0x8410006260090c10006,0x4100101c107041000400,0xc10b0400304021040008,0x400304003042c162040],#[0x2]]
def g215H6 := limbs80 #[#[0x355bb0c0109400b1463,0x5644000000f8013c1822,0x83b32fc30f4800003301,0x45c3ab40d3ff4731072d,0x21d000e251a46013a8d,0xc1220932345200000000,0xc32d4b000b00503000,0x417000a54e4e00073e0,0x12e00000025300,0x74243d000a4c439,0x3735d1a1ad000e0e0000,0xf38f3440fea203654,0x1331823cd4620a000000,0xde31927921d28207cb31,0xf0b250000000f196b054,0x8800000031f551000884,0xe40461181ba2000021cd,0xb4a82a5556490000002a,0x81105c22aaaaaf20dc0c,0xe000f262166b2c2b229f,0x53734130852c506000c1,0x54f000514c02000824]]
set_option maxRecDepth 16000 in
def g215D7 := limbs80 #[#[0xb58a43b798f40b758f40,0x58453be58053e7d0e43b,0x9053af59053bb58853bd,0x120d7d4e53bed8153af9,0x30bf99520bf59520fe54,0xbf59130f754d30fe541,0xfe50330bf99530bf5953,0xf59330f754f30fed4330,0x54140bf99730bf59730b,0x9540ef55140ef50d40fe,0xf40ef50f40bf99540bf5,0x40bf59740ef55340bf58,0xbfd8950fed4150bf997,0xbfd8d50dfd4d50df54d5,0xf54f50bf58b50bfd9150,0x59350bf58f50dfd4f50d,0x8143bf99443bf59443bf,0x543f794d43f754d43bfd,0x43bf99543bf59543bf19,0x3bf59243f754e43bfd95,0xf754c53bf99643bf5964,0xe18153bf99453bf59053,0xd8953bfd8153fed8153f,0x4e53bfd9153f7d4d53bf,0x353bf59653bf59253f7d,0x30bf59353bf58b53bf58,0xff55330ffd5130ff551,0xffd4d40ff54d40ffd533,0xf54950ffd4f40ff54f40,0x54d50ff50d50ff58950f,0x9150ff55150ff58d50ff,0xf50ff54f50ff50f50ff5],#[0x43ff59350ff55350ff58,0x3ff54d43ffd8143ff581,0xff59543ff19543ffd4d4,0xf55243ffd9543ff99543,0x95053ff55053ffd5243f,0x8953ffd8153ff58153ff,0x153ffd4d53ffd8953ff5,0x53ffd5153ff95153ff55,0x3ff99153ff59153ff191,0xffd5253ff95253ffd915,0x1b000ff99353ff59353,0x90e70c50a308105f03d,0x1d51b318a16814612b1,0x2a728c27124f22d20b1f,0x8e37335833630d2eb2c9,0xc45343140f3ed3d23b03,0x53a5184f64db4c049e47,0x1a5f85d65b459257755c,0xb7026e76cc69566c63c6,0x8137ea7c879f77d75472,0x18d88b689b88085e83c,0x69db9b299096e9459239,0xa98a7da62a4ea33a119f,0x55b33b1fb0bae9aceab3,0x4bf0bd5bbaba6b92b70b,0xcb4ca7c85c55c3ac18c0,0x94d79d65d3cd13cf1ccf,0x5e21e0ddf2dd0dbcda8d,0xec2ea7e9ae86e6be57e3,0x803090426010241c0283,0xb1180308202600c24411,0xc20b11803082c4060e20],#[0xc8c018809803082c4600,0x1478ec03441623006110,0x6863b00b1a2101e3b00d,0x82c4e01a20bc03431f80,0x64061300d1620f098068,0x83f04110201c1203c02,0x2058a130411020bc0244,0x12343463f00e10241c0,0xc2c41e0f00e105e01c1e,0xbc028309805060c1e01,0x162838380509047e0142,0xe12181c0404070700a,0xd107e01a18fc03431e37,0x80d1018ec03c4083f00,0xd105e00c18bc03431d8,0x1300610583c038416130,0x6162700d10404c018410,0x588c0185c42d0830980,0x38032004104078078e1,0x28202101e0148601e182,0x82c208c018516104600c,0x84082300616284118030,0x16284162300614588c01,0x1e010789c03440820360,0xf102601a184c0343c486,0x5880808b07805200f00,0x118030a10360102080d8,0x26020344098078d10584,0x60c2220c18104105e014,0x85890618444041882c48,0x307042062c3090c1890,0x88407850e0901e18b0c1],#[0x1e20f0c10f0c10407047,0x203170441e8848611141,0x4862d1090c5860858608,0x1080c4068420c2421688,0xd121401018c0c5840c5a,0xb080c31608b44850082,0x802c2161018812122062,0x3042c242830050909141,0x21634220342160d0863c,0x5042030d141080c4820c,0x210444850080c4850458,0x618b0420308584061a11,0xb042221]]
def g215H7 := limbs80 #[#[0x8008204140030200401,0x1020022000000e105000,0x4881224380065058a18,0x91844218040008a000,0x80022c28004041803e28,0x262a8c01005cd0e02a2c,0x40002124a68386200110,0x719881b86de3ca50f07,0x181c240002d0a00000,0xd6b21cd900000006d500,0x8f74a50004942442000c,0xad00040d99dacf445363,0xfb0cae6c0b6066597e8e,0x60000000000258960c9f,0x4eaa6000312e1bccbbeb,0xbb00018b01d00000d2b3,0xa34a958ca70648a4000a,0x2e2c0c0ae2ee0193e0ea,0x90001c2674b24fa7408e,0xd8ce0007b444d2662e00,0xe000000121122d800112,0x4c0000006114001d42c8,0xf42aa8001c9e762bb5a4,0x8b80000583e5c0016954,0x36de150cbf37cd638001,0x39cea97829b9c6720670,0x875116817964df5d29f,0xc841360ea0a000172c00,0x6033e56b9d23f54a1a,0xbb0da40009ec00000000,0x98f000098908f06d1,0x4868001446a5f0000000],#[0x950a00073a6b44000146,0x283705020330000001c7,0x4071a62e28a3,0x5800000154c00000000,0x145255a800000000a1,0x300cc2621f7433138,0xc000000000000273fc07,0x310ddbac000a6b0b1d8e,0xbf8d86d00007a7d87d9a,0x520c001a2a01758,0xeec0000a113b1d2ddae0,0x13600061cabb2000f267,0x4ac6d68000d4c0954001,0x40009500b53d52ac0000,0x8c17894726e811e0d26c,0x16585c8f80000007e46c,0x2069a1f4c0b9e5e8001d,0x1240007279c74000a614,0xd2c9a6658c000e13ba11,0xcd84000c56180a870f4d,0x1211b240eec4a0000eb,0xf40000000003dac46200,0xb16c8f5b36e4191c81,0x180000000d538a88dc80,0x31038571360006356,0xc87b4fda73961800333c,0xf02bf668b7c000000f48,0x15c5aa0bf0004dbf71,0x658d9102000000149300,0x7f46e1bc07a8193ee9e,0xcf0863a72999246a067e,0x1a400ad617b703b77],#[0x9889222e09720b496000,0xede829214d08a0005c6,0x3570acf15600,0x370000001e40acf00000,0xa2515158ca7180000012,0xda5da0007a20,0x7610357a9ca8430170a2,0x2b70005a02860443000,0x27b4a75856a2be01]]
def g215D8 := limbs80 #[#[0xf40fea07fcc3fa61fd20,0x87fd43fe21ffd43faa1f,0x3fea7fe53fea9ff14ffc,0x3a998a8421989c300c00,0x3433a0343cc5eab92c84,0xa10680e0c9060204260,0x3a034504f3a03451818,0x18528980d10812018405,0x4410204b220187084220,0x43e03451088061011203,0x40]]
def g215H8 := limbs80 #[#[0x60400018440040082000,0x210480010,0x28db68200c000,0xc0004cc00000000254c0,0x7280013a5f9c0039168a,0x0,0x64003c200000000000,0x0,0xd3eb64000000,0x14386680000000,0x358c00000000,0x206c000000,0x3d6c371b87c4f6430f00,0x998935e6ecb000233400,0xdcc000000000003,0xdd80000000024040000,0x3cab1c687c00000000,0x341b398000,0x25700010280,0x47800000000000000000,0x38000000000000000000,0x21,0x4b800000000000000000,0xc0000000000000000001,0x2ec800040249c0000033,0x45800000000373000000,0x2,0x422c30a000062c0000,0x11d40024d400,0x0,0x3d868150bc0,0x6000103fcec00000000],#[0x3c12ce7,0x39592c40,0x15b8d75d60002d5,0xa619c003cb7920000000,0x14300000038,0x55400000000000000000,0x0,0x18d00,0x0,0x7c000000000000000000,0x9180000000000001da91,0x25e310,0x20f8000,0x16745d00,0x19dc00,0x35b19a4000000,0x0,0x0,0x2cc4000000000000000,0x40000015b40000000000,0x24fdc5,0x2544000000001d0c,0x101c0000000000000,0x12800000000000000000,0x249b883da248d,0x21ac0000000000000000,0xfdc00000000019400,0x27a1d8800286a0f4,0x0,0x0,0x2dc8002050,0x0],#[0x0,0x67940003d48000000000,0x7de4002844000000002d,0x490001ce0000000c733c,0x94000000000000000f79,0x38,0x8374c000215cb5056800,0x1000000351800204a1c3,0x2700019,0x35c00000200800000000,0x34774de,0x142c000000000002f800,0x3024000000002105d3,0x392c002888002f2c000,0x0,0x5240005bc00,0x30840014cbce8000000,0x251c0,0x1a78000000002d0,0x197bb7c000000000,0x3d900,0x345c00000]]
def g215D9 (j : Nat) := if j=0 then 0x8200ff else 0
def g215H9 := limbs80 #[#[0x15600,0xac0d6a3310,0x1c82b0020800005ed48,0xa00000bbad6e70e00000,0x1a800000000000002,0x1ab69d9f8c000,0xbb0000000000000,0x41005c400a6ce00]]
def g215L : Nat → Packing
  | 4 => (6,5,5,0,0,5,0,g215D4)
  | 5 => (86,4,5,0,0,10,0,g215D5)
  | 6 => (238,3,5,0,0,12,0,g215D6)
  | 7 => (122,2,5,0,0,12,0,g215D7)
  | 8 => (14,1,5,0,0,9,0,g215D8)
  | 9 => (1,0,5,0,0,0,0,g215D9)
  | _ => emptyPacking
def g215I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 23 0 7 3 0 g215H5
  | 6 => lookupWord 24 137 5 12 7 1 g215H6
  | 7 => lookupWord 74 409 7 13 8 1 g215H7
  | 8 => lookupWord 38 563 3 12 7 1 g215H8
  | 9 => lookupWord 6 67 3 9 4 1 g215H9
  | _ => fun _ => none
def g215 : Forest := ⟨215,9,fun i => g215Y[i]?.getD (0,0),g215C,g215A,g215L,g215I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215P4_0 : block g215 4 0 6=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g215B4 : block g215 4 0 6=true := g215P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215P5_0 : block g215 5 0 86=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g215B5 : block g215 5 0 86=true := g215P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215P6_0 : block g215 6 0 21=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215P6_21 : block g215 6 21 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215P6_117 : block g215 6 117 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215P6_213 : block g215 6 213 25=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g215B6 : block g215 6 0 238=true := (@block_merge g215 6 0 117 121 (@block_merge g215 6 0 21 96 g215P6_0 g215P6_21) (@block_merge g215 6 117 96 25 g215P6_117 g215P6_213))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215P7_0 : block g215 7 0 11=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215P7_11 : block g215 7 11 63=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215P7_74 : block g215 7 74 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g215B7 : block g215 7 0 122=true := (@block_merge g215 7 0 11 111 g215P7_0 (@block_merge g215 7 11 63 48 g215P7_11 g215P7_74))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215P8_0 : block g215 8 0 14=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g215B8 : block g215 8 0 14=true := g215P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215P9_0 : block g215 9 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g215B9 : block g215 9 0 1=true := g215P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215T : checkedTables g215 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g215 0 0 0 = true)
  · exact (rfl : block g215 1 0 0 = true)
  · exact (rfl : block g215 2 0 0 = true)
  · exact (rfl : block g215 3 0 0 = true)
  · exact g215B4
  · exact g215B5
  · exact g215B6
  · exact g215B7
  · exact g215B8
  · exact g215B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215G : graphValid g215 (boundsBefore K207) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low215 : Lower true (varsX 215) (graphGoal 215) 10 := lower_forest (g:=g215) (i:=0) (hints:=16778820) (before_sound K207 V207) g215G g215T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K215 := extendKnown K207 10 [(215,[]),(221,[32,49,64,96])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V215 : Known true K215 := extend_ok (m:=215) V207 low215 (by decide +kernel)
def g219Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xe007ffffe1ffff9164,0xdc16e000000fc0000fff])),(BitVec.ofNat 152 (word80 [0x44510a204404101144,0xcc00e249249249249249]))),((BitVec.ofNat 152 (word80 [0xfff800fffe1ff8318b,0x3c89500003f000fff000])),(BitVec.ofNat 152 (word80 [0x80602c028040213083,0x3c0140c30c30c30c30c3]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffff00001fffda3d,0x31312000fc003f00003f])),(BitVec.ofNat 152 (word80 [0x80300b0881400a39,0x31110186186186186186]))),((BitVec.ofNat 152 (word80 [0xffffffffffe000462a,0x8b87903f00000003ffc0])),(BitVec.ofNat 152 (word80 [0x902404c0009824628,0x3861514514514514514]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x4984,0x67ec8fc000003ffc0000])),(BitVec.ofNat 152 (word80 [0xe038070110e044104,0x42ec8618618618618618]))),((BitVec.ofNat 152 (word80 [0x2651,0x42404fffffffc0000000])),(BitVec.ofNat 152 (word80 [0x100400800010000000,0x820820820820820]))),(0x0,0x0)]
def g219C : List ColumnInfo := [(1,0,218,0,7),(2,0,217,0,7),(8,0,211,0,7),(16,0,203,0,7),(64,0,155,0,7),(128,0,91,0,7),(3,0,216,0,5),(9,0,210,0,5),(10,0,209,0,5),(19,0,200,0,4),(25,0,194,0,4),(73,0,146,0,4),(129,0,90,0,4),(130,0,89,0,4),(136,0,83,0,4)]
def g219A : List (List Nat) := [[],[97,67],[16,99],[16,48,64,96],[48,100],[48,65,96,16],[64,49],[64,97,48,49],[96,16,49,67],[96,65]]
def g219D5 := limbs80 #[#[0x54950443cc5515150110,0x54237e0d7654910e6962,0x841d51c08df835c762]]
def g219D6 := limbs80 #[#[0x3b4a92a0904df7359510,0xdf2caa0221fc5454044,0x437cb12a088779525411,0x10bf6e8a8221be591504,0x4427ebb2a4885fb70549,0x5109fee4b2a213fdd562,0x15427fb8aca906df7359,0x85509fae5b0aa177dcd6,0x418027eb8ec4a84fd74d,0xe765e0dd9a5713d08b88,0x8516283033f26f2dac28,0x208504282001088c2280,0x4000182000101840410,0x182000]]
def g219H6 := limbs80 #[#[0x34400108000000,0x0,0x318000000a9000,0xb40]]
def g219D7 := limbs80 #[#[0xf58910fe54110fe50110,0x59520fe54120bf59510b,0x8950df54950bfd8550bf,0x550ff54520ff54910bfd,0x2a0d82400ff58950ff58,0x62a24ca34fc6c2e92c78,0xa496219a24a92296485,0x42985aa50869820448a4,0x29650a20449821c60259,0x9a11c90c182518588718,0x1c60e19a6263083]]
def g219H7 := limbs80 #[#[0x2000000000d234829410,0x74300050870ab0000000,0x670fa01110427107000,0xce62242000c1178570d4,0xc0ee4b000b0500068820,0x3104846e09000984363,0x60b000000000222d497]]
def g219D8 := limbs80 #[#[0x489a3407f543fa41fd10,0xa600ab48d58ad424aab]]
def g219H8 := limbs80 #[#[0x489c36613c509611a410,0x1c544738880000172400,0xf362c001936048200348,0x394800d28002d098c8,0xba2596206e0210515a30,0x3d9700000000000a0b28,0x2c]]
def g219D9 (j : Nat) := if j=0 then 0x5432101bf else 0
def g219H9 := limbs80 #[#[0x20030a00000b04000012,0xf73d2030004518,0x50000000000000000000,0x424000011a00044000c,0x55000000000d0000,0x48b8]]
def g219L : Nat → Packing
  | 5 => (4,4,4,0,0,5,0,g219D5)
  | 6 => (18,3,4,0,0,8,0,g219D6)
  | 7 => (13,2,4,0,0,9,0,g219D7)
  | 8 => (3,1,4,0,0,6,0,g219D8)
  | 9 => (1,0,4,0,0,0,0,g219D9)
  | _ => emptyPacking
def g219I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 31 0 9 2 3 g219H6
  | 7 => lookupWord 7 47 4 12 5 3 g219H7
  | 8 => lookupWord 7 41 5 11 4 3 g219H8
  | 9 => lookupWord 3 41 2 10 2 4 g219H9
  | _ => fun _ => none
def g219 : Forest := ⟨219,9,fun i => g219Y[i]?.getD (0,0),g219C,g219A,g219L,g219I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P5_0 : block g219 5 0 4=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g219B5 : block g219 5 0 4=true := g219P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P6_0 : block g219 6 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P6_2 : block g219 6 2 16=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g219B6 : block g219 6 0 18=true := (@block_merge g219 6 0 2 16 g219P6_0 g219P6_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P7_0 : block g219 7 0 9=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P7_9 : block g219 7 9 4=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g219B7 : block g219 7 0 13=true := (@block_merge g219 7 0 9 4 g219P7_0 g219P7_9)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P8_0 : block g219 8 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g219B8 : block g219 8 0 3=true := g219P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P9_0 : block g219 9 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g219B9 : block g219 9 0 1=true := g219P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219T : checkedTables g219 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g219 0 0 0 = true)
  · exact (rfl : block g219 1 0 0 = true)
  · exact (rfl : block g219 2 0 0 = true)
  · exact (rfl : block g219 3 0 0 = true)
  · exact (rfl : block g219 4 0 0 = true)
  · exact g219B5
  · exact g219B6
  · exact g219B7
  · exact g219B8
  · exact g219B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219G : graphValid g219 (boundsBefore K215) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low219 : Lower true (varsX 219) (graphGoal 219) 10 := lower_forest (g:=g219) (i:=0) (hints:=16777283) (before_sound K215 V215) g219G g219T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K219 := extendKnown K215 10 [(219,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V219 : Known true K219 := extend_ok (m:=219) V215 low219 (by decide +kernel)
def g235Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xf801ffe0fffffffea8,0xe90535840007c00003ff])),(BitVec.ofNat 152 (word80 [0x511441422080410280,0xe8050185294a5294a529]))),((BitVec.ofNat 152 (word80 [0xfffe0000ffc1ff8195,0x6311d29800f8000f8000])),(BitVec.ofNat 152 (word80 [0x601815840504120995,0x63115010e739ce739ce7]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffff0001fffcd7,0x85e044441f0001f07c1f])),(BitVec.ofNat 152 (word80 [0x802006000608040054,0x1404440421084210842]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffffffe000021,0x2edc7a2000003e007fe0])),(BitVec.ofNat 152 (word80 [0x44118008801181021,0x6983a0294a5294a5294]))),((BitVec.ofNat 152 (word80 [0x44,0x903f89b3e0003fff8000])),(BitVec.ofNat 152 (word80 [0x18060083010602000,0x902481a1084210842108]))),((BitVec.ofNat 152 (word80 [0x33a,0x528a034bffffc0000000])),(BitVec.ofNat 152 (word80 [0x6018010c02180402a,0x8a020a108421084210]))),(0x0,0x0)]
def g235C : List ColumnInfo := [(1,0,234,0,7),(32,0,203,0,7),(64,0,171,0,7),(128,0,107,0,7),(0,2,41,192,6),(2,0,233,0,6)]
def g235A : List (List Nat) := [[],[80,118]]
def g235D7 := limbs80 #[#[0xa15662e85d03ec43f521,0x498b]]
def g235D8 (j : Nat) := if j=0 then 0x2c21a1bf else 0
def g235H8 (j : Nat) := if j=0 then 0x1b2 else 0
def g235L : Nat → Packing
  | 7 => (2,1,3,0,0,5,0,g235D7)
  | 8 => (1,0,3,0,0,0,0,g235D8)
  | _ => emptyPacking
def g235I : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 1 2 0 5 1 0 g235H8
  | _ => fun _ => none
def g235 : Forest := ⟨235,8,fun i => g235Y[i]?.getD (0,0),g235C,g235A,g235L,g235I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P7_0 : block g235 7 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g235B7 : block g235 7 0 2=true := g235P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P8_0 : block g235 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g235B8 : block g235 8 0 1=true := g235P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235T : checkedTables g235 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g235 0 0 0 = true)
  · exact (rfl : block g235 1 0 0 = true)
  · exact (rfl : block g235 2 0 0 = true)
  · exact (rfl : block g235 3 0 0 = true)
  · exact (rfl : block g235 4 0 0 = true)
  · exact (rfl : block g235 5 0 0 = true)
  · exact (rfl : block g235 6 0 0 = true)
  · exact g235B7
  · exact g235B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235G : graphValid g235 (boundsBefore K219) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low235 : Lower true (varsX 235) (graphGoal 235) 9 := lower_forest (g:=g235) (i:=0) (hints:=16777315) (before_sound K219 V219) g235G g235T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K235 := extendKnown K219 9 [(235,[]),(249,[80,65,33,96,112])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V235 : Known true K235 := extend_ok (m:=235) V219 low235 (by decide +kernel)
def g237Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffc00ffe0ffc1ffffe,0x915365415000f00000ff])),(BitVec.ofNat 152 (word80 [0x4288a2142208402100,0x81532101555555555555]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffff0000fffe0ff81,0xa8697328200f000f0f00])),(BitVec.ofNat 152 (word80 [0xb00c0584050020208,0x88297308033333333333]))),((BitVec.ofNat 152 (word80 [0xfffffffff00000fffc,0xc6b0569090f000f0f00f])),(BitVec.ofNat 152 (word80 [0xc0100600060840400,0x40a05600822222222222]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffff0000,0x32aaa8e240000f00fff0])),(BitVec.ofNat 152 (word80 [0x102208800880008810,0x320008e2088888888888]))),(0x4154991e6f000fff0000,(BitVec.ofNat 152 (word80 [0x600c03008301083020,0x1548010644444444444]))),((BitVec.ofNat 152 (word80 [3,0x3f0502078ffff0000000])),(BitVec.ofNat 152 (word80 [0x80300c010c0210c043,0x36000006088888888888]))),(0x0,0x0)]
def g237C : List ColumnInfo := [(32,0,205,0,7)]
def g237A : List (List Nat) := [[],[117],[32,99],[32,99,117]]
def g237D7 (j : Nat) := if j=0 then 0x7f else 0
def g237L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g237D7)
  | _ => emptyPacking
def g237I (_ _ : Nat) : Option (Nat × Nat) := none
def g237 : Forest := ⟨237,7,fun i => g237Y[i]?.getD (0,0),g237C,g237A,g237L,g237I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P7_0 : block g237 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g237B7 : block g237 7 0 1=true := g237P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237T : checkedTables g237 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g237 0 0 0 = true)
  · exact (rfl : block g237 1 0 0 = true)
  · exact (rfl : block g237 2 0 0 = true)
  · exact (rfl : block g237 3 0 0 = true)
  · exact (rfl : block g237 4 0 0 = true)
  · exact (rfl : block g237 5 0 0 = true)
  · exact (rfl : block g237 6 0 0 = true)
  · exact g237B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237G : graphValid g237 (boundsBefore K235) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low237 : Lower true (varsX 237) (graphGoal 237) 8 := lower_forest (g:=g237) (i:=0) (hints:=33555715) (before_sound K235 V235) g237G g237T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K237 := extendKnown K235 8 [(237,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V237 : Known true K237 := extend_ok (m:=237) V235 low237 (by decide +kernel)
def g238Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0x807ffff8007ff01ffc,0x3cb735019000f000f00])),(BitVec.ofNat 152 (word80 [0xb0a0950b504a34148,0xb38b7350113333333333]))),((BitVec.ofNat 152 (word80 [0xff807fffff80001fff,0xf9bb81994600f000f00f])),(BitVec.ofNat 152 (word80 [0x121302602606c58191,0x219b8090461111111111]))),((BitVec.ofNat 152 (word80 [0x7fffffffffe000,0x69728c4a50f000f00f0])),(BitVec.ofNat 152 (word80 [0x1c1c038038070601e1,0xc69328c0841111111111]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x7fffffffffffff,0xf96279a7230000f000ff])),(BitVec.ofNat 152 (word80 [0x20204c04c048001200,0x60512721aaaaaaaaaa]))),((BitVec.ofNat 152 (word80 [0xffff80000000000000,0x98c46290f000ffff00])),(BitVec.ofNat 152 (word80 [0x10010010000400,0x4444444444]))),(0x665163c4cffff000000,(BitVec.ofNat 152 (word80 [0x404060060060081802,0x64042c088888888888]))),(0x0,0x0)]
def g238C : List ColumnInfo := [(4,0,234,0,7)]
def g238A : List (List Nat) := [[],[50]]
def g238D7 (j : Nat) := if j=0 then 0x7f else 0
def g238L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g238D7)
  | _ => emptyPacking
def g238I (_ _ : Nat) : Option (Nat × Nat) := none
def g238 : Forest := ⟨238,7,fun i => g238Y[i]?.getD (0,0),g238C,g238A,g238L,g238I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g238P7_0 : block g238 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g238B7 : block g238 7 0 1=true := g238P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g238T : checkedTables g238 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g238 0 0 0 = true)
  · exact (rfl : block g238 1 0 0 = true)
  · exact (rfl : block g238 2 0 0 = true)
  · exact (rfl : block g238 3 0 0 = true)
  · exact (rfl : block g238 4 0 0 = true)
  · exact (rfl : block g238 5 0 0 = true)
  · exact (rfl : block g238 6 0 0 = true)
  · exact g238B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g238G : graphValid g238 (boundsBefore K237) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low238 : Lower true (varsX 238) (graphGoal 238) 8 := lower_forest (g:=g238) (i:=0) (hints:=287331680) (before_sound K237 V237) g238G g238T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K238 := extendKnown K237 8 [(238,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V238 : Known true K238 := extend_ok (m:=238) V237 low238 (by decide +kernel)
def g243Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3fffffffffc1f5a0e,0x30aeb200000fc003f03f])),(BitVec.ofNat 152 (word80 [0x28428410040840120a,0xa4b209249249249249]))),((BitVec.ofNat 152 (word80 [0xfc003ff83fffe0206a,0xe661718003f000fc0fc0])),(BitVec.ofNat 152 (word80 [0x30130020809002204a,0x244131030c30c30c30c3]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffc0003fffffb48c,0x995842c0fc0000000fff])),(BitVec.ofNat 152 (word80 [0x408409410920008084,0x99184094514514514514]))),((BitVec.ofNat 152 (word80 [0xffffffffc000008945,0x6156a9c000003f03f000])),(BitVec.ofNat 152 (word80 [0x8218218021c0840945,0x615201e69a69a69a69a6]))),((BitVec.ofNat 152 (word80 [0x9171,0x18b1dc3f00003ffc0000])),(BitVec.ofNat 152 (word80 [0xe00e020e01089020,0x18a0cc18618618618618]))),((BitVec.ofNat 152 (word80 [0x4e93,0x4f80057fffffc0000000])),(BitVec.ofNat 152 (word80 [0x30030043002104c11,0x42000060820820820820]))),(0x0,0x0)]
def g243C : List ColumnInfo := [(1,0,242,0,7),(32,0,211,0,7),(64,0,179,0,7),(128,0,115,0,7),(0,32,146,65,6),(2,0,241,0,6),(16,0,227,0,6),(1,32,146,64,5),(17,0,226,0,5),(33,0,210,0,5),(34,0,209,0,5),(48,0,195,0,5),(64,32,146,1,5),(66,0,177,0,5),(3,0,240,0,4),(49,0,194,0,4),(65,0,146,0,4),(65,32,146,0,4),(80,0,163,0,4),(97,0,146,0,4),(98,0,145,0,4),(129,0,114,0,4),(130,0,113,0,4),(144,0,99,0,4),(160,0,83,0,4),(192,0,51,0,4)]
def g243A : List (List Nat) := [[],[96,65]]
def g243D5 := limbs80 #[#[0x54920443d85495148110,0x443e85092150110e6965,0x5492154110f315454540,0x54110f515348550443d8,0xf51538855044378dca21,0x589504439a5895254110,0x4439654f6254110e5953,0xdd55348510e656554921,0x54510e65625495144355,0x87f855d9424438d59154,0x54d624423be097654910,0xc423be097655110c5f75,0xdd55348710e656554921,0x58b10e656254951c4355,0xd6952dc55048317dd553,0x58551c82ae61a4150320,0xc8317dd55358720e6552,0xdd953485508f7815d954,0x58550d59535c22154317,0xd59535c2615435354f72,0xdc1514879954951d8121,0x886976036554d21d6552,0xdd55358a21e656254951,0xc008ef825c36454717,0x9a4b45427120843c1683,0x58aad4a9f4ca28f67537,0xe770b6daacf64b0d7ab7,0x3b1788c2e0aff7cbcdda,0x440e86000e0c002,0xc10182000000c1000]]
set_option maxRecDepth 16000 in
def g243D6 := limbs80 #[#[0x277b92ca887595354110,0xed2a4a824137dd953c4,0x866ebaec6a0759535412,0x21cbacaa9843b654d600,0x4872eb9aca10cdf7654c,0x110cbecaa9a43d954951,0x443f928a40887f15148,0x8110fb2a690221fa5492,0x204437cb2a40885f9744,0x50110bf2ea90221bed95,0x940443f8a8a80887f121,0x550110f72a8a0221ee50,0xd5404437db2a80886f96,0x2154110fe242a82217e5,0x58950443bca92a0887f2,0xb7254110df6c4a8221be,0xed91504437cb22a0885f,0xfb7048510bf6e8a8221b,0xf950921443f9b8242885,0x7d55348510fcaa490a21,0x1bdd95214437ab2a4288,0x85f77548510beaea90a2,0x21bd59621443eaa9c428,0x887755254510beaeb10a,0xa21bdd89514437ab12a2,0x2887755454510beee4a8,0x8a21bdd91514437ab22a,0x84885f57294510deac52,0xa92213f5d942442fbb8a,0x2a48867d6554910ddac4,0x6b1221bedc1624427ebb,0xaac4884ff7458910dbaa],#[0xe9b1221b754f624427fb,0xb8aa8884fd75d89109fa,0xaecaa221af59154442fb,0xfbaac8884ff72591109f,0xfaebb22213f5cb644427,0x76392ca885ef72595109,0x9fee4b2a21bbdc965443,0x27eb96ca884ff7459510,0xfcaa490e213f5d36544,0x437ab2a43887d5534871,0x10beeea90e217d5d521c,0xc437ab12a38877552547,0xb10dbac6a9621bb58952,0x2c427ebb2a58867d6554,0x41209feeab1621b754d6,0x41482fcb8482905fb715,0x94520edaa4a8a413f5da,0x5654827ebb4a2905f970,0x1503209fee8b2a413fdc,0x4940c837cb0a81907ba4,0x6550320f72a8a0641fa5,0x58551c827ebb483906f9,0xd6554720edaa4a8e41bd,0xd58651c827ebb2a39067,0xed52587209faed28e41b,0x3fdd161c836ea9ac3906,0x6ed6454b209feeab0e41,0x13f5d954c835eb22a990,0x7795254140bf6e2a828,0x81b7d8d21502fdb8242a,0xa06df63545409feec90a,0xaa13fdc565502dfba2a2],#[0x2a875d5348550edaa490,0xaa17e5c2215427fbb24,0x42a875d5388550ddec51,0xb0aa17bdc9615427ebb4,0xcc2a85f97098550ebaa6,0xd30aa15f5d661543aea9,0x96c2a867d52d85509fae,0xa6b12a13f5d3615427eb,0xba6c4a84fd71d8950eba,0xae5b22a13f5c7645427e,0xb28ec090ef551d81219f,0xbaa7b0243bb54b604877,0x7ebaec090cfd74d8121d,0xcfecaa8a43db54951486,0x7bbb2aa290df77054521,0x1cfecaa9a437d5c25148,0x873fb2aca90f5f6554d2,0x219fae1b2a433fdc1654,0x8876ea9ac110ef551582,0xa21deac4a8c43dd54951,0x28867ebb2a510e7d6554,0x49319feeab1443b754d6,0x528c77ca92c118df7715,0x54a31ddac4a94637ddc5,0x5628c67ebb2a518e7d65,0x258151bd8e4b02a33fdd,0xcb605473ea96c0a8def7,0x71989519fae9b02a33f5,0x5d3625467eb86c4a8df5,0xd70d9151b7ee8b1aa33f,0xfdc1629467eb96c8a8cf,0xdd72185539fae5b0aa73],#[0x8090058002eeb96c2a9d,0x3d83402c82502181a012,0x805485305185004c8450,0x87306d86606286105d85,0x9189008e88708588007a,0xa0a48a109b89a0968930,0x8bd0b98b60b48af0ad8a,0xcd8ca0c88c50c38c20be,0x40e28df0db8d80d48d10,0x8f90f78f40f08e90e58e,0xd90a1049031019000fc,0xa12892511f91e1169111,0x93513393213092d12b92,0x4394214093f13d93c13a,0x415294f14d94a1489451,0x96115f95c15a95915595,0x6f96e16a969165964162,0xe17c97b1799761749711,0x98f18998618498317f97,0xa59a419e99d199996192,0x81b69b31b19ae1ac9ab1,0x9d11c99c61be9bd1bb9b,0xe59e41de9dd1db9da1d6,0x81f49f31f19f01ec9eb1,0xa09205a042009fd1fb9f,0x1da1a218a17211a0e20a,0x22ea2b229a26222a1f2,0xa4123da3a236a35233a3,0x4fa4c248a47245a44242,0xc25aa59257a54252a512,0xa34d128c115110a61a5,0x11511880d900c20324c],#[0xa31285352038d61880c1,0x605230d86362034d48a1,0x8105210a141000000410,0xc8a84222a1000c141001,0xc04602084514246a10e0,0x28c1030400001105210,0x800004441421104440c2,0x10018180040800e0,0x1a3040c10e04006040,0x10c00100003040c10e07,0xc10004006040c104030,0x30800163041004200000,0x410042001810043110,0x401080000060400000,0x40050400304000000000,0x504000141000030,0x4003040004410008100,0xc203040000c100000005,0x20008100040810504440,0x40150400304002001004,0x4585620300080040030,0x181052408549084300,0x10010042005e202000,0x5810504000040c100000,0x5c58203040410014100,0x4000040c105040030400,0x4104040c100001040030,0x4001000000000,0xb030800000604]]
def g243H6 := limbs80 #[#[0x1d3605b23080048,0x70000000050800020800,0x3ce31312e4280060,0x291a44000000000,0x457b070061c,0x2a1000000001d450a00,0x600163c000000005880,0x516f12000a61,0x80000000000160c0d981,0x394d000000000004c391,0xa4000000000b,0x519000000,0x4eb9c780000000000000,0x1c7e090000000000062,0x14eecb830000005a50,0x0,0x78492800250000c1a00,0xdc20000]]
set_option maxRecDepth 16000 in
def g243D7 := limbs80 #[#[0x754d50b7d8d40b758f10,0x59421b758c21be58021d,0x110fe48110be582319f,0x510fd48510fe54110fe5,0x10fd94510fd54510fd88,0xf754d10bfd8910bf589,0xbfd9110bf59110f794d1,0xd48710bfd9510bf59510,0x54f10bf58b10fd54710f,0x4920fe54120bf59710f7,0x320bf59520f754d20fb5,0x20fb54b20bf58720fe50,0xbf59720bf59320f754f,0xbfd8550bf59540fe5414,0xfd9150bfd8950df54950,0xd8121bf59421f754c21b,0x4d21fd94521fd54521bf,0x521bf59521f794d21f75,0x21fd54621bf58221bfd9,0x1bf59621f754e21bf58a,0xbfd8151bf59631bf58a3,0xfd9151bfd8951df54951,0xd8553bf58a51bf58251b,0x8510f7d8553f718553bf,0x910ff50910ff54510ff4,0x10ff55110ff58910ff54,0xff54b10ff59510ff591,0xff54520ff90520ff5052,0xf90720ff55120ff94520,0x55320ff94720ff54720f,0x4540ff48540ff54530ff,0x550ff88550ff48550ff5],#[0x50ff58950ff98550ff58,0x1ffd8121ff58121ff591,0xff58d21ff54d21ff5452,0xfd9521ff59521ffd8d21,0x54a31ff54931ff54a21f,0x8951ff58951ff58151ff,0xff59151ff58d51ff9,0x30d30b809607b059029,0x92001c21a017e14e11e1,0x30a2e12b128f26d24b22,0x304003de3bc39a37f34f,0x350a4e84d44964744524,0x6296005d05ae57e55553,0x4872670b6e26a4682652,0xe85382a7f37bc7a17637,0x9729499208f78c789086,0x8aa61a3fa169e69b698d,0x7b2cb18b04ae2aceaaca,0xbfebeabcfbbbba0b77b4,0xadc99c7ec63c4fc34c19,0x3d48d2dd0bcf0cdccc1c,0xdfede3dc8dadd99d85d6,0xade8be70e5ce48e2de12,0x231c018285ef0eceec1e,0x32b20889231c2093600d,0x28318185071068a1018,0xe1e1cb838c6050e30d1,0x383a31898e43186911b1,0xa103841c1510f10ae242,0x852c3b085488a0232068,0x1c20e06087889308d463,0x9a31e2468a8c8880b18f],#[0x63888a38303263488d14,0x1c54202021a023249860,0x5081a18608080a31c316,0xd1018a10344490069610,0x40c1000d145868c8c3c,0x464442e9118810a87462,0x22e542844608088222c8,0x88e00614182802c49644,0x85064888b16323222154,0x99191102840406017185,0x2025453254305264462a,0x441518b95480c40a1820,0x9b2080c1489510284040,0x41a2841614c424300223,0x63430a18b23101821e18,0x8684c048502345464174,0x3972c111820200746507,0xa2050e14305080808046,0x4706345081030d2c1831,0x400d2c3188c110c0473,0x7185850a0c60b0e28406,0x4b960c3020804b0a1808,0x8b096182020380b0a1,0x18d14304c23618e18304,0x61d28a1838c302040202,0x5803844c303981130c8,0x2e382450090e10716083,0x343a144319223831c202,0x10a5c32c54708462901c,0x50cb08082a21018d1014,0xc106441432220c868c40,0x4204443190c3230a1862],#[0x430a5428258807048042,0xe84a86584151c2062a1,0x3840464aa1222172a203,0x1a1086030c14b0619004,0x1865cb230c2210858414,0xa5c308282465c20c15,0xa10b025cb0458a8e4024,0x192c343301110]]
set_option maxRecDepth 16000 in
def g243H7 := limbs80 #[#[0x12010305000300304091,0x32502010203420015334,0x10071200100320110,0x61d0000000001c1340,0x786800180700000000,0x555259f2b0001cf60000,0x7608ccfd14000014b,0x8000d5850e000053f510,0x835100000005340b0b10,0x2e34c000e4880000012a,0x20800000000001a,0x20a200000039680000,0x10530000,0x2ae0000,0x745848145eed6000000,0x85d000000,0x0,0x1981c1000000003000,0x0,0x28a00051f4,0x885e9aa0000000000384,0x64f0000000000792,0x9312c000000000000000,0x1600001a000000000038,0x2cf9490690007c6a8898,0x60ff1254410005,0x6186e5000000052f0000,0xa0000000000000000000,0xdd930000000000000210,0x4c000f9e80014560c425,0x4080010ca00000000005,0x1638000000000129ca],#[0x8008000,0x2452000000000386e000,0x6b1d0000000000baa000,0x9f10545f000000000190,0xcda00085770,0x24800000000000,0x5462973cf00000000,0x15ec0c0006d9421c000,0x20b0190000000000615,0x0,0x87e6cb43000000189300,0x20f81680011,0x0,0x22e80004f20004200000,0xc140009518000000000,0xf27800,0xd4000000000000000000,0xa2c621000000000068,0x8e60005be826c0000,0x2c6c0003068,0xc0000000062b0000,0x1783000,0x0,0xe320000001c7500,0x4c8000001e4b16280000,0x6a9400143d2,0x21420000002124,0x800000000054ac000c31,0xd000000164e28e000180,0x78000033202000348c88,0x7100001c8d4000000056,0x93483600000030b00002],#[0xda100062c116de1505a3,0xd4fc0e024311a5af9076,0x5a9d55800000069a,0x48f780000000000,0x5a00080c000000000000,0x196c0004abd3bf851d,0x8350000b360000,0x0,0x15120000000000000000,0xf0002864061121000000,0xa95e2f709483f2b,0x79500001ab00000,0x830000aa700058980000,0xe9d91e51afc2e0000005,0x5938000000c3ff2a417b,0x0,0x204400162e00000e400,0x720000000003c423a700,0x7000213c0000005a01b,0x76149800050262d416f9,0x34440000000000,0x51e000,0x2ac6cfc000602800,0xb80017390000b0442400,0x84d000000000000041,0x43d220c0000,0x0,0x800000000000006b0000,0x922c07800000064b,0x131d0b0b72c000000000,0xcfd88e4df54666,0x21d80],#[0x39100000,0x1df0,0x3cc400042a8000000000,0x7000000016e93b9b1a8a,0x2806000000000000175,0x0,0x10210afd318ad40000,0x83eea3a9f16604501330,0x2b204a6668000,0x1ae40000002b1]]
def g243D8 := limbs80 #[#[0xd20ff887f443bca7dd53,0x43fd50fea07f4c3fe41f,0x7fc63fd31ff10ff487f8,0x780c001fd53ff28ff54,0x318ae24c7e1bc5d13839,0x21a21cd523438f6390d5,0x44708e680426086a1e28,0xc711e20244601a50d11c,0x23151987882c710058a2,0xa8114240e1909826911a,0x46a1e20408019a41438a,0xe39719850e2c66905082,0x308b401a830201718a60,0x1650219838c34068650a]]
def g243H8 := limbs80 #[#[0x12051201100001101020,0x27017023a0000a146,0xd13000000000000,0xe5372d10000000000000,0xf1953c00000000000058,0x3db0910bb3b5ad762011,0x100000000000000080e9,0x816000000000cd8646d3,0x4000000000d6e000000,0x30153a5b6db58d593c4a,0x3b779e88245c000000a2,0x4000000000044f000000,0x503000f27000d,0xaaf00000059,0xd5345a000000000,0xac30000000000,0xf3f00000000,0x0,0xeb0600000000096b0000,0xd4b00000000035,0x323a11e9788047000000,0x20006020000004910003,0x61f0000000009c200031,0x664c9f45000de1,0x8991410,0xc61783f4e000ce800,0x9cd00048520000000000,0xd636a1c467adf550363c,0xd68ae000000000088a82,0x69000000e4cd5f85221a,0xdb18e54000a0c00016c3,0xe39808321c5],#[0x84d72e000000000,0x107b2900092c0000000,0x0,0x1cea57000000,0x4956000000000000b5b0,0xc261e7e350006a883,0x817000000000,0x3c7000b960000000,0x65100000000000000000,0x551d2ae000000000,0xb010000000,0xb4a00,0x220000008650002c19a2,0x528000000f55e,0xb0d13a00000,0x25000000000000000000,0x82f0002646,0xe4400030f00000,0x6cc00051e00029df1b,0xb2a843000d6043eb9f0,0xe38000b4200000000000,0xd5000010000000000a6a,0x952b0000000000001498,0xd30a33000000414ed,0x9200000090ae24000000,0x2]]
def g243D9 (j : Nat) := if j=0 then 0x1882013f else 0
def g243H9 := limbs80 #[#[0x28200000b7ce,0x34727000000000000,0xc6dd7d3001c100,0x708000000058a0000,0x1e480000000003100000,0x60000000001c80000,0x78c000000000,0x6200000000706f400,0xa0000000000278000000,0x1d7158a51d,0xc40000,0x69600000000015280,0xea600000000000000000,0x38]]
def g243L : Nat → Packing
  | 5 => (38,4,5,0,0,9,0,g243D5)
  | 6 => (198,3,5,0,0,12,0,g243D6)
  | 7 => (111,2,5,0,0,12,0,g243D7)
  | 8 => (17,1,5,0,0,10,0,g243D8)
  | 9 => (1,0,5,0,0,0,0,g243D9)
  | _ => emptyPacking
def g243I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 12 127 2 11 6 1 g243H6
  | 7 => lookupWord 62 631 4 13 8 1 g243H7
  | 8 => lookupWord 37 379 4 12 7 1 g243H8
  | 9 => lookupWord 7 107 1 10 5 1 g243H9
  | _ => fun _ => none
def g243 : Forest := ⟨243,9,fun i => g243Y[i]?.getD (0,0),g243C,g243A,g243L,g243I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P5_0 : block g243 5 0 38=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g243B5 : block g243 5 0 38=true := g243P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P6_0 : block g243 6 0 12=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P6_12 : block g243 6 12 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P6_108 : block g243 6 108 90=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g243B6 : block g243 6 0 198=true := (@block_merge g243 6 0 12 186 g243P6_0 (@block_merge g243 6 12 96 90 g243P6_12 g243P6_108))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P7_0 : block g243 7 0 7=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P7_7 : block g243 7 7 61=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P7_68 : block g243 7 68 43=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g243B7 : block g243 7 0 111=true := (@block_merge g243 7 0 7 104 g243P7_0 (@block_merge g243 7 7 61 43 g243P7_7 g243P7_68))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P8_0 : block g243 8 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P8_2 : block g243 8 2 15=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g243B8 : block g243 8 0 17=true := (@block_merge g243 8 0 2 15 g243P8_0 g243P8_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P9_0 : block g243 9 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g243B9 : block g243 9 0 1=true := g243P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243T : checkedTables g243 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g243 0 0 0 = true)
  · exact (rfl : block g243 1 0 0 = true)
  · exact (rfl : block g243 2 0 0 = true)
  · exact (rfl : block g243 3 0 0 = true)
  · exact (rfl : block g243 4 0 0 = true)
  · exact g243B5
  · exact g243B6
  · exact g243B7
  · exact g243B8
  · exact g243B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243G : graphValid g243 (boundsBefore K238) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low243 : Lower true (varsX 243) (graphGoal 243) 10 := lower_forest (g:=g243) (i:=0) (hints:=16777284) (before_sound K238 V238) g243G g243T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K243 := extendKnown K238 10 [(243,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V243 : Known true K243 := extend_ok (m:=243) V238 low243 (by decide +kernel)
def g245Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3fffffc1fffff724e,0xb0ac1300000fc0000fff])),(BitVec.ofNat 152 (word80 [0x28428408401040324a,0x20a01209249249249249]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfc003fffe0ffe02922,0xe663708003f000fff000])),(BitVec.ofNat 152 (word80 [0x300b00500200822802,0xa44350030c30c30c30c3]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffc00000ffffbd84,0x995842c0fc000000003f])),(BitVec.ofNat 152 (word80 [0x408c09608425008984,0x99584096596596596596]))),((BitVec.ofNat 152 (word80 [0xffffffffff0000804d,0x6156a9c000003f03ffc0])),(BitVec.ofNat 152 (word80 [0x821021800086040005,0x411429e4924924924924]))),((BitVec.ofNat 152 (word80 [0x9171,0x18b1dc3f00003ffc0000])),(BitVec.ofNat 152 (word80 [0xe00e010838089160,0x18a08418618618618618]))),((BitVec.ofNat 152 (word80 [0x4e93,0x4f80057fffffc0000000])),(BitVec.ofNat 152 (word80 [0x300300210c0104411,0x42000160820820820820]))),(0x0,0x0)]
def g245C : List ColumnInfo := [(32,0,213,0,8)]
def g245A : List (List Nat) := [[],[98]]
def g245D8 (j : Nat) := if j=0 then 0x7f else 0
def g245L : Nat → Packing
  | 8 => (1,0,1,0,0,0,0,g245D8)
  | _ => emptyPacking
def g245I (_ _ : Nat) : Option (Nat × Nat) := none
def g245 : Forest := ⟨245,8,fun i => g245Y[i]?.getD (0,0),g245C,g245A,g245L,g245I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g245P8_0 : block g245 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g245B8 : block g245 8 0 1=true := g245P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g245T : checkedTables g245 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g245 0 0 0 = true)
  · exact (rfl : block g245 1 0 0 = true)
  · exact (rfl : block g245 2 0 0 = true)
  · exact (rfl : block g245 3 0 0 = true)
  · exact (rfl : block g245 4 0 0 = true)
  · exact (rfl : block g245 5 0 0 = true)
  · exact (rfl : block g245 6 0 0 = true)
  · exact (rfl : block g245 7 0 0 = true)
  · exact g245B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g245G : graphValid g245 (boundsBefore K243) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low245 : Lower true (varsX 245) (graphGoal 245) 9 := lower_forest (g:=g245) (i:=0) (hints:=33555716) (before_sound K243 V243) g245G g245T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K245 := extendKnown K243 9 [(245,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V245 : Known true K245 := extend_ok (m:=245) V243 low245 (by decide +kernel)
def g252Y : Array (Bits × Bits) := #[(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffff8007fffffc03f,0xe5c3109b84e000f00f0f])),(BitVec.ofNat 152 (word80 [0x140150350250148585,0x2143009904c111111111]))),((BitVec.ofNat 152 (word80 [0xffffff8007ffffc0,0x1a4b2dc05c400f00f0f0])),(BitVec.ofNat 152 (word80 [0x260260260360190909,0x9a4304804c4111111111]))),((BitVec.ofNat 152 (word80 [0xfffffffff8000000,0x7718e0d9950f0000000])),(BitVec.ofNat 152 (word80 [0x382b813813815e0e0e,0x7518e0d985777777777]))),((BitVec.ofNat 152 (word80 [0xffffffffffffffff,0xc8137847ab90000f00ff])),(BitVec.ofNat 152 (word80 [0x408c04404404600000,0x107842831aaaaaaaaa]))),((BitVec.ofNat 152 (word80 [0xff0000000000000000,0x45c463c762f000fff00])),(BitVec.ofNat 152 (word80 [0x3001801801801010,0x40c0204302444444444]))),(0x33a4d3e0015ffff00000,(BitVec.ofNat 152 (word80 [0x80c006006006002020,0xa05160010888888888]))),(0x0,0x0)]
def g252C : List ColumnInfo := [(4,0,248,0,7)]
def g252A : List (List Nat) := [[],[50]]
def g252D7 (j : Nat) := if j=0 then 0x7f else 0
def g252L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g252D7)
  | _ => emptyPacking
def g252I (_ _ : Nat) : Option (Nat × Nat) := none
def g252 : Forest := ⟨252,7,fun i => g252Y[i]?.getD (0,0),g252C,g252A,g252L,g252I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g252P7_0 : block g252 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g252B7 : block g252 7 0 1=true := g252P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g252T : checkedTables g252 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g252 0 0 0 = true)
  · exact (rfl : block g252 1 0 0 = true)
  · exact (rfl : block g252 2 0 0 = true)
  · exact (rfl : block g252 3 0 0 = true)
  · exact (rfl : block g252 4 0 0 = true)
  · exact (rfl : block g252 5 0 0 = true)
  · exact (rfl : block g252 6 0 0 = true)
  · exact g252B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g252G : graphValid g252 (boundsBefore K245) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low252 : Lower true (varsX 252) (graphGoal 252) 8 := lower_forest (g:=g252) (i:=0) (hints:=573003008) (before_sound K245 V245) g252G g252T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K252 := extendKnown K245 8 [(252,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V252 : Known true K252 := extend_ok (m:=252) V245 low252 (by decide +kernel)
def g127Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xf3a38808b46acc81d5,0xe080000000000fe03fff])),(BitVec.ofNat 152 (word80 [0x41218800946a4c00c5,0x8010a142850a142850a1]))),((BitVec.ofNat 152 (word80 [0x92add040298bc3743,0x1b400001fc00001fc000])),(BitVec.ofNat 152 (word80 [0x610adc040218ac3741,0x9458b162c58b162c58b]))),((BitVec.ofNat 152 (word80 [0x7508f40f734115d35,0x84000fe0007f0000000])),(BitVec.ofNat 152 (word80 [0x83508f00f334104d15,0x843870e1c3870e1c387]))),((BitVec.ofNat 152 (word80 [0xf25c4eb7aac1d04140,0x69007f0003f80000007f])),(BitVec.ofNat 152 (word80 [0x25c46862281904100,0x6803060c183060c18306]))),((BitVec.ofNat 152 (word80 [0x85835f63a014663a,0xd68000000000001fff80])),(BitVec.ofNat 152 (word80 [0x84035b618010403a,0x56aa54a952a54a952a54]))),((BitVec.ofNat 152 (word80 [0x116648158062bf0a8,0x15ff800003ffffe00000])),(BitVec.ofNat 152 (word80 [0x20001080023b028,0x118c183060c183060c18]))),((BitVec.ofNat 152 (word80 [0xce93272055b22080f,0xc3ffffffc0000000000])),(BitVec.ofNat 152 (word80 [0xca120700442000002,0x43060c183060c183060]))),(0x0,0x0),(0x0,0x0)]
def g127C : List ColumnInfo := [(4,0,123,0,10)]
def g127A : List (List Nat) := [[]]
def g127D10 (j : Nat) := if j=0 then 0xff else 0
def g127L : Nat → Packing
  | 10 => (1,0,1,0,0,0,0,g127D10)
  | _ => emptyPacking
def g127I (_ _ : Nat) : Option (Nat × Nat) := none
def g127 : Forest := ⟨127,10,fun i => g127Y[i]?.getD (0,0),g127C,g127A,g127L,g127I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P10_0 : block g127 10 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B10 : block g127 10 0 1=true := g127P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127T : checkedTables g127 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g127 0 0 0 = true)
  · exact (rfl : block g127 1 0 0 = true)
  · exact (rfl : block g127 2 0 0 = true)
  · exact (rfl : block g127 3 0 0 = true)
  · exact (rfl : block g127 4 0 0 = true)
  · exact (rfl : block g127 5 0 0 = true)
  · exact (rfl : block g127 6 0 0 = true)
  · exact (rfl : block g127 7 0 0 = true)
  · exact (rfl : block g127 8 0 0 = true)
  · exact (rfl : block g127 9 0 0 = true)
  · exact g127B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127G : graphValid g127 (boundsBefore K252) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low127 : Lower true (varsX 127) (graphGoal 127) 11 := lower_forest (g:=g127) (i:=0) (hints:=16778563) (before_sound K252 V252) g127G g127T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K127 := extendKnown K252 11 [(127,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V127 : Known true K127 := extend_ok (m:=127) V252 low127 (by decide +kernel)
def g191Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfff607e8a2c1076819,0x3208000003f000fc0fff])),(BitVec.ofNat 152 (word80 [0x28202e08241036008,0x10081041041041041041]))),((BitVec.ofNat 152 (word80 [0x2c635900a8df1f6,0x45280000fc000003f000])),(BitVec.ofNat 152 (word80 [0xcc2863090088d71f4,0x4508b2cb2cb2cb2cb2cb]))),((BitVec.ofNat 152 (word80 [0xfb234c3c9788551,0x5050003f00003f000000])),(BitVec.ofNat 152 (word80 [0x570fb234c3c9288151,0x104071c71c71c71c71c7]))),((BitVec.ofNat 152 (word80 [0xffe4b9325eaa878214,0xb440fc0000fc000003f])),(BitVec.ofNat 152 (word80 [0x9804b912508a848214,0xa406186186186186186]))),((BitVec.ofNat 152 (word80 [0x10b84759f40b063,0xa8e3f00000000003ffc0])),(BitVec.ofNat 152 (word80 [0xe00109046582408003,0xa8e14514514514514514]))),((BitVec.ofNat 152 (word80 [0x22c1b057070590e,0xe5540000000ffffc0000])),(BitVec.ofNat 152 (word80 [0x4090430501802,0xe5178e38e38e38e38e38]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x19d049c814980680,0x9c8ffffffff000000000])),(BitVec.ofNat 152 (word80 [0x1040090814100400,0x60820820820820820]))),(0x0,0x0)]
def g191C : List ColumnInfo := [(4,0,187,0,10)]
def g191A : List (List Nat) := [[]]
def g191D10 (j : Nat) := if j=0 then 0xff else 0
def g191L : Nat → Packing
  | 10 => (1,0,1,0,0,0,0,g191D10)
  | _ => emptyPacking
def g191I (_ _ : Nat) : Option (Nat × Nat) := none
def g191 : Forest := ⟨191,10,fun i => g191Y[i]?.getD (0,0),g191C,g191A,g191L,g191I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P10_0 : block g191 10 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g191B10 : block g191 10 0 1=true := g191P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191T : checkedTables g191 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g191 0 0 0 = true)
  · exact (rfl : block g191 1 0 0 = true)
  · exact (rfl : block g191 2 0 0 = true)
  · exact (rfl : block g191 3 0 0 = true)
  · exact (rfl : block g191 4 0 0 = true)
  · exact (rfl : block g191 5 0 0 = true)
  · exact (rfl : block g191 6 0 0 = true)
  · exact (rfl : block g191 7 0 0 = true)
  · exact (rfl : block g191 8 0 0 = true)
  · exact (rfl : block g191 9 0 0 = true)
  · exact g191B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191G : graphValid g191 (boundsBefore K127) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low191 : Lower true (varsX 191) (graphGoal 191) 11 := lower_forest (g:=g191) (i:=0) (hints:=1347) (before_sound K127 V127) g191G g191T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K191 := extendKnown K127 11 [(191,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V191 : Known true K191 := extend_ok (m:=191) V127 low191 (by decide +kernel)
def g223Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfffc8b4b42714a5d45,0xf00000003f000000fff])),(BitVec.ofNat 152 (word80 [0x80500b4a4051481d04,0x7249249249249249249]))),((BitVec.ofNat 152 (word80 [0xc00356b060138c0de6,0xb8000000fc0000fff000])),(BitVec.ofNat 152 (word80 [0x19b12b060120c0dc6,0x280c30c30c30c30c30c3]))),((BitVec.ofNat 152 (word80 [0x1d86c74701fa20e,0xcc00003f00003f000000])),(BitVec.ofNat 152 (word80 [0xae1d06c74701ea00e,0xcc1c71c71c71c71c71c7]))),((BitVec.ofNat 152 (word80 [0xfffca0b17dee80f842,0x8a000fc0000fc000003f])),(BitVec.ofNat 152 (word80 [0x1300a0b13d2680e042,0x88186186186186186186]))),((BitVec.ofNat 152 (word80 [0x60af92a4ff84a1,0x9003f00000000003ffc0])),(BitVec.ofNat 152 (word80 [0x1c00600592a4b38021,0x90514514514514514514]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1d50ac8d518315,0x72fc0000000ffffc0000])),(BitVec.ofNat 152 (word80 [0x20000d008089410211,0x12618618618618618618]))),((BitVec.ofNat 152 (word80 [0x32304911220201a,0x5fffffffff000000000])),0x820820820820820820),(0x0,0x0)]
def g223C : List ColumnInfo := [(2,0,221,0,10),(4,0,219,0,10),(8,0,215,0,10),(64,0,159,0,9),(1,0,222,0,8),(16,0,207,0,8),(128,0,95,0,8),(5,0,218,0,7),(9,0,214,0,7),(18,0,205,0,7),(20,0,203,0,7),(132,0,91,0,7),(0,4,27,192,6),(17,0,206,0,6),(24,0,199,0,6),(65,0,158,0,6),(80,0,143,0,6),(7,0,216,0,5),(19,0,204,0,5),(21,0,202,0,5),(25,0,198,0,5),(64,4,27,128,5),(128,4,27,64,5),(129,0,94,0,5),(144,0,79,0,5),(77,0,146,0,4),(192,0,27,0,4),(192,4,27,0,4)]
def g223A : List (List Nat) := [[],[64,49]]
def g223D5 := limbs80 #[#[0xa1079ec5a9a1f8259540,0x454298ddab08c9908b02,0x2eca841e7b16a3925da7,0x825d76083cf62d4d09c1,0xa704b82cb079ec5a9a13,0x772606705960f3d8b533,0xd1b00406e4b2c9c7b36a,0xc584e4d80dc965c39753,0x3d9b50c8d01b92cb471e,0x36c2a91e612306028e]]
set_option maxRecDepth 16000 in
def g223D6 := limbs80 #[#[0x70596ca9a2dd56458140,0x957154040873e8d98dca,0x2e89655cd50103d63a25,0x103c6976e496554040f5,0x8654140f1ae89955d950,0x9975e11605021f7a165d,0x2eaba25956458140a2fe,0x58140f0e5d5655916050,0x8559160502eaba261564,0xb9965d66458140ba6e8d,0x140d665d593211605034,0x5d5605033998564c8458,0xa161f8259540b3668c96,0x87b6a687e09655029e7,0x5655029e7a165f825954,0x2597559540b1d684965d,0x6ee539061d65502c6da2,0x550317b95e418759540c,0x58759540c3ee5b9061d6,0xe4f9161d655031e792e4,0x31e7a2e458759540c75,0x65d540c1fe5b9561d655,0x185e01765020ffa96188,0x1f7a1657805d940a6ee9,0x8240f0e5d56455160902,0x55516090393b87615545,0xba25978055240b4ee9d8,0x40a73e8d87e0965903b2,0x1d659029cfa365f82596,0x2e4d8759640c73e4f926,0xb8e69a64551605431cfa,0x60542f31a12115458150],#[0x115458150bca68884551,0xee916559160542f19a32,0x542ea9a29d16458150b8,0x6458150ba668e7459160,0x888459160542eb1a1211,0x2e99a32116458150baa6,0x58150b8e694845916054,0x84211605433998464c84,0xbba96108458150acee95,0x150c73e4f9261f605423,0x5d9545431cfa2e4d87d8,0x98e497655150d4b25392,0xd47253935d95454316c,0x16454315c98e4d765515,0x6448059150cdc6159120,0xda61592201645431f187,0x45433598564c8059150c,0xc80591508deea5852016,0xe4f9261f645421fba961,0x431cfa2e4d87d9150c73,0x39d150a73e8d7660a745,0x57660e745429cfa25d98,0x1eda8e49769d150877ea,0x95508776a3935da74542,0xe1165542b71a1a43845,0xf95e4b835d950a9e69a9,0x50e56e1783e017654334,0x9765429e7a1613825d9,0x3a13825d950a73e8d84e,0x87b6a684e09765429cda,0x765429e7a1653825d950,0x4b835d950a7368e94e09],#[0x5e8584e0d7654354f95e,0x5429cfa2613835d950a7,0x835d950a7368a84e0d76,0x5392e0d765421dda9a13,0x31cf94e4b835d950c736,0x5d950c6765094e0d7654,0x94e0d7654295da525383,0xcfa2653835d950a75e85,0x950a7368a94e0d765429,0x5c5609421bfa9610845d,0xa16578059160d7865992,0x9ae69195201645823f3,0x164583639a4654805916,0x65780591609bce8595e0,0x67e8d95dd2645826eba2,0x45829e7a25d5811d1609,0x5821d160a75e8d756047,0xe957460c745829cfa35d,0x829cfa25d5831d160a67,0x5dd160877ea57560c745,0xb93617745831cf93e498,0x9cfa361f8259660c73e8,0xd760a73e8d97e0965982,0x4e0975d831cf93e09805,0xda3a13825d760a79e858,0x6087b6a684e0975d829c,0x975d829cfa3643825d7,0x3a53825d760a79e8594e,0xc76e63935c0705969cda,0x705969e7a15d3825c165,0xd3825c165a7368e74e09,0x3e5792e0d705961eda99],#[0x5969cca7e4b835c165cd,0x835c165a75e8574e0d70,0xa674e0d705969cda29d3,0x69e5a9dc9819c1658776,0x9c165cd9655926067059,0x92606705972e59664981,0xe6a7649819c165c7965d,0x165c9d65995606705969,0x606705969f3a065d819c,0xa365d819c165a79e8997,0x5a6de9197606705969d7,0xa705963cfa3663729c16,0x663729c165a73e8d98dc,0x72e8d80203725971cfa3,0x25971eba960080dc965e,0xd80dc965c73613936037,0x6a191a03725971cf84e4,0x25cfa366280dc965c79,0x1f0380640b0130200340,0x7c0ec1983005a094110,0x61602a85209e13024846,0xc03686a0ce1903085e0b,0x4788c1122183f0760e61,0xa914c28c5009812a248,0x61863005e8ba1642bc56,0xb63606a8d219e330648c,0x3d4790ef1d83a4708de1,0x4851072084047f0fb1f0,0x39242424788d91822043,0x4127c4ec9c13525a4a89,0x2ac54ca814d29451ca21,0x5d4b916f2ce57cae159],#[0x34c5187308604bf17b2f,0xd119f338664cb1933206,0x1b73686c4d71ab350694,0xf398724e31c33806f4dd,0xdc7acf41e53c477cee1c,0x82102a023fe7f0fa1f13,0x1f17c01416,0x1c4080030200003020,0x0,0x80000000001e0908080,0x7860800000000108,0xe102000000000000000,0x8000000000000000000,0xb10200000000002c4,0x82000000000000000000,0xc30371,0x0,0x1a708400000000000000,0x6c208000000000002]]
def g223H6 := limbs80 #[#[0x6007a4000023a8ac6002,0x12,0xe4404140050000001,0x8080]]
set_option maxRecDepth 16000 in
def g223D7 := limbs80 #[#[0xb92a02074c5517154040,0x81c397655150103a52a8,0x957254040eb8b2ae2a80,0x103ab2cab9aa02075a5,0xcbb2caa8081d39765515,0x2a02055ee5d6554040e3,0x5e792595711038f32abb,0x82594408f7cc2cab9081,0x31daedc12ca2065b5d7,0x930eb28811ed97e09651,0xc2055be49865d4408f7c,0x975591605029df24c2ae,0x58140e5dbaac8b0281cb,0xf3326422c0a05ae65a64,0xeb2a815e992dd560502,0x47be4987595408fbc8b,0x25974090337709c02eca,0x640d9cb2f00aa4817ab9,0xf26c3acb2047be498759,0xb02a1e3964551605423b,0x77e4d87d81508f7c930f,0x1f645423df24c3ec8a84,0xdb5c1100b2aa11df936,0x7c12eca865ee17805d95,0x4a19cf92e0d7654339f0,0x5917158250ef0c92e2b0,0x609439e6c8b8ac12873c,0x75b22e4b04a1ce9645c9,0x12e32872e5d16458250e,0x15f190d91719433cb0cc,0x3645ca50af8c850cb8ca,0x5833cb0ac12e23057a64],#[0xc9100b22c16f19120164,0xc8b05b664c8059160b74,0x9d7460c74582cf32a402,0x5dd1608dfcc2e83a2c19,0x63bf26c2ee8b047be498,0xee4b82cb1fb985c07059,0xb2e79dc9819c165ce7c1,0x80203725963db31b94e0,0xc965ae7c9b01b92cb9e9,0xd724b2aa02057964680d,0xca8081d797659550103e,0x779e49655c440ebccaae,0xe0965103adaebc12ca20,0x40cf6c3f04b2881ced76,0xedc12ca2057b65f82594,0x28819ed97e09651033da,0xbe49865d440cf7c930eb,0x576102bdf24c2aec2075,0xf5cb22c0a8281cef9261,0xbb2a0a057ee417654140,0x813ef9261950502aff2a,0x5186541409efc9b0ca82,0x5023fb2ec32a0a04efe,0xdc82c8b0281eb9905916,0x2c0a072f5d56458140f5,0x4ff965d56050337aebc2,0x64581408ffcab0eb0281,0x3b72eab22c0a07ae595,0xaac8b0281dbb75591605,0xa07ae6156458140f5cb,0x89859160503d770ab22c,0x58140edcbacc8b0281eb],#[0xb72ea422c0a073e5d764,0x8b0281bb98521160503,0x76edd78458140edcbaf,0x559560502fd724b2ac0a,0x140b7dcb2eab0281d797,0x72cbaac0a073e2597558,0xb02817eb92615605039f,0xeee518558140bedc9b0a,0x9660502fd724b2cc0a05,0xcfcc32eb30281d79755,0xac26c0a067ee61759814,0x28197d855d76050337ae,0xe4985d8140a7fcb2ebb0,0x6550277b29c02caa04fb,0xf6c3f04b2a81d6d75e09,0x12caa067ba1f8259540c,0x19ef76e09655033daedc,0xf8259540cf6cbf04b2a8,0x5038f92cbaacaa067ba5,0xcaaecb2a81c7f965d565,0xcaa055f6577659540abf,0xff9661d65502bef22c3a,0x7595409fbc8b0eb2a814,0x33f720c3acaa04fbe498,0xb0eb2a811ff9061d6550,0xa067be498759540cfbc8,0x9661d655032ff2ac3aca,0x95408ffcb30eb2a818ff,0xfb21c3acaa053f65a875,0xcbaa8157f955d9755023,0x55f656765d540c7fc32e,0x219755031ff0d3b2eaa0],#[0x40af6c910cbaa815f591,0x20c32eaa063f618865d5,0xaa815f79161975502bf7,0xe642865d540af7c930cb,0x1765031ff0d432eaa057,0xeddc2700bb281bbb84e0,0xc02eca067e617805d940,0x811fd95e01765033f70b,0x45855d940afdc830abb2,0x6502bdf24c2aeca057de,0x5c92cba04813ef926167,0x2c1207ae5915458240fd,0xd797555160903d76c8aa,0x5458240f9cb2aa8b0481,0x3b770eaa2c1207ce615,0xaac8b0481db974591609,0x12073e5d76458240e7cb,0x97559560902fd724b2ac,0x58240bf5c930ab0481d7,0x3f70ec2ac1205f6e4d85,0xeb04815fb9761560903,0x5eee416455240afccaf,0x559154903a7aeab22a92,0x240e5ebb2c8aa48173f9,0xb2bb22a9205ee6436455,0xaa481cbd76d9154902e7,0x5f65d6555240cbec3aca,0xd554902aff2eb2aa9205,0x9fdc830caa48197d865,0x4c32a9204fde45865524,0x481f2f92595549027df2,0x6557655240e9ebb2caaa],#[0x54902f7720c32a92074f,0xd7c930caa4817b791619,0x32a92056fe5d8655240b,0x15bd97a1954902f73214,0xf8559240cfcbaf00b248,0x9033f2eac06c92047f65,0xc930bb248197d855d764,0xe92057be49655d2409f7,0xfd98d9574902bf321b2a,0x259640eb6baf04b2c811,0x33daedc12cb2067b61f8,0x708b2c819ed97e096590,0x2065f5d784596409fcc8,0x9261d65902bbf26c3acb,0xda40cefc9b0eb2c819ef,0xbf26c2aed2057be49855,0x8b02a11fd94e1576902b,0x6cfe115458150f1eb22a,0x551605426fb29c2ac0a8,0x50f9d322a8b02a1f3964,0x8aa2c0a879ed9154581,0x2a1f3b8455160543e71,0xee595458150bbccb2a8b,0x160543cf2cab22c0a85d,0xf5d3a2c8b02a1eb97459,0xb22c0a873edd16458150,0xa1ebb8459160543d7108,0x556458150f3dc2ac8b02,0x542ef32b322c0a879e6,0xccbcc8b02a16f9969916,0x2c0a873edd36458150af,0x7e9929d160542df72cba],#[0x7458150becc9ce8b02a1,0x427f3313a2c0a85be65a,0x8908b02a1d7965dd1605,0xa85fa6488458150bf8c,0x98421160542fb326422c,0x58150bbcca908b02a1bb,0x77709422c0a85dee5584,0x8b02a1b7b85a1160543,0x87dae496558150bbccad,0x4e1560542ef728b2ac0a,0x150dbcc32a9302a17799,0x72caa4c0a85de6595498,0x302a1f6b9259660542ef,0xcf61154d8150bbdca2cb,0x53605432fb0eaa6c0a86,0xdb7c930bb02a137d985,0x4c3ec0a84dfe5185d815,0x2a19df9361f605433df2,0xe497655150bbdc82ecaa,0x54542ebf26bb2a8a85db,0xbdc82ecaa2a173f945d9,0xb2a8a855fe417655150e,0x1d5f935d954543adf24b,0x17655150e9e4a2ecaa2a,0x5432f930bb2a8a874fe5,0xca4ecaa2a1779909d954,0xc8a85fc6448059150b9e,0xd99320164542fd324402,0x59150dbcc2900b22a17,0x36f30bc02c8a867e61c8,0xf00b22a19fa87e016454,0xa867edd380591509beca],#[0x95e01645436f2cbc02c8,0x9150cfcbb700b22a1b79,0x73213a2c8a867eddb805,0x8b22a17ad929d164542f,0x53f65b7459150bcec9ce,0x5d964542e7f28b2ac8a8,0x50aefc9aecb22a15ef92,0x29bb2c8a856fe5176591,0x22a15f79161d64542b7b,0x7e4d8759150af7c930eb,0xd645427f720c3ac8a857,0x9f7c930eb22a13f79161,0xc3ac8a84f7e4d8759150,0xa173f94596645427f321,0xd98599150cbec3acb322,0x45432feecc2cc8a865f5,0xfc9aed322a15ef925da6,0x4c8a856fe517699150ae,0x9fb7460364542b7b29bb,0x74d9150cbec2ee9b22a1,0x436df24c2ec8a853f65b,0x9b0fb22a13ef9261f645,0x8a867be4987d91509efc,0xf86595745433bf26c3ec,0x5d150af7c92ecba2a1a7,0x1ff0cbb2e8a8577e4d76,0xecba2a15f9909d974543,0x86de595809d150c7fc34,0x560a745433f2ecc04e8a,0x150cf6bb3053a2a1b6d6,0xaecc1ce8a86d7595839d,0x3a2a1a7d86596745433b],#[0x77e4d769d150af7c92ed,0xda74542b7f28bb4e8a85,0xeb7c92cbba2a18fd865,0x6c02caa85dbe49805955,0xaa1b7984e0165542ebf2,0xe138259550db6c2704b2,0x65542ef720c22caa86db,0xb7c9308b2aa177791611,0x22caa85de6428459550b,0x175d93a1165542edb254,0xa8459550d9fc2508b2aa,0x542ef321c22caa859f65,0x48708b2aa1b7990e1165,0xeca86f6e0f805d950dbd,0xcf83e09765436f70bc02,0x35d950db7c2f04bb2a1b,0x37b721c1aeca86d7e178,0xf06bb2a1bcf92e0d7654,0xa8677e0f805d950dafca,0x85e0176543bb707c02ec,0xd950ee7c1f04bb2a1d7b,0xdb09c12eca867b213825,0x4bb2a19ee84e09765433,0x75be17825d950cf7c270,0xe09765433db29c12eca8,0x50eedc8706bb2a19ee94,0x9c1aeca8773e4b835d9,0xb2a19dd84e0d765433b9,0x7e13835d950cef42706b,0xd76543abf0bc1aeca867,0xcefc8706bb2a1d5f95e0,0xc1aeca8677253835d950],#[0xa19de94e0d765433bb29,0x10845d950cefca706bb2,0x6542bf720c22eca866f6,0x7c9308bb2a15f7916117,0x2eca8577e4d845d950af,0x5f990a1176542aff2ac2,0x845d950af6c9508bb2a1,0x4337f09422eca857764e,0xa70abb2a157d95a11765,0x12877c5917158250abec,0x1965c560943be308b8ac,0x58250ef4b22e4b04a1df,0xb72e8b22c12877a61172,0x8b04a1cfb8759160943,0x857e6538758250afdcbb,0x6e0164943b72e9c02c92,0x250cfcc3f00b24a1cf97,0x32fc02c92867e5db8059,0xb22c19fb75e01645833f,0xbee4165591609fccaf00,0x164582ddf24b2ac8b05,0xb7d4b900b22c16f9952,0xbc02c8b07aedd3805916,0x2c16ef925d564582df32,0xe517559160b6fc9aeab2,0x6458337b0bba4c8b05af,0xfecc6eb322c15bd95dd2,0xaec8b05bbe4975d91608,0x12ff985d764582dbf26b,0x5821d160cfabab023a2c,0x5833baeac18e8b067b5d,0xcc2e83a2c15bf955d074],#[0xe8b057be49751d160cdf,0xff985d474582bbf26ba8,0x51d1609fcc830a3a2c11,0x2bdf24baae8b06de6418,0xee93a2c15df935d57458,0xb057be49759d160cdec2,0x945d674582bbf26bace8,0xd1608fecc6eb3a2c15bf,0xbf26baee8b057be4975d,0xbba2c13ef9261774582b,0x57be4965dd1609efc9b0,0x61774582bdf24c2ee8b0,0x608fec830bba2c15df93,0x26c2ee8b067be4985dd1,0x2ac13f994e01655833bf,0xf6537559560eb7baf04b,0x9755837b707c02eab055,0xdedc8706baac1bcf83e0,0xc26eab06f3e4b835d560,0xc19fb9061375582bf720,0x538059660af7c92caba4,0x5983adaebc12cb304fe6,0x6cbf04b2cc19ed87e096,0x2cb3065f5d78459660cf,0x5df9361d659823fb2fc2,0x855da60af7c930abb4c1,0x82bef22c2ae9b0577e4d,0x1300baec15ef9261574d,0xbb0577e4d805d760cf7c,0xe84e0975d833db09c12e,0x5d760cf6c8704baec19e,0x3dd29c12ebb067b65382],#[0x8baec15f79161175d83,0x55f656845d760aeec9d,0x35c0705969fb2d422ebb,0x165cfdcc2e0382cbddb9,0xf22ba0e0b2e7b613721c,0x382cb1ff985d070596be,0xf3e0f725c1659becab08,0xc970597b9f07b92e0b2e,0x5eb7c2ee4b82cb9ef84d,0xbc12e0b2ef3e0f825c16,0x2cb9ed74e09705976df0,0xe17835c165cf73a704b8,0x7059779f25c1ae0b2ed7,0xef3a706b82cb9dd74e0d,0x1ae0b2e77dd3835c165c,0xb5ed929d1705976bf2bc,0x2745c165aeec9ce8b82c,0x5969fb2d3a2e0b2e6fe1,0xc9303382cbbe77260670,0xe0b2e7ddd1819c165df2,0xf596606705976eb2ac0c,0x29c165cfacbb03382cba,0x67db31b94e0b2ebb61b7,0x6e5382cb9ed84dca7059,0xb2e7b663729c165cf6c3,0x84dcb705971fb0dba4e0,0xc165aeec9d09b82cb9ed,0xfb2d426e0b2d5f65684d,0x1b92cb7cf93603725969,0xdf964680dc965bb7cab0,0xa0372596edb2b406e4b2,0x65af6ca101b92cb6ed96],#[0x8c06e4b2f73e4d80dc9,0x92cb9ef84603725973db,0xb65280dc965af7ca301b,0x372596bdb2d406e4b2d7,0xaf6ca701b92cb5ed98a0,0x6600057e642845c365,0x2ca09901fe0618132033,0xb0120043e0ff03960cc0,0x618305a615d854614584,0x20e880a1ed87741c3869,0x6d098425508ee226886a,0x48b102b38a8c2970a2c2,0x8ce431f8c182ec8b822d,0xeee3ab0e5837c8d9e349,0xe641b90083ed0f603c78,0xe49e124848191a045790,0x50593c24e0132c4c392d,0x4014d052c949451d9458,0x8958455e156c55395305,0x963858695ea57315c056,0x7225b8168c59b9662595,0xc5f717d05ec97945d91,0x8655991462b985a60f18,0x6901a2267c99d466d999,0xc19ad66ae1a9a69f1a5e,0xa1b8a6db1b606d09b246,0x1c3e70c9c146fd9bd86e,0xce07351cc872f1c7a717,0x827591d4674a1d1c7441,0x77d1dd67729dbe7681d,0x7b31ec07a89e847909e0,0xd71f507cc9f147bd9eea],#[0xd9faa7e79f807dd1f687,0x204c8071ffe7f81fd47e,0xdc83420c482e209a816,0x7e858215484da11883ea,0x880a1f687621ba86721,0x8a4a27489a223888b222,0xcd23168be22da8b3a2b0,0x5a3b88e6a38e8dc23528,0x245a90f2430904a3f48f,0x50e93c24d292d249691e,0x7a95ba55094ca526946a,0xc97fa5f2970a5a496625,0x9ba26b89a2266a98ea61,0xe2a76c9d3a71e9c026f4,0xd2844a0527f69f627ba9,0xa964a4d2916a3528a4a1,0xa4ea8c2a00a6fa9a0a60,0x26abdaad8aaeaa9ca9b2,0xaaf3ab9eae02b62ad12b,0xb17ac40b0d2c16b02abd,0x492d06b3a2ccab2b2c8e,0x62dbab672d7eb582d42b,0xaea4ba1ae56b89adf6b7,0xf46bceaf2ebc42ef2bb0,0xcbfbafbebe82f70bd4a,0xec28b084c19b048c0ab0,0xc4cb102c3db0eac3330a,0x67b192c5d3168c57313e,0x2b1fec7cb1d4c6db1aac,0xb258c933240c8d3216c8,0x2e8cb2b2beca83282c9d,0x9ccdfb360cd0b324cc1b],#[0xed0cb402cf4b3c6ceeb3,0xd27b492d1d3456d12b43,0x5db546d4a34f8d36b4bc,0x635fad7735d0d6cb582d,0xb6aeda43672d953636d8,0x73edc83702dbdb6d8dae,0xcedec3792ddd3756dd2b,0xe14b834e05b7f8dfb37,0xe4f390ce2e389ae23b87,0x8539e4e6d39a8e62b948,0xfbae0ea7ba92e98ba32e,0xbb82ed93b58eca3b0aeb,0xc48f063bfaef73bd0eec,0x44f453ce4f31bca8f1e3,0x2f6dbd98f5ebd6ef543d,0xf963e4cf8bbdfef783dc,0xb5becafafbea0fa0be64,0x2bf6cfcf3f1efc03ee2f,0x4021000bfe4ff1bfa8fe,0x8d020407501a404b00b,0x705f414d05040ff02f4,0x90cb43210bc42d309fc2,0xdd43690d743510d1433,0xef43b10e943990e34381,0x9c48911ac43b102c3c90,0x453d14344dd13444b312,0x5df16bc59115cc567152,0x6f198c65718e461b183c,0x51c146d51adc68719ec6,0x1f747bf1e847831d4c73,0x2d4897222c82520647fb,0xa493924b48fd237c8c12],#[0x4a35285c9e7269498725,0xb312c04ad12b14a95299,0xd32f1cba92e2cb6d2d84,0x93234c6f3144c0f2fc4b,0x33e4ced3384cd53294c9,0x6fcda1360cd53348cd05,0x84e553924e1937a4ddd3,0x248b3ad4ea939e4e6d39,0x1fe2f041c50803fc3e2,0xc54910200ff0f8bc0284,0xd517c00ff141c6f083f,0x7f8bc02d17c3e007c205,0x8ac5f0f83c40f1421e10,0x3e0f103c50d787c1e207,0xe2f058c3f158f121d17c,0x262f8bc0c4d18be2f005,0x8c5f17802f17802f1780,0xd0378bc03e17c5e0c25,0x5fc3e2f00346f08401e,0x80281f840de2f003450c,0xbc5e10bc00df105840bf,0xe13c5e013c5e00bc5e00,0x8bc0151021e2f07845c2,0x2e1007f8bc03787c017,0x78bc01f87c0178bc0106,0xa070ff107e193780393,0x1b87c16216c3e00bc1e2,0x485e1b86c1e2090b8fe,0x34653788241f0fc217f1,0xe006f88483f0c2fe0f10,0x30889e10bf8bc00d154d,0xf1048233788241f8825c],#[0x278825860889e2f01983,0x85fc1e2068be10bf8824,0x34606f8c2fe1f0120623,0x18f005030b83fc3e2f00,0x2f005830c787c1e2068a,0xbf0fc3e2f00be1f005e,0x1ab0f83c42788193f802,0x371782c9c313c1e23206,0x41e0c8c10d02e032788,0x410382839084c4908461,0xf08c2080610402080010,0x20001000000203041a0,0x840c0c0502060c010040,0x406081a0810180a,0xc0d102c0b8c0c106dc21,0x186c8ae27083c50803c4,0x10302050241838238e0c,0x8203040608e20a080818,0x7818207820f040c0e141,0x6040c0800f070c0e1810,0x80818103020f06840,0x4d84c00d0c08001,0x80010302000c26004,0x6078810000003e104,0x4000f8803e00fc5e1,0x60400080010000080,0x6820018100000020000,0x418010006000dc410341,0x108021004c2080000000,0x20f040c0a10107820040,0x800fb10400006040030,0x1078210040220326042c],#[0x20404002820604200840,0x41e0801a070a0e141020,0x824404060c4018802440,0x5040c2820404000001,0x8080b081000ec2098808,0x2f085e20085e1068a040,0x6083c10803c201820000,0x103c108021004200f080,0x1e149408149408109508,0x184a103c1068981e1a10,0x1892a1030b8217078608,0x8184a1018107820f1284,0xc103094287830f040c0,0x801285c20b8217040c08,0xc182128206181030cc30,0x101020210042e0834181,0x40808141078243070808,0x2017842f100420183430,0x40a440a1e0c3c107834,0xe2f0840504000002820f,0x30786083c10291020683,0x808001001e0b0819283c,0x80021010006c2080020,0x10000000080010000000,0x2820404001820000000,0x4040a08141930326040,0xc4010800034081419283,0xc080010000005e10b,0x782e215848f040a080c1,0x81a1064da20800738424,0x41a0d101a20303040a0,0xd040c303860406202c4],#[0x821b04080e1810000682,0x4c40a3c14782003c187,0xc1fe2f0890f040310362,0x20414e27006038ac2106,0x9c40831c0106d1e100e,0xe70b80302c419091e62,0x860808f31048f0407082,0x5e205c0080e105c2e009,0x3e13105e23085e2f08,0x820784c41788c2100010,0x682a60400682a604002,0x4044a080005c1128182,0x61010d82160400000182,0x1010d8217042e0835c61,0x3042c0801b07080e,0x384306388c21b89c2100,0xd12874038601a1000531,0x246a2d0e8060661b0923,0x4060418020080c4c361,0x1063,0xbc401081802008600000,0x1600400d03860405e10,0x400182063ec4123cc41,0x4061310203b082620204,0x103d882000000f082040,0x9c40b11c41029c01784,0x4000f841f082e20418e0,0x100361707f8bc2280050,0x4049d441584103020618,0x5291c0186c1b0821a478,0xc0158832138015238820,0x13848f31040291c21385],#[0x882e1040a081a11405a2,0x20d7138433002600400,0x288341000068152,0xa105861a0b87a1080a08,0x53205643104019013203,0x806431040000006]]
def g223H7 := limbs80 #[#[0x230e030d010000051417,0x210704200b0401110505,0x7f190102029941020505,0x2d5d9405330f08003f42,0xd489400919005e04111f,0x92a104822896649b3600,0xc2ca386a63ac416a908,0x4280955c8b0f665f3940,0xc1044b1422300c8f28c7,0xba68407d83a50c93e437,0x405f0e101e01c650002,0x1a453c2ef231c5767700,0x368a1d0e688db4109008,0xc4e90221000108fc52e,0x81180fd60707978c60f7,0xbac86801b0f8de902659,0xee3a0d80c0ea5711f458,0x1063444d82719a11ee8,0x16d3e482f85ac3300000,0xa4006000d08c0004240,0x248d8fb1e8000c78d94b,0xc96b87750d6126816ca8,0xe884a41d98400085c010,0xabc1ba1f22c23721c8cf,0x1042e045b94125ca27e2,0x89e04c001043ab194f1d,0xd0bc2fe98f15a4c16063,0x21a41c503421de27244b,0xd864a89a13000022f27e,0xd82f786e42813df34c07,0xeac30e2ab26819091471,0x160000000000665f2310],#[0x472000f2600004ed1,0x40259f8003a9265bf060,0x104a0000002116523,0xf0368838000001d2f000,0x50840809a1900e41f6b1,0xcec4f635ec41e5600060,0xcc000033b0002de00]]
set_option maxRecDepth 16000 in
def g223D8 := limbs80 #[#[0xde97254040df17154040,0xf395454040dd97354040,0xeb96458140cf97654040,0xbbb80552409ed82dd540,0x9df835d9509ef825d950,0xde97258250df17158250,0xde5825c460de5825c650,0xf7965540409ef825d760,0xdf5655c440df97654040,0xded655c840df7655c440,0xbef8259440def655c840,0xcfd7659440d7d7559440,0x9ff87594409fd8759440,0xcfd76d9440d7d75d9440,0xd7d865d4409fd87d9440,0x9ff855d840d7e865d440,0xcff855d840cfd855d840,0xbbf8458140ebd6458140,0xfb964581409fd8758140,0xefb6458140fba6458140,0xfbb8458140fb88458140,0xdfb7558140df97558140,0xbf98698140df97598140,0xbef8259540bbd84d8140,0x9fd8759540d7d7559540,0xbf980d95409ff8759540,0x9ff865d5409fd87d9540,0xdfb805d9409fd86dd540,0x9ff855d9409ff805d940,0xfb965d02409fd85dd940,0xfb95458240fbb65d0240,0xef96458240fba5458240],#[0xdf97558240efb6458240,0xd7d7555240dfb8758240,0xf3d65552409fd8755240,0xdbd7695240dbd7655240,0xcfd7659240bfb8059240,0xcfd76d9240bf980d9240,0xd7d7559640bef8259640,0x9ff87596409fd8759640,0x9fd87d9640bf980d9640,0xb7f85581509ff855da40,0xef96458150f795458150,0xdfb7458150efb6458150,0xf7b8558150f796558150,0xf796598150f795498150,0xb7d85d8150bf98698150,0xd7d76551509fd87d8150,0xbf98019150d7f7655150,0xbed8219150bf58119150,0xb7d8519150bdd8319150,0xbfb80591509fd8719150,0xebf64991509ff8759150,0x9fd8799150b7d8599150,0xb7d85d9150bf980d9150,0xbf9809d1509fd87d9150,0xbdd839d150bed829d150,0x9fd86dd150d7d65dd150,0xf7b8059550f788059550,0xb7f8459550f6f8259550,0xbef825d950bfb805d950,0xdfb805d950bdf835d950,0xdef825d9509ff805d950,0x9ff845d950ddf835d950],#[0xbf9809d950d7f855d950,0xef964582509fd84dd950,0xdf97458250efb6458250,0xdf5645c650dfb8758250,0xdf5865c650df7645c650,0xded645ca50df6865c650,0xbfb8059250def645ca50,0xcfd7659250dbd7459250,0x9ff87592509fd8759250,0xcfd76d9250bf980d9250,0x9ff845da509fd87d9250,0xdbd855d060df5855c460,0xbfb8059160d7d845d460,0xefb8059160ef88059160,0xdbf7499160bf98099160,0xbf5811d160afd8699160,0xbdd831d160bed821d160,0xb7d851d160dbd741d160,0x9fd85dd160dbf749d160,0xbef8259560bfb8059560,0xbef825d560d7f7559560,0x9fd84dd560bdf835d560,0xbef8259660bfb8059660,0x9ff855da60d7d7559660,0xdef825d7609ff855d360,0xdf9701c1659ff845d760,0xdef725c165def721c165,0xbdf835c165bef825c165,0xbf5819c165dfb709c165,0xbed829c165def729c165,0xdef72dc165afd869c165,0xdec80dc9659fd84dc165],#[0xdee80dc965ded80dc965,0x9ff845c365def80dc965,0xdfd7659440fef8259440,0xdfd855d840dfd8759440,0xfbd6454140ff96054140,0xdfd7654140f7d6554140,0xfbd6458140bfd8654140,0xbff8558140dfd7558140,0xff98458140dfd7658140,0xff96558140ffb8458140,0xff98558140ff97558140,0xff96598140ffb8558140,0xbfd85d8140dfd75d8140,0xfef8259540bff8059540,0xdfd7659540f7d7559540,0xdfd8759540dff7659540,0xdfe8759540bfd8759540,0xbfd80d9540bff8759540,0xdfd765d540bfd87d9540,0xbff865d540dfe765d540,0xdfd865d540dfc865d540,0xdff865d540dfe865d540,0xbff855d940ffb805d940,0xdfd855d940dff805d940,0xbfd859d940dff855d940,0xff96458240ff95458240,0xff96558240ff98458240,0xfbd6455240ff98558240,0xf7d6555240fbf6455240,0xbfd8655240dfd7655240,0xfbe8655240fbd8655240,0xbff8559240dfd7559240],#[0xdfd75d9240dfd7659240,0xdfd655d240bfd85d9240,0xfef8259640dff655d240,0xdfd7659640bff8459640,0xbfd84d9640dfd8759640,0xdfd855da40dfd845da40,0xefd6458150f7d5458150,0xbff8458150eff6458150,0xff96458150f7d6558150,0xff97458150ffa6458150,0xff88458150ffa7458150,0xffa8458150ff98458150,0xff96498150ffb8458150,0xefd64d8150f7d54d8150,0xf7d8055150bfd84d8150,0xf7e7655150f7d7655150,0xff88059150bfd8719150,0xbff8059150ffb8059150,0xfbe7459150fbd7459150,0xf7d6559150dff7459150,0xdfd7659150f7d8559150,0xdfd8759150dff7659150,0xdfe8759150bfd8759150,0xfbd7499150bff8759150,0xdfd7699150f7d6599150,0xbfd8699150dff7699150,0xbfd80d9150bfd8799150,0xbfd87d9150dff74d9150,0xdfd765d150f7d655d150,0xbff865d150dfe765d150,0xdfd769d150f7d659d150,0xf7d8059550bfd869d150],#[0xf7c8459550f7f8059550,0xf7e8459550f7d8459550,0xffb805d950f7f8459550,0xfdf835d950fef825d950,0xf7f855d950bff845d950,0xdfc845d950dff805d950,0xdfe845d950dfd845d950,0xbfd849d950dff845d950,0xff98458250ff96458250,0xdfd7659250ffb8059250,0xdfd845da50dfd8759250,0xefd6559160bff8059160,0xefd8059160dff7559160,0xefd7559160eff8059160,0xefc8759160eff7559160,0xbfd8599160dff7599160,0xefd75d9160efd74d9160,0xbfd851d160dfd751d160,0xdfd755d160ffb805d160,0xbff855d160dff755d160,0xdff759d160dfd759d160,0xdfd75dd160bfd859d160,0xdfd65dd160bfd85dd160,0xbff8059560dfd85dd160,0xbff8459560fef8259560,0xfef825d560ffb805d560,0xbff845d560fdf835d560,0xdfd84dd560bfd84dd560,0xdfd655d260dfe84dd560,0xbff8459660fef8259660,0xdfd855da60dfd8759660,0xdfd855d360dfd805d360],#[0xdfd845d760dfd805d760,0xdfd741c165dfe845d760,0xfef725c165bfd841c165,0xfdf835c165fef825c165,0xdfe745c165dfd745c165,0xbff845c165dff745c165,0xfef729c165f7f855c165,0xbfd849c165dff749c165,0xbfd84dc165bfd869c165,0xdfe84dc165dfd84dc165,0xfee80dc965fed80dc965,0xdfe845c365dfd845c365,0xf00b0010401500130000,0x7d00df018002a404b006,0x5c40ab0143026004540,0x303f007640df01a30318,0x55028704d80934119021,0xcc418b02fb05c00b141,0x307680e841c3036b0698,0x2d0447085810441fb03d,0x138426304af092811f42,0xb0ab814f4297051f0a00,0xfd05db0b8016b42cb057,0x1a34337064f0c6018442,0xf0e201be436f06c30d58,0xdf079f0f101db43a7072,0x20f441108070fd01f543,0x711782294445086f10a8,0xb9095b1278248447f08d,0x28144f309cb135826344,0xf151029b45290a371440,0x910b0315e02b5455d0a9],#[0x2ed45c90b7316a82ce45,0xb186030645fd0be31798,0x670caf193031f46310c4,0x35146970d131a0033a46,0x71b9836b46cb0d771ac0,0x310e4b1c6838747010de,0x3b847630eaf1d2839e47,0xf1ed03d347990f171df8,0x10fe71f983ec47cd0f7,0x42248351053207840848,0x72200439486710b72140,0xd3118b22e0454489d111,0x48a490911f323c047048,0xb25404a14939125b2488,0x9f131f26184bc496d12b,0x4f049d3139326e84d649,0x728a050e4a0f13ff27c0,0x5914a329305224a3b146,0x53f4a7714e329985304a,0x72a8854e4a95151f2a20,0xd315972b1055f4ab9155,0x57a4aef15cf2b7856c4a,0x72c585884b0f16132c00,0x49167f2cc05934b21163,0x5b24b5f16b32d585a64b,0x72e105bf4b7716e32db8,0xa9174b2e805cc4b91171,0x5e94bcb178b2ef05d84b,0x32fe85f94be917c32f68,0x29184730606084c09180,0x6274c49188330e86184c,0x731e06374c6718bb3160],#[0xb5195b329064e4c93190,0x66b4ccb198b330065d4c,0xf33d86784ce919c33370,0x211a2f34406854d0319f,0x6a14d411a7734c86944d,0x335b06b24d5d1aa33528,0x9d1b2336206bf4d771ae,0x6e34dc11b6736a86d14d,0xb37d86f64ddf1bab3740,0x271c3f38687084e071bf,0x72c4e4d1c8b38f07194e,0x739d87374e691ccb3978,0xa31d373a487444e811cf,0x7644ec31d773ad07554e,0xb3bd87784edd1dab3b38,0x1d1e333c407854f071df,0x7a74f451e733cb87914f,0xb3df07b84f651ebb3d58,0xa51f3b3e687ca4f8d1f0,0x7e84fc91f7b3ec87d64f,0xb40187fd4ff31fd33f70,0x43206b40a08105017201,0x839506b20c7416082750,0x74268849508d210741e8,0x787883d24485850ab214,0x1780203c50745e0e20f1,0x3883c510e1e2e00f1785,0x606e30de1e2e02785178,0xe010168f8b804c405042,0x83311870f8b807e144e2,0x4b88662c3a68fe1e01a9,0xdc3e0e20719805f0f84],#[0x2e28611104b0f8844417,0xe20f1833121b8b828c61,0xb851783883c51bc5e1e0,0x8e259866684e2e163891,0x6685e2e063871e138789,0x3c41e178b818e1d9861a,0x8b83843c60c86c5e2e0a,0x1745e2e044e1a31c1917,0xe1a3205d178b83843c6,0x8b803e9861aa64544e2e,0xc645e1e2e0a317191787,0x2e0e10f1917878b828c5,0x1a17843f8b819866685e,0xb83858c785e163e2e017,0x5e1e2e06317185e16138,0xe00d138c9b878b803468,0x605c0c37878b80717e2,0x3460504e3e10de2e0262,0x26e0e20d1813841b8388,0x71013878037885c617e1,0x3f84341b838880de0e21,0x346e117e0e20d158c40,0x117e0e20d143c1b878b8,0xe2e01c63849b8388346e,0x43c1b8b8070c86c5c4a3,0x8b806c3e1e2e00c34438,0xb807a3e10517e0e2261f,0x10fe2e018605c9b868f8,0xe2128f878b80345a310e,0xd100f878388606180de0,0x8034518170de1e2e0631,0x8584e2e063e11d8f878b],#[0x41e16118f878b8198766,0x811610745e11063e2e08,0xe1e2e045841c618f878b,0x20f1b845f8b803451817,0x878063885c6e18517e0e,0xb80347e1e20fe0101413,0x2e110e0c41c401a8f878,0x1443868f8b811071b03e,0x388605e1a344e2e0851a,0x8e117e244e0851f85138,0xe2e00d13878a17805c51,0xf18321b168f8b8310717,0x87803f886c506e1e0e20,0x5c60544e0e21b145c17,0x126e0e2441817868f8b8,0x1714158f878b805c6a3e,0xf844383883c6e10fe0e2,0x4182625e10fc3e0e2245,0x185c3f0f843783889888,0xf8388987e11725e2e00f,0x6e10fe0e21716950f843,0xe0e20f1c43843f8b8034,0x7849b83883c7a50326e1,0x8872643e1e0e20f185c9,0x5e0e2185f0c143f8387,0xd18438783883c517e10f,0x849b88a4603e1e026e20,0x5c4c3e026e22a1b130f,0x1e026e20d1b0f8780985,0xc31843849b838834610e,0xf87838860444e125e0e2,0x80345c4c3e1e02625e21],#[0x1006e1e2e00d1b84438b,0x2261c5c13870f8388987,0x9b8387888e1a504e01be,0xe1e0e20f0d145c6c170c,0x1e08f14145b8388aa3c5,0x16940c638b87803c718e,0x43f8b806c605e1e0e20f,0x88686650fe0e21b14359,0xe1830de2e01a1987823f,0xe28f1c97803f886c565,0x8a9b87823c615c361a6e,0x3886c4e10fe0e21b170d,0x8458fc31b61e0e218178,0xc30fe21be01b0e3d8b83,0xe20f1c3f87805f88501,0x178783883c5172625e1e,0x5c618c317e1e2e00d1c,0x117e0e20d1b0f84378b8,0x121413870f83885c6c3e,0x70f87899848566c3e1e2,0xf884998566e1c3e2121,0xd9866665c3e2e0871b87,0x3e1e0e20d170c378b821,0xe00d1b841b0f8b803460,0xf0f878b8034617c3e1e2,0x805c644e1c3e0e218185,0xe1c3e2e00d18370f878b,0x2e017189b878b8034526,0x198f878a184850d03e1e,0xb8b8034663e1e286e00d,0x71744e1e0e218183f861,0xe218181b8c5f878b8060],#[0x7845f83883450644e1e0,0x878b80347e125e2e0171,0xc5e3e1e2291714605c1b,0x3e1e01714178f8388a85,0xe0e2171863878b80345e,0x22384978b805c563e125,0x886c51b170f6305e1e0e,0xc54786a3e0e21c5d1383,0xe2186c8f8b83845c616,0x1a3f868f80661c416a3e,0xc4180d17e1e2e0a31d8b,0x586a3e2e0c41d1383886,0xe217186f8783883c516c,0x413878b806050563e1e0,0xf8b806c4a301e0e21a1,0xb80686170fe1e0e21b18,0x5c3271ae0e21e1a96938,0xc3e11a90878b806c58fa,0x11f8b80906c4c68f62e0,0x8b829060dc62460e2c3e,0xd2127e2e01b186a970f,0x21a106c5c9387830f887,0x1f0c04438b806c6a5e0e,0x13f887466564e2e0c316,0x321e2e0641f0d9432878,0x1595938b830c5860c65c,0x3088700685c3e1e2e017,0xc6c5f843c4a117a30f1,0x3450f0d0c3c34261170f,0x888414518030b14343c,0x8610401a1032684086e1,0x3170d08605c3430d8463],#[0x3c98344611b08105d14,0x8c5c21b0f86626145184,0xd211b0e1018403611b09,0x8403c344211a086c1420,0x40e116868c20da1030c9,0xbe1086c88848041b0d42,0x2262308605c205170801,0x3c34706a3100f101a8c,0x10662616010401989858,0x6630834110060f0d1018,0x98c162616063105c3420,0x430526098c4114321630,0xc3d89843611b085c603,0x14403100510402464410,0x1104048583212004145e,0x40c62143c3441009858,0x406850f0c61109838685,0xc3430d611b0c1086146c,0xd146c103c4211a0c198,0x8086c5d083f845a117a3,0x1762610f10605c343041,0x3e102450f840c5c403c3,0x526101a1021745260f10,0x26100f103c9894318c32,0xf171c958984983c50d,0xc6218370c4262562616,0xf250c9894105c48625c3,0x8603c2450f08403c2180,0xf085d8984943c5100f0,0x970c30f25c30c4034225,0xf044098343c444c30810,0x40603180f083c189430],#[0x10983c14342410f05111,0x3086088848040f424140,0x43c9a9430f0d100c00f4,0xc983c1432642410f051,0x3c30317084034218250f,0x4983c41b222117101894,0x189420f6261262514403,0x51a8a84983c4100d260c,0xf106098226a262a1610,0xf260d65120d10262611b,0xd441060421981138460,0xbe2e10f1113846c36261,0xa622e18f1388846e3c41,0x3f8b845e2e10f0c5c942,0x38b8440543e2e1106c5c,0x150f8b84505e2e10c158,0x20d0460949831825085c,0xd085c3420544170c9510,0x84612544105e15103170,0x1031718440c41118c5c4,0x98c5c32562610f101861,0xf1009105c24418170c1,0x868091b62610c605c343,0x63170a1816108e898a85,0x4016261252310605c343,0x263041589858c4186308,0xc5c5102562611714158c,0x41025846117146c88843,0x46831783440c5d89858c,0x3f886f8451b0da30f108,0xb868c41b8fe221a3145c,0x8605e8c31b0f250e3c8],#[0x846830d61100c5c10517,0x45d088f846c5231b0a8c,0x145c603431b176261631,0xc3d8b868c61b18616063,0x8b846c36018e11b106c5,0x384946c31b8683616015,0xf886e3d8448fa21a271,0xa8a85858094906228fe1,0xe8a845a262a16105241,0xf8b84517e12425106c35,0x6e8680361a01a0c6c5c3,0xb130f846d184e10d250c,0x62611b0c146c218e1251,0x5c2601aa10d8a853c684,0x170460]]
set_option maxRecDepth 16000 in
def g223H8 := limbs80 #[#[0x8104000008001001c780,0x14b812000209060038b0,0x42070000082022800604,0x28008282900000086041,0xe0034286001c2010e04,0xe0200e92041c08f0c0c0,0x144820200104022848,0x46011624001023c105,0xc010003c00100103850,0x448d0224080003c08d02,0x883c2010a2014382062,0xd1e080220a096050e04,0x91214115245010d060cd,0x162010a160c21110bc00,0xb0029300454043a4c386,0x47d40000404143030,0x1cea00000002c0500000,0xe24a9800082d870d4000,0x3c600000004102b1f622,0xf1ef60a80001079a,0xa101d99460000b3afc4a,0xb287be84380000001f2,0x31e60000000000040036,0xbc000681f9bae0000000,0xc5900000000220822,0xeb00000001e9400000,0xed2b9000000000001689,0x1afc5140000000d9db41,0x80000000000000070ff9,0x55430000c2e44ef,0x9ed06600000000000000,0x43c8a4880005823b],#[0x8de198000a3f00001cf7,0x3314c9579f6000133,0x90320000a7dd0e8e8770,0x8057000000000003497,0xa544000746a000106,0x98ca6393081588949ce0,0x1cca541f92b2490,0xadf35b6a2b8000c91600,0x9c8f15200000000000c,0x488cf68981327c150d0f,0x22800006473000146,0xb8fe7801070b86780000,0x5b0be40e342a1419fc65,0x10ba7a0000000049d264,0xd6a54060003ca51024a,0xc6d0a7c6ba42f60a4000,0x37200018fa6866000180,0x18c0b,0x91882b920a135e74c00b,0x31525d7ab829ed32eed3,0xe433c0e3c047,0x24300000b34fe4f2621,0x239a8a482280f4000000,0x71bc18ee00034e000000,0xb3f053911b41c0000000,0x1d306fb80b8000f88813,0xb167000062b1c4f1d4d0,0xb306490882142000289b,0x26a000301d58bd000008,0xde060435110c00031a97,0xbfd0161191954d0d1815,0x174cee4139527d16],#[0x54dbc1a7c7a480110700,0x3a8ef01a000000000000,0x8d20003058300c0001d8,0x800000000776c58c1b86,0x8b8acc130000000008c6,0x702ac668000000023,0x74990,0x1409b20a92ba24a0000,0x252e29000000bf000000,0x64bc8bfa00030739179d,0x20e8000a0000000,0x2c6a3c00000000000000,0x19913e604c90a698ddd,0x190f0000000010657230,0x1ca94d5a20f04ac12141,0xfc6d13e2784400058dbe,0x6ed179c08000003130df,0x45c00024b8645151e474,0x8000c35701fec2d00003,0x1046800081450522cd1,0x4460000000400b81a400,0xe18c000000004da091f1,0x8006b48390000d30f044,0x8c60002d1578c28439e8,0x60c50000000224e381d7,0x305549e538c994958b0,0x269c84c50d8000000000,0xba12b947472ec1be99de,0xd08e78000512a000084d,0x10239d0cae702,0x58190000000146800000,0x2c03f00d525681a8896],#[0x1528a0cd2910603000,0x34cb0001c356d1080000,0x7147ee47584160000000,0x97000000000833000134,0x13b2a5bc83980003,0xc88508c7ba8578a8000,0x3500c0d4000123,0xd209144f06b349380000,0x218e9301eb0f8c1e349f,0x386289800064f2d3f241,0x8d2d50d668a2c1e50094,0xf8e710000404a0001106,0x2e885684430876000080,0x6c670001f1400004c6c1,0xbe0179882a3024244000,0xc456ab47527b2ed86,0x80000000000104f80000,0x3c52ac05c432f28180d,0x24d521fc347880000000,0x4ad7a4da4700d676,0x300e00000000000,0x4c00000000000000000,0x5cabb43f53d2caf0000e,0xc800078969099a426e93,0xe5c0418c4a97a522f07,0x8000f2f6f2e7c8c00f8b,0x1901e2a4000244b,0x837b0720000000000,0x8b543f4000000000000,0x338ce003d000181a4000,0xce3380002984f3d954,0x9a300000a14c0e6d97e2],#[0x18000456e000051624eb,0x40c46c4000f1560000c6,0x1d59b112a9579,0x9369744a16a5f93c4000,0x283d78bb835588,0x494cc36a000000000000,0x323ce9060000000142f,0x1da0000000614be12600,0x38ef5976c3e9436d02df,0x2a42b1e20001b5c4000,0x1edc4780453847000000,0x858000083d40000000d,0xb199b194000,0x8000000000000732c00,0x19240070e29b4409c720,0xd8089c96a934843c427,0x1f9859800000000001e6,0x588bfb6067154fd80ead,0xf10c3fc590000542c000,0x9a6000007cc95f916f47,0x8000934d26a0000713ae,0xbcc38c02c000000034d9,0x82ee76c00058b3000121,0x5cc932d000000000000e,0x9447080000000a057ea2,0xc1fc12543e8000042d21,0x4931abfc00010b70000d,0xc94a071140001e6dc000,0x99aa55309699a2000170,0x5050b0850762d03819f5,0x10ceb74ceaad90888000,0x8a9837d4f56db521d920],#[0x4d69a,0x3079ad0df28e506c000,0x84cec2fc908000000,0x15a0002c2e4a110,0x11650001f225e52,0x241028ab625c00,0x0,0xfb0a100000000c39b4dd,0x30a44e30d719c7a087c1,0x81e1d0c9a52543180009,0x5301fe8bcf0d8000010e,0x36525c400000740001e0,0x800000010504d0604a92,0x564175c7159840003413,0x285f10a74235e1,0x304f1383c5a80006cc40,0x2c00009e7a2dae304000,0x3ccb8000441086,0x49804226f3300002a2d0,0x11ca00000000000,0xafc8af81b4191c1b800,0xa975440e8b9f1232,0x328640000806a0000ce6,0xace5c80000000892262,0x997da2d6641c8f5fd9a8,0x3e0209083eb2b24374bf,0x21c000000000006034a2,0x80006277a56263b00000,0xc14041092e97a016d0ad,0xa54265695e14363e080,0x90b210c5305b800415c8,0x3cbc4407d9ce00020d0],#[0x4513540001144000000,0xcce8f174803c0004061d,0x1c8df0840001c1d7c25,0x1a200020fe8000000000,0x98e123b06b5cc420f1a,0x8a8def529b18ce5a4c54,0x376f027880121543ff65,0x69909138000000078122,0x664ca0000e2aa853d46d,0x1266fc146851527ac3,0x11feba22000000071610,0x418e2304400000000000,0x29d042ccd20000491454,0x8000000000030ed11253,0xb8000089d598000030c7,0xc75182680000000c3,0x108e338c084101a00000,0xdbd0065b2000181b9e63,0x236000000000001c2,0xc1b00001475400000000,0x20d2cc610a4846db010,0xb169c518000000000,0x310c00000]]
set_option maxRecDepth 16000 in
def g223D9 := limbs80 #[#[0xd75102f6b90817d5c440,0x4813f9d8409faec2057,0x60bdae5285f571943dda,0x5dd73182f6b90c17d5c4,0xeba8c16f9d060b7ae830,0x4040bdee4b2efb60982b,0xa05fd76102feba881fe5,0x2febaa81fe98140ff2c0,0xfdd940bfaeca05ff7550,0xa9207bd54903fcb04817,0x902febac817f5d240f7c,0x1fe98150ff2c0a85fd76,0xfacaa85ff74543beaa2a,0x60942ffbb2a17f5d950e,0xc17f5da50bfae9287f9,0xdfac8b05fd75182feba,0xff75582ffba2c1bfd916,0xbb4c17f5d660bfae9305,0x165bfaebb05fd74d82fe,0x5fd70d97f7b92cb7fdc,0xfea8281ffd9440ffaca2,0x59540ffec0a07fd60503,0xca07fd75503ffb2a81ff,0x3feaa481ff9d940ffae,0xff59640ffec9207fd649,0xec0a87fd60543ffb2c81,0x4543feb22a1ff19150ff,0xa1ff5d150ffec8a87fe6,0xffceca87fd76543ff3a2,0xd64583ffb24a1ff59250,0xa2c1ff1d160ffcc8b07f,0x60ffee8b07fe74583feb],#[0x7ff75583febaac1ff595,0xeb82cbff1c165ffacb30,0x2000ffee0b2ffe70597f,0xd84481c40b2041014805,0xb622b0fa071032816409,0xc10d2c6362eb1648a484,0x97c48e22f10b87e03c01,0x2fd170cb2656329993f0,0x4eb27223759ad0cec63f,0xc447217905c7f73e39e2,0x753be9af4bfa5052068c,0x755982be5592a9252a28,0x389948c5f6142fa9758b,0xe4870536f9b00d506903,0x3ef1ee0f397813af5d0c,0x311486ec29a0df0387fd,0xa4a764cd2218ee46262b,0xc941f9ed4e8e6cb31296,0x8b8f084c4245a73d28a8,0x78509871601b185c5803,0xd871601b1e10b8b00418,0x92171850987160182840,0x4861b0f1600e284878b0,0xb8c362c01c6098f106c2,0x4c58071b8f086c02061,0x38608170e2c030dc7843,0x9871601c78d0984362c0,0x621e346878b008371860,0x3860b871601e303c3170,0x23706220be3c21716008,0xc69b0e2c03460c131a6c,0xd1868646407e1c5808],#[0x93631b8716018323c38b,0xc21316021363c38b00d1,0x521851e2c11070d8cbc5,0x71601a3230b871608830,0x83868b871601e306c78,0xfc38314324bc5c787062,0xa54d870621e386089530,0x3c71a14261203f160206,0xc3f0e0c438606970e2c0,0x8c153431f830e21c3034,0x184c38311015361c1887,0x8386c30f1601a3174c36,0xd8b00d18b8d87870620,0x160206e10d8b00f1b1e1,0xb08dc58070a103631b87,0x103631b871602e417c61,0x1a3060814be1c189190,0xd8d870621e346c78716,0x8030e5c2631a1b0e0c44,0xd851e0c46c8318c6e1c5,0xc15261878311b1c2c40,0x1e1c18830f190c3c580d,0xc3268b8b061471090a5e,0x1e3488b87160469a20e6,0x6c38310d223268b87062,0xc347870624c3472e131a,0x988369a2c41a8f0e2c04,0x38b00d222c41a8f0e2c0,0x4d8f0e2c0346469880fc,0x16088408c7871604c346,0xc361c4170442a3260b87,0x8f0e20b8134420c434c8],#[0x61cda68b8b0614710886,0x61c188793170a3c58222,0x2e1c18930f1cbc54a113,0x10ca1f0f0a6c18868f15,0xc43480a622261e970e2c,0x18783126207a64b0f0e0,0x8d4c430e0c43c7883d2e,0x8710f1cc26c38310f1a3,0x970e0c49878f0d2a6c1,0x8c603054d0f161c03493,0x261c5803170f161c0986,0xb0e0c43490a5cc44c694,0x8f0a5c580b925d1c3081,0xe5e363c2370621f18608,0xe2c05c82f1b1e1c18868,0x344c5830a32c325098f0,0x87e047871105c21b8a94,0x24325c28f0622e3974b1,0x3649b8a94362c1851c4,0xe0c58481a19283c29316,0x343c5830a426325370c7,0x9283c2931603641b4a36,0x1]]
set_option maxRecDepth 16000 in
def g223H9 := limbs80 #[#[0x22000500080820010007,0x25288064850318904800,0xc000c1051440041ae02,0x908066c5021a40035062,0xe4e00c9816082008a98,0xc00902ac30904000,0x160861a1a380823c0058,0xa1430c0204705020c603,0x1c01d5433834060059a1,0x30a3c74b8718033073e,0x2d6c1421d6858505000,0x22e4cb815c0c0c4143c,0xc66ebae2b6000424cb65,0x78541e80236c48f1660b,0x102ec86c0000000a8918,0xeab0001e480ccd48d316,0x11ca9a79392a06c88ccf,0x326fc7e7affc6990623,0xe13a00000004b7a9b529,0xef40000001a80800133b,0x5c346a2efc771a2ba79d,0x3a1bf582253000000072,0x28cb48e9b270c3204,0x89f90000062abe07602e,0xcc00018d311bb3521724,0xb83e861d9380007132c7,0xc55817d817c7aaa7df7b,0x99780000006b289d86a5,0x56042e3d253ab0ec86f1,0x263000042f9eb90854a5,0xc18e876be800189ea8ab,0x7d2d641a486400000012],#[0x5dd91311a7600069cfc4,0x9806b566b4907895e24a,0x13229d0b761496e2a4c7,0x7e5c218fd0900012bcc0,0x76480010c5f26cc64995,0x240000b82dcc7a222034,0x6221e4afd2cba054c942,0x36beb35800182,0xac38acf97952a7c45280,0x60cec5889298386500,0x7c2800169900,0x6a05a52c0980000162cc,0x7286e5d699a8418001,0x90000208eb01e9a00000,0x143b800012fa196a2,0x5f00000001ea60000000,0xd1968ba8aa0ed0ea5ac7,0xc0006275f37787f812f2,0x483a0b80000001d08760,0x7364d4e000710f,0x90123845fd7f43180000,0xa27ecbd99e59988001cb,0x7280000000a0df8b4e5f,0x84f349d2408580000001,0x400029ff55a670766825,0xc16e2f96b1301e00064b,0x2650ad5772adca998001,0x997d426e9d1a98dd5ab,0xfc5768f99269bd90ecba,0x246792f81472f5b24,0x32d800040fb2960,0xc81cbd38a8dfa04c4480],#[0x3293490f04d2aedea,0x290ac10527200028fc,0x204e0000001a18288a0,0x44ca26c89500001c0e00,0x83dcabf5a7c40fde42b0,0xdb9c5423327580004437,0x4f7d80006704831d1eac,0x4927e440ae000125df9f,0xb6800174d865600049c6,0xe58920000001a06109f8,0x5a1de77c0676450000c8,0xf1bc7640ffe115da165a,0x258217ea4d79c19443c8,0x16b26d7a081fb146733b,0xa88327801c7829e21a08,0x2b11451e5a9471700a,0xc908000191186ea0b00,0x7869d6b40918f8e2,0x21e3231040000000a91,0x3cec285ae10200000000,0x672692c00078f40004a,0x6c7c2cbc486fadc66,0x6be2fc09588cd859919e,0x1ccc966ad804897eaa86,0x599c00030d01944953a1,0x530db2a00058c4c55,0x40a041ebdc60000,0x5c37b159cb3062340680,0x51c241f50e22bb50e,0x918001c3730b34624c6e,0xf00008a9000056000003,0x86a1e5889be0002a4f07],#[0x161ab1654150001f7e,0x311a2731967b00000000,0x80004d9901d48760000a,0x521,0x9ad80f82f58d558151ca,0x19ee599ef2a6,0x7ab076d3652365c8a800,0x5332629a29c56812b767,0x82a9690d80b88001e7ed,0x8a6461bda5259a4584b2,0x3a12884009794d100,0x3b42e1500ba6058caa9c,0x3f45bb7e59b75c76af1f,0x516c8398643d1,0x48bc4f2c0518d8a2c3a1,0x5d11f993527de471e748,0xe0002271cca0001c2364,0x1c5efa8c0a5396,0x1668b63f44fd618,0x728dbc239a0d8788df20,0xca08a4712d2e2ba943cc,0xa0bead7251a28a712488,0x256032a2e2af5dfea76d,0x20a88001a30daa64b389,0xc4de28ed2478f7c6e1b1,0xc080006ba429f40b4ac7,0x5c6e052ad0064c209e1e,0xcb9e048e35b9d5c1,0x167a0c4c908b31a35d,0x8946c0000e617a855340,0x7834d32d4c13a478254a,0xc33b8e18c87a91451329],#[0x9a800140ab96ac3a0000,0x7659a0001b1ee52f85c7,0x1e3041f0e5]]
def g223D10 := limbs80 #[#[0x50ff543fe40ff503fc40,0xff60ff983fd60ff183fe,0x89c1b036003ff65ff597,0x108829da6a9745110834,0x233618a02060e31618a0,0x8881858e18a01071851,0x3438a18042061443c386,0x873450e31a18a0109185,0x68e18a01081631848608,0x8211c51238608861c534,0x51038628061c51060e2]]
def g223H10 := limbs80 #[#[0x904368004024275a810,0x1ce0984002a44048e6a,0xd88dee5c0000001a3547,0xbdf000d27e1393a4,0x3572f3385b40ba00000,0xd3000a19f26cac12e511,0xa0f8bb539f360001c84,0x24d556c4215,0x43712000000e1b000093,0x7000cb6a4c602d209514,0x455a5f000000653b23b0,0x916fc92c273b,0x40000000000000000000,0x30600043400080,0x59203d2a000000000000,0xa00040a00053db3cf5b1,0x5d019adc190174451c14,0x145032990433,0xb3e000000d1872d3520,0xa0eccb55a846fc3a1500,0xe14e0d41d940c4e,0xa54000000b21bdd0000,0xc1f000f22a5e3c400000,0xdc0007db20ca4fdc5000,0xb5a4025e496100000007,0x62c00000064be29508e2,0xfcaf172d1000000,0xfe58e48741530bb939b0,0x294f2828025d00003,0xc24e0bc1eb57831,0x837e0510971a0]]
def g223D11 (j : Nat) := if j=0 then 0x3088027f else 0
def g223H11 := limbs80 #[#[0xcc0000000,0xa0000050,0x2b000,0x48000c000054c0000000,0xd78,0xe7002d4004500680000,0x9a00388e340f480,0x8100]]
def g223L : Nat → Packing
  | 5 => (10,6,5,0,0,6,0,g223D5)
  | 6 => (147,5,5,0,0,11,0,g223D6)
  | 7 => (561,4,5,0,0,14,0,g223D7)
  | 8 => (408,3,5,0,0,15,0,g223D8)
  | 9 => (96,2,5,0,0,13,0,g223D9)
  | 10 => (11,1,5,0,0,10,0,g223D10)
  | 11 => (1,0,5,0,0,0,0,g223D11)
  | _ => emptyPacking
def g223I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 2 29 2 9 4 1 g223H6
  | 7 => lookupWord 46 211 8 13 8 1 g223H7
  | 8 => lookupWord 177 1061 7 15 10 1 g223H8
  | 9 => lookupWord 137 677 7 14 9 1 g223H9
  | 10 => lookupWord 32 191 5 12 7 1 g223H10
  | 11 => lookupWord 4 67 0 9 4 1 g223H11
  | _ => fun _ => none
def g223 : Forest := ⟨223,11,fun i => g223Y[i]?.getD (0,0),g223C,g223A,g223L,g223I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P5_0 : block g223 5 0 10=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g223B5 : block g223 5 0 10=true := g223P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P6_0 : block g223 6 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P6_2 : block g223 6 2 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P6_98 : block g223 6 98 49=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g223B6 : block g223 6 0 147=true := (@block_merge g223 6 0 2 145 g223P6_0 (@block_merge g223 6 2 96 49 g223P6_2 g223P6_98))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P7_0 : block g223 7 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P7_3 : block g223 7 3 62=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P7_65 : block g223 7 65 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P7_161 : block g223 7 161 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P7_257 : block g223 7 257 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P7_353 : block g223 7 353 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P7_449 : block g223 7 449 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P7_545 : block g223 7 545 16=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g223B7 : block g223 7 0 561=true := (@block_merge g223 7 0 257 304 (@block_merge g223 7 0 65 192 (@block_merge g223 7 0 3 62 g223P7_0 g223P7_3) (@block_merge g223 7 65 96 96 g223P7_65 g223P7_161)) (@block_merge g223 7 257 192 112 (@block_merge g223 7 257 96 96 g223P7_257 g223P7_353) (@block_merge g223 7 449 96 16 g223P7_449 g223P7_545)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P8_0 : block g223 8 0 15=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P8_15 : block g223 8 15 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P8_111 : block g223 8 111 85=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P8_196 : block g223 8 196 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P8_292 : block g223 8 292 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P8_388 : block g223 8 388 20=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g223B8 : block g223 8 0 408=true := (@block_merge g223 8 0 196 212 (@block_merge g223 8 0 15 181 g223P8_0 (@block_merge g223 8 15 96 85 g223P8_15 g223P8_111)) (@block_merge g223 8 196 96 116 g223P8_196 (@block_merge g223 8 292 96 20 g223P8_292 g223P8_388)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P9_0 : block g223 9 0 16=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P9_16 : block g223 9 16 39=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P9_55 : block g223 9 55 41=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g223B9 : block g223 9 0 96=true := (@block_merge g223 9 0 16 80 g223P9_0 (@block_merge g223 9 16 39 41 g223P9_16 g223P9_55))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P10_0 : block g223 10 0 11=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g223B10 : block g223 10 0 11=true := g223P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P11_0 : block g223 11 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g223B11 : block g223 11 0 1=true := g223P11_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223T : checkedTables g223 11 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g223 0 0 0 = true)
  · exact (rfl : block g223 1 0 0 = true)
  · exact (rfl : block g223 2 0 0 = true)
  · exact (rfl : block g223 3 0 0 = true)
  · exact (rfl : block g223 4 0 0 = true)
  · exact g223B5
  · exact g223B6
  · exact g223B7
  · exact g223B8
  · exact g223B9
  · exact g223B10
  · exact g223B11
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223G : graphValid g223 (boundsBefore K191) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low223 : Lower true (varsX 223) (graphGoal 223) 12 := lower_forest (g:=g223) (i:=0) (hints:=16778819) (before_sound K191 V191) g223G g223T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K223 := extendKnown K191 12 [(223,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V223 : Known true K223 := extend_ok (m:=223) V191 low223 (by decide +kernel)
def g239Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffffee14261209cb86,0xf69000001f00000003ff])),(BitVec.ofNat 152 (word80 [0x52028a142602098384,0x269094a5294a5294a529]))),((BitVec.ofNat 152 (word80 [0xff000ac14f891c329f,0xb8040003e00001f00000])),(BitVec.ofNat 152 (word80 [0x640cca414f8114329f,0xb800739ce739ce739ce7]))),((BitVec.ofNat 152 (word80 [0x1f66cba280825a,0x622007c00003e007c00])),(BitVec.ofNat 152 (word80 [0x78171e464b2280825a,0x202318c6318c6318c63]))),((BitVec.ofNat 152 (word80 [0xffffe44b1363d60d92,0x11800f800007c00f801f])),(BitVec.ofNat 152 (word80 [0x801804431160960812,0x10002108421084210842]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x10ab09d24965c,0xc850000000f8000fffe0])),(BitVec.ofNat 152 (word80 [0x200108809d001400,0xc8414a5294a5294a5294]))),((BitVec.ofNat 152 (word80 [0x2954164680021,0x2cfbf00000fffff00000])),(BitVec.ofNat 152 (word80 [0x4000900000680020,0x4b08421084210842108]))),((BitVec.ofNat 152 (word80 [0x19700c0c937420,0x430dffffff0000000000])),(BitVec.ofNat 152 (word80 [0x800120000c004400,0x410d0842108421084210]))),(0x0,0x0)]
def g239C : List ColumnInfo := [(4,0,235,0,9),(128,0,111,0,9),(1,0,238,0,8),(2,0,237,0,8),(8,0,231,0,8),(32,0,207,0,8),(64,0,175,0,8),(0,2,45,192,7),(5,0,234,0,7),(9,0,230,0,7),(34,0,205,0,7),(68,0,171,0,7),(6,0,233,0,6),(10,0,229,0,6),(12,0,227,0,6),(33,0,206,0,6),(40,0,199,0,6),(64,2,45,128,6),(66,0,173,0,6),(96,0,143,0,6),(13,0,226,0,5),(38,0,201,0,5),(41,0,198,0,5),(44,0,195,0,5),(65,0,174,0,5),(68,2,41,128,5),(70,0,169,0,5),(72,0,167,0,5),(69,0,170,0,4),(73,0,166,0,4)]
def g239A : List (List Nat) := [[]]
def g239D5 := limbs80 #[#[0x32543b418754d814c950,0x796c20b40bc2e918754d]]
def g239D6 := limbs80 #[#[0x40a64a87d054d814c950,0xa1f095450d32543e82a7,0x51534c950ba4caa86992,0x1543ea2e8a9a62a85d2e,0x9c9ae898aa1f519454d3,0xa64a87f0dcd814c950be,0xfc373a05325437c30ec0,0x534c950fc4ba286992a1,0x43e9328a9a64a87d25d1,0xa6e6992a1f498754d325,0x4a87725d3734c950fa4a,0xb935d132542f9329b9a6,0x50d50bd5ca30e992a17c,0xe32a8b9a86a87c65d153,0xe6a9aa1d99745cd43543,0x85d66537354d50eacba6,0x71983c002eb726ba2a6a,0xe4bd173fcf03a8db2c48,0x86e5aa691955d1655593,0x371a07805fb7b1dd739c,0x30ad5e11059636131bc2,0x6c85e11b88581bf84317,0x4f04027821b27f846e20,0x89026102e50a04c25004,0x821cb420c36093c127,0x44a08901009e093c100b,0x240]]
def g239H6 (j : Nat) := if j=0 then 0x7c else 0
def g239D7 := limbs80 #[#[0xf49534c950f51534c550,0xbc5839c532bc7835c532,0xfe1814c950f71544c550,0xfc9434c950fe2814c950,0xf69544c950fcb734c950,0xf395450d50f595350d50,0xf5b7354d50b798550d50,0xf3b7455150b7b8454d50,0xfc5535c532f555454d31,0xde5755c532fc7835c532,0xf8d5450d32fc5539c532,0xf4d5454d32bcd8550d32,0xf1d5454d43bcf8454d32,0xfe9744c950ff1744c550,0xfd97350d50fe9874c950,0xbf98750d50fb97450d50,0xf798454d50f797454d50,0xdf9745cd50f79545cd50,0xdf974dcd50f7954dcd50,0xbfb835d150bf984dcd50,0xfcd8454d32fd58454d31,0x44b07f0c01341d01b000,0xd143250434790db1902c,0xf73c0724db1a33085c4a,0x4f89c53324b470885051,0xb255f2b3550a854b28b,0xe11af75e0b956d2d75a,0x47a874df8472da7e51de,0x7846440e49e11a128109,0x5a7a31de0e165a41ca92,0xc2e16a2e186b0b8544dc,0x15811630b1b84dc519c6],#[0x30194da87784dc5422ee,0xc4f8780c061ba718e1e0,0x6051b1302e0e1a418629,0xf65e1e01b159c938384,0xd89e1e0651cab8780744,0x1531112784c45c4c71b0,0xa66152f2784c45c549e1,0x17159b86245c40e49e1a,0x1a86e27845c51b66e189,0x1917878224689e1171b1,0xc65140d3c9024f240b1c,0xf24085810f240824c021,0x1804901a41d086c4c20,0x6c40210043c9020f2408]]
def g239H7 := limbs80 #[#[0x4c000000000402,0x65c00003c94400000,0xa300000000049c000,0x6539000058e4000044c0,0xa82a002a05e8d002d,0x40b080000000006300,0xe50000096000000000ee,0xe1b000070]]
def g239D8 := limbs80 #[#[0x932543f918aa1fc4c550,0x9a63de55150ef2a6a87e,0x32fcce2997e5714cbeaa,0x7f950503e6a9a65f350d,0xfba2a1df55150bfaeaa0,0xcd50ff2e6a87f943542f,0x98ffb74543fcba2a1fed,0xbf6b8a65fb4c951feaa8,0x754d43fdaea997ed544c,0xa8a9dfd7550fdeaa287f,0x54ffeba2a17fdd153efa,0x84788ba0ea130007fd74,0x3fa41406730d51882be4,0xbf97a0e65adb245ccabd,0xeaa148274cb992119e1b,0x92360c274ac217d6df58,0x30b06148a8547096a7ca,0xa41e1203b475248d85b9,0x213c38150c08e91d5830,0xe29b8f94689c1853100b,0x97107615524446c64e12,0x41b63a8b89c298755844,0x382490623c34d870091e,0x278702a923181e1c193c,0x33020383c29704930398,0xc4e0c2747309d1c2c382,0x9d2a305830a4304274a8,0x547458c6120fc38150e,0x431b1d3614b824900b0e,0x864aa622ca40a70c7a43,0x91784b8caa4e1665c519,0x6371f089c09880e8d8c],#[0xc9e1c12488f864e0264,0xb1cdaac3809c918d900e,0x3304c7861d283938701,0x1b264]]
def g239H8 := limbs80 #[#[0xe840000000000000a453,0x0,0x2d20000000000f7755,0x0,0x0,0xf9451000000008500000,0x203,0x6580000549d2800,0x22c00000000011716000,0x248842e21650000244,0xe3c0000000,0x186000000000000213,0x550000025b,0xb30000019e0000000000,0x18e0000000000d6a29,0xca1a700000,0xd34a4000000000000000,0xf7266001c200000,0x1e3,0xa7f6081c0000000]]
def g239D9 := limbs80 #[#[0x32fd8c7f531fe943f950,0xfd31ff543fd40ff443ed,0x3fd54ff54ffd43ff547,0xa54240f6692a11454180,0x848c950d0423fe3919eb,0xa3cd2c10924543430122,0x4cbd509234301448819,0x8c54301278d01509288a,0x10944a22b03235410923,0x5424c080c3d25410a434,0x950262b632354109238c,0x530]]
def g239H9 := limbs80 #[#[0x1c00000900010,0x7600000004a0100,0x7700003ba00,0x1da6e00001e4,0x180,0xb0d00000c3800007e000,0xf000000000000028800f,0x16,0x1cc00004200,0x80001638880000000000,0x25400000066a260085,0x5400748000000,0x0,0x119f6000,0x1f922000]]
def g239D10 (j : Nat) := if j=0 then 0xca48402ff else 0
def g239H10 := limbs80 #[#[0x35400186a9f640000002,0x321080000c0000000000,0x1900000000000ee700,0x3cc00000384000]]
def g239L : Nat → Packing
  | 5 => (2,5,5,0,0,5,0,g239D5)
  | 6 => (26,4,5,0,0,10,0,g239D6)
  | 7 => (42,3,5,0,0,11,0,g239D7)
  | 8 => (31,2,5,0,0,11,0,g239D8)
  | 9 => (13,1,5,0,0,9,0,g239D9)
  | 10 => (1,0,5,0,0,0,0,g239D10)
  | _ => emptyPacking
def g239I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 2 0 5 1 0 g239H6
  | 7 => lookupWord 6 67 2 9 5 0 g239H7
  | 8 => lookupWord 10 157 2 10 6 0 g239H8
  | 9 => lookupWord 7 127 1 9 5 0 g239H9
  | 10 => lookupWord 3 37 2 8 4 0 g239H10
  | _ => fun _ => none
def g239 : Forest := ⟨239,10,fun i => g239Y[i]?.getD (0,0),g239C,g239A,g239L,g239I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239P5_0 : block g239 5 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g239B5 : block g239 5 0 2=true := g239P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239P6_0 : block g239 6 0 5=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239P6_5 : block g239 6 5 21=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g239B6 : block g239 6 0 26=true := (@block_merge g239 6 0 5 21 g239P6_0 g239P6_5)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239P7_0 : block g239 7 0 4=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239P7_4 : block g239 7 4 22=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239P7_26 : block g239 7 26 16=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g239B7 : block g239 7 0 42=true := (@block_merge g239 7 0 4 38 g239P7_0 (@block_merge g239 7 4 22 16 g239P7_4 g239P7_26))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239P8_0 : block g239 8 0 10=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239P8_10 : block g239 8 10 19=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239P8_29 : block g239 8 29 2=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g239B8 : block g239 8 0 31=true := (@block_merge g239 8 0 10 21 g239P8_0 (@block_merge g239 8 10 19 2 g239P8_10 g239P8_29))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239P9_0 : block g239 9 0 5=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239P9_5 : block g239 9 5 8=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g239B9 : block g239 9 0 13=true := (@block_merge g239 9 0 5 8 g239P9_0 g239P9_5)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239P10_0 : block g239 10 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g239B10 : block g239 10 0 1=true := g239P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239T : checkedTables g239 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g239 0 0 0 = true)
  · exact (rfl : block g239 1 0 0 = true)
  · exact (rfl : block g239 2 0 0 = true)
  · exact (rfl : block g239 3 0 0 = true)
  · exact (rfl : block g239 4 0 0 = true)
  · exact g239B5
  · exact g239B6
  · exact g239B7
  · exact g239B8
  · exact g239B9
  · exact g239B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239G : graphValid g239 (boundsBefore K223) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low239 : Lower true (varsX 239) (graphGoal 239) 11 := lower_forest (g:=g239) (i:=0) (hints:=16778595) (before_sound K223 V223) g239G g239T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K239 := extendKnown K223 11 [(239,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V239 : Known true K239 := extend_ok (m:=239) V223 low239 (by decide +kernel)
def g247Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x828c2cd2734a2424d0,0xfe0000001fc07f])),(BitVec.ofNat 152 (word80 [0x82840c92520a2020d2,0x24489122448912244891]))),((BitVec.ofNat 152 (word80 [0x42bbc498503613c030,0x7f000007f0003f80])),(BitVec.ofNat 152 (word80 [0x4289c4985036124000,0xa142850a142850a14285]))),((BitVec.ofNat 152 (word80 [0xdcc73d801410da3100,0x3f800003f80fe00000])),(BitVec.ofNat 152 (word80 [0xcc822d801410922100,0x60c183060c183060c183]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x8532339ea8cc988c00,0x1fc00000000000003fff])),(BitVec.ofNat 152 (word80 [0x532330028c0888c05,0x4a952a54a952a54a952a]))),((BitVec.ofNat 152 (word80 [0x10a98a6d2c92ec42a0,0x1fc000fffc000])),(BitVec.ofNat 152 (word80 [0x1029806c28804c4229,0x93264c993264c993264c]))),((BitVec.ofNat 152 (word80 [0x6154172348210167df,0xe0000001fffff0000000])),(BitVec.ofNat 152 (word80 [0x2154120300000104d6,0xc183060c183060c1830]))),((BitVec.ofNat 152 (word80 [0x3f00c064938102186f,0xfffffffe000000000000])),(BitVec.ofNat 152 (word80 [0x100000648101001028,0x10204081020408102040]))),(0x0,0x0)]
def g247C : List ColumnInfo := [(1,0,246,0,10),(4,0,243,0,10),(32,0,215,0,10),(2,0,245,0,9),(64,0,183,0,9),(128,0,119,0,9),(16,0,231,0,8),(34,0,213,0,8),(0,16,100,131,7),(0,32,146,69,7),(130,0,117,0,7),(1,32,146,68,6),(2,16,100,129,6),(4,32,146,65,6),(18,0,229,0,6),(48,0,199,0,6),(64,32,146,5,6),(66,0,181,0,6),(128,16,100,3,6),(144,0,103,0,6),(80,0,167,0,5),(98,0,149,0,5),(130,16,100,1,5),(146,0,101,0,5),(160,0,87,0,5),(192,0,55,0,5),(194,0,53,0,4)]
def g247A : List (List Nat) := [[]]
def g247D6 := limbs80 #[#[0x644c629fa960c8359564,0x458359564d2bddb92615,0x7dd783a0d6559363775e,0x263da5a5f8359564e8,0x58189c59]]
def g247D7 := limbs80 #[#[0xb2ac8a8f8de456559151,0xa7c3f87595645478790e,0x1d6559153f0e49acab22,0x359387eeab2ee2b270f2,0xec1906b2ac9a3d855947,0xacab25ade458359564d4,0x1df985cc7359753f0741,0x8559131f1fc2acab2263,0xc797eecc2ac898debe49,0x8acab2663cbf76e15644,0x998f8fe156559331f5bc,0xf9261564cc6f6f22c2ac,0x59151f1fc3acab22a37a,0xc7eeac0acab25cf65787,0x6b2ac9e3f75e0565593,0x25afa5c8359564f1fba9,0x5a0d65593c7eeac1acab,0x564f1fbaf06b2ac9e3f7,0x15637866005afa5f8359,0xc75113ded9b12a22226f,0x5ad63d71505233ccb124,0x71bbaea9a2e5b8adfb77,0x814460b113c3e0618bce,0x91e1f004060cb23c3e00,0xc2913c2e00b3185d1145,0x670bc2101432a9f0f802,0x12a83250bc3e00b8e315,0xbe1f0690633693c21613,0x119b49e0f0858589f0b0,0x9c48b0878505900f882c,0x2403c366041606c88208,0x893420880094420170c1],#[0x9a10618060a240ac6a40,0x24e104a40493420ac64]]
def g247H7 := limbs80 #[#[0x724000016005a00d0000,0x2]]
def g247D8 := limbs80 #[#[0xcbf7659131ed56358531,0xe3d6559151e756558551,0x9f7815d953e3d6559153,0xabf865cd64bbb805cd64,0xabd869cd64d9f739cd64,0xbaf825d564e3f7559564,0xef56558531abf865d564,0xebd6559331ebd6559131,0xef56358551bf78159731,0xbf5819cd51bf7815cd51,0xdbf8759151dbc8759151,0xbf7815d951f778159551,0xef78159561df7815d951,0xf5c8359553dbc8759153,0xebd65dc564dbf8759253,0xdbf75dc564dbd75dc564,0xebd651cd64bbd85dc564,0xebd65dcd64bbd851cd64,0xebd8159564bbd85dcd64,0xebc8359564ebf8159564,0xebe8359564ebd8359564,0xbbf815d564ebf8359564,0xbf7815cd65ddd731cd65,0xddf739cd65aff865cd65,0xfbd8559131afd869cd65,0xfbd8559331fbf8559131,0xff78159731fbf8559331,0xfbd85dc564fbf8759151,0x4c1160e00a2064036000,0x62602321fc1d61b018a1,0x39a36c33e3202e22ac28,0x144e64b047243c4063c8],#[0x66586325f45a658054a5,0x7d279c74e7286f26cc69,0x7c94e9208da8a485e810,0xea90a62a34a069d89a29,0xd238b87805c6aeaad4ab,0x8384287e412e1e04e140,0x1716e0e1871c105c5b8b,0x51814428b87805865110,0x4387142c708c4e2e1e0a,0x484e1e0100f10a29b8c,0x84406e1e013101387804,0xe3a4e0c50d144b0b8f83,0x6e1e0121710278780544,0xe1c6161d908b8780485c,0xc1717871858364c322e0,0x17838b8444585c2e1e00,0x7804295447e2e1e01117,0x6484610e1e01819211b8,0xe1a5111c5b838b869444,0xc584787802861716e0e2,0x83105864362e1e016145,0x8460e2e146161a88a787,0x216e1e010278780405c4,0x838593142471831a3a6c,0x314407e0e1101810c4b3,0x2e1e010171860a09b878,0xe010161b8780405c4198,0x10a278780405841982e1,0x1c64649a41966c216e0e,0x24e1e017191d985b8781,0x6918c4f0b838458905c2,0x949a412c2e0e11720652],#[0xe06320930b8780586461,0x38b84585282609c5a4e1,0x50584c4e2e0e116149b1,0xc5c4e226e0e1161b8780,0x585614e4817886787805,0x61464c16159139228851,0x61609930d311a88515c3,0x8924a3181144402c]]
def g247H8 := limbs80 #[#[0xb7342620000345109401,0x7a668cb339b5e001c9b6,0x7b801d2a1d1031a9,0xe0cee355a00a6004aabc,0xf33200005850]]
def g247D9 := limbs80 #[#[0xd534c7fab0a63af59564,0x1a63f758d31fbca698fd,0x31bfaea98fbd644c7ef3,0xdff764c6febb2637fdd5,0xeb2663f758f31fbaa798,0x8551bfaed98dfd75cc7d,0xa8dff73547bea9aa3fd5,0x6febb2a3df59551f7ac8,0xf59561dfac6b0dff7654,0xc6a9fdd6354effb8aa7b,0x54fbeb2aa7ef59153fbc,0x77f5c653bfeeca9dfd76,0xfaed29fbd6494feeb1ca,0x7198effbaac77fdc563b,0xac9ef5c564bfaeb31dfd,0x4f7ae6b27bc73593dfb8,0xbd75593dfb9ac9ef9cd6,0xb9acb7fdc565f7eeab27,0xd51ffacb98ffd654c6ff,0x8ffd73547ff31aa3ff58,0xfeb8acbff5d951ffce6a,0x5cd65ff8e6b2fff71597,0x8007ff73597ff39acbff,0xa808c87806004b83381b,0x21269120fd8e90d48c00,0x1e39bd9a598a16b15694,0x9d285270a5523d221a06,0xab26311afd2e1ac9ab1a,0xbbcba8393b7f367352b3,0x6844943142040f3f73d4,0x8d0d4f54d9cc1ca9c8ac,0xdcddb2593574558d40d2],#[0x82c2218f0e0483e085ec,0x498219218905c5870171,0xe02e362c29301717161,0x5c7c58700e24283118b,0x878b0e0243054590961c,0x161c05c5498b0e02e2a4,0x987016170e2c04870a23,0x60c2587c58700c262e24,0x305498b0e02c2c345923,0x25a260c5845118b0e026,0x9218884078b0e02c3972,0xba521830962a262c3821,0xe1e04b8b096268c48688,0x1c8972d8b06114391085,0x2c380b8c18b25c18b091,0x852e59262c18450e301e,0x8a261c09460d13161c05,0x89870161b144c380b0b,0x700c1c205c5870161911,0x16262c380b0b101a5c58,0x6c5130e02e2c4c587017,0x3161c05c54442261c05c,0xc184b8b93062c23098d1,0xe02c2e2c38071215262,0x5894c1f0e02c406498b,0xc380b8c621232f14861c,0x102e261c040b084a110,0x1844909a110c380b0d87,0xc7830c5204924d8e2a4c,0x747130e2c05882499202,0x9171a262c38228c1a29,0xd262c1863161d262c38],#[0x2c298b0f13161c030b8d,0xc61d83161225864b1306,0x80b62c26871983161225,0x64b912d8b0611441723,0x97323842e5b161c08cc9,0x213c58309620292c5830,0x2319884b160c25c7328e,0x6c5830963]]
def g247H9 := limbs80 #[#[0x27246b302ca1c0001001,0x1a169de839798d532a5,0xdb69ad35725aa0000070,0x11f0001c59cee3231cad,0x82c927ed00280574009,0x5e366e40033773c862,0xbc00d340012000ad4900,0x70005af31a6c0094800b,0x30109b9592c13002e28,0x28edc99127fc3c6aee0]]
def g247D10 := limbs80 #[#[0x61ff547ff31ff4c7bd64,0xfe63ff58ffe53ff54ffd,0xfa10cc4b1985400ff597,0x890a48c58601bc1b0ba4,0x38a11871a59080e18a03,0x2464650e012188896480,0x228162175860e48a180a,0x50d71218221881850e11,0x1461d30c690c88586024,0x68c51208a11e48e2860]]
def g247H10 := limbs80 #[#[0x88003c6030624520300,0x4640000000003b6003d4,0x3ea6283a6d00000000,0x2ad003b0002d1f03af,0xd965acdf12b3ec7a7486,0x135003df,0x156c8e6876c00a9161,0x9bad8dc84d108000017b,0x4e000778009f0e9e07e0,0x9aca700026d5f4371213,0x2cf9920000000000000,0x155ce00145c2400cce2c,0xaf800633fd4400000000,0xdc8c400]]
def g247D11 (j : Nat) := if j=0 then 0x1483080437f else 0
def g247H11 := limbs80 #[#[0xe9008200b80000004000,0xf6000000000045001300,0xe10054f700000000]]
def g247L : Nat → Packing
  | 6 => (5,5,5,0,0,6,0,g247D6)
  | 7 => (29,4,5,0,0,10,0,g247D7)
  | 8 => (56,3,5,0,0,12,0,g247D8)
  | 9 => (63,2,5,0,0,12,0,g247D9)
  | 10 => (10,1,5,0,0,9,0,g247D10)
  | 11 => (1,0,5,0,0,0,0,g247D11)
  | _ => emptyPacking
def g247I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 1 13 0 7 3 0 g247H7
  | 8 => lookupWord 7 37 5 9 5 0 g247H8
  | 9 => lookupWord 14 71 6 10 6 0 g247H9
  | 10 => lookupWord 15 101 4 10 6 0 g247H10
  | 11 => lookupWord 2 29 0 8 4 0 g247H11
  | _ => fun _ => none
def g247 : Forest := ⟨247,11,fun i => g247Y[i]?.getD (0,0),g247C,g247A,g247L,g247I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P6_0 : block g247 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P6_1 : block g247 6 1 4=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g247B6 : block g247 6 0 5=true := (@block_merge g247 6 0 1 4 g247P6_0 g247P6_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P7_0 : block g247 7 0 11=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P7_11 : block g247 7 11 18=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g247B7 : block g247 7 0 29=true := (@block_merge g247 7 0 11 18 g247P7_0 g247P7_11)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P8_0 : block g247 8 0 13=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P8_13 : block g247 8 13 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P8_49 : block g247 8 49 7=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g247B8 : block g247 8 0 56=true := (@block_merge g247 8 0 13 43 g247P8_0 (@block_merge g247 8 13 36 7 g247P8_13 g247P8_49))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P9_0 : block g247 9 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P9_1 : block g247 9 1 49=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P9_50 : block g247 9 50 13=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g247B9 : block g247 9 0 63=true := (@block_merge g247 9 0 1 62 g247P9_0 (@block_merge g247 9 1 49 13 g247P9_1 g247P9_50))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P10_0 : block g247 10 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P10_1 : block g247 10 1 9=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g247B10 : block g247 10 0 10=true := (@block_merge g247 10 0 1 9 g247P10_0 g247P10_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P11_0 : block g247 11 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g247B11 : block g247 11 0 1=true := g247P11_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247T : checkedTables g247 11 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g247 0 0 0 = true)
  · exact (rfl : block g247 1 0 0 = true)
  · exact (rfl : block g247 2 0 0 = true)
  · exact (rfl : block g247 3 0 0 = true)
  · exact (rfl : block g247 4 0 0 = true)
  · exact (rfl : block g247 5 0 0 = true)
  · exact g247B6
  · exact g247B7
  · exact g247B8
  · exact g247B9
  · exact g247B10
  · exact g247B11
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247G : graphValid g247 (boundsBefore K239) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low247 : Lower true (varsX 247) (graphGoal 247) 12 := lower_forest (g:=g247) (i:=0) (hints:=16778564) (before_sound K239 V239) g247G g247T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K247 := extendKnown K239 12 [(247,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V247 : Known true K247 := extend_ok (m:=247) V239 low247 (by decide +kernel)
def g251Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xb45c75c5441000000,0xff00000000ff00ffff])),(BitVec.ofNat 152 (word80 [0x41431c1441212121,0x21212121212121212121]))),((BitVec.ofNat 152 (word80 [0x40ab06a9e949000000,0xff000000ff0000ff0000])),(BitVec.ofNat 152 (word80 [0x40a30608c9010b0b0b,0xb0b0b0b0b0b0b0b0b0b]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x210085aeaa20000ff,0xff00ff000000ff])),(BitVec.ofNat 152 (word80 [0x2100042e882060606,0x6060606060606060606]))),((BitVec.ofNat 152 (word80 [0x4a78b000a4be00ff00,0xffff00])),(BitVec.ofNat 152 (word80 [0xa18b00020be545454,0x54545454545454545454]))),((BitVec.ofNat 152 (word80 [0xa522fe2403b0000000,0xff0000ffff000000])),(BitVec.ofNat 152 (word80 [0x8522ac200330989898,0x98989898989898989898]))),((BitVec.ofNat 152 (word80 [0xbc0950031552ff0000,0xffffff0000000000])),(BitVec.ofNat 152 (word80 [0x280850011440606060,0x60606060606060606060]))),((BitVec.ofNat 152 (word80 [0x919621a01a05ffffff,0xffff0000000000000000])),(BitVec.ofNat 152 (word80 [0x910400a00200808080,0x80808080808080808080]))),(0x0,0x0)]
def g251C : List ColumnInfo := [(1,0,250,0,10),(8,0,243,0,10),(32,0,219,0,10),(64,0,187,0,10),(128,0,123,0,10),(2,0,249,0,9),(16,0,235,0,9)]
def g251A : List (List Nat) := [[],[96,65]]
def g251D10 (j : Nat) := if j=0 then 0x659ab8c1ffd31 else 0
def g251D11 (j : Nat) := if j=0 then 0x3544383ff else 0
def g251H11 (j : Nat) := if j=0 then 0x1 else 0
def g251L : Nat → Packing
  | 10 => (1,1,3,0,0,0,0,g251D10)
  | 11 => (1,0,3,0,0,0,0,g251D11)
  | _ => emptyPacking
def g251I : Nat → Nat → Option (Nat × Nat)
  | 11 => lookupWord 1 2 0 4 0 0 g251H11
  | _ => fun _ => none
def g251 : Forest := ⟨251,11,fun i => g251Y[i]?.getD (0,0),g251C,g251A,g251L,g251I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P10_0 : block g251 10 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B10 : block g251 10 0 1=true := g251P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P11_0 : block g251 11 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B11 : block g251 11 0 1=true := g251P11_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251T : checkedTables g251 11 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g251 0 0 0 = true)
  · exact (rfl : block g251 1 0 0 = true)
  · exact (rfl : block g251 2 0 0 = true)
  · exact (rfl : block g251 3 0 0 = true)
  · exact (rfl : block g251 4 0 0 = true)
  · exact (rfl : block g251 5 0 0 = true)
  · exact (rfl : block g251 6 0 0 = true)
  · exact (rfl : block g251 7 0 0 = true)
  · exact (rfl : block g251 8 0 0 = true)
  · exact (rfl : block g251 9 0 0 = true)
  · exact g251B10
  · exact g251B11
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251G : graphValid g251 (boundsBefore K247) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low251 : Lower true (varsX 251) (graphGoal 251) 12 := lower_forest (g:=g251) (i:=0) (hints:=16777283) (before_sound K247 V247) g251G g251T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K251 := extendKnown K247 12 [(251,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V251 : Known true K251 := extend_ok (m:=251) V247 low251 (by decide +kernel)
def g253Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfe6810d09140de7c42,0x4000003f00000003ffff])),(BitVec.ofNat 152 (word80 [0x810101040c66440,0x49249249249249249249]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x72213a6e2a3522a,0x40000fc0000fc0fc0000])),(BitVec.ofNat 152 (word80 [0x2c042013a48283522a,0x430c30c30c30c30c30c3]))),((BitVec.ofNat 152 (word80 [0xff049c85c8831692b0,0x8003f00003f03f00003f])),(BitVec.ofNat 152 (word80 [0x49040081c883101230,0x82082082082082082082]))),((BitVec.ofNat 152 (word80 [0xf86cd3deac000027,0x80fc0000000000000fc0])),(BitVec.ofNat 152 (word80 [0x70606cc3ceac000027,0x96596596596596596596]))),((BitVec.ofNat 152 (word80 [0x112a6c083f8928e4,0xfc003ffff000])),(BitVec.ofNat 152 (word80 [0x80110a6c0028080884,0x24924924924924924924]))),((BitVec.ofNat 152 (word80 [0x2e552b025400c55c,0xbf000000ffffc0000000])),(BitVec.ofNat 152 (word80 [0x2a55000254008440,0x18618618618618618618]))),((BitVec.ofNat 152 (word80 [0x191c1206588680781,0x7fffffff000000000000])),(BitVec.ofNat 152 (word80 [0x9180200100280180,0x20820820820820820820]))),(0x0,0x0)]
def g253C : List ColumnInfo := [(32,0,221,0,10)]
def g253A : List (List Nat) := [[]]
def g253D10 (j : Nat) := if j=0 then 0xff else 0
def g253L : Nat → Packing
  | 10 => (1,0,1,0,0,0,0,g253D10)
  | _ => emptyPacking
def g253I (_ _ : Nat) : Option (Nat × Nat) := none
def g253 : Forest := ⟨253,10,fun i => g253Y[i]?.getD (0,0),g253C,g253A,g253L,g253I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P10_0 : block g253 10 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g253B10 : block g253 10 0 1=true := g253P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253T : checkedTables g253 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g253 0 0 0 = true)
  · exact (rfl : block g253 1 0 0 = true)
  · exact (rfl : block g253 2 0 0 = true)
  · exact (rfl : block g253 3 0 0 = true)
  · exact (rfl : block g253 4 0 0 = true)
  · exact (rfl : block g253 5 0 0 = true)
  · exact (rfl : block g253 6 0 0 = true)
  · exact (rfl : block g253 7 0 0 = true)
  · exact (rfl : block g253 8 0 0 = true)
  · exact (rfl : block g253 9 0 0 = true)
  · exact g253B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253G : graphValid g253 (boundsBefore K251) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low253 : Lower true (varsX 253) (graphGoal 253) 11 := lower_forest (g:=g253) (i:=0) (hints:=33555715) (before_sound K251 V251) g253G g253T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K253 := extendKnown K251 11 [(253,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V253 : Known true K253 := extend_ok (m:=253) V251 low253 (by decide +kernel)
def g254Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffb2416914c07c274e,0xc8000000fc0000fc003f])),(BitVec.ofNat 152 (word80 [0xa20416904403c2642,0x48145145145145145145]))),((BitVec.ofNat 152 (word80 [0x4808bb623f143349,0xa00003f00003f000fc0])),(BitVec.ofNat 152 (word80 [0x330800bb003e143309,0xa0c30c30c30c30c30c3]))),((BitVec.ofNat 152 (word80 [0x39b32f0c22138523,0x3000fc0000fc003f000])),(BitVec.ofNat 152 (word80 [0x5c39b12b0422118103,0x20c30c30c30c30c30c3]))),((BitVec.ofNat 152 (word80 [0xff949c4c97ae4e9988,0x1203f00000000000003f])),(BitVec.ofNat 152 (word80 [0x6014980492ae429988,0x1269a69a69a69a69a69a]))),((BitVec.ofNat 152 (word80 [0x652c2fb48934e42,0x2200000003f00003ffc0])),(BitVec.ofNat 152 (word80 [0x800642407b40824c40,0xb2cb2cb2cb2cb2cb2c]))),((BitVec.ofNat 152 (word80 [0x8a90580d3a05810,0xbdfc000003fffffc0000])),(BitVec.ofNat 152 (word80 [0x8048081000010,0xb1410410410410410410]))),((BitVec.ofNat 152 (word80 [0x674430492480a0b5,0x54fffffffc0000000000])),(BitVec.ofNat 152 (word80 [0x4204004900800024,0x4820820820820820820]))),(0x0,0x0)]
def g254C : List ColumnInfo := [(4,0,250,0,10)]
def g254A : List (List Nat) := [[],[50]]
def g254D10 (j : Nat) := if j=0 then 0xff else 0
def g254L : Nat → Packing
  | 10 => (1,0,1,0,0,0,0,g254D10)
  | _ => emptyPacking
def g254I (_ _ : Nat) : Option (Nat × Nat) := none
def g254 : Forest := ⟨254,10,fun i => g254Y[i]?.getD (0,0),g254C,g254A,g254L,g254I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g254P10_0 : block g254 10 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g254B10 : block g254 10 0 1=true := g254P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g254T : checkedTables g254 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g254 0 0 0 = true)
  · exact (rfl : block g254 1 0 0 = true)
  · exact (rfl : block g254 2 0 0 = true)
  · exact (rfl : block g254 3 0 0 = true)
  · exact (rfl : block g254 4 0 0 = true)
  · exact (rfl : block g254 5 0 0 = true)
  · exact (rfl : block g254 6 0 0 = true)
  · exact (rfl : block g254 7 0 0 = true)
  · exact (rfl : block g254 8 0 0 = true)
  · exact (rfl : block g254 9 0 0 = true)
  · exact g254B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g254G : graphValid g254 (boundsBefore K253) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low254 : Lower true (varsX 254) (graphGoal 254) 11 := lower_forest (g:=g254) (i:=0) (hints:=287397184) (before_sound K253 V253) g254G g254T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K254 := extendKnown K253 11 [(254,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V254 : Known true K254 := extend_ok (m:=254) V253 low254 (by decide +kernel)
def g255Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x7f8000000000007f8,0x7fff8120589b6023bc4])),(BitVec.ofNat 152 (word80 [0x90909090909090909,0x90908120488b6001904]))),((BitVec.ofNat 152 (word80 [0xf800000007f8000007,0xf80000d80612078dbc9b])),(BitVec.ofNat 152 (word80 [0x585858585858585858,0x5858585804100285b899]))),((BitVec.ofNat 152 (word80 [0x7f80007f800,0x51818043830c00f])),(BitVec.ofNat 152 (word80 [0x383838383838383838,0x38383c1808041010400f]))),((BitVec.ofNat 152 (word80 [0x7f80007f80000,0x7fa382000404100c7])),(BitVec.ofNat 152 (word80 [0x303030303030303030,0x303030080000000000c3]))),((BitVec.ofNat 152 (word80 [7,0xfff800e44067807e0f23])),(BitVec.ofNat 152 (word80 [0xa2a2a2a2a2a2a2a2a2,0xa2a2a0a40067007a0222]))),((BitVec.ofNat 152 (word80 [0x7f8000007fffff8,0x3000078007ff038])),(BitVec.ofNat 152 (word80 [0xc4c4c4c4c4c4c4c4c4,0xc4c4c3000030006fa030]))),((BitVec.ofNat 152 (word80 [0x7fffffff8000000,0x427807fff800000])),(BitVec.ofNat 152 (word80 [0x30303030303030303,0x3030026804bed000000]))),((BitVec.ofNat 152 (word80 [0xfff800000000000000,0xfff8000000030])),(BitVec.ofNat 152 (word80 [0x40404040404040404,0x4040001730000000000]))),(0x0,0x0)]
def g255C : List ColumnInfo := [(4,0,251,0,12),(8,0,247,0,12),(32,0,223,0,12),(1,0,254,0,11),(2,0,253,0,11),(16,0,239,0,11),(64,0,191,0,11),(128,0,127,0,11),(34,0,221,0,10),(96,0,159,0,9),(130,0,125,0,9),(144,0,111,0,9),(0,2,45,208,8),(0,16,108,131,8),(0,32,146,77,8),(3,0,252,0,8),(17,0,238,0,8),(18,0,237,0,8),(33,0,222,0,8),(48,0,207,0,8),(65,0,190,0,8),(66,0,189,0,8),(80,0,175,0,8),(129,0,126,0,8),(160,0,95,0,8),(192,0,63,0,8),(1,16,108,130,7),(1,32,146,76,7),(2,16,108,129,7),(4,32,146,73,7),(8,32,146,69,7),(16,2,45,192,7),(50,0,205,0,7),(64,2,45,144,7),(64,32,146,13,7),(128,2,45,80,7),(128,16,108,3,7),(146,0,109,0,7),(3,16,108,128,6),(5,32,146,72,6),(19,0,236,0,6),(49,0,206,0,6),(65,32,146,12,6),(80,2,45,128,6),(82,0,173,0,6),(97,0,158,0,6),(128,4,27,96,6),(129,16,108,2,6),(130,16,108,1,6),(144,2,45,64,6),(145,0,110,0,6),(192,2,45,16,6),(194,0,61,0,6),(51,0,204,0,5),(67,0,188,0,5),(81,0,174,0,5),(131,0,108,0,5),(131,16,108,0,5),(147,0,108,0,5),(161,0,94,0,5),(208,0,45,0,5),(208,2,45,0,5),(210,0,45,0,5),(224,4,27,0,4)]
def g255A : List (List Nat) := [[]]
def g255D6 := limbs80 #[#[0x52bd271bb05d79460570,0x13]]
def g255D7 := limbs80 #[#[0x83b0e71975e91915c160,0x560b16fc26a3975d5415,0x75582c57f0da8e5d7550,0x85d560bc73c16d176641,0xa6175582a4ff11b169e9,0x817550570a977c16d1a7,0x175e51815c275af09b6e,0xb65d79460570b539c6ec,0x26d975e51815c2d4ef01,0xf09b6e817560570b52fc,0x6bc26dba05d5845c275a,0x25be1fb269b905d5419d,0x5d47796ec5a45d9805d7,0x5d715daa7b1691766017,0x900ac75c0e1ba165176,0x96ccd5274884f1b303c6,0xc8604001c0c1fde3,0x3d14100000]]
def g255H7 (j : Nat) := if j=0 then 0x1 else 0
set_option maxRecDepth 16000 in
def g255D8 := limbs80 #[#[0xe0884d6bb269b905d570,0x65d570502eb5d934cbaa,0x2ebd2322b82c175aec9a,0x6c79a6e85755c160da7,0x570582e3cdb742baae0b,0xd02eab22c171e6dba45d,0x7976e51905d560b8f76e,0x58363cbb341c8aeab074,0xecbaac1b1e5d9a0e5175,0x4685875d560b8ef62d22,0xcbbd8b48c3aeab0593fb,0xae1d4eec175e51815c2,0xb945d570e27b0cbaf28c,0xc3f44cb2eaa0cd7bb069,0xb51f6daa95d9805d74b7,0x5d975c8ff4cbb321c0ae,0x42ca2ecbad577b165190,0xf6a3965d97550363bc37,0x60f0fd51cb2ecbaa81e1,0x8ae0b07c79b65d5415c1,0x97565170583e3cdb2eac,0x8f2ecd02eaa0ac1f1e6d,0x2b0757b976817550560f,0x5d541583a3fcbb4cbaa8,0x51cbaeaa0ac1c5f6a397,0x5b6fb26a17550560e2fd,0x41582dafd9b50baa82b0,0x42eaa0ac165fedda85d5,0x9b15d9905d560b2fb6f5,0x83e3cda2ecc82eab07c7,0x8baac1a5fee987e45755,0x685875d560d2ff74c3f2],#[0xbbd8b48c3aeab05d3fb4,0xac1a5f6c5a7a6175582e,0x985d560d2ff62d3d30ba,0xa34f4c2eab0697db469e,0x75e6dba05d5415c34bfd,0x570baf760d32eaa0ae1,0xbaac2b85d6fb2699755,0xe63a05d5615c3abccc74,0xea7b6cbaf28c0ae1d5e,0xb02b8753fb65d7946057,0xa05d5815c3cbcc3740ba,0xf760d32eac0ae175e6db,0xb85d6fb26997560570ba,0xd5845c2ebcdb740bab08,0x4d32eac22e175eec1a65,0xd7bb161b905d570badf6,0x55066bfdd30dc8aeab85,0x320baa83b1fe99766417,0xb269b905d541d2ff0fd3,0x74bfc3b4dc82eaa0cf6f,0xbaa8371f6c3965d97550,0x89965d541d2ff0fd032c,0xfc3b41cb2eaa0f96f87e,0xc9b1fae976641755874b,0x460175d8fd74bb320baa,0x342bb300bae57dba5db9,0x5faa5a15d9805d7a3fcb,0x175baef62d22ecc02eb9,0xbb300baf47f966917660,0xc5a45db805d72bf54b48,0xcafb74bb321c22eb75de,0xecbad57fb968176e1175],#[0x4641765d7a3fc3328c82,0xb61c3322bb2ebb1fe1ba,0x5c7db0e19945d975b8f,0xcd0a908505b83d02400,0xe49b01869629391150f1,0xbac2298a8525ba322139,0xb81b68b5ab4cb33b152e,0xff3f6be8bcfbbc3a8b9a,0x5c42c3fc31c18c10407b,0x48ec8647846fc61c53c4,0xf64e84d4cc6cadc9fc97,0xe565d5253ed30d1d509c,0xdac59e595d8d584d76d6,0xf85efde1dd3dcb5bd5b4,0xa651e43e35e22619e0bd,0xc104e369267ee7666865,0x27c187a2617f8bf12e37,0xe19dc6c2e09fe08a09fc,0xe198c6c4f810690bfc11,0xc498ca914f81f040d8d,0x150c46ae210ff81f042c,0x4178c1608818df81f04,0x8be08c048277c0e8bf,0xf81f04150e2ac4a490f8,0x96f8216060b0256464c5,0xfc0f07f047143b17e00,0xfa17c0f824c19c317145,0xf0483358670bdc4f0de0,0x4d0e19c2f717c1f42f81,0x7f823f4461ff03e09981,0xdc61cccf44c3470be011,0x198686c666c5f81063e0],#[0x34a6687f81f047723f05,0x9f020c6c3f823a54e865,0xd05067e07c11c9124de8,0x56f81f058c0b85ee2961,0xc082066e10873021362a,0x89d8ac0c4607944221c,0xd5442d8ac0c670891067,0x9b51b06182f2a3618330,0x224302222431c0b80101,0x44222091107238391c12,0x1e209609273c468425,0x2bc40b0ce170b0ce1708,0x30178a0bc578813c405e,0x4272421388c3308a6025,0x9780e0c309c908205ed1,0xfa2d0f6881bc633011c,0x82893d17a206533a290f,0x9e8a1f45a209243e8b82,0x10635421980e0b042744,0xcc02121707050902a301,0x88903301048482413180,0x418240546f8509467840,0x1e4606c1144088758201,0xe180ae21450805dc4b8a,0x5698a10462a0102f07a1,0x40ac1c55d04154319a09,0x66ec]]
def g255H8 := limbs80 #[#[0x5f7d1b8100009773810,0xc900de00369275007c0,0x2800fad48]]
set_option maxRecDepth 16000 in
def g255D9 := limbs80 #[#[0x7450110f6c5d17150110,0xfac5914158110e6e61d,0x97558110f3c5d9715811,0x10d5e65d7558110f1e5d,0xd5415c110f6c5d1415c1,0x110e6e611745c110f5c5,0x5d7845c110e5e5d5845c,0xc110f5c685755c110e5e,0xee19755c110e5e619755,0x50510d5ee59755c110e5,0x5de5d7550510e6d61d74,0x65c510e6d611745c510d,0x8efe91985d110e3d6197,0x765d510c5fe5d7561110,0xacfe91985d510e1f619,0xe985d510a5fe9d985d51,0x408efe91985d910a5f69,0xd7815c140e6e5d3815c1,0x140d6e5d3915c140e5e5,0xe19745c140e6e619745c,0xc140f4e691755c140e6e,0xee19755c140e5e619755,0x5d540b4fe9d945d540e5,0x5fe9d985d540e1f61976,0x85d940a5f69e985d540a,0xe5e5d7815c1608fde859,0x645c160f2e5d1645c160,0xe5e5d7845c160f1e5d5,0x975e0560f1e699755c16,0x60c5f65d75e0560e1f5d,0xd975e1160e1f61d75591,0x560c5f65d75e1160e1f5],#[0xe9d905d560f1e5d9905d,0xd560adbe89985d560b5e,0xfe9d985d560ad7e8d985,0x60570a5f69e985d560a5,0x5e687905d570d4f5d794,0x5d570d5e653905d570b,0xb5e69b905d570b5e6939,0x945d570b5ee81915d570,0xb5ee81965d570b5ee81,0x9645c541b5be89965d57,0x41b6d69d645c541f2d5d,0x19765c541e6d619745c5,0x141f0f5d97559141e3d6,0x619765d541e4fe1d7559,0xd541a5fe9d865d541e1f,0xf69b875d541a5f683875,0xe01618fde85985d941a5,0x1f5d975e0161e3d5d971,0x45c561f2d5d1645c561e,0xe3d5db845c561b3d69d6,0x75e1161b3de91765c561,0x1f1d5d9915d561e1f5d9,0xd985d561adbe89985d56,0x64a5f69e985d561a5fe9,0xd975e0564e1f5d975e01,0x564f0f5d9945d564e1f5,0xe81765d564b4fe9d945d,0xd564adde85985d564b1f,0xfe9d985d564adbe89985,0x60175a5f69e985d564a5,0x5f69b9760175d1fe5976,0x6605759dbe8996e01759],#[0xd1fe597660575e1fe197,0x9761175d1fe597661175,0x595f69b976117595f683,0x3865d975b5de85945d97,0x75b1f687865d975b1f68,0x997558110b1f693865d9,0x110f5e65d7558110f9e6,0x699755c110f5e659755c,0xd510f5ee99755c110f5e,0xbe89965d510f1fe59765,0x5c140f6e5d1615c140bd,0x6e659745c140f5e5d561,0x55c140f5e685755c140f,0xf5e659755c140f5ee857,0x755c140f5e699755c140,0xf6d5d17158540f5ee99,0x97558540f3d5d9715854,0x40f1fe59765d540f1f5d,0xa1765d540e5f6a1765d5,0x940bdbe89965d540e5fa,0x69e985d940a7fe9d985d,0xc160f6e5d1415c160a7f,0xe5d5815c160f5e5d5415,0x5c160b7ee9d815c160f5,0x5e5d5915c160beee9191,0x45c160f6e611745c160f,0xb7ee9d845c160f5e5d58,0x755c160f5e5d5945c160,0xf5ee91755c160f5ee85,0x97150560f6d5d1715056,0x60f1f5d97550560f3d5d,0x5d7550560e5f61d75505],#[0x560f3d5d9815c560d5fe,0x5d975605609efe91985c,0x560e5f61d7560560f1f,0xfe5d8760560d3fe5d766,0x59160f9e6817559160c7,0xfde85985d160f1f61d75,0x561160f1f5d975611609,0xd3fe5d7661160e5f61d7,0x905d560c7fe5d8761160,0xbde683915d560ddee51,0xb915d560f1f5db915d56,0x60b9f69b915d560d9f65,0xa3915d560e5f61f915d5,0x560bde683945d560adf6,0x69b945d560f1f5db945d,0xd560e5f61f945d560b9f,0xf685765d560adf6a3945,0x5d560f1f691765d560f1,0x5fe85875d560e5f68587,0x75d560e5f691875d560e,0xbbde85945d960e5fe918,0x9461d60aefe919161d60,0xf5ee817550570afde85,0x17558570f5ee81755857,0x70d5fe617558570d5f66,0x9f985857097fe9d98585,0x570cef61b946057097f6,0x6197560570f5ee817560,0x1170f5ee817559170e5f,0xf6197561170f5ee81756,0x5d570f5e61b905d570e5,0x5f65b915d570e5fe1b91],#[0x45d570b5f69b915d570d,0xb5fe85865d570b5f69b9,0x905d541b5fe85965d570,0x1e5fe1f905d541e5fe1d,0x9965d541f1fe59765d54,0x41e5fe1d965d541bdbe8,0x81765c561e5fe1f965d5,0x561f1f5d9905d561f3d6,0x5db905d561b5fe9d905d,0xd561f1f5d9945d561f1f,0xf681765d561f1f5db945,0x5d564f1f5d9905d564f1,0x1f5db905d564b5fe9d90,0x160175f1f681765d564f,0xe5f5db8460175d5fe5f9,0x9460175e5fe5f8460175,0x5d5f5db9460175d5fe5f,0x576601759df69b946017,0x75d5f5d990e0575d5faa,0x8986e05759dfe9990e05,0x175d5faa57661175edbe,0xe8176e1175d5f5d990e1,0xd9759dfe8196e1175b5f,0xf651905d975d5f645905,0x5d975b5fe91905d975d5,0x1fe19915d975f1fe1990,0x161975f1fe19945d975f,0x9df6839161975ddbe4b9,0x9261975ddbe539261975,0x6ddbe939261975ddbe87,0x17550560afde85846017,0x60f9f6997550560fde68],#[0xa17550560f5f61d75505,0x560edfaa17550560edf6,0xe85875d560f5f685875d,0xd560f5f691875d560f5f,0xfe919161d60f5fe91875,0x50570bfde859461d60be,0x5fe997550570f5f69975,0x560570f5f6997560570f,0xf5f6997561170f5fe997,0x915d570f5fe997561170,0xf5f685865d570f5f61b,0xd9161970f5fe85865d57,0x41f5f5d9905d541b7fe9,0xdb905d541bdfe99905d5,0x541bdf69b905d541f5f5,0xe89965d541bdfe81965d,0x175bdf683965d541fdb,0xf6917660175f5f685766,0xe0175f5f68576e0175f5,0xdf69990e0575f5f69176,0x6e1175f5f68176e1175d,0xf5f691905d975ddf6819,0x9460176f5fe91905d975,0x16401980170000b7fe9d,0x21a03c406800a500fe0,0x101a802fa05840a5012e,0xa30135824a046608480f,0x6620c5417a02c905640,0x683cc076a0e641be8357,0x28423d845a0868104c1f,0xa78148027d04e3098e1,0x985dc0b8016542bc8562],#[0xa3833b864c0c6a18642f,0xe841c8437d86da0d681,0xf07e20f8c1e583bd075e,0x2dc44b087510a820b83f,0x12a424ec48a88f911a62,0x709f7139826984c00969,0xa905418a5d148c28a850,0x16922cc857c0ae1158a2,0x28be917902e9c5c08b65,0x2e464e8c7c18b630ac60,0x1ab234b868b8cf119aa3,0xc0e121bd837046d28d89,0xb247540e961cfe397871,0x1f043d707a00f151de83,0xf905e2070405c7f38fc1,0x4e088e10fb21b442d083,0x23ce47048d0117a22b24,0x929624e0495091c120d,0xdfc9af133d26384bd896,0x288450709f613cb27404,0x5950529b452e4a499472,0x768ad7958e2ada5530a9,0x2d805a2cb2d96352c1e5,0x217742e7e5c78b8116e1,0x1d8c25981b2ff45f28bd,0x329a64b0c8818d631386,0xd9a1a33d46724cd41982,0xb94d5d1a9434e66970d1,0x37146da4da69b2736206,0xa9c3438306ff0ded9bba,0x488e7e1cdb394c71d8e2,0x3bf2774ced91d7d3aa47],#[0x31e8f3ce67970f229e1a,0xe1cfb09f3b3e167b44f5,0x406c8054ff51fc93f5a7,0x820ef41a682a103c2057,0x7110cf218742c2849d08,0x44b488f9116221043e88,0xaa2be45588a55141a26c,0xdad1a7a324461a8bb116,0x47ee8f951dfa3a347188,0xd247e48ba9119215240e,0x48528524f349ae92ed24,0x4b4695f52b5a54f4a7a9,0xc0ac5f03c10702b125b5,0xc0087c10bc7017c0f061,0xbc2f03c10ac703c14f0b,0xe42af03c10cc70670322,0xe1039f03c10cc8e13c50,0xff0bc0f042f1914b0bc5,0xc606fc0f042f0cc5a320,0xcc2f1407f0bc0f04330b,0xf03c10bc3d1018f03c10,0xc10c4840fc0f04310a85,0x50f2c18e1217b09c6f03,0x1805ec249bc571bc0f0,0x3c2a05fc0687c1242a09,0x12fc0f052119c6f142fc,0x211bc0f04330bc4e0fc2,0x3c147c6e0fc212fc0f05,0xb47f03c11e0ae0fc2f0,0xf0033f05281384e0c0df,0x8e134216783f03c10c48,0x85e1383d1fc0f0422181],#[0xa60887e0fc0f042308,0xf0bc0f047f1784e0fc1f,0xcbc12705e1383d1b47,0xc40cfc00cbc10c05f0bc,0xbc0f049c1bc0f049c0a,0x71bc2f03c10c8782dc6f,0x40fc0f042a0bc60ac23,0x18e143071bc0f042f1c3,0xa470a81871bc0f043a18,0xc070904e16020f03c10,0x209050a818d0b83f03c1,0xc0f04220c84e0fc0f042,0x785e0f46d1fc2f03c11f,0xf04261c0af03c10c42a1,0xaf04391017a184bf0bc0,0x8808fc0f042f0a85f002,0x42f40fc5f1217f03c10a,0xc42a100af03c10c42a1,0x4d16c2f03c10e47f03c1,0x8412fc0f04300a850651,0x17c0f042a23c0f04300a,0xf04350a840cc86f1119f,0x5f1386e0f47f041d1fc0,0xc5f1386e0f47f001e1fc,0x47f17c403bc0f042d1b,0xbc6f17c403b86e0fc0f,0x10c42a15c2f1b44f03c1,0x18f03c10bc2a1483f03c,0x1b2423f03c10bc2a14,0x142408fc5f121771bc1f,0x10bc2a16c4f03c10e42a,0x17b1bc0f041b2423f03c],#[0x2c6f04271c2408fc5f11,0xbc0f042f1b07c5fc5f1,0xf0bc042bc126860650af,0x571bc2f020af049a1ac6,0x3c10bc7f0bc082bc10bc,0x47c10bc508859b0b84f0,0xd0b84f03c10bc7d1bc04,0xa813c00bfc12b0431818,0xfc00bfc12b04f0033f04,0x1c0cd1b47e17c2f03c11,0x4202609343f0bc0f0434,0x4063c50e42ad0fc0f043,0x3c109a1f17c0f041f098,0x13c2f03c187c2f1404f0,0x457c10bc7f03c10991f,0xc0f04310a860600bb0bc,0x38606f47f041d1b4221b,0xd04e1bc0f041b08c5e1,0x4f0343f05162fc1f001b,0x39102a08c1805ec24afc,0xbc0f04300a85f03c10cc,0xbc7083c0f04240a8521,0x106c6f10330a819f03c1,0x47f041d1b85e1b47f03c,0xbc0f042406c5e178606f,0x17c4e1bc02afc106c7e1,0xf17c426743f03c10889e,0xe86035f03c10b4609023,0x85f17c4b1b87f04271a0,0x42a0cc5063c0f04330a,0xd17c0f043d0a85093c0f,0x40920e86020f03c10a47],#[0xfc0f061923c0f04240a8,0x3c10889e0830187c382,0xa8509023f17c4865c3f,0xf04300a8511bc0f0431,0x85e13c0f04330a8811bc,0x39f03c10cc2a1d26127,0x12c2f03c10cc391fc5e1,0x43f84f07c006c3d1d14e,0x4e13c1f002a1603d18c9,0xbc109e3d0fc0f042a0f4,0xe48b1bc2f03c10c4391,0x9181b46058b1bc0f0431,0xc10a8871a85f03c2f043,0x3d142485d10e14c8f03,0x32f04391fc00ebc10c,0xf7c1f001b33853082af,0x6310325c44402471a17,0x97183385fc0f04580a87,0x46e0e0cf088bf004af04,0xc46f0bc0f04300e86437,0x182a16458f03c10c03a1,0x10c0ae1058f003df042a,0x30c90e61342e0c59f03c,0x2443b42167c0f043a1c3,0xc06e12c68f747f042718,0xf043a1406e0fc2f03c10,0xf0865f042f1806f0bc0,0x86463c0f04650bc6887c,0xa9551fc5f0039f042a1f,0x85c7b13c0f0839f06141,0x30e47c52c4f001af0bc1,0x140988b15c2463c0f043],#[0x839161704247f0bc0f05,0x3c2f04391610f03c10a,0xb1518f03c10c8391ec5f,0x430839f03c11602a2386,0x17717c0f04580a8a715c,0xbc11951a1c330c5c430a,0x3c11942f1847887c0f0,0xcfc0f04650bc6267c2f,0x60cc82f03c11942f1898,0x2b20980cfc0f05510bc,0x28646415f0bc012bc125,0xf042a2786f03c2f041a9,0x31f44454c7267c50e7c0,0x1427c5d1039f03c10a83,0x39857c5d1099f0bc0f06,0xa870e744f03c2f043318,0xa864ad16d17c0f042f0,0x3f064b2019d17c0f0439,0x2a0e47131c4e1bc0f0b8,0x42a0e4645b10267c0f04,0xbc0f04391899d17c0f0,0xd17c0f0bc10e4626614f,0x82adc5f03c11602a1899,0x3b0e6c4317c0f04580a8,0x919f16c4f03c11602a28,0x13c0f04580a870c02f90,0x287c0f04580a8729bc5b,0x20e7c0f04580a89f149a,0xc4f03c1160a466c5b124,0x2a183b2848de1885e0e,0x42a0e462849af03c116,0xf03c10a8391642467c0f],#[0xa46642f002af0439183f,0x8ce1884e0ec5f03c1160,0xc39f03c10cc34243f268,0x3c10bc3d1fc571218e0,0xe7c0f043325c4d0a18f,0x8f0433191b0d1c571342,0x42f03c10e4971439f014,0x7c10e4846dc40f432717,0x6191e1916094d0bc071,0xf0bc12f14086c5f0bc0f,0xc5f1471719d1f86b13c0,0x7d1f83b17c0f0bc12c9a,0xc18942f14a1c67147131,0x498f0439f002a1898f03,0x16c2d1bc025fc10c4ad1,0xf0155f04391c340bc4e5,0x2f0383f0431182313ac2,0x87d1bc2f03c10e46d1bc,0x59486917f0344f0bc125,0x1b45263c0f0439181f66,0x9134530bc0f04330e46d,0xc0f04320e46f03c10a83,0xcc2f03c10c8391c98d17,0x142ff03c18602a209982,0xf0117f06180a8805dc4f,0x7f03c106c3d102fb16c4,0x4523c49e0fc0063c10f4,0x5480c460ffc0f042a0e,0xf02c6f04312783b1bc0f,0x1f042f188f1261871383,0xc0f04580bc6162c6f019,0x458f07c08943316c6647],#[0xf00331b07927c1c96331,0x1f00580cc6162c3f0591,0xc2f0039f060a26c3647c,0x7c0f042229c3051c5067,0xd46656c525423b0d190e,0x1602a1c5813b86f03c10,0xf042a26c30bd19f07c0,0x39222008d19256c5e13c,0xca06096a1242f03c10c4,0x1c3717420e784f03c10c,0x5b85f03c1088391a1825,0x3858e1bc00bfc10d472,0x3923850abc0f04580e46,0x448609406742e17c0f04,0x22f043913c008bc10d,0x20d44063c008bc10d45f,0xc6f0343f043023c0f042,0xb87f03c1b14b15918b15,0x649137438384c71844e0,0x9061863c5f13c0f05122,0xee450e7c00cfc10a870,0x71344571b44f03c10ec7,0x586255a25c0f041b8f4,0x63c10e46093c0f042a48,0x267c18602a205671bc00,0x3d17c10fc60cf45d13c0,0x39f03c10cc34184c111c,0x5c4a0bc0f042f0f46a08,0x39c5e0ac3f03c1864302,0xb1033f03c14602a20932,0x6463c1f00340f45066c5,0x63d12c4b0d18f07c00f4],#[0xb87f03c1b10b06fc107,0x747133468384d115c3e,0x74f447113d06f87d1bc1,0xc4d1bc109c2e1f09f042,0x619b17c0f0bc12533c25,0xbe4761951141cc5f1428,0x50c332264760e6514350,0x47605804450c14330bc6,0x15c40e43412474450c0e,0x57103d0c8485dc40cc37,0x717c534712190bdc50dc,0x60c331b19c5f14d1c4c6,0x1c44332604225c0c4551,0xc9127457018308e0a215,0x24671b4518a0a2605138,0x1889810c97020b60c4e1,0x746618b1117d08571a0b,0xc30e02f08e17715c40d0,0x1423466c445c485dc40c,0x62448c1452a45913182f,0x6a45910bc581052c1cc,0x448c1449c1cc33009123,0x927073000e1849c1cc32,0x514b073189123058cf25,0xc241584449824388a154,0x8605d0c8a46e1811c422,0x50ec6171837134346c8b,0xc5a70c325f45c0899860,0xf03309219715c40c870f,0x445ec54644865c50bc30,0x2]]
def g255H9 := limbs80 #[#[0x27c1801404214002000c,0x20f70c000d1a42c,0xfc2000000a8909e86b3c,0x719aea22920940000023,0x34d0000000000061ee,0x54d5185e4dc,0xa6c15953425e4c00,0x82003560009a40000000,0x11c00000000000000007,0x65d84f2ee98007c863a,0x7800b0da240038200000,0x96d7d204003b1e01effa,0x935292261ada72440002,0xd38c2fc5a07f2891c91,0xd59ba0728cf40035000,0x516adb611a18a87,0x5aea30c1f9d800781cd0,0x31dec19d6c672a86400,0x3552a886422a5c00]]
set_option maxRecDepth 16000 in
def g255D10 := limbs80 #[#[0x77f28c3a21d79755c110,0xbcbaae0a076e5d170502,0xfaecbaac1d79755c160e,0xdc82eab865f61d755838,0xae8b8a8397f865d570eb,0xbb2e2b0e5fe1d75507b6,0xecbaac9c7d765d561e7a,0xbb00bacfde45875938fa,0xbb2eb57f9761175abfc,0x30cbaf1fe19765d6aff2,0xa0221ff17150110bb7c9,0x80887de5d540443f72e8,0x2217fb9650110bfccb2,0x886fee1d404437f30ea,0x2217fb9750110bfccba8,0x887fc5c560443fe282b0,0x217fb9458110f7cb22c0,0x87be5d960443ef2eab02,0x1bfb8758110dfcc3ac08,0x5fee5d60442ff32eb022,0xdf9745c110ff8a0ae088,0xfee11704437f308b8221,0xf9865c110bfdca2e0886,0xee59704437f70cb8221b,0x57450510fdab2282885f,0x61d41443eeaeaa0a21fb,0x9750510dfbc3a82886fd,0xd171442fef2ea0a217f5,0x45c510dfac22e28877d5,0x971443beaecb8a21bf78,0x59110dfbc32e2886fd61,0x6444377f08b22217f791],#[0xd1109fecc2c8886bf619,0x44433fb0eba221bbd845,0x110dbebab08884ff6617,0x4427ff2ec22213ff9661,0x109fecb708886df5d784,0x43eeb22baa213fd97e11,0xdbec32ea8875f5d9754,0x36fb30baa21b7f865d51,0xbfbc8aec886dfa617544,0x7fb30bb221afd865d910,0xffcbb0c884ffe5186442,0xfb2fc32213fd94e19109,0xe4a30e885efe51874427,0xf28c3a21bbf9461d10dd,0xca70e884ffe59874427f,0x2b82813fd96e1d109fe,0x32e0a05fee45705037f7,0x8b8a81bfb865c140dfcc,0xf02a06ef5d381503b7ae,0xc0a813fd96e0540dbeba,0xe8a06ef619745027fb2f,0xaa81f3d945d540ddfc32,0xaa06df61975503afaecb,0xa81b7d985d540dbfc32e,0xa06bf619765036fd30ba,0x813ff91619409fecc2ec,0x4ff647865027ff2ec32,0x13ff9161d409fecbf0ca,0x4ff647875027ff2cc3a8,0xbfb815c1609fecb70ea0,0xbe59170582ff722b82c1,0xfb845c160efcba2e0b07],#[0xf59141582ff720a0ac1b,0xd64e0560e7ebb2e2b07a,0x5d7815827fb29c0ac1af,0x97e0560d7ebb702b06df,0xd564583d7ae8b22c13fd,0x759160d7ec3ac8b079f5,0xd64582dfb2eb22c1aff8,0xe11609fec8f08b05bfe5,0x845835faedc22c1b7d75,0xd560fbcc82eab04ff65f,0x5583afb0ebaac1e7d965,0x960dbf4c2eab06df6617,0x5827ff22c3ac16ff945d,0x609fec8f0eb04ffe5187,0xc3b7ae8a0ae13fd94e1d,0xebebaac2b875f5d5415,0x3afaeac0ae17bf946057,0x9feca702b867f5d3815c,0xb7ae8b22e13fd96e0570,0xbebaac8b86efe11645c3,0xfb23c22e1d7d7561170e,0xec8aeab84ff65b845c27,0xb28baae1d7f915d570eb,0xc32eab875fe51755c3af,0x2cbaae1d7d965d570ebe,0xa70cb84ff647865c3aff,0x8b8a833fd96e01419fec,0x2e2a0f7d5d971507f6ac,0xb2283f3d7559141dfac3,0xc8a0eef61d64507d7aec,0x22837bd9759141ddfc3a,0xaa0eef61974506f7f2eb],#[0xa83b7d865d541ebebb2e,0xa0ebf619765076fb30ba,0x833ff90619419fecc2ec,0xcff643865067ff2ec32,0x33fd96e1d419fec870ea,0xebf593805877eae3c02c,0xb7d75e01619feca700b0,0xff65f805875faedc02c3,0xf5745c561f7ab22e2b0c,0xf5d1645877ef08b8ac3d,0xd8759161f3ebaac8b0fa,0x65d645875ff0eb22c3af,0x90e1161b7fcbac8b0dbf,0xdb845876faebc22c33fd,0x15d5619fecbf08b0ebf5,0x1755876fb30baac3f759,0x61d61b7fca2ecb0edfa6,0x875867ff28c3ac33ff90,0x91719feca70eb0cff643,0x45c79faecb22e3dbd745,0x164affca2ecb8d7f65d6,0x59377ae9c02c93fd91e0,0x64d7ebb700b26df5d780,0x927fb21c0ac93fd97e01,0x4dbebaf02b26ef5d3815,0x27fb2fc0ac9afd76e056,0xdbecc2eab27cf6517559,0xdff20bb2c9b7e985d564,0xfbc8b0eb25bfe4576592,0xe922c3ac93ff9061d64b,0xfc8b0eb26fde45875937,0xb23c3ac93fd90e1d649f],#[0xc2300baddfe45805d67f,0x28c02ebb7f8460175dbe,0xb300baf5f5d9805d6eff,0x3c02ebd7f9760175bbfc,0x700baedf613805d6efb2,0xc02ebd7d76e0175bbeca,0x2baddfe41815d6efb2d,0xaebb7f8460575dbec23,0x2baf5f5d9815d6eff28c,0xaebb7f8660575dbec330,0xbaddf643815d6eff2cc0,0xeb77d94e0575dbec2702,0xaedf61b815d7afaedc0a,0xb77f9061175bbecb702b,0xf5f5d9845d6eff22c22e,0xd7f9761175bbfcb308ba,0xdf647845d6efb21c22eb,0x7d96e1175ebebb708bad,0xf645765d7afb20bb2eb7,0xf9061975ebeca2ecbaf5,0xe49865d6eff22c32eb77,0x90e1975bbfca30cbafdb,0x53865d6efb23c32eb77d,0x4e01769fec8f00bb5df6,0x3815da7fb21c0aed3fd9,0xe1176bfbc8b08bb4ff65,0x604427fb23c22ed3fd90,0xc110ffccbac0887fe651,0x5443efb2cbaa21ff9965,0x140ffcb0ae0a07dfe597,0x503feae2b0a81ff9965c,0x40fbebaac2a07ef5d161],#[0x37fb0eb0a81efd76585,0xbfecbac2a06ffe1d615,0x3bfaecb8a817ff975854,0xfbfc8aeaa07df6457550,0xeff2cbaa81f7d965d540,0xfecc2eca05ffe4576503,0xf282b82c1bfe985d940d,0xcc8ae0b07fe60570583f,0x328b82c1ff9845c160ff,0xba282b07fd5c541583ff,0xeca0ac1f7d7550560fde,0x3a82b06ff61d41583dfa,0xea0ac17fd9750560dffc,0x282b05ff66141582fff2,0xb8ac1ff5815c560bffcc,0x2b05ff66171583bfae8,0xac1bfd8460560f7eb23,0x2b07df5d581582fff28c,0xac1bfd8760560f7ebb30,0xb07bf61d64582fff2ec0,0xc17fd985d160fdec22e8,0x7df5d584582fff22c22,0x1bfd8761160f7ebb308b,0x7dfe4575582fff2ec22c,0xefd915d960fbfca2eab0,0xffe4587583dfb28bb2c1,0xfd9161d60bffca30eb05,0xf651875837ff22c3ac1b,0xd7458570dffca30eb06f,0x661615c37ff08b0ae1df,0x8660570bffcc2c2b85ff,0x19845c3bfb0cba2e1bfd],#[0x5d541bffc8b0cb86ff6,0x975507eff20baa83f7d9,0x5d561fbfcb2eaa0fdf65,0x75587eff20baac3f7d90,0xd961fbfca2eab0fdf651,0x5593bfb20bb2e3efd905,0x964fbfc82eab27df6417,0x5d7eff22c02ebefd905d,0x75fbfc8b0cbafdfe5180,0xdb7fb02c02edf7f94619,0xbffca300bb6ff611805,0x3ffb22c3ac1ffd875056,0xffeca30eb07ffe458758,0xffb22c32e1fff9461d60,0xfeca300bb7ffe45865c3,0x700570001fff9460176f,0x9600fc01a1029403cc05,0x7740dd419c82f4053a0,0x2852e09f612d822f8408,0xb5434806540c3017282c,0x10021ef03c007440e101,0x209361218234044a084f,0xbbc5550a5c142e27484c,0x18002f345c88b5516442,0x10d7d1a9434146528c45,0xb4c7500e6d1c6237f86e,0x20463f787cc8f541e303,0xa1161224a43808569068,0xb24946925a244e47648c,0x28444f509c3134a260a4,0xb15a82ab45454a63948b,0xcd0b7c16aa2cdc58c8af],#[0x31086120bfd17b52ee05,0x819d4331e6504c8298d2,0xcf0d7b9abb35106930d0,0x393c7164e059ba236de6,0x29e093b9a75fce9d1cec,0xde8f9a9f023d7a7a28f2,0x417081850129fe93f5a7,0xda1ff43aa85f909ca0fd,0xd9d19122e6455489b911,0x494a91a521223df47588,0x1a5fe4b4e956528ea4e1,0xf253c2273f4e069a8d32,0x5268a32d4432853501c9,0xbaa69545aa7a14daa970,0xf55f32b8f5694abf155,0x5b74b56968f2ce25916b,0xe2f405e1abb45738ae23,0x2c583ab0305fd6bebd7b,0x63ccc6858ae312061c8c,0x9333f6618cb1d9413234,0x1e9a1f340b67b0ce959b,0x6ba6d6a5ab2351f697ed,0x236f66d86da1db25b60f,0x1c1c1a37ef6f78de01ba,0x7380e611c9b38e87158e,0x8bafe7584e9f5d253a05,0x205e0c3be57752edb5d9,0x7ba2f655eacbd1d79c2f,0xa3f0f7d82fa15f293e0d,0x24a026c0117f86fe1dfa,0x83d7069a0b0c12581af0,0x8c383868f0b9e13f4227],#[0x51628044a088a510121e,0x8cd1188e2f3c5b48b151,0x847948ec31cde370469b,0x482464c896909120563e,0x94e128424eec9aa92dd2,0xb4bff973f2d6a58acab5,0x7966cbcd5299e532b662,0x9efb3cbe770ce8a9c553,0xdd0dfa13541327ff4fb9,0xaaa920d1d8a327455e88,0xa91550ce9ee5385a66f4,0x85622ab4f55aea9354e1,0xfb6bcfd75aae3d5b1eb3,0xb2c36472c6bd889b0775,0xb5abab4fd68e6cfa59af,0x1aae09dbd7b7136d12d7,0xbb9975d6e93dcf4b95f7,0xbdf64be1b7afef3d5e23,0x40b05ee078c0557f4efc,0xc4c9887f0ed618cc2598,0x563f3c75d8da718962c4,0x6b32af6522c9bb928722,0xce2f9b4b342663fcbe39,0xee8b8d0c3a0733ebe789,0x8a74fb69b1d2d9a4c347,0xd717ad1b580eab3d4cba,0xec93d8d3b0935fd6bb5,0x11c0e08e49dab3b42f67,0xa3f0382488c3017e2f19,0x382391c3e0de361307c2,0x5e0704724f18200be170,0x3822a2430c20bc438d8],#[0xc11512c20c71789860bf,0x704aa106389c50ce0f81,0xc85f8b42e261b07c015,0xb93c6e2f102fc0e08607,0x7150245fc5e231b81c10,0x488dc603f0f85c0e0894,0xb81c11e8e02e370f81c1,0x384703823d2386150570,0x1781c11e8e490c8612bc,0xc2a3f03824f0c33420c6,0xf0382121c380ce1e1b0b,0x1c0e08a8402f181c181a,0x971467c461f038219243,0x8bc4e186781c10c0e2a0,0x8c4278bc4a361f822723,0x8e8681f0b81c1450ac6,0x803de08e870e71b85c0e,0x2703822b180a308230b,0x50ac60270b802be08e86,0x804be0898681f0b81c14,0xe301385c0e08e871470b,0xe1e10e370b81c118101c,0x60a40f85c062f04663c7,0xe08e4681f0b81c1450ac,0x381c1158c040b05381c2,0x8616138a391570382332,0x1f09c51c85385c0e08cc,0x4663a1607c2e0705142b,0xe08cc8c27144dc2e070,0x382331c29c5c20e785c,0xc0e08bc662e107214e17,0x3178c31e170382391785],#[0x38231178c07e1703823,0x47c207381c11e8b47e17,0x107950303b1b85c0e08c,0x424e289a2f476370b81c,0xe2861f846370b81c10b9,0x7c207f038221178e2f0,0x233178fc2e0704343316,0x57068a21183703617038,0xdc2e07044c331785c00,0x233178bc2e012f82210d,0x382f81c1130ac5e17038,0xac6c1b1785c0e0c2842,0x7c0e08ac7a383f81c112,0x1703830a0f8e0fc1f086,0x85c007f0614211f06c6e,0xa2f0a8dc0c1f0446389b,0x88b84e17028d83e08907,0x85c0e088c702f0382261,0xc192f81c1198d46a2e0f,0x884702f038226158bc2,0x81c1199145a3e0f85c0e,0xe08a06628398418a2e0f,0xe8dc2e070446281785c0,0x81c1188c2461703830f1,0xe1703821f120ec6c1f0b,0x1083e0704622a198f83,0x80c10854c6c1f03823d2,0x2c31426360f81c1150c4,0x18a1714554763703828f,0x21707c0e088862329848,0xe2442d1f0983e0704444,0x31238546a3f0307c10f8],#[0x87c8236100f83e170382,0xe241a8c05a3e0f85c0e0,0x170382311b07c2e07043,0x85c0c1f0442241b0746e,0x28998fc2e003f822123,0x288468570b81c110c3c6,0x810ae087c7e170215c16,0xe151f81c10f8e05e1087,0x707c2a3f038221201b83,0x806f0b8147e08a060681,0x140a266370b800fe088c,0x2fc1158dc2e00cb8230,0x76370b81c1179010e170,0x8d8dc2e07046438ac460,0x60e02b85c0e08e86158,0x1880cc6e131f81c10807,0xb81c1108c05610c381c,0xc383e0f85c0e08704637,0xe08e856360f85c0e0c2,0x2d07c0e08c0542b1b85c,0x42e260c48c615703823d,0x31b07c01570460406321,0x1421531b81c11d0e18a1,0x1a130b83a3f038222203,0x4684a3e1707c0e088881,0x841180f83e170382301c,0x18d460251f07c2e07043,0x81c1180d83e1703821c1,0xe17028dc1118f46c1f0b,0xe0f46e1703823a170785,0x823a141983e151f81c10,0xe17038347108ec6e1703],#[0x88dc2e00438230170785,0x2fc1158c0ae105381c11,0xa70385c11c8c14e1700,0x8283d1cf0b81c1259216,0xb11e1b85c0e08bc70be1,0x178e83c370385c1328c2,0x3824a250c14e170289c1,0x6188814c1f143239e170,0xf85c0e087c483703822,0x38231180fc0e08c4542e,0x3e170382311815c20a70,0x1e0dc2e070496261a898,0x4723c198583e00ab8239,0x2e08e450c8528bc0e170,0xf85c025f044c385381c,0xc40b0af81c2e08bc7830,0x150d86e1703821c118d,0x5381c1180c07a2f03823,0x45c1f0b81c1180c4be10,0x8cd0dc4e2d1f81c11511,0xe09e220f8b47e0704544,0x50642fc4e2f03822a1c5,0x47c5e261b0747e07041c,0xe251f0d83e07041c5090,0x385c00cf044c309047c5,0x76260f85c0a3f043e384,0xf8ec5c1f0a8fc0e0870,0xf821c1f0786e17028fc1,0x12f045e2e1b07c2e051,0xd05c6e07044a2f1f85c,0x46e288f062ae0704725c,0x51385c0e08bc60c55585],#[0xb450571985c0e08e47e3,0xc0e087c702f038226158,0xf0b81c1158c0dc1e1f85,0xc45e17004dc1179183c3,0x151b8183c3f0438385a8,0x30821560e8dc0e08e48e,0x84b0817c61970382391c,0x68ac40660f0fc2e07043,0xd6361f8945e1703823d2,0x1d8a8324703823915100,0xc6e2b1307c0e08e4304c,0x9182683e070454391885,0x38217298cc5e0063823,0x1b2c32c6a17138a2f157,0xf1724a0f8bc46370780,0x8bf178818e07045440be,0x30746e17030fc10614c6,0x3e1703828b0e0c0d02b1,0x108bc6e1703821a128b8,0xb81c1128cc50570b81c1,0x5e3f098dc0857045e370,0xe08bc71130a8dc0c2704,0x3828a0d0c192370b8184,0x6e17038211178bc2a370,0x178ac6e170309c105868,0xb81c18586870270b81c1,0x2e1f038225198ec6c270,0x8318463703822f210c4,0x85c251f8022e086c8075,0x9180f84e1703822f1c41,0xbc5a351f09c2e0704343,0xc0e088c582f0b81c1160],#[0x3140bc2e070442251785,0xb81c1118b05e1703822,0x382391a87c2e07047c2f,0x2e050f82241c0bc2e00b,0xa98fc0e08e62a561b09c,0xc2e070468386185c5a18,0x8e785c0e08d071309287,0x47c3703821f1c8805a1,0xc0e08543e307c17c2e07,0x41b85c0e092c4c370a8f,0x7c722c1185c018f04723,0xc3e17038231200bc0e08,0x70b804be089868e4582b,0xbc51670b808ae08ac683,0xc0e0c545e3e1b81c10f8,0xf082bc0e08bc60c03985,0xa86c370b81c11207c605,0xc1e006c80421b81c1188,0x707801b204885c261a8f,0x19e08986122168f84c3,0x18e785c0e08d0708f0b8,0x8b84e17028fc10d0e056,0xfc10d0fc20af03823115,0x22b82261b0d84e17028,0xc19e17038239168dc2e,0x5c1130d46e122b81c113,0x3703821a118dc2a37021,0xc58b0b703828b130bc2c,0x1186185c41531e87c0e0,0xd32c7a1f0b81c10b152b,0x7e105b81c1130c23e20a,0x130cc3c370b81c1180cc],#[0x383161c8cc70b7038223,0x7e17038230198c236170,0x158f86e1703821c118ec,0x3821b180c86e0704602a,0x7c2e1b81c10d9084c370,0x1433c2e07045e388d094,0xa2c3617801fe08e450fe,0x7e070434442f85c0e086,0x13830b0d0c0c0261b854,0xc4e1703830b0d0fc2e03,0x330dc2a3f03821c1e2c,0xd860230f842be0704484,0xc1198e0ce17028fc1160,0x50f82221f04c418d0f81,0x22e07047230c70ec5e0,0x17198b43e0704604860a,0x8bc4a1f0382222e300ec,0xe07044450cc24874c91b,0x84430904612e2f128787,0xe088c5440606bc0e084,0x31c1150a240c11511c,0x132210f81c1120a8862f,0xa678bc40c707802a2046,0x3c5e231b83c00c06caa1,0x2c2381c11c8a871208c1,0xec51170211c10d8f872,0x1c1178f45e0704723d13,0x38208dc0e08a87a360b8,0x8a851861e10c6e070436,0xfc084704543d138018e0,0x2d1381c11c8609121170,0x8bc0e08f47220ed87c6e],#[0x18e08f46c1703822f1e,0xaa2437c1e00f47a250f8,0x8a882186381c11e8a182,0x639144613225170fc0e0,0x2f03823d151382e07046,0x81c11e8a8809a1e8846a,0xe0704401b182644a2e1f,0xc8a46e00638239143022,0x83c01e860ac170382331,0x1c8607a250e0545630e7,0xb81c10c943f630f783c0,0x11e8e1761e0b8bc4198a,0x3823d1f040ae18d381c,0xc0c3f0436531017c3c17,0x7046248904609e2f128d,0x21d26300ec13138746e0,0x78f09207178987a306f8,0x30222b04c51851b81c11,0x1c48230971788c3e0704,0x5440908a88e0704462a,0x10f8e230991031c0e089,0x1f820d2b0d87e170287c,0x392418c50261a87c2e06,0x100c61e1f8b44e070b82,0x246198b87e170289c10d,0x30c3010f0e17c2e07063,0x81c10e0f86e17030fc11,0xe17045639201986c3f0b,0x38414e08cc80821509c0,0xe170466391f8b841cf0,0x251fc1e006c7a361029c,0x472323c85c0e08a87a31],#[0xe1704723b1b85c0e08c,0xb0bc0e0928b630530bc,0xc1459655868541983a37,0x210c080368d83e151381,0xc1c430b44e00a98fc13d,0x74430930588688e2b46,0x10e12592a91b85c0e08c,0x4090a8328d83e122f81c,0x48541946e131e89c0e0a,0x200da360f85c0257043e,0x6e0f84c7c2f03825524,0xe09c2e0704602b1d0e10,0x7431204890e0704622a1,0xe0f00366d0b8030e08f4,0x9024b1121841231a8e3d,0x612843de0704b02a2031,0xac4c1f0b81c12c87c963,0x960f85c02cf046048401,0x4859e1703823a1866841,0xa408629c0e1704ca2f1c,0xc90394a91c29c0e17047,0x7244501ec5e070b82331,0x1c90102385b81c2e0850,0x45e38418b14e070b8232,0x10d19472399781c2e088,0x3826517904719f0385c,0xc2e09945e391d849819f,0xf0385c1328bc74a0cf81,0x3c019f0b8294178e9419,0x2f1843c0e17043465182,0x705282f2067c0e1704a2,0x5c14a1947160a289c0e1],#[0x1253824a1590210d7038,0x85c0e08ac4c30541fc0e,0x22f03844ae0a5056492b,0x48bc2e070456391c7234,0x52291381c2e08ac72385,0x63f0454470385c1158bc,0xb82141993448af1473c0,0x2e08cc90a91f8a39e070,0x628491c2944e28e781c,0x391e2a21e28e781c263f,0x92c4c40668bc0e105382,0x24b1312160861b81c2e0,0x30cc51e8c88986e070b8,0x21c0e08a872370385c11,0x8811f81c20a704724c5a,0xc2945e070b8239213216,0x60870385c18a0e474c91,0x1189c51cf038258150e1,0xb81c1198d0ae07045439,0x1178f480ac5189c51cf0,0x6282b1c2d146270b81c,0x47e0c504c3b1381c2a3f,0x8e781c2e08cca62f0b81,0x1c2e08cc88a31468c4e2,0x70b82392629c51cb138,0x85c11c8f14620f464c5e,0xe070462391e331462f03,0xb85c0e0a5c384d188bc2,0x2e025f8231242a0c62d1,0xabc11c8c2f228d28dc,0x45e070b82331c8e23e17,0x92033c0e142f82391929],#[0xc474ca5217c0e1704643,0x251790c4a370b81c18b8,0x9605e3c1cb0c61af0383,0x3c0928cc86310b81c192,0x494b0331e0e58619278,0x8e39e070444630c85c1e,0x151018cab152b8511b0e,0x543b0f0b421cf078058,0x1188e471008d2bc0e08c,0xb81c11992952c61b81c,0xc1850cc7618518a39c27,0x70382221c8ac51cf0b81,0xe474b10b81c1150e464b,0xc1110e140ce1785c0e08,0x7044439178b87a1f0073,0x10922707801b1e8c45e0,0x44278987a30f783c00d9,0x8f14a28e785c0e08cc68,0x2301e28c4e1703822f1e,0x98bcca231687c2e07063,0x6c218a3147234250e941,0x83d1912c78bc51883310,0x4466282f6288370d4518,0x88381788e28c56245c68,0x8c56246464445e28c419,0x46628c517883c198922]]
def g255H10 := limbs80 #[#[0x8280094004842a10882,0x49803784911002008006,0x9c6008e402a5a0002e7,0x9ac73cd440108550048,0xc36000b63800280d0cd0,0x924937f0f6000d03d991,0xc001caa085fc1e10c000,0x2c6080280000c3e6da93,0xdc000ae02354b44000e1,0x5600029a244a83826301,0xc7f15f42500004,0xf528000001c2c0000,0x133401a000053a2cc000,0x800000000000f4000000,0xf8002146000d2a5b9415,0x746c500018d847a000c1,0x82039c45bcd714614288,0x1a28975c8ed1a60003,0x6443c2505fc914871024,0xf8e4000000000353d102,0x8d080000000000b313b8,0x4d1d487e00000000008f,0x64c44605c8071a4802,0x31882cc852445e5fe0,0x905110216ed6ca613260,0x1120daaaf51710b73038,0x866000792edb448ae40,0x302c000822000000000,0x1034387d1a400026000,0xd5bc9740,0xd64000b58e3f3d9fc8f0,0x25e4000c7d8002],#[0x3233f16e5d2288001081,0x15c00021b3e1e000000,0x80a66c000142000000,0xa762c1ae1b60240980,0x8931070bc67780000000,0x43c8770000001503c742,0xf1640018c007d000183f,0x6c6730d5b2962beb025f,0xa0af7d2bc19f500208ca,0x5c4b40000277591e23c3,0x5bde40ce3396f1bf6c,0xae90007c064ec6ed0,0x937a0d4cc72bb000626c,0x612f6d2008ea1c000000,0x58558002c8c00073cb38,0x28e7489e4,0x54d403c00146572928,0x1863c9c00068991160,0x2b5c78195f094d1400a0,0x13f96184c99200350000,0x1c0812f7154624e43000,0x5b0800002913983cc00,0xb000060be03351c00000,0x40af41c45a00000001,0xc9b51326800000000000,0x350a000b212298,0x2d420000002860000000,0xde448002197a1da67000,0x184e00033c54098d,0x10738310400149200000,0x3c4e000f735bd80011,0x101e940000421f568],#[0x3d7386b0001004000,0xc06e24c927c001e5c000,0x4a340010a800029f5da,0x65f67cf1e148e00000,0x88a3d0000aafe2c10580,0x65e7c18042ba0ea0371,0x70f8001e84136a8ab,0xad52000a0a80c20a2000,0x5a5]]
set_option maxRecDepth 16000 in
def g255D11 := limbs80 #[#[0x50110d7d765d75f5d570,0x443fe5c110ff960443fe,0xbfd84443fd5c510ff541,0x61910f7d75442ffe1110,0x442ff61d10bff86442ff,0xbff81503fe5c140bff87,0x61940f7d75503ef5d140,0x502ff61d40bff86502ff,0xbff81583fe5c160bff87,0x5d560bff84583bf59160,0x582ff61d60efd76583df,0xdfd745c2ffe0570bff87,0xe0141bff865c2ffe1170,0x507ef59141ff571506ff,0xbfd86507df5d541fbd74,0xe1d41bfd87506ffe1941,0x587fd5c561bff80586ff,0xf7d75586ffe1161efd64,0xe1d61bfd87587bf5d961,0x5937f5d971dfd745c6ff,0xfbd74592ffe0564bff80,0x61d64efd76593df5d564,0x5d7df60175bff87592ff,0xf7f815d7df60575f7f80,0x61975f7f845d7df61175,0x5daffe0176f7f865d7df,0xffd64442ffe1176bff81,0x5d910ffd84443ff5d110,0x503ff61d10ffd86443ff,0xffd81503ff5c540ffd61,0x61d40ffd86503ff5d940,0x583ff5c560ffd41583ff],#[0xffd84583ff5d160ffd81,0x58570ffd415c3ff61d60,0x5c3ff59170ffd815c3ff,0xffd80507ff61970ffd84,0x60161ffd86507ff5d941,0x587ff61161ffd74587ff,0xffd80593ff59171ffd87,0x60176ffd87593ff60564,0x3ff61176ffd815dbff,0xf01a605000f2027004e0,0x3b20d302ee0aa024207,0x57614a04e2125044e0fe,0x6a1c706de1a0063a1750,0xe238089220f07f61ec07,0x2a30a4628209c225f093,0x100bda2e50b562c00ac2,0x50d7e34c0cea32b0c763,0xf623c90ec639e0e1a37,0x11642e107240b0fe63e8,0xfa4a9125e48211c245b1,0x6520143a4f9139e4d012,0x58715ce564154a54114c,0x417c25dd16fe5ac1662,0x719c665c190262f18766,0x1bba6d51b166b21a7268,0xd7674e1cf27271c4e702,0x2a7bb1ea67961e0a7711,0x982e206a8051fc67de1f,0x241d085f1b1713020f04,0x4a078219c5c4c3c046c1,0x718703c4116130b0304f,0xc0f85144684c0c2c13d2],#[0x3f140f1a111f0b0304e4,0x4c2c045c18333288c5c,0xa0f0b0304ac288110f46,0x6844583c2c0c133303d1,0xb00f7043c811100f070,0x844783c0c1392c1b1d17,0xb0b0304c4c421823c5c6,0x10f2054503c1c16120d1,0xaf0428a26c7c546c2c0c,0xc10f205c3c18160f0b00,0xb0304e4926c6c547c2c0,0x33c1102217185c411f0,0xf0b03042c9070644c2c,0x858347c0c12f1b103442,0xb0304c0c42182490c6c4,0x205850401c12151a0f0,0x42cb07043a46c2c0c11,0x1cc85c40131a0c730b03,0xb051c9c6c447c2c0c110,0x13114205c5313161b030,0x170b04e48070544c2c0c,0xc2c0c130142058520f01,0x61a0f011f04a8a070445,0x583c0c2c147250863131,0x1e1a0f030b04b1914c4c,0xc0c2c1141c645c531711,0x5130b0304ac5c8c5c447,0x7c68339c2c0c10b20181,0x17231b13091703045c71,0x3049462fc5c446c2c0c1,0x7c3c2c0c1251c190f0b0,0x160f0b011b0610bcac60],#[0xc607c3c2c0c1251c5844,0xf30601d0b1b0f0304948,0x5110785034684c2c0c12,0x25180d1b0b0304946161,0xf030b04447c6c3c2c0c1,0x53e43c2c0c115231b0d1,0xc30561b0b0304289070,0x16158445c2c0c1392b17,0xd140f0b0304bc548c31f,0x395c5c3848647c0c12c1,0x64551f0b0304f4942182,0xc3861fc2c0c10a2e130c,0xd1f0b030454734191505,0x8c6c3c2c0c10b0a1f170,0x1620670d18f70b030428,0x4e45882bc7c443c2c0c1,0x26c10b200f1d130b030,0x1e1b0304e4b164386c2c,0xc0c139290862130cf615,0x3042ca3dc316194785c2,0x1162064580c121b089b0,0xf0304a2bc4c347c2c0c,0xc1182209186317121c89,0x30304f4a02c6c5c443c0,0x13d182119150c621ca82,0xab0304e4b4645c344c0c,0x3918220919110c621d14,0xd1b0700a4443c645c0c1,0xc118210c246317121c6,0xb030464802c5c4c346c,0xc244c0c1191ccf17110f,0x4100f0b030498648c3c5],#[0x74683160fc0c12b39211,0xf2325143c2f030498f4,0x304f48111045c221c0c1,0xfc10f232465183e0f0b0,0x2b043c7c9151446c2c01,0x1fc0c11c385d17088700,0x55108544c715904683c2,0x4c11043182b0b0304e89,0xc11100f44c2c0c124282,0x10411d18920f0b0304f4,0x14c21cc0c11024206643,0x45c402f0b030470c8816,0x4c7838644c0c2c11a513,0x1a0f030b0528a9411451,0xc0c2c13d14291050e716,0xf030b052ca441547450f,0x2c139142914521b10f60,0xb045094510474416c0c,0xc1252f1c645f13151f03,0xd1b0b0304e4c8617c2c0,0xc139245d5714561e0c8,0x304e48170f45c60ac2c,0xc2c0c139245e0c591b0b,0xb030b045ca321710c60b,0xc11123206450bf17111,0xb030494cc7100fc221c,0x11c2c046c11a23250c67,0xc53087f0304548c81615,0x14515c30bc2c0c13e243,0x585445170b03048cb093,0x4719150ac2c0c11f3420,0x116242610582b0304ace],#[0x458909141043c2c01cc,0xc1161c24544513086b03,0xb030464a1944c21a0bc0,0xc13d245c5314cf110f0,0x304f49341915c30ac2c,0x6459130c2f0b]]
set_option maxRecDepth 16000 in
def g255H11 := limbs80 #[#[0x4038481a37030340a15,0x543a0002846000009c4a,0x34043500804380012820,0xd01c8e020c805ea01028,0xb0a8189c120f0f0081f0,0x58f00005d08b000ac0c4,0x808000a8100202c98bc2,0x181d01a0858310280,0x260082ed24f1e9400820,0x771a03c4800018241802,0x14777a9a400fab50044e,0x9524436a582372265810,0x4b7655e6d13e72dc001,0x828905b42e45b0a4e000,0x2b4ef0e1862b6ae2d67,0xc84b859ae24f065a4f00,0x77caff31b17fb360002e,0xc22000000394ee713694,0xd34f48d2b8c03bc472cf,0x9b0173ea819a90da087e,0x4834328163cecee19881,0x491c732f58992a40fa49,0x46eb723c48c6c43643f3,0x550819e9087e208223b2,0x80b5421dab725173799a,0x89b854f438e460bff292,0x800018924dc4ab96f6bd,0x20000001536ea8f36c8c,0xcb183163029362d628,0x7833aa8726e20001a940,0xd8c00023e4ccb6776,0xa7ec1d459f450d2fd5c8],#[0xbec1117dc2141ddc8000,0x661bb30ca9ac9965642,0x58713a61f11610080166,0xcb3b083ad727eaec09ec,0x4ed2e147fc0b34a31ec4,0xe37f2e0bde8154d5c143,0xa3d55f6a5d76bc1ae6fa,0xc51488c48778cf322750,0x1e0529ff47ad5c4e,0x31eaf97344a4662e12d8,0x248e3800097e000005f8,0xa95e9a0002d9625864b4,0x906c3d3054932a352a49,0xc0002a3ca6ed54122cda,0x20005223a18d5d810860,0x7b64a00076fa0b40cc85,0xe13420a5394728a092,0xd78000a99158395eaec0,0xedec4c75e41e40000002,0xb434000f0fdc7f2b5a57,0x9a1478ad9e228a415560,0x5a16c0000000001e5049,0xd6b4c50ca275ddc000b8,0x20dd2f68e6dda215e436,0xd9bc5135f7dde322b402,0x3014975a01f834b66,0xf5c2b1c7b8c025611efe,0x3a1b2a05c1f96c524581,0x5b1da16370d04ffa322f,0x2cb224cea6b6742423e1,0xcc3c56000ba7c61690ac,0x87b1a83bb199040452f2],#[0x6c91d8a279111e2f191d,0x4b05a5d9e2b5a93626be,0xcd56287b120a39cba155,0x9b701513fa0e44a69512,0x4bea98439b566541d654,0xe5ce74b5a839d0758e0b,0xe1a52026694a2b563ba7,0x24e753c1fe009e73948,0xe8885e0427b21e3bd189,0xd5a34000cb319605a310,0x6751f23720600bd73d58,0x31a11443182579bfebf7,0xd26f1e431f7054f86bac,0xd07d68ce0800000bbc36,0x88106b419c111bec2188,0x8ddd09f444578fb53916,0x1d778d625968ab5ee553,0x55b50c876b09b590d138,0x317aa2e053d21c]]
def g255D12 := limbs80 #[#[0xffac1ff503fe8877d75,0x64ffae3ff587fea0ffd7,0x1061f001ff5dbfeba7fd,0x53b2fc34ee32ea921a64,0x20920a345890c3c0824,0x70a041247c78b1820385,0xd001c2824908f1a2050,0x5881c1c085049291e245,0xc6861424281052925e34,0x4158f161840d0a041243,0x50209212345870a04114,0x850208b20b47890c3058,0x4861c342810490b1a243,0x662c]]
def g255H12 := limbs80 #[#[0x8f002003b1c182047084,0x29dc31d400010c0032,0x1d5fa5d049e79e12c,0x65486a01d000e0b85c00,0x3e47901a6002c575,0x1e23ba82c000000,0x68f91bac2001a5000c04,0x52911e2ca0c000000b4,0xdecb600000033c8e0000,0x5c00071b0191800051d,0xb80c2268768001d54ec,0x15800054e41ad680000,0x1edd0b1a0000063c0000,0x63947e300006e4eb264f,0xc001534cd000f6a82400,0x4dd062e5225100012a22,0x10ca4c0e0000006f8003,0xddb21df01d9b0c8b1c8d,0xa52b22d097abc44000ae,0xda17ccbe72c91f991140,0xfaa0036c4a100153b038,0x7d0b5c5d226f19e8a800,0x10724956b50]]
def g255D13 (j : Nat) := if j=0 then 0x7185103080048ff else 0
def g255H13 := limbs80 #[#[0x6db57491fc540030da87,0x61536]]
def g255L : Nat → Packing
  | 6 => (1,7,6,0,0,0,0,g255D6)
  | 7 => (16,6,6,0,0,7,0,g255D7)
  | 8 => (85,5,6,0,0,12,0,g255D8)
  | 9 => (282,4,6,0,0,15,0,g255D9)
  | 10 => (405,3,6,0,0,15,0,g255D10)
  | 11 => (109,2,6,0,0,14,0,g255D11)
  | 12 => (11,1,6,0,0,10,0,g255D12)
  | 13 => (1,0,6,0,0,0,0,g255D13)
  | _ => emptyPacking
def g255I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 1 2 0 4 0 0 g255H7
  | 8 => lookupWord 4 23 3 8 4 0 g255H8
  | 9 => lookupWord 21 127 5 11 7 0 g255H9
  | 10 => lookupWord 70 419 5 13 9 0 g255H10
  | 11 => lookupWord 101 439 9 13 9 0 g255H11
  | 12 => lookupWord 27 149 6 11 7 0 g255H12
  | 13 => lookupWord 2 13 3 8 4 0 g255H13
  | _ => fun _ => none
def g255 : Forest := ⟨255,13,fun i => g255Y[i]?.getD (0,0),g255C,g255A,g255L,g255I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P6_0 : block g255 6 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B6 : block g255 6 0 1=true := g255P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P7_0 : block g255 7 0 16=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B7 : block g255 7 0 16=true := g255P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_0 : block g255 8 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_1 : block g255 8 1 21=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_22 : block g255 8 22 63=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B8 : block g255 8 0 85=true := (@block_merge g255 8 0 1 84 g255P8_0 (@block_merge g255 8 1 21 63 g255P8_1 g255P8_22))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_0 : block g255 9 0 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_96 : block g255 9 96 11=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_107 : block g255 9 107 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_203 : block g255 9 203 41=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_244 : block g255 9 244 38=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B9 : block g255 9 0 282=true := (@block_merge g255 9 0 107 175 (@block_merge g255 9 0 96 11 g255P9_0 g255P9_96) (@block_merge g255 9 107 96 79 g255P9_107 (@block_merge g255 9 203 41 38 g255P9_203 g255P9_244)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_0 : block g255 10 0 20=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_20 : block g255 10 20 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_116 : block g255 10 116 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_212 : block g255 10 212 90=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_302 : block g255 10 302 94=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_396 : block g255 10 396 9=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B10 : block g255 10 0 405=true := (@block_merge g255 10 0 212 193 (@block_merge g255 10 0 20 192 g255P10_0 (@block_merge g255 10 20 96 96 g255P10_20 g255P10_116)) (@block_merge g255 10 212 90 103 g255P10_212 (@block_merge g255 10 302 94 9 g255P10_302 g255P10_396)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_0 : block g255 11 0 2=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_2 : block g255 11 2 69=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_71 : block g255 11 71 38=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B11 : block g255 11 0 109=true := (@block_merge g255 11 0 2 107 g255P11_0 (@block_merge g255 11 2 69 38 g255P11_2 g255P11_71))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P12_0 : block g255 12 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P12_1 : block g255 12 1 10=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B12 : block g255 12 0 11=true := (@block_merge g255 12 0 1 10 g255P12_0 g255P12_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P13_0 : block g255 13 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B13 : block g255 13 0 1=true := g255P13_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255T : checkedTables g255 13 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g255 0 0 0 = true)
  · exact (rfl : block g255 1 0 0 = true)
  · exact (rfl : block g255 2 0 0 = true)
  · exact (rfl : block g255 3 0 0 = true)
  · exact (rfl : block g255 4 0 0 = true)
  · exact (rfl : block g255 5 0 0 = true)
  · exact g255B6
  · exact g255B7
  · exact g255B8
  · exact g255B9
  · exact g255B10
  · exact g255B11
  · exact g255B12
  · exact g255B13
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255G : graphValid g255 (boundsBefore K254) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255R : Impossible true graph 13 sevenInputs.toFinset := by
  rw [show graph = targetOf g255 by decide +kernel]
  exact root_index (g:=g255) (top:=13) (i:=0) (before_sound K254 V254) g255G g255T (by decide) (by decide +kernel)

end PEqualNP.Outside.L_meta_32506

open PEqualNP.Outside.L_meta_32506 in
theorem PEqualNP.Outside.L_meta_32506 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o fit _ correct
  exact replaceShort g255R gates o fit correct

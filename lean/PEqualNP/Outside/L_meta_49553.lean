import PEqualNP.Defs

-- The two-mode live-state and cofactor checker follows L_meta_1674 and L_meta_670.
-- The graph, restrictions and all search certificates below are for L_meta_49553.

-- Shared forest and cofactor certificates from L_meta_1674 and PR 11111 for L_meta_1677.
-- The original credit line is retained below. The two root certificates here cover the unpinned graph.

-- The checker and the bound certificates are adapted from PEqualNP/Outside/L_meta_1667.lean (Apache-2.0).
-- Two modes: u=false are monotone runs (AND, OR); u=true are runs up to complement, where negation is free.
namespace PEqualNP.Outside.L_meta_49553
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
def graph : Sig := (BitVec.ofNat 512 (word80 [0xffffffff,0xffffffffffffffffffff,0xfffefffffffffffefffa,0xfefefefeeeccaa00ffff,0xffffffffffffffffffff,0xfffffffefffffffffffe,0xfffafefefefeeeccaa00]))
def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 3) || (x 1 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 2 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 5 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 2 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 5 && x 7) || (x 6 && x 7)
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
  (x 0 &&& x 3) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 2 &&& x 5) ||| (x 0 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 5 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 2 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)
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
  (x 0 &&& x 3) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 2 &&& x 5) ||| (x 0 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 5 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 2 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)
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



def target (x : Fin 8 → Bool) : Bool := decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
def smallCircuit : Circuit := ⟨[⟨.or,[5,7]⟩,⟨.or,[0,2]⟩,⟨.or,[1,3]⟩,⟨.or,[4,5]⟩,⟨.or,[0,6]⟩,⟨.or,[1,7]⟩,⟨.or,[3,8]⟩,⟨.or,[6,8]⟩,⟨.and,[13,11]⟩,⟨.and,[14,12]⟩,⟨.and,[15,9]⟩,⟨.and,[7,10]⟩,⟨.or,[16,17]⟩,⟨.or,[20,18]⟩,⟨.or,[21,19]⟩], 22⟩

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

def lowRow (i : Fin 8) : Row := Fin.ofNat 512 (1 <<< ([3, 4, 5, 0, 1, 0, 0, 0] : List Nat).getD i.val 0)
def highRow (i : Fin 8) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< ([3, 4, 5, 0, 1, 0, 0, 0] : List Nat).getD i.val 0))

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
def g73Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3ff63ff63ff63ff63f,0xf63ff63ff63ff63ff63f])),(BitVec.ofNat 152 (word80 [0x492049204920492049,0x20492049204920492049]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xc7fbc7fbc7fbc7fbc7,0xfbc7fbc7fbc7fbc7fbc7])),(BitVec.ofNat 152 (word80 [0x924092409240924092,0x40924092409240924092]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xf8fdf8fdf8fdf8fdf8,0xfdf8fdf8fdf8fdf8fdf8])),(BitVec.ofNat 152 (word80 [0x248124812481248124,0x81248124812481248124]))),(0x0,0x0),(0x0,0x0)]
def g73C : List ColumnInfo := []
def g73A : List (List Nat) := [[],[99],[48],[48,96],[96,48],[96]]
def g73D3 (j : Nat) := if j=0 then 0x7 else 0
def g73L : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,g73D3)
  | _ => emptyPacking
def g73I (_ _ : Nat) : Option (Nat × Nat) := none
def g73 : Forest := ⟨73,3,fun i => g73Y[i]?.getD (0,0),g73C,g73A,g73L,g73I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g73P3_0 : block g73 3 0 1=true := by
  apply cellsBlock (ar:=3) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g73B3 : block g73 3 0 1=true := g73P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g73T : checkedTables g73 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g73 0 0 0 = true)
  · exact (rfl : block g73 1 0 0 = true)
  · exact (rfl : block g73 2 0 0 = true)
  · exact g73B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g73G : graphValid g73 (boundsBefore []) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low73 : Lower true (varsX 73) (graphGoal 73) 4 := lower_forest (g:=g73) (i:=0) (hints:=3) (before_sound [] baseKnown) g73G g73T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K73 := extendKnown [] 4 [(73,[]),(97,[83,67]),(100,[32,16,83,67]),(137,[118]),(146,[16,67,118]),(161,[83,67,118]),(162,[16,83,67,118]),(193,[99,67,84,117]),(200,[48,16,33,98,66,84,117])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V73 : Known true K73 := extend_ok (m:=73) baseKnown low73 (by decide +kernel)
def g43Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xe6de3fff03fff1ffe6,0xde3fff03fff1ffe6de3f])),(BitVec.ofNat 152 (word80 [0x648490a2850240206,0x48490a28502402064849]))),((BitVec.ofNat 152 (word80 [0x19e9c0fffc07fe3f19,0xe9c0fffc07fe3f19e9c0])),(BitVec.ofNat 152 (word80 [0x50e8db2c3161408450,0xe8db2c3161408450e8db]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xece607fffff8003fec,0xe607fffff8003fece607])),(BitVec.ofNat 152 (word80 [0x8a7b6b04185892808,0xa7b6b04185892808a7b6]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1b3df8ffffffffc01b,0x3df8ffffffffc01b3df8])),(BitVec.ofNat 152 (word80 [0x891524c08206003089,0x1524c082060030891524]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g43C : List ColumnInfo := []
def g43A : List (List Nat) := [[],[80,49]]
def g43D3 (j : Nat) := if j=0 then 0xf else 0
def g43L : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,g43D3)
  | _ => emptyPacking
def g43I (_ _ : Nat) : Option (Nat × Nat) := none
def g43 : Forest := ⟨43,3,fun i => g43Y[i]?.getD (0,0),g43C,g43A,g43L,g43I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g43P3_0 : block g43 3 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g43B3 : block g43 3 0 1=true := g43P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g43T : checkedTables g43 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g43 0 0 0 = true)
  · exact (rfl : block g43 1 0 0 = true)
  · exact (rfl : block g43 2 0 0 = true)
  · exact g43B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g43G : graphValid g43 (boundsBefore K73) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low43 : Lower true (varsX 43) (graphGoal 43) 4 := lower_forest (g:=g43) (i:=0) (hints:=83) (before_sound K73 V73) g43G g43T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K43 := extendKnown K73 4 [(43,[]),(45,[33]),(51,[16,67]),(54,[16,32,67]),(106,[96,32,66]),(114,[80,65,32,99,33])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V43 : Known true K43 := extend_ok (m:=43) V73 low43 (by decide +kernel)
def g77Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfdf00fff81fc7e3ffb,0xe01fff03f8fc7ff7c03f])),(BitVec.ofNat 152 (word80 [0x45c09245142904808b,0x81248a28520901170249]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xe6a8703ffe007fc7cd,0x50e07ffc00ff8f9aa1c0])),(BitVec.ofNat 152 (word80 [0x96a9b6d618b228112d,0x536dac316450225aa6db]))),((BitVec.ofNat 152 (word80 [0xfbb781ffffff8007f7,0x6f03ffffff000feede07])),(BitVec.ofNat 152 (word80 [0x235249820c0312204,0x6a49304180624408d492]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x64ffe3ffffffff80c,0x9ffc7ffffffff0193ff8])),(BitVec.ofNat 152 (word80 [0x249204100400400,0x4924082008008000924]))),(0x0,0x0),(0x0,0x0)]
def g77C : List ColumnInfo := [(4,0,73,0,4)]
def g77A : List (List Nat) := [[],[48]]
def g77D4 (j : Nat) := if j=0 then 0x1f else 0
def g77L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g77D4)
  | _ => emptyPacking
def g77I (_ _ : Nat) : Option (Nat × Nat) := none
def g77 : Forest := ⟨77,4,fun i => g77Y[i]?.getD (0,0),g77C,g77A,g77L,g77I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g77P4_0 : block g77 4 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g77B4 : block g77 4 0 1=true := g77P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g77T : checkedTables g77 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g77 0 0 0 = true)
  · exact (rfl : block g77 1 0 0 = true)
  · exact (rfl : block g77 2 0 0 = true)
  · exact (rfl : block g77 3 0 0 = true)
  · exact g77B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g77G : graphValid g77 (boundsBefore K43) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low77 : Lower true (varsX 77) (graphGoal 77) 5 := lower_forest (g:=g77) (i:=0) (hints:=1539) (before_sound K43 V43) g77G g77T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K77 := extendKnown K43 5 [(77,[]),(99,[33,99,67,84]),(102,[32,16,99,67,84]),(108,[32,16,49,81,65]),(139,[33,118]),(141,[118]),(147,[16,32,67,118]),(153,[66,118]),(154,[16,50,66,118]),(170,[16,50,82,66,118]),(172,[32,16,49,81,65,118]),(177,[66,83,118]),(180,[32,16,65,83,118]),(209,[66,99,83,117]),(210,[16,98,67,50,83,117]),(216,[48,16,66,97,33,82,117])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V77 : Known true K77 := extend_ok (m:=77) V43 low77 (by decide +kernel)
def g101Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfe7d01c7fc0fc7cfe7,0xd01c7fc0fc7cfe7d01c7])),(BitVec.ofNat 152 (word80 [0x51d124928a290a051,0xd124928a290a051d1249]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x3f8b8e38fff007f3f8,0xb8e38fff007f3f8b8e38])),(BitVec.ofNat 152 (word80 [0x884b924930c3210884,0xb924930c3210884b9249]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x3fe7703ffffff803fe,0x7703ffffff803fe7703f])),(BitVec.ofNat 152 (word80 [0x100024924104020100,0x2492410402010002492]))),((BitVec.ofNat 152 (word80 [0xc018ffc0fffffffc01,0x8ffc0fffffffc018ffc0])),(BitVec.ofNat 152 (word80 [0x200049248208040200,0x4924820804020004924]))),(0x0,0x0),(0x0,0x0)]
def g101C : List ColumnInfo := [(1,0,100,0,4)]
def g101A : List (List Nat) := [[],[101],[32],[32,101]]
def g101D4 (j : Nat) := if j=0 then 0x1f else 0
def g101L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g101D4)
  | _ => emptyPacking
def g101I (_ _ : Nat) : Option (Nat × Nat) := none
def g101 : Forest := ⟨101,4,fun i => g101Y[i]?.getD (0,0),g101C,g101A,g101L,g101I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g101P4_0 : block g101 4 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g101B4 : block g101 4 0 1=true := g101P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g101T : checkedTables g101 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g101 0 0 0 = true)
  · exact (rfl : block g101 1 0 0 = true)
  · exact (rfl : block g101 2 0 0 = true)
  · exact (rfl : block g101 3 0 0 = true)
  · exact g101B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g101G : graphValid g101 (boundsBefore K77) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low101 : Lower true (varsX 101) (graphGoal 101) 5 := lower_forest (g:=g101) (i:=0) (hints:=1285) (before_sound K77 V77) g101G g101T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K101 := extendKnown K77 5 [(101,[]),(105,[48,82,32]),(163,[33,118]),(166,[16,118]),(169,[48,82,32,118]),(178,[64,16,82,50,49,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V101 : Known true K101 := extend_ok (m:=101) V77 low101 (by decide +kernel)
def g201Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xdf7ec03c3ffe0fbefd,0x80787ffc1f7dfb00f0ff])),(BitVec.ofNat 152 (word80 [0x820404444444210408,0x8888888420810111111]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1fbf43c3c3fff03f7e,0x878787ffe07efd0f0f0f])),(BitVec.ofNat 152 (word80 [0x40808888888420810,0x11111110841020222222]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xe03fbc03fc3fffc07f,0x7807f87fff80fef00ff0])),(BitVec.ofNat 152 (word80 [0x81011111110841020,0x22222221082040444444]))),((BitVec.ofNat 152 (word80 [0xffc03ffc003fffff80,0x7ff8007fffff00fff000])),(BitVec.ofNat 152 (word80 [0x102022222221082040,0x44444442104080888888]))),(0x0,0x0)]
def g201C : List ColumnInfo := [(1,0,200,0,4),(8,0,193,0,4),(64,0,137,0,4),(128,0,73,0,4)]
def g201A : List (List Nat) := [[],[118],[99],[99,115],[115,99],[115],[48],[48,118],[48,96],[48,96,112],[48,112,96],[48,112],[96,48],[96,48,115],[96],[96,112],[96,115],[96,115,48],[112,48,99],[112,48],[112,96],[112],[112,99,48],[112,99]]
def g201D3 := limbs80 #[#[0x23ea6a1221e12148110,0x8028]]
def g201D4 := limbs80 #[#[0x2fd0910bd42443e48110,0x609085870]]
def g201H4 (j : Nat) := if j=0 then 0x37c0 else 0
def g201D5 (j : Nat) := if j=0 then 0xd1027d10 else 0
def g201H5 := limbs80 #[#[0xb20000000000000000,0xc500580017c8c003cc,0x688016100000]]
def g201D6 (j : Nat) := if j=0 then 0x3904f else 0
def g201H6 := limbs80 #[#[0x280000000,0x8800002c4000000000,0x582880000528]]
def g201L : Nat → Packing
  | 3 => (2,3,2,0,0,5,0,g201D3)
  | 4 => (3,2,2,0,0,5,0,g201D4)
  | 5 => (1,1,2,0,0,0,0,g201D5)
  | 6 => (1,0,2,0,0,0,0,g201D6)
  | _ => emptyPacking
def g201I : Nat → Nat → Option (Nat × Nat)
  | 4 => lookupWord 1 5 0 5 1 0 g201H4
  | 5 => lookupWord 2 23 0 9 2 3 g201H5
  | 6 => lookupWord 1 23 0 9 0 5 g201H6
  | _ => fun _ => none
def g201 : Forest := ⟨201,6,fun i => g201Y[i]?.getD (0,0),g201C,g201A,g201L,g201I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g201P3_0 : block g201 3 0 2=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g201B3 : block g201 3 0 2=true := g201P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g201P4_0 : block g201 4 0 3=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g201B4 : block g201 4 0 3=true := g201P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g201P5_0 : block g201 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g201B5 : block g201 5 0 1=true := g201P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g201P6_0 : block g201 6 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g201B6 : block g201 6 0 1=true := g201P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g201T : checkedTables g201 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g201 0 0 0 = true)
  · exact (rfl : block g201 1 0 0 = true)
  · exact (rfl : block g201 2 0 0 = true)
  · exact g201B3
  · exact g201B4
  · exact g201B5
  · exact g201B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g201G : graphValid g201 (boundsBefore K101) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low201 : Lower true (varsX 201) (graphGoal 201) 7 := lower_forest (g:=g201) (i:=0) (hints:=3) (before_sound K101 V101) g201G g201T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K201 := extendKnown K101 7 [(201,[]),(228,[32,16,83,67])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V201 : Known true K201 := extend_ok (m:=201) V101 low201 (by decide +kernel)
def g47Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xf8003ffe00fff803ff,0xfffffffffffb5d61e03f])),(BitVec.ofNat 152 (word80 [0x501a80941a02905828,0x540940a414940616249]))),((BitVec.ofNat 152 (word80 [0xffffc00000fffffc01,0xffe001ffe008a3d3c1c0])),(BitVec.ofNat 152 (word80 [0x61530ad8ac2b22914c,0x2986d84c8668a351c6db]))),((BitVec.ofNat 152 (word80 [0xffffffffff00000001,0xfffffe000004e42dde00])),(BitVec.ofNat 152 (word80 [0x819c0ce13033c4e270,0x4e04e06f0b84e429c6db]))),((BitVec.ofNat 152 (word80 [1,0xfffffffffff22feda007])),(BitVec.ofNat 152 (word80 [0x5e02f01c0bc070381,0x701701700c022f8c8db6]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffffffffffffe,0xdfa9e5ff8])),(BitVec.ofNat 152 (word80 [0x600300000c0000001,0x80180180100018861924]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g47C : List ColumnInfo := [(2,0,45,0,4)]
def g47A : List (List Nat) := [[],[33]]
def g47D4 (j : Nat) := if j=0 then 0x3f else 0
def g47L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g47D4)
  | _ => emptyPacking
def g47I (_ _ : Nat) : Option (Nat × Nat) := none
def g47 : Forest := ⟨47,4,fun i => g47Y[i]?.getD (0,0),g47C,g47A,g47L,g47I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g47P4_0 : block g47 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g47B4 : block g47 4 0 1=true := g47P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g47T : checkedTables g47 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g47 0 0 0 = true)
  · exact (rfl : block g47 1 0 0 = true)
  · exact (rfl : block g47 2 0 0 = true)
  · exact (rfl : block g47 3 0 0 = true)
  · exact g47B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g47G : graphValid g47 (boundsBefore K201) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low47 : Lower true (varsX 47) (graphGoal 47) 5 := lower_forest (g:=g47) (i:=0) (hints:=1363) (before_sound K201 V201) g47G g47T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K47 := extendKnown K201 5 [(47,[]),(55,[16,67])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V47 : Known true K47 := extend_ok (m:=47) V201 low47 (by decide +kernel)
def g59Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3fffffc07ffff800ff,0xfffc07fffff27a560f0f])),(BitVec.ofNat 152 (word80 [0x822810810004504a01,0x4008102201300a525555]))),((BitVec.ofNat 152 (word80 [0xc003ffff80ffffff00,0x1fffffff001dadf9f0f0])),(BitVec.ofNat 152 (word80 [0xb005000201600c05,0x8050000404102c993333]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffc000000ffffffff,0xe00007fffe67e88e000f])),(BitVec.ofNat 152 (word80 [0x24c2a61a34a98510a6,0x156165485047e08caaaa]))),((BitVec.ofNat 152 (word80 [0xffffffff,0xfffff800002697f400f0])),(BitVec.ofNat 152 (word80 [0x3703382c58ce0660c8,0x1982467098269364cccc]))),((BitVec.ofNat 152 (word80 [0xffffffffff00000000,0x19d530dff00])),(BitVec.ofNat 152 (word80 [0x3803c03060f00780f0,0x1e038780e08d51048888]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g59C : List ColumnInfo := []
def g59A : List (List Nat) := [[],[16,67]]
def g59D4 (j : Nat) := if j=0 then 0x1f else 0
def g59L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g59D4)
  | _ => emptyPacking
def g59I (_ _ : Nat) : Option (Nat × Nat) := none
def g59 : Forest := ⟨59,4,fun i => g59Y[i]?.getD (0,0),g59C,g59A,g59L,g59I⟩
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
theorem g59T : checkedTables g59 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g59 0 0 0 = true)
  · exact (rfl : block g59 1 0 0 = true)
  · exact (rfl : block g59 2 0 0 = true)
  · exact (rfl : block g59 3 0 0 = true)
  · exact g59B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59G : graphValid g59 (boundsBefore K47) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low59 : Lower true (varsX 59) (graphGoal 59) 5 := lower_forest (g:=g59) (i:=0) (hints:=65603) (before_sound K47 V47) g59G g59T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K59 := extendKnown K47 5 [(59,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V59 : Known true K59 := extend_ok (m:=59) V47 low59 (by decide +kernel)
def g91Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xc00fff0ffffffc00ff,0xfff0fffeea3a5303f03f])),(BitVec.ofNat 152 (word80 [0x84a08a210802284a02,0x80220882200a53145145]))),((BitVec.ofNat 152 (word80 [0xfff0000ffc3fffff00,0x3fffffc009adfd000fc0])),(BitVec.ofNat 152 (word80 [0xc42c405090b10c4b,0x11404108092d994d34d3]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffff0003fffffff,0xc000fffd77e88afc003f])),(BitVec.ofNat 152 (word80 [0x90130026104c0100c,0x584120152a08828a28a]))),((BitVec.ofNat 152 (word80 [0x3fffffff,0xffff00012697f4000fc0])),(BitVec.ofNat 152 (word80 [0x2e09c08b8227026090,0x26009c11269264b2cb2c]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffc0000000,0x39d530dfff000])),(BitVec.ofNat 152 (word80 [0x300e000c00380380e0,0x3808e0208d5104c30c30]))),(0x0,0x0),(0x0,0x0)]
def g91C : List ColumnInfo := [(0,2,73,16,5)]
def g91A : List (List Nat) := [[],[99],[65],[65,99],[48],[48,96],[48,65],[48,65,96],[96,48],[96],[96,65,48],[96,65]]
def g91D5 (j : Nat) := if j=0 then 0x3f else 0
def g91L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g91D5)
  | _ => emptyPacking
def g91I (_ _ : Nat) : Option (Nat × Nat) := none
def g91 : Forest := ⟨91,5,fun i => g91Y[i]?.getD (0,0),g91C,g91A,g91L,g91I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g91P5_0 : block g91 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g91B5 : block g91 5 0 1=true := g91P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g91T : checkedTables g91 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g91 0 0 0 = true)
  · exact (rfl : block g91 1 0 0 = true)
  · exact (rfl : block g91 2 0 0 = true)
  · exact (rfl : block g91 3 0 0 = true)
  · exact (rfl : block g91 4 0 0 = true)
  · exact g91B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g91G : graphValid g91 (boundsBefore K59) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low91 : Lower true (varsX 91) (graphGoal 91) 6 := lower_forest (g:=g91) (i:=0) (hints:=65603) (before_sound K59 V59) g91G g91T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K91 := extendKnown K59 6 [(91,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V91 : Known true K91 := extend_ok (m:=91) V59 low91 (by decide +kernel)
def g103Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffc01ff81ffffff00,0x3ff01ff80feae3c40e07])),(BitVec.ofNat 152 (word80 [0xa0a8d4253452502a1a,0x84a342916288e2c49249]))),((BitVec.ofNat 152 (word80 [0xffffe0001ff03ffff,0xc0001ffff0054bb40038])),(BitVec.ofNat 152 (word80 [0xc930993658649a4c93,0x26c5932244c54bb6db6d]))),((BitVec.ofNat 152 (word80 [0xffffffffe0003ffff,0xffffe00000196c9871c0])),(BitVec.ofNat 152 (word80 [0x1c0e0386078e0701c,0x70603c387086c989249]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xf0000000000003ffff,0xffffffffffe47e6381ff])),(BitVec.ofNat 152 (word80 [0x20100400080008020,0x8000400000000012492]))),((BitVec.ofNat 152 (word80 [0xfffffffffffffc0000,0x1b91bffe00])),(BitVec.ofNat 152 (word80 [0xc02018001000300c0,0x30081804081311224924]))),(0x0,0x0),(0x0,0x0)]
def g103C : List ColumnInfo := [(1,0,102,0,5)]
def g103A : List (List Nat) := [[],[32]]
def g103D5 (j : Nat) := if j=0 then 0x3f else 0
def g103L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g103D5)
  | _ => emptyPacking
def g103I (_ _ : Nat) : Option (Nat × Nat) := none
def g103 : Forest := ⟨103,5,fun i => g103Y[i]?.getD (0,0),g103C,g103A,g103L,g103I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g103P5_0 : block g103 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g103B5 : block g103 5 0 1=true := g103P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g103T : checkedTables g103 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g103 0 0 0 = true)
  · exact (rfl : block g103 1 0 0 = true)
  · exact (rfl : block g103 2 0 0 = true)
  · exact (rfl : block g103 3 0 0 = true)
  · exact (rfl : block g103 4 0 0 = true)
  · exact g103B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g103G : graphValid g103 (boundsBefore K91) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low103 : Lower true (varsX 103) (graphGoal 103) 6 := lower_forest (g:=g103) (i:=0) (hints:=1365) (before_sound K91 V91) g103G g103T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K103 := extendKnown K91 6 [(103,[]),(174,[16,48,117,101]),(181,[65,49,117,101]),(185,[48,65,82,16,32,112,96]),(186,[64,49,82,16,33,113,97])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V103 : Known true K103 := extend_ok (m:=103) V91 low103 (by decide +kernel)
def g107Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffc03ff0fffffc03f,0xfff0fffff5560300f0ff])),(BitVec.ofNat 152 (word80 [0x2028280a2020028281,0x40220020900603111111]))),((BitVec.ofNat 152 (word80 [0xffffc000ff0ffffc0,0x1fff0ff014b579000f00])),(BitVec.ofNat 152 (word80 [0x48b0322c41428b2325,0x9140284214b551bbbbbb]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffff000ffffff,0xe0000fff2bb5260f000f])),(BitVec.ofNat 152 (word80 [0x82c140b005842c0406,0x58442802b9120666666]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xf00000000000ffffff,0xfffff000134bf8f00ff0])),(BitVec.ofNat 152 (word80 [0x30180c08608300808,0x6000304034828444444]))),((BitVec.ofNat 152 (word80 [0xffffffffffff000000,0xcea8c5fff000])),(BitVec.ofNat 152 (word80 [0xc0203000800c03030,0x18088c084420c4888888]))),(0x0,0x0),(0x0,0x0)]
def g107C : List ColumnInfo := [(0,2,73,32,5),(2,0,105,0,5),(8,0,99,0,5),(1,0,106,0,4),(32,2,73,0,4),(64,0,43,0,4)]
def g107A : List (List Nat) := [[],[96]]
def g107D4 (j : Nat) := if j=0 then 0x5bd4940 else 0
def g107D5 (j : Nat) := if j=0 then 0xc8404fd40 else 0
def g107H5 (j : Nat) := if j=0 then 0x4 else 0
def g107D6 (j : Nat) := if j=0 then 0x2b2a0bf else 0
def g107H6 (j : Nat) := if j=0 then 0xa else 0
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
theorem g107G : graphValid g107 (boundsBefore K103) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low107 : Lower true (varsX 107) (graphGoal 107) 7 := lower_forest (g:=g107) (i:=0) (hints:=83) (before_sound K103 V103) g107G g107T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K107 := extendKnown K103 7 [(107,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V107 : Known true K107 := extend_ok (m:=107) V103 low107 (by decide +kernel)
def g109Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfe1ff00ff87f87ffc0,0x7fff8fffd8b95000f0ff])),(BitVec.ofNat 152 (word80 [0x1440a0a05101100285,0x5012008488941111111]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1ffff0007ff87fff,0x807ff1fc2b1e600f0f00])),(BitVec.ofNat 152 (word80 [0x5882c0c1620a010b06,0x160a0411291e43333333]))),((BitVec.ofNat 152 (word80 [0x1fffffff80007fff,0xff8001ff941fb0f0000f])),(BitVec.ofNat 152 (word80 [0x610b0505802c222c08,0x182c48a01416b6666666]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffe000000000007fff,0xfffffe000be4bf000ff0])),(BitVec.ofNat 152 (word80 [0x800c06060430443010,0x203000c20260b4444444]))),((BitVec.ofNat 152 (word80 [0xffffffffffffff8000,0x6442cffff000])),(BitVec.ofNat 152 (word80 [0x1008080040004020,0x40400100000008888888]))),(0x0,0x0),(0x0,0x0)]
def g109C : List ColumnInfo := [(1,0,108,0,5),(4,0,105,0,5),(8,0,101,0,5),(32,0,77,0,5)]
def g109A : List (List Nat) := [[],[80,50]]
def g109D6 (j : Nat) := if j=0 then 0x4e09f else 0
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
theorem low109 : Lower true (varsX 109) (graphGoal 109) 7 := lower_forest (g:=g109) (i:=0) (hints:=1283) (before_sound K107 V107) g109G g109T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K109 := extendKnown K107 7 [(109,[]),(171,[33,118]),(173,[118]),(179,[16,32,67,118]),(242,[80,16,66,99,115])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V109 : Known true K109 := extend_ok (m:=109) V107 low109 (by decide +kernel)
def g110Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0x7ff001ff80ffc07ff0,0x3ffffe03ff4b12b0007])),(BitVec.ofNat 152 (word80 [0x42a8d4251a148b42a9,0xaa4a8a458a64b1235b6d]))),((BitVec.ofNat 152 (word80 [0x7ffffe0000ffffffff,0xfc00ffffc068db9401f8])),(BitVec.ofNat 152 (word80 [0x4c098362c191204c1,0x306c0c891340d3841249]))),((BitVec.ofNat 152 (word80 [0x7fffffffff00007fff,0xffff0000000ff00e8e00])),(BitVec.ofNat 152 (word80 [0x1702e0b8305e1c1701,0xc0702f0e1c0df00cb6db]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x800000000000007fff,0xffffffffff99af6d703f])),(BitVec.ofNat 152 (word80 [0x180300c04060201802,0x80300000190c082492]))),((BitVec.ofNat 152 (word80 [0xffffffffffffff8000,0x6754f2ffc0])),(BitVec.ofNat 152 (word80 [0x600c0100008000600c,0x300c010202200724924]))),(0x0,0x0),(0x0,0x0)]
def g110C : List ColumnInfo := [(2,0,108,0,5)]
def g110A : List (List Nat) := [[],[49,101]]
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
theorem low110 : Lower true (varsX 110) (graphGoal 110) 6 := lower_forest (g:=g110) (i:=0) (hints:=34628944) (before_sound K109 V109) g110G g110T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K110 := extendKnown K109 6 [(110,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V110 : Known true K110 := extend_ok (m:=110) V109 low110 (by decide +kernel)
def g115Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffc01ffffffff003ff,0xff87ffc374d9420f83e0])),(BitVec.ofNat 152 (word80 [0xa8540a09002a0a814,0x910008a645802318c63]))),((BitVec.ofNat 152 (word80 [0xffffe00ff87ffffc01,0xfff87ffcd352b6007c1f])),(BitVec.ofNat 152 (word80 [0x830190c02120c43118,0x8201210050123694a529]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffff0007ffffffe,0x7ffcafd11c00001f])),(BitVec.ofNat 152 (word80 [0x2c16050ac24b08c221,0x2c224a00afc1096b5ad6]))),((BitVec.ofNat 152 (word80 [0x7fffffff,0xffff80004d2fe9f07fe0])),(BitVec.ofNat 152 (word80 [0x30180603040c010040,0x30000c100105c8421084]))),((BitVec.ofNat 152 (word80 [0xffffffffff80000000,0x33aa61bff8000])),(BitVec.ofNat 152 (word80 [0xc020180c00700e0381,0xc04470211aa2118c6318]))),(0x0,0x0),(0x0,0x0)]
def g115C : List ColumnInfo := [(0,16,97,2,5),(16,0,99,0,5),(1,0,114,0,4),(2,16,97,0,4),(64,0,51,0,4)]
def g115A : List (List Nat) := [[],[96]]
def g115D4 (j : Nat) := if j=0 then 0x4fd5130 else 0
def g115D5 := limbs80 #[#[0x480e140fd40ff30fd30,0x4088]]
def g115H5 (j : Nat) := if j=0 then 0x4 else 0
def g115D6 (j : Nat) := if j=0 then 0x18989f else 0
def g115H6 := limbs80 #[#[0x1a000000039000381a,0x350]]
def g115L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g115D4)
  | 5 => (3,1,3,0,0,5,0,g115D5)
  | 6 => (1,0,3,0,0,0,0,g115D6)
  | _ => emptyPacking
def g115I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 4 0 0 g115H5
  | 6 => lookupWord 1 13 0 7 2 1 g115H6
  | _ => fun _ => none
def g115 : Forest := ⟨115,6,fun i => g115Y[i]?.getD (0,0),g115C,g115A,g115L,g115I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g115P4_0 : block g115 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g115B4 : block g115 4 0 1=true := g115P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g115P5_0 : block g115 5 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g115B5 : block g115 5 0 3=true := g115P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g115P6_0 : block g115 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g115B6 : block g115 6 0 1=true := g115P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g115T : checkedTables g115 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g115 0 0 0 = true)
  · exact (rfl : block g115 1 0 0 = true)
  · exact (rfl : block g115 2 0 0 = true)
  · exact (rfl : block g115 3 0 0 = true)
  · exact g115B4
  · exact g115B5
  · exact g115B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g115G : graphValid g115 (boundsBefore K110) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low115 : Lower true (varsX 115) (graphGoal 115) 7 := lower_forest (g:=g115) (i:=0) (hints:=65605) (before_sound K110 V110) g115G g115T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K115 := extendKnown K110 7 [(115,[]),(118,[32])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V115 : Known true K115 := extend_ok (m:=115) V110 low115 (by decide +kernel)
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
theorem g143G : graphValid g143 (boundsBefore K115) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low143 : Lower true (varsX 143) (graphGoal 143) 6 := lower_forest (g:=g143) (i:=0) (hints:=1907) (before_sound K115 V115) g143G g143T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K143 := extendKnown K115 6 [(157,[33,65]),(188,[32,49,64,81])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V143 : Known true K143 := extend_ok (m:=143) V115 low143 (by decide +kernel)
def g155Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffc01ff87fc3fff00,0xffff1ffed2e680007c1f])),(BitVec.ofNat 152 (word80 [0x222894451108808a4a,0xa02444252268a5294a5]))),((BitVec.ofNat 152 (word80 [0xffffe0007ffc3ffff,0xffffe11773400f83e0])),(BitVec.ofNat 152 (word80 [0x40b018162050082c0c,0x2c140089146346318c63]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffff80003ffff,0xff001ffce8f541f0001f])),(BitVec.ofNat 152 (word80 [0x84c120980261113010,0x30588900a8d154a5294a]))),((BitVec.ofNat 152 (word80 [0xf0000000000003ffff,0xffffe0005f98fe0003e0])),(BitVec.ofNat 152 (word80 [0x701c0e0438221c060,0x40600e104b9898c6318c]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffffffffc0000,0x3280bbffffc00])),(BitVec.ofNat 152 (word80 [0x80201000400020080,0x80801000000021084210]))),(0x0,0x0)]
def g155C : List ColumnInfo := [(1,0,154,0,5),(2,0,153,0,5),(8,0,147,0,5),(16,0,139,0,5),(9,0,146,0,4),(18,0,137,0,4)]
def g155A : List (List Nat) := [[],[65],[16,67],[16,48,64],[48],[48,65],[64,16,49],[64,49]]
def g155D4 := limbs80 #[#[0x9bd89544426d6215110,0x31825f635474]]
def g155D5 := limbs80 #[#[0x7c54443f280885bd4940,0xfea8885f95110beaa221,0xbd4940bfa8a81fb40502,0xcc8d018160c02faa3a07,0x882188201141080d176b,0xc110204810001]]
def g155H5 := limbs80 #[#[0x490000280000710000f2,0x90]]
def g155D6 := limbs80 #[#[0x540a0380ff40fd40fd10,0x3140cc503]]
def g155H6 := limbs80 #[#[0x308000000000070b41,0x3240051800d1c0000000,0x18590cd9e100004400,0xa4c0025c000000000000,0x95200c84000000000000]]
def g155D7 (j : Nat) := if j=0 then 0x1605f else 0
def g155H7 := limbs80 #[#[0x60027400a12a53200006,0x2200000214d8ba801041,0xb]]
def g155L : Nat → Packing
  | 4 => (3,3,3,0,0,4,0,g155D4)
  | 5 => (10,2,3,0,0,7,0,g155D5)
  | 6 => (3,1,3,0,0,6,0,g155D6)
  | 7 => (1,0,3,0,0,0,0,g155D7)
  | _ => emptyPacking
def g155I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 11 0 8 2 2 g155H5
  | 6 => lookupWord 4 41 0 10 4 2 g155H6
  | 7 => lookupWord 3 19 1 9 2 3 g155H7
  | _ => fun _ => none
def g155 : Forest := ⟨155,7,fun i => g155Y[i]?.getD (0,0),g155C,g155A,g155L,g155I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g155P4_0 : block g155 4 0 3=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g155B4 : block g155 4 0 3=true := g155P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g155P5_0 : block g155 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g155P5_1 : block g155 5 1 9=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g155B5 : block g155 5 0 10=true := (@block_merge g155 5 0 1 9 g155P5_0 g155P5_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g155P6_0 : block g155 6 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g155B6 : block g155 6 0 3=true := g155P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g155P7_0 : block g155 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g155B7 : block g155 7 0 1=true := g155P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g155T : checkedTables g155 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g155 0 0 0 = true)
  · exact (rfl : block g155 1 0 0 = true)
  · exact (rfl : block g155 2 0 0 = true)
  · exact (rfl : block g155 3 0 0 = true)
  · exact g155B4
  · exact g155B5
  · exact g155B6
  · exact g155B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g155G : graphValid g155 (boundsBefore K143) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low155 : Lower true (varsX 155) (graphGoal 155) 8 := lower_forest (g:=g155) (i:=0) (hints:=65603) (before_sound K143 V143) g155G g155T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K155 := extendKnown K143 8 [(155,[]),(211,[99,83]),(218,[16,48,32,66,98,82])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V155 : Known true K155 := extend_ok (m:=155) V143 low155 (by decide +kernel)
def g167Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xc07fc01ff03fe07fff,0x7fc0ff81fed6800e07])),(BitVec.ofNat 152 (word80 [0x950a8d44a68a4b282a,0x35129a292ca6d6849249]))),((BitVec.ofNat 152 (word80 [0x7fffe0003fff81ff,0xff8000fffe0725a07038])),(BitVec.ofNat 152 (word80 [0x26130986cb0c924c4c,0x261b2c32493725a49249]))),((BitVec.ofNat 152 (word80 [0x7fffffffc00001ff,0xffffff0000074b4381c0])),(BitVec.ofNat 152 (word80 [0x381c0e070c0f1c7070,0x381c303c71c74b449249]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xff80000000000001ff,0xfffffffffffacd3c01ff])),(BitVec.ofNat 152 (word80 [0x2010080010000080,0x40200040000000092492]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffffffffffe00,0x532dffe00])),(BitVec.ofNat 152 (word80 [0x4020100020000100,0x80400080000000124924]))),(0x0,0x0)]
def g167C : List ColumnInfo := [(1,0,166,0,5)]
def g167A : List (List Nat) := [[],[117],[33],[33,117],[16],[16,117],[16,32],[16,32,117],[32,16],[32,16,117],[32],[32,117]]
def g167D5 (j : Nat) := if j=0 then 0x3f else 0
def g167L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g167D5)
  | _ => emptyPacking
def g167I (_ _ : Nat) : Option (Nat × Nat) := none
def g167 : Forest := ⟨167,5,fun i => g167Y[i]?.getD (0,0),g167C,g167A,g167L,g167I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g167P5_0 : block g167 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g167B5 : block g167 5 0 1=true := g167P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g167T : checkedTables g167 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g167 0 0 0 = true)
  · exact (rfl : block g167 1 0 0 = true)
  · exact (rfl : block g167 2 0 0 = true)
  · exact (rfl : block g167 3 0 0 = true)
  · exact (rfl : block g167 4 0 0 = true)
  · exact g167B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g167G : graphValid g167 (boundsBefore K155) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low167 : Lower true (varsX 167) (graphGoal 167) 6 := lower_forest (g:=g167) (i:=0) (hints:=1365) (before_sound K155 V155) g167G g167T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K167 := extendKnown K155 6 [(167,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V167 : Known true K167 := extend_ok (m:=167) V155 low167 (by decide +kernel)
def g203Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfe1ff00ff87f87ffc0,0x7fc7ffffd3b94000f0ff])),(BitVec.ofNat 152 (word80 [0x1440a0a05101100285,0x2902008418941111111]))),((BitVec.ofNat 152 (word80 [0x1ffff0007ff87fff,0x8007f1fc231ee00f0000])),(BitVec.ofNat 152 (word80 [0x588ac4c5622a012b06,0x2b214491231ee7777777]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1fffffff80007fff,0xfff801ff9c1f30f00f0f])),(BitVec.ofNat 152 (word80 [0x61030101800c220c08,0xc0188201c1602222222]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffe000000000007fff,0xfffffe000be4bf000ff0])),(BitVec.ofNat 152 (word80 [0x800c06060430443010,0x300200c20260b4444444]))),((BitVec.ofNat 152 (word80 [0xffffffffffffff8000,0x6442cffff000])),(BitVec.ofNat 152 (word80 [0x1008080040004020,0x40040100000008888888]))),(0x0,0x0)]
def g203C : List ColumnInfo := [(2,0,201,0,7)]
def g203A : List (List Nat) := [[],[99],[48],[48,96],[96,48],[96]]
def g203D7 (j : Nat) := if j=0 then 0x3f else 0
def g203L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g203D7)
  | _ => emptyPacking
def g203I (_ _ : Nat) : Option (Nat × Nat) := none
def g203 : Forest := ⟨203,7,fun i => g203Y[i]?.getD (0,0),g203C,g203A,g203L,g203I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g203P7_0 : block g203 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g203B7 : block g203 7 0 1=true := g203P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g203T : checkedTables g203 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g203 0 0 0 = true)
  · exact (rfl : block g203 1 0 0 = true)
  · exact (rfl : block g203 2 0 0 = true)
  · exact (rfl : block g203 3 0 0 = true)
  · exact (rfl : block g203 4 0 0 = true)
  · exact (rfl : block g203 5 0 0 = true)
  · exact (rfl : block g203 6 0 0 = true)
  · exact g203B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g203G : graphValid g203 (boundsBefore K167) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low203 : Lower true (varsX 203) (graphGoal 203) 8 := lower_forest (g:=g203) (i:=0) (hints:=115) (before_sound K167 V167) g203G g203T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K203 := extendKnown K167 8 [(203,[]),(217,[65,33]),(241,[65,33,83]),(244,[32,65,83])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V203 : Known true K203 := extend_ok (m:=203) V167 low203 (by decide +kernel)
def g205Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xff0ff01fe3f8ffe0,0x3fc7f1ffd675000f00ff])),(BitVec.ofNat 152 (word80 [0xa0a20a14148120142,0x82902402163411111111]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xff000fffe003ff1fff,0xc007fe3f317a00f00f00])),(BitVec.ofNat 152 (word80 [0x2c2c42c18590a04583,0xb214084b17a33333333]))),((BitVec.ofNat 152 (word80 [0xffffffc001fff,0xfff8003fede10f00f00f])),(BitVec.ofNat 152 (word80 [0x303083020600c48604,0xc01890829c122222222]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffff0000000001fff,0xffffffc01388f000fff0])),(BitVec.ofNat 152 (word80 [0x404004040801000808,0x10020010000044444444]))),((BitVec.ofNat 152 (word80 [0xffffffffffffffe000,0x2816ffff0000])),(BitVec.ofNat 152 (word80 [0x808008081002001010,0x20040020000088888888]))),(0x0,0x0)]
def g205C : List ColumnInfo := [(4,0,201,0,7)]
def g205A : List (List Nat) := [[],[118],[48],[48,118]]
def g205D7 (j : Nat) := if j=0 then 0x3f else 0
def g205L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g205D7)
  | _ => emptyPacking
def g205I (_ _ : Nat) : Option (Nat × Nat) := none
def g205 : Forest := ⟨205,7,fun i => g205Y[i]?.getD (0,0),g205C,g205A,g205L,g205I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g205P7_0 : block g205 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g205B7 : block g205 7 0 1=true := g205P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g205T : checkedTables g205 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g205 0 0 0 = true)
  · exact (rfl : block g205 1 0 0 = true)
  · exact (rfl : block g205 2 0 0 = true)
  · exact (rfl : block g205 3 0 0 = true)
  · exact (rfl : block g205 4 0 0 = true)
  · exact (rfl : block g205 5 0 0 = true)
  · exact (rfl : block g205 6 0 0 = true)
  · exact g205B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g205G : graphValid g205 (boundsBefore K203) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low205 : Lower true (varsX 205) (graphGoal 205) 8 := lower_forest (g:=g205) (i:=0) (hints:=1539) (before_sound K203 V203) g205G g205T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K205 := extendKnown K203 8 [(205,[]),(227,[33,99,67,84]),(230,[32,16,99,67,84]),(236,[32,16,49,81,65])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V205 : Known true K205 := extend_ok (m:=205) V203 low205 (by decide +kernel)
def g229Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x7f01fc7f01fc7e7fc,0x7f1f9fe7ea000f00f0f])),(BitVec.ofNat 152 (word80 [0x50a14290a142905028,0x50a414051ea111111111]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x7ffe007ffe007f9ff,0xf801fe7f8b700f00f0f0])),(BitVec.ofNat 152 (word80 [0x60c18320c183208430,0x60c821084b7111111111]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xf8000007fffff801ff,0xfffe007fe640f00f00ff])),(BitVec.ofNat 152 (word80 [0x810204010204010040,0x81004010000222222222]))),((BitVec.ofNat 152 (word80 [0xfffffff800000001ff,0xffffff8001af000fff00])),(BitVec.ofNat 152 (word80 [0x20408020408020081,0x2008020000444444444]))),((BitVec.ofNat 152 (word80 [0xfffffffffffffffe00,0x181ffff00000])),(BitVec.ofNat 152 (word80 [0x40810040810040102,0x4010040000888888888]))),(0x0,0x0)]
def g229C : List ColumnInfo := [(1,0,228,0,7)]
def g229A : List (List Nat) := [[],[118],[101],[101,117],[117,101],[117],[32],[32,118],[32,101],[32,101,117],[32,117,101],[32,117]]
def g229D7 (j : Nat) := if j=0 then 0x3f else 0
def g229L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g229D7)
  | _ => emptyPacking
def g229I (_ _ : Nat) : Option (Nat × Nat) := none
def g229 : Forest := ⟨229,7,fun i => g229Y[i]?.getD (0,0),g229C,g229A,g229L,g229I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g229P7_0 : block g229 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g229B7 : block g229 7 0 1=true := g229P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g229T : checkedTables g229 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g229 0 0 0 = true)
  · exact (rfl : block g229 1 0 0 = true)
  · exact (rfl : block g229 2 0 0 = true)
  · exact (rfl : block g229 3 0 0 = true)
  · exact (rfl : block g229 4 0 0 = true)
  · exact (rfl : block g229 5 0 0 = true)
  · exact (rfl : block g229 6 0 0 = true)
  · exact g229B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g229G : graphValid g229 (boundsBefore K205) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low229 : Lower true (varsX 229) (graphGoal 229) 8 := lower_forest (g:=g229) (i:=0) (hints:=1285) (before_sound K205 V205) g229G g229T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K229 := extendKnown K205 8 [(229,[]),(233,[48,82,32])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V229 : Known true K229 := extend_ok (m:=229) V205 low229 (by decide +kernel)
def g63Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3fffffffffffffffff,0xfcd8034dfabc9c007c1f])),(BitVec.ofNat 152 (word80 [0x80a0a80a1280a14810,0xa4d003043a28985294a5]))),((BitVec.ofNat 152 (word80 [0xfffffc00003ffffc00,0x1a55e33360f780f83e0])),(BitVec.ofNat 152 (word80 [0x53000db00099003,0x31a11e21200c58318c63]))),((BitVec.ofNat 152 (word80 [0x3fffffffffc0000000,0x233e3a455ec53f00000])),(BitVec.ofNat 152 (word80 [0x2c9c02c9c02cde025,0xc231c3a454ac52f7bdef]))),((BitVec.ofNat 152 (word80 [0x3fffffffffffffffff,0xfac58e65c5f6a400001f])),(BitVec.ofNat 152 (word80 [0x2b0e02b0e02b0e0146,0x2058c61c5d625ad6b5a]))),((BitVec.ofNat 152 (word80 [0xc00000000000000000,0x245795afe62520003e0])),(BitVec.ofNat 152 (word80 [0x33f0033f0033f00278,0x244615ade6203ce739c]))),(0x73aa5b8895b2bfffc00,(BitVec.ofNat 152 (word80 [0x3c0003c0003c000380,0xa2018815321084210]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g63C : List ColumnInfo := [(4,0,59,0,5),(8,0,55,0,5),(16,0,47,0,5),(1,8,54,0,4),(2,16,45,0,4)]
def g63A : List (List Nat) := [[],[16,67]]
def g63D5 (j : Nat) := if j=0 then 0x1ef52 else 0
def g63D6 (j : Nat) := if j=0 then 0x222317f else 0
def g63H6 (j : Nat) := if j=0 then 0xc else 0
def g63L : Nat → Packing
  | 5 => (1,1,3,0,0,0,0,g63D5)
  | 6 => (1,0,3,0,0,0,0,g63D6)
  | _ => emptyPacking
def g63I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 2 0 4 0 0 g63H6
  | _ => fun _ => none
def g63 : Forest := ⟨63,6,fun i => g63Y[i]?.getD (0,0),g63C,g63A,g63L,g63I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P5_0 : block g63 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g63B5 : block g63 5 0 1=true := g63P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P6_0 : block g63 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g63B6 : block g63 6 0 1=true := g63P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63T : checkedTables g63 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g63 0 0 0 = true)
  · exact (rfl : block g63 1 0 0 = true)
  · exact (rfl : block g63 2 0 0 = true)
  · exact (rfl : block g63 3 0 0 = true)
  · exact (rfl : block g63 4 0 0 = true)
  · exact g63B5
  · exact g63B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63G : graphValid g63 (boundsBefore K229) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low63 : Lower true (varsX 63) (graphGoal 63) 7 := lower_forest (g:=g63) (i:=0) (hints:=66883) (before_sound K229 V229) g63G g63T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K63 := extendKnown K229 7 [(63,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V63 : Known true K63 := extend_ok (m:=63) V229 low63 (by decide +kernel)
def g111Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xf003ffffffffffffff,0xfe28e884bd89000f00ff])),(BitVec.ofNat 152 (word80 [0x20581400a804a01481,0x4e08a0808c0911111111]))),((BitVec.ofNat 152 (word80 [0xfffc00fffc000fffc0,0x7d10ea50cb300000f00])),(BitVec.ofNat 152 (word80 [0x4290a6853236c89906,0x67d10ea50c91bbbbbbbb]))),((BitVec.ofNat 152 (word80 [0xfffffff00000,0x1cf2190dad100f0f000])),(BitVec.ofNat 152 (word80 [0x84e13809c02700de0b,0x814b2180da9133333333]))),((BitVec.ofNat 152 (word80 [0xffffffffffff,0xf2153f483bb80f00000f])),(BitVec.ofNat 152 (word80 [0x701c02e00b802e00c,0x151d4033b066666666]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffff000000000000,0x116d0a38776f000fff0])),(BitVec.ofNat 152 (word80 [0x3000c0030010,0x45000016644444444]))),(0xce9177e4005ffff0000,(BitVec.ofNat 152 (word80 [0x80200c003000c0020,0xa0023e000088888888]))),(0x0,0x0),(0x0,0x0)]
def g111C : List ColumnInfo := [(2,0,109,0,7),(4,0,107,0,7),(0,2,77,32,6),(1,0,110,0,6),(8,0,103,0,6),(3,0,108,0,5),(4,2,73,32,5),(6,0,105,0,5),(9,0,102,0,5),(10,0,101,0,5),(32,0,77,0,5),(32,2,77,0,5),(64,0,47,0,5),(5,0,106,0,4),(36,0,73,0,4),(66,0,45,0,4),(68,0,43,0,4)]
def g111A : List (List Nat) := [[]]
def g111D4 := limbs80 #[#[0x50d40483625d54350120,0x482d86174154120d8b75,0xe1561541209e187d0550,0x54120f095450d50482d8,0x9e3855c3414827221d43,0x9956148239e1975d0520,0x5423561f63d0550c6775,0xe0976d07508e7825db41,0x597418e7825db53d0639,0xb19801955450e3960372,0x5c06550ec36086555143,0xe0217e1d6519543c5965,0x6aa4e9109e2d4e84d951,0x480fef1cb666c1,0x90100]]
def g111D5 := limbs80 #[#[0x6f0b8682907894350120,0xf52a8a024139dc965d0,0x82f5baa80905e9755012,0x20fc2a2a8241f8d05504,0x483f0b8aa0907e161541,0x120f96e6a8241f250d50,0x483b5aa2a0907695454,0x520bcaeba0a417add15,0x61482f3bb2a2905e576d,0x50d20bceeab0a41b9995,0x954483c6aa286907cb70,0x359520bd2e1aa2413bdd,0xd50502f4b84ca905cf7,0x7050d40e72a8a8281e65,0xd95435034eb2a86a079b,0xf73595409dee4b2a81a7,0x5d8f41542f8b8682a84d,0xf576d0550aeaeba0aa1b,0xb5d8d615436bb1aa2a84,0x4dc7650d50e3aa8a1aa1,0x1b55c7635426f3b286a8,0x857575d07509bae9b1aa,0xa1c755143d427abb683a,0xa0cef7259350d3ac8a1e,0xe833d5db53d067bbaac1,0x6a1ee772597419eee0b2,0x9a87675d35350ecfba2a,0xcaa1cfb7059543cbecba,0xaa28767dc15450e77b92,0xaa8a1f1c6555143f1ee4,0x432a87765c06550f8fb2,0x82caa1e5d6519543b9ae],#[0xcb32a8773dc96550eedb,0xb86c4aa4ef7259353cbe,0x580f00137dcd60d5276,0x1684f100390c82f0901d,0x2187f1e0751b86b1905d,0x2d8af2b0a52889b2508d,0x388df370d9358cf320bd,0x419033f0f53b8eb3a0e5,0x4891f471194490f43109,0x4e9374d1314b92b4a125,0x5795b561555494b5113d,0x5024857c01da96759161,0x3480804802115831409,0x920204402841b480e1d2,0x40083020c080480801a0,0x20201202015824808382,0x202c4081d1054409,0x80e102120800000000,0x18408000000,0x3102c40c58200000000]]
def g111H5 := limbs80 #[#[0x3d800002af88004d80,0x14c82da000018a8f4e64,0x9200214010f53002c74a,0x4000f10020401]]
def g111D6 := limbs80 #[#[0x9d0520fa54120fa50120,0x50d20f958520f954520f,0x8341b7d8d50e750d40f3,0x143bdd8151bd59741bd5,0x20fb55120bbd8954e755,0xfb59520fb59120fbd51,0xef55140fe54140fb9952,0xdd0550bfd9540bf59540,0x50d50fd58550fd54550f,0x5150df55150f7d8d50f7,0xf50fdd0750bfd9150dfd,0x41bf59350df55350f750,0x3fd54d51fdd4f41fd54f,0xef55143f7d4d43f754d4,0x758143bfd9543bf59543,0x59543f719543f7d8143f,0x9153f7d9543f799543f7,0x954bfd8154bf59353bfd,0x54bf58354bfd8d54fbd8,0xe07a0b00f411000bf58f,0x7c2b44e0921091dc3144,0x472895051e138c6acc81,0x4bbd66ab252ea0d37a4d,0xadc83836c2d359931e61,0x14c077e6f61e5bc5762e,0x5099cf34e58c818bf112,0x1589676c157cac351a92,0x890642a0c6e01018dc02,0xd58a1e40d5624141215,0x3c0184c3805c315241c1,0x23c58984505845280f0c,0x558782584130e016223c],#[0x20147205618340ac3403,0x910c086a2401901a911,0x820400208080801018b,0x140107c80a18f8880388,0x3841420610487803150e,0x50e14012182082020018,0x10120208004040070811,0x20200416102448050630,0x48044480406281000c18,0xa01050446890a0182234,0xc504448044480246890,0x10100184040400810100,0x202001800704b0c]]
def g111H6 := limbs80 #[#[0xa20a0216083910a00000,0x1879060096242024,0x188000f66001888,0xb4af107340006c34cb8b,0x34c59f000e152291cc2,0x5221af6cca209ba99720,0x14093b28a418a1736635,0xc8cae08733a163d0815,0x188c000bb0000000000,0xc3d96baf35c002932020,0xc00000a7e22589744001,0x2a540000003184578a5,0xbde2929fc40001020000,0xd6a45b03d410000019f7,0x1b80001530dd92ac]]
def g111D7 := limbs80 #[#[0xd43faa8fdd07da41f510,0x87ff50fea87f503bc87d,0x3fea9fd54ffa9ff54ffa,0x439c8c0511f8b4420f00,0x1458482c4ea6ab015c9c,0x2884b16884a0c136b808,0x58212c810482384b1403,0x18230a8602063208482c,0x532084b20528286020c,0xb18a0a180c20630a8602,0x40e084c2c63040e084]]
def g111H7 := limbs80 #[#[0x64338e1da080d41,0xe7100060000006635900,0x5430a001349000d75,0x384dd00000e250107,0xc726d646f954c24c006b,0x342f6bad71664001abcc,0x9b0f4a8be1c4307f5b00,0x5509800c46ee2380058,0x129678288dbaaf3e4800,0x359a3000af912a775]]
def g111D8 (j : Nat) := if j=0 then 0x5a02013f else 0
def g111H8 := limbs80 #[#[0x9800002d82c5004e0225,0xb4a90a699b00740048d3,0x4e]]
def g111L : Nat → Packing
  | 4 => (19,4,5,0,0,7,0,g111D4)
  | 5 => (71,3,5,0,0,10,0,g111D5)
  | 6 => (55,2,5,0,0,11,0,g111D6)
  | 7 => (14,1,5,0,0,9,0,g111D7)
  | 8 => (1,0,5,0,0,0,0,g111D8)
  | _ => emptyPacking
def g111I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 4 31 4 9 5 0 g111H5
  | 6 => lookupWord 17 97 7 11 7 0 g111H6
  | 7 => lookupWord 13 71 6 10 6 0 g111H7
  | 8 => lookupWord 3 19 5 8 4 0 g111H8
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
theorem g111P5_3 : block g111 5 3 68=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g111B5 : block g111 5 0 71=true := (@block_merge g111 5 0 3 68 g111P5_0 g111P5_3)
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
theorem g111G : graphValid g111 (boundsBefore K63) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low111 : Lower true (varsX 111) (graphGoal 111) 9 := lower_forest (g:=g111) (i:=0) (hints:=1363) (before_sound K63 V63) g111G g111T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K111 := extendKnown K63 9 [(111,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V111 : Known true K111 := extend_ok (m:=111) V63 low111 (by decide +kernel)
def g119Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3fffffe0003fff801,0xc71d31124cb001f003e0])),(BitVec.ofNat 152 (word80 [0x589402540da81290ad,0xc11d30124c80c6318c63]))),((BitVec.ofNat 152 (word80 [0xfc00fffffffffffffe,0xf8051a6f0d5800007c1f])),(BitVec.ofNat 152 (word80 [0x902640988131032048,0xf8041a6204525294a529]))),((BitVec.ofNat 152 (word80 [0xfffffffc000000,0x39c4f6938a803e0f8000])),(BitVec.ofNat 152 (word80 [0xe13804e009c01bc170,0x2944b6138880c6318c63]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffffffffe,0x428bea0bd9e80000001f])),(BitVec.ofNat 152 (word80 [0x1c097012e025c0180,0x28be009d9adad6b5ad6]))),((BitVec.ofNat 152 (word80 [0xffff00000000000000,0x22fa117cb687c00fffe0])),(BitVec.ofNat 152 (word80 [0x18003000600200,0x2a0010c120108421084]))),((BitVec.ofNat 152 (word80 [1,0x9d26ecc07137fff00000])),(BitVec.ofNat 152 (word80 [0x200e001c003800400,0x140248c02136318c6318]))),(0x0,0x0),(0x0,0x0)]
def g119C : List ColumnInfo := [(1,0,118,0,7)]
def g119A : List (List Nat) := [[],[32]]
def g119D7 (j : Nat) := if j=0 then 0x7f else 0
def g119L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g119D7)
  | _ => emptyPacking
def g119I (_ _ : Nat) : Option (Nat × Nat) := none
def g119 : Forest := ⟨119,7,fun i => g119Y[i]?.getD (0,0),g119C,g119A,g119L,g119I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P7_0 : block g119 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g119B7 : block g119 7 0 1=true := g119P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119T : checkedTables g119 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g119 0 0 0 = true)
  · exact (rfl : block g119 1 0 0 = true)
  · exact (rfl : block g119 2 0 0 = true)
  · exact (rfl : block g119 3 0 0 = true)
  · exact (rfl : block g119 4 0 0 = true)
  · exact (rfl : block g119 5 0 0 = true)
  · exact (rfl : block g119 6 0 0 = true)
  · exact g119B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119G : graphValid g119 (boundsBefore K111) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low119 : Lower true (varsX 119) (graphGoal 119) 8 := lower_forest (g:=g119) (i:=0) (hints:=66885) (before_sound K111 V111) g119G g119T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K119 := extendKnown K111 8 [(119,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V119 : Known true K119 := extend_ok (m:=119) V111 low119 (by decide +kernel)
def g126Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffffffff,0xd927e638c872c00003ff])),(BitVec.ofNat 152 (word80 [0x28802a40252014805,0x1927622080229294a529]))),((BitVec.ofNat 152 (word80 [0x1ffff00007fffc00,0x3ed8320ba06d800ffc00])),(BitVec.ofNat 152 (word80 [0x14c014c01b60099019,0xba50320b006186318c63]))),((BitVec.ofNat 152 (word80 [0x1ffffffff8000000,0x73433e14bd881f00000])),(BitVec.ofNat 152 (word80 [0x6702a7015380ade0ae,0x63433214bd88e739ce7]))),((BitVec.ofNat 152 (word80 [0x1fffffffffffffff,0xc858f56c4e4f4000001f])),(BitVec.ofNat 152 (word80 [0xb81338099c04ce0130,0x58954c4e4d6d6b5ad6]))),((BitVec.ofNat 152 (word80 [0xffe000000000000000,0x4578a17773c3e007fe0])),(BitVec.ofNat 152 (word80 [0xc003c001e000f001c0,0x4008814631c08421084]))),(0x33aa5dc49781bfff8000,(BitVec.ofNat 152 (word80 [0x1c000e0007000200,0x18a44c09400318c6318]))),(0x0,0x0),(0x0,0x0)]
def g126C : List ColumnInfo := [(8,0,118,0,7)]
def g126A : List (List Nat) := [[]]
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
theorem g126G : graphValid g126 (boundsBefore K119) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low126 : Lower true (varsX 126) (graphGoal 126) 8 := lower_forest (g:=g126) (i:=0) (hints:=34694464) (before_sound K119 V119) g126G g126T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K126 := extendKnown K119 8 [(126,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V126 : Known true K126 := extend_ok (m:=126) V119 low126 (by decide +kernel)
def g175Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfff803ffffffffffff,0xffc46d363a10000f00ff])),(BitVec.ofNat 152 (word80 [0x290582802a0250148,0x29c425140a1111111111]))),((BitVec.ofNat 152 (word80 [0xfffffc01fff0007ffc,0xf714685e2000f00f00])),(BitVec.ofNat 152 (word80 [0x2b22914c14c1b60990,0xccf704285e2333333333]))),((BitVec.ofNat 152 (word80 [0x1ffffff8000,0x22278cbfc00f00f000])),(BitVec.ofNat 152 (word80 [0x33c4e2702701380de1,0x7022278cbe8333333333]))),((BitVec.ofNat 152 (word80 [0x1ffffffffff,0xfe580f6b35b0f000000f])),(BitVec.ofNat 152 (word80 [0xbc070380b805c02e01,0x80180a6b35a666666666]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffe0000000000,0x24f859c3ef0000fff0])),(BitVec.ofNat 152 (word80 [0xc0000000c006003002,0xd841014444444444]))),(0x0,0x0),(0x19b82850c0fffff0000,(BitVec.ofNat 152 (word80 [0x10008004000,0x888888888]))),(0x0,0x0)]
def g175C : List ColumnInfo := [(2,0,173,0,7)]
def g175A : List (List Nat) := [[],[33]]
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
theorem g175G : graphValid g175 (boundsBefore K126) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low175 : Lower true (varsX 175) (graphGoal 175) 8 := lower_forest (g:=g175) (i:=0) (hints:=1363) (before_sound K126 V126) g175G g175T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K175 := extendKnown K126 8 [(175,[]),(183,[16,67])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V175 : Known true K175 := extend_ok (m:=175) V126 low175 (by decide +kernel)
def g187Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xff000ffffff01ffffc,0xda89f525200001f07c1f])),(BitVec.ofNat 152 (word80 [0x8a04a00a0020404400,0xda09a02025294a5294a5]))),((BitVec.ofNat 152 (word80 [0xfffff000fffffffe03,0xc47b40e2c0003e0f83e0])),(BitVec.ofNat 152 (word80 [0x2c00c02c0140000809,0xc41b40808318c6318c63]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffff00001ffffe,0xa4b07e8c6007c000001f])),(BitVec.ofNat 152 (word80 [0x3051053055858a90a2,0x24b05e8c4a5294a5294a]))),((BitVec.ofNat 152 (word80 [0xffffffffffffe00002,0x31aab2f300f8000003e0])),(BitVec.ofNat 152 (word80 [0xc066064066090ce132,0x31a0b2730c6318c6318c]))),((BitVec.ofNat 152 (word80 [2,0x4954930fdf00000ffc00])),(BitVec.ofNat 152 (word80 [0x780780780e0f01c2,0x144130f484210842108]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [1,0x37050a181ffffff00000])),(BitVec.ofNat 152 (word80 [0x8008008000100000,0x108421084210]))),(0x0,0x0)]
def g187C : List ColumnInfo := [(32,0,155,0,8),(8,0,179,0,7),(16,0,171,0,7),(1,0,186,0,6),(2,0,185,0,6),(9,0,178,0,5),(10,0,177,0,5),(17,0,170,0,5),(18,0,169,0,5),(24,0,163,0,5),(33,0,154,0,5),(128,0,59,0,5),(25,0,162,0,4),(26,0,161,0,4),(41,0,146,0,4),(136,0,51,0,4),(144,0,43,0,4)]
def g187A : List (List Nat) := [[],[16,67]]
def g187D4 := limbs80 #[#[0x32a215a1941cb7154110,0x82dd16544311b06c12e8,0x4fca30db9aa308623e0f,0xaa188d84dcc62585508,0xf624c30215f31ba0c4b]]
def g187D5 := limbs80 #[#[0x54630443d454d514c110,0x4431dd9771541109f387,0x6106554110a6d8219550,0x541108ef825d9504428f,0xde072dc5504422fe1176,0xd49504439a5895254110,0x442ea6107254110e6b62,0x6086554110ce876dc950,0x54910b398419550442da,0x8bf845d95244237e0d76,0x5c7524433ad8970d4910,0x4429b61762d4910ce762,0xe1176d49108df835db52,0x19510c3d655d0654422f,0xcad825d0654421fe1d65,0x1c96544333dcc7259510,0x44333dcf7259510caf74,0x20b7459510caf74dc965,0x99510caf82dd1654432b,0xec963dc9508423be0970,0x5c3518423761b7354610,0x88237e0d7199520cd963,0xe0d76546209e9809d521,0xd4a208bf845d95188237,0x8df835c66588273e0d71,0x585508c23be0976d4530,0x8c33c58570d4630ee372,0x6087558630a778558751,0x58630ad5831d5618c2b9,0xad7835d5618c2ad61075,0x585501431ddd67558630,0x142baa1d6254050ee372],#[0x5937254050ec963dc950,0x54050ceb76dc950143aa,0xccf73589511433ae0b76,0xdcd5114237a1d6354450,0x54276e0d71d4150c9d64,0xd8b5194550ccf73d8951,0x585508f7875846154399,0xcaf741896154333dcc62,0x18961542ab6106258550,0x54333dcf62585508ee87,0x61062d8550caf74d8961,0xd89508df835c762542ab,0xae9801c7625422fe1171,0x5c762542b3e0d71d8950,0x94276e0d71d4250aaf84,0xe0976d4250b5b835c750,0xd8152a9d841cd61d439a,0x9cf835c75254a37e0d71,0xcc2d09c2106c1503c00,0x1d46f1a4631744e12039,0x2949f26493234872047b,0x354cf324c32f4b72c4ab,0x414ff3e4f33b4e7384db,0x4d52f4a523475174450b,0x5955f56553535475053b,0x6558f625835f5775c56b,0x781da751c56fdb96cd9b,0x8420a811fe7e1f27b1e6,0x40030200000000000881,0x60,0x0,0x0],#[0x0,0xc1820000689401000]]
def g187H5 (j : Nat) := if j=0 then 0x1b006af720a89 else 0
set_option maxRecDepth 16000 in
def g187D6 := limbs80 #[#[0x25eba0ca884ed7219510,0x97ee8b2a213bdc96544,0x83b4a92a0906d9635421,0x20ed6a4a84413bdc9654,0x4c336b2ea5105e970d4a,0x50de2c2a84613bdc965,0x14374b12a0286f16154,0x4050d72c8a80a1b658d5,0x50942d6ba0c4a84fb765,0x587529bee6b0ea19e5db,0xd30443f8a8a60884df73,0x54c110fb6c698221f654,0xd5304437db2a60886f96,0x658c110fe2a3182217e5,0x5d6304437db2c60886f9,0xf7254110beee2a82217e,0xfd95504433e32aa0885e,0xf151541109faeca82219,0xfc1c550443f928aa0887,0x7795254110fe6e2a8221,0x1be58950443bda92a088,0x87e87254110df6c4a822,0x21be58d50443f5b92a08,0x885fb7354110df6c6a82,0x221ded9550443bc32aa0,0x887f25194110df0eca8,0x82217e9da50442fcbaca,0xa48867f65d4110beae3a,0xa9221bb58952442fdb82,0x6a4884fe76549109faec,0x5a92217d5c752442fcb8,0xb6a4884fd76d4910ddec],#[0xeab1221bbd89624427f3,0xb90ca884fd75d89109fe,0xaca32a216f5d065442f6,0x7b92ca884fe7619510cf,0xfecab2a216fdd165442f,0x7fb82ca886fb7059510c,0xddee4b2a21bb1c965442,0x35fba2ca884ff7259510,0x9fae132a219fd966544,0x43f5b92a1084fd72d951,0x10bf6e0a8c21bedd9508,0x842efb9aa3086dd63546,0x610cfccaa8c219f59551,0x18436eb1ea3085f970d4,0x4120fd2a4a82419f5975,0x51482efb9aa2907eb725,0xd4520bf2e1a8a413fdd9,0x5654827ebb6a2905ed72,0x199520ddee4b2a413fdc,0x8550883f490aa1104fd7,0x7254220fd6a4a8441be5,0x59521883f2a8a43107eb,0x56154620bdcea90c41bb,0x7dcd51882f7b92a3106f,0xff76546209faeca8c417,0x3f5db51882fcb86a3104,0x7e970d4a209feeab0c41,0x1bb59752882f6b8ea510,0x4ff7159620ddaeda944,0x613f5c66588377b92cb1,0x987eb7254130bf6e2a82,0xa61f6dcd504c3eca9aa0],#[0x2985df7354530ebaa6a8,0x8a617e5c3514c27fbb2a,0xa2985dd73d4530ebaa7a,0xb2a613fdc5654c27ebb6,0xcca986df7359530ddee4,0x2a8461be585508c27eb8,0xaa3187eb7254230bf6e,0xeca8c6177dcd518c37ab,0xb86a3184ff76546309fa,0xaeda8c61bd587518c2fc,0xa3aac3184ff75586309f,0xeceab0c61bd5d5618c37,0x7fb8acb186f77558630d,0xdf2c2a80a13f5c6658c2,0x37dbb2a0287eb7254050,0xdbac6a88a1bb5895114,0x435eb22a2285df735445,0x50deac3288a13fdd9511,0x1436eb1ca2286ed62944,0x1509faed288a1af59251,0x542fcb8ea0a86ef62d4,0x4550bf6e0a8aa1fad8b5,0x51542fcb84a2a86ef625,0x94550deec328aa1ddd46,0x46154377b16a2a86ef62,0x258550ddec430aa1bd58,0xc96154377b12c2a86ec6,0x7458550bbee6b0aa17bd,0xd8a615437bb0cc2a85bf,0xc62d8550bdae530aa1bb,0xf5cb6154377b16c2a86e,0x6f52549509fae7b0aa13],#[0xdbd895254377b12a4a87,0x5ee7618950edec5a92a1,0x1bb58f62543f5b86c4a8,0x84fd71d8950ddec7b12a,0xa1bbdc36254376b86c4a,0xa86ed71d8950dd8e3b12,0x2a1bbdc7625437738ec4,0x4a86ef53d8950ddaa7b1,0x9aa1bbdcf6254376b9ec,0xc6a85ef7258d50dbec6a,0xa84a1de947509427eb8e,0xea12877971d4250bf2e3,0x6b0ea17e5c251943bd38,0x9ac3a84ff7258750bbee,0xe6b0ea1b7dcd61d436e3,0xb8ec0a97cd53549329fe,0xae1b0aa577dcd6154a7e,0x6b8ea4a95ed70d49529f,0xbee6b0ea53fdc560d4af,0x6fb9ac3a94ff7058752b,0xd01581000e80b0058003,0x83c03683302d82802081,0x6686105785204c847041,0xf07d87a07687306f86a0,0x89208e88b08988608487,0xae8ad0a78a0098895093,0x50c18be0ba8b70b38b00,0x8d80d48d30d18ce0ca8c,0xf48ef0eb8e80e48e10db,0x110f90a1089010fd8fa0,0x91e11c91911791611491,0x3092b12992612292111f],#[0x514194013c93b1379361,0x95415294f14d94a14894,0x6e96d16b96616095d157,0x317f97c1789771759721,0x99819699518f98a18698,0xac9ab1a79a61a099f19d,0xf1bb9ba1b69b31b19ae1,0x9d21ce9cd1c99c61c29b,0xe69e51e19de1da9d71d5,0x91f39f21f09ef1ed9ea1,0xa0e20aa07205a001fc9f,0x28a25223a2221ea1b211,0x323fa36232a2f22ba2a2,0xa58254a5124da4a248a4,0x6ea6b267a64260a5d25b,0x527da78276a75273a722,0xa9228ea8d28ba8a288a8,0xaaaa52a1a9c29aa97295,0x52c1abc2baab72b1aae2,0xad62d4ad32d1acc2c8ac,0xe8ae52e3ae02dcadb2d9,0xd2fbaf82f6af32efaec2,0xb1030cb0b307b02300af,0xe00b0b1fb1c318b17315,0x30305e0080e004403c2,0xfe0083c17803e0042f8,0x5e00817802e00417802,0xe0081428205e00817802,0x80105e0083c183038405,0x2048814404881c1e00b,0x104040020400421080,0xa10b0c08040030004000],#[0x60484121040001284262,0x881620b0884106048410,0x4108420b041810000405,0x2830b081010304881210,0x322a10c10104040800,0xb04000021040020008,0x209e0080000400100000,0x48410004100001000780,0xc2210400004007040030,0x34108042c20406100,0x81020414100003040410,0x100420f410814181041,0x41000800200003a20800,0x41020410504081040000,0x1c1001c1c20408102050,0x4103041c1020400304,0x40e08200000007040410,0xc103040030208081840,0x8142040d85802040304,0x881a2041410000204001,0x3020a8818442c1c010,0x4083040c10b042c10b04,0x101c107041a204001830,0x41a8a803a2a008000000,0x30408304841000000210,0x1410b210a0c10b830800,0x20008009050c8426004,0x6260090c10504841,0x10b04021040010006204,0x400304003042c162040c,0x8041000810201080020,0x8101070410000b43]]
def g187H6 := limbs80 #[#[0x889c0085069828304002,0x92b8e0058000c4201425,0x42700000010cb,0x6c000000044e59551a80,0x1e80079d800000000000,0xb81772571c0000000006,0xf03d088001a5800487d9,0x32609b695,0x4a98e9400000769f2228,0x2178c400000000059002,0x4594c00018a000000408,0x38500000051f9010004,0x646d9850900000,0x1300000011a000121412,0x6a9c899000684e27c8b1,0x59e000391fa1a8980021,0x486800793ea0942000,0xd3ccb8e80019d50f68f8,0x280e0630bf23000151d8,0x699e22000004000300,0xf44114ba4ec02c203a68,0x800782101e94d9640dc4,0x4dd10911000000042,0x20c0000a38000,0x6832a400050a80000000]]
set_option maxRecDepth 16000 in
def g187D7 := limbs80 #[#[0xd98630bd58630b758e10,0x58850bd98450bd58450b,0x8950af59050b758c50bb,0x410bf59410ded4250bbd,0x10fe8c110fe4c110bf99,0xbf58910fe94110fe541,0xbf59510bf19510bfd891,0xe54210bfd9510bf99510,0x99610bf59610bf58610f,0x9520fb54920fe54120bf,0x620fe54220bf99520bf5,0x20fbd4a20bf58620fb48,0xfe54130bf99620bf596,0xbf99530bf59530f754d3,0xf59630bf58630fe54230,0x58450fe54050bf99630b,0x8550fed4150bf99450bf,0x950dfd4950df54950bfd,0x50bfd8950fbd8950fb18,0xbf58650fed4250bfd8d,0xdf54b50bf58750bf5965,0xf58f50bf58b50dfd4b50,0x99532bf59532fb54932b,0x4952bfd8552bfd8152bf,0x752bf58352bfd8d52fbd,0x10ff54110bf58f52bf58,0xffd4910ff54910ffd41,0xff19510ffd8910ff5891,0xfd9510ff99510ff59510,0x54520ffd4610ff54610f,0x4620ff54620ffd4520ff,0x630ffd4530ff54530ffd],#[0x50ff54450ffd4630ff54,0xff54550ffd4150ff944,0xff18550ffd4550ff9455,0xfd8550ff98550ff58550,0x58950ffd4950ff54950f,0x4d50ff54d50ffd8950ff,0x650ffd8d50ff58d50ffd,0x50ff58750ffd4650ff94,0x2ff58552ff58152ff987,0xff58352ff58d52ff54d5,0x105f03d022000ff58752,0x1461241090e70c50a308,0x3b2191f01c01a518a168,0x531c2f32ca2af29425d2,0x40a3e83c63ab39036734,0xea4cf4a648446944742c,0xf5b659457255052e50c4,0x6b969e67565362a6015d,0x9277074e7337186f66d4,0x85e83c81a7ff7e47bb7,0x95393190f8ed8cb8a988,0x3aa189f69db9b9997975,0xeadcac1ab4a92a62a4ea,0xbaeb9ab7fb5db42b20af,0x87c65c51c28bffbe4bc9,0xfd1bd00cecccacb6ca2c,0xdc3dafd94d72d57d43d2,0x4fe34e20e13df8debdd7,0xe207c0144e99e85e6ae,0x3e00a24209802890b005,0x82c3e00a20709802882c,0xf0062c3851420b0f8028],#[0xe1300510587c0144431,0x144062300c0c384c0144,0x7c0145c42d08309806c0,0xc3601820b0d806081058,0x38032004104078078e2,0x28202101e0148601e182,0x82c207c014516103e00a,0x3081f005162840f8028,0x1e1300c107e01818bc03,0x1c31f8208710260182c4,0x403823862f0070c2600d,0x8184838038b14260821c,0x4c0304484300c105e01,0x12110c0144098060b108,0x28b14242c01441780288,0xf8028a2c3e00a2048580,0xe01e2040e1700b1420b0,0x3f00c0c101160f00a401,0x1e010786c03041780606,0xb1026018184c0303c486,0xf00514205c01c40e1700,0xc0303020820bc028b081,0x304098078c105e00a18f,0xdc03051e3700c1026020,0x7e01820dc02c6084078,0x890c0e0202031b807881,0x806882c2601820f19806,0xb4210188370101820b07,0x6844080d08f1018b0818,0x203181a108286082031,0x862c116890a0105a2428,0x858310242440c416101],#[0x1882c3050c2228214409,0x70c20708586061844404,0x28b100c308081862c40,0x842c2428300509091418,0xa084061a28210189041,0x18208890a0101860a08b,0x10b0a10f0a10b080c342,0x3068a090105834218f0a,0x40610b181101810b821c,0x31e14216084442c31608,0x4407890e0901e18f4418,0x16883062c28]]
def g187H7 := limbs80 #[#[0x21000b041838022ac980,0x4901021c00b065000c2,0x105060c08d004642000,0x8000214d132e0ca81081,0x20644b811218e850ec6,0x4220c8829e0528038180,0x63000154000092004413,0x60f49dabd0b118d051fc,0x2600004d738bcc40d157,0x1ccd4eb80c18674a3,0x7d33000500a4efae4e6b,0xd536330949782a9a1b5c,0x1ed3a1d4831c7b72fee,0x1add1765fb12ea000,0x65d4d2814029a2360000,0x52e4548349b2c6b20,0xdcacb28b48000184000,0xe690f53000000093a800,0x4092000f2b000088aed,0x6f0004a2253dece0091a,0xb9884aea0000003d422,0xd22feb8b77eb4e030006,0x1388000e07626cd36d24,0x3ca8718d627d63aaf63f,0x868dbea1e8d664cb69f6,0xc000442f8df52800092,0x198003460000707b0050,0x310000b49b455cca405f,0x5113d31652000422a,0x22aef6300038c8000000,0xe0000002c10057f1a99b,0xd40008dc15b586e0fee8],#[0x3bc338c01dd2000f4db5,0x154ab92610e741df,0x6c30002566761669c0d0,0x15774c13b2da970b2,0x4000b5c0a8d8ba0e1000,0x9b02f4c2668f8d7cab09,0xe38d1f53e84417facca0,0x3e0003c7600000000014,0xf5fc3839e0a13d600734,0xb1f27432569ba840,0x2a6200028b20f24f4795,0x400068500012200168ce,0xc6c8d61796ac0f9ce4d6,0xd0fa084113cedb731d,0x87104f81d36254cbcb60,0x1deb352b34a6aeec0000,0xe9b12b00d00048930fb,0xac900000c7356e22f22d,0x3a6a922cc61b08001a8,0x7cd0e8b9eaf4f2000c5,0x208026dc191d9c28e1b9,0x82200071b4000172b,0x45d085409e07b067bab0,0x293f187f8c3d3aa32000,0x5b4e4b6ec8600002391d,0x2133cae00038780014b,0x64b65db00001a8ce0b00,0x2f257d676aa9dc0869ec,0x11f5628001c4c00073c0,0xa5b6cc4fb2c5113509b3,0x18e7c55408f724653715,0xab5dd0000b4e800000],#[0x1c7060202d2aa84a900,0x1621b8000429025fa0b0,0x166648d6f8002995c3f1,0x54b4dbe50fa5c32a0b5d,0x2748000]]
def g187D8 := limbs80 #[#[0xe20fe907f843fa21fc10,0xa1fd50fe287f8c3fa61f,0x3fea5fd52fe997fd43fc,0x409a4b44e1f8c03c0f00,0x107120144cf5eac53e90,0xa03040841e014520680c,0x1442203031818071011,0x80c1040812c78051c80a,0xd010f80c1441e0144044,0xd80c1413cd80c14d80c0,0x140]]
def g187H8 := limbs80 #[#[0xc1430016100090014681,0x850d88000004cdc91,0x797365564c101400600,0xa15d9f725124c0183a00,0xc003dcfb75fb1124503c,0xd952cd78566e7e4aacf,0x6d72dd300024200000e7,0x4003c417c0d7ec7c45e4,0xdb258db27416885b6a51,0x3c000c4d9bc000000a35,0x8e80025c2c718c975b0,0x974001d5c4a400000188,0x3c508cfcb981201f058,0x6c8a29bc4452386b8e00,0x36c000ced3880028dc73,0xb4036157478630d45786,0xe091d9393f57023c002c,0xf519080014f076224548,0x3cfb494002848000000,0xc00d2a1940021b68240,0x19cd3a9a9f311adf6400,0x20b0001984000001,0xc0019a256f641b57e380,0xddf4740028bf7796fec2,0xdde28091c733b5991d5,0x8518d071d254851c90d0,0x581568002d5b01a03109,0xc609e96369e553c28001,0x17ae060b5e80534d8d50,0x1c80026978f5d400030d,0x4d456588000000d37039,0x3dbbcaf9a67290655]]
def g187D9 (j : Nat) := if j=0 then 0x8200ff else 0
def g187H9 := limbs80 #[#[0x15600201662735c12072,0xb90008cd3e7401b42d00,0xce00192f7f41da420092,0x79bf06266a2ae403]]
def g187L : Nat → Packing
  | 4 => (6,5,5,0,0,5,0,g187D4)
  | 5 => (80,4,5,0,0,10,0,g187D5)
  | 6 => (238,3,5,0,0,12,0,g187D6)
  | 7 => (121,2,5,0,0,12,0,g187D7)
  | 8 => (14,1,5,0,0,9,0,g187D8)
  | 9 => (1,0,5,0,0,0,0,g187D9)
  | _ => emptyPacking
def g187I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 7 0 7 3 0 g187H5
  | 6 => lookupWord 23 157 5 12 7 1 g187H6
  | 7 => lookupWord 77 379 7 13 8 1 g187H7
  | 8 => lookupWord 38 191 7 12 7 1 g187H8
  | 9 => lookupWord 6 31 4 9 4 1 g187H9
  | _ => fun _ => none
def g187 : Forest := ⟨187,9,fun i => g187Y[i]?.getD (0,0),g187C,g187A,g187L,g187I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P4_0 : block g187 4 0 6=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g187B4 : block g187 4 0 6=true := g187P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P5_0 : block g187 5 0 80=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g187B5 : block g187 5 0 80=true := g187P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P6_0 : block g187 6 0 21=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P6_21 : block g187 6 21 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P6_117 : block g187 6 117 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P6_213 : block g187 6 213 25=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g187B6 : block g187 6 0 238=true := (@block_merge g187 6 0 117 121 (@block_merge g187 6 0 21 96 g187P6_0 g187P6_21) (@block_merge g187 6 117 96 25 g187P6_117 g187P6_213))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P7_0 : block g187 7 0 10=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P7_10 : block g187 7 10 63=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P7_73 : block g187 7 73 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g187B7 : block g187 7 0 121=true := (@block_merge g187 7 0 10 111 g187P7_0 (@block_merge g187 7 10 63 48 g187P7_10 g187P7_73))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P8_0 : block g187 8 0 14=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g187B8 : block g187 8 0 14=true := g187P8_0
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
  · exact g187B4
  · exact g187B5
  · exact g187B6
  · exact g187B7
  · exact g187B8
  · exact g187B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187G : graphValid g187 (boundsBefore K175) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low187 : Lower true (varsX 187) (graphGoal 187) 10 := lower_forest (g:=g187) (i:=0) (hints:=65603) (before_sound K175 V175) g187G g187T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K187 := extendKnown K175 10 [(187,[]),(250,[96,32])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V187 : Known true K187 := extend_ok (m:=187) V175 low187 (by decide +kernel)
def g189Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xe003ffffffffffffff,0xfffc45acaf050000f0ff])),(BitVec.ofNat 152 (word80 [0x411822008a02140288,0x127c4508020511111111]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffc007fff0001fffc,0x37bc23568c000f0f00])),(BitVec.ofNat 152 (word80 [0x82504b012c07580b10,0x27370c22568c33333333]))),((BitVec.ofNat 152 (word80 [0x7fffffffffff,0xff902573edb900f0000f])),(BitVec.ofNat 152 (word80 [0xc618c2a305460ac21,0x44002073edb866666666]))),((BitVec.ofNat 152 (word80 [0x7ffffffe0000,0xecd578e4a0f000000])),(BitVec.ofNat 152 (word80 [0x1782f033c06780cfc2,0x780ecd578e4a77777777]))),((BitVec.ofNat 152 (word80 [0xffffff800000000000,0x8bacf93a6f0000ff0])),(BitVec.ofNat 152 (word80 [0x1803003c007800f003,0x8000b2c5812244444444]))),(0x0,0x0),(0x674250407afffff000,(BitVec.ofNat 152 (word80 [0x400080010000,0x88888888]))),(0x0,0x0)]
def g189C : List ColumnInfo := [(16,0,173,0,7),(1,0,188,0,6),(4,0,185,0,6),(8,0,181,0,6),(32,0,157,0,6),(0,16,45,128,5),(9,0,180,0,5),(12,0,177,0,5),(17,0,172,0,5),(20,0,169,0,5),(36,0,153,0,5),(48,0,141,0,5),(52,0,137,0,4),(128,0,45,0,4),(128,16,45,0,4)]
def g189A : List (List Nat) := [[],[80,50]]
def g189D3 := limbs80 #[#[0xa822158197d4d4250110,0x8558d504426832442ac6,0x6304c4650]]
def g189D4 := limbs80 #[#[0x5c75344274602754c510,0x44233e0976d4d109d380,0xd4d425011089f845db53,0x50110f816350940443e0,0xda17550940443e05cd42,0xd4d4044368dd54250110,0x4427461f5350110b9184,0x5514254110b938458d40,0x541109e08750950443c8,0xe536558d50443c455143,0x19550442d42156354110,0x442cc6106554110b6182,0xe116350910bc180d4d42,0x50d10a948655143442e1,0xdc3825c3534427460275,0x5d35344274e1170d4d10,0x44271e0976d4d108d786,0x6087558d10997845db53,0x55110995841d56344271,0xc35655d0654427460373,0x5d2654c21de1d6519510,0x54235e0576d4d408d781,0xe0970995318d7815d363,0x583538cf825c36354633,0xf060240c030023361372,0x433180b45427120642c0,0x4ac53261248c43200f47,0x1c4dc6b34194c45f2e16,0x10c83401f4f4773a,0x2684100920800,0x14820000000002608]]
def g189H4 (j : Nat) := if j=0 then 0x2e2d else 0
def g189D5 := limbs80 #[#[0xee8b86a6887a14250110,0xfa262a822133dc960d4,0x436bb2a62886d5654c51,0x10be6e0a8a21759d5314,0x442f8b86a2885d773545,0xd10bb2e1a9a219dd9751,0x54426ebb6a6885d571d4,0x11097ee8b2a213bdc96,0x40443e8b1a80887d3535,0x50110f62a8a0221f45cd,0x540442f8baa80887b364,0x254110fc284a82217cdd,0x4d50443e8a1aa0887e37,0x7354110fa2c6a8221f4d,0xd5150443b8aa2a0887d3,0x6554110be6e8a8221dc,0x8dc142443b9b2aa08877,0xc56350910f8ea6a1221f,0xe5d9143443caaa286887,0x5d57650d10baceaa1a21,0x1755d353443e8b86a688,0x85d776d4d10baaeda9a2,0x21b559563442ebba2c68,0x885d47558d10daecab1a,0x2213d1d954442ebb9aa8,0x8885f170d51109eeecaa,0x2a21795c865442eab9ec,0xca885b57419510baae63,0xb2a2179dc9654433ab28,0xcca885b77459510baee6,0x4a8261755cf654433bb2,0x8aa8987595454130f96e],#[0xe932a61375c6654c2ebb,0xb86a6a073954541409ba,0xee2b2a81375db53502ec,0x7b1ec4a86cf624c5509e,0x9ee7b12a1b3d4f625436,0x6eb8ec6a84ed74d8950d,0x9eee2b26a1375d363542,0x66eb84ca98dd77054531,0x39dee4b06a3375c36354,0x4e6fb8ac1a9dcf725835,0x539bee8b06a7b3dc960d,0x2106a14036004df70587,0x439023d8dc340c42e0ac,0x6297e5914a4f9324991a,0x96a32829f0759ca6f996,0xb92d8afab2a9a8ca0274,0xe638ce0366d3340c9b0c,0xfc330640cfcbe6efba4,0x2ecaf28c9722c7f1cc59,0x515394b52141ced34cc7,0x6cda766d8f60d775ad5f,0x88615825fd78dd772dbf,0x981270b807946458e62d,0x60800000240015306882,0x100890400000000002,0x4530a9824c1000260820,0xc100026080046044d308,0x118080401200a9a81004,0x90406840212080000cc,0x4824c1001020,0x80000381c0089040000,0x400000000000000001c],#[0x8]]
def g189H5 := limbs80 #[#[0x981000000054002a2c32,0xe12c500000000042,0x0,0x0,0x407b92745000c9400000,0x7c00000dbcf3400000a2,0x71053a000000000382,0xf0c46c00000001c44,0x30000000000014600000,0x7d90000000045,0xc66809ca00100c000000,0x90800e1f,0x0,0x0,0x1c20,0x1a6000000d2c00000000,0x46c8500000087000d1,0x1c505d43a4e0000,0x0,0x162c00,0x4ac000001a,0x427230000000,0x80000000000000000000,0xb9200393000001e6]]
def g189D6 := limbs80 #[#[0xc50110b758d10f54c510,0x50d10f950910fc54110f,0x4f10f558d10f5d4d10f5,0x530b759130f654130f5d,0x31b7d8d50bbd8950b799,0x3b7d8d51b799531f5545,0xfe54110b758753b75835,0x7d4d10fdd4510fd54510,0xd9510bf59510f758d10f,0x9110fdd5110fd55110bf,0x510fd19510fdd9110fd5,0x30fdd9510fd99510fd59,0xfe54140f755130f7545,0xbf59540f758d40f7d4d4,0xfd8550f74c550bfd9540,0xd8d50f7d4d50fbd8950b,0x9150dfd5150df55150f7,0x151bf59350bf58750bfd,0x51f7d8d51f7d4d51bfd8,0xf758753f758353bf583,0x742884506609c0c00c00,0x5589f12c234408750d21,0xff1ec39c6d8d21862dc,0x629a5049a92923444484,0x4e66cc91863005d0b115,0x7a4f01d43966f0d99ad3,0x518a2843885906a013ea,0x4cc1cec9b52f2524928f,0x6030616032824d51c194,0x130714cd869c582908a1,0x31070684d507a1330712,0xb3070e014c684d4c706],#[0xe00b50939b5067144860,0x1261607086aed066ac14,0x802104842c412008481c,0x2806a028062820062881,0x9840a02840a01a0504a0,0x1c1040a01a00a89a01a8,0x2164042827024247064,0x28014671218a00428610,0x846813066c64061c3806,0x70601c10a18019c0880,0x21b10019a48428200610,0xa0a628418201c]]
def g189H6 := limbs80 #[#[0x4c0313cd85b028009081,0x1240000000,0x1c36c9600000092a0,0x0,0xcac001a34000e22e60,0x2a8a5ea880940000000,0xc33382c2068,0xc7c00000042da18,0x1f81405a10000a3be440,0x0,0x0,0x0,0xc9200000163809806200,0xa6c615078001,0x66e0000000000000000,0x0,0x65a00187a001a2a000,0xf870001155a578758080,0x89c0aa001a7,0xa0000000001e3000163e,0x1c8c0000000,0x1e0c0000000000b,0x32001d44000000000000,0x41600000000154e1,0x52e00000000000000,0x5268f26bb24000000000,0xe58363c836,0xc43490000e0600000000,0x48e66c76001aae000000,0x161228a8020001,0x118aa0eea6527c0a00,0x1c0000014a000],#[0x192042f669055c720000,0x4a4e28000001ca200000,0xc6512da4845c001,0x184605173a0000000,0x24ca3d62600000000000,0x1c1e000000,0xa00189e0000000000000,0xc24e9a00024ea4,0x58ef66000000000,0x968400061a41c0000000,0x1286000000f6]]
def g189D7 := limbs80 #[#[0xf53ee98f74c3ee21f510,0xa3ff50fea87f503fa21d,0x87341245e1a007fd47fa,0x83152061230f96d2ed42,0x615d13a922bb46409032,0xae828c23a0650970375,0x13c14290503385710503,0x13c14e15c]]
def g189H7 := limbs80 #[#[0x320021120500008000,0x1440000b0001f21d88,0xa0000000076c00000000,0xc9e900001628,0x9911b92b003695a60000,0x18861c7dab3c2be,0x292800000e2000,0x68000002170006df8a00,0x84b4c71a000003571a86,0xdb00024fe1d,0x68f7d14001c2b9100000,0xca44000548000000008,0x156c00000000000003,0x148c0058f,0x79f454b440037400,0x8de000000000000,0x80000060c0000000152c,0x6300000000,0x3a000000000000000000,0x38300078400000000c,0x11a80000000000000466,0x122c0078900000,0xa08000000000000,0xcadab40000000041c000,0x2ac0028400168000000,0xce000001b180000000,0xd600000049d098009320,0x11e1]]
def g189D8 (j : Nat) := if j=0 then 0x7a6013f else 0
def g189H8 := limbs80 #[#[0x18006ac0000,0x2000298010600000,0x1d315f000005a562170,0xe00001d64800b9506800,0x884cd0a4]]
def g189L : Nat → Packing
  | 3 => (3,5,4,0,0,4,0,g189D3)
  | 4 => (39,4,4,0,0,9,0,g189D4)
  | 5 => (89,3,4,0,0,10,0,g189D5)
  | 6 => (57,2,4,0,0,11,0,g189D6)
  | 7 => (11,1,4,0,0,9,0,g189D7)
  | 8 => (1,0,4,0,0,0,0,g189D8)
  | _ => emptyPacking
def g189I : Nat → Nat → Option (Nat × Nat)
  | 4 => lookupWord 1 3 0 6 2 0 g189H4
  | 5 => lookupWord 12 181 1 11 6 1 g189H5
  | 6 => lookupWord 27 277 3 12 7 1 g189H6
  | 7 => lookupWord 18 191 4 11 6 1 g189H7
  | 8 => lookupWord 5 37 4 9 4 1 g189H8
  | _ => fun _ => none
def g189 : Forest := ⟨189,8,fun i => g189Y[i]?.getD (0,0),g189C,g189A,g189L,g189I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g189P3_0 : block g189 3 0 3=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g189B3 : block g189 3 0 3=true := g189P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g189P4_0 : block g189 4 0 39=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g189B4 : block g189 4 0 39=true := g189P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g189P5_0 : block g189 5 0 3=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g189P5_3 : block g189 5 3 86=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g189B5 : block g189 5 0 89=true := (@block_merge g189 5 0 3 86 g189P5_0 g189P5_3)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g189P6_0 : block g189 6 0 19=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g189P6_19 : block g189 6 19 38=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g189B6 : block g189 6 0 57=true := (@block_merge g189 6 0 19 38 g189P6_0 g189P6_19)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g189P7_0 : block g189 7 0 5=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g189P7_5 : block g189 7 5 6=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g189B7 : block g189 7 0 11=true := (@block_merge g189 7 0 5 6 g189P7_0 g189P7_5)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g189P8_0 : block g189 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g189B8 : block g189 8 0 1=true := g189P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g189T : checkedTables g189 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g189 0 0 0 = true)
  · exact (rfl : block g189 1 0 0 = true)
  · exact (rfl : block g189 2 0 0 = true)
  · exact g189B3
  · exact g189B4
  · exact g189B5
  · exact g189B6
  · exact g189B7
  · exact g189B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g189G : graphValid g189 (boundsBefore K187) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low189 : Lower true (varsX 189) (graphGoal 189) 9 := lower_forest (g:=g189) (i:=0) (hints:=460035) (before_sound K187 V187) g189G g189T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K189 := extendKnown K187 9 [(189,[]),(190,[16,67])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V189 : Known true K189 := extend_ok (m:=189) V187 low189 (by decide +kernel)
def g207Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x7fffffffffffffff,0xffc055367a50000f00ff])),(BitVec.ofNat 152 (word80 [0xd01482802a0250148,0x29c005144a5111111111]))),((BitVec.ofNat 152 (word80 [0x7ffc01fff0007ffc,0xf334695e8000f00000])),(BitVec.ofNat 152 (word80 [0x5615914c94c5b62990,0xccf334695e8777777777]))),((BitVec.ofNat 152 (word80 [0xff800001ffffff8000,0x26278cbf400f000f00])),(BitVec.ofNat 152 (word80 [0x9819e2702701380de1,0x7006278c3f4333333333]))),((BitVec.ofNat 152 (word80 [0x1ffffffffff,0xfe580f6a35b0f000f00f])),(BitVec.ofNat 152 (word80 [0xe01e03803801c00e01,0x80180a6a350222222222]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffe0000000000,0x24f859c3ef0000fff0])),(BitVec.ofNat 152 (word80 [0x200000c006003002,0x20d00180a444444444]))),(0x19b82850c0fffff0000,(BitVec.ofNat 152 (word80 [0x4000010008004000,0x888888888]))),(0x0,0x0)]
def g207C : List ColumnInfo := [(2,0,205,0,8)]
def g207A : List (List Nat) := [[],[48]]
def g207D8 (j : Nat) := if j=0 then 0x7f else 0
def g207L : Nat → Packing
  | 8 => (1,0,1,0,0,0,0,g207D8)
  | _ => emptyPacking
def g207I (_ _ : Nat) : Option (Nat × Nat) := none
def g207 : Forest := ⟨207,8,fun i => g207Y[i]?.getD (0,0),g207C,g207A,g207L,g207I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g207P8_0 : block g207 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g207B8 : block g207 8 0 1=true := g207P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g207T : checkedTables g207 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g207 0 0 0 = true)
  · exact (rfl : block g207 1 0 0 = true)
  · exact (rfl : block g207 2 0 0 = true)
  · exact (rfl : block g207 3 0 0 = true)
  · exact (rfl : block g207 4 0 0 = true)
  · exact (rfl : block g207 5 0 0 = true)
  · exact (rfl : block g207 6 0 0 = true)
  · exact (rfl : block g207 7 0 0 = true)
  · exact g207B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g207G : graphValid g207 (boundsBefore K189) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low207 : Lower true (varsX 207) (graphGoal 207) 9 := lower_forest (g:=g207) (i:=0) (hints:=1651) (before_sound K189 V189) g207G g207T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K207 := extendKnown K189 9 [(252,[32,65,48,80,16])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V207 : Known true K207 := extend_ok (m:=207) V189 low207 (by decide +kernel)
def g219Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x1fffff87fff6a323,0xb48680000007f01fc07f])),(BitVec.ofNat 152 (word80 [0x9402801102206a022,0xa082850a142850a14285]))),((BitVec.ofNat 152 (word80 [0xffe003ffffff0205ed,0x63cb000003f800003f80])),(BitVec.ofNat 152 (word80 [0x2184b08a010422056d,0x224b13264c993264c993]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffc0007fffb1ad1,0x92518001fc000fe0007f])),(BitVec.ofNat 152 (word80 [0x200c02c20480912d1,0x12400a142850a142850a]))),((BitVec.ofNat 152 (word80 [0xfffffffff80008caba,0xcb8c00fe000000003f80])),(BitVec.ofNat 152 (word80 [0x4c090130027048ca92,0xc9842c58b162c58b162c]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x92d42,0x4c3f7f0000000fffc000])),(BitVec.ofNat 152 (word80 [0x700e01c04380800d00,0x4c3d3060c183060c1830]))),((BitVec.ofNat 152 (word80 [0x4d414,0x28607ffffffff0000000])),(BitVec.ofNat 152 (word80 [0x801002000400000000,0x4081020408102040]))),(0x0,0x0)]
def g219C : List ColumnInfo := [(1,0,218,0,8),(2,0,217,0,8),(8,0,211,0,8),(16,0,203,0,8),(64,0,155,0,8),(18,0,201,0,7),(0,2,73,144,6),(0,16,73,130,6),(128,0,91,0,6),(3,0,216,0,5),(9,0,210,0,5),(10,0,209,0,5),(16,2,73,128,5),(65,0,154,0,5),(66,0,153,0,5),(72,0,147,0,5),(128,2,73,16,5),(128,16,73,2,5),(73,0,146,0,4),(130,0,73,0,4),(130,16,73,0,4)]
def g219A : List (List Nat) := [[],[99],[65],[65,99],[48],[48,96],[48,65],[48,65,96],[96,48],[96],[96,65,48],[96,65]]
def g219D4 := limbs80 #[#[0x50c8ae1192d915254110,0x30c4ae13925d152d41]]
def g219D5 := limbs80 #[#[0xa8221a2b6460b5454120,0x6454950442cd325b22a4,0x94aa2a5b82848868ee13,0x12214e9921977050910e,0x5dc1424429b32632ee0a,0x4c94cbb82848843e6606,0x2210f9989977050910a7,0x5c86544315ee8c16c8a9,0xc1a84a8a809053ae4184,0x41aa98650b5150120dc5,0x49404839572eb2a84a02,0xa2eaa92809078ae59545,0x1c6b965d55250120e95c,0x55048369706a92a2a824,0xaa4b8aa0904ce6508558,0xe29645515254120da5c1,0x50483a56e8aa2a4a8241,0xa8a92a09059ae5954549,0xab84dd15254120f15b26,0x483c56e9b22a4a82419,0x8a92a09059aa5f645495,0xb745537254120d95c26e,0x48335309ba6e4a8241d2,0xaa2a0905ca64b5455150,0x6460b5454120d55b2305,0x8256f28c36a2a8a41e2b,0x2ea290527e5165dcd514,0x4e0176d452085fca30fb,0x287b283aacab0a418b88,0x2a89062ee13805d95448,0x5c970d5120c74c1301bb,0x13ec9c1ae3aa241cab64],#[0xca9066ae0b80dd165483,0x17159520e55ba6e5b82,0x38e9c1ae2b2a418b874e,0xa90627dd3835c5654831,0x3745952085f4c0e8b8ac,0xf26c0ee8b2a41aab82e0,0xa855ae497454b5054293,0x6258550c9dc22e8a96a0,0x9ba6e0a92a189f84dcd,0x852ee4174d9352543273,0x458b50b1dc82e9b26a4a,0x9018030018af74e096,0x8210781b060150480f03,0x5c16451124410f8360b,0xc88214821d4721a86719,0x4aa29c9f270992588e22,0x8db338cb2f8b62ccb02b,0xfd3e8f73a8e7390e137,0x431094190340,0x8080d05400400000000,0x814003a103a1020648,0x28540040600080050,0x1d182000001a0800,0x11801016168011800800,0x1322c81000000006]]
def g219H5 (j : Nat) := if j=0 then 0xd1a000c9 else 0
set_option maxRecDepth 16000 in
def g219D6 := limbs80 #[#[0x54940483aa5954250120,0x4835a5d55250120f2954,0xd915254120e696454950,0x54120d6b74549504839a,0xe3b64d5150482da60b54,0x5d9544822fe1176d4520,0x4832ed9170d51208fb80,0x1d37059520a3d85d9354,0x54110f6952509504432e,0xf6b7254950442de61542,0x549504439ed915254110,0x4439e2195254110b7b84,0xa1f6254110af984d8950,0x54510bbb845c950442be,0xcf774d8951442fce0142,0xdc951442bd6136254510,0x4437a54b70509109f584,0x9977050910cf865dc142,0x509109f985dc1424433e,0xaed8219542443cb55152,0x19542442b760c6550910,0x442b7e0d65509108fd87,0x60a65509108ff8759542,0x509108fd8799542442bb,0xaed82d91524427ee0175,0xd91524432fdd36454910,0x4423fa1f64549108fd87,0xe1574d8910a7d859d952,0x195108ff845d7624423f,0xced845c8654423fe1172,0xdc9654433be117219510,0x4823fe1172995108fd84],#[0xe0d5150120fa94254540,0x50120fa942d4540482f6,0xaf986d4540482fa60b51,0x54940483ea5515250120,0x4837a5d55250120fa984,0xe096550120deb8754940,0x50120ebb8459540483ba,0xf6952545504833ee1d65,0xd4550482f6e0d5154120,0x482fa60b5154120f6952,0x2156154120f695258550,0x54120b7b8558550482de,0xbeb825c550483da54971,0xdc550482f6e0d7154120,0x483da5515254120f6952,0x5915254120f6b5454950,0x54120eeb6454950483ba,0xf6a65549504837add152,0x54950483da5d15254120,0x483da5537254120f6b74,0x5d37254120f6b54dc950,0x54120deb74dc9504837a,0xf3b5455150482fa61372,0x551504836edd15454120,0x483da6095454120afb86,0xe195454120f3b7455150,0x54120be982d51504839e,0xf6982d5150483aed9354,0xd9150483aedd36454120,0x482fae097454120afa87,0x60a6554120deb82dd150,0x54520bf180d4551482fa],#[0xcdd64dcd51482bd61b51,0xdcd5148337d937354520,0x48337d977354520cdd65,0x61b7454520cbf74d9151,0x54520abf84595514823f,0x9df835d9514827ee0176,0xdd9514826fe117654520,0x4837a5c970d45209f980,0x59170d4520deb825c351,0xd4520cfb645c3514833e,0x8fd87593514827ee1170,0x5d3514823f61f64d4520,0x482afe1165d45208ff86,0x61f65d45208ff8759751,0xd4520abf845db514823f,0x9bf845db514827ee0176,0x5db514833ee0176d4520,0x4832fe1176d4520cbc84,0x61e76d45208ff845db51,0x585209f980ddb514823f,0xc7c7559561482afe1165,0x1d5614831fdd56558520,0x4826f61075585209dd83,0x6037155120de9725c154,0x551208fd86dc5544827e,0xe3d65d5154482ee60354,0x59554482af61b5455120,0x4839ee016555120abf84,0xe017655120e3f8459554,0x55120cfb805d954482be,0xde9725c3544833e60376,0x5c354483aed9170d5120],#[0x48277e0d71d5120deb82,0x61764d5120cbf645c754,0xd5120abd87d9354482af,0xe3f84597544839ee0165,0x5db544833ee0176d5120,0x4832fe1175d9120cbf84,0xdd37059520deb72dc165,0x59520cbf76dd1654836e,0xcbf86dd1654836ee0374,0xdc165483badcb7059520,0x483aedd37059520eb874,0xe017159520af984dc165,0x59520adf835c565482be,0xcbf745c5654832f1d171,0xdc565482afe117159520,0x4832fdd37159520cbc74,0xe017459520abe871d165,0x59520ebb80dd165482be,0xcbf81dd1654832f60774,0x5c6654837a5c97099520,0x543dad8952d41509df83,0xe1152d4150d797454b50,0xd4150bbb8458b50542de,0x9fb845cb505437a5cb62,0xd895154357dcd5254550,0x5433b5cb62d4550cdf73,0xdc952585509fb805cb51,0x58550d5f73549615435b,0xabf845896154337dcd62,0x58b6154337dcf6258550,0x5433b5cb62d8550abf84,0xd8b70549508ff845cb61],#[0x54950d7954dc152543ba,0x9f984dc1525435ed5370,0xdc1525432fdd36454950,0x543dae0b7054950f6b62,0xdd37054950d7974dc152,0x54950b7984dc1525435e,0xd3f74d9152542dbe0964,0xd93525439be0b6454950,0x5427ee0174d4950cbd74,0x5d364d4950b6f8259352,0xd4950e3d74d93525434f,0xd7b805d352542dee0174,0xdc1625436e1d37058950,0x5436bdc87458950dbb74,0x60b64d8950dbb80dd162,0x58b50adf835c762542bb,0xafb805d162d42bbe0964,0x5c3515463fe1172d8151,0xd46bee0162583519f782,0x6137258351abf845c960,0x2b821012009c0600023f,0x5851c4e04c846840833c,0x869c68464860c5d05945,0x81c7e07c87447086f06d,0x789188b88a088884c834,0xb04aecab0a74a389d89,0xca8c90c54bf4bb8b7cb4,0x70decdd4d98d5ccfccc0,0x50f90bd038ffcfc0ed0e,0x3753392912551f519513,0x8162157953d5014593d5,0xd89d83d7dd77d71d6bd6],#[0xb85b25ae9aad9e195d8f,0x71d35cf9cbdc81c21bc1,0x1f21f09ecde91e31dadd,0xc60ae09605a01dfbdf8,0x4620a1ce19215611a102,0xe3d23ba37e3422be2822,0x52e4ce4b647a43e42640,0x8a67263661e5e25a656a,0xa7aa76e73271a7026c66,0x9ba97e9428e28a686a80,0xa6afeac2a86a6ea329f6,0xed32cf6cbaca2c42c06b,0xeb2e76e3adfede6daad6,0x7b03efdefa2f66f2aeca,0xb1e31cb16b10b0cf0b70,0x3ab36f3572f72732371f,0xe34cb48f45343b4233e7,0x36275eb5af57353751f4,0x73b72370b6cf6b769f66,0xbb87f8438077a778f777,0x39b797b9639278eb8d38,0xb13ad7a9ba5fa47a0b9f,0xb7c9fc63c4bc0fb8bb4f,0x415240bd5fd47d0bccfc,0x31d8c08181ba4a106120,0x28363b1814e4101e0d05,0x82450441b64080a0f724,0x10903c2040f1e84206f0,0x200401630200068c0b90,0x40d1805001f041000080,0x21161820002002001a30,0x881d10002d16002c0010],#[0x3020804020800407440e,0x40400000080400101810,0x4006039017202e46004e,0x520ac2801b09820ac682,0xd05508302020d041e0d0,0x2b481034041008109020,0x9d1ac680134808294810,0x40020ac21d1900160810,0x244048209068d6105824,0x305c2041202082763210,0x4040500040542c00480a,0x7028005007204087204e,0xa043928500141ae4a10,0x20804083c84103410002,0x1c1030a061408081a0,0xc209056404060804100a,0x2041ac2080c00208041b,0x8080068c1d18282c0040,0x10003a3040c08181018,0x20485a120060007800f0,0x841e002001c204003020,0x78008001d08204008406,0x81010008080000,0x211002047002e0020604,0x20204051408080208081,0x424080a40748080010,0x40f0a80102348c2a008c,0x120648084810309c0080,0x14082815202069010902,0x50a041408481b2308202,0xc2b182000017202e4850,0xc80b0010000258420758],#[0x502038dc2122ac8640e,0x40c0038004003000f001,0xd0010982010400081400,0x1010000002001a306c80,0x24006800a8a8010003,0x40800102800e0010002,0x7440820101020020100,0x4005028ab21903510340,0x720200001e182000000]]
def g219H6 := limbs80 #[#[0x218000248100000052,0x1a09481600,0x1038000,0x49a8,0x80000000000000000000,0x580e000680,0x405c000382e,0x283c00000000002c100,0xd21c0000000000000000,0x5035306,0x101380002208,0xa8a8001a179a3200000,0x5848000000,0x1e960000000481e,0x0,0x10880000000000000000,0xa270001e28,0x30ac000405a0000,0x5067200800000000,0x78622a63806000000,0x68592103814,0x68000000000000028260,0x6260001128000052,0x23e000302c000502b800,0x1,0x0,0x4a780000000001004000,0xc000000000000000001,0xaabe1b00000000000e,0x1018000000000000,0x2bc00000000000000000,0xe14b84400000000002],#[0xa0000000000000000000,0x780c6109a66c06906,0x58600000000,0x0,0x128f0001108585600,0x5000000000000000000,0x640000001c9200320002,0x18,0x6237e06000,0x8800000000000000680a,0x150600000010,0xfa1a0000000000000000,0x2a0000188e0005846c04,0xb8000000000000000005,0xea71a,0x104c0000000000000,0x6a4000062340000000,0x78000000000000000000,0xeb38000e2,0x8000000000000000,0x0,0x486e000000000000,0x80d80000000000000000,0x84205400000000005004,0x2a64007000040ec0682,0x0,0x0,0x0,0x0,0x58ba000683e000000,0x346a00000000000000,0x182281c08e400000000],#[0x0,0x6021c0a,0x240000000000784a0000,0x2a]]
set_option maxRecDepth 16000 in
def g219D7 := limbs80 #[#[0x26eb98ca884ed7219510,0xf5284a024137dcd6544,0x826eb9ec290769525412,0x2097ae832a413d5c4654,0x4426fb9ac3a84bf74595,0x510df6c4a8221de54950,0x14437bb12a2886f76448,0x8910bf6e0a12217ddc95,0x624427eba6c4884ff745,0x595109fae432a213f5d7,0x9404827eb94ca884ff72,0x254120df2caa0241fa54,0x5150483f5b92a0907e95,0x6454120ef6a8a8241de5,0xdd1504837db22a0906f9,0x970d4520bbee6a8a417e,0xf595544827ebb6a2905f,0xfd7655120cfccaaa2419,0x7e5c3544827fbb2a8904,0x67d65d5120d7ec9aa241,0x13f5d7644827ebb6a890,0x5bf7459520bf6e0b2a4,0x41af1d1654837db82ca9,0x904ff7459520d7ee8b2a,0xa413f5da65482fcb84ca,0xa877952d41509fae932,0xaa177dcd51542fcb96a,0xa4a84fd72d8550bbee6b,0xa92a1dedc152542fdb82,0x6a4a867f64d4950cfec8,0x9b12a16fdd162542beba,0xa2c5a867d64d4b509fae],#[0xe1a8aa33f5cb605467fb,0xa12a0884ff7258351bea,0x6e4a8221fe5c950443fc,0x6a9284887f54254510ff,0xfacaa1221bf19542443f,0x7fb2a84886fe6550910d,0xefaa8a92217f5d542443,0x2ffba2a4886ff6454910,0xdfceca9221bf1d95244,0x83fda8a80907f9515012,0x20ff6a2a8241fe545504,0x483fcb8aa0907f961541,0x120ff2a8a8241fedc550,0x483fcba2a0907fb5454,0x4520ff4caa8241fedd15,0x51483fab0aa2907f7515,0x54520dfac8a8a41f7dcd,0x551482ffba2a2906ff64,0x654520dfecaa8a41bf59,0xc351482ffbb2a2905fd7,0x64d4520dfac9a8a41fe5,0x59751482feba6a2906ff,0xd76d4520dfecba8a41bf,0xf9db51482febb6a2906f,0xfd6558520bfeeda8a41b,0x7fdd561482fe3aac2906,0x5ff7155120ff2e0aa241,0x1bf59554483dfaa2a890,0x6ff7655120dfaecaa24,0x417f5c754483fcb86a89,0x906fd76d5120dfacbaa2,0xa417fdc565483fdb82ca],#[0xa906fe6559520f7ee8b2,0x2a41bfdc5654837eb8ac,0xca906ff7459520dfae8b,0xa82a17f5c665483fcb84,0x2a2a87fb62d4150ff2c5,0x5a8aa1bfd8951543bea9,0x96a2a86ff62d4550efaa,0xc4b0aa1df54961542feb,0xb92c2a86ff6258550dfa,0xac5b0aa1df54b61542ff,0xeb96c2a86ff62d8550df,0xfaa8a92a1fedc152542f,0x7fb22a4a877f5454950e,0xefec8a92a1df59152543,0x2feba6a4a86ff64d4950,0xefec9a92a1df5935254,0x43fdb82c4a877d74d495,0x50dfac8b12a1fbd89625,0x543de3a2c4a86ff64589,0x950bfee8b12a1efdd162,0x25437fb26c4a87fb70d8,0x8950dfae3b12a17f5d36,0x625437eba6c4a86ff71d,0x58b50dfac8b16a1bfdd3,0x162d437eba2c5a85ff74,0x258351dfac4b06a3bfdd,0xc960d477eb92c1a8dff7,0x816008a02e0098001bfd,0xa0da06182b0132086039,0xb850026212208984001d,0x8a1be0d5866030216e0a,0x1d88a041a1fe0f987503],#[0x5822ae14b8a104ca2521,0x19b8cc064a30a1738b40,0x7823a61cb8e006ea35a,0xe22d91208624121ff8f7,0x109e24de26392b091a46,0xa62c195c0a9a53228b94,0x880c1a5f62ef9720b6a5,0x69e34799f0cca64631d9,0x9ba0dc26d63639ad0d52,0xa75a3a39ce0e4270e37b,0x79ef0f6a79e3c79df0ec,0x8a83240da020ff27e63e,0x53a25110a872433a1510,0x1da8e646ba3211828b64,0x4a9a51127a926483a3d1,0x13729a24c7a5e12e2966,0x24ffa7c13c29d24e5a70,0x814a2a3e51ba89143aa1,0xbe553aa51512a7a533a9,0xca163ab0e57fabb15aaa,0xb8a5bbada16aab4659ba,0xafa17b2bd25dfaec1732,0x2c32613b051812c025fb,0xbb2318fac6e62fb15188,0xc2cd6665b2e194ac9e64,0x930023144d0a67fb3c19,0xf00405e4e2c00708451b,0x944860200e5121393881,0x407c2c0101108444203,0x28511c2c010130b00203,0xe4e207c01015930b0396,0x4c562100910018b14404],#[0x85030985100c08261440,0x3159040540c52f0c001,0x4402446408c5a209168b,0x40462e4c008c514131,0x40c4810408c562139317,0x47938f860040287c20aa,0x64c2184440483800a08,0xa151d1820484110d8a1,0x1e02299308408474664,0x22970840c8807c4c2a1c,0xb029040ac2c004a51500,0x180c044851110120c2b0,0x807060301c2c0a4201c,0x1244a092845004293086,0xac2c007060301a42048,0x54012081c180c042a906,0x6e4c20a0f8f0b870228,0x1c08a641b0b022b8f859,0x1c1b8f0b8701908e3c2e,0x80c04487111040121028,0x4c2c0116410170b001c1,0x7801162101044298840,0x1c0101c309f130a87004,0x8b00101a9462763e4e2a,0x1028842726c440a21429,0x1928840f64c0a210444,0xb0060a11a21064c0182b,0x301c064a22229938f868,0xa2204702884040d07060,0x280503080706640301c0,0x8b931680508066085101,0x91b04562812f09101421],#[0x24186c18046091029918,0x1003c7248608528d8a00,0xf43a2810614210e89060,0x42a210090c1a8a003c40,0xc900840244221008182,0x8e083100704402440906,0xe084c484610d0a821611,0x2c283094261468215198,0x2151b082130963c21024,0xc3593082040a640880c,0xa04282192030850d64c2,0xa3c0090a141a8c870040,0x4a313060c8f004c1840b,0xa0644c01314928c4c18,0x4a306a10d128c1a844,0x4001b08406c0084c908f,0xc18928428406a1120e8,0x12843a1051284244c00a,0x844c0068410624c00c29,0x82423c0090a1d93001a,0x28312068700402c2450b,0x42a90224c0088a101b00,0x40081028230b02905120,0x21206108f004c185a4c2,0x8a0f001984312042a90,0x664636112930028324c,0x42b0b01904120419842,0x164620a0c8f00198440a,0xa8c2c183a34010141200,0x92214250a8488440080,0x11450428c882450842a1,0xc2c1a8c8440664a322a],#[0x30b640a8500403130962,0x2890031062a10c188a84,0x1208230034424a2c0102,0xa21435928830f64a2c0,0x864102a899030864804,0x282030a08640c481a20a,0x88424a2082810aa20990,0x228928838aa2083c9302,0xc0a20c890020ac0a2641,0x8420663610c359288324,0x40824c0a211901640419,0xc2190240640823019288,0x64620b0401883c122200,0x19882]]
set_option maxRecDepth 16000 in
def g219H7 := limbs80 #[#[0x20019a0a18082046c280,0x1022420016000810,0x4209142430a065820400,0x10d06483811208302260,0x6040019402002830220,0x1001808e001c0ab00240,0x1278d0202040033c3c18,0x60121202001801448091,0xd484120c200023c68f0,0xef005e7070d120600102,0xdad12a0000a0600001c0,0x88a113a05800000000c4,0x12103800000000000121,0x1829400000000cab1c8,0xa6ee892000000,0x58000000000000000000,0xcb015e0000213e000009,0xe024a077e1,0x1a00861bfa0d0000000,0xe3cc00000000000000,0x439101b2427589aa00,0x14165319d60f400,0x58000000000000c2c600,0x4e0001313ca06e3439e1,0x76000008e8204d80a2e1,0x4000103b000000001a8,0x39101a0000000170e921,0x1a089d89300000495761,0x1400e8b2ef4,0xc360bef44cc815618400,0x4dc16021a6a00c6148e0,0xd58153a47ea0c7200510],#[0x38c0aaa10e21d288bae1,0x1e382e05281ce000100,0xb760448b1fa1d8000000,0x148b800000000000121,0x120e502b200,0xfe0000b02c215a000000,0x1808e81b862a7812ba0,0x408200006068000000,0x0,0xdb20d8e4660000000000,0x1088b8987a0,0x2c09796c220000218600,0xf50041a1672999481941,0x890a71bde92c411a24,0xac0001c8dc0000000000,0xf6608483d2823fe1a1c0,0xa02b180000217f4178e0,0xaf2207f03dd43de09a88,0x880001e15c012200106a,0x41806a21628823e99a20,0x140b3a0dc000140e9a9,0xc1320000000000,0x68011800000001e9a600,0x3560740ab7620c819a11,0x1a50c00010029016a0b,0xa4e0ba0000818b42be00,0xe00001cb1d4b3380bce9,0x1ab9a0001816f80,0x7f8002e1a80001011e00,0x1503200000000002e80,0xaea1776073c22f42c400,0x17048200000000000161],#[0x4ba3c800004065418da1,0x90000000000000814141,0x9fe0de00000000a115c1,0x183acc01d81,0x101340001088c00,0x800000e198e094000000,0xaa730193c21a000021,0x640000c92a639c000000,0xeda38dc0660000000085,0xcf00d44169291962,0x62925a018c879480e00,0xe68486446a0001e07800,0x98e0a0e0d3e56f51b400,0xe53720b548a3c87b62,0x42b8e17a0000cad800,0x1ca1280000c174202600,0x81bc00016182000009,0xa8a252e291ec8da2ba00,0xd70901e2cc80ae819420,0xcb058e00000001e14481,0x93655ec091204a000108,0x7cc102699cc14dd0132c,0xf261a3c070813b2b2100,0x9c2a6cb340d19a81c320,0x30401529af01c5238b01,0x2fe0922000209e804301,0x24000180e20001404e61,0x142d340620000d1,0xaa01be17200006a0400,0x5c217da171a0ec803761,0x188fc0000e9d5215000,0x18143a0a5a56c000000],#[0x180222888000000,0x80e1080000608128c800,0xac62016b1a000148b282,0x818377c050409802a4c1,0x120f0000111be0000c3,0x3e03b60001424e000000,0x8c000000016562000040,0xeb8a7d88bc00008125e4,0x1e10d88,0xe1b4c1abb43a000000,0x180c000008a77896800,0xf800002954c2a8000000,0x3b6096c42a62ca000040,0xc9776196096bd0,0xb42aaa93c0000000000,0x7b11a761116100e805a0,0x3ea95e9298156d39b40,0x191a981a44047e8,0xb0c249a27d132d413600,0xcc6013c03cc031cab300,0x14234618e8592c1,0xd0416c455deab5812600,0xcd02798020c04960c9a1,0xfa0000aa74086c40cb40,0x161c1a26d80,0x1e0fc000000,0xe1460000ab1600,0x3ba885c220406c805600,0xb80001001f026f202a00,0x120,0x88af00c5086e000000,0x0],#[0x7548b40000c0874c1fca,0xa640d6c02d93280001e9,0x81bbe204c0ea01c820,0x14ab800000000000000,0x805480b60001e03200,0xe2000000000000000000,0x17408dd4340000000148,0x1a80ae8be0001649300,0x69e99e0000e08be94800,0x9c681e039a81554106c8,0x340001c94ccaf30953e0,0x71f035c05b013c41b020,0x1c0001701d811c087c28,0x20280ce1c60000000154,0x2762872000069a861,0x12874688000]]
def g219D8 := limbs80 #[#[0xd48510fe54110b7d8d51,0xd8910bf58910fd54510f,0x9510bf59510bf19510bf,0x120fe50120bfd9510bf9,0x20bf59120bfd8520fe54,0xbf59520bf19520bfd91,0xfed4150bfd9520bf9952,0xfd4950df54950bfd8550,0xd4b50bf58750bfd8950d,0x4551bfd8151bf58b50df,0x910bf58351f7d8d51fdd,0x20ff54520ff54910ff50,0xff55120ff58520ffd45,0xff99520ff59520ffd512,0xf58550ffd4550ff54550,0xd4950ff54950ffd8550f,0x8b50ffd8950ff58950ff,0x2060037000ff58351ff5,0x18615d1340fd0d40ab08,0xb327524521c2011d11af,0x73b038e36533c31a2f12,0x4eb4bb4994694474173e,0x496195e25a456d54451b,0x87a17637337036d368e6,0x90d8e48ad8688388017d,0x145202900e33262c1047,0x500290151400a4040193,0x228a245088a045202e4c,0x405c808262802228e432,0x917262802228b931408a,0x890c1016524264c51480,0xca4854a4090600890cb0],#[0x91020386ca9050c20386,0x2140ca40708080800640,0x10242804480a10386159,0x80b93100224050e1b292,0x5007c995140132628094,0xd911658030ac8472904,0x14020264078834028307,0x480a09908c0219510c45,0x626364c5804050c364c,0x48511931208a283c98b0,0x825222811480e884908a,0x251c5444818a42809488,0xb129490d1120a110a0,0x48848706010468491242,0x24311090e0c046848122,0x121031e12430885031e1,0xa0084a423890a0102831,0x27262809480e91109890,0x1208a00f931404a40528,0x8981905114440623931e,0x8a00e9089015931e1808,0xb911118040522431e1c8,0x3262402228]]
set_option maxRecDepth 16000 in
def g219H8 := limbs80 #[#[0x40119c2a01040682c02,0xc09030184e050511800,0x2000002313c202103818,0x8000063b2100c101d008,0x7002d42c102213818001,0x4001482c0e0f0f81c087,0xc6a054d84cd20e048000,0xa5a800251268404001b,0x2cb940a0547034020572,0x1b3100044720e028029b,0x1c03080097052061a400,0xc2250207927561441494,0x81a3c194416b505801c7,0x8567c089c6e489d1d103,0x42ccc45002a0046bd45d,0xd24840ea0484c27e8a4a,0x402e802ac688515e4026,0xd0af4222e03981d8856b,0x9550c642e680784a3c,0x809f82c18ac285590455,0xbea915407186814281,0xc1bc6130cabd41e340b4,0x81e9406cc918a1240002,0xd48884590a3849914667,0x8954c0fb443802af49b8,0x801242328483a92e418f,0x81f6c1e400e4927a94a6,0x481b411601de8081c657,0x81a94075d0db4132451b,0xd0e4c171213901234106,0x8246107441b9683e4252,0x1601400bc26989bd41ff],#[0x8134a0f640f6464c826f,0x856d423d017c9161603f,0x59a9a59816680d150d3,0x3c640000344d40003,0x80c5c18581f8000285a8,0x4968000055e801248016,0x495ac68d8a4d0035065e,0x61c9a34050182ac288,0xd5dc0001d17c00000002,0x8a53c09115f255940000,0xc284c67bc07fc47c0001,0x82e301456945846f86dd,0x406a828e6121819ca932,0x14a06702284000002b7,0x46a3420bd245146a,0xec0a8c91c00034a40,0x185240a0a462e01d5,0x5c105f41780000e290,0x34249c42a803b822b,0xc96410e99458d48fc174,0x2d1ddd06c4a28c2a8,0xc960023780a780fc04ec,0x4310109c2124118c50b,0x29710b6424d408ca927,0x25a15e25a4ad1a84240,0x1f3415000030a62c16e,0xd5880001d07342d402d8,0x42c8956f0198d2078291,0x6e9903180e3115a895c,0x89b38676c42c81d046e0,0x4a1c14dc5c1c652863a,0x28085057382b120da],#[0x848a81c8000005e84510,0xc67f047810ee41c00000,0x92688663815c0002c0d8,0x1a7c21c00b942780003,0x80b200dcd58002574101,0x49f840c8863c0001c215,0x3c2d000ee213c9498,0x42b80000000182bc,0x24a1a422c429c,0xc1295170098fc57495ec,0x9154854044e00001025d,0x49ac509b412dc4d08155,0x468055c63185fdd03a,0x810f499f147ec45ea114,0x9e360714042411f8277,0x2244804c0a1700c0c644,0x2c1ee42e9c51cc143,0x95f8844dca37d06bc020,0x8437023982194403902b,0x81b4401a419242df41ac,0xc0afc163d27dc0a10951,0x41cfc13c82010263855c,0xc5780000612e9224c82b,0xd5f68648c9980003c29b,0xca5915b4c2a781385150,0x4098000151f480ce4503,0x465b55e782c6ca5d4182,0x80f005ba80d781b2c059,0x80324158401e110e4065,0x3f4636426641880001,0x4581293809cf610e293f,0x516e4271820e004ad081],#[0x458a925a8113c005c4f3,0x30002]]
def g219D9 := limbs80 #[#[0xd51ffa87f543fa41fd10,0x51b0259b138a803fea3f,0x410202548526489000,0x101464648a50101a48a5,0x248a02051549228]]
def g219H9 := limbs80 #[#[0x6d6851460800a30c0003,0x20d57803430060c20041,0xd4030001c0a000200000,0x87000140007186413640,0xf154000c23000068b4,0xb253c040000c2300b00,0xc0b79296026c51903000,0x102bb142e1fc597830,0xa5c200000d1e00004810,0x90a10000017406000090,0x5283481c0e0002d0ba0b,0x909746c0001607ba82,0xc8c7c0dc0a8000b1100,0x8006457a07880640a000,0xb8a4000d86c059,0x38a900000000000d640,0x8000a80c000e42a04200,0x22d879a2842aa5a0a45,0x12402c0000000000ea7f,0x20001819d09a81fc18ac,0x4180c14b2af161412c56,0x1580000000ca30000000,0x41d0000c8770840a87,0x141100be41084b400000,0x4a214c605a785bc84000,0x270090415846de20b01c,0xe6023d07000104580c64,0x406a00fd05a9088222c6,0x1bd46d0000c02b070000,0x341be263e089]]
def g219D10 (j : Nat) := if j=0 then 0x2080513f else 0
def g219H10 := limbs80 #[#[0x30,0x2d1fb0a060,0x30500000040000320000,0x501d480000000000,0x8000000000000000,0x2110000,0x794b8600000000000,0x15410278900000,0x1e10008400000,0x32a002408]]
def g219L : Nat → Packing
  | 4 => (2,6,5,0,0,3,0,g219D4)
  | 5 => (57,5,5,0,0,10,0,g219D5)
  | 6 => (237,4,5,0,0,12,0,g219D6)
  | 7 => (187,3,5,0,0,13,0,g219D7)
  | 8 => (50,2,5,0,0,12,0,g219D8)
  | 9 => (6,1,5,0,0,8,0,g219D9)
  | 10 => (1,0,5,0,0,0,0,g219D10)
  | _ => emptyPacking
def g219I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 5 0 8 1 3 g219H5
  | 6 => lookupWord 25 379 3 14 6 4 g219H6
  | 7 => lookupWord 111 673 7 16 8 4 g219H7
  | 8 => lookupWord 98 431 9 16 8 4 g219H8
  | 9 => lookupWord 28 157 6 14 6 4 g219H9
  | 10 => lookupWord 4 71 2 11 3 4 g219H10
  | _ => fun _ => none
def g219 : Forest := ⟨219,10,fun i => g219Y[i]?.getD (0,0),g219C,g219A,g219L,g219I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P4_0 : block g219 4 0 2=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g219B4 : block g219 4 0 2=true := g219P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P5_0 : block g219 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P5_1 : block g219 5 1 56=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g219B5 : block g219 5 0 57=true := (@block_merge g219 5 0 1 56 g219P5_0 g219P5_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P6_0 : block g219 6 0 13=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P6_13 : block g219 6 13 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P6_109 : block g219 6 109 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P6_205 : block g219 6 205 32=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g219B6 : block g219 6 0 237=true := (@block_merge g219 6 0 109 128 (@block_merge g219 6 0 13 96 g219P6_0 g219P6_13) (@block_merge g219 6 109 96 32 g219P6_109 g219P6_205))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P7_0 : block g219 7 0 10=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P7_10 : block g219 7 10 59=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P7_69 : block g219 7 69 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P7_165 : block g219 7 165 22=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g219B7 : block g219 7 0 187=true := (@block_merge g219 7 0 69 118 (@block_merge g219 7 0 10 59 g219P7_0 g219P7_10) (@block_merge g219 7 69 96 22 g219P7_69 g219P7_165))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P8_0 : block g219 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P8_1 : block g219 8 1 30=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P8_31 : block g219 8 31 19=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g219B8 : block g219 8 0 50=true := (@block_merge g219 8 0 1 49 g219P8_0 (@block_merge g219 8 1 30 19 g219P8_1 g219P8_31))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P9_0 : block g219 9 0 6=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g219B9 : block g219 9 0 6=true := g219P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P10_0 : block g219 10 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g219B10 : block g219 10 0 1=true := g219P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219T : checkedTables g219 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g219 0 0 0 = true)
  · exact (rfl : block g219 1 0 0 = true)
  · exact (rfl : block g219 2 0 0 = true)
  · exact (rfl : block g219 3 0 0 = true)
  · exact g219B4
  · exact g219B5
  · exact g219B6
  · exact g219B7
  · exact g219B8
  · exact g219B9
  · exact g219B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219G : graphValid g219 (boundsBefore K207) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low219 : Lower true (varsX 219) (graphGoal 219) 11 := lower_forest (g:=g219) (i:=0) (hints:=65603) (before_sound K207 V207) g219G g219T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K219 := extendKnown K207 11 [(219,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V219 : Known true K219 := extend_ok (m:=219) V207 low219 (by decide +kernel)
def g231Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffffffc007ff01ffc0,0x7f164bde40000f00f00f])),(BitVec.ofNat 152 (word80 [0x29280a83504a34148b,0x14124bde011111111111]))),((BitVec.ofNat 152 (word80 [0xff81fffff80001ffff,0x80ab6aa96000f00000f0])),(BitVec.ofNat 152 (word80 [0x324c9312626c589912,0x26ab6aa9655555555555]))),((BitVec.ofNat 152 (word80 [0x1fffffffffe0000,0x731dc1300f000f0f00])),(BitVec.ofNat 152 (word80 [0x3c701c038070601e1c,0x38321dc1311111111111]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1ffffffffffffff,0xff080b2390f000f00fff])),(BitVec.ofNat 152 (word80 [0x400020040080002000,0x22222222222]))),((BitVec.ofNat 152 (word80 [0xfffe00000000000000,0xd7d024ef0000fff000])),(BitVec.ofNat 152 (word80 [0x8000c018030080c020,0x40c58020c44444444444]))),(0xa0a4d80fffff000000,(BitVec.ofNat 152 (word80 [0x100200400010000,0x88888888888]))),(0x0,0x0)]
def g231C : List ColumnInfo := [(1,0,230,0,8)]
def g231A : List (List Nat) := [[],[117],[32],[32,117]]
def g231D8 (j : Nat) := if j=0 then 0x7f else 0
def g231L : Nat → Packing
  | 8 => (1,0,1,0,0,0,0,g231D8)
  | _ => emptyPacking
def g231I (_ _ : Nat) : Option (Nat × Nat) := none
def g231 : Forest := ⟨231,8,fun i => g231Y[i]?.getD (0,0),g231C,g231A,g231L,g231I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231P8_0 : block g231 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g231B8 : block g231 8 0 1=true := g231P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231T : checkedTables g231 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g231 0 0 0 = true)
  · exact (rfl : block g231 1 0 0 = true)
  · exact (rfl : block g231 2 0 0 = true)
  · exact (rfl : block g231 3 0 0 = true)
  · exact (rfl : block g231 4 0 0 = true)
  · exact (rfl : block g231 5 0 0 = true)
  · exact (rfl : block g231 6 0 0 = true)
  · exact (rfl : block g231 7 0 0 = true)
  · exact g231B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231G : graphValid g231 (boundsBefore K219) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low231 : Lower true (varsX 231) (graphGoal 231) 9 := lower_forest (g:=g231) (i:=0) (hints:=1365) (before_sound K219 V219) g231G g231T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K231 := extendKnown K219 9 [(231,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V231 : Known true K231 := extend_ok (m:=231) V219 low231 (by decide +kernel)
def g237Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xf87ffe01ffff8fffe6,0x33c2300000f8000f83ff])),(BitVec.ofNat 152 (word80 [0x110014140a01200422,0x11c03084210842108421]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xff87fffe00fff1fe0b,0xbad50001f0001f07c00])),(BitVec.ofNat 152 (word80 [0xa01058182c0a04088b,0x3a9518c6318c6318c63]))),((BitVec.ofNat 152 (word80 [0x7ffffff0001ffc5,0xea98e003e0003e00001f])),(BitVec.ofNat 152 (word80 [0xc2216020302c485005,0xea18c318c6318c6318c6]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x7fffffffffe0012,0x6c4f807c0007c0007fe0])),(BitVec.ofNat 152 (word80 [0x44180404030006110,0x6c068210842108421084]))),((BitVec.ofNat 152 (word80 [0xfff800000000000029,0x84009f800007ffff8000])),(BitVec.ofNat 152 (word80 [0x200808040008000,0x421084210842108]))),((BitVec.ofNat 152 (word80 [0x10,0x51304ffffff800000000])),(BitVec.ofNat 152 (word80 [0x401010080010000,0x842108421084210]))),(0x0,0x0)]
def g237C : List ColumnInfo := [(1,0,236,0,8),(4,0,233,0,8),(8,0,229,0,8),(32,0,205,0,8),(64,0,173,0,7),(128,0,109,0,7)]
def g237A : List (List Nat) := [[],[118],[80,50],[80,50,118]]
def g237D8 (j : Nat) := if j=0 then 0x2a54dc0dfd54 else 0
def g237D9 (j : Nat) := if j=0 then 0x2c4581bf else 0
def g237H9 (j : Nat) := if j=0 then 0x8 else 0
def g237L : Nat → Packing
  | 8 => (1,1,3,0,0,0,0,g237D8)
  | 9 => (1,0,3,0,0,0,0,g237D9)
  | _ => emptyPacking
def g237I : Nat → Nat → Option (Nat × Nat)
  | 9 => lookupWord 1 2 0 4 0 0 g237H9
  | _ => fun _ => none
def g237 : Forest := ⟨237,9,fun i => g237Y[i]?.getD (0,0),g237C,g237A,g237L,g237I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P8_0 : block g237 8 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g237B8 : block g237 8 0 1=true := g237P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P9_0 : block g237 9 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g237B9 : block g237 9 0 1=true := g237P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237T : checkedTables g237 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g237 0 0 0 = true)
  · exact (rfl : block g237 1 0 0 = true)
  · exact (rfl : block g237 2 0 0 = true)
  · exact (rfl : block g237 3 0 0 = true)
  · exact (rfl : block g237 4 0 0 = true)
  · exact (rfl : block g237 5 0 0 = true)
  · exact (rfl : block g237 6 0 0 = true)
  · exact (rfl : block g237 7 0 0 = true)
  · exact g237B8
  · exact g237B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237G : graphValid g237 (boundsBefore K231) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low237 : Lower true (varsX 237) (graphGoal 237) 10 := lower_forest (g:=g237) (i:=0) (hints:=1283) (before_sound K231 V231) g237G g237T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K237 := extendKnown K231 10 [(237,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V237 : Known true K237 := extend_ok (m:=237) V231 low237 (by decide +kernel)
def g238Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffc07ff800fffffe03,0xfecb2a2ba20000f0000f])),(BitVec.ofNat 152 (word80 [0x148b21526a4948a458,0xa6cb0a2aa25555555555]))),((BitVec.ofNat 152 (word80 [0xffffffffff001ffffc,0x34edb8091000f000ff0])),(BitVec.ofNat 152 (word80 [0x191202604c0d80c891,0x334e5a00111111111111]))),((BitVec.ofNat 152 (word80 [0x7fffffffe00000,0xd372d62500f000f000])),(BitVec.ofNat 152 (word80 [0x5e1c0b80700e02f0e1,0xc0c372d4253333333333]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x7fffffffffffff,0xf922299d6b0f000f00ff])),(BitVec.ofNat 152 (word80 [0x60200c008010030000,0x202195082222222222]))),((BitVec.ofNat 152 (word80 [0xffff80000000000000,0x98c67ad8f0000fff00])),(BitVec.ofNat 152 (word80 [0x8000300300600c0102,0x10842ac04444444444]))),(0x665142404fffff00000,(BitVec.ofNat 152 (word80 [0x40040080100000,0x8888888888]))),(0x0,0x0)]
def g238C : List ColumnInfo := [(2,0,236,0,8)]
def g238A : List (List Nat) := [[],[49,101]]
def g238D8 (j : Nat) := if j=0 then 0x7f else 0
def g238L : Nat → Packing
  | 8 => (1,0,1,0,0,0,0,g238D8)
  | _ => emptyPacking
def g238I (_ _ : Nat) : Option (Nat × Nat) := none
def g238 : Forest := ⟨238,8,fun i => g238Y[i]?.getD (0,0),g238C,g238A,g238L,g238I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g238P8_0 : block g238 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g238B8 : block g238 8 0 1=true := g238P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g238T : checkedTables g238 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g238 0 0 0 = true)
  · exact (rfl : block g238 1 0 0 = true)
  · exact (rfl : block g238 2 0 0 = true)
  · exact (rfl : block g238 3 0 0 = true)
  · exact (rfl : block g238 4 0 0 = true)
  · exact (rfl : block g238 5 0 0 = true)
  · exact (rfl : block g238 6 0 0 = true)
  · exact (rfl : block g238 7 0 0 = true)
  · exact g238B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g238G : graphValid g238 (boundsBefore K237) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low238 : Lower true (varsX 238) (graphGoal 238) 9 := lower_forest (g:=g238) (i:=0) (hints:=303064400) (before_sound K237 V237) g238G g238T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K238 := extendKnown K237 9 [(238,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V238 : Known true K238 := extend_ok (m:=238) V237 low238 (by decide +kernel)
def g243Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xe003ffffe1fff819e1,0x9c2b4000000fc0fc0fc0])),(BitVec.ofNat 152 (word80 [0x40a80a0244001118e1,0x9c0040c30c30c30c30c3]))),((BitVec.ofNat 152 (word80 [0xfffc00fffe1fffb10e,0x7c90700003f00003f03f])),(BitVec.ofNat 152 (word80 [0x84308c208044203106,0x4c806249249249249249]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffff00001fffda3d,0x33312000fc000000003f])),(BitVec.ofNat 152 (word80 [0x8c1104b0889404a39,0x33310596596596596596]))),((BitVec.ofNat 152 (word80 [0xffffffffffe000462a,0x8987903f00003f03ffc0])),(BitVec.ofNat 152 (word80 [0x100200c0001820608,0x1039104104104104104]))),((BitVec.ofNat 152 (word80 [0x4984,0x67ec8fc000003ffc0000])),(BitVec.ofNat 152 (word80 [0xe01c070110e044104,0x62ec0618618618618618]))),((BitVec.ofNat 152 (word80 [0x2651,0x42404fffffffc0000000])),(BitVec.ofNat 152 (word80 [0x100200800010000000,0x820820820820820]))),(0x0,0x0)]
def g243C : List ColumnInfo := [(2,0,241,0,8),(16,0,227,0,8),(32,0,211,0,8),(1,0,242,0,7),(64,0,179,0,7),(128,0,115,0,7),(65,0,178,0,5),(129,0,114,0,4),(192,0,51,0,4)]
def g243A : List (List Nat) := [[],[96]]
def g243D6 := limbs80 #[#[0xe3c1243e437395454140,0x5]]
def g243D7 := limbs80 #[#[0xf55150bf59540fe54140,0x42a00ff59150bfd9150d,0xc32187c70572186ae8a5,0x481c5c705328c82071b1,0x81c60d4c70c871]]
def g243H7 (j : Nat) := if j=0 then 0x20 else 0
def g243D8 := limbs80 #[#[0xa38c2461a403faa1fd40,0x1e851c6121c]]
def g243H8 (j : Nat) := if j=0 then 0x8852030000b041a40000 else 0
def g243D9 (j : Nat) := if j=0 then 0x5431021bf else 0
def g243H9 (j : Nat) := if j=0 then 0xe7800f else 0
def g243L : Nat → Packing
  | 6 => (1,3,4,0,0,0,0,g243D6)
  | 7 => (5,2,4,0,0,8,0,g243D7)
  | 8 => (2,1,4,0,0,6,0,g243D8)
  | 9 => (1,0,4,0,0,0,0,g243D9)
  | _ => emptyPacking
def g243I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 1 2 0 4 0 0 g243H7
  | 8 => lookupWord 1 11 0 8 3 1 g243H8
  | 9 => lookupWord 1 5 0 6 1 1 g243H9
  | _ => fun _ => none
def g243 : Forest := ⟨243,9,fun i => g243Y[i]?.getD (0,0),g243C,g243A,g243L,g243I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P6_0 : block g243 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g243B6 : block g243 6 0 1=true := g243P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P7_0 : block g243 7 0 4=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P7_4 : block g243 7 4 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g243B7 : block g243 7 0 5=true := (@block_merge g243 7 0 4 1 g243P7_0 g243P7_4)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P8_0 : block g243 8 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g243B8 : block g243 8 0 2=true := g243P8_0
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
  · exact (rfl : block g243 5 0 0 = true)
  · exact g243B6
  · exact g243B7
  · exact g243B8
  · exact g243B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243G : graphValid g243 (boundsBefore K238) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low243 : Lower true (varsX 243) (graphGoal 243) 10 := lower_forest (g:=g243) (i:=0) (hints:=65605) (before_sound K238 V238) g243G g243T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K243 := extendKnown K238 10 [(246,[32])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V243 : Known true K243 := extend_ok (m:=243) V238 low243 (by decide +kernel)
def g245Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xe03ffff800fffffe03,0xfed3aa41320000f00f0f])),(BitVec.ofNat 152 (word80 [0x458a01506a0940a458,0xa6530a40321111111111]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffc07fffff001ffffc,0x34e5bc281000f00f0f0])),(BitVec.ofNat 152 (word80 [0x891302604c0d80c891,0x334e1a42011111111111]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x7fffffffe00000,0xd372be2500f0000000])),(BitVec.ofNat 152 (word80 [0xe1c2b82704e0af0e1,0xc0d372be257777777777]))),((BitVec.ofNat 152 (word80 [0x7fffffffffffff,0xf922299d6b0f000f00ff])),(BitVec.ofNat 152 (word80 [0x10200c008010030000,0x20218d082222222222]))),((BitVec.ofNat 152 (word80 [0xffff80000000000000,0x98c67ad8f0000fff00])),(BitVec.ofNat 152 (word80 [0x300300600c0102,0x80c430c04444444444]))),(0x665142404fffff00000,(BitVec.ofNat 152 (word80 [0x40040080100000,0x8888888888]))),(0x0,0x0)]
def g245C : List ColumnInfo := [(1,0,244,0,8)]
def g245A : List (List Nat) := [[],[101],[32],[32,101]]
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
theorem low245 : Lower true (varsX 245) (graphGoal 245) 9 := lower_forest (g:=g245) (i:=0) (hints:=460037) (before_sound K243 V243) g245G g245T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K245 := extendKnown K243 9 [(245,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V245 : Known true K245 := extend_ok (m:=245) V243 low245 (by decide +kernel)
def g127Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfdc920712d36aa096a,0x350c800003f8001fc07f])),(BitVec.ofNat 152 (word80 [0x504100102d348a0168,0x250c050a142850a14285]))),((BitVec.ofNat 152 (word80 [0x170978870930258ed,0xea4d000000000fe03f80])),(BitVec.ofNat 152 (word80 [0x9970078870120058ec,0x84c23468d1a3468d1a3]))),((BitVec.ofNat 152 (word80 [0x2e54e9fbee00a2a44,0x970001fc07f0000000])),(BitVec.ofNat 152 (word80 [0xe0e14e9f3ca00a2a40,0x170f1e3c78f1e3c78f]))),((BitVec.ofNat 152 (word80 [0xfeb671b1740f94ce22,0x501300fe00000000007f])),(BitVec.ofNat 152 (word80 [0x2b471a1500b140e02,0x50131a3468d1a3468d1a]))),((BitVec.ofNat 152 (word80 [0x2012d631f855287d9,0xea838000000000003f80])),(BitVec.ofNat 152 (word80 [0x20128630f85528711,0xe283dcb972e5cb972e5c]))),((BitVec.ofNat 152 (word80 [0x24592a2c119793013,0x1f2ff000007ffffc000])),(BitVec.ofNat 152 (word80 [0x20490208009710003,0x809020408102040810]))),((BitVec.ofNat 152 (word80 [0x13a484c0a6855d794,0x62c7ffffff800000000])),(BitVec.ofNat 152 (word80 [0x10a0040024000d094,0x22060c183060c183060]))),(0x0,0x0),(0x0,0x0)]
def g127C : List ColumnInfo := [(16,0,111,0,9)]
def g127A : List (List Nat) := [[]]
def g127D9 (j : Nat) := if j=0 then 0xff else 0
def g127L : Nat → Packing
  | 9 => (1,0,1,0,0,0,0,g127D9)
  | _ => emptyPacking
def g127I (_ _ : Nat) : Option (Nat × Nat) := none
def g127 : Forest := ⟨127,9,fun i => g127Y[i]?.getD (0,0),g127C,g127A,g127L,g127I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P9_0 : block g127 9 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B9 : block g127 9 0 1=true := g127P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127T : checkedTables g127 9 := by
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
  · exact g127B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127G : graphValid g127 (boundsBefore K245) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low127 : Lower true (varsX 127) (graphGoal 127) 10 := lower_forest (g:=g127) (i:=0) (hints:=66883) (before_sound K245 V245) g127G g127T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K127 := extendKnown K245 10 [(127,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V127 : Known true K127 := extend_ok (m:=127) V245 low127 (by decide +kernel)
def g191Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfffe68002e382df19f,0xad0c0000000fc003f03f])),(BitVec.ofNat 152 (word80 [0x42828002a302c309b,0x8c0c5145145145145145]))),((BitVec.ofNat 152 (word80 [0x244fb0c2d41c5f,0xba80000003f000fc0fc0])),(BitVec.ofNat 152 (word80 [0xcc2447b00294140e,0xaa0030c30c30c30c30c3]))),((BitVec.ofNat 152 (word80 [0x1e2ecf33da00e36,0xc240000fc003f000000])),(BitVec.ofNat 152 (word80 [0x970e06cf33da00e16,0xc24f3cf3cf3cf3cf3cf]))),((BitVec.ofNat 152 (word80 [0xffff52717c5eb37a44,0x3110003f00000000003f])),(BitVec.ofNat 152 (word80 [0x51815271544e934a44,0x3111a69a69a69a69a69a]))),((BitVec.ofNat 152 (word80 [0x1194b4bed2a4d39,0x19c00fc0000000000fc0])),(BitVec.ofNat 152 (word80 [0x9e0119084bed2a4931,0x11c1c71c71c71c71c71c]))),((BitVec.ofNat 152 (word80 [0x122a456034e8160,0x53fff00000003ffff000])),(BitVec.ofNat 152 (word80 [0xe00102800400428160,0x51d10410410410410410]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x9d108124920282,0xc453ffffffffc0000000])),0x20820820820820820),(0x0,0x0)]
def g191C : List ColumnInfo := [(4,0,187,0,10)]
def g191A : List (List Nat) := [[],[16,67]]
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
theorem low191 : Lower true (varsX 191) (graphGoal 191) 11 := lower_forest (g:=g191) (i:=0) (hints:=66883) (before_sound K127 V127) g191G g191T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K191 := extendKnown K127 11 [(191,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V191 : Known true K191 := extend_ok (m:=191) V127 low191 (by decide +kernel)
def g223Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xf9a480503accf8ff34,0x3f8001fc07f])),(BitVec.ofNat 152 (word80 [0xa0a48050284c18de34,0x142850a142850a14285]))),((BitVec.ofNat 152 (word80 [0x9b7f6100a80debf9,0x1fc0000003f80])),(BitVec.ofNat 152 (word80 [0x309a6f6000a80c6379,0x4c993264c993264c993]))),((BitVec.ofNat 152 (word80 [0x780d966b87d07a452,0x200000fe00000fe00000])),(BitVec.ofNat 152 (word80 [0xc780d162b87d07a450,0x23c78f1e3c78f1e3c78f]))),((BitVec.ofNat 152 (word80 [0xfd4963fab542bb2108,0x7f000007f000007f])),(BitVec.ofNat 152 (word80 [0x549432a9102a32108,0x2850a142850a142850a]))),((BitVec.ofNat 152 (word80 [0x46156955a5f27c885,0x403f8000000000003f80])),(BitVec.ofNat 152 (word80 [0x46110955a57238884,0x4b162c58b162c58b162c]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x482a8ae46964012cf,0xbfc000000007ffffc000])),(BitVec.ofNat 152 (word80 [0x228844680400083,0x8c183060c183060c1830]))),((BitVec.ofNat 152 (word80 [0x27e0100c921020430,0xdffffffffff800000000])),0x10204081020408102040),(0x0,0x0)]
def g223C : List ColumnInfo := [(4,0,219,0,11)]
def g223A : List (List Nat) := [[],[65],[48],[48,65]]
def g223D11 (j : Nat) := if j=0 then 0xff else 0
def g223L : Nat → Packing
  | 11 => (1,0,1,0,0,0,0,g223D11)
  | _ => emptyPacking
def g223I (_ _ : Nat) : Option (Nat × Nat) := none
def g223 : Forest := ⟨223,11,fun i => g223Y[i]?.getD (0,0),g223C,g223A,g223L,g223I⟩
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
  · exact (rfl : block g223 5 0 0 = true)
  · exact (rfl : block g223 6 0 0 = true)
  · exact (rfl : block g223 7 0 0 = true)
  · exact (rfl : block g223 8 0 0 = true)
  · exact (rfl : block g223 9 0 0 = true)
  · exact (rfl : block g223 10 0 0 = true)
  · exact g223B11
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223G : graphValid g223 (boundsBefore K191) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low223 : Lower true (varsX 223) (graphGoal 223) 12 := lower_forest (g:=g223) (i:=0) (hints:=67139) (before_sound K191 V191) g223G g223T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K223 := extendKnown K191 12 [(223,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V223 : Known true K223 := extend_ok (m:=223) V191 low223 (by decide +kernel)
def g239Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfffffef143449828c8,0xe4c000001f0001f003ff])),(BitVec.ofNat 152 (word80 [0x29028f04240902840,0x84c21084210842108421]))),((BitVec.ofNat 152 (word80 [0xfff8013e94621f602c,0xcac00003e00000007c00])),(BitVec.ofNat 152 (word80 [0x1320cd3e94621b202c,0xcad6b5ad6b5ad6b5ad6b]))),((BitVec.ofNat 152 (word80 [0x14e6872d00e14,0xf180007c00003e0f8000])),(BitVec.ofNat 152 (word80 [0x1bc1714a4872d00a14,0xf086318c6318c6318c63]))),((BitVec.ofNat 152 (word80 [0xffffff10b5f8e8d2c4,0x62000f800007c000001f])),(BitVec.ofNat 152 (word80 [0x5c018100a5b8685284,0x620c6318c6318c6318c6]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x8ab85754d05,0x841f00000f8000fffe0])),(BitVec.ofNat 152 (word80 [0x600200002185244401,0x84210842108421084]))),((BitVec.ofNat 152 (word80 [0xa750a900833a,0xbbe000000fffff00000])),(BitVec.ofNat 152 (word80 [0x80040005100000812a,0x9108421084210842108]))),((BitVec.ofNat 152 (word80 [0x1400412223023,0x943fffffff0000000000])),0x210842108421084210),(0x0,0x0)]
def g239C : List ColumnInfo := [(2,0,237,0,10)]
def g239A : List (List Nat) := [[]]
def g239D10 (j : Nat) := if j=0 then 0xff else 0
def g239L : Nat → Packing
  | 10 => (1,0,1,0,0,0,0,g239D10)
  | _ => emptyPacking
def g239I (_ _ : Nat) : Option (Nat × Nat) := none
def g239 : Forest := ⟨239,10,fun i => g239Y[i]?.getD (0,0),g239C,g239A,g239L,g239I⟩
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
  · exact (rfl : block g239 5 0 0 = true)
  · exact (rfl : block g239 6 0 0 = true)
  · exact (rfl : block g239 7 0 0 = true)
  · exact (rfl : block g239 8 0 0 = true)
  · exact (rfl : block g239 9 0 0 = true)
  · exact g239B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239G : graphValid g239 (boundsBefore K223) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low239 : Lower true (varsX 239) (graphGoal 239) 11 := lower_forest (g:=g239) (i:=0) (hints:=1363) (before_sound K223 V223) g239G g239T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K239 := extendKnown K223 11 [(239,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V239 : Known true K239 := extend_ok (m:=239) V223 low239 (by decide +kernel)
def g247Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xc00fc7869828682455,0x40000000fc003f000fc0])),(BitVec.ofNat 152 (word80 [0x856fc2869008682445,0x430c30c30c30c30c30c3]))),((BitVec.ofNat 152 (word80 [0xfff2f820851743a0f7,0x4000003f00000003f03f])),(BitVec.ofNat 152 (word80 [0x242f800850641a096,0x49249249249249249249]))),((BitVec.ofNat 152 (word80 [0x13ad0e5c0780e64,0xc0000fc0000fc0fc0000])),(BitVec.ofNat 152 (word80 [0xb812a90a5c0680664,0xc30c30c30c30c30c30c3]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfff9416bf1a38ad461,0x8003f00000000000003f])),(BitVec.ofNat 152 (word80 [0xc09016b70a18a5461,0x96596596596596596596]))),((BitVec.ofNat 152 (word80 [0x21570a95747488,0xfc000003f000ffffc0])),(BitVec.ofNat 152 (word80 [0x100001410a11104008,0x4104104104104104104]))),((BitVec.ofNat 152 (word80 [0x49ca952220d1b94,0xbf00000003ffff000000])),(BitVec.ofNat 152 (word80 [0x200014284022051990,0x18618618618618618618]))),((BitVec.ofNat 152 (word80 [0xb0208244881410a,0x7ffffffffc0000000000])),0x20820820820820820820),(0x0,0x0)]
def g247C : List ColumnInfo := [(1,0,246,0,10)]
def g247A : List (List Nat) := [[],[32]]
def g247D10 (j : Nat) := if j=0 then 0xff else 0
def g247L : Nat → Packing
  | 10 => (1,0,1,0,0,0,0,g247D10)
  | _ => emptyPacking
def g247I (_ _ : Nat) : Option (Nat × Nat) := none
def g247 : Forest := ⟨247,10,fun i => g247Y[i]?.getD (0,0),g247C,g247A,g247L,g247I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P10_0 : block g247 10 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g247B10 : block g247 10 0 1=true := g247P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247T : checkedTables g247 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g247 0 0 0 = true)
  · exact (rfl : block g247 1 0 0 = true)
  · exact (rfl : block g247 2 0 0 = true)
  · exact (rfl : block g247 3 0 0 = true)
  · exact (rfl : block g247 4 0 0 = true)
  · exact (rfl : block g247 5 0 0 = true)
  · exact (rfl : block g247 6 0 0 = true)
  · exact (rfl : block g247 7 0 0 = true)
  · exact (rfl : block g247 8 0 0 = true)
  · exact (rfl : block g247 9 0 0 = true)
  · exact g247B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247G : graphValid g247 (boundsBefore K239) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low247 : Lower true (varsX 247) (graphGoal 247) 11 := lower_forest (g:=g247) (i:=0) (hints:=66885) (before_sound K239 V239) g247G g247T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K247 := extendKnown K239 11 [(247,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V247 : Known true K247 := extend_ok (m:=247) V239 low247 (by decide +kernel)
def g251Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x2e41498b0e1b881800,0xfe0007f01fc07f])),(BitVec.ofNat 152 (word80 [0x264048000e09081850,0xa142850a142850a14285]))),((BitVec.ofNat 152 (word80 [0x67b42811b1a34e4000,0x7f0000000fe03f80])),(BitVec.ofNat 152 (word80 [0x27a0281130a3420132,0x64c993264c993264c993]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x45bae0c3e05ca12000,0x3f800003f80000007f])),(BitVec.ofNat 152 (word80 [0x40b2a0c3e014a120a1,0x42850a142850a142850a]))),((BitVec.ofNat 152 (word80 [0x5006db98fa40bcd000,0x1fc00000000000003f80])),(BitVec.ofNat 152 (word80 [0x5006d388ca40bcd2c5,0x8b162c58b162c58b162c]))),((BitVec.ofNat 152 (word80 [0xd215342a49a4a1880f,0xe0000001fc000fffc000])),(BitVec.ofNat 152 (word80 [0xd015140a4104a10081,0x2040810204081020408]))),((BitVec.ofNat 152 (word80 [0x9ca1724506341f7f0,0x1fffff0000000])),(BitVec.ofNat 152 (word80 [0x9080324106240c306,0xc183060c183060c1830]))),((BitVec.ofNat 152 (word80 [0xb020824406047207ff,0xfffffffe000000000000])),(BitVec.ofNat 152 (word80 [0x408,0x10204081020408102040]))),(0x0,0x0)]
def g251C : List ColumnInfo := [(32,0,219,0,11)]
def g251A : List (List Nat) := [[],[96]]
def g251D11 (j : Nat) := if j=0 then 0xff else 0
def g251L : Nat → Packing
  | 11 => (1,0,1,0,0,0,0,g251D11)
  | _ => emptyPacking
def g251I (_ _ : Nat) : Option (Nat × Nat) := none
def g251 : Forest := ⟨251,11,fun i => g251Y[i]?.getD (0,0),g251C,g251A,g251L,g251I⟩
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
  · exact (rfl : block g251 10 0 0 = true)
  · exact g251B11
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251G : graphValid g251 (boundsBefore K247) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low251 : Lower true (varsX 251) (graphGoal 251) 12 := lower_forest (g:=g251) (i:=0) (hints:=65603) (before_sound K247 V247) g251G g251T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K251 := extendKnown K247 12 [(251,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V251 : Known true K251 := extend_ok (m:=251) V247 low251 (by decide +kernel)
def g253Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffffffe741484e1a15,0x9328000000f8000f83ff])),(BitVec.ofNat 152 (word80 [0xa2024e700480a1805,0x90001084210842108421]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfff000bcb42d01f981,0x328a00001f0001f07c00])),(BitVec.ofNat 152 (word80 [0x2c404ebca42d007881,0x120a318c6318c6318c63]))),((BitVec.ofNat 152 (word80 [0xffffff14af9c9c0194,0x6b580003e0003e00001f])),(BitVec.ofNat 152 (word80 [0xb0828810a794140190,0x6b586318c6318c6318c6]))),((BitVec.ofNat 152 (word80 [0x9316bfaf1e20,0x2732007c000000000000])),(BitVec.ofNat 152 (word80 [0x3f04f09316bfaf1e20,0x2732f7bdef7bdef7bdef]))),((BitVec.ofNat 152 (word80 [0x2157254abe3,0x24540f800007c0007fe0])),(BitVec.ofNat 152 (word80 [0xc00700001112548362,0x20504210842108421084]))),((BitVec.ofNat 152 (word80 [0x49ca15911468,0x54a5f0000007ffff8000])),(BitVec.ofNat 152 (word80 [0x800004800810408,0x4a48421084210842108]))),((BitVec.ofNat 152 (word80 [0xb0208222440a,0x8853fffffff800000000])),0x10842108421084210),(0x0,0x0)]
def g253C : List ColumnInfo := [(16,0,237,0,10)]
def g253A : List (List Nat) := [[],[80,50]]
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
theorem low253 : Lower true (varsX 253) (graphGoal 253) 11 := lower_forest (g:=g253) (i:=0) (hints:=460035) (before_sound K251 V251) g253G g253T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K253 := extendKnown K251 11 [(253,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V253 : Known true K253 := extend_ok (m:=253) V251 low253 (by decide +kernel)
def g254Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffc8b4b4a791a5d44,0xd00000003f000000fff])),(BitVec.ofNat 152 (word80 [0x80500b4a4851181d04,0x5249249249249249249]))),((BitVec.ofNat 152 (word80 [0xc00356b04013cc0de6,0xaa000000fc0000fff000])),(BitVec.ofNat 152 (word80 [0x19b12a040124c0dc6,0x2a0c30c30c30c30c30c3]))),((BitVec.ofNat 152 (word80 [0x1d86c74704fa20e,0xcc00003f00003f000000])),(BitVec.ofNat 152 (word80 [0xae1d06c54704fa00e,0xcc1c71c71c71c71c71c7]))),((BitVec.ofNat 152 (word80 [0xfffca0b1fdeec0f842,0x8a000fc000000000003f])),(BitVec.ofNat 152 (word80 [0x1300a0b1b5aec0e042,0x8a596596596596596596]))),((BitVec.ofNat 152 (word80 [0x60af12a4bf84a1,0x9003f000000fc003ffc0])),(BitVec.ofNat 152 (word80 [0x1c0060051224a38021,0x80104104104104104104]))),((BitVec.ofNat 152 (word80 [0x1d50ac8d518315,0x72fc0000000ffffc0000])),(BitVec.ofNat 152 (word80 [0x20000d10a889100210,0x10618618618618618618]))),((BitVec.ofNat 152 (word80 [0x32304911220201a,0x5fffffffff000000000])),0x820820820820820820),(0x0,0x0)]
def g254C : List ColumnInfo := [(4,0,250,0,10)]
def g254A : List (List Nat) := [[]]
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
theorem low254 : Lower true (varsX 254) (graphGoal 254) 11 := lower_forest (g:=g254) (i:=0) (hints:=303129920) (before_sound K253 V253) g254G g254T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K254 := extendKnown K253 11 [(254,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V254 : Known true K254 := extend_ok (m:=254) V253 low254 (by decide +kernel)
def g255Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfe000001fe,0x1fe01fe0850c713ce])),(BitVec.ofNat 152 (word80 [0x50a142850a0a0a0a0a,0xa0a0a0a0a08404303c4]))),((BitVec.ofNat 152 (word80 [0x7f0000000000,0x1fe01fe0082633eade8])),(BitVec.ofNat 152 (word80 [0x3468d1a34646464646,0x464646464682413e08e8]))),((BitVec.ofNat 152 (word80 [0x3f80000001fe01,0xfe00000000008008401b])),(BitVec.ofNat 152 (word80 [0xf1e3c78f1e1e1e1e1e,0x1e1e1e1e1e000000000b]))),((BitVec.ofNat 152 (word80 [0x1fc0000001fe0000,0x1fe130c308e5b])),(BitVec.ofNat 152 (word80 [0xa3468d1a3434343434,0x34343434341204108c1b]))),((BitVec.ofNat 152 (word80 [0xfe000000000000000,0x1fe011c0fc10f92])),(BitVec.ofNat 152 (word80 [0xcb972e5cb8b8b8b8b8,0xb8b8b8b8b9180ec10312]))),((BitVec.ofNat 152 (word80 [0xf000000001fe000001,0xfffffe0000200001f035])),(BitVec.ofNat 152 (word80 [0x20408102020202020,0x2020202020000000f010]))),((BitVec.ofNat 152 (word80 [0x1fffffffe,0x1c00ffe0020])),(BitVec.ofNat 152 (word80 [0xc183060c0c0c0c0c0,0xc0c0c0c0c1800bac0020]))),((BitVec.ofNat 152 (word80 [0xfffffffffe00000000,0x1fff0000000])),(BitVec.ofNat 152 (word80 [0x101010101,0x10101010065b0000000]))),(0x0,0x0)]
def g255C : List ColumnInfo := [(4,0,251,0,12),(32,0,223,0,12),(1,0,254,0,11),(2,0,253,0,11),(8,0,247,0,11),(16,0,239,0,11),(64,0,191,0,11),(5,0,250,0,10),(9,0,246,0,10),(18,0,237,0,10),(128,0,127,0,10),(0,16,109,130,9),(3,0,252,0,9),(10,0,245,0,9),(17,0,238,0,9),(24,0,231,0,9),(65,0,190,0,9),(66,0,189,0,9),(144,0,111,0,9),(0,2,77,176,8),(2,16,109,128,8),(25,0,230,0,8),(72,0,183,0,8),(80,0,175,0,8),(128,16,109,2,8),(129,0,126,0,8),(136,0,119,0,8),(0,8,54,193,7),(1,16,108,130,7),(8,16,101,130,7),(16,2,77,160,7),(128,2,77,48,7),(130,0,109,0,7),(130,16,109,0,7),(192,0,63,0,7),(1,8,54,192,6),(64,8,54,129,6),(64,16,45,130,6),(67,0,188,0,6),(74,0,181,0,6),(81,0,174,0,6),(88,0,167,0,6),(128,8,54,65,6),(129,16,108,2,6),(136,16,101,2,6),(145,0,110,0,6),(152,0,103,0,6),(129,8,54,64,5),(131,0,108,0,5),(131,16,108,0,5),(137,16,100,2,5),(138,0,101,0,5),(138,16,101,0,5),(192,8,54,1,5),(192,16,45,2,5),(200,0,55,0,5),(208,0,47,0,5),(193,0,54,0,4),(193,8,54,0,4),(194,0,45,0,4),(194,16,45,0,4)]
def g255A : List (List Nat) := [[]]
def g255D7 := limbs80 #[#[0x839e2f0d97e917158120,0x120d78bb4e8da165d604,0x604835e2ed3b36859758,0x15c120b78bc46c7a365d,0x641764839e2f0d96e919,0x546c90900d78bb4e8d91,0x37102bc406f101344073,0x2b1013c40784]]
set_option maxRecDepth 16000 in
def g255D8 := limbs80 #[#[0xc0906ea976e917158120,0x9dc5604833d4cbf48b8a,0x766d4ee8b02419f2ecda,0x5eabb46857658120cf9,0xd60482be5d9b42cbac09,0xd232eb02415eaed1a165,0xe1765c5615c120af9766,0x483e70bb322b0ae0907c,0xc2b8241f38ec57658570,0x6e91715c1209f9766d4a,0x6d4bb748c8ae0906da97,0x82419ea65ba464570483,0x57658520bb5768d0aecb,0xd8742cbac2905ee1b0e8,0x13f86c3a15d971482bf0,0x5c160af5768c8b20bb24,0x48c8ae0b06cb976e9171,0xeed1a15d97058365cbb7,0x60a73f66c3f28b8ac172,0x9b0eb0639fa4e4d9161d,0xd86e51815c29cfda343c,0x13aedc22e6b1ae34e7ec,0x6b1ec9d76e91915cd63f,0x605805dae4fda342bb2e,0x66cbae2b02418e7e9393,0x7eabb46857658120ef97,0x60483be5d1b42cbac090,0xb2eb0241df2ecda165d,0x9b1e8d9758120ef5768d,0x83be4d2746cbac09077c,0x2b8241df26d3a365d604,0x659945c120ef9766cb32],#[0xd5da342bb2e09077cbb3,0x241bf2e8da165970483e,0x7158520df9363d1b2cb8,0x9b40bb2c2907ee1b05d9,0xdea6c176e5171483f65d,0xd920fd9766d02ecb2241,0x2c82ec905fabb4645905,0xed19164176483be5d1b2,0xbf5768d0b20bb241dea,0x2e0b077c994e8d905d92,0x87e5171583e5dda342bb,0xb727d0322c3ac1ce7ecd,0xb06bdba3e819161d60e7,0x45875835edc9f40c8b0e,0x9c9b22c3ac1ae7e93936,0xb9fa4e8d9161d60e73f4,0x7582dedd8343c9b0eb06,0x726c3ac16e7ed1a1e4d8,0xb06939361d60b7b760ca,0x39cfda343c9b0eb05bdb,0xc0ae1f3cec176605615c,0x879061970e73f66c3728,0xdc9f40c8b0cb867db936,0xe15f66c7a0e4d865c33e,0x65c561afb760d0f26c32,0xb40bb708b8ded7b36817,0x27ed1a15d97358edcfd9,0x176cf3f49c9b02c02edf,0xc0b00bb6b9fa4e4d8160,0x9393645805db9cfd2726,0xaf3f68d0f26c02ed9e7e,0x581100de0a106f032000],#[0xa2e72aa26d2251dd1951,0x4c949746541d3ca38d33,0x7464d6265ff5ac559506,0x37d77bb7947416ee69b6,0x9358f88d18898578257f,0x51a2a9f89c699497895c,0x6b25afeae2ac6a9fa78a,0xbe9bd8bc7bb6b84b73b3,0xa2c86c6ac59c3dc21c05,0xd29d0dcf1ce0ccfcbec,0xdc1dbbdaad99d93d56d5,0x3847c11588708e0ff044,0xe01e2419f822219600c4,0xfc113e1f80789067e08b,0xc0610611f046c21c2383,0x67c0610e11f04584c0bf,0xd0a216f80c20c23e08d8,0xf8dc23838d1993f042f8,0x7e08bc23838d1993f042,0xb1b83fc1178470718cb2,0x33c2383bc6f823823611,0x9e11c1de37c11e65ec34,0xb80621c23e08b32f61a1,0xe1e19e11c1f637c11d0c,0x42a4b8870f147e08c72e,0x49f8225490a7147e0880,0xce80c21a23e08a14f635,0xd056c370df07e07081f0,0xc2b61b86f83f03840f22,0x1570f437c1f81c207916,0xe07c10fc17c0f82198bc,0xf81f043e21f03e087e0b],#[0xaf06d1be0fc0c903f82,0x56c370df07e07081e85a,0xae1e86f83f03840f22d8,0x52881742f81f04331782,0xc6135c539a245138a16c,0xc5e10243184d725e2090,0x2dc4786898e20c0c6131,0x50710545a8a0e7868c5e,0x2d8a71218868b5e2dc44,0x19b71440c271423890b4,0x8478af0d15a261215c26,0x40e27430c886c578912,0xc10e8a7103232f10c807,0xc40ae2ac40b0cec4c201,0x2166203867086880ce2e,0x2443080c20822716e1f0,0x10720813041cc3184db,0x1c857136185335628571,0x815808ac03c436204c40,0x9c40762c5108e2dc3098,0x4404662880520819300,0xe1f04140e8bc0f0506c4,0x2c506a2020420822716,0x38802]]
def g255H8 := limbs80 #[#[0x74069a600000013000a,0x3400000000000000000]]
set_option maxRecDepth 16000 in
def g255D9 := limbs80 #[#[0x765c110f3c5d9615c110,0x8f7e8d985d910e3e619,0xb7158120beae91715812,0x209fa6a77158120bba69,0xa77458120bba69b74581,0x120df2e8d97581209fa6,0xe91715c120f3a5d9615c,0xc120beae91915c120bea,0x2e8d965c120f3a5d9645,0x5d9209ebe919758520bf,0xfa683945d9209fa68391,0x8dc5609ebe9191dd9209,0x8f7e8d98dd1608f7e8d9,0x765cd31f355d97358531,0xe375d973e0563e37619,0x5765c110f7c5d9715c11,0x10bf6e8d965c110f7c68,0x917158120af7e8d985d9,0x120fba5d97158120feae,0x6857658120dfa65d7158,0x8120fbae857658120fba,0xae917658120fba691765,0x58120dfa6859758120fb,0xfa6919758120dfae8597,0x15c120dfae919758120d,0xff8645615c120ff85c56,0x615c120fba5d9615c120,0xbfa6a5615c120bfa69d,0x9915c120f7a5d9715c12,0x20dfa659915c120f7a5d,0x59945c120f7a5d9945c1,0x120bfae85765c120dfa6],#[0xe85765c120f7a685765c,0xc120f7a691765c120f7a,0xae85965c120f7ae91765,0x58520ff2e8d965c120bf,0xb95d97158520fe9e9171,0x658520fba6817658520f,0xdf9e859758520fb9e857,0x945c520debe919758520,0xdeb5db945c520deb65b,0x5765c520deb69b945c52,0x20dfa68196dc520bf9e8,0x8196dd120fba68176591,0x920dfa645905d920dfa6,0xe8d905d920dfae45905d,0xd920dfa651905d920ff2,0xbe91915d920dfae51905,0x5d920bfa683915d920be,0xfa683945d920dfa68391,0x15c160bf6e8d965c140b,0xf3e5d9715c160beee917,0x915c160beee91915c160,0xf3e5d9945c160f3e5d9,0x5765c160f3e685765c16,0x60f3e691765c160f3ee8,0xdb945c560f3ee91765c1,0x560cef61f945c560daf5,0xe8d98dc560af7e8d875c,0xd960cf7e8d98dd160cf7,0xfe91915d960bbee81915,0x61d60bbee81945d960ba,0xfee819161d60ef6e4f90,0x161d60cf7e4d9161d60a],#[0xaefe919161d60af7e8d9,0x9361d60cf7e4f9161d60,0xcf76539361d60ef6e83,0x79361d60cf7e539361d6,0x60cf7e879361d60cf768,0x939361d60cf76939361d,0xd60afee819461d60cf7e,0x5d97158570af7e8d9461,0x8570f3d5d98158570f3d,0xde857658570f3ee81765,0x585709fee819758570f3,0x6f5db945c5709f7e8d98,0x460570d6f5db9460570d,0xaf7e8d8660570cef61b9,0x8661170f3ee817659170,0xb7e687905d970af7e8d,0x1915d970b7ee81915d97,0x70b7ee81945d970b6fe9,0x839361970df6e4f90619,0xd31f755d9735c531df6e,0x5d9735c561f75685765c,0xcd61f3d5d9915cd61f3d,0x7e8d765cd61f3de85765,0x5d961af7e8d875cd61f3,0xbd683915d961bb7e8d90,0x61d61bbd68f915d961b,0xafd6839161d61cefe539,0x9361d61afd68f9161d61,0x1ee7e117358d71cefe53,0xb8458d71f375d97358d7,0x71cef65f8458d71eaf5d,0x8d9858d71cefe5f8458d],#[0xd71aefe919858d71af7e,0x69a9858d71af768e9858,0x1171e6f5db845cd71abf,0xfe8d86e1171aefe8186e,0xe1171aefe8176e1171ae,0xefe8196e1171aefe8d76,0x15d971aefe8d96e1171a,0x9fd68f915d9719fd6839,0x7360563af7e8d9061b71,0x3be7e91915cd63f375d9,0x9845cd63f375d9915cd6,0x63f375d9945cd63f375d,0x85765cd63f37685765cd,0xd63f37691765cd63f37e,0xe8d985d163f37e91765c,0xd963bb7e8d915d9639f7,0x7e8d945d963bafe91915,0x61d63af7e8d9161d63bb,0xf7e8d9461d63aefe9191,0x4605739efe9191a1d63a,0xcef61b9460573d6f5db9,0x915d973f37e8d7659173,0x3b6fe91915d973b77e8d,0xd945d973b77687935d97,0x74bb7e8d905d964b77e8,0x4d8160176af7e8d9061b,0x176aefe918160176cf7e,0x6139360176cf7e4f8160,0x176cf7e139360176cf7,0xfe9191e0176aefe9181e,0x60576cefe518360576ae,0xefe9191e0d76cefe5383],#[0x65c120ff6e8d965c110a,0xffa685965c120ffa6857,0x905d920ffa681765c520,0xffa685905d920ffa645,0x1905d920ffa651905d92,0x40febe91915d920ffa69,0x85765c160ff6e8d965c1,0x960ef7e8d875c560fbe6,0x6479061d60fafe91915d,0x1d60efee819161d60efe,0x7e8d9161d60ef7e4d916,0x61d60eefe919161d60ef,0xf76539361d60ef768793,0x660570ef76939361d60e,0xefee818660570f7ee817,0x8661170ef7e8d8660570,0xf6fe91915d970ef7e8d,0x79061970dfe647906197,0x70bfee819161970bfe68,0x879361970df7e4d91619,0x561fbd681765c561df76,0xe8d905d961fbd68d765c,0x8d71fede119158d71fb7,0xf65f8458d71eef663845,0xe1171eef6a78458d71ee,0xef68d76e1171eef68176,0x65cd63bf7e8d905d971e,0xfafe91915d963fb76857,0x915d973dbf68596a1d63,0x4bf76879361973f6fe91,0xd8160176fb7e8d905d96,0x76befe918160176df7e4],#[0x918160176ef7e4d81601,0x176df7e4d9160176eefe,0x6139360176befe919160,0x176df76539360176ef7,0x76139360176df7687936,0x60576df76939360176df,0xefe518360576defe5183,0x12601c802880260000e,0x7812e0206039c06580af,0x7e40ee81b7032205c00a,0x53209e012b8236042a0,0xb037006800c4017502bf,0x164219840807c40f041c,0xa06139c26084a008f41,0x385c10b3615d42aa0529,0xa94342065e0c7a18482f,0xee41d0838e06f10d961,0xb0830101e1fa43dc8798,0x41447208be113021dc42,0x134a26104b1894212422,0x38a8614ac28c050289d5,0xd6c59a8b1415d22b2055,0x187830445f30bb617202,0x50d0419b232b86440c5d,0x73c6d70d881ad8352c69,0x1d2e39b07208e161bd63,0x70f321e183bc07650eae,0xfe07e68fac1f0c3da87a,0x214e42048329044203c3,0xf917922b044a087e90d2,0x988920922023e0473c8c,0x264a4bfc96a12ae25064],#[0x813cf275c4e349b89346,0x27ca3a1453286450449f,0x2af65554a9a150929b25,0x8162f2c1c578cae115ab,0xbacb6516a92d1059b0b2,0x2f525df8ba997282e185,0xb9871309660a8bff97d4,0x518c8d98fa319e62ccc4,0x341c67a0ce1199c32e26,0xb9ad6356a6a14d2a9a2f,0xeacdc29b69367c6c4cd7,0x38a070bce021be8378e6,0xb1cf03994727ce3f1c6c,0x688ec31d6a3aa674c8e8,0x3c5c7820ef11dd03b727,0x29ec43d507a1cf331e4a,0xd74fa31f343e307bf0f7,0x3fe67f5cfdd9f9f3f067,0x1207040bc811d01aa014,0x3ad06a20bd4156825104,0x42b28509093210f41fa8,0x1a1cc436a86790c3a170,0x94511d2228441887e90f,0x8d1384781e083e3c4d08,0x48a1984781e0f1244184,0x7a3311e0f81c48c08494,0x8ae2e1183d87e0e20303,0x4783648a6561183f8364,0x6561183f83648a0ce0f8,0x821c900ce0f84783648a,0x9a235a50cb890879383f,0x3f830c8c0cd938460fe0],#[0x8460fe0c3230b161e118,0xd83e1164f822c0e2c587,0x570879383f830c8e0c98,0x48ba370fe08b1c40a17c,0xc3f83648c88310c3f836,0x5c3d87e0f10309688310,0xdc1495e0f81a48da349,0xf8fc370525783e069237,0xc49106a2384d11e0f800,0x2382d2512286e11e0f81,0x4248301002de0f814469,0x330658ae3611e07820f8,0xa1963313e07838403e48,0x87130cf81e0e1838430c,0x15713a3783e0518405f0,0xb8460fe0e20700c12310,0xc03161183a21e0d92398,0x1c00ce0e88611e0d9241,0x10a30860fe0e10e48e1d,0x3c218460ee4f82310c3,0xb030af08610e4e0fe09b,0xb93840f0861183b93e09,0xb921d0a1d0621360fe0,0x83b93e0e106c0f8460fe,0x183f83843926c101405b,0x9384782688be30730cc2,0x60e64e11e09a22f8f839,0x560f64e11e09a22f8e06,0x2c1a383e1164f822f8e2,0xc2c1a383d93847822f90,0x8a0ce10e360fe08c2404,0xd8b83e10e3782188c315],#[0x307562f0088611e08623,0x168f64e1183f822c05a,0x822f8e88592c0783844b,0xe10e4916360ee4e10867,0x8c43c32311a230e0fe0,0xe08b0498d0ce1183b93e,0x3c326b8a563610e4e0f,0xbe318d0ce1183f82e48b,0xf821c936360f84782e48,0xf8f15c3262421e2f8783,0x2f8c2a710e2f0fe0ca22,0x2c44a238a3c3f8324f10,0xfe08c43021a4874c3f8,0xa3c3f822f8c28a93c47,0x2e8dc470fe08be38c3c4,0x2baa3c3f83c40bc3aa8e,0xae3687c3f822c71030be,0xf10308c2c70fe0f10a88,0x4693e0832358dc38a7e0,0xc3f83a4b112c0c1cb0ec,0x21cb0e0cf82c46923020,0x321d2a30850ee4f83441,0x11943b93447823112b0c,0x278743f821c901cc3308,0xe4f83442b03c330878a6,0xee4d11e0ab04c330850e,0x822c71030730cc204750,0xd93e0b10310da3587c3f,0x830ec40a7e0d923232c3,0x2c68d64b0fe0b1129108,0xf08713e0f81876303232,0x1445d870ce11e0f81880],#[0x3e1003384783e059288,0x18b184783e0620384430,0x18611e0f8164a204c336,0x3e0f81840b040400cc18,0x83e039384100941c8859,0x783e004434201104048f,0x4f83e06102c10e4e1086,0xe0393840b038250812ee,0x5c4783e0320440c87783,0x87e0f81c41091417a1a9,0x783486923a448c8b0c86,0x4f83e043234c0a6855e0,0xe2693e0f810c8d11389a,0x203a2108f83e03102c44,0x3103445618b1c4783e06,0x8783e00b62c2e88783e0,0x61a20c4783e010e24330,0x466d93e078240748c827,0x92c4783e0101cc631370,0xf83e0710444c1a85f885,0x7821c881b632e2e2161,0x3a3244783e02202d93e,0xb02f0c67f04e4f83e02b,0x783883923f05e0f80e4a,0xe20e48542a4c0dd11e0,0x2e20e4f83e02b02f81e,0x82c47803e21e0f80e4ab,0xf83e0064323362a202c7,0xf800ff1010901ae2164,0xe0f81c403e3845628a3e,0x1e0f81a4844384228c93,0xa3e0f81c4044303328b1],#[0x88fa3693e0f80c40aa48,0xc41011855a4b11e0f812,0x424525e868cb8de0f81,0x1b497a1a32e3783e071,0x6c8cc30c8687e0f81c41,0xa9a17e1963693e078248,0xcf83e0692c4430346190,0xa7f0563693e0f818c0e0,0x20c68ce4f83e05100f92,0x3361c43e0f80c40c1043,0x99785587a3783e07104a,0xcd9309783e031034458c,0x434454c433e0f81080c8,0x3e1090cc22044783e024,0x3e383506b8d44783e00,0x4042421b0d043e0f8184,0x120e1168a88f83e003f6,0x110c10d1248f83e0690,0x81c4844431248f83e069,0xf80a40a1203548a91e0f,0xac21e0783888dc3713e0,0x8d12e4783e004437121,0x90342344f82e4780110d,0xf83e00c0ff0c0f783e05,0x4027e0f80351308b9009,0xc303de0f81640d44c22e,0x7c1e8d24783e0434403f,0x4011783e0491c4972b21,0xf81a4125003e0d02c150,0x10912ad05a8dc1b15e0,0x32444c2ac8d707a4783e,0xa40e4c707a4783e02ac],#[0x812b1208f8a2b21be0f8,0x988e1a05f14c4e91e0f,0xdf83e06903143e0f80a4,0x8d38de0f81a41008f120,0xc0f783e0390324545f06,0x3f6303de0f80e40c0fd8,0x1442b18e4783e014428,0xe0f800f430331ae4783e,0xc0f783e0430e40d63391,0x8c09e8ce478344f80358,0x4c322827a3391e0f8144,0xe0f814402c4389e0f81c,0x1e0f810d1065223a4c1b,0x9384436462c45d87c361,0x78107901010d06f83e05,0x40b0412e295920b78384,0x84102941ec3593e0f818,0x432361104048f83e0393,0x102c0e86f83e0610e484,0xe102c0e2912fe0f80e4e,0xf80c40b0321fe0f80e4,0x8b423e0f80c40be1ca5e,0x58b60d61f83e00b1c410,0x108b42f29783e0310344,0x22dc378a09837e0b11e0,0xb70ce2d87c4783e00364,0x62a35e18b1e0b11e0118,0x7c349561f83e07103a2d,0x96c5687e0f81c4048389,0x38d0c687c4783e00363c,0xc40e0d783e0692c44303,0x1c4124d8408d593e0f80],#[0x31163465e1561e8de0f8,0x340c68ce4f83e05100f9,0x23564c25e0f80c40c104,0xc8b08713e0f804ae303,0x564f81e090e2783e0713,0x83e069045426686b48e8,0xf81110b11632a762161f,0x1393e0f80cc0f64c99e0,0xe4f83e029ccc0a67f0da,0x44281664e91e0f81110c,0xf83e05904587a4783e04,0x591110d1119f4d52da1,0xa4783e04442816a4f83e,0x8b0c9a23189080721d87,0x874136106890300be2c3,0x2b89a1920386015c32e2,0xe2d89082a238c530833a,0x4e28634404c28c4b0c32,0x90cab0abd89082a4307,0x998bc14a2287416d1014,0x22614626310870a28c22,0x8a42073a1882c38a1012,0x18634404c398b088761e,0x1302764b10386c1ab8ae,0x31358a1c99a28781d062,0x62346313026e25922c6,0x1a4c1c8c1e44c0998bc4,0x942b0e299e2a62e2d88e,0x896ab162250e2988325a,0x311a2862286da2e86188,0x1e8a626861cc62286c48,0xe0f98a1087621898c45a],#[0xa1a86015c32e2b88130,0x4586880a4c0a74438708,0x1589b62f05130a0fa32c,0x6480c95b8ae1a4d440b,0x2270560632270568ae26,0x2b08624201c864b68ae2,0x341876148661c234541b,0x21a0204aab03a1a44ab2,0x71108511ac4d0651132e,0x862c38a101222643c2f0,0x1d882c38a488662c221d,0x10b0a7a3386283e62842,0xd8b4888626310870a213,0x1c8911633a2620244550,0x862e8809876258aa2586,0x63388690246226d8b130,0x27a501b312238ba1081b,0x241a62e2b86934902a5a,0x20896b8a944902330cbb,0x28a098761c454d52d6]]
def g255H9 := limbs80 #[#[0xc11401000811010,0x614000000,0xc0000015880026c00000,0x14300000096a0000053,0x0,0x75200000000000,0x1560000000071c00,0x0,0x2c800078a000000,0x19500000000000000,0x68a0000000000000,0x5181ab8e0,0x1a4f01f3c00000000000,0x65806c0000000000000,0x1e67104b9000a9c005b,0x36500000000210d930,0x29d800d7a27c00000000,0x7c600000,0x7000,0x62a00000000001f21258,0x21e00000000643,0x3a20000008340000000,0xdf000000000007b3e700,0x786d44002,0x12200000,0x1f08000000000000000,0x0,0x140e27000000,0xa418e5b4580038900000,0x4c9178b9d,0x6200040f000000000,0x601],#[0x9650a00000000,0x12bc000000000,0xb0ab2400382000000,0x7000a5c0000000000000,0x73,0x25474000000000,0xd240000000029a,0xa0e0034200000000,0x1c764e0000000000,0x526000000000,0x3dfdc1]]
set_option maxRecDepth 16000 in
def g255D10 := limbs80 #[#[0xdd2ecb02413bf9461d10,0xf4bb2e0905fa65d60483,0xd72cb8241deb765c120e,0x4c86e2905ebe5171482f,0x321bb2417e990dd120bf,0xc9b0eb073e5d970582fd,0x28c3a633bf94607709ef,0xa702b1cefe518758677f,0x8c0ee7cdd765cd639dec,0xae0884efe5181dda77f2,0xb8221ff1715c110ff8b0,0xe08877edd970443bf2ec,0xa21ef57658510dfcc32,0x2885fd65d614437eb0eb,0xa21bf5865c510fdbca2e,0x886bf61976442fef2cb8,0x213ff985d9109fecc2ec,0x85fd64776442ff321bb2,0x13ff97619109fecc6ec8,0x4ffe598744377f28c3a2,0xfeb7158120ff4b8ac090,0xfadd160483fd2e8b0241,0xe9715c120ff4b0ae0907,0xa59170483fd322b8241f,0x9765c120ff4ca2e0907f,0x5c561483fd32cb8241fe,0x9758520f76bb2c2907f9,0x5971483f5f28b8a417ed,0x459120bf6cb6e2905fbe,0xd64483ddaecb2241fad7,0xdd120bf7cbac8905fb65,0x76483fd320bb2417ed96],#[0xd920bf7ca2ec905fbe45,0x7503bf2ecb82817ed91d,0x560f7cbb2e0b04ffe598,0x582ff321b8ac17bf945c,0x609fecc6e2b05bf65b71,0x82dfb2dba2c17f990dd1,0xf7dc82ecb04ff663745,0x27ff22c3ac1bfb9061d6,0xe7ebb2c2b86f7e4d8758,0xf7f28c0ae17bf945c570,0x7ebb2c8b84ff65b815c2,0xf720bb2e13fd96e1170e,0xfc9b0cb877ee41765c2f,0xb02b0ee13fd91e1970be,0xc32c3b873f5d961dc37e,0x22c36e13fd9858770d7e,0xb2c298ff55cd614c67ff,0xeb0a63bf58758531f7ab,0x2e298ff55cd714c6feb2,0xb8a63bf5865c531fdbca,0xe698f775d9734c6fef2c,0xb263bdd865cd31eefbb2,0xc98cff661764c75fb0cb,0x2637f591dd9319ffcc2e,0x98cff663764c6fbb27bb,0x63bbf9461d319ffcbb0c,0xdfde41715867ff2cc3a,0x3fb7945c561bfbc9ae2b,0xf3f5d973587deaecb8ac,0xcfd76dcd61bfac8ee6b0,0xff66373586dfb2db9ac3,0xff9061d61f7bc8aecb0c],#[0xfe4d875877ef22c3ac33,0xf8460171ddfca30eb0cf,0xe11635c67fb2dc02e3bb,0x8460d71ddfc22e6b8eef,0x1b845c67fb2dc1ae3bbf,0x3e1171ddec8708b8eef6,0xb845c777aedc22e3bbd9,0xe1971bfbc8aecb8eef65,0x63dc67fb27c32e33fd90,0x8f71d7ec32c7b8ef760d,0x6dc67ff20c36e33fd985,0xd43eeebb2e6a1cffe4d8,0x58f7bae7c0ac73ff9661,0x639fecbf02b1ebf5db81,0x8efbb27ba2c7edd765cd,0x39fecc6e8b1dbf65b745,0xefbf26c3ac7edf935d96,0xdefc9b0eb1cffe458758,0xdfb2d43ac77dd93a1d63,0xfec8f0eb1cff6628758e,0xfb2dc0ae77bf94605739,0xecb708b9f3f5d9645ce7,0xf26bb2e77df935d9739f,0xc8b0db9cff647865cfbb,0xedc02c9bbd74e01649ff,0xa706b24ff65f805935fa,0xfc1ac9afd76e0d64ddeb,0xb0eb24ffe41875927fb2,0xc36e93ff9061b749ffc9,0xbb5f7e4d805da7ff26,0xaed7bf94605769fec8f,0x6bb4ff64f815da7fb21c],#[0x2ed3fd90e11769fec8f0,0x887fe5d9704427fb27c2,0x21ff5765c510ffccb2e0,0x86ff61d76443feb22bb2,0x1fed765c520dfecc2ec8,0x7fb64576483fdb2cb8a4,0xfed945d920ff7c8aec90,0xfe65970503fdf28bb241,0xf9915c160ffcb8ae0b07,0xfe5171583ff328b82c1f,0xd875c560f7ebb2e2b07e,0xe4576583dfb22bb2c1bf,0x945d960f7eca2ecb07bf,0x45875837fb22c3ac1eff,0x461d60dfeca30eb06ffe,0x5615c3feae2b0ae1bff9,0x58570f7ebb2c2b87fd60,0x715c2ffb30b0ae17fd97,0x570efebb302b877f5d9,0x45c3bfaecc22e1bfd866,0x970bffc8aecb86ff6198,0x5c3bff22bb2e1dfd915d,0x70effca2ecb877f65176,0xc2fff22c32e1ffb90619,0xefec8aedb87f7e4d865,0x7feaecb8a63bfd9161b7,0xfeecb2e698ff75d9734c,0x7fb0ebb263ff5915d931,0xfab9ae2b0eff661764c7,0xfaecb9ac3ff5915cd61f,0xecc2e6b0eff61d73587d,0xf20bb2c3efd905d961df],#[0xc9aecb0fbf64d76587df,0x26c3ac3bff9061d61f7f,0x9ac6b8ffd645635c77ff,0xcb1ae3fbf8458d71feeb,0xac6b8dff65d635c7dfae,0xb1ae3bfd9858d71bffcb,0xecb8f7f5d9735c77fd30,0x32e37ff935d971bffc82,0x7b8dffe4d865c6fff20c,0x6e3bfd9061b71dfecc2c,0xb1ff76597350f7fb26c3,0xc7efd7660563feeb9b02,0x1ff76457358f7fb0ec0a,0x7fdd945cd63feec22e6b,0xdff6617458ff7b08ba2c,0xefd7661163bfecc6e8b1,0xbf6457658f7fb0ec22c7,0xfd945d963f7fc8aecb1f,0xfe458758fdff28bb2c7e,0xf9461d63fefc9b0eb1df,0xe458758f7fb22c3ac77f,0x9461d63dfeca30eb1eff,0xd9815ceffb2343ac7bff,0x661173dfec3302b9f7f5,0x5765cf7fb0cc22e7dfd7,0x5d973efec8aecb9dffe4,0x765cfbfb28bb2e7dff91,0x1973bffc8b0cb9f7fe51,0x6dcfbfb22bb6e7fdf936,0x964f7ec82ecb26ff6458,0x593dfb26bb2c9eff905d,0x74dfec830dba7bfe4d76],#[0xdb7fb02c02edbfd9361b,0x6bffc8b00bb6ffe05805,0xb7fb08c02edfdf936017,0xdfec0f00bb6ffe11805d,0x7fb09c02ed7fd91e0176,0xfeca700bb6ff647805db,0xfb06c0aed7ff9060576d,0xfc9b02bb6ffe0d815db7,0xb21c0aedfbf9460576bf,0xc9f02bb6ff60f815daff,0x27c0aedbfd90e0576bfe,0x2306bb5ffe45835db7fb,0x3c1aedbff8460d76dfec,0xf06bb6ff613835daffb2,0xc22edbfd94e0d76dfec8,0x8bb5ffe4d845dafff20,0xb2e17fd93e1176bfec87,0x6b8fff645865c3ffb22b,0x2e3ffd9858d71ffecbac,0xb9fff64d765c7ffb20bb,0xedffd8160176ffec8aec,0xb7ff611805dbffb22c02,0xdffd8360576ffeca300b,0x6f00660003ffb08c1ae,0xd68168025803c005a0,0x60b1c14a024f0426078,0x42607d40e941b9033606,0x42c4054309ea129c2358,0x281b3c345064e0c24173,0x852102c1f683ca87500e,0x4c8095d1242239444b8,0x22af05400a441410273],#[0xc63182a2f1c5c10b4616,0x86c30d531a2e336c64f8,0x123b347440e431c0e370,0x6220283f3c7c50f571e,0x48e6919122aa441c8581,0xa04be495e9281248a482,0x4b228da50a09ed138c26,0x8afc95ab2acc54a8a729,0x2e5d24b8b16da2d2a58f,0x8cc31206150c0797d32f,0x4d0e19ce33246534c889,0x626db0d981aeb354c698,0xce6396671dce1d9bed37,0x4f121ddf3b227530e8c9,0x3c7d88f931ed83d4a79a,0xca4140819100f9fe33f,0x5108a1cc43448599090a,0xf28d1918522ce4512893,0x49348c090911f423ac46,0x92ff25b04ac494512632,0x269d3938926d64d3498e,0x8f5514ea189405a7cf4f,0x95272a0953aca6454aaa,0xeaaec15ba2b1d559eaa2,0xd2a59eeb2c9636ac3a57,0x172fae115bbcb6ad6b7a,0xd6bebd7b52f255dd2ba9,0x1716246c35583f30305f,0x196e329764a4c8358dfb,0x6d0f99f3b3a266cccc6,0x62d6bacd5d9a8b34c869,0x5bc7b7536e0adb01b34b],#[0xc6e479c6838797068df7,0xae97524e911cffb9b172,0x9e3c3c1877a6edf1d9bb,0xbcf865ee13d6b7a4cf31,0xfed7f3efd45f78bea37c,0x60b5412581af020201db,0x6b0be615ec25d8443070,0x4df88ff10a21dfc37186,0xe33746208bc9165a2a44,0xf51ed63b847348df11ac,0x953921d232644248368f,0x2575ca9d948d27be4d0c,0x6d317e60d4bc396fd2cc,0xe0f9b8335f269bccfb99,0x27bd4f359dcf3a66725c,0x7943de850505ba02d3f2,0x2cba4fb48be8f5519ca2,0x6a1253dfa7354d569885,0xf156aaab75517a94b51a,0x787ae855bd2b4ed646ab,0x2c7dd8a4b0655fdabe1d,0x336976d10d9d3b32f650,0xc0db77f6dc6d8d5adeb5,0x2ea5dd06b983723ae295,0xf77ab6f345e1abbab764,0x78c0677f72fc75f49bd,0xc10c6205c2b3840b05ee,0xb4b921083f0610360f81,0x2060cb4821c983c23823,0x8e094860cf258d07e0c,0xb1a0f08e086460cc1c21,0xa4ba571b0f43e0e207e4],#[0xc1a486454421f83490c8,0x8650f4644704a432210f,0x4050c0679210e0f02103,0xae0f0310354b93c1e04,0x81b07c1e006310282e87,0x31018170d83e4707801,0x1a0b72783c0840f43e0f,0x1c17438570781881830,0x43e302f0d0ae450f83c,0x8e07044242261091e07,0xc2381c186100c628643f,0xdc0e086712388832c6c4,0x4c2123c0e087c7064218,0x184684f0383880f8e0ac,0x1f1b1109e0706201f1a,0x70710201e8d09e07071,0x13c0e0e203e3c308a13e,0x631b81c1c408466302a,0xf8e460562781c1c407c7,0x101f181746c4f0383880,0xe070712191b1346e0f03,0x89489e070427881e8c88,0xb2551b13c0e0e2026451,0x180c13a37038389c40c0,0x381c1188a0509e2381c1,0x6654220fc18832466362,0x8834868441f82c988328,0xf82c988328664c220fc1,0x70cb261107e0b4468441,0x188ec6628660f08e0984,0x5922b1818c662c1e11c1,0x983c23822d1d8d0883f0],#[0xca50883f04324038b0c,0x10e4c1e11c10c9062637,0x1870e49e0e20a230e856,0x2710312a9387e0e20a23,0x87e0e20c03184a387e0d,0x9198d87e0e20c22f188b,0x710521d8c4ac3f07114,0xc1a4e20b0312e8d8724f,0x12ca587e0d2710391b0f,0xc4ba314b0fc1c45247a3,0xc11d10c62561f8388a48,0xe21922d483288087250f,0x746c3f0710c91e8d87e0,0x12a8d87e0e219239489,0x32c60c62611c1e043883,0x8902d8d89c4707810e20,0x83e19e184383c0841489,0xe05d2b1143e0f0320408,0xc40c064470781490c8c1,0x78188a48c22257078149,0x64470781490c8c220cf0,0xa48c22257078149c40c0,0x383c0110c220cf078188,0xe4a2383c01113c90822,0x4381c1c432461d0d8321,0x19620e793c1e0440809c,0xa28a349c4707810c22a5,0xf860c50f11c1e046470c,0x49178c18a1e2383c08c8,0xf078018c40e19e0f0311,0x690e0f031149183246a4,0x407e24194470780221c1],#[0x8e360c0679288e0f0044,0x28c245f2be4c4383c08c,0x98e190584e8d8864f038,0x101f180c8a24f0781880,0xe0527101f142149e0f03,0xe8c13457078149c411c1,0x3e304e15c1e062192302,0xe06203e3c2511c1e0444,0x78109c407c68691a13c1,0x7a342783c0c407c60370,0x100c0d0d07d11c1e0084,0x781880f8f0de0f003d88,0x6e0f031021198c0a84f0,0x698d8984707810d201ac,0xd6342383c0c48687110,0xf1c158948c2383c00f8e,0x203e39181589e0f03101,0xc0c407c605d1b13c1e06,0x22783c009e207c4d1b83,0x1464470781890d0d4625,0x302c9546c4f078188099,0xf0066304e8dc1e062710,0xd88e0f006828142788e0,0xc8108bc1e04459021158,0xf2383c0888807e0f0222,0x411e407f83c010904509,0xd12b13c1e0521223d144,0x8c062522783c0a404c70,0x3480f8a16c4f0781480f,0x992b83c0c4d208e0f031,0x901144f0780221817860,0x1f1c2711e0f0312c81b],#[0x625903087908908f078,0x9111e0f003c384e23c1e,0x704e91c0e08c060287f,0x1f0781482783c0a40844,0x83c08d0e1eab22f1546c,0xa470780331a8c18c1d23,0x787e0f029021101e13,0x821e0e0c170ff2123c1e,0xc70780c80f0c1864703,0x944c6e460f83c00c0e1d,0x8021198dc8e0f00301e1,0xe0705902117914609f07,0x48686a370780c8108b46,0x83c0c4d2060312383c0c,0x1106b83c0a462461122b,0x4b20442f078189640885,0x318984707810f2383c0c,0x6362711c1e043c80d318,0x2938644707801f22240b,0x84352783c0c407c80d06,0x282786e0f03114918401,0x220f86b8616e0f021052,0x8180c88e0f02921a1854,0x3114918444ae0f02938,0xc94470780221c441ae0f,0x7242dc1447004430a82d,0x444e1827c1e0621923,0x161c6e1b0d05b9288e0f,0x14b10407ca488e0f0034,0x52c4141fe18882dc1e0,0x98c370d8582786e1f078,0x83c08d0f8664f0781880],#[0xe0f031149178c18a1e23,0x83446a4f0781880c0e1a,0x80221c1712e0f0311491,0xe0f0044407e241ae0a23,0x783c04692181206b9288,0xc432460d02c2746c432,0x2783c0a4248709c2b83c,0x17c4f078148490e0bc32,0x8490e17e0f0313481432,0x290921c178644f07814,0xc1e06269028682f89e0f,0x2f0d12e0f0312c81c2f,0x2444282e25c1e0625903,0xc1e062590221783c0646,0xc6589921af2783c08811,0x60705e1993c1e05203e3,0xc8a48d22c372287c1e00,0x70780c8a48e134870780,0xcc9e0f02901f1c2696c3,0x382d21c1e032292302f0,0x87c805c4b0dc1e032292,0x30c24330c637038308c4,0x903a0f8431308e0f003,0x3e45158c1fc4703830c1,0x1890214604513c0e0e20,0x3e40610b46c4703821f,0x8308e181889b13c0e0e2,0x4a6611cc549c3b1b838,0x87e0947103d24a388c3f,0x61f82c9c418863118593,0xe52a361f82c9c4160825,0x181cb187e0b27106218a],#[0x32620486421c1e042313,0x311cc01f1006611c1e0,0x4405a38318b08e0f022,0x83c0c818080732611c1e,0xe0f029290288b4309e23,0x3114928c01f250804588,0x82474223004c3290e0f0,0xc3c100444510e0f01938,0x58c41310e0f019388110,0x8871105c251064f0780,0xc9c4111064e2383c047,0x32474304c7431137078,0x93c1e0620b0404f11c1e,0xe0f0193882c1236140b5,0x781882888471c8da3310,0x9e0f003e514c92c50ff0,0x781494c87c810833104,0xc1e0527101f1c4446c47,0x14693c1e06203e4060a3,0x4196370781881090260c,0xd2710c6e0f00623d144,0x7413a2a4383c0c40c481,0x931a9388e0f00302d24,0x92149e0e238118169036,0x90651b83c064e203e38d,0xf232221094783c064e20,0xa2346783c064e204438,0x4642457a332783c00c62,0x21864e2383c047088811,0x40af8bc30cf07803a2a3,0x11c1e03243f191c6c104,0x227178710e0f00724d1b],#[0x221c1e0327101f265719,0xe0f0193880f8e261006,0x183f88e0f021a211c302,0x1a86b1b83c0846243e43,0x7f1308e0f00350d0d94,0xa1144f0781880f901663,0x2d1b11c1e007c6840851,0x6827c4f0781880f90184,0xa287f83c064444423860,0x41a89a4707801f489689,0x24352383c0c49683e408,0x243091e0f0313480f8e2,0x270c2471348e0f00b41b,0x8642022c4f0780c88894,0x511e0f0312c8110c3a0f,0xf8682c22c4f0780c8889,0x8d11e0f0312c8110c370,0x2c80f8d86c4f0780c80f,0xd23802a139186e0f031,0x91c1e006a2258441a89e,0xa428095007c545610624,0x14255590b8309d1b83c0,0x87c54222b6248dc1e052,0x130d518adc1e0523125,0x552383c0c495881b8894,0x1348e0f004e1b2140134,0x995b83c0a42846868d3,0xf0a220d70780c6a40848,0x443c8119c1e062590221,0x6407c69023783c0c4b20,0x781896407c6a37078189,0x2a462783c00d06c7a370],#[0x187219e0f0312c8110e2,0x313182035c1e06259022,0x1509c70b0698dc1e042,0x7802a138e1606a2383c,0xc1c47004e2a1c2c11c47,0xe1b8308e006c68404e93,0xec9e0c23805814900d62,0x4e1b8308e01605c4c681,0x9649e0f031052262c0f6,0xa4f078052c4101707e18,0x383c0a48683638bb0c4b,0xba4f0711c0150a481162,0x278388e016036291c2f0,0x163084445c1e0327104d,0xc591bc1e032710221c79,0x5162905f83c064e20b04,0x34599388e0f011e221c4,0x6c6e384f11c1e03246e,0x3c0c414870d05911c1e0,0xf0193880d918625b278,0x11c164f006e304c6827e,0x1716193c1e062036404f,0xa2d1ae0f0310c92c1029,0x992b11c1e03262c40d,0x204349e0e2380241a0e6,0x8809d158dc1c47003634,0xe1c3012a4f0711c0120b,0x203e3d2631c1c4700362,0xc064e20906d1b83c064e,0xe204438f234221094783,0xc90c620a2346b83c064,0x78888114682457a37078],#[0x3f1a1e341864e2383c04,0xe006c6e451b10c9e0f00,0x193880f90980b06911c1,0x64e203e38604027e0f0,0x781896446070c08383c,0x17e0f0312c8110e22087,0x8882dc1e062591181c95,0x8872545f83c0c4b20443,0x89110c390cf078189640,0x70780c9a4181ae0f0191,0x448f074a18c84c449188,0x873198813193c1e05204,0x8039230dc0e0b26901f1,0x4c52088cc438bc324707,0x690222445198870780c9,0x81112398cc409dc1e032,0x7c81da85224ce0f01934,0x221c401848f0780c9a40,0xd2044303930c9e0f0290,0x3c1e05204428ef83c064,0xc8304011e0f01903c199,0x429a098892d11e0f0292,0x26f0781496408891e0de,0x783c0a4b206a38ee4311,0x4e144783c00f8ec91004,0x6783c0a4b204430848bc,0x9a4b13783c0a4b204442,0x480c9ae0f0292c8110c,0x780c8a48e136452783c,0xc1e0326901f192d8609f,0x45b0dc1e03253148270d,0xc4fe0f0290c91110228d],#[0xc24783c064d203e446a2,0x1e9864f078148110e200,0x221477c1e0326902218,0x4f0780c81c0ec9e0f029,0x25c1e052590351c2e12a,0x4c86383c0a4b2044385c,0x88e9a0c7078149640887,0x1051204018628f03f192,0x2b60c7180ae32c51d09b,0x3122750903711614541a,0x41160ca040f06e3309d1,0x14ac22c18f210f8670ac,0x186287e345122421f0d6,0xb16882248c4091a88840,0x431135209838f1421f8c,0xbd1070984944071e3147,0x74381b0b45148270f194,0x9087d3496a2889891124,0x4451a4bc593144491035,0xd]]
def g255H10 := limbs80 #[#[0x830031403c01e60c3100,0x10010011cd0010000460,0x2c100504420100104,0x52020022d40450c1280,0xe000b4d1895581012022,0x600015de25b1522958d7,0xb5cad111000000000016,0x5c8002d5e00000062660,0x102ae21d1f4000c585,0x207c404c6a9668000,0x5472a14c678b2800027f,0x700043b8000000602b39,0x21a1ce063,0x58cc00000000000,0x184c000461da540000,0x84fd6c423c000000b508,0xe0c71e0afe00d58a1091,0x46944448000000c4292c,0x70bb41c6fc01b000317,0x23a2c95641e00002f780,0x34d33b5a80000003b061,0x5d7eab0003b6f0ae0007,0x876ca48000264b4e8001,0x40006e2b2fc1d9dd1ae0,0xb000000000000000009b,0x1849d300000074c6,0xe60000000000000a0e80,0xbb000142144100000000,0x3819dcfc7a04c3,0x10484fc0007689c0042c,0x148d000400ed60000000,0x19c80008bc837000000],#[0x12c855452cc8466d300,0x495713400065f00000,0x8c700020565002f30,0xa2988ca53e0002443298,0x5d77619e52e218000000,0xc000000047e000000136,0x724f200006b99730a4c6,0xfd83b800144feb737a80,0x698bda4a,0x8179048000000a403550,0x3c0800081a8844001,0xecc256819ccdaae47b4e,0x88000000000671d17552,0x21007962b8000000b2,0x6fb3d24e904400000000,0xaa30000002c7a0005,0x142f0002804,0x95fe00052748b451d40c,0x1000332c1e2000000722,0xe9e00000030bc44,0x764f0a400000000000,0xa300000000263a040000,0xe54d0438d2170e6f141b,0xe8800016a7c1c000240f,0x74c07339028000eb2c5e,0x11bc000000384d12,0xc7ee103080000cc8c400,0x6d61185d4a9bd63707a8,0x30693e8000e96a,0xb3a800350b4180001a88,0x201e000000306f49a63b,0xb00000000006f6000000],#[0x3df7a2b0003b1400007,0xf956ed241ca1a4506b00,0x204a000a25fbe00012,0x1b900008dc7420,0x72d1c952b51121a1c000,0x9ce900068f8000000000,0x48f00008b10000001cf,0x53ca0318000000000000,0x2a2ece26b6a32a02c5]]
set_option maxRecDepth 16000 in
def g255D11 := limbs80 #[#[0xe1171fe970483fa58120,0x443fd58510ff970442ef,0xbfd87442ff61910ff571,0xdc520fed71483fb58520,0x483fb5d120fed64483fb,0xfef76483fb5d920fef74,0x5d140fbd64503fe5c140,0x582ff61d40bfd86503ef,0xbfd87583bf5d960ff970,0x5d970bff845c2ffe0570,0xdc2ffe1970dff765c37f,0xbfd86dc37f5db70bfd81,0x5cd31ff5714c7fd58531,0x586ff61d31bfd864c7f7,0xbfd87587bf5d961ff571,0xe1171bff835c6ffe0171,0xdc6ff60371bff865c7ef,0xfdd7350eff61b71bfd83,0x61943fbd7450fef59143,0x58effe0563bfd8750eff,0xefd7658effe1163fdd73,0xe0573bff8758eff61d63,0x5cf7f5d973bff845ceff,0xbfd81dceffe1973dff76,0xe0164bfd86dcf7f5db73,0x593ef5d164bff83592ff,0xbff87592ff61d64efd76,0x61b74bfd83dd2ff60374,0x5daffe0576bff805daff,0xbfd80ddaffe1176bff83,0x5d910bfd83ddaff60776,0x583ff5d940fff76443ff],#[0xffd74583ffdc560ffd71,0x5c570ffd615c3ffdd160,0x5c3ff59170ffd815c3ff,0xffd865c3ff5d970ffd84,0xdd931ffd764c7ff58770,0x5c7ffdcd61ffd73587ff,0xffd735c7ff58d71ffd80,0x61971ffd765c7ff60d71,0x58fff5d943ffd63dc7ff,0xfff7458fff5d163ffd81,0xa1d63ffd8758fff61163,0x5cfff59173ffd815cfff,0xffd865cfff5d973ffd84,0x60576fff805dbff60176,0x5dbff60d76fff815dbff,0xfff845dbff61176fff83,0x23c0e805501b005c000,0x815909f047c2080d9059,0x3082c3d01cd0d9065c2f,0xc82c115109fc4c024511,0xc90ddc6b033d18f0bfc5,0x8a842d2070fac7a03b11,0x28313bc9b04b924f11fc,0xcb685912b9155ca78525,0x5337190cc506092f7173,0x1ce507093771b3cd5068,0xf93ef1efcf387813b11d,0x28d11086d42720cd0287,0x9614a1247d2008dd45f2,0x286d3f89dd4dd266d300,0xad15592a4d4f0a5951f,0x32e8d710b655a12c6d5f],#[0x28c75623307d808be55e,0xb134dda30cf966d32ed9,0xc78e156fb372db48d856,0x78f3bfdda8ea9743397d,0x4405fd97d93e4dec0f45,0x619c90807c11f24201f0,0x1c2e2b1b220f0700752c,0x444306c6198908c0c10c,0x988c0c1210c222027030,0x287c4303062620913c60,0x190cc6c0c18889284430,0xd29261f0621446312113,0x21286614ac687c188491,0x4687c14988211a1f0526,0x919261f0621486574b52,0x1f062064687c188494a1,0x438746c18852194b251a,0x818643b1823030624608,0x700483870609c1c0881,0x4689c1c08818182e2027,0x1020184a2707002e207,0x702207185219c908c1c,0x10c9c1c08820614b2443,0xc1a23070124646190b52,0x220706120bc1c088491,0x88c1c019182867251b07,0x82d1b262307006471246,0x4a2070605c1c088211,0xc3c1c012881c8b0c4307,0xd2220270700443462246,0x34713c60988c1c0210,0xc1c0898827186a242307],#[0xb07022224a160d0a1f11,0x1c021111cd0844c68371,0x2b222707004461309c8c,0x845132111c8c1c0891d,0x706c1c04821141b07012,0xc02114160f1b23070080,0x8192307022464646c8c1,0x7022470648c1c0891a1,0x8c1c089182089182b23,0xc18270702206061a0fc6,0x206060b8809c1c00f121,0x89c1c00b881d1a270702,0x6282a230701245860612,0x50a181a16c952c1c0088,0x52c1c088212707022060,0xa1b2707022090618c916,0x2c988c1c0161c682c594,0x491c1a230701246860b5,0xb070220706120bc1c088,0x24688c1c01a18286b251,0x21182d1b262307006871,0xb07004a2080605c1c088,0x6c3c1c012881c885b0d1,0x17182a270701205c6224,0xc2707004870a89c1c048,0x706c8c1c089181b22182,0x18171a18482f23070224,0x923070224646c889c1c0,0x22470648c1c0891a181,0xc9c1c0482089182b2307,0xa1b230701247920b2286,0x20b2286c9c1c048204e2],#[0x191c4a182f2307012479,0xb070084603861248c1c0,0x3861248c1c01a1c17221,0x1c89291a262303063080,0x62387898846c0c14a8c,0x8c1c04990211a2623070,0x230701252a40613214a8,0x64060b4988c1c052901e,0x9c1c088511e230701292,0x171867070220847198a4,0x21190cc64988c1c03125,0xd245d186223070124ac8,0x648120ec6184988c1c02,0xc019208b0d184b062300,0x22a214463a2b10c9c188,0xa468988c1c08d2127070,0x1e251a2307012a347224,0x9224461a4a89c1c04891,0x91348c0c131262707012,0x851b07012224b190c218,0xc1c048211c85584e285a,0x6244d230700d0985c61a,0x922c846c1c0211c68348,0x8a1e27204707004c8478,0x226206071646c1c08948,0xa4988c1c027291a3f070,0x270702214881f16110d4,0x86c1c049884a1c582e19,0xc3c2d4926230700a4916,0x6371b1ac9c188c016285,0x247f0f06230059487528,0x8211a0dc64988c1c034],#[0x2e245d186306230124b,0x688120fc6184988c1c,0x88c01a288b0d184b0623,0x70120a371b162c46c9c1,0x8221e48e860886443270,0x2307012490618c9c1c04,0xc1c0492218f084887c47,0x868d61b27070120c0ac8,0x9c1c048221e48dc88605,0x8a1b230701246090618c,0x18c8c1c04922185c48]]
def g255H11 := limbs80 #[#[0x100130d00181501070d,0x71410080905030000,0x1102000b020a170524,0x14000e0a085624530000,0x3c162800000652033a0c,0xb2347000902130c0003,0x18040802000203000705,0x1d15090f685795020e00,0x2500012b006d38171b,0x1da0000924b3580000,0xa14d008000000000e3c0,0x541894c70a0000000eb8,0x8000d53c12822eab3c57,0xd341e038ce4a8900000f,0x29c91763293783380ab9,0x778d24001f1bb6e0003e,0xd81ecc1303d2a8716f41,0x25e2b6793ab23d89fa0d,0x11be40cb8080004d2000,0x251575740000007a254e,0x944dc00074d64ed4c8c0,0xd359a1566ced435b3a48,0x890001ef8381797b1134,0xb561ff0ec025e403460,0x20fbe0a47a0000002087,0x1357387e47c001018000,0xaa0d845d5530003c9000,0x9a00093f01a32adc5d77,0x6dbf0e7a020e8f02196,0x6b0535699b8580017150,0xf54e8f64c4000e400953,0x597be4e88222a2abcd2d],#[0x475e26fa6292fb63d43,0x568574e5c6af0174d60f,0xf9a0fa2ca81d656c7381,0x3dc6541a3bc986df5c,0x2ff15c0000d27562a4f0,0x53cf91a00078e7345a1d,0xa09cf4b0002410761f50,0x5c2e9480009a6023899,0xf459085db08fd00,0x13a9468460000007d3c0,0xa610a2baaa9c7a876925,0x79c82122448da4167aa8,0x3510663d05c1b058634e,0x457030bd8e601a45b742,0xa1a78e7b84fd4acd5a20,0x650a38001491415f7b13,0x595988ca3b58385d99da,0x94800021aacce0000003,0xb4ff873b36d298003c0d,0x964400075815bd532760,0xbb57ee3400021e1c00aa,0xa4e33e3c832e8a106f71,0x25800197c000c04e2949,0xd28a7fb386b240002853,0x396ca427450003a43,0x6de486db188970001e0f,0x4e7bc50aa4d4c2d4ad31,0xfe60768146a3430001ab,0xa0d8002a2c8ab0000a,0xc4000163a145200fe500,0xe2333ec5aeee1aa92,0xd3a4000eb723a9148000],#[0x411d9f0a84001564a84,0xc6c4564a6ca26db4dc00,0x58000f3ef198e54abad2,0x9700032400001ad509ba,0x50e000a19438800184c0,0x40ec58c00081ef116104,0x8000727f7680005cc000,0xdc78d1140004c8ea023a,0x177082f56191f80fed,0xec000000359e31d40800,0x8a4000000894915e9dc4,0x85a68ce52c133413f589,0x78d18e48280002a5c000,0x42dd2cbd47a8c0009a8,0x780c0131242757c3f800,0xd5b95cf463c00000b4,0x313c000000000017c0]]
def g255D12 := limbs80 #[#[0xffac1ff503fe887ed20,0x71ffac3ff4c7ffb87fd7,0xd73ffac7ff50fffb8ffd,0xff74ffae9ff593ffb9ff,0x4b8c014801ffddbfebb7,0x19bf8e632ab2a5c7f18e,0x2f3fb7e7f87da350cd5,0x8c204c0823078d243c11,0x101894610260c01c38a,0x494693060081c5491106,0x830068f1a1c1802090c6,0x715204c1804461518488,0x60091430a431a4418024,0x1c94612220c01e3c6910,0x9830040e28b069306008,0x488d0e0c010486344a34,0x601218b8b241a441802,0x1a34883005091a34813,0xc80d0601218949901a0c,0x21]]
def g255H12 := limbs80 #[#[0x900018041784e200820,0x1d261198c68811a8865,0x8003069f67cb86a93e71,0x1fe00000092508ce896,0x13da97f4c000000000,0x6ff1eb8b933e7e708000,0x40000000036d5a12a620,0x94b84f7864,0x25d00043e000000000,0xb5f30a75bcaeca3dd0b8,0xe56f8cc14880958ec12d,0x8b04118983c1284856cd,0x154fb27ea390005a42ae,0xa00000000921ab17d800,0x659000003832b5d8,0x5c8b8c002d84050000,0x182001e88009c2dd0,0xc9cbe00000000053d9c,0xac001ca8003d60000000,0x3e40015e800000b,0xc000a155e0000023f000,0x900cf0503c000009115c,0x7974500fd1ca60019799,0x932f5000485134005,0x1cc799eda2c60010059b,0x7a3b9470000030e00000,0x72dc,0xf4a0012a247000001edc,0xd3bc610b8540000002f,0xe4001218000000000000,0x42400019ddd8ec002d70,0x1]]
def g255D13 (j : Nat) := if j=0 then 0x189201005ff else 0
def g255H13 := limbs80 #[#[0x9c00000000000001,0x6900000000045800000,0x2f000000123411c80,0xc80000108f500,0x18c8057003820000,0xf1000b4014ce25140000,0x1]]
def g255L : Nat → Packing
  | 7 => (6,6,6,0,0,7,0,g255D7)
  | 8 => (80,5,6,0,0,12,0,g255D8)
  | 9 => (257,4,6,0,0,15,0,g255D9)
  | 10 => (358,3,6,0,0,15,0,g255D10)
  | 11 => (128,2,6,0,0,13,0,g255D11)
  | 12 => (19,1,6,0,0,10,0,g255D12)
  | 13 => (1,0,6,0,0,0,0,g255D13)
  | _ => emptyPacking
def g255I : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 1 23 0 7 3 0 g255H8
  | 9 => lookupWord 20 307 3 11 7 0 g255H9
  | 10 => lookupWord 64 419 6 13 9 0 g255H10
  | 11 => lookupWord 89 443 8 13 9 0 g255H11
  | 12 => lookupWord 32 211 5 11 7 0 g255H12
  | 13 => lookupWord 4 53 1 9 5 0 g255H13
  | _ => fun _ => none
def g255 : Forest := ⟨255,13,fun i => g255Y[i]?.getD (0,0),g255C,g255A,g255L,g255I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P7_0 : block g255 7 0 6=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B7 : block g255 7 0 6=true := g255P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_0 : block g255 8 0 31=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_31 : block g255 8 31 49=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B8 : block g255 8 0 80=true := (@block_merge g255 8 0 31 49 g255P8_0 g255P8_31)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_0 : block g255 9 0 23=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_23 : block g255 9 23 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_119 : block g255 9 119 78=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_197 : block g255 9 197 60=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B9 : block g255 9 0 257=true := (@block_merge g255 9 0 119 138 (@block_merge g255 9 0 23 96 g255P9_0 g255P9_23) (@block_merge g255 9 119 78 60 g255P9_119 g255P9_197))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_0 : block g255 10 0 19=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_19 : block g255 10 19 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_115 : block g255 10 115 75=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_190 : block g255 10 190 96=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_286 : block g255 10 286 59=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_345 : block g255 10 345 13=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B10 : block g255 10 0 358=true := (@block_merge g255 10 0 190 168 (@block_merge g255 10 0 19 171 g255P10_0 (@block_merge g255 10 19 96 75 g255P10_19 g255P10_115)) (@block_merge g255 10 190 96 72 g255P10_190 (@block_merge g255 10 286 59 13 g255P10_286 g255P10_345)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_0 : block g255 11 0 3=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_3 : block g255 11 3 79=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_82 : block g255 11 82 46=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B11 : block g255 11 0 128=true := (@block_merge g255 11 0 3 125 g255P11_0 (@block_merge g255 11 3 79 46 g255P11_3 g255P11_82))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P12_0 : block g255 12 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P12_1 : block g255 12 1 18=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B12 : block g255 12 0 19=true := (@block_merge g255 12 0 1 18 g255P12_0 g255P12_1)
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
  · exact (rfl : block g255 6 0 0 = true)
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

end PEqualNP.Outside.L_meta_49553

open PEqualNP.Outside.L_meta_49553 in
theorem PEqualNP.Outside.L_meta_49553 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o fit _ correct
  exact replaceShort g255R gates o fit correct

import PEqualNP.Defs

-- The two-mode live-state and cofactor checker follows L_meta_1674 and L_meta_670.
-- The graph, restrictions and all search certificates below are for L_meta_49539.

-- Shared forest and cofactor certificates from L_meta_1674 and PR 11111 for L_meta_1677.
-- The original credit line is retained below. The two root certificates here cover the unpinned graph.

-- The checker and the bound certificates are adapted from PEqualNP/Outside/L_meta_1667.lean (Apache-2.0).
-- Two modes: u=false are monotone runs (AND, OR); u=true are runs up to complement, where negation is free.
namespace PEqualNP.Outside.L_meta_49539
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
def graph : Sig := (BitVec.ofNat 512 (word80 [0xffffffff,0xffffffffffffffffffff,0xffeefffffffefffffffc,0xfffefefeffaaaa00ffff,0xffffffffffffffffffff,0xffffffeefffffffeffff,0xfffcfffefefeffaaaa00]))
def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 3) || (x 0 && x 4) || (x 3 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 2 && x 5) || (x 1 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 4 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 5 && x 7) || (x 6 && x 7)
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
  (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 3 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 2 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)
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
  (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 3 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 2 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)
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



def target (x : Fin 8 → Bool) : Bool := decide (∃ i < ([0, 3, 0, 4, 3, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 3, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 3, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
def smallCircuit : Circuit := ⟨[⟨.or,[0,6]⟩,⟨.or,[7,8]⟩,⟨.or,[0,1]⟩,⟨.or,[5,6]⟩,⟨.or,[1,2]⟩,⟨.or,[7,12]⟩,⟨.or,[5,7]⟩,⟨.or,[3,9]⟩,⟨.and,[13,11]⟩,⟨.and,[14,10]⟩,⟨.and,[15,4]⟩,⟨.and,[9,3]⟩,⟨.or,[16,17]⟩,⟨.or,[20,18]⟩,⟨.or,[21,19]⟩], 22⟩

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

def lowRow (i : Fin 8) : Row := Fin.ofNat 512 (1 <<< ([3, 5, 5, 0, 0, 0, 1, 0] : List Nat).getD i.val 0)
def highRow (i : Fin 8) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< ([3, 5, 5, 0, 0, 0, 1, 0] : List Nat).getD i.val 0))

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
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low9 : Lower true (varsX 9) (graphGoal 9) 1 := by
  have q := @lower_count true (vars 9) (graphGoal 9) (proper_of _ (by decide +kernel)) (graphPairs 9 3) (by decide +kernel)
  exact q
def K9 := extendKnown [] 1 [(33,[83,67])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V9 : Known true K9 := extend_ok (m:=9) baseKnown low9 (by decide +kernel)
def g25Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3ff63ff63ff63ff63f,0xf63ff63ff63ff63ff63f])),(BitVec.ofNat 152 (word80 [0x492049204920492049,0x20492049204920492049]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xc7fbc7fbc7fbc7fbc7,0xfbc7fbc7fbc7fbc7fbc7])),(BitVec.ofNat 152 (word80 [0x924092409240924092,0x40924092409240924092]))),((BitVec.ofNat 152 (word80 [0xf8fdf8fdf8fdf8fdf8,0xfdf8fdf8fdf8fdf8fdf8])),(BitVec.ofNat 152 (word80 [0x248124812481248124,0x81248124812481248124]))),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g25C : List ColumnInfo := []
def g25A : List (List Nat) := [[],[67],[48],[48,64],[64,48],[64]]
def g25D3 (j : Nat) := if j=0 then 0x7 else 0
def g25L : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,g25D3)
  | _ => emptyPacking
def g25I (_ _ : Nat) : Option (Nat × Nat) := none
def g25 : Forest := ⟨25,3,fun i => g25Y[i]?.getD (0,0),g25C,g25A,g25L,g25I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g25P3_0 : block g25 3 0 1=true := by
  apply cellsBlock (ar:=3) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g25B3 : block g25 3 0 1=true := g25P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g25T : checkedTables g25 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g25 0 0 0 = true)
  · exact (rfl : block g25 1 0 0 = true)
  · exact (rfl : block g25 2 0 0 = true)
  · exact g25B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g25G : graphValid g25 (boundsBefore K9) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low25 : Lower true (varsX 25) (graphGoal 25) 4 := lower_forest (g:=g25) (i:=0) (hints:=3) (before_sound K9 V9) g25G g25T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K25 := extendKnown K9 4 [(25,[]),(88,[48,16,33,66,98,82]),(137,[116,84,101]),(145,[67,115,83,101]),(152,[48,16,33,66,114,82,101]),(161,[83,116,100]),(162,[16,83,116,100]),(194,[16,99,116,83,84]),(200,[48,16,33,98,116,82,84])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V25 : Known true K25 := extend_ok (m:=25) V9 low25 (by decide +kernel)
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
theorem g43G : graphValid g43 (boundsBefore K25) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low43 : Lower true (varsX 43) (graphGoal 43) 4 := lower_forest (g:=g43) (i:=0) (hints:=83) (before_sound K25 V25) g43G g43T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K43 := extendKnown K25 4 [(43,[]),(51,[67]),(75,[96,16,49,83]),(83,[96,16,49,67,84]),(99,[16,99,67]),(105,[48,81,33,96,66,64]),(106,[16,48,32,82,66,100]),(113,[64,81,33,99,32]),(114,[16,64,32,83,99])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V43 : Known true K43 := extend_ok (m:=43) V25 low43 (by decide +kernel)
def g57Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfd5b8fff83fffff3fa,0xb71fff07ffffe7f56e3f])),(BitVec.ofNat 152 (word80 [0x92410820802000,0x1248210410040000249]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x3bac71fffc0fc7fc77,0x58e3fff81f8ff8eeb1c7])),(BitVec.ofNat 152 (word80 [0x818d24921241124103,0x1a492424822482063492]))),((BitVec.ofNat 152 (word80 [0xc6b47e3ffff007ff8d,0x68fc7fffe00fff1ad1f8])),(BitVec.ofNat 152 (word80 [0x16324924208a24802c,0x6492484114490058c924]))),((BitVec.ofNat 152 (word80 [0x64f803ffffff8000c,0x9f007ffffff000193e00])),(BitVec.ofNat 152 (word80 [0x264f6db8430c070a4c,0x9edb7086180e14993db6]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g57C : List ColumnInfo := [(32,0,25,0,4)]
def g57A : List (List Nat) := [[],[67]]
def g57D4 (j : Nat) := if j=0 then 0x1f else 0
def g57L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g57D4)
  | _ => emptyPacking
def g57I (_ _ : Nat) : Option (Nat × Nat) := none
def g57 : Forest := ⟨57,4,fun i => g57Y[i]?.getD (0,0),g57C,g57A,g57L,g57I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g57P4_0 : block g57 4 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g57B4 : block g57 4 0 1=true := g57P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g57T : checkedTables g57 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g57 0 0 0 = true)
  · exact (rfl : block g57 1 0 0 = true)
  · exact (rfl : block g57 2 0 0 = true)
  · exact (rfl : block g57 3 0 0 = true)
  · exact g57B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g57G : graphValid g57 (boundsBefore K43) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low57 : Lower true (varsX 57) (graphGoal 57) 5 := lower_forest (g:=g57) (i:=0) (hints:=3) (before_sound K43 V43) g57G g57T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K57 := extendKnown K43 5 [(57,[]),(90,[96,16,81]),(139,[112,33,65,48,49,81,101]),(154,[112,16,81,101]),(170,[112,16,49,84,67,100]),(178,[112,16,49,84,99]),(184,[112,16,33,98]),(195,[112,33,49,100,80]),(225,[112,48,84,100,67]),(232,[112,16,33,100,66])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V57 : Known true K57 := extend_ok (m:=57) V43 low57 (by decide +kernel)
def g89Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xf1fe003ffc0f9f3f1f,0xe003ffc0f9f3f1fe003f])),(BitVec.ofNat 152 (word80 [0x241e49248a2142a241,0xe49248a2142a241e4924]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfe750fc7fff01fffe7,0x50fc7fff01fffe750fc7])),(BitVec.ofNat 152 (word80 [0x400012491042040400,0x1249104204040001249]))),((BitVec.ofNat 152 (word80 [0xff8af1f8ffffe03ff8,0xaf1f8ffffe03ff8af1f8])),(BitVec.ofNat 152 (word80 [0x800024922084080800,0x2492208408080002492]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x19fe00ffffffc001,0x9fe00ffffffc0019fe00])),(BitVec.ofNat 152 (word80 [0x959c924c308103095,0x9c924c3081030959c924]))),(0x0,0x0),(0x0,0x0)]
def g89C : List ColumnInfo := [(1,0,88,0,4)]
def g89A : List (List Nat) := [[],[67],[96],[96,67]]
def g89D4 (j : Nat) := if j=0 then 0x1f else 0
def g89L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g89D4)
  | _ => emptyPacking
def g89I (_ _ : Nat) : Option (Nat × Nat) := none
def g89 : Forest := ⟨89,4,fun i => g89Y[i]?.getD (0,0),g89C,g89A,g89L,g89I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g89P4_0 : block g89 4 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g89B4 : block g89 4 0 1=true := g89P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g89T : checkedTables g89 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g89 0 0 0 = true)
  · exact (rfl : block g89 1 0 0 = true)
  · exact (rfl : block g89 2 0 0 = true)
  · exact (rfl : block g89 3 0 0 = true)
  · exact g89B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g89G : graphValid g89 (boundsBefore K57) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low89 : Lower true (varsX 89) (graphGoal 89) 5 := lower_forest (g:=g89) (i:=0) (hints:=50331651) (before_sound K57 V57) g89G g89T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K89 := extendKnown K57 5 [(89,[]),(163,[33,49,81,116,65,97]),(169,[48,116,84,101]),(201,[116,84]),(202,[16,99,116,84]),(209,[67,115,83]),(226,[80,16,49,116])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V89 : Known true K89 := extend_ok (m:=89) V57 low89 (by decide +kernel)
def g153Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xdf7ec03c3ffe0fbefd,0x80787ffc1f7dfb00f0ff])),(BitVec.ofNat 152 (word80 [0x820404444444210408,0x8888888420810111111]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1fbf43c3c3fff03f7e,0x878787ffe07efd0f0f0f])),(BitVec.ofNat 152 (word80 [0x40808888888420810,0x11111110841020222222]))),((BitVec.ofNat 152 (word80 [0xe03fbc03fc3fffc07f,0x7807f87fff80fef00ff0])),(BitVec.ofNat 152 (word80 [0x81011111110841020,0x22222221082040444444]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffc03ffc003fffff80,0x7ff8007fffff00fff000])),(BitVec.ofNat 152 (word80 [0x102022222221082040,0x44444442104080888888]))),(0x0,0x0)]
def g153C : List ColumnInfo := [(1,0,152,0,4),(8,0,145,0,4),(16,0,137,0,4),(128,0,25,0,4)]
def g153A : List (List Nat) := [[],[116],[67],[67,115],[115,67],[115],[48],[48,116],[48,64],[48,64,112],[48,112,64],[48,112],[64,48],[64,48,115],[64],[64,112],[64,115],[64,115,48],[112,48,67],[112,48],[112,64],[112],[112,67,48],[112,67]]
def g153D3 := limbs80 #[#[0x23ea6a1221e12148110,0x8028]]
def g153D4 := limbs80 #[#[0x2fd0910bd42443e48110,0x609085870]]
def g153H4 (j : Nat) := if j=0 then 0x13 else 0
def g153D5 (j : Nat) := if j=0 then 0xd1027d10 else 0
def g153H5 := limbs80 #[#[0x2b9010071801448,0x2c00052fe1c40]]
def g153D6 (j : Nat) := if j=0 then 0x3904f else 0
def g153H6 := limbs80 #[#[0x2082000010a000000050,0x12000000058801]]
def g153L : Nat → Packing
  | 3 => (2,3,2,0,0,5,0,g153D3)
  | 4 => (3,2,2,0,0,5,0,g153D4)
  | 5 => (1,1,2,0,0,0,0,g153D5)
  | 6 => (1,0,2,0,0,0,0,g153D6)
  | _ => emptyPacking
def g153I : Nat → Nat → Option (Nat × Nat)
  | 4 => lookupWord 1 2 0 5 1 0 g153H4
  | 5 => lookupWord 2 23 2 9 2 3 g153H5
  | 6 => lookupWord 1 23 0 9 0 5 g153H6
  | _ => fun _ => none
def g153 : Forest := ⟨153,6,fun i => g153Y[i]?.getD (0,0),g153C,g153A,g153L,g153I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g153P3_0 : block g153 3 0 2=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g153B3 : block g153 3 0 2=true := g153P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g153P4_0 : block g153 4 0 3=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g153B4 : block g153 4 0 3=true := g153P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g153P5_0 : block g153 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g153B5 : block g153 5 0 1=true := g153P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g153P6_0 : block g153 6 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g153B6 : block g153 6 0 1=true := g153P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g153T : checkedTables g153 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g153 0 0 0 = true)
  · exact (rfl : block g153 1 0 0 = true)
  · exact (rfl : block g153 2 0 0 = true)
  · exact g153B3
  · exact g153B4
  · exact g153B5
  · exact g153B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g153G : graphValid g153 (boundsBefore K89) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low153 : Lower true (varsX 153) (graphGoal 153) 7 := lower_forest (g:=g153) (i:=0) (hints:=3) (before_sound K89 V89) g153G g153T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K153 := extendKnown K89 7 [(153,[]),(216,[48,16,33,66,98,82])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V153 : Known true K153 := extend_ok (m:=153) V89 low153 (by decide +kernel)
def g59Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xf007ffff87fff007ff,0xfffffffa0dce40f83ff])),(BitVec.ofNat 152 (word80 [0xa05014011000a0500a,0x20100082201824108421]))),((BitVec.ofNat 152 (word80 [0xfff801fff87ffff800,0xff87fc03373b3f00000])),(BitVec.ofNat 152 (word80 [0xc261582a010ac060ac,0x40a109082171b2739ce7]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffe00007fffffff,0xf0007ffccfd11c007c1f])),(BitVec.ofNat 152 (word80 [0x80608c2223048230,0x4c22200c2c118a5294a]))),((BitVec.ofNat 152 (word80 [0x7fffffff,0xffff80004d2fe8007fe0])),(BitVec.ofNat 152 (word80 [0xb058130444c0904c0,0x9004c100d26c14a5294]))),((BitVec.ofNat 152 (word80 [0xffffffffff80000000,0x33aa61bff8000])),(BitVec.ofNat 152 (word80 [0xc0601c000700e0700,0x8e0470211a86098c6318]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g59C : List ColumnInfo := [(0,2,25,32,5),(2,0,57,0,5),(8,0,51,0,4),(16,0,43,0,4),(32,2,25,0,4)]
def g59A : List (List Nat) := [[],[67]]
def g59D4 (j : Nat) := if j=0 then 0x57d4d20 else 0
def g59D5 := limbs80 #[#[0x460e140fd32fe20fd20,0x4088]]
def g59H5 (j : Nat) := if j=0 then 0xe else 0
def g59D6 (j : Nat) := if j=0 then 0x16a09f else 0
def g59H6 := limbs80 #[#[0x200500da000000160200,0xc]]
def g59L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g59D4)
  | 5 => (3,1,3,0,0,5,0,g59D5)
  | 6 => (1,0,3,0,0,0,0,g59D6)
  | _ => emptyPacking
def g59I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 4 0 0 g59H5
  | 6 => lookupWord 1 13 0 7 2 1 g59H6
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
theorem g59G : graphValid g59 (boundsBefore K153) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low59 : Lower true (varsX 59) (graphGoal 59) 7 := lower_forest (g:=g59) (i:=0) (hints:=83) (before_sound K153 V153) g59G g59T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K59 := extendKnown K153 7 [(59,[]),(122,[96,81,32])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V59 : Known true K59 := extend_ok (m:=59) V153 low59 (by decide +kernel)
def g91Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffc01ff0ff0ffc03f,0xf0ffffff24d65b0000ff])),(BitVec.ofNat 152 (word80 [0x282a140a202282a2a0,0xa2820820048653999999]))),((BitVec.ofNat 152 (word80 [0xffffe000fffffffc0,0xff0ff0c6353900f000])),(BitVec.ofNat 152 (word80 [0x42b098ac45402b030a,0xc4142242823539777777]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffff000ffffff,0xff000fff39b5260f0f0f])),(BitVec.ofNat 152 (word80 [0x80c0203001840c0403,0x184080383100222222]))),((BitVec.ofNat 152 (word80 [0xf00000000000ffffff,0xfffff000134bf8f00ff0])),(BitVec.ofNat 152 (word80 [0x300c0c0860830080c,0x200304034828444444]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffff000000,0xcea8c5fff000])),(BitVec.ofNat 152 (word80 [0xc0301000800c03030,0x8c08c084480c4888888]))),(0x0,0x0),(0x0,0x0)]
def g91C : List ColumnInfo := [(0,2,25,64,5),(1,0,90,0,5),(2,0,89,0,5),(8,0,83,0,4),(16,0,75,0,4),(64,2,25,0,4)]
def g91A : List (List Nat) := [[],[67]]
def g91D4 (j : Nat) := if j=0 then 0x5ed4132 else 0
def g91D5 (j : Nat) := if j=0 then 0xc8404fd32 else 0
def g91H5 (j : Nat) := if j=0 then 0x90 else 0
def g91D6 (j : Nat) := if j=0 then 0x23468bf else 0
def g91H6 (j : Nat) := if j=0 then 0xa else 0
def g91L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g91D4)
  | 5 => (1,1,3,0,0,0,0,g91D5)
  | 6 => (1,0,3,0,0,0,0,g91D6)
  | _ => emptyPacking
def g91I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 4 0 0 g91H5
  | 6 => lookupWord 1 2 0 4 0 0 g91H6
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
theorem g91P5_0 : block g91 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g91B5 : block g91 5 0 1=true := g91P5_0
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
theorem g91G : graphValid g91 (boundsBefore K59) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low91 : Lower true (varsX 91) (graphGoal 91) 7 := lower_forest (g:=g91) (i:=0) (hints:=16777315) (before_sound K59 V59) g91G g91T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K91 := extendKnown K59 7 [(91,[]),(121,[96,81,33])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V91 : Known true K91 := extend_ok (m:=91) V59 low91 (by decide +kernel)
def g107Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xf003ff0ff87ff007ff,0xff87fffcd47c560003ff])),(BitVec.ofNat 152 (word80 [0xa4280a201120a45214,0x81102080501c1694a529]))),((BitVec.ofNat 152 (word80 [0xfffc000ffffffff801,0xfff87fc35353a20ffc00])),(BitVec.ofNat 152 (word80 [0xc0302c40a002c06058,0xa01010a425122318c63]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffff0007ffffffe,0x7ffcafd11df0001f])),(BitVec.ofNat 152 (word80 [0x140b002c20b008060,0x2c220a00a741086318c6]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x7fffffff,0xffff80004d2fe8007fe0])),(BitVec.ofNat 152 (word80 [0x982c08b044c090481,0x30004c100d22c94a5294]))),((BitVec.ofNat 152 (word80 [0xffffffffff80000000,0x33aa61bff8000])),(BitVec.ofNat 152 (word80 [0xe03000c00700e0701,0xc044702118a6118c6318]))),(0x0,0x0),(0x0,0x0)]
def g107C : List ColumnInfo := [(1,0,106,0,4),(2,0,105,0,4),(8,0,99,0,4),(32,0,75,0,4),(64,0,43,0,4)]
def g107A : List (List Nat) := [[],[97,83],[16,99],[16,48,80,96],[48,101],[48,81,96,16],[80,49],[80,97,48,49],[96,16,49,83],[96,81]]
def g107D4 (j : Nat) := if j=0 then 0x57d4d10 else 0
def g107D5 (j : Nat) := if j=0 then 0xc1a0fd20fd10 else 0
def g107H5 (j : Nat) := if j=0 then 0xc0 else 0
def g107D6 (j : Nat) := if j=0 then 0x23440bf else 0
def g107H6 := limbs80 #[#[0x42000000c57a00,0x4eeb000000,0xa1000000f700061320]]
def g107L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g107D4)
  | 5 => (2,1,3,0,0,4,0,g107D5)
  | 6 => (1,0,3,0,0,0,0,g107D6)
  | _ => emptyPacking
def g107I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 4 0 0 g107H5
  | 6 => lookupWord 2 29 0 8 1 3 g107H6
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
theorem g107P5_0 : block g107 5 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g107B5 : block g107 5 0 2=true := g107P5_0
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
theorem low107 : Lower true (varsX 107) (graphGoal 107) 7 := lower_forest (g:=g107) (i:=0) (hints:=16777299) (before_sound K91 V91) g107G g107T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K107 := extendKnown K91 7 [(107,[]),(115,[67])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V107 : Known true K107 := extend_ok (m:=107) V91 low107 (by decide +kernel)
def g155Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfe1ff00ff87f87ffc0,0x7fc7ffffd3b94000f0ff])),(BitVec.ofNat 152 (word80 [0x1440a0a05101100285,0x2902008418941111111]))),((BitVec.ofNat 152 (word80 [0x1ffff0007ff87fff,0x8007f1fc231ee00f0000])),(BitVec.ofNat 152 (word80 [0x588ac4c5622a012b06,0x2b214491231ee7777777]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1fffffff80007fff,0xfff801ff9c1f30f00f0f])),(BitVec.ofNat 152 (word80 [0x61030101800c220c08,0xc0188201c1602222222]))),((BitVec.ofNat 152 (word80 [0xffe000000000007fff,0xfffffe000be4bf000ff0])),(BitVec.ofNat 152 (word80 [0x800c06060430443010,0x300200c20260b4444444]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffff8000,0x6442cffff000])),(BitVec.ofNat 152 (word80 [0x1008080040004020,0x40040100000008888888]))),(0x0,0x0)]
def g155C : List ColumnInfo := [(2,0,153,0,7)]
def g155A : List (List Nat) := [[],[67],[48],[48,64],[64,48],[64]]
def g155D7 (j : Nat) := if j=0 then 0x3f else 0
def g155L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g155D7)
  | _ => emptyPacking
def g155I (_ _ : Nat) : Option (Nat × Nat) := none
def g155 : Forest := ⟨155,7,fun i => g155Y[i]?.getD (0,0),g155C,g155A,g155L,g155I⟩
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
  · exact (rfl : block g155 4 0 0 = true)
  · exact (rfl : block g155 5 0 0 = true)
  · exact (rfl : block g155 6 0 0 = true)
  · exact g155B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g155G : graphValid g155 (boundsBefore K107) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low155 : Lower true (varsX 155) (graphGoal 155) 8 := lower_forest (g:=g155) (i:=0) (hints:=115) (before_sound K107 V107) g155G g155T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K155 := extendKnown K107 8 [(155,[]),(248,[48,81,32,66,98])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V155 : Known true K155 := extend_ok (m:=155) V107 low155 (by decide +kernel)
def g171Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfe1ff00ff87f87ffc0,0x7fff8fffd8b95000f0ff])),(BitVec.ofNat 152 (word80 [0x1440a0a05101100285,0x5012008488941111111]))),((BitVec.ofNat 152 (word80 [0x1ffff0007ff87fff,0x807ff1fc2b1e600f0f00])),(BitVec.ofNat 152 (word80 [0x5882c0c1620a010b06,0x160a0411291e43333333]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1fffffff80007fff,0xff8001ff941fb0f0000f])),(BitVec.ofNat 152 (word80 [0x610b0505802c222c08,0x182c48a01416b6666666]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffe000000000007fff,0xfffffe000be4bf000ff0])),(BitVec.ofNat 152 (word80 [0x800c06060430443010,0x203000c20260b4444444]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffff8000,0x6442cffff000])),(BitVec.ofNat 152 (word80 [0x1008080040004020,0x40400100000008888888]))),(0x0,0x0)]
def g171C : List ColumnInfo := [(1,0,170,0,5),(2,0,169,0,5),(8,0,163,0,5),(32,0,139,0,5)]
def g171A : List (List Nat) := [[],[80,49]]
def g171D6 (j : Nat) := if j=0 then 0x4e09f else 0
def g171L : Nat → Packing
  | 6 => (1,0,2,0,0,0,0,g171D6)
  | _ => emptyPacking
def g171I (_ _ : Nat) : Option (Nat × Nat) := none
def g171 : Forest := ⟨171,6,fun i => g171Y[i]?.getD (0,0),g171C,g171A,g171L,g171I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g171P6_0 : block g171 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g171B6 : block g171 6 0 1=true := g171P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g171T : checkedTables g171 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g171 0 0 0 = true)
  · exact (rfl : block g171 1 0 0 = true)
  · exact (rfl : block g171 2 0 0 = true)
  · exact (rfl : block g171 3 0 0 = true)
  · exact (rfl : block g171 4 0 0 = true)
  · exact (rfl : block g171 5 0 0 = true)
  · exact g171B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g171G : graphValid g171 (boundsBefore K155) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low171 : Lower true (varsX 171) (graphGoal 171) 7 := lower_forest (g:=g171) (i:=0) (hints:=83) (before_sound K155 V155) g171G g171T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K171 := extendKnown K155 7 [(171,[]),(179,[67]),(203,[96,16,49,83]),(211,[96,16,49,67,84]),(227,[16,99,67]),(233,[48,81,33,96,66,64]),(234,[16,48,32,82,66,100])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V171 : Known true K171 := extend_ok (m:=171) V155 low171 (by decide +kernel)
def g185Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3fc7f807f8ff1ffe0,0x7fffffcfd609000ff0ff])),(BitVec.ofNat 152 (word80 [0x80801010100200041,0x2040080000011111111]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfc007fff800ffe1fff,0x80fe3ff1cdec00f00f0f])),(BitVec.ofNat 152 (word80 [0x109112121222404482,0x240889040cac22222222]))),((BitVec.ofNat 152 (word80 [0x7ffffff0001fff,0xff003ffe31e30f000ff0])),(BitVec.ofNat 152 (word80 [0xa12224242404848904,0x8511200b14344444444]))),((BitVec.ofNat 152 (word80 [0xffff80000000001fff,0xffffc0003b98f000f000])),(BitVec.ofNat 152 (word80 [0xc1c038383847090e08,0x30601c293b9866666666]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffffe000,0x2816ffff0000])),(BitVec.ofNat 152 (word80 [0x20040404008001010,0x40802000000088888888]))),(0x0,0x0)]
def g185C : List ColumnInfo := [(32,0,153,0,7)]
def g185A : List (List Nat) := [[],[67],[112],[112,67]]
def g185D7 (j : Nat) := if j=0 then 0x3f else 0
def g185L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g185D7)
  | _ => emptyPacking
def g185I (_ _ : Nat) : Option (Nat × Nat) := none
def g185 : Forest := ⟨185,7,fun i => g185Y[i]?.getD (0,0),g185C,g185A,g185L,g185I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g185P7_0 : block g185 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g185B7 : block g185 7 0 1=true := g185P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g185T : checkedTables g185 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g185 0 0 0 = true)
  · exact (rfl : block g185 1 0 0 = true)
  · exact (rfl : block g185 2 0 0 = true)
  · exact (rfl : block g185 3 0 0 = true)
  · exact (rfl : block g185 4 0 0 = true)
  · exact (rfl : block g185 5 0 0 = true)
  · exact (rfl : block g185 6 0 0 = true)
  · exact g185B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g185G : graphValid g185 (boundsBefore K171) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low185 : Lower true (varsX 185) (graphGoal 185) 8 := lower_forest (g:=g185) (i:=0) (hints:=3) (before_sound K171 V171) g185G g185T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K185 := extendKnown K171 8 [(185,[]),(218,[96,16,81])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V185 : Known true K185 := extend_ok (m:=185) V171 low185 (by decide +kernel)
def g186Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffc00ff87fc3fff00,0xffffffe257e300007fe0])),(BitVec.ofNat 152 (word80 [0x20a82a051048802a2a,0xa12004a546306318c63]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffff0007ffc3ffff,0xff1ffd9276c00f801f])),(BitVec.ofNat 152 (word80 [0x42308c262110088c0c,0x4c0444811226ca5294a5]))),((BitVec.ofNat 152 (word80 [0xffffffff80003ffff,0xff001ffce8f541f0001f])),(BitVec.ofNat 152 (word80 [0x84c130480261113030,0x10588900e8d114a5294a]))),((BitVec.ofNat 152 (word80 [0xf0000000000003ffff,0xffffe0005f98fe0003e0])),(BitVec.ofNat 152 (word80 [0x701c070438221c040,0x60600e100b98d8c6318c]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffffffffc0000,0x3280bbffffc00])),(BitVec.ofNat 152 (word80 [0x80200800400020080,0x80801000000021084210]))),(0x0,0x0)]
def g186C : List ColumnInfo := [(2,0,184,0,5),(8,0,178,0,5),(16,0,170,0,5),(32,0,154,0,5),(24,0,162,0,4),(34,0,152,0,4)]
def g186A : List (List Nat) := [[],[67],[49,84],[49,81,65],[65,49,83],[65,83],[81],[81,67]]
def g186D4 := limbs80 #[#[0x9bd89544426d6215110,0x31826f625474]]
def g186D5 := limbs80 #[#[0x7c54443f2808857d4d40,0xfea8885f95110beaa221,0x7d4d40bfa8a81fb40502,0xcc8d018160c02faa3a07,0x882188201161080d176b,0x8118204c10001]]
def g186H5 := limbs80 #[#[0xc0000000f10000286200,0xc900]]
def g186D6 := limbs80 #[#[0x540a0380ff40fd40fd10,0x2150c8543]]
def g186H6 := limbs80 #[#[0x1d21c581000000009055,0x114d97002d4705c77091,0xc19490000026400b0c2,0x10]]
def g186D7 (j : Nat) := if j=0 then 0x1605f else 0
def g186H7 := limbs80 #[#[0x58a5001c4004,0x20000000ba0078000000,0x40044801240000764000,0x2c200002b25]]
def g186L : Nat → Packing
  | 4 => (3,3,3,0,0,4,0,g186D4)
  | 5 => (10,2,3,0,0,7,0,g186D5)
  | 6 => (3,1,3,0,0,6,0,g186D6)
  | 7 => (1,0,3,0,0,0,0,g186D7)
  | _ => emptyPacking
def g186I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 13 0 8 2 2 g186H5
  | 6 => lookupWord 4 23 4 10 4 2 g186H6
  | 7 => lookupWord 3 31 1 9 2 3 g186H7
  | _ => fun _ => none
def g186 : Forest := ⟨186,7,fun i => g186Y[i]?.getD (0,0),g186C,g186A,g186L,g186I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g186P4_0 : block g186 4 0 3=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g186B4 : block g186 4 0 3=true := g186P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g186P5_0 : block g186 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g186P5_1 : block g186 5 1 9=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g186B5 : block g186 5 0 10=true := (@block_merge g186 5 0 1 9 g186P5_0 g186P5_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g186P6_0 : block g186 6 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g186B6 : block g186 6 0 3=true := g186P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g186P7_0 : block g186 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g186B7 : block g186 7 0 1=true := g186P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g186T : checkedTables g186 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g186 0 0 0 = true)
  · exact (rfl : block g186 1 0 0 = true)
  · exact (rfl : block g186 2 0 0 = true)
  · exact (rfl : block g186 3 0 0 = true)
  · exact g186B4
  · exact g186B5
  · exact g186B6
  · exact g186B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g186G : graphValid g186 (boundsBefore K185) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low186 : Lower true (varsX 186) (graphGoal 186) 8 := lower_forest (g:=g186) (i:=0) (hints:=269697104) (before_sound K185 V185) g186G g186T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K186 := extendKnown K185 8 [(186,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V186 : Known true K186 := extend_ok (m:=186) V185 low186 (by decide +kernel)
def g217Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x7f01f9fc07f1fc7fc,0x7e7e7f1fce000f000ff])),(BitVec.ofNat 152 (word80 [0x122441489122489089,0x105052241ce444444444]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x7ffe01fff801ff9ff,0xf807fffe66800f00ff0f])),(BitVec.ofNat 152 (word80 [0x204082010204010010,0x20808040000111111111]))),((BitVec.ofNat 152 (word80 [0xf800001fffffe001ff,0xfff807ff8160f00f0ff0])),(BitVec.ofNat 152 (word80 [0x408104020408020020,0x41010080000222222222]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffe000000001ff,0xfffff8000bbf000ff000])),(BitVec.ofNat 152 (word80 [0x8306080c18308c24c1,0x820203094bb444444444]))),((BitVec.ofNat 152 (word80 [0xfffffffffffffffe00,0x181ffff00000])),(BitVec.ofNat 152 (word80 [0x40810102040100102,0x4040400000888888888]))),(0x0,0x0)]
def g217C : List ColumnInfo := [(1,0,216,0,7)]
def g217A : List (List Nat) := [[],[116],[67],[67,115],[115,67],[115],[96],[96,116],[96,67],[96,67,115],[96,115,67],[96,115]]
def g217D7 (j : Nat) := if j=0 then 0x3f else 0
def g217L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g217D7)
  | _ => emptyPacking
def g217I (_ _ : Nat) : Option (Nat × Nat) := none
def g217 : Forest := ⟨217,7,fun i => g217Y[i]?.getD (0,0),g217C,g217A,g217L,g217I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g217P7_0 : block g217 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g217B7 : block g217 7 0 1=true := g217P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g217T : checkedTables g217 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g217 0 0 0 = true)
  · exact (rfl : block g217 1 0 0 = true)
  · exact (rfl : block g217 2 0 0 = true)
  · exact (rfl : block g217 3 0 0 = true)
  · exact (rfl : block g217 4 0 0 = true)
  · exact (rfl : block g217 5 0 0 = true)
  · exact (rfl : block g217 6 0 0 = true)
  · exact g217B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g217G : graphValid g217 (boundsBefore K186) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low217 : Lower true (varsX 217) (graphGoal 217) 8 := lower_forest (g:=g217) (i:=0) (hints:=50331651) (before_sound K186 V186) g217G g217T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K217 := extendKnown K186 8 [(217,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V217 : Known true K217 := extend_ok (m:=217) V186 low217 (by decide +kernel)
def g123Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfff83ffffffff3422b,0x8c7ca80000000fe03fff])),(BitVec.ofNat 152 (word80 [0x805090080804034022,0xc4c0842850a142850a1]))),((BitVec.ofNat 152 (word80 [0x3ffc1ffe07b50c,0x5cbc20003fff0000000])),(BitVec.ofNat 152 (word80 [0x5610050404823a00c,0x50bc20e1c3870e1c387]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffc0001ffffad8c8,0x93211e01fc00001fc07f])),(BitVec.ofNat 152 (word80 [0x118002608110009088,0x912114142850a142850a]))),((BitVec.ofNat 152 (word80 [0xffffffffe0000804f4,0x691ab3fe0000001fff80])),(BitVec.ofNat 152 (word80 [0x260004800260480444,0x2012a32850a142850a14]))),((BitVec.ofNat 152 (word80 [0x91713,0xa28774000007ffe00000])),(BitVec.ofNat 152 (word80 [0x380227011380881711,0xa28034b162c58b162c58]))),((BitVec.ofNat 152 (word80 [0x4e917,0x7e4005fffff800000000])),(BitVec.ofNat 152 (word80 [0xc00438021c01044913,0x4a4000c183060c183060]))),(0x0,0x0),(0x0,0x0)]
def g123C : List ColumnInfo := [(1,0,122,0,7),(2,0,121,0,7),(8,0,115,0,7),(16,0,107,0,7),(32,0,91,0,7),(64,0,59,0,7),(0,2,25,96,6),(0,32,88,3,6),(1,32,88,2,5),(2,32,88,1,5),(33,0,90,0,5),(34,0,89,0,5),(64,2,25,32,5),(66,0,57,0,5),(3,0,88,0,4),(3,32,88,0,4),(9,0,114,0,4),(10,0,113,0,4),(17,0,106,0,4),(18,0,105,0,4),(24,0,99,0,4),(72,0,51,0,4),(80,0,43,0,4)]
def g123A : List (List Nat) := [[],[67],[96,81],[96,81,67]]
def g123D5 := limbs80 #[#[0x4c930483b2595324c120,0x483d254d3254120ecb65,0x1cf72595208ef825d953,0xc185b54f0333]]
def g123D6 := limbs80 #[#[0x26fb9aca907c9324c120,0xd7ec8992217edc13244,0x837db2a60906f9654c12,0x20fd6e4a8241fa4c9504,0x4837cb1aa09077953541,0x520bf6e6a8241bed8d50,0x2483e6a9a64906df634c,0x4d20ddeca99241bb5953,0x634827fbaac6904fd765,0x59520bdee4b2a413f5d7,0xd6548377b92ca905df73,0x359520dbee6b2a41b71c,0xd9325427eb9eca904ff7,0x73d8950bbee6b12a13f9,0x5c3634867eb9ec090cfd,0xf75585329faebb02653f,0x1a8c85e2810858260057,0x6c32978ae50249087638,0x2e9446a2906803c9c8de,0x1084b056aa94ea450a69,0xc1a20710042019c0e0,0x4041c206941050400000,0x100594100003040c1100,0x28810000304010040,0x30810000]]
def g123H6 := limbs80 #[#[0x3e088b1002c0a408,0x2a40101018005600]]
def g123D7 := limbs80 #[#[0xe54120fe4c120afd9110,0xd8d20bf58d20fb4c920f,0x8950bfd9520bf59520bf,0x132bfd8d21bfd8121bfd,0x20ff4c520ff4c910bfd8,0xff54d20ff58520ff545,0xff4c940ff59520ff58d2,0xfd8950ff58950ff4c950,0x58532ff58132ff4c941f,0xd47f0b911214814800ff,0x50a7f49087cfb1b83024,0x36c6a2cbd86af9592ad5,0x1e00c1607be6796ec1c7,0x84b0872440423842e3c4,0x94209c14046310c31a20,0x40728488070c14201804,0x9080c0065070c100e546,0x4a1018120395201c3250,0x5801c304038e2a220386,0xc384003088a101a81844,0x44187081c30503910141,0x203244230d0c10626144,0x2885091046216201111c,0xa880141110a0e195208d,0xc306140220ca90468840,0x4b0908c5091084805442,0x4c886]]
def g123H7 := limbs80 #[#[0x244440b81005,0x1c2400005707c914c64,0x44c00000281c0,0x3c6000146cc6b44000,0x0,0x87921000000343c0000,0x382000142f07,0x0,0x202b05d0100744480000,0x718c0f45000245800000,0x1110000003c34001831,0x0,0x148372c00151800000,0x39618000000c00000000,0x3a24000000002d,0x43b52c000003c1400,0xe1c002c1b804000000]]
def g123D8 := limbs80 #[#[0xd21fea87f503fa41fd10,0xd210c024007f4cbfa83f,0x10882448e230f161cea5,0x2258e22891464009648e,0x99023071638a4221300,0x18030898e22cc2058c18,0x1c652592]]
def g123H8 := limbs80 #[#[0x92ca702015810121c00,0xd5468c30005b88780000,0x6113e6488795fb0c,0xe4200000231905b1d848,0x460024b800cc4eb741,0x11145b4c001a60c400,0xe08006000006884b0000,0x5d42b6003c100078c428,0x287614003a9893001d6,0x1098000009220000]]
def g123D9 (j : Nat) := if j=0 then 0xa4188201bf else 0
def g123H9 := limbs80 #[#[0x94bce100006005,0x7a400dc0000000000,0x8000000025d00020b460,0xa00036200000031,0x14a006080]]
def g123L : Nat → Packing
  | 5 => (5,4,5,0,0,6,0,g123D5)
  | 6 => (33,3,5,0,0,9,0,g123D6)
  | 7 => (26,2,5,0,0,11,0,g123D7)
  | 8 => (7,1,5,0,0,9,0,g123D8)
  | 9 => (1,0,5,0,0,0,0,g123D9)
  | _ => emptyPacking
def g123I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 2 17 4 9 3 2 g123H6
  | 7 => lookupWord 11 113 2 12 6 2 g123H7
  | 8 => lookupWord 11 67 5 11 5 2 g123H8
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
theorem g123G : graphValid g123 (boundsBefore K217) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low123 : Lower true (varsX 123) (graphGoal 123) 10 := lower_forest (g:=g123) (i:=0) (hints:=16777299) (before_sound K217 V217) g123G g123T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K123 := extendKnown K217 10 [(123,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V123 : Known true K123 := extend_ok (m:=123) V217 low123 (by decide +kernel)
def g187Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xe007ff87ffffff98c2,0x903af000000fc0fc0fff])),(BitVec.ofNat 152 (word80 [0x4050051004001018c2,0x80006041041041041041]))),((BitVec.ofNat 152 (word80 [0xfff80007fe1ff83b0f,0x3485500003f03f000000])),(BitVec.ofNat 152 (word80 [0x806056202841213a0f,0x140551c71c71c71c71c7]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffff8001fffd03d,0x79312000fc000003f03f])),(BitVec.ofNat 152 (word80 [0x48118013084400015,0x7931028a28a28a28a28a]))),((BitVec.ofNat 152 (word80 [0xffffffffffe000462a,0x8b87903f00000003ffc0])),(BitVec.ofNat 152 (word80 [0x90260024009824628,0x2869514514514514514]))),((BitVec.ofNat 152 (word80 [0x4984,0x67ec8fc000003ffc0000])),(BitVec.ofNat 152 (word80 [0xe038043810e044100,0x63e88618618618618618]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x2651,0x42404fffffffc0000000])),(BitVec.ofNat 152 (word80 [0x100400040010000000,0x820820820820820]))),(0x0,0x0)]
def g187C : List ColumnInfo := [(1,0,186,0,8),(2,0,185,0,8),(32,0,155,0,8),(8,0,179,0,7),(16,0,171,0,7),(128,0,59,0,7),(24,0,163,0,5),(136,0,51,0,4),(144,0,43,0,4)]
def g187A : List (List Nat) := [[],[67]]
def g187D6 := limbs80 #[#[0xe5c5243e0374d5354932,0x5]]
def g187D7 := limbs80 #[#[0xf54d52bf59532fb54932,0x42a00ff58d52bfd8d52d,0xc70187cb1570186ae8a5,0x481c5cb15308c82071b2,0x81c60d4c72c071]]
def g187H7 (j : Nat) := if j=0 then 0x90 else 0
def g187D8 := limbs80 #[#[0xa3946061a403faa5fd32,0x1e851ca301c]]
def g187H8 := limbs80 #[#[0x0,0x410000000000000000,0x9800000000,0x4200000000,0x830000c4,0xa00000]]
def g187D9 (j : Nat) := if j=0 then 0x5432101bf else 0
def g187H9 (j : Nat) := if j=0 then 0x1c8f5 else 0
def g187L : Nat → Packing
  | 6 => (1,3,4,0,0,0,0,g187D6)
  | 7 => (5,2,4,0,0,8,0,g187D7)
  | 8 => (2,1,4,0,0,6,0,g187D8)
  | 9 => (1,0,4,0,0,0,0,g187D9)
  | _ => emptyPacking
def g187I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 1 2 0 4 0 0 g187H7
  | 8 => lookupWord 1 53 0 8 3 1 g187H8
  | 9 => lookupWord 1 3 0 6 1 1 g187H9
  | _ => fun _ => none
def g187 : Forest := ⟨187,9,fun i => g187Y[i]?.getD (0,0),g187C,g187A,g187L,g187I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P6_0 : block g187 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g187B6 : block g187 6 0 1=true := g187P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P7_0 : block g187 7 0 4=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P7_4 : block g187 7 4 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g187B7 : block g187 7 0 5=true := (@block_merge g187 7 0 4 1 g187P7_0 g187P7_4)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P8_0 : block g187 8 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g187B8 : block g187 8 0 2=true := g187P8_0
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
  · exact (rfl : block g187 5 0 0 = true)
  · exact g187B6
  · exact g187B7
  · exact g187B8
  · exact g187B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187G : graphValid g187 (boundsBefore K123) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low187 : Lower true (varsX 187) (graphGoal 187) 10 := lower_forest (g:=g187) (i:=0) (hints:=83) (before_sound K123 V123) g187G g187T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K187 := extendKnown K123 10 [(187,[]),(250,[96,81,32])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V187 : Known true K187 := extend_ok (m:=187) V123 low187 (by decide +kernel)
def g219Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x1ffc01ffc3ffffffe4,0x1b4332800007c00003ff])),(BitVec.ofNat 152 (word80 [0x4829148289040820c4,0x1b031225294a5294a529]))),((BitVec.ofNat 152 (word80 [0xfffffe0003fe1ff047,0x2c4bcc8000f8000f8000])),(BitVec.ofNat 152 (word80 [0x2b0182b1028424243,0x2c4b4c9ce739ce739ce7]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1ffffffffc001fff38,0xf46918001f0001f07c1f])),(BitVec.ofNat 152 (word80 [0x80c0200c0030808038,0x44480808421084210842]))),((BitVec.ofNat 152 (word80 [0x1fffffffffffe00010,0xaa846f83e0003e007fe0])),(BitVec.ofNat 152 (word80 [0x30040300040030400,0xa0046590842108421084]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xe0000000000000000e,0x11ba877c00003fff8000])),(BitVec.ofNat 152 (word80 [0xc0180c021810c0804,0x11b08221084210842108]))),((BitVec.ofNat 152 (word80 [0xc1,0x4514407fffffc0000000])),(BitVec.ofNat 152 (word80 [0x100201000200100000,0x42108421084210]))),(0x0,0x0)]
def g219C : List ColumnInfo := [(1,0,218,0,8),(2,0,217,0,8),(64,0,155,0,8),(8,0,211,0,7),(16,0,203,0,7),(128,0,91,0,7),(0,2,25,192,6),(10,0,209,0,5),(24,0,195,0,5),(128,2,25,64,5),(136,0,83,0,4),(144,0,75,0,4)]
def g219A : List (List Nat) := [[],[67]]
def g219D5 (j : Nat) := if j=0 then 0x2f8e017354921 else 0
def g219D6 := limbs80 #[#[0xb73b1aa490f655354921,0x19f6e0b2a65d354d524c,0x4b7db82ca997e5735492,0x471eda9652017edc1635,0xd03f211a0ae02790b61,0x2c98f971104f0e4204e,0x1602]]
def g219H6 (j : Nat) := if j=0 then 0x80 else 0
def g219D7 := limbs80 #[#[0xdd8d21bd58d21f954921,0x59532fb54932fd54d21b,0x8d52bfd8d52df54d52bf,0xa379688a331205400ff5,0x479122141e986448d388,0x3298479122e0a64388a,0x41656246580c52a4e191,0x6386450a5942e3864a46,0x16520408a]]
def g219H7 := limbs80 #[#[0x8090000402c95b8e,0x257a000]]
def g219D8 := limbs80 #[#[0x88a4b807f54bfa65f521,0x1ca38c24818273568384,0x2a851c612]]
def g219H8 := limbs80 #[#[0xf280000d30031c01a8,0x460000000c30018000,0xd3480000000000220800,0x5]]
def g219D9 (j : Nat) := if j=0 then 0x5430211bf else 0
def g219H9 (j : Nat) := if j=0 then 0x12a400c802b19 else 0
def g219L : Nat → Packing
  | 5 => (1,4,4,0,0,0,0,g219D5)
  | 6 => (7,3,4,0,0,8,0,g219D6)
  | 7 => (9,2,4,0,0,9,0,g219D7)
  | 8 => (3,1,4,0,0,7,0,g219D8)
  | 9 => (1,0,4,0,0,0,0,g219D9)
  | _ => emptyPacking
def g219I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 2 0 4 0 0 g219H6
  | 7 => lookupWord 2 13 1 8 3 1 g219H7
  | 8 => lookupWord 2 29 0 9 4 1 g219H8
  | 9 => lookupWord 1 7 0 7 2 1 g219H9
  | _ => fun _ => none
def g219 : Forest := ⟨219,9,fun i => g219Y[i]?.getD (0,0),g219C,g219A,g219L,g219I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P5_0 : block g219 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g219B5 : block g219 5 0 1=true := g219P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P6_0 : block g219 6 0 4=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P6_4 : block g219 6 4 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g219B6 : block g219 6 0 7=true := (@block_merge g219 6 0 4 3 g219P6_0 g219P6_4)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P7_0 : block g219 7 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P7_3 : block g219 7 3 5=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P7_8 : block g219 7 8 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g219B7 : block g219 7 0 9=true := (@block_merge g219 7 0 3 6 g219P7_0 (@block_merge g219 7 3 5 1 g219P7_3 g219P7_8))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P8_0 : block g219 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P8_1 : block g219 8 1 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g219B8 : block g219 8 0 3=true := (@block_merge g219 8 0 1 2 g219P8_0 g219P8_1)
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
theorem g219G : graphValid g219 (boundsBefore K187) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low219 : Lower true (varsX 219) (graphGoal 219) 10 := lower_forest (g:=g219) (i:=0) (hints:=16777315) (before_sound K187 V187) g219G g219T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K219 := extendKnown K187 10 [(219,[]),(249,[96,81,33])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V219 : Known true K219 := extend_ok (m:=219) V187 low219 (by decide +kernel)
def g235Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xe007ffffe1ffff9164,0xdc16e000000fc0000fff])),(BitVec.ofNat 152 (word80 [0x44510a204404101144,0xcc00e249249249249249]))),((BitVec.ofNat 152 (word80 [0xfff800fffe1ff8318b,0x3c89500003f000fff000])),(BitVec.ofNat 152 (word80 [0x80602c028040213083,0x3c0140c30c30c30c30c3]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffff00001fffda3d,0x31312000fc003f00003f])),(BitVec.ofNat 152 (word80 [0x80300b0881400a39,0x31110186186186186186]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffe000462a,0x8b87903f00000003ffc0])),(BitVec.ofNat 152 (word80 [0x902404c0009824628,0x3861514514514514514]))),((BitVec.ofNat 152 (word80 [0x4984,0x67ec8fc000003ffc0000])),(BitVec.ofNat 152 (word80 [0xe038070110e044104,0x42ec8618618618618618]))),((BitVec.ofNat 152 (word80 [0x2651,0x42404fffffffc0000000])),(BitVec.ofNat 152 (word80 [0x100400800010000000,0x820820820820820]))),(0x0,0x0)]
def g235C : List ColumnInfo := [(1,0,234,0,7),(2,0,233,0,7),(8,0,227,0,7),(32,0,203,0,7),(64,0,171,0,7),(128,0,107,0,7),(3,0,232,0,5),(9,0,226,0,5),(10,0,225,0,5),(33,0,202,0,5),(34,0,201,0,5),(40,0,195,0,5),(65,0,170,0,5),(66,0,169,0,5),(72,0,163,0,5),(96,0,139,0,5),(35,0,200,0,4),(41,0,194,0,4),(73,0,162,0,4),(74,0,161,0,4),(98,0,137,0,4),(129,0,106,0,4),(130,0,105,0,4),(136,0,99,0,4),(160,0,75,0,4),(192,0,43,0,4)]
def g235A : List (List Nat) := [[],[97,83],[16,99],[16,48,80,96],[48,101],[48,81,96,16],[80,49],[80,97,48,49],[96,16,49,83],[96,81]]
def g235D4 := limbs80 #[#[0x10c7060f915c87254110,0x30d095539259171d49]]
set_option maxRecDepth 16000 in
def g235D5 := limbs80 #[#[0x90221c69765495048110,0x71543204421bf26c3aca,0xa0a9a64a8e4088758549,0x221bc3834c951c8110f,0x354720443aa2e6a9aa39,0x1c3b02a964088674e0d7,0x2215e39760552c8110cf,0x485304421f32fc32a790,0xb2a6490a60887705d132,0x21dc1754c9214c110f60,0x85304437830a99242982,0x2aa690a60886f0e15324,0x1d517454d514c110f28b,0x530443a62e8aa2a29822,0xae8a9a60885d464f5454,0xe5391595534c110e2cb2,0x30443ac2eaa924318221,0x6a8c60884f4e4d85486,0x3174551518c110ce8baf,0x4427a726c0ea518221d,0x6b2c60884f4e4d81d523,0x1434c92150110c6dc3f0,0x443e42a8a9242a0221f8,0x10a80887585d55248540,0x985d62150110d98c2aa9,0x43c62a9b12a2a02211f3,0x8a80886cc55382545404,0x3dcd5150110b98ca6a6a,0x2e632b2a2a2a02219d38,0xa80885e8648845454044,0x20d6550110bc8c9908a8,0x1b10fc1acaa0221a9b84],#[0x808847c65f8254640443,0x895290110cb9c3aa8a8c,0xe32fc0aa920221c69755,0x8874555173547404423,0x9625411086ecbf06b2e8,0x2c4a92a2a822186f85dc,0x886d8e095254550443cc,0x5154110f28b1aa6a8aa0,0x7b9aa2a8221d537354d,0x879858952945504433a7,0x154110db0c12a528aa08,0x4ba6e2a8221b61825487,0x792d8d524c950442bc12,0x54110d34c32a4992a088,0xc0c64a8221a598654d32,0x9a619528c9504436c2a4,0x4110db0a9303212a0886,0x12a4a8221a698654a425,0xae4d62549504434d706b,0x110ba4c9cc4a92a08859,0x2a4a8221761911c95254,0x6507254950442e932639,0x10b34c96c6a92a0885ca,0xa4a8221a5b83d8d52541,0xd63d4950442cd325b22,0xb35c92c9a92a0886966,0x4a82216c9931c9625411,0xf5358950442cd325a9ac,0xb2cc990ab12a088696e0,0xa82215e3915c87254110,0x82d4d5044339306b90e4,0x34c910ab22a088696d8d],#[0x82215e192a077454110b,0x759132442ae32b40ee8a,0xfca30eb2a648841fe558,0x2214eb92595701091085,0x5c0424429b726b2ae021,0xcc2cab98848852ee5165,0x2186d75e09651091086f,0x94424430baebc1aca212,0x9b0eb28848843765f835,0x145f93619751091086fc,0xa4244296f28b2ae32122,0x708b2c84885a3e4d65d0,0xdf9361d6590910956c9,0x524433a306b88e0a9221,0xe2382a48866c611711c1,0xb97661070549108f9cc2,0x24421f730bb0e0a92218,0x5b22a48842fe5187d8d5,0x591dd36454910c57ba30,0x4421bf26c36e8a92214b,0xbb2a48863620f805d952,0x85e057654910c3dc2f00,0x4313f0841aeca9221877,0x86a488627e13835d9524,0x259171d4910a75c92c8b,0x21bf26c3ac7a92214e79,0x6a48862b5d3825935244,0x61d64d4910936caf04b2,0x15ee9c12c8b12210df93,0xc48841fe61751d562443,0xc8725951086ecbf06b2c,0xb0e7c02e4b2a210ef985],#[0xa88627e10735c9654431,0xd725951086f4c0e6b92c,0xf09b9ae4b2a2189c84dc,0x8842fe5182dcd6544313,0x7359510a6ac8905b9aca,0x28c16e6b2a2149c9460b,0x86a6593835c55084293f,0x454210f0cc9ac8a9aa10,0xac0ac8a84216ab925d16,0x58d6595454541842c772,0x50610b1bcb2a8a8a8308,0xc06e4a8c214bb905d564,0x8d6158159151843172c8,0x4610a57c930eb22a3086,0x36e8a8c2149f9361d645,0xe59180dc5528421bf26c,0xe10a5cc86e8b22a70862,0x6e6aa4214b79161d6454,0xe458759153083172c8c0,0x2087bc8b09bb2a61052d,0xc9a98414cf925d163d4c,0x97825d35308295f24ba2,0xd34c32a518aa09061b5,0x2a8241a698654a515412,0xc725c55048369706a92e,0xda5c1aa6a92a09057264,0x18a4166991d8d5254120,0x86dcd5148217f28c3acb,0x7bcc2e238aca9042fe51,0x84418f37160271595208,0x6dd151883552c9c12a8a,0x7c92e8b26a310437e4d8],#[0xc411e990e0974d4620a5,0xdd9538821bf26c3ea8b0,0xc92e8b26a71043de4584,0x411e990e0974d4e20a57,0x8a515431d72cc06e4aa4,0x3f06b08c2a8437e4d87d,0x1569905c95218550c6bc,0x96154313b09b98c4b0aa,0x6e6312c2a8627a137318,0x4cf92590735855086fcc,0x6154299f24b26e6b0aa1,0xb94c2a843766264dcd,0xcf936197298550cb4c2b,0x154295f28c32e530aa14,0x3b82a4a852e650805cb6,0x99260470549508ddca30,0x5436c324c08e0a92a136,0xb14a4a84cee5181dc152,0x73e056218950967c9b03,0x217f28c16e6b0ea18cd,0x1a02e0500880e00c00c0,0xc21642604405a0a8138,0xc1d8398700da1a833864,0xc44a89211e230420810f,0x680cd19431c620bc1682,0x8ea1ce390708de1b634c,0x72083f07c8f61e63c076,0x564a09291d23445c8790,0x514a113f2784e49b12e2,0x4ad1572a8544a714b290,0x916f2d85a4b31632c057,0x87308604bf17b2f05d4b],#[0x338664cb193320634c51,0x26c4d71ab350694d119f,0x60ea9d239e730e21c137,0xf69ea3ce790f09de3b67,0xa023fe7f0fc9f63e67c0,0xa42e85108a0e41682102,0x5e8b114a264468810ea1,0x91120a3e4768e11aa324,0x12ca564a694126a4a48e,0x8a6e4d69a132a624be97,0x86506a013ea7a4ee9d13,0x536a614aa9251ea3144a,0x6ac156aaa54ea9150a9e,0x2162ac257eaf15cab656,0x4001000b5168ace596b,0x8901100002e020200000,0x640422404202c1819640,0x41000200100000000001,0x2b820488190614000090,0x10400000001041088100,0x41000000000000000004,0x2800400206040504001,0x141000,0x0,0x0,0xc1000c040c0400000000,0x70]]
def g235H5 (j : Nat) := if j=0 then 0x19f else 0
set_option maxRecDepth 16000 in
def g235D6 := limbs80 #[#[0x48420443705cd2108110,0x443785d52108110d6175,0x5d15108110dd17354420,0x8110d7175544204436c,0xd71815d4204427ce1d51,0x54530443f04c9214c110,0x44396595534c110f5153,0x5515150110bd38354630,0x541109f38754640443cc,0xe69625495044237e0d76,0xd4d504439658d5354110,0x443acd076454110e5b63,0xe0d76d49108df835d952,0xd4d10cdb635c35344237,0xe596554d308429761763,0x549508439a5895254210,0x8438e5935254210e3964,0x5915354210e596354d50,0xd4610e3964d4d508438e,0xcb9645c3528432e59170,0x5c3548432e59170d4e10,0x833658f7054c20cb964,0x5977054c20cb964dc153,0x54120e6952d85504831e,0xb6b83549504839ad8d52,0x1c950482da6165254120,0x882da60b5354120bc983,0xe0d7654620e596354d50,0x552209e980dc95488237,0x8f787584615432b59372,0x1c152542dc6047054950,0x542ce6107054950b5983],#[0xe1d6218950ccd7358862,0x81108df835c7625423b,0xdf1815d4204437c5d551,0x54120443da5495048110,0x4433d5d95148110cf976,0xe0d6548110aef8259520,0x481108fd8759520442b7,0x9f7815d5204427ee0175,0x543204423fe157648110,0x442fce0550c8110df171,0x5d550c8110f695254320,0xc8110bf181d43204435e,0xbe982d4320443da54b50,0x547204435e5d750c8110,0x4427de1d51c81109f587,0x59571c8110de5525c720,0xc8110aef82597204433d,0x8ff8759720442b7e0d65,0x4c720443f854931c8110,0x4437c5d531c8110fd153,0x4c951c8110bf1854c720,0xc8110fe15254720443f8,0xf735354720443dc54d51,0x547204437c5cd51c8110,0x4437c5d551c8110bf383,0x5d532c8110fc9534cb20,0xc8110be9854cb204437a,0xde97354b20443f860552,0x54b20442fae0d52c8110,0x443765cd53c8110deb87,0x61d53c8110afb8654f20,0xc8110bf181d4f204427e],#[0x9f987d4f20442fa60b53,0x59720442fae0965c8110,0x4427ee1d65c8110bdb83,0x61e65c8110be98299720,0xc8110df1815d7204427e,0xfe142485304427ee0d75,0x48530443f8549214c110,0x4437c5d1214c110fd153,0x5d5214c110ef16548530,0x4c110bf185485304437c,0xfd13254530442fce1521,0x54530442fce09514c110,0x443dc551514c110fd153,0x5d1514c110f735454530,0x4c110df175545304437c,0xed9654c930443765d132,0x54930443765d5324c110,0x442fc607524c1109fb87,0x61b524c110bd983d4930,0x4c1109f987d4930442be,0xbdb8254d30443f460553,0x54d30443765d1534c110,0x442fce05544c110ed965,0x61d544c110db97455130,0x4c110bf181d51304427e,0xaf986d5130442f660f54,0x5d1304427e61f544c110,0x4433e595744c110df381,0xe05654c1109fb855d130,0x4c110edb8359530443bc,0xddb835d5304437ce0575,0x486304427ee11754c110],#[0x443bc595218c110fe152,0x615218c110df17548630,0x8c110bf38548630442fc,0xfd38354630442fce0951,0x54630443dc551518c110,0x4437c5d1518c110f7354,0x5d5528c110df17554630,0x8c1109fb8754a304435e,0xd7975d4a30442fc60752,0xd4a30442be61b528c110,0x442fce05548c1109f987,0x61d548c110db97455230,0x8c110bf181d52304427e,0x9f987d5230442be61b54,0x596304433e595748c110,0x4433ee1d658c110edb83,0xe0550501109fb845d630,0x50110af98654140442fc,0xf355454540442fc60750,0x59540442b7e0d6550110,0x443f84c92150110abf84,0x5952150110fe15248540,0x50110ef36548540443bc,0xfb154885404437c5d521,0x88540443bc5962150110,0x442fc6162150110df175,0xe115150110f395454540,0x50110ef36254540442ee,0xf715354540442fce0951,0x54540443dcd4d5150110,0x442fce0d5150110df373,0x9515150110fb15454540],#[0x50110f735454540443ec,0xfb38454540443ec21151,0x545404437c5d55150110,0x4437c5d65150110df375,0x6165150110df37594540,0x50110bb984d4540442fc,0xd7975549404427e61f51,0xd49404427ee1d5250110,0x442ee6135250110bf181,0x61b5250110d7975d4940,0x501109f987d4940442be,0xcf975d8940442eee1162,0x59540442be6176250110,0x442eee116550110bdb83,0xe056550110ef38159540,0x50110afb8259540442be,0xedb8359540443b620d65,0x59540443ae2116550110,0x4433e21d6550110ebb84,0x60b6550110bb98499540,0x90110ef16254640442be,0xf715454640442fce0951,0x54640443dcd515190110,0x443ba5895290110df175,0x6195290110d797554a40,0x901109fb8754a40442be,0xd7975d4a40442fc60752,0xd4a40442be61b5290110,0x4433e5d562901109f987,0xe055490110afb8558a40,0x90110d797555240442fc,0xd7975d5240442fc60754],#[0x59640442be61b5490110,0x443b6e0d6590110afb82,0x6057590110cfb8759640,0xd0110df171543404437c,0xbbb8454340443765cd50,0x547404435e5d550d0110,0x443cd55151d0110dd573,0x61d51d0110d757554740,0xd01109f787547404427d,0xcf5655c7404436d55171,0x5cf404436755173d0110,0x442b7e0d65d0110cdd65,0x5d565d0110abf8459740,0x541108ff87597404431f,0xe6d62549504427d60b71,0x589504433bdc96254110,0x4429fe156454110a7f85,0xe097654110adf8359550,0x54110cdf835d9504423f,0xef16254550443dc54951,0x54550443bcd895154110,0x443dc54d5154110bf382,0xd8d5154110ef16354550,0x54110df37354550443bc,0xef16294550443dc54a51,0x94550442fc60a5154110,0x4437cdd25154110ef164,0x6087154110f71521c550,0x54110bdb835c550442fc,0xdf272dc550443dc54b71,0xdc550442fc60b7154110,0x4437c5cf7154110f7153],#[0x5d37154110bf183dc550,0x54110f69524c9504437c,0xedb634c950443d654d32,0x4c950442de6153254110,0x442fc6063254110af986,0x6163254110f69528c950,0x54110af9868c950442de,0xbd98310950442fc60442,0x10950442de6144254110,0x4427e61c4254110af986,0x54942541109fa8710950,0x54110af98650950443da,0xfab4290950442fc60642,0x90950443da54a4254110,0x442be61a4254110b7985,0x61f4254110af986d0950,0x541109fa87d09504427e,0xf718154950443ba58952,0x54950443dca055254110,0x443da9895254110f6962,0x1c95254110e7b6254950,0x54110f6b7254950443da,0xe7b63549504439e58d52,0x54950442dee0d5254110,0x4439ed915254110e7964,0x6065254110d7b7454950,0x54110ee96294950442fc,0xaf98694950442de61652,0xd49504439e58b5254110,0x4439e58f5254110e7b62,0x60f5254110e7b63d4950,0x54110e7964d4950442de],#[0xd7b74d49504439ed9352,0x58950442dee156254110,0x443badc96254110ee872,0xd4d6254110e795358950,0x54110afb83589504439e,0xafb84589504433edd162,0x589504439e2156254110,0x442f660e6254110e7b85,0xdd36254110b798598950,0x54110af984d89504433e,0xde9721c950442fc60472,0x1c950442f660c7254110,0x442eea107254110bb984,0x6067254110bf3815c950,0x54110bf38150d50442fc,0xddb7350d50443b6d8d43,0xd0d504427ea1d4354110,0x4427e61f4354110af986,0x58d53541109fa87d0d50,0x54110ddb7354d50443b6,0xb7b8254d50443dc60553,0xd4d50443d6dcd5354110,0x442be60b6354110b7982,0x6136354110edb73d8d50,0x54110bf3815cd50442be,0xbf381551504427e61373,0x951504436edd15454110,0x442be61a5454110dbb74,0xe096454110b7b8559150,0x54110e788559150442be,0xbd983991504439ee1564,0xd9150442de6166454110],#[0x442fce057454110af982,0xe097454110be8825d150,0x54110bf1819d150442fa,0xdbb749d150442f660e74,0xdd150442fc6077454110,0x4437ca077454110df181,0xe1d62941109f983dd150,0x94110bf381552504433e,0xcfb87592504436e5d154,0x5c7504433d58971d4110,0x4433d59171d41109f782,0xe1562d4110ced7258b50,0x4c910a7f85593504429f,0x9f984dc1324433e59370,0x591324427e617704c910,0x4423f61d644c910aef82,0xe0d654c9108ff8759132,0x4c9108fd8759532442b7,0xcfb805d9324423fe1d65,0x5d9324423fe11764c910,0x44379549718c9108ff85,0xe01528c910cf5655c632,0x8c910ced7654a32442fa,0x8fd8759632442b7e0d65,0x5d6324423fe1d658c910,0x4423fe15768c9109fb80,0xd957010910cf9655c042,0x10910cdd655cc424433e,0xaef825944244337d9573,0x59442442b7e0d6510910,0x4423f61d6510910c7d75,0x5d765109108ff8759442],#[0x109108fd87d94424431f,0xc7d865d4424435e60175,0x5d8424431fa197510910,0x443cb55152509108ff85,0xe0d65509108fd87d8d42,0x509108ff8759542442b7,0x9fb805d5424423f61f65,0x5c6424423fe197550910,0x4433d5957190910de552,0x5974290910cf7655c642,0x90910eaf65d0a42443ab,0xadf83596424433b5d952,0x59642442afe116590910,0x4423fe1d65909108fd87,0xe0175909108fd87d9642,0x549108ff855da424427e,0xbd9831c1524437c5c470,0x1c152442ee6107054910,0x4437c5c77054910cf976,0x5db7054910df271dc152,0x54910cfa76dc1524433e,0xdf181dc1524427d60770,0xdc1524437ca077054910,0x4427e60f7054910cfb62,0x59770549109f984dc152,0x54910cfb65dc1524433e,0x9f980dc5524433ea1b70,0xd8952442f360e6254910,0x442bb60b6354910a7d85,0x61f6354910cdf73d8d52,0x549109f581dcd524423f,0xb7980d51524423f61b73],#[0xd91524423fe1d6454910,0x4432fdd36454910aed82,0x60774549108fd87d9152,0x549108fd86dd1524427d,0xadf8359552442bbe0965,0x5d952442bb60b6554910,0x442afe117654910adf83,0xe1176549109df835d952,0x54910cfb805d9524426f,0x8ff815d9524433de0576,0x5d9524433720d7654910,0x4423fe0d7654910cdf83,0x6037654910c7f855d952,0x549108fd83dd9524423f,0xcf5655c6524423f61376,0x596524433dd957194910,0x442b7e0d6594910aef82,0xd8970d4910aed82d9652,0xd4910cf9635c3524433e,0x9fb835c3524433ed8d70,0x5c3524433e59170d4910,0x4427ee1170d4910cfb64,0x58d71d4910cf7625c752,0xd4910cf7635c7524433d,0xcf5645c7524427de0d71,0xd8b524433dd9171d4910,0x443375cd63d4910a7d85,0x61f63d49108fd8758f52,0xd4910aef82593524423f,0x8fd87593524432f5d164,0xd93524423fe1d64d4910,0x4427de0574d49108fd87],#[0x20d76d49109df835db52,0xd4910cdf835db5244337,0x8ff845db524423fe0d76,0x59562442bbe096458910,0x442b7e0d6558910aef82,0x60a6558910c7f7559562,0x58910c7f7599562442bb,0x8fd85dcd624423f61373,0x1d562442b760c7558910,0x442bde057558910c7d75,0x6067558910adf835d562,0x58910c7f759d562442bd,0xcdd655ce624423f60f75,0x59662442bbe096598910,0x4431f5d56598910adf83,0xe1175d89108ff855d362,0x54d10df1715c1534423f,0x9f581dc9534427e60372,0x595534423f61b7254d10,0x4439ee016554d10adf83,0xe017654d10e5f8359553,0x54d108ff825d9534433e,0x8fd82dd95344337e0d76,0x5cb534427ee1170d4d10,0x44337d8d72d4d109fb80,0xe0976d4d10e5f8359753,0xd8d10cdf835db534423f,0x8ff855cb634423fe1172,0x5d7634423fe0975d8d10,0x4437cdc77059510cdf83,0xe037359510ddb73dc165,0x59510cdf73dc16544376],#[0xed873dc165443bcdc770,0xdc165443b6dcf7059510,0x442be6137059510af983,0xdcc7259510ced721c965,0x59510afb805c96544337,0xcdc735c965442bde0572,0x5c96544337dcd7259510,0x442af2117259510adf83,0x6027259510abf845c965,0x59510af5819c965442be,0xcdf739c9654433bdca72,0xdc965442b760e7259510,0x44337dcf7259510cdc73,0x61372595108fd83dc965,0x59510afb805cd654423f,0x8fd82dcd65443b6e0373,0xdcd65443376037359510,0x4433720b7359510cdf80,0xa0b7359510cdd82dcd65,0xd9510cdf82dcd6544337,0xed96554d308423fe1172,0xd5130842f660f544c210,0x8427e61f544c210af986,0xe19754c2109fb845d530,0x54210eb964505508433e,0xeb96454550843bc58551,0x5c550842f6e0d7154210,0x843ba5895254210eb964,0xdd95254210eb96454950,0x54210e7961d49508439e,0xafb865c950843ae59172,0x54d50843b658d5354210],#[0x8439e5915354210eb964,0x5935354210e7b7654d50,0x54210eb9645cd508439e,0x9f984dcd50842bee1973,0x59150843ae5915454210,0x843ae6056454210eb974,0x6156454210eb98359150,0x54210beb825d150843ae,0x9f983dd150842bee1974,0xdd950842be60b7654210,0x842be6137654210af983,0x5515150610bf38054541,0x50610eb56454541843cd,0xabd86551418439d59551,0x59141842afe195450610,0x8427ee017550610cbd75,0x60372546109f984dc151,0x54610cbd64dc9518427e,0x8fd86dc9518431f59772,0x551518438f5915454610,0x8429fe195454610a7d86,0x61b5454610e3d64d5151,0x54610cbf74591518429f,0xe3d8559151843ad60564,0x591518438fa156454610,0x8432fa1d6454610cbd87,0xe1165546108fd86dd151,0xd4610cf9625c3518429f,0xced7258b518433e59170,0x5cb518427ee0172d4610,0x8431f59572d4610cbd64,0x61954d4610e3d6455351],#[0xd4610cbd74593518429f,0xcbd87593518438f61564,0xd4961842be6035258610,0x8423f61f5258610af581,0x5977054a10ee962dc152,0x54a10cf976dc1528439e,0xcf986dc1528433e59770,0xdc5528427e6037154a10,0x8432f5937154a10ced62,0x59171d4a10c7d65dc552,0x54e10c7d655c7528432f,0xe9d83591538432fdd164,0x591538432f61d6454e10,0x8427e6037454e10cbe87,0xe117654e108fd86dd153,0xd4e108fd84dd9538423f,0xcbd74593538433e59170,0x593538423f61d64d4e10,0x842be6035458e10cbd87,0x61f5458e10add83d5163,0x552109f980dc5548423f,0x9f980dcd548432f59371,0xdcd548432f5937355210,0x8423fe0d76552108fd86,0x59171d52108fd83dd954,0x59210cbd645cf548432f,0xabf855c5648432f5d571,0x5cd648432f5d57359210,0x842afe057559210abf85,0x6067559210abf835d564,0x59610abd839d564842af,0x8fd84dcd65842b7e0d71],#[0x54d610823f60f7459610,0x82bd6135358420af784,0x5937054c20ed963dc153,0x54c20e7965dc153083ae,0xcf964dc1530833e5db70,0xdc1530833e5977054c20,0x8337dd16354c20cf986,0x60d6454c20cbf7459153,0x54c20cbd8759153083a7,0xc7d65dd1530832fa1d64,0x5d9530823f61b7454c20,0x823f6137654c208ff84,0x5d164d4c20cdd7458f53,0xd4c208fd87593530832f,0x9ef825d3530832f61d64,0x5d1630831f59574d4c20,0x82b7e157458c20cdd75,0xe117558c20edb805d563,0x59420add849d563082b7,0xe7b805cd650823f61373,0xdcd650829fe117359420,0x483da6015254120a7d84,0x5493154120f6b8054950,0x54120f59534c550483da,0xaf9868c550483da54a31,0x54550482be61a4154120,0x483da54a5154120f6952,0x5496154120af98694550,0x54120b7b8558550483da,0xb798598550483da54a61,0xd8550483ba54b6154120,0x483da5487154120eeb72],#[0x1c97154120f69525c550,0x54120beb825c5504837a,0xf69529c550482f6e0d71,0xdc550482fa60a7154120,0x483da54d5254120f6952,0xe0d5254120eeb6354950,0x54120f697354950482fa,0xf698354950483dadcd52,0x54950483dae0d5254120,0x483da54f7254120f6887,0x5d37254120be983dc950,0x54120f698254d504837a,0xaf981d8d50483d6dcd53,0x55150482fae097354120,0x482be6076454120dbb74,0xe1d654c520beb825d150,0x8c520cf576546314823f,0x8fd8759631482b7e0d65,0x5da314823fe1d658c520,0x4827b60b70545208ff85,0x6076354520a7d85d8551,0x54520cdf73d8d51482bd,0x8fd86dcd514823f61f63,0xd9551482bde056554520,0x482b7e0d7654520af581,0x60f76545209df835d951,0x94520af781596514823f,0xcfb615c351482bd60765,0x5c3514835e54d70d4520,0x4833ed9170d4520cfb63,0x61761d45209fb845c351,0xd45208fd87d8f514829f],#[0xc7f75595614823fe0d76,0x596614831fdd66558520,0x4831f5d56598520af781,0x61b7154d209ed82dc553,0x54d209ed82dd1534823f,0xadf83595534823f61b74,0xdd9534823f6077654d20,0x4827ee1170d4d208fd84,0xe1176d4d208ff815db53,0xd8d208ff855c7634823f,0xdeb72dc1654823fe0575,0xdc1654833edc77059520,0x482be6137059520eeb72,0xe017159520cf5711c565,0x59520adf835c565482be,0xcf7719c565482be60271,0x5cd654823f60f7159520,0x482bbe097359520afb80,0x61373595208fd81dcd65,0x54220ef161545508823f,0xe7b52585508839e54961,0x5c5508833edd16154220,0x8833edd97154220bdb83,0x5895254220afb865c550,0x54220ed96354d50883ba,0xe7b7654d508839e59153,0x5cd508839e5935354220,0x882fae095454220afb86,0xe097454220eb96455150,0x54220afb865d150882fa,0xaf983dd950882be60776,0x58551882be6137654220],#[0x8839d5516154620cf772,0x6037254620e775458551,0x54620e3d64551518827e,0x8fd86dd1518832fdd164,0x5d951882b7e0d7654620,0x8823fe117654620cdf83,0x58970d46208fd84dd951,0xd4620cf9645c3518833e,0xe3d64553518823f61d62,0x593518832f5d164d4620,0x8827be0974d46208fd87,0x6035258620afb8054961,0x58620af581d4961882be,0xaf980d5161882bde0554,0xd5161882bd6075458620,0x8823f61b7154a208fd87,0xe117654e208fd86dd153,0xd4e208fd84dd9538823f,0xcbd74593538833e59170,0x5d3538823f61d64d4e20,0x882bbe095458e209ef82,0x60f5458e20af980d5163,0x552208fd87d5163882b7,0x9f980dc5548837adc970,0xdc9548823f61b7155220,0x883ab5937255220be980,0x6037255220ced76dc954,0x552209ed81dc9548837a,0xced86dc9548833b59772,0xdcd548827e6037355220,0x8823f61b7355220cbd64,0xe0976552208ff815d954],#[0x552208ff835d9548833b,0x8fd83dd9548823f60776,0xdc565882b7e0d7159620,0x8823f61373596208fd84,0x6077459620aef825d165,0x545508fd83dd1658823f,0x9f982dc1515435e54b70,0xdc1515435e54f7054550,0x5427e61370545509f983,0xdcf6354550e5f6354d51,0x94550d79525c25154337,0xe7552d86515433ed9170,0xd8651542bd60b6194550,0x5433b5cb6294550af584,0x61f64945508fd87d8a51,0x18550cf572584615423f,0xcf78758461543b5e0d61,0x588615435b5c95218550,0x5427e60172185508ff87,0xe1d6418550aef8259061,0x585509f9805d0615423f,0xddb73dc161543761cf70,0x549615435bdc95258550,0x54357dcf5258550d5f73,0xdcc625855097e87d4961,0x58550add831896154337,0xabe8418961542af61062,0x589615423fa1c6258550,0x5433bdca6258550cdf73,0xdcf6258550cdf7398961,0x58550e5f6354d6154337,0xd5f73d4d6154357dcd53],#[0x1cd61543375907358550,0x54376e037358550cdf64,0x9937358550cdd64dcd61,0x58550cdf64dcd6154337,0xcbf7499161542b760e64,0xd86615439d54b6198550,0x5435b5c95298550af582,0x5cb5298550d7970d4a61,0x9855097d87d4a615435b,0xde9805ca61542bde0562,0x5ca615433bd917298550,0x5433b6197298550d6d85,0x61e52d8550afb8058b61,0xd8550afb805cb615423f,0xcfb805cb615433e20172,0x5cb615423fe0d72d8550,0x5423fe0973d85508ff84,0xe0974d85508ff845cf61,0xd85508ff835d3615423f,0xadd839d361542be60274,0xdc1525429f61674d8550,0x5427e60f70549509f981,0x60470549509f984dc152,0x54950b7a861c152542de,0xf6b62dc152542de60770,0xdc152542de60f7054950,0x542dbe096354950b7984,0x6076294950cef625c652,0x189509f9805c462542bb,0xaef81588625437c60171,0x5c6625433be1d6218950,0x54277e0d71d8950cef62],#[0x20d71d8950adf835c762,0xd8950cdf835c76254337,0x8ff845c7625423fe0d71,0x5cf625423fe0573d8950,0x5423fe0574d89508ff84,0xe0d70587508ff835d362,0x58750abc845c961d42b7,0xaf5819c961d42afe1172,0xdc961d42b760e7258750,0xd423f61372587508fd83,0x61373587508fd82dcd61,0x58750af5819d161d423f,0x8fd83dd161d423f60b74,0x9c562d42afe117158b50,0xd42bb60a7158b50af980,0x6137158b508fd83dc562,0x58b50afb805cd62d423f,0x8fd84dcd62d423f60773,0xdd162d423f6077458b50,0x12003000600008fd83,0x3a80c002a009001e006,0x5e81740570132048c10b,0x41f207b01d406f01a40,0x42790960237087c21008,0x3120c0c2eb0b4c2b20a4,0x900dbc3570cfc3300c84,0xb10684020fa83c90ee83,0x123c46e117c450110443,0x45850714044f213444b0,0xc056a156c54c14f45251,0x45bb16b05a6165c58815,0x5f117ac5e517585d0170],#[0x4b191462d18786181800,0x819a4663197465719446,0x1aa06a21a4c68419f867,0xbe46e11b486c31ad06ae,0xe07321cb071d1c387081,0xc7681d647531d347471c,0x7cb1ea87a41e3077d1dd,0x3720a081020047e91f8c,0x621c0861216c84c20f48,0x234c8bb22b088b21f087,0x49090c23f48ee23a08e2,0xb0954253893f24c092a2,0xc99c265898725e097225,0x9e427549cf27009b126a,0x3528bca202844a0227cc,0x429b8a5f2964a4a2910a,0x2a90a952a3ca892a0ca7,0xb8cad42b38abf2ac0aaa,0xf4b252c58b072be0ae92,0xcb882de4b732d90b552c,0xc062fb8bdf2f64bca2ee,0x573144c4230ccc243054,0xf3240c8131ecc7531bcc,0x3414ce43330cbd32b8c9,0x5a0d503504d3234b0d14,0x74dc536d8da7363cd773,0x8e1f3840e0a37ecdec37,0xe703984e523930e3d38b,0xaf3aa4ea33a50e8539fc,0x73ba0ee23b4cec43ad4e,0x3d08f333cb4f1e3c3cef,0xe28f7b3d8cf5d3d5cf51],#[0x48fc33ed0fa53e7cf903,0x101d40390083fc0fe13f,0x654159047410503240b,0xb6429d098422507a41ad,0x44290fb43b10dd43150,0x456d14c44f5125445911,0x6f91af46a519a462d16a,0x1920047e91eb47711cd4,0x924848e522a489121548,0x28749bd269498d25d493,0xd84b252ba4ad12a54a59,0xd4cf93264c5d2ff4bc12,0x4e193804dc536b4d7134,0xf813d14f093b34e91395,0x5544f510143150654014,0x148551d947051a946451,0x4d6531d4b852a549a525,0x15541950053c54eb5395,0x4553953f54c152a54915,0x55ed56c5599560556955,0x70d5b4569559f566558a,0x5160557fd5f057855c95,0x5656591d63858c962c58,0x6b95acd6a45a5567d599,0xf85bc96e35b516ce5b21,0xe5ca17195c4d70d5c1d6,0x5d9d7615d497435cf572,0xe997975e457825dcd76d,0x957df5f417ca5eed7ac5,0x982760618095fe97eb5f,0x88161c9863615184560d,0xd2630d8b46295896621d],#[0x163e58f363b58e763618,0x654d93b64b191d645d91,0x66d995661998065a1962,0xada1c68119e367099a16,0xda7f69e5a736949a3a68,0xabe6abdaa96a8da9d6a5,0xfd6bddae86b89aca6b11,0xa6c91b1e6c3db096c0da,0x6dd5b666d5db3f6ce5b2,0xf3dbc06ee9ba26e71b84,0x5dbff6fc1bea6f91bde6,0x9c4770e1c32708dc1d70,0xc867201c7a71adc5c715,0xc572d9ca77285c9b7231,0xb73d5cef73a5cda7351c,0x74d1d25747dd107405cf,0x5cdd6d759dd587525d43,0x11dbe76bdda07645d8b7,0x1dfd77b9ddf7765dd377,0xe4578d9e3078a9e1b783,0x7b79d5e6f79a5e5a792d,0xa7ad1ea57a7de997a29e,0x7ba9edb7b55ecf7b01eb,0xcc9f237c75f0e7bfdef9,0xa1f597d4df447cf9f387,0x9f8f7e25f837dd1f6e7d,0xfe07f45fc27ea9fa47e7,0x4380f602e8035ffe7fbd,0x4821607f819e058814a0,0x82ca0ac829a0a0826a09,0x40e0f483ba0df83420c1,0xa13c84b612784861128],#[0x618d85fa16f858215185,0x1d5873e1c986ea1ab869,0x1d883a20887e61f38792,0xc895a247890623b88b22,0x89ea27489ba268898a25,0xae62aa8a6e28c8a1a280,0x7230d8bfa2e68b3a2c88,0x23558d1a3378cc63228c,0x39d8e3a3888de63738d9,0xf78fc63e28f723c48eb2,0x4907a418904a40c901a3,0x919a457912244290ce42,0x272496921e48191ee475,0x4a4cc931a4c092c64a29,0x2526943a50893e64e193,0x56e957e559952a54494b,0x9b9632586960257a95d2,0x397525c596da5a796865,0x984e60497fa5f897a65e,0x92663a98d262e98a2619,0x6a69499f2676999e6589,0x26ca9b126be9abe6a99a,0x7009bea6f49b966df9b4,0x3f9ce67339c6e7159c3e,0x9e0677b9dd67669d3a7,0x9eba7a89e8a79c9e5a79,0xfb67de9f3e7c09eea7b4,0xb2814a0167ff9fe67f39,0xa86ea1a2859a14e84da0,0x8c8a30a8b3a292895a21,0x19a42a904a3d68efa35e,0xea5b694ca4f6937a4a29],#[0xa7429c1a6ca9a3a67698,0x916a36a89e9fda7ba9df,0xa2a99a9e2a69a96aa4ba,0x2afcab92ad5ab1aab7aa,0xb83adaeb53accab23ac5,0xefaf82bd1af0abb3ae4a,0x7b07ec19b04ec04affab,0xb19ec61b14ac4cb0f6c3,0x29aca0b26ac8bb1f2c6d,0x96cdfb366cd3b312cb5b,0xed15b43ed09b40ecf4b3,0xd4bb4f2d36b4c2d21b46,0x8ab5eed75b59ad57b546,0xb6eadb4b6bada8b666d,0xb79ede1b74adccb71adc,0x89ae17b846e02b7f2df6,0x96e56b942e41b8cae2cb,0x6e95ba3ee89ba0ee74b9,0xee6bb5eed1bb0aeb3bab,0x1cbc36f07bbe2ef2bbb2,0xbbd56f46bcdef31bc8af,0xbe52f8ebdfef70bd86f5,0xf4efcdbf1efb8bea6fa3,0x2ffabfd2feebfa2fd9b,0x3042c0cf024c07b00fc0,0x81c1cb06cc177057c12,0xaec2a3099c24f08dc21f,0xdc37b0d8c34b0ccc2f70,0xc42f105c3ff0f9c3cf0e,0x507132c4b3126c48311a,0x9715fc567153c537147c,0x319ec663189c5eb16bc5],#[0x1efc7831dac72f1bcc69,0x49c90f234c87320dc7fb,0x1ca0b273c9b725ec93f2,0xcb4f2c4cad72a6ca5f29,0xc93315cc1b2eecba32e2,0x8f35dcd5f351cd2f333c,0x33c0cec7399ce4f37bcd,0x408d00b3f3cfb73decf6,0x35d0bf429d08f414d03b,0xdd1df45fd14344ad0ef4,0xd2db4a7d263492d23347,0x36b4d4d33b4c8d30b4bc,0x1f4f8d3cb4ecd39b4e0d,0xb55bd533534d497516d4,0x5a3d67758ed5ff570d5a,0xd9d72b5c4d6fb5b8d6cb,0x6d8035fad7af5e5d77f5,0xd8b7627d863612d83360,0x9b3666d95f651d90b63c,0x67693da3767ed9e3672d,0x8402daeb6b4da9769fda,0x9840209840209840209,0x2098402098402098402,0x2c100c11640884040984,0x581806120c0858201060,0x38200c051000b04020c8,0x9040204c9420284020,0x21844201040192832504,0x250884120a84430a8482,0x2210402a110c20150887,0x90325064a08424a1494,0x82218418410418410401],#[0x8611042e150884840b04,0xc0a11082a11080a1208,0xc200b001600200542011,0x8443090542218482a110,0x208007042f640386120a,0x8141028207030406068,0x10000080410200c20000,0x3020008104000020088,0xc3010480040120002,0x20c0410000002000000,0x4040604100b04100002,0x4100083022204004022e,0x2008200041c082000020,0x2602122602410c017020,0x1110042418264040402,0x10002082002414002019,0x8902102c183089021804,0x52002008203040000208,0x1100420102080c10000,0x302003c10002080c100,0x83050008041080200401,0x80410400002019011102,0x1820000000100c80,0xc14182000c100440d041,0x4218406120401040c080,0x9230c500020104112020,0x810080c3051808ac1006,0x82083011102c30418410,0x12020000288181000604,0x21042030224048209041,0x5100429203245100431,0x21088111004220822404],#[0x18422048208924410480,0xc1810044090410082042,0x21820f04002020604820,0x82000010410782003c1,0x81086100010002085812,0x1048608016040c0,0x182010c1002c081a4810,0x9042a28200040c081812,0x208000040208300040a2,0x41000380041e08004048,0x10082058004000406080,0x30003040304000000800,0x81a03000c0e08141028,0x1510205050008125040a,0x400a834104001000814,0xe4a100000150400a8215,0x8200040408205040008a,0xa088b021604111204202,0x141090385044401080,0x208141028200040c082,0x40041791048302820104,0xa8204001800207030522,0x82220400902170400000,0x92820000504020800102,0x1000a001000090205040,0x181040c081810000000,0xa82220a840614102820,0x41000408002110206141,0x28585008401040a080,0x9410000a820040183021,0x40008200000881000a0a,0xa08000106040a080050],#[0x20e141030a0818507,0x1028206068208000181,0x1a080010002010408080,0x8106820504060800104,0x83010400000441000808,0x2080c04100c1c082000,0xc0060000b04061810200,0x200c04181286020e4b81,0x44c10804080810180820,0x4c24100001186020c,0xc1018602080000208000,0x10400006080000030,0x182618206040c0832441,0x2408901018601080090,0x2080030c02100410000,0x8101000a0800100,0x203040008000141000,0x10002000000000400,0x410002000c107820,0x40c9410102030c0010,0x1008212040a080001410,0x40408005040000a0904,0x200003040a08000005,0x80000400080000c10000,0x100000040800004000,0x80002c1000028200,0x80810002010482400800,0x10042c1583061604000,0x802060c0210041002008,0xc1810302650400000000,0x200106060c0818101820,0x416083c1000200040070],#[0xb04000800f0704100,0x20004000820504108020,0x18208000101080,0x8205041a082410000000,0x325044405081206080a0,0x48325040a080070400a8,0x20282220400482005410,0xa080a504006a9420601c,0x41001a08341000000002,0x8000000064a080,0x52840004000000830104,0x180020146a208040820d,0x10000000000080220400,0x88101820004020800000,0x200041000000200,0x200000a0415282000400,0x800104001800,0x10000001000110200001,0x5041a000882080000400,0x20006,0x200000000040008001,0x20000250800352c0020,0x8100020204020008000,0x201910010081000408,0x30102000010102020400,0x7040a0240060501000,0x40e08581028205040e08,0x5040c08200c250388020,0x88183038280040a0802,0x28242070a08181400216,0x22081410c0442402142c,0x6022141600106012420c],#[0x9042a080801050e0a08,0x241002a086012102,0x200004040028200330a1,0x204040000a08001000,0x410082000000010,0x20800000100000820000,0x203040008000040,0xe080070400000000,0x21104000000800004,0x30400000001028202040,0x2a08005040a080090,0x80150400a820014100,0x608001908200021040,0x2000000810002000c10,0x100000800100000000,0x400082000c1000608,0x102070400002000000,0x800000000704000,0x8000000000000040000,0x10ac8420000b0385042c,0x20104020b00100800d00,0x42008000041018042a00,0x40a08185040a081400,0xa10080028008581a0034,0xc02102c105820b068,0x84005a80105446100000,0xa104043314260020b50,0x8000005001000002008,0x8200341413001018a,0x20800100,0xa8216042a081c1000000,0x80810030086410c05c20],#[0x40000000e080c5040a0,0x1000000000408000003,0x80040400082000,0x1020000000004000]]
set_option maxRecDepth 16000 in
def g235H6 := limbs80 #[#[0x201010114000b01042c,0xc1204010d08040702,0x107112622030b060301,0x133050e032408050410,0x101163b000000110301,0x1e170700001707061c07,0x80f07061003142f030a,0x6606000429c0020c0314,0xe024984d00041908,0xc02e1222a123c122,0xb054e076007a0000,0xa89bb026300e83200000,0x2067700af4450000,0x8353e38c723490aa0000,0xb0bda64ac0700000b0b1,0xf096b0ac0050b4420000,0x487504a081110000501d,0x444000000002074601f,0xf089544600000000b0c0,0xa069321200000000,0x30121053f46e000070a1,0x10948087b001440d20a5,0x50440000904fc042e510,0x3043531d425a044d740a,0xc05cf062c08c80bea401,0xa4300000b045c0ba9091,0x7323e23200000000c003,0x2019e0a700000000f603,0x8512604bf5ac3113d02d,0x30812034000080a934bd,0x920030bc112ba44c206b,0xa02c41091051f1540000],#[0xa025505db036b03da28a,0xc0041409e086f0aea01e,0x9346f340c1327812c,0x2035c047040840b530af,0xa73e8080904e121fc03b,0x307120a4321a64667816,0xc0300000773db055573a,0x7078c08f13774022a095,0x505fb0580000001ab0a2,0x902a7326c2048046,0x407bf80f0469900dd259,0x3083a0c1743b0000f002,0x208d000030230000c06f,0x307f000070b6784eb028,0x15130000e0b90000,0x30ab309c0000309f0077,0x712a40210000a28ce090,0x50738039343290a004bb,0x80b4206cb05b707ef0b8,0xe801e068c029a0313465,0x153407e1b4f533e013,0x95149082e42c507c609a,0xa11810b3531f6211841e,0xa11d0000e04120850000,0x125c40595322b00c601b,0x843cc60b0000111a0000,0x90050000a50974370000,0xc09e90140000,0x9006d4a4740e738a0000,0x400f449b895a1175103c,0x273b102000b22139d040,0x40070000f0a314166038],#[0x8048000031178098,0xa21e300b8155e027f0b0,0x604aa04c000000000000,0xa09922280000802b0000,0x327de2a8047540725704,0xf00870330000,0xf049a14a42091227504d,0x5063c223601700000000,0x601800000000a08a0000,0xf0880324b0add221f052,0x4609d02f3468c08b6032,0x340f000094710000,0x611900000000f9586066,0x206ed06a7415273f90bb,0x4000801c108ee12d,0x1093f0118010903714be,0xe061f03f2311203a4057,0x7229040600000000,0x7064b21047033214,0x30bf3405c065005a1075,0x306d4097b402549fe740,0x569f60a89079109d,0xa2371092105e00003467,0xf01600000000c70940b7,0x6263607d6056e226,0x91534121c09b60a60000,0x44bc532e944100000060,0xa084b225603e6601181e,0x580b]]
set_option maxRecDepth 16000 in
def g235D7 := limbs80 #[#[0x2ecb9840887e12108110,0xaf2ea102216e5d02044,0x835cb22a1084df735951,0x10ddac4a9021da549504,0x427ebb2a40867d65548,0x810cfacba90213fdd952,0x30436eb1aa6084fd76d4,0x4c109faeca98219f5955,0x530433eb2ea6084ff765,0x594109fee4b28213f5db,0x420443f8a8840884ff73,0x1c81109faec902217e5d,0x4720443f898e40885f57,0x52c8110fd26590221fc5,0x5d720442fcb9e40887e9,0x1514c110fe242982217e,0x654d30443ec99260887f,0xf9654c110bf2e898221f,0xfc48630442fcbaa60886,0x5f9748c110fe2a318221,0x17e5d6304437cb2c6088,0x87f22150110fe242a022,0x21fc94540443f8a8a808,0x886f96550110df6c4a02,0x221fc546404437db2a80,0x885f97490110df2c520,0x2217e5d6404437cb2c8,0xa0885dd73d0110beae3a,0xa82213f5d950442fbb8a,0xaa0887f25154110fe2a2,0x4a8221fcdc550443f838,0x12a08877b5254110ef2a],#[0xa6a8221bed89504437cb,0xb1aa08877b5354110ef2,0x6e6a8221bed8d504437c,0xdb22a0886f96454110bf,0xf2c5282217edd1504437,0xfcba4a0886f96494110d,0xbeae3a82217e5d650442,0x27ebb264885fb704c910,0x9faed192217d5c63244,0x42eeb9884885f9701091,0x10afcea212215f5d4424,0x442fab8c84884fd76109,0x9109faed21221ebd0a42,0x2442fab88a4885f97014,0x4910b7ae829221775cc5,0x524427ebb0a4885be741,0x549109faeca92217edc1,0xa52442fab8ca4884ff76,0xd49109faed29221dbd4,0xdb52442fab8ea4885f97,0x75589109fee6b12213f5,0x5d362442eeb9cc4884ff,0xd6354d109faebb12213f,0xf5d9534433eb2aa6886d,0xf970d4d109feeca9a213,0x9f597534436fb1ea6885,0x4fd72d8d109faeda9a21,0x177dcd654427ebaec688,0x84ff7059510df6e0b2a2,0x21b71cd654427fb92ca8,0x884ff7359510dbee6b2a,0x421fa54b208427eb96ca],#[0x1087d9534c210bf2eb90,0x84217e5d5308437cb2a6,0xa10877b5254210ef2a4a,0xa8421de54d508437cb12,0xaa1086f96354210ef6a6,0x8a8421be59150842fdb9,0x2283086fb7654210bf6e,0xc8a8c217edc1518435eb,0xb2aa3086be6454610d7a,0xac9a8c217e5c3518433e,0xeb2ea3086be64d4610d7,0xdac4a94217edc1528433,0x5f322a5086bd6454a10d,0x9faeca94219f59552843,0x2fcb86a5084ff7654a10,0xd7cc9a9421af5935284,0x427ebb6a50867d65d4a1,0x10d7ac8a9c21b758d538,0x8433eb2aa7086be6454e,0xe109feeca9c213f5d953,0x38435eb26a7085f970d4,0x4e10cfacba9c21af9935,0x548435eb22a9084fd76d,0xd52109feecaa4213f5d9,0xb548435eb26a9085f970,0x359210d7ae2b24213f5d,0xd5648435ebaac9086bd7,0x73596109fee4b2c21af9,0x585510827fba2cb084ff,0xe6354420dbac6a8841bd,0xf5d9510833eb2aa2106d,0xf561d44209feeca88413],#[0xb798f510836eb1ea2106,0x4fd76d4420cfacba8841,0x1bdd4d610837aa9ac210,0x6f67558420deaeab084,0x41bdd4e610837aa9cc21,0x106dd6354c20bf6e0a98,0x841af991530835eb22a6,0x6104fd7654c20cfacaa9,0x9841b758f530827fbb2a,0xa6106be64d4c20d7ac9a,0xb18413f5db530833eb2e,0xac6106dd7558c20dbae8,0x6b28413fdc5650836f3a,0x8aca1067d71594209fee,0xe6b28419f5cd650833fb,0xb92a09076d5254120cfe,0x6c2a82413f5d950482f7,0x5292a0907e95254120df,0xd0e4a8241ded4950483f,0xbca9aa0907eb7254120f,0xdf6c6a8241ded4d50483,0x2fdba2a0906fb6454120,0xbdae5a82417e5d65048,0x82fcb80a2904fd768c52,0x209faec28a41775cc514,0x483bba8ca2904ff76545,0x520bf2e1a8a413f5da51,0x34827ebaec2904fd76d4,0x4d20bf2e1a9a413fdd95,0x634827ebb6a6905ed72d,0x595209faebb1a413f5c7,0x5654827fb82ca906fb70],#[0x1d95209fee6b2a413fdc,0x49508837cb0aa1104fd7,0x5354220ef6a4a8441de5,0x58d50883bda9aa110779,0xb7454220df2c8a8441be,0xd585518837dbb2a1105f,0xff76546209faeca8c41b,0x3f5db51882fcb86a3104,0x67d6554a20bf6e0a9441,0x19f59752882fcb86a510,0x67d6554e20dbac6a9c4,0x413fdd9538827ebb2a71,0x1067d65d4e20bf2e1a9c,0x4417bdc9548827ebb6a7,0x9104fd7655220d7ac8aa,0xa4417e5c3548827fbb2a,0xcb104ff71596209faeda,0xb08a13fdd1658827fb9a,0xac4286f57458450deae4,0x128aa17edc15154376b8,0x8c2a86f76194550bf2e,0xe6b0aa1771cd615437ab,0xb94c2a86f76198550bbe,0xae5b0aa17b9ca61542f6,0xfa9ec2a867d53d85509f,0xfae9b0aa13f5cf615433,0xbc382a4a85fb70549509,0xbf2e1292a1dedc152543,0x2bebaca4a86ef6294950,0xbeae2312a15f5cf5254,0x4376b10c4a85f6711895,0x50bbce6312a1775cc625],#[0x542df3a0c4a85bd74189,0x9509fae3b12a1bbd8a62,0x1d427eba6c4a84fd73d8,0x87509fee6b0ea13fdc96,0x62d427fb8ac5a84ff745,0x548109fee8b16a13fdcd,0x5530437ebb2a4086fd65,0x259410dfaeca9821bf59,0x41204437eb9aca086fd7,0x5248110feaa290221fe5,0x5d5204437eb2a40887ed,0xb50c8110ff2a1902217f,0xb54b20443faa8e40887f,0xfd75c8110dfacb90221f,0xfed4f20443fca9e40885,0x7fa65c8110ff2cb90221,0x1fe54930443fca126088,0x87f9544c110ff6a49822,0x21fe54a30443fdaa2608,0x887f9548c110ff6a5182,0x221fe54140443fdaa460,0x887f55150110ff6a0a0,0x221fe545404437eb2a8,0x80887f97150110ff6a2a,0xa0221fe54940443fc992,0xa80887f96250110ff6a4,0x520221fe99540443fcb2,0xa480887fb5290110ff2a,0xa1a0221fed5240443fca,0xaa680887f551d0110ff2,0xaeba0221bf59740443de,0xea92a0887f55154110bf],#[0xfac4a8221dfd4950443b,0x7eb22a0885ff7254110d,0xdfacaa82217fdd150443,0x3fdb8aa0887f97154110,0xff464a8221fe4c95044,0x43fca12a0887f8425411,0x10ff684a8221fe909504,0x443fd292a0887f952541,0x110ff4c4a8221fe58950,0x443fcb92a0887f87254,0x4110ff6e4a8221fe9c95,0x50443fda1aa0887f9435,0x54110ff2e6a8221fe54d,0x150443fcaa2a0887fb73,0x454110ff2c8a8221fe95,0xd150443fc3a2a0887fa6,0x7454110ff4e8a8221fe5,0x55250443fca94a0887fb,0xd62d4110efaa5a8221fe,0xf59350442feb96a0886f,0xfd644c910bfae9a8221b,0xfb54a324437eb2a64886,0x5fd758c910dfacb19221,0x1bfd94424437eb288488,0x85fd7610910bfaea2122,0x21bf58d42443f6a92848,0x886fd6550910dfec6a12,0x2217f5d5424437fb2a84,0x4887ed5290910bfaeca1,0x1221bfd96424437eb2c8,0xa4885fd7690910bfaeb2,0xa9221fe1c152442febb0],#[0xaa4885ff7054910ff6e0,0x2a9221fd9c552443fab8,0x12a4887ed6254910bfee,0xc6a9221bfd8952443f73,0xb9aa4886ff6354910dfa,0xea8a9221df55152442ff,0xfb22a4886fd6454910ef,0xfacaa92217fdd1524437,0x7ebb2a4886ff6554910d,0xdfceca92217f5d952443,0x3f6b14a4885ff7654910,0xdfecb29221bf5965244,0x42febb4a4885fd759491,0x10bfae3a92217f5c3524,0x4437eb1ea4886ff62d49,0x910bfae7a9221bfd8f52,0x24437fb26a4886fd64d4,0x8910bfaeda92217f5d35,0x62442ffba2c4886fd645,0x58910dfccab1221bf595,0xd624437eb9ac4885ff75,0x558910df8eab1221bfdc,0xd5624437f3aac4886fd7,0x7598910dfacb31221bfd,0xdc953443fcb82a6885fd,0xd7654d10dfacaa9a217f,0xedc165442feb96a6886f,0xdf7359510bfee4b2a21f,0xbf1c9654437fb82ca887,0x6fe7259510dfae4b2a21,0x1bf5cd654437fb92ca88,0x85fd7299510dfee6b2a2],#[0x21fed5130843fcaa2610,0x87f95154210ff282a84,0x421fe54950843fcb8aa1,0x1087f95354210ff2e4a8,0x8421fe55150843fcb9aa,0x83087f55150610ff2e8a,0xa0c21bf59541843deaa2,0x2a3086fd6254610bfaea,0x8a8c21df55151842ffb9,0xa2a3086fd6454610efea,0xc5a8c21bf59551842ffb,0xaa6a3085fd72d4610dfa,0xae9a8c21bf59351843be,0xdb82a5086ff5258610bf,0xfacaa94217fdc552843f,0xfeb8ea5086fd7654a10d,0xdfac8a9c21fe5c153842,0x37eb2aa7085ff7454e10,0xdfac9a9c21bf5d95384,0x437eaa2c7085fd74d4e1,0x10ff2e0aa421bfd51638,0x842ffb9aa9085ff71552,0x210dfaecaa421bf59554,0x5842feb9ea9085fd71d5,0x9610dfae4b2c21bf5c56,0x510837eba2cb086fd735,0x54c20dfaeca8841bf595,0x1530837eb22a6107fb70,0x654c20dfacaa98417fdd,0xd3530837eb26a6106fd7,0x7359420dfae2b28417f5,0x54950482ffb8aa0906fd],#[0x93154120dfacaa8241fb,0xe50550483fd18aa0907f,0xf95154120ff482a8241f,0xfe58550483fd28aa0907,0x7f87154120ff4c2a8241,0x1fe9c550483fcb8aa090,0x7f97254120ff6e2a824,0x41fe54d50483fdb92a09,0x907fb7354120ff2e6a82,0x241fe5d150483fcaa2a0,0x907f95194120ff6e8a8,0x8a41bf59531482feb8ea,0x62906fd658c520feaa31,0xa8a417f5d851482febac,0xaa2907f56154520bfee0,0x6a8a41bfd8551483fb30,0x1aa29077f5354520efaa,0xcaa8a417fdcd514837fb,0xbb2a2906ff6554520dfa,0xceca8a417f5d9514837e,0xab0ca2905ff7654520df,0xfecb28a41bf59651483f,0xfebb4a2905fd7594520d,0xdfec3a8a417f5c351482,0x37fb1ea29077d53d4520,0xbfaeda8a417f5cf5148,0x837f32ac2906fd655852,0x20dfacb30a417fdd5614,0x482ffb8aa6905fd75985,0xd20bfee8a9a41fb5c953,0x34837ebb2a6906fd6554,0x9520bfae9a9a417f5c75],#[0x65482ffb8aca907fb705,0x59520df8e2b2a41bfdc1,0x5654837f38aca906fd71,0x359520dfae6b2a41bfdc,0x4550882feb8cca906ff7,0x5254220ff2e2a8441fe5,0x54d50883fcb92a1107f9,0x95454220ff2e6a8441fe,0xfdc951883fcba2a1107f,0x7f5454620efaa8a8c417,0x7fdd1518837eb22a3107,0x6fd7654620dfacaa8c41,0x17f5cb518837eb16a310,0x6fd64d4620efaa9a8c4,0x41bf54961882feba6a31,0x106fd5458620dfea4b0c,0x4417fdc5528837faa2c3,0x7105fd71d4a20dfacaa9,0x9c417fdd1538837eb22a,0xa7106fd7654e20dfacaa,0xb1c417f5d3538837eb26,0x2a9106ff5458e20dfaa8,0x4aa4417fdc554883fcb8,0x2aa9105ff7355220fdee,0xe3aa441bf5d9548837eb,0xb8acb105fd73d5220bfa,0xae6b2c41bf5c9658837e,0xfb82a2a86fd7459620df,0xfec4a8aa1df54951542f,0xbea9aa2a85ff7254550d,0xefaa528aa1bfd8d51543,0x2feb94a2a86ff6294550],#[0xbfae928aa1bfd925154,0x437eb10c2a877d521855,0x50dfac830aa17f5c8615,0x543fdb82c2a85fd74185,0x550efea4b0aa1df54961,0x15437eb12c2a86fc6258,0x8550dfec4b0aa1bf9896,0x61543bea9ac2a85ff725,0x58550dfac6b0aa1dfd4d,0xd61543ee39ac2a86ff63,0x458550bfee6b0aa1f7dc,0x91615437f322c2a86fd6,0x5298550bfee8b0aa1bfd,0x58a61543bfa94c2a877d,0xd7298550dfec530aa1bf,0xf5d2615437fb24c2a85f,0xfd62d8550efaa5b0aa17,0x7f5cb615437f316c2a86,0x6fd63d8550efaa7b0aa1,0x17f5d361542feb9ec2a8,0x86fe52d8550dfaa5b0aa,0xa1bf9cb615437eb96c2a,0xa86fd73d8550dfaa7b0a,0x2a1bf9d3615437eba6c2,0x4a86ff6354950bfee0a9,0x92a1dfdc152543beb82a,0xa4a877f6354950efac6a,0xa92a17f5c652543be3b2,0x8c4a877d63d4950efac5,0x2b12a1fedc162542feb8,0x1ac4a86fd6358950bfee,0xe8b12a17fdcd625437fb],#[0xb8ec4a85fd7198950bfe,0xae9b12a17f5cf62542fe,0xf38ec4a86fd71d8950bf,0xfae9b12a1bf5cf625437,0x7eb92c3a86fd7058750d,0xdfae6b0ea1bf9c961d43,0x37f3a2c3a86fd7458750,0xdfae2b16a1bf5c162d4,0x437eb9ac5a86fe7158b5,0x801600160001bf5d162d,0xe0032804a006e00b0010,0x1a60300056809e011601,0x811a0216040007880e20,0xe00b2815a029604f0094,0x38e06e00d28192030e05,0x8222041e07f00f481da0,0xf0134825a04960900116,0x5860ae01528292050e09,0x830e06060bc017282d60,0xa01ac834a06760cc0190,0x7a60ef01d0838a06f60d,0x8432083e10301f883e20,0x2023c846a08be1140220,0x9be134026084ae093612,0x85360a46144027e84ea0,0xa02ca85820ade15702a4,0xc0617c02ee85ca0b7616,0x86620c9e18f031486160,0x10358869e0d1e1a0033a,0xe661c7038486ee0dae1b,0x877a0ede1d903aa87460,0xa03e687ba0f5e1e703c4],#[0x6e209040c880e0ff61f,0x888a10f621a043088521,0xa046a88c6117622b044e,0x26e24a048c890611ee23,0x898a12ee25a04ac89461,0xb04ec89ca137626b04cc,0x46e289050a8a0613f627,0x8a8e14f629a052a8a461,0xc056e8ace157e2ac0550,0x68e2ce05928b1216062b,0x8ba2171e2df05b68b5a1,0x405fe8bea17ae2f205da,0x8de31706248c36184630,0x8cc2196632806488c821,0x806888cfe19de3380668,0xae635906aa8d421a5e34,0x8dca1b6e36906cc8d861,0xf07148e161c0637c06ee,0xd363a2073a8e621c9e38,0x8eee1dbe3b4075e8eae1,0x607a48f321e463c50780,0xf5e3e907ca8f821ede3d,0x8ff21fd63f707e68fbe1,0x40820903220464050800,0x14e423083e906e20be41,0x910221ce436086490b62,0xa08ac913e22564480888,0x37e46b08ce918a22ee45,0x920623ee47b08ee91ce2,0xc0930924e247e48b090c,0x57e4ac09509292250649,0x931626064bd097292d22],#[0xc09ae9352267e4cb098e,0x78e4ee09d4939627064d,0x940a27fe4fd09f293d62,0xc0a2a9446286650a0a0e,0x98652c0a4c948628f651,0x951e2a0e53e0a7494da2,0x10aba95622aa65510a98,0xbce5750adc95aa2b2e56,0x96462c665880b0695fa2,0x80b4a96862cf659b0b2c,0xdbe5b40b6096b62d565a,0x971e2e2e5c30b7e96f22,0xd0bb4975a2e965cf0b96,0xf6e5ea0bce978a2efe5d,0x97f62fd65f80bea97c62,0x10c1c982a302e6030c00,0x12e6210c3a9866309e61,0x98e2319e6300c5898a63,0xc0c929916321663f0c78,0x2e66590caa994a327664,0x99ba335e6690cc899823,0xa0d0a9a0233e66780ce6,0x4f669b0d2e9a4a347668,0x9ac2356e6ab0d4e9a8e3,0x50d809af235ce6b70d68,0x6b66d40da29b32363e6c,0x9b9e37266e10dbc9b6a3,0xb0dee9bd2378e6ef0dd6,0x87e70d0e109c1237f66f,0x9c7a38de7190e2a9c4a3,0xf0e589ca639267230e40,0x9fe73c0e709cd2398e72],#[0x9d423a7674b0e909d0e3,0x30ec29d7a3ad67570ea8,0xb9e7710eda9da63b2e76,0x9e0a3bf677e0ef69dde3,0x70f289e463c7678b0f0e,0xd467a50f449e7a3cd679,0x9ee23dae7b40f609eb23,0xc0f8e9f163e167bf0f78,0xee67da0fac9f463e7e7c,0x9faa3f367e50fc49f7e3,0xb0ff09fd63f967ef0fd8,0x4e8071006a0063fee7f,0xa05e409e811101ca02e4,0xb104ea08e410681d1036,0x1c68361064a0be416e82,0xa12a4236843107ea0f24,0xe10b6a15e42ae852109c,0x37686c10d0a192430e85,0xa20643ee87a10eca1ca4,0x51122a23644568881108,0x5268a1113ca26a44be89,0xa2d645968b0115aa2a24,0x9118aa30645ee8bc1172,0x6c68d611a6a33e465e8c,0xa3a2472e8e311bea3724,0x911eca3c647768ed11d6,0x83e9051206a40247de8f,0xa46a48be914121ea42e4,0x8124ca492490e920123a,0x9be9331260a4b6495692,0xa51a4a16941127aa4e64,0x912b0a5524a8694d1294],#[0xb3e96512c2a5764ace95,0xa5da4b9697112daa5aa4,0x8130aa6064bf697c12f2,0xca69931320a6364c5698,0xa6824cee99c1332a65a4,0xe1358a6aa4d469a51346,0xdd69b8136aa6ce4d869a,0xa72e4e3e9c31382a6fa4,0xf13b6a75e4e9e9d2139c,0xf769eb13d2a79a4f169d,0xa8064fee9fa13eca7ca4,0x61424a83e5066a09140a,0x13ea241440a87250c6a1,0xa8ea51aea331460a8ae5,0xd1494a91a5216a40147a,0x306a5d14b0a9525286a4,0xa9ca5376a6b14cea98a5,0x61504a9fa53e6a7814ea,0x4aea92151eaa325446a8,0xaa925516a9f1536aa625,0x71568aac6557eaaa1550,0x62eac3157eaaf255ceab,0xab4e568eace1596ab225,0x515c2ab7656deada15ac,0x7aeaf315deabae573eae,0xac0a57feafd15f4abe25,0x61626ac3e585eb09160a,0x936b241640ac7658ceb1,0xacda599eb32165cacaa5,0xb168ead0e59f6b3c1672,0xad6b5716a8ad465a76b4,0xada25b36b6416c0ad765],#[0x13100adda5b96b7016d8,0x86084c4021013084c402,0x505121118445448404a5,0x41121014450448402002,0x141120c5504444841511,0x25114112104495044841,0x504431514110c1450443,0x4110c945044314110854,0x1114150c460448544251,0x1440484131008584c403,0x613104c4020812100c20,0x6130e02184cac416010,0x48006130e0218ac4c480,0x416a264101021904440,0x88504041810085048444,0x2100c608840316100830,0x21210085a8990404081,0xc4c484150c221010544,0xc5a88301841210081b,0x1643040610484020c131,0x4048316a224101030402,0x2100c54104031210084c,0x86c51412103448403a42,0x61615040210149054403,0xa2251014040192881894,0x66406150d90544036400,0x151225109414885c1848,0x31522100c2018141c406,0xc144021525100c609440,0x60510548840315a5100,0x28006119000544040d0c,0x820512100c1440483642],#[0x90944040c22151010404,0x4141040412c52b101058,0x201440484c5081012104,0x3142090444c508241110,0x13049490444170824111,0x41110204844305082411,0x251110201448444c5082,0x22511102048944440112,0x25241113044894444c11,0x2c3011210204894444c1,0x484430403170c100c22,0x201448444c1122511102,0x28800589451501122510,0x10404161504020325189,0x84440804030706144414,0x10084030512100c5c4a1,0x40402100c94402051008,0x42152225101010084060,0x100840616152510111a9,0x84041105041010585494,0x161018582a5860994100,0xc585418100c086040210,0xa5040210104010f0b100,0x48315081211101008403,0xc444021811100c4420,0x15110c5c544844415111,0x31815101110544844312,0x8544031015110c405444,0xc045448309c11512108,0x6100e943448404001615,0xa510130c329688404221,0x429442210150c5854403],#[0x10c54402a510130c3288,0x81111210144448312011,0x4441512110e94444c3a5,0x45440112171110540448,0x444c38111a5121004484,0xc94484432512110e94,0x44101032944440405111,0x5041110105444403a511,0x41110150c1060444041,0x40311a54410103046944,0xe0448404111510104494,0x4644841503011210168,0x28e06944840115120c0c,0x10359448404030115121,0x511958d04484650c1110,0x10100444485446341126,0x3100c0c0448544041115,0xa540431312944c403051,0x4c4031513100c544c403,0x312944c403a513100e94,0x13100c544c4034043a51,0x48265101195920840415,0x5046513100d944c4036,0x430828280651411960a0,0x32950840405a4421010,0x10569108404a54442101,0x1011086040415044210,0x1010310a94404a442a51,0x510129108544044442a5,0x82101194320840404421,0x513100d9209944046564,0x31513100c1208544041],#[0x544041564821010544c4,0x448544432512110d9208,0x14544844317150112111,0x14484441202001125,0x15080054443151225111,0x4431525110c609444307,0x2110c4811215110c5448,0x513100c5c4894444151,0x4c4031325100c4c94403,0xc4c944030403160c94,0x3012518085494305131,0x11118100448443171504,0x461725110c5494443040,0x30510120c5c549410044,0x4485c444171108044844,0x4443171507040301180,0x3208544040112110c10,0x11104454483171512111,0x15110c4054443181510,0x45c54315120818544831,0x541008404c205a410102,0x1008544030402161010,0x1112130c5c4830402151,0x31115120c44544831715,0x444041511100c144440,0x40544430410181110541,0xc041044544041125100c,0x84150301121016844838,0x4544841512080c04644,0x445440404021015100c,0xe144840303011215101,0x540160e1448403128510],#[0x5840215100b08544031,0x15100b144020fc510111,0x46c510120c342314404,0x44021510085c541c100c,0xc083054515040210105,0x4544844515c340171064,0xc54484430540170c5c1,0x1105c541448445151211,0x100c2048544441815051,0x8121511105d90443c512,0x44081215111314484030,0xc0861512110c2090544,0x84150401111058541810,0x4040403001610540c044,0x5c40302001610100858,0x485c40401111710100c0,0x50c541c20240150c0c04,0x42421507085424203401,0x22060e881c1830607085,0x183170108590e0008407,0x280060c1812206089488,0x88831780060d0e040830,0x220818ac281412b0e041,0x44222814109120448206,0xc24185030981410c18,0x182410c081c18222410,0x40c0608301820c06083,0x30182160c060c590e001,0x20c5040ad2c4c50c0608,0x24080610881848322061,0x4183240608589040307,0xc6604901840781060c8a],#[0x2524100c944022481060,0x8641822504100c10182,0x3068009081a0030580,0xc36001434215060c2016,0x100858550c1840580060,0x8842581062b101504215,0x44832522811010960418,0x8a0590425810622101a0,0x1894883170622251018,0x100c8894403072508061,0x522410c5e141d0442215,0xd9040281060888005438,0x82101508604021825100,0x3430941840625640c641,0x541101a1495904251008,0x888341150a14402190c8,0x80d081820c19060c5c1,0x18380050d0c5c1828005,0x7220a042c2800b086430,0x851722060c0e040831,0x5c1842502100c94110c4,0xe084c482080708201c,0x438182430e08388c1831,0x10e0408422044c482060,0xc20807085c1820206081,0xd04008834106220c201,0x840061048205c3174001,0xc1810807060c5c002170,0x623170c405c20622050,0x17084c11312090c5c183,0x831712060c5c1848381,0x30c19110c30602090c18],#[0x1c18203001904217242,0x60c9418083254306021,0x582011508201c21722,0x6a50c44144030522060c,0x81838105120c60182110,0x4588c5431912060c144,0x148821025220c2048212,0x4041004444020807250c,0x6101411210050c201448,0x17250840942c30805070,0x10049440218060860402,0x860c5488210060c5c183,0x40082410b0854402a523,0x40310045409043100b08,0x20c09082411722085854,0x50c24581830541080034,0x42428018150c1c117222,0xd0854301c31915800c5,0xa1204003150d0834145,0x434481084e140030716,0xd100058381160c0c1512,0x170c16041c31640250,0xc64002810ca50c64113,0x31300170c89002070506,0xc4c00583150708090054,0x44000c60243031815090,0x943031509080d0054318,0xc05090c2464219000826,0xc6400219000864544830,0x8400160c305420440150,0x1c216091506121060003,0xa1150c5430215090854],#[0x80c60243034004541824,0x43150909028c54300141,0x8541821402190c24329,0x1c32580081e021431509,0x782081e0820782085c54,0x62507101c94216044810,0xa144440785081c942080,0x83150708541854208581,0x26150841825110c00550,0x91208644822500150c60,0x10a041c5821604485421,0x2080608581c203010804,0x50c1c125080706105808,0xc58381050e0484307210,0x10c1c0421643070c1c8,0x1624230c1d110c30725,0x430725010c1c2018300,0x21508201820716081c94,0x840141c3430484141c30,0x48422521085c54218070,0x162508940420806250c1,0x1104601c2181108601c2,0x420704641c2071608441,0x1211010c041150708148,0x45821511084410104041,0xc1c30225082418216048,0x15428010241182508545,0x4843160008550830319,0x644000c5818303810512,0x41c31543060c05005431,0x6050c0d101001708181,0x81831742060c0864003],#[0xc3014183190c060c15,0x2100160c5d0094385210,0x80d0054318000860302,0x30219000c24143031509,0x4544830c05090c250864,0x80b00219024100106,0x58215120812090054419,0x5070c542418300180800,0x500315420c0c54242171,0x2089005444022800c560,0x523400a104011621070c,0x1c32240150d008a0031,0x80401034302401508182,0x160030122150e1410522,0x10608585418324150822,0x884442450b100c584421,0x1606220c2054443210b0,0x4015144011615100c401,0x584022386084010a4523,0x9030d4008403c2242108,0x20108548824022085884,0x4084810608220c885422,0x50e001080416005430d2,0x30a8008145440317221,0x22005431924150c60544,0x54402150408542801508,0x310150810542151008,0xc545d0031511085609,0x431505110c8824205174,0x85c541c3060809005c5,0x31715070c20845431811,0x711082c54211045c8884],#[0x88c185442108085c4821,0x110c64544831815110c5,0x54482151108885420115,0x31016085c5821516100c,0x7070c581191608605840,0xc443401708485c583151,0x1917120c605]]
set_option maxRecDepth 16000 in
def g235H7 := limbs80 #[#[0x24160002e0e000300000,0x12130100402000101802,0x43811001480e0103028,0x981c262d010040c01018,0x906808042430004062d0,0x4001f804120000008120,0x10240600c000e0c8243,0x81000050080802012e02,0x141a0805004020702,0x14030080c020e818082d,0xa2705854283e0700026,0x200611091300e0201000,0x90008209020080808090,0x50015004040e01c04002,0x20c048542e0e03814000,0x40c02088848a00000001,0x8380e0201834041e0186,0x1004060002028343500,0x171087456180e8401a07,0x9a1b010044c0b0101800,0xc0102858181c0d008,0x84c56180103402051c8,0xd0588464000042c00060,0x6c030841615048686a2,0x80417288081a0d188149,0x8045e0b1812916290081,0x80828152a07004391e,0x603804d6083782c8c00,0x481d0280034020007006,0x403800398d0580216001,0xd0440a050a81c1823108,0x81883024040d00400641],#[0x67b000e4acae30078201,0x4400f028000c62021ec0,0x7c3a0380432000005,0xa8852c1a0782c2e1d02,0x682c38e51a1401001,0x1a010501856001c80c64,0x94e2000499802d50101c,0xe41709000db11228,0x500004c4000005414100,0x40f14b68aa002499c100,0x2a150289c60150dc042,0x8147a1c678708e010800,0x482c4abc1aa4c8c0303,0x11040840c03010006828,0x5a06000280e111a00010,0x3420050200c020b00064,0x789400d40d0008622040,0x81985dac0004929e0123,0xb3f15840741f1a0502e0,0x4025a010015c23019d00,0x8140cdf03011ff901c17,0xb982c0e002a01d824111,0xab143be41e5905db21ea,0xd022e010e981d7b10a,0x480000124433c956000,0x1c0948811ca2,0x2928df118ec0b9d490a0,0xdc806a650f3a0eb40000,0x8a503040000000000c88,0xcc580eaa057ba477e80,0xc05c280c665015e04b44,0xc48d891b69084860588],#[0xd5d0dad810f706126688,0x41a51a53828500001281,0xce80000301203004f60,0xc02c31ca4290e800001a,0xb8080c0200f021db0010,0x20c84700000503fbf062,0x1a09026400003103d520,0x66400d8f408c881bde0,0xe054370c9d002c1030d0,0xd9021b023bf41b3b03c3,0x38d234ae10be91a4b10f,0x3d3e17d8e0b3741a6212,0x39af543d2025888089d0,0x121ab318c2a5f9c0663,0xdea20d0000160c690545,0x9f590d4e2754e0596543,0x21e80b3204400000288,0x382d980761e80d84,0x4e1a680310466d86c6b8,0x480000480f8905ba2495,0x1c70043303ce00000a6e,0x2305c0a080000f026510,0xe1144000078033604978,0xd0855688d980000a317e,0xd1001211d02581e9b02c,0x6642049c0000203be600,0x70420003c4d88000024,0xb230ca80c18110800003,0x49627152bbf110f8109f,0x20298c908d00503999,0x8bad24ca0000151ad000,0xa30c10077a092780c290],#[0x700b100000a22c000001,0x6805e600ca00000c078,0x83e83fd00001c05d8000,0x14bc9b490231ee633d81,0xc6180000a0716e0eae4,0xe011f99915707bb8c16e,0x340d5a82a00000028ca,0xb490015000006345c000,0xee3c152298cde168468,0x6465e8057e411fa01342,0x240cd9c1699037090364,0x2c6428180f140199924d,0x899c2372c60058116551,0x429e2264800006203220,0x7232a00001c2167828e5,0x9f052c010aa0d58cb9c5,0x25d0508e0b1b81b23abb,0xd07ac20cc310b4903,0x289837360c20a9008f80,0x80faa21d32049ac5a40,0xe588a9524c9e23cec45b,0x6cd016cb087d209ddc08,0x28178a042741102cc,0x81cca01c101120c0b200,0xb4860e8089440c240380,0x30016de832700001401f,0x181bb102cef7283ca2,0xe4e40000512af305ac00,0x4879b8c86a83d8835658,0xae04d00000000000001c,0xb8000008012000009082,0x724e0391886580000803],#[0x14ae0e0c0000010c750,0x30936881b83,0x20000020784000028a24,0x94134060321406e6235,0x7133ace768010d499,0x19e731ace05d0000000,0x47507d300801481e2,0x110ca37293a0535014c,0x8f001644041fee6eb54c,0x10b8919935516203e700,0x17ce107400001a018dc,0xd89b80000141e91270d,0x380000003b3000016078,0x58480f1b02922215ce06,0x8b0000030275100cf60,0x1003d00000e,0x8a42dc00004837300000,0xb300b2c110842380d413,0x62400b500000180dbb00,0x31840000342023021c30,0x10801c00003488b3,0x15012b48115045580000,0xe400000c41574405f905,0x26811108c0ce2c03d103,0x434f330e400000000070,0xb42e260e1810a28,0x6cb9d700000000014227,0xfd0bb8120027a0adbc06,0x91d402eb340cc2030380,0x844f88fca081a843bac,0x20122c110728d01,0xbe485f5910a00000cc6c],#[0x691c881610c4717d6001,0x6ddc174c80f38320a00,0x806ea9a2dc03668,0xb002d9c8ebe021b40822,0xb800001049188073857f,0x5e6000014055183a1b05,0x21c660475983bd800680,0x705c240e5c000000000a,0x7b11ec680e48103103f3,0x11380e6a0960c87f7023,0x502848005945ca781,0x98be90810005be48af00,0x80000611efc073800005,0xd8000004009201bb9449,0x58180080ed00025dcd,0x13a00000973fc88e9000,0x47f700e9008822804c8,0xe4002502efc24b4a09c7,0x9f40d3b8447c334d40f2,0x12241c4a816ef216a20a,0xc04c1621a06464063a1,0x60e700000718c152389e,0x4041524900680b5c0736,0xfc2091400006808ce185,0x7f0c04960878782d0903,0x11a3ca1f441e8e0020a0,0x1c09ed80eb090db5,0x8902c0e8d8bc0bce1095,0x130318e0000140970990,0x428227b0c4ab40472203,0x4224284fb8c144000002,0x90281b03da000014834b],#[0x69832620080283edc1ef,0xeb914c4079f24982519,0x14aa21ab8032cc00d400,0x6416b107300000a0bd10,0xd0ddf00000807a8642ed,0x3e4201e4214f0481487c,0x194c0a309217901b1ac9,0x2e027f002e0000088,0x628be8112fa887951140,0x2443aa419549078d02b7,0xb841081800829011b207,0x6064221641fe510c3a24,0x70b702400816d001a070,0x74471c1077d04d983546,0xe061600003c871603c6,0xa600001e0ab2416c0000,0x95b673c30030a0846b13,0x182ee0,0x6907b6250a60f73c07a8,0x4c190f0000148cf40000,0xc6800000000040560492,0x8935042b21179210c701,0xc8bed927030740805c84,0x9c136483c48088400002,0x718c69da15d64098002b,0x113d08c80000055c4e0c,0x8852614060329804a7a0,0x20221409c603e6205542,0x82237d8155b01120240e,0xf9c064941f793139924a,0xa0501c02039283a2230,0x379940405013998222f0],#[0x223fec0ded401b68131c,0x802da4235c01f672426,0x294119960cdf05a58000,0x2a30102184acac940e82,0x66454000010c6528,0x3ba32107d7e23f408d50,0xe218d7511db022a3449a,0x682004f564a8c63251c2,0x483f5806e4c0ed68c,0x90a39bfb240200d540,0x2c1d538319a023600003,0x2f010858017004482664,0xef281fc80000c06fae03,0x54b416f0a042a049a00,0xe0ad7c92be90ba803024,0xa000018061f936300001,0xdaa079c017de8c06a054,0xa03d049edd103eb81,0x2c0ea0000000,0xc078fc0af000001b9400,0x6e0209a227fd18698235,0x8b0000022688c131ea1f,0xd02bb00053845138a,0xcbc500001406be00b800,0xb81289256660d3c00003,0xde8267310fc6449cc116,0x8b68041000000000219e,0x60032000008016cc1,0x113b8391231b5c02500,0x1c1337841320195c075d,0x55c0e99822f000000000,0x41bf8000044273243],#[0x0,0x20136944709914105260,0x300676804cfa043942a8,0x780a0400000000002031,0x6c56e529c0fe40228408,0x38ca01ca8007e008ab0,0xd11e128918c074790157,0xb8080c80de4421fe823a,0xf0035d2f1000005020,0x1fc04f5e090c0000000,0x18ce71014e0fc58c6c50,0x7803400000000028478c,0xd2184a266901fa,0x44703a470702a05f8000,0x72a08d8621906641b55,0x1152810c91322000018,0x800007233cb230200cb8,0xcfc219d013c50672c040,0xcbf0077f39ffa2368c22,0x41c80000000016045d80,0xe0730000010175d23f80,0xc0000040ca0836100001,0x9730d76ea35f9054,0x11e6038b91bf41192000,0x42200000c11e0000070,0xc014de22be414cf043d9,0x19321c12534000042057,0xdf000000000041605023,0x50816c03c99444f81,0x400d800000000000,0x8427403de20a5088600,0xf901a5904240000241c7],#[0xfb702809058200002c13,0x44c080510000020f78c1,0x501338270f07fca4b48c,0x1833c412098062d,0x4ed1bee9053000000000,0xf0a08c6482bba328a046,0x1d025a8023504c3c0,0xf2f0400000190c000000,0xe001a701a1c82f7e000f,0x6c26f1f1025102c7212c,0x327c029202007802c725,0x6deb00e4c186482b950,0x7089400246088a8a0763,0xa101e3602ddc09d03854,0xf6f03bce076a0014783c,0xd06b6a03ef0464101,0xa058104ae846115cde00,0xd899f3089b28c9a01540,0xa10015a013e010c8003b,0x9fb035df06e3a0bd740d,0x88e08070b643ba05e8c1,0xc17b703d7f0489e055f0,0xb9915e803a4010e00d03,0xfd52113001e3022b20a1,0x9f58008a9196c4673244,0x6c18056d126f50753e0,0x8c14c00000215e900f90,0xa207a980e3ea324904be,0xb8a42e6011180000021d,0x4a4e230180b54820ce00,0x740bc4ac540fa101e512,0xc00a9e0c6c48287494c6],#[0xb8118660d83046958026,0x448727b60e17c1b6601f,0x3c2116964139047f983,0x2ae166d7a0a28a0b5d8,0x58300b0824808f748cc3,0x7680c44154ec000c0000,0x738a1ef000004c043c06,0x92872243122804039d08,0xd5a3283bfb113c806885,0x5e5e43a366021a10091c,0x51e08e41a2fc0259c0ef,0xc38cc88ec06ab2227e63,0x2297d446b127f2230480,0x605dd83455128be,0xc80fb8000010888e0178,0xd6a09b60207790b1001b,0x6b0641f40134a8377103,0x46b9823e9c10ac221190,0x2510cc811101a3c833d7,0x8f032320abe40e93b827,0xff5073fc0d9a80ec0830,0xaa580896c01ae414d980,0x81adf03866020b084f68,0xdb9ce9213422233c0d1d,0x4c0439031abe2292806a,0xaaa01b9502aca80fd940,0x13130149e04f06908780,0xc1652010b2025540db70,0x41bf01009003bae0d46,0x7000df010a1d01f80051,0x13100bde02018026f263,0x85b0d2126103aa649c20],#[0x28ac856ec127b06154,0x100035c146683e198138,0x67a053e81016013d0000,0x46800000444980000b06,0x218d00cd3c8df70418b0,0x3727600278012c808a01,0x1b00a40000000006235b,0xdf2085a000000000082d,0x2740000000fa9c145f80,0x843600001e0da11ca361,0x2836b00001c6a3640ace,0xa482828530a809400000,0x3063180124e03,0x12b00000a05fb400c000,0x5ce1a90cda012ee07dc0,0x2158bc013ef400b606d5,0xfd504ee815a522420000,0x2094894881f114650c22,0x50c80255c22b706bf82,0x1511111959d011be,0x3c0e280000512d16047c,0x14636dcc6600000300e,0x12d4e50804d1911e0000,0x81580f24c041c2897e0,0x8030c406a4d44880000b,0x6a0534e819d00c148430,0x56b119a00001d01bf027,0x2b300001609e56439283,0xd64636ec002fc1fd10,0x500b2f04304263784d53,0x8169c0886e0fb64836,0x40300f7d06d204f5c000],#[0x483bac0182e024d80,0x502e2c040f80cac0,0x1c0fff025b1467fe0f54,0x40dc9e510d7e0413008c,0xf8000003026fc071164b,0xc0e5101835531060,0xc0c1594bfa839ac238e0,0x44105f55b900000805ca,0x74a0158000000000f26a,0x56120b5700cfc035cb05,0x835601550cd8e027cb0,0xe1d420f802330,0x7a00bee443f0162e03e3,0x5964351004038144282d,0x3237727f2010b01be089,0x111a30116e0f65412798,0xe0450920d44451ec1d63,0x7800002076562a7c588d,0xf8000008116a20096544,0xafc899cb66c00000090,0x48662036a504bc000024,0x740a868892202a220e76,0xec01f280000606408094,0x5dc81246844980339606,0x423b887e739cff017580,0x20fde41a1402ec5042d4,0xa0dd701a54233a90378,0xe7028ac00002001b0000,0x251e08d80000402ad340,0x727d501b049346b9ca02,0x5236ae038400007a1186,0x19111f60bc6815a11277],#[0x22e9304864424069a831,0x8b96005ac40338132903,0x35050812203980076d1,0xc08db921c2c08e3020e4,0x57a1f700001c031681d1,0x2359056b01c64026f400,0x87310321d02a68052281,0x91a661892e02e780968c,0x6c0e1203963083d04ab8,0xabc4ca38335908424c96,0x18840b438078740ab606,0x88e640aa703e2e059968,0xe01e40000583b6a5111e,0xe7610cd2c818ac05fe,0x96210d0086fd10e40000,0x57cc4f6b482ca98e4922,0x25006422b00e7d8378e0,0x50628c8c014f6899ec,0xed041420741810280000,0x3a9041b604e440984834,0x156240bf881b855edc3b,0x808150309400fa004efb,0x2a2d8c01a3e0f4341649,0xc481ece42dc442fc0000,0x3b80000f21d640088001,0x455283ff000016e17548,0x51570039273a4206d9c,0x280b3ea0f2e0173006b9,0x894010800000088c0000,0x4ffc087510ef10709801,0x41f2c1a5c08e3d929740,0x6229a10b06a3331063ce],#[0xca0db94196381d942014,0x1cc0062c1352237a6084,0x308002a1c17500000713,0x43dcae4ea84c4b00a3f1,0x90212e063581d7639c19,0xf40138c06334896b82e0,0x19104fc2ed039036b998,0x1f28051f2255a8050a82,0x839022285c0b3c5214c2,0x321eb804dc249ea9526f,0xf901350089fa0cc40000,0x6a5824100001c04290dd,0x1e44307fc4359aadb9c0,0x519f301a190700a818c8,0x244070b935502766a1ea,0x5a13a608d05114f8a24,0x6c741786a03bc1117822,0xd5c8c68d026034000c0,0x60f3290b5208ad126514,0x16845de03a9841b72092,0x9aa041dc0d65804e0000,0x65a8e7791ce4c01f8707,0x238724494008d200f640,0x3c0c83015ec,0xd302fe28f5940cb80000,0xdb0000040e63c47c2ab6,0x141100f7800480000683,0x8060c42de00003c081a9,0x3812487287ecceb519b8,0x7110cfb008c0000001da,0xb8802900856800002c8e,0x22b9220120cf980],#[0xc49489284f54b1003ac0,0x7805d8844400000e0212,0xa008c8101e60000120aa,0x41711ee883520000060b,0xa4502b7aa8a611eac0,0xe01da820a3a09a50210c,0xea61801d34099bf20f5,0xaf64a0c0457121260000,0x44d40d238d1390140501,0x881d000007014b94,0xa01576024110382005d0,0xea071e000000000721e8,0xb9f223c00bfbc94ac039,0x289302d7803f61030512,0xe01fc00003d4c258,0x591a6511420065641e00,0x15039500000f0c9a417e,0xa7483c5505a400002c16,0x44a3190ab01920000240,0x14fd22ddb355e2012ec,0xd907d501d18031100d4e,0x2f10232900b7006280ed,0x22649eccc217903d1a62,0x659700158802f405c6c2,0xc04a45109102b8066490,0xe607c00000309a1e40b5,0x9fe04ae0104202f87086,0x3f201017100460c03740,0x580b9bc827e02bff0,0x3086b80adec1a6888ddf,0x4d0247ee56280d310349,0xd263190c498c006cba1f],#[0x3c1c018e0499c4862e98,0xa0476117c80fc9508f30,0x408c9001680000000003,0x6703b95082da0c77086b,0x11e830647288c10ef007,0x9b103da442a1e046102,0xe5a800582505c423d0,0x202013800ce063fa22b0,0xbc014e70085744780000,0x66d8030802552049ce04,0x2605c1812037a00000c0,0x1260d404c00422704bb5,0x4c4219dd9f8000000000,0x6a4033cc1c98232f2049,0x7296029f582920133931,0x24d96106781192823b20,0xc03dcc02a51cfe800006,0x4f028ba00dc0000681a8,0x7b058660b90488f8807,0xa2000391e42e1c02d404,0xda100cdc0248000018,0x418c0916880000241469,0x838204b46f100d0441f4,0xe03838cc42e066375020,0x562409a52240a0899c0,0xc0eda2006a061ea2034c,0xf48672926a00001003bb,0xc0feb910e950f04c61,0xa5119d90214b00da000,0xa1c81944a1ecb068c21,0x30274a5e3d82df522254,0xf40cec80f9c040cb235a],#[0xfe0ec581d3b03143028,0x1681050029a807f003,0x7760000061690801900,0x407cea0e97401f80000f,0x4d085020c5c000000000,0x6b1737a30d5dc4b2b026,0x90b2124049e58217382,0x297dc02c6604434832f1,0x708f4f24fc00001c0e26,0xe88064f46f8e087ac139,0xfa9024270335e0a89403,0x831e0374202b94680340,0x8126301bfb47bf0879c4,0x341592829d9823600003,0x2400007835e587382c61,0x71799a2888d4b24fbe81,0xd68d0b58000000001c0,0x80792405f42099b0870a,0xb40beac02b80000640bd,0x9b802390469c88a3e084,0x1dc0063d405ff2027103,0x3e40000180e4ab93821,0x5081ff05b0482ba83a8e,0x2c24060000280a5182ee,0xedc041c205f1805ee02f,0x9d9b0375a087c484a602,0x445a07a50816701f86b,0x3190b273c8cecf3c1921,0xe6817df1704e0a440000,0x58890d2506cbb0b22400,0xc6258075a01a54c14081,0x80ea888f9844808c58ac],#[0x22908f2484da40d67,0x18095]]
set_option maxRecDepth 16000 in
def g235D8 := limbs80 #[#[0xd58420af99210af59210,0x98c20b758c20bd98420b,0x84509f994209f59420b7,0x850bb58850bd98450bd5,0x10bf58810ded4250bb98,0xfe08110bf59410bf58c,0xfe8c110fe4c110fec811,0xe54110fe90110fe50110,0xd8910bf58910fe94110f,0x9510bfd8d10bf58d10bf,0x210fec8210bfd9510bf5,0x10bf58610fe54210fe4c,0xbf59210bf58e10bf58a,0xbf58c20bf58420bf5961,0xe94120fe54120bf59420,0x59520bfd8d20bfd8520f,0x8620fe54220bfd9520bf,0x220bf58e20bf58a20bf5,0x50bf58450bf59620bf59,0xdf54950bfd8550bf588,0xbf58650bfd8950dfd495,0xf58750bf59650bf58a50,0xd4810ff54810bf58b50b,0x8110ffd4c10ff54c10ff,0x110ff50110ffc8110ff4,0x10ffd4110ff54110ffd0,0xff10910ff8c910ff4c9,0xff14910ff90910ff5091,0xfd4910ff94910ff54910,0x54d10ff98910ff58910f,0x9510ff59510ffd4d10ff,0x610ff54610ff50610ff9],#[0x10ffd4a10ff54a10ffd4,0xff55210ffd4e10ff54e,0xffd4420ff54420ffd521,0xf54120ffd4c20ff54c20,0x8c520ff4c520ffd4120f,0x4520ff54520ff14520ff,0x520ff58520ffd4520ff9,0x20ffd4d20ff54d20ff98,0xff54620ff99520ff595,0xffd4a20ff54a20ffd462,0xf55220ffd4e20ff54e20,0x94550ff54550ffd5220f,0x8550ff58550ff18550ff,0x950ff54950ffd8550ff9,0x50ff58950ff18950ff94,0x2c044000ffd8950ff989,0x1e07a834c16208f03681,0x8343d61c20cc85c02801,0x2d915f0a544e62581140,0x8f0473036f1a68c90604,0xc486235914085c4051f1,0x1159ca7c523280936096,0xb863a30c17d8b9a5a42c,0x9b1c50de46d035019f8c,0x207e73db9e54ef47513,0x47c233d13e87d43120c9,0x13dc9c54d525e92b0921,0xd5722ad1516a54519284,0xed824bcd5d22dd167ab0,0x5469933ed96cc9463930,0x9b5c96e146f5b6b5b08d,0xf8d7b5bcede16ed4755b],#[0x42b611705b8193fedf96,0x31db8dcc64229712986b,0x94bd2597294935c92643,0x23430a004f0a73335b99,0xf15676adb536a86d33e9,0x24404b54d9e6ca1619a,0x80132021300442101488,0x884c002202010400a080,0x4c80a4c0022020206009,0x5284462248290101000a,0xc80a440120a405240400,0x222110014910141000a4,0x915024460a5088614901,0xa0401026201264032800,0x880a889100d101284480,0x4a405440491010094264,0x893202a24a4880815100,0x84480815101244052414,0x84049480a14a11202052,0x20192104430809290101,0x910102922000a9118611,0x84480814041244451014,0x91005491014290241851,0x44050a3011010293201,0x91110280249488a54980,0xa44812102a1244440c94,0x460294911100a5244440,0x102c2244040a488002a4,0x8120c28c224040a18911,0x8482900c8802a4880a14,0x80080829520306241488,0x18a920a4440400292222],#[0x889149100c0010a48a91,0x2912a00292203068a48,0xe04b920a4450808b052,0x8c14a4842e1412523049,0xa94a110cc050694a1118,0x48a94910122a5444880,0x4a4078a94910122a5244,0x6848862520295848800c,0x52a22048529152922240,0x864c90e96288209088d1,0x54b14312104464a8c345,0xd1414a18912208252444,0x4a3864a4841114117868,0x44a20910111c3441a092,0x1c2488929024ba52440,0x122240709125203980b1,0x5325d2224a4064889290,0x52a41014811152901a48,0x22487889042520296880,0x811048a5242170a092c1,0x8a5202980b101a44a44,0x24319090d1a582487889,0x60a0529320304868e0a5,0x1a44b08810052932021,0x223c4480e125203180b1,0x1424929114ac14201292,0x5293222454b112112034,0x80950872c9114a4c80b1,0x74a4c80804b44490d1c2,0x45488e243430a0074a48,0x224164a4090894406244,0x1429488c6220382910a5],#[0x4925222a14a488891124,0x202968805225844072c8,0x28295085224888892125,0x129120441424529214b8,0x22224229480a602c4069,0x14a48632121c14685292,0xc2445a0210014d868e0a,0x242001481004ac4490d1,0x440548880102a415488a,0x1a222901d2222b1480a3,0x292152220040a8c55222,0x49111c1158284b802444,0x84280245488e550c1001,0x88a4888c84a928a44510,0x840120a44a8c5508]]
set_option maxRecDepth 16000 in
def g235H8 := limbs80 #[#[0x7818100000010400400,0x4380000400b48101010,0x1040e040019c1850200,0x5120a380000200104341,0x8b5400f830e6c0000e0c,0x10a00c84002000700000,0x12840800e00081040438,0x8000830800b870024e91,0x88810004302001c1010,0x180140c100004c10006,0x401081c0162001381000,0x8083008914102060610,0x8703830625c0406040,0x18200050868014024c80,0xc000041e00e000008101,0xc011144da820a004031,0xe060028c95080629d14,0x48a2818f32084c081102,0x50e241830c0c0050000,0x9084428f305802604141,0x240b110634004025808,0x408281760c0972850600,0x1380022870b02f000e0,0x7000000b83002c30c00,0x90b0a541103ced70d040,0x5020d7034a22f9b0230,0xa2ebc227101859902180,0x142d0152e18637402850,0x800c011410b07032c009,0x1524f0804001160029c2,0x4001221dc13000c4094c,0x30320e89027],#[0xb780a00000790a940728,0x278f828cc4c300001e04,0x4a428cc1e88529800016,0xb71c4cb8443b2039f221,0x32ad8000000001203263,0x2c800000000025300000,0xe01900001241aa057141,0x6504496840f2404f9311,0x2568207f800018138103,0xd98174c132d8344c4dab,0x3e5058a843ee01b8614,0x16529401e8613ea05f89,0x41e82c00000160cc422c,0x1840742f65023fc07248,0x657005e000000001e4d0,0x21397b1fc0057e2498e0,0x10867094e6001630146,0x8625416738589232f000,0xc10560c1824062600f3c,0x6bbd00eda330a908bc17,0x3b51a0000505b30,0x438a1690000,0x5cd8000000000020ca80,0x9e000008882b02c80000,0x28798000068,0x20000000000000000000,0x2453e0f95a8e460cf514,0x3b08a000050233a10f6,0x5c201cc000000000000,0xa82ef8020000051ca56,0x2c9a037202df413f0000,0x22cce11202],#[0x16163800000000,0xa36700000a13d70a7200,0xc14b00000000000000,0xe0010000020b2800,0x80000000000000000000,0x30885eecc9208e3a03,0x2a946285a120e7000010,0x53f00f180000000040ae,0x302f92ee04104844ff38,0xd0426610438283a04c,0xc14180001c214784d5a5,0xd80000502466869900ae,0x938cc0e4c0d9be18f602,0xb003e3009a502aa4ee2f,0x5651218c00004059fc11,0x2000010418a070b904b8,0x4cda0358819d6215b0a8,0x80000c11f4336b2104bc,0x43044d1c535f903f80b8,0x5f8003c80aa7a03b61,0x95007c88166c117134a0,0x1f7a187f8ada0000502,0x1058a09b704bf021d2,0x140a72a3ec075,0xe00006822a00001ad1e0,0x16003892e8000018d3,0x500b1419300000010700,0x42da9db813df1c33e078,0x404ff9858e0,0x5ce0c3281ece058cc3c4,0x16068382fa0000692,0xa80000000048576c0958],#[0x383be44bbc85a2216,0x6a8f3182ac2223f04a40,0x683496055c8ad,0x2a71687808048f13380,0x12b007842b7928e10831,0x61208000000005908c22,0x2e0507b815c000000001,0x81a80000000000000704,0x30a00004,0x37880001404080000000,0xd0012baadb40f12826bc,0x822180000816a0832,0x601b0000032007e17a00,0x1840264b4108ec0000,0x20812018440c97902e00,0x8b26bdc008b817380000,0x8353e067f0c2e68f3893,0x180001893f124de08791,0x4fd80000000032c60817,0x1681fc824f6151b9328a,0x55400007843a00005018,0xb84f2810000000000028,0x614880000c0e5,0x3a4e20000084da00,0x4a292ac1087605808446,0xb8c00000000000000106,0x1905e6000000000c133e,0x864d0096261800001e13,0x4369285ae0000784bba,0x1ec000000001a4270000,0x80001e12e34c736eed42,0xa600001e501800016431],#[0x7044a000010528a0,0x5c809d684a080f04053a,0x33a7022700000aa56513,0x401ee800000005,0x21052203e685b8000,0xf6ee148b4d8037800000,0xdd40000684c80000085e,0x110916a864b8ac6b5d18,0xe9b02fee2bf00001c166,0x2a12d11f4f35f838b380,0x3540b0338b77151113e7,0x3baca0db09b07e173504,0x7831d40f5f83190073f,0x212bb4113921ae000,0x8001f0a4252e2ff82bc0,0x168e7000016184802e,0x5904c000000000000000,0x53000000000000000000,0xc0d70000102190000065,0x2c5a240c4e2886,0x12025205088d00800,0xa6210400001a4d000000,0x3404c000000000a02,0x6115000000000000000,0x818a000050a2,0x9082cc011900,0x184c4a01b725e64222,0x61085823000004a3ba00,0xc6a17500001a0fb6b8a4,0x1815080001605a313,0x29412c55180000650c0,0x9593a19bc02301b4a000],#[0x4ef228223a126000018,0x0,0xc0226000000000000000,0x837c418f,0x28b5200000000000,0x78424000040496,0x15a6e14a800018126800,0x74029662baa837985112,0x616a85bec53238006013,0x8174c0d3d408e70429a,0x7f40a4e0d4000000000,0xc0863a151125f6a16ee0,0x621b14016800008411,0xae3300001c41a583dc00,0x42441898b5880c0125a8,0x80b40000283fd60c594b,0x68000020e57a2cb20ac6,0xdbd03d28935e8018611,0x26e0d8000140ca5a2338,0x20b8eeb80001016d1aa0,0xf102a0000200f0000028,0x2a8000160e88889a6191,0x812b9a5000015000006e,0x8de1800000000000051c,0x582000000001417b581,0x76055781108000000000,0x17dd82c40000581ac618,0x424b3c823b2134800008,0x3a94c284902600660031,0x16021c1593c0e390,0x484a384dbc13c40027,0xa218581e60000621c400],#[0x92c8ad800000000221d5,0x10940b0628612d290,0x800000a1181203f80c10,0xa1700863b60b,0x7a11a80000011a783e00,0x9dae033a1549e8b0e027,0x913d380c7c85d0000048,0x7ff81376cf4980a5211f,0x60ae18c2aa020c823461,0x4e24b1c2567e13b701f1,0x55a20d2e140d2388b08,0x500000092b7841b21884,0x4bf0a99fe871a1b0a612,0xac02aa10600000385c22,0x212100000440c980e,0xb13bd6565fa505042200,0x4048c02be80000e07e,0x12a182e4000012c5c00,0x38cb7080001a14e18107,0x214d00001401ba80,0xbe01728927584ea00000,0xb25500812b45800016a3,0x64027e060f8123e934f8,0x53a0ae0dfd805,0x485218215383ba001480,0x298856440fde89e40000,0xe03518051247c0000180,0xeb271c1a03d86bab81d2,0x122a612f781f5e185585,0xf00001e144203c8c16db,0x70d8000004f963b25a2d,0x1e830e053c40b1c03b92],#[0x1aea14824c00000000,0x4001a000028224092480,0x924c4e5a217000000000,0x800400001c1228000181,0xc9e607ac01be,0x12933088580000000,0x48000060fc8a5214aff8,0x2cb902ba000061c3dc00,0x80000000000000382f01,0x429ff60430856,0x700fce277003d4000000,0xa8501912edf000000000,0x9137884fe00005037620,0x1c4c8505fc00004a39f,0xa4e4000058322c41c800,0x6209722d56140fa4c68,0x6b202000000000000,0x1801d06ec000080,0x1ed00de9204dc1410000,0x80000285fb860200003c,0x480c141534a317a0e0,0x6e2f501d601159040a00,0xa0a6b3b8f437c00001,0x24b4145800000000000,0x1288e4a0c2202872114c,0xb47057504f52851e811,0x520952186fe93228b672,0x615b503b741867104,0x39308000000000000000,0x3101f96048b8207e010,0xe638384203319857a1,0x53e00001a37be01a2],#[0x92a80000420d14949000,0x40000000000000140904,0x11880001013351065a08,0x1607b922c5c4c7c0291e,0x3ae20bd4134c214b8000,0x3834160838000128ae30,0xbb712f12b5b104500000,0xc0980a1a3a98300000a0,0xff06ba40084000040cc7,0x14883b80d80000483,0xb800014169db4de00000,0x8d8683ab6190d235ac71,0x800006860a000000000e,0x162175f05150d44a802,0x800000000480e54cff10,0x58088000000001803d,0xc80c00000647c8000000,0x3200007a1f6000000000,0x822d804780af40000004,0x28a0ce00000000002228,0x7213400005091f471,0x4000000000e01160e100,0x5c40000284c040f28033,0xd14500000138a70a8fb8,0x76303b4614980000e0ab,0x830b00000000040c2840,0x140315bbdde0e070d19,0x25f0084885bc0000000,0x4137b602c93d1800006,0x849f8835580990b0,0x400003ac2800005a1a40,0x4422843ca45a0000603a],#[0x4a909c50dd1017c371f1,0x7240389e4f61021e8801,0x8383e838d51384a8e9c3,0x100d7f9103e0d8f1303,0x6cbc800012410000,0x88000000006196800000,0x37088590000000000882,0x6808db00ee0000580362,0x43da11c29b0e00004bbd,0x800012ad0792fbc0f309,0x71365c03ce21d3e043,0xaa7f00001847dd828e00,0x3e6426501b440f780000,0x655680001e083000,0x2815420c8782f7a8e50,0x14480000000078066000,0x60000792ea0000204ef0,0x303003a00001a071301b,0x8000110e9f3ad2000058,0x4549078000028478e80a,0x618580001c819d8634ad,0x6f7811c0000401c1,0x0,0x701152d406112bc1788,0xd800001028600000000,0x80000485e489291218a2,0x50e4306c0306a2c7b24b,0x80000875f00001e023f8,0x24800000000093a6a011,0xee2a2403fc1,0xd1e00c98ba600000086a,0xa0c800006055c0000204],#[0x5054b00340000180503,0xac1a000038aee000,0xe689f80001603d235180,0xdffc2d200000e0f0f05d,0x8000000007838a000078,0x51e92d80000000010497,0x60cc80000656630288e7,0x1c177203eea8e5fa1cf,0x100e0b3d85c826d75b2,0x5134220788006b06f67,0x40d1032e211bd0220000,0xa0000280926096744a2e,0x3046008d80b940f42856,0xb035140908000102be61,0xbbd805c810b085d8e05b,0xa0d1f8dc580c6ea538c0,0x1dc3317a6060edab8014,0x104236bf943e0000782,0x47a48a618e12c8c418b4,0x2d198597ee2840073a04,0x1615f0036ba127782a7c,0x4e6202df8641a0028000,0x601ae000018,0x0,0xe0bc9827000007861a00,0xea9134fa49f602f80000,0x43088c000000000491,0x1028120b9b02d4e1107,0x8818244f6e10e8000,0x44117c10f8e10154448a,0xb0c00005105d6427b059,0x1496d70e08e0fd79],#[0x50310a146800008872,0x4157880ff32911203400,0x720098a904e201c280bb,0x3e8c286d02640000684,0x4800000000085f240659,0xecf0339eec9f0518209,0x8244b2829e0000000012,0x1dfc164b00bc437493b2,0x48251a08510ad2275e98,0x66715342b66a92b66e2c,0x53ad906f64b6b93a931,0xbac024185874d33601a7,0x630e0742859a204e501,0xe800000000723b602bdf,0x755c002ba50628126caf,0x362c7504e9808624d88a,0x2d2205e60e1920497912,0x80000c0dd512caf0ed91,0x20fe00001c43d,0x2cda7004f00792884800,0x3360b498bffc05280001,0x248ea0eb7085204d4430,0x2b82b28028e82454a389,0x116093fb271e58525283,0x9410510563e0e1824a7a,0x1da0000484ab30f4b035,0x2c2a0a2da4ae005398,0x30a0076a163785db402b,0x216c0000000005adef21,0xea00000000000007023d,0x57ea036800000000223,0x7060c2c0dc92e0e0d9f],#[0x18c1d8820cc504415,0x1e15ec025c00002a60e0,0x88e60000,0xd84e34b2f00001089e80,0x31d3b6c61218000080b5,0xa0d5a22bce6935060560,0x3f61560013da4ee6802e,0x2c1c00000000140ec684,0x493c9605f3033a804a9,0x7500000a2253033e000,0xa000010b57e18c802b64,0xb036085ca1068933a862,0x383dae53f4014ca13640,0xc2200d36137ba3122178,0x1b8ae81359849166,0x1805da22ba000000000,0x26e40fe80001e92a000,0xe701160000004f88ecae,0xd713b04181c0372482,0x724046a2c7e054e83274,0x144a0825010964bb0802,0x686cc8bb062bff8,0x7a98bd32b4600001a04d,0xa80b00000e08a4848948,0x1d20d3524c304d2c044c,0x2611aecb6048062d1435,0x52330633068342c064a,0x38d064400004027c4a1,0x80000602dbe9152891b2,0x7400d6b80fa0000511f,0xc61c00000000070,0x2890da88218cbf6160],#[0xc02680623eb7fda3c800,0x2a038000000001,0x8474612d800004063800,0x538b4b80e6a84b1e9852,0xa43003e600000000140d,0xc64eb880cbe0927bbaa8,0x27d217d285726a127804,0x8000180a1392e2618402,0xc1027f200c3816b2018,0x809e00000843c28068a1,0xc380e400000a41680001,0x92b00000426080000112,0x793b6e4d11,0xf600000000048578000,0x201617ac68e86a000010,0x1434211981658007a042,0xf20cdc052601c628e6f2,0x45181180000082ea609c,0xea4543b76000030aed02,0x3d4030b012e000000000,0x30e4504220d6000052d,0x5003a411998337e105a,0x8d7d8158000050ae8000,0xf0a3980000000000120a,0x409c4c2f81fc60968834,0x72c892648982a3c513e0,0x1efbb7ba4caa0476a0a9,0x852a124e040468900101,0xe154702036ad100000,0x1b3f31e909cce04ef02,0xdca2be000030ae161526,0xdc40867604a00001618],#[0x1694bb85fba350c3b892,0x4f060afc9405a2b60000,0x80001aa11521be221b08,0xef181dc60ad185332061,0x19ba86558142c0,0x6c000000000000000000,0x9aed80868218100bf081,0x5512cd60187050a00004,0x5056745670000102b,0xcc97621c2dc15388adc0,0x38112216b404a,0x3a0d360fc00001814080,0xece11ef6172c8b040000,0x84da2813200004042a24,0x884872885300000384a6,0x1500000203ea9155601,0x15ac245d81a400003,0x1bb6e000000000000,0x1488be0500a0b7383a00,0xa70609e80001608b8000,0x81aba099c1af48216f8,0x1250292846c00b,0x6730a1d8600004856e00,0x1470780000a05e80000,0x185c4b46803680000000,0xcedce,0xe79062e215480000000,0x8437e]]
def g235D9 := limbs80 #[#[0xd20fe107f843fa21fc10,0xa1fe50fea87f143fc41f,0x19508a379506c1e003fe,0x485103091054009f96db,0x814900091440c2040407,0x51030500930084451030,0x4900091440c108049120,0xc2052405009445103081,0x24002440c20450064440,0x10308100519110308115]]
set_option maxRecDepth 16000 in
def g235H9 := limbs80 #[#[0x6102010800602000800b,0x580010a0000006003241,0x4090180428800280841e,0x58a0a201021c20202520,0x100040042c000800200,0xd0298109026420012403,0x25152623a10305185220,0x2,0x1a3051804a1057e0760,0x24e0000f078713ce5551,0x1054f04110840000a,0x1169083b00d406e11080,0x7512466c665105600005,0x248d03ee01422500000e,0x24b736100002037555ef,0x4b0000197af028607c8,0x346470f96070180000e,0x60481186613b7,0x57000000000000000000,0x113f074621500000149a,0x708253505db007e740e,0x5430000c07e0000c3472,0x7520000800ad022610b3,0x2c41662063d0090000a,0xf5781187f4053,0x4d874f3024107900000,0x75c00000000804e474c3,0x3013f8441801c00005,0x4071000082417483b,0x8184000040520,0x65e206b11120000c03f0,0xb2462450903502176],#[0xb0590000d67000000,0x808600000,0x78351800000441000000,0x4f9020d00f407720447,0x610000000090664136b,0x87de0260000b445845de,0x1200000106f0000c03db,0x711a00005021c404d,0x0,0x201d725a0000220d0,0x320000126bd37a00000,0x27dc556611790873263c,0x154219d013412f942c7,0x464e10aa244b00b00006,0x467e97b9030d06400001,0x19c033e51a46787,0x13a0000801600000,0x252a038a8699068e2180,0x8740000000000002210d,0x961001f0000000000006,0x55f00000000c564f245c,0x776802f0000e44400002,0x50000d07b0000504cf,0x85a75710000918161290,0x2b82742216f01280851,0x41e911fa047102e1001c,0x49f065d062a4768031e,0x69a138b741000032593,0x74b102330450000d4689,0x80003451405b11676,0x6a00000000000000000,0xc429000051858],#[0x29c5790000024f00000,0x36275d000000000000b,0x2500000471803ac139d,0x452000061099360e6645,0x30060000a671b135f,0x90400000000000000,0x365f0000a0580,0x75000000000000000000,0x542717f324900002148c,0x6067203cb046226c5,0x2144072c008000000000,0x42d2405512a4409212e,0x73524a44690000f05c9,0xd44f00007,0x137a37b307d425b30750,0x2d100200000000500e8,0x17601ea183200c30807,0x43713e3060000000009,0x42a0000574e2081b,0x26d412df039000012540,0x213508200000000f05ee,0x530000702700009,0x5359e050000016790,0x7439000000000,0x26a00003875000000000,0x917c606d00000000c,0xa45c95655411105f0,0x74d00005011c777b51f0,0x2470000f05ab465f0108,0x2110000712a917d00003,0x115100451825275e85b2,0x807f0000e055017ee],#[0x427611c7739d03b74770,0x1b207a0000c02af06c6,0xb]]
def g235D10 (j : Nat) := if j=0 then 0x3f else 0
def g235H10 := limbs80 #[#[0xa98231156208034a0060,0x7a41aa798233dc971,0xc38c3644a880001a2800,0x2000000284213e4ae830,0x5440000006b491,0x2b8883800000000501,0x18a092a4e3973852a8,0x400a3400000000051480,0xa30a9a09f02800019d93,0x850ab1191118881a0005,0x6c2d0a629421000284ea,0x3a8b00000000641000,0x0,0x9460278180000000000,0x238005b283323a800000,0x731799092a]]
def g235L : Nat → Packing
  | 4 => (2,6,5,0,0,3,0,g235D4)
  | 5 => (194,5,5,0,0,11,0,g235D5)
  | 6 => (1106,4,5,0,0,14,0,g235D6)
  | 7 => (807,3,5,0,0,15,0,g235D7)
  | 8 => (136,2,5,0,0,13,0,g235D8)
  | 9 => (10,1,5,0,0,9,0,g235D9)
  | 10 => (1,0,5,0,0,0,0,g235D10)
  | _ => emptyPacking
def g235I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 3 0 5 1 0 g235H5
  | 6 => lookupWord 84 419 8 16 8 4 g235H6
  | 7 => lookupWord 480 2203 9 19 11 4 g235H7
  | 8 => lookupWord 361 1973 7 18 10 4 g235H8
  | 9 => lookupWord 76 457 7 16 8 4 g235H9
  | 10 => lookupWord 15 97 5 12 4 4 g235H10
  | _ => fun _ => none
def g235 : Forest := ⟨235,10,fun i => g235Y[i]?.getD (0,0),g235C,g235A,g235L,g235I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P4_0 : block g235 4 0 2=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g235B4 : block g235 4 0 2=true := g235P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P5_0 : block g235 5 0 96=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P5_96 : block g235 5 96 96=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P5_192 : block g235 5 192 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g235B5 : block g235 5 0 194=true := (@block_merge g235 5 0 96 98 g235P5_0 (@block_merge g235 5 96 96 2 g235P5_96 g235P5_192))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P6_0 : block g235 6 0 2=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P6_2 : block g235 6 2 52=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P6_54 : block g235 6 54 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P6_150 : block g235 6 150 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P6_246 : block g235 6 246 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P6_342 : block g235 6 342 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P6_438 : block g235 6 438 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P6_534 : block g235 6 534 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P6_630 : block g235 6 630 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P6_726 : block g235 6 726 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P6_822 : block g235 6 822 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P6_918 : block g235 6 918 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P6_1014 : block g235 6 1014 92=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g235B6 : block g235 6 0 1106=true := (@block_merge g235 6 0 438 668 (@block_merge g235 6 0 150 288 (@block_merge g235 6 0 2 148 g235P6_0 (@block_merge g235 6 2 52 96 g235P6_2 g235P6_54)) (@block_merge g235 6 150 96 192 g235P6_150 (@block_merge g235 6 246 96 96 g235P6_246 g235P6_342))) (@block_merge g235 6 438 288 380 (@block_merge g235 6 438 96 192 g235P6_438 (@block_merge g235 6 534 96 96 g235P6_534 g235P6_630)) (@block_merge g235 6 726 192 188 (@block_merge g235 6 726 96 96 g235P6_726 g235P6_822) (@block_merge g235 6 918 96 92 g235P6_918 g235P6_1014))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P7_0 : block g235 7 0 7=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P7_7 : block g235 7 7 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P7_103 : block g235 7 103 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P7_199 : block g235 7 199 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P7_295 : block g235 7 295 45=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P7_340 : block g235 7 340 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P7_436 : block g235 7 436 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P7_532 : block g235 7 532 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P7_628 : block g235 7 628 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P7_724 : block g235 7 724 83=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g235B7 : block g235 7 0 807=true := (@block_merge g235 7 0 340 467 (@block_merge g235 7 0 103 237 (@block_merge g235 7 0 7 96 g235P7_0 g235P7_7) (@block_merge g235 7 103 96 141 g235P7_103 (@block_merge g235 7 199 96 45 g235P7_199 g235P7_295))) (@block_merge g235 7 340 192 275 (@block_merge g235 7 340 96 96 g235P7_340 g235P7_436) (@block_merge g235 7 532 96 179 g235P7_532 (@block_merge g235 7 628 96 83 g235P7_628 g235P7_724))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P8_0 : block g235 8 0 13=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P8_13 : block g235 8 13 51=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P8_64 : block g235 8 64 72=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g235B8 : block g235 8 0 136=true := (@block_merge g235 8 0 13 123 g235P8_0 (@block_merge g235 8 13 51 72 g235P8_13 g235P8_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P9_0 : block g235 9 0 10=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g235B9 : block g235 9 0 10=true := g235P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P10_0 : block g235 10 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g235B10 : block g235 10 0 1=true := g235P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235T : checkedTables g235 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g235 0 0 0 = true)
  · exact (rfl : block g235 1 0 0 = true)
  · exact (rfl : block g235 2 0 0 = true)
  · exact (rfl : block g235 3 0 0 = true)
  · exact g235B4
  · exact g235B5
  · exact g235B6
  · exact g235B7
  · exact g235B8
  · exact g235B9
  · exact g235B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235G : graphValid g235 (boundsBefore K219) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low235 : Lower true (varsX 235) (graphGoal 235) 11 := lower_forest (g:=g235) (i:=0) (hints:=16777299) (before_sound K219 V219) g235G g235T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K235 := extendKnown K219 11 [(235,[]),(243,[67])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V235 : Known true K235 := extend_ok (m:=235) V219 low235 (by decide +kernel)
def g251Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x433095a1cd00000000,0xff00000000ff00ffff])),(BitVec.ofNat 152 (word80 [0x410014a04d21212121,0x21212121212121212121]))),((BitVec.ofNat 152 (word80 [0x40db1a310400000000,0xff000000ffff00000000])),(BitVec.ofNat 152 (word80 [0x409b18310007070707,0x7070707070707070707]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x8c3a21c210000000ff,0xff000000ff00ff])),(BitVec.ofNat 152 (word80 [0x4322142100a0a0a0a,0xa0a0a0a0a0a0a0a0a0a]))),((BitVec.ofNat 152 (word80 [0x598fc00baa0000ff00,0xff00000000ffff00])),(BitVec.ofNat 152 (word80 [0x889c009a214141414,0x14141414141414141414]))),((BitVec.ofNat 152 (word80 [0xa2e48a4e1300ff0000,0xffff000000])),(BitVec.ofNat 152 (word80 [0xa264824e1258585858,0x58585858585858585858]))),((BitVec.ofNat 152 (word80 [0x920562644eff000000,0xffffff0000000000])),(BitVec.ofNat 152 (word80 [0x920402044c60606060,0x60606060606060606060]))),((BitVec.ofNat 152 (word80 [0x2400141c70ffffffff,0xffff0000000000000000])),(BitVec.ofNat 152 (word80 [0x80808080,0x80808080808080808080]))),(0x0,0x0)]
def g251C : List ColumnInfo := [(8,0,243,0,11),(16,0,235,0,11),(1,0,250,0,10),(2,0,249,0,10),(32,0,219,0,10),(64,0,187,0,10),(128,0,123,0,10),(3,0,248,0,8),(33,0,218,0,8),(65,0,186,0,8),(66,0,185,0,8),(96,0,155,0,8),(0,2,25,224,7),(0,32,88,131,7),(35,0,216,0,7),(98,0,153,0,7),(129,0,122,0,7),(130,0,121,0,7),(160,0,91,0,7),(192,0,59,0,7),(1,32,88,130,6),(2,32,88,129,6),(32,2,25,192,6),(64,2,25,160,6),(128,2,25,96,6),(128,32,88,3,6),(0,64,33,154,5),(67,0,184,0,5),(97,0,154,0,5),(129,32,88,2,5),(160,2,25,64,5),(161,0,90,0,5),(192,2,25,32,5),(194,0,57,0,5),(131,0,88,0,4),(131,32,88,0,4),(224,2,25,0,4)]
def g251A : List (List Nat) := [[],[67],[96,81],[96,81,67]]
def g251D8 := limbs80 #[#[0xaa2c28879c5956154110,0x21c757559561443c6aca,0x617655110b9bc8acaaa2,0x644237f28c3aca8846fe,0xbc8aecaa2811bd95e117,0x2a8a054fe557655140ad,0x5b79161d5458276f22c3,0x81dd560a9ecad0eaa2c1,0x8727b0aaa6e0b0c6fe51,0x32cab82a91bf94603755,0xcaa56de45765c154d1fc,0x795e057655366f0bc0ae,0x59540f5cc2ac8b0281b3,0xf7728c0ac0a85ede4584,0x8b8ac15bf9460576542,0x4ef657845c560cdebaf,0x5955458737b28c2ee8b,0xd9ec0b00b2aa9e3d9,0x23605b8960e013c1c021,0x30d598a2d2534961101f,0x5728d4ce9191520e3d07,0xc08386d89a3320608b65,0x7c003c20101304509f07,0x3d871bc1f010c4384f0,0x6f0783f007b188cf07c0,0x46d17c1f00603745e0ac,0x746e0f82f07c01b83e0b,0x108ce0ac6f07c0c2c603,0x5f07c0c20542fc1f020e,0x8ce0b86f07c092c6b1b4,0x2c31b82e1bc1f004f14,0xf07c023c6d1782f0786f],#[0x3e1bc1b0bc01893e1b42,0x8731b42f07c083c5d178,0x485c2147d0a0bf07c0b1,0xf010b130542fc1f00144,0x304109f07c08386d1bc1,0x1270e0bf07c0a20191c1,0x805207f07c0843091a,0x2094c4f1071309b0fc1f,0x85193440cb62743f07c0,0xc04387e09c5f07c00785,0x10e08050901f073c1037,0x1bc1f008e068683fc1f0,0x4cd]]
set_option maxRecDepth 16000 in
def g251D9 := limbs80 #[#[0xeb964581409bf845d910,0xeb564585419f7815d940,0xe3d6555161f355155161,0xb3f8159554d3d7555161,0xb3f855d954bb7815d954,0xf796554110ff16154110,0xbf98654110df97654110,0xdf97558110fb95458110,0xfb55458510bfb8558110,0xdf57558510ef56558510,0xdbd7655110f3d6555110,0xd7d7559510bf78159510,0x9ff865d5109fd8759510,0x9ff855d910dbf845d910,0xf3d6555140fb95458140,0xbbd8655140dbd7655140,0x9ff855d940bbf8559140,0xef96458150bfb8158150,0x9ff815d950b7f8558550,0xdbd54dc560bbf845c560,0xfb980551609fd85dc560,0xdbd8755160f3d5155160,0x9fd85dd160dbe8755160,0x9fd84dd5609fd81dd560,0xdbd54dc161bbf845c161,0xf3d75551619fd85dc161,0xf3d655c1549fd80dd561,0xbbf865c154dbd765c154,0xf3d8159554f3d8059554,0xfb7815d954bbf805d954,0xff98558110f3f855d954,0xfbd8459540ff98558140],#[0xff98158150dfd8759540,0xdfd815d950ff98458150,0xdfd755c560dff815d950,0xdfd755d160efd7559160,0xffd815d560bff815d560,0x824c09c000fff815d560,0x62160f606782b2114070,0xd0dd46722fd1608a144b,0xe4d424c11b88523f61d,0x2e9884bdc5b22bf950ca,0xf6677739d9bfcd986903,0x484a3591468704159fe0,0x1488a114eaa6892de933,0x15daade568cb1356baa0,0x19a82cea652b1a5848bf,0xe5754b9d9c74e076e136,0x17e046fe77d13dbde66e,0x70780445aa2390e984dc,0x3c0070e1606f168d83c1,0x161383c020248d087178,0x820fe003850a8338b46c,0x48a330dc2e0f001e381b,0x790174884f85c1e003c7,0x1e2084268cc370b83c00,0xe151b83c0858fc1e004c,0x48386e0f00240f102e15,0x13c1e0438648b1b83c08,0x6342783c00705c629b18,0x23c70802783c0870806,0x800e0c0d1062c1e8dc1e,0x62f078010870a06e0a2b,0x9118651b83c08383c7],#[0x8346e0031123707810e1,0x10f1b83c007e1c40283b,0x2f07808e198c1743f078,0xc45e0f00308e168c0ca,0x3c0870b46a283383c047,0x241c2fc1e00586065178,0x22c1c351b83c00bc3850,0xbc1e00661c28428dc1e0,0xe198c0de0f02160e188,0x707810e1a8ac6e0f001b,0xb4662f07810e1c1ac5a3,0xe1f83c0848401c2c401,0x1461c28502410e0f0212,0xa0cc2f07808e150bc1e0,0xc08813c4e2d0f83c00e8,0xf1418c5c3707810e1b83,0x1b83c0278a08e0f00324,0xc5c16181bc1e013c6c16,0x5e0f021c30370dc1e013,0xb0dc1e05141848370cc,0xda2f07808e181ac3026,0x1478b07e0f002f11170c,0x1423c1e04386a1707811,0x8509f07800f46244649b,0x1e003c323e1b83c00ba3,0x780c60683c68411a85c,0xda14218dc1e043c7217,0x64a02004c3f83c00992,0xc2109f0b83c00788070d,0xb0a8e0da330b83c0878,0x481e14168c430a70781,0xa0908707810e100dc1e0],#[0xc00ca38604f07810e0e8,0x51783c00ca3880902f83,0x20ee0f00402318401f0e,0x8e100fc1e003a121f161,0xf011c201842230df0780,0x344e0f0040231a2109e0,0x1f218a13e0f021c1d191,0x238549c49130ee0f003a,0xc41086c94451783c00c,0x44212c31008220e8622]]
def g251H9 := limbs80 #[#[0x8058554780002f14245,0x944704192b0c0000011,0x2660639b001e000010e5,0x80a,0x1c2502b014c000b0e00,0x0,0x93582589c8302ce50000,0x61a003c568b]]
def g251D10 := limbs80 #[#[0x9504439eb2aa9cf54554,0xa221fd58510ff2c0887f,0x40bfaec885fd75443dea,0x7bd64503deaa281fe581,0xebb2a1fe58150bfaeca0,0x5160f7aa8b05ff71582f,0xb05ff745837eb22c1ef9,0x6febb283fd58541bfeea,0xf95161f7aa8b0dff7058,0xeab0dff745877eb22c3e,0x443debb2a9ef5c154bfe,0x1ff58550ffacaa07fd65,0xfaeab07fd74583feb8ac,0x75587feba2c3ff5c161f,0x7f0600450320170007fd,0x12910e0f70dc0b909a0,0x1fa1db1c41a118a16b15,0xab29427525e243228211,0x834d3323172f82e12ca2,0xc264073ec3cd3aa38b36,0x360e0078d8d8583801e2,0xe0070d8380121c209e12,0x38a8d83801c38862a360,0x1c3c322e0e043878c182,0xe0e0071014318c138380,0x8d83801c308880ba362,0x801c34360e005870b8a2,0xfe2e0e007121a248d83,0x8c1d8380123090806a3,0x1c28988234760e0048e2,0xc122e0e011900b838020,0x70f0c8b83801c2a24327],#[0x80201c28a090862e0e00,0x1c34722e0e0080a0b83,0x887e0e0070c228c1f838,0xe0078e0b8380221c2890,0xd828b801c28bc8e14360,0x1c289088307e0e0070f0,0x8160e008878a1f838022,0x78c32118c8583801e3,0x8b83811c4030a612360e,0xd12409a322e0e0470c26,0xe0118ea22e228d83801,0x3b83801c3e4088862876,0x8e84c760e0080e24218a,0x6078e222183801c2e309,0x83801e423890760e0088,0x262219]]
def g251H10 := limbs80 #[#[0x931417d4395041003205,0x7c646040006a15b016b6,0x7000585703fc1ec05f91,0x400000510c8c4c04664,0x2ac04d070c070182a198,0x2885cd0b403bc49027a,0x41681f810124b82661a5,0x808988760eb230c5bc11,0xf2335061053c0dc1b910,0xe7436082236924b04a06,0x76b17318480205054461,0x12c0b6c84c2700880024,0xc7b1238080002c73c3e8,0x43a0000004083,0x6c9002f62200e3434000,0x9d160002495c0f000603,0x5f21ec31e15a460001e2,0x3500058eaa80024c0128,0xc]]
def g251D11 := limbs80 #[#[0x50ff503fd10ef953bd54,0x6e00ff587fd41ff583fd,0x1803c7a4c81d2b94819c,0xc608160c01c3048d082c,0x1a2c1803858d160c01c2,0x6830070f1230e830048d,0x70e187c180385200a28,0x220c786830]]
def g251H11 := limbs80 #[#[0x22b926c3831004282440,0x1c06f1bb0c8a031cd0f7,0xe04000318f2471,0x3815c0741eb25f0a58c,0x1508e1df12b200007163,0xd1092100009151f000e0,0x8a500a0b00041751a000,0xf2328b982000d1920d5,0x41310219e60940552600,0xd0e49fb94d14e86]]
def g251D12 (j : Nat) := if j=0 then 0xc2881840803ff else 0
def g251H12 := limbs80 #[#[0xc0123000000101004160,0x2180000bbe4,0x28800fac1c000040,0xb200002c400]]
def g251L : Nat → Packing
  | 8 => (28,4,6,0,0,11,0,g251D8)
  | 9 => (75,3,6,0,0,13,0,g251D9)
  | 10 => (39,2,6,0,0,12,0,g251D10)
  | 11 => (8,1,6,0,0,9,0,g251D11)
  | 12 => (1,0,6,0,0,0,0,g251D12)
  | _ => emptyPacking
def g251I : Nat → Nat → Option (Nat × Nat)
  | 9 => lookupWord 7 53 3 11 5 2 g251H9
  | 10 => lookupWord 22 101 6 13 7 2 g251H10
  | 11 => lookupWord 12 59 6 12 6 2 g251H11
  | 12 => lookupWord 3 31 2 9 3 2 g251H12
  | _ => fun _ => none
def g251 : Forest := ⟨251,12,fun i => g251Y[i]?.getD (0,0),g251C,g251A,g251L,g251I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_0 : block g251 8 0 19=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_19 : block g251 8 19 9=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B8 : block g251 8 0 28=true := (@block_merge g251 8 0 19 9 g251P8_0 g251P8_19)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_0 : block g251 9 0 10=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_10 : block g251 9 10 51=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_61 : block g251 9 61 12=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_73 : block g251 9 73 2=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B9 : block g251 9 0 75=true := (@block_merge g251 9 0 61 14 (@block_merge g251 9 0 10 51 g251P9_0 g251P9_10) (@block_merge g251 9 61 12 2 g251P9_61 g251P9_73))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P10_0 : block g251 10 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P10_2 : block g251 10 2 28=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P10_30 : block g251 10 30 9=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B10 : block g251 10 0 39=true := (@block_merge g251 10 0 2 37 g251P10_0 (@block_merge g251 10 2 28 9 g251P10_2 g251P10_30))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P11_0 : block g251 11 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P11_2 : block g251 11 2 6=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B11 : block g251 11 0 8=true := (@block_merge g251 11 0 2 6 g251P11_0 g251P11_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P12_0 : block g251 12 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B12 : block g251 12 0 1=true := g251P12_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251T : checkedTables g251 12 := by
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
  · exact g251B8
  · exact g251B9
  · exact g251B10
  · exact g251B11
  · exact g251B12
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251G : graphValid g251 (boundsBefore K235) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low251 : Lower true (varsX 251) (graphGoal 251) 13 := lower_forest (g:=g251) (i:=0) (hints:=16777299) (before_sound K235 V235) g251G g251T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K251 := extendKnown K235 13 [(251,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V251 : Known true K251 := extend_ok (m:=251) V235 low251 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255R : Impossible true graph 13 sevenInputs.toFinset := by
  change Impossible true (graphGoal 255) 13 sevenInputs.toFinset
  exact cut_root (m:=255) (before_sound K251 V251) (4, 0, 251, 0, 13) (by decide +kernel) (by decide +kernel)

end PEqualNP.Outside.L_meta_49539

open PEqualNP.Outside.L_meta_49539 in
theorem PEqualNP.Outside.L_meta_49539 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 3, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 3, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 3, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 3, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 3, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 3, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o fit _ correct
  exact replaceShort g255R gates o fit correct

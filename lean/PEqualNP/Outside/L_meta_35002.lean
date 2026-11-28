import PEqualNP.Defs

-- The two-mode live-state and cofactor checker follows L_meta_1674 and L_meta_670.
-- The graph, restrictions and all search certificates below are for L_meta_35002.

-- Shared forest and cofactor certificates from L_meta_1674 and PR 11111 for L_meta_1677.
-- The original credit line is retained below. The two root certificates here cover the unpinned graph.

-- The checker and the bound certificates are adapted from PEqualNP/Outside/L_meta_1667.lean (Apache-2.0).
-- Two modes: u=false are monotone runs (AND, OR); u=true are runs up to complement, where negation is free.
namespace PEqualNP.Outside.L_meta_35002
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
def graph : Sig := (BitVec.ofNat 512 (word80 [0xffffffff,0xffffffffffffffffffff,0xfffefffefffefffefffc,0xfefefefeeeeeaa00ffff,0xffffffffffffffffffff,0xfffffffefffefffefffe,0xfffcfefefefeeeeeaa00]))
def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 2 && x 5) || (x 1 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 2 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 5 && x 7) || (x 6 && x 7)
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
  (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 2 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 2 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)
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
  (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 2 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 2 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)
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



def target (x : Fin 8 → Bool) : Bool := decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
def smallCircuit : Circuit := ⟨[⟨.or,[4,5]⟩,⟨.or,[1,2]⟩,⟨.or,[3,8]⟩,⟨.or,[0,6]⟩,⟨.or,[0,7]⟩,⟨.or,[3,7]⟩,⟨.or,[5,6]⟩,⟨.or,[7,14]⟩,⟨.and,[12,10]⟩,⟨.and,[13,11]⟩,⟨.and,[15,9]⟩,⟨.and,[8,1]⟩,⟨.or,[16,17]⟩,⟨.or,[20,18]⟩,⟨.or,[21,19]⟩], 22⟩

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
def g137Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3ff63ff63ff63ff63f,0xf63ff63ff63ff63ff63f])),(BitVec.ofNat 152 (word80 [0x492049204920492049,0x20492049204920492049]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xc7fbc7fbc7fbc7fbc7,0xfbc7fbc7fbc7fbc7fbc7])),(BitVec.ofNat 152 (word80 [0x924092409240924092,0x40924092409240924092]))),(0x0,0x0),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xf8fdf8fdf8fdf8fdf8,0xfdf8fdf8fdf8fdf8fdf8])),(BitVec.ofNat 152 (word80 [0x248124812481248124,0x81248124812481248124]))),(0x0,0x0)]
def g137C : List ColumnInfo := []
def g137A : List (List Nat) := [[],[115],[48],[48,112],[112,48],[112]]
def g137D3 (j : Nat) := if j=0 then 0x7 else 0
def g137L : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,g137D3)
  | _ => emptyPacking
def g137I (_ _ : Nat) : Option (Nat × Nat) := none
def g137 : Forest := ⟨137,3,fun i => g137Y[i]?.getD (0,0),g137C,g137A,g137L,g137I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g137P3_0 : block g137 3 0 1=true := by
  apply cellsBlock (ar:=3) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g137B3 : block g137 3 0 1=true := g137P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g137T : checkedTables g137 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g137 0 0 0 = true)
  · exact (rfl : block g137 1 0 0 = true)
  · exact (rfl : block g137 2 0 0 = true)
  · exact g137B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g137G : graphValid g137 (boundsBefore []) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low137 : Lower true (varsX 137) (graphGoal 137) 4 := lower_forest (g:=g137) (i:=0) (hints:=3) (before_sound [] baseKnown) g137G g137T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K137 := extendKnown [] 4 [(137,[]),(145,[67]),(146,[16,67]),(194,[16,99,67,84]),(196,[32,16,99,67,84]),(200,[48,16,33,98,66,84])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V137 : Known true K137 := extend_ok (m:=137) baseKnown low137 (by decide +kernel)
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
theorem g27G : graphValid g27 (boundsBefore K137) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low27 : Lower true (varsX 27) (graphGoal 27) 4 := lower_forest (g:=g27) (i:=0) (hints:=67) (before_sound K137 V137) g27G g27T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K27 := extendKnown K137 4 [(27,[]),(45,[33,84]),(54,[16,32,67,83]),(75,[96,16,49,67,84]),(83,[16,99,83]),(86,[16,32,67,99,83]),(89,[48,65,33,96,32,82]),(90,[16,48,32,66,98,82])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V27 : Known true K27 := extend_ok (m:=27) V137 low27 (by decide +kernel)
def g139Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfdf00fff81fc7e3ffb,0xe01fff03f8fc7ff7c03f])),(BitVec.ofNat 152 (word80 [0x45c09245142904808b,0x81248a28520901170249]))),((BitVec.ofNat 152 (word80 [0xe6a8703ffe007fc7cd,0x50e07ffc00ff8f9aa1c0])),(BitVec.ofNat 152 (word80 [0x96a9b6d618b228112d,0x536dac316450225aa6db]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfbb781ffffff8007f7,0x6f03ffffff000feede07])),(BitVec.ofNat 152 (word80 [0x235249820c0312204,0x6a49304180624408d492]))),(0x0,0x0),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x64ffe3ffffffff80c,0x9ffc7ffffffff0193ff8])),(BitVec.ofNat 152 (word80 [0x249204100400400,0x4924082008008000924]))),(0x0,0x0)]
def g139C : List ColumnInfo := [(2,0,137,0,4)]
def g139A : List (List Nat) := [[],[48]]
def g139D4 (j : Nat) := if j=0 then 0x1f else 0
def g139L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g139D4)
  | _ => emptyPacking
def g139I (_ _ : Nat) : Option (Nat × Nat) := none
def g139 : Forest := ⟨139,4,fun i => g139Y[i]?.getD (0,0),g139C,g139A,g139L,g139I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g139P4_0 : block g139 4 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g139B4 : block g139 4 0 1=true := g139P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g139T : checkedTables g139 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g139 0 0 0 = true)
  · exact (rfl : block g139 1 0 0 = true)
  · exact (rfl : block g139 2 0 0 = true)
  · exact (rfl : block g139 3 0 0 = true)
  · exact g139B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g139G : graphValid g139 (boundsBefore K27) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low139 : Lower true (varsX 139) (graphGoal 139) 5 := lower_forest (g:=g139) (i:=0) (hints:=115) (before_sound K27 V27) g139G g139T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K139 := extendKnown K27 5 [(139,[]),(141,[33]),(149,[33,67]),(150,[16,32,67]),(154,[16,48,32,66]),(195,[16,99,67,84]),(197,[32,16,99,67,84]),(209,[97,33,67,50,83]),(212,[32,65,99,83]),(216,[48,65,32,98,82])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V139 : Known true K139 := extend_ok (m:=139) V27 low139 (by decide +kernel)
def g147Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfe7d01c7fc0fc7cfe7,0xd01c7fc0fc7cfe7d01c7])),(BitVec.ofNat 152 (word80 [0x51d124928a290a051,0xd124928a290a051d1249]))),((BitVec.ofNat 152 (word80 [0x3f8b8e38fff007f3f8,0xb8e38fff007f3f8b8e38])),(BitVec.ofNat 152 (word80 [0x884b924930c3210884,0xb924930c3210884b9249]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x3fe7703ffffff803fe,0x7703ffffff803fe7703f])),(BitVec.ofNat 152 (word80 [0x100024924104020100,0x2492410402010002492]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xc018ffc0fffffffc01,0x8ffc0fffffffc018ffc0])),(BitVec.ofNat 152 (word80 [0x200049248208040200,0x4924820804020004924]))),(0x0,0x0)]
def g147C : List ColumnInfo := [(1,0,146,0,4)]
def g147A : List (List Nat) := [[],[116],[16],[16,116]]
def g147D4 (j : Nat) := if j=0 then 0x1f else 0
def g147L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g147D4)
  | _ => emptyPacking
def g147I (_ _ : Nat) : Option (Nat × Nat) := none
def g147 : Forest := ⟨147,4,fun i => g147Y[i]?.getD (0,0),g147C,g147A,g147L,g147I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g147P4_0 : block g147 4 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g147B4 : block g147 4 0 1=true := g147P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g147T : checkedTables g147 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g147 0 0 0 = true)
  · exact (rfl : block g147 1 0 0 = true)
  · exact (rfl : block g147 2 0 0 = true)
  · exact (rfl : block g147 3 0 0 = true)
  · exact g147B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g147G : graphValid g147 (boundsBefore K139) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low147 : Lower true (varsX 147) (graphGoal 147) 5 := lower_forest (g:=g147) (i:=0) (hints:=68) (before_sound K139 V139) g147G g147T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K147 := extendKnown K139 5 [(147,[]),(153,[48,65,33,32]),(166,[16,32,84]),(178,[64,81,32,50,49]),(198,[16,32,100,84]),(201,[97,33,50,67,84]),(202,[16,48,32,100,84]),(210,[64,97,32,50,49,83])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V147 : Known true K147 := extend_ok (m:=147) V139 low147 (by decide +kernel)
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
theorem g47G : graphValid g47 (boundsBefore K147) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low47 : Lower true (varsX 47) (graphGoal 47) 5 := lower_forest (g:=g47) (i:=0) (hints:=1363) (before_sound K147 V147) g47G g47T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K47 := extendKnown K147 5 [(61,[80,49,66,33])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V47 : Known true K47 := extend_ok (m:=47) V147 low47 (by decide +kernel)
def g55Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xe003ff80ffe03ffff0,0x3ffffe03f90b59b81c7])),(BitVec.ofNat 152 (word80 [0x41a8251a0a458a02a1,0xa84a0a458a00b1839249]))),((BitVec.ofNat 152 (word80 [0xfffc0000ffffc07fff,0xfc00ffffc068db448e38])),(BitVec.ofNat 152 (word80 [0x8130362c0c891304c1,0x306c0c891340d3049249]))),((BitVec.ofNat 152 (word80 [0xffffffff0000007fff,0xffff0000000ff02e7000])),(BitVec.ofNat 152 (word80 [0x5c0b8302f0e1c1701,0xc0702f0e1c0af02e36db]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x7fff,0xffffffffff99af6d003f])),(BitVec.ofNat 152 (word80 [0x1602c040b01020580a,0x280b00000190c686db6]))),((BitVec.ofNat 152 (word80 [0xffffffffffffff8000,0x6754f2ffc0])),(BitVec.ofNat 152 (word80 [0x18030000c00000600c,0x300c010202504504924]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g55C : List ColumnInfo := [(1,0,54,0,4)]
def g55A : List (List Nat) := [[],[16]]
def g55D4 (j : Nat) := if j=0 then 0x3f else 0
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
theorem g55G : graphValid g55 (boundsBefore K47) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low55 : Lower true (varsX 55) (graphGoal 55) 5 := lower_forest (g:=g55) (i:=0) (hints:=1348) (before_sound K47 V47) g55G g55T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K55 := extendKnown K47 5 [(55,[]),(59,[64,81,50,16]),(118,[80,97,66,48,49])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V55 : Known true K55 := extend_ok (m:=55) V47 low55 (by decide +kernel)
def g87Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xe001ffc07ff01ffe00,0x3fffff80ffd35632000f])),(BitVec.ofNat 152 (word80 [0x48d4128d0522c8549a,0x92522916299346225555]))),((BitVec.ofNat 152 (word80 [0xfffe00007fffffffff,0xc007ffff01a3adc80ff0])),(BitVec.ofNat 152 (word80 [0x80981b160644809813,0x36032244d030cc81111]))),((BitVec.ofNat 152 (word80 [0xffffffff80001fffff,0xfff80000003f407df000])),(BitVec.ofNat 152 (word80 [0x2e05c18178702e01c,0x380bc387033007d3333]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1fffff,0xfffffffffe663f7600ff])),(BitVec.ofNat 152 (word80 [0x130160205808130120,0x2404c00000643114aaaa]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffe00000,0x19dd38dff00])),(BitVec.ofNat 152 (word80 [0x1c01800060001c01c0,0x38070040808cd300cccc]))),(0x0,0x0),(0x0,0x0)]
def g87C : List ColumnInfo := []
def g87A : List (List Nat) := [[],[32,100]]
def g87D4 (j : Nat) := if j=0 then 0x1f else 0
def g87L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g87D4)
  | _ => emptyPacking
def g87I (_ _ : Nat) : Option (Nat × Nat) := none
def g87 : Forest := ⟨87,4,fun i => g87Y[i]?.getD (0,0),g87C,g87A,g87L,g87I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g87P4_0 : block g87 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g87B4 : block g87 4 0 1=true := g87P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g87T : checkedTables g87 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g87 0 0 0 = true)
  · exact (rfl : block g87 1 0 0 = true)
  · exact (rfl : block g87 2 0 0 = true)
  · exact (rfl : block g87 3 0 0 = true)
  · exact g87B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g87G : graphValid g87 (boundsBefore K55) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low87 : Lower true (varsX 87) (graphGoal 87) 5 := lower_forest (g:=g87) (i:=0) (hints:=16778820) (before_sound K55 V55) g87G g87T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K87 := extendKnown K55 5 [(87,[]),(117,[64,81,98,49])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V87 : Known true K87 := extend_ok (m:=87) V55 low87 (by decide +kernel)
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
theorem g91G : graphValid g91 (boundsBefore K87) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low91 : Lower true (varsX 91) (graphGoal 91) 7 := lower_forest (g:=g91) (i:=0) (hints:=16777283) (before_sound K87 V87) g91G g91T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K91 := extendKnown K87 7 [(91,[]),(109,[33,84])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V91 : Known true K91 := extend_ok (m:=91) V87 low91 (by decide +kernel)
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
theorem g143G : graphValid g143 (boundsBefore K91) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low143 : Lower true (varsX 143) (graphGoal 143) 6 := lower_forest (g:=g143) (i:=0) (hints:=1907) (before_sound K91 V91) g143G g143T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K143 := extendKnown K91 6 [(143,[]),(158,[16,32,48,64])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V143 : Known true K143 := extend_ok (m:=143) V91 low143 (by decide +kernel)
def g151Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffc00ffc07fe03fff,0xe00ffffe07f469d401c7])),(BitVec.ofNat 152 (word80 [0xa0a86a128d0a458a05,0x46a250a4b29029d49249]))),((BitVec.ofNat 152 (word80 [0xfffff00007fffc07f,0xfff007fff813a68c0e38])),(BitVec.ofNat 152 (word80 [0xc1304c1b160c891309,0x84c360c924d1a28c9249]))),((BitVec.ofNat 152 (word80 [0xfffffffff8000007f,0xfffff800000bc8b47000])),(BitVec.ofNat 152 (word80 [0x5c1705c182f0e1c2e,0x70382f1c70bc8b5b6db]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xf0000000000000007f,0xffffffffffe6fe67803f])),(BitVec.ofNat 152 (word80 [0x60180602030102030,0x8040300000654212492]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffffff80,0x1911bbffc0])),(BitVec.ofNat 152 (word80 [0x80200800040000040,0x10080400000000024924]))),(0x0,0x0)]
def g151C : List ColumnInfo := [(1,0,150,0,5)]
def g151A : List (List Nat) := [[],[16]]
def g151D5 (j : Nat) := if j=0 then 0x3f else 0
def g151L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g151D5)
  | _ => emptyPacking
def g151I (_ _ : Nat) : Option (Nat × Nat) := none
def g151 : Forest := ⟨151,5,fun i => g151Y[i]?.getD (0,0),g151C,g151A,g151L,g151I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g151P5_0 : block g151 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g151B5 : block g151 5 0 1=true := g151P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g151T : checkedTables g151 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g151 0 0 0 = true)
  · exact (rfl : block g151 1 0 0 = true)
  · exact (rfl : block g151 2 0 0 = true)
  · exact (rfl : block g151 3 0 0 = true)
  · exact (rfl : block g151 4 0 0 = true)
  · exact g151B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g151G : graphValid g151 (boundsBefore K143) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low151 : Lower true (varsX 151) (graphGoal 151) 6 := lower_forest (g:=g151) (i:=0) (hints:=1860) (before_sound K143 V143) g151G g151T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K151 := extendKnown K143 6 [(151,[]),(157,[48,65,16]),(199,[16,32,100,84])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V151 : Known true K151 := extend_ok (m:=151) V143 low151 (by decide +kernel)
def g155Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfe1ff00ff87f87ffc0,0x7fff8fffd8b95000f0ff])),(BitVec.ofNat 152 (word80 [0x1440a0a05101100285,0x5012008488941111111]))),((BitVec.ofNat 152 (word80 [0x1ffff0007ff87fff,0x807ff1fc2b1e600f0f00])),(BitVec.ofNat 152 (word80 [0x5882c0c1620a010b06,0x160a0411291e43333333]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1fffffff80007fff,0xff8001ff941fb0f0000f])),(BitVec.ofNat 152 (word80 [0x610b0505802c222c08,0x182c48a01416b6666666]))),((BitVec.ofNat 152 (word80 [0xffe000000000007fff,0xfffffe000be4bf000ff0])),(BitVec.ofNat 152 (word80 [0x800c06060430443010,0x203000c20260b4444444]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffff8000,0x6442cffff000])),(BitVec.ofNat 152 (word80 [0x1008080040004020,0x40400100000008888888]))),(0x0,0x0)]
def g155C : List ColumnInfo := [(1,0,154,0,5),(2,0,153,0,5),(8,0,147,0,5),(16,0,139,0,5)]
def g155A : List (List Nat) := [[],[64,49]]
def g155D6 (j : Nat) := if j=0 then 0x4e09f else 0
def g155L : Nat → Packing
  | 6 => (1,0,2,0,0,0,0,g155D6)
  | _ => emptyPacking
def g155I (_ _ : Nat) : Option (Nat × Nat) := none
def g155 : Forest := ⟨155,6,fun i => g155Y[i]?.getD (0,0),g155C,g155A,g155L,g155I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g155P6_0 : block g155 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g155B6 : block g155 6 0 1=true := g155P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g155T : checkedTables g155 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g155 0 0 0 = true)
  · exact (rfl : block g155 1 0 0 = true)
  · exact (rfl : block g155 2 0 0 = true)
  · exact (rfl : block g155 3 0 0 = true)
  · exact (rfl : block g155 4 0 0 = true)
  · exact (rfl : block g155 5 0 0 = true)
  · exact g155B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g155G : graphValid g155 (boundsBefore K151) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low155 : Lower true (varsX 155) (graphGoal 155) 7 := lower_forest (g:=g155) (i:=0) (hints:=67) (before_sound K151 V151) g155G g155T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K155 := extendKnown K151 7 [(155,[]),(171,[84]),(173,[33,84]),(181,[33,67,83]),(182,[16,32,67,83]),(203,[96,16,49,67,84]),(211,[16,99,83]),(214,[16,32,67,99,83]),(217,[48,65,33,96,32,82]),(218,[16,48,32,66,98,82])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V155 : Known true K155 := extend_ok (m:=155) V151 low155 (by decide +kernel)
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
def K167 := extendKnown K155 6 [(185,[48,65,82,16,32])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V167 : Known true K167 := extend_ok (m:=167) V155 low167 (by decide +kernel)
def g179Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x1fe1fe01fe1fc3ffc,0x7ffe3ff1ecd460071c7])),(BitVec.ofNat 152 (word80 [0x141441414144088028,0x50a04802424506249249]))),((BitVec.ofNat 152 (word80 [0xfe001fffe001ffc3ff,0xf80ffc7fe17493038e38])),(BitVec.ofNat 152 (word80 [0x181881818188100830,0x60c08104095412249249]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1ffffffe0003ff,0xfff0007ffcc2f51c003f])),(BitVec.ofNat 152 (word80 [0xa0a10a0a0a00a11140,0x810512280082e1492492]))),((BitVec.ofNat 152 (word80 [0xffffe00000000003ff,0xffffff80003b4be00fc0])),(BitVec.ofNat 152 (word80 [0xc0c00c0c0c10c22181,0x2060030902a49492492]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffffffffffc00,0x30628fff000])),(BitVec.ofNat 152 (word80 [0x10010101001000202,0x4080040000000924924]))),(0x0,0x0)]
def g179C : List ColumnInfo := [(1,0,178,0,5)]
def g179A : List (List Nat) := [[],[84],[16],[16,84],[64,81],[64,81,16],[80,65,16],[80,65]]
def g179D5 (j : Nat) := if j=0 then 0x3f else 0
def g179L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g179D5)
  | _ => emptyPacking
def g179I (_ _ : Nat) : Option (Nat × Nat) := none
def g179 : Forest := ⟨179,5,fun i => g179Y[i]?.getD (0,0),g179C,g179A,g179L,g179I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g179P5_0 : block g179 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g179B5 : block g179 5 0 1=true := g179P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g179T : checkedTables g179 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g179 0 0 0 = true)
  · exact (rfl : block g179 1 0 0 = true)
  · exact (rfl : block g179 2 0 0 = true)
  · exact (rfl : block g179 3 0 0 = true)
  · exact (rfl : block g179 4 0 0 = true)
  · exact g179B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g179G : graphValid g179 (boundsBefore K167) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low179 : Lower true (varsX 179) (graphGoal 179) 6 := lower_forest (g:=g179) (i:=0) (hints:=68) (before_sound K167 V167) g179G g179T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K179 := extendKnown K167 6 [(179,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V179 : Known true K179 := extend_ok (m:=179) V167 low179 (by decide +kernel)
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
theorem g213G : graphValid g213 (boundsBefore K179) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low213 : Lower true (varsX 213) (graphGoal 213) 8 := lower_forest (g:=g213) (i:=0) (hints:=33555972) (before_sound K179 V179) g213G g213T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K213 := extendKnown K179 8 [(213,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V213 : Known true K213 := extend_ok (m:=213) V179 low213 (by decide +kernel)
def g63Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffffffffffffffffff,0xffa617c8e127cb00f0ff])),(BitVec.ofNat 152 (word80 [0x14000a8004a001480,0x14a4148880028a111111]))),((BitVec.ofNat 152 (word80 [0xffffc0000ffffc0,0x7940b93e83b60f0f00])),(BitVec.ofNat 152 (word80 [0xa600530036c009900,0x666940992c0382333333]))),((BitVec.ofNat 152 (word80 [0xfffffffff000000,0x1cf88f857962f00000])),(BitVec.ofNat 152 (word80 [0x3380a9c02a700ade02,0xb81c708b857162777777]))),((BitVec.ofNat 152 (word80 [0xfffffffffffffff,0xff216395b13d3d00000f])),(BitVec.ofNat 152 (word80 [0x5c0ace02b380ace014,0xc0016315313d35eeeeee]))),((BitVec.ofNat 152 (word80 [0xfff000000000000000,0x115e685ddcf0000ff0])),(BitVec.ofNat 152 (word80 [0x600cf0033c00cf0027,0x100a6051dc70cccccc]))),(0xcea977125e06fff000,(BitVec.ofNat 152 (word80 [0x800f0003c000f00038,0x28964120c04888888]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g63C : List ColumnInfo := [(2,0,61,0,5),(8,0,55,0,5),(1,8,54,0,4),(32,4,27,0,4)]
def g63A : List (List Nat) := [[],[80,65,50]]
def g63D6 (j : Nat) := if j=0 then 0x4e13f else 0
def g63L : Nat → Packing
  | 6 => (1,0,2,0,0,0,0,g63D6)
  | _ => emptyPacking
def g63I (_ _ : Nat) : Option (Nat × Nat) := none
def g63 : Forest := ⟨63,6,fun i => g63Y[i]?.getD (0,0),g63C,g63A,g63L,g63I⟩
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
  · exact (rfl : block g63 5 0 0 = true)
  · exact g63B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63G : graphValid g63 (boundsBefore K213) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low63 : Lower true (varsX 63) (graphGoal 63) 7 := lower_forest (g:=g63) (i:=0) (hints:=1347) (before_sound K213 V213) g63G g63T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K63 := extendKnown K213 7 [(63,[]),(126,[16,32,48,64,80,96])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V63 : Known true K63 := extend_ok (m:=63) V213 low63 (by decide +kernel)
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
def K95 := extendKnown K63 8 [(95,[]),(125,[32,49,64,81,96])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V95 : Known true K95 := extend_ok (m:=95) V63 low95 (by decide +kernel)
def g111Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3fffffffffffffffe,0xc93d3b130c58000003ff])),(BitVec.ofNat 152 (word80 [0x581440548129029028,0xc9143a1204525294a529]))),((BitVec.ofNat 152 (word80 [0xfc00fffe0003fff801,0xf605502e2d9001f07c00])),(BitVec.ofNat 152 (word80 [0x90a602980db01320cd,0xf20550220d80c6318c63]))),((BitVec.ofNat 152 (word80 [0xfffffffc000000,0x39c4d6d38a803e0f8000])),(BitVec.ofNat 152 (word80 [0xe13804e009c01bc170,0x3144d6138880c6318c63]))),((BitVec.ofNat 152 (word80 [0xfffffffffffffe,0x428bca0bd9efc000001f])),(BitVec.ofNat 152 (word80 [0x1c017002e005c0180,0x289c009d9898c6318c6]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffff00000000000000,0x22fa317cb680000fffe0])),(BitVec.ofNat 152 (word80 [0x98013002600200,0xaa014c3205294a5294]))),((BitVec.ofNat 152 (word80 [1,0x9d26ecc07137fff00000])),(BitVec.ofNat 152 (word80 [0x200e001c003800400,0xc2228c02036318c6318]))),(0x0,0x0),(0x0,0x0)]
def g111C : List ColumnInfo := [(2,0,109,0,7)]
def g111A : List (List Nat) := [[],[33],[48,101],[48,33,101]]
def g111D7 (j : Nat) := if j=0 then 0x7f else 0
def g111L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g111D7)
  | _ => emptyPacking
def g111I (_ _ : Nat) : Option (Nat × Nat) := none
def g111 : Forest := ⟨111,7,fun i => g111Y[i]?.getD (0,0),g111C,g111A,g111L,g111I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P7_0 : block g111 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g111B7 : block g111 7 0 1=true := g111P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111T : checkedTables g111 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g111 0 0 0 = true)
  · exact (rfl : block g111 1 0 0 = true)
  · exact (rfl : block g111 2 0 0 = true)
  · exact (rfl : block g111 3 0 0 = true)
  · exact (rfl : block g111 4 0 0 = true)
  · exact (rfl : block g111 5 0 0 = true)
  · exact (rfl : block g111 6 0 0 = true)
  · exact g111B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111G : graphValid g111 (boundsBefore K95) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low111 : Lower true (varsX 111) (graphGoal 111) 8 := lower_forest (g:=g111) (i:=0) (hints:=16778579) (before_sound K95 V95) g111G g111T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K111 := extendKnown K95 8 [(111,[]),(123,[48,65,82,96,33,16])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V111 : Known true K111 := extend_ok (m:=111) V95 low111 (by decide +kernel)
def g119Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffc0007fffffff001f,0xfd1608e6de84f0000f0f])),(BitVec.ofNat 152 (word80 [0xa8435084a105202c0,0x511608a64284a5555555]))),((BitVec.ofNat 152 (word80 [0xffffff8000ffffffe0,0x3acfa16013c20f0f0f0])),(BitVec.ofNat 152 (word80 [0x130026006c00640480,0x9ba41806001c01111111]))),((BitVec.ofNat 152 (word80 [0xffffffffff00000000,0x773d2b26530f0f0000])),(BitVec.ofNat 152 (word80 [0x5c0038007001780700,0xe027382a261203333333]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffffffff,0xfc81271697b3d00000ff])),(BitVec.ofNat 152 (word80 [0x6029405280a580500a,0x1271095235aaaaaaa]))),(0x45d4e0f96d000fff00,(BitVec.ofNat 152 (word80 [0x8031806300c6009813,0x40c440996108888888]))),(0x33a4dd980e26ff00000,(BitVec.ofNat 152 (word80 [0x3e007c00f800e01c,0x1845d180e06ccccccc]))),(0x0,0x0),(0x0,0x0)]
def g119C : List ColumnInfo := [(2,0,117,0,5),(32,0,87,0,5)]
def g119A : List (List Nat) := [[],[32,100],[64,81,98],[96,81,66]]
def g119D6 (j : Nat) := if j=0 then 0x20bf else 0
def g119L : Nat → Packing
  | 6 => (1,0,1,0,0,0,0,g119D6)
  | _ => emptyPacking
def g119I (_ _ : Nat) : Option (Nat × Nat) := none
def g119 : Forest := ⟨119,6,fun i => g119Y[i]?.getD (0,0),g119C,g119A,g119L,g119I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P6_0 : block g119 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g119B6 : block g119 6 0 1=true := g119P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119T : checkedTables g119 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g119 0 0 0 = true)
  · exact (rfl : block g119 1 0 0 = true)
  · exact (rfl : block g119 2 0 0 = true)
  · exact (rfl : block g119 3 0 0 = true)
  · exact (rfl : block g119 4 0 0 = true)
  · exact (rfl : block g119 5 0 0 = true)
  · exact g119B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119G : graphValid g119 (boundsBefore K111) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low119 : Lower true (varsX 119) (graphGoal 119) 7 := lower_forest (g:=g119) (i:=0) (hints:=16778564) (before_sound K111 V111) g119G g119T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K119 := extendKnown K111 7 [(119,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V119 : Known true K119 := extend_ok (m:=119) V111 low119 (by decide +kernel)
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
theorem g159G : graphValid g159 (boundsBefore K119) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low159 : Lower true (varsX 159) (graphGoal 159) 9 := lower_forest (g:=g159) (i:=0) (hints:=1859) (before_sound K119 V119) g159G g159T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K159 := extendKnown K119 9 [(159,[]),(190,[16,32,48,64,80])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V159 : Known true K159 := extend_ok (m:=159) V119 low159 (by decide +kernel)
def g183Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xe03ffff800fffffe03,0xfe43aa433a0000f00f0f])),(BitVec.ofNat 152 (word80 [0x458a01506a0940a458,0xa6430a42321111111111]))),((BitVec.ofNat 152 (word80 [0xffc07fffff001ffffc,0x34e5bc0c1000f00f0f0])),(BitVec.ofNat 152 (word80 [0x891302604c0d80c891,0x334e5a40011111111111]))),((BitVec.ofNat 152 (word80 [0x7fffffffe00000,0xd3729e2500f00f0000])),(BitVec.ofNat 152 (word80 [0xe1c0b80700e02f0e1,0xc053728e253333333333]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x7fffffffffffff,0xf92229bd6b0f000000ff])),(BitVec.ofNat 152 (word80 [0x10202c0280500b0000,0x2021bd486666666666]))),((BitVec.ofNat 152 (word80 [0xffff80000000000000,0x98c67ad8f0000fff00])),(BitVec.ofNat 152 (word80 [0x300300600c0102,0x808430c84444444444]))),(0x0,0x0),(0x665142404fffff00000,(BitVec.ofNat 152 (word80 [0x40040080100000,0x8888888888]))),(0x0,0x0)]
def g183C : List ColumnInfo := [(1,0,182,0,7)]
def g183A : List (List Nat) := [[],[16]]
def g183D7 (j : Nat) := if j=0 then 0x7f else 0
def g183L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g183D7)
  | _ => emptyPacking
def g183I (_ _ : Nat) : Option (Nat × Nat) := none
def g183 : Forest := ⟨183,7,fun i => g183Y[i]?.getD (0,0),g183C,g183A,g183L,g183I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183P7_0 : block g183 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g183B7 : block g183 7 0 1=true := g183P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183T : checkedTables g183 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g183 0 0 0 = true)
  · exact (rfl : block g183 1 0 0 = true)
  · exact (rfl : block g183 2 0 0 = true)
  · exact (rfl : block g183 3 0 0 = true)
  · exact (rfl : block g183 4 0 0 = true)
  · exact (rfl : block g183 5 0 0 = true)
  · exact (rfl : block g183 6 0 0 = true)
  · exact g183B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183G : graphValid g183 (boundsBefore K159) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low183 : Lower true (varsX 183) (graphGoal 183) 8 := lower_forest (g:=g183) (i:=0) (hints:=1348) (before_sound K159 V159) g183G g183T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K183 := extendKnown K159 8 [(183,[]),(187,[64,81,50,16]),(246,[80,97,66,48,49])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V183 : Known true K183 := extend_ok (m:=183) V159 low183 (by decide +kernel)
def g215Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3ffe001ffffff01fc,0x5f8b8545600001f0001f])),(BitVec.ofNat 152 (word80 [0x588544d44944522c50,0x5f83814465294a5294a5]))),((BitVec.ofNat 152 (word80 [0xfffffffe001ffffe01,0x98b361b240003e007fe0])),(BitVec.ofNat 152 (word80 [0x900980980d80644899,0x989300b0410842108421]))),((BitVec.ofNat 152 (word80 [0x3ffffffffe0000002,0x54dc3874c007c00f8000])),(BitVec.ofNat 152 (word80 [0xe02e00e00e017870e0,0x549c3870c318c6318c63]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x3fffffffffffffffe,0xa08ef66320f8000003ff])),(BitVec.ofNat 152 (word80 [0x13009009009800002,0x200c76030a5294a5294a]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfc0000000000000002,0x4970938fdf00000ffc00])),(BitVec.ofNat 152 (word80 [0x1c00e00e00e008102,0x160830f0c6318c6318c]))),((BitVec.ofNat 152 (word80 [1,0x37050a181ffffff00000])),(BitVec.ofNat 152 (word80 [0x20010010010000000,0x108421084210]))),(0x0,0x0)]
def g215C : List ColumnInfo := [(2,0,213,0,8),(1,0,214,0,7),(4,0,211,0,7),(16,0,199,0,6),(64,0,151,0,6),(5,0,210,0,5),(17,0,198,0,5),(18,0,197,0,5),(20,0,195,0,5),(65,0,150,0,5),(68,0,147,0,5),(128,0,87,0,5),(19,0,196,0,4),(21,0,194,0,4),(69,0,146,0,4),(129,0,86,0,4),(132,0,83,0,4)]
def g215A : List (List Nat) := [[],[32,100]]
def g215D4 := limbs80 #[#[0x32a87993746047054d43,0x80dc56550f1c304c02e2,0x73c8b0db92a921e38e0b,0x2a74e39259171181538,0xf624c3021e730b22e23]]
def g215D5 := limbs80 #[#[0x5d9544c3965915354130,0x4c23de0576551308fb80,0xe0176d51308ef825d954,0x503308ef825d2654c23e,0x9eb825d350cc27660e75,0xdc154cc27660f7055330,0xcc23de057655330cb964,0xe0974997308ef825d954,0xd4d40f195350d505023b,0xa9f8654d43d023be0976,0xdc153d033658f7054f40,0xd03275d163d4f409b984,0xe095458f40a5f8558f53,0x58f40ad9801d563d03a3,0xacd821d563d02b560475,0x9d563d02b6e017558f40,0x5427ae0974d4150c5f75,0x54f7050f508ef825d363,0x50f50cd963dc143d4356,0x97985dc143d432e59370,0x5d943d423de057650f50,0x50f0fd977454d438ef82,0x6046554d43a798019553,0x54d438f7815d95350e9d,0xd9b741c15350ef460470,0x1955350f361db7054d43,0x50ed56046554d43b5980,0xe1d6519543c75655c465,0x59543cf1805c46550e1f,0xceb721c16550f3cdc470,0xdc16550f3cdc77059543,0x50f3c2037159543ceb72],#[0xdd37359543cf380dc565,0x58a43ecb8054d6290f27,0x8ed86dc95490eb360f54,0x5516014f36e1d5358053,0x14fb4e015358453aeb82,0xe015358853ae78255161,0x54c538ef875516214fb2,0xcdb76dc15314fa659370,0x5c46054f36e037654c53,0x54f3cd917118153cf164,0xe096418153af38159060,0xd81538fb875906054eba,0xaeb825936054ebce0564,0x5d36054e3de0574d8153,0x54ebae0954d81538ef82,0x60c74d8153e3b5495360,0xd8153cb9741d36054eb6,0xaeb825d36054ebce0574,0x5906454e73e0974d4d53,0x94e73e0974d4e538bf87,0xe0176d4e53b4f825d353,0x3c00ae5811c964d4f96,0xfc390cc2d09c2106c15,0x1e0721b06615c5112c45,0x2a0a2270962408a2107e,0x360d2330c6300ba2d0ae,0x4450b414f63c0ea390de,0x5053b4d52f4a52347517,0x5c56b5955f5655353547,0x6859b6558f625835f577,0x7b1e6781da751ce721b9,0x872168420a811fe7e1f2],#[0x2418d22e8a222,0x1020800000000000,0x0,0x90400000000000,0x0,0xe2300400000000000000,0x6182]]
def g215H5 := limbs80 #[#[0x15000000400034cb,0x2000000000000000320]]
def g215D6 := limbs80 #[#[0x27db82ca987595354130,0xbb2e7a8661d654f50cc,0x277b92caa067965d433,0x439dee4b26a1a755163d,0x50e7ab88caa1cf970195,0xa439eee2b2a873edc165,0x114f6ca9ac029ecd5358,0x4c53d9aa6b10a7b554d6,0x6054e6fbb2a629e9d645,0x59353cbaeda9ca77c5c4,0xd504c3f4a92a0904ef72,0x54d30df2c8a8261f654,0xc9544c36eb22a6987db7,0x7655130d7ac8aa2617bd,0x5c3544c27fbb2a8984fd,0xd76d5130bbae7aa2617e,0xfdd5644c37db82c8984f,0xff7459530df6e0b2a613,0xf654d40cc27eba4ca984,0x6f96550330f72a8a0661,0x1f654f50cc2fd3aa8198,0x85f974d4330fb2e7a866,0x61be5db50cc37cb2ea19,0x986dd6454f30fb6e0a9e,0x6617bdc954cc2fdb82a9,0x9984fd7655330d7ac8aa,0xa661775cf54cc27fbb2a,0xcb984ff75593309faeda,0x32e613fdd165cc37db82,0xaa0a07b943541409fae9,0x8a8281ded4d50503bca9,0x9a86a07bb7050d40f72a],#[0xeaa1a81af59543503cea,0xb82a6a05bf7550d40b7a,0x2e1a9a813fdd953502fd,0xebb6a6a05bd74d4d40bf,0x5ee4aa281eedc1545027,0x7db82caa05bf7355140f,0x9fee6b2a81bbdc965503,0x3cea9a87a04fd7399540,0xb7aeaa1e81af59543d0,0x2fdb82a7a05bf7550f4,0x409faeca9e81b758d53d,0xd036eb1ea7a04ff7654f,0xf409faeda9e816f5d353,0x3d027fbaac7a06bd5458,0x8f40dbaeab1e81b71d56,0x54d036fbaac7a06de755,0x59740b7ee6aa681ebdc9,0xf505427eb9ccba04ff73,0x4d4150bf2e7a82a1de54,0x8d43543aea9a86a85f97,0x7054d509feeca1aa1b7d,0x5d363543bdb82a6a85fb,0xf7255150bf6e0aa2a13f,0xf5cf64542f7b92c8a85e,0x5d5350f50bf6e0a1ea13,0xaf59143d436eb1a87a87,0x4ff7650f509faeca1ea1,0x1bedc163d43bdb82a7a8,0x85ef72553509fee8b1ea,0xa1bbdc964d42f7b92c9a,0xa1edd53d81439fee6b26,0xa873f5d76050f5eaa6c0],#[0x6a1dbf7454d43bf6e0a9,0x9a879fd955350f3e32aa,0xa6a1fd87054d439faeca,0xa9a8777dc95350fedb82,0x2a6a1f9e5454d43f3aa8,0xaa9a87e7dd15350fce3a,0xb2a6a1f5f6554d43eb8c,0xeb29a87e79525350f6e3,0xba6a6a1dde7694d43bba,0x2e032a879fd975350ede,0xeb28caa1df57119543bf,0xf6e0b2a873f9d86550f3,0x3fb2acaa1df77159543b,0xdf6e0b2a87be1c16550f,0xf7bb8acaa1cff7059543,0x39fee6b2a87b7dcd6550,0xe7eb9ccaa1e7f659954,0x43ddaa8b14873f5c3655,0x90fedb82a721eef5458a,0x243bdee4aa487b7dd953,0x490f3eb2aa921ddf7355,0x5243bbae7aa4879f9955,0x6014f7caa2c029e7d65d,0x58453deaa8b08a7be951,0x16214f76aa2c429ef654,0x454c53fb6e0a98a7bb95,0xc95414f6fbb2a629edd6,0x64950539feecaa0a77bd,0x5906054e7ebb4a829ebd,0xa7618153df6c8302a7be,0xed8b6054f7cb16c0a9df,0xfb63d8153fb6a7b02a7b],#[0xbe1936054fedb9ec0a9e,0xefa64d8153df2c9b02a7,0x73f5d36054f7db26c0a9,0x9efb72d8153df2e5b02a,0xa7be5536054f7db9ec0a,0xa9efb54d8153df4a9b02,0x2a7be5d36054f7c3a6c0,0x4a9efb74d8153df4e9b0,0x9aa73f5d36254efdb82c,0xa8a9ddf7355153bbae9a,0x2a2a7cfd525454eeeb9c,0x2c8a9ebd6419153d7ec9,0x4b22a77ddc56454efdb8,0x24c8a9df97099153bdee,0xe5b22a73f5c36454f5fb,0xba6a729f5e54d4e539fa,0xce9a9ca7d75d35394eee,0x7b92c9a9ddd7395253eb,0xd8e4b26a73fdc164d4ef,0x7fb92c9a9eef7259353d,0x101d81801280b0078002,0x83c03a83703182c02682,0x6685d05785204c847041,0x508187c07887506f86c0,0x89809489108f88a08688,0xaa8a70a38a209e89d099,0xf0bb8ba0b68b30b18b00,0x8d40ce8cd0cb8c80c28b,0xe68e50e18e00de8db0d9,0xf0fb8f80f48f10ed8ea0,0x91210e90d1099081048f,0x2a92712191e11a919115],#[0xd13993813493112d92c1,0x95415094f14b94614293,0x6c96b169966162959155,0x317f97e17897316f96e1,0x99a19699318d98a18698,0xb09a91a59a21a099d19b,0x71c39c01be9bb1b79b61,0x9d81d69d51d19ce1ca9c,0xf29ef1eb9e81e09dd1db,0x9205a04202a011ff9fa1,0xa2021ea1b217a1220ca0,0x32a2d229a28226a25223,0x7243a42240a3d239a382,0xa5c258a55251a4c248a4,0x74a7126da6a264a6325f,0x9285a84282a7f27ba782,0xaa62a2a9d299a98292a8,0xbcabb2b5ab22aeaad2a9,0x32cface2ccac72c5ac42,0xae42e2add2d9ad82d6ad,0xf6af32efaec2eaae92e5,0x7305b02300aff2fbafa2,0xb1a316b1330fb0c30ab0,0xe00d0f27b24322b1f31d,0x83f8020f06e00f8010b,0xb078020ae00b80106e0,0x6e0080e004403c2e00b,0xe0081b8020607081b802,0x8020f090d0c101b80206,0x82c10b0408042e0041b,0x400200082c1002410341,0x81001810018100041030],#[0x4106040001004209040,0x81043d042810418102,0x10400200080e8820,0x10904241230408101041,0x41034209041410424,0x4100081010410100101,0x504100002043c2420107,0x4104810a0c100041030,0x101000c100101030108,0x4105041046260061,0x41002d0c20b430804100,0x2042d042830410104050,0xc1014104001040003c10,0x10418100080020342c10,0x21040410207041c10404,0x4003000400004002841,0x8a842c30404841090408,0x20b0424100000004a109,0x4003048810321081084,0x80205e0080010000000b,0x10004100000040010007,0x6101030484144030820,0x588104040c8420000103,0xb048810b058810b0,0xc0828442c1c010181,0x14160050c16260080c1,0x89803010c84243050c10,0x20418100002000800025,0x8410006260090c10006,0x4100101c107041000400,0xc10b0400304021040008,0x400304003042c162040],#[0x2]]
def g215H6 := limbs80 #[#[0x355bb0c0109400b1463,0x5644000000f8013c1822,0x83b32fc30f4800003301,0x45c3ab40d3ff4731072d,0x21d000e251a46013a8d,0xc1220932345200000000,0xc32d4b000b00503000,0x417000a54e4e00073e0,0x12e00000025300,0x74243d000a4c439,0x3735d1a1ad000e0e0000,0xf38f3440fea203654,0x1331823cd4620a000000,0xde31927921d28207cb31,0xf0b250000000f196b054,0x8800000031f551000884,0xe40461181ba2000021cd,0xb4a82a5556490000002a,0x81105c22aaaaaf20dc0c,0xe000f262166b2c2b229f,0x53734130852c506000c1,0x54f000514c02000824]]
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
theorem g215G : graphValid g215 (boundsBefore K183) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low215 : Lower true (varsX 215) (graphGoal 215) 10 := lower_forest (g:=g215) (i:=0) (hints:=16778820) (before_sound K183 V183) g215G g215T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K215 := extendKnown K183 10 [(245,[64,81,98,49])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V215 : Known true K215 := extend_ok (m:=215) V183 low215 (by decide +kernel)
def g219Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xe007ffffe1ffff9164,0xdc16e000000fc0000fff])),(BitVec.ofNat 152 (word80 [0x44510a204404101144,0xcc00e249249249249249]))),((BitVec.ofNat 152 (word80 [0xfff800fffe1ff8318b,0x3c89500003f000fff000])),(BitVec.ofNat 152 (word80 [0x80602c028040213083,0x3c0140c30c30c30c30c3]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffff00001fffda3d,0x31312000fc003f00003f])),(BitVec.ofNat 152 (word80 [0x80300b0881400a39,0x31110186186186186186]))),((BitVec.ofNat 152 (word80 [0xffffffffffe000462a,0x8b87903f00000003ffc0])),(BitVec.ofNat 152 (word80 [0x902404c0009824628,0x3861514514514514514]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x4984,0x67ec8fc000003ffc0000])),(BitVec.ofNat 152 (word80 [0xe038070110e044104,0x42ec8618618618618618]))),((BitVec.ofNat 152 (word80 [0x2651,0x42404fffffffc0000000])),(BitVec.ofNat 152 (word80 [0x100400800010000000,0x820820820820820]))),(0x0,0x0)]
def g219C : List ColumnInfo := [(1,0,218,0,7),(2,0,217,0,7),(8,0,211,0,7),(16,0,203,0,7),(64,0,155,0,7),(128,0,91,0,7),(3,0,216,0,5),(9,0,210,0,5),(10,0,209,0,5),(17,0,202,0,5),(18,0,201,0,5),(24,0,195,0,5),(65,0,154,0,5),(66,0,153,0,5),(72,0,147,0,5),(80,0,139,0,5),(19,0,200,0,4),(25,0,194,0,4),(73,0,146,0,4),(74,0,145,0,4),(82,0,137,0,4),(129,0,90,0,4),(130,0,89,0,4),(136,0,83,0,4),(144,0,75,0,4),(192,0,27,0,4)]
def g219A : List (List Nat) := [[],[97,67],[16,99],[16,48,64,96],[48,100],[48,65,96,16],[64,49],[64,97,48,49],[96,16,49,67],[96,65]]
def g219D4 := limbs80 #[#[0x10c7060f915c87254110,0x30d095539259171d49]]
def g219D5 := limbs80 #[#[0x90221c69765495048110,0x71543204421bf26c3aca,0xa0a9a64a8e4088758549,0x221bc3834c951c8110f,0x354720443aa2e6a9aa39,0x1c3b02a964088674e0d7,0x2215e39760552c8110cf,0x485304421f32fc32a790,0xb2a6490a60887705d132,0x21dc1754c9214c110f60,0x85304437830a99242982,0x2aa690a60886f0e15324,0x1d517454d514c110f28b,0x530443a62e8aa2a29822,0xae8a9a60885d464f5454,0xe5391595534c110e2cb2,0x30443ac2eaa924318221,0x6a8c60884f4e4d85486,0x3174551518c110ce8baf,0x4427a726c0ea518221d,0x6b2c60884f4e4d81d523,0x1434c92150110c6dc3f0,0x443e42a8a9242a0221f8,0x10a80887585d55248540,0x985d62150110d98c2aa9,0x43c62a9b12a2a02211f3,0x8a80886cc55382545404,0x3dcd5150110b98ca6a6a,0x2e632b2a2a2a02219d38,0xa80885e8648845454044,0x20d6550110bc8c9908a8,0x1b10fc1acaa0221a9b84],#[0x808847c65f8254640443,0x895290110cb9c3aa8a8c,0xe32fc0aa920221c69755,0x8874555173547404423,0x9625411086ecbf06b2e8,0x2c4a92a2a822186f85dc,0x886d8e095254550443cc,0x5154110f28b1aa6a8aa0,0x7b9aa2a8221d537354d,0x879858952945504433a7,0x154110db0c12a528aa08,0x4ba6e2a8221b61825487,0x792d8d524c950442bc12,0x54110d34c32a4992a088,0xc0c64a8221a598654d32,0x9a619528c9504436c2a4,0x4110db0a9303212a0886,0x12a4a8221a698654a425,0xae4d62549504434d706b,0x110ba4c9cc4a92a08859,0x2a4a8221761911c95254,0x6507254950442e932639,0x10b34c96c6a92a0885ca,0xa4a8221a5b83d8d52541,0xd63d4950442cd325b22,0xb35c92c9a92a0886966,0x4a82216c9931c9625411,0xf5358950442cd325a9ac,0xb2cc990ab12a088696e0,0xa82215e3915c87254110,0x82d4d5044339306b90e4,0x34c910ab22a088696d8d],#[0x82215e192a077454110b,0x759132442ae32b40ee8a,0xfca30eb2a648841fe558,0x2214eb92595701091085,0x5c0424429b726b2ae021,0xcc2cab98848852ee5165,0x2186d75e09651091086f,0x94424430baebc1aca212,0x9b0eb28848843765f835,0x145f93619751091086fc,0xa4244296f28b2ae32122,0x708b2c84885a3e4d65d0,0xdf9361d6590910956c9,0x524433a306b88e0a9221,0xe2382a48866c611711c1,0xb97661070549108f9cc2,0x24421f730bb0e0a92218,0x5b22a48842fe5187d8d5,0x591dd36454910c57ba30,0x4421bf26c36e8a92214b,0xbb2a48863620f805d952,0x85e057654910c3dc2f00,0x4313f0841aeca9221877,0x86a488627e13835d9524,0x259171d4910a75c92c8b,0x21bf26c3ac7a92214e79,0x6a48862b5d3825935244,0x61d64d4910936caf04b2,0x15ee9c12c8b12210df93,0xc48841fe61751d562443,0xc8725951086ecbf06b2c,0xb0e7c02e4b2a210ef985],#[0xa88627e10735c9654431,0xd725951086f4c0e6b92c,0xf09b9ae4b2a2189c84dc,0x8842fe5182dcd6544313,0x7359510a6ac8905b9aca,0x28c16e6b2a2149c9460b,0x86a6593835c55084293f,0x454210f0cc9ac8a9aa10,0xac0ac8a84216ab925d16,0x58d6595454541842c772,0x50610b1bcb2a8a8a8308,0xc06e4a8c214bb905d564,0x8d6158159151843172c8,0x4610a57c930eb22a3086,0x36e8a8c2149f9361d645,0xe59180dc5528421bf26c,0xe10a5cc86e8b22a70862,0x6e6aa4214b79161d6454,0xe458759153083172c8c0,0x2087bc8b09bb2a61052d,0xc9a98414cf925d163d4c,0x97825d35308295f24ba2,0xd34c32a518aa09061b5,0x2a8241a698654a515412,0xc725c55048369706a92e,0xda5c1aa6a92a09057264,0x18a4166991d8d5254120,0x86dcd5148217f28c3acb,0x7bcc2e238aca9042fe51,0x84418f37160271595208,0x6dd151883552c9c12a8a,0x7c92e8b26a310437e4d8],#[0xc411e990e0974d4620a5,0xdd9538821bf26c3ea8b0,0xc92e8b26a71043de4584,0x411e990e0974d4e20a57,0x8a515431d72cc06e4aa4,0x3f06b08c2a8437e4d87d,0x1569905c95218550c6bc,0x96154313b09b98c4b0aa,0x6e6312c2a8627a137318,0x4cf92590735855086fcc,0x6154299f24b26e6b0aa1,0xb94c2a843766264dcd,0xcf936197298550cb4c2b,0x154295f28c32e530aa14,0x3b82a4a852e650805cb6,0x99260470549508ddca30,0x5436c324c08e0a92a136,0xb14a4a84cee5181dc152,0x73e056218950967c9b03,0x217f28c16e6b0ea18cd,0x1a02e0500880e00c00c0,0xc21642604405a0a8138,0xc1d8398700da1a833864,0xc44a89211e230420810f,0x680cd19431c620bc1682,0x8ea1ce390708de1b634c,0x72083f07c8f61e63c076,0x564a09291d23445c8790,0x514a113f2784e49b12e2,0x4ad1572a8544a714b290,0x916f2d85a4b31632c057,0x87308604bf17b2f05d4b],#[0x338664cb193320634c51,0x26c4d71ab350694d119f,0x60ea9d239e730e21c137,0xf69ea3ce790f09de3b67,0xa023fe7f0fc9f63e67c0,0xa42e85108a0e41682102,0x5e8b114a264468810ea1,0x91120a3e4768e11aa324,0x12ca564a694126a4a48e,0x8a6e4d69a132a624be97,0x86506a013ea7a4ee9d13,0x536a614aa9251ea3144a,0x6ac156aaa54ea9150a9e,0x2162ac257eaf15cab656,0x4001000b5168ace596b,0x8901100002e020200000,0x640422404202c1819640,0x41000200100000000001,0x2b820488190614000090,0x10400000001041088100,0x41000000000000000004,0x2800400206040504001,0x141000,0x0,0x0,0xc1000c040c0400000000,0x70]]
def g219H5 (j : Nat) := if j=0 then 0x1ea else 0
set_option maxRecDepth 16000 in
def g219D6 := limbs80 #[#[0x48420443705cd2108110,0x443785d52108110d6175,0x5d15108110dd17354420,0x8110d7175544204436c,0xd71815d4204427ce1d51,0x54530443f04c9214c110,0x44396595534c110f5153,0x5515150110bd38354630,0x541109f38754640443cc,0xe69625495044237e0d76,0xd4d504439658d5354110,0x443acd076454110e5b63,0xe0d76d49108df835d952,0xd4d10cdb635c35344237,0xe596554d308429761763,0x549508439a5895254210,0x8438e5935254210e3964,0x5915354210e596354d50,0xd4610e3964d4d508438e,0xcb9645c3528432e59170,0x5c3548432e59170d4e10,0x833658f7054c20cb964,0x5977054c20cb964dc153,0x54120e6952d85504831e,0xb6b83549504839ad8d52,0x1c950482da6165254120,0x882da60b5354120bc983,0xe0d7654620e596354d50,0x552209e980dc95488237,0x8f787584615432b59372,0x1c152542dc6047054950,0x542ce6107054950b5983],#[0xe1d6218950ccd7358862,0x81108df835c7625423b,0xdf1815d4204437c5d551,0x54120443da5495048110,0x4433d5d95148110cf976,0xe0d6548110aef8259520,0x481108fd8759520442b7,0x9f7815d5204427ee0175,0x543204423fe157648110,0x442fce0550c8110df171,0x5d550c8110f695254320,0xc8110bf181d43204435e,0xbe982d4320443da54b50,0x547204435e5d750c8110,0x4427de1d51c81109f587,0x59571c8110de5525c720,0xc8110aef82597204433d,0x8ff8759720442b7e0d65,0x4c720443f854931c8110,0x4437c5d531c8110fd153,0x4c951c8110bf1854c720,0xc8110fe15254720443f8,0xf735354720443dc54d51,0x547204437c5cd51c8110,0x4437c5d551c8110bf383,0x5d532c8110fc9534cb20,0xc8110be9854cb204437a,0xde97354b20443f860552,0x54b20442fae0d52c8110,0x443765cd53c8110deb87,0x61d53c8110afb8654f20,0xc8110bf181d4f204427e],#[0x9f987d4f20442fa60b53,0x59720442fae0965c8110,0x4427ee1d65c8110bdb83,0x61e65c8110be98299720,0xc8110df1815d7204427e,0xfe142485304427ee0d75,0x48530443f8549214c110,0x4437c5d1214c110fd153,0x5d5214c110ef16548530,0x4c110bf185485304437c,0xfd13254530442fce1521,0x54530442fce09514c110,0x443dc551514c110fd153,0x5d1514c110f735454530,0x4c110df175545304437c,0xed9654c930443765d132,0x54930443765d5324c110,0x442fc607524c1109fb87,0x61b524c110bd983d4930,0x4c1109f987d4930442be,0xbdb8254d30443f460553,0x54d30443765d1534c110,0x442fce05544c110ed965,0x61d544c110db97455130,0x4c110bf181d51304427e,0xaf986d5130442f660f54,0x5d1304427e61f544c110,0x4433e595744c110df381,0xe05654c1109fb855d130,0x4c110edb8359530443bc,0xddb835d5304437ce0575,0x486304427ee11754c110],#[0x443bc595218c110fe152,0x615218c110df17548630,0x8c110bf38548630442fc,0xfd38354630442fce0951,0x54630443dc551518c110,0x4437c5d1518c110f7354,0x5d5528c110df17554630,0x8c1109fb8754a304435e,0xd7975d4a30442fc60752,0xd4a30442be61b528c110,0x442fce05548c1109f987,0x61d548c110db97455230,0x8c110bf181d52304427e,0x9f987d5230442be61b54,0x596304433e595748c110,0x4433ee1d658c110edb83,0xe0550501109fb845d630,0x50110af98654140442fc,0xf355454540442fc60750,0x59540442b7e0d6550110,0x443f84c92150110abf84,0x5952150110fe15248540,0x50110ef36548540443bc,0xfb154885404437c5d521,0x88540443bc5962150110,0x442fc6162150110df175,0xe115150110f395454540,0x50110ef36254540442ee,0xf715354540442fce0951,0x54540443dcd4d5150110,0x442fce0d5150110df373,0x9515150110fb15454540],#[0x50110f735454540443ec,0xfb38454540443ec21151,0x545404437c5d55150110,0x4437c5d65150110df375,0x6165150110df37594540,0x50110bb984d4540442fc,0xd7975549404427e61f51,0xd49404427ee1d5250110,0x442ee6135250110bf181,0x61b5250110d7975d4940,0x501109f987d4940442be,0xcf975d8940442eee1162,0x59540442be6176250110,0x442eee116550110bdb83,0xe056550110ef38159540,0x50110afb8259540442be,0xedb8359540443b620d65,0x59540443ae2116550110,0x4433e21d6550110ebb84,0x60b6550110bb98499540,0x90110ef16254640442be,0xf715454640442fce0951,0x54640443dcd515190110,0x443ba5895290110df175,0x6195290110d797554a40,0x901109fb8754a40442be,0xd7975d4a40442fc60752,0xd4a40442be61b5290110,0x4433e5d562901109f987,0xe055490110afb8558a40,0x90110d797555240442fc,0xd7975d5240442fc60754],#[0x59640442be61b5490110,0x443b6e0d6590110afb82,0x6057590110cfb8759640,0xd0110df171543404437c,0xbbb8454340443765cd50,0x547404435e5d550d0110,0x443cd55151d0110dd573,0x61d51d0110d757554740,0xd01109f787547404427d,0xcf5655c7404436d55171,0x5cf404436755173d0110,0x442b7e0d65d0110cdd65,0x5d565d0110abf8459740,0x541108ff87597404431f,0xe6d62549504427d60b71,0x589504433bdc96254110,0x4429fe156454110a7f85,0xe097654110adf8359550,0x54110cdf835d9504423f,0xef16254550443dc54951,0x54550443bcd895154110,0x443dc54d5154110bf382,0xd8d5154110ef16354550,0x54110df37354550443bc,0xef16294550443dc54a51,0x94550442fc60a5154110,0x4437cdd25154110ef164,0x6087154110f71521c550,0x54110bdb835c550442fc,0xdf272dc550443dc54b71,0xdc550442fc60b7154110,0x4437c5cf7154110f7153],#[0x5d37154110bf183dc550,0x54110f69524c9504437c,0xedb634c950443d654d32,0x4c950442de6153254110,0x442fc6063254110af986,0x6163254110f69528c950,0x54110af9868c950442de,0xbd98310950442fc60442,0x10950442de6144254110,0x4427e61c4254110af986,0x54942541109fa8710950,0x54110af98650950443da,0xfab4290950442fc60642,0x90950443da54a4254110,0x442be61a4254110b7985,0x61f4254110af986d0950,0x541109fa87d09504427e,0xf718154950443ba58952,0x54950443dca055254110,0x443da9895254110f6962,0x1c95254110e7b6254950,0x54110f6b7254950443da,0xe7b63549504439e58d52,0x54950442dee0d5254110,0x4439ed915254110e7964,0x6065254110d7b7454950,0x54110ee96294950442fc,0xaf98694950442de61652,0xd49504439e58b5254110,0x4439e58f5254110e7b62,0x60f5254110e7b63d4950,0x54110e7964d4950442de],#[0xd7b74d49504439ed9352,0x58950442dee156254110,0x443badc96254110ee872,0xd4d6254110e795358950,0x54110afb83589504439e,0xafb84589504433edd162,0x589504439e2156254110,0x442f660e6254110e7b85,0xdd36254110b798598950,0x54110af984d89504433e,0xde9721c950442fc60472,0x1c950442f660c7254110,0x442eea107254110bb984,0x6067254110bf3815c950,0x54110bf38150d50442fc,0xddb7350d50443b6d8d43,0xd0d504427ea1d4354110,0x4427e61f4354110af986,0x58d53541109fa87d0d50,0x54110ddb7354d50443b6,0xb7b8254d50443dc60553,0xd4d50443d6dcd5354110,0x442be60b6354110b7982,0x6136354110edb73d8d50,0x54110bf3815cd50442be,0xbf381551504427e61373,0x951504436edd15454110,0x442be61a5454110dbb74,0xe096454110b7b8559150,0x54110e788559150442be,0xbd983991504439ee1564,0xd9150442de6166454110],#[0x442fce057454110af982,0xe097454110be8825d150,0x54110bf1819d150442fa,0xdbb749d150442f660e74,0xdd150442fc6077454110,0x4437ca077454110df181,0xe1d62941109f983dd150,0x94110bf381552504433e,0xcfb87592504436e5d154,0x5c7504433d58971d4110,0x4433d59171d41109f782,0xe1562d4110ced7258b50,0x4c910a7f85593504429f,0x9f984dc1324433e59370,0x591324427e617704c910,0x4423f61d644c910aef82,0xe0d654c9108ff8759132,0x4c9108fd8759532442b7,0xcfb805d9324423fe1d65,0x5d9324423fe11764c910,0x44379549718c9108ff85,0xe01528c910cf5655c632,0x8c910ced7654a32442fa,0x8fd8759632442b7e0d65,0x5d6324423fe1d658c910,0x4423fe15768c9109fb80,0xd957010910cf9655c042,0x10910cdd655cc424433e,0xaef825944244337d9573,0x59442442b7e0d6510910,0x4423f61d6510910c7d75,0x5d765109108ff8759442],#[0x109108fd87d94424431f,0xc7d865d4424435e60175,0x5d8424431fa197510910,0x443cb55152509108ff85,0xe0d65509108fd87d8d42,0x509108ff8759542442b7,0x9fb805d5424423f61f65,0x5c6424423fe197550910,0x4433d5957190910de552,0x5974290910cf7655c642,0x90910eaf65d0a42443ab,0xadf83596424433b5d952,0x59642442afe116590910,0x4423fe1d65909108fd87,0xe0175909108fd87d9642,0x549108ff855da424427e,0xbd9831c1524437c5c470,0x1c152442ee6107054910,0x4437c5c77054910cf976,0x5db7054910df271dc152,0x54910cfa76dc1524433e,0xdf181dc1524427d60770,0xdc1524437ca077054910,0x4427e60f7054910cfb62,0x59770549109f984dc152,0x54910cfb65dc1524433e,0x9f980dc5524433ea1b70,0xd8952442f360e6254910,0x442bb60b6354910a7d85,0x61f6354910cdf73d8d52,0x549109f581dcd524423f,0xb7980d51524423f61b73],#[0xd91524423fe1d6454910,0x4432fdd36454910aed82,0x60774549108fd87d9152,0x549108fd86dd1524427d,0xadf8359552442bbe0965,0x5d952442bb60b6554910,0x442afe117654910adf83,0xe1176549109df835d952,0x54910cfb805d9524426f,0x8ff815d9524433de0576,0x5d9524433720d7654910,0x4423fe0d7654910cdf83,0x6037654910c7f855d952,0x549108fd83dd9524423f,0xcf5655c6524423f61376,0x596524433dd957194910,0x442b7e0d6594910aef82,0xd8970d4910aed82d9652,0xd4910cf9635c3524433e,0x9fb835c3524433ed8d70,0x5c3524433e59170d4910,0x4427ee1170d4910cfb64,0x58d71d4910cf7625c752,0xd4910cf7635c7524433d,0xcf5645c7524427de0d71,0xd8b524433dd9171d4910,0x443375cd63d4910a7d85,0x61f63d49108fd8758f52,0xd4910aef82593524423f,0x8fd87593524432f5d164,0xd93524423fe1d64d4910,0x4427de0574d49108fd87],#[0x20d76d49109df835db52,0xd4910cdf835db5244337,0x8ff845db524423fe0d76,0x59562442bbe096458910,0x442b7e0d6558910aef82,0x60a6558910c7f7559562,0x58910c7f7599562442bb,0x8fd85dcd624423f61373,0x1d562442b760c7558910,0x442bde057558910c7d75,0x6067558910adf835d562,0x58910c7f759d562442bd,0xcdd655ce624423f60f75,0x59662442bbe096598910,0x4431f5d56598910adf83,0xe1175d89108ff855d362,0x54d10df1715c1534423f,0x9f581dc9534427e60372,0x595534423f61b7254d10,0x4439ee016554d10adf83,0xe017654d10e5f8359553,0x54d108ff825d9534433e,0x8fd82dd95344337e0d76,0x5cb534427ee1170d4d10,0x44337d8d72d4d109fb80,0xe0976d4d10e5f8359753,0xd8d10cdf835db534423f,0x8ff855cb634423fe1172,0x5d7634423fe0975d8d10,0x4437cdc77059510cdf83,0xe037359510ddb73dc165,0x59510cdf73dc16544376],#[0xed873dc165443bcdc770,0xdc165443b6dcf7059510,0x442be6137059510af983,0xdcc7259510ced721c965,0x59510afb805c96544337,0xcdc735c965442bde0572,0x5c96544337dcd7259510,0x442af2117259510adf83,0x6027259510abf845c965,0x59510af5819c965442be,0xcdf739c9654433bdca72,0xdc965442b760e7259510,0x44337dcf7259510cdc73,0x61372595108fd83dc965,0x59510afb805cd654423f,0x8fd82dcd65443b6e0373,0xdcd65443376037359510,0x4433720b7359510cdf80,0xa0b7359510cdd82dcd65,0xd9510cdf82dcd6544337,0xed96554d308423fe1172,0xd5130842f660f544c210,0x8427e61f544c210af986,0xe19754c2109fb845d530,0x54210eb964505508433e,0xeb96454550843bc58551,0x5c550842f6e0d7154210,0x843ba5895254210eb964,0xdd95254210eb96454950,0x54210e7961d49508439e,0xafb865c950843ae59172,0x54d50843b658d5354210],#[0x8439e5915354210eb964,0x5935354210e7b7654d50,0x54210eb9645cd508439e,0x9f984dcd50842bee1973,0x59150843ae5915454210,0x843ae6056454210eb974,0x6156454210eb98359150,0x54210beb825d150843ae,0x9f983dd150842bee1974,0xdd950842be60b7654210,0x842be6137654210af983,0x5515150610bf38054541,0x50610eb56454541843cd,0xabd86551418439d59551,0x59141842afe195450610,0x8427ee017550610cbd75,0x60372546109f984dc151,0x54610cbd64dc9518427e,0x8fd86dc9518431f59772,0x551518438f5915454610,0x8429fe195454610a7d86,0x61b5454610e3d64d5151,0x54610cbf74591518429f,0xe3d8559151843ad60564,0x591518438fa156454610,0x8432fa1d6454610cbd87,0xe1165546108fd86dd151,0xd4610cf9625c3518429f,0xced7258b518433e59170,0x5cb518427ee0172d4610,0x8431f59572d4610cbd64,0x61954d4610e3d6455351],#[0xd4610cbd74593518429f,0xcbd87593518438f61564,0xd4961842be6035258610,0x8423f61f5258610af581,0x5977054a10ee962dc152,0x54a10cf976dc1528439e,0xcf986dc1528433e59770,0xdc5528427e6037154a10,0x8432f5937154a10ced62,0x59171d4a10c7d65dc552,0x54e10c7d655c7528432f,0xe9d83591538432fdd164,0x591538432f61d6454e10,0x8427e6037454e10cbe87,0xe117654e108fd86dd153,0xd4e108fd84dd9538423f,0xcbd74593538433e59170,0x593538423f61d64d4e10,0x842be6035458e10cbd87,0x61f5458e10add83d5163,0x552109f980dc5548423f,0x9f980dcd548432f59371,0xdcd548432f5937355210,0x8423fe0d76552108fd86,0x59171d52108fd83dd954,0x59210cbd645cf548432f,0xabf855c5648432f5d571,0x5cd648432f5d57359210,0x842afe057559210abf85,0x6067559210abf835d564,0x59610abd839d564842af,0x8fd84dcd65842b7e0d71],#[0x54d610823f60f7459610,0x82bd6135358420af784,0x5937054c20ed963dc153,0x54c20e7965dc153083ae,0xcf964dc1530833e5db70,0xdc1530833e5977054c20,0x8337dd16354c20cf986,0x60d6454c20cbf7459153,0x54c20cbd8759153083a7,0xc7d65dd1530832fa1d64,0x5d9530823f61b7454c20,0x823f6137654c208ff84,0x5d164d4c20cdd7458f53,0xd4c208fd87593530832f,0x9ef825d3530832f61d64,0x5d1630831f59574d4c20,0x82b7e157458c20cdd75,0xe117558c20edb805d563,0x59420add849d563082b7,0xe7b805cd650823f61373,0xdcd650829fe117359420,0x483da6015254120a7d84,0x5493154120f6b8054950,0x54120f59534c550483da,0xaf9868c550483da54a31,0x54550482be61a4154120,0x483da54a5154120f6952,0x5496154120af98694550,0x54120b7b8558550483da,0xb798598550483da54a61,0xd8550483ba54b6154120,0x483da5487154120eeb72],#[0x1c97154120f69525c550,0x54120beb825c5504837a,0xf69529c550482f6e0d71,0xdc550482fa60a7154120,0x483da54d5254120f6952,0xe0d5254120eeb6354950,0x54120f697354950482fa,0xf698354950483dadcd52,0x54950483dae0d5254120,0x483da54f7254120f6887,0x5d37254120be983dc950,0x54120f698254d504837a,0xaf981d8d50483d6dcd53,0x55150482fae097354120,0x482be6076454120dbb74,0xe1d654c520beb825d150,0x8c520cf576546314823f,0x8fd8759631482b7e0d65,0x5da314823fe1d658c520,0x4827b60b70545208ff85,0x6076354520a7d85d8551,0x54520cdf73d8d51482bd,0x8fd86dcd514823f61f63,0xd9551482bde056554520,0x482b7e0d7654520af581,0x60f76545209df835d951,0x94520af781596514823f,0xcfb615c351482bd60765,0x5c3514835e54d70d4520,0x4833ed9170d4520cfb63,0x61761d45209fb845c351,0xd45208fd87d8f514829f],#[0xc7f75595614823fe0d76,0x596614831fdd66558520,0x4831f5d56598520af781,0x61b7154d209ed82dc553,0x54d209ed82dd1534823f,0xadf83595534823f61b74,0xdd9534823f6077654d20,0x4827ee1170d4d208fd84,0xe1176d4d208ff815db53,0xd8d208ff855c7634823f,0xdeb72dc1654823fe0575,0xdc1654833edc77059520,0x482be6137059520eeb72,0xe017159520cf5711c565,0x59520adf835c565482be,0xcf7719c565482be60271,0x5cd654823f60f7159520,0x482bbe097359520afb80,0x61373595208fd81dcd65,0x54220ef161545508823f,0xe7b52585508839e54961,0x5c5508833edd16154220,0x8833edd97154220bdb83,0x5895254220afb865c550,0x54220ed96354d50883ba,0xe7b7654d508839e59153,0x5cd508839e5935354220,0x882fae095454220afb86,0xe097454220eb96455150,0x54220afb865d150882fa,0xaf983dd950882be60776,0x58551882be6137654220],#[0x8839d5516154620cf772,0x6037254620e775458551,0x54620e3d64551518827e,0x8fd86dd1518832fdd164,0x5d951882b7e0d7654620,0x8823fe117654620cdf83,0x58970d46208fd84dd951,0xd4620cf9645c3518833e,0xe3d64553518823f61d62,0x593518832f5d164d4620,0x8827be0974d46208fd87,0x6035258620afb8054961,0x58620af581d4961882be,0xaf980d5161882bde0554,0xd5161882bd6075458620,0x8823f61b7154a208fd87,0xe117654e208fd86dd153,0xd4e208fd84dd9538823f,0xcbd74593538833e59170,0x5d3538823f61d64d4e20,0x882bbe095458e209ef82,0x60f5458e20af980d5163,0x552208fd87d5163882b7,0x9f980dc5548837adc970,0xdc9548823f61b7155220,0x883ab5937255220be980,0x6037255220ced76dc954,0x552209ed81dc9548837a,0xced86dc9548833b59772,0xdcd548827e6037355220,0x8823f61b7355220cbd64,0xe0976552208ff815d954],#[0x552208ff835d9548833b,0x8fd83dd9548823f60776,0xdc565882b7e0d7159620,0x8823f61373596208fd84,0x6077459620aef825d165,0x545508fd83dd1658823f,0x9f982dc1515435e54b70,0xdc1515435e54f7054550,0x5427e61370545509f983,0xdcf6354550e5f6354d51,0x94550d79525c25154337,0xe7552d86515433ed9170,0xd8651542bd60b6194550,0x5433b5cb6294550af584,0x61f64945508fd87d8a51,0x18550cf572584615423f,0xcf78758461543b5e0d61,0x588615435b5c95218550,0x5427e60172185508ff87,0xe1d6418550aef8259061,0x585509f9805d0615423f,0xddb73dc161543761cf70,0x549615435bdc95258550,0x54357dcf5258550d5f73,0xdcc625855097e87d4961,0x58550add831896154337,0xabe8418961542af61062,0x589615423fa1c6258550,0x5433bdca6258550cdf73,0xdcf6258550cdf7398961,0x58550e5f6354d6154337,0xd5f73d4d6154357dcd53],#[0x1cd61543375907358550,0x54376e037358550cdf64,0x9937358550cdd64dcd61,0x58550cdf64dcd6154337,0xcbf7499161542b760e64,0xd86615439d54b6198550,0x5435b5c95298550af582,0x5cb5298550d7970d4a61,0x9855097d87d4a615435b,0xde9805ca61542bde0562,0x5ca615433bd917298550,0x5433b6197298550d6d85,0x61e52d8550afb8058b61,0xd8550afb805cb615423f,0xcfb805cb615433e20172,0x5cb615423fe0d72d8550,0x5423fe0973d85508ff84,0xe0974d85508ff845cf61,0xd85508ff835d3615423f,0xadd839d361542be60274,0xdc1525429f61674d8550,0x5427e60f70549509f981,0x60470549509f984dc152,0x54950b7a861c152542de,0xf6b62dc152542de60770,0xdc152542de60f7054950,0x542dbe096354950b7984,0x6076294950cef625c652,0x189509f9805c462542bb,0xaef81588625437c60171,0x5c6625433be1d6218950,0x54277e0d71d8950cef62],#[0x20d71d8950adf835c762,0xd8950cdf835c76254337,0x8ff845c7625423fe0d71,0x5cf625423fe0573d8950,0x5423fe0574d89508ff84,0xe0d70587508ff835d362,0x58750abc845c961d42b7,0xaf5819c961d42afe1172,0xdc961d42b760e7258750,0xd423f61372587508fd83,0x61373587508fd82dcd61,0x58750af5819d161d423f,0x8fd83dd161d423f60b74,0x9c562d42afe117158b50,0xd42bb60a7158b50af980,0x6137158b508fd83dc562,0x58b50afb805cd62d423f,0x8fd84dcd62d423f60773,0xdd162d423f6077458b50,0x12003000600008fd83,0x3a80c002a009001e006,0x5e81740570132048c10b,0x41f207b01d406f01a40,0x42790960237087c21008,0x3120c0c2eb0b4c2b20a4,0x900dbc3570cfc3300c84,0xb10684020fa83c90ee83,0x123c46e117c450110443,0x45850714044f213444b0,0xc056a156c54c14f45251,0x45bb16b05a6165c58815,0x5f117ac5e517585d0170],#[0x4b191462d18786181800,0x819a4663197465719446,0x1aa06a21a4c68419f867,0xbe46e11b486c31ad06ae,0xe07321cb071d1c387081,0xc7681d647531d347471c,0x7cb1ea87a41e3077d1dd,0x3720a081020047e91f8c,0x621c0861216c84c20f48,0x234c8bb22b088b21f087,0x49090c23f48ee23a08e2,0xb0954253893f24c092a2,0xc99c265898725e097225,0x9e427549cf27009b126a,0x3528bca202844a0227cc,0x429b8a5f2964a4a2910a,0x2a90a952a3ca892a0ca7,0xb8cad42b38abf2ac0aaa,0xf4b252c58b072be0ae92,0xcb882de4b732d90b552c,0xc062fb8bdf2f64bca2ee,0x573144c4230ccc243054,0xf3240c8131ecc7531bcc,0x3414ce43330cbd32b8c9,0x5a0d503504d3234b0d14,0x74dc536d8da7363cd773,0x8e1f3840e0a37ecdec37,0xe703984e523930e3d38b,0xaf3aa4ea33a50e8539fc,0x73ba0ee23b4cec43ad4e,0x3d08f333cb4f1e3c3cef,0xe28f7b3d8cf5d3d5cf51],#[0x48fc33ed0fa53e7cf903,0x101d40390083fc0fe13f,0x654159047410503240b,0xb6429d098422507a41ad,0x44290fb43b10dd43150,0x456d14c44f5125445911,0x6f91af46a519a462d16a,0x1920047e91eb47711cd4,0x924848e522a489121548,0x28749bd269498d25d493,0xd84b252ba4ad12a54a59,0xd4cf93264c5d2ff4bc12,0x4e193804dc536b4d7134,0xf813d14f093b34e91395,0x5544f510143150654014,0x148551d947051a946451,0x4d6531d4b852a549a525,0x15541950053c54eb5395,0x4553953f54c152a54915,0x55ed56c5599560556955,0x70d5b4569559f566558a,0x5160557fd5f057855c95,0x5656591d63858c962c58,0x6b95acd6a45a5567d599,0xf85bc96e35b516ce5b21,0xe5ca17195c4d70d5c1d6,0x5d9d7615d497435cf572,0xe997975e457825dcd76d,0x957df5f417ca5eed7ac5,0x982760618095fe97eb5f,0x88161c9863615184560d,0xd2630d8b46295896621d],#[0x163e58f363b58e763618,0x654d93b64b191d645d91,0x66d995661998065a1962,0xada1c68119e367099a16,0xda7f69e5a736949a3a68,0xabe6abdaa96a8da9d6a5,0xfd6bddae86b89aca6b11,0xa6c91b1e6c3db096c0da,0x6dd5b666d5db3f6ce5b2,0xf3dbc06ee9ba26e71b84,0x5dbff6fc1bea6f91bde6,0x9c4770e1c32708dc1d70,0xc867201c7a71adc5c715,0xc572d9ca77285c9b7231,0xb73d5cef73a5cda7351c,0x74d1d25747dd107405cf,0x5cdd6d759dd587525d43,0x11dbe76bdda07645d8b7,0x1dfd77b9ddf7765dd377,0xe4578d9e3078a9e1b783,0x7b79d5e6f79a5e5a792d,0xa7ad1ea57a7de997a29e,0x7ba9edb7b55ecf7b01eb,0xcc9f237c75f0e7bfdef9,0xa1f597d4df447cf9f387,0x9f8f7e25f837dd1f6e7d,0xfe07f45fc27ea9fa47e7,0x4380f602e8035ffe7fbd,0x4821607f819e058814a0,0x82ca0ac829a0a0826a09,0x40e0f483ba0df83420c1,0xa13c84b612784861128],#[0x618d85fa16f858215185,0x1d5873e1c986ea1ab869,0x1d883a20887e61f38792,0xc895a247890623b88b22,0x89ea27489ba268898a25,0xae62aa8a6e28c8a1a280,0x7230d8bfa2e68b3a2c88,0x23558d1a3378cc63228c,0x39d8e3a3888de63738d9,0xf78fc63e28f723c48eb2,0x4907a418904a40c901a3,0x919a457912244290ce42,0x272496921e48191ee475,0x4a4cc931a4c092c64a29,0x2526943a50893e64e193,0x56e957e559952a54494b,0x9b9632586960257a95d2,0x397525c596da5a796865,0x984e60497fa5f897a65e,0x92663a98d262e98a2619,0x6a69499f2676999e6589,0x26ca9b126be9abe6a99a,0x7009bea6f49b966df9b4,0x3f9ce67339c6e7159c3e,0x9e0677b9dd67669d3a7,0x9eba7a89e8a79c9e5a79,0xfb67de9f3e7c09eea7b4,0xb2814a0167ff9fe67f39,0xa86ea1a2859a14e84da0,0x8c8a30a8b3a292895a21,0x19a42a904a3d68efa35e,0xea5b694ca4f6937a4a29],#[0xa7429c1a6ca9a3a67698,0x916a36a89e9fda7ba9df,0xa2a99a9e2a69a96aa4ba,0x2afcab92ad5ab1aab7aa,0xb83adaeb53accab23ac5,0xefaf82bd1af0abb3ae4a,0x7b07ec19b04ec04affab,0xb19ec61b14ac4cb0f6c3,0x29aca0b26ac8bb1f2c6d,0x96cdfb366cd3b312cb5b,0xed15b43ed09b40ecf4b3,0xd4bb4f2d36b4c2d21b46,0x8ab5eed75b59ad57b546,0xb6eadb4b6bada8b666d,0xb79ede1b74adccb71adc,0x89ae17b846e02b7f2df6,0x96e56b942e41b8cae2cb,0x6e95ba3ee89ba0ee74b9,0xee6bb5eed1bb0aeb3bab,0x1cbc36f07bbe2ef2bbb2,0xbbd56f46bcdef31bc8af,0xbe52f8ebdfef70bd86f5,0xf4efcdbf1efb8bea6fa3,0x2ffabfd2feebfa2fd9b,0x3042c0cf024c07b00fc0,0x81c1cb06cc177057c12,0xaec2a3099c24f08dc21f,0xdc37b0d8c34b0ccc2f70,0xc42f105c3ff0f9c3cf0e,0x507132c4b3126c48311a,0x9715fc567153c537147c,0x319ec663189c5eb16bc5],#[0x1efc7831dac72f1bcc69,0x49c90f234c87320dc7fb,0x1ca0b273c9b725ec93f2,0xcb4f2c4cad72a6ca5f29,0xc93315cc1b2eecba32e2,0x8f35dcd5f351cd2f333c,0x33c0cec7399ce4f37bcd,0x408d00b3f3cfb73decf6,0x35d0bf429d08f414d03b,0xdd1df45fd14344ad0ef4,0xd2db4a7d263492d23347,0x36b4d4d33b4c8d30b4bc,0x1f4f8d3cb4ecd39b4e0d,0xb55bd533534d497516d4,0x5a3d67758ed5ff570d5a,0xd9d72b5c4d6fb5b8d6cb,0x6d8035fad7af5e5d77f5,0xd8b7627d863612d83360,0x9b3666d95f651d90b63c,0x67693da3767ed9e3672d,0x8402daeb6b4da9769fda,0x9840209840209840209,0x2098402098402098402,0x2c100c11640884040984,0x581806120c0858201060,0x38200c051000b04020c8,0x9040204c9420284020,0x21844201040192832504,0x250884120a84430a8482,0x2210402a110c20150887,0x90325064a08424a1494,0x82218418410418410401],#[0x8611042e150884840b04,0xc0a11082a11080a1208,0xc200b001600200542011,0x8443090542218482a110,0x208007042f640386120a,0x8141028207030406068,0x10000080410200c20000,0x3020008104000020088,0xc3010480040120002,0x20c0410000002000000,0x4040604100b04100002,0x4100083022204004022e,0x2008200041c082000020,0x2602122602410c017020,0x1110042418264040402,0x10002082002414002019,0x8902102c183089021804,0x52002008203040000208,0x1100420102080c10000,0x302003c10002080c100,0x83050008041080200401,0x80410400002019011102,0x1820000000100c80,0xc14182000c100440d041,0x4218406120401040c080,0x9230c500020104112020,0x810080c3051808ac1006,0x82083011102c30418410,0x12020000288181000604,0x21042030224048209041,0x5100429203245100431,0x21088111004220822404],#[0x18422048208924410480,0xc1810044090410082042,0x21820f04002020604820,0x82000010410782003c1,0x81086100010002085812,0x1048608016040c0,0x182010c1002c081a4810,0x9042a28200040c081812,0x208000040208300040a2,0x41000380041e08004048,0x10082058004000406080,0x30003040304000000800,0x81a03000c0e08141028,0x1510205050008125040a,0x400a834104001000814,0xe4a100000150400a8215,0x8200040408205040008a,0xa088b021604111204202,0x141090385044401080,0x208141028200040c082,0x40041791048302820104,0xa8204001800207030522,0x82220400902170400000,0x92820000504020800102,0x1000a001000090205040,0x181040c081810000000,0xa82220a840614102820,0x41000408002110206141,0x28585008401040a080,0x9410000a820040183021,0x40008200000881000a0a,0xa08000106040a080050],#[0x20e141030a0818507,0x1028206068208000181,0x1a080010002010408080,0x8106820504060800104,0x83010400000441000808,0x2080c04100c1c082000,0xc0060000b04061810200,0x200c04181286020e4b81,0x44c10804080810180820,0x4c24100001186020c,0xc1018602080000208000,0x10400006080000030,0x182618206040c0832441,0x2408901018601080090,0x2080030c02100410000,0x8101000a0800100,0x203040008000141000,0x10002000000000400,0x410002000c107820,0x40c9410102030c0010,0x1008212040a080001410,0x40408005040000a0904,0x200003040a08000005,0x80000400080000c10000,0x100000040800004000,0x80002c1000028200,0x80810002010482400800,0x10042c1583061604000,0x802060c0210041002008,0xc1810302650400000000,0x200106060c0818101820,0x416083c1000200040070],#[0xb04000800f0704100,0x20004000820504108020,0x18208000101080,0x8205041a082410000000,0x325044405081206080a0,0x48325040a080070400a8,0x20282220400482005410,0xa080a504006a9420601c,0x41001a08341000000002,0x8000000064a080,0x52840004000000830104,0x180020146a208040820d,0x10000000000080220400,0x88101820004020800000,0x200041000000200,0x200000a0415282000400,0x800104001800,0x10000001000110200001,0x5041a000882080000400,0x20006,0x200000000040008001,0x20000250800352c0020,0x8100020204020008000,0x201910010081000408,0x30102000010102020400,0x7040a0240060501000,0x40e08581028205040e08,0x5040c08200c250388020,0x88183038280040a0802,0x28242070a08181400216,0x22081410c0442402142c,0x6022141600106012420c],#[0x9042a080801050e0a08,0x241002a086012102,0x200004040028200330a1,0x204040000a08001000,0x410082000000010,0x20800000100000820000,0x203040008000040,0xe080070400000000,0x21104000000800004,0x30400000001028202040,0x2a08005040a080090,0x80150400a820014100,0x608001908200021040,0x2000000810002000c10,0x100000800100000000,0x400082000c1000608,0x102070400002000000,0x800000000704000,0x8000000000000040000,0x10ac8420000b0385042c,0x20104020b00100800d00,0x42008000041018042a00,0x40a08185040a081400,0xa10080028008581a0034,0xc02102c105820b068,0x84005a80105446100000,0xa104043314260020b50,0x8000005001000002008,0x8200341413001018a,0x20800100,0xa8216042a081c1000000,0x80810030086410c05c20],#[0x40000000e080c5040a0,0x1000000000408000003,0x80040400082000,0x1020000000004000]]
def g219H6 := limbs80 #[#[0x900600200118000a343,0x100c3c50c000110f04a0,0x38308b14000520405630,0x487881c904f1040c0040,0x510b7d06cc3801041043,0x410dc25b0ce00268105,0xa010744533105fb03001,0x88c801f073700ec01fa4,0x549311c020a0a5000050,0x84051334a42603170940,0x9e001700251006c27df0,0xbc43b0000c4bb10c0d0,0xbc000000000000b28c48,0xb212d0656075000064,0x1080a700000740000000,0x5051514a00000000d2,0x40b930980000409000,0x2ab0290000b07d125900,0x30000b06e50474405c1,0x53f00c601b1437000010,0x8cb73f73770000c05663,0x87341ef092502ae08ad3,0x55e06b2465104d40a920,0x3d706de00b0000805c20,0x4095ac00001467450910,0xbf0000c4150000d03fe0,0xc06a1704e20490,0x72000080860000946e00,0x8e842c906000006036b0,0x44680693442608d30,0x19904ec00f373b000000,0x7000000000000c69fb1],#[0x81000040be000060b414,0x1c0000c079208c4475c0,0x2c0000d0423009422320,0xaf806f202650414011c0,0x14be10c1684ed064e0,0x10000040b310b030a300,0x1f0000602ee958a06c20,0x8a0000f00200b2d109b3,0x80a20000f21f225a53,0x22000090389441000000,0xb10000000040ac000083,0x364a509f121e0000a0,0xd0a010aa0000000000,0x2d000020b690a4000000,0x20059430e07b609950,0xc532600001228602200,0x42a8b49fc043b4,0x10902100006013e0bd00,0x3c704a000034067037e5,0x332400000000706334,0x3e140ad0120000440200,0x6650b744320000000027,0x3007000000323035f0,0x45012c00000000c22200,0x77000071b4803ba0bac0,0x93102f60890000000040,0x9b0000a04cf083607cc0,0x70ab0000131d18,0xa73d0000a0ae00,0x49b23400000000000000,0xf052303a00007320e0,0x206270820000000000],#[0x0,0x6019000000,0x5a303000004111422900,0xd00100000000000079,0xd22700000000000000,0x24452016000000,0x67d05700003512304800,0x7118702bd11dc01a10,0xa00000000000e02400,0x4dc0a6e0310000000000,0x90000505ae0bb000098,0x300d00002408000034,0x5059c08f72,0x444c0000901d000000,0xd73ad09b107e000000,0xe12200,0x54000075149263000000,0x130000e01400002046a1,0x69103cf0bc40532008f1,0x3f004e039881e0000b4,0x71805b00005078a0b8a7,0xb11a0000d225281610,0xb5321126014027000000,0x274061605e000020a100,0x680000212da015912b73,0xf4097140d0000009d40,0x201ef21a61170000d4,0xe07011534034044d00,0x21d214625cd155000000,0x7f009490766175646832,0xc0850000322600,0x71e04b00002050000000],#[0x5d000030a8e023000064,0x18600a0000b466000060,0xb107a746f280fb09640,0x39c03e909a3323f23766,0x58503324445091d02811,0x49b20951875332e60,0xe640170806609112100,0x1600000000a209423284,0x2370ad809c408bc044a4,0x8a0000b04f0000b4bd21,0x72]]
set_option maxRecDepth 16000 in
def g219D7 := limbs80 #[#[0x2ecb9840887e12108110,0xaf2ea102216e5d02044,0x835cb22a1084df735951,0x10ddac4a9021da549504,0x427ebb2a40867d65548,0x810cfacba90213fdd952,0x30436eb1aa6084fd76d4,0x4c109faeca98219f5955,0x530433eb2ea6084ff765,0x594109fee4b28213f5db,0x420443f8a8840884ff73,0x1c81109faec902217e5d,0x4720443f898e40885f57,0x52c8110fd26590221fc5,0x5d720442fcb9e40887e9,0x1514c110fe242982217e,0x654d30443ec99260887f,0xf9654c110bf2e898221f,0xfc48630442fcbaa60886,0x5f9748c110fe2a318221,0x17e5d6304437cb2c6088,0x87f22150110fe242a022,0x21fc94540443f8a8a808,0x886f96550110df6c4a02,0x221fc546404437db2a80,0x885f97490110df2c520,0x2217e5d6404437cb2c8,0xa0885dd73d0110beae3a,0xa82213f5d950442fbb8a,0xaa0887f25154110fe2a2,0x4a8221fcdc550443f838,0x12a08877b5254110ef2a],#[0xa6a8221bed89504437cb,0xb1aa08877b5354110ef2,0x6e6a8221bed8d504437c,0xdb22a0886f96454110bf,0xf2c5282217edd1504437,0xfcba4a0886f96494110d,0xbeae3a82217e5d650442,0x27ebb264885fb704c910,0x9faed192217d5c63244,0x42eeb9884885f9701091,0x10afcea212215f5d4424,0x442fab8c84884fd76109,0x9109faed21221ebd0a42,0x2442fab88a4885f97014,0x4910b7ae829221775cc5,0x524427ebb0a4885be741,0x549109faeca92217edc1,0xa52442fab8ca4884ff76,0xd49109faed29221dbd4,0xdb52442fab8ea4885f97,0x75589109fee6b12213f5,0x5d362442eeb9cc4884ff,0xd6354d109faebb12213f,0xf5d9534433eb2aa6886d,0xf970d4d109feeca9a213,0x9f597534436fb1ea6885,0x4fd72d8d109faeda9a21,0x177dcd654427ebaec688,0x84ff7059510df6e0b2a2,0x21b71cd654427fb92ca8,0x884ff7359510dbee6b2a,0x421fa54b208427eb96ca],#[0x1087d9534c210bf2eb90,0x84217e5d5308437cb2a6,0xa10877b5254210ef2a4a,0xa8421de54d508437cb12,0xaa1086f96354210ef6a6,0x8a8421be59150842fdb9,0x2283086fb7654210bf6e,0xc8a8c217edc1518435eb,0xb2aa3086be6454610d7a,0xac9a8c217e5c3518433e,0xeb2ea3086be64d4610d7,0xdac4a94217edc1528433,0x5f322a5086bd6454a10d,0x9faeca94219f59552843,0x2fcb86a5084ff7654a10,0xd7cc9a9421af5935284,0x427ebb6a50867d65d4a1,0x10d7ac8a9c21b758d538,0x8433eb2aa7086be6454e,0xe109feeca9c213f5d953,0x38435eb26a7085f970d4,0x4e10cfacba9c21af9935,0x548435eb22a9084fd76d,0xd52109feecaa4213f5d9,0xb548435eb26a9085f970,0x359210d7ae2b24213f5d,0xd5648435ebaac9086bd7,0x73596109fee4b2c21af9,0x585510827fba2cb084ff,0xe6354420dbac6a8841bd,0xf5d9510833eb2aa2106d,0xf561d44209feeca88413],#[0xb798f510836eb1ea2106,0x4fd76d4420cfacba8841,0x1bdd4d610837aa9ac210,0x6f67558420deaeab084,0x41bdd4e610837aa9cc21,0x106dd6354c20bf6e0a98,0x841af991530835eb22a6,0x6104fd7654c20cfacaa9,0x9841b758f530827fbb2a,0xa6106be64d4c20d7ac9a,0xb18413f5db530833eb2e,0xac6106dd7558c20dbae8,0x6b28413fdc5650836f3a,0x8aca1067d71594209fee,0xe6b28419f5cd650833fb,0xb92a09076d5254120cfe,0x6c2a82413f5d950482f7,0x5292a0907e95254120df,0xd0e4a8241ded4950483f,0xbca9aa0907eb7254120f,0xdf6c6a8241ded4d50483,0x2fdba2a0906fb6454120,0xbdae5a82417e5d65048,0x82fcb80a2904fd768c52,0x209faec28a41775cc514,0x483bba8ca2904ff76545,0x520bf2e1a8a413f5da51,0x34827ebaec2904fd76d4,0x4d20bf2e1a9a413fdd95,0x634827ebb6a6905ed72d,0x595209faebb1a413f5c7,0x5654827fb82ca906fb70],#[0x1d95209fee6b2a413fdc,0x49508837cb0aa1104fd7,0x5354220ef6a4a8441de5,0x58d50883bda9aa110779,0xb7454220df2c8a8441be,0xd585518837dbb2a1105f,0xff76546209faeca8c41b,0x3f5db51882fcb86a3104,0x67d6554a20bf6e0a9441,0x19f59752882fcb86a510,0x67d6554e20dbac6a9c4,0x413fdd9538827ebb2a71,0x1067d65d4e20bf2e1a9c,0x4417bdc9548827ebb6a7,0x9104fd7655220d7ac8aa,0xa4417e5c3548827fbb2a,0xcb104ff71596209faeda,0xb08a13fdd1658827fb9a,0xac4286f57458450deae4,0x128aa17edc15154376b8,0x8c2a86f76194550bf2e,0xe6b0aa1771cd615437ab,0xb94c2a86f76198550bbe,0xae5b0aa17b9ca61542f6,0xfa9ec2a867d53d85509f,0xfae9b0aa13f5cf615433,0xbc382a4a85fb70549509,0xbf2e1292a1dedc152543,0x2bebaca4a86ef6294950,0xbeae2312a15f5cf5254,0x4376b10c4a85f6711895,0x50bbce6312a1775cc625],#[0x542df3a0c4a85bd74189,0x9509fae3b12a1bbd8a62,0x1d427eba6c4a84fd73d8,0x87509fee6b0ea13fdc96,0x62d427fb8ac5a84ff745,0x548109fee8b16a13fdcd,0x5530437ebb2a4086fd65,0x259410dfaeca9821bf59,0x41204437eb9aca086fd7,0x5248110feaa290221fe5,0x5d5204437eb2a40887ed,0xb50c8110ff2a1902217f,0xb54b20443faa8e40887f,0xfd75c8110dfacb90221f,0xfed4f20443fca9e40885,0x7fa65c8110ff2cb90221,0x1fe54930443fca126088,0x87f9544c110ff6a49822,0x21fe54a30443fdaa2608,0x887f9548c110ff6a5182,0x221fe54140443fdaa460,0x887f55150110ff6a0a0,0x221fe545404437eb2a8,0x80887f97150110ff6a2a,0xa0221fe54940443fc992,0xa80887f96250110ff6a4,0x520221fe99540443fcb2,0xa480887fb5290110ff2a,0xa1a0221fed5240443fca,0xaa680887f551d0110ff2,0xaeba0221bf59740443de,0xea92a0887f55154110bf],#[0xfac4a8221dfd4950443b,0x7eb22a0885ff7254110d,0xdfacaa82217fdd150443,0x3fdb8aa0887f97154110,0xff464a8221fe4c95044,0x43fca12a0887f8425411,0x10ff684a8221fe909504,0x443fd292a0887f952541,0x110ff4c4a8221fe58950,0x443fcb92a0887f87254,0x4110ff6e4a8221fe9c95,0x50443fda1aa0887f9435,0x54110ff2e6a8221fe54d,0x150443fcaa2a0887fb73,0x454110ff2c8a8221fe95,0xd150443fc3a2a0887fa6,0x7454110ff4e8a8221fe5,0x55250443fca94a0887fb,0xd62d4110efaa5a8221fe,0xf59350442feb96a0886f,0xfd644c910bfae9a8221b,0xfb54a324437eb2a64886,0x5fd758c910dfacb19221,0x1bfd94424437eb288488,0x85fd7610910bfaea2122,0x21bf58d42443f6a92848,0x886fd6550910dfec6a12,0x2217f5d5424437fb2a84,0x4887ed5290910bfaeca1,0x1221bfd96424437eb2c8,0xa4885fd7690910bfaeb2,0xa9221fe1c152442febb0],#[0xaa4885ff7054910ff6e0,0x2a9221fd9c552443fab8,0x12a4887ed6254910bfee,0xc6a9221bfd8952443f73,0xb9aa4886ff6354910dfa,0xea8a9221df55152442ff,0xfb22a4886fd6454910ef,0xfacaa92217fdd1524437,0x7ebb2a4886ff6554910d,0xdfceca92217f5d952443,0x3f6b14a4885ff7654910,0xdfecb29221bf5965244,0x42febb4a4885fd759491,0x10bfae3a92217f5c3524,0x4437eb1ea4886ff62d49,0x910bfae7a9221bfd8f52,0x24437fb26a4886fd64d4,0x8910bfaeda92217f5d35,0x62442ffba2c4886fd645,0x58910dfccab1221bf595,0xd624437eb9ac4885ff75,0x558910df8eab1221bfdc,0xd5624437f3aac4886fd7,0x7598910dfacb31221bfd,0xdc953443fcb82a6885fd,0xd7654d10dfacaa9a217f,0xedc165442feb96a6886f,0xdf7359510bfee4b2a21f,0xbf1c9654437fb82ca887,0x6fe7259510dfae4b2a21,0x1bf5cd654437fb92ca88,0x85fd7299510dfee6b2a2],#[0x21fed5130843fcaa2610,0x87f95154210ff282a84,0x421fe54950843fcb8aa1,0x1087f95354210ff2e4a8,0x8421fe55150843fcb9aa,0x83087f55150610ff2e8a,0xa0c21bf59541843deaa2,0x2a3086fd6254610bfaea,0x8a8c21df55151842ffb9,0xa2a3086fd6454610efea,0xc5a8c21bf59551842ffb,0xaa6a3085fd72d4610dfa,0xae9a8c21bf59351843be,0xdb82a5086ff5258610bf,0xfacaa94217fdc552843f,0xfeb8ea5086fd7654a10d,0xdfac8a9c21fe5c153842,0x37eb2aa7085ff7454e10,0xdfac9a9c21bf5d95384,0x437eaa2c7085fd74d4e1,0x10ff2e0aa421bfd51638,0x842ffb9aa9085ff71552,0x210dfaecaa421bf59554,0x5842feb9ea9085fd71d5,0x9610dfae4b2c21bf5c56,0x510837eba2cb086fd735,0x54c20dfaeca8841bf595,0x1530837eb22a6107fb70,0x654c20dfacaa98417fdd,0xd3530837eb26a6106fd7,0x7359420dfae2b28417f5,0x54950482ffb8aa0906fd],#[0x93154120dfacaa8241fb,0xe50550483fd18aa0907f,0xf95154120ff482a8241f,0xfe58550483fd28aa0907,0x7f87154120ff4c2a8241,0x1fe9c550483fcb8aa090,0x7f97254120ff6e2a824,0x41fe54d50483fdb92a09,0x907fb7354120ff2e6a82,0x241fe5d150483fcaa2a0,0x907f95194120ff6e8a8,0x8a41bf59531482feb8ea,0x62906fd658c520feaa31,0xa8a417f5d851482febac,0xaa2907f56154520bfee0,0x6a8a41bfd8551483fb30,0x1aa29077f5354520efaa,0xcaa8a417fdcd514837fb,0xbb2a2906ff6554520dfa,0xceca8a417f5d9514837e,0xab0ca2905ff7654520df,0xfecb28a41bf59651483f,0xfebb4a2905fd7594520d,0xdfec3a8a417f5c351482,0x37fb1ea29077d53d4520,0xbfaeda8a417f5cf5148,0x837f32ac2906fd655852,0x20dfacb30a417fdd5614,0x482ffb8aa6905fd75985,0xd20bfee8a9a41fb5c953,0x34837ebb2a6906fd6554,0x9520bfae9a9a417f5c75],#[0x65482ffb8aca907fb705,0x59520df8e2b2a41bfdc1,0x5654837f38aca906fd71,0x359520dfae6b2a41bfdc,0x4550882feb8cca906ff7,0x5254220ff2e2a8441fe5,0x54d50883fcb92a1107f9,0x95454220ff2e6a8441fe,0xfdc951883fcba2a1107f,0x7f5454620efaa8a8c417,0x7fdd1518837eb22a3107,0x6fd7654620dfacaa8c41,0x17f5cb518837eb16a310,0x6fd64d4620efaa9a8c4,0x41bf54961882feba6a31,0x106fd5458620dfea4b0c,0x4417fdc5528837faa2c3,0x7105fd71d4a20dfacaa9,0x9c417fdd1538837eb22a,0xa7106fd7654e20dfacaa,0xb1c417f5d3538837eb26,0x2a9106ff5458e20dfaa8,0x4aa4417fdc554883fcb8,0x2aa9105ff7355220fdee,0xe3aa441bf5d9548837eb,0xb8acb105fd73d5220bfa,0xae6b2c41bf5c9658837e,0xfb82a2a86fd7459620df,0xfec4a8aa1df54951542f,0xbea9aa2a85ff7254550d,0xefaa528aa1bfd8d51543,0x2feb94a2a86ff6294550],#[0xbfae928aa1bfd925154,0x437eb10c2a877d521855,0x50dfac830aa17f5c8615,0x543fdb82c2a85fd74185,0x550efea4b0aa1df54961,0x15437eb12c2a86fc6258,0x8550dfec4b0aa1bf9896,0x61543bea9ac2a85ff725,0x58550dfac6b0aa1dfd4d,0xd61543ee39ac2a86ff63,0x458550bfee6b0aa1f7dc,0x91615437f322c2a86fd6,0x5298550bfee8b0aa1bfd,0x58a61543bfa94c2a877d,0xd7298550dfec530aa1bf,0xf5d2615437fb24c2a85f,0xfd62d8550efaa5b0aa17,0x7f5cb615437f316c2a86,0x6fd63d8550efaa7b0aa1,0x17f5d361542feb9ec2a8,0x86fe52d8550dfaa5b0aa,0xa1bf9cb615437eb96c2a,0xa86fd73d8550dfaa7b0a,0x2a1bf9d3615437eba6c2,0x4a86ff6354950bfee0a9,0x92a1dfdc152543beb82a,0xa4a877f6354950efac6a,0xa92a17f5c652543be3b2,0x8c4a877d63d4950efac5,0x2b12a1fedc162542feb8,0x1ac4a86fd6358950bfee,0xe8b12a17fdcd625437fb],#[0xb8ec4a85fd7198950bfe,0xae9b12a17f5cf62542fe,0xf38ec4a86fd71d8950bf,0xfae9b12a1bf5cf625437,0x7eb92c3a86fd7058750d,0xdfae6b0ea1bf9c961d43,0x37f3a2c3a86fd7458750,0xdfae2b16a1bf5c162d4,0x437eb9ac5a86fe7158b5,0x801600160001bf5d162d,0xe0032804a006e00b0010,0x1a60300056809e011601,0x811a0216040007880e20,0xe00b2815a029604f0094,0x38e06e00d28192030e05,0x8222041e07f00f481da0,0xf0134825a04960900116,0x5860ae01528292050e09,0x830e06060bc017282d60,0xa01ac834a06760cc0190,0x7a60ef01d0838a06f60d,0x8432083e10301f883e20,0x2023c846a08be1140220,0x9be134026084ae093612,0x85360a46144027e84ea0,0xa02ca85820ade15702a4,0xc0617c02ee85ca0b7616,0x86620c9e18f031486160,0x10358869e0d1e1a0033a,0xe661c7038486ee0dae1b,0x877a0ede1d903aa87460,0xa03e687ba0f5e1e703c4],#[0x6e209040c880e0ff61f,0x888a10f621a043088521,0xa046a88c6117622b044e,0x26e24a048c890611ee23,0x898a12ee25a04ac89461,0xb04ec89ca137626b04cc,0x46e289050a8a0613f627,0x8a8e14f629a052a8a461,0xc056e8ace157e2ac0550,0x68e2ce05928b1216062b,0x8ba2171e2df05b68b5a1,0x405fe8bea17ae2f205da,0x8de31706248c36184630,0x8cc2196632806488c821,0x806888cfe19de3380668,0xae635906aa8d421a5e34,0x8dca1b6e36906cc8d861,0xf07148e161c0637c06ee,0xd363a2073a8e621c9e38,0x8eee1dbe3b4075e8eae1,0x607a48f321e463c50780,0xf5e3e907ca8f821ede3d,0x8ff21fd63f707e68fbe1,0x40820903220464050800,0x14e423083e906e20be41,0x910221ce436086490b62,0xa08ac913e22564480888,0x37e46b08ce918a22ee45,0x920623ee47b08ee91ce2,0xc0930924e247e48b090c,0x57e4ac09509292250649,0x931626064bd097292d22],#[0xc09ae9352267e4cb098e,0x78e4ee09d4939627064d,0x940a27fe4fd09f293d62,0xc0a2a9446286650a0a0e,0x98652c0a4c948628f651,0x951e2a0e53e0a7494da2,0x10aba95622aa65510a98,0xbce5750adc95aa2b2e56,0x96462c665880b0695fa2,0x80b4a96862cf659b0b2c,0xdbe5b40b6096b62d565a,0x971e2e2e5c30b7e96f22,0xd0bb4975a2e965cf0b96,0xf6e5ea0bce978a2efe5d,0x97f62fd65f80bea97c62,0x10c1c982a302e6030c00,0x12e6210c3a9866309e61,0x98e2319e6300c5898a63,0xc0c929916321663f0c78,0x2e66590caa994a327664,0x99ba335e6690cc899823,0xa0d0a9a0233e66780ce6,0x4f669b0d2e9a4a347668,0x9ac2356e6ab0d4e9a8e3,0x50d809af235ce6b70d68,0x6b66d40da29b32363e6c,0x9b9e37266e10dbc9b6a3,0xb0dee9bd2378e6ef0dd6,0x87e70d0e109c1237f66f,0x9c7a38de7190e2a9c4a3,0xf0e589ca639267230e40,0x9fe73c0e709cd2398e72],#[0x9d423a7674b0e909d0e3,0x30ec29d7a3ad67570ea8,0xb9e7710eda9da63b2e76,0x9e0a3bf677e0ef69dde3,0x70f289e463c7678b0f0e,0xd467a50f449e7a3cd679,0x9ee23dae7b40f609eb23,0xc0f8e9f163e167bf0f78,0xee67da0fac9f463e7e7c,0x9faa3f367e50fc49f7e3,0xb0ff09fd63f967ef0fd8,0x4e8071006a0063fee7f,0xa05e409e811101ca02e4,0xb104ea08e410681d1036,0x1c68361064a0be416e82,0xa12a4236843107ea0f24,0xe10b6a15e42ae852109c,0x37686c10d0a192430e85,0xa20643ee87a10eca1ca4,0x51122a23644568881108,0x5268a1113ca26a44be89,0xa2d645968b0115aa2a24,0x9118aa30645ee8bc1172,0x6c68d611a6a33e465e8c,0xa3a2472e8e311bea3724,0x911eca3c647768ed11d6,0x83e9051206a40247de8f,0xa46a48be914121ea42e4,0x8124ca492490e920123a,0x9be9331260a4b6495692,0xa51a4a16941127aa4e64,0x912b0a5524a8694d1294],#[0xb3e96512c2a5764ace95,0xa5da4b9697112daa5aa4,0x8130aa6064bf697c12f2,0xca69931320a6364c5698,0xa6824cee99c1332a65a4,0xe1358a6aa4d469a51346,0xdd69b8136aa6ce4d869a,0xa72e4e3e9c31382a6fa4,0xf13b6a75e4e9e9d2139c,0xf769eb13d2a79a4f169d,0xa8064fee9fa13eca7ca4,0x61424a83e5066a09140a,0x13ea241440a87250c6a1,0xa8ea51aea331460a8ae5,0xd1494a91a5216a40147a,0x306a5d14b0a9525286a4,0xa9ca5376a6b14cea98a5,0x61504a9fa53e6a7814ea,0x4aea92151eaa325446a8,0xaa925516a9f1536aa625,0x71568aac6557eaaa1550,0x62eac3157eaaf255ceab,0xab4e568eace1596ab225,0x515c2ab7656deada15ac,0x7aeaf315deabae573eae,0xac0a57feafd15f4abe25,0x61626ac3e585eb09160a,0x936b241640ac7658ceb1,0xacda599eb32165cacaa5,0xb168ead0e59f6b3c1672,0xad6b5716a8ad465a76b4,0xada25b36b6416c0ad765],#[0x13100adda5b96b7016d8,0x86084c4021013084c402,0x505121118445448404a5,0x41121014450448402002,0x141120c5504444841511,0x25114112104495044841,0x504431514110c1450443,0x4110c945044314110854,0x1114150c460448544251,0x1440484131008584c403,0x613104c4020812100c20,0x6130e02184cac416010,0x48006130e0218ac4c480,0x416a264101021904440,0x88504041810085048444,0x2100c608840316100830,0x21210085a8990404081,0xc4c484150c221010544,0xc5a88301841210081b,0x1643040610484020c131,0x4048316a224101030402,0x2100c54104031210084c,0x86c51412103448403a42,0x61615040210149054403,0xa2251014040192881894,0x66406150d90544036400,0x151225109414885c1848,0x31522100c2018141c406,0xc144021525100c609440,0x60510548840315a5100,0x28006119000544040d0c,0x820512100c1440483642],#[0x90944040c22151010404,0x4141040412c52b101058,0x201440484c5081012104,0x3142090444c508241110,0x13049490444170824111,0x41110204844305082411,0x251110201448444c5082,0x22511102048944440112,0x25241113044894444c11,0x2c3011210204894444c1,0x484430403170c100c22,0x201448444c1122511102,0x28800589451501122510,0x10404161504020325189,0x84440804030706144414,0x10084030512100c5c4a1,0x40402100c94402051008,0x42152225101010084060,0x100840616152510111a9,0x84041105041010585494,0x161018582a5860994100,0xc585418100c086040210,0xa5040210104010f0b100,0x48315081211101008403,0xc444021811100c4420,0x15110c5c544844415111,0x31815101110544844312,0x8544031015110c405444,0xc045448309c11512108,0x6100e943448404001615,0xa510130c329688404221,0x429442210150c5854403],#[0x10c54402a510130c3288,0x81111210144448312011,0x4441512110e94444c3a5,0x45440112171110540448,0x444c38111a5121004484,0xc94484432512110e94,0x44101032944440405111,0x5041110105444403a511,0x41110150c1060444041,0x40311a54410103046944,0xe0448404111510104494,0x4644841503011210168,0x28e06944840115120c0c,0x10359448404030115121,0x511958d04484650c1110,0x10100444485446341126,0x3100c0c0448544041115,0xa540431312944c403051,0x4c4031513100c544c403,0x312944c403a513100e94,0x13100c544c4034043a51,0x48265101195920840415,0x5046513100d944c4036,0x430828280651411960a0,0x32950840405a4421010,0x10569108404a54442101,0x1011086040415044210,0x1010310a94404a442a51,0x510129108544044442a5,0x82101194320840404421,0x513100d9209944046564,0x31513100c1208544041],#[0x544041564821010544c4,0x448544432512110d9208,0x14544844317150112111,0x14484441202001125,0x15080054443151225111,0x4431525110c609444307,0x2110c4811215110c5448,0x513100c5c4894444151,0x4c4031325100c4c94403,0xc4c944030403160c94,0x3012518085494305131,0x11118100448443171504,0x461725110c5494443040,0x30510120c5c549410044,0x4485c444171108044844,0x4443171507040301180,0x3208544040112110c10,0x11104454483171512111,0x15110c4054443181510,0x45c54315120818544831,0x541008404c205a410102,0x1008544030402161010,0x1112130c5c4830402151,0x31115120c44544831715,0x444041511100c144440,0x40544430410181110541,0xc041044544041125100c,0x84150301121016844838,0x4544841512080c04644,0x445440404021015100c,0xe144840303011215101,0x540160e1448403128510],#[0x5840215100b08544031,0x15100b144020fc510111,0x46c510120c342314404,0x44021510085c541c100c,0xc083054515040210105,0x4544844515c340171064,0xc54484430540170c5c1,0x1105c541448445151211,0x100c2048544441815051,0x8121511105d90443c512,0x44081215111314484030,0xc0861512110c2090544,0x84150401111058541810,0x4040403001610540c044,0x5c40302001610100858,0x485c40401111710100c0,0x50c541c20240150c0c04,0x42421507085424203401,0x22060e881c1830607085,0x183170108590e0008407,0x280060c1812206089488,0x88831780060d0e040830,0x220818ac281412b0e041,0x44222814109120448206,0xc24185030981410c18,0x182410c081c18222410,0x40c0608301820c06083,0x30182160c060c590e001,0x20c5040ad2c4c50c0608,0x24080610881848322061,0x4183240608589040307,0xc6604901840781060c8a],#[0x2524100c944022481060,0x8641822504100c10182,0x3068009081a0030580,0xc36001434215060c2016,0x100858550c1840580060,0x8842581062b101504215,0x44832522811010960418,0x8a0590425810622101a0,0x1894883170622251018,0x100c8894403072508061,0x522410c5e141d0442215,0xd9040281060888005438,0x82101508604021825100,0x3430941840625640c641,0x541101a1495904251008,0x888341150a14402190c8,0x80d081820c19060c5c1,0x18380050d0c5c1828005,0x7220a042c2800b086430,0x851722060c0e040831,0x5c1842502100c94110c4,0xe084c482080708201c,0x438182430e08388c1831,0x10e0408422044c482060,0xc20807085c1820206081,0xd04008834106220c201,0x840061048205c3174001,0xc1810807060c5c002170,0x623170c405c20622050,0x17084c11312090c5c183,0x831712060c5c1848381,0x30c19110c30602090c18],#[0x1c18203001904217242,0x60c9418083254306021,0x582011508201c21722,0x6a50c44144030522060c,0x81838105120c60182110,0x4588c5431912060c144,0x148821025220c2048212,0x4041004444020807250c,0x6101411210050c201448,0x17250840942c30805070,0x10049440218060860402,0x860c5488210060c5c183,0x40082410b0854402a523,0x40310045409043100b08,0x20c09082411722085854,0x50c24581830541080034,0x42428018150c1c117222,0xd0854301c31915800c5,0xa1204003150d0834145,0x434481084e140030716,0xd100058381160c0c1512,0x170c16041c31640250,0xc64002810ca50c64113,0x31300170c89002070506,0xc4c00583150708090054,0x44000c60243031815090,0x943031509080d0054318,0xc05090c2464219000826,0xc6400219000864544830,0x8400160c305420440150,0x1c216091506121060003,0xa1150c5430215090854],#[0x80c60243034004541824,0x43150909028c54300141,0x8541821402190c24329,0x1c32580081e021431509,0x782081e0820782085c54,0x62507101c94216044810,0xa144440785081c942080,0x83150708541854208581,0x26150841825110c00550,0x91208644822500150c60,0x10a041c5821604485421,0x2080608581c203010804,0x50c1c125080706105808,0xc58381050e0484307210,0x10c1c0421643070c1c8,0x1624230c1d110c30725,0x430725010c1c2018300,0x21508201820716081c94,0x840141c3430484141c30,0x48422521085c54218070,0x162508940420806250c1,0x1104601c2181108601c2,0x420704641c2071608441,0x1211010c041150708148,0x45821511084410104041,0xc1c30225082418216048,0x15428010241182508545,0x4843160008550830319,0x644000c5818303810512,0x41c31543060c05005431,0x6050c0d101001708181,0x81831742060c0864003],#[0xc3014183190c060c15,0x2100160c5d0094385210,0x80d0054318000860302,0x30219000c24143031509,0x4544830c05090c250864,0x80b00219024100106,0x58215120812090054419,0x5070c542418300180800,0x500315420c0c54242171,0x2089005444022800c560,0x523400a104011621070c,0x1c32240150d008a0031,0x80401034302401508182,0x160030122150e1410522,0x10608585418324150822,0x884442450b100c584421,0x1606220c2054443210b0,0x4015144011615100c401,0x584022386084010a4523,0x9030d4008403c2242108,0x20108548824022085884,0x4084810608220c885422,0x50e001080416005430d2,0x30a8008145440317221,0x22005431924150c60544,0x54402150408542801508,0x310150810542151008,0xc545d0031511085609,0x431505110c8824205174,0x85c541c3060809005c5,0x31715070c20845431811,0x711082c54211045c8884],#[0x88c185442108085c4821,0x110c64544831815110c5,0x54482151108885420115,0x31016085c5821516100c,0x7070c581191608605840,0xc443401708485c583151,0x1917120c605]]
set_option maxRecDepth 16000 in
def g219H7 := limbs80 #[#[0x270e8101e06000600400,0x2010c000341b008040a,0xc0203008b402000100c,0x6830261a000040000010,0x5000ac0e31018380e600,0x200008040a0600034000,0xc32020082c0a021a0181,0x2842050083c0a0c0000,0x18006815008041c3118,0x260008000020e8300600,0x1205008ec02570201400,0x1c06010081c0415000c4,0x38640a064500438040a8,0x7000608e030000814060,0x4190000ca8000081c3c1,0x800020601c0201028280,0x80c04050284c12080180,0x41808102203004040d86,0x40900c1a1c05008140e,0x20101828001f0400452,0x20021d0580000000481c,0x8fc2e1000800060d018,0x3028081402240540e070,0x2010b808182e2a020080,0xc0403008000000020040,0x8f0280b0300426530981,0x178340812038009c2505,0x8024d140040e05,0x300e0a8ec36050183800,0xc0000001880582200000,0x308802730f0107e011b0,0xd1218c02000987872300],#[0x506000120009034109,0x4000403c06040f8940,0x1c02090380008000d0a,0x5048002903024120001,0x2804014401e000300603,0x60f0b99c3a110005008,0xcc08010085490070506c,0x8bc183c00014081a480,0x10500c1e040380804020,0xa1201008007c00810300,0x60a02854b8100d8045,0x8041e01011445e07110a,0x268283e0c0e01428010e,0xe808a00000000060c,0x22010285c8804228b066,0x34000504001880500090,0x68013c000c80c6401100,0x209804005a46000080b0,0x1a0383008120194c060,0x45607008187e93260580,0x38000f1810806b7008e,0x9068001b1584c020500,0x9000008c146c16820277,0x2292474249480000600e,0xbc700000000000000500,0xa35fa0053002e78201d1,0x780dbc00ca0000000007,0x54033404445e0b780000,0xb3102458322b604e3087,0x203100a9307a960aef11,0x880598378f010800001c,0xc45a90ca0000000003],#[0xbe005f281b3000000000,0xbd148696820a00000c0c,0x485c0000583c90003700,0xe8849c11e5838a521fc0,0x1e07084445880c5f0186,0x200300000483300000,0x3c42049400001044a000,0x28860b3ac185b818c00,0x10408ce786c187f416b8,0x6443cc0c176d030b0898,0x90c0283c44fdcd57ec32,0x2d40085d20258c1fa088,0x36793320e05945d1938,0x3a240407ebae717c0aa9,0xa608af2082a809ef544b,0x28c8338b321a222b2e15,0x83ca83c18864e009af82,0x9c9c439d711156c84e4c,0x50068503a29320ca0b34,0x47c1cda0375000014022,0x5168133a00fbc70a8a01,0x22a0411800000d0004e6,0x887a2004af01d5c0578c,0x48847b01d83a98090260,0x346cdb3c4cec014d485a,0x6af80c5a0887e832cb01,0x223f8070610215b9c100,0x3056c600624d469203fc,0x92114be04fb8089c00b7,0xe16077c60bb4c1132287,0x2add064aa632a01c1503,0x21bb049860768885709],#[0xc81df5038ae480690030,0x769065404948069b8875,0x38c80c4f07466068b50b,0x4cf58307d485020292a0,0xc1503036d00000045320,0xac20638106a019a840f9,0xf40015c84285067900b6,0x6f0000008118403eae0e,0x28113981c0e08534e,0x20b74000000000c63600,0xf4020448551406c8210d,0x9fa0d3750f9781b4a028,0x22bc08b7a140180d3120,0x413984acdc8505042420,0xc0545e087b884900000a,0x6c0061a05c1d01df8400,0xdf000006e5218479408f,0xa04224e062fad02fd11,0x81cbb030aa09a85003b8,0xa0154c930380971c4084,0x703583070324a080018,0xc1510633021064ae4000,0xdac10c480694246dac5,0x808548100d4093030008,0x80150800001151610853,0x900000590b1e043b00ed,0xb2002cb00a8f134028c,0x3018ed01a47058260,0x803b40000401ca000000,0x1409d8c223a0231204c7,0xb60e4f3102b703ef0000,0x56c42669088a812d1d06],#[0x56e4e07790c6300000b2,0x41440c038a89408041bd,0x1b24346019f809400000,0x39d240680c2b40d69042,0x39f1202a40a1541230b1,0xb949203a2000574450d8,0x792700000100a1f04069,0x4e92603549a000000000,0x4510242c26a4a0a29c44,0x120e842ba037260f2305,0x216471054704c3a01150,0x2c47cb8342f01798202e,0x6b40ebd88f4b027aa03c,0x390029233de35da605,0x9118892c0032e031e00,0x38206c0042f03dd2,0x810ec0b52a067a0290,0xd2a1e89cff800000000,0x1094127e301,0x106403f800000000000,0x1a0fa682191237ae,0x7505f8000010615182cc,0x26c04a380ae2c014083b,0x35a105e640047c058881,0x40067d44758,0x5ba0410306004d684410,0x783df4087a8cce80000,0x6b000000000004f5c000,0x19bf84308069ea891880,0x94bf8000000001c61f38,0x74c85fa160f04a4ce73a,0x9fc84f883526530ac816],#[0x1c052f83ee40137602,0xa04345a580000b118600,0x88cbc4805791c7007352,0xd80dacc1ba591a540882,0x2b8009ac1904416c8113,0x55a000024227cb9d9006,0x9116a050100a9ca2d8d0,0x6034b449701022284405,0xb208240028c0000688bc,0x40341372034750aa420f,0x5800000406dc0000080,0x1f1a01b8c0af7806d40,0x7211870130406e301edf,0x399145074a5085ec099,0x38539bb625a4d270c000,0x1aa41892000002a246d0,0x16c18396c20f1610fc8,0x1c199ea37d000012c1ff,0xb00000798d3000000000,0xcae40e92038600000010,0x148c13af1238f20afc0,0x6a236c086c02ff4008ec,0x5a790138000000001,0x9300ed2a5e2783b88022,0x22f601e00937921ec673,0x635ca0fec00003806644,0x822d40167b02a88,0xda20a6a0642c4d0a215e,0x1900001288e681ed318c,0x27800001285400000503,0x18d60274de090c41f890,0x80000000000000000003],#[0xd60064007a00000381d5,0x357803cc207521110485,0x6a887000004433e08,0x8860202c093328000000,0x92b80000301cec43b6,0xc6046e090a1000000000,0x30cc92d00000e071e804,0xeccd0fa000000078b66,0x4853dd002508bae0182e,0x9c08c808f07a1f080794,0xf540e43c0bb200e55318,0xe017b805c00000f41,0x2170e40f55545a801000,0x907ee6103b605df020f1,0xe4232fc0a65d9285a170,0x261083e409f8c18fa190,0x3db0000000003dca50a2,0x83cd90284e08dac93d09,0x53942a033c40189d0f4c,0xdf08e3c05a62020a401d,0x6800fb02fc60de4d82,0x1b1183769562fa0a0400,0x488d9825a00000c25954,0x190569080fe8ccf,0x9b010400000554b02499,0xd9a80db3811ea0145846,0xac781976812790613e0,0x60d7848c7b90cef345ba,0x4e0a420d596288800001,0x54681b4808d300efc40c,0x32c8035105ca38173100,0x20644a54603a3817842],#[0xf010ace4e598dba031cd,0x8605c2a287641d300000,0x66f21cf206f6c1529b95,0x26e0000020dcddc9fe81,0x92d0a088560ea8000060,0x800000000100d1add9e7,0x782355726ac08f60198,0x404380000066594000,0xce900000a07d80000000,0x783116218baa2279,0x811a20112501f000000,0x18c10700000904a00000,0x203d800000c05,0xaa2841a9c204f0000000,0xc630a902358904b048e0,0x1008b80000e071c,0xc0000034846b18dc0000,0x302f5f66,0x7387004fc00004820000,0xf22fa0000000003836ef,0x8a0093a0b0b000d30991,0xbef119a4268b504c8003,0xe6e019140ac201dfa08,0x1280000008403100d8a0,0x351184027a80fe6,0x668006d0026125344024,0xc780f900001c041111a,0x580ea0000000003c1,0x20007803e8444800,0x483e70a24a12b2a08fc,0xdf045b70102b07f4202c,0x2ec411d00000d86ae442],#[0xb8fc080800000000068,0x5010f000016,0x664410174fc34f004cc,0x8b602d40000612790044,0x2c3423d400002808ee05,0x47014812380b013345e0,0x40682419b7211c2,0xf00000e0fc00000001a7,0x4b30820c07d9401d8404,0x306d3e81544002683,0x8070973fbe07b0000000,0x301aa304db209c5ccaca,0x8d020d00000204e74453,0x4a681bee242980c6d404,0x4d8f828fc01c2e0bc4c8,0xc183123d6100a9cc1de0,0x200530833d00000a0301,0x1500a19088cc84fa6447,0x381c380000c4656200,0x66c0000000000000000,0x80025013d390b9963096,0x6a0bb0011400000021cc,0x41e01d740ca9811fb218,0x512e42d78c60fa05a302,0x46816065e589b9038490,0xf03020000341e9492aff,0x500422e812d083638402,0xdbf0634508900000382b,0x3f22059420d66c059a88,0x3b3ab032200000188dd8,0x108d1521d3a81140463f,0xc703c7d978a80f880000],#[0x100c7480ec0064d111,0x17db006b340e60000000,0x1210a032100000000020,0x40000289345007e00003,0x5e81fe98385f030f60d1,0x2c9144bd0025b04c8a0e,0x536115d042ab31a2a0,0xa0fa2c1cca81a1520788,0xe868025018983b24436a,0xda000028515ec0393037,0x5ad04384088d00000b81,0x18063782af60,0x31180000039000000000,0xdd05b8c0d1000003336b,0x2b6039e00c304c6da90c,0x12d7064e000000000032,0xe04ac84024014fa1,0x4099c0000040b2081eb8,0x138962b2252a036141f2,0xccc8260507ba0000141e,0xa1a8f01280000200,0x54c30822300001c00040,0x648c600000b00158643d,0x1000000000081166c4f6,0x3c941808fe202a2407,0xad000005805b300a000,0x740000050529a,0x488cde401000000322bc,0x73a0be580dde8883700e,0x3fbe003940e430420806,0x5013aaa20820e1880ed0,0x1807c80000488d75],#[0xf000012266f809dca87b,0x227086600003006cfa1e,0x744511e207ce820a404,0x815e000fd410201c9f21,0x80448c2201ac95000003,0xc8803e6002dcc55b004c,0xae28279025098018280f,0xc5cb8239331a420f80c1,0x417d218c9300f80c93f0,0x600de2393a447bf241de,0x8a9445692acd04f862a9,0x13000002322ad01e9209,0xc90c47b890efa60a7a0,0x41564887481ed405d16,0xa241470165839400087c,0x4f4908990b5188bf100d,0x789643f080eeb041a611,0x4abee77bc18438361a0,0x531afe300c017024072b,0x4a0006c05f0d927083ad,0x49911980000088c93004,0x11d60139a108f008e41b,0x443b345d2222241a858,0x80033400956255b886fe,0xd703d59042ac009c8105,0x1b98134e6270e0bc0810,0x1ce303a440407805e8c2,0x816910419742d8e0a34a,0x81a700000b228400000,0x7d48816032d137980000,0x5144077283d1f0605a08,0x766c15390270a02b6c2],#[0x7ee41d44233bd07b88,0xae03aec11109909f066b,0xa582324018960347807c,0x650890a400004031ef46,0x6d560e4c000068371c2,0x42754f260fc4d1b88edb,0xf428b2427a9cec703ed,0xdf180e702028190e8000,0x5900001c22d3c0bdd02,0x7823e0000340c4f9,0xf237ee21c58082400000,0x78404000004636840bf,0xe25009200000e23cc000,0x724ffa633dc8,0x410a600dd00000a82680,0x4000000000504b600001,0x4b0451188d8070b6f027,0x6cd8154c0300b23320c1,0x301bd80000443e604,0xe8b4b4044411285086ae,0x5a44791ca0c02f2a1183,0xe23bec0ab902aab105,0x605b6845200000000,0x8c00e5000004918400,0xf95dfa0dc800004a87de,0xd029f6071dc8c980000,0x4c00000a810400000000,0xe02e4000000117f03,0xa3280000142320895900,0x411aa000000000281912,0x5312b19075260ec7cc6c,0x68304f7361aa218004],#[0x3a00000d40bd6af6c00,0xc17be81f091312c00781,0x2417f181e9727b5e00b7,0x24000048233d084a0000,0x864c85dea35ba41e580e,0x41dc07b000000000100,0xc080700480041e180e08,0x400003c9b198039106de,0xb6a8b778c39003d36466,0xbaa08b34182f18c8821,0x3e093e829177,0xc930480d82c00ed10be0,0xc3042e00432412990348,0x42240c0000024209fa04,0x356a076b4055a81fb70b,0x8105e035840231811c50,0x800de000012005f80b8e,0x9408d3982386033acc88,0x5d98274304dfe102d007,0xfb1812af01978ecfc00,0x90f3801ff42092608df5,0x1c14b8899f5224d442b6,0xf985f5e1a20157fa2038,0x85a4280f300000c8c,0x34152000007039c00,0x68d6a0cd300000000000,0x446d3816ae816c111f9,0x3f023e9c1996005ce053,0x41b2591ffa01,0x476000030072039bf00,0xe229660b9a8553a0097e,0xd0023620a574037e8087],#[0x311ba8246c507a0039,0x16e7085a401380000000,0xe3f740ae49b7c1b2b0,0xe01af124e8808a795a35,0xf80257a334ac05d1c163,0xe8000000001e44f84c5,0x1bb8000094646043f642,0x4213904160000000000c,0xcc0c5800000000160b11,0xd541a080000842d7a41c,0x1c0f5590f04001b101,0xd0d4109992540000000,0xe000000121f7000018,0x2c08844149681cce4010,0x7be0072047eeab6d4049,0x17e000028208a110ca00,0x465a228a8000030012b2,0xc0e2298280233aa,0xf31bba062000003028e,0xd0f02bb40ffd84b38000,0x703c2909d1c222b08,0x81f7e31c96074281cf00,0x203cf2080800001,0xdabb81a0556c0bac817c,0x6a7038d00001ce768421,0x603000003408e0000288,0xcc68602e70000060a1b4,0x9204d212698441a00003,0x1cd03b00000a072ae02a,0x32100b38000000001e45,0x4304c0beb033e001ea84,0x40b58005f00000a],#[0xe80176018a289845003e,0x148d290c84420661113,0x7ba1252fd121c8992000,0x6800000000000000074,0x4053d485a58181f280a5,0x4c021200000000048182,0xc7c704fe01d000002899,0x13a801000000381dd798,0x9b92621ac00000000048,0xc03924737500c60c0376,0xfd0021805086101580e1,0x9ee8363200afa24a4815,0x8a0d030db00fa000029c,0x49180000b06f44e7904,0x981be000009467e6032a,0xaa4890a02d1e17d88812,0x2b6c0767828b00000808,0xd7d40b190426f06e0a2,0x2080000d218ca,0x640e73d01b98043104a8,0xb40000001630385c7435,0x2b72435c0000310cc300,0x4bf4064b81038a16fa1,0x3047c046b781ff280939,0x8078c66efdc20c2814c,0x6cc03f16075b40d40000,0x1521040ac0b91c10e712,0x2eea739f80734c16da8,0x3c26d7075980df40cc7e,0xe0000070558000000000,0x7d000004211fe8e90421,0x4cd09006251a0032440],#[0x93e9019ce025a205dd2,0x300f5f8439b089cc04b8,0x5280979008f605934049,0x6ca40ec0a039411e2a06,0xf3b0932c10c726648e0,0x720b480a8501e800001e,0xb001344c674907a402c5,0x6c000024cd8881366131,0x52608d8b01d780069801,0x23300938c0c5388df00,0xd04e460445cd179908a3,0x3016800ebb0056301dc,0x314080280488c12e8000,0x259c0813c46d740f1e04,0x11951057ce04de511e48,0x300567053ae228f10b89,0xc280cca24d0a0a71d10a,0xc3f2ae2e31ab60a9880a,0x8896088fd0575cc58bd8,0x47c3a984b0621880d9c,0xd99eda190cc07974c040,0xfe4091c010ba049140ce,0x3f08745904ef2113403,0x9b2403b280ab040b0a1,0x48741f5202061062f6,0xa888404223283cf65311,0xb1c0439802790355705f,0x4d5e03dd8159c838c227,0x73100c9b80edc10c252,0xd212ac0ef3c46a5844b9,0x10038c00001d4bf30450,0x203c028467813eb006],#[0x3390255d20a325032000,0x3ccc00168a1e2c440da,0x800004056ee030b80d4d,0x8313b045d610dbc0cf,0xc16044cb033106350000,0x193700af340c60460688,0x8127d81e69230d008945,0x1cd13e233cb81396470c,0x2405fa82e5401e20000,0xf2000002a37800000000,0xa8e9018203a1c114012,0xc4926421a00000906d14,0x1ae4ed504ea819640356,0xbe007900000491ce0000,0x268035c9cff60159c02,0x7ac00000000000000d4,0x1e0f000000000006,0x40000088d26818700000,0x931810909000003822,0x201b6000,0x829af069340a0cd18680,0x4827300000c41f6c0964,0x4f007b2316be00d20157,0x7018000000d0d37022,0x180800002057300d4400,0x4134f39ca00001046f84,0xa0029800000000020524,0x340bcb015cf02298234,0xee400000000024064000,0x23400000000000000c0,0x4221000003822b000016,0xc0000000000000030308],#[0x511409015,0x1c600001c93bc0b44000,0x21c8000000000191d742,0xf21c9c19d00000f,0xb131c000020067a8175,0x85601f8c22aa80ff0000,0x14e00046e0516c86af08,0x13a806ba088558,0x221100001a0bbc81950,0x6bb40b24cf8c965c0dd,0x682ea00000e23c0000,0x3400000c04800000000,0x181ef102d1e0ac98,0x68c85000000000000000,0x8900cec03f3a036106ac,0x36400123c94c7031d60b,0x2c126b83dea0335c6,0x201b100a5c0894e00960,0x1402f4c1bfa8077a40dd,0x118aee68217800008212,0xe404400004a893d05,0x381fc8000000,0xf7288000000000000000,0x3743dd200bc000000000,0xb01fb647f000006911,0x240e4c847000,0x39bd324c600001812580,0x552fae04cc00005,0x54887ec9782000000000,0xe0355003,0xa04ac00,0x8828108ee00814000000],#[0xe95b700000911c800000,0x101c5800009404ce018,0x7240000783eb00740000,0x2cddf680d20000020,0x2e50cd0ae80000000000,0xfa84994094f0116320f7,0x1020b80000d067,0x24c82881fa000,0x0,0x8865800000,0xc507cf00a08c877301d4,0x1f804bc00000801be83f,0x1e5220d2a0b5c0000122,0x8728d40841492af8,0x483e6000004096000000,0xdf8164543d7e00ba00a5,0xe39043a000000000341d,0x44980892300e600e9c65,0x161a12070000040f0e0,0x800001027f205360037e,0x4000000000020011c87a,0x4f100c300000600e3440,0xe445211c89aa0000080,0xc0c8dc1aea8328842aaa,0x1843410517a844dc00fe,0x2000a588056800000000,0x1ff2e6bd944c4411b623,0x422a6d0d60000081,0x304ca00000002a800000,0xc0000000000000008216,0xd9f115d8466000001020,0x140fe251ae402],#[0x109a00000a028581ec80,0x800ba000010480004585,0xf9818d8250b009a1c0b7,0xd180383a461860bd9854,0x2bf1072480d500ca480,0xc01b0a890a319920f8e9,0x641bf7008b00001e01eb,0xf2001a80000740cae81d,0x9a814010079703a688d,0x1c9]]
def g219D8 := limbs80 #[#[0xd58420af99210af59210,0x98c20b758c20bd98420b,0x84509f994209f59420b7,0x850bb58850bd98450bd5,0x10bf58810ded4250bb98,0xfe08110bf59410bf58c,0xfe8c110fe4c110fec811,0xe54110fe90110fe50110,0xd8910bf58910fe94110f,0x9510bfd8d10bf58d10bf,0x210fec8210bfd9510bf5,0x10bf58610fe54210fe4c,0xbf59210bf58e10bf58a,0xbf58c20bf58420bf5961,0xe94120fe54120bf59420,0x59520bfd8d20bfd8520f,0x8620fe54220bfd9520bf,0x220bf58e20bf58a20bf5,0x50bf58450bf59620bf59,0xdf54950bfd8550bf588,0xbf58650bfd8950dfd495,0xf58750bf59650bf58a50,0xd4810ff54810bf58b50b,0x8110ffd4c10ff54c10ff,0x110ff50110ffc8110ff4,0x10ffd4110ff54110ffd0,0xff10910ff8c910ff4c9,0xff14910ff90910ff5091,0xfd4910ff94910ff54910,0x54d10ff98910ff58910f,0x9510ff59510ffd4d10ff,0x610ff54610ff50610ff9],#[0x10ffd4a10ff54a10ffd4,0xff55210ffd4e10ff54e,0xffd4420ff54420ffd521,0xf54120ffd4c20ff54c20,0x8c520ff4c520ffd4120f,0x4520ff54520ff14520ff,0x520ff58520ffd4520ff9,0x20ffd4d20ff54d20ff98,0xff54620ff99520ff595,0xffd4a20ff54a20ffd462,0xf55220ffd4e20ff54e20,0x94550ff54550ffd5220f,0x8550ff58550ff18550ff,0x950ff54950ffd8550ff9,0x50ff58950ff18950ff94,0x2c044000ffd8950ff989,0x1e07a834c16208f03681,0x8343d61c20cc85c02801,0x2d915f0a544e62581140,0x8f0473036f1a68c90604,0xc486235914085c4051f1,0x1159ca7c523280936096,0xb863a30c17d8b9a5a42c,0x9b1c50de46d035019f8c,0x207e73db9e54ef47513,0x47c233d13e87d43120c9,0x13dc9c54d525e92b0921,0xd5722ad1516a54519284,0xed824bcd5d22dd167ab0,0x5469933ed96cc9463930,0x9b5c96e146f5b6b5b08d,0xf8d7b5bcede16ed4755b],#[0x42b611705b8193fedf96,0x31db8dcc64229712986b,0x94bd2597294935c92643,0x23430a004f0a73335b99,0xf15676adb536a86d33e9,0x24404b54d9e6ca1619a,0x80132021300442101488,0x884c002202010400a080,0x4c80a4c0022020206009,0x5284462248290101000a,0xc80a440120a405240400,0x222110014910141000a4,0x915024460a5088614901,0xa0401026201264032800,0x880a889100d101284480,0x4a405440491010094264,0x893202a24a4880815100,0x84480815101244052414,0x84049480a14a11202052,0x20192104430809290101,0x910102922000a9118611,0x84480814041244451014,0x91005491014290241851,0x44050a3011010293201,0x91110280249488a54980,0xa44812102a1244440c94,0x460294911100a5244440,0x102c2244040a488002a4,0x8120c28c224040a18911,0x8482900c8802a4880a14,0x80080829520306241488,0x18a920a4440400292222],#[0x889149100c0010a48a91,0x2912a00292203068a48,0xe04b920a4450808b052,0x8c14a4842e1412523049,0xa94a110cc050694a1118,0x48a94910122a5444880,0x4a4078a94910122a5244,0x6848862520295848800c,0x52a22048529152922240,0x864c90e96288209088d1,0x54b14312104464a8c345,0xd1414a18912208252444,0x4a3864a4841114117868,0x44a20910111c3441a092,0x1c2488929024ba52440,0x122240709125203980b1,0x5325d2224a4064889290,0x52a41014811152901a48,0x22487889042520296880,0x811048a5242170a092c1,0x8a5202980b101a44a44,0x24319090d1a582487889,0x60a0529320304868e0a5,0x1a44b08810052932021,0x223c4480e125203180b1,0x1424929114ac14201292,0x5293222454b112112034,0x80950872c9114a4c80b1,0x74a4c80804b44490d1c2,0x45488e243430a0074a48,0x224164a4090894406244,0x1429488c6220382910a5],#[0x4925222a14a488891124,0x202968805225844072c8,0x28295085224888892125,0x129120441424529214b8,0x22224229480a602c4069,0x14a48632121c14685292,0xc2445a0210014d868e0a,0x242001481004ac4490d1,0x440548880102a415488a,0x1a222901d2222b1480a3,0x292152220040a8c55222,0x49111c1158284b802444,0x84280245488e550c1001,0x88a4888c84a928a44510,0x840120a44a8c5508]]
set_option maxRecDepth 16000 in
def g219H8 := limbs80 #[#[0x6881d408040801200705,0x80020001a0a0c1810,0x102000c105002800004,0x2b00000820c18007060,0x83065c701101820b001c,0x20a081122e0812e0a198,0x800080061008c000890,0x182800200000026c08c,0x10307100831420000030,0x810a04a00301018c00,0xd022810846000010c4,0x870c08a07301c005204c,0x3082c301180418000dc0,0x8000002000000400a0,0x62c39006042001420a80,0x1001e041001200043800,0x400e3a540030c4c80100,0x68d00480890400181220,0x86067800404000110c00,0x1e683100c405a506006,0xac420c00004062e5418,0x6002a100081803a38684,0x4805c04111062c4281,0x8411001430000280000e,0x10116101b700016ce260,0xe160590f16bd4860200,0x6002c30224211920e103,0x2c000000000d061960,0x81813c3838d201448d,0x5c30206008010e4c0050,0xc2033c0018226cc30168,0x111018e303d34099005],#[0x33046e8927b05d900ea9,0x127202f2215f380b724b,0x600002861b00fa7017e6,0x21b6146881dc000020ba,0x1213980000000050,0x80bec616,0x4f6c0619e47ab818200,0x81a0fd72230012500001,0x9b0c0000738ae1112402,0x480001a101025b50013a,0x43e0909e000060595513,0x1e0b9d819ec413f82d7c,0x3400c4521c88afe8000,0x8000103748105d602ec2,0x91100f2208000000c098,0xc15ac0196000000001f2,0xaa0000000000157d8504,0x1e094081b600005bb,0xb00001e056a0339c53a8,0x240000000d200000e44,0x80000000000000783b38,0x1b80000592b6475efc59,0x1ab1848586000018,0x8500000241ba15358567,0x3813860,0xc755a10f6000020592,0x5156049d4d89e049000,0x748bffc00a9941800001,0x13800000809c601c422c,0x5b0eda9122013a223b74,0xe0fe701e4292be037,0x800000000588488edd80],#[0x23880c66091000008052,0xe38218459c3301845f09,0xa6e0b6c0bd8818c20853,0x1a1c0578852560eb0a4,0x4a8195e146285dbe71e2,0x832e0359c32fa8387f0f,0x1401df84abee2990b01e,0xad61635828a0f46512e,0x784c28ee2381b5015880,0x465a60e000060d19003b,0xc0b0f85b1ce0de81d0e0,0x51a0d9800e1f1412057e,0x540000062959a069b13,0xec8c1c818341a4d8c284,0xb2f4848748e612d9bc89,0xb80cfd3324c166b02b60,0x60400ec201dae08da857,0x5bb7b48af3802580db00,0xcec10f1a0861843ec04f,0x48fa885584147993b980,0x83c2c0c01d562255012b,0x205f1802e0000120,0x75862be4f240b56a18c8,0x6c2104e5a53f08217c09,0xd003f00000c0d6800002,0x3db4933b85e1e841d004,0x533d2e02f08417a8c4e8,0x82522ba086baa4a96136,0x409bd83574034a13b160,0xb8c13e40606405de3b6a,0x901164b2f037224bb420,0x57029e04da504d600007],#[0x5380001286cd8575a10,0xb22df00000a051000002,0x27c000d1a2c6e1929039,0x48b44087ae8228409d70,0xd352611c4d2f044d680b,0xe067680fa000018135e0,0x300000000002077d84b1,0x645e062d85cd0350823,0x6fad19a2d28000180a30,0x8380000047e00001624,0x8931cb8026801d2a4552,0x18f861c0000000001a20,0x8000000005890c28f240,0x8181680e000008026,0xeedc00354a985493ae00,0x604de000058474,0xa09200000c0f9800,0xf80000e0328936a00000,0x10c0000104b890391009,0x80000000000000000016,0x2c3e018e816a00005806,0x1836e409e50bb082bfc1,0x9f785f4000000001c245,0x38ad7c98200000c8,0xdf6416f80316412c92b0,0x82a40000484b7a86a00a,0xb0584a4edb83700054c,0xb7008468850b82eb693,0xf4108d00e2e8e6c81640,0x85e0000220cd2ad15030,0xa01488b2260aec000048,0x96e012f6a111932ae064],#[0x4835a3513c0f6000c320,0x36000041411470b00001,0x1b0c048183460b4f483,0xa2130b20a8a815c00005,0x7b36800003834e02b,0x3e648a04cd68d7d04760,0xaf60000000008513a89e,0xc13454423484e262b639,0x54482be00a6424e1a06a,0x82b81a8e2000000001a1,0xd7e8af88549452a6813b,0xb4dfe50108128294bb00,0x218db,0x400000000000685fa000,0x28142c82b4e13c3886ce,0x86fc853200000814,0x1e061e860180ef00,0xc860,0xe05b00001c0bf79aec00,0x132b1708060000000566,0x632f1a1940a11e81,0x81538000000000,0x4ecd4555c12b00000000,0x2e330b85ad0872b0856e,0x20fc703682066ea0d,0xd8133e2c100001897600,0x111ee208b80000a100,0x684a742169018800,0x1800e80000000068178,0x683a00000000,0x70000000000000000000,0xb700a0088ba9d86461],#[0x18245b2dee00001aad98,0x17a442280001209ee00f,0xf940aa29c32530aa3958,0xcc0846c000001c1ee154,0xc0b7eba0a00000000020,0x6e60143443b018bb8437,0x42d1aa4c4513,0x900000007280000411c8,0x40364842a00000052,0x68852012d84d01a1b00,0x569d07a494a600000000,0x64cbf858ba1245a,0x48ad5013ef00c842b7,0x5930c00002839e00,0xcc000000000000038150,0xc0b6000000000782,0xd8000000001040fa8670,0x29f84b260727b8a1014,0x82d45485f9243ed84cba,0x2c1a449710136051a843,0x38561aec9601a5c41aea,0x1c0175303e200640000,0x292600001003a0000101,0xf400002b501c107e8500,0x81c6615c62848c0b8c9a,0xfe8627e163d056ea0167,0x89e505a4a410000014b7,0x69aee6017800010,0x3cf40811018c00000000,0xd041c09293032a000028,0x6ce8d3e0a3b800002039,0x1288284d81e1],#[0x2042b21e70e3000000,0x14e60000503fc0000000,0x1c0abc033d614b3,0x8ccb8b680f91043c000,0x924b679420000058033e,0x49482eaa2c80000582c,0xa4520000505a1e13f58,0x5834520732a2ccceed,0x80020000000000000000,0x48629cd0d9c000000001,0x800d0134bb2000000604,0x3b3b854140800016e2a6,0x2352518000078859a17,0xa82b6e00048099100dda,0x1c0e7000000000782a,0x68ae200007a1a2000000,0xbe5b8b3a0f1a38ac0000,0x2eeb784270869a83e360,0x7a167c04108135380af,0x82466214101312238d85,0x4e826980a0a063d2d46f,0xfee8d9a6535b01bb60e,0x20003ba18cc4ba2138d6,0x2f28e2fd847c01437041,0x14070e44cce1060b,0x1e0a5095940000,0x504f548fb600da00,0xa800002c4d0000000000,0x61e0750000000000482,0x9a803deedbe81f2018f9,0x11968875207d80000c05,0x30b47d026de0a7005808],#[0x9da80781022aa416712d,0x82caa022c823de02c02,0xea438a40000000000000,0xe04ff2c29e1930000020,0x5c8ab6a203aa507884f6,0x1089d0f1602fbaef2112,0x580483808700000670cb,0xa42009cc4edc80001609,0xec16ab088f0130705a20,0x30cc0fb783258058e03b,0x800000000523cc612960,0x3100000000070ad2e4bb,0xc212d807800003032da8,0xda610be44cea0c280000,0x85a9409a800000000392,0x1206112004c2a0c,0x18de2000000000000,0x2000000001e0f1000000,0x817a0000000007810,0x104b400,0xe23b5a0060000,0xe330000000,0x8a813198c2e840b80000,0x207e000000001b2d0b13,0x423cee9378,0x4ca0000100d4aa1e4000,0xec111b042b44fdb85e78,0x55522218000000007024,0xd8396293f2043aeeebd0,0x36800004080b04cfce2a,0x813cc83a70148c83c0c1,0x66000000001893880001],#[0x60ab20a2000002a0,0xab037e00000054600000,0x864b1860000000000c92,0x812ed05ae80c7000004,0x1e025b8da4ca128000,0x0,0x11204b960d71109da87b,0x21407a2272851ce0,0x10b0680000e14a00000,0x82b201849844ba14e800,0x10c600003807a40001,0x783d5e4d721052000,0x2416e000000000000000,0x1c2d31008ec03e0b40,0x3909164ff40dd52a2180,0x6600000000042d744132,0xe10d080dec35002a1861,0x4560bfe4d7e80c6681cf,0x9343e0a123b80e4f9845,0xaf82c0c6c1f05c800000,0xee2b01ed24aed904c011,0xc00002807c000000001a,0xafd6c22b2425e47d202b,0x1617c41086a0ba60,0x537844f0090121a408e7,0x7037c00006886505,0x8000000000000000000,0x15168f0094e0c4c85,0xc0000109342351ce03d0,0x5c04ce22200000e05,0xe0029000002841500a80,0x454434f000000000085e],#[0xe4f540,0x78204246d281a5e60000,0xcdad05d5013103b7d08,0x12008c00000aa39d93c6,0xb8b0005a40421050c514,0x18866800002150a,0x88800006276c8088000,0x1c8eea9b4ae0f48a5654,0x1a800000000000000000,0x5b202000059547401b38,0xa0b8000000000,0x1800200,0x50b53a08980000,0x16010884,0x70000165322053e00000,0x569f805ba125c0aeaa13,0x25115cb2e4616e82972,0x49b416fc841a40065807,0xe052aa1714a4d7217488,0x10544201fd05bbe0a4,0x39063a2188000000,0x16e97d9906800f73a5a8,0x85318001c83000000003,0xc61032402d584bf4082f,0x3f80000000058159c0a,0xc0e5222ca00004045ba,0xa03e0ca40b58088c8000,0x80001a16d00001e4f4c2,0xe8800006eca4a1d4a172,0xec99902ac15e4064600,0x522ee3b38bd2128c2500,0x84af0187000000000500],#[0xec001f40de0000000004,0x2793089a000000001a08,0x7e17b312ce211080000e,0x314000052a71e17c801e,0x181f0000071026a06628,0x855600b11838fa4f1,0x287130635c10a6a50200,0xed618a00000000010860,0xa2b7c02ad0239a564a04,0x51093217da809d012d5,0x559a492000008304000,0xa160b063b41703a03ee,0x55bc08d600ce80f80000,0x20c7c954888b0e8,0x700001c1747047e8941,0x8124b0625e428c0c2b2b,0x804d889dd4020b034b,0x940c00003299f6213800,0xd80000c4b1ea56680c98,0x871b12fc40d02804a209,0xcc12149b0a0000002b88,0x1c1170000124182a4a,0xca49c000000000000000,0x7e800010041800ee0565,0x58086a2beb004780,0x6ec159684a980ee90538,0x93bc00004940300b9780,0x305340000500382171d,0xb45f0154205cf8080000,0x2000000001c09300001c,0x1e730804ea2b250802,0x8854e1709134e001580],#[0x103809fc148000000000,0x7ae00d40000683b920,0xd20000711f04028805eb,0x862d616dc203c26bae01,0xcd0224007f483c8a4f96,0xef7201f4e0fda05116c0,0x80000220c3c71c001e8c,0x1c70dabb2ae0b1c8af,0x31bd900fc80001648a80,0x58499d139000000000,0x614b8000042170048800,0x162192000010d4610cc7,0x823e6188da90c007ff23,0x23036617f80001c9334,0xaea061400001131a000,0xe270f501ae600480000e,0xbd6c15a302a000006a9f,0x1cecb00001200423,0x783760000602f00000,0xe0640000000001002000,0xdfca456048e000000001,0x322c13ff239e20530c4,0x9000000000785fd641c8,0x615f0b542503f047ac93,0x19320cb1a000000,0x641ede1530000,0x6ba8400000a097a0de80,0x2f3217ec18410382a729,0xc0303840a00003a04c61,0x1e37c5029aa115e0603,0x8e40000000000000000,0x1702d0c9484828600005],#[0x50309261b80001211,0xde07580001c2bd800000,0x1c0950000160d0e053,0x224c8000050b66000000,0x14d0e180000000000000,0x4b0050108000061309c1,0xcca0e6381f80048e0384,0x1a83410dee0000300,0xa1021000000000064c78,0x8ae2002901027048bc4a,0x4007b80001a092a94f9c,0xd6da0213a2c580367906,0xa811bcd336934ce11472,0xbc7046160ebbb3fde0ed,0xe949000000000302f464,0x106ec00000000019049,0x82906098502ecc4ea000,0xb80001e8d69801d400fe,0x247fa20f440ff85a7671,0x188d8000000190e9ae9e,0x1649830000000005a03,0x848c000000000000038,0x3d800000000000000000,0x221f641034052620,0xf200001060ac17580000,0x84320000000012006c11,0xb0811e000000000002ca,0x84d0000000002888ac08,0xa00000000000000a0d46,0xe0f280000000079c4,0x283340000320cf806880,0x79451a30a0825ff138],#[0xca3a000004286780c400,0xb4000008c2caa10381d8,0x37e118f2dc2c16f583,0x60117a0848000000004,0xa8fb2b41816220380000,0x2c127a12fa002600001a,0xdc663726835e411c1944,0x883a5e0407245ac84398,0xc0ecc7be405a13d920ff,0x1e0583821e64,0xd240e3501be22f480000,0x13a7a0e20000080d8d3a,0x4800016039194372099f,0x4deb0e22c16412394287,0x8000040cc52828a1103a,0xe80a38603d6a15d8996,0x3143c000030620c0a389,0x7f183cc0000000000000,0xc370b83de4922800014a,0xea247d8000146c399364,0xe1104262010e0000280,0xd80af480834155a4affe,0x84ba8000080b,0x3801500000c0c8000000,0x3fa2c7f484ee80199857,0x302000000001218381,0x47000018383800000000,0x18250479b0e98000080,0x1012800001880a80617,0x85e3c41e0000040fa800,0xa06f0000000b51,0x144a1d7d816700000000],#[0x6000000000000000000e,0x18b42c78855da0c19851,0x38c1b300fa04d1692e3a,0x4aa050e000000001c179,0x209c80001815b0000024,0x6a000000000000000000,0x81c00000000000000288,0x6e03c200000000188326,0x680d0000028480028,0xb82bb80001e4117854a0,0xc9f60a239d4600006836,0x98b48c0d8000008873e8,0x97881ac000000466837f,0x56600332205000001a4,0x5c6090f83d0e094a038b,0x10d20fbb01e30ce9b1b,0xd0000062d1d239780b3c,0x17750093210b4227f840,0x2e0cbd01b20000000006,0xa01a9c4a,0x78221e411c8867800500,0x2e185df805b8930560d4,0x17680724002c025800,0x683710000080a992538,0x640aedb282d3c045226,0x1a143f811a00000c36ba,0x410831b81103ac8ce08,0x160bbc0597a]]
def g219D9 := limbs80 #[#[0xd20fe107f843fa21fc10,0xa1fe50fea87f143fc41f,0x19508a379506c1e003fe,0x485103091054009f96db,0x814900091440c2040407,0x51030500930084451030,0x4900091440c108049120,0xc2052405009445103081,0x24002440c20450064440,0x10308100519110308115]]
def g219H9 := limbs80 #[#[0x2028141a00030001a00,0x3601070f804000003c5a,0xcbc05058105c0700008,0x900408000300800082c8,0x5020091200000441c200,0x26f06018200106000024,0x24d000084610178180,0x808e1301a640a020186,0x1d00dfc0aa2,0x50000745d1564137b000,0x29021107f00007139e06,0xd706ef0100000d011518,0xa069c05e6571605f804,0x43006b471c542413c000,0x6d00800530061f031506,0xa0000487d92470361302,0x194513032541ed254900,0xd926ad65e0000801ee25,0xb5012421138699109612,0xaf248001f81173556410,0x7e00cc03d525b3062c10,0x8737a200fb5700000208,0x9e009c001e016624fc07,0x1506b90460000c51f714,0x6713bf2100777375d408,0x9921410394029a05aa21,0xc4135755e00002030812,0xbc45c9020e04f1072f01,0xd2593410a404d06cf07,0x536000002018000,0x50000507900000000000,0x7117df02e00002023501],#[0xc0000835921080000c42,0x8b4392037c1488579426,0xb3003f063e076b11f521,0x757762084b187b249000,0x1071255fc212200,0xaa07db24ea2401035000,0xed783106d003b207c003,0xd5126679c01b1752303,0x9e085d4644052f751812,0xb7000b0059024903c973,0x3f019713f324ac441605,0xa802f00002219300df48,0x974d126382457013a25,0xdb4528244875c0000f47,0xb6741713ee9610000f05,0x59028c17c9250b429e74,0xb1027a05470360000240,0x50000702c6665024b997,0x774773180a51ab678902,0x63444c17f012a9411601,0xac181006ae1386186d24,0x9033b874f167a12fc42,0x50492112e0021440675,0x3c02aa04e0047a467000,0x507590459275c02df21,0x4a27d6262c0140038406,0xe0450907450413960d04,0xf0000774cf080307a717,0xb067404083475022374,0x504ae6710000305,0xed086b184d2150000000,0x8b664404bd1831469d74],#[0xdb07e9466385af116a04,0x4000060684166d578626,0xa0000e05ce1363073a03,0xe97a620db5650000701,0x6e2744051200ee468b74,0x27445d04c65430000c47,0xa85556082e004e85b204,0xf68753670a1370000913,0xc0000d0582217d06fd03,0x570700000d44f0000a11,0x500003059742cb26b105,0x5a056e077b0436113711,0x2711af02b00665241846,0xd765f7185d0573253425,0x7083601]]
def g219D10 (j : Nat) := if j=0 then 0x3f else 0
def g219H10 := limbs80 #[#[0x6c4c68c014e002b00100,0x191c001e140030c409,0xc8001223cd2549dc108c,0x494fccdd1b8909540009,0x84d526619026a4a08840,0x56097c0f608000002002,0x4920000c1c845d0be1cc,0x18a181b9a21a541,0x24d6c4800349999c840,0x8000942e540035940000,0x38c3822951852d4559,0xca224000002010000514,0xb5d45880000025c40004,0x9e8a480]]
def g219L : Nat → Packing
  | 4 => (2,6,5,0,0,3,0,g219D4)
  | 5 => (194,5,5,0,0,11,0,g219D5)
  | 6 => (1106,4,5,0,0,14,0,g219D6)
  | 7 => (807,3,5,0,0,15,0,g219D7)
  | 8 => (136,2,5,0,0,13,0,g219D8)
  | 9 => (10,1,5,0,0,9,0,g219D9)
  | 10 => (1,0,5,0,0,0,0,g219D10)
  | _ => emptyPacking
def g219I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 5 1 0 g219H5
  | 6 => lookupWord 84 499 6 16 8 4 g219H6
  | 7 => lookupWord 480 2371 9 19 11 4 g219H7
  | 8 => lookupWord 361 1973 7 18 10 4 g219H8
  | 9 => lookupWord 76 349 9 16 8 4 g219H9
  | 10 => lookupWord 15 83 6 12 4 4 g219H10
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
theorem g219P5_0 : block g219 5 0 96=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P5_96 : block g219 5 96 96=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P5_192 : block g219 5 192 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g219B5 : block g219 5 0 194=true := (@block_merge g219 5 0 96 98 g219P5_0 (@block_merge g219 5 96 96 2 g219P5_96 g219P5_192))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P6_0 : block g219 6 0 2=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P6_2 : block g219 6 2 52=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P6_54 : block g219 6 54 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P6_150 : block g219 6 150 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P6_246 : block g219 6 246 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P6_342 : block g219 6 342 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P6_438 : block g219 6 438 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P6_534 : block g219 6 534 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P6_630 : block g219 6 630 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P6_726 : block g219 6 726 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P6_822 : block g219 6 822 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P6_918 : block g219 6 918 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P6_1014 : block g219 6 1014 92=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g219B6 : block g219 6 0 1106=true := (@block_merge g219 6 0 438 668 (@block_merge g219 6 0 150 288 (@block_merge g219 6 0 2 148 g219P6_0 (@block_merge g219 6 2 52 96 g219P6_2 g219P6_54)) (@block_merge g219 6 150 96 192 g219P6_150 (@block_merge g219 6 246 96 96 g219P6_246 g219P6_342))) (@block_merge g219 6 438 288 380 (@block_merge g219 6 438 96 192 g219P6_438 (@block_merge g219 6 534 96 96 g219P6_534 g219P6_630)) (@block_merge g219 6 726 192 188 (@block_merge g219 6 726 96 96 g219P6_726 g219P6_822) (@block_merge g219 6 918 96 92 g219P6_918 g219P6_1014))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P7_0 : block g219 7 0 7=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P7_7 : block g219 7 7 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P7_103 : block g219 7 103 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P7_199 : block g219 7 199 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P7_295 : block g219 7 295 45=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P7_340 : block g219 7 340 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P7_436 : block g219 7 436 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P7_532 : block g219 7 532 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P7_628 : block g219 7 628 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P7_724 : block g219 7 724 83=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g219B7 : block g219 7 0 807=true := (@block_merge g219 7 0 340 467 (@block_merge g219 7 0 103 237 (@block_merge g219 7 0 7 96 g219P7_0 g219P7_7) (@block_merge g219 7 103 96 141 g219P7_103 (@block_merge g219 7 199 96 45 g219P7_199 g219P7_295))) (@block_merge g219 7 340 192 275 (@block_merge g219 7 340 96 96 g219P7_340 g219P7_436) (@block_merge g219 7 532 96 179 g219P7_532 (@block_merge g219 7 628 96 83 g219P7_628 g219P7_724))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P8_0 : block g219 8 0 13=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P8_13 : block g219 8 13 51=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P8_64 : block g219 8 64 72=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g219B8 : block g219 8 0 136=true := (@block_merge g219 8 0 13 123 g219P8_0 (@block_merge g219 8 13 51 72 g219P8_13 g219P8_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P9_0 : block g219 9 0 10=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g219B9 : block g219 9 0 10=true := g219P9_0
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
theorem g219G : graphValid g219 (boundsBefore K215) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low219 : Lower true (varsX 219) (graphGoal 219) 11 := lower_forest (g:=g219) (i:=0) (hints:=16777283) (before_sound K215 V215) g219G g219T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K219 := extendKnown K215 11 [(219,[]),(237,[33,84])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V219 : Known true K219 := extend_ok (m:=219) V215 low219 (by decide +kernel)
def g127Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfffe74328e94e9560e,0x314ec000000000fc0fff])),(BitVec.ofNat 152 (word80 [0x2824320e14684600,0x10068011451451451451]))),((BitVec.ofNat 152 (word80 [0x125db443a1f0164,0x943221c003f03f03f000])),(BitVec.ofNat 152 (word80 [0xcc21134438190124,0x142221030c30c30c30c3]))),((BitVec.ofNat 152 (word80 [0xea117fd972a535,0x60800c80fc0fc0000000])),(BitVec.ofNat 152 (word80 [0x57068117e99520534,0x20800c871c71c71c71c7]))),((BitVec.ofNat 152 (word80 [0xfffe4b8cd8bb01caa4,0x1b295abf00000000003f])),(BitVec.ofNat 152 (word80 [0x29804b88d0ab0180a4,0xb29488e38e38e38e38e]))),((BitVec.ofNat 152 (word80 [0x10b6b18bc6a908,0xecf540c000000003ffc0])),(BitVec.ofNat 152 (word80 [0x4e001084b18386a808,0xe8d140ecb2cb2cb2cb2c]))),((BitVec.ofNat 152 (word80 [0x22c951648cbcdb,0x980f840000ffffc0000])),(BitVec.ofNat 152 (word80 [0x700002c8014084b8cb,0x9005068a28a28a28a28]))),((BitVec.ofNat 152 (word80 [0x19d242605342aeb,0xca03173ffff000000000])),(BitVec.ofNat 152 (word80 [0x800194240004242a4b,0xc0001230c30c30c30c30]))),(0x0,0x0),(0x0,0x0)]
def g127C : List ColumnInfo := [(2,0,125,0,8),(4,0,123,0,8),(16,0,111,0,8),(32,0,95,0,8),(1,0,126,0,7),(8,0,119,0,7),(64,0,63,0,7),(1,8,54,64,5),(9,0,118,0,5),(64,8,54,1,5),(65,0,54,0,4)]
def g127A : List (List Nat) := [[],[96,81,66]]
def g127D7 (j : Nat) := if j=0 then 0x6780577dcd60 else 0
def g127D8 := limbs80 #[#[0x99c1091340ff583fd30,0x28e54c65099]]
def g127H8 (j : Nat) := if j=0 then 0x40 else 0
def g127D9 (j : Nat) := if j=0 then 0xca842603ff else 0
def g127H9 := limbs80 #[#[0xe40000000680,0x1]]
def g127L : Nat → Packing
  | 7 => (1,2,4,0,0,0,0,g127D7)
  | 8 => (2,1,4,0,0,5,0,g127D8)
  | 9 => (1,0,4,0,0,0,0,g127D9)
  | _ => emptyPacking
def g127I : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 1 2 0 4 0 0 g127H8
  | 9 => lookupWord 1 17 0 6 1 1 g127H9
  | _ => fun _ => none
def g127 : Forest := ⟨127,9,fun i => g127Y[i]?.getD (0,0),g127C,g127A,g127L,g127I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_0 : block g127 7 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B7 : block g127 7 0 1=true := g127P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_0 : block g127 8 0 2=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B8 : block g127 8 0 2=true := g127P8_0
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
  · exact g127B7
  · exact g127B8
  · exact g127B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127G : graphValid g127 (boundsBefore K219) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low127 : Lower true (varsX 127) (graphGoal 127) 10 := lower_forest (g:=g127) (i:=0) (hints:=16778563) (before_sound K219 V219) g127G g127T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K127 := extendKnown K219 10 [(127,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V127 : Known true K127 := extend_ok (m:=127) V219 low127 (by decide +kernel)
def g191Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffffff99a0b4a704b5,0xc406d0000007c00f83ff])),(BitVec.ofNat 152 (word80 [0xa400a0920a4050081,0xc0065084210842108421]))),((BitVec.ofNat 152 (word80 [0xffe0006a6a0701f8c0,0xde1ca00000f801f07c00])),(BitVec.ofNat 152 (word80 [0x4c80336a6a0601a0c0,0xdc04818c6318c6318c63]))),((BitVec.ofNat 152 (word80 [0x3b47c74f03ea,0x2089c0001f003e000000])),(BitVec.ofNat 152 (word80 [0x6f015c3b43c70f02e2,0x2089c39ce739ce739ce7]))),((BitVec.ofNat 152 (word80 [0xffffff944b5edee81f,0x8508a003e0000000001f])),(BitVec.ofNat 152 (word80 [0x700a60144b5adae81e,0x508a739ce739ce739ce]))),((BitVec.ofNat 152 (word80 [0x41af92a4ff8,0x4a39007c000000007fe0])),(BitVec.ofNat 152 (word80 [0x8013800410592a4f38,0x23906318c6318c6318c]))),((BitVec.ofNat 152 (word80 [0xb950ac8d518,0x31572f8000003fff8000])),(BitVec.ofNat 152 (word80 [0x1c00009408c05518,0x1502421084210842108]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x647048112202,0x1e05fffffffc0000000])),0x842108421084210),(0x0,0x0)]
def g191C : List ColumnInfo := [(1,0,190,0,9),(32,0,159,0,9),(4,0,187,0,8),(8,0,183,0,8),(10,0,181,0,7),(18,0,173,0,7),(20,0,171,0,7),(128,0,63,0,7),(0,4,27,160,6),(0,8,54,129,6),(6,0,185,0,6),(12,0,179,0,6),(128,4,27,32,5),(130,0,61,0,5),(132,0,59,0,5)]
def g191A : List (List Nat) := [[],[80,65,50]]
def g191D7 := limbs80 #[#[0xbe581d8921be78158921,0xe097888084704bc45a40,0x8]]
def g191D8 := limbs80 #[#[0xd62487fab0a43f958521,0xb2437f5d921fdec490fe,0x61bfee4b0fee76487f6b,0x5fd764cbf6b12657f5cb,0xeb8ec57fdcd62bfee2b1,0xc961ffac4b0dfd73d8af,0x781382a003feb1ac5ff5,0xc26616e529203d8cc288,0xc451a889c2588d20a799,0x65306c05c4c28530a130,0x12069309715ca187930c,0x5c62a4c3194c18a93097,0x45912c08c651a42b0971,0x81871b0c643061e4c319,0x505530c553852e6c3190,0x941625305713469b1c09,0x210e30a0d230e0c7c709,0x24332]]
def g191H8 (j : Nat) := if j=0 then 0xa7c00 else 0
def g191D9 := limbs80 #[#[0x61ff587fd21fbc87ed21,0x4800ffd8bfd62ff4cbff,0x9089468337572953610c,0x88902c54390518145128,0x22422728cd3c89089473,0x5c83d21130e73123058c,0x14844e61]]
def g191H9 := limbs80 #[#[0x9a4008204b901,0x4a000000000000000000,0x4603c400039040400003,0x900000e10000030d001,0x138000000000000001,0x83000052440000000000,0x8200000a1e8c002]]
def g191D10 (j : Nat) := if j=0 then 0xac8202ff else 0
def g191H10 := limbs80 #[#[0xdc000000e200000000,0x7800000000,0x0,0xcf000000a600000000,0x0,0x0,0xa40000000000006a00,0x900f5000000000000,0x670000,0x0,0xd3200041db00,0x3e00]]
def g191L : Nat → Packing
  | 7 => (2,3,4,0,0,6,0,g191D7)
  | 8 => (18,2,4,0,0,10,0,g191D8)
  | 9 => (8,1,4,0,0,9,0,g191D9)
  | 10 => (1,0,4,0,0,0,0,g191D10)
  | _ => emptyPacking
def g191I : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 1 5 0 5 1 0 g191H8
  | 9 => lookupWord 4 53 3 10 5 1 g191H9
  | 10 => lookupWord 3 127 0 8 3 1 g191H10
  | _ => fun _ => none
def g191 : Forest := ⟨191,10,fun i => g191Y[i]?.getD (0,0),g191C,g191A,g191L,g191I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P7_0 : block g191 7 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g191B7 : block g191 7 0 2=true := g191P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P8_0 : block g191 8 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P8_1 : block g191 8 1 14=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P8_15 : block g191 8 15 3=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g191B8 : block g191 8 0 18=true := (@block_merge g191 8 0 1 17 g191P8_0 (@block_merge g191 8 1 14 3 g191P8_1 g191P8_15))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P9_0 : block g191 9 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P9_2 : block g191 9 2 6=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g191B9 : block g191 9 0 8=true := (@block_merge g191 9 0 2 6 g191P9_0 g191P9_2)
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
  · exact g191B7
  · exact g191B8
  · exact g191B9
  · exact g191B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191G : graphValid g191 (boundsBefore K127) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low191 : Lower true (varsX 191) (graphGoal 191) 11 := lower_forest (g:=g191) (i:=0) (hints:=1347) (before_sound K127 V127) g191G g191T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K191 := extendKnown K127 11 [(191,[]),(254,[16,32,48,64,80,96])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V191 : Known true K191 := extend_ok (m:=191) V127 low191 (by decide +kernel)
def g223Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfffc8b4b42714a5d45,0xf00000003f000000fff])),(BitVec.ofNat 152 (word80 [0x80500b4a4051481d04,0x7249249249249249249]))),((BitVec.ofNat 152 (word80 [0xc00356b060138c0de6,0xb8000000fc0000fff000])),(BitVec.ofNat 152 (word80 [0x19b12b060120c0dc6,0x280c30c30c30c30c30c3]))),((BitVec.ofNat 152 (word80 [0x1d86c74701fa20e,0xcc00003f00003f000000])),(BitVec.ofNat 152 (word80 [0xae1d06c74701ea00e,0xcc1c71c71c71c71c71c7]))),((BitVec.ofNat 152 (word80 [0xfffca0b17dee80f842,0x8a000fc0000fc000003f])),(BitVec.ofNat 152 (word80 [0x1300a0b13d2680e042,0x88186186186186186186]))),((BitVec.ofNat 152 (word80 [0x60af92a4ff84a1,0x9003f00000000003ffc0])),(BitVec.ofNat 152 (word80 [0x1c00600592a4b38021,0x90514514514514514514]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1d50ac8d518315,0x72fc0000000ffffc0000])),(BitVec.ofNat 152 (word80 [0x20000d008089410211,0x12618618618618618618]))),((BitVec.ofNat 152 (word80 [0x32304911220201a,0x5fffffffff000000000])),0x820820820820820820),(0x0,0x0)]
def g223C : List ColumnInfo := [(4,0,219,0,11)]
def g223A : List (List Nat) := [[],[64,49]]
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
theorem low223 : Lower true (varsX 223) (graphGoal 223) 12 := lower_forest (g:=g223) (i:=0) (hints:=16778819) (before_sound K191 V191) g223G g223T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K223 := extendKnown K191 12 [(223,[]),(253,[32,49,64,81,96])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V223 : Known true K223 := extend_ok (m:=223) V191 low223 (by decide +kernel)
def g239Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfff2ca868b0a6ba075,0x40000000fc0000000fff])),(BitVec.ofNat 152 (word80 [0x8142ca84810a69a014,0x49249249249249249249]))),((BitVec.ofNat 152 (word80 [0xc00ff520c415442457,0x4000003f00003f03f000])),(BitVec.ofNat 152 (word80 [0x66ff120c404402447,0x430c30c30c30c30c30c3]))),((BitVec.ofNat 152 (word80 [0x13ad0e5c0700ee4,0xc0000fc0000fc0fc0000])),(BitVec.ofNat 152 (word80 [0xb813290e5c0600664,0xc30c30c30c30c30c30c3]))),((BitVec.ofNat 152 (word80 [0xfff94163f1a382d461,0x8003f00003f00000003f])),(BitVec.ofNat 152 (word80 [0xc0901637081824461,0x86186186186186186186]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x215f0a957c7488,0xfc0000000000ffffc0])),(BitVec.ofNat 152 (word80 [0x1000004b0a11145088,0x14514514514514514514]))),((BitVec.ofNat 152 (word80 [0x49ca952220d1b94,0xbf00000003ffff000000])),(BitVec.ofNat 152 (word80 [0x20000c0802220d1990,0x18618618618618618618]))),((BitVec.ofNat 152 (word80 [0xb0208244881410a,0x7ffffffffc0000000000])),0x20820820820820820820),(0x0,0x0)]
def g239C : List ColumnInfo := [(2,0,237,0,11)]
def g239A : List (List Nat) := [[],[33],[48,101],[48,33,101]]
def g239D11 (j : Nat) := if j=0 then 0xff else 0
def g239L : Nat → Packing
  | 11 => (1,0,1,0,0,0,0,g239D11)
  | _ => emptyPacking
def g239I (_ _ : Nat) : Option (Nat × Nat) := none
def g239 : Forest := ⟨239,11,fun i => g239Y[i]?.getD (0,0),g239C,g239A,g239L,g239I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239P11_0 : block g239 11 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g239B11 : block g239 11 0 1=true := g239P11_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239T : checkedTables g239 11 := by
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
  · exact (rfl : block g239 10 0 0 = true)
  · exact g239B11
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239G : graphValid g239 (boundsBefore K223) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low239 : Lower true (varsX 239) (graphGoal 239) 12 := lower_forest (g:=g239) (i:=0) (hints:=16778579) (before_sound K223 V223) g239G g239T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K239 := extendKnown K223 12 [(239,[]),(251,[48,65,82,96,33,16])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V239 : Known true K239 := extend_ok (m:=239) V223 low239 (by decide +kernel)
def g247Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xe003ff945c06c9ead6,0x5a2000000f800007c1f])),(BitVec.ofNat 152 (word80 [0x40580a145c02c86286,0x1a25294a5294a5294a5]))),((BitVec.ofNat 152 (word80 [0xfffc0036a8b87c1081,0x2ba00001f003e0f83e0])),(BitVec.ofNat 152 (word80 [0x809013368810680081,0x2321084210842108421]))),((BitVec.ofNat 152 (word80 [0x41df34620320,0xf3260003e007c1f00000])),(BitVec.ofNat 152 (word80 [0xe01c409f34620300,0x1322318c6318c6318c63]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffca036ccd1c14,0xaf0c007c0000000003ff])),(BitVec.ofNat 152 (word80 [0xa014048036c051c10,0xac0ca5294a5294a5294a]))),((BitVec.ofNat 152 (word80 [0x90adb14abe9,0xa4000f80000001fffc00])),(BitVec.ofNat 152 (word80 [0x1302600900c9148868,0xa4008421084210842108]))),((BitVec.ofNat 152 (word80 [0x24e54a91106a,0xdce5f0000007fe000000])),(BitVec.ofNat 152 (word80 [0x1c038000604a91106a,0xccc4c6318c6318c6318c]))),((BitVec.ofNat 152 (word80 [0x58104122440a,0x853fffffff800000000])),0x10842108421084210),(0x0,0x0)]
def g247C : List ColumnInfo := [(2,0,245,0,10)]
def g247A : List (List Nat) := [[],[32,100],[64,81,98],[96,81,66]]
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
theorem low247 : Lower true (varsX 247) (graphGoal 247) 11 := lower_forest (g:=g247) (i:=0) (hints:=16778564) (before_sound K239 V239) g247G g247T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K247 := extendKnown K239 11 [(247,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V247 : Known true K247 := extend_ok (m:=247) V239 low247 (by decide +kernel)
def g255Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x22000000000fc0000,0x7f01fffc03f3c1c1])),(BitVec.ofNat 152 (word80 [0x20451451451448912,0x24489122448c01638001]))),((BitVec.ofNat 152 (word80 [0x28300000003f00000f,0xe03f80fe00000c01e61d])),(BitVec.ofNat 152 (word80 [0x2020c30c30c30c1830,0x60c183060c180400e215]))),((BitVec.ofNat 152 (word80 [0x751000000fc00007f0,0x1fc0000000001002182d])),(BitVec.ofNat 152 (word80 [0x7011c71c71c71c3870,0xe1c3870e1c380000002d]))),((BitVec.ofNat 152 (word80 [0x24700003f00003f800,0x3f8603c16e3])),(BitVec.ofNat 152 (word80 [0x24738e38e38e3870e1,0xc3870e1c3870200816a0]))),((BitVec.ofNat 152 (word80 [0x8dd000fc0000000000,0xfffc0080c0072e])),(BitVec.ofNat 152 (word80 [0x8ddb2cb2cb2cb162c5,0x8b162c58b1600080052a]))),((BitVec.ofNat 152 (word80 [0x1f403f000000000000,0x1fffff00000101001832])),(BitVec.ofNat 152 (word80 [0xd4a28a28a28a14285,0xa142850a14000001802]))),((BitVec.ofNat 152 (word80 [0x208fc000000003ffff,0xe0000000000601ffe002])),(BitVec.ofNat 152 (word80 [0x8c30c30c30c18306,0xc183060c18401e30002]))),((BitVec.ofNat 152 (word80 [0xc0cffffffffffc0000,0x7fe000000])),(BitVec.ofNat 152 (word80 [0x20408,0x102040810203da000000]))),(0x0,0x0)]
def g255C : List ColumnInfo := [(2,0,253,0,12),(4,0,251,0,12),(16,0,239,0,12),(32,0,223,0,12),(1,0,254,0,11),(8,0,247,0,11),(64,0,191,0,11),(128,0,127,0,10),(65,0,190,0,9),(9,0,246,0,8),(72,0,183,0,8),(0,8,54,193,7),(73,0,182,0,7),(129,0,126,0,7),(136,0,119,0,7),(192,0,63,0,7),(1,8,54,192,6),(64,8,54,129,6),(128,8,54,65,6),(65,8,54,128,5),(129,8,54,64,5),(137,0,118,0,5),(192,8,54,1,5),(193,0,54,0,4),(193,8,54,0,4)]
def g255A : List (List Nat) := [[],[96,81,66]]
def g255D8 := limbs80 #[#[0xe09874dbb665d7358130,0x65cd704c3c6cc32ecb9a,0x2edc9ae6b82c1d36e597,0xf8be1f8c7e4a24c00e9b,0x2f87e389c803c08d17e0,0xe1033e3180a02408f83e,0xbe3f83e1620703fe0f8b,0x380af8]]
def g255D9 := limbs80 #[#[0x7358130f365d97358130,0xe76619735c130d7665d,0x9735c130e76e19735c13,0x30b76683765cd30d76e5,0xd973581308f7e8d985d9,0x130fb66997358130fb65,0x61d7658130df665d7358,0x8130ef6e8d8758130ebe,0x6e8d9758130ebee99875,0x5c130dbee999758130df,0xf6619735c130f765d973,0x35c130ef6e19735c130e,0xf76659735c130df6e597,0x735c130f76e59735c130,0xf76e99735c130f76699,0x9765c130df665b935c13,0x30dbee59765c130ebe61,0xdb905cd30bf6e8d965c1,0xd30bf669b905cd30f765,0xe59765cd30f76681765c,0xd930bf6e81965cd30f37,0x7e8d985d930abfe99875,0x5d930cfee81985d930af,0xf6e4f9061d30cf7e8d98,0x61d30ef6e4f9061d30d,0xafee819661d30afe69b9,0x735c160af7e8d9661d30,0xf3e5d9735c160df6e4d,0x9735c160f76e4d735c16,0x60f3e699735c160f3ee5,0x99935c160dbee59935c1,0x160dbe5db935c160bbee],#[0x659905cd60bbe68f965c,0xcd60af7e8d875cd60dbe,0x7e8d875cd60e7ee81875,0x61d60ef624f9061d60e7,0xfe68f9061d60ef6e4f90,0x361d60ebee5b9061d60a,0xafee819361d60af7aa49,0x905cd70ef6e839361d60,0xe775db835cd709fe69b,0x1765cd70af769b835cd7,0x70f76e0f905cd70b7ee8,0x1b835cd70b7e69b905cd,0xd70b7769b835cd70e776,0xe81965cd70b77e8d865c,0x19709fe68f905d970b7e,0x6e4f9061970df624f906,0x8a000df6e839361970df,0xf1869c2b210b05e82040,0x76e3721920b344da2280,0x2bc948899648f2208ff0,0xcef473e3739a64c725d9,0x34a2a40117686d4069ef,0x59590a9552ca8753b099,0xea649b0f17cab975a92c,0xa21c98dfe6dcb5ada4cc,0x4a8073f49ed2f2d76fb,0x475a32314c88cc352131,0xd3a19a54c1659327b912,0x3d5b2a4f4d9a4a50f67c,0x83060783bc5e0f0f8c18,0x1e3f0830607f8bc1e1f1,0x3783c5e3f0824803f8bc],#[0x13e2f078511e3201c0d7,0x13f8bc166f0f8c82549e,0xd8be2f0f8fc1881a14c4,0x96383c1de1f1783c60c1,0xf1a20a0578bc3e3f0220,0x9078361267a2f83c5e1,0x381a89e2f87c1e2f1c2,0xe0d04e9bc5e0f1f84224,0x81e12a6f1783c7e1088,0x78c283853c5e062f87c7,0x3e2f1830804717c3e2f0,0xf8e4e0c181c0f06f83c,0xc1e2f0f8c132727c5e0f,0xf0f83c5e306920e06b9b,0x7c1e2f1a20a0561212e6,0x2f1834a25c9c1e0da2f8,0x2ca2509c134573787c1e,0x792a8b8473783c5e1f19,0x9707a2f8bc1e3f0a2080,0x252228be0f178fc20d24,0x60fe0f17864fe3060d09,0xc708201f27f078bc3e30,0xf0038ac3a27c0c5f0f8b,0x8885c1688097378bc3e3,0x81dcc8a84f83c5e1f183,0x382c383d0be2f0f83c61,0xe16278c8f1783c7e1060,0x7854de31d130ab3783c5,0x5e1f078f103f13c5c5f0,0x1033c00bf0f8c66284bc,0x830505833c5e0f0f8c6f,0x5e00778c204783c5e1f1],#[0xf8bc1e3080c1104f87c,0x1366f078bc20bf18e0ef,0x44f12cde0f1787c60b21,0xa4e2b32f8bc7e1f06209,0xe06d97c5e1f1f8110483,0x97c5e3f0f801b88241e0,0xe1f1783c688068c10071,0xd22cbe2f0f8fc088080f,0x2078492bc288f078bc60,0xe3441009b2f8bc3e0f1a,0xc201a30281b65f1787c1,0x5e1f1f80564f87c1e2f1,0x7854be322128a23113c,0xc1e1f1860693f13c5c6f,0xf171bc1e3f0a94b07f8b,0x7c1e30b8c0d0a03e1016,0x8f1783c3e30b8d08f178,0x5211e272f83c7e10b110,0xf103823c5e1f078c3030,0xf186050b053c5e1f078,0x33c5e0f0f8d103f8bc3e,0xaaa2787c5e0f183870a0,0x83855e2f1f87c0e60690,0x688e2789cde0f1c97c24,0x4e941be2f0787c60f201,0x407f1787c7e00704c60,0x3e009920ff1787c7e007,0x4c70b0345525f178fc,0xc7e008120ff1037c7e1f,0xf0040907e1ecca5f1787,0x41e383f4ac4f1786cde3,0x3d3394872d13c5e0f1f8],#[0x87c7081e1b44f1787c1e,0xe1f178d1033961be0f17,0x78019]]
def g255H9 (j : Nat) := if j=0 then 0x1e61cc03748a8009 else 0
def g255D10 := limbs80 #[#[0x7bf26c3ac1dd9735c130,0x7cbb2c0987f65cd604c2,0xf32eb0261bf98758130f,0xdc9ae0987f65cd704c2f,0x70cb8261bf9865c130fe,0xc82e6985fee59704c37f,0xecb9a61ddd765cd30fed,0x32e6986f7619734c3bbe,0xbb2613fd985d930defc,0xeec985fe643764c27ff3,0xc32613fd98dd930beec9,0xe985fee41874c27fb2f,0x3a61bfb9061d30befc9b,0xe984ffe59874c37bf26c,0xa617dd93a1d30bfcc850,0xb077e5cd705827fb3143,0xc17fb935c160efdb9ae0,0x7bee5970583df2ecb82,0x13ff985cd60cfec3ae6b,0x67f61f73582ff321b9ac,0xbfb9061d609fecc6e6b0,0xf7e4d875837b926c3ac1,0xfb905cd709ffc9b0eb06,0xee41735c37bf06b9ae17,0xf865cd70eefc1ae6b877,0x65b835c33ff0db9ae19f,0x9361970bfdc82ecb84ff,0x1973dc27fb27c32e17df,0x361b709ffcb307b867f6,0x980dce7fb2dc02e73ff9,0x5c130ffcbb2e0984ffe5,0x734c3ff72cb8261ff996],#[0xcd30feecb2e6987f75d9,0x64c3ff320bb261fdf965,0xd30dfecc2ec986ff61d7,0x4c3fbf26c3a61ffb9061,0x60dffcb30e986ff65987,0x83ff326b82c1ff9735c1,0xffcc82e6b07fee4d705,0x37fb30b9ac1bfd875cd6,0xdffc9b0eb06ff64d8758,0x7ff0cb9ae1dfd765cd70,0xfec32e6b85ffe59735c3,0xfb2cb9ae1dff865cd70e,0xec36e6b877fe59735c3b,0xb0cc1ae1ffb9060d70ef,0xcb306b86ffe19835c37f,0x2dc1ae1bfd86e0d70bff,0xb706b86ff5db835c2ffb,0x6c32e1ffb9061970dfec,0xb0cb87f7e4d865c3fb92,0xc32e17fd93e1970bffc9,0x7b877f65973dc37fb27,0x2e7bfd9361b70dfecb3,0xb9eff619805cffbf26c,0x2e77ff9660173dffc330,0xb9eff65b805ceffb2dc0,0x6101f008c000dfecb301,0x44c1f00dd05d027c0f80,0x1d10db062c2d814d09b0,0xa4c4d8249113081c3e0,0x3491930c0c5c82c9157,0x7103c7e03c91d30e1c6d,0xf04d1255121c8d044921],#[0xdd164cad855129b146c9,0xd2866d32718bcc105e12,0x3b31cfce4070136d1acc,0xd0808153f91f2cf58789,0xd481238d1908ad43f217,0xdd3a89ad4c725ad28091,0xc155329fd4a8a2d50927,0xe8d6f8b5959b2c2d5c0a,0xc71627309d800be15e12,0x34cda18ce966532bd920,0x8e0d6f3370db30d716a9,0x788338c8ea5743395dc5,0x2e1e3e0881a109d17838,0x399c278b87838e20865e,0x38e2080fe2e1e0e30c18,0xe1e30c183827178b878,0x3383849f8b8c6080fe2e,0xc3060ce1e2e0e30d1a10,0xe2e1e309201f8b83878,0x1f8b83878c3050d0766e,0x38c3070b09e2e1e0e30e,0x6e2e1e327283c9f8b878,0x878f803060e090ac4e06,0xee266e0e3e1091c1f8b,0x2e1e30f1f8b878f80305,0x829b878b8c9c8c5c4e0e,0xc4a6e0e1e2e327203717,0x837109f838b878e9890e,0x8c306e2a6e0e3e109183,0xe1e2e0e30c1913838b87,0xd20244787838b8c38745,0x859881109e6e1e0e2e30],#[0xe1e30c1e2717138b838f,0x7878b838c3072744e0e2,0x8c5c4e2e1e0e30c1c9d1,0x8824389d978b8f878220,0x22070d092765e2e3e1e0,0x3e008181c35978b8f878,0x84238b838c34627e2e1e,0x38727e2a5e3e1e0481f,0x3e1e048231b138b878f8,0x8b8f87803090d27a5e2e,0xe2e3e1e048243c35209f,0x78b83878c3c80f0d27a5,0x665e2e1e0e3881858239,0xe3e08819978b87838e20,0x6387838b8c38965e2e1,0x5e6e1e2e0e30d2437991,0x10638b878f803890b0e2,0x25e6e2e1e3e00d241f99,0x99b8a97878f831090713,0x7e2a5e166e0e30d1c34a,0xe30f2436978b8f838520,0x38e20716e5440de2e0e1,0x2e0e1e3a6271d97878b8,0x97838f859890d4965c4e,0xe2e0e3e10e1c3c3b138a,0x597138b83878c3c766c4,0x866c50e4ae2e1e3e0a42,0xc219813178b87838c34,0xc30607270f0de0e2e1e3,0x66e2e30d243f8b87838,0x8b838c305882789c5e1e,0xe1e2e0e3c412283c9f87],#[0xb878f81203870f0a8766,0xb0fe2e1e0e30c181e278,0x383713152783878b8e98,0xc306e20ce0e1e3161854,0x1e0e30b0c1f8b838f842,0x238b878f80302c645e2e,0xe20a0ee266e1e3e01115,0x820503835978b878f809,0x203470e0988e1e2e0e31,0xe3e0481625978b878f82,0xb87838c6080e09a5e2e1,0x2e1e3e00b0c18209e978,0x651824338b87838c606e,0x71198a0f0d88e2e1e0e3,0x30d243c38378b878f829,0x203860a44a5e2e166e0e,0xe2e1e0e3181f8b878f81,0x37859b8b838c50a48a5,0x4e2e166e3e01028a81d1,0x9b8f8780384c8872aa5c,0x48e2e1e0e30d0c201f89,0x42697878b838c546090f,0x50726a5e1e2e0e3181c3,0xe066151c2b859b838b8c,0x38b878e943490ee2e1e3,0x2e3e1e0480d2458a9238,0x8b87838d20348160fa5e,0xa5e2e0e3e10d481c2a97,0x3171834238b87838c607,0x8b87838c5c788e2e1e0e,0xe1e2e088e36514209623,0x83597878b838e985090f],#[0x30765e1e2e0a6e30d1c3,0xe30b0e243c3b8b878f80,0x38f843ca0f2ac4e2e0e1,0x30d11229838a9978b138,0x838e902c90e09e2e1e0e,0xe3e10e111e25299b8b87,0x7878f81984454a08e2e0,0x1e2e0e30e102c3717882,0x8b838c3870f0ac5a466e,0xe2e1e3e0280d212a9387,0xfc5]]
def g255H10 := limbs80 #[#[0x41140046485b0001d62f,0x98a0ad74a12d021a8c8,0x2e12f737ba722544400,0xec13d9b92d12c934543,0x878dac693000000050d1,0xf1dc1442042883f73683,0x626618341fa14c0009,0x2000182000000d9e480a,0x3b8322215b8a33d2201,0x9944628a13d31b327906,0x1b76012b640718921e5,0x8531a8353b4d9db9000,0x4a41589f000781239331,0x7240a2d1112a7ada1cb,0x63e4493173bc72900000,0x420b000b086406c73bb,0x547d3c000e2332b0006,0x548119d057bea0260c00,0x8800000030300078e00a,0xfe877420000005450004,0x13a9b0b16d8f61f410c0]]
def g255D11 := limbs80 #[#[0x5cd30ff9704c3fe58130,0x4c2ffe1930bfd864c3f7,0xff970582ffe1d30bfd87,0xdcd70dfd735c2ff61d60,0xdc2ffe1970bff835c37f,0xbfd86dc2ff60f70dfd73,0x5d930bfd80dceffe0173,0x4c3ff61d30fff764c3ff,0xfff73583ff5cd60ffe87,0xe0d70ffd835c3ff5cd70,0x5c3ff61970ffd765c3ff,0xfff805cfff60173fff86,0x57c8d0e31661b818000,0x3d81ac550e8ecfe9bf31,0x844ca9351720bbd9728d,0x700d5b9a30adc2b094e2,0x1187160c6306fbbe2ba6,0x18c242278b830e2c6308,0x7063183070a9e260c38b,0x243a6c18b0e312387c58,0x3182a7139a2c4c187163,0x27cb8b0e3c0207c38316,0x812909c2e5c587063104,0x98b0e3c0507cd13161c7,0xc18b0e34a40d13983a58,0xdcb13161c18d31037344,0x8e13983c44b8b061c650,0x9891d13307c5830e34a4,0x18d2103f2c40f8b061c6,0xc5871e04848ecd170e2c,0x64f8b0e0c63081b17307,0x318c230e2c18d38c1878],#[0x8b0634e3068b113e2c38,0xc1e2274b8b1e1c120ac3,0x982e2624b871e04f2081,0xc16386e60e970c4c5831,0x491b1c4e688970e0c58c,0x80c161c266c38b0634a3,0x20a1e37287898b0a6c7,0x4c3484a363e5c5870633,0xc5871962c3e5c38b063,0x60c6907123a389cd1526,0x3e68b871]]
def g255H11 := limbs80 #[#[0x400ca00101114110b005,0x61010010c37030404c40,0xc00284d7045a8014400,0x27580009824bdc1654c1,0xb2d6c61400315282800,0x9ef5558bce48d4af8122,0xe8fbc340019b4002c019,0x307f0ec6940024d,0x20ffd8cb20000,0x32c0010651640026100,0xaeec44d4ada5d6988800,0x184c1db3513009ca3a7d,0x800220c00124a8abd7b1,0x26cf88c06,0x56974d40000002c2d0ac,0x400312bc5c0020948505,0x4d91bd90000318593802,0xb800d4ce89ed27db9a08,0x1479da000296287383d0,0xb9800106e0d1e330e000,0x8483492bafc3334b486,0xfd5fa4d4180031a80039,0xc74000594003cc9e7930,0x1c0004e80000004a7849,0x1d2c000003d58003c609,0xe500004f0002247999f0,0x220b50f451740400041d,0xfc54002d44012f0643ac,0x44000000285923719097,0xc4134000000000002132,0x813e9af505098003621c,0x130baa11700026fe37]]
def g255D12 := limbs80 #[#[0x3ffee1ff5c3feb07fd30,0x37950721e003ffb9ffd7,0x2081c61448218a33098a,0x848628232071258a18e0,0x32259848228631c81e59,0x8a08631c81e69058a086,0x26905]]
def g255H12 := limbs80 #[#[0xab310000034b4c626203,0x80c154c00b488b002251,0x3c004fc00d7c48914003,0x9d4e02432001dd002d6a,0xfb80000cd3cd14ee2d15,0x3575c10c26c000008a7,0x10006180078800003900,0x3a9468dc001d570ddec,0x51cc2f62d90022d0]]
def g255D13 (j : Nat) := if j=0 then 0x62900208c7ff else 0
def g255H13 := limbs80 #[#[0x32b48800000000,0x30b500e33100000000,0x6b006a]]
def g255L : Nat → Packing
  | 8 => (4,5,5,0,0,8,0,g255D8)
  | 9 => (75,4,5,0,0,13,0,g255D9)
  | 10 => (112,3,5,0,0,13,0,g255D10)
  | 11 => (32,2,5,0,0,11,0,g255D11)
  | 12 => (6,1,5,0,0,9,0,g255D12)
  | 13 => (1,0,5,0,0,0,0,g255D13)
  | _ => emptyPacking
def g255I : Nat → Nat → Option (Nat × Nat)
  | 9 => lookupWord 1 11 0 7 2 1 g255H9
  | 10 => lookupWord 26 127 6 12 7 1 g255H10
  | 11 => lookupWord 35 197 6 12 7 1 g255H11
  | 12 => lookupWord 11 67 4 10 5 1 g255H12
  | 13 => lookupWord 2 23 0 8 3 1 g255H13
  | _ => fun _ => none
def g255 : Forest := ⟨255,13,fun i => g255Y[i]?.getD (0,0),g255C,g255A,g255L,g255I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_0 : block g255 8 0 4=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B8 : block g255 8 0 4=true := g255P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_0 : block g255 9 0 7=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_7 : block g255 9 7 68=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B9 : block g255 9 0 75=true := (@block_merge g255 9 0 7 68 g255P9_0 g255P9_7)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_0 : block g255 10 0 2=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_2 : block g255 10 2 57=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_59 : block g255 10 59 53=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B10 : block g255 10 0 112=true := (@block_merge g255 10 0 2 110 g255P10_0 (@block_merge g255 10 2 57 53 g255P10_2 g255P10_59))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_0 : block g255 11 0 18=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_18 : block g255 11 18 14=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B11 : block g255 11 0 32=true := (@block_merge g255 11 0 18 14 g255P11_0 g255P11_18)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P12_0 : block g255 12 0 6=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B12 : block g255 12 0 6=true := g255P12_0
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
  · exact (rfl : block g255 7 0 0 = true)
  · exact g255B8
  · exact g255B9
  · exact g255B10
  · exact g255B11
  · exact g255B12
  · exact g255B13
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255G : graphValid g255 (boundsBefore K247) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255R : Impossible true graph 13 sevenInputs.toFinset := by
  rw [show graph = targetOf g255 by decide +kernel]
  exact root_index (g:=g255) (top:=13) (i:=0) (before_sound K247 V247) g255G g255T (by decide) (by decide +kernel)

end PEqualNP.Outside.L_meta_35002

open PEqualNP.Outside.L_meta_35002 in
theorem PEqualNP.Outside.L_meta_35002 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o fit _ correct
  exact replaceShort g255R gates o fit correct

import PEqualNP.Defs

-- The two-mode live-state and cofactor checker follows L_meta_1674 and L_meta_670.
-- The graph, restrictions and all search certificates below are for L_meta_33076.

-- Shared forest and cofactor certificates from L_meta_1674 and PR 11111 for L_meta_1677.
-- The original credit line is retained below. The two root certificates here cover the unpinned graph.

-- The checker and the bound certificates are adapted from PEqualNP/Outside/L_meta_1667.lean (Apache-2.0).
-- Two modes: u=false are monotone runs (AND, OR); u=true are runs up to complement, where negation is free.
namespace PEqualNP.Outside.L_meta_33076
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
def graph : Sig := (BitVec.ofNat 512 (word80 [0xffffffff,0xfffffffeffffffffffff,0xffeefffffffefffffffa,0xfefefefceeeeaa00ffff,0xfffffffffffeffffffff,0xffffffeefffffffeffff,0xfffafefefefceeeeaa00]))
def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 4 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 5 && x 7)
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
  (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 1 &&& x 5) ||| (x 2 &&& x 5) ||| (x 0 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7)
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
  (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 1 &&& x 5) ||| (x 2 &&& x 5) ||| (x 0 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7)
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
def packedAt (word : Nat → Nat) (pos len : Nat) :=
  let i := pos/8192
  let shift := pos % 8192
  let lo := word i >>> shift
  if shift+len ≤ 8192 then lo &&& ((1 <<< len)-1)
  else (lo ||| (word (i+1) <<< (8192-shift))) &&& ((1 <<< len)-1)


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



def target (x : Fin 8 → Bool) : Bool := decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
def smallCircuit : Circuit := ⟨[⟨.or,[3,4]⟩,⟨.or,[0,1]⟩,⟨.or,[0,2]⟩,⟨.or,[8,10]⟩,⟨.or,[0,7]⟩,⟨.or,[1,2]⟩,⟨.or,[7,13]⟩,⟨.or,[4,7]⟩,⟨.and,[14,5]⟩,⟨.and,[6,11]⟩,⟨.and,[15,9]⟩,⟨.and,[12,8]⟩,⟨.or,[16,17]⟩,⟨.or,[20,18]⟩,⟨.or,[21,19]⟩], 22⟩

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

def lowRow (i : Fin 8) : Row := Fin.ofNat 512 (1 <<< ([3, 4, 5, 0, 0, 1, 0, 0] : List Nat).getD i.val 0)
def highRow (i : Fin 8) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< ([3, 4, 5, 0, 0, 1, 0, 0] : List Nat).getD i.val 0))

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
theorem low19 : Lower true (varsX 19) (graphGoal 19) 2 := by
  have q := @lower_count true (vars 19) (graphGoal 19) (proper_of _ (by decide +kernel)) (graphPairs 19 68) (by decide +kernel)
  exact q
def K19 := extendKnown [] 2 [(88,[48,65,32,33,98,82])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V19 : Known true K19 := extend_ok (m:=19) baseKnown low19 (by decide +kernel)
def g73Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3ff63ff63ff63ff63f,0xf63ff63ff63ff63ff63f])),(BitVec.ofNat 152 (word80 [0x492049204920492049,0x20492049204920492049]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xc7fbc7fbc7fbc7fbc7,0xfbc7fbc7fbc7fbc7fbc7])),(BitVec.ofNat 152 (word80 [0x924092409240924092,0x40924092409240924092]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xf8fdf8fdf8fdf8fdf8,0xfdf8fdf8fdf8fdf8fdf8])),(BitVec.ofNat 152 (word80 [0x248124812481248124,0x81248124812481248124]))),(0x0,0x0),(0x0,0x0)]
def g73C : List ColumnInfo := []
def g73A : List (List Nat) := [[],[99],[48],[48,96],[96,48],[96]]
def g73D3 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7
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
theorem g73G : graphValid g73 (boundsBefore K19) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low73 : Lower true (varsX 73) (graphGoal 73) 4 := lower_forest (g:=g73) (i:=0) (hints:=3) (before_sound K19 V19) g73G g73T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K73 := extendKnown K19 4 [(73,[]),(81,[67]),(137,[118]),(145,[67,118]),(146,[16,67,118]),(162,[16,83,67,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V73 : Known true K73 := extend_ok (m:=73) V19 low73 (by decide +kernel)
def g27Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xe6de3fff03fff1ffe6,0xde3fff03fff1ffe6de3f])),(BitVec.ofNat 152 (word80 [0x648490a2850240206,0x48490a28502402064849]))),((BitVec.ofNat 152 (word80 [0x19e9c0fffc07fe3f19,0xe9c0fffc07fe3f19e9c0])),(BitVec.ofNat 152 (word80 [0x50e8db2c3161408450,0xe8db2c3161408450e8db]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xece607fffff8003fec,0xe607fffff8003fece607])),(BitVec.ofNat 152 (word80 [0x8a7b6b04185892808,0xa7b6b04185892808a7b6]))),((BitVec.ofNat 152 (word80 [0x1b3df8ffffffffc01b,0x3df8ffffffffc01b3df8])),(BitVec.ofNat 152 (word80 [0x891524c08206003089,0x1524c082060030891524]))),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g27C : List ColumnInfo := []
def g27A : List (List Nat) := [[],[64,49]]
def g27D3 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xf
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
theorem g27G : graphValid g27 (boundsBefore K73) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low27 : Lower true (varsX 27) (graphGoal 27) 4 := lower_forest (g:=g27) (i:=0) (hints:=67) (before_sound K73 V73) g27G g27T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K27 := extendKnown K73 4 [(27,[]),(51,[16,83]),(54,[16,32,67,83]),(86,[96,32,50,83]),(90,[96,32,82]),(101,[32,16,83,100]),(102,[32,99,84,67]),(108,[32,49,81,100]),(114,[64,81,32,99,33]),(116,[32,65,83,97,49]),(165,[80,16,33,50,116,100]),(172,[112,33,16,84,65,100]),(195,[99,116,83,84]),(204,[48,33,16,113,100,81]),(212,[64,33,16,115,97,81,83]),(225,[81,33,99,116]),(228,[80,97,32,115,66,65,67]),(232,[48,81,32,98,116]),(240,[64,81,32,99,114,50])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V27 : Known true K27 := extend_ok (m:=27) V73 low27 (by decide +kernel)
def g77Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfdf00fff81fc7e3ffb,0xe01fff03f8fc7ff7c03f])),(BitVec.ofNat 152 (word80 [0x45c09245142904808b,0x81248a28520901170249]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xe6a8703ffe007fc7cd,0x50e07ffc00ff8f9aa1c0])),(BitVec.ofNat 152 (word80 [0x96a9b6d618b228112d,0x536dac316450225aa6db]))),((BitVec.ofNat 152 (word80 [0xfbb781ffffff8007f7,0x6f03ffffff000feede07])),(BitVec.ofNat 152 (word80 [0x235249820c0312204,0x6a49304180624408d492]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x64ffe3ffffffff80c,0x9ffc7ffffffff0193ff8])),(BitVec.ofNat 152 (word80 [0x249204100400400,0x4924082008008000924]))),(0x0,0x0),(0x0,0x0)]
def g77C : List ColumnInfo := [(4,0,73,0,4)]
def g77A : List (List Nat) := [[],[48]]
def g77D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1f
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
theorem g77G : graphValid g77 (boundsBefore K27) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low77 : Lower true (varsX 77) (graphGoal 77) 5 := lower_forest (g:=g77) (i:=0) (hints:=1539) (before_sound K27 V27) g77G g77T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K77 := extendKnown K27 5 [(77,[]),(83,[33,99,67]),(85,[67]),(139,[33,118]),(154,[16,50,66,118]),(163,[16,32,83,67,118]),(166,[16,115,67,84,101]),(169,[82,66,118]),(170,[16,50,82,66,118]),(177,[82,67,50,118]),(210,[16,98,115,66,83])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V77 : Known true K77 := extend_ok (m:=77) V27 low77 (by decide +kernel)
def g89Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffe701fffc1f9f9ffe,0x701fffc1f9f9ffe701ff])),(BitVec.ofNat 152 (word80 [0x40012490841010040,0x1249084101004001249]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x3e7d0e07ffe01fe3e7,0xd0e07ffe01fe3e7d0e07])),(BitVec.ofNat 152 (word80 [0x891d2492508a4a0891,0xd2492508a4a0891d2492]))),((BitVec.ofNat 152 (word80 [0x3f8bf038ffffe003f8,0xbf038ffffe003f8bf038])),(BitVec.ofNat 152 (word80 [0x104ba492610c0c5104,0xba492610c0c5104ba492]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xc018ffc0fffffffc01,0x8ffc0fffffffc018ffc0])),(BitVec.ofNat 152 (word80 [0x200049248210100200,0x4924821010020004924]))),(0x0,0x0),(0x0,0x0)]
def g89C : List ColumnInfo := [(8,0,81,0,4)]
def g89A : List (List Nat) := [[],[67],[96],[96,67]]
def g89D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1f
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
theorem g89G : graphValid g89 (boundsBefore K77) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low89 : Lower true (varsX 89) (graphGoal 89) 5 := lower_forest (g:=g89) (i:=0) (hints:=3) (before_sound K77 V77) g89G g89T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K89 := extendKnown K77 5 [(89,[]),(147,[64,33,49,16,118]),(153,[118]),(178,[16,67,83,118]),(201,[99,116,84]),(209,[99,116,83,84])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V89 : Known true K89 := extend_ok (m:=89) V77 low89 (by decide +kernel)
def g55Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xe001ffc07ff01ffe00,0x3fffff80ffd35632000f])),(BitVec.ofNat 152 (word80 [0x48d4128d0522c8549a,0x92522916299346225555]))),((BitVec.ofNat 152 (word80 [0xfffe00007fffffffff,0xc007ffff01a3adc80ff0])),(BitVec.ofNat 152 (word80 [0x80981b160644809813,0x36032244d030cc81111]))),((BitVec.ofNat 152 (word80 [0xffffffff80001fffff,0xfff80000003f407df000])),(BitVec.ofNat 152 (word80 [0x2e05c18178702e01c,0x380bc387033007d3333]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1fffff,0xfffffffffe663f7600ff])),(BitVec.ofNat 152 (word80 [0x130160205808130120,0x2404c00000643114aaaa]))),((BitVec.ofNat 152 (word80 [0xffffffffffffe00000,0x19dd38dff00])),(BitVec.ofNat 152 (word80 [0x1c01800060001c01c0,0x38070040808cd300cccc]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g55C : List ColumnInfo := []
def g55A : List (List Nat) := [[],[32,84]]
def g55D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1f
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
theorem g55G : graphValid g55 (boundsBefore K89) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low55 : Lower true (varsX 55) (graphGoal 55) 5 := lower_forest (g:=g55) (i:=0) (hints:=1049924) (before_sound K89 V89) g55G g55T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K55 := extendKnown K89 5 [(55,[]),(59,[48,65,82,32,16]),(103,[33,100]),(110,[16,32,48,84,100]),(122,[48,65,82,97,33]),(199,[16,116,101,84]),(206,[16,48,116,101,84])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V55 : Known true K55 := extend_ok (m:=55) V89 low55 (by decide +kernel)
def g87Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x7ff003ff80fffffff0,0x3ffffe03ff4b19901c7])),(BitVec.ofNat 152 (word80 [0x2a1a8251a148a02a1,0xa84a0a458a44b1811249]))),((BitVec.ofNat 152 (word80 [0x7ffffc0000ffc07fff,0xfc00ffffc068db260038])),(BitVec.ofNat 152 (word80 [0x44c132362c191344c9,0x326c8c891360d3265b6d]))),((BitVec.ofNat 152 (word80 [0x7fffffffff00007fff,0xffff0000000ff00e8e00])),(BitVec.ofNat 152 (word80 [0x1705c0b8305e1c1701,0xc0702f0e1c0db00eb6db]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x800000000000007fff,0xffffffffff99af6d703f])),(BitVec.ofNat 152 (word80 [0x180600c04060201802,0x80300000190c082492]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffff8000,0x6754f2ffc0])),(BitVec.ofNat 152 (word80 [0x60080300008000600c,0x300c010202240704924]))),(0x0,0x0),(0x0,0x0)]
def g87C : List ColumnInfo := [(2,0,85,0,5)]
def g87A : List (List Nat) := [[],[33,100]]
def g87D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3f
def g87L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g87D5)
  | _ => emptyPacking
def g87I (_ _ : Nat) : Option (Nat × Nat) := none
def g87 : Forest := ⟨87,5,fun i => g87Y[i]?.getD (0,0),g87C,g87A,g87L,g87I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g87P5_0 : block g87 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g87B5 : block g87 5 0 1=true := g87P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g87T : checkedTables g87 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g87 0 0 0 = true)
  · exact (rfl : block g87 1 0 0 = true)
  · exact (rfl : block g87 2 0 0 = true)
  · exact (rfl : block g87 3 0 0 = true)
  · exact (rfl : block g87 4 0 0 = true)
  · exact g87B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g87G : graphValid g87 (boundsBefore K55) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low87 : Lower true (varsX 87) (graphGoal 87) 6 := lower_forest (g:=g87) (i:=0) (hints:=1604) (before_sound K55 V55) g87G g87T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K87 := extendKnown K55 6 [(87,[]),(167,[16,116,84,101]),(174,[16,32,48,84,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V87 : Known true K87 := extend_ok (m:=87) V55 low87 (by decide +kernel)
def g91Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffc03ff0fffffc03f,0xfff0fffff5560300f0ff])),(BitVec.ofNat 152 (word80 [0x2028280a2020028281,0x40220020900603111111]))),((BitVec.ofNat 152 (word80 [0xffffc000ff0ffffc0,0x1fff0ff014b579000f00])),(BitVec.ofNat 152 (word80 [0x48b0322c41428b2325,0x9140284214b551bbbbbb]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffff000ffffff,0xe0000fff2bb5260f000f])),(BitVec.ofNat 152 (word80 [0x82c140b005842c0406,0x58442802b9120666666]))),((BitVec.ofNat 152 (word80 [0xf00000000000ffffff,0xfffff000134bf8f00ff0])),(BitVec.ofNat 152 (word80 [0x30180c08608300808,0x6000304034828444444]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffff000000,0xcea8c5fff000])),(BitVec.ofNat 152 (word80 [0xc0203000800c03030,0x18088c084420c4888888]))),(0x0,0x0),(0x0,0x0)]
def g91C : List ColumnInfo := [(0,2,73,16,5),(2,0,89,0,5),(8,0,83,0,5),(1,0,90,0,4),(16,2,73,0,4),(64,0,27,0,4)]
def g91A : List (List Nat) := [[],[96]]
def g91D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x5bd4940
def g91D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xc8404fd40
def g91H5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xd
def g91D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x2b2a0bf
def g91H6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3
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
theorem g91G : graphValid g91 (boundsBefore K87) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low91 : Lower true (varsX 91) (graphGoal 91) 7 := lower_forest (g:=g91) (i:=0) (hints:=67) (before_sound K87 V87) g91G g91T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K91 := extendKnown K87 7 [(91,[]),(182,[16,32,67,83,118]),(203,[99,116,84]),(205,[33,115,100,84,83]),(213,[33,115,100,83]),(233,[81,33,99,116]),(241,[81,33,99,116,67]),(242,[16,96,32,83,50,115])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V91 : Known true K91 := extend_ok (m:=91) V87 low91 (by decide +kernel)
def g93Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3ff801ffc07fe03fff,0xfffffffffff6ef4401ff])),(BitVec.ofNat 152 (word80 [0x805014028100408001,0x40500800101063409249]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x3ffffe00007fffc07f,0xe007fc0ff810c6bc0e00])),(BitVec.ofNat 152 (word80 [0x156298ab162a8a1515,0x8d6251a522d0c6bdb6db]))),((BitVec.ofNat 152 (word80 [0x3fffffffff8000007f,0xfff8000fffee16747007])),(BitVec.ofNat 152 (word80 [0x198320cc2433132626,0x98362c6448e14352492]))),((BitVec.ofNat 152 (word80 [0xc0000000000000007f,0xfffffff00003f8a78038])),(BitVec.ofNat 152 (word80 [0x1e03c0f0383c1c3838,0xe038307870398a52492]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffffff80,0x1911bbffc0])),(BitVec.ofNat 152 (word80 [0x200401000040000040,0x10040008000000024924]))),(0x0,0x0),(0x0,0x0)]
def g93C : List ColumnInfo := [(4,0,89,0,5)]
def g93A : List (List Nat) := [[],[67]]
def g93D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3f
def g93L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g93D5)
  | _ => emptyPacking
def g93I (_ _ : Nat) : Option (Nat × Nat) := none
def g93 : Forest := ⟨93,5,fun i => g93Y[i]?.getD (0,0),g93C,g93A,g93L,g93I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g93P5_0 : block g93 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g93B5 : block g93 5 0 1=true := g93P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g93T : checkedTables g93 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g93 0 0 0 = true)
  · exact (rfl : block g93 1 0 0 = true)
  · exact (rfl : block g93 2 0 0 = true)
  · exact (rfl : block g93 3 0 0 = true)
  · exact (rfl : block g93 4 0 0 = true)
  · exact g93B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g93G : graphValid g93 (boundsBefore K91) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low93 : Lower true (varsX 93) (graphGoal 93) 6 := lower_forest (g:=g93) (i:=0) (hints:=1539) (before_sound K91 V91) g93G g93T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K93 := extendKnown K91 6 [(93,[]),(185,[82,118]),(186,[16,50,66,82,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V93 : Known true K93 := extend_ok (m:=93) V91 low93 (by decide +kernel)
def g94Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1fff0007ff803ffc01,0xfffffffffff245f3f007])),(BitVec.ofNat 152 (word80 [0x502a8350250681482d,0x550950a414040f37b6d]))),((BitVec.ofNat 152 (word80 [0x1ffffff800003fffff,0xffe001ffe001b15bc038])),(BitVec.ofNat 152 (word80 [0x854c2a62b62b159148,0x2986d84c8661a159c6db]))),((BitVec.ofNat 152 (word80 [0x1fffffffffffc00001,0xfffffe00000ce425d1c0])),(BitVec.ofNat 152 (word80 [0x6703383384c19e270,0x4e04e06f0b88a425d6db]))),((BitVec.ofNat 152 (word80 [0xe00000000000000001,0xfffffffffff22fedae07])),(BitVec.ofNat 152 (word80 [0x7803c03c0701e0380,0x700700700c022d0c8492]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffffffffffffe,0xdfa9e5ff8])),(BitVec.ofNat 152 (word80 [0x1800c0040000200001,0x80180180100452820924]))),(0x0,0x0),(0x0,0x0)]
def g94C : List ColumnInfo := [(4,0,90,0,4)]
def g94A : List (List Nat) := [[],[50]]
def g94D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3f
def g94L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g94D4)
  | _ => emptyPacking
def g94I (_ _ : Nat) : Option (Nat × Nat) := none
def g94 : Forest := ⟨94,4,fun i => g94Y[i]?.getD (0,0),g94C,g94A,g94L,g94I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g94P4_0 : block g94 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g94B4 : block g94 4 0 1=true := g94P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g94T : checkedTables g94 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g94 0 0 0 = true)
  · exact (rfl : block g94 1 0 0 = true)
  · exact (rfl : block g94 2 0 0 = true)
  · exact (rfl : block g94 3 0 0 = true)
  · exact g94B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g94G : graphValid g94 (boundsBefore K93) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low94 : Lower true (varsX 94) (graphGoal 94) 5 := lower_forest (g:=g94) (i:=0) (hints:=33646144) (before_sound K93 V93) g94G g94T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K94 := extendKnown K93 5 [(94,[]),(124,[81,50,66]),(188,[33,49,65,81,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V94 : Known true K94 := extend_ok (m:=94) V93 low94 (by decide +kernel)
def g107Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xc00fff0ffffffc00ff,0xfff0fffeea3a5303f03f])),(BitVec.ofNat 152 (word80 [0x84a08a210802284a02,0x80220882200a53145145]))),((BitVec.ofNat 152 (word80 [0xfff0000ffc3fffff00,0x3fffffc009adfd000fc0])),(BitVec.ofNat 152 (word80 [0xc42c405090b10c4b,0x11404108092d994d34d3]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffff0003fffffff,0xc000fffd77e88afc003f])),(BitVec.ofNat 152 (word80 [0x90130026104c0100c,0x584120152a08828a28a]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x3fffffff,0xffff00012697f4000fc0])),(BitVec.ofNat 152 (word80 [0x2e09c08b8227026090,0x26009c11269264b2cb2c]))),((BitVec.ofNat 152 (word80 [0xffffffffffc0000000,0x39d530dfff000])),(BitVec.ofNat 152 (word80 [0x300e000c00380380e0,0x3808e0208d5104c30c30]))),(0x0,0x0),(0x0,0x0)]
def g107C : List ColumnInfo := [(0,2,73,32,5)]
def g107A : List (List Nat) := [[],[99],[81],[81,99],[48],[48,96],[48,81],[48,81,96],[96,48],[96],[96,81,48],[96,81]]
def g107D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3f
def g107L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g107D5)
  | _ => emptyPacking
def g107I (_ _ : Nat) : Option (Nat × Nat) := none
def g107 : Forest := ⟨107,5,fun i => g107Y[i]?.getD (0,0),g107C,g107A,g107L,g107I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g107P5_0 : block g107 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g107B5 : block g107 5 0 1=true := g107P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g107T : checkedTables g107 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g107 0 0 0 = true)
  · exact (rfl : block g107 1 0 0 = true)
  · exact (rfl : block g107 2 0 0 = true)
  · exact (rfl : block g107 3 0 0 = true)
  · exact (rfl : block g107 4 0 0 = true)
  · exact g107B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g107G : graphValid g107 (boundsBefore K94) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low107 : Lower true (varsX 107) (graphGoal 107) 6 := lower_forest (g:=g107) (i:=0) (hints:=1048659) (before_sound K94 V94) g107G g107T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K107 := extendKnown K94 6 [(107,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V107 : Known true K107 := extend_ok (m:=107) V94 low107 (by decide +kernel)
def g109Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xf003ff87fe1fffc01f,0xfff87fffe474a4007c1f])),(BitVec.ofNat 152 (word80 [0xa12845108440228940,0xa01108826014a45294a5]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffc0007ffe1ffffe0,0xfffffc0335be20f83e0])),(BitVec.ofNat 152 (word80 [0xc030162028040b0182,0xc0a00108225922318c63]))),((BitVec.ofNat 152 (word80 [0xfffffff80001ffffff,0xf0007ffccfd11df0001f])),(BitVec.ofNat 152 (word80 [0x240980130884c0203,0x2c2120087c108a5294a]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1ffffff,0xffff80004d2fe80003e0])),(BitVec.ofNat 152 (word80 [0xb82e045c111702c14,0xb005c104d26c9ce739c]))),((BitVec.ofNat 152 (word80 [0xfffffffffffe000000,0x33aa61bfffc00])),(BitVec.ofNat 152 (word80 [0xc0300060001803018,0xc046021182211084210]))),(0x0,0x0),(0x0,0x0)]
def g109C : List ColumnInfo := [(0,32,73,4,5),(32,0,77,0,5),(1,0,108,0,4),(4,32,73,0,4),(8,0,101,0,4)]
def g109A : List (List Nat) := [[],[48]]
def g109D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x5bd4940
def g109D5 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x2012,0x240d140ff40fd40fd20])
def g109H5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xe
def g109D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x18989f
def g109H6 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x44000000,0x1580001a010007200000])
def g109L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g109D4)
  | 5 => (3,1,3,0,0,5,0,g109D5)
  | 6 => (1,0,3,0,0,0,0,g109D6)
  | _ => emptyPacking
def g109I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 4 0 0 g109H5
  | 6 => lookupWord 1 19 0 7 2 1 g109H6
  | _ => fun _ => none
def g109 : Forest := ⟨109,6,fun i => g109Y[i]?.getD (0,0),g109C,g109A,g109L,g109I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g109P4_0 : block g109 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g109B4 : block g109 4 0 1=true := g109P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g109P5_0 : block g109 5 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g109B5 : block g109 5 0 3=true := g109P5_0
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
  · exact g109B4
  · exact g109B5
  · exact g109B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g109G : graphValid g109 (boundsBefore K107) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low109 : Lower true (varsX 109) (graphGoal 109) 7 := lower_forest (g:=g109) (i:=0) (hints:=2098435) (before_sound K107 V107) g109G g109T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K109 := extendKnown K107 7 [(109,[]),(115,[33,99,67]),(117,[67]),(173,[82,118]),(181,[82,67,118]),(214,[16,98,115,67,82,84]),(227,[16,32,83,67,100,116]),(230,[16,115,67,101]),(234,[16,50,82,66,100,116])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V109 : Known true K109 := extend_ok (m:=109) V107 low109 (by decide +kernel)
def g118Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0xf003ff0ff87ff007ff,0xff87fffcd47c560003ff])),(BitVec.ofNat 152 (word80 [0xa4280a201120a45214,0x81102080501c1694a529]))),((BitVec.ofNat 152 (word80 [0xfffc000ffffffff801,0xfff87fc35353a20ffc00])),(BitVec.ofNat 152 (word80 [0xc0302c40a002c06058,0xa01010a425122318c63]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffff0007ffffffe,0x7ffcafd11df0001f])),(BitVec.ofNat 152 (word80 [0x140b002c20b008060,0x2c220a00a741086318c6]))),((BitVec.ofNat 152 (word80 [0x7fffffff,0xffff80004d2fe8007fe0])),(BitVec.ofNat 152 (word80 [0x982c08b044c090481,0x30004c100d22c94a5294]))),((BitVec.ofNat 152 (word80 [0xffffffffff80000000,0x33aa61bff8000])),(BitVec.ofNat 152 (word80 [0xe03000c00700e0701,0xc044702118a6118c6318]))),(0x0,0x0),(0x0,0x0)]
def g118C : List ColumnInfo := [(2,0,116,0,4),(4,0,114,0,4),(16,0,102,0,4),(32,0,86,0,4),(64,0,54,0,4)]
def g118A : List (List Nat) := [[],[98,84],[33,100],[33,65,81,97],[65,101],[65,82,97,33],[81,66],[81,98,65,66],[97,33,66,84],[97,82]]
def g118D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x57d4d10
def g118D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xc1a0fd20fd10
def g118H5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0
def g118D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x23440bf
def g118H6 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x85002ed7000000009000,0xc33600000000610000,0x6a000000005b0200])
def g118L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g118D4)
  | 5 => (2,1,3,0,0,4,0,g118D5)
  | 6 => (1,0,3,0,0,0,0,g118D6)
  | _ => emptyPacking
def g118I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 4 0 0 g118H5
  | 6 => lookupWord 2 37 0 8 1 3 g118H6
  | _ => fun _ => none
def g118 : Forest := ⟨118,6,fun i => g118Y[i]?.getD (0,0),g118C,g118A,g118L,g118I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g118P4_0 : block g118 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g118B4 : block g118 4 0 1=true := g118P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g118P5_0 : block g118 5 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g118B5 : block g118 5 0 2=true := g118P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g118P6_0 : block g118 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g118B6 : block g118 6 0 1=true := g118P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g118T : checkedTables g118 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g118 0 0 0 = true)
  · exact (rfl : block g118 1 0 0 = true)
  · exact (rfl : block g118 2 0 0 = true)
  · exact (rfl : block g118 3 0 0 = true)
  · exact g118B4
  · exact g118B5
  · exact g118B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g118G : graphValid g118 (boundsBefore K109) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low118 : Lower true (varsX 118) (graphGoal 118) 7 := lower_forest (g:=g118) (i:=0) (hints:=34669888) (before_sound K109 V109) g118G g118T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K118 := extendKnown K109 7 [(118,[]),(229,[16,82,100,114,66]),(236,[33,49,84,100,116]),(244,[33,65,49,83,99,115])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V118 : Known true K118 := extend_ok (m:=118) V109 low118 (by decide +kernel)
def g155Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfe1ff00ff87f87ffc0,0x7fff8fffd8b95000f0ff])),(BitVec.ofNat 152 (word80 [0x1440a0a05101100285,0x5012008488941111111]))),((BitVec.ofNat 152 (word80 [0x1ffff0007ff87fff,0x807ff1fc2b1e600f0f00])),(BitVec.ofNat 152 (word80 [0x5882c0c1620a010b06,0x160a0411291e43333333]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1fffffff80007fff,0xff8001ff941fb0f0000f])),(BitVec.ofNat 152 (word80 [0x610b0505802c222c08,0x182c48a01416b6666666]))),((BitVec.ofNat 152 (word80 [0xffe000000000007fff,0xfffffe000be4bf000ff0])),(BitVec.ofNat 152 (word80 [0x800c06060430443010,0x203000c20260b4444444]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffff8000,0x6442cffff000])),(BitVec.ofNat 152 (word80 [0x1008080040004020,0x40400100000008888888]))),(0x0,0x0)]
def g155C : List ColumnInfo := [(1,0,154,0,5),(2,0,153,0,5),(8,0,147,0,5),(16,0,139,0,5)]
def g155A : List (List Nat) := [[],[64,49]]
def g155D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x4e09f
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
theorem g155G : graphValid g155 (boundsBefore K118) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low155 : Lower true (varsX 155) (graphGoal 155) 7 := lower_forest (g:=g155) (i:=0) (hints:=67) (before_sound K118 V118) g155G g155T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K155 := extendKnown K118 7 [(155,[]),(179,[16,83]),(211,[99,116,83])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V155 : Known true K155 := extend_ok (m:=155) V118 low155 (by decide +kernel)
def g171Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffc01ff87fc3fff00,0xffff1ffed2e680007c1f])),(BitVec.ofNat 152 (word80 [0x222894451108808a4a,0xa02444252268a5294a5]))),((BitVec.ofNat 152 (word80 [0xffffe0007ffc3ffff,0xffffe11773400f83e0])),(BitVec.ofNat 152 (word80 [0x40b018162050082c0c,0x2c140089146346318c63]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffff80003ffff,0xff001ffce8f541f0001f])),(BitVec.ofNat 152 (word80 [0x84c120980261113010,0x30588900a8d154a5294a]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xf0000000000003ffff,0xffffe0005f98fe0003e0])),(BitVec.ofNat 152 (word80 [0x701c0e0438221c060,0x40600e104b9898c6318c]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffffffffc0000,0x3280bbffffc00])),(BitVec.ofNat 152 (word80 [0x80201000400020080,0x80801000000021084210]))),(0x0,0x0)]
def g171C : List ColumnInfo := [(1,0,170,0,5),(2,0,169,0,5),(8,0,163,0,5),(32,0,139,0,5),(9,0,162,0,4),(34,0,137,0,4)]
def g171A : List (List Nat) := [[],[81],[16,83],[16,48,80],[48],[48,81],[80,16,49],[80,49]]
def g171D4 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x31825f635474,0x9bd89544426d6215110])
def g171D5 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0xc110204810001,0x882188201141080d176b,0xcc8d018160c02faa3a07,0xbd4940bfa8a81fb40502,0xfea8885f95110beaa221,0x7c54443f280885bd4940])
def g171H5 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0xf100,0x1900008880a20000])
def g171D6 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x3140cc503,0x540a0380ff40fd40fd10])
def g171H6 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [2,0x17a47880020444c0001b,0xd4514000000041c00425,0xc03040050a03987d9cc8])
def g171D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1605f
def g171H7 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x212002a001a,0x431210000000005e401a,0xa92000005a0063202000,0x30000000000000001])
def g171L : Nat → Packing
  | 4 => (3,3,3,0,0,4,0,g171D4)
  | 5 => (10,2,3,0,0,7,0,g171D5)
  | 6 => (3,1,3,0,0,6,0,g171D6)
  | 7 => (1,0,3,0,0,0,0,g171D7)
  | _ => emptyPacking
def g171I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 13 0 8 2 2 g171H5
  | 6 => lookupWord 4 23 3 10 4 2 g171H6
  | 7 => lookupWord 3 31 1 9 2 3 g171H7
  | _ => fun _ => none
def g171 : Forest := ⟨171,7,fun i => g171Y[i]?.getD (0,0),g171C,g171A,g171L,g171I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g171P4_0 : block g171 4 0 3=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g171B4 : block g171 4 0 3=true := g171P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g171P5_0 : block g171 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g171P5_1 : block g171 5 1 9=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g171B5 : block g171 5 0 10=true := (@block_merge g171 5 0 1 9 g171P5_0 g171P5_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g171P6_0 : block g171 6 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g171B6 : block g171 6 0 3=true := g171P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g171P7_0 : block g171 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g171B7 : block g171 7 0 1=true := g171P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g171T : checkedTables g171 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g171 0 0 0 = true)
  · exact (rfl : block g171 1 0 0 = true)
  · exact (rfl : block g171 2 0 0 = true)
  · exact (rfl : block g171 3 0 0 = true)
  · exact g171B4
  · exact g171B5
  · exact g171B6
  · exact g171B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g171G : graphValid g171 (boundsBefore K155) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low171 : Lower true (varsX 171) (graphGoal 171) 8 := lower_forest (g:=g171) (i:=0) (hints:=1048659) (before_sound K155 V155) g171G g171T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K171 := extendKnown K155 8 [(171,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V171 : Known true K171 := extend_ok (m:=171) V155 low171 (by decide +kernel)
def g217Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3fff80ff1fe3ffc07,0xf8ff1ffffc80b60381ff])),(BitVec.ofNat 152 (word80 [0x81010202004000810,0x10020008000000249249]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfc07fff001ffc3fff8,0xffe1fc3c655d1c0e07])),(BitVec.ofNat 152 (word80 [0x50a0a0414428085020,0xa2140410806454492492]))),((BitVec.ofNat 152 (word80 [0x7fffffe0003ffff,0xff0001ffc3be10e07038])),(BitVec.ofNat 152 (word80 [0x60c0c0818030906040,0xc01848200aac10492492]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfff80000000003ffff,0xfffffe00007ba8007fc0])),(BitVec.ofNat 152 (word80 [0x8105050a0941228285,0xa001411013a8924924]))),((BitVec.ofNat 152 (word80 [0xfffffffffffffc0000,0x3066bff8000])),(BitVec.ofNat 152 (word80 [0x206060c0180030306,0x4c0918221022b924924]))),(0x0,0x0)]
def g217C : List ColumnInfo := [(8,0,209,0,5)]
def g217A : List (List Nat) := [[],[118],[67],[67,118],[99,116],[99,116,67],[115,100,67],[115,100]]
def g217D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3f
def g217L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g217D5)
  | _ => emptyPacking
def g217I (_ _ : Nat) : Option (Nat × Nat) := none
def g217 : Forest := ⟨217,5,fun i => g217Y[i]?.getD (0,0),g217C,g217A,g217L,g217I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g217P5_0 : block g217 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g217B5 : block g217 5 0 1=true := g217P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g217T : checkedTables g217 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g217 0 0 0 = true)
  · exact (rfl : block g217 1 0 0 = true)
  · exact (rfl : block g217 2 0 0 = true)
  · exact (rfl : block g217 3 0 0 = true)
  · exact (rfl : block g217 4 0 0 = true)
  · exact g217B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g217G : graphValid g217 (boundsBefore K171) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low217 : Lower true (varsX 217) (graphGoal 217) 6 := lower_forest (g:=g217) (i:=0) (hints:=3) (before_sound K171 V171) g217G g217T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K217 := extendKnown K171 6 [(217,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V217 : Known true K217 := extend_ok (m:=217) V171 low217 (by decide +kernel)
def g218Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0xff007fe1ff0fffc01f,0xf0ff0fffe81d9a00f00f])),(BitVec.ofNat 152 (word80 [0x8a2511444220228940,0xa2022220880d1a555555]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffff8001fff0ffffe0,0xfffff00c76790f00f0])),(BitVec.ofNat 152 (word80 [0x2c06058814020b0182,0xc4140042083631333333]))),((BitVec.ofNat 152 (word80 [0xfffffffe0000ffffff,0xff000fff33b526f00f0f])),(BitVec.ofNat 152 (word80 [0x3008060018440c0203,0x184080303024222222]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffff,0xfffff000134bf8000ff0])),(BitVec.ofNat 152 (word80 [0xc0b058116088b02c14,0xa00b040349c8cccccc]))),((BitVec.ofNat 152 (word80 [0xffffffffffff000000,0xcea8c5fff000])),(BitVec.ofNat 152 (word80 [0xc060018000c03018,0x8c08c084680c0888888]))),(0x0,0x0)]
def g218C : List ColumnInfo := [(8,0,210,0,5)]
def g218A : List (List Nat) := [[],[99,116]]
def g218D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3f
def g218L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g218D5)
  | _ => emptyPacking
def g218I (_ _ : Nat) : Option (Nat × Nat) := none
def g218 : Forest := ⟨218,5,fun i => g218Y[i]?.getD (0,0),g218C,g218A,g218L,g218I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g218P5_0 : block g218 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g218B5 : block g218 5 0 1=true := g218P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g218T : checkedTables g218 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g218 0 0 0 = true)
  · exact (rfl : block g218 1 0 0 = true)
  · exact (rfl : block g218 2 0 0 = true)
  · exact (rfl : block g218 3 0 0 = true)
  · exact (rfl : block g218 4 0 0 = true)
  · exact g218B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g218G : graphValid g218 (boundsBefore K217) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low218 : Lower true (varsX 218) (graphGoal 218) 6 := lower_forest (g:=g218) (i:=0) (hints:=318857280) (before_sound K217 V217) g218G g218T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K218 := extendKnown K217 6 [(218,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V218 : Known true K218 := extend_ok (m:=218) V217 low218 (by decide +kernel)
def g220Y : Array (Bits × Bits) := #[(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xe003ff01ff80ffe003,0xff80ffe03ff495470007])),(BitVec.ofNat 152 (word80 [0x49a84a3429164549a9,0x251a4a458a64950736db]))),((BitVec.ofNat 152 (word80 [0xfffc0001fffffffffc,0xffffc068dbb00e38])),(BitVec.ofNat 152 (word80 [0x81306c583224098130,0x362c0c891348d3801249]))),((BitVec.ofNat 152 (word80 [0xfffffffe0000ffffff,0xffff0000000ff00ef1c0])),(BitVec.ofNat 152 (word80 [0x1c070603c380e01c0,0x38300f0e1c0cf0049249]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffff,0xffffffffff99af6d01ff])),(BitVec.ofNat 152 (word80 [0x120280814040901202,0x40009000001108684924]))),((BitVec.ofNat 152 (word80 [0xffffffffffff000000,0x6754f2fe00])),(BitVec.ofNat 152 (word80 [0x1c0300018000e01c03,0x8040e010202304726db6]))),(0x0,0x0)]
def g220C : List ColumnInfo := [(8,0,212,0,4)]
def g220A : List (List Nat) := [[],[67]]
def g220D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3f
def g220L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g220D4)
  | _ => emptyPacking
def g220I (_ _ : Nat) : Option (Nat × Nat) := none
def g220 : Forest := ⟨220,4,fun i => g220Y[i]?.getD (0,0),g220C,g220A,g220L,g220I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g220P4_0 : block g220 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g220B4 : block g220 4 0 1=true := g220P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g220T : checkedTables g220 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g220 0 0 0 = true)
  · exact (rfl : block g220 1 0 0 = true)
  · exact (rfl : block g220 2 0 0 = true)
  · exact (rfl : block g220 3 0 0 = true)
  · exact g220B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g220G : graphValid g220 (boundsBefore K218) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low220 : Lower true (varsX 220) (graphGoal 220) 5 := lower_forest (g:=g220) (i:=0) (hints:=839280128) (before_sound K218 V218) g220G g220T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K220 := extendKnown K218 5 [(220,[]),(248,[82,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V220 : Known true K220 := extend_ok (m:=220) V218 low220 (by decide +kernel)
def g63Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffffffffffffffffff,0xf9925e5fc09dd40003ff])),(BitVec.ofNat 152 (word80 [0x5040150804a100a400,0xa192524c0019c094a529]))),((BitVec.ofNat 152 (word80 [0x3ffff80000ffffe00,0x5ed82413e2f620ffc00])),(BitVec.ofNat 152 (word80 [0x9800a60036c004c803,0x35a50241380c60318c63]))),((BitVec.ofNat 152 (word80 [0x3fffffffff0000000,0x27363e45dcc19f00000])),(BitVec.ofNat 152 (word80 [0xe0153802a70056f015,0xc26362445d8c18739ce7]))),((BitVec.ofNat 152 (word80 [0x3ffffffffffffffff,0xfa858e25cdf6a400001f])),(BitVec.ofNat 152 (word80 [0x299c053380a6700a6,0x2058c21cde6256b5ad6]))),((BitVec.ofNat 152 (word80 [0xfc0000000000000000,0x245795af66252007fe0])),(BitVec.ofNat 152 (word80 [0x31e0063c00c780138,0x2402912c662134a5294]))),(0x73aa5b8895b2bff8000,(BitVec.ofNat 152 (word80 [0x3e0007c000f8001c0,0x1885b88053038c6318]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g63C : List ColumnInfo := [(0,4,27,32,5),(0,8,54,1,5),(4,0,59,0,5),(8,0,55,0,5)]
def g63A : List (List Nat) := [[],[80,65,50]]
def g63D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xe413f
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
theorem g63G : graphValid g63 (boundsBefore K220) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low63 : Lower true (varsX 63) (graphGoal 63) 7 := lower_forest (g:=g63) (i:=0) (hints:=1049923) (before_sound K220 V220) g63G g63T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K63 := extendKnown K220 7 [(63,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V63 : Known true K63 := extend_ok (m:=63) V220 low63 (by decide +kernel)
def g95Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3ffffffffffffffff,0xff8aba26071cb000f0ff])),(BitVec.ofNat 152 (word80 [0x5805000a8012801480,0x5382a824040881111111]))),((BitVec.ofNat 152 (word80 [0xfc003fffc0003fffc0,0x1f50ab07c5b20000f00])),(BitVec.ofNat 152 (word80 [0x9029a05320db209901,0x99b50ab0645a2bbbbbbb]))),((BitVec.ofNat 152 (word80 [0x3fffffffc00000,0x738dada715000f0000])),(BitVec.ofNat 152 (word80 [0xe0ce0a9c0a9c0ade0a,0xe0538daca71507777777]))),((BitVec.ofNat 152 (word80 [0x3fffffffffffff,0xfc85179417b3d0f0000f])),(BitVec.ofNat 152 (word80 [0x1700ce00ce00ce013,0x5179013b116666666]))),((BitVec.ofNat 152 (word80 [0xffffc0000000000000,0x45f462f96d0f000ff0])),(BitVec.ofNat 152 (word80 [0x1800f000f000f001c,0x401442992504444444]))),(0x0,0x0),(0x33a4dd980e26ffff000,(BitVec.ofNat 152 (word80 [0x20030003000300020,0x284001004268888888]))),(0x0,0x0),(0x0,0x0)]
def g95C : List ColumnInfo := [(4,0,91,0,7)]
def g95A : List (List Nat) := [[]]
def g95D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7f
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
theorem low95 : Lower true (varsX 95) (graphGoal 95) 8 := lower_forest (g:=g95) (i:=0) (hints:=1603) (before_sound K63 V63) g95G g95T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K95 := extendKnown K63 8 [(95,[]),(190,[16,32,48,64,80,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V95 : Known true K95 := extend_ok (m:=95) V63 low95 (by decide +kernel)
def g111Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3ffffffffffffff6,0x703a8aee349000fc003f])),(BitVec.ofNat 152 (word80 [0x5820a821282148142,0x603a88e8048145145145]))),((BitVec.ofNat 152 (word80 [0xffffffc0003fffc00b,0x82dcc6b8712000000fc0])),(BitVec.ofNat 152 (word80 [0x29105310db1099066b,0x82dcc2a03124d34d34d3]))),((BitVec.ofNat 152 (word80 [0x3fffffffc0000009,0xcd1cb9421e203f03f000])),(BitVec.ofNat 152 (word80 [0x4e009c009c00de0b89,0xc41cb8021c00c30c30c3]))),((BitVec.ofNat 152 (word80 [0x3ffffffffffffffa,0x162d5a1393dfc000003f])),(BitVec.ofNat 152 (word80 [0x7004e004e004e00c08,0x1605121313128a28a28a]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffc000000000000009,0x15e285ddcf000003ffc0])),(BitVec.ofNat 152 (word80 [0x2700270027001000,0x1122055dc20b2cb2cb2c]))),((BitVec.ofNat 152 (word80 [4,0xea977125e06ffffc0000])),(BitVec.ofNat 152 (word80 [0x803800380038002004,0x8804104e06c30c30c30]))),(0x0,0x0),(0x0,0x0)]
def g111C : List ColumnInfo := [(2,0,109,0,7)]
def g111A : List (List Nat) := [[],[48]]
def g111D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7f
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
theorem low111 : Lower true (varsX 111) (graphGoal 111) 8 := lower_forest (g:=g111) (i:=0) (hints:=1049939) (before_sound K95 V95) g111G g111T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K111 := extendKnown K95 8 [(111,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V111 : Known true K111 := extend_ok (m:=111) V95 low111 (by decide +kernel)
def g119Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xf8001fffffff00ff57,0x203b85e22c003f00003f])),(BitVec.ofNat 152 (word80 [0x504d41250452161417,0x202984a2285145145145]))),((BitVec.ofNat 152 (word80 [0xffffe0007fffff0029,0x7e83923688000003ffc0])),(BitVec.ofNat 152 (word80 [0x620988362064242629,0x16039026891451451451]))),((BitVec.ofNat 152 (word80 [0xffffffff800000009d,0x8e48e9a5400fc0fc0000])),(BitVec.ofNat 152 (word80 [0x800e0038017838381d,0xc40c1a54030c30c30c3]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffffffa0,0x49c585ccf7f000000fff])),(BitVec.ofNat 152 (word80 [0x9002400980000080,0x48c0014854a28a28a28a]))),((BitVec.ofNat 152 (word80 [0x91,0x75383e5b400000fff000])),(BitVec.ofNat 152 (word80 [0x4e013804e00404080,0x61382e5802cb2cb2cb2c]))),((BitVec.ofNat 152 (word80 [0x4e,0x937660389bffff000000])),(BitVec.ofNat 152 (word80 [0x7001c007000808040,0x93162010830c30c30c30]))),(0x0,0x0),(0x0,0x0)]
def g119C : List ColumnInfo := [(1,0,118,0,7),(2,0,117,0,7),(4,0,115,0,7),(0,32,81,6,6),(32,0,87,0,6),(16,0,103,0,5),(64,0,55,0,5)]
def g119A : List (List Nat) := [[],[33,100]]
def g119D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x4fb7059653
def g119D6 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x1002628,0x401413142f3185b400bf,0x59653fed8153d7d4e53b,0xed8153bd58453be58053])
def g119H6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x10
def g119D7 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x190e,0x6a1474365a981d90ea61,0x47888807f94ffaa7fc53])
def g119H7 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x69000000610000,0x220000000000,0x6300000000e5d000,0x34])
def g119D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x468817f
def g119H8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xc1980000007900
def g119L : Nat → Packing
  | 5 => (1,3,3,0,0,0,0,g119D5)
  | 6 => (6,2,3,0,0,6,0,g119D6)
  | 7 => (3,1,3,0,0,7,0,g119D7)
  | 8 => (1,0,3,0,0,0,0,g119D8)
  | _ => emptyPacking
def g119I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 2 0 4 0 0 g119H6
  | 7 => lookupWord 1 37 0 8 3 1 g119H7
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
theorem low119 : Lower true (varsX 119) (graphGoal 119) 9 := lower_forest (g:=g119) (i:=0) (hints:=1049924) (before_sound K111 V111) g119G g119T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K119 := extendKnown K111 9 [(119,[]),(231,[16,116,101]),(238,[16,32,48,84,100,116])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V119 : Known true K119 := extend_ok (m:=119) V111 low119 (by decide +kernel)
def g123Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffffffc03fffffff72,0x8cb8cc1ec003f000fff])),(BitVec.ofNat 152 (word80 [0x214040808000820032,0x8010c01a85145145145]))),((BitVec.ofNat 152 (word80 [0x1fffffc03fff00ad,0x6cb21b07180000fff000])),(BitVec.ofNat 152 (word80 [0x5880500009004022c,0xca211031934d34d34d3]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffe00000003fffffbd,0x958cd210640fc000003f])),(BitVec.ofNat 152 (word80 [0x4602960b0b05282885,0x158cd20044a28a28a28a]))),((BitVec.ofNat 152 (word80 [0xffffffffffc0000080,0x4b05b7ec53f00003ffc0])),(BitVec.ofNat 152 (word80 [0x880318121206304c80,0x4304a2c4408208208208]))),((BitVec.ofNat 152 (word80 [0x91,0x75782c5bc00000fc0000])),(BitVec.ofNat 152 (word80 [0xf013e01c1c27c07091,0x71582c58c2cb2cb2cb2c]))),((BitVec.ofNat 152 (word80 [0x4e,0x937660389bffff000000])),(BitVec.ofNat 152 (word80 [0x1c00202038008048,0x80720038130c30c30c30]))),(0x0,0x0),(0x0,0x0)]
def g123C : List ColumnInfo := [(8,0,115,0,7)]
def g123A : List (List Nat) := [[],[96]]
def g123D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7f
def g123L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g123D7)
  | _ => emptyPacking
def g123I (_ _ : Nat) : Option (Nat × Nat) := none
def g123 : Forest := ⟨123,7,fun i => g123Y[i]?.getD (0,0),g123C,g123A,g123L,g123I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P7_0 : block g123 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g123B7 : block g123 7 0 1=true := g123P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123T : checkedTables g123 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g123 0 0 0 = true)
  · exact (rfl : block g123 1 0 0 = true)
  · exact (rfl : block g123 2 0 0 = true)
  · exact (rfl : block g123 3 0 0 = true)
  · exact (rfl : block g123 4 0 0 = true)
  · exact (rfl : block g123 5 0 0 = true)
  · exact (rfl : block g123 6 0 0 = true)
  · exact g123B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123G : graphValid g123 (boundsBefore K119) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low123 : Lower true (varsX 123) (graphGoal 123) 8 := lower_forest (g:=g123) (i:=0) (hints:=1048643) (before_sound K119 V119) g123G g123T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K123 := extendKnown K119 8 [(123,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V123 : Known true K123 := extend_ok (m:=123) V119 low123 (by decide +kernel)
def g125Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfffffffffffffffffe,0xc6d9c3930e48000f83ff])),(BitVec.ofNat 152 (word80 [0x502050202000101000,0x4448828206414a5294a5]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xf80007fff003fff801,0x704135ae8db001f07c00])),(BitVec.ofNat 152 (word80 [0x600d6009406805202c,0x700101aa0db0c6318c63]))),((BitVec.ofNat 152 (word80 [0xfffff8000003ffffff,0x79b3191023c83e00001f])),(BitVec.ofNat 152 (word80 [0x8149814d82b0a64149,0x31b31910018a94a5294a]))),((BitVec.ofNat 152 (word80 [0xfffffffffffc000001,0x29e0b4bd9a7c00003e0])),(BitVec.ofNat 152 (word80 [0x18e018e04c0c78271,0x296094989a294a5294a]))),((BitVec.ofNat 152 (word80 [1,0x22eaf07cb68000007c00])),(BitVec.ofNat 152 (word80 [0x5f005f00702f80381,0x2eaf054b20739ce739c]))),(0x9d26ecc07137ffff8000,(BitVec.ofNat 152 (word80 [0x60006000803000400,0x88006400700421084210]))),(0x0,0x0),(0x0,0x0)]
def g125C : List ColumnInfo := [(8,0,117,0,7)]
def g125A : List (List Nat) := [[],[67]]
def g125D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7f
def g125L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g125D7)
  | _ => emptyPacking
def g125I (_ _ : Nat) : Option (Nat × Nat) := none
def g125 : Forest := ⟨125,7,fun i => g125Y[i]?.getD (0,0),g125C,g125A,g125L,g125I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P7_0 : block g125 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g125B7 : block g125 7 0 1=true := g125P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125T : checkedTables g125 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g125 0 0 0 = true)
  · exact (rfl : block g125 1 0 0 = true)
  · exact (rfl : block g125 2 0 0 = true)
  · exact (rfl : block g125 3 0 0 = true)
  · exact (rfl : block g125 4 0 0 = true)
  · exact (rfl : block g125 5 0 0 = true)
  · exact (rfl : block g125 6 0 0 = true)
  · exact g125B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125G : graphValid g125 (boundsBefore K123) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low125 : Lower true (varsX 125) (graphGoal 125) 8 := lower_forest (g:=g125) (i:=0) (hints:=2098435) (before_sound K123 V123) g125G g125T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K125 := extendKnown K123 8 [(125,[]),(189,[82,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V125 : Known true K125 := extend_ok (m:=125) V123 low125 (by decide +kernel)
def g126Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffffffff,0xd925ba38c873c00003ff])),(BitVec.ofNat 152 (word80 [0x28802a40252014805,0x1925322080239294a529]))),((BitVec.ofNat 152 (word80 [0x1ffff00007fffc00,0x3ed8224bb06c800ffc00])),(BitVec.ofNat 152 (word80 [0x14c014c01b60099019,0xba58224b006086318c63]))),((BitVec.ofNat 152 (word80 [0x1ffffffff8000000,0x73623e14bd881f00000])),(BitVec.ofNat 152 (word80 [0x6702a7015380ade0ae,0x63623614ad88e739ce7]))),((BitVec.ofNat 152 (word80 [0x1fffffffffffffff,0xc858e56c4e4f7e00001f])),(BitVec.ofNat 152 (word80 [0xb80338019c00ce0130,0x58c14c4a4c4c6318c6]))),((BitVec.ofNat 152 (word80 [0xffe000000000000000,0x4579a17773c00007fe0])),(BitVec.ofNat 152 (word80 [0xc013c009e004f001c0,0x4028814771c294a5294]))),(0x33aa5dc49781bfff8000,(BitVec.ofNat 152 (word80 [0x1c000e0007000200,0x1801c809501318c6318]))),(0x0,0x0),(0x0,0x0)]
def g126C : List ColumnInfo := [(8,0,118,0,7)]
def g126A : List (List Nat) := [[],[81,66]]
def g126D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7f
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
theorem low126 : Lower true (varsX 126) (graphGoal 126) 8 := lower_forest (g:=g126) (i:=0) (hints:=34694464) (before_sound K125 V125) g126G g126T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K126 := extendKnown K125 8 [(126,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V126 : Known true K126 := extend_ok (m:=126) V125 low126 (by decide +kernel)
def g175Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfc00fffffffffffffe,0xcf0912f74a48000f801f])),(BitVec.ofNat 152 (word80 [0x481610542128429028,0x450812f642414a5294a5]))),((BitVec.ofNat 152 (word80 [0xfffffffe0003fff801,0x701535aec91001f003e0])),(BitVec.ofNat 152 (word80 [0x90a402980db01320cd,0x701130aa4910c6318c63]))),((BitVec.ofNat 152 (word80 [0xfffffffc000001,0x39c4f2135e8000007c00])),(BitVec.ofNat 152 (word80 [0xe13884e109c21bc171,0x3984f2035e04e739ce73]))),((BitVec.ofNat 152 (word80 [0xffffffffffffff,0x428bea0b89e83e00001f])),(BitVec.ofNat 152 (word80 [0x1c027004e009c0181,0x283a00989aa94a5294a]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffff00000000000001,0x22fa117cb687c0007fe0])),(BitVec.ofNat 152 (word80 [0x38007000e00200,0x26a0154808318c6318c]))),(0x0,0x0),(0x9d26ecc07137ffff8000,(BitVec.ofNat 152 (word80 [0x200c0018003000400,0x88044c00300421084210]))),(0x0,0x0)]
def g175C : List ColumnInfo := [(4,0,171,0,8)]
def g175A : List (List Nat) := [[],[48]]
def g175D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7f
def g175L : Nat → Packing
  | 8 => (1,0,1,0,0,0,0,g175D8)
  | _ => emptyPacking
def g175I (_ _ : Nat) : Option (Nat × Nat) := none
def g175 : Forest := ⟨175,8,fun i => g175Y[i]?.getD (0,0),g175C,g175A,g175L,g175I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175P8_0 : block g175 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g175B8 : block g175 8 0 1=true := g175P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175T : checkedTables g175 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g175 0 0 0 = true)
  · exact (rfl : block g175 1 0 0 = true)
  · exact (rfl : block g175 2 0 0 = true)
  · exact (rfl : block g175 3 0 0 = true)
  · exact (rfl : block g175 4 0 0 = true)
  · exact (rfl : block g175 5 0 0 = true)
  · exact (rfl : block g175 6 0 0 = true)
  · exact (rfl : block g175 7 0 0 = true)
  · exact g175B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175G : graphValid g175 (boundsBefore K126) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low175 : Lower true (varsX 175) (graphGoal 175) 9 := lower_forest (g:=g175) (i:=0) (hints:=1049939) (before_sound K126 V126) g175G g175T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K175 := extendKnown K126 9 [(175,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V175 : Known true K175 := extend_ok (m:=175) V126 low175 (by decide +kernel)
def g183Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfff0007ffffff00ff5,0x7a60d23e280001f0001f])),(BitVec.ofNat 152 (word80 [0x42a135092845216141,0x3a60d21428294a5294a5]))),((BitVec.ofNat 152 (word80 [0xffffff8003fffff002,0x96e8554583003e007fe0])),(BitVec.ofNat 152 (word80 [0x4c02601b006424262,0x90605505800842108421]))),((BitVec.ofNat 152 (word80 [0xfffffffffc00000009,0xd8c3e099d100000f8000])),(BitVec.ofNat 152 (word80 [0x17083841c217838381,0xd8c36019d19ce739ce73]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffffffffffffa,0x4ff083ab807c00003ff])),(BitVec.ofNat 152 (word80 [0x980240120098000008,0x49a082a105294a5294a]))),((BitVec.ofNat 152 (word80 [9,0x1710a38776f8000ffc00])),(BitVec.ofNat 152 (word80 [0xe003801c00e0040408,0x7108282226318c6318c]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [4,0xe9177e4005fffff00000])),(BitVec.ofNat 152 (word80 [0xc00600300080804,0x40052040058421084210]))),(0x0,0x0)]
def g183C : List ColumnInfo := [(1,0,182,0,7),(2,0,181,0,7),(4,0,179,0,7),(0,4,147,32,6),(16,0,167,0,6),(32,0,147,0,5),(32,4,147,0,5),(128,0,55,0,5)]
def g183A : List (List Nat) := [[]]
def g183D5 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0xf624c3,0x27db82c7aa4f7715954,0x39f6e0b2a877adc15354,0xa76bb6a7a15eb7054f42])
def g183D6 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x10062086208008c410c,0x4100862283d20e1b1013,0x61201d6422e42d0caba,0xaa9f8f75604b3b2b2010,0xbf58f54bfd8d54bf59,0x353bfd9153fed8153bfd,0x9543bf59543ef55143f7,0x54d43fb54d52fbd4f42f,0xb54f42bed8153bb59742])
def g183H6 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x1d40000000,0x70000000,0xa4042000000000,0xc00000000016000000,0])
def g183D7 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x8512ec33a544b0c,0xa69152e3bad2448ce951,0x2c339644b0d912a25849,0x38291a0b007fd53faa9f,0xf53fea9ff50fdaa5ef42])
def g183H7 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x6c0,0x3b400021003734800000,0,0x201c4000000c,0xd1400000000000000000,0xe0000000000,0x2282400000,0x15c00000000031800012])
def g183D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x681117f
def g183H8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1dae009200045500215b
def g183L : Nat → Packing
  | 5 => (6,3,3,0,0,5,0,g183D5)
  | 6 => (14,2,3,0,0,8,0,g183D6)
  | 7 => (7,1,3,0,0,8,0,g183D7)
  | 8 => (1,0,3,0,0,0,0,g183D8)
  | _ => emptyPacking
def g183I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 53 0 7 3 0 g183H6
  | 7 => lookupWord 3 71 2 8 4 0 g183H7
  | 8 => lookupWord 1 11 0 7 3 0 g183H8
  | _ => fun _ => none
def g183 : Forest := ⟨183,8,fun i => g183Y[i]?.getD (0,0),g183C,g183A,g183L,g183I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183P5_0 : block g183 5 0 6=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g183B5 : block g183 5 0 6=true := g183P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183P6_0 : block g183 6 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183P6_2 : block g183 6 2 12=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g183B6 : block g183 6 0 14=true := (@block_merge g183 6 0 2 12 g183P6_0 g183P6_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183P7_0 : block g183 7 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183P7_2 : block g183 7 2 5=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g183B7 : block g183 7 0 7=true := (@block_merge g183 7 0 2 5 g183P7_0 g183P7_2)
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
theorem low183 : Lower true (varsX 183) (graphGoal 183) 9 := lower_forest (g:=g183) (i:=0) (hints:=1049924) (before_sound K175 V175) g183G g183T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K183 := extendKnown K175 9 [(183,[]),(215,[16,116,101])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V183 : Known true K183 := extend_ok (m:=183) V175 low183 (by decide +kernel)
def g187Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x1ffffff80ffffffc,0xc2c7f445a00001f003ff])),(BitVec.ofNat 152 (word80 [0x11410a081020010400,0xc247a000a5294a5294a5]))),((BitVec.ofNat 152 (word80 [0xffe000fffff01ffe03,0x8c7961a2c0003e0ffc00])),(BitVec.ofNat 152 (word80 [0x1802c00a000400809,0x8c1960808318c6318c63]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffff0000001ffffe,0xd4b05e8c6007c000001f])),(BitVec.ofNat 152 (word80 [0xa20a3052c2c58a50a2,0x14b05e8c4a5294a5294a]))),((BitVec.ofNat 152 (word80 [0xffffffffffffe00002,0x11aab2f300f800007fe0])),(BitVec.ofNat 152 (word80 [0xc40c406304890c6132,0x11a01273084210842108]))),((BitVec.ofNat 152 (word80 [2,0x6954930fdf00000f8000])),(BitVec.ofNat 152 (word80 [0xf80f807c070e0f81c2,0x6144930f4c6318c6318c]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [1,0x37050a181ffffff00000])),(BitVec.ofNat 152 (word80 [0x1000800000100000,0x108421084210]))),(0x0,0x0)]
def g187C : List ColumnInfo := [(16,0,171,0,8),(8,0,179,0,7),(32,0,155,0,7),(1,0,186,0,6),(2,0,185,0,6),(9,0,178,0,5),(10,0,177,0,5),(17,0,170,0,5),(33,0,154,0,5),(34,0,153,0,5),(40,0,147,0,5),(128,0,59,0,5),(25,0,162,0,4),(41,0,146,0,4),(42,0,145,0,4),(136,0,51,0,4),(160,0,27,0,4)]
def g187A : List (List Nat) := [[],[16,83]]
def g187D4 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0xf624c30311ee8c18c4b,0xaa10cf98dcc62585508,0x4fc9b0dba2a308623e13,0x82dcd6544311b08c12e6,0x32a215c1931cb7154110])
def g187D5 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0xc1820,0x1a25004000000000,0,0,0,0x6040030,0x20000000000088188a1c,0x85a1082a047f9f87c9ec,0x799e0745cb715bf6e5a1,0x66d9563d8960d7d5dd71,0x5ad6557d5954d4d51d41,0x4ed354bd2948d1d45d11,0x42d053fcf93cced39ce1,0x36cd533cc930cbd2dcb1,0x2aca527c9924c8d21c81,0x1ec751bc6918c5d13848,0xe4330b4270841b0540f,0x26be1171d49528bf84,0x5c76054aa760c7458750,0xe6b825db50942cee1171,0xd42509bb845c7509432d,0x90571d9150aaf845c762,0x542b3e0d71d8950ae980,0x1c7625422fe1171d8950,0x8df835c762542b360c62,0xd8550caf74d896154333,0xdcf62585508ee8718961,0x5432bdd06258550acd83,0x1896154333dcc6258550,0x8f7875846154399d8b51,0x94550caf74d89515426e,0xe1171d41508be8759151,0x14327dd16354450caf74,0x589511433ae0b7654050,0xceb76dc950143aa59372,0x54050ec963dc950142ba,0xa1d6254050ee37258550,0x1431ddd67558640ab784,0x5d561902ad6107558640,0xad5831d561902b960875,0x58640a7785587519033c,0x58570d46409b980dd151,0x9032ddd16154640ee372,0x585509023be0976d4540,0x8bf845c6658826be1171,0xd4a208bf845d95188237,0xe0d76546209e9809d521,0x8822fe117199520cb964,0x5c3518422f61b7454610,0xea964dc9508423be0970,0x99510ccf82dcd6544333,0x20b7359510caf74dc965,0x44333dcf7259510caf74,0x1c96544333dcc7259510,0xccd825cc654421fe1d65,0x19510c5d655cc654422f,0xe1176d49108df835db52,0x4429b61762d4910ce762,0x5c7524433ad8970d4910,0x8bf845d95244237e0d76,0x54910b598319550442da,0x6086554110ce876dc950,0x442f260c7254110e6b62,0xd49504439a5895254110,0xde072dc55044237e0d76,0x541108ef825d95044297,0x60c6554110a6d8219550,0x4431dd9771541109f387,0x54640443cc5515150110])
def g187H5 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x5005d0,0xc2000000003d03])
def g187D6 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then (word80 [0x37738ec4,0xa86ed71d8950dd8e3b12,0xa1bbdc36254376b86c4a,0x84fd71d8950ddec9b12a,0x1bb59362543f5b86c4a8,0x5ee7618950edec5a92a1,0xdbd895254377b12a4a87,0x6f52549509fae9b0aa13,0xf5cb6154377b16c2a86e,0xc62d8550bdae530aa1bb,0xd8a615437bb0cc2a85bf,0x7458550bbee6b0aa17bd,0xc96154377b12c2a86ec6,0x258550ddec430aa1bd58,0x46154377b16a2a86ef62,0x94550deec328aa1ddd46,0x51542fcb84a2a86ef625,0x4550bf6e0a8aa1fad8b5,0x542fcb8ea0a86ef62d4,0x1509faed288a1af59251,0x1436eb1ca2286ed62944,0x50deac3288a13fdd9511,0x42dfba2a2286bd645445,0xdbac6a88a1bb5895114,0x37dbb2a0287eb7254050,0xdf2c2a80a13f5c665902,0x7fb8acb206f77558640d,0xeceab0c81bd5d5619037,0xa3aac3204ff75586409f,0xaeda8c81bd58751902fc,0xb86a3204ff76546409fa,0xeca8c816fdd1519037ab,0xaa3207eb7254240bf6e,0x2a8481be585509027eb8,0xccaa06bf7459540ddee4,0xb2a813fdc5655027ebb6,0xa2a05bd74d4540e7aa9a,0x8a817e5c3515027fbb2a,0x2a05bf7454540e7aa8a8,0xa81eedd150503dcaa2a0,0xa07eb7254140bf6e2a82,0x813f5c66588377b92cb1,0x4ff7159620ddaeda944,0x1bb59752882f6b8ea510,0x7e970d4a209feeab0c41,0x3f5db51882fcb86a3104,0xff76546209faeca8c416,0xfdd151882f7b92a3106f,0x56154620bdcea90c41bb,0x59521883f2a8a43107eb,0x7254220fd6a4a8441be5,0x8550883f490aa1104fd7,0x199520ddee4b2a413fdc,0x5654827ebb6a2905ed72,0xd4520bf2e1a8a413fdd9,0x51482dfba2a2907eb725,0x4120fd2a4a82419f5975,0x18435eb26a3085f970d4,0x610cfccaa8c219f59551,0x842dfba2a3086bd64546,0x10bf6e0a8c21bedd9508,0x43f5b92a1084fd72d951,0x9fae132a219fd966544,0x36fb9aca884ff7259510,0xddee4b2a21bb1c965442,0x7fb82ca886fb7059510c,0xfecab2a2177dcd65442f,0x7b92ca884fe7619510cf,0xaca32a21775cc65442f6,0xb90ca884fd75d89109fe,0xeab1221bbd89624427f3,0xb6a4884fd76d4910ddec,0x5a92217d5c752442fcb8,0x6a4884fe76549109faec,0xa9221bb58952442fdb82,0xa48867f65d4110beae3a,0x82217e9da50442fcbaca,0x887f25194110df0eca8,0x221ded9550443bc32aa0,0x885fb7454110df6c8a82,0x21be59150443f5b92a08,0x87e87254110df6c4a822,0x1be58950443bda92a088,0x7795254110fe6e2a8221,0xfc1c550443f928aa0887,0xf151541109faeca82219,0xfd95504433e32aa0885e,0xf7254110beee2a82217e,0x5d6404437db2c80886f9,0x6590110fe2a3202217e5,0xd5404437db2a80886f96,0x550110f76c8a0221ee55,0x140443f8a8a80884bf74,0x5875297ee8b0ea19e5db,0x50942e6b98c4a84fb765,0x4050d72c8a80a1b658d5,0x14374b12a0286f16154,0x50de2c2a84813bdc965,0x50336b2ea5105e970d4a,0x20ed6a4a84413bdc9654,0x83b4a92a0906b9645421,0x9bee6b2a213bdc96544,0x26eb98ca884ed7219510]) else (word80 [0x810107041000,0xb430804100081020108,0x20400304003042c162,0x40c10b0402104401018,0x81620400006260090c10,0x50484102000800a050c8,0x4260041410b210a0c10b,0x83080030408304841000,0x21041a8a803a2a008,0x101c107041a204,0x18304083040c10b042,0xc10b04003020a110b070,0x42206881a2041410000,0x20400108142040d85802,0x4403040c103040030208,0x8184040e08200000010,0x8080410004103042010,0x2040030420100201c204,0x8102050410204105040,0x81040000410008002000,0x3a208000100420f4108,0x14181041810204141000,0x3040410000341082c10,0x406100c2210400006101,0x8040030484100041000,0x100078020ae00800004,0x10000000b040000000,0x4002000800322a10c101,0x404080020b041010304,0x8812104108420b041810,0x462098810b0484106,0x4841060484121040001,0x284262a10b0c08040030,0x400000104040020488,0x10421080020488144048,0x81c1e00b80105e0083c1,0x83430405e00817802050,0x7081780205e00817802e,0x4178020fe0083c1780,0x3e0042f8034305e0080e,0x4403c2e00b0b23b203,0x1cb1b319b14310b0f30b,0xb06304b012ffafc2faaf,0x72f3af02ecae92e7ae42,0xe0adf2dbad82d6ad52d3,0xace2caac72c3abe2bcab,0x92b3ab02acaa72a3a9e2,0x9ca99297a94290a8f28d,0xa8c28aa8727fa7a278a7,0x7275a74270a6d269a662,0x62a5f25da5a256a5324f,0xa4c24aa4523ba38234a3,0x122da2c22aa27225a242,0x20a1d213a1020ca09207,0xa021fe9fb1f59f41f29f,0x11ef9ea1e69e51e19de1,0xda9d71d59d21ce9cd1c9,0x9c61c29bf1bb9ba1b69b,0x31b19ae1ac9ab1a79a61,0xa099f19d99819699518f,0x98a18698317f97c17897,0x717597216e96d16b9661,0x6295f15995615495114d,0x94a14894514194013c93,0xb13793613092b1299261,0x2292111f91e11c919117,0x91611491110f90a10890,0x10fd8fa0f48f10ed8ea0,0xe68e30dd8da0d68d50d3,0x8ce0ca8c70c38c00bc8b,0x90b58b20b08af0a98a20,0x9a89709589409088d08b,0x88808487f07d87a07687,0x306f86a0668610578520,0x4c84704183c03683302d,0x82802081d01581000e80,0xb00580035fba2c3a94ff,0x7058752b7ee8b0ea53fd,0xc560d4af6b8ea4a95ed7,0xd49529fae1b0aa56fdd,0x16154a7eb8ec0a97ad54,0x549429fee8b0ea1afdd1,0x61d435e3a2c3a84ff725,0x8750b7ee8b0ea17e5c25,0x1943bd38ea12877971d4,0x250bf2e3a84a1de94750,0x9427eb8ec8a85ef72591,0x50d7ec8aa2a1bbdd3625,0x4376ba6c4a86ef54d895,0xddaa9b12a1bbdc76254]))
def g187H6 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x28588d91d74700,0x24ff180000000,0xa8200063a13bc9d806,0x412000000000b08ca360,0xf9c20e000d3d24e34b0,0x622035000d39,0x78800000000051cb1400,0x62e0003018979114,0x27d0f25073fb09000d42,0x72b69934091b72894513,0x2000e4a000d1e000451f,0x1ac02000d25515000717,0x624f4409ad9800000,0x2410,0x72aa4900058b,0x63812933181600000094,0x652f85200029ef3ec03f,0x7c3464c58064dd48f33,0xd1f13ca4310433650c22,0x6130313000000000a0dc,0xb821a23b37720c2cb10,0x20500082d70a98400091,0x90000000000241800a06,0xb461304c83844010855])
def g187D7 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then (word80 [0x21610186,0x8430411121402030c141,0x16141080c34504203120,0x8308584850600a121228,0x30051624186121030c58,0x9101841010b0c0c30888,0x83105860a1844414309,0x858310242440c416101,0x862c116890a0105a2428,0x203181a108286082031,0x6844080d08f1018b0818,0xb42101883b0101a20b07,0x807082c2601a20f1b807,0x90c0e0202031d807881,0x7e01a20ec02c6884078,0xec03451e3b00d1026020,0x344098078d105e00a18f,0xc0343020820bc028b082,0x300514205c0204101700,0xb102601a184c0343c486,0x1e010786c03441780686,0x3f00d0c101160f00a401,0xe01e204101700b1420b1,0x18028a2c4600a2048580,0x28b14242c01441780289,0x12110c0144098068b108,0x4c0344484300d105e01,0xa184838040b142608220,0x403824062f0080c2600d,0x2031f82088102601a2c4,0x1e1300d107e01a18bc03,0x43082300516284118028,0x82c208c014516104600a,0x28202101e0148601e182,0x38032004104078078e2,0xc3601a20b0d806881058,0x8c0145c42d08309806c0,0x144862700d0c404c0144,0x101300510588c0144432,0x30062c4600a20b101438,0x82c4600a20809802882c,0x4600a24209802890b005,0xe208c0144e92e7ee63e,0x48e2de19e0cdf1de4dd0,0xdbcda8d8dd6bd50d3cd2,0x8d14cf9ce5cc3cafc9bc,0x80c5ec4ac21bf8bddbc2,0xba7b93b78b56b3bb20af,0xeadcac1ab4a92a62a4ea,0x3aa189f69db9b9997975,0x95393190f8ed8cb8a988,0x85e83c81a7ff7e47bb7,0x9277074e7337186f66d4,0x6b969e67565362a6015d,0xf5b659457255052e50c4,0xea4cf4a648446944742c,0x40a3e83c63ab39036734,0x531c2f32ca2af29425d2,0x3b2191f01c01a518a168,0x1461241090e70c50a308,0x105f03d022000ff58752,0xff58352ff59152ff5515,0x2ff58552ff58152ff987,0x50ff58750ffd4650ff94,0x650ffd9150ff59150ffd,0x5150ff55150ffd8950ff,0x58950ffd4950ff54950f,0xfd8550ff98550ff58550,0xff18550ffd4550ff9455,0xff54550ffd4150ff944,0x50ff54450ffd4640ff54,0x640ffd4540ff54540ffd,0x4620ff54620ffd4520ff,0x54520ffd4610ff54610f,0xfd9510ff99510ff59510,0xff19510ffd8910ff5891,0xffd4910ff54910ffd41,0x10ff54110bf59352bf58,0x752bf58352bfd9152fbd,0x4952bfd8552bfd8152bf,0x99542bf59542fb54942b,0xf59350bf58b50dfd4b50,0xdf54b50bf58750bf5965,0xbf58650fed4250bfd91,0x50bfd8950fbd8950fb18,0x950dfd4950df54950bfd,0x8550fed4150bf99450bf,0x58450fe54050bf99640b,0xf59640bf58640fe54240,0xbf99540bf59540ef5514,0xfe54140bf99620bf596,0x20fbd4a20bf58620fb48,0x620fe54220bf99520bf5,0x9520fb54920fe54120bf,0x99610bf59610bf58610f,0xe54210bfd9510bf99510,0xbf59510bf19510bfd891,0xbf58910fe94110fe541,0x10fe90110fe50110bf99,0x410bf59410ded4250bbd,0x8950af59050b758c50bb,0x58850bd98450bd58450b,0xd98640bd58640af59210]) else (word80 [2,0xd1060c5850880f141c12,0x3c31e883063c2842c10,0x8885862c1080c2163422,0x34217044060d1412020,0xb068431e142161421e14]))
def g187H7 (j : Nat) : Nat := if 3 ≤ j then 0 else (if j<1 then (word80 [0xb6ec6ce7,0x53f0001,0x19400000078cd4ce000e,0x6e80000006c400000028,0x7e000000000000100962,0x20b700000000000002ca,0x4e250000000000000000,0,0,0xc6b00000000000,0,0,0,0,0,0x84186d00000008280000,0,0,0x1a7c00088930c0c5953,0x200000002f7942000000,0,0,0x30a26640000000000b,0x59000000000000000010,0x70000000a08000000000,0,0x1c720000000000000000,0,0,0x1ec000000c1680000,0x13a643800000000000,0,0,0xf880000000000,0,0,0,0x1444000000000000000,0,0x3cae000,0x148800297e0000000000,0,0,0,0,0xc250000001438000,0x13800000000000000000,0x72a09b80000000005000,0,0xb15800000000015180,0x1ad7000000000000,0xd1df1780011320000ba,0x4000000a698000000000,0x5da4,0xb4d00000000000000,0x24cba5f00000000,0x74680000000006b,0x78000000000000000000,0,0x8d80000000,0,0x11,0x1d000000000080400000,0,0x5ca8000000000000000,0,0xc070000000,0x63200000000007560000,0,0x1d8600000000006c800,0x4e940012ec0002bb400,0x6568000000c8b,0x8000000000000000016c,0x48340000000000,0x1b3300000000000,0x1e0600000,0,0,0x12a9,0x42b0,0x41ebd500000000,0,0x118e00050,0x78000000000000000000,0x5044000000000,0xc24,0x421e20c000000aa2c,0x21400000000000000000,0x1ca600000000,0,0,0,0x34340000000000,0,0x39f00004aeb7180000,0x40b7b038f200000,0x575c00,0x208c000000,0,0x10102000000000000,0x50001000020000010010,0x30100020310401800201,0x11000002011010000100]) else (if j<2 then (word80 [0xf23800,0x1ae40000598000000000,0,0,0x546a98cee400000000,0x400800000000000,0x6384000000000000000,0,0x16350000000000,0x4cb800120b0000,0x34d80000000003cb20,0x3324000000b5c00,0x29d0000000000000000,0x7ba80000000004d8,0x40014b50000000000349,0,0x10770,0x394000000000000000,0x4d8000000002600000,0x241d41f000000312,0x78290000000000000000,0xf9280038e0,0xcd4f2080038152df0000,0x1a,0x4d00000000000000002b,0x40000000000000000a9,0x70000000000000000000,0xdab80004ea000,0x35d00005620000000000,0,0xe3c00000,0,0xf01000000,0x413,0x83540000000000000000,0,0xa4400002100000008,0x55000000000000000000,0x918babc00186,0x614c0000000000000000,0,0x7a10,0x2832cb0000c,0x9d800256400000000000,0,0x16780021b,0x60000000000000000000,0x39240000000000000,0x22380000000,0x51600000000,0x83d000000000000038,0xd000000000000018fe00,0x71000,0xa218c0000b62000,0x82e0000,0xc1e00000002d60,0x7e0c00000000000000,0xa8f0000000000a3000,0,0,0x10960000000000000,0x4690000,0x54c00000000000018,0xa4000000000000000000,0x2cd530e00,0x187,0x80000007410000000000,0,0x44000000000000,0xb000043440,0,0x978000000000000,0x1bac000000000,0x133c91b1a40000,0,0x43474080000,0x682000000000000,0x2536792000000000000,0,0x1e240000000000000,0x1080000000000000000,0x38bc0000000,0x330800085400000,0x577800000000,0,0xe450001cb6000843,0xa36000b4b0921d1c,0,0x3aa60,0x208a00000000,0x8ba800000000,0xb8aba54000000a66000,0x2d9a0004550278d28000,0x122e0000000,0x4b939880000006280,0x93a00000,0,0x70c800,0,0x10b40000000000,0x1270db40000000006,0xe140006540000000000e,0x8c000000000000000042]) else (word80 [1,0xa2c0000002278003cfb8,0xbba5b800000000000000,0x59bc00063,0x74538000000000861800,0xcc500024bc000000,0x200600000078a8,0x65a0,0x41858,0xc4000000000000000000,0,0x9130000000000000,0x18980006ae7d3982a,0xa6860140000000000,0x3534000d5580000000,0x58400000000,0,0xf4ebaf,0x8b64a1b1730000000000,0x21a80000000000000,0x31960000,0x32ca00000000000,0xaa50000000000000d6,0x90000000000000000000,0x11180005bc000000,0x44961f46bc000,0,0,0,0,0x6c84000000bc4800,0xe170000000000000,0xd440000,0x49cc9c00000000000,8,0x33a6000000026c8d1f00,0xa3a000000000,0x10720000000000000000,0,0x4f694ba00016c8,0x21d0000000000c,0x71000000000000000000,0x10e,0x50000000000000000000,0,0x69e0000000000,0,0x24ec00000041029,0xb4d00a500001ce600000,0xaa6000000,0x1b62c6700000000006d3,0xd2b0001102,0x8a800026e22630000,0x21b80000])))
def g187D8 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [5,0x3a034504f3a03453a03,0x434043e0345108805101,0x12034410204b22014724,0x280510980d0c60602041,0xa034308422014524680d,0x108120144cc5d2b9388d,0x3f198ae4b1e0c03c0f00,0x3fea5fd52fea17fd43fc,0xa1fd50fe287f903fa81f,0xe20fe907f843fa21fc10])
def g187H8 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x35d5fb24c28be7290670,0xd19b74a00038f4d358d5,0x1c9915d40b565510fa69,0x57ae060c9229934fc455,0x8100e960003a43c2bcb8,0x2d590c51c40014575a,0xe8d800341654851dde31,0xd3c4090c518c4f59be38,0xb374740e4001dddd6ec2,0xf7799a06325021940013,0x39d0701b93e0b0002825,0x9840029a80014f000024,0x60974a9f64d3b56658ac,0xb40039bb038d28f3075a,0xd725c0f508ff83703d48,0xf5d9d91f5f47b1200032,0xfc000c048cd7840028de,0x36cd44cec000002c8938,0x89740008eb69f86b8e00,0x149c5699bd81023d030,0x3058001b2400800188,0x8ac0000000000000000,0x3b2e58d124a37,0xc5152cc98a7e885b6a46,0xec71d5e01d7c284845dd,0x3119d908001b60d78d7e,0xc7c0018cbb740009b242,0x28a7dce00000154e1540,0x39a5f72510001c64060,0x3147888902180490400,0x1980614980000802a2,0xa0c60e764489d0010201])
def g187D9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x8200ff
def g187H9 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x19df2f1c0000f,0xa8000179b080057d4718,0x1d23600000,0x2980000000000000,0x35000520000000,0xdc00000008179b64ed00,0x1b0d4000070000002b9f,0xfae41010])
def g187L : Nat → Packing
  | 4 => (6,5,5,0,0,5,0,g187D4)
  | 5 => (83,4,5,0,0,10,0,g187D5)
  | 6 => (238,3,5,0,0,12,0,g187D6)
  | 7 => (121,2,5,0,0,12,0,g187D7)
  | 8 => (14,1,5,0,0,9,0,g187D8)
  | 9 => (1,0,5,0,0,0,0,g187D9)
  | _ => emptyPacking
def g187I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 17 0 7 3 0 g187H5
  | 6 => lookupWord 24 149 5 12 7 1 g187H6
  | 7 => lookupWord 77 1571 4 13 8 1 g187H7
  | 8 => lookupWord 38 191 7 12 7 1 g187H8
  | 9 => lookupWord 6 67 4 9 4 1 g187H9
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
theorem g187P5_0 : block g187 5 0 83=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g187B5 : block g187 5 0 83=true := g187P5_0
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
theorem g187G : graphValid g187 (boundsBefore K183) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low187 : Lower true (varsX 187) (graphGoal 187) 10 := lower_forest (g:=g187) (i:=0) (hints:=1048643) (before_sound K183 V183) g187G g187T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K187 := extendKnown K183 10 [(187,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V187 : Known true K187 := extend_ok (m:=187) V183 low187 (by decide +kernel)
def g207Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffffffffffffffffff,0x451537a70a4801f003ff])),(BitVec.ofNat 152 (word80 [0x481400540128029029,0x401416a2024042108421]))),((BitVec.ofNat 152 (word80 [0xfc00fffe0003fff800,0xf8255c3ea8903e000000])),(BitVec.ofNat 152 (word80 [0x90a612982db05320cc,0xe8255c3e8881ce739ce7]))),((BitVec.ofNat 152 (word80 [0xfffffffc000000,0x39c4d2d31f8000007c00])),(BitVec.ofNat 152 (word80 [0xe13844e089c11bc170,0x1984d2d30f82d6b5ad6b]))),((BitVec.ofNat 152 (word80 [0xfffffffffffffe,0x428bca0bc9efc00f801f])),(BitVec.ofNat 152 (word80 [0x1c007000e001c0180,0x894809498884210842]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffff00000000000000,0x22fa317cb680000fffe0])),(BitVec.ofNat 152 (word80 [0x98013002600200,0x22622104b005294a5294]))),((BitVec.ofNat 152 (word80 [1,0x9d26ecc07137fff00000])),(BitVec.ofNat 152 (word80 [0x200e001c003800400,0x1502a0403036318c6318]))),(0x0,0x0)]
def g207C : List ColumnInfo := [(2,0,205,0,7)]
def g207A : List (List Nat) := [[],[33,118],[48],[48,33,118]]
def g207D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7f
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
theorem g207G : graphValid g207 (boundsBefore K187) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low207 : Lower true (varsX 207) (graphGoal 207) 8 := lower_forest (g:=g207) (i:=0) (hints:=1651) (before_sound K187 V187) g207G g207T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K207 := extendKnown K187 8 [(207,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V207 : Known true K207 := extend_ok (m:=207) V187 low207 (by decide +kernel)
def g219Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xf801fffff83ffffe88,0x4dc1a4940007c00f83ff])),(BitVec.ofNat 152 (word80 [0x501402801080010280,0x48410014210842108421]))),((BitVec.ofNat 152 (word80 [0xfffe003fffc1ff8195,0xf147508800f800007c00])),(BitVec.ofNat 152 (word80 [0x61184b08a004420994,0xf14540816b5ad6b5ad6b]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffc00001fffcd7,0x853047441f0001f0001f])),(BitVec.ofNat 152 (word80 [0x80200c02c108140051,0x85104640c6318c6318c6]))),((BitVec.ofNat 152 (word80 [0xfffffffffffe000021,0x2e5c7a23e0003e007fe0])),(BitVec.ofNat 152 (word80 [0x4010030000181021,0x4103a00842108421084]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x44,0x90bf89b000003fff8000])),(BitVec.ofNat 152 (word80 [0x581602c0211602004,0x10ae81a318c6318c6318]))),((BitVec.ofNat 152 (word80 [0x33a,0x528a034bffffc0000000])),(BitVec.ofNat 152 (word80 [0x6018030042180400a,0x28a010a108421084210]))),(0x0,0x0)]
def g219C : List ColumnInfo := [(8,0,211,0,7),(16,0,203,0,7),(64,0,155,0,7),(128,0,91,0,7),(0,2,73,144,6),(1,0,218,0,6),(2,0,217,0,6)]
def g219A : List (List Nat) := [[],[99,116]]
def g219D7 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x4a8b9,0x1552a2e46f03ee21f510])
def g219D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x344191bf
def g219H8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x28f
def g219L : Nat → Packing
  | 7 => (2,1,3,0,0,5,0,g219D7)
  | 8 => (1,0,3,0,0,0,0,g219D8)
  | _ => emptyPacking
def g219I : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 1 2 0 5 1 0 g219H8
  | _ => fun _ => none
def g219 : Forest := ⟨219,8,fun i => g219Y[i]?.getD (0,0),g219C,g219A,g219L,g219I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P7_0 : block g219 7 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g219B7 : block g219 7 0 2=true := g219P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P8_0 : block g219 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g219B8 : block g219 8 0 1=true := g219P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219T : checkedTables g219 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g219 0 0 0 = true)
  · exact (rfl : block g219 1 0 0 = true)
  · exact (rfl : block g219 2 0 0 = true)
  · exact (rfl : block g219 3 0 0 = true)
  · exact (rfl : block g219 4 0 0 = true)
  · exact (rfl : block g219 5 0 0 = true)
  · exact (rfl : block g219 6 0 0 = true)
  · exact g219B7
  · exact g219B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219G : graphValid g219 (boundsBefore K207) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low219 : Lower true (varsX 219) (graphGoal 219) 9 := lower_forest (g:=g219) (i:=0) (hints:=67) (before_sound K207 V207) g219G g219T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K219 := extendKnown K207 9 [(219,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V219 : Known true K219 := extend_ok (m:=219) V207 low219 (by decide +kernel)
def g221Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffffffffffffffffff,0xf88328178da00f000fff])),(BitVec.ofNat 152 (word80 [0x50028008000080,0x8820014848111111111]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfff8003ffc03ffc0,0x18bdb420ce500000f000])),(BitVec.ofNat 152 (word80 [0x2a45626b1250692905,0x98b5b400ce5777777777]))),((BitVec.ofNat 152 (word80 [0xffffffc00003ffff,0xcc31afca2090f00f000f])),(BitVec.ofNat 152 (word80 [0x4c09804c0360b03209,0x11ad4a201222222222]))),((BitVec.ofNat 152 (word80 [0xfffffffffffc0000,0x3535841ba5f00f000f0])),(BitVec.ofNat 152 (word80 [0x700e00700380c03c0e,0x11108413a5222222222]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xff0000000000000000,0x45c4638772000ffff00])),(BitVec.ofNat 152 (word80 [0x9004802401024010,0x4484220012888888888]))),(0x33a4d3e4015fff000000,(BitVec.ofNat 152 (word80 [0x80e007003802038020,0x322452a0010ccccccccc]))),(0x0,0x0)]
def g221C : List ColumnInfo := [(8,0,213,0,7)]
def g221A : List (List Nat) := [[],[67]]
def g221D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7f
def g221L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g221D7)
  | _ => emptyPacking
def g221I (_ _ : Nat) : Option (Nat × Nat) := none
def g221 : Forest := ⟨221,7,fun i => g221Y[i]?.getD (0,0),g221C,g221A,g221L,g221I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P7_0 : block g221 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g221B7 : block g221 7 0 1=true := g221P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221T : checkedTables g221 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g221 0 0 0 = true)
  · exact (rfl : block g221 1 0 0 = true)
  · exact (rfl : block g221 2 0 0 = true)
  · exact (rfl : block g221 3 0 0 = true)
  · exact (rfl : block g221 4 0 0 = true)
  · exact (rfl : block g221 5 0 0 = true)
  · exact (rfl : block g221 6 0 0 = true)
  · exact g221B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221G : graphValid g221 (boundsBefore K219) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low221 : Lower true (varsX 221) (graphGoal 221) 8 := lower_forest (g:=g221) (i:=0) (hints:=1539) (before_sound K219 V219) g221G g221T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K221 := extendKnown K219 8 [(221,[]),(249,[82,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V221 : Known true K221 := extend_ok (m:=221) V219 low221 (by decide +kernel)
def g222Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfc00ffffffffffffff,0xc525323f0a5801f0001f])),(BitVec.ofNat 152 (word80 [0x481610542128429029,0xc104323e02414a5294a5]))),((BitVec.ofNat 152 (word80 [0xfffffffe0003fff800,0xf8155966a990000003e0])),(BitVec.ofNat 152 (word80 [0x90a442988db11320cc,0xf8155822a992d6b5ad6b]))),((BitVec.ofNat 152 (word80 [0xfffffffc000000,0x39c4d6931e803e007c00])),(BitVec.ofNat 152 (word80 [0xe13804e009c01bc170,0x2984d6030e80c6318c63]))),((BitVec.ofNat 152 (word80 [0xfffffffffffffe,0x428bca0bc9efc00f801f])),(BitVec.ofNat 152 (word80 [0x1c007000e001c0180,0x89c801c88884210842]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffff00000000000000,0x22fa317cb680000fffe0])),(BitVec.ofNat 152 (word80 [0x98013002600200,0x262215c1005294a5294]))),((BitVec.ofNat 152 (word80 [1,0x9d26ecc07137fff00000])),(BitVec.ofNat 152 (word80 [0x200e001c003800400,0x142200c03136318c6318]))),(0x0,0x0)]
def g222C : List ColumnInfo := [(8,0,214,0,7)]
def g222A : List (List Nat) := [[]]
def g222D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7f
def g222L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g222D7)
  | _ => emptyPacking
def g222I (_ _ : Nat) : Option (Nat × Nat) := none
def g222 : Forest := ⟨222,7,fun i => g222Y[i]?.getD (0,0),g222C,g222A,g222L,g222I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g222P7_0 : block g222 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g222B7 : block g222 7 0 1=true := g222P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g222T : checkedTables g222 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g222 0 0 0 = true)
  · exact (rfl : block g222 1 0 0 = true)
  · exact (rfl : block g222 2 0 0 = true)
  · exact (rfl : block g222 3 0 0 = true)
  · exact (rfl : block g222 4 0 0 = true)
  · exact (rfl : block g222 5 0 0 = true)
  · exact (rfl : block g222 6 0 0 = true)
  · exact g222B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g222G : graphValid g222 (boundsBefore K221) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low222 : Lower true (varsX 222) (graphGoal 222) 8 := lower_forest (g:=g222) (i:=0) (hints:=302081600) (before_sound K221 V221) g222G g222T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K222 := extendKnown K221 8 [(222,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V222 : Known true K222 := extend_ok (m:=222) V221 low222 (by decide +kernel)
def g235Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3fffffc1ffff60acd,0x4aee8000007f01fc07f])),(BitVec.ofNat 152 (word80 [0x280280084044060884,0xce80a142850a14285]))),((BitVec.ofNat 152 (word80 [0xfc003ffffffe021d28,0x11d9d70003f800003f80])),(BitVec.ofNat 152 (word80 [0x304b04500208221d28,0x1c941264c993264c993]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffc0001ffffbf0ca,0x83210b01fc000fe0007f])),(BitVec.ofNat 152 (word80 [0x400c0160809009404a,0x12103142850a142850a]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffe0000824f6,0x691ab2fe000000003f80])),(BitVec.ofNat 152 (word80 [0x8090098004e04820c6,0x6012b258b162c58b162c]))),((BitVec.ofNat 152 (word80 [0x93711,0xa287740000000fffc000])),(BitVec.ofNat 152 (word80 [0x2e02e011700803711,0xa28214e1c3870e1c3870]))),((BitVec.ofNat 152 (word80 [0x4c917,0x7e4005fffffff0000000])),(BitVec.ofNat 152 (word80 [0x30030021801008011,0x1e000481020408102040]))),(0x0,0x0)]
def g235C : List ColumnInfo := [(64,0,171,0,8),(1,0,234,0,7),(2,0,233,0,7),(8,0,227,0,7),(32,0,203,0,7),(0,2,73,160,6),(0,32,73,130,6),(0,64,162,9,6),(128,0,107,0,6),(1,64,162,8,5),(2,32,73,128,5),(8,64,162,1,5),(34,0,201,0,5),(128,2,73,32,5),(128,32,73,2,5),(9,0,162,0,4),(9,64,162,0,4),(130,0,73,0,4),(130,32,73,0,4)]
def g235A : List (List Nat) := [[],[81],[48],[48,81]]
def g235D5 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x308bd87,0xd935148327d937354520])
def g235D6 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x201100780402070,0x81e8820306901c1c00,0xa8811004238040307071,0xb142207803c687401e4d,0xc632c144943f1c0c4441,0xb0027fb92c1a8f7b7054,0x950bf6e0a92a1bedc165,0x4827ebb6a2906bf64d45,0x20bf2e1a8a41afd91514,0x82efb9aa2906bf644c52,0xfd6e4a8241fa5495048,0x25ebaec8907695254120])
def g235H6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xcb
def g235D7 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x82012020160104031215,0x141808078e920c022145,0x450600c0a2a107925608,0x42071c34806386900f00,0x60a101101878e1307023,0x1a38e1b811c114305080,0xb0101a345c02080a1b26,0x8234595931c210246c7,0x843601a2c11a2c31a402,0xc83b10d202e4c50c3c11,0x711bf6e2aae829662281,0xdec6f1855712c40cda2a,0x881198520a400ffd8950,0xff58950ff54950ffd452,0xff54520ff4c520bf583,0x51bf58b50ef55150bfd8,0x950dfd4950df54950bf5,0x9520fe54120bfd8910af,0x59351b7d8d51af59350c,0xf55350cf55150afd9120])
def g235H7 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x19c0000000d2800,0x85800804000000091749,0x34b0004022000,0x60c00ab0000000000000,0x60000000000cae6a,0x80800734000000000000,0x207f3000912580001a])
def g235D8 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x8e,0x12a48022071238458121,0xa30a180c3460ce060345,0x92388e04d80720614182,0x489020308a90180d1e40,0x2238d4069c439c8c0481,0x685400ffa8ff547fa63f,0xf50fea87f483fa21bd54])
def g235H8 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x9040,0x204e1200000000001d2,0xb8918a001851812ce81f,0x1d48e3100060d085860,0x11034006130170166160,0xe498c300000000000098,0x301001a02a3e0a40804e])
def g235D9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x41882017f
def g235H9 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0xc100001e,0x80eb200000000000001a,0xfce085e005280192001,0x381800000980c01710a0])
def g235L : Nat → Packing
  | 5 => (2,4,5,0,0,3,0,g235D5)
  | 6 => (14,3,5,0,0,9,0,g235D6)
  | 7 => (21,2,5,0,0,10,0,g235D7)
  | 8 => (8,1,5,0,0,9,0,g235D8)
  | 9 => (1,0,5,0,0,0,0,g235D9)
  | _ => emptyPacking
def g235I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 2 0 5 1 0 g235H6
  | 7 => lookupWord 5 53 2 10 4 2 g235H7
  | 8 => lookupWord 7 43 5 11 5 2 g235H8
  | 9 => lookupWord 3 29 4 9 3 2 g235H9
  | _ => fun _ => none
def g235 : Forest := ⟨235,9,fun i => g235Y[i]?.getD (0,0),g235C,g235A,g235L,g235I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P5_0 : block g235 5 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g235B5 : block g235 5 0 2=true := g235P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P6_0 : block g235 6 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P6_2 : block g235 6 2 12=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g235B6 : block g235 6 0 14=true := (@block_merge g235 6 0 2 12 g235P6_0 g235P6_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P7_0 : block g235 7 0 6=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P7_6 : block g235 7 6 9=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P7_15 : block g235 7 15 6=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g235B7 : block g235 7 0 21=true := (@block_merge g235 7 0 6 15 g235P7_0 (@block_merge g235 7 6 9 6 g235P7_6 g235P7_15))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P8_0 : block g235 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P8_1 : block g235 8 1 7=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g235B8 : block g235 8 0 8=true := (@block_merge g235 8 0 1 7 g235P8_0 g235P8_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P9_0 : block g235 9 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g235B9 : block g235 9 0 1=true := g235P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235T : checkedTables g235 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g235 0 0 0 = true)
  · exact (rfl : block g235 1 0 0 = true)
  · exact (rfl : block g235 2 0 0 = true)
  · exact (rfl : block g235 3 0 0 = true)
  · exact (rfl : block g235 4 0 0 = true)
  · exact g235B5
  · exact g235B6
  · exact g235B7
  · exact g235B8
  · exact g235B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235G : graphValid g235 (boundsBefore K222) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low235 : Lower true (varsX 235) (graphGoal 235) 10 := lower_forest (g:=g235) (i:=0) (hints:=1048659) (before_sound K222 V222) g235G g235T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K235 := extendKnown K222 10 [(235,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V235 : Known true K235 := extend_ok (m:=235) V222 low235 (by decide +kernel)
def g237Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3fffffc1ffff722c9,0xc6ea80003f8001fc07f])),(BitVec.ofNat 152 (word80 [0x280280084044032080,0xc0ca80a142850a14285]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfc003ffffffe03d52c,0x5d8c60000000fe03f80])),(BitVec.ofNat 152 (word80 [0x310b1050080823d12c,0x54840468d1a3468d1a3]))),((BitVec.ofNat 152 (word80 [0xffffc0001ffffad8ca,0x93211a01fc07f000007f])),(BitVec.ofNat 152 (word80 [0x400c0160809000504a,0x912012142850a142850a]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffe0000804f6,0x691ab3fe000000003f80])),(BitVec.ofNat 152 (word80 [0x8050058002e04804c2,0x2812b33870e1c3870e1c]))),((BitVec.ofNat 152 (word80 [0x91711,0xa28774000007ffffc000])),(BitVec.ofNat 152 (word80 [0x26026011300880611,0x228304a142850a142850]))),((BitVec.ofNat 152 (word80 [0x4e917,0x7e4005fffff800000000])),(BitVec.ofNat 152 (word80 [0x38038021c01048915,0x424004c183060c183060]))),(0x0,0x0)]
def g237C : List ColumnInfo := [(1,0,236,0,7),(4,0,233,0,7),(8,0,229,0,7),(32,0,205,0,7),(64,0,173,0,7),(128,0,109,0,7),(0,4,137,96,6),(0,32,73,132,6),(4,32,73,128,5),(36,0,201,0,5),(64,4,137,32,5),(68,0,169,0,5),(128,32,73,4,5),(160,0,77,0,5),(5,0,232,0,4),(9,0,228,0,4),(12,0,225,0,4),(33,0,204,0,4),(65,0,172,0,4),(72,0,165,0,4),(96,0,137,0,4),(129,0,108,0,4),(132,0,73,0,4),(132,32,73,0,4),(136,0,101,0,4)]
def g237A : List (List Nat) := [[],[82,118],[48],[48,82,118]]
def g237D5 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x8185b54f033a,0x1cb70595408fb805d954,0x483ca5515250120dab75,0x509404836a5d54250120])
def g237D6 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x188100000081,0x5448200481c0040650,0x59410000204003001001,0x41c0068c042c00408102,0x4012040000410318110,0xa004b85aac95ea852a69,0x2e9044a18fe783a9c8d6,0x6832978b654269087634,0x168a846200e85826004f,0xd72d8154bdee4b02a93f,0x5cb655027fb92caa06ef,0x7259540dd8e4b2a81bed,0xc165502f7b92caa05fb7,0x59540b7ee4aa281eedc,0x1545027ebaec4a06bd54,0xd8940e7aa8a9281afd95,0x425035eb2a84a04fd75d,0x91209feeab22413fdd95,0x44827ebb2a8906bd6455,0x120b7ee8b0a419fd9551,0x482efb9aa2905fb75501,0x20bf2eaa0241ee551404,0x83f4a9280904fd72d951,0x9faebb12217edc15244,0x277b92caa07a94250120])
def g237H6 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x500019300002c400c40,0x4810e8803020011801])
def g237D7 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x14220,0xca92448042a4912510a,0x11141d0a318687089921,0xe8843048226487c04828,0x5090078840706490108c,0x8e0062c2401618380243,0x6187051038606071454,0x4070c94182024872a48,0x3864b101818008a258e3,0xc1149600e1c303039511,0x21c992148a00a1c30506,0x9308f1c793241c305480,0xc092487c6009210c0c14,0x8143850e1418a1c2e2c0,0x1e28a16124027c0ec1ce,0x37a6cccf58daeb592ab9,0x49a7f482828df1872a04,0x9c780ab0f614814800ff,0xd8154ff58154ff59540f,0xf58d40ff54d40ff58940,0xff54940ff59120ff5512,0xff58520ff54520ff505,0x20ff4c520ff54910bfd8,0x154bfd9540bf59540ef5,0x5140bfd8940ef50940bf,0xd9120bf59120fe50120b,0xfd9510bfd8910b7d8d51])
def g237H7 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x145245b468c,0x24000003e1b855918000,0xc19871008c7400000102,0xdc46c480000000000000,0x2400000816062644,0x2c37030000c3c00000,0x465479c1f01135cc06c,0x20000828000003559529,0x61c000000000002a4bc6,0xc001531c4365d85c0000,0x1f1983a00fb08002,0x48000000000000347ec4,0xfd4610c1180044240000])
def g237D8 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x1628212a330,0x42038a02971658a08c81,0x8b1e280930a147484963,0x8a100a24718f9648e108,0x26506222300a1e40fc6,0x62a0d830007f553faa3f,0xd41fe98ff503fa41fd10])
def g237H8 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x28b265cc00008d00000,0x6352ea124caae305e,0x85000000920e33c00000,0x12f0c2c80004640010,0xa62c810007ec30605c00,0x6d8b242169772390d03a,0x80968000e1dc46d9d220,0x3c006a5b498a041009b2,0x650c008504a0441a6282])
def g237D9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xa4188201bf
def g237H9 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x24400000000021,0x600000000000000,0x10c000000000011a1c00,0x7340000340000,0x14800000030c0,2,0x60026400701149400002])
def g237L : Nat → Packing
  | 5 => (5,4,5,0,0,6,0,g237D5)
  | 6 => (33,3,5,0,0,9,0,g237D6)
  | 7 => (26,2,5,0,0,11,0,g237D7)
  | 8 => (7,1,5,0,0,9,0,g237D8)
  | 9 => (1,0,5,0,0,0,0,g237D9)
  | _ => emptyPacking
def g237I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 2 17 1 9 3 2 g237H6
  | 7 => lookupWord 11 79 6 12 6 2 g237H7
  | 8 => lookupWord 11 59 6 11 5 2 g237H8
  | 9 => lookupWord 3 59 1 9 3 2 g237H9
  | _ => fun _ => none
def g237 : Forest := ⟨237,9,fun i => g237Y[i]?.getD (0,0),g237C,g237A,g237L,g237I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P5_0 : block g237 5 0 5=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g237B5 : block g237 5 0 5=true := g237P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P6_0 : block g237 6 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P6_2 : block g237 6 2 31=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g237B6 : block g237 6 0 33=true := (@block_merge g237 6 0 2 31 g237P6_0 g237P6_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P7_0 : block g237 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P7_1 : block g237 7 1 11=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P7_12 : block g237 7 12 14=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g237B7 : block g237 7 0 26=true := (@block_merge g237 7 0 1 25 g237P7_0 (@block_merge g237 7 1 11 14 g237P7_1 g237P7_12))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P8_0 : block g237 8 0 7=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g237B8 : block g237 8 0 7=true := g237P8_0
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
  · exact g237B5
  · exact g237B6
  · exact g237B7
  · exact g237B8
  · exact g237B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237G : graphValid g237 (boundsBefore K235) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low237 : Lower true (varsX 237) (graphGoal 237) 10 := lower_forest (g:=g237) (i:=0) (hints:=2098435) (before_sound K235 V235) g237G g237T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K237 := extendKnown K235 10 [(237,[]),(245,[67]),(246,[16,115,67,101])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V237 : Known true K237 := extend_ok (m:=237) V235 low237 (by decide +kernel)
def g243Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x1fffff83ffc1f432e,0x60693a40000fc0fc003f])),(BitVec.ofNat 152 (word80 [0x94028010808840030e,0x600132030c30c30c30c3]))),((BitVec.ofNat 152 (word80 [0xfe003fffffffe0205a,0xa626f48003f00003ffc0])),(BitVec.ofNat 152 (word80 [0x18230420041002200a,0x424f409249249249249]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffc0003fffffb48c,0x91d84280fc003f000fff])),(BitVec.ofNat 152 (word80 [0x200401410120001080,0x81580084104104104104]))),((BitVec.ofNat 152 (word80 [0xffffffffc000008945,0x6956a9bf00000003f000])),(BitVec.ofNat 152 (word80 [0xc048098009c0848944,0x69520896596596596596]))),((BitVec.ofNat 152 (word80 [0x9171,0x18b1dc4000003ffc0000])),(BitVec.ofNat 152 (word80 [0x1702e022e01088071,0x18a0cc78e38e38e38e38]))),((BitVec.ofNat 152 (word80 [0x4e93,0x4f80057fffffc0000000])),(BitVec.ofNat 152 (word80 [0x18030043002104411,0x2800160820820820820]))),(0x0,0x0)]
def g243C : List ColumnInfo := [(1,0,242,0,7),(2,0,241,0,7),(16,0,227,0,7),(32,0,211,0,7),(64,0,179,0,7),(128,0,115,0,7),(0,32,81,130,6),(0,64,162,17,6),(1,64,162,16,5),(2,32,81,128,5),(16,64,162,1,5),(33,0,210,0,5),(34,0,209,0,5),(80,0,163,0,5),(96,0,147,0,5),(128,32,81,2,5),(160,0,83,0,5),(3,0,240,0,4),(17,0,162,0,4),(17,64,162,0,4),(18,0,225,0,4),(81,0,162,0,4),(97,0,146,0,4),(98,0,145,0,4),(129,0,114,0,4),(130,0,81,0,4),(130,32,81,0,4),(162,0,81,0,4)]
def g243A : List (List Nat) := [[],[16,116,101]]
def g243D5 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x20,0x40b6785b54603d2e0152,0x4c950c9f64dcd514835a,0x54b7154120e696254950,0x443d85492154110e6965,0x54920443d85495148110])
def g243D6 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x180c21305904c2060308,0x4c1050401a04643e8e84,0x40001513080130710100,0x180c2070408007060,0x403104c14213044c1130,0x5086811a13084c900430,0x20408113110a918c202c,0x7c01a101f082c605130f,0x1b8c604c41a130aa6a62,0x829b25e9424a8f216842,0xa7d1ee781d2731c6701,0xaa6518e5a15251136481,0x123f0de340c22b0961c0,0x5a0f0160027eb8ec0a97,0xcf7054932f9ae0a92653,0xf5c762542fdb82c4a877,0xb70549509fae5b0aa19f,0x54b615439eaa2c2a876d,0x52485509fee2b2a41bed,0xc1654835fb22a6907eb7,0x54920bbee6a8a41db54,0x9514835fb2262905fb71,0x541209faebb12213fdd5,0x624427fbb2a4884fd765,0x4910ddac4a92217edc95,0x4437db12a0886f96254,0x110ef2a4a8221fc48550,0x442fcbaa40886fb65481,0x10df2ca90221fa549204,0x43f8a8a408874d524c95,0x97aebb2241da5495048,0x39caa2a08870d5454932])
def g243H6 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0xe20000000000,0xe100000000000000,0x59661400000000000000,0xf5000000d000730000fb])
def g243D7 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x526118484c31,0xa1c306612130cc98223d,0x1a118d18265048840307,0x11199242441818328488,0x8848886344c887143030,0x24c548a04c21e2870908,0x4c31e3060604c1314c47,0x4e3e02218d9308d1308d,0x870808d1818c060604a9,0x31a325261988c9498854,0x305064c88c508c10c141,0x9526413361133411b304,0x5208343152299263824c,0x74b0ca8654d046898583,0x20a34218c38c793172e3,0xc3003c21a50c868d7142,0x103fe7c6f05d33766b6c,0xc984ad9560a013625845,0x7e0ee9bb3165349c925,0x1ea2f85188f0f6164180,0xffd8152ff58152ff54,0xd42ff58950ff58550ff4,0x8550ff54d20ff54520ff,0x4c520ff58910ff54910b,0xfd8152f7d8132bfd8132,0xbfd8950df54950f7cc95,0xf74c950bfd8550bf595,0x20fb54920fe54120bfd8,0x910bf58910f7cc910f74,0xc910fe54110fe48110e7,0x95332e795132e755132f,0x354932cf55150afd9120])
def g243H7 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x24f72084c0048981704,0xbc2515001208878a2f30,0x47746000f40000000800,0xc3781800882d23c8f9,0x973e26a232a4d3883ac0,0xa49b4693365c94001c7a,0x5157a3749400416f0f0,0x180074792e002d0800c1,0x61460b90701120e2007])
def g243D8 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x38a2481218233,0xe428508895734810a920,0xc224f1d80248a18cf20,0x526584a5842248892cf1,0x951849638531d10658a4,0x22324024a9038026c60c,0xa92009a1b9192ba51210,0xea60240a82a007f50ffa,0xa5fd42fe997f543fa81f,0xd30fe907f443be65dd32])
def g243H8 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x1d00000000036b,0xca440f23800813248,0xe0323c000000012,0x4c003960015280680000,0x62364800001c60004c2,0xd32001c31,0x9a0000000000039c003a,0x3000196c7400261001c7,0x5170000000059ff90,0x1c86c00000,0x410000000000000,0xc174a,0x8e00042800000000000,0x5c1140e00000560000f,0x60000000011640000010,0x80034a8008880010de9e,0x1734c8000682000000,0xbb6e30000000040605])
def g243D9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xa4188201bf
def g243H9 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x44,0xcca0000284d2b6500000,0,0x43000ce000000320006,0xa00000000000330000aa,0x8800e300000000055000,0xf10000000000000000,0,0x65c01c40000001e8d4])
def g243L : Nat → Packing
  | 5 => (7,4,5,0,0,6,0,g243D5)
  | 6 => (38,3,5,0,0,10,0,g243D6)
  | 7 => (34,2,5,0,0,11,0,g243D7)
  | 8 => (11,1,5,0,0,9,0,g243D8)
  | 9 => (1,0,5,0,0,0,0,g243D9)
  | _ => emptyPacking
def g243I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 2 37 0 8 3 1 g243H6
  | 7 => lookupWord 11 59 6 11 6 1 g243H7
  | 8 => lookupWord 13 131 3 11 6 1 g243H8
  | 9 => lookupWord 4 71 2 9 4 1 g243H9
  | _ => fun _ => none
def g243 : Forest := ⟨243,9,fun i => g243Y[i]?.getD (0,0),g243C,g243A,g243L,g243I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P5_0 : block g243 5 0 7=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g243B5 : block g243 5 0 7=true := g243P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P6_0 : block g243 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P6_1 : block g243 6 1 4=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P6_5 : block g243 6 5 33=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g243B6 : block g243 6 0 38=true := (@block_merge g243 6 0 1 37 g243P6_0 (@block_merge g243 6 1 4 33 g243P6_1 g243P6_5))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P7_0 : block g243 7 0 6=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P7_6 : block g243 7 6 17=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P7_23 : block g243 7 23 11=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g243B7 : block g243 7 0 34=true := (@block_merge g243 7 0 6 28 g243P7_0 (@block_merge g243 7 6 17 11 g243P7_6 g243P7_23))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P8_0 : block g243 8 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P8_2 : block g243 8 2 9=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g243B8 : block g243 8 0 11=true := (@block_merge g243 8 0 2 9 g243P8_0 g243P8_2)
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
theorem g243G : graphValid g243 (boundsBefore K237) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low243 : Lower true (varsX 243) (graphGoal 243) 10 := lower_forest (g:=g243) (i:=0) (hints:=1048644) (before_sound K237 V237) g243G g243T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K243 := extendKnown K237 10 [(243,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V243 : Known true K243 := extend_ok (m:=243) V237 low243 (by decide +kernel)
def g250Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffffffffffff7,0x33e9103d880001f003ff])),(BitVec.ofNat 152 (word80 [0x40a102840400202003,0x2221100d08294a5294a5]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfff0003ffe01fff00a,0x824a9d4ea6003e007c00])),(BitVec.ofNat 152 (word80 [0xac06b0128340a416a,0x804a9d0ca018c6318c63]))),((BitVec.ofNat 152 (word80 [0xffffffc00001fffffb,0xccce82a05807c00f801f])),(BitVec.ofNat 152 (word80 [0x13004c01b0580c8248,0x8cce8020401084210842]))),((BitVec.ofNat 152 (word80 [0xfffffffffffe000008,0x14f6681bb1f8000003e0])),(BitVec.ofNat 152 (word80 [0x9c027009c0604f0388,0x14c62812b15294a5294a]))),((BitVec.ofNat 152 (word80 [9,0x1711a3877600000ffc00])),(BitVec.ofNat 152 (word80 [0xe00b802e0081700401,0x1311228316e739ce739c]))),((BitVec.ofNat 152 (word80 [4,0xe9177e4005fffff00000])),(BitVec.ofNat 152 (word80 [0xc00300101800804,0x41104240048421084210]))),(0x0,0x0)]
def g250C : List ColumnInfo := [(8,0,242,0,7),(16,0,234,0,7),(0,64,162,24,6),(32,0,218,0,6),(64,0,186,0,6),(2,0,248,0,5),(96,0,154,0,5),(128,0,122,0,5),(18,0,232,0,4),(160,0,90,0,4)]
def g250A : List (List Nat) := [[]]
def g250D5 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x183b,0xe35cafb299a069e54d8d,0x50d3aa9b1aa1735c8635,0x432eb2ea7185d970d4e3,0xeb6a6a846137dcd654c,0x31fb2aa8987595354130])
def g250D6 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x608e,0x8e0811823c610018200,0x60860800001820003823,0x8200608a3e21e208b88e,0x18e4043e214b24114844,0x9ece46f34998c05a2b9,0x50a24b241147e391b0c0,0x481e0902400bf58353bf,0x59650ef95250ef55250b,0xf58e50ef95150ef55150,0xbfd8d50f7d8d50f718d5,0xdfd4d50df54d50bf596,0x30ef55230f7d4e30fe54,0x230bfd9530bf59530ef5,0x5130f754d30fe94130fe,0x54130ded4250b7d8d50b,0x758c50bb58850bd58450])
def g250H6 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0xc508a,0x43d5195c00020e10028])
def g250D7 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0xa2844c718a68,0x45229482845231c83142,0x251c8219cb088e329050,0x8a473c22628a72c22614,0x47844c2912284459d46d,0xeece529f0ba3e0f803fe,0xa7fd53ffa87f943faa1f,0xc50ff187f4c37ca9bd54])
def g250H7 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x7480001f0668e309,0x6f0021c960099b440095,0x270016fe83b78a280c83,0x1495540b2803473a3080,0x72000000000001a0510])
def g250D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3420117f
def g250H8 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x20c000003140000,0x1d9624001,0x80001e40000000002dc,0x3c790000002])
def g250L : Nat → Packing
  | 5 => (9,3,4,0,0,6,0,g250D5)
  | 6 => (27,2,4,0,0,9,0,g250D6)
  | 7 => (10,1,4,0,0,9,0,g250D7)
  | 8 => (1,0,4,0,0,0,0,g250D8)
  | _ => emptyPacking
def g250I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 2 13 3 8 4 0 g250H6
  | 7 => lookupWord 6 41 4 9 5 0 g250H7
  | 8 => lookupWord 2 37 1 8 4 0 g250H8
  | _ => fun _ => none
def g250 : Forest := ⟨250,8,fun i => g250Y[i]?.getD (0,0),g250C,g250A,g250L,g250I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g250P5_0 : block g250 5 0 9=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g250B5 : block g250 5 0 9=true := g250P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g250P6_0 : block g250 6 0 5=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g250P6_5 : block g250 6 5 22=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g250B6 : block g250 6 0 27=true := (@block_merge g250 6 0 5 22 g250P6_0 g250P6_5)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g250P7_0 : block g250 7 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g250P7_2 : block g250 7 2 8=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g250B7 : block g250 7 0 10=true := (@block_merge g250 7 0 2 8 g250P7_0 g250P7_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g250P8_0 : block g250 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g250B8 : block g250 8 0 1=true := g250P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g250T : checkedTables g250 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g250 0 0 0 = true)
  · exact (rfl : block g250 1 0 0 = true)
  · exact (rfl : block g250 2 0 0 = true)
  · exact (rfl : block g250 3 0 0 = true)
  · exact (rfl : block g250 4 0 0 = true)
  · exact g250B5
  · exact g250B6
  · exact g250B7
  · exact g250B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g250G : graphValid g250 (boundsBefore K243) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low250 : Lower true (varsX 250) (graphGoal 250) 9 := lower_forest (g:=g250) (i:=0) (hints:=319905856) (before_sound K243 V243) g250G g250T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K250 := extendKnown K243 9 [(250,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V250 : Known true K250 := extend_ok (m:=250) V243 low250 (by decide +kernel)
def g252Y : Array (Bits × Bits) := #[(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x3fffffffffffffffe,0xc93d3b130c58000003ff])),(BitVec.ofNat 152 (word80 [0x581440548129029028,0xc9143a1204525294a529]))),((BitVec.ofNat 152 (word80 [0xfc00fffe0003fff801,0xf605502e2d9001f07c00])),(BitVec.ofNat 152 (word80 [0x90a602980db01320cd,0xf20550220d80c6318c63]))),((BitVec.ofNat 152 (word80 [0xfffffffc000000,0x39c4d6d38a803e0f8000])),(BitVec.ofNat 152 (word80 [0xe13804e009c01bc170,0x3144d6138880c6318c63]))),((BitVec.ofNat 152 (word80 [0xfffffffffffffe,0x428bca0bd9efc000001f])),(BitVec.ofNat 152 (word80 [0x1c017002e005c0180,0x289c009d9898c6318c6]))),((BitVec.ofNat 152 (word80 [0xffff00000000000000,0x22fa317cb680000fffe0])),(BitVec.ofNat 152 (word80 [0x98013002600200,0xaa014c3205294a5294]))),((BitVec.ofNat 152 (word80 [1,0x9d26ecc07137fff00000])),(BitVec.ofNat 152 (word80 [0x200e001c003800400,0xc2228c02036318c6318]))),(0x0,0x0)]
def g252C : List ColumnInfo := [(8,0,244,0,7)]
def g252A : List (List Nat) := [[],[67],[82,118],[82,67,118]]
def g252D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7f
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
theorem g252G : graphValid g252 (boundsBefore K250) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low252 : Lower true (varsX 252) (graphGoal 252) 8 := lower_forest (g:=g252) (i:=0) (hints:=841377024) (before_sound K250 V250) g252G g252T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K252 := extendKnown K250 8 [(252,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V252 : Known true K252 := extend_ok (m:=252) V250 low252 (by decide +kernel)
def g127Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfee452b8e041c6843b,0xe620800003f800003fff])),(BitVec.ofNat 152 (word80 [0x282052284040468019,0xa2208912244891224489]))),((BitVec.ofNat 152 (word80 [0xb85b250ba3110715,0x1b99800000000fffc000])),(BitVec.ofNat 152 (word80 [0xccb81b2409a1010415,0x1381a3468d1a3468d1a3]))),((BitVec.ofNat 152 (word80 [0x172b56edcfa0714a1,0x480001fc07f0000000])),(BitVec.ofNat 152 (word80 [0x7072352eccca0304a1,0x48070e1c3870e1c387]))),((BitVec.ofNat 152 (word80 [0xff5b28f8af85484d98,0x49c00fe00000000007f])),(BitVec.ofNat 152 (word80 [0x815a28d0ae81084d80,0x49c162c58b162c58b16]))),((BitVec.ofNat 152 (word80 [0x10096918e422928e6,0xe8db7f000000001fff80])),(BitVec.ofNat 152 (word80 [0x100849186022808a2,0x485a142850a142850a14]))),((BitVec.ofNat 152 (word80 [0x122c951708cbc338a,0x917480000007ffe00000])),(BitVec.ofNat 152 (word80 [0x100c0513004bc330a,0x803458b162c58b162c58]))),((BitVec.ofNat 152 (word80 [0x9d24061534aaea41,0x3277ffffff800000000])),(BitVec.ofNat 152 (word80 [0x8500001134802240,0x10160c183060c183060]))),(0x0,0x0),(0x0,0x0)]
def g127C : List ColumnInfo := [(8,0,119,0,9),(1,0,126,0,8),(2,0,125,0,8),(4,0,123,0,8),(16,0,111,0,8),(32,0,95,0,8),(0,2,77,48,7),(0,32,89,6,7),(9,0,118,0,7),(10,0,117,0,7),(12,0,115,0,7),(18,0,109,0,7),(36,0,91,0,7),(64,0,63,0,7),(0,4,27,96,6),(0,8,54,65,6),(2,32,89,4,6),(4,2,73,48,6),(4,32,89,2,6),(16,2,77,32,6),(16,32,73,6,6),(20,0,107,0,6),(34,0,93,0,6),(40,0,87,0,6),(1,8,54,64,5),(3,0,124,0,5),(5,0,122,0,5),(6,0,89,0,5),(6,32,89,0,5),(17,0,110,0,5),(24,0,103,0,5),(33,0,94,0,5),(48,0,77,0,5),(48,2,77,0,5),(64,4,27,32,5),(64,8,54,1,5),(68,0,59,0,5),(25,0,102,0,4),(65,0,54,0,4),(65,8,54,0,4),(96,4,27,0,4)]
def g127A : List (List Nat) := [[]]
def g127D5 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x30927ea5761d9,0x5450f499766407655143])
def g127D6 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0xd081d081,0x3420742040e14100000,0xb081b08100007740,0x81d05844042030d0400,0x638408c343c250800781,0xb0542813a9546a29047f,0x3e1e4ec73381a0c05d2d,0x1348a381a8b454180582,0xb4f4c0ecb2287c9f7,0x69d95450ef3720bb2a8a,0x1f275d87655143bc6c90,0xecaa287799901d95450e,0x3bb29c1ae1b14f3e4d80,0xd8921ae7c930bb9ac15c,0xf9259773582baf22aa6e,0x6b0567e5181dcd60ae7c,0x92ebb9ac1e9b90591435,0x8333d0eaa286b066721d,0x5450d60ccfc26e6b8ac1,0x95f85dcd21583b3720bb,0x286a05e6e417650d40f4,0xcb2706b02811dd94e0d7,0x64827b130a1ac0907a65,0x91435812086fcc2ec3b2,0x878d9766007650ed3320,0x3b2c8a1ce62614358140])
def g127H6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3e4
def g127D7 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then (word80 [0x88e45612,0x4615048e45104e083c,0x1000000018507020b0,0xb0220438806078016070,0x10340216004e1016841,0x600162b0c261820f0446,0xb0816182c4610417618,0x5811304260f042605858,0x11021c413820a0686088,0x810303c00813440a8408,0x180210181c0054504002,0x70802089c11300021387,0x780186010e8204008418,0x2007430a820013840104,0x4e08001068426041e000,0x81e000800f03c2010608,0x404106821a11050d06,0x1a0c37081708301e0c8e,0x4210604239080018103,0x1c2c06104c20609a1f08,0x9a250f844d1286230f04,0x131284472109c343f149,0x627101f0de2e0c443a0b,0x223103b86c088c40783,0xc2c088e88270800260f0,0x82611e183d8117080a1d,0x4270e8826c08750e82a,0xc1e0c0546112138101,0x144c1e0c5183a283c1a3,0xea2fa29a23a1da0e9ff9,0xe79bd9939729489038fd,0x8ee8d68ac88287385b85,0x584f84984383d82e81f7,0xf57ef7d77bf7a778f777,0x76875074173272371470,0x56ed6d56bd6a569666c6,0x5d64e63f63062a6125fa,0x5eb5d35cd5b55a658e57,0xf5705585375285195014,0xe04d14b94aa49b49547d,0x46e45643e43842041a40,0xb4053ff3f03e13c93ba3,0xab39337234831e2f42d3,0x2b22912792612402161e,0xc1c219818915f1351020,0xf30c908d07504200f000,0x9fd80dc964bdf835c164,0xbdd829d943bdf825d943,0xbdd821d943f9f8259143,0xf9d8259143f9f8059143,0xf9d8059143f9f7655143,0xf9e7655143f9d7655143,0xf9c7655143bdd86dc943,0xddd76dc943f9d64dc943,0xf9d54dc143f9d545c143,0x9ff805d3629fd80dd162,0xf9d6450d629fd84dc162,0xddd43dc1629ff805d942,0xbef8058942bed80d8921,0xbf78155360f9d5450f60,0xddd435cb60bef825d560,0xbef8259560efb8059160,0xbfb8059160dbf7455160,0xbf78155160ddd85dcd60,0xddd65dcd60ddd84dcd60,0xddd64dcd60ddd54dcd60,0xddd82dcd60ddd81dcd60,0xddd75dcd60bdd84dcd60,0xddd74dcd60edd64dcd60,0xf9d5450d609fd84dc960,0xddf735c960ddf7358960,0xebd6450960ddf7350960,0xbbf845c560ddf735c560,0xddf7358560bfb8058560,0xddf7354560b7f8548560,0xddf73485609fd879d940,0xbbd849d940bf9809d940,0xddf835d940dfb805d940,0xbdf835d940bfb805d940,0xfbb8059140f9d7650d40,0xf9d435c9409fd87d8940,0xbbd84d8940bf980d8940,0xf9d4358940fb96458140,0xfdb83581409ff845d920,0x9fd86dd120ddf7650d20,0xddd7650d20f9d6450d20,0xfdb8050d20bef8458920,0xdef7458920fcd4358920,0xdfb7458120ef96458120,0xfdb8358120fd94358120,0x9df835c364cdf769d943,0xb9d849d943b9f845d943,0xbdb805d943cdd761d943,0xbcd821d943bd9801d943,0xe9f7659143e9c7659143,0xb9f8059143d9d7450f62,0x9df835c362d9d7450f60,0xe9d6450f609dd84dcd60,0x9de8750d609dc8750d60,0xe9d6450d609df835d940,0xd9f7650d40d9d7650d40,0xf9b8050d40eb96458140,0xf9943581409df835d920]) else (word80 [0x1e000846080000c,0x3042a081182108c3ac14,0x84722d0a0025088e45,0xe84c123914409b0e84c,0x2608808e380c1043d430]))
def g127H7 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0xe78000000a2,0x8cb6c00cc1440000da00,0x1aa00068240000006329,0x7d0e01cf867700000005,0x90070689ca5400000000,0x23984c64d36c4e01a65])
def g127D8 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x43220890385430d0,0x4410c9c7501044832224,0xd0a04801c4428116061,0xa10e047f009c6438007,0x28120477009c404800d2,0x7110a06001c80524811a,0xc027150e008890443801,0x52211120467009c50680,0x4281110a060058185064,0x5801b2214749c2814027,0x1d10683854343271d0e0,0x4903831a220818083702,0x305060602c0142816103,0x8903260d070605840302,0x22c0412c1c1407010e2c,0x3870e070605030241c08,0x4270a008c94447464543,0xc24d84182079351d1915,0xd06030a1060b1341001,0x445434d8b2525351b093,0x9450a238b4c18170a00,0x789c4c2082325101c043,0x7160f012c78c4b270c1c,0x18100b17020c9c807060,0x5020144c02421007a1a0,0x7088d123080706050402,0x41c024201c1814080700,0x543880b4715221118305,0x488407050dc0118b1838,0x1c140d041b022c88685c,0x8b4d1c18341c18140c0,0xb0089109221d86c0810d,0x441e1e1a160f0a05108c,0x8c00e240c381c1815100,0xf03089c926221d8681c0,0x440d209c361b0205106c,0x5c4c3c28100261e1e1a1,0x60e0709109c80e070604,0x2c0c5432724180a0700,0x523060e0706050302c01,0xd209e0474381c1816100,0xc0b00b1dc0220b81141c,0x1816100b010c8880d224,0x6c01d27841f00886831a,0x7060504830281c00e28,0x341f17012c6860781c5c,0x4b2219007a3462052e3,0x74601c00c2216183054,0x8844581c04b221c18340,0x51f020c8860e07050381,0x6c08b2037004e3048dc,0x11210c0141b041a13023,0x58014cc0b27150b051d,0x308450d0711c08b160f0,0x41c8b022c60f8dcccb81,0x1400960453302c9c78a7,0x44c22250ec86742a2105,0x4c8134001fb4fac7bf3,0xd61e64f0476f3ac1d04e,0x6c72338a1c14dec6eb36,0x81ae4d5467b32e18d4c4,0x45ff2e816a4b2457b2b4,0x1554a6c527282138497c,0x49b23c11948a443720a0,0xfe47a43b31c80e046b43,0x3718e0bf45b42b314c09,0xd448c22f10607b43bc1b,0x30cc05f42bc14709a046,0x41fc0db06402b412c07f,0x34014406c01f0003ffb,0x92c9ff5c964ffee0b27f,0xd70593feb22c5ff55360,0xffaa3b07fd75583feb2a,0xc1ff5d160ffac8b07fd5,0x4583feb92c1ff58960ff,0xa84b07fd71583feb0ac1,0xff54560ffa42b07fe765,0x3febb281ff5c940ffec,0x4a07fd62503feb22417f,0x5c365bfee0b2dfd72d92,0xfeb86c97fdc964bfee0b,0x27df7650fef3b287f75d,0x943fb8eca1fdf7250fee,0xb9287f7dc143fbae0a1d,0xfd74d8beea1ec57f5c36,0x2bfee8b17dd4358affb8,0x2c57f5d942f7ac8a17ed,0x6250afeb86c37fdc161f,0xdec490dfd74d837eb26c,0x1f750f60bfae5b05ff74,0x5837fb22c1bf59160fbe,0xe6b07dd43582ffb92c17,0xfdd950bfeeca05fd7650,0x3deb22817fdc940ff2c0,0xa05ff76482febb2417fd,0xd120bfae8907dd43483f,0x6b1241fb50920fda4290,0x7f960482ffbb2217d5c7,0x65bdee4b2df771553ceb,0x2287e755143afaebb0d7,0xf75486efb9ac1e750d40])
def g127H8 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x60985ae828600,0xa951b0007ac79e,0xeac000000018d828a5eb,0x1bf1813adf0000000000,0x4ee5c00032a,0x800000000000001e1b38,0x20000000000002a00006,0x572d18f4ac0026be8800,0x21257585812002999b2,0xd01a50aee35001153684,0xdc000003cc000001c480,0x4cb00191f3880000000,0x14800000000000421000,0xa5c00000c68000005d8c,0x90000a2b63001e0c0000,0x85a000000006d4fbdf5,0x90e46e00089828ec4001,0x5ca696716930d80013c0,0x672b34f9a4b3b00,0x1044b0e223ca0011e800,0x50f87e2159967ee99e96,0x4100000000000a2cabc0,0x4e4934ec4000002dbe1,0x9c563a060004000bc0a6,0x6d8e6946a974e0004,0x3ae300024c000000001c,0xd852b100072ad0105825,0x15400340301902202024])
def g127D9 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x4046c028,0x3080e360c0283080c88a,0x41990068b1c694833200,0xb181410f00621188c197,0x68c1920e1a460cb803,0x844360c01630a8e140c,0x5203600b2240d8314840,0x16447821a00c16586441,0x6086802ce0e1c322992c,0xc01a40d0e180c0992d3,0x90340c02030a0c34e940,0x33200b1cd0d22880cb80,0x3081b14801802c88e00a,0x41982c5f2799d8b32c0a,0xd2a525d87de86e18150d,0x53549e18029003ff65f,0xf597ff64ff593fd54ffd,0x8bfd62ff50bff61ff587,0xfd51ff487ff60ff583fd,0x50ff503fd20ff443dd43])
def g127H9 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x456737,0xe99f489e4f8c800000f,0x3c000003643034ad5200,0x1af759800b5400000000,0x50e625d1f90742001246,0xac0480039b5430002035,0xd1c90844a58608ed7225,0x1af620a00b1aeda6,0xe4a05303a1192ddf8000,0x1f1a5d800000d380060,0x5a3085f9780000000000,0x3468000008f0,0x20c20800000000e,0x6ddc00033c0035f18b21,0xe002d29a0000000aaa1c,0x65a098db80074472800e,0x3408200168527000611e,0x6000461b1e62e117a355,0x21a9f003a1040000d090,0x440083121c0802614403])
def g127D10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x9858027f
def g127H10 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x240000000868004e004,0x48000000450000000675,0xb0000000000000000000,0x81629780082000004800,0xab,0xa8f9001a5818018c5002])
def g127L : Nat → Packing
  | 5 => (2,5,6,0,0,3,0,g127D5)
  | 6 => (28,4,6,0,0,9,0,g127D6)
  | 7 => (114,3,6,0,0,12,0,g127D7)
  | 8 => (86,2,6,0,0,13,0,g127D8)
  | 9 => (19,1,6,0,0,10,0,g127D9)
  | 10 => (1,0,6,0,0,0,0,g127D10)
  | _ => emptyPacking
def g127I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 3 0 5 1 0 g127H6
  | 7 => lookupWord 7 47 3 9 5 0 g127H7
  | 8 => lookupWord 28 191 4 11 7 0 g127H8
  | 9 => lookupWord 21 127 7 11 7 0 g127H9
  | 10 => lookupWord 4 53 2 9 5 0 g127H10
  | _ => fun _ => none
def g127 : Forest := ⟨127,10,fun i => g127Y[i]?.getD (0,0),g127C,g127A,g127L,g127I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P5_0 : block g127 5 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B5 : block g127 5 0 2=true := g127P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P6_0 : block g127 6 0 4=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P6_4 : block g127 6 4 24=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B6 : block g127 6 0 28=true := (@block_merge g127 6 0 4 24 g127P6_0 g127P6_4)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_0 : block g127 7 0 26=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_26 : block g127 7 26 88=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B7 : block g127 7 0 114=true := (@block_merge g127 7 0 26 88 g127P7_0 g127P7_26)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_0 : block g127 8 0 9=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_9 : block g127 8 9 52=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_61 : block g127 8 61 25=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B8 : block g127 8 0 86=true := (@block_merge g127 8 0 9 77 g127P8_0 (@block_merge g127 8 9 52 25 g127P8_9 g127P8_61))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P9_0 : block g127 9 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P9_1 : block g127 9 1 18=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B9 : block g127 9 0 19=true := (@block_merge g127 9 0 1 18 g127P9_0 g127P9_1)
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
  · exact g127B5
  · exact g127B6
  · exact g127B7
  · exact g127B8
  · exact g127B9
  · exact g127B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127G : graphValid g127 (boundsBefore K252) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low127 : Lower true (varsX 127) (graphGoal 127) 11 := lower_forest (g:=g127) (i:=0) (hints:=1049923) (before_sound K252 V252) g127G g127T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K127 := extendKnown K252 11 [(127,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V127 : Known true K127 := extend_ok (m:=127) V252 low127 (by decide +kernel)
def g191Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfff9914845dc0c3208,0x57f93000000fc0000fff])),(BitVec.ofNat 152 (word80 [0xa081484148081200,0x13e13249249249249249]))),((BitVec.ofNat 152 (word80 [0x2e1698323522625,0xfa40c00003f000fff000])),(BitVec.ofNat 152 (word80 [0x330e0680303102205,0xfa4000c30c30c30c30c3]))),((BitVec.ofNat 152 (word80 [0x5cac5a9599d85d5,0x4d40100000003f000000])),(BitVec.ofNat 152 (word80 [0x15c1c8c1a9599d8595,0x4d4009e79e79e79e79e7]))),((BitVec.ofNat 152 (word80 [0xfffd6ca45bd5527d10,0x501c4000fc000000003f])),(BitVec.ofNat 152 (word80 [0xa60568241a95526d10,0x401c4596596596596596]))),((BitVec.ofNat 152 (word80 [0x402593eb1ca049b,0x8436a03f00000003ffc0])),(BitVec.ofNat 152 (word80 [0x380402111cb0c2049a,0x4148514514514514514]))),((BitVec.ofNat 152 (word80 [0x48b2640ac338afe,0x20847fc000003ffc0000])),(BitVec.ofNat 152 (word80 [0xc004030640a402086a,0x847618618618618618]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x27492b802a4c902,0xbc70fffffffc0000000])),(BitVec.ofNat 152 (word80 [0x21480a000248000,0x20820820820820820]))),(0x0,0x0)]
def g191C : List ColumnInfo := [(4,0,187,0,10)]
def g191A : List (List Nat) := [[]]
def g191D10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xff
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
theorem low191 : Lower true (varsX 191) (graphGoal 191) 11 := lower_forest (g:=g191) (i:=0) (hints:=1049923) (before_sound K127 V127) g191G g191T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K191 := extendKnown K127 11 [(191,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V191 : Known true K191 := extend_ok (m:=191) V127 low191 (by decide +kernel)
def g223Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffe647a826c1076899,0x12480000fc0000fc0fff])),(BitVec.ofNat 152 (word80 [0x28242a00641036088,0x10001041041041041041]))),((BitVec.ofNat 152 (word80 [0x1a1675100a05e7f6,0x5520003f00000003f000])),(BitVec.ofNat 152 (word80 [0xcca167010080563f6,0x5500b2cb2cb2cb2cb2cb]))),((BitVec.ofNat 152 (word80 [0xf7a344bcdb08551,0x501c000000003f000000])),(BitVec.ofNat 152 (word80 [0x570f7a344bcdb08551,0x100975d75d75d75d75d7]))),((BitVec.ofNat 152 (word80 [0xffe43932daaacf8214,0x8b000fc0000fc000003f])),(BitVec.ofNat 152 (word80 [0x98043912588a4c8214,0xa006186186186186186]))),((BitVec.ofNat 152 (word80 [0x18b84719f40b063,0x28a3f00003f00003ffc0])),(BitVec.ofNat 152 (word80 [0xe00089046186408001,0x28204104104104104104]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x22c1b017070590e,0xe514000003fffffc0000])),(BitVec.ofNat 152 (word80 [0x4090030001802,0xc5168a28a28a28a28a28]))),((BitVec.ofNat 152 (word80 [0x19d049cc14980680,0x9ccffffffc0000000000])),(BitVec.ofNat 152 (word80 [0x1100098010900400,0x80cf0c30c30c30c30c30]))),(0x0,0x0)]
def g223C : List ColumnInfo := [(4,0,219,0,9),(8,0,215,0,9),(0,4,155,64,8),(1,0,222,0,8),(2,0,221,0,8),(16,0,207,0,8),(128,0,95,0,8),(0,2,77,144,7),(9,0,214,0,7),(12,0,211,0,7),(18,0,205,0,7),(20,0,203,0,7),(64,0,155,0,7),(64,4,155,0,7),(1,4,154,64,6),(5,0,218,0,6),(8,4,147,64,6),(16,2,77,128,6),(16,4,139,64,6),(128,2,77,16,6),(130,0,93,0,6),(136,0,87,0,6),(9,4,146,64,5),(13,0,210,0,5),(17,0,206,0,5),(24,0,199,0,5),(65,0,154,0,5),(65,4,154,0,5),(66,4,153,0,5),(72,0,147,0,5),(72,4,147,0,5),(80,0,139,0,5),(80,4,139,0,5),(129,0,94,0,5),(140,0,83,0,5),(144,0,77,0,5),(144,2,77,0,5),(28,0,195,0,4),(73,0,146,0,4),(137,0,86,0,4),(192,4,27,0,4)]
def g223A : List (List Nat) := [[]]
def g223D5 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0xa008500,0x4080e9a2e505c300b236,0x9f8659143d4ab8ba0661,0x43d4940a636a37650f52,0x502b89a8e4143d4940ce,0x26639050f52502bc3a06,0x6143d4910de06a543d49,0x404437819850f5250110])
def g223D6 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then (word80 [0x81290129,0x18408000000c10103040,0xf001010540c200000001,0x41000304006415350308,0x2c4040174133411401,0x1c0734217503701cd11,0xc073420381334104b830,0x802938308c9891cd0e0f,0x70524062cd17c106c0b0,0x9240f706d0d95b135a6a,0xed51a8b3a66ecbd96324,0x642c5188b09602bf97da,0xf35d6ba1702d85a0b0d5,0xdab8560ab5552a753ea7,0x14a28c508a053ca764e6,0x9ad31a604a692d21a3b4,0x668c116a2542682d041f,0xb3dc7acf19e03ba768e9,0x1cf3846c0d69a031c618,0xc19802fa5c0b41652ba5,0x54a694027a4e89b92f25,0x84909091922c42483103,0x2003f47a8f21d439c6f8,0xd219e330620c11722c45,0x48a61322083a86d0ca16,0x2a84806c06809000477,0xe4d80dd1659ceca70eb2,0xa8739f9461d6550e7b72,0xc3acaa1ce7653805954,0x3b4ecaeecb228769d90d,0xd96450ed3f2cbaac8a1f,0x875d56559143b4fc82ca,0xb228739f906195450ee3,0xf2abb2a8a1dc765b7555,0x143b8ec86eaaa287e1d7,0x65955450ee3f20b2aa8a,0x1ee3593805c943d4fc32,0xc8b8287c9f765917050f,0x63f0aaa2e0a1f47dd554,0x5c143ba64ab04b82873e,0x590e0564d4ab9f20c3a8,0x7a957365f8650f52ec7c,0x32e8a1ea5d8d865d143d,0x4bb1b0eb2287a97a3e19,0x6450f52ae6cbf00a1ea5,0x9cd87e0143d4bb1ae9c0,0x287a967361d8050f52ec,0x6ba300a1ea55e7915917,0xd4b39b30a1ae1a97635,0x91435c352ee4c8286b86,0xa51df9361774582b3b29,0x43a86b05676537550d60,0xe4fbaac8a1ac169d9655,0x143583c3acaaa286b067,0x3a1d8250d60f46b2304a,0x1ac1ad98660143583d32,0xc8c0286b06e361143d49,0x60f46b2287a92c11dd94,0xe0d765423bf30bb286a8,0x7275d96450d50f0eb2ac,0x8a1aa171d9655143543a,0x3aecaa286a86d6615805,0xd50f8caa300a1aa11df,0x9361d65502f3720c3286,0xa05676577650d40acfca,0xaeca1a8179b906154350,0x2b3b2dbaa86a0567e597,0x550d40acecbacaa1a81c,0x9d7659543503a3aeab2a,0x86a0763dd98250d40ec6,0xbb304a1a8179996e0143,0x5037330dc0286a05e665,0x78050d40dccc2f00a1a8,0x1d8d7650d72503f1720a,0x1ae4a047b66376d4940d,0xc6cc287a9281b8d8750f,0x52503b1eeca1ea4a0763,0x5d943d4940fc5c8287a9,0x281ba964603525035770,0xab22c0a05ae659545814,0xf1cb2aa8b0281e99965,0xd605037370aa1ac0a07,0xa65954358140fc4c9286,0xb0281ea9645c960503f1,0x286b92c0a05ea6535258,0x140f54b26a4b0281f894,0x3d49605035730cb22a0a,0x78e5956454140b9ccb2,0xa8a8281b398655150503,0x7330ca1aa0a07c665543,0x54140f8cb2a86a82817c,0xb9061943483b1d0eb228,0x6907a3e196450d20be9c,0x830aa1a21f1785551434,0x4378b30a1ea4885f4e4d,0x8558110fc9caa86a0221,0xf919550d40443f230aa1,0xa80885f86635250110bc,0x5c8304a1a8198d8750f5,0x250371286c06a4a06e16,0x1143d4910fc0c9286a02,0x21f814360940442f4329,0xa9280887e050f5250110]) else (word80 [0x4404000,0x44040000337447001910,0x110100c704071019080,0x7101b101000d081c2010,0x10041005c604517102b,0x1010010040000b0c1001,0x605c4044804021010000,0x90109010124064220c10,0x64129012901000064163,0x6c4e003a3410083b082b,0x81908031c1000008404,0x210010824613c00c049,0x220924611010cc70400,0x291c4090f040040104]))
def g223H6 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x930,0xd25660007f00022162])
def g223D7 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then (word80 [0x4f89bc47,0xe1c70b0847c1ba09b02c,0x80a3ff1fdafe77e7bf25,0xf62f907bc3dc9eb4f397,0x99bc49de2ed0757ba39c,0xece5571eb8b9c3ee1070,0xb781b7eda76cc35ddab,0xed47697b4399daccc655,0xb2058c0c486183061824,0xbdf5daae756f8b645a62,0xc895f0ace556aa0d4b2a,0x2f50ba7fd3ce9cf4dba6,0xa134498a4c225b12ba94,0xe49b24c120c8dc45da24,0x50ce8464099fa4f6c77a,0x3a81c74dd46b7342198c,0xc726062ee16ecb1055e2,0x9113bc95447722690447,0xce3b41c50d8066c30316,0x80a744e6240102074434,0xe17d0a984801ec0c3048,0x1980660009fd80dd165,0x9fd84dc165bdf835c165,0xaff80595649ff805d954,0xb7f8059554bdd85dd943,0xbdd80dd943bdf855d943,0xbdf805d943bdd86dd543,0xbdd80dd543bdf865d543,0xbdf805d543bdf8759543,0xbdd8759543edd7659543,0xf5d7559543f9d8459543,0xbdf8059543f9f7559143,0xf9d7559143f9f7655143,0xf9d7655143fcd765c943,0xbdd86dc143ddd76dc143,0xbdd85dc143ddd75dc143,0xf9d64dc143f9d54dc143,0xbdf865c143ddf765c143,0xddd765c143bdf855c143,0xddf755c143ddd755c143,0xf9d645c143f9d545c143,0xfcd825c143fcd725c143,0xfcf8650f52fcd8650f52,0xfcf8050f52fcd8050f52,0xded645c352bed80d4961,0x9fd84dd560bdf835d560,0xaff84595609fd85dd160,0xcfd65dd160cff7559160,0xafd8655160e7d6555160,0xdde8750d60ddd8750d60,0xedd8650d60ddf7550d60,0xedd6550d60f9d7450d60,0xf9d5450d60fcd8250d60,0xfd98050d60bed84d4960,0xdef74d4960eed64d4960,0xfcd43d49609ff845d950,0xddf835d950b7f8459550,0xcfd7659150e7d6559150,0xbf78159150b7d8655150,0xd7d7655150ddd8750d50,0xddd7650d50f5d8550d50,0xf5d6550d50f9d6450d50,0xfd98050d509fd85dd940,0x9ff855d9409fd86dd540,0x9ff865d5409fd8759540,0xcfd7659540d7d7559540,0xebd6559140bbd8655140,0xf3d6555140f9f8650d40,0xf9d8650d40f9d7650d40,0xf9f8550d40f9d8550d40,0xf9d7550d40f9d6550d40,0xded765c940fad645c940,0xbed87d4940def76d4940,0xded76d4940fad64d4940,0xbfb8558140ef96558140,0xfb95458140fe97258140,0xfeb5258140bf98654140,0xf796554140fb96454140,0xfcf8650d20fcd8650d20,0xfd78550d10fd58550d10,0xff18558110ff18550110,0x9f580dc564e9f7659143,0xe9d6559143b9d8655143,0xf1f7555143f1d6555143,0xf8d645c943bcf805c943,0xbe78159352dcd8750f52,0xf8d6450f52dcd435c352,0xe9d6450d609df835d950,0xf1d5450d50d9f7650d40,0xd9d7650d40d9f7550d40,0xd9d7550d40f8d8250d40,0xf9b8050d40f8d435c940,0x9ed87d4940bad84d4940,0xf8d43d4940be980d4940,0xeb96458140f994358140,0xf395454140f994354140,0xbe78159120dce8750d20,0xf8d6450d20f955450d10,0xfc58250d10be584d4910,0xfc543d4910ef16558110,0xfe35258110fb15450110,0xfe18250110fe35250110,0xd8d7450f52f914350110]) else (word80 [0x100400181c08,0x200098de00405040e04,0x1000486821d02908802,0x200a422008150290880,0x20548e44218815238148,0x820200a4220081d02841,0xd2190880210880111c88,0x432110050ab138019103,0xc4d60064411d35881fe0,0xa05211003a23019a191,0x3b44603348c2b1984c0,0xc881508b10982255230,0x96331050a91c88431000,0xe90c844012840b128540,0xc8942a0064304014844,0x1086090c10401485c01,0x87420a84430810c4a1d,0xa8046189943a1500102,0x89686170c4a898406c64,0x150432a945881a0a8212,0x8901310100040008012,0xc20100400189380100,0x2401842426d003004e87,0x4206240aa0c302a09001,0x89380830c30c41206240,0xf8524248643040642520,0x2a405480a90101004001,0xe3403c00e1a03080a0a3,0x689800f018d0a1a030a1,0xa05084c8240068240064,0x30f20d1a1a3700830d89,0x8011e344043083218080,0x100800101c081000702,0x8020014480c4270040,0x32002120638018900610,0x9304130980240c881562,0x9106206189c01208c06,0x686430eb019a83103e18,0xe033441230831c01188a,0x40816a408240e0948020,0x908a4094808018e00400,0x3e8c14141028218c1040,0x23d8c82a0885528b1106,0x210580cd0cbc83603344,0xd30580cd1034c066860,0x7e0b0f0bc01615c01206,0x440cc2b80cd120a1f00c,0x2b814d120d0ae00649a2,0x42833c0120805a006515,0x4d520a09e21358625148,0xfc1c0517042841194a0c,0x824ac61904e230618c58,0x70a19e060c48260f818d,0xc3387e0081362857802,0x40c0818c180615c0120c,0x19427019a18143e18420,0x78183668e198512706c,0xd158e83e006448782d82,0x8aa686060003b8212102,0x48a26707062a051583a6,0x80ee09330a200f81c11,0x20819a3d1b8018168fc0,0x107043628668e18e046c,0x5e0d17078d13881046d1,0x51e298d8c41c192b1a31,0x7818312180524e0d9b2,0x41099c1c1a90460e0e98,0xa41043c0e0b34482c0f8,0x2cc9209c10c700486014,0x1fc192334302c0f82cc9,0x209c6e1849184a1430c1,0xe6f00482d852bd55d2ae,0x1d666b15560a9b54329c,0x54b8a4751da899434a00,0xcf5e75b37a9acccbe5f9,0x2d295449d649724590dc,0x8323c51c18cbc6222f31]))
def g223H7 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x1f5dc,0xa54b50737fceb5800000,0x426000002b43a5000,0xe40000020bd5400000a,0x580017662ae760000045,0x34ba0025ab04001a2800,0x1e7eb7793764002,0x30aef9a05523ca1b68e,0x1f1c5b035a48fc000000,0x240d8ccc20020723d,0xd8feb02b8c4000003,0x9b000bd1615af1eaf1a3,0x97cc721a34002a9fa0ed,0xc2444a513fc6fb80097e,0x99f8f473fb77ae0bde0f,0xd20009d3a02dfd000019,0xcc2200181000b7d3d975,0x49a00014a944e60922cf,0xde00bba2d78b20001dbd,0x73d2000000000000004c,0xa00000492d9c002e1922,0x4b21e167800c89cc5aa6,0x89825c21b78fbb5a631,0x38c5b2c0000071904015,0x221c000282e112841a40,0x400c11848c2283000001])
def g223D8 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x1189c6a20,0xf94600e431a823451803,0x14108d20a0268c423088,0x482120fa010a68a34890,0x471a2a2400a46838a42,0x3089804828f8d0c60268,0xa4884318050292018160,0xe025140e0e0a08058087,0x82504144560e026920c5,0x3e071581831a4841406,0xc560e012100e99148684,0x380483240ca6218ac56,0x120e8c860381149a323,0x8ca3218f6045268f1502,0x3287809a483a623a3210,0xe260218c928432988e8,0xd0b8980104a1a560c632,0xb8299150f2828382826,0x60a6908e50430980278,0x3069a40660e012108a43,0x818306482a08cc641e01,0x20d0d0b09278306983c1,0xe0a692085042340e8c0a,0x981071b8259406c3e26,0x23608d910f82403620c,0xc3c320c6e26022cd9218,0x5824980303108c41864,0x560e012100e0c0801829,0xa3038f8d0c0383428241,0xe060a696318183064828,0xc600560c1900c1f8c171,0x5829a303c341e0c5260a,0x42310e8e0781828d0a48,0xc23e060c28d8cc68d830,0x71a94341e0a3c6a50a8d,0x818307149a36041e0898,0x8a68d8183069a482a026,0xe0c192300d0781822714,0x9a341e0a645498b9b870,0xc0f83810a3808566e1e0,0x120c03818d86144030c8,0x4e361c5268d8d8624198,0x294320e361c6250b8d94,0x19821c28c20e6e360054,0x18f821a941e220e341c6,0xa50b83069914220e6e04,0x1920b09830748982e0c1,0xa6920842079b81824830,0xc01e6e0e0120dd91d25c,0xb9c6dc11bb5b59afdaa1,0xa459c993d8d18457c973,0xd6c16455c954d4b14153,0xb935d2e12551f919d131,0xb5068facf20ed4e38dc,0xcd40cc4c08bacb40ac4a,0x689cc9608f489882c7c0,0x7646f868c6305b45484d,0xc4704043a834c2d02842,0x281dc1801240d806c001,0xff5d165ffae0b2ffd755,0x83feba2c1ff55160ffac,0x8a87fd61543febb281ff,0x5d540ffacaa05ff74596,0xffb82cbbf59564bfaeca,0xa77d65553efbb287f75d,0x943fbeeaa1fdd7550fee,0xb2a87f7dc143fbae0a1f,0xed64d4bf7a92c37fdd56,0xdfacab05ff745837eb2,0x2c1f750d60fdea4b07ed,0x42582febb2a1df59550e,0xfaa8a87dd43542ffbb28,0x17f5d940bfeeaa05fd75,0x503deb2281ef55140fda,0xe4a07ef52503fcb0281f,0xe54140fdac8907ed6148,0x3fab2e21fddd510feaca,0x887f554442ffbaa21fbd,0x4910beee2b279d6450fc,0xeaa287f35c943bdae9a9,0x7cd43d4af6b86a5e750d,0x40bdee8907cd43483f3a,0x9621f550d10fcea4887e,0x542443f8b0221fc50110])
def g223H8 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0xe3d659798000a3900000,0x926f4032f0000000000,0x8cb5a000f97f2d,0x49d00708de1bb1ffa200,0xd3700085c0006490000,0x895052a77519670d25,0x442954920000a7880e87,0x4000000000c480000002,0x80e30b2b971e5f33f593,0x788118a14785e1df3aa0,0x3500192e6683b7642559,0x9c2e560876a9b799062,0x310a5095b158000000f0,0xd54db1526df1743104a4,0xa0f4b00083608f94c208,0x75e10a57d33328343,0x815d290581f2cd2a0009,0xb0004470940004a109a,0x49c075b84a6cb2315600,0x30c00007976fb45e73f,0x65687f02b8236aa11c29,0x81241636e16967f00021,0xc00029ef32000000f7b0,0x17a79f85100088e000,0xf04000a3ed3500000097,0xc941567186c68306134f,0x4e061d0fc4338a000b8b,0x98975752162700100036,0x3000b05a2476b000591e,0x96c3c000722000146d1a,0x31ec4f228000000e7e47,0x22449135536e0073c102,0xce180a301836e6000114,0x482970c00508042c9090,0x10040000183010048183])
def g223D9 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0xa0340864e5411a44d,0x150e0c04830d8d0218a8,0x28079b0c3c18028a0e0a,0x41144ce0c8434d272a0,0x3824071b0234a826c70,0x4626c6070600a2060383,0x513180cd8d0e00a1a3,0x43950460b1a1c1143458,0xd1a541063459b1a08380,0x286093608380906b0e93,0x972257d5b760142448e2,0x2e48918030003fd65ff5,0x93fd54ff587fd51ff583,0xfd50ff503fd10f750fef,0x52fb50bed20fdc43f510])
def g223H9 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0xe840000000000,0x1c1c00000000,0,0x188e2a0000000000,0xc520000000000000000,0,0xcd000000000000000000,0,0x35c00000000,0,0,0x41d0000000000000000,1,0xc0c0000000000002000e,0x40000000000000000000,0x66c0000000000000000,0,0x1048000000000,0x1a08000000000000000,0x80a00000000,0x3d1f,0xa000000000000000021,0xc4b7e6a0000000000000,0xc4000000,0,0x14818,0xe4660000000000000000,0x167000000000000,0,0x15c8000000000000000,0,0x87c003160,0x6800000000,0x2a70000000000075000,0,0,0x8760000000,0x7c0f2c00000,0,0,0,0x5280000000000000,0x186800000000000,0x3260000,0xd88002de00000000,0x5f80098400000000000,0x14ac0000b0,0x1a0a920000000000000,0,0x20d800000000,0x695000000000000000,0x20b800000000d880000,0xe2400000000864c6000,0,0xac0000000000000,0,0,0x1888000000,0xd780,0x1e0400,0,0x668000000000000,0,0x2c300061800000,0,0,0x414f6400,0x2260000014f000000,2,0x3e000000000000000000,0x15e80000000000,0x41e003,0xdd000000000000000000,0,0xb5a00000000,0,0x24c0000012811])
def g223D10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x68c19408037f
def g223H10 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x3d40b66b,0x903ac32f4000001d2440,0x398011fa0ab4ce])
def g223L : Nat → Packing
  | 5 => (8,5,6,0,0,7,0,g223D5)
  | 6 => (121,4,6,0,0,11,0,g223D6)
  | 7 => (163,3,6,0,0,13,0,g223D7)
  | 8 => (69,2,6,0,0,12,0,g223D8)
  | 9 => (15,1,6,0,0,10,0,g223D9)
  | 10 => (1,0,6,0,0,0,0,g223D10)
  | _ => emptyPacking
def g223I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 2 13 2 7 3 0 g223H6
  | 7 => lookupWord 30 167 6 11 7 0 g223H7
  | 8 => lookupWord 40 211 7 12 8 0 g223H8
  | 9 => lookupWord 17 577 1 11 7 0 g223H9
  | 10 => lookupWord 3 23 2 8 4 0 g223H10
  | _ => fun _ => none
def g223 : Forest := ⟨223,10,fun i => g223Y[i]?.getD (0,0),g223C,g223A,g223L,g223I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P5_0 : block g223 5 0 8=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g223B5 : block g223 5 0 8=true := g223P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P6_0 : block g223 6 0 8=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P6_8 : block g223 6 8 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P6_104 : block g223 6 104 17=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g223B6 : block g223 6 0 121=true := (@block_merge g223 6 0 8 113 g223P6_0 (@block_merge g223 6 8 96 17 g223P6_8 g223P6_104))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P7_0 : block g223 7 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P7_2 : block g223 7 2 42=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P7_44 : block g223 7 44 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P7_140 : block g223 7 140 23=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g223B7 : block g223 7 0 163=true := (@block_merge g223 7 0 44 119 (@block_merge g223 7 0 2 42 g223P7_0 g223P7_2) (@block_merge g223 7 44 96 23 g223P7_44 g223P7_140))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P8_0 : block g223 8 0 16=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P8_16 : block g223 8 16 43=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P8_59 : block g223 8 59 10=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g223B8 : block g223 8 0 69=true := (@block_merge g223 8 0 16 53 g223P8_0 (@block_merge g223 8 16 43 10 g223P8_16 g223P8_59))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P9_0 : block g223 9 0 6=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P9_6 : block g223 9 6 9=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g223B9 : block g223 9 0 15=true := (@block_merge g223 9 0 6 9 g223P9_0 g223P9_6)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P10_0 : block g223 10 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g223B10 : block g223 10 0 1=true := g223P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223T : checkedTables g223 10 := by
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
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223G : graphValid g223 (boundsBefore K191) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low223 : Lower true (varsX 223) (graphGoal 223) 11 := lower_forest (g:=g223) (i:=0) (hints:=1603) (before_sound K191 V191) g223G g223T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K223 := extendKnown K191 11 [(223,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V223 : Known true K223 := extend_ok (m:=223) V191 low223 (by decide +kernel)
def g239Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x53129020bd67c6988,0xff0000ff0000ff])),(BitVec.ofNat 152 (word80 [0x531010202c2586908,0x5050505050505050505]))),((BitVec.ofNat 152 (word80 [0x655714c93b408f3648,0xff0000000000ff00])),(BitVec.ofNat 152 (word80 [0x255704891b408f3040,0x13131313131313131313]))),((BitVec.ofNat 152 (word80 [0x991b81245628f75424,0xff00ff0000])),(BitVec.ofNat 152 (word80 [0x911b81041208e75424,0x43434343434343434343]))),((BitVec.ofNat 152 (word80 [0xb0984f5581e08781d1,0xff0000ff00000000ff])),(BitVec.ofNat 152 (word80 [0x10084e5501208700d0,0xa0a0a0a0a0a0a0a0a0a]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xb429ac7602d1ac91a,0xff000000000000ffff00])),(BitVec.ofNat 152 (word80 [0xa001a42602410891a,0x2c2c2c2c2c2c2c2c2c2c]))),((BitVec.ofNat 152 (word80 [0x2c8d22b02c17c09a67,0xffffff000000])),(BitVec.ofNat 152 (word80 [0x288420a02c15008203,0xb0b0b0b0b0b0b0b0b0b0]))),((BitVec.ofNat 152 (word80 [0xd224e40a9601212633,0xffffffff000000000000])),(BitVec.ofNat 152 (word80 [0xc000a0008401200621,0xc0c0c0c0c0c0c0c0c0c0]))),(0x0,0x0)]
def g239C : List ColumnInfo := [(2,0,237,0,10),(4,0,235,0,10),(1,0,238,0,9),(8,0,231,0,9),(64,0,175,0,9),(32,0,207,0,8),(128,0,111,0,8),(0,2,77,160,7),(0,4,139,96,7),(0,32,73,134,7),(0,64,162,13,7),(9,0,230,0,7),(34,0,205,0,7),(36,0,203,0,7),(1,64,162,12,6),(2,32,73,132,6),(4,32,73,130,6),(4,64,162,9,6),(8,64,162,5,6),(32,4,139,64,6),(65,0,174,0,6),(72,0,167,0,6),(128,2,77,32,6),(128,32,73,6,6),(9,64,162,4,5),(33,0,206,0,5),(40,0,199,0,5),(73,0,166,0,5),(96,0,139,0,5),(96,4,139,0,5),(129,0,110,0,5),(136,0,103,0,5),(160,0,77,0,5),(160,2,77,0,5),(137,0,102,0,4)]
def g239A : List (List Nat) := [[],[48]]
def g239D6 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x6081000,0x1038081c040e02070103,0x8081c040e0206ae967e3,0xa21dd995510cc8844029,0xd7a35d7815d160c2fe61,0x655d0745829d7a35db81,0x59150cd66559060c6454,0x29d7a161373d8d509b66,0xa68458d604c2ed3a1611,0x6358130bb4e856458d60,0x4c3e1b649915354130bd,0x4e856454d504c2d59a71,0x915354130bd26886454d,0x504c2f51a11915354130])
def g239D7 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0xa04000000,0xc3040000034004070c16,0x8103060400182040000,0x700c000c000020417042,0x70207020409181d001,0x18305820400182041a0,0x40000504090400141000,0x303040c081c081c081c,0x8140810001000008207,0x604ca04170589040004,0x4090400241e081000,0x504000c1064106,0x4030b830703041780822,0xc200660270083160205,0xc2626027002010141282,0xc0c1c0c1013030814129,0x30f0307030415052021,0x2848081809c008150500,0xb809c17004a1c17f0020,0x7ac40603063c00b025f4,0xbdd7a2f15dcb9971ae05,0xbab69692cf58eafd5e2b,0x4562ab9532a3540a3945,0xa885009e1382684c0975,0x2aa4d4949091d2374688,0xb11222143c8590720b40,0x6800fe9fa3e47bcf39df,0x3ae73ce39bf3786e4db1,0xae34c678cb18e30c5f8b,0xb1732d658cb015d2b455,0xcaa14c2925049c92c248,0x470850ee1c23285e8b51,0x5a280470860fc19c2f85,0x205807c06800577e4d85,0x5c364afdc830ab86c95f,0x79059771592bf726c2ae,0x3257e657835c064cfcc,0x2f06b80c99f98560d701,0x92bbf26baee8b047f663,0x759d160aefc9aeb3a2c1,0xcbd65dd274582bbf26ba,0xae8b067ddd7815d160cf,0xabaf02ba2c1af565e057,0x45823ff30ba8e8b0577e,0x4d751d160e5eb2ae83a2,0xc19f775e05645835eacb,0xc0ac8b057de4584dcd60,0xafbc8ac9b9ac11fd989d,0x373582bef22ba6e6b057,0xde45745cd6097ecc4e8b,0x1ac16dd939d163582dbf,0x26ba2c6b05bde457458d,0x60b7bc8ac8b1ac13f791,0x61a64542bbf26bb4c8a8,0x577e4d7659150cfbbb70,0x2b22a19f576e05645436,0xeacbc0ac8a8677a5d831,0x9150ceecbb06322a1b5d,0x9560c645437b320c18c8,0xa84fee4d8019150e5fb2,0x4c9b9aa15dd939937354,0x2bbf26b26e6a857de456,0x4dcd50aeec98c9b9aa15,0xed9219373542beb22326,0xe6a857e64064dcd509fb,0xc8b09b1aa19dd84dcf63,0x543c7ec9322a6a85dde4,0x56454d50bb6c90c8a9aa,0x17759119153542ef3203,0x22a6a853f65a8758d40b,0x5ecb508b1a815f7915d9,0x53503774c9c02a6a06ee,0x5938054d40bedc9b0ab0,0x281eb96521160503d752,0x8b1ac0a07b6e0d635814,0xa7ecb508bb2615f990a,0x11764c29ff2cc22ec985,0x7de45845d930afdc8308,0xbb2613f79161a644c397,0xaebb24c89867d5db8159,0x130cfabaf02b22619ed7,0x5608644c33eaeac08c89,0x867e5d58019130b7ccb5,0x8b02617d993a11604c2,0xdf72cc22c0985f6e4d84,0x58130bf9c8b08b02617f,0x391591604c3db508b1ac,0x987b66116358130f6d3,0x22c6b0261ed96458d604,0xc2fb327b22a0987aed92,0x6454130bf9c8ac8a8261,0x5f997191504c2fb32632,0x2a0985fa6486454130bf,0x8c88c8a8261f5b6454d5,0x4c3eb4c8a9aa0987d65,0x915354130fac322a6a82,0x611bf985d0745829f12e,0xb2ac0a0676e0f805d930])
def g239H7 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x1100167a1,0x304010b1000000d9b480,0x2d9258561800480030c8])
def g239D8 (j : Nat) : Nat := if 3 ≤ j then 0 else (if j<1 then (word80 [0xae956c6a,0xeb542a8c53de99b4aca4,0xa51aa893431a084f9a77,0x93929b8cd4265f30596d,0xcb325692789274802389,0x16d89d441e1850868254,0x15fb6fb17babd09e42f,0x75dba69c86e196f336,0xcdb00d56684330d8eac3,0x5f12e5169eb255822b2,0x152aa505012719302945,0x48da3a117c870423204c,0xfae79b3b41cb0de06b43,0x3c1914c245d62d1959ca,0x684dd250917081c3ae1b,0xc485882a312f08f43f,0x1c50c9057c2340e7055,0x81e0066000dfd855c364,0xbff8059664bff8059564,0xdfd855c064dfd75dd160,0xefd65dd160dff759d160,0xdfd759d160efd659d160,0xbfd839d160dff755d160,0xdfd755d160efd655d160,0xbff835d160dfd751d160,0xefd651d160dff7599160,0xefd6599160dff7559160,0xefd6559160bfd8795160,0xbff8755160dfe84dcd60,0xdfd84dcd60dfe64dcd60,0xdfd64dcd60dfe74dcd60,0xdfd74dcd60dfe745cd60,0xdfd745cd60efe7458d60,0xefd7458d60efe6458d60,0xefd6458d60bfd83d9150,0xbfd8699150dff7699150,0xdfd7699150f7d6599150,0xbfd8399150dff7659150,0xdfd7659150f7d6559150,0xbff8359150ff78159150,0xbfd8319150dff64dcd50,0xdfe64dcd50dfd64dcd50,0xdfc64dcd50bfd84d8d50,0xbff8458d50f7f6454d50,0xf7e6454d50f7d6454d50,0xf7c6454d50dfd865cf40,0xdfd8758f40fbd8458f40,0xdfd7654f40fbd6454f40,0xdfd86dcd40dfe8758d40,0xfbe8458d40dff7654d40,0xdfd7654d40fbe6454d40,0xfbd6454d40ffb8558140,0xff98558140ffb8358140,0xff98358140ff95358140,0xdfe845d930dfd845d930,0xdfd75d9130bfd8699130,0xdfd7699130dfd7599130,0xdfd7659130dfd7559130,0xff78159130dfd7519130,0xffa8458130ff98458130,0xffa6458130ff96458130,0xffb6454130ffa6454130,0xff96454130ff86454130,0x9fd80dd1659ff835c364,0x9ff835c264df565dc564,0x9fd83dc164dfb855c064,0xdf9855c064dfb835c064,0xdf9835c0649ff835c064,0xbdf835d560bfb8059560,0x9fd83dd160afd869d160,0xdbf749d160aff865d160,0xbf7815d160dbd741d160,0xbf781591609fe8795160,0x9fd8795160bf98095160,0xbef8255160efb8058d60,0xbfb8058d60ebf6499150,0xbf78159150bdd8319150,0xbed8219150bf58119150,0xbf98019150ddf73d8d50,0x9ff87597409ff865cf40,0xdbd645cf409ff8758f40,0x9fd8758f40ddd7358f40,0x9ff835d9409fd86dd540,0x9fc8759540bbf8359140,0xbbd86951409fd86dcd40,0xdbe64dcd40dbd64dcd40,0x9fe8758d409fc8758d40,0xbfb8054d40bbd86d0d40,0xdbf76d0d40dbd76d0d40,0xef96558140fb88458140,0xfba5458140dfb7358140,0xef96358140fbb4358140,0xdfb805d9309fd87d9130,0xbf980d9130ebf6499130,0xbf781591309fd8719130,0xbed8219130bf58119130,0xbf98019130fdb8358130,0xfd96358130fd96354130,0x9f7815da649ef825d664,0x9ef825d9549f7815d954,0x9f7815d3609df835d950,0x9f7815d9409ef825d540,0xed96358130f595354130]) else (if j<2 then (word80 [0xa0834105,0xc20e40a8082102e82a00,0x8441003820b838204878,0x202b003c1a182e050c34,0x54130012285c0a10681,0x2456008050bd0c304b00,0x8b43102f021106210c85,0xe04c0218d020b8502600,0x5c422050141050144004,0x88460481432320c12051,0x280a23208441850141d,0x12050d07400481440a,0x288d40410a830a02832,0x80121e130483050505,0xa0498c1850241300281,0x20d82c00a04840a02a06,0x40048a140504150a4081,0x42408181300281305801,0x50a02861006821006821,0x7c3485102a0a089408,0x642e105c10c85c20a828,0x20a829000912044a0a04,0x822507066203830a4198,0x8c344a14644a15870283,0xb0605a250a2414aa0e0,0xc300962088402b004418,0x6c141608802004884604,0x81430b8142a00240a186,0xc1540048982200801225,0x6800a0d88220be0c310,0x30306191a06170d13036,0x80441850950312060b,0x206130580140592a063,0x70780170c080a04b0c05,0xc4e07043c402809c1a17,0x2e34260ec36103d0c8,0x5e0b109050138342108b,0x56270780221432c382f,0x20dc1620ec4e0b0e0dc,0xc8cc461c1783c0110c,0xa0270587c0830647c37,0x78018109344e0060405,0x138382e005c60f12b83,0x82108a45e00883e00642,0xe19268bc4e1e0b82161f,0x80220b864923e13060f8,0x34178382248bc1e00604,0x1011783c00c0a06e0917,0x80181420080bf0030286,0x2fc011081e0c12709c1,0xa1f0104460f0845e0f00,0x8d821c0f0682e0c1f84e,0xe0880d6108bc1e011b0,0x438370648c21178046c1,0x100cc191f0845e0e088c,0x40670645e061382461f0,0x5c0095184e0860421828,0x9c1c108434323b89c1c,0x108450521409c1e06083,0xe3a14401a0501383c0c1,0x101aa27043182108c0ac,0x17102fc1e030c704e0b8,0x3c0a20486e0f002e1813,0x824ae06082e2f0780170,0xc0819050130417e0f028,0x6421705c00b888ee0e0b,0x80171414040bf0780191,0x81404e0f002e191b0d81,0xe0038aa281495c1c1700,0x2e32281382a1f020a322,0xa0a03c17002e301b8217,0xe031030303b8217e0088,0x50f70780170c0a196187,0x831c00b8c220c30f8017,0x15861ee0f0030171b89c,0x10c70044287c3c0a0481,0x409c12370090f12813c0,0xc19186c260b8245e011b,0x16381e0d05c26081fc1c,0x5901a0c828098322f070,0x5c023140d046130445e0,0x11b16403309822391782,0x46c59019c21288bc1e01,0x1916440b80180c2fc4e0,0x8638046058fc00906c3e,0x270f8407837060a3c142,0x408e003850902411c007,0xa1204f040e0e1789c30,0x481f05c1830f46c17078,0x121789c304e0b821618,0x13820470024285c45c40,0xc707800b1c044ae0f003,0x62fb63d4be72f2478c3c,0x31e12eeff6d7b3bd85ea,0x4f45b9ebcdde5572278e,0x3c47e0ef0177dbbd5dda,0x6e4f6c1b48d8f6bf75a7,0xab2d3b697b469a1ccf96,0x74734f97dcae64ef2238,0xdec5ee2730d3848c1860,0x3efcb7b2bcd5dc2ec374,0x9b86dbd6dbb6b3b4dda3,0x2ce9665b26d8d6c175f3]) else (word80 [0x530d8818381,0x30682014507016098004,0x8a1c0550988207186120,0x82e1001702b0c14c4142,0xe822511040bb0c20e500,0x205025874022b10610a0,0xa804a220a200cb0c3833,0xc2250188902410b060b])))
def g239H8 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x4a8,0x239163fbe94d75c58,0xd000f3c21461c71fc543,0xa9f8922bd48144351088,0x662024357000e55bbd22,0x2530411e9f44a93263bd,0x110b0e29c6a36ac2661,0x10f41c2ca1302170fb1,0xac29c5a71d000907c8cd,0x2e1ab000045116000958,0x546c1500000030000000,0x73eda24098068a58ad0,0x25d1774063175e03dd4b,0xa27a4f64ca1883f93709,0x292dc8bd0d35680365fe,0x47b8a4879bf000959442,0x660000050f533d1d5b63,0x8f3a92a991c43ca4000e,0x3571ba4e00020c004f02,0xb12000f19000608f05a2,0xf00000000a0006496b34,0xc180eb23a52a64f90d28,0xf20026a34f1ed3355,0xd998013d59a04bc00222,0x54001047441f0a200412,0x4041264a0838c5c00101])
def g239D9 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then (word80 [0x1b006060,0x4c1c01817142414121b0,0x700607064412c0c10e18,0x2a140c2710190b070088,0xa00c4c3c209c1211c151,0x4b07003860a05c4c342,0xc1c017221a1513004b04,0x38700c4c3c209c1201c2,0xb130d0b04846054412c1,0xc00e182b0c1b110b0700,0x1488904c118211018170,0x70060518c0171d104b07,0x5c38589060485c012c,0x10e20045c4b0038406c0,0x181d0c2415101a0b0700,0x48844c006c1181710030,0xc27060884706c4c01782,0xc11821202415121b060b,0x48814c017c12118181,0x91307006050ac4c3c182,0xc0171c24147a0b110f03,0x460906c017c418c1210,0xb20188b110f060b00608,0xa090546c1c01b1c5024,0x140d1a0b070048917044,0x6c0c182121f07005c6c4,0xc1c0141210082b03046c,0x50ac4c382c1211a0b004,0x87440ec4c3c182211b00,0x607431a0543c0c482c11,0x821242b130e0b07005c7,0xac4c382c1c0171c1826,0x160b030448782c0c1171,0x21710170f060b005c70e,0xc4c3c182c0171c50145f,0x30460602c1c01718146,0x50f120b045f00608c418,0x1705c1c00b1c48390e0b,0x7005c70206c4c3c1c01,0x71c24148b106307002c8,0xac1c01b10120e0b0700,0x605c7172246c418c1c00,0xb20480f07006c5171113,0x6c0181b130f08181707,0x70786c4c3c2850fc12,0x18170700605c4c3c206,0xc00d1b130f0b0418306c,0x4c305c106c01a1214205,0xc4300607c6d62930bd81,0x8bed5e32e7d700b5d59b,0x2c4d5e0ad155b2a6d4f0,0xa5551127cd3909954b52,0x4fd248911477234d1788,0xa9447218d0888193f71e,0xfcf307853b51d4ce6871,0x93771b3cd68691339194,0xcc7061d2fb178cb985b9,0x2d115fcac8555299146c,0x9f84d925b126c9084652,0x1f106c7f03d91d90e4c7,0x36d1ab0cec65030d17,0xf0b5c57029913d098c48,0x822510507cc3a01b10c9,0x5cc2a013d08f03ec1c8,0xc9055021c0e005501d0,0x7c000ffee8b2ffc7459,0x7feb2cc9ff59564ffeea,0xb07fd75583feb2ac1ffd,0xd160ffce8b07fd74583f,0xe3a2c1ff99160ffac8b0,0x7fe54583feaa2c1ffdcd,0x60ffae6b07fd63583ffb,0x22a1ff99150ffac8a87f,0xc64543ffb1aa1ff58d50,0xffacba07fd63d03fea9e,0x81ffdd540ffacaa07ff7,0x3503feb1a81ff54d40ff,0xec8987fe644c3feb2261,0xff19130bfae9b2dfd70d,0x96ffba2cb7fdc165bfae,0xbb25fd70d92febb4c97f,0x5d664bfae1325ff75593,0xfbb8ac97fdc164bfaea3,0x25fd70192febb4a97f5c,0x254bfeecaa5fd76553be,0xb2aa9fbdc954bfee0aa5,0xfd75d837eb2ec17f5d36,0xbfae7b05ff755837fb2,0xac1bf59560bfee8b05ff,0x735837fb1ac1bf58d60b,0xfeeca85fd76543beb2aa,0x17fdd150bfee6a877d53,0x542febb6817f5d740f7a,0xc9a07bd54d02feb9e817,0xfdd940bfaeca05ff7550,0x2febaa81ef99140f7ac8,0xa07be54503deaa2817fd,0xcd40f7e86a07bd43503f,0xcb02817f5d930bfaea98,0x5fd744c3fcb0261fe541,0x30bdae5b2ebf64992fbb,0x8ac95f5d464bdae4325f,0x571192fcb80c97bdc954]) else (word80 [0x512c1c0,0x170e1824104b04388460,0x6434244c1c08517201a0,0x10d0913045c848174544,0xc1c01e181c5d150c5219,0x13070060945028506174,0x4c1c0182438171307005,0xc8871e0e17c4c382c121,0x20783887130e0b07005c,0x90e0617c4c145c022201,0xa120e0b0701145c84084,0x8382c117211c79100b04,0x846061e1dc1c01718191,0x45f106307010c7881745,0x43c4c118c022207c7a15,0x1463105f050f001a08c4,0x31409830a4582c084c14,0x62d0c502a0d1a1307020,0x914a208343140a094645,0x84c182c030520d0c2916,0x1307020918a178545031,0x482c0c14612291917070,0x486c604c12118107e11,0x110f06086084886c1c00,0xe851b181307005c605c1,0xc017181310630702085c,0x61f0584444382c118c01,0x7280a1a170700386c70e,0x984448245c1c0468b28,0x391a1112085f0701162c,0xa84820e4421094645c1c,0x8b2e120861111707022,0xd18909c1182110145f04]))
def g239H9 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then (word80 [0x80000000,0x32a3c9b000559d0b96,0x6000000000000000019,0x99d16000000000000000,0,0,0x44e51a0000000000,0,0x71700000,0xa0,0x6800000000000000014a,0xe0000000000000000000,0,0x52400000000000000,0,0x107200000,0x46,0xa2d4800000000000030b,0xe3b,0x52800000000000000,0xc8d0420,0x181c00000000000,0xb0a000000000000,0x38c123e000000595000,0x1c2f0000003e68277000,0x93e00020bc,0x50615400000000006,0x2000000091c80000000,0xd14e0fc00000065100,0xc7a000000000018,0x80004094924169000000,0x2eaa000,0x8b40000000000000,0x126a2080000000,0,0x94f0000003c09a8300,0x70480000000000002e6,0x40001238000000000d8e,0,0,0x1c11000494c001b,0x870000002442000c4b80,0x70e42800000000,0x20be000000000,0x28cee606288000000000,0xf0800030d8e310000000,0x29c5,0x2d000000000000000000,0x1b0940f14,0x9f167b0b45600000014c,0x40000000000000000000,0x1cd80000000000000000,0x4bc0,1,0x7700000030f2000d0c80,0xe6a000f52800000109,0x5000700807a000000000,0x5c000632,0x1140000,0x6dc0000000000000d620,0x62600000,0x54,0x38000f50000d48000000,0x12493bf0003870000000,0x2dc0001f3300059d4000,0x147fb138,0x30d20000000003c160,0xb4f005611471600000,0x33,0xb0007210000000c28488,0xc00000000000028ba000,0x5120000001d990000002,0xc6c00000059600000000,0x606800000000000000,0x4a8c00000000,0xd2,0x20000000000001635caa,0,0xb548000000000ac18,0x48ac0000,0,0x98b000000000000,0x3b1969a84b000,0x61c7826000,0x5992c800000000002,0xcfce3300058740000000,0,0x140a0000003d0200003,0x78000000a7d000000000,0x18fbcd6000d36,0x80032a40000006df7454,0xab400000000000000,0x72740000,0x7c000,0x7e0400000,0,0x7328000000000,0,0xa3c000c,0x1cc3400068c00000000,0x450000a3c00000001,0x401019008018c000002,0x18244010001408240]) else (word80 [0x15300,0x38f0000b10049400088,0xeb9c800000136b000000,0,0xe208000,0xe0f00038ec0000,0x1a2e00000000000,0x1e000000000000,0,0x24a0000002ce924f000,0,0xa100000000000000004,0x224001a9fe2200000000,0x3bfd154001c1f00000,0xa71c80000488800000,0x2a9000145b000000,0x1d970000000000000,0x1c869150000001,0xa6fa1600029ec0016260,0,0x1407000206000000000,0xc36000000000309,0xc0000000000000686b54,0,0x59300008c6000a4a0,0x610007c280000,0xcaaf0480,0x1e37000000109600,0x329ed30000000000,0x1888,0x1a000005a64,0xa7a0000000000000605f,0xa9d8e94dc00000000000,0x140100049a14a400000,0x4e681c000000146]))
def g239D10 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x1418242,0x5c2408260314141820c1,0x2041304090b121c28300,0x3101a24385060051c305,0x890e1098105092101828,0x90e10683002941818242,0x120c0301490c0c105085,0xe04130485425e243820a,0x624286890e08280386,0xa0ca04800a092243218,0x90e082801480c162432e,0xa0c0203050462241802,0xc8d270bb369694605701,0x7b4d8ff2e87c0f800ffd,0x97fd65ffd93fe64ff593,0xfc64ff953fd54ffd83fd,0x60ff543ff40ff503fd30])
def g239H10 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0xd100023930a0,0xa65000,0xb5000,0xe5c0000000,0x51c000000000000000,0xd5200000000000,0,0x7a5004000112000,0x71500000044d00,0xb,0x57000f0b000000000000,0x454000a0900000000000,0x8270000000000000000,0x1d2000000,0xd14000000000c4e14500,0x2553580,0xb33f0d2af000000000,5,0x90000000000008420080,0x8d40004da3ad000000,0x32a00000088f00000000,0x410000007250000000,0,0x2640b8000000000d016d,0x50000000000002290000,0x9200000065b0dc000,0xa2,0x1f38000000000395e510,0xf1122c000000,0x59700085e00000,0,0xc94000,0,0xc5300049a0000000000,0xf22000abe000,0xea100000000011,0x51300000000000043c0,0x6bb000000000000,0x93b000516e2b00000,0x2d90,0x507a9b,0xc370000000d300000,0x52e0000000,0x33a000000,0,0x81e000000000e910000,0xa23000000000a354a9,0x4b00061d0008db00000,0x80c000f1f0,0x720000,0x24300000000,0,0x5cf0009c2000,0x6100000000061a4939c,0xe000000026c03f280000,0x240000000c600002b6,0x50600000023600000000,0x15f0000000000000,0xd00000000000000,0x45d000f2f00000000000,0xb81000000000c,0x1b000000000000000000,0xfcd00006700000,0x3e00000033d7630001,0x3100000000080f288d30,0xfcb202e4800022,0xd766000000000000db40,0x3c9000000000000000,0x517d050003c000034400,0,0xa89000,0xed051900064903f00000,0x74f0,0x54a000,0x9c82e1a4,0x6000000c320000000000,0x4181a8e34656,0x94c00000000020e00036,0x2000ca20000005240000,0x84735a000000000000,0,0x8490410,0x8010293100000040400])
def g239D11 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x81840802ff
def g239H11 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x21e62000,0x3d000635840123002,0xaad66d00000000000001,0x2600b480384000000000,0x6000abe4b2802e800,0x2c8000048])
def g239L : Nat → Packing
  | 6 => (13,5,6,0,0,8,0,g239D6)
  | 7 => (101,4,6,0,0,11,0,g239D7)
  | 8 => (171,3,6,0,0,13,0,g239D8)
  | 9 => (104,2,6,0,0,13,0,g239D9)
  | 10 => (14,1,6,0,0,10,0,g239D10)
  | 11 => (1,0,6,0,0,0,0,g239D11)
  | _ => emptyPacking
def g239I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 3 23 2 9 4 1 g239H7
  | 8 => lookupWord 32 149 7 12 7 1 g239H8
  | 9 => lookupWord 56 829 3 13 8 1 g239H9
  | 10 => lookupWord 36 547 3 12 7 1 g239H10
  | 11 => lookupWord 4 53 2 9 4 1 g239H11
  | _ => fun _ => none
def g239 : Forest := ⟨239,11,fun i => g239Y[i]?.getD (0,0),g239C,g239A,g239L,g239I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239P6_0 : block g239 6 0 13=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g239B6 : block g239 6 0 13=true := g239P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239P7_0 : block g239 7 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239P7_3 : block g239 7 3 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239P7_99 : block g239 7 99 2=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g239B7 : block g239 7 0 101=true := (@block_merge g239 7 0 3 98 g239P7_0 (@block_merge g239 7 3 96 2 g239P7_3 g239P7_99))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239P8_0 : block g239 8 0 10=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239P8_10 : block g239 8 10 70=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239P8_80 : block g239 8 80 91=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g239B8 : block g239 8 0 171=true := (@block_merge g239 8 0 10 161 g239P8_0 (@block_merge g239 8 10 70 91 g239P8_10 g239P8_80))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239P9_0 : block g239 9 0 8=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239P9_8 : block g239 9 8 60=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239P9_68 : block g239 9 68 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g239B9 : block g239 9 0 104=true := (@block_merge g239 9 0 8 96 g239P9_0 (@block_merge g239 9 8 60 36 g239P9_8 g239P9_68))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239P10_0 : block g239 10 0 14=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g239B10 : block g239 10 0 14=true := g239P10_0
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
  · exact g239B6
  · exact g239B7
  · exact g239B8
  · exact g239B9
  · exact g239B10
  · exact g239B11
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239G : graphValid g239 (boundsBefore K223) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low239 : Lower true (varsX 239) (graphGoal 239) 12 := lower_forest (g:=g239) (i:=0) (hints:=1049939) (before_sound K223 V223) g239G g239T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K239 := extendKnown K223 12 [(239,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V239 : Known true K239 := extend_ok (m:=239) V223 low239 (by decide +kernel)
def g247Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x8366c3359803cd000,0xff0000ff000000ff])),(BitVec.ofNat 152 (word80 [0x816683159000c1005,0x5050505050505050505]))),((BitVec.ofNat 152 (word80 [0x4f4a6867855b401000,0xff0000000000ffff00])),(BitVec.ofNat 152 (word80 [0x454a68270503001011,0x11111111111111111111]))),((BitVec.ofNat 152 (word80 [0x1727e208320d8a7200,0xff00ff000000])),(BitVec.ofNat 152 (word80 [0x1727e00822090a5043,0x43434343434343434343]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xf2a04dd88e21110600,0xff0000ff00000000ffff])),(BitVec.ofNat 152 (word80 [0x12a005c0820011020a,0xa0a0a0a0a0a0a0a0a0a]))),((BitVec.ofNat 152 (word80 [0x899534d41346622bff,0xffff0000])),(BitVec.ofNat 152 (word80 [0x889014d0104460232c,0x2c2c2c2c2c2c2c2c2c2c]))),((BitVec.ofNat 152 (word80 [0xc41a93a66070a8ac00,0xffffff00000000])),(BitVec.ofNat 152 (word80 [0xc00812060070a0acb0,0xb0b0b0b0b0b0b0b0b0b0]))),((BitVec.ofNat 152 (word80 [0x30c990090098855dff,0xffffff00000000000000])),(BitVec.ofNat 152 (word80 [0x200180080098804cc0,0xc0c0c0c0c0c0c0c0c0c0]))),(0x0,0x0)]
def g247C : List ColumnInfo := [(1,0,246,0,10),(2,0,245,0,10),(4,0,243,0,10),(16,0,231,0,9),(32,0,215,0,9),(64,0,183,0,9),(128,0,119,0,9),(0,4,147,96,7),(0,32,81,134,7),(0,64,162,21,7),(2,32,81,132,6),(4,32,81,130,6),(16,64,162,5,6),(80,0,167,0,6),(128,32,81,6,6),(160,0,87,0,6),(96,0,147,0,5),(96,4,147,0,5),(130,32,81,4,5),(144,0,103,0,5)]
def g247A : List (List Nat) := [[],[16,116,101]]
def g247D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x29f3a05d7815d163
def g247D7 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x380,0x1e202139360ecbe0f0f1,0x7c752280cfbbaf02ba2,0xc79f575e057458efb720,0xc2ac6a1d3725d6558d43])
def g247H7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7
def g247D8 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x10a108242285809690,0x60e0c0997103030d6560,0x48c414a6938384385e5c,0x3e2e012142c1f1a92970,0xf83848c4c309e2e1e0a5,0x1e978b8313869b0c765c,0x4e2e0e10e0c1e9b0f8b8,0x285a5c407c3e0e11a58,0x88a0c7b9c064964478e0,0x288640d800dff755d163,0xdfd755d163bff8755163,0xfdf8558d43fdd8558d43,0xaff865d163bf7815d163,0xbef82551639fd86dd543,0x9fc8759543edd6558d43,0x9f7815d9439ef825d543])
def g247H8 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x16001000,0xd4c000000000401])
def g247D9 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x665498,0xb00ec24c81e332c3498b,0x611c493238b0611c307,0x1a247888a91343c58701,0x617062c23070d831611c,0x305c3806111010ec1846,0xb184858d8a1e0c22081,0x11362c18468e93043c3,0x8870c242c3c58308e1c4,0x854d0f160c22080d121e,0x1c18848e961e0c38870c,0x321e0c49b0881c1e0c38,0x870c181e5898b0611c38,0xb0f9b1c5c113091ebf25,0xade116c55f46cbb0fbd0,0xdc302a1a186e14a3a87c,0x7ff7458ffeba2c7ff5,0x5163ffac8a9fff7550ff,0xeb2a877fdcd54fdee4aa,0x5ff7458effbb2a77fdd1,0x53bfeeca1dfd7650effb,0xaa877f5d543f7ac8a1fb,0xd5450feeb1a877bdc954])
def g247H9 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x680030eb8860050,0x58ecb000000000000000,0x71464000000001300,0x926a800000031400000,0x5b0000094f800000839])
def g247D10 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0xe,0xe614c1208622659060e,0x28211cd2669031618222,0x4694e0c4822848a27236,0xff553fd63ff54ffd43])
def g247H10 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x3d100,0x1c223ecbe2bac00283a2,0x40000287214004860118,0xec0f236ab48c641066e8,0x80000250dc400d930e83,0x400002b26300040c0020])
def g247D11 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3148310023ff
def g247H11 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x280099ec0000,0x164000c514000])
def g247L : Nat → Packing
  | 6 => (1,5,5,0,0,0,0,g247D6)
  | 7 => (4,4,5,0,0,7,0,g247D7)
  | 8 => (13,3,5,0,0,10,0,g247D8)
  | 9 => (19,2,5,0,0,10,0,g247D9)
  | 10 => (4,1,5,0,0,8,0,g247D10)
  | 11 => (1,0,5,0,0,0,0,g247D11)
  | _ => emptyPacking
def g247I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 1 2 0 4 0 0 g247H7
  | 8 => lookupWord 1 17 0 7 2 1 g247H8
  | 9 => lookupWord 4 41 3 9 4 1 g247H9
  | 10 => lookupWord 7 41 4 10 5 1 g247H10
  | 11 => lookupWord 1 23 0 7 2 1 g247H11
  | _ => fun _ => none
def g247 : Forest := ⟨247,11,fun i => g247Y[i]?.getD (0,0),g247C,g247A,g247L,g247I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P6_0 : block g247 6 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g247B6 : block g247 6 0 1=true := g247P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P7_0 : block g247 7 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P7_1 : block g247 7 1 3=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g247B7 : block g247 7 0 4=true := (@block_merge g247 7 0 1 3 g247P7_0 g247P7_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P8_0 : block g247 8 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P8_2 : block g247 8 2 6=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P8_8 : block g247 8 8 5=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g247B8 : block g247 8 0 13=true := (@block_merge g247 8 0 2 11 g247P8_0 (@block_merge g247 8 2 6 5 g247P8_2 g247P8_8))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P9_0 : block g247 9 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P9_1 : block g247 9 1 12=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P9_13 : block g247 9 13 6=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g247B9 : block g247 9 0 19=true := (@block_merge g247 9 0 1 18 g247P9_0 (@block_merge g247 9 1 12 6 g247P9_1 g247P9_13))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P10_0 : block g247 10 0 4=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g247B10 : block g247 10 0 4=true := g247P10_0
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
theorem low247 : Lower true (varsX 247) (graphGoal 247) 12 := lower_forest (g:=g247) (i:=0) (hints:=1049924) (before_sound K239 V239) g247G g247T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K247 := extendKnown K239 12 [(247,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V247 : Known true K247 := extend_ok (m:=247) V239 low247 (by decide +kernel)
def g251Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x821209d867fcc18010,0xfe0007f0003fff])),(BitVec.ofNat 152 (word80 [0x2120850662c400000,0xa142850a142850a14285]))),((BitVec.ofNat 152 (word80 [0x22af700644067ca210,0x7f0000000fffc000])),(BitVec.ofNat 152 (word80 [0x2077006440620a012,0x64c993264c993264c993]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x18c58a81005dacbd80,0x3f800003f80000007f])),(BitVec.ofNat 152 (word80 [0x188182810050acad01,0x42850a142850a142850a]))),((BitVec.ofNat 152 (word80 [0xd022269a3800be4c60,0x1fc00001fc00001fff80])),(BitVec.ofNat 152 (word80 [0xd020028800009e4c21,0x2040810204081020408]))),((BitVec.ofNat 152 (word80 [0x15b99b69ac12c842af,0xe000000000000fe00000])),(BitVec.ofNat 152 (word80 [0x11b88b49a810c842a5,0x8b162c58b162c58b162c]))),((BitVec.ofNat 152 (word80 [0x6154172748a10167d0,0x1fffff0000000])),(BitVec.ofNat 152 (word80 [0x2144152608810102de,0x1c3870e1c3870e1c3870]))),((BitVec.ofNat 152 (word80 [0x3f00c064938102186f,0xfffffffe000000000000])),(BitVec.ofNat 152 (word80 [0x240000201181001048,0x10204081020408102040]))),(0x0,0x0)]
def g251C : List ColumnInfo := [(8,0,243,0,10),(16,0,235,0,10),(64,0,187,0,10),(1,0,250,0,9),(32,0,219,0,9),(2,0,249,0,8),(128,0,123,0,8),(0,2,73,176,7),(0,32,89,130,7),(0,64,162,25,7),(10,0,241,0,7),(18,0,233,0,7),(96,0,155,0,7),(160,0,91,0,7),(1,64,162,24,6),(2,32,89,128,6),(8,64,162,17,6),(32,2,73,144,6),(33,0,218,0,6),(34,0,217,0,6),(65,0,186,0,6),(66,0,185,0,6),(128,2,73,48,6),(128,32,89,2,6),(3,0,248,0,5),(48,2,73,128,5),(97,0,154,0,5),(129,0,122,0,5),(130,0,89,0,5),(130,32,89,0,5),(160,2,73,16,5),(162,0,89,0,5),(192,0,59,0,5)]
def g251A : List (List Nat) := [[]]
def g251D6 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x6c204000002df0,0x429715fae5088e00b0fe,0x999059774586d2fa2641,0x65dd161d1bddb9260165,0x506a79a0e6165dc560f1,0xce8165dc671583a3ba05,0x97845c560e8ee8165e11,0x6158307798595711c560])
def g251D7 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x87070607842142c1,0xb8409c3b08270dc00b84,0x6c3408224c87b0ec013,0x6074460c2126420903b,0x8260c1126420b441264,0x20c20060640c2058151f,0x449083523445443d1147,0xa49320c7d0983f03c11,0xe4f91783f0016f046922,0x47619c2f0383f047f081,0x6f04391783f0016f0459,0x224741982f0383f04706,0xd87f0384f0417181b623,0x3f00c961fc11ec480fc,0x5a85f046f0bc1f000f,0x58594524a3c45e8890a,0xa0d4007a4f09d438e6e8,0xd91a532662cbf1762c85,0x48a291f1fc360630aa10,0x818c1e81c000b3fcb300,0xb2cc376f9260165986cf,0xf2cc02cab0ddbe498059,0x561e9fc82cbba2c3d3d9,0x59774586edf24c02cb2,0xf1fddb8059541e3fbb3,0xb2a8376f9260165507,0xcf720b2ee8b079ee4165,0x5d160d3fcc2cbb8ac1e7,0xb9059771583cf720b2ce,0x2b079ee41655c560d3fc,0xc2ca38ac1e7b90594715,0x83cf720b2cc2b079ee41,0x6558560f3dc82cb20ac1,0xe7b9059541582cf32040,0xacab071d597719c560d1,0xeb2f08b8ac11f7985c47,0x15838eacab88e2b068f5,0x978458560e3c4bacab02,0x81c789759560443ce2ca,0x40ac08846d6637190540])
def g251H7 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x9803,0x814000003acf600123c7])
def g251D8 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x832158616a10b0661b,0x2c85141c878321708c,0x3a10f06c230d8087428d,0x8461d09228814358461b,0x122881a0d8461a4d0f4,0x2183506c230d8093438e,0x1723917800ee0c347241,0x138016e08386e07041c1,0xd10124722f0287c1468f,0xc0e091b0a224885c0e08,0x383a306d88420ef03821,0x607101b0bb3e0cc42170,0x382c5071416a1703820e,0x868d448193381c10d874,0x724e0d840de07043a3d1,0x206c20ef002dc10d901b,0xe117844fc1f0382406c,0x2f4f24b082dc4c1f0383,0x452c9fc222e0f81c10b0,0xe1de07042c18143649c1,0xd1185c00ef042c484706,0x48e170382161c2f4f033,0xb8903a2f03821b288b8,0x3e170382161b068206f0,0x383450b0f44c1a0b81c1,0xb07472411c230682f0b,0x8183e09344c1a0b81c10,0xb8787a260d05c0e08583,0xe3d090e850bf0307c186,0x91c0e08383a250892884,0x270307c10b10c481f0b8,0x85e0858727f108bc0e0,0x8386e07041c161381c10,0xa8384c11228a51e07041,0xc382781c10d0982c6d0f,0x8210158508e1e162286e,0x7048e170038191385c0,0xe091822281d0bc2e011b,0x82370b8046e084450401,0xf87c2e07041a385b87c0,0xe0a4c58381385c0e087c,0x60703781c10a0ac4c1f0,0xb81c1830c170b50b89c0,0xe08387e17008bc10b0b0,0x3c230b81c10e8d83e170,0x38216140c0e6107789c0,0xe08588e3de0adc5d89d5,0x6d1acdec99c54c18beeb,0xa9b7fb43af5a95a59a14,0x9cf9819338ca8858527f,0xb7b675671a6d56906395,0xf45af5615374e94a4468,0x43e4143cf3a53723242f,0xa2c728b2582131e01a41,0x711350f00bd08104e000,0xf7f8059661f7d8059661,0xf7f8059561f7d8059561,0xf7f8059641f7d8059641,0xf7f8059541f7d8059541,0xb7d80dd165b7d80dc565,0xb7d801c565b7f865c165,0xbbd80d9241e7f8459560,0xe7f8159560e7c8159560,0xf7b8059560e7d65dd160,0xe7d655d160e7d65dc560,0xafd869c560e7d659c560,0xdf7719c560aff865c560,0xe7d655c560bbf845c560,0xe7d651c560df5711c560,0xe7d6598560e7d6558560,0xbbf8458560e7d6590560,0xe7d6550560d7c8759540,0xd7f8759710d7c8759510,0xff08158110a7d869c565,0xd77719c565a7f865c565,0xb3f845c565a7f865c165,0xb6f825c165d3d65dd161,0xb9d831d161cbd76d9241,0xbb581d9241eb76458641,0x9bf845d941c7f7659541,0xeb56458541c7f8759760,0x9bf845c760e7b8059560,0xdb77190540e796558140,0x9bf845d910e796558110])
def g251H8 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [1,0x1a0f800003482bf1f663,0x980000be6c8000000b5,0x6810ea4001d54c41d42b,0xc1b4226638fbd13b8da2,0x2b006a6647891004218])
def g251D9 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x44c2c0c11b1d1848,0x370b0304746c41dc2c01,0x6c11b1c6e0c5b0b03047,0x471b4483c4c21dc0c116,0x245c18593f11170b0304,0x6ca83c20dc0c145161d1,0x20f0b0304587474483c2,0xc0c1171e1d120f0b0304,0x587c782440ec0c11d183,0x303043874582c41d0ec0,0xc1161f0304387441d44c,0xc1160e185a083b03047,0x4617164543828dc0c10e,0x245c59160a350f030424,0x907c2c006c10f1a10183,0xc5b0b03050c80743c2c0,0xc10d18101f0b03047464,0x2c385c00dc1161c230b0,0x37044c6040f43c2c0c1,0x161d08370c5b03047470,0x8c2c00dc11118101f0b0,0x30470607c2c0c11c1413,0xb0304443c604c2c0c11,0x10f190f0b030474505c2,0xc0c10d170b0304445c58,0x442c317c0c11e1f0b030,0x61518504c2c0c1111719,0xf0b0304785c0c2c1161,0x3141f0b03047c5420dc3,0x16c0c11f1c20170b0304,0x7c613c2c0c10d0f181c1,0x30b03047c68443c2c0c1,0x1f1a0f0b03041c346421,0xd1683c0c10d1f0b03043,0x43c5c211c083c1161b03,0x448744c2c0c10d0f150,0x83a0f0304746c2c0c10d,0xf17020f043c585c2c04,0x583c117180e130b03047,0x4683c2c0c11d15083a0f,0x30474644c083c113171,0x9120f0b0304746041dc2,0x83c0c1161c120c5b0b03,0x4447420e1dc483c0c11,0x62113020f04445c683c2,0xc044c11619103f0b020f,0x458744c283c011c1161,0xc0c1b10770b030458844,0xc0c1111d14583c381b02,0x130470785420ec0c10d1,0xf0b0017043450886c385,0x11c0c2c1203817030434,0x5c2c005c10d170b00342,0xc4c2c10a0d10170b0304,0x3451d160983c0c10d1c7,0x4583a0f030434706420e,0xc4c083c11e2c112a8764,0x2ba0c100a7e63e39ea0f,0x1276e3ab9ce0e4a70a37,0x79b20d426863319920c5,0xa60e2f99750b6a59a2bf,0x95a0a9a53228d94109da,0x4ce25b927090a46e22b9,0xe083a4021f38f307623,0x921bd8d8069a33618d8c,0x105da2d215b8a8050a26,0xa12788c04221ee0e986e,0x33217a0ab8500242102,0x75832016209a04381d0,0xba03e00f8001ffdd160,0xffae8b07ff71583ff38a,0xc1ff5c560ff8e2b07fe6,0x1583feb0ac1ff90560ff,0xa82b077f74597beba2cb,0xdfdc565efce2b2f7d715,0x97be38acbdfdc165efae,0xb2dfd71d92feb86c97f,0x5c361bfaed30f7d65986,0xfeba4c37f5c261efacab,0xdff74587dfba2c3ef1d,0x161dfec8b0efd64586ff,0xb82c37f5c061bfaed20f,0x7d65907dfb2483fd5864,0x1bfae120dff76506febb,0x283df59541f7ac8a0ff6,0x61507fab0a837fdc141b,0xfae3b077d65582ffba2c,0x17fdc560bfeeca05fd76,0x503beb2a81ef59140bfe,0xe2a07be41503fcb02817,0xf5db10efacb885fd74c4,0x3fab0e217fdd910bfaec,0x8877d65442ffba2217f5,0xd110fecc2887f561443f,0xcb0221fe50110afaebb2,0x57d75d877bb0cc36fdd1,0x61afaea30dbd74186eeb,0x98c37b5c861bf2e030d7,0xd75d833eb2ec19f59560])
def g251H9 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [3,0x26b00000000e1c00000,0x730004840000000001,0x20000000000000000,0x571ca0036710f,0xaf000000000000000000,0x25ec3c9f00231000,0x9040000000000daa8a,0x65eb9190036945800000,0xcb611d9000134,0x3f7d2c0095000743,0xa61a0005c149ada6a003,0xc647400610004391724c,0x3d5003e000375ecc,0x3c500000000008d2,0x720000000298003eb000,0,0xe8fb9b6c,0x9e0,0xb490059200e13])
def g251D10 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [2,0xc3c2c381082410c49e1e,0x161c281046901c2c3850,0x208d1c7c31b021410a38,0x40e1618d850209d24203,0xb0a0411a38d870a0410,0x8147261c28d870024282,0x48507021411a3051a0e1,0x40823060a120038504e9,0x187c407021410a4060b,0x120038504f100a18d810,0x45b9ea99ca3b7d9bf621,0x4344ce3294670a400ffd,0x93fd64ffd87fe61ff587,0xfc61ff907fd41ffd83fd,0x60ff503ff10ff4437d65])
def g251H10 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x111da3,0x214000efc00628000002,0x9a7a0000000531c131d4,0x6cc4fb1000e065780028,0x5ea800000e6c0001159e,0x1880014371c000000005,0x3d000000000000000000,0x8340035f000f240e,0x3a620f042a000004b466,0xab000696b2a001c6d497,0x6ba200064e0004c326d3,0xcd90e280000072e0008f,0x800e4fcdc000009202b8,0x5b9a53a74000020002,0xb7a1dca00121f81a9989,0xe61342924f7444e05811,0x565b41958,0xa5446e6000000001b002,0x28003180000073b08046,0x2dc00028641842050c44])
def g251D11 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x81801022ff
def g251H11 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x740000590000fd000000,6,0xbc000042000000000000,0,0x40,0x7ac300000000000000,0x31fb000000000000,0x35000000000097,0xe80000000000,0,0])
def g251L : Nat → Packing
  | 6 => (8,5,6,0,0,7,0,g251D6)
  | 7 => (32,4,6,0,0,11,0,g251D7)
  | 8 => (58,3,6,0,0,12,0,g251D8)
  | 9 => (81,2,6,0,0,13,0,g251D9)
  | 10 => (14,1,6,0,0,10,0,g251D10)
  | 11 => (1,0,6,0,0,0,0,g251D11)
  | _ => emptyPacking
def g251I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 2 13 3 7 3 0 g251H7
  | 8 => lookupWord 8 41 4 9 5 0 g251H8
  | 9 => lookupWord 14 149 3 10 6 0 g251H9
  | 10 => lookupWord 20 131 5 11 7 0 g251H10
  | 11 => lookupWord 4 127 0 8 4 0 g251H11
  | _ => fun _ => none
def g251 : Forest := ⟨251,11,fun i => g251Y[i]?.getD (0,0),g251C,g251A,g251L,g251I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P6_0 : block g251 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P6_1 : block g251 6 1 7=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B6 : block g251 6 0 8=true := (@block_merge g251 6 0 1 7 g251P6_0 g251P6_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P7_0 : block g251 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P7_1 : block g251 7 1 9=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P7_10 : block g251 7 10 22=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B7 : block g251 7 0 32=true := (@block_merge g251 7 0 1 31 g251P7_0 (@block_merge g251 7 1 9 22 g251P7_1 g251P7_10))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_0 : block g251 8 0 21=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_21 : block g251 8 21 29=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_50 : block g251 8 50 8=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B8 : block g251 8 0 58=true := (@block_merge g251 8 0 21 37 g251P8_0 (@block_merge g251 8 21 29 8 g251P8_21 g251P8_50))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_0 : block g251 9 0 12=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_12 : block g251 9 12 59=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_71 : block g251 9 71 10=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B9 : block g251 9 0 81=true := (@block_merge g251 9 0 12 69 g251P9_0 (@block_merge g251 9 12 59 10 g251P9_12 g251P9_71))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P10_0 : block g251 10 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P10_1 : block g251 10 1 13=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B10 : block g251 10 0 14=true := (@block_merge g251 10 0 1 13 g251P10_0 g251P10_1)
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
  · exact g251B6
  · exact g251B7
  · exact g251B8
  · exact g251B9
  · exact g251B10
  · exact g251B11
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251G : graphValid g251 (boundsBefore K247) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low251 : Lower true (varsX 251) (graphGoal 251) 12 := lower_forest (g:=g251) (i:=0) (hints:=1048643) (before_sound K247 V247) g251G g251T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K251 := extendKnown K247 12 [(251,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V251 : Known true K251 := extend_ok (m:=251) V247 low251 (by decide +kernel)
def g253Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xd286f06c321da0a250,0xfe00000fe03fff])),(BitVec.ofNat 152 (word80 [0x282c00c020da00040,0x142850a142850a14285]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x6019c8514e56f4680e,0x600000000007f01fc000])),(BitVec.ofNat 152 (word80 [0x6018c8504c14f46006,0x28d1a3468d1a3468d1a3]))),((BitVec.ofNat 152 (word80 [0xa12c0ac09193c79746,0x40007f0003f80000007f])),(BitVec.ofNat 152 (word80 [0x2c0ac09112478606,0x42850a142850a142850a]))),((BitVec.ofNat 152 (word80 [0x1c2645f754205d2402,0xc03f8001fc0000003f80])),(BitVec.ofNat 152 (word80 [0x1c2400e35420552402,0x42850a142850a142850a]))),((BitVec.ofNat 152 (word80 [0x6e22aa31f8268c8e9,0x5fc000000000001fc000])),(BitVec.ofNat 152 (word80 [0x6a222a31382088869,0x470e1c3870e1c3870e1c]))),((BitVec.ofNat 152 (word80 [0x8b93402c1cc0c1599,0xa0000001ffffffe00000])),(BitVec.ofNat 152 (word80 [0x1340000c0081199,0x942850a142850a142850]))),((BitVec.ofNat 152 (word80 [0x6741939828201310a7,0xbffffffe000000000000])),(BitVec.ofNat 152 (word80 [0x614111102800001080,0xb83060c183060c183060]))),(0x0,0x0)]
def g253C : List ColumnInfo := [(8,0,245,0,10)]
def g253A : List (List Nat) := [[],[67],[82,118],[82,67,118]]
def g253D10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xff
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
theorem low253 : Lower true (varsX 253) (graphGoal 253) 11 := lower_forest (g:=g253) (i:=0) (hints:=2098435) (before_sound K251 V251) g253G g253T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K253 := extendKnown K251 11 [(253,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V253 : Known true K253 := extend_ok (m:=253) V251 low253 (by decide +kernel)
def g254Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfb22da18b028cc2155,0xe0c00001fc0000003fff])),(BitVec.ofNat 152 (word80 [0x4102d81090284c0045,0x80c48912244891224489]))),((BitVec.ofNat 152 (word80 [0x12aad0406d89e97c3,0x1b00000000000fffc000])),(BitVec.ofNat 152 (word80 [0x61288c0406588e17c3,0x911a3468d1a3468d1a3]))),((BitVec.ofNat 152 (word80 [0x7508d02f736115d35,0x84000fe0007f0000000])),(BitVec.ofNat 152 (word80 [0x83508d02f724105d15,0x803870e1c3870e1c387]))),((BitVec.ofNat 152 (word80 [0xf25c4ce7aac1f04140,0x69007f0003f80000007f])),(BitVec.ofNat 152 (word80 [0x25404c622c1904100,0x6903060c183060c18306]))),((BitVec.ofNat 152 (word80 [0x85814f63a014663a,0xd6bf80000000001fff80])),(BitVec.ofNat 152 (word80 [0x5014b6180106038,0x520a142850a142850a14]))),((BitVec.ofNat 152 (word80 [0x116669158062bf0a8,0x15c0000003ffffe00000])),(BitVec.ofNat 152 (word80 [0x26211080221a028,0x14ec58b162c58b162c58]))),((BitVec.ofNat 152 (word80 [0xce93272055b22080f,0xc3ffffffc0000000000])),(BitVec.ofNat 152 (word80 [0xca822200012220002,0x43060c183060c183060]))),(0x0,0x0)]
def g254C : List ColumnInfo := [(8,0,246,0,10)]
def g254A : List (List Nat) := [[]]
def g254D10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xff
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
def g255Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x7fc0000007fc0000,0x7fffe06130c0ff31e6])),(BitVec.ofNat 152 (word80 [0x48241209048241209,0x48241202110405f3142]))),((BitVec.ofNat 152 (word80 [0xff80000000000001ff,0xff80000181c314c03ec9])),(BitVec.ofNat 152 (word80 [0x1188c46231188c4623,0x1188c460814114c014c9]))),((BitVec.ofNat 152 (word80 [0xff803fe00,0x600000703c00b])),(BitVec.ofNat 152 (word80 [0x43a1d0e8743a1d0e87,0x43a1d0e200000101400b]))),((BitVec.ofNat 152 (word80 [0x1ff000000000,0x3fe0020c180400f7])),(BitVec.ofNat 152 (word80 [0xb0582c160b0582c16,0xb0582c00004000000b5]))),((BitVec.ofNat 152 (word80 [0x3fe00000000000,0xffffc000040020080301])),(BitVec.ofNat 152 (word80 [0xa05028140a0502814,0xa050280000000000200]))),((BitVec.ofNat 152 (word80 [0x3ffff,0x18380fc00ffc04])),(BitVec.ofNat 152 (word80 [0x2c160b0582c160b058,0x2c160b08280ec00ea804]))),((BitVec.ofNat 152 (word80 [0x3ffffffffc0000,0x1fc00ffff00008])),(BitVec.ofNat 152 (word80 [0xb0582c160b0582c160,0xb0582c1dc00bbea00000]))),((BitVec.ofNat 152 (word80 [0xffffc0000000000000,0x1ffff000000010])),(BitVec.ofNat 152 (word80 [0xc06030180c06030180,0xc060301756a000000000]))),(0x0,0x0)]
def g255C : List ColumnInfo := [(4,0,251,0,12),(8,0,247,0,12),(16,0,239,0,12),(1,0,254,0,11),(2,0,253,0,11),(32,0,223,0,11),(64,0,191,0,11),(128,0,127,0,11),(10,0,245,0,10),(0,4,155,96,9),(5,0,250,0,9),(40,0,215,0,9),(0,2,77,176,8),(0,32,89,134,8),(0,64,162,29,8),(3,0,252,0,8),(6,0,249,0,8),(32,4,155,64,8),(33,0,222,0,8),(34,0,221,0,8),(64,4,155,32,8),(65,0,190,0,8),(66,0,189,0,8),(129,0,126,0,8),(130,0,125,0,8),(132,0,123,0,8),(160,0,95,0,8),(0,8,54,193,7),(1,4,154,96,7),(1,64,162,28,7),(2,4,153,96,7),(2,32,89,132,7),(4,2,73,176,7),(4,32,89,130,7),(8,64,162,21,7),(16,2,77,160,7),(32,2,77,144,7),(96,0,155,0,7),(96,4,155,0,7),(128,2,77,48,7),(128,32,89,6,7),(192,0,63,0,7),(5,64,162,24,6),(6,32,89,128,6),(9,64,162,20,6),(17,64,162,12,6),(130,32,89,4,6),(160,2,77,16,6),(162,0,93,0,6),(35,0,220,0,5),(67,0,188,0,5),(97,0,154,0,5),(97,4,154,0,5),(98,0,153,0,5),(98,4,153,0,5),(129,8,54,64,5),(131,0,124,0,5),(161,0,94,0,5),(3,32,88,132,4),(193,0,54,0,4),(193,8,54,0,4),(224,4,27,0,4)]
def g255A : List (List Nat) := [[]]
def g255D8 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0xc1810000,0xdb04200072460800000,0xd0a081a101d8a0e070,0x7270ecab29a2a11a1897,0x1594128e4cc8844029ee,0xd8f0bc9b00bb63dda5e4,0xf8160176d3bf0fd1b20b,0xb2a34f7ecd86e45855c2,0x9efd9b0dcab02b851ffb,0x76618654570c7bf31d1b,0xca8ae18f7663a361951,0x5c29eed8f4bc9b0eb053,0xddb5e879361d60a7bb63,0xcaf26c3ac18f769793e4,0x587583a7dcbf40bb2a2b,0x57dbb3659915c150b7b,0x766cb702b82a15f6ecd9,0x665570442dedd9b2dc2a,0xe0885bdbb3659855c110])
def g255D9 (j : Nat) : Nat := if 3 ≤ j then 0 else (if j<1 then (word80 [0x31c98c0c,0x4e620b0d1844c105ff2f,0xc57c8bd25e02eb9742b8,0xf5bead996b2b4c59d2c7,0x960eaeb56caae152ea7b,0x534a93546ca1a504279d,0x3969aa4c4a5dd2a29214,0x78a34115e889431a0f50,0x247ec3e81ebcee075939,0xc1c48dd86c134619acc9,0xe6333069788b6e58c2b8,0x153ca484fe26c12f0940,0x47022290047ac3b01c50,0xd7c6723131740af451a2,0x5811408083b81b60c085,0x1c24210006f82f813a07,0x702b0098000cff68590e,0x1576cff69590e0576aff,0x6878560176aff6978160,0x176e7fe1f905d951e7fe,0x1d905d951bf7e8d905d9,0x51b7f687955d970b7f69,0x7915d970ef7e8d866157,0xefee818661570f7ee81,0x7661570cff61b9161570,0xd7f5db9161570ef7e8d8,0x660570efee818660570f,0x7ee817660570cff61b95,0x60570d7f5db9560570af,0xfe998560570cffe59856,0x570e7f5d98560570aff,0xea16560570f3f5d96560,0x570bfbe896560570cffe,0x618558570f3f5d985585,0x709ff6a396545709ffea,0x19654570cffe61865457,0xcff6618654570bf7e8d,0x8654570bfee818654570,0xd7fe617654570d7f6617,0x654570f7ee817654570a,0xff6879561d60aff69791,0x61d609ff6879561d609f,0xf6979161d60bbf687955,0xd960bbf697915d960bf7,0xe8d985d5609ff6979760,0x5609ff69f9560560bfde,0x857560560befe91985c5,0x60bf7e8d985c560bfee8,0x1985c560bfbe89855c56,0xef7e8d8754560efee81,0x8754560bf7e8d8754560,0xbfee818754560fbee817,0x654560cff68597e1950f,0xf6e8d965c150f7ee8576,0x5c150bfee99915c150df,0xe659915c150f7e5d9915,0xc150efe65b815c150bfe,0xea5615c150cff69597e1,0x910ff6e8d965c110f7ee,0x95765c110bfee99955c1,0x10dfe659955c110f7e5d,0x9955c110efe65b855c11,0xefe659855c110bfeea5,0x655c110afbe8985e0576,0xcf7e179360176cf7e4f8,0x1601769df68395619759,0xfd6839161971adf68385,0x595719fd683915d561af,0xde8575e01618ff683985,0xd951a7f683875d951df6,0xe839361970df6e4f9061,0x970af7e8d86615709f7e,0x8d98595709fbe8998595,0x709fee819859570d3f5d,0xb9159570afbe8965e057,0xaf7e8d866057097fe9d,0x98585709efe919858570,0x9f7e8d98585709fee819,0x858570d3f5db95585709,0x7f69f985457097fe9d98,0x545708ff6a396545709f,0xe68396545709fbe89965,0x4570cf7e979361d60cf7,0xe879361d60cf7e579361,0xd60cf7e4f9161d60af7e,0x8d8754560d3fe5d76545,0x60f5d5d57154560bf6e8,0xd965c150e7e5db815c15,0xf3e5d9615c1508ff69f,0x9661510c7fe5d7661510,0xcfde1b915d5109fbe899,0x759510cfbe1f9259510c,0xfb61f9259510bf9e8965,0x5c510bf6e8d965c110e7,0xe5db855c110e7e5d9855,0xc110f3e5d9655c110bfa,0xe89655c110e5d5d571e0,0x1518f7e8d985d950f1e5,0xd9655c1508efe91985d9,0x108f7e8d985d9109f968,0xb965c510e5d615755c51,0xf3c5d9615c110f5c5d5,0x7154110f9c5956154110]) else (if j<2 then (word80 [0x8a207a08,0x1aa28623d8683062bd87,0x6082a201d148413f0617,0x61470617874a9820707,0x6202e4a81d23783a28da,0x29062748c202d22988e0,0x8182b0613854a9820707,0x6202e4a81d23783a20c4,0x189d2306e08480686c18,0x50102c0698b228812818,0xa2488218d22b06a34882,0x85122819a209600cc170,0x78c62f87e88204f2201b,0x62880b8ac17861803a10,0x4e0e856081d63076081d,0x63070b824be882606138,0x9c2312e20602708d4188,0x13c8da21060e8be0818e,0x207e081ae2860758a101,0xd62044901dc1864781dc,0x1874a81c06860758e101,0xd62848b21e0a860752ba,0x2060752ba20606688168,0x90a81c19021d81c192e4,0xae89e0890a81c112ba20,0x523e884186188500630a,0xe20b0ad8c608762050c2,0xb881483a2f0ae303a193,0xe2650ae098cc28c0ea24,0x6350a0785c313e8ab8cc,0x2b82283a46f0a1862138,0x1ac238a2c2b631821d88,0x13b8ac20520e8bc238c0,0xe862698d42308e094832,0x1e0ed08e305e29488ab8,0xcc2383628c8a9264640e,0xe3382303a467081992e0,0x58bc3f85e083a3e2aa93,0x886081da1f81e12524e2,0xb27d8a60e8607781e145,0x24e8d42f800ff83e10da,0x3509e0049e17823709c3,0xe8c06f83e07843e8ba3f,0xc06781e0f843d8a0658,0xfc3781e0f843f0a0668d,0xa3b87e0783e1100af0ae,0x1f83e004fe10e8af8094,0xf84160b0a83b14f81e14,0x2e34738d52b8901ca586,0xfa242f63781e119e0784,0x17058268c2485de0f854,0xb8c2668ba3307e0783e1,0xe0be8a13f81e17820e8,0xe10813a258d62f83e162,0xe406f8c52b87a91a2c2f,0x63781e11401e8de0783e,0x105e37801785be0d2e2f,0x8017859e152e289ba268,0xcc1f81e0f84382ec3d8b,0xe003be0f842b11a2e882,0x730fc1f81e0f84430fa2,0x89da2781e092fe1100ef,0x81e0f84180a03d8de078,0x3e103a370e24e8b63689,0xc1f83e110e268fc1845e,0x7840d8ee2e8fc1845e0,0x7840d8ee2b89e07841d8,0xb62d89e07841d8a11037,0xa2f0dc1e8963f81e1120,0xa90f43707e0f81e12a64,0x340c0268688fc3418a2,0xc89c1f81e0f846c2b895,0x8c1bf0be07850b9014d8,0x88bf83e0785090f46d88,0x8bf81e0f840e8fa2f09c,0x181de0783e158c400da2,0xf07e0783e104e3e8fa28,0x19c1f83e07843f07a309,0x3a2d8fc2783e11010812,0xe3e8da2f83e131e4042c,0xc32ec7813a368be0f844,0xe318789363609c1d8be0,0xe8fe1150ae1fe286f637,0x80c47850b9214a2f62f8,0x1e0f85078e14d8a8bf81,0xe0f84138e13a2f62f83e,0x7840e8f8be1e64d8d81,0xd8ba3f83c278451344c2,0x1b0602fe3687e0027e0f,0x845837a3383c1f81e103,0xe382e0ef83e0784170da,0x3e8dc1f81e08463709c1,0xe8fe0784110d8258da3f,0x83e10a2300fc191be078,0x3e1218382e0ef81e0f84,0x178c4c41e890b4a6d19e,0xf81e1120901e0ef83e0,0x784170fe66f2678a3c09,0xde0ed97663ae9d50e917,0x383965c7ae3070cb7e1b,0xccdd46e3b6c1b32d7d6b,0x33551a7ad2668a341d9f,0x4ce866b3339978ca5647]) else 0x181d03e181a1205a081))
def g255H9 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0xc880000000,0,0xf0800000000003,0xcc000000000000000000,0xe5000001000,0x62c000000,0,0xb38000000000000,0,0,0,0,0,0,0,0,0x123000000000000000,0x67800000,0,0,0,0,0,0x1c0000,0x5a,0x40000000000000000000,0x19a0000000000,0x1423,0x50000000480000000000,0,0x7b000,0xa20000000])
def g255D10 (j : Nat) : Nat := if 6 ≤ j then 0 else (if j<3 then (if j<1 then (word80 [0xfcbaca88,0x5ff65d654437ff0eb2a2,0x1bfd8759510f7ebb2ca8,0x87fbe4965443feacab8a,0x21ff9965c110ffccaae0,0x887fe59570443ff2eca8,0x2213fd91e15769fec870,0xabb5fbe49855da7fb2bc,0xaed3fd90e05769fecaf,0xbb4ff647805dafbf26,0xc02ed3fd91e19759fec8,0x70cbaddfe55865d6fdf2,0x4c32eb3fd96e05759fec,0x8702bacff65b805d67fb,0x23c02eb3fd91e1d659fe,0xc870eb2edfe55875977d,0xf24c3acb3ff9161d659f,0xfc830eb2ddfe5587597c,0xff2abb2cb6ff915d965d,0xf6cbf04b2efb64782597,0x7db21c12cbbed87e0965,0xf76bb704b2cff65f8159,0x75faedc0acb3fd90e056,0x5df7c1302b2cff65f805,0x975faedc02cb3fd91e01,0x65df7c1300b2cff65786,0x5c67fb21c32e37f79161,0x9719fecb70ab8cff6438,0x55c76ff0ab2ae37ef925,0x95719fecb700b8cff657,0x805c67fb2bc3ac33fd90,0xe1d619ffcab0eb0efde4,0x5875867ff20c3ac37f79,0x161d61b7fcaaecb0fbde,0x45765867fb2fc2ac3afd,0x76e15619fec870ab0dfb,0xe4985586fef22baac36f,0xf9759561b7ecbacab0eb,0xfe1d655875fb0eb2ac3e,0xef92595619fecbf00b0e,0xbf5db805867fb2bc02c3,0x3fd96e1d519fec870ea8,0xcffe59875467ff20c3aa,0x33fd97e19519fec870ca,0x8cffe5d865477df24c32,0xa33ff9061951bf7c930c,0xa8cffe61765467fb30bb,0x2a39ff875d951d7ec32e,0xca8cff65f805467fb2dc,0x2a3b7d75e0151dfab8f,0xa8cff657865c27fb23,0xc32e17df9361970bfdc8,0x30cb877ee41765c27fb2,0xdc2ae13fd91e1570e7eb,0xb2cab85fbe49655c27fb,0x2dc0ae13fd95e0570e7e,0xbb2c2b84ff657875827f,0xb23c3ac13ff9561d60de,0xfc9b0eb04ffe45875837,0xf720c3ac17df9361d60b,0xfdc830eb07bee4176582,0x7fb2fc2ac1afd76e1560,0x9fec8f0ab05fbe498558,0x27fb2fc0ac1afd76e056,0x9fecaf02b04ff65b875,0x427fb23c3aa13ff9661d,0x509ffc8b0ea84ff65f86,0x5427fb23c32a13ff9761,0x950df7c930ca84ffe458,0x6542fdf24c32a13ff985,0xd9509fecc2eca86bf619,0x76542eff2cbaaa177f97,0x59550bbecbacaa879f5d,0x965543edf24b2aa13fd9,0x7e05509fecb702a86df5,0xd781543afaeab8aa1e7d,0x6558550efcbb2e0a87de,0x59570542ff722b82a1bf,0xb815c1509fecb70e884f,0xf657874427ff2cc3a213,0xff9561d109fecbf0c884,0xff657864427ff2ec3221,0x3ff95619109ffcc2ec88,0x4ff661764435fb0cbb22,0x13fd97e15109fecb70a8,0x84ffe5d854427ff2cc2a,0x213fd985d510dbec2aea,0x885fde45754427fb30b2,0xa217ef9259510bfbc8ac,0xa885fde59714437ef0ab,0x8a21bf5855c510efabaa,0xe2885fde5d61442feb2e,0xb0a21ef57658510f7ab2,0xac28877e5d970442ff72,0xab8221bfb855c110dfcc,0x2ae0887fc58570442ff7,0x2ea82217f99754110dfd,0xc3aa0886fe61d50443ef,0x2eaa8221f796554110ff,0x8b8aa0887fc585504427,0xdf24c3acb3ed92e19719,0xf7c930ca8f5d5d571546,0x7bf26c3ac13ef9261950]) else (if j<2 then (word80 [0xa43132a2,0x35442587c10e2619042c,0x9848b07ba0b9c0ef811f,0xbdff53fa57eaefc01f,0x5dbe647c50f769ecabd4,0x779f2f289e183bd97716,0xed19d853abc74cae881c,0xe4b98d725ae3e9c56386,0x77032df75bd0b7536dc2,0xda29b19b5ee6b52d501a,0x7db4b6689acfb59cb334,0x86618cb1d945b24f6402,0xc6cd8a9b0fc6192c1ed8,0x122fe85f46bd557882ed,0xd5d54b9dd71dadff5b74,0xb5f96a12d065994b2156,0x1bac045790ade959f2af,0x9557aa9e151529e55340,0xa501474a8b650d0a08d3,0xe6277e4e729c19369a69,0x74cb6987d2f1a59e4ad6,0x9499279a4ae48f690b51,0xf8a3ac46bc8c41165a28,0x6449488150eda19642d8,0x84c10712094409e8028f,0xe29f923e887bd8f4f9e4,0x83be27668ea61cf5393c,0x7140df81b9936846bd0d,0x4e9a4633de6684ca518f,0x3315c6180c0917c42f10,0x5d30b7f16b02ce858e0a,0xec15812a545328a30941,0xc279c4e249a693112574,0x496890611b5231645188,0x8990e0212441347ff8f9,0xf1ec63bc47560e701c44,0x372c6ba0d1d197a31506,0x78bc1170a2cb856b8a8,0x9147627fc4d889631218,0x231c43c882b0f841df43,0x9306d80d2618a82fb85b,0x20afe150c2688495088e,0xfc01d5836f06660bdc1,0x5d8288048608400e5817,0xd028203cc045003c0001,0xfff905d951ffec82eca8,0xfff595815c3ffb0ab0ae,0x1ffd8654570ffecc2eab,0x7ff64575583ffaeac0a,0xc1ffd985c560ffecaae2,0xb07ff61571583ffb30a8,0xac1ffd9754560ffec3aa,0x2b07ffe4576543fff2ab,0xb221bfd90e1576bfec8f,0xabb5ff643855dafff22,0xc2aedbfd90e0576bfeca,0xf02bb6ff617815daffb2,0x1c0aed7ff9560576dffc,0x2b02bb5ffe55805db7ff,0xac02ed7ff9160176dff,0xc0b00bb5ffe41865d6ff,0xf2cc02ebeff915d965bf,0xfc830cb8dffe41655c6f,0xff2cc02e3eff955d961d,0xfebaf00b0dffe4176547,0x7faedc02a37ff9660151,0xbffcab0cb87f7e4d865c,0x2fff22c32e1ffb906197,0xeffcaaecb877fe45765,0xc2fff2cc2ae1bfd86615,0x70efebb30ab85ffe4585,0x5c2fff30b2ae17fd9859,0x570ff7c92cab85ffe456,0x55c37facbc0ae17ff966,0x570dfec3302b877f5d9,0x815c2fff2ac0ae1bfd85,0x60570bffcc2c2b85ff66,0x1615c2fff2ab0ae1bff8,0x558570f7eb2ac2b85ffe,0x61515c2ffb30a8ae17ff,0x9654570bfecb2a2b86ff,0xe19515c3bfaeca8ae1bf,0xf9561d60dffc8b0eb05f,0xfe5587582fff22c3ac1e,0xff955d960f7fc8aecb05,0xffe4575582fff2ec0ac1,0x7ff9560560bffcaae2b0,0x77f5d571582fff2ea8ac,0x17fd9754560dffc3aa2b,0x6ff61d51583dfaeca8a,0xc1f7d7554560ffab8aa2,0xb06ffe5987542fff2cc3,0xaa17ff915d950dfebb70,0x2a85ffe59815437ff0cb,0x8aa17ff9758550bfecba,0xc2a86ffe1d615437fb0e,0xb0aa1efd7658550fbeba,0xac2a87fe65970543ff32,0x2b82a1ff9615c150dffc,0xb30e885ffe5987442fff,0x2abb221bfd76e1510dff,0xcb30a886ff5d985442ff,0xf2cc2a21bff865d510bf]) else (word80 [0x60f0f44e,0xf03840d250fc54bd138,0x1c1e10748060130d83a3,0xf0781c206920de2e1b07,0x47e0707840c241804a3e,0x1b07c1e07081a48078bc,0x4a3e0f81c211100d02d1,0xf0d83e0707840c242e15,0xe2f128fc0e17043a4f17,0x8947e070845151c2bc5e,0x251f81c2e08748e280f8,0x947e070b821d201804c3,0x60f83c0e10a080d05783,0xc0e10b86c1f0781c20f8,0x9c6e3f101d450a707851,0x5201a05c360f81c1e109,0xc80c05781c1e10bc6c1f,0x781c2120a0606024098,0x5c1d1f83c0e1038a0701,0xb0785a3f0781c206120c,0x251f0b83e0707840e24,0x1c066251f0b83e070784,0xc281c0c63e1707c4e07,0x785461c9783c2d1b81c,0x1e109c7060128d83e0f0,0x3842820001f1409b83c2,0x108f83e0f03841f138c1,0x114707841f890c0c0260,0xe8d47e0f03840d241809,0x251e8d83e0f03840d28,0x4f85c1d1f83c0e103881,0x783625836370383c20d1,0x3c1e10985c231c07c0e0,0xf083a1f1f83c0e10745c,0x28a383c20f8945070198,0xf83e0f03841f2012c6c1,0xf0781c2170e0d4d31e89,0xc0e0f08244090b092468,0x6b07c0e0d1384504b83c,0xe10745c3048521de20a,0x22417c2b1b81c1e11903,0xbb1b83c0e10b87c285f,0x83c0e10b86e345e8ec4e,0xf038412201a05c260e8,0xfc1e07081c48380d83c2,0x51f83c0e10349068168f,0x84c1f0383c207120e033,0x168f84c1f0781c206940,0xe06b1f0983e2f038346e,0x10e0bc1e128dc1e07085,0x38340b83a370383c213,0x9183e0f038428120c0d0,0x2e0e8d47e0707840c241,0xa05a3d1b07c0e0f08184,0x8a30983a3f0383c20710,0xe0331f07c1e07084843,0x1b07c0e0f085e30380d8,0x3a2f0383c2139007a2e1,0x307c1e07081c40380d47,0xa2e0f81c1e10309c1e13,0x83c0a3f081a38768f45c,0x1f0781c2061009a35170,0x7c1e07084e44931f83a3,0x1278f84a2f07842a2e8d,0x45c1f0781c2138e0f177,0x1706c6e0707841824191,0x8a3b1781c1e103c8c1b1,0x781c1a3f0818383c3e5a,0x87c303183e0f0384c52c,0x2dc0e0f085e280d8fc0e,0xf083a241f81c1e10745,0xe281383c0e10745e303c,0x521d13c3f8a176361381,0xc1e119840bf0781c2178,0xdc68bd1d8bc0e0f081e4,0x1f8d038bb1781c1e109,0xc90bc0d8dc0e0f085e3e,0x1025c1e07085e301383c,0xff085e35141fc1e070,0x85c301783c0127085c37,0x781c20f8bc58183d8dc,0x1e07085c3f0781c2120b,0x85818498dc1e07085e3f,0x138747c361413c1e1118,0x7a361383c2088dc7e1d1,0xb0b8404f0784471809c3,0x4686830138670781c22c,0x45c5e251f0d83e07088a,0x360c13c1e10b86b7df6e,0x62db2db3bb5ff6aa2d3a,0xda39b3d766becb55913b,0x1af626ec345835afe15e,0xaebaed718ada75a3ab24,0xd5fbab6d55c6a9654cca,0x90f509e9f5d3afa6d54c,0x969555265a44147028ab,0xd100a17741da80fcfda9,0xf073cb276ace7e9bd136,0x22698cce3994f31ae617,0xcbea97272bf654eca469,0x3cd263e4a9c91791a522,0x3641fc7e88f351d0e376,0x467a8c6b17c22da45788]))) else (if j<4 then (word80 [0x1f06c6e0,0xf0384241e8fc0e0f0a1e,0x241b074607f0781c20f8,0xbc8148398cc7a2f0383c,0x2879383a2b1b83c0e109,0xc7070a58d45c1f0383c2,0x139345e0707850f138d5,0xa0d0368ec6a2f0781c24,0x7942fe0f085c66141e0c,0x63f043bc0e107c812d1b,0x83c0e123c5c3d1b0625e,0xf038424171027e0f038,0x41d170c400ef07846517,0xc1822e0f83c0e10905c,0x443c782e0a89f8ac6e06,0x1385c10b9817092138dc,0xe0f085e2e242ec64240,0xf83c0e10bc5c4c118dc1,0xe07085e2e1c1986c3f07,0x81c20f8e0d0661d8786e,0x27078145e10f0be261e8,0xbc2e08503a38370d87e0,0xf0384241c180dc3b0f0d,0xc5e0f0289c21e160c048,0x130d87a1f0781c206940,0xd02e1b0f43e0707840c2,0x70dc5e261e87c0e10888,0x651b81c1e10c060251b,0x81c2e08bc3a3d1835c1e,0x7083e351823c1e107e3,0x430270f85a270785c00e,0x900e0330f0fc1e07083e,0x40318c04c3e1687c0e0f,0x81c50380d87c2f0287c,0x1e103090651f83c21b0a,0xc0230f0dc1e07085040,0x98358606d1f81c1e1074,0x90007783c21307c60651,0xf0dc1e07083e38300947,0xc2f0385c10e900da3f10,0x3bc1e10987e070b82290,0xe8a24e0f03842e158fc1,0xe10a8562b130bc1e1078,0x54330f0dc1e107056306,0x58e1fe0f083a211e01c1,0xe10943a2e1b0dc1e0708,0x4e1f184e1de0f084c2e1,0x98786e0f03842e182144,0x14707841d108e0c0231f,0xbc0e0f083a431f83c20,0xe8985c2f0383c2138746,0x561a86280ff07842120,0x1b46e0f038430180b46e,0x7045dc20e8f46e00638,0x3c2120d87c251781c1e1,0x747070198787e0f0384,0x24230f84a370781c2068,0xe2b24f0e8dc1e10b8706,0xb180b87c250f81c1e103,0x8a0701b0f84a1f0781c2,0x6920da3f078436141a0,0x56185b81c1e109c806d1,0xf0dc1e07084838602d86,0x651f81c1e1074906816,0x8f84e0707841d202c0ca,0x3f0383c20e8e1fe07078,0x42f1781c1e10a43a2e1b,0x83c0e10a04830583bc1e,0x7085e330f0dc1e07085,0xe351429c1e10762c351e,0x8b86e0707840c1c5fc1e,0x10985c2b1e8b84e07078,0x41d1f822fe07085c2b1f,0x945e0f03841d1f83c21,0x28745c28340ac70b7038,0x3c20e90c7e005b83c20e,0x8c09c270781c21407470,0x4e170947e0f03841d201,0xc066184f83c0e109c863,0x61709c0e0f083a38380c,0xc3e0f0384301c0746e07,0x78430180f85c270383c,0x20e8fc113f086c20004e,0x1de0f084c201f821de10,0xd84a304783c213c4c601,0xe168d47e0707840c2013,0x85c251f83c0e1074823f,0xe8dc1e0709263e17094,0x7e0f03841d1c1c06a1f0,0x781c2180e0ea1f078436,0x141ac74d50f81c1e104c,0x8062618f43e0f0384132,0x1804c1e1e8dc1e07081,0xa48340b83c3d1b81c1e1,0x3098a8dc59c5e251b81,0xc28b922813f178817e07,0xb8229278bc41485f81c,0x1e10748060130f83a2f0,0x383c207120e0360f0f45,0xe0707840c250fc44bd17,0x85c1e00748cbe0c9346e,0x261e8bc1e10a8a068170,0xf83a270383c207120e03]) else (if j<5 then (word80 [0x22e66170,0xa924b9585e251182274a,0x94d2e30f478331303982,0xc01ca5492c0c0a65a068,0xb168ac3e880e190c3c19,0x3a88c2608e12a416a88,0x302996018329a88c019a,0x492a0e1c6a3318898194,0x4600c8a6496a88302c14,0xc183511823c4ba541c30,0xa124c414874513a3d8a2,0x90e8b870ef028bc1e107,0xc7e189f83c0e10a45c3d,0x144e44e070b82290e918,0x7a2f0781c2620747c387,0x78144e1704483f0c51c1,0xe0708522f1ca6c5c3f0b,0x83c00e8f441411781c2e,0x8a43a461e89c1e07098,0xa1d1ca744c3f0383c20e,0x8e05a1f0781c2070b871,0x7d118852a1f001dc2e08,0xa4a0250f83c0e10385e3,0x8ba8ac527d0f800ee170,0x452551b81c1e14683e35,0xf83c0e107e3433130bc,0x2e0f00521d1f08c3e070,0x78518120e1fa30601825,0xee118787e0f028bc237,0x943e0f0384248c0ec5c,0x270383c20e8a476d0681,0xac7a1b1783c0e1458a09,0x8318629c287709c0a3f0,0x78458a41cc6a1b1f83c0,0xe144c9c250f83c0e109e,0x263b168dc0e0f0a2e2e1,0xe2bc5e21068c1de07087,0x64b128dc0e17062e2f1c,0x2bc5e27042fc0e107478,0x4a488cc462f0385c10e8,0xa49479198ac4e070b821,0xd149227637128bc0e170,0x62e1d2478398d256240e,0x68be88c40bb1b8145e1,0x70501c86a881da2f0385,0xc16305ca0ef1a8ac4e07,0x785171392281387789c,0x2e0a5ccc40778034e0f0,0x85c31003bc1e11945c30,0x9f07c1e10b8cc30958dc,0x1e17022e2e1c50c6e2d1,0x381c1e10762e48f07118,0x4ac3c1c0c175158a1763,0x70289c2e0a0380c5143b,0x44e07058dc20b941de33,0x1689c0e0f0a2e28268cc,0x622e0c89c0e0f085e2e2,0x850270ef1781c1e11592,0xe49583bc0e0f085e360f,0x81c1e11585e305a8dc0e,0xf092e2f1c8983e07078,0x42f170e1d13f1b81c1e1,0x14d2e407461c6a2f0382,0x97e109c90be1d8d83e07,0x78453206c17c3d1689c,0x1e07083a484c19456351,0x381c1e125c91489c3a97,0x89d1688c6e0707858330,0xac4e0f001dc21e0ec50,0x2707800ee10f07221178,0x1c2070f062291381c207,0xf0617b158983e070b82,0xe14922e62b1307c0e17,0x41c2924181507619898,0x3e0707845a288a47e070,0x7840e190e4722f0383c2,0x70c870a83b06c5c3703,0x83c22c128d86618b458c,0x1b1781c1a2708b0a83b0,0x6c7c370781c229925829,0x9682a0ea2b1c19831861,0xb81c1e11c13065158f44,0xe0f038495252a9709833,0x63c075158f44e070b82,0x6856a68614c312b45075,0x1307c0e0f098e7618b45,0x306e0e89c0e0b1f84561,0x8b0530660e8bc0e0f098,0xe551f06c6e0f03841f1c,0xd47e0707841f0e8f83a,0x304b81c1e10905c40a41,0xcc7a231b81c2e0c48903,0x51383c0e10a03a386019,0x476351381c1e12489e0f,0x38456178b86090358fc,0xe08778424202d46e070,0x78492178f46c185b81c1,0xe107c5e405a1a44e0707,0x841d17901d06a4a8d83e,0x707842f26243c178558,0x828637030bc2e085cc0b,0x83d0bc6e0707842e1792,0x176340f81c1e10b85e45]) else (word80 [1,0x1c8d846187452309cae5,0x549e1182c314838987b0]))))
def g255H10 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x14c2001eca001,0x4ec000000001e00a7e00,0x1a9a6f2001506000f05c,0xf16a0ada49c427ead848,0x296c6c000001a936ce87,0x1cd14760014,0x5e0000000012f800128a,0x2cc00000000000000,0x2b60,0x121a000000000000,0x128,0x800000c0000000000000,0x1c82e66,0x1ce6d08000cb400000,0xe0000001804000001c,0x20001c9400000165c000,0xe800000000046800067,0xc000001a53ed28384232,0xf40a200140eee2001ab0,0x1c1200000000,0,0xd544c06ff02,0xe7800046123600000000,0x43a030001c4e000000e,0x18000a096c0000001a14,0x150000000065800,0x8100000,1,0x2dc000000c84000abe00,0x2aea020000016c96,0x24000000000cea000000,0xe5600,0x1806286464001c16a5ae,0x9e48e000000000000001,0xca6000001e72001e5400,0,0x10fe001,0xb2000000000832c2f07,0xa4bde400014df2ee6a84,0xfbcf6aa5244eab242e51,0x4b9898000001090000cc,0x68d600102c00000142a4,0x8c23e000000ad8001e4a,0x18c58ba001c3c00000,0xe28001c1c0000,1,0xa0000000002fc00000,0x186a0,0x1280001274c46,0x1f2632e400000000063,0x40000000000000000008,0x20421456620000810402,0x18c21180280040228125])
def g255D11 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then (word80 [0x30708986,0xc7c443c1c22618bb170d,0x1b070308608c6c345c1c,0xc2181c907c68631b0d1,0x707030a10b2ec6c543c0,0xc1c21823170d1f070308,0x5872418160386c547841,0xdc0c1c2301b1458751f0,0x21307089c7c345c1c0c2,0x161f1c5b011476130708,0x989c7c543c1c0c2161f1,0xb0d1f0703084c718131a,0x47850cc6c3c1c0c23033,0x1f0d1b0703084c716460,0x703138527c01dc1c2263,0x31b0c684c351f0702130,0x8ac6c318130c47c1c085,0xc22b1f190f0703084c7c,0x5c446c0c1c2171c1c745,0xf17111b030b060cac6c4,0x45c0c1c2171f1b151303,0x7085c7c5c447c0c1c21,0x51c54391e0f1712185f0,0x30b04b06c5c4150e47c0,0xc283c1281d1410bb0703,0x85480705442fc0c1c21,0x5231b111f0703084871a,0x17128504c647831fc0c1,0xc2331f111b0703084871,0x21507048346c0c1c2262,0xe2f1b106848360f03070,0x91ca12c04683c1c22e26,0x231f1913070308487281,0x712c6c485c0c1c2472b1,0xb151f0703083c718170f,0x584c6478324c0c1c233,0x1f151b0703083c7160f1,0x507058346c0c1c22f2f1,0xf19170703083c713120f,0x784c6834527c1c0c233,0x18603c33160f03051f08,0xa160f450446c083c1c22,0xf289c5c3f1b151f03061,0x308a241f120fc7c6c145,0xc084c22c271f130e1a17,0x708885420fa82d205e8,0x21faa7d91f067ae1e7a,0x78d1dee7681d3a7391c8,0xe7121bfa6eb1b666c01a,0xaa68f19e6664193a6331,0x876602179a5d316ee59c,0x161a5671526536149250,0x913d64e0130a4af12764,0x8211ba45910ee4281052,0x4010fbe3e00f3a3c10e9,0xe3940e0a3750d9e3560d,0x1a32f0c7630e0bd22e10,0xb462be0aba29f0a16276,0x97224708c6222084a1f,0xd07b61de073a1b706861,0x9005fa16f055614604ba,0x119041e0f8038a0d302e,0x60aa024a08301a605400,0xfa02900460003ffe1576,0xffd855dbffe0576ffd81,0x5dbffe0176ffd805dbff,0x61975ffd815d7ff60175,0xffd87597ff60565ffd80,0x597ff61971ffd855c7ff,0x59571ffd805c7ff61d61,0xffd85587ff5d561ffd80,0x587ff61d51ffd86547ff,0x5d951ffd80547ff61970,0xffd855c3ff59570ffd81,0x5c3ff58570ffd515c3ff,0x61d60ffd85583ff5d560,0xffd81583ff5c560ffd51,0x583ff61d50ffd86543ff,0x5d950ffd81543ff5c550,0xffd61543ff61d10ffd86,0x443ff5d910ffd85443ff,0x5d510ffd65442ffe1576,0xbff815daffe0176bff86,0x5d6ffe0575bff805d6ff,0xe1d65bfd87597bf5d965,0xfef82596ffe0565bff80,0x596ffe1971bff855c77f,0x5d571bff805c6ffe1d61,0xbfd87587bf5d961bff85,0x587bf59561bff80586ff,0xe1d51bfd87546ffe1951,0xbfd86547df5d551ff571,0x546ffe0151bff865c37f,0x5d970bff855c2ffe0570,0xbff87582ff61d60efd76,0x582ffe1560bff81582ff,0xe1d50bfd87542ffe1950,0xbfd86543df5d550f7d65,0x542ffe0550ff970542ff,0xe1d10bfd87442ffe1910,0xbfd86442ffe1510bfd85,0x443fd5c510ff561443fe,0x5c110ff950442fbe0965]) else (word80 [0x1f130d17030708a4,0x8261a86c48745c2c1c01,0xd281f170d13030708a48,0x181686c58744c0c1c21d,0x281c1b17110f030b04a4,0x74a171586c5c48743c0c,0x2c10e2c990d1b0703086,0x87c81a1813c644c30dc1,0xc0c2302c5c49190f0703,0x8687c91ac01fc2c11d2,0x61c584f00a3070874988,0x1512c028c1c21f26205a,0x110d1b030708609091a1,0x813c68445c30cc1c0c23,0x306116130c991b07030,0x8b8a170f468443c1c0c2,0x18242860591f03070890,0x74826161345c1c0c2271,0xd246a130c5a1b030708b,0xc9150f27c1c0c2162420,0x68604f1a111f0c330703,0x8c0c261613844046c1c,0x2273628a44c3a130d1e4,0xd1a170703089cd120f46,0x8543c1c0c2132728f074,0x5717111b030b045ca391,0xa44c6122ec0c1c217289,0xa5d185f120d17021c770,0x70998d381845c60f2fc0,0xc1c2172a5c59185f160d,0x5a1d1300770708d97134,0x417c687538345c0c1c22,0x7345f17111f030b04543,0x89261512c74045c40ec1,0xc2342c54bd6838346a1b,0x120d151e570b0304f160,0xfc7c544c0c1c20e15285,0x4b960383062571619120,0xd1f030708f13950e0c15,0xc74544838653c1c0c238,0x685d191f070308487c92,0x6151fc1c2c0122820a64,0x848a3120d1a151f03070,0x874d130f4644c1c0c212,0x28244a151318620f0703,0x8b8a16921f4612c7835,0x68544c0c11dc238605d1,0x91f0307083c909161524,0xc0c1c20f2720a63c3c9f,0x160d1a111f03070874d1,0x3124645c0c1c20f27246,0xa1319143e0f070308bca,0x268f24460fc78345c084,0xc11dc26638121f0c7e1b,0x701170890587c32486c,0x44c1c22717121c74a70,0x10f0b0492fc4c346c0c1,0xc21a231b0d1307030868,0x72fc6c443c1c0c21a231,0x30d1f07089861a868504,0x3471fc01dc1c226301b,0x121700751f0708989c7c,0x400c32ec1c225231f0d1]))
def g255H11 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x200045e000f2a3b,0x3ca5651808b80004c000,0xc948000000e53d89800,0x350000000000005a6872,0x2d9868c1540000,0x47b800385466a1,0x5e00000000000005c3c0,0x8435723a440010c500,0x64b69f5106000000040,0xc22e66700034204e7814,0x73200014192471891e0f,0x4300002c880000004208,0x7023ab412d4,0x3300019031bfa47255d9,0x906200000059e800000,0x1ade240b24,0xb14b4f13634803f327,0x57c39ad45889f49ea10,0x131a00040540013250,0x1af0d8900000,0x1eae0007848001d0800,0x4a6c0005355440cc089,0xd287e2e1058220000000,0x2274132ad1161006c581,0xef210f7c64864e50d2f4,0x37828000338c1addf80,0x72280038de0000002b,0x4305284bb8fd02800172,0x488f0404000000934000,0xc30007294000a5b,0x674213c09800076a8000,0x9940000000c340000000,0x6be040a00000063ed4,0x713160007084000c56c0,0x1a2e06292ba407b99800,0x21824b8003cea49ae77,0x6be6943e37a1eace0c44,0xaf500000020d20004250,0x1a1767000000000000,0x6cf8264d86c63778c,0xd8947711b138aa857a0b,0x600000028400000004bb,0x10f60007369205cf1,0x31a800047c0000000003,0x25070a8798001ccacc4a,0x5cb2ca8ce000000120a5,0x8e00000071764b200000,0xb845aee1c3996c7482,0xf8a7a74f4719d7921441,0xe993010134c71e1100c5,0xe5ae45a8e4d92c2513b3,0xa5651ea63291f9f5a2b8,0x92000194aa1c89883680,0x17e061a8da0ea45640,0x14399433612274c82c27,0xc000ae29999a9800f2fd,0xe26d23486900204f31f0,0x1e57b6c23d00000000,0x11da00000042b09,0x7784676a000000000000,0x1121cabb00000283000,0x162326e80035b800093f,0x4260000003480001,0x8e5b0890b6d4930470d0,0x385987927f2b36d400,0xb45517e952000d9bb4,0xc5c6c000659d2d4d9600,0x38ee0ef52fd07000,0x2ca3a0b875000343a894,0xa42800387f5260007ac6,0xdad07f0003a72d6f8c18,0x6d8a18cdc0000004bfc0,0x1ebe33c0000000000c7,0x68f000000000032c165,0x587b897440e09312c000,0xc39121460b127c00,0xc0050786070010002040,0x8040838700440060204,0xa0a02a02820608181120,0x45850438121081028008,0x50495020000006341882,0x40008102002010a10800])
def g255D12 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x1162,0x430e1a0418441a8d1218,0x70b06042263c48614340,0x830931262345861c2408,0x30892d1e2c3081a04184,0x4938f1a185090604224b,0xc68b103838106112563c,0x5880c34083089251e344,0xa0e0c08448f8f1a2830,0x906042266d8a1e367959,0x450cf22845003febb7fd,0x75ffacbff5c7feb0ffd5,0x1ffae1ff583fea87fd10])
def g255H12 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x651001,0x328006065cfb8c000000,0x1d688c0a8000003954d,0x91cc559617dd5bd5a000,0x19bf82e8b,0x5e15c0006d0a9bb17a8e,0xb1ac3bb0aa4909f8d723,0xa0039c8c42b7f0f9d12d,0xf6a0000000084145e5f5,0x13802002c6000428216d,0xb5a9456e7fa00000018f,0x40000032262605e9a000,0xd8b4200012a11eb0a9e0,0x452313ce496533c4188,0xfd4b84a66ab085f8e183,0x9b3b964640b40e747623,0x10c80b38d7ee496045d2,0x40531d2001d391bad0f8,0xb51aa656571ac2850712,0x4507000441522881901,0x40108242092450034001])
def g255D13 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7185103040088ff
def g255H13 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x40040000003d8de20,0x1cc0000c8000000,0x2d40224000003d00001])
def g255L : Nat → Packing
  | 8 => (18,5,6,0,0,8,0,g255D8)
  | 9 => (133,4,6,0,0,13,0,g255D9)
  | 10 => (313,3,6,0,0,15,0,g255D10)
  | 11 => (105,2,6,0,0,14,0,g255D11)
  | 12 => (10,1,6,0,0,10,0,g255D12)
  | 13 => (1,0,6,0,0,0,0,g255D13)
  | _ => emptyPacking
def g255I : Nat → Nat → Option (Nat × Nat)
  | 9 => lookupWord 4 293 0 9 5 0 g255H9
  | 10 => lookupWord 33 337 5 12 8 0 g255H10
  | 11 => lookupWord 78 463 7 13 9 0 g255H11
  | 12 => lookupWord 26 131 7 11 7 0 g255H12
  | 13 => lookupWord 2 29 1 8 4 0 g255H13
  | _ => fun _ => none
def g255 : Forest := ⟨255,13,fun i => g255Y[i]?.getD (0,0),g255C,g255A,g255L,g255I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_0 : block g255 8 0 18=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B8 : block g255 8 0 18=true := g255P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_0 : block g255 9 0 10=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_10 : block g255 9 10 51=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_61 : block g255 9 61 72=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B9 : block g255 9 0 133=true := (@block_merge g255 9 0 10 123 g255P9_0 (@block_merge g255 9 10 51 72 g255P9_10 g255P9_61))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_0 : block g255 10 0 6=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_6 : block g255 10 6 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_102 : block g255 10 102 87=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_189 : block g255 10 189 96=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_285 : block g255 10 285 12=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_297 : block g255 10 297 16=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B10 : block g255 10 0 313=true := (@block_merge g255 10 0 189 124 (@block_merge g255 10 0 6 183 g255P10_0 (@block_merge g255 10 6 96 87 g255P10_6 g255P10_102)) (@block_merge g255 10 189 96 28 g255P10_189 (@block_merge g255 10 285 12 16 g255P10_285 g255P10_297)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_0 : block g255 11 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_1 : block g255 11 1 56=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_57 : block g255 11 57 48=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B11 : block g255 11 0 105=true := (@block_merge g255 11 0 1 104 g255P11_0 (@block_merge g255 11 1 56 48 g255P11_1 g255P11_57))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P12_0 : block g255 12 0 10=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B12 : block g255 12 0 10=true := g255P12_0
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
theorem g255G : graphValid g255 (boundsBefore K254) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255R : Impossible true graph 13 sevenInputs.toFinset := by
  rw [show graph = targetOf g255 by decide +kernel]
  exact root_index (g:=g255) (top:=13) (i:=0) (before_sound K254 V254) g255G g255T (by decide) (by decide +kernel)

end PEqualNP.Outside.L_meta_33076

open PEqualNP.Outside.L_meta_33076 in
theorem PEqualNP.Outside.L_meta_33076 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o fit _ correct
  exact replaceShort g255R gates o fit correct

import PEqualNP.Defs

-- The two-mode live-state and cofactor checker follows L_meta_1674 and L_meta_670.
-- The graph, restrictions and all search certificates below are for L_meta_32373.

-- Shared forest and cofactor certificates from L_meta_1674 and PR 11111 for L_meta_1677.
-- The original credit line is retained below. The two root certificates here cover the unpinned graph.

-- The checker and the bound certificates are adapted from PEqualNP/Outside/L_meta_1667.lean (Apache-2.0).
-- Two modes: u=false are monotone runs (AND, OR); u=true are runs up to complement, where negation is free.
namespace PEqualNP.Outside.L_meta_32373
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
def graph : Sig := (BitVec.ofNat 512 (word80 [0xffffffff,0xfffffffefffffffeffff,0xfffeffffffffffffffcc,0xfffffafaeeee0000ffff,0xfffffffffffefffffffe,0xfffffffeffffffffffff,0xffccfffffafaeeee0000]))
def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 4) || (x 1 && x 4) || (x 0 && x 5) || (x 2 && x 5) || (x 4 && x 5) || (x 1 && x 6) || (x 3 && x 6) || (x 4 && x 6) || (x 5 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 2 && x 7) || (x 3 && x 7) || (x 4 && x 7)
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
  (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 2 &&& x 5) ||| (x 4 &&& x 5) ||| (x 1 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 5 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 2 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7)
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
  (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 2 &&& x 5) ||| (x 4 &&& x 5) ||| (x 1 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 5 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 2 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7)
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



def target (x : Fin 8 → Bool) : Bool := decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 4, 5, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 4, 5, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 4, 5, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
def smallCircuit : Circuit := ⟨[⟨.or,[0,1]⟩,⟨.or,[0,2]⟩,⟨.or,[4,9]⟩,⟨.or,[1,3]⟩,⟨.or,[4,11]⟩,⟨.or,[5,7]⟩,⟨.or,[6,7]⟩,⟨.and,[13,10]⟩,⟨.and,[14,12]⟩,⟨.and,[6,5]⟩,⟨.and,[4,8]⟩,⟨.or,[15,16]⟩,⟨.or,[19,17]⟩,⟨.or,[20,18]⟩], 21⟩

theorem witnessMonotone : ∀ g ∈ smallCircuit.gates,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [smallCircuit,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ⟨Or.inl rfl,by decide⟩ | exact ⟨Or.inr rfl,by decide⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem witnessCorrect : ∀ x : Fin 8 → Bool, smallCircuit.eval (List.ofFn x) = target x := by
  decide +kernel

theorem witnessSize : smallCircuit.gates.length = 14 := rfl

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

def lowRow (i : Fin 8) : Row := Fin.ofNat 512 (1 <<< ([4, 4, 5, 6, 0, 0, 1, 0] : List Nat).getD i.val 0)
def highRow (i : Fin 8) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< ([4, 4, 5, 6, 0, 0, 1, 0] : List Nat).getD i.val 0))

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
    (lower : Impossible true graph 12 sevenInputs.toFinset) (gates : List Gate) (o : Nat)
    (fit : ∀ g ∈ gates, (g.op=GateOp.and ∨ g.op=GateOp.or ∨ g.op=GateOp.not) ∧ g.inputs.length≤2)
    (correct : ∀ x : Fin 8 → Bool, (Circuit.mk gates o).eval (List.ofFn x)=target x) :
    ∃ (gs : List Gate) (out : Nat), (∀ g ∈ gs, (g.op=GateOp.and ∨ g.op=GateOp.or) ∧ g.inputs.length≤2) ∧
       gs.length≤gates.length ∧ ∀ x : Fin 8 → Bool, (Circuit.mk gs out).eval (List.ofFn x)=target x := by
  classical
  by_cases big : 14 ≤ gates.length
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
def g49Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3ff63ff63ff63ff63f,0xf63ff63ff63ff63ff63f])),(BitVec.ofNat 152 (word80 [0x492049204920492049,0x20492049204920492049]))),(0x0,0x0),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xc7fbc7fbc7fbc7fbc7,0xfbc7fbc7fbc7fbc7fbc7])),(BitVec.ofNat 152 (word80 [0x924092409240924092,0x40924092409240924092]))),((BitVec.ofNat 152 (word80 [0xf8fdf8fdf8fdf8fdf8,0xfdf8fdf8fdf8fdf8fdf8])),(BitVec.ofNat 152 (word80 [0x248124812481248124,0x81248124812481248124]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g49C : List ColumnInfo := []
def g49A : List (List Nat) := [[],[84],[64],[64,80],[80,64],[80]]
def g49D3 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7
def g49L : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,g49D3)
  | _ => emptyPacking
def g49I (_ _ : Nat) : Option (Nat × Nat) := none
def g49 : Forest := ⟨49,3,fun i => g49Y[i]?.getD (0,0),g49C,g49A,g49L,g49I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g49P3_0 : block g49 3 0 1=true := by
  apply cellsBlock (ar:=3) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g49B3 : block g49 3 0 1=true := g49P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g49T : checkedTables g49 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g49 0 0 0 = true)
  · exact (rfl : block g49 1 0 0 = true)
  · exact (rfl : block g49 2 0 0 = true)
  · exact g49B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g49G : graphValid g49 (boundsBefore []) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low49 : Lower true (varsX 49) (graphGoal 49) 4 := lower_forest (g:=g49) (i:=0) (hints:=4) (before_sound [] baseKnown) g49G g49T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K49 := extendKnown [] 4 [(49,[]),(82,[16,101]),(112,[64,16,33,50,83,99]),(145,[117,101]),(146,[16,117,101])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V49 : Known true K49 := extend_ok (m:=49) baseKnown low49 (by decide +kernel)
def g51Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3de871ff81fc7ffc7b,0xd0e3ff03f8fff8f7a1c7])),(BitVec.ofNat 152 (word80 [0x81a892451429080903,0x51248a2852101206a249]))),((BitVec.ofNat 152 (word80 [0xc6980e3ffe007cff8d,0x301c7ffc00f9ff1a6038])),(BitVec.ofNat 152 (word80 [0x169adb66193212902d,0x35b6cc326425205a6b6d]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfb978fffffff80fff7,0x2f1fffffff01ffee5e3f])),(BitVec.ofNat 152 (word80 [0x124882040202000,0x2491040804040000492]))),((BitVec.ofNat 152 (word80 [0x66ff03fffffff000c,0xdfe07ffffffe0019bfc0])),(BitVec.ofNat 152 (word80 [0x26464930418040c24c,0x8c926083008184991924]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g51C : List ColumnInfo := [(2,0,49,0,4)]
def g51A : List (List Nat) := [[],[80]]
def g51D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1f
def g51L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g51D4)
  | _ => emptyPacking
def g51I (_ _ : Nat) : Option (Nat × Nat) := none
def g51 : Forest := ⟨51,4,fun i => g51Y[i]?.getD (0,0),g51C,g51A,g51L,g51I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g51P4_0 : block g51 4 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g51B4 : block g51 4 0 1=true := g51P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g51T : checkedTables g51 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g51 0 0 0 = true)
  · exact (rfl : block g51 1 0 0 = true)
  · exact (rfl : block g51 2 0 0 = true)
  · exact (rfl : block g51 3 0 0 = true)
  · exact g51B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g51G : graphValid g51 (boundsBefore K49) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low51 : Lower true (varsX 51) (graphGoal 51) 5 := lower_forest (g:=g51) (i:=0) (hints:=68) (before_sound K49 V49) g51G g51T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K51 := extendKnown K49 5 [(51,[]),(83,[16,101]),(178,[16,80,32,50,115,99]),(209,[97,33,50,117]),(240,[80,113,32,49,98])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V51 : Known true K51 := extend_ok (m:=51) V49 low51 (by decide +kernel)
def g54Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0xf5e207ff01fc7e3ff5,0xe207ff01fc7e3ff5e207])),(BitVec.ofNat 152 (word80 [0x15616d8a942904a215,0x616d8a942904a215616d]))),((BitVec.ofNat 152 (word80 [0x1bd038fffe007fff1b,0xd038fffe007fff1bd038])),(BitVec.ofNat 152 (word80 [0x5ac0db2c18b228045a,0xc0db2c18b228045ac0db]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xecefc7ffffff803fec,0xefc7ffffff803fecefc7])),(BitVec.ofNat 152 (word80 [0x88a923020c0310808,0x8a923020c03108088a92]))),((BitVec.ofNat 152 (word80 [0x1b3df8ffffffffc01b,0x3df8ffffffffc01b3df8])),(BitVec.ofNat 152 (word80 [0x813524c0c100403081,0x3524c0c1004030813524]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g54C : List ColumnInfo := []
def g54A : List (List Nat) := [[],[33,84]]
def g54D3 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xf
def g54L : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,g54D3)
  | _ => emptyPacking
def g54I (_ _ : Nat) : Option (Nat × Nat) := none
def g54 : Forest := ⟨54,3,fun i => g54Y[i]?.getD (0,0),g54C,g54A,g54L,g54I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g54P3_0 : block g54 3 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g54B3 : block g54 3 0 1=true := g54P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g54T : checkedTables g54 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g54 0 0 0 = true)
  · exact (rfl : block g54 1 0 0 = true)
  · exact (rfl : block g54 2 0 0 = true)
  · exact g54B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g54G : graphValid g54 (boundsBefore K51) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low54 : Lower true (varsX 54) (graphGoal 54) 4 := lower_forest (g:=g54) (i:=0) (hints:=2164032) (before_sound K51 V51) g54G g54T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K54 := extendKnown K51 4 [(99,[32,16,84,100]),(163,[32,80,116,100]),(195,[32,16,97,116,81,84]),(225,[16,96,114,50,84,64,67]),(226,[81,114,50,100,67])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V54 : Known true K54 := extend_ok (m:=54) V51 low54 (by decide +kernel)
def g113Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xf1fe003ffc0f9f3f1f,0xe003ffc0f9f3f1fe003f])),(BitVec.ofNat 152 (word80 [0x241e49248a2142a241,0xe49248a2142a241e4924]))),(0x0,0x0),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfe750fc7fff01fffe7,0x50fc7fff01fffe750fc7])),(BitVec.ofNat 152 (word80 [0x400012491042040400,0x1249104204040001249]))),((BitVec.ofNat 152 (word80 [0xff8af1f8ffffe03ff8,0xaf1f8ffffe03ff8af1f8])),(BitVec.ofNat 152 (word80 [0x800024922084080800,0x2492208408080002492]))),((BitVec.ofNat 152 (word80 [0x19fe00ffffffc001,0x9fe00ffffffc0019fe00])),(BitVec.ofNat 152 (word80 [0x959c924c308103095,0x9c924c3081030959c924]))),(0x0,0x0),(0x0,0x0)]
def g113C : List ColumnInfo := [(1,0,112,0,4)]
def g113A : List (List Nat) := [[],[84],[96],[96,84]]
def g113D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1f
def g113L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g113D4)
  | _ => emptyPacking
def g113I (_ _ : Nat) : Option (Nat × Nat) := none
def g113 : Forest := ⟨113,4,fun i => g113Y[i]?.getD (0,0),g113C,g113A,g113L,g113I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g113P4_0 : block g113 4 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g113B4 : block g113 4 0 1=true := g113P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g113T : checkedTables g113 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g113 0 0 0 = true)
  · exact (rfl : block g113 1 0 0 = true)
  · exact (rfl : block g113 2 0 0 = true)
  · exact (rfl : block g113 3 0 0 = true)
  · exact g113B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g113G : graphValid g113 (boundsBefore K54) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low113 : Lower true (varsX 113) (graphGoal 113) 5 := lower_forest (g:=g113) (i:=0) (hints:=67108868) (before_sound K54 V54) g113G g113T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K113 := extendKnown K54 5 [(113,[]),(114,[16,101]),(147,[33,49,81,113,97]),(177,[80,64,118]),(210,[96,16,65,84,117])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V113 : Known true K113 := extend_ok (m:=113) V54 low113 (by decide +kernel)
def g115Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfc7fc01fe1fc7fc03f,0xe1ffff87c1f960000f0f])),(BitVec.ofNat 152 (word80 [0x2942a141440942a2a1,0x45084110407969999999]))),((BitVec.ofNat 152 (word80 [0x7fffe001ffffffc0,0x1fc7ff8592cb00f00f0])),(BitVec.ofNat 152 (word80 [0x321309898890130309,0x881112011928b5555555]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x7ffffffe007fffff,0xfe007fffba0940f0f0ff])),(BitVec.ofNat 152 (word80 [0x400402020020040402,0x200400000002222222]))),((BitVec.ofNat 152 (word80 [0xff80000000007fffff,0xffff80000ff28f00ff00])),(BitVec.ofNat 152 (word80 [0x80180c0c10c218080c,0x4018220f8084444444]))),((BitVec.ofNat 152 (word80 [0xffffffffffff800000,0x6446ffff0000])),(BitVec.ofNat 152 (word80 [0x6030100100603030,0x11826044604648888888]))),(0x0,0x0),(0x0,0x0)]
def g115C : List ColumnInfo := [(1,0,114,0,5),(2,0,113,0,5),(32,0,83,0,5),(64,0,51,0,5)]
def g115A : List (List Nat) := [[],[16,101]]
def g115D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x2709f
def g115L : Nat → Packing
  | 6 => (1,0,2,0,0,0,0,g115D6)
  | _ => emptyPacking
def g115I (_ _ : Nat) : Option (Nat × Nat) := none
def g115 : Forest := ⟨115,6,fun i => g115Y[i]?.getD (0,0),g115C,g115A,g115L,g115I⟩
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
  · exact (rfl : block g115 4 0 0 = true)
  · exact (rfl : block g115 5 0 0 = true)
  · exact g115B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g115G : graphValid g115 (boundsBefore K113) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low115 : Lower true (varsX 115) (graphGoal 115) 7 := lower_forest (g:=g115) (i:=0) (hints:=16777284) (before_sound K113 V113) g115G g115T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K115 := extendKnown K113 7 [(115,[]),(179,[16,80,112,96]),(211,[97,117]),(241,[96,113,33,50]),(242,[80,113,32,50,99,49])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V115 : Known true K115 := extend_ok (m:=115) V113 low115 (by decide +kernel)
def g227Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xf007ffff87fff003ff,0xff87fffa0f5a40f801f])),(BitVec.ofNat 152 (word80 [0xa25114211008a1280a,0x201108822015a45294a5]))),((BitVec.ofNat 152 (word80 [0xfff801fff87ffffc00,0xfffffc0335af3f003e0])),(BitVec.ofNat 152 (word80 [0xc060580a0102c0302c,0x40a00108215832318c63]))),(0x0,0x0),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffe00007fffffff,0xf0007ffccfd11c007c1f])),(BitVec.ofNat 152 (word80 [0x80608c2223044130,0x4c22200c3c018a5294a]))),((BitVec.ofNat 152 (word80 [0x7fffffff,0xffff80004d2fe8007fe0])),(BitVec.ofNat 152 (word80 [0xb058130444c098240,0x9004c100c27c14a5294]))),((BitVec.ofNat 152 (word80 [0xffffffffff80000000,0x33aa61bff8000])),(BitVec.ofNat 152 (word80 [0xc0601c000700e0380,0x8e0470211aa2098c6318]))),(0x0,0x0)]
def g227C : List ColumnInfo := [(1,0,226,0,4),(2,0,225,0,4),(32,0,195,0,4),(64,0,163,0,4),(128,0,99,0,4)]
def g227A : List (List Nat) := [[],[97,117],[16,101],[16,80,112,96],[80,118],[80,113,96,16],[96,16,81,117],[96,113],[112,81],[112,97,80,81]]
def g227D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x4fd5110
def g227D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x101a0fd20fd10
def g227H5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7
def g227D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x23440bf
def g227H6 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x5403b800000158,0x1c402000000019eaf,0xe80000038c0002880001])
def g227L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g227D4)
  | 5 => (2,1,3,0,0,4,0,g227D5)
  | 6 => (1,0,3,0,0,0,0,g227D6)
  | _ => emptyPacking
def g227I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 4 0 0 g227H5
  | 6 => lookupWord 2 29 1 8 1 3 g227H6
  | _ => fun _ => none
def g227 : Forest := ⟨227,6,fun i => g227Y[i]?.getD (0,0),g227C,g227A,g227L,g227I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g227P4_0 : block g227 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g227B4 : block g227 4 0 1=true := g227P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g227P5_0 : block g227 5 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g227B5 : block g227 5 0 2=true := g227P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g227P6_0 : block g227 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g227B6 : block g227 6 0 1=true := g227P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g227T : checkedTables g227 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g227 0 0 0 = true)
  · exact (rfl : block g227 1 0 0 = true)
  · exact (rfl : block g227 2 0 0 = true)
  · exact (rfl : block g227 3 0 0 = true)
  · exact g227B4
  · exact g227B5
  · exact g227B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g227G : graphValid g227 (boundsBefore K115) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low227 : Lower true (varsX 227) (graphGoal 227) 7 := lower_forest (g:=g227) (i:=0) (hints:=16777317) (before_sound K115 V115) g227G g227T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K227 := extendKnown K115 7 [(227,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V227 : Known true K227 := extend_ok (m:=227) V115 low227 (by decide +kernel)
def g243Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x7ff83fffffe0f94cb,0xb522a000fc000003f03f])),(BitVec.ofNat 152 (word80 [0x508508420104201089,0x35222249249249249249]))),((BitVec.ofNat 152 (word80 [0xf80003ff0ffff032ae,0x997403f00003f000fc0])),(BitVec.ofNat 152 (word80 [0x60261004204801302e,0x9160145145145145145]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffc000fffffd010,0xc583fc0000fc0fc0fff])),(BitVec.ofNat 152 (word80 [0x800800080010000000,0x82082082082082]))),((BitVec.ofNat 152 (word80 [0xfffffffff000002956,0xda22500003f000fff000])),(BitVec.ofNat 152 (word80 [0x23001100460422156,0xc8005514514514514514]))),((BitVec.ofNat 152 (word80 [0xfad,0x4669000003ffff000000])),(BitVec.ofNat 152 (word80 [0x4c022604980840e81,0x6690a28a28a28a28a28]))),((BitVec.ofNat 152 (word80 [0x6651,0x63c4cffffc0000000000])),(BitVec.ofNat 152 (word80 [0x70043808e01084650,0x42c0cc30c30c30c30c30]))),(0x0,0x0)]
def g243C : List ColumnInfo := [(1,0,242,0,7),(2,0,241,0,7),(16,0,227,0,7),(32,0,211,0,7),(64,0,179,0,7),(128,0,115,0,7),(3,0,240,0,5),(33,0,210,0,5),(34,0,209,0,5),(65,0,178,0,5),(66,0,177,0,5),(96,0,147,0,5),(129,0,114,0,5),(130,0,113,0,5),(160,0,83,0,5),(192,0,51,0,5),(17,0,226,0,4),(18,0,225,0,4),(48,0,195,0,4),(80,0,163,0,4),(97,0,146,0,4),(98,0,145,0,4),(131,0,112,0,4),(144,0,99,0,4),(161,0,82,0,4),(194,0,49,0,4)]
def g243A : List (List Nat) := [[],[97,117],[16,101],[16,80,112,96],[80,118],[80,113,96,16],[96,16,81,117],[96,113],[112,81],[112,97,80,81]]
def g243D4 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0xc60c54617915cc734,0x8110c92e558358e52481,0x10c92e1593d953248110])
def g243D5 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then (word80 [0x434428df,0x2ac32e421a2143f9460f,0x7558910a1e4a307baac4,0x8861760c83dd5624428e,0xb2241eeab12210bf9460,0xf755891083f4c0eab9ac,0x48860fdd7845cd624430,0x78ebc22e6b122183f752,0x117358910c3c3af00b9a,0xc488437e61731cd62442,0x8bb27baca6b122187775,0x606535891083fcab0f21,0xac48852764f7490d6244,0x383eeba1c86b12218b77,0x4606435891083fcab0e2,0x1ac48841fe637510d624,0x420fb31ba886b122186f,0x756084358910c67b9b04,0x21ac48861edd58010d62,0x443176e8c0086b12218d,0xb736004358910e39baee,0x3b82c48841f6637598d6,0x24430f70bc02eca92210,0x7f9561d658c91083fcab,0xeb2464886275d383592,0x3244307f0bc22ec99221,0x83f85211764c910c3c42,0xf00bb2648863ce07805d,0x93244217f28c3eca9922,0x147591dd7654c910c2fb,0xab07b2a648841fe5586d,0xd13244296b23ba6c8992,0x2189f7460f644c91083f,0xcab0eb22648843ee6176,0x1c132443172ecc20e099,0x2211f3985c4704c910cb,0x8c2ae2382648866c6117,0x11c1324430f70fc2ac52,0x82213739560642941109,0xb9cab03194a088798e45,0x62549504420fb2fc2ac5,0xa02211f197e054290110,0xf88aa2a698a80885e465,0x5434c540443d2287b126,0x2a02210f997e1952cc11,0xae9cbb029966088674e,0x1d814cb30442ba32740e,0xe8902215e192a0774481,0x10c6c43706ba24088674,0x20f815d120442d932641,0x2c890221a7365e055448,0x110cacc2ae639a408857,0x4e45731cd20442cb32a3,0x9ac69022166995209634,0x8110d64b1b0529a40886,0x9ad958394920442cd72a,0xb1ca490221ac98358e52,0x48110b34cb2a6a924088,0x69a615658c920442d972,0x6b246490221a6b85d953,0x248110b64c9eca992408,0x85b264f644c920442e93,0x2a39a6490221789941cd,0x3248110be0c88e699240,0x885d2656634c920442d9,0x728b1a6490221ccb7458,0xd3248110e64ba2c69924,0x885b265a534c920442f,0x832329a6490221e4b655,0x4d3248110b64cb486992,0x40885f0646434c920442,0xd932ca1a6490221d8974,0x50d3248110ae849ae9b8,0xa40886f060d321c52044,0x2ae72aba4a2902219737,0x560a5148110de0c1a652,0x8a408874c5d154545204,0x42ec32b192a290221971,0x85dd74148110e99baaa9,0xa0a40886d861552d0520,0x443e42a8a968290221b4,0x9854cb31481108f8cc6e,0x918a408847ce61748c52,0x4433c50e99462902219,0x7385dd53148110ba8ca8,0xe698a40885e4650734c5,0x20442f832529a6290221,0xd517554d3148110be0c9,0x48698a40887645d1434c,0x520442f8327292629022,0x1b61855493148110fa0a,0x9aa498a40885f064e324,0xc520443b86e899262902,0x21dc1744c93148110f61,0xb226498a40887b059132,0x4c520443783069944290,0x221ec1634ca2148110cb,0x9c2eea90a4088758dd55,0x248520443cc2caa92429,0x221bc3834c92148110f,0x60b1a6490a408842fe51,0x8758d2044378264c0e60,0x90221ac9864c93048110]) else (word80 [0x714100090409040,0x898204881906,0x1608714412004000002b,0x4000000000000000000,0,0x204000000,0xa00168c100000000000,0x200108d010880,0x4080400002001002304,0x280040020604020400,0x810100040b9170ade5b,0x6b616aad259eb3164ac6,0x586b015eaba56ead158a,0xae556aa152aa253ea714,0xca96526a4146a8a50ea1,0x140a7e4f69e13aa724de,0x9b134a664c69812ea5a4,0xae95128a4e49692122a4,0x247e8f11ca364668c116,0xa2a44e89110a1e436861,0xaa1241e83104a064068,0xfe9fa3ee7d0f89ee3d,0x67a0f29e23be770ec9d6,0x3a6740e69ca38e710e09,0xbe3766e0da9b235e6b0d,0x49a6346680ce99a32463,0xcc397f2f85e4bb1732e0,0x5b4a893a26e4d0989292,0x4c48c9011d23445c8a11,0x121c42c841052043fc7e,0xf91ec3cc780ed1d439c,0x720e11bc36c6c0d51a43,0x3c660c91822f85d8b816,0xa2c8550a213e2704c896,0x1262404688a10e210408,0x7e0ec1a4308590ac14c2,0x804808a0f41d03705e0b,0x148210320580700b006,0x10bf9460f755872093,0xacaf02b26a39062d5d38,0x159351c8217f28c3ac72,0x8e418b574e056414720a,0x73c8ac8b90a39053ce45,0x645c051c8256b23c22c7,0x20e4189f845cd6390720,0x87bcc2e238ac690617dd,0x783595634830baebc0ac,0x631a4125f9560763cc92,0x9d5ca303b8264906f06,0x4d811c13248279326c08,0xe0992411bb94607704c9,0x20a5cca100b9ec290517,0xe55865ce6148293f28c3,0x2e730a419c9826017398,0x520c6ab9f02b1cc29041,0xf66375991614830beebc,0x1ac8b0a4185f7520d645,0x852083fcc6ea31ac2906,0xfdd68418d6148307eea,0xc20c6b0a415c9905cd32,0x18520c3bc3f0ab08c290,0x437e4d849db514830ef2,0xec0ecb28a410df936127,0x614520a4fc9b0cba0a29,0x41fe5587d8e414820ff,0x2ac3ac720a412b591e11,0x639052083fcab0fb1a82,0x9041fe5587d8e2148333,0x2e9c1a85182415c991dd,0x1324c120f45b22849926,0x9059665463585304836,0x970a992c2982419c9874,0xca414c120ce4c3a6510a,0x609052de458759152842,0x97321ba2c8a94214b990,0xdd56450a10c5cb2301b8,0xa650841fe5586dd12184,0x287f2ac3ac890c2149f9,0x361d6448610d52c1302b,0x22430852ee4174591218,0x43172c8c06e690c216a7,0x965094148610b52cb284,0xa0a43085aae498159120,0x842d3726ba2c890421e2,0x9955915248210d1dc2ac,0x8b8a410862b90982dd16,0x34421df30b90e4b1a218,0x9f84e0d7650d10a3dc82,0xebb2a868843be4987595]))
def g243H5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x24011036
def g243D6 (j : Nat) : Nat := if 11 ≤ j then 0 else (if j<5 then (if j<2 then (if j<1 then (word80 [0x273dc520,0x443f854b7148110fe132,0xdc520442dee157148110,0xbf1831c520443f84c871,0x48110f7375945204437c,0xdd25148110df17494520,0x442fc60e5148110f7153,0x94520442fc60a5148110,0xfe23294520443f84ca51,0x48110df374545204437c,0x5d15148110f715454520,0x443dc5495148110fe232,0x54520443f84c95148110,0xbf185d05204437cdd741,0x48110df175d0520443ec,0x5534148110bf182d0520,0x443f894b4148110fe152,0xd0520443ec50b4148110,0x9fa87d05204427e61f41,0x48110bf182105204427e,0xa1f31481109f987cc520,0x442de6173148110be982,0xcc520443f24cb3148110,0xdf3748c5204437c5d231,0x48110ef1648c520442fc,0x60e3148110bf1828c520,0x443f88ca3148110fe132,0x8c520442fce153148110,0xbf1854c5204437cdd531,0x48110df1754c5204437c,0xdd13148110df1744c520,0x443bcd913148110ef164,0x4c520443f4dcd3148110,0xfd0734c520443f494d31,0x48110fd1534c520443f4,0x90d3148110fd1434c520,0x442fce093148110fe252,0x4c520443f85493148110,0xfd3324c520443f88c931,0x48110fd1324c520443f2,0x4c93148110df37488520,0x4437c5d22148110ef164,0x88520442fc60e2148110,0xef16388520443f84ca21,0x48110df375485204437c,0x5d52148110ef36548520,0x443bc5952148110bf383,0x48520442fc60d2148110,0xef36348520443bc58d21,0x48110fe15248520443f8,0x4c92148110c7f855d920,0x4423fe0d76481109f581,0xdd12044277e0d7448110,0x9f7815d120442bbe0964,0x481109f7815cd204427e,0xe0173481108fd8758d20,0x44337dcd6348110aef82,0x58d204429fe156248110,0xecd634c9204427d60f71,0x48110dd7734c520443f1,0x4c93148110b7985d0120,0x4436edd34048110be982,0xd0120442fc6074048110,0xaf986501204433e5d940,0x48110df37150120442fa,0x60b3048110fc932cc120,0x442fc6073048110df371,0xcc120442be6193048110,0xfc9324c1204421fe1571,0xd8d208df8758c6348317,0x5d56318d20b69851c132,0x482ea610704c920be181,0x1c1324823de1d6118520,0xa7581d96514831ed9570,0x94520c3f655d0514831b,0xd957214520c7b655c051,0x4821fe157690520d6975,0x54a30482d6614634c120,0xbc98394930482f260e32,0x4c120dcb744c930483b2,0xd91324c120dc932dc530,0x4832e5917094a10cb964,0x5c2428432e591708ca10,0xcb9645c3218439a58952,0x54210ea964949208439a,0x5955248210ea96454920,0x843aa5923248210ea964,0x4c920843b258d3248210,0xc7b65dc1534429b60b65,0x94910c7b655c2524421f,0xe15768c9108bf845d932,0x4439a5895254110f9143,0x4c54044378605720c110,0xdd1724c4304439ad9652,0x48110e696554920443b2,0x58d3248110d737594520,0x443d85495148110eb364,0xd05204427ca1c4148110,0xb718510520442f460c41,0x48110be182105204427c,0xa1e3148110fc1324c520,0x4421fe157648110d9174,0x4c430443705c9310c110]) else (word80 [0x358b3044,0x33d58971cc110dd5325c,0x7304423fe09764c110a7,0xf8558930442b7e0d624c,0x110df1815c8304427de0,0x574c8110aef825932044,0x3375cd63c8110aef8258,0xf204433d59171c81109f,0x7835c7204433d58d71c8,0x1109f5874c720443755c,0xd31c8110df1715032044,0x3765cf30c8110be982cc,0x320443f24cb30c8110df,0x171cc3204433ee1d6488,0x110cfb8758e204436e5d,0x14288110bf38150a2044,0x2fce0931881109f984dd,0x5204427ee117548110df,0x3815d5204435edd57548,0x110bf3815d5204439edd,0x76548110af984d952044,0x2be60f65481109f985dd,0x1204437ca077448110df,0x181dd120442fc6077448,0x110b79859d1204436edd,0x27448110bf1819d12044,0x33e21974481109fb855d,0x12044376e0d7448110dd,0x8835d1204437ce057448,0x110df0815d1204436edd,0x17448110bdb835d12044,0x2f620d7448110bf3815d,0x1204427ea1c7448110af,0x983d9120442de6166448,0x110be98299120442bee0,0xd6448110eeb825912044,0x3ba2096448110beb8259,0x1204427ea1e54481109f,0x98795120442be61a5448,0x110db974951204427ea1,0xd54481109f9875512044,0x35edd55448110e7b6555,0x1204436e5d15448110bf,0x38155120442fc6067348,0x110bf3815cd20442de61,0x47348110bba841cd2044,0x2ee6107348110dd9731c,0xd20442fc6047348110af,0x984d8d204433edd36348,0x110cf974d8d20442de61,0x66348110be98298d2044,0x2bee156348110afb8458,0xd204433edd16348110cf,0x97458d20443b6dcd6348,0x110ed87358d20443bae0,0x96348110ee88258d2044,0x2fae096348110af98694,0xd20443b658e5348110be,0x98294d20442fc6065348,0x110af98654d204435e5d,0x55348110e7b6554d2044,0x3b658d53481109fa87d0,0xd204427e61f4348110af,0x986d0d204436e5d34348,0x110af98690d20443e6d0,0xe4348110be98290d2044,0x2fc6064348110af98650,0xd204436e5d143481109f,0xa8710d204427e61c4348,0x110af98610d20442de61,0x44348110be98210d2044,0x2fc6044348110be98394,0x920443ba58e5248110f6,0xb7554920442fae0d5248,0x110ee96354920443da54,0xd5248110fe1815492044,0x35edd55248110e796554,0x920442be61b4248110db,0xb74d09204436edd14248,0x110bf38150920442be61,0xb3248110ed963cc92044,0x2fc6073248110be9858c,0x920443bad963248110ee,0x9658c9204437add23248,0x110de9748c920443bad9,0x23248110ee9648c92044,0x2fa60e3248110eeb638c,0x920443ba58e3248110be,0xb854c920442fa6153248,0x110eeb654c920443ba59,0x53248110deb744c92044,0x37a5d13248110eeb644c,0x920443ba5913248110fc,0xb734c920443f21cd3248,0x110eeb634c920443f298,0xd3248110fc9634c92044,0x3f294d3248110fc9534c,0x920443f290d3248110fc,0x9434c920443f8a053248,0x110fe1814c920443b658,0xd3248110bf185dc52044,0x37c5d77148110df174dc,0x520442fc60f7148110df])) else (if j<3 then (word80 [0xc2324423,0xf617764c9108fd84dd93,0x24423f603764c9108ff8,0x45d9324432fe11764c91,0xcbc845d9324433be097,0x64c9108ff815d9324433,0xde05764c910cfb805d93,0x24425fe15764c9109bf8,0x45d9324429fe15764c91,0xabf845d9324423f61b7,0x54c9109f581dd5324423,0xfe19754c9109fb805d53,0x24423f61f654c910c7f7,0x5d9532442b760f654c91,0x8fd86dd1324427d6077,0x44c9108ff865d1324427,0xee01744c9108fd87d913,0x24432fdd3644c910add8,0x3d91324423fe1d644c91,0x8fd8759132442bb60b6,0x34c910b5d8598d32442b,0x761a534c910bd58194d3,0x2442b761a434c910bd58,0x190d32442b760f624c91,0xa7f8558932442b7e0d6,0x24c910be98090932443e,0x350d424c9109f980dc53,0x24433ea1b704c9109f98,0x5dc1324427e613704c91,0xcfb63dc1324437694f7,0x4c910cfb62dc1324433,0xe58b704c910df281dc13,0x24437c607704c9109f58,0x1dc1324433e9db704c91,0xcf976dc1324437c9c77,0x4c910df171dc1324433,0xe5d8704c910b79851c13,0x2442ee610704c910df17,0x11c1324427ee11729411,0xcfb8758a504439ee156,0x294110cf97458a504427,0xe61e4294110af98690a5,0x442fc60642941109f98,0x750a504436e5d1429411,0xbf38150a504427e61e3,0x294110af9868ca504437,0xa5ca3294110bf1818ca5,0x4427ee1d3294110de97,0x24ca504439ee15625411,0xef38158950442dee0d5,0x254110e796254950443d,0xc60552541109f9879095,0x442be61a4254110b798,0x590950442fc606425411,0xbf381509504427e61e3,0x254110af9868c950442d,0xe6163254110bf1818c95,0x4427ee1d3254110b798,0x54c9504423fe1d62d011,0xa7f8558b404431f5d56,0x2d0110abf8458b404433,0xb5c962d0110d3d7550b4,0x4433d58971d0110db54,0x25c740442bee09639011,0xcf9635ca404437c6057,0x290110cfb8758a404439,0xee156290110afb8358a4,0x442be61a4290110de97,0x290a40442fc606429011,0xde97250a40442fce054,0x2901109f9878ca40442b,0xe61a3290110de9728ca4,0x442fc60632901109fb8,0x74ca40442be619329011,0xde9724ca40442be60b6,0x350110ebb8458d40442b,0xee096350110bbb8458d4,0x443b658d5350110af98,0x3d8940442ee612625011,0xb7b8558940442eee116,0x2501109f9878c940442b,0xe61a3250110bb9848c94,0x442fc60632501109fb8,0x74c940442fc60a515011,0xdf37294540443ec50d5,0x150110df37254540443d,0xc5495150110bf1828c54,0x4437c5d53150110fd15,0x34c540443bcd89315011,0x9fb855cb304437654d7,0x2cc110df1815cb30442f,0x660e62cc110b7b8558b3,0x442f6e0d62cc1109f98,0x794b30442f660e52cc11,0xbf18194b304427e61d5,0x2cc110afb8654b304435,0xe5d552cc110ddb874cb3,0x442f6e1532cc110bd98,0x54cb30443765d532cc11,0xfd1814cb304437c5c95,0x1cc110f715254730443f,0x44c951cc1108ff8758b3,0x4429fe1562cc110adf8]) else (if j<4 then (word80 [0x20843ae5,0x913248210ed9634c9208,0x42dee157148210eb9645,0xc520843ae5914148210e,0xb96448520843bc585214,0x82108ff845cf654423fe,0x973d95108ff835cb654,0x423fe0974d8d108ff845,0xcb634423f6177458d108,0xfd82dd1634423f613725,0x8d10cef729c963442bd6,0x67258d10abf845c9634,0x42bde057258d10abd841,0xc9634433b5c87258d10a,0xdf83591634423fe09769,0x4d109fb805ca534427e6,0x137054d109f982dc1534,0x423fe097690d109fb805,0xca434423fe157650d10c,0xdf835d9434423fe09765,0xd108ff865d5434427ee,0x17550d108fd87d95434,0x431f5d76550d108fd875,0x95434423fe097610d10c,0xee865c8434433b619721,0xd10de9805c8434423fe,0x1173d89108fd8790f624,0x43a7d0e43d8910af5819,0xf624423f61d43d89108,0xfd8710f624429f61443d,0x8910aed8210f62442be6,0x43d8910cdd7358e624,0x42bbe096398910c7f83d,0xd5624431fa0f7558910c,0x7d83dd5624431f20f755,0x8910c7d82dd5624431fe,0x37558910c7d80dd5624,0x423f60f7558910e7b80d,0xd562442bee0175589108,0xfd85dcd624423f613735,0x8910c7f75dcd624431f1,0xd77358910a7d859cd624,0x431fdd67358910cdf739,0xcd62442bd6067358910a,0xf9809cd624429fe15735,0x8910c7f755cd624431f1,0xd57358910abf845cd624,0x42af2117358910af7815,0xcd62442bee017358910c,0x7f751cd62443375cc735,0x89108fe8794d624423f6,0x1e5358910c7f7594d624,0x42bd60653589108fe879,0xd624423f61e4358910c,0x7f7590d624432fdd2435,0x8910e9f4390d62442bd6,0x643589108fe8750d624,0x431fdd543589108fe871,0xd624423f61c4358910a,0x7d8510d624431fdd4435,0x8910cdf7310d62442bb6,0x84358910af98010d624,0x42be6177058910e7b75d,0xc1624439e1d77058910a,0xf984dc162443bcdc7705,0x8910c7f75dc1624435ee,0x37558910a7d8598d624,0x431fdd66358910cdf739,0x8d62442bb60a6358910c,0x7f7558d6244337dcd635,0x8910aef8258d624435ed,0xd77058910df371dc1624,0x431fe1576949108ff835,0xda524431fd9573949109,0xfb805ce524439be15629,0x49109fb845c2524423f6,0xf7654910c7f855d9524,0x423fe0d7654910cfb805,0xd9524423f61b73549109,0xf581dcd524427e603735,0x4910e6f8558952443bae,0x16254910a7f85589524,0x437c5c57054910add83d,0x8b324429fe1562cc910a,0xdf8358b324433dd8971c,0xc910cf5625c7324423fe,0x15768c910c7f855da324,0x431f215768c9108ff845,0xda324425fe15768c9108,0xfd87d96324423f61d658,0xc910c7d75596324427de,0x5748c9108fd87d92324,0x423fe1d648c9108fd875,0x92324432f5d1648c910a,0xdf8359232442bb60b638,0xc9109f7855c6324433dd,0x95718c910cf5655c6324,0x433dd91718c910cf5645,0xc6324433dd8d718c9109,0xfb855c2324433ed95708,0xc910cf9655c2324427ee,0x11708c910cfb645c2324,0x433e591708c910cfb635]) else (word80 [0x4837a8c9,0x718c120de9325c630482,0x7ee1d618c120cfa76586,0x30482dee15618c1209f9,0x87506304837c5c5218c1,0x209f981dd530482f6e0d,0x654c1209f981dd130482,0xf6e0d644c120bd985d8d,0x30483b6593634c120f6b,0x6554930483f260d524c1,0x20fcb6354930483aed91,0x424c120fc8864c930483,0xf2e11324c120fc9844c9,0x30483f2d91324c120fc9,0x644c93048376dd1324c1,0x20edb644c930483f2509,0x324c120ddb63dc530483,0x764cb714c120be9829c5,0x30483f24ca714c120beb,0x825c530483f24c9714c1,0x20fc932d8530482f660e,0x614c120fc93298530482,0xdee15614c120bdb83585,0x30483b618d614c120fc9,0x3258530483f24c8614c1,0x209f98794530483da549,0x514c1209f98790530483,0xf24ca414c120fc932505,0x304827e61e214c120fc9,0x3288530483f24c9214c1,0x20fcb804c930483f2601,0x324c120abf825d564842,0xaf6167259210abd819c9,0x64842afe157259210cbd,0x755c964842afe0572592,0x10abf825c5648432f5c9,0x71592108fd84dd562842,0x3f6177458a10a7f855c5,0x628432f61d6494a108fd,0x87592528432f5d16494a,0x10cf9645c2528423f613,0x7654a108ff845d952842,0x3f61b7454a109f980dd1,0x528432fa1d6454a10cbd,0x87591528438f6156454a,0x10cbf74591528423f61d,0x6590a10c7d7559642843,0x2f5d56490a10cbd645c6,0x428433e5957090a108fd,0x85dd9428423fe157650a,0x108fd86dd5428427e603,0x7550a10cbf7559142843,0x2f5937150a109f980dc5,0x428432f591718ca10ced,0x625c6328432f593714ca,0x10cdd63dc5328433b58b,0x714ca109f980dc532843,0x3e61b704ca10cf962dc1,0x328433e5db704ca10ed9,0x63dc132843ba58b704ca,0x108fd878c961842bd606,0x3258610af9808c961842,0xafe194250610abd86509,0x418432f61d64c8610ead,0x82593218432f5d164c86,0x10cbd645cf218427ee01,0x73c8610cdd7358f21843,0x3b5cd62c8610aed8650b,0x21843ab59142c8610cf9,0x645c3218433e58d70c86,0x108fd86dd1218427ee01,0x7448610cbe8759121843,0x2f61d6448610eae82591,0x21843ab6096448610eb5,0x81591218432fdd164486,0x10cbd74591218423f61b,0x7348610cbd64dcd21842,0x7e6037348610aef84589,0x218433bdcd6248610aed,0x8690921843ab59242486,0x10aef8650921842bb619,0x4248610ead6450921843,0xad5914148610ee562505,0x21843e950941486109f9,0x84dc1218437c50770486,0x10e7962549508427e61e,0x4254210af98690950842,0xde6164254210af985dd9,0x20842be6137648210af9,0x83dd9208427e61375482,0x10cfb865d5208427ee11,0x7548210afb865d520842,0x7e6177448210afb865d1,0x20842f6e0d7448210eb9,0x8559120843ae5d564482,0x10eb98259120843ae605,0x6448210eb97459120842,0xbee197348210eb9645cd,0x20843ba5925248210eeb,0x7654920843ba59152482,0x10e796554920843ae591,0x5248210eb96450920843,0xba5863248210eeb764c9])))) else (if j<8 then (if j<6 then (word80 [0x23fe1173,0xd8520cfb805cf614823f,0x60173d8520cf8805cf61,0x482bee0173d85208fd87,0xccb61482bee0163d8520,0xcdd865ce6148337d9173,0x98520dcd825ce6148376,0x6017398520cdd7358e61,0x482bde0563985209ed87,0x8ca61483735ce3298520,0xde9708ca61483735cd32,0x98520af583d8661483b9,0x4cb6198520d7b80dd561,0x4831fdd56558520c7f75,0xd91614831f1d76458520,0xa7d85991614831fdd664,0x58520cbf7499161482b7,0xe0d6458520adc8359161,0x4831fdd76358520c7f75,0x98d6148337dce6358520,0xc7f7558d6148337dcd63,0x585208fe8718d614829f,0x6146358520c7f7518d61,0x482afa106358520abd84,0x18d614835bdd65258520,0xd6f75549614839bd9552,0x585209ee878c9614835b,0xdd63258520d6f754c961,0x48373dcd3258520d7b75,0xdc1614835e1d77058520,0x9f9805d0614823fe1d64,0x18520adf83590614827e,0x60173185208ff8758c61,0x483735cd3218520cf787,0x584614839de156118520,0xcf573584614823f61276,0xd45208ff845db514823f,0x61f64d45208fd849da51,0x4823f60e7694520c7f85,0x5da514823fe117694520,0x8ff835da514831f61f65,0x94520a7d83d96514839d,0x6076594520c7d76d9651,0x482dd6076594520c7f65,0x5d2514823f61f6494520,0xaf581d92514823f61f63,0x94520cdd73d8e51482bd,0x6076394520c7f655ca51,0x4839dd956194520e7764,0xd46514835ed957094520,0xcfb645c2514837a8c970,0x945208fd849d9514823f,0x60e76545208fd87d9151,0x482bd60764545208fd87,0xd8d51482bd6076354520,0xb6d858c9514823f61276,0x145208ff845d8514831f,0x61f6514520c7d76d9451,0x4832fa197414520cbd86,0x5d0514834fd957414520,0xdb9805d0514831fd9574,0x145208fd87d90514832f,0x5d36414520cdf645cc51,0x4835bd957214520cef64,0x5c8514831fd957214520,0xd7b655c0514833ed9170,0x145208fd839da414831f,0xe1576905208ff835da41,0x4825fe157690520af581,0xd92414823f61f6390520,0xcdd73d8e414823fe1d63,0x905208fd8758e41482af,0xe116390520dcd734ca41,0x4833ed917090520dea32,0x5c2414837a4c97090520,0x8fd839d94148277e0d76,0x50520adf835d9414823f,0x61b73505209f980dcd41,0x4823f61f6350520cdf73,0xd8d414823fe1d6350520,0x9f980dc941482af61361,0x505209ed82dc1414823f,0x61f64885208fd87d8e21,0x483375cf6388520af781,0x58e21482bd6136188520,0xaf583d8621483b94cb61,0x88520cfb645c2214837a,0x4c97088520c7f75d9521,0x482bde056548520af781,0x58d214839bd955248520,0x9f985dc1214827e61370,0x485209f983dc1214837a,0x54b7048520de932dc121,0x48337d8d71cc1208fd87,0xd87304827e616768c120,0x9f9849da304827e60676,0x8c1209fb87596304827e,0xe1d648c120bdb8359230,0x4837a5d2528c120dea76,0x54a304837a5d1528c120,0xd797554a304836e5d142,0x8c120bdb8350a3048376,0x5cd328c120cfb645c630]) else (if j<7 then (word80 [0xd2694996,0x264098125c896c257495,0x7252094224cc92424549,0x624008fa23ac8d322ec,0x8ac22988a02220879218,0x4852210c82b207081620,0x408011fc87e31f507c51,0xeb479e1e3c7801dc476b,0x1d7074d1cf872f1c386f,0xf1bc06cf1adc6a81a886,0x931a3467e19bc6601944,0x63918a861b18545fd17b,0x85df17405c116a45a316,0x5058515b455e15605491,0x4e8534149450d141c501,0x13804bf127847d11b845,0xf11404381080411102c3,0xea0f483ba0e6436f0d80,0x33f0cc03210c483030ba,0xc2d30ac829109e425808,0xdc21f084020107c81ec0,0x7501aa064817a058814a,0x48011103c00d803000a,0x80240078018003600c00,0x1800023f6137558a308f,0xd85dd1628c23f6077458,0xa30adf835d1628c23f61,0x37158a30a7f855c5628c,0x23fe0572d91308ff825c,0x7644c376dcf7058930af,0x78158a614c33bdca6258,0x5308ff825da414c2afe0,0x97559030abd859c9640c,0x2afe157259030cbd755c,0x9640c3a7e0d7259030ae,0xd85dd1620c2bbe157458,0x830ecf835d1620c23f61,0x774588308fd84dd563c8,0x23f6077558f20afb805d,0x563c823f6177458f208f,0xd81dd163c823f6177158,0xf208fd84dc563c82b760,0xe7158f20af9809c563c8,0x2afe117158f208fd84dd,0x561c823f60f75587208f,0xd85dd161c823f60f7458,0x720af5819d161c823f61,0x773587208fd84dcd61c8,0x29f6167358720af5819c,0xd61c82afe117358720ab,0xc845cd61c829fe157058,0x720c7d655d351c823f61,0xd64d4720cbd7459351c8,0x2bde0564d47208fd8759,0x251c832f5d164947208f,0xd8758e51c83375cd6394,0x720cf57458651c833d5c,0xd6194720e7564d4651c8,0x23fe1176547208ff835d,0x951c829fe116554720cb,0xd865d051c823f61d6414,0x720cbd7459051c82bde0,0x56414720cdd645cc51c8,0x33b5917214720cf9645c,0x51c823f61d6390720ab,0xf8458e41c83375cd6390,0x720cf57458641c833d5c,0xd61907208ff835d941c8,0x23f61b7350720cf77558,0x541c82bde0d6150720cf,0x77358541c827b60b7050,0x720cf561dc141c833758,0xd71cc320cf57158730c8,0x27e60372506208ff845d,0x7634823fe0575d8d208f,0xf855d3634823fe0574d8,0xd208ff855c7634831fe1,0x571d8d20c7c855c76348,0x23fe1171d8d20a7f855c,0x7634825fe1571d8d20cd,0xf635c6634823f6177458,0xd208fd81dd1634823f61,0x37158d20aed829c56348,0x33ddc67158d20abf845c,0x563482bbe097158d20cf,0x5711c563482b7e0d6558,0xd20add85d8d6348337d8,0xf7158d20edb63dc16348,0x337e1d6318d20adf8158,0xc634837c6017118d209f,0x9805c463482b760763cc,0x920cdf635c732482fae0,0x1744c920be985dc13248,0x2fa613704c920fcb63dc,0x132482fa607704c920be,0xa861c132482fa604704c,0x9209f985dc1324827e61,0x3704c9209f981dc13248,0x23fe1175d85208ff835d,0x7614829f61674d8520ae,0xd829d361482be60274d8,0x5208ff855d3614823fe0,0xd74d85208ff855cf6148]) else (word80 [0x5a547950,0x653b94b2526948251194,0x2e50593fe4f993aa4d29,0x3324c692ba4a8926648a,0x91ee46c919a457914644,0xb911643f90e643390924,0x15901a4008fc63eb8f96,0x3df8f663d38f363c78f0,0x63bb8eb239d8e5e3888e,0xa3738db63678d623498,0xcc63198c4e3048bfa2ef,0x8b822d18b0a2b38ab629,0xe8a3e27789c6259892a2,0x3b88b2226888221a8852,0x20e87fe1f987ce1ed877,0xa1d887261c386f61ae86,0xa2199862a18485fa16f8,0x5a615a855214584da130,0x8486112843210683960c,0xd831e0c182ee0b582be0,0xa0826a08b821607681c2,0x6a819205e813e04080e,0xa02b807200d7ff9fef7f,0xa5fe37f51fc57efdfb97,0xea9f9b7e31f7d7db9f68,0x7d41f417cc9f2c7c75f0,0x57bd9ee77b3dec97ae9e,0xb47ab9e9f7a1de8179ed,0xe5178c1e217801dfa776,0x5dc176eddac7675d9776,0x45d8b75f1d6d759dd617,0x549d4c74f5d2e747dd19,0x744dd0d741dcef7381cd,0x1732dcbc72d9ca77261c,0x8971e9c597129c3b708d,0xc1d705dc11702dbf36fb,0x5bde6f61bd26f31bc66f,0x1bb16e89b9c6e59b876,0xde1b726db1b666d81b51,0x6d2db3c6cb5b276c85b1,0x26c0daf46b95adf6b65a,0xd36b11abe6abdaa06a45,0xa8b69f1a6d699da61696,0xda55693da4068e9a2b68,0x71a16681d9f867a59e36,0x7519ce67219b966cd9a4,0x665598f662598365f597,0x765a1962654d94d64d59,0x26648191a642d90563fd,0x8f963858db63318bd62d,0xd89f626588161c986361,0x5183c60b582760618096,0xd7f45fb97df5f417ca,0x5f117b55ebd7a95e8d79,0x45e1577f5de576a5d497,0x435cd172e5ca17195c29,0x6fb5bd56ef5b816d15b0,0x96b35a916955a1968059,0xc56625971656591d6415,0x8c962c587561758215f0,0x57a95db57315c656dd5a,0x8564158155ed57555bd5,0x6054fd53954a951b5431,0x4fd53954d652f94a6525,0xd49151c146a519145550,0xf540a50113fe4fbd3d74,0xf453c24ef13b64ec13a1,0x4e6d3954e193804de936,0xb4d713444cf93384cc93,0x2c4c993204c212f94bcd,0x2ed4b792cf4b012ba4aa,0xd2a54a5928749e126049,0x4524248f123648c12214,0x84920347d11ee47a11d9,0x47291c446b11a6465d18,0x8460917345b515e453d1,0x4044e9134449511f4441,0x10143ed0ec43750ce42f,0xd0b942a90a4425508f42,0x107141ad065413503e4,0xbd0204044ff93fa8fe4,0x3f54fbd3eb8fa83e40f8,0x13dc8f6c3d74f4e3d20f,0x393ca8f243c78f183c48,0xf033bd0ee53b58ec73b0,0x4eb23ab0e9d3a38e7f39,0x9ce4f3924e3a38ace1c3,0x834dfe37bcde03768dcb,0x36f0dad3654d8635dcd5,0xf351cd4134ecd2c3498d,0x203468d0b33f0ce43354,0xccf3324cc332d0ca5325,0x8c903204c7b31d4c6631,0x5cc4830e4c333090c1e3,0x3cc09300cbfd2fb8bdf,0x2f40bc12eecbac2e74b8,0x52dfcb792dccb642d30b,0x2b2c70b0d2c1cb012bc8,0xaec2b74ace2afcab92ac,0xcaad2a78a8f2a00a7129,0xaca652958a4728e0a292,0x88ca1d2838a0828089f3,0x27b49e727609c9270c9b]))) else (if j<9 then (word80 [0x80000010,0x5460a8c1170200080041,0xa0a8c120820008004000,0x2080005810b02000230,0x8580040008301040400,0x2008c100460800108028,0x400046088c02119010,0x1020100011a002030206,0x11842e044608ac82148c,0x100040022305000a0014,0x2a3008402054608081,0x400200041910202040e0,0x99146000c04080810340,0x6001c000c10141000008,0x4000800100820502,0x4010400080028004000,0x40c0a001c10382408400,0x101028502042404000,0x2230400102070304000,0x12b201c30a0403018502,0x180c28100c061605420,0xc8410c48420c48420c02,0x5820180c2018080418,0x804180a061409040302,0x50108860281c8810a03,0x22042c08602c14883010,0x5820180c2c100c07220c,0x414080603080602818b,0x88c10581910322040088,0x582037142a14102a1608,0x2c15081922080416080e,0x8030084830217080583,0xb05020a05820a05820a,0x5820a05820805820904,0x10061000b05420b0542,0xd8cf62dd89f621d86f61,0x5d83f609d80f5fdd7df5,0xf1d7af5dcd75b5bed6bf,0x5a0d66b58bd5f356dd59,0xf561d56f555d53f549d4,0xeb534d4bb528d467513d,0x4374fed3bf4e9d38f4d4,0xd33b4c8d30b4bcd2db4a,0x7d28749bd23347dd1bb4,0x68d18b45cd15b450d12b,0x43bd0b341dd05f411d00,0xb3f3cfb73e7cf633c9cf,0xf3bdcedf3b1ceaf3a5c,0xe7f399ce4f384cdfb36f,0xcda7363cd77357cd2334,0x2ccf3336ccc332acc6f3,0x15cc3f300cbeb2f4cb97,0x2dfcb432cacb132becae,0x32b2ca8f294ca3b288c9,0xe7261c94b243c8d3225c,0x85b210c82b204c7fb1f8,0xc7cb1ecc79b1e0c76b1c,0xbc7171b6c6c31aac6931,0x95c63f177c5c7162c54f,0x144c4fb138c4cb12cc47,0x7117c4470f9c3ab0e4c3,0x570c6c2df0b1c2af093c,0x237087c20707bc1b3054,0xc11702dc07b00fc026ff,0x1bf66fd3bf36fbebebef,0xa0be46f82bdf2f6dbd7a,0xf58bd26f3abcd2f2ebc7,0xef19bc2af04bbd6eefbb,0xa6ee3bb76ed7bb46ec2b,0xaf2eb6bac2eaaba92e95,0xba1ae80b9c6e6bb996e5,0x6b942e4ab912e35b89ae,0x20b846e0bb7cededb79e,0xdd8b74adb1b68ad8ab61,0x2d75b59ad60b546d4bb5,0x16d3fb4e6d2ab46ed15b,0x43ed00b3c6ce2b372ccd,0xb31ecb8b282c9ab22ec8,0x5b1fec79b1cec64b156c,0x4fb126c3ab0aec1cb036,0xbf5af9abe0af6abd4af3,0xabc8aee6baaae6eb8cad,0xd2b6eada2b59ad2ab3ba,0xcd6b2fac82b1aac52b0e,0xabfeaf9abceae4ab7aac,0xfab02abaaaaeaa5aa7ea,0x90aa2aa7ba9d6a66a95e,0xa51a90aa3ca892a15a81,0xa9f7a7a29d9a74e9b2a6,0x6a979a586949a4ea92ba,0x44e904a3d68efa3828d1,0xa29e88fa202871a18a85,0x3a112823a0528059ffe7,0xf09f867d29f0e7b49e96,0x7849d8e75d9d5e7519d0,0xa7339cb67159c1a7009b,0xea6f49bba6e89b666d39,0xb126be9abe6a99a6a68b,0x99f266d999e658994a64,0xc991a62e98a262298726,0xd981e5f897ca5ec9776,0x5d797465c296f25b6969,0xe598964a58395d256595]) else (if j<10 then (word80 [0x40800,0x10018080020404080,0xc04004e082060223042,0x85c10802000c01020c,0x41408260b4006148104,0x130a0402042808502612,0x101020108103020803,0x1080e220104160811183,0x82040c0a001088600c18,0x1c10102000810a020704,0x4081c10882030120030,0x1808001800000004c408,0xa00044104000000000,0x2000410008080000502,0xa881000200001000000,0x2000800000002008c100,0x2000010400000088,0xc1000a08001008322040,0x20800000100000020000,0x23040a00080014aa30,0x804082a2040008001000,0x800000000004180832,0x20402202000000000000,0x8c1080200401002008,0x30151020a51040903,0x84001c10020083010103,0x220404080100644088c0,0x41000c03040a06820808,0x10000000000080000020,0x40000200000040008201,0x4000020800004005820,0x1040058202040018a040,0x18623608400000000081,0x60800004000001820,0xa8810180081010b02000,0x402080050410b020000e,0x4000858107020f04007,0x82c20002000400582050,0x1840506820c140610005,0x40030a0e14061000014,0x4010008050200c30703,0x22a0d003030a04018785,0x20404181a0020000304,0x10702000000400002000,0x60c08000006140210581,0x82005810000080c100,0x2010422108306110400,0x9048010000003140010,0x504000000001020004,0xa080810000000102,0x81208200002040208,0x50101020000004100080,0x83c10002000010002000,0x1000208101000,0x40814100020004100001,0x2001410002000000000,0x10000080150a0401040,0x2080000c500840050,0x11202031402100140304,0xc5040c0818104c8c2008,0x20014182820014100460,0xd0410000282000000010,0xb0200005041a80080208,0x141000408201040a0800,0x410302050700083c10,0x201040010241040000,0xc0804504022820044103,0x49020002091410022081,0x81228102000200001041,0x849150818041060c0904,0x10082450204410449230,0x8280108480802b802003,0x4832404048904019,0x8b24140001008ac10101,0x81040000408200106040,0xc0820115820200000,0x6280824002000000,0x40c08001000208002040,0x808112000240022404,0x208206040e0d0410,0x118201040065042014,0x408081000c0800107040,0xe0810000402008c10402,0x201048382070408001,0x4083020008101020018,0x200840104040a8c10082,0x23008541040518281000,0x423040118402c1021004,0xc102020401183810400,0x100a001400206040,0xc0800204000028104040,0x88d0210ba44100010402,0x8081118202070208001,0x4088c1c1022300840,0x20702088f02108d02100,0x401000002c0c1810b0,0x8200820000004101022,0x30409102000230428080,0x81000200081000008000,0x2304280848108020400,0x18002070304000005019,0x1a0020a48c2418081080,0x20001004008021006820]) else (word80 [0x102066208060,0x80010006080010182000,0x40000020200,0x4020800000100000,0x4080000410202010,0x40000000000208041008,0x20000104020800004101,0x2000000000000000810,0x608000000141000000,0x800004100000020,0x10000000184080810,0x98217090413042008,0x44108020704000000000,0x2080000400000,0x82003414100c0058408,0x1000000a0020008661,0x521040a002160642080,0x3a4810000000001028,0x420703420b040e041c0,0x8011a004101284001400,0x4220d001a00202040c10,0x202040a0021604000060,0x80000400002000000000,0xd040000000008205040,0x6820000104000000020,0x50400282000c02100001,0x41000ac3008605060ac2,0x8000820104002820000,0x40a080000410282,0x1040028205001520042,0x800800000008102820,0x400080010082050,0x8540040000000200340,0x40008001084842000c1,0x2110422080004010000,0x2008000401000408081])))))
def g243H6 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then (word80 [0x1c02e,0x115bc800000003200000,0x41b8415e01c7809d8040,0x143040000,0xc71fc30c000390f3118c,0x242a8000005340002,0xc4a54488000200b9023c,0x81c810cc000140bc0003,0x80f00000000350c59854,0x5273826c00000002,0x104c000109be0192815b,0x2354848000180cc0003,0xd007c0ea807280c3c076,0x81e219b64124000298f0,0x25649b881740001,0x9b0c8145c29000000887,0xc0b000000001448110c3,0xc2100000c22000000000,0xc4bd00800002c23a817c,0x3c1062530,0x28c95402901438011,0xd8640000000110460003,0xc20c40c400000002c9d8,0x81f000d082a782c00003,0xc276c178000350a5c1b5,0x4e4a58f402610044c019,0xe4b80001410ec0300000,0xc2880001c1d80003d070,0x141ed00d80003c048,0x8160ca4b000a4120,0xe130c20400018090d028,0x1140000000000000034,0x181a6e4aa,0xc249506302f5c07e24b0,0x42ae0268ce7e8085c318,0x242e00000,0x2806000000000,0x2903500040001,0xc415a54cd8474516421c,0x2816882800000,0x1405cc2f0002180f5,0x5c7d00af80380003d02c,0x802400028d1a0297,0x31c0000000000000000,0x24228,0x9190000042be116a512b,0xc2dc000392e3406ec103,0xd474927c92824299406b,0x8d5240c80003c0e784a2,0x604000000000000102d4,0x81b153119ec0002,0x12c0002480800000002,0x300000000000a3cc108,0x1100002,0x826400000002d15c0002,0xf885200000404cc930,0x302cdc2c80003c00e,0xe3c0001811890ec4199,0xe4fc00000003c14b0258,0xc524000112e8409b,0x908e0200000000028948,0x381cc,0x8173c54240ffc9504244,0x210fc0001104a428f,0x80e240b6c28541e4c271,0x549c3138180016dc8a0,0x3150e8600a000020d1f,0x418502b0000000000000,0x2c14c90240002424c,0x408bc1d3c03d,0xc531c19c000290080003,0xd9b2c1ff951100500000,0xc8780000000000004232,0x1d01af10d2c067984b,0x940000000282e742a0,0x382c641be,0x4214000290bc00039164,0x12e4000380d4,0x1c6c082b700dc,0x16591888824c1340001,0xc1eb42f91161d10051a0,0x110400000003c0540002,0xc18e821800000001c811,0x50d600a4000000000001,0xd86c000000000001811f,0x132512c000192ef9055,0xc1d40002822c00019d39,0xc9a400028195c4eb418b,0x82ec0000000000004224,0xc1a8000301b000000001,0x827882d8000000018a1d,0x24b40001cca38d380003,0x5058c29c0003db08e5a0,0x2005bc1c0,0x2b800000003c2fc0000,0xc253030800000000d2cd,0x9011808c000000002349,0x2452c41c05c300910044,0x3050c50012c02410a70,0x5095383007041200,0x600100201200100318,0x71001881420000000141,0x44000001042140005]) else (word80 [0x1c88c,0x2491102e88243d030,0xc1f8000000015050027d,0xc0a889140001505f8151,0x80140000000000000000,0xe4af025fc8700001c157,0x1f40000c9b400030078,0x1420bcc6ac49c,0x1a2984ec13c00028128,0xec00000003,0x813841dd82d204780000,0]))
def g243D7 (j : Nat) : Nat := if 9 ≤ j then 0 else (if j<4 then (if j<2 then (if j<1 then (word80 [0x2fcb8c60,0x905fb754c120bf6e8982,0x41bed9130483edb1a609,0x7d8634c120fd4a49824,0x1fa54930483ed9926090,0x7ea324c120fb26498241,0x7edc5304827ebb260906,0xdf634c120f9a6498241b,0x75c5630837aba2c2106f,0x573584209faeca0841b7,0x58d410837ab0a82106bd,0x7559210d7ce4b2421af5,0xc9648435eb8ac9084ff7,0x558a109fee8b14213fdc,0xd628427ebb4a5086be64,0x94a10d7ac929421bb58a,0x52842fcb84a5084ff765,0x4a109faeca94219f5955,0x28435f322a5086bd6454,0xa10ddac4a94213f5da42,0x8435eb2485085f97090a,0x109feeca14213f5d9428,0x435eb2285084fd768ca1,0xd7cc919421af5923284,0x376b1465085f9708ca10,0x9feec994213f5d932843,0x5f32265086bd644ca10d,0xbac699421bb58932842f,0xdb8265086bd6450610d7,0xcc990c21af5932184376,0xb1643085f970c8610d7c,0xc890c21af5912184376b,0x1243085fb7048610df2c,0x4a8421de54950842fcb9,0x661087d932cc210df6ec,0x904217edd520842fcbaa,0x41086f96548210bf6e89,0x421be591208437cb1a4,0x1087ea5248210fd2a490,0x421fa8c920843f499241,0x84fd73d95109fae5b2a,0x213f5d3634427eb96c68,0x857d7598d109fee8b1a2,0x13fdc9634427ebb4a688,0x5f57194d10bf6e0a9a21,0x3f5da43443cfa1c86885,0xf57190d109faeca1a213,0xf5d843442beba886885e,0xe7210d10bdae421a217e,0x5c0434427eb9ec4884ff,0x7558910cfeeab12219f1,0xd5624427fb9ac4884ff7,0x58910df6e0b12215fdd,0x5624427ebb4a48867f65,0x94910ddac5292217e5c2,0x524427fbb2a4884fd765,0x4910cfacaa9221bb5895,0x24427ebb664885f571cc,0x9109faed192217d5c632,0x442fcb8464884ff764c9,0x109faec992217edc1324,0x427ebb0648857d750c91,0xb7ce8192216f5d03244,0x2fab8864885f9700c910,0xbf2e9282217e5ca50443,0x7cb14a0887795354110d,0xf2c4a8221de54950442b,0xebae80885f571d0110bf,0x2e920221be58e40442fc,0xb9480886f96290110df6,0xc6a0221be58d404437db,0x1280887f25150110fe2a,0x2a0221fc8c540443f898,0xa80885f975cc110fb2a7,0x982217e5cb30443ec996,0x60887f151cc110beae39,0x82213f5d930442fcb906,0x885f571c8110bf2e910,0x221be592204437cb1c40,0x885f97288110fe263102,0x217edd520442fcbaa408,0x86fb6548110df2ca9022,0x17edd120442fcba24088,0x6fb6448110df2c890221,0xbed8d204437cb1a40887,0xea5248110fd2a490221f,0xa8c920443f499240887f,0x37148110fe0e290221fc,0x94520443f8a8a40887f3,0x4148110fe08290221fc8,0xc520443f898a40887f22,0x148110fe242902213f5d,0x920442fbb8a40884ff75,0x588109fee6b10213f5da,0x5204376b14a4084ff765,0x48109faeca90219f5955,0x204376b12a4084fd768c,0x810ddac5190213fdd932,0x427ebb264086dd634c8,0x10ddac499021f24c9304,0x835cb22410847f755891,0xaf2ea182216e5d03044,0x2f4b9060887d1310c110]) else (word80 [0xff4c4a0,0x221fe58940443fd19280,0x887f93250110ff2e2a02,0x21fe98b30443fcb16608,0x87fa52cc110ff2a59822,0x17f5cb304437eb166088,0x7dd32cc110dfac498221,0xf74c930442feba640886,0xfd64c8110bfae790221b,0xf58f20443f699640887f,0x531c8110ff28190221fe,0xcc320443fca1440887f9,0x3288110ff6ea90221fe5,0xd520443fdba240887fa7,0x448110ff2e890221fe1d,0x120443fd32240887f964,0x48110ff4a890221fe551,0x20443fdb9a40887fa734,0x8110ff2e690221fe1cd2,0x443fd31a40887f96348,0x110ff4a690221fe54d20,0x443fda1a40887fa43481,0x10ff28690221fe10d204,0x43fca9240887fb424811,0xff28490221fecc92044,0x3fc99240887fb7148110,0xff2e290221fed0520443,0xfca0a40887fb3148110f,0xf262902217fdd120442f,0xeba240886fd6448110bf,0xee6902217f5cd204437e,0xb1a40886fd6248110fdc,0x6490221fb4c920443fa9,0x8a40887f52148110ff68,0x90221fe50120443fd98,0x240887f93048110dfaea,0xb1021bf5cd620437ebb2,0xa4086fd6254810dfaec9,0x9021bf589320427fbaac,0x5184ff7458a309fee2b1,0x4613f5cb644c27eb8ec8,0x984fd71d89309fae5b0a,0x613f5da414c35ebaac81,0x86be7259030d7ae4b206,0x1bbdd1620c376ba2c418,0x6ef7158830ddae2b1061,0x3fdd1620c27fb8ac4186,0xf67258430deae4b08613,0xfdd563c827fba2c7904f,0xf7158f209feeab0e413f,0xdd161c827fb9ac3904fd,0x76d4720cfacba8e417b5,0xcb51c827ebb4a3906f56,0x194720eeea328e413f5d,0x951c833eb2aa3906f561,0x547209faec28e416f9d0,0x51c82deba0a3905de731,0x4720bbae628e417b5c85,0x1c82fcb80a3904fd7690,0x720deac320e41edd0641,0xc827ebb283906f561507,0x209faec20e41779cc41c,0x82eeb9883905ed721072,0xbf2e020e41b758f30c8,0x2f6b9661906dd634c320,0x9faeca0c413f5d763482,0x7eba6c6904fd71d8d20d,0xbec731a413fdd1634827,0xfb8ac6906df6358d209f,0xcec31a415f9d463482be,0xba8c6905be7418d20b7a,0xe831a41b758c63482fb3,0x88c6905f57118d20dbec,0x7992417e5c332482f6ba,0xc64905ed738c920fd6e0,0x99241fa1c132482fdb82,0x64904fd75d85209fae9b,0xa413f5cf6148377296c,0x2906ed52d8520bbce730,0xa41775ce614837bb0cc2,0x9057f7558520af8eab0a,0x41bd584614827f3b6a29,0x4fd76d4520bdae5a8a4,0x17e5c3514827f3b4a290,0x4fd7694520cfecb28a41,0xddd4651482fcb84a2904,0xfe76545209fcec28a413,0xf5d8514833fb28a2905b,0xe7414520b7ae828a4177,0x9cc51482eeb98a2905ed,0x7214520bf2e028a413f9,0xda414827ebb482907b74,0x190520bf2e120a413f9d,0x9414827f3b082904fd76,0x10520bbce620a41775cc,0x41482f6b9082905f9701,0x520deec310a417e5c22,0x1482fdb8242906df63cc,0x120bdae5982417e9da30,0x482fcbac60905f9748c1,0x20df6c9182417e5ce304,0x83f529460907e9528c12,0xfd46518241fa4ca3048])) else (if j<3 then (word80 [0x837fb244,0x2905fd7388520dfec710,0xa41bf58e21483f699442,0x907f54188520dfeca90a,0x41bf59521482ffb9a429,0x6ff6348520dfac690a4,0x1fb54921483f69924290,0x5ff7048520bfae598241,0x7f5c7304837fb0e60907,0xf9658c120ff2c918241f,0xe58e30483fca9460907f,0x9428c120ff26518241fe,0x58630483fca0c60907f9,0x218c120ff6ca98241fe5,0x9530483fdb2260907f96,0x44c120ff6c698241fe5c,0x930483fca9260907f942,0x4c120ff4e298241fe5c5,0x30483fdb0a60907fa614,0xc120ff2c298241fe1853,0x483fd28a60907f9514c,0x120ff48298241fe50530,0x483fd10a60907f9214c1,0x20bfae498241f74c9304,0x837fb0a60906fd765042,0xdfaeab1421bf5d16284,0x37eb9ac5086fd7158a10,0xbfae929421bf59252843,0x7ebb2a5085ff7454a10d,0xfac8a9421bf58952843f,0xcb82a5085fd7590a10df,0xacb214217f5c6428437e,0xbb285085ff7550a10dfa,0xcaa1421bf58942842ffb,0x8a85087f97050a10bfae,0x319421bf5d9328437eb1,0x265085ff714ca10ff6e0,0x99421bf8c9618437eb12,0x83087bd4250610bfae99,0xc21bf59321842feb9e4,0x3086fd63c8610fda8590,0xc217fdd121842feba243,0x86fd6448610bfee690c,0x21bf58d218437eb12430,0x87ee4248610fda8490c2,0x1fd50521843fd212a108,0x7f94254210ff2ea90421,0xfe5d120843fcb9a41087,0xf95248210ff28490421f,0xe4c920843fcb8a41087f,0x94148210ff242904217f,0x5ca634437fba2c6886fd,0x7458d10dfee4b1a21bf9,0xc9634437eb92c6886fc7,0x258d10bfee8b1a21bf59,0x163442ffb92c6885fd72,0x94d10bfaed21a217f5ca,0x43442febb286885fd755,0xd10dfecaa1a21bf5954,0x3442febb086885fd7210,0xd10dfc87b1221bf50f62,0x4437e21ec4885fd73989,0x10dfac731221bfdd5624,0x437ebaac4886ff735891,0xdfce6b1221bf5cd6244,0x37e39ac4886fe5358910,0xdfc86b1221bf50d62443,0x7e21ac4886ff7058910e,0xfeeab12217fdcd624437,0xf31ac4886fd6358910ff,0x6e0b12217f5ce524437e,0xbb2a4885ff7354910dfa,0xc4a9221fe5c152442feb,0xb664887dd63cc910dfec,0x599221bf58b32442febb,0x464885fd758c910dfecb,0x19221bf59632442feba4,0x64886ff648c910dfac91,0x92217f5ce324437fb1c6,0x4885fd718c910bfae119,0x2217fdd9324437f3b264,0x885fd764c910dfaec992,0x217fdd532442febaa648,0x86ff654c910dfaca9922,0x17fdd132442feba26488,0x6ff644c910dfac899221,0xbfd8d32443ef31a64887,0xdd634c910fbca699221f,0x790d32443eea1a64886f,0xf624c910dfac499221fb,0x90932443f6a1264885ff,0x714c910fece299221fd5,0xc532442ffb8264887fb7,0x4c910ff0e0992217f5d,0x832443fd214a0887f942,0x94110ff46528221fe4ca,0x50443fca1aa0887fa425,0x4110ff284a8221fe8c95,0x443fc992a0885fd72d0,0x110dfac5a0221ef50b40,0x443fd21480887f942901,0x10ff46520221fe4ca404,0x43fcb1a80887f9535011]) else (word80 [0x85100a0a,0x13c827384d4099212f82,0x55849c09221208239846,0x408b2111821d842c0832,0x10381fd83e807aa0f181,0xdb83ac073a0e281bf836,0xc06c20d481a183300642,0xc4818182f405d20b581,0x6182b0053a0a3813d826,0xc04ba092811782200422,0x7f80f581d8039206d80,0xd1818c02e205680a5813,0xc02520468085810001e2,0x38806980c0015a02780,0x45807800ca012801b802,0xc0042005800580006fd7,0x558a30dfae8b1461bf5c,0xd628c37eb8ac5185fd71,0x98930bfee2b1261fedc1,0x624c2feb94c2986fd629,0x8530bfee4b0a61bf9896,0x14c37eb12c2985fd7290,0x530dfae8b1061bf5c562,0xc37ebaac7906fd7458f,0x20dfce2b1e41bf5c563c,0x837eb82c7906fd755872,0xdfce8b0e41bf5d161c8,0x37f39ac3906fd7358720,0xdfae0b0e417f5d351c83,0x7eb26a3905fd7494720d,0xfac928e417f5ce51c837,0xeb1ca3906fd6454720df,0xac6a8e417f5d051c837e,0xb20a3905fd7490720dfa,0xc920e417f5ce41c837eb,0x1c83906fd7650720bfee,0x6a0e41bf58d41c837eb0,0xa83905ff7050720bfae3,0x98641bf58730c837eb0a,0x61906fd7650620bfee4a,0xc41fe5c1418837ebaec,0x6906fd74d8d20dfce3b1,0xa41bf5c763482febaec6,0x905fd74d8d20bfae3b1a,0x417f5c6634837fba2c69,0x6fd7458d20dfee2b1a4,0x1bf9c5634837eb8ac690,0x6fc7158d20bfeeab1a41,0xbfd95634837eb2ac6905,0xff7458d20dfec6b1a417,0xfdc563483fdb82c6905f,0xd7118d20bfae399241fb,0x59632483f6b1c64907ec,0x764c920fdee899241fb5,0xd132483f7b8264907ed7,0x4c920bfee8992417fdc,0x1324837ebaec2906fe74,0xd8520dfae9b0a41bf9cf,0x614837eb9ec2906fd52d,0x8520dfe65b0a41bf4cb6,0x1482febaec2906fd65d8,0x520bfae9b0a417f5cf61,0x4837f31ec2906fd63d85,0x20fdaa5b0a41fb4cb614,0x82feba4c2906ff649852,0xbfae730a41bfd8e6148,0x37eb1cc2907ee3298520,0xfda6530a417fdd561483,0xbfbaac29077c7558520d,0xfecab0a41bf59561482f,0xfba2c2906ff6458520df,0xcc8b0a41bf59161482ff,0xb9ac2906ff6358520dfc,0xc6b0a41bf58d614837e3,0x1ac2907ee5258520fdaa,0x4b0a41fb8c961483f699,0x2c2907fb7058520bfae8,0x30a41bf59061482feb98,0xc2906fd6318520fda643,0xa417f5db51482feba6a,0x2906ff64d4520bfae5a8,0xa417f5da51483bfb2ca2,0x905fd7494520dfec928a,0x417f5ce514837fb1ca29,0x5fd7294520fdc6528a4,0x1fd58651482febb2a290,0x6ff6454520dfec6a8a41,0xfb8c951483fab0aa2905,0xfd7614520efeca28a417,0xf5d0514837fb20a2905f,0xd7214520bfaed20a417f,0x5d2414837fb2482905fd,0x7390520dfec720a41bf5,0x8e41482feb9482907ee3,0x290520fda6520a417fdd,0x9414837f3b282905fd76,0x50520dfaeca0a417fdcd,0x414837fb1a82906fd635,0x520bfee4a0a41fb8c94,0x1483f699282906ff6150,0x520bfee0a0a41fe9c141,0x483fcb8282905fd76105,0x20bfae420a417f5d2214]))) else (if j<6 then (if j<5 then (word80 [0xa93e9275,0xa4e449a2932925da4a84,0x93a9259243a47848d291,0x79227a448487290a920f,0xa40c48028fd91f7a3e84,0x7ba8f291dfa3b4474a8e,0x691c5a38046ea8d891ad,0xa350467a8cc9195a3204,0x6328c39181a2fc45da8b,0x89169a2c8457a8ac9153,0xa294451289e9137a2604,0x4a28909119a224442a88,0x190fda1f043ca87590e5,0xa1bc435a86890c9a1844,0x2f285b90b1a15c42a285,0x1909ba12842428449083,0xa0f841d28379067a0c44,0x17282a904fa098411a81,0xf903ba06840b2812901d,0xa030404a8069007a0043,0xfe27fa8fed9fc83f7a7e,0xd8fd39f983f1a7e08fbb,0x9f6c3eba7d48fa39f343,0xe527c78f879f043df27b,0xa8f719ed43d927af8f59,0x9ea83d2a7a28f399e683,0xcb27938f1f9e303c5278,0x68f099e083bfa77c8ef3,0x9dd83b9a76f8ed79da43,0xb327638ebf9d703ab275,0x28e9d9d303a4a7488e8b,0x9d0839f273a8e6f9cd03,0x98a72d8e579ca0392a72,0x18e3f9c7038ca7178e29,0x9c48387270c8e139c1c3,0x8126fe8df59bdc379a6f,0x8ddb9bac374a6e58dc5,0x9b7c36da6d78da59b403,0x6626c98d8b9b0435f26b,0xa8d6b9ac0356a6a98d4b,0x9a8834fa69c8d339a583,0x49268e8d159a1c341267,0xe8cf599e033aa6728cdf,0x99b433526668cc5997c3,0x2e26598cad9950327a64,0xa8c8f990c320263d8c73,0x98d8318a62d8c5398943,0x10a61c8c2f984c307a60,0xa8c0d980c30025fc8bef,0x97d42f925f08bd997a42,0xf325e28bbb97682eb25d,0x38b9f972c2e425c48b81,0x96f82dda5b88b6796c42,0xd725ab8b5196942d1259,0xe8b3396542c8258c8b11,0x96142c0a57c8af195d02,0xb7a56b8acd958c2afa55,0xb8aaf95502a8254b8a8d,0x950829ea5388a6794bc2,0x95a5278a45948028da51,0x48a219434284a50489ff,0x93ec27b24f289db93a42,0x72a4e189b5935c269a4c,0xe8995931c261a4bf8977,0x92dc259a4ae895392902,0x50249c892b9248246a48,0x98909920023da47788e7,0x91bc235a46788c591742,0x2ca453889d9128222243,0xd887590e021a242f8859,0x90a8212a422883b90642,0xaa41188199020203240,0x187fb8fe41fa23ef87d9,0x8fa01f1a3de87b38f541,0xe823cb878d8f0c1df23b,0xa876d8ecc1d723aa874d,0x8e8c1d0239c87318e541,0xc8238c87118e141c1237,0xe86f58dd81b9236d86d1,0x8d941b0a35f86b98d641,0xaaa35186998d201a1233,0xe86718cd4198a32d8653,0x8c98191231e86358c5c1,0x89230d86118c1017fa2f,0xa85eb8bc417622e885c9,0x8b8016da2d785a58b381,0x6522c585818af415c22b,0x3855d8aa815322a1853b,0x8a6414a228f85178a1c1,0x41a27f84f789dc139a26,0xe84d789a0132225f84b7,0x896012aa251849b89241,0x232242847d88ec11ba23,0x2845d88ac1132222843b,0x886410a2210841988201,0x1a1fc83ef87cc0f721e,0x983c987840ee21d783a5,0x87380e4a1c4838186f00,0xdd21b6836186b00d4a1a,0x6833f86740cc2193831d,0x862c0c42185830185f40,0xbb217082d785a00b2a16,0x82b7855c0a9214d8291]) else (word80 [0x1288605,0x438118a2141060885030,0x11814101004506048410,0x11814128860543a2811,0x8141008605031018140c,0x5004603a2160a1412885,0x854309a316a210405822,0x310160e885854309a3a2,0x161044405832311160c6,0x5821718160c60205031,0x818141044402231016,0xc40605831610180c045,0x4030cc1101410504060,0x31610180c5c584060418,0x10140c48406050418040,0x2161188100c584021416,0xc100858312188614105,0x41408504080706050402,0x18200858504c20816141,0x5308b85840802181413,0x820906040814180c541,0x40850402082418130820,0x90604c12422181048209,0x604c208241810100858,0x3a2040316105810f0e16,0xc441410401850403161,0x11018442a28608444088,0x100c58646a2084440885,0x841023221610100c585c,0x40403160c08582221608,0x2008605040818140c444,0x100c1488624a3001122,0x144004508840504120c1,0x410223c5011410206088,0x504c1182214130490886,0x4c11822141020608850,0x40118221410505821009,0x23161040582191418161,0x4458217160a1b086450,0x40a16140c58502151614,0xe908c5831004160c505,0x82064515141024582091,0x5160c268c64584141608,0x1b145450480862e15120,0x21854b848006150e0018,0x54315160820505830802,0x16141058542112422161,0x585020216140c085850,0x30923101610205850310,0x23160c5c8c58310a2160,0xc0858264238006104c8c,0x4244640010161028241,0x80841023160c2018081c,0x41022160c5c885830610,0x1422108c880848185066,0x406100d90405831064a3,0x161041928c5841000061,0x41040505831064231610,0x4190201846400a322161,0x40401928c18886111004,0x3161490405831819100,0xc6204504041819100c88,0x64603191808406460302,0x19180c40646031841141,0x106089045041841140c,0x41046050402184114104,0x6104504030042021814,0x18604058504a28608545,0x821615085854216150ad,0xa45b2ab6196bbad6c5ac,0x2b5696a7ad445a6ab4a9,0x68fad145a0ab3e9675ac,0xe059aab31965bacac594,0xab269647ac8458eab1a9,0x62dac50588ab0e9615ac,0x20582ab0295fdabf057c,0xaaf695e5abc0576aaea9,0x5cfab945712ade95b7ab,0x6456b2ad2959fab30564,0xaac59583aaf855caab69,0x567aac85582aae9555aa,0xa45532aa39543aa7c54e,0x2a989529aa445472a8b9,0x50faa105402a7d94f3a9,0xd8539aa6f94d9a9a8533,0xaa6594c5a98052eaa599,0x4aba94c527aa4b9493a9,0x205222a40947ba8f051c,0x2a359465a8c0516aa2a9,0x44fa8985102a1e9435a8,0x6050aaa12941da82c504,0x2a059403a7f84fe29f99,0x3eda7cc4f829ec93d1a7,0x9c4f129df93b9a7684eb,0x29d393a1a7344e529c69,0x385a6f84de29b8936da6,0xd04d8a9af9359a6a44d3,0x29a1933ba6644caa9929,0x31da62c4c3a9849301a5,0xfc4bea97c92f7a5e04ba,0x297092d9a5ac4b3a9659,0x2c3a57c4ada95992a9a5,0x484a7294b9291a5144a0])) else (if j<7 then (word80 [0x160c8c18,0x5032306140c241828123,0xa04b8281412e0e04188,0xc31280060d16040c3038,0x60c4516000c4072306,0xc4c24183020a0848182,0x208090c182080608901,0x824123810c244c183120,0x6230c584021716090440,0x28216084c26090440682,0x226410885820a0922061,0x1905828106088c004032,0x382410c4a081d0442310,0x160c8c58883072208061,0x888c5832281062e1018,0x8e0590422810623101a0,0x450323228116105c8858,0x30664220c4c182810623,0xc48188c884024108405,0x82060590281832322160,0xc201820280060c4c8e00,0x440a80020d0c4018312,0x108200a003111045061,0x1a0024306800c402018,0x3028008885820906088a,0x48d0440607084030210,0x708403020540100c401,0xc20340100c1060405840,0x50114101010085840401,0x18140c08546030118140,0xc0460503080216141188,0x305436580621511958a0,0x5446510150c41960054,0x41016150c40585430510,0x150c58544031615620d8,0x85854304011812101404,0x504840504001210100c5,0x84440503001110141000,0x4440416171810605c583,0x1642180c100c44584111,0x60b10870860417114204,0x316185d085831142160,0xc1044603212514c21028,0x87086042125c21413108,0x708604c411180f108708,0x60403021116101058443,0xc216140c4c44140c0108,0x60411420c44585032423,0x16c21308585031116140,0xf08585031410180c5108,0x60312144218100858503,0x10040118104014045041,0x10405100614504060305,0x1140c48401c1410046a,0x410070c0460405041614,0x100c2050406040824101,0x8102050406041264180f,0x8505830814101810604,0x5031410180c5c400860,0x41210021814140900483,0x12021410181443150048,0x410040316104c140c244,0x5121007050401184058,0x210160b08585030a08c2,0x161040582c216083f085,0x86041116081060405841,0x7041816105c586030216,0x180c100c405841104031,0x612181c4c22118130c08,0x58304031610101084406,0x4110421181062182c22,0x12514102b0884604c221,0x25141313088460411c42,0x11813100884604040310,0x161044100c584c216140,0xe930c085840503100f08,0x585031116140f08908c5,0x84c216140c4458503021,0x6140c58402c310160c41,0x4431410180c4048506,0x40c12100c5840603061,0x140c405021410180c58,0x40603171016181060405,0x31210181410260c4058,0x41410180c50406031404,0x1c4020010180c4108603,0x1742180c000850604101,0x4421810600c005108510,0x14180c48400460505181,0x140d08605038216140c,0x5a085038216140c59085,0x31642140c5908503621,0x6140d950451884656241,0x14102988585040418101,0x61014045040401181410,0x101060405841844a2161,0x2462885841822160c60,0x58403041817161040106,0x5840218160e88611058,0x409a2181610406058305,0x1141012960688504011,0x4100c14044c504100501,0x1412940a045040118141]) else (if j<8 then (word80 [0x30104486,0x20e1008601121408481,0xc21223210c48401c3082,0x1100c182021817084840,0x1c34012100c480850340,0xb0808490031012400c4,0x85021083400c14402161,0x81040210040c402101,0x60a004020880100c5c40,0x5830d80084c904031223,0x100e0010804085840302,0x80100c28902140418208,0xc32310088c0421023090,0x8c21116089618216043,0x49509004051604448490,0x30a4008583c224210844,0x188c30818100c8438221,0x180908385831110160c5,0x81181108601821110060,0xc904020882800c048c40,0x382048c0a01004170c08,0x403c210050894005c311,0x1608168420a85100c400,0x421006080c4060043852,0x10011106011110160c58,0x1100d084034280041840,0x21106250c16842100506,0xa1004504030521c0111,0x44941830a1008904004,0x31006080c40500431401,0x8840044314045010000,0xa25230c41150c30a4310,0xc408c2830a042908003,0x80048e01003100408290,0x830a05082428184110,0x60887004430a09090040,0x20608070c8d004030701,0x9008e00310044095003,0x44160444841c30823401,0x101c0421605008e0031,0x81400e004108310080a,0x8010830c04408c24310,0x12070c5d082131023801,0xd0820c060800111044,0x602170c822310504021,0x3140800408c31007085d,0x860313140a0d0820806,0x420710401822308441a0,0x86040782086010782085,0x10782081c0821104484,0x1c342800a001d083090,0x60840302100908401c21,0x1100c06104c0020ca209,0xc403021744000c5c302,0x430540100c5c40303841,0x7000c24083038400110c,0x24402130008304c20440,0x100c4c0021310140c540,0x4431007080d00403150,0x120c8d0020206084028,0x20a044c00209a2085400,0x4830240070c4c1440011,0xd100028111090c56080,0x3071108450088344020,0x9100428222440c243020,0xc04403021009070c1c18,0x17100c4c42003122322,0xc3044183000a0809042,0x12220820502151408200,0x81c18402045850083080,0x2161410205021404201c,0x8831223060c201c21206,0x8545024506082c94183,0x160b08201c2080712061,0xc1820b06080c885831,0x223088c0821110160c58,0x11003410c58382160309,0x438216030a1411040c4,0x850b0a141088580c5101,0x608968a1831023085888,0x3831623220c581851206,0xc581170608885821716,0x8201c20706080c180c2,0x4506030c449440317060,0x81a882021608504c1830,0x214060c900e060008512,0x23060d04081830011080,0x440200190421225240c1,0x9151034512060e0c1820,0x625120c584821214060c,0x1811206140e044824106,0x20c1810807060c488c2,0x23045450206030914180,0xc3150454502120008482,0x1001841408120c490004,0x34100230d04188c30807,0x8241824109081812341,0xe045020c06190c320,0x5043810c060c8e050430,0x41306088810583040608,0x92041831381240612041,0x822381060c1c90201841,0x9142e4e1514901821124]) else (word80 [0x100c0,0x8410c2431210070c4030,0x18321110808842070444,0x88222010820188830221,0x8888421107080c40243,0x100609005c4831312090,0x4821412110c48401c31,0x71108441131108584421,0x211084440583020f0804,0x4c143020a08044c20208,0x86004483130d0834482,0xac20850044c3020a080,0x44c20208084850043131,0x10808282120a08104420,0x20a08082020300110c1c,0x442090608280020a0906,0xc144020423100c8c402,0x118100c5c4060313091,0xc44941840421080848,0x50214040410104605004])))))
def g243H7 (j : Nat) : Nat := if 8 ≤ j then 0 else (if j<4 then (if j<2 then (if j<1 then (word80 [0xdb000000,0x1450000,0x2804b0000000000000,0x100a3,0x40000000004241c00000,0x81b680c0fe233400000c,0x228e10c9000000000241,0x7250205c1831c4439496,0x17824f0000040c814089,0x80000d05d00000000005,0x805810144000034917ca,0xe6e243de04d80000602,0xfc00000c4555c6068000,0xae232553671346,0x3011d60738448bb81919,0x61a3463700000303bf30,0x24328cc54138f2058f07,0x44c076401f3d8065f319,0x200003808f7214ae0638,0xc493c000060448807a80,0x780793047400,0x1810,0x6ad83e00000603c60000,0x18061000006119800003,0x41e4412b000000000000,0x500afa40d48113400,0x50313161d24101fc01,0x830331a13f6c0c54004c,0x8a160000000000000005,0x918d2469800000d07600,0x9038000003e0051a3,0xd00001a02fd813ad014,0x4808388232c000000000,0xf1278000000000202302,0x1e600c8bcc8d2836950,0x70600b4b1482a841e003,0x6a64164003e0ca3eb153,0xc203c6090b58802a0746,0x640f8421700000b280ce,0x6699806680000905b9c8,0x6e40000708e5112ce40a,0xca02280000000000e06e,0x1c02e800000000000000,0x203d30000000e794,0x19c918b6c22db40b28c8,0xa4f8068d41e94415a118,0x3bba6e1209e000000000,0x16072c00000,0,0x21c855a0,0x33f086600001c1d5990c,0xa8079500598000000000,0x6e5ec5800000000000,0,0x300ea80000001,0xaac07d80000688c1a07c,0xc00000000000000b91d6,0x80444000000000943d8a,0xf89103b30437d019200,0x3c470f815414064000,0x582559053c0000,0x1118e201c0c083121000,0x406003811410a8902242,0x7004818010082812218,0x58102551203e00102082,0x41040a2c092061c20600,0x300130c480000a2423d4,0x620181040c200000ce03,0x461c1890430110021420,0xb060c0820a1600000080,0xc32140051c242000c1c,0xa831a00006002810f002,0x81030008083045030000,0x4106220800102a45130,0xa2010016080010a10086,0xc006180e00004000c20,0x30a00483244c0031c040,0x1416053810e205020008,0x11506140030408207028,0xb04180050c205810a,0x42a0000800042033,0xc1a10214380184400c,0x4000810000187021801,0x33c00302020c002013c1,0x1104002830e084800400,0x3080408086002c600180,0x800c2614789040400312,0x30e080020604007800,0x60c50404006810e2c204,0x2001060000f22022008,0x400388040808202002,0xb0a148810c000000004,0x8002080000400281160,0x17030030800183008414,0xc010000c00004102020,0x40c0030600001041c501,0xe00580041c400020018,0x30c005020a0418b02280,0x840a0400106000000014,0x8202000030418184040,0x50404480001800008,0x81820e1410a04085811,0xa1800006101800414901]) else (word80 [0x1df02e52,0x883e0837700000000000,0x710580000000000d0,0xa08000040320c06ec093,0x700000000000000248cc,0x800004211e929dec1a68,0x8056021bb60474000000,0x3829600000c45f888,0xa5c062c0000000002001,0x70000000000000070380,0x707b80000081b8900488,0x45940782814e0032ba0,0x41c80878c80700000605,0x4a087c40000000000000,0x1c05d400000000093351,0x44216c0e38000000000f,0x5540000283e000001cc,0xae0000000000607ace00,0x20eb,0xe8203791e80000000003,0xc1bf323f200001608838,0x8c47824526474e45b800,0xa0261806b8000,0x1033b705ec8438c0000,0xe436e0000000004,0x6b0000000002cc4a00,0x806f4816ab02,0xab000000000102138000,0x3933fc241e00b100000,0x208000000000004029de,0xeacc94b4042a81b3e0,0x67ce0b5800005a365000,0x41a5000000000,0x16107c0000399632005c,0x1418c3abaed043a0,0x4832a804d960,0x29dc1f700000b0697a42,0x4c0000000003227e201e,0xd50387122c705a1a0e7d,0x1d000007028d20b6c0,0x58167e073560684e0,0xec80000a013e228d8000,0x52303103bb20a9b491c,0x8000090385c638800000,0xa804ea0858000058,0x394d00180000288ca800,0x9027ec0ac594965831,0xa0000000002051ba8213,0x803f1802370112000008,0x2ed284d0c091f124691,0x128600a4000011aaa401,0x3a865a85466d8024a82a,0xe4417940e9c8317d00c1,0x485c80000202e7e02e00,0x121,0x1380000308d900000a25,0x8cc02380000486ef6062,0x40036881abd03f800002,0xc07d3838a932d1020bc0,0x2dd2050148115c1,0xccf92670000000000000,0xe055f09a2,0x80000203d200000c0cf0,0x3805d80,0x1241718c44000,0,0x2818000000,0,0x1255d4,0x27d804eb191b00000000,0x24983000000000,0x200678000000000,0x388e2d12ead,0x2764000030343c5025c0,0xaf30888e83fc44362806,0xf280ea0005c343830050,0xa420610292901e112684,0x404a80000a40a4000029,0xccc8000092427203d800,0x822790090c000,0x30392502038014cc885,0x58b9620387c28ea90d82,0x9198f101a682c8008120,0x29530495202819000b2a,0xef00001303a5000e8000,0xa22c1c104bc86780000,0x52690086fb41286019d0,0xe817ac0232020700,0x103d8708,0x36a03200000080c6b041,0xe00003c4b55206624381,0x82610403a60909d05980,0x180,0xac000002804254272000,0x60045000004043,0xc163402b64065a00001,0xc4b2b49ef803e7424540,0x10438233e024ea01db00,0x8541969a004dc0716003,0x88000070544000000000,0x879ec0a9c,0x8164706e080f00440290,0x122e04dca09300000603])) else (if j<3 then (word80 [0x10fc0000,0x3c270224c83d800000,0xe001d009d841f400,0x422f9e0aed013fc8b,0x1d00001a449cc1dc9810,0xd611ab682e201e882054,0x906f80000000005823be,0x68a0000000000000000,0x40a600000c11,0x8600003459d8932d5057,0x220bd41012a03232801a,0xd06a78266000014,0x8edb4cd4b03bd0000000,0x1c088602f300001e03,0x87492380000022c5a436,0x1610f2,0x492149ca60138000015,0x18f00000154180000042,0x980000610240000110f,0xad11a9000017063cc210,0x9a1bf000000000380a01,0x9073b43c3400f4000078,0x289b017c000018225000,0x803ff266a800007c15,0x4f0096c4749807c90360,0xe014b425f6c48e80000e,0x70c00000000000000b0,0x811a41e88156b01b7000,0x14096c000000000f048,0x368b4f88a58000000001,0x62e97004a0000000000c,0x494c000038283c08a820,0x9714220ea013f5690602,0x81af38922d03820201,0xcd036d807fa210400000,0x1c0ecc0,0x1227b00000a490640,0x83600867410000003483,0xf00000d077de46000000,0x18401108856103e014cf,0x9088411bf66cdac0c220,0x2bf20667a4b4948b3489,0x76d044e00d1381a3991f,0x9f0852202e681bd1007d,0xa0604000000302a,0x60ef8001f00c18000000,0x20fb4000000000000,0x1c0f3c0000402c10000,0x1a81bac19e8000000001,0xe64670134a0206000010,0x244000000000000001aa,0xc9400000000000000c42,0,0x686121b3817400002,0x9213820c00000a0c424,0x1d3a8115000000000109,0xab80000e435e80067d09,0xd082aa00000c034b0039,0x80000000000000000000,0x3c041d8,0x6f00000000000000000,0x50009e00a000000000,0xe04e908240c14a00000,0xf20a200001c216380e72,0x212520ff80000183c180,0x55e404ac180c81edc00,0x14000020106800000000,0x120af4010d190895076d,0xe2eec111000000740e94,0x21c541c8e813100000e0,0xcd8c84580000a0444000,0x38396f15154022,0x18412480ec701ee00000,0x80b8f02c3e01dae25fd1,0x6e80000000000000191,0xb00823c000002221c000,0xe01d5406880000,0x80e6301d02,0x3038424ad323a9801080,0xc41e7049c4814d800,0xaa34ee4e40000,0xb07c200001c1456c9da,0x5046a00000c90a402090,0x205c18000070,0x55c22f09a45d73004000,0x88e7a80cc3915,0xba8c2241f21014bf0840,0x39924849a3924350,0xf64c1bab81ac512be46,0x10c0000181a000000443,0x5a04e680000000000000,0x1c84c0000040881c0368,0x4060800006209cb270c0,0x403cb1334fa0fcd00,0x5e48b280000000000000,0x7013b00000000000053,0xe12d6425ee42141,0x307f146564465e80dd18,0x2a1002f9608d2901c000,0xd1010220469189803e,0x3432294041601a8b900d,0x606286028d982929b1a0,0xd23a441eaa839d90]) else (word80 [0x9487009,0x1960d20000000006a80d,0x1803f58231f,0x86a08fe000000000000,0x100360000060201000,0x10096400005a14eb40d,0x7c6b3c011c8000076484,0,0x689ab0000108,0x4f4c055d805100001c22,0x3c000000000000000000,0x308c200001e09e1,0xc13000385e00ccd23b00,0x3831f000004250000,0x1ba670000000000000,0x8349a462a0000100bb,0x882531124a0000000005,0x809e0000000003002900,0x5209000001c0aac90,0x7100000860f800000000,0x117058076b017480000,3,0x20a400003c2262804300,0x100632c93ca207c000,0x1421428090002ac8245,0x5a01b3800d8189ba025a,0x108c5d0985f04f3e,0xe9a0417600000a03ee00,0x34883a900734686000,0x380820000000001a04d,0x6807fe83b20062200000,0x2c,0x6700000e17780000251,0x3e8000000000000030cb,0x2800000000080e380000,0xc009c00fa800006,0x91c300001a08bc000058,0xaa0f01d1642340000000,0xc06b80000000000000,0x320fa00000000000000,0xb,0x7200000000007235800,0x120668000000000000,0x130cdd8000e8921904c,0xf8440d48b6580ad00000,0x6e65c00007a907d08480,0xa33a4142610e40000000,0x5016a0000080f,0x7c000069344805cd601c,0x8000031142f164d00d7c,0x1d500000706ae600b14,0xfcb840200001c4f5200,0x7970195307180000100e,0x8d81f4307260066cc10d,0x9029fb02b3c0d5381011,0x9038c043200000000000,0x229c0813806a90058000,0x902c3f22ac000018b8,0xf4003164448000000000,0x811b080a6a00d2000001,0x3d64114800003191bd0,0x42a00000000070b4ab01,0xfb281d4000000416e088,0xe424ac81310000000001,0x113c0000301e8000000,0x4014d402f468,0x976c0878911370006410,0x2800f08000000001c031,0x400002813e0000000002,0xd6f988e4b02c784b3c4,0x81d03b5a004b40351c8,0x26403f10000000acc000,0x1083c7e4c8,0x1405b000000,0x982a660f1ac0fee9,0x143c016ecc81c0000284,0x4300001c075ee4ff682d,0xe000010057f808b1027b,0xd008820eec000068a2e8,0x50ae465b58a600000d3,0x3120000340a50022d120,0xea00001001c80000a60f,0x7e092400000000000000,0x84230c05a700aa123b00,0x2929ee0,0xeb9006980000605de000,0x3012f11840703019276,0xfd909f91a5760e2a0497,0xc82a7917d566e0000000,0x302ea00001e0b1000,0x6000000105460000108f,0x19000d00001000f9d83a,0x80000000000000185ab3,0xa13800000080c4000000,0x200a4800,0x102db0065c404d3839,0x70000000000000000000,4,0x2357a02e80000580dd71,0x16d64176417dd8128000,0xe26000000000000000,0x140d994135c906000000,0x3482b80000000016]))) else (if j<6 then (if j<5 then (word80 [0x62a17401,0xb7505480000523e0326b,0x908f9184f650373905e4,0x3c4bbba0d1042ba0,0x8fd41e60004cb002200,0x69e809700000f212e24d,0x6f086e00000000000000,0x1fe94a3c0000040229,0x4cd2f833a705ca005964,0xee79187202dd2050400,0x10d92088aa000948c,0xf000000000000000c91e,0xc02e300000487a000000,0xb91da0c1aa08b271,0xa624b0000000000000,0xa207e805800000611a,0x800000eeaa8000000000,0x54166e20f750f78842fc,0x7de0000181628844900,0xd02600000a62,0x5c4064c000000000120f,0x280a32c08c0000000000,0,0x2916c8019fd60be00,0x41930000000001e42,0x6d4c8e00000401860000,0x1c4247022aa0485a4304,0x280328030fe05f84,0x1e9401457033980fd201,0xe380000c146440968000,0x160,0x4078a6223800005,0x8240f40d928798000030,0x8be2576c05680000000,0xd40d20000140ef8000,0x1c08a00000,0x122fdcc1e340b5800000,0x341d30000040,0x12000014913b1238f07,0x4b60fe781b150962e03b,0x140cc582d300001,0xa8c5c48980805a601640,0x1c05b5097a0006200,0xc0f95204743314000,0x2020c00000e007e0000,0x150da521b29628460fad,0x84430000000001209940,0,0x300f8e05b088204000,0x5812c00001208968910,0xd39c2621ae00001118e9,0xa0c7d116800000000038,0x3c3e00b3210d80102000,0x50447e804000000000,0x4088802ca8d1f348378,0x8479600000000000000c,0x1f68c1ae40d80000090,0x7aee002c0000303dd000,0xc9400007033f2210,0x6000000186d81bfe25a6,0x88c0,0x582100000000,0x4240e000,0x200ba7838b793b82103,0x8c06e092851174c00003,0x50780000000000000018,0x80280000f05910049000,0x7a04d460da00000518,0x880000000012235b8445,0x604aac4bc0,0xa07fea0d04014888,0xe53050400000cc28080,0xc7000000000000000000,0xda00ab0811a,0xa332c000000000512590,0xc0b380000382f972,0x68fc0208d1fac01fed04,0x644056c4149800000000,0x40695811ee03823125b,0xc4501c011683b1b21c16,0x42474cc3e10f39047008,0xc6e11c3182572003d403,0xfa64ae400bd6181312fa,0x2916ec04221002940f78,0x4011c800595544405fcc,0x8a25024da06cfd275000,0x68151000002026e401,0x7b03460000000003103b,0xa0148000000000000000,0xe009a24520008018,0x3b4d255de09840000000,0xd430cc854400000000,0x10493340d900000,0xd03cec0dbf41ae9806e0,0x6cd606132805700,0x1c074040b980308000,0x20093281be0000,0x1a2a918c3f00000e0399,0xe80ef402f083bc711c62,0xe42c8084381c49039fc0,0x45f413980000b2128000,0x19039c8134e0496a038,0xb0184e81efe084aa0e85]) else (word80 [0x10000000,0x14099d82da710fa607,0x23206958827716d320d6,0xc841f00000900c78004a,0xc06c98364d04f8000000,0x204f54a66b01,0xdc20033305532c518000,0x1202b508674049,0xc092945210a077988880,0x210530229e9,0x7200607002b285af202,0xe0a1254208858161200d,0x1600a9ea66e4d612a332,0xc5127cc1bac48dd8374a,0x57168543d591f002760,0x45100019d0a48012fa20,0x96c037a808e0838fc429,0xac8802411b7032470684,0xf3420680061006908,0x5a4000000000f06b000,0xc225b841100000623,0x7884bcf0084000000000,0x2c991a083a00000,0x508e0b24b4000000,0x1009a000,0x200eb504c7e0260000,0x323f02119a000000000,0x34b7f000000000014830,0x1207a8421300,0x89aa803,0x5210407287b800000000,0x1e0ed00000,0x381c43826a0,0x290a28000000,0x86200d8883da911,0x1a00000a108b00b50000,0x983c800004233b,0xe0fc80000080d7e915dc,0x794581600000d0669e0,0x6490117208850036c000,0x851c244c407e,0xc000010b1a7063df22ec,0x38335000006025c0,0,0xb026e00000000,0x31081c4634c068d05c9,0x48b95912c04091ae13af,0x83f7f43e600000012f80,0xe86f200002d190482,0xfd403286096000002191,0x800000c22e0000000000,0x2042400003d1efa83555,0x416000000000208f300,0x30431307,0xa0ce74f8886800000000,0xa0ee8986a0000000001,0xdba0009da903e061e0,0x6813200001e2,0x6b8000078332800f4606,0x3a88a500000006fb00fc,0x181d6d092340750c0bb9,0x88e280000a12f8000000,0x62920000380,0xa1983fb10857c013c000,0x2039300b7c80e5,0x492b25052e0000240d48,0x717e4000010914a0,0xc1c000000000380c7903,0x3c10148606d000004823,0x7601c050248000000000,0xd271c0000203e98,0x8748463800000120a90,0x11940ca0000000000000,0xa86ce8137800000000,0x28264200e0,0xe0adf8ccc00000203c80,0x220840000000,0,0x81bfd9967446c60000,0x3ca05383790000000000,0x182f4a75912fc40d644,0x1894843e602a000d68c1,0xa06032c0000000000000,0x1ec1e98183,0x201be0000000000,0xa0022e539f8,0x13d00000000000000000,0x809ca01e68000,0x2035e00000000060405,0xc1ab00000f,0x79c000035077803ac00,0x1e04e00000402ba643,0xcbe07d40000721ba0000,0xe6305c915a006900000,0x2408580000000010,0x5480000000000000000,0x9037e0081505c3245,0x4c000000000000000000,0x5011b1255bf29da,0xe4c9401853326100f240,0,0xe061850cea884,0x31a1852039a000000000])) else (if j<7 then (word80 [0x2c000000,0x703f500000c0a9c00,0x2233720a3c407,0xaa8254a06d1e01e1105f,0x38050f011e0000000000,0xa41e440c7760ab00,0xc1056c138000,0x10350e0bac0000090e,0x2d03c400000000040296,0x2458d800000,0x10,0x8462091f817f00000000,0x140a7800000000,0x82114,0x68353000008,0x2227c07e000000000000,0x88b00000000,0x3d025000000000120e5,0x488b0800000000046478,0x4043000000000038,0x190890b6708680000104,0x96000000000022370000,0x180d60000108c30c516,0x802776245a60ea400000,0x502baa25c041bdf0,0x16800001c67cc0000000,0x975c4281a00000280e,0x600001ee430000062024,0x307ece089b400e00000d,0x32c2c82a8000040172f9,0x345065ac00006c993224,0xbc000008198000000000,0xd4ce700b100000,0x300a1000010,0x6b40000040e7b227200,0x4482790f96842040d,0x40000000000a219a0000,0x3d0ada018a703b600003,0x416888041605dbe02a40,0x2a0700d56233f85,0x511307dd47c22236b40a,0xf000000000000003c127,0x901dc00000415a0,0xf40f0c493b018508,0x2f7c043e00000448b601,0xd2c03e2127fdc15f0000,0x118220000000001823e,0x3c957800003,0x239c0000000001018600,0xe0c38000000000305,0x5000a040000401780000,0xc0650000000000,0x20c1dc21c70381d256de,0xc1a288d620090b321360,0x851c0bc80000e01c6000,0x45bdc324406d50105,0xf4cc720158f4178809f4,0x50bbf4021c00002c,0x1dbb00f4304a4000004c,0xc60807700000607c2982,0xb680cb0000020c9f9024,0x8804ab05fe086e35ce90,0xa001e00000858f00,0,0x3021cf02a,0xf50069a67eb48310091f,0xe085a881100000000000,0xc0ec000000000042,0xf746c88504144099410,0xc3e496c0000000000000,0x1e460945188036bb06c6,0xa24dc00000838400000c,0x800000382e20000000,0xd40ce000,0x2992a8000040739c082,0x8000000000b00c862483,0x40cb780e90000000003c,0x84800000000000000000,0x48365602fb06aefc20,0x21112f59400c0bc3021e,0xe8107e015d4632800001,0x4030000060698000000,0x88c7f0165800,0xa8207f5a604502081001,0x6a93aa2007e010880000,0x242ec6053a813f7a0e95,0x73600001c9293828649,0x37800000000000000000,0xa40190094a034f805b,0x36659800000000012492,0xc0cdf808f80000106ec0,0x6003be063660,0x4e591f3e0319b00cfc61,0x880000000004059aa64b,0xf4115a02d430490b00a5,0x40ccc016fb03732c1b00,0x3899d000000000000,0x410be0000000003019,0x7000001002a000030194,0xa23e2500700000000004,0x2cf0000000000000000,0x9078846737e4d2521,0x2e000018417dc1f2b12d]) else (word80 [0x241a7000005819b5239,0x80000483380000000002,0x48ac80000c0112000030,0x168000000000005ec00,0x3f80000080798884,0xd00000f11ae000000000,0x749a091336c10a800000,0xa00434059f0,0x432722280c0ac4cc4320,0xa9310b400000014c0025,0x61436a00001014800000,0x4308264184000000000f,0x5ae0000040f70000000,0x14ce700000b06,0xc2000000000000000000,0x6457c000031995f2449,0x210651969800004038d0,0x9b400c58000000000c0,0xdc000058109c0712000,0x3e4e4800000000144d2,0x4000032083e05e800002,0xa4fae184f0000048d870,0xcfd80000684240000145,0xafe910f00001a07e8000,0x702c7516ba000004144,0x100494071a20872805c2,0x82fa724a8a0be1c884e0,0x28750517687de0996380,0x5fc081780db3d9655091,0xc400c4404acc8e880000,0xd11b600002810b800005,0x548000d59916f034cc0,0x7d8000034850500c4000,0xab2021f0164800000755,0xc86d601d616690,0x11900000c,0x3900000000008056a00,0x6814792694887,0xe8000000000046160000,0x248663815c0000120803,0x12ecb30600000b0ce00,0x1c3b8251974de00001cc,0xcc9030b00000e0637046,0xe80000c05e200001421d,0xb209690056a0623d8f41,0x400000180e90000068,0x1a0000120c11c147380,0x5b4030400003c1978000,0x80488804f140f63910b,0xd43f6d22b00000000000,0x264ca0000000,0x78092321]))))
def g243D8 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then (word80 [0x88b14121,0x222858447091142c2c34,0x6251161484346004a22c,0x3a2326032e1412232606,0x3105114109030488c412,0x83821260b0808b140c10,0x6305043000816282c304,0x50b0808a94302014460a,0x809098282021800a884,0xb03005450458a860491,0x804505080c8822c28684,0x60a08608000458a0d08a,0x160c3423050400041182,0x5060308c14108180450,0x4060011828280080c110,0x2c318040081628302006,0x211414c16045042808b0,0x6084982c2022c5030402,0x98282980040b1414402,0x285841260b06504180cc,0x22000b1418119305840,0x464c16111820250b0a60,0x1142c545080d11610284,0x688b0a8ca160d181326,0xb0a8c0942c2013254b1,0x4140802c5440258a868d,0x1142c223040111614119,0x301823004a0864018200,0x4a0c002032c2160600a8,0x80c0022c5452c0c01510,0x83006440600b1510180,0x458a8a6001604505300,0x400232506305811410c1,0x60800a8a6001628259e6,0xcaf635b0657aab75591a,0xb0d4c6a034d8a49d1c68,0x9141f9fecf3673b37499,0xecc1a58329192d48c63e,0x71b58bbc4e61f70c4838,0xc106006fa27b5bcd1e16,0xee275239d1c7ae1b6f23,0x6edb24d5b69cb45d9dcc,0xbe647315d84ebf75eaae,0x796b2b3057caad1516a6,0x9523a8953f89d34ce260,0x52a292f47c2359176899,0x438213905880a3f41f18,0xf3a7823ac9cc0e1c6de3,0x619a84ce264f3169810b,0xa85a42bd9564a7c51c28,0x936095e48d239115c84,0xe4051f18ee872236f1a3,0xcac6042e015b8a544f4,0x25811788503e41c20d00,0x5f82aa13308883bc18c0,0x9d036812c044000ff989,0x30ff58930ff98530ff58,0x530ff90530ff50530ffd,0x4720ff94720ff54720ff,0x14720ff90720ff50720f,0xf10720ffcc320ff4c320,0xff50620ffd8d20ff98d2,0xff58d20ff18d20ffcc9,0x20ff4c920ffd8520ff98,0x520ff58520ff18520ffd,0x4520ff94520ff54520ff,0x14520ff90520ff50520f,0xf10520ff88520ff48520,0xffcc120ff4c120ff5042,0xff94a10ff54a10ff90a,0x10ff50a10ff8ca10ff4c,0xa10ff50610ffc8610ff4,0x8610ff98d10ff58d10ff,0x94d10ff54d10ff90d10f,0xf50d10ff10d10ff98910,0xff58910ff94910ff5491,0xffcc910ff8c910ff4c9,0x10ff0c910ffd0110ff50,0x110ffcc110ff4c110ffc,0x8110ff48110ff94810ff,0x54810ff8c810ff4c810b,0xf59630bf59230bf58e30,0xbf58a30bf58630bfd913,0xbfd8930bfd8530bf590,0x30bf58830bf58430bf58,0xf20bf58720bf58e20bf5,0x8a20bf58620fe4c220bf,0xd8d20bf58d20fb8c920f,0xb4c920bfd8520fe8c120,0xfe4c120bf58c20bf5842,0xbf59610bf59210bf58e,0x10bf58a10bf58610fe54,0x210fecc210fe48210bfd,0x9510bf59510bfd8d10bf,0x58d10bfd8910bf58910f,0xe94110fe54110fe90110,0xfe50110fecc110fe0c11,0xfe88110fe48110bf594,0x10bf58c10bf58810af99,0x30af59030bb98830bb5,0x8830bd98430bd58430b7,0x98c20b758c20bd98420b,0xd58420af99210af59210]) else (word80 [0x4509,0x8445054288c14108a22c,0x5044420c16282c24458a,0x9152c24454a0d112168,0x460588921a3845868892,0x1a384586889002184606,0x868d2422c2c586951c04,0x884542240422c5048284,0xa42302c1425211814542,0x2c5044200c0228406208,0x44422860642608422828,0x84208014206072086080,0x450c0e0c84142480182,0x8089488c1002c4062091,0x18a1108b0e9119084585,0x14212230400b10208240,0x4022422c608209118089,0xe116208244602243845,0x88209010089090982082,0x3010d2422c38021152c3,0x46910c28028b20080422,0xc50620911c4860011620,0x908a96224868c8c0420,0x11a410c28208a181c82,0x18202114303992b08b14,0x162243088b0a5c2c4049,0x11182c4454a120a22831,0x38a112a2825078261114,0x10903048a098283c2445,0x8514162241088b0a4622,0x444201161c9222858444,0x20a16121224658a0a661,0x222860b0c8a1062820c0,0xc951068b08a941d14210,0x5921818992488d116192,0x23445840b112434688b0,0xe5c2c48609223445890c,0x88c08282a58a8c341288,0x87064a2a547051062848,0x82c88c14161222858484]))
def g243H8 (j : Nat) : Nat := if 5 ≤ j then 0 else (if j<2 then (if j<1 then (word80 [0x14225,0xf046c000000000000000,0x50904ce8059,0x8043d484ca42bb303388,0xa0f0046a81b1c1b40000,0x21ac0431e30b1ac58bc,0x760dc253f22478286938,0x67402a000018c3d307a9,0x82b2e0b3c41f4e20a510,0x5170c0000000000091d6,0x50327099d00003c22900,0x32642c2f3e01b,0x8c2920000144f731ade4,0x5a0bad831000001161,0x4c06280000d05cb9e180,0x14a2c092000000000458,0xf3108c40c86825ec2c10,0x4097f14ec044f00001c0,0xa0825a7484140a52c81d,0xd07ed497450b64000092,0x9b80000238c6c106309f,0x84c42b1686d48e000008,0x6550000009c19071c000,0x483b4026694164825ab,0x260cc125b09b141f8502,0x6b8140519aa42a030a58,0xb06a400003066082,0x3f00000000030a754130,0x80350000000000000024,0x5b3a5cd4042b84441371,0xc0000000000000802348,0x924305ec000054b5d802,0xeb832c92470000000000,0x3124c00002c07400a,0xa7c0b9902d3c07dc0634,0x9051c0000820ca05,0x749030a4430112298086,0x674000084,0x63292888088000000000,0x295e3476c1d,0x1d3003f7808800002c09,0xb6097c00000000000003,0xbe282a7a26bc813950b,0x1e8288719d4000014163,0x1c6ff08b00000b64b60a,0x49203e00000729dc8157,0x20bd6a12ea80ef46fda0,0xb14010b0000000000000,0x308078196e811870ca28,0x209272dc0b760258000,0x5442802dad0c20094eb,0x4bb40000d09a00000000,0x1004382792c86ed0499,0x40f000003804140c0e42,0x40405c00000300db1c70,0x1080000a06aa007300,0xb665cc13b002a,0xb8039b0af8d24db578bc,0xa1d000000000b17b9da6,0xd80816c5c75069308626,0xf000006873602e3000,0x24159240e40000c268c,0xc05df058c0000e0c1783,0x1ff09d75b0a091e28251,0xe02cc41f3d0ab9817406,0x1a2014d00001c0ab459b,0x80000000000000000009,0xe38e0120cb1c113d0481,0xb000008084f074fc20f0,0x31a74e08db1166851,0x94000000000000000000,0x6011420005440b6b3184,0x8005000008a240520324,0xd4a821e6818416000863,0x831d0800333000005982,0x240101e1448681170800,0x4002103008048182,0x86001400140780870004,0x58214200942820189065,0x85000028881621872904,0x4470a48dc19114000060,0x2a40031a8800d0004806,0x8240850410100903c00,0x70c15983004018304380,0x8142105873c746820a08,0x110034000004048a188,0xc081044400106244211a,0x28d0a4810920140001,0xe0c480022ca013400004,0x400b820400aa10428d0,0x20020380140000308403,0x1a0a00786000000d5621,0x5000608b8814101000c1,0x41822800000241858726,0x4811001030e40000841,0x214f84085c1000e54081,0x4c0808b0c140073c4810,0x11c0c40102c018004241,0x80020440100046805e48,0xf800c1478a021c200040,0xc880142000804007010a,0x4381000000302080800,0x8204029c0000200309]) else (word80 [0x505a526d,0x3942d703f9966ab16550,0x9a871984023700001007,0x5791d00000d031ec02f2,0xa3ac07fb099dc02301a,0x4c0000f15dec30e402f7,0x8c3f7018501510000182,0xdcb4b7cd600b01880000,0xb168fd1d40000240cfe0,0x743c14100003c56dd032,0xa4087802bf4973a2c0a9,0x8ec905b2030b00003c2f,0xf00000001b9072555040,0x301f2709e28161901,0x58000030b340000d016c,0x42a0e80b8f0031c0,0xbcd06980000e83500000,0x604894171b02ec000000,0x3c5a9107dd95b1846e,0x884c5c0673d0c4104404,0x30200000000030b75813,0x1b491b91900000000001,0xae599ef00003004c808,0x5d02c1c149a010c436ac,0xd003682,0xef048ac0000000000000,0x707f1c271e0294c0f552,0x7cd86a465987004528c3,0xac2e0202280576827c1e,0x604a0b854423a038799b,0xfb4172e5dac9b6d96af6,0x15bb056a00001c5a7000,0x349794086c,0x11bc00003c155806bc00,0xc0cd80b4282b1,0x45c71256f027fc06a00,0x499fe03a8043f40bb,0x9c2fe8073e8148b05580,0x86924000050065867,0xc00002003b984e9c31c0,0x80b,0x2e805862a25c30730c1a,0xe5be329bf800260a6342,0x99103b28150325ac0000,0x40772c9f7d20f9c17562,0xbfe8311f25d588984256,0xa905532872c15e000000,0x14178671cbc0d,0xf000000000b060650030,0x38819e7867866fc05,0x9352ce441404257a06eb,0xe13d3980c233804cc06,0xc4f49998844141efc16b,0x101e400004520f064a91,0x61cc440208ab81dbb1ae,0xb05041238e430ca267ac,0x13fd028f441b408f2800,0x300b8802fbf0685c291e,0xc05c293601024244d09,0x568868a6a415196c07fd,0xc42ae07b80af600c6342,0x8db96b7105b107e6850c,0xe898556d0e043a808c30,0xc980000b0482c2b3500f,0xbc26383263482cf09094,0x241c445fc681f0343028,0x646e1c84d591e400005,0x184e02e820694c1e8b4b,0x689322a01edc12700003,0xc188f088c0000c10cf41,0xd1e00600000000004830,0x1215c411300003128021,0x9c00000104f7c4be0000,0x84ca51bfac,0x2a5d0563c04400002c0e,0x60000209e90097400000,0x3064fe0efa08,0x541e1500b2403030a28,0x4a8ea09dd4575b0b0049,0xef205a8c274000038a76,0x25182c46014097006300,0x19582f035800008258,0x640720023bc2822084e4,0x9640000002b8342809a4,0x8e0927d03770b6e01ab0,0x389f174a9c0000000,0xe0678,0x6024d4132b980800,0x10a31822f000000000,0x603bf092630,0x7184076358fec1eb6034,0xa945ed84c00000c138c0,0x37842902028b41c,0,0x627680000000,0x28da100000000000001,0xc8e1f1b7842e7f459580,0x829202c8617c015f2292,0x408840000829fc0238c0,0x51602ac00002e5cb6196,0x3019ff26f80000000000,0xd4aff42ccd27a2c1e,0xc06b9cd8df29eb00380])) else (if j<3 then (word80 [0x9472e803,0x5f05e800008052b02fad,0x23a489f8504d04e36000,0xd0ad4c29eb054c,0x10a87927d0000080,0x10208d40000f02b3c2fd,0xf0368005094176993000,0x7002250562091,0xc000000001c83f000000,0xe36c0000000798000,0x3020e40a1929b74af70,0x3c58a000000000000,0x1ec00000000000000,0x3149400,0x34250000024319,0x381f600001c0b100,0xa8c1800000000,0xc0f4502640000000000,0x5089d503500000000,0xd06d000000081b40d9c,0x4acc2ea246fe0295895,0xebc6b8f9b5d428700000,0xf19500000a0a8c42,0x12d078800000000389b0,0x746e5047330a98000000,0x290c60000000000000,0x3c4424202709b11050e8,0x923f0774000090c758e2,0x1c91514db5000010027a,0x97580443e1a374265009,0xf3023bd497c80c300000,0x1d28a0000291,0x46229a4000010b5591bb,0x20ae800005471c000000,0x1c9db20245c9940000,0xd96b906dca12f019f40,0x100d0465d00001021,0x8b8a4001ca209beca2a3,0x889c315d20540000f00,0xb7c26b61b31448930071,0x1c71602928162425b800,0x3a0d520c121990,0xb019c0000e061c027344,0x46800000000202adf375,0xc000094b19c4d4402f9c,0x2839012d401d40191a47,0x73077a90813097180d59,0x13a520cd05b80000409,0x63015d00003c116a04f2,0x8190f914e5a9c1045c5e,0x34a4a3357e430f,0xe58e64705f05b4428540,0x87c000010be4217ae10b,0x901860000241f0764b80,0x301d2a079056c,0x75118ec0dbe60bc00005,0x6e000000000182aa509,0x30c29c00001424a829cb,0xa19b30851c0f2b36ab06,0x5a909dbe5d9401e358ee,0x6087b400600000000000,0x3a26e7943400000040,0x880157289c0000000010,0x8500000000000003020,0x200002d0420000000000,0xc340000508c6812460b,0x4dc1f1f0b98000034324,0x716200000d448400,0x219c0000,0x2522fa05180000e6,0x640000d02554021e83e,0xbc81c00000c4e29175d0,0xa5d00000000000000000,0xa27b040550000000009,0x51880000e0b0c0262000,0x8245a1a44c324104b9,0x5a8b02a70207b430c82,0x46e17bd4100e36bec18c,0xe81dc000000000000000,0x3024b0000282afd036,0x2c6630000244d7e0a6dc,0x6ff76c501c8f2a3242f,0xe070540b265352420bc,0x277b110b106cec18f108,0x720204e06e4000032741,0xc10f00000821d0000103,0x13b07f4496f301700000,0x3013c49f2b001d1dc9e0,0x7660104000001021608f,0x74e2300002099c000014,0x1b000002496d00000497,0x68072c000000003806ce,0x458906e6c28860985c26,0xff89d6c1212416fa48b2,0x89cc00000c1c40000041,0x5c10893c823b65840000,0x905da9212a4b6625c200,0x1a0000062129c2708052,0xeca82e0b125252000014,0xdb451c34081e229ac000,0xa03cee5aef093c00001,0x159182ce20a3cc203a10,0xfa441c0000398f8005f5]) else (if j<4 then (word80 [0x782d8106,0x9dc17732722827900000,0x5110400000000000,0xf0649483840603c200,0x5029a080060370000042,0x611407a329a388de9121,0xc081a2687ec09ed0c580,0x263b6a25541980001,0xef0068c26a206f001f50,0x30114a16,0x1acc400000349c0e068a,0x11cf910920033f039f92,0xad5435a8a79440eb814f,0xf07b6813ac05f350d3f2,0x71d86bba04b5c197a05e,0x7c111000020017703d84,0x185d2093a5b340524c10,0x900000024d369b800009,0x25b20004b0c8f886d105,0x7c8252a073886ff607a7,0x804d0000000006082091,0xec0b900000d01799dbd,0xf38a0000022581c61450,0x91489470a0400000000,0x24189226340659c04778,0xa1b00003806df0964c27,0xa00000c12f0000000004,0x95ee024800001c297000,0x42f779770000000000,0xb032f011ff26aec4,0x46920d0424300003a0ee,0x2466b800ea8a8c931b94,0x76a4194706f88578a068,0x341d6f082641cc00b204,0x6a1983f3929634bed800,0xab3682c0ffb06fc80b00,0x508f927eb0a249aa0119,0x904a6c0000026da00000,0xc30ac0381005f0000000,0x30c50000070b2a02d4,0x1417525300002821680,0x27400000000000000000,0x367798184410580,0x32736c011908e540b,0x59024140e9583c3c2f20,0xe0a2c0000000,0x288e224b8e25ceb204c,0x3c2de2023c89,0xe2d693342d200000826d,0x18890308684d7300,0x2062d20f20000,0x827b5053088e7a00068,0x312f05fec06500001529,0xbb040c0000219bac0c43,0x13c400006132e12ec000,0x318096d4256d079c,0x42ec00000000000002c0,0xe5b0843e1e6000000000,0xa0344c2ab9113a42a460,0xafd8260108ae80e46042,0x1031b000034847000000,0xe0a88000,0,0xc16700002803d677,0xf890c8000000000b30a4,0x2114a0000285,0x79115a6c1ef603a28191,0x324529070c42b442,0x1a681b560203c165b022,0x445355475c269670aa15,0x134267d109563d4000,0x301df05a0420b7409cd,0x78c82e9e0795c182906,0xb14d69707540000d0472,0xc15b000010012a083a64,0x3ba60694a1a000004081,0xa034c0000d44600000d9,0x706c037301478536a06f,0x4d19220448000000003c,0x1fab09fdc1ad0000280f,0xbb0c9d4925a02b400006,0xbb40000663cb018e227,0xec8573a03ac89e700000,0xe040750d200001c4,0x2b087900000000000000,0xe96c8157550568006065,0x7f8c82f000000000b041,0xc0000b04840000000004,0xc100000000000002e0e,0xc201198828a00c942b72,0x1a0a407c000000000505,0x48c1b6c0bc7a19cd4b5a,0x884881a01d44a10865c9,0x82e011f6131905a1012c,0xd1abf4703000008827f7,0x1ba01bb50af7c8e0f005,0x80000340bf8026e0c5dc,0xc4900000814e00000429,0xfc10a542320000045a5f,0x737096820c240000504,0xa00000303b741d7f04d5,0x4211b08300000e09f680,0x25930fa80f130464844d]) else (word80 [0x9266f80fa000000,0x3c05,0xae191fd92f40513c11e6,0x7154173a019800f9208,0x990049b13560e18b17b4,0x45e7065b41,0xa830129022df4661c261,0x85328000043120001f00,0x2006b1666400000000,0x14094e00500,0x1c0dd00000000,0x5135a031a0,0x30836208280000b09,0x500000202fe41d4a0b5e,0xc2153031be5ca0000000,0xf97c1ca22129220195,0x529ecc22820550000084,0x36c0000d63adc22e0000,0xa08f900f7139521,0x31409c80000d014bd0d,0xf26a800009008880e20,0x20517e02b89e34503,0x15c137b0af0842da8328,0xc5a2e41180000c068edd,0xfc000004610e19fac956,0xf04fb503c001a5d45f70,0x2e9816900002c00fd12f,0x4000002763c0c8000010,0xee71c2000000093b01b,0x2627a821a4402d902b68,0x7600000d2a000000a83,0xee88e40000101dfc275c,0x2f68030001,0x38006680000f32a142d1,0xa00fc418300002c84bd0,0x66cc999500260e1bc52c,0x4819994a1c0000b09b98,0xfcb03300000000020a5,0xc000000000222000000f,0x6a78000038a954997e01,0xf9183800001c054c048c,0x531ce8059f002e05,0xa600001c483c07680000,0x109a494613014e81fee2,0x61823ae36b206c70000,0x3908d701c0c17e3970c0,0xa1c2c0000a1aa8000,0xe08d349a20,0x2bf0c589d0c800000376,0xbc00004022ea47604481,0x115a0c940000926d400,0x238c3c2c2245240000,0x5a2520bf0c29ae2,0x9c149e6202a040290178,0xc9191b20ad09f4d05824,0x136f6c321655c038ed01,0x9826a606980000142c9f,0xa202d6000034284000,0x2c1c2000000000c2100,0x4483682,0x300000340d7000000000,0x3001300000000000,0x7112ec616b00e,0x800000000000008499dc,0x69900001516be46df95e,0x580b95c2df300ad43221,0x52240000000000000e04,0x3782f4004a40000f25de,0x48dd0000202b0e029c00,0x3420d5111749df,0x52dbb1a7f026470,0x2624071604aa51616041]))))
def g243D9 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x60510308159400914408,0x10c06142051020560d50,0x81440c10021981440c1,0x9650024510304200660,0x51030565020096051030,0x815940091440c2040587,0x605103094059009f06aa,0xe94a87391506c1e003fc,0x61fd30fe187fc83fc41f,0xd20fe107f843fa21fc10])
def g243H9 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then (word80 [0xd0390000,0x112d21785056494c5972,0xe055501ea54e706c,0x62472542b24b0000304e,0x245c00000000a75e0000,0xd16f0000000000000000,0xc128000050740000d036,0x985f5085000000000000,0x20320000c021a03b412b,0xd080f117000000000000,0,0,0xf860,0,0xb2430000,0x1125,0,0,0xb6580000000000004127,0xa131,0x305000000000a446521a,0x206300000000,0x206900000000255f305f,0x7880c02f6012f67f9083,0xa44a2665165929557008,0x74270000394970100000,0xd023a445f04c50227007,0x2139029f67e787e8079,0x807d000000000000,0x8560300d044b,0x90200000,0,0x81320000000000000000,0,0xf2680000000000000000,0,0xf064000000000000f267,0xa17600000000,0,0x520f000000000000,0x995b0000,0xa0356472000000000000,0x6261816e00000000,0x404d,0x835d10263254703e0000,0x602d,0x5d00009038,0xf95c835a0000e2140000,0x3072404970510000c93f,0x4175b02e0000512ab034,0,0x52400000d042e35e,0xd030000000000000,0x7059000000000000,0xd03c,0x2940f2190000000b9057,0xb92b0000000000000000,0,0,0xf05c0000000000000000,0x20140000,0x806a0000207000000000,0x32460000,0x8381e215405b886c7953,0,0x2043794a00000000124a,0x81710000000071102045,0xb41ee07e000042567752,0x886a901d00003515b169,0x624cc06d000080860000,0x538044,0x8017,0xd94b0000000082443077,0xb67d,0x387d000000375006,0x117d0000,0xc17200000000,0,0xb4360000000000000000,0xc16d0000f07630730000,0x4ba00300000000,0xd04f00000000f1030000,0x611d0000b2660000504a,0xc0240000d0050000,0xb033611fe04700000000,0x7168200ec12c102b566b,0xb439000000000000,0xa00f000051640000,0x51146062602ad2120000,0x566a00000000,0xa165d17c0000,0x9025416c0000,0xc27c240ae041703a0000,0x94120000c42b,0x105a00007068c0780000,0x70820000000000000000,0xc27b151f940b0000,0x2061000000000000a180,0,0x62240b11f8600343,0x30242100366115400810,0x68100b02092030001000,0x64057024102420305200]) else (word80 [0x3479301cf13300000000,0xc07c0000000000000000,0x6052000000000000,0x8463c11b3478c1290000,0x22530000000000008071,0x6e000000000000,0x1143000084620000,0,0x5013112e00000000,0xd0280000000000000000,0,0,0xd0270000744c00001009,0x71442751000000000000,0x3869a23f11731245,0xb06bf00400002002,0,0x3105f00c000000000000,0xb4820000843f0000,0x12164174320d0000912f,0,0x142e9258107f0000,0x400a000000000000,0x925aa16a,0x6001616b000000001126,0xc02cc2650000e0840000,0x525700008249e4400000,0x540000f259,0x82489040c031,0x255911600180000910f,0x401b017e0000f01f0000,0x81020000e03f00000000,0xc17f9115,0xa05e,0x5282e06f,0x203d534800000669,0x6449506700008016,0x20605011000000000000,0x5081517081040000,0x60650000000080750000,0x216300190000,0x6277951b4000727a,0x801ab07b0000c2104411,0,0x50660000,0,0x8179,0xb2110000a0580000c162,0x454d,0x15c541b07a7048,0xc45b475d,0,0xe04600000000]))
def g243D10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3f
def g243H10 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x10b0001b32,0xc4c24540200000000061,0x2000000001621e720003,0xb284000f0d08644ac10,0x6068f2252000825804e0,0xccc580a08a4c9471aae6,0xa56226ca6a0262000e50,0x80ee32eb3e096cd6a3ae,0x4200001d044e10480000,0xc6692665047f080d2c88,0x91200002e000c6e524e8,0xdc4e001e600012e20000,0x1831d06152080,0x85c022a0a40080201480])
def g243L : Nat → Packing
  | 4 => (3,6,5,0,0,4,0,g243D4)
  | 5 => (201,5,5,0,0,11,0,g243D5)
  | 6 => (1109,4,5,0,0,14,0,g243D6)
  | 7 => (809,3,5,0,0,15,0,g243D7)
  | 8 => (135,2,5,0,0,13,0,g243D8)
  | 9 => (10,1,5,0,0,9,0,g243D9)
  | 10 => (1,0,5,0,0,0,0,g243D10)
  | _ => emptyPacking
def g243I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 5 0 6 2 0 g243H5
  | 6 => lookupWord 83 541 6 16 8 4 g243H6
  | 7 => lookupWord 477 3061 7 19 11 4 g243H7
  | 8 => lookupWord 366 1997 7 18 10 4 g243H8
  | 9 => lookupWord 76 761 4 16 8 4 g243H9
  | 10 => lookupWord 15 83 7 12 4 4 g243H10
  | _ => fun _ => none
def g243 : Forest := ⟨243,10,fun i => g243Y[i]?.getD (0,0),g243C,g243A,g243L,g243I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P4_0 : block g243 4 0 3=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g243B4 : block g243 4 0 3=true := g243P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P5_0 : block g243 5 0 96=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P5_96 : block g243 5 96 96=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P5_192 : block g243 5 192 9=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g243B5 : block g243 5 0 201=true := (@block_merge g243 5 0 96 105 g243P5_0 (@block_merge g243 5 96 96 9 g243P5_96 g243P5_192))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P6_0 : block g243 6 0 2=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P6_2 : block g243 6 2 53=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P6_55 : block g243 6 55 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P6_151 : block g243 6 151 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P6_247 : block g243 6 247 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P6_343 : block g243 6 343 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P6_439 : block g243 6 439 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P6_535 : block g243 6 535 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P6_631 : block g243 6 631 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P6_727 : block g243 6 727 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P6_823 : block g243 6 823 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P6_919 : block g243 6 919 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P6_1015 : block g243 6 1015 94=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g243B6 : block g243 6 0 1109=true := (@block_merge g243 6 0 439 670 (@block_merge g243 6 0 151 288 (@block_merge g243 6 0 2 149 g243P6_0 (@block_merge g243 6 2 53 96 g243P6_2 g243P6_55)) (@block_merge g243 6 151 96 192 g243P6_151 (@block_merge g243 6 247 96 96 g243P6_247 g243P6_343))) (@block_merge g243 6 439 288 382 (@block_merge g243 6 439 96 192 g243P6_439 (@block_merge g243 6 535 96 96 g243P6_535 g243P6_631)) (@block_merge g243 6 727 192 190 (@block_merge g243 6 727 96 96 g243P6_727 g243P6_823) (@block_merge g243 6 919 96 94 g243P6_919 g243P6_1015))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P7_0 : block g243 7 0 7=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P7_7 : block g243 7 7 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P7_103 : block g243 7 103 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P7_199 : block g243 7 199 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P7_295 : block g243 7 295 47=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P7_342 : block g243 7 342 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P7_438 : block g243 7 438 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P7_534 : block g243 7 534 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P7_630 : block g243 7 630 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P7_726 : block g243 7 726 83=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g243B7 : block g243 7 0 809=true := (@block_merge g243 7 0 342 467 (@block_merge g243 7 0 103 239 (@block_merge g243 7 0 7 96 g243P7_0 g243P7_7) (@block_merge g243 7 103 96 143 g243P7_103 (@block_merge g243 7 199 96 47 g243P7_199 g243P7_295))) (@block_merge g243 7 342 192 275 (@block_merge g243 7 342 96 96 g243P7_342 g243P7_438) (@block_merge g243 7 534 96 179 g243P7_534 (@block_merge g243 7 630 96 83 g243P7_630 g243P7_726))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P8_0 : block g243 8 0 12=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P8_12 : block g243 8 12 51=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P8_63 : block g243 8 63 72=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g243B8 : block g243 8 0 135=true := (@block_merge g243 8 0 12 123 g243P8_0 (@block_merge g243 8 12 51 72 g243P8_12 g243P8_63))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P9_0 : block g243 9 0 10=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g243B9 : block g243 9 0 10=true := g243P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P10_0 : block g243 10 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g243B10 : block g243 10 0 1=true := g243P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243T : checkedTables g243 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g243 0 0 0 = true)
  · exact (rfl : block g243 1 0 0 = true)
  · exact (rfl : block g243 2 0 0 = true)
  · exact (rfl : block g243 3 0 0 = true)
  · exact g243B4
  · exact g243B5
  · exact g243B6
  · exact g243B7
  · exact g243B8
  · exact g243B9
  · exact g243B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243G : graphValid g243 (boundsBefore K227) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low243 : Lower true (varsX 243) (graphGoal 243) 11 := lower_forest (g:=g243) (i:=0) (hints:=16777284) (before_sound K227 V227) g243G g243T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K243 := extendKnown K227 11 [(243,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V243 : Known true K243 := extend_ok (m:=243) V227 low243 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255R : Impossible true graph 12 sevenInputs.toFinset := by
  change Impossible true (graphGoal 255) 12 sevenInputs.toFinset
  exact cut_root (m:=255) (before_sound K243 V243) (12, 0, 243, 0, 11) (by decide +kernel) (by decide +kernel)

end PEqualNP.Outside.L_meta_32373

open PEqualNP.Outside.L_meta_32373 in
theorem PEqualNP.Outside.L_meta_32373 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 4, 5, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 4, 5, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 4, 5, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 4, 5, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 4, 5, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 4, 5, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o fit _ correct
  exact replaceShort g255R gates o fit correct

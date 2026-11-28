import PEqualNP.Defs

-- The two-mode live-state and cofactor checker follows L_meta_1674 and L_meta_670.
-- The graph, restrictions and all search certificates below are for L_meta_51746.

-- Shared forest and cofactor certificates from L_meta_1674 and PR 11111 for L_meta_1677.
-- The original credit line is retained below. The two root certificates here cover the unpinned graph.

-- The checker and the bound certificates are adapted from PEqualNP/Outside/L_meta_1667.lean (Apache-2.0).
-- Two modes: u=false are monotone runs (AND, OR); u=true are runs up to complement, where negation is free.
namespace PEqualNP.Outside.L_meta_51746
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
def graph : Sig := (BitVec.ofNat 512 (word80 [0xffffffff,0xfffffffffffffffeffff,0xfffefffffffefffffffc,0xfffefffaeeeeaa00ffff,0xfffffffffffffffffffe,0xfffffffefffffffeffff,0xfffcfffefffaeeeeaa00]))
def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 4) || (x 0 && x 5) || (x 2 && x 5) || (x 3 && x 5) || (x 1 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 4 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 2 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 6 && x 7)
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
  (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 2 &&& x 5) ||| (x 3 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 2 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7) ||| (x 6 &&& x 7)
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
  (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 2 &&& x 5) ||| (x 3 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 2 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7) ||| (x 6 &&& x 7)
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



def target (x : Fin 8 → Bool) : Bool := decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
def smallCircuit : Circuit := ⟨[⟨.or,[5,7]⟩,⟨.or,[3,4]⟩,⟨.or,[0,7]⟩,⟨.or,[3,2]⟩,⟨.or,[0,11]⟩,⟨.or,[4,7]⟩,⟨.or,[6,13]⟩,⟨.or,[11,13]⟩,⟨.and,[1,14]⟩,⟨.and,[12,8]⟩,⟨.and,[9,10]⟩,⟨.and,[6,15]⟩,⟨.or,[16,17]⟩,⟨.or,[20,18]⟩,⟨.or,[21,19]⟩], 22⟩

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
def K41 := extendKnown [] 4 [(41,[]),(82,[16,67,101]),(137,[117,101]),(145,[67,117,101]),(146,[16,67,117,101]),(194,[16,99,67,117]),(196,[32,16,99,67,117]),(208,[64,16,33,99,117])]
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
def K27 := extendKnown K41 4 [(27,[]),(51,[83]),(53,[33,67,83]),(75,[96,16,49,67,84]),(77,[96,16,33,50,67,84]),(85,[96,16,33,50,83]),(101,[32,16,99,84,67]),(113,[64,81,33,99]),(116,[32,65,83,97,49]),(120,[48,65,32,82,97,33]),(163,[83,116,100]),(166,[32,83,116,100]),(170,[48,32,82,116,100]),(180,[32,65,83,113,49,99]),(225,[112,81,33,99,64])]
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
def K45 := extendKnown K27 5 [(45,[]),(57,[48,66,80]),(83,[16,32,99,67,84]),(90,[16,50,66,101]),(105,[98,83,66]),(139,[33,117,101]),(141,[117,101]),(149,[67,117,101]),(150,[16,67,117,101]),(154,[16,50,66,117,101]),(177,[64,82,115,32,99]),(195,[16,32,99,67,117]),(197,[32,99,67,117]),(228,[96,16,82,115,65,67])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V45 : Known true K45 := extend_ok (m:=45) V27 low45 (by decide +kernel)
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
theorem g147G : graphValid g147 (boundsBefore K45) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low147 : Lower true (varsX 147) (graphGoal 147) 5 := lower_forest (g:=g147) (i:=0) (hints:=68) (before_sound K45 V45) g147G g147T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K147 := extendKnown K45 5 [(147,[]),(153,[48,65,33,32]),(169,[80,113,33,50,64]),(201,[97,33,50,67,84]),(202,[16,48,32,100,84]),(204,[32,49,100,84]),(212,[32,65,49,99,83]),(216,[48,65,32,33,98,82])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V147 : Known true K147 := extend_ok (m:=147) V45 low147 (by decide +kernel)
def g210Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0xdf7ec03c3ffe0fbefd,0x80787ffc1f7dfb00f0ff])),(BitVec.ofNat 152 (word80 [0x820404444444210408,0x8888888420810111111]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1fbf43c3c3fff03f7e,0x878787ffe07efd0f0f0f])),(BitVec.ofNat 152 (word80 [0x40808888888420810,0x11111110841020222222]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xe03fbc03fc3fffc07f,0x7807f87fff80fef00ff0])),(BitVec.ofNat 152 (word80 [0x81011111110841020,0x22222221082040444444]))),((BitVec.ofNat 152 (word80 [0xffc03ffc003fffff80,0x7ff8007fffff00fff000])),(BitVec.ofNat 152 (word80 [0x102022222221082040,0x44444442104080888888]))),(0x0,0x0)]
def g210C : List ColumnInfo := [(2,0,208,0,4),(16,0,194,0,4),(64,0,146,0,4),(128,0,82,0,4)]
def g210A : List (List Nat) := [[],[118],[100],[100,116],[116,100],[116],[65],[65,118],[65,97],[65,97,113],[65,113,97],[65,113],[97,65],[97,65,116],[97],[97,113],[97,116],[97,116,65],[113,65,100],[113,65],[113,97],[113],[113,100,65],[113,100]]
def g210D3 := limbs80 #[#[0x23ea6a1221e12148110,0x8028]]
def g210D4 := limbs80 #[#[0x2fd0910bd42443e48110,0x609085870]]
def g210H4 (j : Nat) := if j=0 then 0x20b else 0
def g210D5 (j : Nat) := if j=0 then 0xd1027d10 else 0
def g210H5 := limbs80 #[#[0x2700000000027000,0x1c1000000000c2f1000,0x1440000002c00000000,0x10c00000]]
def g210D6 (j : Nat) := if j=0 then 0x3904f else 0
def g210H6 := limbs80 #[#[0xa255123a000000018000,0x1a40000001]]
def g210L : Nat → Packing
  | 3 => (2,3,2,0,0,5,0,g210D3)
  | 4 => (3,2,2,0,0,5,0,g210D4)
  | 5 => (1,1,2,0,0,0,0,g210D5)
  | 6 => (1,0,2,0,0,0,0,g210D6)
  | _ => emptyPacking
def g210I : Nat → Nat → Option (Nat × Nat)
  | 4 => lookupWord 1 2 0 5 1 0 g210H4
  | 5 => lookupWord 2 31 0 9 2 3 g210H5
  | 6 => lookupWord 1 17 0 9 0 5 g210H6
  | _ => fun _ => none
def g210 : Forest := ⟨210,6,fun i => g210Y[i]?.getD (0,0),g210C,g210A,g210L,g210I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g210P3_0 : block g210 3 0 2=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g210B3 : block g210 3 0 2=true := g210P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g210P4_0 : block g210 4 0 3=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g210B4 : block g210 4 0 3=true := g210P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g210P5_0 : block g210 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g210B5 : block g210 5 0 1=true := g210P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g210P6_0 : block g210 6 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g210B6 : block g210 6 0 1=true := g210P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g210T : checkedTables g210 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g210 0 0 0 = true)
  · exact (rfl : block g210 1 0 0 = true)
  · exact (rfl : block g210 2 0 0 = true)
  · exact g210B3
  · exact g210B4
  · exact g210B5
  · exact g210B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g210G : graphValid g210 (boundsBefore K147) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low210 : Lower true (varsX 210) (graphGoal 210) 7 := lower_forest (g:=g210) (i:=0) (hints:=285278272) (before_sound K147 V147) g210G g210T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K210 := extendKnown K147 7 [(210,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V210 : Known true K210 := extend_ok (m:=210) V147 low210 (by decide +kernel)
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
theorem g55G : graphValid g55 (boundsBefore K210) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low55 : Lower true (varsX 55) (graphGoal 55) 5 := lower_forest (g:=g55) (i:=0) (hints:=1348) (before_sound K210 V210) g55G g55T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K55 := extendKnown K210 5 [(55,[]),(103,[32,16,84,100])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V55 : Known true K55 := extend_ok (m:=55) V210 low55 (by decide +kernel)
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
def K59 := extendKnown K55 7 [(59,[]),(107,[48,100]),(115,[64,81,49,99]),(118,[96,81,32,49,66,67]),(122,[96,81,32,49,67]),(182,[112,81,32,49,66,67,99]),(186,[112,81,32,49,67,98]),(227,[112,81,49,64,99])]
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
def K61 := extendKnown K59 6 [(61,[]),(87,[96,49,32,66,84])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V61 : Known true K61 := extend_ok (m:=61) V59 low61 (by decide +kernel)
def g91Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffc01ff0ff0ffc03f,0xfff0ffff35d6430000ff])),(BitVec.ofNat 152 (word80 [0x282a140a202282a2a1,0x50220820148643999999]))),((BitVec.ofNat 152 (word80 [0xffffe000fffffffc0,0x1fff0ff0d4353900ff00])),(BitVec.ofNat 152 (word80 [0x40b0182c41400b0305,0x81402042903511333333]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffff000ffffff,0xe0000fff2bb5260f000f])),(BitVec.ofNat 152 (word80 [0x82c0a0b005842c0406,0x58442802b3120666666]))),((BitVec.ofNat 152 (word80 [0xf00000000000ffffff,0xfffff000134bf8f00ff0])),(BitVec.ofNat 152 (word80 [0x300c0c08608300808,0x6000304034828444444]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffff000000,0xcea8c5fff000])),(BitVec.ofNat 152 (word80 [0xc0301000800c03030,0x18088c084480c4888888]))),(0x0,0x0),(0x0,0x0)]
def g91C : List ColumnInfo := [(1,0,90,0,5)]
def g91A : List (List Nat) := [[],[48,100]]
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
theorem g91G : graphValid g91 (boundsBefore K61) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low91 : Lower true (varsX 91) (graphGoal 91) 6 := lower_forest (g:=g91) (i:=0) (hints:=16777283) (before_sound K61 V61) g91G g91T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K91 := extendKnown K61 6 [(91,[]),(109,[32,16,99,84]),(121,[64,81,33,99]),(181,[32,65,16,83,112,96]),(229,[97,33,83,116])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V91 : Known true K91 := extend_ok (m:=91) V61 low91 (by decide +kernel)
def g93Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffe003ff80ffc07fff,0xfffffffffffcaf0d003f])),(BitVec.ofNat 152 (word80 [0x150280502008140a8,0x15010080806407095b6d]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffc0000fffffff0,0x1ff80ffc0618ade01c0])),(BitVec.ofNat 152 (word80 [0x558531562c55140ac3,0x584a1a290b418ace36db]))),((BitVec.ofNat 152 (word80 [0xffffffffff00007fff,0xfe0000ffff9f8a238e07])),(BitVec.ofNat 152 (word80 [0x660641984866261302,0x606c2c3212198822a492]))),((BitVec.ofNat 152 (word80 [0x7fff,0xffffff000009f56c7038])),(BitVec.ofNat 152 (word80 [0x780781e07078381c03,0x8070303c1c09e0642492]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffff8000,0x6754f2ffc0])),(BitVec.ofNat 152 (word80 [0x80180200008000600c,0x18040c0202614104924]))),(0x0,0x0),(0x0,0x0)]
def g93C : List ColumnInfo := [(8,0,85,0,4)]
def g93A : List (List Nat) := [[],[67]]
def g93D4 (j : Nat) := if j=0 then 0x3f else 0
def g93L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g93D4)
  | _ => emptyPacking
def g93I (_ _ : Nat) : Option (Nat × Nat) := none
def g93 : Forest := ⟨93,4,fun i => g93Y[i]?.getD (0,0),g93C,g93A,g93L,g93I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g93P4_0 : block g93 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g93B4 : block g93 4 0 1=true := g93P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g93T : checkedTables g93 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g93 0 0 0 = true)
  · exact (rfl : block g93 1 0 0 = true)
  · exact (rfl : block g93 2 0 0 = true)
  · exact (rfl : block g93 3 0 0 = true)
  · exact g93B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g93G : graphValid g93 (boundsBefore K91) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low93 : Lower true (varsX 93) (graphGoal 93) 5 := lower_forest (g:=g93) (i:=0) (hints:=33555971) (before_sound K91 V91) g93G g93T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K93 := extendKnown K91 5 [(93,[]),(110,[80,16,33,50,67]),(124,[80,16,66,50]),(167,[80,49,33,32,66,118]),(174,[80,16,33,50,67,118]),(188,[80,16,66,50,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V93 : Known true K93 := extend_ok (m:=93) V91 low93 (by decide +kernel)
def g94Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0x3ffc003ffc01ffe00f,0xfffffffffffeddea003f])),(BitVec.ofNat 152 (word80 [0x80a81a8128340a4160,0xa02a094148524c6a1249]))),((BitVec.ofNat 152 (word80 [0x3fffffc00001fffff0,0x7ff001ffc0118f681c0])),(BitVec.ofNat 152 (word80 [0x15315315b158ac8a45,0x314c6d89919918f6b6db]))),((BitVec.ofNat 152 (word80 [0x3ffffffffffe000000,0x7ffffe000031f070e00])),(BitVec.ofNat 152 (word80 [0x19c19c19c260cf1389,0xc2704e0de2e31f0736db]))),((BitVec.ofNat 152 (word80 [0xc00000000000000000,0x7fffffffffcbfdc7007])),(BitVec.ofNat 152 (word80 [0x1e01e01e0380f01c0e,0x380700e0300b3942492]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffffffff,0xf800000000036237fff8])),(BitVec.ofNat 152 (word80 [0x200200200001000000,0x4008010000000004924]))),(0x0,0x0),(0x0,0x0)]
def g94C : List ColumnInfo := [(4,0,90,0,5)]
def g94A : List (List Nat) := [[],[50],[65],[65,50]]
def g94D5 (j : Nat) := if j=0 then 0x3f else 0
def g94L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g94D5)
  | _ => emptyPacking
def g94I (_ _ : Nat) : Option (Nat × Nat) := none
def g94 : Forest := ⟨94,5,fun i => g94Y[i]?.getD (0,0),g94C,g94A,g94L,g94I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g94P5_0 : block g94 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g94B5 : block g94 5 0 1=true := g94P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g94T : checkedTables g94 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g94 0 0 0 = true)
  · exact (rfl : block g94 1 0 0 = true)
  · exact (rfl : block g94 2 0 0 = true)
  · exact (rfl : block g94 3 0 0 = true)
  · exact (rfl : block g94 4 0 0 = true)
  · exact g94B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g94G : graphValid g94 (boundsBefore K93) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low94 : Lower true (varsX 94) (graphGoal 94) 6 := lower_forest (g:=g94) (i:=0) (hints:=16868928) (before_sound K93 V93) g94G g94T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K94 := extendKnown K93 6 [(94,[]),(143,[64,16,33,50,118]),(158,[118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V94 : Known true K94 := extend_ok (m:=94) V93 low94 (by decide +kernel)
def g117Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xf003ff0ff87ff007ff,0xff87fffcd47c560003ff])),(BitVec.ofNat 152 (word80 [0xa4280a201120a45214,0x81102080501c1694a529]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffc000ffffffff801,0xfff87fc35353a20ffc00])),(BitVec.ofNat 152 (word80 [0xc0302c40a002c06058,0xa01010a425122318c63]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffff0007ffffffe,0x7ffcafd11df0001f])),(BitVec.ofNat 152 (word80 [0x140b002c20b008060,0x2c220a00a741086318c6]))),((BitVec.ofNat 152 (word80 [0x7fffffff,0xffff80004d2fe8007fe0])),(BitVec.ofNat 152 (word80 [0x982c08b044c090481,0x30004c100d22c94a5294]))),((BitVec.ofNat 152 (word80 [0xffffffffff80000000,0x33aa61bff8000])),(BitVec.ofNat 152 (word80 [0xe03000c00700e0701,0xc044702118a6118c6318]))),(0x0,0x0),(0x0,0x0)]
def g117C : List ColumnInfo := [(1,0,116,0,4),(4,0,113,0,4),(16,0,101,0,4),(32,0,85,0,4),(64,0,53,0,4)]
def g117A : List (List Nat) := [[],[98,84],[32,100],[32,64,80,96],[64,101],[64,82,96,32],[80,66],[80,98,64,66],[96,32,66,84],[96,82]]
def g117D4 (j : Nat) := if j=0 then 0x57d4d10 else 0
def g117D5 (j : Nat) := if j=0 then 0xc1a0fd20fd10 else 0
def g117H5 (j : Nat) := if j=0 then 0x90 else 0
def g117D6 (j : Nat) := if j=0 then 0x23440bf else 0
def g117H6 := limbs80 #[#[0x4a210000003bb0000000,0x0,0xeb7a300009200000016,0x6500]]
def g117L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g117D4)
  | 5 => (2,1,3,0,0,4,0,g117D5)
  | 6 => (1,0,3,0,0,0,0,g117D6)
  | _ => emptyPacking
def g117I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 4 0 0 g117H5
  | 6 => lookupWord 2 37 0 8 1 3 g117H6
  | _ => fun _ => none
def g117 : Forest := ⟨117,6,fun i => g117Y[i]?.getD (0,0),g117C,g117A,g117L,g117I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g117P4_0 : block g117 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g117B4 : block g117 4 0 1=true := g117P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g117P5_0 : block g117 5 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g117B5 : block g117 5 0 2=true := g117P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g117P6_0 : block g117 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g117B6 : block g117 6 0 1=true := g117P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g117T : checkedTables g117 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g117 0 0 0 = true)
  · exact (rfl : block g117 1 0 0 = true)
  · exact (rfl : block g117 2 0 0 = true)
  · exact (rfl : block g117 3 0 0 = true)
  · exact g117B4
  · exact g117B5
  · exact g117B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g117G : graphValid g117 (boundsBefore K94) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low117 : Lower true (varsX 117) (graphGoal 117) 7 := lower_forest (g:=g117) (i:=0) (hints:=33555716) (before_sound K94 V94) g117G g117T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K117 := extendKnown K94 7 [(117,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V117 : Known true K117 := extend_ok (m:=117) V94 low117 (by decide +kernel)
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
theorem g151G : graphValid g151 (boundsBefore K117) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low151 : Lower true (varsX 151) (graphGoal 151) 6 := lower_forest (g:=g151) (i:=0) (hints:=1860) (before_sound K117 V117) g151G g151T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K151 := extendKnown K117 6 [(151,[]),(157,[48,65,16])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V151 : Known true K151 := extend_ok (m:=151) V117 low151 (by decide +kernel)
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
def K155 := extendKnown K151 7 [(155,[]),(185,[48,65,33,80,114,32]),(203,[96,16,49,67,84]),(205,[96,16,33,50,67,84]),(213,[96,16,33,50,83]),(233,[112,81,33,99,64,67])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V155 : Known true K155 := extend_ok (m:=155) V151 low155 (by decide +kernel)
def g171Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xff007fe1ff0fffc03f,0xf0ffffffe85e1a00f0ff])),(BitVec.ofNat 152 (word80 [0xa0501440220028280,0xa2020020880612111111]))),((BitVec.ofNat 152 (word80 [0xffff8001fff0ffffc0,0xff0ff00c35f90f0000])),(BitVec.ofNat 152 (word80 [0xac26158854022b030a,0xc41422420835b9777777]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffe0000ffffff,0xff000fff33b526f00f0f])),(BitVec.ofNat 152 (word80 [0x3008060018440c0403,0x184080303104222222]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffff,0xfffff000134bf8000ff0])),(BitVec.ofNat 152 (word80 [0xc0b058116088b0282c,0xa00b040348e8cccccc]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffff000000,0xcea8c5fff000])),(BitVec.ofNat 152 (word80 [0xc060018000c03030,0x8c08c08468840888888]))),(0x0,0x0)]
def g171C : List ColumnInfo := [(0,2,41,128,5),(2,0,169,0,5),(32,0,139,0,5),(1,0,170,0,4),(8,0,163,0,4),(128,2,41,0,4)]
def g171A : List (List Nat) := [[],[48]]
def g171D4 (j : Nat) := if j=0 then 0x57d4d20 else 0
def g171D5 (j : Nat) := if j=0 then 0xc8404fd20 else 0
def g171H5 (j : Nat) := if j=0 then 0xa else 0
def g171D6 (j : Nat) := if j=0 then 0x232a8bf else 0
def g171H6 (j : Nat) := if j=0 then 0x8 else 0
def g171L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g171D4)
  | 5 => (1,1,3,0,0,0,0,g171D5)
  | 6 => (1,0,3,0,0,0,0,g171D6)
  | _ => emptyPacking
def g171I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 4 0 0 g171H5
  | 6 => lookupWord 1 2 0 4 0 0 g171H6
  | _ => fun _ => none
def g171 : Forest := ⟨171,6,fun i => g171Y[i]?.getD (0,0),g171C,g171A,g171L,g171I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g171P4_0 : block g171 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g171B4 : block g171 4 0 1=true := g171P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g171P5_0 : block g171 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g171B5 : block g171 5 0 1=true := g171P5_0
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
  · exact g171B4
  · exact g171B5
  · exact g171B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g171G : graphValid g171 (boundsBefore K155) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low171 : Lower true (varsX 171) (graphGoal 171) 7 := lower_forest (g:=g171) (i:=0) (hints:=115) (before_sound K155 V155) g171G g171T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K171 := extendKnown K155 7 [(171,[]),(179,[64,81,115,48]),(234,[96,81,32,115,66]),(241,[64,81,33,115,32,96,48]),(244,[96,81,32,115,65,50]),(248,[96,81,32,115,65])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V171 : Known true K171 := extend_ok (m:=171) V155 low171 (by decide +kernel)
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
theorem g173G : graphValid g173 (boundsBefore K171) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low173 : Lower true (varsX 173) (graphGoal 173) 6 := lower_forest (g:=g173) (i:=0) (hints:=1283) (before_sound K171 V171) g173G g173T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K173 := extendKnown K171 6 [(173,[]),(236,[96,16,82,115,65])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V173 : Known true K173 := extend_ok (m:=173) V171 low173 (by decide +kernel)
def g211Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfe3fc03fc3f8ffe0,0x1fc7e7f1f53c000f000f])),(BitVec.ofNat 152 (word80 [0x4a1492929289120949,0x42905224353c55555555]))),((BitVec.ofNat 152 (word80 [0xff003fffc003ff1fff,0xe007fffe127b00f00ff0])),(BitVec.ofNat 152 (word80 [0xc1903030310204181,0x83208040807b11111111]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x3ffffffc001fff,0xfff807ffc5a10f00f0ff])),(BitVec.ofNat 152 (word80 [0x102004040400400202,0x4010080000022222222]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffc0000000001fff,0xfffff8003bc8f000ff00])),(BitVec.ofNat 152 (word80 [0x604018181821848c0c,0x80203093b8044444444]))),((BitVec.ofNat 152 (word80 [0xffffffffffffffe000,0x2816ffff0000])),(BitVec.ofNat 152 (word80 [0x808020202002001010,0x10040400000088888888]))),(0x0,0x0)]
def g211C : List ColumnInfo := [(1,0,210,0,7)]
def g211A : List (List Nat) := [[],[116],[97],[97,116]]
def g211D7 (j : Nat) := if j=0 then 0x3f else 0
def g211L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g211D7)
  | _ => emptyPacking
def g211I (_ _ : Nat) : Option (Nat × Nat) := none
def g211 : Forest := ⟨211,7,fun i => g211Y[i]?.getD (0,0),g211C,g211A,g211L,g211I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g211P7_0 : block g211 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g211B7 : block g211 7 0 1=true := g211P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g211T : checkedTables g211 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g211 0 0 0 = true)
  · exact (rfl : block g211 1 0 0 = true)
  · exact (rfl : block g211 2 0 0 = true)
  · exact (rfl : block g211 3 0 0 = true)
  · exact (rfl : block g211 4 0 0 = true)
  · exact (rfl : block g211 5 0 0 = true)
  · exact (rfl : block g211 6 0 0 = true)
  · exact g211B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g211G : graphValid g211 (boundsBefore K173) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low211 : Lower true (varsX 211) (graphGoal 211) 8 := lower_forest (g:=g211) (i:=0) (hints:=16777284) (before_sound K173 V173) g211G g211T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K211 := extendKnown K173 8 [(211,[]),(214,[32,100]),(218,[48,32,100])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V211 : Known true K211 := extend_ok (m:=211) V173 low211 (by decide +kernel)
def g217Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfe1fe03fc3fc3ffc,0x7f1fc7ffed2d400703f])),(BitVec.ofNat 152 (word80 [0x420448489089088109,0x10240922021254492492]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xff001fffc003ffc3ff,0xf801ffff1dd9250381c7])),(BitVec.ofNat 152 (word80 [0x142882810510500850,0x2148500441c121249249]))),((BitVec.ofNat 152 (word80 [0x1ffffffc0003ff,0xfffe007fe064f31c0e38])),(BitVec.ofNat 152 (word80 [0x183103020600611060,0x418062080864a1249249]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffe00000000003ff,0xffffff80003b4be00fc0])),(BitVec.ofNat 152 (word80 [0x60400c0c1821822181,0x82008030901a4a492492]))),((BitVec.ofNat 152 (word80 [0xfffffffffffffffc00,0x30628fff000])),(BitVec.ofNat 152 (word80 [0x808010102002000202,0x4010040000000924924]))),(0x0,0x0)]
def g217C : List ColumnInfo := [(1,0,216,0,5)]
def g217A : List (List Nat) := [[],[67],[48,100],[48,96,64],[64,48,99],[64,99],[96],[96,67]]
def g217D5 (j : Nat) := if j=0 then 0x3f else 0
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
theorem g217G : graphValid g217 (boundsBefore K211) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low217 : Lower true (varsX 217) (graphGoal 217) 6 := lower_forest (g:=g217) (i:=0) (hints:=50331651) (before_sound K211 V211) g217G g217T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K217 := extendKnown K211 6 [(217,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V217 : Known true K217 := extend_ok (m:=217) V211 low217 (by decide +kernel)
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
theorem g63G : graphValid g63 (boundsBefore K217) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low63 : Lower true (varsX 63) (graphGoal 63) 8 := lower_forest (g:=g63) (i:=0) (hints:=1347) (before_sound K217 V217) g63G g63T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K63 := extendKnown K217 8 [(63,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V63 : Known true K63 := extend_ok (m:=63) V217 low63 (by decide +kernel)
def g95Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3ffffffffffffffff,0xfd92ba36075cb00000ff])),(BitVec.ofNat 152 (word80 [0x5805200aa012a01480,0x5192a8340448a9999999]))),((BitVec.ofNat 152 (word80 [0xfc003fffc0003fffc0,0x3ed0aa07c1b2000ff00])),(BitVec.ofNat 152 (word80 [0x9029805300db009901,0x9ba50aa0641a03333333]))),((BitVec.ofNat 152 (word80 [0x3fffffffc00000,0x738dada715000f0000])),(BitVec.ofNat 152 (word80 [0xe0ce0a9c0a9c0ade0a,0xe0638daca71507777777]))),((BitVec.ofNat 152 (word80 [0x3fffffffffffff,0xfc85179417b3d0f0000f])),(BitVec.ofNat 152 (word80 [0x1700ce00ce00ce013,0x5178013b316666666]))),((BitVec.ofNat 152 (word80 [0xffffc0000000000000,0x45f462f96d0f000ff0])),(BitVec.ofNat 152 (word80 [0x1800f000f000f001c,0x401442992504444444]))),(0x0,0x0),(0x33a4dd980e26ffff000,(BitVec.ofNat 152 (word80 [0x20030003000300020,0x184011004068888888]))),(0x0,0x0),(0x0,0x0)]
def g95C : List ColumnInfo := [(1,0,94,0,6),(4,0,91,0,6),(8,0,87,0,6),(2,0,93,0,5),(12,0,83,0,5),(18,0,77,0,4),(20,0,75,0,4),(64,0,27,0,4),(64,4,27,0,4)]
def g95A : List (List Nat) := [[]]
def g95D4 := limbs80 #[#[0xa6c3b286a87195450d50,0x9cee2b26a5a359143d4,0x930c]]
def g95D5 := limbs80 #[#[0xe55150f6d8d50f650d50,0x59352f350f52bb58752d,0x5143f358943f6d8143bb,0x21e3030300bdd8554e75,0x800000080400274260a9,0x4c11300]]
def g95H5 (j : Nat) := if j=0 then 0xaeed00000f40 else 0
def g95D6 := limbs80 #[#[0xd43f7a97b50bda43f950,0xbaa44686807f553faa3d,0x232029410510128a04fd,0xc280c280851814491c]]
def g95H6 := limbs80 #[#[0xa0000144000000dbc002,0x3e4000000014c000001,0x14800000295100000,0x5c]]
def g95D7 (j : Nat) := if j=0 then 0x8502117f else 0
def g95H7 (j : Nat) := if j=0 then 0xab675ac03199 else 0
def g95L : Nat → Packing
  | 4 => (4,3,4,0,0,5,0,g95D4)
  | 5 => (10,2,4,0,0,7,0,g95D5)
  | 6 => (7,1,4,0,0,7,0,g95D6)
  | 7 => (1,0,4,0,0,0,0,g95D7)
  | _ => emptyPacking
def g95I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 11 0 6 2 0 g95H5
  | 6 => lookupWord 2 37 1 8 4 0 g95H6
  | 7 => lookupWord 1 11 0 7 3 0 g95H7
  | _ => fun _ => none
def g95 : Forest := ⟨95,7,fun i => g95Y[i]?.getD (0,0),g95C,g95A,g95L,g95I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P4_0 : block g95 4 0 4=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g95B4 : block g95 4 0 4=true := g95P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P5_0 : block g95 5 0 10=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g95B5 : block g95 5 0 10=true := g95P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P6_0 : block g95 6 0 5=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P6_5 : block g95 6 5 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g95B6 : block g95 6 0 7=true := (@block_merge g95 6 0 5 2 g95P6_0 g95P6_5)
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
  · exact g95B4
  · exact g95B5
  · exact g95B6
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
def g111Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfffffffffffffffffe,0xc9353b270a58000003ff])),(BitVec.ofNat 152 (word80 [0x481440548129029028,0xc9143a2202525294a529]))),((BitVec.ofNat 152 (word80 [0xfc00fffe0003fff801,0xf405507ea99001f00000])),(BitVec.ofNat 152 (word80 [0x90a612982db05320cd,0xf005503ea981ce739ce7]))),((BitVec.ofNat 152 (word80 [0xfffffffc000000,0x39c4d6931e803e007c00])),(BitVec.ofNat 152 (word80 [0xe13804e009c01bc170,0x1184d6130e80c6318c63]))),((BitVec.ofNat 152 (word80 [0xfffffffffffffe,0x428bca0bc9efc00f801f])),(BitVec.ofNat 152 (word80 [0x1c007000e001c0180,0x89c009498884210842]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffff00000000000000,0x22fa317cb680000fffe0])),(BitVec.ofNat 152 (word80 [0x98013002600200,0x22620144b005294a5294]))),((BitVec.ofNat 152 (word80 [1,0x9d26ecc07137fff00000])),(BitVec.ofNat 152 (word80 [0x200e001c003800400,0xc2228c01036318c6318]))),(0x0,0x0),(0x0,0x0)]
def g111C : List ColumnInfo := [(4,0,107,0,7)]
def g111A : List (List Nat) := [[]]
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
theorem low111 : Lower true (varsX 111) (graphGoal 111) 8 := lower_forest (g:=g111) (i:=0) (hints:=16778595) (before_sound K95 V95) g111G g111T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K111 := extendKnown K95 8 [(111,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V111 : Known true K111 := extend_ok (m:=111) V95 low111 (by decide +kernel)
def g119Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xf8001fffffff00ff1d,0x203397a2ac000003f03f])),(BitVec.ofNat 152 (word80 [0x520d4825205216141d,0x2390a2a91451451451]))),((BitVec.ofNat 152 (word80 [0xffffe0007fffff0063,0x7e8b807608003f000fc0])),(BitVec.ofNat 152 (word80 [0x604981360464242623,0x36098066085145145145]))),((BitVec.ofNat 152 (word80 [0xffffffff800000009d,0x8e48e9a5400fc0fc0000])),(BitVec.ofNat 152 (word80 [0x800e00380178383815,0xa48c1a54030c30c30c3]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffffffa0,0x49c585ccf7f000000fff])),(BitVec.ofNat 152 (word80 [0x9002400980000080,0x48c0050854a28a28a28a]))),((BitVec.ofNat 152 (word80 [0x91,0x75383e5b400000fff000])),(BitVec.ofNat 152 (word80 [0x4e013804e00404080,0x75102e5802cb2cb2cb2c]))),((BitVec.ofNat 152 (word80 [0x4e,0x937660389bffff000000])),(BitVec.ofNat 152 (word80 [0x7001c007000808048,0x81362010830c30c30c30]))),(0x0,0x0),(0x0,0x0)]
def g119C : List ColumnInfo := [(1,0,118,0,7),(2,0,117,0,7),(4,0,115,0,7),(0,32,82,5,6),(32,0,87,0,6),(16,0,103,0,5),(64,0,55,0,5)]
def g119A : List (List Nat) := [[],[32,100]]
def g119D5 (j : Nat) := if j=0 then 0x4f77159653 else 0
def g119D6 := limbs80 #[#[0xdd8553bd58453be58053,0x59653fdd8553d7d4e53b,0x4018a1141f3185b2c0bf,0x41082628]]
def g119H6 (j : Nat) := if j=0 then 0x5 else 0
def g119D7 := limbs80 #[#[0x47888807f94ffaa7fc53,0x2a5474365a891d90ea61,0x190e]]
def g119H7 := limbs80 #[#[0xf400d100009300000065,0x3268f00000000000]]
def g119D8 (j : Nat) := if j=0 then 0x468817f else 0
def g119H8 (j : Nat) := if j=0 then 0xc1980000007900 else 0
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
def g123Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffffff83fffff242eb,0xcf4680000000fe03fff])),(BitVec.ofNat 152 (word80 [0x80a4010808040240a2,0xc444842850a142850a1]))),((BitVec.ofNat 152 (word80 [0xffffc1ffe06b588,0x5cbc60003f8001fc000])),(BitVec.ofNat 152 (word80 [0x12c08a00410822b188,0x58b40162c58b162c58b]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfff000001ffffbd84c,0x93211a01fc07f000007f])),(BitVec.ofNat 152 (word80 [0x3002c10805001804c,0x1121120c183060c18306]))),((BitVec.ofNat 152 (word80 [0xffffffffe0000804f4,0x691ab3fe0000001fff80])),(BitVec.ofNat 152 (word80 [0x240130000260480444,0x2010b32850a142850a14]))),((BitVec.ofNat 152 (word80 [0x91713,0xa28774000007ffe00000])),(BitVec.ofNat 152 (word80 [0x3809c0211380881711,0xa28224b162c58b162c58]))),((BitVec.ofNat 152 (word80 [0x4e917,0x7e4005fffff800000000])),(BitVec.ofNat 152 (word80 [0xc00e00421c01044813,0x4a4004c183060c183060]))),(0x0,0x0),(0x0,0x0)]
def g123C : List ColumnInfo := [(1,0,122,0,7),(8,0,115,0,7),(16,0,107,0,7),(64,0,59,0,7),(0,2,41,80,6),(2,0,121,0,6)]
def g123A : List (List Nat) := [[],[48,100],[64,81,99],[96,81,67]]
def g123D8 (j : Nat) := if j=0 then 0x2c6881bf else 0
def g123L : Nat → Packing
  | 8 => (1,0,3,0,0,0,0,g123D8)
  | _ => emptyPacking
def g123I (_ _ : Nat) : Option (Nat × Nat) := none
def g123 : Forest := ⟨123,8,fun i => g123Y[i]?.getD (0,0),g123C,g123A,g123L,g123I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P8_0 : block g123 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g123B8 : block g123 8 0 1=true := g123P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123T : checkedTables g123 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g123 0 0 0 = true)
  · exact (rfl : block g123 1 0 0 = true)
  · exact (rfl : block g123 2 0 0 = true)
  · exact (rfl : block g123 3 0 0 = true)
  · exact (rfl : block g123 4 0 0 = true)
  · exact (rfl : block g123 5 0 0 = true)
  · exact (rfl : block g123 6 0 0 = true)
  · exact (rfl : block g123 7 0 0 = true)
  · exact g123B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123G : graphValid g123 (boundsBefore K119) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low123 : Lower true (varsX 123) (graphGoal 123) 9 := lower_forest (g:=g123) (i:=0) (hints:=16777283) (before_sound K119 V119) g123G g123T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K123 := extendKnown K119 9 [(123,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V123 : Known true K123 := extend_ok (m:=123) V119 low123 (by decide +kernel)
def g125Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfffffffffffffffff6,0x9e94539ca0000007fff])),(BitVec.ofNat 152 (word80 [0xa402900400802006,0x8214508484a5294a529]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfff0003ffe01fff00e,0x724a8c0cf4003e0f8000])),(BitVec.ofNat 152 (word80 [0xac06b0128340a416e,0x504a880cd018c6318c63]))),((BitVec.ofNat 152 (word80 [0xffffffc00001fffff3,0x4cce92e21807c1f0001f])),(BitVec.ofNat 152 (word80 [0x13004c01b0580c8240,0x40ce80e2101084210842]))),((BitVec.ofNat 152 (word80 [0xfffffffffffe000000,0x94f6681bb1f8000003e0])),(BitVec.ofNat 152 (word80 [0x5c017005c0602f0380,0x94c62813b0318c6318c6]))),((BitVec.ofNat 152 (word80 [1,0x1711a387760001fffc00])),(BitVec.ofNat 152 (word80 [0x600980260081300401,0x710220126a5294a5294]))),((BitVec.ofNat 152 (word80 [0xc,0xe9177e4005fffe000000])),(BitVec.ofNat 152 (word80 [0x800e00380101c00800,0x2911560005c6318c6318]))),(0x0,0x0),(0x0,0x0)]
def g125C : List ColumnInfo := [(8,0,117,0,7),(4,0,121,0,6),(16,0,109,0,6),(64,0,61,0,6),(1,0,124,0,5),(20,0,105,0,5),(32,0,93,0,5),(68,0,57,0,5),(80,0,45,0,5),(5,0,120,0,4),(9,0,116,0,4),(48,0,77,0,4)]
def g125A : List (List Nat) := [[],[80,66]]
def g125D4 := limbs80 #[#[0x589501038c5516154040,0x30e2954]]
def g125D5 := limbs80 #[#[0x374b12a0206f16154040,0xe72a8a8081b658d5010,0x277b92caa04f7715954,0x809bee6b2c816edc1549,0xaa479848c1]]
def g125H5 (j : Nat) := if j=0 then 0x40bd else 0
def g125D6 := limbs80 #[#[0xb58840bd584409f59610,0xd8d50eed02409f59440b,0x510fe50110bd58650b7,0x210fe50210bf59110fd5,0x40bf59230bfd9130bf59,0xbfd8540bf59440fe540,0xbf58e40bfd9540bf5954,0xf59240ef95240ef55240,0x55150f7d8d50bf59640b,0x1800bf59250bfd9150df,0x41147e39198b4421b090,0xf36180ba5a2a1449c4b2,0x19c4b229087e3d9e0e46,0x1300f0046282106c03c0,0x4041070070046,0xc10000810030000c10,0xc10c112244308108100]]
def g125H6 := limbs80 #[#[0x12c8801ae0742,0xf57201240020a3aa995c]]
def g125D7 := limbs80 #[#[0xc40ff187f4c3fc21fd10,0x1fe50fea87f903fa81f,0x1604e362280f85d1f07c,0x8582053160720a629e09,0x18411ae0918c58110298,0xf040a618a09146209890,0x19103905310]]
def g125H7 := limbs80 #[#[0x6000006c4ebaad400080,0x1550000078,0x20000000000000000000,0x8dc1c84584000000011,0xfb70000059ea20012680,0x180c52000c,0xea4b2898a2000000000,0xe0020f40001e2801c500,0x3000f80007a02c0072,0x15400000224002960000,0x8001c200000000000000,0x1a0000016d21]]
def g125D8 (j : Nat) := if j=0 then 0x875013f else 0
def g125H8 := limbs80 #[#[0x0,0x1570024000,0x0,0x182000,0x30060400000000000000,0x5c401d,0x0,0x0,0x2140000cc,0x61c0000000000000,0x2000000,0x8800000000000007c8,0x3d000000000000000,0x60000000000000001160,0x18300000012]]
def g125L : Nat → Packing
  | 4 => (2,4,4,0,0,3,0,g125D4)
  | 5 => (8,3,4,0,0,6,0,g125D5)
  | 6 => (28,2,4,0,0,9,0,g125D6)
  | 7 => (9,1,4,0,0,9,0,g125D7)
  | 8 => (1,0,4,0,0,0,0,g125D8)
  | _ => emptyPacking
def g125I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 3 0 6 1 1 g125H5
  | 6 => lookupWord 3 19 3 8 3 1 g125H6
  | 7 => lookupWord 9 97 3 10 5 1 g125H7
  | 8 => lookupWord 4 137 0 9 4 1 g125H8
  | _ => fun _ => none
def g125 : Forest := ⟨125,8,fun i => g125Y[i]?.getD (0,0),g125C,g125A,g125L,g125I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P4_0 : block g125 4 0 2=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g125B4 : block g125 4 0 2=true := g125P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P5_0 : block g125 5 0 8=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g125B5 : block g125 5 0 8=true := g125P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P6_0 : block g125 6 0 7=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P6_7 : block g125 6 7 21=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g125B6 : block g125 6 0 28=true := (@block_merge g125 6 0 7 21 g125P6_0 g125P6_7)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P7_0 : block g125 7 0 9=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g125B7 : block g125 7 0 9=true := g125P7_0
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
  · exact g125B4
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
def g126Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfc00fffffffffffffe,0xd62932b74a48000f801f])),(BitVec.ofNat 152 (word80 [0x481610542128429028,0x540832b642414a5294a5]))),((BitVec.ofNat 152 (word80 [0xfffffffe0003fff801,0x601555aee91001f003e0])),(BitVec.ofNat 152 (word80 [0x90a402980db01320cd,0x601550aa4910c6318c63]))),((BitVec.ofNat 152 (word80 [0xfffffffc000001,0x39c4d2534e803e007c00])),(BitVec.ofNat 152 (word80 [0xe13804e009c01bc171,0x3184d2034e00c6318c63]))),((BitVec.ofNat 152 (word80 [0xffffffffffffff,0x428bca0b99efc000001f])),(BitVec.ofNat 152 (word80 [0x1c027004e009c0181,0x281c00999aa94a5294a]))),((BitVec.ofNat 152 (word80 [0xffff00000000000001,0x22fa317cb68000007fe0])),(BitVec.ofNat 152 (word80 [0xb8017002e00200,0x26a2154b08739ce739c]))),(0x9d26ecc07137ffff8000,(BitVec.ofNat 152 (word80 [0x200c0018003000400,0x88220c40200421084210]))),(0x0,0x0),(0x0,0x0)]
def g126C : List ColumnInfo := [(4,0,122,0,7)]
def g126A : List (List Nat) := [[],[50],[65],[65,50]]
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
def K126 := extendKnown K125 8 [(126,[]),(190,[118])]
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
def K183 := extendKnown K175 9 [(183,[]),(231,[32,100])]
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
def K187 := extendKnown K183 10 [(187,[]),(235,[48,100])]
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
def K189 := extendKnown K187 8 [(189,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V189 : Known true K189 := extend_ok (m:=189) V187 low189 (by decide +kernel)
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
theorem g207G : graphValid g207 (boundsBefore K189) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low207 : Lower true (varsX 207) (graphGoal 207) 8 := lower_forest (g:=g207) (i:=0) (hints:=16778851) (before_sound K189 V189) g207G g207T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K207 := extendKnown K189 8 [(207,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V207 : Known true K207 := extend_ok (m:=207) V189 low207 (by decide +kernel)
def g215Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffc07ff800fffffe03,0xfecb2a2ba20000f0000f])),(BitVec.ofNat 152 (word80 [0x148b21526a4948a458,0xa6cb0a2aa25555555555]))),((BitVec.ofNat 152 (word80 [0xffffffffff001ffffc,0x34edb8091000f000ff0])),(BitVec.ofNat 152 (word80 [0x191202604c0d80c891,0x334e5a00111111111111]))),((BitVec.ofNat 152 (word80 [0x7fffffffe00000,0xd372d62500f000f000])),(BitVec.ofNat 152 (word80 [0x5e1c0b80700e02f0e1,0xc0c372d4253333333333]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x7fffffffffffff,0xf922299d6b0f000f00ff])),(BitVec.ofNat 152 (word80 [0x60200c008010030000,0x202195082222222222]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffff80000000000000,0x98c67ad8f0000fff00])),(BitVec.ofNat 152 (word80 [0x8000300300600c0102,0x10842ac04444444444]))),(0x665142404fffff00000,(BitVec.ofNat 152 (word80 [0x40040080100000,0x8888888888]))),(0x0,0x0)]
def g215C : List ColumnInfo := [(1,0,214,0,8)]
def g215A : List (List Nat) := [[],[32,100]]
def g215D8 (j : Nat) := if j=0 then 0x7f else 0
def g215L : Nat → Packing
  | 8 => (1,0,1,0,0,0,0,g215D8)
  | _ => emptyPacking
def g215I (_ _ : Nat) : Option (Nat × Nat) := none
def g215 : Forest := ⟨215,8,fun i => g215Y[i]?.getD (0,0),g215C,g215A,g215L,g215I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215P8_0 : block g215 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g215B8 : block g215 8 0 1=true := g215P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215T : checkedTables g215 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g215 0 0 0 = true)
  · exact (rfl : block g215 1 0 0 = true)
  · exact (rfl : block g215 2 0 0 = true)
  · exact (rfl : block g215 3 0 0 = true)
  · exact (rfl : block g215 4 0 0 = true)
  · exact (rfl : block g215 5 0 0 = true)
  · exact (rfl : block g215 6 0 0 = true)
  · exact (rfl : block g215 7 0 0 = true)
  · exact g215B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215G : graphValid g215 (boundsBefore K207) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low215 : Lower true (varsX 215) (graphGoal 215) 9 := lower_forest (g:=g215) (i:=0) (hints:=16778820) (before_sound K207 V207) g215G g215T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K215 := extendKnown K207 9 [(215,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V215 : Known true K215 := extend_ok (m:=215) V207 low215 (by decide +kernel)
def g219Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x1ffc01ffffe1fffff4,0x934332000007c00003ff])),(BitVec.ofNat 152 (word80 [0x4829148520440820d4,0x13031225294a5294a529]))),((BitVec.ofNat 152 (word80 [0xfffffe007ffe1ff057,0x2c4b888000f8000ffc00])),(BitVec.ofNat 152 (word80 [0xb018160280404253,0xc4b080c6318c6318c63]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1fffffff80001fff28,0xf4695c001f0001f0001f])),(BitVec.ofNat 152 (word80 [0x82c020180b08828028,0xe4484c18c6318c6318c6]))),((BitVec.ofNat 152 (word80 [0x1fffffffffffe00010,0xaa846f83e0003e007fe0])),(BitVec.ofNat 152 (word80 [0x30040200c00030400,0xa0046590842108421084]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xe0000000000000000e,0x11ba877c00003fff8000])),(BitVec.ofNat 152 (word80 [0xc0180c030110c0804,0x11b08221084210842108]))),((BitVec.ofNat 152 (word80 [0xc1,0x4514407fffffc0000000])),(BitVec.ofNat 152 (word80 [0x100201004000100000,0x42108421084210]))),(0x0,0x0)]
def g219C : List ColumnInfo := [(1,0,218,0,8),(8,0,211,0,8),(9,0,210,0,7),(16,0,203,0,7),(64,0,155,0,7),(2,0,217,0,6),(128,0,91,0,6),(3,0,216,0,5),(17,0,202,0,5),(18,0,201,0,5),(24,0,195,0,5),(65,0,154,0,5),(66,0,153,0,5),(72,0,147,0,5),(80,0,139,0,5),(129,0,90,0,5),(25,0,194,0,4),(73,0,146,0,4),(82,0,137,0,4),(144,0,75,0,4),(192,0,27,0,4)]
def g219A : List (List Nat) := [[],[48,100]]
def g219D4 := limbs80 #[#[0x9928158b97595434c940,0x8550d325027133132a86,0x85caae8a9a64a06e0e45,0x928170994995534c940b,0x654d3250271728c32a69,0x81c6564cb0c04e26538,0x328200000ca08ca]]
def g219D5 := limbs80 #[#[0x54d32502e2615434c940,0x502ece056590540f0954,0x6066590540bab8259641,0x545409b98799641502ec,0x9eb825d951503cc55161,0x5d95150276e0d7654540,0x5026e61376545409bb84,0xdd554585409eb825db51,0x4c940f896550d325034e,0xf895454d32503e299543,0x54d32503e25d1534c940,0x503d2595534c940f8984,0x619534c940f4a6554d32,0x4c940bcb8654d32502f2,0xbcb8558d32503b259563,0x995325027ae1d654c940,0x502ea612654c940bc983,0x9955350d40f196554d43,0x50d40bab8259543503c6,0xb998399543502e6e0d65,0x5d5435026e61e6550d40,0x503c65516354d40db381,0x6126554d40e596558d53,0x54d409f3815d953502ce,0x9bb845d9535027ae0976,0x5db535026e6137654d40,0x5034edd55458d409eb82,0x60f7259540bb3815cd54,0x8a2d138843615078027a,0xa13281391b0cc572892c,0x7ca63514873d9e0d8602,0xb8d8ab956a852a77359],#[0x1c2de6b74fa1cde571f8,0x3210200000000240f3b9,0x88c21502000000400001,0x4103852103454148c125,0x402000651084013c5,0x89411282000000230400,0x941000000004c0]]
def g219H5 := limbs80 #[#[0x3d0578c025808c26c030,0xc40]]
def g219D6 := limbs80 #[#[0x3d8a8c82a0789434c940,0xe72a8a8a816e5d64150,0x39caa6a2a05bb745454,0x40f92a6992816e5d3515,0x503cca9a86a07c9634c9,0xd40e72a8a9a816e5d543,0x4502dcba6a6a073954d4,0x9540bd6e4b2a816edcd5,0x5350faaa9aa298db9749,0x905409eee2b2a87c7551,0x551503dd32c82a07b965,0x454540f72a8a8a81fc58,0xd951502fcbb2a2a07bb7,0x5458540bf2eda8a817ed,0xdd5615037cb2ac2a07b9,0xa654c940fd2ca992817e,0xe59543503f4bb264a07e,0xd96354d40f74caa1a81e,0xee5d153503dcaa2a6a07,0x77a6554d40ef2caa9a81,0x17edd953502fcbb2a6a0,0x5f976d4d40ef2cba9a8,0x81be59563503dcaa2c6a,0xa07b97155140bf6eab1a,0xa817edc565503dcb9aa8,0xaa05fb7359540fd6e4b2,0x8a637e5ce65502fcb8cc,0xca98fd77354531faaa6a,0xa9aa3b7d8d535476fb9a,0xacaa1f9d5454d43ebec6,0x260017ddc56454f7bb8,0x62303e86a0ae1201a826],#[0x80888fe1d6360628b214,0xc89822ee590ac9462664,0x9de39e700da9b234e670,0x246e8b110a0e3fe7d0f4,0xfe9d136a6a4be97128a4,0xb3160ab654ea814aa8e4,0x182afe5eebc174ae25b6,0xa44824b2a12131a626c3,0xf844840be1290c502f84,0x2f849848400e1120c502,0x21700a848326e1001210,0x12102f844834b2a08821,0x61210502f844841400e1,0x1412109b84004840be12,0x50be114123f0310308e1,0x6e1e01213841b804842,0x2c9420b25610f13130c2,0x2254408989420726840c,0x30b26070c3c842008c84,0x3093ca8207040b118498,0xf0b61231046084034b2,0xe0e8c5020826082c8c2,0xc10094842003c8c21429,0x223042c209830f21083,0xf040850383030c04201,0x23041010f23210e3c842,0x60418100042410504181,0x1410]]
def g219H6 := limbs80 #[#[0x192158002cda0c493620,0x15210e00000242,0x6560000000,0x6a5d1a97001e88000000,0x28f80060a00193907000,0x4000500d3535dd113200,0x3c,0x53000001a0ac30,0xca00000000000000000,0x880003270470e00033,0x2368a0000000,0xe810000000051a000000,0xc764f00000082d47,0x2500000000000,0x52b680006160,0x74bf380048a000,0x270daa00000,0x1084000000000000,0x180c448]]
def g219D7 := limbs80 #[#[0xe50d40fa4c940ee90540,0x58c51be58051ee55140e,0x4540fe54540ddd4651b7,0xd40fe54d40fe58540fed,0x40fe59540fe58d40fed4,0x1f754d31fd54531fe995,0xbf59631fd54631bf5953,0xfd8d51dfd4d51df54d51,0x58f51df54f51bf59651b,0x8553bf59543f754d43bf,0x153dfd5153df55153bfd,0x51bf59353bf58753bfd9,0x3ffd8d51ff58d51ff54d,0xff59153ff55153ff5855,0xc330550880be1100d800,0x50f21bb3245a4a01171d,0x8baee598a8d40a5f47a8,0x40c7c6f05cfb7d6a8ce5,0xca1139a624a290117a17,0x2428bc2a43acd52e9bd1,0x592c228bc248343025aa,0x1860913086182448050,0xc0169b0921700618244c,0x1d30bc248517030a6242,0xb81853121600b4d8490a,0x518fc22c610985e12428,0xd80908951e116985809,0x293c380909849e024261,0x2170e086304278704318,0x90784360242130d8701,0xc0189081b0e018245c38,0x293c3809081b0e024261],#[0x21b06126484284f0e024,0x84c18431210a130d8701,0xc04840d8701213061264,0x8c3262420c1519310361,0x48e1219426193121060a,0x284c]]
def g219H7 := limbs80 #[#[0x840000231788d7c8081,0x708dc6ff1a08100b01a3,0xa33c471b27a8d7b2baa9,0x40012fd4d87aa4271b74,0x9f44f30c193043cd2d04,0xc95078000006c9c,0x260e12a16000000,0x60024a800c0000000000,0xa000a73cf95080029,0x1ddb679c6ad96800c1a0,0x30410aac2d732900109e,0x9d954c4006a40002a000,0x1cd62c1b1f001e80a371,0xa280030288ee5c00000a,0x6da5c5f0ff32518d7000,0x82c3c580000009dc3922,0x7020350ad98220000034,0x7]]
def g219D8 := limbs80 #[#[0xd51fe28ff8c7fa63f940,0xa7fd53fea1ffd47fca3f,0xecd85a258cc4212003fe,0x86048400b1214859f451,0xc63218091c60e084c146,0x41a180c2451a18121040,0x8604861a181212181218,0x38604861530c6]]
def g219H8 := limbs80 #[#[0xcd08b18d18b003281917,0x2307c9010800000a0924,0xaa04ef185ac84642d39a,0x7600029e816166eb000d,0x40005172921d04720230,0x28d7bc0031326273641,0xc48240748b70cc1e67c0,0x33400082454115225528,0xe00351800a3823b43348,0x5c8c800001d15b2000b8,0xe065200000000481887e,0x69589e00140000122001]]
def g219D9 (j : Nat) := if j=0 then 0x20c2013f else 0
def g219H9 := limbs80 #[#[0x1e60008cc,0x1e58a000000001e70061,0x44000000000000240000,0x40002b4a478000,0x980044000]]
def g219L : Nat → Packing
  | 4 => (7,5,5,0,0,6,0,g219D4)
  | 5 => (45,4,5,0,0,9,0,g219D5)
  | 6 => (63,3,5,0,0,11,0,g219D6)
  | 7 => (40,2,5,0,0,11,0,g219D7)
  | 8 => (10,1,5,0,0,9,0,g219D8)
  | 9 => (1,0,5,0,0,0,0,g219D9)
  | _ => emptyPacking
def g219I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 2 11 3 8 3 1 g219H5
  | 6 => lookupWord 12 131 2 11 6 1 g219H6
  | 7 => lookupWord 20 113 6 11 6 1 g219H7
  | 8 => lookupWord 15 79 6 11 6 1 g219H8
  | 9 => lookupWord 3 41 2 9 4 1 g219H9
  | _ => fun _ => none
def g219 : Forest := ⟨219,9,fun i => g219Y[i]?.getD (0,0),g219C,g219A,g219L,g219I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P4_0 : block g219 4 0 7=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g219B4 : block g219 4 0 7=true := g219P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P5_0 : block g219 5 0 2=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P5_2 : block g219 5 2 43=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g219B5 : block g219 5 0 45=true := (@block_merge g219 5 0 2 43 g219P5_0 g219P5_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P6_0 : block g219 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P6_1 : block g219 6 1 19=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P6_20 : block g219 6 20 43=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g219B6 : block g219 6 0 63=true := (@block_merge g219 6 0 1 62 g219P6_0 (@block_merge g219 6 1 19 43 g219P6_1 g219P6_20))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P7_0 : block g219 7 0 7=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P7_7 : block g219 7 7 27=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P7_34 : block g219 7 34 6=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g219B7 : block g219 7 0 40=true := (@block_merge g219 7 0 7 33 g219P7_0 (@block_merge g219 7 7 27 6 g219P7_7 g219P7_34))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P8_0 : block g219 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P8_1 : block g219 8 1 9=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g219B8 : block g219 8 0 10=true := (@block_merge g219 8 0 1 9 g219P8_0 g219P8_1)
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
  · exact g219B4
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
def g221Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffc07fffffffffffff,0xff8a29a1ab0000f000ff])),(BitVec.ofNat 152 (word80 [0x8120520520200808,0x78828208a5555555555]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffff8007ff01ffc,0x34fa116d1000f000f00])),(BitVec.ofNat 152 (word80 [0x55140560d609434290,0xb34f2116513333333333]))),((BitVec.ofNat 152 (word80 [0x7fffff80001fff,0xf9b301df0600f000f00f])),(BitVec.ofNat 152 (word80 [0x66260980980d858321,0x202301df042222222222]))),((BitVec.ofNat 152 (word80 [0x7fffffffffe000,0x627a9c690f000f00f0])),(BitVec.ofNat 152 (word80 [0x78380e00e00e0603c1,0xc062509c612222222222]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffff80000000000000,0x98c67ad8f0000fff00])),(BitVec.ofNat 152 (word80 [0x800030030030080c02,0x908620884444444444]))),(0x665142404fffff00000,(BitVec.ofNat 152 (word80 [0x40040040001000,0x8888888888]))),(0x0,0x0)]
def g221C : List ColumnInfo := [(8,0,213,0,7)]
def g221A : List (List Nat) := [[],[67]]
def g221D7 (j : Nat) := if j=0 then 0x7f else 0
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
theorem low221 : Lower true (varsX 221) (graphGoal 221) 8 := lower_forest (g:=g221) (i:=0) (hints:=33555971) (before_sound K219 V219) g221G g221T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K221 := extendKnown K219 8 [(221,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V221 : Known true K221 := extend_ok (m:=221) V219 low221 (by decide +kernel)
def g222Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1fff007ffffffffff,0xffd303fa730000f000ff])),(BitVec.ofNat 152 (word80 [0x340520b0500a812814,0x851103fa221111111111]))),((BitVec.ofNat 152 (word80 [0x1fffff803ffc003ff,0xc02c923f47000f000f00])),(BitVec.ofNat 152 (word80 [0x5856452298530db099,0x19ac923f473333333333]))),((BitVec.ofNat 152 (word80 [0xfe00000003fffffc00,0x1c2f8b5c00f000f000])),(BitVec.ofNat 152 (word80 [0x606789c4e09c09c0de,0x2e1c2f8b5c3333333333]))),((BitVec.ofNat 152 (word80 [0x3ffffffff,0xffe2e2a1fd0f000f000f])),(BitVec.ofNat 152 (word80 [0x80780e0700e00e00e0,0x3022e001dd2222222222]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffffc00000000,0x15d4020ef0000ffff0])),(BitVec.ofNat 152 (word80 [0x8000000100100100,0x4444444444]))),(0x28295d80fffff00000,(BitVec.ofNat 152 (word80 [0x10000000200200200,0x8888888888]))),(0x0,0x0)]
def g222C : List ColumnInfo := [(4,0,218,0,8)]
def g222A : List (List Nat) := [[],[118],[50],[50,118],[65],[65,118],[65,50],[65,50,118]]
def g222D8 (j : Nat) := if j=0 then 0x7f else 0
def g222L : Nat → Packing
  | 8 => (1,0,1,0,0,0,0,g222D8)
  | _ => emptyPacking
def g222I (_ _ : Nat) : Option (Nat × Nat) := none
def g222 : Forest := ⟨222,8,fun i => g222Y[i]?.getD (0,0),g222C,g222A,g222L,g222I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g222P8_0 : block g222 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g222B8 : block g222 8 0 1=true := g222P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g222T : checkedTables g222 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g222 0 0 0 = true)
  · exact (rfl : block g222 1 0 0 = true)
  · exact (rfl : block g222 2 0 0 = true)
  · exact (rfl : block g222 3 0 0 = true)
  · exact (rfl : block g222 4 0 0 = true)
  · exact (rfl : block g222 5 0 0 = true)
  · exact (rfl : block g222 6 0 0 = true)
  · exact (rfl : block g222 7 0 0 = true)
  · exact g222B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g222G : graphValid g222 (boundsBefore K221) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low222 : Lower true (varsX 222) (graphGoal 222) 9 := lower_forest (g:=g222) (i:=0) (hints:=285304384) (before_sound K221 V221) g222G g222T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K222 := extendKnown K221 9 [(222,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V222 : Known true K222 := extend_ok (m:=222) V221 low222 (by decide +kernel)
def g237Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x7ff83ff83ffffea8,0xc9432ca40007c00003ff])),(BitVec.ofNat 152 (word80 [0x450850841080210280,0xc8430884a5294a5294a5]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xff80003fffc1ff8195,0x6345909800f801f07c00])),(BitVec.ofNat 152 (word80 [0x6016100a004020995,0x614100106318c6318c63]))),((BitVec.ofNat 152 (word80 [0xffffffc00001fffcd7,0x853046441f003e0f801f])),(BitVec.ofNat 152 (word80 [0x8018000c108040055,0x5000440421084210842]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffffffe000021,0x2e5c7b200000000fffe0])),(BitVec.ofNat 152 (word80 [0x905200290001481020,0x21c732318c6318c6318]))),((BitVec.ofNat 152 (word80 [0x44,0x90bf89b3e0003ff00000])),(BitVec.ofNat 152 (word80 [0xe01c020e0210702000,0x80b689a18c6318c6318c]))),((BitVec.ofNat 152 (word80 [0x33a,0x528a034bffffc0000000])),(BitVec.ofNat 152 (word80 [0x600430042180402a,0x1208020a108421084210]))),(0x0,0x0)]
def g237C : List ColumnInfo := [(4,0,233,0,7),(32,0,205,0,7),(1,0,236,0,6),(64,0,173,0,6),(9,0,228,0,5),(40,0,197,0,5),(68,0,169,0,5),(132,0,105,0,5),(192,0,45,0,5),(12,0,225,0,4),(160,0,77,0,4)]
def g237A : List (List Nat) := [[],[96,82,115]]
def g237D5 := limbs80 #[#[0x7e2b92a690f455354921,0x2b2080d1816ddd16548]]
def g237D6 := limbs80 #[#[0x554d21f954921d754d50,0xf0f00fd59521fd59121f,0x213888c08560448266b4,0xe9843028c0c48]]
def g237H6 := limbs80 #[#[0x18400040019000000000,0x740000]]
def g237D7 := limbs80 #[#[0xf80fea97f543fa81f521,0x918208201388905a6e4,0x118208246082]]
def g237H7 := limbs80 #[#[0x3300000000e000f2,0xf40000009149000018]]
def g237D8 (j : Nat) := if j=0 then 0x841013f else 0
def g237H8 := limbs80 #[#[0x5000000000000000000,0x0,0x0,0x0,0x0,0x6200000000000000000,0x0,0x880000000000,0xcd829800]]
def g237L : Nat → Packing
  | 5 => (3,3,4,0,0,5,0,g237D5)
  | 6 => (5,2,4,0,0,7,0,g237D6)
  | 7 => (4,1,4,0,0,7,0,g237D7)
  | 8 => (1,0,4,0,0,0,0,g237D8)
  | _ => emptyPacking
def g237I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 17 0 7 2 1 g237H6
  | 7 => lookupWord 1 19 0 8 3 1 g237H7
  | 8 => lookupWord 1 97 0 7 2 1 g237H8
  | _ => fun _ => none
def g237 : Forest := ⟨237,8,fun i => g237Y[i]?.getD (0,0),g237C,g237A,g237L,g237I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P5_0 : block g237 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P5_1 : block g237 5 1 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g237B5 : block g237 5 0 3=true := (@block_merge g237 5 0 1 2 g237P5_0 g237P5_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P6_0 : block g237 6 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P6_3 : block g237 6 3 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g237B6 : block g237 6 0 5=true := (@block_merge g237 6 0 3 2 g237P6_0 g237P6_3)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P7_0 : block g237 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P7_1 : block g237 7 1 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g237B7 : block g237 7 0 4=true := (@block_merge g237 7 0 1 3 g237P7_0 g237P7_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P8_0 : block g237 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g237B8 : block g237 8 0 1=true := g237P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237T : checkedTables g237 8 := by
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
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237G : graphValid g237 (boundsBefore K222) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low237 : Lower true (varsX 237) (graphGoal 237) 9 := lower_forest (g:=g237) (i:=0) (hints:=33555715) (before_sound K222 V222) g237G g237T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K237 := extendKnown K222 9 [(237,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V237 : Known true K237 := extend_ok (m:=237) V222 low237 (by decide +kernel)
def g238Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffff8003ffc03ffc0,0x29c134d0ae6000f00f00])),(BitVec.ofNat 152 (word80 [0x1409505a8128681485,0xa94134908e4333333333]))),((BitVec.ofNat 152 (word80 [0xffffffc00003ffff,0xda59298254d00f00f00f])),(BitVec.ofNat 152 (word80 [0x2602601301b0b01909,0x1a41088054c111111111]))),((BitVec.ofNat 152 (word80 [0xfffffffffffc0000,0x7638c0d9940f00f00f0])),(BitVec.ofNat 152 (word80 [0x3803801c01c0c01e0e,0x3438c08904111111111]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffffff,0xc8137a47ab90000000ff])),(BitVec.ofNat 152 (word80 [0x40ac05602a0002a000,0x1072472b1eeeeeeeee]))),((BitVec.ofNat 152 (word80 [0xff0000000000000000,0x45c463c762f000fff00])),(BitVec.ofNat 152 (word80 [0x3001800c0100c010,0x41c0204202444444444]))),(0x33a4d3e0015ffff00000,(BitVec.ofNat 152 (word80 [0x80c006003002030020,0xa04160011888888888]))),(0x0,0x0)]
def g238C : List ColumnInfo := [(4,0,234,0,7)]
def g238A : List (List Nat) := [[],[118],[50],[50,118]]
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
def K238 := extendKnown K237 8 [(238,[]),(252,[65])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V238 : Known true K238 := extend_ok (m:=238) V237 low238 (by decide +kernel)
def g243Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3fffffffffc1f4b0e,0x20ae7a00000fc003f03f])),(BitVec.ofNat 152 (word80 [0x28428410040840030a,0xa47209249249249249]))),((BitVec.ofNat 152 (word80 [0xfc003ff83fffe0206a,0xe661b18003f000fc0fc0])),(BitVec.ofNat 152 (word80 [0x30130020809002200a,0x2441b1030c30c30c30c3]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffc0003fffffb48c,0x915842c0fc003f000fff])),(BitVec.ofNat 152 (word80 [0x400401410120001084,0x81180084104104104104]))),((BitVec.ofNat 152 (word80 [0xffffffffc000008945,0x6956a9c000000003f000])),(BitVec.ofNat 152 (word80 [0x8298298029c0848845,0x695289f6db6db6db6db6]))),((BitVec.ofNat 152 (word80 [0x9171,0x18b1dc3f00003ffc0000])),(BitVec.ofNat 152 (word80 [0xe00e020e01088160,0x18a04c18618618618618]))),((BitVec.ofNat 152 (word80 [0x4e93,0x4f80057fffffc0000000])),(BitVec.ofNat 152 (word80 [0x30030043002104c11,0x42000060820820820820]))),(0x0,0x0)]
def g243C : List ColumnInfo := [(0,32,210,1,8),(32,0,211,0,8),(1,32,210,0,7),(2,0,241,0,7),(16,0,227,0,7),(64,0,179,0,7),(128,0,115,0,7),(66,0,177,0,5),(18,0,225,0,4),(80,0,163,0,4),(130,0,113,0,4),(192,0,51,0,4)]
def g243A : List (List Nat) := [[],[116],[97],[97,116]]
def g243D5 := limbs80 #[#[0x50941487a95954250521,0x487695d54250521ea765,0x5d55250521f255454941,0x54521f25545095148759,0xe676454951486d961542,0x5d954486d9e115254521,0xc032d1d371595218f781,0xa0d49d2213c6ca0d141,0x808402000]]
def g243D6 := limbs80 #[#[0x7b2a92a290fa54250521,0x1fcaa4a0a432fdd16548,0x877ab2a8290fb5545052,0x21beaeaa0a43bdd95414,0x4877bb22a290fe542545,0x921ddecaa1243bb59542,0x2487b6aa2a490fe77154,0x4921ddec8a9243bb5915,0x644867ebb2a890def745,0x595219faebb22433fdd5,0x565486dfba2ca90df771,0x459521d78e8b2a43bddc,0xd3654867fba2ca90ebf7,0x74585529feeca92833f5,0xe4b110027eba6c2a95bf,0xd72ac4fa65187f39194b,0xc822706803cdccd9662f,0xcadeabf59a9d1a813396,0x1710d0d27217884e41c4,0x801010a08504402071e0,0x60430220108080141ac0,0x100802016c0f0040c60d,0x38f00f18100180005040,0x1a839]]
def g243H6 := limbs80 #[#[0x0,0x58000000008980000000,0x0,0x0,0x0,0x0,0x180000000,0x0,0x0,0x2d00000000,0x0,0x0,0xd795000,0x0,0x347000000000000000,0x0,0x0,0x0,0x0,0x3e9000000000000000,0xf0800,0x9100000000,0x32800000000000000000,0x0,0x0,0x0,0x304000024300000,0x12400000000000014000,0x0,0xa140000000,0x0,0xa2000],#[0x2610000000000,0x0,0x0,0x0,0x0,0x0,0xc0]]
def g243D7 := limbs80 #[#[0xb50921fd54521fd50521,0xd9121bf59121fb54921f,0x8552bfd9521bf59521bf,0x521ff59121ff55121bfd,0x52ff58552ff54941ff59,0x360a81f84e09000ffd85,0x799bc679865d14a4b0fc,0x80f25a4188c729071616,0x8f2586248c44c958c728,0x881492241b11f21c8c44,0x810a2235859321d5c76c,0x2c80a4d714e6c86156c8,0x5050718a2155842481c3,0x4c5288564c704c71a34,0x1a4c7]]
def g243H7 := limbs80 #[#[0x21500,0x0,0x14b8000000,0x111000001a180078a000,0x10600000000,0x33e3216516000001b180,0x3,0x0,0x60500000000000000c0,0x41d1d12548c0,0x0,0x0,0x4200000000000,0xa90001448000000,0x767328000,0x30e00000000f3006c00,0x0,0x49c00000e10000000000,0x2e5b9c00000000000000,0x8000001ca00039a00000,0x3e,0xfe000000000000000000,0x11600000000,0x1c780000,0x1054000000000,0x72e502000,0xb140000000000000000,0x838000008263280000,0x6a800000a08000000000,0x3400000001,0x3040000000000000,0x0],#[0x194800000000000]]
def g243D8 := limbs80 #[#[0x879aa407f54bfa83fd21,0x90c3b469238d145aa324,0x11accc4]]
def g243H8 := limbs80 #[#[0xe1dd3812a31401a00ce0,0x514008380000242000b0,0x10ca0e205184a,0x651b39278d0a1c049b81,0xe226e003ad0034b00000]]
def g243D9 (j : Nat) := if j=0 then 0x1654321bf else 0
def g243H9 := limbs80 #[#[0x1400000011,0x82581c00000090]]
def g243L : Nat → Packing
  | 5 => (11,4,4,0,0,7,0,g243D5)
  | 6 => (30,3,4,0,0,9,0,g243D6)
  | 7 => (15,2,4,0,0,10,0,g243D7)
  | 8 => (3,1,4,0,0,7,0,g243D8)
  | 9 => (1,0,4,0,0,0,0,g243D9)
  | _ => emptyPacking
def g243I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 4 307 0 10 4 2 g243H6
  | 7 => lookupWord 11 239 2 11 5 2 g243H7
  | 8 => lookupWord 6 37 5 10 4 2 g243H8
  | 9 => lookupWord 1 17 0 8 2 2 g243H9
  | _ => fun _ => none
def g243 : Forest := ⟨243,9,fun i => g243Y[i]?.getD (0,0),g243C,g243A,g243L,g243I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P5_0 : block g243 5 0 11=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g243B5 : block g243 5 0 11=true := g243P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P6_0 : block g243 6 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P6_3 : block g243 6 3 27=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g243B6 : block g243 6 0 30=true := (@block_merge g243 6 0 3 27 g243P6_0 g243P6_3)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P7_0 : block g243 7 0 9=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P7_9 : block g243 7 9 6=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g243B7 : block g243 7 0 15=true := (@block_merge g243 7 0 9 6 g243P7_0 g243P7_9)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P8_0 : block g243 8 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g243B8 : block g243 8 0 3=true := g243P8_0
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
def K243 := extendKnown K238 10 [(243,[]),(246,[32,100]),(250,[48,32,100])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V243 : Known true K243 := extend_ok (m:=243) V238 low243 (by decide +kernel)
def g245Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3fffffc1fffff620e,0xa0acdb00000fc0000fff])),(BitVec.ofNat 152 (word80 [0x28428408401040220a,0x20a05a09249249249249]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfc003fffe0ffe02962,0xe663308003f000fff000])),(BitVec.ofNat 152 (word80 [0x300b00500200822902,0xa44310030c30c30c30c3]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffc00000ffffbd84,0x915842c0fc003f00003f])),(BitVec.ofNat 152 (word80 [0x400c01608405001984,0x81580086186186186186]))),((BitVec.ofNat 152 (word80 [0xffffffffff0000804d,0x6956a9c000000003ffc0])),(BitVec.ofNat 152 (word80 [0x8290298000a6048045,0x4914a1f4d34d34d34d34]))),((BitVec.ofNat 152 (word80 [0x9171,0x18b1dc3f00003ffc0000])),(BitVec.ofNat 152 (word80 [0xe00e010838088060,0x18a0cc18618618618618]))),((BitVec.ofNat 152 (word80 [0x4e93,0x4f80057fffffc0000000])),(BitVec.ofNat 152 (word80 [0x300300210c0104411,0x42000160820820820820]))),(0x0,0x0)]
def g245C : List ColumnInfo := [(1,0,244,0,7),(4,0,241,0,7),(32,0,213,0,7),(128,0,117,0,7),(0,32,208,5,6),(16,0,229,0,6),(64,0,181,0,6),(1,32,208,4,5),(4,32,208,1,5),(17,0,228,0,5),(33,0,212,0,5),(48,0,197,0,5),(68,0,177,0,5),(96,0,149,0,5),(5,0,208,0,4),(5,32,208,0,4),(20,0,225,0,4),(37,0,208,0,4),(49,0,196,0,4),(65,0,180,0,4),(100,0,145,0,4),(129,0,116,0,4),(132,0,113,0,4),(144,0,101,0,4),(160,0,85,0,4),(192,0,53,0,4)]
def g245A : List (List Nat) := [[],[32,100]]
def g245D5 := limbs80 #[#[0x485404427c61f41c8110,0x443cc5515150110fa142,0xe157650910e696254950,0x501208bf845d9524421f,0xd697554940483ca55152,0x549504839a5915254120,0x483965915354120d6b74,0xe156454d20e2d6455152,0x547208ef825d95448297,0xe2d6455152c822fe1176,0x5095050297e156454f20,0x503c654d4254140f2952,0x54f4254140dab72d0950,0x48540e5953d8950503c6,0xe2d65549425032bdd362,0x54942d0347dd55350940,0xd0347dd55350b40e2d65,0xdd55358b40e2d5458952,0xd0950c5f7654d4254317,0xd59535c3425433ad8970,0x59153542ab61362d0950,0x50ad66026454d50b4f82,0x5537154942e2d5454b60,0x54a42a5d80d955350b4b,0xa5f855915390b8b59154,0xc27030022fe1171d8152,0xcf06931974ae51259146,0xadd62ab52a7d329346a1,0x76b9dc2db6ab3d92c35e,0x238ec5e230b82bfdf2f3,0x8241078441080604be53,0x6080c100000000001]]
set_option maxRecDepth 16000 in
def g245D6 := limbs80 #[#[0x3b4a92a0904dd75d8d10,0xeb2a6a8281d654d5048,0xa6fbb2a7a04ef725954,0x42cbacaa9885b654d601,0x50b2eb9aca214df7654c,0xa42cbecaa9a85cb55152,0x443f9a0e408878d53d0,0x8110fd2a590221fc5472,0x40442fcbae40885f974c,0x50110fe2a2a0221fc485,0x1404437cb1280887b942,0x550110df2caa0221ee55,0x4950442fdbaa80885f97,0x6454110df2c4a8221de5,0xdc142442fdba2a0886f9,0xd7650910dbec6a12217e,0xedc1524427fbb284884f,0xdf6354910ddac4a92217,0x3fdd1624427ebb2a4886,0x4ff72595109feeab1221,0x1f654d40483f4a928090,0x7ba5450120f72a8a024,0x417e5d5404837cb2a809,0x906f96454120bf6eaa02,0xa417e5c341482fdba2a0,0x49076d54549209faeda0,0xa241b75915348376b22a,0xa8904fd7655120d7ac8a,0x2a241af59254482fcb84,0xac8906fb70591209faed,0x2b2a413fdd5644827fb8,0xb683904ff74595209fee],#[0xeca8e41bd58551c827eb,0xaa2a5906ed52587209fa,0xac8a9e41bb59152c83b6,0xeb2aa9906bd6455320db,0x7ac92a6413f5d954c833,0x7fb8ac9904fd7695320d,0xdf6c2a82813fdd564c82,0x3dca12a0a05fb7154140,0xef2a4a8281eed095050,0x2fdb92a0a06fb625414,0x40ddec490a81eb509215,0x502dfba2a2a073d54545,0x540d7aa9b0a813f5cb61,0x2502fdb8284a04fd75d8,0x940f5aa4a1281eedc14,0x425035eb2a84a079d535,0x50940b7aeaa1281afd95,0x742503cea9e84a05bf75,0x454940b7aeba1281af59,0xc7625033eb2aa4a073d5,0x54d8940dbaa7b12813f5,0xdc9545027ebaec4a06bd,0xf7259540b7ae52a2816f,0xb1c9655027fb8acaa05e,0xff7259540ddee4b2a81b,0x3f5cb655027eb8ecaa04,0x79d5350b40f5aa4a1681,0x16f5d542d035eb2a85a0,0x6ed6254b40b7eeaa168,0x81cf55152d036eb1aa5a,0xa04fd7654b40cfacaa96,0x681af55162d036ea9ac5],#[0x2a84fd72d85509feeab1,0x12a1db549425427eba6c,0x84a84ff7650950ebaa6a,0xa12a1bbd8b42542fcb86,0x2a4a84fd76d0950ebaa7,0x3b12a1d754d625433fb2,0x22a6a84fd74d89509fae,0xe4b22a1d799153543aeb,0xbacc8a85f97099150bde,0xae3b22a13f5da64542be,0x7b92a8994fd72d91509f,0xdee4aa465bd551618caf,0x3eb2aa9196bd6455232b,0x9feeab24653f5d9548cb,0xb76a96c0a14fd71d8142,0x2d7aa9b0285b754f6050,0xa7ebaec0a16be54d814,0x42cfecaa9285cf551525,0x50bb7b2aa4a15ef71549,0xd42cfecaa9a857b5c652,0x550b3fb2acaa175f6554,0x86429fae1b2a853fdc16,0x5290b6ea9ac3216ed525,0x54e42ddac8a9485db551,0x95490b3eb2aa9216dd64,0x1d81529feeab24853f5d,0xd16154a7eba6c0a94fd7,0x70d8552b7ee8b0aa56f1,0x5d36154b3eaa6c2a94fd,0xd7299152bf6e0b1aa53f,0xf5c76454a7eb86c8a95e,0xfd74d89539fee2b24a53],#[0x775d36254eeeba0c4a9c,0x280dc0c009405801c001,0xc2802642281ec1a01641,0x36432831c3002f42d82c,0x9848c4604243f83cc390,0xc55054452850c4e04b44,0x65464860c6005e45b858,0xe86cc6c06b469868c680,0xc76075473872c7107046,0x7f47e87cc7c07a478876,0x5884c84083482881c800,0xc8f08d48c88bc8a08848,0x96495894c94093492890,0xf89ec9d09c49b89ac980,0xcab0a94a78a5ca40a249,0xb34b28b0caf0ae4ad8ab,0xc8bacb90b84b68b5cb50,0xcc60c54c38c1cc00bf4b,0xce4cd8cacca0c84c78c6,0x48d3cd20d14d08cfccf0,0xcdb0da4d98d7cd70d54d,0xe34e28e0ce00de4dd8dc,0x8eccec0e94e68e5ce50,0xcfc0fb4f98f6cf50f44f,0x5503901d000ff4fe8fc,0xc90bd0b10a508907d061,0xd15113512910d1010e50,0x1f51d91cd1b11a519916,0x8927d26125524922d211,0xd2e12d52c92bd2a12952,0x20336933d3313253092f,0xa1e10a87c486c8061218],#[0x31448649814698251822,0x1a624d151894498921c6,0x18804083029186c51912,0x600082007820314644b,0x1612080061e4c1136108,0x841e0c841e120840c84,0x8781841e06100020128,0x8041020181060008202,0xc0804180060e10084,0x820c0800428200008041,0x82060800028200182002,0x4820000a08006081,0x80001820c08781840000,0xe0800000000a08182060,0x88040518200000783041,0x608002000898202090,0x800a0c0020000008,0x201040a089820028200,0xa08000006002c60b1820,0x18200000000008041000,0x2000060800a08000,0x8400112080060802a080,0x6322a92180080410bc4,0x2820c481000200a9211,0x1020808182000040800,0xe0828200000182000020,0x322e10182040800a0802,0x8182060828200182000,0x820000030200000,0x1a0610003082000020]]
def g245H6 := limbs80 #[#[0x7d4c0e80252800048004,0x11000184216ebda,0x8bada00078c000000,0x4f800d500004360c2ba,0x19d0000000041b00000,0x97be00145914001e080,0x53d6958d313147610004,0x728206f1c4482434c000,0x29a58000000000000040,0x89000001592c70000006,0xd58f2a00083e96101023,0xf001604007992ca70cc8,0x350a8]]
set_option maxRecDepth 16000 in
def g245D7 := limbs80 #[#[0x754d50b758f40b7d8d10,0x58c42be58042bd58632d,0x8110ebd0a429f59442b7,0x910fe54110fe50110fec,0x20fe50120bf59510bf58,0xf754d20fb54920fe541,0xbf58720bf59520bf5912,0xf59320f754f20fb54b20,0xd8540fe54140bf59720b,0x8940efd0940ef50940bf,0x140f794d40f754d40bfd,0x40bf59540ef95140ef55,0xbf58b40ef50b40bfd95,0xbf59740ef55340f754f4,0xfd8950df54950bfd8550,0x59632bf59232bfd9150b,0x8142bf59442f754c42bf,0xd42fb94942fb54942bfd,0x42bf59542f794d42f754,0x2fb54a42bf58642bfd95,0xbf59642bf59242f754e4,0xf55152bfd8552bfd8152,0x59252bf58652bfd9152d,0x8953f718953bfd8953bf,0x520ff54910ff50910f7d,0x20ff54520ffd0520ff50,0xffd0720ff95120ff551,0xff95320ff55320ff5472,0xf54540ff48540ff55130,0x54940ff50940ff58540f,0x9540ff55140ff58940ff,0x950ff58550ff54b40ff5],#[0x50ff58950ffd0950ff50,0x2ff55132ff99150ff591,0xffd8142ff58142ff5523,0xf58d42ff54d42ff54942,0xd9542ff59542ffd8d42f,0x8552ff58152ff55242ff,0x152ff59152ff58d52ff5,0x60ab07b059030000ff99,0x18416213211e1030e80c,0x872652432211ff1e41b4,0xb38b35b3393172ee2c52,0x48e46c44a4284063e43b,0xc95a758556a53a4f54cc,0x86bf69666663d61b5eb5,0x7d07b579377874f7116e,0x128db8c089786082980e,0x8a089df9c49949649349,0xafdae2aceaaca83a61a3,0xacb91b76b5bb47b2cb11,0xec5cc2cc11befbdbbc0b,0xd27d05ce3cbaca6c92c7,0xdddc2daed93d71d56d3b,0x5e6ae56e3be20e05df1d,0xf27f13ef1ecfeb4ea0e8,0x1c01a205938e08499006,0x58c4050e3032b2478927,0xc310185871048c161cd8,0xf1958f0848c16189182,0x3c62a9518f1099184946,0xc54305223c6201819112,0xc488543a312261264832,0x6049091a4a31e217488],#[0x78a5ca86088c10112413,0xe215488e005145860640,0xc02e30303005891a2a31,0x29545849874630608080,0x3109864248422141931e,0x518f100e3244c4183449,0x488602322312464448d1,0x1929310c464c5324f106,0x519318c932a101010b01,0x1a246083448c0c284040,0x3248030c891518798203,0xa1828f2a205080068c32,0x4040449518b95480c48,0xc4050e2850808095143,0x44732490181080e5c51a,0x83082458c2e298450600,0x328c4861431746203024,0xa120d11809060468a8c8,0x8c7325c223040400e8c,0x63048b202860a101010,0xc46088a0a392386125c3,0x80c101125c6062c60910,0x4045c60c100e2405c60,0x80612e285325c30c840,0x1862450c131098640608,0x21874a286101cc081010,0x8e0e10e093080e6044c2,0x125830c844863048508b,0x190850d1890c1991210f,0x105461830a6421e14b06,0x62c4c786860132020a08,0x8305804c426386074484],#[0xc4a3149990898908b930,0x2a887890a0062e2192a4,0x5ca890ca890c1862a116,0x20b083a22a1991254988,0xb86150044c485042990c,0x208684161a2086030c14,0x66420c1518664ba30c22,0x5885cb10422172a2434,0x2e0992e118088]]
def g245H7 := limbs80 #[#[0x604781041c101200098f,0x1018b0a240123a341881,0x40920010005000080104,0x7030a000804c1818202e,0x47c10d00b01881119,0x4029c48952104aba7043,0x11b216c000a060002572,0xe41dd1e0724d4000000,0x62ec000a8593a800000,0x94cbd000000183d56700,0x2d81a2d6fa6d28bad674,0x8e2e2f1b3792015b339b,0xa49649413880db62ec4c,0xba0dd87d39e09204d518,0x4047428dca5c9088739d,0x8bca801f328a0dbc16ab,0x9911412c6e37c0ea5979,0x800001b4503e0d5d05c4,0x83f00049f4914000300f,0x6ab2072000d5f0000000,0x5267a44800104b6a6000,0x9800193ce4f000019b02,0xe93a70002cd0000000c2,0x142c00000000024,0xcfd04400000010740000,0xd31a172579dafa2c8003,0x304106e00003130f4000,0x4310a9a506b497559800,0x96001b852f9ee54006,0x5ac30fdba011b6f00000,0x20a013a19bb28003f64a,0x55a05180000006],#[0xa0c001207a302047552,0xc1700071964f0000f2c,0xc62000000558400,0x18ba635800197137e00,0xcba42a00000000,0x185f1c0000002a740000,0x2234f4d0870000001,0x376a0006078000001698,0x82c41a4400042c000000,0x5926d0ae12070ce51141,0xb521d911c248013416a4,0x2a3677c6f1d980005870,0x650b51517c00003741a0,0x127712a80014ac,0xa000453a9c8001c43000,0x4ea44aff5800074cbc2,0x7a44b214800311756474,0x35e8d3749d0000000f,0x80cc0384310f40000000,0xb4b3d8c00111408f5abc,0x52c1a3c68acdecb48000,0x7cd132a918c64e2d751e,0x8c88d4ab90e992706093,0x8fb52713102898b34ffc,0xa866712270005afc465c,0xf690006a540010840005,0x3e64001e420003a4c001,0x179b6116251d35c2b000,0x699fdc46a0a00000018e,0x827785229632251d3362,0x1c706800065ec0850f89,0x604f40eb0080a0009]]
def g245D8 := limbs80 #[#[0xf20fe907f443bca7dd53,0x65fd50ffa07f503fa61f,0xbfc85fd42fe217f8cbfa,0x780c001fd53ff297f54,0x300ae24c7e18c5410833,0x419e1cd523438ff3c0d8,0x88461319e304a241a228,0x2420d1c201628d1c2908,0xa3429931c43980106c64,0xa8114248e19011319801,0x9b18a40e39b19058e28c,0x6a242040801926163840,0x308bc21a434661258824,0x1a58419038c34258648a]]
def g245H8 := limbs80 #[#[0x500000cc48000bb2810e,0x141108ac42804201002,0x96800000000204628881,0xcc658003158000000006,0x21d00000001eccda8f20,0x232a78007e832535341a,0xb8000000002b50004223,0x5c8b065b727029c8001a,0x61354d7c821400d000,0x1c3598e8000003720f08,0x4898000006978000004e,0x303308319800,0x6736d654281a70ae04f0,0x398402e0100006793,0xb399e72a80015188e000,0x180018ab16122eab784c,0x1c5fc10003ca8000b277,0x3141508241b51bd923b4,0x323f4e8003948000000,0x4007855b008ba3780000,0x7840001990004e1120,0x39fd100001676d932c0,0x79150691700000,0x3352a0000004eb8ae800,0x32f1e4b5280021c0006,0x9e40000000000000a080,0xde6e5e2000000287c0f,0x7245d88005076a18003,0xea4d2dbc238c19180000,0xd01c5312800244000298,0xd8af8000002580005295,0x793a7162d65cdc4b08ee],#[0xa2ea2a169aa32800000,0xde6d09781885b9d8009,0x8005a612880013091f25,0xb4ecf9693f5000526831,0x6038004a9d630acf908,0x38b0003a580000]]
def g245D9 (j : Nat) := if j=0 then 0x1882013f else 0
def g245H9 := limbs80 #[#[0x4f1c1380113000344860,0x6f0e0040cc1d10004838,0xa0000002180011ef,0x2200000102000428ca0,0x1c50378d257000d50940,0x65dc9e68859]]
def g245L : Nat → Packing
  | 5 => (41,4,5,0,0,9,0,g245D5)
  | 6 => (199,3,5,0,0,12,0,g245D6)
  | 7 => (112,2,5,0,0,12,0,g245D7)
  | 8 => (17,1,5,0,0,10,0,g245D8)
  | 9 => (1,0,5,0,0,0,0,g245D9)
  | _ => emptyPacking
def g245I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 13 83 5 11 6 1 g245H6
  | 7 => lookupWord 65 359 7 13 8 1 g245H7
  | 8 => lookupWord 39 239 5 12 7 1 g245H8
  | 9 => lookupWord 7 41 5 10 5 1 g245H9
  | _ => fun _ => none
def g245 : Forest := ⟨245,9,fun i => g245Y[i]?.getD (0,0),g245C,g245A,g245L,g245I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g245P5_0 : block g245 5 0 41=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g245B5 : block g245 5 0 41=true := g245P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g245P6_0 : block g245 6 0 13=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g245P6_13 : block g245 6 13 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g245P6_109 : block g245 6 109 90=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g245B6 : block g245 6 0 199=true := (@block_merge g245 6 0 13 186 g245P6_0 (@block_merge g245 6 13 96 90 g245P6_13 g245P6_109))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g245P7_0 : block g245 7 0 8=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g245P7_8 : block g245 7 8 61=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g245P7_69 : block g245 7 69 43=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g245B7 : block g245 7 0 112=true := (@block_merge g245 7 0 8 104 g245P7_0 (@block_merge g245 7 8 61 43 g245P7_8 g245P7_69))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g245P8_0 : block g245 8 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g245P8_2 : block g245 8 2 15=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g245B8 : block g245 8 0 17=true := (@block_merge g245 8 0 2 15 g245P8_0 g245P8_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g245P9_0 : block g245 9 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g245B9 : block g245 9 0 1=true := g245P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g245T : checkedTables g245 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g245 0 0 0 = true)
  · exact (rfl : block g245 1 0 0 = true)
  · exact (rfl : block g245 2 0 0 = true)
  · exact (rfl : block g245 3 0 0 = true)
  · exact (rfl : block g245 4 0 0 = true)
  · exact g245B5
  · exact g245B6
  · exact g245B7
  · exact g245B8
  · exact g245B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g245G : graphValid g245 (boundsBefore K243) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low245 : Lower true (varsX 245) (graphGoal 245) 10 := lower_forest (g:=g245) (i:=0) (hints:=33555716) (before_sound K243 V243) g245G g245T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K245 := extendKnown K243 10 [(245,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V245 : Known true K245 := extend_ok (m:=245) V243 low245 (by decide +kernel)
def g249Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfffffe0ffffffe9c,0x2d232c040007c0007fff])),(BitVec.ofNat 152 (word80 [0x421042042008200284,0x232004842108421084]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xff001ffff07ff07d23,0x8841d43c00f801ff801f])),(BitVec.ofNat 152 (word80 [0x40280280100410102,0x88005410210842108421]))),((BitVec.ofNat 152 (word80 [0xffffe000007fff80c3,0xcf3442c01f003e0003e0])),(BitVec.ofNat 152 (word80 [0x80300b04202800803,0xcf0440806318c6318c63]))),((BitVec.ofNat 152 (word80 [0xffffffffff80000035,0x265c7b200000000ffc00])),(BitVec.ofNat 152 (word80 [0x90a414c00053021031,0x265c0b235ad6b5ad6b5a]))),((BitVec.ofNat 152 (word80 [0x44,0x90bf89b3e0003ff00000])),(BitVec.ofNat 152 (word80 [0xe0380700841c042044,0xb389218c6318c6318c]))),((BitVec.ofNat 152 (word80 [0x33a,0x528a034bffffc0000000])),(BitVec.ofNat 152 (word80 [0xc018010860084038,0x1008024a108421084210]))),(0x0,0x0)]
def g249C : List ColumnInfo := [(1,0,248,0,7),(8,0,241,0,7),(16,0,233,0,7),(64,0,185,0,7),(0,32,208,9,6),(32,0,217,0,6)]
def g249A : List (List Nat) := [[],[48,100]]
def g249D7 := limbs80 #[#[0x8156ea605d03bca7dd53,0x4ba9]]
def g249D8 (j : Nat) := if j=0 then 0x2c6881bf else 0
def g249H8 (j : Nat) := if j=0 then 0x3d5 else 0
def g249L : Nat → Packing
  | 7 => (2,1,3,0,0,5,0,g249D7)
  | 8 => (1,0,3,0,0,0,0,g249D8)
  | _ => emptyPacking
def g249I : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 1 2 0 5 1 0 g249H8
  | _ => fun _ => none
def g249 : Forest := ⟨249,8,fun i => g249Y[i]?.getD (0,0),g249C,g249A,g249L,g249I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g249P7_0 : block g249 7 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g249B7 : block g249 7 0 2=true := g249P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g249P8_0 : block g249 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g249B8 : block g249 8 0 1=true := g249P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g249T : checkedTables g249 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g249 0 0 0 = true)
  · exact (rfl : block g249 1 0 0 = true)
  · exact (rfl : block g249 2 0 0 = true)
  · exact (rfl : block g249 3 0 0 = true)
  · exact (rfl : block g249 4 0 0 = true)
  · exact (rfl : block g249 5 0 0 = true)
  · exact (rfl : block g249 6 0 0 = true)
  · exact g249B7
  · exact g249B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g249G : graphValid g249 (boundsBefore K245) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low249 : Lower true (varsX 249) (graphGoal 249) 9 := lower_forest (g:=g249) (i:=0) (hints:=50331651) (before_sound K245 V245) g249G g249T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K249 := extendKnown K245 9 [(249,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V249 : Known true K249 := extend_ok (m:=249) V245 low249 (by decide +kernel)
def g127Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xf3228a18b468cc81d7,0xe080000000000fe03fff])),(BitVec.ofNat 152 (word80 [0x4120881094684c00c7,0x8010a142850a142850a1]))),((BitVec.ofNat 152 (word80 [0x92afd0402989e3741,0x1b400001fc00001fc000])),(BitVec.ofNat 152 (word80 [0x610adc0402188e3741,0x9458b162c58b162c58b]))),((BitVec.ofNat 152 (word80 [0x7508d02f736115d35,0x84000fe0007f0000000])),(BitVec.ofNat 152 (word80 [0x83508d02f334104d15,0x843870e1c3870e1c387]))),((BitVec.ofNat 152 (word80 [0xf25c4ce7aac1f04140,0x69007f0003f80000007f])),(BitVec.ofNat 152 (word80 [0x25c44c62281904100,0x6803060c183060c18306]))),((BitVec.ofNat 152 (word80 [0x85814f63a014663a,0xd6bf80000000001fff80])),(BitVec.ofNat 152 (word80 [0x5014b6180104038,0x528a142850a142850a14]))),((BitVec.ofNat 152 (word80 [0x116669158062bf0a8,0x15c0000003ffffe00000])),(BitVec.ofNat 152 (word80 [0x22201080223b028,0x15ac58b162c58b162c58]))),((BitVec.ofNat 152 (word80 [0xce93272055b22080f,0xc3ffffffc0000000000])),(BitVec.ofNat 152 (word80 [0xca022300442200002,0x43060c183060c183060]))),(0x0,0x0),(0x0,0x0)]
def g127C : List ColumnInfo := [(2,0,125,0,9),(4,0,123,0,9),(8,0,119,0,9),(1,0,126,0,8),(16,0,111,0,8),(32,0,95,0,8),(64,0,63,0,8),(0,2,45,80,7),(0,32,82,13,7),(1,32,82,12,6),(4,32,82,9,6),(16,2,45,64,6),(33,0,94,0,6),(64,2,45,16,6),(17,0,110,0,5),(80,0,45,0,5),(80,2,45,0,5)]
def g127A : List (List Nat) := [[]]
def g127D7 := limbs80 #[#[0xbbf845d940fbb8458140,0xbf78159150dbf845d940,0x1038c94180ebf7459160,0x40400f0ee00c38]]
def g127D8 := limbs80 #[#[0x960502f7b92cb7ddc564,0x22c17fdd940bfaeca07f,0x65bfeecaa5ff745837eb,0x7fd64543febb2817fdd1,0x1b801ffdd160ffae8b0,0x6ed362c42a2861aa4f0c,0x2e30f1b0c4c43c8f0f40,0x381362884098d8310a17,0x1c202e0c38880e3a2e11,0x143484884c170e0c4387,0xb0e2c09070d954611f83,0xc4245c382262122880b1,0x6080c78e168130b87046,0x181a40c78e1a8120a80]]
def g127H8 (j : Nat) := if j=0 then 0x95101f00102600000 else 0
def g127D9 := limbs80 #[#[0x64ff553fd60ff543fd40,0x4d2511b07800ff597fd,0x88c1ce0e694486026226,0x99468600e2226908821,0x38624071851208622479,0x1441a08a124720096]]
def g127H9 := limbs80 #[#[0x19060,0x12bf3c0004c0000,0x123180001a8,0xee000000000000000000,0xb6e40001e601540000]]
def g127D10 (j : Nat) := if j=0 then 0x3148308043ff else 0
def g127H10 := limbs80 #[#[0xe5f64000064000,0x721800]]
def g127L : Nat → Packing
  | 7 => (5,3,5,0,0,6,0,g127D7)
  | 8 => (13,2,5,0,0,10,0,g127D8)
  | 9 => (6,1,5,0,0,9,0,g127D9)
  | 10 => (1,0,5,0,0,0,0,g127D10)
  | _ => emptyPacking
def g127I : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 1 11 0 7 3 0 g127H8
  | 9 => lookupWord 3 53 3 8 4 0 g127H9
  | 10 => lookupWord 1 17 0 7 3 0 g127H10
  | _ => fun _ => none
def g127 : Forest := ⟨127,10,fun i => g127Y[i]?.getD (0,0),g127C,g127A,g127L,g127I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_0 : block g127 7 0 5=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B7 : block g127 7 0 5=true := g127P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_0 : block g127 8 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_2 : block g127 8 2 7=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_9 : block g127 8 9 4=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B8 : block g127 8 0 13=true := (@block_merge g127 8 0 2 11 g127P8_0 (@block_merge g127 8 2 7 4 g127P8_2 g127P8_9))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P9_0 : block g127 9 0 6=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B9 : block g127 9 0 6=true := g127P9_0
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
  · exact g127B7
  · exact g127B8
  · exact g127B9
  · exact g127B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127G : graphValid g127 (boundsBefore K249) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low127 : Lower true (varsX 127) (graphGoal 127) 11 := lower_forest (g:=g127) (i:=0) (hints:=16778563) (before_sound K249 V249) g127G g127T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K127 := extendKnown K249 11 [(127,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V127 : Known true K127 := extend_ok (m:=127) V249 low127 (by decide +kernel)
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
def g223Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffffff2ca9685e1695,0x83a8000000f8000003ff])),(BitVec.ofNat 152 (word80 [0x520142ca9481a1605,0x80a094a5294a5294a529]))),((BitVec.ofNat 152 (word80 [0xfff000ff560c22eb01,0x22a800001f00000ffc00])),(BitVec.ofNat 152 (word80 [0x264066fd160c226301,0x228318c6318c6318c63]))),((BitVec.ofNat 152 (word80 [0x13ad9cae03a0,0x7b700003e00001f00000])),(BitVec.ofNat 152 (word80 [0xb782b8132d9cae03a0,0x3b70739ce739ce739ce7]))),((BitVec.ofNat 152 (word80 [0xffffff9416bf8d1814,0x271a007c00003e00001f])),(BitVec.ofNat 152 (word80 [0x3804c09016b7840810,0x271a6318c6318c6318c6]))),((BitVec.ofNat 152 (word80 [0x2157254abe3,0x24540f800007c0007fe0])),(BitVec.ofNat 152 (word80 [0xc007000200324488e2,0x24504210842108421084]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x49ca15911468,0x54a5f0000007ffff8000])),(BitVec.ofNat 152 (word80 [0x80000c000111408,0x40848421084210842108]))),((BitVec.ofNat 152 (word80 [0xb0208222440a,0x8853fffffff800000000])),0x10842108421084210),(0x0,0x0)]
def g223C : List ColumnInfo := [(4,0,219,0,10)]
def g223A : List (List Nat) := [[]]
def g223D10 (j : Nat) := if j=0 then 0xff else 0
def g223L : Nat → Packing
  | 10 => (1,0,1,0,0,0,0,g223D10)
  | _ => emptyPacking
def g223I (_ _ : Nat) : Option (Nat × Nat) := none
def g223 : Forest := ⟨223,10,fun i => g223Y[i]?.getD (0,0),g223C,g223A,g223L,g223I⟩
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
  · exact (rfl : block g223 5 0 0 = true)
  · exact (rfl : block g223 6 0 0 = true)
  · exact (rfl : block g223 7 0 0 = true)
  · exact (rfl : block g223 8 0 0 = true)
  · exact (rfl : block g223 9 0 0 = true)
  · exact g223B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223G : graphValid g223 (boundsBefore K191) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low223 : Lower true (varsX 223) (graphGoal 223) 11 := lower_forest (g:=g223) (i:=0) (hints:=16778819) (before_sound K191 V191) g223G g223T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K223 := extendKnown K191 11 [(223,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V223 : Known true K223 := extend_ok (m:=223) V191 low223 (by decide +kernel)
def g239Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffb860a824125c734e,0xc5000000fc0000000fff])),(BitVec.ofNat 152 (word80 [0xa2820a804121c3202,0xc5249249249249249249]))),((BitVec.ofNat 152 (word80 [0x4a093e427c362749,0xa200003f00003f000000])),(BitVec.ofNat 152 (word80 [0x330a093e022c162749,0xa21c71c71c71c71c71c7]))),((BitVec.ofNat 152 (word80 [0x39b32e0c21138d23,0x9000fc0000fc003f000])),(BitVec.ofNat 152 (word80 [0x5c39b12c0421138503,0xc30c30c30c30c30c3]))),((BitVec.ofNat 152 (word80 [0xff949c4d96ac4e9188,0x3f00003f000fc003f])),(BitVec.ofNat 152 (word80 [0x60109845002c428188,0x82082082082082082]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x652c2fa4a934e42,0x30000000000000ffffc0])),(BitVec.ofNat 152 (word80 [0x80064202fa40804840,0x30d34d34d34d34d34d34]))),((BitVec.ofNat 152 (word80 [0x8a90581d3a05810,0xbffc000003ffff000000])),(BitVec.ofNat 152 (word80 [0x81d2205800,0x1d618618618618618618]))),((BitVec.ofNat 152 (word80 [0x674430492480a0b5,0x54fffffffc0000000000])),(BitVec.ofNat 152 (word80 [0x4444004800800034,0x820820820820820820]))),(0x0,0x0)]
def g239C : List ColumnInfo := [(4,0,235,0,10)]
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
theorem low239 : Lower true (varsX 239) (graphGoal 239) 11 := lower_forest (g:=g239) (i:=0) (hints:=16778595) (before_sound K223 V223) g239G g239T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K239 := extendKnown K223 11 [(239,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V239 : Known true K239 := extend_ok (m:=239) V223 low239 (by decide +kernel)
def g247Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x829c3cd0734a242250,0xfe0000001fc07f])),(BitVec.ofNat 152 (word80 [0x82941c90520a202052,0x24489122448912244891]))),((BitVec.ofNat 152 (word80 [0x42abc49950361380b0,0x7f000007f0003f80])),(BitVec.ofNat 152 (word80 [0x4289c4995036120000,0xa142850a142850a14285]))),((BitVec.ofNat 152 (word80 [0xdcc72d801410da7100,0x3f800003f80fe00000])),(BitVec.ofNat 152 (word80 [0xcc822d801410922100,0x60c183060c183060c183]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x8432239ea8cc988c00,0x1fc00001fc0000003fff])),(BitVec.ofNat 152 (word80 [0x422210228c0888801,0x42850a142850a142850a]))),((BitVec.ofNat 152 (word80 [0x11a99a6d2c92ec42a0,0xfffc000])),(BitVec.ofNat 152 (word80 [0x1129826d28804c42ad,0x9b366cd9b366cd9b366c]))),((BitVec.ofNat 152 (word80 [0x6154172348210167df,0xe0000001fffff0000000])),(BitVec.ofNat 152 (word80 [0x2154120000000146d6,0xc183060c183060c1830]))),((BitVec.ofNat 152 (word80 [0x3f00c064938102186f,0xfffffffe000000000000])),(BitVec.ofNat 152 (word80 [0x100000648101001028,0x10204081020408102040]))),(0x0,0x0)]
def g247C : List ColumnInfo := [(1,0,246,0,10),(2,0,245,0,10),(4,0,243,0,10),(0,32,210,5,9),(16,0,231,0,9),(32,0,215,0,9),(64,0,183,0,9),(128,0,119,0,9),(80,0,167,0,5),(144,0,103,0,5)]
def g247A : List (List Nat) := [[],[32,100]]
def g247D6 := limbs80 #[#[0x7654f8d776e0f815d953,0x17835d953cd5e5793e05,0x5e1783e057654f85f76e,0x54f55795e4f815d953e5,0x815d563d35e5b93e0576,0x91e612306032d796e4f]]
def g247D7 := limbs80 #[#[0xc1aeca9e37ddb835d953,0xa7e5f76e156354f2bf0b,0xdb815d953debc1f02bb2,0x654f7af27c0aeca9f3dd,0xfbb706bb2a7b5f85e0d7,0xaeca9f75e0f815d953e6,0xcf796e057654fbaf27c0,0x8359563eafc2f06bb2a7,0x8f7af07c0aeab1f97dd7,0x9f02baac7af786e05755,0xab1ebde5b815d563debc,0x920e8b058035bf0dc1ae,0xb531ae2aa723a01c9915,0xa607c75c2f1f00bfbc38,0x7c41d704c417005c01,0x5c01a407c413104c417,0x35813104c4170]]
def g247H7 := limbs80 #[#[0x31000054000012f500f3,0x9de658000040]]
def g247D8 := limbs80 #[#[0x9f7815d953e5d6558d53,0xedf7658d53f5f8558d53,0xbdf835d953bf7815d953,0xdf7815d953cff765d953,0xedf8359563ddf835d953,0xbdf835d563bf7815d563,0xff7815d953aff865d563,0xff7815d563fdf835d953,0xeff865d563fdf835d563,0x5b14344cd5294750f800,0xb7ac3abe789060374daa,0xbf5e69a272e1c48c36f2,0x1c6b8dd79e6c9cb8571c,0x91c8bc4e3c330dc9344e,0x271ae331ebcf372e192b,0x3c08cd93970e2288e5c1,0xe5c2bf117364ebcebf26,0x856ce44749cb8f0ac366,0x3971e15b38ec7af3c9cb,0xae1094fcb8f0ad907129,0x26b710c8d608457e2191,0x135b886]]
def g247H8 := limbs80 #[#[0x30,0x0,0x7240000000000000000,0x0,0x30600000001c20000,0xd300,0x0,0x2450b00000000000009,0x0,0xa000000000000000032,0xd0000000000000009940,0x3c40008,0x0,0x1a40,0x3c0000000000000000,0x0,0x0,0x0,0x0,0x78280000000000000000,0x381c00000000000028ea,0x50400000000000,0x0,0x800000000000020eaa00,0xe140000000000000020]]
def g247D9 := limbs80 #[#[0xe6454fdeb22a7f758d53,0x2ac77fdd953bfaeca9fb,0x53ffaeca9dff7558f7eb,0x7ff7558ffebaac7ffdd9,0x2c4991f86612c3306c00,0x9ae7365862b910b3b4cf,0xbe58623cd226be58e038,0xf36b9c8be586244d22a,0x6b65863211ae6be19633,0xbe24eb9ad8658ce38fae,0xe5862b9049136b9c9960,0x326b9cf92d86248c26b9,0xe26b9e58e0b1249]]
def g247H9 := limbs80 #[#[0x5a000000000000000300,0x0,0x22e7400000000,0x50c00401c800000,0xa3d2532e8e044002a400,0x18e87000000000600000,0x185c31090000000000,0x62b4d,0x181,0x24400000,0x9080000000]]
def g247D10 := limbs80 #[#[0xff58ffd53ef993bd64,0x180f6a1c719407805229,0x8bd66624a1122d43965,0x2d5990f28c]]
def g247H10 := limbs80 #[#[0x30008343e579001a9803,0x1e273fc31145a,0x1a]]
def g247D11 (j : Nat) := if j=0 then 0xec8a642047f else 0
def g247H11 (j : Nat) := if j=0 then 0x2900019800069f80 else 0
def g247L : Nat → Packing
  | 6 => (7,5,4,0,0,6,0,g247D6)
  | 7 => (18,4,4,0,0,8,0,g247D7)
  | 8 => (18,3,4,0,0,10,0,g247D8)
  | 9 => (11,2,4,0,0,10,0,g247D9)
  | 10 => (4,1,4,0,0,8,0,g247D10)
  | 11 => (1,0,4,0,0,0,0,g247D11)
  | _ => emptyPacking
def g247I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 2 17 0 8 3 1 g247H7
  | 8 => lookupWord 6 199 1 10 5 1 g247H8
  | 9 => lookupWord 5 89 2 10 5 1 g247H9
  | 10 => lookupWord 3 17 4 9 4 1 g247H10
  | 11 => lookupWord 1 11 0 7 2 1 g247H11
  | _ => fun _ => none
def g247 : Forest := ⟨247,11,fun i => g247Y[i]?.getD (0,0),g247C,g247A,g247L,g247I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P6_0 : block g247 6 0 7=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g247B6 : block g247 6 0 7=true := g247P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P7_0 : block g247 7 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P7_2 : block g247 7 2 16=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g247B7 : block g247 7 0 18=true := (@block_merge g247 7 0 2 16 g247P7_0 g247P7_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P8_0 : block g247 8 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P8_2 : block g247 8 2 11=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P8_13 : block g247 8 13 5=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g247B8 : block g247 8 0 18=true := (@block_merge g247 8 0 2 16 g247P8_0 (@block_merge g247 8 2 11 5 g247P8_2 g247P8_13))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P9_0 : block g247 9 0 7=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P9_7 : block g247 9 7 4=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g247B9 : block g247 9 0 11=true := (@block_merge g247 9 0 7 4 g247P9_0 g247P9_7)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P10_0 : block g247 10 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P10_2 : block g247 10 2 2=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g247B10 : block g247 10 0 4=true := (@block_merge g247 10 0 2 2 g247P10_0 g247P10_2)
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
def g251Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x74d875c5041000000,0xff00000000ff00ffff])),(BitVec.ofNat 152 (word80 [0x49031c1041212121,0x21212121212121212121]))),((BitVec.ofNat 152 (word80 [0x60a346a9e849000000,0xff000000ff0000ff0000])),(BitVec.ofNat 152 (word80 [0x60a30608c8010b0b0b,0xb0b0b0b0b0b0b0b0b0b]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x210085aeba20000ff,0xff00ff000000ff])),(BitVec.ofNat 152 (word80 [0x2100042e882060606,0x6060606060606060606]))),((BitVec.ofNat 152 (word80 [0x4a78b000a4be00ff00,0xff00000000ffff00])),(BitVec.ofNat 152 (word80 [0x210a00024be141414,0x14141414141414141414]))),((BitVec.ofNat 152 (word80 [0xa522fe2403b0000000,0xffff000000])),(BitVec.ofNat 152 (word80 [0xa522fc200330d8d8d8,0xd8d8d8d8d8d8d8d8d8d8]))),((BitVec.ofNat 152 (word80 [0xbc0950031552ff0000,0xffffff0000000000])),(BitVec.ofNat 152 (word80 [0xc0850011140606060,0x60606060606060606060]))),((BitVec.ofNat 152 (word80 [0x919621a01a05ffffff,0xffff0000000000000000])),(BitVec.ofNat 152 (word80 [0x910400a00200808080,0x80808080808080808080]))),(0x0,0x0)]
def g251C : List ColumnInfo := [(1,0,250,0,10),(8,0,243,0,10),(16,0,235,0,10),(32,0,219,0,10),(64,0,187,0,10),(0,32,210,9,9),(2,0,249,0,9),(128,0,123,0,9),(18,0,233,0,7),(144,0,107,0,7)]
def g251A : List (List Nat) := [[],[48,100]]
def g251D9 := limbs80 #[#[0x41aa03eeb8ac7b758d61,0x888cf1c34247273c709b]]
def g251D10 := limbs80 #[#[0x4525c03fd61ef593dd63,0xe72ca9180c9158f38c28,0xd33c612a0]]
def g251H10 (j : Nat) := if j=0 then 0x3c00 else 0
def g251D11 (j : Nat) := if j=0 then 0xec208463ff else 0
def g251H11 (j : Nat) := if j=0 then 0x4372 else 0
def g251L : Nat → Packing
  | 9 => (2,2,4,0,0,6,0,g251D9)
  | 10 => (3,1,4,0,0,7,0,g251D10)
  | 11 => (1,0,4,0,0,0,0,g251D11)
  | _ => emptyPacking
def g251I : Nat → Nat → Option (Nat × Nat)
  | 10 => lookupWord 1 3 0 5 1 0 g251H10
  | 11 => lookupWord 1 3 0 6 2 0 g251H11
  | _ => fun _ => none
def g251 : Forest := ⟨251,11,fun i => g251Y[i]?.getD (0,0),g251C,g251A,g251L,g251I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_0 : block g251 9 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_1 : block g251 9 1 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B9 : block g251 9 0 2=true := (@block_merge g251 9 0 1 1 g251P9_0 g251P9_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P10_0 : block g251 10 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P10_2 : block g251 10 2 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B10 : block g251 10 0 3=true := (@block_merge g251 10 0 2 1 g251P10_0 g251P10_2)
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
  · exact g251B9
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
def g253Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfe4010db9140de7c02,0x4000003f00000003ffff])),(BitVec.ofNat 152 (word80 [0x10131040c66400,0x49249249249249249249]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x72610a6f2a3522a,0x40000fc0000fc0fc0000])),(BitVec.ofNat 152 (word80 [0x2c042410a68283522a,0x430c30c30c30c30c30c3]))),((BitVec.ofNat 152 (word80 [0xff049c84c8831692f0,0x8003f00003f03f00003f])),(BitVec.ofNat 152 (word80 [0x49040480c883101230,0x82082082082082082082]))),((BitVec.ofNat 152 (word80 [0xf82cd2deac000027,0x80fc0000fc0000000fc0])),(BitVec.ofNat 152 (word80 [0x70482cc0cea8000027,0x86186186186186186186]))),((BitVec.ofNat 152 (word80 [0x116a6d083f8928e4,0x3ffff000])),(BitVec.ofNat 152 (word80 [0x80114a6c003c0808c4,0x34d34d34d34d34d34d34]))),((BitVec.ofNat 152 (word80 [0x2e552b025400c55c,0xbf000000ffffc0000000])),(BitVec.ofNat 152 (word80 [0x22510b0054008440,0x18618618618618618618]))),((BitVec.ofNat 152 (word80 [0x191c1206588680781,0x7fffffff000000000000])),(BitVec.ofNat 152 (word80 [0x9180200100280180,0x20820820820820820820]))),(0x0,0x0)]
def g253C : List ColumnInfo := [(8,0,245,0,10)]
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
def g254Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffb2416914027c674e,0xc8000000fc0000fc003f])),(BitVec.ofNat 152 (word80 [0xa20416904023c2642,0x48145145145145145145]))),((BitVec.ofNat 152 (word80 [0x4808bf623d142349,0x2a00003f00003f000fc0])),(BitVec.ofNat 152 (word80 [0x330808bf003c142309,0xa0c30c30c30c30c30c3]))),((BitVec.ofNat 152 (word80 [0x39b32f0c60138523,0x3000fc0000fc003f000])),(BitVec.ofNat 152 (word80 [0x5c39b12f0420118103,0x20c30c30c30c30c30c3]))),((BitVec.ofNat 152 (word80 [0xff949c4c97ac4e9988,0x203f00003f00000003f])),(BitVec.ofNat 152 (word80 [0x6014980412ac428988,0x228a28a28a28a28a28a]))),((BitVec.ofNat 152 (word80 [0x652c2fb4a934e42,0x3200000000000003ffc0])),(BitVec.ofNat 152 (word80 [0x80064240fb42824c40,0x30f3cf3cf3cf3cf3cf3c]))),((BitVec.ofNat 152 (word80 [0x8a90580d3a05810,0xbdfc000003fffffc0000])),(BitVec.ofNat 152 (word80 [0x8041005010,0xb1410410410410410410]))),((BitVec.ofNat 152 (word80 [0x674430492480a0b5,0x54fffffffc0000000000])),(BitVec.ofNat 152 (word80 [0x4204004900800024,0x4820820820820820820]))),(0x0,0x0)]
def g254C : List ColumnInfo := [(4,0,250,0,10)]
def g254A : List (List Nat) := [[],[118],[50],[50,118],[65],[65,118],[65,50],[65,50,118]]
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
def g255Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x7f8000000000007f,0x807fff84102435b0438a])),(BitVec.ofNat 152 (word80 [0x909090909090909090,0x90909084002415b00182]))),((BitVec.ofNat 152 (word80 [0x7f800000007f800000,0x7f8000086838c8319b06])),(BitVec.ofNat 152 (word80 [0x858585858585858585,0x85858580202840109b02]))),((BitVec.ofNat 152 (word80 [0x800000007f80007f80,0xc001c61c06])),(BitVec.ofNat 152 (word80 [0x838383838383838383,0x83838380004000c20806]))),((BitVec.ofNat 152 (word80 [0x7f80007f8000,0x7f8001000008200f])),(BitVec.ofNat 152 (word80 [0x30303030303030303,0x303030000000000000c]))),((BitVec.ofNat 152 (word80 [0x7f800000000000,0x7fff80118e030e0fc1b4])),(BitVec.ofNat 152 (word80 [0xa0a0a0a0a0a0a0a0a,0xa0a0a008201020f4004]))),((BitVec.ofNat 152 (word80 [0x7fffff,0x80000061f003f00ffe00])),(BitVec.ofNat 152 (word80 [0x6c6c6c6c6c6c6c6c6c,0x6c6c6c61f003e00df600]))),((BitVec.ofNat 152 (word80 [0x7fffffff800000,0x7e0003fff00051])),(BitVec.ofNat 152 (word80 [0x303030303030303030,0x303030240002b5200001]))),((BitVec.ofNat 152 (word80 [0xffff80000000000000,0x7ffffc00000060])),(BitVec.ofNat 152 (word80 [0x404040404040404040,0x40404043559000000000]))),(0x0,0x0)]
def g255C : List ColumnInfo := [(4,0,251,0,12),(8,0,247,0,12),(1,0,254,0,11),(2,0,253,0,11),(16,0,239,0,11),(32,0,223,0,11),(64,0,191,0,11),(128,0,127,0,11),(0,32,210,13,10),(1,32,210,12,9),(4,32,210,9,9),(18,0,237,0,9),(33,0,222,0,9),(96,0,159,0,9),(130,0,125,0,9),(0,2,45,208,8),(3,0,252,0,8),(17,0,238,0,8),(34,0,221,0,8),(48,0,207,0,8),(65,0,190,0,8),(66,0,189,0,8),(80,0,175,0,8),(129,0,126,0,8),(144,0,111,0,8),(160,0,95,0,8),(192,0,63,0,8),(2,32,208,13,7),(16,2,45,192,7),(16,32,194,13,7),(50,0,205,0,7),(64,2,45,144,7),(64,32,146,13,7),(128,2,45,80,7),(128,32,82,13,7),(19,0,236,0,6),(80,2,45,128,6),(82,0,173,0,6),(98,0,157,0,6),(112,0,143,0,6),(144,2,45,64,6),(146,0,109,0,6),(192,2,45,16,6),(194,0,61,0,6),(51,0,204,0,5),(67,0,188,0,5),(81,0,174,0,5),(114,0,141,0,5),(131,0,124,0,5),(145,0,110,0,5),(208,0,45,0,5),(208,2,45,0,5),(210,0,45,0,5)]
def g255A : List (List Nat) := [[]]
def g255D7 := limbs80 #[#[0xc2f0ef11a95d5645c160,0xd64d537b42c5985d5645,0x31830edaeba4e459061]]
set_option maxRecDepth 16000 in
def g255D8 := limbs80 #[#[0xe0a06d3975e91915c140,0x65d570502ed9d8b4cba2,0x361d0aecba28174eed19,0x63b7a4285985d9409b7,0x570583e1cbaac8a0ae0b,0xbab28b82c1b1ee997564,0xb5b75917150560d8f74c,0x5c3e1abaac8b0a82b85c,0x22b22e154fed1985d561,0x56839159170cb72e8d07,0xabbd8b30baac8b865797,0x8ac355e6c3985d5645c2,0x190e0564b9cf64d2aecb,0xd8742bb2e8b270bd765d,0x972bec9a55d97459265e,0x61d64c76f4848b20c3ac,0x2bc8b0eb243f6ba24590,0x9ec9a5e45875929f3d93,0x40a7cf64c2f22c22ed4f,0xa2c0a07cb9b85d974581,0x1a85d960503e5ccbb4cb,0xa7768cb2eab82817aeed,0xca07cb986681765d140f,0xe45765033ddda341c8ae,0x68d4722bb2811efed1a8,0x6abfa6e91985d940c77f,0x765034dfd3f48cc2eca0,0xb30bb281a3fe9fa6661,0x7a4e85985d940cf6f485,0x39dbd2142cc2eca067b,0xbb281cbde98a1661765,0xe85985d940e3ef4e50b3],#[0x7bd3742cc2eca073b7a4,0x281c7de9fa1661765039,0x985d940e57f4dd2330bb,0x3f4ccc2eca071bfa7e91,0x8efed1a9a617650387fd,0x1940d76f4850b2ec3281,0x2cbb0ca06af7a6285976,0xe9ba165d865035dbd274,0xd57f4dd232ec3281abd,0x30ea06bb7a42859661d4,0xa1659875034fbd3942cb,0xef4fd0b2cc3a81aede93,0xa869bfa7e919661d40d3,0x8541543b5acbac8b0a82,0xeb22c2a0aa1bad69d645,0xcb5765d16150550bd6b6,0x15436dad3ae8b0a82a87,0x2e2a0aa1d3d65d765854,0xb75917150550f96aecb2,0x3adacb2e8b8a82a85db5,0xa0aa176ded9745c54154,0xd96450550e9eb2cbb2e2,0xecb2ecba282a874bd975,0xa11fdec5a95d941543a5,0x158550f96ae8b22e2b0a,0x728b8ac2a85cf5b75917,0x3ded1765c561543a7abb,0x150e97b2eba2c8b0aa17,0xba2c8a874bd765d39159,0xc5765d16454365ebb742,0xf97370ba2c8b82c172fe,0xe0b07c79a95d5645c160],#[0x45d170582f5dda352b22,0x768d42e8b82c1f2e6998,0x7cb9876817459160bb7,0x174583e5cbb308c82e8b,0xcb308ba2c1e6e61d8464,0xbfb4661765d160f17b0e,0x5834dfd3f48cc2e8b05c,0x30ba2c19ede90a166174,0x6e85985d160cdef4c50b,0x35fd3748cc2e8b066f7a,0x3ac1c6fe5fa461d84583,0x59461d60d76f4850b28c,0xd3942ca30eb06af7a628,0x1abde9ba1651875834fb,0x61d60d3ef4fd0b28c3ac,0x4cca30eb06abfa6e5194,0xf61975591415c347fd3f,0x70f9730cba320b22e1f0,0x8ac8b87c79865d590591,0x1865d5645c32bed42ebc,0xa7f68cc2eab22e1f0fed,0x8b87574b16617559170b,0x5d5645c3abbd8b30baac,0x4dd2330b22e1d4fed198,0x67b7a42859859170d57f,0x645c32fbd3942cc2c8b8,0x2330b22e197de9fa1661,0xfb46197561170cb7f4fd,0xc2ebbd8b2cbab08b8793,0xcbaae174fed1965d5845,0x691865d570ba7f68d0b0,0x5fda341c8aecb25d77b1],#[0xac9cede9091641875933,0x9061d64e5ef4c48b20c3,0xd122c830eb271f7a7245,0xcede9391641875929fb5,0x1d64e5ef4dc8b20c3ac9,0x2c830eb271f7a7e45906,0xe9ba4641875929fb5d72,0x4d37f4fd2320c3ac9aaf,0xaecba68ffa7e999061d6,0xc2980f40032dfda341c8,0x9c89007b46c05cc4d838,0xd50e0fc0e74d28bdcae8,0x978d6c55fd5094152f51,0xb4dadda6da299b98f182,0xa5c61c49c31c19ba9b65,0xde69e25db5d71d2dce9c,0x46001fbdf79f35ef1ea,0xf61b216e12a0e60ce08a,0x63e63a23322c227e20e1,0x5c257e50e4f64b246e45,0x7272e6ea6d268e64a632,0xa9ba9768da8127fa7b67,0xc72c2ebbeb4eadea6ea2,0xcad86d6ed56d12ccecb6,0xaf0aef2edae96e52e0ed,0x1ef1ab13b0cb086feaf7,0x7335b3172d32bb2a325f,0x358f54b4db46b4273b73,0x76b7276e369f65b6175d,0x184fc11787b8377f37af,0xa13817c0f824ec3067f0,0x13f04531e53f84e07b8d],#[0xbb87f03e08e0cee37c0c,0xdc3f81f045623b184780,0xa2fc09960abe08bd1fe2,0xf823dc5f800c3e083315,0x331019dc5191b13e0417,0x4fc0f820cc6f8bf03e08,0x8147c0d13f04506910dc,0xd1a0780ed87f03e08fd1,0x8865cc4ec3f81f04732f,0x7e8dd13e0689f823f46e,0xf46e88a27e07c118a7e8,0x231c9e0672be0c3314a7,0xf82319af8a03b07fc0f8,0xc18662e16f8a02c67fc0,0x2fc0f8370c5393c10e57,0x8227c5065f03e089d1fe,0x4b8a727e087714e49caf,0x45e183312e29c9395f04,0x9c204050150845020280,0x9b0c2d86081411238571,0x20cc17800bc004000003,0x10660dc3066103304198,0xd0106608330419820cc,0x80f0017800bc0076382,0x60403c005e002f001d8c,0xd8c08c60430822021198,0x42182004661810440425,0x8c09860211fc60400470,0x3e30100218213810023e,0xe1833100f180d8c04220,0x2808177860cc302e051,0x85419220405c188e4502],#[0x291d2205a18a204a18a3,0x3c005e0020144040d0,0xbc005e002f00158808,0x390e51024960a8200078,0x83451020420a1490ed10,0x820cca1840cc12ada1c2,0x1440407800bc00400019,0x82c35b1824300e18e881,0x408320419020101c35b1,0x106408320419020c8106,0x10206608330419820c8,0x9e]]
def g255H8 (j : Nat) := if j=0 then 0x809a80 else 0
set_option maxRecDepth 16000 in
def g255D9 := limbs80 #[#[0x7450110f6c5d17150110,0xfac5914158110e6e61d,0x1415c110f3c5d9715811,0x10f5c5d5415c110f6c5d,0xd5845c110e6e611745c1,0x110e5e5d7845c110e5e5,0xe19755c110e5e619755c,0x510ead6196450510e5e,0xd611745c510e6d61d745,0x5d910e3d619765c510e6,0x2e5d974581408efe9198,0x15c140d6e65d7458140f,0xe5e5d7815c140e6e5d38,0x745c140d6e5d3915c140,0xe6ee19745c140e6e619,0x9755c140d6ee59745c14,0x40e5ee19755c140e5e61,0x85985d940e2f619765d1,0x160e5e5d7815c1608fde,0x5d5645c160f2e5d1645c,0x9160e5e5d7845c160f1e,0xd5939058541e2f61d745,0x58541f8d5d56458541da,0xad61d6458541f8d9d564,0x458541dad65d6458541e,0xbad69d6458541dade5d6,0x7458541bade9d6458541,0x1d6d65d7458541f2d5d9,0x9645c541e3d61d765854,0x41b6d69d645c541f2d5d,0x99745c541e6d619745c5,0x141e3d619765c541b6de],#[0x619765d141e2f61d7659,0xd941a5fe9d865d541e2f,0xd5d971e01618fde85985,0x5c561f2d5d1645c561e3,0x3d5db845c561b3d69d64,0x459161b3de91765c561e,0xe2f5d974e0164e2f61d7,0x915d164e2f5d974e0564,0x4b2fe81765d164d2f5db,0x596e0174b2fe85765d16,0x10f5e5d5945c1108fde8,0xd17158140f5e659755c1,0x140f3e5d97158140f6e5,0x6997458140beee919158,0x8140f6e65d7458140fae,0xee998758140bbee99875,0x58140beee919758140eb,0x6e5d1615c140deee9197,0x15c140f5e5d5615c140f,0xf5e5d5815c140f6e5d18,0x915c140f6e5d1915c140,0xf5e5d5915c140beee91,0x9745c140f6e685745c14,0x40f6e659745c140f6e61,0x19755c140f6e699745c1,0x140f5e659755c140f5e6,0xe9d865c140b7ee9d865c,0x8540beee91965c140e7e,0xd5d97158540f6d5d1715,0x58540f2f5d97458540f3,0xefe919858540d6f65d74,0x15c5409ef69398585409],#[0xe6f619745c540f6d5d18,0x765c540e6fe19745c540,0x9efe91985c540e3f619,0x5765d140f6e681765d14,0x40f2f619765d140b6fe8,0x9d865d140b6fe9d865d1,0x940bede85965d140e6fe,0x6a3915d9409fe683915d,0xd940e3fe9d865d9408ff,0xfe9d985d940abfe99985,0x5d9409fde85985d940a7,0xfd285985d9409efe9198,0x85d940cfde85985d940c,0xcbfe99985d940cefe919,0x985d940c7fe9d985d940,0xa7f69e985d940abf69a,0x3985d9408ff6a6985d94,0x409ef693985d9409fe68,0x5d8761940abfe9987619,0x940aefe919161940c7fe,0xe919761940afde859761,0x1d40aefe919161d40aef,0xfe919661d40afde85966,0x50550fad5916150550ae,0x3d5d97158550f6d5d171,0x759150f2f5d97459150f,0xfae591415c1609fde859,0x415c160f6e5d1415c160,0xf5e5d5815c160f5e5d5,0x5915c160b7ee9d815c16,0x60bbee99915c160f5e5d,0x99745c160f6e611745c1],#[0x160f5e5d5845c160f3e6,0x5d5945c160b7ee9d845c,0x560bbee99945c160f5e,0xd5d17150560fad591715,0x50560f3d5d97150560f6,0x8f5d56450560fad59181,0x450560f8f9d56450560f,0xeafe1d6450560eaf61d6,0x6450560daf65d6450560,0xbafe9d6450560baf69d,0xd7450560f2f5d9745056,0x60d3f65d7650560e6f61,0xd1645c560f3d5d9815c5,0x560b3f69d645c560f2f5,0xe91765c560e3f5db845c,0xc5609efe91985c560b3f,0xfe5164605609bfe99985,0x60560d3fe5d7660560da,0xae6817459160c7fe5d87,0x459160bafe857459160f,0xbafe918759160f2f61d7,0x9759160eafe918759160,0xdbd2859759160bbde85,0x9905d160dbde85975916,0x60dbe659905d160f3e5d,0xdb915d1609fe683915d1,0x1609bf69b915d160d3f5,0x5d9845d1608ff6a3915d,0xd160e6f61d845d160f2f,0xfe91985d160e6fe91875,0x5d160a7fe9d985d160ae,0xbfe99985d1609fde8598],#[0x85d160aef692985d1609,0x9fe683985d160a7f69e9,0x76611609bf69b985d160,0xc7fe5d8761160d3fe5d,0x19161d60bbde85945d96,0x60abfe999161d60aefe9,0x999461d60afde859461d,0x570fad5916150570abfe,0x5d56150570f6d5d16150,0x570f6d5d18150570f5d,0xf5d56450570f5d5d5815,0x50570e6fe197450570f4,0x5f6597550570d6f65974,0x458570d5f6617550570d,0xf1f5d56458570f2f5d16,0x9458570cefe538458570,0xd5f6617558570d5f5d7,0x19858570d5fe61755857,0x7097fe9d98585709efe9,0x51746057097f69f98585,0x570e5f5d58460570d6fe,0x6197560570d5f5d79460,0x9170d5fe597560570e5f,0xe5d59059170f6e5d1905,0x591709fe6839159170f5,0x5f5d79159170d6f5d391,0x4591708ff6a39159170d,0xf1f6197559170f2f6197,0x7559170d5f6617559170,0xaefe919859170d5fe61,0x59859170abfe99985917,0x7097fe9d98591709fde8],#[0x9a9859170aef69298591,0x1709fe6839859170abf6,0xe91865d17097f69f9859,0x1170b7de85965d170b6f,0xf6197561170d5f5d7916,0x5d570d5fe597561170e5,0x5fe91865d570b5fe8586,0x458541fad6816458541b,0xf6d681745c541fad5d56,0x745c541f6d595745c541,0x1abfe998759541f6d695,0x1765c561f3d5d9545c56,0x61f3d695765c561f3d68,0x89955d961aefe9187551,0x164b7be89955d971bbbe,0xe5d7460164f2f5d97460,0x164d3fe5d7660164d6f,0xfe5d8760164afde85876,0xe0564cef5d190e0564c7,0xdf9d590e0564cdf5d590,0xe0564cbf5d990e0564c,0xf2f5d9905d1648ffe9d9,0x855d164bafe99905d164,0x4f2f5d9955d164f2f5d9,0x1765d164bafe99955d16,0x64f2f695765d164f2f68,0x91905d964afde8587615,0x9649bf683915d964bafe,0xe91955d964bbbe89955d,0x1d64cfd2459061d64baf,0xfe919061d64cfde45906,0x61d64abfe999061d64ae],#[0xff6839161d64cfd65791,0x161d64cfd6839161d648,0xafbe899561d64cfd6979,0x9561d64aefe919561d64,0x4d3fe597660174abfe99,0x990e0574afde85866017,0x74d3fe5976615748ffe9,0x91905d974afde8586615,0x97497f683915d974b6fe,0xe91955d974b7be89955d,0x576afde858460176b6f,0xfe9190e0576afbe89856,0x61176cfd61791611768f,0xee6a57458140afbe8985,0x758140fbe6a17658140f,0xfeee91965c140feee919,0x765c540f6f619745c540,0xf6f6a1765d140f3f619,0x9905d940feee91905d94,0x409ff6a3915d940fbe61,0x91985d940befe91985d9,0x940ebfe99985d940eefe,0x285985d940e7fe9d985d,0xd940dfde85985d940dfd,0xfe919161940defe91985,0x61940bfde859761940be,0xfd2859761940befe9197,0x761940efde859761940e,0xebfe999761940eefe919,0x9661d40befe919161d40,0xbefe919661d40bfde85,0x59661d40efd2859661d4],#[0x40eefe919661d40efde8,0xd16150550e7fe9d9661d,0x550fbd5d96150550fed5,0x69d6150550dfd65d6150,0x550fed5917150550bfd,0xd6597150550f7d5d9715,0x50550faf5d96450550df,0xef69d6450550def65d64,0x450550f6f5d97450550b,0xbefe997450550def6597,0x7650550dbf6597650550,0x9ff6a57650550d7f65d,0x171585509ffe99975055,0x50f7d5d17158550fbd59,0xd16458550dfde5171585,0x550dbf65d6458550faf5,0x5d97458550bbf69d6458,0x8550d7f65d7458550f3f,0xf69f9458550dbf5db945,0x58550bbfe9176585509f,0x6f5d1645c5509ffe9197,0x45c550f3f5d9645c550f,0xb7fe99745c550b7f69d6,0x9159150b7fe91765c550,0xdbf5db9159150def5d3,0x574591509ff69f915915,0x50bbfe857659150befe8,0x859759150bfde8597591,0x150dfde859759150dfd2,0x5db915d1509ffe859759,0xd1509ff69b915d150d7f,0xde85965d150b7fe85765],#[0x5d9509ff687965d150bf,0xfde85945d9509ff69391,0x45c1609ff687945d950b,0xf7e6a1745c160fbe6a56,0x7450560faf61d6450560,0xf6f611745c560f6f61d,0x17459160f3f5d9845c56,0x60fafe918759160faf6a,0x1d905d160fee611905d1,0x1609ff6a3915d160f7e6,0x661765d160faf659845d,0xd160f3f61d965d160f3f,0xfe91985d160f6fe91875,0x5d160eefe91985d160be,0xfd285985d160e7fe9d98,0x85d160dfde85985d160d,0xdbfe99985d160defe919,0x9761160eefe918761160,0xbefe919761160bfde85,0x19161d60bbfe99976116,0x60bbfe999161d60befe9,0x999461d60bfde859461d,0xd60efd2859461d60bbfe,0xe519461d60efde859461,0x1d60ebfe999461d60eef,0xf6196450570e7fe9d946,0x50570f6f6197450570fa,0x5f5d58458570f5f61975,0x159170fbe6199059170f,0xf6f66174591709ff6a39,0x8659170f5f6617559170,0xbefe919859170fafe91],#[0x99859170eefe91985917,0x70dfd2859859170ebfe9,0x919859170dfde8598591,0x170d7fe9d9859170defe,0x5d59161170f6fe91865d,0x1170f5f6597561170f5f,0xde859661170eefe91866,0x61170befe919661170bf,0x5f685865d570b7fe9d96,0x65d570f5fe85865d570f,0xf5fe91865d570f5f6918,0x9161970befe919161970,0xbfde859461970b7fe9d,0x19760164b7fe9d946197,0x64bbfe999760164befe9,0x91905d964cff69d90e05,0xd64eefe919061d64fafe,0xe9d9061d64ebfe999061,0x174befe919660174e7f,0xf69990e0574b7fe9d966,0x60176f6fe91905d974cf,0xbfe999460176eefe5184,0xe0576b7fe9d9460176b,0xcffe9190e0576cff6919,0xe013001c802600260000,0xb18142024c041406d00b,0x8700fb01d0035406100,0x305fa0b7015b027c048e,0x703e8075c0e0c1ac032,0x13d0262048f08dc110c2,0xe0b5016302b3054f0a34,0x3706480c62182c2fa05c],#[0x1c8837e06db0d741a503,0x60fb61efc3cc87730e9a,0x55888a10d2210c40e880,0x26084a6892c120c23444,0x6147628544fa09d31350,0x998b1215ce2ac85460a6,0x30145ef8bb917262d8c5,0xd1990329c6408c561860,0xf18db31b1035606990cf,0x3a7073d8e551c7238246,0x61eaa3cd07820eed1d8e,0x2410181fda3ef47cb8f7,0x447c87a10ba211441a48,0xd23ba46a08c111612280,0x59129624ea4950917120,0x4e249b1933325fc4b4c9,0x528ac50d4a0513d0275e,0xa715282a0e5398a62949,0x581caee15b62b205594a,0x42da85ab8b3c96532c5a,0xe897ab2f1e5d90b9a170,0x6200c2f983e303a5fb4b,0x532686460c7918d13142,0xc19f233a266d4cc2995,0x6af4d509a8534be68f8d,0xb370a6d90d9a1b0935bc,0x399c4d38447004df01ba,0x75b4e9e9d0d39ba72c8e,0x3c607828ef49dc83b4e,0x941f073dae7a88f409e6,0x7ffcfe01f9f3ef27d24f,0x941708221033a04b404a],#[0xc1a15d4282845907aa0d,0x88b5103a1e6438a86910,0x845a48ad914aa26f4492,0xdda39046c08cfd18ca2f,0x929923b2446484a8fe91,0xa4ac8950d29124f74998,0x2e262c4bee976d2dd258,0x9c9137f26d34d6499f53,0x94fb09ec93c8a7704e8a,0x4f288250b8a0ed40aa7f,0xa521493a8fc51c0a3114,0x65416a7814d8299452d2,0x7caadd5578aa45535aa3,0xaec95c62b665676ac695,0xd58b8b1016122c0857a6,0x9b2d0b59b6b2c164cac7,0xb7316d5ad945afab5856,0x55d0ab99171f2e1d5bee,0xb22f345e3abbc9768aeb,0xbfad7ecafc75f56be3d7,0x660a8c11d813300f5ffa,0x58b0a4612ec229839b06,0xc419877b0d8618cc2e58,0xd62acc51189931256230,0xe131b06346c6598c2316,0xc8218fdb1ee63c2c7518,0x16488c8dd917b222642a,0x49328564f0c9ad92f325,0xcb6196832c3656cca919,0x26614cc0997d32ed65c0,0xa4b3416672ccb198fb31,0xce019b9b36666b2cd459],#[0x8678ccee59d6339f6724,0xf340c6808cfc99f2b3d,0xd1b9a2bb44a687ad0ada,0xe69a4d301a57349c6914,0xa435366a48d449a8034e,0xd6edad4b5886aecd591a,0x46beed7a9af135d56b9a,0x36b6566c7ed8b5b0db60,0xdae1b5836a36d2cda11b,0xf6e1adbedb74b6d26d8a,0xc937806ec8dd0db98b71,0xdf89beab7cd6f76dea5b,0x97082e0a9c04b7f76fd4,0x5938a57108e1c9c30384,0xe4a9c89b8fc71cae339c,0x17308e5c9cb0394e7278,0xf0b9cf737ae6adccf399,0xe8c5d123a127400e7cdc,0x70608ef1709f03c10907,0x87013c523b09f03c1090,0x907c27c545024f03c10a,0xa8723bc5c245af03c10,0x10a85c27c545c28f03c1,0x28f03c10a88a2d09f03c,0x7c0f042a1b0901fc585c,0xd09f03c10cc50668b42,0x3180771a09f03c10a06e,0xc1484771b83827c0f043,0x3c147c7e27c582f82f03,0x3c147c7e27c501382f0,0xf03c14707e2407f1782f,0x2d1fc0f048e27c583b82],#[0xc0f04332b89f1746e0f8,0xcba13c3c0914847c5c27,0x346f0fc5c2684f03c10c,0x5c28f03c10a8705f0245,0x427c0847c10a86c27c54,0xb51fc5c27c0f04241c0e,0xc3f170991fc0f0433280,0x411f03c10cc80451471b,0x5fc0f043323c371b09f1,0xf03c10ccbf0dc6c27c50,0x4511191dc6e13c385e09,0xaf0dc682433f03c14447,0x11f0e47f1789f03c10cc,0xb84e0b47f03c12382251,0x27c0853c10a06e27c5d1,0x853c5c27c0f0433280e4,0x427c10cc9a1bc3c0917,0xc18507a1ac4f0d17853c,0x3c10ccaf0c33426c4f03,0x38225d14f0fc591389f0,0xf03c10cc7b0bc0f04341,0xf05210bc50d1c580dc9,0x6f17c2f03c10d0780fc,0xfc5013c2f03c10d0743c,0xf04331d21f03c10bc443,0xf042f1034f1403f0bc0,0xbf17c2f03c10d07487c,0xfc5013c2f03c10d07084,0x3c06f17c2f03c10d0743,0x31bc5f082af03c109064,0xc10d07f1403f0bc0f043,0x20bf04843fc501fc2f03],#[0x4341fc5f0818839c6f0,0xf04241d0f01fc5f0bc0f,0xf04341fc5e0fc20abc0,0xc0f04a5142101fc5f0bc,0xf46e1347f03c12021d27,0x1f42f03c10d04f17c203,0x31c1c03bc5f0bc0f0434,0x1c1834f1403f0bc0f043,0x3c14706f17c20afc0f06,0xbc0f04341fc5f082bf0,0xd0816f03c1281cf1404f,0x10a0708417d27c5093c3,0xc10906f1743f082af03c,0xbc006bc12bc5f082af03,0x90707011727c50abc370,0xf048f15c3f0828f03c10,0x31b42f1749e12c6e1fc0,0xc10cc605f83427c0f043,0xbc0f04331c17e0e09f03,0x3bc0f04242111c274533,0xb7c10cc74501ac27853,0x9f03c10cc744709f17c0,0xc00cfc1450a059148470,0x6112211f17c305f09a13,0xc460cfc545309f02c7f0,0xf061425c8f1433f03c10,0x1243385d11c27c5b1fc0,0x3722c785fc585184f03c,0xc8b0d02f03c10a0341c3,0xd17b0d09f03c10a0341d,0x23c5b0f09f03c108c331,0x45e10b0d09f03c10ce23],#[0x8043c5c244ef03c10cc7,0x11042c3c27c5f03c10cc,0xa8405c4e427c0f04331d,0x44a70f09f03c10a4331,0x453c5f0f0991fc00cfc1,0x3c2684f0033f041729c6,0x2f03c10cc771914f17c,0xe09f03c14449715c3c27,0x417e10885d1491fc30c,0xf061125c670e09f0033f,0xe1c33f151785309b1bc0,0x172414723c50cfc0f042,0x3385111c26c6f17c0f06,0x4331fc5073c0f043414,0xf043318430d3c5e27c0f,0x2f03c107080d3c5e0bc0,0xc0f04281fc526011d1b8,0x3c10b0341048f1746e0b,0x2547f17c0093c108c9f0,0xf17c093bc109064600be,0x6f1618f03c1244241891,0x4241c94f17c093bc1090,0x433244800bc5f0347f0,0x201444589c1017f17c0f,0xf17118638216bc0f041c,0x9f0fc591fc00cfc14449,0xc5b1bc00cfc184460538,0x609047c5f0033f042e1b,0x4789f141cb1b82f03c18,0xe1445d1fc0b0fc1e10bc,0xcf02c3f0486474603d89,0x33f042e1b4602347f141],#[0x782f03c10cc6053c5f00,0x1fc5e0bc0f04331946f1,0xf1789d1bc0d1c1cf0475,0x6613c3f17c0d1f82f04a,0x33f15c3f03c124331234,0x7c00cfc11b46e1389d1c,0x1fc50cfc0f047e25c3f1,0xf17470cfc0f046d1bc3d,0x5d1b84f1433f03c11b84,0x3c10cc651bc5f03c10cc,0x17c0f04332147f1782f0,0xf03c1244ad1f460d008f,0x1242a627466084ff1747,0x6f15841a848d1fc0f049,0x2e453c50cfc0f06c71f4,0x83125fc50cfc0d1bc11c,0xf04b447c50b7c0f04331,0x70f14c4789e0bc5f02c7,0x30cfc5f02c7f04827316,0xc3f17c0f0433182e447c,0x782d1fc5b1bc0f04c446,0x3c1249cc631170f17e2,0x1831447c3d1c33f16c6f,0xbe30610f88f03c1e302f,0x4ee238c184ef03c1e204,0x3c0f0788e30711bc0f04,0x23c0f0788e30411d4691,0x45016c274532fc0f042a,0x745f09e14cbf03c10cc7,0xc845ec3f0109f06cb0a8,0xe9584117b0d09f03c10c,0x1d17c27c5f002df04331],#[0x31e8605c4e427c0f0433,0x142914c27c5f0030f043,0xc5f0c11c2647f0033f05,0xa1745309f03c10cc785f,0x1fc30cd09f03c1850906,0xc26c4f03c1850945e115,0xcfc1e1890ce11f1517,0xc185c80c6c3b1017427c,0x4241433f1514c27c0b13,0x2fc0f04331fc5f024ef0,0xf024bf042a144ef17891,0x9f17c012fc12502a27c5,0xc06264bf042a19160578,0xa16717c092fc10a8685b,0xa86253c5f024bf042a1,0x7f041f27c585bc0f0494,0x331bc5d0c14e0a16f01c,0xfc10907f1743e0bc0f04,0x3c10cc5f1743e0bc071,0xf17c092fc10a86f164bf,0xe05344e0bc0f041f2497,0x47f03c125024249af144,0xbc0f0433151a05789f15,0x1743e0bc0f04331bc553,0x63c553bc0253c10907f,0x6f1743e081af03c10907,0x4241fc5e27c0d1fc1090,0x4331448f1782f0347f0,0xf17c0f04331743f17c0f,0x825fc5f002df04331b43,0x174518971411f03c10cc,0xf14f161670fc0f045820],#[0xfc5913c00cfc1450923,0xb1fc00cfc1850605f89f,0x5e0a14b1fc0f04331fc5,0xc517382f02c7f06162bc,0x782f03c10c8686b14e27,0x27c5e0bc0f04321b89f1,0x4689b1417f03c10cc8e,0x7722c5847c0f04331c94,0x31d1347b0fc0e1bc1321,0x3c116086500f62785114,0x41f260f653c546ac3f0,0x2448f1744b0f82d1fc0f,0xd1008d1fc507fc0b0fc1,0x3f1547f0033f04942431,0x86053c0f04332c11e27c,0x433191784789f1644e0b,0x3c10cc6f154485fc0f0,0xe0bc0f04331944f1782f,0x9d13c0d1c1ff04751fc5,0x86f0344d1f82f049f178,0x382f03c10cc60cfc5121,0x1fc5e0bc0f04331bc551,0x13f44f1747f03c1250a5,0x2d1fc0f0494242862582,0x33f06141bc51a048d103,0x433f0344f046f1744f00,0x81fb13c0f061a2497f1,0xf17c0f04331f14e27c5e,0x50c3c0f04331b17c5389,0x82d1fc5f02c4f04c453c,0x3c11c9fc6b1470f17e27,0x4331d14f17470cfc0b1],#[0xf043414430d3c5e27c0f,0xb627c0f04341bc5087c0,0xc5513c0f042a25c90864,0x189f064b0a864600ee27,0x1b43627c0f0433140ef0,0x10848f1618f03c125c2a,0x3417c58601771b82f03c,0x289f042a1c21f0289f04,0xbc0f043318291154bf0,0x90d89f03c10cc60d3c5e,0x6f1428f0155f06971834,0x4281d97627c0f06550a0,0x43415440af46f0289f0,0xf0028f06971c21a27c0f,0x6e0bc0f04281f89f1746,0xc5e0bc0f04341848f174,0xcc7f160ef03c10cc5123,0xc0605e44d0d89f03c10,0xf04331c0ef0189f0433,0xc10cc30181751b43a27c,0x7c5f03c10cc903a89f03,0x3c10cc825c14a258704,0xf0787309761e1484489f,0x62746e14450bb44b0fc0,0x8e0856f03c1084865c0f,0x21f03c1626561bc565d1,0x8f16c3f0021f04965c,0x13c00cfc125c90bb46d1,0xcfc125c705389f0fc59,0xce89f04851a89f0344,0x89f05562031d1b4450fc,0x3c10cc65902125fc3f02],#[0xbc0f04331944f1782f0,0xd1b44f03c1084751bc5e,0x7d1bc0d1382f049f1789,0x82f03c10cc60cfc51218,0x946f17c0f043317c5513,0x198213f44f17c0f04972,0x12344f03c125c909189d,0xcfc185c661f46f1464,0xc6e0bc0f06182bc5513c,0x7c10a8686b17e27c5172,0x2744f04332344b0fc062,0xf03c10c470c41771bc0a,0xf06170a0650dc60ce89,0x33c27c0f061722c6c27c,0xbc0f042f0cc6b19c4f0c,0xdc7f07c07242f1b0370,0x70bc5727c082fc10cc78,0x331607f07c082dc97346,0x7c1f03491e0bf03c1724,0x7c0b261e1ac7e1383d1,0x72703f03c10cc741d86f,0x7c0fc1f01c90cc570bc5,0xc5b1f86e0f45f07c0d24,0x2bc18cc53278332bc18c,0xd27c5f03c10cc8327833,0x1d0bc0f04331b4205011,0xc585342f03c10cc6f161,0x311d23c5093c0f06c723,0xf049f1742f03c10cc5c5,0xf142e03ac2e1a0ff01c7,0xfe1b84d0dc7f00c9f048,0xfe11c5f01c7d0fc1220],#[0x99ae1343f01c7f04ae1a,0xfc0f042e1e0ff142eb0,0xb0bc0f04332008f15c7d,0x2f03c10cc605c11b27c5,0x47f07c0b242f17c5846c,0xcc606413f07c0b243319,0xf043322c584cc9f03c10,0x90cc77081405dc9f17c0,0xc1d2470640dc13c1f01c,0x3c10cc6d178447ac7f03,0x2c3e13c12bc5852c2f0,0x8cc513f06f15c2c5b47f,0xdf03c10cc53278432bc1,0x46b23c5f03c10c853260,0x4331410b23c5f0032f0,0xf17c0f043312c2f17c0f,0x7e1b84279c5f07c07248,0x8d1fc503fc0f06c3274,0xb84d1c0ff03c12386e10,0xdc5f07c07248f15c9e1,0x324caf06331747e1b843,0xc10cc4327c0f0433101b,0x617d0bc0f043318c9f03,0x4748f16c6f0028f048f1,0xbc507fc0f04311f17c,0x7d1619527c0f04331808,0xc6e111eb1b45f07c0d24,0x13c127c585ec2f03c10c,0x1707f140b70b4613fc0e,0xf04331b84324caf0633,0xc4f03c10a8861219327c,0x4caf06331317c5348f16],#[0xfc5e1bc0e1ec2f04932,0x71744f07c0724871008d,0x3324caf0633145ee1f86,0x8330c31a11c30b833174,0x852170e17212140dc30b,0x4ed0c241091938240c84,0x81491f0470c310cc6250,0x30702a101451c385e140,0x8910d02053476109112c,0x33083304340cc20d0330,0x5ac344440c42e0cc310c,0xe4443c5b14c4746101c4,0x1c330c330ac70cc24582,0x344440cc2eb1c30cc2eb,0x43c6317c4747101c462c,0x30c330ac60cc24603144,0x20cc31b1830cc31b183,0x40846e30212f8c0855e3,0x1c212f8c084e6302e304,0x8c10c21190c0b8c078c1,0x10c8c0a8c11c212e8c08,0x81d031190c0847e302,0xc084ee3027180c020303,0x844e302e30111c11578,0x202e3011101e30110f8c,0x4e0788e30210f8c080c0,0x210f8c08430443078c04,0x1c0c020371f8c098c71c,0x88e302e33440b46e3027,0xe20210f8ce203e33880b,0x171808e30371b8c0b8c,0x80c0c0202d138ce203d1],#[0x8e302e238c09c40300,0x91dc30cc50b81770c331,0x4b0a832524b0a830c414,0x514e09032464e090325e,0x4850305e4470c2e0cc52,0x8175103a181151c38684,0x91c1625030c6c307c3a1,0x1a25030501191dc30cc5,0x138216068694485c3510,0x30c340c4330c1a05f865,0xcc110c33083304340c43,0x11d10405144082e0cc20,0xb9140d16445440f16c53,0x34504c6b17c534711160,0x3c6b17c5347101f46ac,0x30c330ac40cc246ac445,0xa840cec40833b1020cc1,0xa0c9792c2a0c9412f430,0x1440f43954280f4352c2,0xc433182eb0c210e8705,0x3e08310cc505287911c3,0xd441584868448503a1dc,0xb8330c340b8330c14e1,0xcc20cc110c3308330434,0x50a64b184486a170c310,0x4470c310cc40c021320c,0x5103c6317c4744114407,0xc30ac64603145c346111,0xcc570c2a0830086c6711,0xb1a1a71040c6c6711c30,0xc345c4c6b17c53461017,0x5c3c6b17c5346102146a],#[0xe45834442e458346ac44,0x21486830b94308434502,0x40cc20d03308340cc221,0xd170c5180d110c5180c3,0x3088485e1a0c3150c1f0,0xec44683452c44683b0c3,0x3dc40943070245]]
def g255H9 := limbs80 #[#[0x80049243001283004000,0x23e80000002080,0x2e000000000000000000,0x90000005b20000001b5b,0x28fc2f0000007b,0x37000000211000000000,0x4b48000002,0x5af80000032480,0xaa00000f000000000000,0x200059f0004800000003,0x4b100048d7c,0x68db31800594,0x1368000000000000000,0x199e9a8007c280000,0x0,0x0,0x80000070180000000000,0x197eacf26,0x78000000000000000000,0x5a300000022,0x99000000702800000,0x787b260000000,0x30480,0x2b800000000000000000,0x4,0x2a000000003400,0x23c800000,0x968000000000000000,0x58900000003b80000000,0x0,0x400030c2131900000000,0x111800093800010f8],#[0x31e800000000,0x4228000000000,0xa100000000000000000,0x9c5c180000000003df41,0x7330066be4,0x14080000000000000,0xc000000000063c43f800,0x2a900048761a2,0x0,0x0,0x39b8000000000000000,0x30200000000,0x0,0x59d30e8a18000,0x69880000000000000,0x401000000000000,0xa800000109f1ddad8000,0x7a380023880000000070,0x7b7ca5000000000,0x12580000079c8,0x158000ac00000000000,0xb2e96000000000000000,0x5,0x30b80,0xb0d2831f812800000730,0x6270000000000000005,0x4030000003b600,0xa9f14800000000000000,0x5950000000000000000,0x63d00061258c80,0x7bb0000000004b3800,0xf00000048a6a20000000],#[0x58500000008380023,0x2ab724000000,0xb31800000000048851e0,0x53500038,0x31b,0xeba8000000000000000,0x3ae80000000033a48,0x39800117000000000000,0x88000000000005888000,0x20c8592a80032,0x1b8386d8e3ad000]]
set_option maxRecDepth 16000 in
def g255D10 := limbs80 #[#[0xb72e8b8281d79755c110,0xbcbaae0b075e5d570503,0x6ae8b8a83eb56458541e,0xebb2e8b273d5d971587b,0x2e2a02213f79161d64e5,0xbaa80887ee5d140443fe,0xca0221f7a7550110fbc,0xb280886fee19404437f3,0xea02217fb9650110bfcc,0xa80886fee1d404437f30,0xb02217fb9750110bfccb,0xc0887fc5c560443fe282,0x221bf98458110f7cb22,0x885fee51604437f708b,0x221f7a7558110fbcbaac,0x886fe61d60443df2ecb0,0x217f99758110dfdc3ac0,0x87fc50570442ff72eb02,0x1bf9845c110efcba2e08,0x5fee51704437f708b822,0xbfb865c110dfcc32e088,0xed59141442ff72cb8221,0x757550510fdaba282887,0xd61941443eeceaa0a21f,0x58750510dfbc3282886f,0x65d414437ef0ea0a21bf,0x845c510efaba2e2885fd,0xd9714437ef08b8a21bf5,0x65c510dfac32e28877d5,0x964442fef22b2221bf78,0x5d1109fecc2c8886bf61,0x744433fb0eba221bbd84],#[0x1110dbebab08884ff661,0x44427ff2cc2221b7e756,0x110dbebaf08884ffe5d8,0x4427fb2dc2221b7e75e1,0x10dbec32ea884ff65f84,0x436fb0d3aa21b7f865d5,0xbfbc8aec886dfe1a754,0x27fb30bb221afd865d91,0x9ffcbb0c884ffe518644,0x7fb2fc32213fd94e1910,0xffcb30e884ffe5187442,0xfb2dc3a213fd94e1d109,0xdc8ac0a06fee05605027,0x2eab0281fb97458140bf,0xbb2c0a07de9d560503ef,0xeb0281bf98758140f7c,0xbac0a05fe65d605037f7,0x2b8281bfb815c140bfdc,0x2e0a06fe61970502ff72,0xb8a817fb965c140dfdc3,0x2a06ef5d381503b7ae8,0xa81b7e75e0540dbebaf,0x8a04ff65f815027fb2dc,0x281bbd865d140edebb2e,0xa06df6197550377f0cba,0x81b7d869d540dbfc32ea,0x6bf619765036ff0d3aa,0x13ff91619409fecc2eca,0x4ff647865027ff2ec328,0x3ff9161d409fecbf0ca0,0xff647875027ff2cc3a81,0xfb815c1609fecb70ea04],#[0xe59170582ff722b82c1b,0xb845c160efcba2e0b07b,0x59141582ff728b82c1bf,0x64e0560e7ebb2e2b07af,0xd7815827fb29c0ac1afd,0x6e0560dbf3af02b06df5,0x1645827fb2fc0ac1afd7,0x59160f3ebaac8b07af5d,0x645835fb0eb22c1e7e75,0x9160b7ecbac8b06bfe1d,0x45839faecba2c16ff975,0x1609fec8f08b067f61d7,0x5836fcebc22c1b7d75e1,0x609fecbf08b06bf5db84,0x827ff22c3ac16ff945d9,0x9fec8f0eb04ffe51875,0x3b7ae8a0ae13fd94e1d6,0xebebaac2b875f5d5415c,0x3fae9c0ae1d7d7560570,0xfecb702b84ff653815c3,0xfaeab22e1dbd74591709,0xebab08b867fe19745c3a,0xb2dc22e13fd91e1170eb,0xc8f0cb875f619755c27f,0x20b0a833fd94e19709fe,0xaac2a0fed5d161506fef,0xcb0a83f767558541fbab,0xac2a0efd61d61507deae,0xb8a837f79758541bfacb,0xe2a0f7d5d971507f6ac8,0x2283f3d7559141dfac32,0x8a0faf5d964507e7ceab],#[0x2837bd9759141ddec3ac,0xa0f6f5d974506f7f2eb2,0x837bf965d141ddec32e8,0xedf61a755076fb0cbaa,0x39fd875d941d7ec32eca,0xcffe41865067fb30bb28,0x3ff9061d419ffcbb0ca0,0xff65b845467ff2cc3a83,0xfd97e19519fecbf08a8c,0xd5c7805867fb2dc3aa33,0xd94e0161d7eb2700b0ef,0x9d7805876faebc02c33f,0x97e0161d7ebb700b0edf,0xd171587deac8b8ac33fd,0x459161dfbc22e2b0f7d5,0x564587cfaeab22c3ebd7,0x59161d7ec3ac8b0f9f9d,0x64586dfb2eb22c3aff87,0xd161e7ebb2e8b0dbfe5d,0x45867fb21c22c39fd875,0x161dbf3af08b0edf5d78,0x5867fb2fc22c3afd76e1,0x619ffc830eb0dbfe5176,0x867fb21c3ac33ff9461d,0x1edeba2c8b8cff653875,0x6bfb2eb22e3cfd765917,0xaffca2ecb8d7fe59745c,0x7fb2fc0aa93fd96e0554,0xfecb70eaa4ff65f86552,0x7ae9c02c93fd91e01649,0xf3af00b26df5d7805937,0xb2fc02c9afd76e0164db],#[0xba702b24ff643815927f,0xebc0ac9b7d75e0564dde,0xbf02b26bf5db815936fc,0xbb2c97bf915d1649fec,0xb0eb25bfe4576592dff2,0xc3ac93ff9061d64bfbc8,0xeb26fde45875937e922,0x3ac93fd90e1d649ffc8b,0xba4ff647805d27fb23c,0xae93fd90e05749fecb70,0xba4ff65b815d33faedc0,0xe95ff915d974affc82ec,0xa4ff643865d2fef22c32,0xb3fd94e05759fec8f0cb,0xcff647845d67fb2dc0ae,0x3fd91e19759fecb708ba,0xdf653815d67fb29c32eb,0x7d91e1175bbecb702bad,0xf647865d6efb2dc22eb7,0xd91e0176bbeca70cbadd,0x643815da7fb29c02ed3f,0x91611769feca702bb4ff,0x47845da7fb21c22ed7f7,0x650110bf7c930abb4ff6,0x160443ff32ea0221ff99,0x5c110ffccbac0887fe65,0x60503ff32cb8221ff994,0x8140ffcc0ac0a07fe5c5,0x503ff30eb0281ff9915,0x140ffcb0ae0a07fe65d6,0x503ff322b8281ff9815c,0x40ffccb2e0a07fe61970],#[0x3f7ae8b0a81ff571585,0xfbf3aac2a07df5d5615,0x37fb0eb0a81efd765854,0xbfecbac2a06ffe1d6150,0xffb30b0a817ff9758540,0xfac0ae2a05ffe6161502,0xfb0cb8a81dfd765c540f,0xecc2e2a06ffe19715037,0xaeac0a81fbd7460540bf,0xc3b02a06ff61981503ef,0xcba281fbd915d140dfe,0x32eaa07ef65974503f7b,0xbb281f7d869d540fbec,0x2eca05ffe4576503ff32,0xbb281bfd985d940f7ec3,0xeca06ffa6176502ffb30,0x32817ff9161940bffcc2,0xca05ffe5d865037fb0ec,0x281bff9161940dfec8b0,0xa06ffe5d865037fb2ec3,0x817ff9661d40bffc8b0e,0x6ffe45875037fb22c3a,0x1bff9661d40dfecb30ea,0x7fd5c541543feac2a0aa,0xfbd7450550fdeb2282a8,0xff65d41542ffb2ca0aa1,0xfd6458550ffab8ac2a85,0xf5d961542fff28b0aa1e,0xf9758550bfecbac2a87b,0x5d971543bfae8b8aa17f,0x7459150bffc8ac8a877f,0x5d64543dfaecb22a1fbd],#[0x15d150bffcbac8a85ff6,0x974543bfaecba2a17ff9,0x5d950bffc8aeca85ffe5,0x70583ff282b82c17ff94,0xc160ffcc8ae0b07fe605,0x1583ff328b82c1ff9845,0x560ffac0a82b07fd5c54,0x583efaeaa0ac1fbd7450,0x60f7ebb282b07df9d541,0x837ff0ea0ac1bfd87505,0xbfecc282b05ff65d415,0x3dfac8b8ac1ff5815c56,0xdffc22e2b077f5d17158,0xdfac8c0ac17fd985c560,0xffca302b06ff61181583,0xfceac0ac1f7d7560560b,0xec3b02b07bf5d981583e,0xb22b22c17ff9760560df,0xcbac8b07bf61d64583df,0x22ba2c1ff9905d160f7e,0xb2e8b07ef61174582fff,0xba2c1dfd875d160f7ec,0x2e8b05ff661745837fb3,0xc22c17ff985d160dff4c,0x8b07df5d584582fff22,0x22c1efd7661160fbf3ab,0xcb05ffe5d845837fb0ec,0xac1efd945d960f7ec8ae,0xb05ffe5187582fff22c3,0xc1bff9161d60dfec8b0e,0x86ffe51875837fb28c3a,0x1ff58150570ffab0a82b],#[0x6ffe19415c3f7ac8a0ae,0x7fd9850570bfecb282b8,0x7f5d1615c3dfac8b0ae1,0xff9458570dffc22c2b87,0xfe61615c2ffb30b0ae17,0xd8460570efeba302b85f,0x619815c2fff28c0ae1bf,0x9059170bffcb302b86ff,0x19645c2fff22b22e1ff9,0x859170dfecc2c8b87bf6,0x1645c37fd30b22e17fd9,0x5d170efec8ae8b85ffe6,0x845c3bfb2cba2e1dfd86,0x1170dfec3308b85ffe45,0x65c2fff22c32e17ff966,0x541ffabaac2a0dffe518,0x507f7b20b2283ff5655c,0x41fdec82e8a0fef5d564,0x7f7b2aba283fbd655d1,0x1dfec32eaa0eff61d655,0x7eff2cbaa837ff965d54,0xf7ebb2a8b0ffd5517158,0xdfb20b22c3bfd8755161,0xfebaf08b0fbf5d564587,0xff28baac37ff945d561d,0xecaaecb0fbf64176587e,0xb20ba2e3dfd7655171f7,0xcaae8b8f7f595745c7bf,0x2abb2e3dfd905d971efe,0xc2ecaa5ffe4576553bfb,0x8c02c9bfd8160164dff4,0xb00b27df5d580593f7ae],#[0xc02c9efd7660164fbf3a,0x2b25ffe5d805937fb0e,0xa2c9fbd905d164dfebaf,0xab27ef65574593f7b0ab,0xac9f7f985d564bffcc2e,0xb26ff61d85593dfaecc2,0xc9efd955d964f7ec82ec,0xa6ff655875937fb20c3a,0x9dfd7660174dfec0b00b,0x5ffe59805d37fb0cc02e,0xbfd65e0574dfec2b02ba,0xff619855d3bfaecc2ae9,0xfd905d974bffcb30aba6,0xf605805dbbfb2abb2e9d,0xf9460176dfec2300bb6f,0x615845db7fb0ac0aed7f,0x8758540bffca30abb6ff,0x6176503ffb0cb8a81ffd,0x761940ffec8b0ca07ff6,0x987503ffb22c3a81ffd9,0x58550ffebb282a87ff65,0x71543ffb2eb0aa1ffd74,0xd150ffecbac8a87ff591,0x6543ffb2cba2a1ffd915,0x560ffeca2eca87ff6457,0x583ffb08b8ac1ffd8750,0x60ffec8b08b07ff66174,0x83ffb22c3ac1ffd97611,0xffeca30eb07ffe45875,0x3ffb0ca0ae1fff9461d6,0xffecc2c8b87ff611615c,0xffb2cc22e1ffd9161170],#[0xffc8b0cb87ff645865c3,0xff28c32e1ffd9461970f,0xecb300ba7ff65d80593f,0xf28c02edffd9460176ff,0x2803f002b801140003ff,0xf809c008640750063c05,0x840e700da40cd80be80a,0x3413441254118810500f,0x8181817281638156c14,0xb81cc81bfc1b0c1a1c19,0xb021c020881f981ea81d,0x6026702580249023a022,0xc42bb02a9c2988287427,0x7430602f702e5c2d902c,0xb435c434b0339c326431,0x183b0439cc38dc37c836,0xc411c3fc03e883d743c,0x8453c449443c842fc42,0x9449a448d8480c46f846,0x644f504df44c984b604a,0x80546c53585244517850,0xe459645850573c564c55,0xd4609c5ef85d785c405a,0xa066fc65e864d4637861,0x946dc86cd86b7c69fc68,0xd0732c718870746f606e,0x7c79b078787740760874,0x6c80347ed87da07c207a,0xf086b8855c840082c881,0x748d188b988a18890487,0x689354926491088fac8e,0xcc982897149600953494],#[0xbc9f189de09c609b0499,0xd0a698a560a3bca218a0,0x30acf8ab9caa40a908a7,0x90b358b1fcb0c4af8cae,0x60b94cb838b724b5ecb4,0x8bfd0be74bd3cbc04ba,0x90c5e8c4b0c378c240c1,0xacca98c984c8b8c7a4c6,0x80cf6cce7ccd8cccc0cb,0xcd41cd32cd23cd170d0,0x28d914d800d6ecd5fcd5,0xb4dde8dcf8dc08daf4da,0xf8e22ce160e070df80de,0xace5e0e538e490e3c4e2,0xcce9b8e8c8e820e754e6,0xc4eef8ede4ecf4ebe0ea,0x50f360f294f180f0d8ef,0x24f834f768f678f564f4,0x1cfd08fc18fb28fa14f9,0xcd01b900c8ffd8fee8fe,0xa106d5060904f503e102,0x6d0cc90b910a7d08d907,0xf113dd12a5116d0fc90e,0x991a6118bd17a9162914,0xb51f351e451d551c891b,0x392595241522dd21ed20,0x992c852b4d29a9284d27,0x213231311d30092ef52d,0x61377136813549345933,0xa13c693b313a65392d38,0x2542c941d940593ed93d,0xad4875473d464d453944],#[0xe94ed54d554c1d4ae549,0xb1565554d5533151694f,0x315db15c9d5af9593157,0xdd63816225611160215f,0x656909683d66bd65cd64,0x7d6f696e0d6cd56b796a,0x9574f173957281719170,0x197bbd7a61794d77f176,0x2d828981997fd17e997d,0x898a7588d18775856584,0x99165902d8ef58d758b,0x21983197419609941d93,0x619d4d9c159b259a1199,0xda31da1c1a0659f519e,0x1a8a5a749a635a521a4,0x19af05ada9ac95aba5aa,0xc1b541b3c1b241b12db0,0xd5bcc1bb65ba51b889b6,0xedc2b5c159bfd9bec5bd,0x71c95dc7ddc681c4ddc3,0xf5cf99ce3dcce1cba9ca,0x31d5d5d479d31dd209d0,0xb1dd0ddb69d9e9d869d7,0x31e48de30de1b1e031de,0x91eb35e9d9e8a1e745e6,0x7df2fdf17df021ee35ec,0xb5f9edf8b5f735f5b5f4,0x5e0101ffedfe91fd7dfb,0x60786060604f2034e02,0x420de60c8a0b760a1a09,0xc6146a12ea11d6107a0f,0xb61b5a1a22187e172215],#[0x12222620ee1f921e121c,0x4e295e28022682254a24,0x462e562d422c2e2b3e2a,0xf23396325e312630362f,0x56391e382e373e362a34,0x6e3f5a3e6a3d323bb23a,0x8a449a43864296418240,0x5a4a6a48ea47d646c245,0x4a50ee4f924dee4c6e4b,0x1a570655f254de53a652,0xc65cb25b9e5a42592e58,0x926312616e60125eda5d,0xae68526762664e655e64,0x326ed66d566c1e6b0a69,0x9a73ce730271ee70fe70,0x9278a2778e769e75ae74,0x667d527c627b967a8279,0x16824a8136806a7f327e,0x5687428676853e83e283,0x2e8b628a9689ee88fe88,0x2905a8f468e7a8d428c,0x66952e93d2929a91f291,0xf182f8304f0382331e96,0xd02e1f16121708f03825,0x185f09c004f048020638,0x8617c370013c12223c6e,0xe10cc17c0e08bc78a713,0xf8bc20702f81c1198e06,0x664f1784150770382331,0x200fc3437178504e0704,0x607f178586c251f81c1,0xe08cc684f17808ee089],#[0xf8009e08cc5e2c2423c,0x382281e07c0e08cc582e,0xe08cc58281213c56370,0x461383e2f038233218dc,0x448300f81c1198b050a0,0x11f046634278bc04770,0x2707c5e07046644268bc,0x8622f0047c1198a1708c,0xee0890684f17808be08a,0x2429c0e08cc684f17808,0x8584f1517c0e08a87e2c,0x1198d8384f1781c1198c,0x13c1198b83e285381c,0xc68160f80c5e08cc6c1f,0xee08906e2c2429c0e08c,0x278bc0e08cc684f17808,0x1484e0f8bc0e08cc8c1c,0xa1b07c50a7038233182e,0x382331a13c5e022f822,0xc545f03822a1b8b090bf,0x31b0709e2f0382331a13,0x382281f07c50bf03823,0xc5e070466381e13c5637,0xe0c2fc0e08cc7c1b1a13,0xa10c109381c1150f8522,0x28438b821570382281f8,0x706162a17810be0a2454,0xac6c1703830b108ec5e0,0x1f1f8b82e042f822a1b8,0xf04543717040ee070616,0x5c0077043e471705c085,0x460b81c1120e48e2d130],#[0x40be07061c1f1c21c51,0x83f1705c087704483717,0x70707e2843042ae07044,0x1dc1120dc56360b81c18,0xa360b81c11091c5c1702,0x30424e07045039238b44,0x5a351305c0e08849e281,0x1c5182e0704543f14100,0x89e281305c0e08908e28,0x168947c1703821f248f,0xc19a27038289150dc504,0x2a118a2385b1781c1150,0x71781c11508c5e2f0382,0x38310198bc0e0a24662,0x7c4f1421c0e08a0662f,0x9140a08e2b1c21c0e089,0x1b81c1848cc563703830,0x8582e098d45e07045033,0x7c1703821c218dc0e08a,0x6b05c0e08a09247168d4,0x82e0704384e248c07e29,0x70382281c1004e2d1a8f,0xd82e07045038238b46c1,0x3f1781c1118a85047168,0x8907047158e10e070448,0x1c1120e08e2e0a8fc0e0,0x70454231411c5c151f8,0xf89e284381c1140dc5e,0x2281c2909e284781c115,0x70466502e13c50a7038,0x664c5023c3a371612c7e,0x222911e1e118fc0e0824],#[0xca8a31708c7e0704662c,0xc4709c584b1c29c0e08c,0x6c784f168dc0e08ccbe1,0x3f03823308901708e138,0x8b84e0704665f0e13c56,0x1985090b8528dc363c27,0x4543e138709e2b1f81c1,0x7e08907074278a11e070,0x1f81c119960b84f17801,0x11242811636138709e2d,0x95c3a3b1a13c5e070466,0xc270d8d09e2f0382330b,0x713c519e0b81c1271245,0x5e28a023c0e08a860c24,0xe0c44542d0f81c1448a8,0x38b84c1703822a1d8bc0,0xb047170982e070454382,0x6313c588b1b05c0e08cc,0xc5c4d1f81c1199611e18,0x704661123049408f0d8d,0x1c119c248c4b1b8b47e0,0xcf8291212891e1d1f8,0x8bc0e08cc86320e8f09e,0xe051f822c1523c34a51e,0xc29c5c4d1f81c11996c6,0x5c4f0382332b098248f0,0x38221200784a351f87c,0xc0e08cc9047168d84c17,0x70442451b09c3e2e258f,0x233089208e2e130546e0,0x87c8a370d8f89e2f038,0x82332411c5c260a8fc0e],#[0xf9384a3f0f8ac6c4f03,0x48e28200b84c17028fc1,0x81f8789a3f1781c11984,0x448383a13c50a703822,0xc0e08cca0a4278bc00bf,0x8ccae1c5f8b09a3b1029,0xe1c530dc584b102fc0e0,0xe8ec484f1781c1198509,0x3624278bc0e08cc2e470,0x5313c5c10cf81c12593c,0x89e2e0867c0e093890b2,0xf1449c00a70450306929,0xa05047170d82e0704503,0xc0e0c50502d0f81c1448,0x83b13c5e005382281d8b,0xccb047170d82e0704503,0x185b13c58a31f05c0e08,0x294463f038233449014e,0xa231d8bc0c1704664f0e,0xf8b89a270382332b8714,0x7e07046614212e14e1b1,0x1f05c0e08ccbc4f1688c,0xc10b121a0b70e89c5c4b,0x8ccb0a70f8a24c4b1f81,0xe186b13c54a51305c0e0,0x82fc5c4d1381c1199614,0x6a27038221230c94e1e0,0x278033e0c50804717058,0xc5e00cf831422890363a,0x31f81c1198508a240d8e,0x3c5e070466142713c5a2,0x4b1381c10d1344e1b1f1],#[0x8fc0e0870808f0f8a2ac,0x6270382332411c5c360a,0x28fc10e1186a3f0f8b89,0xe08cc2840238b82c370,0xb81c12593c3c4d1f8bc,0xc144d2c80c25f13c519e,0xf038289250f434bf1b81,0x2330b915510a5f8946a1,0xbf04483d1a880e44f038,0xfc0e0890705e278bc00,0xc161f81c1120e08e2e0b,0x52f46c170382332c11c5,0xe08cd12405b8618c4f1,0x382330b9097e1d128dc,0x89e07042e4e258dc5a27,0x703821f206218e370e88,0x1c11985c8047170587a2,0x4f0382172289c3c4f178,0xfc0e087080d71386c68,0xe070466172011c5a360b,0xd85c0e08d04a370f13c5,0x6838842bc5e170382341,0x108bc510b1616c9e0704,0xf8bc2e0704683c2f81c1,0xfe281b85c0e08d071082,0x141fc50270b81c11a0e0,0x21dc1120c0410f03822f,0x5e142f81c1150dc5e170,0x181fc503f0b81c11a0fc,0x4542f158b8364f038233,0x5c1f0b81c1198d03e070,0x198dc5e123b81c1120dc],#[0xf81c1178dc5e160f81c1,0x5e142f81c1198c2401b1,0x1c43c503f0b81c11a0fc,0x4683f1707c2637038228,0x1108bc510d143349e070,0x1f8bc2e070468389781c,0x6e2f0917c0e08a86108,0xe08d05e2f081fc0e08d,0x184a21e07045e2b085fc,0x43e29181005617038234,0x9e07043826178bc2e070,0x84878563f038309120b0,0x28fc0e0c243c2d1b81c1,0x85c0e08d04a170382341,0x2491a094217f03823416,0x341284c7e07045e2f038,0x1685c0e08d06a170382,0xe1c0771785c0e08d0704,0x1c1c3815e2f0b81c11a0,0x7046637178547e07042a,0x6c9e07046638d38bc2e0,0x3c0f81c1140bc51a3160,0x8bc40e71409c2e070468,0xa03e170382331c51c0e0,0x3318488ee07045e28d38,0x70382341c69c5e170382,0x415e07045038738a04e1,0x2b2781c18a8a06047158,0x70450331781c18a8a056,0x5c0e0870563717842be0,0x5f17841ae0704503f178,0xac60401585c0e08d061],#[0xbc0e08a07e2f0b81c10e,0x2f038221178a08e2b082,0x8cc6e2f091dc0e08cc61,0x7c0e08cc6e2e0f85c0e0,0x1f0831c0e08907e2f0b0,0x8b83e106b81c1120fc5c,0x63e170909e07043e1b1f,0x48785c2e1213c0e08843,0x8fc0e0c243c2d1b81c18,0x40170d84e050b822122,0x786244c31e85c0e0858b,0x363f0382498b0e21a4f1,0xe84c563f03831620430,0x244d31e85c0e0858b10c,0xb1f81c10b1221a4f1786,0x143e08b8ba17178624a4,0x4100fc330b09c764f178,0x42431f8b43e105b81c11,0x8b0e1962d0d93c0e0c58,0x3822a22870262f038221,0xe0884a63f1687c2c270,0x9070431e87c5e161b09c,0xc10d1786e2f0a8fc0e08,0x38c9e2f0c5516c230b81,0xe2e1187c2a3f03822420,0x8cc5e2f0a8fc0e08906,0x8bc2e070464301593c0e,0xe500f8bc2e070464306f,0x38ac3e161b0947e07041,0x3127159347e07042c402,0xf902507d1f81c1178dc,0x43050200b84c3d0b81c1],#[0x80c6549e2f0c5142e070,0x58764f1b8bc0a1f04625,0x2f0b09c0e08a8707e118,0x8bc2c261f81c10f92c6e,0x8c61185c0e0868b0431b,0xb81c114101c64f17862a,0x6e0704503f1708c3e106,0x1585c0e08609c2717854,0x46e0704523d1b862864f,0xc2781c10e06c7e2f081f,0xb09c3f07801f0d8f85c3,0x1d218787e0706121f1b0,0x87060780d8d090cf0780,0x3c0e0880861e1f81c184,0x7061228181e03624243,0x321be0706122a18321be,0x3c00e90c3e0706122a14,0xc2450288486c6848678,0x89090cf0382202187c0e,0xc361e85c0e087081090d,0x7862aa1703821a201005,0x5c330b0fc0e0d0caa4f1,0x1b0fc0e0870a07f1193c,0xc0e08a860431287c5e16,0xd1185c0e08689e2f0a89,0xf44e0704563f0c54c9e2,0x270c93c1254687e2f081,0x91830a7038233160d2ae,0x6405f07c584f03822319,0x9901184f1707c00a7046,0x66405e13c5c185381c11,0x19901184f170617e0704],#[0x848505213c5c185f81c1,0xc5222c3c2d1613c0e0b3,0xcca8a04047c0e08cc583,0x8840aa8484f178014e08,0x13c5638cf81c1a3044c8,0xe070708142c63140bf0e,0x6854442fc384f158e33,0xc5e22c3c2d1613c0e08a,0xe1061c278bc0e088c664,0x213a13c50bf0382332a2,0x8a33e07068e113222104,0xc205cb1745c28c6e1c27,0x110a31b8709e28cf81c1,0x4289c1ce2e2781c11a0f,0x2c823f168782e0704503,0x2c1a8628e07051234192,0xf0382331e2b46e070450,0xbc01470468490c69c5c4,0x7052228252e91a1a238,0x39c11a0c15a42238b46e,0xc4f038255140dc5c4f00,0x713c5a370123c11415c5,0x90e703822c1a0a482289,0x401789e289381c12708c,0x9c4f168782e07046638,0x25123434471781c1a709,0x288a1f1523c0e0d38484,0x411453c5c4f009dc1121,0x8e0bc4f1781c1118cc72,0x8331a210b44f03823391,0x70446331d2823e07045,0x5c0e08a4664a5f13c5e],#[0xe07068e112e2389e282f,0x46648b98c94e1f171233,0x1242d1161e278bc0c170,0xf844a70c6709e051f829,0x332708964a7028fc1160,0x1291c205c2889e2f0382,0x8b0f13c5c1703825a0e,0xf13c50a70067c1a3a44a,0x1c16278bc0e08cc81770,0x278b4719f03829130689,0x91e08cc6188bb874621e,0xf1781c148968bc4f1780,0x31114101c24114d5c3c4,0x8f058e730f13c5a37038,0x78a50d8746c4f1780330,0x1467c0e0b1c5c48c45c9,0xc3e2f0382332c29c3c4f,0x704663c5112c51288f12,0x7c063f04dc4b0f8bc017,0x222c31751b0989e1f146,0x9e1f1467c0e0b1c5c545,0x168fc0e0c44484050238,0xc519f018dc11890c3c4f,0xe2587c5e0704665f0f13,0x31e08cc78ba258a2911,0x37178033e09b8961f178,0x88bc458631c26268fc36,0x1b13c3e28cd8dc0e08c4,0x3184b189788e0707182f,0x8e0707182f1b804ee0e2,0x618fc0e0e20978c1c878,0x318411f11c0e0e305e31],#[0xec60e582711897c0e0e2,0x7182f18ab46e0707104,0xc0c470718551c8788e07,0x31f81c1a1e2318491d89,0x84ee0707118c24b45523,0x470319c1178c5a2ad188,0xb0c4e0707118c270ec7c,0xc39698dc0e0e209d8c1c,0x4630961f1f11c0e0e30a,0x184960ac44a370382c7c,0x2cb4562331f81c1a2623,0x5663d1a8843e0707118c,0xb1f11c0e0e305e3168b0,0x30961f1b8188e0e30b03,0x3968b047637038344c46,0x16876310f81c1c4630b0,0x18c2d0ec3e27038388c6,0x705962a298843e07071,0x82332a2f1461e168b09e,0x2a2e104a91e13c50a703,0x104313a13c50bf038233,0x4278a33e07068e143228,0x1c1c305cc1745c23c362,0xc631408f0d8909e28cf8,0x544f1713c0e0938961f1,0x1c2a10c4f178094e092c,0xc54360b8b89e012f8233,0x5e0d2c543d0f81c144d2,0xb81c1a58a8aa1e0b80c,0xc1a58a894a3208fc5a1e,0xd2c54425d29434471781,0x21f1a0c88a1f178094e0],#[0x5f0129c11517c5c4f038,0x9c24244a232411713c52,0x121415086278a94e0704,0x94647148943c1703834e,0x42305c5c4f009dc1198e,0x9084450f8a94e07069c2,0x3324882be2e27804ee08,0x92150811313c5e070428,0x489102989e2d0f81c119,0x42189e291381c1168cc9,0x78ac4287c0e0a2466385,0x199315883178114e08cc,0xc90a8408f89e2f038214,0xa5c8e14c4f1687c0e08c,0xa10c4f148fc0e08b4664,0xab0c4b14e07045e33202,0x8b89638cf81c1a2050a0,0xc4f1705c0e08cca4bf0f,0x78bc0e08ccb0d05a28c3,0x12c16314a5102e11c322,0x80fc10538b8961f030dc,0x4f1423c019f068e942b2,0x13c5e060b8233285dc3c,0x19f068894243416a2253,0xb81c11995c3c4f142fc0,0x14a1631a20d12989e2e0,0xdc3a210f13c5a38cf81c,0x4d1313c5e070528331c5,0x3e68e1e278bc0e0a50b0,0x61e278b44e0706282a20,0x223c319a2780c7e0c509,0x4e1b1d8bc019f06284d1],#[0x131233e07058e142e234,0xc00a7058e68ba23c3e2d,0x5c9788d0d8789e2d1067,0xe1e278a33e07058e2e24,0x78ac3c1703822b199411,0x9e2e0b81c11994158a62,0x1f831412101a0b451878,0xc06270628530f13c5e05,0x70466545f1347e1f1467,0x6445e28c415e2587c5e0,0x99178a6278ac3e07046,0x3c36268fc3e28cf80c4e,0xf8a33e070588645e28c,0xc11a0f86c14531317a3f,0xf04962a249621e2e2781,0x1c1198e10076278bc04b,0xbf06962a2713c5a1e0b8,0x43c11a0dc5a1a210bc04,0x25f012fc11517c5c4f00,0x382331c52232411713c5,0xe08a068510c69c5c4f0,0x5c50525d91c52250f05c,0x38569088227168dc0e0a,0x8a09cbf1713c0e095450,0x839105789e2d1b8097e0,0xb8cc910e278a97e07046,0x6648401c44c4f1781c10,0x202e91226278b0ee0704,0xc9086278b0ee07046033,0x85d2846c4f161dc0e08c,0xccac4f161dc0e08cc603,0x725f0e1408a278bc0e08],#[0x8789e2e0b81c12b08491,0xe28538033a27052e485d,0xf0589e2f038233278789,0x5a20cf81c14b962e1a25,0x52e332063c3a310f13c,0xc12b25c9c4a1511c5e07,0x8a4664884c9c3c4f1781,0x8172a2f89e283b05c0e0,0x58c94e1f171233e07068,0xa8bb0f13c5e060b82332,0xf13c5a2703831715101,0xc6c4f178033e085e886b,0x31b823120629488d0d86,0x1c18b8a08e1e278a33e0,0x3138317298789e2d1b8,0x16c9268d14c4f0f8a33e,0x668c0f8ab168cc7e0f02,0x3822f198d0ee0f01930b,0x363f0780c9178d0b08f0,0x1c23c564f0217c1198f0,0x46634628fc1e042d92cd,0x1e05269a304e17c0e0b2,0x1783c010d245e322c3fc,0xfc1b1b81c124e2cb240,0x88306c6e0704938b2c90,0xec58ae1989c1e03261c4,0xd2550cc7e0f02931e201,0x8c13c323b83c0a487074,0xc9178d830a703822f19,0x2f07811564910363f078,0x7c1e0124b2486688c76,0xe0f009259282a0fc3313],#[0x38233203a8f4ae198983,0x648cc6610538ac9c1f0,0x1b83c0a4c78706e0f83c,0xc564f021dc1198e9a473,0x46289c1e03261ccd1c2f,0x46638661dc0e0b24663,0xc0648cc60bf15930ee07,0xe1383c02d62480ce0f83,0x89e0f00b49e1c1e1361,0xa4444bc0e08bc6638884,0x2214a4f1685c0e08cca8,0x8a44781c1248cc617058,0x995428a44780c7e08bc7,0xe0b5082811a4f1781c11,0x218748e2d0b81c119962,0xc5e07045c33245d1488b,0xf07811664921408b1e93,0x5c0e08cc90c83d8b4363,0x3245e40c422c9e285d8,0x80c9198f1809b168fc1e,0xe0f00b22f1c32130c707,0x4b3c0e09246638803a49,0xa06b1f83c0a48bc71007,0x24649a4c7078149178e9,0x1a610502ec9e2f038233,0x31c320dc270780c9198e,0x24663b0869c564f03823,0xc1148cc80db0c4fc1e03,0x7038233262f11a471781,0x1c11996310bd278a11a1,0x8631788b218748e2d0b8,0x1c231a93c5e070466312],#[0x668c29e07059233142e1,0x78149198f43e0f019318,0x3e0f0292331832c609f0,0x662745e01278233240ac,0xc9e2b0b81c11992c6c24,0xe1383c0648cc70d05c28,0x948e2f03822b19901906,0x1d238b42e070466545e2,0x8b42e0704664c5e28c86,0xe0f0192331589178a527,0x98e05a1f0780c9198c2b,0x682815891986f0093c11,0x4a246874e120a9748d0c,0x18c311751f08c3488cc7,0x5d11198c1c8a2258a251,0x44b145223270e318a30c,0x85d17618c62233183917,0xab8c1e865a84220978c1,0x27623182b12865884220,0xe8656842209d8c18b455,0x102968b05661b1f118c1,0x61b1b198820b04e25e33,0x8aa4ec463052d160ad44,0x52d160acc36262318396,0xa1d38482a5d2943a58a8,0xf0cc3c15112833252891,0x444b144a232590311751,0x1e22c3174506628b43f1,0xc5420b43f178a310564e,0xe8bb118714198d178a30,0xa1d2c542c6a291762082,0x98e9748d0c6828152e94],#[0x464b20622ec3d1186971,0x8b8cc5180862e89628a4,0x628c461c5c563c458631,0x2e331a2f14618a841808,0x8d45e28c41063146230e,0x464248a445862e8b15c8,0x21445e2384618c630542,0xc855178a311871a28903,0x1178d4518820]]
set_option maxRecDepth 16000 in
def g255H10 := limbs80 #[#[0x6600270300020900010b,0x407383a40101b0a04,0x204260f0e3a000d1c4c,0x6073d0a023c04010001,0x254507006b111101284b,0x40a04020e415a21011e,0xd0019240204281d0d00,0x3b66b1010c302a8a8400,0x28c02551638092d00ec,0x48000e0a008904,0x140e07016f140011098b,0x11168b2d21010bbf1928,0x5e4f57db2dcd5b022a40,0xd29b737b0265d33451f6,0xf1349eb6f5f000000161,0x8f5a68000e2f96600034,0xd6fd5ef90ac3ad06cf58,0x32e132738e0e5082b,0xae38f5018516813104c6,0x92db39920227a82fdad8,0xc0b7e60e2fad96a1cc01,0x45c964ac109ab5f4ec95,0x7b3b49c56e7c1cb12e81,0xe50e7fd10369f3609be1,0xf7bcc58af1abc3ddbd97,0xc00116d6e60003e163a1,0x1e5d44ca94a6116afca,0xba9f2000f713392cafd3,0x41669f35,0xee40011d80000001dea0,0x19400000034340000a1d,0x64e05f6a7b55388c513d],#[0x13dba01c654754145ee3,0x6f224a540000000a2c00,0x9ce99ffb5833084618,0x18181819974929086300,0xed00009a405f036689fb,0xc43000098fdac0000003,0x1894612b5533026a6,0xec327c04cde6cbf19c37,0x26626f3211f1d4e1e67,0xff8a7bb6bc2027d35500,0x42705fbae26115442cec,0xab45ed4b5e0a20000000,0xc216014a4c8aaf07d484,0xe30800020d4c9759198c,0x8733bd8a7a099edf7625,0xa5dcaa02fe8d80141235,0x7092b84480001a616de4,0x932202581c889ebce4f7,0xd71c63d1019ba6abf1a8,0x9b26375190415357a9c0,0xb4b8819adbb83df3688c,0x4e1a817b4b14ab12b533,0xc8ca3b3beab8db5321c9,0x1614bb1266dece9801d7,0xfd12aebbe0e360376e12,0xf0fc05951178958736fc,0x86eadc371b9b3aeeb9eb,0x50001e735b42317eac86,0x366c674695a40010a9dc,0xcbb114001bb2360a47ef,0xd74de7215bdc18,0x332d5c1a20074c3ba920],#[0x2430c82bb5a2319e4d02,0x63c800004f829f1e3a9,0x70177ae64bce58f82800,0x7252210a166a989d2b4f,0x4bba3df9f0a9a5424544,0xf88833c749f045a2f912,0xe87aba01bc2a02a4e077,0xebbf4b662fca0897704e,0x4f1e1c5b7dfdb9cbf810,0x19c5778f9b3d4165e3e,0x344a4a93731d2ef2d640,0x5577ad44d36a4d90cfca,0x3800000c2f04aa59d2d5,0x51a2146bb25885ac2819,0x9b4adc96a3949094ba3b,0x3ae8e9c385381000132,0x1a000314394377aa2c80,0x3030758cfd20b431f01b,0xc6942756d9909d9a6e1c,0x2c99e840faa2039cd87,0x8000e1f2f5551dca8a1c,0x58d82effc47000417f30,0xab0e0f920365a58fa570,0x248003e97e7637705c84,0x54a000000281cd9a9349,0x305586c0004e6ab4d,0xd332000baf9e480014b1,0xf8173cce62a0000cf7ad,0x3ace000028a220d7889c,0x6b0000981a9d56f3a904,0x5fad8b900000000000,0x6d86a102452d401b0780],#[0x7260001d180000000001,0x1176e9d0001c9bd8b444,0xb9026f0698de8353a000,0x95a7100020e7a4600df9,0x30b54a34dc22079]]
set_option maxRecDepth 16000 in
def g255D11 := limbs80 #[#[0x58110ff9404435f5d570,0x443fd50510ff970443fe,0xbff84442ff61110ff571,0x61910f7e75443df5d510,0x442ff61d10bff86442ff,0xff970503fe58140bff87,0x5d540fbd74502ffe0540,0x502ff61940f7e75503df,0xbff87502ff61d40bff86,0x59160bff81583fe5c160,0x583df5d560bff84583bf,0xbfd87583bf5d960f7e75,0x5d170bff815c2ffe1d60,0x506ffe1970bff845c37f,0xfbd64507fd5c541ff561,0x9d541f7d75507ef5d141,0x546ff61d41bfd86507df,0xbff87546ffe1951bff84,0x59161ff571586ffe0161,0x587df5d561bff84587bf,0xbfd87587bf5d961f7e75,0x5d971dfd745c6ffe1d61,0x552ffe1954bff815537f,0xbff81592ffe0164bff87,0x9d564f7d75593ef5d164,0x592ff61d64efd76593df,0xbff815d2ffe0174bff87,0xe0575bff865d37f5d974,0x5d6ffe1975bff845d6ff,0xf7f865d7dfe1175f7f81,0xe1176bff815daffe0176,0x443ff5d110ffd64442ff],#[0xffd86443ff5d910ffd84,0x5c540ffd61503ff61d10,0x503ff5d940ffd81503ff,0xffd41543ff61d40ffd86,0x59150ffd71543ff58550,0x583ff5d950ffd74543ff,0xffd81583ff5c560ffd41,0x61d60ffd84583ff5d160,0x5c3ff58570ffd415c3ff,0xffd845c3ff59170ffd81,0x5d541ffd65507ff61970,0x547ff59151ffd76507ff,0xffd80587ff5d951ffd74,0x61161ffd74587ff55161,0x587ff61561ffd75587ff,0xffd645c7ff55171ffd87,0x60164ffd76553ff59571,0x593ff5d564ffd81593ff,0xffd805d3ff61d64ffd85,0x61574ffd655d3ff60574,0x5dbff60176ffd865d3ff,0xffd855dbff61176ffd81,0x63814003a809c0118000,0x883340b982a009481dc0,0x854813c849c11383f00e,0x72c1b9868018c85ec165,0x18234887c20b87d81e48,0xc2ab8a6828089ac25789,0x31e8c3c2fb8b982d48af,0x998e083668d543418cc0,0x8fac3d78f103b68ea43,0x91b045290fc429904840],#[0x3344bf92c84a2924447f,0x30534947c50993c84e09,0x45b9968859095f456995,0x61a982c5fb97b05dc973,0x8d99e8666994c64198a8,0x49bf46df9b306b69a8c6,0x9e187749d747459ca871,0xff47e59f487be9eac799,0x30874a17c847a0b08149,0xc907a3c88daa2fc8a9a2,0x960a554949a4f892aa45,0xd7a7209aea674985a5e0,0xaa8c4a1ba8309f8a7ac9,0xaae0a9caa14a75a978a4,0xce4b25ac38af4ab74acb,0xc5f1b130f0304248b50a,0x61144c50983c0c133281,0x511b14260f0304cc910c,0x1709c54783c0c1332840,0xa27160b00ab042c910c6,0x689c58224c0c10e24411,0x1a27160b00ab042ce104,0x33c11024444020148c1c,0x304cc24807064489c5c0,0x582c0c13326131a0d1f0,0x91b0304a0d84c683474,0x10245450401c120e2716,0x438b070489c546c033c1,0x45c40181227160893030,0xa06048947c5c033c1102,0x50471f0c27151b030610,0x11c6c309c584c0c14728],#[0xc190e271700ab0444917,0x1c6c3c58982c0c147281,0x471b0e111f0304248181,0x8384c6458247c0c12c26,0x71f0e27151a120b0304c,0x389c546c0c1112058504,0xe2716111e0b0304cc7c,0xc547c0c11120605c471b,0xc27161b03051cac6c389,0x9c5c028c114245c53130,0x1627020b0510a0704438,0xc544c0c1142058531f0f,0x30e191f0304248c7c389,0x4c386474582c0c126531,0x130f16260b03051ca94c,0x89c5864782c0c1306853,0x51f03045081a1714c4c3,0x9c5c024c11727130e271,0x162513030608a0604438,0xc544c0c11720605f1b0f,0xe27151b03045cac6c389,0xf1546c0c10b242017130,0x170b0304382c7c7c5c20,0x16c233462fc0c10b231b,0xb246317091ccf03042c8,0x2c8194583c64947c0c18,0xc10b360f1b09151f0306,0x1505070825c5c24621c0,0x1b17087c2f030438b16,0x706c03309c1121c60a42,0xc11e181d182703047860,0x4d10b03045490647c009],#[0xf1586c0c10e241c11271,0xcd120f0304bcac5c4c20,0xc244c0c1152058541b08,0x219260d1f0304b08c7c5,0x54783c0c129146486571,0x1f0304cc92195c4c2864,0x1cc0c10e306b170a0c55,0x45491a152b0804c5c286,0x10e2020141308bd1f030,0x30438818c5c24433c0c,0x9c0c1131c6b170918cf,0x81d1827030478607062a,0x3045890647c0c1091e1,0xc0c11620931d27170d0b,0x91f0304ccb08c5c2c743,0xc133286058130f170a1,0x4bca4519c384864749c,0x332cce0e130916191f03,0x1a1606c3c5c28447c0c1,0x2130e191f170b0304cce,0x247c0c116246860580c2,0xd0b03046090824c5c3c,0xc643c0c11820a3192717,0x7091a130304ccb08c5c2,0x246c0c1182468601f0f1,0x930304246470828c5c3c,0xc6c344c0c109191c1810,0x9191f130d1b030424647,0x30424647464433c0c10,0xc346c0c109191f1b0d13,0x52717130d0b030468bc4,0x5c2c443c0c11a20a8201],#[0xab170f0913030468908c,0x461089c582c0c1332420,0x422714620b0304cc916,0x509451f0bc0c11021291,0x184227160b0304cc911c,0x48c546c01cc110212869,0x3147c3b0304407091514,0x584558946c0c11c385d2,0x30538b1591431182c7c,0x2c2a450c471a2716120b,0xcd11104746230b33c0c1,0x6130f1625191e0b0304c,0x389c546c0c1112c6a444,0x151f030444b2e1614c7c,0xc14b8c20c4605f1b0e27,0x30304be30943c7c688c0,0x8c0c18c4e21131d190e2,0x12230304be30943c6c48,0x884744c0c18c250f1d19,0xe211d1b030630958c6c3,0x9c586c082c14b2d6b130,0x1a0b030538b944314c78,0xc133142e510c53122716,0x4ccd151047444389c5c0,0x530e271619111e0b030,0x7c389c544c0c1142c625,0x27151f030450a2e1611c,0x8987c0c14b2c685f130e,0xb030484e974317c682c5,0xc550c5e0b13161d56251,0x6440e89c5c0c133172a5,0x161d19120b0304ccd104],#[0x44c0c1172e5c585f0e27,0x3045ca311811c6c389c5,0xb4d1c6853130e27151b0,0x3062d2498783c0c1498,0xc0c18b2a24660f19151f,0xb030624cc54883c51ac2,0x224cc51ec0c18933144,0xc5421cc0c115212c4b07,0xc7b030524bc614104886,0x32818c515c2c0c1342e1,0x54942f030484bc848448,0xc445868347c1c0493058,0x48703043470719952115,0x5c5c20ec0c11c2b24492,0x24261b030526387861a1,0x93474883c516c2c0c18e,0x1c033892a120f0701263,0x30458c8513c3478446c,0x24b850450b1f0c931527,0x4b1615c2250b2fc0c133,0x660e1a11151f0700bd2,0xccb13c70dc0c1492f1c9,0x686059210d1f170b0304,0xc628c349c542c0c11834,0x7082f0304cc931841711,0x4c1c04d3349206038a71,0x14a30f03052460b83878,0xc5c2c0c13330644e1319,0x30468b1a181648844346,0x3245c510b130cab15270,0xccb1a152b0ec5c2c0c13,0x686059210d13170b0304],#[0x192ac40dc3c1c01a4924]]
set_option maxRecDepth 16000 in
def g255H11 := limbs80 #[#[0x5540221010b3d08090d,0x720017000903062e2500,0x30306001c170a0f0800,0xb0e0232172a06150f28,0x244b0a00541204010002,0x1071a06002b07140003,0x109000d1606160e5e0b,0x14b0015170016000061,0x31100016310200001209,0x10b1a302906070c0d00,0x70107a900020a140602,0x601010202000a0e0901,0x200715000019071c0c31,0x3e070a0e044c04000021,0x182200011a4002e,0x23184000752013407dc0,0x788c000000000000018c,0x4c40002658000761c62b,0x6000001b000000000004,0x8ce84141c77000122983,0xe5040d205d59ce12d,0xbff78ec1ed0d1013f158,0xeb3e00001824932f6a14,0xb6bb11d000061bf205c2,0x73000000005f40002c27,0x70000832400028691657,0x29b9f6d40fe981916654,0xc9300038998188000000,0x713a94500000002479,0x81849e28615c49f20800,0xc736636000000000039e,0x1aa538649d4e9f392d30],#[0xb80000000000855cdcf6,0x60160002c94343458ae8,0xde12f7905213400007b,0x290003c73168cd7f446f,0x74065e05706d8400002c,0xe54cd3f057394784ea00,0x5e200f123c00000010ab,0x5b917e490000a047c8d6,0xf90422b692d7638e2774,0x9d1583f5620000000c0f,0xff0002cf0020d560c4b1,0x9c80b4fa686147f00034,0x65c78f276de0bef00255,0x74ddd765ead7644608ec,0x711ec23aa0b470254951,0xe238612dc31337c09710,0x8b000093ba6f503ca65,0x2680e800076a7d880001,0xd063000077200a70726e,0x5a5000000077191f,0x45580bb5a296755b145b,0x1582319ec05020a8866,0x4a17e2a8000653000000,0xc98b0ec4b10003e07461,0x4525a400000029724578,0x917bc92524d6d10e1508,0x21080009544000d5f013,0x6341e2da397d94,0x3240e01731a6064a22c0,0x2451421d5dad1a0de500,0x4a10000000a39c4f3000,0xdda75788c83d84550001],#[0x15e1d35f02476779,0x86da59527e34fce7c91a,0xb6c0ccf0002c80,0xbdcc52841d1ad63c8530,0xe035278b4c600015ebc4,0x8f7b2c81dc84cedea079,0x1f00009f015c309e0000,0x3f48410893730e2f4259,0x202308a60e79fe56a9c4,0x7db0f465d39dfe028000,0x86ca3e61bdafb53f90f7,0x3ddb73f4000d131cee80,0x54b92171b1c3b453ed66,0xcd663683eb06b963135b,0x4d865846111000086068,0x62691e6579020124325d,0x70cc15c0f6872d226806,0x7821e7882ce0350a96ea,0x8c32b19adf538cf838d1,0x4a267c61f3467861c775,0xba638c000456bcc303d6,0xd056109dd1219a77295c,0x257687c985148e0241e0,0x1ae830a51055f9452119,0xd0c60e85aa0a53ed8640,0xf8efa5dfa256035e3248,0x92b26e2433a01054eb60,0x5946ed1bfb323d7e92cd,0xfb823c14932d9ee405c8,0x152a8a80002d9345f78a,0x1e64c725ed07ee711537,0x349ad9499c4a562786f1],#[0x718412eed56e42b60435,0x1abf1a4000426da31a38,0x79a409c1ff8e6802a765,0x834c000554395b72445,0xe88a07174a71de368800,0x7159a1e7499bc6640d07,0xc0d9a26d15c7050e5be7,0xae0c4106c03678000082,0x361500025f9c4a,0xa9f291d9b93501d80000,0x660b219fc16a5d0d7f28,0x72c000944cd0,0xa217483180209a211,0x70dd3892561f70186d0,0xc4bcb0df1911502d36d4,0xd8b0001c84a6e8000187,0x73afd49a1600008063,0xfa11c000035400000000,0x590cf162b800000b642,0x149c7b00014b5709587a,0x48000c1d00000518000b,0x34b70001c6e25575c260,0xdb225bd065000216bb4a,0x142e320ef367999d258,0x3b32912ea4f0000d0d88,0x57e8000a36c000000097,0x1049043adcaf7ef428,0xbe112c3124ac00000000,0xc000000000018c30c1d8,0xa00b80fa13b270c7d86c,0x15b6c76e39a023d0a9,0x767386300000],#[0x74038b900030c,0x5ab122e0ac000317c20b,0x790bf8a89526338470f,0x5e98332e350002c5d37,0x954287553d94468a0000,0x1de0420a600000750002,0xc58dd4d1a7fc000813e4,0x840e4da03e400000031a,0x1923c223478f248000]]
def g255D12 := limbs80 #[#[0xffa81ff443bf3af7d75,0x51ffa83ff5c3feb07fd5,0xd64ffaa9ff5c7feb0ffd,0xfd76ffaebff597feba7f,0x33c5488a0c80f80f8007,0x8e219e2fe5729b5179ea,0xa243121e0412224c0b7a,0x2a3448708385810480b1,0x12884789184c5060a041,0x8c208c78d0c4c5080a04,0x3028104a8f1a24311020,0x43828104a291e2431314,0x16140822c92f1a243131,0xb1a2038104490201c78d,0x2b1e2c484181c0825470,0x8100e345890a0411c488,0xa0412a3858d0c2408224,0x1e041284168f161c2081,0x1046891c4188d161c208,0x890c28781044911e2438,0x8351624384183c082546]]
def g255H12 := limbs80 #[#[0x8501d0000820c5309041,0x88460055530af1130404,0xa0000091205430014a01,0x60b53e5666d138000000,0x300071334800000017a7,0x35900052147fc5db0b72,0x3400000050df6a56fa05,0x5768b3340c82a73ba4a3,0x281c3f78418e72fc7,0x2b111657000036963831,0x27244fd20d1f2022823,0x41886b228d4200000000,0x8cd7d740387c32689d86,0x5001385e1b60671c3167,0x41e00023c07eb4dc7ce1,0x12e000676139,0xe000051477d3d045d6e0,0x4b00060900041736435,0x7420fb30578f5c865435,0xd8845400000000001a2,0x65ba22a5fd2c983f6200,0x7b74671060a000867000,0x7073771827b3a550f66e,0x35881d000204b41b3e94,0x43b52c2458a46c20e000,0xf04e000f3727998db268,0xb1440762951218,0x8bd1900032d10316134c,0xd69025644149d5a5556,0xe70e8040800]]
def g255D13 (j : Nat) := if j=0 then 0x7185103080048ff else 0
def g255H13 := limbs80 #[#[0x3836f000011a22cc,0x6b00490e0439400094a7,0x4241de0b64944d]]
def g255L : Nat → Packing
  | 7 => (3,6,6,0,0,4,0,g255D7)
  | 8 => (134,5,6,0,0,12,0,g255D8)
  | 9 => (480,4,6,0,0,15,0,g255D9)
  | 10 => (570,3,6,0,0,16,0,g255D10)
  | 11 => (144,2,6,0,0,14,0,g255D11)
  | 12 => (17,1,6,0,0,11,0,g255D12)
  | 13 => (1,0,6,0,0,0,0,g255D13)
  | _ => emptyPacking
def g255I : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 1 5 0 6 2 0 g255H8
  | 9 => lookupWord 33 499 3 12 8 0 g255H9
  | 10 => lookupWord 120 547 8 13 9 0 g255H10
  | 11 => lookupWord 142 701 8 14 10 0 g255H11
  | 12 => lookupWord 36 179 6 12 8 0 g255H12
  | 13 => lookupWord 4 23 2 9 5 0 g255H13
  | _ => fun _ => none
def g255 : Forest := ⟨255,13,fun i => g255Y[i]?.getD (0,0),g255C,g255A,g255L,g255I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P7_0 : block g255 7 0 3=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B7 : block g255 7 0 3=true := g255P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_0 : block g255 8 0 24=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_24 : block g255 8 24 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_120 : block g255 8 120 14=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B8 : block g255 8 0 134=true := (@block_merge g255 8 0 24 110 g255P8_0 (@block_merge g255 8 24 96 14 g255P8_24 g255P8_120))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_0 : block g255 9 0 65=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_65 : block g255 9 65 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_161 : block g255 9 161 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_257 : block g255 9 257 59=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_316 : block g255 9 316 96=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_412 : block g255 9 412 68=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B9 : block g255 9 0 480=true := (@block_merge g255 9 0 257 223 (@block_merge g255 9 0 65 192 g255P9_0 (@block_merge g255 9 65 96 96 g255P9_65 g255P9_161)) (@block_merge g255 9 257 59 164 g255P9_257 (@block_merge g255 9 316 96 68 g255P9_316 g255P9_412)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_0 : block g255 10 0 9=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_9 : block g255 10 9 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_105 : block g255 10 105 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_201 : block g255 10 201 95=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_296 : block g255 10 296 96=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_392 : block g255 10 392 96=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_488 : block g255 10 488 44=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_532 : block g255 10 532 38=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B10 : block g255 10 0 570=true := (@block_merge g255 10 0 296 274 (@block_merge g255 10 0 105 191 (@block_merge g255 10 0 9 96 g255P10_0 g255P10_9) (@block_merge g255 10 105 96 95 g255P10_105 g255P10_201)) (@block_merge g255 10 296 192 82 (@block_merge g255 10 296 96 96 g255P10_296 g255P10_392) (@block_merge g255 10 488 44 38 g255P10_488 g255P10_532)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_0 : block g255 11 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_1 : block g255 11 1 82=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_83 : block g255 11 83 61=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B11 : block g255 11 0 144=true := (@block_merge g255 11 0 1 143 g255P11_0 (@block_merge g255 11 1 82 61 g255P11_1 g255P11_83))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P12_0 : block g255 12 0 2=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P12_2 : block g255 12 2 15=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B12 : block g255 12 0 17=true := (@block_merge g255 12 0 2 15 g255P12_0 g255P12_2)
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

end PEqualNP.Outside.L_meta_51746

open PEqualNP.Outside.L_meta_51746 in
theorem PEqualNP.Outside.L_meta_51746 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o fit _ correct
  exact replaceShort g255R gates o fit correct

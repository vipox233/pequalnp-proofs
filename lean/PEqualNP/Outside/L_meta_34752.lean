import PEqualNP.Defs

-- The two-mode live-state and cofactor checker follows L_meta_1674 and L_meta_670.
-- The graph, restrictions and all search certificates below are for L_meta_34752.

-- Shared forest and cofactor certificates from L_meta_1674 and PR 11111 for L_meta_1677.
-- The original credit line is retained below. The two root certificates here cover the unpinned graph.

-- The checker and the bound certificates are adapted from PEqualNP/Outside/L_meta_1667.lean (Apache-2.0).
-- Two modes: u=false are monotone runs (AND, OR); u=true are runs up to complement, where negation is free.
namespace PEqualNP.Outside.L_meta_34752
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
def graph : Sig := (BitVec.ofNat 512 (word80 [0xffffffff,0xfffffffeffffffffffff,0xfefefffffffefffefffc,0xfffffafaeeeeaa00ffff,0xfffffffffffeffffffff,0xfffffefefffffffefffe,0xfffcfffffafaeeeeaa00]))
def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 4) || (x 0 && x 5) || (x 2 && x 5) || (x 4 && x 5) || (x 1 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 2 && x 7) || (x 4 && x 7) || (x 5 && x 7)
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
  (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 2 &&& x 5) ||| (x 4 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 2 &&& x 7) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7)
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
  (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 2 &&& x 5) ||| (x 4 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 2 &&& x 7) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7)
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



def target (x : Fin 8 → Bool) : Bool := decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 4, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 4, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 4, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
def smallCircuit : Circuit := ⟨[⟨.or,[4,7]⟩,⟨.or,[1,2]⟩,⟨.or,[3,9]⟩,⟨.or,[2,4]⟩,⟨.or,[1,5]⟩,⟨.or,[5,7]⟩,⟨.or,[3,5]⟩,⟨.or,[8,14]⟩,⟨.and,[6,10]⟩,⟨.and,[15,0]⟩,⟨.and,[8,12]⟩,⟨.and,[13,11]⟩,⟨.or,[16,17]⟩,⟨.or,[20,18]⟩,⟨.or,[21,19]⟩], 22⟩

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
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low19 : Lower true (varsX 19) (graphGoal 19) 2 := by
  have q := @lower_count true (vars 19) (graphGoal 19) (proper_of _ (by decide +kernel)) (graphPairs 19 68) (by decide +kernel)
  exact q
def K19 := extendKnown [] 2 [(134,[16,32,116,84,101])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V19 : Known true K19 := extend_ok (m:=19) baseKnown low19 (by decide +kernel)
def g49Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3ff63ff63ff63ff63f,0xf63ff63ff63ff63ff63f])),(BitVec.ofNat 152 (word80 [0x492049204920492049,0x20492049204920492049]))),(0x0,0x0),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xc7fbc7fbc7fbc7fbc7,0xfbc7fbc7fbc7fbc7fbc7])),(BitVec.ofNat 152 (word80 [0x924092409240924092,0x40924092409240924092]))),((BitVec.ofNat 152 (word80 [0xf8fdf8fdf8fdf8fdf8,0xfdf8fdf8fdf8fdf8fdf8])),(BitVec.ofNat 152 (word80 [0x248124812481248124,0x81248124812481248124]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g49C : List ColumnInfo := []
def g49A : List (List Nat) := [[],[84],[64],[64,80],[80,64],[80]]
def g49D3 (j : Nat) := if j=0 then 0x7 else 0
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
theorem g49G : graphValid g49 (boundsBefore K19) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low49 : Lower true (varsX 49) (graphGoal 49) 4 := lower_forest (g:=g49) (i:=0) (hints:=4) (before_sound K19 V19) g49G g49T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K49 := extendKnown K19 4 [(49,[]),(145,[117,101]),(146,[16,117,101]),(161,[84,116,100]),(164,[32,16,84,116,100]),(176,[64,16,33,50,83,115,99])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V49 : Known true K49 := extend_ok (m:=49) V19 low49 (by decide +kernel)
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
theorem g27G : graphValid g27 (boundsBefore K49) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low27 : Lower true (varsX 27) (graphGoal 27) 4 := lower_forest (g:=g27) (i:=0) (hints:=67) (before_sound K49 V49) g27G g27T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K27 := extendKnown K49 4 [(27,[]),(45,[33,84]),(54,[80,32,50]),(75,[96,16,49,67,84]),(77,[96,16,33,50,67,84]),(83,[16,99,83]),(86,[16,32,67,99,83]),(89,[48,65,33,96,32,82]),(90,[16,48,32,66,98,82]),(102,[32,83,100]),(105,[48,81,33,96,64]),(114,[16,80,32,99]),(116,[32,65,99,81]),(139,[116,84,101]),(141,[33,116,84,101]),(195,[16,99,116,83,84]),(197,[32,16,99,116,83,84]),(201,[97,33,115,67,82,84]),(202,[16,48,32,114,100,82]),(212,[32,65,99,113,81]),(226,[16,80,32,99,116])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V27 : Known true K27 := extend_ok (m:=27) V49 low27 (by decide +kernel)
def g51Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3de871ff81fc7ffc7b,0xd0e3ff03f8fff8f7a1c7])),(BitVec.ofNat 152 (word80 [0x81a892451429080903,0x51248a2852101206a249]))),((BitVec.ofNat 152 (word80 [0xc6980e3ffe007cff8d,0x301c7ffc00f9ff1a6038])),(BitVec.ofNat 152 (word80 [0x169adb66193212902d,0x35b6cc326425205a6b6d]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfb978fffffff80fff7,0x2f1fffffff01ffee5e3f])),(BitVec.ofNat 152 (word80 [0x124882040202000,0x2491040804040000492]))),((BitVec.ofNat 152 (word80 [0x66ff03fffffff000c,0xdfe07ffffffe0019bfc0])),(BitVec.ofNat 152 (word80 [0x26464930418040c24c,0x8c926083008184991924]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g51C : List ColumnInfo := [(2,0,49,0,4)]
def g51A : List (List Nat) := [[],[80]]
def g51D4 (j : Nat) := if j=0 then 0x1f else 0
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
theorem g51G : graphValid g51 (boundsBefore K27) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low51 : Lower true (varsX 51) (graphGoal 51) 5 := lower_forest (g:=g51) (i:=0) (hints:=68) (before_sound K27 V27) g51G g51T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K51 := extendKnown K27 5 [(51,[]),(53,[33,84]),(150,[16,32,116,84,101]),(153,[64,49,33,117,101]),(166,[32,116,100]),(210,[64,97,32,50,49,117]),(228,[80,97,32,49,66,116])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V51 : Known true K51 := extend_ok (m:=51) V27 low51 (by decide +kernel)
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
theorem g147G : graphValid g147 (boundsBefore K51) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low147 : Lower true (varsX 147) (graphGoal 147) 5 := lower_forest (g:=g147) (i:=0) (hints:=68) (before_sound K51 V51) g147G g147T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K147 := extendKnown K51 5 [(147,[]),(178,[16,80,32,50]),(180,[32,65,49,83])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V147 : Known true K147 := extend_ok (m:=147) V51 low147 (by decide +kernel)
def g177Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xdf7ec03c3ffe0fbefd,0x80787ffc1f7dfb00f0ff])),(BitVec.ofNat 152 (word80 [0x820404444444210408,0x8888888420810111111]))),(0x0,0x0),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1fbf43c3c3fff03f7e,0x878787ffe07efd0f0f0f])),(BitVec.ofNat 152 (word80 [0x40808888888420810,0x11111110841020222222]))),((BitVec.ofNat 152 (word80 [0xe03fbc03fc3fffc07f,0x7807f87fff80fef00ff0])),(BitVec.ofNat 152 (word80 [0x81011111110841020,0x22222221082040444444]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffc03ffc003fffff80,0x7ff8007fffff00fff000])),(BitVec.ofNat 152 (word80 [0x102022222221082040,0x44444442104080888888]))),(0x0,0x0)]
def g177C : List ColumnInfo := [(1,0,176,0,4),(16,0,161,0,4),(32,0,145,0,4),(128,0,49,0,4)]
def g177A : List (List Nat) := [[],[117],[84],[84,116],[116,84],[116],[64],[64,117],[64,80],[64,80,112],[64,112,80],[64,112],[80,64],[80,64,116],[80],[80,112],[80,116],[80,116,64],[112,64,84],[112,64],[112,80],[112],[112,84,64],[112,84]]
def g177D3 := limbs80 #[#[0x23ea6a1221e12148110,0x8028]]
def g177D4 := limbs80 #[#[0x2fd0910bd42443e48110,0x609085870]]
def g177H4 (j : Nat) := if j=0 then 0x241c else 0
def g177D5 (j : Nat) := if j=0 then 0xd1027d10 else 0
def g177H5 := limbs80 #[#[0x800008c125509f30c008,0x3483]]
def g177D6 (j : Nat) := if j=0 then 0x3904f else 0
def g177H6 := limbs80 #[#[0x1000001620071001ea,0x424000000000000]]
def g177L : Nat → Packing
  | 3 => (2,3,2,0,0,5,0,g177D3)
  | 4 => (3,2,2,0,0,5,0,g177D4)
  | 5 => (1,1,2,0,0,0,0,g177D5)
  | 6 => (1,0,2,0,0,0,0,g177D6)
  | _ => emptyPacking
def g177I : Nat → Nat → Option (Nat × Nat)
  | 4 => lookupWord 1 3 0 5 1 0 g177H4
  | 5 => lookupWord 2 11 2 9 2 3 g177H5
  | 6 => lookupWord 1 17 0 9 0 5 g177H6
  | _ => fun _ => none
def g177 : Forest := ⟨177,6,fun i => g177Y[i]?.getD (0,0),g177C,g177A,g177L,g177I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g177P3_0 : block g177 3 0 2=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g177B3 : block g177 3 0 2=true := g177P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g177P4_0 : block g177 4 0 3=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g177B4 : block g177 4 0 3=true := g177P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g177P5_0 : block g177 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g177B5 : block g177 5 0 1=true := g177P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g177P6_0 : block g177 6 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g177B6 : block g177 6 0 1=true := g177P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g177T : checkedTables g177 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g177 0 0 0 = true)
  · exact (rfl : block g177 1 0 0 = true)
  · exact (rfl : block g177 2 0 0 = true)
  · exact g177B3
  · exact g177B4
  · exact g177B5
  · exact g177B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g177G : graphValid g177 (boundsBefore K147) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low177 : Lower true (varsX 177) (graphGoal 177) 7 := lower_forest (g:=g177) (i:=0) (hints:=4) (before_sound K147 V147) g177G g177T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K177 := extendKnown K147 7 [(177,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V177 : Known true K177 := extend_ok (m:=177) V147 low177 (by decide +kernel)
def g55Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x7ff003ff80fffffff0,0x3ffffe03ff4b19901c7])),(BitVec.ofNat 152 (word80 [0x2a1a8251a148a02a1,0xa84a0a458a44b1811249]))),((BitVec.ofNat 152 (word80 [0x7ffffc0000ffc07fff,0xfc00ffffc068db260038])),(BitVec.ofNat 152 (word80 [0x44c132362c191344c9,0x326c8c891360d3265b6d]))),((BitVec.ofNat 152 (word80 [0x7fffffffff00007fff,0xffff0000000ff00e8e00])),(BitVec.ofNat 152 (word80 [0x1705c0b8305e1c1701,0xc0702f0e1c0db00eb6db]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x800000000000007fff,0xffffffffff99af6d703f])),(BitVec.ofNat 152 (word80 [0x180600c04060201802,0x80300000190c082492]))),((BitVec.ofNat 152 (word80 [0xffffffffffffff8000,0x6754f2ffc0])),(BitVec.ofNat 152 (word80 [0x60080300008000600c,0x300c010202240704924]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g55C : List ColumnInfo := [(2,0,53,0,5)]
def g55A : List (List Nat) := [[],[33,84]]
def g55D5 (j : Nat) := if j=0 then 0x3f else 0
def g55L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g55D5)
  | _ => emptyPacking
def g55I (_ _ : Nat) : Option (Nat × Nat) := none
def g55 : Forest := ⟨55,5,fun i => g55Y[i]?.getD (0,0),g55C,g55A,g55L,g55I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g55P5_0 : block g55 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g55B5 : block g55 5 0 1=true := g55P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g55T : checkedTables g55 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g55 0 0 0 = true)
  · exact (rfl : block g55 1 0 0 = true)
  · exact (rfl : block g55 2 0 0 = true)
  · exact (rfl : block g55 3 0 0 = true)
  · exact (rfl : block g55 4 0 0 = true)
  · exact g55B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g55G : graphValid g55 (boundsBefore K177) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low55 : Lower true (varsX 55) (graphGoal 55) 6 := lower_forest (g:=g55) (i:=0) (hints:=1348) (before_sound K177 V177) g55G g55T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K55 := extendKnown K177 6 [(55,[]),(59,[80,50]),(61,[64,33,49,80]),(157,[64,33,49,112,80,101]),(171,[80,50,116,100])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V55 : Known true K55 := extend_ok (m:=55) V177 low55 (by decide +kernel)
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
theorem g79G : graphValid g79 (boundsBefore K55) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low79 : Lower true (varsX 79) (graphGoal 79) 5 := lower_forest (g:=g79) (i:=0) (hints:=16778851) (before_sound K55 V55) g79G g79T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K79 := extendKnown K55 5 [(79,[]),(94,[64,33,49]),(110,[80,50,64]),(143,[48,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V79 : Known true K79 := extend_ok (m:=79) V55 low79 (by decide +kernel)
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
theorem g87G : graphValid g87 (boundsBefore K79) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low87 : Lower true (varsX 87) (graphGoal 87) 5 := lower_forest (g:=g87) (i:=0) (hints:=16778820) (before_sound K79 V79) g87G g87T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K87 := extendKnown K79 5 [(87,[]),(103,[33,84]),(107,[16,48,82,32,100,64]),(122,[48,82,100]),(234,[48,82,100,116])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V87 : Known true K87 := extend_ok (m:=87) V79 low87 (by decide +kernel)
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
def K91 := extendKnown K87 7 [(91,[]),(118,[16,32,67,99,83]),(203,[116,84]),(205,[33,116,84])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V91 : Known true K91 := extend_ok (m:=91) V87 low91 (by decide +kernel)
def g115Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xe007fffe1ffc00ffe1,0xfffffc3cf28ce6007c1f])),(BitVec.ofNat 152 (word80 [0x4850280444288a2144,0x420208803208c65294a5]))),((BitVec.ofNat 152 (word80 [0xfff803ffffffff0001,0xff0fffc3517a93f003e0])),(BitVec.ofNat 152 (word80 [0x8261304801300c0988,0x420900a413882318c63]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffc001ffffffffe,0xffffcadd91c0f83ff])),(BitVec.ofNat 152 (word80 [0x8041108841104200,0x8844200084c018842108]))),((BitVec.ofNat 152 (word80 [0x1fffffffff,0xfff000004f27e80ffc00])),(BitVec.ofNat 152 (word80 [0x130582611182208c01,0x1008c110492721294a52]))),((BitVec.ofNat 152 (word80 [0xffffffffe000000000,0x33aa61bf00000])),(BitVec.ofNat 152 (word80 [0x1c0603801e03c0f011,0xe08f02213a8619ce739c]))),(0x0,0x0),(0x0,0x0)]
def g115C : List ColumnInfo := [(0,64,49,2,5),(64,0,51,0,5),(1,0,114,0,4),(2,64,49,0,4),(32,0,83,0,4)]
def g115A : List (List Nat) := [[],[80]]
def g115D4 (j : Nat) := if j=0 then 0x57d4d20 else 0
def g115D5 := limbs80 #[#[0x480e140fd30ff20fd20,0x4088]]
def g115H5 (j : Nat) := if j=0 then 0x80 else 0
def g115D6 (j : Nat) := if j=0 then 0x18989f else 0
def g115H6 := limbs80 #[#[0xb60800000000000391c,0x200]]
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
theorem g115G : graphValid g115 (boundsBefore K91) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low115 : Lower true (varsX 115) (graphGoal 115) 7 := lower_forest (g:=g115) (i:=0) (hints:=16777284) (before_sound K91 V91) g115G g115T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K115 := extendKnown K91 7 [(115,[]),(117,[33,84]),(121,[64,49,33]),(213,[33,116,84]),(217,[64,49,33,117]),(218,[64,97,32,50,49,117]),(227,[116]),(233,[80,49,33,64,116])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V115 : Known true K115 := extend_ok (m:=115) V91 low115 (by decide +kernel)
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
theorem g151G : graphValid g151 (boundsBefore K115) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low151 : Lower true (varsX 151) (graphGoal 151) 6 := lower_forest (g:=g151) (i:=0) (hints:=1860) (before_sound K115 V115) g151G g151T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K151 := extendKnown K115 6 [(151,[]),(167,[33,84])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V151 : Known true K151 := extend_ok (m:=151) V115 low151 (by decide +kernel)
def g155Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffc03ffff0fffc03f,0xfff0fffff9560600f0ff])),(BitVec.ofNat 152 (word80 [0x202828140220028281,0x40220020980602111111]))),((BitVec.ofNat 152 (word80 [0xffffc01fff0ffffc0,0x1fff0ff01cb5390f0f00])),(BitVec.ofNat 152 (word80 [0x40b0305814020b0305,0x81402042189511333333]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffe0000ffffff,0xe0000fff23b56600000f])),(BitVec.ofNat 152 (word80 [0x8ac141615844ac2426,0x15844a8023b164eeeeee]))),((BitVec.ofNat 152 (word80 [0xf00000000000ffffff,0xfffff000134bf8f00ff0])),(BitVec.ofNat 152 (word80 [0x30181806088300808,0x6000304014868444444]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffff000000,0xcea8c5fff000])),(BitVec.ofNat 152 (word80 [0xc0202018000c03030,0x18088c08462084888888]))),(0x0,0x0)]
def g155C : List ColumnInfo := [(0,8,146,1,5),(2,0,153,0,5),(8,0,147,0,5),(1,8,146,0,4),(16,0,139,0,4),(128,0,27,0,4)]
def g155A : List (List Nat) := [[],[116]]
def g155D4 (j : Nat) := if j=0 then 0x5dd4543 else 0
def g155D5 (j : Nat) := if j=0 then 0x108404fd43 else 0
def g155H5 (j : Nat) := if j=0 then 0x20 else 0
def g155D6 (j : Nat) := if j=0 then 0x2c458bf else 0
def g155H6 (j : Nat) := if j=0 then 0x40 else 0
def g155L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g155D4)
  | 5 => (1,1,3,0,0,0,0,g155D5)
  | 6 => (1,0,3,0,0,0,0,g155D6)
  | _ => emptyPacking
def g155I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 4 0 0 g155H5
  | 6 => lookupWord 1 2 0 4 0 0 g155H6
  | _ => fun _ => none
def g155 : Forest := ⟨155,6,fun i => g155Y[i]?.getD (0,0),g155C,g155A,g155L,g155I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g155P4_0 : block g155 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g155B4 : block g155 4 0 1=true := g155P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g155P5_0 : block g155 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g155B5 : block g155 5 0 1=true := g155P5_0
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
  · exact g155B4
  · exact g155B5
  · exact g155B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g155G : graphValid g155 (boundsBefore K151) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low155 : Lower true (varsX 155) (graphGoal 155) 7 := lower_forest (g:=g155) (i:=0) (hints:=67) (before_sound K151 V151) g155G g155T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K155 := extendKnown K151 7 [(155,[]),(173,[33,84]),(211,[16,99,83]),(242,[16,80,32,99]),(244,[32,65,99,81])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V155 : Known true K155 := extend_ok (m:=155) V151 low155 (by decide +kernel)
def g179Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x1fe3fc03fc3f8ffe0,0x3fc7fff1d67c000f0f0f])),(BitVec.ofNat 152 (word80 [0x141482828288120142,0x82904024047c11111111]))),((BitVec.ofNat 152 (word80 [0xfe003fffc003ff1fff,0xc007e7fe313b00f000f0])),(BitVec.ofNat 152 (word80 [0x189913131311204983,0x13209240b13b55555555]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x3ffffffc001fff,0xfff807ffc5a10f00f0ff])),(BitVec.ofNat 152 (word80 [0x202004040400400204,0x4010080000022222222]))),((BitVec.ofNat 152 (word80 [0xffffc0000000001fff,0xfffff8003bc8f000ff00])),(BitVec.ofNat 152 (word80 [0x40c018181821848c08,0x180203093b8044444444]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffffe000,0x2816ffff0000])),(BitVec.ofNat 152 (word80 [0x810020202002001010,0x20040400000088888888]))),(0x0,0x0)]
def g179C : List ColumnInfo := [(2,0,177,0,7)]
def g179A : List (List Nat) := [[],[116],[80],[80,116]]
def g179D7 (j : Nat) := if j=0 then 0x3f else 0
def g179L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g179D7)
  | _ => emptyPacking
def g179I (_ _ : Nat) : Option (Nat × Nat) := none
def g179 : Forest := ⟨179,7,fun i => g179Y[i]?.getD (0,0),g179C,g179A,g179L,g179I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g179P7_0 : block g179 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g179B7 : block g179 7 0 1=true := g179P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g179T : checkedTables g179 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g179 0 0 0 = true)
  · exact (rfl : block g179 1 0 0 = true)
  · exact (rfl : block g179 2 0 0 = true)
  · exact (rfl : block g179 3 0 0 = true)
  · exact (rfl : block g179 4 0 0 = true)
  · exact (rfl : block g179 5 0 0 = true)
  · exact (rfl : block g179 6 0 0 = true)
  · exact g179B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g179G : graphValid g179 (boundsBefore K155) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low179 : Lower true (varsX 179) (graphGoal 179) 8 := lower_forest (g:=g179) (i:=0) (hints:=68) (before_sound K155 V155) g179G g179T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K179 := extendKnown K155 8 [(179,[]),(181,[33,84])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V179 : Known true K179 := extend_ok (m:=179) V155 low179 (by decide +kernel)
def g182Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfe1ff00ff87f87ffc0,0x3fc7f1ffd31dc000f00f])),(BitVec.ofNat 152 (word80 [0x1448a4a45121102292,0x82902488430dc5555555]))),((BitVec.ofNat 152 (word80 [0x1ffff0007ff87fff,0xc007fffc23ba600f00f0])),(BitVec.ofNat 152 (word80 [0x5882c0c1620a010b03,0xb214011219a63333333]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1fffffff80007fff,0xfff801ff9c1f30f00f0f])),(BitVec.ofNat 152 (word80 [0x61030101800c220c04,0xc0188201c1222222222]))),((BitVec.ofNat 152 (word80 [0xffe000000000007fff,0xfffffe000be4bf000ff0])),(BitVec.ofNat 152 (word80 [0x800c06060430443018,0x100200c2026494444444]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffff8000,0x6442cffff000])),(BitVec.ofNat 152 (word80 [0x1008080040004020,0x20040100000008888888]))),(0x0,0x0)]
def g182C : List ColumnInfo := [(2,0,180,0,5),(4,0,178,0,5),(16,0,166,0,5),(32,0,150,0,5)]
def g182A : List (List Nat) := [[],[33,84]]
def g182D6 (j : Nat) := if j=0 then 0x2709f else 0
def g182L : Nat → Packing
  | 6 => (1,0,2,0,0,0,0,g182D6)
  | _ => emptyPacking
def g182I (_ _ : Nat) : Option (Nat × Nat) := none
def g182 : Forest := ⟨182,6,fun i => g182Y[i]?.getD (0,0),g182C,g182A,g182L,g182I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g182P6_0 : block g182 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g182B6 : block g182 6 0 1=true := g182P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g182T : checkedTables g182 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g182 0 0 0 = true)
  · exact (rfl : block g182 1 0 0 = true)
  · exact (rfl : block g182 2 0 0 = true)
  · exact (rfl : block g182 3 0 0 = true)
  · exact (rfl : block g182 4 0 0 = true)
  · exact (rfl : block g182 5 0 0 = true)
  · exact g182B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g182G : graphValid g182 (boundsBefore K179) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low182 : Lower true (varsX 182) (graphGoal 182) 7 := lower_forest (g:=g182) (i:=0) (hints:=270599488) (before_sound K179 V179) g182G g182T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K182 := extendKnown K179 7 [(182,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V182 : Known true K182 := extend_ok (m:=182) V179 low182 (by decide +kernel)
def g185Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfc7fc07fc7ffffc07f,0xc7ffffff909d100f0fff])),(BitVec.ofNat 152 (word80 [0x80081008010008100,0x80100100000001111111]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x7fff8007f87fff80,0x7f87f87aacdc000000f])),(BitVec.ofNat 152 (word80 [0x5155125512a1552255,0x14a152102acdceeeeeee]))),((BitVec.ofNat 152 (word80 [0x7ffffff8007fffff,0xf8007ff87b2860f0f0f0])),(BitVec.ofNat 152 (word80 [0x6206040600c2060406,0xc20401322822222222]))),((BitVec.ofNat 152 (word80 [0xff80000000007fffff,0xffff80000ff28f00ff00])),(BitVec.ofNat 152 (word80 [0x801818182304180818,0x10018220dd004444444]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffff800000,0x6446ffff0000])),(BitVec.ofNat 152 (word80 [0x6020600400603060,0x260460444006d8888888]))),(0x0,0x0)]
def g185C : List ColumnInfo := [(8,0,177,0,7)]
def g185A : List (List Nat) := [[],[117],[84],[84,116],[116,84],[116]]
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
theorem g185G : graphValid g185 (boundsBefore K182) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low185 : Lower true (varsX 185) (graphGoal 185) 8 := lower_forest (g:=g185) (i:=0) (hints:=3) (before_sound K182 V182) g185G g185T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K185 := extendKnown K182 8 [(185,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V185 : Known true K185 := extend_ok (m:=185) V182 low185 (by decide +kernel)
def g199Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xe003ff80ffe03ffff0,0x1ff80ffc0009ede81c0])),(BitVec.ofNat 152 (word80 [0x45a8a51a2a458a12a2,0xd4251a148b009e8eb6db]))),((BitVec.ofNat 152 (word80 [0xfffc0000ffffc07fff,0xfe0000fffff8da218e07])),(BitVec.ofNat 152 (word80 [0x8130362c0c891304c0,0x98362c191248d2019249]))),((BitVec.ofNat 152 (word80 [0xffffffff0000007fff,0xffffff00000ff10e7038])),(BitVec.ofNat 152 (word80 [0x1c038300f0e1c0700,0xe038301e1c0ad10a1249]))),(0x0,0x0),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x7fff,0xffffffffff99af6d003f])),(BitVec.ofNat 152 (word80 [0x1602c040b01020580b,0x14000a000112c646db6]))),((BitVec.ofNat 152 (word80 [0xffffffffffffff8000,0x6754f2ffc0])),(BitVec.ofNat 152 (word80 [0x18030000c00000600c,0x18040c0202500704924]))),(0x0,0x0)]
def g199C : List ColumnInfo := [(2,0,197,0,4)]
def g199A : List (List Nat) := [[],[33]]
def g199D4 (j : Nat) := if j=0 then 0x3f else 0
def g199L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g199D4)
  | _ => emptyPacking
def g199I (_ _ : Nat) : Option (Nat × Nat) := none
def g199 : Forest := ⟨199,4,fun i => g199Y[i]?.getD (0,0),g199C,g199A,g199L,g199I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g199P4_0 : block g199 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g199B4 : block g199 4 0 1=true := g199P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g199T : checkedTables g199 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g199 0 0 0 = true)
  · exact (rfl : block g199 1 0 0 = true)
  · exact (rfl : block g199 2 0 0 = true)
  · exact (rfl : block g199 3 0 0 = true)
  · exact g199B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g199G : graphValid g199 (boundsBefore K185) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low199 : Lower true (varsX 199) (graphGoal 199) 5 := lower_forest (g:=g199) (i:=0) (hints:=16778855) (before_sound K185 V185) g199G g199T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K199 := extendKnown K185 5 [(199,[]),(206,[48,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V199 : Known true K199 := extend_ok (m:=199) V185 low199 (by decide +kernel)
def g214Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0xff007fe1ff0fffc03f,0xfff0fffff95e0200f0ff])),(BitVec.ofNat 152 (word80 [0xa0501440220028281,0x40220020980602111111]))),((BitVec.ofNat 152 (word80 [0xffff8001fff0ffffc0,0x1fff0ff01c35b90f0f00])),(BitVec.ofNat 152 (word80 [0x2c06058814020b0305,0x81402042183511333333]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffe0000ffffff,0xe0000fff23b566f0000f])),(BitVec.ofNat 152 (word80 [0xb028160058442c0406,0x5844280213164666666]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffff,0xfffff000134bf8000ff0])),(BitVec.ofNat 152 (word80 [0xc0b058116088b02828,0x16000b040348e8cccccc]))),((BitVec.ofNat 152 (word80 [0xffffffffffff000000,0xcea8c5fff000])),(BitVec.ofNat 152 (word80 [0xc060018000c03030,0x18088c08468880888888]))),(0x0,0x0)]
def g214C : List ColumnInfo := [(4,0,210,0,5)]
def g214A : List (List Nat) := [[],[113,98]]
def g214D5 (j : Nat) := if j=0 then 0x3f else 0
def g214L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g214D5)
  | _ => emptyPacking
def g214I (_ _ : Nat) : Option (Nat × Nat) := none
def g214 : Forest := ⟨214,5,fun i => g214Y[i]?.getD (0,0),g214C,g214A,g214L,g214I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g214P5_0 : block g214 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g214B5 : block g214 5 0 1=true := g214P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g214T : checkedTables g214 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g214 0 0 0 = true)
  · exact (rfl : block g214 1 0 0 = true)
  · exact (rfl : block g214 2 0 0 = true)
  · exact (rfl : block g214 3 0 0 = true)
  · exact (rfl : block g214 4 0 0 = true)
  · exact g214B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g214G : graphValid g214 (boundsBefore K199) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low214 : Lower true (varsX 214) (graphGoal 214) 6 := lower_forest (g:=g214) (i:=0) (hints:=285279808) (before_sound K199 V199) g214G g214T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K214 := extendKnown K199 6 [(214,[]),(230,[33,84])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V214 : Known true K214 := extend_ok (m:=214) V199 low214 (by decide +kernel)
def g248Y : Array (Bits × Bits) := #[(0x0,0x0),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xc003ff0ffc3ffc00ff,0xffffffc02b3e79000fc0])),(BitVec.ofNat 152 (word80 [0x90a80a204890a92a42,0x91204088292e194d34d3]))),((BitVec.ofNat 152 (word80 [0xfffc000fffffffff00,0x3ff0fffec8a9d703f03f])),(BitVec.ofNat 152 (word80 [0x2304c411002300c13,0x4209020009d3145145]))),((BitVec.ofNat 152 (word80 [0xfffffff0003fffffff,0xc000fffd77e88afc003f])),(BitVec.ofNat 152 (word80 [0x4c090026104c03004,0x584120172a00828a28a]))),((BitVec.ofNat 152 (word80 [0x3fffffff,0xffff00012697f4000fc0])),(BitVec.ofNat 152 (word80 [0x2702e08b8227024098,0x26009c110691e4b2cb2c]))),((BitVec.ofNat 152 (word80 [0xffffffffffc0000000,0x39d530dfff000])),(BitVec.ofNat 152 (word80 [0x3803000c00380380e0,0x3808e0208d5204c30c30]))),(0x0,0x0)]
def g248C : List ColumnInfo := [(0,8,176,64,5)]
def g248A : List (List Nat) := [[],[117],[84],[84,116],[116,84],[116],[99],[99,117],[99,84],[99,84,116],[99,116,84],[99,116]]
def g248D5 (j : Nat) := if j=0 then 0x3f else 0
def g248L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g248D5)
  | _ => emptyPacking
def g248I (_ _ : Nat) : Option (Nat × Nat) := none
def g248 : Forest := ⟨248,5,fun i => g248Y[i]?.getD (0,0),g248C,g248A,g248L,g248I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g248P5_0 : block g248 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g248B5 : block g248 5 0 1=true := g248P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g248T : checkedTables g248 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g248 0 0 0 = true)
  · exact (rfl : block g248 1 0 0 = true)
  · exact (rfl : block g248 2 0 0 = true)
  · exact (rfl : block g248 3 0 0 = true)
  · exact (rfl : block g248 4 0 0 = true)
  · exact g248B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g248G : graphValid g248 (boundsBefore K214) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low248 : Lower true (varsX 248) (graphGoal 248) 6 := lower_forest (g:=g248) (i:=0) (hints:=1128620032) (before_sound K214 V214) g248G g248T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K248 := extendKnown K214 6 [(248,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V248 : Known true K248 := extend_ok (m:=248) V214 low248 (by decide +kernel)
def g63Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffffffffffffffffff,0xffe29798e321cb00f0ff])),(BitVec.ofNat 152 (word80 [0x14000a8004a001480,0x14e0948880008a111111]))),((BitVec.ofNat 152 (word80 [0xffffc0000ffffc0,0x7d409d2ed1b2000f00])),(BitVec.ofNat 152 (word80 [0xa6a0532836ca09910,0x666d409d2e5182bbbbbb]))),((BitVec.ofNat 152 (word80 [0xfffffffff000000,0x1cf88f852b660f0000])),(BitVec.ofNat 152 (word80 [0x3380a9c02a700ade02,0xb814d88c852b66777777]))),((BitVec.ofNat 152 (word80 [0xfffffffffffffff,0xff216395b13d3d00000f])),(BitVec.ofNat 152 (word80 [0x5c0cce033380cce024,0xc0016315313d35eeeeee]))),((BitVec.ofNat 152 (word80 [0xfff000000000000000,0x115e685ddcf0f00ff0])),(BitVec.ofNat 152 (word80 [0x6000f0003c000f0007,0x100a40418c70444444]))),(0xcea977125e06fff000,(BitVec.ofNat 152 (word80 [0x800f0003c000f00038,0xa2133125000888888]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g63C : List ColumnInfo := [(2,0,61,0,6),(4,0,59,0,6),(8,0,55,0,6),(0,4,27,32,5),(1,0,54,0,4),(1,8,54,0,4),(16,2,45,0,4),(32,4,27,0,4)]
def g63A : List (List Nat) := [[],[33,84],[64,33,49,80],[64,49],[80,50],[80,49,33,64]]
def g63D4 (j : Nat) := if j=0 then 0x4d576d0630 else 0
def g63D5 := limbs80 #[#[0x5d0630bdd9510f9d4910,0x930c0b759230f]]
def g63H5 (j : Nat) := if j=0 then 0x8 else 0
def g63D6 := limbs80 #[#[0xb0942c07f503bc61f510,0x1908328d3081d4a]]
def g63H6 := limbs80 #[#[0x3112214c00001078107c,0x2a1e]]
def g63D7 (j : Nat) := if j=0 then 0x3ea881bf else 0
def g63H7 := limbs80 #[#[0x180000000000000001,0xc0024322000000111090,0xea1090801940000001c,0x44b00000]]
def g63L : Nat → Packing
  | 4 => (1,3,3,0,0,0,0,g63D4)
  | 5 => (4,2,3,0,0,5,0,g63D5)
  | 6 => (3,1,3,0,0,6,0,g63D6)
  | 7 => (1,0,3,0,0,0,0,g63D7)
  | _ => emptyPacking
def g63I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 4 0 0 g63H5
  | 6 => lookupWord 2 11 2 9 2 3 g63H6
  | 7 => lookupWord 3 31 1 9 2 3 g63H7
  | _ => fun _ => none
def g63 : Forest := ⟨63,7,fun i => g63Y[i]?.getD (0,0),g63C,g63A,g63L,g63I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P4_0 : block g63 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g63B4 : block g63 4 0 1=true := g63P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P5_0 : block g63 5 0 4=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g63B5 : block g63 5 0 4=true := g63P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P6_0 : block g63 6 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P6_2 : block g63 6 2 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g63B6 : block g63 6 0 3=true := (@block_merge g63 6 0 2 1 g63P6_0 g63P6_2)
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
  · exact g63B4
  · exact g63B5
  · exact g63B6
  · exact g63B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63G : graphValid g63 (boundsBefore K248) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low63 : Lower true (varsX 63) (graphGoal 63) 8 := lower_forest (g:=g63) (i:=0) (hints:=1347) (before_sound K248 V248) g63G g63T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K63 := extendKnown K248 8 [(63,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V63 : Known true K63 := extend_ok (m:=63) V248 low63 (by decide +kernel)
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
def K95 := extendKnown K63 8 [(95,[]),(111,[33,84]),(126,[64,33,49,80])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V95 : Known true K95 := extend_ok (m:=95) V63 low95 (by decide +kernel)
def g119Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xf8001fffffff00ff55,0xa23193a23c000003f03f])),(BitVec.ofNat 152 (word80 [0x510d44251052161455,0x822190a2289249249249]))),((BitVec.ofNat 152 (word80 [0xffffe0007fffff00eb,0x7e8d8016080fc0000fc0])),(BitVec.ofNat 152 (word80 [0x6049813604642426e9,0x76098006005145145145]))),((BitVec.ofNat 152 (word80 [0xffffffff800000001d,0x8e4ae985c3f000fc0000])),(BitVec.ofNat 152 (word80 [0x800e00380178383819,0x8a0a8185c030c30c30c3]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffffff20,0x49c585ecf4003f000fff])),(BitVec.ofNat 152 (word80 [0x21008402180000000,0x8c40508d52492492492]))),((BitVec.ofNat 152 (word80 [0x11,0x75383e5b40003ffff000])),(BitVec.ofNat 152 (word80 [0x46011804600404000,0x75102a50024924924924]))),((BitVec.ofNat 152 (word80 [0xce,0x937660389bffc0000000])),(BitVec.ofNat 152 (word80 [0x7801e007800808006,0x17460381b8e38e38e38]))),(0x0,0x0),(0x0,0x0)]
def g119C : List ColumnInfo := [(1,0,118,0,7),(2,0,117,0,7),(4,0,115,0,7),(0,64,49,6,6),(64,0,55,0,6),(16,0,103,0,5),(32,0,87,0,5)]
def g119A : List (List Nat) := [[],[33,84]]
def g119D5 (j : Nat) := if j=0 then 0x4fb7059243 else 0
def g119D6 := limbs80 #[#[0xed8143bd58443be58043,0x59243fed8143e7d0e43b,0x401413142f3185b400bf,0x1002628]]
def g119H6 (j : Nat) := if j=0 then 0x0 else 0
def g119D7 := limbs80 #[#[0x47888807f90ffa87fc43,0x6a1474365a981d90ea61,0x190e]]
def g119H7 := limbs80 #[#[0x30000000,0x620000000000d5000000,0xc900c300110014]]
def g119D8 (j : Nat) := if j=0 then 0x468817f else 0
def g119H8 (j : Nat) := if j=0 then 0x68520000076 else 0
def g119L : Nat → Packing
  | 5 => (1,3,3,0,0,0,0,g119D5)
  | 6 => (6,2,3,0,0,6,0,g119D6)
  | 7 => (3,1,3,0,0,7,0,g119D7)
  | 8 => (1,0,3,0,0,0,0,g119D8)
  | _ => emptyPacking
def g119I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 2 0 4 0 0 g119H6
  | 7 => lookupWord 1 29 0 8 3 1 g119H7
  | 8 => lookupWord 1 7 0 7 2 1 g119H8
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
theorem g119G : graphValid g119 (boundsBefore K95) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low119 : Lower true (varsX 119) (graphGoal 119) 9 := lower_forest (g:=g119) (i:=0) (hints:=16778564) (before_sound K95 V95) g119G g119T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K119 := extendKnown K95 9 [(119,[]),(123,[80,50]),(125,[64,33,49,80]),(235,[80,50,116])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V119 : Known true K119 := extend_ok (m:=119) V95 low119 (by decide +kernel)
def g159Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3ffffffffffffffff,0xfe98ba2e079c9000f0ff])),(BitVec.ofNat 152 (word80 [0x5805000a8012801480,0x5290a82c040881111111]))),((BitVec.ofNat 152 (word80 [0xfc003fffc0003fffc0,0x1e50ab87c19600f0f00])),(BitVec.ofNat 152 (word80 [0x9029805300db009901,0x99a50aa8641843333333]))),((BitVec.ofNat 152 (word80 [0x3fffffffc00000,0x738da5275700f00000])),(BitVec.ofNat 152 (word80 [0xe0ce0a9c0a9c0ade0a,0xe0718ca5275707777777]))),((BitVec.ofNat 152 (word80 [0x3fffffffffffff,0xfc85179497b3d000000f])),(BitVec.ofNat 152 (word80 [0x1702ce02ce02ce013,0x5179093b35eeeeeee]))),((BitVec.ofNat 152 (word80 [0xffffc0000000000000,0x45f462f96d0f000ff0])),(BitVec.ofNat 152 (word80 [0x1800f000f000f001c,0x401442994504444444]))),(0x0,0x0),(0x0,0x0),(0x33a4dd980e26ffff000,(BitVec.ofNat 152 (word80 [0x20030003000300020,0xa411000a028888888]))),(0x0,0x0)]
def g159C : List ColumnInfo := [(4,0,155,0,7)]
def g159A : List (List Nat) := [[]]
def g159D7 (j : Nat) := if j=0 then 0x7f else 0
def g159L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g159D7)
  | _ => emptyPacking
def g159I (_ _ : Nat) : Option (Nat × Nat) := none
def g159 : Forest := ⟨159,7,fun i => g159Y[i]?.getD (0,0),g159C,g159A,g159L,g159I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g159P7_0 : block g159 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g159B7 : block g159 7 0 1=true := g159P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g159T : checkedTables g159 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g159 0 0 0 = true)
  · exact (rfl : block g159 1 0 0 = true)
  · exact (rfl : block g159 2 0 0 = true)
  · exact (rfl : block g159 3 0 0 = true)
  · exact (rfl : block g159 4 0 0 = true)
  · exact (rfl : block g159 5 0 0 = true)
  · exact (rfl : block g159 6 0 0 = true)
  · exact g159B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g159G : graphValid g159 (boundsBefore K119) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low159 : Lower true (varsX 159) (graphGoal 159) 8 := lower_forest (g:=g159) (i:=0) (hints:=1859) (before_sound K119 V119) g159G g159T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K159 := extendKnown K119 8 [(159,[]),(175,[33,84])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V159 : Known true K159 := extend_ok (m:=159) V119 low159 (by decide +kernel)
def g183Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfffffff800fffffe03,0xfecbaa01b20000f00f0f])),(BitVec.ofNat 152 (word80 [0x148a01506a0940a458,0xa6cb0a00321111111111]))),((BitVec.ofNat 152 (word80 [0xffc07fffff001ffffc,0x34e5baa81000f0000f0])),(BitVec.ofNat 152 (word80 [0x191322624c4d88c891,0x334e5a2a815555555555]))),((BitVec.ofNat 152 (word80 [0x7fffffffe00000,0xd372d62500f000f000])),(BitVec.ofNat 152 (word80 [0x5e1c0b80700e02f0e1,0xc0c332d6253333333333]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x7fffffffffffff,0xf922299d6b0f000f00ff])),(BitVec.ofNat 152 (word80 [0x60200c008010030000,0x202195082222222222]))),((BitVec.ofNat 152 (word80 [0xffff80000000000000,0x98c67ad8f0000fff00])),(BitVec.ofNat 152 (word80 [0x8000300300600c0102,0x10c428c04444444444]))),(0x0,0x0),(0x665142404fffff00000,(BitVec.ofNat 152 (word80 [0x40040080100000,0x8888888888]))),(0x0,0x0)]
def g183C : List ColumnInfo := [(2,0,181,0,8)]
def g183A : List (List Nat) := [[],[33,84]]
def g183D8 (j : Nat) := if j=0 then 0x7f else 0
def g183L : Nat → Packing
  | 8 => (1,0,1,0,0,0,0,g183D8)
  | _ => emptyPacking
def g183I (_ _ : Nat) : Option (Nat × Nat) := none
def g183 : Forest := ⟨183,8,fun i => g183Y[i]?.getD (0,0),g183C,g183A,g183L,g183I⟩
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
  · exact (rfl : block g183 5 0 0 = true)
  · exact (rfl : block g183 6 0 0 = true)
  · exact (rfl : block g183 7 0 0 = true)
  · exact g183B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183G : graphValid g183 (boundsBefore K159) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low183 : Lower true (varsX 183) (graphGoal 183) 9 := lower_forest (g:=g183) (i:=0) (hints:=1348) (before_sound K159 V159) g183G g183T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K183 := extendKnown K159 9 [(183,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V183 : Known true K183 := extend_ok (m:=183) V159 low183 (by decide +kernel)
def g187Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffffffc03ffffff,0xec8bac8b448000f0f0ff])),(BitVec.ofNat 152 (word80 [0xa005000808000080,0x28020880448111111111]))),((BitVec.ofNat 152 (word80 [0xfff0007ffffc03ffc0,0x19246d9c8e200f000f00])),(BitVec.ofNat 152 (word80 [0x28c2961450a0a8a109,0x98246c9c860555555555]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffff80000003ffff,0xcd31f67620a00000000f])),(BitVec.ofNat 152 (word80 [0xb10b1859613132ca11,0x531f676202eeeeeeeee]))),((BitVec.ofNat 152 (word80 [0xfffffffffffffc0000,0x2531855ba60f00f0ff0])),(BitVec.ofNat 152 (word80 [0x20020018000000c02,0x2011001382222222222]))),(0x45c462c771f000ff000,(BitVec.ofNat 152 (word80 [0x3c03c01e01c1c0f01c,0x45c442c021444444444]))),(0x0,0x0),(0x33a4d3e0015ffff00000,(BitVec.ofNat 152 (word80 [0xc00c00600202030020,0x1808340014888888888]))),(0x0,0x0)]
def g187C : List ColumnInfo := [(2,0,185,0,8)]
def g187A : List (List Nat) := [[],[116]]
def g187D8 (j : Nat) := if j=0 then 0x7f else 0
def g187L : Nat → Packing
  | 8 => (1,0,1,0,0,0,0,g187D8)
  | _ => emptyPacking
def g187I (_ _ : Nat) : Option (Nat × Nat) := none
def g187 : Forest := ⟨187,8,fun i => g187Y[i]?.getD (0,0),g187C,g187A,g187L,g187I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P8_0 : block g187 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g187B8 : block g187 8 0 1=true := g187P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187T : checkedTables g187 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g187 0 0 0 = true)
  · exact (rfl : block g187 1 0 0 = true)
  · exact (rfl : block g187 2 0 0 = true)
  · exact (rfl : block g187 3 0 0 = true)
  · exact (rfl : block g187 4 0 0 = true)
  · exact (rfl : block g187 5 0 0 = true)
  · exact (rfl : block g187 6 0 0 = true)
  · exact (rfl : block g187 7 0 0 = true)
  · exact g187B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187G : graphValid g187 (boundsBefore K183) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low187 : Lower true (varsX 187) (graphGoal 187) 9 := lower_forest (g:=g187) (i:=0) (hints:=67) (before_sound K183 V183) g187G g187T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K187 := extendKnown K183 9 [(187,[]),(189,[33,84])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V187 : Known true K187 := extend_ok (m:=187) V183 low187 (by decide +kernel)
def g207Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfc00ffffffffffffff,0x4c25363f4a4801f0001f])),(BitVec.ofNat 152 (word80 [0x481610542128429029,0x4804363e02414a5294a5]))),((BitVec.ofNat 152 (word80 [0xfffffffe0003fff800,0xf0155d26a8b03e0003e0])),(BitVec.ofNat 152 (word80 [0x90a402980db01320cc,0xf015542288a0c6318c63]))),((BitVec.ofNat 152 (word80 [0xfffffffc000000,0x39c4d2d30f87c0007c00])),(BitVec.ofNat 152 (word80 [0xe13804e009c01bc170,0x388452830f80c6318c63]))),((BitVec.ofNat 152 (word80 [0xfffffffffffffe,0x428bca0bd9e8000f801f])),(BitVec.ofNat 152 (word80 [0x1c047008e011c0180,0x89c801d9aa94a5294a]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffff00000000000000,0x22fa317cb680000fffe0])),(BitVec.ofNat 152 (word80 [0x98013002600200,0x262215c2005294a5294]))),((BitVec.ofNat 152 (word80 [1,0x9d26ecc07137fff00000])),(BitVec.ofNat 152 (word80 [0x200e001c003800400,0x52288407016318c6318]))),(0x0,0x0)]
def g207C : List ColumnInfo := [(2,0,205,0,7)]
def g207A : List (List Nat) := [[],[33],[48,118],[48,33,118]]
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
theorem g207G : graphValid g207 (boundsBefore K187) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low207 : Lower true (varsX 207) (graphGoal 207) 8 := lower_forest (g:=g207) (i:=0) (hints:=16778851) (before_sound K187 V187) g207G g207T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K207 := extendKnown K187 8 [(207,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V207 : Known true K207 := extend_ok (m:=207) V187 low207 (by decide +kernel)
def g215Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfff0007ffffff00ff5,0xb361d03e280001f0001f])),(BitVec.ofNat 152 (word80 [0x42a135092845216141,0xb261d01428294a5294a5]))),((BitVec.ofNat 152 (word80 [0xffffff8003fffff002,0x16e8554587003e007fe0])),(BitVec.ofNat 152 (word80 [0x4c02601b006424262,0x10605505810842108421]))),((BitVec.ofNat 152 (word80 [0xfffffffffc00000009,0xd8c2c299d107c00f8000])),(BitVec.ofNat 152 (word80 [0x17003801c017838381,0x98c24019d118c6318c63]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffffffffffffa,0x4fe283ab8f8000003ff])),(BitVec.ofNat 152 (word80 [0x980240120098000008,0x48a282a105294a5294a]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [9,0x1711a3877600000ffc00])),(BitVec.ofNat 152 (word80 [0xe00b805c02e0040408,0x711a28226e739ce739c]))),((BitVec.ofNat 152 (word80 [4,0xe9177e4005fffff00000])),(BitVec.ofNat 152 (word80 [0xc00600300080804,0x41140240048421084210]))),(0x0,0x0)]
def g215C : List ColumnInfo := [(2,0,213,0,7),(4,0,211,0,7),(0,64,145,6,6),(1,0,214,0,6),(64,0,151,0,6),(16,0,199,0,5),(65,0,150,0,5),(128,0,87,0,5),(18,0,197,0,4),(129,0,86,0,4)]
def g215A : List (List Nat) := [[]]
def g215D5 := limbs80 #[#[0x31fb2aa8987595354130,0xeb2a7a86613edc1654c,0x4f3cb2ea1985d973d433,0x53d72a9b02a77c5c4605,0xe35cafb299a06ba54d81,0x183b]]
def g215D6 := limbs80 #[#[0xb58853bd58453be58053,0x54130d7d4e53bed8153b,0x5130f794d30f754d30fe,0x330bfd9530bf59530ef5,0x30ef55330f754f30fed4,0xdf54f50df54d50bf597,0xfed8153fe18153bf58f5,0xf95153ef55153bfd8153,0x95253ef55253bf58253e,0x481e0a83000bf59653ef,0x509c4b241147e3c1b0c0,0xf1d4e46c34998c05a2b9,0x39010b80e1c9a350e843,0x608e08a3e01e008f804,0x60860800060800003820,0x38204608f18400608000,0x182382]]
def g215H6 := limbs80 #[#[0x1432000000,0x7800000075000000,0x0,0x2700,0x0,0xf600000000f10000,0x0,0xa00000930000]]
def g215D7 := limbs80 #[#[0xd50ff987f4c37ca9bd54,0xa7fe53fea9ff14ffea1f,0xd0bf4d9f0ba3e0f803fe,0x478c0c291228c059d445,0x82453c60628a72c60614,0x828c1239451818e314d1,0x8a3028e410ce58c07194,0xa41460918e41]]
def g215H7 := limbs80 #[#[0xe40000780,0x7480000000000000000,0x8000000000000000000c,0x5980000000011,0x2e0000000002de000071,0x9180000770000000009d,0xdb0000000001880000,0x192aa00000d00000000,0xa25c00c08039b7100594,0xe3a,0x500003d60000728e6000,0x3]]
def g215D8 (j : Nat) := if j=0 then 0x3421017f else 0
def g215H8 := limbs80 #[#[0x900000000f300c80044c,0x800056d591d2c77]]
def g215L : Nat → Packing
  | 5 => (9,3,4,0,0,6,0,g215D5)
  | 6 => (27,2,4,0,0,9,0,g215D6)
  | 7 => (10,1,4,0,0,9,0,g215D7)
  | 8 => (1,0,4,0,0,0,0,g215D8)
  | _ => emptyPacking
def g215I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 2 79 0 8 4 0 g215H6
  | 7 => lookupWord 6 101 2 9 5 0 g215H7
  | 8 => lookupWord 2 17 2 8 4 0 g215H8
  | _ => fun _ => none
def g215 : Forest := ⟨215,8,fun i => g215Y[i]?.getD (0,0),g215C,g215A,g215L,g215I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215P5_0 : block g215 5 0 9=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g215B5 : block g215 5 0 9=true := g215P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215P6_0 : block g215 6 0 5=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215P6_5 : block g215 6 5 22=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g215B6 : block g215 6 0 27=true := (@block_merge g215 6 0 5 22 g215P6_0 g215P6_5)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215P7_0 : block g215 7 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215P7_2 : block g215 7 2 8=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g215B7 : block g215 7 0 10=true := (@block_merge g215 7 0 2 8 g215P7_0 g215P7_2)
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
  · exact g215B5
  · exact g215B6
  · exact g215B7
  · exact g215B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215G : graphValid g215 (boundsBefore K207) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low215 : Lower true (varsX 215) (graphGoal 215) 9 := lower_forest (g:=g215) (i:=0) (hints:=16778820) (before_sound K207 V207) g215G g215T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K215 := extendKnown K207 9 [(215,[]),(231,[33,84])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V215 : Known true K215 := extend_ok (m:=215) V207 low215 (by decide +kernel)
def g219Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffffff83fffff628eb,0x10b3680003f800003fff])),(BitVec.ofNat 152 (word80 [0x10a0810801040220a2,0x10816812244891224489]))),((BitVec.ofNat 152 (word80 [0xffffc1ffe02d788,0x15ccc201fc000fffc000])),(BitVec.ofNat 152 (word80 [0x2c00a004008225088,0x150c40060c183060c183]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfff000001ffffbd84c,0x8b211e000007f000007f])),(BitVec.ofNat 152 (word80 [0x83042c10885001d84c,0x920164c993264c99326]))),((BitVec.ofNat 152 (word80 [0xffffffffe0000804f4,0x691ab3fe0000001fff80])),(BitVec.ofNat 152 (word80 [0x240130000260480440,0x2812932850a142850a14]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x91713,0xa28774000007ffe00000])),(BitVec.ofNat 152 (word80 [0x3809c0211380880713,0xa28320b162c58b162c58]))),((BitVec.ofNat 152 (word80 [0x4e917,0x7e4005fffff800000000])),(BitVec.ofNat 152 (word80 [0xc00e00421c01048915,0x424004c183060c183060]))),(0x0,0x0)]
def g219C : List ColumnInfo := [(1,0,218,0,7),(2,0,217,0,7),(8,0,211,0,7),(16,0,203,0,7),(64,0,155,0,7),(128,0,91,0,7),(0,8,146,65,6),(0,64,145,10,6),(1,8,146,64,5),(2,64,145,8,5),(8,64,145,2,5),(9,0,210,0,5),(72,0,147,0,5),(17,0,202,0,4),(18,0,201,0,4),(24,0,195,0,4),(65,0,146,0,4),(65,8,146,0,4),(80,0,139,0,4),(129,0,90,0,4),(130,0,89,0,4),(136,0,83,0,4),(144,0,75,0,4),(192,0,27,0,4)]
def g219A : List (List Nat) := [[],[116],[16,99],[16,99,116]]
def g219D5 := limbs80 #[#[0x54d30443d454d514c110,0x44237e0d7654d10e5965,0x54f6154130c5f731d563,0x304085b5460396]]
def g219D6 := limbs80 #[#[0x3aca9aa09847f7558d10,0xfb2a698221fc5453044,0x437cb2a60887db634c11,0x10bf2ea98221bed95304,0x4436eb1aa6885fb754c1,0xd109fceca9a213f5d953,0x3442bfbaac6886df6358,0x8d10cfeeab1a219f1d56,0x504c27ebaec6884ff755,0x58530ebaa6a8a61bed85,0xf614c2bfbaac2985df73,0x5551309faebb0a61b754,0xc7654c27fb8aca9867f6,0x7054d40ddaa7b12813f5,0x5c7654ca7ebaec2995fb,0xb70589539fae3b02a73f,0x168983e1c0c85806005f,0x602c958a64c229087634,0x1e88429f8f674369a8c6,0x3100b458ab956a04ca49,0x68c1030400006605804,0x1a3040050704101,0x1000010d040650400504,0x30826305841001010014,0x30c1000001]]
def g219H6 := limbs80 #[#[0xe600212005268c01613,0x612a9b3a]]
def g219D7 := limbs80 #[#[0xf58d10fe4c110bbd8940,0xd8530fe54130bfd8d10b,0x9530bf59530f754d30bf,0x153bfd9532bfd8532bfd,0x10ff58d10ff54d10bfd8,0xff54d20ff4c520ffd8d,0xff55130ff58530ff5453,0xf54d40ff59530ff59130,0x58953ff58153ff54d42f,0x28898ea15818014800ff,0x50a7f49087cfb1bf2f45,0xb57686c8586af25bcb0d,0x1a0091607be6796ea5c3,0x5286e44e88423823e5c6,0xc12070d0e18223050600,0x6884b0c5801c30405951,0x9460e18284048468e4c,0xe18202030092c353038,0x50e182024b8468e5898d,0xc384022078a14229103c,0x200b081c30403890161,0x1820201186386a546223,0x6a5422141a1231618316,0x8488080e8920c1cb8438,0x3068e10720216263528,0x868110c5898d86805463,0x54786]]
def g219H7 := limbs80 #[#[0x40e00000000000c41249,0x802000000000,0xc000,0xc8600029243061c00000,0xc1b614000b09c18000,0x60a0019860000000000,0x224c3400000000000000,0x130682a41200123e,0x1c040000000006320,0x28c00000000000000,0xe10000000036a3a000,0x1e3c0000000000,0xc16008000000f8c00000,0x62e001,0x8a8aa2190f60c0000000,0xaa480600081fc41a2,0x8a000439627a2c000822,0x17]]
def g219D8 := limbs80 #[#[0xd32fea07f4c3fa41fd10,0x3288cc36007f54ffa85f,0x70658e22242402234f66,0x9228432099638642862c,0x32079428c94451cd025,0x50c996330920594284a9,0x1c65a48a180]]
def g219H8 := limbs80 #[#[0x120400006000183815e1,0x6145a0a05e0000000000,0x4946600103800489f315,0x800d8d034000006ac001,0x100123000000a4c64cc1,0x3844b1902297670074,0xc1000c08c54568000,0x80000000008d687a1b0c,0x380000000000117c10ab,0x22001f1e8cc85fe783d0,0x74bc9e00088e]]
def g219D9 (j : Nat) := if j=0 then 0xa4188201bf else 0
def g219H9 := limbs80 #[#[0x19400cd0000161000012,0x7d3d8130021,0x11800c40000000000000,0x90000091000010c00,0x27380001280000]]
def g219L : Nat → Packing
  | 5 => (5,4,5,0,0,6,0,g219D5)
  | 6 => (33,3,5,0,0,9,0,g219D6)
  | 7 => (26,2,5,0,0,11,0,g219D7)
  | 8 => (7,1,5,0,0,9,0,g219D8)
  | 9 => (1,0,5,0,0,0,0,g219D9)
  | _ => emptyPacking
def g219I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 2 13 2 9 3 2 g219H6
  | 7 => lookupWord 11 113 3 12 6 2 g219H7
  | 8 => lookupWord 11 73 5 11 5 2 g219H8
  | 9 => lookupWord 3 41 2 9 3 2 g219H9
  | _ => fun _ => none
def g219 : Forest := ⟨219,9,fun i => g219Y[i]?.getD (0,0),g219C,g219A,g219L,g219I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P5_0 : block g219 5 0 5=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g219B5 : block g219 5 0 5=true := g219P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P6_0 : block g219 6 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P6_2 : block g219 6 2 31=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g219B6 : block g219 6 0 33=true := (@block_merge g219 6 0 2 31 g219P6_0 g219P6_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P7_0 : block g219 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P7_1 : block g219 7 1 11=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P7_12 : block g219 7 12 14=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g219B7 : block g219 7 0 26=true := (@block_merge g219 7 0 1 25 g219P7_0 (@block_merge g219 7 1 11 14 g219P7_1 g219P7_12))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P8_0 : block g219 8 0 7=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g219B8 : block g219 8 0 7=true := g219P8_0
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
def g222Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0x3ffffffffffffffff,0x451d37930c4801f003ff])),(BitVec.ofNat 152 (word80 [0x581400540128029029,0x40141692044042108421]))),((BitVec.ofNat 152 (word80 [0xfc00fffe0003fff800,0xfa255c2e0c903e007c00])),(BitVec.ofNat 152 (word80 [0x90a602980db01320cc,0xea055c220c80c6318c63]))),((BitVec.ofNat 152 (word80 [0xfffffffc000000,0x39c4d2d3ab80000f8000])),(BitVec.ofNat 152 (word80 [0xe13844e089c11bc170,0x3944d293a982d6b5ad6b]))),((BitVec.ofNat 152 (word80 [0xfffffffffffffe,0x428bca0bd9efc000001f])),(BitVec.ofNat 152 (word80 [0x1c017002e005c0180,0x2894809d9898c6318c6]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffff00000000000000,0x22fa317cb680000fffe0])),(BitVec.ofNat 152 (word80 [0x98013002600200,0xaa214c1205294a5294]))),((BitVec.ofNat 152 (word80 [1,0x9d26ecc07137fff00000])),(BitVec.ofNat 152 (word80 [0x200e001c003800400,0x1522a0402036318c6318]))),(0x0,0x0)]
def g222C : List ColumnInfo := [(4,0,218,0,7)]
def g222A : List (List Nat) := [[]]
def g222D7 (j : Nat) := if j=0 then 0x7f else 0
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
theorem g222G : graphValid g222 (boundsBefore K219) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low222 : Lower true (varsX 222) (graphGoal 222) 8 := lower_forest (g:=g222) (i:=0) (hints:=285304384) (before_sound K219 V219) g222G g222T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K222 := extendKnown K219 8 [(222,[]),(238,[33,84])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V222 : Known true K222 := extend_ok (m:=222) V219 low222 (by decide +kernel)
def g243Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfff83ffffffc1f530a,0x312e3a40000fc003f03f])),(BitVec.ofNat 152 (word80 [0x8508210020840130a,0x1243205145145145145]))),((BitVec.ofNat 152 (word80 [0x3ff83fffe0206a,0xe621f48003f03f000fc0])),(BitVec.ofNat 152 (word80 [0x2610020809002200a,0x6401b0830c30c30c30c3]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffc0003fffffb49c,0x90d84280fc0000fc0fff])),(BitVec.ofNat 152 (word80 [0x108004410420000094,0x90184008208208208208]))),((BitVec.ofNat 152 (word80 [0xffffffffc000008945,0x6856a9bf000000fff000])),(BitVec.ofNat 152 (word80 [0x2300088008c0848840,0x68428892492492492492]))),((BitVec.ofNat 152 (word80 [0x9171,0x19b1dc4000003f000000])),(BitVec.ofNat 152 (word80 [0xbc022f022f01089171,0x19b04c7cf3cf3cf3cf3c]))),((BitVec.ofNat 152 (word80 [0x4e93,0x4f80057fffffc0000000])),(BitVec.ofNat 152 (word80 [0xc00430043002104401,0x2800560820820820820]))),(0x0,0x0)]
def g243C : List ColumnInfo := [(0,64,177,2,8),(64,0,179,0,8),(1,0,242,0,7),(2,64,177,0,7),(16,0,227,0,7),(32,0,211,0,7),(128,0,115,0,7),(33,0,210,0,5),(17,0,226,0,4),(48,0,195,0,4),(129,0,114,0,4),(160,0,83,0,4)]
def g243A : List (List Nat) := [[],[116],[80],[80,116]]
def g243D5 := limbs80 #[#[0x4c930483b2595324c120,0x483725d5324c120ecb65,0x5d5524c120f495354930,0x54120f49534c9504835a,0xe6b6354950482da61532,0x5d953482dae0d5254120,0xc03361cf70595208fb80,0xa0d49d2213c6ca0d141,0x808402000]]
def g243D6 := limbs80 #[#[0x3b4a92a0907c9324c120,0xfd2a49824137dcd6548,0x837cb2a60907d9534c12,0x20bf2ea98241bed95304,0x4837db1aa0907e932541,0x920ddeca99241bb59532,0x2483b6a9aa4907eb7054,0x4920ddec6a9241bb58d5,0x634827ebb2a6905ef735,0x595209faebb1a413fdd5,0x165482efb9aca905fb70,0x359520db8e6b2a41bedc,0xcf654827fb9aca906df7,0x73581529feeca92613f5,0xe4b110027eb9ec0a95df,0xd72ac4fa65187f39194b,0xc822706803cdccd9662f,0xcadeabf59a9d1a813396,0x1710d0927317884e61c4,0x801010a08504402071e0,0x60430220108080141ac0,0x100802016c0f0040c40d,0x38f00f10100180005040,0x19]]
def g243H6 := limbs80 #[#[0x9000041800000006,0x2e6001f4c8000003a90,0x25700109000c7000000,0x210000,0x44000f08000,0x52210008371400000000,0x32800d04c8c]]
def g243D7 := limbs80 #[#[0xb4c920fe54120fe4c120,0xd8d20bf58d20fb54920f,0x8152bfd9520bf59520bf,0x520ff58d20ff54d20bfd,0x52ff58152ff54930ff59,0x360a81f84e09000ffd81,0x799bc679865d14a4b0fc,0x80b35a4188c739071616,0xce2586248c44cd588728,0xc81492241b11f31c8c44,0x810a2225859331d5c76c,0x2c80a4d714a6cc6156cc,0x5050718a2155842481c3,0x485288564c704871a24,0x1a4c7]]
def g243H7 := limbs80 #[#[0xa82c00e290a491401182,0x15541a38600000627e1,0xe13c20000870040,0xfc0,0x6c1c2313380000148fe5,0x2d0600000000165f4938,0x32c8e800001c3c498008,0xb1800800001a428ac36,0x59000000000000d5000,0x1c029016564847a00000,0xe4441a9995c000e28,0x15]]
def g243D8 := limbs80 #[#[0xc79aa407f54bfa61fd20,0x98c2b469338d145aa224,0x11ac8c4]]
def g243H8 := limbs80 #[#[0xa4c11673001cd60e208b,0x8c00000000b1f2040,0x14e000008240052fc881,0x2d0036800000c06a674,0x8000001468cee00000f0,0x34c00b280011]]
def g243D9 (j : Nat) := if j=0 then 0x1654231bf else 0
def g243H9 := limbs80 #[#[0xb0000051008400,0x8200a8ec000000]]
def g243L : Nat → Packing
  | 5 => (11,4,4,0,0,7,0,g243D5)
  | 6 => (30,3,4,0,0,9,0,g243D6)
  | 7 => (15,2,4,0,0,10,0,g243D7)
  | 8 => (3,1,4,0,0,7,0,g243D8)
  | 9 => (1,0,4,0,0,0,0,g243D9)
  | _ => emptyPacking
def g243I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 4 53 1 10 4 2 g243H6
  | 7 => lookupWord 11 79 4 11 5 2 g243H7
  | 8 => lookupWord 6 43 3 10 4 2 g243H8
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
theorem g243G : graphValid g243 (boundsBefore K222) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low243 : Lower true (varsX 243) (graphGoal 243) 10 := lower_forest (g:=g243) (i:=0) (hints:=16777284) (before_sound K222 V222) g243G g243T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K243 := extendKnown K222 10 [(243,[]),(245,[33,84])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V243 : Known true K243 := extend_ok (m:=243) V222 low243 (by decide +kernel)
def g246Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1ffe0ffe0ffff7222,0x914baa40000fc0fc003f])),(BitVec.ofNat 152 (word80 [0x940142004204403202,0x1432a05145145145145]))),((BitVec.ofNat 152 (word80 [0xfe0000ffffffe0394a,0x8626748003f03f000fc0])),(BitVec.ofNat 152 (word80 [0x18058402800082380a,0x840250830c30c30c30c3]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffff0000ffffad94,0xb0d84280fc000003f03f])),(BitVec.ofNat 152 (word80 [0x202600130411000990,0xb018408a28a28a28a28a]))),((BitVec.ofNat 152 (word80 [0xffffffffff0000804d,0x6956a9bf00000003ffc0])),(BitVec.ofNat 152 (word80 [0xc04800240026048044,0x944a914514514514514]))),((BitVec.ofNat 152 (word80 [0x9171,0x18b1dc4000003ffc0000])),(BitVec.ofNat 152 (word80 [0x17008b808b8088171,0x18b08478e38e38e38e38]))),((BitVec.ofNat 152 (word80 [0x4e93,0x4f80057fffffc0000000])),(BitVec.ofNat 152 (word80 [0x18010c010c0104401,0x42800460820820820820]))),(0x0,0x0)]
def g246C : List ColumnInfo := [(2,0,244,0,7),(4,0,242,0,7),(64,0,182,0,7),(128,0,118,0,7),(0,64,176,6,6),(16,0,230,0,6),(32,0,214,0,6),(2,64,176,4,5),(4,64,176,2,5),(18,0,228,0,5),(36,0,210,0,5),(66,0,180,0,5),(80,0,166,0,5),(96,0,150,0,5),(6,0,176,0,4),(6,64,176,0,4),(20,0,226,0,4),(34,0,212,0,4),(70,0,176,0,4),(82,0,164,0,4),(100,0,146,0,4),(130,0,116,0,4),(132,0,114,0,4),(144,0,102,0,4),(160,0,86,0,4),(192,0,54,0,4)]
def g246A : List (List Nat) := [[],[33,84]]
def g246D5 := limbs80 #[#[0x485304427c61f31c8110,0x443d454d514c110fc132,0xe15764c910e696254950,0x4c1208df835d9524421f,0xd697554930483d254d52,0x549504839a58d5254120,0x4838e5516354120d6b73,0xe097654d20e4d6354d52,0x54720c3f75551634823b,0xe4d6354d52c8237e0d76,0x4c9504c30fdd55458f20,0x4c3c65513254130f4952,0x5533254130dcb72cc950,0x4c930e3954d89504c3c6,0xd1f75551324c39359552,0x55132cc393595524cb30,0xcc39354d6254b30d1f75,0xdd9544c950c3f7555162,0x58d50d39545c3325430f,0xd39545c2635434b55372,0xdc5524cb9354d52d8132,0x8ca8f6036555132d4d53,0xdd55458e32e4d6354d52,0xc0c008df835c76054b0f,0x1a4c65d2b94496451b09,0x58aad4a9f4ca4d1a873c,0xe770b6daacf64b0d7ab7,0x3b1788c2e0aff7cbcdda,0xc12083c220840302,0x3040608000000]]
set_option maxRecDepth 16000 in
def g246D6 := limbs80 #[#[0x3b4a92a0904bd75d9110,0xe72a8a8261ce5515048,0xca5fbb2a9984ef725953,0x32c7acaaa065ae551600,0x4cb1eba2ca194bf76550,0x110c7ecaaa265d354d52,0x443f8a8e40887f331c8,0x8110bf2e790221fa54b2,0x30443f890a60885f975c,0x4c110fb26498221fc545,0x530443eca9a60886f962,0x54c110bf2ea98221be59,0x8950443bca92a0885fb7,0x7354110df2c6a8221be5,0xd9132442fdb8264885fb,0xf764c9109faec99221af,0xb58952442fdb82a4884f,0xfd7654910d7ec8a9221b,0x3fdd5624427fb9ac4884,0x7e9524c1209fee4b2a21,0x1f694d30483eca9a6090,0x6f9654c120f72a89824,0x417edd530482fcbaa609,0x905fb7354120df2c6a82,0x2413f5db31482fcb8662,0x6906ed6354920edaa6a9,0x9a413f5d9534836eb1aa,0xa6906dd6394d20bf2e12,0xb1a41bedc1634827ebb4,0xac6906bd5458d209fee2,0x6b2a413fdc5654827fba,0xaa3904fd76cc7209fee],#[0xa4b0e413f5d951c837ab,0xb1aa59076d5354b20dda,0xacaa9e41b758d53c8376,0xeb1ca7904fd7654f20cf,0xfee2b1e413f5da53c836,0x7fbaac7906bd5458f209,0xbf6e2a8261bed85504c2,0x3ed992a0987d93254130,0xdf6c4a8261de549504c,0xc3e699242985fb725413,0x30ebaa6a8a61bbd89214,0x4c27eb96c2985df73545,0x9309faebb0a61b754f61,0x24c3edb8264985fb704c,0xc930f3aa899261f35493,0x324c36fb2a64986dd654,0xcc930bbeea99261775d5,0x7324c36eb2e649879d54,0x554930ebaa6a9261775d,0x4f624c27eb8ec49867d6,0x75d8930d7aa9b1261b75,0x5ca534c2efb92a6984fd,0xf7159530bdee4b2a6177,0xbdc9654c376392ca984f,0xfd71d95309fee4b2a61b,0xf354932cc27eb96ca984,0x6dd654cb30f3aa899661,0x177dd532cc2eebaa6598,0x875d5354b30ddac4a966,0x619f59552cc35eb22a59,0x986dd5358b309faeca96,0xaa13fdd562cc35eaa2c5],#[0x4a84fd73d85509fae5b0,0x92a1cf55132543b6a926,0x64a85f970cc9509feec9,0x992a1cf5533254377b16,0x2c4a867f63549509faed,0x7b12a13f5c7625439eaa,0xa2c6a85ef7258d509fae,0xa931aa17e5c2635439ea,0xbb4c6a857d7598d50e7a,0xae5b1aa13f5c7635427e,0x6a96c0994fd71d81329f,0xbca7b0265b754f604cb7,0x7ebaec0996bd54d8132d,0xcfecaa9265d754d524ca,0xbb7b2aa4995ef7154932,0x2cfecaaa2657b5c6524c,0xcb3fb2aca9973f655513,0x329fae1b2a653fdc1654,0x8cb5eaa2c3196ed52586,0xe32ddac6a9465db54d52,0x38ca7ebb2a71967d6554,0x4d429feeab1c65af5516,0x5390b7aa9ac3215ef725,0x54e42dbac6a9c857bdc9,0x56390a7ebb2a72167d65,0x3d81529fae3b02a53fdd,0xcd6154aee39ac2a94fd7,0x53d85529fae1b0aa577d,0x5ca6354a7eb9ec2a967d,0xd71d8d529fae1b1aa57b,0xfdc56394afdb82c8a94f,0xbd73189549fae7b12a93],#[0x80b0038002deb9ec4aa5,0x3d83402c82501b818012,0xa05685505185004c8450,0x87b07587006886305b85,0x9b89809288d089888082,0x80b68b30ad8a80a089f0,0x8cb0c98c80c68c10bf8b,0xdd8dc0d88d70d38d00cc,0xec8eb0e78e40e28e10,0x8fd0fb8f80f68f30f18f,0xf90e10a9071019000fe,0xe11c91b1199181149111,0x92f12d92c12692312191,0x4594213e93b135934130,0x815495315194e14c9491,0x96716396216095d15b95,0x7d97a17897516f96c168,0xc18a9871859841829811,0x99919799619499319198,0xa79a61a49a119f99e19a,0x81b69b31b19b01ac9ab1,0x9c91c39c21c09bd1bb9b,0xe99e41dc9d91d19d01ce,0x81f69f51f39f01ee9ed1,0xa09205a042009fd1fb9f,0x1da1a218a17211a0e20a,0x22ea2b229a26222a1f2,0xa4123da3a236a35233a3,0x4fa4e24aa49247a46242,0xe25ca5b259a56254a512,0xf890d900c243040663a5,0x3028d284a304543c2150],#[0xa31289292438a62890c9,0x605230d8a2a2434a49a2,0x840300041003c1000810,0x420b09040030f26089b0,0x940420f06420f0904206,0x1043c0c20f030800100,0x42040208100c08300041,0x20800604020c00307080,0x1410606141000000040,0xc10304000141000c10,0x304000040001410,0x3040000c106043c0c200,0x20f04003040000001410,0x484402028c1000003c18,0x4003040010004441010,0x40050600100000,0x30410082050444100141,0x504000003001630406,0xc1000000000040208,0x4000001000c100005040,0xe2420008004003040150,0x460562430000402085,0x14106240854908830,0x5c105040030400000004,0x605c203040810014100,0x4000040c105040030400,0x8104040c100002040030,0x400004100000181000,0xd03080000610400]]
def g246H6 := limbs80 #[#[0x81208800880000070,0xc0000000014800000000,0x30968f001f08005a232,0x1634000000000,0x24ab5c00000000000,0x8f0e002c309ca0200000,0x3400002ba0000029,0x6cb00068c000000,0xc37a774f800000,0x9b800,0x146400000001f840,0x934000000,0x820ca000c1c000e1800,0x4205000000000c1000dc,0x6b41ef260000058bc2fe,0x50a00000620642456,0x900000186000a0600000,0x156400000000000f138]]
set_option maxRecDepth 16000 in
def g246D7 := limbs80 #[#[0xf55150af59330afd9110,0x59432af59032be58032c,0xc110fec8110bd586429f,0x510bf58910fe54110fe4,0x20fe54120fe4c120bf59,0xef55120bf58d20fb549,0xfb54b20bf58720bf5952,0xf59720ef55320bf58f20,0x4c930bfd8530fe54130b,0x4d30bfd8930f7cc930f7,0x130ef55130f794d30f75,0x30bfd9530bf59530ef95,0xf754f30bf58b30f74cb,0xbfd8550bf59730ef5533,0xfd8d50bfd8950df54950,0xd8132bf59432ef55032b,0x5132fb94932fb54932bf,0x532bf59532ef95132ef5,0x32fb54a32bf58632bfd9,0x2bf59632ef55232bf58e,0xbfd8152bf59642bf58e4,0xfd8d52df54d52bfd8552,0xd8954bf58e52bf58652b,0xc910efd8954ef18954bf,0x520ff4c520ff54910ff4,0x20ff54d20ff54520ffcc,0xff54720ffcc720ff94d,0xff48530ff94f20ff54f2,0xf4c930ff58530ff54530,0x54d30ff58930ff54930f,0x4d40ff54b30ff59530ff,0x950ff4c950ff58550ff5],#[0x50ff58d50ff58950ffcc,0x2ffd8132ff58132ff98d,0xff59132ff55132ff5493,0xfd9532ff59532ffd9132,0x54e42ff54d42ff54e32f,0x8d52ff58552ff58152ff,0xff59152ff98d52ff5,0x30d30b809607b059030,0x61e41c91991691471171,0x2fc2d32aa26c24a22820,0xd3eb3c93a037034031e,0xf51f4da4b849646d42f4,0x6226005d05ae58c56a54,0x4872670b6e26a467b64b,0xe85382a7f37bc7a17637,0x9799499208f78c789086,0x91a68a46a1d9ed9c49a9,0x9b25b0aaf6ae2ac7ab3a,0xbd4bb2b97b83b68b54b3,0xa6c7dc69c55c41c1fbef,0x3d41d26d0bcf7cd5cc1c,0xdf7ddcdc1da6d92d7ed6,0xa6e8be69e55e41e26e0b,0x8e08495006ee9edcec8e,0x32b24789271c01a20593,0x430310186071048a1818,0x2c1e14d858c4050e3091,0x552a31e212230928a1e3,0x60a4878c40303242478c,0xa8746244c24498658a8,0x8f10883024c42e911891,0xb950c11182022488d251],#[0xa911c00a28c0c0c80f14,0xc68d1518f10181803042,0x8b0910e8c60c10101805,0x10c8498848283223c52a,0x6401c64c888286892221,0x148c88a608e20c910c04,0x313464848d1518f11262,0x23182254202021602326,0x8a106891418508080a32,0x8c3ca112401460406344,0x51e5440a1000d146068a,0x80892a3172a901891430,0x952480a101012a286080,0x4123051714ca28300223,0x62430a18ba3101812618,0x8688c848302345464184,0x3982e111820200746509,0x42461014305080808046,0x470630509103092e1831,0x80892e3198c11141472,0x80e5c51a0c4050e28406,0x8b8c18201c480b8c1810,0xc25c50a60b8619080080,0x48a18262130c80c10100,0xe9450c2039910202030c,0xc21c126101cc88984430,0x960c309085090a1171c1,0xc1424624306604843c4,0x102a30c1853010f0a583,0x3a242316223c34300890,0x45c884182c0222111c28,0xcc15222518a44c044448],#[0x162a887882c205083170,0x885ca890c2950c1862a1,0x8889083a22a19812548,0x3034410c86182970c2a0,0x2a30cc17461844410d08,0x28214c08106048cc0418,0x5c22e5882110b95121c,0x1908806085c13]]
def g246H7 := limbs80 #[#[0xc08780a418b001a00004,0x7420a5d38c823e5d3010,0x159e060ea8d040760f02,0x78106774851401a0d020,0x801e02000361c900c004,0x6659150c0a70f0032682,0x86fe88ea0000000184a,0xf82975a8000000234ac4,0xe6137c188c2ede688387,0x1c3030aa492354eb7fb,0x5a000122ec70ad800000,0x81325c621012a4bc0192,0xc9ae436ec7e93924a040,0x49c18abac808fe12,0x6d33f30e120c57662326,0xf8e475870000000001b5,0x2785735600d964624f1a,0xde7c0e000b5e14cea6fb,0x80f302daa74c0652b204,0x6a22ccd4ba820bd8b091,0x9e0be51b1136f585a731,0x73a66cc7481d3a39abd1,0x4ce3b7b6e1f8d0462603,0x3791de6cac16227080a9,0x6c9a6100064d8446e336,0xa070000000a58639eae0,0x38e38693b34887557b1d,0xb78da873cf76b0000000,0x4f0700a8000000274322,0xa5c4a8000d7e091046e9,0x4000000d4bf0d58014,0xe3990c54e5b3d603eabb],#[0x8003c15f329ce0868981,0x42e00012db09636e744,0x644e3850f13000621000,0xce3d0000002583e1482,0x4a4e980008b9e21c85c6,0x5ec8e3024a88ca307df,0xd3fa21d0d6ec500008c9,0x251567c00008eac11637,0x824d90b5ced1863afe14,0x29692e80f811e66,0x56f58d193b3400060f80,0x67dd25eafc2cb84f48ac,0x89a53c921aa296ad53c4,0x409cd66ca46188001c3c,0x6bbb4ea44b058000000,0x5952c78a1d000566c00,0xd17605c5fe9d14f27a00,0x989047444000ad5d48be,0x62c3b2c4001b5cb6a555,0x64fb6b32cf4245bb8000,0x306ca2ccbe000,0x6742b4f2cea000355000,0x8415984f55eb46bd0640,0x20e48365c55a]]
def g246D8 := limbs80 #[#[0xf20fe907f4437ca9bd54,0x65fd50fea07fcc3fa61f,0xbfc85fd42ff197f4cbf8,0x780c001fd54ff297f54,0x318ae24c841bc5410833,0x419e1cd523438f6390d5,0x90451319e304a261a428,0x40d1c201828d1c2988,0x44c601468d0a24c710e5,0xa8114248e1906c642620,0x46a2620408019251838c,0xe39b19060e2c65126082,0x308bc21a630268518a40,0x1a60419038c34260648a]]
def g246H8 := limbs80 #[#[0x25010033021002360027,0xd10003001994222d0b00,0x5e79ccf110000002a,0xf46000000545,0xdaf0000,0x0,0xced61000000000000000,0x786b000a08e052623e01,0x56e000dc30000ae08,0x90d23352000000000000,0x93300000030c0006d0c,0x83000141f39000b2b00,0xa18000,0x0,0x3600000000000000,0x434000ba000011e000,0x542e755da450e9e9c880,0x966c5084472,0x26000a01000000000000,0xe4200073e2,0xa3800000000051fd4,0x43127000816000000000,0x20463b6b700071b73af,0x0,0xbc800024a000000000,0x549d000659d8fcc7cc50,0xf1000042ab5d0000007a,0x304e19dae519cdc9a73d,0x4c0016c000000a48549e,0xa25e8000000c5c0c256,0x231000000000000,0x8f17000000000ddf0000],#[0xb8a0000000002ca000a5,0x0,0x5d50000000,0x0,0x1300043222d000000000,0xf00000055b000000b4f2,0x50770a00060300000073,0x28409d47000000000,0xb120000000,0xd5a0007d885400,0x260000000,0x206d0d0,0xf4e000000c9c03546500,0x95d8200061a00000026d,0x50f000f21a,0xe19168000000000c1500,0x8d200000024d,0x42200074cac90,0x0,0xd5e000000000,0x55f0000000,0x56b6a000f1d00000000,0x3769ef53000000000114,0x72c21cec19295db000a,0x557000000c8900000,0xb000067824000b2f000,0x663000000f990000008,0x10200023c000d2000000,0xa9f000a4b000,0x3690000]]
def g246D9 (j : Nat) := if j=0 then 0x1882013f else 0
def g246H9 := limbs80 #[#[0x580067a5a12800018621,0x80dc400000000005d9c,0x1d09611ce86000d78018,0x68a002a1923c6e,0x5fcc0000144800000000,0x751c00000000017458f3,0x26f95b]]
def g246L : Nat → Packing
  | 5 => (38,4,5,0,0,9,0,g246D5)
  | 6 => (198,3,5,0,0,12,0,g246D6)
  | 7 => (111,2,5,0,0,12,0,g246D7)
  | 8 => (17,1,5,0,0,10,0,g246D8)
  | 9 => (1,0,5,0,0,0,0,g246D9)
  | _ => emptyPacking
def g246I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 12 127 3 11 6 1 g246H6
  | 7 => lookupWord 65 307 7 13 8 1 g246H7
  | 8 => lookupWord 39 397 4 12 7 1 g246H8
  | 9 => lookupWord 7 47 5 10 5 1 g246H9
  | _ => fun _ => none
def g246 : Forest := ⟨246,9,fun i => g246Y[i]?.getD (0,0),g246C,g246A,g246L,g246I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246P5_0 : block g246 5 0 38=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g246B5 : block g246 5 0 38=true := g246P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246P6_0 : block g246 6 0 12=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246P6_12 : block g246 6 12 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246P6_108 : block g246 6 108 90=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g246B6 : block g246 6 0 198=true := (@block_merge g246 6 0 12 186 g246P6_0 (@block_merge g246 6 12 96 90 g246P6_12 g246P6_108))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246P7_0 : block g246 7 0 7=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246P7_7 : block g246 7 7 61=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246P7_68 : block g246 7 68 43=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g246B7 : block g246 7 0 111=true := (@block_merge g246 7 0 7 104 g246P7_0 (@block_merge g246 7 7 61 43 g246P7_7 g246P7_68))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246P8_0 : block g246 8 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246P8_2 : block g246 8 2 15=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g246B8 : block g246 8 0 17=true := (@block_merge g246 8 0 2 15 g246P8_0 g246P8_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246P9_0 : block g246 9 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g246B9 : block g246 9 0 1=true := g246P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246T : checkedTables g246 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g246 0 0 0 = true)
  · exact (rfl : block g246 1 0 0 = true)
  · exact (rfl : block g246 2 0 0 = true)
  · exact (rfl : block g246 3 0 0 = true)
  · exact (rfl : block g246 4 0 0 = true)
  · exact g246B5
  · exact g246B6
  · exact g246B7
  · exact g246B8
  · exact g246B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246G : graphValid g246 (boundsBefore K243) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low246 : Lower true (varsX 246) (graphGoal 246) 10 := lower_forest (g:=g246) (i:=0) (hints:=287376704) (before_sound K243 V243) g246G g246T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K246 := extendKnown K243 10 [(246,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V246 : Known true K246 := extend_ok (m:=246) V243 low246 (by decide +kernel)
def g249Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfc1ffffffffff7302e,0x4b8e80003f8001fffff])),(BitVec.ofNat 152 (word80 [0x84082002080023004,0x904808102040810204]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1fff07ffc1f04f21,0xcd27ca000007f000007f])),(BitVec.ofNat 152 (word80 [0x508814120904004821,0xcd2682468d1a3468d1a3]))),((BitVec.ofNat 152 (word80 [0xffe00007fffe0b48e8,0x93c11601fc000fe03f80])),(BitVec.ofNat 152 (word80 [0x6001182042002108a8,0x81411412244891224489]))),((BitVec.ofNat 152 (word80 [0xfffffff800000894d0,0x691ab3fe00000fffc000])),(BitVec.ofNat 152 (word80 [0x800220008c08488440,0x600aa224489122448912]))),((BitVec.ofNat 152 (word80 [0x91717,0xa28774000007f0000000])),(BitVec.ofNat 152 (word80 [0x113c044f010891716,0x228174b972e5cb972e5c]))),((BitVec.ofNat 152 (word80 [0x4e917,0x7e4005fffff800000000])),(BitVec.ofNat 152 (word80 [0x21c00870021044113,0x1e0001c183060c183060]))),(0x0,0x0)]
def g249C : List ColumnInfo := [(0,64,177,8,8),(64,0,185,0,8),(8,64,177,0,7),(16,0,233,0,7),(32,0,217,0,7),(128,0,121,0,7),(1,0,248,0,6),(48,0,201,0,4),(144,0,105,0,4),(160,0,89,0,4)]
def g249A : List (List Nat) := [[],[117],[84],[84,116],[116,84],[116]]
def g249D4 (j : Nat) := if j=0 then 0x194975e0d528c120 else 0
def g249D5 := limbs80 #[#[0x4c930483b2595324c120,0x482f2615324c120ecb65,0x54d524c120bcb854c930,0x8c120bcb8354a30483d2,0xe4d6554d324835a5d552,0x1d5634823be097654d20,0x4cb1b5977254e20c6f72,0x94170d9532e4d5354b60,0x8d0192c4c80d141c031e,0x8080000000002036294c]]
def g249H5 (j : Nat) := if j=0 then 0xe600 else 0
def g249D6 := limbs80 #[#[0xa3fbaac6907c9324c120,0xf9a6498241d354d524c,0x83f4a9260905ef724c12,0x20df2ca98241fadc9304,0x483f4a9460906fb654c1,0x120df6cb18241be59630,0x2483e6a9a64905f9758c,0xc920ddaca99241f3d8d3,0x32482f6baa64906ef654,0x54d209faeca9a417bdd5,0x5634836fb1ac6904fe76,0x558d20cf8eab1a415fdd,0xd7634827fbaac69067f7,0x6354e20bdee4a9c413f5,0xdd5638827ebb2a7106dd,0xf7558132bdee4b02653f,0xf5da604caf6b94c09957,0xfd75d8132ddaa5b02653,0x3f5c3654ca7fb82ca994,0x5ca14a239025f1b08801,0x5610fb73b69a8ce60aed,0x3d86a94ea44ee5d28914,0x7dd6b74193c6e1ef574b,0xf008314e48c4f3f6ba9c,0xf8f00c205e3c1243178,0x2020540420218100002,0x30350108084061090400,0xa080141000000d404000,0x41838c1060800050406,0x700400a085]]
def g249H6 := limbs80 #[#[0x54320800000228003345,0x140e06000c8000000,0x5080000000000000,0x3a7000628000000000,0x550517e5c0078c000000,0x3098a40060022400000,0xd4b9180000,0x0,0x24298700000000000f76,0x0,0x9b0010240000068a0000,0x206,0x615,0x254403a9]]
def g249D7 := limbs80 #[#[0xb4c920fe8c120fe4c120,0x58e20bfd8d20bf58d20f,0x9532fb54932bfd8132bf,0xd20ff4c120bfd9532bf5,0x20ffd8d20ff58d20ff54,0x2ff98132ff58132ff54e,0xe8961b04207800ff5953,0x81c86a986589263d8d82,0x146c948c497a40889f87,0x860f1187c941878f2506,0x21315358f21711d48c5c,0xc705641c5c721c41541b,0x49207c465648f22481c3,0x9131c06523146c55c871,0x2461835031d55031940c,0x501c41958c71140e1806,0x92078d51634]]
def g249H7 := limbs80 #[#[0x4046c2de4d7191277080,0x10e1a1203728a91a0220,0x9c0f621000480800d088,0x7d24287c000000000103,0x44424423e13493780724,0x11643912a8c7f09106aa,0x91720a6cf511005f91b6,0x45004fb0764108197053,0xc881c4b49230af817d13,0x862430b1c6fc0945cd07,0x7fa8de18000c43312e82,0x1601905f802819e0962,0x3a5400188530d5a840,0x61a34fe0800014260000,0x12603c911b0c0003]]
def g249D8 := limbs80 #[#[0x86909007f4cbfc41fd20,0x1c870d683348689ab41c,0x1131ea4]]
def g249H8 := limbs80 #[#[0x82270,0xe0000007110000000,0xd2400000000000080792,0xd25409c00e2d,0xf808000d42000d238050,0xc02000a2250b000e2ca0,0x121,0x1000b8b0000,0x10d000b03000c0c00,0xa06004,0xa1470000000000000000,0x38138e00064100ad2,0xe10000000]]
def g249D9 (j : Nat) := if j=0 then 0x1543217f else 0
def g249H9 := limbs80 #[#[0xc20772423c1000016000,0x1c0b40034d]]
def g249L : Nat → Packing
  | 4 => (1,5,4,0,0,0,0,g249D4)
  | 5 => (13,4,4,0,0,7,0,g249D5)
  | 6 => (39,3,4,0,0,9,0,g249D6)
  | 7 => (18,2,4,0,0,10,0,g249D7)
  | 8 => (3,1,4,0,0,7,0,g249D8)
  | 9 => (1,0,4,0,0,0,0,g249D9)
  | _ => emptyPacking
def g249I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 3 0 6 0 2 g249H5
  | 6 => lookupWord 7 113 2 11 4 3 g249H6
  | 7 => lookupWord 18 83 6 13 6 3 g249H7
  | 8 => lookupWord 8 83 3 12 5 3 g249H8
  | 9 => lookupWord 2 17 0 9 2 3 g249H9
  | _ => fun _ => none
def g249 : Forest := ⟨249,9,fun i => g249Y[i]?.getD (0,0),g249C,g249A,g249L,g249I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g249P4_0 : block g249 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g249B4 : block g249 4 0 1=true := g249P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g249P5_0 : block g249 5 0 13=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g249B5 : block g249 5 0 13=true := g249P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g249P6_0 : block g249 6 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g249P6_3 : block g249 6 3 36=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g249B6 : block g249 6 0 39=true := (@block_merge g249 6 0 3 36 g249P6_0 g249P6_3)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g249P7_0 : block g249 7 0 10=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g249P7_10 : block g249 7 10 8=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g249B7 : block g249 7 0 18=true := (@block_merge g249 7 0 10 8 g249P7_0 g249P7_10)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g249P8_0 : block g249 8 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g249B8 : block g249 8 0 3=true := g249P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g249P9_0 : block g249 9 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g249B9 : block g249 9 0 1=true := g249P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g249T : checkedTables g249 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g249 0 0 0 = true)
  · exact (rfl : block g249 1 0 0 = true)
  · exact (rfl : block g249 2 0 0 = true)
  · exact (rfl : block g249 3 0 0 = true)
  · exact g249B4
  · exact g249B5
  · exact g249B6
  · exact g249B7
  · exact g249B8
  · exact g249B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g249G : graphValid g249 (boundsBefore K246) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low249 : Lower true (varsX 249) (graphGoal 249) 10 := lower_forest (g:=g249) (i:=0) (hints:=50331651) (before_sound K246 V246) g249G g249T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K249 := extendKnown K246 10 [(249,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V249 : Known true K249 := extend_ok (m:=249) V246 low249 (by decide +kernel)
def g250Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0xf8001fffc03fffff63,0x44e29b013c003f03f03f])),(BitVec.ofNat 152 (word80 [0x501940428680a21422,0x44409101382082082082]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffe000003fff003c,0x78de8447880000fc0000])),(BitVec.ofNat 152 (word80 [0x6211886b0b10c4263c,0x48d684078934d34d34d3]))),((BitVec.ofNat 152 (word80 [0xffffffffffffffffbc,0x8889e994640fc0000fff])),(BitVec.ofNat 152 (word80 [0x8042010c0002080014,0x894814445145145145]))),((BitVec.ofNat 152 (word80 [0xffffffffffc0000081,0x4f4585ecd3f000000fc0])),(BitVec.ofNat 152 (word80 [0x9c02700c04f03881,0x4e4485c810a28a28a28a]))),((BitVec.ofNat 152 (word80 [0x91,0x75383e5b400000fff000])),(BitVec.ofNat 152 (word80 [0x4e013801027004081,0x31282a5842cb2cb2cb2c]))),((BitVec.ofNat 152 (word80 [0x4e,0x937660389bffff000000])),(BitVec.ofNat 152 (word80 [0x7001c002038008048,0x91322020830c30c30c30]))),(0x0,0x0)]
def g250C : List ColumnInfo := [(8,0,242,0,7)]
def g250A : List (List Nat) := [[],[116]]
def g250D7 (j : Nat) := if j=0 then 0x7f else 0
def g250L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g250D7)
  | _ => emptyPacking
def g250I (_ _ : Nat) : Option (Nat × Nat) := none
def g250 : Forest := ⟨250,7,fun i => g250Y[i]?.getD (0,0),g250C,g250A,g250L,g250I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g250P7_0 : block g250 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g250B7 : block g250 7 0 1=true := g250P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g250T : checkedTables g250 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g250 0 0 0 = true)
  · exact (rfl : block g250 1 0 0 = true)
  · exact (rfl : block g250 2 0 0 = true)
  · exact (rfl : block g250 3 0 0 = true)
  · exact (rfl : block g250 4 0 0 = true)
  · exact (rfl : block g250 5 0 0 = true)
  · exact (rfl : block g250 6 0 0 = true)
  · exact g250B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g250G : graphValid g250 (boundsBefore K249) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low250 : Lower true (varsX 250) (graphGoal 250) 8 := lower_forest (g:=g250) (i:=0) (hints:=289497152) (before_sound K249 V249) g250G g250T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K250 := extendKnown K249 8 [(250,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V250 : Known true K250 := extend_ok (m:=250) V249 low250 (by decide +kernel)
def g127Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfe7472aee051d0c438,0x7420800000000fe03fff])),(BitVec.ofNat 152 (word80 [0x2824322e405040c010,0x30209122448912244891]))),((BitVec.ofNat 152 (word80 [0x12753742b03278696,0x98a8001fc00001fc000])),(BitVec.ofNat 152 (word80 [0xcc2353742901278496,0x1808b162c58b162c58b]))),((BitVec.ofNat 152 (word80 [0xea196fdd5a071560,0x21900fe0007f0000000])),(BitVec.ofNat 152 (word80 [0x706a182fcd4a070460,0x218070e1c3870e1c387]))),((BitVec.ofNat 152 (word80 [0xfe4b8cf8af25604d19,0x4dc7f0000000000007f])),(BitVec.ofNat 152 (word80 [0x804b8cd0af21200508,0x4dc0e1c3870e1c3870e]))),((BitVec.ofNat 152 (word80 [0x10b6918ec2092866,0xe8db000003f8001fff80])),(BitVec.ofNat 152 (word80 [0x1004818682002860,0x485b2448912244891224]))),((BitVec.ofNat 152 (word80 [0x22c951708cbc330a,0x9174800003ffffe00000])),(BitVec.ofNat 152 (word80 [0xc1503004b8130a,0x81044891224489122448]))),((BitVec.ofNat 152 (word80 [0x19d24061534aaeac1,0x3277ffffc0000000000])),(BitVec.ofNat 152 (word80 [0x19420001014886a01,0x2370e1c3870e1c3870]))),(0x0,0x0),(0x0,0x0)]
def g127C : List ColumnInfo := [(2,0,125,0,9),(4,0,123,0,9),(8,0,119,0,9),(1,0,126,0,8),(16,0,111,0,8),(32,0,95,0,8),(64,0,63,0,8),(0,64,49,14,7),(8,64,49,6,6),(17,0,110,0,5),(33,0,94,0,5),(48,0,79,0,5),(65,8,54,0,4),(80,2,45,0,4),(96,4,27,0,4)]
def g127A : List (List Nat) := [[],[33,84],[64,33,49,80],[64,49],[80,50],[80,49,33,64]]
def g127D7 := limbs80 #[#[0xbef8259540f395454140,0xbf7815d940d7f7559540,0x35794d98009fd85dd160,0x1821a884005e5c782486,0x3]]
def g127D8 := limbs80 #[#[0xd75503fca828177dcd60,0x2a817fdd160bfeeaa05f,0xffaeca07fd75503feb,0x20696421d4c64b18054,0x2890f2c70564235d23c7,0xb0c491cb2891c6cb1c08,0x11ce1051f1c0c147195c,0x1e34905872ca2635458d,0x34c]]
def g127H8 := limbs80 #[#[0x7c400c4000000000,0x284000000142,0x7b00000000010000,0x618]]
def g127D9 := limbs80 #[#[0xe328249cc0ff583fd40,0x6ad071848e41ed52]]
def g127H9 := limbs80 #[#[0x2c3661ab8c0140000005,0x1220000000000c2100,0x614016700000000062]]
def g127D10 (j : Nat) := if j=0 then 0xca864203ff else 0
def g127H10 := limbs80 #[#[0xe1f9900000320000,0x3584000000]]
def g127L : Nat → Packing
  | 7 => (5,3,4,0,0,7,0,g127D7)
  | 8 => (8,2,4,0,0,9,0,g127D8)
  | 9 => (2,1,4,0,0,6,0,g127D9)
  | 10 => (1,0,4,0,0,0,0,g127D10)
  | _ => emptyPacking
def g127I : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 1 29 0 9 3 2 g127H8
  | 9 => lookupWord 2 29 3 9 3 2 g127H9
  | 10 => lookupWord 1 17 0 8 1 3 g127H10
  | _ => fun _ => none
def g127 : Forest := ⟨127,10,fun i => g127Y[i]?.getD (0,0),g127C,g127A,g127L,g127I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_0 : block g127 7 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_1 : block g127 7 1 4=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B7 : block g127 7 0 5=true := (@block_merge g127 7 0 1 4 g127P7_0 g127P7_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_0 : block g127 8 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_1 : block g127 8 1 4=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_5 : block g127 8 5 3=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B8 : block g127 8 0 8=true := (@block_merge g127 8 0 1 7 g127P8_0 (@block_merge g127 8 1 4 3 g127P8_1 g127P8_5))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P9_0 : block g127 9 0 2=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B9 : block g127 9 0 2=true := g127P9_0
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
theorem g127G : graphValid g127 (boundsBefore K250) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low127 : Lower true (varsX 127) (graphGoal 127) 11 := lower_forest (g:=g127) (i:=0) (hints:=16778563) (before_sound K250 V250) g127G g127T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K127 := extendKnown K250 11 [(127,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V127 : Known true K127 := extend_ok (m:=127) V250 low127 (by decide +kernel)
def g191Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfffffd817c545c20ed,0x432241000007c00f83ff])),(BitVec.ofNat 152 (word80 [0x4800a0805c1048206c,0x1020104210842108421]))),((BitVec.ofNat 152 (word80 [0xfc00009946938753bc,0x3e48150000f800007c00])),(BitVec.ofNat 152 (word80 [0x9083308946138703ac,0x3e48112d6b5ad6b5ad6b]))),((BitVec.ofNat 152 (word80 [0x3ac47b0792510,0xaaaa3a001f0001f00000])),(BitVec.ofNat 152 (word80 [0xe015c38c45b0792510,0x2aa2181ce739ce739ce7]))),((BitVec.ofNat 152 (word80 [0xfffff92e274bd758f0,0x4291788000000000001f])),(BitVec.ofNat 152 (word80 [0x126012e234b975890,0x429178fbdef7bdef7bde]))),((BitVec.ofNat 152 (word80 [0x42f1aeb16816,0xc650c03e0003e007fe0])),(BitVec.ofNat 152 (word80 [0x380000a1a4304810,0x250c10842108421084]))),((BitVec.ofNat 152 (word80 [0x8b0240ae8e0b,0x21dcaafc00003fff8000])),(BitVec.ofNat 152 (word80 [0x1c000030240860203,0x48a2a1084210842108]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x6748939029300,0xd01391ffffffc0000000])),(BitVec.ofNat 152 (word80 [0x20004700008009000,0xc0100042108421084210]))),(0x0,0x0)]
def g191C : List ColumnInfo := [(2,0,189,0,9),(4,0,187,0,9),(8,0,183,0,9),(0,8,182,1,8),(10,0,181,0,8),(16,0,175,0,8),(32,0,159,0,8),(128,0,63,0,8),(1,0,182,0,7),(1,8,182,0,7),(18,0,173,0,7),(36,0,155,0,7),(0,2,45,144,6),(0,4,27,160,6),(2,8,180,1,6),(4,8,178,1,6),(16,8,166,1,6),(20,0,171,0,6),(24,0,167,0,6),(32,8,150,1,6),(34,0,157,0,6),(40,0,151,0,6),(130,0,61,0,6),(132,0,59,0,6),(136,0,55,0,6),(3,0,180,0,5),(3,8,180,0,5),(16,2,45,128,5),(17,0,166,0,5),(17,8,166,0,5),(32,4,27,128,5),(33,0,150,0,5),(33,8,150,0,5),(48,0,143,0,5),(128,2,45,16,5),(128,4,27,32,5),(128,8,54,1,5),(19,8,164,0,4),(50,0,141,0,4),(52,0,139,0,4),(129,8,54,0,4),(144,0,45,0,4),(144,2,45,0,4),(160,0,27,0,4),(160,4,27,0,4)]
def g191A : List (List Nat) := [[],[33,84]]
def g191D4 := limbs80 #[#[0xa3b01699765514254630,0x2547303d332cc9aa8a12,0x6305700b068d965514,0x1e83f0010]]
def g191D5 := limbs80 #[#[0x40443a31865955450110,0x5142581109e869392595,0x86995450960443e21655,0x8c3c6175e496558110ba,0x4254630f415d95450951,0x9954509518c2f05a6551,0x3d05a75514254630bc1e,0x54630f8159564509518c,0x64551518c3c857659142,0x15a75915454630f055d9,0x630d4565974551518c2d,0x551518c3517965d15454,0x655d16454630d1565976,0xd1565d65591518c3c15,0x5518c21d5a7e61645463,0xe496554630f115db9259,0x155db94595518c2d45a7,0x48c2c57a45d96554630d,0x56455230e0761d655915,0x69f91619548c341d9759,0xc3155955d78159230875,0x1592308756a575e05648,0x954545605021d7a565f8,0xe25a65514254560b8c69,0xc151b496995450b70546,0x458d42547c256559142d,0x59664d5450951dc1aa55,0x51bc1e99935514254770,0xd54547705a365954509,0x66198355151d85e59646,0xad428193619545472579,0x64546b17a464d8655151],#[0xf815d954b85e9193595,0x5e55855cf715929d0a06,0x5931579561583dc564c5,0x300c00a742819361771,0x2691c823b1a8bc522309,0x833e9dce26b3297cb253,0x72b356a9d429b4aa3d12,0xf26d1a8a3e1e4ec73329,0x2f976b85aac95ea14,0xa810,0x0,0x800000580a820580800,0x2000e83e00201a0b80,0xf83e]]
def g191H5 (j : Nat) := if j=0 then 0x940126 else 0
set_option maxRecDepth 16000 in
def g191D6 := limbs80 #[#[0xa12c08874c5d55450110,0x21c717559560443d42c8,0x514254630e92baaa8a12,0x18c3a2ae8aa2a3187c15,0xacbf02b2461c55765955,0xa84a8f4955142dc1518e,0xf059355142547e0aa8b1,0x5450951b92cb2a8a12a3,0x43c4acab2284a8dc9e59,0x32a8a0221f3165551404,0x885ec6595450110dd8c,0x16559140442f672caa28,0x50110bf1c92caa0221eb,0xf42a8a12c0886bc61965,0xa8b0221ee16550960443,0x879c5955458110f58b22,0x5e1160442de32caa2c08,0x110f71c92cab0221af16,0x724c2ac0885bce516558,0xa1221f256555142442fc,0xe9e595450910bd2cb2a8,0x9542443d4acab2284885,0xf1ab2ac8aa2213e7985,0xbc3ac8884f9e49865511,0xa21d6575e09654423eb2,0x59142546309f2ca704b2,0x518c3b8aeca12a3187e1,0xaabb2a8a8c61f1564551,0xa2a3185d56595454630e,0x1d5597551518c2eaf2ca,0x56454630ecaba2c8a8c6,0x8c39aaecb22a31879559],#[0xcc2c8a8c615d59759151,0xa31875559574546309eb,0x5794595518c3e8f24b2a,0x654630eaacbacaa8c617,0x2f8f24c32a318575e517,0xac8aa461e1d65591548c,0x187275d96455230e8eba,0x97591548c333b0eb22a9,0x5230ccec32e8aa46159d,0xbb0cbb2a918667e19745,0xcaa4611dd985d9548c31,0x47765f86552309ebc8b0,0xe05648c23bf2cc3aa918,0x30e6abb702b2461d9574,0x2fc0ac91867561f81592,0x24619d575e05648c2bab,0x565f81592309eacaf02b,0x1648c393acaba2c91867,0xc6ec3acab246199f855d,0xc2ac9186375db8559230,0x614df955d9648c23bb2f,0x558759230cebc8b0eb24,0x68c2baf22c22ed18477e,0xcbb2a8a82811dd95e117,0x2a0a05ce6595454140e9,0xe396559150502e772caa,0x5158140d5cc32c8a8281,0x3d62c8a8ac0a07cc551,0x2aa8b0281e7165545605,0xa05ae6595458140f1cb,0x97559160503d6722b22c,0x58140d5dc2ac8b0281cb],#[0xa6aecaa2a2a05aee5564,0xa8a8a817359655151503,0x78d5956454540b9bcb2,0x6595545038eaecb2aa2a,0x540e1ebaacab2281c3d7,0xb29c12caa04fa6438259,0xbb2811ed97e096550275,0xc955142545608facaf02,0x5151583d4ac8a12a2b07,0xb3acb2a8a8ac1e35645,0x4b2aa2b071d597745456,0x2a36779459551583ccf2,0x59542dc151ed2b2285b8,0x70547a6ac8aa6e0a8f59,0x3ab2ac9b82a357596553,0x2ee0a8f59e4965dc151e,0x3f259055142546aef28b,0x96550d51f92cb2a8a12a,0x5476ad30b2a86a8fd1e4,0xb2306aa2a3b569855163,0xa8a8ed56198355151f8a,0x679261954546eaf2cc1a,0x655151db3c930caa2a37,0x7ccf24b2ac8a8ed564d8,0x70eb22a3e55935956454,0xa8dd964382595518fac8,0x94e09655476cb09c12ca,0x9551daac2306b2aa3765,0xcb21c12eca8dd5e51835,0x4b2a879ce87e096550e7,0x70f59564dc154ce74bf0,0x59173553c3acab22e6aa],#[0x54aebc8aecb9aa9a9f86,0xcbc02c8aa637e19765cd,0x22a9e3565e056455347a,0x7e558359154f0eb2b06b,0x5765533cf05c0aecaa5c,0x8fac8702bb2a99d583e0,0xc1aecaa576241835d954,0xc99d5855cf71592b3f28,0x4975dc564aebcaae7b8a,0x15923ef2ac06e2b2579e,0xbcab07b8ac99d58560f7,0xee2b2579e4985dc564ae,0x9e792617715923ef20c2,0x655cd64ceac9b0bb8ac9,0x2b9f24baae6b2697e15,0x83102a82681d81200900,0x7a06c05b850049840837,0xd89989588f0888848830,0x8ba8b40b28ae8a80a189,0xde0da0d10cd0c90c28be,0x28f10ef8ee0ec8e60e48,0xfe0fc8f88f70f58f40f,0xd90c10a909107903902,0xa91911791611491090f1,0x12392212091f11d91c11,0x3092c92b129928126925,0xb1399381369351339321,0x94414294113f93e13c93,0x6c96616215b952949945,0x298e98a98417d9799731,0x9b99b31ac9a619f99919,0xd59ca1c89c71c59c19bd],#[0x41f29ec1e81e41e01dc1,0xa022009ff1fb1f99f59f,0x2fa2922522121d21ba08,0x5a5424b244a3e237a33a,0xa72a7126aa61a5da5725,0x87285a84280279a78276,0xa9f29b299a95a8f288a,0x2b3ab22b0aacaa8aa72a,0xc32bf2bdabc2b82b6ab5,0x13c20942a0fc28742a0e,0x1f0b890a83f0709f082a,0xf043f058808906202e20,0xc7b242f0826d24362345,0xb3c20a86d0780085c912,0x9fc20a8261421d07800,0xc20a8103c20b02a0c2c,0x81c2410a810a8c3082a3,0xa810a9c3082ac2420a,0xa30c2c2410a810a8c308,0x42a264410c510709042,0x118450800a851082a,0x130401001000000000,0x4c10000000001501,0x0,0x3810,0x30b02a30c30a81000000,0x82c042c0a820b02a30c,0x10b30909c30b020b309,0x101c181709082c30c20b,0xa820a814082c30c20b0,0x814082c0a820b02a082c,0x100000624101c101810a],#[0x2a042c0a820b02ae0b89,0xb02a082b042a042a04,0x9c90800014040050100,0x781b70d4160021f0877,0x70580081504130413040,0x780082be00207810541,0x80002c056140c2b8502f,0x20b1c160030ac10ad800,0x15048200003c10015f04,0x1209864142000001204,0x3c1f0020004040048106,0xc2040000000010101010,0x1804003]]
def g191H6 := limbs80 #[#[0x19100060c090802c8044,0x25a3580b00022e00,0x94000000000000000000,0x886a1d4a000002,0xe00387ae78a800000000,0x3465980013094ac07db,0x6b108c0008a0000,0x22a6c000004cc000,0x6a0cc800000003a2,0xc000000,0x29ad12000150000,0x800000a3e000005d5000,0x1ba,0x149c00000116cb00,0x60400000000000000000,0x880c0002b3c00000058d,0x93c4000c0b00653000d3,0x44f0008134f41d0010,0xca9587f2ac9a69a24000,0x30700000000169,0x0,0x10000000000000000]]
set_option maxRecDepth 16000 in
def g191D7 := limbs80 #[#[0xfb15450110f255450951,0xdf17550110fb16450110,0xfe14258110bf18650110,0xbf38458110ef16458110,0xdf17558110ef16558110,0xfa55450910df37558110,0xde57550910fa56450910,0x9f78759110d757555110,0xd757559510be78259510,0xf555454630fc54254630,0xf556554630dd57454630,0xd9d7455230dd57654630,0xbd781592309dd8755230,0xcdd7659230d9d7459230,0x9df845da309dd8759230,0xeb96458140f395454140,0x9f7815d940f355454540,0xde542dc151e756554560,0xd7565dc151d7554dc151,0xfa56450951fc56350951,0xbd78650d51f556550d51,0xbd78458d51f555458d51,0xf356455151f558355151,0xb778655151b758655151,0x9f78759151e756559151,0xf558359551f678259551,0xbe7825d951b778459551,0x9dd85dd943bcf8259543,0x9f7815d954e3d6559154,0x9f580dc564dd573dc564,0x9f585dc564dd583dc564,0xff15458110ff16550110],#[0xff18558110ff18458110,0xfe58550910fe56550910,0xfb56455110fe58650910,0xbf58655110f756555110,0xef56559110bf78655110,0xbf78459510fe78259510,0xfd56454630bf7855d910,0xfd58654630fd58454630,0xddd7655230f9d6455230,0xbdf8655230bdd8655230,0xfd78159230ddd8755230,0xddd7559230edd6559230,0xddd8759230bdf8559230,0xfb96454140ddd845da30,0xff15158140df97654140,0xef96558140fb95458140,0xbfb8558140df97558140,0xf756554540fb56454540,0xf3d6555140df57654540,0xbbd8655140dbd7655140,0xfb78159140bbf8655140,0xdbd7559140ebd6559140,0xbef8259540bbf8559140,0x9fd8759540cfd7659540,0xdf7815d9409ff865d540,0xfe542545609ff855d940,0xef56454560f755454560,0xebd6455160df77454560,0xef78159160afd8655160,0xaff8559160cff7559160,0x9fd85dd160bf7815d160,0xf758055151df564dc151],#[0xf758059551f758655151,0xbf7805d951f758459551,0xdde8759543fcf8259543,0xdbd64dc154dde8755163,0xf9d645cd549fd86dc154,0xbdf865cd54ddd765cd54,0xfb78159154bbf8059154,0xbf7815d954f9d8359154,0xdf7815d9549ff805d954,0x9fd80dd954ddd835d954,0xcfd65dc164df7715c164,0xbf580dc5649fd85dc164,0xdf575dc564ef565dc564,0xdf580dc564bf585dc564,0xedd655cd64df585dc564,0xbdf855cd64ddd755cd64,0x9fd80dd564bef825d564,0x1ec0cc051020409c000,0x210687b038417d0a9848,0xc867e30c16c8a984f825,0x8022b108c7f23cf1d28d,0x5f0aa451f27613089424,0x6b73421920c3c5e22d79,0x1f5cf487713a81c50dc2,0x890946fa28d0e083d405,0x9a8a53ec9cc4cca5e127,0xd4b4058b2bd5572a7d52,0x40b15d85abf15e82e996,0xa58d0b66c3301962c906,0x6f03745b72d8f6b2b4ed,0x9cbce4671bb859c0edf8,0x877bbb59d6ae9d742b9d],#[0xa1f20f787b03d21e60f1,0x5c82240d604cffc7e4be,0x3b21970aa84dc2320e90,0x1cd8d1c5e629f13787dc,0xc99a49d236913c81a3dd,0x332c985cb6255d28d93a,0xfd19e88d4259f4ce926e,0x7952da8653ae99548ea3,0x5d7aab81584ab6552ea,0xda36c2b4c5972c9b623b,0xbddde46ee1746b92dc12,0x7c9e3a50a3c22300d7e5,0x186c33c2630745108783,0x51212c68e8a84e10a84a,0x1583c215094414708542,0x78428150828e0f085425,0x41408833c1e14258c389,0x23f098c250f84c6848a8,0x28a840de013251e131b1,0x8a85a0b1b122a1384511,0xe0ca2f0b12291b85c1c4,0x89150b47c051b8589168,0x306814662e2052370b83,0x28c884809c12a317102,0x18f46440a54e0b1f1025,0x20880f8146082204e0d0,0xfc0082204a3d1710184c,0x10440bc1127028a88168,0xd1780c51242041251f80,0x1f85c00e8bc1e0708401,0x441086f8214e12746e08,0x4e0f085989181985e162],#[0x1309c260b16931414441,0x98fc2e0852922f0b8349,0x582a0e838063e1a8ac91,0xa49158fc14a516922f08,0xa528ec5a48ac7c061a8,0xb24422e028f86629245e,0xc210a70b822a142b14e0,0x2a13082c10f0b01c1150,0x5185814e1704542f0b82,0x53842b0f83470661b854,0x4582a102b14e0b24582c,0x12207b85478a06c5e170,0xa351d8c12848947a3617,0x361784301f8486e0f020,0x3244020a5921d1f820cc,0x86c38330ac9101985e1,0xc1848a840661f0ac6e0f,0x1470a12330a122a0d84,0x15081f61306122088388,0x86d34570c96094586c2,0x921908822a148e450854,0xdc220882a04544321061,0x4321082a219088226268,0xacc108940a0ca810308c,0x1820320900312024604,0x2611141c19002098402,0x4031270020180c80150,0xa122a08582a84862460,0x7085909085909085909,0x1228b1862a0c59090a12,0xa20d042a105982c08ab,0x8584308862c080c08b01],#[0xc1510c303822c0712290,0x401000c06041b82c4862,0xc200080301040d0600c0,0x2c4880c018080020a713,0x618a82c10ab1218b0558,0x420410c210822a41a083,0x70b1218a88610141c48a,0xd8414141a0301004411,0x43c21c3ec264862962b,0x2608b19228b036c360a0,0x8842c34070b822c1c3ec,0xc8218781947219088230,0x8213080424e084c3a360,0x1c306830060200800603,0x58e120d82c0a10615093,0xb0854120c06290454085,0x101a0c0180401c21b841,0x10402e0f00314f0b8200,0xa185408a43343a108030,0x178429101a0301004002,0xc521461b098228a4164e,0x708406709921e1784290,0xaa8420a830120d86c106,0x4618618dc00908c1600,0x602000a84e170]]
def g191H7 := limbs80 #[#[0x81440036013010004000,0x4c08200087210e8c6002,0xc38508b404606103ab02,0x2810414a80183448700d,0x8f1e5818102159800086,0x48eb884000147800010a,0xac5a22812fa4ad831137,0x2110b97b05380,0x242a03283cb03800000,0x6c0c00000000000,0xd6c00020839440900000,0xd375e68001a50942e,0xab72ed41d12b000051e,0x8b67a2f058e4d000,0xd641b65d340000385000,0x84bf9a195010392180,0x5448f8001a5a7c630ac0,0x80b60c09aa263c0e0002,0x5538003b1e58451b4283,0xea7e8200000001c24a70,0x1f247a5762b69b729414,0x50000c4500019a695600,0x94f090409ca1fc05ea,0x110000423bb075d2a440,0xd8685246250e895760dd,0x59ef85c000c0b2d4bd1b,0xa6ac324e21d43291c334,0x7100d646d7888c99008e,0x87caa68d31c40008048c,0x50801b0d4ea2709c4830,0xa0446b31bc9640006843,0x24c00085c0004667],#[0x864f84fe0e0003660000,0xee8b20fc0fc173308d67,0x610145891dc5c571bd3,0x24d25b44e66270003c,0x92972c03c52de9088440,0xca544f9a5ad3327cb322,0x868527a810718f982c54,0xe000a49698f686b90d3b,0xb000040008662394f3cc,0x183460f0a396ea16aa3,0x5310f6c4a81769b00000,0x189d78c70c3cf00002,0xa17a97663fb1b0000000,0x6d2107a7c40000d14000,0xf43160cec5355f996e9b,0x24ae0002418000d2ff4,0x72893491800000030780,0x40284dc51d48cc2223c0,0x86f59db155ac418a3c13,0x34ff52cb54c0e329b,0x40971cbe1664827d3b7,0x1ba33d3999b71d0a2400,0x980009c3a20b81ae5eb5,0x360003cca066430e0d58,0x7]]
def g191D8 := limbs80 #[#[0x542443f8b0221fc50110,0x8c617ddd510beaea887e,0x51bbaed185dd748c3eaa,0xfd543547f2a12a37ddc1,0xab2aa3dd55151faac6a8,0xd163bbeeca1ddf7550fb,0x887f554442fbb8ac977d,0x3fabaa21fd59510feac8,0x759230fbaa9187f57644,0xa2a07f960503fca8281f,0x503deb2281ef55140fea,0x1fd54560bfaeca05fd75,0xeae0a8dff745837eb22c,0x76547faba2a3fd59151f,0x2a9f755163fbacaa1ff5,0x4f7ac8aa7dd73552ffb8,0xff70592ffbb2a97f5d95,0xb2ac9f75cd64feee2b25,0x160ffacaa05ff755937e,0xa7fd70553feba2c1ff55,0xfebaac9ff5c164ffaeca,0x704783e02e82100d8003,0x8bc0aa89908187406485,0x249111018f60ea8df0cd,0x917d9701629531439301,0x9f21dc9c71b99ac19898,0x62a53247a36226a17205,0x72c7ab029ea8f281a722,0xb36324b15303af42e4ad,0xc1251b83b74360b53343,0xb146b051c24909c7c6c2,0x151c2c7c62518a08b1b0],#[0x251068530b0518aa2474,0x1531f151b06207c2c146,0x207c7c6c1c00810190,0xc2c1144918931b151f07,0x7947271e191708bc7c5,0xc786c145492106006e5,0x5203161b051d2481b948,0x211bc9c714c1c245208a,0x2148b271453051f08b08,0x1f070024485c1c013091,0xf070a147c1c018091015,0xbc2c14645892433271a1,0x251b0b04a89458019471,0xc78019474522c2c14689,0x21a1b1c5227070888686,0x1b070116206164680c1c,0x7454647c1c04588191d,0x9c1c2c0471d1f0b07008,0x1d006e270b051a749280,0x74621c1c2c0461d1852,0x5c2c1c08928ab07091f0,0xb070224a211f1c07468,0xc1468924a8a0711c1a17,0xb011624840148522c287,0x2c145c0281ca8a01f070,0x690b048851246c70603c,0x8514484543c2c1862a20,0x7c2c1141b1f0b0428889,0x491f0217051a24716484,0x48461846c1c08745891c,0x2c1c049211c1f0b07012,0x84170b07011e18815c71],#[0x308478685c2c1c02ca8,0xd1f0703088472c2a21,0x8a4706c2c1c0492a182,0xc0c1492a1f271a140307,0x81f0b07011a14818c612,0x8080346c0c1c22a1cb0a,0x28191a090a05047224b0,0x101170a2474582428921,0x9211f1c85c24918a8a07,0x1cb0a886150d05011f08,0xb00a88281c85c2c02a49,0xb2150d04870]]
def g191H8 := limbs80 #[#[0x604a5388270080090000,0xcc00184230b20408409,0x1d9c3302f8d1d2b11042,0x523700f0a62026119002,0x3f0934a000000247566,0x9f0005a0ac2e71374c80,0x160000677397f8e20afe,0xc1e0000001d100870006,0x4f40000004278864,0xd77f02f0000000645000,0xc90d2eb540dcb5b054ab,0x1629000510800147020,0x15000289a00000071840,0x68cc430000a844a52284,0x7d84000000ca8008e,0x2a1a0000000983408000,0xdd93ac4486a00000019a,0x1409c000000000350cc2,0x365b4792400134483228,0x16,0xd32c2f8003edc0000000,0x242c000073c1f0000000,0x73d8000010000000,0x12ce72b8f335a4da6800,0x3c5b0060005c,0x48e243817e9700000000,0x112000429f0288600004,0xd45800044529680d0001,0x586e00028d8001255a5b,0xcda58457843b2350961f,0xcb4294066348474000c1,0x77d31e0ad30e61d53a89],#[0x1b8f0000423c58f,0x45d100611c000000c3c0,0x1e6d0002e74000,0xd336cca8000000f0c000,0x3606cc88f663881841c1,0xba100012f400072,0x8e151c00000000080000,0x2ca000d1200000000003,0x740c00183f00018c6,0xf170000000e55,0xf964058136530d46800,0x14000e33c4e00030b800,0x2064254d391c00000064,0xc88686e6b00014ffa122,0x11754a00000016710005,0xf2471474e8,0xc00000058312d4000120,0x98003c0e000000000184,0x1a8a2350001d0000054,0x2d2312529872828e40,0xe1cf41a0880006b71890,0x6ab800000084c51ec09d,0x85e41330c7a1694135f,0x574651da93b23b727800,0xb7e5c00053300028d802,0x1c0fb41e5,0x1f000147f00000000000,0xe09fcc21f8cac4790001,0x80034040004208000f23,0x1a8fdba7128001881b37,0x3e00000695d0fd96400,0x367831712f4b400000],#[0x3cce000b2a00000,0x7810]]
def g191D9 := limbs80 #[#[0x63f750ff551f78c3f510,0xfd64ff553fd60ff503dd,0xfef53c82b554a671b803,0x6008180478d092c1123e,0x524c78a1a0c2223c68b0,0x1802468f1a0c00a24600,0x98f1a141807478d143c,0x8292a21468a1e0c0124,0x10612a241a1931c34181,0x393183858]]
def g191H9 := limbs80 #[#[0x22412001c3142001141,0x1081e67e72c0b003430,0x11d001b091b29f0,0x17d400360000,0xc14623d305ec31462c00,0x3926e002054ab24d48a1,0x14840018c713ace87a,0xfc0e31000ca800156ccd,0x604000000561958b,0xf080000000000000a100,0x8000000000000051d091,0xcb8001cc,0x20001c900044eb400000,0x2720380082fc0046feb7,0x479f300012a5c1000eb4,0x1800a0a000c88a800111,0x6036000003b5c8662c9,0x32e12c2a05ca05d8d,0x186a4c2b486554997c13]]
def g191D10 (j : Nat) := if j=0 then 0x1238c2820043ff else 0
def g191H10 := limbs80 #[#[0x4413241c032319080028,0x130018401187280001,0xe45d4006700000]]
def g191L : Nat → Packing
  | 4 => (3,6,6,0,0,4,0,g191D4)
  | 5 => (46,5,6,0,0,9,0,g191D5)
  | 6 => (174,4,6,0,0,12,0,g191D6)
  | 7 => (162,3,6,0,0,13,0,g191D7)
  | 8 => (58,2,6,0,0,12,0,g191D8)
  | 9 => (9,1,6,0,0,9,0,g191D9)
  | 10 => (1,0,6,0,0,0,0,g191D10)
  | _ => emptyPacking
def g191I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 5 0 6 2 0 g191H5
  | 6 => lookupWord 15 157 3 11 6 1 g191H6
  | 7 => lookupWord 63 311 7 13 8 1 g191H7
  | 8 => lookupWord 58 379 5 13 8 1 g191H8
  | 9 => lookupWord 20 127 6 11 6 1 g191H9
  | 10 => lookupWord 3 23 3 9 4 1 g191H10
  | _ => fun _ => none
def g191 : Forest := ⟨191,10,fun i => g191Y[i]?.getD (0,0),g191C,g191A,g191L,g191I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P4_0 : block g191 4 0 3=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g191B4 : block g191 4 0 3=true := g191P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P5_0 : block g191 5 0 46=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g191B5 : block g191 5 0 46=true := g191P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P6_0 : block g191 6 0 14=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P6_14 : block g191 6 14 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P6_110 : block g191 6 110 64=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g191B6 : block g191 6 0 174=true := (@block_merge g191 6 0 14 160 g191P6_0 (@block_merge g191 6 14 96 64 g191P6_14 g191P6_110))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P7_0 : block g191 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P7_1 : block g191 7 1 61=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P7_62 : block g191 7 62 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P7_158 : block g191 7 158 4=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g191B7 : block g191 7 0 162=true := (@block_merge g191 7 0 62 100 (@block_merge g191 7 0 1 61 g191P7_0 g191P7_1) (@block_merge g191 7 62 96 4 g191P7_62 g191P7_158))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P8_0 : block g191 8 0 18=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P8_18 : block g191 8 18 33=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P8_51 : block g191 8 51 7=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g191B8 : block g191 8 0 58=true := (@block_merge g191 8 0 18 40 g191P8_0 (@block_merge g191 8 18 33 7 g191P8_18 g191P8_51))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P9_0 : block g191 9 0 5=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P9_5 : block g191 9 5 4=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g191B9 : block g191 9 0 9=true := (@block_merge g191 9 0 5 4 g191P9_0 g191P9_5)
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
  · exact g191B4
  · exact g191B5
  · exact g191B6
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
def K191 := extendKnown K127 11 [(191,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V191 : Known true K191 := extend_ok (m:=191) V127 low191 (by decide +kernel)
def g223Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfb02da18b421cc2951,0xe0c00001fc0000003fff])),(BitVec.ofNat 152 (word80 [0x4102d81094204c0841,0x80c48912244891224489]))),((BitVec.ofNat 152 (word80 [0x1228d2402d89e9fc1,0x1b0000fe00000fffc000])),(BitVec.ofNat 152 (word80 [0x61008c2402188c1fc1,0x90183060c183060c183]))),((BitVec.ofNat 152 (word80 [0x758ad02f634115537,0x8407f000007f0000000])),(BitVec.ofNat 152 (word80 [0x87188d02f634105513,0x803870e1c3870e1c387]))),((BitVec.ofNat 152 (word80 [0xf25c4ce7abc3f04140,0x6900000003f80000007f])),(BitVec.ofNat 152 (word80 [0x25c04e623c3904100,0x6913264c993264c99326]))),((BitVec.ofNat 152 (word80 [0x85814f63a014663a,0xd6bf80000000001fff80])),(BitVec.ofNat 152 (word80 [0x5010b618010603a,0x520a142850a142850a14]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x116669158062bf0a8,0x15c0000003ffffe00000])),(BitVec.ofNat 152 (word80 [0x26211080023a028,0x14ec58b162c58b162c58]))),((BitVec.ofNat 152 (word80 [0xce93272055b22080f,0xc3ffffffc0000000000])),(BitVec.ofNat 152 (word80 [0x8e022400043220004,0x43060c183060c183060]))),(0x0,0x0)]
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
def K223 := extendKnown K191 11 [(223,[]),(239,[33,84])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V223 : Known true K223 := extend_ok (m:=223) V191 low223 (by decide +kernel)
def g247Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xd2c83c9253ca252200,0xfe0000001fc07f])),(BitVec.ofNat 152 (word80 [0xd2c01c90520a212001,0x22448912244891224489]))),((BitVec.ofNat 152 (word80 [0x42af409550361b84a0,0x7f0003f800003f80])),(BitVec.ofNat 152 (word80 [0x42ad409110161b0020,0xa142850a142850a14285]))),((BitVec.ofNat 152 (word80 [0xecd729801410d27110,0x3f8001fc000fe00000])),(BitVec.ofNat 152 (word80 [0xccd628801410920010,0x60c183060c183060c183]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x8432279aa84d908c40,0x1fc000000007f0003fff])),(BitVec.ofNat 152 (word80 [0x41221022841808c02,0x44891224489122448912]))),((BitVec.ofNat 152 (word80 [0x1a99a692c12e442af,0xe00000000007ffffc000])),(BitVec.ofNat 152 (word80 [0x129024900004442a4,0x89122448912244891224]))),((BitVec.ofNat 152 (word80 [0x7154172748a10967d0,0x1fff800000000])),(BitVec.ofNat 152 (word80 [0x3100172648a10067cf,0x1e3c78f1e3c78f1e3c78]))),((BitVec.ofNat 152 (word80 [0x3f00c064938102186f,0xfffffffe000000000000])),(BitVec.ofNat 152 (word80 [0x200080248180001048,0x10204081020408102040]))),(0x0,0x0)]
def g247C : List ColumnInfo := [(1,0,246,0,10),(2,0,245,0,10),(4,0,243,0,10),(0,64,177,6,9),(16,0,231,0,9),(32,0,215,0,9),(64,0,183,0,9),(128,0,119,0,9),(48,0,199,0,5),(144,0,103,0,5)]
def g247A : List (List Nat) := [[],[33,84]]
def g247D6 := limbs80 #[#[0x7650f8db76e0f805d943,0x13835d943ce6e5393e01,0x6e1383e017650f89f76e,0x50f59b94e4f805d943e6,0x805d163d36e5b93e0176,0x91e612306032db96e4f]]
def g247D7 := limbs80 #[#[0xc1aeca1e37ddb835d943,0x87e9f76e116350f33f09,0xdb805d943dedc1f00bb2,0x650f7b727c02eca1f3ed,0xfbb706bb287b9f84e0d7,0x2eca1f76e0f805d943e6,0xcfb96e017650fbb727c0,0x8359163ecfc2706bb287,0x8f7b707c02e8b1fa7dd3,0x9f00ba2c7afb86e01745,0x8b1ebee5b805d163dedc,0x920e8b058035bf0dc1ae,0xb531ae2aa723a01c9915,0xa507c35c2f1f00bfbc38,0x7c01d704c013004c01,0x4c01a407c013004c013,0x35413004c0130]]
def g247H7 := limbs80 #[#[0x14000030,0x0,0x402c61a8c20880310000,0x1940000000003b]]
def g247D8 := limbs80 #[#[0x9fb805d943e9d6458d43,0xedf7658d43f9f8458d43,0xbdf835d943bfb805d943,0xdfb805d943cff765d943,0xedf8359163ddf835d943,0xbdf835d163bfb805d163,0xffb805d943aff865d163,0xffb805d163fdf835d943,0xeff865d163fdf835d163,0x5b14344cd5294750f800,0xb7ac3abe789060374daa,0xbf6e696272e3c08c36f2,0x3c2b8ddb9e5c9cb8d71c,0x91c8bc4e3c328dc92c4e,0x270ae330edcf2f2e392b,0x2c08cb93971e0288e5c5,0xe5c6bf0172e4edcebf2e,0x8d5ce44749cb8f0aa365,0x3971e15738ec3b73c9cb,0xae1094fcb8f0ab907129,0x26af00c85508457e0190,0x1357806]]
def g247H8 := limbs80 #[#[0x1ca0024481f8cb13803,0x3d4800943ba0c1b8c000,0x1a4ba39d020000846208,0x9dc56a54d69400000009,0x1c9d]]
def g247D9 := limbs80 #[#[0xe6550fbeb2a87f758d43,0x22c77fdd943bfaeca1f7,0x43ffaeca1dff7458f7eb,0x7ff7458ffeba2c7ffdd9,0x2c4991f86612c3306c00,0x9b672e58e0b910b3b4cf,0xbe58e03cb226be58e038,0x8f2ed9c8be58e044b22c,0x6ae58e1211b66be39612,0xbe04ed9ab8e584e38fb6,0xe58e0b904912ed9c9962,0x326d9cf92b8e048a26d9,0xe26d9e58e0a9249]]
def g247H9 := limbs80 #[#[0x544000034cf264113c03,0xfa007701ae7360b13c00,0xa2800c0c00f420200069,0x345,0x348e97c443823000c6]]
def g247D10 := limbs80 #[#[0xff58ffd43df9977d65,0x180f5a1c709447805229,0x8bda6524a3022b439a5,0x2b6990f28c]]
def g247H10 := limbs80 #[#[0x40cc400,0x0,0x80000035000000094000,0x6840186000000130124,0x117cfc90000000000]]
def g247D11 (j : Nat) := if j=0 then 0xea8c642047f else 0
def g247H11 (j : Nat) := if j=0 then 0x342a011e9b1 else 0
def g247L : Nat → Packing
  | 6 => (7,5,4,0,0,6,0,g247D6)
  | 7 => (18,4,4,0,0,8,0,g247D7)
  | 8 => (18,3,4,0,0,10,0,g247D8)
  | 9 => (11,2,4,0,0,10,0,g247D9)
  | 10 => (4,1,4,0,0,8,0,g247D10)
  | 11 => (1,0,4,0,0,0,0,g247D11)
  | _ => emptyPacking
def g247I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 2 37 3 8 3 1 g247H7
  | 8 => lookupWord 6 31 4 10 5 1 g247H8
  | 9 => lookupWord 5 37 4 10 5 1 g247H9
  | 10 => lookupWord 3 47 0 9 4 1 g247H10
  | 11 => lookupWord 1 7 0 7 2 1 g247H11
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
theorem g247G : graphValid g247 (boundsBefore K223) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low247 : Lower true (varsX 247) (graphGoal 247) 12 := lower_forest (g:=g247) (i:=0) (hints:=16778564) (before_sound K223 V223) g247G g247T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K247 := extendKnown K223 12 [(247,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V247 : Known true K247 := extend_ok (m:=247) V223 low247 (by decide +kernel)
def g251Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x4e844a219d84168000,0xff000000ff00ffff])),(BitVec.ofNat 152 (word80 [0x46800a210d00068009,0x9090909090909090909]))),((BitVec.ofNat 152 (word80 [0x27b0031d6076ae300,0xff0000ff0000ff0000])),(BitVec.ofNat 152 (word80 [0x271001196060ae305,0x5050505050505050505]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x2005c746be72596000,0xff0000000000ff])),(BitVec.ofNat 152 (word80 [0x200545469212596046,0x46464646464646464646]))),((BitVec.ofNat 152 (word80 [0xa7226dd0022bc11400,0xff00000000ff00ffff00])),(BitVec.ofNat 152 (word80 [0x10245800029c10012,0x12121212121212121212]))),((BitVec.ofNat 152 (word80 [0xd91534dc13442229ff,0xffff000000])),(BitVec.ofNat 152 (word80 [0x981530541244202124,0x24242424242424242424]))),((BitVec.ofNat 152 (word80 [0xc49a93a66070a8ae00,0xffff0000000000])),(BitVec.ofNat 152 (word80 [0xc48a92a06060a00cb8,0xb8b8b8b8b8b8b8b8b8b8]))),((BitVec.ofNat 152 (word80 [0x30c990090098855dff,0xffffff00000000000000])),(BitVec.ofNat 152 (word80 [0x200880080090001cc0,0xc0c0c0c0c0c0c0c0c0c0]))),(0x0,0x0)]
def g251C : List ColumnInfo := [(2,0,249,0,10),(8,0,243,0,10),(32,0,219,0,10),(0,64,177,10,9),(16,0,235,0,9),(64,0,187,0,9),(128,0,123,0,9),(1,0,250,0,8),(0,8,178,65,7),(33,0,218,0,7),(17,0,234,0,5),(129,0,122,0,5),(144,0,107,0,5),(146,0,105,0,4)]
def g251A : List (List Nat) := [[],[116]]
def g251D6 := limbs80 #[#[0x764c38db76e0f805d930,0x13835d930e2eddb84e01,0x6e4f90e11764c389f76e,0x4c359b93e43845d930ce,0x701c163d27e5b93e1176,0xa5845c07058f9b394605,0xf1bb98e51701c163a6ea,0x5c163c6ee93985c07058,0x1e6123060329f96e4f84,0xf36c2a9,0x190100]]
def g251D7 := limbs80 #[#[0x402c698637ddb8358130,0x6179994201634c2fa322,0x5701c163c7dbb700bb2,0x58f37308b80e0b1e7c6,0xfca30f382c71fb985c07,0xac0987b6e4163581308d,0x7da97201634c3db6edc1,0x805d930f6dbb700b1a61,0xc377709c02ec986f6e0f,0x2706bb261cfb76e01764,0xc98737ddb835d930dcfc,0xb90e11764c397eedc22e,0x5d930dcfc9f08bb261bb,0xb7709c02ec9866fe1380,0x8bb261dbb90e11764c3,0x1e6fe43845d930ecfc9f,0x85c07058fb7728b80e0b,0x163dcfc2706b82c79fb9,0xf27c22e0b1eb7e1b835c,0x382c73bf9461e7058f73,0x781a84407800cdfca30f,0x5050934499083e8c4278,0xc06c9a4659885e96c579,0x28869fc7d9f0789d4719,0x20d13cfcbc0396a4c8fa,0x84f207cfc028a44f30af,0xc860b0ab319102c2acfc,0xe1a903f3042c2b9b900f,0x1b0075815607101a4041,0x3204c817007c81b007c8,0x2bc830003204c81b0040,0x7901660428902a4042c],#[0x2]]
def g251H7 := limbs80 #[#[0xf4650024800000000180,0x4d470000263e581b24c3,0x508002000622]]
def g251D8 := limbs80 #[#[0x9bf845d930ed96358130,0xbdf8358130edd6358130,0xbfa8798130fdb8358130,0xfdb8058d30fd88058d30,0xbfb805d930edf7658d30,0xcff765d930bbf845d930,0x9ff805d930dfb805d930,0xdf9701c163dbf845d930,0xbed821c163bf5811c163,0xbdf835c163bbd841c163,0xdfb709c163bbf845c163,0x9fd879c163bdd839c163,0xffb805d930fdf8058d30,0xfdf835d930bff805d930,0xdff805d930fbf845d930,0xfbf845c163fdf835c163,0x661d41f000bfd879c163,0x8ecfe9c631e560908ea1,0x5d0369664bed6229b4f2,0x8d369f13064544c838f9,0xebe7746db5a2b0f5b2a,0x780f1faf32c938f0e446,0xc7824e51c865d79d6c9c,0xe2b9f049c79561faf32d,0x71e7907e7c23a4e5c6b0,0x20ae6c787218387e15b9,0x5c050ecd3c4e1c79561c,0xe1c6b73e590809cf896e,0x4cfd5973e1c6b6420527,0x83d6c9c39f2179f015c8,0xe7c59701eb05e7c7872c,0x7a7c058a67c8b8f5b275],#[0xf970c84f5c9cf8f22e34,0xcf8f032307119baf3625,0xc840ce69397016375c9,0xf2e05c60fd6bb2e7c737,0x40ce7c4bf0e4907c94d9,0xd1138798605c9cf8f0e4,0xab720c5564e18aadc838,0xb49c84162b9064ab042,0x2624332095f2120c6]]
def g251H8 := limbs80 #[#[0x31d000c019060,0x2d3000000000050b0f,0xddd8c00000c140000000,0x1175c400001d0,0x88800,0x218000000032b0880fee,0x61c00000000013b00000,0x10400f4800,0x216000000020400000,0xb35d8f2e0000000c4400,0x638000000000000c7921,0x9241a350230000045400,0xc6d1f4f400e719900000]]
def g251D9 := limbs80 #[#[0xd634c3fd30261fe58130,0xb4617fdd930bfaec987d,0x30ffac0985ff7058efeb,0xffc7058fffbb261ff5d9,0xfb82c7ff9c163ffae0b1,0x84e102348a21b036003f,0x6422e2a9a6a889e66a96,0x75a4c32c481f5cd6c32c,0xc871359f3c70c96235cc,0x735b1c329075b5ce4c70,0xca61e4d731f1c32588d,0xd73c16cb11e42a4d73c7,0x892a7d73930c56c892ca,0x7cb030b1c4d73c32c562,0xcf1930c89d53195933c5,0x26d73c64cb05c93355e6,0x197d64cf1cb03093]]
def g251H9 := limbs80 #[#[0xa009412c0c0003044,0x9300030ce2000f0767c,0xe26cde9e001e5000,0x24002c3800a8ca008780,0xa340d000e05c40cb404f,0x84e999d1181423800818,0x5901d1574c088569b081,0x4b431271ef70e42ee568]]
def g251D10 := limbs80 #[#[0x45c5c03fd63ff8c3fd30,0xb324a303907b566484a2,0x7accd124a041a]]
def g251H10 := limbs80 #[#[0xd689a0d2020079942004,0x72a250c0000003a9cb2,0x1304e8b000010]]
def g251D11 (j : Nat) := if j=0 then 0xc8a64203ff else 0
def g251H11 := limbs80 #[#[0x4000140009801880,0x3a0]]
def g251L : Nat → Packing
  | 6 => (11,5,4,0,0,6,0,g251D6)
  | 7 => (32,4,4,0,0,10,0,g251D7)
  | 8 => (33,3,4,0,0,11,0,g251D8)
  | 9 => (14,2,4,0,0,10,0,g251D9)
  | 10 => (3,1,4,0,0,7,0,g251D10)
  | 11 => (1,0,4,0,0,0,0,g251D11)
  | _ => emptyPacking
def g251I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 3 23 3 9 4 1 g251H7
  | 8 => lookupWord 10 101 3 10 5 1 g251H8
  | 9 => lookupWord 10 53 6 11 6 1 g251H9
  | 10 => lookupWord 4 23 1 9 4 1 g251H10
  | 11 => lookupWord 1 13 0 7 2 1 g251H11
  | _ => fun _ => none
def g251 : Forest := ⟨251,11,fun i => g251Y[i]?.getD (0,0),g251C,g251A,g251L,g251I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P6_0 : block g251 6 0 11=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B6 : block g251 6 0 11=true := g251P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P7_0 : block g251 7 0 8=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P7_8 : block g251 7 8 24=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B7 : block g251 7 0 32=true := (@block_merge g251 7 0 8 24 g251P7_0 g251P7_8)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_0 : block g251 8 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_2 : block g251 8 2 22=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_24 : block g251 8 24 9=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B8 : block g251 8 0 33=true := (@block_merge g251 8 0 2 31 g251P8_0 (@block_merge g251 8 2 22 9 g251P8_2 g251P8_24))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_0 : block g251 9 0 7=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_7 : block g251 9 7 7=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B9 : block g251 9 0 14=true := (@block_merge g251 9 0 7 7 g251P9_0 g251P9_7)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P10_0 : block g251 10 0 3=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B10 : block g251 10 0 3=true := g251P10_0
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
theorem low251 : Lower true (varsX 251) (graphGoal 251) 12 := lower_forest (g:=g251) (i:=0) (hints:=16777283) (before_sound K247 V247) g251G g251T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K251 := extendKnown K247 12 [(251,[]),(253,[33,84])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V251 : Known true K251 := extend_ok (m:=251) V247 low251 (by decide +kernel)
def g254Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0xff0418928204c0afd7,0x62c00001fc000fe0007f])),(BitVec.ofNat 152 (word80 [0x450418028204400ed3,0x42c2850a142850a14285]))),((BitVec.ofNat 152 (word80 [0x1224e0c0c7c9c1f51,0x9a0000fe0007f0003f80])),(BitVec.ofNat 152 (word80 [0x61000c040c4c9c1b51,0x880183060c183060c183]))),((BitVec.ofNat 152 (word80 [0x75c2c42f7b0171535,0x940000003f800000000])),(BitVec.ofNat 152 (word80 [0x874c0c42e7b0171515,0x953a74e9d3a74e9d3a7]))),((BitVec.ofNat 152 (word80 [0xf258cda5aac3f04140,0x69007f000000001fc07f])),(BitVec.ofNat 152 (word80 [0x218458508c3900100,0x29050a142850a142850a]))),((BitVec.ofNat 152 (word80 [0x85814f63a014663a,0xd6bf80000000001fff80])),(BitVec.ofNat 152 (word80 [0x5800a632000642a,0x528a142850a142850a14]))),((BitVec.ofNat 152 (word80 [0x116669158062bf0a8,0x15c0000003ffffe00000])),(BitVec.ofNat 152 (word80 [0x126291100220e028,0x142c58b162c58b162c58]))),((BitVec.ofNat 152 (word80 [0xce93272055b22080f,0xc3ffffffc0000000000])),(BitVec.ofNat 152 (word80 [0x8e022700010220004,0x43060c183060c183060]))),(0x0,0x0)]
def g254C : List ColumnInfo := [(8,0,246,0,10)]
def g254A : List (List Nat) := [[],[33,84]]
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
theorem g254G : graphValid g254 (boundsBefore K251) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low254 : Lower true (varsX 254) (graphGoal 254) 11 := lower_forest (g:=g254) (i:=0) (hints:=287401280) (before_sound K251 V251) g254G g254T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K254 := extendKnown K251 11 [(254,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V254 : Known true K254 := extend_ok (m:=254) V251 low254 (by decide +kernel)
def g255Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xff800000000003fe0,0xffffc0d107063590fcc])),(BitVec.ofNat 152 (word80 [0x108844221108844221,0x10884404002021580484]))),((BitVec.ofNat 152 (word80 [0xf0000001ff0000001f,0xf00000000081801e003f])),(BitVec.ofNat 152 (word80 [0xb0582c160b0582c160,0xb0582c000000800a001f]))),((BitVec.ofNat 152 (word80 [0x3fe00007fc000,0x1000c60103f])),(BitVec.ofNat 152 (word80 [0x70381c0e070381c0e0,0x70381c0000000400003f]))),((BitVec.ofNat 152 (word80 [0x7fc000000000000,0x7fc3000021080000f])),(BitVec.ofNat 152 (word80 [0xe472391c8e472391c8,0xe472381000000000000b]))),((BitVec.ofNat 152 (word80 [0xff80001f,0xfff800c21e0c1f01e1e1])),(BitVec.ofNat 152 (word80 [0x412090482412090482,0x4120904004041e004120]))),((BitVec.ofNat 152 (word80 [0xffffffe0,0x303e00fe001fe02])),(BitVec.ofNat 152 (word80 [0x824120904824120904,0x82412100400bc0009800]))),((BitVec.ofNat 152 (word80 [0x7ffffff00000000,0x3fc000ffffe0000])),(BitVec.ofNat 152 (word80 [0xb85c2e170b85c2e17,0xb85c3ec000f7bf40000]))),((BitVec.ofNat 152 (word80 [0xfff800000000000000,0x3fffff000000010])),(BitVec.ofNat 152 (word80 [0xc06030180c0603018,0xc0602b889c000000000]))),(0x0,0x0)]
def g255C : List ColumnInfo := [(2,0,253,0,12),(4,0,251,0,12),(8,0,247,0,12),(1,0,254,0,11),(16,0,239,0,11),(32,0,223,0,11),(64,0,191,0,11),(128,0,127,0,11),(0,64,177,14,10),(0,8,182,65,9),(2,64,177,12,9),(8,64,177,6,9),(17,0,238,0,8),(33,0,222,0,8),(48,0,207,0,8),(80,0,175,0,8),(96,0,159,0,8),(129,0,126,0,8),(144,0,111,0,8),(160,0,95,0,8),(192,0,63,0,8),(1,64,176,14,7),(16,64,161,14,7),(32,64,145,14,7),(65,0,182,0,7),(65,8,182,0,7),(128,64,49,14,7),(17,8,166,64,6),(33,8,150,64,6),(49,0,206,0,5),(81,0,166,0,5),(81,8,166,0,5),(97,0,150,0,5),(97,8,150,0,5),(112,0,143,0,5),(145,0,110,0,5),(161,0,94,0,5),(176,0,79,0,5),(193,8,54,0,4),(208,2,45,0,4),(224,4,27,0,4),(49,8,134,64,3)]
def g255A : List (List Nat) := [[],[33,84]]
def g255D7 := limbs80 #[#[0x36c661fb36195454140,0x140d71997ecd86551505,0x505033c669fb36195454,0x454140cf1ba7ecd86551,0x5515050334eedda76995,0x1d5454140bb33c16d987,0x9a755150502ec6f0db66,0xb669d5454140af33c16d,0x3619755d150502bc670f,0xf05a65d57454140bd1bc,0x33c1699a55d150502f4c,0x56665fb36197454140af,0xd59997ecd965d150503,0x50356c65fb1699745414,0x4140b5abc26d9975d150,0x150502d66f0db665d745,0x545c140b53bc56d9975d,0x555170502f46f0d865d5,0x5d5545c140bd1bc36597,0x599555170502f4af09b6,0xfb3619545c140b71bc36,0xa7ecd965517050336669,0xcf05b669d545c140cd99,0xdabc26d9a755170502b6,0x2b4ef15b669d545c140a,0x40ad99c3ed9a75517050,0x502e66f0d86615745c1,0x5c140b99bc3659855d17,0xd170502e6cf05a661574,0x5745c140b99bc36d9855,0x955d170502e6cf05a6e1,0x6e55745c140b59bc3659],#[0x69b955d170502d66f0d8,0x5a6695745c140b5b3c1,0xbc361ba55d170502b6cf,0x66f0d96e95745c140ad9,0xadabc2699a45d570502b,0x2e56f0d86615755c140,0x140af2bc2699a05d5545,0x5450364761fb36197555,0x555140d92d87ec9a65d5,0x5d554502e4ef01b661d7,0x1d7555140b937c16d987,0x9a05d574502e47f0db66,0x86615755d140adabc269,0x1659855d574502e47f0d,0xf01b6615755d140b937c,0x1fc36d9855d574502e4e,0xc4e61d85651905d540b9,0x4b91fc3619855d1545c3,0x552e4df05a65d574e015,0xd154b537c16597564174,0x12002d4bf09b65d7905,0x8a1e066150420f03609,0x11a420f6390d2300ae27,0x1926016e5714a4e12648,0x20a811f2781ce6f1aa69,0x25e962469023a8a22287,0x2d6b12b2a828ea22769c,0x141d2336cc31ec02eeba,0x41e450400180c1604059,0x48180c07c0c1f030791,0x58101684058101d0306,0x604c181104003a101e84],#[0x307c0c16030580c1c840,0x1c1c070711c1f03040f0,0x340c1000c84040e47070,0x605040d04040d030400,0x711c1d04079141e4504,0x4404d172102e47040c07,0xc85040c]]
set_option maxRecDepth 16000 in
def g255D8 := limbs80 #[#[0xe0a05f1bb36195454140,0x65d170502ecdd9b0cba2,0x762d32e8b8281766ecd9,0xa791d755d154e0d60bb6,0x150502e9bd8b2cbaae8a,0xbb2a8a82817ceee17655,0x39876195454140be7774,0x503b9ccbb0caa2a0a07b,0xa8a8281dcee5d8655150,0x76195454140de734ec32,0xd9cc3b4caa2a0a06f3ba,0x8281ecee1da655150503,0x95454140de734ed32a8a,0xdb30eaa2a0a05f3bb769,0x1eceed98755150503d9c,0x54140de736cd3aa8a828,0xeaba2a0a06f3bb669d54,0xe699755d150503e9cc32,0x40fa7370baae8a8281f4,0xa2a0a06f39a669574541,0xd865d150503e9ccbb4ab,0xb732ec32e8a82817e6ec,0xa05f9bb36597454140e,0x5d150503adccbb2cba2a,0x2ed32e8a82817ecec5a6,0x75b9b665d7454140eb73,0x50503adddb32eba2a0a0,0x1b0ca82813de6d7a85d9,0x997e8d8654140d7b30fd,0x2df9d8b4cc3aa0a067d,0xea82816f6ecda661d505,0x6998754140b77768d330],#[0x9cc32eaaa2e0a05b7bb5,0x281f4e6597555170503e,0x545c140fa734cbaaa8b8,0xc2eaaa2e0a07d39b65d5,0xdce6599555170503e9cd,0xc140fa734ecaaa8b8281,0xcaa2e0a05f9bb3619545,0xecd96551705036dcd3b0,0xdb734ecb2a8b82817e6,0x2e0a06db9a7699545c14,0xa7551705036dcdb34eaa,0x7770b2ae8b8281b6eed9,0xa05dbbb9595745c140bb,0xd170502edddd2caba2e0,0xcc2ae8b8281e6e619855,0x9b9a6615745c140f3732,0x503cdcdb30aba2e0a07,0xae8b8281e6eed9855d17,0xa6e15745c140f3732dc2,0x3adccb32aba2e0a079b9,0xb8281d6e61b955d17050,0x95745c140eb734dcaae8,0xcc374aba2e0a06db9a66,0x81b6e65ba55d1705036d,0x45c140bb776acb2e8b82,0xf50b2ae0a05dbbb56997,0xee6d3a9595705026fcdb,0x140fa730ad22eab82813,0xbaae0a06db9a6691755c,0xcd865d570503cbcc330a,0xbbb766cb2eab8281776e,0xe0a05dbbb4659755c140],#[0x65d570502ebddab2cbaa,0x766c330ab828177aec9a,0x5bdbb3659855c140b7b,0x570502dedd9b4cc2ae0a,0xcb32ab828167eedda661,0xbbb4659955c140afb766,0x502bedd9b0dcaae0a057,0xeaaa2813ee6d7a465970,0x76817555140de734cd02,0xf8fd9b0cbaaa8a07d398,0xa281e4f61d865d554502,0x97555140be7760cb2eaa,0xdbb2cbaaa8a0793d8765,0x17cbec9a65d554502e9f,0x55140f27b0ed32eaaa28,0xebaaa8a0793db661d75,0xf6d7a85d954503c9fdb3,0x409f7361d4aecaa2813c,0x32a8a06b9d87e8d86551,0xfa3619545033cecbf46c,0xf732fd032caa2819e7e5,0x8a04fb9b7e819655140c,0x61d545032dfd3b2ecb2a,0x62d330eaa2816eeec1a6,0x5b9fb36998755140b76f,0x54502d9fdab4cc3aa8a0,0x332eaa2815eeec1a665d,0xfb26999755140af6f62d,0x2b9fdab4ccbaa8a057a,0xaba2815e76cfa665d545,0xea5655d1409b7b6fd42c,0x9cc2b40baae8a04fb9b0],#[0x281b6e699a05d574503e,0x755d140f27b0cc2aeaba,0xb30abaae8a0793d96615,0xe4fed9855d574503c9ed,0xd140bb3f66c32eaba281,0xcbaae8a05dbbb0659755,0xed5965d574502edbd8b2,0xbb5f64d32eaba28174f,0xae8a05b9fb3619855d14,0xa661574502ddbd8b2cc2,0x3f66d330aba2816eeec1,0xa059bfb7699855d140b7,0x5574502ddbd8b2dc2ae8,0x2cb32aba2815eeec1966,0x79fb361b955d140af6f6,0x55027dcdaf40cb2e8a05,0x30eb2a818dfe63a561d6,0xa9e958759540a3fb6fcc,0x29fcd8552c3acaa0637e,0xbaa814ef6d2a961d6550,0x51905d540ee730aca320,0xcc3b0ac82eaa075b9876,0x815faec99664175503cb,0x45d540f27b0ec2b28baa,0xb0cc2aeaa057afb26599,0x7761fa361975502dafd9,0x540c7bb31d1b0cbaa81a,0xc32eaa063df98e8d865d,0xd198619755029fdd8330,0xd3db0fd132cbaa814efe,0xeaa063ed98e89965d540,0x8659755031f74c744cb2],#[0xf6ecc32cbaa814dfed59,0x59fbb0699875d540a3f,0xd75502cfbd8b4cc3aeaa,0xd330ebaa81677ecda661,0x7fb5699875d540b37f68,0x5034bfd3f4acc2eaa059,0x30baa819eee93a066175,0x6e81985d540e77749d03,0x1fdd3740cc2eaa063f9a,0xaa81c7ee9fa066175503,0x1985d540e67f4bd2330b,0xd3748cc2eaa063bda6e9,0x1c6fe9fa4661755031df,0x5d540a7f760d3330baa8,0x4ccc2eaa053f7b169998,0xfed1a6661755029efd9b,0x40c3ff4ed3330baa814e,0xc2eaa051ffb7699985d5,0x3975d9855030ffd3f4cc,0x6fb6bd42ecc2a8187fea,0xaa063df97e8d86615409,0x5d9855030ffd4f2ebb30,0x6fd032cc2a812fe6c3a9,0x63dd97e8d966154097f3,0x855031efcbf46cb30aa0,0xbb2cc2a814feec197659,0xbb065f9661540a77f68c,0x29dfda32fcb30aa053f,0xec2a81aeee93a065d855,0x69b9761540d67f4bd232,0xfbd8b4ccbf0aa053dfb3,0xa814f7ed587e4d865029],#[0x9561d40d77749d032ac3,0xb740cab0ea069fba7e81,0x8fee5ba0655875031fcc,0x1d40d37f4fd232ac3a81,0x8cab0ea063bd96e91956,0xec596655875031dfcb74,0xa7bf66cb32ac3a814fd,0xb0ea061ffa76599561d4,0x96e55875030ffd3f2cca,0xbf66cb72ac3a814fdec5,0xa053f7b169b9561d40a7,0x59875029efd9b4dcab0e,0xbd232cc3a812fe6d7a06,0x93e985d57455160977b6,0x4583c9f542eaba2a8b07,0x2e8aa2c166f6de985d15,0x98e819755160b67b6b54,0x28fedbd30cbaa8b063fa,0xaa2c18feaa3a065d5458,0x61755d160a77b695432e,0xd4c740caae8b0597db5a,0xe1f4e61574641545c31f,0x55170eb732cba320aa2,0xb08c82a8b87b39856119,0x4f619855d1545c3adccb,0x170bb3f66c32e8aa2e1e,0xba2a8b85dbbb06997455,0xd5a65d1545c2edbd8b4c,0xf27b2ec2b08aa2e174fe,0xa8b85b9fb36198455170,0x3619545c32eecbf46c32,0xf31d1b0caa2e18f7663a],#[0x853fbb06618655170c7b,0x9545c28ffdbb30c32a8b,0xd332eaa2e14efed19865,0xf7b16999755170abf760,0x5c2adfda34ccbaa8b855,0x30aa2e15776cfa665d54,0x7e819855170d67f4bd23,0xabedaf30baac8b865fba,0x22e157e6c2a95d5645c2,0x9855d170c77f31d230ab,0xda30cc2ae8b859dfb361,0x167dec596e15745c2cdf,0x5d170abf760cb32aba2e,0xdcaae8b855f7b165995,0xf6d7a4619745c2aefd9b,0x709bf36bd032cba2e136,0xaf08b853dfb361b95611,0xda6657845c29f7d934cc,0x27b0cbaae8c02a94f7ec,0xaa59bfb76197460154f,0x5d3805530ffd472ebb30,0x62d32e9c02a9e4f69975,0x53f7b169997e0154b76f,0x74553a9ecb2eac82e8aa,0xb320ba2a95edec596641,0xd865d7905d154ae7f6ac,0x53a9edb2ebc82e8aa753,0xaba2a974fec1865d5745,0xe9d865d154ba7f60cb2e,0x9ed874acb2e8aa4dbdb0,0xaa947f6c39761d865527,0x9061d54d67f4bd2320c3],#[0xb748c830eaa69bfa7e91,0x8efe5ba4641875531dec,0x1d54a7ef62cb320c3aa9,0xcc830eaa61ffa7659906,0xe9f96641875529eed9f2,0x4a7ef62cb720c3aa987f,0x30eaa53f7b169b9061d5,0xa6643875525ded8748cb,0x7d31d2320baac94f7ecd,0xba59f7b16197560174c7,0x55805d2cbfdab0cbab00,0x4d32ebc02e94fdec586e,0x3f7b169995e0174b3df6,0x55d29f7d934ccaf00ba5,0x720c2ae935f6c3a56197,0xb169990e1574a7ef62c3,0x29efd9b4cc870aba53f7,0xb0bf04801c609b01e800,0x104d024111287f83ae1b,0x8419e0ba45842b11500a,0x2108a442b2020f747403,0x52c28293d09b04c72559,0x177cb9c5b22cb1564a7a,0xa671325188cc246012f8,0x1cbce3c6f73629a78d1,0xfc7d73cd1e24eda75c3a,0x5e228110885d420a068f,0x34c98a4ac24f122a8f94,0x558a9d1484a1b4ffa735,0x169cb48590abe95bcac2,0xa5d4ae6170eb765b2ad5,0x5d860c14601af9d7acbb],#[0xd366132c5940c79639b1,0x645aead5969eb4019c8c,0xe0d6fe3781b88db36d13,0x3a7dd1ce6772038bdc3c,0xaf267853bb9da4ec1758,0x3fbdfbcfc27c83dd1e9,0xcd05582240ce04501180,0x76c3721970af84f41de0,0x2a7142898c48221f1098,0x8fdc7aa3871b28cb45ea,0x24ef25b91fc8e643b20c,0x4979cb8a58d2aa9524a2,0x26f53699ac4cc664130,0xfc9fb4f1277d3b89d94e,0x20e8a3440a0cd04e8053,0x4c8a5bd2c694149aa4a5,0xd4e6a3b501a7dd37e9b3,0x355daabd546a97545a9f,0xfd6e2b655acac2d5feaf,0x8b63fb1cd84abd75e5ae,0x55da3ed13683b33d986c,0xe65721b885c2addd6d2b,0xbd1de1eeed765bafdd0e,0x308182fc0f6036fe37ca,0x4c746333161889c36e17,0xd72c9953ca164c722b90,0xe6ce566bb351997cbde5,0x98b48da2ad0ce8233ef9,0xae9d71eb1f541a84d3f6,0x6e1b6d5b59d93ec87621,0x7c65e24f0b77e1bc9dd1,0xe72d795fc9ee3bf1c78d],#[0x2dd10e8574139fdcede6,0xb37583a9fd49e96f473a,0x800705ed57693b3dd82e,0x6f83f02061171a067c1f,0xfc103631c829232723dc,0xe57c282429c8b8df0208,0x17c1cc4f81f048e07f04,0x272be1412178478618eb,0xb816e06181602a1685f8,0x770807857092281f0c0,0x40782b84060203d7080e,0x71e81b030c11020401b8,0x2003c0680cb8d813818e,0x204e0980fbc278191460,0xa013bc1781c0c578d914,0xd784078378cf0b81860,0x4886a0c12063c004e1c,0xa8421a150378009c3026,0x810070341b8403c2c1a0,0x420b7000785048150970,0x9e36840814020784f07,0x83d1416080b45040a805,0x1e0c1301e00a182607a2,0x80c1102f081305039e10,0x8130220304709039e082,0x2c1c088e06423c204c1,0x11037080c050441b8406,0xe061828044f05e070314,0x80ae840c0a81609e33c2,0x278511c0f860680b0406,0x78591c57800502784050,0x80d86f1b23840881001f],#[0x5908a10478009c204cf0,0x8981bc00de101e09e11c,0xc203c13c038b40d81880,0x534208e10102847841b,0x8205007e04e064345030,0x280d2390c080a804080a,0x100088ef080f0740de08,0x81c1c8e0c13041302098,0x1c1684041001e0ba383,0x820a030418442c080826,0xb7080f060245a0815047,0x28260822040802088148,0x980f3c27819145b82040,0x801840580284f1b22840,0x404426060b0305a28205,0x5041382088104f838204,0x6182703c0143e8a0f4,0x8209c1f060f830413822,0xc080b003080b0070bc1,0xf080f07411e08280d239,0x1e78591c4780050288e,0x104e0c0c05e36470810,0x381c1c8e0c1304138383,0x7041101e00e1f4704110,0x90580c1d06082701a160,0x7a28205c1c8a08008b0,0x9a2c8409a3c849061f45,0xa3945d061e8404a2e840,0x212304d141c8e0e8304,0x60a0806d841006d84100,0x6c108036c1080010a182,0x81b8dd142e8a08270403],#[0xc182514104e098028609,0x400000033c2782f00400,0x804000033c2782f00,0x6e0080201052022e306,0x8191c1000010082900d7,0x4000858c10000010340,0x1b610401b61,0xcf09e00600051b24040,0x8c1800006784f0030000,0x40000a4035c00c148089,0xc10005c6390101318e40,0xb007080d016a8a181702,0x40a820001000b005080,0x22042702001a00a1783,0x260d43a83a8a19452881,0xe041383046e305111e10,0x185914188b110204e0e0,0x1091820520212307b198,0x40181052018200db0820,0x1f06082807c1820a0138,0x4080034081a00a100510,0x4e0e04041300e0a6364,0x61208146110ae303a0c1,0xc3011718202231c80814,0xe0060022022144718ed0,0x298558620181c104c615,0x147081380d0b4282f024,0x70420786081823c10c10,0x70405007e85c08234538,0x78018000007b090407b0,0xd706e00603c204033c1,0x1410000000014820a410],#[0x5c6080c0a08009c06859,0x45c608000136120804]]
def g255H8 := limbs80 #[#[0x2004210040040,0x9600030041c4a800fbe0,0x21b00091c00000000001,0x9c0000000000000,0x20200,0x0,0x34a1b100000000000000,0x2f50000000000000000,0x0,0x59c00317000114000000,0x2db80000000000049,0xd3ba079780000,0x526000000000000000,0x0,0xcf00000000258,0x6000000000000000000,0xe24000006,0xc0031a00000000000000,0x45100000055000001b6,0x1a1000000e2c0,0x1d74000,0x24e00000000000000,0x1928000000000000000,0x0,0x76a2a4,0xf0000000c00000000000,0x464006f10000034114,0x3758000,0x80000000000000000000,0x172,0xaad02800a500000,0x190000000000000],#[0x1da00000000000000,0x0,0xf8000000000000000,0x4b8000000,0x0,0x10000000000000000000,0xcb000000000005,0x2d1800000,0x9b20000079700000,0x0,0xebc00000000000000000,0x60000061300000152000,0xd6,0x510000000039b0000000,0x25a00000000000000,0x1a840000000000000,0x12cbc7dd,0x1298000015bc000000,0x1aa98e000002cb000000,0xd3e4340000000000,0xaa800000000001a180,0x19a400412000000000,0x0,0x2ed0000014422b80000,0x134000000000,0x48c00000000000000000,0x711ece00000]]
set_option maxRecDepth 16000 in
def g255D9 := limbs80 #[#[0x5454140ece61d5454140,0xbce69d5454140ecee1d,0x57454140bcee9d545414,0x40d6e65d7454140f4e5d,0x9d545c140f4e5d5545c1,0x140e6e615745c140b6e6,0xe55745c140e6ee15745c,0x5140b6ee95745c140d6e,0xf615755d140e4f61d755,0x5d154e4f5d574e0154e4,0xce5d95454140d4f5d790,0x454140fce6195454140f,0xfce61d5454140fce6995,0x7454140fce69d5454140,0xf6e65d7454140fce695,0x58754140bf6e8d865414,0x40edee958754140bdee9,0x9d545c140fce655545c1,0x140f6e595745c140f6e6,0x655745c140f6e615745c,0xc140f6e695745c140f6e,0xe659745c140f6e619745,0x5c140f6e699745c140f6,0x5e615755c140f6e69175,0x55c140b7ee9d855c140f,0xbeee91955c140e7ee9d8,0x965c140bf6e8d865c140,0xbeee91965c140bf6e8d,0xd7555140fce681755514,0x40be7e8d8655140f4f61,0x958755140beee8196551,0x140ecfe958755140bcfe],#[0xe819755140beee819755,0xd140f6e681755d140dee,0xfe9d855d140f4f615755,0x5d140e6fe9d855d140b6,0xe7e8d865d140beee8195,0x65d140beee81965d140b,0xadfe958759540bede859,0x855d540dee651905d540,0xe5fe95875d540e5f61d,0xd985d540adfe95985d54,0x409fee81985d540a7fe9,0x81985d5409efe91985d5,0x540cefe91985d540cfee,0x696985d540c7fe9d985d,0xd540a7f69e985d540adf,0xe683985d5408ff6a6985,0x615409ef693985d5409f,0xdfe958761540af7e8d86,0x661540c7fe5d8761540a,0xafee819661540c7fe5d7,0x9761540af7e8d9661540,0xcf761f9361940afee81,0x19561d40afee819561d4,0x40afee819661d40aefe9,0x8d9661d40afde859661d,0xd60aefe919661d40af7e,0x69d54e0d60ee75d154e0,0xd60af7e9d54e0d60af7,0x7e9574e0d60e775d574e,0x55160f4f5d57455160af,0xffe9597e11609fee8197,0x55170f6e5d190551708],#[0xf4f6157455170d7e65d9,0x9755170ecf6158455170,0xaefe919855170d7ee81,0xd98551709fee81985517,0x70aef692985517097fe9,0x9f98551709fe68398551,0x170b6fe91855d17097f6,0xe8d865d170b7ee81955d,0xd170b6fe91865d170b77,0xde85965d170b7ee81965,0x60154af7e8d8661170b7,0x6fe5d7460154f4f5d574,0x5d154c7fe5d8760154d,0xbcfe95905d154f4f5d59,0x755d154f4f619755d154,0x4b6fe9d865d154f4f659,0x5965d154bede85965d15,0x54c7fe5d8761954bcfe9,0x859661d54aefe919061d,0xd54aefe919661d54afde,0xe9d95e0164af768f9661,0x15648ffe9597e01648ff,0xfe8195e1d648ffe8197e,0x60174d5fe5575601748f,0x7de85865d574afde8586,0x661574b5fe95865d574b,0x8ffe9594e0176afde858,0x95e11768ffe9590e1176,0xfee61974541408ffe81,0x97454140fee659745414,0x40fee6a57454140fee69,0x1d8654140bfeea176541],#[0x140dfe65d8654140efe6,0x6998754140dfee5d8654,0xc140efee998754140efe,0xe659545c140fee619545,0x5c140fee699545c140fe,0xfeea1655c140fee6a554,0x55c140bfeea5655c140b,0xf7e659755c140f7e6197,0x755c140f7e699755c140,0xefe619855c140f7e6a1,0x9855c140efe659855c14,0x40efee99855c140efe69,0x59955c140efe65b855c1,0x140dfe61b955c140dfe6,0x6197555140bfee95965c,0x5140fcf6597555140fcf,0xf6a17555140fcf699755,0x55140befea17655140fc,0xef61d8655140befea576,0x655140def65d8655140e,0xeef61d9655140defe5d8,0x9655140eefe1d9655140,0xbefe9d9655140def65d,0x98755140eef699875514,0x40def6999755140eefe9,0xa1655d140defe9997551,0x140befea5655d140befe,0x659755d140f6f619755d,0xd140f6f699755d140f6f,0xf619855d140f6f6a1755,0x5d140eef659855d140ee,0xefe99855d140eef69985],#[0x55d140eef65b855d140e,0xdef61b955d140def6599,0x8759540befe95965d140,0xcffe618759540bdfe95,0x58759540edfe95875954,0x409ff6a39759540cffaa,0x15905d5409ff69f98595,0x540dfe659905d540fde6,0x615945d540f7e61d905d,0xd540def659945d540fcf,0xf619855d540f6f61d945,0x5d540bf7e8d865d540ed,0xff661865d540e7f61d86,0x65d540cffe61865d540c,0xe7f61d965d540bfbe899,0x965d540cff661965d540,0xe7f699875d540cffa61,0x5985d540e7fe99875d54,0x40e7fe9d985d540edfe9,0x91985d540dfee81985d5,0x540cff699985d540defe,0xe5d7661540cffe99985d,0x1540affea17661540d7f,0xee819661540cffe5d866,0x61540bfee819761540bf,0x7fe5d7661540befe9197,0x661540affea57661540e,0xcffe5d9661540cff65d9,0x9661540affe9d9661540,0xaff69f9661540cff65f,0x19761540efee81976154,0x40cff69b9761540eefe9],#[0xa3955d940cff69997e15,0x9409ff697985d9409ff6,0xe819561d40affe958761,0x1d40befe919561d40bfe,0xde859661d40bfee81966,0x61d40befe919661d40bf,0xefe919561d40efee8195,0x561d40cff6599561d40e,0xe7fe9d9561d40cffe599,0x9561d40cff65b9561d40,0xaffe959661d40cff69b,0x995e1d40aff6979661d4,0x60ef769d54e0d60cff69,0x617455160ef769574e0d,0x160eefaa17455160eefa,0xe819755160aff6a78755,0x5160cffa619755160bfe,0xfaa19755160dfee81975,0x5d160aff69e9855160cf,0xff6a7855d160e7fa6175,0x55d160bfee81955d160a,0xaff696985d160cffa619,0x9055170fee6119055170,0xf6f6197455170dfe659,0x97455170f6f659745517,0x70f6f6617455170f6f69,0x5d8455170eef61984551,0x170bf7e8d8655170f6f6,0x6618655170d7f65d8655,0x5170cffe618655170cff,0xf6619655170d7f65d965,0x55170cffa619655170cf],#[0x7fe999755170d7f69997,0x855170eefe919855170d,0xd7fe9d9855170dfee819,0x7559170d7fe617559170,0xbefe918559170d7faa5,0x39559170cffe61855917,0x709ff69798591709ff6a,0x5b855d170e7f619855d1,0x170d7f659955d170e7f6,0xe95865d170d7f61b955d,0x1170b7fe95965d170b7f,0xfe9d9561170bfee81956,0x61170cff61b9561170b7,0xfee819661170affe9586,0x661170bfde859661170b,0xcff69995e1170bf7e8d9,0x74601549ff6979461970,0x4d7fe5d7660154eef619,0xd8660154affea1766015,0x54affe9d8660154cffe5,0x919760154bf7e8d96601,0x154eef69974e0154befe,0x659905d154cff69997e0,0xd154def61b905d154def,0xfe81965d154befe81865,0x5d9549ff6a3905d954be,0xff61f90619549ff68398,0x7619549ff69f9061954c,0x9ff6839761954affe818,0x9661d54befe919061d54,0x4befe919661d54bfde85,0x99061d54eefe919061d5],#[0x54cffe599061d54cff65,0x5b9061d54e7fe9d9061d,0xd54cff69b9061d54cff6,0x6839661d54affe819661,0x164cff69990e1d54aff,0xfe91905d564cff6a575e,0x5d564cffa61905d564be,0x7f6197560174aff68298,0x560174befe919560174e,0xcff61b9560174b7fe9d9,0x9660174affe958660174,0x4bf7e8d9660174bfde85,0x975e0174befe91966017,0x74cff69995e0174e7f69,0x919061574b7fe81865d5,0x574b7fe9d9061574befe,0xe818661574cff61b9061,0x1574bfde859661574aff,0xfe919661574bfbe89966,0xe1574b7fe9d9661574be,0xff6979061974cff69990,0x3a00009ff68395619749,0xa401090194027c03280,0x8094411301fb03820608,0x9906b40ca817d02bb04f,0x247045908480fbc1dd03,0x156c293050509be130c,0x8f0cdc18e430205cf0b2,0x3c487630e5c1be436206,0x420f440e07fb0fa01ea8,0x3a123223cc46688a710e,0x50889eb136c26044b009],#[0x2b145520a8314b028c8,0xdb176a2e3c5b70b2f15e,0x6450c691890309c6008b,0x435346938d0119a232ac,0x5e1c3e37e46e70da81b0,0x7958f0a1dc83af87420e,0xe40d07fd0fc51f483d80,0x40223e43d085a908a20b,0x924922823d246d08ba91,0x4c0897092bb252a49bc,0xe127804e7c9ba134e265,0xa5e949728e250f0a0113,0x256a0ac1154d2a3053c8,0x8c2cd658d8b0815ea2b9,0xb9897102dde5b38b5696,0x5fbcbe217a32f045d5c,0x8830ec6190c291831302,0xc7b18df319a62ecc5498,0x26540ca19931323e6448,0xd53386669ccca998332e,0xd1f1a31342a680ccf899,0xc6a88d481a7e34d86954,0x27362a6c0cd789ad0357,0xdbb9b6536b06d2cd9c9b,0x46f80de71bb737546e38,0x7438a670f0e0d9c0437e,0xe699cc139687260e431c,0x874c8e901d0e39f873a8,0xa33b2275fceb41d563a8,0xefe9deb3bb2771ceda9d,0x7998f279e383c4c7850,0xdc3d947af4f509e8a3cf],#[0xf9d9f2e3e247c00f771e,0xc7e90fc91f7b3ebe7d34,0x1f40107fc4fed1fc83f6,0x352058409680f9013a0,0x8838906820b4413a822d,0x58429684f9093a10b41e,0xde21a5431285f10ba21,0xa890d113a20643d4874d,0xb945448a4113ca26744a,0x18ea30645e88b89165a2,0x88dc91ada353468c8cbd,0x647ca8f611e323a5470,0x22b2449488290bd20ea4,0xe92d5251a49148fe91a1,0x174a1493e1275a4d9498,0x2ca25784ac29515294a5,0xe97e12ee25ca4b709699,0x914cf4997931ea6264c1,0x37fa6e34d989ae935426,0x69df13b2a7494e5a9c6d,0xf74fc09f253dba7a54f2,0x43a2858508ca0a9409a7,0x4a339460a8b45130a22d,0x58528ca4bd48c290151d,0x4e0a9af5326a5f14b529,0xea9215112a0653dea74d,0xcd5576aaa554baa7b54b,0x5acab425638ac01574aa,0xc1f03c22eba85718adc1,0xe249118340cf19c7917,0xa0df19c7033c1f03c222,0x33c671f03f07c0f08b83],#[0xf07c0f08803a0d248538,0x1f03c2320d833c671c0e,0xca13032490df1853833c,0xc6d1684f07c0f08c0340,0x3c22c920460c43453c0f,0x3034448ef1853833c1f0,0x1ac5c0fc1f03c2300ea1,0xf08b049118308e14e84f,0x2390d033c691dc5f07c0,0x67140cf07c0f08884a11,0xc5047c1f03c22212847c,0x412f07c0f08884a0cf19,0x17c1f03c23211833c671,0x4c128390c24704f1b839,0xc13c6e0e47f07c0f08c1,0x1f03c224538480e4308d,0xc2249324811f1b4303bc,0x134380df1ac304bc1f03,0xa8471f03f07c0f09c831,0x1c807c60380d0320571,0xf03c2039c829c2917c1f,0x2030a71dc61408fc0fc1,0x824911f19c7f0645f03c,0xc671fc1c0fc0f080e29c,0xfc1f03c2248a7205324b,0x90d28134360cf180ec0,0x4c92833c604684f07c0f,0x5f087b1bc1f020c07050,0xc0f08643611b1fc1f014,0x7c0f09112a11833c1517,0x38a04c8e833c603684f0,0x460cf1812c0fc1f03c22],#[0x71684f07c0f09c830134,0x2030a048110320771b03,0x82390df19c5f0647f03c,0xc6717c1a13c0f081129c,0x703f03c2048a72053437,0x201f19c814c8ef19c5f0,0xf0811720a70a47f07c07,0x829c67151915284f07c0,0x51508fc0fc1f0bc0049c,0x12c0fc1f03c214ca719c,0x7c0f090c2a110390cf18,0x8714e1103bc603647f0,0xf08683784f0511f02c5f,0x613c21e0d833c151fc0,0xc1f020c210c836c5f07c,0x61106c6c44c8b1b47327,0x33c1f002618c8b1bc0f0,0xc13c1f03c214ca060c84,0xf090c28118390cf180d,0x714c1183bc604a45f07c,0x87c3ac6327c1f0345830,0x8703cc8433c1f03c208,0xf08643a12b1fc1f0145f,0x60fc21e12833c1517c0,0x83f03c2190c84ac7f07c,0x3c1f03c214ca84a0ef05,0x90c2a120350cf1811c1,0x4e12037c603a47f07c0f,0x83b83f07c044ac5f0871,0xc21e0e833c151fc0f086,0x20c210c83ac5f07c060f,0x9c6c48c8b1b47327c1f0],#[0xf0a12180f3210cf07c20,0x1f03c2d208c3383f04ca,0xc1f03c232c7e1383d1bc,0x1143a0d04f4761345a0f,0x147e0e45f07c0f08c44a,0x3c219124460e8340ce1,0xf03c214c784a11f0545f,0x1f03c214c751784e0fc1,0xc1f03c2230751f84e0fc,0x7c1f03c2230760f47d17,0x1784f07c0f08661347d1,0xd1f45e0fc1f03c21b47d,0xc21b45e1383f07c0f086,0x7c0f087e1383517c1f03,0x7c0f08951f84e0fc1d1,0xf087d1c250900801b45f,0xf087d1f4560fc1e13c0,0xc1f00ad1f45613c1e0fc,0xec340bd1f453260cb1b,0xc1d4390df07c0b1fc21f,0x202324891f07c0d17c21,0xd1784e0ec6f07c0f0ac8,0xc4350c323c1f03c20887,0xc7d1784e0ec6327c1f00,0xfc1f03c21f0ec370c70b,0x3346f07c02c1d4350cb1,0x1d926440b71dc5922494,0x21c234450cb17c1f03c2,0x2718234490cb17c1f03c,0x4caf08a4450c323c1f08,0x712c470cd1fc5e1383f0,0x1784e0cc8326c6f07c03],#[0xf00261b12c470c70b47f,0x71fc1b14a4490c323c1,0xc12cd233b08e18c4e0fc,0xce02c09b16c4e1b83f03,0xf86e0fc0f04ce20d3348,0xfc0f05c5b108025c702,0xe0fc0f04d220d3348c7e,0x1f03c2e20c02c09e19c5,0x30480e11f8651644e0fc,0x45d1386f07c0f0b88201,0xbc105bc0e0fc2b1c6b1f,0x37c603187f07c0f084e2,0xd1283f07c0f08c448910,0x1291344a0d8300ed1587,0xe037c604e44f07c0f089,0x45e0e44f07c0f08c8484,0x3c219138490d83011e1d,0x3c2138784e12f0583f0,0xf03c2244751387e0fc1f,0x1f03c2244760f45d13c1,0xc1d17c0f08761f45d13c,0x183f07c0f086e1d44e0f,0x1744e0fc1f03c21f45d1,0x84ec5f07c0513c21d87d,0x3d13c1447c0b17c21d12,0xc8b18c9f0344f0611221,0x81432112f07c00986c48,0x8486050c8447c1f08271,0x6f03c12f11e0fc132bc2,0x2c300bd1345324c8846c,0xc6d0fc131fc0f080e2b1,0x7c024b43f087d210d833],#[0x4bc1f0343f08783385f0,0xf0585f03c2048a094932,0xeb0fc21ec81460cf1ac3,0xc2039c82a0cd1fc1f010,0xa719c32410f91fc1f03,0xc5443e85f07c2f001272,0x2112f07c0f08221dc670,0xc3b85f04caf0a12180f3,0x221c0f3210ef07c209c6,0x3c21c9324948f07c0f08,0x8ca28254490eb0fc1f0,0x4f12c3b47e1784f0fc1f,0x51912438c8f03c20a06c,0x15f086f0dc2b1bc0f042,0x384f0ac71ac5e13c1f00,0x5fc0e13c2b1c6f0415f0,0xb1784f07c006bc21bc10,0x884784f07c024f43f087,0x11c3343d1612f07c2328,0x9c6c4f45f04caf0a121b,0xf08ca201432113f07c20,0x2b106c4f0ed174384bc1,0x87f0ac31bc1057c0e1fc,0xbc0e1fc2b146f0416f03,0x708200e0d7081f0fc105,0x308d0d188f700270d19,0x7c305416d14307413a13,0x20784866c203c3b09450,0x2707dc270345141c866c,0x983839c207c371b4508,0x308c8e188f0882465c2,0x10305447058307413a13],#[0x56105465c2078306815e,0xc5151c10a0306014708c,0xa4707c303a47c0c2408,0x107dc2d1c5465c205037,0x9197081b11c6d1c20882,0x7081e0dc231684610409,0xf7081e0c18314260d19,0x4280c1003e0c31d8315,0x7411917040950c18507,0xc305817e0c305815d143,0x78383ec20603b094507,0xc383c220a0f040283ec2,0x140fb1845088431e8360,0x471b45082607dc270345,0xdc670b830c28705c0e0c,0xe101606b830c16057470,0xc700c560c643dc67081,0x306151c670428101403e,0x91c1f0c2303647c10254,0xc670b47150f700140dc2,0x3dc009c371b47082007d,0xf7081e0dc03168360c44,0xf48e0f460c0f314270d0,0x50f48017460c08916c70,0x5c71022e0c200c0851b4,0xa0351c0d230305b8305,0xe230304545a103a11c1,0x14122303a0dc10a0351c,0x7d1783830491dc207835,0x2c2022c60d45b081e0f4,0xe138384c4e0ec2022c61,0xc1022c60c54b04100f45],#[0x9c0d145d16c1022c612,0x5091450dc6d142079c67,0xc23075830c25091450c2,0x709c1701c61423075830,0x43b2383b183021c60808,0x5046916c2b20502247d1,0xd0750c0d0d122c643040,0xec801ec60d0e0750c0d0,0x22c231ec61008b1cc60,0x20079c7101431ac2b204,0x81d021c7b1840501088,0xc2721c60c1db1c2076c7,0x9830781b021c2701c619,0x81416e0c15714409f830,0x1108d0c0c1091c46d0b4,0x4448b190c111208d0c0d,0x64304c4b11c3383d1c54,0x423b14208ec50912122c,0x508100408709c031ac51,0x84040c6709c0720508ec,0x9c26079c511c2701c871,0x8709c61423022c671440,0xd233b08e19c7181e06c0,0x1c334cd233ac4714534c,0x407830581ad14305817b,0xec70f88d1382e1840834,0xe0c3e2003e0b861008a0,0xc50c17d101671c402186,0xb861026d101e0c1a05a,0x6714402283b143e2344e,0x98408810304e081ad101,0x3184f718220c94719c20],#[0x2313860500f839c05158,0xa45708260c2503687910,0x12345d12c684460484e0,0x8b183252c6b08181088,0xb1820881b0808b183b08,0xc1703831344022c60c08,0x941d5103719c2e0c3089,0x30902370030902370030,0x1820690305c306815b14,0x309c1e0808912c50f48d,0x9c231644510506815714,0x60c40891481183700531,0x451c6511c215c031683,0xc14314270c14314260c2,0x8151208d110d0c08d110,0xc631426101011944709c,0x3344110c122c64444038,0xc470c122c6d106c4b11c,0xc41026021c2705c61712,0xd4691cc750c40a020c46,0x8100891f430ec8e12c60,0xc62148408850504690ec,0x383c3b0dc3384d0c5044,0x988f81d8570054301d4,0x8530c408808705c07185,0x8830810f51e0511c0a15,0x409c303cc309c303cc30,0xc221017e101670c40a38,0xa38409f0eb0c50464690,0xec3ac7141891c46d2040,0x34715120950e0c20e101,0x4848b190e1313c4b0ee1],#[0x8705c031ac31425b0c24,0x1c81425b0c2061c2080,0x705c0721c61018319c17,0x8b19c3102809c2270c4,0x14220c22021c27184094,0x8a12c30f88d17860c27b,0x4c550c506b4505dc3100,0x4483430234483519c091,0x40404650dc0720544423,0x70ce1343140d318c509c,0x470c122c6e13431f12c4,0x4704543048b19121312c,0x8705c07185080948158,0x38254483050c309c309c,0x6515c0720544c2544834,0x345140d318c309c40604,0x22c6e13451f13c4b0ee1,0x43848b19121313c4b0e1,0xc2701c61513122c64484,0x428e1022c4ac31427021,0x26e101ec4ac51]]
set_option maxRecDepth 16000 in
def g255H9 := limbs80 #[#[0x20020481c080919d081,0x90c50002c31821000,0x14009f0401c110000528,0x18b00e0460082c52e1,0x808200a0c50090400020,0x10134f1c72431c908f15,0x462406c3049292406a00,0x387e1423df0cf0411c00,0x510000469703202ec3f,0x1184000fba4,0x12b7ceaa3dc00000000,0xf29ece0000000023e000,0x606506e000371c,0xb18c2000000053b7ce30,0x40000000493d9c800028,0x7382516749089086812,0xf389ad0dea360c4e0001,0xb2ec000b4b00e289890,0x22e5c6b48ee806cc0400,0xc41e0c68720557c7c4ab,0xdcc54796f07263fea0a7,0x307f0000000893e91211,0x8a6c2c00000002131000,0x212074000b05e1190003,0x790b108fd463c9a0001e,0xf028000d3c448,0x9b2808c1b0000d95f079,0x8b2a1c50eea080000d,0xc000a8be09900004aa00,0x527228c0000003c95245,0x900000000b0380000000,0x24aba8603da52d00028],#[0x91e518e011000000,0x332513d36400062764d2,0xf31d0cde00c0004,0x22f033e8c98549800000,0x84699b444f9ad324a000,0x93160f9eb7945881b4,0x5b74000e0a5ee30ac40,0x150c69db1011c9000,0x2e8700014760000c59,0x26e7500000009101f180,0x14525b0d88c98,0xb9951df22609c535,0x9000000000000000000,0xf0000a279a9f70074471,0x58ac0008878000a1780a,0x1900a2534c000032483d,0x8,0x38835090000000000000,0x10300008ac00020be000,0xc00008e40003e0eaa14,0x2127e841013000032d3f,0x1a800022f0000000065,0x20aea0370fd,0x44000626ce0622280000,0xc856386000051bc00003,0x312f947,0x4b16c400307890512cc,0x384a0000cb700019,0x6a5800,0x3cc400000005214e4c,0x700009a616c6000323d0,0x2c8820e94e1822fc3c74],#[0x828e0af22a0000000000,0xd6000183000017152111,0x5060000000000050c74,0x930322d78f0000f12000,0x1f70059c94000498c000,0x391aa248000d2028bf5,0xf4e6315d63811c000000,0xd0d530400963f80a4b3e,0x2f5be4000943dce90003,0x2a40027c21a000018b80,0x6aac000a42a86043ca81,0x3a16948800099e200b,0xdc75320400000000000,0xdc9600034f450e00004a,0x6b084548e85c8e0a0187,0xce64a20dd005968808e4,0x21f304d39e8000697d8,0x30effbe18b6c48000,0x19a8ca7aca4d70001125,0x878b544b8000305542ac,0x50b40000000000a4,0x32e3d4421741de0b000,0x207354474000151b0001,0x7600547be12d6f668752,0x7c7bac59237a9258c980,0x2ceb91758a8a2c748e,0x68000239c000000130e0,0x51241baa878220bd10c3,0x12b54a40000000c3f886,0xc368d2236b0f9c366439,0x1000005c0001434a197c,0x6168000a25c000000265],#[0x3f443f17f49103c0425,0x1a314285681414080008,0x684500000000000000d4,0xe610042b1d0000000c39,0x60645800000014476941,0xe09e0c800014df6371e,0x10820d0000000000000,0x7132b00018bd00020a1,0x6f6a0b8d400000016ebe,0x40000002291d1e8c3923,0x130000000032e210852a,0x9fa0d400000032e70002,0x300000000003c1f58f8e,0x90ec000c32d00222e905,0x12e58d8cf426a99c000,0x6a467c0cf6b6d04c850e,0xc000b0dfc9e0000000b0,0x542c000206c0006ae,0x84b18b8ecf31b4cfe08c,0x1d23d4504a5d3434]]
set_option maxRecDepth 16000 in
def g255D10 := limbs80 #[#[0xb72e8b8281f395454140,0xdcba2a0a074f5d574553,0xf70ea8281bf98754140f,0xcbaae0a07ee551705037,0x70ab8281bf9855c140ef,0xbaaa8a05fee55705037f,0xeaa281bbd8755140f9e,0xbaa8a05ef65d5450377f,0xaba281dbd755d140bdfc,0xae8a06efe157450377b0,0xbaa819fd875d540bdfca,0xaa04ffe5d855027fb30,0x3a817df93619409fecbf,0x6b04ff657875027ff2ac,0x2c1bdd74e0d60deeaa70,0xb04ff65f845827fb2bc2,0xe1dbd74551709feca70e,0x867fe15745c2bfb2eaa2,0x13fd95e1170affcaae8b,0x6ef5d380552fbf26c32e,0x7bf905d1549fecbf00aa,0xff643875527ff20c3aa9,0xfd97e01649fecaf00b24,0xf65f855927fb21c2ac93,0xd95e1d649fec870eb24f,0x657805d33faebc02e93f,0x91619749fec870aba4ff,0x43845da7fb29c02ed7f7,0x6541409fecaf08bb4ff6,0xd50503ff30ca8281ff97,0x5c140ffcb2ae0a07fe61,0x70503ff32ab8281ff985],#[0x5140ffccb2e0a07fe619,0x4503f7b0caa281fbd765,0x140fdec3aa8a07ef6595,0x503f7acaba281fbd9755,0x40fdecaae8a07ef61574,0x3f7b2cba281fbd865d1,0xdffc3acaa06ff61d655,0x2fff30b2a817ff975954,0xfdeca2eaa07fe6417550,0xbfb0ebaa81f7d855d540,0xfecc2eaa06ff66175503,0xff30baa81bfe985d540b,0xec3b0aa06ff61985502f,0xaecc2a817ff9761540df,0xcb30aa06ff659855037f,0x2ec2a81bfd9761540dff,0xaaeca06ff5db855037ff,0xec32817ff985d940bffc,0xb0ea05ffe55875037fb0,0xc3a81bff9561d40dfeca,0xa8b06ffe59875037fb2c,0xa2c1bff8755160fdeba2,0x8b05ffe5d54582ffb2ea,0x2c1dfd755d160dff4c2a,0xb05ffe55745837ff0aba,0xe1ff99055170dff4c2e8,0x877f65d545c3f7b08aa2,0x17fd9855170dfecc2a8b,0x5ffe61545c37fd30aa2e,0xbff8559170efebaac8b8,0xffe61645c2fff2ab22e1,0xfd955d170efec2ae8b85],#[0xf659745c3bfb0cba2e1d,0xf9561170dfec2b08b877,0xe51865c37fb0cc22e17f,0x8660154fdeba300aa5ff,0x5d805537fb0ec02a9bfd,0x5d154dfebb700aa5ffe,0x974553f7b0cba2a9fbd9,0x5d954bffc82ecaa7ef65,0x86552fff20c32a97ff98,0x1d54bffcbb0caa6ff61d,0x75537fb20c3aa97ff906,0xd54dfecb30eaa6ffe418,0x5937faebc02c9bff9661,0x74dff4c2eab25ffe4175,0xd37fb0ac02e9dfd75601,0x4dfec3300ba5ffe55805,0x2fff20c2ae9dfd865d57,0xbffc830cba6ff619855d,0xffb0eb2a817ff9561974,0xfecb2eaa07ff61975503,0xfaecc2a81ffd985d540f,0xecbb0aa07ff65985503f,0xb2cc3a81ffd9561d40ff,0xcaae8b07ff65d54583ff,0x2caa2e1ffd8655170ffe,0x2ac8b87ff661545c3ffb,0xcc22e1ffd9561170ffec,0x300aa7ff5d980553ffb2,0xc3aa9ffd9760154ffecb,0xeab27ff65987553ffb20,0x2e9ffd9560174ffec82,0xaba7ff641855d3ffb2cc],#[0x4003000300000ffecb30,0x2ee052e08dc0f4818002,0x825e045307e60e941ab8,0xb01a2831085c10ae6142,0x89d108c1f983c787260d,0x852809f91344252c4758,0x122eec5a90af2159029e,0xd981a8233cc6570c5718,0x47938ee21d3a39186f30,0x54414c8028fc01f2c3d4,0x21523a0462c8a3110121,0x4a039395266a4b0c93a9,0x8e5778ac81530298e51e,0x86f2ffa5e2cb9596b92c,0x4d309a01336664bcc631,0xae7194dfe1b9336546b0,0xedb3c787794ecb9d4939,0x5078a07640627efcf9d9,0x2c8ad912fa1ff433e854,0x5084950918d1f8a39146,0xd37426884c62978d2afa,0x2ca2b5426a7e44f1a9cf,0xae45508a8fd4f8a98852,0x9666ac5b57d2ae495992,0x86bbd57462e355b3eb4d,0x16b623ac2f580f2fb55e,0xd9b7b30f655ec9198eeb,0xa6d5cda7c34986870cf3,0x7986e70dba9b4536456b,0xdcedb9727212e2a5c053,0xeeee5dda93afb7548e8e,0xd987aa6f3f1e5bbc5777],#[0x1f9cbee27d28f919eeeb,0xf702da034402c7fe0fe4,0x2788467074e0c7414981,0xc1e0708a86b30c5215ec,0x708a0703607c7e311419,0x204b8dc58184419c1e0,0xa09c6e191c1dc1e0708a,0xd0631e8bc1e0708a0984,0x1f83c0e1514b06f19250,0xc206101186a4819c6c23,0xf0384571a1b4563f0781,0x4483b8d11470328ec5e0,0xf8c53860458b84e0f038,0xe0671b08c5e0f0385472,0x1d8bc1e07081844441a8,0x8462f0781c20891c688d,0x398f83e0f0384571a19,0xfc1e070a8a58338c5386,0x1030809439220ce360d8,0x85832f8d0ea2b1f83c0e,0x4a18530771a8ac7e0f03,0xc68660d8fc1e07081c40,0x14e181262e0f83c0e115,0xd8362f0781c2a3960ce3,0xf03840c22240e468338,0x83c0e10488e344a8ec5e,0xe0f0385452f8d0cc1b17,0x384494c24114671b0983,0xd281147e35170983e0f0,0x145c1e138dc163f03841,0x431f8d45e0f03840c241,0x7c7e2f07804b8610230],#[0xc1f1b82c5e070846551b,0xa8fc1e07081848228f84,0x4c1f07810b243a0862f1,0xf83c08592cec371d8ac,0xc00b08446961b8ac7626,0x158f83e0f0384162383,0x781c22b83c00d07c4c3,0x832c1dc6489382545c1f,0x22122771a8b44e0f0385,0x895118bc1e070822404d,0xa238362f0781c20911c6,0x862f1a89c1e0708224f1,0x1b8bc4e0f0097111c480,0xc64931e87c1e07081c45,0x8218fc6a1f0781c20713,0xd0ec2b0f83c0e1048812,0x26178dc161f0384252b8,0x8d47e0f03840e241147c,0x7f0781c20a8e1d0430f,0x58e0fe0f0384151c0ec5,0x81c20b8fc1e005c3e201,0xe0f00341f1006c707f07,0x910036283f83c0e10687,0x244f1926c5a1f0781c20,0x244a0862f1a87c1e0708,0x230430f8d45e0f038412,0x51f09c5e1f07844a890e,0x82c38158814e0f03841,0xc0e1058702b0c29c1e07,0xf0385846414036285383,0xc80f90c686c318f45e0,0x15141860661ac2a2f078],#[0x3868459092e331f83c0e,0x318b47e0f03858464142,0xc5e0f0385470618c688c,0x610226076220d6423b8c,0x860359053e331783c0e1,0x622c2a3f0780c80f9024,0x52a7078184e132022586,0x781c2c1b20a0cc318cc,0xc06407c86343a18c7a2f,0xf09900e2c1f0e6151783,0x8603e18c76314383c0c1,0x99091e331f83c0e15141,0x7e0f0385830718238704,0xd90509618126414f8cc,0x631a250c62d1f83c0e16,0x908de331783c0e151c18,0xe0f03858309181d89039,0x3e4896180e6414f8cc5,0x22e240f6330a8fc1e032,0x8c66295383c2c1f01901,0x651a8bc1e070a90703e1,0x18408d24c7c204306914,0x28141063d1783c0e1521,0xc2406b08c7c1f0781c2,0xe0c91c7e0f0384504614,0x20de0f0385842996160a,0x70b06532c488ce35142,0x18589519c6a28481dc1e,0x4f8d830703783c0e151d,0x1208f0781c2a2a30b0e9,0xf0781c229982329f1b06,0x860944945462238d84c1],#[0xca648e351e8bc1e07091,0x6e0f0384534610230ee0,0x1b83c0e1230a642228bc,0xc2a3f0780c80f9248c1f,0x31f83c0e15151874368a,0x48c3a1b83a43228cc606,0xb83c0e131c3a508c3a92,0x1e0709907038918306f1,0xd45c2053070d863198fc,0x18843fc1e03238460761,0x83c20e8f0ea2e138ec6c,0x63f0781c23411c763703,0xe86c303ac8a2e1307c6,0x83191c6e0f0384c70e95,0xac7e0f0384c886100e06,0x231707c1e0708a850528,0x83c0e11511850309017c,0xe05203e48582b8324717,0x98a2329249163d098bc1,0x2342448c18478dc1e070,0x6c8a3e1307c662f0781c,0xf0384c511951288c304,0x81c26418120883191c6e,0x4a23476371709830ff07,0xa047158dc1e0708463c,0x1489d8363f0781c2a2e2,0x1aa2b1e89c1e02649c3,0x761b07c1e070b1070391,0x9c4094a6c7a286288522,0x4c921863e0f83c0e1620,0xa0b85a8888e3f07804e,0x14ca58362f0781c2a262],#[0x17a3b1689c1e02649c3,0x2e0f83c0e1620a440491,0x8888e2f0780524c92186,0x67078187e1138b0d05a,0x3854548941d48f1a880d,0x227162327718240ce0f0,0xa91e35102612e0f0307c,0x471b0f83e0f03844e304,0x83c0e1244b1287688914,0x4890241193891c6a2d13,0x49c3a2289c6e0f03844e,0x262d20a2471b83c0e124,0x448a324d2344c1f0781c,0x4f281ec5a270781c2a42,0x22480be1d8b83e0f0384,0xa9238bc1e07089e9124,0x78cc5e0f03854408981a,0xe160c24609224136423,0x6258884d904ee331783c,0x331533c1e051384c8089,0x83c2c1f0190122c29126,0xe070a88805222c66293f,0x8d865219146630458bc1,0xf0384c511922411a4e24,0x3c0e1320b0912019c6e0,0x31112863168ac608d138,0x1c60609014e2f0780c41,0x32910de350f83c0e131c,0xea1f0781c264161d490,0xf038543461b0c63d1d8c,0x8661290c8a33181cc7e0,0x384c70e94250ea4d250d],#[0x887100d2461019c6e0f0,0x1424605286c7e0f0384c,0x70319051e330f83c0e16,0x21c1e051f84c80716238,0xc2f0190122e240f6330d,0x8a8503e1cc66195383c2,0x389015c2b0f09c1e070,0xd842470f83c0e11511c5,0x7f1f83c061f0844505c2,0x8dc1e070a90584091840,0xe1088a49a4a86c36383a,0x4a08123080fe1f0780c7,0x9230812e370781c26189,0xf85c271987c1e0708d09,0x130c4a544e250e12b228,0x90604c240e6471b83c0e,0x3a8f85c270d8dc1e1701,0xc36370781c2128f13894,0xb1e87c162f03850f2811,0x9c1e070b10532027080a,0x1f0781c24794ca07b0f0,0x81c262848c0d05e8a88e,0x44469308d2219c6a1f07,0xc8a331824c5e0f038543,0x942511a4e228e8661290,0x2461019c6e0f0384c511,0x58c12a1f0785c0641611,0x2a2f0190122e230c62d1,0xc4a505226c661a3f83c,0x584c91840771b83c0e13,0x87436304a8bc1e170190,0x7f1783c26189c989c39],#[0xf87c1e13144e48509184,0x348a30a1481c2848c203,0xd84c6a29203c524a8d8,0xc6c1a205052651e88a3e,0x94d185150a048a2e1182,0x389448230ed1f0945c1,0x608498731b070d861519,0xa63878370e2431b06c28,0x8614c711c3a1b830ec30,0x9810c2a161d894470623,0x8203c1b8944490c6c1b0,0x20829e1a898229139338,0x2624a786a26089c524ce,0x12994a2228ac26351090,0x2813c9187a260d8c8811,0x461dc3d17074448938a,0x649d191a9127d2061289,0x8887c81244a182388938,0x8a8c81c4d122431984c0,0x210c383e44358d848643,0x103b0e288e222431b08c,0x12c20961c511c4b0d866,0x31b08c160438a8507627,0xa4d29a3f10388a271224,0x8c33082389134728e1a8,0x90c6c230981120f92258,0x89c3b082589134713c44,0x890c6c23058112281423,0x2789c3]]
set_option maxRecDepth 16000 in
def g255H10 := limbs80 #[#[0x500020200010c062c0b,0x7001205060000000114,0x200000e022a09000612,0x53211010f0009010c08,0x1030a000404001004,0x241e080a050801050e05,0x142512100500062c2103,0x1021a52072601033a01,0x8373414040700022708,0x8020b46070000003201,0x312000102322f1b0400,0x1d0c1f079a3a0109430b,0x1e211c85000149580d51,0x2338000d2d800033b760,0xa9c000753e332000331b,0x30000c2af862331cd524,0x8000d20e9470000000fd,0x8cbe438000e0eee7ff1d,0xdaf3700004204000e08f,0x1bafc0001344000a032a,0x70bb403e24eab3235f12,0x3f000229a71e6347,0xa1e1c0000c2cd8f04a40,0x3104000373674f0000a3,0x3c71440ea0245356000,0x47455b6749aa7d53d3d3,0xbb5280002482457b8ce0,0xe0458001580c5bb58e8b,0x30191fb42454b000095f,0x15401e502115436aef44,0x34e4e8c50465052c8263,0x87b7324000e2ea833000],#[0x5d72298b1d473c131021,0x8c39cd7884c80a0f88f4,0x42f60e16a7c169121f92,0x34ad013127975f986964,0xee206228f8bcb9e78262,0xdf1d3a6dc7ce341488bc,0x81d8440000bb0a4d6cb4,0x72b550a94a7c6be932,0xa807aa0ca36461100000,0x1a53934e16400014c771,0x3da51273ae440000304c,0x35f2963fd4a9c28b8c68,0x5ad0948c000000184335,0x26c5350000d0ac08e9a6,0x1e8a00000a434000c463,0x2581429572aa49ad3def,0x586cc3a349a607e85bce,0x3f70bea158cc485634f0,0x8222741a402775c51723,0x3c5a1506232a5a1c688a,0xa54a199d39217c961000,0x1bd556080aae66698242,0x1ed500000000154b0698,0x8aaf4f57012cecab6cc7,0xaa266e4cc000c12ca91,0x85143802c000234f8db2,0x96e382345c714dd25f0,0x1069008d576226cb7000,0xfa4ffc155420d3b0180,0xc130c041f0c702404b8e,0xa5bc0fa0000000d4006b,0x42d92b1d5d1799080c8f],#[0xbf2276e44007c0006,0x2eaf91aa6b50001d7300,0x26ed11354884c0149c32,0x77000300e65ad08d2a3d,0x708a78cca37989675084,0x24f1000109be0a351,0x1d0fc4dc000000014e,0x940000000ca629c88090,0xa43794e8000b98c25945,0x42b98e341e800073b,0x9960a40000000000b5d8,0xe151e1ae0d9c2500028,0xa7ea4f847f515400,0x3ef8fc31e2807051bc73,0xb8f6c000000032b00007,0x6c303d044228c7d6c4fc,0x7e62d00004260058c30,0x240bd1450000cf90001,0x291964fe000000072cd5,0x246de13c00090c9c4,0x21ad0c0002d27b138000,0x16eb654da95a439acb90,0x45700000000848947d84,0x905b14c440d045328,0x39946d4cd71c246473a4,0x4303c92d000006cb375c,0x927d4b80000000601687,0x56ed6643e280ac857c92,0x3676e512c6358ba48b4,0xe83dc1499778c2c00000,0x713c544812b59f1163b0,0x59ec60000000086fa0f9],#[0x7ea410c2a2d4c9ea4929,0x3035d2a42312926065ca,0x1d5b559270000c2bc162,0x46d3da17a11e41c88d8b,0x7213414144db01b55094,0xc480002913000303440b,0x3c180000,0xcaebd2c125000052a00,0x94d64b200008b0e57400,0x2e9d2452ce5bab0000,0x780009801a7a00014f20,0xeadcb073061e0e023685,0x174841f52fe3b,0x1000010df75b0f61e380,0xf84e0000d5738d553cd0,0x512a067025c11900034c,0x1cca61b8000b8ac8a5,0xa80000003c1700000000,0x75b691ae5]]
def g255D11 := limbs80 #[#[0x5c140ff950502f7e0d60,0x503ef5d140fbd54503fe,0xbfd87502ffe1540bfd85,0xe1d60bff84582ffe1d40,0x552ffe1170dfd745c2ff,0xbfd87553ef5d154bff80,0xe1564bff80592ffe1d54,0x5d2ffe0174bff87592ff,0xbff805daffe1574dfd75,0x5d540ffd65502ffe1176,0x503ff5d940ffd85503ff,0xffd54583ff61d40ffd86,0x59170ffd545c3ff5d160,0x553ff61970ffd845c3ff,0xffd86553ff5d954ffd80,0x60174ffd75593ff61d54,0x3ff61974ffd855d3ff,0xa87905f84c0388250118,0xf98e80d48c50b58a408,0x7e16c95b14993811e90b,0xe9f11d79c61b49a318f9,0x2a5a8c272a59241a2820,0x5233ab21307af22daac3,0xc1c00b23b639cb8336bb,0x707030a109c786c5c483,0x7c1c0c2842434331f191,0x1707030a0c9110cc6c54,0x47c1c0c2832438331f19,0x6120f070308c120cc6c5,0xc20c20383430231f191,0xf070308c08c7c645c1c,0xc20484430231b151e12],#[0x70064708c6c547c1c0c2,0x447c1c0191c231f15130,0x1b160f07030910908c5c,0xc6c544c1c0c211204847,0x4231f190f07030838808,0xc120ec6c347c1c0c2852,0x38231b0d1e1613070308,0xc6c347c1c0c20e204c48,0x231f150f0703083c808,0x3c808c7c345c1c0c20f2,0xc2122023170d1f070308,0x7030a10908c6c543c1c0,0x1c0c212204c4b1b0d170,0xf07030850808c6c345c,0xc344c1c2c01420231711,0xe120d1707030920c08c5,0x5c183c0c2384230311b1,0xc0c538848138cc647844,0x3835231f191707030830,0x848347c1c0c248320c74,0x52307007cb148c0c46c5,0xc20c30643e0d0b1d1b1,0xc8323121148c6c547c1c,0x3a1b1d15120f07030a20,0x474483c1c0c288306538,0xf05130308e19521286c5,0xc3a462120453b1a1d160,0xf46c5878344c1c0c2482,0x231b151307030844b910,0xc4c1c0c24811288c4831,0x90f07030838c191446c5,0xc2483210743431231f1],#[0xb148e0e46c3858447c1c,0x3e131d1b0f0703092038,0x48c6c347c1c0c20e3040,0x61307030a20b84251312,0x1c0c212314c3e1b0d1d1,0x48c8423110c48c6c543c,0x944c39231b0d17070308,0x46c5c3c1c2c048122e10,0x140f84]]
def g255H11 := limbs80 #[#[0x2818d0200003080c39b,0x818e121411b0c002060,0xc90c0800f0c18d8a00,0x18030047b502d4283006,0x1061888f0e009042200,0x8fb5a00a98360001e200,0x17a39e2f00000000016,0xe58d4e800000183f4575,0xad280000000000000000,0x2a600020b2000781,0x3a87422000000000000,0x2876220e2200a779800,0xc4800000000061bd2331,0x80800088f800000033ff,0x93e800000170771c0ae3,0x7d4ef3d7bc09310ee13a,0x665d1a0a8a3c1dc018aa,0x6412fd44c4964d50abf9,0x712898b4f323b0003a,0x87c0c0000000292d1120,0x675c48000242c00043e3,0x360800052382adadb,0x403311a40b0000009a56,0x210c6495706a3d0002a4,0x38000000460868449361,0x57b5de0ba415313e01d9,0xcade8e0000000000000e,0x3915cf122b8458003,0xaa28a0248800004b8eb3,0xfc0a568ece925e0afc53,0xb98dd400e1c96bd28190,0x7f79cfaaa84666561ed8],#[0xc0c3361e8380607528c,0x339584d56b30b0007,0x8003efa000f2180014d8,0x38b11c199ed089410a0b,0x962000a909600069a000,0x4d50c00042b400000011,0x2fb8a0000000816ee72d,0x825e0ab45616d6f6000b,0xac9150000000243b,0xcf6f320000593f2a5a0d,0xc000000000183c000320,0xc440c83e682e2ec852e1,0x676358000536000a059d,0x90b9440005280000148b,0xb3b00069a80000000003,0x3a56881857207eae593c,0x7467430ea69931b26c50,0x2800050a84df2480018c,0xfd45137e96800147155,0x121a88c29f00000035,0x84c20c00071b78fdc200,0xf33000366200055b9120,0xb81000030c7ac086aa69,0x2b48da36d6c000d0d58e,0x2ce64a3442399244382,0xaa07000000000000000,0x8d88a4000ea7e939e237,0x7]]
def g255D12 := limbs80 #[#[0x4ffaa9ff5c3feb07fd40,0x4893001ff5dbfeba7fd6,0xa101c18108add5ba52dd,0x880e0c08420910323c68,0x68b1038383021151c345,0x478d0c2848302114208c,0x3868b0c2418108412207,0x44128d1618709060422a,0x68b1218783021082]]
def g255H12 := limbs80 #[#[0x240088033f144312007,0xe7048481668ea3544226,0xc490f52022cb0b3374f9,0x23e1400040660400659c,0x1b1800440b3800199c84,0x5aa77291244ad1c32203,0x9f1a12c02ba5927a1cc,0xe52e28007dc70191c909,0xfc74ad00000026144716,0x124bc2a00121bd3000f3,0x9b1c0e8c0062b0010]]
def g255D13 (j : Nat) := if j=0 then 0x7185103040088ff else 0
def g255H13 := limbs80 #[#[0x42b49600009ce0b8,0xc5d3fd008100]]
def g255L : Nat → Packing
  | 7 => (57,6,6,0,0,10,0,g255D7)
  | 8 => (306,5,6,0,0,13,0,g255D8)
  | 9 => (378,4,6,0,0,15,0,g255D9)
  | 10 => (188,3,6,0,0,15,0,g255D10)
  | 11 => (45,2,6,0,0,12,0,g255D11)
  | 12 => (7,1,6,0,0,9,0,g255D12)
  | 13 => (1,0,6,0,0,0,0,g255D13)
  | _ => emptyPacking
def g255I : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 21 431 3 11 6 1 g255H8
  | 9 => lookupWord 104 617 6 14 9 1 g255H9
  | 10 => lookupWord 119 587 8 14 9 1 g255H10
  | 11 => lookupWord 60 331 7 13 8 1 g255H11
  | 12 => lookupWord 15 71 6 11 6 1 g255H12
  | 13 => lookupWord 2 17 0 8 3 1 g255H13
  | _ => fun _ => none
def g255 : Forest := ⟨255,13,fun i => g255Y[i]?.getD (0,0),g255C,g255A,g255L,g255I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P7_0 : block g255 7 0 57=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B7 : block g255 7 0 57=true := g255P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_0 : block g255 8 0 6=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_6 : block g255 8 6 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_102 : block g255 8 102 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_198 : block g255 8 198 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_294 : block g255 8 294 12=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B8 : block g255 8 0 306=true := (@block_merge g255 8 0 102 204 (@block_merge g255 8 0 6 96 g255P8_0 g255P8_6) (@block_merge g255 8 102 96 108 g255P8_102 (@block_merge g255 8 198 96 12 g255P8_198 g255P8_294)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_0 : block g255 9 0 16=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_16 : block g255 9 16 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_112 : block g255 9 112 30=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_142 : block g255 9 142 96=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_238 : block g255 9 238 96=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_334 : block g255 9 334 44=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B9 : block g255 9 0 378=true := (@block_merge g255 9 0 142 236 (@block_merge g255 9 0 16 126 g255P9_0 (@block_merge g255 9 16 96 30 g255P9_16 g255P9_112)) (@block_merge g255 9 142 96 140 g255P9_142 (@block_merge g255 9 238 96 44 g255P9_238 g255P9_334)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_0 : block g255 10 0 3=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_3 : block g255 10 3 53=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_56 : block g255 10 56 96=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_152 : block g255 10 152 9=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_161 : block g255 10 161 27=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B10 : block g255 10 0 188=true := (@block_merge g255 10 0 56 132 (@block_merge g255 10 0 3 53 g255P10_0 g255P10_3) (@block_merge g255 10 56 96 36 g255P10_56 (@block_merge g255 10 152 9 27 g255P10_152 g255P10_161)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_0 : block g255 11 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_1 : block g255 11 1 24=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_25 : block g255 11 25 20=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B11 : block g255 11 0 45=true := (@block_merge g255 11 0 1 44 g255P11_0 (@block_merge g255 11 1 24 20 g255P11_1 g255P11_25))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P12_0 : block g255 12 0 7=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B12 : block g255 12 0 7=true := g255P12_0
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

end PEqualNP.Outside.L_meta_34752

open PEqualNP.Outside.L_meta_34752 in
theorem PEqualNP.Outside.L_meta_34752 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 4, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 4, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 4, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 4, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 4, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 4, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o fit _ correct
  exact replaceShort g255R gates o fit correct

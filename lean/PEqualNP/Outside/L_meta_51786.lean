import PEqualNP.Defs

-- The two-mode live-state and cofactor checker follows L_meta_1674 and L_meta_670.
-- The graph, restrictions and all search certificates below are for L_meta_51786.

-- Shared forest and cofactor certificates from L_meta_1674 and PR 11111 for L_meta_1677.
-- The original credit line is retained below. The two root certificates here cover the unpinned graph.

-- The checker and the bound certificates are adapted from PEqualNP/Outside/L_meta_1667.lean (Apache-2.0).
-- Two modes: u=false are monotone runs (AND, OR); u=true are runs up to complement, where negation is free.
namespace PEqualNP.Outside.L_meta_51786
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
def graph : Sig := (BitVec.ofNat 512 (word80 [0xffffffff,0xffffffffffffffffffff,0xfefefffffffffffefffe,0xfffefffaeeccaa00ffff,0xffffffffffffffffffff,0xfffffefefffffffffffe,0xfffefffefffaeeccaa00]))
def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 3) || (x 1 && x 4) || (x 0 && x 5) || (x 2 && x 5) || (x 3 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 5 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 2 && x 7) || (x 4 && x 7) || (x 5 && x 7) || (x 6 && x 7)
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
  (x 0 &&& x 3) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 2 &&& x 5) ||| (x 3 &&& x 5) ||| (x 0 &&& x 6) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 5 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 2 &&& x 7) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)
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


structure QuotientSpec where
  a : Nat
  b : Nat
  rev : Bool
  z : Nat
  o : Nat
  extra : Nat
  fl : Nat
  sw : List Nat
  single : Nat

def quotSpec : Nat → QuotientSpec
  | 0 => ⟨0,7,true,8,0,0,1,[80, 97, 116],3⟩
  | 1 => ⟨0,7,true,40,0,0,1,[96, 80, 81, 116],1⟩
  | 2 => ⟨0,7,true,72,0,0,1,[80, 97, 116],1⟩
  | 3 => ⟨1,3,true,144,0,0,2,[96, 80, 81, 117],1⟩
  | 4 => ⟨1,6,true,16,0,0,2,[112, 32, 81, 99, 82],1⟩
  | 5 => ⟨1,6,true,17,0,0,2,[112, 81, 99, 80],1⟩
  | 6 => ⟨1,6,true,24,0,0,2,[112, 80, 97],1⟩
  | 7 => ⟨1,6,true,48,0,0,2,[112, 80, 97, 83],1⟩
  | 8 => ⟨1,6,true,144,0,0,2,[32, 81, 99, 117],0⟩
  | 9 => ⟨3,4,false,33,0,0,0,[33, 83],0⟩
  | 10 => ⟨3,7,false,64,0,0,0,[16, 33, 115, 84],0⟩
  | 11 => ⟨4,5,false,9,0,0,0,[33, 84],0⟩
  | 12 => ⟨5,7,true,8,0,0,32,[97, 81, 84, 117],3⟩
  | 13 => ⟨5,7,true,9,0,0,32,[96, 81, 64, 117],1⟩
  | 14 => ⟨5,7,true,72,0,0,32,[81, 100, 117],1⟩
  | _ => ⟨0,0,false,0,0,0,0,[],0⟩

def quotDom (b : QuotientSpec) : Sig :=
  let d := (inputs.getD b.a zero) ^^^ (inputs.getD b.b zero)
  subcube b.z b.o &&& (if b.rev then d else ~~~d)

def quotSteps (b : QuotientSpec) : List Move :=
  let a := inputs.getD b.a zero
  let dest := inputs.getD b.b zero
  let want := if b.rev then ~~~a else a
  let move : Move := (want &&& ~~~dest, dest &&& ~~~want, Fin.ofNat 512 (1 <<< b.b))
  let flips := (List.range 9).filterMap fun i =>
    let w := inputs.getD i zero
    if b.fl.testBit i then some ((~~~w, w, Fin.ofNat 512 (1 <<< i)) : Move) else none
  b.sw.map swapRows ++ flips ++ fixRows (b.z ||| b.extra) b.o ++ [move]

def phaseFree (roots : List Sig) (w : Sig) := freeWord roots w || roots.contains (neg w)

theorem phaseFree_ok {xs w} (h : phaseFree xs w = true) :
    Available true (xs.map observe) (observe w) := by
  simp only [phaseFree,Bool.or_eq_true,List.contains_eq_mem,decide_eq_true_eq] at h
  rcases h with h | h
  · exact freeWord_ok h
  · refine Or.inr (Or.inr ⟨rfl, ?_⟩)
    rw [← obs_neg]
    exact List.mem_map_of_mem h

def signedMap (ms : List Move) (raw : List Sig) (base : List Sig) :=
  raw.all (fun a => phaseFree base (movedWord ms a))

theorem signedSlice {ms raw T base d L} (h : signedMap ms raw base = true)
    (all : movedWord ms d = one) (pr : proper (movedWord ms T))
    (low : Lower true base (movedWord ms T) L) : Slice true raw T d L := by
  have he : restrictRows (movedRow ms) (observe T) = observe (movedWord ms T) := by
    rw [moved_eq_rename, observe_rename]
  refine ⟨movedRow ms,base,?_,?_,?_,?_⟩
  · intro r
    rw [← bit_moved, all, bit_one]
  · intro a ha
    rw [← observe_rename, ← moved_eq_rename]
    exact phaseFree_ok (List.all_eq_true.mp h a ha)
  · rw [he]
    exact observe_proper pr
  · rw [he]
    exact low

def quotientCheck (u : Bool) (raw : List Sig) (T : Sig) (b : QuotientSpec) (q L P : Nat) : Bool :=
  let ms := quotSteps b
  let G := movedWord ms T
  let bs := varsX (q ||| b.single)
  let xs := supportPairs 0 b.single
  u && signedMap ms raw bs && (movedWord ms (quotDom b) == one) &&
    properB G && properB (graphGoal q) &&
    checkLift (fixRows b.single 0) G bs (varsX q) (graphGoal q) xs &&
    decide (L ≤ P+(xs.map Prod.fst).toFinset.card)

theorem quotientSound {u raw T b q L P}
    (low : Lower u (varsX q) (graphGoal q) P)
    (ok : quotientCheck u raw T b q L P = true) : Slice u raw T (quotDom b) L := by
  simp only [quotientCheck,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at ok
  obtain ⟨⟨⟨⟨⟨⟨hu,hm⟩,hd⟩,pg⟩,pq⟩,lift⟩,hle⟩ := ok
  subst u
  apply signedSlice hm hd (proper_of _ pg)
  intro p bank reach hit
  exact hle.trans (lift_ok lift (proper_of _ pg) (proper_of _ pq) low p bank reach hit)

def fieldDomain (z o : Nat) : Sig :=
  if o < 512 then subcube z o else quotDom (quotSpec (o-512))

def fieldCheck (u : Bool) (m : Nat) (c : ColumnInfo) (prior : Nat → Nat) : Bool :=
  if c.2.1 < 512 then colCheck m c prior else
    let q := c.2.2.1
    quotientCheck u (varsX (rawMask m c)) (chartGoal m) (quotSpec (c.2.1-512)) q c.2.2.2.2 (prior q)

theorem fieldSound {u m} (c : ColumnInfo) (prior : Nat → Nat)
    (low : ∀ q, Lower u (varsX q) (graphGoal q) (prior q))
    (ok : fieldCheck u m c prior = true) :
    Slice u (varsX (rawMask m c)) (chartGoal m) (fieldDomain c.1 c.2.1) c.2.2.2.2 := by
  by_cases h : c.2.1 < 512
  · simpa only [fieldDomain, h, if_true] using
      col_sound c prior low (by simpa only [fieldCheck, h, if_true] using ok)
  · simpa only [fieldDomain, h, if_false] using
      (quotientSound (low c.2.2.1) (by simpa only [fieldCheck, h, if_false] using ok) :
        Slice u (varsX (rawMask m c)) (chartGoal m) (quotDom (quotSpec (c.2.1-512))) c.2.2.2.2)

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
  (x 0 &&& x 3) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 2 &&& x 5) ||| (x 3 &&& x 5) ||| (x 0 &&& x 6) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 5 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 2 &&& x 7) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)
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
    materialize g.mode (varsX (rawMask g.mask ci)) (chosenSteps bank ops paid d) (fieldDomain ci.1 ci.2.1) ci.2.2.2.2

theorem buildRule_sound (g : Forest)
    (cols : ∀ ci ∈ g.cols, Slice g.mode (varsX (rawMask g.mask ci)) (targetOf g) (fieldDomain ci.1 ci.2.1) ci.2.2.2.2)
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
    (cols : ∀ ci ∈ g.cols, Slice g.mode (varsX (rawMask g.mask ci)) (targetOf g) (fieldDomain ci.1 ci.2.1) ci.2.2.2.2)
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
  g.cols.all (fun c => fieldCheck g.mode g.mask c prior) &&
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
      (fun x hx => fieldSound _ prior lower (geometry.1.2 x hx)) geometry.2 (by omega)
    exact block_at (rows 0 hk) i (by omega) (by omega)
  | succ k ih =>
    intro hk i hi
    apply nodeVerified_sound g _ i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => fieldSound _ prior lower (geometry.1.2 x hx)) geometry.2
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
    (ok : fieldCheck u m ci prior = true)
    (cut : (decide ws.Nodup && poolCut u (fieldDomain ci.1 ci.2.1) ci.2.2.2.2 cap 0 (varsX (rawMask m ci)) ws)=true) :
    Impossible u (graphGoal m) cap ws.toFinset := by
  simp only [Bool.and_eq_true,decide_eq_true_eq] at cut
  exact poolCut_sound (fieldSound ci prior low ok) [] rfl cut.1 cut.2

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

def kwDir (u p n : Bool) : Prop := p≠n ∧ (u=false → p=true)
structure PolarRooms (u : Bool) (S : Finset Sig) (T : Sig) where
  owns : Sig → Row → Row → Prop
  total : ∀ p n, bit p T=true → bit n T=false → ∃ v, owns v p n
  valid : ∀ {v p n}, owns v p n → v∈S ∧ kwDir u (bit p v) (bit n v)
  unique : ∀ {v w p n}, owns v p n → owns w p n → v=w
  rect : ∀ {v p n p' n'}, owns v p n' → owns v p' n → owns v p n

def polarLeaf (u : Bool) (T : Sig) : PolarRooms u {T} T where
  owns v p n := v=T ∧ bit p T=true ∧ bit n T=false
  total p n hp hn := ⟨T,rfl,hp,hn⟩
  valid := by rintro v p n ⟨rfl,hp,hn⟩; exact ⟨by simp,by simp [kwDir,hp,hn]⟩
  unique := by rintro v w p n ⟨rfl,_,_⟩ ⟨eq,_,_⟩; exact eq.symm
  rect := by rintro v p n p' n' ⟨e,hp,_⟩ ⟨_,_,hn⟩; exact ⟨e,hp,hn⟩

def kwBoolGate (d : Nat) (x y : Bool) : Bool :=
  if d=0 then x && y else if d=1 then x || y else if d=2 then x && !y else !x && y
def kwTurn (d : Nat) (a : Bool) :=
  (if d=3 then !a else a) == decide (d=1)
def kwTurnGate (d : Nat) (p n value : Bool) :=
  if value=decide (d=1) then kwTurn d p else kwTurn d n
theorem kwGateTable : ∀ (u : Bool) (d : Fin 4) (pa pb na nb : Bool),
    allowed u d.val → kwDir u (kwBoolGate d.val pa pb) (kwBoolGate d.val na nb) →
      kwDir u (if kwTurnGate d.val pa na (kwBoolGate d.val pa pb) then pa else pb)
        (if kwTurnGate d.val pa na (kwBoolGate d.val pa pb) then na else nb) := by
  unfold kwDir allowed
  decide +kernel

def polarFork {u : Bool} {U : Finset Sig} {T a b : Sig} {d : Nat} (hd : allowed u d)
    (ha : a∉U) (hb : b∉U) (hz : bin d a b∉U)
    (H : PolarRooms u (insert (bin d a b) U) T) : PolarRooms u (insert a (insert b U)) T := by
  let z := bin d a b
  let branch := fun r : Row => if kwTurn d (bit r a) then a else b
  let sel := fun p n : Row => if bit p z=decide (d=1) then branch p else branch n
  have pick (p n) : sel p n=a ∨ sel p n=b := by
    dsimp only [sel,branch]; split <;> split <;> simp
  have outside (p n) : sel p n ∉ U := by
    rcases pick p n with eq | eq
    · simpa only [eq] using ha
    · simpa only [eq] using hb
  have separates (p n) (h : kwDir u (bit p z) (bit n z)) :
      kwDir u (bit p (sel p n)) (bit n (sel p n)) := by
    have lt : d<4 := by rcases hd with h | ⟨_,h⟩ <;> omega
    have gate (r : Row) : bit r z = kwBoolGate d (bit r a) (bit r b) := by
      dsimp only [z,kwBoolGate,bin]; split_ifs <;> simp [bit,r.isLt]
    have ok := kwGateTable u ⟨d,lt⟩ (bit p a) (bit p b) (bit n a) (bit n b) hd
      (by simpa only [←gate] using h)
    change kwDir u (if kwTurnGate d (bit p a) (bit n a) (kwBoolGate d (bit p a) (bit p b)) then _ else _)
      (if kwTurnGate d (bit p a) (bit n a) (kwBoolGate d (bit p a) (bit p b)) then _ else _) at ok
    rw [←gate] at ok
    by_cases side : bit p z=decide (d=1)
    · cases ha : kwTurn d (bit p a) <;> simpa only [sel,side,ite_true,branch,kwTurnGate,ha,
        Bool.false_eq_true,ite_false] using ok
    · cases ha : kwTurn d (bit n a) <;> simpa only [sel,side,ite_false,branch,kwTurnGate,ha,
        Bool.false_eq_true,ite_true] using ok
  refine { owns := fun v p n => (v∈U ∧ H.owns v p n) ∨ (v=sel p n ∧ H.owns z p n)
           total := ?_
           valid := ?_
           unique := ?_
           rect := ?_ }
  · intro p n hp hn
    obtain ⟨v,hv⟩ := H.total p n hp hn
    rcases Finset.mem_insert.mp (H.valid hv).1 with eq | mem
    · have vz : v=z := eq
      refine ⟨sel p n,Or.inr ⟨rfl,?_⟩⟩
      rw [←vz]
      exact hv
    · exact ⟨v,Or.inl ⟨mem,hv⟩⟩
  · intro v p n h
    rcases h with ⟨mem,hv⟩ | ⟨e,hv⟩
    · exact ⟨Finset.mem_insert_of_mem (Finset.mem_insert_of_mem mem),(H.valid hv).2⟩
    · subst v
      have inS : sel p n ∈ insert a (insert b U) := by
        rcases pick p n with eq | eq <;> simp [eq]
      exact ⟨inS,separates p n (H.valid hv).2⟩
  · intro v w p n h1 h2
    rcases h1 with ⟨vU,hv⟩ | ⟨ve,hv⟩ <;> rcases h2 with ⟨wU,hw⟩ | ⟨we,hw⟩
    · exact H.unique hv hw
    · apply False.elim
      apply hz
      change z∈U
      rw [←H.unique hv hw]
      exact vU
    · apply False.elim
      apply hz
      change z∈U
      rw [←H.unique hw hv]
      exact wU
    · exact ve.trans we.symm
  · intro v p n p' n' h1 h2
    rcases h1 with ⟨vU,hv⟩ | ⟨ve,hv⟩ <;> rcases h2 with ⟨wU,hw⟩ | ⟨we,hw⟩
    · exact Or.inl ⟨vU,H.rect hv hw⟩
    · exact False.elim (outside p' n (we ▸ vU))
    · exact False.elim (outside p n' (ve ▸ wU))
    · refine Or.inr ⟨?_,H.rect hv hw⟩
      have e : bit p z = bit p' z := by
        have v1 := (H.valid (H.rect hv hw)).2.1
        have v2 := (H.valid hw).2.1
        cases ep : bit p z <;> cases ep' : bit p' z <;> cases en : bit n z <;> simp_all
      by_cases h : bit p z=decide (d=1)
      · simpa only [sel,h,ite_true] using ve
      · have h' : bit p' z≠decide (d=1) := e ▸ h
        simpa only [sel,h,h',ite_false] using we

theorem kwWidth {u T k S} (h : Live u T k S) : S.card ≤ k+1 := by
  induction h using Live.ind with
  | stop hp => simp
  | @binary k U a b d hd ha hb hab hf tail ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a:=a) (insert b U)
    have h2 := Finset.card_insert_le (a:=b) U
    omega

theorem polarTight {u T k S} (run : Live u T k S) (tight : S.card=k+1) :
    Nonempty (PolarRooms u S T) := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,_⟩ := run
    exact ⟨polarLeaf u T⟩
  | succ k ih =>
    obtain ⟨U,a,b,d,hd,rfl,_,_,hab,hfresh,tail⟩ := run
    have fresh : bin d a b∉U := fun h => hfresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    have li := kwWidth tail
    rw [Finset.card_insert_of_notMem fresh] at li
    have le1 := Finset.card_insert_le (a:=a) (insert b U)
    have le2 := Finset.card_insert_le (a:=b) U
    have ha : a∉U := by
      intro h
      rw [Finset.insert_eq_of_mem (Finset.mem_insert_of_mem h : a∈insert b U)] at tight
      omega
    have hb : b∉U := by
      intro h
      rw [Finset.insert_eq_of_mem h] at tight le1
      omega
    have eq : (insert (bin d a b) U).card=k+1 := by
      rw [Finset.card_insert_of_notMem fresh]
      omega
    obtain ⟨H⟩ := ih tail eq
    exact ⟨polarFork hd ha hb fresh H⟩

def polarOnly (u : Bool) (S : Finset Sig) (T v : Sig) (p n : Row) :=
  bit p T=true ∧ bit n T=false ∧ ∀ w∈S, kwDir u (bit p w) (bit n w) → w=v

theorem polarOwn {u S T v p n} (H : PolarRooms u S T) (one : polarOnly u S T v p n) : H.owns v p n := by
  obtain ⟨w,hw⟩ := H.total p n one.1 one.2.1
  have eq := one.2.2 w (H.valid hw).1 (H.valid hw).2
  exact eq ▸ hw

theorem polarCross {u S T k a b p n pa pb na nb} (size : k+1=S.card) (different : a≠b)
    (A : polarOnly u S T a p na) (B : polarOnly u S T b p nb)
    (C : polarOnly u S T a pa n) (D : polarOnly u S T b pb n) : Impossible u T k S := by
  intro j hj run
  have lb := kwWidth run
  have tight : S.card=j+1 := by omega
  obtain ⟨H⟩ := polarTight run tight
  exact different (H.unique (H.rect (polarOwn H A) (polarOwn H C)) (H.rect (polarOwn H B) (polarOwn H D)))
def kwProbe (xs q : Nat) : Row := Fin.ofNat 512 ((xs >>> (9*q)) &&& 511)
def CutRow (g : Forest) (k start n : Nat) : Prop :=
  ∀ j, start≤j → j<start+n → nodeVerified g k j=true ∨ Impossible g.mode (targetOf g) k (stateSet g k j).toFinset
theorem mixedEmpty (g : Forest) (k a : Nat) : CutRow g k a 0 := by
  intro j lo hi
  omega
theorem checkedRow {g k a n} (h : block g k a n=true) : CutRow g k a n :=
  fun j lo hi => Or.inl (block_at h j lo hi)
theorem joinRow {g k a x y} (first : CutRow g k a x) (last : CutRow g k (a+x) y) :
    CutRow g k a (x+y) := by
  intro j lo hi
  by_cases e : j<a+x
  · exact first j lo e
  · exact last j (by omega) (by omega)
def mixedTables (g : Forest) (top : Nat) := ∀ k ≤ top, CutRow g k 0 (g.levels k).1
theorem mixedForest (g : Forest) (top : Nat) (prior : Nat → Nat)
    (lower : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geometry : graphValid g prior=true) (rows : mixedTables g top) :
    ∀ k ≤ top, ∀ i < (g.levels k).1, Impossible g.mode (targetOf g) k (stateSet g k i).toFinset := by
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geometry
  intro k
  induction k with
  | zero =>
    intro hk i hi
    rcases rows 0 hk i (by omega) (by omega) with checked | done
    · exact nodeVerified_sound g 0 i (chart_pairs geometry.1.1.1 geometry.1.1.2)
        (fun x hx => fieldSound _ prior lower (geometry.1.2 x hx)) geometry.2 (by omega) checked
    · exact done
  | succ k ih =>
    intro hk i hi
    rcases rows _ hk i (by omega) (by omega) with checked | done
    · exact nodeVerified_sound g _ i (chart_pairs geometry.1.1.1 geometry.1.1.2)
        (fun x hx => fieldSound _ prior lower (geometry.1.2 x hx)) geometry.2
        (fun _ => by simpa using ih (by omega)) checked
    · exact done
theorem mixedRoot {g top prior k i ws} (lower : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geom : graphValid g prior=true) (blocks : mixedTables g top) (le : k≤top)
    (idx : indexedRoot g k i ws=true) : Impossible g.mode (targetOf g) k ws.toFinset := by
  simp only [indexedRoot,Bool.and_eq_true,decide_eq_true_eq] at idx
  rw [←sameWords_sound idx.2]
  exact mixedForest g top prior lower geom blocks _ le i idx.1
def polarCell (ws : List Sig) (T v : Sig) (p n : Row) :=
  bit p T && !bit n T && ws.all (fun w => (bit p w==bit n w) || w==v)
theorem polarCell_sound {ws T v p n} (h : polarCell ws T v p n=true) :
    polarOnly true ws.toFinset T v p n := by
  simp only [polarCell,Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true] at h
  refine ⟨h.1.1,h.1.2,?_⟩
  intro w hw sep
  have e : (bit p w==bit n w)=false := beq_eq_false_iff_ne.mpr sep.1
  simpa only [e,Bool.false_or,beq_iff_eq] using h.2 w (List.mem_toFinset.mp hw)
def polarWord (T : Sig) (ws : List Sig) (k v : Nat) :=
  let a := ws.getD (v &&& 15) zero
  let b := ws.getD ((v >>> 4) &&& 15) zero
  let pos := kwProbe (v >>> 8)
  let negs := kwProbe (v >>> 35)
  decide (k+1=ws.toFinset.card) && decide (a≠b) &&
    polarCell ws T a (pos 0) (negs 1) && polarCell ws T b (pos 0) (negs 2) &&
    polarCell ws T a (pos 1) (negs 0) && polarCell ws T b (pos 2) (negs 0)
theorem polarWord_sound {T ws k v} (h : polarWord T ws k v=true) : Impossible true T k ws.toFinset := by
  simp only [polarWord,Bool.and_eq_true,decide_eq_true_eq] at h
  exact polarCross h.1.1.1.1.1 h.1.1.1.1.2 (polarCell_sound h.1.1.1.2)
    (polarCell_sound h.1.1.2) (polarCell_sound h.1.2) (polarCell_sound h.2)
def polarSeries (g : Forest) (k start n : Nat) (data : Nat→Nat) :=
  (List.range n).all (fun j =>
    let r := (data 0 >>> (64*j)) &&& ((1 <<< 64)-1)
    if r=0 then nodeVerified g k (start+j) else polarWord (targetOf g) (stateSet g k (start+j)) k r)
theorem polarBlock {g k start n data} (mode : g.mode=true)
    (ok : polarSeries g k start n data=true) : CutRow g k start n := by
  intro j lo hi
  have h := List.all_eq_true.mp ok (j-start) (List.mem_range.mpr (by omega))
  have e : start+(j-start)=j := by omega
  dsimp only at h
  split at h
  · left; simpa only [e] using h
  · right; rw [mode]
    apply polarWord_sound
    simpa only [e] using h
theorem mixedLower {g prior i hints} (low : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : mixedTables g g.cap)
    (idx : indexedRoot g g.cap i (vars g.mask) = true) (hp : properB (targetOf g) = true)
    (ess : checkEssential (targetOf g) (vars g.mask) (graphPairs g.mask hints) = true)
    (all : (graphPairs g.mask hints).map Prod.fst = vars g.mask) :
    Lower g.mode (vars g.mask) (targetOf g) (g.cap+1) := by
  apply lower_impossible (proper_of _ hp) (essential_plain ess).1 (essential_plain ess).2 _ (mixedRoot low geom blocks (Nat.le_refl _) idx)
  intro a ha
  apply essential_ok ess a
  rw [all]
  exact List.mem_toFinset.mpr ha



def target (x : Fin 8 → Bool) : Bool := decide (∃ i < ([0, 3, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
def smallCircuit : Circuit := ⟨[⟨.or,[0,5]⟩,⟨.or,[6,7]⟩,⟨.or,[0,2]⟩,⟨.or,[1,8]⟩,⟨.or,[4,6]⟩,⟨.or,[6,8]⟩,⟨.or,[1,7]⟩,⟨.or,[5,9]⟩,⟨.and,[14,12]⟩,⟨.and,[13,3]⟩,⟨.and,[15,10]⟩,⟨.and,[9,11]⟩,⟨.or,[16,17]⟩,⟨.or,[20,18]⟩,⟨.or,[21,19]⟩], 22⟩

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
theorem g41P3_0 : CutRow g41 3 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=3) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g41B3 : CutRow g41 3 0 1 := g41P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g41T : mixedTables g41 3 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g41 0 0
  · exact mixedEmpty g41 1 0
  · exact mixedEmpty g41 2 0
  · exact g41B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g41G : graphValid g41 (boundsBefore []) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low41 : Lower true (varsX 41) (graphGoal 41) 4 := mixedLower (g:=g41) (i:=0) (hints:=3) (before_sound [] baseKnown) g41G g41T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K41 := extendKnown [] 4 [(41,[]),(73,[101]),(97,[83,67,100]),(100,[32,16,83,67,100]),(104,[48,16,33,82,66,100]),(146,[16,67,117,101]),(161,[83,67,116,100]),(193,[99,67,117]),(194,[16,99,67,117]),(224,[80,16,33,99,66,116])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V41 : Known true K41 := extend_ok (m:=41) baseKnown low41 (by decide +kernel)
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
theorem g45P4_0 : CutRow g45 4 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g45B4 : CutRow g45 4 0 1 := g45P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g45T : mixedTables g45 4 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g45 0 0
  · exact mixedEmpty g45 1 0
  · exact mixedEmpty g45 2 0
  · exact mixedEmpty g45 3 0
  · exact g45B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g45G : graphValid g45 (boundsBefore K41) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low45 : Lower true (varsX 45) (graphGoal 45) 5 := mixedLower (g:=g45) (i:=0) (hints:=1283) (before_sound K41 V41) g45G g45T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K45 := extendKnown K41 5 [(45,[]),(75,[33,101]),(147,[16,32,67,117,101]),(163,[33,83,67,116,100]),(172,[32,16,49,113,65,100]),(177,[66,83,115,99]),(178,[16,82,67,50,115,99]),(202,[16,50,114,66,101,84]),(240,[80,16,66,99,33,114,50])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V45 : Known true K45 := extend_ok (m:=45) V41 low45 (by decide +kernel)
def g83Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x2fc38ff01fff1ff02,0xfc38ff01fff1ff02fc38])),(BitVec.ofNat 152 (word80 [0x42ccdb2a5451240242,0xccdb2a5451240242ccdb]))),((BitVec.ofNat 152 (word80 [0xfdcbc7fffe07fe3ffd,0xcbc7fffe07fe3ffdcbc7])),(BitVec.ofNat 152 (word80 [0x1448490c1860408414,0x48490c18604084144849]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xece607fffff8003fec,0xe607fffff8003fece607])),(BitVec.ofNat 152 (word80 [0x8a7b6b06085892808,0xa7b6b06085892808a7b6]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1b3df8ffffffffc01b,0x3df8ffffffffc01b3df8])),(BitVec.ofNat 152 (word80 [0x893124c08106003089,0x3124c081060030893124]))),(0x0,0x0),(0x0,0x0)]
def g83C : List ColumnInfo := []
def g83A : List (List Nat) := [[],[64,97]]
def g83D3 (j : Nat) := if j=0 then 0xf else 0
def g83L : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,g83D3)
  | _ => emptyPacking
def g83I (_ _ : Nat) : Option (Nat × Nat) := none
def g83 : Forest := ⟨83,3,fun i => g83Y[i]?.getD (0,0),g83C,g83A,g83L,g83I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g83P3_0 : CutRow g83 3 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g83B3 : CutRow g83 3 0 1 := g83P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g83T : mixedTables g83 3 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g83 0 0
  · exact mixedEmpty g83 1 0
  · exact mixedEmpty g83 2 0
  · exact g83B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g83G : graphValid g83 (boundsBefore K45) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low83 : Lower true (varsX 83) (graphGoal 83) 4 := mixedLower (g:=g83) (i:=0) (hints:=65606) (before_sound K45 V45) g83G g83T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K83 := extendKnown K45 4 [(83,[]),(90,[48,32]),(114,[64,97,32,50,83]),(139,[16,67,118]),(153,[48,113,33,32,96]),(170,[16,80,32,50,67,118]),(184,[48,113,32,33,82,101]),(216,[48,113,32,33,82])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V83 : Known true K83 := extend_ok (m:=83) V45 low83 (by decide +kernel)
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
theorem g101P4_0 : CutRow g101 4 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g101B4 : CutRow g101 4 0 1 := g101P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g101T : mixedTables g101 4 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g101 0 0
  · exact mixedEmpty g101 1 0
  · exact mixedEmpty g101 2 0
  · exact mixedEmpty g101 3 0
  · exact g101B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g101G : graphValid g101 (boundsBefore K83) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low101 : Lower true (varsX 101) (graphGoal 101) 5 := mixedLower (g:=g101) (i:=0) (hints:=1285) (before_sound K83 V83) g101G g101T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K101 := extendKnown K83 5 [(165,[118]),(169,[48,114,32,80,101]),(195,[33,101,117]),(210,[64,16,98,50,49,81,117]),(232,[48,16,114,66])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V101 : Known true K101 := extend_ok (m:=101) V83 low101 (by decide +kernel)
def g105Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xdf7ec03c3ffe0fbefd,0x80787ffc1f7dfb00f0ff])),(BitVec.ofNat 152 (word80 [0x820404444444210408,0x8888888420810111111]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1fbf43c3c3fff03f7e,0x878787ffe07efd0f0f0f])),(BitVec.ofNat 152 (word80 [0x40808888888420810,0x11111110841020222222]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xe03fbc03fc3fffc07f,0x7807f87fff80fef00ff0])),(BitVec.ofNat 152 (word80 [0x81011111110841020,0x22222221082040444444]))),((BitVec.ofNat 152 (word80 [0xffc03ffc003fffff80,0x7ff8007fffff00fff000])),(BitVec.ofNat 152 (word80 [0x102022222221082040,0x44444442104080888888]))),(0x0,0x0),(0x0,0x0)]
def g105C : List ColumnInfo := [(1,0,104,0,4),(8,0,97,0,4),(32,0,73,0,4),(64,0,41,0,4)]
def g105A : List (List Nat) := [[],[101],[83],[83,99],[99,83],[99],[48],[48,101],[48,80],[48,80,96],[48,96,80],[48,96],[80,48],[80,48,99],[80],[80,96],[80,99],[80,99,48],[96,48,83],[96,48],[96,80],[96],[96,83,48],[96,83]]
def g105D3 := limbs80 #[#[0x23ea6a1221e12148110,0x8028]]
def g105D4 := limbs80 #[#[0x2fd0910bd42443e48110,0x609085870]]
def g105H4 (j : Nat) := if j=0 then 0x1800000088000 else 0
def g105D5 (j : Nat) := if j=0 then 0xd1027d10 else 0
def g105H5 := limbs80 #[#[0x200000000001e2,0x2200001fc610,0x1e1430008a000]]
def g105D6 (j : Nat) := if j=0 then 0x3904f else 0
def g105H6 := limbs80 #[#[0x0,0x5680000094000049000,0x2c0000090002]]
def g105L : Nat → Packing
  | 3 => (2,3,2,0,0,5,0,g105D3)
  | 4 => (3,2,2,0,0,5,0,g105D4)
  | 5 => (1,1,2,0,0,0,0,g105D5)
  | 6 => (1,0,2,0,0,0,0,g105D6)
  | _ => emptyPacking
def g105I : Nat → Nat → Option (Nat × Nat)
  | 4 => lookupWord 1 11 0 5 1 0 g105H4
  | 5 => lookupWord 2 23 1 9 2 3 g105H5
  | 6 => lookupWord 1 23 0 9 0 5 g105H6
  | _ => fun _ => none
def g105 : Forest := ⟨105,6,fun i => g105Y[i]?.getD (0,0),g105C,g105A,g105L,g105I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g105P3_0 : CutRow g105 3 0 2 := by
  apply checkedRow
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g105B3 : CutRow g105 3 0 2 := g105P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g105P4_0 : CutRow g105 4 0 3 := by
  apply checkedRow
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g105B4 : CutRow g105 4 0 3 := g105P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g105P5_0 : CutRow g105 5 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g105B5 : CutRow g105 5 0 1 := g105P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g105P6_0 : CutRow g105 6 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g105B6 : CutRow g105 6 0 1 := g105P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g105T : mixedTables g105 6 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g105 0 0
  · exact mixedEmpty g105 1 0
  · exact mixedEmpty g105 2 0
  · exact g105B3
  · exact g105B4
  · exact g105B5
  · exact g105B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g105G : graphValid g105 (boundsBefore K101) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low105 : Lower true (varsX 105) (graphGoal 105) 7 := mixedLower (g:=g105) (i:=0) (hints:=3) (before_sound K101 V101) g105G g105T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K105 := extendKnown K101 7 [(105,[]),(225,[83,67,100,116]),(228,[32,16,83,67,100,116])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V105 : Known true K105 := extend_ok (m:=105) V101 low105 (by decide +kernel)
def g59Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xc00fff0ffffffc00ff,0xfff0fffeea3a5303f03f])),(BitVec.ofNat 152 (word80 [0x84a08a210802284a02,0x80220882200a53145145]))),((BitVec.ofNat 152 (word80 [0xfff0000ffc3fffff00,0x3fffffc009adfd000fc0])),(BitVec.ofNat 152 (word80 [0xc42c405090b10c4b,0x11404108092d994d34d3]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffff0003fffffff,0xc000fffd77e88afc003f])),(BitVec.ofNat 152 (word80 [0x90130026104c0100c,0x584120152a08828a28a]))),((BitVec.ofNat 152 (word80 [0x3fffffff,0xffff00012697f4000fc0])),(BitVec.ofNat 152 (word80 [0x2e09c08b8227026090,0x26009c11269264b2cb2c]))),((BitVec.ofNat 152 (word80 [0xffffffffffc0000000,0x39d530dfff000])),(BitVec.ofNat 152 (word80 [0x300e000c00380380e0,0x3808e0208d5104c30c30]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g59C : List ColumnInfo := [(0,2,41,16,5)]
def g59A : List (List Nat) := [[],[83],[65],[65,83],[48],[48,80],[48,65],[48,65,80],[80,48],[80],[80,65,48],[80,65]]
def g59D5 (j : Nat) := if j=0 then 0x3f else 0
def g59L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g59D5)
  | _ => emptyPacking
def g59I (_ _ : Nat) : Option (Nat × Nat) := none
def g59 : Forest := ⟨59,5,fun i => g59Y[i]?.getD (0,0),g59C,g59A,g59L,g59I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59P5_0 : CutRow g59 5 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g59B5 : CutRow g59 5 0 1 := g59P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59T : mixedTables g59 5 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g59 0 0
  · exact mixedEmpty g59 1 0
  · exact mixedEmpty g59 2 0
  · exact mixedEmpty g59 3 0
  · exact mixedEmpty g59 4 0
  · exact g59B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59G : graphValid g59 (boundsBefore K105) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low59 : Lower true (varsX 59) (graphGoal 59) 6 := mixedLower (g:=g59) (i:=0) (hints:=65603) (before_sound K105 V105) g59G g59T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K59 := extendKnown K105 6 [(59,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V59 : Known true K59 := extend_ok (m:=59) V105 low59 (by decide +kernel)
def g91Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xf003ff87fe1fffc01f,0xfff87fffe474a4007c1f])),(BitVec.ofNat 152 (word80 [0xa12845108440228940,0xa01108826014a45294a5]))),((BitVec.ofNat 152 (word80 [0xfffc0007ffe1ffffe0,0xfffffc0335be20f83e0])),(BitVec.ofNat 152 (word80 [0xc030162028040b0182,0xc0a00108225922318c63]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffff80001ffffff,0xf0007ffccfd11df0001f])),(BitVec.ofNat 152 (word80 [0x240980130884c0203,0x2c2120087c108a5294a]))),((BitVec.ofNat 152 (word80 [0x1ffffff,0xffff80004d2fe80003e0])),(BitVec.ofNat 152 (word80 [0xb82e045c111702c14,0xb005c104d26c9ce739c]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffffffe000000,0x33aa61bfffc00])),(BitVec.ofNat 152 (word80 [0xc0300060001803018,0xc046021182211084210]))),(0x0,0x0),(0x0,0x0)]
def g91C : List ColumnInfo := [(0,16,73,2,5),(16,0,75,0,5),(1,0,90,0,4),(2,16,73,0,4),(8,0,83,0,4)]
def g91A : List (List Nat) := [[],[48]]
def g91D4 (j : Nat) := if j=0 then 0x5bd4940 else 0
def g91D5 := limbs80 #[#[0x240d140ff40fd40fd20,0x2012]]
def g91H5 (j : Nat) := if j=0 then 0xd else 0
def g91D6 (j : Nat) := if j=0 then 0x18989f else 0
def g91H6 := limbs80 #[#[0xa008005200000000001a,0x118000f]]
def g91L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g91D4)
  | 5 => (3,1,3,0,0,5,0,g91D5)
  | 6 => (1,0,3,0,0,0,0,g91D6)
  | _ => emptyPacking
def g91I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 4 0 0 g91H5
  | 6 => lookupWord 1 19 0 7 2 1 g91H6
  | _ => fun _ => none
def g91 : Forest := ⟨91,6,fun i => g91Y[i]?.getD (0,0),g91C,g91A,g91L,g91I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g91P4_0 : CutRow g91 4 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g91B4 : CutRow g91 4 0 1 := g91P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g91P5_0 : CutRow g91 5 0 3 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g91B5 : CutRow g91 5 0 3 := g91P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g91P6_0 : CutRow g91 6 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g91B6 : CutRow g91 6 0 1 := g91P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g91T : mixedTables g91 6 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g91 0 0
  · exact mixedEmpty g91 1 0
  · exact mixedEmpty g91 2 0
  · exact mixedEmpty g91 3 0
  · exact g91B4
  · exact g91B5
  · exact g91B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g91G : graphValid g91 (boundsBefore K59) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low91 : Lower true (varsX 91) (graphGoal 91) 7 := mixedLower (g:=g91) (i:=0) (hints:=65603) (before_sound K59 V59) g91G g91T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K91 := extendKnown K59 7 [(91,[]),(115,[83]),(122,[48,32,82]),(155,[16,67,118]),(186,[16,80,32,67,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V91 : Known true K91 := extend_ok (m:=91) V59 low91 (by decide +kernel)
def g107Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfe1ff00ff87f87ffc0,0x7fc7ffffd3b94000f0ff])),(BitVec.ofNat 152 (word80 [0x1440a0a05101100285,0x2902008418941111111]))),((BitVec.ofNat 152 (word80 [0x1ffff0007ff87fff,0x8007f1fc231ee00f0000])),(BitVec.ofNat 152 (word80 [0x588ac4c5622a012b06,0x2b214491231ee7777777]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1fffffff80007fff,0xfff801ff9c1f30f00f0f])),(BitVec.ofNat 152 (word80 [0x61030101800c220c08,0xc0188201c1602222222]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffe000000000007fff,0xfffffe000be4bf000ff0])),(BitVec.ofNat 152 (word80 [0x800c06060430443010,0x300200c20260b4444444]))),((BitVec.ofNat 152 (word80 [0xffffffffffffff8000,0x6442cffff000])),(BitVec.ofNat 152 (word80 [0x1008080040004020,0x40040100000008888888]))),(0x0,0x0),(0x0,0x0)]
def g107C : List ColumnInfo := [(2,0,105,0,7)]
def g107A : List (List Nat) := [[],[83],[48],[48,80],[80,48],[80]]
def g107D7 (j : Nat) := if j=0 then 0x3f else 0
def g107L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g107D7)
  | _ => emptyPacking
def g107I (_ _ : Nat) : Option (Nat × Nat) := none
def g107 : Forest := ⟨107,7,fun i => g107Y[i]?.getD (0,0),g107C,g107A,g107L,g107I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g107P7_0 : CutRow g107 7 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g107B7 : CutRow g107 7 0 1 := g107P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g107T : mixedTables g107 7 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g107 0 0
  · exact mixedEmpty g107 1 0
  · exact mixedEmpty g107 2 0
  · exact mixedEmpty g107 3 0
  · exact mixedEmpty g107 4 0
  · exact mixedEmpty g107 5 0
  · exact mixedEmpty g107 6 0
  · exact g107B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g107G : graphValid g107 (boundsBefore K91) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low107 : Lower true (varsX 107) (graphGoal 107) 8 := mixedLower (g:=g107) (i:=0) (hints:=99) (before_sound K91 V91) g107G g107T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K107 := extendKnown K91 8 [(107,[]),(241,[65,33,83,99,115])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V107 : Known true K107 := extend_ok (m:=107) V91 low107 (by decide +kernel)
def g109Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xff0ff01fe3f8ffe0,0x3fc7f1ffd675000f00ff])),(BitVec.ofNat 152 (word80 [0xa0a20a14148120142,0x82902402163411111111]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xff000fffe003ff1fff,0xc007fe3f317a00f00f00])),(BitVec.ofNat 152 (word80 [0x2c2c42c18590a04583,0xb214084b17a33333333]))),((BitVec.ofNat 152 (word80 [0xffffffc001fff,0xfff8003fede10f00f00f])),(BitVec.ofNat 152 (word80 [0x303083020600c48604,0xc01890829c122222222]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffff0000000001fff,0xffffffc01388f000fff0])),(BitVec.ofNat 152 (word80 [0x404004040801000808,0x10020010000044444444]))),((BitVec.ofNat 152 (word80 [0xffffffffffffffe000,0x2816ffff0000])),(BitVec.ofNat 152 (word80 [0x808008081002001010,0x20040020000088888888]))),(0x0,0x0),(0x0,0x0)]
def g109C : List ColumnInfo := [(4,0,105,0,7)]
def g109A : List (List Nat) := [[],[101],[48],[48,101]]
def g109D7 (j : Nat) := if j=0 then 0x3f else 0
def g109L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g109D7)
  | _ => emptyPacking
def g109I (_ _ : Nat) : Option (Nat × Nat) := none
def g109 : Forest := ⟨109,7,fun i => g109Y[i]?.getD (0,0),g109C,g109A,g109L,g109I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g109P7_0 : CutRow g109 7 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g109B7 : CutRow g109 7 0 1 := g109P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g109T : mixedTables g109 7 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g109 0 0
  · exact mixedEmpty g109 1 0
  · exact mixedEmpty g109 2 0
  · exact mixedEmpty g109 3 0
  · exact mixedEmpty g109 4 0
  · exact mixedEmpty g109 5 0
  · exact mixedEmpty g109 6 0
  · exact g109B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g109G : graphValid g109 (boundsBefore K107) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low109 : Lower true (varsX 109) (graphGoal 109) 8 := mixedLower (g:=g109) (i:=0) (hints:=1283) (before_sound K107 V107) g109G g109T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K109 := extendKnown K107 8 [(227,[33,83,67,100,116])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V109 : Known true K109 := extend_ok (m:=109) V107 low109 (by decide +kernel)
def g171Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffc03ffff0fffc03f,0xf0ffffffe8561e00f0ff])),(BitVec.ofNat 152 (word80 [0x202828140220028280,0xa2020020880612111111]))),((BitVec.ofNat 152 (word80 [0xffffc01fff0ffffc0,0xff0ff00cb5790f0000])),(BitVec.ofNat 152 (word80 [0x42b1315854022b030a,0xc4142242089579777777]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffe0000ffffff,0xff000fff33b526000f0f])),(BitVec.ofNat 152 (word80 [0x88c0406118448c2423,0x98488032b104aaaaaa]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xf00000000000ffffff,0xfffff000134bf8f00ff0])),(BitVec.ofNat 152 (word80 [0x3018180608830080c,0x200304014868444444]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffff000000,0xcea8c5fff000])),(BitVec.ofNat 152 (word80 [0xc0202018000c03030,0x8c08c08462084888888]))),(0x0,0x0)]
def g171C : List ColumnInfo := [(0,2,41,128,5),(2,0,169,0,5),(8,0,163,0,5),(1,0,170,0,4),(32,0,139,0,4),(128,2,41,0,4)]
def g171A : List (List Nat) := [[],[80]]
def g171D4 (j : Nat) := if j=0 then 0x5bd4930 else 0
def g171D5 (j : Nat) := if j=0 then 0xc8404fd30 else 0
def g171H5 (j : Nat) := if j=0 then 0x5 else 0
def g171D6 (j : Nat) := if j=0 then 0x232a8bf else 0
def g171H6 (j : Nat) := if j=0 then 0xb0 else 0
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
theorem g171P4_0 : CutRow g171 4 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g171B4 : CutRow g171 4 0 1 := g171P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g171P5_0 : CutRow g171 5 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g171B5 : CutRow g171 5 0 1 := g171P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g171P6_0 : CutRow g171 6 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g171B6 : CutRow g171 6 0 1 := g171P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g171T : mixedTables g171 6 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g171 0 0
  · exact mixedEmpty g171 1 0
  · exact mixedEmpty g171 2 0
  · exact mixedEmpty g171 3 0
  · exact g171B4
  · exact g171B5
  · exact g171B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g171G : graphValid g171 (boundsBefore K109) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low171 : Lower true (varsX 171) (graphGoal 171) 7 := mixedLower (g:=g171) (i:=0) (hints:=115) (before_sound K109 V109) g171G g171T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K171 := extendKnown K109 7 [(171,[]),(185,[65,33]),(217,[65,33,101]),(218,[16,48,32,66,117,101]),(248,[80,65,32,98])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V171 : Known true K171 := extend_ok (m:=171) V109 low171 (by decide +kernel)
def g173Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfe1ff01fffe3ffc03f,0xe1fe1fffb19d500f00ff])),(BitVec.ofNat 152 (word80 [0x1440a1414048028281,0x44044008218911111111]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1fffe01ffc7fffc0,0x1ffe1fc6d3a20f00f00])),(BitVec.ofNat 152 (word80 [0x5882c18582810b0305,0x882804112d3823333333]))),((BitVec.ofNat 152 (word80 [0x1fffffe0007fffff,0xfe0001ff9e1bc000f00f])),(BitVec.ofNat 152 (word80 [0x6113020613124c2426,0x13089201e12caaaaaaa]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffe0000000007fffff,0xfffffe000be08f00fff0])),(BitVec.ofNat 152 (word80 [0x800404080400100808,0x400040000004444444]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffff800000,0x6446ffff0000])),(BitVec.ofNat 152 (word80 [0x1808101800603030,0x118111824046c8888888]))),(0x0,0x0)]
def g173C : List ColumnInfo := [(1,0,172,0,5),(4,0,169,0,5),(8,0,165,0,5),(128,0,45,0,5)]
def g173A : List (List Nat) := [[],[112,50]]
def g173D6 (j : Nat) := if j=0 then 0x4e09f else 0
def g173L : Nat → Packing
  | 6 => (1,0,2,0,0,0,0,g173D6)
  | _ => emptyPacking
def g173I (_ _ : Nat) : Option (Nat × Nat) := none
def g173 : Forest := ⟨173,6,fun i => g173Y[i]?.getD (0,0),g173C,g173A,g173L,g173I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g173P6_0 : CutRow g173 6 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g173B6 : CutRow g173 6 0 1 := g173P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g173T : mixedTables g173 6 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g173 0 0
  · exact mixedEmpty g173 1 0
  · exact mixedEmpty g173 2 0
  · exact mixedEmpty g173 3 0
  · exact mixedEmpty g173 4 0
  · exact mixedEmpty g173 5 0
  · exact g173B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g173G : graphValid g173 (boundsBefore K171) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low173 : Lower true (varsX 173) (graphGoal 173) 7 := mixedLower (g:=g173) (i:=0) (hints:=1283) (before_sound K171 V171) g173G g173T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K173 := extendKnown K171 7 [(203,[33,101]),(211,[16,32,67,117,101]),(234,[80,16,33,66,100]),(242,[96,16,66,83,115,49])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V173 : Known true K173 := extend_ok (m:=173) V171 low173 (by decide +kernel)
def g179Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffc00ff87fc3fff00,0xffffffe257e300007fe0])),(BitVec.ofNat 152 (word80 [0x20a82a051048802a2a,0xa12004a546306318c63]))),((BitVec.ofNat 152 (word80 [0xfffff0007ffc3ffff,0xff1ffd9276c00f801f])),(BitVec.ofNat 152 (word80 [0x42308c262110088c0c,0x4c0444811226ca5294a5]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffff80003ffff,0xff001ffce8f541f0001f])),(BitVec.ofNat 152 (word80 [0x84c130480261113030,0x10588900e8d114a5294a]))),((BitVec.ofNat 152 (word80 [0xf0000000000003ffff,0xffffe0005f98fe0003e0])),(BitVec.ofNat 152 (word80 [0x701c070438221c040,0x60600e100b98d8c6318c]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffffffffc0000,0x3280bbffffc00])),(BitVec.ofNat 152 (word80 [0x80200800400020080,0x80801000000021084210]))),(0x0,0x0)]
def g179C : List ColumnInfo := [(1,0,178,0,5),(2,0,177,0,5),(16,0,163,0,5),(32,0,147,0,5),(18,0,161,0,4),(33,0,146,0,4)]
def g179A : List (List Nat) := [[],[65],[16,84],[16,80,64],[64,16,81],[64,81],[80],[80,65]]
def g179D4 := limbs80 #[#[0x9bd89544426d6215110,0x31826f625474]]
def g179D5 := limbs80 #[#[0x7c54443f2808857d4d40,0xfea8885f95110beaa221,0x7d4d40bfa8a81fb40502,0xcc8d018160c02faa3a07,0x882188201161080d176b,0x8118204c10001]]
def g179H5 (j : Nat) := if j=0 then 0x200d85100a9b0 else 0
def g179D6 := limbs80 #[#[0x540a0380ff40fd40fd10,0x2150c8543]]
def g179H6 := limbs80 #[#[0x80003610031100000140,0x19350800d0fc9704,0x85420d985dc700254000,0x61800712]]
def g179D7 (j : Nat) := if j=0 then 0x1605f else 0
def g179H7 := limbs80 #[#[0x600000191ba0018869,0x334002080000,0x30400e65c800b9003a8]]
def g179L : Nat → Packing
  | 4 => (3,3,3,0,0,4,0,g179D4)
  | 5 => (10,2,3,0,0,7,0,g179D5)
  | 6 => (3,1,3,0,0,6,0,g179D6)
  | 7 => (1,0,3,0,0,0,0,g179D7)
  | _ => emptyPacking
def g179I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 7 0 8 2 2 g179H5
  | 6 => lookupWord 4 29 3 10 4 2 g179H6
  | 7 => lookupWord 3 31 0 9 2 3 g179H7
  | _ => fun _ => none
def g179 : Forest := ⟨179,7,fun i => g179Y[i]?.getD (0,0),g179C,g179A,g179L,g179I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g179P4_0 : CutRow g179 4 0 3 := by
  apply checkedRow
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g179B4 : CutRow g179 4 0 3 := g179P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g179P5_0 : CutRow g179 5 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g179P5_1 : CutRow g179 5 1 9 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g179B5 : CutRow g179 5 0 10 := (@joinRow g179 5 0 1 9 g179P5_0 g179P5_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g179P6_0 : CutRow g179 6 0 3 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g179B6 : CutRow g179 6 0 3 := g179P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g179P7_0 : CutRow g179 7 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g179B7 : CutRow g179 7 0 1 := g179P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g179T : mixedTables g179 7 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g179 0 0
  · exact mixedEmpty g179 1 0
  · exact mixedEmpty g179 2 0
  · exact mixedEmpty g179 3 0
  · exact g179B4
  · exact g179B5
  · exact g179B6
  · exact g179B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g179G : graphValid g179 (boundsBefore K173) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low179 : Lower true (varsX 179) (graphGoal 179) 8 := mixedLower (g:=g179) (i:=0) (hints:=65605) (before_sound K173 V173) g179G g179T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K179 := extendKnown K173 8 [(179,[]),(182,[16,32,84])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V179 : Known true K179 := extend_ok (m:=179) V173 low179 (by decide +kernel)
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
theorem g229P7_0 : CutRow g229 7 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g229B7 : CutRow g229 7 0 1 := g229P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g229T : mixedTables g229 7 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g229 0 0
  · exact mixedEmpty g229 1 0
  · exact mixedEmpty g229 2 0
  · exact mixedEmpty g229 3 0
  · exact mixedEmpty g229 4 0
  · exact mixedEmpty g229 5 0
  · exact mixedEmpty g229 6 0
  · exact g229B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g229G : graphValid g229 (boundsBefore K179) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low229 : Lower true (varsX 229) (graphGoal 229) 8 := mixedLower (g:=g229) (i:=0) (hints:=1285) (before_sound K179 V179) g229G g229T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K229 := extendKnown K179 8 [(233,[48,114,32,80,101])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V229 : Known true K229 := extend_ok (m:=229) V179 low229 (by decide +kernel)
def g123Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3fffffc1ffff60ac8,0x4caee8000007f01fc07f])),(BitVec.ofNat 152 (word80 [0x280280084044060880,0x400ce80a142850a14285]))),((BitVec.ofNat 152 (word80 [0xfc003ffffffe021c2c,0x13d9d30003f800003f80])),(BitVec.ofNat 152 (word80 [0x304b04500208221c28,0x3c941264c993264c993]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffc0001ffffbf0cb,0x81210b01fc000fe0007f])),(BitVec.ofNat 152 (word80 [0x400c0160809009404a,0x12103142850a142850a]))),((BitVec.ofNat 152 (word80 [0xffffffffe0000824f7,0x691ab200000000003f80])),(BitVec.ofNat 152 (word80 [0x8290298014e04820d7,0x6812b2d9b366cd9b366c]))),((BitVec.ofNat 152 (word80 [0x93710,0xa28774fe00000fffc000])),(BitVec.ofNat 152 (word80 [0xe00e010700803700,0xa2821060c183060c1830]))),((BitVec.ofNat 152 (word80 [0x4c917,0x7e4005fffffff0000000])),(BitVec.ofNat 152 (word80 [0x30030021801008015,0x1c000481020408102040]))),(0x0,0x0),(0x0,0x0)]
def g123C : List ColumnInfo := [(0,16,105,2,8),(16,0,107,0,8),(1,0,122,0,7),(2,16,105,0,7),(8,0,115,0,7),(32,0,91,0,7),(64,0,59,0,6),(9,0,114,0,4),(33,0,90,0,4),(40,0,83,0,4)]
def g123A : List (List Nat) := [[],[83],[48],[48,80],[80,48],[80]]
def g123D4 (j : Nat) := if j=0 then 0x1a2b6460b5454120 else 0
def g123D5 := limbs80 #[#[0x50940483aa5954250120,0x483ca5515250120eab65,0x5915254120d697554940,0x54120e6b64549504839a,0xb6982d51504835add152,0x5d9544838ed935454120,0x4832ed9170d51208fb80,0x1d37059520a3d85d9354,0x8d01d345ca0d141c032e,0x8080002836294c]]
def g123H5 (j : Nat) := if j=0 then 0x3a8000 else 0
def g123D6 := limbs80 #[#[0x3b4a92a0907a94250120,0xfd2a4a02412fdd16548,0x837db2a80906f9655012,0x20fd6e4a8241fa549504,0x483bdaa2a09077954541,0x120df6c8a8241be59150,0x44833eb2aa8905fb7454,0x51209feecaa2413f5d95,0x544835fb26a8905f970d,0x591209faedaa2419f597,0x1654827ebaec8904ff75,0x59520b7ee8b2a417edc,0xd1654835e3a2ca906fb7,0x70995209fee8b2a41afd,0x5d3654827ebb4ca905f9,0xb7054950bf6e0a92a13f,0xfd93525433fb22a4a877,0xbf7458950afae9a92a19,0x3fdd162d427eba6c4a85,0x78a8431e4d85f258a401,0x5610fb7aba1b6d564309,0x75a2b74ea0cee5d288dc,0xee46ef5da1cde3b037bb,0x8178f049085f3f6ba9c,0x82141100f1e010649ce1,0x810000808205c7806102,0x80101c4080141c80801,0x400e0e2043820700400a,0x8604002005041020050,0x35040000a8]]
def g123H6 := limbs80 #[#[0xbe4e000861b305e8210,0xd09a5c00000f61e268a0,0x7a0400507000f2400506,0x80000000a00355000e2,0xd4d246c432c2210,0x123c516a5d8800000000,0x562200020c00]]
def g123D7 := limbs80 #[#[0xf59120fe54120fe50120,0xd9520bf59520bfd9120b,0x8950dfd4950df54950bf,0x120ff55120bf58b50bfd,0x20ff59520ff59120ffd5,0xff58950ff54950ff995,0x90ba2585a0c000ffd895,0xc9ce691865a144481023,0xb1c159079aa528ba107,0x648b3242c461f3906207,0x3186c55cc7149207c465,0x522105c731c4c4792217,0x54d62cc51e2cd41851b3,0x51c6185887105506cc4c,0x88710920789516245019,0xf1c065221624501c4195,0x60940c75540]]
def g123H7 := limbs80 #[#[0x3978905508c946840346,0x105631299000044524c0,0x83d323e295c2840768a,0x1e087896425acd124621,0x30000a14d08da4140ea6,0x8242fa8501bc4df5011,0x8990020d034400020272,0xa2084e000240a0000004,0x844c19d698885d12,0x404304c682702e08344b,0xc5a7c00101ba0b498a03,0x38404201522c01660e60,0x220074000623000781bc,0xc1880f0005803c3f2c34,0x1114448a15124933d]]
def g123D8 := limbs80 #[#[0xc79aa407fd43faa1fd20,0x98d13568298d131ea414,0x1ad046]]
def g123H8 := limbs80 #[#[0x9020000000204,0x10500,0xa2f000b10,0xa50d6260000000000000,0xe4000010f40,0xd06000000,0x100000000080436b0000,0x33,0x501000000000000000,0x0,0xd4100000,0x8700000000002860e611,0xa300007,0xe4700000000000,0xa09000,0x2032270003089079290,0x72400b00092100,0x30000000000050c16a]]
def g123D9 (j : Nat) := if j=0 then 0x1542317f else 0
def g123H9 := limbs80 #[#[0xeac88002402020800000,0xd4fb283]]
def g123L : Nat → Packing
  | 4 => (1,5,4,0,0,0,0,g123D4)
  | 5 => (13,4,4,0,0,7,0,g123D5)
  | 6 => (39,3,4,0,0,9,0,g123D6)
  | 7 => (18,2,4,0,0,10,0,g123D7)
  | 8 => (3,1,4,0,0,7,0,g123D8)
  | 9 => (1,0,4,0,0,0,0,g123D9)
  | _ => emptyPacking
def g123I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 5 0 6 0 2 g123H5
  | 6 => lookupWord 7 47 4 11 4 3 g123H6
  | 7 => lookupWord 18 83 6 13 6 3 g123H7
  | 8 => lookupWord 8 127 2 12 5 3 g123H8
  | 9 => lookupWord 2 13 0 9 2 3 g123H9
  | _ => fun _ => none
def g123 : Forest := ⟨123,9,fun i => g123Y[i]?.getD (0,0),g123C,g123A,g123L,g123I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P4_0 : CutRow g123 4 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g123B4 : CutRow g123 4 0 1 := g123P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P5_0 : CutRow g123 5 0 13 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g123B5 : CutRow g123 5 0 13 := g123P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P6_0 : CutRow g123 6 0 3 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P6_3 : CutRow g123 6 3 36 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g123B6 : CutRow g123 6 0 39 := (@joinRow g123 6 0 3 36 g123P6_0 g123P6_3)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P7_0 : CutRow g123 7 0 10 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P7_10 : CutRow g123 7 10 8 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g123B7 : CutRow g123 7 0 18 := (@joinRow g123 7 0 10 8 g123P7_0 g123P7_10)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P8_0 : CutRow g123 8 0 3 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g123B8 : CutRow g123 8 0 3 := g123P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P9_0 : CutRow g123 9 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g123B9 : CutRow g123 9 0 1 := g123P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123T : mixedTables g123 9 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g123 0 0
  · exact mixedEmpty g123 1 0
  · exact mixedEmpty g123 2 0
  · exact mixedEmpty g123 3 0
  · exact g123B4
  · exact g123B5
  · exact g123B6
  · exact g123B7
  · exact g123B8
  · exact g123B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123G : graphValid g123 (boundsBefore K229) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low123 : Lower true (varsX 123) (graphGoal 123) 10 := mixedLower (g:=g123) (i:=0) (hints:=65603) (before_sound K229 V229) g123G g123T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K123 := extendKnown K229 10 [(123,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V123 : Known true K123 := extend_ok (m:=123) V229 low123 (by decide +kernel)
def g187Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3fffffc1ffff64acc,0x4aee8000007f01fc07f])),(BitVec.ofNat 152 (word80 [0x280280084044060884,0xce80a142850a14285]))),((BitVec.ofNat 152 (word80 [0xfc003ffffffe029c28,0x13d9d30003f800003f80])),(BitVec.ofNat 152 (word80 [0x304b04500208229c28,0x3c940264c993264c993]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffc0001ffffbf0cb,0xa1210b0000000fe0007f])),(BitVec.ofNat 152 (word80 [0x420c2160909009c04b,0x212103952a54a952a54a]))),((BitVec.ofNat 152 (word80 [0xffffffffe0000824f7,0x491ab201fc0000003f80])),(BitVec.ofNat 152 (word80 [0x8090098004e04820d6,0x4012b258b162c58b162c]))),((BitVec.ofNat 152 (word80 [0x93710,0xa28774fe00000fffc000])),(BitVec.ofNat 152 (word80 [0xe00e010700803710,0x82821060c183060c1830]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x4c917,0x7e4005fffffff0000000])),(BitVec.ofNat 152 (word80 [0x30030021801004001,0x3c000581020408102040]))),(0x0,0x0)]
def g187C : List ColumnInfo := [(8,0,179,0,8),(1,0,186,0,7),(2,0,185,0,7),(16,0,171,0,7),(32,0,155,0,7),(0,2,41,144,6),(0,8,146,33,6),(0,16,41,130,6),(128,0,59,0,6),(1,8,146,32,5),(2,16,41,128,5),(18,0,169,0,5),(32,8,146,1,5),(128,2,41,16,5),(128,16,41,2,5),(33,0,146,0,4),(33,8,146,0,4),(130,0,41,0,4),(130,16,41,0,4)]
def g187A : List (List Nat) := [[],[65],[80],[80,65]]
def g187D5 := limbs80 #[#[0xd8b5150333dcf6254540,0x1832edd370595408ed87,0x1004003]]
def g187D6 := limbs80 #[#[0x276baec4a07395454140,0xf76e8a8281ee5515050,0x377b12a2a06ef624c54,0x40bf2e1a8a8177dcd515,0x5027ebb6a2a06ef62d45,0x150bf6e0aa2a1bedc165,0xb0027fba2c1a8f7b7055,0xc632c1448c3f1c0c4441,0xf142207803c687401e4d,0x68811004238040306071,0x81a882040707002a30,0x201100780402060]]
def g187H6 (j : Nat) := if j=0 then 0xa7e02c else 0
def g187D7 := limbs80 #[#[0xb54b50db54950bbd8940,0x58b51b7d8d51bb58b50d,0x9540fe54140bfd9110bb,0x150df55150fb54950bf5,0x51bf59350bfd9150dfd5,0xff54540ff4c540bf583,0xff59150ff55150ffd454,0x881198520a400ffd9150,0x1d066570555253f0d32a,0x70abdadba927b94a1b80,0xc63b10d202e3c5103411,0x843e01a2c11a3031a402,0x3c10468b2b1c210245c9,0xc160203478b80410143e,0x1b812411470d201870a0,0x1101878e13070241a38e,0x10840e386900f0070a0c,0x8a8a0c01614542131cac,0x2a2830100f1d1c180442,0x1040240402c02080624]]
def g187H7 := limbs80 #[#[0x1801e3c0495800007c04,0x515e6fb00050ba,0x830000000106513a,0x5800f5000000cf6a8000,0x382002d9a27900]]
def g187D8 := limbs80 #[#[0xf50fea87f503fa21ed52,0x685400ffa8ff547fa63f,0x2238d4069c439c8c0481,0x389020408a8c180d1e30,0x92388e04d80720714182,0xa40a180b34610e060345,0x12a38022079038458121,0x92]]
def g187H8 := limbs80 #[#[0x180d10001630021,0x0,0x1868000000000000000,0x88000000000000000,0xb0b20800000000,0x4000000c06c722200109,0x6040000000049,0x485a96000004090,0x30f41c00000000000,0x702f2600000000001ec,0x4900000000000c0e0000,0x503000000007,0x16700000000000306,0x50b0000004500000,0xd620]]
def g187D9 (j : Nat) := if j=0 then 0x41882017f else 0
def g187H9 := limbs80 #[#[0xb2803dd41000002,0x100000719300,0xdc80000004a000000000,0x71d120000180c800,0x0,0x4c00000000001c300000,0x4bc0000007]]
def g187L : Nat → Packing
  | 5 => (3,4,5,0,0,4,0,g187D5)
  | 6 => (14,3,5,0,0,9,0,g187D6)
  | 7 => (21,2,5,0,0,10,0,g187D7)
  | 8 => (8,1,5,0,0,9,0,g187D8)
  | 9 => (1,0,5,0,0,0,0,g187D9)
  | _ => emptyPacking
def g187I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 5 0 6 2 0 g187H6
  | 7 => lookupWord 5 37 3 10 4 2 g187H7
  | 8 => lookupWord 7 107 2 11 5 2 g187H8
  | 9 => lookupWord 3 59 2 9 3 2 g187H9
  | _ => fun _ => none
def g187 : Forest := ⟨187,9,fun i => g187Y[i]?.getD (0,0),g187C,g187A,g187L,g187I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P5_0 : CutRow g187 5 0 3 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g187B5 : CutRow g187 5 0 3 := g187P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P6_0 : CutRow g187 6 0 2 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P6_2 : CutRow g187 6 2 12 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g187B6 : CutRow g187 6 0 14 := (@joinRow g187 6 0 2 12 g187P6_0 g187P6_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P7_0 : CutRow g187 7 0 6 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P7_6 : CutRow g187 7 6 9 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P7_15 : CutRow g187 7 15 6 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g187B7 : CutRow g187 7 0 21 := (@joinRow g187 7 0 6 15 g187P7_0 (@joinRow g187 7 6 9 6 g187P7_6 g187P7_15))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P8_0 : CutRow g187 8 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P8_1 : CutRow g187 8 1 7 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g187B8 : CutRow g187 8 0 8 := (@joinRow g187 8 0 1 7 g187P8_0 g187P8_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P9_0 : CutRow g187 9 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g187B9 : CutRow g187 9 0 1 := g187P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187T : mixedTables g187 9 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g187 0 0
  · exact mixedEmpty g187 1 0
  · exact mixedEmpty g187 2 0
  · exact mixedEmpty g187 3 0
  · exact mixedEmpty g187 4 0
  · exact g187B5
  · exact g187B6
  · exact g187B7
  · exact g187B8
  · exact g187B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187G : graphValid g187 (boundsBefore K123) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low187 : Lower true (varsX 187) (graphGoal 187) 10 := mixedLower (g:=g187) (i:=0) (hints:=65603) (before_sound K123 V123) g187G g187T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K187 := extendKnown K123 10 [(187,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V187 : Known true K187 := extend_ok (m:=187) V123 low187 (by decide +kernel)
def g219Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xc007ffffe0ffff72a6,0xa10baa00000fc003f03f])),(BitVec.ofNat 152 (word80 [0x82500a004204403202,0x21032a05145145145145]))),((BitVec.ofNat 152 (word80 [0xfff800ffffffe03d4a,0x8666308003f000fc0fc0])),(BitVec.ofNat 152 (word80 [0x602c02800082350a,0x844210030c30c30c30c3]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffff0000ffffad84,0xb85846c000003f00003f])),(BitVec.ofNat 152 (word80 [0x2084308b0489000d84,0x985804eaaaaaaaaaaaaa]))),((BitVec.ofNat 152 (word80 [0xffffffffff0000804d,0x6156adc0fc0000000fc0])),(BitVec.ofNat 152 (word80 [0xb01402c002e048045,0x2114a9dc71c71c71c71c]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x9171,0x18b1d83f00003ffff000])),(BitVec.ofNat 152 (word80 [0xc0180300830088071,0x20c010410410410410]))),((BitVec.ofNat 152 (word80 [0x4e93,0x4f80057fffffc0000000])),(BitVec.ofNat 152 (word80 [0x300600c010c0104880,0x4a800420820820820820]))),(0x0,0x0)]
def g219C : List ColumnInfo := [(1,0,218,0,7),(2,0,217,0,7),(8,0,211,0,7),(16,0,203,0,7),(64,0,155,0,7),(128,0,91,0,7),(0,8,146,65,6),(0,16,73,130,6),(1,8,146,64,5),(2,16,73,128,5),(9,0,210,0,5),(17,0,202,0,5),(24,0,195,0,5),(64,8,146,1,5),(72,0,147,0,5),(128,16,73,2,5),(144,0,75,0,5),(3,0,216,0,4),(25,0,194,0,4),(26,0,193,0,4),(65,0,146,0,4),(65,8,146,0,4),(66,0,153,0,4),(73,0,146,0,4),(129,0,90,0,4),(130,0,73,0,4),(130,16,73,0,4),(146,0,73,0,4)]
def g219A : List (List Nat) := [[],[16,67,118]]
def g219D5 := limbs80 #[#[0x55140443cc5515150110,0x443cc5514154110e3965,0x5537154140e396455150,0x50d50ccf73d89515034e,0x40b6785b54603c6e0154,0x40]]
def g219D6 := limbs80 #[#[0x3b4a92a08870d5450d52,0x9daebb1281ce5515050,0x43f8a8a808871d5450d5,0x10df2caa0221ee551404,0x442fcbaa80886fb65501,0x110ef2a8a8221fc50550,0x4437db22a0886f96454,0x5110d7ac8aa2217edd15,0x644427fbb2a8884fd765,0x545209faebb22213fdd5,0x951502fdb8aa0a05df73,0x3d8940e7aa8a8a81bbd8,0xc165503ddb82a8a06ed5,0x54505509fee2b2a81bed,0x55361543b6a92c2a873d,0xb70551509fae9b0aa19f,0xf5c764542fdb82c8a877,0x6f7155152edae2aa2a53,0x5a0f0160027eb8ec0aa7,0x123f0de340c22b0961c0,0xaa6518e5a15251136481,0x127d1e6781da731c6701,0x929f266962529121e862,0x1f8c605441a150ab6aa2,0x6c01a101b102c705150f,0x4041011511098e88204c,0x5086811a150854880430,0x30210541421504541150,0x1c0c2060208007060,0x1817150c541000a304,0x2050401a04643e8e8440,0x21a058c6820703086054],#[0x1c0c]]
def g219H6 := limbs80 #[#[0x35ce00e316590100008,0x8400902b0000520]]
def g219D7 := limbs80 #[#[0x350d52db54950bbd8940,0x90e52db55152f390d52f,0x4910fe54110fe50110f3,0x110bf59110fb94910fb5,0x40ef55140fe54140bfd9,0xf750d50bfd8550bf595,0xbfd9150df55150f790d5,0xfd8154fbd8552bfd8552,0x54520ff59110ff55110b,0x550ff54d40ff54540ff,0xd42ff59150ff58550ff5,0xffd8154ff58154ff54,0x1f8314550880da164180,0x686d001de35c5c0a712c,0x55962fc5a6a8d47a7b49,0x21c2180cf91e4b996fcd,0xc3003441a5eca291d1ce,0x19a2a118c38c795172e3,0x548483c38c795122a32a,0x841a18b914f8d1412a3c,0x4a5c4c72529510d98228,0x62c460870a0cb9522092,0xcc474a5442e1c2832a44,0xc60383025ca8d1d2950,0x6ca8468a846c3040468c,0x30260a8a623261f0120c,0x228d143838a2210d1838,0x2a4438a1c1812a2a3522,0x18a0c19628444224831a,0x52c242201c34708c9411,0x8a8664c111e8d08c68c1,0x52a118445431c182308]]
def g219H7 := limbs80 #[#[0xa4b0240f4c9690a40002,0x1da6323001c500068a,0xa27d1a00e9a00,0xec8000aa0000000,0x3a200000000000000000,0xf0000000071000162c00,0x9b704f10101c,0x290000003,0x93e00000000000,0x2e0000058f00000,0x0,0x147656000001638,0x3c2096d30000ce792,0x8403695000001a580000,0x640000004300000043be,0x38800000282800532000,0x120c003e3e2200000,0x3868000000000000]]
def g219D8 := limbs80 #[#[0xd30fe907f443dca5ed52,0xa5fd42fe997f543fa81f,0xd257240a82a007f553fa,0xf8e11551b557aae4fa04,0x22324024f8c28455c608,0x4b3c5961352111065922,0x81495c70a58e15472222,0x10c3492046009228633c,0x83e3842148347953388,0x218233e23451]]
def g219H8 := limbs80 #[#[0x998221021188101150,0x8859110e32c0a00f3e00,0xc7f07a4ba354af12d616,0x85ce4918001655852,0x2840074ba0487400000,0x6e0f0e1001817a442000,0xc200090c2464e000ac0a,0xa19626001e860700110e,0xee1c001cb610b89e6b86,0x29b36ad90b7ac0022904,0x8f3]]
def g219D9 (j : Nat) := if j=0 then 0xa4188201bf else 0
def g219H9 := limbs80 #[#[0xc8800000090,0x3200000000068401e7,0xd0000000000000000044,0x18000000000000000159,0x21200000,0x7e00000000cc00000,0x800750000159007952a0,0x1c0f80024600000022]]
def g219L : Nat → Packing
  | 5 => (7,4,5,0,0,6,0,g219D5)
  | 6 => (38,3,5,0,0,10,0,g219D6)
  | 7 => (34,2,5,0,0,11,0,g219D7)
  | 8 => (11,1,5,0,0,9,0,g219D8)
  | 9 => (1,0,5,0,0,0,0,g219D9)
  | _ => emptyPacking
def g219I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 2 17 2 8 3 1 g219H6
  | 7 => lookupWord 12 127 3 11 6 1 g219H7
  | 8 => lookupWord 13 67 6 11 6 1 g219H8
  | 9 => lookupWord 4 71 2 9 4 1 g219H9
  | _ => fun _ => none
def g219 : Forest := ⟨219,9,fun i => g219Y[i]?.getD (0,0),g219C,g219A,g219L,g219I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P5_0 : CutRow g219 5 0 7 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g219B5 : CutRow g219 5 0 7 := g219P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P6_0 : CutRow g219 6 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P6_1 : CutRow g219 6 1 4 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P6_5 : CutRow g219 6 5 33 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g219B6 : CutRow g219 6 0 38 := (@joinRow g219 6 0 1 37 g219P6_0 (@joinRow g219 6 1 4 33 g219P6_1 g219P6_5))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P7_0 : CutRow g219 7 0 6 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P7_6 : CutRow g219 7 6 17 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P7_23 : CutRow g219 7 23 11 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g219B7 : CutRow g219 7 0 34 := (@joinRow g219 7 0 6 28 g219P7_0 (@joinRow g219 7 6 17 11 g219P7_6 g219P7_23))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P8_0 : CutRow g219 8 0 2 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P8_2 : CutRow g219 8 2 9 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g219B8 : CutRow g219 8 0 11 := (@joinRow g219 8 0 2 9 g219P8_0 g219P8_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P9_0 : CutRow g219 9 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g219B9 : CutRow g219 9 0 1 := g219P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219T : mixedTables g219 9 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g219 0 0
  · exact mixedEmpty g219 1 0
  · exact mixedEmpty g219 2 0
  · exact mixedEmpty g219 3 0
  · exact mixedEmpty g219 4 0
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
theorem low219 : Lower true (varsX 219) (graphGoal 219) 10 := mixedLower (g:=g219) (i:=0) (hints:=65603) (before_sound K187 V187) g219G g219T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K219 := extendKnown K187 10 [(219,[]),(250,[80,32])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V219 : Known true K219 := extend_ok (m:=219) V187 low219 (by decide +kernel)
def g235Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfffc01ffc3ffffffa2,0xa4b358000f8000f83ff])),(BitVec.ofNat 152 (word80 [0x2814028804002002,0xa0b1404210842108421]))),((BitVec.ofNat 152 (word80 [0x1ffffe0003fe1ff049,0x38c78e801f0001f00000])),(BitVec.ofNat 152 (word80 [0x42b0182b1028424209,0x38c78c9ce739ce739ce7]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1ffffffffc001ffffd,0xa141580000003e007c1f])),(BitVec.ofNat 152 (word80 [0x90c2210c02309080fd,0x140484a5294a5294a52]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1fffffffffffe00010,0xfe246883e007c0007fe0])),(BitVec.ofNat 152 (word80 [0x30040300040030400,0xf0242090842108421084]))),((BitVec.ofNat 152 (word80 [0xe0000000000000000e,0x1132807c0007ffff8000])),(BitVec.ofNat 152 (word80 [0x40080400080040000,0x21084210842108]))),((BitVec.ofNat 152 (word80 [0xc1,0x459c477ffff800000000])),(BitVec.ofNat 152 (word80 [0x1803018023011808c0,0x5104342108421084210]))),(0x0,0x0)]
def g235C : List ColumnInfo := [(2,0,233,0,8),(8,0,227,0,8),(128,0,107,0,8),(1,0,234,0,7),(32,0,203,0,7),(64,0,171,0,7),(0,2,41,192,6),(3,0,232,0,5),(33,0,202,0,5),(64,2,41,128,5),(65,0,170,0,4),(96,0,139,0,4)]
def g235A : List (List Nat) := [[],[80]]
def g235D5 (j : Nat) := if j=0 then 0x2f8e097350110 else 0
def g235D6 := limbs80 #[#[0x379b1a80887b14350110,0x9dee4b2261e650d404c,0x377b92c8987f1735011,0x471eda9652017bdc9635,0x2d03f211a0ae22790b61,0x2c98f970104f1e4204e,0x41622]]
def g235H6 (j : Nat) := if j=0 then 0x2 else 0
def g235D7 := limbs80 #[#[0xdd8d10bd58d10fc50110,0x59130fe50130fd50d10b,0x8d40bfd8d40ef50d40bf,0xa379688a331205400ff5,0x479122141e98e448d388,0x3298c79122e2a64388a,0x41656046588c52a4e391,0x618e450a5942e18e4a46,0x16522408a]]
def g235H7 := limbs80 #[#[0xe4e60000b55078e25190,0x5300]]
def g235D8 := limbs80 #[#[0x88a4b807f503fa61f510,0x1ca3846481807356838c,0x2a851c612]]
def g235H8 := limbs80 #[#[0xc800000020600,0x7a00001250000000,0x4d43e60100000000001c,0x128802]]
def g235D9 (j : Nat) := if j=0 then 0x5431201bf else 0
def g235H9 := limbs80 #[#[0x80000e00000000002849,0x6a5]]
def g235L : Nat → Packing
  | 5 => (1,4,4,0,0,0,0,g235D5)
  | 6 => (7,3,4,0,0,8,0,g235D6)
  | 7 => (9,2,4,0,0,9,0,g235D7)
  | 8 => (3,1,4,0,0,7,0,g235D8)
  | 9 => (1,0,4,0,0,0,0,g235D9)
  | _ => emptyPacking
def g235I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 2 0 4 0 0 g235H6
  | 7 => lookupWord 2 11 4 8 3 1 g235H7
  | 8 => lookupWord 2 29 0 9 4 1 g235H8
  | 9 => lookupWord 1 13 0 7 2 1 g235H9
  | _ => fun _ => none
def g235 : Forest := ⟨235,9,fun i => g235Y[i]?.getD (0,0),g235C,g235A,g235L,g235I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P5_0 : CutRow g235 5 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g235B5 : CutRow g235 5 0 1 := g235P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P6_0 : CutRow g235 6 0 4 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P6_4 : CutRow g235 6 4 3 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g235B6 : CutRow g235 6 0 7 := (@joinRow g235 6 0 4 3 g235P6_0 g235P6_4)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P7_0 : CutRow g235 7 0 3 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P7_3 : CutRow g235 7 3 5 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P7_8 : CutRow g235 7 8 1 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g235B7 : CutRow g235 7 0 9 := (@joinRow g235 7 0 3 6 g235P7_0 (@joinRow g235 7 3 5 1 g235P7_3 g235P7_8))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P8_0 : CutRow g235 8 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P8_1 : CutRow g235 8 1 2 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g235B8 : CutRow g235 8 0 3 := (@joinRow g235 8 0 1 2 g235P8_0 g235P8_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P9_0 : CutRow g235 9 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g235B9 : CutRow g235 9 0 1 := g235P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235T : mixedTables g235 9 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g235 0 0
  · exact mixedEmpty g235 1 0
  · exact mixedEmpty g235 2 0
  · exact mixedEmpty g235 3 0
  · exact mixedEmpty g235 4 0
  · exact g235B5
  · exact g235B6
  · exact g235B7
  · exact g235B8
  · exact g235B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235G : graphValid g235 (boundsBefore K219) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low235 : Lower true (varsX 235) (graphGoal 235) 10 := mixedLower (g:=g235) (i:=0) (hints:=99) (before_sound K219 V219) g235G g235T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K235 := extendKnown K219 10 [(235,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V235 : Known true K235 := extend_ok (m:=235) V219 low235 (by decide +kernel)
def g243Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xff801ffffffff818e7,0x982a5000000fc003ffc0])),(BitVec.ofNat 152 (word80 [0x1505405024001118c3,0x982040c30c30c30c30c3]))),((BitVec.ofNat 152 (word80 [0xffffe007fe1fffbb0a,0x3491700003f000fc003f])),(BitVec.ofNat 152 (word80 [0x460182600841203a02,0x4817145145145145145]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffff8001fffd03d,0x3b712000fc000000003f])),(BitVec.ofNat 152 (word80 [0x98260882b08a40403d,0x3b70069a69a69a69a69a]))),((BitVec.ofNat 152 (word80 [0xffffffffffe000462a,0x89c7903f00003f000fc0])),(BitVec.ofNat 152 (word80 [0xe0080300c003820628,0x1c3930c30c30c30c30c]))),((BitVec.ofNat 152 (word80 [0x4984,0x67ac8fc000003ffff000])),(BitVec.ofNat 152 (word80 [0x300c03010c044104,0x620c0410410410410410]))),((BitVec.ofNat 152 (word80 [0x2651,0x42404fffffffc0000000])),(BitVec.ofNat 152 (word80 [0x4010040010000000,0x820820820820820]))),(0x0,0x0)]
def g243C : List ColumnInfo := [(2,0,241,0,8),(16,0,227,0,8),(64,0,179,0,8),(1,0,242,0,7),(32,0,211,0,7),(128,0,115,0,7),(33,0,210,0,5),(129,0,114,0,4),(160,0,83,0,4)]
def g243A : List (List Nat) := [[],[80]]
def g243D6 := limbs80 #[#[0xe3c1243e437595354130,0x5]]
def g243D7 := limbs80 #[#[0xf54d50bf59530fe54130,0x42a00ff58d50bfd8d50d,0xc32187c70572186ae8a5,0x481c5c705328c82071b1,0x81c60d4c70c871]]
def g243H7 (j : Nat) := if j=0 then 0xf0 else 0
def g243D8 := limbs80 #[#[0xa38c2461a403faa1fd30,0x1e851c6121c]]
def g243H8 := limbs80 #[#[0x8300620000440000,0x910018]]
def g243D9 (j : Nat) := if j=0 then 0x5431021bf else 0
def g243H9 (j : Nat) := if j=0 then 0x2fe78000 else 0
def g243L : Nat → Packing
  | 6 => (1,3,4,0,0,0,0,g243D6)
  | 7 => (5,2,4,0,0,8,0,g243D7)
  | 8 => (2,1,4,0,0,6,0,g243D8)
  | 9 => (1,0,4,0,0,0,0,g243D9)
  | _ => emptyPacking
def g243I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 1 2 0 4 0 0 g243H7
  | 8 => lookupWord 1 17 0 8 3 1 g243H8
  | 9 => lookupWord 1 5 0 6 1 1 g243H9
  | _ => fun _ => none
def g243 : Forest := ⟨243,9,fun i => g243Y[i]?.getD (0,0),g243C,g243A,g243L,g243I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P6_0 : CutRow g243 6 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g243B6 : CutRow g243 6 0 1 := g243P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P7_0 : CutRow g243 7 0 4 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P7_4 : CutRow g243 7 4 1 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g243B7 : CutRow g243 7 0 5 := (@joinRow g243 7 0 4 1 g243P7_0 g243P7_4)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P8_0 : CutRow g243 8 0 2 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g243B8 : CutRow g243 8 0 2 := g243P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P9_0 : CutRow g243 9 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g243B9 : CutRow g243 9 0 1 := g243P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243T : mixedTables g243 9 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g243 0 0
  · exact mixedEmpty g243 1 0
  · exact mixedEmpty g243 2 0
  · exact mixedEmpty g243 3 0
  · exact mixedEmpty g243 4 0
  · exact mixedEmpty g243 5 0
  · exact g243B6
  · exact g243B7
  · exact g243B8
  · exact g243B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243G : graphValid g243 (boundsBefore K235) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low243 : Lower true (varsX 243) (graphGoal 243) 10 := mixedLower (g:=g243) (i:=0) (hints:=65605) (before_sound K235 V235) g243G g243T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K243 := extendKnown K235 10 [(243,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V243 : Known true K243 := extend_ok (m:=243) V235 low243 (by decide +kernel)
def g249Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xf801fffff83fffffc8,0xd60a4540007c00f83ff])),(BitVec.ofNat 152 (word80 [0x9024010090800102c0,0x8400054210842108421]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffe007fffc1fffd97,0xa1015784000001f07c1f])),(BitVec.ofNat 152 (word80 [0x24090a412005020112,0xa10147025294a5294a52]))),((BitVec.ofNat 152 (word80 [0xffffff800001ff80d7,0xc5fc404800f800000000])),(BitVec.ofNat 152 (word80 [0xc1304c15c1085408c7,0x85fc4049ef7bdef7bdef]))),((BitVec.ofNat 152 (word80 [0xfffffffffffe000021,0x2ed47a201f003e007fe0])),(BitVec.ofNat 152 (word80 [0x4010060000181021,0x4843800842108421084]))),((BitVec.ofNat 152 (word80 [0x44,0x903f89b3e0003fff8000])),(BitVec.ofNat 152 (word80 [0x18060180210602004,0x103880a1084210842108]))),((BitVec.ofNat 152 (word80 [0x33a,0x528a034bffffc0000000])),(BitVec.ofNat 152 (word80 [0x60180600421804118,0x42020302108421084210]))),(0x0,0x0)]
def g249C : List ColumnInfo := [(0,16,105,128,8),(8,0,241,0,8),(16,0,233,0,8),(1,0,248,0,7),(32,0,217,0,7),(64,0,185,0,7),(128,16,105,0,7),(33,0,216,0,4),(65,0,184,0,4),(96,0,153,0,4)]
def g249A : List (List Nat) := [[],[101],[80],[80,96],[96,80],[96]]
def g249D6 := limbs80 #[#[0x27bb8ac8987994350130,0xdeee2b22617ddc5644c,0x820bc927187d86bf1180,0x3901e01e3e5c03e5d]]
def g249D7 := limbs80 #[#[0xfd9130bf59130fe50130,0x690884603600ff59130b,0x2481f2c761881c3cb157,0x78d1572c08572c761c5,0x92]]
def g249H7 (j : Nat) := if j=0 then 0x6e401c0 else 0
def g249D8 (j : Nat) := if j=0 then 0xf2a9071b0ffd30 else 0
def g249H8 (j : Nat) := if j=0 then 0x53c10000206248 else 0
def g249D9 (j : Nat) := if j=0 then 0x5423161bf else 0
def g249H9 (j : Nat) := if j=0 then 0x93c0000700000000 else 0
def g249L : Nat → Packing
  | 6 => (4,3,4,0,0,7,0,g249D6)
  | 7 => (4,2,4,0,0,8,0,g249D7)
  | 8 => (1,1,4,0,0,0,0,g249D8)
  | 9 => (1,0,4,0,0,0,0,g249D9)
  | _ => emptyPacking
def g249I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 1 5 0 6 2 0 g249H7
  | 8 => lookupWord 1 7 0 8 2 2 g249H8
  | 9 => lookupWord 1 17 0 6 0 2 g249H9
  | _ => fun _ => none
def g249 : Forest := ⟨249,9,fun i => g249Y[i]?.getD (0,0),g249C,g249A,g249L,g249I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g249P6_0 : CutRow g249 6 0 2 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g249P6_2 : CutRow g249 6 2 2 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g249B6 : CutRow g249 6 0 4 := (@joinRow g249 6 0 2 2 g249P6_0 g249P6_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g249P7_0 : CutRow g249 7 0 3 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g249P7_3 : CutRow g249 7 3 1 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g249B7 : CutRow g249 7 0 4 := (@joinRow g249 7 0 3 1 g249P7_0 g249P7_3)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g249P8_0 : CutRow g249 8 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g249B8 : CutRow g249 8 0 1 := g249P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g249P9_0 : CutRow g249 9 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g249B9 : CutRow g249 9 0 1 := g249P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g249T : mixedTables g249 9 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g249 0 0
  · exact mixedEmpty g249 1 0
  · exact mixedEmpty g249 2 0
  · exact mixedEmpty g249 3 0
  · exact mixedEmpty g249 4 0
  · exact mixedEmpty g249 5 0
  · exact g249B6
  · exact g249B7
  · exact g249B8
  · exact g249B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g249G : graphValid g249 (boundsBefore K243) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low249 : Lower true (varsX 249) (graphGoal 249) 10 := mixedLower (g:=g249) (i:=0) (hints:=458755) (before_sound K243 V243) g249G g249T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K249 := extendKnown K243 10 [(249,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V249 : Known true K249 := extend_ok (m:=249) V243 low249 (by decide +kernel)
def g251Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xff000000ff00f,0xf00ff00864431431bf6b])),(BitVec.ofNat 152 (word80 [0x505050505050505050,0x50505008200114109d00]))),((BitVec.ofNat 152 (word80 [0xff000000ff00000,0xff00041b88498cdcf10])),(BitVec.ofNat 152 (word80 [0x313131313131313131,0x31313040a880984d8710]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xff0000ff0,0xff491c018e30e73f8])),(BitVec.ofNat 152 (word80 [0xa8a8a8a8a8a8a8a8a8,0xa8a8a491c00881046210]))),((BitVec.ofNat 152 (word80 [0xff000000000000000,0xff0091e031f03f07c10])),(BitVec.ofNat 152 (word80 [0xc6c6c6c6c6c6c6c6c6,0xc6c6c91a031f03b07800]))),((BitVec.ofNat 152 (word80 [0xf000000ff000000fff,0xf00001e003e003ff80a5])),(BitVec.ofNat 152 (word80 [0x30303030303030303,0x3030140018002e90000]))),((BitVec.ofNat 152 (word80 [0xffffffff000,0xe0003fffc0000c6])),(BitVec.ofNat 152 (word80 [0x40404040404040404,0x4040800023640000000]))),((BitVec.ofNat 152 (word80 [0xfffffff00000000000,0xffffc0000000000])),(BitVec.ofNat 152 (word80 [0x80808080808080808,0x80806a5540000000000]))),(0x0,0x0)]
def g251C : List ColumnInfo := [(1,0,250,0,10),(2,0,249,0,10),(8,0,243,0,10),(16,0,235,0,10),(32,0,219,0,10),(64,0,187,0,10),(128,0,123,0,10),(0,16,105,130,9),(2,16,105,128,8),(10,0,241,0,8),(18,0,233,0,8),(24,0,227,0,8),(72,0,179,0,8),(128,16,105,2,8),(144,0,107,0,8),(0,2,41,208,7),(0,8,146,97,7),(3,0,248,0,7),(9,0,242,0,7),(17,0,234,0,7),(26,0,225,0,7),(33,0,218,0,7),(34,0,217,0,7),(40,0,211,0,7),(48,0,203,0,7),(65,0,186,0,7),(66,0,185,0,7),(80,0,171,0,7),(96,0,155,0,7),(129,0,122,0,7),(130,0,105,0,7),(130,16,105,0,7),(136,0,115,0,7),(146,0,105,0,7),(160,0,91,0,7),(1,8,146,96,6),(1,16,104,130,6),(8,16,97,130,6),(16,2,41,192,6),(32,8,146,65,6),(32,16,73,130,6),(64,2,41,144,6),(64,8,146,33,6),(64,16,41,130,6),(128,2,41,80,6),(192,0,59,0,6),(11,0,240,0,5),(33,8,146,64,5),(41,0,210,0,5),(49,0,202,0,5),(65,8,146,32,5),(73,0,178,0,5),(74,0,177,0,5),(88,0,163,0,5),(96,8,146,1,5),(104,0,147,0,5),(192,2,41,16,5),(35,0,216,0,4),(57,0,194,0,4),(67,0,184,0,4),(97,0,146,0,4),(97,8,146,0,4),(98,0,153,0,4),(105,0,146,0,4),(131,0,104,0,4),(131,16,104,0,4),(137,0,114,0,4),(138,16,97,0,4),(161,0,90,0,4),(162,0,73,0,4),(162,16,73,0,4),(168,0,83,0,4),(194,0,41,0,4),(194,16,41,0,4),(0,512,224,3,6),(0,513,224,1,5),(0,514,224,1,5),(0,515,224,1,5),(0,516,228,1,8),(0,517,224,1,5),(0,518,224,1,5),(0,519,224,1,5),(0,520,228,0,7),(0,521,228,0,7),(0,522,182,0,8),(0,523,228,0,7),(0,524,224,3,6),(0,525,224,1,5),(0,526,224,1,5)]
def g251A : List (List Nat) := [[],[80]]
def g251D5 := limbs80 #[#[0xa981691a0658825d540,0x6981695a0658825d540e,0x30e0]]
set_option maxRecDepth 16000 in
def g251D6 := limbs80 #[#[0x81b82691a05955358940,0x550307454740cbacab12,0x2eaa064a9a4681962097,0x6258110c8d34ad032c41,0xaa2a0241e8a61584551,0x16558551503f10b2a84b,0xd02cab12a2a06e31a468,0xc1a4e456558950dc5348,0x1d12cac22c2a822139ae,0xa2bb4619545895044373,0xd8d16ed32a8b12a0887,0x221a3aee986dd1625411,0x61443535d2b0ac22c4b0,0x12c28877239055152509,0x96150120ec6720b2aa8a,0xa12c2a0241d625d79350,0x4d4258540483ac5baf26,0xbc9a84b0a8090738985e,0x6d7935096150120e7170,0x14c2acaa12c2a02415e2,0x770b935515258540483d,0x20ee1726aa284b0aa090,0x8241d525d39354961541,0x550483aa5ba726a92c2a,0xb0aa090734984e4d5258,0x496154120e69709c9aa4,0xac0ac2a82819d2693935,0x5539358550503719d22c,0xe4aa726b0aa0a0751972,0x660954e4d6154140ea36,0x98dc12a9c9ac2a8281cc,0x7c2bb15d95458950503],#[0x140f45762c32a8b12a0a,0xa8281b8a685a45956254,0x9550503715d0b48b2ac4,0x2b2aa0a06e3161693915,0x5917158140dc52c4d272,0xeab22e2b028172aec975,0x12897559160503a1dcaa,0x343d12eab22c0a06ca9a,0x1a684a25d56558140d95,0x3634d0f44baacab0281b,0xa064e991698925d56050,0x8140d95368d3124baac0,0x6b1281b1a6d5a6249755,0x54d62503f04d2340b2aa,0xcaa9ac4a07e0bb468165,0x75955358940f89760d3a,0x341c8acab1281e132e1a,0xa12a19759562503354ca,0x32ecca320b2aa6a060ef,0xb1a6c1a62497559540ec,0x3236c8b4c492eab2a81,0xaa068e9b069882605755,0x5d540d1cb62d3104c0ae,0x2baa81a1b6d5a620981,0x6209755030775cb4c413,0x32c412eaa074a9a46819,0xa5658825d540e8d34ad0,0xb4acb104baa8191b685,0x974597945c560543237d,0x4d744b2ae9c0ac0a8743,0x1d1a5c565e497458150d,0x543934c0acbc92e8b02a],#[0xc2a8743574597945c561,0x554d629ce760d2722b2a,0x2caa9ac5d92ec1946416,0x90e056558b706ca748c8,0x928338a80062ad84e91,0xfa7299a5a93a0e7a1a86,0x7ad2b1abaabaa2a5a8a9,0xfb32c9b1ac3b02bdaeab,0x7b92e1b7adbb62d5b4ac,0xfbf2f9bdaf3bc2edbaae,0x7c5311c3b0bc2305c0af,0xfcb329c9b23c831dc6b1,0x7d1341cfb3bce335ccb2,0x800d59d5b53d434dd2b4,0x28202d313988f13ef04b,0x8601e07825dc300f03ec,0x3602b00043290704bb,0xc161c00238]]
def g251H6 (j : Nat) := if j=0 then 0xb4 else 0
set_option maxRecDepth 16000 in
def g251D7 := limbs80 #[#[0x50503c29765516254140,0xd16154110e8a61954589,0xa5915458950443c7165d,0x443a69865516254110f8,0x6254110b9a6995458950,0x1b7458950443c6965dd1,0x3479965977254110e3a6,0x54110e8e619645515044,0x76595504434799659774,0xe3745895158110b1ee91,0x110db8e516254560443c,0x54560443c7165dd15158,0xa5dd16258110d9c59794,0xd1e65565dd160442ce9,0x95144375153e41425451,0xe116254510f195977458,0x1d65965dc951443a6565,0x1443475965977454510d,0x96554510e1d5d965e115,0x65565dd161442c77a45d,0x43b295454b8050910d1d,0x150120d1b65565dd1624,0xd4258540483f09535095,0xf096554d4250120de2e4,0x120eca6156550940483,0x454d40483b2985591525,0x9855956450120f865956,0x20dd2e4d5258550483a3,0x4d62482d3ba459774541,0x4a5d6458920f13a9d655,0xb1b6969759562482cada,0x54482d1fa465d6554d20],#[0x4d615414087b69b9261d,0xa695645895050371954e,0x503e29a45956254140f8,0x6254140f1ae957658950,0x5954dc950503aaba4619,0x3479965977254140d4e6,0x54140cce65954e095050,0x64549605032b99659382,0xa9a4e456258140f0e5d5,0x140baae918558960502e,0x59160503e19a45955358,0xa25d56458140baae8975,0xf2ae897559160503ca8,0x560503c68a25d5655814,0x2497558140f1ae897559,0x73e8975e0d61502ce9a6,0x2503e49a05955358940a,0x16558940f1369d6554d6,0xe9597595625036a99464,0x34eba065d6558940b1b,0x558940d1be9597595625,0x1955d9625030eca865d6,0x85d8659553dc940b3ae8,0x4d40dc66519059553503,0x759553502d4fa265d655,0xda62497559540b1769a9,0x40c7a24b9061d65502c6,0x5755028eda6209815d5,0x618825d54087baa4826,0x87bea586209755029eba,0x755034e9a0658825d540,0x937158150d1b69596209],#[0xe59594dc5605434b9945,0x543339945538158150d1,0x6258150c9e59594e0560,0x97915896054366995e45,0x3e29845516258150b9a6,0x58150b9ae95845896054,0x9655160542679a6e4954,0x3ba46595458150b8ee91,0x150b8ee9195591605436,0x5937154366965e497458,0xa0e456254950e0f59584,0xc9e59590e0562542769,0x56254366965643815895,0x5d95458950cda61590e0,0xbe917655162543c6ba0,0x2543669956416458950f,0xd6458950b8be91955916,0x6539059562542cafa465,0x42e69a4e416558950d9a,0x658950b9ae8194595625,0x1945d962542ce9a4e417,0xc6fa56517658950b3ae8,0x4560c9e59590e0564542,0xe1151582ae9a0e11625,0xba06538158960c9e5959,0x609ba693905d5625826e,0x955358365992e416554d,0x4e416554d60d96653905,0xb96e819259553582e59a,0x70546e5ba06516554d60,0x1162dc151e1d59584587,0xbe55656037158b86d656],#[0x58b64d946416554d62c9,0x6554d62d93e519059553,0x93905955358ae4fa4641,0x2a6da5a5f8059562b936,0x54110fd8549425855044,0x5258550443e716550961,0x71656096154110f5cdd1,0x110f9c5958458550443e,0x59150443e39865915454,0x866116454110f8e59584,0xfca5515250960443ab9,0x960443ea984551625811,0x6116258110f9a6155458,0xbae958458960443ae985,0x442eeba46156258110b,0x15458110f2e5d1646096,0x5958455160443e398559,0x43b39856115458110f8e,0x258510fc955152509614,0x96154540483e35655514,0xe71655855150120fe850,0x120fca5954254540483,0x258540483fa142605615,0x9545496150120faa5954,0x20eea6194260540483f2,0x8550483f295458d52501,0x56056154120fd8549815,0xfca5514258550483e716,0x50483e69a25956154120,0x8d4254120eda61952605,0xae858654950483f29545,0x483e69a15956254120bd],#[0x6554120f9ae856558950,0xdb9159550483c7976645,0x3e65655096154520f1e5,0x54140f99689655855148,0x8158550503f31545c561,0x71656056154140fcc551,0x140f8e6916558550503e,0x5c550503d39765517154,0x765957154140f8e59564,0xece6195460550503c79,0x550503e3965591815414,0x5d95454140eae6196460,0xcee858655150502f3ba1,0x503e39a15956454140b,0x56554140f8ee85655915,0xe857659550502f39a4e4,0x3eb1645c55158140b9e,0x158140f8e69165545605,0x5645c560503cb9755917,0xc79755957158140daee5,0x8140bbae858558960503,0x159560502ebba1615645,0x1a05956154540bae6939,0x40f9a6816558951503e7,0xc5615037399464165545,0x46416558540f1d5d5655,0xbba68391595625036b99,0x60542c7fa15d97559540,0x517158150f8e591545c5,0xe59572e056054367965e,0x543a79655d38158150e9,0x7458150d9e6599155160],#[0x8565dd160543c79a1597,0x2e79a4e456558150f1ee,0x58550d9d597945c56154,0x9159561543c77a159774,0x7ba06516558550b9d693,0x950f9a6856560162542e,0xdd162543e6ba15958058,0xa15977458950f1b68565,0xb9b6939159562543c6f,0x56154677ba0653815955,0x6416558551d9d6499059,0x9d6519059561546e77a2,0x1546e77a46416558551d,0x16558951b9de81925956,0xe91905956254766d9464,0x8ae6da0dd58159562b9b,0x1595629bbe9190e05655,0x375e056558b66f756438,0xf31545096154110b9b68,0x4110bdc6954258550443,0x458550442f73a2551615,0x9765494254110bf8e898,0x10f5add95250950443d6,0x950443d397655142541,0x65514254110f4edd9545,0xf1e5d96550950443b398,0x50443579766554254110,0xd15254110d5edd995509,0xee917654950442d79a6d,0x443e69a55916254110b5,0x6254110eba6918658950,0xa58658950443aeba4619],#[0x3c79765958254110eba2,0x54110d5e5db925515044,0x925515044357b76e4954,0x3ba461954541109de69b,0x110ecee918655150442f,0x59150443578a76595454,0xa961b7454110eaee9186,0xdda59792611504431fb,0x1504435e976e49845411,0xe498454110d7addb9261,0xfa69b92611504433e986,0x443c797659584541109,0x95158110fac609645056,0x6116254560443e716550,0x43e71656095158110fb8,0x258110f9c59584545604,0x554509604436eb985894,0xe39645515258110f8e59,0x8110bba6a15458960443,0x4609604436bb94591825,0xb955958258110d6ee517,0x10cdee55856096044367,0x5160443cba9759154581,0x76595458110f1ea5d655,0xbaee9185591604434f8a,0x6044367b955958458110,0x414254510cdee5585611,0xc61b905095144377165e,0x4433f386e414254510cf,0x4258510f1d5097659551,0x5390509614437e152e41,0x36f165e414258510dec5],#[0x585109fc697905096144,0x54e0142443c769759554,0x2d765515250910ece595,0x910f4bdd95454942443d,0x61542443c3d765955450,0xa76595458910cfc58790,0xf0fa1d65591544434ec,0xd5444357960656875511,0x6568755110d5d58595a1,0x5f61995a1d5444353d64,0x48257fa66568755110c,0x95150120dea659425454,0x59564545404837ab9650,0x83da9755096150120f8e,0x150120f6add542585404,0x54258540483ba9855096,0x7a9985096150120eeae1,0x120df2e4d5258540483,0x358540483b6985549615,0x975e4d6150120de65539,0x20d76dd793585404835d,0x85404833d985e4d61501,0x5e4d6150120cf6e17935,0xf8e59554585404827d9a,0x40483d39755516150120,0x98150120e9e61565585,0xa5d563509404837ab965,0x483ba98558d4250120f6,0x4250120beae856550940,0x156354940482faba1619,0x3f19a45955350120eda6,0x54120f4e5d55458d4048],#[0x42585504837cb9350961,0x69a55096154120f9a595,0x120f5a5d15258550482f,0x58550483d6b745496154,0x985496154120edae1152,0xdd65539358550483769,0x5504835d974e4d615412,0xe4d6154120d76dd39358,0x4e5d154585504833db84,0x483e73a15956154120f,0x56154120f1e5d1655855,0xe116558550483c7b7459,0x8376b965498154120e9e,0x254120d9ee5965605504,0x163549504837699558d4,0xd6b7458d5254120f5a5d,0x4120edae116354950483,0x458d50482f6ba1591525,0xba15915454120f4e5d15,0x20d9ee456559150482f3,0xd150483e3ba459564541,0x26456554120f4ee9165d,0xdda64b91595504837699,0x51483c75745956154520,0x956154520f1ddd165585,0xd69d6558551483a77845,0x483c76a75956154520f1,0x4258520f1ba9d6558951,0xd783509614839cd75e0d,0x2bcda5e0d4258520e73d,0x58520ed3553835496148,0x83549614839cd74e0d52],#[0xdd955d38358520e73dd3,0x520a7769574e0d614831,0xe0d614829dfa55d38358,0xa5dd38358520c7765774,0xe5755175e0d614829dd,0xd614829dfa45d7835852,0x5915454920a7769375e0,0x3ba5d9159562482f2fa1,0x34834ee97e456558920d,0x77454d20f87e91655915,0xe456559154483d1fa459,0x8353f915d56455120d8f,0x755120c7b5879261d544,0x794597744831ed63e498,0x5bfa1e5165dd12096f68,0x9520d4f5479461d65482,0x461d654834bd61e51875,0xf81e518759520c6f6079,0x20d1f5879561d654831b,0x855050347d6165687595,0x55c56154140f9c595715,0xbece918158550502f73a,0x5050375b935496154140,0x4d6154140d76dcb93585,0xedc954585505033db82e,0x503b3b825516154140f4,0x6154140dce65d5458550,0x85655855050373998551,0x3c7b725956154140f9ce,0x54140d9e65d655855050,0x545c550503b398655171,0x3b955917154140dcee59],#[0x140eae619645c5505037,0x5c5505036bb965917154,0xa6e557154140d5e5db95,0xb5ee95765c550502779,0x550503d3976551815414,0x5518154140dcee595460,0xce5979460550502f39a6,0x5033b986e518154140d,0x581541409ee69b946055,0xe596560550503c797659,0x3ea9a15916254140d9e,0x254140f9a68565589505,0x57658950503e6ba15956,0xaeba16196254140f3ae8,0x4140f4e58d54dc950503,0x655150503b3963553825,0xba16195454140f4ee857,0x40ecee9d8655150503b3,0x9150503e399159564541,0x75956454140f8e69d655,0xf8e6199559150503e3ba,0x50503ab9916196454140,0x196454140eaee8586591,0xe6519159550503abba76,0x503c79766456554140dc,0x6554140dce6539159550,0xd99459550503c7976e45,0x3c7b975d96554140f8e5,0x58140f1ee85765955050,0x7154560503e71655c551,0xe1815895158140bbce99,0x140fac6056454560503e],#[0x545605036bb975915158,0x975955158140f9c60565,0xf2e5c9645c56050367b,0x560503abb85591715814,0x5d57158140b7ae89755c,0x3ee59755c56050357b95,0x503ea9a45898158140d,0x98158140f3a5d5626056,0x5d56460560503ceb7558,0x3cbb755918158140f2e,0x258140baee9564605605,0xd6554d605036bb915918,0xe5ba75955358140f9669,0x8140f2e6857559160503,0x159560502ebba7615645,0x9756456558140dae6519,0x40dae6539159560503c7,0x9560503c7975e4565581,0x75d56558140f8e5d5945,0xf1e6057559560503c7b9,0x60503c79a15d56558140,0x497558140d7a644925d5,0xddc965585515035e991e,0x503a77875956154540f1,0x6154540d9d65d6558551,0x9d6558551503c75a7595,0x3c75655d97154540f1da,0x54540f1b69d655895150,0x90e1d5150387f875d965,0xb9646438754540cfc585,0x540cde59590e1d515033,0xe1d515031f9766438754],#[0xa25d571585408fee9990,0xd5de55755c561502de7,0x9615031dd95e0f725854,0x5d78358540a7769783dc,0x7328975e0d6150395d52,0x15039cfa25d78358540e,0x78358540a77e8975e0d6,0x68391595615029dda2dd,0x3c7575e456558540bbc,0x558540b3d69f91595615,0x5755956150387d875d56,0xc6ca25d56558540f1d68,0x8540f1be897559561503,0x25d5615035e5a1e49755,0xd86e49755c540c7b6a39,0x40c7be1b925d5715031e,0xd5715025eda6e49755c5,0x16416558940a5f69b855,0xdbae4590595625036e99,0x62503ea9946416558940,0x456558940faae9190595,0xb65d9159562503c6d756,0x503c6d75e456558940d3,0x6558940d3b65f9159562,0x819759562502ceda7e45,0x3c6fa565d6558940f3ae,0x58940e3b2a1975956250,0x915d9625034efa165d65,0xed95e457658940d3b261,0x940b3b697915d9625034,0x5d962502cefa16557658,0xa859553dc940b3b68498],#[0xe1f585855977250395d,0xb7250387d5161965dc94,0x6416554d40a7be859261,0xc6e919059553503f1994,0x3503e59766416554d40f,0xd6554d40f17e5d765955,0x2899759553503d5ba065,0x3d4fa265d6554d40f53,0x59540b576a697595535,0x98460165503b39756118,0x3b9846438159540eae5d,0x9540cee50990e0565503,0x7e05655033bba4643815,0xca265f8159540c7ee819,0x40c7be8997e05655031e,0xd565503c79805d975595,0x1e497559540d5b644925,0xd5b5479261d6550356d9,0x655034ed61e498759540,0x498759540c7b6079261d,0xf5879561d655031ef81e,0x5031ef912498759540d1,0x8759540c7be479261d65,0x4596a1d6550347d61656,0x29efa15db825d540d1f5,0x5d540cfae8196e097550,0x90605755031efa765b82,0xb964e41815d540d7c587,0x540d5e59790605755035,0x605755025f9a6e41815d,0x96209815d540e7958482,0xa7b69882605755031ef],#[0x5755039eb90e09815d54,0xe09815d540e795878260,0x7b65b826057550396f95,0x55031ef96e09815d540c,0x8825d540a7b69b826057,0x68196209755029efa161,0x34ed61658825d540d7a,0x25d540d3b58d96209755,0x5962097550356da56588,0x4efa1658825d540d3b68,0xd540d3b68d9620975503,0x6e09755034efa3658825,0xfa161b825d540e7ae818,0x40e5be9586e09755029e,0x9755031efa961b825d5,0x565b825d540d7ae8196e,0xc7b65991e097550356fa,0x755029efa6647825d540,0x5b825d540a7be8596e09,0xee0790609765031efa16,0x5431ef81e49855d940c7,0x7158150dcee51545c560,0x99545c56054367b96551,0x3cb9745917158150b9e6,0x58150f1e5c9655c56054,0x655c560543c797459571,0xf974e597158150e9ee11,0x150f1e61165dc5605434,0x60560543e69545898158,0xa55898158150f3add162,0xf1edd16560560543e69,0x560542e79a4595815815],#[0x5538158150cde65152e0,0xfae8974e0560542b7ba2,0x543a79a15978258150a,0x15458150e9ee8565e096,0x69d6455160543e398159,0x43e39966115458150f8e,0x458150f8ee9196551605,0x5745916054367ba16595,0x5e971e497458150f8e65,0x8150e9e68565e1160543,0x159560543a7ba1597845,0x9946456558150d9e6499,0x50d9e64b915956054367,0xc56154367994e4565581,0x25957158550dcde51545,0xf1d5d1655c561543c757,0x6154395f74e0d5258550,0xf7258550e5755383dc9,0x768b74e0d615431dd94e,0x54366f925957458550a7,0x545c550b9ee819259561,0x9b845517154393d76e11,0x3c3d74595645c550acf6,0x5c550d79587925d17154,0x925d17154356d65e4974,0xef86e49745c550c7b61b,0x55097b69b925d1715431,0xdc96254387d74e19655c,0xa95db8158950d3be8596,0xf1be8576551625434ef,0x5625434efa165b745895,0xe456558950d9b6519159],#[0x9ae81945956254366d94,0x2543ce898e417658950f,0x57658950d3b261915d96,0xe53915d9625434ed94e4,0x42ceda4e457658950d3b,0x658950d3b263915d9625,0x586593725434efa1e517,0x73ba0e517655150e2f50,0x9150f8e5d16560164543,0x560164543b3974615805,0x9526438159150e9e5d98,0x50cde48195e056454337,0xd164543e3ba059574591,0x5d97459150f2e601765,0xf0f615765d164543cbba,0x6454363d76e518559150,0x498759150d9e617905d9,0xe4439561d645435ad41e,0x5434bd4165a8759150cd,0x825d150cde44195e1d64,0x8176e0974543b6ba0597,0x29efa15db825d150e7ae,0x5d150cfae8196e097454,0x946097654336fa565b82,0xbf81e51825d950d6e443,0x950d7a44392611765431,0x5c5515831ef81e49845d,0x845957154560eb9e1162,0xb9ee819259551583a77,0xd52582e7ba0651655456,0x5d38058960cee4439461,0xbae8575e0162582eeba1],#[0x2582cefa15d57458960b,0x17558960d3be8595dd16,0x693915d5625836e898e4,0x83e5ba06516554d609bb,0x1595619bee8194e05655,0x5915957058a6f7a46438,0xa6f85645655c162f1bdd,0xc162f1bdd7915957058b,0x15957058ba6f85e45655,0xd946416554d62abbaa39,0x62f93691905955358be4,0x955358be4fa46416554d,0x46058059562f9329d905,0xcbbe53816016558b2ef9,0x6558aaeda4e058059562,0x518059562ebae8184601,0x6e81846016554f6ad84e,0x54f71d84e518059553ed,0x80dc565dd66039060965,0xa02d005a00031bd74e51,0x96020a06f017a04e00e,0xf903960d8032a0b7029a,0xd04fe135048610804020,0x66618905e2168056a14,0x7c21e3074a1c806c61a4,0xca22b086a20a080a1fb0,0x226d0996258092a23d08,0x2c70ae62af0a922910a0,0x210c423030bca2e50b6a,0xd0d5634e0d1a33f0cba3,0xe9a3960df236c0d9235,0xff63ed0f8a3c90efa3b7],#[0x2243b10c2429106240b0,0x247411a645f116a45011,0x4ce13024b0128a492121,0x22145250713e64ec137a,0xc15ba564154e54614d65,0x173a5b8169e597161a57,0x89661b184260917ca5e2,0x2267819b6666193e6391,0xa6cc1aee6b11a9a6991a,0x7351c8671a1c1a6f31b8,0x831dbe75f1d5e7471cfe,0xc1ec67aa1e727921e1e7,0x1fce7ef1f867d41f1a7b,0xa6825206a81320167fe,0xa2864215a85221128372,0x2894222687c21de87021,0x8d0230a8b522aa89d226,0x1224128fa23be8df2352,0x8250e93f24d292d24969,0x25f297225aa95d254a94,0x7069ba26be99c2646984,0xde9f027969e1274e9c92,0xaa2c289ea23284aa0527,0xa5f295ea4a2916a3b28d,0x982a36a8629faa7729be,0xa2b3eac82aeaab32a96a,0x2c22afb2bc2ae92b86ad,0xcfab3d2cd6b2b2c76b13,0x1eb462d12b432d06b402,0x2b4f2d36b4c2d2ab492d,0xb582d5ab552d4eb522d4,0x612d7eb5e2d72b5b2d66],#[0xa2da2b672d96b642d8ab,0x2dc6b702dbab6d2daeb6,0xdeab792ddeb762dd2b73,0xeb822e02b7f2df6b7c2,0x2b8b2e26b882e1ab852e,0xb942e4ab912e3eb8e2e3,0x9d2e6eb9a2e62b972e56,0x62e92ba32e86ba02e7ab,0x2eb6bac2eaaba92e9eba,0xedabb52ecebb22ec2baf,0xfebbe2ef2bbb2ee6bb82,0x2bc72f16bc42f0abc12e,0xbd02f3abcd2f2ebca2f2,0xd92f5ebd62f52bd32f46,0x22f82bdf2f76bdc2f6ab,0x2fa6be82f9abe52f8ebe,0xfcabf12fbebee2fb2beb,0xeebfa2fe2bf72fd6bf42,0x2c033006c002ffabfd2f,0xc0c302ac09301ec06301,0x15304ec123042c0f3036,0xe3072c1b3066c18305ac,0x3096c24308ac21307ec1,0xbac2d30aec2a30a2c27,0xdec3630d2c3330c6c303,0x2c3f30f6c3c30eac3930,0xc48311ac45310ec42310,0x51313ec4e3132c4b3126,0xa3162c573156c54314ac,0x3186c60317ac5d316ec5,0x1aac69319ec663192c63,0xcec7231c2c6f31b6c6c3],#[0x2c7b31e6c7831dac7531,0xc84320ac8131fec7e31f,0x8d322ec8a3222c873216,0x63252c933246c90323ac,0x3276c9c326ac99325ec9,0x29aca5328eca23282c9f,0xbecae32b2cab32a6ca83,0x2cb732d6cb432cacb132,0xcc032facbd32eecba32e,0xc9331ecc63312cc33306,0x23342ccf3336ccc332ac,0x3366cd8335acd5334ecd,0x38ace1337ecde3372cdb,0xaecea33a2ce73396ce43,0x2cf333c6cf033baced33,0xcfc33eacf933decf633d,0x5340ed023402cff33f6,0xe3432d0b3426d08341ad,0x3456d14344ad11343ed0,0x47ad1d346ed1a3462d17,0x9ed263492d233486d203,0x2d2f34b6d2c34aad2934,0xd3834dad3534ced3234c,0x4134fed3e34f2d3b34e6,0xa3522d473516d44350ad,0x3546d50353ad4d352ed4,0x56ad59355ed563552d53,0x8ed623582d5f3576d5c3,0x2d6b35a6d68359ad6535,0xd7435cad7135bed6e35b,0x7d35eed7a35e2d7735d6,0x63612d833606d8035fad],#[0x3636d8c362ad89361ed8,0x65ad95364ed923642d8f,0x7ed9e3672d9b3666d983,0x2da73696da4368ada136,0xdb036badad36aedaa36a,0xb936dedb636d2db336c6,0x23702dbf36f6dbc36ead,0x3726dc8371adc5370edc,0x74add1373edce3732dcb,0x6edda3762dd73756dd43,0x2de33786de0377addd37,0xdec37aade9379ede6379,0xf537cedf237c2def37b6,0xe37f2dfb37e6df837dad,0x3816e04380ae0137fedf,0x83ae0d382ee0a3822e07,0x5ee163852e133846e103,0x2e1f3876e1c386ae1938,0xe040f47e25388ee22388,0x3d1c130088075637e0f,0x4404b01d03858df83f81,0x3f010381947c0b760c0a,0x13c040e0505812721cf0,0x84f03f01038140c8076e,0x442e12c0e8440e06927b,0x41df83b84e85a1118866,0x760803140fc040d8582f,0x610601d984032f010381,0x30f1004544140fc04067,0xd43f61607c431030301c,0xd41119078458351a1a08,0x44801d90f080b643c201],#[0xfe0c080074c1de16e108,0x1d8401d507f010381a0b,0x38a111006a65d87c301,0x249fc0f8200e04910b03,0x6bc00550302cf000361,0x703f0040f1544361140c,0xc40c0c83fc005527e08,0x2de08c4029f00a1f0c07,0xf00020f01d841fe0fc04,0x681167c0f43c2ff83507,0xf44587a04d86b02e001,0xf83b8603d0c0ff010e7c,0x80d8503603f0ae180f42,0xd86a0c1406405661bc0,0x360f0480d82587d81a0,0xc3cc1c0c00d84f0089f,0xab27c430f3070330361,0x36186010e850a0cfc00,0x220571661d817605c138,0xe040e00f4621c6000381,0x1d04c0440c08a637e0f,0xcd8202a12077a150bc3,0x43c03140f6080a8650f0,0x809c4017d820270fc11,0x19a86d8202f14057a176,0x514c3c84627c0f4401c0,0xf44c20190e00704b8,0x90c8db85815140b627f8,0x2c8d03c0b2340f022901,0x340f02c8d03c0b2340f0,0x627c0cbc105e86b8509a,0x598502a60289f21c540b],#[0x340e00f4503cf04f0071,0x700cf04f001508a0772,0x4f0004a0c1280f4230f3,0x13e0fe07c036141288f0,0x8504441d03d0c8bf237c,0xf03d13c13c0067c0aba0,0x13c000ab27c4b0002dc9,0x231030ff04f0048d17c,0x1404e86e857820da340f,0x83e8504d0961b6040f0,0x6e180f0303c06e1ba176,0x77c145825b8603c0e09,0x90701e90f100c941f604,0x3e0d243604067a185032,0x2800bc589001af8388f1,0xb8103803d1086660be0c,0xe0854c150741305211,0xe0808c4190b8404c81d1,0x15223a860361361004a,0x22b05100880e00db8004,0xa0da3761106460150360,0xf0003201ee8116240643,0x3d14017e0f6180bc4a07,0xe00f43e8201a80ff830,0xe03f83032e8602f13e0c,0x19f0003804b140c812c0,0xe3236e0c3580f455849,0x147036f830380a2f0014,0x9613a08c3cc1c05fc03c,0x5315905b83223b000381,0x7001f414a40e0ec000e0,0x2129c20290d05383b84],#[0xe10304a32903d0c12c0e,0xe84f8301ad811812bc02,0xfa04083a16e10789080f,0x7e81022d841c4bfe0ca1,0xf07c0f4203df8301a88,0x307de080f45187012038,0x5300032c1f02d14c48c0,0x3d0c0f4c0307c0b4431,0x1f140f707ee103300c1f,0xa0086878af01d01ae805,0x3d162bfe0c08007681f,0x307ee006006f83487e81,0x402dc1f180b4c9cc8de1,0x1b07c0f4248532739578,0x43c85120310b8002dc1f,0xe08590fd83080b48800f,0x823d830847904643f60e,0x821847904643f60ee085,0x64111e41190fb84d83b,0xa7814610322901c0190d,0x4ca42097182e01823128,0xca6c043b8403841d0fc0,0x44211b8430ff0111c04,0xfd8281210844c3de13c,0x201df011290c87411165,0xc0fe83182e06104a4610,0x160260099f0f03fa0c2,0x8004a02581a0012a1381,0xa02a0059f1360dc0a619,0x2581a003021360c1d83,0x61bc0826009860ae3819,0xd44360f6058004d8304],#[0xc430f06e381902302581,0x25107810d049440635e0,0x40510848c40636e0c441,0x817000ec101310b02b81,0x5a61b60c0440545c0fc,0x6861bc10301a0119860c,0x41306829d83d81600100,0x9815080f543d61a80160,0x4b58603d0c0e543c203,0xcc3f001e04303b040ec1,0x635e0c1204c0030f7810,0x70846e043781229088a4,0xc058044054430f781080,0x21b604682cd816000c27,0x8117850d43d615e0a802,0x4330f781080e543c2816,0x202221189f13000c3de0,0x282ce817040dc1018d,0x4039e83c81f00130b0c,0xd30489f170a727fa0cc0,0x10303b07c0018d202d01,0x2e080f030330504506ae,0x114a35e0d800403e06e1,0x88070846e04578150f08,0x903fa0c201ab84080b40,0x311a0fa0ca3c2022e830,0x11a24c15e06414428d78,0x1e0543c204528d783700,0x70044202d022311b811,0x883c82422a3a013800c,0xf80c0c85883c2a01380,0x10ec05c04e000e042112],#[0x1303760c268331630ff0,0x44424243c52085c1f01d,0xd812850864]]
def g251H7 := limbs80 #[#[0x47181249002042001080,0xf1c0000ae2c56000440,0x40e000000d2e84900,0x1100090da1000043b8ba,0xad13000000b2aa39f27b,0x72b00000093100023210,0x2561b4a0000c0f343a3f,0x9018000000d01f0cd05c,0x742a41c3e730c2c033c2,0x16c3482d92fda1e38e45,0x6b8000048204d23317e,0xe4700000002800000000,0xa07b88000726000000,0xe000e818448092120000,0x2bfc9180be2252001,0xf1900000054a1b3,0x70000000000001030000,0xd46e14000f900000003a,0x1aa3600030213de241c8,0x40000e8498301ff15d,0x508d35000f3a81d00000,0xa37e0000072153c206]]
set_option maxRecDepth 16000 in
def g251D8 := limbs80 #[#[0xa0aa0887d85492154110,0x21e716558550443e62a8,0x956254110eb4b92a4a82,0x4435d30cb12a08879a5,0xcbb2caa8221d39745515,0xac0887b85892158110e3,0xeb16450560443dc2c4a0,0x5158110f70b12a2b0221,0x43dc322b12c08879c595,0xa2c4b0221ce974589604,0x8873add56258110e75b,0x974591604435d70ab12c,0x54510f32b2ac4a8a21cb,0xaaaa7b92a28875554d72,0xa6a8a21d557454d51443,0x871d5d96554510eabba2,0x6dc9624429df2cb92c48,0x120fc4a9a84a02414ed9,0x2eaa1280907e294d4250,0xa0241dab7550940483b5,0xeae154250120dd4c2a84,0x940483b52eca1280906,0xf94aa2a4a0241dab765,0x8b1280906da615525012,0x241ceb7658940483d52c,0x5d96450120e9cbaaa8a0,0x50483ad2a5b8aa09072e,0xb4caa84a8241f2954509,0x92a09075a5d15254120b,0x1b6b8454950483ad6e8a,0x95254120eb4bb2a4a824,0x482ed32ca92a09075add],#[0xbb2c4a8241e696558950,0xa09074e5d15454120e75,0x4d6554d624838f2ecb2a,0x358920e67bb2a6b1241e,0x29df2cba2c490733dda5,0x6ecb12414ef965d56248,0x9053b6577658920a76ca,0x7659553482abf2aba2a6,0x95208f7c930eaa241c5d,0x72a9b8aa0a046fe51875,0x4a8281f295458950503a,0x79a5956254140f54b22c,0x589505039d2ecb12a0a0,0x40f94aa4c4a8281ae986,0xa9c12a0a074e55372541,0x8281d397655150503672,0xe6195454140e9dbb2a8a,0x1505036770caa2a0a06c,0xd5cc32c8a8281e396559,0xb8ac0a071e5d96554140,0x81cb964dc5605039d2c5,0x4d6258140f64a9ac4b02,0x503d5328b12c0a07b29,0x5baac4b0281ce9755896,0x2c0a06bae156258140e7,0xe996454d60503572c9c1,0x5358140f2cb2aa6b0281,0x3972eab22c0a07a6592,0x2ac8b0281cbb75591605,0x2a071e5d56558140d5dc,0xd9894f715031db0cb16e,0x58940a76cb6e4b12811d],#[0xc9acaa9ac4a06ea61180,0xa6b1281ccd7654d62503,0x71b5d56558940e66bb4,0x7595625029db2eb2ac4a,0x9408f7cc2eab12814ef9,0xf2abb2c4a053b65b7558,0xa9a811ef985d6625029d,0x7be498759540e2ebb2ca,0x9755029db2c412eaa04,0x8f7c930bbb2811ed96e,0xbb8ac0a873a58b715815,0x2a1a7965e05605438f2c,0x6595258150f34b12a4b0,0x60543cd2a8b12c0a859e,0x75c22c4b02a1ceb74589,0x12c0a879a6556258150d,0x1e3964551605434f2cbc,0x77458150b3ccb2a8b02a,0x5434f2cbc22c0a871e59,0xca2cab02a167b9259560,0xe2a871b59562dc550b3d,0xed96dc9625431db0cb16,0x58950f34b2b00b12a14,0x38daecaa2c4a86da6158,0x6e8b12a1c6d65dd16254,0xa879ae416558950a76cb,0x905d962542cdf28b2ac4,0x8950e75c82ecb12a16eb,0x5f28c3ac4a853be51765,0xb12c11ef9261376542b,0x7b254f8058960b74c8f0,0xe0162583d94a7c02c4b0],#[0x60b74ca700b12c1ae984,0x2bc02c4b06ba61780589,0x12c16eb9060562582dd3,0x3dd25358960e67ba2a6b,0x1625829db2bba2c4b073,0xb75c82eab12c16eb9061,0xc2ac4b053b6537558960,0xc1c5d6554f72582dd720,0x416554d60e2eb2ee8a9a,0x1487ccacab12a290f96e,0xab2ac3b82a3c75765955,0x2c4a8f1b59562dc151e3,0xe6565605625469db2db9,0x535c162e2eb2aa7b82c5,0x8b8deeab2ae0b1793595,0x2aa7b82c5a6f85595705,0x2b171bdd5655c562f26b,0xd905955358b4df0ab2ae,0x59562f27c82caa9ac5e4,0xcdb21baacab14bb65380,0x82a822166d91dd56558a,0x87dc5496154110fb8a92,0x458550443ee2a8b0aa08,0x110fb4a9284a8221df37,0x32aa12a0887ce5514254,0xa8221f696254950442ef,0x5edd15254110ebcba2a4,0x4950443af2eca92a0887,0xbbccb2a4a8221d7b765,0xcb12a08879e595625411,0x221f6954589504435f30,0xdd16254110f74b22c4a8],#[0x50443ed32ab12a08877a,0xb4aa4c4a8221ee986589,0x92a08877add26254110f,0x15f996dc950443af2cbb,0x95454110fb8c8aa8a822,0x443e72c8aa2a0885dee4,0xbb2a8a8221d797655150,0xa0886de6195454110ebd,0x7996551504436f70caa2,0x454110bbdcb2a8a82217,0x35f30cb22a08879e5956,0x6e8a8221d7965dd15044,0x8867ee1b7454110cfcc3,0x9261150442bf32dba2a0,0x8110afdca2eca82217eb,0xe6e890ac0887bc591215,0x2b0221ef16250560443b,0x7bc5895158110bf9c928,0x54560442fe724a8ac088,0x10ef9ba2a2b0221ef164,0xc4a12c0885fce5151581,0x2216f99650960443dd2,0xe6595258110f74b12a4b,0x9604439f2e8b12c0885b,0xb7dca2c4b0221cfb7458,0xb12c08873edd56258110,0x216fb95589604435f70a,0x116258110f74aa2c4b02,0x443dd328b12c0887ba6,0x4c2ac4b0221eeb945896,0x2c0887ba6556258110f7,0xeb96455160443dd72ab1],#[0x5458110f3cb2aa8b0221,0x43de322b22c0885be659,0xaac8b02216fb92591604,0x886bee156458110e7db,0x965dd160442df72ab22c,0x50510afccaee8b0221cf,0xfe720a12a28857d65b72,0xc4a8a21f555350951442,0x87b95916254510f3ab2a,0x458951443bcee8b12a28,0x510ef3ba4c4a8a21be78,0xacbb92a2886f9e126254,0xa8a215f596dc951443ae,0x9d59564545109facb704,0xd151443aeacbba2a2887,0xcfbc36e8a8a219f586d,0xbc22a28857d65b745451,0xa219f576e11514436eac,0x65b8454510cfbbb708a8,0x51442bef28bb2a2884fd,0xf9c8284b0a213f794619,0xa2c28879d5955458510b,0x15f595dd1614439eacbb,0xb8050910df4a9700a122,0x4437b2a7c0284886fa58,0xcaf00a1221bb954e0142,0x84884fe65b80509109fc,0xef8658942443e5aa8a92,0x6509109fdc830aa1221a,0x3d5ac8aa2c4884fee418,0x2a8b1221e6d655516244,0x887b96456458910b76cb],#[0x7559162443d5f08b22c4,0x8910b77caac8b1221cef,0xdd2eb22c48873b65d645,0x8b1221ced65dd1624439,0x5fae418458910af6caee,0xdd262443cdf0ab2ac488,0x10cdec22c9b92215ed95,0xab2ee48847f66164dc9,0x92218fd86597724432fb,0xf59564551108fecc2cbb,0xd544438faecb2aa88878,0xabfcab0eaa2215bf9461,0xc3ac88855f6568755110,0x214fd96a1d644429ff2c,0x1565dd1108fecb704ba2,0x44431fb0cb2ee88865f6,0xfcb30bba2211fd985977,0xaca8853fe5176595108f,0x1fd95e11764423fb29c3,0x5150120fd4a12a2a0241,0x83f5284b0a80907d654d,0x1302a02417db93585404,0x907ea54d4250120fd4a,0x96550940483f52c6a128,0x50120fd4c3284a0241fa,0xf32c8a9a80907ea59152,0xa6a0241f596554d40483,0x7ce5955450120fccb24,0x259140482f732caa2809,0x120f5cb2ac8a0241fa99,0x6eab22809076e5d56450,0xa0241bb98559140483b7],#[0xeee556450120dddc2ac8,0x85504836f30ab2a80905,0xbedc9ac2a8241f69525,0x4c0aa09079e595615412,0x241f696550950483ed2a,0x58d5254120fb4a1aa4a8,0x50483ed306a92a0907da,0xb4c32a4a8241f6964549,0xa2a0907ce5915454120f,0x1e796559150482ef32ca,0x77454120ebcb2ae8a824,0x4836f2cbc22a09075e59,0xca2caa8241f699259550,0xa29079d5956154520bbd,0x6d6558951483e9aa6a12,0x354520e77bb2c4a8a41e,0x3abee8a9aa2907575d15,0xa84b0a41c7d765955148,0x906f3e0d5258520de7c1,0x74e0d614833bae9c1ac2,0x8520ceebaf06b0a419df,0xbb2bc1ac290677dd7835,0x5b8a41ced6458b714827,0x63f61964dc520cf6c22c,0x54d424823fb30b26e290,0x20f96b22a8a9241f4d65,0x2eb2ac49073ba5d64589,0x9a415bf945d5434839dd,0x75957454d20f2eb2ac8a,0x553483abacbba2a69075,0xeaecbacaa9a41f4d9259,0xb22a890757a5d6554d20],#[0x41d3d7559154483c7aca,0x528759120adfca30eb22,0x5482b7f28b2ee89056f6,0xfcab0eb2a415bf9461d6,0xaec9055f6568759520ab,0xf39544c5505023fb29c0,0x6154140bedc9ac2a8281,0x3cf2cab0aa0a07ce551,0xaae2a8281f39545c5505,0xa07ce5518154140bbdc,0x96454950502f7728c0aa,0x54140ebcbb2a4a8281f3,0xbf32db92a0a075e59772,0x4a8281bb964e0950502,0x7ce55163541409fccb7,0x460d50503e72a8b9aa0a,0x140bddca306a8281f395,0x30caa2a0a07ce5d95454,0xa8281f399559150503e7,0xce6516554140f5cc32c8,0xd950503cf2ecb2aa0a07,0xebdcaaeca828177b955,0x8c32a0a05eee51865414,0x281eb964485605037772,0x5915158140f74b12a2b0,0x60503cf2caa8ac0a07ae,0x5cb22e2b0281ee9625c5,0xac0a05bee597158140f,0x1eb96460560503dd2c4c,0x55258140f5cb22a4b028,0x503dd722b12c0a075e5d,0xb22e4b0281ee98558960],#[0xc0a07ae5918258140f5c,0xb97559160502f7728c12,0x558140f5cc2ac8b0281e,0x3cf2eab2ac0a07ae6516,0x2eab02817eb925d56050,0xa077ae497558140ef449,0x96dc921502f7728c2ac0,0x4540af7c92ea98a815ed,0xaaa6b8aa2a079d595615,0x4a8a81e6d6558951503e,0x75754f7254540e76bb2c,0x61d515038faecb2aa2a0,0x409fcc870ea8a813fb90,0xebc1ac2a0677e0f72585,0xa819df75e0d615033ba,0xf5d565585409eecaf06b,0x971502bdf24baac2a071,0xaf7c92eab8a81ced7658,0xbb2e2a065fe15755c540,0x813f990e05625031ff0c,0x5f8158940cf7b9702b12,0x2502fd321c0ac4a047f6,0x743f02b1281ced76e056,0xac4a057b65f8158940cf,0xced9759562503dd320b2,0x7658940e76c8aecb1281,0x39db2abb2c4a073be45,0xc2ecb1281cef955d9625,0x4a075759553dc940e764,0xd8694f725033bb0ca9ee,0xdc940cbec2acbb92819d,0x3fb30b2ee4a063f61965],#[0xdb92819ed9261b72502,0x7d66416554d408ffcab,0x759553503cbaecb2aa6a,0xd40eaf4bacaa9a81d5d9,0xf24baae6a057be497558,0xb2a81bb98460165502bd,0x7f65f81595409fcc8702,0xd5655038faecbaacaa04,0xeb7c92eab2a81d6c925,0x4c3acaa071fe55765954,0xa8157f9561d65502bdf2,0xe4187595409fdc830eb2,0x655033d924c3acaa067e,0xbfcab0eb2a819ef9261d,0x3acaa055f6568759540c,0x11fd98a1d655029fb2d4,0xb825d5409fcc870eb2a8,0x5027db2dc12eaa067b5d,0xc8302baa8157f955d975,0xeaa067b209815d540afd,0xed86209755033df04c0a,0x25d540af6cb104baa819,0x33db0dc12eaa067b60f8,0x704baa815ed96e097550,0xa067b647825d5408fecb,0x96e09755033db27c12ea,0xd540afdc8306baa819ed,0xf720c12eca057ee41865,0xabb2815fb9061576502b,0x7da5492158150af7c930,0x5c560543cf2ca90ac0a8,0x50f3cb2ae2b02a1ee962],#[0xc9b8ac0a85bee5971581,0x2a15f994dc5605439f2,0xe5958158150f74b1302b,0x5605436f2a5c0ac0a879,0x9fcca702b02a1b7954e0,0xa92c0a87da6095258150,0xa1d7b7454960543cf2c8,0x456258150dbdc22a4b02,0x543dd308b12c0a87bae,0xcb2b04b02a1e79655c96,0x2c0a85dee558258150f3,0xf398455160542ef724aa,0x6458150f3ccb2a8b02a1,0x43cf32ab22c0a87ae5d1,0x2ae8b02a17eb925d1605,0xa879e5958458150f3cb,0x99159560542ef72ac22c,0x58150f3dc8acab02a1e7,0xcf724b2ac0a879e64965,0xcab02a1e799459560543,0x879d5957158550f3dca2,0x3dc9615436bf06a92c2a,0x550daeaa706b0aa19df8,0xacbba2c2a8677dd38358,0xb8aa1e7791595615438f,0x3b5d9625c550f36b2ac4,0xd17154367f08aa2e2a87,0xd3fc32cab8aa15ef925,0x8b26e2a863fe19765c55,0xaa1c7d655937154337b0,0x66164dc550c7ec32c9b8,0x525432facac26e2a847f],#[0xbdc82eca92a176f91589,0xac4a84fe6438158950b,0x137d95e05625434facbc,0x165589508fecbf02b12a,0x5439f720bb2c4a879ee4,0xb2f02b12a17e990e0562,0xc4a86db6178158950f36,0xed76e0562542edb2bc0a,0x458950af6cbf02b12a1c,0x3cdb2ab22c4a87ba6416,0xacab12a1ced975916254,0xa879be456558950f36c8,0x9459562543cdb28b2ac4,0x8950f75c82ecb12a1e6f,0xdf22bb2c4a873b645765,0xcb12a1ced945d9625439,0x73b2617658950e77ca2e,0x553725423ff28c0ee4a8,0x50cdec22c9b92a197d86,0x30b26e4a863f61964dc9,0x92a19ed9261b725423fb,0xfe11545cd508ffca30db,0x954542bdf24ba2e6a86c,0xb9fca2ecaa2a177b905d,0xbb2a8a875ee417655150,0xa1e796560164543a7f28,0x438159150dbcc2b00b22,0x45434facbc0ac8a84fe6,0xecbf02b22a137d95e056,0x2c8a878f59574591508f,0xe7b905956454397aecba,0x8559150f1fca2cab22a1],#[0x42df720bb2c8a85cfe51,0xa2ecb22a1cfb905d9645,0x8a857be498759150e5fc,0xb9061d64542b7f28c3ac,0x591509bfcab0eb22a13f,0x9fb2d43ac8a856f65287,0xeb22a13f990e1d64542,0x86db597825d1509becaf,0x6e09745433daedc12e8a,0x550dbcc1700b2aa13ed9,0x309c02caa85de64b8059,0xb2aa177994e01655436f,0xdee418459550bbdc8304,0x1765427f329c02eca85,0x8feca702bb2a15f994e,0x8c12eca857ee41825d95,0x2a157f9560976542b7f2,0xe49845d950afdc8308bb,0x21582aff2ac22eca857b,0x72b12e2a8ac1e7565545,0x12a2b079d5957154560f,0x1cef7458951583dd720b,0xd6254560d77c22c4a8ac,0x5838facbb92a2b06bbe1,0xcbf04a8ac13f990e0951,0xa2b071f59774545608fe,0x7d65e11515827f321c22,0x7545608fecbf08a8ac1a,0x3dd720b12e2b04bf65b8,0xac4b8ac1ced745897158,0xb063f59584dc560e76ba,0x9061d525823ff2ac26e2],#[0x89609dfca30ea92c13fb,0xd2e9c02c4b05bee41755,0x2b12c1ee975e0162583d,0x5bb6538158960e77ba70,0xe05625839deebc0ac4b0,0x60b76caf02b12c1aed85,0xe929ac4b07b35d153589,0x12c16ef915d162583d9a,0xbe557458960e76baae8b,0x562582ddf22c22c4b05b,0xb77c8aeab12c1eeb905d,0xc2ac4b05bbe517558960,0xc1e5d6554d72582ddf22,0x15655c960d5fc22c8b92,0x3583cbacaba2a6b069fe,0xfc92caa9ac1e5d925955,0xaa6b07976516554d60f2,0x6fb905d564583cbf28b2,0x655d160b5fca2eab22c1,0x835f305c02cab069fe15,0xa700b2ac1af984e01655,0xab05bee418259560b7cc,0x994e0175582df720c22c,0xdc151dbab2f00a8a433f,0x8facab16e0a8e7d61161,0xc5b82a39ed8458b70547,0x8e5f59584dc151cf6c24,0x595615463ff2cc26e0a,0x951f3ac92cab0aa3e759,0xacac02c4a8e9f5978058,0xb12a3e6d65e0162547cd,0x7f653805d951f36c82ca],#[0x56254adeb21c0acab0c,0x28fec8702bb2a53ed90e,0xac06e2b147fe5180dc56,0xac51ff956037158b1fac,0xe416554d62f2ec82caa9,0x7058b5df0dc0ae0b1797,0xf7ca301b8ac53ed94e05,0x6e2b16bb59580dc5629,0x53ef956037158b3daeac,0x58059562d76c0b00b2ac,0x58b5db08c02cab16bbe0,0xca300b2ac5aef8460165,0xcab179bdd58059562b77,0x6f75e016558addb29c02,0x59562d76ca700b2ac5e,0xbcdeeac0acab16bba5f8,0xf02b2ac56ed90e056558,0xa9cfb643815d562f37ba,0x826016554f6bb04c02ca,0x9553bafc9300b2aa7b5f,0xbf08c02caa9ed7611805,0xb2aa775f946016554f6,0xdd764b8059553daec170,0x6096554eebb29c02caa9,0x65baec8704b2aa775f90,0x84b0aa08847fe5180dc5,0x8221ff18258550443fe2,0xe5954254110ff8c22c2a,0x950443ef2c8a92a0887d,0xfbcb2b04a8221f798654,0xb22a0887de6195454110,0x21ef98659150443f7308],#[0x198454110fbcb2b08a82,0x442ff728c32a0886fe6,0x8c12a2b0221ff1425456,0x2c0887fc6115158110ff,0xfe98250960443fd2a4a1,0x4258110fdcaa284b0221,0x43bf6eaa12c0887be595,0xa2a4b0221fe982549604,0x887be5915258110fbca,0x98458960443bf6e8a92c,0x58110f7cc2ac4b0221ef,0xbf2e8c12c0887be59182,0x4b0221bf98460960443,0x86fe6158258110f7cb2b,0x455160442ff72ac12c08,0x110fbcc2aa8b0221fb98,0x30ab22c0887be6496458,0xb0221ef96561160443df,0xfee558458110dfcc2b08,0x1560442ff724c2ac0885,0xff2a9284b0a217fb946,0xaa12c2887ed551425851,0xa21df77550961443deac,0xdd15258510fbaaa2a4b0,0x52443e7acaaa2848877d,0xf8b0aa2a0241f3d64551,0x8a80907ee5915150120f,0x1ff18158540483ef2caa,0x16150120ff4a92c2a024,0x483df2cab0a80907ee55,0xc3302a0241fb96460540,0x80907fa58d5250120dfc],#[0xf18158550483f72a8b1a,0x154120ff4a12c2a8241f,0x3ef2cac0aa0907de5516,0xa84a8241bf9866055048,0x907de5516354120ff4b1,0x9159550483ef322b2aa0,0x4520bfdc8b0ca8241f7b,0xdacaa12a2907f9509615,0xaa8a41e7d6559151483e,0x7bb5954258520fb6c92c,0x55161483edaa8a92c290,0x20f7bc8acab0a41e7d65,0xa8b1aa4907bb64965585,0x1241eed9159562483eda,0xf5d98159520f77c8acab,0x5505039faedc0aca9073,0xff8c0ac2a8281ff17158,0xb8aa0a07de5496154140,0x81f79655c550503f72c8,0x918154140efcbb2e2a82,0x503ef2cac0aa0a07ee5,0xcb1aa4a8281bf9866055,0xaa0a07de6456554140fb,0x7fb915d950503ef722b2,0x5158140bfdc8b0ca8281,0x3df2cab8ac0a07fc5c5,0xaae2b0281df9755c5605,0xa07be6456558140bfdc,0xb9161560503df722b2ac,0x54540efabb2e2a8a817f,0xcfaecb2aa2a07de64165,0xe2b0a81ef5655c561503],#[0x5fde557158540efabaa,0x159561503df320b2ac2a,0x540f3ebaacab0a81ef79,0xaecb2ae2a075f5d5655c,0xb8a819fd76e15715039f,0xbb6456558940affcaaec,0x565503ddf22b2ac4a07,0xb7fc8aecb2a817f990e,0x4b8ac0a857fe45765d54,0x2a1f79545c560543ef2a,0xe517158150f7cb22e2b0,0x605437f2e5c0ac0a85fe,0xbcc8aa8b02a1bf974e05,0x8ac2a87dd5497158550f,0x17f7945c561543eeaa8b,0x57458550f3eb2ae4b0aa,0x543cfb24b2ac2a879f59,0xbb2a4b8aa1e7d9459561,0xe2a875f5d9545c550ebe,0xfd7659171543cfacab22,0x45c550dbeb2f08b8aa1c,0x2eff22bb2a4a867f5db8,0xacab12a1e7d915956254,0xa85dfe457655150f3fc8,0x9159564543cfb22b2ac8,0xd150ebec8acbba2a1e7f,0xfb29c0acaa875fe4565d,0x4a8ac1eed7458951582e,0x79f5957454560f3eb2ae,0x59551583cfb24b2aa2b0,0x60b7fc8aeab12c1e7d94,0x29c0acab05bfe4575591],#[0x2aa3e7d9059562546dfb,0xfe498059551dbec1300b,0x1655476fb08c02caa8dd,0xbbfc8304b2aa377f9460,0xc02cab0ebf6098059561,0xc3afd8460165586dff24,0x418259561b7fca300b2a,0x58adfb21c0acab15bfe,0x7c8acab82c5eed915957,0x2a0884ffe5180dc565f7,0xdfb7650950443bf2eca1,0x8254110dfcc3284a8221,0x43bf6ecc12a08877e5d9,0xb2a8a8221bf986609504,0x887de6556454110fbcc,0xb9859150442ff330b22a,0x54110efcc36e8a82217f,0xbf6ecc22a08877e5d984,0xca8221bf99261950443,0x86fe6518654110dfdc93,0x4485604437f728c32a08,0x110ff8c1282b0221ff18,0x32aa12c0886fee154258,0xb02217fb9550960442ff,0xfee614258110bfccc284,0x960442ff330a92c0885,0xbfdc92a8b02217fb946,0xeaa2c0887be659545811,0x2217f99855160443bf52,0x6556458110bfdcc2a8b0,0x51442ff724c22c0887be,0xfabb284a8a21f7565509],#[0x12a28877ddd94254510e,0x1bf786509514437eb0ca,0x54258510bfacaa84b0a2,0x442fef24aa2c2885fde5,0xb2f00a1221df69755161,0x84886fe5d78050910dfc,0xed76549424437f2edc02,0x450910ef7bb2a4a1221d,0x3b7eecaa2848876f5d95,0xacaa1221cfd765954244,0x8857f65b7550910affcb,0x76615424433faecc2a84,0x910cffbb70aa12219ff,0xfaecaa2a48857fe55765,0x8a9221d7f7655152443a,0x57fe517654910afecb6e,0xe0954443ddb2ab22c488,0x10cffbb704aa2219fd76,0xeb22a8884ff65b82551,0xa221d7e8759554443b7d,0xf25d8655110affcc2eca,0xd544433fb0d43aa88867,0xbfdc8304b22215fd96a1,0xa8a80905fe6595150120,0x41df97558540482ff72c,0x156150120efdbaac2a02,0x4837f70ab0a80906fe6,0xdcb302a02417f9985854,0xa809077e5d56350120bf,0x7fb91595404837f30ab1,0x8650120fdcca2caa0241,0x83bf2e8b0aa0905fee45],#[0x22c2a8241dfb74585504,0x905fe6616154120dfdc,0x97458d50482ff72cc0aa,0x54120efdba2c6a8241df,0xff722b22a0906fee1163,0xcaa8241f799459550482,0x77d5d16154520fbdca2,0x458551483beee8b0aa29,0x520df6c3284a8a41bf78,0xacaba2a2906fbe194254,0xa8a419fd865d151483af,0x5f5977454520cffc32e8,0xd1514833fb0dba2a2907,0xdbeb2f08a8a419ff86d,0xeb2aa2904ff65b845452,0xa41d7e9759551483afb2,0x5d542585209ffca30ca8,0x61483bdeeaa12c29077b,0xf7ba2a4b0a41ded74549,0x1ac2906f75538358520e,0x1bdd75e0d614837bae9c,0xd5458520ebebaaa8b0a4,0x4839facaba2c29057f65,0xb2ee8b0a415ff955d161,0xc29057f6577458520e7e,0xfe97595614839fb2eb2a,0x558520affca2eab0a41c,0x3bdaeab1a849057f6537,0x2c6a92417ef915954248,0x9077bdd16354920ef6ba,0x9459553482fdf22b22a4,0x8d20fafca2caa9a41f5d],#[0xfb2eaa2c69075f5d5545,0xab1a415fd95dd163482b,0x5efe456455120affca2e,0x61954483e7f28b2aa890,0x20d7eb2f02b22413ff91,0xebc0ac89067f5d781591,0x22413fd95e05644833fe,0xf6478559120f5fca2cab,0x774482bff22b2ae8904f,0xedfca2cbba2415ff9159,0xc0aca906fb6098159520,0x419fe87605654833fb0e,0x1f8159520df6c1702b2a,0x54833fd0fc0aca9067f6,0xeca702b2a41bed92e056,0xaca9067f65f81595209f,0x3fd91e11654833fd2fc0,0x6154140efdb92c2a8281,0x2ff32eb0aa0a06fee09,0x32e2a82817f998585505,0xa05fee597154140dfcc,0xb9660550503bf2ecc0aa,0x54140efcb1ee4a82817f,0xf7322b22a0a06fe58f82,0xcaa8281fb99859150503,0x7dee5d6554140fbccba,0x461950503bf722bb2a0a,0x140dfdc8b0ca8281fbb9,0x302a8ac0a06fee5d8654,0xb02817fb9754560503fe,0xfee157158140efcb92e2,0x560503df2cac0ac0a06],#[0xefdbab02b0281df9756,0xeb2ac0a05fee45825814,0x281efb9759560503df32,0xe5d8558140efcc8aeab0,0x31502fdf24baa62a05fe,0xfbb92c2a8a81def925d5,0xaa2a06fde1d6154540e,0x1f75655c551502feb2eb,0x97154540dfac32e2a8a8,0x502fef2cb8aa2a06fde1,0xc36e4a8a81d7d65dc951,0xa2a067fe1b7254540cfe,0x7f8759551502bfb2db92,0x554540ebecbacaa8a81b,0x33ff0ebb2a2a075fa5d6,0x70ea8a813ff976195150,0xa077d5c971585409fecb,0x75549615037bf06a92c2,0x8540defc1ae4b0a81d7d,0xfacbb92c2a067f61d725,0x6b0a815fd95dc9615039,0x6bf61d6558540deebaf0,0x595615039fb2eb2ac2a0,0x40bf7c92eab0a81cfe97,0x22baac2a067f61d75585,0xa81dec925d561503beb,0xfe497558540ef7c92eab,0x5615033fb30baac2a057,0x9ffcab0eb0a815fd92dd,0xb2ae2a067fe19725c540,0x813ff9859571502bfb2e,0x5b855c540cffc32eab8a],#[0x2503afaeab1aa4a04ff6,0x6c8aecb1281cff915d96,0xee4a057fe45765c940f7,0x5ff91597725033fb0ab1,0x6554d40cfecc2cbb9281,0x3ebf2eb2aa6a07d765d,0x92eab1a817ef925d5635,0x6a077be497558d40ef64,0x98160165502bff24baac,0x59540dfdc0b00b2a81bf,0xf7728c02caa07ee61180,0xb2a81f797560165503,0x75f5d58159540f7cbb3,0x7605655039faecc0acaa,0x540cff43b02b2a819fd8,0xaedc0acaa075f5d78159,0xb2a819fd87e05655039f,0x7f65f8159540cff43f02,0x5655037f321c0acaa05,0x9fecbf02b2a819fd97e,0xebaacaa067fa5f815954,0xa81d7d915d565503aff0,0xe457659540e7fc3aecb2,0x65503bf720c3acaa073f,0xf7c930eb2a81dec9261d,0x3acaa075fe558759540e,0x13ff9161d655037f720c,0x58759540cffcbb0eb2a8,0x502bfb3143acaa067fe4,0xc8f0eb2a81bf990e1d65,0xeaa077ee41815d5409fe,0xfd8660575503aff2ac0a],#[0x65d540affcb302baa819,0x2bff22c32eaa077ee418,0xf02bb281d7f956197550,0xa04ff647855d9409feca,0x85e05765033fb05c0aec,0xd940afecaf02bb2819fd,0xff22c2aeca057fe45825,0x2b02a1df9725c560542b,0x6fee117158150efcba2e,0x60560543bf309b8ac0a8,0x50f7cb2302b02a1f7954,0x30aa2c0a877edd181581,0x2a1ef99159160543ef3,0xbe49744c550f7ccbac8b,0x561543beae4b8ac2a85f,0xebfba2a4b0aa1df5745c,0xb92c2a86df61d5258550,0xa19fd875c9615437bf06,0x537258550ebeaa6e4b0a,0x15437bae9c1ac2a857f6,0x7c92e8b0aa1b7d875516,0x2c2a867f61d7458550bf,0x3ff9461d61542bfb25ba,0x725c550dbfc32a4b8aa1,0x433ff0cb92e2a875f595,0xb2a8b8aa1b7f86551715,0x2a876f5d1645c550bbec,0xf9759171542bfb2eb22e,0x5c550ebeb2ae8b8aa15f,0x7fb2dc22e2a867fe1974,0xc6a92a15ff945d971542,0x85dfe456454950ebfba2],#[0x15d962543ef720bb2a4a,0x950f76c8ac8b12a1cff9,0xf22bb2c4a87bb6457658,0xb92a1f7b9059572543dd,0x7fe45765c950efdc82ec,0x8f72543afaa8b1ee4a85,0xaffc8ac9b92a19fd845,0x4ba2c6a867fe4586dc95,0x2a15fd92dd163542fdf2,0xe517655150fbdc82ecaa,0x64543aff22bb2a8a87cf,0x7cbb300b22a1fb974601,0xa2c8a84ff65f8159150f,0x1e7d8159564543e7b0ab,0x98559150f3ec3acab22a,0x543df720bb2c8a879f5d,0xc0aecb22a1ebf945d964,0xc8a873fe457659150e7e,0xbf9461d645437f720c3a,0x55d150dbfcab0eb22a1b,0x3bf720bb2e8a87dee416,0x2ecba2a15ff915d97454,0xa867fe4586dd150edfca,0x84605655436fb04c0aca,0x9550dbec1702b2aa1b7d,0xf720c22caa86df613815,0xbb2a1bf984e0176543e,0x5fe653805d950dfdc270,0xe11765427fb29c0aeca8,0x50cfec1702bb2a1bfb90,0x9c0aeca867fe0b815d9,0xb2a19ff84e05765433fb],#[0xfe47845d950afeca702b,0x551583deac8b8aa2b067,0xf76ca2c4b8ac1bf7845c,0xb12e2b07bbe51625c560,0xc1eef9558971583ddb2a,0x1152dc560b7fcaac8b8a,0x15833fb24c26e2b067f6,0xfc8ae8b12c19fd956137,0xac4b07bb5d38158960b7,0xeef915d562583ddaebc0,0x815c960f764c2eab12c1,0x833fae9c0ae4b06bf593,0x8ae8b92c13fd94e05725,0x4b057fe45755c960affc,0xf91597725839fb22b2ee,0xdd160affc8aeaba2c1cf,0x9ff22b2ee8b073f64565,0x2b2ac19ff9161774583,0x6bf6118159560d7ec13,0x4e05655835fb05c0acab,0x560f7dc8308b2ac1afd8,0xb22b2ee0b14ff653815d,0xb8ac5cff915977058b9f,0x7f65580dc562cfeca301,0x16558b5fb02c02cab16,0x2f76c8acbb82c5aff816,0x8c06e2b17bbe4565dc16,0xac5bed956037158b7db2,0x6518059562f76c2300b2,0x6558bddf28c02cab17bb,0xaec1300b2aa7eec97601,0x2caa9fd76498059553f],#[0x7f5d846016554febf24c,0x18059553faeca300b2aa,0x5973ff04b8ae0b2fd7e5,0xc16e2b82cb9ff845c570,0xe0b2e7fe13715c165cff,0xfb905d170596bfb29b8a,0x25c565ddeba708b82cbd,0x73fae4c06e2b2d7fe417,0x301b8acb5ff905cb7159,0xb2d7fe4980dc565cfec1,0x94603715973fb08c06e2,0xc565cfec9301b8acb5ff,0xfb28c06e2b2e7fe4980d,0x5b8acb9ff94603715973,0x6fe5c3805c965affc830,0x8500360010a00530000,0x46010a00704030801310,0x60366018f00b58051c02,0x8ec044f021400fac074,0x6180a9205170272812cc,0x101a140ca6062102e701,0x3d001d8c0e6206f4036,0x8bb04448215c104a07d2,0x3009fc04c982558121c0,0x815c00aae053e0292814,0x314c18160bad05b282c4,0xc2035741a560ccd064d8,0xf0731038941bd00dab06,0xf9e07a583c0c1d8c0e9,0x24e10d4084b8413c1ff8,0x1824a4121508e6845e82,0x50a0277e1377098704b],#[0xae3855d02a6e15100a4e,0x5b0b8985b002cf0161a0,0x4187b0c1f05fac2f5c17,0x34e41a560ceb865b831f,0xf3c373a1b6b0d8686abc,0xb87364390c1c3e0e0086,0xf368783c3ba41d8a0e9,0xc0fe207d983dfa1ecb,0x56216e1088082f440d42,0x445d82299111d887f843,0x93b84936243d11e488d5,0x25897b44b34257e12ab8,0xe13c609d104de226a913,0x2891142a0a0304fe027b,0x36e299014b48a50851c8,0xd4561c2abb152e8a8285,0x8b15457ee2baf15b90ac,0x6de8b6005a9c2cf0164e,0xf917638ba285c842dfa1,0xa2fed17d80be245e822e,0x61fa30d618520c1f4606,0x8e4642431bf18c10c514,0x50cce065f632be19408c,0x1a298d08467b2339c19b,0x5791aa38d3fc69843490,0x5436571b128d7746b6c3,0xc6fc037981ba28dbc86d,0xe54c721638ce1c3d8e0c,0x528e948741439cd1cc80,0x81de80ee4c76ac3b0e1d,0x3d4e1e8e0f2f878ec3c1,0xce83e2c1ef78f6c87b00],#[0xf47f803f6d1f878fb487,0x103c4817e408d201d0ff,0x1169073c832441602097,0x1921c790cf0861442ac2,0x8454f227e112a488ac44,0x8d4246592308917248b1,0x508f56476e239e11ba4,0xf125d891d84883242312,0x256f12a8494de4a2724d,0xc5c260a12f5c971e4b47,0xca4da826aa93408995e4,0xc9dc84ea72735138e09b,0x3f4c9f424f6f27a413c2,0x7714298a0fe502c28029,0x6290c94668a2d0511528,0x5397299714b14a526525,0x9d254b72a4295070a7d4,0x68abd055952ab1954f0a,0x15d6cae5256e12b36958,0xc2516060aff857ca2bc1,0x202ce1165bcb1e058a82,0xa5b6c2da296bc8b4fc5a,0xb9a85ca22e32970a0b7a,0x814bb905d8b2eb21749c,0xa97b8cbd4c5e7f2f2697,0x2fee97eacbf085f5d2f8,0x13a307918250c06c6004,0xaa622330f8986fcc31a6,0xcc63a62f6316d18a48c4,0x9240c84e63ea31d698d3,0x199770cb3e654132719,0x6339719b6ccd26664b33],#[0x68d834481a0c8cfd4677,0x41269e234d81a624d282,0x14d5fa6ab5352b9a8ecd,0x1afdcd7746b9335b61ad,0x68e9b354d91a6c5b361a,0x3836fd9b6ccdad66d4f3,0x26f6e37829ba9cdcd46e,0xe1ee70ba382e1c07cdf8,0x9a8e44471b938ad9c478,0x31cdd0e65872fa395e9c,0x3a739d224e8ae73f939d,0x62e3b039d754eb467550,0x1677383b621da1cecc07,0x4f15678793c189df20ef,0xe718f2e679363c879e37,0xa21eb6cf4fa7a563cf69,0x13e3d1f14cf82c7bb83d,0x7d7f3e8b1f3e8f9907ca,0xec07ee13f521f894fba4,0x4d011680173fe79fe1cf,0xa092d03da81a5409e203,0x1b8a0cd1061a82db4154,0x974232a10a107aa83a34,0x485c242bd2149d09be84,0xe1286cc4347a191d0c1,0x24910c087f743cca1ced,0x1a269d12d489224472a2,0x457ca2a6d146489df44e,0xc4b460ca2f9d176a8b62,0x928d604691a33f1193c8,0xd1de88e8b4727238451b,0x417120808fd747bca3d1],#[0xc6a4541221090c048472,0xc496724995245091e048,0x941549fca4f4926fe932,0xa8c95094a66252112878,0xed2d7c96604b0c256652,0xa60412f7a97754b9c25b,0xcb12646931e698c14c3c,0x14d67a6941343c99b54,0x89c424deca6e1936a89b,0x3b969d994e8d272f138e,0xe593e449ecf4f3e27821,0x5283314108a03c4ffa27,0x512aa8861438aa172509,0x39c51baa8ce145b4a29d,0x8a4bc5245290b1479ca,0x94bf0a5c652c4a95314a,0x9c4d4daca6a45339298a,0x1ca9fc54f52a78253a2a,0xe54b7aa49d5192a88c54,0xab92559a2abdd54f0a9e,0xa8eacf45650ab13957f6,0x155d10ae2a56f6ab6695,0xabfc15f92af76579cabb,0x89bac3656122b0545816,0xf7594cac8c163bab18a5,0xcb41759f82ce1d6668b2,0x6abcb5005a5c2d195687,0xa3d6ca4b5ff5ae6ad66d,0xadee96ea2b6fe5b60ad,0x5c5fae20970a0b81e5bf,0x9e55cd9ae529725cb8fc,0xeabac35d3dae8f97444b],#[0x977a6bb965db22ecc975,0xf5457a28bcd75e3caf09,0x832fa497c68bde15ed22,0xd5ff7afe9d7ebebf225f,0xc162608d303758140c04,0x568c26c6112307f58354,0xed8766c38161a7b0c1d8,0x3149989bcc496622cb0f,0x37331a798c96c5f862cd,0x4363fdb1ecd8eecc72e6,0x6c96e649332379912cc8,0x95eecaa4652e32825935,0x12597c0cb9865b332cd1,0x3b36299a9accfa6648b3,0x6758339759c6ccdee66e,0x1867f8b3e799eaccf19,0x66d1016867b4275a0c0d,0xda40cd1c968c634595a2,0x4ec1a6d0d2ff694b3490,0x76352e9a8fad44069fc3,0x56b113573daaccd5296a,0xd7536b8b35b91ad64d67,0xdcd8266bfa35f35af20,0xa9b2dad9256c5e36255b,0xb6a4db4acda196cf9366,0xdc136d41b63cdb026d62,0x9d6e3037061b7ccdba96,0xedd7b6e9f37431b99edc,0xbc66de226f0337751bb2,0xdbdbe64deea6f5137995,0x381b9c078dff46fdbb7,0x70ca38589c24ae0e8705],#[0x2997133b88d5c3f0e1d1,0x26e36c71a838c79c5d8e,0x5c848e3fd71eb38ee9c7,0x93c9c96ae48e72393918,0xca3960dcab8e5407297b,0x173183987dcbdae5bb72,0xe6dd7360b9a95ccfce64,0xf82e78f73b439cd9ce08,0x3dd0bae84c7407b9fcdc,0x3a5e1d276e8fe7460ba2,0x549ba92dd432e9dc74d5,0x6c7597bac79d5eeeaba7,0xcec1e75f63af15d73ceb,0xda5cecfc76653b261d8c,0x9a9dc18edcf76cebb555,0xe3bdd1de6eeefa775ebb,0x785dbc1cde082eff977d,0x1ec78d7bc5f5e26af0f8,0xccf2ca794c3c96de43cf,0x5e75cf37c79a53cc61e5,0xd351e92ef45a7a03bcf5,0xe1bd645eaeaf5387a833,0x27b45bd939ec22f5f57a,0xf7647b9ebdc01edc8f6b,0x156f86e7c18bdfd1ef58,0xedf312f9367c87be375f,0xbe9e1f48cfa147cfc3e6,0xdbebed01f61cfae77d5a,0xf07e4ebf155f81afbba7,0xcfd087e813f3f1f9ecfc,0xfa4cfd207e8d3f451fa1,0x511fa7cfd387e993f4b1],#[0x13f571faacfd507ea53f,0x7ebd3f5d1fadcfd687eb,0xd987ec93f631fb0cfd80,0x6cfdb07ed53f691fb3cf,0x1fb9cfdc87ee13f6f1fb,0xf7b1fbccfde07eed3f75,0x53f811fbfcfdf87ef93,0x87f113f871fc2cfe107f,0xfe407f1d3f8d1fc5cfe2,0xcbcfe587f293f931fc8c,0xf1fcecfe707f353f991f,0x3fa51fd1cfe887f413f9,0xf593fab1fd4cfea07f4d,0xd07f653fb11fd7cfeb87,0xcfee87f713fb71fdacfe,0xfe0cff007f7d3fbd1fdd,0xc91fe3cff187f893fc31,0x13fcf1fe6cff307f953f,0x7fad3fd51fe9cff487fa,0xf787fb93fdb1feccff60,0x2cff907fc53fe11fefcf,0x1ff5cffa87fd13fe71ff,0xff31ff8cffc07fdd3fed,0xf53ff91ffbcffd87fe93,0x880013fff1ffecfff07f,0x20800d40052001d000,0x7d00388019400b2004d,0x7200ad00508025401120,0x401d200dd00688031401,0x4940232010d0080803d,0xb0805540292013d00988,0xd00c88061402f2016d00],#[0x1cd00e0806d40352019,0x41201fd00f88079403b2,0x140472022d0110808540,0x809d404d2025d0128809,0x15880a940532028d0140,0xed017080b54059202bd0,0x2031d018880c1405f202,0x6b2034d01a080cd4065,0xe540712037d01b880d94,0x880f14077203ad01d080,0x20080fd407d203dd01e,0x43d0218810940832040d,0xf2046d02308115408920,0x40952049d02488121408,0x139409b204cd0260812d,0x90814540a1204fd02788,0xd02a8815140a72052d02,0x58d02c0815d40ad2055,0xb9205bd02d8816940b32,0x140bf205ed02f0817540,0x818d40c52061d0308818,0x338819940cb2064d0320,0xad035081a540d12067d0,0x206dd036881b140d7206,0xe32070d038081bd40dd,0xd540e92073d039881c94,0x881e140ef2076d03b081,0x3e081ed40f52079d03c,0x7fd03f881f940fb207cd,0x72082d04108205410120,0x410d2085d04288211410,0x22941132088d0440821d],#[0x7082354119208bd04588,0xd04888241411f208ed04,0x94d04a0824d41252091,0x312097d04b88259412b2,0x14137209ad04d0826541,0x827d413d209dd04e8827,0x5188289414320a0d0500,0x6d05308295414920a3d0,0x20a9d054882a1414f20a,0x15b20acd056082ad4155,0xc5416120afd057882b94,0x882d1416720b2d059082,0x5c082dd416d20b5d05a,0xbbd05d882e9417320b8d,0xf20bed05f082f5417920,0x418520c1d06088301417,0x319418b20c4d0620830d,0x508325419120c7d06388,0xd06688331419720cad06,0xd0d0680833d419d20cd,0xa920d3d0698834941a32,0x141af20d6d06b0835541,0x836d41b520d9d06c8836,0x6f8837941bb20dcd06e0,0x2d0710838541c120dfd0,0x20e5d0728839141c720e,0x1d320e8d0740839d41cd,0xb541d920ebd075883a94,0x883c141df20eed077083,0x7a083cd41e520f1d078,0x520bc783d941eb20f4d,0x3d070208c213423c1832],#[0xcf84f0447c1c0f423c18,0xc0283207049c402360d0,0x8f060f41c0e47c1e8380,0x78307a0e0503b60b80f0,0xcf84f0447c1c0e01784,0x181602f2280c84054016,0x381ac238243a0bc0f838,0xe82c1b007821448740f8,0x90e83819c121db0a07c1,0xbc1083217c2508f07e0,0x5801c241f0703211400,0x3842081c203d0822820b,0x141e838082183d070104,0x3d07020a283be0a0f838,0x2005e0087c1b09e0f040,0x83e0f8a0338021f06c,0xf834e1108c1f1815384e,0x782c11e0f800381c1520,0xe270004e0aa0a080abc2,0x808e7c1e8bc001382a43,0xc58004509503a11c183f,0x4a81d08443c3004a280f,0x40ffc351407a2f86f02,0xc312a1fc37812540e840,0x181f88e37c1804f020bd,0x809fc351407e2400074e,0x102f06c383ff0d4501e8,0xc0903618c6f83f0215c5,0xe1b8a03f14c6f83f020b,0x215c5102f06c480404f,0x40700fc231a013c1f02f,0x1a8a03f1015786a280fc],#[0x2713c3110a280fc4221e,0x351406649c4f0d450199,0x5c6f83f020c9c31271fc,0xa5c6f83f02e181f8c0a,0x1be0c00781064e189390,0x8f02637c183206c30387,0x18df07e041901206c303,0x60c81b11e181571407e2,0x6c202900bc0bc098df0,0x83e0027c1b060b78009f,0xe0fc082a0602f008280d,0xaa37c1f8104e0cc551b,0x198361646f83f020c01b,0x141569f2601c8df07e04,0x856283005e05c004f836,0x368504e3f86d08043806,0x8178382346f83f03c034,0xf4705406b00588f07e0,0x7a3038b1be0d00781b0c,0x307a283831be0fc09220,0xf83f020f47071e04c6f8,0xc1f8107a384c044074c6,0x6c303f1c2581d070637,0x80d8190c0e2c6f83401e,0xb280d8178a0a7c3582b2,0x83f02131c303d2ac1786,0x303d181492243b215c6f,0xdc303d2414b8df07e05c,0x321d071411c6f83f0212,0x7a483871be0fc0b8607a,0x8001c782245e07c198d0,0x9e0cc6e850960f4aa09],#[0x30980f4a2440741c781a,0x3a0a491485f03c10c6f8,0x1789f070289f05e0e030,0x820ec2f70a27c7c01e08,0x107617b851423d820650,0xf030741783222c103284,0x8391a0f46b05237c1a00,0x1c8d70a0bc7059077c0f,0xfc081d07a302cf03077c,0x15d1102f06c383891be0,0x16141e89f1546f83f02,0xdc01e0b8203d13e3f82c,0xf82c016141e8a1150e82,0x43782f03e0dc2c8d07a5,0xbdc28152a11015059076,0x1642283be07c1c8df040,0x37c1f82f02e140e83d24,0x3c13c1c8d07a5c220712,0xa0e81905980243782f0,0x4e00252c28a11417838,0x1f81095c138004405447,0xfc0900d0c0bc5510a37c,0xb78009f07a268d209e0,0x8a107a222243a27c1e88,0x16781f072341e8a8890e,0x1c2500291be0fc083d18,0x8246f83e09c0117838,0xf07e040868de09c02c29,0x4451be0fc0d8505e3e86,0x604491be0fc083d18260,0x3e468df07e074303c142,0x4888ec85e09e0b8003d1],#[0x7e0782700021a1b4290,0x4292095c3194078268df,0x1071be0fc0b86e09c03,0xc0810d1bc13805852025,0x1fc1d88b020f46d0de0f,0x5e090ef83b100e0803b4,0x433623c18381e83f8406,0x4c43a0c8178e0abc2782,0x621d0640bc851be0fc08,0x60e83d1546f83b05e042,0xe0e46b840643c8df07e0,0x7e040e83d141678183b,0xdf07e060e83205e448df,0xa8df060c81b0f6090048,0xc0f8351a0f49052033c0,0x5c1e9580282f82144877,0x828a2f03803c1a8db081,0xd46f820656100c94876,0x60741e900b01121df03e,0x5e3829f05613c0a8df0,0x3d2646f83071e060e832,0xa0be09c248df07e041c0,0xc1603d0b0383807a1c86,0x12946f83f03c03828271,0x4417c0a8df060c81b10,0x3201e074303214e4038d,0xa8df07e041e8c0e346f8,0xc0f8351b610190e12c0e,0x37c1f81b080c8605808b,0x3d1246f8307a0e04096a,0xe060700f4291be0c1c0,0x20f4503b237c184b07a],#[0x6e01c14138e12e46f83f,0xf00e0b6108d1be0fc0e8,0xf8320f43783f0204346,0x4420f43a0087c1e860bd,0x83f0212e0eb840643d00,0x5c1df07835c20321f06f,0xfc084c83ae1417900b02,0xe0f06b8505e3820c1be0,0x8a0be0f8320c1604c83b,0x10a1d150bb84b0a8760f,0x37c1f8107a3217709616,0x3e0f06d84064404b03b8,0x7a0741c0c1281621df0,0xdf07e041e8e04bc1e0d,0x1e0db0a0bc80981100ee,0x8f836102502c43be07c,0xe0ac203d23a87c5019c0,0x321bc211d0980b60f8b,0x78321a04e08f060d816,0xb400491504e08f060d9,0xc0834003d0922032f09e,0x90dc23c1f0104fc14118,0xc1e8646b4110506c07c1,0x2178168023e0d85e0447,0xc0e286f83f03a001b0c,0x1e860b3c0f83a1ba001b,0xc4283683e0c8444047c,0x205a0f60f8c0da0f832,0x38007a0b60f8ac09c07,0x6c3e0df07e041c03d149,0x20c16085f03e0f06b800,0xd834320bc1c0c0d90f83],#[0xc1a1951947c148b42381,0xa3e2d83432e1014d1f16,0x830460fc470960c08829,0xfc5e020ffc183d1380f,0xc230178dc0400023f06,0x39180bc1c08c3c197837,0xa44033e0e4621105e2f8,0x723108838160cb1f9180,0x22e1bc188c05e3419f0,0x81e8bc23c183807a2419,0xe0c1c03d0c0e838e0360,0x8816381f08e020e01e8d,0xc303205e3f834236181e,0x41c03d1846229423e0e,0x2866c10381f8401df07c,0xb0da15088ee1381a1ce0,0x1170c0d86432e13c1d82,0x6103b040d8705a867c1c,0xdc183807a3386e021000,0x67c189c046381a611c0,0x7c041e8381408f01705,0x7039066c231f0523058e,0xe05833e0ec2211070292,0x20c81c0a0741ed84e020,0xe07c041e838180cd84e0,0x19e07c044e0381c08d84,0x1832e11c041c120d8118,0x380838182c03605f613c,0xe0c1e838140ef0806561,0x3a0f6c27010702c11b09,0x8465e0ec238682286464,0x1922040dc3011b09a14],#[0x8f08f07613808321820,0xc91020643ec368523,0x3811c221da280e047081,0xe91405e0e04023424178,0x7a281d8236120f832140,0xc2340bc603a0b00fb820,0xb84b0a0b0803ba1fc182,0xc2c1f142b82f0648740f,0x101ee8623440117080f6,0x8450190e07608983d0ee,0xa280c8512f04687a1db0,0x8343a630178a87408d84,0x3f83b04876c282f1f83f,0x7a2006a280bc1c080478,0x483b4501e8a07508d140,0xf440716090883d1008b8,0x5c041c03d17c181db040,0x70ee0f8083807a4707b0,0x227080bc209607508f07,0x8a411016421840e14c10,0x97b040b108b8483e0c88,0x104783b07c5003d120e8,0x5e6582305c0419784070,0x74c6707f0684780b850,0x702801e8a0b010387653,0xdb0e28b808381f83f010,0xd87b09c041c0fc1c1901,0x23e020e0705fc1c0e,0x5c108a207028a2e0f610,0xc0460e8a26280c854001,0xc0d07784032b088441c0,0x81c0dc201901db09c041],#[0x441c0c08c0cf07e0228,0xe0441c0e0bd0ed8443f,0x643e0d8407a0eec201d2,0xa11c11a0ccb832178001,0x8a1ab0903ec170043e4,0x17047830700f44b2f442,0x8583e48580ae07c1603d,0x43483ec1423220e13806,0x8709c0d41f00b0da14c,0x141f1908a0fb0449c486,0xac3685250d20fe01a16c,0x321141f82381a83e0160,0x6c202d70fe0f8002c06c,0x3059a14178bc000621f0,0x608b0761380038270478,0xc1c11070305806dc0c19,0x178000f43e3387b080f7,0x603f8021a43e2a23507a,0x3404488584d0a87c644,0x1ac116101ef83e000e07,0x3e08607c01c300fd0a38,0xf0400ff06e1b42a111c9,0x822c2083022e180d0e49,0x8e4438000fd0b07c5121,0x4c10243c1f0001f61b42,0x10f838160a21132f87c,0x9a0e08a1f0702e83b09c,0x1a8c12e281105387c3b0,0x3e231f12e0c83f07c041,0x3e020c85b89401c2c976,0x7c1907e0f8082316e278,0xdc23c183fe020f47d08c],#[0x18b71a0a0970641882e0,0x28f8320fc1f07e0dc041,0xc0c51701e100e01e8fa1,0x382fc1f0807a0e040b1,0x2441c0f84584105c0780,0xa204215c1c0a15a138a,0xa20220ae2820f83d148b,0xe002881c13c218883807,0x382613c20119c0f84701,0x420c0d017000ac28a0f8,0x10405c020f8a20b03841,0x4449a220e10f83d10162,0x81010785ee17c1d84d0c,0x807a2097b0987c1909a0,0xd84d05a18888fe0f8403,0xc251fe000d8320ee17c1,0xd056181b0e1038061406,0x23e0d8440fe0f80f00,0xf0000e00f410361c207,0x817f08e03c001c141038,0x4841c0c08b8185806c0c,0x20f41c0889c0e684e00,0x8083d1b8083d0701a84e,0x10f838102583f50be0f,0x5545040b01042221c,0x183b40fc078003823427,0x38068423f614607ba13c,0xc0780586b0ba10b08084,0x76384007604003803005,0xf200800700600b423860,0x8043c0e110709c0342c1,0x7005e0f80686d0a03c80],#[0x701e00e1743584280800,0xc403d1c2001000e00c01,0x7c1e876041fd86409e0e,0xa4410260022967c9c086,0xb0dc0b420e05c0a812b0,0x862280f45c2b848c3e00,0x238870ae341d0a800185,0xc0f47808e39c403a120,0xa07a2c04702e37c183f7,0xb86a180bc370d011c083,0xe0f45e048890a99f06c2,0xe048541b0c0ff0270233,0x8307ee181e88e1ac1a22,0x15c51036145103607e1f,0x8c288c683f07a2017400,0x1b076181170282ae1413,0x5e2702b0c0f4382a848,0x4482a2881b0761b81385,0x8010659f23c1f02b0c0f,0x5a148033612c1812220,0x41b0ce1230f60700586e,0x83d1c14d1005a864cfd1,0x1f8960500586f0762019,0x2202b8d0742386f060a8,0x8d07a2400818e21c708e,0x1b8171a0fc1e8b409c43,0xa81383702e341983d19c,0x1e8815c1b03f0c1f83d0,0x66c2386054418db060fc,0xd0481b0a0b414f02f068,0xe05611c3032150cf8370,0x81f078001c58606c4f83],#[0xc586e040d87833634067,0x86970013e405702bc0c1,0x6114f914420782de09c0,0x6c2d17a24a1688502e01,0xf2240d8305ba07800d20,0x1a41ee138002a93e309,0xc301a90a83dc231293e3,0xb083805e05a07800d206,0xc1a8bd1250f40b43700,0x3e862a89287d03a1b805,0x15624c15c2702e01a064,0x2b8490fa1b40b12198bb,0xb8030490fa074330c218,0x21f40e8670ac486632c4,0x9c0340e8670bc089609,0x68290481b0c21c15826e,0xe0493e0d818061581118,0x80c30a0380f80584c280,0x402707e160405467c1f8,0x8160a2f07e0646a1206c,0x4a7c1f8191a8481b0c15,0x8761781700d11a0f468c,0xc182a53e0fc313e0d81f,0x19c024f836168929f06,0xc36080cf8049f06c282d,0xa1c6903607e202a93e0f,0xc08ac3702139c00138d,0x1f8815887907e002881b,0x6c361206c110f20fa18,0x8606c3781d1be0f43700,0x1e8607e290f20fe0f806,0x78170005327c421e41fc],#[0x4d0a4205609802c6d941,0x938670a987b03802c370,0x9b0760817a04053802cf,0x82d053c110c99f1c0e01,0x8f86b11e0c1e910bec1,0x47c183907a283fb02058,0xc046c4783b020f4807e0,0x23e0c1d83d141f81ab0,0xe4602f141c48c07a183f,0x609c3415054421d052c0,0x760815120b414a19f07,0x719c368508843c067042,0x84b1c11386b048560c82,0xc70a055c3704c01a1413,0x16c683a1102b04c01622,0x604d82588b1a0f46b10a,0x303d1e09d8331a0f4403,0x81e90089c6f83f02075c,0x2504070075c6f83f02e1,0x700741e900f41c1220ae,0x807a492231b413c1f810,0x45637c1781f07802c303,0x231b217c081df060f470,0x302209e0e0ed8607a202,0x3d120ed8607a181d02a1,0x282cb280f4383b61b428,0x7a348a0960b10e89f07a,0xb01101d0978004fd850,0x5a0f50ef04b0234870ae,0x943b45a0889f07a282c0,0x916823e17c102f02a27c,0x5081113e12c1c8c34850],#[0x82208d14212c2088348,0x707163017882345084b,0x2804f83d174318c07a1f,0x712340e84b07a398283a,0x1e92a181d03d0dc1b810,0x583b0304946904096074,0x32181e9004a0e83d0c10,0x9648d270405646f83f0,0x6e050c83891a411c281d,0xf0323700038b0a0f4a70,0x8d90c0f4883a08bc1f82,0x282f146941d033e0fc0c,0xf46e860781e1dd1ba1ac,0x4b0a0f60e87a374303c0,0x274568d0b827009280a8,0x503c16f02e0834b8009f,0xe0105a0889f07a3d2f03,0x1ae01a046903d1c4d285,0x270025fa144f960b4162,0xc5244474220a02041338,0xa046916a6a0782aa2aa7,0x9111d41e0178270007b,0x107a303e1a40f4309811,0xd82a2a304b07fe0d8068,0x40c87d0c5785d0da0543,0x31c632c578270070ac0b,0x4b0290fa05c2e8662a3,0xac13702e09a05c2e86e0,0xfa0c8cf04e0127c910e0,0xe016174f8c0f11791c41,0x11e0027c1e9004341f04,0x182fb0a40442444770b6],#[0x41e8985b08e81d0fa1bc,0x60c1c80f098203ff060e,0xa093e0a8508527c1e87,0xa204708527c1e89c1380,0x14027c1e8e1081049f07,0x93e0a850888890ec82,0x304708527c1e88283827,0x7a301df07e041c48d07a,0xf0983a02253e0fc0c8d0,0x8441911b835041182089,0x2503d185091570aa244f,0x302203d154148df07e04,0xbe0fc084407a302203a1,0x5ba081561533e28a091,0xa4a09c138068233e0a85,0xc02c36820544704e000a,0x1a08151083d03f04f07,0x2054484441e63782203e,0x89c138000f00e00c00e8,0x150441f827000600a840,0xf64f8a03c03803003a08,0x44744f83d198002de080,0xe00c081ec9f1642f0024,0x1a3e88d1c149f07a1704,0xd2545f04d07c0344585d,0x3ba37c1d00d0c0e34283,0x121a1b42d81e0842228,0x802d0da16c09203fc1b0,0xe83d1f8270000e043c1,0x181e0834911587e00e0d,0x9a37c1e86078268df07a,0x2700054382203a130220],#[0x38068623c0e8df07a1b8,0xf4307be0c8790750bc1,0x7bc13436850942b00d0c,0x4f07e0780686d0a12890,0x802f020f4250c04346f0,0x1ef04e01a18250ba37c1,0xd0a490f20fe0f4303d14,0xa0bc8810f50dc1081f00,0xe00c010010940f4751,0xf42900e18068607a200f,0x4b2263ae19c3b837020b,0xdc6f83f03c01c3685c2a,0x307c0f44b0c0f4209408,0xf06b0d6041e050101ff8,0x81286b02626c3d86f060,0x70c0f0570ee19c1b8107,0x8b710e0dc68ee37c1f81,0x3b837020f06d0bc13801,0x7c1f8170c0f05040e19c,0x1c01801d0a042c112e3,0xe2342810238270001e,0xd706e207702e1b82783e,0x6850203e85e09c00c138,0xc683d0fc1f8171bc1380,0xf061281e876181e85e04,0x860880f50ef82d0d6146,0xbc5d1be0fc082fb0a12,0x596241e8ba1b41832312,0xdb11e0c1c03d1f83e830,0x32f060641c1746a08a1,0x60236048d588f09e0843,0x648023623418380980ec],#[0x1158806541ec0a1d7090,0x82281d20f6074303d14,0x38098104507160c4f84c,0xcf83b02c320e8d60c4f8,0x3c1a19b02e120e8e2410,0xe13c1e86b03c14914e07,0x98874178c23f00019120,0xd51b4301e880e0091050,0x310e82f180cd0c05e1a1,0x1e0c5003d1c148195074,0x3a1301e92609c0c1d71,0x3d1229038044e0dc0c8d,0x284c03a0f4bd06a34198,0x52070082c1d81824a348,0x470118e0482641d07a22,0x3a130403ba1b41b82832,0x3f038014683d1c1c03d4,0xf8191b2181e920890ef8,0x51057101c0a283a057c1,0x3741e86b080c8691a800,0x2a37c0f8350c0f48c3ba,0x20b6100e84c2c1c58203,0x89481c583b0228a0aa8d,0x380922815b09074260,0x5c47837020b4a11ae0f0,0xf4706421882b8470484,0x7a3820f020e3c1c8d218,0xd2909105705237c18380,0x5e05c278391b8001c03,0xdf06e101e8382051022f,0x3823227c610de0a82c8,0x40e86e014306035e13c1],#[0x1f40f84d0d4646a32a1f,0xec1740e86709c008b04a,0x90fa0743319198e31990,0xfd076108ca9f1dc2302,0x6e83511c00148f0bc114,0xb447830700f4510de0c1,0x47743f83d020e01e8c86,0x32201f81af060ec1e8a,0x5c3584740e87d0de0ec2,0x2c1c0606b447830700ec,0x382103e81b0c0f44b061,0x4581ec2032b07a23800,0x8806560ec2700e0a0b08,0xf4600e00c1603d11086,0x400bc603d01fc1e8170c,0x205a0f45033815c0f831,0xff07a181e8a0a4c1e8,0x20f44b11e0c1c03d1021,0xfe0f4303d1bc1e8605,0x44d05e0c1c03d1021029,0xe0c5003d140e838d040f,0x8b623c183807a2042b03,0x1c03d0ec0832f0628017,0x7641588f060e01e8de0c,0xe10894907f07a181e8c8,0x7007646b831441601e8,0x81e91237c18a20ae0f45,0x302c60680980c8d14415,0x5a588d70708380038092,0x415c2420f06e23803810,0x1a0d81c7003188a8910c,0xa0a10282144e13c0f839],#[0x6de0e46b84e000e0ba0b,0x807a28a062a21b414200,0x83813e12c803b237c183,0xc08382420a23706a0824,0xc1d232e11c1f00512e21,0x1c28291be0fc084a07a3,0x741c48df07e042583d1c,0x107646f83f022801e8e0,0xe00ec0f00e0a0b0707,0x86a0b613800270963e82,0x3f00b0dc17410271c0bb,0xc6f00e0a09c258a83d0,0x1c01801e01c141384a2,0x94e138070506609c501e,0xf00e00c00e82e01c1413,0xc1b510a341e8a12ac300,0x82f00b09a2341e8d1f41,0xb0c0f453060e01e86a2f,0xc50320e025860b7c1829,0x2882c0d6181c70007a12,0xda106b1007546d83070,0x1e0a3838d1b60c82900d,0x381c48044d09e0f4358,0x148f08c0cf00b11e0f42,0x49121a13c1e86b03c00,0x4201000e00c016860536,0x73c0a8df06a181e90113,0x161fc1a1d07a28381440,0x20ae0f41e8407a0e0707,0x8307a08b83f000704c8d,0x1f8307015c30b0e1c437,0x8f234258380e4683807a],#[0x603ae1d42700071c1425,0x18804fa37807050ad288,0x1e90f20ea13c1700e0ba,0x7a230011e20f4303d14,0xf20fa181e88c17c1e86,0x928d50c4438070514439,0x7a230011e20f4303d141,0x3d08e18190ac17c1e860,0x387706e07420321dc6f8,0xc0f83d08e1b0c92c75c3,0xc1c03d0c25023544e37,0x3810067838320e01b0be,0x278307a0e04a01e0c1e8,0x7a2829819e0f4303d15c,0x30700f44053e0f435840,0x1407d8124258380a8008,0xa270002001c01802d0dc,0xf021281e8a4a50ed8207,0x425584142503d0b46f83,0xe06c204a0643129d0dc1,0x8ba1b8004ab08268df07,0x2604112447039120e01e,0x140f02c098104403c0b0,0x1d83e381d0984820f83d,0xd03d1c8bc2025fa15c21,0x425901280ed06d11e0d4,0x282c120a0c4168853447,0xa0bc501903c8ea5206c,0x3d0b608178e21f40f06d,0x3d4a44745091a040380,0xc183dd0b613830f03ec2,0xe3c1d84e00268807621f],#[0x5c1b42d84280ee8807a0,0x81de810900400380300,0xdd0612c260411425849,0x340d709a0cc104c08234,0x3e440dd06609c284b082,0x1120781a821613803854,0x2001c0178370ba04220e,0x8e8a23c43f06d0a0bc50,0xb74103d1b8682f095232,0x30802503d181601d30e0,0xf070802503d1dc3b8370,0x4643b07c1e86075c3b81,0xf4608e0802511183e0f,0xa0bc7b0f6050ef83840,0x807a3783905622c08207,0xc1f07a2111119623c183,0x322243b0841e888890e,0x7a4090113a0a0ea1f07,0xa0e2c1b83b02e070684a,0xf832181160d0981101e8,0xe84b1825111b080b10,0x6160e82c288cf83c1a0e,0x4808930860f41381711,0xb0c1981c1b0742583d2,0x18e23c1d850580bc705a,0xc242174111f07a39111,0x122041a0a8683d182622,0x16020a1a1320e83d1816,0x149151510a87c8e84c18,0x1f07a302d6002320f83d,0xef0083e331210ae0816c,0x5c241f05a3b8205ae101],#[0x77420381842b82e000f,0x1b61425c1d180a832c1a,0x2a1ba102641d181682cc,0x38283b8341c03d141602,0xe9157080cb06d000704,0x75c2222c1b4001c0e88a,0x20810e900c1a0f4607b0,0x15308b06a1db09a14715,0x4407ae1043d00070283d,0xa000d51f13c181ac120f,0x3b81fc1d824340f4615f,0x40e2bfc1e80b0c86890,0xd82d016190d0ce12c102,0x3f83d00069c31281fc1,0x1b4003e1c1f58407a076,0xe0248a04003803004e,0x7008501c04915c238270,0x129036185025207a1b84,0x9485003d0f4111ae0360,0x2e01c22820640e0248e,0xe00c01686e0b6009e,0xb8043a0b60f8bc042401,0x47f83b03a1b8282f1b81,0x3c03e86f07c1417d811c,0x1a43e0f46c280f421060,0xf8307a108508503f810,0x7a202de0507c1e8801f4,0x204e0a88f88c0816c1f0,0x7c1e8623f40036a3e221,0xa1081003843e0f450858,0xe84217c1e81040e14178,0xe810380923887d03e0c1],#[0x6010f82d260eb83b0087,0x7a4c1d322c2542b84a05,0x76c1b83b02e07068380,0x3ae0ec1e0d0700f46445,0x6153077c1f81c1a0f468,0xf45b0f60ec08384400f4,0x60e01e8a88bc1e0d0700,0xc1be0c1c03d12c3b87b0,0x248a44b06f830700f45,0x61016c1f2606d834400e,0x5a3c52e04e010e910212,0xf1ec2580f07622c0a200,0x8a23c43f06f07a16c082,0xf83d101698070587c1e,0x16c0382c3e0d8405a64b,0x3dc3e282d7080f6c061f,0x158007b87c5b00e10168,0x3e0d8405b87c1e86e13c,0x2b000f416e1f1ac020cc,0x7c1e870330f83d0dc218,0xfe0fc1580e0dc14905b8,0xb06e094b8ce134081000,0x1221f60dc10a47887a85,0xf21521ee12c1b82188f2,0x180e0178a846c10320c8,0xc052c06c103216062111,0xe01e8a0c908d82066240,0x19100a83d080eb010320,0x8d84b040f4403b6101c2,0x1ee101e8b6098083d0d0,0x683ee094b832100e8112,0x10583e4690910f705800],#[0x2610118907c8d21521ee,0x46074097013082897c0,0x90f823144be013040c84,0x12522d82064125225360,0x6010700bc4046048c670,0x105e202f041c02f08c1,0x6301b040c80e8a0b0c17,0x811812058074c2701181,0x2160910f40d60b001161,0x92943e3184a02c070018,0x182a022a520460480e,0x470010f30bc046252c07,0x1d100e815e024a440240,0xba1114415c60336101c2,0x4c230107007450582804,0x1112901503a4a50f8a06,0x90f30bc045252c04c250,0x2e105e02e08118605408,0xd07818c2080640890fe0,0x10f8f03f41e06304240f,0x60844a484607e83b0540,0x660b03029120f00f40d,0xe1c1760c0c83d0708c2d,0x90360ccfe040b0102905,0xdc0853020db020667d0,0x95830ac182047025833,0x30dc08178b60ccfe040d,0x2fc09408c0b021509057,0x130dc083425638271c08,0x642412b0649c3b06081,0x32a046058108044c3702,0xa424635c18b638171c08],#[0x88784849c082a0c1509,0x845020aa820727d8205c,0xa0415300106902cc020a,0x284d06268353f4103019,0xe10d2a09a0e138904a08,0x4084341b0093e2e8313,0x3e23834248404f896381,0x40b60c4f8a349092101,0x8d22214090289f148911,0xdc10402c044c358342a2,0x4760cc1029100d01130,0x81e880580881530c0f45,0x61b0258107a3411072e1,0x704141ec11076184c21e,0x2598607a181a0220f4c3,0x52268c6b830902b8e04,0xdc0c150c1488542ae044,0x60220f4421fc11c08643,0x9f8220e5c2c15184f81,0xa0e447056064303d1069,0x252e0c2409f101e81170,0xf823810c6912942a27c4,0xf44f89a01fc00260c43,0xf0023a2c2c033a058208,0xc2e83e0104481a448b40,0x2434811c6903913f059,0xbc00088a27807e83705c,0x3ba0e4fb04140b08670,0x4641f41741f0013e2c29,0xf451a447341f0093e46,0xe5078d21b40f00072,0x520f41c883484fc85e],#[0x81a90c2078003d01e370,0xec545707c002412913e2,0x93e067820c34b8002d13,0xfd0bc004f880766902d,0xc8403521b4170030c29,0x340464303d1500486098,0x4822e12c083b07028380,0x1109033081e8117080ec,0x292340f8442ae11c103c,0x218444606980486101e8,0x8069c20110c1481a023,0x14e81232382913da0c86,0x340838144f11cd07608,0x5a0d806810702820d06c,0x303d10c1281065208404,0xac26810760e050960e14,0xd0356101d880ec1c0486,0x148408a4083d076203,0x2d1446b83e000e0248b8,0x3810521a23504e07800,0x20b4211ae0c1c049130,0xc0861148d18d706c0057,0x880e111e01604620a83d,0x507d4d45223a130605a0,0xe8a4804d25223a130524,0x340838149109a4a41308,0x7180681070202a018c0,0x3810581890703a081608,0x168220384478041f1f00,0x642838505c041909148,0x4e020a8207140580980,0xc04879161280b013000e],#[0x8803302f0121e4445033,0x87f03c3e1f033000e30f,0x21f87c5e066001c61f10,0x330043f0f8a074c2703,0x681d2124420ff021c107,0x908383d0047c4d0d1481,0x54984e8023f214c28c84,0x3a059c2580ca587c0c8e]]
set_option maxRecDepth 16000 in
def g251H8 := limbs80 #[#[0x10011100010232,0x12312140024210204002,0x101310120111001,0x5210032001041010220,0x2110000170000101310,0x1010050100120401131,0x20120000352302202003,0x10010020020020110020,0x1000920013001200011,0x41100901410000301000,0x10000022300033010000,0xe3680000110000101,0xc07e000000001f842da0,0xa856548e0bc0004091,0x22b500000000232000,0x749a00000,0x29836c32c00018428000,0x1a880000349888,0x6ac2753a0,0x5178e38460b80000000,0x0,0x3110385f00000,0x40d2000000000000000,0x8600003a070000000000,0x18a2093e00014,0x2a940001b4200000000,0x1eab80000000000000,0x0,0x5f0f1000000000000000,0x97c0000000d2fe25eb63,0x5ba3c36c71cf89980f9c,0x1a16],#[0x28de80000000000000,0x109200000,0x1a000000000000a5e,0x0,0x69dc4958000000000000,0x70b200001606847,0x1d69800018e2000000,0x0,0xe8d40000000,0x0,0xf244000194780001b540,0x20ac79a215,0x1864800,0xb3832774000000000000,0x64c3ef4a600000000000,0x9110f780000310000149,0x14a940000000fa1c2,0x3800042c0000387b0000,0x2d540000f1c603ab0b,0xd160000000000000,0x1200000000000003cab,0x356704690001490c00,0x0,0xa2a460000431c0000000,0x715f0000b4e643,0x0,0x622bb000000000000000,0x1b22b00,0x1a7cc000000000000,0x423600002008000,0x35000028da0000000000,0x11],#[0xb80006c3c00000001969,0x893a5f6d3100000000c2,0x12690000000000006,0x245e00000000000,0x3868000000,0x673cae2f5b300000,0x61a3000000000000000,0x3c17000104fc00,0x8a1800000000,0x0,0x0,0x1c3f0ae9000020d60,0x0,0x3e055f404a101e000000,0xdb44b5740000000140bc,0x30000000084098e7390b,0x1c19314,0x0,0xa0000000000000000000,0x6a3c0000000348,0x34f200000000000eb940,0x627592e0000,0x51aa000000,0x556c00032a5000000000,0x259c41820002e760000,0xb2e000000,0x0,0x91cac028000,0x84800000006148000000,0x3168c9052,0x292000000000000,0x0],#[0x6be000000000,0x0,0x5141d298000000,0x1202c000000000000,0x40180000000,0x0,0x908c0000000000095a00,0xb28ff000000000000000,0xb0c00000000001534dc3,0x4490d,0x34f68000,0x1c0a00000000000000,0x1c400000,0x346a0000,0x4cc1c0ee000000,0x106d0000000000000,0x5949000000034598000,0x74155380000000000000,0x2374000000050e600000,0x4b3400000000000,0x6c7ebfb1cc000047e800,0xa,0x1531c0000000,0x6044000000,0x21e908060,0x4d23,0x27000000000000000000,0xfc7a000000000000000c,0x448bf19720d28e88000,0x9b7cbed0bb0000000000,0x1a69c00000000000a,0x0],#[0x4d115100000000000000,0x1c6f2ce400016,0x318fb4f000000000000,0x0,0x426ea0e20,0xf8000642e00000000000,0x17000000000000000343,0x7a340000b,0xb0000b14e00000000000,0x84280001c4,0xf4200,0x100000001f38bc700000,0xaf2ad200000000ea6205,0x46f000000000001c,0x0,0xaf40000000128ad0b400,0x48e800074a914c3a,0xba0c4427600000003a76,0xac956a00004ad6f9c240,0xc010000000002cc00004,0x0,0x0,0x1a0c853ffd9e828e0,0x1aa340000000,0x0,0x0,0x150e8000,0x986a52000,0x0,0x80000000000000000000,0x200,0x4628000000000000],#[0x329e00000000000,0x1067400,0x738a00028b7000000000,0x95b000000000000000,0x0,0xa1180000000526300000,0x142e0000,0x1ef66dc095db6095bc00,0x394e7480003ec500016,0x153e000000000000000,0x0,0xf0f35634000000000000,0x6994b000020640000000,0x78c000413500009493d2,0xe1da0000000000061426,0x0,0x7c9c9972b500018a4400,0x4e680000001e,0x34fdc835,0x0,0xa84464ac000000000000,0x1a52732000006998000,0x43482de1ac0001a8c400,0x1364eadd831b282aa9a6,0x2a66000000000000000,0x41bc00,0xf07c0000000000000000,0x0,0x0,0xe338000000000000,0x7a60000000016838000,0x22080000000000],#[0x0,0x58000000000000000000,0x24df000000008e,0x30a40002e32000000000,0x5a0100000001c1e8000,0x12c000,0x0,0x1881000183140000000,0x388000496c8408000000,0x51543b986,0x70000000000000000000,0x245032f2e48347,0x0,0x310f0000,0xe49000101e000,0x1ea7c000000000000,0x208e,0xe43000,0x92c000000000000,0x8680000000,0x5aa08800000000000000,0x10aa40000000e2e3c,0x0,0x0,0xa11400019018000e3860,0x502d1dee51,0xc8de000000,0xf3f9a35e4d31ab900000,0x0,0x243480000001b8a400,0x0,0x1aa540e80000000],#[0x68b400,0x0,0x28720000000091c0000,0x884b134000000,0xf5e5200,0x71d2d9085580000,0x0,0x2068000000000,0x910600000000000,0x1e82c00,0x0,0x1cc30000,0x0,0xc5b800000000,0x29d948ce8b100000000,0xc4e0000000,0xa1780,0x83436fa1bd0500000000,0xe3,0xd4440,0xd13f750400039f9,0x33400000000000000000,0x14,0x0,0x9d088400000000000000,0x34d6804cf9034,0x0,0x604000203c0001649800,0x352080000001e,0x0,0x69380000000000,0x0],#[0x19153e5b0000,0x685740f02b0000000000,0x1928e1e50001e,0xe3ac0000000,0x0,0xe1b20,0x2c5b22e00034f00000,0x1e7a000,0x0,0x42a000000000000,0x0,0x22720000000000000000,0xbc0c0000c5c00b9,0x9a4c00,0x0,0x10b22b2849540000000,0x0,0x3e0d41d800000,0x48fb9b6,0x58400048200000000000,0x302b18bd60c3a,0x20138000,0x3ee580000000e2e800,0x72e60000000000000000,0xa5600000000,0x603400,0x92120000000000000000,0x27680004496,0x0,0xb0380000000000000000,0x48f4e20e00000002dab,0x745167f800],#[0x70040000000000000000,0x2c81d62c,0x1924000000,0x0,0x0,0x43362d80000001717400,0x9,0x30c30000000109e0000,0x321b0001814000,0xbc7800000000000d55a0,0x0,0xeee1800002536000000,0x94932,0x122e,0x0,0x0,0xeb2200000000000,0x0,0xfbf3207800020f911920,0xd0000000000000007d8e,0x55c967ee0f93cc0001e1,0x782aa2e50,0x331800000000000,0x0,0x0,0x90000000001d051043,0xae800000000000000000,0x935c00000000000325de,0x28d52a4a,0x51c8a23a000000,0x0,0xd0000000000000005104],#[0x2be52dfd49000000010a,0x1a,0x40000000008c00000000,0x281,0x0,0x0,0x0,0x106ec6d125960,0x0,0xc2c00000000000000,0x14bdf19b00000,0x0,0x6819152d9f32bc444800,0x0,0x27c40000000,0x1c000000000000000000,0xd8400000000000018798,0x0,0x2240002a210000000000,0x127a000213dd0b4449cc,0x143580000000,0x0,0x274000000048b531940,0xb0000000000000000000,0x50dcb30800,0x0,0x0,0xb14a000000,0x0,0x49b5641e00000000000,0x6cbb0000c75800,0x191c800000000],#[0x9d937f0ea00000000000,0xa9b308,0x0,0x0,0x0,0xa35e0,0x0,0x1447800,0x62ba0000000000000000,0xf000071520002c8c7a29,0x313,0x147fc000108825120,0x63d800000000000,0x0,0x1c00c000000000000,0x3840,0x6dd64342bf15a3d76800,0x1a528000000000008,0xc8000000000000000000,0x997b09a00000d,0x0,0x0,0x3bc00000000000000000,0x6c940001f,0x0,0x0,0x1c696088800000000,0x217e000000000000000,0x455400,0x4ac40004a7a52320,0x300000000b1f40001c8f,0x212c80000000000296],#[0x251c8896138800018580,0x343b,0xa780006a6f0000000000,0x422d459492c310f00012,0x2c7b8000,0x0,0x62ea0000000000053300,0x5aac,0x0,0x49ca0000000042b00000,0x0,0x181a000,0xe6f8000000000000,0x3982291200000000000,0x1e78400,0x0,0x10c6000000000000000,0xb3a9c25000,0x240e800000000,0x0,0x2b000000000000000000,0x0,0x0,0x490000000022f8000000,0x1c,0xa06,0x3d7962a3217800,0x64d20000000092df5260,0x244069f0,0xd4ba000000,0x0,0x30000012e00006090000],#[0x83,0x2894000000000,0x86ec00064ad,0x0,0x0,0x19b1ea228000,0x22e0a100000000000000,0x16,0x2540000000000000000,0x20ea8000705a000000,0x1d014000000000000,0x0,0x13c00000000000000000,0x116000071c82,0x31a8,0x1804c380000000000000,0x428d6700101000000012,0x0,0x0,0x18b3123200000,0x105380000000,0xe1be000000,0x0,0x0,0x3a8e80000000000000,0x65485a780,0x0,0x0,0x3d35e0cfc5340,0x0,0x9d400000000000f39800,0xc],#[0x855e00000000000,0x18d30000000000,0x1488c000000000000,0xa00000001ea480000000,0x115,0xb31a0000000000022420,0x161b18d80000,0x671c7440e50000000000,0x4,0x0,0x3c000000000000000000,0x5ae88500003024c,0x0,0x4b71e64c00,0xc228000c4220,0x0,0x8f792299150000000000,0x594d00006,0x0,0x0,0x0,0x0,0x3cfb0000000000,0x141f8000000000000,0x0,0x36000000000001aa0000,0x14a138ccf8bf00004,0x1c7880000000,0x7901f5a542ac00,0x1823c0006930f2a60,0xf46c82188480000,0x143100001160000000],#[0x1895c000000083fa0,0x1838448e00000000000,0x0,0x53ea110a8b8000000000,0x12270001e8272f0d8c2,0x4f756680000000000000,0x5,0x220d000000000000000,0x0,0x0,0x7049000000000000000,0x3a86000000,0x0,0xa3b781040000000,0x24640702a60000000000,0x70000000000000045955,0x1713b43e8000,0x0,0x43d60,0x1c62c000553f,0x68550000000000,0x94380002cc2800000000,0xd10000,0x20f20000000000,0x0,0x3115203be000046e0000,0xf60888,0x0,0x0,0x59000000000000000000,0x14d0000125b800000000,0x0],#[0x0,0x0,0x0,0x9dc00000000000000000,0xd33c0001b1d8000b1f4a,0x15638000,0x1d328000952c000000,0xb47ca194000000000000,0x63ae00000000000,0x1e786cc90000000000,0x558600000003887514c0,0x7022b9246c0603038000,0x10800000009d29e04e8f,0xc058000000028aa00012,0x18f0d12c0000000,0xa8594a80007466000000,0xb25e0000000000000010,0x75ba0000c3000000000,0x3aa5098d4b0000000000,0x493d03e5,0x7250,0xa0c0000000c1de000000,0x55542084000000002c7a,0x29e4000000000ab0000,0x0,0x65468138000000000000,0x49c09ada0e6118ee0000,0x355588510000000256,0xc5adaacc00055ac00000,0x0,0x93000000000000000000,0x937e00030129a8b0001c],#[0x48000e502000000069c7,0x20cafa26000000030c,0x0,0x3a927000000000000000,0x17400000000000c6014f,0xc04c000000000000253c,0x449c00000002c570000,0x91d400,0x0,0x18cc,0x0,0x9364000000000000,0xa3f5ea8e06d,0x89369b4000000,0x20720002cca382300000,0x8b8ad400200000007264,0x7d8000100a0001778b86,0xb3d48,0x20000000000000000000,0x9970000341,0xc49e0003446800000000,0xd0000506600034588000,0x1cfa000090b40001d2,0xc419c4388d9f84b31fc0,0xf0000000000018d58000,0x3c4,0x2921000000000,0x1000070a800000000000,0x1205553,0x0,0xf0000000000000000000,0x28e],#[0x1214d2ce99c600000,0x24500000,0x10338000000109c800,0x0,0x11c3b6040000000,0xc00000000c00e000000,0xbadd8,0x0,0xb392000000,0x82900000,0x79910000f43c0000000,0x0,0xf0080000000411a00000,0x6655000000000c70000,0x0,0x8a3c2ee0,0x46e00000000,0x3a578000743e000000,0x8bb281100000,0x800000004b540000000,0x114c961,0x1500,0x400000001574cd460000,0x2a370000000282,0x8a64000000000000,0x12c1000000000000000,0x392a0000000000,0x21350000d0620,0x1000061d800000000000,0x1a5be8b,0x0,0xd55c0002ed68000],#[0x2473e9d30000000000,0x0,0x528a000000000000000,0x0,0x3e66887300000,0xbc19a00000000000006a,0x18cf80000000000114,0x1b686133800000000,0x148fc0000000,0xa49400,0xa2665883c4c000000000,0xcf974000000000002a40,0x2f800000004570000110,0x0,0xb00003bb800000000000,0x6c00029f790f4000345,0x11658000000000016,0x74b9000000000000000,0x0,0x1a54f50e0,0x0,0x741c000000,0x0,0x65380000000427d,0x3c7d80000000000000,0x0,0x9800000000001cae0000,0x9f000046ba0000000193,0x319800000000001c,0x98000f0880003d640000,0x89b00000000000376,0x26a4000303700000],#[0x0,0x15c400,0x1550000000000,0x826200030c18000,0x79596012a26c00,0x0,0x0,0x0,0x0,0xa4700000000,0x16800000000000000000,0x3d620001f]]
set_option maxRecDepth 16000 in
def g251D9 := limbs80 #[#[0xee96258110e4d6554d62,0xfa94250120f555354510,0xcef7658920f695254120,0xee96258140f395454140,0xced7658940eb96458140,0xee962581509ef825d540,0xe6d6558950e796558150,0xeeb8058960ced7658950,0xece5358960ecd5358960,0xcef7558960cef7458960,0xf555354521e5d6554d60,0xe6d6558951e756558551,0xe5d6554d629dd85dcd61,0xe6f7559562aef8059562,0xff14154110ff12154110,0xf795254110ff16154110,0xfea6254110fe96254110,0xdfb7254110df97254110,0xdf97454110f795454110,0xf796554110dfb7454110,0xdfb7654110df97654110,0xbfb8654110bf98654110,0xff14158110ff12158110,0xef96258110ff15158110,0xdf97458110ef96458110,0xef96558110dfb7458110,0xbfb8558110dfb7558110,0xfe56248510fe55248510,0xdf57448510fd55348510,0xbf58448510df77448510,0xdf77548510df57548510,0xbf58648510bf58548510],#[0xfe66250510fe56250510,0xfd55350510df77250510,0xdf57550510fd65350510,0xdf57650510df77550510,0xfe56254510df77650510,0xdf57254510fe66254510,0xbf78254510df77254510,0xdf77454510df57454510,0xf756554510bf78454510,0xdf77654510df57654510,0xbf78654510bf58654510,0xdf77458510df57458510,0xdf77558510ef56558510,0x9fd8750910bfb8050910,0xded7258910ded7254910,0x9fd8758910def7258910,0xeed6458910fe58158910,0xdef7458910ded7458910,0xdef7558910eed6558910,0xdee8758910ded8758910,0xdef7498910ded7498910,0xddd535c910def7598910,0x9ff855c9109ff845c910,0xddd53dc9109ff865c910,0x9fd85dc9109fd84dc910,0xddd7454d109fd86dc910,0xddd7494d10ddf7454d10,0x9fd8759110ddf7494d10,0x9ff855d1109ff825d110,0x9fd82dd1109ff865d110,0x9fd86dd1109fd85dd110,0x9ff8759510cfd7659510],#[0x9ff845d5109ff825d510,0x9fd84dd5109fd82dd510,0x9ff825d9109fd86dd510,0x9ff855d9109ff845d910,0x9fd84dd9109fd82dd910,0xfe96250120fe95250120,0xfda5350120fd95350120,0xfb96450120fb95450120,0xdfb7550120df97550120,0xbfb8550120bf98550120,0xdfb7650120df97650120,0xfe94254120dfb7154120,0xf795454120fe96254120,0xdfb7454120df97454120,0xf796554120bfb8454120,0xdfb7654120df97654120,0xbdf8358520f5d5354520,0xded62dc520ded52dc520,0x9fd84dc520ddd53dc520,0x9fd86dc5209fd85dc520,0xfce5350920fcd5350920,0xdef7550920ded7550920,0xdef7650920ded7650920,0xded7454920f6d5454920,0xded7654920def7454920,0xbed8654920def7654920,0xfce5358920fcd5358920,0xded7458920eed6458920,0xbef8458920def7458920,0xded7558920eed6558920,0xbef8558920def7558920,0xddf7454d20ddd7454d20],#[0xddd7654d20f5d6554d20,0xddd7494d20ddf7654d20,0xddd7694d20ddf7494d20,0xd7d7555120ddf7694d20,0xcfd76591209fd8755120,0x9ff815d1209fd8759120,0x9ff865d1209ff855d120,0x9fd85dd1209fd81dd120,0xcfd76595209fd86dd120,0x9ff815d5209fd8759520,0x9ff865d5209ff845d520,0x9fd84dd5209fd81dd520,0x9ff815d9209fd86dd520,0x9ff855d9209ff845d920,0x9fd84dd9209fd81dd920,0x9fd85dc9309fd85dd920,0x9fd82dd5309fd85dd130,0xdfb71541409fd84dd530,0xfe96254140f795254140,0xdfb7254140fea6254140,0xfb96454140bfb8254140,0xdf97654140f796554140,0xbf98654140dfb7654140,0xdfb7158140bfb8654140,0xbfb8258140ef96258140,0xfda5358140fd95358140,0xdf97558140ef96558140,0xbfb8558140dfb7558140,0xf5d5354540def7248540,0xded62dc540bdf8358540,0x9fd82dc540dee62dc540,0xdde53dc540ddd53dc540],#[0x9fd86dc5409fd85dc540,0xdef7258940d7d7554940,0xfe98058940cfd7658940,0xfce5358940fcd5358940,0xded7558940eed6558940,0xeed7658940def7558940,0xdee8758940ded8758940,0xfce5398940fcd5398940,0xdef7598940ded7598940,0xddd53dc9409fd81dc940,0x9fd85dc940dde53dc940,0xf5d6554d409fd86dc940,0xddf7654d40ddd7654d40,0xddf7694d40ddd7694d40,0xcfd7659540d7d7559540,0x9ff87595409fd8759540,0x9ff815d540bef825d540,0xdef825d540dec825d540,0x9ff865d5409ff825d540,0x9fd82dd5409fd81dd540,0x9ff815d9409fd86dd540,0x9ff855d9409ff825d940,0x9fd82dd9409fd81dd940,0xdfb71581509fd85dd940,0xf795258150bfb8158150,0xbfb8258150ef96258150,0xef96458150f795458150,0xbfb8458150dfb7458150,0xbdf8358550f6d5248550,0xded62dc550e7d6558550,0x9fd82dc550dee62dc550,0xd7d65dc5509fd84dc550],#[0xf6d62549509fd86dc550,0xb7d8654950d7f7454950,0xe7d6558950def7258950,0xfe98058950cfd7658950,0xeed6458950f6d5458950,0xf6d8558950def7458950,0xded8758950eed7658950,0xf6d5498950dee8758950,0x9fd81dc950def7498950,0x9fd84dc950d7d54dc950,0xd7d76551509fd86dc950,0xe7d6559150d7f7655150,0xbef825d150cfd7659150,0x9fd82dd1509fd81dd150,0x9fd86dd150d7d65dd150,0xb7f8259550f7b8059550,0xbfb805d950b7f8459550,0x9ff815d950dfb805d950,0x9ff845d9509ff825d950,0x9fd84dd9509fd82dd950,0xeed6254560eed6248560,0xeed625c560e7d6554560,0x9fd84dc5609fd82dc560,0x9fd85dc560cfd65dc560,0xafd8654960eed6254960,0xede5358960edd5358960,0xaff8458960cff7458960,0xaff8558960cff7558960,0xeef8158960eed8158960,0xeed8458960eed7458960,0xeed7558960eef8458960,0xeef8558960eed8558960],#[0xddd53dc9609fd81dc960,0xcfd64dc960dde53dc960,0xcfd65dc9609fd84dc960,0xedd6454d609fd85dc960,0xedd6494d60ddf7454d60,0xcff7559160ddf7494d60,0x9fd82dd1609fd81dd160,0x9fd85dd160cfd65dd160,0xaff8259560efb8059560,0xbfb805d560aff8459560,0x9fd82dd5609fd81dd560,0xbf780545219fd84dd560,0xf756554521fe56254521,0xded7654921df57654521,0xeed6558921bed8654921,0xcfd7659521bef8558921,0x9ff805d9219ff805d521,0xdf561dc1519ff855d921,0xdee62dc151ded62dc151,0x9fd84dc1519fd82dc151,0x9fd86dc151d7d65dc151,0xe7d6558951def7258951,0xdee8758951fe58158951,0x9fd86dc9519fd80dc951,0x9ff825d9519ff805d951,0xef78159561ddf7354961,0xbef8158952bef8058952,0x9ff815d9529ff805d952,0xddd53dc1629fd81dc162,0x9fd84dc162dde53dc162,0x9fd85dc162cfd65dc162,0xcfd65dc5629fd80dc562],#[0xaff80595629fd85dc562,0x9fd81dd5629fd80dd562,0xfcd535c162bef815c162,0xded745c162fce535c162,0xbef845c162def745c162,0xded755c162eed655c162,0xbef855c162def755c162,0xbed81dc162eef865c162,0xfce53dc162fcd53dc162,0xeed65dc162bed84dc162,0xbed85dc162ded75dc162,0xeed655c562bef805c562,0xdef755c562ded755c562,0xbed80dc562bef855c562,0xded75dc562eed65dc562,0xeed8059562bed85dc562,0xeed8159562eef8059562,0xbef805d562eef8159562,0xbed80dd562bef815d562,0x9fd82dc153bed81dd562,0x9fd80dc9539fd84dc153,0xbdd84dc153bdd82dc153,0xf5d8059553bdd80dc953,0xf5d8259553f5f8059553,0x9fd81dc165f5f8259553,0x9fd84dc1659fd82dc165,0x9fd82dc5659fd80dc565,0x9fd81dc9659fd80dc965,0xff96254110ff94254110,0xff96454110ff98254110,0xff98654110ff98454110,0xff95258110ff94258110],#[0xff95458110ff98258110,0xff98558110ff98458110,0xff55250510ff56448510,0xff54254510ff56250510,0xff56454510ff56254510,0xff55258510ff54258510,0xfed5250910ff55458510,0xfdd5350910fed6250910,0xdfd7550910fbd5450910,0xbfd8550910dff7550910,0xdfd7650910bff8550910,0xbfd8650910dff7650910,0xfed6254910bff8650910,0xdfd7454910f7d5454910,0xdfd7654910dff7454910,0xbfd8654910dff7654910,0xdfd7458910efd6458910,0xbff8458910dff7458910,0xdff7558910efd6558910,0xfed5458910bff8558910,0xfef8458910fed8458910,0xfef8558910fed8558910,0xdfd645c910fed5498910,0xdfd65dc910dfd64dc910,0xbff8255110ff58155110,0xf7d6555110fbd6455110,0xdff7655110dfd7655110,0xbff8655110bfd8655110,0xdfe8755110dfd8755110,0xbff8259110ff58159110,0xdff7559110efd6559110,0xdfd8759110bff8559110],#[0xbff825d110dfe8759110,0xdfd65dd110dff825d110,0xbff845d510bff825d510,0xff96150120ff95150120,0xff95350120ff98150120,0xff96550120ff96350120,0xff96154120ff98650120,0xff94354120ff98154120,0xff98354120ff96354120,0xff98654120ff96454120,0xfed4254520ff56154520,0xdfd7454520fed6254520,0xbff8454520dff7454520,0xdfd7654520f7d6554520,0xbfd8654520dff7654520,0xfed4258520bff8654520,0xdfd7458520fed5258520,0xefd6558520dff7458520,0xdff7558520dfd7558520,0xfed5350920dfd64dc520,0xfed6550920fed6350920,0xfed6354920fed4354920,0xdfd7550d20fed6454920,0xdff7454d20dfd7454d20,0xfdd6454d20bff8454d20,0xfdd6494d20fdf8454d20,0xdff7458d20dfd7458d20,0xdff7558d20dfd7558d20,0xf7d6555120fbd6455120,0xbff8159120bfd8655120,0xefd6559120fed8259120,0xdff7559120dfd7559120],#[0xdfd8759120bff8559120,0xdfd655d120dfe8759120,0xbff8159520dfd65dd120,0xbff8459520fed8259520,0xdfe8759520dfd8759520,0xdff815d920bff815d920,0xbff8255130f7d5454930,0xff93154140dfe8755130,0xff97154140ff96154140,0xff96354140ff98154140,0xff98354140ff97354140,0xff98654140ff97654140,0xff95158140ff92158140,0xff98158140ff97158140,0xff97258140ff95258140,0xff97558140ff98258140,0xdfd7648540ff98558140,0xdff754c540dfd754c540,0xff57154540ff56154540,0xfee6254540fed6254540,0xf7d6554540dff7254540,0xdff7654540dfd7654540,0xbff8654540bfd8654540,0xbff8754540bfd8754540,0xdff7258540ff57158540,0xdfd7558540efd6558540,0xbfd8758540dff7558540,0xfee625c540fed625c540,0xfdd535c540dfd725c540,0xdfd755c540fde535c540,0xdfd765c540bff855c540,0xdfd7654940bff865c540],#[0xfef8158940bff8158940,0xdfd53dc940dfd765c940,0xdfd65dc940dfd63dc940,0xfdd7654d40bff8754d40,0xfdd7694d40fdf8754d40,0xdff7558d40dfd7558d40,0xff98059540dfd755cd40,0xf7d7559540bff8159540,0xdfd8759540efd7659540,0xdfe8759540bfd8759540,0xdfd765d540bff8759540,0xdfd835d540dfd815d540,0xbff815d940dfd865d540,0xdfd815d940bff855d940,0xdfd825d940dff815d940,0xdfd855d940dff825d940,0xff92158150dff855d940,0xff98158150ff97158150,0xff98258150ff97258150,0xff98458150ff97458150,0xdfd7648550f7d6548550,0xdff744c550f7d544c550,0xf7d5258550ff57158550,0xf7d5458550dff7258550,0xbfd8758550dff7458550,0xfed625c550f7d525c550,0xdfd725c550fee625c550,0xdfd745c550f7d545c550,0xf7d655c550bff845c550,0xbff865c550dfd765c550,0xf7d6354950dfd64dc550,0xf7d6454950f7d7354950],#[0xbff8158950f7d7654950,0xdfd735c950fef8158950,0xdfd765c950f7d655c950,0xdfd64dc950dfd63dc950,0xdff7458d50f7d5458d50,0xdfd745cd50f7d545cd50,0xf7d7655150bff845cd50,0xbff8159150ff98059150,0xf7d8559150fbd7459150,0xdfd8759150efd7659150,0xdfe8759150bfd8759150,0xf7d655d150bff8759150,0xf7d8159550dfd765d150,0xf7d8259550f7f8159550,0xf7d8459550f7f8259550,0xffb805d950f7f8459550,0xbff845d950bff815d950,0xdff815d950dfd815d950,0xdff825d950dfd825d950,0xdff845d950dfd845d950,0xfed5248560ff55148560,0xdff7448560efd6448560,0xdff7548560efd6548560,0xff57154560bfd8748560,0xdff7254560efd6254560,0xefd6454560bff8254560,0xbff8454560dff7454560,0xefd625c560bff8754560,0xefd645c560dfd725c560,0xefd655c560dfd745c560,0xdfd52dc560dfd755c560,0xefd6454960fed7254960],#[0xbfd8754960dff7454960,0xefd7558960efd7458960,0xfdd535c960bff815c960,0xefd645c960fde535c960,0xbff845c960dfd745c960,0xdfd755c960efd655c960,0xfdd7454d60bff855c960,0xefd7559160fdd7494d60,0xbff825d160bff815d160,0xdfd755d160efd655d160,0xefd8159560bff855d160,0xefd8259560eff8159560,0xefd8459560eff8259560,0xffb805d560eff8459560,0xbff825d560bff815d560,0xdfd62dc151bff845d560,0xfed8058951bff8058951,0xf7d8059551fef8058951,0xefd8059561f7d8259551,0xdff815d952efd8259561,0xefd8059562bff815c162,0xefd8159562eff8059562,0xbff815d562eff8159562,0xfef815d562fef815c162,0xdff715c165dfd715c165,0xdff725c165dfd725c165,0xdfd745c165bff825c165,0xbff845c165dff745c165,0xbfd82dc165dfd72dc165,0xdfd82dc165bfd84dc165,0xdfd725c565dfd84dc165,0xdfd72dc565bfd80dc565],#[0xdfd80dc565bfd82dc565,0xbff805c965dfd82dc565,0xffd6550910bfd80dc965,0xffd6454910ffd7650910,0xffd6454520ffd8259110,0xffd7458520ffd5458520,0xffd5458d20ffd7558520,0xffd8159520ffd7558d20,0xffd754c540fff8159520,0xffd5258540ffd7654540,0xffd7558540ffd7258540,0xffd6354940ffd655c540,0xffd8159540ffd7558d40,0xffd744c550fff8159540,0xffd7458550ffd7258550,0xffd635c950ffd645c550,0xffd7254560ffd7458d50,0xffd7550910ffd7454560,0xffd8559110ffd8655110,0xfff8459520ffd8459520,0xffd865c540ffd855c540,0xfff8759540ffd8759540,0xffd855d940ffd815d940,0xffd8759150ffd8159150,0xfff815d950ffd815d950,0xfff845d950ffd845d950,0xffd7548560ffd7448560,0xffd725c165fff815d560,0xfff825c165ffd825c165,0xffd845c165ffd745c165,0xb000700000fff845c165,0x6d002e4013a007c002],#[0x1bb00ca8058002600105,0x38027b01258086c03d60,0xc06540304016f00af405,0xf8c0766038801b380d2,0x46811b008aa043402048,0x5029c8143809c604b302,0x60102eb016c00aec055,0xd88069e0339819340c44,0x580ec20727038081b800,0x202c0fe807d303db81e,0x43f0218810a008340411,0xf6046d022e4114e08900,0xe096604a5024cc122408,0x142a09f904ec026b4130,0xac015140a690526828b0,0x602dac166c0b01056b02,0x60f82ff817a60bb205c,0xcce06568324418cc0c3b,0x960d2f068c0340419d40,0x41be40dcc06d3035b01a,0x3a201ce20e5a071f0387,0x7d83b901da40ec007520,0xe07ae03cd81e3e0f0d07,0xff207eb03ec01f1e0f6,0x12e1080082f840d02030,0x90229011180876843302,0x47b4239811a608c5045,0x93f04974248c12250902,0x14097c04b84258012950,0x2139d09c084d94269213,0x283e140809fb04f7c277,0x2ac291e14780a2e05114],#[0x9855202a3a15010a6d85,0xae0056b82b3815800ab,0x63d0b10858282bdc15d7,0x9216ad0b4b059fc2cb21,0xc2ec217360b8805b942d,0x60042fc017b50bc505dc,0x5d0625030e618480c110,0x20c928644c31da18d60c,0x19840cb6865583288193,0x4661a170cf1066dc3340,0xe835281a7d0d33069283,0x6d0c36581b150d7286a,0xdec86ef4372e1b800db2,0x740e29870dc384a1bff0,0xa1cfd0e6b872ec392a1c,0x3b581d860eb2875103a5,0xa343ce21e370f0387734,0x587ca83e081ee80f6107,0xffe07ef43f1a1f6c0fa,0xc9104f081e040c22031,0x82212a1084883dc41c02,0xc4380219510bf0859c42,0x898044742228110b087a,0x9b88c3045ae22ac11430,0xc11e008e5446de235311,0x2488122489064480423d,0xa4625071273093284952,0x744bf825d612cb895744,0x89ad44d0a26691329098,0x3c109d844e4e270b136d,0x63141e8a0484fe227b21,0x82923147c0a320513028],#[0x541c29de14d48a5d0528,0xaf4554c2a8a152d0a8bc,0x60ad2c56402afa156c8a,0x15ff8af64575c2b8815b,0xcb316468b19c58962c25,0xd82d5016928b3d459b22,0x45c262de316e10b65c5a,0xbc205da62e9e17410b93,0xed0be945ee02f5417920,0xe18368c13060382ffb17,0x314e18918c3a4617c308,0x40e31dc18db0c62c62e8,0x14653e327419298c88c6,0xccc0661e32fd19758cb,0x9f48cf0c6744337719ab,0xd41a548d1d068a634231,0x235301a8f0d43069ea34,0x6bdc35c31ace8d5dc6aa,0xac46d16365b1b1d0d83c,0x40dd886e82370c1b6e0d,0x1c128dfe86fa837b81bc,0x8cf1c598e25c70f6385f,0xa2393a1c918e43071d63,0x4736439911cbd0e5a072,0xe9ac74a83a1f1d018e77,0x920ebf875ba3aad1d438,0xf1dcf0ede076b83b4a1d,0x3c4d1e138f01877ca3bb,0x9943ca41e490f21478dc,0x807a883d321e888f3ac7,0xf7907b903da71ec08f5,0xf3d0f93c7c5c3e081efb],#[0x4c1f930fbec7daa3eaa1,0x63fb71fc60fde87ed03f,0x80ae4036200f8ffd07fa,0x378818e40a62045101e0,0x31060082b44125208490,0x21219086083ee41cc20d,0x2d9216110a8484f6425f,0x6435d219e10c6c85fe4,0x885e43ff21e790ea487,0x13f0899844b022451119,0xf1116c88afa4543228c1,0x235d91a048c98461722,0x475623a211c8c8e2246f,0x5a480c23eb91e748f0c,0xc09194489a243c9214c9,0x925e492a6492d2483923,0x51b9284493ea49d924d4,0xe6256292a6894f24a5d2,0xa4b5b259f92ca096184a,0x97c44bc625d512e2496d,0x21c98d64c4a260a92ff8,0xb1340499c04cc9265693,0x26f3937189b224d61269,0xebe2751139f09cb64e21,0xc4f65279a93c509db44,0x4a0004fda27df13e889f,0x42e4a130507228239408,0xaf144cca22450ec286a9,0x728f614740a354518928,0x52b42949949b4a484521,0x6bc5342298b94bd8a5aa,0x70a7e253c629d294dd4a],#[0x95398a95854812a2d950,0xad2155f8aace55372a88,0x492b1695830abd655cf2,0x656dc2b5615a68acde56,0xaec6574c2b9315c28ade,0x84aff657d02bd795e24,0x4962d0b0f458592c1e96,0x2cc316544b260590f2c7,0xa492d1916830b3b859b6,0xd25ac32d51169f0b4c05,0x8b7525b832da716c64b5,0x7188b88c5c1b2df596f2,0x9297424b9c65cc72e469,0xd2ee8976e8bb145d552e,0x5e8a2f37178d0bc085de,0xef45f4a2f8597b6cbd4c,0xa8c05660002fef97ee4b,0x984a8c1fe60bb3045981,0xf418730c342618530b4,0x14316f98a1cc4a4620e3,0x8638931b698d58c67e63,0xc88e642b320298f40c76,0x3d8c9a064b93244991b4,0xd19700cb206560329599,0x335d199d8cca0662f32f,0x77833a419c74cdf866db,0x76680633f799efccf326,0xd1c468bc343e9a170d0,0xa720d362697734a11a42,0x391a930d44c6a0f34f49,0xa358a1ab90d5726a8e35,0x6bd735d39adf0d6b66b3],#[0x9e86cc436401b118d82c,0x78db046d5c36a01b490d,0x9b838dbda6dd636dd1b6,0x7661bac0dd146e4b3717,0x8037aa9bcbcde126eed3,0x2702c38031bf94df6a6f,0xe20670d338591c230e0c,0x77ce386719338af1c4e0,0x51ca68e4d4723f390a1c,0x39b89cd40e64072eb396,0x4343a0c1cff0e7ca73ab,0x8074a43a419d188e88c7,0xeab075233a7e9d384e9,0xd880ebfe75de3ade9d62,0x5d9da40ece876583b1b9,0x33bac1dc8cedfa76e13b,0x77fd3bf09df14ef52778,0x20278c73c491e188f05a,0x24f350797d3cab9e4c4f,0x1e9d4f4a87a1f3cf51e7,0xdab1ec70f5ec7ac63d4b,0x2d3dfc1ef5cf74e7b863,0xc7c983e409f194f8a67c,0xfa987d2b3e851f390f97,0x7ecfba07daa3ec71f5a0,0x69fa4cfcc67e383f109f,0x3fcb9fd38fe467f023f6,0x6e4021a007500027fc7,0x76810b406da02c101148,0x9039c81a340c12057102,0xa1d04c28245410aa07a,0x98a0c5505e882d341542],#[0xa41e220e6506f0834d41,0x849b423821101082a83e,0xabc853842892139d0978,0x350bce85cb42d2a15fd0,0xa19910cc2865e431c218,0x339a19c10cda866a4333,0x82433fa19f10cf286764,0x2868e4345a1a210d0a86,0xd3a869a434ba1a510d2,0xf8b0d5286a64351a1a81,0xc2f080f978110bc27000,0x29042c1400100590883b,0xdc27050883507e000f8e,0x7a2f0d002284207a1d0,0x191a1b024370c0922806,0xc3707007021e9010703c,0x9c191a0e87a400bc1209,0x3c191a0a92c1041c0e0,0xf021e941103bc2f05007,0x8440ed04016098011bc1,0x4821c3707c0e098050a3,0xc1041c083bc191b8287a,0x900705c0f064683248a4,0x3c191b8007a48a40ef0,0xe018287a48a54104082f,0xe840303b4100446f07c0,0xc287a0f8dc0f070683a1,0x58030a1e842343b41600,0x906f07c087a0e8f0ed0,0x41bc1f02c287a0e8e0bb,0x2a3a42f09c16000f8c06,0x2903e341e0d07b0483e],#[0x9c060229101c709c170,0x30b80e0c484082d041c7,0xe83e380e1584dc2705c0,0x1c07a40a9c270042e041,0xa100c0941bc1f02c050a,0x101c07a210bc0f070687,0xb09007068407a1c0cc1a,0x4b0700433c270414a3e3,0xc305308e11c187b80918,0x500603847061e8704033,0x384706c107e1c1102b0,0x206028641c06c2c0b006,0x1e96c1611c18640886c3,0xc170d8405308f06c2602,0x2b09c187a1c0e0c823,0x10c27074287a08910061,0xf09c10328f870370dc16,0x2c010cf09c10528f9008,0xc270408e11c187038540,0x3c270580f07840704433,0x419611c18321c0e0e83,0xc0d0ec01c22281c0b80f,0xf8583f050043ac203e1,0xa1ea285c01c27050eb0a,0x5c2f09000400f8590883,0x440ef0bc1422c203e50a,0x704c243e1c0c29042161,0x3443c2f04c20822c3b00,0x208829709c103a0f870,0x7c27041c0822709c107,0x88121783e190b0405e1c,0x160530a0b4103e1e860],#[0x28148808c281e86c260,0x1907034121607a1e0016,0x646058178a08c1304706,0xcc30000a052178b0410,0xa0702508c16000f85e1c,0x7c2d800281b0b026000,0x42386c195098003e148c,0x58442d08d080a600c28,0xc0c1904f047078030b42,0x10852286504707420221,0xd420220f870204f80508,0x8582b058050a0f87a160,0x1e001606c3600c150a0f,0xd411c18221b0f0400a8,0xf08c11c1834178ec101f,0x11c1b098050a1610c101,0x50b047061e822505e154,0x187a0d150d01fc3704c2,0x342207f0d80704c2411c,0xe0f8fc27050470780070,0x3e160c15709c16014281,0xe000783e4709c150a088,0xf834160c11f0841f0542,0xc260014c3e2f09c16000,0x3c2d07c130808c3e4506,0x941f058003e1c1017c4,0x709c102214c3e28a408f,0x148a80223c370a4bc283,0xb8004e1c094260016428,0x8550f898004f0f854200,0x30078004f0f8522e0013,0xa0f96888128005e10864],#[0x2105058885851600c207,0x4c26010f85e1c0e2904,0x841413088887b0f8e105,0x20a416001e83e1c1110,0x41611c187a8887030a41,0x550f8881e0013c3e150b,0xf8ac26010a0702600138,0x412221c0a82b090a2230,0x5c1b078023e1b0784707,0x70701e11c186c17090a0,0x10a06c26008f86c1c281,0x58470780e001b0e0360,0x530f8d0a06c2086035,0x42a221ec3e3054813098,0xa88e010a50b108ec2205,0x8ec242942a23108a8b22,0xa0a08006015098043e14,0x426001c1003509800548,0x8f87030200160384707,0x29420541708080054260,0xe11c3704c28a21e82252,0x870bc1508208c1dd0801,0xc2207c16000f87042420,0x1c1e014350a07921500b,0x5800a4138a08709c161,0xd0b80704c207a290f42b,0x1c0f847074284e170b80,0x2208c08611c1f04c2022,0x4e1543e200fc2007c105,0x4420870bc1308208d800,0xf8803f0910f04148823,0x4c243e08870360013855],#[0x86c404fc32281f880800,0xe8c0ab1bc1c09c0b0c17,0x1b074207f023078133e1,0x40907fc36281e8b02228,0x1bc1f03811442bb0c1e9,0x84fc30098a07e282a093,0x8a07a2f0c027021b0742,0xc17f02c2874287fc3605,0x1bc1809c085ec306c3f0,0x18701f8602074c307e23,0xc1906c3855c32281f888,0x7f8a07a20701031bc1b0,0xb0802f0c156281f8bc30,0xc3628c20642f0d8a0661,0x20cb1bc1c24c307a4867,0x1bc1864c306c3e041c70,0x52c6f06c307e285202b,0x905467135c26058013e4,0xc2f098150243e0143118,0x6c0913e1c0a1c07e1625,0x34281f860d93e1f87018,0x10a070200e1c4281f880,0x8c18550233e1f8a0260,0x30090a07e2c080a0541d,0x43f0c02702150742821c,0x7e231bc1f02c36014205,0xf0c13c281f8900074c30,0x604e280bc30210a07e2,0x2c36010604e470d0a025,0x1c0b0c1f8e14b1bc1f0,0xb0c06600139014b1bc1c,0x26004f86c1870c6f07c0],#[0x646e001b11436000a06c,0x14305440ae09145c0f0,0x241b0c1651bc1f02c26,0xe001006c351bc1f0343,0xc0f0646e001b0f46f07c,0x7c0e0143018139009071,0x7c0d0c0906c305946f0,0x51bc1f03800401b0f46f,0x1b0802d061553e1f8a1c,0x5c26018113e3d074fa24,0x87e16004f86c185b8905,0x894281b070a0541d064f,0xd42874230d804281b08,0xf880204fc36281f8b0a3,0xc191b8006c470c086281,0x9436001514026042b945,0x28281f46f0603807c0d0,0x70215074200f8005814a,0x8a08078021d30c1f8bc3,0xfc362813866260016052,0x1007b0dc1f02c68241b0,0x8538100bc0f0646e001b,0x251bc1f038050d4284e4,0xe1988038061607e201e0,0x1bc1f02c307e370d8a04,0xd08c470616054170a07b,0xc0b1a0906c3f0dc08541,0x9816001493e281ec3707,0x1f46f07c0d0d8006c380,0x81f46f07c0d0d8006c38,0x8754307e28524f85c1,0xc07d1bc1f034307e301e],#[0x8503e078041106854128,0x684e28200130b0402706,0x4027068563e010450b0,0x2c47060a870482001309,0x18ca07a205481f0417c3,0x70c6c09c1b0c1e8dc31,0x190e1c31b02706c307e3,0x2178c14d0bc3304ca608,0xac307a5e08c170cca03,0x321c02bc131bc1f02915,0x71c0b1bc1e08c307a48,0x27062630d4287a5833c1,0xc307a28529103bc0b1b8,0xa25b0d8207a5052c6f06,0xc1e8e0e870c6f07c0d0,0x93e1c0a1c31a02707c0b,0x191ac103a1e8f8270417,0xc1f021783a1b0d82097c,0xdc143b8230a1e93e351b,0x87a4f050ee08c287a508,0x700ef05c0f0646e08c2,0x17038270746b0b4307a6,0x4330a0a950e8320a859c,0xa4859c0c3bc1d1bc105f,0x146f07c17038230a1e83,0x7a4f8f8260015128207,0x3e01431067135c160980,0x17870262bc2f05825024,0x601c0f801281c090193e,0x370130b0a93e3128150,0x178703928c2c2a508815,0xe4f870200e01f0582600],#[0x54470c465281e880105,0xe901651bc1f038260143,0x40941103a46f07c0d041,0x1051bc1a09c0d0c1786c,0x8f801421e878013e1e86,0xe8e82e001c703c191a1e,0x178e1604146f07c0d0c1,0xa1e901651bc1f02c2d0c,0x545089800440ef03c191,0x1bc1a0e81f0382601430,0xf07c0d0d826001510165,0x2e098030b4113e285946,0x34307e3e098050cc2928,0x4c2a2a40580151bc1f0,0x524a0a1651bc1f03435,0x1d04cfc2a150f8260016,0x44c0c1542a4a0814836c,0xe03b0b4170d826014a05,0x1c1f02c6f0a22504601,0x7a4f8c0809407b0d826,0x150a1e93e305bc160980,0x1520542a2a4f8a9123bc,0x422a448ef054287a508c,0xd1b4307a58548150a8a9,0x8380c859c170382601c1,0xe018211bc18994287a5,0xc1f034687a60440e853c,0x2500407e098050d42f05,0xd820058051bc187a1c0e,0x8585601c3707c0d0a178,0x311c180e01f058260142,0xc0878284bc33281e0808],#[0x980329428204805c3707,0x2c307a381e03f0cc160,0x60142858481e0131bc1f,0x2874282001302c470782,0xc0b0c2602a5f0dc08214,0xe3088078054285ec6f07,0x151208005826001493,0x9807b0546f07c0d0d826,0x60946f07c0898c2d0c1e,0x26001493e30880780580,0xc0e098050c1510080058,0xbc1f034307a381f46f07,0x6c430343032501e0151,0xb020e9283f09c10650ef,0x61215709c1432c470782,0xc899c0c3b46f074307a8,0x82899c191ac103a1e900,0x214d1bc18640e86c30a5,0x5c0d1b0ef06c250c1e9,0x703c191ac260a1e940cf,0x950cc203250a45103bc1,0xe92167030ef0746f041,0x14f05c0d1ac27078287a,0xc40194470619112178c,0x938cf09c160b4090f805,0x65418708cf09c16004f,0x1f8903c0740b0c1e8a29,0x1c1d02138662c0ec3128,0xe1f80d447074087a351,0x61103f0419511c1e001c,0x300944707c1601828641,0x2178ac6819c1b0c1905e],#[0x61930c178fc34194a03,0xe014360a139141000c6f,0x6f074107a385946f07c0,0xc1f034107a38a5807024,0xbc1d0c1906c38940e91b,0x146f074307a28701051,0x8a451045c0f064687a3a,0x385946f07c0b09430643,0xa28188051bc1d0c1905e,0x18284e483bc0f064687,0x84e40588251bc1f03436,0xf8a1651bc1f034360182,0x435048c908051bc1d0c1,0xb41058405946f07c0b09,0x1b0c02302c47078060,0x6018284e4b094170d4a6,0x2d04581e03b094170d4a,0x7f08c6f07c0896c36018,0xc0e0025b0d4207a50200,0x7c0b0c1e8b02a3ac6f07,0x3c191b426001e94c6f0,0x8974207a50a482945c17,0x90a5103bc0f0646e0182,0x82d081613c3703c1d081,0x8198a08004c0b11c1e01,0x654230c0c95c3020ca50,0x832505811702c6f07c10,0x1e01064c6f07c0b0c25,0x3709c151bc18321c0d42,0x1e921c51bc18654305e,0xdc170346b09c1e014307,0x870351bc1f04190321c0],#[0x360a07920ed1bc183225,0x139008709c1311c1e014,0xa581f46f07c0d0d8060a,0x546f07c0e01828974307,0x38060b4304e430807f0,0xf07c0d0c1e8e07d1bc1f,0x420c1792819080780546,0x1023ac150b8003e1e8a4,0x8ef09c107140e00290e,0xa41181ac1043c2f08209,0x243e4e0d8004e1512828,0x344207821c2b09c16002,0xc149015709c16000f870,0x5e3821c2705447078060,0x5e38988ef03c1a1a460,0xf87a18988ef03c1a1a46,0x40e87a340c4a07a1d040,0x3bc1c1a1e8f06f07c0d0,0xf034103a1e8cc250425c,0x2f03417070687a441bc1,0x44a001783e190c2643ac,0x24143b8007a0f8403b06,0x941703c1c1a1e83a584,0xc1ac2064490425044223,0x7a343a0bd05c0a01c1,0x687a0e950ef03c1c1a1,0xe40a54110425b0bc0f07,0xd0e919c0a01c1c1ac285,0x882243bc0f07068401e8,0x1b078023e1b060392814,0xe917068683a1b0d80128,0x1f86f07c0e0d8006c38a],#[0x8520670286f060e86c38,0x401f86f07c0e0d8006c3,0x9123ac270542e001e83e,0x4243088150a8e87b0f8c,0x8c9123ac270542e001e8,0xe83a4b088150a1ec428e,0x3c4542705c0f0706b0a1,0x44020018054260014a3e,0x207e1bc1f03836014205,0x286f07c1508c287a0e9,0xf07c0b0a2587a0e9414f,0x683a26070301f4200586,0xef0706d0a178fc27070,0x706b09428701e93c0871,0x1a0e8961c0b80705c0f0,0xf0801f0407d0a208fc1e,0x6f07c0e0d8050a139003,0xc1f03428981e83a581f8,0x20d07a2888c201e0161b,0x340486c0f8642c11c1c1,0xf8642c13c1c101e87028,0x484f06046280a1b01e0,0x843b0c1381904846330c,0x86c1006424121b03e190,0x17868203e1b228190980,0x3e190817c3e190784706,0x709c15000d23e30061b4,0x150184706c307b0d1019,0x8470740304c34343840c,0x345611c1d00138682c09,0x740610c2705c309e1e8,0x922f09c150024881f0],#[0x4304f828463821c27054,0x1c07a294124a0fc1e03,0x6c0f864304082f0980f0,0x60213e0a118e8d012828,0x470780e0a178e83f0743,0x248a0105e2486035058,0x213e0a118e08709c130,0x20f83603460c03f07436,0x2705c005a0f8523f09c0,0x46f07c08410605e3607c,0x5e3b11c185ec0841060d,0x81e301f46f07c0d0d828,0x4a3e1788c47074360a17,0xf832281e868f87a10061,0x8c07e1bc1f02c2040190,0x5e3d01c0841c1a1a1e,0x1ec3e301f86f07c0b0a1,0xa1e83e1c06078850a300,0x701e8d447078307a148,0xb001006c3c1bc1f0381,0xc086d83064301f86f07c,0x78106d4023e1c0a03806,0x50f402421b074023e1b0,0x1b0d86f07c0e0cc25001,0x18306c461bc1f0340040,0x1b121602586f07c0d0,0x901c0258110bc0f0686d,0x87186f07c0e0d4030a13,0x407186f07c0d001006c3,0x1602586f07c0d018306c,0xa10703c1a1a13824150e,0x23e1e860490617a3e190],#[0xc20401911012421e8701,0xa1007a28580be1bc1f02,0x7c0b0a1005e3703c1a1,0x61bc1f02c2840179186f,0x190c0485f0f864205806,0xec284635070490a1b03e,0xa1b43e1906c3e0d4084,0x7b0f8c049061b43e19,0x1007a0f8702442213001,0x486503c1d10c285e1010,0x7a5041447061e870293,0x3ac060542f03c1c1a1c,0x605c1c1ac007a1c0e81,0xc1e05c203fc0070248e1,0x2910a84f09c003e168e,0x580661bc1f038350a179,0xb1181311c1d0a1785830,0x28580961bc1f02c00401,0xb0404e28124186c8f864,0x904037068483d0106e0,0xe0b06c101184a3020013,0xd8483c1b040481a8981,0x1068642854413090441a,0x5bc2704c043e303612c1,0x80bc2704c005b0f8c0c8,0x3c0ac2300168181ec3e3,0x23b08c13002a07a16c3e,0x4e480fc2007c101f4009,0x1ec161bc1f0383501828,0xf05c0f0786d001c07a48,0x4706c060d82d02560d82,0x40e0a118e07821c27054],#[0xd82870178e038078304f,0x60785e248a03807c0e0,0xb044bf07808641f92038,0x1611c18701e8b08d0e42,0x8e10c1707808661e90c,0x4c270780e101e8705825,0x78087a50b008c0b0030,0x121f82b08b0cc2305847,0xe11c270419707808321c,0x643a4bc228a3090f940e,0x43e02c607054a411b0a1,0x820940ee0ec3b08c1c01,0x421059000400930ac222,0xec3b06c1309808705ca,0x44c208250238387a0ed,0x8d29088164420ab0ac1,0xa070183380f09c10702,0x781d06c1c101c05e305f,0xd07040641f920a070178,0xf8581e890d422c120181,0xc16014287a0f8585b040,0x98043e50b02b83408b08,0xd2932e4830b0881e0a30,0x8523b0941e00c643e148,0x187e382341b04c26010f,0x8f864360383109c1e101,0x14130a8f920bc1f08d08,0x21e8f11d2f088534260,0x2a41f8983105847061fe,0x3505c18648887e3d0419,0x60dc1e101187e3a0e8,0x780e0dc1e104b8643e02],#[0xa8281f0a6008f896489,0x50b4223f0a222482e085,0x8d088f8642aa48282e08,0xe392e0881e8f87e281e0,0x7a384087f078430c4605,0x870285383611c1919808,0x1a234605e320f4670617,0x81e008fd18149083a0dc,0x1c1d1888870302142208,0x1fc1e10c3118178f4261,0xc08160442bc281e8a088,0x412230f87a28410a05e1,0x3e1c07a29410f87a1841,0xd07412221c07a30a5410,0x1e8a08e11c18701e8b43,0x2c243e190a88e11c1870,0x85e51045043e1e881622,0x404622294f078450cc2,0x2a2241611c18701e8c16,0x8f86c3a23847061c07e,0x8f86c28ac170581160,0xe8d8023e1b07020ac116,0x4e04650340b211c18701,0x430238301ec1611c1e02,0x62c14580e101ee001c10,0x3c1e11426001e8704e0,0x505426008f852520d816,0x1a221c0c2084e81a040e,0x8087b800705d0584509c,0x5945420ac08905c1e11,0x381105c1e1180e004e07,0x5847061c07a306c1182],#[0x8538470dc1a221e8e08a,0x190a0b044108ae1c0a1f,0x98003e1c160881f4243e,0xc2906c17a0a2c0645150,0x704d07416101ea221c0,0x60441023847061ee0051,0x2c0a818838043e2b0703,0x2160528a0a166010f944,0xf4260016228148b4242,0x78d013041ed088fc221c,0x8858380584707428581,0x6c407a4046419058450b,0x8cf8e1fc08c0b0d8170,0x2281e8c8830b0ac248a5,0x430ac6874286102022c3,0xc1e8f0231cc40742408c,0x741e8d02302c6f061fb0,0x22942b3e4401023020e8,0x40661e908830814c3309,0xc6874330208b0d81706c,0xb81310c70f0cb108c50a,0x4c431a1e8b0cc250050,0x404c1b02c687e1e9009e,0xeb06c0b1a1987a40aec3,0x811a58050a4f91814000,0xc827074407e3a2007e09,0x1e096004f86c35021550,0x50343707440541f8d0d4,0x1f8d43511c1d028906c3,0x1409a4410e437061b134,0x3e1b0a1605b820558160,0x8340793e1f880d01f801],#[0x90218250b8013e674284,0x4fe09816006913431080,0xa8ba2408029803094f90,0x941824086008653e450,0x81e82b09804294f98895,0x953e38608ba2a8902142,0xc293e401f42a0b0a3088,0x94f9614c2016e090a600,0x2890214250607a098021,0x882506c2a254f9019a3,0x844c26010a07038ae07d,0x430b803074231a48ad03,0x231cc407420210bc24c,0xc3408c0f06c68541f8f,0x20c1c24c4600c2418c69,0x387e3425803110631c28,0x4451a138d00306c0b1a1,0x74405546874283180219,0x36c250b46d0689510380,0x2181110c26004693640,0x8011a4d921b13e1f8609,0xc1d08142208960444309,0xa82d1d44074230d0a06,0x6511470e82b094722544,0x475101d088ca25802088,0x45150f02b0c1b07e3b0b,0xa543c09c1b0c1b07e39a,0x11043906408ae1b07e31,0x393e4282582821802285,0xe284146a000b9442b86c,0x1a1387e29454191a1b07,0xd03468242b86c350740d],#[0x1e0240825801441b1741,0x2b1441b141c60e43e064,0xe385946a021820e81e00,0x7e30ac1604fc08745107,0xc241b0cc3303c1b1a150,0x50b8113e530cc0f06c6,0x1b126701f82108090218,0x107021c51a0670743600,0x2820ae439064086c1f8e,0x819f0346f07436001b1,0x855c0d1bc1d0c1f8e14a,0x4f85426001393e150814,0xe4e1198461a1d0b8004e,0xc08026c161180139868,0x6b2838561450a8421a1d,0x42b3e4c330ac0142e08c,0xa505ec1b0414c330ae09,0x20ab0208f0c0b311c187,0xc0d311c1b021e941f87,0xe08c431c387e1de0808b,0x9d0ac687434330ac0142,0x9e08c431a1e8d0cb100,0xac6f07c082ac307a4836,0x1bc0f06c307a40881103,0x43ac493e1e8a0e8700cb,0x5c3a4fb0b8207a691016,0x8b70bc105e0a93e58582,0x22588229a41c9430e822,0xe8250cc605e38224694,0xc3a0950c1d07a28710ee,0x9306c0d1a820960e87a4,0xad1bc1f034307a50400],#[0x8c283a25926943a0cb04,0x281e880cb06c087146a0,0x2388ca2b46d282a448ed,0x42e004f92c2a2b46d282,0x61e969783407e05821a5,0x24d70d42e000b0224470,0x8b804341613e1e8a1f87,0xa2a1515804341613e1f,0x4a0c0d50c07b05447074,0xd05b8107b82503801a4,0x98009807d0a1e93e6058,0x2a4f929123a222040d60,0x98152040d5049781f42a,0x9040ae0542e098019c4f,0x26006913438921181e41,0x805026907a30584fe058,0x14470dc19341e900d105,0xb0228a93e607e07e0,0x8c6907217943c2d07c16,0x293e482007f0a4a22b4f,0x6c5f4185a14e0582600c,0x41d0407a0582600c2d3e,0xa8ad3e407817a388ca2b,0x2a4f9817d074120407b0,0x738008c2084650f0bc12,0xe010b4224f87a299c220,0x4a07a46010b4224f87e2,0xe1e8a8bc2c8942343060,0x28c2c2a508f8042d0893,0xd0dc1d021e9b8042d089,0x8730b422c3b0cc160143,0x70cc2d11c18721e941f],#[0xc105e0a93e887e0b0238,0x8ec2d0881f8050ac2d04,0x44f87251a42207291142,0x690465082c08e01c2f0,0x448e85283a0680d18179,0x13e1e89801404f87a22,0x42448eb021d07a2e005,0xa0d820c1d04c6b0b0ab1,0x42a15154170ac742ac40,0x85300b0216d04c6f06c3,0x28501260044136468743,0x4687a3e009123a4f87a,0x3a5087a2850126004d91,0xe09802054451c4e00912,0x2d1d4407422388ca2ac2,0x1e2388cc314451a1d0ec,0xb46f061c50b436081e94,0x1f42e098013e5705c083,0xd0c1e9267047811040a8,0xe9269039c0e000cd1bc1,0x2703800440ed0bc191a1,0xc0d1bc1d0b8050c1e962,0x7c0d0c1e948105382705,0x7a319c2205b8007f46f0,0xd0c1e8e14f0346f07430,0xb0c1e9a1c60146f07c0,0xed0f41503801a4c3b06c,0x1ff0dc1b101e8c222448,0xc12b0418b10c687a3302,0x888407ec6f07c0b0c1e8,0xe921194207e01c2f044f,0x103b8030bc1f03468881],#[0x8381ec188c2093e260c1,0x7a485e5081fc2f044f88,0x1bc1b0446b07c0860250,0x330a2514c10882507a25,0x307ac151b82707c0e014,0x21e8c1103a0ab0a26088,0x60c870643b83d061c31,0x22c0a34c4709c110c197,0x2246b060e898208f0e8,0xe82546d07430661e8e1c,0xc1b0346a0a2603a1e970,0x3c1d0c1e952907010024,0x9858710e82ac103346f0,0x2ac1b025151a82b080e8,0xe8d447061c07a24a41c0,0x46d283a3a1c20e81d121,0xa8cd2822388ca0ac2601,0x23c270414a324f8ec251,0xd0941a33802194f8e0d0,0x4f9007f084a2334f8a11,0xe405f41d048e232c2601,0x217d074120407b088cd3,0x8211907c27048c8524f9,0x83543511c1a181e8e248,0x343508d11c18701e8d40,0x61e910d423447061c07e,0x7a4c3508d0343d0dc186,0x7e1d8354302344707408,0xb0cc150f437074087a60,0x18761e921f8770d422c3,0x1c161f83408f0cc2511c,0x40d1043709c1065c1832],#[0x4197060cd021c1a0d023,0x28ed0e435094130ec230,0x23c27054410dc18701d9,0xb061151140b0c1e920d0,0xce00c4418c70a2b40f01,0x81e8e0dd04c431a1e8b0,0x181e8a2c30cc0f06c6c1,0x303c19401e8ac0f06c6c,0x1e88c4303c19401e8ac4,0x9c1b0c1987a3066c431a,0x3ac3b06c08661e8cc681,0xc84e6505c23110cb1c2a,0x340700b06c0d041131b0,0x82b0980511470e2b058c,0xcc220544233470a8e232,0x87a283609b094451a1e8,0x19104687a3806c151146,0xc0f06c307a3b090dc274,0xac182a510b0403a0cb1b,0x38060a51141c03b46e0,0x7a48464103381311c1b,0x7051039c082b46f0743,0x1e8f46f0780038510ae3,0x42b14517020ed09c191a,0x881a048087b46e018294,0x525151bc0f074307a405,0x20680d1a2b1441e8e1f8,0x485346f03c19441e8c16,0xe5040cb1bc0f06c307a,0x540b0ec0f06c307a5070,0x780070248e1c23b43d0,0x7078030216940d43246b],#[0xc07a486443308c1432c4,0x284143201c0d1a067061,0x1ee00530546f061c07a,0x5150dc170346b09c187,0xdc151bc187ac26001c1,0xd1bc2704197060c87041,0x4709c1707430530c920e,0x46f03c1d0c1e9211b02c,0x21c13e258c16b0814c3b,0x9c1f04c08705082c189,0x8941e921943b0ce00c47,0xe8c1c308c151bc1f0219,0xc20945d1bc1f02c10941,0x1c30546f07c0d0d8060a,0x7c0d0d8060ac2096587a,0x580f87a203a0c87146f0,0xe8b8191344070178a448,0x8ed281e869123a835281,0x121e8c8e8714483e1e8a,0x5f0f864307083a068ed,0xf05808898208a2185c4a,0xc283a2603ec10a41e8c0,0xc4d05e383407e010f86,0x87b800a450940ed11c1e,0xe922b8969123ac203f42,0x10354101f42b081ec3e8,0x80707443081ee0c4d148,0x9441348e89630940ee05,0x460f92825898208c4185,0x8906d06078962608230,0x41b0820898301a108962,0xb418700f898208a07c1b],#[0xc3ac61106d061c096208,0xe8983c08c20214470740,0x4605e28701061a0905e8,0x680a3b4605e3a448ea1b,0x1a2523a4605e505283a0,0x8941e90198584210640e,0x507a3844c1b0306d040e,0x4a0702b06c0c1b4103a2,0x1095048f87a2e01c243a,0x87a4c410960c4a07a2c4,0x4141d030921a420960e,0x1b0740b03869042507a5,0x961a25c3a1e93831094,0xa2603a1e941604041902,0x7a58701050740c248690,0xb41b0740b0386904250,0x825868990e87a4871831,0x287b0fa3a38581010640,0x4287b10a3a3e00917054,0xa4230a0e896460091705,0x50ea3e1c0cc1b028cc1,0xb054243a250643047427,0xc2a8690b4203a261586,0xed08c28945070115074,0x8220c1c506c1d02c0e1a,0x1c09230458682ac289,0x43b8003e16930eb060fe,0x69181e922906442b08c1,0x1e8e1043a807021c7070,0xb801642b050ec1bc1870,0x5c1702c270706d0a1c07,0x61ec1b803081c130e84],#[0xe1a0e870258d0e90bc17,0x1311c1d0a1643a4833c1,0xed0a2505e3046c0f09c,0x640e1b42c3a259586b05,0x50d07a385a16032c210,0x9410f87a184184706c33,0xf87a20588d3010f86c2,0x2c2304c0070248e41141,0x2c230006070248f8083,0xb00c23040ec3e1c0f02e,0x3040c23010fa281c0d81,0x48a0b43706c404f06046,0x7106e041e8f4004f1005,0x707068701e8a0ef03c18,0x709c003e1c228248f81,0x15441c27000fa1216911,0x443f0613d0b1004638a4,0xd0a11914004e8f854260,0xc0924c18c460dc1b0213,0x5c3b0cb074023f425041,0xc2305405094112216a3e,0x186f068607a50650ec32,0x701e8d0ee0cc09014087,0xd00c106c443a4961bc18,0x207b401c14e0dc0f0786,0x1502c0e0d82f061c61ac,0xc187ac20704a450ed04c,0xc1eb085c3ac15054061b,0x30ed01c0e1bc1f0582e0,0x70382586f061c07a285,0x7040400661bc1d001b,0x1e8a91309c161bc187b4],#[0x1eb081c0e0161bc1870,0x86070249186f07c150,0x30016c3e4a4141c3ec23,0xf85a4ca41523a8cf09c1,0x32408650940308c01130,0xf0f8f290408606d0f864,0x1f0f8d2760bc2704c001,0xe1b0607a460bc2700c10,0x18701e8a1484183703c1,0x8fc224ba2219114161bc,0x74123a07a224c2f412a4,0x181c05e28468f12e8430,0x5084ba22510ae3c18889,0xfc244d2246906c305850,0x6904e4f4248e13889104,0xc8bd061822a890203506,0x51c2a334186686224080,0x921943d1c2a390390e89,0xc1e04168548913e42328,0x46905a890544f8c67134,0x328ab058030b43d14460,0x23b8013e1e934690e8e2,0x5211c3c8a918861091,0x8bd07802248ad3e45078,0x5801a48ca2b4f9218046,0x721c13e1e901e23941b0,0x90f0631c342d08e00690,0x1600c2d0f47118042a83,0x800522413e42388ca2ac,0x98005a4f8e6713582307,0x4c250f450e8a90a6960,0x8528653e8c8c8e2328ab],#[0x1b048a8528cd3e3a2541,0xd422c25021d8703a394,0x1c3c3309418c3b1c287b,0x89842388ca2ac130943d,0x60e9043e4d601292248e,0x9143e4d4a48aa3a2]]
set_option maxRecDepth 16000 in
def g251H9 := limbs80 #[#[0x4501310210008010b182,0x22410514840000c10440,0x41850000400c210514,0x401413400832840c70c5,0x401c00c13835c12805,0x14208444004000018200,0xa6202298006381004041,0xd00d0400c10490400c10,0x801820400450864c610,0xd1c01c10c1101200047,0x18a8700a0404840000,0xcd38200300504b08340,0xc600208d003843142652,0x24000570813050000,0x11c20001c004014408,0xc168a1c2013252,0x1412400011840800800,0xd1c918808700048200,0x1001005746180083006,0x43421c10040c71020830,0x200100a0830c10817c,0x8a0001800c401404b249,0x90c00000066055051c30,0x60020050c328d0cc10,0xc000608067c0009018c0,0x100804a2157810087510,0x100205408104230e28,0x81080060b4118010b504,0x30000500030060c40000,0x79a1c025f49114318b11,0x5800a18a1250c00a98ca,0x42d648a7e020134110c1],#[0x6cd2c270320d68345044,0xddc041441062212400de,0xe6c204000a00004c0412,0x100495050c000404600,0x94662fc8d52d13839c00,0xb1c6a7e2b1d2813184ca,0x84c049c5e8ebc9e0d9eb,0xe012b9c77c00014f2f82,0x900002b61826caa55393,0xa146d7e2780000000388,0xe86e03cf5b46a2861bc4,0xe4000000b400000000a6,0xf6306209f80867337402,0xc703f58e96acd64b4c86,0x280c3d057f51000003d1,0x3f91b82d494d63871ecc,0x44ecafc3c0272d1f85,0xbc0001e2fc0002d31400,0xd0c23d8f9950bcd200ef,0x7ef1a84a9c0002450b0e,0x65e71c00026a0d4189cb,0x5d51a28fbd8b798ddeab,0x24148000292e0000087,0xf69211b15ecb8a833c00,0xccd1cc0002028c00028e,0xb74ae122a24e35245609,0xad0a0b0793876fe83e0a,0x1071e78ad8e48a2da910,0x35063c278d11dd4eec8,0xfc0001c9980000000000,0xfc000000000000000110,0x40003ef1baad4000252],#[0x395e701c1c882ce1296,0x66c4fc4af503e3b64c00,0x54ce9d424c299b1406e1,0x25818434f554fd01b949,0x1c00028100000254f2cd,0x9800016e74ee26815cd5,0xa503fd3a611c82a9e4a,0x8fc255155bc4ae2bf781,0xa80658451e94784e98ab,0x580000016643bb913611,0x9400000002c93c000271,0x8814000380d500,0x28f8cb3458d33440800,0xdd0f81961c0000000000,0x16811ec7ef942a159170,0x1071b89e800018ab1cd,0x700002e1430c1b111400,0xc4cba14b000000000251,0x1c00014ee991f846facd,0x3f563bd247c2cf63460a,0x28000000029078000212,0x3aee8878c0002896780,0x2511db8242ad3f699400,0xd6d4a145c495b041be47,0x6cd508000368810422c5,0x2007c61340003455d6f,0xea555c00032158c90000,0x880000000000008c9981,0xa00001ca3c0000000210,0x34b500a2dd6c64000029,0x38ea00002a57acd,0x54e49400009498000000],#[0x61c74000f7d472e7fc88,0x306dc00000000000234,0x9000018a41532f946400,0x54000000000000000020,0x55547c00016d290c0e8f,0xb504c00002cd818b23cd,0x49abb80ecd894384d18b,0xcc0000ab36c8b400006e,0x18c6251dd870ec5,0x5f1571c37000000dc800,0x1510dd465dd2f800008f,0x39563d26040003c46a50,0x60cf7441a24178000045,0x41c84,0x9fd2881249b058000000,0xd1c86deddcc150000050,0x131cfc74453270f21d0,0x6b6edb0b39b628877800,0x20302cebc0003c1af4b,0xa4000000004defd5ac00,0x2a4840000ef9182e808,0x3119449fec7b4000000,0x420a1ab1164d1f30e000,0xf04cd800000000cbd163,0x1c374000300ab48bfe5,0x600002d2b00000000000,0xe5aeaeb1680002c7a187,0x3cca984140002476421,0xb1468800013044000000,0xa845b78e6c0002ef73a5,0x2c57486,0xbd096c0000000204b400],#[0x470570000242680002d1,0x3007dc1564000341b642,0x4443a800000000eb8607,0x32a75803dd09ad031ca,0x6c6e302e24e2ccafc00,0x867070731c0003cc8907,0xdc0cb0e4c3564ee0af8f,0x20b1980002272c000353,0x188c4400000000000195,0x82efc70b86cd7800030d,0x380003421c000140fb46,0x10736b0500001c9,0xd60441038562af80ec00,0xb4000000000001c8df31,0x284f7ad8c0001429d50,0xd08bbc21800001c66800,0xd1c6934d8a8200000141,0x73564994d40000000151,0xbc000000012a0bf62c81,0xfba78a4d9365d00002eb,0x7c0003140d83340001d4,0x3cf054edb4c1c000082,0x1e708acf300003480800,0x18b2b4130000006e740,0xd1cb4346cd22eecdcc00,0xab492d6e87caa4000387,0xc0c2f335a6d4bc0001ec,0x28b54000000030f,0xfc6dca31520de150f400,0xd6c5f5d1780000cdbf4c,0x20c43f46f095cd1,0x1405708cc00024a6c00],#[0x20ce6c0d5b800,0x44e49474000282b800,0x68000000010329d45800,0xb00000000314d8451908,0x10b5395f8000088ad4d,0xaa47e000000002ccf000,0x200224883cd339ed5610,0x1c12f091574e19abe306,0x154418250000189,0x4c0003ad60000175b400,0xd4000000000000000340,0xc9946c00038ac400014f,0x2ad0c000112d0000101,0x4d4848000000008cbc00,0x2113c8eaad34f75,0x212ac00,0x28000024bfaa10000000,0x2348505574129a9b5a7,0xd8000000024c64000000,0xce0df000000000000085,0x5305bc000181fc00038f,0xd35e4ff20a5d0d,0x2284c00029298000000,0x960888bec000105b800,0x20776944d6462d5a4d3,0x971625c6536eb8cbdc00,0x6908f00003c537aec6cd,0x24e9b04217083b2bde51,0x998a008c5c00018b6ee1,0x6243a70918d18dc4b940,0x7c0003cd20558ec818c5,0x24f78588000264],#[0x2087400014cb7b3e800,0x31955000000000000000,0x868934100f913800018b,0xc4090e45580000000093,0x3b0cc000241d51628c3,0x8b0404465400026e6c00,0x1210c000003d5468fc7,0x2814c00,0x62400000003c2b400,0x6b060fe1fc0002269000,0x6253c102b0000355c549,0x4000122bc0000c94ec2,0x248fccefba5838b484d,0x35022510a0d9dd17c00,0x1b5c400,0xa800000003d59a8eb400,0xc32dcc4ce0e61c0001aa,0x4623ce82654f7871424b,0x3c611e8e9400f87c309,0xa12fb9c18d41f4497c00,0x66de00002c9c8f4ba8c,0xcfa6cc000240c80003e4,0xf4d0401224efac00024b,0x3400036796525709d408,0x1166f0cacaeb6106992d,0x188b303a04f344a,0x3d2dda6bb90f3501800,0x10ec0000000000,0x2a38fb0e5209f4bd400,0xf5435855e3d1c0000000,0xc80c4d4c94000000018d,0x190240000000095d007],#[0x294b9ea280000000000,0x49d4940001031e91e000,0xcc87d215c860000195,0x180000000364ab049c00,0x3912ce2cc00002c190f,0x8e7935cec40000,0x329778952124c00,0x34b654fac0002a53800,0x8a69a5c4830464000000,0xa3c4980000000000030e,0x202ec458e4168000175,0x9c000000028d12899000,0x1c677c9acc6,0xbc0001142024a2492400,0x11066c294eced558365,0xd500303494aa8000000,0xfacd5de46fc60005fcb3,0x41a6d0280003263a90,0xfe4e90000188e8000000,0xd685339236467800032d,0x146474c10c6324f9f12,0x20cc5538c0000514800,0x8ec6fec62e21390cc800,0x9586ae8b72a05188420c,0xee62c989ec0311ac1006,0x8006db454d8759c7ab2f,0xf802c800018ff514de4e,0x90c551a68ced94cb620c,0xe554cf816c0001e97c8b,0x290e28c2d51f3006650,0x612db7c25c0003cf4000,0xafc752e3aad192e4b2e5],#[0x2c0003d1ec0000000224,0xec004400024d4908d28d,0x231a013918f,0x15b18188e00000000000,0x9c00039452c0e690cb8e,0x38e5c0000000387978c,0x478bc48667ca04000000,0x4553968bffcdb86fe98e,0x323ee93b750ba0d7011,0x1cf080000000000,0x21418000048ec000000,0x228f400000000ebfc00,0x2c00000003c540000000,0x20e2785dfd22eaf,0x9c0000c9c0c49355a000,0xc4000000000000000009,0x813415446dfad3ba8e,0xe99411e29ccc9002d400,0x9e546b028800000000cf,0x200002c315914c5209ef,0xc4f80002d602c9aa85,0x4000d800012c5c000000,0x1429a0360c0a78e01d1,0xb4483400020c30000000,0x54d01fc6e80000000263,0x3cb740000000255,0x6a2c000144a400,0xf1a56540e031c04be400,0xec000000030bf2ce61b0,0xe149e40003ec9b4858ce,0x3f2eed6a3064b4ccad49,0xf4000312914787b136ef],#[0x20000087be7190000052,0x3306c000000008d6401,0x70943800038920000000,0xc8998e31e3f288,0x55844d05e00002449400,0x7400000002a3f6809d31,0x156140000000226,0x5c000000000000000000,0x2cfb00000000000032d,0xa41c00,0x8583bc448c0002e98c00,0x4546c400018fd3eceb15,0xd3508d6e07043aea820d,0x1526e49d284a80003e4,0xa9cc830cddd4e8543000,0x3c66952fa80001c0840d,0xd8834fe75fce4c000270,0x340003c828f1fd10a153,0x5180bcc364000293a0b5,0xcc000088a964226eff6d,0x10c57aa9a800000f3d40,0xd08e3c719f8193d5eb40,0x28c0b9c7c42b13d0d854,0x49536c0003cd0c43d1c6,0x3800000003528400004c,0xf000032daf0ff950070e,0x386eeca600002e7012c,0x34d680003c97148c800,0x9c000000000002882000,0x5a944400009383cf69a9,0x2800000001c48a8218a5,0x8800014f88ef1cc79d85],#[0x6000002db8211a112923,0x6408d8000000000000a0,0x55a7a605847014443c13,0xd3960c00000002030554,0x840002d60934fe44cd40,0x1800004be94e8e6f1744,0x4e03924159519c00006b,0x56092ad57bf0d000024d,0x3321c000000036cb050,0x92e400000000000000,0xd38978000033a3452400,0x1c2580c,0xd884240002ceb0000000,0x312b413f0000144,0x2dc5b115bc0001931c00,0x17f126262244f0000190,0xac0003304189c4000200,0x282281b3c8510a17d3,0x1a03b93040003159400,0x8000000003842dc4dc00,0x2c220000284eb10,0xf18a64000300f0000000,0xa923990ccd02d00002c3,0x4b09058acc0003c4b102,0xbb00000e3,0x3eed40002eda000,0xcc5359c89ca074000000,0x215309105a33c121a2a,0x1706040000881ca59c00,0xbb507e467d1403cc3a8c,0xac000393204ba653fa4f,0x22c38efe1b366937b05],#[0xc000026c0a533f214400,0x9864ac2934bd9122290,0x616f13dd512d4,0x1a6c4000000,0x38e0b41e4000000,0x12573c458000000,0x39be04f706400,0x14ba8000153fc2fa000,0x543d80b18000370a800,0x264400003cc7c0002f0,0x81ab07e400,0xf20177aba89634000000,0x1925dc5,0x319087d4840000000000,0x256a0ca40003cec0e5,0x2c00015334aff4cf6400,0x58956c0e7c05f8000147,0xd400014f2400012c4c51,0x20edc0003037c000044,0x1b420a281c000300dc00,0x30cf700fcd3efb3,0x3942c04c800,0xa1539f45100000000000,0x2c06bc0002abd40000a0,0x240000656c14f40000d6,0x474e77859d2bce919881,0x380002d00b8ed548960f,0x354fa042a7c8c0c916c7,0x26dc4ed2c231954,0x274f4f41838988000000,0x498d8d8adc0000000060,0x205800000a3f9844645],#[0x7b4a840001a3a6888400,0x18e6800004c36a084cc,0x2867000000000000000,0x28000391b400006d7000,0x55a6faac37232d402dac,0xd1ceff830845c00001ca,0x243f8000000000ee545,0x2d30000028f38000000,0x1d5ec000000,0x0,0x3499400,0x5c000000000000000000,0x26884c06835ef92bf50,0xd7047d304b0318000000,0xf926800001128dd528d5,0xe8000000000003944b01,0x5f215d47f6c7f1a9384d,0x200800003153f8da551,0x6ad5000ee043dc000000,0x2ecce8000280b28663d5,0xcc8dc374fa8fc8854603,0x281c7cd7cc05a154c93,0x7c0002a57c0000000000,0x5d15140002104d04e2a6,0x5bcbbbc1e045a3d1ad08,0x327125049ec,0xbc00012f24000108c400,0x408dcc6f0de400022a,0x152cf4640000254c400,0x5fc35c0000c729056800,0x6c4b2dc0c705a952aaeb,0x187ce31fad0b1cea6b1],#[0xa813540002d630e68800,0xfc00000f0c00030bfa13,0x394c00003cad7022f8f,0x8800000002e7264db400,0x275bb948345c80000f3,0x440002cce6c8a1491000,0x8ac0000042c400006d,0x2f2fb400000001445c00,0x347700003ecad92c608,0x2153ac3c166a800,0xe2000,0x7c000076200000000000,0x18f9000038a,0xae852c00000000000000,0x1d18800018e,0xfd927f95fec347a6dc00,0x958e598fe10b954b3e65,0xc96e11ecbf93700002a0,0xa800000003525a476a12,0x3811e800036f7847d46e,0x2cf2b4163a8e703,0x572d300003287c000000,0x3800026bf0d130000041,0x1d30ff1b641dc47db4d,0x30000000000003617c00,0x43ca374228000065ea40,0x70000093ea4fa92d27d2,0x16151887c0001d2ec40,0x8790d5d2c00001107400,0x5e8b0550130cd4247065,0x4b89bc0003af7400028b,0x496a036b5bc847942593],#[0x40003830c0000ec30c7,0x4d20780000e55ccc7545,0x5ab0558d7663800000ad,0xad6490000000014bc84d,0xf206340002cd4164a782,0xe8e41800000000850086,0x206b000014e1d82810a,0x2846d493000038a5000,0xd80002b01b8d6f0f4800,0x9c55c80000c3fc000349,0x951490ade800000000d2,0xc23400000000cf,0x864a900002e0b3157400,0x38eb80000edc24e714e,0x59296aa732ef82b5c800,0x107e800008d0be3,0x5831ace75bd65013f400,0xb8000186d1a7072ad9c9,0x1f59d438249,0xf08a4bc80168c5ada400,0x1410f6de652d8832009,0x1d069a1300000000000,0x3244c706c35124000000,0xbb95b490c5023b017e48,0x3739381f000014a,0x3536000000002d64000,0x1c000000000000000000,0x43833000000000000346,0xd4b000000000000153,0x2c35254a400,0xfa4e2a4dfe6224000000,0x9bc078c12fc80c000202],#[0x5a608c000294ac000053,0x70007730d712e923eb0b,0x20f1c000108e4000302,0xe655c0a4179328000000,0xd0000000028bf50638a6,0x94c800000000000235,0x12b1c0003c9b400,0x126fd80002c1ce126400,0x6c0f01e8b80000000281,0x88000000000002c805cf,0x3c9f6d51a00400000ae,0x14c580000c9b000,0x2548800026f00000000,0x130fe40001d270000000,0xa8000042a32a150c0b02,0x280200000000275,0x9629240003a9ad71bc00,0x6b9959c00000001d0,0xf96c7000039351e49800,0x2a65d945a664f00a79c7,0xe62eb60a2f874c000112,0x34b0c438fc1db4e6645,0x4970770a339180860800,0xb7844bca770b1051b289,0x1964669902bb7d50c25,0x3f53bff172cfd8866c4d,0x84ed8a00a3c4bd134434,0x3ea46bd463cb8ec90acd,0x38df80000000301ed07,0xa55165488c00006d1400,0x210d299160e43c000012,0x2583b4c7ac00000003d6],#[0xaf42bf53100595af1343,0x2adf00000c9a7ed6ec0,0x564341411800004ef000,0xa494b691f7664ab18c8e,0x331380000cb1d95f250,0x5177c4280889141400,0x4ed4344700000000000,0x9ec96083ce53c800028c,0x9b8c03111815dc45ed41,0x3ac4324ad1625800008d,0x5e13c6c7a5ec034a7241,0xe18f61836a83c80001b0,0x55ab8c680000000094,0x8b615af8c00,0x1f6268981557eca8800,0x8944100000000347fc00,0x145900001340d93,0x187b000000001c56400,0x3d2380003ed9c00,0x73214c00000000000000,0x253d400000d3cc8fb0f,0xe0a459405c0000000000,0x4aafcc0002884d0cb8e7,0xcea557ab4400000000ce,0x980000000288794b3755,0x4eb788a5b047b401987,0x1400030974000000008e,0x800003506c0000000141,0x1a88982c2a6464003c7,0x8000000000000000000,0x6c00010aefe0faca228b,0x341811fee1110cee00],#[0x2d3e400,0x82f606b57020000000,0x938dd31263063de2d400,0x859a15d8000180,0xcc000002d80000000000,0x510b81013c137c0001f4,0x9466b400020700436d84,0x20afb8b140000000041,0xc1040000952f54e400,0x96115087540000000000,0xff86ca2df400026f7f03,0xb0943e464f730b6cc142,0x5d10d498443e90daf13,0x446869524e4d4438a12,0x4000310580002a72215,0xa415888a2b4f14000002,0x1f70fc2a19ad38e66d6c,0xb400000001cc5400036a,0x203784f,0x399184cdd491a4000000,0x1f153400000001ab96ea,0x26516da48d8a25871652,0xc81091d120d295ac454c,0xc26e09df4b445541ce,0xa0fedb0c455405000,0x3d1e4d31a6adc00,0xc000029047ca68000000,0xb80002af9800004fde4c,0x10c03912a3a234000187,0xe583ec00000003e42847,0xa000024abf94a800034a,0x740003d070000103b3c9],#[0x4e145c8c2210cc4e42d2,0x1e154d41c0a,0x2e4314434000000,0x3d61000000fa4000000,0x290ea4c738b2553d000,0x9fd03400030063870800,0x28e0d235c824854,0x255f40003d2520a8c00,0x82a63c000200056ee400,0xb81050520f62f3213d4a,0x1800000002ad9b4a3929,0x3000010c50cda243e4d6,0xc474808a856f450dc2,0x388b953740fc400,0x25ce500000d2684be000,0xf2041b697a4144216e88,0x87210515cbae41428a,0x30680000000040c000,0xc0000000000004aac00,0x2a8ec0001a1150f1144,0x98e2e4e4831233511000,0x540002e49c136800038b,0x3b8dda3160000322f403,0x2de1278000290,0x383ac0003948c00,0xa093300003c0e8000000,0xc4e59ac98ccf5301994a,0xb7d560c036c2750f7e6b,0x28b9c000262]]
set_option maxRecDepth 16000 in
def g251D10 := limbs80 #[#[0xf73587aea9aa3bb58960,0x2ac5f394d62f9aa6b15d,0x53f9ca7317cd5398b76b,0x7f960443fca8221d7595,0xaa8a21fd50510fea4288,0x8910fdac4887f561443f,0x885ff72442feb9221fb9,0x2feba221f794d10fbaa6,0xfdd510bfaea885ff7444,0x80905ff76442febb2217,0x482ffb8a41fe54120ff2,0x1fb58920fdaa4907ed42,0xfae8907de53483eea9a4,0x75482febaa417fdd120b,0x2617fdd920bfaec905ff,0xbfeea985ff744c2ffb9,0xff71503fcb0281fe5414,0xb9281fb98940fdac4a05,0x540fbca6a07dd53502ff,0x5fd76502ffbaa817f5d,0xffb8aa1fe58150bfeeca,0x98950fdac4a877d52542,0x8a877d54542ffb92a1fb,0x42febb2a1df59550bfee,0xbf58960bfee2b05ff765,0xca6b07dd53582ffb92c1,0x5582ffba2c1bf59160fb,0x43fd54521bfeeab06fd6,0xfbaa690fed62487f6a92,0xf70546febb2437f5d521,0x12a3fb58951feac2a8df,0x51efacaa8dff72547f73],#[0x6fd65586ffbb2a37f5d9,0xfb82c57f5d952fdac4a9,0x4d62fbaa6b15ff7158af,0xb15ff7558b7eb2ac5f79,0xbf6b8ac5fbdc162fdae0,0xbdd562fdaeab17ef7158,0xe0a9dff7254effb82a7f,0x596ffb82cbf7dc953fbe,0x1ff50910bfee4b2dff71,0xfae4887fd62443fea922,0x74443feb2221ff55110f,0x221ff5d510ffaca887fd,0xffac2907fd51483febb,0xfd53483fea1a41ff5c52,0xaa241ff5cd20ffac6907,0x520ffae8907fd64483fe,0x87fd76483febaa41ff59,0xfe90a81ff55130ffaa49,0x58540ffaa2a07fd31503,0x4a07fd32503feb8a81ff,0x3feb9281ff58940ffaa,0xff5cd40ffac6a07fd535,0xaeca07fd75503feb2a81,0x1543fe98aa1ff48550ff,0xa1ff4c950ffae2a87fd6,0xffac6a87fd72543feb12,0xd74543feb22a1ff5cd50,0x8ac1ff48560ffaeca87f,0x60ffaa4b07fd71583fea,0xffd75583feba2c1ff5c9,0xea92c3ff58951ffaca90,0xc562ffae0b17fd6354bf],#[0xb2ffd70597febaac5ff5,0x7ffb8acbff5c565ffee0,0x138000ffee4b2ffd7259,0xd818304f810b03600930,0x3060b4c27c08701e906,0x522130847410503b40d5,0xe41aa066317a05a31578,0x121cc82e1f5c7921ca46,0x2940a0b26d0954243c8c,0x1b0c1e2eb0b672bf8ac2,0x24de03624d293390ca83,0xfd83e28f3c3c00ea939,0x2214705161444d0aa417,0x104f093624c992c64975,0xa573156c54c14d951c14,0x5df172e5ba5692595961,0x48d8e762ad84b603d7c1,0x4da856925a0467219836,0xdc3e6f79b996d75b186b,0xe0976a5d6d74c5cf5729,0x1c7ecdf777c39eb7795d,0x3858e12783ae0af81ce0,0x8eb23438b6a27188461c,0x74657a94b24de91b23e8,0x267609cb66f19a8e61f9,0x2961a44e898a14e80e9f,0xb50ac76ac6a9e2a21a77,0x51b432cd9b19ec07ae32,0xbbbcaea4b97edffb6c6d,0xc4830c0c21303fbf36f5,0xc1b2afc9ab225c6f3192,0x3f4e6d263441cfab381c],#[0xb72fdbcf693d8ab5b8d5,0x8dfe247855dfd77c2de1,0x8ea6fa29e79398de523,0xf1d041dc2e13038306c0,0x1e0c38149c1ac260b001,0x804287c5c2e130580808,0x51e0584c0214422c0b09,0x83e2c0b0981c060c1a8,0x84c04190a1417098042c,0x380a14a02e1305800f8b,0x7c9148642386c260a118,0x2948422c0e8470b84c10,0xa12003820223d800e028,0x60f80214a0b0470408c1,0x7cac3613041a088230,0xa290850785c26081e118,0x850420164470b848007c,0x2c88e1709000a07c8290,0x8e00a04c34006c1428a4,0xa04c30d82811189c1208,0x38a62384c14010a1f1c0,0xe0d1344709000a21442,0x88180b01c160e108480,0x70508c1a102239382c15,0x7c26090b01801486c361,0xf9786c260a118342844,0x1d089040a21c260a0029,0x9484385c2608221f1c9c,0xa120061a0514420f4744,0x40670d0209216283d1c2,0x103f038180b841c05024,0x83e1b0a1709040290042],#[0xd8ac361020120a4001,0x982c10401246e0f02868,0xc362a89612010242a7c,0xc1544b0d8480214283a,0x1c0b02c3212002a8a0c,0xf86c2c510812182e1509,0x381067868009e280c2c0,0xd848a21424393832120,0x46e0f0286800d8c1d01f,0xd0c1220401d090140902,0x80694c6028111b83c08f,0xd080806954602c0d040,0x4010e90a080684c702c,0x8030586c0e0e08851e94,0xb82c0e0d1b044312190a,0x7e0b06881c054b0e8570,0x861e94070301406811,0x1f9282104151b83c0c12,0x4682c111b83c0a0a0086,0x54f8f4803e1b0a824a05,0x850a3a21061bc1412008,0x83c08f4e1ea510704802,0x32150101f0504806190b,0xc360f058142854827070,0x70782c0c1200862c0e2f,0x2c0a182a40883a15c2a3,0x37068682942fc2a37078,0x810c94520e8670982c0a,0xc07018cb0d844460f04,0x861e9619c3401283d06,0x8a48210413028dc1c160,0x4c0a370705414010c3f2],#[0x280f8641611281918a50,0x1902e0b0d81c1a12003d,0x8cb0d83c160508192038,0x384c16051b8380218a03,0x1e0b030082a18b290143,0x2860c924e0e867088dc,0xe87c6290cb088dc1e0b,0xc1b00410f4a10e170982,0x11b0748c2e10401dc0e0,0x10a1f180a0441437078,0x84c14010a211a3b84c14,0xe170581c18350900263b,0xb0dc1e0b02840e8e220e,0xee130581c18360085230,0x918486e0f05814287470,0x836181e1ac18210a3d04,0xf8bc28561b0708178241,0x3e31486c2082c1200320,0x42824a434120085848f4,0x1850a0bc3e5010002f,0x8c1a003439386c201901,0xb01052907c6c3613050,0x204161301050f9487c26,0xf0d1184c04143e82290c,0x4a43810018641423062,0x52707c7028e30982c04,0x600a41a0f8c03c260b01,0x638c260b00850f8f84c1,0x811b83c0a185e0c2a0,0x1b83c0a185e0c2ca5048,0x400f44041509c2002001,0x300200f8c05024370781],#[0x4c04090a3d0f8c14c2e1,0x1e9584c04190a3d0a0d8,0x54c26004181c18350b02,0x10010dc1e050a3d1010,0xa84104370781832006c5,0x14370781400f4404c090,0x21048c85e1f2d0a840,0xc00803e31486c2042a11,0x70781832145e58870b84,0x51e88092921100200643,0x34363210048086e0f028,0xd178203636130480040,0x61304800403436301000,0x705211000d1e820363,0x41530305c24370782832,0x14542703f0982c04143e,0x41000710dc1e060c2f2a,0x44697c361509000a1604,0x8c1c02028c2c2f110784,0xf4285938231114e1b090,0x90470b841040059110f8,0x8f4e090445814148b862,0x14e1b0500c1c21088580,0x705004207cc270722211,0x920a42108a8845111661,0xe080b0550484130b0222,0x2c240a5208e1305000f8,0x901a0ce1305838421422,0x47074238441e083e2920,0xb0d8440a159d00444485,0x4800513e413934830d40,0x9c282a170c120844b0b8],#[0x4b82861108d1d0a12088,0xa8258441c0a008842a3,0x985814007488470e1b89,0x384c1688150491a271e0,0x95cd438730c121b4507e,0xc2c0b038343212008d13,0xb0c84c08a87440894412,0x342c491b00151a170a84,0xcc72a0487102c26050d8,0x12151219096181914138,0x4208102183b83c0a344e,0xb0d24aa13c240e010d46,0xe8b0309e090b00424207,0x90046a5060ac1a00941,0x42c1200ce440f4d8ae16,0x13e513934830d61b0481,0xbd421541c570b828240,0x281c3617042fc1a202a6,0x221168d1e8b001c8582,0x9507800570c94460bc78,0x824011b830ae0504861e,0xc25000ae19283a1e9020,0x28220e0088428e91a505,0x1609001d2211c38bc370,0x13c2c010688468e88816,0xa37070442c010c3d2c30,0xb86c1e047a60547182c0,0xa983f0e0642a87414010,0x20ee151b8317e0b02860,0x183288c1a247a3c00882,0xca8ce120b0046a506274,0x6506528ce13050082a7],#[0x384c10cb06881c064c19,0x422d1a3d10761a08a190,0x1810ca370682430f4b4,0x661866941e8e5210416,0x7098282c01108e1c3212,0x3c220c6582440651a4c6,0x37068482c010c3d34361,0x831e96520ca884582c0a,0x7e1c0c8550e824261b03,0xc20cb058146e0d0c1924,0x50a848ec003e3d4a121d,0xdc260a00850f94882907,0x370982c288496412c351,0x8186c01185948981d088,0x874c29074991d8361307,0x100490a8441607070d1e,0xb038386a10981d2c8500,0xd4292c3a51104415c2e0,0x247031483384c1607070,0x820f8f4a449509c3d0fc,0x601191f18401ac26020a,0x584c023a1888149d03c2,0x940a1b83c0a004e20151,0x90200a09c461f150c1d0,0x59521b83c089c182011,0x70306c260a0b8386a007,0x5c260b070d400e070e86,0x690784c107f003824920,0x52961305800f8b47270,0x2020d81c1c34703d0618,0xb83410f47041520a2042,0x84401521]]
set_option maxRecDepth 16000 in
def g251H10 := limbs80 #[#[0x10680024480001c2416,0x180003034000b2080400,0x2c000401018460000000,0xc002900064002d000,0x800008262b020c83e040,0x21802010021d1a0200e0,0x1400020342e09100280,0x8000409010040c150200,0xe918000b11000180232,0x2000401401268700405,0x6630048400a020789c44,0x7c402f0281470223186c,0x2018120c0400400041e0,0x63f8002a4f220544c060,0xa120e8b00c3800004040,0x1031940404250580,0xf83a00020446c051ba4,0x20000020118144260904,0x1702824020308000060e,0x4c0346004140e1780c10,0x18362e028040e0b080dc,0x8a432040000c000a008,0x65803010001112454190,0xc2670808de00020000a1,0xc00280582ca00d15004a,0x34020c88820431686,0x661936800040605,0x6010180401298100e17,0x2f0b0080603029042a,0x22a22824001721000,0xad00814000180e90118,0x41b984040200090a8060],#[0x6fd050a000080b018324,0x40605118553c3c06809b,0x8241e1b082ac8596032f,0x1298cac0008060016118,0x635cc00003e00808025d,0x837e00016462f960829e,0x1a8bb845f64b92d96975,0x50b4555d1c2d72040239,0xaf726ce0ca1c0000065d,0x7c445e1db126a66d9300,0x175c06d45ab2959cc1,0xd2dc5aefb7d0c3e31860,0x291d638a45e5b8ab057,0x29402cdcc2788e000000,0xa7ae21c20003daa29543,0xbdc2ed45ae5a5e9e04b4,0x57b2b5d475fc42518e88,0x79a9034c08a9911a2828,0x5bbd2a60963f92c06f30,0x6e27e3df86f980caaa19,0x5ad6b05648265a098926,0x4510d9ab8186e0003fd2,0x54e84cb182285758a8b7,0x9a46aa0001979e1e81,0x9399ed13392ff331e02a,0x84880de1d75b38f6eca9,0x7d8b5410082f82d963f2,0xf2947928d5041ad9c71e,0x3fbbfff94215c9943c2,0xdd69370b0a1394a5b263,0x69f43a915b338cbe7d4c,0xc17fa7e062c8f95cb219],#[0x3ba151ab8753885b258d,0xaace1b0bee251dd56d63,0xafecb4f8681004fc9425,0x6614c72a24de15a53b73,0xacb041922f091c9ad4e5,0x4d3c6475de000000002d,0x28a62b25ba604f19b052,0xa000004b6b81a13cee7b,0x6a5e47b91e727b00004b,0x934492f043fd89e623f2,0x830e0392cc0e9d89145c,0x58ae3315cb7466710fc4,0x22299d210bd547c3e4f8,0xbfef6a5561448e1edd81,0xce81990f6319b03ba84,0x85e0508800029cdbb59c,0xaa31b9607d5f4a7068c7,0x1cf108d8434775,0x8000a5fdc6ac12ade800,0xc00030526550684118b,0x4e0001e464591000062,0x82be1282000000026175,0x8c5bbeab301f780aa0dd,0x6bbcb630b88a500175d3,0x60d3a3bc80e800069bc9,0x4c000715a95d3e0242ff,0x9ea0ed00005b6f1561aa,0x1a020001f86bc9700000,0x74000724b97000933084,0x27c00000006cd2f6d030,0x228b4064610000007604,0xb400008b23af0675bd9e],#[0x63fb2285a3c9e61c4ebb,0xc9df01089a36d8c00002,0x1bcffc9766ae22b02067,0xed269d5834ae7eb02589,0x7b96a099207780a4,0x180001885332e0000000,0x59b83c2a23800016f0c7,0x616de330000118c907e7,0x915a410f1e3b2c042c61,0xcf6c62fe2afa0a53434d,0x9bf639c2d471c49e48d,0x6a15cc63459685118000,0x91d6eb50c85b08597b0b,0xef8a621cc74800000000,0xa31437c8f5176a694719,0x333c59817bb3937709a9,0xb5b871000025c5d28ee,0x840000b0c41e545f8da7,0xbed290882b7b24c4f2c5,0xf2ac532681c800071235,0x76ce9f2349d380002d5a,0x6e1cc0e8cea09ff51449,0x298c7578e1bc20844d1b,0x43f87500831a44cf980a,0x98124ac45a800057296b,0xff65358822c3483e0535,0x37bb10ba7a4258836ea6,0x37518db57dc390de02b1,0x887ac68a784e6a9320fe,0x2f57e000074f8bc77d60,0x5f0c4483db9f1a8efde0,0x817544e1ca8c9c88000d],#[0xf52f67205e9324dba026,0x4ade4f980002c51b9,0x845c8144c22303ba26a0,0xaaa35eb6d05341053167,0x6258b7c011a39a473f2e,0xd9eebb6d62fc52dd03f6,0x3c852187fc6127281d8e,0x9297e1fcee4a4a8d3aad,0x2b3215220003c7363169,0x26439d5a3e34ffa3c000,0x8a16408024cce50001b1,0xc343e707e03153d00002,0x4e42caae55150e3a1930,0xd330681e1f9055b2272d,0xdcc9850c000796f9,0xe6b119819e2f98367707,0xdd0a54b08ea09bd21301,0xff32354577e286ff9f86,0xe1985e9944b84f392662,0xeabdd83a57e107364,0xc10a99d4e4e73b880000,0xb38afe1e1129bb146c92,0x6eab6e6f8109f0c3a3eb,0xe1c7749e2e960c733bbe,0x1521e62c9db6176d21c3,0xa3a53ec4b2d41119026,0x4c64e12e0002c9a00000,0xc4b7b0000d2380000111,0x5dc2230000001a711420,0x6f5ab46520c000000005,0x9511df673e00a65925ac,0xca85e9c8f96064725bec],#[0x800048a4659d073c0609,0xd60933a6c902f365c538,0xbc60002156bd0506d488,0x9b49b7630eb2968f0429,0x7bcec386b204b8ce7017,0x3d4206d30ae095000189,0xb34c696639f193be85c1,0x61ae546966435452fdb0,0x656b98ddabe3a018707d,0x14ef0db39afb5f6,0xdaed2d962842f6324000,0x4724a0748d8000e3fd4e,0x4f29db4712314f9ef9,0x1d995000000014a8423f,0x5fbfba6c950815c5aae0,0x6173d49140d963061929,0xd8af2e1308e338e88000,0x2a0cb8348d3b29402784,0xa0388292a2ba676403de,0x83eefd06a80692624b42,0x674f2b00d9f0e0071dec,0x69f71eafb9e55d446810,0xde8dba15e7b8d8874000,0x7679580493c13d21efec,0xc22752ba61a2119ad358,0xba9dc00000000654d01d,0x6b899ca4c50000230566,0x4688a4a400000000000e,0xa56dea9e69e089ba117,0x363f9ab8dec0c3442867,0x800000000089860aa607,0x40ee832a6c162d5ce675],#[0x3d6d11692b30811c5a4d,0x6b8f00000001b23e81ca,0x8780f000000000000000,0x33537040cfa0dce9e462,0x238db22de3e800058d64,0x16bc2fb81ac1935ec000,0x5c2c8a0e55e02cc32b65,0x82f400009268aafc157a,0x865640784b0a12e67c10,0x1cb887b800fe00018c,0xa071b6bdca2214000000,0xac0007c90d9765a5046e,0xe03ca533d00008c4079,0x79582,0x93152c099000046b0000,0x87a9da58e00ad34cc8b,0x8000c749f4e30d68a303,0x47db33b6000000001807,0xe8e5721954c98d000128,0x8000b098150c8a300002,0x9148405a36c70792c9d,0x46d0335966296cc5cc10,0xb84600010cd6b4d00001,0x4c90f2944ec76ab53510,0xf060000b2da39871d3c8,0x214c0000a7a7c4f4b426,0xa8a1ccc3aa0b8cc01,0xa8800007078be9e00,0x637fdc60bde04f2c9310,0xe5d8df9b0059662ad5b1,0xec0e99929d207913974,0xe4486861c75e126b13ad],#[0xfe87e40ef91c6000094b,0x67e35d55c9686e416d64,0xacba5585b2a995ff43b2,0x7c0000aa0219400010e2,0x3a78c400052620000bd,0x8000c2c0000000030b7c,0x507a3f89575e3a4c1b9,0x3e3a6aad0ad9a2f87da1,0x29f44760caac51ee84ee,0x3216f237aa773181081f,0x7618c0005a4e00012a,0x94c9548ba36897780007,0xc89a0525abc591235191,0x6f2992512fe34a946fcd,0x32195a68036cf0ca225d,0x2acf07583b05bd8ea5dd,0xd180002d6c8226ae72ab,0xf374ea9770c4aa4ee26f,0x3400058de6c14ee79c00,0x28018450b43a92f1222d,0xb4ae000097524dc4315a,0x186c22d000111fc3b0,0x5300003c5e8000266600,0xe1b90000acc2c77561d2,0x6ac8316382369bbf5f2e,0x5e3ecb7d3fd1a4874727,0xe86a2b6555c00078b48,0xd4031035d28fd12d502,0xe2265f7c67700054b26a,0x9458821a00000007deef,0xf2973800032dd45ad8fd,0x23d5a2d970000a101f5],#[0x6a000000e0f37668a577,0xa55d0b2735e1058d42c,0x16e722493b5a180eee,0x6e0f92f2783706334b50,0xc000049f9202ccaa8385,0x1e62eca86a390f453ffc,0xa165f1ab7a5a45c1015,0xb40005917b392623c000,0x6f9e21899a61296b5c81,0xb0e2b097a281c4a00007,0x5988fef9002f70a6c888,0x14b78ac12071cd0001cd,0x41ed636a03d90124956d,0x455d4ff0f000000016de,0x439f515072f231000030,0x430123eb466,0x60528e0c421c88c38506,0x4dfb2c5748bab6000102,0x5d580000e73df8f29658,0x630c5b1155ec33a4e73,0x3a1ce5c97fea418eacf3,0xc99e0000b6fa855300da,0xb0e30ab140001a99486b,0x6d8f12a55dd04ae45762,0x27135396aca2963f8c0b,0xb604e800000000003fd3,0x4e400028143610000039,0x30a9722000027190a7d2,0x9c1bdd0b8de3941d5075,0x5bac178ebcf1be34da49,0x2889447d6cc7338ae4cf,0xd4e49966c00000003b1f],#[0xf035d66121d87d90d9a7,0xd919740c000154480006,0x24d9000016fa6952ad0,0x586c117d522cad224200,0x114898bb84503bb680e8,0xda0315b2faa74228e522,0x62032e6cfb30cbec3fec,0xa018e627c20859659006,0x1984852ae4067c9d050f,0x3cf3d8ca4beb69730f15,0x1b9dd3f563b5a12a76a2,0xd80002a0e520b3e2072f,0xb98c862f8d80003248b9,0xa17a629c0bb400003ab5,0xa2881f3b54834b71547a,0x184000327e3c9746,0x3773161f6c2a27380000,0xf4000797402e1ac8a8b9,0xb7400008fe9a9652b283,0xae78435e6d2dad00a036,0xc48468000a70d0bab924,0x538774e4e4000076774a,0x14ef530683b2023bb8ce,0xbb54e9ddb1284e623583,0xbac49cc0006893320900,0x302c34491600008,0x582d26a950001e98c000,0x1d3d1d8f0000585a46]]
def g251D11 := limbs80 #[#[0x10f794fdd53fb98bed62,0xfd50ff503fd30ff483fd,0x87fd51ff4c7fd21ff583,0xf54ffd62ff54bfd32ff5,0x8423023000ff597fd63f,0xad133218394630a30f81,0x22f4107b4e91b33105c4,0x1610360e06001889a527,0x85840d8381800602200a,0x10514180e120a00147c6,0x1208220c000490384802,0x2868584001420461a16,0x6140e120800203470712,0x90715868583828104002,0x241c661a120a060c1400,0x51d85848281830d0006,0x584800d14161a1612005,0x6a1a120a0021381404a8,0x62103858482801f1c0c,0x480140c1a161200342c2,0x16120e06003408907868,0x8482800305080d1c801a,0x305062216120a0020386,0x848281800d8]]
set_option maxRecDepth 16000 in
def g251H11 := limbs80 #[#[0x233000201105200210,0x72b30001100002120003,0x620620202334126e2,0xf19000000005002,0xd7e0d04986a400000000,0x6,0x0,0x16ae0000000000000,0xdd278001d28484000727,0xabc6797d00038dc00005,0x82e25f800000004c18,0x240a00000000000000,0x10a0004b48,0x80c0000000000000,0x51e0000000000dcd,0x3c9,0x25309fc00092700,0x324800000000045100,0x410dcc9a180000000,0xe14b0ec0007413018000,0x2742407b8fa2a4164000,0x34da000000000,0xddf4a000b56800000000,0x183cb3a510132e2,0x1da7c33b00030f20,0x3020,0xf80000000004cb4000,0x470f04880000000006bd,0x121900000018a,0x4e0b4000043802a21e00,0x35980800000000019d1d,0x42c2b5000000223627b4],#[0x5ae80000000000000002,0x80006400005934000008,0x624b0002c7ac1a845898,0x145912f3a7ac3963,0x31dc000000e1d00,0xe9355000000000000000,0x69b24409c40000000007,0x9a4000000000000130e,0xe0000000000000caf000,0x75b40000006bba00213,0xe2100000000f000000,0x44a00000000000,0xcaa00000000000003710,0xc0c0000002,0x1c26000000391c000,0xd000021c000000d0b800,0x165a000022400147,0xc2a0001c4400000000,0x4800000000000002c300,0xf70e1fc94fc968270002,0x10500000005aa84e6,0x28c4001ca0000,0xad191c9400000028e000,0x109a851da00000a3051,0x88000000000000119c0,0x81400003080038fce24e,0x30bc,0x3a580000003234001e2b,0x4264000000000000,0x8c48c000000000000000,0x14440004493d3f5,0x11509c44100078240000],#[0x2970000001f0945f92ba,0x80000000000006a74000,0xe0008418000000000e37,0x783543,0xe50b01238001c8659c00,0x55b00028,0x128200026600000000,0x584e52bf0d1bad180,0x710000,0x80586d11e07a000116,0xab935fc00000,0xb89ccf0cdcf1900000,0x8e4000000eba00000000,0x5851d560000004,0x1b20000003ec8,0x0,0x5d2ceccdc6c628d4eecd,0x424c00000070,0x40480000000005c500,0x162e00000000000000,0x0,0xc928000000000,0x6f8b8000000000785800,0xe9d29af685,0x416c000000b2200,0xb3500000000,0x0,0x0,0xa528000000000000,0x28b400,0xf40da96d1a11800000,0xd580a100016080],#[0x14e80000000,0xe00f18c001c200000000,0x454508a00010b0000000,0x5fc0c88c000000000648,0x80017b30000000001a7,0x9f958800000000000071,0x368f9,0xa9000000030e00000000,0x80000000000000003903,0x19226b5]]
def g251D12 (j : Nat) := if j=0 then 0x305080c101003ff else 0
def g251H12 := limbs80 #[#[0xc280000000704000002,0x3440,0xa600000000000000,0x1c00020e000000000,0x581c0000000000000000,0x3e,0x38fd18000000,0x2400000214000000,0x30000000000000000000,0x35,0x3c800000000000000,0x0,0x7a40030c00000000000,0xb4800000000010b0000,0x893390c13c9000cd0000,0x42000000012]]
def g251L : Nat → Packing
  | 5 => (2,7,7,0,0,3,0,g251D5)
  | 6 => (75,6,7,0,0,10,0,g251D6)
  | 7 => (727,5,7,0,0,14,0,g251D7)
  | 8 => (1429,4,7,0,0,17,0,g251D8)
  | 9 => (957,3,7,0,0,17,0,g251D9)
  | 10 => (184,2,7,0,0,14,0,g251D10)
  | 11 => (20,1,7,0,0,11,0,g251D11)
  | 12 => (1,0,7,0,0,0,0,g251D12)
  | _ => emptyPacking
def g251I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 2 0 5 1 0 g251H6
  | 7 => lookupWord 22 137 6 12 7 1 g251H7
  | 8 => lookupWord 230 3413 4 15 10 1 g251H8
  | 9 => lookupWord 479 2843 6 16 11 1 g251H9
  | 10 => lookupWord 326 1489 9 15 10 1 g251H10
  | 11 => lookupWord 62 631 4 13 8 1 g251H11
  | 12 => lookupWord 6 127 1 10 5 1 g251H12
  | _ => fun _ => none
def g251 : Forest := ⟨251,12,fun i => g251Y[i]?.getD (0,0),g251C,g251A,g251L,g251I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P5_0 : CutRow g251 5 0 2 := by
  apply polarBlock (data:=fun _ => (word80 [0x400120024c0,0x21320044008944264220])) rfl
  decide +kernel
theorem g251B5 : CutRow g251 5 0 2 := g251P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P6_0 : CutRow g251 6 0 4 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P6_4 : CutRow g251 6 4 5 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P6_9 : CutRow g251 6 9 48 := by
  apply polarBlock (data:=fun _ => (word80 [0x410402,0x41041210004104024104,0x12300062220180822330,0x8080110a8c448420041,0x4012104123100410401,0x21041230040082012082,0x28210041040121041230,0x410402410412100041,0x4024104121000440181,0xc0644230044020082442,0x2a520400120104c02132,0x60220120820b530044,0x894426422000240101,0x80424163080000082482,0x486208080100a0424863,0x220402098021530808,0x100a042484308080100,0xa0424843002802012042,0x93200622400a0122342,0x400402410412400040,0x4024104124000400402,0x41041240004004024104,0x12400102020104902820,0x400402410412500040,0x4024104125000400402,0x41041250004004024104,0x12500040040241041250,0x400402410412600040,0x4024104126000220201,0x80820942004004024104,0x12600040040241041250,0x400402410412500040,0x4024104125000400402,0x41041250014021108c54,0xb60014021108c540b64,0x240401201241630400,0x820120c0284200208100,0xa0c00943010200090412,0x28430400000824422861])) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P6_57 : CutRow g251 6 57 18 := by
  apply polarBlock (data:=fun _ => (word80 [0x8020400,0xa0906053004104012104,0x12310041040121041230,0x44800090442a0520048,0x90442825404000201,0x20c02842040000082442,0x2842040000182c462862,0x220201808221430022,0x2018082213000220201,0x80822130004104024104,0x12100041040241041210,0x611402410413210022,0x2018082213000220201,0x8082212000440181c064,0x42300022020180822130])) rfl
  decide +kernel
theorem g251B6 : CutRow g251 6 0 75 := (@joinRow g251 6 0 9 66 (@joinRow g251 6 0 4 5 g251P6_0 g251P6_4) (@joinRow g251 6 9 48 18 g251P6_9 g251P6_57))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P7_0 : CutRow g251 7 0 2 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P7_2 : CutRow g251 7 2 48 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P7_50 : CutRow g251 7 50 48 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P7_98 : CutRow g251 7 98 31 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P7_129 : CutRow g251 7 129 48 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P7_177 : CutRow g251 7 177 48 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P7_225 : CutRow g251 7 225 5 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P7_230 : CutRow g251 7 230 48 := by
  apply polarBlock (data:=fun _ => (word80 [0x1403100,0x84500b41014032010490,0xb41040400502c546063,0x404000a044260630140,0x200884122a710802000a,0x4826063040400090442,0x6032100200512816a064,0x10040050a816c0640400,0x80082442286202203403,0x1201351022034030120,0x13510028020120840963,0x2203403012013510602,0x24020520323100611402,0x410413200400020120c0,0x28720400020120c02862,0x400020120c028620400,0x20120c0286204000008,0x24422862010202018090,0x28310102020300902851,0x1001101805009510102,0x90412285101020009,0x41228610408020300c0,0xa0430404004120506053,0x4040041205060530061,0x14024104132008001400,0x24904143080014002490,0x41430800140024904143,0x60a100a0c00b540443,0x4024104322004430402,0x41043220010202018090,0x28310102020180902831,0x611402410413201000,0x12010580814300611402,0x410413200048008a4426,0x82300061140241041310,0x48008a442682300400,0x20120c0287104040041,0x20506052010202018090,0x282000240442a1144173])) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P7_278 : CutRow g251 7 278 48 := by
  apply polarBlock (data:=fun _ => (word80 [0x8080012,0x884c0320800110024c0,0x41420800104024904142,0x80800c260b0c0320400,0x120104c0214301001200,0x84900941040400522816,0x60740040040241041270,0x400402410412600040,0x4024104126000400402,0x41041260004004024104,0x12600040040241041260,0x400120024c021420040,0x402410412700048008a,0x44268230002202018082,0x9640800110024c04142,0x208201208209640800,0x10402490414204080051,0x2816a074004404030104,0x42200044040301044220,0x2080112886490530060,0xa100a0420b200060a201,0x20820b20002400512816,0x41500044008944264250,0x60a100a0420b200020,0x8110a846095001020008,0x84122820006114024104,0x13310061140241041321,0x611402410413210140,0x21108c540b510060a100,0xa0420b10014021108c54,0xb70014021108c540b60,0x14021108c540b600440,0x20502c54236102203401,0x9201342010200088412,0x28200102000884122820,0x14021108c540b600104,0x1108c5448610104000a,0x41248610102000a0412,0x28611100108a40320961])) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P7_326 : CutRow g251 7 326 48 := by
  apply polarBlock (data:=fun _ => (word80 [0x400402,0x41041261004004024104,0x12710040040241041261,0x400402410412610040,0x4024104126100400402,0x41041271004004024104,0x12610040040241041261,0x208201208209500020,0x82012082091000208201,0x2082091000440181c064,0x426500208100a0420910,0x208100a04209101004,0x502d14c05301488203,0x848a30010000088412,0x28510041040241041220,0x40800522854a0630444,0xc06434425001001100,0x845009410408001a0c46,0xa0320024010180420954,0x208100a04209540400,0x10402450214204008200,0x24c02842020800190c26,0x9062040800c26070a032,0x240101804241640100,0x11008450094101020008,0x84122831080800c06832,0xc0540100110084500941,0x400402410412600040,0x4024104126000400402,0x41041260004004024104,0x12600048008a44268230,0x240101804209640020,0x8100a042096404001040,0x245021420400820024c0,0x28420024011288544173,0x400402410412700100,0x12008490094100410402,0x410412500400120024c0,0x2142004400c160344220])) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P7_374 : CutRow g251 7 374 48 := by
  apply polarBlock (data:=fun _ => (word80 [0x1020201,0x4902841100202008580,0xa0430061140241041320,0x100200088502a0630104,0x1008450485101040100,0x84504861010401008450,0x4851020800188c269062,0x80800088482c0630104,0x1008450485100611402,0x41041320100400088502,0xc0630443040241043220,0x4001040245021430808,0x180c862c0540048008a,0x442682300048008a4426,0x82300024004120122164,0x220040a01221640040,0x4024104126000400402,0x41041260004004024104,0x12700102020104902840,0x1040100845048500808,0x180c862c05400208201,0x208209200404001a0c46,0x605400200040a0122160,0x200040a01221600020,0x40a012216000200040,0xa012216000200040a012,0x216000200040a0122160,0x200100a04209600020,0x100a042096000208201,0x208209200408001a0c46,0x606500200040a0122150,0x410402410412410808,0x120884485400440401,0x21044241044400886426,0x42510040040241041261,0x400402410412610040,0x4024104125100400402,0x41041261004004024104,0x12710040040241041261])) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P7_422 : CutRow g251 7 422 48 := by
  apply polarBlock (data:=fun _ => (word80 [0x410402,0x4104125000440181c064,0x42300104000904124831,0x611402410413200061,0x14024104132000611402,0x41041310040400090442,0x60320061140241041310,0x20801108c6490520404,0x90442607308000100,0xa0c04873010401018050,0x48310140310084500b41,0x440181c06442600220,0x34020920135100440089,0x44264230022034020920,0x13510220340209201350,0x20801108c6490510602,0x24030120325104403401,0x5402343004104024104,0x12200041040241041220,0x4001401054021431004,0x1108d44c05304001401,0x5402143100401108d44,0xc0530041040241041220,0x8001400858041430800,0x14008580414300410402,0x41041220004104024104,0x12200041040241041220,0x4430402410432200041,0x4024104122010001200,0x85808143006224028102,0x23540024004120122164,0x220040a01221640800,0x14002490414304403400,0x2450234208080100a042,0x485408080100a0424854,0x4430402410432100208,0x190c26906204080009,0x442a063010202010490,0x28510102020104902851])) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P7_470 : CutRow g251 7 470 48 := by
  apply polarBlock (data:=fun _ => (word80 [0x240101,0x80424170080000082482,0x48740800000824824864,0x8000008248248640060,0x2110a8460b6000602110,0xa8460b60002202018082,0x21300022020180822130,0x220201808221300048,0x894426825100220201,0x80822130002202018082,0x2130100021108d448276,0x400402410412610040,0x4024104126100400402,0x41041251004004024104,0x12510040040241041251,0x400402410412710040,0x4024104126100240101,0x80424170080000082482,0x48730208011288649052,0x440181c06442400140,0x320104900b5100440089,0x44264230080010502c94,0x41530022040180822140,0x220201808221300220,0x34030120134200220201,0x80822130002202018082,0x21300220340109201352,0x440089442642650022,0x40a012213004402201,0x20c02a6200440181c064,0x42300400120104c02143,0x4040009044260530041,0x4024104122000410402,0x410412200400120104c0,0x2143080801108cc4c053,0x400120104c021430808,0x1108cc4c05300410402,0x410412200800110084c0,0x41430041040241041250])) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P7_518 : CutRow g251 7 518 48 := by
  apply polarBlock (data:=fun _ => (word80 [0x602110,0xa8460b60006222018082,0x23300104001a0c164852,0x200100a04209600020,0x100a042096000200100,0xa042096000200100a042,0x96000602100a0420b60,0x220201808221300041,0x4024104122000220442,0xa1122130002202018082,0x21300400120104c02173,0x1020201049028510808,0x120884c04308080112,0x88c4c043004104024104,0x12200041040241041220,0x410402410412510041,0x4426114124100410402,0x41041241004104024104,0x12400041040241041241,0x410402410412400102,0x2010490283100410402,0x4104124000602110a846,0xb6000220040a0122140,0x220040a01221400041,0x4024104125108008018,0x2c86485400622400a012,0x233000622400a0122330,0x622400a01223300061,0x14024104132100622201,0x80822330004104024104,0x12210041040241041221,0x410402410412100022,0x2018082213000220201,0x80822130002202018082,0x21300022020180822130,0x220201808221300041,0x4024104121000410402,0x41041210080800182c86,0x4853080800182c864853])) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P7_566 : CutRow g251 7 566 48 := by
  apply polarBlock (data:=fun _ => (word80 [0x410402,0x40861220020801108c64,0x90520102020180902831,0x440320104c023430140,0x320104900b4108001110,0x8cc441430408020104c0,0xa0530061140241041320,0x1020009041228610060,0x2110a8460b6001402110,0x8c540b6100602110a846,0xb6000602110a8460b60,0x602110a8460b600060,0x2110a8460b7000410402,0x41041221004104024104,0x12100041040241041221,0x410402410412210060,0x2110a8460b6000410402,0x41041210002202018082,0x21300022020180822130,0x220201808221300022,0x2018082213000410402,0x41041221002202018082,0x21300022020180822130,0x410402410412100062,0x22018082233000602100,0xa0420b7000602100a042,0xb6000602100a0420b60,0x2080012082490420022,0x201808221200208001a,0xc269041002202018082,0x21300061140241041321,0x220201808221200061,0x14024104132004001201,0x4c021630800110084c0,0x41630400120104c02162,0x200100a04209600041,0x4024104121000602110,0xa8460b60002204028102,0x21400022020180822140])) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P7_614 : CutRow g251 7 614 48 := by
  apply polarBlock (data:=fun _ => (word80 [0x410402,0x4104121008080110a8c4,0x485408080110a8c44854,0x240101804241400028,0x2012082094004008018,0x2c4628530400801a0c46,0x2853020800190c269053,0x4000008244228730400,0x82442286304000008,0x24422863040000082442,0x28630400000824422862,0x622201808223500102,0x90412286201020009,0x4122852040014030140,0x21430400000824422873,0x400402410412610040,0x4024104126100400402,0x41041261004004024104,0x12610062220180822330,0x60a20120820b100102,0x90412286108080112,0x88c44154080800522894,0x41540808011288c44154,0x148820104848a500102,0x2018090283101020201,0x809028310400020120c0,0x28620041040241041220,0x4040401054060430041,0x4024104122000410402,0x41041220004104024104,0x12200061140241041320,0x1020201809028310102,0x2018090283104000018,0x2c462872100010502d14,0x81540408000a0442a043,0x611402410413200061,0x14024104132000611402,0x41041310006114024104,0x13100061140241041310])) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P7_662 : CutRow g251 7 662 48 := by
  apply polarBlock (data:=fun _ => (word80 [0x208401,0x21020970006801128046,0x81600100120300900951,0x1001202409009310404,0x90442604300410402,0x410412100400820120c0,0x28530062240280122330,0x4403052085423420044,0xc16034423001000201,0x80902861010012030090,0x9410400120300c02143,0x1020008841228310400,0x80082442286200602110,0xa8460b600400020120c0,0x286200602050a8162360,0x1000201809028610041,0x4024104122100410402,0x4104121000602110a846,0xb600041040241041210,0x410402410412100408,0x20300c0a04300240403,0x1024140010401108c54,0x48510020020120820960,0x410402410412200041,0x4024104123100410402,0x41041231004104024104,0x12200041040241041220,0x410402410412200408,0x20300c0a0430408000a,0x442a043004104024104,0x12200041040241041220,0x410402410412200041,0x4024104122000240041,0x20124140002401018042,0x41400062220180822330,0x240401201241400024,0x1118846414000622201,0x80822330006114024104,0x13210041040241041210])) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P7_710 : CutRow g251 7 710 17 := by
  apply polarBlock (data:=fun _ => (word80 [0x80204028180,0x60640041040241041240,0x410402410412410041,0x4024104124000410402,0x41041221004104024104,0x1210080800182c864854,0x8080110a8c448540808,0x110a8c4485400410401,0x21041241004104012104,0x12410041040121041241,0x410401210412410020,0x82012082095000208201,0x20820940002084012102,0x9700020820120820940])) rfl
  decide +kernel
theorem g251B7 : CutRow g251 7 0 727 := (@joinRow g251 7 0 326 401 (@joinRow g251 7 0 129 197 (@joinRow g251 7 0 50 79 (@joinRow g251 7 0 2 48 g251P7_0 g251P7_2) (@joinRow g251 7 50 48 31 g251P7_50 g251P7_98)) (@joinRow g251 7 129 96 101 (@joinRow g251 7 129 48 48 g251P7_129 g251P7_177) (@joinRow g251 7 225 5 96 g251P7_225 (@joinRow g251 7 230 48 48 g251P7_230 g251P7_278)))) (@joinRow g251 7 326 192 209 (@joinRow g251 7 326 96 96 (@joinRow g251 7 326 48 48 g251P7_326 g251P7_374) (@joinRow g251 7 422 48 48 g251P7_422 g251P7_470)) (@joinRow g251 7 518 96 113 (@joinRow g251 7 518 48 48 g251P7_518 g251P7_566) (@joinRow g251 7 614 48 65 g251P7_614 (@joinRow g251 7 662 48 17 g251P7_662 g251P7_710)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_0 : CutRow g251 8 0 48 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_48 : CutRow g251 8 48 48 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_96 : CutRow g251 8 96 48 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_144 : CutRow g251 8 144 39 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_183 : CutRow g251 8 183 48 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_231 : CutRow g251 8 231 48 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_279 : CutRow g251 8 279 48 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_327 : CutRow g251 8 327 48 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_375 : CutRow g251 8 375 48 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_423 : CutRow g251 8 423 48 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_471 : CutRow g251 8 471 48 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_519 : CutRow g251 8 519 48 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_567 : CutRow g251 8 567 48 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_615 : CutRow g251 8 615 48 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_663 : CutRow g251 8 663 48 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_711 : CutRow g251 8 711 48 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_759 : CutRow g251 8 759 34 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_793 : CutRow g251 8 793 48 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_841 : CutRow g251 8 841 48 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_889 : CutRow g251 8 889 48 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_937 : CutRow g251 8 937 32 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_969 : CutRow g251 8 969 48 := by
  apply polarBlock (data:=fun _ => (word80 [0x611402,0x41041331006114024104,0x13210061140241041321,0x1020008841228310208,0x120824905201402110,0x8c540b710060a100a042,0xb100404004120506043,0x1020201809028310102,0x2018090283108002402,0x9804264080800120884,0xc0540220340209201362,0x280052281681500220,0x34030120136204403050,0x2c542373014031028050,0xb610404040301406043,0x4040403014060430140,0x310084500b6101403102,0x80500b61040400412050,0x6043014031108c540b71,0x1040009041248410102,0x88412283101020008,0x84122831010202018090,0x28310102020180902831,0x10001201058081650602,0x2402052032510300a402,0x5201a510808000a0482,0xc0540808000a0482c054,0x808000a0482c0540808,0xa0482c05400611402,0x410413200048008a4426,0x82500102020180902831,0x408020300c0a0530408,0x20300c0a05301403101,0x80500b61014031018050,0xb610800144225904164,0x40800c26070a0530048,0x8a442682500808000a,0x482c054006114024104,0x13200048008a44268250])) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_1017 : CutRow g251 8 1017 48 := by
  apply polarBlock (data:=fun _ => (word80 [0x208100,0xa0420910004104024104,0x12200041040241041220,0x40800522854a0530800,0x110084c0416401001100,0x84500961010200088412,0x2831040800c26070a053,0x480203008482500800,0x110084c0416401001100,0x84500961010200088412,0x2831004400c160344240,0x410402410412200808,0x120884c05404040009,0x4426043010400090412,0x4841080800c260b0c054,0x480182c06482500400,0x120104c0216304040009,0x4426043010012010490,0x9610104000904124841,0x440403010442400044,0x4030104424001402110,0x8c540b81044304024104,0x32310060a100a0420b20,0x208110a84609200443,0x402410432310060a100,0xa0420b200060a2012082,0xb200404004120506054,0x4040041205060540404,0x41205060540060a110,0xa8460b60044304024104,0x32310443040241043231,0x611402410413310061,0x14024104133100611402,0x41041331010202018090,0x28420102020180902842,0x1020201809028420061,0x1402410413310808000a,0x482c065006114024104,0x13310061140241041331])) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_1065 : CutRow g251 8 1065 48 := by
  apply polarBlock (data:=fun _ => (word80 [0x408001a,0xc46a0640408001a0c46,0xa084040400190c466054,0x410402410412311002,0x188d06a07500208100,0xa042092000208100a042,0x92000208100a0420920,0x208201208209200041,0x4024104126100410402,0x410412610408001a0c46,0xa05300208100a0420960,0x220040a01221300808,0x120884c05400240041,0x20124140002082012082,0x92000208100a0420920,0x208201208209200020,0x82012082092000208100,0xa042092000208100a042,0x9200020820120820920,0x208100a04209200020,0x8100a042092000208201,0x20820920004004024104,0x12710040040241041271,0x400402410412710020,0x8100a042097000220040,0xa0122130002082012082,0x9700024004120124140,0x4430402410432310020,0x82012082092000208201,0x20820920044304024104,0x323100440181c0644281,0x208100a04209200020,0x8100a042092000208100,0xa042092000208100a042,0x92000208100a0420920,0x208100a04209200044,0x4030104424100440403,0x104424108002180c8e0,0x427400208100a0420910])) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_1113 : CutRow g251 8 1113 48 := by
  apply polarBlock (data:=fun _ => (word80 [0x410402,0x41041220040400090442,0x60430041040241041220,0x410402410412200044,0x181c064424000611402,0x41041320040400090442,0x60430061140241041320,0x1040101805048410142,0x200884122a3100440181,0xc0644240022034020920,0x13710041040241041220,0x808001a0c86c0540041,0x4024104122004403402,0x5402363004104024104,0x12200041040241041220,0x410402410412200443,0x4024104322008001040,0x24904164040010402450,0x21630061140241041320,0x408000a0442a0530443,0x402410432200808000a,0x482c054004802030084,0x825000480182c0648250,0x8001040249041640400,0x10402450216300440403,0x1044251080800120884,0xc0650020820120820920,0x4040403014060540808,0x120884c05408080012,0x884c065002082012082,0x920080800522894c054,0x440403010442510020,0x82012082092008080052,0x2894c05400200040a012,0x216000208100a0420920,0x208100a04209200443,0x4024104323100410402,0x41041231040404030140,0x60540408001a0c46a064])) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_1161 : CutRow g251 8 1161 48 := by
  apply polarBlock (data:=fun _ => (word80 [0x4400c1,0x60344251080080082482,0x4864004400c160344251,0x220201808221400048,0x8a4426826100611402,0x41041331080800120884,0xc0650808000a0482c065,0x80800c260b0c0650048,0x2030084826100208100,0xa04209200048008a4426,0x826100220040a0122140,0x220201808221300022,0x2018082213000220201,0x808221300048008a4426,0x82610800000824824884,0x220201808221400022,0x2018082214000611402,0x41041331004004024104,0x127100220040a0122140,0x220040a01221400048,0x8a4426826100400402,0x41041281002202018082,0x21400040040241041281,0x220050a81621300061,0x14024104133100611402,0x41041331002204028102,0x21400022040281022140,0x220402810221400044,0x894426427100220040,0xa012214000220040a012,0x214000220040a0122140,0x220040a01221400220,0x34020920137208002402,0x9804274080800120884,0xc0540220340301201362,0x100020884d2282750800,0x20884ca2427400220040,0xa0122130002202018082,0x21300800000824824884])) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_1209 : CutRow g251 8 1209 48 := by
  apply polarBlock (data:=fun _ => (word80 [0x410402,0x41041220006114024104,0x13310022020180822140,0x2080012082490530208,0x1a0c26905200440403,0x1044251004104024104,0x12200041040241041231,0x622201808223400041,0x4024104123108080012,0x884c065004104024104,0x12200041040241041231,0x410442611412210041,0x4024104122100410402,0x41041220006224028102,0x23400041040241041231,0x220201808221400041,0x4024104123108080012,0x884c065080800120884,0xc0650022020180822140,0x80800120884c0540022,0x2018082214008080012,0x884c065002202018082,0x21400022040281022140,0x220201808221400044,0x4030104425100220201,0x80822140002204028102,0x21400022020180822140,0x410402410412200041,0x4024104122000410402,0x41041220004104024104,0x12200808001a0c86c054,0x808001a0c86c0540022,0x40a012214000220201,0x80822130002202018082,0x21300800000824824884,0x410402410412610041,0x4024104126100410402,0x4104123100220040a012,0x214000220040a0122140])) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_1257 : CutRow g251 8 1257 48 := by
  apply polarBlock (data:=fun _ => (word80 [0x408001a,0xc46a054002401018042,0x41600024011188464150,0x4430402410432310061,0x14024104133100622201,0x808223400060a2012082,0xb200408000a0442a064,0x240111884641400408,0x20300c0a05400611402,0x41041331040800c26070,0xa0640060a20120820b20,0x40800c26070a0540443,0x4024104323100208201,0x208209200048008a4426,0x82610400000824422883,0x48008a442682510040,0x4024104127100220201,0x80822140002400412012,0x41800048008a44268261,0x400402410412810048,0x8a4426825100240101,0x80424170002401118846,0x41400024005128164140,0x4000008244228830041,0x4024104122004430402,0x41043220004104024104,0x12200061140241041320,0x611402410413200061,0x14024104132000410402,0x41041220010202018090,0x28310440320104c02363,0x140320104900b610062,0x24028102234000622402,0x81022340006224028102,0x23400062240281022340,0x4400c1603442510104,0x190c1648520808000a,0x482c065004104024104,0x12310062220180822340])) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_1305 : CutRow g251 8 1305 48 := by
  apply polarBlock (data:=fun _ => (word80 [0x240051,0x281641500060a2012082,0xb200041040241041220,0x408000a0442a0640041,0x4024104122000410402,0x41041220004104024104,0x12200041040241041220,0x100401118944c0651004,0x512914c06510040111,0x8944c065014882030084,0x8a510024010180424150,0x410402410412310062,0x22018082234000410402,0x41041220004104024104,0x12200041040241041231,0x410402410412310041,0x4024104122000240403,0x1024150002404030102,0x41500041040241041231,0x410402410412200041,0x4024104123100410402,0x41041231044304024104,0x32310041040241041231,0x142200884122a420041,0x4024104122000410402,0x41041220002802030082,0x81500041040241041231,0x410402410412200020,0x82012082092004000008,0x24422883002400412012,0x41500024004120124150,0x220201808221400024,0x41201241800060a201,0x20820b20004104024104,0x12200041040241041220,0x40080182c4628630400,0x80082442286304430402,0x41043221002404030102,0x41500041040241041220])) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_1353 : CutRow g251 8 1353 48 := by
  apply polarBlock (data:=fun _ => (word80 [0x410402,0x41041221004104024104,0x12210440a00824422a63,0x440181c06442410022,0x2018082213000220201,0x808221300808001a0c86,0xc0650808001a0c86c065,0x142200884122a420044,0x181c064425100220201,0x80822140002202018082,0x21400404000904426054,0x410402410412200808,0x11288c4c06508080052,0x2894c0650808011288c4,0xc0650148820300848a61,0x1020201809028420102,0x2018090284201020201,0x80902842006224028102,0x23400102020180902842,0x1020201809028420028,0x5228168160004400c1,0x6034425100440181c064,0x425100440181c0644251,0x440181c06442510041,0x4024104122104008018,0x2c4628630440a0182c46,0x2a6300440181c0644241,0x4400c1603442510060,0xa100a0420b20004400c1,0x60344251002204028102,0x21400104000904124852,0x4040009044260430061,0x14024104132104040009,0x4426043006114024104,0x13210102000884122831,0x2203402092013620024,0x1018042415000240403,0x1024150002401118846,0x41500062220180822340])) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_1401 : CutRow g251 8 1401 28 := by
  apply polarBlock (data:=fun _ => (word80 [0x410402,0x41041220080800120884,0xc0650024040301024150,0x240403010241500024,0x4432112415000240403,0x1024150080800120884,0xc065080800120884c065,0x80800120884c0650808,0x120884c0650808001a,0xc86c065080800522894,0xc0650148820300848a61,0x410402410412310041,0x402410412200808001a,0xc86c0650808011288c4,0xc065080800522894c065,0x808011288c4c0650148,0x820300848a6100410402,0x41041251004104024104,0x12510041040241041251,0x410442611412510041,0x4024104125100410402,0x41041251004104024104,0x12210041040241041221])) rfl
  decide +kernel
theorem g251B8 : CutRow g251 8 0 1429 := (@joinRow g251 8 0 711 718 (@joinRow g251 8 0 327 384 (@joinRow g251 8 0 144 183 (@joinRow g251 8 0 48 96 g251P8_0 (@joinRow g251 8 48 48 48 g251P8_48 g251P8_96)) (@joinRow g251 8 144 87 96 (@joinRow g251 8 144 39 48 g251P8_144 g251P8_183) (@joinRow g251 8 231 48 48 g251P8_231 g251P8_279))) (@joinRow g251 8 327 192 192 (@joinRow g251 8 327 96 96 (@joinRow g251 8 327 48 48 g251P8_327 g251P8_375) (@joinRow g251 8 423 48 48 g251P8_423 g251P8_471)) (@joinRow g251 8 519 96 96 (@joinRow g251 8 519 48 48 g251P8_519 g251P8_567) (@joinRow g251 8 615 48 48 g251P8_615 g251P8_663)))) (@joinRow g251 8 711 354 364 (@joinRow g251 8 711 178 176 (@joinRow g251 8 711 82 96 (@joinRow g251 8 711 48 34 g251P8_711 g251P8_759) (@joinRow g251 8 793 48 48 g251P8_793 g251P8_841)) (@joinRow g251 8 889 80 96 (@joinRow g251 8 889 48 32 g251P8_889 g251P8_937) (@joinRow g251 8 969 48 48 g251P8_969 g251P8_1017))) (@joinRow g251 8 1065 192 172 (@joinRow g251 8 1065 96 96 (@joinRow g251 8 1065 48 48 g251P8_1065 g251P8_1113) (@joinRow g251 8 1161 48 48 g251P8_1161 g251P8_1209)) (@joinRow g251 8 1257 96 76 (@joinRow g251 8 1257 48 48 g251P8_1257 g251P8_1305) (@joinRow g251 8 1353 48 28 g251P8_1353 g251P8_1401)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_0 : CutRow g251 9 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_1 : CutRow g251 9 1 27 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_28 : CutRow g251 9 28 48 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_76 : CutRow g251 9 76 48 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_124 : CutRow g251 9 124 48 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_172 : CutRow g251 9 172 48 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_220 : CutRow g251 9 220 48 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_268 : CutRow g251 9 268 48 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_316 : CutRow g251 9 316 48 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_364 : CutRow g251 9 364 48 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_412 : CutRow g251 9 412 48 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_460 : CutRow g251 9 460 44 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_504 : CutRow g251 9 504 48 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_552 : CutRow g251 9 552 48 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_600 : CutRow g251 9 600 48 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_648 : CutRow g251 9 648 48 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_696 : CutRow g251 9 696 48 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_744 : CutRow g251 9 744 48 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_792 : CutRow g251 9 792 48 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_840 : CutRow g251 9 840 48 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_888 : CutRow g251 9 888 13 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_901 : CutRow g251 9 901 30 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_931 : CutRow g251 9 931 26 := by
  apply polarBlock (data:=fun _ => (word80 [0x41040241041231,0x410402410412310041,0x4024104123100410442,0x61141231004104024104,0x12310041040241041231,0x10200188c1628420141,0x844261141a3101418442,0x61141a31004104024104,0x12310041040241041231,0x10200188c1628420102,0x88412284200410402,0x41041231044304024104,0x32310041040241041231,0x1040009041248520041,0x4024104123100410402,0x41041231010400090412,0x48520208001208249063,0x410402410412310041,0x402410412310060a110,0xa8460b200060a110a846,0xb200208001208249063])) rfl
  decide +kernel
theorem g251B9 : CutRow g251 9 0 957 := (@joinRow g251 9 0 460 497 (@joinRow g251 9 0 172 288 (@joinRow g251 9 0 28 144 (@joinRow g251 9 0 1 27 g251P9_0 g251P9_1) (@joinRow g251 9 28 48 96 g251P9_28 (@joinRow g251 9 76 48 48 g251P9_76 g251P9_124))) (@joinRow g251 9 172 144 144 (@joinRow g251 9 172 48 96 g251P9_172 (@joinRow g251 9 220 48 48 g251P9_220 g251P9_268)) (@joinRow g251 9 316 48 96 g251P9_316 (@joinRow g251 9 364 48 48 g251P9_364 g251P9_412)))) (@joinRow g251 9 460 284 213 (@joinRow g251 9 460 140 144 (@joinRow g251 9 460 44 96 g251P9_460 (@joinRow g251 9 504 48 48 g251P9_504 g251P9_552)) (@joinRow g251 9 600 48 96 g251P9_600 (@joinRow g251 9 648 48 48 g251P9_648 g251P9_696))) (@joinRow g251 9 744 144 69 (@joinRow g251 9 744 48 96 g251P9_744 (@joinRow g251 9 792 48 48 g251P9_792 g251P9_840)) (@joinRow g251 9 888 13 56 g251P9_888 (@joinRow g251 9 901 30 26 g251P9_901 g251P9_931)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P10_0 : CutRow g251 10 0 9 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P10_9 : CutRow g251 10 9 48 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P10_57 : CutRow g251 10 57 48 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P10_105 : CutRow g251 10 105 7 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P10_112 : CutRow g251 10 112 48 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P10_160 : CutRow g251 10 160 24 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B10 : CutRow g251 10 0 184 := (@joinRow g251 10 0 105 79 (@joinRow g251 10 0 9 96 g251P10_0 (@joinRow g251 10 9 48 48 g251P10_9 g251P10_57)) (@joinRow g251 10 105 7 72 g251P10_105 (@joinRow g251 10 112 48 24 g251P10_112 g251P10_160)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P11_0 : CutRow g251 11 0 4 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P11_4 : CutRow g251 11 4 16 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B11 : CutRow g251 11 0 20 := (@joinRow g251 11 0 4 16 g251P11_0 g251P11_4)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P12_0 : CutRow g251 12 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B12 : CutRow g251 12 0 1 := g251P12_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251T : mixedTables g251 12 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g251 0 0
  · exact mixedEmpty g251 1 0
  · exact mixedEmpty g251 2 0
  · exact mixedEmpty g251 3 0
  · exact mixedEmpty g251 4 0
  · exact g251B5
  · exact g251B6
  · exact g251B7
  · exact g251B8
  · exact g251B9
  · exact g251B10
  · exact g251B11
  · exact g251B12
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251G : graphValid g251 (boundsBefore K249) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low251 : Lower true (varsX 251) (graphGoal 251) 13 := mixedLower (g:=g251) (i:=0) (hints:=65603) (before_sound K249 V249) g251G g251T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K251 := extendKnown K249 13 [(251,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V251 : Known true K251 := extend_ok (m:=251) V249 low251 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255R : Impossible true graph 13 sevenInputs.toFinset := by
  change Impossible true (graphGoal 255) 13 sevenInputs.toFinset
  exact cut_root (m:=255) (before_sound K251 V251) (4, 0, 251, 0, 13) (by decide +kernel) (by decide +kernel)

end PEqualNP.Outside.L_meta_51786

open PEqualNP.Outside.L_meta_51786 in
theorem PEqualNP.Outside.L_meta_51786 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o fit _ correct
  exact replaceShort g255R gates o fit correct

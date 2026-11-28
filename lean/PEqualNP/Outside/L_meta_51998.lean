import PEqualNP.Defs

-- The two-mode live-state and cofactor checker follows L_meta_1674 and L_meta_670.
-- The graph, restrictions and all search certificates below are for L_meta_51998.

-- Shared forest and cofactor certificates from L_meta_1674 and PR 11111 for L_meta_1677.
-- The original credit line is retained below. The two root certificates here cover the unpinned graph.

-- The checker and the bound certificates are adapted from PEqualNP/Outside/L_meta_1667.lean (Apache-2.0).
-- Two modes: u=false are monotone runs (AND, OR); u=true are runs up to complement, where negation is free.
namespace PEqualNP.Outside.L_meta_51998
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
def graph : Sig := (BitVec.ofNat 512 (word80 [0xffffffff,0xfffffffeffffffffffff,0xfffafffffffefffffffe,0xfffffefefefaeca0ffff,0xfffffffffffeffffffff,0xfffffffafffffffeffff,0xfffefffffefefefaeca0]))
def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 2) || (x 1 && x 3) || (x 0 && x 4) || (x 2 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 2 && x 5) || (x 4 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 4 && x 6) || (x 0 && x 7) || (x 2 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 5 && x 7)
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
  (x 0 &&& x 2) ||| (x 1 &&& x 3) ||| (x 0 &&& x 4) ||| (x 2 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 2 &&& x 5) ||| (x 4 &&& x 5) ||| (x 0 &&& x 6) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 0 &&& x 7) ||| (x 2 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7)
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
  (x 0 &&& x 2) ||| (x 1 &&& x 3) ||| (x 0 &&& x 4) ||| (x 2 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 2 &&& x 5) ||| (x 4 &&& x 5) ||| (x 0 &&& x 6) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 0 &&& x 7) ||| (x 2 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7)
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



def target (x : Fin 8 → Bool) : Bool := decide (∃ i < ([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
def smallCircuit : Circuit := ⟨[⟨.or,[0,4]⟩,⟨.or,[2,8]⟩,⟨.or,[1,3]⟩,⟨.or,[9,10]⟩,⟨.or,[3,5]⟩,⟨.or,[1,7]⟩,⟨.or,[5,7]⟩,⟨.and,[13,12]⟩,⟨.and,[6,11]⟩,⟨.and,[8,2]⟩,⟨.and,[4,0]⟩,⟨.and,[14,9]⟩,⟨.or,[15,16]⟩,⟨.or,[20,17]⟩,⟨.or,[21,18]⟩,⟨.or,[22,19]⟩], 23⟩

theorem witnessMonotone : ∀ g ∈ smallCircuit.gates,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [smallCircuit,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ⟨Or.inl rfl,by decide⟩ | exact ⟨Or.inr rfl,by decide⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem witnessCorrect : ∀ x : Fin 8 → Bool, smallCircuit.eval (List.ofFn x) = target x := by
  decide +kernel

theorem witnessSize : smallCircuit.gates.length = 16 := rfl

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

def lowRow (i : Fin 8) : Row := Fin.ofNat 512 (1 <<< ([2, 3, 0, 1, 0, 0, 0, 0] : List Nat).getD i.val 0)
def highRow (i : Fin 8) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< ([2, 3, 0, 1, 0, 0, 0, 0] : List Nat).getD i.val 0))

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
    (lower : Impossible true graph 14 sevenInputs.toFinset) (gates : List Gate) (o : Nat)
    (fit : ∀ g ∈ gates, (g.op=GateOp.and ∨ g.op=GateOp.or ∨ g.op=GateOp.not) ∧ g.inputs.length≤2)
    (correct : ∀ x : Fin 8 → Bool, (Circuit.mk gates o).eval (List.ofFn x)=target x) :
    ∃ (gs : List Gate) (out : Nat), (∀ g ∈ gs, (g.op=GateOp.and ∨ g.op=GateOp.or) ∧ g.inputs.length≤2) ∧
       gs.length≤gates.length ∧ ∀ x : Fin 8 → Bool, (Circuit.mk gs out).eval (List.ofFn x)=target x := by
  classical
  by_cases big : 16 ≤ gates.length
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
def g21Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3ff63ff63ff63ff63f,0xf63ff63ff63ff63ff63f])),(BitVec.ofNat 152 (word80 [0x492049204920492049,0x20492049204920492049]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xc7fbc7fbc7fbc7fbc7,0xfbc7fbc7fbc7fbc7fbc7])),(BitVec.ofNat 152 (word80 [0x924092409240924092,0x40924092409240924092]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xf8fdf8fdf8fdf8fdf8,0xfdf8fdf8fdf8fdf8fdf8])),(BitVec.ofNat 152 (word80 [0x248124812481248124,0x81248124812481248124]))),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g21C : List ColumnInfo := []
def g21A : List (List Nat) := [[],[66],[32],[32,64],[64,32],[64]]
def g21D3 (j : Nat) := if j=0 then 0x7 else 0
def g21L : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,g21D3)
  | _ => emptyPacking
def g21I (_ _ : Nat) : Option (Nat × Nat) := none
def g21 : Forest := ⟨21,3,fun i => g21Y[i]?.getD (0,0),g21C,g21A,g21L,g21I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g21P3_0 : block g21 3 0 1=true := by
  apply cellsBlock (ar:=3) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g21B3 : block g21 3 0 1=true := g21P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g21T : checkedTables g21 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g21 0 0 0 = true)
  · exact (rfl : block g21 1 0 0 = true)
  · exact (rfl : block g21 2 0 0 = true)
  · exact g21B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g21G : graphValid g21 (boundsBefore []) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low21 : Lower true (varsX 21) (graphGoal 21) 4 := lower_forest (g:=g21) (i:=0) (hints:=2) (before_sound [] baseKnown) g21G g21T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K21 := extendKnown [] 4 [(21,[]),(37,[84]),(49,[66,50,83]),(52,[32,16,65,49,83]),(69,[100,84]),(74,[16,50,100,84]),(133,[116,84,101]),(145,[66,50,115,83,101]),(148,[32,16,65,49,115,83,101]),(161,[82,50,116,100]),(164,[32,16,81,49,116,100]),(176,[64,16,82,49,115,99])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V21 : Known true K21 := extend_ok (m:=21) baseKnown low21 (by decide +kernel)
def g39Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfdf00fff81fc7e3ffb,0xe01fff03f8fc7ff7c03f])),(BitVec.ofNat 152 (word80 [0x45c09245142904808b,0x81248a28520901170249]))),((BitVec.ofNat 152 (word80 [0xe6a8703ffe007fc7cd,0x50e07ffc00ff8f9aa1c0])),(BitVec.ofNat 152 (word80 [0x96a9b6d618b228112d,0x536dac316450225aa6db]))),((BitVec.ofNat 152 (word80 [0xfbb781ffffff8007f7,0x6f03ffffff000feede07])),(BitVec.ofNat 152 (word80 [0x235249820c0312204,0x6a49304180624408d492]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x64ffe3ffffffff80c,0x9ffc7ffffffff0193ff8])),(BitVec.ofNat 152 (word80 [0x249204100400400,0x4924082008008000924]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g39C : List ColumnInfo := [(2,0,37,0,4)]
def g39A : List (List Nat) := [[],[32]]
def g39D4 (j : Nat) := if j=0 then 0x1f else 0
def g39L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g39D4)
  | _ => emptyPacking
def g39I (_ _ : Nat) : Option (Nat × Nat) := none
def g39 : Forest := ⟨39,4,fun i => g39Y[i]?.getD (0,0),g39C,g39A,g39L,g39I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g39P4_0 : block g39 4 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g39B4 : block g39 4 0 1=true := g39P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g39T : checkedTables g39 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g39 0 0 0 = true)
  · exact (rfl : block g39 1 0 0 = true)
  · exact (rfl : block g39 2 0 0 = true)
  · exact (rfl : block g39 3 0 0 = true)
  · exact g39B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g39G : graphValid g39 (boundsBefore K21) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low39 : Lower true (varsX 39) (graphGoal 39) 5 := lower_forest (g:=g39) (i:=0) (hints:=82) (before_sound K21 V21) g39G g39T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K39 := extendKnown K21 5 [(39,[]),(71,[101]),(75,[16,50,101]),(77,[49,101]),(78,[16,32,48,101]),(89,[49,66,101]),(90,[16,64,50,32,101]),(92,[32,49,64,16,101]),(106,[48,81,98,66]),(163,[114,50,67,100]),(169,[49,82,66,116,100]),(202,[16,112,98,48,66,83]),(225,[80,97,114,49,66])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V39 : Known true K39 := extend_ok (m:=39) V21 low39 (by decide +kernel)
def g43Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x2fc38ff01fff1ff02,0xfc38ff01fff1ff02fc38])),(BitVec.ofNat 152 (word80 [0x42ccdb2a5451240242,0xccdb2a5451240242ccdb]))),((BitVec.ofNat 152 (word80 [0xfdcbc7fffe07fe3ffd,0xcbc7fffe07fe3ffdcbc7])),(BitVec.ofNat 152 (word80 [0x1448490c1860408414,0x48490c18604084144849]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xece607fffff8003fec,0xe607fffff8003fece607])),(BitVec.ofNat 152 (word80 [0x8a7b6b06085892808,0xa7b6b06085892808a7b6]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1b3df8ffffffffc01b,0x3df8ffffffffc01b3df8])),(BitVec.ofNat 152 (word80 [0x893124c08106003089,0x3124c081060030893124]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g43C : List ColumnInfo := []
def g43A : List (List Nat) := [[],[48,81]]
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
theorem g43G : graphValid g43 (boundsBefore K39) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low43 : Lower true (varsX 43) (graphGoal 43) 4 := lower_forest (g:=g43) (i:=0) (hints:=4149) (before_sound K39 V39) g43G g43T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K43 := extendKnown K39 4 [(43,[]),(46,[32]),(58,[48,81,32,66]),(105,[48,16,33,82,66,100]),(108,[48,33,16,81,65,100]),(120,[48,65,32,82,98]),(139,[49,117,101]),(142,[16,112,32,50,83,101]),(154,[16,112,32,67,50,83,101]),(195,[16,115,67,101,84]),(210,[16,64,32,115,101,83]),(226,[96,81,32,115,66,67]),(232,[80,49,32,97,65,114,66])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V43 : Known true K43 := extend_ok (m:=43) V39 low43 (by decide +kernel)
def g53Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xdf7ec03c3ffe0fbefd,0x80787ffc1f7dfb00f0ff])),(BitVec.ofNat 152 (word80 [0x820404444444210408,0x8888888420810111111]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1fbf43c3c3fff03f7e,0x878787ffe07efd0f0f0f])),(BitVec.ofNat 152 (word80 [0x40808888888420810,0x11111110841020222222]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xe03fbc03fc3fffc07f,0x7807f87fff80fef00ff0])),(BitVec.ofNat 152 (word80 [0x81011111110841020,0x22222221082040444444]))),((BitVec.ofNat 152 (word80 [0xffc03ffc003fffff80,0x7ff8007fffff00fff000])),(BitVec.ofNat 152 (word80 [0x102022222221082040,0x44444442104080888888]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g53C : List ColumnInfo := [(1,0,52,0,4),(4,0,49,0,4),(16,0,37,0,4),(32,0,21,0,4)]
def g53A : List (List Nat) := [[],[84],[66],[66,82],[82,66],[82],[32],[32,84],[32,64],[32,64,80],[32,80,64],[32,80],[64,32],[64,32,82],[64],[64,80],[64,82],[64,82,32],[80,32,66],[80,32],[80,64],[80],[80,66,32],[80,66]]
def g53D3 := limbs80 #[#[0x23ea6a1221e12148110,0x8028]]
def g53D4 := limbs80 #[#[0x2fd0910bd42443e48110,0x609085870]]
def g53H4 (j : Nat) := if j=0 then 0x7540 else 0
def g53D5 (j : Nat) := if j=0 then 0xd1027d10 else 0
def g53H5 := limbs80 #[#[0x110000000,0x8a000000000009308400,0x70000000600000000001,0x20800cc0]]
def g53D6 (j : Nat) := if j=0 then 0x3904f else 0
def g53H6 := limbs80 #[#[0x25003d0003100001a4,0xe00000000002800000]]
def g53L : Nat → Packing
  | 3 => (2,3,2,0,0,5,0,g53D3)
  | 4 => (3,2,2,0,0,5,0,g53D4)
  | 5 => (1,1,2,0,0,0,0,g53D5)
  | 6 => (1,0,2,0,0,0,0,g53D6)
  | _ => emptyPacking
def g53I : Nat → Nat → Option (Nat × Nat)
  | 4 => lookupWord 1 5 0 5 1 0 g53H4
  | 5 => lookupWord 2 31 0 9 2 3 g53H5
  | 6 => lookupWord 1 17 0 9 0 5 g53H6
  | _ => fun _ => none
def g53 : Forest := ⟨53,6,fun i => g53Y[i]?.getD (0,0),g53C,g53A,g53L,g53I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g53P3_0 : block g53 3 0 2=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g53B3 : block g53 3 0 2=true := g53P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g53P4_0 : block g53 4 0 3=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g53B4 : block g53 4 0 3=true := g53P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g53P5_0 : block g53 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g53B5 : block g53 5 0 1=true := g53P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g53P6_0 : block g53 6 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g53B6 : block g53 6 0 1=true := g53P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g53T : checkedTables g53 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g53 0 0 0 = true)
  · exact (rfl : block g53 1 0 0 = true)
  · exact (rfl : block g53 2 0 0 = true)
  · exact g53B3
  · exact g53B4
  · exact g53B5
  · exact g53B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g53G : graphValid g53 (boundsBefore K43) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low53 : Lower true (varsX 53) (graphGoal 53) 7 := lower_forest (g:=g53) (i:=0) (hints:=2) (before_sound K43 V43) g53G g53T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K53 := extendKnown K43 7 [(53,[]),(85,[101]),(149,[117,101]),(165,[84,116,100]),(177,[66,50,83,115,99]),(180,[32,16,65,49,83,115,99])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V53 : Known true K53 := extend_ok (m:=53) V43 low53 (by decide +kernel)
def g101Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xf3e58e3ffc1ffcff3e,0x58e3ffc1ffcff3e58e3f])),(BitVec.ofNat 152 (word80 [0x200012490842080200,0x1249084208020001249]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfcfa71c7ffe0ff3fcf,0xa71c7ffe0ff3fcfa71c7])),(BitVec.ofNat 152 (word80 [0x400024921084100400,0x2492108410040002492]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xff0e81f8ffff003ff0,0xe81f8ffff003ff0e81f8])),(BitVec.ofNat 152 (word80 [0x804ec924a108a2a804,0xec924a108a2a804ec924]))),((BitVec.ofNat 152 (word80 [0x19fe00ffffffc001,0x9fe00ffffffc0019fe00])),(BitVec.ofNat 152 (word80 [0xa99c924c210c030a9,0x9c924c210c030a99c924]))),(0x0,0x0),(0x0,0x0)]
def g101C : List ColumnInfo := [(32,0,69,0,4)]
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
theorem g101G : graphValid g101 (boundsBefore K53) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low101 : Lower true (varsX 101) (graphGoal 101) 5 := lower_forest (g:=g101) (i:=0) (hints:=2) (before_sound K53 V53) g101G g101T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K101 := extendKnown K53 5 [(101,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V101 : Known true K101 := extend_ok (m:=101) V53 low101 (by decide +kernel)
def g31Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xc00fff0ffffffc00ff,0xfff0fffeea3a5303f03f])),(BitVec.ofNat 152 (word80 [0x84a08a210802284a02,0x80220882200a53145145]))),((BitVec.ofNat 152 (word80 [0xfff0000ffc3fffff00,0x3fffffc009adfd000fc0])),(BitVec.ofNat 152 (word80 [0xc42c405090b10c4b,0x11404108092d994d34d3]))),((BitVec.ofNat 152 (word80 [0xfffffff0003fffffff,0xc000fffd77e88afc003f])),(BitVec.ofNat 152 (word80 [0x90130026104c0100c,0x584120152a08828a28a]))),((BitVec.ofNat 152 (word80 [0x3fffffff,0xffff00012697f4000fc0])),(BitVec.ofNat 152 (word80 [0x2e09c08b8227026090,0x26009c11269264b2cb2c]))),((BitVec.ofNat 152 (word80 [0xffffffffffc0000000,0x39d530dfff000])),(BitVec.ofNat 152 (word80 [0x300e000c00380380e0,0x3808e0208d5104c30c30]))),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g31C : List ColumnInfo := [(0,2,21,8,5)]
def g31A : List (List Nat) := [[],[66],[49],[49,66],[32],[32,64],[32,49],[32,49,64],[64,32],[64],[64,49,32],[64,49]]
def g31D5 (j : Nat) := if j=0 then 0x3f else 0
def g31L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g31D5)
  | _ => emptyPacking
def g31I (_ _ : Nat) : Option (Nat × Nat) := none
def g31 : Forest := ⟨31,5,fun i => g31Y[i]?.getD (0,0),g31C,g31A,g31L,g31I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g31P5_0 : block g31 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g31B5 : block g31 5 0 1=true := g31P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g31T : checkedTables g31 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g31 0 0 0 = true)
  · exact (rfl : block g31 1 0 0 = true)
  · exact (rfl : block g31 2 0 0 = true)
  · exact (rfl : block g31 3 0 0 = true)
  · exact (rfl : block g31 4 0 0 = true)
  · exact g31B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g31G : graphValid g31 (boundsBefore K101) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low31 : Lower true (varsX 31) (graphGoal 31) 6 := lower_forest (g:=g31) (i:=0) (hints:=4146) (before_sound K101 V101) g31G g31T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K31 := extendKnown K101 6 [(31,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V31 : Known true K31 := extend_ok (m:=31) V101 low31 (by decide +kernel)
def g47Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xf003ff87fe1fffc01f,0xfff87fffe474a4007c1f])),(BitVec.ofNat 152 (word80 [0xa12845108440228940,0xa01108826014a45294a5]))),((BitVec.ofNat 152 (word80 [0xfffc0007ffe1ffffe0,0xfffffc0335be20f83e0])),(BitVec.ofNat 152 (word80 [0xc030162028040b0182,0xc0a00108225922318c63]))),((BitVec.ofNat 152 (word80 [0xfffffff80001ffffff,0xf0007ffccfd11df0001f])),(BitVec.ofNat 152 (word80 [0x240980130884c0203,0x2c2120087c108a5294a]))),((BitVec.ofNat 152 (word80 [0x1ffffff,0xffff80004d2fe80003e0])),(BitVec.ofNat 152 (word80 [0xb82e045c111702c14,0xb005c104d26c9ce739c]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffffffe000000,0x33aa61bfffc00])),(BitVec.ofNat 152 (word80 [0xc0300060001803018,0xc046021182211084210]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g47C : List ColumnInfo := [(0,8,37,2,5),(8,0,39,0,5),(1,0,46,0,4),(2,8,37,0,4),(4,0,43,0,4)]
def g47A : List (List Nat) := [[],[32]]
def g47D4 (j : Nat) := if j=0 then 0x5bd4940 else 0
def g47D5 := limbs80 #[#[0x240d140ff40fd40fd20,0x2012]]
def g47H5 (j : Nat) := if j=0 then 0xf else 0
def g47D6 (j : Nat) := if j=0 then 0x18989f else 0
def g47H6 (j : Nat) := if j=0 then 0x10dd000005a6c02800 else 0
def g47L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g47D4)
  | 5 => (3,1,3,0,0,5,0,g47D5)
  | 6 => (1,0,3,0,0,0,0,g47D6)
  | _ => emptyPacking
def g47I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 4 0 0 g47H5
  | 6 => lookupWord 1 11 0 7 2 1 g47H6
  | _ => fun _ => none
def g47 : Forest := ⟨47,6,fun i => g47Y[i]?.getD (0,0),g47C,g47A,g47L,g47I⟩
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
theorem g47P5_0 : block g47 5 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g47B5 : block g47 5 0 3=true := g47P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g47P6_0 : block g47 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g47B6 : block g47 6 0 1=true := g47P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g47T : checkedTables g47 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g47 0 0 0 = true)
  · exact (rfl : block g47 1 0 0 = true)
  · exact (rfl : block g47 2 0 0 = true)
  · exact (rfl : block g47 3 0 0 = true)
  · exact g47B4
  · exact g47B5
  · exact g47B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g47G : graphValid g47 (boundsBefore K31) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low47 : Lower true (varsX 47) (graphGoal 47) 7 := lower_forest (g:=g47) (i:=0) (hints:=4146) (before_sound K31 V31) g47G g47T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K47 := extendKnown K31 7 [(47,[]),(59,[66]),(62,[32,64]),(143,[49,117,101]),(155,[49,66,117,101]),(158,[32,49,64,117,101])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V47 : Known true K47 := extend_ok (m:=47) V31 low47 (by decide +kernel)
def g55Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfe1ff00ff87f87ffc0,0x7fc7ffffd3b94000f0ff])),(BitVec.ofNat 152 (word80 [0x1440a0a05101100285,0x2902008418941111111]))),((BitVec.ofNat 152 (word80 [0x1ffff0007ff87fff,0x8007f1fc231ee00f0000])),(BitVec.ofNat 152 (word80 [0x588ac4c5622a012b06,0x2b214491231ee7777777]))),((BitVec.ofNat 152 (word80 [0x1fffffff80007fff,0xfff801ff9c1f30f00f0f])),(BitVec.ofNat 152 (word80 [0x61030101800c220c08,0xc0188201c1602222222]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffe000000000007fff,0xfffffe000be4bf000ff0])),(BitVec.ofNat 152 (word80 [0x800c06060430443010,0x300200c20260b4444444]))),((BitVec.ofNat 152 (word80 [0xffffffffffffff8000,0x6442cffff000])),(BitVec.ofNat 152 (word80 [0x1008080040004020,0x40040100000008888888]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g55C : List ColumnInfo := [(2,0,53,0,7)]
def g55A : List (List Nat) := [[],[66],[32],[32,64],[64,32],[64]]
def g55D7 (j : Nat) := if j=0 then 0x3f else 0
def g55L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g55D7)
  | _ => emptyPacking
def g55I (_ _ : Nat) : Option (Nat × Nat) := none
def g55 : Forest := ⟨55,7,fun i => g55Y[i]?.getD (0,0),g55C,g55A,g55L,g55I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g55P7_0 : block g55 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g55B7 : block g55 7 0 1=true := g55P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g55T : checkedTables g55 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g55 0 0 0 = true)
  · exact (rfl : block g55 1 0 0 = true)
  · exact (rfl : block g55 2 0 0 = true)
  · exact (rfl : block g55 3 0 0 = true)
  · exact (rfl : block g55 4 0 0 = true)
  · exact (rfl : block g55 5 0 0 = true)
  · exact (rfl : block g55 6 0 0 = true)
  · exact g55B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g55G : graphValid g55 (boundsBefore K47) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low55 : Lower true (varsX 55) (graphGoal 55) 8 := lower_forest (g:=g55) (i:=0) (hints:=82) (before_sound K47 V47) g55G g55T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K55 := extendKnown K47 8 [(55,[]),(87,[101]),(93,[49,101]),(167,[116,100]),(173,[49,84,116,100])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V55 : Known true K55 := extend_ok (m:=55) V47 low55 (by decide +kernel)
def g79Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffc01ff87fc3fff00,0xffff1ffed2e680007c1f])),(BitVec.ofNat 152 (word80 [0x222894451108808a4a,0xa02444252268a5294a5]))),((BitVec.ofNat 152 (word80 [0xffffe0007ffc3ffff,0xffffe11773400f83e0])),(BitVec.ofNat 152 (word80 [0x40b018162050082c0c,0x2c140089146346318c63]))),((BitVec.ofNat 152 (word80 [0xffffffff80003ffff,0xff001ffce8f541f0001f])),(BitVec.ofNat 152 (word80 [0x84c120980261113010,0x30588900a8d154a5294a]))),((BitVec.ofNat 152 (word80 [0xf0000000000003ffff,0xffffe0005f98fe0003e0])),(BitVec.ofNat 152 (word80 [0x701c0e0438221c060,0x40600e104b9898c6318c]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffffffffc0000,0x3280bbffffc00])),(BitVec.ofNat 152 (word80 [0x80201000400020080,0x80801000000021084210]))),(0x0,0x0),(0x0,0x0)]
def g79C : List ColumnInfo := [(1,0,78,0,5),(2,0,77,0,5),(4,0,75,0,5),(8,0,71,0,5),(5,0,74,0,4),(10,0,69,0,4)]
def g79A : List (List Nat) := [[],[49],[16,50],[16,32,48],[32],[32,49],[48,16,33],[48,33]]
def g79D4 := limbs80 #[#[0x9bd89544426d6215110,0x31825f635474]]
def g79D5 := limbs80 #[#[0x7c54443f280885bd4940,0xfea8885f95110beaa221,0xbd4940bfa8a81fb40502,0xcc8d018160c02faa3a07,0x882188201141080d176b,0xc110204810001]]
def g79H5 := limbs80 #[#[0xe800d9000000b10000,0x2200b0]]
def g79D6 := limbs80 #[#[0x540a0380ff40fd40fd10,0x3140cc503]]
def g79H6 := limbs80 #[#[0x309910020725c81002d3,0x18300000001c000000,0x78645a100071bc800000,0x3d99500000289]]
def g79D7 (j : Nat) := if j=0 then 0x1605f else 0
def g79H7 := limbs80 #[#[0x7e95999005c85540,0xa20000000c0000040882,0x6900000000000002,0x3d00000120]]
def g79L : Nat → Packing
  | 4 => (3,3,3,0,0,4,0,g79D4)
  | 5 => (10,2,3,0,0,7,0,g79D5)
  | 6 => (3,1,3,0,0,6,0,g79D6)
  | 7 => (1,0,3,0,0,0,0,g79D7)
  | _ => emptyPacking
def g79I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 13 0 8 2 2 g79H5
  | 6 => lookupWord 4 29 0 10 4 2 g79H6
  | 7 => lookupWord 3 31 3 9 2 3 g79H7
  | _ => fun _ => none
def g79 : Forest := ⟨79,7,fun i => g79Y[i]?.getD (0,0),g79C,g79A,g79L,g79I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g79P4_0 : block g79 4 0 3=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g79B4 : block g79 4 0 3=true := g79P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g79P5_0 : block g79 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g79P5_1 : block g79 5 1 9=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g79B5 : block g79 5 0 10=true := (@block_merge g79 5 0 1 9 g79P5_0 g79P5_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g79P6_0 : block g79 6 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g79B6 : block g79 6 0 3=true := g79P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g79P7_0 : block g79 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g79B7 : block g79 7 0 1=true := g79P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g79T : checkedTables g79 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g79 0 0 0 = true)
  · exact (rfl : block g79 1 0 0 = true)
  · exact (rfl : block g79 2 0 0 = true)
  · exact (rfl : block g79 3 0 0 = true)
  · exact g79B4
  · exact g79B5
  · exact g79B6
  · exact g79B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g79G : graphValid g79 (boundsBefore K55) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low79 : Lower true (varsX 79) (graphGoal 79) 8 := lower_forest (g:=g79) (i:=0) (hints:=4146) (before_sound K55 V55) g79G g79T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K79 := extendKnown K55 8 [(79,[]),(91,[66]),(94,[16,32,48,64])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V79 : Known true K79 := extend_ok (m:=79) V55 low79 (by decide +kernel)
def g103Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfffc03fe1fe1fff00f,0xf87f87ffff856420703f])),(BitVec.ofNat 152 (word80 [0x50282814404400a0a0,0x51011002098064049249]))),((BitVec.ofNat 152 (word80 [0x7fffc001ffe1ffff0,0x7ff87f01c9c9c381c0])),(BitVec.ofNat 152 (word80 [0x60b03058828042c0c1,0x620a01042181c98db6db]))),((BitVec.ofNat 152 (word80 [0x7ffffffe0001fffff,0xff80007ff233d69c0e07])),(BitVec.ofNat 152 (word80 [0x80c040600308830101,0x800c2208021380892492]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xf800000000001fffff,0xffffff80013c2ae00ff8])),(BitVec.ofNat 152 (word80 [0x50282811411140a0a,0x500050402c02724924]))),((BitVec.ofNat 152 (word80 [0xffffffffffffe00000,0xce2917ff000])),(BitVec.ofNat 152 (word80 [0x60303001800180c0c,0x4604460846010724924]))),(0x0,0x0),(0x0,0x0)]
def g103C : List ColumnInfo := [(2,0,101,0,5)]
def g103A : List (List Nat) := [[],[101],[32],[32,101]]
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
theorem g103G : graphValid g103 (boundsBefore K79) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low103 : Lower true (varsX 103) (graphGoal 103) 6 := lower_forest (g:=g103) (i:=0) (hints:=82) (before_sound K79 V79) g103G g103T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K103 := extendKnown K79 6 [(205,[49,101,117]),(217,[49,66,101,117]),(220,[32,49,64,16,101,117])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V103 : Known true K103 := extend_ok (m:=103) V79 low103 (by decide +kernel)
def g107Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xff003fe1ff0fffc01f,0xfff0fff0d97f0000f0f0])),(BitVec.ofNat 152 (word80 [0x2a0a814412200a8541,0x41220022993600333333]))),((BitVec.ofNat 152 (word80 [0xffffc001fff0ffffe0,0x1fff0fff3c14bb0f0f0f])),(BitVec.ofNat 152 (word80 [0xc0301880402030181,0x80402040180413111111]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffe0000ffffff,0xe0000fff23b566f0000f])),(BitVec.ofNat 152 (word80 [0xb02c0a0058442c0602,0x5844280213164666666]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffff,0xfffff000134bf8000ff0])),(BitVec.ofNat 152 (word80 [0xc0b02c116088b02814,0x16000b040249e8cccccc]))),((BitVec.ofNat 152 (word80 [0xffffffffffff000000,0xcea8c5fff000])),(BitVec.ofNat 152 (word80 [0xc030018000c03018,0x18088c08468880888888]))),(0x0,0x0),(0x0,0x0)]
def g107C : List ColumnInfo := [(1,0,106,0,5)]
def g107A : List (List Nat) := [[],[80,97]]
def g107D5 (j : Nat) := if j=0 then 0x3f else 0
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
theorem g107G : graphValid g107 (boundsBefore K103) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low107 : Lower true (varsX 107) (graphGoal 107) 6 := lower_forest (g:=g107) (i:=0) (hints:=4149) (before_sound K103 V103) g107G g107T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K107 := extendKnown K103 6 [(107,[]),(171,[16,112,48,83,101]),(174,[16,112,32,50,83,101]),(186,[16,112,32,67,50,83,101]),(203,[49,117]),(206,[32,49,117]),(218,[64,49,32,117]),(227,[16,115,67,101]),(230,[16,32,115,67,101]),(233,[48,16,33,82,66,100,116]),(234,[80,49,32,97,66,116]),(236,[48,33,16,81,65,100,116]),(242,[16,64,32,115,101]),(248,[48,65,32,82,98,114])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V107 : Known true K107 := extend_ok (m:=107) V103 low107 (by decide +kernel)
def g109Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xff007fc3ff0fffc03f,0xfff0fffff1de0200f0ff])),(BitVec.ofNat 152 (word80 [0x120900881220048480,0x81220020908602111111]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffff8003fff0ffffc0,0x3fff0fff2435bb0f0f0f])),(BitVec.ofNat 152 (word80 [0x240205102402090105,0x2402040203111222222]))),((BitVec.ofNat 152 (word80 [0xfffffffc0000ffffff,0xc0000ff01bb564f00000])),(BitVec.ofNat 152 (word80 [0xb82c1600b8442e0606,0xb84428219b560777777]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffff,0xfffff000134bf8000ff0])),(BitVec.ofNat 152 (word80 [0xc0b05822c088b02828,0x2c000b040348e8cccccc]))),((BitVec.ofNat 152 (word80 [0xffffffffffff000000,0xcea8c5fff000])),(BitVec.ofNat 152 (word80 [0xc060030000c03030,0x30088c08460884888888]))),(0x0,0x0),(0x0,0x0)]
def g109C : List ColumnInfo := [(0,8,37,64,5),(8,0,101,0,5),(32,0,77,0,5),(1,0,108,0,4),(4,0,105,0,4),(64,8,37,0,4)]
def g109A : List (List Nat) := [[],[32]]
def g109D4 (j : Nat) := if j=0 then 0x57d4d10 else 0
def g109D5 (j : Nat) := if j=0 then 0xc8404fd10 else 0
def g109H5 (j : Nat) := if j=0 then 0x8 else 0
def g109D6 (j : Nat) := if j=0 then 0x232a8bf else 0
def g109H6 (j : Nat) := if j=0 then 0x9 else 0
def g109L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g109D4)
  | 5 => (1,1,3,0,0,0,0,g109D5)
  | 6 => (1,0,3,0,0,0,0,g109D6)
  | _ => emptyPacking
def g109I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 4 0 0 g109H5
  | 6 => lookupWord 1 2 0 4 0 0 g109H6
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
theorem g109P5_0 : block g109 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g109B5 : block g109 5 0 1=true := g109P5_0
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
theorem low109 : Lower true (varsX 109) (graphGoal 109) 7 := lower_forest (g:=g109) (i:=0) (hints:=24578) (before_sound K107 V107) g109G g109T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K109 := extendKnown K107 7 [(109,[]),(121,[66]),(124,[32,16,65]),(199,[49,117]),(211,[33,65,49,117]),(214,[32,16,65,49,117])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V109 : Known true K109 := extend_ok (m:=109) V107 low109 (by decide +kernel)
def g117Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfe07ffc07f3f9ff01,0xfcfe7fc7f4800f00f0ff])),(BitVec.ofNat 152 (word80 [0x204104081020100204,0x8040080000111111111]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfff81fff803fe7ffe,0xff9ff8e150f00f0f0f])),(BitVec.ofNat 152 (word80 [0x408208102040200408,0x10080100000222222222]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xf00001fffffc007fff,0xff001fff0a2f00f00ff0])),(BitVec.ofNat 152 (word80 [0x810410204080400810,0x20100200000444444444]))),((BitVec.ofNat 152 (word80 [0xfffffe000000007fff,0xffffe0001e5000fff000])),(BitVec.ofNat 152 (word80 [0xa082142850a8550a1,0x40a014125e5888888888]))),((BitVec.ofNat 152 (word80 [0xffffffffffffff8000,0x19bfff000000])),(BitVec.ofNat 152 (word80 [0xc10418306030060c1,0x82c1582499b888888888]))),(0x0,0x0),(0x0,0x0)]
def g117C : List ColumnInfo := [(32,0,85,0,7)]
def g117A : List (List Nat) := [[],[101],[66],[66,101],[32],[32,101],[32,64],[32,64,101],[64,32],[64,32,101],[64],[64,101]]
def g117D7 (j : Nat) := if j=0 then 0x3f else 0
def g117L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g117D7)
  | _ => emptyPacking
def g117I (_ _ : Nat) : Option (Nat × Nat) := none
def g117 : Forest := ⟨117,7,fun i => g117Y[i]?.getD (0,0),g117C,g117A,g117L,g117I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g117P7_0 : block g117 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g117B7 : block g117 7 0 1=true := g117P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g117T : checkedTables g117 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g117 0 0 0 = true)
  · exact (rfl : block g117 1 0 0 = true)
  · exact (rfl : block g117 2 0 0 = true)
  · exact (rfl : block g117 3 0 0 = true)
  · exact (rfl : block g117 4 0 0 = true)
  · exact (rfl : block g117 5 0 0 = true)
  · exact (rfl : block g117 6 0 0 = true)
  · exact g117B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g117G : graphValid g117 (boundsBefore K109) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low117 : Lower true (varsX 117) (graphGoal 117) 8 := lower_forest (g:=g117) (i:=0) (hints:=2) (before_sound K109 V109) g117G g117T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K117 := extendKnown K109 8 [(117,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V117 : Known true K117 := extend_ok (m:=117) V109 low117 (by decide +kernel)
def g181Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xc0fc0fc0fdf81fbf7f,0x3f7efec0007c00f83ff])),(BitVec.ofNat 152 (word80 [0x820820820810410202,0x8204040210842108421]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xff000fff01ffe03fbf,0xfc07f7f400f801f07c1f])),(BitVec.ofNat 152 (word80 [0x41041041020820404,0x10408080421084210842]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffff00001ffffc03f,0xfff807f81f003e007fe0])),(BitVec.ofNat 152 (word80 [0x82082082041040808,0x20810100842108421084]))),((BitVec.ofNat 152 (word80 [0xfffffffffe0000003f,0xfffff803e0003fff8000])),(BitVec.ofNat 152 (word80 [0x104104104082081010,0x41020201084210842108]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffffffc0,0x3ffffc0000000])),(BitVec.ofNat 152 (word80 [0x208208208104102020,0x82040402108421084210]))),(0x0,0x0)]
def g181C : List ColumnInfo := [(1,0,180,0,7),(4,0,177,0,7),(16,0,165,0,7),(32,0,149,0,7),(128,0,53,0,7),(5,0,176,0,4),(17,0,164,0,4),(20,0,161,0,4),(33,0,148,0,4),(36,0,145,0,4),(48,0,133,0,4)]
def g181A : List (List Nat) := [[],[117],[84],[84,116],[116,84],[116],[66],[66,117],[66,82],[66,82,114],[66,114,82],[66,114],[82,66],[82,66,116],[82],[82,114],[82,116],[82,116,66],[114,66,84],[114,66],[114,82],[114],[114,84,66],[114,84],[32],[32,117],[32,84],[32,84,116],[32,116,84],[32,116],[32,64],[32,64,117],[32,64,80],[32,64,80,112],[32,64,112,80],[32,64,112],[32,80,64],[32,80,64,116],[32,80],[32,80,112],[32,80,116],[32,80,116,64],[32,112,64,84],[32,112,64],[32,112,80],[32,112],[32,112,84,64],[32,112,84],[64,32],[64,32,117],[64,32,82],[64,32,82,114],[64,32,114,82],[64,32,114],[64],[64,117],[64,80],[64,80,112],[64,112,80],[64,112],[64,82],[64,82,114],[64,82,32],[64,82,32,112],[64,82,112,32],[64,82,112],[64,114,82],[64,114],[64,114,32,80],[64,114,32],[64,114,80],[64,114,80,32],[80,32,66],[80,32,66,116],[80,32],[80,32,114],[80,32,116],[80,32,116,66],[80,64],[80,64,116],[80],[80,112],[80,116],[80,116,64],[80,66,32],[80,66,32,114],[80,66],[80,66,112],[80,66,114],[80,66,114,32],[80,114,64,66],[80,114,64],[80,114,66],[80,114,66,64],[80,114],[80,114,32],[112,32,66,84],[112,32,66],[112,32,82],[112,32],[112,32,84,66],[112,32,84],[112,64,84],[112,64],[112,80],[112],[112,84,64],[112,84],[112,66,32,82],[112,66,32],[112,66,80],[112,66],[112,66,82,32],[112,66,82],[112,82,64],[112,82,64,66],[112,82,66,64],[112,82,66],[112,82,32],[112,82]]
def g181D3 := limbs80 #[#[0x887805915350d2148110,0x4180360709aa26498a40,0x2]]
def g181D4 := limbs80 #[#[0x48110f415350d2148110,0x54d2148110b618550d21,0xe636454d2148110e6164,0x48110b638454d2148110,0xd4d2148110e6364d4d21,0xf41544c93148110b6184,0x48110f43544c93148110,0xd913148110f814350931,0xcb374d913148110ad183,0x4c91087b805d9544c910,0x82a4854300c3874dc165,0x808103df5df82d4b78d9,0x4002820a04000000120,0x1]]
def g181H4 := limbs80 #[#[0x330000000000000,0xd0d9c40000010000]]
def g181D5 := limbs80 #[#[0xa4290221d854d2148110,0x4887c1324c520443b1a9,0x850d214811087ee8b2a6,0xc520443f0a9a4290221f,0x10fc2e498a40887e1424,0xaa26290221dc55131481,0xa40886f1644c520443b9,0x15e5d54348110de6c898,0x254d20442f5b92a69022,0x8110cf2c8a9a408876b7,0xbdba2a6902219ed91534,0xa9a408867b64d4d20442,0x221bc585604c910af2e9,0xf76551324423ebb2a899,0x44c910adae5aa2648847,0x423ebb6a8992218fd935,0xe8b2a648856f72595324,0x992219edc1654c910a7e,0x63f74595324431e3a2ca,0xa654c9108fee8b2a6488,0x24423ebb4ca992215b5c,0x7ee8b1aa48856f7254d5,0xc7a92211f5d36354910a,0xb62007a1502e0023fba2,0x364a11a43106400e2370,0xbe681926317e5e16a531,0x16821fa7b1e6781d2711,0x669825a9323e8c22a872,0xc19cc144090805739216,0x7381801800a090605101,0x300242048144070605,0x8202041810904000241d],#[0x3481002410805020c200,0xc1d2040d221200c0810,0x404000074810204000,0x41010204]]
def g181H5 := limbs80 #[#[0xb978a00c211192d10084,0xd0f4a00a0398032,0x31e38000e3c1630400,0x10649ca0cbc800180,0x4800030e00002803b003,0x38f57000005009892ac0,0x230141f32017c,0x2a940000080294c16892,0x30656852020400038c,0x10d7a1a0000424790c00,0x5830db6c600008f800c3,0x23033d312c1c9200346,0x63c3078c0005006354f4,0x8000f26ec036f060000,0x9238308000b307a92d00,0x2,0x900a0000000248d,0x800000000000000,0xb1c346320c6d48c00000,0x3d78c334600000]]
def g181D6 := limbs80 #[#[0xfc4c520443e12148110,0x10ded4d2044379534811,0x9109fd8d524427d654c9,0x8110fe50d204427d63d4,0x4c910fe58132443f9534,0x54c910dfd51324437d54,0x5354910df995324437d6,0xd6354910bfd8d524437d,0x40600dc00dfd8d524437,0xf1935a94847d0436cb22,0x414795e43886067e5de6,0x12199d20a2870d03a732,0x333a414412202b3c3486,0x5d30e0662d3a58700414,0x4467083058228466143a,0x14288a42836114488241,0x2520ca5214144294a0c0,0x7c019989809920e90215,0x1c305662346610]]
def g181H6 := limbs80 #[#[0x1101c410c01400c0145,0x1281c50410011104090,0x830035e9a0d201e51810,0x5700de808e4045818ca3,0x8007864398605c790c01,0x218a00a90e2800016518,0x8a811c60241046c0006c,0x8000000000000d0c5106,0x3c5f044c0001c00ecc47,0x1c0000300440001e0088,0x1e68a1051100100000ac,0x304348400948640000,0x2c02f001f600600002,0x2835b0615a019000000,0x53c84bc51002c8000f05,0x7c0b022fed28400c0000,0x1600000000000034f0a0,0x20e230d11000030743d2,0x9a1b4082000006460000,0x10006000000000000004,0x6000038c000000c185b0,0x23e0800400000ec8,0x99400000000000000000,0x2dcf14a021202480001f,0xa0030000107,0x7d32380382668d91c0,0x118345b1c30000060252,0xfc09a7006b34334317a1,0x304bf83674d0,0x10c9f004f000004870,0xd9f140001868e838980,0x20e07242bc0120000f3c],#[0xc185800738091a4c8,0x44478700003804fa6180,0xe403b2907200289e00cf,0x8050c034e548c0201002,0x5b22b8c396002e0e57]]
def g181D7 := limbs80 #[#[0x7f52442faa4887e48110,0x3015007f54910fe99221,0x94301030ba6694235a3f,0xa5011a6690a20e30ba66,0x38da6690a3c8a142a70,0x4]]
def g181H7 := limbs80 #[#[0x8004021200c020208180,0x35800033c5d700162800,0x38000000040617005a8,0x2120414000800051a47c,0x7284408245860a00000,0x1163c621e15802586458,0x6841c0,0x7583b010e007d81700,0xc6e81320718843800000,0xc0ebc4d802e3213801cb,0x44b80541c464a111a190,0x3426000038710011ed,0x1239c100708006f3c500,0x11e0b00849a1000028,0x35984f804da40800000,0x12c01781c1d003c81470,0x6000050741818b008b8,0xb41000021c3800010,0x4506180001424801800,0x35000000004821800048,0x40010000000058]]
def g181D8 (j : Nat) := if j=0 then 0x2d2720806fd10 else 0
def g181H8 := limbs80 #[#[0x0,0xa0b0000,0x71200000000,0x114000000000e20ae0,0x904000000f243020000,0x0,0x200000000000,0x110103000000cc06d00,0x81100000012201b00,0x1000000000621000]]
def g181D9 (j : Nat) := if j=0 then 0x219080bf else 0
def g181H9 := limbs80 #[#[0x248005aa0000004f586,0xa9e65a24800000000d0,0x38c0013]]
def g181L : Nat → Packing
  | 3 => (2,6,4,0,0,5,0,g181D3)
  | 4 => (14,5,4,0,0,7,0,g181D4)
  | 5 => (38,4,4,0,0,10,0,g181D5)
  | 6 => (18,3,4,0,0,10,0,g181D6)
  | 7 => (5,2,4,0,0,8,0,g181D7)
  | 8 => (1,1,4,0,0,0,0,g181D8)
  | 9 => (1,0,4,0,0,0,0,g181D9)
  | _ => emptyPacking
def g181I : Nat → Nat → Option (Nat × Nat)
  | 4 => lookupWord 1 13 0 12 1 7 g181H4
  | 5 => lookupWord 16 101 5 15 4 7 g181H5
  | 6 => lookupWord 30 163 6 17 6 7 g181H6
  | 7 => lookupWord 17 97 7 16 5 7 g181H7
  | 8 => lookupWord 4 67 0 12 3 5 g181H8
  | 9 => lookupWord 2 17 0 11 0 7 g181H9
  | _ => fun _ => none
def g181 : Forest := ⟨181,9,fun i => g181Y[i]?.getD (0,0),g181C,g181A,g181L,g181I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g181P3_0 : block g181 3 0 2=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g181B3 : block g181 3 0 2=true := g181P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g181P4_0 : block g181 4 0 14=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g181B4 : block g181 4 0 14=true := g181P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g181P5_0 : block g181 5 0 4=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g181P5_4 : block g181 5 4 34=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g181B5 : block g181 5 0 38=true := (@block_merge g181 5 0 4 34 g181P5_0 g181P5_4)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g181P6_0 : block g181 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g181P6_1 : block g181 6 1 6=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g181P6_7 : block g181 6 7 11=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g181B6 : block g181 6 0 18=true := (@block_merge g181 6 0 1 17 g181P6_0 (@block_merge g181 6 1 6 11 g181P6_1 g181P6_7))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g181P7_0 : block g181 7 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g181P7_3 : block g181 7 3 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g181B7 : block g181 7 0 5=true := (@block_merge g181 7 0 3 2 g181P7_0 g181P7_3)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g181P8_0 : block g181 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g181B8 : block g181 8 0 1=true := g181P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g181P9_0 : block g181 9 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g181B9 : block g181 9 0 1=true := g181P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g181T : checkedTables g181 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g181 0 0 0 = true)
  · exact (rfl : block g181 1 0 0 = true)
  · exact (rfl : block g181 2 0 0 = true)
  · exact g181B3
  · exact g181B4
  · exact g181B5
  · exact g181B6
  · exact g181B7
  · exact g181B8
  · exact g181B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g181G : graphValid g181 (boundsBefore K117) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low181 : Lower true (varsX 181) (graphGoal 181) 10 := lower_forest (g:=g181) (i:=0) (hints:=2) (before_sound K117 V117) g181G g181T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K181 := extendKnown K117 10 [(181,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V181 : Known true K181 := extend_ok (m:=181) V117 low181 (by decide +kernel)
def g229Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x7fff00ff3fc7ff01f,0xffc7ff1fd62200f0f0ff])),(BitVec.ofNat 152 (word80 [0x102020202008002040,0x80800200000011111111]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xf80ffff003ff8fffe0,0x3ff8ffe3c0d90f0f0f0f])),(BitVec.ofNat 152 (word80 [0x204040404010004081,0x1000400000022222222]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffc000fffff,0xc000fffc2f0df0000ff0])),(BitVec.ofNat 152 (word80 [0x4282828280a1228102,0xa1228008f0944444444]))),((BitVec.ofNat 152 (word80 [0xfff0000000000fffff,0xffff00002a7a000ff000])),(BitVec.ofNat 152 (word80 [0x830b0b0b0ac24b0a14,0x2c00b0492a7acccccccc]))),((BitVec.ofNat 152 (word80 [0xfffffffffffff00000,0x3996fff00000])),(BitVec.ofNat 152 (word80 [0x40c0c0c03000c0c18,0x3024c092309688888888]))),(0x0,0x0)]
def g229C : List ColumnInfo := [(64,0,165,0,7)]
def g229A : List (List Nat) := [[],[117],[32],[32,117]]
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
theorem g229G : graphValid g229 (boundsBefore K181) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low229 : Lower true (varsX 229) (graphGoal 229) 8 := lower_forest (g:=g229) (i:=0) (hints:=2) (before_sound K181 V181) g229G g229T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K229 := extendKnown K181 8 [(229,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V229 : Known true K229 := extend_ok (m:=229) V181 low229 (by decide +kernel)
def g63Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3fffffc1ffff60ac8,0x4caee8000007f01fc07f])),(BitVec.ofNat 152 (word80 [0x280280084044060880,0x400ce80a142850a14285]))),((BitVec.ofNat 152 (word80 [0xfc003ffffffe021c2c,0x13d9d30003f800003f80])),(BitVec.ofNat 152 (word80 [0x304b04500208221c28,0x3c941264c993264c993]))),((BitVec.ofNat 152 (word80 [0xffffc0001ffffbf0cb,0x81210b01fc000fe0007f])),(BitVec.ofNat 152 (word80 [0x400c0160809009404a,0x12103142850a142850a]))),((BitVec.ofNat 152 (word80 [0xffffffffe0000824f7,0x691ab200000000003f80])),(BitVec.ofNat 152 (word80 [0x8290298014e04820d7,0x6812b2d9b366cd9b366c]))),((BitVec.ofNat 152 (word80 [0x93710,0xa28774fe00000fffc000])),(BitVec.ofNat 152 (word80 [0xe00e010700803700,0xa2821060c183060c1830]))),((BitVec.ofNat 152 (word80 [0x4c917,0x7e4005fffffff0000000])),(BitVec.ofNat 152 (word80 [0x30030021801008015,0x1c000481020408102040]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g63C : List ColumnInfo := [(0,8,53,2,8),(8,0,55,0,8),(1,0,62,0,7),(2,8,53,0,7),(4,0,59,0,7),(16,0,47,0,7),(32,0,31,0,6),(5,0,58,0,4),(17,0,46,0,4),(20,0,43,0,4)]
def g63A : List (List Nat) := [[],[66],[32],[32,64],[64,32],[64]]
def g63D4 (j : Nat) := if j=0 then 0x1a2b6460b5454120 else 0
def g63D5 := limbs80 #[#[0x50940483aa5954250120,0x483ca5515250120eab65,0x5915254120d697554940,0x54120e6b64549504839a,0xb6982d51504835add152,0x5d9544838ed935454120,0x4832ed9170d51208fb80,0x1d37059520a3d85d9354,0x8d01d345ca0d141c032e,0x8080002836294c]]
def g63H5 (j : Nat) := if j=0 then 0xc0e else 0
def g63D6 := limbs80 #[#[0x3b4a92a0907a94250120,0xfd2a4a02412fdd16548,0x837db2a80906f9655012,0x20fd6e4a8241fa549504,0x483bdaa2a09077954541,0x120df6c8a8241be59150,0x44833eb2aa8905fb7454,0x51209feecaa2413f5d95,0x544835fb26a8905f970d,0x591209faedaa2419f597,0x1654827ebaec8904ff75,0x59520b7ee8b2a417edc,0xd1654835e3a2ca906fb7,0x70995209fee8b2a41afd,0x5d3654827ebb4ca905f9,0xb7054950bf6e0a92a13f,0xfd93525433fb22a4a877,0xbf7458950afae9a92a19,0x3fdd162d427eba6c4a85,0x78a8431e4d85f258a401,0x5610fb7aba1b6d564309,0x75a2b74ea0cee5d288dc,0xee46ef5da1cde3b037bb,0x8178f049085f3f6ba9c,0x82141100f1e010649ce1,0x810000808205c7806102,0x80101c4080141c80801,0x400e0e2043820700400a,0x8604002005041020050,0x35040000a8]]
def g63H6 := limbs80 #[#[0xe544b00000000081803,0x22e98005940000000000,0x60800000002000000004,0x1c2800001,0x30d6100000002600,0x35380c003b0000a400,0x240000000000000,0xe12400009000000005b3,0x2c0000034e003946a242,0x40c00000000000000a,0x7b15140008380051008c]]
def g63D7 := limbs80 #[#[0xf59120fe54120fe50120,0xd9520bf59520bfd9120b,0x8950dfd4950df54950bf,0x120ff55120bf58b50bfd,0x20ff59520ff59120ffd5,0xff58950ff54950ff995,0x90ba2585a0c000ffd895,0xc9ce691865a144481023,0xb1c159079aa528ba107,0x648b3242c461f3906207,0x3186c55cc7149207c465,0x522105c731c4c4792217,0x54d62cc51e2cd41851b3,0x51c6185887105506cc4c,0x88710920789516245019,0xf1c065221624501c4195,0x60940c75540]]
def g63H7 := limbs80 #[#[0x4450429e3e01c138310e,0x3130a2e8416453c0300b,0x40006035451011035088,0x6266fa84001012012c82,0x4d108811521e87fc4260,0x61e01206000024d00050,0x91259000034860929a60,0xe98368283ac19c1b0006,0x9272410000205b85c000,0xc00040a000103b8a0806,0x4a2650aa83000712603,0x2b00780b000140000000,0x4065838cc3211a8288,0x92d44cd62003c000acf0,0x189ca4610700b42a,0xe057243c8e53ea22]]
def g63D8 := limbs80 #[#[0xc79aa407fd43faa1fd20,0x98d13568298d131ea414,0x1ad046]]
def g63H8 := limbs80 #[#[0xcf4,0xf47000e31000e6ab0e00,0x29000000008e21000000,0x9f010410000000000000,0xd28f02000f26000c0,0xe0b000e3010c000,0x540f000000000000,0x2f56b00000031000,0xd24000000706,0xb030000000000000000,0x687b2720400000,0x1140d80f000707000,0x10ae050]]
def g63D9 (j : Nat) := if j=0 then 0x1542317f else 0
def g63H9 := limbs80 #[#[0xf00000000a4803a200,0x99aa000000000b200000,0x2c9852100000]]
def g63L : Nat → Packing
  | 4 => (1,5,4,0,0,0,0,g63D4)
  | 5 => (13,4,4,0,0,7,0,g63D5)
  | 6 => (39,3,4,0,0,9,0,g63D6)
  | 7 => (18,2,4,0,0,10,0,g63D7)
  | 8 => (3,1,4,0,0,7,0,g63D8)
  | 9 => (1,0,4,0,0,0,0,g63D9)
  | _ => emptyPacking
def g63I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 6 0 2 g63H5
  | 6 => lookupWord 7 79 3 11 4 3 g63H6
  | 7 => lookupWord 18 89 6 13 6 3 g63H7
  | 8 => lookupWord 8 83 2 12 5 3 g63H8
  | 9 => lookupWord 2 23 0 9 2 3 g63H9
  | _ => fun _ => none
def g63 : Forest := ⟨63,9,fun i => g63Y[i]?.getD (0,0),g63C,g63A,g63L,g63I⟩
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
theorem g63P5_0 : block g63 5 0 13=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g63B5 : block g63 5 0 13=true := g63P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P6_0 : block g63 6 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P6_3 : block g63 6 3 36=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g63B6 : block g63 6 0 39=true := (@block_merge g63 6 0 3 36 g63P6_0 g63P6_3)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7_0 : block g63 7 0 10=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7_10 : block g63 7 10 8=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g63B7 : block g63 7 0 18=true := (@block_merge g63 7 0 10 8 g63P7_0 g63P7_10)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P8_0 : block g63 8 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g63B8 : block g63 8 0 3=true := g63P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P9_0 : block g63 9 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g63B9 : block g63 9 0 1=true := g63P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63T : checkedTables g63 9 := by
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
  · exact g63B8
  · exact g63B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63G : graphValid g63 (boundsBefore K229) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low63 : Lower true (varsX 63) (graphGoal 63) 10 := lower_forest (g:=g63) (i:=0) (hints:=4146) (before_sound K229 V229) g63G g63T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K63 := extendKnown K229 10 [(159,[49,117,101])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V63 : Known true K63 := extend_ok (m:=63) V229 low63 (by decide +kernel)
def g95Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x1fffff87fff6a323,0xb48680000007f01fc07f])),(BitVec.ofNat 152 (word80 [0x9402801102206a022,0xa082850a142850a14285]))),((BitVec.ofNat 152 (word80 [0xffe003ffffff0205ed,0x63cb000003f800003f80])),(BitVec.ofNat 152 (word80 [0x2184b08a010422056d,0x224b13264c993264c993]))),((BitVec.ofNat 152 (word80 [0xfffffc0007fffb1ad1,0x92518001fc000fe0007f])),(BitVec.ofNat 152 (word80 [0x200c02c20480912d1,0x12400a142850a142850a]))),((BitVec.ofNat 152 (word80 [0xfffffffff80008caba,0xcb8c00fe000000003f80])),(BitVec.ofNat 152 (word80 [0x4c090130027048ca92,0xc9842c58b162c58b162c]))),((BitVec.ofNat 152 (word80 [0x92d42,0x4c3f7f0000000fffc000])),(BitVec.ofNat 152 (word80 [0x700e01c04380800d00,0x4c3d3060c183060c1830]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x4d414,0x28607ffffffff0000000])),(BitVec.ofNat 152 (word80 [0x801002000400000000,0x4081020408102040]))),(0x0,0x0),(0x0,0x0)]
def g95C : List ColumnInfo := [(1,0,94,0,8),(2,0,93,0,8),(4,0,91,0,8),(8,0,87,0,8),(16,0,79,0,8),(10,0,85,0,7),(0,2,21,72,6),(0,8,21,66,6),(64,0,31,0,6),(3,0,92,0,5),(5,0,90,0,5),(6,0,89,0,5),(8,2,21,64,5),(17,0,78,0,5),(18,0,77,0,5),(20,0,75,0,5),(64,2,21,8,5),(64,8,21,2,5),(21,0,74,0,4),(66,0,21,0,4),(66,8,21,0,4)]
def g95A : List (List Nat) := [[],[66],[49],[49,66],[32],[32,64],[32,49],[32,49,64],[64,32],[64],[64,49,32],[64,49]]
def g95D4 := limbs80 #[#[0x50c8ae1192d915254110,0x30c4ae13925d152d41]]
def g95D5 := limbs80 #[#[0xa8221a2b6460b5454120,0x6454950442cd325b22a4,0x94aa2a5b82848868ee13,0x12214e9921977050910e,0x5dc1424429b32632ee0a,0x4c94cbb82848843e6606,0x2210f9989977050910a7,0x5c86544315ee8c16c8a9,0xc1a84a8a809053ae4184,0x41aa98650b5150120dc5,0x49404839572eb2a84a02,0xa2eaa92809078ae59545,0x1c6b965d55250120e95c,0x55048369706a92a2a824,0xaa4b8aa0904ce6508558,0xe29645515254120da5c1,0x50483a56e8aa2a4a8241,0xa8a92a09059ae5954549,0xab84dd15254120f15b26,0x483c56e9b22a4a82419,0x8a92a09059aa5f645495,0xb745537254120d95c26e,0x48335309ba6e4a8241d2,0xaa2a0905ca64b5455150,0x6460b5454120d55b2305,0x8256f28c36a2a8a41e2b,0x2ea290527e5165dcd514,0x4e0176d452085fca30fb,0x287b283aacab0a418b88,0x2a89062ee13805d95448,0x5c970d5120c74c1301bb,0x13ec9c1ae3aa241cab64],#[0xca9066ae0b80dd165483,0x17159520e55ba6e5b82,0x38e9c1ae2b2a418b874e,0xa90627dd3835c5654831,0x3745952085f4c0e8b8ac,0xf26c0ee8b2a41aab82e0,0xa855ae497454b5054293,0x6258550c9dc22e8a96a0,0x9ba6e0a92a189f84dcd,0x852ee4174d9352543273,0x458b50b1dc82e9b26a4a,0x9018030018af74e096,0x8210781b060150480f03,0x5c16451124410f8360b,0xc88214821d4721a86719,0x4aa29c9f270992588e22,0x8db338cb2f8b62ccb02b,0xfd3e8f73a8e7390e137,0x431094190340,0x8080d05400400000000,0x814003a103a1020648,0x28540040600080050,0x1d182000001a0800,0x11801016168011800800,0x1322c81000000006]]
def g95H5 (j : Nat) := if j=0 then 0xa0a10099 else 0
set_option maxRecDepth 16000 in
def g95D6 := limbs80 #[#[0x54940483aa5954250120,0x4835a5d55250120f2954,0xd915254120e696454950,0x54120d6b74549504839a,0xe3b64d5150482da60b54,0x5d9544822fe1176d4520,0x4832ed9170d51208fb80,0x1d37059520a3d85d9354,0x54110f6952509504432e,0xf6b7254950442de61542,0x549504439ed915254110,0x4439e2195254110b7b84,0xa1f6254110af984d8950,0x54510bbb845c950442be,0xcf774d8951442fce0142,0xdc951442bd6136254510,0x4437a54b70509109f584,0x9977050910cf865dc142,0x509109f985dc1424433e,0xaed8219542443cb55152,0x19542442b760c6550910,0x442b7e0d65509108fd87,0x60a65509108ff8759542,0x509108fd8799542442bb,0xaed82d91524427ee0175,0xd91524432fdd36454910,0x4423fa1f64549108fd87,0xe1574d8910a7d859d952,0x195108ff845d7624423f,0xced845c8654423fe1172,0xdc9654433be117219510,0x4823fe1172995108fd84],#[0xe0d5150120fa94254540,0x50120fa942d4540482f6,0xaf986d4540482fa60b51,0x54940483ea5515250120,0x4837a5d55250120fa984,0xe096550120deb8754940,0x50120ebb8459540483ba,0xf6952545504833ee1d65,0xd4550482f6e0d5154120,0x482fa60b5154120f6952,0x2156154120f695258550,0x54120b7b8558550482de,0xbeb825c550483da54971,0xdc550482f6e0d7154120,0x483da5515254120f6952,0x5915254120f6b5454950,0x54120eeb6454950483ba,0xf6a65549504837add152,0x54950483da5d15254120,0x483da5537254120f6b74,0x5d37254120f6b54dc950,0x54120deb74dc9504837a,0xf3b5455150482fa61372,0x551504836edd15454120,0x483da6095454120afb86,0xe195454120f3b7455150,0x54120be982d51504839e,0xf6982d5150483aed9354,0xd9150483aedd36454120,0x482fae097454120afa87,0x60a6554120deb82dd150,0x54520bf180d4551482fa],#[0xcdd64dcd51482bd61b51,0xdcd5148337d937354520,0x48337d977354520cdd65,0x61b7454520cbf74d9151,0x54520abf84595514823f,0x9df835d9514827ee0176,0xdd9514826fe117654520,0x4837a5c970d45209f980,0x59170d4520deb825c351,0xd4520cfb645c3514833e,0x8fd87593514827ee1170,0x5d3514823f61f64d4520,0x482afe1165d45208ff86,0x61f65d45208ff8759751,0xd4520abf845db514823f,0x9bf845db514827ee0176,0x5db514833ee0176d4520,0x4832fe1176d4520cbc84,0x61e76d45208ff845db51,0x585209f980ddb514823f,0xc7c7559561482afe1165,0x1d5614831fdd56558520,0x4826f61075585209dd83,0x6037155120de9725c154,0x551208fd86dc5544827e,0xe3d65d5154482ee60354,0x59554482af61b5455120,0x4839ee016555120abf84,0xe017655120e3f8459554,0x55120cfb805d954482be,0xde9725c3544833e60376,0x5c354483aed9170d5120],#[0x48277e0d71d5120deb82,0x61764d5120cbf645c754,0xd5120abd87d9354482af,0xe3f84597544839ee0165,0x5db544833ee0176d5120,0x4832fe1175d9120cbf84,0xdd37059520deb72dc165,0x59520cbf76dd1654836e,0xcbf86dd1654836ee0374,0xdc165483badcb7059520,0x483aedd37059520eb874,0xe017159520af984dc165,0x59520adf835c565482be,0xcbf745c5654832f1d171,0xdc565482afe117159520,0x4832fdd37159520cbc74,0xe017459520abe871d165,0x59520ebb80dd165482be,0xcbf81dd1654832f60774,0x5c6654837a5c97099520,0x543dad8952d41509df83,0xe1152d4150d797454b50,0xd4150bbb8458b50542de,0x9fb845cb505437a5cb62,0xd895154357dcd5254550,0x5433b5cb62d4550cdf73,0xdc952585509fb805cb51,0x58550d5f73549615435b,0xabf845896154337dcd62,0x58b6154337dcf6258550,0x5433b5cb62d8550abf84,0xd8b70549508ff845cb61],#[0x54950d7954dc152543ba,0x9f984dc1525435ed5370,0xdc1525432fdd36454950,0x543dae0b7054950f6b62,0xdd37054950d7974dc152,0x54950b7984dc1525435e,0xd3f74d9152542dbe0964,0xd93525439be0b6454950,0x5427ee0174d4950cbd74,0x5d364d4950b6f8259352,0xd4950e3d74d93525434f,0xd7b805d352542dee0174,0xdc1625436e1d37058950,0x5436bdc87458950dbb74,0x60b64d8950dbb80dd162,0x58b50adf835c762542bb,0xafb805d162d42bbe0964,0x5c3515463fe1172d8151,0xd46bee0162583519f782,0x6137258351abf845c960,0x2b821012009c0600023f,0x5851c4e04c846840833c,0x869c68464860c5d05945,0x81c7e07c87447086f06d,0x789188b88a088884c834,0xb04aecab0a74a389d89,0xca8c90c54bf4bb8b7cb4,0x70decdd4d98d5ccfccc0,0x50f90bd038ffcfc0ed0e,0x3753392912551f519513,0x8162157953d5014593d5,0xd89d83d7dd77d71d6bd6],#[0xb85b25ae9aad9e195d8f,0x71d35cf9cbdc81c21bc1,0x1f21f09ecde91e31dadd,0xc60ae09605a01dfbdf8,0x4620a1ce19215611a102,0xe3d23ba37e3422be2822,0x52e4ce4b647a43e42640,0x8a67263661e5e25a656a,0xa7aa76e73271a7026c66,0x9ba97e9428e28a686a80,0xa6afeac2a86a6ea329f6,0xed32cf6cbaca2c42c06b,0xeb2e76e3adfede6daad6,0x7b03efdefa2f66f2aeca,0xb1e31cb16b10b0cf0b70,0x3ab36f3572f72732371f,0xe34cb48f45343b4233e7,0x36275eb5af57353751f4,0x73b72370b6cf6b769f66,0xbb87f8438077a778f777,0x39b797b9639278eb8d38,0xb13ad7a9ba5fa47a0b9f,0xb7c9fc63c4bc0fb8bb4f,0x415240bd5fd47d0bccfc,0x31d8c08181ba4a106120,0x28363b1814e4101e0d05,0x82450441b64080a0f724,0x10903c2040f1e84206f0,0x200401630200068c0b90,0x40d1805001f041000080,0x21161820002002001a30,0x881d10002d16002c0010],#[0x3020804020800407440e,0x40400000080400101810,0x4006039017202e46004e,0x520ac2801b09820ac682,0xd05508302020d041e0d0,0x2b481034041008109020,0x9d1ac680134808294810,0x40020ac21d1900160810,0x244048209068d6105824,0x305c2041202082763210,0x4040500040542c00480a,0x7028005007204087204e,0xa043928500141ae4a10,0x20804083c84103410002,0x1c1030a061408081a0,0xc209056404060804100a,0x2041ac2080c00208041b,0x8080068c1d18282c0040,0x10003a3040c08181018,0x20485a120060007800f0,0x841e002001c204003020,0x78008001d08204008406,0x81010008080000,0x211002047002e0020604,0x20204051408080208081,0x424080a40748080010,0x40f0a80102348c2a008c,0x120648084810309c0080,0x14082815202069010902,0x50a041408481b2308202,0xc2b182000017202e4850,0xc80b0010000258420758],#[0x502038dc2122ac8640e,0x40c0038004003000f001,0xd0010982010400081400,0x1010000002001a306c80,0x24006800a8a8010003,0x40800102800e0010002,0x7440820101020020100,0x4005028ab21903510340,0x720200001e182000000]]
def g95H6 := limbs80 #[#[0x60c3001a18581280080f,0x4b80022031e1004ad90,0xe5d07708005a0000c02,0x4a5841a9883880700c6,0x2005601d026e8f300200,0x5948d8a214143019207,0x9c99326a000400fa0be,0x1417a01ae04a0a0a19c8,0x4a75833a1252cf21c000,0xaf00000006865299ec1a,0x9202440c0057e11122b6,0x30adc1b3a104000001c3,0x49a000023e0004ab8487,0x55222683c414f0200901,0x7e13b03f701c810e8d70,0x1c10a0ec02a692583,0x2ef817689208fc0b0000,0x6835807b815c08c46ae,0x800068ce0982a6000000,0x610d0694132a9f227,0x1c1180000000,0x88273aabb283a1ac1000,0x30600000000017302,0x12c2a0000506e2028062,0x14]]
set_option maxRecDepth 16000 in
def g95D7 := limbs80 #[#[0x26eb98ca884ed7219510,0xf5284a024137dcd6544,0x826eb9ec290769525412,0x2097ae832a413d5c4654,0x4426fb9ac3a84bf74595,0x510df6c4a8221de54950,0x14437bb12a2886f76448,0x8910bf6e0a12217ddc95,0x624427eba6c4884ff745,0x595109fae432a213f5d7,0x9404827eb94ca884ff72,0x254120df2caa0241fa54,0x5150483f5b92a0907e95,0x6454120ef6a8a8241de5,0xdd1504837db22a0906f9,0x970d4520bbee6a8a417e,0xf595544827ebb6a2905f,0xfd7655120cfccaaa2419,0x7e5c3544827fbb2a8904,0x67d65d5120d7ec9aa241,0x13f5d7644827ebb6a890,0x5bf7459520bf6e0b2a4,0x41af1d1654837db82ca9,0x904ff7459520d7ee8b2a,0xa413f5da65482fcb84ca,0xa877952d41509fae932,0xaa177dcd51542fcb96a,0xa4a84fd72d8550bbee6b,0xa92a1dedc152542fdb82,0x6a4a867f64d4950cfec8,0x9b12a16fdd162542beba,0xa2c5a867d64d4b509fae],#[0xe1a8aa33f5cb605467fb,0xa12a0884ff7258351bea,0x6e4a8221fe5c950443fc,0x6a9284887f54254510ff,0xfacaa1221bf19542443f,0x7fb2a84886fe6550910d,0xefaa8a92217f5d542443,0x2ffba2a4886ff6454910,0xdfceca9221bf1d95244,0x83fda8a80907f9515012,0x20ff6a2a8241fe545504,0x483fcb8aa0907f961541,0x120ff2a8a8241fedc550,0x483fcba2a0907fb5454,0x4520ff4caa8241fedd15,0x51483fab0aa2907f7515,0x54520dfac8a8a41f7dcd,0x551482ffba2a2906ff64,0x654520dfecaa8a41bf59,0xc351482ffbb2a2905fd7,0x64d4520dfac9a8a41fe5,0x59751482feba6a2906ff,0xd76d4520dfecba8a41bf,0xf9db51482febb6a2906f,0xfd6558520bfeeda8a41b,0x7fdd561482fe3aac2906,0x5ff7155120ff2e0aa241,0x1bf59554483dfaa2a890,0x6ff7655120dfaecaa24,0x417f5c754483fcb86a89,0x906fd76d5120dfacbaa2,0xa417fdc565483fdb82ca],#[0xa906fe6559520f7ee8b2,0x2a41bfdc5654837eb8ac,0xca906ff7459520dfae8b,0xa82a17f5c665483fcb84,0x2a2a87fb62d4150ff2c5,0x5a8aa1bfd8951543bea9,0x96a2a86ff62d4550efaa,0xc4b0aa1df54961542feb,0xb92c2a86ff6258550dfa,0xac5b0aa1df54b61542ff,0xeb96c2a86ff62d8550df,0xfaa8a92a1fedc152542f,0x7fb22a4a877f5454950e,0xefec8a92a1df59152543,0x2feba6a4a86ff64d4950,0xefec9a92a1df5935254,0x43fdb82c4a877d74d495,0x50dfac8b12a1fbd89625,0x543de3a2c4a86ff64589,0x950bfee8b12a1efdd162,0x25437fb26c4a87fb70d8,0x8950dfae3b12a17f5d36,0x625437eba6c4a86ff71d,0x58b50dfac8b16a1bfdd3,0x162d437eba2c5a85ff74,0x258351dfac4b06a3bfdd,0xc960d477eb92c1a8dff7,0x816008a02e0098001bfd,0xa0da06182b0132086039,0xb850026212208984001d,0x8a1be0d5866030216e0a,0x1d88a041a1fe0f987503],#[0x5822ae14b8a104ca2521,0x19b8cc064a30a1738b40,0x7823a61cb8e006ea35a,0xe22d91208624121ff8f7,0x109e24de26392b091a46,0xa62c195c0a9a53228b94,0x880c1a5f62ef9720b6a5,0x69e34799f0cca64631d9,0x9ba0dc26d63639ad0d52,0xa75a3a39ce0e4270e37b,0x79ef0f6a79e3c79df0ec,0x8a83240da020ff27e63e,0x53a25110a872433a1510,0x1da8e646ba3211828b64,0x4a9a51127a926483a3d1,0x13729a24c7a5e12e2966,0x24ffa7c13c29d24e5a70,0x814a2a3e51ba89143aa1,0xbe553aa51512a7a533a9,0xca163ab0e57fabb15aaa,0xb8a5bbada16aab4659ba,0xafa17b2bd25dfaec1732,0x2c32613b051812c025fb,0xbb2318fac6e62fb15188,0xc2cd6665b2e194ac9e64,0x930023144d0a67fb3c19,0xf00405e4e2c00708451b,0x944860200e5121393881,0x407c2c0101108444203,0x28511c2c010130b00203,0xe4e207c01015930b0396,0x4c562100910018b14404],#[0x85030985100c08261440,0x3159040540c52f0c001,0x4402446408c5a209168b,0x40462e4c008c514131,0x40c4810408c562139317,0x47938f860040287c20aa,0x64c2184440483800a08,0xa151d1820484110d8a1,0x1e02299308408474664,0x22970840c8807c4c2a1c,0xb029040ac2c004a51500,0x180c044851110120c2b0,0x807060301c2c0a4201c,0x1244a092845004293086,0xac2c007060301a42048,0x54012081c180c042a906,0x6e4c20a0f8f0b870228,0x1c08a641b0b022b8f859,0x1c1b8f0b8701908e3c2e,0x80c04487111040121028,0x4c2c0116410170b001c1,0x7801162101044298840,0x1c0101c309f130a87004,0x8b00101a9462763e4e2a,0x1028842726c440a21429,0x1928840f64c0a210444,0xb0060a11a21064c0182b,0x301c064a22229938f868,0xa2204702884040d07060,0x280503080706640301c0,0x8b931680508066085101,0x91b04562812f09101421],#[0x24186c18046091029918,0x1003c7248608528d8a00,0xf43a2810614210e89060,0x42a210090c1a8a003c40,0xc900840244221008182,0x8e083100704402440906,0xe084c484610d0a821611,0x2c283094261468215198,0x2151b082130963c21024,0xc3593082040a640880c,0xa04282192030850d64c2,0xa3c0090a141a8c870040,0x4a313060c8f004c1840b,0xa0644c01314928c4c18,0x4a306a10d128c1a844,0x4001b08406c0084c908f,0xc18928428406a1120e8,0x12843a1051284244c00a,0x844c0068410624c00c29,0x82423c0090a1d93001a,0x28312068700402c2450b,0x42a90224c0088a101b00,0x40081028230b02905120,0x21206108f004c185a4c2,0x8a0f001984312042a90,0x664636112930028324c,0x42b0b01904120419842,0x164620a0c8f00198440a,0xa8c2c183a34010141200,0x92214250a8488440080,0x11450428c882450842a1,0xc2c1a8c8440664a322a],#[0x30b640a8500403130962,0x2890031062a10c188a84,0x1208230034424a2c0102,0xa21435928830f64a2c0,0x864102a899030864804,0x282030a08640c481a20a,0x88424a2082810aa20990,0x228928838aa2083c9302,0xc0a20c890020ac0a2641,0x8420663610c359288324,0x40824c0a211901640419,0xc2190240640823019288,0x64620b0401883c122200,0x19882]]
set_option maxRecDepth 16000 in
def g95H7 := limbs80 #[#[0x50130500b8c101530011,0x9221010062002001420,0x5001021111100000101,0x52811143212300001000,0x1909310100d608012,0x845f000000002232081,0x905260e39434000,0xb4cf145d00000000000,0x54010000309d0000000,0xe018200f703781e9000,0xe0023401e00009011000,0x280,0x0,0x6140000000000000000,0x101300002019000,0x90000c02700000000000,0xf0000000000000000d40,0x50b,0x2000000000000d43b000,0x90be00000000244,0x1074b4d4000,0xa3485000070ec0000000,0xb4cdd48c0000055,0xa025703e000054a0000,0x4015707c00000000000,0xc000000000000801d000,0xcf11a0051d0a40000f0a,0x53a8044b0abb81,0x80000000000000000000,0x4a00000000903db1c,0x91060000000,0x140700000000000],#[0xa4bc34b570dba450000,0x9000092410000000070c,0x600122b6f55,0x10570000000,0x400000000249e0000000,0x679a0d09130e90000b06,0x8094d00cc026753,0xe59a61e4000,0x913ed816c11f000,0xdf0d6000000000000000,0x6110000627ac08e181,0x0,0x0,0x0,0xc000000009406081a000,0x343,0x90000f07100000000000,0xc4abd05520880000480,0xd246f00900003159c11,0x3148000,0x321570cf24390000000,0x0,0x68d40000000,0x10000000051620000000,0xa03b000020eb40c,0xe0000a2c700000000000,0xb075a0de0000844,0xf10d700d800000000000,0x800000000d090a474302,0xb05b00000000349,0x18df19cd00000000000,0x904],#[0x0,0x864900000000000,0x85020000c492000,0x58ce82b1000,0xf0000000000000000000,0xf0dd000040c50000005,0x6000010bca0ba0000000,0x10620000000045cdf03,0x930aa404e905d0000000,0x80000000061290000f4a,0x5000000000000c437f55,0x43eb09700000000023,0x81e600000000000,0xda1ed8cd000,0x608b00000000000,0x0,0x31690000000,0x0,0x704c000054450000000,0x1000040d400000000000,0x70000000091370000d0d,0x5021d153aa26c0bdb08,0x0,0x30000000000000000000,0x206,0x0,0xf000000004041d464000,0xa56c0000715,0x10c80000000,0xe43d0000408f0000000,0x758c000,0xb436000051520000000],#[0xa0000000000000000000,0xac00e00000000040524e,0xf0e14475107a514ac4b,0xd13b60485165b0e2203,0x0,0x440ad08000000000000,0x102400000000000,0x7495000000000000000,0xa089b0a0d0700000000,0x50d0000000000000000,0x4d3000,0x9260f0000201b0000000,0x9f0580000e8190000e05,0x200d100600005117e02,0x558bc4d20000e480000,0x701ca2afc005000,0x8a0d000,0x50500000d0bb000,0x709e00000000000,0x1c6000000000000000,0xa30200000000094bb000,0xe153ee58d0000214ce02,0x3607e00000000e444958,0x7000021550000c08de8d,0x8a00000000000022b,0x60000f00328b4d446000,0x104dc06900000000a01,0xd0e5c0b650d2000,0x90000309ca5370000000,0x57457c0a390b800af753,0xe906600610000b008508,0x747e0000205e402],#[0xb124803cb0a10000000,0x40000000000000000400,0x8e04f80310000000044b,0x3b0350000000010ccc02,0x8000000000000c4c3d07,0x202c00000000409,0x0,0xf05c000,0x5d0c4000020540000000,0x500000000e895e100b0a,0x909,0x2127000,0x30ce00000000000,0x199690b2000,0x200000000000068da000,0x48077017670b7381e109,0xb0780000d10d908,0xb43a000000000000000,0x0,0xa03f40dc0000e0e4000,0xe00008065e09a0000000,0x1500f1c,0x826000030b00000000,0x40a9a89e0000000,0xc060816600000000000,0xf440000040cb000,0x706d0000000,0x8000000000000e067000,0x10e7a103000011d,0x71cd000090c60000000,0x30a600000000458f000,0x9004b06a0000903a000],#[0xf0000115c55790000000,0x2892209,0x9b0b3000062430000000,0x8046501450d5323f224,0x3e646d496e411253b000,0x660b40000b00ba54a604,0xa0073034807,0xf04740e8000,0x76451000000000000000,0xd026de08c00000000301,0x7c096f2c9a557ba0ed0c,0x80000a0b90000328650c,0x60000500a74a4000020a,0x70d30000807dc05a308,0x30820000000091c0000,0x0,0xc597000000000000000,0xd000000e000000000000,0xc46e000000000000e80,0xf02d000,0x0,0x30dad07b00000000000,0x506f00000000000,0x740c00000000a154000,0x3402d55b00000000000,0xaf0c2000000000000000,0x64d5c8740000a13,0xab2aee1db00000000000,0xb0000000014651033a45,0xc0930000b0327994909,0xc0000000000000449d59,0x80c32599413cd06],#[0x84042000010220000000,0x80d98068c07fc43,0x0,0xe0000000000000000000,0x90000000000000000a48,0x2e4cc000000001136b07,0x445990a7100,0x0,0x0,0x20100000aa1d0000000,0xe0530000000,0x947100000000a233000,0x90b5806e9a1a10ae000,0x60000b08100009012000,0xfa1c000030e,0xb0ea0000000,0x0,0x70720000000,0x0,0x661c53049e0df0000000,0xc0000929b00000000c4a,0xb0000f06b62b20000a55,0x15d00000000000071b,0xe01fe04500000000000,0xa0000805634d781d6000,0x845e0000d1c1301,0xad4aad038000004ce000,0xc9a0b10000000060c,0xb0a2d16300000000000,0x7039000,0x0,0x0],#[0x224ac000000000000000,0x545c002bf0830000210,0x504b000000000000000,0x0,0xe040fb0ad00000000000,0x549430990000000038d]]
def g95D8 := limbs80 #[#[0xd48510fe54110b7d8d51,0xd8910bf58910fd54510f,0x9510bf59510bf19510bf,0x120fe50120bfd9510bf9,0x20bf59120bfd8520fe54,0xbf59520bf19520bfd91,0xfed4150bfd9520bf9952,0xfd4950df54950bfd8550,0xd4b50bf58750bfd8950d,0x4551bfd8151bf58b50df,0x910bf58351f7d8d51fdd,0x20ff54520ff54910ff50,0xff55120ff58520ffd45,0xff99520ff59520ffd512,0xf58550ffd4550ff54550,0xd4950ff54950ffd8550f,0x8b50ffd8950ff58950ff,0x2060037000ff58351ff5,0x18615d1340fd0d40ab08,0xb327524521c2011d11af,0x73b038e36533c31a2f12,0x4eb4bb4994694474173e,0x496195e25a456d54451b,0x87a17637337036d368e6,0x90d8e48ad8688388017d,0x145202900e33262c1047,0x500290151400a4040193,0x228a245088a045202e4c,0x405c808262802228e432,0x917262802228b931408a,0x890c1016524264c51480,0xca4854a4090600890cb0],#[0x91020386ca9050c20386,0x2140ca40708080800640,0x10242804480a10386159,0x80b93100224050e1b292,0x5007c995140132628094,0xd911658030ac8472904,0x14020264078834028307,0x480a09908c0219510c45,0x626364c5804050c364c,0x48511931208a283c98b0,0x825222811480e884908a,0x251c5444818a42809488,0xb129490d1120a110a0,0x48848706010468491242,0x24311090e0c046848122,0x121031e12430885031e1,0xa0084a423890a0102831,0x27262809480e91109890,0x1208a00f931404a40528,0x8981905114440623931e,0x8a00e9089015931e1808,0xb911118040522431e1c8,0x3262402228]]
set_option maxRecDepth 16000 in
def g95H8 := limbs80 #[#[0x3a07804fa020102c7c03,0x804060002c430001436,0xc80400020086c0711000,0x30101e04010005a08091,0x94e85c04081d00004f22,0x445810002d2f990003,0x5100a010e810040b0000,0x8000e1a130082a387a83,0x79c9020020303c082e26,0x2902806240c13ddf480d,0x4a2b0200c2831831a414,0x106bd17d42b646e6c2a8,0x400dc0cd89b982978157,0x81efd03846739152c07c,0x456609cf003ce0d8c962,0xc95f0a6040a18093816d,0x23800014501949bd56d,0x220c14e516dd1dd8579,0xd10f8189d07446540003,0x77409a82d195e00003,0xc1680001ca4c00029497,0x414ac18e10d922900003,0x40605080c24a84500001,0x4273863bc01cd05d422c,0x4299d4590010000302bf,0x9100000001d4c1fa4126,0x1c680c8946800020572,0xd0d090b5845d8633d4a7,0x4175e2476133c4796138,0xc15c00010a3f867fc2a3,0x829151f5c180148e801a,0x688020d8455c96855b7],#[0x4a12071c4ecc2c3419a,0xc575915d45ff4a4085aa,0xc5b881f784d5210c095b,0x44034a18443a127d0265,0x50afc219c4d0c04700c4,0x292e019540be005c41be,0x269310677c1d1,0x44c891cc0815249899c,0x5a58c543c229803481e2,0xff843080e740e06947,0xa08e13f855b00d100ab,0xc00542258137526a41b5,0xc6e8864f40940003147f,0x90e7427fc0b4c1115058,0x4818c275c67810e889d1,0x3011dc043c09d80ef,0x8152c48400035207d588,0xc56c109841ca2114,0x847d8637412e15810024,0x825401c2c10a4203c28a,0x8166d1735073906f06df,0x802f86604ac0c2128105,0xc2e495e9851c0170c06e,0xd5f701388070862c0243,0x4a382284a12000f5c2dd,0x4a4aa939548982d78569,0x4a14e0f6915741ea0a29,0x41b1c2c500a509ae41df,0x1001595820b425dc050,0x42858469603e859980ad,0x4118582ac9180000c2a7,0x98f8648404c01f381d9],#[0x50c7502ac2cf40e94683,0xb80000612f55e401cd,0x458a826b421682040003,0x9a042d811aac459c143,0x408d06e2c26ec956c29d,0xa12400028033811486a1,0x89fb49e3018609654a5d,0x41b8000102b00002d161,0xc1af292700b000014436,0x1a186588829c0d40001,0x1798583899bd602c251,0x4f1c42bc68e403b8000,0x80dc0002515a293e855e,0x1019e407ac25a442e,0x899180d80089413e1a48,0x8640828c0001024c0001,0x81e40001c0540132,0x283c246c0f000030028,0xc52481aa42794512c50a,0x1614650d45f103295df,0x848086640000863f6914,0x92240000603a00488488,0x821cc06515f80001005b,0x644ca5bc1a6c4e142ca,0xc23f815b55efc5e8c009,0x41200001c0fac46c0015,0x85c34a5082e2810cc952,0x10262865f0a36,0xcabf81ffd0ec00848518,0x814455f31276c23349bc,0x406b1244002349b042e9,0xe14782aea83f1259017c],#[0x52790192c235c0c0c2ba,0x2012b]]
def g95D9 := limbs80 #[#[0xd51ffa87f543fa41fd10,0x51b0259b138a803fea3f,0x410202548526489000,0x101464648a50101a48a5,0x248a02051549228]]
def g95H9 := limbs80 #[#[0x84c0051e081030404100,0x1e9833c44009040089a1,0xd81500010aa022ca0112,0x207800004b7004f07,0x20f047c2d00000005048,0x2d28402a215f05a88c79,0xb0880000003028000086,0x1c087928d2070003870,0xa0e9f3180c562428000c,0x7131780c04400bec6eb4,0x4037140a290000da0415,0x6d807045900000000002,0x700010ab000210bb00b8,0xa1ef1b040f285b01,0x24a2508dc100000094,0x51b4881488809d44b0,0xd161000380bc0af62d00,0x54780000000421a86,0x60360610003c060000,0xc004000000201450c00,0x3142972a3962306800,0x230000502400090c4000,0x93045508222850009088,0x68980000000110981bb5,0xc258206565006101644a,0x300000000000000da80,0xe80380004093c8498201,0x801680a0098d07445ac2,0x1051207661f32a5813,0x1c0851bc819000042c0]]
def g95D10 (j : Nat) := if j=0 then 0x2080513f else 0
def g95H10 := limbs80 #[#[0xc21b0247a8950714980,0x480000090ec1800001d4,0x50a0a8810000009,0xa0450000589e20002828,0x580]]
def g95L : Nat → Packing
  | 4 => (2,6,5,0,0,3,0,g95D4)
  | 5 => (57,5,5,0,0,10,0,g95D5)
  | 6 => (237,4,5,0,0,12,0,g95D6)
  | 7 => (187,3,5,0,0,13,0,g95D7)
  | 8 => (50,2,5,0,0,12,0,g95D8)
  | 9 => (6,1,5,0,0,8,0,g95D9)
  | 10 => (1,0,5,0,0,0,0,g95D10)
  | _ => emptyPacking
def g95I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 5 0 8 1 3 g95H5
  | 6 => lookupWord 25 127 7 14 6 4 g95H6
  | 7 => lookupWord 111 1123 4 16 8 4 g95H7
  | 8 => lookupWord 98 431 9 16 8 4 g95H8
  | 9 => lookupWord 28 157 7 14 6 4 g95H9
  | 10 => lookupWord 4 31 3 11 3 4 g95H10
  | _ => fun _ => none
def g95 : Forest := ⟨95,10,fun i => g95Y[i]?.getD (0,0),g95C,g95A,g95L,g95I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P4_0 : block g95 4 0 2=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g95B4 : block g95 4 0 2=true := g95P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P5_0 : block g95 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P5_1 : block g95 5 1 56=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g95B5 : block g95 5 0 57=true := (@block_merge g95 5 0 1 56 g95P5_0 g95P5_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P6_0 : block g95 6 0 13=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P6_13 : block g95 6 13 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P6_109 : block g95 6 109 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P6_205 : block g95 6 205 32=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g95B6 : block g95 6 0 237=true := (@block_merge g95 6 0 109 128 (@block_merge g95 6 0 13 96 g95P6_0 g95P6_13) (@block_merge g95 6 109 96 32 g95P6_109 g95P6_205))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P7_0 : block g95 7 0 10=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P7_10 : block g95 7 10 59=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P7_69 : block g95 7 69 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P7_165 : block g95 7 165 22=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g95B7 : block g95 7 0 187=true := (@block_merge g95 7 0 69 118 (@block_merge g95 7 0 10 59 g95P7_0 g95P7_10) (@block_merge g95 7 69 96 22 g95P7_69 g95P7_165))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P8_0 : block g95 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P8_1 : block g95 8 1 30=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P8_31 : block g95 8 31 19=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g95B8 : block g95 8 0 50=true := (@block_merge g95 8 0 1 49 g95P8_0 (@block_merge g95 8 1 30 19 g95P8_1 g95P8_31))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P9_0 : block g95 9 0 6=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g95B9 : block g95 9 0 6=true := g95P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P10_0 : block g95 10 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g95B10 : block g95 10 0 1=true := g95P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95T : checkedTables g95 10 := by
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
  · exact g95B8
  · exact g95B9
  · exact g95B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95G : graphValid g95 (boundsBefore K63) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low95 : Lower true (varsX 95) (graphGoal 95) 11 := lower_forest (g:=g95) (i:=0) (hints:=4146) (before_sound K63 V63) g95G g95T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K95 := extendKnown K63 11 [(95,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V95 : Known true K95 := extend_ok (m:=95) V63 low95 (by decide +kernel)
def g111Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xc007ffffe0ffff7226,0xa10bae00000fc003f03f])),(BitVec.ofNat 152 (word80 [0x82500a004204403202,0x21032a05145145145145]))),((BitVec.ofNat 152 (word80 [0xfff800ffffffe0395a,0x8666308003f000fc0fc0])),(BitVec.ofNat 152 (word80 [0x602c02800082390a,0x844210030c30c30c30c3]))),((BitVec.ofNat 152 (word80 [0xffffff0000ffffad84,0xb0d842c0fc003f00003f])),(BitVec.ofNat 152 (word80 [0x80300b0409000984,0x905800ca28a28a28a28a]))),((BitVec.ofNat 152 (word80 [0xffffffffff0000804d,0x6956a9ff000000000fc0])),(BitVec.ofNat 152 (word80 [0xb01402c002e048044,0x2914a9dc71c71c71c71c]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x9171,0x18b1dc0000003ffff000])),(BitVec.ofNat 152 (word80 [0x2c0580b008b0088071,0x8a0c430c30c30c30c30]))),((BitVec.ofNat 152 (word80 [0x4e93,0x4f80057fffffc0000000])),(BitVec.ofNat 152 (word80 [0x300600c010c0104411,0x42800420820820820820]))),(0x0,0x0),(0x0,0x0)]
def g111C : List ColumnInfo := [(32,0,79,0,8)]
def g111A : List (List Nat) := [[],[32]]
def g111D8 (j : Nat) := if j=0 then 0x7f else 0
def g111L : Nat → Packing
  | 8 => (1,0,1,0,0,0,0,g111D8)
  | _ => emptyPacking
def g111I (_ _ : Nat) : Option (Nat × Nat) := none
def g111 : Forest := ⟨111,8,fun i => g111Y[i]?.getD (0,0),g111C,g111A,g111L,g111I⟩
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
  · exact (rfl : block g111 4 0 0 = true)
  · exact (rfl : block g111 5 0 0 = true)
  · exact (rfl : block g111 6 0 0 = true)
  · exact (rfl : block g111 7 0 0 = true)
  · exact g111B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111G : graphValid g111 (boundsBefore K95) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low111 : Lower true (varsX 111) (graphGoal 111) 9 := lower_forest (g:=g111) (i:=0) (hints:=4146) (before_sound K95 V95) g111G g111T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K111 := extendKnown K95 9 [(111,[]),(123,[66]),(207,[49,117]),(219,[49,66,117]),(222,[32,49,64,117])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V111 : Known true K111 := extend_ok (m:=111) V95 low111 (by decide +kernel)
def g119Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x7fff803ff83ffffffe,0xc00f44693000f000f0ff])),(BitVec.ofNat 152 (word80 [0x502805080400100,0xc00b0009111111111111]))),((BitVec.ofNat 152 (word80 [0x83ffffc0003fe0ff81,0xca6953a4400f000f0000])),(BitVec.ofNat 152 (word80 [0x85603056102821208,0xca2953a0477777777777]))),((BitVec.ofNat 152 (word80 [0x3ffffffffc000fffc,0x85b0769090f000f00f0f])),(BitVec.ofNat 152 (word80 [0x101804018003040400,0x7690822222222222]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x3ffffffffffff0000,0x32aaa8e24f000f000ff0])),(BitVec.ofNat 152 (word80 [0x206008060004001810,0x12a00860444444444444]))),((BitVec.ofNat 152 (word80 [0xfc0000000000000000,0x4154991e60000ffff000])),(BitVec.ofNat 152 (word80 [0x2805028022808a020,0x1548006288888888888]))),((BitVec.ofNat 152 (word80 [3,0x3f0502078ffff0000000])),(BitVec.ofNat 152 (word80 [0x43006030043010c043,0x25040006088888888888]))),(0x0,0x0),(0x0,0x0)]
def g119C : List ColumnInfo := [(2,0,117,0,8)]
def g119A : List (List Nat) := [[],[101],[66],[66,101],[32],[32,101],[32,64],[32,64,101],[64,32],[64,32,101],[64],[64,101]]
def g119D8 (j : Nat) := if j=0 then 0x7f else 0
def g119L : Nat → Packing
  | 8 => (1,0,1,0,0,0,0,g119D8)
  | _ => emptyPacking
def g119I (_ _ : Nat) : Option (Nat × Nat) := none
def g119 : Forest := ⟨119,8,fun i => g119Y[i]?.getD (0,0),g119C,g119A,g119L,g119I⟩
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
  · exact (rfl : block g119 5 0 0 = true)
  · exact (rfl : block g119 6 0 0 = true)
  · exact (rfl : block g119 7 0 0 = true)
  · exact g119B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119G : graphValid g119 (boundsBefore K111) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low119 : Lower true (varsX 119) (graphGoal 119) 9 := lower_forest (g:=g119) (i:=0) (hints:=82) (before_sound K111 V111) g119G g119T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K119 := extendKnown K111 9 [(221,[49,101,117])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V119 : Known true K119 := extend_ok (m:=119) V111 low119 (by decide +kernel)
def g125Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xf801fffff83ffffeca,0xde0a4140007c00f83ff])),(BitVec.ofNat 152 (word80 [0x9024010090800102c2,0x8400014210842108421]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffe007fffc1fffd95,0xb101548c00f801f07c1f])),(BitVec.ofNat 152 (word80 [0x20080a012004020110,0xa1014400421084210842]))),((BitVec.ofNat 152 (word80 [0xffffff800001ff80d7,0xc57643401f0000000000])),(BitVec.ofNat 152 (word80 [0xc1304c15c1085408d7,0xc5764201ef7bdef7bdef]))),((BitVec.ofNat 152 (word80 [0xfffffffffffe000021,0x2e5c7a23e0003e007fe0])),(BitVec.ofNat 152 (word80 [0x4010060000181021,0x4043a00842108421084]))),((BitVec.ofNat 152 (word80 [0x44,0x90bf89b000003fff8000])),(BitVec.ofNat 152 (word80 [0x58160580211602004,0x10ba81a318c6318c6318]))),((BitVec.ofNat 152 (word80 [0x33a,0x528a034bffffc0000000])),(BitVec.ofNat 152 (word80 [0x60180600421804008,0x1288014a108421084210]))),(0x0,0x0),(0x0,0x0)]
def g125C : List ColumnInfo := [(0,8,53,64,8),(8,0,117,0,8),(32,0,93,0,8),(1,0,124,0,7),(4,0,121,0,7),(16,0,109,0,7),(64,8,53,0,7),(5,0,120,0,4),(17,0,108,0,4),(20,0,105,0,4)]
def g125A : List (List Nat) := [[],[66],[32],[32,64],[64,32],[64]]
def g125D6 := limbs80 #[#[0x25fba2c6887d1314c110,0xd7ee8b1a216fdd16344,0x820bc527287d86bf1180,0x171e01e3e3c03e3d]]
def g125D7 := limbs80 #[#[0xfd8d10bf58d10fe4c110,0x690884603600ff58d10b,0x2481f1cb61881c3c7257,0x78d2571c08571cb61c5,0x92]]
def g125H7 (j : Nat) := if j=0 then 0x3e040c3f000 else 0
def g125D8 (j : Nat) := if j=0 then 0xf1a9072b0ffd10 else 0
def g125H8 := limbs80 #[#[0x31a300000000b2000000,0xe0a8]]
def g125D9 (j : Nat) := if j=0 then 0x5413261bf else 0
def g125H9 (j : Nat) := if j=0 then 0x2d12f else 0
def g125L : Nat → Packing
  | 6 => (4,3,4,0,0,7,0,g125D6)
  | 7 => (4,2,4,0,0,8,0,g125D7)
  | 8 => (1,1,4,0,0,0,0,g125D8)
  | 9 => (1,0,4,0,0,0,0,g125D9)
  | _ => emptyPacking
def g125I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 1 7 0 6 2 0 g125H7
  | 8 => lookupWord 1 13 0 8 2 2 g125H8
  | 9 => lookupWord 1 3 0 6 0 2 g125H9
  | _ => fun _ => none
def g125 : Forest := ⟨125,9,fun i => g125Y[i]?.getD (0,0),g125C,g125A,g125L,g125I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P6_0 : block g125 6 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P6_2 : block g125 6 2 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g125B6 : block g125 6 0 4=true := (@block_merge g125 6 0 2 2 g125P6_0 g125P6_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P7_0 : block g125 7 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P7_3 : block g125 7 3 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g125B7 : block g125 7 0 4=true := (@block_merge g125 7 0 3 1 g125P7_0 g125P7_3)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P8_0 : block g125 8 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g125B8 : block g125 8 0 1=true := g125P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P9_0 : block g125 9 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g125B9 : block g125 9 0 1=true := g125P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125T : checkedTables g125 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g125 0 0 0 = true)
  · exact (rfl : block g125 1 0 0 = true)
  · exact (rfl : block g125 2 0 0 = true)
  · exact (rfl : block g125 3 0 0 = true)
  · exact (rfl : block g125 4 0 0 = true)
  · exact (rfl : block g125 5 0 0 = true)
  · exact g125B6
  · exact g125B7
  · exact g125B8
  · exact g125B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125G : graphValid g125 (boundsBefore K119) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low125 : Lower true (varsX 125) (graphGoal 125) 10 := lower_forest (g:=g125) (i:=0) (hints:=24578) (before_sound K119 V119) g125G g125T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K125 := extendKnown K119 10 [(125,[]),(215,[49,117])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V125 : Known true K125 := extend_ok (m:=125) V119 low125 (by decide +kernel)
def g175Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xc007ffffe0ffff7224,0xa70baa00000fc003f03f])),(BitVec.ofNat 152 (word80 [0x82500a004204403200,0x25032a05145145145145]))),((BitVec.ofNat 152 (word80 [0xfff800ffffffe03d48,0x8e6630c0000000fc0fc0])),(BitVec.ofNat 152 (word80 [0x20642c828080823d08,0x8e4210638e38e38e38e3]))),((BitVec.ofNat 152 (word80 [0xffffff0000ffffad86,0xb058468003f03f00003f])),(BitVec.ofNat 152 (word80 [0x80300b0409000506,0x9058048a28a28a28a28a]))),((BitVec.ofNat 152 (word80 [0xffffffffff0000804d,0x6156adc0fc0000000fc0])),(BitVec.ofNat 152 (word80 [0xb01402c002e048045,0x2114ad9c71c71c71c71c]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x9171,0x18b1d83f00003ffff000])),(BitVec.ofNat 152 (word80 [0xc0180300830088071,0x20c010410410410410]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x4e93,0x4f80057fffffc0000000])),(BitVec.ofNat 152 (word80 [0x300600c010c0104880,0x4a800060820820820820]))),(0x0,0x0)]
def g175C : List ColumnInfo := [(2,0,173,0,8)]
def g175A : List (List Nat) := [[],[49,117],[32],[32,49,117]]
def g175D8 (j : Nat) := if j=0 then 0x7f else 0
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
theorem g175G : graphValid g175 (boundsBefore K125) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low175 : Lower true (varsX 175) (graphGoal 175) 9 := lower_forest (g:=g175) (i:=0) (hints:=4146) (before_sound K125 V125) g175G g175T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K175 := extendKnown K125 9 [(175,[]),(187,[66]),(190,[32,64])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V175 : Known true K175 := extend_ok (m:=175) V125 low175 (by decide +kernel)
def g183Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfffc01ffc3ffffff22,0xacb338000f8000f83ff])),(BitVec.ofNat 152 (word80 [0x2814028804002002,0xa8b1004210842108421]))),((BitVec.ofNat 152 (word80 [0x1ffffe0003fe1ff049,0x39c7ca80000001f00000])),(BitVec.ofNat 152 (word80 [0x52b2192b1228524249,0x39c7cadef7bdef7bdef7]))),((BitVec.ofNat 152 (word80 [0x1ffffffffc001ffffd,0xa0411c001f003e007c1f])),(BitVec.ofNat 152 (word80 [0x80c0200c003080803d,0x400c08421084210842]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1fffffffffffe00010,0xfe246883e007c0007fe0])),(BitVec.ofNat 152 (word80 [0x30040300040030400,0xf0242090842108421084]))),((BitVec.ofNat 152 (word80 [0xe0000000000000000e,0x1132807c0007ffff8000])),(BitVec.ofNat 152 (word80 [0x40080400080040000,0x21084210842108]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xc1,0x459c477ffff800000000])),(BitVec.ofNat 152 (word80 [0x1803018023011808c0,0x5104342108421084210]))),(0x0,0x0)]
def g183C : List ColumnInfo := [(2,0,181,0,10)]
def g183A : List (List Nat) := [[],[116],[66],[66,114],[114,66],[114],[32],[32,116],[32,64],[32,64,112],[32,112,64],[32,112],[64,32],[64,32,114],[64],[64,112],[64,114],[64,114,32],[112,32,66],[112,32],[112,64],[112],[112,66,32],[112,66]]
def g183D10 (j : Nat) := if j=0 then 0x7f else 0
def g183L : Nat → Packing
  | 10 => (1,0,1,0,0,0,0,g183D10)
  | _ => emptyPacking
def g183I (_ _ : Nat) : Option (Nat × Nat) := none
def g183 : Forest := ⟨183,10,fun i => g183Y[i]?.getD (0,0),g183C,g183A,g183L,g183I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183P10_0 : block g183 10 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g183B10 : block g183 10 0 1=true := g183P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183T : checkedTables g183 10 := by
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
  · exact (rfl : block g183 8 0 0 = true)
  · exact (rfl : block g183 9 0 0 = true)
  · exact g183B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183G : graphValid g183 (boundsBefore K175) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low183 : Lower true (varsX 183) (graphGoal 183) 11 := lower_forest (g:=g183) (i:=0) (hints:=82) (before_sound K175 V175) g183G g183T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K183 := extendKnown K175 11 [(183,[]),(189,[49,117])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V183 : Known true K183 := extend_ok (m:=183) V175 low183 (by decide +kernel)
def g231Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x7ff83ff83fffffc8,0x950ae1400f801f003ff])),(BitVec.ofNat 152 (word80 [0x500508010800100c8,0x8500014210842108421]))),((BitVec.ofNat 152 (word80 [0xff80003fffc1ff81cf,0x33c110e000003e007c00])),(BitVec.ofNat 152 (word80 [0x6216110a0048209cf,0x23c100416b5ad6b5ad6b]))),((BitVec.ofNat 152 (word80 [0xffffffc00001fffc87,0xc526444c1f07c00f801f])),(BitVec.ofNat 152 (word80 [0x8018000c108040005,0x5200448421084210842]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffffffe000031,0x2e4c7923e000000fffe0])),(BitVec.ofNat 152 (word80 [0x500a00050000281010,0x47920842108421084]))),((BitVec.ofNat 152 (word80 [0x44,0x90af8bb00007fff00000])),(BitVec.ofNat 152 (word80 [0x604c02260211302000,0x900e8ba294a5294a5294]))),((BitVec.ofNat 152 (word80 [0x33a,0x529a034bfff800000000])),(BitVec.ofNat 152 (word80 [0x807004380421c04322,0x528a020318c6318c6318]))),(0x0,0x0)]
def g231C : List ColumnInfo := [(2,0,229,0,8)]
def g231A : List (List Nat) := [[],[32]]
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
theorem g231G : graphValid g231 (boundsBefore K183) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low231 : Lower true (varsX 231) (graphGoal 231) 9 := lower_forest (g:=g231) (i:=0) (hints:=82) (before_sound K183 V183) g231G g231T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K231 := extendKnown K183 9 [(231,[]),(237,[49,117]),(243,[66,50]),(246,[32,64,48]),(249,[49,66,117]),(252,[32,49,64,16,117])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V231 : Known true K231 := extend_ok (m:=231) V183 low231 (by decide +kernel)
def g235Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x1fffffc1fffe0f3ac,0xa445084003f000fc0fc0])),(BitVec.ofNat 152 (word80 [0x54028048400042f18c,0xa00100030c30c30c30c3]))),((BitVec.ofNat 152 (word80 [0xfe003fffe0ffff7410,0xe42ab68000003f03f03f])),(BitVec.ofNat 152 (word80 [0x188310100240807400,0x64021611451451451451]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffc00000ffff25c6,0x93d84280fc0fc000003f])),(BitVec.ofNat 152 (word80 [0x6004016084050001c4,0x93480086186186186186]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffff0000084d,0x6956a9bf00000003ffc0])),(BitVec.ofNat 152 (word80 [0x802805800016040840,0x954a88c30c30c30c30c]))),((BitVec.ofNat 152 (word80 [0x1171,0x18b1dc40000ffffc0000])),(BitVec.ofNat 152 (word80 [0x13026010898080031,0x8b0c868a28a28a28a28]))),((BitVec.ofNat 152 (word80 [0xce93,0x4f80057ffff000000000])),(BitVec.ofNat 152 (word80 [0x1c0380210e0100613,0x44800570c30c30c30c30]))),(0x0,0x0)]
def g235C : List ColumnInfo := [(1,0,234,0,6),(2,0,233,0,6),(8,0,227,0,6),(32,0,203,0,6),(64,0,171,0,6),(128,0,107,0,6),(10,0,225,0,5),(33,0,202,0,5),(66,0,169,0,5),(72,0,163,0,5),(129,0,106,0,5),(160,0,75,0,5),(3,0,232,0,4),(9,0,226,0,4),(40,0,195,0,4),(74,0,161,0,4),(96,0,139,0,4),(130,0,105,0,4),(161,0,74,0,4)]
def g235A : List (List Nat) := [[],[49,117],[16,115,101],[16,112,48,83,101],[48,16,81,97,113],[48,81,118],[80,49,97,112],[80,97],[96,81,115],[96,113,83],[112,99],[112,97,49,80]]
def g235D5 := limbs80 #[#[0x8520442f060c2148110,0x442f860c2148110ba184,0x60c214c110fc1324c520,0x4c110bb18408530442f4,0xf914350530442dc61421,0x5d050443e450d3150110,0x4427c61f21d4110db181,0xe1172d8d108bf845d932,0xc8530aaf845c5628422f,0x3660a890c0c021fe1576,0x400006fd38eed7a32de,0x180800004180]]
def g235D6 := limbs80 #[#[0x2f4b90a0887e02148110,0xb72e828221765cc5044,0x425fba2c48867b65d411,0x10fe26290221ba589408,0x442fcb9a40887f151481,0x110fe042982217edcd20,0x443f8a0a60887f3214c,0xc110fb28698221fc9053,0x30443ec99460885f9744,0x50110bf2e9182217e5ca,0x540443f898a80885f771,0x350110f7286a0221fcdc,0xc850443dcaa280885fb7,0x21d4110bf2e8282217e5,0x5d350442fcb96a0887f3,0xd764c910beee2992217e,0xfdd952442fdb82a4884f,0xff7358910b7ee8b12213,0x3f5cf624435fba2c4884,0x4fd7650d109faebb1221,0x13fdc9634437db82c688,0x84fd72d8d109fee8b1a2,0x21bb5c5628427eba6c68,0x186f56148430ddae8b14,0x861af591210c376b1242,0x21867e6548430cfaca90,0x861bd585410c27ebb24,0x821867d6550430ddac4a,0xb08613f5d9410c33f32a,0xac4186f57458430deae4,0xd10a617e5c2214c376b8,0x8482984fd76c85309fae],#[0xed20a61edd06414c2fcb,0xbb685184fd76d06309fa,0xee4b24613fdc5648c27e,0xf3b262a04fc764c5409f,0xfaebb0a813f5cf615027,0x8ac298901a844078009,0xa92447918429043b8d83,0x97c5d96858954519384,0x89d4719c06c9a4639886,0xa3489a2086a14819f07,0x4a7c9da6898a5c93a489,0x6accb1ac0aeab4a9a98a,0x4b04bfaf8bcaecb9ae0b,0x4b4cd1b40ceb34c9b18c,0x103431203dab64d7b58d,0xc10341c943040d07250c,0x8281c20030ac20d07250,0x70402501089434222000,0x3010d040410c0400000,0x43418100080000003010,0x141020004441010400c0,0x4000001040400000104,0x101201820010100000,0x10000000004,0x104141000410000,0x4000000000]]
def g235H6 := limbs80 #[#[0x6008,0xce900000000000000000,0x190,0x4d04140d120000000000,0x3c3800000000000001,0x168800584000,0x44a00,0xc1c00190732eaa0000,0x293000000000,0x30000000000000,0x8000000000000000000,0x224a12c,0x0,0xca10000000005b475800,0x28,0x16d800000000000000,0x75000000000,0x28d00000,0x28c000000000000,0xa0600000000000000000,0xe2800000000a2c00000,0x0,0x42800000000000000000,0x13000000000000c0c002]]
def g235D7 := limbs80 #[#[0xd58430bb98a10bb58a10,0x98830bb58830bd98430b,0x84409f994309f59430bb,0x110eed0240bd98440bd5,0x10fe4c110fe88110fe48,0xfe90110fe50110fe8c1,0xbf58910fed4110fe1411,0xfd8d10bf58d10bfd8910,0x58a10bf58610fe50210b,0x8830bf58430bf59210bf,0x230bf58a30bf58630bf5,0x40bf58640bfd8540bf59,0xff50110ff48110bf592,0xff58910ff54910ff4c91,0xf48430ff58d10ff50d10,0x88530ff48530ff50430f,0x530ff50530ffc8530ff,0x540ffd0a30ffd0630ff9,0xffd8540ff58540ff4c,0x1f834c588880cc0f4110,0xa78ce79ad2fa588a392c,0x21732bd5289ad2122740,0xf7bc673ae09b3b45654c,0xcd69772663f463883061,0x2aef572a4534a2541678,0x3d82afb5e2b9d6ead359,0xe1831a2a407131c624c,0x40300184203460314289,0xa241800c2101a3018a14,0xd18141801880d180c50,0x101c3081c306243880c8,0x38f1820d18961801e309],#[0x1e20d141c6083090428,0x40874a305141c7863128,0x181418f1460002ac88a3,0x604044840a0c00f1828d,0x70c20a0e3c3080861210,0x828a0e3c3141c7862840,0xa4060a0634520345031,0x204182838d1420d141c6,0xa0e3c30a0c7860808a0e,0x2030c34606284880e20,0x8688181841808e1810c0,0x406200060c6070880c0,0xc20e082021c20e1820c0,0x800834208302021c2101,0x8046080]]
def g235H7 := limbs80 #[#[0x4012000022200064,0x50140000402,0x0,0x0,0x41040800000000000000,0x1c2218220000000080,0x0,0x0,0x4800000000000000000,0x20700000000a,0x683e50580003d81,0x122900000000000000,0x0,0x34000000000000000000,0x77a00000006a3e00018e,0x1648400060272,0xad415000000018034000,0x28706880000000000060,0x28080000000240900003,0x2c000000000000003020,0x25d900000000a4,0x18051425683d0,0x0,0x10400000000000000000,0x5987504a000000000002,0xc20f80b5003,0x203c0000000000000,0x0,0x819000000000000000,0x0,0xe08800000000,0xfc0001a8b4050a08c000],#[0x168,0x8000808c0000000483c0,0x800,0x38070000000000,0x301800000,0x50862c74000,0x8200000000000000000,0x8000f76c000000000002,0x450000077660003409,0x2c00000000000000000,0xb,0x86c0dc80c00012438000,0x22e00010028000000126,0x76800000000000f,0x0,0x20fc0000000906c00,0x241d58170,0x0,0x8e00,0x1402fc4480000,0x7c00000000000000048a,0x6a,0x140a400000000,0xcc000000000000000000,0x140,0x31411762000000000000,0xe024000,0x71490b2200,0x381080000,0x8078c1a,0x502fd08a00,0x0],#[0x8000000000000000000,0x340003c8c8000a720c0,0x3838883000000000000a,0x0,0x0,0x1210800048030,0x701900000002800,0x114000240f8000d04c00,0x210e00004258039a,0x1018800032180000000,0x1de02200,0x282e000080ec00000000,0x55120000000,0x636000000000000001a4,0xe,0x10072522612754e,0xb,0x606000000000000,0x18440000,0x72a00000001129000000,0x25da88379,0x2010,0x902a00,0x590f1314000000000000,0x2d8f58480000000280c,0x186240000000282000,0x406a000000000000,0x68000000000000000000,0x22]]
def g235D8 := limbs80 #[#[0xd30fe187f843fa21fc10,0x1fe40fea07f103fc61f,0x1204f069289084e1b078,0x8828f1c33123c32881c6,0x710205210408140d3032,0x8a2481c410204d30a1c,0x28f1c348f]]
def g235H8 := limbs80 #[#[0x30800000306032011010,0x201700302,0x1e00004050000000995c,0x40c0000285d0,0x1c27000000,0xa0d4000000048b,0x300005b5481934b48090,0xc454000903000091,0x46000000000000000000,0x9cd00000000002,0xb77bb814e034d6600000,0x52a4000529c64fd0ca9d,0xbc00078900000001249,0x2c04928d5f0e0600000,0x800020b8000788327500,0x50a40000000000202,0x2c00000000003473001c,0x100035ea0000000c07cc,0xf04dc9,0x72500000000000,0xf0680000,0x0,0xc21000,0xa070000b094,0x3493f0a00,0xd25400,0x182d00000000044000,0x50991d5d8200000,0x88e000000000,0x34150000000000,0x1c4f00000000000,0x200010900000000c03c0],#[0xe301a820000019,0x0,0x127400000000,0x2c74a70800022c000000,0x7500000000001c31000,0x6ec04b88d0001e0f0002,0x4b0000244c09200015,0x6120000c980000c0cc00,0x19000000002640000000,0x1a355008000d0900008,0xe92a000299100,0x8fa7b54510000000000,0xc388250960003c0bc2af,0xa920000000000000029,0x7140000c0ac000f23000,0x216ac0400000000000,0x3801015c00000000000,0xb41b0000000505e01600,0x21840000000000f0a,0xa4000000000000002000,0x10,0x8f81d00020a5c0d000,0xb1240004020000,0x39800038d14220]]
def g235D9 (j : Nat) := if j=0 then 0x3f else 0
def g235H9 := limbs80 #[#[0x418231156208034a0060,0x7a41a2799a325c171,0xc88c86592830001a1000,0x200000028aa18e4ae898,0x5490000006d291,0x2b888a000000000501,0x1a2042d46397385228,0x400a3280000000055100,0xa30a1a01f09000013598,0x8502b119111838138005,0x6c2d0262942a8002daea,0x3a8b00000000644000,0x0,0x99608f8800000000000,0x238005b4031a3a800000,0x73179a892a]]
def g235L : Nat → Packing
  | 5 => (15,4,5,0,0,7,0,g235D5)
  | 6 => (76,3,5,0,0,10,0,g235D6)
  | 7 => (54,2,5,0,0,11,0,g235D7)
  | 8 => (9,1,5,0,0,9,0,g235D8)
  | 9 => (1,0,5,0,0,0,0,g235D9)
  | _ => emptyPacking
def g235I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 8 173 2 11 4 3 g235H6
  | 7 => lookupWord 32 487 2 15 7 4 g235H7
  | 8 => lookupWord 30 311 4 14 6 4 g235H8
  | 9 => lookupWord 15 97 5 12 4 4 g235H9
  | _ => fun _ => none
def g235 : Forest := ⟨235,9,fun i => g235Y[i]?.getD (0,0),g235C,g235A,g235L,g235I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P5_0 : block g235 5 0 2=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P5_2 : block g235 5 2 13=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g235B5 : block g235 5 0 15=true := (@block_merge g235 5 0 2 13 g235P5_0 g235P5_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P6_0 : block g235 6 0 7=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P6_7 : block g235 6 7 69=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g235B6 : block g235 6 0 76=true := (@block_merge g235 6 0 7 69 g235P6_0 g235P6_7)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P7_0 : block g235 7 0 11=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P7_11 : block g235 7 11 24=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P7_35 : block g235 7 35 19=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g235B7 : block g235 7 0 54=true := (@block_merge g235 7 0 11 43 g235P7_0 (@block_merge g235 7 11 24 19 g235P7_11 g235P7_35))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P8_0 : block g235 8 0 9=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g235B8 : block g235 8 0 9=true := g235P8_0
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
theorem g235G : graphValid g235 (boundsBefore K231) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low235 : Lower true (varsX 235) (graphGoal 235) 10 := lower_forest (g:=g235) (i:=0) (hints:=4149) (before_sound K231 V231) g235G g235T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K235 := extendKnown K231 10 [(235,[]),(238,[16,112,32,50,83,101]),(250,[16,112,32,67,50,83,101])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V235 : Known true K235 := extend_ok (m:=235) V231 low235 (by decide +kernel)
def g245Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffe00ff8ff8fff0ff0,0x222a0003e007c00f83ff])),(BitVec.ofNat 152 (word80 [0x4020100100020000,0x1084210842108421]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x3ffff000fff1fff0f2,0xd080007c00f801f07c1f])),(BitVec.ofNat 152 (word80 [0x8040200200040000,0x2108421084210842]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x3fffffff0001ffff01,0x5440f801f003e007fe0])),(BitVec.ofNat 152 (word80 [0x10080400400080000,0x4210842108421084]))),((BitVec.ofNat 152 (word80 [0x3ffffffffffe00000f,0x6931f00000003fff8000])),(BitVec.ofNat 152 (word80 [0x8a050280280050222b,0x69208421084210842108]))),((BitVec.ofNat 152 (word80 [0xc00000000000000001,0xfe5800001fffc0000000])),(BitVec.ofNat 152 (word80 [0x2c160b02b025604441,0xfe598c6318c6318c6318]))),((BitVec.ofNat 152 (word80 [0xc,0x88dfffffe00000000000])),(BitVec.ofNat 152 (word80 [0x30180c04c049808884,0x80df0842108421084210]))),(0x0,0x0)]
def g245C : List ColumnInfo := [(64,0,181,0,10)]
def g245A : List (List Nat) := [[],[117],[66],[66,117],[32],[32,117],[32,64],[32,64,117],[64,32],[64,32,117],[64],[64,117]]
def g245D10 (j : Nat) := if j=0 then 0x7f else 0
def g245L : Nat → Packing
  | 10 => (1,0,1,0,0,0,0,g245D10)
  | _ => emptyPacking
def g245I (_ _ : Nat) : Option (Nat × Nat) := none
def g245 : Forest := ⟨245,10,fun i => g245Y[i]?.getD (0,0),g245C,g245A,g245L,g245I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g245P10_0 : block g245 10 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g245B10 : block g245 10 0 1=true := g245P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g245T : checkedTables g245 10 := by
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
  · exact (rfl : block g245 8 0 0 = true)
  · exact (rfl : block g245 9 0 0 = true)
  · exact g245B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g245G : graphValid g245 (boundsBefore K235) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low245 : Lower true (varsX 245) (graphGoal 245) 11 := lower_forest (g:=g245) (i:=0) (hints:=2) (before_sound K235 V235) g245G g245T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K245 := extendKnown K235 11 [(245,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V245 : Known true K245 := extend_ok (m:=245) V235 low245 (by decide +kernel)
def g127Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x4a3d875d4009000000,0xff000000ff00ff00ff])),(BitVec.ofNat 152 (word80 [0x4810831d0009050505,0x5050505050505050505]))),((BitVec.ofNat 152 (word80 [0x40c0068aefcb000000,0xff000000ff000000ff00])),(BitVec.ofNat 152 (word80 [0x40c00608cf41131313,0x13131313131313131313]))),((BitVec.ofNat 152 (word80 [0x17000858ec200000ff,0xff0000ff0000ff])),(BitVec.ofNat 152 (word80 [0x3000040ec200a0a0a,0xa0a0a0a0a0a0a0a0a0a]))),((BitVec.ofNat 152 (word80 [0x4f78b000b0be00ff00,0xff00])),(BitVec.ofNat 152 (word80 [0xf38b00030be6c6c6c,0x6c6c6c6c6c6c6c6c6c6c]))),((BitVec.ofNat 152 (word80 [0xa022fe2403b0ff0000,0xff000000ffff0000])),(BitVec.ofNat 152 (word80 [0x20222c000390303030,0x30303030303030303030]))),((BitVec.ofNat 152 (word80 [0xbc0950031552000000,0xffffffff00000000])),(BitVec.ofNat 152 (word80 [0x940950021002c0c0c0,0xc0c0c0c0c0c0c0c0c0c0]))),((BitVec.ofNat 152 (word80 [0x919621a01a05ffffff,0xffff0000000000000000])),(BitVec.ofNat 152 (word80 [0x900400a00000808080,0x80808080808080808080]))),(0x0,0x0),(0x0,0x0)]
def g127C : List ColumnInfo := [(32,0,95,0,11)]
def g127A : List (List Nat) := [[],[66],[32],[32,64],[64,32],[64]]
def g127D11 (j : Nat) := if j=0 then 0xff else 0
def g127L : Nat → Packing
  | 11 => (1,0,1,0,0,0,0,g127D11)
  | _ => emptyPacking
def g127I (_ _ : Nat) : Option (Nat × Nat) := none
def g127 : Forest := ⟨127,11,fun i => g127Y[i]?.getD (0,0),g127C,g127A,g127L,g127I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P11_0 : block g127 11 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B11 : block g127 11 0 1=true := g127P11_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127T : checkedTables g127 11 := by
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
  · exact (rfl : block g127 10 0 0 = true)
  · exact g127B11
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127G : graphValid g127 (boundsBefore K245) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low127 : Lower true (varsX 127) (graphGoal 127) 12 := lower_forest (g:=g127) (i:=0) (hints:=4146) (before_sound K245 V245) g127G g127T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K127 := extendKnown K245 12 [(127,[]),(223,[49,117])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V127 : Known true K127 := extend_ok (m:=127) V245 low127 (by decide +kernel)
def g191Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x4abd87dd4008000000,0xff000000ff00ff00ff])),(BitVec.ofNat 152 (word80 [0x4890831d0008050505,0x5050505050505050505]))),((BitVec.ofNat 152 (word80 [0x41c0268aedca000000,0xff000000ff00])),(BitVec.ofNat 152 (word80 [0x41c02688cd40939393,0x93939393939393939393]))),((BitVec.ofNat 152 (word80 [0x6020858ec21000000,0xff0000ff0000ff0000ff])),(BitVec.ofNat 152 (word80 [0x2020040e4210a0a0a,0xa0a0a0a0a0a0a0a0a0a]))),((BitVec.ofNat 152 (word80 [0xcf7a9000a0be0000ff,0xff00])),(BitVec.ofNat 152 (word80 [0x8e3a900020be6c6c6c,0x6c6c6c6c6c6c6c6c6c6c]))),((BitVec.ofNat 152 (word80 [0x2020fe2403b000ff00,0xff000000ffff0000])),(BitVec.ofNat 152 (word80 [0x20202c200190303030,0x30303030303030303030]))),((BitVec.ofNat 152 (word80 [0xbc0950031552ff0000,0xffffffff00000000])),(BitVec.ofNat 152 (word80 [0x940950020002404040,0x40404040404040404040]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x919621a01a05ffffff,0xffff0000000000000000])),(BitVec.ofNat 152 (word80 [0x10400801a00808080,0x80808080808080808080]))),(0x0,0x0)]
def g191C : List ColumnInfo := [(2,0,189,0,11)]
def g191A : List (List Nat) := [[],[66],[49,117],[49,66,117],[32],[32,64],[32,49,117],[32,49,64,117],[64,32],[64],[64,49,32,117],[64,49,117]]
def g191D11 (j : Nat) := if j=0 then 0xff else 0
def g191L : Nat → Packing
  | 11 => (1,0,1,0,0,0,0,g191D11)
  | _ => emptyPacking
def g191I (_ _ : Nat) : Option (Nat × Nat) := none
def g191 : Forest := ⟨191,11,fun i => g191Y[i]?.getD (0,0),g191C,g191A,g191L,g191I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P11_0 : block g191 11 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g191B11 : block g191 11 0 1=true := g191P11_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191T : checkedTables g191 11 := by
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
  · exact (rfl : block g191 10 0 0 = true)
  · exact g191B11
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191G : graphValid g191 (boundsBefore K127) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low191 : Lower true (varsX 191) (graphGoal 191) 12 := lower_forest (g:=g191) (i:=0) (hints:=4146) (before_sound K127 V127) g191G g191T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K191 := extendKnown K127 12 [(191,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V191 : Known true K191 := extend_ok (m:=191) V127 low191 (by decide +kernel)
def g239Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x422cb15f401c000000,0xff000000ff0000ff00ff])),(BitVec.ofNat 152 (word80 [0x4008811e001c050505,0x5050505050505050505]))),((BitVec.ofNat 152 (word80 [0x4445072ae049000000,0xff0000ff00ff00])),(BitVec.ofNat 152 (word80 [0x4045032ac001434343,0x43434343434343434343]))),((BitVec.ofNat 152 (word80 [0x329008d8e0a30000ff,0xff0000ff000000ff])),(BitVec.ofNat 152 (word80 [0x2900840e0830a0a0a,0xa0a0a0a0a0a0a0a0a0a]))),((BitVec.ofNat 152 (word80 [0x4a78c000bfae00ff00,0xff000000000000ff00])),(BitVec.ofNat 152 (word80 [0x238c00026ae1c1c1c,0x1c1c1c1c1c1c1c1c1c1c]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xa522ce2403a0ff0000,0xffffff0000])),(BitVec.ofNat 152 (word80 [0x252044000320303030,0x30303030303030303030]))),((BitVec.ofNat 152 (word80 [0xbc0960031542000000,0xffffffff0000000000])),(BitVec.ofNat 152 (word80 [0xbc0020011140a0a0a0,0xa0a0a0a0a0a0a0a0a0a0]))),((BitVec.ofNat 152 (word80 [0x919631a01a15ffffff,0xff000000000000000000])),(BitVec.ofNat 152 (word80 [0x900630a01800c0c0c0,0xc0c0c0c0c0c0c0c0c0c0]))),(0x0,0x0)]
def g239C : List ColumnInfo := [(1,0,238,0,10),(4,0,235,0,10),(2,0,237,0,9),(8,0,231,0,9),(32,0,207,0,9),(64,0,175,0,9),(128,0,111,0,9),(10,0,229,0,8),(66,0,173,0,8),(72,0,167,0,8),(160,0,79,0,8),(0,2,133,104,7),(130,0,109,0,7),(192,0,47,0,7),(138,0,101,0,5),(194,0,37,0,4)]
def g239A : List (List Nat) := [[],[49,117],[32],[32,49,117]]
def g239D8 := limbs80 #[#[0xb5f835c565bd7835d561,0xe12350acf8f091a85a40,0x19f1]]
def g239D9 := limbs80 #[#[0x5735873eb1acbbd58d61,0x9acbdf5c565feaeab0ff,0xe392412006fd74597beb,0x6382e2998e05322fb664,0x25d4c8c3e383351c31a5,0x52e31e69186352e39186,0x1a5518e148c6938e1]]
def g239H9 (j : Nat) := if j=0 then 0x395 else 0
def g239D10 := limbs80 #[#[0x65bf5977d65fd987f561,0xfd54ff587fd41bfd977e,0x31dace57a40ce4312003,0xa18f18190289998c1434,0x902b4d4446091cadbc60,0x3c60a40a98c0c8153181,0x13182902c6075205]]
def g239H10 := limbs80 #[#[0xc00000008c0580000000,0xc01040000000000c,0xa80003a]]
def g239D11 (j : Nat) := if j=0 then 0x1314e2037f else 0
def g239H11 := limbs80 #[#[0xe100002ce00e00000020,0x8c00eb9da4945a19e001,0x14509]]
def g239L : Nat → Packing
  | 8 => (2,3,4,0,0,6,0,g239D8)
  | 9 => (7,2,4,0,0,8,0,g239D9)
  | 10 => (9,1,4,0,0,9,0,g239D10)
  | 11 => (1,0,4,0,0,0,0,g239D11)
  | _ => emptyPacking
def g239I : Nat → Nat → Option (Nat × Nat)
  | 9 => lookupWord 1 2 0 5 1 0 g239H9
  | 10 => lookupWord 1 29 0 7 3 0 g239H10
  | 11 => lookupWord 3 19 3 9 4 1 g239H11
  | _ => fun _ => none
def g239 : Forest := ⟨239,11,fun i => g239Y[i]?.getD (0,0),g239C,g239A,g239L,g239I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239P8_0 : block g239 8 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g239B8 : block g239 8 0 2=true := g239P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239P9_0 : block g239 9 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239P9_2 : block g239 9 2 5=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g239B9 : block g239 9 0 7=true := (@block_merge g239 9 0 2 5 g239P9_0 g239P9_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239P10_0 : block g239 10 0 6=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239P10_6 : block g239 10 6 3=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g239B10 : block g239 10 0 9=true := (@block_merge g239 10 0 6 3 g239P10_0 g239P10_6)
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
  · exact g239B8
  · exact g239B9
  · exact g239B10
  · exact g239B11
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239G : graphValid g239 (boundsBefore K191) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low239 : Lower true (varsX 239) (graphGoal 239) 12 := lower_forest (g:=g239) (i:=0) (hints:=4146) (before_sound K191 V191) g239G g239T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K239 := extendKnown K191 12 [(239,[]),(251,[66]),(254,[32,64])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V239 : Known true K239 := extend_ok (m:=239) V191 low239 (by decide +kernel)
def g247Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xd1808798803cc60400,0xfc0000fc0000fc0fff])),(BitVec.ofNat 152 (word80 [0x18004180024c00410,0x41041041041041041041]))),((BitVec.ofNat 152 (word80 [0x2b9e4430f8d0944800,0x3f00003f000000])),(BitVec.ofNat 152 (word80 [0xa99e4430f050844975,0xd75d75d75d75d75d75d7]))),((BitVec.ofNat 152 (word80 [0xc50c3841f00d00f000,0x3f000fc0000fc003f03f])),(BitVec.ofNat 152 (word80 [0xc2001900900c020,0x82082082082082082082]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x863246e560007080f,0xc003f00003f00003ffc0])),(BitVec.ofNat 152 (word80 [0x82200404600060841,0x4104104104104104104]))),((BitVec.ofNat 152 (word80 [0x8bd0850dc22827f0,0x3fffffc0000])),(BitVec.ofNat 152 (word80 [0x190840880282082,0x8208208208208208208]))),((BitVec.ofNat 152 (word80 [0x367501820803f03800,0x3fffffc0000000000])),(BitVec.ofNat 152 (word80 [0x16410182080230328a,0x28a28a28a28a28a28a28]))),((BitVec.ofNat 152 (word80 [0x2c004b32233239c3ff,0xfffc0000000000000000])),(BitVec.ofNat 152 (word80 [0x24004b22211211030c,0x30c30c30c30c30c30c30]))),(0x0,0x0)]
def g247C : List ColumnInfo := [(2,0,245,0,11)]
def g247A : List (List Nat) := [[],[66],[32],[32,64],[64,32],[64]]
def g247D11 (j : Nat) := if j=0 then 0xff else 0
def g247L : Nat → Packing
  | 11 => (1,0,1,0,0,0,0,g247D11)
  | _ => emptyPacking
def g247I (_ _ : Nat) : Option (Nat × Nat) := none
def g247 : Forest := ⟨247,11,fun i => g247Y[i]?.getD (0,0),g247C,g247A,g247L,g247I⟩
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
  · exact (rfl : block g247 6 0 0 = true)
  · exact (rfl : block g247 7 0 0 = true)
  · exact (rfl : block g247 8 0 0 = true)
  · exact (rfl : block g247 9 0 0 = true)
  · exact (rfl : block g247 10 0 0 = true)
  · exact g247B11
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247G : graphValid g247 (boundsBefore K239) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low247 : Lower true (varsX 247) (graphGoal 247) 12 := lower_forest (g:=g247) (i:=0) (hints:=82) (before_sound K239 V239) g247G g247T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K247 := extendKnown K239 12 [(247,[]),(253,[49,117])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V247 : Known true K247 := extend_ok (m:=247) V239 low247 (by decide +kernel)
def g255Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x7fe007fe007f,0xe0401e0e244d8199eff2])),(BitVec.ofNat 152 (word80 [0x280a0280a0280a0280,0xa0000c0000048088e480]))),((BitVec.ofNat 152 (word80 [0x1ff80000001ff80,0x1b198100082e67e7c00])),(BitVec.ofNat 152 (word80 [0x9a2689a2689a2689a2,0x60b198100082a27a2c00]))),((BitVec.ofNat 152 (word80 [0x7fe00001ff800007f,0xe201e024383318678d34])),(BitVec.ofNat 152 (word80 [0x501405014050140501,0x4000c000101208270800]))),((BitVec.ofNat 152 (word80 [0x1ff80,0x200c0433c1f87f001])),(BitVec.ofNat 152 (word80 [0x60d8360d8360d8360d,0x80020040433c1d85d000]))),((BitVec.ofNat 152 (word80 [0xf80000001ffffe0000,0x43c010783c01ff80258])),(BitVec.ofNat 152 (word80 [0x806018060180601806,0x180001018017500000]))),((BitVec.ofNat 152 (word80 [0xffffffffe000000000,0x180001f803ffe000006e])),(BitVec.ofNat 152 (word80 [0x18060180601806018,0x80001e8026940000000]))),(0x1fc001fffc0000000080,(BitVec.ofNat 152 (word80 [0x50140501405014050,0x1f4001a8000000000000]))),(0x1ffffe0000000000030f,(BitVec.ofNat 152 (word80 [0x60180601806018060,0x17e1100000000000030f]))),(0x0,0x0)]
def g255C : List ColumnInfo := [(1,0,254,0,12),(2,0,253,0,12),(4,0,251,0,12),(8,0,247,0,12),(16,0,239,0,12),(32,0,223,0,12),(64,0,191,0,12),(128,0,127,0,12),(10,0,245,0,11),(66,0,189,0,11),(72,0,183,0,11),(160,0,95,0,11),(0,2,149,104,10),(0,8,53,194,10),(5,0,250,0,10),(17,0,238,0,10),(20,0,235,0,10),(40,0,215,0,10),(96,0,159,0,10),(130,0,125,0,10),(3,0,252,0,9),(6,0,249,0,9),(9,0,246,0,9),(12,0,243,0,9),(18,0,237,0,9),(24,0,231,0,9),(32,2,149,72,9),(33,0,222,0,9),(34,0,221,0,9),(36,0,219,0,9),(48,0,207,0,9),(65,0,190,0,9),(68,0,187,0,9),(80,0,175,0,9),(132,0,123,0,9),(144,0,111,0,9),(1,2,148,104,7),(1,8,52,194,7),(4,2,145,104,7),(4,8,49,194,7),(16,2,133,104,7),(41,0,214,0,7),(44,0,211,0,7),(56,0,199,0,7),(97,0,158,0,7),(100,0,155,0,7),(112,0,143,0,7),(128,2,21,104,7),(131,0,124,0,7),(134,0,121,0,7),(146,0,109,0,7),(7,0,248,0,6),(13,0,242,0,6),(19,0,236,0,6),(21,0,234,0,6),(22,0,233,0,6),(25,0,230,0,6),(28,0,227,0,6),(33,2,148,72,6),(35,0,220,0,6),(36,2,145,72,6),(37,0,218,0,6),(38,0,217,0,6),(48,2,133,72,6),(49,0,206,0,6),(50,0,205,0,6),(52,0,203,0,6),(69,0,186,0,6),(81,0,174,0,6),(84,0,171,0,6),(148,0,107,0,6),(53,0,202,0,5),(149,0,106,0,5),(23,0,232,0,4),(29,0,226,0,4),(45,0,210,0,4),(101,0,154,0,4),(113,0,142,0,4),(116,0,139,0,4),(135,0,120,0,4)]
def g255A : List (List Nat) := [[],[66],[49,117],[49,66,117],[32],[32,64],[32,49,117],[32,49,64,117],[64,32],[64],[64,49,32,117],[64,49,117]]
def g255D7 := limbs80 #[#[0xb2bc5f0bb46858550120,0x5374cb308b22a4a82419,0xf13c26996561150483e4,0x2784db74ac22a0906e8a,0xf0bb56998454120cd95e,0xd32aaa2c4b02419b2bc4,0xed1a161554482dc53a95,0xbb46cc2a89066caf0bc0,0x68d9855120c8f5e1781d,0xcb0880c01917bc5f03b7,0x40083c0020124e0d4c8b,0x38400000194902e0e802,0x2f0e0cf0ebc]]
set_option maxRecDepth 16000 in
def g255D8 := limbs80 #[#[0x83c8a659845915254120,0x120fa2bc561965509404,0x404836caf15b85954250,0x250120bb2bc56c585509,0x50940482ecaf15b36154,0x915250120bb2bc56d985,0x964549404827caf15ba5,0xba5915250120aea9c6ae,0x5ee964549404823ea72e,0xf11b165552501209f29c,0x2bc56d1a654940482dca,0x78aed5656916250120af,0xd66bc56e56558940483,0x482d9af15b6655625012,0x4120fa29966116454950,0x950482dca712b9591525,0x5254120b669c6ae56454,0x4549504825da72eb9591,0x59152541209b69c8ee56,0xc584549504823da72bb9,0x1b36115254120bb2bc46,0xc46d98454950482ecaf1,0xa712ba5516254120bb2b,0xe69c6ee95458950482bc,0x3e8a6958459162541209,0x20fa2bc5611645895048,0x48279af15b959162541,0x54120b6a9c4ae5645895,0x89504825ba72eb959162,0x962541209e69c5ee5645,0xa259150482d9af15b465,0x96896454120a7a9c4aa5],#[0x69965611504829ba71aa,0x15b95516258120ba6bc2,0x9c4ae55458960482d9af,0x9a716b95516258120b6a,0x9ae9c8ee55458960482d,0x823ba72bb95516258120,0x120baabc46d584589604,0x604829ea712a96895458,0x458120a769c5aa5a2551,0x61160482b9af15b26995,0x499059120ba6bc269565,0x2a85c94244399ae95656,0xb4a61745c910d9adc76d,0x76c9a4a617244366b709,0xf15b36154250120c9edb,0x2bc56d98550940483eca,0x7caf15ba5915250120fb,0xf669ca6596554940483,0x483d9af2996595525012,0x120d76bca6e56554940,0x940483d9a699b5659525,0x5250120e6ebba6999654,0x654940482ddaf15ba659,0x6995250120b769c5ee99,0x556558940483bcaf15b4,0x9a56556250120f669ca6,0xc56d99558940483d9a6d,0xaf15ba6556250120f66b,0xbabc2ed1a161540482dd,0x36cef17b46858550120d,0x20fb29b9611645495048,0x483b9a6e99659152541],#[0x54120f669ba659645495,0x4950483ecaf11b361152,0x95254120fb2bc46d9845,0x5458950482ddaf29b465,0x65516254120de69ba659,0x6116458950483d9a6e99,0xe5a55916254120faa9b9,0xbb9695645895048379a6,0x9af15b95916254120de6,0xde69ba59594589504837,0x827daf15ba6516254120,0x120de6bb9595a4589504,0x504835baee5966916254,0x2541209f69c5ee5a4589,0x59150483d9af15b46596,0x8d8454120cf69c56cba9,0x965611504836eaed3b26,0xb6e958454120fa6bc269,0x4ec9a6611504836daf09,0xed7b26998454120dbabb,0x6bc2ed5a6611504836da,0xb9a6e9955516258120db,0xee6aba6555458960483,0x4833baae9b9551625812,0x8120f66bc56e55458960,0x1604827ba72bb9551625,0x5458120e76bc56a5a255,0x659554483b9af15b2699,0x6a16555120ba3dc4ee58,0xd1a161554482acf713b9,0xbb06a58655120db3bc0e,0xb5ec1a9619544834faec],#[0xfed7b46a58655120d37b,0x3ebb2ec1a9619544832c,0x38deed7b06a58655120e,0x20c37fc56eaa96195448,0x44832cf6d5b4ea586551,0x55120e76bb5689a06595,0x61544834cfed7b46a196,0xd9855120e3eba2ec1a36,0xa3661544834faecbb068,0x68d9855120e37ba5ec1,0xec1a3661544834deed7b,0x83b568d9855120d1fbb7,0xfb7ed5a3661544838dee,0x7ee83b768d9855120d17,0xe17fa5edda3661544838,0x8347ef03b768d9855120,0x120d17fc5edda3661544,0x544834faecbb06999855,0x559120d37bb5ec1a6661,0x5956448368fed7b46616,0x616559120f2ebb2ec198,0x1a961564483c9eed7b06,0xb06a58559120d3ebb2ec,0x5ed1a9615644834deed7,0xe93a2e819859120cb3fb,0xeba6e8ba066164483cea,0xcfaf09a5e819859120f2,0xd3ebb2ec1a566164482,0x4834deed7b0695985912,0x1120cbe9b7e8ba064584,0x584482cfaf0997e81916,0x6561120f27bc06599559],#[0x6595844836baecbb0659,0x6a56561120da7bb5ec19,0xc1a9595844832faecbb0,0xbb069b9561120cb7bb5e,0xa4e8ba0659844832faec,0xa6d7a2e819661120ebab,0xbebc2697a0659844832f,0x32de6d7a5e819661120a,0x20cbebb2ec3a56598448,0x54836baecbb069186595,0x59520ea7ba5ec1a46196,0x616548369eed7b069186,0x19859520d3ebb2ec1a46,0xa4661654834deed7b069,0xe919161520d37ba5ec1,0xec3a4645854832faecbb,0xc3a56519361520cb7bb5,0xba5ec1a4659854834dee,0xbae9ba2e819461920cb7,0xabebc2697a065186483a,0x433da709b0ea16454950,0x950cf69c06cba8591525,0x625426db70bb96918654,0x458950ae79c0ea195591,0x66162542b9e703a85959,0xa69858950c77ba5ec1a4,0x1a4e61625428dff15b46,0xb06919261950c779b56c,0x82940f604a80032dee97,0xd159894844a1f80e5867,0xc486c4091e10e206822e,0x5b30a1700b0c53227592],#[0x48f7c74337e1b3cd2a6,0x96e49a23e916686c4262,0xab29506a4950e2789350,0x6c4d6032ec96d6b3e588,0x4b63daaad1b67db36d97,0x2ce7672b38d9c46e106e,0xdf3e79ec8f4477ebb0dd,0x1e70b983fc149ffcfd17,0x90747ba3351608a044b6,0x26392e2967cabe4d122e,0x39fb4f8e76d3899bb4cf,0x2a9a14b0a48518e8a142,0xd7ad5565eb0954aa8ed4,0x856c055efaf4d78ebbb5,0x6a1b40d9bac9d648b0dd,0xdcb6e356fab73db1ed69,0x1792bc65de6ecd760ba6,0x4df0ef7b7aabd25e7af3,0x43801bf75f6efab7cfbe,0x3ce1cf0c185ac2a613b0,0x13b897c48e22f10b87fc,0xc6de3231858bcc54e28f,0x724d920c86e3eb1e98ee,0x9165e5af2b1945c9fe4e,0xa0770751251105c52e27,0x7ae2c71d0a87d83720f,0x48d02080ff042715389e,0x8c04701680b3908b8bdc,0x681d40d8e6b9097895c5,0x2407ab8b0ef1403d5c58,0x7f62c30076e25b161de,0x6ea13713d8bf000e02dd],#[0x703b712d8b1008a02e01,0x66901fd02bc4e62c6017,0xb523b60f6c5ee24540f0,0xc58ba0ffc1d624f16200,0xdae2c302000b8059d025,0xae29713110e459204050,0xe2441d0a87c02500f60d,0x13916b8917715c8b023e,0x3917b89e810dc0e5c56e,0x81db89e45880440176e1,0x9d02e45ee27c0036e11,0x80f24d722ef12280bb7,0x244fc080db91778a1102,0xfb13a8b0ef14036e45de,0x5cd89dc26a2f81c2a83,0x1d98acc4ba2e41e92024,0xf00e7458cc1d70d804a0,0xb847458820f207662601,0xf2202a443d161003b313,0xd17c0e1408802ecc37a2,0x1602cbc20802ecc4ee11,0x9d8aec4fa2d22026625d,0x4b51620043604920f458,0xb913b845c5880366074a,0x22e2c4e072e137161f03,0x722b717c891781dc89dc,0xe13a05b8bf000bb84607,0xec587c8a01b5e2c30176,0x817a2523ad8b17d12910,0x96a26c1dd846c58c010d,0x303b5152929c58a02e44,0xa2ad1390e3c5fa10801b],#[0xad08c820a44011d3495,0x3c841370868209905584,0x2ce42011c401e80a805,0x4502100b805be001005a,0x23a08130088036017247,0x1d9078402c28e85d0205,0x8002c28e87a0f01b040,0x2480502380b805b60f10,0xb0a4010130080036017,0x1b0402e016740808020,0xc684f816e043b4203d02,0x44020306c0253846810,0x5ae001005b384a0d86,0x7203801b72144017004,0x74081022811006dc8510,0xe00800b5c002540a4361,0x20386c025e006810c02,0x812030d8461b48104044,0xba4362810005c02ce810,0x72200360808a04001b00,0x1006eb0cb84a810861b0,0x4001774080582010bc00,0x90603801a7a143b81020,0x43f42860360408a03694,0xd0a0810c06d7020c0880,0x107c73c100b473cc000e,0x1700b3a04200b883e1,0x80402166c0836100204,0x40493c0810805a02eb07,0x4000000d09f02dc086e8,0x1d0593000c0000020470,0xa2c200682047f4584001],#[0x8f68b0801a080341023b,0x25c1833875c18400d040,0x810238201e1c1bc39e1c,0xd80020000000124,0x22811028c3020360400,0x600080000044021b6143,0x11c100000000000003,0x1307020000470407a080,0x8080001000c090205a08,0x370]]
def g255H8 := limbs80 #[#[0xa02000a556481d050,0xe40d45000000a04711,0x73017051070881069830,0x982e00384008b1,0x103141000000]]
set_option maxRecDepth 16000 in
def g255D9 := limbs80 #[#[0x80905b69b2e115254110,0x550940483d94c2acaa12,0x370b2a84a0241eaa6196,0x5babb66154250120b75,0x940482dd5dab0ca12809,0xaa2a4a0241bca6995454,0x29655915250120de574c,0x483754d32c8a9280907e,0xa4a0241d9a6596554940,0x66555250120aed372b2a,0x3b5d332aa9280906769a,0x2415daed99554940483,0x95250120cdd34ccb2a4a,0xd2ac8b1280904fa9b4e9,0x1d9a6556558940483755,0x50120add372b2ac4a024,0x4ab1280904fa9b4e9562,0xaed59658940483374cb7,0x20f65308b22a4a82415b,0x92a09076699659152541,0x984549504839b4cb308a,0xed34dca2a4a8241cdae5,0x90676ba6e515254120c,0x54950482bb4db728a92a,0x69cb2a4a82415daed196,0x7669965516254120aed3,0x50482f34db2a8b12a090,0x22c4a8241eaa61164589,0x9966116254120f4d2cac,0x83b34b2f28b12a09072e,0x4a82415ba6db94589504,0xe916254120dcd2cbd22c],#[0x74cb748b12a0904f69b5,0x2415baed196589504833,0x62581209ed365d32a8a8,0x2f28b12c09072eb95611,0x5ba6d79458960483375d,0x8120add369caac4b0241,0x4a12a0884ee9b2e95645,0x6519250950443f94ca2a,0x9ef76ad4a84a8221dea,0x284885f6bb2651525411,0xa854942443d97542a8a9,0x4ae8d0ae4a12216db6d6,0x8879ada85d17250910fb,0xc942443cd7542e8b9284,0xed42e4a12216ebed1a85,0xbadb4aa17250910b3df6,0x2442cf6dbd50b9284885,0x32ea12214df6d6a86554,0xa8e819750910cfe343d0,0x31fd54740cba848863f9,0xa12219fc6c7a065d4244,0xa19750910abef6ed0b2e,0xfdab50cba848853efb26,0x2147fedda865d424429b,0x750910a7db655432ea12,0x34b4c2a48851fdb7aa19,0xfcec194645724425bfda,0x910b37f68cc2e8b92215,0xba2e48859edb2a61745c,0x63a065172442cdeda530,0xc7f531d0328b92218fe6,0xe48849fdb4e9d985c910],#[0x5509404825f7da3454c2,0x366c2a84a0241eea6c58,0x7ba9b66154250120f75,0x940483dd4dab0ca12809,0xd0aa4a0241eeaed58650,0xa9a46855250120fe52a8,0x483bb4cab42a9280906f,0xa4a0241fca551a354940,0x568d5250120df5348d1a,0xf94d32a8a92809077699,0x241fca6d56454940483,0x15250120fd534cb22a4a,0xdd2c8a9280906fa9ba59,0x1beaae96454940482fd4,0x50120bf5774b22a4a024,0x48a9280907f296569152,0xa6c595549404837d4d33,0x20eed366caaa4a0241dd,0x9280907769a665552501,0x59654940483bb4db32aa,0xdd34ccb2a4a0241dda6d,0x906fa9b46995250120e,0x58940483f54d2ac8b128,0x4ad22c4a0241faa595a4,0x5fabb56916250120df53,0x40483bb4d2b2ab128090,0x2ac4a0241dba6d995589,0x9b56596250120edd32cd,0x83b75dab2cb12809076e,0xaa0241eceed185595404,0x6196550120f57768c32c,0xddda350b2a80907a7bb5],#[0x241adeed5a8595404835,0x8550120b7d764d0b0aa0,0xab42c2a80905bbbb4685,0x6eeed1a361540482dbdd,0x120b6f76ad1b0aa0241,0x8c2a80906bb9a6e91855,0xed1a661540482ddcdb74,0xb6f76ad330aa02416ee,0x280906bb9a5e91865012,0xa561940482ddcdaf48c3,0xd308a9322a82416eeed1,0x907769945499154120f6,0x45504837b5d22a4c8aa0,0x9d1322a82417daed1526,0x7e994e899154120ded2a,0x4827f4da744c8aa0906,0xaa4a8241bcee91546455,0x9464d5254120f6d308c9,0x37b5d2326a92a0907769,0xa8241f9a659645495048,0x915254120eed372b22a4,0x55cac8a92a0905f69b95,0x417daee56454950483bb,0x254120f6d362c22a4a82,0x308a92a0907b69b36115,0xda6d98454950483db4cb,0x120eed32cca2a4a8241e,0xa92a0906f69a66515254,0xd19654950483bb4d3728,0xfcd32caa2c4a8241dda6,0xa0907e69b65516254120,0x4589504837b4dd2a8b12],#[0x574aa2c4a82417da6e95,0x5f6bba5516254120ded,0x950483f34d2ac8b12a09,0xb22c4a8241f9a6d56458,0xe9b95916254120edd372,0x483b755cac8b12a0905e,0xc4a82417baee56458950,0x56116254120f6d34ac22,0xd74cb308b12a0907b6bb,0x8241f9a5959458950483,0x16254120edd32cca2c4a,0xb2b48b12a0907769a5e5,0x1bda695a458950483f34,0x54120edd32cd22c4a824,0x2cb12a0906ee996e9162,0xa689a155150483b74da3,0x20ded346d12a8a8241bd,0xa2a09077699668954541,0x9a6551504837b4d3344a,0xcd2cad12c8a8241bda6c,0x906f69a56896454120f,0x59150483b74cb344b22a,0x52d12c8a82419fa6a5a2,0x4febb26a56454120cfd5,0x504827bddab52b22a090,0x4ac8a82415ee6d2a9591,0x9baaa56454120adf36d5,0x827f4d9752b22a09047f,0x8a82413de6d7a9591504,0x685845412097f371d4ac,0xbdd2b42c22a0905bebb2,0x2416deed5a1611504835],#[0x8454120b7d764d1b08a8,0x32cac22a0905b7bb568d,0x6de6dba561150483d3cd,0x4120b7d764d3308a8241,0x4ca2a0905b7bb5699845,0x65ba2651504837b4b2f4,0x9fd36dd1328a82419fa,0x2a09057ebb2691965412,0x5458960482bbddab48cb,0xd372aa2c4b0241f9a655,0x905ee9b95516258120ed,0x8960483b755caa8b12c0,0xac22c4b02417baee5545,0xae9b56116258120f5d32,0x483d75dab08b12c0907,0x2c4b0241dba655945896,0xb56516258120ddd74aca,0x3b74d2f28b12c0905eeb,0xb0241f9a595a25516048,0x895458120ddd34cd12a8,0x554b44aa2c09067e9a96,0x41bba6c9a6551604833f,0x458120aef76ad4aa8b02,0x552aa2c0904febb26a55,0xde6d6a955160482bdcda,0x1209fd365d4aa8b02415,0xaa2c0904ef9b6ea55458,0x55a2591604825fcdc752,0xddd34ad12c8b0241dbae,0xc0905eebb56896458120,0x561160483d3cd2acac22,0x2cbd1328b02416faec9a],#[0x67e995e899458120ddd,0x1604827f4daf44ca2c09,0xd0b08a8a41b9ee956565,0xfbb06a58454520b7e760,0x4829fcd8552c22a29053,0x8b8a416fcec1a161171,0x9e9d845c520d3ef4ed0b,0x4fad8f4ec22e29061fda,0x8a414feec1a961171483,0x99055120a6ff6ad4b08b,0xda330c9aa89077696564,0x14dfed59864d544829df,0x55120b67f68cc2caaa24,0x50b2aa890737bb066165,0xeec1a16155448359fda3,0x20b67f68d0b0aaa2416d,0x2aa8905b3fb468d85551,0x1a66155448359ed3748c,0x7f760d4b0caa2416cfed,0x8904bbfb46a58655120a,0x619544825bfdab52c32a,0x6ad4b0caa2418feec1a9,0x53f9b0aa58655120c6ff,0x5448297edb552c32a890,0x4b0caa2410ff6eaa9619,0xdb5ea58655120977b69d,0x833f4d1340cb2a8904b7,0xcaa2415deed5a0659544,0x6a19655120a77f68d432,0xbedb74acc2a890537fb5,0x2414feec1a1661544825,0x9855120a6ff6ad0b30aa],#[0xab46cc2a89053fbb068d,0x47fedda3661544829bfd,0x5120a6fb6dd2b30aa241,0xccc2a89053fbb0699985,0x59592641644829bfdab4,0xcfd74ac9320b2241dba,0xac8906e7ba5595905912,0x9859564482d5fda330b2,0xf760cc2cab224169fed5,0x90727fb56616559120e5,0x956448355fda350b2ac8,0xad330ab2241a9fed5a85,0x3fbb06a58559120b4ff6,0x44829bfdab52c2ac8905,0xb0ab22412efed1a96156,0xb5aa58559120a7f36154,0x25deda752c2ac890537d,0xb22412bf6dba96156448,0x958659120d57b4bd230c,0xfd3748cc2c8905abfb46,0x41cfae8ba06616448355,0x859120e5f74dd0330b22,0x740c8b089053fbb06959,0xfe6d7a0645844835f5d1,0x12097f36fd0322c22412,0xb2b089053fbb065d9161,0x599559584482dbdd832a,0xb5f760cb2cac2241c9f6,0x8904bfbb06a56561120,0x659844825fcdb740cab,0x36bd032cc2241afae8ba,0x5b7bb0691855952097f],#[0x965482d7dd8348c32ca9,0xd230cb2a41a9fe95a461,0x7db4e958659520b4ff6a,0x4829fdd8348cc2ca905a,0x30b2a414dfed5a466165,0x6e959859520a6fb69d2b,0x5fcda740c8b0a90727fa,0x2a414dfed59464d85482,0x5946152096fb69d2b26c,0xda74acb30a904b7db6e9,0x1afae8ba0651864825be,0x60550d5f74dd0328c324,0x24a9302a8736d84e4952,0xbec9a859152542bb6da7,0x50b67b69542c8a92a13d,0x22a4a85a7db6aa164549,0x3a8591525425bedd550b,0xedb65d42c8a92a13de6c,0x4a8477db9ea164549509,0x619525435b6c3744c22a,0x68cc2c8b12a16dbec9a4,0x567fb56616458950b57f,0x62542d76d9530b22c4a8,0xc2c8b12a16af6d298591,0xdbaa616458950a5fb734,0x42b7cd8730b22c4a84af,0x8b12a159f6d798591625,0xe618458950a7f361cc30,0xf6d9530ca2c4a8537db5,0x2a14bf6da98651625429,0x8658950b5df64d230cb1,0xa74acc2c4a85a7fb5691],#[0x2fbed1a2a61625423bed,0x895087ff68d4d30b12a1,0xac930ca847fbb4683985,0x6d3a56498654353fd374,0xd5db0bd1308b12c12df,0xb04b0727f95595846096,0xa4a6172442b3eda72ab2,0xfb6ed2530b9221afb6c9,0x907fa9ba5915250120d3,0x4940483bf4dd32ca9280,0xad22c4a0241dfaee9965,0x7e9ba6556250120ff536,0x483dbddab46c2a80907,0x2a4a8241edeed5a66154,0xba5516254120fed372b2,0x3f74dcac8b12a0907f69,0xa8241fda695945895048,0x916254120bfd374ca2c4,0x4cb348b12a0907f69b56,0x417faee5a458950483f7,0x454120fed36ad12c8a82,0xb44b22a0907ee9966896,0xee611a9591504837f4d4,0x120def76ad4ac8a8241e,0xc22a0907bebb268d8454,0xd5a661150483df5d934c,0xeef76ad232ca8241edee,0xc0907ee9b95516258120,0x458960483f74d2b28b12,0x32ad12a8b0241fba6d59,0x6fe9a96895458120fed,0x160483bbddab52aa2c09],#[0xd12c8b0241fba655a259,0x7db96196555120fdd36a,0x483d3fdcb0cb2aa8907a,0xcaa241adfee5a859554,0x96598655120f4fb2cd2b,0xdbfdab52c32a89072ffa,0xa2418ffea5a961954482,0x58655120e7f760d4b0ca,0xda352c32a890737fb56a,0x1adfed5a9619544835df,0x55120a7fb7554b0caa24,0x52c32a8905bbdb4ea586,0xf6d3a961954482dbedaf,0x20d6fb6bd4b0caa241ae,0xb2a890777bb568196551,0x5a8659544839dfda350c,0x7f760d1b30aa241cdfed,0x890737fb568d9855120e,0x661544838ffdbb46cc2a,0x6ad3330aa241cfeec1a6,0x77e9a56499059120e6ff,0x64483d3edcb0ab2ac890,0xc2cab2241eafed198595,0xda66558559120f4ff6ac,0x83d3fdab4cc2ac8907a7,0xab22416dfed5a9615644,0x6a58559120e7f760d4b0,0xdfda352c2ac890737fb5,0x241adfed5a9615644835,0x9559120f57f68c332ab2,0xab30caac89073bfb4661,0xaef697a4661644839bfd],#[0x9120d77f4bd2330b2241,0xacc2c8907abfa6e91985,0x697a066164482ddfda34,0xe7f74bd0330b2241cfe,0x2c89073fbb0695985912,0xa0645844839bfd2b4acc,0xf36fd0322c2241cfe65f,0x907afbb06596561120b7,0x9584483d3fdab2cb2b08,0xad4acac2241afeec1a95,0x3fbb06599561120d6ff6,0x44839bfdab2ccab08907,0x72ac2241cfeec196e558,0xa2e819661120d7f760d3,0x35fcd2f40cb308907beb,0xc2241afee97a06598448,0x959661120b7f36bd032c,0xdd874acb308905bfbb06,0x41ebeec1a4619654835f,0x859520f4ff6ad230cb2a,0xb48cc2ca9073fbb06919,0xdfed5a4661654839bfd2,0x520d7f761d2322c2a41c,0xc9b0a906b7fb5e919161,0xd3a564d854839bfd2b28,0xe6ff6acb328c2a416df6,0xa905bfbb06919661520,0x4659854835bfd2b48cb3,0xb69d2b2cc2a416dfed5a,0x7beba2e819461920b6f,0x1864839fccaf40ca30c9,0xd0328c3241cfee57a065],#[0xfba5e819461920d7f34b,0x483d7dd3740ca30c906b,0x28c3241afe657a065186,0x56559461920d6ff4acab,0xdfdd834aca30c90737fa,0x92a16feec1a465586482,0x96454950ecfb52c32c8a,0xdcb48c32a4a87a7da961,0x1b9f6a19559162542dbf,0x58950dcff50caac8b12a,0x30b22c4a86affa866164,0xf6ea9859162543b3fdab,0x50dcfb52b2b08b12a16b,0x22c4a8737fb566184589,0x165651625427bfdab52c,0x5ff50c3328b12a1b9fea,0x4a863ffa86619458950d,0x65162542df7d9350ca2c,0x6954328b12a16fb6caa8,0x5afdb6aa19458950b77b,0x625429fedcd50ca2c4a8,0x4328b12a12ff6eaa8651,0xdb5ea194589509ff361d,0x43d3fdab48c32c4a84f7,0xb12a16fbec9a4661625,0x6919858950b6ff6ad233,0xbfd2b48cc2c4a857fbb0,0x2a15dfed5a4661625433,0x9858950aefb69d2b30b1,0xa341cc2c4a863fdb46a6,0x9fe6c1a4e61625433fcd,0x8950cefb6ad2730b12a1],#[0x8c930ca863fdb8693985,0xec1a4649865439bfd2b2,0xd6ff4ad2324c32a16fe,0x30ca85b7fb5691926195,0xa261162582dbeda74ac9,0xf74dd0328c12c1bbb657,0xb06ef965e819460960dd,0x51825835fcc2f40ca304,0xab2b28c12c19fe657a06,0xb7fa56159460960dcff4,0xc600930060002d00006,0x1890156012f00fc00db0,0x2940261022e01fb01c20,0x36f0336030902e202a90,0x45c042f040803cf03a80,0x54f052804f504c8048f0,0x64205fd05ca059d057c0,0x74d072606f906c006810,0x82e080707e007a707800,0x90308dc08af0882085b0,0x9e409bd09900969093c0,0xad10aaa0a770a440a0b0,0xb9a0b6d0b4c0b1f0af80,0xc690c3c0c0f0be80bc10,0xd3e0d1d0cf00cc30c960,0xe1f0df80dc50d980d6b0,0xf060ecd0e940e670e400,0x50fcc0f930f660f2d0,0x12210e910b01077103e1,0x239120c11d311a011611,0x31a12e712b4128712601,0x42513ec13b9138613531],#[0x52414f714ca1491145e1,0x61d15f015c3159015571,0x6ec16c516981671164a1,0x7af178e1767174017191,0x8781851182a180317dc1,0x9891956191718d8189f1,0xa521a1919fe19d119b01,0xb4b1b181adf1ab21a7f1,0xc201be71bc01b931b6c1,0xd131cda1ca71c6e1c471,0xe181df11dbe1d7f1d401,0xf231ee41ea51e661e391,0x101fdd1fb61f831f501,0x11b20e220a9207620432,0x23e21ff21c0218d21542,0x367231c22d7229e22712,0x4482427240623d9239a2,0x4f924d824bd2496246f2,0x5bc259525682541251a2,0x68b2664263d261625e32,0x73c271b26fa26d926b22,0x82f280827db27a227692,0x90a28d728aa288328682,0xa2d29fa29af296a29372,0xaf62ad52aae2a8d2a542,0xbb32b862b5f2b382b172,0xc8e2c672c402c1f2bf82,0xd512d302d092ce22cbb2,0xe1a2df32dc62d932d6c2,0xee32ebc2e952e6e2e412,0xfb22f792f4c2f252f0a2,0x75304e302730062fd92],#[0x138311130ea30bd30963,0x1fb31da31a7318631653,0x2ac32913276325b322e3,0x321330632eb32d632c13,0x3fc33d533ae337b333c3,0x4d7349e3471344a34293,0x5a63585355e353735103,0x66f3648361535ee35c73,0x70836e136ba369f368a3,0x7bf37a43783375637293,0x8763855382e380737e63,0x93f391e38eb38c4389d3,0xa1a39f939d2399f396c3,0xae33ac23a9b3a743a473,0xb943b793b523b2b3b0a3,0xc573c303c093be83bbb3,0xd203cf93cd23ca53c7e3,0xdf53dce3da73d7a3d473,0xec43e9d3e6a3e433e163,0xf6f3f4e3f2d3f063eeb3,0x44401d3fe43fb73f903,0xdd40c840a1406e40594,0x17641494134411f40fe4,0x227421241f141d041a34,0x2c042994278425d42484,0x33b4320430542f642e14,0x3ec43cb43a4437d43504,0x4914470444f442e44134,0x4dc44c744b844a3449a4,0x533451e4509450044f14,0x58a45814578455745484,0x5ed45de45cf45ba45a54],#[0x65c463b4614460b46024,0x6c546b646a1468c46834,0x722470746f846e346d44,0x78b4770475b474647374,0x7d047c747b847a947a04,0x8394830480f47fa47eb4,0x86c485d4854484b48424,0x8b148a8489f4884487b4,0x90e48f948e448d548ba4,0x995497a4953493249234,0x9fe49e349c849bf49aa4,0xa494a3a4a2b4a1c4a0d4,0xaa64a914a884a6d4a584,0xb0f4afa4af14ad64ac14,0xb724b574b484b334b244,0xbdb4bc64bab4ba24b8d4,0xc264c174c084bf94bea4,0xc714c624c4d4c3e4c354,0xcb64ca74c984c894c804,0xd134cfe4cef4ce04cd14,0xd8e4d734d584d434d2e4,0xddf4dd04dc14dac4d9d4,0x29e11709917e123cdf44,0xc51c5823dc490a2b8364,0x81f716400e80de08607d,0x9004003e81d820714713,0x168166085c5607dc4dc5,0x4bc58b716f1208e18238,0x1741ef1245c5608607dc,0xc48c05aa4023b81cf153,0xb164007e073c508ecc5b,0x43020a3b41f81c714712],#[0xc51c4e077c4507ec5925,0xc1e713316481689028e9,0x9043e03a08923b81c714,0x170166075c54c5823dc4,0x81cf1531741ef1240220,0x8ecc5bc49023b036a41,0x208e182040de077423c5,0x4e077c4507ec593316f1,0x17712309010fa8e9c51c,0x903c58e03ac1f71581db,0x8e4cc54c4d07e077c40,0x3781c041d09315312716,0xc4f427c46075c5932404,0xb137163017016023cc54,0x905c592040c1fb1581d,0x2020fac52c4e077427c4,0xa3b81d31531341ef1630,0x79d0dc5023e45dc48e,0x871581c7139177084008,0x5645c883c49274383a05,0x123b0fa0dd07c072493c,0x6d01c836f1541f916f,0xec0ddc23c5607645bc49,0x3af15221916f123016a0,0x73c5645c883c48f0368,0x712a219160582b0f80de,0xe075c5307e45dc48f715,0x4b1351781d708400de0e,0x4d45e0716a4153c058b1,0xa9014f50d8495c22c52c,0x681d315313d1650170d0,0x91434324112422041fc3],#[0x40730dd07ac52c4b45a4,0x4b13221d16481b290488,0x58e83ec3741f01c924b1,0x106072c55c210dac4b4,0x437708b14b1381dd163,0x52c4e077c45c23458901,0x9b1581cd17b12300dac,0x905c27c4607745922417,0xd16058301620fac52c48,0x645dc48d315313f10a21,0xf912f163e0db075c5288,0x4bc58c06d01c83f91541,0x20f163c0fa1064548864,0xc58e03ec3781d9159132,0x300fc8ee07645644b07d,0x93436c1d915912a21716,0xdf8450d5458c8784,0xd17e12321c343c0e807f,0x345f8430d0c81f01c037,0x7709e138343b0e784cc8,0x5b8a01e0d03c83a30591,0x17e1392037c1d42784cc,0x802c5d861213a04de00b,0x4011009c0ad84584a487,0x61105e13e10e19316090,0x84784b8a4c5824100660,0xe13b1609e30178134417,0x2c5e480198c067e10921,0x3e00921b163051784f84,0x3784ac5e480e04de11e1,0x13e00b16285178478001,0x84b843866c58e93c93be],#[0xe10e19b16374274118a3,0x6318a6c58de13d09d05,0xe12e11b163012784f84,0x3584f802c58fd09d0560,0x21e01b163d84251a5106,0x8018d0e18c945e13e109,0xb163e51e51648784f847,0x8e18c946945e13e11e00,0x63251784248784f806c5,0x946945e13e11e00b1638,0x8133c2780784d458a18c,0x9d05709a13a11d17a183,0x4c187847802c26458ea2,0x13e01e119169203a51f8,0x847802c26459014405fe,0xe19d163017a51f41784f,0x7458630be13b09d05e10,0xf09e015163784f8418a,0x45417807458e05fe13e1,0x1381e7344817bc2784f8,0x382101c07c076f11716f,0x501481ebc43c55c5e079,0x15716f1208e360840701,0xc55c4bc5e079205a058f,0x863816816608023821d,0x1201d82171571381ef16,0x1f6075c4307ac5dc48cd,0xb17712c1f3344a0f48a8,0x8cd1283c82181c07d711,0xdc8adc46072c5dc4b07,0x81d710b17714c1e4a0f2,0x6c5b079283d22e05423b],#[0x8ba086070150215c45c5,0x22f71023ab17714c1e4c,0x4c5bc4d079283c83781d,0x2529040f016e0708ebc5,0x13d41f715712b1781c54,0xec5d07a8e9405ca3b020,0x16950c080906071c51c4,0x5b71581d713b1608e40,0x5c55c4d07ec59208a05c,0x65423821017016950e07,0x58d41f715712a3b81db1,0x8e328edc4e07150d07ec,0x238e03b41ef14b16f120,0x4290500016bc56c5bc48,0x6ba04f10f1331633408e,0x15bc43c54c5823900820,0x316f1341e4e8101c0148,0x9103d03781ca40f1423b,0x220160173c54c5bc4823,0x714088b1771208e46810,0xd07ec5a8e9005d81c059,0x6c1e490fe070901c51c4,0x24181c08e05b715713b1,0x4c54c48903c5d079205d,0xef162404410a8e816e07,0x79208b02181cb14b1341,0x16e07022ec56c4bc5d0,0x5b1381cf1608a3a8ec08,0x39c5d07a900e02141fb1,0x1371608e410dec56c482,0x79205ca41a04058b14b,0xfe0748eac52c4dc58903],#[0x59315312f1781c4210a0,0x73c58220e08805c08e0,0xb1207a3a8e907cc54c4e,0x8218e03641df06c1f317,0x6300f907307cc54c4ec5,0x60c325315313c1eb1608,0x8638218166c4823ec582,0xc08e059b12098b17d080,0x3a0701edc4ec5f4201d8,0x7606783781d712d09b16,0xd81edc4ac5f420198c0,0x68052d09715b1609632,0xa0ddc501eac5f4201a0c,0x260e07af12543b160982,0x302181e8163c4d426c58,0x8c086059712d09b16098,0x6320ddc481ef422c5821,0x18c859b15b1208ef1608,0x836c56c4a16023bc582,0x4d13b1408f059b13716d,0x790744e6c4188545ec4c,0x951741db13134560a10,0x881443c03782841fb10f,0x72c640e40a6c4545ec49,0x1d517b13134440da0a50,0x4581d8c06a43af09b114,0xd16076284d1885076c4b,0xec481e01d8ec1fb12621,0x607608e201ad073c2745,0x45c5288645c4893b1351,0x1c0523d0b207a0740ddc,0xc510f080817117159178],#[0x4a0ec0ddc43c2645e075,0x871591671205808e381,0x23e45dc4e071d0927437,0x71208e40220170165c50,0x8a74208805c059715917,0x208e3645dc55c49d0823,0x48238f80171571391674,0x8e301b81aa4d3c4645bc,0x4912072070f11916f140,0x7c0720dbc53c4e45c882,0x88f15916f1208e330fc0,0xc53c4e458160238c08a0,0x81cf15916f1341e4c813,0xc0da0e9083a824a41037,0x84e07016bc5488645bc4,0x5d714f0991771381c05,0x2c4d458160238e08e088,0x351781c53c52906812c5,0x5c342a41436124b14b1,0xec5016d45ec4e0714f14,0x341e05a402282101750d,0xf0c08a05db1408f517b1,0x8e2d0dec4e07545a9014,0xc20168ea41b15517b120,0x342530db45cc54c4e075,0x3cc36125315312d1781c,0xc54c4f45e071405d2405,0x50220200174905c20164,0x4181d315313d17220058,0x77458d08e08005c3432,0xd16342449030dcc54c4e,0x10241221314c3731381d],#[0x76c5023ec4b45d07a90,0x1db14d17b1208e30094,0xc072c52c4f458239041e,0x4d16b1208e429000920f,0x60239082581ca40436b1,0x904886072c52c4f4581,0xa83bb15708d16437b124,0x4c886073458901381c05,0x1e05a4a0930d822ac52c,0x43781c08bb14d17b134,0x6072c52c4f45c881322,0x16240c364a0fa0930d89,0x5981c83eb14b13709d,0x3cc53c24c4f45e070161,0x9135917712c1c501702,0x71483b330820083711b,0x882101584f3c43c5645d,0x1d916f13220440eacca4,0xc48238e83703a858f154,0xc1c4a495000173c5645b,0x4208e05d71405b917712,0xc52c4d073458d09608b3,0x630de0782289024910da,0x15b1243781ed1741c924,0x881005d24093d22008bb,0xf8902162c52c4d07745c,0x59b1541db13d17220520,0xc4b0d8e08e08805d2408,0x9a2c901076c5488745e,0x3458220a089b12c1dd16,0x1d16343c1c310dec4f07,0x4f458d0f070db15b1208],#[0x9bd17b13e0430162c52c,0xc26c4b0774588089b080,0x58a437b12d1615dc1c2e,0x13d1630226c23076c4f4,0xc4b458c81c06c53406b7,0x712d16394e607e0714d5,0x7458c06a06653581f81d,0x609432077c081b01c5c5,0x594910070069711714d1,0x2281b607e071c51c4d4,0xc088086f14f1351606c3,0x32075c55c481b7458220,0xc08808781f81d712d16,0x3407fc1d07345bc4820,0x68ac3e24141cf13d1608,0x1609a28223c4d0774582,0x810160220a089b1208fd,0x71781d7080583b45ec4f,0x5c5e071cf1273d915912,0x84820017610645644816,0x70808f91591371781c05,0xe44e075c59cf0e08805d,0x371781c73c321064520f,0x4bc5c882491283f91591,0x8e230dc07c0720fe4564,0x453c581b0d914f179120,0xf1781c0583807644a496,0x3c5c0f9008941f915912,0x838202105c2645644e07,0x23a41f81d915912f1608,0xe45644c883c5c0fa1010,0xf41cd12b1633c5e07016],#[0xc3f81e08423a924d1443,0x34510fe07b44d076c598,0x4017250c8ea49488021,0x5d23a85941dd13b1722,0x907744c886c5b0f8c080,0xd51405b513b16c1c4c8e,0x72c58220a08514333c05,0x9d15b16c1c30cf744f0,0x22744f076c58bd1208fb,0x33dd12b17c1c05828cf0,0x1c37450816c5f448238a,0x448c43ed14d13b1615dc,0xf1638206c27453076c5f,0x1608483f04191591341c,0x22817645644850bc5d07,0xf1608a341060facf2490,0x1c58238b83f91591341c,0xd717d140803545544949,0x4d073c58220c81dd1206,0x3b41cf160883c07b4534,0x23bc58220cc37d15d122,0x717c1c0883745744d810,0x544544f458c525515512,0xa1dd13d162a8781b287,0x3287a87744f4588a1fd1,0x90a1e26ca1d511513d16,0x81780149d44546345d44,0xe01d13d10d195163ec27,0x780344b445458db09e05,0xfd10a1dd13d1636c2781,0xd687744744b458e26ca1,0x1cd16f1208e368868794],#[0xc56c45877458cd25f072,0xb15b10d1761c304f24ce,0x6c4ec564581e8c13c923,0xdb13b1591608e200904f,0x3823c16c16645ec4b420,0x3613407b713d0991607c,0xdf817805c4e45b42128,0x53916d08301f01de0ee,0x3c4e4581e8f715711055,0x3916d082a16a16150942,0x5745ec4f420d05b05971,0x5e01b13d16328fa876c,0x817806c4b458bb14d09e,0xd09e05b15d17b1236c57,0x7817806c5345ec48e08f,0x4a1dd17d09b123023f42,0xfac52c4f45f420ca3fb1,0x99a1db15d17b123a9028,0x817806c4f458a09c09a0,0xe05e01b13d08d162b427,0x238177426c4f4598711,0x9b12d1761c15c2a16c16,0x26c5745f817806c49008,0x17e05e01b123a50a4f10,0xc554581b0893c925b14d,0x389711713d1608e23c4b,0x1408fd161dc45c4b4582,0x171508e1dc5345823877,0x8e23c4bc55458238971,0x5c4b4582389715713d16,0x208af1781f21cd2455c5,0x58221008844083ed14d1],#[0x51008ed08745487744bc,0xc525515513a1c7160883,0x3850ec5e45644e490218,0x8b17e05913915e00924,0x6301b645644822ec58bd,0x60fd09e05e01913914b1,0x8168166c5e45644b4202,0x4099e05e00b17913d084,0x544f422c59205a05991,0x16328ea8dd4501ef8178,0xc58ca37d14a1dd13d09b,0xd12328ea8df45744f422,0x6c58ad09d15e05e01b17,0x3d08b162a8da87744f42,0x7456c5f448ca3aa37d1,0x15b17d08d12334278178,0x4f64564482191e05e00d,0x914d083216a161423c59,0x3448238991305b059717,0x2389d09d15d121824345,0xd15d1371630243453448,0x1a8cd6c48c08fd09e05,0xf41db12f16281b9076c4,0x7ec45076c4bc58e06f41,0x5b11b13716381bc1b50,0xc5cc90238a09206dd09e,0xb14b1331608e26c4ec54,0x822cc54c4cc96c58238c,0xc58cc1fb14c1db13b162,0x883021507bc4d073c56,0x8228a06c41c08bb15b12,0x59160843507ec4d073c5],#[0x4f458228c837d1207bd1,0x12d16086320f821e4564,0x455c23459053d7099159,0x862e1060ff81780644e,0xf44dc20ef09915913516,0x37084026023a16745745,0x9808e85a859d14d17d1,0xc16c16744d45821bc210,0x8d15516d1208e3026023,0x76c481d3c27458a05a05,0x7a854853708d17b143d0,0xd81a6c53c25458e0960,0xf12f1551606c341ed0ed,0xec4bc2021d458d43b436,0x641dd15d13b082d0ed0d,0x190f8243453448238c08,0x8ca3dd12321a16076282,0x23020f44bc268581e01d,0x388c3b05db09c16d05b1,0x13d0405836c5705ec482,0x58177410eb15b09c16b,0xc16c1c2ec2780026ec4f,0x6c4b417058c437b09b13,0x5c1605de00330ef806c2,0xebc4f058200c09db13d0,0x17709b12d04305030950,0x44f806452c20e08f05dc,0x913b08e163250c16785e,0xe456448238d915e01d05,0x791591208e3050008785,0x5785e44e4810942209e1,0x13d043826021816f8064],#[0x858c09bb09914059e179,0x5a3645380741644ec27,0xa878b915e00e17913b08,0x4e17b08388df44f41785,0x4a480ca3c01e237d13d0,0x17b084050745780785f4,0xc942020140d14d13e01e,0x3017785e453416448268,0x89914e17913709d04058,0x7d1407a33c2744d85821,0x5f448260a005d12f09e1,0x12f09e160862bc274578,0x45585b448160238a001d,0x437425d12f0961608633,0x5103c594ef057048220f,0x961561303e717d044b09,0x4cc58218d24262433db0,0x66d0f7081c893c268568,0xa3b02040183415c2060,0x38c08a08405c05a542c0,0x3a1826022017507e8102,0x16b000238228a41f70ca,0x5d41fa0409808e28170,0x5808e098181e81482586,0x170165c21d0e070238e0,0x5c53da04c0005a38220,0xd0f002810160e08a084,0xc08f41ea402822020017,0x28174885078238a43781,0x48830d8a08a05a08e182,0x8221b0cc361a0fe07090,0x81ec362823c880228168],#[0x50760790d8c34224083f,0x143681e09a28220176c3,0x9410200160268608808,0xa202282201b7428806c,0x238268160608808606cd,0x8005d70873d81c05838,0xc0fa0928ea105078c088,0x5c73ca040580883410,0x30cf08ea0de07b0f8a08,0x8808005db0b81f41c43e,0xfb088582820016781026,0x73000168228b04104283,0x9c09a06c09893c282101,0x1681614f07d080a4f020,0x181b68714f0603d21c10,0x8e08260238409c09a08e,0xc09a08e1827026823860,0x53dd0a129028fa870609,0x81e81681678014f0a,0x608e059e0409a238002e,0x9c09a08e18270268238,0xdc186d1608e174582384,0x808830238208e08069c3,0x62508a08e05d81e60485,0x42925b0a302702681b02,0x85421ac28208a08806c1,0x8e10168160260605a05,0x8609808e102602385d08,0x4f09d0808e1027026823,0x89b0a08e191010fc872,0x8609c09a08e1f422c284,0xa089600508201b5423c2],#[0x38408e0823dc29420608,0xe20238208f70a13c282,0x41ec08248406c018b02f,0x20218c2cc30a08a06d32,0x8208e08c90208e082282,0xdb0c16c281b0406c0823,0x88086f0a08e20238206,0x9d0a25c28208e0bc282,0xf7081dc23428408606d7,0x7081a16a160238609808,0x708281d5c20409808f,0x69c24c18c135e05b03e,0x53b06096201ea152148,0x5808e191691602387055,0x885a85808e2023820988,0xb081026416c160238809,0x8408ef0a12c202384087,0x21ec20406cf0a1026023,0x69161c28845808e09818,0x23ec25c28670a082391,0x16d0d8608e859b0a0982,0x10205d02405a09c24c20,0x5018d8605c6369041f4,0x16816026060580981409,0xb48d8270268805894210,0x1b0607a45a059b08201,0xc2543541086360a8de48,0x24804098b09308180da,0x401250a4804940920125,0x294292012506c2049429,0x70268160608405c17828,0x980823a160408e098101],#[0x260485a0981026823840,0x78409c09a098d2024168,0x816dc204087708102198,0x164c10238809a09808e1,0x60238608e0988581a168,0x808e85a0988582026a1,0x504245a1023c16826416,0x60443e224086182190f8,0x50f8c28608e098150711,0x4580d10]]
set_option maxRecDepth 16000 in
def g255H9 := limbs80 #[#[0xc20cb1424c2041080840,0x320600608d54200a1922,0x4c900824034303c54210,0xc01404ca6c3080082002,0x200201a00520a0111c11,0xc400c09c00b02d00004,0x200abc3aca10b454580,0x260d219,0x426c06300000c1d64098,0x506581bec06b44eb,0x41a214df21cf81b44090,0x9160925684b5856185f7,0xc56d85e8000145a6c24c,0x94ed843c00000003,0xc51c5240c4a6023040ec,0xc218010d542c00004153,0x4434d1cc0002c6824063,0x418a14e40000000341a7,0x2225864c000080a00003,0x381eb9574843a121e,0x84dc00020124c055405c,0x2412fc0100000,0x616781fbd4a0,0x260b7c1281247409c,0x4ef14f8252c125b4a28,0x29467415c00034623,0x140375493902fc28c,0x14d80000000310b18278,0x51b601c8000000000003,0x1120000084e500004a40,0xbe216e8147c22a00bb,0x802a01bb82a0d00005c0],#[0x115cc05b4271802280d5,0x161d000000001c043,0x19176d0258148,0xe234000184fb54aac050,0x2449c470000000000001,0x21a88066810400000003,0xc27c055d14e0d4bb,0x3d494e244000180a8,0x917b40a4000184d99428,0xd2340074000361edc195,0x119408195780003,0x111aa51f800030178,0x6001c1c240c584580000,0x94fc0000000382080001,0xc474862941cc807c0003,0x127040e98190000151ed,0x240b784e0c243c20e,0xc525c1f0008400029128,0xc1854298000321680000,0xa08c0000a1da801ac236,0x141dc000202380003,0x80f506100002c1b00000,0xd49c01aa04fcd116,0x41d0c518d01fd5800000,0x5584000041ecd5700002,0x211c486428469660158,0x440200e400000002822f,0x2406e14780001,0x819800014134000321f8,0x214600002510e81e0,0xfc0002811f01618640,0x40e0206c0000d57f4166],#[0x12645274860c00000003,0x145105c0add1e0116f,0x818c00008478052b40d9,0x14ad5020000000000002,0x11d0000390d2445cd4f4,0xc01dc68c814c826a927d,0x25c41fd54d3c0d00002,0x45384103c00ad26c1113,0x4277048ada400000949b,0x2823dca50c6140003,0xc4564175c13e02800110,0x9061c172026440464250,0x41c581da9109416b824b,0x38685446b40f80002,0x10a6160000185bea1e0,0xc04ac2170079522c0001,0x4225002e558b44f54138,0x808ad4d400000001c096,0x116b047f017d003c0002,0x1c08f40ded0b9908d,0x95004221c21cc0040000,0x28288c29c0002,0x4204064700c800000000,0xd212519c90b400008031,0x4027003814f0000051d8,0x9f4,0x5680003814182548294,0x2848c00009223a1ca,0x20246442944d5c554,0x606a8130000000000000,0x5034114000081f54155,0x41e6222c000000009019],#[0x419c4638400d41ae55b5,0x94e85426120341225419,0xe15f861fd048d41fc0c0,0x241800001c0b05170,0x203f54b014300000d260,0x40f00000103f804e50f3,0x25aa2195196a10d1226,0x280cc9289d18951c9,0x62200001a21000000290,0xa95800000000c16c1032,0x24071d4389437]]
set_option maxRecDepth 16000 in
def g255D10 := limbs80 #[#[0x4250120eea6154250120,0xfca5515250120eea619,0x16250120dda655525012,0x20dba6596250120faa59,0x515254120eda61152541,0x120dda6595254120ddae,0x5956254120ddae595254,0x8120dba6596254120f9a,0xae516258120eba611625,0x54110dbae556258120db,0xde6954254110fda54942,0x254110edee115254110b,0xafe6938254110bdee915,0x8448510cfde5f8448510,0xafd6938748510afd69f,0x38254510cfde53825451,0x109fd6939254510afd69,0x515250910afd693825c5,0x910f6b5d17250910fcb5,0x6a787509108ffea58550,0x49109fee8197509108ff,0xf6a78454910afb68b845,0x5c910adf69698549108f,0xff6a7845c9108ffea584,0x85c910a7fe9d985c9108,0xa7f69e985c910afb68a9,0x97609108ff69f9460910,0x8ffe9594e09108ff693,0x195e09108ffe9d94e091,0x108ff69392615108ffe9,0x9192e1d108ff6939261d,0x120fea50951501208ffe],#[0x5954250120fea5097150,0x120fea5915250120fea,0xa5955250120fea691525,0x50120dfa6595250120fd,0xfae995250120bfa69952,0x250120fea6916250120b,0xdfa6556250120fba5956,0x6550120bfae956250120,0xebe6196550120ede615,0x18550120afe6a1655012,0x20afee998550120eeee9,0x958650120eeee9186501,0x120fda5499154120afee,0x64d5254120bfae899154,0x4120fda5915254120fda,0xa6595254120fda651525,0x54120fda5516254120fd,0xfa6116254120fba59162,0x254120dfae516254120e,0xfda6956254120bfae916,0x5454120fba6596254120,0xdde6595454120fda689,0x95454120ddee59545412,0x20bdee995454120bde69,0x596454120f9e59564541,0x120ede5958454120dbe6,0x6598454120edee958454,0x4120cfee598454120cfe,0xe5979454120bfae89945,0x541209fe69b9454120dd,0xfe69396541209fee9196,0x258120fba55162581209],#[0xfba6556258120fba6516,0x5458120f9e5955458120,0xfba6896458120bbe699,0x56458120dbee55645812,0x20ebe5958458120bbee9,0x998458120cfee5584581,0x120bfae899458120ebee,0x6979458120dbe5979458,0x45209fe69395581209fe,0xfe9d845c5208ff6a3945,0x55120dfa6499055120a7,0xff6a391551209fe68391,0x3551209fe68393551208,0xe9f61965551208ff6a39,0x6555120cdf6616555120,0xecfe918555120adf6a1,0x98555120cdf659855512,0x20adfe998555120cdfe5,0xa58655120cbf65986551,0x1208ffea586551208ff6,0x6a396551209fe6839655,0x5120aefe9198551208ff,0xee819855120adfe95985,0x55120cdfe959855120cf,0xfa64990591208ffe9998,0x559120e9f6156559120d,0xabf6a16559120cbf6616,0x95591208ffea58559120,0xcbf61b95591209fe683,0x186591208ff6a3955912,0x20abfe958659120eafe9,0x999859120aefe9198591],#[0x120cfee819859120abfe,0xe9998591208ffe959859,0x1120afee819161120cbf,0xfaa56561120af768f916,0x61120afee8195611208f,0xfee8196611208ff69b95,0x5595208ff6979661120a,0xe9fe998559520adfe918,0x8659520abfe918659520,0x8ffe919859520e9fe95,0x99859520cdfe95985952,0x20afee819161520cbfe9,0x959361520adfe9591615,0x520afee819461520adfe,0x69b9461520adfe959461,0x1520adfe9596615208ff,0xee8194619208ff693966,0x61920abfe999461920af,0xbfe9995619208ff69794,0x2605508ff6939561920a,0x8ffe9192e0550ddbe495,0x8454950e9f6196454950,0xcdf65b8454950bdbe89,0xb8454950cdfe5b845495,0x50adfe918654950adf69,0x978458950adf69386549,0x950abf69b8458950e9f5,0x59794589508ff6a78458,0x89509df6979458950d9f,0xf6a39458950cbf61b945,0x58950abfe9186589508f,0xdfe959858950abfe9998],#[0x858950afb68a98589509,0x8ff6a69858950abf69a9,0x98589509fe6839858950,0xd9fe5965609509df697,0x594e0950cbfe59866095,0x508ffe9994e0950cdf59,0x9592619508ffe9192e0d,0x9508ff6939261950adfe,0xe8984589608ffe9192e1,0x8960cbfe578458960bbb,0xf6938558960abf697845,0xe0960d9fe556560960ab,0xffe9594e0960cbf59594,0x2e01518ffe9192e15608,0xffa64942541108ffe919,0x5254110bfe6a54254110,0xfde6915254110fde651,0x19254110efe653825411,0x10bfee919254110dfe65,0xa15250910efdaa174485,0x910ff96857250910efba,0xaa17250910efb6a17250,0x910cffaa19550910efb,0xd6859750910dfee81975,0x50910cff6a19750910df,0xdfa615454910cffaa197,0x454910aff6a78454910e,0xf7d5d1915c910cffa619,0x915c910efde11915c910,0xe7f661745c910dfd651,0x5845c910e7fa61745c91,0x10aff6a7845c910affea],#[0x61945c910bfee81945c9,0x910cffa61945c910cff6,0x692985c910affe91985c,0x120ffa6855250120aff,0xa6995250120ffa68d525,0x50120ffa6956250120ff,0xfe68d8550120efe68585,0x650120efe6998550120e,0xefee958650120efe6958,0x9154120fde5519154120,0xdfe6519154120efe611,0x16254120bfee91915412,0x20ffa6916254120ffa65,0x119354120fde55193541,0x120dfe6519354120efe6,0x68d5454120fde6855454,0x4120fde6595454120fde,0xa6896454120fde699545,0x54120fde6956454120ff,0xfe6a56454120fbe65964,0x454120bfe6a56454120d,0xbfeea56454120dfeaa56,0x8454120efe6858454120,0xefe6598454120efe68d,0x59454120efe699845412,0x20dfe6599454120fde59,0x895458120dfe69196541,0x120fde6555458120ffa6,0x6a55458120fbe6995458,0x8120bfe6a55458120dfe,0xeea55458120dfeaa5545,0x58120fbe6556458120bf],#[0xfe6558458120fbe69564,0x458120efe6958458120e,0xfbe5959458120efee958,0x9458120dfe6559458120,0xefd6858454520bfee95,0x58454520cff6a5845452,0x20efd685845c520cffaa,0xa5845c520e7fe9d845c5,0x120dfe6459055120cff6,0x5959055120dfe64d9055,0x5120dfe6599055120fde,0xf6619155120edf615915,0x55120edf6159355120cf,0xdf6616555120cff66193,0x555120edf6858555120e,0xedf6598555120edf68d8,0x8655120edf6998555120,0xebf6598655120edf695,0x58655120cff6a5865512,0x20cffaa58655120aff6a,0x619655120affea586551,0x120dfe6819655120cff6,0x6859855120cff6a19655,0x5120cff68d9855120cff,0xe5959059120cff699985,0x59120dfe6559059120fb,0xbf6616559120bfee9590,0x559120edf6558559120e,0xcff6a58559120ebf6998,0x8559120aff6a58559120,0xaffea58559120cffaa5,0x19559120ebf619955912],#[0x20ebf6958659120cff66,0x919859120ebfe9586591,0x120affe959859120eefe,0x6959859120ebfe999859,0x1120cffe959859120cff,0xf6559161120efee81916,0x61120cffe559161120cf,0xff65d9161120affe9591,0x161120cffe5d9161120c,0xedf6556561120affe9d9,0x6561120ebf6596561120,0xcff6599561120aff6a5,0xf9561120aff687956112,0x20cff65b9561120aff68,0x879561120aff69b95611,0x120cff68f9561120cff6,0xe819661120cff69b9561,0x9520affe959661120efe,0xfe918559520edf691855,0x59520ebf6918659520ed,0xff6919859520ebfe9186,0x161520cffe919859520c,0xcffe519161520cff6519,0x9361520affe919161520,0xcffe519361520cff651,0x59361520affe91936152,0x20cff6599461520edfe9,0x5b9461520aff68f94615,0x520aff69b9461520cff6,0x68f9461520cff6879461,0x1520cff69b9461520cff,0xfe959661520affe91966],#[0x61920efee819461920ed,0xffe559461920cff65594,0x461920affe959461920c,0xcff6579461920ebfe999,0x9461920aff6979461920,0xaffe919561920cff697,0x39561920ebfe99956192,0x50cff6939561920aff69,0x515260550edf61152605,0x550bdfe915260550ddfe,0xe918260550cffe518260,0x49509ff6939260550aff,0xfe518354950edf611835,0x54950f9f6196454950dd,0xdf6a16454950edf6a164,0x454950edfaa16454950b,0xedf6198454950bdfea16,0x8454950ddf6598454950,0xedf6918654950edf65b,0x16458950f9f655645895,0x50dbf6616458950ebf66,0x616458950ebfa6164589,0x950f9f5958458950dbfe,0x6618458950ebf6198458,0x8950cffe618458950cff,0xf6a78458950edf657845,0x58950f9f5959458950af,0xbf6199458950ddf65594,0x458950cff6619458950e,0xdbf61b9458950cffa619,0x86589509ff6a39458950,0xaffe919858950ebf691],#[0x19858950ebfe99985895,0x50ddfe9598589509ffe9,0x939858950aff69298589,0x950bfee8191609509ff6,0xe518360950bdfe959160,0x950bdfe959360950cff,0xf5979460950edf595846,0x60950cff61b9460950dd,0xdfe9596609509ff69b94,0x4e0950cff68594e0950b,0xcff69994e0950cff68d9,0x9261950cff6519261950,0xedfe959261950affe91,0x58458960ebfe99926195,0x60dbfe558458960ebf61,0x578458960bbfe9584589,0x960ebf5958460960ebf6,0xe819460960cffe558460,0x960bbfe999460960bfe,0xf6179460960dbf597946,0x609609ff6979460960cf,0xff6939560960bbfe9995,0x2e1560cff69594e09609,0xffe6a56454120cff6919,0x9458120ffe6a55458120,0xeff6a58655120ffe695,0x59059120effea5865512,0x20eff6a58559120ffe69,0x959859120eff69598591,0x120eff6959661120effe,0x6919661520effe959661,0x1920eff6559461920eff],#[0xfe959461920eff695946,0x54950eff6919561920ef,0xbf6616458950fdf6a164,0x458950fdf6558458950f,0xbff6a58458950eff6618,0x9458950fdf6959458950,0xdff6619458950fbf619,0x19458950eff6a1945895,0x50bffea19458950effaa,0x919858950eff69198589,0x960eff6919261950dff6,0x6958458960fbf6558458,0x960eff6558460960fbf,0xf5959460960ffee81946,0x60960eff6159460960fb,0xffe959460960dff65594,0x740000fbfe999460960b,0x5501ec0199013000d200,0x3603cd037a031c02be02,0xf60598054504f2049404,0xcc0784071b06d3066a05,0x55090208ba0867081f07,0xa0ab70a6409fb099d09,0x880c350bed0ba50b5d0b,0xf00da80d600d180cd00c,0x790f310ee90e960e430d,0xec1099105110090fc10f,0xc2126411fb119d113f10,0x4b140e13b0135d12ff12,0x15ce1570151214b414,0x9f17571704169b165316,0xb7194e18e51887181317],#[0x821b241ac61a731a2019,0x161cce1c5a1c331be01b,0xec1e831e301dc71d741d,0x5f20221fe51f921f3f1e,0x4b21ed218f212620b220,0x1623ad2365231d22bf22,0x89254c24f924b1246924,0x726bf2677262425dc25,0xd2287427f527a2275a27,0xa82a812a1829a4294628,0x472bf42bac2b6f2b1c2a,0x8e2d5c2d1f2ce22c9a2c,0x852f482edf2e812e022d,0x2430dc308930362fcd2f,0x3f320d31c53193316131,0x9c3349330c32da32a832,0x2534d234a0344d33fa33,0xae3650360835aa356235,0x3737e437a7376a370c36,0xcb3978392538d2388a38,0x803b0c3ac43a663a1e39,0xf33cb63c793c3c3bd33b,0x923e343dec3da43d463c,0xfa3fc83f8b3f433eda3e,0x78412540bc407f40373f,0xbf4282422441f241b541,0x643be43814344430742,0x79451b44de448b444e44,0xd64699463b45f345b645,0xc2486f480647a8473f46,0x824a2f49d14973492b48,0x794c104b9c4b284ad54a],#[0x4f4de64d7d4d2a4cd74c,0xf4fc74f744f214ec34e,0xfb5192513f50d6506250,0xe7537e532052c2526451,0xbd556a552254ae545053,0x7d571456b65663560555,0x3258c95855580257ba57,0x85aaa5a4159cd596f59,0xbd5c755c2d5be55b715b,0x305de85d8a5d4d5d055c,0x115fb35f4a5eec5e995e,0xd16173611560cd608560,0x7b632862bf626c623a61,0x4664dd647f642163c363,0x3266d4665565ec658365,0x9a6852680a67cd677a67,0x4469db6993692a68d768,0x306bdd6b8a6b216ab86a,0xcf6d926d1e6cc06c786c,0x426efa6e9c6e336e016d,0x2e70c5707d70146fab6f,0xee727a721171a8716b71,0x98744573fd73b5734172,0x1675b87570753374eb74,0x68772b76ee769b765376,0xfc78bf784b77d777a577,0x4e79f079be7981794f78,0x247bbb7b477ade7aa17a,0xfa7d917d3e7d017c987c,0xba7f677efe7ea07e4d7d,0x7a813280f5808c80397f,0x5082d18273821581b781],#[0x584a7844983f6839883,0x78863b85f385a0854285,0x59880687b3874a86ec86,0x2f89d18973891588b788,0xce8b5a8b128aca8a8d8a,0xe68d888d098ca08c2c8b,0xc78f538ef58e8c8e398d,0x9d912990b5906d90048f,0x9f934c92e39290921191,0x5f950194ae945b940893,0xf3967f962c95e4959c95,0xa8985597ec9799974696,0x5d99de9996994e98fb98,0x289bca9b619b0e9abb9a,0x99dab9d4d9cd99c7b9c,0xbe9f6b9f189eaf9e5c9e,0x3ca0e9a096a04ea0069f,0x83a230a1e8a1c1a16ea1,0x88a34ba303a2e7a2c0a2,0xaea45ba41ea3f7a3c5a3,0x16a5e4a59ca554a501a4,0x3ca70aa6e3a6b1a669a6,0x62a830a7e8a7a0a76ea7,0xbfa982a93aa8e7a8aaa8,0x260878881ee2caa9fca9,0xee24803a06c0778a08fe,0x201001f01d043c5b8a81,0x42788ef8941fe220718b,0x41fe260778831611c9f1,0x8b314625078e0780df8a,0x7f8bf110389142482077,0xc23920840f9203146250],#[0x800ef14c3107f89f1122,0x7c4c0e037e208848b200,0xb1c548b81ce248f1507,0x1522dc48471e0e81bf08,0xa312a2e07120740dc0e7,0x68b200d92012486fc218,0x824007fc202c31462607,0x42083e443c5c8a41f224,0x701ff1722a449101c07,0x820748a03f225c58f082,0xbc2145f093208688f090,0x434a2cc8709280de0013,0x14242109e13a05300708,0x83606ac1708e12e1245a,0x1ae1122d07f0913a301d,0xae1b709c22c1709d164c,0x704414717240624c0501,0x300a609c10e2c701982,0x405304609b163584d05,0xcb0582304b0fd163c0cd,0x40cc1160b04e8b1a0a00,0x6700c1160b04e8b1c0a,0x5206608b05827458c072,0xbc2048700317c248d100,0xe01c204818be12481e03,0xe1362c704608b8a70c,0x4d8b05e382804da0b847,0x6c5f081f42682e11c038,0x453458dc3180684d05c2,0x13a2c140c0cf84709b08,0x517c24130da0b84700e,0xd84e01a2f840e2778470],#[0x84700d160a0604c0bf84,0x8b84f085160cc6d05c27,0x5c0384709d160bc62182,0x4dc278428b1440c0614,0xc7d05c0384f087160a06,0x3b84d05c0384709b160b,0xc13584e11a0b80709716,0x9ac2709d05c038438b1,0xc09b41708e01c26c58c,0x130ce1384700e13a2c13,0x27458ce1384f08e01a2c,0xd626c58c0bf84582e01c,0x41d626c58c84107d8841,0x89717039c90e84107d88,0x540e71362c782103dc53,0x7c458b08e42a1a3a83dc,0x64b07900740878a41fe2,0x164b8a71247607788316,0x742251d81ce2907b89b,0x3b039c5389b1783c843e,0xeb1783dc491d14169202,0xa0ff1762ac4c0e240440,0xc518971783cc90e04022,0x3ec50477176248241038,0xd83dc5920169021b0408,0xb14838c5d89c1e4d8981,0x89c1f62c808e0740d992,0x5e0f201001f324838c51,0x4808e0b416702b15626c,0xd80ef15e27c420fb160f,0x1e10c700962dc4847100,0xf716301f01de2ec55894],#[0x8471344843b15c0ac4e0,0x703806e0a58841ca2ec4,0x9a0296210768bb120ec,0x2540e714e22458470523,0x860ec1b708e2a0748b71,0xfe27c448b08e501d036e,0x58401b83426bc501e41,0x206fc240e71411dc4c8b,0xa4086ec538481ca2ec49,0xe314e10c4e8b254f092,0x3e8b92449a112586c904,0xc7a400400720fb156242,0x382081d629c268bb1286,0xdc0eb15625c268b240,0x86fc240eb14a2ec482d2,0x9038c5189d160b0803a,0xef13e2245847200f920f,0x48b713838703c077c520,0x45b8908e181b058e2ac2,0x6c4958471522dc4e0e2a,0x7839c489e18171a113d0,0x31462545e0e220db8a91,0x84d1783873422490dc0f,0x5d10524481f058628c4d,0xc706c86e07c0e714e254,0x480f01de2bc4f8851611,0xe07c0e524e2b45b89a20,0x3dc540e713a2c743e86,0x13e210768b0803836437,0x4f10a2f072921c07f8af,0xd84d17838160ae240dd8,0xc3d89709a2f0702c15c4],#[0x282001b70962ac4e8bc1,0x7dcf3849152260738b,0x9152240fc0e261041f04,0x89058402184011107f8b,0x7110800ff8481d229c5c,0x9e12487e07a8a51262f0,0xf092b08a2944d8bc1c51,0xa44a0e142402e14287cc,0xe2f070c0820f845f1722,0x1ce2c508d6100fc8a912,0x9717441491307e45489c,0xe891c1b21f81f0394528,0x238c0d90fc0fd15039c5,0x38220c03c0728a090a24,0x7839490e03fc5e8ad128,0xc1c0b0503f6114528971,0x8ad1383ac58fa26c238b,0x4689d160a0608807dc26,0xb80689517a207e05c034,0xe27c468b08e368cb09c0,0x11a138168bb12378a21d,0x4e01a12c468bb123824b,0xd88d09c0b45d8a181302,0x12f00d0962345d8a1c12,0x7b4218a31322d871609c,0xf624824047c0f0920872,0x2b42702e0124ac548b08,0x9c0b8058ad0922c23d89,0xf13e2245847202182d05,0x8b713438a03a06c4d78a,0x13d0760d892543a11c54,0x1be05c01c548b7122789],#[0x438a916e2423860f60ec,0x8f89253da10c5189d17,0xc0023d8ad17624714248,0x962ac4e8b0862e84e05,0x708162b4268bb12c386d,0x842081c034258ad17624,0x8678af13e204f68b07a3,0x17c5789f102794583618,0x8b08e2f8af13e2345847,0x5b8a71211c4f15e27c42,0x42240ff17a28876892b4,0x224c5b0e2d1041f42011,0x48e91b12411e50e84915,0xa1381700915226c59008,0x122a44e84b164836925,0x9d140f4505a0b023f02e,0x684d12c3ac58da12c5e8,0x8028a51362c509211345,0x2b44d8b1c1ea2043fc0b,0x5224218e11422700d09a,0x717438604007c50f8b91,0x8ad1210c553da1245489,0x2048514a242389e2c50e,0x15a25c58de2f4568908a,0x8514a242389a1381700d,0xcf1611ec458906e484,0xc1848b1211c409083d07,0xb1611c5b1362ec503611,0x36712e2ac58fe2bc4f88,0x3d8ab121148d09c0b800,0x9c5d891c2420f41de2c2,0xa2a870fa138170006d62],#[0x1211c407b249c2689917,0x491522745d0e1d4548b5,0x48a912a2c218a10e4938,0x81700d14e1345e891849,0xb416784d15a254584323,0xa0b14568b51211c60980,0x13562023d89d160f8805,0x8808f62545833210da0e,0x3d8a5160d0843a86c4d5,0x345847150ea1b01b6202,0xe27c428b08e2f8af13e2,0x5c01c4d84d16e287f15,0xbb1411ec4a8b086383de,0xf02e0162b45d89190ea1,0x7043f17a2b448451c1e,0x810f848514a24238e87d,0x5c0345584717a2470868,0x43f62d4528908e3843e0,0xe05a2b44d8b1821a20,0x391dd11a268583b2021f,0x344e88e1609860380682,0x62b05989b09a08a709c0,0x1611c734204b0e82ce00,0x9836481e319e2bc4f88c,0x5a8750968271582ec238,0x160a87705c1b71324050,0x2d4802c15c5389c17240,0x5a0b05d8961e3d8ab138,0xb08c2d4491b200de1db1,0x89b080b0604084b4128a,0x5e89b080b06d05c2d452,0x944d84616280807ba2b8],#[0xc2ec202d180da12e00a2,0x8a27858a02745700d12,0x405a302c43e84b8028ab,0xa900582843d15c2f44d8,0x85a8a51211c4915c2e44,0xd12311bd15a258584317,0xa005828a0e01a2823f0b,0x570bd120b49e16a29448,0x7858e13021e82e01e134,0xb45f0810c8de82d15a2,0x16624238ba2b44b0b236,0x8e1662416047108918aa,0x1b625a09c530b71343c,0xe370b715a09c48401420,0x862b84d11c034570b04,0x89b040b05d14c2f4482c,0x2689e17a281e8ba2b85e,0x810a20f1782b0484419c,0xc151060ac1307dc5c901,0xd8b61e3e0a7178264802,0xc5843140fc9dd0582b04,0x2984b8ba1e4112a15424,0x4e2c220a1100fb12d04c,0xe15c27458431785709d0,0x24d01c22c1709e163384,0x400ec35a2f8499043640,0x70a708d17c24238a0f78,0x6f84582917c2507c1a2,0x2122f8489d834484083a,0xb437050808427a0df083,0x61a242020fe11c26c168,0x7a06f8420fd17c2607],#[0x384e1386b45f0807a384,0x6609c11a090a58b2407,0x2e48314078302f051611,0x162f804900624783e136,0x61962e48100558630961,0x149203830145c0384f08,0x5b141c178a2e13c22c5b,0x630f2401f83ce11c26c,0xc00a629c3180709b17c2,0x819031920c258430cb17,0xc278470061962ca18c11,0x16c50918d28e51314921,0x31a51ca261924384f08b,0x35e0f84d84916c501e10,0x3e11c26c268b2283c9e0,0x708e13a2d8a03c1c1d83,0x84384517c00189327a48,0x208a68b2551813a19426,0x2510c04504e0ad097094,0x1948509a11a2f8050c06,0x3c2245b0c09040c65461,0x916c50240e0cc180a2e1,0xe11a2c704c28b84f08,0x268b060302f04dc26c27,0x745f0818c3833e13c22c,0x24345b0c298a70c601c2,0x4634a3144c5384f08e01,0x28986709e1124345b142,0x13c2345b8409e38c6946,0x8709c2745ca22419830e,0x99ac1e482f04d4308a70,0x807c4548eb8881d62dc4],#[0x11781ce208eb8ab1783c,0x738a71362f0792d2015,0x2ac4b8bc1e4b48240476,0x6e24cd60f249011d81d6,0xc1e483e8360f607388b1,0x60aa0703d052e21c558b,0x580b5c558b71211c809,0x2cb15625c5e0f2826684,0x5843182670205a11c218,0xc4d0471c0758ab1383dc,0x624238c0700a588b12a2,0x1383a4d100720a588d17,0xe076381b08162107e8bb,0x847200a58870962745e0,0x943724a9020fb15a2ec4,0x845b14442c4c0ed16480,0xc55885160a4238b24b0d,0x1e0b011b1162b458471a,0x410107d88b15a2f07029,0x836e21c4c8b13c26b071,0x8a91627b07121044e198,0x604714cc82b836245c43,0x645e0e15c438a71322c1,0xa2cd0942784941b714e2,0xc2292022086ec558941d,0x86ec5589517838571386,0x1703f0702c204f09281e,0xbc1c684934207cc5189d,0x141102684705962ac4e8,0x105d612c5589d1783816,0x589d17838d08c134201a,0xc5589d17838d08c86ec5],#[0xdd4d388d16e24238c86e,0xc1281cb88d16e28238c0,0x38a87c0938ad16e24238,0xdc48472022b8ad16e242,0x11c603ca4a8101b714a2,0x1c0b09a04e29c4e8b058,0x1342382eb14e1345d89c,0x3b87c8868ab17a24238e,0xbd15a24c5c0fc1c0b082,0xa8a51362f070ae24cf01,0x44e0e33c40a112503d0f,0x38161410026e8a05962f,0x2202e08f61345689b178,0x2b44d8b43f838cf0c134,0x87f4558bd1267b070da,0x3ee2e45489b09838161,0x1f915225c5e0e15c4421,0x5e8ad134414912284494,0xf448471207c0e08e87dc,0xa274538b5240d87d14e2,0x14a240fb8bc1c480f01d,0xbc1c0b07042a482240f5,0x38b088304481fa2b44b8,0x46289d16400fd15a2707,0x2745914401b50fa1ca21,0x6451053943e8728cd11a,0x4287a8c53943b44689d1,0x743e87288518a2745934,0xd10a2f44936149b51052,0xfa1ca3344689d164a93,0x5b89535438926d44149d,0xe87161060d84071103f4],#[0x8c0f0800ac4f388715a2,0xa8728b71211c8836a654,0xa2c57047180f01b524e2,0x12a2c4d0471e8138a713,0x8d17624238a2700c588b,0x819b15621458471a4d58,0x4cc91b15a2ec40471848,0x8e3c92b1522ec484716,0x472419e84710e264589a,0x680a814e84714e22458,0x92042e2a45b8908e304b,0x682cd08e2a45b8908e48,0xa87589517a10a09810c1,0xa7890980b41604708762,0x8f8a112462b45989a1c,0x43823d8ad09627459248,0x15a2ec48471c26520a3f,0xbb156254f0e13826843b,0x68bb12a786a4147e8768,0xc568bb1211c6e05c02c5,0x2ac4e8b61c2b8894324a,0x5a2ec4b0e28268470596,0x142704d94324b42047b1,0x8b08e2388713a2d4d047,0x4b8ad16e242388e21c56,0xd4940f514a25c5d0e142,0xa2b44b8ba1c2b8808807,0x13439c58441a0fc0f089,0xa912c3850c922407e8ad,0xd0e54248450880dac5c8,0x923a46c49047d15a24c5,0xe8405a0b14558b51211c],#[0x50e8ab17a24238c13150,0x23e8ad1362d5092131,0x362d50847142704de05c,0x54362f4568908e2e8ad1,0x9293ca2944d8b61c2849,0x5e8ad12c3a49128810f8,0x5c5e84282284408e286c,0x60470860b41650e91522,0x88748a913a11c58431c2,0xe1781700d15a245094a7,0x1ce2e508ca1022844f0f,0x8514a24238c11f45689a,0x47d15a25c58e1142204,0x8068ad12e2c7d09c0b80,0x22c499a0923047d09c0b,0x5621c5d8908e2836f0f6,0x39621c5d8906c668633,0x3506666ac438bb1211c8,0x3049b10e2ec4848141b8,0x923813019622c4b8b092,0x7141b835067622c4b8b0,0xd8b08e2d8ab1262cc904,0xc558bb1211c5324628c4,0xb16538ab16e24238864a,0xa0cf0860fc1c631c4389,0xc1c635c438ab16503706,0x8b06c28390700d30860f,0x4b8ab160d87324e25c55,0x6c5b8806c204508810dc,0x611c6b8ab16e201b0ae2,0xd8a08b624871362dc503,0xc48471d07a0e06de1fc2],#[0x24238a11422043b14e2e,0x6e134503d25c268a917a,0xd16501d0362488768991,0xf2481b043a1d22a44b84,0x915225c268b0864c2083,0x8bd12e10a04007c4910e,0x85b0b026702e0011f456,0x2d059a2b45e897081309,0x4589d17268238a10c1e8,0x1c2589d176224d03d1ec,0x631c2588d17624239206,0x11a2ec50471c1f03b066,0x4b15a2c258e12e15429b,0x68b70812c8032036c438,0xc684b241a02a053622c5,0x83d0540a7c2588b14a2c,0x2622d458e2b45b8908e3,0x6f0718d711a2dc55842c,0x7610260e0d015029c3b8,0xb08130907a085c5389d1,0xa10c1e82d058e29c4e8b,0x503d1ac2389d16e201e8,0xdc503d15c6d84711a2dc,0x62745b840984584713a2,0x12a2c261010c1682cb15,0x9b08403d05a0b3c258ab,0x9687c21a0ef0fe174568,0x7087c0b8068ad13611c5,0x68971610c60988b51604,0x45584d12e2c808f61345,0x29448471f1061f08f83b,0x761021908810f843090a],#[0x86422d45811f4568971,0xa11d16a2cb09a2b44b8b,0x204c22c268ad12e2c218,0xc707a0b41668ad1362dc,0x304305a0b2c5a8a51211,0x862847709a2b44d8b086,0x9b05068ad14e1344d8b0,0x3d8502001bd10e1285e8,0xc035a2344d0b3200ec82,0x384a17a248ec1a268e81,0x859900763c1c06bc0344,0x2f0d03d1e8ed0ed11a27,0x60f01d90061c2689d11c,0x52404106ba21c2689e1,0x879c2040b1562305e82,0x82306ec5384c176210e9,0x8431582cc482c08e4029,0x3e0bb138381710684095,0xb05d8908e404d0596282,0x624238a1342202e05962,0x1382cd084718d0d8ac17,0xa71382c160471b0058ab,0xb8ad0582dc4d0f2a4138,0xec1b210ea1283c8b60d,0xb0a05a849c5584c16e25,0x2202eb14e1305d89d040,0x2a44f00b080b4909a11c,0x361016972858d8126172,0xe5082c08fc0385c8a91,0xb22b85c899200b080981,0x9136105031b1e5084c05,0xb9132418d8f28785c8a],#[0x530b51211c9142282457,0x4239047b072a02368494,0x50a09218394502ce16a2,0x81622dd15a0b85e89a1e,0xa2785aa008e284c07b47,0x5a2985d84d1246c9d15,0x4d15a24160c8750902dd,0x289c1cc2c50140f785d8,0x16942850931b08b24145,0x60e2361174530bd1343c,0x45700513c2e481528648,0x26481687d090a1458281,0x21ca105a8b38068ae17a,0x2f45490d12c6c709811c,0x8a27858a06364ca1141c,0x6360b4705887d0928ab0,0x820584843b09a2b44f0b,0x9a0b823c8a709c2e44e,0x3d059c2f456897081307,0x182d059c2d4528908e38,0xc16e8ad13c2dc204c1c2,0xb3c268ad12c2c261010,0x17a2b44ca008e283d05a,0x6141a29c270bd1346c6e,0x1c743683ac470bb1211c,0xa521de0086ec430bb121,0x344ca82b14e1385d8807,0x762185d8a08e3d16a236,0x714c2dc48471d0ef0043,0xbb08e281e8ec4a42682,0x270b7120f4903ac49c4b,0x260ec7d890a1904e2ac],#[0x11c70860b5c5389e1761,0x343a1de0086ec530bb12,0x181dc1b711c2dc4e826,0x8401814b88d05c2dc504,0xc25822c1638ad05c2dc4,0x22e85a11c1668ae17a25,0x4570bd12e10261013426,0x2985e89098384307a0b7,0x6a242384c1c16f84059a,0xa1fa0816120b41628ae1,0x202210e20088e2f05609,0x81086c260ac12e2e0fa,0xfc4182b04e827161107,0x960ac13611c5a2083e41,0xd8560e612e2e87940b50,0xe2c21904851031208810,0x86452113ca0a87f0ae12,0x87fc3f8541d613857090,0x4087c2430a61211c218e,0x624c2984d8471610c74,0x482e15c25c5d84086482,0x84d8471610c7636c484f,0x298484308e384745bc2b,0x5c26c5843191021fb16c,0xe13a09c58441823a90e1,0xa709c2745843181670a,0x70234303c2682c1c227,0x38119e81e134160e1102,0x71c22047058134408810,0x613826d0eb0da102604,0x2240f058134621d6194f,0x328768454211c708fc08],#[0xc135c2e8408e284e09a1,0x3047324168408ee14309,0x8e284508810dc2d8608e,0xc09811c50990b6161a10,0x84c70b610238810d16a2,0x96142604716c204770a1,0xb08134170470583c2d85,0x90e000b02602d1e0960e,0x960ea1ea80238e10e094,0xa4860e09811c623c46d0,0x2428784e54011c605984,0x31b1c2384505a0b8409b,0x260c2850fa12c1c28248,0x80238810f0960e05b43c,0x1b1250ca0920184c9432,0x742c09811c4121a1ac23,0x8e640609a13216847102,0x245b43c609a13216c2c0,0x2e05813448428820fa1,0x21e8245a0b02384c1822,0x863a1fe0c11021a0e14,0x2c182203644087cc2c90,0x3c901422620d0410c23a,0xc1b60e70a2a2dc3e1302,0x87f80044d0410c6c4187,0x440]]
set_option maxRecDepth 16000 in
def g255H10 := limbs80 #[#[0x10440110100600100020,0x41000440510000c00010,0x40404000081005102604,0x10040141070500000000,0x64340000003040010400,0x13090004000404520000,0x4c000410401015002040,0x210040,0x0,0x0,0x0,0x0,0x1c424b21d00000000000,0x0,0x100a0000000,0x0,0x0,0x2881600000,0x0,0x2d0060,0x0,0x0,0x3d1780000,0x0,0x821c0000b04540000,0x41660000000000000000,0x0,0x0,0x0,0x1406f00000000,0x347300000000000,0x0],#[0x5035a001a00,0x0,0x4428400000000000,0x0,0x20064000,0x0,0x0,0x203ee8212000000,0x0,0x0,0x3e149915e80000,0x0,0x1c000000000000000000,0x13540000000000000811,0x150e10,0x0,0x0,0xd23cc00000000,0x3893300000000000,0xbf000000000000000000,0xc419000000000149,0x0,0x0,0x280580,0x8121c403f00000000,0x38c09000000,0x0,0x0,0x0,0x0,0xd0138,0x11467000000000000],#[0x0,0x0,0x0,0x0,0x0,0x390d6000000000,0x0,0x3546e00000,0x0,0x0,0xb4390000,0x400000000011d4000000,0x640000000000000060a,0x40,0x0,0x40ec005a400000000000,0x1c0e600000000000002,0x0,0x0,0x148247440000e03e0000,0x38,0x480c400000000,0x184c5b5388000000,0x0,0x0,0x0,0x0,0x10a00,0xf84b0000,0x0,0x0,0x0],#[0x1146b,0x0,0x3682200000000000000,0x0,0x0,0x0,0x147000000,0x0,0xc1198000000,0x0,0x107c0000000000000000,0x1802a00003,0x0,0x0,0x7250c000,0x0,0x0,0x0,0x6f000000000d04480000,0x381,0x0,0x0,0x0,0xe0038000,0x427300000000000,0x0,0xb46ac000000,0x0,0x0,0x0,0x7e801bd000000000000,0x5],#[0x0,0x0,0x36cc9920000000000000,0xf1,0x0,0x81c40000044f50000000,0x3,0x88e0000000000000,0xe0000000000000000000,0x2512300000d45,0x0,0x0,0x1a08f00000000000,0x0,0x0,0x110,0x0,0x0,0x0,0x14588000000000000000,0x0,0x0,0x19081000000000,0x0,0x31180b12a4000000000,0x0,0x0,0x0,0x427480000000000,0x0,0x41634000000000000000,0x0],#[0x0,0x0,0x0,0x0,0xa000000000000000000,0x24,0x48050000000000000,0x1d06b00,0x0,0x0,0x1d0cd00000,0x0,0x0,0xd409f21ab00000000,0x0,0x94680000010190000,0x0,0x0,0xc58f0000000,0x0,0x0,0x0,0x0,0x0,0x0,0x6449c000000000000000,0x1d1e9000000000,0x0,0x0,0x0,0x0,0x51058000],#[0x2500b000000,0x0,0x0,0x3003dc42ac0000,0x0,0x2c03000002411a00000,0x0,0x0,0x0,0x201106d80000a41700,0x3c9450000000000000,0x0,0x0,0x9210000,0x0,0x388e1812a80000000,0x0,0x0,0x0,0x0,0x0,0x80000000000000000000,0x701ac50,0x0,0x0,0x0,0x0,0x0,0x4800008086c00000000,0x41,0x0,0x0],#[0x0,0x0,0xf407000000000000000,0x0,0xf02a00,0x0,0x0,0x0,0x0,0x0,0x0,0xd00000000000003807f0,0x2c07,0x0,0x0,0x0,0x0,0x0,0x291ca00000,0xc045000000000000,0x452400000000000000,0x2c20290444000,0x8300000000000,0x0,0xb4738000000000000000,0x9127c0000,0x0,0x0,0x0,0x0,0x0,0x0],#[0x291b70000000000000,0x1499700000000000,0x0,0x0,0x1905b00000,0x0,0x0,0x30278000,0x0,0x0,0x0,0x205400000000000000,0x0,0x74000000000000000000,0x4015751,0xb406c00000000000000,0x0,0x0,0x201a9b174,0x80f300,0x0,0xf106800,0x3c5f200000000000000,0x0,0x0,0x0,0x40000000000000000000,0x28c00000000000004404,0xb4,0xe07ac0000000000000,0x0,0x0],#[0x0,0x506c000000000000000,0x14400000000000000000,0x32,0x0,0xa06a8000000000000000,0x0,0xb806400,0x3c00000000000004500c,0x4a3,0xc134941850000000000,0x11c00000000000000000,0xf44180000000030,0x0,0x0,0x0,0x140c20000000,0x0,0xe02ac0000000,0x0,0x0,0x0,0x0,0xf006c000000,0x9b000000000000000000,0xc0,0x0,0x0,0x0,0x0,0x0,0x0],#[0x72860000000000000000,0x19000000000000000000,0x340bde01fac4,0x0,0x411d1c0a2000,0x1417af062800000,0x1d00000000000000000,0x8,0x0,0xe423c000000000000000,0x31000000000000000000,0x957a0000000000000141,0xd4184000000001,0x816d000000000000,0x907c400000000000000,0x51600000000000000000,0xc43200000000035,0x281bc0000000000000,0x90f100000000000,0x0,0x181000000000,0x0,0x0,0x4122c000000000447b0,0x60408000000000000,0x0,0x0,0x0,0x1082c,0x0,0x3006800000,0x0],#[0x0,0x0,0x0,0x0,0x546b8000000,0xa5000000000000000000,0x381,0x0,0x0,0x0,0xf900000000000000000,0x462f9c,0x304350000000000000,0x420b4000000000000000,0x0,0x3411f0000000,0x0,0x111e5000,0x0,0x0,0x0,0x0,0x90,0x0,0xe081800,0x743e4000000000,0x0,0xeb073c00000000000000,0x1040,0xb10080000000000,0x0,0x140a700],#[0x34c11,0x301d70000000,0x0,0x0,0x9037c00000,0x0,0x161c3000000,0x0,0x103f0000000,0x40770000000000c9d3,0x4022c00009519800,0x944e0000000000,0x0,0x0,0xc23d4000000000000,0x80000000000000000000,0x9024,0x0,0x14ba144bc0000,0x0,0x26f0000000000,0x0,0x8273800000,0x0,0x0,0x0,0x3d4e500,0x144c700003c09c,0x0,0x20048,0x28022000,0xe833400000],#[0x0,0x80000000000000000000,0x3700000000000000605d,0xe0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x84600000,0x40514000000,0xbd000000000000000000,0x10,0x706740000b6100,0x0,0x40000000000000000000,0x1c18b00002c0a,0xc101c0000000000,0x0,0xd2868909200000000000,0xa06d00000000000000,0x0,0x1419600000e0ab00000,0x281a7000,0xd02c000008536909250,0x0,0x0,0x0,0x0,0x0],#[0x0,0x0,0x8440000000000000000,0x9000000000a102800004,0x14b,0x0,0x0,0x1c16000,0xf049984c3000000000,0xc1590000000,0xc04c0000000000,0x184c4000,0x0,0x0,0x402e000000000000000,0x0,0x0,0xe421c0000,0x490000350915082c00,0x2,0x15a8000,0x0,0x140a100000000,0x143240,0x0,0x85500,0x0,0x0,0x0,0x311d5000,0xd850000000,0x0],#[0x89416000000000000000,0xc42d,0x0,0x81f9000000000,0x40e87082800000000000,0x5b406600000000000001,0xb27,0xe0000000000000000000,0x91558000034182012,0x0,0x0,0x0,0x0,0x341510000000,0x40224000000000,0x0,0x6031400000,0x55364000,0x40000000000000000000,0x1b800000000150ca0013,0x407e2902d00000000034,0x0,0x0,0x0,0x0,0x3c1c30,0x0,0x2c415000000000000000,0x0,0x0,0x12000000000000000000,0xc12d0000000000000054],#[0x3,0x10088000,0x0,0x0,0x0,0x400000000000000000,0x1,0x0,0x0,0x0,0x7461c0000000,0xd12a000000,0x7f00000000000000000,0x3007e107d00002d,0x0,0x194ee00,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x94a00000000000000000,0x1,0x0,0x3405f0,0xd0608000000000000,0x0],#[0xf51b400000000,0x0,0x3f000000000000000000,0xc0860c9,0xb02b4,0x10dc0000000000000000,0x314b86,0x3000000000000000000,0x1d,0x300da0000000000000,0x0,0x0,0x905dc00,0x0,0x0,0x0,0x0,0x0,0xd10ef500400000000,0x0,0x0,0xe47a000,0x0,0x1502c000000000000,0x0,0x0,0x24053000000,0x0,0x0,0x782640000,0x0,0x2a0f900000000000000],#[0x4400000000000000000,0xe05300000d,0x0,0x40000000000000000000,0xa63,0x38320000000000000000,0x0,0x0,0x0,0x1042c000000000000,0x0,0x281f500000000,0x700e40,0x0,0x191f100000000000,0x1003b,0x221200000000,0xd8000000000000000000,0x414,0x0,0xb700000000000000000,0xc0000000000000700449,0xd011,0x0,0xe9000000000000000000,0x49e5d4228000000003c0,0xc18000000,0x106800000000,0xc0000000000000000000,0x6402000000000040b,0x0,0x0],#[0x0,0x0,0x0,0xaad07ea0484000000000,0x207,0x4000000000912f400000,0x12b000000000842f0547,0x8,0x0,0x0,0x0,0x0,0x140eb70390000000000,0x0,0x0,0x0,0x0,0x78c00000000000000000,0x0,0x0,0x0,0x0,0x0,0x0,0x56b403c000000000000,0x38,0x2046a0000,0x0,0x0,0x6037400,0x0,0x0],#[0x0,0x0,0x0,0x0,0x81e200000000000,0x615500000,0x0,0x0,0x404280000000,0x340a90000000000,0x0,0x80000000000000000000,0x152d,0x0,0xb16040000000000000,0x0,0x50105a00000000000000,0x84fc0000000000000550,0x29462000000000e,0x21c00000000000000000,0x18,0x3813c0000,0x0,0x0,0xd1b0050ac00000000000,0x90538,0x0,0xa9049400000000000000,0x66fc16,0x150380000000000,0x0,0x0],#[0x290fa000000000,0x0,0x0,0x11e000,0xa84f514e94545400000,0x3038c000000000000,0x0,0x0,0x0,0x16000029593000000000,0x381,0x811c8,0x0,0x2113c0000000000,0xa15d0000,0x747080,0x0,0x0,0x0,0xe438800,0x4c000000000000000000,0x300,0x80000000000000000000,0x191d,0x0,0x0,0x0,0x0,0x0,0x0,0x3010c0000000,0x0],#[0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x7580000000,0x0,0x0,0x2408f003d2c1ab000000,0xd108,0x220c900,0x0,0x0,0x0,0xb87c00000000,0xb875400000000101990,0x0,0xc0000000000000000000,0xe105,0x9b200,0x453900000,0x0,0x0,0x7240000b21bc0000000,0x3c9b00000000000,0x0,0x0,0x0,0x0,0x38923000000000],#[0x0,0x0,0x3c194000000000000,0xb06cec08e0000000000,0x1d40ae003c000,0x0,0x0,0x0,0xd429c00000000320ca,0x353b000000000000,0x0,0x141b5000,0x353100000f05cc00000,0x0,0x121dc0000207cc0,0x341cf84c80000,0x0,0x323300000000000000,0xb418941620000000,0x0,0x13c80000000000000000,0x6,0x15500000000000000000,0x249c30000260f7000024,0x0,0xf079a61d400,0xc4cb,0x5111000,0x902cc,0x0,0x381fc0000000000,0x0],#[0x80000000000000000000,0x17d30922d054,0x0,0x7031c802b0000101c1,0x804fc00000000000,0x3c0cc00000,0x0,0xf0000000000000000000,0x1c15,0x1c0d2c04a40,0xe184400000000,0x0,0x0,0xf473c00000000000,0x0,0x281dd000,0x0,0x0,0x0,0x0,0xf43e0000000,0x0,0x0,0x58410,0x0,0x0,0x0,0x0,0x502180000c519,0x85054000000,0x4403,0x21c60000000000000000],#[0x350f000000000000003,0x0,0x0,0x0,0x0,0x0,0x0,0x1007b,0x3011800,0xc8000000000000000000,0xf00,0xb036000000,0x0,0xa535c0,0x0,0x240f500000000000,0x0,0x0,0x200cd00000,0x516300000000,0x0,0x0,0x0,0x300270000,0x0,0x0,0x0,0xda0dc,0x0,0x80000000000000000000,0x3c9c,0x0],#[0x1406a0000000000000,0x0,0xc0de,0x0,0x0,0x0,0x0,0x0,0x801b00,0x0,0xa1318000000,0x0,0x2857c343c800,0xf4710000000000,0x0,0xf00003e0db0000000000,0x291e,0x0,0x1017400000000,0x1113770464000000,0x0,0x0,0xd5024000000000,0x0,0x0,0x94068959400000000,0x190b3000000,0x198cf0000000000000,0x0,0x0,0x0,0x0],#[0x132000000000000,0xd006000000000000000,0x884305d4000000000000,0x1c,0x0,0xe0394000000000000000,0x0,0xc01cc00000000000,0x3c000000000000000000,0x200d4e01,0x56000000,0x0,0x300300000000000,0x0,0x0,0x0,0x0,0x0,0x5191000,0x0,0x0,0x0,0x0,0x0,0x30096e061c0000,0x0,0x0,0x0,0x0,0x0,0x181cd000000000000000,0xa03b800000000],#[0x0,0x0,0x0,0x0,0x1480000000000000000,0x721380000000000000e,0xa4468000000000000,0x80000000000000000000,0x85,0x2d47000000000000,0xb01c00000,0x705ac00,0x351f000001842300000,0x910000091d2000,0x0,0x0,0x280f1000000000000000,0x7102000000000,0x0,0x0,0x9518000,0x10100,0x0,0x0,0x0,0x0,0x0,0x551a8000000000000000,0x0,0x0,0xa07d0000000000,0x0],#[0xe1ca0,0x5079c000,0x0,0x2414b0000000000000,0x0,0x3810b,0x0,0x0,0x0,0x0,0x20f000000000e06e4000,0xc0000000000000141bd4,0x7200000000000000fa10,0x3805e000000000a8,0x0,0x0,0x85640000071298,0xc189000000000000,0x0,0x5072c000000000000,0x0,0x0,0x2c14a00,0x71000000000d461141b2,0x181,0x0,0x0,0x0,0x0,0x6e80000000000,0x0,0x123c000000000000000],#[0x0,0x209e70000000,0x506e0,0x25018000000000000,0x0,0x0,0x0,0x0,0x0,0x3d0ce000000000,0x8104400,0xb12b00000f035c,0x51c80000000000000000,0x14ef5,0x0,0x0,0x180770000,0x0,0x0,0xd0ba0000000000000000,0x0,0x4457000,0x0,0x54294000000000000,0x0,0x86400000000000000000,0xa0,0x0,0x0,0x101918103400001104c,0x0,0x0],#[0xf7c11a4000000000000,0xd077a0,0x488000000002001c0000,0xe1300000010,0x0,0x80cf0000000000000000,0x2,0x0,0xd077c00000,0x0,0xc0000000000000000000,0x1476,0xa5084000000,0x0,0x0,0x2013300000000000000,0x4071000,0x0,0x41000000000000000000,0x19,0x0,0xf0090000000000000000,0x0,0x0,0x0,0x0,0x0,0x0,0xf03f80000000000,0x1c802c01e000000000,0xb0450000000000000000,0x0],#[0x0,0x0,0x2413a000000000000,0x9528c00000,0x0,0x342e40000000000,0x0,0x10170000000,0xb07180000000000000,0x0,0x0,0x0,0x2017c0,0x2400000000000000000,0x9,0x0,0x0,0x0,0x2c16ee86b800,0x0,0x0,0x90000000000000000000,0x1c13,0xc0000000000000000000,0xa80c,0x0,0x904a00000,0x41e40000000000000000,0xa8000000000000000002,0xe04,0x30000000000000000000,0x40720000000002d01],#[0x0,0x922f400000000,0xa0824000000000000000,0x0,0x0,0x1af00000000000000,0x0,0x0,0x92300000000000000000,0x107b80000000011,0x0,0x40024000000,0x3481c0000,0x0,0x0,0x0,0x0,0x15e4000000000000,0x0,0x0,0x20433546100,0x0,0x0,0x0,0x91d000,0x24207284e000000,0x0,0x0,0x240cb0000,0x0,0x4140000000009086,0x0],#[0x0,0x6b40000706400000000,0xf,0x0,0x0,0x8153721d400000000,0x70294000000000000000,0x404340000000000000,0x3004000,0x71168,0x0,0x0,0x0,0x0,0x0,0xc00b4000000000000000,0x0,0x21cc0000000000000000,0x0,0x0,0x0,0x0,0x80000000000000000000,0xb005,0x0,0x4142,0x0,0x0,0x0,0x0,0x0,0x203240],#[0x68c0000f129c00000000,0x5,0x0,0xc1fe0000000000000000,0x2,0x1300000000000000000,0xf07d800000000000002,0x0,0x80000000000000961380,0x1565,0x1004100000000000,0xea7036c0000000000000,0x9517c000063181d4,0x4dd57c00000000000000,0xd20,0x0,0x0,0xd200c0000000000,0x0,0x0,0x0,0x2c18c0000000,0x998d00000000000000,0x0,0x0,0x0,0x80000000000000000000,0x6032,0x0,0x0,0x8249c00,0x300000415ac000000000],#[0xb12,0x0,0xf42e0000000000000,0x902080,0x0,0xd8090000000000000000,0xd1000000000000000000,0x3e1,0x0,0x0,0x0,0x0,0x0,0x0,0x10164000000000000000,0x0,0x81be0000000000000000,0x436e,0x3802f000,0x0,0x0,0x0,0x0,0x499600000000000,0x600100000,0x0,0x1c000000001417f70654,0xa16,0xf0000000000000000000,0x510e744b,0x0,0x0],#[0x0,0x3c1f0000000000,0x250d80000000,0x0,0x0,0x0,0xe0304000,0x0,0x0,0x0,0x555e2c4d1,0x1560000000000000000,0x3,0x0,0x806d0000000000,0xb500000000000000000,0x349be000000000000038,0x13800000000000000000,0x3a,0x0,0x0,0x2101500000000000000,0x910c40000000,0x0,0x0,0x0,0x0,0xa085c000000000000000,0x0,0x0,0xf40000683380000c4340,0x423],#[0xa07b400000,0x3404b00000000,0x141e10000081a4c02ec0,0x0,0x281cc60364000000,0x0,0xb075400,0x180f000000,0x0,0x0,0x0,0xd0bb000000,0x0,0x30380000000,0x0,0x0,0x0,0x5358000000001c1ec000,0x3509c984f000004,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x2803e00000000,0x408000,0x81ef0000000000000,0x3000200000000000],#[0xc84380000000000069,0x81fde02bf41610000000,0x3,0x10180000000000000000,0x148d8c,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xe1270,0x0,0xd00980000000000,0x282080000381700000,0x0,0x341dc0000,0x810f0000000000000000,0x3,0x0,0x0,0x960000004c100000000,0x9,0xba41d10000000000000,0x203f4000092,0xf040f1014,0xb060c00000000000,0x20500000000000,0x504c0000000000000000,0x1540de],#[0x18d00000000000000000,0x18,0x254690000,0x90418000000,0x0,0x403a800000000000,0x0,0x0,0x0,0x0,0x0,0x4b00000fa32c00000000,0x20,0xd05500000,0x41240000000000000000,0x106800002,0x350da000000000000,0x2c0050,0x1440b00000000,0x0,0x0,0xe0698000000,0x0,0x0,0xb7106c00000000000000,0x5cb09d100002820df53,0x60000000007028c00001,0x2414,0x0,0xb50c,0x0,0x25078],#[0x0,0x0,0x0,0x0,0xa04bc000,0x9580000000,0x0,0x2014d00000000000,0x0,0x190120000000,0x0,0x0,0x221ce0,0x1146300000000,0x28001000000000000000,0x0,0x0,0xa06100000000000000,0x0,0x0,0x4d40000000000000000,0xa050dd0d77,0x141c0000,0x0,0x37c00000000000000000,0xa0f800000000064,0xb5398000000003c13d,0x0,0x0,0x0,0x0,0x0],#[0x0,0x0,0xb05f4000000,0x0,0x0,0x0,0x241f2000000000000,0x0,0x3c14400000000,0x18076000000000000000,0xc419400000000,0x0,0x0,0x0,0x0,0x2600000000000000000,0x3c0c46,0x0,0x0,0xd55e400000000,0x0,0x0,0x0,0x0,0x14048a007814f0000,0x100f1d9b00,0x0,0x0,0x0,0xa501c000000,0x0,0x4127d018c00000000000],#[0xe07a4000000003,0x800180000000,0x6873c00000000000000,0x0,0xc0000684bc0000000000,0x104e,0x57300,0x4067c0000,0x0,0x0,0x0,0x0,0x2d4e300000000,0x0,0x0,0x3412000000000000,0x0,0x0,0x1c21a00000,0x0,0x341d00,0x61570000,0x0,0x0,0x41da00000000000,0x843f80000,0x0,0xc58b00000000000000,0x0,0x0,0x6063c000000000000,0x0],#[0x0,0xc5360000000000000000,0x0,0x702f800,0x0,0x0,0x0,0xc11cc000,0xc024100ba000000,0x0,0x0,0x0,0x503b400000000000,0x0,0x0,0x0,0x50780000000000000,0x0,0x300500000,0x615b0000000,0xfb000000000000000000,0x141,0xc0000a0154000000000,0xb02,0x0,0x1417b00000000,0xc1bb000000,0x2b400000000000000000,0x40197114598,0x34164,0x81ce0000102150000000,0x0],#[0x1420500001080f000,0x905f0000000000,0x0,0x0,0x20800000000000000000,0x64,0x0,0x0,0x0,0xc23d058a7000,0x0,0x3611a00000000,0x28104000000,0x0,0x0,0x0,0x82140000000000000000,0x1,0x83400000000000000000,0x91973,0x55e00000000000000000,0x20,0x0,0x902d8000000,0x15190000000000,0x0,0x0,0xc0ef000000000000,0x0,0x0,0x0,0x0],#[0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x140420000000000000,0x0,0x0,0x2c9730000000,0x0,0x0,0x0,0x383e8000000000000,0x302500000000000,0x0,0x0,0x0,0x7a63000,0x0,0x0,0x5059a11c400000,0x18e00000000000000000,0x596280000000021,0x84000000,0x0,0xbb000000000000000000,0xc0ff0000000000000249,0x2,0xc025c0000000],#[0x0,0x0,0x0,0x0,0x812ec00009041d845e00,0x0,0x0,0x0,0x1d1c3000000000000,0x0,0x0,0x0,0x7237000000000,0x0,0x0,0x0,0x0,0x0,0x15516000000000000000,0x141b,0x0,0x0,0x80684000000000000000,0x0,0x2900a0000000,0x74000000000000000000,0x811,0x88711805a0000000000,0x0,0x0,0x923bc00000000,0xd116660f100],#[0x0,0x400ae21b800000000000,0xd0000034254000000000,0x433c0000000000000e10,0x328cc0,0x0,0x0,0x0,0x0,0xa2000000000000000000,0x281,0x14000000000000000000,0xb02,0x0,0x1c500000000000000000,0x343be8,0x0,0x345fc000000,0x58000000000000000000,0x952df50,0x0,0x0,0x318b31155c00000,0x605c00340000b0794000,0xc0000e07500000000024,0xd539,0x0,0x7b00003817e000000000,0x508100000144f415,0xc00dc,0x0,0xc4040114d0],#[0xf0668000000000000,0xf23780,0x0,0x221cc000000,0x0,0x0,0x2502900000,0x0,0x0,0x0,0x145100000000000,0x3c0b70000,0x0,0xc7000000000000000000,0x241,0x0,0x0,0x26800000,0xc00b0202200000000,0xc0000000000000000000,0x2502,0x0,0x0,0x0,0x0,0x501e40000000,0x0,0x0,0x0,0x0,0x0,0x8055c80e2000000000],#[0x0,0x0,0x0,0x60000000000000000000,0xd12600000000018a1,0x0,0x0,0x0,0x3e83f,0x0,0x0,0x0,0x0,0x3600000000000000000,0x4000000000000000003c,0x70144dc000000000e042,0x181d330,0xce000000000,0x0,0xa47a8,0x0,0x0,0x24885200d0000,0x0,0x0,0x0,0x0,0x528400000000000,0x0,0x0,0x0,0x0],#[0x550080,0x0,0x0,0x0,0x2117d0000000,0x0,0x516c0000000012106000,0xb,0x0,0x0,0x380620000,0x9024cd07600000000000,0x340f2000000000,0x9f00003d10b0000000,0x2,0x3c1a3000,0x0,0x0,0xc45c000000000000000,0x0,0x0,0x0,0x0,0xc4546f00000000000000,0x41d9000000000942,0x381780,0x0,0x802c40000000000,0xd54880000802d,0x50234000000000000000,0x0,0x0],#[0x0,0x0,0x70000000000000000000,0x1805,0x0,0x0,0x0,0x0,0x80d10000000000000000,0x1,0x0,0xe005c00000,0x2a01a00000000,0x3c0bf000000000000000,0x311040000,0x0,0x5a000000000000000000,0x7059d41,0x24000000000000000000,0xd16,0x0,0x0,0x0,0x7bc00000000000000000,0xe1,0xa26440000000000000,0x0,0x0,0x0,0x15950000000000,0x0,0x0],#[0x0,0x0,0x0,0xc8560000000000000000,0x150a600000,0x0,0x0,0x0,0xc0000000000000000000,0x1c0e1951c,0x0,0x0,0x0,0x0,0x31523000000000000,0x0,0x0,0x0,0x0,0x84034000000000000000,0x18136000000000,0x0,0x58000000000000000000,0x847,0x362866c11d0000000000,0x203ea108,0x0,0xa00000f03d800000000,0x1c47554,0x2840f000000000,0x0,0x80728000000000],#[0x0,0x50000000000000000000,0x2c19ee0526081,0x0,0x0,0x0,0x0,0x0,0x0,0x60900000000000000000,0x8,0x0,0x0,0x63800003a10000000000,0x201b7f8,0x0,0x84ad0000000000000000,0x0,0x0,0x0,0x2c8243125c000,0x0,0x65c00000000000000000,0x1905d00,0xb06600000,0x3014400000000000,0xa0000000000000000000,0x507,0x0,0x0,0xc0000000000000000000,0xb13c],#[0x44030000000000000000,0x0,0x4870800,0x301b8000000000,0x3c438000000000000,0x1013e0000000000,0x0,0x28809000000,0x79800000000341650000,0x1d0000074,0x0,0x0,0x0,0x0,0x380a60,0x0,0xc0000000000000000000,0xc030f14080156,0x91ee00,0x0,0x44fc00,0x3d11000000,0x944194a2000000000000,0x7,0xcf00000000000000000,0x751c5e,0x0,0x0,0x0,0xe015000,0x0,0x9056c0000000],#[0xea10800000,0x0,0x0,0x0,0x2418600000000000,0x0,0x0,0x0,0x0,0x0,0xb2374000,0x0,0x2650b607dc44f60000,0x81030000000,0x0,0x80330000000000000000,0x3,0x3c099000,0x0,0x0,0x0,0x0,0x4290000000000000000,0x0,0x81410000000000000000,0x0,0x0,0x0,0x0,0x0,0x0,0x3118d00],#[0xaaa51640000000004084,0x1c0,0x0,0x0,0x34279800000000000000,0x3c12,0x712680000000000,0x0,0x0,0xd13758870000000000,0xd504400,0x5408c000000000,0x0,0x8421400000000000000,0x0,0x0,0xc058c00000000,0xc1ae00000000000,0x0,0xd5b00000000000000000,0x2,0x0,0x8426400000,0x0,0x237c0,0x12800000000000000000,0x30,0xea000000000000000000,0x122f9c9,0x2d17e00000,0x48ee1632ec210000,0x0],#[0xf42f8000,0x0,0x0,0x0,0xb53ac0000000000000,0x40d0000000000014e400,0x3,0x42500000000000000000,0x7002000000000000001,0x0,0xc8db000000000000000,0x0,0x0,0x701e998db,0x0,0x0,0x0,0x0,0x0,0x0,0x70800000000000000000,0xe0,0x716019c000000002446d,0xc417b10,0x1c13800000000000000,0x53a00000000000000000,0x9f044c0000000000000d,0x907,0x0,0x0,0x2603200000000000,0x806480000000000000],#[0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x290acd134c000000000,0x2086d000,0x0,0x0,0x0,0x0,0x0,0x2d11c000000000,0x90090000000000000000,0x1,0x27080000000000000000,0xe008c00001,0x10254000000000000,0x0,0x0,0x0,0x141ff,0x0,0x390e600000,0x0,0x70000000000000000000,0x3d45],#[0x10035000000,0x0,0x0,0x0,0x0,0x0,0x6137000000000000,0x0,0x2d1ed00000000,0xc0000000000000000000,0x5418,0x0,0x0,0x0,0xe039c,0x0,0xd479c00000000000000,0x0,0x0,0x0,0x145c00000000000,0x0,0x0,0x0,0x3cc6d000000000000,0x0,0x0,0x0,0x0,0x0,0x0,0x7415c00],#[0x0,0x0,0x1c00b0,0x0,0xc84700000000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x300c60000390e30000,0x344d4c0184000000,0x0,0x0,0x0,0x2b000006119c0000000,0x244bc0000000003,0xd300000000000000000,0x14038000000000000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x70274000000000000,0x0],#[0xf874800000000,0x0,0x0,0x0,0x0,0xd14000001855d000,0x0,0x0,0x645ec0000000000,0x0,0xa06fc000000,0x406700000000000000,0xa057000,0x0,0x0,0x0,0x0,0x0,0x0,0x1846b00000000000,0x344b1909d,0x0,0x0,0x0,0x0,0xf27a000000021c000,0x340840000000000,0x2e400000000000000000,0x80420000000000000000,0x75000000000000000000,0x807c0000000000000114,0x7503c000000003],#[0x0,0x0,0x0,0x0,0x0,0xd83f84117a080c000000,0x3146c,0x0,0x0,0x3906d000,0x155970000000000,0x3182c00000000,0x0,0x0,0x0,0x9084c0000,0x0,0x0,0x51680000000000000000,0x5,0x0,0x0,0x2e000000000000000000,0x0,0x37a83c80000000000000,0x30462c1,0x0,0x0,0x0,0x2500002c93c00000000,0x34,0x43800000000000000000],#[0x10,0xe52900000000000000,0x0,0x0,0x0,0x0,0x80621214561264000,0x966300,0x4400000000000000000,0xe2,0x20081000000000,0x40070000000,0x0,0x0,0x0,0xc4720000,0x0,0x184c20000,0x0,0x0,0x3863400,0x0,0x0,0x314650,0x2815df4288000,0x7133c0,0x0,0x0,0x0,0x1156800000000000,0x0,0x41ee909300003c14f000],#[0xc808c0000b,0x0,0x0,0x411a000000000,0xc0084000000,0x0,0x0,0x3803a00000000000000,0x0,0x0,0x0,0x0,0x0,0xe5490000000000000000,0x7000c00002046c0000,0x519f742c800005503000,0x1,0x0,0x8030000000000000000,0x2817490748000,0xc0000000000000000000,0xa454,0x398cc00000000000,0xe44800000000000000,0x0,0x0,0x1a84a000000000000,0x0,0x0,0x0,0x0,0xc0080000000],#[0x0,0x90840000000000000000,0x18100000000000003,0x0,0x0,0x2405be0404000,0x0,0x268380000,0x0,0x302000000000000000,0x0,0x606a240b200000,0x0,0x300290000000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x100c8000000000000,0x0,0x1acf4080000000000000,0x191e0000028168000028,0x2497b00003602c0000,0x0,0x0,0x0,0xf43dc000000000,0x0,0x60ac0],#[0x18e00000000000000000,0xd02ba4,0x56000000000000000000,0x1,0x44be000000000,0x0,0x38000000000055900000,0x48f0308,0x0,0x0,0x0,0x195000000000000000,0x0,0x20193,0x0,0x441e8,0x5e400000000245f3000,0x7,0x340d500000000,0x0,0x0,0x0,0x2b0000000000000288fc,0x310,0x640000000000000b0578,0x943,0x0,0x1076f900700000000,0x0,0x0,0x0,0x0],#[0x0,0x2c13400000000000000,0x0,0x0,0x40760000,0x247180000000000,0x304ab0000000000000,0x50180000000,0x2c072000000000,0x0,0x0,0x20075000,0xe1509c4090,0x2940600000000,0x0,0x0,0x0,0x0,0x0,0x30000000000000000000,0x123b016c000000000902,0xc,0xd00500000913d0000,0x700c40,0x0,0x0,0x0,0x0,0x70228]]
set_option maxRecDepth 16000 in
def g255D11 := limbs80 #[#[0xed2a4a8241fa94250120,0xbca92a0887ba58960483,0xef0890a21bfb8254110f,0xbc12a2886fde1d214437,0xf04b8a217f79254510df,0xcbb04884ffe51824437e,0x2bc12213fd94e09109ff,0x930a884ff65f824427fb,0x5c3a213ff9261d109ffc,0x280907fa549404827fb2,0xa0241bf98550120ff4b1,0xa0907fa589504837f30c,0x8241bf98454120fbcaa2,0x907de59550482ff728a,0x2417fb9654120bfccb2a,0x906fe61160483df2c8b0,0x41ef96558120bfdca2c0,0x6df61554482ff72ab02,0x1afd86591209fecc2a89,0x4ffe55844827fb30b224,0xb7d85595209ffcb30890,0xff661654835fb0cb2a41,0xff96615209ffca30a904,0xfe55864827ff28c32413,0xf84549509fec9702a84f,0xe19525436fb0ca92a1b7,0x8658950f3eb2ac4a86df,0x97825427fb29c12a1afd,0x2e0d509fecb704a86df5,0xb865427ff24c32a13fd9,0x58960d7fc22c4b04ff64,0x825827fb29c12c1aff85],#[0x15609fecaf04b06bf597,0x4427fb25c02a33fd92e,0x510ffcc92a0887fe5095,0x443fea84a8a21ff57448,0x10ff6a9284887fd50971,0x437fb0aa1221fed72509,0xbfecaa84886ffe15424,0x37ff0ea1221bfd875091,0xfbeaa2a4885ff65d4244,0xfff28a9221bff8454910,0xfac8ae4886ffa6152442,0xfb08b9221dfd745c910f,0xfca2e4886ffe11724437,0xd30b9221bfd985c910bf,0xb8a80907fe545404837f,0x22a8241ff96550120ffc,0x22a0907fe64d50483ff3,0xca8241ff99454120ffcb,0x2c0907fe55160483ff32,0xa8a41ff99558120ffcca,0xe2905ffe51514837fb08,0xa241ff99055120dfec22,0x8905ffe4d54482fff22a,0x241bfd8655120fbeb2aa,0x905ffe5954482ffb2caa,0x41ff99059120dfecc2a8,0x6ff61564483dfacab22,0x1bfd9859120bffcaac89,0x6ffe45844837fb22c224,0xbfd9561120dfeb2b0890,0xff659844837ff2ac2241,0xfd9161520dffcb308906],#[0xf64d854837ff22c2a41b,0xd9461520dffc9b0a906f,0x659854837ff28c2a41bf,0x9461920dffcb30a906ff,0x55864837ff28c3241bfd,0x260550dffcab0c906ff6,0x9815437fb04c0aa1f7d5,0x54950fbec1aa4a85ffe4,0x52543efb08a92a1f7d64,0x8950f7eb22c4a87df619,0x2542fff28b12a1bff845,0x950f7ec32c4a87df6556,0x542ffb30b12a1bfd9858,0x50bffcc2c4a86ffa6162,0x42fff26c12a1bfd83609,0xbffca304a86ff611825,0x37fb0cc12a1f7d656095,0xdfec930ca85ffe598254,0xdfb0ab12c1efd8458960,0xffca304b06ff61182583,0xfb0ac12c1efd6560960b,0xeca2a4885ffe55825837,0xb22aa241ffd945c910ff,0xcb2a8907ff64d54483ff,0x8b12a1ffd9559120ffe,0xc2c4a87ff65162543ffb,0x6c12a1ffd9160950ffec,0x304b07ff65982543ffb2,0x60001ffd9560960ffeca,0x3e00d702b007c015802,0x7981b6061816004e8119,0x8c2b80a4826209042110],#[0x3b00e0035a0ca83090b,0x4a3121c45c10d84100f8,0x82154853614404ef1324,0xe198c638180c5e216dc5,0x1d9473f1c646e41ae468,0x19c83720447dc1ed878b,0x7c93e244c8f2234489c2,0xa1327c89cc269898525,0xb152b94aba2a28a5a28d,0x122fb0bc62e6cb752d14,0x2341ccd73260c72311cc,0x384cde836ccd833574d3,0xbc8ed63ae8e9439a4e3e,0xe4fce3e50f693d0cf133,0xd0df42d107a413d0243f,0x1f046ed18b459513f443,0x14b3129c49c52464895,0x54f2539e4e093484c893,0x52b5491518543b50413e,0x6a958e5579529540d4e7,0xd9686594563058015d55,0xd7b55e0174b5c456e65a,0x8cb626d86b60ed8155fb,0xb9662596d64f591c63ed,0x6a41a656925a1e67b99,0x6e85b766d19b206bc1ac,0x319c967185c2c6fc9bc2,0xd5dca7655d5b7499cf67,0xc40200781c3f955e2077,0x9c4f10071164f15c4f17,0x144481c3835c503a0df0,0x1178483448400ff09c59],#[0x4834413a0ef080de10c1,0xd0dc24360a305845178,0xc582833094141104828,0x1104d160a0d4101904c1,0x198041104d163b04064,0x141145c120a4263b040e,0xc386784309848344818c,0x819e1384316485141601,0x584828405e065058070,0xb160a121a84cc2717845,0x80c1d84c0d7094161184,0x45e12480941613843161,0x387613019c230584601,0x1640180230584e114586,0x8e1985ec17080a61184d,0x78dc523bc481dc431707,0xc5c1e4a4007716c53130,0xe383a0df1423f1207710,0x2448400f81dc5b14c4c1,0x37c22410d81cc5313459,0x13c0df13c430845c1c48,0x671223f10885164835c5,0xdf1107516381fc501c8,0x4c5116c4c1c3f15c4b08,0x58c531345c1c47080d92,0x36c4d17070a0f837c20,0x83ec271645113070ec5,0x7c3e0771745221448e5,0x243f1745512c241c0f8c,0xc1c2f080f91444b17071,0x450845a1c4d154483ec5,0x23d16503a0df15c488fc],#[0xc501a0650981601c4f10,0xf943c5d08451128711,0x95816014271745512304,0x8194260580713c406cc5,0x91c5b1423b12471406,0x4951445a1d4491426058,0x44511287516403a0df08,0x14551744901003fc212,0xf10c2516505a16709816,0x48fc501a06605807121e,0x448e02605803154588ec,0x2c58f8160021f1745309,0x17449021f09806054551,0x9203b05800080651023e,0x131257150ef13c44160d,0xe8360970816600c54174,0xed04c503705b12238f0,0x8502360911444a170712,0x598011444d0585940df0,0xf114161651400f825c20,0x90dc501a06080c27120d,0xc48583314c4d04858368,0x23e17451002504c5616,0x174485833058000806d1,0xd158588f448e02305456,0x5c150483e480cc10080d,0x1050505412c583e3c41c,0x8c2717856134103e3f09,0xd41316852120fa24308,0x4d1638094161584b1616,0x400384886c17080fe158,0x4487c12305c261185e13],#[0x60a3050061145e12c843,0x378401d45e1223c34403,0x5058041304418c592c20,0x441306516c8120a828c2,0x6516c8120e028c16010,0x8d0e0a026c160104413,0x12c5904ee11803178492,0xd203e298614580610486,0x82283d058021984612c5,0x4823455040d61184b174,0x2113c4e82984600c5e12,0x14160086613843174810,0x194161184b1748228386,0x280660184920c5e1060,0x16120d12519442362986,0x8a104f13b84309801174,0x4403a0d5058430984d16,0xe0a30980517846124ec3,0x93c20358461345a281e0,0x827c2219802128451618,0x1600c26134111784140a,0x8421984d164629861465,0x3845168a1011504c2601,0x1784144401811504c261,0xa1851100a0198030984d,0xa1443861c260184e1145,0xc5c1c2819c2613845168,0x107b12c5c1c2b1107b12,0x12c5312c5c1f07324331,0x28c2036c4516c4c1c4d,0xb308c431545c1c148e0e,0xdc36c231545b1307100],#[0x481037c4f114588e5b42,0x1707058403d0d13407f1,0xb1707100f837c2314c4d,0xfc1c403ecf43ec251544,0x16101088807f17455120,0x6583e0df0945512c5c1c,0x9460380621f4421d44d1,0x945d138713842201b53,0x51744a1d499206601443,0x451623921b2200621f44,0x870e0f03607f15c4a1dc,0x7870f8050846310c4d17,0x2587138050846b10c551,0x944f6000f508c5312459,0x8874f03d423148731345,0x7508c5516c4e1c52408f,0xc4e1c4f0c5093c496001,0x5c4f114588e4600c5516,0x1544a1c50900721a8671,0x1124961c483e07889c5d,0x5d125143800434231645,0xa3a8d88e10d094521cc,0x23e0145512c5e1c508d5,0x12588a22717455128714,0x200633507f170731023b,0x18c4090c488e2892244,0xb42107b14c4b17073244,0x61b11c5713c4316238a1,0x1240200781dc5713c431,0x8e2442107f170731423b,0xd120801e073142431223,0xec3623f08c4516c4c1c4],#[0x6c5160631145b12238b0,0xa06f08150530731023d1,0x8e06b1145b14238a25b1,0xe944d714c2713c451623,0xd93407715c4f1145b081,0x1641cc508f45b12483a0,0xcc5516c488e2899c205a,0x3e21f16c251507512401,0x81dc5d1544b082191104,0x67094541d44b1648400f,0x45512c588630982185a1,0xc1217448360d1407709,0x12874344a3a0e42823d1,0x764a3a0d88fc251185d,0x380d029c251185d12c1,0xe82341314c408f058524,0xdb08c550505e00c4970,0x3c441623940e836d0c3b,0x58503c0d01fc51040df1,0x360970823b1541313058,0x6014111444b0985970e8,0x55128d8e108418d94250,0x44e16500e10504c26174,0xd44a1616920de0145309,0x1216120e8248df094541,0x920f824507084541d859,0x8616709806174551216,0x6f094151585d12161226,0x85d1544a36500c2607a1,0x3c251544e16502363709,0x1b4241c23b14c4616149,0x39206b1185b14238b0e8],#[0xd235c510941713c46162,0xc501dc4f1185b081e950,0xec521707312483a46919,0x1385858403bc22240d88,0xb12238b0ed090708ec53,0x151585d1216100731585,0x4141504a1e489816f08c,0x3410584842224400ff17,0x1c483e09441c23170541,0x431008821a1fc5e1584c,0x8400771785612c20863a,0x225c203e85213073164,0xc241d853178485840861,0xdc261584b16218d10087,0x284861145e130d08e481,0x21984d1784090593c4ea,0xf61c5146516298622848,0x9384c6004d31145b124,0x48a1ac4516c513d87142,0x4c4d178715c4e0015932,0x178715c49424f1258031,0x88e49424f1258051544b,0x5408f2365021f4561744,0x2a378051448513859405,0x1651585d1226178d9422,0x223942187b0905b07708,0x70ec364ac1c8d31185b1,0x5215314c461623896407,0x5ac53138588e2611070,0x3f0b8561248086541c16,0x84b1626131043f07089c,0x21c1c1670816e15]]
set_option maxRecDepth 16000 in
def g255H11 := limbs80 #[#[0x170381c2408010000c18,0xc020e8a400151000000,0xc02020083c221f02000,0xd80c1a0307800780f098,0x100060027e0000020071,0x2390485c1213068ac060,0xc0001040140020008500,0x860001601034500e0082,0x1000020a00004020800,0x3008000a0a0201cda03,0x2e090101846041b810ac,0xc12056913454410a84c,0x10183006038203801000,0x2018b402200708048200,0xa20550280a0300018780,0xc7a2e2d000e001010580,0x741e03160106c000126,0x9006260a0500304,0x192806c5c013913c000a,0x8010cc740a020400cc0,0x181418000a808203f854,0xb8181800019162e00050,0x80004402dc0b850fc000,0xe0406c060102c34300,0x4b1211d80c16025d1880,0x81c4c00060dc141b0080,0x1a2c0e986702478104d,0x182a07c4e0d000040944,0x1062000893603010440a,0xba819b71044a8e5018a8,0x11e7c1bbd0288c106921,0xf84021503350150c92cb],#[0x50b05e30112341d4c01,0xd817ba27ad4025c01e44,0x60b28ea743ec00009122,0x505a14a03a87d220a880,0x29f1786600f60496408c,0x15650201e1059006b21,0x5cd03ea549f946404388,0x410e00b94412f4032704,0xf1061214357274d80f8e,0x1182067ec899b04ce954,0x480d1b071894fde05fc2,0x579986378272085a627f,0xf553504dbf440d81abd2,0x33d501459b5424a109e6,0x848900002413fd112ac4,0x641052e858200d4e1412,0x1350014f400f45482716,0xf45480c10288307548fd,0x192500dc4551b0678153,0x64976005fad122301d38,0x5089ffb45c91038504b,0x2571843df402bc4fc44,0x4f4015f40937263ec153,0x403be21c500bab17bc89,0xb6088af1690545420796,0x50e3c950a0716c96a724,0x970378000062812c453e,0x1a45064300676155385b,0x401da3468849d4402bc1,0x1bdc0e5200c558f71066,0x100dac10b8444780b690,0xec7415bc1454403b904e],#[0x96d610814a01c048789,0xa3953500499184b254ef,0x44250029a03a10027a41,0x6006f80d58202e4083d,0x5cf13bd00491046a09d,0xc9069ba13348d4402364,0x2d005dfd40250132a025,0x622839481010ec907398,0x7c4218481bdc50f64895,0xe09a2103cc056f06e140,0x3b4135725de043722361,0x11bc80640169fa172e61,0xd5008d4157f13fb019df,0x22761c1c3644de898,0xe19117004684e2b05c00,0x5385ad60275147e324c,0xa518704bd9004a083a80,0xd724437148e9418b807e,0x8375073e503b50738c1,0x5a05a17279ec5abc410a,0x405754019d02,0xd03981557702b800000,0xbe50340000011418000,0xc8131244a700020867fe,0x30596e06380000b425,0x2d12a90748504c00,0x127b75909,0xc10fa0816c1a9411b400,0xa2403850561c4b660145,0x274881c8000008c36f21,0xca2200d47741447810db,0x503f2440b412],#[0x405a507fb144a002c00,0x890015b01c101c2d16b,0xd145b01eea86d040f270,0xb246c0000a05540000,0xf86cf95e40000000,0x8c584cc076d008161090,0x2dd01a4c55240000421,0x9a000c408f0000340732,0x128000000000906cf105,0x81f5954e9052c441634,0x341a250216406a6411,0x90647c1c78a3cb817300,0x13ce411e00003a8e8,0x8010a06580000f021800,0xcb550d0000090b670245,0x40f600591051cc144c07,0xf0000048438056800003,0x1228017800002240c095,0x4c0a1000000000e03580,0x340000000000000105a,0xe53f000000000180bf84,0x58c41200000000000000,0x9455000000000350d000,0xe40000c42b701e0b10f2,0x69d80a7e06c680c6f05,0x695512402d140d80000d,0x10741c0f380447404,0x1487e1023a400e000000,0x21400001005f0957820f,0x210d800001a305801d34,0x15203ee80ec3a6d40000,0xe91b905af40634078981],#[0x76e04c505b444fb65220,0x1e25034d077d44bb101,0xbd24a800000000000e97,0x4640e984b800000400,0x2c59e603e5413aa02d01,0x9a5c00d05d800003054,0x144f008af50efd5e020,0x6ee86d4c9900002ac45e,0x155000002018c40185c1,0x2f94fe00000000000002,0x24888af507a40000501,0xaf51ee511b00002d1985,0x201905950101f20ff89d,0x9486df062309583174a4,0x4c0b3951d00000610e,0x20273c1346013c090225,0xc2f050280ebba3df948d,0xe019f02d681bac452044,0xa80000e01ee01e8a059a,0x6dd4151454e5d437c05,0x4f253741dee3001d4731,0x105450e4010a4070141d,0x71525807ea859fc02f34,0x62801d588469c0726816,0x28042c0edd06e4143f34,0x600ab00450000280a0,0x9135a47be591b054d000,0x6f951f000038040c51d8,0x24100c790360c008504,0x4d0080512134683003a5,0xc0b43f6805b01348909,0x800006001181d8d10059],#[0x7e741307400800009027,0x940e780c15402f68e420,0x104d80000,0xc1771028c0000603d400,0xfb8198703344065f1452,0x235e0869b01c4c02bf20,0x8049f044ca16a5014a1,0xb1b825fa058203f845f,0x540bb507dcd54e424ac4,0x5904a402a2808b9072,0x2065328f6546d3015b40,0xf8168ac929905c96094,0xd0b7d17fd60dc403d885,0xfc01bf803c780a94816e,0x1d114446840000237,0xe058c0000407db45170,0x43ab06c34421f82fc000,0x741dc901d5c4dd000015,0xd00000f413dc5fed82b,0x1041680475046ef0,0x7901e89046000000000,0x417000000000a50f390,0xf1c16400000000040704,0x291805200519c11c400,0x30000000000000040ab1,0xb801057c1162064c41e,0xe11bc022684ecb062f8,0x69ac0da9219c05a69630,0xe038f8969903300000f0,0x91053ec543600734d110,0xc1597011d001c60669c9,0xc0002800003c1f400002],#[0x80f81fcd04ec804c807,0xee200341eae830350577,0x80b00002d53850315451,0x800c80020b5466103261,0xd7c1105053a19b40467,0xe02a940dd407fc0000e0,0xd47f4000080774d1b5,0xc138b400e51d1106d000,0x41cb74191c01e30135,0x65780fc523f88120000,0xc0000000000000041be0,0x45100000c09f504fa147,0x4c1efb04f5c18100003d,0x80800009072b00ce751d,0x168d808700002810042,0xf54840000000039523,0x301ad5025400,0x4403713574160d1680,0x7ec0000d06f001b2000,0xcf41550068801ffc044b,0x18d12453c06cf0552c1a,0xd10fc82196418f3047d8,0x17c00000000241437041,0x405240000003ffc92720,0x527a18923c06800000,0x80e21821740d9106da04,0x77c0e4208125049c0025,0x467561f7214575040514,0xf107c5c4b5f073340fa7,0xa8905d000002a3a4d11,0x1048c0000d052c9,0xcc8965901b6c0550000],#[0x316a9c919000000000a0,0x104910423500911012,0x51c025a000000000000,0x55886ae068e0832444d1,0x10fbc12e7119fc457117,0x3c07adc16cb142ad005c,0x114801f641afa12d300c,0xc00009234e905a337570,0xb2012b1043080b22033,0x506a800c04044d893200,0x26305364108154428021,0x210b504a9443fe026ec5,0x8434f810980381,0x51e4c1e7d07b48066e50,0xdc474f015cc549000002,0x5d09453b0076607cc84f,0xcc0a5644da00169060f0,0x2b78077803ab8456e010,0x3a3bfc15ec253981d6a0,0xdbc1173015f1058a809a,0xc03ef014fc5ae82746c0,0x1401ecf040c947284268,0x14b74060c05bc8104d10,0x75035c414860799a1a7a,0x18f0370c00661032903,0xe4891000000000000014,0x4640000f02fa8c334001,0x2792519f80509880e20,0xcb92592a1b2f14ad1548,0x605afa4641081c81ac80,0x1209e900002895af00e7,0xbf155864197883b602],#[0xcaa6a00137d449d2128b,0x1e4d080805a8b20c0903,0x400005165d1542b0532c,0x120dba05c640efd010,0xc04a7045dba07fc08800,0x1b500bb417c503f78030,0x1e1da07381a5c0263a0,0xe961a81114a40df91670,0x7e04973e458290de305,0x5a112e400d940d5c04af,0xff50686885724234c1b,0xc49d900000000000003d,0x2e950a53440601618117,0xa26311051d05f4418a91,0x6b1046380f01548949e1,0x49dd312e651001032b40,0xbac175f44398926e10e0,0x39c1403d0800c1d3c03,0xc0025000bdd101a00622,0x435104f1c4f2a061b850,0x8d0666a3c40000500020,0x7540000b223bd0b4d013,0x50fbc139a0764906322,0xe451c20959a141d90fe,0x8460745370069450cec1,0x4b81805034d212a56467,0x109c1a8521fcc06ec05,0x48551dc19c503d15118c,0x1fd00710c0a6f059f095,0xc4bc122740000f03dc8,0x22dc46c10384c189c003,0x280486250e180e72],#[0xf03128831246940000,0xd53c3427000002a7dc00,0x9501d1a54380000241ad,0x26781ae102b0c0d2e51,0x23061d1537651a310414,0x60309c013354dbd11,0x5c00f904bee069841500,0x34197c001684dfb061,0x8262e49fed0504000000,0x206a100fd0512]]
def g255D12 := limbs80 #[#[0x54510ff521443fe54110,0x442ff60910ff571443fd,0xbff85442ff61510bff82,0x50120bff87442ff61d10,0x483fe58120ff950483fe,0xbfd86482ff61520bfd84,0xe0950f7d52542ffe0550,0x543df59550bff83542ff,0xefd62582ffe1950bfd86,0xe1560efd65582ffe0960,0x443ff50910bff80546ff,0xffd51483ff5c910ffd52,0x59120ffd54483ff5c520,0x543ff60550ffd65483ff,0xffd83543ff60950ffd62,0x61560ffd82583ff61950,0x5ac49836024c138003ff,0xf0bb8ac89d88c47b069c,0xd4412e51d10bcf3cde0c,0xc81b91a599697e96b159,0xbe43e29a13dfbdea9db9,0xed9ec1eac29ae8766f65,0x22e121a2330f1d707af1,0x90406870006f098284,0x24100c458f87c220a0,0x8b0482018132309828,0xc220a0108848687c260a,0x48f844162e11090a0d87,0x16141f098280420188b8,0x84031163e13041a84425,0xa1308458506c260a0109,0x8c56271788078386c260],#[0x18358ac206f13880722c,0xf100e27081fc5a29120e,0xe459410c5034198907e2,0xe1d0de281a0cc2627100,0xb1c401fc262d140e448,0x2e004e1305000622113,0x61b27141d0de13138841,0x58e0d0662b0989416221,0x16122309828003514888,0x85a24ac2608370045224,0xc60f86c242cc260a008a,0xa04c008c260a168a4486,0x2a121f18401fc262d040,0x458281212230882c5c,0x60a15094587c6c26083f,0x584c1202110b848707c2,0x1432280c8062e1109481,0x8828440117090d12144,0xc220a010945c20b4e853,0x116898714148628a280c,0xe49909c46400380cc222,0x2e1c540019844422d130,0x4078358a8027b1284c42,0xe2180285098b452261c,0x61a26018445225170e49,0x4941c0a613048885a243,0xb50082378441401150b4,0x6b09890711f110b0d941,0x84c122a168814938a0e8,0x609150b448b090b0441b,0xd8b854243e407c3612c2,0x142a128b16122021e101],#[0xf86c2584c]]
set_option maxRecDepth 16000 in
def g255H12 := limbs80 #[#[0x110000060300001b00,0xb0d37010f61002307,0x4401070d051255061300,0x100c1002022507000200,0x2f3900030f0198072c07,0x31c06132093131500,0x113023207101101033a,0x87070e0100123d1400,0x21d084f01000c3d8500,0x460331930b0208ab0112,0x713e508f548dd11bb901,0x6415d04c5262e032,0x2b4018d651d94208462,0xd084c052e002d06be18c,0x1618f25c6014f19f002b,0x722e5195b093e129703b,0x34847b84ff080,0x21337148f56e20400000,0xa5226a4c5071e0ad5aae,0xf892d004605ca036c029,0x500070a6103d71a1e033,0x800b9089a112245faa54,0x3a480000816090a71512,0x4060000209bc56d615f,0x7050d1240000f091c066,0x20947062a25a42722212,0x4082c414805702207164,0xc45c0000a031907a202d,0xc14314139265e849a1a0,0x949441414634c0530000,0x44d4a1d106a2640010,0x708cf12f057190190000],#[0xe5681122f0aea114e5ab,0x914750610430f026c562,0x913c60b2c10400000030,0xb06e7020211a40af,0x6287a41ac08e6569,0xe433e092723c005fb842,0x6f21800002042,0x801a619d91885027b110,0x60353016f155e48bc060,0x106f5078301b3051,0xb11370b3c46871151140,0xe070722a7408308d0000,0xf2a40000684b81360000,0x101f0000115d0000156b,0x20a5a1630000b6580000,0x68ae0048c8949128707d,0xf355000020a16234d566,0xa0584097905e0000d130,0x5a4e0000a81e610f4279,0x60a4000060673416008b,0x748e9132f144d0438a91,0x40815065122131a588a7,0x5701156b19c2a580000,0xa19830961405600a,0x7aa8e02c818a,0x25aa5834e025b4320278,0x71a4800d91218073,0x705b413902a67099d055,0x80b48214d04a00004107,0x3515709d111cb1030000,0x55ac66a1f076d134d13b,0x6286e65fa046d0a85074],#[0xd08760a04418200e60a2,0x605a009e8653207241ad,0x25ba470c064c846d417,0xa0283056904500008a18,0xba53b017c172d273e09a,0xf267d11fb090b0a31513,0x5131d03fb26c021bd45b,0xf193a023100f903a1275,0x5109c0aa5012c45a604d,0xd04900242018ba8fb276,0xd07ec01172ac7524b845,0xe0054007000098335514,0xf0394008931200000000,0xd06a223eb098a138c41d,0xc09c215000009891200c,0xf059906d718e504f0000,0x26d1085308a0000d56a,0xa1170000413a0000f02a,0xf5a95009403ce02ec56f,0xf0b1000000ab504eb41e,0x641bb105000000ac0000,0xf16170750694484c1120,0x75730000c56c0063a434,0x903e34920000223f605d,0x51199226001558510108,0x802fe2719054907f40a9,0xf2a110956831,0x907900000068d088f63c,0x5223c0137189b18b9412,0x843c5403f616011df069,0x50414a57051700006037,0xf2a50000b4310000943b],#[0x9818d022007cd314e021,0xb09f0000d277b0382083,0x212af07b80347001a01d,0xc88f0000d04b52290000,0x75741190e08638080000,0xc25f94a00000c06c,0x611140773047601c20b0,0x901ed488315e]]
def g255D13 := limbs80 #[#[0x1ffac1ff543fe907fd10,0x4211801ff597feb8ffd5,0x8022c24208c653a10ca,0x84898b880e1c503212,0xe286e120a2402202c88a,0x2c2081f8482008b0a091,0x908131c7032120a0024,0xa002c28244878482800b,0x2120]]
def g255H13 := limbs80 #[#[0x4800b2000003040c0186,0x461400184000404c3000,0xc22f424301c69c1078,0x47409d8b0000000417c0,0x728c419119a11,0x658ba061138c0f,0x1108415c48e68740000,0xec452284044e57c00000,0x417d009a1c0001869140,0x23e2800008580c133196,0x700ea25b41bd2500000,0x51780000002a02000000,0x940000000000518cc22,0x7c000514911b480c0148,0x144cb09c001a01000042,0x82a413d161000000c000,0xf696a1b00022150002,0xca163410000000080840,0xd42800012aac880001c1,0xc1b402280d0000000,0x143000081479630,0x5c0e0000c41000001600,0x280000000b174c4bd04,0x15000001d0000c0a709a,0x400642fc1fc8660,0xd0600005820000e02e42,0xa58050000000b455409,0x680000000519e180ea54,0x80001a7bc950002c1ac2,0x406000059e2475c99804,0x28524840003]]
def g255D14 (j : Nat) := if j=0 then 0xa080800916207ff else 0
def g255H14 := limbs80 #[#[0x49000000000000841,0x70600000000c8400,0x8400000000220c64e000,0x780f0c00000000000006,0xc8b4b48900000000186,0x30928100000000129f6,0xa85854a40000050212a0,0x1252,0x52300000000]]
def g255L : Nat → Packing
  | 7 => (9,7,7,0,0,8,0,g255D7)
  | 8 => (169,6,7,0,0,13,0,g255D8)
  | 9 => (541,5,7,0,0,16,0,g255D9)
  | 10 => (518,4,7,0,0,16,0,g255D10)
  | 11 => (181,3,7,0,0,14,0,g255D11)
  | 12 => (43,2,7,0,0,12,0,g255D12)
  | 13 => (7,1,7,0,0,9,0,g255D13)
  | 14 => (1,0,7,0,0,0,0,g255D14)
  | _ => emptyPacking
def g255I : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 5 29 4 12 4 4 g255H8
  | 9 => lookupWord 91 499 6 16 8 4 g255H9
  | 10 => lookupWord 294 9767 2 18 10 4 g255H10
  | 11 => lookupWord 260 1193 9 18 10 4 g255H11
  | 12 => lookupWord 102 467 8 16 8 4 g255H12
  | 13 => lookupWord 27 163 6 14 6 4 g255H13
  | 14 => lookupWord 6 61 2 11 3 4 g255H14
  | _ => fun _ => none
def g255 : Forest := ⟨255,14,fun i => g255Y[i]?.getD (0,0),g255C,g255A,g255L,g255I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P7_0 : block g255 7 0 9=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B7 : block g255 7 0 9=true := g255P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_0 : block g255 8 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_1 : block g255 8 1 46=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_47 : block g255 8 47 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_143 : block g255 8 143 26=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B8 : block g255 8 0 169=true := (@block_merge g255 8 0 47 122 (@block_merge g255 8 0 1 46 g255P8_0 g255P8_1) (@block_merge g255 8 47 96 26 g255P8_47 g255P8_143))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_0 : block g255 9 0 49=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_49 : block g255 9 49 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_145 : block g255 9 145 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_241 : block g255 9 241 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_337 : block g255 9 337 37=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_374 : block g255 9 374 96=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_470 : block g255 9 470 71=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B9 : block g255 9 0 541=true := (@block_merge g255 9 0 241 300 (@block_merge g255 9 0 49 192 g255P9_0 (@block_merge g255 9 49 96 96 g255P9_49 g255P9_145)) (@block_merge g255 9 241 133 167 (@block_merge g255 9 241 96 37 g255P9_241 g255P9_337) (@block_merge g255 9 374 96 71 g255P9_374 g255P9_470)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_0 : block g255 10 0 15=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_15 : block g255 10 15 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_111 : block g255 10 111 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_207 : block g255 10 207 12=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_219 : block g255 10 219 96=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_315 : block g255 10 315 96=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_411 : block g255 10 411 68=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_479 : block g255 10 479 39=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B10 : block g255 10 0 518=true := (@block_merge g255 10 0 219 299 (@block_merge g255 10 0 111 108 (@block_merge g255 10 0 15 96 g255P10_0 g255P10_15) (@block_merge g255 10 111 96 12 g255P10_111 g255P10_207)) (@block_merge g255 10 219 192 107 (@block_merge g255 10 219 96 96 g255P10_219 g255P10_315) (@block_merge g255 10 411 68 39 g255P10_411 g255P10_479)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_0 : block g255 11 0 3=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_3 : block g255 11 3 63=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_66 : block g255 11 66 96=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_162 : block g255 11 162 5=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_167 : block g255 11 167 14=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B11 : block g255 11 0 181=true := (@block_merge g255 11 0 66 115 (@block_merge g255 11 0 3 63 g255P11_0 g255P11_3) (@block_merge g255 11 66 96 19 g255P11_66 (@block_merge g255 11 162 5 14 g255P11_162 g255P11_167)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P12_0 : block g255 12 0 28=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P12_28 : block g255 12 28 15=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B12 : block g255 12 0 43=true := (@block_merge g255 12 0 28 15 g255P12_0 g255P12_28)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P13_0 : block g255 13 0 7=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B13 : block g255 13 0 7=true := g255P13_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P14_0 : block g255 14 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B14 : block g255 14 0 1=true := g255P14_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255T : checkedTables g255 14 := by
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
  · exact g255B14
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255G : graphValid g255 (boundsBefore K247) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255R : Impossible true graph 14 sevenInputs.toFinset := by
  rw [show graph = targetOf g255 by decide +kernel]
  exact root_index (g:=g255) (top:=14) (i:=0) (before_sound K247 V247) g255G g255T (by decide) (by decide +kernel)

end PEqualNP.Outside.L_meta_51998

open PEqualNP.Outside.L_meta_51998 in
theorem PEqualNP.Outside.L_meta_51998 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o fit _ correct
  exact replaceShort g255R gates o fit correct

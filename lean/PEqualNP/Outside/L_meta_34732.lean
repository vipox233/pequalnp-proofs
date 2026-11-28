import PEqualNP.Defs

-- The two-mode live-state and cofactor checker follows L_meta_1674 and L_meta_670.
-- The graph, restrictions and all search certificates below are for L_meta_34732.

-- Shared forest and cofactor certificates from L_meta_1674 and PR 11111 for L_meta_1677.
-- The original credit line is retained below. The two root certificates here cover the unpinned graph.

-- The checker and the bound certificates are adapted from PEqualNP/Outside/L_meta_1667.lean (Apache-2.0).
-- Two modes: u=false are monotone runs (AND, OR); u=true are runs up to complement, where negation is free.
namespace PEqualNP.Outside.L_meta_34732
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
def graph : Sig := (BitVec.ofNat 512 (word80 [0xffffffff,0xfffffffffffffffeffff,0xfefefffffffefffffefa,0xfffeffecfefaeca0ffff,0xfffffffffffffffffffe,0xfffffefefffffffeffff,0xfefafffeffecfefaeca0]))
def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 2) || (x 1 && x 3) || (x 0 && x 4) || (x 2 && x 4) || (x 1 && x 5) || (x 3 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 4 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 2 && x 7) || (x 4 && x 7) || (x 6 && x 7)
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
  (x 0 &&& x 2) ||| (x 1 &&& x 3) ||| (x 0 &&& x 4) ||| (x 2 &&& x 4) ||| (x 1 &&& x 5) ||| (x 3 &&& x 5) ||| (x 0 &&& x 6) ||| (x 2 &&& x 6) ||| (x 4 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 2 &&& x 7) ||| (x 4 &&& x 7) ||| (x 6 &&& x 7)
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
  (x 0 &&& x 2) ||| (x 1 &&& x 3) ||| (x 0 &&& x 4) ||| (x 2 &&& x 4) ||| (x 1 &&& x 5) ||| (x 3 &&& x 5) ||| (x 0 &&& x 6) ||| (x 2 &&& x 6) ||| (x 4 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 2 &&& x 7) ||| (x 4 &&& x 7) ||| (x 6 &&& x 7)
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



def target (x : Fin 8 → Bool) : Bool := decide (∃ i < ([0, 2, 1, 3, 0, 4, 2, 4, 1, 5, 3, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 1, 5, 3, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 1, 5, 3, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
def smallCircuit : Circuit := ⟨[⟨.or,[4,6]⟩,⟨.or,[1,3]⟩,⟨.or,[0,8]⟩,⟨.or,[2,8]⟩,⟨.or,[0,7]⟩,⟨.or,[2,7]⟩,⟨.or,[3,7]⟩,⟨.and,[5,9]⟩,⟨.and,[14,1]⟩,⟨.and,[12,11]⟩,⟨.and,[13,10]⟩,⟨.and,[6,4]⟩,⟨.or,[15,16]⟩,⟨.or,[20,17]⟩,⟨.or,[21,18]⟩,⟨.or,[22,19]⟩], 23⟩

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

def lowRow (i : Fin 8) : Row := Fin.ofNat 512 (1 <<< ([2, 3, 0, 1, 0, 1, 0, 0] : List Nat).getD i.val 0)
def highRow (i : Fin 8) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< ([2, 3, 0, 1, 0, 1, 0, 0] : List Nat).getD i.val 0))

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
def K21 := extendKnown [] 4 [(21,[]),(42,[16,50,84]),(69,[100,84]),(81,[66,50,99,83]),(84,[32,16,65,49,99,83]),(133,[116,84,101]),(145,[66,50,115,83,101]),(148,[32,16,65,49,115,83,101]),(193,[98,50,116,83,84]),(196,[32,16,97,49,116,83,84]),(208,[64,16,98,49,115,82,83])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V21 : Known true K21 := extend_ok (m:=21) baseKnown low21 (by decide +kernel)
def g85Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xdf7ec03c3ffe0fbefd,0x80787ffc1f7dfb00f0ff])),(BitVec.ofNat 152 (word80 [0x820404444444210408,0x8888888420810111111]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1fbf43c3c3fff03f7e,0x878787ffe07efd0f0f0f])),(BitVec.ofNat 152 (word80 [0x40808888888420810,0x11111110841020222222]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xe03fbc03fc3fffc07f,0x7807f87fff80fef00ff0])),(BitVec.ofNat 152 (word80 [0x81011111110841020,0x22222221082040444444]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffc03ffc003fffff80,0x7ff8007fffff00fff000])),(BitVec.ofNat 152 (word80 [0x102022222221082040,0x44444442104080888888]))),(0x0,0x0),(0x0,0x0)]
def g85C : List ColumnInfo := [(1,0,84,0,4),(4,0,81,0,4),(16,0,69,0,4),(64,0,21,0,4)]
def g85A : List (List Nat) := [[],[100],[66],[66,98],[98,66],[98],[32],[32,100],[32,64],[32,64,96],[32,96,64],[32,96],[64,32],[64,32,98],[64],[64,96],[64,98],[64,98,32],[96,32,66],[96,32],[96,64],[96],[96,66,32],[96,66]]
def g85D3 := limbs80 #[#[0x23ea6a1221e12148110,0x8028]]
def g85D4 := limbs80 #[#[0x2fd0910bd42443e48110,0x609085870]]
def g85H4 (j : Nat) := if j=0 then 0xe8 else 0
def g85D5 (j : Nat) := if j=0 then 0xd1027d10 else 0
def g85H5 := limbs80 #[#[0x2e0000046b0c004,0x69584007236]]
def g85D6 (j : Nat) := if j=0 then 0x3904f else 0
def g85H6 := limbs80 #[#[0x681d00082002442a,0x3c000]]
def g85L : Nat → Packing
  | 3 => (2,3,2,0,0,5,0,g85D3)
  | 4 => (3,2,2,0,0,5,0,g85D4)
  | 5 => (1,1,2,0,0,0,0,g85D5)
  | 6 => (1,0,2,0,0,0,0,g85D6)
  | _ => emptyPacking
def g85I : Nat → Nat → Option (Nat × Nat)
  | 4 => lookupWord 1 2 0 5 1 0 g85H4
  | 5 => lookupWord 2 13 3 9 2 3 g85H5
  | 6 => lookupWord 1 11 0 9 0 5 g85H6
  | _ => fun _ => none
def g85 : Forest := ⟨85,6,fun i => g85Y[i]?.getD (0,0),g85C,g85A,g85L,g85I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g85P3_0 : block g85 3 0 2=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g85B3 : block g85 3 0 2=true := g85P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g85P4_0 : block g85 4 0 3=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g85B4 : block g85 4 0 3=true := g85P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g85P5_0 : block g85 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g85B5 : block g85 5 0 1=true := g85P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g85P6_0 : block g85 6 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g85B6 : block g85 6 0 1=true := g85P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g85T : checkedTables g85 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g85 0 0 0 = true)
  · exact (rfl : block g85 1 0 0 = true)
  · exact (rfl : block g85 2 0 0 = true)
  · exact g85B3
  · exact g85B4
  · exact g85B5
  · exact g85B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g85G : graphValid g85 (boundsBefore K21) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low85 : Lower true (varsX 85) (graphGoal 85) 7 := lower_forest (g:=g85) (i:=0) (hints:=2) (before_sound K21 V21) g85G g85T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K85 := extendKnown K21 7 [(85,[]),(149,[118]),(197,[100,84,117]),(209,[66,50,99,83,117]),(212,[32,16,65,49,99,83,117])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V85 : Known true K85 := extend_ok (m:=85) V21 low85 (by decide +kernel)
def g135Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfdf00fff81fc7e3ffb,0xe01fff03f8fc7ff7c03f])),(BitVec.ofNat 152 (word80 [0x45c09245142904808b,0x81248a28520901170249]))),((BitVec.ofNat 152 (word80 [0xe6a8703ffe007fc7cd,0x50e07ffc00ff8f9aa1c0])),(BitVec.ofNat 152 (word80 [0x96a9b6d618b228112d,0x536dac316450225aa6db]))),((BitVec.ofNat 152 (word80 [0xfbb781ffffff8007f7,0x6f03ffffff000feede07])),(BitVec.ofNat 152 (word80 [0x235249820c0312204,0x6a49304180624408d492]))),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x64ffe3ffffffff80c,0x9ffc7ffffffff0193ff8])),(BitVec.ofNat 152 (word80 [0x249204100400400,0x4924082008008000924]))),(0x0,0x0)]
def g135C : List ColumnInfo := [(2,0,133,0,4)]
def g135A : List (List Nat) := [[],[32]]
def g135D4 (j : Nat) := if j=0 then 0x1f else 0
def g135L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g135D4)
  | _ => emptyPacking
def g135I (_ _ : Nat) : Option (Nat × Nat) := none
def g135 : Forest := ⟨135,4,fun i => g135Y[i]?.getD (0,0),g135C,g135A,g135L,g135I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g135P4_0 : block g135 4 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g135B4 : block g135 4 0 1=true := g135P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g135T : checkedTables g135 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g135 0 0 0 = true)
  · exact (rfl : block g135 1 0 0 = true)
  · exact (rfl : block g135 2 0 0 = true)
  · exact (rfl : block g135 3 0 0 = true)
  · exact g135B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g135G : graphValid g135 (boundsBefore K85) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low135 : Lower true (varsX 135) (graphGoal 135) 5 := lower_forest (g:=g135) (i:=0) (hints:=114) (before_sound K85 V85) g135G g135T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K135 := extendKnown K85 5 [(135,[]),(170,[48,113,82,66])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V135 : Known true K135 := extend_ok (m:=135) V85 low135 (by decide +kernel)
def g139Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x2fc38ff01fff1ff02,0xfc38ff01fff1ff02fc38])),(BitVec.ofNat 152 (word80 [0x42ccdb2a5451240242,0xccdb2a5451240242ccdb]))),((BitVec.ofNat 152 (word80 [0xfdcbc7fffe07fe3ffd,0xcbc7fffe07fe3ffdcbc7])),(BitVec.ofNat 152 (word80 [0x1448490c1860408414,0x48490c18604084144849]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xece607fffff8003fec,0xe607fffff8003fece607])),(BitVec.ofNat 152 (word80 [0x8a7b6b06085892808,0xa7b6b06085892808a7b6]))),(0x0,0x0),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1b3df8ffffffffc01b,0x3df8ffffffffc01b3df8])),(BitVec.ofNat 152 (word80 [0x893124c08106003089,0x3124c081060030893124]))),(0x0,0x0)]
def g139C : List ColumnInfo := []
def g139A : List (List Nat) := [[],[48,113]]
def g139D3 (j : Nat) := if j=0 then 0xf else 0
def g139L : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,g139D3)
  | _ => emptyPacking
def g139I (_ _ : Nat) : Option (Nat × Nat) := none
def g139 : Forest := ⟨139,3,fun i => g139Y[i]?.getD (0,0),g139C,g139A,g139L,g139I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g139P3_0 : block g139 3 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g139B3 : block g139 3 0 1=true := g139P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g139T : checkedTables g139 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g139 0 0 0 = true)
  · exact (rfl : block g139 1 0 0 = true)
  · exact (rfl : block g139 2 0 0 = true)
  · exact g139B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g139G : graphValid g139 (boundsBefore K135) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low139 : Lower true (varsX 139) (graphGoal 139) 4 := lower_forest (g:=g139) (i:=0) (hints:=4151) (before_sound K135 V135) g139G g139T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K139 := extendKnown K135 4 [(139,[]),(142,[32]),(154,[48,113,32,66]),(202,[48,113,32,98,66,84])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V139 : Known true K139 := extend_ok (m:=139) V135 low139 (by decide +kernel)
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
theorem g31G : graphValid g31 (boundsBefore K139) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low31 : Lower true (varsX 31) (graphGoal 31) 6 := lower_forest (g:=g31) (i:=0) (hints:=4146) (before_sound K139 V139) g31G g31T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K31 := extendKnown K139 6 [(31,[]),(47,[16,50,84]),(55,[83]),(59,[16,50,66,82]),(61,[49,81]),(62,[16,32,48,64,80]),(79,[100,84]),(91,[66,98,82]),(94,[32,64,96,80]),(110,[16,32,48,96,84,64]),(173,[49,81,116,100]),(185,[49,66,81,114,98]),(188,[32,49,64,81,112,16,97])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V31 : Known true K31 := extend_ok (m:=31) V139 low31 (by decide +kernel)
def g143Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xf003ff87fe1fffc01f,0xfff87fffe474a4007c1f])),(BitVec.ofNat 152 (word80 [0xa12845108440228940,0xa01108826014a45294a5]))),((BitVec.ofNat 152 (word80 [0xfffc0007ffe1ffffe0,0xfffffc0335be20f83e0])),(BitVec.ofNat 152 (word80 [0xc030162028040b0182,0xc0a00108225922318c63]))),((BitVec.ofNat 152 (word80 [0xfffffff80001ffffff,0xf0007ffccfd11df0001f])),(BitVec.ofNat 152 (word80 [0x240980130884c0203,0x2c2120087c108a5294a]))),((BitVec.ofNat 152 (word80 [0x1ffffff,0xffff80004d2fe80003e0])),(BitVec.ofNat 152 (word80 [0xb82e045c111702c14,0xb005c104d26c9ce739c]))),(0x0,0x0),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffffffe000000,0x33aa61bfffc00])),(BitVec.ofNat 152 (word80 [0xc0300060001803018,0xc046021182211084210]))),(0x0,0x0)]
def g143C : List ColumnInfo := [(0,8,133,2,5),(8,0,135,0,5),(1,0,142,0,4),(2,8,133,0,4),(4,0,139,0,4)]
def g143A : List (List Nat) := [[],[32]]
def g143D4 (j : Nat) := if j=0 then 0x5bd4940 else 0
def g143D5 := limbs80 #[#[0x240d140ff40fd40fd20,0x2012]]
def g143H5 (j : Nat) := if j=0 then 0xa else 0
def g143D6 (j : Nat) := if j=0 then 0x18989f else 0
def g143H6 (j : Nat) := if j=0 then 0xe40750441700 else 0
def g143L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g143D4)
  | 5 => (3,1,3,0,0,5,0,g143D5)
  | 6 => (1,0,3,0,0,0,0,g143D6)
  | _ => emptyPacking
def g143I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 4 0 0 g143H5
  | 6 => lookupWord 1 7 0 7 2 1 g143H6
  | _ => fun _ => none
def g143 : Forest := ⟨143,6,fun i => g143Y[i]?.getD (0,0),g143C,g143A,g143L,g143I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g143P4_0 : block g143 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g143B4 : block g143 4 0 1=true := g143P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g143P5_0 : block g143 5 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g143B5 : block g143 5 0 3=true := g143P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g143P6_0 : block g143 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g143B6 : block g143 6 0 1=true := g143P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g143T : checkedTables g143 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g143 0 0 0 = true)
  · exact (rfl : block g143 1 0 0 = true)
  · exact (rfl : block g143 2 0 0 = true)
  · exact (rfl : block g143 3 0 0 = true)
  · exact g143B4
  · exact g143B5
  · exact g143B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g143G : graphValid g143 (boundsBefore K31) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low143 : Lower true (varsX 143) (graphGoal 143) 7 := lower_forest (g:=g143) (i:=0) (hints:=4146) (before_sound K31 V31) g143G g143T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K143 := extendKnown K31 7 [(143,[]),(155,[66]),(158,[32,64]),(167,[83,67]),(171,[48,113,82,66]),(174,[48,113,82,32,64]),(179,[66,83]),(182,[32,64,83]),(186,[48,113,82,64]),(203,[98,66,84]),(206,[32,96,64,84]),(218,[64,98,82])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V143 : Known true K143 := extend_ok (m:=143) V31 low143 (by decide +kernel)
def g151Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfe1ff00ff87f87ffc0,0x7fc7ffffd3b94000f0ff])),(BitVec.ofNat 152 (word80 [0x1440a0a05101100285,0x2902008418941111111]))),((BitVec.ofNat 152 (word80 [0x1ffff0007ff87fff,0x8007f1fc231ee00f0000])),(BitVec.ofNat 152 (word80 [0x588ac4c5622a012b06,0x2b214491231ee7777777]))),((BitVec.ofNat 152 (word80 [0x1fffffff80007fff,0xfff801ff9c1f30f00f0f])),(BitVec.ofNat 152 (word80 [0x61030101800c220c08,0xc0188201c1602222222]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffe000000000007fff,0xfffffe000be4bf000ff0])),(BitVec.ofNat 152 (word80 [0x800c06060430443010,0x300200c20260b4444444]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffff8000,0x6442cffff000])),(BitVec.ofNat 152 (word80 [0x1008080040004020,0x40040100000008888888]))),(0x0,0x0)]
def g151C : List ColumnInfo := [(2,0,149,0,7)]
def g151A : List (List Nat) := [[],[66],[32],[32,64],[64,32],[64]]
def g151D7 (j : Nat) := if j=0 then 0x3f else 0
def g151L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g151D7)
  | _ => emptyPacking
def g151I (_ _ : Nat) : Option (Nat × Nat) := none
def g151 : Forest := ⟨151,7,fun i => g151Y[i]?.getD (0,0),g151C,g151A,g151L,g151I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g151P7_0 : block g151 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g151B7 : block g151 7 0 1=true := g151P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g151T : checkedTables g151 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g151 0 0 0 = true)
  · exact (rfl : block g151 1 0 0 = true)
  · exact (rfl : block g151 2 0 0 = true)
  · exact (rfl : block g151 3 0 0 = true)
  · exact (rfl : block g151 4 0 0 = true)
  · exact (rfl : block g151 5 0 0 = true)
  · exact (rfl : block g151 6 0 0 = true)
  · exact g151B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g151G : graphValid g151 (boundsBefore K143) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low151 : Lower true (varsX 151) (graphGoal 151) 8 := lower_forest (g:=g151) (i:=0) (hints:=114) (before_sound K143 V143) g151G g151T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K151 := extendKnown K143 8 [(151,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V151 : Known true K151 := extend_ok (m:=151) V143 low151 (by decide +kernel)
def g213Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xc0fc0fc0fbf0fbf7f0,0x3ffdf801c0e3f10c1cfe])),(BitVec.ofNat 152 (word80 [0x820820820022102020,0x8208109209040004084a]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xff000fff03ff03fbff,0xc0fffc0e071c7230631d])),(BitVec.ofNat 152 (word80 [0x41041041040204041,0x4102120502080102111]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffff00003fffc03ff,0xff01fc70381f83c383e1])),(BitVec.ofNat 152 (word80 [0x82082082080008082,0x8204204824013410280]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffffc000003ff,0xfffe03803fe00c03fc02])),(BitVec.ofNat 152 (word80 [0x104104104104410104,0x10408049000924025000]))),((BitVec.ofNat 152 (word80 [0xfffffffffffffffc00,0x3ffc0000ffc0003])),(BitVec.ofNat 152 (word80 [0x208208208208820208,0x20810000249248a80000]))),(0x0,0x0)]
def g213C : List ColumnInfo := [(1,0,212,0,7),(4,0,209,0,7),(16,0,197,0,7),(64,0,149,0,7),(128,0,85,0,7),(5,0,208,0,4),(17,0,196,0,4),(20,0,193,0,4),(65,0,148,0,4),(68,0,145,0,4),(80,0,133,0,4)]
def g213A : List (List Nat) := [[],[118],[100],[100,116],[116,100],[116],[66],[66,118],[66,98],[66,98,114],[66,114,98],[66,114],[98,66],[98,66,116],[98],[98,114],[98,116],[98,116,66],[114,66,100],[114,66],[114,98],[114],[114,100,66],[114,100],[32],[32,118],[32,100],[32,100,116],[32,116,100],[32,116],[32,64],[32,64,118],[32,64,96],[32,64,96,112],[32,64,112,96],[32,64,112],[32,96,64],[32,96,64,116],[32,96],[32,96,112],[32,96,116],[32,96,116,64],[32,112,64,100],[32,112,64],[32,112,96],[32,112],[32,112,100,64],[32,112,100],[64,32],[64,32,118],[64,32,98],[64,32,98,114],[64,32,114,98],[64,32,114],[64],[64,118],[64,96],[64,96,112],[64,112,96],[64,112],[64,98],[64,98,114],[64,98,32],[64,98,32,112],[64,98,112,32],[64,98,112],[64,114,98],[64,114],[64,114,32,96],[64,114,32],[64,114,96],[64,114,96,32],[96,32,66],[96,32,66,116],[96,32],[96,32,114],[96,32,116],[96,32,116,66],[96,64],[96,64,116],[96],[96,112],[96,116],[96,116,64],[96,66,32],[96,66,32,114],[96,66],[96,66,112],[96,66,114],[96,66,114,32],[96,114,64,66],[96,114,64],[96,114,66],[96,114,66,64],[96,114],[96,114,32],[112,32,66,100],[112,32,66],[112,32,98],[112,32],[112,32,100,66],[112,32,100],[112,64,100],[112,64],[112,96],[112],[112,100,64],[112,100],[112,66,32,98],[112,66,32],[112,66,96],[112,66],[112,66,98,32],[112,66,98],[112,98,64],[112,98,64,66],[112,98,66,64],[112,98,66],[112,98,32],[112,98]]
def g213D3 := limbs80 #[#[0x887805915350d2148110,0x4180360709aa26498a40,0x2]]
def g213D4 := limbs80 #[#[0x48110f415350d2148110,0x54d2148110b618550d21,0xe636454d2148110e6164,0x48110b638454d2148110,0xd4d2148110e6364d4d21,0xf41544c93148110b6184,0x48110f43544c93148110,0xd913148110f814350931,0xcb374d913148110ad183,0x4c91087b805d9544c910,0x82a4854300c3874dc165,0x808103df5df82d4b78d9,0x4002820a04000000120,0x1]]
def g213H4 := limbs80 #[#[0x0,0x0,0xfc4c0d00000010,0x30000000201000000000,0x7]]
def g213D5 := limbs80 #[#[0xa4290221d854d2148110,0x4887c1324c520443b1a9,0x850d214811087ee8b2a6,0xc520443f0a9a4290221f,0x10fc2e498a40887e1424,0xaa26290221dc55131481,0xa40886f1644c520443b9,0x15e5d54348110de6c898,0x254d20442f5b92a69022,0x8110cf2c8a9a408876b7,0xbdba2a6902219ed91534,0xa9a408867b64d4d20442,0x221bc585604c910af2e9,0xf76551324423ebb2a899,0x44c910adae5aa2648847,0x423ebb6a8992218fd935,0xe8b2a648856f72595324,0x992219edc1654c910a7e,0x63f74595324431e3a2ca,0xa654c9108fee8b2a6488,0x24423ebb4ca992215b5c,0x7ee8b1aa48856f7254d5,0xc7a92211f5d36354910a,0xb62007a1502e0023fba2,0x364a11a43106400e2370,0xbe681926317e5e16a531,0x16821fa7b1e6781d2711,0x669825a9323e8c22a872,0xc19cc144090805739216,0x7381801800a090605101,0x300242048144070605,0x8202041810904000241d],#[0x3481002410805020c200,0xc1d2040d221200c0810,0x404000074810204000,0x41010204]]
def g213H5 := limbs80 #[#[0x8000482242d520012002,0xc14f040e33182f831c33,0x14e0079e3c86b500da1,0x38920000c30355380000,0xcc0002992826fac32019,0x3c25237de40000301a47,0x58e100000001c8111823,0xc0004c8ca0a50614000,0x19787c3d868000101706,0x80000000000000060ca8,0x4941000000021b1,0x3d7030c7011a4b70f400,0xa01c8063b128,0x29e3a0200000000,0x31860240001804749400,0x180555c00002cc68000a,0x1c7218030001a920000,0xd00000ca0724720e600,0xe18480100008,0x606050100000000]]
def g213D6 := limbs80 #[#[0xfc4c520443e12148110,0x10ded4d2044379534811,0x9109fd8d524427d654c9,0x8110fe50d204427d63d4,0x4c910fe58132443f9534,0x54c910dfd51324437d54,0x5354910df995324437d6,0xd6354910bfd8d524437d,0x40600dc00dfd8d524437,0xf1935a94847d0436cb22,0x414795e43886067e5de6,0x12199d20a2870d03a732,0x333a414412202b3c3486,0x5d30e0662d3a58700414,0x4467083058228466143a,0x14288a42836114488241,0x2520ca5214144294a0c0,0x7c019989809920e90215,0x1c305662346610]]
def g213H6 := limbs80 #[#[0xe0080000a00220428a8a,0x6000a1836c06199004,0x400364127ccd051000,0x1200000321f808a0000a,0x800002343d8034000180,0xcf8a20a033c0082364e1,0xc2cc09f001c1389b732a,0x561e8a4f0ae185a01010,0xa001f322a4c9e0000d0c,0x1c1e0002005c499103c8,0x560184005d044d1e288,0x401de30ab0889800640,0x8717c044410cd007f8c0,0x11520000041a21011e,0x1b00c80001c303c34800,0x1002800014d0cc02,0x1440006c3c82b232190c,0x4c83a0000000001007d0,0x1860000000000e024480,0x4851ca31da230097e686,0x1aa02011c1800002016e,0x2068d53c599a380001e0,0x160d7648380000402,0x23dcd14730c13e0a0238,0xebb418000000001485e6,0x3801c00012004b00,0x7c030249872bc1ac0000,0x10f02a,0x9c020478a90e006d2800,0x72c0001e00cc1c04802,0xad9a2e8318001466474,0xe30e51e1c41356c1c30],#[0xa01e100de81044e22c19,0x317a024c012ec8734013]]
def g213D7 := limbs80 #[#[0x7f52442faa4887e48110,0x3015007f54910fe99221,0x94301030ba6694235a3f,0xa5011a6690a20e30ba66,0x38da6690a3c8a142a70,0x4]]
def g213H7 := limbs80 #[#[0x1061708a080,0x80800000000000000000,0x82470134006181200007,0x6400000000000000007,0x9e080001001f81878003,0x80080002005901180000,0x549c1800051a440710,0x101130c0f041d8172,0x12e3210000000008028,0xbc5800000000bc680000,0xa408000000000006018b,0x3c650350000000068088,0x6100000000000000006,0x6426780480005,0x80300000000000008218,0x0,0x7198618000000000000,0x1a180004006d81400000,0x6080000000000000006,0x80100005007abc480006,0x69c10000600748179,0x10410,0x50038,0x73410000000000000,0x3c500000000000000000,0x1ca14,0x9e100000000000000000,0x5583c184a8211,0x0,0x0,0x1a100000000000000000,0x31c479c3e810e0040],#[0x584420438,0x28358000000000000,0x707098740,0x403bc2480000,0x100265448]]
def g213D8 (j : Nat) := if j=0 then 0x2d2720806fd10 else 0
def g213H8 := limbs80 #[#[0x50403,0xc0000000000210f00000,0x20008140000000003129,0xe2,0xd01000000321,0xb0000000000000000000,0x60,0x206e0e030000006d0000,0xc1b000f11a,0xf02000000b2400]]
def g213D9 (j : Nat) := if j=0 then 0x219080bf else 0
def g213H9 := limbs80 #[#[0x9000000318003895808,0xb8f40600000000000785,0x1da5790a]]
def g213L : Nat → Packing
  | 3 => (2,6,4,0,0,5,0,g213D3)
  | 4 => (14,5,4,0,0,7,0,g213D4)
  | 5 => (38,4,4,0,0,10,0,g213D5)
  | 6 => (18,3,4,0,0,10,0,g213D6)
  | 7 => (5,2,4,0,0,8,0,g213D7)
  | 8 => (1,1,4,0,0,0,0,g213D8)
  | 9 => (1,0,4,0,0,0,0,g213D9)
  | _ => emptyPacking
def g213I : Nat → Nat → Option (Nat × Nat)
  | 4 => lookupWord 1 29 0 12 1 7 g213H4
  | 5 => lookupWord 16 101 4 15 4 7 g213H5
  | 6 => lookupWord 30 149 7 17 6 7 g213H6
  | 7 => lookupWord 17 179 3 16 5 7 g213H7
  | 8 => lookupWord 4 67 2 12 3 5 g213H8
  | 9 => lookupWord 2 17 2 11 0 7 g213H9
  | _ => fun _ => none
def g213 : Forest := ⟨213,9,fun i => g213Y[i]?.getD (0,0),g213C,g213A,g213L,g213I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g213P3_0 : block g213 3 0 2=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g213B3 : block g213 3 0 2=true := g213P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g213P4_0 : block g213 4 0 14=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g213B4 : block g213 4 0 14=true := g213P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g213P5_0 : block g213 5 0 4=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g213P5_4 : block g213 5 4 34=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g213B5 : block g213 5 0 38=true := (@block_merge g213 5 0 4 34 g213P5_0 g213P5_4)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g213P6_0 : block g213 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g213P6_1 : block g213 6 1 6=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g213P6_7 : block g213 6 7 11=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g213B6 : block g213 6 0 18=true := (@block_merge g213 6 0 1 17 g213P6_0 (@block_merge g213 6 1 6 11 g213P6_1 g213P6_7))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g213P7_0 : block g213 7 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g213P7_3 : block g213 7 3 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g213B7 : block g213 7 0 5=true := (@block_merge g213 7 0 3 2 g213P7_0 g213P7_3)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g213P8_0 : block g213 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g213B8 : block g213 8 0 1=true := g213P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g213P9_0 : block g213 9 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g213B9 : block g213 9 0 1=true := g213P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g213T : checkedTables g213 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g213 0 0 0 = true)
  · exact (rfl : block g213 1 0 0 = true)
  · exact (rfl : block g213 2 0 0 = true)
  · exact g213B3
  · exact g213B4
  · exact g213B5
  · exact g213B6
  · exact g213B7
  · exact g213B8
  · exact g213B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g213G : graphValid g213 (boundsBefore K151) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low213 : Lower true (varsX 213) (graphGoal 213) 10 := lower_forest (g:=g213) (i:=0) (hints:=2) (before_sound K151 V151) g213G g213T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K213 := extendKnown K151 10 [(213,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V213 : Known true K213 := extend_ok (m:=213) V151 low213 (by decide +kernel)
def g63Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffffffc1ffffc92d38,0x9940f740000007fc01ff])),(BitVec.ofNat 152 (word80 [0x80a200844110082930,0x8000f708a45229148a45]))),((BitVec.ofNat 152 (word80 [0xffffffff81a52a0,0xabb8d8801ff00003fe00])),(BitVec.ofNat 152 (word80 [0x12c0450008209a50a0,0x2b1090026130984c2613]))),((BitVec.ofNat 152 (word80 [0xfff00001ffffefe183,0x5e2102c0000ff80001ff])),(BitVec.ofNat 152 (word80 [0x30416088240270081,0x5a2100d148a45229148a]))),((BitVec.ofNat 152 (word80 [0xfffffffe0000209965,0x726e4d3fe0000003fe00])),(BitVec.ofNat 152 (word80 [0x240098001381208141,0x106c4d0582c160b0582c]))),((BitVec.ofNat 152 (word80 [0x24d69a,0x5573c00000ffffc0000])),(BitVec.ofNat 152 (word80 [0x3808e0111c0200d60a,0x5560826130984c26130]))),((BitVec.ofNat 152 (word80 [0x132a5d,0xc49781bffff000000000])),(BitVec.ofNat 152 (word80 [0xc00f0021e004012a1c,0xc48300b81c0e070381c0]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g63C : List ColumnInfo := [(0,1,42,20,6),(0,2,21,40,6),(0,4,42,17,6),(0,8,21,34,6),(0,16,42,5,6),(1,0,62,0,6),(2,0,61,0,6),(4,0,59,0,6),(8,0,55,0,6),(16,0,47,0,6)]
def g63A : List (List Nat) := [[],[83],[66],[66,83],[49],[49,81],[49,66],[49,66,81],[81,49],[81],[81,66,49],[81,66],[16,50,84],[16,50,66,82],[16,82,50,67],[16,82,67],[16,32,48,84],[16,32,48,64,80],[16,32,80,48,67],[16,32,80,67],[16,64,50,32,82],[16,64,50,80],[16,64,82,48],[16,64,82,50,48],[32],[32,83],[32,64],[32,64,83],[32,49],[32,49,81],[32,49,64],[32,49,64,81],[32,81,49],[32,81],[32,81,64,49],[32,81,64],[48,16,33,84],[48,16,33,66,82],[48,16,82,33,65],[48,16,82,65],[48,33,84],[48,33,64,80],[48,33,81,65],[48,33,81,64,16],[48,65,33,82],[48,65,33,32,80],[48,65,82],[48,65,82,32],[64,32],[64,32,83],[64],[64,83],[64,49,32],[64,49,32,81],[64,49],[64,49,81],[64,81,32,49],[64,81,32],[64,81,49],[64,81],[80,16,33,50,67],[80,16,33,67],[80,16,50,65],[80,16,50,66,33],[80,33,48,67],[80,33,67],[80,33,49,16,65],[80,33,49,65],[80,65,33,48,50],[80,65,33,50],[80,65,50,32],[80,65,50]]
def g63D8 (j : Nat) := if j=0 then 0x94837261502bf else 0
def g63L : Nat → Packing
  | 8 => (1,0,4,0,0,0,0,g63D8)
  | _ => emptyPacking
def g63I (_ _ : Nat) : Option (Nat × Nat) := none
def g63 : Forest := ⟨63,8,fun i => g63Y[i]?.getD (0,0),g63C,g63A,g63L,g63I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P8_0 : block g63 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g63B8 : block g63 8 0 1=true := g63P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63T : checkedTables g63 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g63 0 0 0 = true)
  · exact (rfl : block g63 1 0 0 = true)
  · exact (rfl : block g63 2 0 0 = true)
  · exact (rfl : block g63 3 0 0 = true)
  · exact (rfl : block g63 4 0 0 = true)
  · exact (rfl : block g63 5 0 0 = true)
  · exact (rfl : block g63 6 0 0 = true)
  · exact (rfl : block g63 7 0 0 = true)
  · exact g63B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63G : graphValid g63 (boundsBefore K213) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low63 : Lower true (varsX 63) (graphGoal 63) 9 := lower_forest (g:=g63) (i:=0) (hints:=1052722) (before_sound K213 V213) g63G g63T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K63 := extendKnown K213 9 [(63,[]),(111,[100]),(123,[66,98]),(126,[16,32,48,64,80,96])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V63 : Known true K63 := extend_ok (m:=63) V213 low63 (by decide +kernel)
def g95Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x7fffffe0ffffd80a20,0xb359cf0000ff00ff00ff])),(BitVec.ofNat 152 (word80 [0x2800420110180200,0x8149c805050505050505]))),((BitVec.ofNat 152 (word80 [0x8003fffffff80a51a1,0xdee5700000000000ff00])),(BitVec.ofNat 152 (word80 [0x24b1228048208a51a1,0xde444053535353535353]))),((BitVec.ofNat 152 (word80 [0xfffc0000ffffefe3ba,0x24800900ff00ff0000ff])),(BitVec.ofNat 152 (word80 [0xc00b040240262130,0x2480010a0a0a0a0a0a0a]))),((BitVec.ofNat 152 (word80 [0xffffffff0000209259,0x65fb340000000000ff00])),(BitVec.ofNat 152 (word80 [0x49024c009381208258,0x21bb34acacacacacacac]))),((BitVec.ofNat 152 (word80 [0x24dd46,0xb16d0ff0000ffff0000])),(BitVec.ofNat 152 (word80 [0xe0070081c0200d806,0x2161030303030303030]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1324dd,0x980e26ffffff00000000])),(BitVec.ofNat 152 (word80 [0x70038010e0040104c9,0x180026c0c0c0c0c0c0c0]))),(0x0,0x0),(0x0,0x0)]
def g95C : List ColumnInfo := [(0,2,85,8,8)]
def g95A : List (List Nat) := [[],[100],[66],[66,98],[98,66],[98],[49],[49,100],[49,66],[49,66,98],[49,98,66],[49,98],[32],[32,100],[32,64],[32,64,96],[32,96,64],[32,96],[32,49],[32,49,100],[32,49,64],[32,49,64,96],[32,49,96,64],[32,49,96],[64,32],[64,32,98],[64],[64,96],[64,98],[64,98,32],[64,49,32],[64,49,32,98],[64,49],[64,49,96],[64,49,98],[64,49,98,32],[96,32,66],[96,32],[96,64],[96],[96,66,32],[96,66],[96,49,32,66],[96,49,32],[96,49,64],[96,49],[96,49,66,32],[96,49,66]]
def g95D8 (j : Nat) := if j=0 then 0x7f else 0
def g95L : Nat → Packing
  | 8 => (1,0,1,0,0,0,0,g95D8)
  | _ => emptyPacking
def g95I (_ _ : Nat) : Option (Nat × Nat) := none
def g95 : Forest := ⟨95,8,fun i => g95Y[i]?.getD (0,0),g95C,g95A,g95L,g95I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P8_0 : block g95 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g95B8 : block g95 8 0 1=true := g95P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95T : checkedTables g95 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g95 0 0 0 = true)
  · exact (rfl : block g95 1 0 0 = true)
  · exact (rfl : block g95 2 0 0 = true)
  · exact (rfl : block g95 3 0 0 = true)
  · exact (rfl : block g95 4 0 0 = true)
  · exact (rfl : block g95 5 0 0 = true)
  · exact (rfl : block g95 6 0 0 = true)
  · exact (rfl : block g95 7 0 0 = true)
  · exact g95B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95G : graphValid g95 (boundsBefore K63) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low95 : Lower true (varsX 95) (graphGoal 95) 9 := lower_forest (g:=g95) (i:=0) (hints:=4146) (before_sound K63 V63) g95G g95T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K95 := extendKnown K63 9 [(95,[]),(119,[83]),(125,[49,81]),(189,[49,81,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V95 : Known true K95 := extend_ok (m:=95) V63 low95 (by decide +kernel)
def g159Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x1fffffe0ffff4b2296,0xc00000fe03f80fec0c6f])),(BitVec.ofNat 152 (word80 [0x4014004202204a0204,0xc142850a142850a4042a]))),((BitVec.ofNat 152 (word80 [0xe001fffffff05cb07d,0xa0007f000007f0003218])),(BitVec.ofNat 152 (word80 [0x8258228010415ca075,0xa4c993264c9932601000]))),((BitVec.ofNat 152 (word80 [0xfffe0000fffff32c21,0x203f8001fc000ff0c197])),(BitVec.ofNat 152 (word80 [0x600b040480812821,0x22850a142850a1404094]))),((BitVec.ofNat 152 (word80 [0xffffffff0000a7dfae,0x400000000007f0000218])),(BitVec.ofNat 152 (word80 [0x14814c00a702a35f8a,0x5b366cd9b366cd800218]))),((BitVec.ofNat 152 (word80 [0xb44153,0xdfc00001fff8001f03e0])),(BitVec.ofNat 152 (word80 [0x70070083804340152,0xc183060c18306010340]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x85fc0,0x3ffffffe0000001ffc00])),(BitVec.ofNat 152 (word80 [0x18018010c008005480,0x102040810204081aa800]))),(0x0,0x0)]
def g159C : List ColumnInfo := [(0,8,149,2,8),(8,0,151,0,8),(1,0,158,0,7),(2,8,149,0,7),(4,0,155,0,7),(16,0,143,0,7),(128,0,31,0,6),(5,0,154,0,4),(17,0,142,0,4),(20,0,139,0,4)]
def g159A : List (List Nat) := [[],[66],[32],[32,64],[64,32],[64]]
def g159D5 := limbs80 #[#[0x50940483aa5954250120,0x483ca5515250120eab65,0x5915254120d697554940,0x54120e6b64549504839a,0xb6982d51504835add152,0x5d9544838ed935454120,0xc032e1d370595208fb80,0xa0cc8d01d345ca0d141,0x202000]]
def g159D6 := limbs80 #[#[0x3b4a92a0907a94250120,0xfd2a4a02412fdd16548,0x837db2a80906f9655012,0x20fd6e4a8241fa549504,0x483bdaa2a09077954541,0x120df6c8a8241be59150,0x44833eb2aa8905fb7454,0x51209feecaa2413f5d95,0x544835fb26a8905f970d,0x591209faedaa2419f597,0x1654827ebaec8904ff75,0x59520b7ee8b2a417edc,0xd1654835e3a2ca906fb7,0x70995209fee8b2a41afd,0x5d3654827ebb4ca905f9,0xb7054950bf6e0a92a13f,0xfd93525433fb22a4a877,0xbf7458950afae9a92a19,0x3fdd162d427eba6c4a85,0x78a8431e4d85f258a401,0x5610fb7aba1b6d564309,0x75a2b74ea0cee5d288dc,0xee46ef5da1cde3b037bb,0x8178f049085f076ba9c,0x82141100f1e010649ce1,0x810000808205c7806102,0x80101c4080141c80801,0x400e0e2043820700400a,0x8604002005041020050,0xa8]]
def g159H6 := limbs80 #[#[0x28018000000000000032,0x200000f,0x0,0x52300000,0x84001ea800522b500000,0x66200000000000003d3e,0xe0000000000000000000,0xa0,0x160c000000000,0x80000000000000000000,0x3c1000000e5d02,0x8004600000001,0x814003e4c110,0x8003b300000000000000,0x89,0x4260000,0x41200000000000000000,0x62900000000000,0x8400000]]
def g159D7 := limbs80 #[#[0xf59120fe54120fe50120,0xd9520bf59520bfd9120b,0x8950dfd4950df54950bf,0x120ff55120bf58b50bfd,0x20ff59520ff59120ffd5,0xff58950ff54950ff995,0x90ba2585a0c000ffd895,0xc9ce691865a144481023,0xb1c159079aa528ba107,0x648b3242c461f3906207,0x3186c55cc7149207c465,0x522105c731c4c4792217,0x54d62cc51e2cd41851b3,0x61c6185887105506cc4c,0x88710920789514589140,0xf1c065221624501c4195,0x60940c75540]]
def g159H7 := limbs80 #[#[0x2d0210200b00c50040,0x92280400000079480000,0xe060003078000ac40002,0x3124000,0x1689241b024000000285,0x38000024000c42000000,0xb4c0000000e4510,0x61c000333c0,0x12200000000000,0x6854,0x3406000,0x101,0x888000000000000,0xd01098000020e14f0400,0x837c0200000000000014,0x18989860000004,0x3042,0x1e9f0000000000000000,0x110000000,0x821f2170452a100,0x605f836000e3100000,0xf23d6680000000000,0xa160000000,0x384bec8000000000049c,0x414c8a000180,0x900000000000000001ca,0xd0ef240517c0cc0580,0x13389be0e000000100a0,0x206b9a66117308,0x8001c4721fd0c000092c,0x140ff0c]]
def g159D8 := limbs80 #[#[0xc79aa407fd43faa1fd20,0x98d13568298d131ea414,0x1ad046]]
def g159H8 := limbs80 #[#[0x1241028405,0x30c00000000000,0x94174020b000000000,0xa26000e09d2f0000001,0xe6b00000000000,0x311910d47000,0x1000000000000d030000,0x10a00000000000000043,0x90e000,0xde0fc6a000e30508b040,0xa27628000c21b06729d0,0xd01000f05000b87000,0x1070]]
def g159D9 (j : Nat) := if j=0 then 0x1542317f else 0
def g159H9 := limbs80 #[#[0xc2000000000007a80000,0x64000012400840000201,0x104000078db2]]
def g159L : Nat → Packing
  | 5 => (11,4,4,0,0,7,0,g159D5)
  | 6 => (39,3,4,0,0,9,0,g159D6)
  | 7 => (18,2,4,0,0,10,0,g159D7)
  | 8 => (3,1,4,0,0,7,0,g159D8)
  | 9 => (1,0,4,0,0,0,0,g159D9)
  | _ => emptyPacking
def g159I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 6 139 3 11 4 3 g159H6
  | 7 => lookupWord 18 181 4 13 6 3 g159H7
  | 8 => lookupWord 8 83 2 12 5 3 g159H8
  | 9 => lookupWord 2 23 0 9 2 3 g159H9
  | _ => fun _ => none
def g159 : Forest := ⟨159,9,fun i => g159Y[i]?.getD (0,0),g159C,g159A,g159L,g159I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g159P5_0 : block g159 5 0 11=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g159B5 : block g159 5 0 11=true := g159P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g159P6_0 : block g159 6 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g159P6_3 : block g159 6 3 36=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g159B6 : block g159 6 0 39=true := (@block_merge g159 6 0 3 36 g159P6_0 g159P6_3)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g159P7_0 : block g159 7 0 10=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g159P7_10 : block g159 7 10 8=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g159B7 : block g159 7 0 18=true := (@block_merge g159 7 0 10 8 g159P7_0 g159P7_10)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g159P8_0 : block g159 8 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g159B8 : block g159 8 0 3=true := g159P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g159P9_0 : block g159 9 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g159B9 : block g159 9 0 1=true := g159P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g159T : checkedTables g159 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g159 0 0 0 = true)
  · exact (rfl : block g159 1 0 0 = true)
  · exact (rfl : block g159 2 0 0 = true)
  · exact (rfl : block g159 3 0 0 = true)
  · exact (rfl : block g159 4 0 0 = true)
  · exact g159B5
  · exact g159B6
  · exact g159B7
  · exact g159B8
  · exact g159B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g159G : graphValid g159 (boundsBefore K95) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low159 : Lower true (varsX 159) (graphGoal 159) 10 := lower_forest (g:=g159) (i:=0) (hints:=4146) (before_sound K95 V95) g159G g159T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K159 := extendKnown K95 10 [(159,[]),(183,[83]),(207,[100,84]),(219,[66,98,82]),(222,[32,64,96,80])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V159 : Known true K159 := extend_ok (m:=159) V95 low159 (by decide +kernel)
def g175Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x7fffffe0ffffdc322e,0x22495f0000ff000000ff])),(BitVec.ofNat 152 (word80 [0x428204209101c3208,0x2495815151515151515]))),((BitVec.ofNat 152 (word80 [0x8003fffffff8086da1,0xd6e1c000ff0000ffff00])),(BitVec.ofNat 152 (word80 [0xb0028000208821a0,0xc440c003030303030303]))),((BitVec.ofNat 152 (word80 [0xfffc0000ffffefc3b2,0x2c8429ff0000000000ff])),(BitVec.ofNat 152 (word80 [0x8c04b04124021c1a2,0x2484212a2a2a2a2a2a2a]))),((BitVec.ofNat 152 (word80 [0xffffffff0000209251,0x65fb34000000ff00ff00])),(BitVec.ofNat 152 (word80 [0x21010c004381201211,0x21ab244c4c4c4c4c4c4c]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x24dd4e,0xb16d0000000ffff0000])),(BitVec.ofNat 152 (word80 [0x4e0270089c0204cc4e,0xa1410b0b0b0b0b0b0b0]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1324dd,0x980e26ffffff00000000])),(BitVec.ofNat 152 (word80 [0x70038010e004020455,0x180206c0c0c0c0c0c0c0]))),(0x0,0x0)]
def g175C : List ColumnInfo := [(1,0,174,0,7),(4,0,171,0,7),(8,0,167,0,7),(32,0,143,0,7),(0,1,42,132,6),(0,4,42,129,6),(0,8,133,34,6),(0,32,133,10,6),(2,0,173,0,6),(128,0,47,0,6),(1,4,42,128,5),(2,8,133,32,5),(2,32,133,8,5),(5,0,170,0,5),(8,32,133,2,5),(128,1,42,4,5),(128,4,42,1,5),(10,0,133,0,4),(129,0,42,0,4),(129,4,42,0,4)]
def g175A : List (List Nat) := [[],[83],[32],[32,83],[48,113,82],[48,113,82,32],[80,113,50,32],[80,113,50]]
def g175D5 (j : Nat) := if j=0 then 0x32bdd3624c550 else 0
def g175D6 := limbs80 #[#[0x377b1262a85bf744c520,0x9faed18ea1bbd8a3154,0xa30700189c38]]
def g175H6 (j : Nat) := if j=0 then 0xb else 0
def g175D7 := limbs80 #[#[0xe58051bbd8950bb58b10,0x59651bf58750ddd4651b,0xd20ff8c520ff4c520bf,0x750ff8c550ff4c550ff5,0x369707a2f8f43600ff8c,0xe205163c3bed8a73177e,0xf1618c08245898f1051,0x2c40e18182c3284c0206,0x1a10347006841080c1e,0xc886470420a8a00d0824,0xd00207049040]]
def g175H7 := limbs80 #[#[0x62002440ba070f0f8,0x2324]]
def g175D8 := limbs80 #[#[0xd50fe987f483fe21fd10,0x1fe51fea8ff147fea1f,0x1ee93e8431944782a0c0,0x4a04c3cb14388c84a2cf,0x50ce84a3cb1808e234f1,0x2388a84910a0638844c,0xc814308004c3cb2081c6,0x40c3cb1a38a181030f2,0x6]]
def g175H8 := limbs80 #[#[0x18c800e2ed093188,0x12256360a0,0xe25247b1640af12ea000,0x33160080000000070181,0x100e11288001a6a4,0x18170d800000003808]]
def g175D9 (j : Nat) := if j=0 then 0x1882013f else 0
def g175H9 := limbs80 #[#[0x141590000000000005,0x3c498a000000,0x600004c26cbe0c00393,0x3998004c20000000031,0xb49d20000000000,0x243560000000,0x1403d0400540a0a09400,0x103800000000006a,0x40800000408000000000,0x1a3001]]
def g175L : Nat → Packing
  | 5 => (1,4,5,0,0,0,0,g175D5)
  | 6 => (4,3,5,0,0,6,0,g175D6)
  | 7 => (12,2,5,0,0,9,0,g175D7)
  | 8 => (9,1,5,0,0,9,0,g175D8)
  | 9 => (1,0,5,0,0,0,0,g175D9)
  | _ => emptyPacking
def g175I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 2 0 4 0 0 g175H6
  | 7 => lookupWord 2 11 3 9 2 3 g175H7
  | 8 => lookupWord 6 41 3 11 4 3 g175H8
  | 9 => lookupWord 6 67 1 11 4 3 g175H9
  | _ => fun _ => none
def g175 : Forest := ⟨175,9,fun i => g175Y[i]?.getD (0,0),g175C,g175A,g175L,g175I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175P5_0 : block g175 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g175B5 : block g175 5 0 1=true := g175P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175P6_0 : block g175 6 0 4=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g175B6 : block g175 6 0 4=true := g175P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175P7_0 : block g175 7 0 4=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175P7_4 : block g175 7 4 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175P7_6 : block g175 7 6 6=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g175B7 : block g175 7 0 12=true := (@block_merge g175 7 0 4 8 g175P7_0 (@block_merge g175 7 4 2 6 g175P7_4 g175P7_6))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175P8_0 : block g175 8 0 9=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g175B8 : block g175 8 0 9=true := g175P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175P9_0 : block g175 9 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g175B9 : block g175 9 0 1=true := g175P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175T : checkedTables g175 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g175 0 0 0 = true)
  · exact (rfl : block g175 1 0 0 = true)
  · exact (rfl : block g175 2 0 0 = true)
  · exact (rfl : block g175 3 0 0 = true)
  · exact (rfl : block g175 4 0 0 = true)
  · exact g175B5
  · exact g175B6
  · exact g175B7
  · exact g175B8
  · exact g175B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175G : graphValid g175 (boundsBefore K159) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low175 : Lower true (varsX 175) (graphGoal 175) 10 := lower_forest (g:=g175) (i:=0) (hints:=1052722) (before_sound K159 V159) g175G g175T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K175 := extendKnown K159 10 [(175,[]),(187,[66]),(190,[32,64])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V175 : Known true K175 := extend_ok (m:=175) V159 low175 (by decide +kernel)
def g215Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfffc01ffc3ffffffe6,0xa43b0800007c00f83ff])),(BitVec.ofNat 152 (word80 [0x28140288040020c2,0xa031004210842108421]))),((BitVec.ofNat 152 (word80 [0x1ffffe0003fe1ff045,0x3d4b4e8000f800000000])),(BitVec.ofNat 152 (word80 [0x4ab118ab11284a4245,0x3d4b4ebdef7bdef7bdef]))),((BitVec.ofNat 152 (word80 [0x1ffffffffc001fff38,0xf46918001f0001f07c1f])),(BitVec.ofNat 152 (word80 [0x80c0200c0030808038,0x54400808421084210842]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1fffffffffffe00010,0xaa846f83e0003e007fe0])),(BitVec.ofNat 152 (word80 [0x30040300040030400,0xa0046390842108421084]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xe0000000000000000e,0x11ba877c00003fff8000])),(BitVec.ofNat 152 (word80 [0xc0180c021810c0804,0x1b88421084210842108]))),((BitVec.ofNat 152 (word80 [0xc1,0x4514407fffffc0000000])),(BitVec.ofNat 152 (word80 [0x100201000200100000,0x42108421084210]))),(0x0,0x0)]
def g215C : List ColumnInfo := [(2,0,213,0,10)]
def g215A : List (List Nat) := [[],[100],[66],[66,98],[98,66],[98],[32],[32,100],[32,64],[32,64,96],[32,96,64],[32,96],[64,32],[64,32,98],[64],[64,96],[64,98],[64,98,32],[96,32,66],[96,32],[96,64],[96],[96,66,32],[96,66]]
def g215D10 (j : Nat) := if j=0 then 0x7f else 0
def g215L : Nat → Packing
  | 10 => (1,0,1,0,0,0,0,g215D10)
  | _ => emptyPacking
def g215I (_ _ : Nat) : Option (Nat × Nat) := none
def g215 : Forest := ⟨215,10,fun i => g215Y[i]?.getD (0,0),g215C,g215A,g215L,g215I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215P10_0 : block g215 10 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g215B10 : block g215 10 0 1=true := g215P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215T : checkedTables g215 10 := by
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
  · exact (rfl : block g215 8 0 0 = true)
  · exact (rfl : block g215 9 0 0 = true)
  · exact g215B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215G : graphValid g215 (boundsBefore K175) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low215 : Lower true (varsX 215) (graphGoal 215) 11 := lower_forest (g:=g215) (i:=0) (hints:=114) (before_sound K175 V175) g215G g215T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K215 := extendKnown K175 11 [(215,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V215 : Known true K215 := extend_ok (m:=215) V175 low215 (by decide +kernel)
def g127Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x2f314954687000000f,0xff000000000fff000fff])),(BitVec.ofNat 152 (word80 [0x271140542060450450,0x45045045045045045045]))),((BitVec.ofNat 152 (word80 [0x836645d51480000000,0xfff000000fff000])),(BitVec.ofNat 152 (word80 [0x836205951402132132,0x13213213213213213213]))),((BitVec.ofNat 152 (word80 [0x1030a6b9389000fff0,0xfff000000fff])),(BitVec.ofNat 152 (word80 [0x102086a918908a08a0,0x8a08a08a08a08a08a08a]))),((BitVec.ofNat 152 (word80 [0xf4cc30e0e0c0000000,0xfff000000000fff000])),(BitVec.ofNat 152 (word80 [0x74842060e0842c42c4,0x2c42c42c42c42c42c42c]))),((BitVec.ofNat 152 (word80 [0xe805392e972fff0000,0xffffff000000])),(BitVec.ofNat 152 (word80 [0x880439028401301301,0x30130130130130130130]))),((BitVec.ofNat 152 (word80 [0x18adc0a0570000000,0xffffff000000000000])),(BitVec.ofNat 152 (word80 [0x8d80a0179c09c09,0xc09c09c09c09c09c09c0]))),((BitVec.ofNat 152 (word80 [0x56c88203c30fffffff,0xff000000000000000000])),(BitVec.ofNat 152 (word80 [0x40c80000430e00e00e,0xe00e00e00e00e00e00]))),(0x0,0x0),(0x0,0x0)]
def g127C : List ColumnInfo := [(0,2,85,40,9),(0,8,85,34,9),(0,32,85,10,9),(1,0,126,0,9),(2,0,125,0,9),(4,0,123,0,9),(8,0,119,0,9),(16,0,111,0,9),(32,0,95,0,9),(64,0,63,0,9),(0,1,42,84,7),(0,4,42,81,7),(4,16,42,65,6),(16,1,42,68,6),(16,64,42,5,6),(17,0,110,0,6),(64,1,42,20,6),(64,16,42,5,6),(5,64,42,16,5),(17,64,42,4,5),(20,64,42,1,5)]
def g127A : List (List Nat) := [[],[100],[83],[83,100],[66],[66,98],[66,83],[66,83,98],[98,66],[98],[98,83,66],[98,83],[49],[49,100],[49,81],[49,81,100],[49,66],[49,66,98],[49,66,81],[49,66,81,98],[49,98,66],[49,98],[49,98,81,66],[49,98,81],[81,49],[81,49,100],[81],[81,100],[81,66,49],[81,66,49,98],[81,66],[81,66,98],[81,98,49,66],[81,98,49],[81,98,66],[81,98],[32],[32,100],[32,83],[32,83,100],[32,64],[32,64,96],[32,64,83],[32,64,83,96],[32,96,64],[32,96],[32,96,83,64],[32,96,83],[32,49],[32,49,100],[32,49,81],[32,49,81,100],[32,49,64],[32,49,64,96],[32,49,64,81],[32,49,64,81,96],[32,49,96,64],[32,49,96],[32,49,96,81,64],[32,49,96,81],[32,81,49],[32,81,49,100],[32,81],[32,81,100],[32,81,64,49],[32,81,64,49,96],[32,81,64],[32,81,64,96],[32,81,96,49,64],[32,81,96,49],[32,81,96,64],[32,81,96],[64,32],[64,32,98],[64,32,83],[64,32,83,98],[64],[64,96],[64,83],[64,83,96],[64,98],[64,98,32],[64,98,83],[64,98,83,32],[64,49,32],[64,49,32,98],[64,49,32,81],[64,49,32,81,98],[64,49],[64,49,96],[64,49,81],[64,49,81,96],[64,49,98],[64,49,98,32],[64,49,98,81],[64,49,98,81,32],[64,81,32,49],[64,81,32,49,98],[64,81,32],[64,81,32,98],[64,81,49],[64,81,49,96],[64,81],[64,81,96],[64,81,98,49],[64,81,98,49,32],[64,81,98],[64,81,98,32],[96,32,66],[96,32],[96,32,83,66],[96,32,83],[96,64],[96],[96,83,64],[96,83],[96,66,32],[96,66],[96,66,83,32],[96,66,83],[96,49,32,66],[96,49,32],[96,49,32,81,66],[96,49,32,81],[96,49,64],[96,49],[96,49,81,64],[96,49,81],[96,49,66,32],[96,49,66],[96,49,66,81,32],[96,49,66,81],[96,81,32,49,66],[96,81,32,49],[96,81,32,66],[96,81,32],[96,81,49,64],[96,81,49],[96,81,64],[96,81],[96,81,66,49,32],[96,81,66,49],[96,81,66,32],[96,81,66]]
def g127D8 := limbs80 #[#[0x8ff865d120fa94250120,0x5e603e1e4e04b9022300,0x9b879383a38a9f0f14a0,0x2f]]
def g127D9 := limbs80 #[#[0xd74483fca0241bb58162,0x387c8753700bfee8905f,0xd8b08c20461cd9306246,0xd19b1614f148161f405c,0x8cd8b0c51a4471e24200,0x6]]
def g127H9 (j : Nat) := if j=0 then 0x22 else 0
def g127D10 := limbs80 #[#[0x20fb98bed62fd987f561,0xa224d227aab9c8f003fd,0x9a1a224d2214126840,0x24c9166864809a224c95,0x16188348c2459a1920a2,0xaa67920a26]]
def g127H10 := limbs80 #[#[0x14030000000000800,0x0,0x3660000000000100a00,0x4880,0x40e000b0300010040,0x600400000054a8]]
def g127D11 (j : Nat) := if j=0 then 0x24e519824020457f else 0
def g127H11 := limbs80 #[#[0x11011c030000d64e5107,0xd003c2461124026a13c0]]
def g127L : Nat → Packing
  | 8 => (2,3,5,0,0,7,0,g127D8)
  | 9 => (4,2,5,0,0,8,0,g127D9)
  | 10 => (5,1,5,0,0,8,0,g127D10)
  | 11 => (1,0,5,0,0,0,0,g127D11)
  | _ => emptyPacking
def g127I : Nat → Nat → Option (Nat × Nat)
  | 9 => lookupWord 1 2 0 5 1 0 g127H9
  | 10 => lookupWord 2 37 0 13 2 7 g127H10
  | 11 => lookupWord 2 11 3 14 3 7 g127H11
  | _ => fun _ => none
def g127 : Forest := ⟨127,11,fun i => g127Y[i]?.getD (0,0),g127C,g127A,g127L,g127I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_0 : block g127 8 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
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
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P9_1 : block g127 9 1 3=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B9 : block g127 9 0 4=true := (@block_merge g127 9 0 1 3 g127P9_0 g127P9_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P10_0 : block g127 10 0 4=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P10_4 : block g127 10 4 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B10 : block g127 10 0 5=true := (@block_merge g127 10 0 4 1 g127P10_0 g127P10_4)
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
  · exact g127B8
  · exact g127B9
  · exact g127B10
  · exact g127B11
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127G : graphValid g127 (boundsBefore K215) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low127 : Lower true (varsX 127) (graphGoal 127) 12 := lower_forest (g:=g127) (i:=0) (hints:=1052722) (before_sound K215 V215) g127G g127T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K127 := extendKnown K215 12 [(127,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V127 : Known true K127 := extend_ok (m:=127) V215 low127 (by decide +kernel)
def g191Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x7ff000000007f,0xf00ffe030c697c3378e1])),(BitVec.ofNat 152 (word80 [0x1142284508a1142284,0x51108a0104285c113920]))),((BitVec.ofNat 152 (word80 [0x3ff800001ffc0000,0xff00004109e0e4f9ff2])),(BitVec.ofNat 152 (word80 [0x4c0981302604c0981,0x30702600101c040f08b2]))),((BitVec.ofNat 152 (word80 [0xffc00000000003ff80,0xffe182310b18ce0ed])),(BitVec.ofNat 152 (word80 [0x2284508a1142284508,0xa221140801102084c2cc]))),((BitVec.ofNat 152 (word80 [0xffe0000000,0xff00060c3e001f0ff0e])),(BitVec.ofNat 152 (word80 [0x8b11622c4588b11622,0xc0845820c3e001f0f704]))),((BitVec.ofNat 152 (word80 [0x3ffff,0xf0000180fc00c1ff0012])),(BitVec.ofNat 152 (word80 [0x4c0981302604c09813,0x4c260805000816a0012]))),((BitVec.ofNat 152 (word80 [0xfffffc0000,0x1ff0000fe00001c])),(BitVec.ofNat 152 (word80 [0x702e05c0b81702e05c,0xf0b81df0000fa000008]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffff0000000000,0x1ffffff00000000])),(BitVec.ofNat 152 (word80 [0x80300600c018030060,0x80c0176aac000000400]))),(0x0,0x0)]
def g191C : List ColumnInfo := [(1,0,190,0,10),(4,0,187,0,10),(8,0,183,0,10),(16,0,175,0,10),(32,0,159,0,10),(0,8,149,34,9),(0,32,149,10,9),(2,0,189,0,9),(128,0,63,0,9),(2,8,149,32,8),(2,32,149,8,8),(8,32,149,2,8),(32,8,149,2,8),(40,0,151,0,8),(0,1,42,148,7),(0,2,21,168,7),(0,4,42,145,7),(0,16,42,133,7),(5,0,186,0,7),(9,0,182,0,7),(10,0,149,0,7),(10,32,149,0,7),(12,0,179,0,7),(17,0,174,0,7),(20,0,171,0,7),(24,0,167,0,7),(1,4,42,144,6),(1,8,148,34,6),(1,16,42,132,6),(3,0,188,0,6),(4,1,42,144,6),(4,16,42,129,6),(6,0,185,0,6),(8,2,21,160,6),(16,1,42,132,6),(16,4,42,129,6),(18,0,173,0,6),(128,1,42,20,6),(128,2,21,40,6),(128,4,42,17,6),(128,8,21,34,6),(128,16,42,5,6),(129,0,62,0,6),(130,0,61,0,6),(132,0,59,0,6),(136,0,55,0,6),(5,16,42,128,5),(17,4,42,128,5),(20,1,42,128,5),(21,0,170,0,5),(129,4,42,16,5),(129,16,42,4,5),(132,1,42,16,5),(132,16,42,1,5),(136,2,21,32,5),(144,1,42,4,5),(144,4,42,1,5),(133,0,42,0,4),(133,16,42,0,4),(145,4,42,0,4),(148,1,42,0,4)]
def g191A : List (List Nat) := [[],[83],[66],[66,83],[32],[32,83],[32,64],[32,64,83],[64,32],[64,32,83],[64],[64,83]]
def g191D6 := limbs80 #[#[0x41d4a5db955093150120,0x483a95bb72aa1262a02,0xa8090762b95591624c54,0x3158120e4d30dcaac498,0x1262b0241d1ae5574589,0x1624c560483a35caee8b,0xd16c898ac090726b95e1,0x5774d913158120ccd72a,0xdd832fc2ac898a41d0ee,0x938a4e8176e15314828b,0xa93a44278d981e304806,0x5010400140c1]]
def g191D7 := limbs80 #[#[0x6048372b955093150120,0xdb854c520d9ae55624c5,0xa5d9424c54048293fa45,0x483dab765093150120f6,0x3150120faa591624c540,0x19624c54048376b95589,0x357976e553150120eba6,0x50120d5eddb954c54048,0x428c540483da97650a31,0xa99650a3150120f6add9,0x120faa591628c5404837,0x50940483ae98658a3150,0x7654d4250120f6a5d953,0xfaa5915358940483dab,0x560483ae98654d625012,0x5893158120ddae55624c,0x3add1624c560483ce974,0x483aeb845893158120f,0x13158120ddae57824c56,0x68b644c56048367b9559,0x83cbb74d913158120bba,0x158120d9ee57644c5604,0x7744c56048357b955d13,0x37b95e113158120d5ee5,0x8120dba659628c560483,0x28c560483ce97458a315,0xb8458a3158120f3add16,0x20bba68b648c560483ae,0x8960483cbb74d9231581,0x454d6258120f3a5d1535,0xebae115358960483ceb7,0x60482ee9a2d915358120],#[0x15644c520f2edd36454d,0xf65f855913148387d76e,0x48317f97e15644c520c5,0x644c52097ee819759131,0x1774d913148337b85643,0x387d76e17644c520e4fe,0x4c520c5f65f85d913148,0x85dd13148317f96e1574,0x7ba05db854c520c5f65b,0x520acfe9176e1531482b,0xe153148397ba05db854c,0xa45db854c520e4f29176,0xa5fe9176e153148393f,0x531482b79a09db854c52,0xddb854c520a5f69e76e1,0x6e253905d93148297da4,0x14825fba065d648c520d,0x1768c520c6f66374d923,0x61b945da314835b894e4,0x825fba065d6454d20c6f,0x24c560d6e253905d9534,0x7905893158337b85e416,0x87f85dd1624c560e9ee1,0xc560e1fe1774d8931583,0x45c93158327f85653624,0xf85653724c560ccfe179,0xc5fe17945c931d8317,0x15c2744607b0be164138,0x45189a9192103b06d8ca,0x990aa043d0704d29892c,0x54297522a0137a6949a8,0xb6c68acd1812e657eab9],#[0x1835025f6bd176ae65be,0x2f24645c7a8e918e2944,0x3b673cd69a12fe5749d9,0x2a753da6f49a8ad0f9fd,0x5dc5b7f6baced8cae155,0x2503b03c003baf746e,0x80ec4206100b2684581e,0x307621010a8b83b101d8,0x5b081d8440c26060b0,0xa030f611010b61034068,0x770ae68570ae68570ae6,0xb101a014202b84806e68,0x68004947622c30f6203,0x40a10081b101d880814,0x3612a1080920ea001f81,0x6107b081542b0f612911,0x68570ae685b08142583b,0x85b0b668570ae68570ae,0x20190100c0d4183b0b66,0x2830409020f4407c00,0x830403000f8004c00200,0x4207a202018304c00201,0x5d342e85d34203a10207,0x6c10644032001e8]]
def g191H7 := limbs80 #[#[0x38200c00,0xc1a89000000000000000,0xc00000002,0x0,0x150c00000000000000,0x1921508000000000,0x291e0100029280,0x58400000000000,0x141c000000,0x0,0x180c00000000,0x14000000000000000000,0x280800089c003c,0x3d82c04002c8000,0xc28000002a24c84000,0x0,0x3d1800098c00,0x3c8c000000000000,0x0,0xd24000003c2400000000,0x1]]
def g191D8 := limbs80 #[#[0xb12c0887b85892158110,0x214f897589604439d2e4,0x598750910b74c90ecb02,0x644237f28c3ac48843fe,0x4bb284a02410ff985d87,0x2809076add94250120ed,0xae98658940483d52c8b1,0x6258120e74b16e2b0241,0x839d6e8b12c09073a5d1,0x96c8b0241aeb84589604,0x29072edd36458120b74c,0xb9061d6448237f28c3ec,0x1c560cdc42700bb2411f,0xf528498a809047de6171,0x62a024177b954c540483,0x7ea5096150120fd4a14,0x350940483f528530a809,0x120fd4b1a84a0241fa95,0x72a98ac0907ba5893158,0xb0241ee9628c560482ef,0xba58a6158120f74b12c2,0x8960483dd2c6b12c0907,0xcbfc2ae898a41ee9535,0xdc2a629065fe17744c52,0xa4197f76e15314832fae,0xe51768c520adfca2ec98,0x61482b7f28bb2c29056f,0xdfca2ed30a414ff965d2,0xa2c69056fe517654d20a,0x15bf945d9634829ff2cb,0x5624c560cdfba303b224,0x5834ff0bb1262b069fe1],#[0xc2ae498ec197f85dc931,0x80907fa5893150120cbf,0xfb764c540483bf2ec98a,0x150120ff4b1462a0241d,0x3bf6ed18a809077e5da3,0xac4a02417f9968c54048,0x9077e5d95350120ff4a9,0x624c560483bf6eca9a80,0x8120ff5c1262b0241fe9,0xf6c898ac0907be591315,0x2b0241df9744c560483d,0x6fee113158120efdba26,0x8c560483fd2c518ac090,0x20f7cb2462b0241feb82,0xe918ac0907bed9231581,0x241dfb748c560483bf2,0xe65a3158120dfdc2462b,0x960483fd2a6b12c0905f,0xf7cb22a6b0241fe953e0,0xa9ac0907bed915358120,0x41dfb7454d60483bf2e8,0x15644c520dfdc22a6b02,0x14839faecb2262906dfe,0xfcbac898a415fd975913,0x262905fe643644c520af,0xb7f85d9131483b7ee9b2,0x644c520e7ebb6c898a41,0x836ff0aba2629057f65f,0xb6e898a415ff965d1314,0x2906df5db854c520afec,0xb905d9314836fcedc2a6,0x4c520bdfca2ec98a417f],#[0xb7928bb2629077ee4176,0xec98a41dbf945d931483,0x5fe642764c520affca2,0x4dd931482bfb2f3b2629,0x520e7ebb2c918a415fd9,0xf2eb24629057f65d648c,0x18a417f990d9231482bf,0x3f5db648c520edfba6c9,0x9231482bfb2fb2462907,0xcfec32e918a413fd98d,0xdba4629057fe59748c52,0xa415fd96dd2314833fb0,0xe51768c520bfdc82ed18,0x31483bf720bb462905ef,0xdfca2ed18a41dbc945da,0xb4629057fe51768c520e,0x17f9909da314833fb0cb,0x2768c520afecbced18a4,0x482bfb29bb462904ff66,0xbb2c8a9a419fd86dda31,0xa69057f65d6454d20e7e,0xf990d9153482bff2eb22,0x454d20edfba6c8a9a417,0x2bfb2fb22a69073f5db6,0x6e8a9a415ff965d15348,0x905fee417654d20afecb,0x905d953482f7f28bb2a6,0x4d20ede4a2eca9a41dfb,0xff28bb2a69076fe51765,0xca9a417f9909d953482b,0x57f6537654d20afecbce,0x58931582ff720b1262b0],#[0x60f7dc82c498ac1b7f85,0xe9b1262b073fdd1624c5,0x8ac16fd94d89315839fe,0xfe15724c560bdfca2e49,0x9315836ff0bb9262b06d,0xbfdc82c518ac15fd94dc,0xb1462b06bf619628c560,0xc1cff7458a31583df720,0x53628c560e7fba6c518a,0x1582f7f28b9462b05bf6,0xec36e518ac15fd94dca3,0x2c4b06fe54f8058960cf,0xcff7454d62583df2a7c0,0x53d8960e7fba2a7b12c1,0x8377f08a9ae4b06bf611,0xa2e498ec19fd8454f725,0x5b057fe51728c760affc,0x1e802e00033ff08a9ae,0x95821e074817c04980da,0x603a00d782f40af028e0,0x84fa130847610f84060f,0x6c219885e416b056a14c,0xda214881a1f607781cb0,0xa2b88a8228d89cc25388,0x3168bfa2eb8b8a2d70b1,0x810dd63600d343418c9c,0x60ef43b68ea239a8e323,0xfa43e28f703d58f3c3c,0x8641d90524068ff63f2,0x5e44e90ee43010b04259,0xa489920c47791ba46591,0x4c212e44b292b04a0924],#[0xff93d04e393744d19322,0x3149451c145650a14184,0x958a557154254514f053,0x680599962e58015dc570,0x9e5dc17425c016d25ab9,0xc61218245fd97d25ee17,0x648191063618be621986,0x921a1a67b19be661994e,0xa9afc6b39aaa6a41a6c6,0x1bde6ee9b8c6da1b4e6c,0xcd47299c827179c30703,0xc07671d827579d267409,0x47981e3c78b1e087769d,0x7da9f327bc1ecc7aa1e8,0xe201e7fe9fd67e79f8e,0xca0ce82d209a81da0528,0x20782f1215e84ea11683,0xc20238ae24904887a27c,0x3c4f0f89f081e074904b,0x27c20681d88872478a02,0xe2b43d0789e008e2bc4e,0xad0411e2780200ff13c2,0xc20781d088703fc4f0b8,0xfc4f08904945e2bc4e27,0x7c4f13c224218494500,0x1f13c243a2317c4f0823,0x8ff13c2b2a22b2412280,0x3c2241c343860a42b28e,0x1029f13c228d221426f1,0x4f08908885f13c207ca3,0x7f13c208b81244509bc,0x945f0b4ae07800474992],#[0xe05c30945f13c2d0f810,0x60741e128490885f13c2,0xf8116c440d81c02c5b54,0x981c02ca3317c4b00d0,0x601704890b22c583903b,0xb12c2b2990c02c989490,0x240590c02c7894a40418,0x725cd1c18b1ac5b12c,0xb007252525c670a03a07,0x16d51818241c4805cb70,0xc2312e045b110860700b,0x583981b0b00b28dc00c9,0xb0b82c0a890b0c12422c,0x2bb1ac5b12c3b08330c8,0x5000cec70c8c0968f400,0x82504ac6b16c4b0ec240,0x19c3807c480033724322,0x71a81c01c97347094127,0x8b0f81e0146524970a08,0x46b0d49a485a6297a4a8,0x192e078060e469246a21,0xd1345d54360e46925921,0x90881192342e0780d287,0x44d0b4a24749e0780920,0xb46d16c3e0425d1c608b,0x1744d089192381e03472,0x91f42e0349d34408b46d,0x492346b0f81e0086d0b4,0x408811d1381e034bd0b,0x2688b07801011e078092,0x9e005a4949e02c1a2055,0x46a2149b045b0546f0d4],#[0xec4251030d17b102a0d,0xc240c245ec20ac440c94,0x709cd0f03c04240ec20a,0xc2b34321ac2b35031217,0x3b1100b56c5420540e,0x8b102b101b101b11014,0x4207146c430f8112c405,0x1400304a0e122c2402c5,0x8307212838c3b085b090,0x2444422c2284384a0eb0,0xec043b0b8108a130ec2,0x34470a00716087345048,0x2b342b0acd09c2806007,0x43b0acd0908b0acd0ec,0x30a88a0f80a484b0acde,0xf21b44210050506d108,0x7442042d13800500510,0x4420c2a0f80a22921344,0x5e92e02c31744050050f,0x4050050f44d17550e98a,0x3806482621c3e0192134,0xd1380d1450480ed10801,0x44d57450f44d5428480e,0xc11d145d1083d574513,0x30500513442002053445,0xc83d084d10140143d108,0x1c8621342014211a1c90,0xed08811342e002101440,0x14320f420a48d0824480,0xe0e83e00120384d08210,0x8110b42087450c280840,0x200204643d0821014508],#[0x42061203b42e03451742,0xf42d1450e40ed0b4513,0x854304742d1450e40e2,0xed08801012a0e025144,0x1450c83d08210144048,0x3039450b42084050c0ee,0x6d0805d34420f42d34,0xd0881d343d0b800174d1,0x74d1083d0b4d0f42d342,0xd344d0b4dd14301b4201,0x4d13422034d0c06d0805,0x343d1b42d343d0b80d17,0xd1083d0b45d344d0b45d,0x45d0880d34301b42d174,0x805d34301883d0805d3,0x440a88b07800f44c502d,0x11430d11d1143b044223,0xc10f44d57450f440511d,0x50050e88a02c10e92b0e,0x10500181a03b420f440,0x88d0a4106851410e1168,0xc005d08186b42b043438,0x3d0a2a03838785150f42,0x9cd081e4002d0821014,0x2b0b41b343821c273437,0xac5b343b0acd0ac2b34,0x3d10140143b0805b343b,0x6b0805b344d0821014]]
def g191H8 := limbs80 #[#[0x61819b0000800016c720,0x359872460301000d7881,0x40360c9400920880803b,0x8090694ee63860100122,0x7401a91ea05080106247,0x7f2c0f00cb12aa05b646,0xb04742228f9006b31860,0x581b1021c253d894,0x8aa0c6502a02c8236486,0x8453628b01e4813c0,0xd1144b06b46c821590c8,0x74405d01c583a0001202,0xb317412a8d3c874002b4,0xb017900af615486a814b,0x1d00b800008a4f06ba0a,0x8bdb446c0d81046b0891,0xad091023b12d806a084a,0x47e0f801a720d0000483,0x94600000001d03000002,0x80970480000c42044cd,0x1e098d974025f141444,0xe15be890000741c00,0x3092f930761d8410d218,0x91290e1307548c648,0x815005720c80000a1d00,0xc0002a3d0000801c0248,0x1a105850e01ca206220,0x801e617043e023181d00,0x1217203a80a1,0x84a3034006a070000000,0x8400000269810f820f8,0x200f9b2c411a000141bc],#[0x22809c6168a270000000,0x240f230000001ed107d0,0x425c1120001e42b821d,0x3c02f1140000000,0x1e0000685980b000000,0x4a42120c00004124,0x80000101800000000000,0x833148b68b7425732a50,0x144ac0879436211c0001,0x44211200428390000000,0xbe761ee0ec451800084,0x84454128128f88ba045f,0x1403ec1138422019a01,0xcc4100c343e00]]
def g191D9 := limbs80 #[#[0xee96258120fa94250120,0xff121581109bf845d920,0xff16158110ff22158110,0xff08158110ff26158110,0xef96258110ff38158110,0xdf97258110efb6258110,0xef87658110dfb7258110,0xbfb8048510efb7658110,0xdf57448510ff38048510,0xdf57648510df77448510,0xdf57488510df77648510,0xbf58488510df77488510,0xdf77688510df57688510,0xbfb8058510bf58688510,0xff38058510cff7658510,0xdf77258510df57258510,0xef47658510bf78258510,0xdf57298510ef77658510,0xbf58298510df77298510,0xbf68798510bf58698510,0xcff76d8510bf980d8510,0xbfb80509109fd87d8510,0x9fe87509109fd8750910,0x9fd87589109fc8758910,0x9ff87589109fe8758910,0xbf581d8910bf980d8910,0x9fe87d89109fd87d8910,0x9ff845c910def725c910,0x9fd84dc9109ff865c910,0xbed821d9109fd86dc910,0x9fe871d910cfd761d910,0xcff765d910bf7815d910],#[0xdf7815d910dfb805d910,0x9ff825d9109ff815d910,0xcff769d910bf5819d910,0xdf572587109fd82dd910,0xdf78758710bf78258710,0xded7258b109fd8750b10,0x9ff8758b109fd8758b10,0x9fd87d8b10bf581d8b10,0x9ff865cb109ff845cb10,0xfe962501209ff825db10,0xdfb7650120df97650120,0xfe96258120dfb7158120,0xef96458120feb8258120,0xdf97458120efb6458120,0xbfb8458120dfb7458120,0x9fd878c520b7f854c520,0xbdd8318520bf98018520,0x9fd8718520bbd8418520,0x9fd87985209ff8758520,0x9fd87d8520bf980d8520,0xbf9809c520bfb805c520,0x9fd879c520bbd849c520,0x9fd86dc5209fd84dc520,0xbf980d8d209ff8758d20,0x9fd87d8d20b7d85d8d20,0x9fd8759120cfd7659120,0xbf980d91209ff8759120,0xcfd76d9120dbf74d9120,0x9ff815d1209fd87d9120,0x9fd81dd1209ff865d120,0xbfb805d9209fd86dd120,0xdfb805d920bbf845d920],#[0xdbc845d9209ff815d920,0x9ff845d920dbf845d920,0x9fd879d920bf9809d920,0x9fd84dd9209fd81dd920,0x9fd86dc9309fd84dc930,0xb7f854c5609fd82dd930,0x9fd878c560bf9808c560,0xbfb80585609fe878c560,0xbf98098560df77158560,0xdf5711c560df77198560,0xdf7719c560aff865c560,0x9fd82dc560afd869c560,0xefb8058960bfb8058960,0xcff74d8960cff7458960,0xbbf845c960afd84d8960,0x9fd84dc9609fd81dc960,0xb7f854c760bfb8058d60,0x9ff825c7609fd878c760,0x9ff845cb609ff815cb60,0x9ff865c2319ff825c231,0x9ff825c0619ff805da31,0xdfb825c061df9825c061,0x9ff825c2619fd82dc161,0x9ff825c3619ff805da61,0x9ff825c3639fd82dc163,0xdff7258510dff7448510,0xff78258510bff8258510,0xff93150120ff58258710,0xff96150120ffa3150120,0xff95350120ffa6150120,0xff93158120ff96350120,0xff96158120ffa3158120],#[0xff95358120ffa6158120,0xdfd744c520ff96358120,0xdfd764c520dff744c520,0xdfd748c520dff764c520,0xdfd768c520dff748c520,0xbfd868c520dff768c520,0xdff7458520dfd7458520,0xdff7658520dfd7658520,0xdff7498520dfd7498520,0xdff7698520dfd7698520,0xdfd7454d20bfd8698520,0xdfd7654d20dff7454d20,0xdfd7458d20dff7654d20,0xdfd7658d20dff7458d20,0xbfd81d9120dff7658d20,0xefd624c560bfd819d920,0xdff724c560eff624c560,0xeff628c560efd628c560,0xbfd868c560dff728c560,0xdff7258560efd6258560,0xdff7298560efd6298560,0xefd5358960efd6358960,0xdfd53dc960efd53d8960,0xdfd724c760dfd63dc960,0xdfd535cb60dfd728c760,0xbff825c161dff725c161,0xffd644c520bfd82dc161,0xffd744c520fff644c520,0xffe764c520ffd764c520,0xfff648c520ffd648c520,0xffd768c520ffd748c520,0xffd6454d20ffe768c520],#[0xffd7454d20fff6454d20,0xffe7654d20ffd7654d20,0xffd724c560ffd624c560,0xffd628c560fff724c560,0xfff728c560ffd728c560,0xffd535c960ffd5358960,0x29402b8000ffd53dc960,0x36c060c09f011d01d40,0xc82fd055e09f011701e9,0x19421003db07500db019,0xaec155429584d409301,0x406750c8418182e505a0,0xb83eb87920e9a1bb435,0x12d8245447588af10e62,0x8aaa14b8285c4ed89a8,0x3606450c4517a62d3c58,0x1ce038646e58d7d1a3a3,0xe0fae1ec03cb47788eac,0x57889110dd210c41047f,0x258049ec91691e823344,0x493b626f44d1c98a12f3,0x3e8a6c94af28e650949f,0x2c5e573cace15602a5a5,0xb97642e3e5b8cb5c9674,0x330c3f184b30305f4cbc,0x34926810ce8996832226,0xd1b6c36726c18d6e1aa0,0x524e749c9b38d07044dd,0x3d7a7a04f1e1de53af87,0xb20433ffc7e9cfac9ef9,0x6650b7a11841ca82a503,0x461a8afd12fa22c43988],#[0x1246648548fb91d4a364,0x7152c9254d4a10935525,0x4d6499fd32aa6194bcc9,0x8a7e74f569de13a2a700,0x44146a28aa50eea0ed40,0x5550a9d550aa9b552cea,0xf2bb056faad295872adb,0x4a966e2ca058c8b0c55f,0x5d96b9896fcadc65adeb,0xfb0636018bed57b82f19,0x9258fdb1a462acc39184,0x6744cdbd99532ee651cc,0x3359d6a56d351a313414,0x95bd5372f6db0d9bdb0,0x73f8e701cb039007140e,0x63b557620eb2dd433a4a,0x4c9e7b3cb178eaf09ddd,0x7e48fb35f36be0d7b48f,0x94104817f017dff6bf84,0xb1a13c420f83a7065e0a,0x892910f61f3439886950,0x4461a8b7515b229844e2,0xf4e3c2c7378dd31ada33,0x92112332448485490431,0x4ca73945d27a64d6c95f,0x200e270920170c04a4a,0x4713848148402443a20,0x80a2208d2389c2c0e007,0xe89190c03e122912261,0x23417848a042246e261a,0x22844890f0a08a30dd1,0x11c44570a00891107878],#[0x28b315c4e1098358918,0x4b044425201189e10986,0x1589138c0609708118ac,0xa362784220f07450470b,0xc244a282313c2110783,0x89c2854244c1a1c1f0aa,0xc27850a618784c3883,0x5098603713850a178d45,0x850ac05044c480613c28,0x4130e143410661fe2427,0x26181233180830850d43,0xc2a121d190c1d8542460,0xa350e02812321a0c330f,0x90787450787a1509128,0x70a150907ac05638f215,0x1c48570a12c107894ae2,0x242b8509c00e07170a41,0x25c48570a1232178e2be,0x4f13850a84ac01e1d24,0xb89c285425600f0e8e0a,0x4e1d18530a60e0212261,0x50244c2f105c2985424,0x439c1c012014091903c9,0x3c287034b0128543a30a,0x854241e1d188c2224424,0x41e032442a121e1c65c1,0x7e12031589a1d044a404,0x2009c2c5626874112920,0x6026278543138748078,0x313c2e2628581d380e,0x22230220803014080301,0x80a03e1010058a12e268],#[0xec571313c21187470781,0x3c09c2c488b154112901,0xcae12031589a09204438,0x873888ae12268248c003,0xe04e162b1248a0888814,0x57138789e15044c1d201,0x1e12c571313c2110749c,0xe3f0b1589a0888523078,0x487860301313c2135046,0x1589138c05e108f15891,0xc571313c2178943a470b,0xf15c4e1e27841e0e9026,0x7c571313c2180983a383,0xf1380e1224441e07894,0x8707e2b8800e1e27841d,0xf0f0c00c4f084a220787,0x291230130dc244894440,0xc260e2b1380119011082,0x709120f111203c3d2389,0xf8ae270f13c20e8788c0,0x283c09c2c562446251c1,0xc24562f0d820ac002470,0x1142714522b05024642,0x8a309f0089118c89a1e,0x448b060f22b0089118a,0x114890d0ac80880d158,0x3345505122518521ca0e,0x7848c03c008e12291006,0x1288c560c2b0109118a2,0xb89c2c0d0c4a305f89c2,0x24262b89c2a18484a2a1,0x1c54296571193c217088],#[0x83c38980008e27084e37,0x2110b840080389c21288,0x1c4dc4e160490221b89c,0x852289811c4e130f0225,0x1e270986321b89c2c088,0x2325c3c091b00491c3f8,0x9222170342111284a2e,0x3c0117024a12904ac092,0x384ac09244a38a44f8,0x3c012b0248248389126,0x713854aa4e0444584420,0x422248945085200f8004,0x7f0a9549c0920443e049,0x803e152b03492408890,0x4252784121288044303c,0x889225890a25091244,0xe005242009422248945c,0x2e13120461f0a9549c0,0x488890301293c2e1e070,0x4428401002c052f89812,0x23604922523098124124,0xf024807124a1489f0780,0x2110b8508843014be270,0x1789c2a1e044a580f89c,0x81a189490781c0802030,0x6041c383c0e0602f1385,0x381c0520613713854324,0x1f138581240886e27082,0xc05e270b0248a1838a0,0x64f0a8781c009880781c,0x80bc4e150f0225240c04,0x464f0b0222130e0f0381],#[0x110bc4e16045222140c0,0x38425114486e27084a12,0x4c483801c4e10e85c071,0x1022cae270d93c2c0e00,0xf89c2070e45e27081c39,0x602f1187c2c0e0052500,0x2b89c22404844283c0e0,0x70301407c4e11230222,0x70b8781653245c25201e,0xe0602f1384c3c0894902,0x162f8811c042446383c0,0x8d8be260b8627848787c,0xd80248cc1c5f13010911,0x45083c4a110d88e1f048,0xc850d87a844a110a800,0x549114203c3844074225,0x212b8449078c8707f0a9,0x8c83c342044490f0a29e,0x7460e9283c49110a3324,0x1e1508840052784220f0,0x13918025088921e1492,0x444381384c1a5524478,0xc20f0bc51361b89c2845,0xf1a83c4e107c5e282389,0x838301187c4e1602101,0x84c301b89c2110c84e27,0x4e16005223140c0464f0,0xc012710342044490f09c,0xf8288c0128424f0f8246,0xaa4c23002320221022f0,0xb0108a083ca02307854,0x8c0044a08b2b89c364f],#[0x7850781c0c05e270a83,0x43012c28362d03042385,0x90f0cc00f60a1422170,0x3061109110b400842a11,0x8c3c442a13080f074585,0x90f0b88e2503858ac48,0x42a1022848785a042847,0x243c370b158984078463,0x10844243c450317c411c,0x42614260e8f8be250386,0x6c1854244c1d2587412c,0x942a1226178a2e1487b8,0x86c260c2a1380078acb0,0x1d42a122b07963519b11,0xf02d52040c461b098380,0x1a1b2898bc49890062d0,0x44a3b218a0e8bc49858,0x43c089496230992caa1e,0xd0d9a4e198cc5623098f,0x2251a2f126330a018164,0x931702d51f88cba1e059,0x10c28960594631201088,0x1b902e0931587001503a,0x46e4a3c56c4613299381,0xd2024086331588c263e0,0xdc76330a01088960592c,0x45aa94120432f8981648,0x8c984ba4a888861e0701,0x745aa8e88a230e8a92aa,0x1d152555168892c0e010,0x1c88c0b0f0142a519444,0x61a4a9442612e92a40c4],#[0x70142a5182108d211142,0x8b843431ca481d4541e0,0xc21245168683a1529244,0x190c4228c0d0b004a305,0x92c3c0894b22870240ec,0x149684410ae894207d2a,0x82a250856c307d2a9292,0x5080e0fa552702372d08,0x4aea4a484a4a110682a2,0x1e068e25344f44a1d0a9,0x6435150b444250904266,0x110942410892547149b4,0x81a38dcd135190d4542d,0xd4542d110883a12084d,0xa25095dc3a3895245519,0xc664ac09244a509e8d45,0x3c05269a560f002b0790,0x4a9a32612e92a122302c,0x83a35269a422284c3a4a,0xd0a9292a68d424960700,0xb4be230f0349128f4641,0x3808454be224a92291c5,0x894941f129742c0d246e,0xa68b84f44a5f0e8492a4,0x88c4522108560fc0d0c4,0x4211222422230d85c260,0x228b8060d546c01188a4,0x92a26018288a2d547a22,0xa5194460f0f0145aa8c,0x82aa18783488a2d09838,0x187a84c1446029458b85,0x8342c0528a150a52545a],#[0x250a0a174228a1e0870d,0x890e068874220e0f0380,0x2028d45a250e84331a0c,0x420a25081f4aa4b04665,0x12046680a38d0645a110,0x4c1a38ccca35168943a,0x283d46435150b4442509,0xc66230e02c2800d19232,0x30a10c6a0e0192cd1c5c,0xf126330b0141843259a4,0x33198cc2a0f0f00c9668,0xa228b55182ccbe250592,0x14544509834a2e888360,0x43259a40a68700418782,0x822b131cc2a0c0d8d808,0x11894361d098452c5625,0xc2c5626800f1c103519d,0x70b1589a00ac70400789,0x7808a1520a4549120fe2,0xa2220a5422a489445110,0x972a24a8a451107808,0x61e001c92a2909807513,0xa89802a24a8a31511144,0x841d0b01120e2486e403,0x210742c02220a4549148,0x42c025c1c92a29022891,0x30f000ea124a8a40c531,0x348a16001c92a28a3944,0x4d211083a16020a45495,0xd34841d0b00888291525,0xb4d2130974950b00c3a2,0x2d345441198742c024a8],#[0x10c1c05568a350b0092a,0x2324a88c360d568a3511,0xe028a4a228880aad158,0x1d4520582a0f06a84886,0x1507861b249862aa1304,0x2838062b3474450900c1,0x6a1b0a82c5668e466142,0x210c28031682cd1a244]]
def g191H9 := limbs80 #[#[0x7058ac140101808001b,0xa190e084080b0e01428,0x4c267d0e848000f1082c,0x500a050e0240e31008,0x35014280e0f850501a0,0xcba250f434022f02c6a0,0x408460d93c5400060046,0x7d1e00251d004011082,0x1a1d5e05331a4543021,0x531c8182b2624001a01e,0x34f3098d4000002018c4,0x5ab2d1b2bc224620b044,0xd000f101180bf082fb95,0xc00af6057c0105011302,0x55b1d980410bd1b38901,0xf381d68b8f94c9b35c04,0x62822e204c09f404be04,0xec0ca9012d0581336a00,0xb080e181a80b66141f00,0x390af80003424b00fa02,0xaf83b40b680001919185,0x5fa21f847c0c0e9519a4,0x7c0b150521836294e98b,0x670199a286a2558ba792,0x5855f0d1a09aec5,0xf78a3a85638d35053000,0x7c006992aa004b00760c,0x62092896e02ba842e0d,0x7d04b30328935b09cd15,0xc3120108e5044a03438b,0xe4b436b41f14c6890b22,0x3b107d84c684900a4a04],#[0x56027d036fb1e40cba12,0x318b8181ef838f8a4603,0x57a09903f203d22377a4,0x38041890638bfaa07830,0x5040a31c18200000204,0x8000000030402c18800,0x3a44d0a07331a9452305,0xa2049c01ca0304005882,0xb904c80002835d01b7a1,0x88ae202eb82ac01360a,0x41817ca46232ae82898d,0xe7101f0d290cc8000004,0x76a1ba021000020b4621,0x7582c832c03045801324,0x2008321d3815e094701,0x18231001dc837e028000,0xaa814c21d98a53809805,0x358569820d8398a1c38a,0xeb409382de14e5112a8a,0xac0316a3238267807e90,0x82838583e902711441a1,0xf8824189bb8031024a01,0xdf23bf3375a3cb81a483,0x5c81f882e68050000104,0xba0a14816291e290408a,0x80000000000297014281,0xb28ab492dd8b4f327a92,0xe000018a07029a88bd09,0x9a91eab200000000008b,0x2800058bda82238ada12,0xc22908540000121e805,0x8d846e120c254b0b298a],#[0xb8093c89fe153b938421,0xb80000013e11dd922091,0xc801fb03e11b080920b,0xdfa050b2a00b7191a180,0x5c04aa833c0d27249380,0xce25408bcc8029b23c92,0xc38d110377a4bd11cba1,0x220cfe000314b202c700,0xe9b39480ad018b821a81,0x1d8acf8331a27f048aa0,0x40846303090cdca1b103,0x28a20118183e20552a3,0x4389a60038a4fea50800,0xbc819704700001a3f512,0x3803c680b522038a1b80,0x2a0ac1825e8bb0000290,0x5100d00005897684318a,0x18000683da8b3a825010,0x9000000005834993e90b,0x6b04ff0bc303bf89c003,0x28324048302a0000002,0xc8000782f38d84223e85,0x6d84ee88f284a0808983,0x138237a550118b126381,0x8c88aeb44f03a80155a2,0x178b3381f4851611aa22,0xc0000000cb9550000084,0x6842683a6342d220b24,0xc20574a24931a7810800,0xd58cc232e60cd5045d11,0x4e0b50428e1516802604,0xa72262058e919a8b2005],#[0x122515a08208de01e180,0x31bbc2]]
def g191D10 := limbs80 #[#[0xd73186fcb80c35fdd531,0xa21fe58110afaebb1dd,0x10feac2887f621443fa9,0x5ff72442feb9221fd985,0xab0e217fdd910bfaec88,0x120bfaed885fd72c43f,0x905ff71483fcb0241fe5,0x2febb2417fdd120bfae8,0xfdd930bfee4985ff7648,0xc4b06fd62582ffb8ac17,0xd82feb8ec17fdc960dfe,0x37f5da31bfae118dfd72,0xfae130dff70586feb80c,0x7058efeb86c37f5da61b,0xa21ff48510bfae1b1dff,0xffa84887ff61443feb0,0xfd72443ffb1221ff5891,0xbb221ff1d910ffee4887,0xb10ffeec887fe76443fe,0x7ff62c43feb1621ff50,0xfe30a41ff8c520ffa629,0xd8520ffcc2907fd61483,0x6907fe71483feb8a41ff,0x83feb1a41ff54d20ffa8,0xff59120ffae6907ff634,0xaec907fd74483ffb2241,0x24c3feb1261ff9d920ff,0xc1ff8c560ffa62b07ff6,0xff8e2b07fe61583feb0a,0xf71583ff38ac1ff5c560,0x92c1ff5c960ffac4b07f,0x60ffac6b07fd53583ffb],#[0x7fd31d83ffb9ac1ff5cd,0xeb82c3ff54f60ffc63b0,0x480b802e0007ff70587f,0x2e10006e82e812606402,0xfc876837e1980b685182,0x5c62bc140896846e2140,0x1e28e886ee35819c8c48,0x897e49c238910882e3ec,0x2d69608aa6530286937,0x98cf66543149838bd65d,0x943b49d18e3e6e83649a,0x1890567f83ea9ef8f567,0x95849ca4691ee8c044ca,0xa9a945ea0c4f2a6b92fe,0xeb3458aabd95b6ab4548,0x2b069806bd85deae596b,0x2ecf4664b29990ec6862,0x917709b36d786a8b4c9a,0xf042820245c3c1c0060,0x18246c3c1c008050a1b,0x8c28a2689302f0f07002,0x250428ec9373407c4000,0x120a093b20c09b120308,0x308282600f0841801e1d,0xdcb08800a093c143c231,0x48200e003f130a2a2504,0x80341c4c28a89803824,0xc0c043cd3130a2a24c0a,0x30126c4c28a80893c24d,0x38091c20ae002824f060,0x60028f02464108c3800a,0x6c4c21712432581200c0],#[0x2400204b13088a04e888,0x4e2e084ac4c3c2264912,0x1c18160313090e0494c,0x529c4c2431224605c482,0xf130a0488e8b0807060,0xc4c3c21224481c181600,0xf1024e04c7070605482e,0x3018bc4093c131c200e2,0x3f07130f092a0124c8a0,0x8c4c21e412f803a20cc,0x84b12030b0c782104cc9,0x7060580c4c2c31e41332,0x130d270b04203cae00a0,0x41c4c2c3100880352d2b,0xc04d208c028a070605,0x3c1c028820a20dc15002,0xf05002820c02470521c,0x30188c4c28a4089302f,0xc0c04d10028c02483734,0xb2b0fc3c1c0080a0920d,0xc0711030a2a2420c8c0,0x820134c48b40300928cc,0xc05022f1020c02483703,0x24988c341800a0926180,0xa09341a0e04200028f0,0x312030a2628f0a088037,0x6c4c28a893c243c1d046,0x30a2a2504dca0701802,0x8a89224125203c1c2312,0x2270904c074d07c412c2,0xa894400c209371d34340,0x2a249488789084342410],#[0x8a8922481e20203f130a,0x2030a24c09474a0fc4c2,0x41841898a3c14209a2b1,0x88a41893714062a24f0,0xa3112224b0d160205548,0x20e48458892c38142804,0xd090e012a052494d2e1,0x8149373a34b8a49c4912,0x490712832b0f80c4c24a,0x5344894230e060128e92,0x880c41233c3c24a49812,0x309292494488882e0f0,0x8743804a251249221d12,0x494d250a0310652d24e,0x4dd24b46428892c3818,0x2534b848220d0a03112e,0x27124442c380c44b8149,0xd12012c9449248892e29,0x80380c412c2372e20584,0x1514482313090e0494e0,0xc4c22531249a1d1e191a,0xb130838e881817128043,0xc4c248122224210e004,0xb104e2e24f064746458,0x154782c4138b4189371e,0x142804a2912230f05160,0x124c8d330e453288c3c,0xac1c98230f071308cd2a,0xe33c3c108804a324924,0x9221e28200128cd24c86,0x247852a0f80c4c24a254,0xc4c24a49333228952889],#[0xd0cb1308e880e080026,0x24341c4c20e3a1c21060,0x4d202003130904a8c071,0xc924a464288c3c18049,0x91e200b0c2304cf112e0,0xcd24c86428013c44b224,0xc3c1458088551d0b112c,0x49d170f06010a2128944,0x94642c3c18049884d20a,0x290d07122b0a2500f098,0x84341c48ac289403c2b]]
def g191H10 := limbs80 #[#[0x441460c520c18504104b,0x6d8200c54a04030b1010,0x407080020401c008e1c,0x4b08214628b48a18c30b,0xf00a28461e0540c1082b,0x50210e0614ce40051526,0x19544220019d9845c3,0x74c6201ac90282c101f0,0x1c50170c1841858f8a1c,0x412e946a16130703200f,0x3884000000091,0x1af0830000288a622f70,0x9052407850,0x10d00000000000000000,0x3bb803384efc01630b6d,0xba201380060000803559,0x217f6a38c000104f3902,0x4056800000001406f,0xde9034a415083fbc1420,0x2c0ccc4c93177d00ecd0,0x2e7817c08f2706f0000,0x2a000000001e0265076a,0x86223000000000000012,0x592d5c14840d,0x9d40000941900002c026,0x82c934468a1d6c,0x28807e45e0000000,0x18325418ca2fd7638,0x32000049424000000000,0xa0000a80b981e80001c0,0x101f,0x212cc],#[0x84038400000000000000,0x201200002c936e50b900,0x506030011a1d80000,0x9c00000000000014a0e0,0x8000082b712119215b40,0x335000000000420fc22f,0x1a00000c0ca000000001,0x3903a800035031c00ba4,0x791680001080,0x5c1249ad0227812cc19e,0x810b0000080a00,0x622d00000c0010000580,0x209e8c1b482c00000000,0x826073e03aa61c000006,0x720c1124b902a4000040,0x504be1349d9f,0x101c8c6a007c06d38200,0xe8000089c8400e718388,0xf02f90bef50d32855d02,0x241a40000,0xd820fb00000000000000,0xf1040e4c29026691c1d1,0x135c05f4e105d06cb041,0xc00003495f6103f07d0,0xb3047880cc19ba609f20,0x84e30000514140000ccc,0x1688471202a910445026,0x7dc166805cc05ef8169e,0xf22d8000044e20017411,0x6bc135388320000d02c,0x843319432416c0000d,0x8c2e1522e8000140b600],#[0x106d803d845e4013c011,0x1bb81f3c102000018136,0x904c0000a47011,0xd03ff00fc00002093000,0x2eab00300003918062c6,0x8b08b50000000000000c,0xc0000c2da0000483c8c9,0xa051c03f20b18274d020,0x2480002817fe02b004a5,0x9363a12304018b408700,0x50a1716c9226810a7e07,0x85e00a53424082994034,0xd1883c0096f2853141b4,0x82f0c0ef804a0000600,0x20149d01682e2107c,0x783071081c8000020610,0xac4047810102148a09c0,0xc190a02f0845a822c813,0x4008062002d803420b20,0x413a1d063007312670b,0xc21da8b1ce16aa40ad03,0x85a402c581ba8144a305,0x4dc0ce545ee805c408b0,0x106784ed205930bf360,0x12fa6056c859e4592215,0x4e029d48e56100507e7,0xb900450af5018f446f32,0xa80f00006a172804b84c,0x7216e41ff,0x119ec00000000481440,0xd827bc9c24418801b800,0x2238000288cde8b87010],#[0x5450550042a05e184eb3,0x704a30000000024915ec,0x182f9707868260511,0x8ec57868bf308240188,0x8e13c800004012001518,0x30246c0040000481,0xe233c83a381ede071,0x5a2a000000,0xdcf2569806c00,0x2789d9240c90688000,0x2f2049408224e01057a,0x5c03f7003fc9bf087f00,0xe05e80286939e8899e82,0x9ca01c4260242a281a1,0xe340a860ee0023eb3e9d,0x222bba16ce092c07af8b,0x162f129b8053c4150000,0x805c5c0ce45700000e,0x1806b304480000000000,0xd108c07ba81280000000,0x188ca00002029d828f,0x58000000000095000000,0x72558000145c60000d07,0x46104d2a2ea402c0000,0xcc8810000010c2741ac6,0x640e8000010848000349,0x13040000e04800007035,0x1d02a00004,0x202180000e09080e300,0xc4f00000582d1c0fa000,0x1be90f2000050b738161,0x0],#[0xbc2b8000064b1d04c800,0x258311ddc0edcc78a630,0x105700108000000c4e,0x2000011824a2ec000000,0xc17b181b7c20,0x30f45dc0000000033188,0x6681c38174e0c2c00608,0xf00eb416c41e36030603,0x40ba17ad92f698e40000,0xee00ac706540b28c8616,0x5002204b29044703cc81,0x4236c041001e20729228,0xe0408,0x80468000381cd808600,0x180c5039118b2000,0x9594027501c80003819a,0x5500c60000404500003c,0x4035101dfb0e55005720,0x629f833389b60000c011,0x925f800011131c0641,0x9809c00003b3fc817600,0x14448301b60241613,0x2c1b762e4b27a01048,0x301e860ddc45b80,0x84ac014e05,0x899b0338000244c2c81a,0x71800db8718000000010,0x381d90c5ee25a692d900,0x1092c0f90464f22a8000,0x30d22e490fb60155034f,0xb505bf23940000000002,0xe0b52055d33d788a4409],#[0x955a0d3863ae1181e09c,0xa09e34308701f70b7dc,0xa2027858964435809823,0x65800030a100000b01a,0xc26254d8431c11ce084c,0x708600000003a4902222,0xc075e2be0000682a3c58,0x41c1a45990844015a]]
def g191D11 := limbs80 #[#[0x60ff4c3fd20ffc43fd10,0xfc61ff8c7fd31ffd83fd,0x8ffd53ffd87fe61ff587,0x3e0ba1b83e003ff63ff5,0xba2aa9ea3c7a5b26093d,0x444870a08a00248d771f,0x40401228443822800918,0x882c009204070c162438,0x511121c282009110c141,0x860b121c282004121c30,0x10a1c2438300295183,0x10e0c01420496202c383,0x850600814248080c1010,0x4882044383005091a243,0xe0c012347890e1418028,0x20143830220b124020d0,0x20287060441620492]]
def g191H11 := limbs80 #[#[0x2a0610365410a028021d,0x1cb960220300080040f4,0x40a86e0019114d418200,0x82c200401318003d9241,0x1140af81978c2800c04,0x7b4238000789c0938c27,0x708d10e26890e5053d1,0x493a0000889d020d9533,0xb0000684600006063017,0x22e0003c268000809540,0x5832e068a30640780008,0x2c130000c49b4554000,0x12925029a935b01000,0xc0514cff19bab420,0x172118000a26e0000000,0x1246ce2580001293ed,0x322c600f436f01c80160,0x9bc25f0350001c8a4d11,0xb5ad038152456f19808,0xf449c497e0f961a8000a,0x29905cc4af2a8acf2824,0xb864f2ca04055617f60,0xe015f1b2000002b0000b,0x14000121000000003210,0x882180c9a01c251a0,0x712d0001804c000780e0,0x1e01ed00dc20c0000000,0x859605021b7811946be8,0xd0425196e8a911b010a6,0x68c0f921101b030b7a06,0x14094c0d803a781603,0x800000014043a14b2210],#[0x2c5035426c03da96c084,0x2709022d65000050a3c0,0xaa23006000000030000c,0x5c22d000060b3c007482,0x283ed04516c02dc08880,0xa852017149796260843d,0x888417c0710996150017,0x845a87f52b10579038c0,0xe812f4ae0b27001b4347,0x31424084031aea4e5c10,0x4ba00dd497b8c2785520,0xf338507720f288e0823d,0xd8906f83f18b9c931a2b,0xb6ece7613ec25318780,0x1d1778a53809c,0x3ec138c060001e091497,0x494f0ada0da11e306221,0xd25a226de45700ec8454,0x342800000000000185b,0x276d07ed2e0000403400,0x84010001c0cfd0d9000e,0x80000591a0000a175264,0x1600a415d225f99520,0x19420001216019dc1110,0x96000028b6601342f,0x2d9d0000000000]]
def g191D12 (j : Nat) := if j=0 then 0x81840802ff else 0
def g191H12 := limbs80 #[#[0x9b0b30200004447000e0,0xb44d4500000c34370,0xd04f8491e30354031d,0xa606000000000562b410,0x700000d85000522d0,0x1000000000000083353,0x207113000000293b,0x90841600078,0xe000805581b0d000000,0x517d]]
def g191L : Nat → Packing
  | 6 => (11,6,6,0,0,7,0,g191D6)
  | 7 => (76,5,6,0,0,11,0,g191D7)
  | 8 => (178,4,6,0,0,14,0,g191D8)
  | 9 => (269,3,6,0,0,15,0,g191D9)
  | 10 => (95,2,6,0,0,13,0,g191D10)
  | 11 => (15,1,6,0,0,10,0,g191D11)
  | 12 => (1,0,6,0,0,0,0,g191D12)
  | _ => emptyPacking
def g191I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 6 139 3 12 4 4 g191H7
  | 8 => lookupWord 44 223 7 15 7 4 g191H8
  | 9 => lookupWord 99 431 9 16 8 4 g191H9
  | 10 => lookupWord 136 743 6 17 9 4 g191H10
  | 11 => lookupWord 57 281 7 15 7 4 g191H11
  | 12 => lookupWord 8 59 5 12 4 4 g191H12
  | _ => fun _ => none
def g191 : Forest := ⟨191,12,fun i => g191Y[i]?.getD (0,0),g191C,g191A,g191L,g191I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P6_0 : block g191 6 0 11=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g191B6 : block g191 6 0 11=true := g191P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P7_0 : block g191 7 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P7_3 : block g191 7 3 73=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g191B7 : block g191 7 0 76=true := (@block_merge g191 7 0 3 73 g191P7_0 g191P7_3)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P8_0 : block g191 8 0 21=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P8_21 : block g191 8 21 31=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P8_52 : block g191 8 52 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P8_148 : block g191 8 148 30=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g191B8 : block g191 8 0 178=true := (@block_merge g191 8 0 52 126 (@block_merge g191 8 0 21 31 g191P8_0 g191P8_21) (@block_merge g191 8 52 96 30 g191P8_52 g191P8_148))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P9_0 : block g191 9 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P9_3 : block g191 9 3 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P9_99 : block g191 9 99 79=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P9_178 : block g191 9 178 67=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P9_245 : block g191 9 245 24=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g191B9 : block g191 9 0 269=true := (@block_merge g191 9 0 99 170 (@block_merge g191 9 0 3 96 g191P9_0 g191P9_3) (@block_merge g191 9 99 79 91 g191P9_99 (@block_merge g191 9 178 67 24 g191P9_178 g191P9_245)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P10_0 : block g191 10 0 4=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P10_4 : block g191 10 4 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P10_40 : block g191 10 40 55=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g191B10 : block g191 10 0 95=true := (@block_merge g191 10 0 4 91 g191P10_0 (@block_merge g191 10 4 36 55 g191P10_4 g191P10_40))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P11_0 : block g191 11 0 15=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g191B11 : block g191 11 0 15=true := g191P11_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P12_0 : block g191 12 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g191B12 : block g191 12 0 1=true := g191P12_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191T : checkedTables g191 12 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g191 0 0 0 = true)
  · exact (rfl : block g191 1 0 0 = true)
  · exact (rfl : block g191 2 0 0 = true)
  · exact (rfl : block g191 3 0 0 = true)
  · exact (rfl : block g191 4 0 0 = true)
  · exact (rfl : block g191 5 0 0 = true)
  · exact g191B6
  · exact g191B7
  · exact g191B8
  · exact g191B9
  · exact g191B10
  · exact g191B11
  · exact g191B12
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191G : graphValid g191 (boundsBefore K127) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low191 : Lower true (varsX 191) (graphGoal 191) 13 := lower_forest (g:=g191) (i:=0) (hints:=1052722) (before_sound K127 V127) g191G g191T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K191 := extendKnown K127 13 [(191,[]),(239,[100]),(251,[66,98]),(254,[32,64,96])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V191 : Known true K191 := extend_ok (m:=191) V127 low191 (by decide +kernel)
def g223Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x7fc0000ff803fe00f,0xf8e1c70fc087b0fafd13])),(BitVec.ofNat 152 (word80 [0x28140a05028140a050,0x28081200820900120910]))),((BitVec.ofNat 152 (word80 [0xf80000000000001ff0,0x30010040070270])),(BitVec.ofNat 152 (word80 [0x994ca6532994ca6532,0x98000010000000000270]))),((BitVec.ofNat 152 (word80 [0x1ff007fc0000f,0xf90207c000f83f04fcab])),(BitVec.ofNat 152 (word80 [0x5028140a05028140a0,0x502000000410122410a0]))),((BitVec.ofNat 152 (word80 [0x1ff0,0x10040070000])),(BitVec.ofNat 152 (word80 [0x66b359acd66b359acd,0x60000000010040070000]))),((BitVec.ofNat 152 (word80 [0x3fe00007fffe000,0x603f800fe007ff800ce])),(BitVec.ofNat 152 (word80 [0x80c06030180c060301,0x80008002080064402048]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x3ffffff80000000,0x7fc0000ffff8000030d])),(BitVec.ofNat 152 (word80 [0x30180c06030180c06,0x340000411a200004200]))),((BitVec.ofNat 152 (word80 [0xfffc00000000000000,0x7ffffff0000000003f1])),(BitVec.ofNat 152 (word80 [0x40201008040201008,0x49324a8204408808001]))),(0x0,0x0)]
def g223C : List ColumnInfo := [(0,8,213,2,11),(8,0,215,0,11),(1,0,222,0,10),(2,0,213,0,10),(2,8,213,0,10),(4,0,219,0,10),(16,0,207,0,10),(64,0,159,0,10),(0,2,85,136,9),(128,0,95,0,9),(5,0,218,0,7),(17,0,206,0,7),(20,0,203,0,7),(65,0,158,0,7),(68,0,155,0,7),(80,0,143,0,7),(129,0,94,0,6),(132,0,91,0,6),(144,0,79,0,6),(192,0,31,0,6),(21,0,202,0,4),(69,0,154,0,4),(81,0,142,0,4),(84,0,139,0,4)]
def g223A : List (List Nat) := [[],[100],[66],[66,98],[98,66],[98],[32],[32,100],[32,64],[32,64,96],[32,96,64],[32,96],[64,32],[64,32,98],[64],[64,96],[64,98],[64,98,32],[96,32,66],[96,32],[96,64],[96],[96,66,32],[96,66]]
def g223D5 := limbs80 #[#[0x829c89d9755954250120,0x29c8a19755954250120b,0x9caa99765515250120b8,0xc5a59866515250120ac2,0x56d0a65d56250120b229,0x6d286dd562501209c29c,0xc9a525974581209c2bc5,0x9a0654865d120cc29b46,0x86654865d120e0698668,0x8632108400c078baec1,0x7706f01d00b449948235,0xdec1dc1b8074028077b0,0x28057d07b06e01700a01,0x7f00201df81dc1b407c0,0x5f003fc00ff0020]]
def g223D6 := limbs80 #[#[0x41e0a619755954250120,0x483614d32ecaa2a4a02,0x280906c2ba5dd5645894,0x4250120f852ecbaacaa1,0x2a84a0241f0a9d975595,0x56550940483d14c32eab,0xbaacaa1280907c29865d,0x19755954250120f2530c,0x5c32eab2a84a0241f0aa,0xc28b65d56550940483c9,0xf8576cbaacaa1280907,0x24174aed576595425012,0x40483e15daaecb2a84a0,0x1280905ca9b79d965509,0x54250120b553713b2caa,0xb2a84a024174a6d77659,0x9d65509404826d4dd6ec,0xd3acaa1280905cabb66,0xed5a7595425012097577,0x55db34eb2a84a0241b4a,0x4dabb669d65509404836,0x20d35770d3acaa128090,0x24172a6daa759542501,0x9404825d4dc74eb2a84a,0xa1280906cabba5db6550,0xd54250120ba576abb2ea,0xcbaa84a0241b2ae99765,0x9d97550940482e94dace,0x6b432eaa12809059a9b8,0xa6e2865d54250120ba53,0x6d4dd50cbaa84a024166,0x5da1b12997550940482],#[0x120d9534c532eaa12809,0xa024166aee1a65d54250,0x940482cd4dc54cbaa84,0xaa1280905d2bb561b755,0xdd542501209b5774c36e,0xdbaa84a0241e4aed586,0x8a1b75509404834d5dd3,0x373436eaa12809059a9b,0x6a6ea86dd54250120ab5,0x2cd5dc34abb284a02413,0x904dabb569e765094048,0x12097576ad44eca1280,0x4a0241b8a69976551525,0x54940482795dd2ecaa2a,0xa8a9280906d29a65d954,0x65515250120f8554cbb2,0x2ecaa2a4a0241b4ae997,0xba5d954549404836945d,0x536f3b2a8a9280906d2b,0x6ca6e2765515250120ba,0x82794dd4ecaa2a4a0241,0x906d2ba6dd954549404,0x50120f852ecb2ac8a928,0xa4a0241f0add96559152,0x454940483e14bb30ab22,0xac8a9280907629966156,0xa55915250120bc576cc2,0xaaecb22a4a0241f0a5d9,0xbb55d96454940482f15d,0xc536b3b2c8a9280907c2,0x172a6de765915250120b,0x482b54dccecb22a4a024],#[0x80905e2bb56596454940,0x250120ec576acb2c8a92,0x2a4a0241caa2e1965915,0x6454940483955dc32cb2,0xb2c8a9280905e29b5a59,0x6965915250120b9536f4,0xdb352b22a4a02415aa6e,0x2bb56a56454940482b55,0xad536d54ac8a9280904f,0x413ca6d7a95915250120,0x483954cb30cca2a4a02,0x2809072aa96619945494,0x5250120cd574ccb328a9,0xa2a4a02415ca6d696651,0x17654940482ad4dbd2cc,0xd230ca9280906d2ba5e9,0x5ba461952501209e536b,0x4daf48c32a4a02419aa6,0x2a996e918654940482d9,0xb65768d2b0ca9280907,0x24169a6d696619525012,0x40482974dcd2cc32a4a0,0x92809053a9b4e5986549,0x16250120c6d72cd2f0ca,0xb22c4a0241f0a5d56559,0xd56458940483b15caaca,0xabaac8b1280906d2ba5d,0xe97755916250120f8534,0x55dc32ab22c4a0241f0a,0x5e2bb569d6458940482d,0x20f852eab2b28b128090,0x241d8ae556565162501],#[0x940483715d2acaca2c4a,0xb1280904eaabad959458,0x516250120da574bbab28,0xaca2c4a0241cca655856,0x5d56558940483995caf0,0xcbaacab128090786986,0xa6d3955956250120f0d7,0x934c372ab2ac4a02415c,0x5a6bb56196558940483,0x120b4d36bc32cab12809,0xa02412ba6eb865956250,0x8940482f15da2eab2ac4,0xab1280907c2bb45d5655,0x5956250120bc5369caac,0x50b2ac4a02413aaed1a8,0x76a16558940483555da3,0x369d42cab12809068ebb,0x2aed1865d562501209d5,0x3c55da30cbaac4a02417,0x905ca9b4a19755894048,0x120b8d36b432eab1280,0x4a024163a6e2865d5625,0x58940482e54da14cbaac,0xeab1280905cabb461b75,0x6dd56250120b8d76ac36,0xb0dbaac4a0241e2aed18,0xba61b7558940483c35da,0x5369436eab12809068eb,0x63a6e286dd56250120b9,0x82d35dab0cc2ac4a0241,0x905aa9b4a1985589404,0x50120b4d36b4330ab128],#[0xc4a0241a9a69b95e1562,0x558940483994da72bc2a,0x72ab1280906369a6e578,0x86e556250120b4d76ac3,0xab0dcaac4a02415aaed1,0xbb461b95589404829b5d,0x4d76ac372ab12809072a,0x15aa6d286e556250120e,0x482974dc50dcaac4a024,0x80904ea9b5e918658940,0x250120b5536bd230cb12,0x2c4a02416aaed1a56196,0x8658940482c75dbb4ac3,0x450cb1280904eabb5692,0x698649655012095d76ad,0xdb530c92caa02418dae9,0x3976e917559540482974,0xb87768bb2eab2a80906c,0x4171a6ca765d56550120,0x482e1cda4ecbaacaa02,0xa80905879b89d9755954,0x7550120d8774bd22ecb2,0xa2eaa02411eaec9a6e51,0x965d5404826d5d934dc,0xd212cbaa80904da9b269,0xd5a4a1b7550120c9732c,0x5da34bc92eca024134ee,0xdabb4697925d9404823d,0xca734bcaf28bb280904,0x24136aec9a5e51765012,0x604823d4da74ac94eca0,0x12c0906ca9a759154589],#[0x1625812099d76ed32a8b,0xb22c4b024133a6dfa655,0xd16458960483c55c2ae8,0xbc22c8b12c0905cabb55,0xdd7845916258120f152e,0x55caf08b22c4b0241e2a,0x5aa9b5e1164589604839,0x20b95369baac8b12c090,0x241b1ae977559162581,0x960482735dab4eb22c4b,0xb12c0905cabb46997458,0x516258120b8d76ad32e8,0x8aa2c4b0241f0a5d5745,0x69d5458960483d14c2b0,0x68d3aa8b12c0905cabb4,0xa2e1a75516258120d957,0xe54da54eaa2c4b0241a3,0x4ce9baa9d5458960482,0x12095d371d3aa8b12c09,0xb02416aaed1a85516258,0x8960482d54da550aa2c4,0x8b12c0905cabb45d5745,0x5d16258120d4d74bc2ae,0xaba2c4b0241b1ae9785,0x46177458960483c35d2f,0x774c2ee8b12c0905cabb,0x9ae9795611625812099d,0x3d14c2ac8aa704b02419,0x9076299559154e096048,0x8120e6532ac22a9c12c0,0x4b02416aaed185593825,0xe0960482b55da32ab270],#[0x24aa2c090636ba565584,0x86495458120ad53694b3,0xb44b22a8b02414ea6d29,0xb565d6455160482f15da,0x736b4bac8aa2c0905c3b,0xd0e659755d15458120b8,0x8361dd32eaba2a8b0241,0x906b2985e8984551604,0x581209d5365d232caa2c,0xa8b024192ea5fa465954,0x655160482a5cda52ecb2,0x32caa2c09056abb46899,0xa2a595458120ad5365d2,0xbb454b2a8b024193a65d,0x99769296551604832754,0x97768cbd2caa2c09064b,0x187a2a3a265d5458120a,0x482754d9748b2ac8b024,0xc0907469955d59259160,0x458120e8d72bbab24b22,0x2c8b0241a9ae97856496,0x745916048361dd2aeaba,0x2f08b22c0906a3ba5e15,0x9a5e116458120b55764c,0xcab49baac8b02413aaec,0x69b2e57755916048361d,0xad5768bab25b22c09074,0x41d2aed17564b6458120,0x482674d934a4b2e8b02,0x2a8906c69b2694965d16,0x8055120f252eaba304c0,0x82ecaa24162e6d2865d9],#[0x3905d9544820fcdd70fc,0xd0328bb2a89061b89869,0xe8986517655120c37131,0x8d892dc830eaa24106fa,0xf9a625b9061d544828f,0xa1f760cb12cc3aa8906,0x24103fee996259875512,0x64483c54bb2e8c1300b2,0x2c890726b9559582601,0x58059120c6d74bcab04c,0xb2ae8b224169a6cb8559,0x83655d16448265cd874e,0xfcaecaba2c890663b956,0x6c276e157459120c87b4,0x1fdaaedcaae8b224162e,0x54b9b09db955d164482a,0x2099776ad04ecba2c890,0x224130fed5a7e5165591,0x56448303fd4f4ac3ecab,0xbaac8904c3fb569287d9,0x417659120c977414b328,0x1ca2ecb224132eed1a5e,0xe57945d964483655d174,0x60d2f28bb2c890643da5,0xe297a066376591209977,0x21fd3749cab0eb224185,0x636ba2e839561d64483,0x120d2d745d072ac3ac89,0xba241a1ee9ba0e558759,0x19744830f8d0f204330a,0xa432e8906569a2681952,0x654865d120e0f30cd032],#[0xcca90cba241c1eec186,0xa619952197448303e5d3,0x14bd030c432e890607fb,0x1fea4a5618865d120d0f,0x303fd4f4ac310cba2418,0x90607cb5ea5862197448,0xd120c0ff6bd4b0c432e8,0x8bb24195ae8ba0e55865,0x611764832b5d1741cab0,0xc9c02c4b0647ba6e8395,0x56138058960a57768caa,0x8003200c800189ee959,0x6843201690a1046c1bc,0xa25412188704161e40d9,0xb8b985942a314909d84c,0xfc3621a88cd464830817,0x28fa479a3bc1d00e3c6,0x94448623a916487a4212,0x28993dc9cc4d526212cc,0x8b8c5aa2c19570a6a524,0x34219a0c98630304978,0x80ef27683a09c68dba6a,0x1c4059fe8fd27d83d89e,0x28d12488143821510708,0x92a48723c91ac8c545a2,0x266d3149794b42531276,0x6a2250327a939c9bd4d6,0x42c5d5f6ad455c29ed46,0xb6bca5dcaea16c0b3959,0x2630ed854c196042fdd7,0x9d2ccd65332558f2c5d6,0x6b83551a86d3268b33e9],#[0xdbacdc56da368db24d81,0x8723b8adc34e096fc379,0x25d70ea774b3a15ce8e5,0x3a794bc61df8eeb76d3b,0xeadf4af947c1bd9de96f,0x3280b3fe9fd2fd87e3b,0x42ba15109783dc17e087,0x313589244221d90db865,0xbc69a32b1848b9c58a2a,0x5121790347aa3b31c88d,0x8ecc325f72ea96cca1a4,0x71d37d9b64d6e69532e9,0xa15cf8e7a53c19d84e7e,0x293948ba3d51a68b1447,0xea86d3f29d74daa64d2e,0xe6ad1557aa354d6a5f51,0xd4ae1d6cab4359bac555,0x8eac53618b03d7dabcb5,0x6a0b47d9facdb65cb25d,0x5c46e016fab7a5b8eda5,0xd78dbbe5d56e89733b91,0xd5ffafdb7d1be05ebef3,0x43885c34e13707982bc0,0x8ee3db1cb8d4c61e2cb1,0x3e39e0cdce6a330394fc,0xd31691b46ba24d09e80b,0x3641b0fd746adb509a73,0xafc3f90402403bf0fe41,0x9ef03e023f0fe4080780,0xf8051d3c0bd0760dc03,0x1df87f007e83b06e0bc,0x4077e1fc0184efc3f803],#[0x273e3e4df804fc00fe00,0x87e00ff00203806fe00c,0x802fc00fe007f0020440,0x200bc0bf007f80100df,0x937e00bf003f801e4df8,0xf802fc00805fc017e007,0x4077e00bf003f801c4d,0xc01006fc0100efc017e0,0x1726fc015e3fc01726f,0xf801015f8023c00806fc,0x5f801fc00fe007f002,0x7e1fc01fe007f003c9bf,0x5f87f00782c057e00c05,0xf803015f80201ff80201,0xfe0080780afc0180afc3,0xe008057e008077e00807,0x2fa0ec1b82f03c014057,0xc3f803f41d83705e0780,0x1fe00405fe1fc0180ff,0x880afc01fe004857e1fc,0xbf003f801fc00fe0040,0x408fe00808fe00808fe0,0xe007f003f801fc00fe00,0x201df802015f802fc00f,0x5fe00bf003f80101df80,0x7f003f801fc00fe0040,0x17f80201df802fc00fe0,0xf03530df801005f8020,0xdc1781b00be83b06e0bc,0xbf0fe00ff0fe00be07a0,0x19e007f003f87f00404,0xf41b82f03e01846fe1fc],#[0x5f801fc00fe00408fc0,0x1fc00fe007f002237f0,0x100efc017e007f003f8,0x100d015f803fc00805fc,0x802e8bf802fc00811fc0,0x4097e00bf003f801e8bf,0xe007f003f801fc00fe00,0xfe005f003f8013c00f,0xbf00205bf005f801fc,0x3f801fc00fe00408fe,0xbf003f801fc00fe007f,0x5f801fc00fe004c5fe0,0xe007f003d17f005d17f0,0xfe007f002017f00407,0xf80101df80201ff802fc,0x9bf00401bf00400bf005,0x3f801005f80203f0036,0xe004017e008037e00bf0,0xf003f801fc00f02fc017,0x7f003f801fc00fe007,0x3f801e0438025c00fe,0xbd0760dc1781f00e620f,0xd83705e07c039871cfc0,0x7f003f801fc008e7f81,0x3f801005f802fc00fe0,0x5f00378015c00fe007f0,0x1781f00df801fc009e00,0x2043f004043e0760dc,0xbf003f801fc00fe007f,0x3f801fc00fe00402fe0,0xc0081f801fc00fe007f0,0x1fc00fe007f003f801f],#[0xe007f003f801bc0081f8,0xfe0057003f801fc00f,0x1fc00fe007f003f801fc,0x34d917217e013f003f80,0xfc00fe0040000003f801,0xe42fc01fe004f002b801,0x7f003f801fc00fe00722,0x7802fc00d605c017e00,0x6c017e007f003f801cc,0xfc00de05c0176018015e,0x803bc00fe007f003f801,0x8716f03e038421a6bc0f,0x3de07c01ce75cf781f00,0xfe004c618bfc01fe0057,0xc00de007f003f801fc00,0xe013f003f801bc0d8026,0x3ae7bc0f8049ceb9ef03,0x7e007f002b9ef03e00e7]]
def g223H6 := limbs80 #[#[0x1a05839db53103866c4,0x1049c0000c9839440,0x5200001a438c60,0x189d4430027037810,0x54458600000800000000,0x801fa8fcd0000a04480,0x29a6000b2a648319000,0xd0380]]
def g223D7 := limbs80 #[#[0x40483d29755954250120,0x954250120f2a5d965509,0xa5db6550940482da9a75,0x482da9a7d954250120f2,0x4250120e6a6197550940,0x9975509404839ab865d5,0x39a986dd54250120b6ae,0x50120e6ae1b755094048,0x7650940482da9a6dd542,0xa9a79d94250120b6ae95,0x120aea6a27650940482d,0x54940482da9a5dd94250,0x765515250120f4a5d954,0xf8a5956454940483d2b,0x940483ca976591525012,0x6195250120daa6596454,0xda69786549404832e996,0x483ca9755916250120a,0x16250120f2add5645894,0x5d565589404836ab9559,0x82ae9a85956250120f1a,0x250120baa69365589404,0x97558940482ae9a8d956,0x8e986dd56250120e3a61,0x120cdae578558940483,0x558940482ae9a6e15625,0x986e5562501209ea6939,0x20baae9186589404832e,0x8940483aaba461962501,0x4a196250120abae95865,0xaba6a28658940482ea9a,0x604832e98664b6550120],#[0x916258120f2a5d164589,0xa69d5458960483aab845,0x482aeaa85516258120b3,0x6258120e3ae157458960,0x177458960482ceba55d1,0x2ce9a5dd16258120e3ae,0x58120cbae57845896048,0x7559160482ae9a5e1162,0x7b95dd56458120b2e693,0x1209ba68b95591604834,0xd91604834e97564b6458,0x8564b6458120d3add592,0x9bae9592d91604832eb,0x160482cbba45d7645812,0x6617655120b1e694965d,0x2e682765d1644821fba0,0x448317895e418759120b,0x8865d120c1f619952197,0x5d565509404820ffa961,0x83ea9765954250120fca,0x250120f6a5d965509404,0x96550940483eaa765954,0xda9a75954250120f6add,0x120bea69d6550940483,0x550940483daaa7595425,0x976d954250120beae9d6,0x20bea69f6550940483ea,0x940483da9765d542501,0x65d54250120f6a9d9755,0xeeae197550940483ba98,0x40482faba65d54250120,0xd54250120f6a61975509],#[0xa2997550940483daa865,0x483da9a65d54250120f6,0x4250120f6aa997550940,0x1b7550940483daba65d5,0x3daa86dd54250120f6a6,0x50120beae95765094048,0x7650940483ba9865d942,0xaba85d94250120eeae19,0x120f6a6957650940482f,0x50940483daba55d94250,0xa59d94250120f6aea176,0xbea6a27650940482fa9,0x940483f2976551525012,0x5515250120fca9d95454,0xca5956454940483f29a7,0x483f29855915250120f,0x15250120fca695645494,0x5d96454940483ea97659,0x83eaa765915250120f6a,0x250120f6add964549404,0x96454940483ea9965915,0xeaa965915250120dea65,0x120deae596454940483,0x4549404837a9a9591525,0xaa95915250120bea6a56,0x20beaea564549404837a,0x4940483f298565152501,0x66515250120f6a5d9945,0xeea6199454940483dab7,0x40483bab866515250120,0x515250120dea65994549,0xae9994549404837aa966],#[0x482faba45d95250120be,0x5250120f6ae917654940,0x9e7654940482fa9a49d9,0x2be9a89d95250120b7a6,0x50120beae91865494048,0x86549404836e99661952,0xaba461952501209faea5,0x120eda6958654940483b,0x549404833e9966195250,0x966195250120ebaa5986,0xcfa2a586549404833eb,0x9404833eba9619525012,0xa195250120bea6928654,0x7a69e8654940482f69a5,0x482be9a8a195250120b,0x952501209fa6a6865494,0x59564589404833eb96e1,0x83da9755916250120faa,0x250120f6add564589404,0x564589404837ab955916,0xea9955916250120faa5d,0x120faae556458940483,0x458940483ea9a7591625,0x9656516250120faae9d6,0x20faad959458940483ea,0x8940483da97565162501,0x56516250120f6add5945,0xeeae159458940483ba98,0x404837a9956516250120,0x516250120deae5594589,0xa6199458940482faba56,0x483eaa866516250120fa],#[0x6250120f5a5d56558940,0x19655894048376b95595,0x3aeb865956250120eba6,0x50120afa6a1655894048,0x6558940483ea9a459562,0x69855956250120f9a5d5,0x120f9ae556558940483e,0x58940483ae9a85956250,0xa85956250120bba6a165,0xbbaea16558940483aea,0x940482ee9a8d95625012,0x5d56250120beae917558,0xbae997558940483ae986,0x483daba45d56250120b,0x56250120f3a619755894,0xa1975589404839e9865d,0x839eb865d56250120f3a,0x250120f3a29975589404,0xb7558940483ceba65d56,0x9e986dd56250120f3a61,0x120f3aa1b7558940483,0x5589404839eb86dd5625,0xa866156250120eba6198,0x20eba6998558940483ae,0x8940483aeaa661562501,0x5e156250120afae99855,0xafa69b8558940483b6b9,0x40483ae9866556250120,0x556250120afaea195589,0xa61b9558940482fa9a4e,0x4837a9a4e556250120eb,0x6250120dba61b9558940],#[0x1b95589404833e986e55,0x33eb86e556250120dbaa,0x50120faae91865894048,0x8658940482eeba561962,0xeba56196250120ebae61,0x120eba6958658940482b,0x58940483aeba56196250,0xa5a196250120ebae9d86,0xafa6978658940482ee9,0x940482faba4661625012,0xe616250120bdae959858,0xea6519259540482fa9a4,0x483ae9866496550120d,0x96550120cfa661925954,0xe9175595404833ea9864,0x83c79765d56550120bce,0x550120f1e9d975595404,0x97659540483a79865d56,0xebba45d96550120bbae8,0x120b5ee957659540482,0x659540483ceba25d9655,0xba55d96550120f2ee917,0x20bba68a7659540483c7,0x9540482eb9a49d965501,0x89d96550120b3e69e765,0xb5e6977659540482af9a,0x404825f9a9dd96550120,0x5d6550120b3ee9997595,0xee9197595404827eba26,0x4823fba865d65501209e,0x6550120d7ae899759540,0x9997595404835bba465d],#[0x25fba665d6550120d3ee,0x50120c7eea1975954048,0x9759540482cf9a6a5d65,0xb9a4e5d65501209fa68b,0x1208fe6a397595404827,0xd95404837a9a464b6550,0xa45db6550120dba61992,0xf2ee9176d9540482ebb,0x5404834fba95db655012,0x65f65501209eee9197d9,0x6e5db945d5404835bba4,0x4827b9a6e517550120d,0x97550120b6ee91765d54,0xe59765d540482d7ba55d,0x82de9a29d97550120d3e,0x550120b6e692765d5404,0x2765d540482d79a59d97,0x5b996e517550120a7e6a,0x120b6e69b945d540483,0x65d540482dbba4619755,0x9a2a197550120e6ee918,0x20b6e692865d540482de,0xd5404829f9a8a1975501,0x1259755012097e6a6865,0xb6e690965d540482df1a,0x404834f9962597550120,0x597550120b6ee91965d5,0xe692965d5404829fba86,0x4829f9a8a597550120b6,0x7550120b6ee9186dd540,0xa586dd540482d7ba561b,0x39bba461b755012097ee],#[0x50120e5ee9586dd54048,0x86dd5404831fba961b75,0xb9a4a1b7550120b7a68a,0x120a7e6a286dd540482d,0xdd5404825f9a9a1b7550,0x94e497650120d6ee9196,0x9fa697925d9404837ab,0x9404837aba2e51765012,0xe5176501209ee697945d,0xeee1b945d9404833b986,0x4827b9a4e617650120c,0x97650120f6ae53925d94,0xe8b945d940482de9a5e4,0x835b995e517650120f6a,0x650120d6ee57945d9404,0x9955d940482db9a5e517,0xdbba46557650120b7ae8,0x120a7eea1955d940482,0x85d9404835bba4e55765,0x9a464a7650120b6e6939,0x209fae95929d9404837a,0xd9404837a9a265276501,0x465e76501209eee95949,0x97ee95979d9404835bba,0x404833eba26627650120,0x5162581208fee95989d9,0xa6995458960483ea9645,0x482eeba65516258120bb,0x6258120b7a69d5458960,0xd56458960483ea974591,0x3ceb755916258120f3a5,0x58120ebae15645896048],#[0x6458960482eeba559162,0xeba75916258120bba69d,0x120bbae997458960482e,0x589604839eb855d16258,0xa65d16258120b7ae9574,0xf3ae997458960483ce9,0x9604839eb85dd1625812,0xe116258120b7a6977458,0xfa69784589604833eb95,0x483ea9745516258120a,0x16258120faa611545896,0x69d5458960483ce9a755,0x83ceaa75516258120bba,0x258120bbae9d54589604,0x15458960483ae9a85516,0xaeaa85516258120bba6a,0x8120bbaea15458960483,0x458960483ce9755d1625,0xba55d16258120ebae157,0x20f3a6157458960482ee,0x8960483ceb855d162581,0x55d16258120f3a695745,0xf3a2a17458960483ceba,0x60483ce985dd16258120,0x116258120f3ae1774589,0xae158458960483ae9856,0x4836eb956116258120eb,0x6258120bbae958458960,0x9784589604836eb95e11,0x3ae9a5e116258120bba6,0x58120eba69f845896048,0x54e0960483ea96455382],#[0xa9945538258120eea611,0x120bba69954e09604837,0xe0960482be9a85538258,0x7459382581209fa6a554,0xeba61564e0960483ea9,0x9604836e995593825812,0x5d38258120bbae9564e0,0xfa65584e0960482eeba6,0x482beba56138258120c,0x954581209fae9594e096,0x6599255160483ea96464,0x836ea966495458120dba,0x458120cfa66192551604,0x964551604833ea986495,0xcb9975915458120faa68,0x8120f2ea5d6455160483,0x455160483d39755d1545,0xba65d15458120dae6597,0x20beae898455160482eb,0x5160483b398561154581,0x76595458120baee91965,0xd3ea5d96551604834f99,0x604825fba76595458120,0x595458120dba68996551,0xe29d96551604836bba46,0x4834fba76595458120d3,0x5458120bba68a9655160,0x5e9655160482eb9a4a59,0x34fa97a595458120d3e6,0x581209be6a6965516048,0x96551604827e9a2e5954,0xbba465d545812097e69f],#[0x1209fae899755160482d,0x551604826fba665d5458,0xa665d5458120d7ae8997,0xd3ee9997551604834f8,0x1604831f8a865d545812,0xa5d5458120b6e6929755,0xfa68b97551604825f9a9,0x4826f9a6e5d54581209,0x154581208fe6a3975516,0xe899855160482bbba466,0x826fba666154581209fa,0x458120aee69298551604,0xb98551604827e9a2e615,0xbab8464964581209be69,0x8120eae5978459160483,0x4591604839b975e11645,0x9a5e116458120e6edd78,0x20baee916559160482bb,0x9160482db9a4dd564581,0x2e556458120d5ee57755,0x9fae8997591604827e9a,0x6048277ba565d6458120,0x4964581209fa68b97591,0xae119259160483ea9746,0x483eaba46496458120fa,0x6458120f3a5d59259160,0x159259160483ceb75649,0x36e9956496458120ebae,0x58120dbae55925916048,0x7459160482eeba564964,0xbb855d16458120f2e5d5,0x120daee557459160483a],#[0x59160482ebba55d16458,0x75e116458120f2ee5d74,0xf2edd78459160483cb9,0x160483ab985e11645812,0x5d56458120bae6978459,0x1ee577559160483cb9a4,0x482eeba26156458120f,0x56458120baee91855916,0x68b9559160482cfba765,0x836e9a2e556458120bba,0x458120bbae8997591604,0x59759160482ebba465d6,0xee9a2e5d6458120b9ee9,0x8120dba5d592d9160482,0x2d91604836e98564b645,0xba45d76458120dba6959,0x20d9e65575d9160482eb,0x9160483cbba45d764581,0x96176458120bbae8985d,0xdba68995d91604826fba,0x60482dbba45d57458120,0x157458120d3ee59755d1,0xe697965d16048337b95e,0x48357b95e1574581209b,0x7458120e5ee57855d160,0x59955d1604834f896655,0x2cfba66557458120d3ee,0x58120b3e694965d16048,0x965d160482cfaa825974,0x7ba56597458120b7ae89,0x120b3e697965d160482d,0xdd160482dbba46177458],#[0x85e49845812097eea585,0xcfae1792611604833e9,0x1604827e9a5e49845812,0x65784581209fae8995e1,0xfae8995e1160482beba2,0x4483ba9746098055120c,0x98055120e7a5d9826015,0xe5982601544839eb7660,0x838f9865d98055120cfa,0x55120e3ea1976601544,0xa86601544832fb966198,0xbb9a4a198055120afa68,0x5120cbee5a8660154482,0x5d9544827b9a4e41765,0xb87e417655120cbe61b9,0x208fe6a3905d9544831f,0xd9544828ffa661d76551,0xe1d765512087f6a5875,0xa3f69b875d9544829f9a,0x544823fba06617655120,0x6176551208efe91985d9,0xe693905d9544821ffa76,0x4838f986e417655120b6,0x7655120c7e263905d954,0xa3905d9544831fa98e41,0x2dbba06517655120a7e6,0x55120d4f655945d95448,0x865d9544831bc9865176,0xfda8a197655120b2f692,0x120a7e683865d9544828,0x5d9544829fba06617655,0xa06617655120a6fe9198],#[0xc3fe99985d9544831fb,0x9544821ffa6661765512,0xe617655120a7e682985d,0x6f693985d9544825bda4,0x44831f9876427655120c,0x27655120c6f61d949d95,0xe81879d9544831bf8765,0x828ffa661e7655120a7e,0x655120a3f69b879d9544,0x79461d544831bf866537,0x5bda6e518755120d4fe5,0x5120e7ae4b9061d54482,0x61d544831f896e41875,0x9a6e418755120c7ea5b9,0x20a7d6849661d544829f,0x1d544830fd9625987551,0xa598755120a7ee81966,0xc3fe5a9661d544829f9a,0x644825bfa66528755120,0x98059120eea5d182601,0xa5958260164483bab946,0x483aeb656098059120eb,0x8059120e7a5d58260164,0x5582601644839eb75609,0x3ae9766098059120cfae,0x59120eba9d9826016448,0x74601644837ab94e4980,0x7b855958059120f2e5d9,0x120d9ee556560164483a,0x60164482ee9a2d958059,0x85dd580591209beaa765,0xafa68b856016448397b],#[0x164482eeba25d9805912,0x9d98059120daee517660,0xf5d5655d164482ee9a2,0x4482cbda75957459120f,0x57459120b2fe9d655d16,0xe57655d164482eb9a0d9,0x82cbda7d957459120d8f,0x459120d4fe55755d1644,0xb855d1644838bd76e157,0x4bd76e557459120e2f9d,0x9120d2f9db955d164483,0x65d164483cbba05d9745,0xda59d97459120b2fe957,0x209ee6839459564482cb,0x95644834bd76e5165591,0x45d9655912096f69f945,0xb2f6937659564482cbfa,0x644828fda8dd96559120,0x516559120a5fe9587595,0xf65f9459564482eb9a0e,0x482cbda7e516559120d2,0x6559120b1fe958759564,0x818759564482afba061d,0x387fa561d6559120e3ee,0x59120b1f696875956448,0x87595644824fda9a1d65,0xbfa461f6559120abe683,0x120b1fe9587d9564482c,0xd95644824ffa961f6559,0xa061f6559120abee8187,0xe1fe9587d95644838fb,0x5644830ffa961f655912],#[0xa1f6559120b2f69287d9,0x3f6a687d95644828fda8,0x4482af9a0e1f65591209,0x97559120d2fe9197d956,0x682765d564482c7fa55d,0x82c7da59d97559120b3e,0x559120a5fe95875d5644,0x7875d5644829f9a0e1d7,0x3f9a0a617559120a5f69,0x912087f69e985d564482,0x45d5644834bd96651755,0xda4e597559120d2fa599,0x20a6fe91985d5644825b,0xd5644825fba066175591,0x6e61755912093fe99985,0x87f69b985d5644824fda,0x6448353f856537559120,0x177559120d1f65b85dd5,0xe68385dd56448317d98e,0x48317d96e177559120e5,0x7559120c5f6a785dd564,0x9196dd5644825bfa465b,0x31bfa46637559120d2fe,0x59120c5fe9598dd56448,0x87615644831bf94a1d85,0x7fa55db8559120a3f69a,0x120a6f69287e1564482c,0xe15644828fda6a1f8559,0xa465f855912087f6a687,0xcfa64990e15644825bf,0x5644833eba2643855912,0x5db8559120abee8176e1],#[0x3ee8176e156448297fa5,0x448387fa55db8559120e,0xb8559120abe68276e156,0x6a776e15644828fda79d,0x823fba065f855912087f,0x559120c7ee8197e15644,0x297e156448317fa565f8,0x8fda6a5f8559120a6f69,0x9120c6fe1f945d964482,0x5d9644836eb92e41765,0x9a5e417659120daee539,0x2096f697945d9644826f,0xd964483ceb92e4176591,0x5e417659120f2ee53905,0xf2ee83945d964482cf9a,0x644834bd95e517659120,0x517659120d2fe57945d9,0xee81955d964482cbda5e,0x482cbfa46557659120b3,0x7659120d2fe93955d964,0x91879d9644826fba5642,0x2c7fa561e7659120b2fe,0x59120d2fe91979d96448,0x94dd9644824ffa565e76,0xbfa4663765912096fe95,0x120c7ee8198dd9644825,0xdd96448317ca56637659,0xa56637659120c5fe9598,0xc5fe1f9561d644821ff,0xd644835bb94e41875912,0xe418759120d5e2579061,0x4f2579461d644834fb96],#[0x448353f95e518759120d,0x58759120d2fe5b9461d6,0xe5b9561d6448347f9625,0x8353fa4e558759120d1f,0x759120d1fe9b9561d644,0xb9061d644824fda5e598,0x3bb94e418759120cfae4,0x9120cde2579061d64483,0x61d6448337b95e41875,0xc95e5187591208fe6979,0x20c5fe5c9561d6448333,0x1d6448337ba0e5587591,0x2e418759120c5fe9f956,0xe5e2579061d644839eb9,0x6448397b95e418759120,0x418759120a7e6979061d,0xee5b9061d644838fb96e,0x48387f962558759120c7,0x8759120c5fe589561d64,0x999561d644829fba0655,0x397ba0e558759120a3fe,0x59120e1fe5b9561d6448,0x9561d6448317f96e5587,0x7da6e558759120e1fe9b,0x120c5fe9b9561d644831,0x61d644828fda5e598759,0xa465a875912087f69796,0x93fe9596a1d644834bf,0xd644833e992643875912,0x5d580d91208fee9590e1,0x6ee917560364482bbba4,0x4482beba265580d9120e],#[0x175d9120d2f5db945d76,0x5d9855d7644831bd87e5,0x82c7fa55d975d9120e1f,0x5d9120a5fe95875d7644,0xb945d7644823fba06617,0x1bd98e5175d9120d2f65,0x9120d2f69b945d764483,0x85d7644831bda8e5175d,0xfa466175d9120c7ee819,0x20cfa64990617644831b,0x176448387fa55d985d91,0x565d85d9120a6fe91976,0xa5f696976176448297fa,0x644828fda6a5d85d9120,0x5d85d912087f6a697617,0xee81955db644823f9a0e,0x482cbfa465576d9120b3,0x76d9120a3fea1955db64,0x819561f644828fda5e61,0x29bfa465587d9120a7ee,0x5d12096f69b945d57448,0x76e157448297fa55db85,0xbda49db855d120a7e682,0x12087f6a676e15744829,0x5d9744823fba065b855d,0x86e51765d120e3ee1b90,0x96f697945d9744838bf,0x9744828fda5e19765d12,0x652765d12097ee95909d,0x3f697869d9744825bfa5,0x44825bfa4662765d120a,0x9855d120d7ae4b906157],#[0x68486615744831fb9021,0x821fea9219855d120a7d,0x55d120c7ee4286615744,0x686e15744830ff96a198,0x5fba065b855d12087f6a,0xd120a7e68296e1574482,0x5219744825f9a0654865,0x9a0654865d120c3f6199,0x20e3ee81862197448357,0x197448387ca5618865d1,0x9618865d120e1fe95862,0xd7ae4b90619744830ffa,0x7448357895e41865d120,0x55865d120d5ee5790619,0xf69786a197448357ba0e,0x4829bfa465985dd120a3,0x85dd120a5fe959661774,0x9696617744829f9a0a59,0x21fda9a5985dd120a5f6,0x5d920a6fe919561b7448,0x84e01764833e994e0b80,0x7ba5613805d920afae89,0x920cee65384e0176482b,0xe11764823fba5653805d,0xa0657845d920cfae4b90,0xd7a65382e01764823fb,0x176482deba2613805d92,0xe13805d920b5ee9584e0,0x7ee9594e01764835b994,0x64835eb92e41845d9209,0x1845d920d6ee53906117,0xe57906117648357895e4],#[0x834fb96e41845d920d5e,0x45d92097e69790611764,0x8956117648353f942558,0x47f96e55845d920d1fe5,0xd920d5ee839561176483,0xe117648347fa6e55845,0xda4e17845d920d7ae4b9,0x2097ee8195e11764829b,0x276482beba2651809d9,0x2641849d9208fe697946,0x8fe68395612764833e99,0x764829bfa465d849d920,0x51879d920a5fe9597612,0xf6979461e764829fba06,0x4829fba065984dd92087,0x84dd920a6fe919661376,0x5564e016258297fa5659,0x2afba55938058960cbe6,0x58960afae8974e016258,0x95dd1625823fba565380,0xe974dcb805896097be89,0x960dba65372e0162583c,0xe0162582eeba25d38058,0x956138058960ebae8984,0xabee9584e01625832f9,0x1625836eba2653805896,0xe4174589609bee9594e0,0xbae83925d1625836eb92,0x25834ed75e497458960d,0x97458960d3bdd7925d16,0xe57855d1625826eda5e4,0x826efa26577458960c9f],#[0x458960b3be8995dd1625,0x5855d3625834efa26577,0x2fda5e6174d8960c9fe5,0xc960abee819561362582,0x4e0172582b7ba5613805,0x994e13805c960abee998,0x60c5fe57855d1725833b,0x137258317d95e17745c9,0x265584dc960a6fe91856,0x806300a2009800029efa,0xb808900f601aa02bc044,0x3a606c80c6016b029404,0x825a045e088810581f40,0x3017802d405660a48138,0x76c0e401b7834e06640c,0x44c085610141f203d20,0x5c27884cb09541224234,0xb7816802bd05540a7014,0x86480c5818682fc85dd0,0x2437686c70d4c1a00334,0xf341dd03b387500e5e1c,0x8260ff61f683e687ac0,0xd4451888710d62164421,0x29624bc48208ed11a222,0x9d7138026a44bc89621,0x105390a56144c2850501,0x6342c0c5738acb15682a,0xbb017282e085ae0b4a1,0x246190c1b17fe2fb45e6,0x91431e06358c6318b631,0xcc6197c32b064d0c921,0xf06928d0e19ee3380667],#[0xb4a364c6be0d651a9c34,0x8deb1ba837086da8dad1,0x2071d8e2e1c3838286fe,0xd303a407440e801cd239,0xef71db63afc7590ea51,0x687ba0f5d1e823ca8787,0x243fec7f20fcd1f583e,0x109420f04170825102e2,0xb087210d2219442e0853,0x2a0450c896111021fc43,0x1196230845f08ba11622,0x88f591de239846fc8d4,0x49048ec9149212241448,0x128424ee499492e92552,0xac96a12c225604a8c94b,0x6a84d08998131e25fa4b,0x93b827424e149bc136b2,0x1ca1f942d28044f989e7,0x9425228a3e946628a851,0x14f629be5348a6294b32,0x24a9e152f2a445454a7f,0xb0a55f4aba956d2ab655,0x15bc2b545688aca958d2,0x64b0615ff2bda5780ae7,0xcaa5920b1d962e2c4c58,0x96af2d445a40b41966c2,0x58b8496f72dd45b4cb60,0xe9a5d00b9c172b2e465c,0x97982f205e0cbb897642,0x98bec97cc2f7e5ec8bd2,0x4e6068c0698002fe65f,0x185430986110c1e182f3],#[0x88c48187e30e261a4c2e,0x1e46394c6998c6315e62,0x994232606464c8898ff3,0x68cc6998032dc6584ca7,0x3de6788ce599be334e66,0x1a5334646894d099a063,0xd8d6d1abe353a6a04d35,0x7186dc0daa1b2e36246b,0x9c0e37f86f6cddd1ba33,0xd8e4f9c7938b07104e12,0xa707484e829cee39b872,0x9dc43b507630eb09d4a3,0xb0f281e393c3077b4eed,0xe0e7b84f601ea43cfc79,0x1f703ec67d44f9f9f193,0x48fe29fb33f427e50fc1,0x30802cfff1ff13fbe7f,0xa06d40c0813901ba0254,0x8d06620c44164824503f,0x26684ad08ca10c41fe83,0xa17942d885690a6a1454,0x810e9a1c6437c869d0ca,0x442882910121f543d087,0x226c44be892111da22e4,0xc1151a296451c8a0513a,0x5d88b9116ba2cf45848a,0x232d464a8c7518823034,0x791c8a37f46c68d4519d,0x7e68f711e2a3b847568e,0x2466489490b920e240a4,0x49262a4b34942922923c,0xa44944127f24ec49be93],#[0xa57c4ad4952529e252f4,0xdd2eb25ba4b50966d2c4,0xc9898fd319261b4c1c97,0x26974d1e9a0933826594,0xbd36ea6d04d729ac5352,0xe7e9ca138da70e4e029b,0x27804edc9d853a7a7474,0x9d3ed27c84f629e7d3c9,0x5aa08140c280b4ff29f,0x285f50a4a11541ea8355,0xa144b288e5102a1d1436,0x1f0a38546a28cc5174a2,0x293e5262a47d48929055,0x1d4bd296d52c0a54d4a3,0x37ca6c54d2299c531ea6,0xa9f553daa7814ec29cb5,0xd1513aa1f5424a8154fe,0x4eaa9a152daa4e5482a8,0x2ab65548aa49542aa7d5,0x4d580aaf455d8ab69564,0x6e4ad955a9ab415668ac,0x2bc7576aae8d5cb2b8e5,0xcd610ac0f57faaf995ea,0x8e8b1b162fac52588ab0,0xacb5595ab281644ac815,0xd1673acdf59a4b32965e,0xa7eb4b5692ad185a0cb3,0x2d805ae6b5996acad4c5,0xd56d42da05b30b6416c4,0xbceb77d6e92dca5b84b6,0xae285c36b84d700adef5,0xd97322e575c94b90971a],#[0xd5aba9574c2e8b5d06b9,0xaedf5da4bb297612eb55,0x79788af095df8bbbd773,0xeaabd357a02f335e56bc,0xaf9b5f1cbdf17b7af5d5,0x557e6afc05f70bec17d1,0x36c04d8032ff95fcebf,0x305c60a8c109815b0236,0xd1853b0906110c1d9832,0x1ccc379868b0c46178c2,0xb11d6220c3f987b30ee6,0x858aa3142626ac4b5892,0x33ac6418c4317b62e6c5,0x31cf637ac6d58d6b1a56,0x75905b1f963e2c7918ee,0x4dac981927323c6454c8,0x32a46538ca3d94132756,0xb596db2d36582cad1956,0x652cc71987b30265eacb,0xb36066a6cd1999f33316,0xa59ce338a66facdd59b6,0x7e8cf899eab3c86776ce,0xb4356850d06da0734066,0xda3db47368ccd165a23,0x96ad2b5a52b49d6920d2,0x34e769b4d349a62b4bd6,0xc1a9435206a26d405a7a,0xab0d541aa435406a70d4,0x35996b0ed5e9ab435606,0x9daed35cd6b80d6b9ad3,0xc6ed8a9b0eb6106c06d7,0x36786cccd965b2636446],#[0xddb55369d6d2ada35b40,0xdf0dbc1b6f36d16d88da,0x372f6e4edc7db8937056,0xb9bae37546e98dd11b9e,0xf4ade75bc5b7836ef6dd,0xb7dc6fa8df31bdfb7ad6,0x95c0eb8107006dfd9bf4,0xaee13dc23b83a7064e0,0xb88470f8e1d1c3638647,0x35c62b8b87156e279c48,0x23ae42dc7cb8ec71aae3,0xb94f7284e4e9c99392a7,0x4dcc3397972e2e591cab,0x380e6e1cd839a37336e6,0x1c0681473e4df0fc83f,0x8820051d3937c373fc84,0xd73fc3f20f937c3f2060,0xcf937c3f20e0882074e4,0x81d73fc3f20e0882074d,0x521773fc3f20d0502485,0x8281805dcff0fc8282b0,0xcff0fc82a17055cff0fc,0x81805815f0fc83217055,0x381586616f3fc3f20d73,0x830220801474e4df0fc8,0xc3f20c0864c74fc3057c,0x1ff0fc8201406016f3f,0xf0fc8101e857c3f20885,0x208015a2d4df0ecff211,0x7c3f20c05ecff0fc8202,0x3015f0fc836ce07017d3,0xa824f3fc3f20cb3817d],#[0xc82824853cff0fc82a14,0x7c3d37c83822f3d17f0f,0x368bf0fc8281dc101a05,0x9022055cff0fc8302dd,0xc838240801d73fc3f20c,0xfc82c15738240774df0f,0x37c345fc81f4d055cff0,0x3f20e05dcfd3015f0fc8,0xc3f20c063160881573fc,0x815f0fc8282dd368b73f,0x902005e8bf0fc8302005,0x83615d301cf3fc3f20c0,0xc3f20fa282405117f0fc,0xfc3f20e09017d3705a2f,0x4fc3f20c0b0240858bb3,0x9021f0fc82818058151,0xe0b5cf73013f0fc83818,0x22055cf73021f0fc8382,0xfc83029053cff0fc828,0x737c3f20b73022083cff,0x408820f3fc3f20d053cf,0x819f0fc82bcff0fc8181,0x578a085cff0fc83020f3,0xff0fc83ecdf0d15f2080,0xcdf0fc83314096cc06dc,0xecc457c3f20e0691514e,0x83cfb37c3f20a08820f3,0x8014f3823b37c3f20e0,0xc8221773f8bf0e53f20c,0xfc83fc3f20404fc20a7,0xf3fc81a1605815e2953f,0x5d378af1f85f0fc037c2],#[0x81df081a057c037c3f20,0x860a05605f0dcff01074,0x201474a0df0fc028220,0xb73dc3f00673e0b817c,0x17c3f00a055ce837c3f0,0x3f00b73fc3f0078284d8,0x15f0821f00b8284d811c,0xfc04022087c3f008088,0xf00a74e0473c4c935c2f,0xdf0c15f00873c4c933c3,0x7c3f0120ac15f0fc0201,0x80701a0601782dcf81,0x33c2277c02025f0a17f,0x885814f189d933c3f011,0xbc3937c01e4df0fc01a1,0x6a188581473e4df0fc04,0x19cea2a17f0fc0281c0,0xaf3e05f0fc04a8af0fc,0x5c282fc020220801805e,0xf00a7482170815f00a08,0xf937c3f009811d3a2fc3,0x1885814f3e4df0fc04bc,0xfc03e4df0fc01822082,0xf02161818059cf82e047,0xc0285f05fc2857c02fc3,0xa14f0fc03416053c217f,0xf00b537c3f0060781c45,0xe857c3f00806a8bf0917,0xfc3f006087c2857c0205,0xc01fc3f005f003f003b3,0xf0fc01fc00fc00817f0f,0xfc00fc00905f0fc01a05],#[0x7c19f0fc0228a45fc01,0x1df0fc02419417c3f008,0xfc0181d067c3f009060,0x3f009413c245fc02504f,0x608217057c02014067c,0xdf005f003f00208015f0,0xfc205fc02020057c0181,0x1821f00408017f007b3,0x7c01017f0fc01a8bf0fc,0xb3a8bf0fc03017f00407,0xc0082007017f00808017,0x7f004077c017c00fc00f,0xc15533c3f00a05fc0101,0xf008093cfa2fc3f00b05,0x6f3a8bf0fc02815a2fc3,0xfc3f00a0afc2857c0201,0x3bce08fc3f00845bce08,0x182408816053cef0fc0,0x18f3d05f0fc03215f0fc,0xfc02023417c3f008088,0x2c19417c3f00846c19f,0xcff0fc02c18f3823f0fc,0xfc02d04f0fc01823063,0x53cff0fc02823a2d04f,0x29417c01a8b417c01818,0x70fc01fc00f4df0fc018,0xfc0180bf0fc01fc00a0b,0x201c34fc2857c02a15f0,0xc01823f0040b11bf0fc0,0xfc0088bf0fc01a0bf0f,0x160afc01821f0fc01fc0,0x182bf004077c3057c022],#[0xc3f009f0fc010140afc0,0xf1fc027c00fc0081d73f,0xc3f0040502bf00627014,0xdf007f003f003f0fc017,0x7c20b7c01823f0057082,0xdf0fc0180bf00408fc01,0x81df0fc0200bf0fc01f4,0x73fc3f00c07017f00773,0xc01a0bf0fc0182206015,0xfc027c2c5fc01823f0f,0xa02fc01317f00522a0bf,0xfc3f0080968a05fc3f00,0xf00805c8af0fc02020f3,0xcf3e8bf0fc02c16f3fc3,0x208534da2c17f0fc0402,0xf005f003a2fc3f006090,0x8bc17c0268a057c0181d,0x5915b3fc02019f00545e,0x5b390bf00645fc3f0064,0x28cff00806fc0100bf00,0x40741bf0fc027c008d3c,0x164df004087c01021f00,0x21f00608015f006087c0,0x3f003f003f003f002088,0xc2fc01fc0080df005f00,0x4c02fc0180dc2fc01816,0xf0040ab4df007d37c017,0x7c00f4df004037c0102b,0x802fc0100df00405fc01,0x17f0fc02022c17c3f00,0x102a087c01821f00408,0xdf0060800df0060afc],#[0x37c0102a0914df00808,0xfc0164df00407a4df006,0xc017c0081ff005f0020a,0xafc0102a0914df008077,0xc00825f0040aa0df0060,0x37c0101df004097c017,0x5c7f004d37c0174df004,0x4037c0174df004d37c01,0xf0047002057c0100df00,0x17c00fc00bc00fc0080d,0x7c0180df005f002057c0,0x5fc01117057c0181403,0x6037c0154cc17c3f008,0xc17c01021f00408705f0,0x7c3f009f00362c15f007,0x37c0101e537c01a1553,0x7c01f4df0040a80df006,0x100df005d37c0102ad3,0xfc01022c17c3f008d37c,0x857c0154cc17c3f00805,0x7d37c010200500df009,0xa2fc0378bf0040800bf0,0xb811c3f00808820091cf,0x813f00b811c2057c0260,0x5605f0853f00d73dcdf0,0x29cfa2dc2097c02e0a0,0x2170fc0282473e8b70fc,0xe04731c2097c02e8ac10,0x28240601673e0470fc03,0x3c17c029cd82e05f0fc0,0x973305f0fc021cda29c,0x4bcef0fc035cdf0e53f0],#[0xa2f04f0a53f00c060160,0xcff0fc02305f0fc01815,0x90628b417c3f00a04b,0xf081773fc03019737c3f,0x60868bf0dcff00e06015,0xfc03815737c3f0080901,0xfc0182e0b60a14e05f0,0x3f00b8105270fc025cdf,0x2da2fc3f008085cc82fc,0x108a70fc025cdf0fc018,0x81452949cd70bc3f0118,0xc029ce0a415f0fc029cf,0x827f0fc025cd06417f0f,0x94fc3f01104fc3f006f3,0x7f0fc0302e0b41905bce,0x1804fc3f008051cd0641,0xfc01bce7368bf0fc028,0x7348aa2dc2f0fc03821f,0xc033c322dc2087c029ce,0xfc3f00e0b1cf7368bf0f,0x6fc3f00609015a2dcd05,0x981b73099f0821f00e8,0x4053c3f006087c3f006,0x5fc01820067c01821f0,0x60b88bf006017c01020,0x87c01153f0040b00bf0,0x7c0101bf00406821f006,0x7f006067c01019f00401,0x7c0182e267c3f0080701,0xb310bf006087c0102fb3,0xcec17c3f00d27499f007,0x27c00913f0fc0182408e],#[0xe057c3f00a33f0a337c0,0x605fc01017f00505ec,0x244ecdf007f002338cdf,0x1305f0fc01f0bf005f00,0x609824e4305f00a09fc0,0xecce2fc3f00809825f00,0xc00ecdf00404fc017c00,0x27c0080bf004057c017,0x7c0102df0040b020c2fc,0xb02a0a7c023c7f0040b,0x404fc017c00fc3f004,0x8bf00402fc017c00821f,0xf0020b7c0102ce2fc01f,0x99417c027c0080bf005,0x3f002097c01021f00409,0x2813f0fc02027f005f00,0xe017c3f00be2fc3f007e,0xc1c2840580bf006865c,0x9417c01115f005c17c01,0x825f0fc02018097c3f00,0xf0fc01824f3fc3f008f3,0x4f0fc02d04f0fc01d05,0x8230618bf0fc02824b35,0x2417f0fc0182af0fc01,0x605fc3f00705fc3457c,0x87c01013f00514bc3f0,0xfc01826087c01821f004,0x6fc0178bf0fc0182bf0,0x7c3f00c09fc01027f004,0x1025f0fc018228618a09,0x5f005c1021f006087c0,0x6915f0fc02823c17c01f],#[0xb02662fc2087c032cc0,0x9f0fc0102608fc3f008,0xf005f0fc0111a057c3f0,0x2209fc3f0080b7c0102d,0xb0020a7c0102b94fc018,0x8f003c15c0102df004,0xbf0060a7c01216853c7f,0x705f005f0829f0060b02,0xa0a7c02552700405fc01,0x718bf007f00270020b02,0xc0182c02fc0180bf0040,0x800bf00602fc0101a067,0xc07fc01b4f22c85f0080,0x7d3485f007d37c0174,0xc017c0081ff005d301ff,0x5f005f003f003f002057,0x17c00805f00530340101,0xfc01fc00813f00400fc0,0xfc01f85f0fc01805f0,0x5c00508057c017c00f84,0x1105f005703401021d3,0xd4df0045394df007d3fc,0xc0100bf004057c017c00,0xf003f0fc017c3f005f0f,0x4037c017c00803f005,0xc0080ff00404fc0134df,0x5f003f003f003b014017,0xf005f002037c0114df00,0xfc01185f005703c01185,0x3f003f0fc015c7f005f0,0x1c8b217c0180df005f00,0xc01c8b217c01d8b217c0],#[0x17c0089c26fc01c8b217,0x85f00d22c85f007217c0,0x605fc0101805f4d22c,0x1f0040901bf0065368bf,0x7c008240828bf0fc0282,0x9f0062128bf00606fc01,0x20a2fc01821f0040801,0x13785f0060ae4de17c02,0x685fc3f00786617f006,0xafc01785f005e17c3f0,0x3e17c017c00f85f004,0x3e17c01452e164df009f,0x17c0090df005f003f00,0xfc0180ff005f00393fc,0x2437c01026087c0180fb,0x16cff00403e4df007f00,0x403fc012cff005b3fc0,0xc00fc00fc00fc0080df0,0x80ff005b3fc017c00f,0xf003f00203fc017c00fc,0x20ae4df00608821f007,0xff005b0fc01025f005f0,0x1803f004017c017c0080,0x5f00204fc01152537c0,0x5f003f003f0fc017c3f0,0xafc017c00fc00803f00,0x3fc017c3f005f003f002,0x3f0fc016cff005f0039,0x3f003937c0100ff005f0,0x180ff00465003f007f00,0x5f00202fc0118a617c0,0x2657c017c00fc00e4df0],#[0x3805f00665003f007f00,0x3f003f0fc016cff005b,0x182208185f009f003f0,0x87c01fc00fc00820d37c,0xc027c00821617c018220,0xfc0094df0045378bf0f,0xfc00b4df005d37c017c0,0x22087c01fc00fc00fc00,0x5f003f003f003d37c010,0xfc0100ff0fc01fc3f00,0xc3f005f002f0cc0f007f,0x3f003f003f0fc017c00f,0xf005739cff007f003f00,0x7f002617c017c00b4d,0x5f005615c0f007617c37,0xf84f0bc01f85f0fc0180,0x5f002f0fc015cee2fc01,0xbcff005703c017c3700,0x6f0fc017c00fc00fc0,0x3739cff007f00373fc3f,0xf00473fc013c3f005f00,0x803f005f002f0fc013c3,0xc01185f005d37c017c00,0x180bf005f003f003e2f,0xf85f007303401785303c,0x5f005937c0164df00414,0x825703401825703c0180,0xc0174df005f0fc017c00,0x8821f00662985f007f0f,0x3f00204fc017c3f0040,0x3f002017c01003f005f0,0x3f005f003f003f003f00],#[0x11d3f005901c017c00fc,0xbf00474803f00674fc0,0xc00fc00fc00fc00fc008,0xc01fc00fc00fc00fc00f,0x3803f007b0fc01116457,0xd200fc01fc00dc0b0040,0x73fc011d3f00403fc011,0x27f005d378be17c3f00b,0xb1fc016c7f005b1fc010,0x5f0dc017c00fc3f005,0xc017c00dce73fc01dc0f,0x1013f005f003f003f0f,0x5217c017c3f00400fc,0xc017c00e85b01c01a85f,0xf00202fc01185f00402f,0xfc00fc00ec07005f003,0x3c016cdf0dc01fc00fc0,0x2b37c3f007f003f00370,0xf005739cff007f003f00,0x4037c017c00fc009cf,0xc01185f00402fc01005f,0x17c00fc3f005f00202f,0xfc3f005f003f00200fc,0x37c017c00fc00fc00fc0,0x4bf004a17c0114bf0040,0x3f009f003f00208fc011,0x585f006097c01685f082,0x94bf00552fc3f00608,0xf00209fc017c00fc00fc,0x5f002097c01021f005,0x5f003f003b01c01027f,0x1f0fc017c00fc00d40b0]]
def g223H7 := limbs80 #[#[0x80b03c480000e03834,0x10000140b0302900002,0x12001020090140e03009,0x7400034000040001c2b,0x5c1a00c050000200414,0x1034000200a0004d,0x240a008050a00601804,0xc030940b0284f00002,0xc0611c040080d0100b,0x241f0181e0680100038,0x100002809024000a800,0x18020341f0880c11c14,0x80b01c1507c1a0e40b,0x13018010181102017,0x2fc00000470040a0181e,0x14c00004360180601806,0xa1d8130080009003,0xc03f028050200f01405,0x5841018070004301c00,0x205709c0100c0300403,0x580f0c40101c4303006,0xc0d80f0203914c05,0x1640c11c6b0780003401,0x120110040603c010b805,0x9e10e0241b474001286e,0x17c00184000140c06416,0x741a1200a0745c10c0b,0x405200002c1200396c04,0x28408200002e607638f7,0x1c0c900141c2da500,0x93397204372394750280,0x45a50b5804918b382d47],#[0xada46938e2e4fba01841,0x54ecd0083c095c396,0xd33c3cc6c23978406500,0x1b000019a4c980cdda40,0x804c910f01a4d8043f99,0xa0df6330080f282ba5,0x18023733200000000,0x565127ccf50301800000,0xce110f50123b0c0520d,0x2d4516511cc11764239e,0x25580fb0319b50210000,0x60c238e81d1,0x626024a4a21f83700000,0xc109c2a9b00490000180,0x1cea500001261e82822,0x1165266f2134ac874000,0x7640ab4e4900003da49c,0x49b751875a53b0485409,0x7ccb1003890c1eb29f8c,0x9da80c4b0c3b4e45109e,0xb3193c474f331cc09df6,0x2539b9b943b30316029f,0xe3eb6451ccfb7217424,0x24a16343fd5472651ea,0x33e750e8d98f660cf000,0xf103be88bfd33c963007,0xa5506493c2c14342f40a,0xd447ad41b4cced000019,0x9c6c06c7029184286021,0x914580432569bec30b03,0x2104248c496221f49a67,0x2400f330cc0e32838e84],#[0x1980a063a9c008e20b8e,0x1cb430282acf40c3810,0xf401af4a24982bf80bbc,0x48000004c2400001407,0xc00007122d8284c12a55,0x9191aa6900424c2d9042,0x9039bc2d9d1168000053,0x24c01aa9a51100020cb3,0xa4e4a40820a0a0407c26,0x5cc4d1c03e40000399fa,0x51ef00d80000104ad390,0x75178d457501db0eaab,0xe33de8110000000e7,0x71c2500153949c703c40,0x207849ab0338000d8227,0xf10a920d4e448c0e53c0,0x541301dc11c63396ccd3,0xc105e0aac84c9f201a0e,0x3441fd12384027e1180,0x1480411de3a800000b13,0xdc003090524039c40bde,0xa1f981eb40cf36430004,0xc0000000000000103f68,0x26700db0b30f98e0a027,0x302d0ce5500002411474,0x81d280b7eb370c442,0x80857010880c8721c44f,0x5540ab00001c053433f8,0x308c10e000015097b34,0x27423fc0cbd33b8c03aa,0x703ad00cc601bb4d2,0x800001836b007c7412c0],#[0x98f4a1420387cd013004,0x1cea1498950a0099,0x708319780aa80234545c,0xce529003b026e00b95c0,0x8cf11006d0d02b3923,0x14e4ba007c0000093,0x910383847b00000da380,0xfc583340000499ff500,0x548d0c10c00000303a14,0x4401150023f409cc039,0x60224c4a8d0a2edc2014,0x4a3b3d00000142a70021,0x804346440e90f620f68e,0x8dd45f8416000007a265,0x80c0001c90b51c4201b3,0x900002c05ec839760dd5,0x2dd500e144361836480e,0x4a407000000000e40024,0x390944aa11900000f422,0x112830ca1027849830,0xdbb40191a4ec00580000,0xc49dc3461804a000006c,0xfa401eb01d00000722b3,0x6393266e501000821083,0x4e11ce0e5fe00be009e6,0x2dea0af800002300960c,0x702d3e413dc028b037e8,0x1f98872d01c624247015,0xd426bdc2d203ce403010,0x4d301bec007913cac400,0xe02b2d448e0bae50,0x1f9a5490175e0b0d0348],#[0x2bc002d10000282e9603,0x924236002d010ffc0316,0x10a628439602c464f,0x180f8c001288c0120240,0xf80cc9702e15a7fe510,0xd6a94c09000406c0eeb5,0x637037b18c0181e48108,0xe123d1a8112a0240,0x1690b5b0b170d0fe9c2c,0x2608ea2000004046740,0xa701e60c25902b88c08a,0xec800278e77483d1c87,0x880960016940a1f12b34,0x307c056c691c8d1b8514,0x3a788800d2083d05da0,0x3d5046740d1263e540b0,0xa7d33a4a00a808388d4,0x3b26600016640d744232,0x810d3017c00f7551,0x800093c4aa939bb60de0,0xc0fe281f5a6e0000360d,0xf443ec03d94c09428544,0x328e42d40478487e0836,0x203371a5cd012c008b60,0x26b41578e3f000021477,0xc03966978447210116d0,0x5dd8f2000039450d3a8c,0x3913a0d6c022380b3164,0xfc0368c03ca11032cddf,0xcd93834dc2a7d0264cce,0x6807b70adc00005041c2,0x1cc104c802501ce04037],#[0xa0357c2f4139d7d44b75,0x4400003803ea03c2807a,0xce979a0344380000344,0x664558a1100001,0x282400000000384f1000,0xc9838000004513d8489b,0x477026b1aa7b019d002,0xa8457812ec0c17a02320,0x2b794588414e8a253341,0x340ac0000a835e4e41d0,0x624125cda4b5b3578086,0x204ba000030c,0x661007a10cda6f0151c0,0x10d641128707fe617e00,0x201107d0b6333d000003,0xaa55101c885c00493ece,0x8c0b25047e02a1ab3864,0xd060c570b3f90908042,0xa04180000d0b3400a511,0xa03640000330159454,0xc89c0000381224516400,0xc084b02fae034c1323,0x4336c7ac285f0001000,0xed12670e680000000009,0xba00003843a5044e02a,0x39a4f2207dce61d028e8,0x17f8118b2203c083e139,0x7288ac48c7304d845d82,0x89cb3610093c201c9094,0x48e4a402104c2f513702,0x18cb5b1160402a7001b,0x3a9000008516f4ea6d99],#[0x801b48c745100900d35,0x67c770790064951d21a8,0x80e4c50acc1065241a9e,0xaa500b64109841167029,0x4390d0323000036cd6a3,0xbdb01d68a06d0c0c2406,0x40dc9416858f58601620,0xdc001400003409b210c5,0x51764a207391c0000101,0xf41258e9f44145908a5,0x3f0980080686002c000,0xc2c4939ab18f1710230,0xe5a52b03408ead0000,0x232b394ebc424c0000c0,0xe7091c2e2e00ed40b5,0x2ced42b700ff0000000,0x40010004260087ce00d0,0x22a8d17c02e78461569,0x800ac00008424500d6c,0x264046d4041e0a88000,0x188111012140fad0b410,0x26cd7963ef1d0f0000,0xe202000c600000000000,0x8100000d0962288f0463,0x42ca00001a67d00ad14a,0xb8c2d700001c03735154,0x6460005100002c0bfd00,0xf6513281049004400008,0x2f67020080602b37d800,0x4401d10a795068003b68,0x266404eb000ac04fc02a,0x511e6405c6527400c093],#[0x67300a6da4a6029d445b,0xcd149019800006b37b26,0x579453a110c087fa0afd,0x282d4091510070eab700,0x800002051310b730cb49,0xe6900350c8c2020edc07,0x1c0f4362c4e40933410c,0xcdcd105016ed09bf339,0x131e800361299fd06920,0x8b0000000005396782a3,0xd00958032c11e3d0,0xd6543f43ad740a200000,0xb7c0000821cc00ea300,0xad001684bf2648e827d6,0x1c445102f1411,0x1c2c6110140000630000,0x408a4f5000015095c902,0xbb1b0000079acc105e60,0x73551c44a7f400234058,0xc462f4079848ac01a740,0xd79478803fb807dd015f,0x40c0000139adcce7d03,0x14a7cb10ee81114,0x530668e42800f4000,0x1a000000000100600,0x18013f005e80220000,0x6218cc49300001944600]]
def g223D8 := limbs80 #[#[0xa12809076a5d54250120,0x41da97650940483b56ea,0x515250120ed5bb284a02,0x483d52c8b1280907ca5,0x4ba2c4b0241ae9865894,0x2c09073add16258120e7,0x6e992d91604835d708b1,0x42501208bfcab0eb2241,0x83f56caa1280907ea595,0xb284a0241fa975509404,0x907ea9d94250120fd4b,0x99454940483f52c8a928,0x50120ef4bb2a4a0241fa,0x7d30ca92809077add952,0xc4a0241beb8654940483,0x7ea6516250120fd4b22,0x558940483dd2cab12809,0x120ef4baac4a0241eeb6,0x30ab12809077add56250,0xa0241beb85589404837d,0xba6196250120bf5caac4,0x89404837d30cb1280907,0xdf5c32c4a0241eea865,0xeb2a809073e5d9655012,0x2417e992d9540482bf32,0x65f6550120e7cbb6caa0,0x40482f7728baa809057e,0xfcc32eaa0241dbb945d5,0xaa809067ee197550120c,0x19f986dd540482bf72cb,0xb7550120cfdc36eaa024,0x482fd724bb2809057e65],#[0xc92eca02417bb945d940,0x809076ee517650120ef5,0xe9929d940482bf72abb2,0x650120bdcca4eca02417,0x27f3313b2809057e65e7,0x2c4b02415f995dd94048,0x9077a5d16258120f74b2,0x8458960483bd6e8b12c0,0x8120f74aa2c4b0241beb,0xd308b12c0907ba5d1625,0x4b0241eeb8458960483d,0x6fa6138258120f74b270,0x55160482fd329c12c090,0x20b7ccb2a8b0241eb964,0x30aa2c09057e65d54581,0x241bbb84591604827f5,0xe5d16458120f74c92c8b,0x160483d7708b22c0907a,0xe7dbaac8b0241cf97559,0xb22c0906bee156458120,0x41cf975d9160482df72a,0x176458120e7dbaec8b02,0x482df32bb22c0906bee,0xdc2ae8b02416fb965d16,0x2c09057ee557458120cf,0xcfb965d1604839f12cba,0x7458120cfdc2ee8b0241,0x82fd724c22c09057e657,0x1300aa2413f995e11604,0x89063f6197655120df4c,0xf985d9544823fb30bb2a,0x55120adeca6ecaa2411f],#[0xb7f28c3aa89047f66376,0xeaa2419fb9061d54482,0x56f65287551208ffcb3,0x2601644823fb3143aa89,0x120e5ebb2e8b2241be98,0xb0eb2ac89072f9d97459,0xb22418ff87595644831f,0x3f61f6559120b7cc86ca,0xd5644829fb2fb2ac8906,0xadeca6eab22411ff985,0xdbaac89065fe17755912,0x2411fd98dd5644829fb2,0x5db85591209fcc870ab2,0x644823fb2fc2ac89063f,0xdfca2ecb22416fb905d9,0xb2c89073ee417659120a,0x14ff955d96448397f28b,0xe7659120b7cc84ecb224,0x482b7b29bb2c89053f65,0xcab0eb22411fd98dd964,0xc89053fe598759120abf,0x7f9561d644827f720c3a,0x759120cfdc830eb22413,0x32ff2ac3ac89065f2558,0x30eb22411ff9561d6448,0x9047fe598759120c7fcb,0x90e1d644829fb2d43ac8,0x91208fecaf0eb22413f9,0xf6eac06c89067e5d580d,0xbb22413fb95603644833,0x47f66175d9120adfca2e,0xdd7644823ff30baec890],#[0x208fecc6ebb22414fd96,0x2abb6c89063f5d985d91,0x22418ff985db644829ff,0xfe51755d1208ffcab0fb,0x974482b7f28bb2e89056,0xafcc84ecba2418ff865d,0x3b2e89056f652765d120,0x411fd96e15744831ff0d,0x54865d120afac890cba2,0x44831fb0c432e89055f6,0xfc350cba24157f956197,0xee89047f657865d120c7,0x1ff9561b744823ff2cc2,0x805d920df5c1700bb241,0x83bd705c02ec904fe653,0x8308bb2415f994e01764,0xc9055fe55845d920afdc,0xb94602764823fb2bc22e,0xdd9208ffca30f3b2413f,0x5f2c9c02c4b047fe5584,0xb12c13f994e0162583,0x6be6138058960f75b97,0x25d162582df329c02c4b,0x960c7fc2ee8b12c16ef9,0xf30ba6c4b053f6577458,0xb12c18fd85dd3625825f,0xbfe5584d8960a7ecaee9,0x1172d823ff2ac26e4b04,0xff4bb2a4a02411fd95e,0xca9280907fa9d9525012,0x241fea8654940483fd30,0x5956250120ff4cc2a4a0],#[0x40483fd2eab1280907fa,0xf4caac4a0241fe985589,0x1280907fae556250120f,0x1fe99858940483fd30cb,0x96550120ff5cc2c4a024,0x483ef2eab2a80907fa64,0xbb2caa0241ef97659540,0x80907be9d96550120efc,0xf99759540483bf6ecb2a,0x550120bfccbacaa0241d,0x2ff72eb2a809077ea5d6,0xecaa0241ef976d954048,0x9077e5d97550120bfccb,0x865d540483bf4ecbaa80,0x120dfdc32eaa0241bf9,0xf30cbaa80905fee59755,0xaa0241dfa865d540483b,0x77e6597550120efc4b2e,0x5d540483bf52cbaa8090,0x20efcc36eaa0241dfb96,0x24bb2809077ea1b75501,0x241fbb945d940483fd7,0xe6197650120bfdcaaeca,0x9404837f70cbb280906f,0xefccaaeca02417fb985d,0xbb2809077ee557650120,0x417f9959d940483bf730,0x516258120bfccc4eca02,0x483fd2e8b12c0907fa5,0x4aa704b0241fe9845896,0x2c0907fa5d38258120ff,0xfb96455160483fd324aa],#[0x5458120fdcba2a8b0241,0x83df32caa2c0907ee611,0xb2a8b02417f996551604,0x905fee595458120f7d4,0x99755160483bf32eaa2c,0x58120efd4baa8b02417f,0x7f330aa2c0905fee5d54,0xa8b02417f99855160483,0x5fee615458120dfd4c2,0x459160483fd324b22c09,0x120f7cb2ac8b0241fb97,0x6eab22c09077e5d56458,0xb0241bfb8559160483bf,0xfe65d6458120bfdcaac8,0x9160482ff72eb22c0905,0xf7cc2ac8b0241ef9755,0xab22c0907bee15645812,0x241efb9559160483df32,0xe5d6458120f7ccbac8b0,0x60483df2ebb22c0907be,0xfcbaae8b0241ef985d91,0xa2c0906fee157458120e,0x17fb965d160482ff72ab,0x57458120efcc2ae8b024,0x483bf32aba2c09077ee1,0xcb2e8b0241dfb955d160,0xc09077ee597458120efc,0xf985dd160483bf130ba2,0x458120efdc2ee8b0241d,0x37f30ac22c0907fae498,0xb08b0241bfb856116048,0x905fe6578458120bfdca],#[0x97e11604837f32bc22c0,0x5120fdcba300aa241bf9,0xf6ecc02a89077e5d9805,0xaa241bf98660154483b,0x5fee598055120dfd4330,0x5d954482ff720bb2a890,0x20cfec3aecaa241afd86,0x30bb2a89067fe1d76551,0xa2413ff985d9544827fb,0xf6517655120efdc82eca,0x9544833fb0cbb2a89076,0xcffc32ecaa241cfe865d,0xbb2a89067f2617655120,0x419fe985d9544833fb30,0x617655120cffcc2ecaa2,0x4482ff3213b2a89057fe,0xec3cecaa2417bd949d95,0x2a89067fe1e7655120cf,0x3fd989d954482bfb2f3b,0x7655120cffc36ecaa241,0x83b7f28c3aa89057f663,0xb30eaa2415ff9661d544,0x89067f6598755120cfe4,0xf9661d544833fd2cc3aa,0x59120afecb50eaa2419f,0xfd724c02c8907fa60980,0xb2241fb97460164483,0x7be5958059120fddca3,0x560164483df6cac02c89,0x120efdbab00b2241df97,0x70ac02c8906fe6158059,0xb22417fb95601644837f],#[0xbe9d98059120f7cbb300,0xd164483d7acaba2c8907,0xedebaae8b2241ebf655,0xaba2c8906efe15745912,0x241dbd765d164482f7f2,0xe516559120edfc3ae8b2,0x644839faecb2ac8905ef,0xfec3acab2241cff76595,0x2ac8907afe516559120c,0x1afd87595644839fb0eb,0xd6559120e7f43acab224,0x4839fb0fb2ac8906bfe1,0x43ecab2241afd87d9564,0xc8906bfe1f6559120e7f,0xfd765d564482dfb2fb2a,0x559120e7f3b2eab2241c,0x33ff0ebaac89067f61d7,0x2eab22413fe985d56448,0x9073f6597559120edeca,0x965d5644839fd2cbaac8,0x9120cfecc2eab22415ff,0xfd30baac89057f661755,0xab22415ff985d5644833,0x57f65b7559120ebfc2ee,0x61564482bfb31baac890,0x20cfec3b0ab2241cfd76,0x2ec2ac89067fa1d85591,0x22417f990e1564482bff,0xf61f8559120e7ebb70ab,0x5644833fd0fc2ac89067,0xdfcc870ab22415fd97e1,0xc2ac8906bf5db8559120],#[0x41afe76e15644833faed,0x5f8559120cffbb70ab22,0x44827fb2fc2ac89067f6,0xfca2ecb22419fe97e156,0x2c89067fe1d7659120bd,0xebf945d964483df720bb,0x7659120b7fcaaecb2241,0x83b7f28bb2c89073fe1d,0xaaecb22415ff955d9644,0x89073fe557659120e7ec,0xd879d964482dfb2b3b2c,0x59120afecaeecb2241cf,0xff720c3ac89057f66376,0xeb224177f9561d64482,0x77ee418759120cffc3b,0x561d64483b7f28c3ac89,0x120ebfcab0eb2241d7c9,0xf2cc3ac89057fe558759,0xb22415ff9661d644839f,0xefe518759120dfdc830e,0x1d644836f92ac3ac8906,0x9ffcab0eb2241b7f956,0xac3ac89067f655875912,0x2419ff9661d644833ff2,0x65a8759120afecad0eb2,0x64482ff321c3ac89057f,0xfecaf0eb2241bf990e1d,0x6c8906fe5d580d91209,0x17bf945d7644837f32ac,0x975d9120dbec2aebb224,0x4833fb0ebaec89073f5d,0xca2ebb22413fd985d764],#[0xc89073f65975d9120edf,0xf990617644833fb30bae,0x5d9120d7ebb30bb2241b,0x33fd2ec2ec89067f65d8,0xaedb22413ff976176448,0x9073f65576d9120b7fca,0x9561f644839ff2abb6c8,0x9120cfecab0fb22413ff,0xff0cbaae89067fe5587d,0xaba2417fb90615744833,0x67f9db855d120cfebb70,0x5d9744827fb2dc2ae890,0x20edfca2ecba241dfb90,0xcbb2e89057fe55765d1,0xa2415fd959d9744833ff,0xee41865d120afecc4ecb,0x974482f7f28c32e8905f,0xaffcbb0cba24177f9561,0x432e8905fe642865d120,0x415fd97a1974482f7b29,0x57865d1209fecc50cba2,0x4483bf720c2ae8904ff6,0xec330aba2419fc866157,0xae89067fa19855d120cf,0x5ff96615744833ff0cc2,0x855d120cfec370aba241,0x82bfb2dc2ae89067fa1b,0xb70aba2419fd96e15744,0x89057f654865d120cff4,0xc9561974483bf720c32e,0x5d120ebfcab0cba241d7,0xbfb2b432e89057fe5586],#[0xcba2415fd95e1974482,0x67f65985dd120cfecaf,0x561b744833fd2cc2ee89,0x920cffcab0dba2419fd9,0x309c02ec907fae0b805d,0xbb241bfb84e01764837f,0xfee41845d920bfcca700,0x1176482eff2ac22ec905,0x9fecaf08bb241bfb90e,0x9c02ec9077e613805d92,0x241dfb9061176483bf70,0x615845d920edfc2308bb,0x764833ff0ac22ec9067f,0xbfcab08bb241d7c95611,0x22ec9057fe55845d920e,0x1dfb90e11764839ff2cc,0x7845d920cffc2f08bb24,0x4833fb2bc22ec9057f65,0xca3013b2419ff95e1176,0xec906fe641849d920dfc,0xfd97612764827ff2ac24,0x79d920cfeca30f3b2419,0x33fb2ac26ec9067fe518,0x700b12c19fd966137648,0xb073fdd56458960dfcba,0x85dd162582fdf24ba2c4,0x8960afecaee8b12c19ff,0xf6e9c02c4b07be5d3805,0x8b12c1efb905d162583d,0x73f5d57458960f77c92e,0x5d1625839feeaba2c4b0,0x60b7fcaae8b12c1aff85],#[0x2bba2c4b06bfe1774589,0x12c1cfd95dd162582dfb,0xf61574d8960e7ebaae9b,0x362582dff2aba6c4b06b,0xd7ecab09b12c1aff985d,0xc02e4b077e5d3805c960,0xc1bf984e0172583bf6e9,0x53805c960dfdc2700b92,0x2582fdf24ba2e4b05fe6,0xfc2ae8b92c1def925d17,0x2e4b067fe17745c960cf,0x7fb9061172582bfb2bba,0x845c960bbfcab08b92c1,0x837f721c22e4b05bfe59,0x8309b92c13fd95e11725,0x4b04ffe5584dc960dfdc,0xf95613725833fb0ac26e,0xdc960cfecab09b92c15f,0x3fb0ac22e5b067fe5584,0xae00015ff9561172d83,0x3f00330027001e601260,0x75606ba061e059404b00,0xa8609ea094e088e07ce0,0xcf00c8a0c000b640afe0,0xe0f840ec40df20d7a0,0x2c01248119a113410aa1,0x5cc155414ca13f8135c1,0x8c6182a178e16f2167a1,0xb8a1b001a6419a4192c1,0xdd01d581ce01c681c021,0x5e1fe61f5c1ec01e481,0x34622aa21ea216020e82],#[0x6e22622253e247e23e22,0x9dc294028b6281a27902,0xcc42c162b9e2b142a782,0xfd02f582ebc2dfc2d722,0x2ee325231da313e307e2,0x57c3504348c33f033543,0x852378036e4366c35e23,0xb163a6839f0395438ee3,0xd4a3c9c3c243bac3b6a3,0x683fde3f423ea63df83,0x31a4290422a417c40f24,0x5cc45424494440a436e4,0x824479a473446bc46564,0xaa04a2849b0492648c04,0xcf84c924c1a4b904b3c4,0xf1a4ec64e844de84d704,0x1ba51305082500a4f924,0x44853ac534652bc52445,0x6fa5670560a558054d25,0x98858ec5862582057725,0xbce5b565af05a7859dc5,0xe4a5dc05d6c5ce25c8e5,0x5a5fe25f7c5f165eb05,0x2c4625e61d4616e60e46,0x4e6646e63f663a2633c6,0x75066d8668465e865706,0x9de694268dc684067b66,0xc246b9a6afe6aaa6a446,0xec46e3a6dc26d386cc06,0x11c70b6703e6fc66f726,0x2f672a2723c71d671827,0x518747c7404739e734a7],#[0x71676c2764a75e4757e7,0x8f0788a78487806776a7,0xb367a9a7a3479aa79567,0xd6a7cce7c7a7c387bae7,0xfc27f267e787e247dac7,0x21a8190811880b2803a7,0x43c83e88382831c82928,0x5f2859e855c84f684908,0x7ba873086ee869a86588,0xa908a18898e890488328,0xcc48c3a8bc28b808b088,0xef88e928e088d908d188,0x16290ea90728fd68f708,0x384931e92a6924091da9,0x5b8955294da948693ea9,0x83497bc973296ba96309,0xa4499ba993098dc98889,0xc789bee9b769afe9aaa9,0xe889e349d989d569cf09,0xbca00e9fa89f309edc9,0x296a21ea1caa12ea0fea,0x4eea476a3daa362a2fca,0x746a6aaa620a5baa554a,0x97aa8f0a89ca7caa788a,0xb8aab24aaacaa34a9f2a,0xdd0ad58acceac7aac02a,0xfe0af68aef0ae78ae12a,0x226b1c0b148b0d0b058a,0x424b3d0b36ab304b29eb,0x5c8b562b520b4ccb48ab,0x77eb72ab6b2b63ab5f8b,0x97cb916b8c2b86eb7f6b],#[0xb0ebaa8ba66ba24b9d0b,0xcc4bc70bc1cbba4bb50b,0xf0abea4be1abd7ebd2ab,0x108c090c02abfd6bf82b,0x2f4c28ec23ac1d4c16ec,0x528c4b0c438c3aec348c,0x792c72cc6a2c63cc5b2c,0x990c93cc8d6c882c81cc,0xb6acb3acaf8ca92ca1ac,0xceacc96cc66cc00cbacc,0xe8ece16cdc2cd80cd3ec,0x20cfcccf8acf5aced0c,0x1fad194d11cd0c8d086d,0x440d3ecd362d2d8d24ed,0x63ed5b4d54ed4fad494d,0x7e2d78ed716d6d4d692d,0xa28d98cd926d8d2d85ad,0xc6edc08dba2db3cda8ed,0xed8de4edde8dd94dcd4d,0x10ce0a6e040dfb6df3ed,0x340e2ece262e1eae184e,0x604e544e4a8e442e3dce,0x838e7e4e77ee718e6b2e,0xa00e976e922e8e0e89ee,0xbc8eb86eb20eaccea42e,0xda2ed2aecc4ec82ec2ee,0xf6aef04eeb0ee4aedf6e,0x10ef0a8f066f024efbee,0x2e8f2a6f21cf1c8f186f,0x48cf44af408f3a2f33cf,0x678f612f5bef558f4f2f,0x8acf810f7aaf756f6f0f],#[0xabcfa7afa02f99cf912f,0xd26fcaefc36fbacfb34f,0xf48fee2fe8efe04fd9ef,0x13500e1007b0026ffc0f,0x2fd02a9024301dd01890,0x58b0525048903ff03510,0x75306ed0687063305df0,0x95108fd08a9085507ef0,0xc85f864ce7f21309b70,0x42fc2e7057906051391b,0x90b053a7cfe193790a86,0x5ba7cfe1057907088421,0x44e45f845f0af2150c8,0xf3f85170af2140b05517,0x68ba6f21412089a70545,0x6f21812851a51782f3f8,0x60a05ca4998204f9fc2e,0x8843cfe17302bc838311,0x9810c179fc30a7379080,0x8a2bce29f0842cde420,0x3f90ad4f874dc5e17906,0xa74c18180b0551705e17,0x2c1506a2f8704e774f90,0x4e46b9fc326057908060,0x841d3e7f0c9815e421d2,0x90573c9bc20a74f90608,0x82f093bc8442917e1b3f,0x786cfa6f20e0f45c2819,0xe0ab3e9bc3e414221005,0xe419160e8569bc367f20,0x1a7c3e42c1d0ab3f8517,0x8522fce11c104816a685],#[0xad28b8579c220cc1787c,0x83484615e173e9bc8384,0x1c9c118539cd3a6f0f90,0x7c828381a0a73f874de4,0x7d342bc3e425ce0ad378,0x9fc28bf20c8d4585822e,0xb8539f4de1f21011853,0x1a7cf45f0a2fc8462c22,0x48b34e9a8be1f2161285,0x4f8517e41c24108579f0,0xd30af0a2fc8305215453,0x34e0b8be1b3e9bc84814,0x2cf82e2f874de418220a,0x80882d1567d3784d3e42,0x2023c5081a6cfa6f0f90,0x4508f142069b3f874de4,0x6f0857c8303517e1f205,0x3b4d67e2f87c8503414a,0xc5f0a2fc844361412458,0xf17c3a6f20e1586c2acf,0x7a6b3f8615e4182a0bb3,0xa6f20d67f0a2e15e4151,0x69bc210f20c0bb382bc3,0xc1045a9bc30af20c0b05,0xe1f20c110569bc210f20,0xb9fc3a6f21010e2c294d,0x3a6f082bc8382b058be2,0x5a98d3e18579060882cd,0xc11c11a415e1d379074,0x3a6f20e1034e9bc30af2,0x1785cde4282a0b7382bc,0x53e42022100539c2545c],#[0x579080602fce0a73786,0x421e4202210f3b9a53e1,0x773790a0679f050a7378,0x90c08842120aa2e0bc2e,0x4e08180bf38a5cde1057,0xce8b737868be428988b9,0x73787c810265212c1043,0xbc210f20e4c1482bcf45,0xca2f8421e4228b020539,0x9a8be108790745c29cc4,0x1208786cfc5f2110a45b,0x2acf66f0f17c8419b04,0x567b371413e1f21089c1,0x559ecdc5f0843c8385f0,0xf9093304b8be10879060,0x8483253e70922acd82f0,0xe53e7e28301629f0a2bc,0xc850a4cc12e2f8421e41,0x3515290a849cfc5f0d9b,0x12084a6cce7f0a2bc842,0x1f212e70859b8be1f20c,0x90a06e08258a73d9b8be,0xaa36168a73f16cde194f,0x210b73d9a53e14579080,0xfe4238ae7b378421e418,0x205050982acdc508785c,0xcdc573f87c8402d53e1f,0xb3715cfe1f2110b85052,0xc1409f0f902836a42810,0xc8282c14a9f0f9028302,0x73f8415e41dcf66f0c2b,0xa176662f87c83056cc10],#[0xd738282166f0f17c8422,0x2c1fa762e9a85e1f2160,0xa6e2f0bc3e4211d0d464,0x69b8bc2f0f90507e9c15,0xc0a04e9f4dc5e1787c84,0xe1f21214e2f0bc3a7f20,0x5440a85013a7d371785,0x87c837842fe40fc22ff2,0xc2f08bfc8369f4dc5e17,0xe9f8bc2d3787c84a9b8b,0x6c5d350bc3e4242e1604,0x2c9b85e1f213a9092321,0x85e154f9088642c1429e,0xe1786cfe422190b0a717,0xacfe10979070a4a74dc5,0xb3e9b8be1f20e13e2f0,0x9b8bc294d9fc3e41c241,0xc507f082167f0e9bc84e,0x1f20fa9d3787c8151423,0x9bc94a1013c5e1052cfe,0xa9e2f0acfe1d37908f0e,0xe9829c5e1786cfe41c14,0x40b6530b4de1b3f17c84,0x38578bc2b3f874de41c2,0xf9050a71785a6f0d9fc8,0xaa6e1787c8369895e108,0xe41c15a6f0847c82e9f8,0xe9bc8404421c5e129bc3,0x24af20b2907f1784e7f0,0x4f1785e1d379070869bc,0xca6e2f0a53e1f20c0a1,0xdc2f211c5e101f4de1f2],#[0x853c82529cfa9f0f174,0x19e76169bc24af20ea9f,0x3e41753c2d378695e418,0x2f0bc2e7f20de7d3717c,0x10e7d371785e1f20da6e,0x8185353a6e2f0bc2e7f2,0xe4180fe10a7904f0853c,0x78495e41953c5e169bc3,0xbc273f8425e41816c2d3,0x6929cfc5d378653e4278,0x20e7d34a7c24af20e0e2,0x83029cfc5d378421e41c,0xe9bc83d9f8bc2f0ea7c,0xc3a6f20545b3f1784a9f,0x54f178567d3787c842a7,0x553c5e17874d67f20e14,0x408f178410d3786cfe42,0x178bc294b9f4de1f20e1,0xf4de1f20e110878429e4,0xc45f842be41b8bc294b9,0x9b4fc50a70bc3e424288,0x4d3e41fc214f2068c45a,0x2f09a7c8422c29a60578,0x84d214f2088c458538bc,0xe90a69b8bc2f0d9fc847,0x40a0be7349a3c2e40a0c,0x1785e134f90673f84d3e,0xe7b4e9b8bc2f0f90ad37,0x41fc2690a7904c662f14,0x902a239f4dc5e1053c3e,0xe7d371785e1f20fa6f0f,0x1f20a110578421e41414],#[0x282210f0f9057350bc21,0xbc3e41a141173787c828,0x5e1786cde41d15e7e2d9,0x9f8bc2f0d9bc83b9f15c,0xbc83b9bc30a0879050ab,0x1f2050594f9f8bc2f0b9,0x2c20e6f0847c8339f53e,0x421e411cd42f0847c828,0x625b9a85e108f906f084,0xf0f9070939a85e108f90,0x785e1f20c12c4f0acca5,0xe159bc3a5f210e7b369,0xf20c10f0f9028239c181,0x7c210f20ae7b3697c210,0x73e9785e1097907b369,0x2c12e7b370b4be1f2101,0x7c00a22cdc2f0847c828,0x670f8050884216675378,0x109d67f0a2fc02c2ccea,0x82a8b70f80845b849de0,0x9d3517c3e01c280fa2e0,0x2cd2a6f082bc0442d166,0x8d3485bc28bf00c0e06c,0x189c8b738474de1f00e,0x8517e01dcfa6a2847c3e,0x8245b87c04840d382097,0xf8517e010281208b9e8b,0x80645d9f4c4ef0f806a2,0x6745780507034d3e1457,0x101469d3787c02847c3,0x990d67b0f80533e9b0be,0x515e0101567f0e9bc02c],#[0x4de012cfa6f0f8041378,0x304421e1457805c2987,0xb87c040442026f0a2bc,0x4ce1f00a69c299e4ca6b,0x2c341de185780533c99,0x3f87c0151a1a15f0c2bc,0x78040978517e0101a45b,0x4e37093b4de0220ce127,0xa6f007a6f0f80306a2c1,0xbf00a0d05787c01515c3,0x1e0cc570f80433b17c28,0xbc02844208bd378415e0,0x7d378615e0202026f0c2,0x9b056142f8060884016e,0x1034c9b8b61057807084,0x873e9bc3e013c3e04586,0xc221045829cfa6f0f80,0xf0a6730e9bc0369bc3e0,0x13e1f01210f0f8116202,0x94f80808829cf0273042,0x7c01018180b7360815e1,0x58138421e018244545f8,0xf00c4c70aa415e015cd0,0x42410f00e172759899e1,0xbf0d9fc08a1b0567e2f8,0x481610e2f86cfe01c180,0x7c3e0145366e2f87c028,0xc0259b8be1f0080a44f1,0x5226cde1f00b853082b,0x3787c0185c53e1457805,0x7878be014538530f804b,0x17c3e0138be1f00610b3],#[0x305e1f00e61e2f803b37,0x5f0ca7c08a1822129493,0x915617084acde02c17c,0xc5f0ca7c0384ccf85a2e,0xf1415e194f80781049cf,0xce7e2a0bc210f00c1233,0x61f00c0db3717c212f00,0x1bc3e0450612338530a,0x17c3e01d1a15b378515e,0xe7f0f8020204c1ae7b37,0x1f00c8a7384b8be1f00c,0x9f04e1f00e293371425e,0x29b378515e014240c053,0xf00a8d33057c28af00c,0xa4cd6170f80809b17c21,0x670a78615e018cf8594a,0x181645b3787c0141a16,0x4fc3e0141782e2f8553e,0x673e0a13e1f00a8d738,0x1f005050bc31cea9f0f8,0x21ce1454b87c0282c15e,0x40582acdc5c178553e0,0x733717c3e01953e1f005,0xf00ce7c1043c3e0151ae,0x6c2e1f00e10b342d8be1,0x1a2d8421e018ce66a2b1,0x48160a73f17c3e01f04e,0x3c0204c1a0af0f802030,0xc02029c210f008c5f084,0xe2c2fc20ff00ea70592b,0xe1b0bd378495e01e1ba6,0x95e0134d457092bc0283],#[0x6e9b8be105f806a2b84,0x578070569885a108f806,0x4229f00c49d3e9b85e10,0x7d854229f00a0fe1585,0x304015e1f011c2f0f803,0x9a6d0847c020474fc2d,0xc0f05787c0201bc3a7f0,0xaf00ba6e2f081fe1f00,0x69c15a6f0f80907d0542,0x80207f87c0184550a308,0xfd38434c0af0f808f0f,0xad0f806d3e9bc3e01022,0x9b85e1d3f805d3108200,0x41fe0181361508bfc02a,0x2d09041fe0238409b0a8,0x9b840af0f80614e9b0b8,0x7c02d05420f057805d3e,0x70b29bc3e0142ba60a78,0x202a14d312893e1f00e1,0x304a9d4cc571b0bc3e0,0xc3e02c13e1f00609f0f8,0x5c2c150a0254ea662b0b,0x61612f00fa624f87c020,0x52178617e01919a962f8,0x9787c0302c95e00c204,0xc24e7f0f17c0304017c5,0x25e0182012f0f17c0282,0x73f8495e019cfc585f84,0x97807a2b8495e010250b,0x17c5f00c0da2b174ce10,0x5e0154d45f0061073f84,0x3f0a17e1f00c10d30509],#[0xd0c54f0a17e1f00d0c7,0x74af00ca903709c215f0,0x3f0bc20bf00d0ce17861,0xc0ae2f0bc229f00c0c7,0x213f00a0a94f09c326f0,0xd858367d37806c570b8,0xf87c02c9c8e8660f805d,0x829e170427e0142929b3,0xc2f0d9fc02852cfe1f00,0x2b3f87c02306cfe00c25,0x13f0bc3e0148fe1f007c,0xe01b85e1f006c1f00412,0x5842be01823a6e1043c3,0x8060ad8425e0101326e1,0xa1b3f8060970ac2a113f,0x13854af0f804a7536c2,0x274de10af805037842be,0x483a6f0081509787c020,0xa15f0f80309787c01e8,0x9a9f0f803a753695e1f0,0x27d3787c0309fc34af00,0x1f009670a787c0202953,0x1015616091fc02d9c1fe,0xf840ff0f808b0b06cfe0,0x2f082f8be01c1567e284,0x18532643787c02842ce1,0x595e0102a479358583e0,0x8be01429e1b3f80460d8,0xd370bc2caf00c0209787,0x578050a91f4de1f00a89,0x828690b2bc02e9b85e16,0x4caf0f8050511fc3e011],#[0x10f00aca23f87c0204b8,0x49ac2a153780708f0bc2,0xc116169815e1f00c29e1,0xe1f00e110870853e1f00,0x3864de01c23c20839f4d,0x21053787c0282852a6e1,0x2ca41e4ad339fc3e01c2,0xe9bc3e01c2ae7d3787c0,0xdc273f87c02844210a73,0x4107f80573b8429e0134,0xaf00e4753787c0205742,0x8695e018220cd330bc24,0x14e1585c3e0178ba6e17,0xc3e00fc3e00895e1f006,0x2e7f00b4a23f87c0252b,0xa9f0f804f0f802d3053c,0x2f0f8030a30bc3e0134c,0x13f0bc3e01385e1f007c,0xf8030939f85e1f05286,0x29a6e2f0bc2e7f00ee7f,0x87c02785cfe00fc3e008,0x30802fc24af00aa9d37,0xc0370bc2e7f008c2f0f8,0xf0843c029354c0ef092b,0x57807d4f0bc3e01026c5,0x5361f00e4e54f089be10,0xb0a844fe01c2b6793708,0x813e1787c020264dc2,0x2aa9d3787c02ea40de1f,0x1e1e2f80504e9bc3e010,0x8d9f841005787c0384c2,0xa1bc3e00c1486f0f8040],#[0x9f85e1087806e1787c01,0xfc3e019cea6f0f80408b,0x208785cfe01828110839,0xf0f8055339fc3e01023c,0x543c2b0853c0404420e7,0x945a2bc3e00a0a135321,0x4ccf2682c8784e10a780,0x6cfe01642e1f03a42828,0x594b0b43a6f00a12e178,0xd0987c0502b84a6f0f80,0x7c0203e52a7229a74dc2,0x709e84c22ff00aa69378,0xa0a144622cce69f0f80,0xf85e153780645a2bc3e0,0xcc5e2b85a6f0f8074622,0xf00505e11a7c214f00b8,0x117c2f0a9bc0322d15e1,0xc3e01b4dc2f0853c02a3,0x178a7c3e01d1827e122f,0x1014b3f87c0205c2dc2,0xc02a30cee345d85c28af,0xb0b86cfe014d3617099f,0xd4cc561386c214f01009,0x5048988a42b3f87c0504,0x16856170853c0485c2c1,0x1470d85d3e0142667935,0x4f0f80504d9fc3e00a0a,0xa0ae9f0f80282024ce1,0x614f0f80304b9fc3e0,0xf807b499fc3e012d3e1f,0x2e7f00609d371785e173,0x205c2c1533f87c0141fc],#[0xa982be1f00a1473f87c0,0x99cfe1f00be10af80304,0x415e00c14e7f0f8040aa,0xcde019cf420a387c02f8,0x7378615e010200aa1385,0x162bc3e016cde1457804,0xd9bc02b17c366f009a9e,0x80573b99c3e01027c2f0,0x3b3787c0184014e1737,0x633d85c266f00a66f0f8,0xf0f80307d85c2e7b3780,0xb9fc0399ecde1f00966,0x966f0f8030a7178566f,0x2e173d9bc02a2bc366f0,0xe7f0061573f86cde016c,0x5f0843c02b9fc3e00fc2,0xc50a1062f86cde015ccc,0x5ce14f0f804e159bc3e0,0xc2e6f00c1473b9bc3e01,0xa851cfe1f00a110802b,0x3295c3e015cf66f0f804,0x82c2d0d874a10f0104b7,0x3e01c2589f0a97c02c99,0x6787c0283619a5e10b3c,0x9709733854be01b124d0,0x612d2f87c03387c0100c,0x3848216652f87c030401,0x780633c954b6170d9bc0,0xda5f0f806613864b6108,0x942dcfa5f0f8060b19ec,0x843c03c26848df0f8050,0xbe108780409836cc2cf0],#[0x10f00c67b0b86cde0154,0x4bc2e7f00a140919fc2,0x8425e0142410f0f8040a,0x3c02295c2e6f00813617,0xc02b9c4ce1f009427084,0xd2b9bc3e014200a70b9b,0x2f87c0222bc2a5f0090a,0x4aa7b3296c2a1f012105,0x33f0ac2a153f8070799e,0xce2533684c2a7f0100c,0xc3e01115a5b3787c0283,0xde0134b66f0f804c5697,0x2b9c2be1b3780545786c,0x2fc3e02097a5f0843c0,0x2e1b378050739ecda509,0xe1f0080673f87c0219ec,0x6f00a1073f87c02295cf,0x25e173f80433d85c36]]
def g223H8 := limbs80 #[#[0xd02250c000603010108,0x92200040301010a03,0x202030f0700070c0014,0x50600030a1203050f00,0x340010c001405010913,0x351540013b070003041a,0x50a01050316040125,0x2010410060104000001,0x91c01000821002611,0x4023b01070106000108,0x1002601050e08022101,0x100920e340313200000,0x80e040c122d36012201,0x1040118290100172e05,0x29170101033c010e0e01,0xa0c0404000300000502,0x40103470700030e091c,0x1010112262200000203,0x5000620080b0808040c,0xe1000130c0104010012,0xc000309002658030e36,0x1a060200223100000005,0x1d00030c000904140103,0x6010d04000b00191439,0x31440c090102090b0005,0x800070b031101190811,0x5509110628000b130a08,0xb111802060002001706,0x19020626000b030800,0xd260a1f000315020001,0x70810010504000c0165,0x1002e02282727141d03],#[0x602000f000c0b2c0200,0xf001300350002020108,0x90f050025090d00000a,0x4040d2f083d2000420f,0x1003a020e19010e0302,0x11101907000206000300,0x44080835161304164342,0x18011c04291b060000,0x712120b44020129110f,0xb000035003f0e07131f,0x150a000107160d0b4501,0x61319090230297c1c1f,0x322190b28639a000003,0xd02402314060c050100,0x31c244a273a02020900,0x9220b1a23565c010c,0x30537001e0614034d04,0x50a0304280105072e0a,0x21c3801070c0101000e,0x190f06fc340201380c,0x3902051a0b070206221b,0x40215142c0b00092a15,0x19b222210703701c1,0x3240966322006200108,0x201411994e1100150034,0xe580b8882b45400c0000,0x1805210813d0322660,0x681c05fb02d1d01be00,0x405110148633988,0x4c8b8947f8000000000,0x5c00001ad4df9b5a9280,0x68113813b6288c094],#[0x2b1e00506cc7a90a600,0xa0111005b700729c1966,0x8697600001ce3d00000,0x310d36421c00000000,0x150000000000241af800,0x11450000000000000010,0x190514006400000046c1,0xff074f00001605f00000,0x9a59a83639540000340b,0x4439a07800001007754c,0x7053c00003c,0x24000381bf0000000000,0x8d8c5f5022d000000000,0x2ce7edca2a904cb001,0x802400004982aa3ea800,0xc74080000301c8a39344,0xde6278c0fac830aa3344,0xa6000008c30d99d21042,0x2156214a50384051a006,0x193a69d0000031cf480,0xe40b756638000002045f,0x100a38a08a0412d7da10,0x6300000000034da181a7,0x1801bd0e8dcc0,0x843000002004c000000,0xa017d5015d3082880819,0xb9023400000000030068,0xc89221f60019071d80e3,0x130e1d6e51152e146420,0x103d6028600001a805b8,0x8000008536e404e644d7,0x829baa8668110a688e],#[0x1266d05b0818b026c000,0x739d413c80000234d022,0x158ece9c38516db34f2,0x8000800000000090582,0xc7e1870c086c90b80000,0x3449780000102,0xf12087a0cda8000000,0xf06c000003ce87c00ac3,0x62590412c182ac,0xf100001203d800000000,0x705f0368324c2be02,0x1f44301262490000000,0x19b2c000000000000000,0xe129caf830a000000000,0x686ef021bf200ea0d3,0x838f80065000,0x3812c00000a13840,0x7008a8c183039cca52dc,0x9c000000000939e4216c,0x4d6841470069d2028e0a,0x6b49cc6b800005833ca2,0x24c49000006044a4,0x1272d3805910b5072c6a,0x9fd68565a8de49a00000,0x58aa1d1e12de1d32306,0x3010ca0,0xe04e4c0020cc4bb1a080,0x490305a014b1000e8022,0xf1802270244114420881,0x23d90cf5e15a502b081a,0x9cb58418d30bcc008028,0x42812a06b8800a001a21],#[0x23268d3a15672cd0413,0x34e7c0000096310000,0x5b6808a010d0004d400,0x910a0c1e01ebe0b6d8,0x24026459fe305288d43d,0x10c99a0609000000000,0xaac00000000000000000,0x34408581120000106,0x2cd3dc0ad61455d0c260,0x17003c009de9d3fa1242,0x3ac1a98c010d015c0000,0x3cf2d1d8432c7a0c3130,0x82e43084e2ccd514baa3,0x10189d06a110e100000e,0xde0198c195b005de050b,0x1be01cf60485a6d83097,0xf0cb4000008275308,0x868700000866f08cae80,0xa32d2d026e02121c1700,0x9bb477f0031203c30337,0x38054f356a0000342d,0x3de0128604d1ccd6000,0x41160035266347088d4,0x30e10d5350410af00949,0x8588576a000000000000,0x10b00ee000003034c205,0x18f200c500000a0253e2,0x613c6cc97a1aa1b024af,0x80000308418000062112,0xd0507f80441c805e20c4,0x4b98024108579886da94,0x1112c845180d198274a0],#[0x200ffc0da8c047a8816a,0xf141408195c810765994,0x5790580e081a006c681a,0xced105c4308fd1a7c919,0x1967333b4cccec612ad1,0x60030141ace08c802d7b,0xd80000f4097603918442,0xba298a0506cc06578c19,0x6c51b53e050fc006742,0xc1570a30428326c23921,0xc000010300b39e74a1ee,0xa5ccd22886bd05579661,0x3bfc0433820a000c1205,0xd1cbce09fc0104052f80,0xaa1de4e4e39c1c106ad4,0xa842eac18ac202390632,0xbae207200b2db436402a,0x8746740644689208be02,0x666e20045ccb08000019,0x940e4200d18169182fa2,0xdb054c604818093a0428,0xdf000000000000006820,0x8ac650d841634000059c,0x4108a201b6c085e8,0xb80a71656a0000000000,0x200000805ae6657e80c9,0xaaa01e380606c821c80c,0xc2c00000900d6000000f,0x60496203ee0,0xb66de80000a023f80a80,0x14a0d4e082b7111c6423,0x25200f9b00b1b01f30c0],#[0x2c0df3135350bc2c2,0x6020c00007c199000000,0x1a824b442d10915710ce,0xb3d2d9ed00d8009c0000,0x30460ad582ce11a5a104,0x1a236fc33fc058013,0xd00e0000009438b9cf90,0x97579871a96cc31c204,0x20804d3865a000000000,0x90122000038061a05,0xd2ffe0073e2308000000,0x106aa64273181e1,0x6b817900000e82680000,0x3102849bb84086e409,0x220a1f307d6686c00,0xd40a2000000,0xb8521023db3270,0x7c000000000f3a0e0000,0x1f0000039b1022ceb866,0x41d3bb831880,0x22be016600000000000,0xe5669a41a34813a810c5,0x47c6978000070147c0a2,0x32b2083c014000000612,0x5e60844089afe05925b,0xd339a000000000000004,0xde126ec0cd0000034291,0xea70455a421ac04fd983,0x1e800001b0620c856716,0x10b7b003c222180d373b,0x40197c034f46b92e60b6,0x3c2869eb34a000035739],#[0x9d000009083ca138c417,0xc9880000d01c1e20e7cd,0x88ec0000010a1900b658,0x386eab047400000,0x945a3752057609f9e073,0x31021e80cea6343a0b,0x6c5e4c0680000d03ae00,0x80208a0c251cf5f11be8,0xd806b7668d7831620687,0x80402e7c176f801f803f,0x2900025432368223c06,0x201a000000000084,0xd002f0c7a4c0e7000000,0x21317020da4581f71b5b,0xe693800003a0fbb81c,0x54256431e09efccf6e90,0x25680b2d8070c000000,0x280b0000018625400001,0xca81a0039400233c04a,0x7401a4000000a0c3e011,0xc65a1ce5403fe507fcc8,0xc8fac1b57623e002326c,0x7acc00985b2336e00003,0x31cd6b290ad805192047,0xe001b868,0x28cb4bccb95056e00,0xe07ec000040227050f00,0x12072cc37db599800001,0x2b270880e81902844046,0x81ab6c2ee6014d620,0x4d786d28c01f34afb00,0x51110e675c1725818089],#[0x12110c67011988131eb,0xea34043868a340bf386a,0x364c036ce059841841ae,0x329520a0c20c7a4a29a0,0x190a79539732d0e01773,0x871a32204bd47471da8d,0x36f401a650e1ed3d7c2d,0xb56004ad118aa224941,0xc28c08257114e92aae8,0x504675030bf38dab30d9,0x1c41b1f108550d518254,0x11b00a9ca87ad0131800,0x816d01105a16b06cb08,0x3cc037015f00000a,0xa60cea4daab2863e06ba,0x1080a7344334010fe014,0xc01a0851c8e7881b5139,0x61a00003eccbc1052e0,0xdb32540c09427d4c18de,0xe14112c000400000b4b9,0x72951c1cca9400005050,0x2a3805a8413dc0d28481,0x32fb5115c000018e8c20,0xd882ea007ea66cd8338c,0x2f9a954061c00002c27e,0x279b320000020015012,0x32c085bb068f0225941,0x9955a1cde00000e42344,0x240543a083a3374a06b9,0x90c02b8c1a7000000000,0x141732827a300b5415,0x73d94858800000000000],#[0x1830edc18f79b998,0x442c3e4ce0b06b200000,0x180025812ee84b,0x53fe0d52c11580000000,0x40dc0000000007201c20,0x1154920c1e8066e09451,0x2f007806ae9813748198,0x10500ea0000242e7b020,0x71163cc8c7b31a446a8,0x9cadb00b8204f0000018,0x14177c0082866e000006,0x28a2770b0c206c78d63,0x4d000003050a00000000,0x400400000381,0x6514880fff3489474680,0x78056e059a00d28,0x56da8c4b228403c4203e,0xac44b8029843a6e219,0x823ace84733169983ac5,0x1415b286fc4831dc,0x280a3f4a7ad919ff048c,0xba6079c0000784f00018,0x1e0bfc00007836ba0b,0x94bec0976c076d00e800,0x1a08c58c9e5999c5,0xb702c82d3d8000000000,0xdb00000660a000006035,0x83420e00c7cd17220,0x80be13a6600000000000,0x8000010eaa000018a865,0xa9855764184483698059,0x22000006022800001c13],#[0xc0a01c59c9c1,0xa0100000000,0x990021d98af5161e0340,0x1c023f0243e009b7324,0xa74813c1b41d60650000,0x927541ad80dd60359c0,0x212f80000610905067d2,0x200001a6e40000096077,0xa14034fca29400fe0116,0x1e0224201a5f9a5ff11,0x33a42254000000000f0,0x80431807680000000005,0xd0435d073884d9992e73,0xff301372a2a74d16b1c7,0x213d39dfa23ffacc499a,0x9b0630e02e72f2da3c90,0x79cb630350706048402e,0x3032b8410cc73e00000,0x1578233910b0422a0000,0x84139d35643808685b90,0x4e422088be39d3c04440,0x8c05500000103e041444,0x52198c680934110540c6,0x6828cb1c067b539d9251,0x97c045c8029926c6cc,0x208fb0e36482d8221bdc,0x2a7ca8d009f99f9482bf,0x1a40b1a011df0101c113,0x150000034e3f30911f11,0x80ae86c61e0119e2,0xd05c7728b7c06f328720,0xf611902096d4ce32b04e],#[0x5770402a016c00005a09,0x1bd330a52733a0c1ae01,0x99d3c022f8035dd064b0,0x80067f0a4ee05d400003,0x880000a40e7ea22d8046,0x56b064720c2e00002c18,0x732b805e39ba6095240,0x80f7a035a23941e200b4,0x7545309c6f7036ea05c0,0xb8d443b94b64316800b1,0x34c0d3849ee815221a,0xc97e046a234b68325800,0x41411819548362003482,0x100a4ada7c00000c6979,0x55808400000400790000,0x10828e02c380000111,0x605a000024465d822900,0x20745cc2e000006,0xc6057300098000000000,0x71228288df17759088,0x4bba832a000011062800,0x8006f03bce06328097e9,0xfc02cf70bf88221900c1,0xeb82812359046879c466,0x21b800bf3a32001d9800,0x12d1cfb50438004f580,0xc4a7a335010a93004c3d,0x5145518176710414720a,0x650082c82c2d01b446a9,0xb59884780000e1115006,0x20b4c12f80000611b212,0x1c282800008017b2],#[0x968339908905a0f00000,0xf0a1bcb5009304e46832,0x143405ec413fa833db02,0x3a2d08205c20ec2232b3,0x33c0000100237032ff,0xfd30b5274da0e3cd0038,0x8a2286d4ed404194d088,0x6498002ce028e0253d10,0x8620240a560db5c411a0,0xa0eb1a10cc0b75b,0x76006c6830fe14264b38,0x558193a6123b004a9400,0x1241824e2021d40a4c40,0x417500000b027cc0afb8,0x3808d119e1803dbe04af,0xda008c301cd365a2802f,0x61a0b9b9a152501e469,0x3998bb202490b9926,0x659224d20002b999700,0x60ac400005001021239,0x48e812900887c1ab411e,0xcc8d464d08af0099206,0x39c800002146fa842fa0,0x60c4c0000080dbb,0x74018e242e7440379a21,0xaf705bea17db9053cc15,0xa116400003009fd29,0x80c0d39c3e73240ce280,0x61f702a853b96c1176,0x97c186a0b928d4590159,0x722a8147383dcb9c1660,0x2c38247a11ae401fb41],#[0x84089097a3102f204cbd,0x68152000008364d26756,0x15816458061111bd60d6,0x459832e0000000001660,0x38e94895081b3f540,0xc01a880c0302cb410060,0x6062f043800000a3598,0x86aef4cf0782090000,0x52200000000000000000,0x2360000000003964bb0,0xd0bdca1848da5c086598,0x60000064231c3b6a8a1f,0xffe365446b1c01896a9b,0x16010551f30670cf4c90,0x80490000000000000000,0xc4ef1c11a7c6d6408f8f,0x5599e8504c180c88803e,0xdf308d51059c000028e7,0x2097e90afa000000c,0x9520c063cd032d20c8c0,0xc0000506f0e0536c0cfe,0x9bc0fb21d0bf05c3b267,0x38cd0e335900001906,0xc0211433d82623395600,0xc844448bce9ccca0cf2c,0x61085591a80000025023,0xb6b666fe0d9e032cc306,0x1b32ebc017a80d6c33,0x41a000003caa38000000,0xa0b56681b74281000006,0x900000000005046f4180,0x5e05ec000000141f81a],#[0xc33a1ca2b9d048203,0x820032973c06cf806a00,0xf0051b103fa6a5c00001,0x22883000006704b9444,0x78c1cc8c0440ee018000,0x28de28af40ad7a698ece,0xc174601b094151a8322c,0xe0cdb182668020d2d066,0x780e2d3c780139,0x9c2d041182366057a000,0xc538000000000f02bc81,0x26c0cd9ab800001008ac,0x4f3470a67868226801d6,0x340f73b4ba4059,0x9dc0000390512001a000,0x80c40054680a10000053,0xb01b80000280f2681b80,0x9d3900069234c54ec221,0x76f26c462b380000506a,0x1c21aa60fe841,0x5338fca1b8c07700,0x3050f340f246c6a46a38,0x782b800000000008e74,0x62000008057740888000,0x3127024c20a700000284,0x1828d0000000000a,0x10112384b81065c00000,0x4dc18600000838cc0000,0x3d09bdc1fa08331807,0x2e0e0aea0296604e200,0xa6c6d410fb529584194c,0x8a1a921a09a019cb8445],#[0x20c0b1dc27300000f41a,0x18f40d61810a80000ab3,0x11a5e00b800005a88e71,0xf01d5e68dc5a8e4894eb,0x764128a60bcc21d041aa,0xf9002d60832c011c4896,0x89100000614c8cd68201,0x817a80c90305704078c9,0x80000000000000084705,0x83a06f09344000034cc1,0x66ea069e0ddac1cabc02,0xfbacc69000004813b90,0x3000a00d56e0a67c,0x260cb80000d0b6800000,0x49e0ac2811c604aeb097,0x390106c20ce280f002,0xc5e0d07682a17327a00,0x20928000002047323bd0,0x30079701a88000078324,0x17c0719504500000d41b,0x51003f4000049d0cc0c,0x3129166592cfe9184fe5,0x604fc8013800a2c32d89,0x51000c8278cd0680190,0xdfa3059067b14cf3585f,0xc850aa520109029ff91,0x2e933373c00dc80cd18,0x30309e03a86276401b0d,0x9456c0e85a0dbac069,0x79a9a43a2e2823c000,0x98d9940500209a211000,0x8c95a0b0400000c05b3d],#[0x54d217c1f900303015cd,0x23c4274026ff200b607f,0x21a409c9193e90097e0a,0x24c3612a39cbe54090aa,0x6224f40b7a0913e2b7a2,0x86a70300c1e9817a840e,0x8013781409ab2d0b02e,0x164a1a2081af09822b10,0x297421941a3d43aba14,0x900bed0818000069ce3d,0x6341b9a2540000008140,0x37304d9c6cc000000818,0x847404f98162540d161b,0x31f000006098d404b60,0x60c94024689c28a,0x602c4968e3803148104,0x39800008116000000000,0x44182a047820c6dd4,0x18c0000000001068f80,0x34108a9a060000000000,0x30801000009690e0000,0xb70000000000209e6000,0xb43c2a47cca50000060,0x6983be39f8e,0x16a2b300e7e808e00000,0x140bd082d1884ed0000,0x995467648d14c1837000,0x28722782cd6c6021953,0xe03a5a0c9840b9832d68,0x5c33684a1974c4c6599d,0xb7d03110c58c83566ae7,0x4f4d515bc00540000180],#[0x33688467b062a828098,0x3359ee173b00cff,0x4d8064500bb803cc4d8b,0xac00a0f847cc218d80c,0x44189d35a72a22394,0x2e4580eca3340000000,0xd069b80e1000004444a,0xf04b18000096a2e0000,0x420000054234723e9c80,0x1c1b3800000000000,0xe054a8e8300350f06020,0x5009c101820000000001,0xbb605059442d599e200c,0x6646670ad453d80d5a05,0x4382a70765a52b0b1f40,0x43a1ae07c5806cf018dc,0x72307961d50611261d57,0xa4101e58233c0216b002,0x8516335da2d83506aea0,0x1981905120000144f928,0x501f8004a62032f8cefc,0xfa03488412c625264093,0x38073d83ecc729ddd7,0x4d6a8b1d409fc06ec00,0x176681d840153805180,0xf4e7d2a881204d560787,0xaccf98e021d000004807,0xcdf0c4b51c87c8525607,0xcb4d4ca9386a20000000,0x6c5908e8719c69003d5e,0x1a6744000000000b0295,0xee0000300a20483c30bc],#[0x1002e800002820ca39,0x393b6614000051b1300,0x203aa00001828380000a,0xe00001207154a0300000,0xcab01d3e09ddac6291ca,0x8049f20154a402b80,0x6046f62478c18e80,0x51006000014213c44250,0x180000868db06d3241a1,0xf0121bff029fec8a420a,0x2000000000f42831180,0x5ac02af3068a80cc70,0xd7600000100e88196d,0x8414e8102515659fc009,0x2000004019266a6ec6c,0x2d04bf1c9b105a602,0xcd1c2cd0c4899f000000,0x9a07c90177a985f00000,0x85864a1d024a423de01e,0x10806904000018097a04,0x337b40167c0c7229b250,0x6009fc0524a0af10187b,0xda09680406b4117b8815,0x68b0dcf4405940f4941a,0x368403d0c06e7cc1d205,0x82126b3f6a59cf906390,0x5b322d005a00001da877,0x8382fc00001ed3dd0490,0x40800009202406ce6412,0xa0ec80b4563ce48349c4,0x80c2a02c9c0388c0285c,0x64d1d900877034200000],#[0xcc00004029500000200f,0x6e650c08089f03bea00,0x73c0000000000304e727,0x4056c00003208400000e,0x50cc8701a08001c71225,0xb3a27ac00004c253e53a,0xf664d003700000c03,0x12a86d4880b40000000,0x7059e000010e8028824b,0x239fce140ccc1680000,0x3460263067584c538000,0x1db503a0000000000681,0x9b3500001a86f01436a8,0xe046a202bec0fe0,0x7282aae354e605651448,0x4080000f360fa624d427,0x2c602a2c013c62596c0,0xa65b898cea069a000004,0x38e35b01fa3043400003,0x26946f000001404c0000,0x30d7d80000941a2865,0x24940000000008019e00,0x4628a8190f02f265150a,0x2240ac0000294bc76626,0x4580d3260d6220429048,0x5360000098d24a09b663,0x2990a2080000041fbf3,0xc69e0c0a40000071b22e,0x200001e048c5a3998085,0x20c954c0f781b,0xb20506289666601a4800,0x1ccbe038f8680b8c2731],#[0x3322d233b80000000d29,0xe68518904aa8038c0000,0x6f3082700000e0120c18,0x16d3a00240672ca3fac1,0x18b5cc024800000c,0xc0000788468367f28014,0xe4087002879900e40699,0xb5a01160828af0af5684,0x19c84400aa0cc0000060,0x613d90011b8352503544,0x1027ccccf9e0c96,0x6f8041f033c000000000,0x415580d9c202f5869,0x5fda085f0e9861b3100,0x450de0000000002081a5,0x73a4f4080c0385f1899,0x3dc8d5e0000,0x97b028a2000000000000,0x207b0000000000000028,0xe02b05408200000acc46,0x4bb19f00000a72e0483a,0x37ba07750af2e0cb4808,0x17cd03336392370510da,0x80617813823a09c09038,0x40000398347325486beb,0x77e0cda21bbc33476202,0x44cc1268054e00001040,0x990417dc80366401128,0x2170c000051c6e306608,0xe1062c8420a81bcf0586,0x181d780000181ab000e,0x64106c6100bb8018f000],#[0x51140231882844206c86,0x3018c67298902d31c682,0x26244f20409c156fc9a1,0xba23bbc079bcda3e801,0x80a66a08e40000082,0x28be511fa67ef0e3a80,0x488c1a33c60000000000,0x680000f3a0a0000101b6,0xe054a2800000e742698f,0xba1023fc02ac6833c00,0x840960133103d88029aa,0x84d29a02a9a429400000,0x9d103891038206790473,0x7cc9953388c3000004d1,0x24329c1512a10eba4,0x181abe8547000000,0x380227034ea0640,0xea0000000004084b4319,0x93a465720c0b00000282,0x29c04d91c9af00000a3,0xd3ad880afe4d72dc142d,0x100bac000050306,0x660d800000000,0x69d39d6005b80000000,0x168f72066d885849,0x8000010ca9e0cd5004e8,0xf8000000001a059d0133,0x54e9a01f09c5800ab026,0x204ef938e20000008,0x19c2073100000472ec0,0xeda36300fc48320417f9,0xf00000284e9f0621e0bd],#[0x3e1801db05daf8334c0a,0xc168000000000a101fa1,0xf31d7ecc8982d5000004,0x5162799a3ab820700000,0x704259994e8c88d6202c,0x375907f0000030053729,0x9d80000041599828e40,0x16006c000040003c,0x50000060704000051092,0xcab0d0daa1888ce18019,0x27de16ba000004193885,0xda1bb01f5c15ca4daa40,0x702f040a1b6075915733,0x302fd03656a06d102d4,0x7598d0352760a94000]]
def g223D9 := limbs80 #[#[0xee96258120fa94250120,0xfe96250120fe95250120,0xdfb7550120df97550120,0xdfb7650120df97650120,0xfeb8258120fe96258120,0xefb6458120ef96458120,0xdfb7458120df97458120,0x9fd8755120bfb8458120,0x9fd8759120cfd7659120,0xbf980d91209ff8759120,0x9fd87d9120cfd76d9120,0x9ff865d1209ff855d120,0x9fd86dd1209fd85dd120,0xdfb805d920bfb805d920,0xbf9809d9209ff845d920,0x9fd84dd9209fd879d920,0xefb8058960bfb8058960,0xcff74d8960cff7458960,0x9fd84dc960afd84d8960,0xff965501209ff845cb60,0xff97550120ffb6550120,0xffa7650120ff97650120,0xff96458120ff95458120,0xff98458120ff97458120,0xff98055120ffb8458120,0xdff7655120dfd7655120,0xdfe8755120dfd8755120,0xfbd7459120ff98059120,0xeff6559120efd6559120,0xdff7559120dfd7559120,0xefd7659120bff8559120,0xefe7659120dfd7659120],#[0xdfd8759120dff7659120,0xdfe8759120bfd8759120,0xdfd75d9120bff8759120,0xbfd85d9120dff75d9120,0xbfd87d9120efd76d9120,0xbff855d120dfd755d120,0xdfe765d120dfd765d120,0xdfd855d120bff865d120,0xdfc865d120dff855d120,0xdfe865d120dfd865d120,0xffb805d920dff865d120,0xdfd845d920bff845d920,0xbfd849d920dff845d920,0xdff7458960efd6458960,0xeff7458960efd7458960,0xffb805c960efd74d8960,0xdff745c960dfd745c960,0xbfd84dc960bff845c960,0xdfd845cb60dfd84dc960,0xffe7655120ffd7655120,0xffd6559120ffd8755120,0xffd8559120ffd7559120,0xffd7659120fff8559120,0xfff8759120ffd8759120,0xffd855d120ffd75d9120,0xffe865d120ffd865d120,0xfff845d920ffd845d920,0xffd745c960ffd7458960,0xfff845c960ffd845c960,0x5d8128034808c0118000,0x282bc0a1823807e81ac0,0x847010c83f40ed83580c],#[0x614171857814c84fc12d,0x801d287141b786a01968,0x4231888821288041f187,0x28e8a0426f8978252890,0x98bc82e28b3c2b98a90,0x28dbc35b8d283348c743,0x8f703c88ed43a78e4838,0x13c43f90b041c900c3ef,0xf04ae926448591d84649,0xc51794084ee93844c992,0x59e962c575956854894a,0x1d98305f4976c5c796d8,0xc99d4665994864098ac6,0x9b906d49b146b19a7868,0xd447419cd07229c3c6fb,0x307ba9e9c78f9dd87649,0x4829a0508069fcc7df9f,0x896a21c875a190852a0f,0x9e0b842c2b9088b7a2a0,0x29e7e682e10ae4201433,0x82d3a2f84299e9b90845,0xb118269e78be10aa6e42,0x353a2c2b87159e9b9090,0x69b9098be1a6670ae418,0x60ae41c462da42b9f871,0x9b8428a790969e78be1a,0xe6e10ae4101844420b9f,0x848a79f86299b17909e7,0xb8a10e7e1c56629e4260,0x24302b9f86a59b1790b0,0x10a9e7e1660ae41d302c,0x2e41f9f8628419b17907],#[0x170a9b90809e1a7a6c5c,0xe1a6c5c2e420a52b9f87,0x1f87170b90486a907e7,0x9094a10e7e1a6c529e42,0xe42444439f871708a69b,0xf9081110e7e1c5c229a6,0x214e420269b170b84519,0x86982b90769e7e1a6c5c,0x69e7e1a60ae41854259f,0x111e41b9f9b842b90446,0x9f8717099b9080ae7e6e,0xe7e610e1290ae41ea62b,0x41f170b9f9b84a42b908,0x879044714a9e7e1660ae,0xe7e6e1e4111d0b9f9843,0x439f859a970b9080942,0x99b908e166a5e41014b,0x66c2a5e4239c4b844297,0xf859b0b90446104be7e1,0xa698b8ae167a6c5e4281,0x2e2b859e9b15a790a0b0,0x694e67e1a60ae4282c2a,0x5a79f86982b909158b0d,0xb67e1a6690ae41e2e084,0xa24422b859d9b1790b8,0x128ae166c529e42428a6,0x79c50a59b842b90b10e7,0xb1066e1c5e429302ea71,0x859b1790408a9128ae70,0xd0be1c5e42f24a79e2b,0xf170b869e9b909164aa6,0xf29e1a7a6e44a1d28a43],#[0x5a992927170b84bf90a0,0x790949a6e12f4ae4185c,0x44a252aa79c4a982f871,0x9f909e7c2140ca90be1e,0x29e4244c48a787170a99,0x69b90c2f12e1c567a6c2,0xd39352856a4499f170b8,0x9b909a912e167a6e44a1,0xe44a1f28284b859f170a,0x92b869b90ae7c229e1a6,0x9a64ae4204440a79f170,0xa7869b9128714e7c2e12,0x4ae7a6c5c2e1e4251e9c,0xf08509e9b852b90a47a9,0x6a9e7a6e14ae4184aa79,0xa6a9e42f0b9e9b852b90,0x1286154e4d4a67c5c2e1,0x567c229e427859e9aa79,0x8698a52b90a130aa6e1c,0xe1294ae424539f084443,0x59c2a9b90ec21110e7a6,0x54513936322f0aa5a78,0x90d0c29c20be167e4142,0xa714529d9f08a7842a9b,0x67a70aa6e169e42a322d,0xb9c2ca78790509148c8b,0x9a6c5c267e1e42c31a70,0xa7859f905088c8b8a146,0x670ae169e41424302c29,0xe9b1709a78790c0ce70b,0x2e169e42e322e299c539,0x90508148c8b8ae7a6c5c],#[0xe10ae418302da79c2b87,0xaa79f859b9228ae7e611,0x5c2e766e1e4204443170,0x170a2b9f859b909678ac,0xc2e729e166e48a1c4443,0xe9d9c44438697099b90b,0xc42e7a5e166e410204b1,0x252c439f099b86979090,0x2c0942e7e166a5e41026,0x1e41c4b9d9b869443907,0x9b869790b100ae7e6e11,0xe4102724412e2a9d9f09,0x59b9098a672ca7a5e166,0x5e4102047262b9f0a978,0x859843906124be766e1a,0x12e766c2e111e41f9e97,0x124a69f0a98bf852b809,0x80ca7c229a62fe14ae02,0x5854529f169b08bd2b87,0x4a67c5c229a6e1e02c5c,0x9369857852b80913128a,0x5c267124ae1e02138a70,0xa49b17099c4b878092fc,0x10c5c229a6e1e04a2528,0x499f169b092b8780911,0xa780a29c2a6e14ae0185,0xe0245539349b099f852a,0x780a158c8bc2148a2fe1,0x22322e28a59f08529b8,0x878088c8b8ac214a6e1e,0xe1e08a2052a59f0a299b,0xe9787804071110c2a966],#[0x9108a66a5e1e0204a252,0x1e299d9a94b3878074bc,0x1110a58ae166e0]]
def g223H9 := limbs80 #[#[0xe0850628108000018104,0x14a021e04204040010a0,0xc58706040800a2030004,0x803320408008009925a1,0x260a5c2010a606044400,0x300000091004880321c1,0xa1028002043801a082a,0x210102000c2814c001ab,0x10012380011202f40bc0,0xc0050400000040040006,0x70700041380638e13000,0x8200400001e001871a0c,0x9026c20b0000305041c1,0x3e083840c0861b1c0020,0xa0018d020dd951c41180,0x7c38b741401010249001,0x4080065c08110ec28202,0xb00184c2003e80298023,0x1062055d06484002400,0x50020422101010502000,0x1a9c1831008182140421,0xa8008000891800600083,0x9849d1404b0404000061,0x4103007810d024909008,0x1800008195003c008aa1,0x87001cb4c1aa40025800,0x1141400c16b01850a219,0x458a1700200cf121018,0x7d3812228c000002406e,0x75e0092823c400004202,0x83bb1042000030071b05,0x81f700001e0062441058],#[0xb01c04218d2a577c249b,0x202382646cc511,0x8b000000000006238000,0xe0360196f02320000254,0xce71800005015b020598,0xdc0eaa023800000a0624,0x3005591ccc203760101,0xb790aa68090c143a000,0x2dc00003017500001e0,0x608f9c1152009b909a8a,0xb4417b14c3a88cca03e2,0x1605968108800000025,0x3dd64066904ed198a000,0x332811150c90fa8d360,0xd01cb264334120000000,0x210438e089dda72b8a37,0x1b60b9ba074100323991,0x14043b82b6306,0x1e4e020a004af40a080,0x811b53206330ac00001,0x3a88b5b011a000000412,0x8501e58403ba735760c,0xf7ec16d980bee062080,0x42e5b0106a0c64023200,0xf8d0e1809a000000064f,0x2ccab481e1002114832,0x1423e0000000000000,0x80540000000000000000,0x67480000108ce301e92,0x80d458928739e4,0x1364c9009cd98210000,0x9f7a1814000078482000],#[0x313fc10a60c1a5020c20,0x24022e0181011e6195d0,0xb2623e4091400001a828,0x380bb700d,0x5fe00000ca5a40000000,0x121608e4870c3400b20,0x7017950207701e7c076a,0x6000bf939d34d06ec100,0xfd81600008e8001e408,0x822f04100000209,0x3811204141e03240,0x7cc19000000000000000,0x81b300001c10f,0x31c0000000001b03a000,0x1c04ec85267821064,0xe13c0000000000000000,0xcc61fc00006015700000,0x9200001c25c80000e001,0xe834c000029c35802,0xa340101800c3f922b00,0xf98a50d39000004418f8,0x70430e12b88067bc047,0x91603bdc12b3023d0000,0x4900000000000023398,0x20a9bc13ad50253c,0x8000060195064c5803e8,0x1f5d0afbea6f71428,0x481328042902044000,0x978000000000a707c00,0xb00d4000004,0x5d8f8b00dc7221d603d8,0x3800007807b430b8c02c],#[0x800000688d804004a20,0x646050356044468269a0,0x2812c00004016c030ad4,0x62137a40f950096a3030,0x24039000005001,0x29a00001da0904106000,0x39b520568c91c8000010,0xd30f960589985a800c19,0x2203bfa0734000000000,0xf1f0095c207780d36802,0xc2600000000002c99c80,0x1cb839cc00000000001,0xe88dee006c000018021a,0x14044,0x2017c000,0x41281169f102a6090c00,0xc05a800ee981f6861ea4,0x7c0047190a10964a05dc,0x921a6044a,0x9892105cc433b8000,0xe0a3e816f0089c00,0xe027ae0808819c000000,0x80000000004814ff321e,0x9de73d84116081aab39b,0x140461021d2005c798,0x11960015808898082800,0x2409a40b921cc90,0xf035200001401900000,0xe0069207e800460000,0x216800,0x8b08e00000000000,0x3013bd419a0000200f60],#[0x359858b827ee083580ec,0x6b00000682d800000422,0xbf800000000000001c4,0x1462a803340148000000,0x540b300000e0af9c48ab,0x4cf05815200000a081,0x2e0803ad0042c09a2000,0x512cc2cb305753057c0,0x412730c88281a0e02148,0x6a0728c21c1988740435,0x6ba01ba100861054339a,0x3fd6209f00176284ad02,0x6227348d485b81edc0,0x40321223484e6c801b6c,0xfe033d90627882ad0183,0x10105ecc873423ff810,0x5d1e403fe6794c109019,0xc159a3850c685180c8c8,0x184ef302a04168f0cd2e,0xa7941b00001a0375ccae,0xb6e1cc8d08e190722446,0xe15844ff045e6136d80,0x643300000e0042006174,0xed8915c1008048800003,0x7cc10bd04d7b00b18066,0x38eac7de01ea34058403,0x80fb60110000002d,0x821ed10040,0xdc006782bf00000d0180,0x183e5028,0x40a35000,0x14078c00002802400],#[0xa803c00007986f0,0x5f0468205fb80aa80000,0x6600001c0287047089c2,0x30b00b2000000000630,0x57f0000047377811850,0xd843e00202000024061a,0x51853e0855a089640f5,0xc880000d01e000000000,0x11eb012a401640000254,0x702206244f41763c,0x3880b5051c401d600000,0xc042b780000e02ac0000,0x654000000000c39a1c64,0x8980000384f6f02bae0,0x1440500000000014,0x200000d4630000000000,0x1070f80000380f96043,0x8011000,0x3e800000c466a081f00,0x407700000000001,0xc0300c1450000000000,0xd4b0c620000000000000,0x13094000041c,0x1009600002047680,0x80000d838da027340fe0,0x781c2150379a4894c11d,0xc95043c000004a61b0cc,0xbd800007004da024ec0,0x930ee00001c,0x1c0700000070b7d01100,0x2700e752819c0007604e,0x47d823b5005300001a00],#[0xa1,0x14864508d3402080,0x1206b0000000000508da,0x7d86154144900000b735,0x42c0000040b519890b09,0x1203632c8000000f0,0x669cc0000280d2ecc900,0x70c5800003c0310046e,0xe800000a06e000000000,0x30b4615b66c98401,0x82040000000000000000,0x808700001e007ac3108,0xbe995800000000001065,0x8301420198030,0xa2c01fd409f16168400,0x8c7669c29311c44613f8,0x5062d9848f02a7a1666,0x3209c70801211afe072,0x2600062401639038a000,0x5cc000000000d004a60,0x3002a80000000010,0xf6114bc09b4047552036,0xe200002609900000b615,0x27a000000c750c169580,0x1403f800000000010,0x82350,0x6205000000807d900ae,0x201724704642728000,0xe00784a31c0000000,0xb121981f380100000000,0x3082ef02944c1f000005,0x401d7911b60000200f0],#[0x6ac80acf038280308000,0x2418a639e02109e40,0xc0240005a000004013c0,0x3005a64104908fc00002,0x58000000000e315cc05e,0xa554c65001c402d1603,0x4107b21577008b60,0xa04a540738000090b880,0xd280ac000069ceb7027c,0x49f03f4e51790148181f,0x4523042fcceb1209cc04,0x303b21142400d38562d0,0x200de823698096000ff2,0x8e3173200040000500fa,0xe8801f1f041c00ce9846,0x1dd00001e17fd9487a80,0x900d2800edc10878,0xa9916c3247a08e400000,0x300000e0334c04818116,0x10d88330000121362900,0x229b00b0e04060000282,0x146b506301036ee065d8,0x44111d191eb4213ed097,0x198042701fb7019a6601,0xe1486808171c82e3a02,0x4a000005015ce610f66,0x208da001580000000014,0xfa0509080a80000408de,0x4000003830200000b100,0x7b2158d4ccc91917a0c,0x29c0000382319a0cf90,0x61195442600013b080f8],#[0xdf52b90831a827200000,0x15303c4d04f800c5301a,0x1b2301cdea4570091fb4,0x842450bfb0732c2099e8,0x6018b7118b6059fc063c,0x5e0114a03b60642c0000,0x800000f0aed2079d810,0x79841414448025d84,0x209ca811600001815ec0,0x1807540512a0a18248b4,0xdc000019c3a301980000,0x2a07e02826f4033408,0x1584c221ed9040000000,0x7274468404e080373e,0x5e050080015011e103b2,0x96e8001005d48080f037,0x2ae612e08293d0465430,0x11d8012d68914e805dd5,0xb0196163f5da2700000e,0x50011000002d409104d6,0xafa225a33432cc42c800,0x630a4563fa40d3a18,0x633681fe66476c27d00,0x701641024ec800c00004,0x35c194a019da6719c02a,0x3bf823a23871201d10d0,0x6808120263a03a5e0,0x59cd120349e70b40,0x1c0b48010b0000180610,0x480658807e0000,0x2ccd780000d0966000,0x170c0000000009306600],#[0x7047100000e,0xca05c250268000000000,0xe64045c0000400c8203c,0x1600e88e7788038900,0xa01b74c6f0000000,0xf00ec00002402f000000,0xc239b60000380e600000,0x1a0100c444ac005e3800,0xd100000412dbc0c7181,0x82090000000000000038,0xa850d50ae52656dd063e,0x49cd700000e00aa80e9,0x18310000106564000,0x89500000d005e2091800,0xccdd3c137e0144000024,0x1811d00000c0149,0x48057922280000,0x468445d708c69011e000,0x1c40cdc984e300001e4,0xc808c0000000005023fa,0xfe034f4069580aa3092d,0x1305860ae,0x3846880000000,0x69c2a00,0x45048000010ca2800000,0x6823c613a4467b1866,0x39f0047462d6185c0000,0x578b002a000004026d00,0x47300000e01f3c02838,0x300cf060dc00ac6,0x11305930153a03b1827e,0x2100000e00f4a206400d],#[0x29e000005037cf63fc01,0x40ed4003f603f0804cc4,0xf540b01915e100681266,0x6b426ad8061000016044,0x2405400000e0482335,0x1422d800000000000,0x8007c00003889c000000,0x3c10200000,0x2a0601a2c82b019f0000,0x657e660d91d58001,0x401c8115000002005b00,0x140e13c8142680000c,0x400000070ce442e80000,0x950051a15b81078d81b,0xa5f0ad74151b485e581,0x10000000000002cc9d80,0x100af73863e80079c5ab,0x7004e80114000000000,0x844c382a00000000,0x460104f540860e061800,0x48a28c8a340ae05e92,0x48c9aa849f7007de052c,0xfc0d0e882c308102038,0x5a00421b8568403a2005,0x934022e6003630,0x263e6ccde3813a6204e0,0xaa0001007bd00145037e,0xa8004544cff102068036,0x467015c0000062024103,0x1c5810e640428000000,0x28c92000001,0xd014ca6839005180000],#[0xd5086a0000240d78000,0x63800001e23640297e19,0xd118e000038077f8,0x29e2870463304c360ae0,0x9b00fca01a0e07a50c21,0x20e1a020000000001405,0x6c158a0b800804800,0x828200d4c146d680780,0x400006b42d4104762357,0xcf4e6310584100c66146,0x2f8000000000b038fa07,0x640a0215c1ce5f0269a0,0x60e5c110800001306d1,0x94806900538000030451,0xe4000038a0040130b02a,0x6ea035c40e270826701,0x41ce07c2c05ed05a0e0,0xb047fa01a34f1301c273,0xf000000000280ffb00f5,0x703f2000014041c809,0x12000012136b8473800,0x124e025d2060a480998,0x39960000000000281015,0xf000d9d0884000020273,0xaf5a98b9383400000c2c,0x61c42a026f40748c0,0x0,0x382905c06f0000180434,0x6f881200000002e80000,0x168cc910859b00001208,0x2830e1345250356ec,0x4041c0000490d6b01320],#[0xc8084ccc2613048430a2,0x86000010e209810230a1,0x27800000000000000103,0x38360000000000000000,0xb09b8001c0507080000b,0x60000000000000041cd8,0xb031a40034cc889201,0x1c002accf8800,0x2010000088084000000,0x1018f451a1e01fc00007,0x2203b0000000378c217,0x100000000000f0414000,0xc0be05580035dc833090,0xc44e9a81500000000034,0x180d878207f00ee00002,0x8000003112c000000000,0x317010a992247037b022,0x64ec421d800003009984,0xa022e00a649ce400000f,0x30289b312051078,0x2220828000041c240000,0xbb4a656980a898122c50,0x3b6d0a9004a0000030,0xb00f00000300adc00dac,0x332216602498d0220051,0xce1103c666a0450d984d,0x8f68386c2706542eb5a0,0x81a3109a5605664409c9,0xd880030223200b28035e,0xcb9ce07011da073d0062,0x7998006e0c6f482d4426,0xcc231e5781ee6c48cc0],#[0x506400000c0464606068,0x699fd01035205f2,0x5a82140000080362a23a,0x100630000000001c70,0x630c03f10609e043a00,0x2051c491108425000008,0xc20495007ef816100000,0x4a6005d8e0e09cd6b826,0xa180000280078808250c,0x27ec02ec00007190916,0x841c58680110aa800005,0x60c27608ae085f9882b,0x8000001c646400000000,0x84800001c04000000304,0x52a000000000040721c,0x8000000812c62e3c0227,0xc00000f3824f06394c04,0x5b104dd0000000003943,0x30c00000402fba806340,0x800400026000038,0x982cf801c6782902115c,0xa07a08194131d32808,0x2da0c170000000000000,0x237f803ce0441b006b66,0x618d000005021f8398ac,0x620888c0afe816e152bc,0x201b240eb00000f02d]]
def g223D10 := limbs80 #[#[0xd74483fcb0241fe50120,0xb2417f5d920bfee8905f,0x60dfec4b06fd62582ffb,0x7fd54482feb96c17fdc9,0xeba241ffd9120ffac890,0x8960ffcec907fd76483f,0x7ff72583feb92c1ff5,0x9962be4bc788c10ea0dc,0xc71cd097eaaa4a0848ed,0x9f0a68b90791b12201bc,0x40b3e6c2a4545c840b15,0xc3058a139f0a68b0b21,0x3618b0b210273e14d905,0x83a9cf9b0e414329159f,0x1296164244e7cd852c2c,0x7cd852c2c838a219f361,0xc239f36184252e42086,0x78a92a57cac29e2a6859,0x490a94a73e18a9a1642c,0x2a50acf862a684a72122,0x42210c16a4a67c298564,0xa9159078b094e7cd8456,0x3e6c2252c2c84c2cf9b0,0x4510cf9b0c24b9092243,0x9059f3614b908112]]
def g223H10 := limbs80 #[#[0xa1584021080108821,0x104e1280420050219401,0x80220800008c01,0x10021080402008018c09,0xc60190010080010050,0x6810000,0xeb819c11680000000000,0x59838000485d0022881,0x9a18d000079ad8000000,0x100,0x38000000079988000000,0x303a3897c82180001c3,0x71d480000000000,0x0,0x108500000000682e800,0x0,0xb0000000000000000000,0x141cc05f8862980c193,0x3c1a082000000000000,0xd00000000081e0000000,0x68433820f06,0x5a811098000,0x0,0x8000000000000704f800,0xc21902801382c80001a8,0x80000204500000000602,0x5051800000000000105,0xb598530668000280d000,0x2d98800000004c35ea1,0x580c800000000000000,0x500000000241c4107000,0x98000104620346072420],#[0x6045f81480000000683,0x80000000078150000000,0x184,0x87080000000000,0x1032800000000000000,0x65c92000000000000000,0x2800018bb58768000243,0x54198000401fe051680,0x783b3072e9ed8000000,0xd0000000058af0000000,0x7071f02,0x77111000000000000000,0xb00002817c036791f119,0xa20054831584a000059f,0x688,0xc0000290300000000000,0x686cd0958833787,0x3082a99500003054800,0x11ae0000000,0x6c09d38000000,0x41c3800,0x3111800008488000000,0x6827f80eb05d8000000,0x4801800,0x1808000,0x79909901000,0x788800000000203,0x5b12000000005835000,0x5817000058368000000,0x402bf02380000000000,0x182401c200000000000,0x0],#[0xf78b0800000007063000,0x406,0x30158000481df091000,0x82b000,0x4807800000000000000,0x6096d996387a0000000,0x502500000000000,0x529b00000000000,0x4418e8186871000,0x5026282f8000000,0x2a850000787b8000000,0x61aa801080001032000,0x2811800000000000000,0x6d06e000000000000000,0xf000000003cc20000705,0x11ae80006a9,0x0,0xa0000000000000000000,0xa996f829aa208802301,0x80300004033e195e03,0x4f881000000006985800,0x6901bb00f22080000743,0x3811203198004824921,0x3c853800000000000000,0x1b052685f0043a016588,0x839000000000000418,0x0,0x0,0x218600000000000,0x11d5682ae087000,0x306df022286b0000000,0x3c1aa0950000000],#[0x1e047000000000000000,0x90000000000000000488,0x5800040420000412db20,0x21819000000000000590,0x3983081,0x781c7016aa01000,0x3005800,0x7a0980000094dc23800,0x826800068210000000,0x2761bb0000000,0xa890000000,0xe0000000000003825800,0x78008000111799d4741,0x681d69c2800,0xce81f000001ee8000000,0x68066905381,0x489f00005c16000,0x2fa018000280a2191000,0x4800000000000083cc05,0x30000000000000000780,0x50000000000006838788,0x69183419180e307,0x0,0x7c86b800000000000000,0x283,0x412e0000000040ad800,0x5342009180000000000,0x30000000058820000000,0x582,0x718d8a0a9d965a03000,0xec9d5800000007078000,0x86],#[0x76813800000000000000,0x51c332a8afa968000203,0x505,0x207b012f192e8000000,0x0,0x483a902f29c1800,0x200f80000000000,0x230650578000000,0x110a580ac0188000000,0x0,0x281400000000000,0xcf21f098680000000000,0x7301b082d982932a0a87,0x302a785,0x800000000483be835800,0xe000040ae00000000682,0xd901ad854005e8000384,0x2842a02e11d10009780,0x21c348703807000,0x98000684680000000000,0x1ee000000000000628,0xb00000000683c2108000,0x38000000000000000119,0x7066200,0x0,0x18aec0640000000,0x7808800,0xb8000213080000000000,0x20000006048348000100,0x5006d189c80b00000a0,0xc8000000000007012800,0x85],#[0x687a800000000000000,0x37885800000000000000,0x4018e800000007061201,0x5038885580532028c80]]
def g223D11 := limbs80 #[#[0x4666c03ff60ff583fd20,0x4b08520e4953cd08a148,0x13cd2c211320e4cf3]]
def g223H11 := limbs80 #[#[0xc060181010301214,0x40000000100be03d046,0x4ac09891c000e2104818,0x8000452c0008140000d0,0x1892b00,0xc06830c470000c0c0124,0x7008e82c8022887203b0,0x4144488000010c00038c,0x500d811e304000,0x2db14b42b00179870,0x1889a38348600,0x4017028000f111041e53,0x91000000000004041242,0x18076120000b0348,0x542f0200002e0b000000,0xf088000]]
def g223D12 (j : Nat) := if j=0 then 0x1cc5104837f else 0
def g223H12 := limbs80 #[#[0xe10000017b2394724a,0x6020020d780950680000,0x719962002e0110]]
def g223L : Nat → Packing
  | 5 => (9,7,5,0,0,9,0,g223D5)
  | 6 => (293,6,5,0,0,13,0,g223D6)
  | 7 => (879,5,5,0,0,15,0,g223D7)
  | 8 => (583,4,5,0,0,16,0,g223D8)
  | 9 => (122,3,5,0,0,14,0,g223D9)
  | 10 => (19,2,5,0,0,11,0,g223D10)
  | 11 => (3,1,5,0,0,7,0,g223D11)
  | 12 => (1,0,5,0,0,0,0,g223D12)
  | _ => emptyPacking
def g223I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 7 43 3 13 4 5 g223H6
  | 7 => lookupWord 217 997 10 18 9 5 g223H7
  | 8 => lookupWord 565 2789 8 19 10 5 g223H8
  | 9 => lookupWord 320 1747 7 19 10 5 g223H9
  | 10 => lookupWord 79 797 5 16 7 5 g223H10
  | 11 => lookupWord 13 89 4 14 5 5 g223H11
  | 12 => lookupWord 3 19 2 11 2 5 g223H12
  | _ => fun _ => none
def g223 : Forest := ⟨223,12,fun i => g223Y[i]?.getD (0,0),g223C,g223A,g223L,g223I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P5_0 : block g223 5 0 9=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g223B5 : block g223 5 0 9=true := g223P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P6_0 : block g223 6 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P6_3 : block g223 6 3 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P6_99 : block g223 6 99 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P6_195 : block g223 6 195 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P6_291 : block g223 6 291 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g223B6 : block g223 6 0 293=true := (@block_merge g223 6 0 99 194 (@block_merge g223 6 0 3 96 g223P6_0 g223P6_3) (@block_merge g223 6 99 96 98 g223P6_99 (@block_merge g223 6 195 96 2 g223P6_195 g223P6_291)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P7_0 : block g223 7 0 65=true := by
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
theorem g223P7_545 : block g223 7 545 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P7_641 : block g223 7 641 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P7_737 : block g223 7 737 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P7_833 : block g223 7 833 46=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g223B7 : block g223 7 0 879=true := (@block_merge g223 7 0 449 430 (@block_merge g223 7 0 161 288 (@block_merge g223 7 0 65 96 g223P7_0 g223P7_65) (@block_merge g223 7 161 96 192 g223P7_161 (@block_merge g223 7 257 96 96 g223P7_257 g223P7_353))) (@block_merge g223 7 449 192 238 (@block_merge g223 7 449 96 96 g223P7_449 g223P7_545) (@block_merge g223 7 641 96 142 g223P7_641 (@block_merge g223 7 737 96 46 g223P7_737 g223P7_833))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P8_0 : block g223 8 0 12=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P8_12 : block g223 8 12 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P8_108 : block g223 8 108 87=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P8_195 : block g223 8 195 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P8_291 : block g223 8 291 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P8_387 : block g223 8 387 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P8_483 : block g223 8 483 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P8_579 : block g223 8 579 4=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g223B8 : block g223 8 0 583=true := (@block_merge g223 8 0 291 292 (@block_merge g223 8 0 108 183 (@block_merge g223 8 0 12 96 g223P8_0 g223P8_12) (@block_merge g223 8 108 87 96 g223P8_108 g223P8_195)) (@block_merge g223 8 291 192 100 (@block_merge g223 8 291 96 96 g223P8_291 g223P8_387) (@block_merge g223 8 483 96 4 g223P8_483 g223P8_579)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P9_0 : block g223 9 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P9_2 : block g223 9 2 37=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P9_39 : block g223 9 39 63=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P9_102 : block g223 9 102 20=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g223B9 : block g223 9 0 122=true := (@block_merge g223 9 0 39 83 (@block_merge g223 9 0 2 37 g223P9_0 g223P9_2) (@block_merge g223 9 39 63 20 g223P9_39 g223P9_102))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P10_0 : block g223 10 0 10=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P10_10 : block g223 10 10 9=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g223B10 : block g223 10 0 19=true := (@block_merge g223 10 0 10 9 g223P10_0 g223P10_10)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P11_0 : block g223 11 0 3=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g223B11 : block g223 11 0 3=true := g223P11_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P12_0 : block g223 12 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g223B12 : block g223 12 0 1=true := g223P12_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223T : checkedTables g223 12 := by
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
  · exact g223B12
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223G : graphValid g223 (boundsBefore K191) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low223 : Lower true (varsX 223) (graphGoal 223) 13 := lower_forest (g:=g223) (i:=0) (hints:=4146) (before_sound K191 V191) g223G g223T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K223 := extendKnown K191 13 [(223,[]),(247,[83])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V223 : Known true K223 := extend_ok (m:=223) V191 low223 (by decide +kernel)
def g253Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x8e6760072000000000,0xffc00003ff00000fffff])),(BitVec.ofNat 152 (word80 [0x844740012000902409,0x2409024090240902409]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1abc0dc00400003ff,0xffc00003ff003ff])),(BitVec.ofNat 152 (word80 [0xa0008c0041204812,0x4812048120481204812]))),((BitVec.ofNat 152 (word80 [0x80751db28980000000,0xffc0000000])),(BitVec.ofNat 152 (word80 [0x806118b28194751d47,0x51d4751d4751d4751d47]))),((BitVec.ofNat 152 (word80 [0x641088d044800ffc00,0x3ff00000003ffffc00])),(BitVec.ofNat 152 (word80 [0x201088500482409024,0x9024090240902409024]))),((BitVec.ofNat 152 (word80 [0x2714d7088ac0000000,0xffc0000000])),(BitVec.ofNat 152 (word80 [0x2714c7080a6b8ae2b8,0xae2b8ae2b8ae2b8ae2b8]))),((BitVec.ofNat 152 (word80 [0xf9881a2a3b3ff00000,0x3fffffff0000000000])),(BitVec.ofNat 152 (word80 [0x59081222080c0300c0,0x300c0300c0300c0300c0]))),((BitVec.ofNat 152 (word80 [0x12402621577fffffff,0xffc00000000000000000])),(BitVec.ofNat 152 (word80 [0x200240053300c0300,0xc0300c0300c0300c0300]))),(0x0,0x0)]
def g253C : List ColumnInfo := [(0,8,213,32,11)]
def g253A : List (List Nat) := [[],[118],[100],[100,116],[116,100],[116],[83],[83,118],[83,100],[83,100,116],[83,116,100],[83,116],[66],[66,118],[66,98],[66,98,114],[66,114,98],[66,114],[66,83],[66,83,118],[66,83,98],[66,83,98,114],[66,83,114,98],[66,83,114],[98,66],[98,66,116],[98],[98,114],[98,116],[98,116,66],[98,83,66],[98,83,66,116],[98,83],[98,83,114],[98,83,116],[98,83,116,66],[114,66,100],[114,66],[114,98],[114],[114,100,66],[114,100],[114,83,66,100],[114,83,66],[114,83,98],[114,83],[114,83,100,66],[114,83,100],[32],[32,118],[32,100],[32,100,116],[32,116,100],[32,116],[32,83],[32,83,118],[32,83,100],[32,83,100,116],[32,83,116,100],[32,83,116],[32,64],[32,64,118],[32,64,96],[32,64,96,112],[32,64,112,96],[32,64,112],[32,64,83],[32,64,83,118],[32,64,83,96],[32,64,83,96,112],[32,64,83,112,96],[32,64,83,112],[32,96,64],[32,96,64,116],[32,96],[32,96,112],[32,96,116],[32,96,116,64],[32,96,83,64],[32,96,83,64,116],[32,96,83],[32,96,83,112],[32,96,83,116],[32,96,83,116,64],[32,112,64,100],[32,112,64],[32,112,96],[32,112],[32,112,100,64],[32,112,100],[32,112,83,64,100],[32,112,83,64],[32,112,83,96],[32,112,83],[32,112,83,100,64],[32,112,83,100],[64,32],[64,32,118],[64,32,98],[64,32,98,114],[64,32,114,98],[64,32,114],[64,32,83],[64,32,83,118],[64,32,83,98],[64,32,83,98,114],[64,32,83,114,98],[64,32,83,114],[64],[64,118],[64,96],[64,96,112],[64,112,96],[64,112],[64,83],[64,83,118],[64,83,96],[64,83,96,112],[64,83,112,96],[64,83,112],[64,98],[64,98,114],[64,98,32],[64,98,32,112],[64,98,112,32],[64,98,112],[64,98,83],[64,98,83,114],[64,98,83,32],[64,98,83,32,112],[64,98,83,112,32],[64,98,83,112],[64,114,98],[64,114],[64,114,32,96],[64,114,32],[64,114,96],[64,114,96,32],[64,114,83,98],[64,114,83],[64,114,83,32,96],[64,114,83,32],[64,114,83,96],[64,114,83,96,32],[96,32,66],[96,32,66,116],[96,32],[96,32,114],[96,32,116],[96,32,116,66],[96,32,83,66],[96,32,83,66,116],[96,32,83],[96,32,83,114],[96,32,83,116],[96,32,83,116,66],[96,64],[96,64,116],[96],[96,112],[96,116],[96,116,64],[96,83,64],[96,83,64,116],[96,83],[96,83,112],[96,83,116],[96,83,116,64],[96,66,32],[96,66,32,114],[96,66],[96,66,112],[96,66,114],[96,66,114,32],[96,66,83,32],[96,66,83,32,114],[96,66,83],[96,66,83,112],[96,66,83,114],[96,66,83,114,32],[96,114,64,66],[96,114,64],[96,114,66],[96,114,66,64],[96,114],[96,114,32],[96,114,83,64,66],[96,114,83,64],[96,114,83,66],[96,114,83,66,64],[96,114,83],[96,114,83,32],[112,32,66,100],[112,32,66],[112,32,98],[112,32],[112,32,100,66],[112,32,100],[112,32,83,66,100],[112,32,83,66],[112,32,83,98],[112,32,83],[112,32,83,100,66],[112,32,83,100],[112,64,100],[112,64],[112,96],[112],[112,100,64],[112,100],[112,83,64,100],[112,83,64],[112,83,96],[112,83],[112,83,100,64],[112,83,100],[112,66,32,98],[112,66,32],[112,66,96],[112,66],[112,66,98,32],[112,66,98],[112,66,83,32,98],[112,66,83,32],[112,66,83,96],[112,66,83],[112,66,83,98,32],[112,66,83,98],[112,98,64],[112,98,64,66],[112,98,66,64],[112,98,66],[112,98,32],[112,98],[112,98,83,64],[112,98,83,64,66],[112,98,83,66,64],[112,98,83,66],[112,98,83,32],[112,98,83]]
def g253D11 (j : Nat) := if j=0 then 0xff else 0
def g253L : Nat → Packing
  | 11 => (1,0,1,0,0,0,0,g253D11)
  | _ => emptyPacking
def g253I (_ _ : Nat) : Option (Nat × Nat) := none
def g253 : Forest := ⟨253,11,fun i => g253Y[i]?.getD (0,0),g253C,g253A,g253L,g253I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P11_0 : block g253 11 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g253B11 : block g253 11 0 1=true := g253P11_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253T : checkedTables g253 11 := by
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
  · exact (rfl : block g253 10 0 0 = true)
  · exact g253B11
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253G : graphValid g253 (boundsBefore K223) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low253 : Lower true (varsX 253) (graphGoal 253) 12 := lower_forest (g:=g253) (i:=0) (hints:=3166210) (before_sound K223 V223) g253G g253T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K253 := extendKnown K223 12 [(253,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V253 : Known true K253 := extend_ok (m:=253) V223 low253 (by decide +kernel)
def g255Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfc0000003fff000000,0x3fff0003fff05c2f])),(BitVec.ofNat 152 (word80 [0x140450114045011404,0x5011404501140450082f]))),((BitVec.ofNat 152 (word80 [0x3ff,0xf0000000fffc0001b878])),(BitVec.ofNat 152 (word80 [0x4c213084c213084c21,0x3084c213084c21309878]))),((BitVec.ofNat 152 (word80 [0xfffc000000000,0xfffc0000003fff01d51])),(BitVec.ofNat 152 (word80 [0x2808a022808a022808,0xa022808a022808a01450]))),((BitVec.ofNat 152 (word80 [0xfffc00,0xfffc0006200f])),(BitVec.ofNat 152 (word80 [0xb142c50b142c50b142,0xc50b142c50b142c22007]))),((BitVec.ofNat 152 (word80 [0x3fff0000000000000,0xfffffff000000000292])),(BitVec.ofNat 152 (word80 [0xc013004c013004c013,0x4c013004c013000080]))),((BitVec.ofNat 152 (word80 [0xffffff,0xf00000000000000603a0])),(BitVec.ofNat 152 (word80 [0x29c0a7029c0a7029c,0xa7029c0a7029c040380]))),((BitVec.ofNat 152 (word80 [0x3ffffffffff000000,0x800c4])),(BitVec.ofNat 152 (word80 [0xe003800e003800e0,0x3800e003800e0000000]))),((BitVec.ofNat 152 (word80 [0xfc0000000000000000,0xfc300])),(BitVec.ofNat 152 (word80 [0x3000c003000c00300,0xc003000c003000f4300]))),(0x0,0x0)]
def g255C : List ColumnInfo := [(1,0,254,0,13),(4,0,251,0,13),(8,0,247,0,13),(16,0,239,0,13),(32,0,223,0,13),(64,0,191,0,13),(2,0,253,0,12),(128,0,127,0,12),(2,8,213,32,11),(2,32,213,8,11)]
def g255A : List (List Nat) := [[],[100],[83],[83,100],[66],[66,98],[66,83],[66,83,98],[98,66],[98],[98,83,66],[98,83],[32],[32,100],[32,83],[32,83,100],[32,64],[32,64,96],[32,64,83],[32,64,83,96],[32,96,64],[32,96],[32,96,83,64],[32,96,83],[64,32],[64,32,98],[64,32,83],[64,32,83,98],[64],[64,96],[64,83],[64,83,96],[64,98],[64,98,32],[64,98,83],[64,98,83,32],[96,32,66],[96,32],[96,32,83,66],[96,32,83],[96,64],[96],[96,83,64],[96,83],[96,66,32],[96,66],[96,66,83,32],[96,66,83]]
def g255D13 (j : Nat) := if j=0 then 0x127942349d504ffd71 else 0
def g255D14 (j : Nat) := if j=0 then 0x1d89004d48ff else 0
def g255H14 (j : Nat) := if j=0 then 0x90 else 0
def g255L : Nat → Packing
  | 13 => (1,1,4,0,0,0,0,g255D13)
  | 14 => (1,0,4,0,0,0,0,g255D14)
  | _ => emptyPacking
def g255I : Nat → Nat → Option (Nat × Nat)
  | 14 => lookupWord 1 2 0 4 0 0 g255H14
  | _ => fun _ => none
def g255 : Forest := ⟨255,14,fun i => g255Y[i]?.getD (0,0),g255C,g255A,g255L,g255I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P13_0 : block g255 13 0 1=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B13 : block g255 13 0 1=true := g255P13_0
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
  · exact (rfl : block g255 7 0 0 = true)
  · exact (rfl : block g255 8 0 0 = true)
  · exact (rfl : block g255 9 0 0 = true)
  · exact (rfl : block g255 10 0 0 = true)
  · exact (rfl : block g255 11 0 0 = true)
  · exact (rfl : block g255 12 0 0 = true)
  · exact g255B13
  · exact g255B14
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255G : graphValid g255 (boundsBefore K253) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255R : Impossible true graph 14 sevenInputs.toFinset := by
  rw [show graph = targetOf g255 by decide +kernel]
  exact root_index (g:=g255) (top:=14) (i:=0) (before_sound K253 V253) g255G g255T (by decide) (by decide +kernel)

end PEqualNP.Outside.L_meta_34732

open PEqualNP.Outside.L_meta_34732 in
theorem PEqualNP.Outside.L_meta_34732 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 2, 4, 1, 5, 3, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 1, 5, 3, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 1, 5, 3, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 2, 4, 1, 5, 3, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 1, 5, 3, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 1, 5, 3, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o fit _ correct
  exact replaceShort g255R gates o fit correct

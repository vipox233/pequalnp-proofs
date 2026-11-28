import PEqualNP.Defs

-- The two-mode live-state and cofactor checker follows L_meta_1674 and L_meta_670.
-- The graph, restrictions and all search certificates below are for L_meta_32321.

-- Shared forest and cofactor certificates from L_meta_1674 and PR 11111 for L_meta_1677.
-- The original credit line is retained below. The two root certificates here cover the unpinned graph.

-- The checker and the bound certificates are adapted from PEqualNP/Outside/L_meta_1667.lean (Apache-2.0).
-- Two modes: u=false are monotone runs (AND, OR); u=true are runs up to complement, where negation is free.
namespace PEqualNP.Outside.L_meta_32321
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
def graph : Sig := (BitVec.ofNat 512 (word80 [0xffffffff,0xfffffffffffffffffffe,0xfffefffffffefffffffc,0xfefefafaeeccaa00ffff,0xffffffffffffffffffff,0xfffefffefffffffeffff,0xfffcfefefafaeeccaa00]))
def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 3) || (x 1 && x 4) || (x 0 && x 5) || (x 2 && x 5) || (x 1 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 4 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 2 && x 7) || (x 3 && x 7) || (x 5 && x 7) || (x 6 && x 7)
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
  (x 0 &&& x 3) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 2 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 2 &&& x 7) ||| (x 3 &&& x 7) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)
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
  (x 0 &&& x 3) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 2 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 2 &&& x 7) ||| (x 3 &&& x 7) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)
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



def target (x : Fin 8 → Bool) : Bool := decide (∃ i < ([0, 3, 1, 4, 0, 5, 2, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
def smallCircuit : Circuit := ⟨[⟨.or,[0,2]⟩,⟨.or,[1,2]⟩,⟨.or,[3,9]⟩,⟨.or,[3,5]⟩,⟨.or,[1,6]⟩,⟨.or,[0,7]⟩,⟨.or,[4,7]⟩,⟨.or,[5,7]⟩,⟨.and,[14,12]⟩,⟨.and,[13,11]⟩,⟨.and,[15,8]⟩,⟨.and,[6,10]⟩,⟨.or,[16,17]⟩,⟨.or,[20,18]⟩,⟨.or,[21,19]⟩], 22⟩

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

def lowRow (i : Fin 8) : Row := Fin.ofNat 512 (1 <<< ([3, 4, 5, 0, 1, 0, 1, 0] : List Nat).getD i.val 0)
def highRow (i : Fin 8) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< ([3, 4, 5, 0, 1, 0, 1, 0] : List Nat).getD i.val 0))

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
def g82Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0x3ff63ff63ff63ff63f,0xf63ff63ff63ff63ff63f])),(BitVec.ofNat 152 (word80 [0x492049204920492049,0x20492049204920492049]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xc7fbc7fbc7fbc7fbc7,0xfbc7fbc7fbc7fbc7fbc7])),(BitVec.ofNat 152 (word80 [0x924092409240924092,0x40924092409240924092]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xf8fdf8fdf8fdf8fdf8,0xfdf8fdf8fdf8fdf8fdf8])),(BitVec.ofNat 152 (word80 [0x248124812481248124,0x81248124812481248124]))),(0x0,0x0),(0x0,0x0)]
def g82C : List ColumnInfo := []
def g82A : List (List Nat) := [[],[100],[65],[65,97],[97,65],[97]]
def g82D3 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7
def g82L : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,g82D3)
  | _ => emptyPacking
def g82I (_ _ : Nat) : Option (Nat × Nat) := none
def g82 : Forest := ⟨82,3,fun i => g82Y[i]?.getD (0,0),g82C,g82A,g82L,g82I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g82P3_0 : block g82 3 0 1=true := by
  apply cellsBlock (ar:=3) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g82B3 : block g82 3 0 1=true := g82P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g82T : checkedTables g82 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g82 0 0 0 = true)
  · exact (rfl : block g82 1 0 0 = true)
  · exact (rfl : block g82 2 0 0 = true)
  · exact g82B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g82G : graphValid g82 (boundsBefore []) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low82 : Lower true (varsX 82) (graphGoal 82) 4 := lower_forest (g:=g82) (i:=0) (hints:=16842816) (before_sound [] baseKnown) g82G g82T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K82 := extendKnown [] 4 [(82,[]),(137,[16,67,118]),(161,[16,84,118]),(164,[33,84,118]),(194,[100,84,117]),(196,[33,100,84,117]),(200,[49,33,100,84,117])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V82 : Known true K82 := extend_ok (m:=82) baseKnown low82 (by decide +kernel)
def g45Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xe6de3fff03fff1ffe6,0xde3fff03fff1ffe6de3f])),(BitVec.ofNat 152 (word80 [0x648490a2850240206,0x48490a28502402064849]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x19e9c0fffc07fe3f19,0xe9c0fffc07fe3f19e9c0])),(BitVec.ofNat 152 (word80 [0x50e8db2c3161408450,0xe8db2c3161408450e8db]))),((BitVec.ofNat 152 (word80 [0xece607fffff8003fec,0xe607fffff8003fece607])),(BitVec.ofNat 152 (word80 [0x8a7b6b04185892808,0xa7b6b04185892808a7b6]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1b3df8ffffffffc01b,0x3df8ffffffffc01b3df8])),(BitVec.ofNat 152 (word80 [0x891524c08206003089,0x1524c082060030891524]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g45C : List ColumnInfo := []
def g45A : List (List Nat) := [[],[80,50]]
def g45D3 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xf
def g45L : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,g45D3)
  | _ => emptyPacking
def g45I (_ _ : Nat) : Option (Nat × Nat) := none
def g45 : Forest := ⟨45,3,fun i => g45Y[i]?.getD (0,0),g45C,g45A,g45L,g45I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g45P3_0 : block g45 3 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g45B3 : block g45 3 0 1=true := g45P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g45T : checkedTables g45 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g45 0 0 0 = true)
  · exact (rfl : block g45 1 0 0 = true)
  · exact (rfl : block g45 2 0 0 = true)
  · exact g45B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g45G : graphValid g45 (boundsBefore K82) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low45 : Lower true (varsX 45) (graphGoal 45) 4 := lower_forest (g:=g45) (i:=0) (hints:=1283) (before_sound K82 V82) g45G g45T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K45 := extendKnown K82 4 [(45,[]),(75,[96,33,16,49,83]),(77,[96,32,50,83]),(89,[96,32,67,50,83]),(101,[32,99,67]),(102,[32,16,83,67,100]),(105,[48,82,96,66,64]),(108,[32,16,49,81,65,100]),(147,[16,32,67,117,101]),(150,[16,67,117,101]),(209,[96,32,67,50,117])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V45 : Known true K45 := extend_ok (m:=45) V82 low45 (by decide +kernel)
def g86Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfdf00fff81fc7e3ffb,0xe01fff03f8fc7ff7c03f])),(BitVec.ofNat 152 (word80 [0x45c09245142904808b,0x81248a28520901170249]))),((BitVec.ofNat 152 (word80 [0xe6a8703ffe007fc7cd,0x50e07ffc00ff8f9aa1c0])),(BitVec.ofNat 152 (word80 [0x96a9b6d618b228112d,0x536dac316450225aa6db]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfbb781ffffff8007f7,0x6f03ffffff000feede07])),(BitVec.ofNat 152 (word80 [0x235249820c0312204,0x6a49304180624408d492]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x64ffe3ffffffff80c,0x9ffc7ffffffff0193ff8])),(BitVec.ofNat 152 (word80 [0x249204100400400,0x4924082008008000924]))),(0x0,0x0),(0x0,0x0)]
def g86C : List ColumnInfo := [(4,0,82,0,4)]
def g86A : List (List Nat) := [[],[65]]
def g86D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1f
def g86L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g86D4)
  | _ => emptyPacking
def g86I (_ _ : Nat) : Option (Nat × Nat) := none
def g86 : Forest := ⟨86,4,fun i => g86Y[i]?.getD (0,0),g86C,g86A,g86L,g86I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g86P4_0 : block g86 4 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g86B4 : block g86 4 0 1=true := g86P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g86T : checkedTables g86 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g86 0 0 0 = true)
  · exact (rfl : block g86 1 0 0 = true)
  · exact (rfl : block g86 2 0 0 = true)
  · exact (rfl : block g86 3 0 0 = true)
  · exact g86B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g86G : graphValid g86 (boundsBefore K45) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low86 : Lower true (varsX 86) (graphGoal 86) 5 := lower_forest (g:=g86) (i:=0) (hints:=16844352) (before_sound K45 V45) g86G g86T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K86 := extendKnown K45 5 [(86,[]),(90,[50]),(139,[32,16,67,118]),(141,[16,67,118]),(163,[32,16,84,118]),(166,[33,84,118]),(172,[33,49,84,118]),(195,[32,100,84,117]),(197,[16,32,100,84,117]),(212,[33,65,49,115,83]),(216,[49,66,114,82]),(225,[16,98,50,84,67,116]),(226,[82,50,100,116]),(232,[49,82,100,116])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V86 : Known true K86 := extend_ok (m:=86) V45 low86 (by decide +kernel)
def g165Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfe7d01c7fc0fc7cfe7,0xd01c7fc0fc7cfe7d01c7])),(BitVec.ofNat 152 (word80 [0x51d124928a290a051,0xd124928a290a051d1249]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x3f8b8e38fff007f3f8,0xb8e38fff007f3f8b8e38])),(BitVec.ofNat 152 (word80 [0x884b924930c3210884,0xb924930c3210884b9249]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x3fe7703ffffff803fe,0x7703ffffff803fe7703f])),(BitVec.ofNat 152 (word80 [0x100024924104020100,0x2492410402010002492]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xc018ffc0fffffffc01,0x8ffc0fffffffc018ffc0])),(BitVec.ofNat 152 (word80 [0x200049248208040200,0x4924820804020004924]))),(0x0,0x0)]
def g165C : List ColumnInfo := [(1,0,164,0,4)]
def g165A : List (List Nat) := [[],[117],[32],[32,117]]
def g165D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1f
def g165L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g165D4)
  | _ => emptyPacking
def g165I (_ _ : Nat) : Option (Nat × Nat) := none
def g165 : Forest := ⟨165,4,fun i => g165Y[i]?.getD (0,0),g165C,g165A,g165L,g165I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g165P4_0 : block g165 4 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g165B4 : block g165 4 0 1=true := g165P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g165T : checkedTables g165 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g165 0 0 0 = true)
  · exact (rfl : block g165 1 0 0 = true)
  · exact (rfl : block g165 2 0 0 = true)
  · exact (rfl : block g165 3 0 0 = true)
  · exact g165B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g165G : graphValid g165 (boundsBefore K86) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low165 : Lower true (varsX 165) (graphGoal 165) 5 := lower_forest (g:=g165) (i:=0) (hints:=1285) (before_sound K86 V86) g165G g165T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K165 := extendKnown K86 5 [(165,[]),(169,[48,82,32]),(198,[16,101]),(201,[98,50,83]),(202,[16,50,101]),(204,[32,16,49,101]),(210,[64,16,114,50,49,81,101]),(228,[80,16,98,49,67,66])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V165 : Known true K165 := extend_ok (m:=165) V86 low165 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low55 : Lower true (varsX 55) (graphGoal 55) 4 := by
  have q := @lower_count true (vars 55) (graphGoal 55) (proper_of _ (by decide +kernel)) (graphPairs 55 66885) (by decide +kernel)
  exact q
def K55 := extendKnown K165 4 [(59,[48,82,32])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V55 : Known true K55 := extend_ok (m:=55) V165 low55 (by decide +kernel)
def g79Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x1fff0007ff803ffc01,0xfffffffffff245f3f007])),(BitVec.ofNat 152 (word80 [0x502a8350250681482d,0x550950a414040f37b6d]))),((BitVec.ofNat 152 (word80 [0x1ffffff800003fffff,0xffe001ffe001b15bc038])),(BitVec.ofNat 152 (word80 [0x854c2a62b62b159148,0x2986d84c8661a159c6db]))),((BitVec.ofNat 152 (word80 [0x1fffffffffffc00001,0xfffffe00000ce425d1c0])),(BitVec.ofNat 152 (word80 [0x6703383384c19e270,0x4e04e06f0b88a425d6db]))),((BitVec.ofNat 152 (word80 [0xe00000000000000001,0xfffffffffff22fedae07])),(BitVec.ofNat 152 (word80 [0x7803c03c0701e0380,0x700700700c022d0c8492]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffffffffffffe,0xdfa9e5ff8])),(BitVec.ofNat 152 (word80 [0x1800c0040000200001,0x80180180100452820924]))),(0x0,0x0),(0x0,0x0)]
def g79C : List ColumnInfo := [(2,0,77,0,4)]
def g79A : List (List Nat) := [[],[33]]
def g79D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3f
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
def K79 := extendKnown K55 5 [(124,[80,49,66,33,16]),(151,[64,16,49,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V79 : Known true K79 := extend_ok (m:=79) V55 low79 (by decide +kernel)
def g91Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffc00ffc3fe1ffc01f,0xfff87ffcd452be00001f])),(BitVec.ofNat 152 (word80 [0x22a4a228884522a950,0xa81148805012bf5ad6b5]))),((BitVec.ofNat 152 (word80 [0xfffff0003fffffffe0,0xfffffc31359e2007fe0])),(BitVec.ofNat 152 (word80 [0xb00c0b102800b0182,0xc0a0010a025922318c63]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffc001ffffff,0xf0007ffcefd1140f801f])),(BitVec.ofNat 152 (word80 [0x4c0904c013084c0203,0x2c21200af4100a5294a]))),((BitVec.ofNat 152 (word80 [0x1ffffff,0xffff80004d2fe9f003e0])),(BitVec.ofNat 152 (word80 [0x700e07021c10700c04,0x3001c104d06c0c6318c]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffffffe000000,0x33aa61bfffc00])),(BitVec.ofNat 152 (word80 [0x803008002001803018,0xc04602110a019084210]))),(0x0,0x0),(0x0,0x0)]
def g91C : List ColumnInfo := [(0,1,82,8,5),(1,0,90,0,5),(2,0,89,0,4),(8,1,82,0,4),(16,0,75,0,4)]
def g91A : List (List Nat) := [[],[65]]
def g91D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x57d4d41
def g91D5 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x2012,0x240d140ff41fd41fd31])
def g91H5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xc0
def g91D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x18989f
def g91H6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x2051600028b5
def g91L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g91D4)
  | 5 => (3,1,3,0,0,5,0,g91D5)
  | 6 => (1,0,3,0,0,0,0,g91D6)
  | _ => emptyPacking
def g91I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 4 0 0 g91H5
  | 6 => lookupWord 1 11 0 7 2 1 g91H6
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
theorem g91P5_0 : block g91 5 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g91B5 : block g91 5 0 3=true := g91P5_0
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
theorem g91G : graphValid g91 (boundsBefore K79) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low91 : Lower true (varsX 91) (graphGoal 91) 7 := lower_forest (g:=g91) (i:=0) (hints:=16842819) (before_sound K79 V79) g91G g91T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K91 := extendKnown K79 7 [(91,[]),(118,[80,32,50]),(155,[64,16,49,118]),(179,[64,16,49,83,118]),(182,[64,33,16,49,83,118]),(241,[64,16,33,99,82,115])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V91 : Known true K91 := extend_ok (m:=91) V79 low91 (by decide +kernel)
def g94Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0x3ffc003ffc01ffe00f,0xfffffffffffeddea003f])),(BitVec.ofNat 152 (word80 [0x80a81a8128340a4160,0xa02a094148524c6a1249]))),((BitVec.ofNat 152 (word80 [0x3fffffc00001fffff0,0x7ff001ffc0118f681c0])),(BitVec.ofNat 152 (word80 [0x15315315b158ac8a45,0x314c6d89919918f6b6db]))),((BitVec.ofNat 152 (word80 [0x3ffffffffffe000000,0x7ffffe000031f070e00])),(BitVec.ofNat 152 (word80 [0x19c19c19c260cf1389,0xc2704e0de2e31f0736db]))),((BitVec.ofNat 152 (word80 [0xc00000000000000000,0x7fffffffffcbfdc7007])),(BitVec.ofNat 152 (word80 [0x1e01e01e0380f01c0e,0x380700e0300b3942492]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffffffff,0xf800000000036237fff8])),(BitVec.ofNat 152 (word80 [0x200200200001000000,0x4008010000000004924]))),(0x0,0x0),(0x0,0x0)]
def g94C : List ColumnInfo := [(4,0,90,0,5)]
def g94A : List (List Nat) := [[],[50],[65],[65,50]]
def g94D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3f
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
theorem g94G : graphValid g94 (boundsBefore K91) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low94 : Lower true (varsX 94) (graphGoal 94) 6 := lower_forest (g:=g94) (i:=0) (hints:=16868928) (before_sound K91 V91) g94G g94T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K94 := extendKnown K91 6 [(94,[]),(143,[64,16,33,50,118]),(174,[33,84,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V94 : Known true K94 := extend_ok (m:=94) V91 low94 (by decide +kernel)
def g103Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xe001ffc07ff01ffe00,0x3ffc07ffffd37a12000f])),(BitVec.ofNat 152 (word80 [0x48d4128d0522c8549a,0x9128d25229934a125555]))),((BitVec.ofNat 152 (word80 [0xfffe00007fffffffff,0xc00007ff01a3a9cc0f00])),(BitVec.ofNat 152 (word80 [0x82985b161644829813,0x5b160644d2329c83333]))),((BitVec.ofNat 152 (word80 [0xffffffff80001fffff,0xfffff800003f4479f0f0])),(BitVec.ofNat 152 (word80 [0xe01c18078700e01c,0x1c18078701304591111]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1fffff,0xfffffffffe663f7600ff])),(BitVec.ofNat 152 (word80 [0x130160205808130120,0x2600048000643124aaaa]))),((BitVec.ofNat 152 (word80 [0xffffffffffffe00000,0x19dd38dff00])),(BitVec.ofNat 152 (word80 [0x1c01800060001c01c0,0x38020700808cd204cccc]))),(0x0,0x0),(0x0,0x0)]
def g103C : List ColumnInfo := []
def g103A : List (List Nat) := [[],[16,101]]
def g103D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1f
def g103L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g103D4)
  | _ => emptyPacking
def g103I (_ _ : Nat) : Option (Nat × Nat) := none
def g103 : Forest := ⟨103,4,fun i => g103Y[i]?.getD (0,0),g103C,g103A,g103L,g103I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g103P4_0 : block g103 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g103B4 : block g103 4 0 1=true := g103P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g103T : checkedTables g103 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g103 0 0 0 = true)
  · exact (rfl : block g103 1 0 0 = true)
  · exact (rfl : block g103 2 0 0 = true)
  · exact (rfl : block g103 3 0 0 = true)
  · exact g103B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g103G : graphValid g103 (boundsBefore K94) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low103 : Lower true (varsX 103) (graphGoal 103) 5 := lower_forest (g:=g103) (i:=0) (hints:=16778597) (before_sound K94 V94) g103G g103T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K103 := extendKnown K94 5 [(103,[]),(117,[65,49]),(121,[64,81,50,33,32,96])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V103 : Known true K103 := extend_ok (m:=103) V94 low103 (by decide +kernel)
def g109Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xf003ff0ff87ff007ff,0xff87fffcd47c560003ff])),(BitVec.ofNat 152 (word80 [0xa4280a201120a45214,0x81102080501c1694a529]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffc000ffffffff801,0xfff87fc35353a20ffc00])),(BitVec.ofNat 152 (word80 [0xc0302c40a002c06058,0xa01010a425122318c63]))),((BitVec.ofNat 152 (word80 [0xfffffff0007ffffffe,0x7ffcafd11df0001f])),(BitVec.ofNat 152 (word80 [0x140b002c20b008060,0x2c220a00a741086318c6]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x7fffffff,0xffff80004d2fe8007fe0])),(BitVec.ofNat 152 (word80 [0x982c08b044c090481,0x30004c100d22c94a5294]))),((BitVec.ofNat 152 (word80 [0xffffffffff80000000,0x33aa61bff8000])),(BitVec.ofNat 152 (word80 [0xe03000c00700e0701,0xc044702118a6118c6318]))),(0x0,0x0),(0x0,0x0)]
def g109C : List ColumnInfo := [(1,0,108,0,4),(4,0,105,0,4),(8,0,101,0,4),(32,0,77,0,4),(64,0,45,0,4)]
def g109A : List (List Nat) := [[],[98,83],[32,99],[32,48,80,96],[48,101],[48,82,96,32],[80,50],[80,98,48,50],[96,32,50,83],[96,82]]
def g109D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x57d4d10
def g109D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xc1a0fd20fd10
def g109H5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x8
def g109D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x23440bf
def g109H6 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x25,0xfe009300000052003100,0x2000,0x26000000bb9700,0,0x6a0000000000000000])
def g109L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g109D4)
  | 5 => (2,1,3,0,0,4,0,g109D5)
  | 6 => (1,0,3,0,0,0,0,g109D6)
  | _ => emptyPacking
def g109I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 4 0 0 g109H5
  | 6 => lookupWord 2 53 0 8 1 3 g109H6
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
theorem g109P5_0 : block g109 5 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g109B5 : block g109 5 0 2=true := g109P5_0
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
theorem g109G : graphValid g109 (boundsBefore K103) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low109 : Lower true (varsX 109) (graphGoal 109) 7 := lower_forest (g:=g109) (i:=0) (hints:=33555715) (before_sound K103 V103) g109G g109T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K109 := extendKnown K103 7 [(109,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V109 : Known true K109 := extend_ok (m:=109) V103 low109 (by decide +kernel)
def g115Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xc003ff0ffc3ffc00ff,0xffffffc02b3e79000fc0])),(BitVec.ofNat 152 (word80 [0x90a80a204890a92a42,0x91204088292e194d34d3]))),((BitVec.ofNat 152 (word80 [0xfffc000fffffffff00,0x3ff0fffec8a9d703f03f])),(BitVec.ofNat 152 (word80 [0x2304c411002300c13,0x4209020009d3145145]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffff0003fffffff,0xc000fffd77e88afc003f])),(BitVec.ofNat 152 (word80 [0x4c090026104c03004,0x584120172a00828a28a]))),((BitVec.ofNat 152 (word80 [0x3fffffff,0xffff00012697f4000fc0])),(BitVec.ofNat 152 (word80 [0x2702e08b8227024098,0x26009c110691e4b2cb2c]))),((BitVec.ofNat 152 (word80 [0xffffffffffc0000000,0x39d530dfff000])),(BitVec.ofNat 152 (word80 [0x3803000c00380380e0,0x3808e0208d5204c30c30]))),(0x0,0x0),(0x0,0x0)]
def g115C : List ColumnInfo := [(0,1,82,32,5)]
def g115A : List (List Nat) := [[],[100],[65],[65,97],[97,65],[97],[80],[80,100],[80,65],[80,65,97],[80,97,65],[80,97]]
def g115D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3f
def g115L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g115D5)
  | _ => emptyPacking
def g115I (_ _ : Nat) : Option (Nat × Nat) := none
def g115 : Forest := ⟨115,5,fun i => g115Y[i]?.getD (0,0),g115C,g115A,g115L,g115I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g115P5_0 : block g115 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g115B5 : block g115 5 0 1=true := g115P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g115T : checkedTables g115 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g115 0 0 0 = true)
  · exact (rfl : block g115 1 0 0 = true)
  · exact (rfl : block g115 2 0 0 = true)
  · exact (rfl : block g115 3 0 0 = true)
  · exact (rfl : block g115 4 0 0 = true)
  · exact g115B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g115G : graphValid g115 (boundsBefore K109) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low115 : Lower true (varsX 115) (graphGoal 115) 6 := lower_forest (g:=g115) (i:=0) (hints:=16842821) (before_sound K109 V109) g115G g115T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K115 := extendKnown K109 6 [(115,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V115 : Known true K115 := extend_ok (m:=115) V109 low115 (by decide +kernel)
def g167Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffc00ffc07fe03fff,0xe00ffc0ffff447d401c7])),(BitVec.ofNat 152 (word80 [0xa0a86a128d0a458a05,0x46a129a2929043d49249]))),((BitVec.ofNat 152 (word80 [0xfffff00007fffc07f,0xfff0000ff81386ac0e00])),(BitVec.ofNat 152 (word80 [0xc5314c5b162c891329,0x84c5b2c324d386adb6db]))),((BitVec.ofNat 152 (word80 [0xfffffffff8000007f,0xfffffff0000be8947038])),(BitVec.ofNat 152 (word80 [0x1c0701c180f0e1c0e,0x701c303c709e0949249]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xf0000000000000007f,0xffffffffffe6fe67803f])),(BitVec.ofNat 152 (word80 [0x60180602030102030,0x806000400061c212492]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffffff80,0x1911bbffc0])),(BitVec.ofNat 152 (word80 [0x80200800040000040,0x10080008000000024924]))),(0x0,0x0)]
def g167C : List ColumnInfo := [(1,0,166,0,5)]
def g167A : List (List Nat) := [[],[32]]
def g167D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3f
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
theorem g167G : graphValid g167 (boundsBefore K115) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low167 : Lower true (varsX 167) (graphGoal 167) 6 := lower_forest (g:=g167) (i:=0) (hints:=1397) (before_sound K115 V115) g167G g167T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K167 := extendKnown K115 6 [(167,[]),(171,[48,82,32]),(199,[16,101])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V167 : Known true K167 := extend_ok (m:=167) V115 low167 (by decide +kernel)
def g173Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfe1ff00ff87f87ffc0,0x7fff8fffd8b95000f0ff])),(BitVec.ofNat 152 (word80 [0x1440a0a05101100285,0x5012008488941111111]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1ffff0007ff87fff,0x807ff1fc2b1e600f0f00])),(BitVec.ofNat 152 (word80 [0x5882c0c1620a010b06,0x160a0411291e43333333]))),((BitVec.ofNat 152 (word80 [0x1fffffff80007fff,0xff8001ff941fb0f0000f])),(BitVec.ofNat 152 (word80 [0x610b0505802c222c08,0x182c48a01416b6666666]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffe000000000007fff,0xfffffe000be4bf000ff0])),(BitVec.ofNat 152 (word80 [0x800c06060430443010,0x203000c20260b4444444]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffff8000,0x6442cffff000])),(BitVec.ofNat 152 (word80 [0x1008080040004020,0x40400100000008888888]))),(0x0,0x0)]
def g173C : List ColumnInfo := [(1,0,172,0,5),(4,0,169,0,5),(8,0,165,0,5),(32,0,141,0,5)]
def g173A : List (List Nat) := [[],[80,50]]
def g173D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x4e09f
def g173L : Nat → Packing
  | 6 => (1,0,2,0,0,0,0,g173D6)
  | _ => emptyPacking
def g173I (_ _ : Nat) : Option (Nat × Nat) := none
def g173 : Forest := ⟨173,6,fun i => g173Y[i]?.getD (0,0),g173C,g173A,g173L,g173I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g173P6_0 : block g173 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g173B6 : block g173 6 0 1=true := g173P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g173T : checkedTables g173 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g173 0 0 0 = true)
  · exact (rfl : block g173 1 0 0 = true)
  · exact (rfl : block g173 2 0 0 = true)
  · exact (rfl : block g173 3 0 0 = true)
  · exact (rfl : block g173 4 0 0 = true)
  · exact (rfl : block g173 5 0 0 = true)
  · exact g173B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g173G : graphValid g173 (boundsBefore K167) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low173 : Lower true (varsX 173) (graphGoal 173) 7 := lower_forest (g:=g173) (i:=0) (hints:=1283) (before_sound K167 V167) g173G g173T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K173 := extendKnown K167 7 [(173,[]),(203,[96,33,16,49,83]),(205,[96,32,50,83]),(214,[16,67,117,101]),(218,[16,50,66,117,101]),(229,[32,99,67]),(230,[32,16,83,67,100]),(233,[48,82,96,66,64]),(236,[32,16,49,81,65,100])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V173 : Known true K173 := extend_ok (m:=173) V167 low173 (by decide +kernel)
def g211Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffc01ffff0fffc00f,0xf0ff0ff0c8957c00f000])),(BitVec.ofNat 152 (word80 [0x22a9549452202a8aa0,0xa212222288157c777777]))),((BitVec.ofNat 152 (word80 [0xffffe01fff0fffff0,0xffffff2c761b0f00ff])),(BitVec.ofNat 152 (word80 [0x4030181804020300c0,0xc4040040080613111111]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffe0000ffffff,0xff000fff33b526000f0f])),(BitVec.ofNat 152 (word80 [0x88c0602118448c2309,0x98488032b104aaaaaa]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xf00000000000ffffff,0xfffff000134bf8f00ff0])),(BitVec.ofNat 152 (word80 [0x30180c06088300c02,0x200304014868444444]))),((BitVec.ofNat 152 (word80 [0xffffffffffff000000,0xcea8c5fff000])),(BitVec.ofNat 152 (word80 [0xc0201018000c0300c,0x8c08c0846a080888888]))),(0x0,0x0)]
def g211C : List ColumnInfo := [(0,1,82,128,5),(1,0,210,0,5),(16,0,195,0,5),(2,0,209,0,4),(64,0,147,0,4),(128,1,82,0,4)]
def g211A : List (List Nat) := [[],[97]]
def g211D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x5bd4931
def g211D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xc8404fd31
def g211H5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x50
def g211D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x232a8bf
def g211H6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0
def g211L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g211D4)
  | 5 => (1,1,3,0,0,0,0,g211D5)
  | 6 => (1,0,3,0,0,0,0,g211D6)
  | _ => emptyPacking
def g211I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 4 0 0 g211H5
  | 6 => lookupWord 1 2 0 4 0 0 g211H6
  | _ => fun _ => none
def g211 : Forest := ⟨211,6,fun i => g211Y[i]?.getD (0,0),g211C,g211A,g211L,g211I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g211P4_0 : block g211 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g211B4 : block g211 4 0 1=true := g211P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g211P5_0 : block g211 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g211B5 : block g211 5 0 1=true := g211P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g211P6_0 : block g211 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g211B6 : block g211 6 0 1=true := g211P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g211T : checkedTables g211 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g211 0 0 0 = true)
  · exact (rfl : block g211 1 0 0 = true)
  · exact (rfl : block g211 2 0 0 = true)
  · exact (rfl : block g211 3 0 0 = true)
  · exact g211B4
  · exact g211B5
  · exact g211B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g211G : graphValid g211 (boundsBefore K173) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low211 : Lower true (varsX 211) (graphGoal 211) 7 := lower_forest (g:=g211) (i:=0) (hints:=16842823) (before_sound K173 V173) g211G g211T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K211 := extendKnown K173 7 [(211,[]),(217,[64,49,33,118]),(242,[80,32,50]),(244,[64,33,16,49,83,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V211 : Known true K211 := extend_ok (m:=211) V173 low211 (by decide +kernel)
def g213Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x7ff003ffffe03ffff0,0x1ff80ffc0069abc81c0])),(BitVec.ofNat 152 (word80 [0x12a5a94a2a458a12a2,0xd4251a148b029aacb6db]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x7ffffc00ffffc07fff,0xfe0000fffff8da038e07])),(BitVec.ofNat 152 (word80 [0x4c1306c0c891304c0,0x98362c19124892039249]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x7fffffff0000007fff,0xffffff00000ff10e0038])),(BitVec.ofNat 152 (word80 [0x4701c0708f0e1c4708,0xe138309e1c0fd10a5b6d]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x800000000000007fff,0xffffffffff99af6d703f])),(BitVec.ofNat 152 (word80 [0x180601803010201803,0x40002000102c242492]))),((BitVec.ofNat 152 (word80 [0xffffffffffffff8000,0x6754f2ffc0])),(BitVec.ofNat 152 (word80 [0x60080200c00000600c,0x18040c0202540504924]))),(0x0,0x0)]
def g213C : List ColumnInfo := [(1,0,212,0,5)]
def g213A : List (List Nat) := [[],[64,118]]
def g213D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3f
def g213L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g213D5)
  | _ => emptyPacking
def g213I (_ _ : Nat) : Option (Nat × Nat) := none
def g213 : Forest := ⟨213,5,fun i => g213Y[i]?.getD (0,0),g213C,g213A,g213L,g213I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g213P5_0 : block g213 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g213B5 : block g213 5 0 1=true := g213P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g213T : checkedTables g213 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g213 0 0 0 = true)
  · exact (rfl : block g213 1 0 0 = true)
  · exact (rfl : block g213 2 0 0 = true)
  · exact (rfl : block g213 3 0 0 = true)
  · exact (rfl : block g213 4 0 0 = true)
  · exact g213B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g213G : graphValid g213 (boundsBefore K211) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low213 : Lower true (varsX 213) (graphGoal 213) 6 := lower_forest (g:=g213) (i:=0) (hints:=33949191) (before_sound K211 V211) g213G g213T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K213 := extendKnown K211 6 [(213,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V213 : Known true K213 := extend_ok (m:=213) V211 low213 (by decide +kernel)
def g227Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffc01ff87fc3fff00,0xffff1ffed2e680007c1f])),(BitVec.ofNat 152 (word80 [0x222894451108808a4a,0xa02444252268a5294a5]))),((BitVec.ofNat 152 (word80 [0xffffe0007ffc3ffff,0xffffe11773400f83e0])),(BitVec.ofNat 152 (word80 [0x40b018162050082c0c,0x2c140089146346318c63]))),(0x0,0x0),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffff80003ffff,0xff001ffce8f541f0001f])),(BitVec.ofNat 152 (word80 [0x84c120980261113010,0x30588900a8d154a5294a]))),((BitVec.ofNat 152 (word80 [0xf0000000000003ffff,0xffffe0005f98fe0003e0])),(BitVec.ofNat 152 (word80 [0x701c0e0438221c060,0x40600e104b9898c6318c]))),((BitVec.ofNat 152 (word80 [0xfffffffffffffc0000,0x3280bbffffc00])),(BitVec.ofNat 152 (word80 [0x80201000400020080,0x80801000000021084210]))),(0x0,0x0)]
def g227C : List ColumnInfo := [(1,0,226,0,5),(2,0,225,0,5),(32,0,195,0,5),(64,0,163,0,5),(33,0,194,0,4),(66,0,161,0,4)]
def g227A : List (List Nat) := [[],[97],[16,101],[16,80,96],[80],[80,97],[96,16,81],[96,81]]
def g227D4 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x31825f635474,0x9bd89544426d6215110])
def g227D5 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0xc110204810001,0x882188201141080d176b,0xcc8d018160c02faa3a07,0xbd4940bfa8a81fb40502,0xfea8885f95110beaa221,0x7c54443f280885bd4940])
def g227H5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x28110000000000229910
def g227D6 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x3140cc503,0x540a0380ff40fd40fd10])
def g227H6 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0xd4f4400e18d31,0x640021400003c7f1000c,0x2000000000034200143f,0x400a0000585c9002571])
def g227D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1605f
def g227H7 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0xc4005e51,0x200000000000e1030740,0x3c4012a00003a4000,0x10254000020000005])
def g227L : Nat → Packing
  | 4 => (3,3,3,0,0,4,0,g227D4)
  | 5 => (10,2,3,0,0,7,0,g227D5)
  | 6 => (3,1,3,0,0,6,0,g227D6)
  | 7 => (1,0,3,0,0,0,0,g227D7)
  | _ => emptyPacking
def g227I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 11 0 8 2 2 g227H5
  | 6 => lookupWord 4 29 1 10 4 2 g227H6
  | 7 => lookupWord 3 31 1 9 2 3 g227H7
  | _ => fun _ => none
def g227 : Forest := ⟨227,7,fun i => g227Y[i]?.getD (0,0),g227C,g227A,g227L,g227I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g227P4_0 : block g227 4 0 3=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g227B4 : block g227 4 0 3=true := g227P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g227P5_0 : block g227 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g227P5_1 : block g227 5 1 9=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g227B5 : block g227 5 0 10=true := (@block_merge g227 5 0 1 9 g227P5_0 g227P5_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g227P6_0 : block g227 6 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g227B6 : block g227 6 0 3=true := g227P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g227P7_0 : block g227 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g227B7 : block g227 7 0 1=true := g227P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g227T : checkedTables g227 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g227 0 0 0 = true)
  · exact (rfl : block g227 1 0 0 = true)
  · exact (rfl : block g227 2 0 0 = true)
  · exact (rfl : block g227 3 0 0 = true)
  · exact g227B4
  · exact g227B5
  · exact g227B6
  · exact g227B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g227G : graphValid g227 (boundsBefore K213) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low227 : Lower true (varsX 227) (graphGoal 227) 8 := lower_forest (g:=g227) (i:=0) (hints:=16777317) (before_sound K213 V213) g227G g227T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K227 := extendKnown K213 8 [(227,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V227 : Known true K227 := extend_ok (m:=227) V213 low227 (by decide +kernel)
def g63Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffffffffffffffffff,0xfb944e4fa4fd6803f03f])),(BitVec.ofNat 152 (word80 [0x282a00a12802852021,0x4b844c0320dc00145145]))),((BitVec.ofNat 152 (word80 [0xffff000003fffff000,0x76ab5eb70a632000fc0])),(BitVec.ofNat 152 (word80 [0x14c280db0a0264206,0x6762344a50a4324d34d3]))),((BitVec.ofNat 152 (word80 [0xfffffffffc00000000,0x67c4351bd4f7fc0000])),(BitVec.ofNat 152 (word80 [0xb27002c9c00b37804b,0x8026c43508d4f33cf3cf]))),((BitVec.ofNat 152 (word80 [0xffffffffffffffffff,0xf58b1674957bf000003f])),(BitVec.ofNat 152 (word80 [0xc380b30e02cc38048c,0x40b12749523f0ebaeba]))),(0x48afbb7e9c20e000fc0,(BitVec.ofNat 152 (word80 [0xfc00c3f0030fc008f0,0x88cbb5a9420cb2cb2c]))),(0xe754a985f269dfff000,(BitVec.ofNat 152 (word80 [0xfc0003f0000f00,0x451028857220cc30c30]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g63C : List ColumnInfo := [(0,2,45,16,5)]
def g63A : List (List Nat) := [[],[65],[80,50],[80,65,50]]
def g63D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7f
def g63L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g63D5)
  | _ => emptyPacking
def g63I (_ _ : Nat) : Option (Nat × Nat) := none
def g63 : Forest := ⟨63,5,fun i => g63Y[i]?.getD (0,0),g63C,g63A,g63L,g63I⟩
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
theorem g63T : checkedTables g63 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g63 0 0 0 = true)
  · exact (rfl : block g63 1 0 0 = true)
  · exact (rfl : block g63 2 0 0 = true)
  · exact (rfl : block g63 3 0 0 = true)
  · exact (rfl : block g63 4 0 0 = true)
  · exact g63B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63G : graphValid g63 (boundsBefore K227) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low63 : Lower true (varsX 63) (graphGoal 63) 6 := lower_forest (g:=g63) (i:=0) (hints:=66883) (before_sound K227 V227) g63G g63T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K63 := extendKnown K227 6 [(63,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V63 : Known true K63 := extend_ok (m:=63) V227 low63 (by decide +kernel)
def g95Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x1ffffffffffffffff,0xdd22222ff857c000001f])),(BitVec.ofNat 152 (word80 [0x2d1415450951429085,0x1d222027b017ab5ad6b5]))),((BitVec.ofNat 152 (word80 [0xffffff80001ffff800,0x3adda05ba07880007fe0])),(BitVec.ofNat 152 (word80 [0x4800a6006d80132019,0xba19a04a007086318c63]))),((BitVec.ofNat 152 (word80 [0x1ffffffffe0000000,0x33421e54bfc800f8000])),(BitVec.ofNat 152 (word80 [0x705938164e059bc12e,0x23421654bfc9ef7bdef]))),((BitVec.ofNat 152 (word80 [0x1ffffffffffffffff,0xcc58e7684e4f41f0001f])),(BitVec.ofNat 152 (word80 [0x8061c01870061c0230,0x58c3484e4854a5294a]))),((BitVec.ofNat 152 (word80 [0xfe0000000000000000,0x4579a17773c3e0003e0])),(BitVec.ofNat 152 (word80 [0x7e001f8007e003c0,0x4441215770c18c6318c]))),(0x0,0x0),(0x33aa5dc49781bffffc00,(BitVec.ofNat 152 (word80 [0x18000600018000400,0x1820c80800121084210]))),(0x0,0x0),(0x0,0x0)]
def g95C : List ColumnInfo := [(4,0,91,0,7)]
def g95A : List (List Nat) := [[],[65]]
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
theorem low95 : Lower true (varsX 95) (graphGoal 95) 8 := lower_forest (g:=g95) (i:=0) (hints:=16844355) (before_sound K63 V63) g95G g95T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K95 := extendKnown K63 8 [(95,[]),(126,[80,50]),(159,[64,16,49,118]),(190,[64,33,49,80,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V95 : Known true K95 := extend_ok (m:=95) V63 low95 (by decide +kernel)
def g111Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffffffffffffffffff,0xd961ba3aa853c00003ff])),(BitVec.ofNat 152 (word80 [0x28802a40252014805,0x1921322280139294a529]))),((BitVec.ofNat 152 (word80 [0x1ffff00007fffc00,0x3eda224bb248800f8000])),(BitVec.ofNat 152 (word80 [0x54c294c15b60a99099,0xbe58224b32488e739ce7]))),((BitVec.ofNat 152 (word80 [0x1ffffffff8000000,0x73423e149fc81f07c00])),(BitVec.ofNat 152 (word80 [0x2700270013800de02e,0x230236108f486318c63]))),((BitVec.ofNat 152 (word80 [0x1fffffffffffffff,0xc858e56c4e4f7e00001f])),(BitVec.ofNat 152 (word80 [0xb80338019c00ce0130,0x58c14c4a4c4c6318c6]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffe000000000000000,0x4579a17773c00007fe0])),(BitVec.ofNat 152 (word80 [0xc013c009e004f001c0,0x44688147708294a5294]))),(0x33aa5dc49781bfff8000,(BitVec.ofNat 152 (word80 [0x1c000e0007000200,0x1821c808501318c6318]))),(0x0,0x0),(0x0,0x0)]
def g111C : List ColumnInfo := [(2,0,109,0,7)]
def g111A : List (List Nat) := [[],[80,50]]
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
theorem low111 : Lower true (varsX 111) (graphGoal 111) 8 := lower_forest (g:=g111) (i:=0) (hints:=16778595) (before_sound K95 V95) g111G g111T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K111 := extendKnown K95 8 [(111,[]),(125,[65])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V111 : Known true K111 := extend_ok (m:=111) V95 low111 (by decide +kernel)
def g119Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffffffc0003fffc00a,0xd27ec6ac340000000fc0])),(BitVec.ofNat 152 (word80 [0x25104a90da9094856a,0xc27ec2a03404d34d34d3]))),((BitVec.ofNat 152 (word80 [0x3ffffffffffffff7,0x20988afa71b000fc003f])),(BitVec.ofNat 152 (word80 [0x98213021302190243,0x209888e801a145145145]))),((BitVec.ofNat 152 (word80 [0x3fffffffc0000009,0xcd1cb9421e203f03f000])),(BitVec.ofNat 152 (word80 [0x4e009c009c00de0b88,0x441cb8421c20c30c30c3]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x3ffffffffffffffa,0x162d5a1393dfc000003f])),(BitVec.ofNat 152 (word80 [0x7004e004e004e00c08,0x1625121312128a28a28a]))),((BitVec.ofNat 152 (word80 [0xffc000000000000009,0x15e285ddcf000003ffc0])),(BitVec.ofNat 152 (word80 [0x2700270027001001,0x1180051dc30b2cb2cb2c]))),((BitVec.ofNat 152 (word80 [4,0xea977125e06ffffc0000])),(BitVec.ofNat 152 (word80 [0x803800380038002004,0x88024104e04c30c30c30]))),(0x0,0x0),(0x0,0x0)]
def g119C : List ColumnInfo := [(1,0,118,0,7)]
def g119A : List (List Nat) := [[],[65]]
def g119D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7f
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
theorem low119 : Lower true (varsX 119) (graphGoal 119) 8 := lower_forest (g:=g119) (i:=0) (hints:=16844101) (before_sound K111 V111) g119G g119T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K119 := extendKnown K111 8 [(119,[]),(123,[80,50])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V119 : Known true K119 := extend_ok (m:=119) V111 low119 (by decide +kernel)
def g175Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffffffffffffffffff,0xf83ab722001c3fc01d4e])),(BitVec.ofNat 152 (word80 [0x290140054012802902,0x98083422492444402948]))),((BitVec.ofNat 152 (word80 [0xff800fffe0003fff80,0xee9901800e00020e17f])),(BitVec.ofNat 152 (word80 [0xb22a65298adb15324c,0xcee99019fffdddc0617f]))),((BitVec.ofNat 152 (word80 [0xfffffffc00000,0x4485df40703c0070875])),(BitVec.ofNat 152 (word80 [0x3c13804e009c01bc17,0x4855b4db6cccc20a55]))),((BitVec.ofNat 152 (word80 [0xfffffffffffff,0xe319cb82380003c80fb7])),(BitVec.ofNat 152 (word80 [0xc05c06700ce019c018,0x311cb81b6d9998006b7]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffff0000000000000,0x47738edc003fc3000ba])),(BitVec.ofNat 152 (word80 [0x6007800f001e0060,0x43708492491112044a2]))),(0x0,0x0),(0x1b854419fffc003ff2c1,(BitVec.ofNat 152 (word80 [0x8001000200000,0x2221c9000]))),(0x0,0x0)]
def g175C : List ColumnInfo := [(2,0,173,0,7),(1,0,174,0,6),(4,0,171,0,6),(8,0,167,0,6),(32,0,143,0,6),(0,2,45,128,5),(3,0,172,0,5),(6,0,169,0,5),(9,0,166,0,5),(12,0,163,0,5),(34,0,141,0,5),(36,0,139,0,5),(11,0,164,0,4),(128,0,45,0,4),(128,2,45,0,4)]
def g175A : List (List Nat) := [[],[80,50]]
def g175D3 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x6304c8650,0x85585504826832642ac2,0xa82419818750f5150120])
def g175D4 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x8e08000000000000982,0x26841000438200,0x401f4f,0x4773a1c4dc6b32184bc5,0xb2c154a44f26114843f1,0xe0e45c2b140843c1b0c0,0x54240f060240c0300235,0xe0d70d85528d584dcd60,0xd4635e0d70995218e782,0x5d36154239e0976d4540,0x9e180dc5544826961075,0x585209c5831d56148361,0xdd143585209a7845db51,0x48271e0d76d45208e786,0x5d35148278e1170d4520,0xdc3835c3514837050d70,0xd4520b298419550482d2,0x60c65541209c88750d50,0x483c25514354120b6085,0x5855048398d956154120,0xd8b7550d40483625d543,0x50120f81435c540482e8,0xe116150120f814358540,0x4827861f5150120ba184,0xd4540483e050f5150120,0x8b7845db5148235e0d76,0xd45209e3805cb5148278,0x60275485208e7825d265,0x442a56126550d109d087,0x50d50443c45514354110])
def g175H4 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [9,0x40000d80000000900000])
def g175D5 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x18,0x10000000000000000070,0x21c10000000000e09304,0x40804c10e080d08041,0xda051da04000000cc100,0x2608001304090087a61,0x6a61004c1040001810e,0x800004c100000000001,0x2000a98200000c040640,0xa004703801800d105402,0x4e1700f1dc5f11c2f05b,0xfef9bcee6b82dab52ceb,0x22c2af2b6ac2aaa9297a,0x2a849fa789ca6c99a599,0x32468e63389a1984dff7,0xadd7745cb715bf6c9ac6,0x999964d8d6017a5b5595,0x153f4ad2547d12414ff3,0xe4f3398e0368d4338c83,0x8bc2a09b2548f2247c1,0xd8691704f108350a01b0,0x26fb9ac1a94f570d855,0x29eee0b16a33ddd160d4,0x76bb9ac1a8cf77258351,0xbaee6b06a33d5c265486,0xf3b82a490cef72593509,0xbae9b1aa1b5dc7635427,0xaba6c2a84f572d8550da,0xec7b0aa1b5d8f515436b,0xb1a42a84ef72595409ea,0xeda8a817c5c3515039ca,0xa2a0a05e571d9520b5ee,0x8b2a4173dcd65482f3b8,0xaca905ad7419520b9ae6,0x32a41795c465482f2b8e,0xc8905e970d51209deeca,0xa2413b1d954482f3b8aa,0x8907cb7050d20bc8eab0,0xa41b9d956148372b2ac2,0x905e77458520f8a86b0a,0x4179ddb51482f2bb6a29,0x5e574d4520f8a87a8a4,0x1f85c351483b5b2aa090,0x7686554120bd6e8a8241,0xdad5150483b4aa2a0907,0xcb7354120f9286a8241f,0x8dc550483f0b0aa0907e,0x35154120bd6eaa02417a,0x5d540483d5b2280907a9,0x5450120fc2e2a0241f85,0x8540483f1a8a80904bf7,0x4595209bee6b2a417a5c,0x352482f3b8aa4905eb70,0x549209eaeda8a41795cb,0x51482f8b86a2905e6754,0x8520dceca90a41b95952,0x1483f090aa0904f57499,0x5109eae532a2179dc954,0x4436abb286886d66550d,0x10f2aa8a1a21f4dc1434,0x43b8aa2a0887d3735411,0xfa286a822135dcd60d4,0x6f0b86a2907894350120])
def g175H5 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0xf3781c00680609e780,0x63000000381dbe00,0x85d8d023e2b8ca90000,0xe3004812928000000009,0x43c5400000ab344fc72a,0x3000880cd00693855ac7,0x9c1b0a32f8b5a24c1d28,0x697780000004820008,0x7c0009d001724c1c08e4,0x994c0004253692011d20])
def g175D6 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x6080708,0x68010a08018a09a38498,0xa10401c1807042860067,0x20821e010a0046d0006,0x68d18719c38628010a18,0x400850c10a09c0840a01,0xa00a89a01a89840a0284,0x8281a0584a028060a010,0xa08018a2060088021207,0x430e10b10472780420c,0x91c18c7054802d621acb,0x619ac0549b5867163870,0xe01002d01a14561a7160,0xa422e83d01c485018581,0x185810a0858f40741a1,0x3741c1a6dcc1d0d9c190,0x31c1cc29612624647a8d,0x11421f426835039fe3ea,0x7a4ee9d13906e4d81aa3,0x48660c91862e85a0af95,0x32944f89792623a45085,0x8fc1e039c6c0cc1862dc,0x558a212c2283c06c0c01,0x50228390600900c00c00,0xbf58352fdd8552bfd81,0x52fd58b51fd54b51fd58,0x351bf59350bf58b50bfd,0x9150dfd5150df55150f7,0xd8d50bfd8950fdd8550f,0xdd4550fd48550bfd9540,0xbf59540fd58540fdd454,0xfe54140fbd9520fb995,0x20fb59520fb19520fbd9,0x120fb59120fbd5120fb5,0x5120bfd9520bf59520fb,0xd4920fb54920fd58520f,0xdd4520fe54120fd55110,0xfd54910bdd8552bd58b5,0x1bd58351bd99521f9549,0x21b7d8d50bdd8550f9d4,0x720f350d20f958520f9d,0x4520fa54120fa50120f9,0x48520bd99510bd59110f,0x550d10bd58910fc54110])
def g175H6 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0xe9f30bc4eb3c04600000,0x8490000000,0x84d000000000,0x353000000a1300,0xc36000d2864a93bf,0x9a0482bf0ac2083933d,0x340719199db554800000,0x286000000000000000d,0x52000000000000134226,0x6b8585db711600028a00,0x22c2270000000000000,0xbc2000000000000000,0x883a1e00000049e00,0x13e24c0,0xc06937000000000000,0xe8700000000000004700,0x418000000000fc40,0x51200000054b008000,0x52d00,0xf3a000454a380,0,0xe32000000a2a00,0x1b4b9b000c2211b0000,0x1da4f030000a25000000,0x42f0000004a500,0x31a8210003410000000,0x651000000,0x7a300000000000,0x61ce450000000000,0xe89000,0xf000505d23f3100000,0xf3f00069c000000e,0x207000000000aac,0xa0df2ee1500060100021,0x942e440000000001330,0x41100050c0007af,0x80300000000000060,0x20000000000000000001,0x55b50000000000000243,0x71700010e51f42,0x9f245143882353041800,0x19010015150700008200])
def g175D7 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x14c16e15c,0x14c16290504385710504,0xae82d023a0858990377,0x815d14ace2c10b0c5482,0x476d061230f96d2ed42,0x8734124681a007fd4bfa,0xa5ff50fea87f503fa41f,0x751fa90fbc83da41f510])
def g175H7 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x31a46508f913,0x36000518002ab00e4a80,0x8ee4000002b57ef53200,0x33600000000a2a,0x31000000b282bc000001,0x1629348156f1c0018c3b,0x19005d3ea00000000000,0xb6eab0000000015cc,0xa14000000000,0x2cb0006c00073401,0x24495065db7083400403,0x45c074000009a1e4c001,0x28000003e7d0881521b9,0x35810000028b80000085,0x8007a7aeb0300060425b,0xca424000001694000000,0xce05c26b14710c9,0xf105879e160f001ccc33,0x2c80027a2100283040a])
def g175D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x9b8013f
def g175H8 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0xa1014008a0034b0e,0x31eb80001307302400ba,0x9a803303300000400064,0x3c7e10066609100401])
def g175L : Nat → Packing
  | 3 => (3,5,4,0,0,4,0,g175D3)
  | 4 => (37,4,4,0,0,9,0,g175D4)
  | 5 => (86,3,4,0,0,10,0,g175D5)
  | 6 => (57,2,4,0,0,11,0,g175D6)
  | 7 => (11,1,4,0,0,9,0,g175D7)
  | 8 => (1,0,4,0,0,0,0,g175D8)
  | _ => emptyPacking
def g175I : Nat → Nat → Option (Nat × Nat)
  | 4 => lookupWord 1 17 0 6 2 0 g175H4
  | 5 => lookupWord 11 67 5 11 6 1 g175H5
  | 6 => lookupWord 27 271 4 12 7 1 g175H6
  | 7 => lookupWord 18 127 5 11 6 1 g175H7
  | 8 => lookupWord 5 31 5 9 4 1 g175H8
  | _ => fun _ => none
def g175 : Forest := ⟨175,8,fun i => g175Y[i]?.getD (0,0),g175C,g175A,g175L,g175I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175P3_0 : block g175 3 0 3=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g175B3 : block g175 3 0 3=true := g175P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175P4_0 : block g175 4 0 37=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g175B4 : block g175 4 0 37=true := g175P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175P5_0 : block g175 5 0 3=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175P5_3 : block g175 5 3 83=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g175B5 : block g175 5 0 86=true := (@block_merge g175 5 0 3 83 g175P5_0 g175P5_3)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175P6_0 : block g175 6 0 19=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175P6_19 : block g175 6 19 38=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g175B6 : block g175 6 0 57=true := (@block_merge g175 6 0 19 38 g175P6_0 g175P6_19)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175P7_0 : block g175 7 0 5=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175P7_5 : block g175 7 5 6=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g175B7 : block g175 7 0 11=true := (@block_merge g175 7 0 5 6 g175P7_0 g175P7_5)
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
  · exact g175B3
  · exact g175B4
  · exact g175B5
  · exact g175B6
  · exact g175B7
  · exact g175B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175G : graphValid g175 (boundsBefore K119) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low175 : Lower true (varsX 175) (graphGoal 175) 9 := lower_forest (g:=g175) (i:=0) (hints:=1395) (before_sound K119 V119) g175G g175T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K175 := extendKnown K119 9 [(175,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V175 : Known true K175 := extend_ok (m:=175) V119 low175 (by decide +kernel)
def g183Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfffffffe0003fff801,0xd61939a64a20000f83e0])),(BitVec.ofNat 152 (word80 [0x489402540da81290ad,0x541930a24a20c6318c63]))),((BitVec.ofNat 152 (word80 [0xfc00fffffffffffffe,0x600516ffc95801f0001f])),(BitVec.ofNat 152 (word80 [0x902610982130432048,0x600412fe40514a5294a5]))),((BitVec.ofNat 152 (word80 [0xfffffffc000001,0x39c4f2134e803e007c00])),(BitVec.ofNat 152 (word80 [0xe13804e009c01bc171,0x1184b2134e00c6318c63]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffff,0x428bea0b99e80000001f])),(BitVec.ofNat 152 (word80 [0x1c0a7014e029c0181,0x28be80199aeb5ad6b5a]))),((BitVec.ofNat 152 (word80 [0xffff00000000000001,0x22fa117cb687c0007fe0])),(BitVec.ofNat 152 (word80 [0x38007000e00200,0x2260014c908318c6318c]))),(0x0,0x0),(0x9d26ecc07137ffff8000,(BitVec.ofNat 152 (word80 [0x200c0018003000400,0x88024c00210421084210]))),(0x0,0x0)]
def g183C : List ColumnInfo := [(1,0,182,0,7)]
def g183A : List (List Nat) := [[],[32]]
def g183D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7f
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
theorem g183G : graphValid g183 (boundsBefore K175) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low183 : Lower true (varsX 183) (graphGoal 183) 8 := lower_forest (g:=g183) (i:=0) (hints:=66885) (before_sound K175 V175) g183G g183T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K183 := extendKnown K175 8 [(183,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V183 : Known true K183 := extend_ok (m:=183) V175 low183 (by decide +kernel)
def g207Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x7ffc01ffffffffff,0xffc035677a50000f000f])),(BitVec.ofNat 152 (word80 [0xd01482c82a4252148,0x29c035454a5555555555]))),((BitVec.ofNat 152 (word80 [0x7ffffffff0007ffc,0xf354385e8000f000f0])),(BitVec.ofNat 152 (word80 [0x5615914814c1b60990,0xccf304385e8333333333]))),((BitVec.ofNat 152 (word80 [0xff800001ffffff8000,0x26278cbf400f000f00])),(BitVec.ofNat 152 (word80 [0x9819e2702701380de1,0x7026078c3f4333333333]))),((BitVec.ofNat 152 (word80 [0x1ffffffffff,0xfe580f6a35b0f000f00f])),(BitVec.ofNat 152 (word80 [0xe01e03803801c00e01,0x80180a2a358222222222]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffe0000000000,0x24f859c3ef0000fff0])),(BitVec.ofNat 152 (word80 [0x200000c006003002,0xf041802444444444]))),(0x19b82850c0fffff0000,(BitVec.ofNat 152 (word80 [0x4000010008004000,0x888888888]))),(0x0,0x0)]
def g207C : List ColumnInfo := [(2,0,205,0,7)]
def g207A : List (List Nat) := [[],[33]]
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
theorem g207G : graphValid g207 (boundsBefore K183) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low207 : Lower true (varsX 207) (graphGoal 207) 8 := lower_forest (g:=g207) (i:=0) (hints:=16778851) (before_sound K183 V183) g207G g207T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K207 := extendKnown K183 8 [(207,[]),(222,[64,33,49,118]),(238,[80,50,64])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V207 : Known true K207 := extend_ok (m:=207) V183 low207 (by decide +kernel)
def g215Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfe007ffe0007ffe00a,0x64598b000700004cc0fd])),(BitVec.ofNat 152 (word80 [0xa44b12545b514a456a,0x44598b3bbb777700c0fd]))),((BitVec.ofNat 152 (word80 [0xfffffffffffffffff7,0x83e1e0807800ff11023d])),(BitVec.ofNat 152 (word80 [0xc812009802600c8247,0x8281808889111100401c]))),((BitVec.ofNat 152 (word80 [0x7ffffff8000001,0xdc843307800f00220c5f])),(BitVec.ofNat 152 (word80 [0xf09c04e013806f0381,0xd48433199b3333000a1f]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x7ffffffffffff2,0x14f06d8000f00fbc3287])),(BitVec.ofNat 152 (word80 [0xe047011c04700400,0x1470655556aaaaac0a83]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffff80000000000001,0x1b0b1f7800fff0c03de8])),(BitVec.ofNat 152 (word80 [0x18006001800800,0x908082220444440a160]))),((BitVec.ofNat 152 (word80 [0xc,0xe43e807fff0000ffc112])),(BitVec.ofNat 152 (word80 [0x10060018006001000,0x20220044448888bb0000]))),(0x0,0x0)]
def g215C : List ColumnInfo := [(1,0,214,0,7),(4,0,211,0,7),(0,1,86,128,6),(2,0,213,0,6),(16,0,199,0,6),(3,0,212,0,5),(4,1,82,128,5),(5,0,210,0,5),(17,0,198,0,5),(18,0,197,0,5),(64,0,151,0,5),(128,0,86,0,5),(128,1,86,0,5),(6,0,209,0,4),(65,0,150,0,4),(68,0,147,0,4),(132,0,82,0,4)]
def g215A : List (List Nat) := [[]]
def g215D4 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x120224040000,0xd99b0518,0x4f1b305490f182430300,0xb0d821915454ec560464,0x55153d477454d5148671,0x21d5350521d457554d41,0x487c15515350521da374,0x505604863a6077259350,0x8eb825db43d423ae0976,0xd07508eb825d941d4236,0x61b73507508eb8759121,0xd42b8e116148750ae186,0x50521d43a85914148750])
def g215D5 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x62,0x58818c0400000000006,0x20400308100000000101,0x40708103c20b0810804,0x9010090100b01240402c,0x490124010800d049010,0x22414207048010d64070,0xc0000000000000001810,0x190100181640490b3803,0x8b052c1b0abcadab0aaa,0xa4a5a889ea749ba6898a,0x5c95a5090a3c8da2888a,0x1c85a10829fc7b9e0729,0xbc6b9a06698c619785a9,0x64559484c92c47910428,0xf4398d82e8b42b8a8288,0x9c25890228841f8701a8,0x5c158480e81c038009be,0xe6b0ca93b5c762552e7b,0x92c8a9dd77159153b9ae,0x4322a7755c46454f8fb2,0x2a8a9f1c6455153e9ee4,0xaa2a757dc55454e77b92,0xcba1e5d6554f439dee4b,0x2a873ddc56550f2fb2aa,0x6a1e5f6454d51eaee2a9,0xaa33bdc965d072eb2aa7,0xa0f1d5454f419bee6b2a,0x833bdc9655066ebaec6a,0xed970d8d419bceca9a8,0x3371d9535072eb2aa6a0,0xf1d5454d41e6aa8a8a83,0xd554d515076db1ac0a0d,0xe57199121b9ee6b22437,0x95c65448677bb2a890f4,0xd5454d21f8ee2a9a4379,0xdd151487b2aa2a290de7,0x7550521bcaeaa0a43e99,0x5141487d2aa28290fc77,0x350521f8aa6a0a43f85c,0x141486f5ba2c090eea64,0x58121fc282b0243badc9,0x64d427db8ac9a84f976d,0xf509f6e8b0ea13e5db4,0x1d435cb2683a84f97650,0x750d72c8a0ea176dcd41,0xd4378b0a83a86e976487,0x50dd2c890ea1f850521d,0x42edb9a82a06ea764854,0xfc28290a81d154d5148,0x675b92c9a86e16148750])
def g215H5 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0xf8fa5200,0x914f0000950070270000,0x930600de8c346df97b78])
def g215D6 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x20200180,0x704c0c1010018b08890,0x8890048d1214020b088,0xd1214030446890088900,0x90c5820018c081040404,0x90a00b0c2020018304,0x40082c1040020630204,0x4007081170a00610100,0xc2020200407082840c2,0x90f0062e1c280242141,0xe921432081606890043,0xc6a4448050681606806a,0xc0c102002052020801c9,0x200782604130e018204c,0x380643170c3c01a48382,0x1ac146e012b041b80486,0x1e48d582611616116a43,0x42a65868f08e1822180a,0x6609606b3560a8b4aa84,0x4f49a528a404658950da,0xa3f97bcef1d7b9b70ed,0xb1afb44652c1d79adf58,0x8a89472734b09110da00,0x3ca760e91c53626acc81,0x7c2b44c48b0ed1962c04,0x707a0be11011000bf58e,0x54bf58654bfd8d54fbd8,0x954bfd8554f7d9153f79,0x9153f759153f719153f7,0xd8553f758553bfd9153d,0xf55153bf59743f754f43,0xbfd9543bf59543f754d4,0x3bfd9151df55151bf597,0x41ef55341f754f41bfd9,0x541bf59541ef95141ef5,0x5141f7d8d41f754d41fd,0x54541fe58141fb59521f,0xb99121fb59121fb95121,0xfb55121fed0f50fe50f5,0xfed0750fe50750fe50d,0x40fe50540bbd8954d755,0x153d754d51b7d8d41f35,0x4d21f954521f950521fa,0x58121be59350be58750f,0xa48750bed8540fa48540])
def g215H6 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x618361cffd1000f78,0xe5000209f65cbc000007,0x50000006a7000002c900,0x6b35d80037d6d08b,0xa1f000003900c2f2be0b,0xa0d2551b058000830000,0xc2a1d25420194cb791,0x66400272d0000015c000,0x18000000000000884d1b,0x1000000038000358d80,0x58ca10cd54980071f8f,0x74c89ee860015999145c,0x2120000018380010a3,0x4c0015c8000000029893,0xac360199580000147000,0xcad0621011a000150])
def g215D7 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x40e084a3062840e084,0xc18a82130914b0a180a2,0x462ca8602452a0849305,0x2c286024a1822ca86024,0x682130910482384c1413,0x6c80916984b0c02a984c,0x145849304ea6ab0d5c9c,0x451d4c0511f8b4420f00,0x3fca9fd54fea9ffd0ffa,0x87fd51ffa0ff507bca7d,0xd53f690fed43f281f910])
def g215H7 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x20d2980,0x19,0xd1d000c8800003d23d40,0x354003110000,0xf100132000000000,0x400,0,0,0x971af7a0000000,0x125001230001,0x30000000000000000000,0x2200034200000002f,0x3a40000000e140060c0,0x157000000000,0x34,0x4207d60038e73c000000,0x7dd86a800a2de45224,0xa0000000000000000000,0x11,0xe00000003550020c0016,0xd7cc8700000000000030,0x9003da00000000000000,0xf002,0xb0000000000518000000,0x2b0b6c64003bb5b0016,0x7000e100000000000000,0x3208420])
def g215D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x6242013f
def g215H8 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x99a800000,0x5d03006c2b804e1100fc,0xd5804680000052004900])
def g215L : Nat → Packing
  | 4 => (16,4,5,0,0,7,0,g215D4)
  | 5 => (68,3,5,0,0,10,0,g215D5)
  | 6 => (55,2,5,0,0,11,0,g215D6)
  | 7 => (14,1,5,0,0,9,0,g215D7)
  | 8 => (1,0,5,0,0,0,0,g215D8)
  | _ => emptyPacking
def g215I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 4 23 2 8 4 0 g215H5
  | 6 => lookupWord 17 109 4 11 7 0 g215H6
  | 7 => lookupWord 13 211 2 10 6 0 g215H7
  | 8 => lookupWord 3 23 5 8 4 0 g215H8
  | _ => fun _ => none
def g215 : Forest := ⟨215,8,fun i => g215Y[i]?.getD (0,0),g215C,g215A,g215L,g215I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215P4_0 : block g215 4 0 16=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g215B4 : block g215 4 0 16=true := g215P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215P5_0 : block g215 5 0 3=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215P5_3 : block g215 5 3 65=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g215B5 : block g215 5 0 68=true := (@block_merge g215 5 0 3 65 g215P5_0 g215P5_3)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215P6_0 : block g215 6 0 13=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215P6_13 : block g215 6 13 42=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g215B6 : block g215 6 0 55=true := (@block_merge g215 6 0 13 42 g215P6_0 g215P6_13)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215P7_0 : block g215 7 0 6=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215P7_6 : block g215 7 6 8=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g215B7 : block g215 7 0 14=true := (@block_merge g215 7 0 6 8 g215P7_0 g215P7_6)
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
  · exact g215B4
  · exact g215B5
  · exact g215B6
  · exact g215B7
  · exact g215B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215G : graphValid g215 (boundsBefore K207) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low215 : Lower true (varsX 215) (graphGoal 215) 9 := lower_forest (g:=g215) (i:=0) (hints:=16844359) (before_sound K207 V207) g215G g215T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K215 := extendKnown K207 9 [(215,[]),(250,[80,50,32])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V215 : Known true K215 := extend_ok (m:=215) V207 low215 (by decide +kernel)
def g219Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xc007ffffe0ffff4214,0x900003f000000fd4759f])),(BitVec.ofNat 152 (word80 [0x8a510a204224404004,0x92ad555555555554558e]))),((BitVec.ofNat 152 (word80 [0xfff800ffffffe014ce,0x8000fc0000fff00a49f8])),(BitVec.ofNat 152 (word80 [0x602c028000820486,0x630c30c30c30c248b8]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffff0000ffffa110,0x381f00003f000fc38e7b])),(BitVec.ofNat 152 (word80 [0x80300b040900a010,0x94228a28a28a2828a71]))),((BitVec.ofNat 152 (word80 [0xffffffffff0000860d,0xe800000fc003f02c1067])),(BitVec.ofNat 152 (word80 [0x2304408c008e048208,0xed94b2cb2cb2cb2c9043]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x9923,0x47e0000ffffc00301f84])),(BitVec.ofNat 152 (word80 [0xc0180300830081901,0x2084104104104100504]))),((BitVec.ofNat 152 (word80 [0x6ae0,0x2ffffff00000003fe000])),(BitVec.ofNat 152 (word80 [0x300600c010c0100260,0x24108208208208292000]))),(0x0,0x0)]
def g219C : List ColumnInfo := [(1,0,218,0,7),(2,0,217,0,7),(8,0,211,0,7),(16,0,203,0,7),(64,0,155,0,7),(128,0,91,0,7),(0,1,82,136,6),(0,16,137,66,6),(2,16,137,64,5),(3,0,216,0,5),(8,1,82,128,5),(9,0,210,0,5),(17,0,202,0,5),(64,16,137,2,5),(80,0,139,0,5),(128,1,82,8,5),(129,0,90,0,5),(10,0,209,0,4),(19,0,200,0,4),(25,0,194,0,4),(66,0,137,0,4),(66,16,137,0,4),(72,0,147,0,4),(82,0,137,0,4),(130,0,89,0,4),(136,0,82,0,4),(136,1,82,0,4),(137,0,82,0,4)]
def g219A : List (List Nat) := [[],[64,49,118]]
def g219D5 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x1010,0xb6785b3060336d8f70,0x54941d3554dc9515078d,0x5915454521f255450951,0x4878d5955450521f2554,0x54941487cce055454540])
def g219D6 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x18,0x206000860542050401,0xa04000605c54315040c3,0x400600081c0c2001c18,0xc004150508541150454,0x1421a04685421523020c,0x101040454442a3600801,0x5058c542140d63611000,0x7c40b181454304a7a11a,0x1058546831a150aaea62,0x829d26e9825a952368a2,0x228520e7e1e2771b6681,0x926116e5814a4b11e440,0xfa390de340ba2508e1e0,0x5a0d0160027eb96c2aa4,0xfd72d9151beee2b22a3d,0xddc5545467eba6c4a8e7,0xd54d8951e7aa8a12a33f,0xdc9655077bb8acaa0fb7,0x7155141e7aa8a92837ed,0xc152506fbb92a2a0cfd7,0x5d91219feeab22433fdd,0x9544867ebb2a890ebd64,0x55121beee8a8a43bdd91,0x514877ab22a290f75545,0x4521fca84a8a437d5d54,0x14877bb2a8290ef56550,0x521f6aa8a0a43f954941,0x486efb9a82a87bb71551,0x40f72e2aa281ee5c5425,0x2efb9a82904dd75d8d4,0x1e6aa8a8a83ce5515150,0x3d4a1242a07195454d40])
def g219H6 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x940000d6a1730000,0x72fac54000ac000d])
def g219D7 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x52a118465433,0x8ca8664c111e8110c68,0xc152c2434064a0858a11,0x108d20c68a910c7070c1,0xa320183462c307143020,0x5450c080182a2988e9c,0x7c14831b0e1019a30318,0xc080172a3464a543311,0x929510b860a00a9118b1,0x184182802e54836608a3,0x106862e45323c108a8e6,0xca8454d848d40a883c53,0x45422a6820e0e20a803c,0x6cb8b0410f1064b10907,0x8718d342173411a2a116,0xc38c69a1650c868d70ee,0xcbf778eeb1c8b766b6c,0xc984ad95529e52f23c41,0x8738cf1672a64fc8b102,0x1dc2f8470730a20f4148,0xffd8554ff58554ff59,0x151ff58951ff50951ff5,0x4941ff59121ff55121ff,0x50d50ff50550ff50520b,0xfd8554bfd9151df55151,0xbfd8951bf59541ef5514,0x1fd54541bfd9121bf591,0x21fd54521fd50521fe54,0x640fe48640fed8540fe5,0x4540fe48540bfd8540b7,0xd8d41f694e40ee55140f,0x694d40f654d40ee50940])
def g219H7 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x65400000aa20000000,0x93580400000c49e7c00,3,0x90023001684c49cd0018,0x64b4684600,0x80fb2c00690,0,0x91c000000000000004,0xc9d40000000000000000,0xf3000000722,0x2800000000288000000,0xe0dc9800d282088b69,0xd61776800000c8200000,0xc33cf418000001,0x82000b3600000000000a,0x3f4b8000000000000000,0x82342d86000002e80a5,0x28e14e1c004005c])
def g219D8 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x228603e33451,0x86019238a03c81495c6,0xe58a05474429648c880,0xa04991240a10d8e10042,0x8f1cc34a2049213d3108,0x8ca24f14d8e10046c600,0xd8e111a1b556e9f409c8,0xb44b1e0a82a007f553fa,0xa3fd41fe90ff543fa81f,0xd30fe907f443f481f940])
def g219H8 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x14540,0xa7491294e7,0x7c0e8e0000064d000,0x26c00000b3eb6e2b7510,0,0xc860000000000000000,0x92f08000000000000,0x61d001a0c007600000,0x13c0020b68200,0x240800000002c7800,0x208002a7f42000001448,0x18000000000000000000,0x3a40004a00003400,0x261001c2000713000,0xd24000c5e54f,0xb867c700020fb320600,0x1a3603000000e2800,0x21000000000700000000,0x221108000001900802])
def g219D9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xa4188201bf
def g219H9 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x24600480000,0x83ba800000055913e,0x50000001f50000066000,0x8c00242c0000,0x1800000000000007c920,0x2880000000000044,0x320000000007c80000,8])
def g219L : Nat → Packing
  | 5 => (7,4,5,0,0,6,0,g219D5)
  | 6 => (38,3,5,0,0,10,0,g219D6)
  | 7 => (34,2,5,0,0,11,0,g219D7)
  | 8 => (11,1,5,0,0,9,0,g219D8)
  | 9 => (1,0,5,0,0,0,0,g219D9)
  | _ => emptyPacking
def g219I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 2 17 4 8 3 1 g219H6
  | 7 => lookupWord 12 127 3 11 6 1 g219H7
  | 8 => lookupWord 12 127 5 11 6 1 g219H8
  | 9 => lookupWord 4 71 2 9 4 1 g219H9
  | _ => fun _ => none
def g219 : Forest := ⟨219,9,fun i => g219Y[i]?.getD (0,0),g219C,g219A,g219L,g219I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P5_0 : block g219 5 0 7=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g219B5 : block g219 5 0 7=true := g219P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P6_0 : block g219 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P6_1 : block g219 6 1 4=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P6_5 : block g219 6 5 33=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g219B6 : block g219 6 0 38=true := (@block_merge g219 6 0 1 37 g219P6_0 (@block_merge g219 6 1 4 33 g219P6_1 g219P6_5))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P7_0 : block g219 7 0 6=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P7_6 : block g219 7 6 17=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P7_23 : block g219 7 23 11=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g219B7 : block g219 7 0 34=true := (@block_merge g219 7 0 6 28 g219P7_0 (@block_merge g219 7 6 17 11 g219P7_6 g219P7_23))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P8_0 : block g219 8 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P8_2 : block g219 8 2 9=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g219B8 : block g219 8 0 11=true := (@block_merge g219 8 0 2 9 g219P8_0 g219P8_2)
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
theorem low219 : Lower true (varsX 219) (graphGoal 219) 10 := lower_forest (g:=g219) (i:=0) (hints:=16842819) (before_sound K215 V215) g219G g219T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K219 := extendKnown K215 10 [(219,[]),(246,[64,33,16,49,83,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V219 : Known true K219 := extend_ok (m:=219) V215 low219 (by decide +kernel)
def g231Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xff000fff80ffffedec,0x100070001c6184c3f237])),(BitVec.ofNat 152 (word80 [0x2a26a2251a25228de8,0x1b559294a42004413207]))),((BitVec.ofNat 152 (word80 [0xfffff00000fff01992,0xc003807c0002071c03a3])),(BitVec.ofNat 152 (word80 [0x4c04c0b62c0644d992,0xc6ccb18c6c02050800a3]))),((BitVec.ofNat 152 (word80 [0xffffffffff00000559,0xc03c0f83e00008201ccb])),(BitVec.ofNat 152 (word80 [0x700700383007870558,0xc244908424000000044b]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffffea0d,0x91c00003ff83f03fe0f5])),(BitVec.ofNat 152 (word80 [0x804804c00048000205,0x4aa65294a8aa13e40b0]))),((BitVec.ofNat 152 (word80 [0x492,0x2e000ffc03fc003fff02])),(BitVec.ofNat 152 (word80 [0x7007004070080000,0x29334631832820739b14]))),((BitVec.ofNat 152 (word80 [0x1360,0x6ffff00003ffffc00008])),(BitVec.ofNat 152 (word80 [0x8008000080000000,0x84210514a800000]))),(0x0,0x0)]
def g231C : List ColumnInfo := [(4,0,227,0,8),(1,0,230,0,7),(2,0,229,0,7),(32,0,199,0,6),(64,0,167,0,6),(3,0,228,0,5),(33,0,198,0,5),(34,0,197,0,5),(36,0,195,0,5),(65,0,166,0,5),(66,0,165,0,5),(128,0,103,0,5),(35,0,196,0,4),(37,0,194,0,4),(67,0,164,0,4),(129,0,102,0,4),(130,0,101,0,4)]
def g231A : List (List Nat) := [[],[16,101]]
def g231D4 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0xf624c3021d730b22e43,0x2a74e39159172181538,0x73c930db8aa921e38e07,0x80dc96550f1c302c02e4,0x32a8798b746087054d43])
def g231D5 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x1860b88c0,0x10000000000000000000,0,0x90400000000000000000,0x10208000000000,0x907a9cee470b79b,0x6d86ab499ecc64b1986c,0x5c6b353a6d1e833b9ac,0xbe53238ec5e230b82bfd,0xf2f376b9dc2db6ab3d92,0xc35a2b950a24e259208a,0x421f8f07236198c05a2a,0x1147e39198b44e210d85,0x41e00ae5821c564d4e75,0xe0574d4e538bf8759064,0x54e75e0574d4d53aeb82,0x5d36054ebce0574d8153,0xad9831d36054ebce0554,0xd81538ef825d36054e3d,0xe0574d8153aeb8259360,0x54ebce0564d81538fb87,0x5906054ebae096418153,0xaf3815906054f3ad9172,0x18153ce9645c86054f36,0xe037654c53cdb76dc153,0x14fa65937054c53ae781,0x5516214fb2e015358853,0x8f7875516114fb4e0153,0x58453af3815516014f36,0xe1d53580538f586dc554,0x90eb560f5458643ed380,0x54d6190f3ae037259543,0xce880dc96550f3adcb70,0x59543cf371dc16550f3a,0xdc87059543cf3711c165,0x50f3a601721954387f87,0x5946550f1b5957219543,0xb4d821955350ed660065,0x54d43cd876dc15350f66,0xdd07054d43bc9821c153,0x50e3be097654d43a6d82,0x1955350e9e6006554d43,0x8ef825d943d423de0576,0x50f50d5953dc143d423d,0xe0574d8d509f3815d350,0x542b6e017558f40acd82,0x1d563d02b56047558f40,0xad9801d563d03a5e0554,0x58f40c9d7458f53d02a7,0xe195350f408f7815db53,0x503c654d43541408f781,0x5d265cc23be097655330,0x8f7815d954cc27ce0574,0xd43308f7815d2654c23e,0xe0176d51308ef825d954,0x4c23de0576551308fb80,0x5d9544c3965915354130])
def g231H5 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x7c62000007,0x4011806a000000003c00])
def g231D6 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then (word80 [0xf7dba6c0,0xa9efa74d8153df2e9b02,0xa7be1d36054f7daa6c0a,0x9efa54d8153df2a9b02a,0x7bedcf6054f7db8ec0a9,0xef971d81539fae9b02a7,0xbed936054f7d326c0a9e,0xf964d8153df0c9b02a7f,0x6dcf6054f7db1ec0a9fd,0xb53d8153df6c3b02a7be,0x5876054efd3b0c0a9efb,0x6418153df2c8302a73f5,0xda5414f5eb24a829cff7,0x655053beee2aa0a7b7dd,0x95314f6eb22a629fdb70,0x54c53ddca8b10a7bb551,0x6214f7b2a2c229ef5545,0x8453df4a8b00a7be5516,0x14f3eb2ea921ddd73d5,0x243cfccaaa4879f59554,0x90eefb9aa921df771552,0x43dbeeca9c87f6dc1539,0xf7baa2c321ef5545864,0x39fae1b2a873f5ce6550,0xf3fb2ccaa1cff7359543,0xdbee6b2a87bbdc96550e,0x7fb82caa1efb7059543d,0xf0e0b2a879fd956550ef,0x7b92caa1dfb70595439f,0xcec32a879f5946550ef6,0xb90caa1df97019543cfe,0xcba9a876f5d35350eef3,0xb4a6a1ddd7594d43f3ca,0x929a87b71d95350fafb2,0xaa6a1f5c6554d43f3ee8,0xa9a87e71d15350fcf2a2,0xa6a1f9d5454d43bbee2a,0x9a87f6dc15350fec382a,0x6a1cfd7654d43cfecaa9,0xa879f1955350edfba2a6,0xa1dfb7054d439faebb02,0x87af5536050f6ea9ec0a,0x1cff7359350deee2b26a,0x17ddc564d42fbb8aa9a8,0x4ff7458f50df6e0b1ea1,0xdedc153d427fbb287a84,0xfd7650f50d7ac8a1ea1b,0x758d43d43aea9a87a85f,0xb7050f509fae7b22a17d,0xdc564542fbb8aa8a85fb,0x70551509fae9b1aa1ded,0xc153542fdb82a6a84ff7,0x650d50dbec6a1aa1d754,0xd43542fcba6a0a85f973,0xd4150ef2a7a82a13f5ce,0x65d027fb9acba05bf735,0x5340f6ee2aa681b7dd56,0x3d036f3aac7a06dd7558,0xf40db8eab1e813fdd563,0xd035eaa2c7a04fd76d4f,0x40b7ae9a9e81b758f53d,0x27fbb2a7a04fd7654f4,0xdbac6a9e817edc153d0,0x2dfbaa87a05bd7550f40,0xd7acaa1e81e754d43d02,0x7eb9ccaa04ff7359540d,0xeee2b2a81bedc165502d,0xfb9aa8a07b77155140f7,0x6e0aa2813f5db53502de,0xba6a6a05f970d4d409fe,0xeca9a817edc153502dfb,0xaa86a05bd7550d40d7ac,0xaa1a81e754d43503ddb8,0x286a07b95454140ef6a6,0xa8281de54d50503dca1a,0xa0a04fd74997309fee8b,0x2e61bedc165cc27fbaac,0x9984fd76d5330bbae7aa,0x6613fdd954cc27ebb2a9,0x986bd6455330beee2aa6,0x617edc154cc36eb22a79,0x87db7054f30df2eda866,0x1be59750cc2fcba6a198,0x7d973d4330fb2a7a8661,0x7e9d540cc37cb2a81987,0xb95450330fb2a6a06613,0xf5d2654c27fba2ca986f,0xb70595309feeab2261be,0xdc1644c27ebb6a8985dd,0x73d5130bf2e1aa2613fd,0xd9544c27ebb2a8986bd6,0x455130beee2aa261b759,0x1534c3edb82a6986f964,0x54130fb2a6a8261fc545,0x504427bb8ac9a9de9721,0x81539beeca98a7a75915,0x314f66a9ac429ed55358,0x453db2a6b00a7b554d61,0x90e77b92caa1cfb70595,0x439dae432a873e5c0655,0xe7bb8ac9a869d5458f4,0x9eee2b2a81d654f50cc,0x27db82ca987595354130]) else (word80 [0x4080060800000018201,0x8200042080060820008,0x1082000c4c01218200,0xc408302000040010000,0x4b130060219084860a18,0x200282c00a182c4c0101,0x82001810508858380203,0x2000031020110203102,0x1082000020420201082,0x6083820008200000080,0x2000f0040bc01000200,0x1608001102420821,0x8400482000000094213,0x15085860809082120810,0x8006000800008005082,0x42080820408182080003,0x2001000406858218202,0x82080020800000204085,0xa0850608202080a08200,0x5a184168610082000000,0x820a08208c4c00c20202,0x182002020602100820,0x9021418200082060a082,0x408002020e082001,0x2020820200202020808,0x20684120828208482120,0x84821e46101020000000,0x20800400101d10400102,0x87a08400302040820c0,0x80002008412081020030,0x20000200082060800400,0x10582004820682105821,0x60810085c00878486068,0x80dc010370040c101037,0x40dc01037004070022,0x1e170058583c0105700,0x5c0087837007c0085f00,0x60773971d7116f56e96d,0xd6d16c56a969d6816756,0x6964d6416356195fd5f1,0x5e55c95bd5b158556955,0xd55153551950d5014d54,0xc94bd48147544942d411,0x4053e93cd3b138536935,0xd3312e52c92bd2b12a52,0x8927d26125523922d211,0x2051e91dd1c11b519917,0xd16115513912d1211050,0xe90dd0b108506905d051,0x4503901d011004fe8fc,0xcfa0f94f78f6cf60f54f,0x48f1cee0ec4ea8e8ce50,0xe34e28e0ce00df4dd8db,0xcda0d84d78d5cd50d44d,0x28d1ccf0cb4c98c7cc70,0xc54c48c3cc20c04bd8bb,0xcba0b84b68b5cb30b04a,0xe8adcad0ac4ab8a9ca80,0xa34a18a0c9f09e49c899,0xc98095493892c9108f48,0xd88cc8c08a488886c850,0x84482880c7f07e47c87a,0xc79076474872c7106f46,0xd86ac69068467866c660,0x64463860c5e05d45c85a,0xc58057455854c5305145,0x84fc4d04b449848c470,0x46444843c4204043f83c,0xc3b03a438835c3403242,0xf82dc29026423820c1e0,0x1b418817c1601341080d,0xc0b009405803c0013fdc,0x564d4f7bb8ac9a9ef471,0x593539fee0b26a77ddc5,0x64d4eeeb9ca929ddd74d,0x4e539fae3b22a73f5c36,0x454f5fb24c8a9df97099,0x153bdee4b22a77ddc564,0x54efdb82c8a9ebd64191,0x53d7ec92a2a7775ce545,0x4eefb9aa8a9ddd74d4d5,0x39fae9b0aa77edc16154]))
def g231H6 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x83d921,0x63fc0c4101229300004a,0x8b1600000073a000000e,0xd000334505804000c12,0xa2600050f402b1900,0xf1a3a2d2f6,0x42fa7ba3000a00000000,0xb45433d2b808899e1c03,0x943c0000000000000008,0x20217000e9f424025000,0x32900a000000b4100,0x118000000c3e0,0x33500000022a000206,0x915d0e000e3658100,0x10700062700002da380,0xa84809a23d1122ef1f,0xd0ba1b6a4a9d000000f1,0xde43932f1423b0004448,0x2c740713501ba6003000,0x51ef37000a3122814000,0x228951846b204041a480])
def g231D7 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then (word80 [0x406042c1,0xa10c7860824283004090,0x9141802c2160c3090910,0x3105840618b045a24280,0x416890a0080c61610216,0x84203101a108309085a2,0x1218b442431618216182,0x80c5c1107a212184450,0x47883c3043c304101c11,0xe2101e14382407862c18,0x40c1810818b121031210,0xb020c308880831058608,0x2220c18104105e014260,0x20304098078c105840f8,0x30a103600e2070d8058,0x80808b07805200f00f10,0x26018184c0303c4861e0,0x10789c0304081c360162,0x84161f00614587c01840,0x81f006162840f803082c,0x207c018516103e00c282,0x2101e0148601e182038,0x32004104078078e1058,0x7c0185c42d0830980616,0x2700c10384c01840e130,0x610583c0384161300c1,0x5e00c18bc03031d8080,0xc1018ec03c4083f00c10,0x7e01818fc03031e3300e,0x100c3c0404070700a162,0x838380509047e01420bc,0x28309805060c1e01c2c,0x41e0f00e105e01c1e012,0x303463f00e102410f805,0x8a130410e20bc0243883,0xf0410e201c11c3c02638,0x61300c1620f09806082c,0x4e01820bc03031f80606,0x3b00b182101e3b00c147,0x8ec0304431f0061c2600,0xc20b0f803082c3861020,0xb0f803082c3e00c2440f,0x80309042600e241c0283,0xe5be40e33e1fe04df0dc,0xedbada6d8bd69d55d41d,0x2dd12cfecdccb3c98c76,0xc5bc4ec2cbfcbe8bc6bb,0x2b9eb83b68b54b40b1eb,0x3ae1acdab9a97a7ca61,0xa46a2ba17a039e89c69b,0x299796e94c92a9018df8,0xbd89487285783c81a7f8,0x7cf7a678475b7397106e,0x76be6a36886516285f85,0xd65b459257054e533518,0x4f64d44b249747c45a43,0x840f3ed3cb3a938e36c3,0x4a32f3142f22c92a7285,0x26324822d20b1e91c71a,0xc19116f1461241090e70,0xc50a308105f03d01b000,0xff99353ff59353ffd525,0x3ff95253ffd9153ff991,0x53ff59153ff19153ffd5,0x153ff95153ff55153ffd,0x4d53ffd8553ff58553ff,0xd8153ff58153ff95053f,0xf55053ffd5243ff55243,0xffd9543ff99543ff5954,0x3ff19543ffd4d43ff54d,0x43ffd8143ff58143ff59,0x350ff55350ff58f50ff5,0x4f50ff50f50ff59150ff,0x55150ff58d50ff54d50f,0xf50d50ff58550ff54550,0xffd4f40ff54f40ffd4d4,0xff54d40ffd5330ff553,0x30ffd5130ff55130bf59,0x353bf58753bf58353bf5,0x9653bf59253f7d4e53bf,0xd9153f7d4d53bfd8553b,0xfd8153fed8153fe18153,0xbf99453bf59053f754c5,0x3bf99643bf59643bf592,0x43f754e43bfd9543bf99,0x543bf59543bf19543f79,0x4d43f754d43bfd8143bf,0x99443bf59443bf59350b,0xf58f50dfd4f50df54f50,0xbf58750bfd9150bfd8d5,0xdfd4d50df54d50bfd85,0x50fed4150bf99740bf59,0x740ef55340bf58f40ef5,0xf40bf99540bf59540ef,0x55140ef50d40fe54140b,0xf99730bf59730bf59330,0xf754f30fed4330fe5033,0xbf99530bf59530bf591,0x30f754d30fe54130bf99,0x510bf59510fe54110bed,0x8153af99053af59053bb,0x58853bd58453be58053b,0xd58643b798f40b758f40]) else (word80 [0x16084442c31608,0x40610b080c3422420889,0xa0101890a08b0a08406,0x1a28210189041842c604]))
def g231H7 (j : Nat) : Nat := if 3 ≤ j then 0 else (if j<1 then (word80 [0x3a80272796,0x4a0c0000000003,0x23000000000000000000,0x5ccd58a00000000,0x1259c10800312600,0x1596000000000,0xb740000440000000000,0xd4e80000000000000003,0x18eee585680000000000,0x56b1c491e171379f40,0x53980000000a000,0xc04000000000000,0,0,0,0,0x2565a,0xd0000000000000000000,0x2340000000000,0xa340000000000,0xd0cf3840000000000001,0xb260000000002b700000,0x2094000000d6ccaac0,0x701400000000,0x570001d6,0x40000000000000000000,0x73c0000000,0x65b40000000000,0x179b00000000000,0x1e1500000,0,0,0x1e32000,0x537f1a8,0x40c00000000000000,0x250200000000000,0x184200,0x4d8000,0xe3e000,0,0x1ea90000,0x2d7400000000000000,0,0x933000000021,0x894ffd04000000000000,0x38a40000000000000000,0xde40016b10000002,0x49c00000072600000000,0,0x51adc9e00000,0xa69800000,0x3988000000,0x148e0000003410,0xa1300000000000000000,0x102d36400000000,0,0,0x121b000000,0xb6f0000000000,0,0,4,0x94000000000000000000,0,0x1f,0x800000000000056499aa,0x4b380000000000,0,0x52,0x90000000000000000000,0,0,0,0xa55b5e80000010be0,0x490511e000e5d80000,0,0xc73262a3e0b2800,0x1cc10000000000000000,0x10cfb368000000,0xf648,0,0x46800000000000000,0xb28c90c00000,0x648000000000039f800,0x13ac000,0x22d40000000000000,0x31940000000,0x288bce000000004,0x3c000000231800000000,0x1e04000000000,0x7a2df02000000,0,0x6c631860000004,0x3372be00000000000000,0xc4dac13a,0x28cd800000053930ae00,0,0x206800000000008fe000,0xc4000000004270000000,0x63106204000008020,0x12010c06000000002002,0x5800040031680201]) else (if j<2 then (word80 [0x8a8b958000000000,0,0x42300000000000000001,0x258000000231b85c0000,0x1c00000000000,0x28cc00101,0xd64d8000000000000000,0xc238000000000,0,0x13400,0x69e9490b40f,0x54000fc48000000000d0,0x8cd1c00000000000030d,0x2000000000000000032d,0x8000000000468800050c,0,0x65000000000000000000,0x71ebf3941a00000,0x18a5000000000000,0,0xd3a8000000000,0x3e0c00000009b8,0x1e7400000000000000,0x2aa800000000000000,0x7a0800000093,0xc8001234000000000000,0x18300000000000000000,0x18ee0000000000000,0,0,0,0x214600,0x2599b17000036,0xc0000000000000000000,0x8890000000,0x7830,0x71a89c80,0x1816000000050a29100,0x636800,0x4a5081a640000,0x582c0014b83b60000000,0,0xf7300000000,0x26e800000000000000,0x31d000200c00,0x2eab871e368dc000000,0x3e920000000000000000,0x21000000000000000001,0x4a000000073500008466,0x1d800000000000000000,0x30c800000,0x5acc00,0x1a2800022bc00098d000,0x58f4000,0x1590d978,0,0x8c700,0x29,0x90000000000000000000,0,0x42d800000000066a1,0x84400000000000880000,0xf3080000,0x48000001b9800,0,0,0,0,0xc0000000004920,0xc840000b4766700000,0,0,0,0,0,0x101400000000,0x33,0,0x950000000,0,0,0,0xc4d000000000031500,0x32a5c72f6ea0,0xa242000000000000000e,0xed20000000cf6000,0x60f0,0x7d280000000,0x1a880,0,0x1df800100f000000006,0x40000005e7c000000000,1,0xa2c0000003e3a0000000,0,0,0xdb0000f2d000000000,0x2c56000000000,0,0xece8000,0x14200000000000000000,0x54800000000]) else (word80 [0x18ba000000,0xa00ca9945e,0x4970000001a1f0000,0,0x1b,0x8c000000307193000000,0x66b8000000000000000,0xea70000000001cdf,0x5840,0x62c1af0000029a,0xc60000001e0300000020,0xb80000000000001c3600,0x3d7,0xe0000000000000000000,0,0x81200000000000000000,0x1cd6c3b3a5c0000,0xc5c800000000000000,0x1a2e33f000000000,0x32c,0x2c6e000,0x2b400000000000000000,0x1c4000000521c0000000,0x10bc00000000000,0,0x792c000000000000000,0x39c4000000000,0x8480000000000,0x35b80000000000000,6,0xc08d1330800000000000,0x938000000000,0x214,0xc0000000000000000000,0x27520000000000,0x14a80018be0000])))
def g231D8 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x40,0x43e03051078061011203,0x410204b1e01870841e0,0x18528980c10712018405,0x3a030504f3a03051818,0xa10680e0c90601c4260,0x3033a0303cc5eab92c84,0x3a998a8421989c300c00,0x3fea7fe53fea9ff14ffc,0x87fd43fe21ffd43faa1f,0xf40fea07fcc3fa61fd10])
def g231H8 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x927,0x66bc0d6f53c8e53a65d7,0x400024d56e000eae107e,0xe425b00080e0426441b0,0x704b2a789828503d1816,0x70006751cb071915b11c,0x9b0e54735c954b8df82b,0xc3c11dd3145d61a75513,0x3668930377b994490004,0xd7a5ad47000840e6d01e,0x659a45226c25d05a0100,0x698e565d2d2d1,0xb020909b12450b62d17,0x93e40254eb2ed2115813,0x209e15f21c724edcc38f,0x54200a61c08bd55e683b,0xb37a22b6470fe1013616,0x30ca54867099a25ce6f5,0x8e543952335d4600083f,0xa1f000d16bafa29051ad,0xa7ee372a6623905e9de1,0x4c64a62c76064180a714,0x83486912f0ef8dd64fde,0x7c19e13b3a523000f1b8,0xc86ad76d06b3d000b57,0x76cb9c1802a1043e1814,0x212701374004767640f,0x301218f2b00230f6102,0x3706002d000010310000])
def g231D9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x8200ff
def g231H9 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x71c56000000000,0x895b58c00008a000016d,0xa0002503b6d,0x382003200000001900,0x2b20019800003d000000,0x1d1000030a0000000000,0xcad080000004f0012c7,0x50008c00000000000204])
def g231L : Nat → Packing
  | 4 => (6,5,5,0,0,5,0,g231D4)
  | 5 => (70,4,5,0,0,9,0,g231D5)
  | 6 => (231,3,5,0,0,12,0,g231D6)
  | 7 => (120,2,5,0,0,12,0,g231D7)
  | 8 => (14,1,5,0,0,9,0,g231D8)
  | 9 => (1,0,5,0,0,0,0,g231D9)
  | _ => emptyPacking
def g231I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 17 0 7 3 0 g231H5
  | 6 => lookupWord 20 127 5 12 7 1 g231H6
  | 7 => lookupWord 72 1481 3 13 8 1 g231H7
  | 8 => lookupWord 37 163 8 12 7 1 g231H8
  | 9 => lookupWord 6 67 2 9 4 1 g231H9
  | _ => fun _ => none
def g231 : Forest := ⟨231,9,fun i => g231Y[i]?.getD (0,0),g231C,g231A,g231L,g231I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231P4_0 : block g231 4 0 6=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g231B4 : block g231 4 0 6=true := g231P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231P5_0 : block g231 5 0 70=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g231B5 : block g231 5 0 70=true := g231P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231P6_0 : block g231 6 0 18=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231P6_18 : block g231 6 18 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231P6_114 : block g231 6 114 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231P6_210 : block g231 6 210 21=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g231B6 : block g231 6 0 231=true := (@block_merge g231 6 0 114 117 (@block_merge g231 6 0 18 96 g231P6_0 g231P6_18) (@block_merge g231 6 114 96 21 g231P6_114 g231P6_210))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231P7_0 : block g231 7 0 9=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231P7_9 : block g231 7 9 63=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231P7_72 : block g231 7 72 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g231B7 : block g231 7 0 120=true := (@block_merge g231 7 0 9 111 g231P7_0 (@block_merge g231 7 9 63 48 g231P7_9 g231P7_72))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231P8_0 : block g231 8 0 14=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g231B8 : block g231 8 0 14=true := g231P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231P9_0 : block g231 9 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g231B9 : block g231 9 0 1=true := g231P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231T : checkedTables g231 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g231 0 0 0 = true)
  · exact (rfl : block g231 1 0 0 = true)
  · exact (rfl : block g231 2 0 0 = true)
  · exact (rfl : block g231 3 0 0 = true)
  · exact g231B4
  · exact g231B5
  · exact g231B6
  · exact g231B7
  · exact g231B8
  · exact g231B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231G : graphValid g231 (boundsBefore K219) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low231 : Lower true (varsX 231) (graphGoal 231) 10 := lower_forest (g:=g231) (i:=0) (hints:=16778597) (before_sound K219 V219) g231G g231T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K231 := extendKnown K219 10 [(231,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V231 : Known true K231 := extend_ok (m:=231) V219 low231 (by decide +kernel)
def g237Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfff8fffac0000f8001,0xfe61b1183199c0387ff7])),(BitVec.ofNat 152 (word80 [0x88120882c94aa4920a,0x506090190099a8080a40]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x3fff3fc020007001fe,0x23e1fc261ffcf9c19])),(BitVec.ofNat 152 (word80 [0xa040080318818622,0x302034538040cc8a9d48]))),((BitVec.ofNat 152 (word80 [0xc0003ff94007807e00,0xe843fe00c7e03f01fe9])),(BitVec.ofNat 152 (word80 [0x2c082010631130c64,0x22042642046202d31185]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffc004a0f800001f,0xf107c0000f8003ffe01e])),(BitVec.ofNat 152 (word80 [0x1300131434a55a28c4,0x870400000f0003142014]))),((BitVec.ofNat 152 (word80 [0x1f00007fe0,0x1f800000ffffc000010])),(BitVec.ofNat 152 (word80 [0x1c041c2018c66c3088,0xc54800000b9530044210]))),((BitVec.ofNat 152 (word80 [0x71fffff8000,0x1fffffff00000000000])),(BitVec.ofNat 152 (word80 [0x200020000000004111,0x8934984200000200000]))),(0x0,0x0)]
def g237C : List ColumnInfo := [(1,0,236,0,7),(4,0,233,0,7),(8,0,229,0,7),(32,0,205,0,7),(64,0,173,0,7),(128,0,109,0,7),(5,0,232,0,5),(9,0,228,0,5),(12,0,225,0,5),(33,0,204,0,5),(36,0,201,0,5),(40,0,197,0,5),(65,0,172,0,5),(68,0,169,0,5),(72,0,165,0,5),(96,0,141,0,5),(37,0,200,0,4),(41,0,196,0,4),(73,0,164,0,4),(76,0,161,0,4),(100,0,137,0,4),(129,0,108,0,4),(132,0,105,0,4),(136,0,101,0,4),(160,0,77,0,4),(192,0,45,0,4)]
def g237A : List (List Nat) := [[],[98,83],[32,99],[32,48,80,96],[48,101],[48,82,96,32],[80,50],[80,98,48,50],[96,32,50,83],[96,82]]
def g237D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xc7060f915c87254110
def g237D5 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then (word80 [0x53842973,0x21ba2c8a9c218b964603,0x7154a1086fc9b0dba2a3,0x8527e4d875915184295,0xf24c3ac8a8c21a358560,0x56454610c5cb2301b92a,0x30852ee417559141842c,0x6b2caa2a2a0c2163b956,0x56454210b55c92e8b22,0xa10878664d6454d50843,0x532c9c1ae2a842149f94,0x60b7359510a4e4a305b9,0xaca8853564482dcd6544,0x217f28c16e6b2a2189f8,0x4dcd7259510c4e426e6b,0x92ca88437a60735c9654,0x4313f0839ae4b2a218d8,0x73e017259510877cc2e4,0x392ca8843765f8359662,0x4420ff30ba8eab12210d,0xf9361d64d491086fc9b0,0xeb1ea488627e13835d95,0x244313f0841aeca92218,0xd883e01765491086fc9b,0xdba2a48842fe5187d8d,0x524421f730bb0e0a9221,0x8b97661070549108f9cc,0x2e2382a48866c611711c,0x1524433a306b88e0a922,0x10df9361d6590910a2fc,0x9b0cba88488437e4d875,0x94424421bb2fc1aca212,0x2185d75e0d6510910c36,0xbaf04b288488437e6165,0x5cc4244297728b2ae021,0x2214db935957010910a7,0x5c92cab80848842fe518,0x7595324420ff2ac3ac89,0x922157195a077454110a,0xf0c9503ba2a08859a648,0x85591504434b6c6c16a6,0xa82219c9835c87254110,0xaf1c8ae4392a08859664,0xc85589504434b707a9ac,0x4a822166992d4d625411,0xb64c98e4b12a08859ae,0x4964d49504434b306b1e,0xa4a822166992d9152541,0x10d2dc1ec6a92a08859a,0x64b6354950442e532839,0x2a4a8221749931c95254,0x110bb0c88e4a92a0885d,0x264e6254950442cd726b,0x12a4a8221a6b83589525,0x4110d34c32a5212a0886,0xd854981909504434d30c,0xa9464a8221b615260632,0x54110d2cc32a6992a088,0x69a619524c950443c96c,0x6a9264a82215e0925d37,0x154110db0c12a438aa08,0x86d86095294550443cc2,0xc4a94a2a82219d383dcd,0x5154110ea9b9aa6a8aa0,0x8879458d53545504436c,0x704a92a2a8221e616254,0x9515411086ecbf06b2e8,0x8874555173547404423,0xe32fc0aa920221c69755,0x895290110cb9c3aa8a8c,0x808847c65f8254640443,0x1b10fc1acaa0221a9b84,0x20d6550110bc8c9908a8,0xa80885e8648845454044,0x2e632b2a2a2a02219d38,0x3dcd5150110b98ca6a6a,0x8a80886cc55382545404,0x43c62a9b12a2a02211f3,0x985d62150110d98c2aa9,0x10a80887585d55248540,0x443e42a8a9242a0221f8,0x1434c92150110c6dc3f0,0x6b2c60884f4e4d81d523,0x4427a726c0ea518221d,0x3174551518c110ce8baf,0x6a8c60884f4e4d85486,0x30443ac2eaa924318221,0xe5391595534c110e2cb2,0xae8a9a60885d464f5454,0x530443a62e8aa2a29822,0x1d517454d514c110f28b,0x2aa690a60886f0e15324,0x85304437830a99242982,0x21dc1754c9214c110f60,0xb2a6490a60887705d132,0x485304421f32fc32a790,0x2215e39760552c8110cf,0x1c3b02a964088674e0d7,0x354720443aa2e6a9aa39,0x221bc3834c951c8110f,0xa0a9a64a8e4088758549,0x71543204421bf26c3aca,0x90221c69765495048110]) else (word80 [0x1c3040,0x3010301000000000000,0,0,0x14100002800400,0x20604050400141000000,0x10410000000,0x4104220400ae0812206,0x41850000241040008004,0x5901089010,0x80b06065902240440000,0xb810000004001000a4d4,0x828d514a1d422814fc9e,0xd3c2754e49bd362694cc,0x98d3025d4b495d2a2514,0x9c92d242454848fd1e23,0x946c8cd1822d45489d12,0x22143c86d0c21542483d,0x620940c80d001fd3f47,0xdcfa1f13dc7acf41e53c,0x477cee1d93ac74ce81cd,0x39471ce21c137c6ecd99,0xb0350680ce99a32e650c,0x898e316620c29822fe5f,0xbc9762e65c0b696a2ce,0x590b095e2b6560aa9522,0x9e530a49462865009e93,0xa26e4d09892e24c48c90,0x11d22a448879071fe3f0,0x7a0f11dc3ac740e51c43,0x7c6e0d91ac338658c818,0xa3085f8b715e2b04808d,0x11421c3f87c0f21c4370,0x6b0d01943105f0b81502,0x383f0500941101a02e05,0x880e00c00c00217f28,0xc16e6b0ea18cd73e0562,0x18950967c9b03b14a4a8,0x4cee5181dc1525436c32,0x4c08e0a92a1369926047,0x549508ddca303b82a4a,0x852e650805cb6154295f,0x28c32e530aa14cf93619,0x7298550cb4c2b00b94c2,0xa843766264dcd6154299,0xf24b26e6b0aa14cf9259,0x735855086fcc6e6312c,0x2a8627a1373189615431,0x3b09b98c4b0aa1569905,0xc95218550c6bc3f06b08,0xc2a8437e4d87d8a51542,0x1ef22c26eca9c410df93,0x61f545862086fc9b0dba,0x2a31063cdc5809c56548,0x21ef30b88e2b2a410bf9,0x461b735452085fca30eb,0x2c629059a64763549504,0x8369706a9aa4a82415c9,0x931c97154120da5c1aa4,0xb8aa09069a6195294550,0x4834d30ca9462a824186,0xd65e0974d4c20a57c92e,0x8b26a610533e497458f5,0x30821ef22c26eca98414,0xb79161d6454c20c5cb23,0x1b9aa90852de4587591]))
def g237H5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xa
def g237D6 (j : Nat) : Nat := if 11 ≤ j then 0 else (if j<5 then (if j<2 then (if j<1 then (word80 [0x987d4a30,0x442be61b528c110d7975,0xd4a30442fc607528c110,0x9fb8754a304435e5d552,0x8c110df175546304437c,0x5d1518c110f735454630,0x443dc551518c110fd383,0x54630442fce09518c110,0xbf38548630442fc61521,0x8c110df17548630443bc,0x595218c110fe15248630,0x4427ee11754c110ddb83,0x5d5304437ce05754c110,0xedb8359530443bce0565,0x4c1109fb855d1304433e,0x595744c110df3815d130,0x4427e61f544c110af986,0xd5130442f660f544c110,0xbf181d51304427e61d54,0x4c110db97455130442fc,0xe05544c110ed96554d30,0x443765d1534c110bdb82,0x54d30443f4605534c110,0x9f987d4930442be61b52,0x4c110bd983d4930442fc,0x607524c1109fb8754930,0x443765d5324c110ed965,0x4c930443765d1324c110,0xdf175545304437c5d151,0x4c110f735454530443dc,0x551514c110fd15354530,0x442fce09514c110fd132,0x54530442fce15214c110,0xbf185485304437c5d521,0x4c110ef165485304437c,0x5d1214c110fd15348530,0x443f8549214c110fe142,0x485304427ee0d75c8110,0xdf1815d7204427e61e65,0xc8110be982997204427e,0xe1d65c8110bdb8359720,0x442fae0965c81109f987,0xd4f20442fa60b53c8110,0xbf181d4f204427e61d53,0xc8110afb8654f2044376,0x5cd53c8110deb8754b20,0x442fae0d52c8110de973,0x54b20443f860552c8110,0xbe9854cb204437a5d532,0xc8110fc9534cb204437c,0x5d551c8110bf38354720,0x4437c5cd51c8110f7353,0x54720443dc54d51c8110,0xfe15254720443f84c951,0xc8110bf1854c7204437c,0x5d531c8110fd1534c720,0x443f854931c81108ff87,0x59720442b7e0d65c8110,0xaef82597204433d59571,0xc8110de5525c7204427d,0xe1d51c81109f58754720,0x442fa60b50c8110f6952,0xd4320442fc60750c8110,0xd797554320443da54950,0xc8110bf381543204437c,0x5c550c81108ff855d920,0x4427de0575481109fb80,0x5d5204423f61d6548110,0xadf8359520442bbe0965,0x48110cf576545204433e,0x5d95048110f695254120,0x4437c6057508110df175,0x5442044237e0d71d8950,0x8ef8758862543335cd62,0x18950b39841c152542d6,0x60c7054950b71811c152,0x5423de1d61185508df83,0x5d9518839658d5354220,0xb6982d4d50482f260c72,0x54120b698594950482da,0xe0d5254120e6b6354950,0x4839a54b6154120c7965,0xdc1530832e5937054c20,0xcd963dc1530832e59170,0xd5210cb9645c3538432e,0x59170d4a10cb9645c351,0x8438e5935354210e3964,0x54d508439658d5354210,0xe3964d49508438e59152,0x54210e69625495084396,0x595534c2108df835db52,0x44237e0d7654910e5b63,0xd4d504439658d5354110,0xe69625495044237e0d76,0x541109f38754640443cc,0x5515150110bd38354630,0x44396595534c110f5153,0x54530443f04c9214c110,0xd71815d4204427ce1d51,0x8110d7175544204436c,0x5d15108110dd17354420,0x443785d52108110d6175,0x48420443705cd2108110]) else (word80 [0x15495044,0x3ba58952541109fa87d0,0x9504427e61f4254110af,0x986d0950442be61a4254,0x110b798590950443da54,0xa4254110bf1819095044,0x2be6194254110f695250,0x9504427ea1c42541109f,0x98710950442be6184254,0x110b798510950442f660,0xc4254110bf1811095044,0x2be61a3254110b79858c,0x950443da54a3254110bf,0x1818c950442be6193254,0x110b79854c950443b6d8,0xd3254110f59534c95044,0x3da5493254110df174dc,0x550442fc60f7154110df,0x173dc550443dc54f7154,0x110bf182dc5504437c9c,0xb7154110f7152dc55044,0x2f6e0d7154110bf1821c,0x550443dc5487154110df,0x37494550443bc5925154,0x110bf18294550443bc58,0xa5154110f71529455044,0x37cdcd5154110ef36354,0x550443bc58d5154110f7,0x15354550442fce095154,0x110ef36254550443bc58,0x95154110f71525455044,0x337e0d76541108ff825d,0x950442b7e0d6554110a7,0xf85591504429fe156254,0x110cef72589504439b58,0x952541109f582dc55044,0x23fe1d65d0110c7d7559,0x740442afe1165d0110ad,0xf83597404433759573d0,0x110d9d545cf404433d59,0x571d0110db5545c74044,0x27de1d51d01109f58754,0x7404435d5d551d0110f3,0x55454740443755cd51d0,0x110d797554340443765c,0xd50d0110df1715434044,0x37c6057590110cfb8759,0x640443b6e0d6590110af,0xb8259640442be61b5490,0x110d7975d5240442fc60,0x75490110d79755524044,0x2fce055490110afb8558,0xa404433e5d562901109f,0x987d4a40442be61b5290,0x110d7975d4a40442fc60,0x752901109fb8754a4044,0x2be6195290110d797554,0xa40443ba5895290110df,0x17554640443dcd515190,0x110f715454640442fce0,0x95190110ef1625464044,0x2be60b6550110bb98499,0x5404433e21d6550110eb,0xb8459540443ae2116550,0x110edb8359540443b620,0xd6550110afb825954044,0x2bee056550110ef38159,0x540442eee116550110bd,0xb8359540442be6176250,0x110cf975d8940442eee1,0x162501109f987d494044,0x2be61b5250110d7975d4,0x940442ee6135250110bf,0x181d49404427ee1d5250,0x110d7975549404427e61,0xf5150110bb984d454044,0x2fc6165150110df37594,0x5404437c5d65150110df,0x375545404437c5d55150,0x110fb38454540443ec21,0x15150110f73545454044,0x3ec9515150110fb15454,0x540442fce0d5150110df,0x37354540443dcd4d5150,0x110f715354540442fce0,0x95150110ef3625454044,0x2eee115150110f395454,0x540442fc6162150110df,0x17588540443bc5962150,0x110fb154885404437c5d,0x52150110ef3654854044,0x3bc5952150110fe15248,0x540443f84c92150110ab,0xf8459540442b7e0d6550,0x110f355454540442fc60,0x75050110af9865414044,0x2fce0550501109fb845d,0x6304433ee1d658c110ed,0xb83596304433e595748c,0x1109f987d5230442be61,0xb548c110bf181d523044,0x27e61d548c110db97455,0x230442fce05548c1109f])) else (if j<3 then (word80 [0xc1524433,0xed977054910cf965dc15,0x24427e61370549109f98,0x3dc1524433ed8b705491,0xdf281dc1524437c6077,0x549109f581dc1524433,0xe9db7054910cf976dc15,0x24437c9c77054910df17,0x1dc1524433e5d8705491,0xbb9841c152442f660c7,0x54910df1711c1524423,0xfe1576909109fb805d64,0x24423f61f65909108ff8,0x7596424423f61d659091,0xabf8459642442b7e0d6,0x590910ced7654a424433,0xdd957190910cf5655c64,0x24437954971909108ff8,0x65d5424427ee01755091,0x8fd87d95424423fe1d6,0x550910adf83595424423,0xf61f6350910f2d545494,0x24423fe157610910c7e8,0x65d4424431f619751091,0xd79805d4424423f61f6,0x510910c7d75d94424423,0xfe1d65109108fd875944,0x24431f5d56510910adf8,0x359442442bbe09651091,0xcdf655cc42443375957,0x310910cfb655c0424433,0xe59570109108ff855da3,0x24427ee01758c9108ff8,0x7596324423f61d658c91,0xadf83596324433b5d95,0x28c910beb8054a324433,0xd595718c910de5525c63,0x24423fe15764c9108ff8,0x45d9324433ee01764c91,0x8ff87595324423f61d6,0x54c910adf83595324423,0xfe1d644c9108fd875913,0x2442bbe09644c9109f98,0x5dc1324427e613704c91,0xcf964dc1324429fe156,0x4d4110a7f8558b504433,0xb5c962d4110cf5645c75,0x4427de0971d4110cf56,0x25c7504433ee1d649411,0xdb97455250442fce055,0x494110cfb8758a504427,0xe60f7454110df281dd15,0x4437c6077454110bf18,0x1dd150442f660e745411,0xbf1819d150442fae097,0x454110be8825d150442f,0xce057454110af982d915,0x442de6166454110bd98,0x3991504439ee15645411,0xe788559150442bee096,0x454110b7b8559150442b,0xe61a5454110dbb749515,0x4436edd15454110bf38,0x1551504427e613735411,0xbf3815cd50442be6136,0x354110edb73d8d50442b,0xe60b6354110b7982d4d5,0x443d6dcd5354110b7b8,0x254d50443dc605535411,0xddb7354d50443b658d5,0x3541109fa87d0d504427,0xe61f4354110af986d0d5,0x4427ea1d4354110ddb7,0x350d50443b6d8d435411,0xbf38150d50442fc6067,0x254110bf3815c950442e,0xea107254110bb9841c95,0x442f660c7254110de97,0x21c950442fc604725411,0xaf984d89504433edd36,0x254110b798598950442f,0x660e6254110e7b855895,0x4439e2156254110afb8,0x4589504433edd1625411,0xafb83589504439ed4d6,0x254110e795358950443b,0xadc96254110ee8725895,0x442dee156254110d7b7,0x4d49504439ed93525411,0xe7964d4950442de60f5,0x254110e7b63d49504439,0xe58f5254110e7b62d495,0x4439e58b5254110af98,0x694950442de616525411,0xee96294950442fc6065,0x254110d7b74549504439,0xed915254110e79645495,0x442dee0d5254110e7b6,0x3549504439e58d525411,0xf6b7254950443da1c95,0x254110e7b6254950443d,0xa9895254110f69625495,0x443dca055254110f718]) else (if j<4 then (word80 [0x50843ae5,0x915354210ed96354d508,0x42bee197254210eb9645,0xc9508439e5875254210e,0x7b7654950843ae591525,0x4210ee96254950843ae5,0x917154210bdb835c5508,0x43ae5915154210ef1615,0x4550843ae5914154210c,0xfb865d5308427ee11754,0xc2109f987d5130842be6,0x1b544c210bd983d51308,0x43b6595534c2108ff845,0xcb6544337e0b7359510c,0xde82dcd654433760b735,0x9510cdc82dcd6544337e,0x37359510cdd80dcd654,0x423f60b7359510edb80d,0xcd65442bee0173595108,0xfd84dc9654423f60f725,0x9510cdf73dc965443371,0xcf7259510add839c9654,0x4337dce7259510cef729,0xc965442bd6067259510a,0xf9809c965442afe11725,0x9510abc845c965442b7e,0xd7259510cdf735c9654,0x43371cd7259510af7815,0xc965442bee017259510c,0xdf731c9654433b5c8725,0x9510af984dc165442be6,0xf7059510edb73dc1654,0x43b61cf7059510ef371d,0xc16544337dcf7059510d,0xdb80dcd6544376dcf705,0x9510df371dc16544337e,0xd75d8d108ff825d7634,0x423fe1572d8d108ff845,0xcb6344337e0d76d4d108,0xff825db5344397e0d65d,0x4d10cdf635cb534427ee,0x172d4d109fb845c3534,0x423f60b7654d10cdf835,0xd9534423fe097654d10c,0xfb805d95344397e0d655,0x4d10e7b8059553442b7e,0xd6554d108fd86dc9534,0x427d6077254d109f980d,0xc9534437c5c57054d108,0xff845d7624423fe1574d,0x8910c7d7559662442b7e,0xd6598910aef82596624,0x433759573989108fd83d,0xd5624431fdd67558910a,0xf5819d562442b7e0d755,0x8910af7815d5624431f5,0xd47558910add831d5624,0x423f61773589108fd84d,0xcd624431fdd66558910a,0xed82995624431fdd5655,0x8910adf8359562442bbe,0x96558910aef82591624,0x423fe1176d49108ff835,0xdb5244337e0d76d4910c,0xdc835db5244277e0d76d,0x49109f7815d3524423f6,0x1f64d49108ff87593524,0x423f61d64d4910cbd745,0x9352442bbe0964d49108,0xfd87d8f524423f61d63d,0x4910cdd7358f524429f6,0x1762d4910cf7645c7524,0x433d59171d49109f7835,0xc7524433dd8d71d4910c,0xf5635c7524433dd8971d,0x49109fb845c3524433ed,0x9170d4910cf9645c3524,0x427ee0d70d4910cfb635,0xc3524433e58d70d4910c,0xfb625c352442bb60b659,0x4910adf8359652442bbe,0x96594910cf7655c6524,0x433d59571949108fd84d,0xd9524423f60f76549108,0xfd80dd9524431fe15765,0x49108ff835d95244337e,0xd7654910cdc835d9524,0x423fe057654910cf7815,0xd9524433ee0176549109,0xbf845d95244277e0d765,0x4910abf845d952442b7e,0xd7654910aed82d95524,0x42b7e0d6554910aef825,0x95524423f61b74549109,0xf581dd1524423f61f645,0x4910cbf74d9152442bb6,0xb64549108ff87591524,0x42de60354549108fd86d,0xcd524427d60773549108,0xfd87d8d5244337dcf635,0x4910aed82d8d524429f6,0x176254910bcd83989524,0x427e6037154910cfa86d]) else (word80 [0x483dadcd,0x5254120f697354950482,0xfae0d5254120eeb63549,0x50483da54d5254120f69,0x52dc550482fa60a71541,0x20f69529c550482f6e0d,0x7154120beb825c550483,0x7a1c97154120f69525c5,0x50483da5487154120eeb,0x72d8550483ba54b61541,0x20b798598550483da54a,0x6154120b7b8558550483,0xda5496154120af986945,0x50483da54a5154120f69,0x5254550482be61a41541,0x20af9868c550483da54a,0x3154120f59534c550483,0xda5493154120f6b80549,0x50483da6015254120a7d,0x84dcd650829fe1173594,0x20e7b805cd650823f613,0x7359420add849d563082,0xb7e117558c20edb805d5,0x63082b7e157458c20cdd,0x755d1630831f59574d4c,0x209ef825d3530832f61d,0x64d4c208fd8759353083,0x2f5d164d4c20cdd7458f,0x530823f6137654c208ff,0x845d9530823f61b7454c,0x20c7d65dd1530832fa1d,0x6454c20cbd8759153083,0xa760d6454c20cbf74591,0x5308337dd16354c20cf9,0x86dc1530833e5977054c,0x20cf964dc1530833e5db,0x7054c20e7965dc153083,0xae5937054c20ed963dc1,0x53082bd6135358420af7,0x8454d610823f60f74596,0x108fd84dcd65842b7e0d,0x7159610abd839d564842,0xaf6067559210abf835d5,0x64842afe057559210abf,0x855cd648432f5d573592,0x10abf855c5648432f5d5,0x7159210cbd645cf54843,0x2f59171d52108fd83dd9,0x548423fe0d76552108fd,0x86dcd548432f59373552,0x109f980dcd548432f593,0x71552109f980dc554842,0x3f61f5458e10add83d51,0x63842be6035458e10cbd,0x87593538423f61d64d4e,0x10cbd74593538433e591,0x70d4e108fd84dd953842,0x3fe117654e108fd86dd1,0x538427e6037454e10cbe,0x87591538432f61d6454e,0x10e9d83591538432fdd1,0x6454e10c7d655c752843,0x2f59171d4a10c7d65dc5,0x528432f5937154a10ced,0x62dc5528427e6037154a,0x10cf986dc1528433e597,0x7054a10cf976dc152843,0x9e5977054a10ee962dc1,0x528423f61f5258610af5,0x81d4961842be60352586,0x10cbd87593518438f615,0x64d4610cbd7459351842,0x9f61954d4610e3d64553,0x518431f59572d4610cbd,0x645cb518427ee0172d46,0x10ced7258b518433e591,0x70d4610cf9625c351842,0x9fe1165546108fd86dd1,0x518432fa1d6454610cbd,0x87591518438fa1564546,0x10e3d8559151843ad605,0x6454610cbf7459151842,0x9f61b5454610e3d64d51,0x518429fe195454610a7d,0x86551518438f59154546,0x108fd86dc9518431f597,0x7254610cbd64dc951842,0x7e60372546109f984dc1,0x518427ee017550610cbd,0x7559141842afe1954506,0x10abd86551418439d595,0x5150610eb56454541843,0xcd5515150610af984dd9,0x50842be60f7654210af9,0x82dd9508427e60f74542,0x10afb865d150842fae09,0x7454210eb98559150843,0xae60d6454210eb981591,0x50843ae5d16454210eb9,0x64551508427e61373542,0x10afb865cd50843ae591,0x7354210e7964d4d50843,0x9edd95354210e796454d])))) else (if j<8 then (if j<6 then (word80 [0x23f61f64,0x945508fd87d8a515433b,0x5cb6294550af584d8651,0x542bd60b6194550cfb64,0x5c2515435e5497094550,0xcdf73d8d5154397d8d53,0x545509f984dc1515427e,0x60f7054550d7953dc151,0x5427e60b7054550d7952,0xdc1515423f60f7459620,0x8fd81dd165882bbe0974,0x596208fd84dcd658823f,0x6137159620adf835c565,0x8823f60f76552208fd81,0xdd9548823fe0d7655220,0xcef825d9548823fe0576,0x552208fd86dcd548832f,0x59373552209f980dcd54,0x8833b61b7255220ced65,0xdc9548827b6077255220,0xde980dc9548833b5db72,0x55220ead64dc9548823f,0x61b71552209f980dc554,0x8837adc970552208fd87,0xd5163882b760f5458e20,0xaf980d5163882bbe0954,0x58e209ef825d3538823f,0x61d64d4e20cbd7459353,0x8833e59170d4e208fd84,0xdd9538823fe117654e20,0x8fd86dd1538823f61b71,0x54a208fd87d5161882bd,0x6075458620af980d5161,0x882bde055458620af581,0xd4961882be6035258620,0xafb80549618827be0974,0xd46208fd87593518832f,0x5d164d4620e3d6455351,0x8823f61d62d4620cf964,0x5c3518833e58970d4620,0x8fd84dd9518823fe1176,0x54620cdf835d951882b7,0xe0d76546208fd86dd151,0x8832fdd16454620e3d64,0x551518827e6037254620,0xe7754585518839d55161,0x54620cf77258551882be,0x6137654220af983dd950,0x882be6077654220afb86,0x5d150882fae097454220,0xeb96455150882fae0954,0x54220afb865cd508839e,0x5935354220e7b7654d50,0x8839e5915354220ed963,0x54d50883ba5895254220,0xafb865c5508833edd971,0x54220bdb835c5508833e,0xdd16154220e7b5258550,0x8839e5496154220ef161,0x545508823f6137359520,0x8fd81dcd65482bbe0973,0x59520afb805cd654823f,0x60f7159520cf7719c565,0x482be6027159520adf83,0x5c565482bee017159520,0xcf5711c565482be61370,0x59520eeb72dc1654833e,0xdc77059520deb72dc165,0x4823fe0575d8d208ff85,0x5c7634823fe1176d4d20,0x8ff815db534827ee1170,0xd4d208fd84dd9534823f,0x6077654d20adf8359553,0x4823f61b7454d209ed82,0xdd1534823f61b7154d20,0x9ed82dc5534831f5d565,0x98520af781596614831f,0xdd66558520c7f7559561,0x4823fe0d76d45208fd87,0xd8f514829f61761d4520,0x9fb845c3514833ed9170,0xd4520cfb635c3514835e,0x54d70d4520cfb615c351,0x482bd6076594520af781,0x596514823f60f7654520,0x9df835d951482b7e0d76,0x54520af581d9551482bd,0xe0565545208fd86dcd51,0x4823f61f6354520cdf73,0xd8d51482bd6076354520,0xa7d85d85514827b60b70,0x545208ff855da314823f,0xe1d658c5208fd8759631,0x482b7e0d658c520cf576,0x546314823fe1d654c520,0xbeb825d150482be60764,0x54120dbb7455150482fa,0xe097354120af981d8d50,0x483d6dcd5354120f6982,0x54d504837a5d37254120,0xbe983dc950483da54f72,0x54120f688754950483da,0xe0d5254120f698354950]) else (if j<7 then (word80 [0x1e303cc0,0x2fc4beb2f94bdf2f1cb,0xc12ec8ba32e50b852dd8,0xb5e2d3cb492ce8b2b2be,0xae92b8cad42b14aad2a,0x78a8f2a24a7a29aca652,0x958a502904a3228b0a26,0x285ca11282ca0527d89f,0x27849db27309c626dc9,0xb1268899326109752598,0x957254494224f0936249,0xc921244890323f48f723,0x7c8d923288bb22d48af2,0x25c88821e487321b485e,0x2118837205880720047f,0xb1fb07e61f5c7c81f087,0xb31e6c78c1dd076e1d58,0x7351cbc7171c207021bc,0xc6e41b786d81b486c31a,0xf46b71aa06a21a7068d1,0x9d4666195c648190863c,0x18d8627186061218305f,0xd17dc5f117ac5e5177c5,0xd917045b216b05941638,0x58815e4573159055e153,0xc54914e852b144c50d13,0xf84ef13804c812e44aa1,0x29049e11f445c10ec41a,0x102c4050f903cc0ed039,0x30e1035a0ce43210c242,0xfa0bac2dc0b342b50a74,0x27c096c243088820107a,0x41da07501bc069017a05,0xd015c04c8123042c0ea0,0x3000a802400780180048,0xc001800023f60f7458,0xb508fd81dd162d423f61,0x37358b508fd81dcd62d4,0x2bee017358b508fd84dc,0x562d423f60f7158b50ae,0xd829c562d42be6027158,0xb50abf845c562d423f60,0xf74587508fd82dd161d4,0x2bd60674587508fd84dc,0xd61d423f60b73587508f,0xd84dc961d423f60f7258,0x750add839c961d42bd60,0x67258750abf845c961d4,0x2af2117258750adf835c,0x161d423fe0d74d89508f,0xf815d3625423fe1173d8,0x9508ff815cf625423fe1,0x171d89508ff835c76254,0x337e0d71d8950cdc835c,0x762542b7e0d71d89509d,0xf835c7625433bd897198,0x950cef8758862542bbe0,0x56218950df1805c46254,0x27e6017118950aed81d8,0xa525433bd897194950b6,0xf8258d52542de6137054,0x950b7983dc152543dad8,0xb7054950b7981dc15254,0x2dea187054950b79811c,0x1525427e61370549509f,0x983dc1525427e6077054,0x950a7d859d361542b760,0xe74d8550af9809d36154,0x23fe0d74d85508ff825d,0x3615423fe1173d85508f,0xf825cf615423fe1172d8,0x5508ff835cb615433ee0,0x172d8550cf8805cb6154,0x2bee0172d85508fd8794,0xb61542bee0162d8550ce,0xd865ca615435b6157298,0x550cef645ca615437a60,0x17298550af78158a6154,0x25f61f5298550d6d72d4,0xa615435e5c35298550d6,0xd7254a61542bd60b6198,0x550cbf7499161542b760,0xe6458550cdf64dcd6154,0x3379937358550cdd64dc,0xd6154376e037358550cd,0xf641cd61543375907358,0x550d5f73d4d6154357dc,0xd5358550e5f6354d6154,0x337dcf6258550cdf7398,0x9615433bdca6258550cd,0xf73589615423fa1c6258,0x550abe8418961542af61,0x6258550add831896154,0x337dcc625855097e87d4,0x96154357dcf5258550d5,0xf73549615435bdc95258,0x550ddb73dc161543761c,0xf70585509f9805d06154,0x23fe1d6418550aef8259,0x615427e60172185508f,0xf87588615435b5c95218,0x550cf78758461543b5e0,0xd6118550cf5725846154]) else (word80 [0xf027b19e,0xae7939e1277e9dbe7609,0xd467429caa7249c5670f,0x9c266e89b426c19aee6b,0x59abe6a99a6a68b99f26,0x7699c266a999265e9962,0x652993263d98de631988,0xa60a97ee5f597be5d797,0x465cb96f25b696c25a19,0x66e58c961a58095ea56b,0x9596556954253894ca52,0x3945250593da4f093aa4,0xe493564cf93024ba92d2,0x4a5927e4909206472918,0xe45d915e448910a43c90,0xda43090aa41b90564069,0x23e88f8a3ca8f123b5,0x8e7638e8e223828df236,0xd8d7a3588d4a3438cf63,0x378cc63228c4e3048bfa,0x2ef8b822da8b522ce8b2,0x22b98ace2a48a7a28689,0xba25f894224a88ee2358,0x89a21788221f987ce1e4,0x877a1cf87021a8864218,0xa85ee16c857615785461,0x4b851613f84e613384b6,0x1278486112843210683d,0xe0e883660d383120be82,0xbe0a0826a09482160768,0x1c2058812603a80ae01c,0x80360077fe1ff27fb1fd,0xd7f39fbf7ee5faa7e6df,0x8c7e19f807de9f747db9,0xf687d65f537cedf2c7c9,0x9f177c45f027b85ed27b,0xdeb47a95e9679f9e787,0x9c9e637975e577921e42,0x78f1e2d789de187849e0,0xc7819df777c5de2774dd,0xcd76f9daf76a5da37651,0xd8e7621d7975cdd6d757,0x9d4f7525d4374f5d2e74,0xa1d22744dd0d741dcf87,0x3a5cda732dcbc72d9cb0,0x7285c9b7255c8f7225c8,0x371adc65717dc507105c,0x3b70b1c1d705dc086fe5,0xbf36fb5be76f85bd26f3,0x1bbd6eb9b9f6e65b936e,0x11b7e6de1b726d8db546,0xd39b3f6cc1b2a6c6db15,0x6c3daf76ba1ae26b71ad,0x66b1dab86ac9a9a6a51a,0x7c69b5a5e693da3768c5,0xa226871a16681da0167e,0xd9f567bd9d767459cb66,0xf19b666c19aa669198c6,0x619980657d94764e1929,0x64458f0633d8ae62a18a,0x2624d88d61d586f61818,0x4860e582a609181e6019,0x8005fe97f45f957df5f4,0x17c15ec97a35e5178e5d,0xfd7705da97645d557465,0xcdd7285c6570a5c116fe,0x5bbd6e95b696cb5af16b,0x65a9d6985a4968c5a196,0x7759a1662594d64d58f9,0x63858c962c5875617582,0x15f957cd5ed57795d857,0x255ba568958a55ed56c5,0x575557554553954a9524,0x545550653b94e853654c,0xa53114be52bd4a052454,0x8b521547f51e54735191,0x455513d44950e942b509,0x5416504140a4fed3ec4f,0x753ce4efd3b94ea939b4,0xe5538f4e2537a4dd1365,0x4d5933e4c993054bd92e,0x74b612c94ae92ab4a952,0x9f4a4128149c925a492d,0x233489120c47f51ee47a,0x11d947291bb468d19d46,0x5d191460917c45b515e4,0x56114944e913444b911f,0x444110143c90e343750c,0xe42fd09e423d08041c50,0x59412904440f902f4081,0x113fe4fea3f6cfcc3f1,0x8fc03ec4fab3e70f8d3e,0x1cf783dc8f633d50f4e3,0xcfcf303c84f1b3c30f06,0x3bdcef13b88eca3b10eb,0xe3ae0ea93a68e943a14e,0x763978e4f3924e3a38ac,0xe1c3858e103828dfb37b,0xde6375cdc836e4db336,0x90d9e363cd8035e8d6b3,0x570d4d34d4d26345ccff,0x339ccd83300cb13288c9,0xc3210c753150c3c30b4c]))) else (if j<9 then (word80 [0x80010302,0x10c1008608016040d24,0x800000082430400b020,0x6040843080008001042c,0x90410000082083c1001,0xe090c107820010100820,0xc1810044090410082042,0x18422048208924410480,0x21088111004220822404,0x5100429203245100431,0x21042030224048209041,0x12020000288181000604,0x82083011102c30418410,0x810080c3051808ac1006,0x9230c500020104112020,0x42184240402080030506,0x8003040110341040000,0x60800000004032020104,0x100000806404440a0c14,0x201042008010040001,0xe0800104060800088021,0x810406080002900100,0x41018200001044481081,0x60c1844810c020800104,0x100120a00100c8088802,0x120c1320202011301091,0x301208600b8101004100,0x20e0410000102080041,0x8100004022e040406041,0xb04100002020c04100,0x2000000000c30104,0x80040120002000408200,0x100440800004020810,0x610000040a081410381,0x82030341040002f64038,0x6120a844309054221848,0x2a110c20080150804430,0x284420a8442028482218,0x4410b8542212102c1208,0x86106104106104100424,0xc941928210928525088,0x4100a844308054221c94,0x2210482a110c2a120886,0x1108052504004c942028,0x402038200c051000b040,0x20c8581806120c085820,0x10602c100c1164088404,0x9840209840209840209,0x84020984020984020984,0x2098402d42b504d3d74,0xefd3a74e3d3774ced323,0x4c2d2f34b6d29f4a1d24,0xb48cd1f7477d1a3462d1,0x73456d14344ad0ef435d,0xbf429d06b414d03b408,0xd00b3fccfdb3e7cf633d,0x2cf333bdcebb396ce1f3,0x78cda735acd5334ecd23,0x342ccf3336ccc332acc9,0x331ecc63309cbeb2f4cb,0xbb2dfcb672c1cacb2acc,0xa77297ca4728bca17276,0xc9c326ac96f255c91b24,0xc8a3219c8071fbc78f1,0xcbc7171bfc6e71b3c66f,0x18cc5f716ec55b150c52,0xb13bc4b311dc43b0ffc3,0xe70eac36f0d5c31b0b7c,0x2c70abc273084c1d706f,0xc1a7063c153045c0b702,0x7c087012c00eff4bfbaf,0xe8bf8afdcbf5afd0bf2a,0xfbbbed6fafbea6fa3be5,0x2f8ebe22f82bdf2f76bd,0x9ef61bd6ef4cbcf6f37b,0xca2f22bc72f16bc42f01,0xbbeeeecbb9aed7bb46ec,0x2baceeadba7ae8fba26e,0x83b9f6e77b9a2e62b972,0xe56b91ee38b8cae23b87,0x6e0eb7fedf0b7aade4b7,0x56dc6b702db1b6aeda5b,0x67ed90b62ad84b5fad6f,0xb5a6d5ab52ed45b4dad3,0xb4aad24b456d06b3dec,0xf1b38acd3b336cc7b2e2,0xcb2b28ec9db25ec88b20,0xac73b1b6c67b186c5bb1,0x56c4fb126c3ab0aec1cb,0x5ac07afe2bf2afb2bdd,0xaf5ebd1af2ebc5aefebb,0x9aecebadae9eba1ae6eb,0x95ae3eb80adc6b62ad72,0xb56ad1eb38aca6b23ac7,0x6b0eac22af9abceadbab,0x56acfab02abaaaaea9ca,0xa36a7ea9bea4ea8fea27,0xa83e9eea77e9d0a6e29a,0xa646982a5ce964a5569,0x34a496916a41e901a3ca,0x8e3a2e68aaa26e88ca1f,0x686ea17e859a12a829a0,0x227f99fce7e49f567c69]) else (if j<10 then (word80 [0x20000100,0x2000410006080,0x3040008000040008000,0x100000040800100,0x60800304000c8410001,0x82000400a8200000141,0x2a08005040a0800,0x90400000002050404080,0x42208000001000008,0x1c1000e0800000000,0x406080010000080,0x41000000200000000000,0x100020404,0xa080010002000040,0x40028200330a10000241,0x2a08601210209042a0,0x80801050e0a086022101,0x422106012420c8408141,0xc0442402142c2824207,0xa081814002160881830,0x38280040a08025040c08,0x200c25038802040e0858,0x1028205040e08007040a,0x2400605010003010200,0x101020204000020191,0x100810004080810002,0x2040200080000200002,0x50800352c00200020000,0x400080010000000,0x200065041a00,0x8820800004001000000,0x10001102000010000000,0x800104001800200000a,0x4152820004000000020,0x410000002008810182,0x40208000001000000,0x802204001800201,0x46a208040820d5284000,0x40000008301040000008,0x64a08041001a0,0x83410000000a82029410,0x1aa5081807080a08881,0x120801504120c94102,0x82001c1002a0c9411101,0x42048182028208141068,0x2000000000000000c104,0x8084010002000410,0x28208401000058200040,0x7838208020b041e0800,0x10002003810008303400,0x40c080c1060c08181000,0x802060c021004,0x1002008000042c158306,0x16040008081000201048,0x2400800000080002c100,0x282000010000004080,0x40008000040008000,0xc1000000200003040a0,0x8000005040000a080001,0x41208201048008141000,0x282000000030c001000,0x410002000c10782000,0x1000200000000040000,0x20304000800014100000,0x8101000a080010002,0x80030c0210041000002,0x40890101860108009018,0x2618206040c083244100,0x10400006080000030c0,0x41000004100000009848,0x20000230c04188982100,0x81010203010404018083,0x250c041c9703800c000,0x16080c30204000410180,0x82018381040010602080,0x8820010101020d04,0xa080c10002083410000,0x8204040008141030341,0x40000c08001070a0e14,0x1030a0e141000020c081,0x41000a08001040000110,0x20014152820001504008,0x3060420050b0a010802,0x8141008200081000422,0x40c28215044415080c2,0x82050400302081810302,0x2001400200080,0x40a08125040000a0804,0x1000205044408080042e,0x8000015040800300040,0xe060a4480082f2209060,0x50402080410282050400,0x8000141090385044401,0x80a088b021604111204,0x20282000404082050400,0x8ae4a100000150400a8,0x2150400a834104001000,0x81415102050500081250,0x40a081a03000c0e08141,0x2830003040304000000,0x80010082058004000406,0x8041000078200101208,0x20000100820c001028a0]) else (word80 [0x10200000,0x4000000000800404,0x82000010000000004,0x8000003040000000018,0xa081410000c021904301,0x7082a085810a82070400,0x8200,0x4000020800d0504c004,0x6282000001400400020,0x80a104043314260020b,0x5084005a801054461000,0xc02102c105820b0,0x68a10080028008581a00,0x340040a08185040a0814,0x42008000041018042a,0x200001001a00215908,0x400016070a0858100000,0x80000000010,0xe08000081038])))))
def g237H6 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x1401e905a827dc813c28,0xa9057414610c5c2b0000,0x2a2344010000,0x3048c0001c09,0xa00bc0000819c0000c12,0xc00000000000189f8000,0x2008b812348db888,0xfc245015800000000000,0x4270000081a,0xe9cf4000041f00000000,0x1812ad0d85c0c0000000,0x1e9c00a81fc000,0x40f,0xa9ce48214000090b281b,0x6804ac47519270464000,0x1003d202c000309f74c9,0x300b2c0c0c1e,0x742a800ac00001184000,0x142310014cc9fc11,0x4000081a800008033c1e,0xc0003416800020201c89,0xa419b44688280423f503,0xb203f8888000214cb10e,0xf8079511281348025c04,0xcc1cf417909c101ddc23,0x40000485082b5cc77417,0x284acc267417d4052411,0x9605a04b4c0700001425,0x4096ec07fc8a5884008a,0x4210000340866078525,0xb40804150c1040000046,0x2824c0003c0ef1824000,0x141f980b988cf80e4000,0xdcf9c8008075c05c000,0x141600002d806413,0x30df800018125501b500,0x9dcf20166c0e00002013,0xbc0cc0000000101cb41e,0x2c489420ec01,0x800000003815601b9429,0xc0001d234000380a3419,0x182a3502800000000455,0x4c80c06192a601f4656,0x4818b409702438844000,0x2810904a9c0eb84b2044,0x7a1ac000000000000000,0x28961180c8054c28c000,0x3912c088512a00003422,0xd418e8895c6825014000,0x1410cb81a4,0x7d022c54a444e510300a,0x80002806480f4019780d,0xec06c000380b600d4000,0x944185ac0000d424000,0x1503c00008c8e411d42a,0x5d1970258000241dac08,0xc00024c4400039193c26,0x8487b90365079c2271c2,0x4000000000000000180d,0x140a4026000000000000,0x250e80002414,0xb8248000351a00001825,0xdc16e8c8b00680174000,0x44e0000201d7421,0x80000000000000000c22,0x8000000014424000082a,0xc000091880001829b81d,0x15030000000030279404,0x544aa136c2238524c27,0x6489c00f3510c0003c15,0xc00000000000101a0000,0x341c20c98413c0000000,0x300c400039cfc0000000,0x112440003854c0000d02,0x44112025000014046911,0x40000000340200000145,0x1e006845d4003cd4ac00,0xfd82f420440fc0292020,0xa0c7f81824df4c23992a,0x80002c26c8004887d80c,0xb40290037c14c0003010,0xe11a541bfdce80003655,0xf918d0964c09e129f513,0x348c4000000000000000,0x8487c869421dd249e13,0xd01c000,0x1144e41a400000000000,0x248480000000,0x81c400025104000,0xc02c00000826100541b,0x18295410140d9405b403,0xb82860091dc11818551a,0xc000010051001461c604,0x14018904c10703a1402,0x4500102b1430cb044082,0x826000c94ce50000304,0x30481c60080400032c22,0x854450412040cd980283])
def g237D7 (j : Nat) : Nat := if 9 ≤ j then 0 else (if j<4 then (if j<2 then (if j<1 then (word80 [0x33eb2aa6,0x106be6454c20d7ac8a98,0x41b758d53082fdb82a61,0x6f75398420deaa73084,0x1bd9d5610837abaac210,0x6f75358420deaa6b0841,0x3f5db510833eb2ea2106,0xde63d4420dbac7a8841b,0xd587510827fbb2a2104f,0xd7654420cfacaa8841b7,0x98d510836eb1aa2106f5,0x61544209fee8b2c213fd,0xcd658427fb92cb086be7,0x559210d7aeab2421af5c,0xd648435eb8ac9084fd76,0xd5210d7ac9aa4217e5c3,0x548427fbb2a9084fd765,0x5210d7ac8aa4213f5db5,0x38433eb2ea7086be64d4,0xe10d7ac9a9c217e5c353,0x8427fbb2a7084fd7654e,0x10cfacaa9c21af991538,0x435eb22a7086dd6354e1,0x9faeda94219f5975284,0x35f326a5086bd64d4a10,0xbf2e1a94213fdd952842,0x7ebb2a50867d6554a10d,0x7cc8a9421af591528437,0x6b12a5085fb7054a10cf,0xacba8c21af993518435e,0xb26a3085f970d4610cfa,0xcaa8c21af991518435eb,0x22a3085fb7054610d7ac,0x8a0c21bedd950842fdba,0x2a1086f96454210bf6e6,0xa8421be58d50843bda9a,0xa1087795354210df2c4a,0x8421ded4950843bca92a,0x1085f9754c210df2ca98,0x421f654d30842fcbae41,0x87e952c82109fae5b2a,0x213fdcd654436fb9aca8,0x86dc73595109fee4b2a2,0x13fdc1654437db82ca88,0x5df73595109faebb1a21,0x3f5cb634427ebb6a6886,0x7d65d4d10dbec7a9a217,0xe5c3534427fbb2a6884f,0xd7654d10cfacaa9a21b7,0x58d534427ebaec4884fd,0x74d8910bbae7312213fd,0xd5624427fb9ac4884fd7,0x6d4910beae3a92217e5c,0x3524427ebb4a4885f571,0x949109feeca92213f5d9,0x52442fdb82a4884fd761,0x4910b7ce8292216f5d05,0x2442eeb98a4885f57114,0x910bf2e0292213f5da42,0x442fab8c84884fd76109,0x10afcea212215f5d4424,0x42eeb9884885f9701091,0x9faed192217d5c63244,0x27ebb264885fb704c910,0xbeae3a82217e5d650442,0xfcba4a0886f96494110d,0xf2c5282217edd1504437,0xdb22a0886f96454110bf,0x6e6a8221bed8d504437c,0xb1aa08877b5354110ef2,0xa6a8221bed89504437cb,0x12a08877b5254110ef2a,0x4a8221fcdc550443f838,0xaa0887f25154110fe2a2,0xa82213f5d950442fbb8a,0xa0885dd73d0110beae3a,0x2217e5d6404437cb2c8,0x885f97490110df2c520,0x221fc546404437db2a80,0x886f96550110df6c4a02,0x21fc94540443f8a8a808,0x87f22150110fe242a022,0x17e5d6304437cb2c6088,0x5f9748c110fe2a318221,0xfc48630442fcbaa60886,0xf9654c110bf2e898221f,0x654d30443ec99260887f,0x1514c110fe242982217e,0x5d720442fcb9e40887e9,0x52c8110fd26590221fc5,0x4720443f898e40885f57,0x1c81109faec902217e5d,0x420443f8a8840884ff73,0x594109fee4b28213f5db,0x530433eb2ea6084ff765,0x4c109faeca98219f5955,0x30436eb1aa6084fd76d4,0x810cfacba90213fdd952,0x427ebb2a40867d65548,0x10ddac4a9021da549504,0x835cb22a1084df735951,0xaf2ea102216e5d02044,0x2ecb9840887e12108110]) else (word80 [0xff4a8a8,0x221fe55150443fdb9aa0,0x887f97354110ff2a6a82,0x21fed0d50443fca1aa08,0x87fb7254110ff4e4a822,0x1fe5c950443fc392a088,0x7fa6254110ff2c4a8221,0xfe94950443fca92a0887,0xfb4254110ff484a8221f,0xe50950443fc212a0887f,0xa3254110ff264a8221fe,0xdc550443fcb8aa0886fd,0x6554110bfee8a8221bf5,0x9150442ffb92a0886fd6,0x254110efea4a8221df54,0x950443faa8aa0885fd75,0xd0110dfacba0221ef553,0x40443faa8e80887f950d,0x110ff6a920221fe5524,0x443fda9480887f95290,0x110ff4caa0221fe59540,0x443fcb1280887fb52501,0x10ff2a4a0221fe4c9404,0x43fcb8a80887fb515011,0xff2a2a0221bf5954044,0x3faa8a80887fb5050110,0xff2a0a0221fed5230443,0xfcaa460887fb528c110f,0xf2a518221fed5130443f,0xcaa260887fb524c110ff,0x2a498221fe50930443fd,0x32e40887f965c8110ff6,0xa790221fe54f20442feb,0xae40886fd65c8110fdaa,0x590221fd54720443fda8,0x640887f950c8110bfaea,0x90221bf59520443f6a92,0x40887f55148110ff2a09,0x221bf5cd650437eb92c,0xa086fd7654c10dfacaa9,0x821bf5d9520437eb2aa4,0x84ff7458b509fee6b16,0xa13fdc562d427fba2c3a,0x84ff73587509fee4b0ea,0x13f5d3625427eb9ec4a8,0x4fd71d8950ddec5312a1,0x6f9d062542deba0c4a85,0xde7318950bbae6312a1b,0xb58862542fb388c4a85f,0x57118950afae7a92a15f,0x5d65254377b14a4a85f9,0x7094950ef6e0a92a1de1,0xc152542fdb82a4a84fd7,0x4d85509fae7b0aa19fd4,0xf615433ea9ec2a84fd72,0xd8550bdce530aa17b5ca,0x615437bb0cc2a85df735,0x8550bb8e6b0aa1bd5846,0x15437bb0ca2a85f97094,0x550bf6e0a8aa1bb5c562,0x1437aba2c2286f572584,0x509fee8b2c413fdcd658,0x827fb8acb104fd76d522,0xbf2e1aa4413fdd95488,0x27ebb2a9106bd6455220,0xbdee4aa4413f5db53883,0x3eb2ea7105f970d4e209,0xfeeca9c413f5d9538833,0xeb2aa7106dd6354e20cf,0xacba94417e5c3528833e,0xb2aa5105fb7054a209fa,0xeda8c417e5c3518827fb,0xb2a3104fd7654620deac,0x2a8c41bedd950882fdba,0x2a1106f96454220df2c6,0xa8441ded4d50883bca9a,0xa11077b5254220ef2a4a,0x8441be585508827eb8ec,0xa904ff73595209fee2b2,0xa413fdc1654837db82ca,0x904fd75d8d209fae3b1a,0x413f5db53482f6b96a69,0x5f970d4d209feeca9a4,0x13f5d7614827ebb6a290,0x5f970d45209faed28a41,0x3fdd9514827ebb0a2905,0xdd7314520bf2e028a413,0xf5da31482f6b96a0905f,0x97594120bf6e8a8241be,0xd91504837db1aa09077b,0x5354120ef2a6a8241fad,0xc950483f4392a09077b5,0x254120fd4a4a8241fa54,0x9504837db0aa0904fd76,0x54120bdee4a8241db549,0x504833fb9aca1067d735,0x9420cfee2b28419f5c56,0x50827fb9aca104ff7159,0x420dbceab1841b75d563,0x836eba2c6104fd76d4c,0x20cfacba9841af993530,0x835eb26a6106dd63d4c2,0x9feeca98413f5d95308])) else (if j<3 then (word80 [0x82ffbb2a,0x2906fe7654520bfaeca8,0xa41bf5d9514837fb2aa2,0x906fd6554520bfee6a8a,0x41bfd8d51483bfa9aa29,0x77d5354520dfec2a8a4,0x1fd98551483fab0aa290,0x5ff7054520bfaec28a41,0x7f5d6314837eb2c62907,0xf5518c520dfaca98a417,0xf5c750483fca8ca0907f,0xb7454120ff2e8a8241fe,0x55150483fdb9aa0907f9,0x7354120ff2a6a8241fed,0xc950483fcb92a0907fb7,0x154120ff4e2a8241fe5c,0x550483fc38aa0907fa61,0x54120ff2c2a8241fe945,0x50483fca8aa0907fa415,0x4120ff282a8241fe8c55,0x483fc98aa0906fd6554,0x120fdaa4a82417fdc550,0x4837eb9aca106fd71594,0x20bfae9a9841bf593530,0x837ebb2a6106fd6554c2,0xbfee8a9841bf5915308,0x3fdb82a6106fd7654420,0xdfacaa8841bf5d165843,0x7eb9acb086fd7259610d,0xfae2b2c217f5cf54842f,0xeb8ea9086fd7655210df,0xacaaa4217fdcd54842ff,0xb8aa9087f97055210dfe,0xa8b1c21bf55163842feb,0xa6a7086fd64d4e10dfae,0xca9c21bf59553842ffba,0x2a7086fd6454e10ff2e0,0xa9c217f5c7528437ebb2,0xa5086fd6554a10bfee2a,0x9421fedc1528437fa92c,0x3085fd74d4610dfac9a8,0xc21df55351842feb96a3,0x86fd62d4610dfacaa8c,0x217fdd1518437eb22a30,0x877f5454610efaa8a8c2,0x17fdc9518437eb12a308,0x5fd7550610dfacaa0c21,0xef55141843faa8a83087,0xf97454210ff2a8a8421f,0xe5cd50843fca9aa1087f,0x97254210ff2a4a8421fe,0x5c550843fca8aa1087f9,0x4154210ff6a898421fe5,0x5130842feb94ca886ff7,0x359510dfae6b2a21bfdc,0x9654437f392ca886fd72,0x59510df8e4b2a21bfdc1,0x65443efb9aca885ff725,0x9510ff6e0b2a217f5cb5,0x34437ebb2a6886fd6554,0xd10bfee4a9a21fe5c153,0x442febacc4886fd65989,0x10dfeeab1221bf9d5624,0x437ebaac4886fc755891,0xdfee6b1221bf5cd6244,0x2ffbaac4886fe6558910,0xdfacab12217fdd162443,0x7eb22c4885fd76d4910b,0xfae9a9221bfd93524437,0xeb26a4885fd73d4910df,0xec7a9221bf58f524437f,0xb16a4885fd71d4910bfa,0xe1a92217f5da52442feb,0xaca4886ff6594910dfac,0xb29221fb58a52442ffbb,0x2a4886fe7654910bfaec,0xa9221bf5d9524437fb2a,0xa4886fd6554910bfee8a,0x9221bfd91524437eb22a,0x48877f5454910efaa8a9,0x2217fdcd524437fb1aa4,0x886fd6354910dfec4a92,0x21fb98952443f6b12a48,0x85ff7154910fece2a922,0x1fd5c552442ffb82a488,0x7fb7054910ff0e0a9221,0x7f5d852442febb484885,0xfd7590910dfecb21221b,0xf59642443f6a9484885f,0xd7650910bfaeaa1221bf,0xd95424437eb2a84886ff,0x6350910dfac6a1221fb5,0x4942442febb084885fd7,0x510910dfeca21221bf59,0x442442febac64886fd65,0x8c910fdaa519221bf595,0x324437eb2264885fd74d,0x4110dfac9a82217f5cb5,0x4437eb16a08877d52d4,0x110ff2a928221fe54a50,0x443fdba2a0887fa74541,0x10ff2e8a8221fe1d1504,0x43fd322a0887f9645411]) else (word80 [0x6030be0,0x17742e505bb0b5016542,0xc1056f0ab8152429b052,0x30a2013f427504df09a0,0x1304257049b091011e42,0x35045f08a01104219041,0xf08180fc41f103d30778,0xe841c5037b06d00d641,0xa5033b06600c84187030,0x305e00b9416b02c30570,0xa94149028704f809a41,0x2d024b048008b4111020,0xf03f807a40ed01c70370,0x6940c9018702f005940,0xad014b027804a408d010,0xb020003c407100d30180,0x2b404f008b00f001940,0x2500370058008400b000,0xb0000dfae8b16a1bf5cd,0x62d437f38ac5a86fd715,0x8b50dfae0b16a1bf9d16,0x1d437eba2c3a86fd7358,0x750dfce4b0ea1bf5c961,0xd437eb82c3a86fd74d89,0x50dfae7b12a1bf9c7625,0x437eb8ec4a85fd74d895,0xbfae7b12a17f5c76254,0x2feb8cc4a85ff7458950,0xbfee6b12a1bfd8d62543,0x7eb1ac4a85ff7158950f,0xf6e0b12a17f5c462543b,0xeb1ea4a877d62d4950bf,0xae3292a1df1d952543bf,0xb1aa4a877d6354950efe,0xe0a92a1df5c1525437fb,0x1aa4a85ff7054950dfce,0x9b0aa1bf5d3615437eb9,0xec2a86fd53d8550dfce5,0xb0aa1bf5cb615437f296,0xc2a86fd52d8550bfae9b,0xaa17f5cf615437eb1ec,0x2a877d53d8550bfae5b0,0xaa1bf98b615437eb16c2,0xa877d52d8550bfae930a,0xa1bfd9261542feb94c2a,0x86ff6298550dfac530aa,0x1dfd4a61543bea94c2a8,0x5ff7458550dfec8b0aa1,0xbf991615437eb22c2a85,0xff7358550fbee6b0aa1f,0x71cd615437fb1ac2a86f,0xd6358550efea6b0aa1df,0x54d61542ffb92c2a86ff,0x6258550dfcc4b0aa1bf5,0x89615437e312c2a877f5,0x258550efaa4b0aa1fedc,0x161542feba0c2a86fd64,0x18550bfae430aa1bf588,0x61543bea90c2a85fd749,0x4550dfec928aa17f5ca5,0x15437fb14a2a877d5294,0x550dfec6a8aa1df54d51,0x542ffb92a2a86ff62545,0x50efaa4a8aa17fdc1515,0x437eba2cb106fd735962,0xdfae4b2c41bf5c56588,0x2feb9ea9105fd71d5220,0xdfaecaa441bf59554882,0xffb9aa9107ef7255220b,0xfee2aa441fe5c1548837,0xfaa2c7106fd5458e20bf,0xae9a9c41bf593538837e,0xbb2a7106fd6554e20bfe,0xe8a9c41bf59153882feb,0x8ea5106fd6554a20bfee,0x2a9441bfd51618837eaa,0x2c3106ff5258620dfaa4,0xb0c417f5d3518837eb26,0xa31077d54d4620bfae5a,0x8c41bf58b518837ebb2a,0x3106fd6554620bfee8a8,0xc41bf59151883bfaa2a3,0x1077d5454620bfee4a8c,0x41fe5d150883fcaa2a11,0x7f97354220ff2a6a844,0x1fe5c950883fca92a110,0x7f97154220ff2a2a8441,0x7f5c6654837fb9aca906,0xfd7359520dfee2b2a41b,0xf9c5654837eb8aca906f,0xc7159520dfee0b2a417f,0xdc565483fdb82ca905fd,0x74d4d20bfae3a9a41bf5,0xd9534837eb2aa6905ff7,0x454d20fdae4a9a417fdc,0x553482febacc2906fd65,0x98520bfeeab0a41bf995,0x614837eb2ac2905fd76d,0x4520bfae7a8a41bfd8f5,0x1483bea9ea2906ff61d4,0x520bfae1a8a417f5da51,0x482febaca2906ff65945,0x20dfacb28a41fd586514]))) else (if j<6 then (if j<5 then (word80 [0x95d52b5,0x25634ab095352a125374,0xa589485289250f4a1893,0xf527724df49a8931525b,0x24af4940924524524774,0x8d8918522b244b488890,0xf5219242b48409055205,0x23ff47d88f751e723c34,0x7788ec51cf239347108d,0xd51b5236346b08d351a1,0x233746508c7518723034,0x5f08ba516f22d345888a,0xd5153229f45288a1513d,0x226f44c8894512122334,0x4508865107220343e887,0x950ed21cf438886e50d5,0x219b431885f50b721634,0x2a8851509d212f424884,0x65089210341e8839506b,0x20c7417082b504f20934,0x11081f503b206b40b881,0x35021203340588075007,0x20033ff07fb4ff31fdb3,0xf987f14fdb1fab3f407e,0x54fc51f7b3ee07da4fad,0x1f533e907cf4f991f273,0xe307c14f7f1eef3db87b,0x54f651ebb3d607a84f4b,0x1e8f3d0079c4f311e4b3,0xc8078d4f151e1b3c2078,0x14efd1deb3bc07744ee1,0x1dbf3b687694ecb1d8b3,0xaf875b4ead1d4f3a9074,0xf4e971d1f3a287414e7f,0x1cef39c87344e611cb33,0x9487254e451c7f38e871,0xa4e2b1c4f388870f4e19,0x1c2738307034e011bf73,0x7c86f54ddf1baf37406e,0x54dc51b7f36e06d94dad,0x1b4f36886cd4d931b1b3,0x6206bf4d751adf35986a,0xf4d591aa735386a34d41,0x1a7734d06964d231a373,0x4506854d0319f333c067,0x34cdf19ab33306614cbd,0x196f32b86534c9f192f3,0x2406454c8318fb31e063,0x84c6b18c7317862b4c4d,0x188f310061d4c3318533,0x8860d4c0f181330105f,0xe4bf317db2fa05f14bdd,0x17af2f505e64bc5177b2,0xed85d64ba717432e705c,0xa4b8d170b2df85bb4b73,0x16d72d885ae4b5316972,0xd1059f4b3916672cb859,0x34b2116332c405834afd,0x15e72ba85704ad7159b2,0xb0055c4aaf154b2a7854,0xa4a8d150b29f05394a67,0x14bf29605284a4514772,0x8c05134a211437283850,0x349fd13ef27c84f449e3,0x13bb27584e749c7137f2,0x6e04d749a5133726484c,0x6498312f325c84b74965,0x12bb25584a6494312772,0x4d049649251237245048,0x5490311f323c047348df,0x11b3234846548c311732,0x2c8454489f112f224044,0x1487910e721b04324857,0x109f212041f483710532,0x8840d4813101720103f,0xe47f50fd71f903f047d9,0xfa31f283e147bd0f6b1,0xeb03d147970f1f1e103b,0xe47750ed71d883ad4753,0xe931d0839c472f0e4b1,0xc7038947090dff1bd837,0x646e30db31b4036346bd,0xd6f1ab8352469d0d2b1,0xa30341467b0ce719a833,0x1465b0ca71930322463b,0xc6718b031146190c1f1,0x8182fe45f30bd317802e,0xb45cf0b8b16f02d945a9,0xb4316602c745870afb1,0x5d02b645630ab315482a,0x545430a7714c8294451f,0xa2b143828344fd09eb1,0x3b827444e109af134026,0x444c1096f12c025344a1,0x9331240244448108f31,0x1c0234446108af114022,0x54443087710c82154421,0x83b105820443ff07f30,0xfd01f543e107a70f281e,0x243bb07630ea81d2439f,0x72f0e401c3437b06e30,0xd901ac434f068b0cf819,0xb4331064f0c7818a430b]) else (word80 [0x40c11a5,0x10104440543041811101,0x5410444041511100e94,0x45104040ca5111010144,0x44032512110c9448443a,0x511130e0446944840112,0x11151004485c44415011,0x211105448443a511130e,0x9604444840511120c480,0x444315100a94404c30ca,0x210a5108840543161510,0xe94404c30ca5a210108,0x858403a50d1210105854,0x20115120c27045448422,0x15100c40544431015110,0xc6054404441512110c48,0x54443171512111054444,0x3111008604440311081,0x20c5420484440402100e,0x94100840410043c2c403,0x16150604030218100840,0x58406160a96182650402,0x10104414104041615250,0x402101858549440446a5,0x8548894404040210181,0x1008403251008144020,0x402100c1448403171286,0x111020100c1c18511050,0x41010585410080c94624,0xa2001625145404489440,0x80512111020484430403,0x170c100c222c30112102,0x4894444c12524111304,0x4894444c112251110204,0x89444401122511102014,0x484440812110c1420904,0x44c1252411105c209044,0x4c508241113142090444,0x8051012131420404841,0x1050410104b14ac40416,0x24251010308854404101,0x20814484030510120d90,0x8a001846400151010343,0x181441522100c569440,0x30510085494403182510,0xc548840308060507101,0x85448944250522170612,0x1990185436415100d900,0x28894405010064a20625,0x18585410084052415100,0xe1b14504840d12100e90,0x884031504100c4840213,0x10120c5a88904040c100,0x8590c10184121008304c,0x40316a20c06104840206,0xc3131210543088404151,0x84840216a264101020,0x484031822100c584020c,0x22141010604021412111,0x105a899040408641110,0x1200184c380862b13120,0x184c38086132b105804,0x184c4131008204840308,0x51012104c4021613100,0xc4450543118112151094,0x504432514110c5044215,0x14110c54504430514110,0xc9445044841125411210,0x45044831541111210544,0x50448405114112100800,0x94144844611151210129,0x6182131008404c213100,0x84c402b5756a72d435a6,0x8b49568f2d135a08b3e5,0x6772cdf59a8b32565f2c,0xaf5940b24563f2c7358d,0xb1756292c4b5878b0b5,0x60f2c135808afe55f52b,0xdb57a0af055d92ba7573,0xae355c12b7756d8ad95,0x5ad2b4f5680acc55912b,0x175610abe55792aeb55b,0x8ab455652abb5560aa95,0x54f2a935508a9e55372a,0x6354b0a9355232a2f545,0xa8655092a0353e8a7a5,0x4ef29cf5388a6e54d529,0x9f5320a6054bd296752b,0x8a5454a129335248a445,0x48528fb51d0a36546528,0xbb5160a285449288750f,0x8a1c542f28535090a0d5,0x413281750109fe53f727,0xe34fa89f253df27af4f4,0x9e453c127734ed09d75,0x3a727434e789cc539327,0x174e109be537526e34da,0x89b2535d26a74d409a55,0x343267b4ce099a532f26,0x534c98991531f262f4c5,0x9875309260b4c0097d5,0x2f725e74bb897452e325,0xbb4b6096852cb258b4b0])) else (if j<7 then (word80 [0x5c188834,0x1150a14402190c854110,0x1a149590425100834309,0x41840625640c64182101,0x508604021825100d9040,0x28106088800543852241,0xc5e141d0442215100c8,0x84094307250806120418,0x8831706222510188a059,0x425810622101a044832,0x52281101096041888425,0x81062b10150421510085,0x8550c1840580060c3600,0x1434215060c201600306,0x8009081a003058008641,0x822510040c1018225241,0xc944022481060c6604,0x901848106088a0418324,0x6085890403072408061,0x88184832206120c5040,0xad2c4c50c06083018216,0xc060c590e001040c060,0x8901820c060830182410,0xc081812241000c241850,0x30981410e04241832281,0x4109120448281220a04a,0xc28141220e0418883178,0x60d0e040830280060c,0x1818122410c95048a044,0x170108590e0008407220,0x60e881c1830607085424,0x2150708542420340150c,0x541c20240150c0c04485,0xc40401111710100c005c,0x40302001610100858404,0x403001610540c044841,0x504011110585418100c0,0x861512110c2090544440,0x81215111314484030812,0x1511105d90443c512100,0xc2048544441815051110,0x5c5414484451512110c5,0x4484430540170c5c1454,0x4844515c3401710640c0,0x83054515040210105440,0x21510085c541c100c046,0xc510120c342314404151,0xb144020fc510111058,0x40215100b08544031540,0x160e14484031285100e1,0x44840303011215101044,0x5440404021015100c045,0x44841512080c04644841,0x50301121016844838c04,0x1044544041125100c405,0x44430410181110541044,0x4041511100c144440311,0x25120c44544831715111,0x2105c444830402151010,0x8544030402161010541,0x8404c205a41010245c,0x54315120818544831015,0x110c4054443181510111,0x4454483171512111032,0x8544040112110c10044,0x43171507040301180448,0x5c444171108044844305,0x10120c5c549410044461,0x725110c5494443040111,0x18100448443171504030,0x1251808549430513100c,0x100c5832513100c4c944,0x31325100c144c403171,0x22511105448443120448,0x544431512110c5494443,0x1825110c1c5420015110,0xc5448944440005121110,0x480800449451512110c5,0xc5404484451215110c94,0x48443648215101055920,0x84041513100c544c4030,0x482151010404c5436482,0x651011959208404650c8,0x21010110854404a44215,0x1011110a944040c42a51,0x12910a9440404421810,0x1054110840415a442101,0x29511084040ca5421010,0x16910840410c20a0a019,0x450465828014104c4194,0x36513100d92099440465,0x64821010544c40315131,0xd010c4e944a513100e,0x944c403a513100c544c4,0x31513100e95010c4c4a,0x513100c144c403030112,0x15101044544040111121,0x5118d044994465634112,0x119430444040d6512101,0xc0454484a381a51210,0x4544830301191210540,0xc0448405a38112101044,0x544041125100c4695104]) else (if j<8 then (word80 [0xc605440,0x30a80081454403172215,0xe001080416005430d24,0x84810608220c8854222,0x1088814022085884903,0xd4008403c2242108584,0x22386084010a4523401,0x5144011615100c401160,0x6220c2054443210b0884,0x442450b100c584421106,0x8585418324150822160,0x30122150e1410522804,0x103430240150818201c,0x32240150d008a0031523,0x400a104011621070c208,0x9005444022800c560500,0x315420c0c54242171507,0xc542418300180800582,0x15120812090054419000,0x80b00219024100106454,0x4830c05090c250864302,0x19000c143021509080d0,0x5431800086030221001,0x60c5d009438521000c30,0x14183190c060c1418217,0x6080864003050c09101,0x1708141c21543060c0,0x5005431644000c581830,0x38105120484316000855,0x8303191542801024118,0x2508545c1c3022508241,0x82160484582151108441,0x1040411211010c04115,0x708148420704641c207,0x16084411104601c21811,0x8601c21625089404208,0x6250c148422521085c5,0x42180708141c24304141,0xc2021508201820716081,0xc0420701081c20183000,0x1624230c1d110c307250,0x10c1c0421643070c1c8c,0x58381050e04843072105,0xc1c1250807061058082,0x80608581c2030108041,0xa041c58216044854219,0x12086448215110860261,0x50841825110c00550831,0x50708541854208581a14,0x4440785081c942080625,0x7101e08216041e08207,0x82081e0820782085c541,0xc32580081e0214315090,0x8541821402190c329421,0x50909028c5430014180c,0x602430340045418240a1,0x150c54302150908541c2,0x16150906121060003840,0x160c305420440150c64,0x219000864544830c05,0x90c2464219000a94302,0x1509080d005431844000,0xc60243031815090c4c00,0x58315070809005431300,0x170c8900205060864002,0xca5086411300170c150,0x1c31640250d10005838,0x1160c0c1512043448108,0x4e1400307160a1000215,0xd08341450d0854301c3,0x1915800c542428018150,0xc1c11722250c24581830,0x54108003420c09082411,0x72208585440310045409,0x43100b0840082410b08,0x54402a523860c5488210,0x60c5c18310049440218,0x6086040217250840942,0xc3080507061014112100,0x50c20144840410044440,0x20807250c14882102522,0xc204821204588c54319,0x12060c15001832402818,0x5146018206a5081440,0x24105060c00582011508,0x201c21722060c1808243,0x6020c1c182030019042,0x1724230c19110c306020,0x90c180831712060c9100,0x5c1848117084c1131209,0xc5c1830623170c405c2,0x4106050c1810807060c5,0xc002170840061048205c,0x31740010d04008834106,0x220c201c20807085c182,0x20608110e0408422044,0xc482060438182430e083,0x88c183100e084c482080,0x708201c5c1842502100c,0x94110c400851722060c0,0xe0408317220a042c2800,0xb086430183050d085c18,0x2050809081820c19060c]) else (word80 [0x1917,0x120c605c443401708485,0xc5831715070c58119160,0x860584031016085c5821,0x516100c5448215110888,0x5420115110c645448318,0x15110c588c1854421080,0x85c4821711082c542110,0x45c888431715070c2084,0x5431811085c541c30608,0x9005c5431505110c882,0x420517400c545d003151,0x10856090031015081054,0x21510085440215040854,0x28015082200543192415])))))
def g237H7 (j : Nat) : Nat := if 7 ≤ j then 0 else (if j<3 then (if j<1 then (word80 [0xf40767c1,0xc73805d3083400000d03,0x86a05400000000024041,0x480832216940ed1c0072,0x8308a635ca00ec000020,0x4052273c000000000682,0xb3000000a1d68463290c,0xf0000000002486e00000,0xf56c16f88a20c,0x1306082900e400000f0,0x77c64642805d8040f000,0xa0364000000000820a,0x2201c020b20000040171,0xda04159298cb00001c,0x50ec08ba88890000140,0xa51c188981ca0115b004,0x44d021511ba000000000,0x5823523448309c9,0xc213801c2616ec000001,0x1a70000000001e08d8c6,0xde0389f464e80e22c1f,0x98034900001c026dc034,0x2036ca209c063254413c,0x88f892309e4960000002,0x33d80168610a9cc57b81,0x84d110c0000240dec82d,0x23069ee0f97c095d0190,0x40439e46b000000826c0,0xc01b9015888036c0,0x25400002412e181e9705,0x26000000000000000000,0x1c0e50000060417101d0,0x34c8000000000018,0xa3c6110603c44036e82,0x2f5017fa08f0621b6000,0x631a7c054d68b1,0x9410ee03d980189e0d01,0x486210237c24f02463fc,0x4741108054630e05e701,0xd94304dd06776e4fe419,0xa28a9c407b0403aa00f8,0x6406ee081a40a8a414e5,0xb9c1b086ea0dedcd52a9,0x2c5d409264305c1f3800,0x701e2807820009b837,0x55009f009dfc05ee0059,0xe04c8e202b00b380000c,0x3d120df0c8fc4814952,0x35bc0a978853c91a4684,0xc420071a18dfb9cec075,0x92025540ab101d8d0310,0x5a32ec010be,0x881c901e8420c202a82e,0x6f3c0fef021900000000,0x2019280000b0178c204,0x780ec360009010e,0x470107071b003903011d,0x12050001050616160005,0x80801272a010307050a,0x72b22070804032f0203,0x12000070a2b0f0c0e07,0x1005700071401000800,0x11701064a0f00000e04,0x1b13360c343507420200,0x8035942045c002e0204,0x303030214114b0e0d00,0xa0a0104081a021b2501,0x225070b000000042501,0xa014407103602000603,0x1700190907000a011c02,0x3020b0a050830010003,0x3000c0a002113050006,0x12000108020502260203,0x2a000206000300031501,0x2b003c000200353e0003,0xd92000140001000f0120,0x1f03020d0205000a0405,0x1007030401001a03071f,0x41c110b0f01072f0305,0xe000400000504002709,0x19011905020200060002,0x70b15010e01011c04,0x110007010407080e0c06,0x901170e130101080001,0x200131801000518,0x80104030003100002,0x1a011702151f03010715,0x3e0605040102030401,0x308000f073f02000204,0x101040200000c8d00,0x2020106020d1b020505,0x19082615020600060800,0x2000a05000301022603,0x20112140c000d000508,0x20150607020004040300,0x63800000b0016090d01,0x400001b01000d040012,0x2b0503000d00010608,0xe04060c130e000d0106,0x61a1107080b01190101,0x3030034000105090d,0x1a2500010001000807,0xd0804010105000402]) else (if j<2 then (word80 [0xa180b500,0xa1186000008c84b81,0xe3e07b5c060800001002,0x39216a60fd55ca100000,0x65104810e0000040017b,0x1500a426c0d11c098654,0xb12220a41cf7804d052,0xebc06cc00fc800000000,0xd1800000000072173,0xe02e4000000000c40df2,0x4263006380000404da00,0x239b600001801,0x4000078097000010a20,0x4c1ef1030c2422180ee9,0x40b90000000000008590,0xd7c98bc0000000001d1,0x28000000000e9053c0d,0x3321569133340b2ac457,0x5f510800003c10a8,0xe2021e235694c000,0x1770061e000039ce0403,0x6e80066288c7618d718c,0xa701bc0000000003b933,0x1a024f81d00,0x7ffce4b9d56b2801a24,0x62f68180000000000470,0xac40980c1dda122d0000,0x2226481b9a804cb020e,0x4015dc01c21bba80370b,0x2510a13aa009e576ebe6,0x61f80adfb079306a1e23,0x2c9c9b800001209e406c,0x28cceb931c610f600003,0x1a22a30000001423e98,0x15c800000000040fc080,0xde6880e140da00000017,0xe800009004868cc788ab,0x88b8900bd00eba01384,0x842800000087a1412598,0x22d6260a46368032283,0x976977664456c03e0000,0x140998c18d090d0,0x14642008ce800000,0x2e073c821289,0x2872064909a300000000,0x1c446882105a03e9083,0xa047c7c060800003110a,0x2cc63412930258d00ec4,0xf7e80438000000001ce,0x4d800000000070430000,0x20071610995057620f3,0x4815180000505008234b,0x14404439050272000028,0x6e00000000000000148,0x7200000c665c0000184b,0xe381cd205bb600340145,0xc02c0404f020ae841818,0x8110600002c0c700,0x224bee08b55004781,0x3de0717c0af304799006,0x93008c0000101cd80000,0x6032a00000000000000c,0x310aeecb8d8ad3836fa0,0x5a1206c400000a883e23,0x56000000000000005085,0xc00003485fc801ed3190,0x6a5dd005160257905d0a,0x49878182a8110e132600,0x8040000783a931350288,0x6e615400000f04a2e007,0x440cf80000a07afe105a,0xc21ff023a5022d80d8ac,0x219000005049c0000380,0x80d11f6a028200001003,0x50030ac479300d580000,0x1020d5030681093814cc,0x8187c648800000887380,0x14635c0000600,0x120000000002018e8000,0xe114760b540000798b3,0xc031ea43450145184026,0x213520058d1930000020,0x3f126a98000000000007,0x31e0b052036f10831020,0x7a4330d01d101f67065c,0x2046f00000b5617e,0x68898086139387044ec6,0x300809e188ba305ee600,0x1281886812d5077f410d,0x7c05638bf83073be8e60,0xc0cbb832100000ce6c8c,0x16c2a03200028e01e681,0xc0e90e5a4345c0b1f91b,0x700000b0005a0cb2a436,0xc03eac108400001,0x50000006640bc0bb30,0x298f1228325e7c0f78c9,0xba932ba0226a817a510b,0x1505c800001c0f6b8377,0x9649c606b44c87502db0,0x5ce4d0a880d7d2,0x1c5203c88857b0161700,0xf04107815e72026bf029]) else (word80 [0xce431320,0x1e412800000000070,0x482000008479600be000,0xc0eb5818cd00fb2065,0xf40168c20a2818920358,0x3c0e2000002221cc,0x23c6c004a01c500001c0,0xa1440328a332701b6644,0x8a80b4500c3a079060c3,0x6802b003dd3406800003,0x21a0a83d0001f4c0bfac,0x141883f9f463e0000149,0x32ac8856251400003811,0x160221023a8000000000,7,0x8130f005f501b0000000,0x1ccd53c19fa82,0xcc000000000000000003,0x18447600003806a80000,0x1c45f00000610bd0,0x12623088241821e88,0x43200000000000000000,0x180d68000000000302e,0x3607c6dd1380000d0247,0x98c00000000000001a,0xd0b405748042d00c400,0x2c84380000e206e000,0x3020978441f43d60000,0x2087d0000088141,0xc1e2d034544639443640,0x22b66000000000194,0x3a00000704a660aa8000,0x103840231588dc40000,0x30431000000000142206,0x90c8006bfea244000028,0xa1590140e223a819cea2,0x380000081045a4a2b835,0xd906600000100537013f,0x8014e00afc01cf928922,0x34702328000000000a0,0x3aa610e4000070248605,0xdce008041729810b7824,0x4103b017900000752ed,0xa0d9cc105f910c000004,0x8468955098cf226ae60,0xc900000000007085e000,0x38219a434391343e048,0x5c0a8a39d0102b000003,0x1117403b1f7272283b34,0x1a98162c015560dc040,0xddba350721f120554c59,0xe08a192083924a9e812c,0x900d6502cce021241aa3,0x2978504df4018e980818,0xa1a013fa22d848a2383,0x1e0000000000000000b3,0x6221956a227803d80000,0x980c8b2edf412f800000,0xd6448e740152d2,0x1aa4a243019480000000,0x8491fcd0e6110b523f,0x8c0127d9e70000024087,0xc059301bc80000106c6e,0x10630837582a70000000,0x2883b00000540b8a0e,0x34000000000000016464,0x4810de80fd0000000000,0x302de9482bc0f99c,0x16490093d440d086b3c0,0xeb700f0b31a2e8c8f81a,0x9025a504aba0bb7c85f,0x81aa4038680ea84058b,0x3a780266000f4402190,0x8eff222748105807bb02,0xe1904f2c02ce01e50814,0xe505d3a02274d413838f,0x273f3ee5000000583cc0,0xc0cfbc1e5b02e2e0,0x72dc816a495180000000,0x100891482ea842dc042,0x9c03af41c2e211700000,0x40645011fb056c0,0x9175b041920,0xa20601a3029730097502,0x5e0111e80f8d10fc0000,0x200b5a0008e6094081ba,0x8475000006727520ca98,0x43613ca3053a0000000,0xc040400001c04,0x8a02ce00000000000000,0x2925e004f800002c1c85,0xe0621560905e8805c0,0x131b422a0000384cd000,0x3050244a0800005126,0xc403002064741dca01ee,0xf01a2000028cd40098a7,0x50120000080bd5395042,0x23f60d2d090480000a01,0x800000342099894e0000,0xcc06840000790de6709c,0x80be8c157180c6000006,0x220000000000684d340,0x42ac5fab022600001685]))) else (if j<5 then (if j<4 then (word80 [0xe870524,0x81040c09a8040a831736,0xc1041d2510c94224328,0x16e80f9681ce11325843,0x85248071d02d9c0c7,0xec0360a04f2427c208a6,0xc039810c6c40bc623088,0x177c08a7b00db26412c1,0xfee004ec469f88144047,0x4a8a9a1237dcecd39ce9,0xa83534367a008fc407fd,0x317f203e7408ef208c01,0x188631a6400d3c200f83,0xc6305b9e090240a45043,0xee2022a43098821e88e7,0x40727c0a46c1f700000b,0x76a40fca94bef81d306,0x34be022e40dab040bd03,0x4be4a9b80db00318304a,0xc20c5540e78820fb406c,0x80da98ca8e03ef622060,0x20831800009005600,0x24454f88eb00000000,0x28cc458358324e66228,0x3844c000000000180820,0x2186c446a72076e0,0x833000001049b210ecc1,0x3f832d701a7680f0000,0x1c90480000,0x7023ce025e00000c0590,0x807a00000c0c2408e299,0xbb3802980000348fa800,0x6f9008904136d4bf4112,0x1c0cf00000,0x208190441dc829d82a1c,0x714405f41cd8a81a030,0x6364100c00b680000510,0x1a0000148280017be40c,0x20000350f6188a140534,0x101ac0000000005230fc,0x3f41f480000424e9e0,0x61400003034e00000000,0x382ec006c28266,0x341583828600001849e9,0x9c988000000000c07740,0x60989800aa000030c,0x9f00000824f36032d41e,0xa81ff00000000024023,0xdb243332020000000000,0x2024e01f300618000000,0,0x320e8408a2c1c3d317,0xc546b480086c46be02b5,0x349c63114052602c60,0x11540000340e90000000,0xe10f0005af990ab42,0x3e00000c16b9b04be279,0xa641c744523831c92286,0x8a0400ddf802da5023ae,0x64dc950b80cfa0375a8,0x2d50449583d3640a4008,0x16011a10426773680000,0x1cc6a00000703b800000,0x5003100c9000018412e4,0x44fd02bd2024e409fe80,0xa580000a320c00000000,0xb40582858c0000,0x299f5000012445c00002,0x80030048c00000000000,0x8049e00000488a000,0x942abc06a400002924,0xa3737568c69813b6911e,0x402ea2498a510bd03914,0x3f4602be4c5ec837891,0x17242cfc0000702ade03,0x56c012000a8000000000,0x86ec9c17000000b0150,0x1c0cd00000602bb4,0x4e6948c588328f007350,0x1a9c013582abc06db000,0x60881a202d9c6099a070,0x281e1790e9c07f6a44e9,0xc183e01dff24eec0c8f1,0xce2b39fab048e7025b84,0xc60a005a051282304411,0xcc003f7067800001407a,0x3815e000002075c04a9a,0x91aa000012c538000068,0x4a323ab40368c008000,0xf045680c5b8934bb85,0x5324a2cc154920c80000,0x506400000000006aa800,0x14085c00005c11490,0x67b403d8000000000004,0x99e0dc80d51d808d145a,0x2e097b80c61895df46d9,0x204161104a18de2053e0,0x2001600,0x2b700000803,0x9400000000000000ea1c,0xc00001233400001602fc,0x602456021a000000,0x15a3033a000038c]) else (word80 [0x7e22e71,0x801417aa7f842d200003,0x488c502cf00000000000,0x582a8000000000000,0x2c04,0x84825d00000000000000,0x182cb00001c076a404a6,0x80e3e07458040800003c,0x115d241e20f3d41e4800,0x40a3000000000,0x148778000022112,0x642cfc00b3c9e7730570,0x2f8e0,0x2e0204c8000068025000,0x15c9d8108e101f,0x884670c9260000054047,0x6306445400000e22330,0x8530000004bb80000006,0x3180000408c7995c7200,0x7c000000000f04b60000,0x1cc7ff811a0000160e98,0x38,0x132800000000160115c5,0x9618d63000e609a0406,0x100000e02854ad87cc66,0x803ea40699e08f9c06c0,0x26900001c10a4000038,0x1f74086c00002d02c882,0xc5022760000341c1c80e,0x64077ae0baadcd380000,0x240ef02413a,0x43c1449bd88bcd00cd31,0x14ca2270017db811ce01,0x2c0000380a332004d07a,0x400001886eb8295424c8,0x4098a9022e2374006740,0x3415000000305e600,0x181edb923e4227004b,0x10407aeb93596229842f,0x10ac00000b07c5004b8,0xc171e0040d032c000f89,0x44380000000000ace800,0xa0019a05bd901,0xfd008ce07a8702d70468,0xca164a02c0e01d3885d6,0x824a05484807d088c700,0xc4222c0ede90f2800,0x7206a0000000000000,0x32ee800004b932,0x200320000000000a1e90,0x466004f2c61a5d013a00,0x160fa301b5e3824943,0xce0000000000198ca069,0x4a032848248000000000,0x303fe000000,0x301be00,0x12c9,0x240000680a5451158227,0x40000000000000000002,0x415c2297c540242c8800,0x610e3b32078079240,0x1380000e040800000000,0x1428900000,0x518cec04e8642edd0f22,0x2fcf0719a099fc01860,0x364603a3ec1c781fb701,0xc60000100f8d00288000,0xa11d8000020927d393d,0x50466c0ab14804d837f0,0xa0,0x42080d54000032346404,0xdc00000c014800009085,0x600df9002fc00d0273e9,0xaa1cb04c2d835be42640,0x2e2042118000070250e4,0x49800001908f00000426,0x5ad0a6f008f00000c047,0xa420f939a6205e08046c,0x2d15052c00001c,0x3bb0200e07700000101,0x9a982f1224ba201fc000,0x4011800001a42a150ed,0x9832b00000c824c00000,0xb02e800000000069,0x2750000180784883a8a0,0x31d05acc8cad01809108,0xc0043e00003c457b88cd,0x3012468d580000000000,0x8054da23530,0x7ac8265d883900000443,0xb8605f08221000000000,0x14027501fe4028d20146,0x2813d2008e921c28,0x4ed01077c2bc0000000,0x100c320c,0xdc51b9139f3d116824f3,0x201e8e8a7f2074200003,0x41f080000703a9ca22fc,0x87e710ea200b6006c9c1,0x83708f9c00cc00000000,0x603b0b0212e0d5c59b0,0x7010ff81290431d01ae6,0x275902b2a055d084a11])) else (if j<6 then (word80 [0x2841c,0xab80f300000442cdc072,0x306a3aa936409c7,0x209600000a0e8ec09b50,0x88d801dfa0e02487b383,0x7400000046ec08d09b93,0xc973a2000010185f8369,0xc07f34039684156,0x2bfa09cc00000000032,0x45e00003c0bc0120ce10,0xf8000000000000004033,0x7a44140000403bc702d3,0xca9f4c1350335f840d00,0x4a3330000104,0x38000002837a00001a40,0xe0000000000000014a21,0x801282a32f00001a0d94,0x95100000000030,0x85c00000824b400001c0,0x76a8165584120000201e,0x7000000000180f81990f,0xf2044c0588823dc00000,0xf00ea00000000020,0x42500000a0663c180481,0xea0000120b20c0196016,0xe7408000000c47680000,0xb038ea0e94c09200119b,0x24ab204a642000000000,0x1e42c990f1888f4031,0x764877e8203a0314c055,0x2841b100666a33ea00c0,0x390b35003c9053ce,0x4a8800006029b0000000,0x1902f8000030508000,0x20c661a094000000000,0xd05f2e4927,0xd708000050462000000,0x58331000006868c00,0xa018a00002408,0x4008d600000206f8402e,0x341ea0000281995,0x82716114a0000041a380,0xf468000001c1c9601,0x2600001006640000301a,0x8e055ec21fc0000281e7,0xc1160000034c6ae90395,0x13400000d5d68022500,0xc0570816a00000000,0x8bf1028e0000,0x20ea000002b9b800000,0x608e001f600000711dc6,0x7b1c1b0000007024000,0x81b88822e904938ec,0xc3804e681a2904a8e0d2,0x141d9903b6105d668cb6,0x8189023701132a000009,0xce7f83825317400003d9,0x9ca02c37255a6005600c,0x580000c111820495c832,0xc1670c80b5087be,0x8115d05ce00000c0d3f0,0x99410281802659898b02,0xb4a7666800e800004927,0x681303c07040000383af,0xc067000000000000000d,0x87ac106c00002027de8,0xe10858bc8fa3801b325,0x8cc222b80dfb01120000,0x6a220884439272673b3,0x43b15b100000000004,0x510043c000004739200,0xcce0083101cca7282000,0x2444da90739219cc101,0x6807d6143e00002,0x4181000001026f802af5,0x58163301dc0000110,0x2ee813e00001c24b4000,0x3117a0370c0000341f6,0x983c700000088b400000,0x1e2b064f20d0dd0a428,0x95a00000a0537d04afc0,0x66b0435c08be8074d043,0x44119da0fac0000483c0,0x180b4c8c69401c9b,0x1a80000000001813417,0x36600003c5f900000957,0xde00001c0a9e83a02047,0xac034941308000053171,0xc02de413900000000018,0x153013f242c6f726940,0xc8800000000000000a40,0x300000302c2000000000,0x40d34,0xa05300000e0794c,0x898206000010422900,0xf58a202707c800000046,0x65833600001a00b55909,0x5a3d01070d0a23400006,0x1b44028a00000000009,0x7700001202c00000000,0xb07ee0000000001221,0x400001209eda4bdc8317,0xa825c0000083f44]) else (word80 [0xa0f0f854a,0xd006f64a94c1484,0x926ed045800001c5ef69,0x8c30000000002482f881,0x4700000c8c0550770000,0x2127d20fe800003a1e1,0xa21120000100bfe18764,0x5ec000018c828000014,0x1e9844dc000068242000,0xa01f904911043a073a,0xd00450044f30213a0626,0xcc914000000000203294,0x386c0171828700735e4,0x96414056012cd11ec081,0x9e4035a202ba02fc20d4,0x884afb08bb00000c0a91,0x4c86a0399f22104202f4,0x1b3283f8d005560dd800,0xc02b4811,0x8112a000464a23fa8204,0x781aef0413c0b3400004,0x241a780de610c000004a,0x2cc6061ca0338c173000,0x102002080c4836c824,0x3192f5e44e40c6858081,0xa06bda019ec0ff002be3,0x40d5e8777d0a38000000,0xe8c8640fda0113a00,0xa600003484200000d06f,0xb41088000000000b00b0,0x1887d182f5500a40,0x70bdd001bb40,0x3f820b1a200700000000,0x201ee2022ac02440000,0x2204081260671,0xd02300000373e4000030,0xc83c8028000002228800,0x238570000000002407,0x380326000000000240a5,0x2a1613236b4000400005,0xa8777318f42374c20300,0x10100000014862902,0x445812600001c05b701b,0x900000000000000201cb,0x20738e23674805018c23,0x317dc247390cf8000040,0x3cda0eaf020c80000603,0x1a00228000040104f031,0x5010b000c0e80ba124b9]))))
def g237D8 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then (word80 [0x56122003,0x12901e2a5244048a9491,0x122a5244048a9511220,0x2a52844330141a528446,0x230529210b8504948c12,0x43812e48291142022c14,0x80a44a800a4880c1a292,0x222452440300042922a4,0x462a48291101000a4888,0xa002020a5480c1890522,0x2120a4032200a9220285,0x204830a3089010286244,0x440b08910102922000a9,0x1180a524444029491110,0x291204840a8491110325,0x244440a0092522295260,0x1101428c044040a4c80,0x644015244050a4090614,0x61120205010491114405,0x244040a488002a446184,0x4806484110c2024a4040,0x61012520285284480814,0xa1120205440491014905,0x224c80a8929220205440,0x12901510124404025099,0x2202a2244034404a1120,0x2810040988049900ca00,0x24540911829422185240,0x48880800526405220090,0x52029202002942231124,0x14808080052640526001,0x1010103004c426001101,0x820050404009901098,0x221080a4401220259e6,0xc93620af4d6caadb53da,0x83537693f461a004f427,0x25369995cc0a5972a293,0x5c90a4411f08d946422c,0xf12288042b6109062819,0x4025fa4fa27b23d09e24,0xee2755ba09c88e226f5b,0x709b08d5b695b4259a4c,0x8d635b125824be95d22d,0xed696b145722aed516a6,0x2515a8253ce9c54ce260,0x52a292f47c233d14c876,0x42a20e50127e73df1e38,0xed87513941c34dd66c93,0x5399dccaa63330897bcb,0x9a5a42bd9564a7c51527,0xd136095e48d22e910884,0xe4051ee0ee873036f1a3,0xc905f62d91580a544d8,0x24a11787fc3c81c20cc8,0x5c028011e07a834c1620,0x8f036812c044000ffd89,0x50ff98950ff58950ff18,0x950ff94950ff54950ffd,0x8550ff98550ff58550ff,0x18550ff94550ff54550f,0xfd5220ff55220ffd4e20,0xff54e20ffd4a20ff54a2,0xffd4620ff54620ff995,0x20ff59520ffd4d20ff54,0xd20ff98520ff58520ffd,0x4520ff94520ff54520ff,0x14520ff8c520ff4c520f,0xfd4120ff54120ffd4c20,0xff54c20ffd4420ff5442,0xffd5210ff55210ffd4e,0x10ff54e10ffd4a10ff54,0xa10ffd4610ff54610ff5,0x610ff99510ff59510ff,0xd4d10ff54d10ff98910f,0xf58910ffd4910ff94910,0xff54910ff14910ff9091,0xff50910ff10910ff8c9,0x10ff4c910ffd4110ff54,0x110ffd0110ff50110ffc,0x8110ff48110ffd4c10ff,0x54c10ffd4810ff54810b,0xf58b50bf58750bf59650,0xbf58a50bf58650bfd895,0xdfd4950df54950bfd85,0x50bf58850bf58450bf59,0x620bf59220bf58e20bf5,0x8a20bf58620fe54220bf,0xd9520bf59520bfd8d20b,0xfd8520fe94120fe54120,0xbf59420bf58c20bf5842,0xbf59610bf59210bf58e,0x10bf58a10bf58610fe54,0x210fe4c210fec8210bfd,0x9510bf59510bfd8d10bf,0x58d10bfd8910bf58910f,0xe94110fe54110fe90110,0xfe50110fe8c110fe4c11,0xfec8110fe08110bf594,0x10bf58c10bf58810bb98,0x850bb58850bd98450bd5,0x84509f994209f59420b7,0x98c20b758c20bd98420b,0xd58420af99210af59210]) else (word80 [0x420090,0x5225462a844452444642,0x549452228842140122a4,0x472a860800a4888e08ac,0x1425c012221490a91100,0x205462a9110d111480e9,0x11158a4051a202a44400,0x81520aa445121000a408,0x256224868e1222d0108,0xa6c347050a52431909,0xe0a34294911112114a4,0x530162034894890220a,0x1229490a5e0a54214892,0x1e224849480a5a201489,0x61101cb21249488a8529,0x22224449050a52231888,0xe0a4429489059290242,0x25101891115223890d0c,0x2801d2921d293202012d,0x11243470a025421cb244,0x5293202c54a4c889152c,0x4484480d050924a4452b,0x50804a4888f11203849,0x480c602c406912c22040,0x14a4c808582814a4c80c,0x121a3829490c64243469,0x60921e224229480a602c,0x40691291204412294908,0x5c2824b048921e224109,0x480a5a2014a904052044,0x54a4069214c974889290,0x192224a40488901c2449,0x480e602c407092224a40,0x92e94910112882440447,0xd106824928e19292104,0x45045e1a345052862448,0x82094911152c50c48411,0x192a30d16193243a58a2,0x824223454a8881214a4,0x54a488901a122189480a]))
def g237H8 (j : Nat) : Nat := if 4 ≤ j then 0 else (if j<2 then (if j<1 then (word80 [0xb1d92c89,0xb00e1890618a26600002,0xc206000008a150000040,0xd0f00ac81727036cc2f1,0x281e360a8e00ce00,0xd2614027fd16320b5,0x11c5a70987c05f781ea8,0x1fa5056bc965d20b982f,0xc503bd0113308d6d01ab,0x2253caaa72761427a309,0xa8c2d3b07784aa000000,0xe2005d44179d493c82,0x2e802d8808b455a842d8,0x44a664569476e3c890b6,0x79b1300821c890e5e035,0xec5a89087bc228a01b8c,0x2f8d082742df50240000,0x157f5028700c1fc3002,0x810000000003c0bcd07,0xc2c125f05da0110c1632,0x146f52814969be0612c0,0x874088f82abc05e38279,0xa03b6ca1eb089a0578d5,0x91f8257c360202b86084,0xc831ce07e309f004320c,0x15e005f94072b23e3c1d,0xfa2744404350713c157c,0x27ec4225e03c6515e303,0xed0445b09ca825f60276,0x409220593803f90606c9,0xafb0432c2cf30454c08f,0xc00e9c030b0168499400,0xc60b00001414c6043,0x800000000141dcc04480,0xb6a1cc0711049b925,0x98280101440000300f70,0x50c6801cfc05,0xbc000014098562b00000,0x1dbbf259ad68c54a5501,0x390000314cd000034248,0xf025389db000010e5ee0,0x60e40f300000000070bb,0xc14a0000300b4300b00,0x401e066bcf24b2083,0x7000038a7be0c340000c,0x8000000003527f408,0xc90a7900001915d02634,0x82764525e106b686,0xe72098cc6e1846b0824f,0x30912126c006bdddbf74,0x654028b506e9c06df019,0x84a68c430ec80800002c,0xd800000561100002001,0xab4ac05643707aec131e,0x74305b0521539c5fd00,0xa20031a090c000000000,0x9df8074b00c600001c2,0x5000002004f0032e0a70,0x406ff8689000000000c1,0x6ed4006000000839f110,0xe016b806600000d011e8,0x2a5241800000f5a21409,0x500000c1505013bc6ca0,0x2679442a60b028169706,0xe6829700b9c00009099f,0x28f024485d3f7006c08,0x26000034217502671064,0x12b549eb1300072217,0x2d881e110d00490409d4,0x11c6b8307122f27002e,0x1c0d1501001d07206d05,0x571d0d153203b11f4f00,0x21016020f1315718b03,0xa0276b01120605022281,0x12c20106030a1c017304,0x101382a8625000000,0x3010057104300610003,0x1e0340081507003907,0x31b502504021b4f3c07,0x1300281441002a020100,0x8813550013a211026106,0x8000249020e0179420b,0x125180b1a16b10b0008,0xd011e170000040d0003,0xe530703281501501906,0xd40c19032c400601333a,0x41e0004060c0404261a,0x560112522d051700b652,0x130f10003f041d000414,0x84020406080104000520,0x18021821047037105b02,0x10b0002090b000a0111,0x2068905000c14050501,0x530d0d1bae3c07002406,0x2b021717071d0a08030c,0x4d1b043a04001e0002,0xb01060101010328004a,0x30011060901016a0400,0x1180b1a0e01281d0700,0x3507000012010017090a,0x1000100103018902190b,0x3090209032c01317604,0xb000a0b060103000000]) else (word80 [0xa2283102,0xdaf1a7210ccf00d80000,0xb0703c56a449a25d9391,0x23650d6e5bf380ea0000,0x18211b8a7c509fa09008,0x13fa0bbac005108a9a51,0xf000000000109d5016e0,0x9cc20fa264bc69b309,0x60810d5877f030bd05f1,0xc1fc40a980000a0c1a50,0x81c7643c096a2b21c1d1,0xc69b3442d78a9f004400,0x10241a0a06ae45a1604a,0xe968980c12901f000000,0x64588411d000000e1,0x600001856d000000000d,0x9380000000000000206,0x769a8b20795408d05b7b,0xddebe08a400006348fc6,0xee40c7b003790508c266,0x7771111cae0864000017,0x74c0000932cb025a513c,0x2409300003426ec2b42e,0x6bd000014182f76d8947,0x5020570851e30de457ef,0x3480000176c8407b226,0x711c7b456c42e430b0d,0x2e3b069b896d78741c1,0x5d000015253000000000,0xd368a0008e0a8b5a89a2,0x8182f65323dc29ef003,0x704b03700000803dac,0xe00000802ea224ec0b,0x1f43d3026f109ce42d0f,0x4a240bb4089f431d007,0x9ac18b000000000938d4,0x63aeea0f4e009982,0x2c907cc0000e40744843,0x2075016ca610bac31fd0,0xc09d0c7f27ebc083c06d,0x68214e066941d9000010,0x2050000389b1902a0c4e,0xfb0b97cd72402dfc97b0,0x2c17a51850c974d09,0xa82aaf015fe264e0bd4,0x419fe0acf0171807d0c9,0x5ad04d294257059e1c52,0xc0792844da2893c13c00,0x24bb033383210041,0xd02fdf2088413621113c,0x9620000000008018f819,0x55041b806570c4040ec0,0x417310414876081b660a,0xd2ca03c30c280bf7763c,0x497ea8b3b8613b05b180,0x2950114c1bcd08920062,0xc286cc2b000001d28da0,0xa048470e09700000f056,0x1bd510b3030eb63f54,0xe8208308a4f00000dde,0x8f0716da86f14d4064c7,0x3940000a0c44e0f2209,0x364067d0057c22bb0b49,0xc2c500000004a7017201,0xf21075841bec0c05c042,0x90755c30300b58414fc1,0x757014db435e15fcc07f,0x780cf348a8160ba400e8,0x56ca07de5de18494040a,0x2776ea4484a4621d2644,0x5cf4dd5649fa1d66f01,0xdf02fb71c39d051802e8,0x80ba74000676f654,0xfc909b005a030445c11c,0x515d2c951306dcc10900,0x209a581979c0a5b0bf,0xc9098c07a2481300001c,0x3130000340ad00003c23,0xea0a574293000000000a,0x2ab457d41b7ad4eb000,0x3d27d000025c5420ad8,0xd2609009a100b400,0xb179940e60775fc65f,0x701be4e346022082a700,0x422d366c5424c5764,0x7c1cc5069e8a2563aea5,0x1f3e54d4ddb53021700d,0x9706b8059f309649c576,0x2139ddd2e23d80000501,0xd40000e4405115af082a,0x49a300001da4d60a8300,0xae000034265000000000,0xf014802bbc0645d227d0,0x3c800003059aa27f0000,0x30a75825b801544,0x286000014221f3a74000,0x420d00000d25624a09a,0x50400001472282b5102,0xe64c2e1045b8317a0648,0x4320f14259c1b2384fc8,0x3c3492c01b8c04ee421b,0x325a58119c4a3cc32290,0x75fc701e44e40000f051])) else (if j<3 then (word80 [0xb4ddd4a0,0x91551864262b056ed057,0xe01c90080a42743478dd,0x305a20c544e4508e1897,0x1d0c2809d03457000004,0xb54ca04801500000d05,0x1c00c53063d022060191,0x80dd00003c87ff025d1c,0x50b04b480a9815eec1c1,0x408bc45a7901f58d8130,0x9f840c91212150f0d06b,0x2800b00c67c57f00b989,0x472827fa80b074abd457,0x26590482f20434198196,0x51c70010501410256904,0x7b61e6f432fc9ab320b7,0xc3086520a814010a7f09,0xc220a100000c03bb010b,0xd88684567f02cd021ab4,0x3740000d0c5102a955ac,0xc00007031d89ba641940,0x4d209e0c124b1c2790e,0x7000000000e042b40619,0x35442715065c801c00a,0x47084424c12c16dc0064,0xe0cd98d940798018000,0x50b464069e026cc283,0xc2581c5e9058c74251d0,0x99101cac004840a6d2b1,0x800df60279d1e4a258e4,0x16880918c1053483c023,0xb000030c3860b2281b30,0x301490000001da171,0x60c97fc05ed52892017a,0x52525109491aa1508d52,0xf8025b9a01f000028174,0x307a90a02108c2c0cda1,0xc18247d0b718305e287,0xc12f40091c1a174c1fc,0xbd00002d159965da005,0x1911bcc1627071dc0c0e,0x118000340c63c081000,0x208a039311ade20d6,0xc8290000100e0114dbd8,0xfb101afd00280a00c03d,0x9087d10e8b07a4028200,0x349c30000,0xcaa100000000090afc4,0x879043540000302e0000,0xe0486008ae06c7c1f60,0xd47860de9826,0xe00fef4c0783129074c,0x8215838e5162da02d590,0x61a01a88236005c20049,0x151b94ec0e36ac80ab90,0xa16c15365bd2823ca06a,0x282ea34b45106730a580,0x3364202113bf717a892,0xb820ca9422135c601512,0x421819450585026df09,0xf7ca5090ab9c12010224,0x499ff109c02f40000141,0xfb00fa826be268950f3,0x61b7d80a0b0a700000d0,0xa32008237709947040bd,0xe50695072f827770b12c,0x18ad07e6198f7491b44e,0xb000028a1ff1bd5cd843,0x77821250218c81ae0b,0xa2d1cc508038c2d00001,0x11c970671cea0210cbc6,0xfc4770605a6a386d895e,0x91c17c2e0f03e7cd7760,0x4cc8074110e9c849776c,0xc8e4fd0bc19303b6a2a0,0x14be063919fec0621010,0x211b5090e3b27a84118a,0x94ec255815c70819000,0x14827205540000a0559,0x900ab30d73c003c81,0xe2c0bbe808cd63f80000,0xa00785160c077702a831,0xbe1251676d00000c223,0xfc2bd30088450aa08fd4,0x96a826c801cde89b490d,0x100003959dc09740000b,0x61cd01800a680000943,0x4b9c534050c82fe10b1b,0xd42087a240000f109000,0xa04c3c222c076c0000,0xd09c00000a40580000c0,0x35a4809f0c3140c20000,0x1a263c15cd4845000000,0x8249279842af00000c0d,0x4c0c3dc955000010a72a,0x2b1e48f50000340a4127,0x8405a9802fa42c1e0239,0xe6c1308400000867ef09,0x91953ef805b30a6cd085,0x10d8300121411721,0x22f82b1d0b894315b596,0xc403440760c165041a19,0x48400a65984510107023]) else (word80 [0x3497aa89bc000,0x643e3c1e04143400000,0x688a026904e354fef30,0xb1c18900ae70568b7174,0x81ce0000280d35072142,0xbe806c2c039344f240fc,0x714f940eb443ba031620,0x323c05600000000000a2,0x2813200002c,0x27660709013ec0c6e016,0x3caa32438bd26e9,0x2b261c5950a254135000,0x8122707d4,0x2594449ec0000e0a8790,0xc400286019642986560a,0x908e4c08451224421c02,0x783c268505144a1810a6,0x924c6412f00ac328360,0x5d000020180e15acc2d,0xbd198040a750b2400006,0x19759015e4926c474204,0xa80000c2754e59e9213f,0x89b4b0b76427b9036940,0x1807b3428e457e8457c,0x4083b809cc108fc26250,0x6d040175030fc0f51445,0x810e1503e9824132097c,0x5d00205cd0f1647c8000,0x80b30d05b9068c44361,0xa29c1c3e058cd107600,0xa980af8457c000015424,0x70000038294d2b2c00,0xb0386c9d4a012e41bb,0x380e3a407091dac0,0xe182b2c5a2b420d80bb,0x4c611a06a4c148210c50,0x103710cd159fd0804dc5,0x6f5473097201a780000d,0x8f4148890564dd02803,0x6828d91bd000000162d,0x49a47082c02c20001c00,0x321ee126f2279f898c,0x108dd807ab3608000090,0x1300000805fcc99dd0ba,0xfc0e75207c0000309298,0x3c00001c44e00002469,0xdd4b5d0013727e0c612b,0x456381fe00003c18d221,0x308254400c9c154009f0,0x4104330ac815c91b8142,0x5e109ffc00460a4900ff,0x93aa1c123166cb8846c0,0x3780000c388b8447c054,0xa0579000031226c071a4,0x86200000814ed08c4000,0x64c000000000807c5,0x27fe41ffb698f419b329,0x460014b0037c4ec56142,0x80f0504000000e10acc9,0x7500001d0cf80b65c2f3,0xe01cd024980679926582,0xa5f556900002011be046,0x84101917f2412cd472f8,0xd74a081c00002034608f,0x946742013da0ade8127a,0x28f86cb1498e4830006,0x1500765112bc29010b79,0x812900ab7496458b2582,0xcbe03e394aa0005b413a,0xb458782d7c08ce8d78c2,0x3815b000000000d0be,0x400003440848f760862c,0x5a3e00940428c15dcc80,0xb20160882c1069400000,0xe0859c2ba000,0x24177826140053c007f,0xc1140000282caa21e9c0,0x8050be8882315adfc260,0xe0312c13700002826999,0x8eb897370b1d807e500e,0xf42bc202605063e07c78,0x2528509149e9e69f5818,0xce078588f3d07bb8323e,0x4ba40000c10a4816a608,0xfc190740ff802038997,0x60ad0a92d115c441080,0x2fd197150662275a80b2,0xf10d7421db07be89efd1,0x599c018f05f752f00000,0x106e6a08d0d13a015eb5,0x1ed40ce806c321da622,0x134ac550bd842fa1c55a,0x4a50400a0000342e170b,0x3792420000151d89079c,0x904bb80cae1b3d40,0x21007b541fb906cae24e,0xa168b00f4a0c254059e4,0x3809244501fd40fd2008,0xd01a4d196dc1aa244524,0xe9d4951144331223181,0xb206658011e02474a062,0x47d82cea00d50068149])))
def g237D9 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x10308100519110308115,0x24002440c20450064440,0xc2052405009445103081,0x4900091440c108049120,0x51030500930084451030,0x814900091440c2040407,0x485103091054009f96db,0x19508a379506c1e003fe,0xa1fe50fea87f143fc41f,0xd20fe107f843fa21fc10])
def g237H9 (j : Nat) : Nat := if 3 ≤ j then 0 else (if j<1 then (word80 [0xe1380,0xa46f0000f74e0000f,0x41da0795147d27c00000,0xc05800000,0xe06900004,0x5e20670000c87c00001,0x42600000000000000000,0x801700000,6,0x25100000000000000000,0xe25a00000,0,0x6111e24800006,0x11200000000000000000,0,0xf059517ee18181164,0x40400000000e03350060,0xe,0x166f7400000e05f00000,0x53790000000000000,3,0x3bd2130000104f0000d,0x40500000000000000000,0x663603c000000000,0x1028102e0000b,0x11b12460000000000000,0,0x5253655d0000b11e1,0x75b000074430000b086a,0x11400007444000000000,0,0,0x945000000,0xf082102a10576,0x40f0000b004000000000,0xb,0x24300001063827300000,0x30551039545c0,0x706d0000000000000,0x2007000000000,0x501f000050320,0,0,0,0,0xb3460000000046780,0xe2470,0x512e0000000000000,0xf26c00000,0x695fb74f00002,0x46000000000000d24f0,0x21200000000000092500,0,0x5065000000000,8,0x41000000000000000000,0x306f0000000000003,0x7700000000000000000,0xa068724e00000,0,0x57820000000000000,0x91809013000062620,0x685ab,0x300000f43f000000000,0,0,0x96700,0x8029000000000,0x11370000e74b00000,0,0x61848056f13600000,0,0x705d0,0xd04d4015000000000,0x94665,0x17f720c9076d46845540,0x5542000000000000e,0x14a24500000000c35f0,0xf2400,0x7d0000c12c0,0,0,0x465d0,0xc,0x8391357775000000000,0x813d0000000015780,0x84380000000000007,0x38a0520000000000000,0x70800000b4750,0x74c00000000074d0000d,0x5cd045e451000000000,0xa,0x3f700f003ac51e27500,0,0,0,0xc13400000000707c0,0x703dd0365,0x42900000000000000008,0x2d0108a010245260820,0x860801069100200203b0,0x80250018800600200202]) else (if j<2 then (word80 [0x56300000,0xb0516072b6640,0x317269000000000,0x800200000,0,0xc75c60010,0x155e0000121600000,0,0,0x1000000000001,0x800000000000000000,0x10900000000000000000,0xc,0x1222590000000000000,0xb06b0000000000000,0x2249327400000000d,0x24a00000000042b00000,0x22100,0x9511f00a00000,0xc0430,0x373f000021650,0,0xe04e0,0,0x717d000000000000f,0x18200000000e01000000,0,0x610a000067510,0x1960000000000,0,0xd0210000000000000,0,0x6600000000000000000,5,0x12900000000000000000,0,0,0x90810000000000000,0x607f000000000,0,0x945b806e000000000,0xb049000000000,0xa440000000000,0x14640000000000000,0x218600000000644e0,0,0x9062701e0,0xc7380000000000000,0x8677000000000,0x10840,0x326a00000,0,0x7258000000000000e,0x4181390000000070190,0xf5550000000000000,0x20440000000000000,0x7360000000000,0,0x702c0,0,0x5025f,0x65e00000000000000000,0x607b277600000,0xa261307a3,0x4700000e13e000000000,0xa859517b00000,0x117cb06c0000e,0x340000b074647620270,0x501a000000000,0xd66f0000000000000,0x90050000f0030,0x4040b02fe0640,0xd0260000000000000,0,0x208500000000f,0x244000000000000113a1,0x1150000e46500000000e,0x7500003053000002522,0x10b72180000954160110,0,0x4820000706000003,0x48604c9061000000004,0x13b00000000000000004,0x24d000000005183f05a0,0x800e0,0x7e84637119000000000,0,0x102b387460715,0x5776519704bc03700000,0xd03e0000000000000,0x8467000000008,0x86800000000007000000,0x611f00780000244f2,0x5b000000000000a26ba,0x57000001215601b00000,0xa00bd018520f6,0x9897a0000000000000,0,0x602200000,0,0xb01c8211b,0x5640000b06ab00c0000f,0x4280000b073000000000]) else (word80 [0xc00d00000,7,0x4700000000014800000,0,0x50540000374a00000,0xe1080000000000000,0xb042000000000,7,0x87300006214000000000,0,0xd0200000000000000,0,0xe128000000000,0xe,0x56fe03500000000f01dd,0x4a0000a01651850000b,0x2403580000c97900000,0,0,0x37a0000523f00000,0xe217e02360500,0xf])))
def g237D10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3f
def g237H10 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x5a35838000000145,0x1812a491c00e1ad99983,0x6a4000291000209e1a71,0x48000000130005080003,0xc3c24b08c490001ba800,0x223f41000604b1,0x3834ea95346449310002,0xa000000743018800701,0x80018af33d82e0152870,0x4021538428c894429004,0x38e923329aafb9199000,0x2a9e22f33244492e0214,0xa94398840022420c9061])
def g237L : Nat → Packing
  | 4 => (1,6,5,0,0,0,0,g237D4)
  | 5 => (174,5,5,0,0,11,0,g237D5)
  | 6 => (1091,4,5,0,0,14,0,g237D6)
  | 7 => (804,3,5,0,0,15,0,g237D7)
  | 8 => (135,2,5,0,0,13,0,g237D8)
  | 9 => (10,1,5,0,0,9,0,g237D9)
  | 10 => (1,0,5,0,0,0,0,g237D10)
  | _ => emptyPacking
def g237I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 4 0 0 g237H5
  | 6 => lookupWord 77 461 6 16 8 4 g237H6
  | 7 => lookupWord 475 2591 8 19 11 4 g237H7
  | 8 => lookupWord 360 1657 8 18 10 4 g237H8
  | 9 => lookupWord 76 1129 3 16 8 4 g237H9
  | 10 => lookupWord 15 79 5 12 4 4 g237H10
  | _ => fun _ => none
def g237 : Forest := ⟨237,10,fun i => g237Y[i]?.getD (0,0),g237C,g237A,g237L,g237I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P4_0 : block g237 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g237B4 : block g237 4 0 1=true := g237P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P5_0 : block g237 5 0 96=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P5_96 : block g237 5 96 78=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g237B5 : block g237 5 0 174=true := (@block_merge g237 5 0 96 78 g237P5_0 g237P5_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P6_0 : block g237 6 0 2=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P6_2 : block g237 6 2 47=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P6_49 : block g237 6 49 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P6_145 : block g237 6 145 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P6_241 : block g237 6 241 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P6_337 : block g237 6 337 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P6_433 : block g237 6 433 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P6_529 : block g237 6 529 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P6_625 : block g237 6 625 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P6_721 : block g237 6 721 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P6_817 : block g237 6 817 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P6_913 : block g237 6 913 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P6_1009 : block g237 6 1009 82=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g237B6 : block g237 6 0 1091=true := (@block_merge g237 6 0 433 658 (@block_merge g237 6 0 145 288 (@block_merge g237 6 0 2 143 g237P6_0 (@block_merge g237 6 2 47 96 g237P6_2 g237P6_49)) (@block_merge g237 6 145 96 192 g237P6_145 (@block_merge g237 6 241 96 96 g237P6_241 g237P6_337))) (@block_merge g237 6 433 288 370 (@block_merge g237 6 433 96 192 g237P6_433 (@block_merge g237 6 529 96 96 g237P6_529 g237P6_625)) (@block_merge g237 6 721 192 178 (@block_merge g237 6 721 96 96 g237P6_721 g237P6_817) (@block_merge g237 6 913 96 82 g237P6_913 g237P6_1009))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P7_0 : block g237 7 0 7=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P7_7 : block g237 7 7 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P7_103 : block g237 7 103 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P7_199 : block g237 7 199 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P7_295 : block g237 7 295 42=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P7_337 : block g237 7 337 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P7_433 : block g237 7 433 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P7_529 : block g237 7 529 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P7_625 : block g237 7 625 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P7_721 : block g237 7 721 83=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g237B7 : block g237 7 0 804=true := (@block_merge g237 7 0 337 467 (@block_merge g237 7 0 103 234 (@block_merge g237 7 0 7 96 g237P7_0 g237P7_7) (@block_merge g237 7 103 96 138 g237P7_103 (@block_merge g237 7 199 96 42 g237P7_199 g237P7_295))) (@block_merge g237 7 337 192 275 (@block_merge g237 7 337 96 96 g237P7_337 g237P7_433) (@block_merge g237 7 529 96 179 g237P7_529 (@block_merge g237 7 625 96 83 g237P7_625 g237P7_721))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P8_0 : block g237 8 0 12=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P8_12 : block g237 8 12 51=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P8_63 : block g237 8 63 72=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g237B8 : block g237 8 0 135=true := (@block_merge g237 8 0 12 123 g237P8_0 (@block_merge g237 8 12 51 72 g237P8_12 g237P8_63))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P9_0 : block g237 9 0 10=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g237B9 : block g237 9 0 10=true := g237P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P10_0 : block g237 10 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g237B10 : block g237 10 0 1=true := g237P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237T : checkedTables g237 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g237 0 0 0 = true)
  · exact (rfl : block g237 1 0 0 = true)
  · exact (rfl : block g237 2 0 0 = true)
  · exact (rfl : block g237 3 0 0 = true)
  · exact g237B4
  · exact g237B5
  · exact g237B6
  · exact g237B7
  · exact g237B8
  · exact g237B9
  · exact g237B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237G : graphValid g237 (boundsBefore K231) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low237 : Lower true (varsX 237) (graphGoal 237) 11 := lower_forest (g:=g237) (i:=0) (hints:=33555715) (before_sound K231 V231) g237G g237T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K237 := extendKnown K231 11 [(237,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V237 : Known true K237 := extend_ok (m:=237) V231 low237 (by decide +kernel)
def g243Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3fffffffffe06d8e8,0x69be0000007f0003f80])),(BitVec.ofNat 152 (word80 [0xa842844802042658a8,0x28960264c993264c993]))),((BitVec.ofNat 152 (word80 [0xfc003ffc1ffff20e0c,0x11ecdb0003f8001fc07f])),(BitVec.ofNat 152 (word80 [0x301300104048020c04,0x14cc80a142850a14285]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffc0001ffffbf0cb,0xa1210b0000000fe0007f])),(BitVec.ofNat 152 (word80 [0xc2042160909009c0cb,0x202103952a54a952a54a]))),((BitVec.ofNat 152 (word80 [0xffffffffe0000824f7,0x491ab201fc0000003f80])),(BitVec.ofNat 152 (word80 [0x98098004e0482456,0x41129258b162c58b162c]))),((BitVec.ofNat 152 (word80 [0x93710,0xa28774fe00000fffc000])),(BitVec.ofNat 152 (word80 [0xe00e010700803310,0x82823060c183060c1830]))),((BitVec.ofNat 152 (word80 [0x4c917,0x7e4005fffffff0000000])),(BitVec.ofNat 152 (word80 [0x30030021801008001,0x3c000581020408102040]))),(0x0,0x0)]
def g243C : List ColumnInfo := [(16,0,227,0,8),(1,0,242,0,7),(2,0,241,0,7),(32,0,211,0,7),(64,0,179,0,7),(0,1,82,160,6),(0,16,161,66,6),(0,32,82,129,6),(128,0,115,0,6),(1,32,82,128,5),(2,16,161,64,5),(33,0,210,0,5),(64,16,161,2,5),(128,1,82,32,5),(128,32,82,1,5),(66,0,161,0,4),(66,16,161,0,4),(129,0,82,0,4),(129,32,82,0,4)]
def g243A : List (List Nat) := [[],[97],[80],[80,97]]
def g243D5 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x1004003,0x1832ddd371595418ed86,0xdc941d4333d8f7250550])
def g243D6 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x804401e010084010,0x8e0100c00600081b0420,0x4068a802c30704106071,0xf14220b803c6833e1c4d,0x45b2c134843b180a4441,0xb003bbb8aa8a8df77155,0x151deee2b2a83eddd151,0x507daaa2a2a0cff74587,0x509faeca0ea17bdc941d,0x437ab0a83a86df635055,0xbdee4a0aa17bdc9414c,0x276baec4a0f355454541])
def g243H6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xe035d00
def g243D7 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x1040240402c02080628,0x2a2830100f1e1a240442,0x8a8a0a0161451c348078,0x385060480c3c70a8581,0x20d1c70dc09210a38690,0xc38506070101a3c5c02,0x80a8826393820881c3e,0x3c10868b0868c0c6900b,0x18ec23480b8f0c40d085,0x938e088142e4c41f00d1,0x70abdadba927b94a3781,0xdd069d8c571333f0d32e,0xa41ec520a400ffd9151,0xff59151ff55151ff5075,0xff50550ff50530bf593,0x51bfd9151dfd5151df55,0x151fb54951bf59541fd5,0x4541bf58750bfd9110bb,0x58b51db54b51db54951b,0xbd8941bb58b50b7d8d50])
def g243H7 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x10c6188a00000,0x215000000000000000,0,0x60400003c80000000000,0x9b000004140000000,0x11d0000000000,0,0x183000000000000000,0x2000000000000000,0,0,0,0xd2c000000000000,0xc8fcd000000000000000,0x2c4,0xa1c00,0x224000000067000,0x30000000000000000000,0,0xe9800,0x84])
def g243D8 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x10,0xe0a034592384e08d8072,0x71428238502248898e0,0x481e40e21604869018a,0x2cd1840498c280d1e30,0x2138d406a2451bcae421,0x685400ffa8ff547fa83f,0xf50fea87f4c3fa21ed52])
def g243H8 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [6,0x20b600a12c8387d54002,0xc420a60b09ec8aac001a,0x3880e0f0005432880061,0xa00000594a49c8f01000,0x50600000212000000540,0x71361800613a20a500])
def g243D9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x41882017f
def g243H9 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x336121800000000,0x18e000000,0x14,0xa0000000000000000000,0x81ce0000000006,0x20019f5458fcc0c00000,0x94800000000000,0x1c20000000,0x44])
def g243L : Nat → Packing
  | 5 => (3,4,5,0,0,4,0,g243D5)
  | 6 => (14,3,5,0,0,9,0,g243D6)
  | 7 => (21,2,5,0,0,10,0,g243D7)
  | 8 => (8,1,5,0,0,9,0,g243D8)
  | 9 => (1,0,5,0,0,0,0,g243D9)
  | _ => emptyPacking
def g243I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 5 0 6 2 0 g243H6
  | 7 => lookupWord 5 167 2 10 4 2 g243H7
  | 8 => lookupWord 7 43 4 11 5 2 g243H8
  | 9 => lookupWord 3 79 3 9 3 2 g243H9
  | _ => fun _ => none
def g243 : Forest := ⟨243,9,fun i => g243Y[i]?.getD (0,0),g243C,g243A,g243L,g243I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P5_0 : block g243 5 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g243B5 : block g243 5 0 3=true := g243P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P6_0 : block g243 6 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P6_2 : block g243 6 2 12=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g243B6 : block g243 6 0 14=true := (@block_merge g243 6 0 2 12 g243P6_0 g243P6_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P7_0 : block g243 7 0 6=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P7_6 : block g243 7 6 9=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P7_15 : block g243 7 15 6=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g243B7 : block g243 7 0 21=true := (@block_merge g243 7 0 6 15 g243P7_0 (@block_merge g243 7 6 9 6 g243P7_6 g243P7_15))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P8_0 : block g243 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P8_1 : block g243 8 1 7=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g243B8 : block g243 8 0 8=true := (@block_merge g243 8 0 1 7 g243P8_0 g243P8_1)
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
theorem low243 : Lower true (varsX 243) (graphGoal 243) 10 := lower_forest (g:=g243) (i:=0) (hints:=16842821) (before_sound K237 V237) g243G g243T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K243 := extendKnown K237 10 [(243,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V243 : Known true K243 := extend_ok (m:=243) V237 low243 (by decide +kernel)
def g245Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfff0007ffffff00ff5,0x7a60d23e280001f0001f])),(BitVec.ofNat 152 (word80 [0x42a135092845216141,0x3a60d21428294a5294a5]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffff8003fffff002,0x96e8554583003e007fe0])),(BitVec.ofNat 152 (word80 [0x4c02601b006424262,0x90605505800842108421]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffffc00000009,0xd8c3e099d100000f8000])),(BitVec.ofNat 152 (word80 [0x17083841c217838381,0xd8c36019d19ce739ce73]))),((BitVec.ofNat 152 (word80 [0xfffffffffffffffffa,0x4ff083ab807c00003ff])),(BitVec.ofNat 152 (word80 [0x980240120098000008,0x49a082a105294a5294a]))),((BitVec.ofNat 152 (word80 [9,0x1710a38776f8000ffc00])),(BitVec.ofNat 152 (word80 [0xe003801c00e0040408,0x7108282226318c6318c]))),((BitVec.ofNat 152 (word80 [4,0xe9177e4005fffff00000])),(BitVec.ofNat 152 (word80 [0xc00600300080804,0x40052040058421084210]))),(0x0,0x0)]
def g245C : List ColumnInfo := [(1,0,244,0,7),(4,0,241,0,7),(16,0,229,0,7),(0,16,165,64,6),(32,0,213,0,6),(64,0,165,0,5),(64,16,165,0,5),(128,0,117,0,5)]
def g245A : List (List Nat) := [[]]
def g245D5 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0xf624c3,0x27db82c7aa4f7715954,0x39f6e0b2a877adc15354,0xa76bb6a7a15eb7054f42])
def g245D6 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x10062086208008c410c,0x4100862283d20e1b1013,0x61201d6422e42d0caba,0xaa9f8f75604b3b2b2010,0xbf58f54bfd8d54bf59,0x353bfd9153fed8153bfd,0x9543bf59543ef55143f7,0x54d43fb54d52fbd4f42f,0xb54f42bed8153bb59742])
def g245H6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x144000c069e800170003
def g245D7 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x8512ec33a544b0c,0xa69152e3bad2448ce951,0x2c339644b0d912a25849,0x38291a0b007fd53faa9f,0xf53fea9ff50fdaa5ef42])
def g245H7 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x1320000,0x116ec0001ca8001d8,0x288e65950200b187dba0])
def g245D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x681117f
def g245H8 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x7c0,0x2c00000,0x2a80f2b34000,0x62])
def g245L : Nat → Packing
  | 5 => (6,3,3,0,0,5,0,g245D5)
  | 6 => (14,2,3,0,0,8,0,g245D6)
  | 7 => (7,1,3,0,0,8,0,g245D7)
  | 8 => (1,0,3,0,0,0,0,g245D8)
  | _ => emptyPacking
def g245I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 11 0 7 3 0 g245H6
  | 7 => lookupWord 3 23 3 8 4 0 g245H7
  | 8 => lookupWord 1 37 0 7 3 0 g245H8
  | _ => fun _ => none
def g245 : Forest := ⟨245,8,fun i => g245Y[i]?.getD (0,0),g245C,g245A,g245L,g245I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g245P5_0 : block g245 5 0 6=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g245B5 : block g245 5 0 6=true := g245P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g245P6_0 : block g245 6 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g245P6_2 : block g245 6 2 12=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g245B6 : block g245 6 0 14=true := (@block_merge g245 6 0 2 12 g245P6_0 g245P6_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g245P7_0 : block g245 7 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g245P7_2 : block g245 7 2 5=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g245B7 : block g245 7 0 7=true := (@block_merge g245 7 0 2 5 g245P7_0 g245P7_2)
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
  · exact g245B5
  · exact g245B6
  · exact g245B7
  · exact g245B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g245G : graphValid g245 (boundsBefore K243) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low245 : Lower true (varsX 245) (graphGoal 245) 9 := lower_forest (g:=g245) (i:=0) (hints:=33948933) (before_sound K243 V243) g245G g245T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K245 := extendKnown K243 9 [(245,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V245 : Known true K245 := extend_ok (m:=245) V243 low245 (by decide +kernel)
def g127Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x64d0642539c27a0000,0x3fc03fc6a581f5c])),(BitVec.ofNat 152 (word80 [0x2410442139c0088a8a,0x8a8b151515142a581f48]))),((BitVec.ofNat 152 (word80 [0xbc8da240695da00000,0x1fe0003fc01801b28ee])),(BitVec.ofNat 152 (word80 [0x3c8d2040495ca02626,0x26264c4c4c4c810908e6]))),((BitVec.ofNat 152 (word80 [0x6e3c5a81fe84240001,0xfe01fc0000001065fc33])),(BitVec.ofNat 152 (word80 [0x6c385a81fa84201e1e,0x1e1e3c3c3c3c10003833]))),((BitVec.ofNat 152 (word80 [0x5961396215337001fe,0x3fe03853e37])),(BitVec.ofNat 152 (word80 [0x596139400433707474,0x7474e8e8e8e801852037]))),((BitVec.ofNat 152 (word80 [0x35b96392a71c3fe00,0x3fc001c0631b9])),(BitVec.ofNat 152 (word80 [0x35296292221425858,0x5858b0b0b0b010063119]))),((BitVec.ofNat 152 (word80 [0x2aa465dd46324e0000,0x1fffc0003e007c0c1])),(BitVec.ofNat 152 (word80 [0x284215c0432476161,0x6160c2c2c2c3c007c080]))),((BitVec.ofNat 152 (word80 [0x9512195a80ac05ffff,0xfffe00000003fff80102])),(BitVec.ofNat 152 (word80 [0x800000120000058181,0x8181030303036e708000]))),(0x0,0x0),(0x0,0x0)]
def g127C : List ColumnInfo := [(1,0,126,0,8),(2,0,125,0,8),(4,0,123,0,8),(8,0,119,0,8),(16,0,111,0,8),(32,0,95,0,8),(0,1,86,40,7),(0,32,90,5,7),(9,0,118,0,7),(18,0,109,0,7),(36,0,91,0,7),(0,2,45,80,6),(0,16,45,66,6),(1,32,90,4,6),(4,1,82,40,6),(8,1,86,32,6),(12,0,115,0,6),(33,0,94,0,6),(64,0,63,0,6),(3,0,124,0,5),(5,0,90,0,5),(5,32,90,0,5),(6,0,121,0,5),(16,2,45,64,5),(64,2,45,16,5),(64,16,45,2,5),(66,0,45,0,4),(66,16,45,0,4)]
def g127A : List (List Nat) := [[],[65],[80,50],[80,65,50]]
def g127D6 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0xe282,0x7141e2839c8f1e0667e,0x1373585609d7ca303b12,0x4193f75e116148275b28,0x43242904f364c8648520])
def g127D7 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x4000010040c103020,0x80000c1c1040a2040c40,0x40000000a406841c3c00,0xa90103141a106901c507,0x14002c500089f1408004,0xc564140c639708300339,0x70b04485e5e4c2121218,0x84a0c819f87a9d4739c8,0x6e9ac69998649845f978,0x5c96c599585293449920,0x449043d8e8348bc25878,0x1685409800bef8258d62,0xbed83d89629fd83dc562,0xbbf845c562def825d932,0xfcf8358932fcd6358932,0x9ff835cb619fd874cb61,0xded724cb61bdf835c361,0x9fd83dc961dbf7458961,0xdbf744c961bf582d8561,0x9fd839d9219ff835d921,0x9fd831d9219fd86dcd21,0xdef7358921df77358521,0xddf73d8560bbf8458560,0xddf7358560bbf8458550,0xbed81d8920d7f75d8520,0xd7f7558520bbf8458520,0xbef8258520bee8648520,0xbec8648520fe56148520,0x9bf845c7629bf845d921,0x9bd841d9219dd831d921])
def g127H7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x4b0200e001520000
def g127D8 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x250918649184401,0x24402470824260236585,0xa44228b828832d049062,0xd1412020647050091209,0x836244446c58904b180c,0x986868600a2c32486860,0xc860110c22480443091,0x5086282454818a081c20,0x1339611850465090859b,0x1460b0c100a3c1288331,0x8c0a103860a0c00b5238,0xc16100ca90487182c386,0xa1008020499c098c0a2,0x3120e18283008a49010,0x59a0c38606032a23638b,0x12149305830e18180cb0,0xa49220b070c141c20124,0x5921c30301265121c949,0x94a0b0b2544a30226152,0x4c089f289846050e1474,0x8522c60e1474816a468b,0x22315122c88ca4a8a1c2,0x8e932050e14749902981,0x85f56882319301c76990,0x34dca3f48e143c2d3204,0xf43e37c076ceb1d138df,0xdcbb0f50e7fcbb90b0,0xcde9b8f696c1d61a473e,0xa5e49a8c70b1f3bb76f2,0xd7993b135f0ae93aa3e4,0x2a7cce89a82f0520930f,0xd1a82ac3d84b044003fe,0xb9ec5ffdcd62ffae6b17,0xff6358bfeb1ac5ffdc56,0x2ffae2b17fd72d87feb1,0x6c3ff4cb61ffae1b0ffd,0x62587fe992c3ff58d21f,0xfec2b07fd61583ffb0aa,0x1ff58550ffec2907fd61,0x482feb9ec57f5c762bfe,0xe6b17ef6258affb8ac57,0xf9d932bfaec997ed624c,0xafeb96c3efdd161bfee4,0xb0ff761586ffbb2437f9,0xd921bfaec90dfc76486f,0xfb9a437f5cd21fdac490,0xff561486feb8ec17fdc5,0x60fdec4907ed21482ffb,0xb2217f1d910b7ee8b0d7,0xd75d82efb9ac15fdd520])
def g127H8 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x7000000001011,0x9b00004d14fd0f209000,0x202000716688e1050c00,0x403704f080007140000,0x82141e74984a40a,0x2186a0000a0781f21d51,0x2406ea4546c0ee22005d,0x19523b20211598d1c024,0xb8ec15813b0d81a296c1,0x784b00000000010b41b0,0x2a664da46034f04])
def g127D9 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0xc9,0xd4d0c1431d4d05094944,0x2020e32555048c38cdb1,0x55048eb1cc504943322b,0x129b49071129b49070a3,0x5251088a28d490a8b29a,0x41270b86b452a40f0632,0x40d84812003ff62ff58b,0xfd32ffd87fd61ff487ff,0x60ff583fd50ff483fd10])
def g127H9 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x346800118b44000,0x18a40000000000028,0xc40000021ac000c18000,0x289945c00,0x3198000003a,0xb8002d8c000000000000,0x24c00000293,0x20a800146c0000,0x50da4,0x3571e3d43c00000000,0x8a00,0x1814000000003,0x236a4003d2c00301c00,0x18960b80000000000014,0x7f08400219400000069b,0x7000000000000000000,0xcbc0824780000000,0x1446d78000980000,0x396400000000000000,0x3da00000000000000014,0x24000000cc0000000000,0x100,0xccac97e5840540000000,0x3920000000000003,0x6400000000047400000,0x39180000000,0x2860000000000000000,0,0x303400000000269c0,0x2c28000003d24000,0xe280031b000,0,0x2e7c000000000000,0x16a800000000,0x1e90000000000003e782,0x8c000003c06f90000000,0x28b000,0x1289831a580000,0x2812,0xd3e54142c00000000000,0xcb40000,2,0xc00000000000a4000000,0x1c4c0000000000000000,0x1890000000000000000,0x303800000385800000,0x3c8c0000,0xc4b09c001408000000,0x3654c8,0x80018800401001010200])
def g127D10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x52501ff
def g127H10 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x5c00,0x596a300000455503a8a9,0x500000000061502d9296,0x125010123050c61a2aa0,0x51c082d4006182400059])
def g127L : Nat → Packing
  | 6 => (5,4,5,0,0,6,0,g127D6)
  | 7 => (37,3,5,0,0,10,0,g127D7)
  | 8 => (50,2,5,0,0,11,0,g127D8)
  | 9 => (11,1,5,0,0,9,0,g127D9)
  | 10 => (1,0,5,0,0,0,0,g127D10)
  | _ => emptyPacking
def g127I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 1 13 0 7 3 0 g127H7
  | 8 => lookupWord 12 67 5 12 6 2 g127H8
  | 9 => lookupWord 22 331 3 12 6 2 g127H9
  | 10 => lookupWord 6 31 5 10 4 2 g127H10
  | _ => fun _ => none
def g127 : Forest := ⟨127,10,fun i => g127Y[i]?.getD (0,0),g127C,g127A,g127L,g127I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P6_0 : block g127 6 0 5=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B6 : block g127 6 0 5=true := g127P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_0 : block g127 7 0 4=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_4 : block g127 7 4 33=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B7 : block g127 7 0 37=true := (@block_merge g127 7 0 4 33 g127P7_0 g127P7_4)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_0 : block g127 8 0 4=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_4 : block g127 8 4 26=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_30 : block g127 8 30 20=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B8 : block g127 8 0 50=true := (@block_merge g127 8 0 4 46 g127P8_0 (@block_merge g127 8 4 26 20 g127P8_4 g127P8_30))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P9_0 : block g127 9 0 11=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B9 : block g127 9 0 11=true := g127P9_0
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
  · exact g127B6
  · exact g127B7
  · exact g127B8
  · exact g127B9
  · exact g127B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127G : graphValid g127 (boundsBefore K245) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low127 : Lower true (varsX 127) (graphGoal 127) 11 := lower_forest (g:=g127) (i:=0) (hints:=16844099) (before_sound K245 V245) g127G g127T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K127 := extendKnown K245 11 [(127,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V127 : Known true K127 := extend_ok (m:=127) V245 low127 (by decide +kernel)
def g191Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfb854087941a9b93c0,0x36f80000007f01fc07f])),(BitVec.ofNat 152 (word80 [0xa084000294121b8340,0x32d050a142850a14285]))),((BitVec.ofNat 152 (word80 [0x48d8f59c328688d41,0xdf41000003f800003f80])),(BitVec.ofNat 152 (word80 [0x308d8f11c128608940,0x964113264c993264c993]))),((BitVec.ofNat 152 (word80 [0x1de3d26d2c03bc00a,0xe4d80001fc000fe00000])),(BitVec.ofNat 152 (word80 [0xc1cc2826d2403bc00a,0xe4480f1e3c78f1e3c78f]))),((BitVec.ofNat 152 (word80 [0xfd78e305f83e0219a7,0x645080fe00000000007f])),(BitVec.ofNat 152 (word80 [0x578e305682c001883,0x6450ba74e9d3a74e9d3a]))),((BitVec.ofNat 152 (word80 [0x4125acc76154dceeb,0x710a0000000000003f80])),(BitVec.ofNat 152 (word80 [0x41250cc36150d46ab,0x610a6cd9b366cd9b366c]))),((BitVec.ofNat 152 (word80 [0x49b250b0d65e43898,0x229e7f0000000fffc000])),(BitVec.ofNat 152 (word80 [0x41305090925c01890,0x923060c183060c1830]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x26490b029a5156636,0x8c217ffffffff0000000])),(BitVec.ofNat 152 (word80 [0x20010800080042424,0x8004081020408102040]))),(0x0,0x0)]
def g191C : List ColumnInfo := [(16,0,175,0,9)]
def g191A : List (List Nat) := [[],[80,50]]
def g191D9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xff
def g191L : Nat → Packing
  | 9 => (1,0,1,0,0,0,0,g191D9)
  | _ => emptyPacking
def g191I (_ _ : Nat) : Option (Nat × Nat) := none
def g191 : Forest := ⟨191,9,fun i => g191Y[i]?.getD (0,0),g191C,g191A,g191L,g191I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P9_0 : block g191 9 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g191B9 : block g191 9 0 1=true := g191P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191T : checkedTables g191 9 := by
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
  · exact g191B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191G : graphValid g191 (boundsBefore K127) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low191 : Lower true (varsX 191) (graphGoal 191) 10 := lower_forest (g:=g191) (i:=0) (hints:=66883) (before_sound K127 V127) g191G g191T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K191 := extendKnown K127 10 [(191,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V191 : Known true K191 := extend_ok (m:=191) V127 low191 (by decide +kernel)
def g223Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffec1e64c3c2074177,0x92a8000003f00000003f])),(BitVec.ofNat 152 (word80 [0x85041864c342034167,0x90a95555555555555555]))),((BitVec.ofNat 152 (word80 [0x789b0b0098de8f9,0x41280000fc000003ffc0])),(BitVec.ofNat 152 (word80 [0x198501b080088d60b9,0x410830c30c30c30c30c3]))),((BitVec.ofNat 152 (word80 [0x1d7031c2cf68a551,0x5850003f000000fc0000])),(BitVec.ofNat 152 (word80 [0x2e1d7031c2cf68a051,0x5040f3cf3cf3cf3cf3cf]))),((BitVec.ofNat 152 (word80 [0xffc9633e1eae878214,0x7400fc000003f00003f])),(BitVec.ofNat 152 (word80 [0x3009631a148c848210,0x340a28a28a28a28a28a]))),((BitVec.ofNat 152 (word80 [0x2178d759f40b063,0x2ce00000000fc0000fc0])),(BitVec.ofNat 152 (word80 [0xc002160d7497408042,0x2ce2cb2cb2cb2cb2cb2c]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x45812057070590e,0xe157f000000ffffff000])),(BitVec.ofNat 152 (word80 [0x8000120101904,0x80110410410410410410]))),((BitVec.ofNat 152 (word80 [0x33a449c814980680,0x9c8ffffffff000000000])),(BitVec.ofNat 152 (word80 [0x2284000810000400,0xc060820820820820820]))),(0x0,0x0)]
def g223C : List ColumnInfo := [(4,0,219,0,10)]
def g223A : List (List Nat) := [[],[64,49,118]]
def g223D10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xff
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
theorem low223 : Lower true (varsX 223) (graphGoal 223) 11 := lower_forest (g:=g223) (i:=0) (hints:=16844355) (before_sound K191 V191) g223G g223T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K223 := extendKnown K191 11 [(223,[]),(254,[64,33,49,80,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V223 : Known true K223 := extend_ok (m:=223) V191 low223 (by decide +kernel)
def g239Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfffc8bc342514a59e5,0xf00000003f000000fff])),(BitVec.ofNat 152 (word80 [0x80500b4240514a1984,0x7249249249249249249]))),((BitVec.ofNat 152 (word80 [0xc00356b470131c89e6,0xb8000000fc0000fc0000])),(BitVec.ofNat 152 (word80 [0x99b52b470120c89e6,0xb81c71c71c71c71c71c7]))),((BitVec.ofNat 152 (word80 [0x1d86864708f260e,0xcc00003f00003f03f000])),(BitVec.ofNat 152 (word80 [0x2e1906064508e240e,0x4c0c30c30c30c30c30c3]))),((BitVec.ofNat 152 (word80 [0xfffca0b17dee80f842,0x8a000fc0000fc000003f])),(BitVec.ofNat 152 (word80 [0x1300a0b13d2680e042,0x88186186186186186186]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x60af92a4ff84a1,0x9003f00000000003ffc0])),(BitVec.ofNat 152 (word80 [0x1c00608d92a4318021,0x90514514514514514514]))),((BitVec.ofNat 152 (word80 [0x1d50ac8d518315,0x72fc0000000ffffc0000])),(BitVec.ofNat 152 (word80 [0x20000d008089510211,0x2618618618618618618]))),((BitVec.ofNat 152 (word80 [0x32304911220201a,0x5fffffffff000000000])),0x820820820820820820),(0x0,0x0)]
def g239C : List ColumnInfo := [(2,0,237,0,11)]
def g239A : List (List Nat) := [[],[80,50]]
def g239D11 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xff
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
theorem low239 : Lower true (varsX 239) (graphGoal 239) 12 := lower_forest (g:=g239) (i:=0) (hints:=16778595) (before_sound K223 V223) g239G g239T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K239 := extendKnown K223 12 [(239,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V239 : Known true K239 := extend_ok (m:=239) V223 low239 (by decide +kernel)
def g247Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x5ce16a57f0000001fc,0xfe000106003837])),(BitVec.ofNat 152 (word80 [0x5ca16a57b13593264d,0x324993264c0002200837]))),((BitVec.ofNat 152 (word80 [0x90307eb0800000fe00,0x3f8001fc42180de593])),(BitVec.ofNat 152 (word80 [0x10301ea08050850a14,0x5082850a144a0820e013]))),((BitVec.ofNat 152 (word80 [0x22bb89b710007f0000,0xfc07f00000420724023])),(BitVec.ofNat 152 (word80 [0x22b309b7103183060c,0x304183060c0000700003]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x6a5726515800000003,0xf0000001fc00c18387cd])),(BitVec.ofNat 152 (word80 [0x2a4720515cab4a9528,0xa9654a9528004143078c]))),((BitVec.ofNat 152 (word80 [0x9428922180f800000,0x7ffe0278fe03fa90])),(BitVec.ofNat 152 (word80 [0x140800002c22c58b2,0xc5962c58b258fc03f280]))),((BitVec.ofNat 152 (word80 [0x520c504d27f0000003,0xffff80000380fffc00ea])),(BitVec.ofNat 152 (word80 [0x4008400023043060c3,0x6183060c310b6840020]))),((BitVec.ofNat 152 (word80 [0xa5a10088effffffffc,0x3ff0000030c])),(BitVec.ofNat 152 (word80 [0x800000084c08408100,0x8204081002501080108]))),(0x0,0x0)]
def g247C : List ColumnInfo := [(1,0,246,0,10),(4,0,243,0,10),(16,0,231,0,10),(2,0,245,0,9),(32,0,215,0,9),(64,0,183,0,8),(128,0,119,0,8),(0,1,86,160,7),(0,16,165,66,7),(0,32,82,133,7),(3,0,244,0,7),(18,0,229,0,7),(65,0,182,0,7),(68,0,179,0,7),(1,16,164,66,6),(1,32,82,132,6),(2,16,165,64,6),(4,32,82,129,6),(34,0,213,0,6),(48,0,199,0,6),(64,16,165,2,6),(80,0,167,0,6),(128,1,86,32,6),(128,32,82,5,6),(50,0,197,0,5),(66,0,165,0,5),(66,16,165,0,5),(96,0,151,0,5),(130,0,117,0,5),(132,32,82,1,5),(144,0,103,0,5),(160,0,86,0,5),(160,1,86,0,5),(146,0,101,0,4)]
def g247A : List (List Nat) := [[]]
def g247D5 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0xf624c3023275d0ebc,0x9308b2ac75916c475e49,0x8459563ac93643af20c2,0x2cab1d651b11d7906116,0x558ed24d90eab2f00b22,0xc76946c4755978059163])
def g247D6 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then (word80 [0x6203b101,0x18e0ac1d8016c1d80100,0x880648400c918e100000,0x1a081d040f4007a002,0x92523840000,0x34204,0,0xc82,0x34204000000003a103d,0x81e840f42040000d0a0,0x80c081604081c0c1e060,0xec00400281ac20800000,0xee3b2eb3a6e839ae27,0x78d9f4bcbf29c3707bae,0xe5b7ed9b4ecdaf2aba6a,0x89a0e7d9de719ae65926,0x438f6378c62b8961f866,0x1383607805fb7a9e4779,0xd8749cc719c06e9b46b9,0xa86899c65990629845f9,0x785c96c599605694950d,0x324b1264811a4510e3f4,0xec36cca310be2e0a7284,0x901fc791a057118400e8,0x1e06012030060029cfa2,0x5d3835c565a76e8174e0,0xd715965dba364665dc16,0x4ab3e899461a7558eadb,0xa0651869d56399769697,0xe116558ee4da21d78459,0x563b9568475e116558e6,0x5ea91d58459563b93688,0x756116558ee55a11d584,0x59563d93dd7926116558,0xf64c75e498459563d96d,0xd7906116558f65875e41,0x8459563ab3e8994e0565,0x58eadba06538159563ab,0x568784e056558eacfa26,0x138159563ab6e8184e05,0x6558eacfa26118159563,0xab6e81846056558ee4da,0x21d56559163b95684755,0x956458ead9a69d780591,0x63ab6e9975e016458ebd,0x3a15d78059163af26887,0x5e016458ebd1a11d7805,0x9163e96dd565e016458f,0xa58755978059163ab6e8,0x565e016458ea5ea921d6,0x55516399de86981d5655,0x86e35a41d78159561b99,0x68875e0565586e71a01d,0x78159561a76e8d75e017,0x45869d9a31d7805d161a,0x7a68875e0174587a73a1,0x59580d5161b36e8194dd,0x5635866d7a16577458d6,0x1d36dd7905d1635874d9,0x75e417458d61bb4e8174,0xe0563587c5775e456558,0xd61d36dd79059163586e,0xd3a05938158d61b33e89,0x945d963d46cdba065176,0x58f51b17e9d9459563d4,0x6e4fa26516558f51b96e,0x819459563d474d976e41,0x6458f51d965979059163,0xd469cfa2613835d951a7,0x6e8184e0d765469dba35,0xdb8059151976e8194a1b,0x735469cfa265186dcd51,0xa76e819461b735465dba,0x65365dcd51c37e59866,0x13735465cfa266164dcd,0x51976e8198593735471d,0x986e4164dcd51973e899,0x6553735465dba065954d,0xcd51cd5e579161b73546,0x5dba065276dcd51c75e6,0x3915db735470df966197,0x4dcd518776a397593735,0x461dfa865d64dcd51973,0xe8997593735465dba065,0xd64dcd51b17e95945d96,0x3546ccfa26517658d51b,0x35e85945d963546cdba0,0x6517658d51f15e57915d,0x963546e4fa26516558d5,0x1b95e859459563546e5b,0xa06516558d51e5521f91,0x595635471da87e416458,0xd51c7621f90591635474,0xd976e416458d51d96597,0x9059163546e67a265165,0x58551b9ce81945956154,0x6b55a32158458551d9c5,0x97906116154767165e41,0x6458551d9565965dcd61,0x547c55655d37358551b9,0x5e958458d61546ed3a06,0x116358551bb4e816458d,0x61546e65a22156558541]) else 0x3)
def g247H6 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0xe4010800,0x3e0301940003000000])
def g247D7 (j : Nat) : Nat := if 4 ≤ j then 0 else (if j<2 then (if j<1 then (word80 [0x7815d951,0xcfbc8b0fb2aa33fb9061,0x3655476ef22c34caa8dd,0xbe498459551bbbc8b08b,0x2aa377b90611655471ff,0xcbb2e8a8e9fe19655d1,0x51cefc9b0fb22a39f791,0x61f645476ef22c2ec8a8,0xcfde4585d91519becaf0,0xeb22a337f9561d645467,0xdf24c3ac8a8cfee41875,0x9151aefc9aecb22a33f5,0x91e15645473f6edc02c8,0xa8e7e5db8059151dbd32,0xf00b22a3b7965e016454,0x67df24c32a8a8cfde458,0x6551519fdc830caa2a3a,0x7f86595545467eb2dc0a,0xa8a8edd5978155151dda,0xb2702aa2a35dd94a1b73,0x5473bf2ac36e6a8e77e5,0x186dcd51ceeca30db9aa,0x35df9461b73546bbb29b,0x2ee6a8e7761965dcd51a,0xefca2cbb9aa35df96613,0x735473bb0cc26e6a8d77,0x66364dcd51aeecaec9b9,0xaa35df9859373546bbb3,0xb26e6a8e7761964dcd5,0x1aefcaac9b9aa3d9d845,0x9373547bb720b26e6a8d,0x77e5954dcd51aeecb2a9,0xb9aa39dd8655373547ab,0xacaaa6e6a8f6759154dc,0xd51dafcab0db9aa3bd79,0x161b73546bbb293b6e6a,0x8e77e6176dcd51eafcaa,0xedb9aa35df945db73547,0xbaf22bb6e6a8ed761965,0xdcd51fabc8acbb9aa35d,0xf965d3735473bb0cba6e,0x6a8f5759574dcd51eebc,0x8ae9b9aa33dd98d93735,0x46bbb2fb26e6a8dd7657,0x64dcd51beac8ec9b9aa3,0x5df9759373546bbb2eb2,0x6e6a8f675d164dcd51be,0xdc82c9b9aa3cdf945d96,0x35479bb28bb2c6a8f75e,0x457658d51f2fca2cab1a,0xa3e5d9459563547eaf22,0xb2ac6a8e77a1d6458d51,0xcee43ac8b1aa3cdd7659,0x163547cbacab22c6a8df,0x6e416458d51f3bca2cab,0xaa3e759459561547cef,0xab2ac2a8f9d59784585,0x51bbbcab08b0aa3b7485,0x61161547ceacac22c2a8,0xdfce418458551b7bcb2e,0x8b0aa3e75655d161547c,0xeacab22c2a8dfce41645,0x8551f3ab2aa8b0aa37d5,0x96dcd61547eaf0bb9ac2,0xa8fd55977358551eeaba,0x6e6b0aa3ed78458d6154,0x7dab08b1ac2a8fb55916,0x358551a7ecb6eab2a83c,0xde97595635079b92eb2a,0xc6a0dbd65a8558541beb,0xc9b0ab0a83b758521561,0x506fab2642ac2a0df964,0x88558541e7a4bacab0a8,0x3e778559561507ce90ab,0x2ac2a0f3ddd56558541f,0x6bc2ac6b0a83ed58558d,0x61506cbd303aacab1db3,0xe498459563b6dc8308b2,0xac774d921d56558eeab2,0x23aacab1eb6597805916,0x3d2e43acaaa2c7a5d65e,0x55458e2ff30ba8eab0d,0x8f6507559561b36c90ea,0xb2ac3679901d5655874e,0xacac0ea8b0e9e59580d5,0x161b6dc82e8b1ac3c5f7,0x559563586daf22b2ac6b,0xdb6e416458d61e2fcba,0xcab1ea31dd98d9773546,0x3bb31b26e6a8d76e4164,0xdcd518eecc4edb9aa31d,0xf985db735463bb2d43ac,0x6a8f17e557658d51e6bc,0x8aecb1aa3e5791595635,0x472b90eb2ac6a8dd564c,0x8558551b3acb4cab0aa3,0xe5565dcd61547caf0ab1,0xac2a8d7525d6358551f2,0xab2ac6b0aa3cd49758d6,0x15079aeeab1ac2a0d876,0x507559563b26c90eab2a,0xc7655911d56558ecb320,0x3aacab1e9659580d5163]) else (word80 [0xdecedc76,0x13ac9d44e9274139c9cd,0x8e5c71c38a1c1cdf46ed,0x3701b4cd966c335d9ae0,0xd5669e34b1a24cda6603,0x2998f0c5e62230817f8b,0xd85e42e916d8b525972c,0x515f4acc55e2a894d4a3,0xc51628493dc9de4e226a,0x932096c4a424e1250918,0x48923e11e48d845f22b9,0x13c88443a21410447f43,0xe81e60eac71436e1a90c,0xc46342f91710b2c54a27,0xf12f090844c2050f2074,0x838a1bd0d5866432217a,0xb4056c29212308103ac,0x1bc0c205582280dc0570,0x2000a402e00057de4585,0x5c765af7c9309b8acb5f,0xb9061371596beb23ba6e,0x2b2d7be4974dc565afdc,0x82e9b8acb5ef925d1715,0x96bf720ba2e2b2e77dd3,0x835c565ceeba706b8acb,0xb5f85e0d71596bbf26c0,0xaebb247f662855c764af,0xac8d0ab8ec95df936157,0x1d92bef22c2ae3b24f7e,0x4d8199564afcc8ccbb82,0xc95fb9159770592aff2e,0xc0acbaa75de45655c754,0xebdc8acab86a9d799159,0x570d52ebf26c0acaaa6b,0x7e51869d563d6eca30d3,0xaac76de97e116558fcbe,0xebc22cab1f971d784595,0x63b6ec8f08b2ac7e5f75,0x6116558fcb8eac22cab1,0xdb7e458459563d6fca70,0x2b2ac7add94e056558f5,0xbf09c0acab1eb7613815,0x9563f2fcab02b2ac7adf,0x846056558f5bb08c0aca,0xb1fb5e058159563baf4c,0xeab2ac7adf985977458,0xedbb2d3aac8b1db7e597,0x559163bebc8aeab22c77,0xcd921d56458efab223aa,0xc8b1f97dd56559163f2e,0x3aacab22c76df9159564,0x58f7b6ebc02c8b1ef69d,0x78059163decbaf00b22c,0x7bd875e016458fcbf22b,0x2aa8b1f976456555163b,0xedc82c9b8ac77db90591,0x7158ebf720c26eab0ebd,0xe45869d561debc1f02ba,0xac397f985d475587aef2,0x2ba8eab0dbde4575d956,0x19fbc8b0f32ac3af7916,0x1a65586cfd303aacab0d,0xbbe498459561b7bc8b08,0xb2ac36fb9061165587ce,0xeebc0acab0f9d1d78159,0x561ebbbaf02b2ac33f79,0x1617745863fb313aee8b,0xd77e4d75dd161cbfc2c,0xeaba2c35df935d574586,0x3fd303aae8b0d7764c75,0x5d161af6c90eaba2c3a7,0xf85595745873f6ebc02e,0x8b0e7e9d7805d161cfcb,0xaf00ba2c39f875e01745,0x875f2cbc02e8b0e7edd7,0x8059161d7cb2f00b22c3,0xe7791597545865fb2dc3,0xaa8b0f9de456555161e6,0xeca6eab1ac3ed7915d56,0x3586dbb2bba2c6b0f375,0xd77458d61b6fcaae8b1a,0xc3cdf755d1635879baea,0xba2c6b0db7e5d5458d61,0xf6aba702b1ac37d7915d,0x563587daf22b2ac6b0f3,0x7dd56458d61f6ab2702b,0x1ac35ef9261176d46bf7,0x20c22eda8d5fe5d84597,0x51bb7c9308b2ea377b90,0x61165d473f2edc02c9a8,0xede5978059351e6fca2e,0xcb1ea3cdd945d963d47c,0xbf28b2ac7a8f97651655,0x8f51e6ebb2c8b1ea3e5d,0x6559163d46fb720b22c7,0xa8edde45859d9519fdc8,0x3093b2a357f956117654,0x6bdf24c22eca8d7de458,0x45d951afdc8308bb2a3d,0x5f85e0d765473bf09c1a,0xeca8e77613835d951cfb,0xc2f02bb2a3d7785e0576,0x547baf07c0aeca8edde1])) else (if j<3 then (word80 [0xf400740,0x41f04001c2040901d86,0x51183709c1300860c101,0x83041f0400054905c470,0x207019d08307017b103,0x508107ec420c3312c009,0x42b00c40c1705c012142,0xd83040660c221283b00,0x33254270030000000000,0x1c405c4705c00dc46242,0x705c00ac0210207e89b0,0x381810681f0810241f0,0x81027c20bc2041a04004,0xdc17003068106bc209c2,0x682f081a0bc20682e08,0x10681e0c106c030b8305,0x10024206d10080207c20,0x4030403e08200c100c1e,0xfc20b83f082d00100c1,0x6081608101830783e082,0xf820b83e08206c100c,0x10701b068300c0060804,0x711c170037101300142,0x102c404c6310200000c,0x13002b00100083182300,0x100c1300200143102215,0xc00819041904c0041904,0x19040064144142a0c306,0x4104cc608133182064c6,0x8192482e0c42081e048,0x30485040304c00813318,0x2c081713420910711c17,0x342141ad08271206081,0xf705c060c4a15830ac4b,0x2b1102b00340ac0210,0x307e89b0038181713038,0x18307c1b705c0c0c5217,0x30ac440d060c1201424,0xec0081f216c00484c18,0x104810081b04846f081a,0x141fa2503b004c141a24,0x1b081030b050c1905460,0x6420654609c4818207dc,0x614307d897003000105,0xc105c10010e102000be1,0x206b840817058904206,0x2426241625848183040c,0x26278410c9f03c10684e,0xbc0074331f06b1382f0,0x45f1382f004d06b061bc,0x4e0bc0f0706068691d06,0xd1182f04552744f03c10,0x68507249d13c0f041a1b,0xc0f081af04432706017c,0xe0fc11b06f038313440,0x1783f0420134407c45f0,0xbc0a0fc11e4761805d13,0xc2e0fc11cc7c1ac4d0bc,0x1e0c605589f03c1e0c50,0x70c9f03c1068531e06b1,0x302f0783181505189f03,0xc1e0c6423c13183f04c6,0xbc10510f04c60d10d0b,0xc10fc10419e0f42f0440,0x6b42f043f041a0a46f04,0x190c85f13c0067c10401,0xc1c19f0017f0bc1c0c6f,0x146f041913c10682f13,0xc091bc10645f0017f041,0xa101cb0bc044bc106860,0x73c006bc1448505fc0f0,0x41a13c4f004d0684f13c,0xf041a13c1068200c4cd,0x13c10684ec075ebae9d6,0x4eaf7563a91d38e99746,0x39fdcf8e6f733b991cb8,0xe547263925c82e39718b,0x891c2ee0f6feb7c1bc6d,0xd16dfb6a1b22d846be35,0xa9abad4b69f34d9a3ed1,0x2682b3e19d6cde668b31,0x196eca564731f18e8c71,0x634b10d862c1a606b001,0x7fabfa5f6af817a6bc65,0xdf2ed975cba65cf2e597,0x1cb8b5c42e016fab7a5b,0xbadbd6bab555a6ad1568,0x4b3f59bac31608b0157c,0xabc55d2ae156a2b09560,0xaa854b2a254eea6f52ea,0x955490a36512288543ca,0x1b50c2855424a0f503a7,0xd53d09db4e726f13689a,0xc4d226713289874bfa5d,0xd2e89624ad2535280933,0x493247922c90e480a3e5,0x1d88df46ba33d18e8ba4,0x5922a913a89044422010,0xf0870436a1950b084b41,0xf20d905c81c40ca04501,0x28063fa1fb0fc87dc3ec,0x9f44f887c13df1eecf5c,0x7a63d19e58f1c78b3bf1]) else (word80 [0x1a50c20000241000d0,0x81d08101c17002065c00,0x800200208050400001e0,0x13081001a041a041a05,0xc206820538409c405c47,0x5c00cc4e08201ac4082,0xb10c90c1c05ec40ec1b,0x88a084080c9b06c010,0x1f30c27101711c170033,0x10c308c4705c00c19e08,0x2a081a09c1700c410c3a,0x826084508455102d004,0x40b401102d13400b44d0,0x2d13400949c0b400c1f,0x5949d00491444d003e0,0x8101c304474194470d82,0x7044f1d49512060c1460,0x949d104d0f820b0bd0c2,0x66c0081af082067c,0x20983068206810181e0c,0x1e0c107c1e0c1a0c1000,0x1010000340040701000])))
def g247H7 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0xd11e6b8b0,0x124ae40000000000,0x249001528544ac00000,0x104800000001e8000000,0x3d9b5f000000000007,0x620012ee1e2c8e2c0000,0x36f000000f8400,0x2410b6000001,0x4664d000000000cc0000,0x7050000000075c05,0x409e6a80000063400000,0x59d35000000889440a95,0x987b0070713b0000001e,0x6248520000000089e00,0x680000000093e,0x30711b000000000003,0xc60002280058dd64002a,0xd00000121800000c892d,0x30e65c00000000003,0x6d80000000000000d64a,0xe68064b11f68c00000a3,0x391c0000080200000000,0x3089d18ac000000,0x85e674000003420000,0x2000b840000000000145,0x40000000000000000000,0x54a000300000,0x2800000000001f5c0020,0xa00000000000b56aefdd,0x726770002c9800000001,0x57000000000005410000,0x19e13f0000000000000,0x10f581906000000006d3,0,0x46a8801f0000000000,0x26e0000000010e40,0x11102103000100010010])
def g247D8 (j : Nat) : Nat := if 4 ≤ j then 0 else (if j<2 then (if j<1 then (word80 [0xf8759151,0xbfd8759151dff7659151,0xdfd7659151bff8559151,0xf7e6559151f7d6559151,0xfbd7459151ffb8059151,0xbff8655151bfd8655151,0xdfd7655151f7d6555151,0xfbd6455151fdf64dcd51,0xfdd64dcd51fdd6458d51,0xff78558551ff58558551,0xff56558551ff78458551,0xff58458551ff57458551,0xff56458551ff55458551,0xdfe8759541dfc8759541,0xdff7559541ff78558541,0xff68558541ff58558541,0xff485585419ff815da65,0x9ff815d2659fd81dd165,0xbef825d165bfb805d165,0xbdf835c5659ff815d764,0x9ff855c7649fd81dd564,0x9fd85dc564dfa65dc164,0xdf965dc164d7d655c754,0x9ff815d954cff7659554,0xbbf81591549fd86dc554,0xd7e65dc554d7d65dc554,0xdbd64dc554bdd869d563,0xbdf865d563edf8459563,0xedd8459563edf8159563,0xedd8159563f5f7559563,0xf5c7559563bdf8159563,0xbdd85dd163edd65dd163,0xbdd81dd163edd6559163,0xbdc8755163edd6555163,0xbdf8155163afd869d561,0xd7f759d561bdf835d561,0xd7d751d561bbd841d561,0xbdd831d561bed821d561,0xbf9801d561afd8699561,0xd7f7599561bf58199561,0xe7f7559561e7c7559561,0xef78159561d7f7559561,0xbf781595619fd85dd161,0xbfb805d161bfb8059161,0x9fe87d51619fd87d5161,0xafd86d5161e7d65d5161,0xbf581d5161bf980d5161,0x9ff87551619fc8755161,0xe7d6555161edf7558d61,0xedd7558d61edf8458d61,0xedf7458d61edd7458d61,0xedd5458d61ddf7558d61,0xedd6558d61edd6458d61,0xfd78158d61d7f8759751,0x9fd87d9351b7d85d9351,0xbfb8059351ddd7658f51,0xf5d6558f51b7d859d951,0x9ff855d951d7f855d951,0xddf835d951df7815d951,0xb7f855d9519fd87d9551,0xbf581d9551b7d8699551,0xf778159551bf78159551,0x9fd87d9151b7d85d9151,0xbf581d9151bfb8059151,0xbf78155151dde86dcd51,0xddd86dcd51ddf65dcd51,0xddd65dcd51ddd84dcd51,0xddf64dcd51ddd64dcd51,0xddd54dcd51bdd86dcd51,0xdde76dcd51ddd76dcd51,0xf5d65dcd51ddd74dcd51,0xddd7658d51f5d6558d51,0xf778558551f748558551,0xef76558551f766558551,0xef56558551f756558551,0xfd77358551fd56358551,0x9ff855d9419fd86dd541,0xbbf8559141dbf7559141,0xddc8758d41ddf7558d41,0xedd6558d41df77558541,0xef565585419fb805d365,0x9df835c665d79655c354,0x9ef825d9549fb805d954,0xadd869d563adf865d563,0xbd7815d563b9d841d563,0xbcd821d563bd5811d563,0xbd9801d563ade87d9563,0xadd81d9563add8699563,0xe5f7559563e5c7559563,0xadf8159563adf865d163,0xbdb805d163bdb8059163,0xadd86d5163e5d65d5163,0xbd980d5163e5d6555163,0x9fb805d361cdd655cf61,0xcdd7558f61add83d9561,0xcdf7558d61ed78158d61,0xcdd7658f51e5d6558f51,0x9df835d9519f980dd151,0x9dd86dcd519de8758d51,0x9dc8758d51cdd7658d51,0xe5d6558d51e756558551,0xed563585519fb805d941,0x9df835d541ed56358541]) else (word80 [0x6e270307,0xc10a0d46e200b81c10c8,0xdc4a1703821a142fc4e0,0x7043428182e46e270a07,0xc0e086890bf1381c10d0,0xb84c1f0b82161781c10a,0x5c46161035c0e085c6e,0x643978e55f92de4338f4,0xe32b8a9e1db855e0f780,0x1dfa77d1dee7798de277,0x68dcfb71ddc176eddaeb,0x687d977645d84b5f1d71,0xf594d5cf549d3cb4b6d2,0xf462d0e3420cfff3dec,0xef739ccdef33fccc330f,0xcb972dfcb1f2a6ca1725,0xbc8c71fec6e7186c54f1,0x29c447102c3870b7c237,0x75c10b02ac026fe8bf1,0xefa6bdf2f49bcc6f10bb,0x52ebcba4ae7ab91ee26b,0x7f2dc9b6c6d63b47acf4,0xb34eca9b1fec55b066be,0xfaf16ba4adeab50ac76a,0xf3ab26a96a9b2a42a83e,0x9dca6a6976a57a934a44,0xe8fba322895a1ae84aa0,0xee8239fe67cf9eba7849,0xcda6fa9b1e68b996261c,0x97825a495c653e94524c,0x6920644e904a3e88eb23,0x678cd22e68aaa265885e,0x1d28612148840e0be81c,0x20348029fd77eb5f7a7d,0x41f1d7bcdeae7a11e487,0x855deb7675d6a7501cfb,0x7321c8c711dc0b6f3db8,0xa6d15b126b7da91699da,0x3d68059bc664996864d5,0x90262d187860a97ee5ec,0x975b5c7d6e35a7966258,0x755e1569555754254c45,0x1d94434ff93d44e85380,0x4d7d31a4b792ab4a0526,0x48491cd462113a44410,0xd4426105c4080fd23e34,0xf483c30ec73a50e6138d,0xcdfb36b4d71351cd0b33,0x3cc9330f0bee2f10b7f2,0xd30b192b98ab32a24a56,0x288c9e726ac96624848e,0x522a486d20e88101f2c7,0xaa1db87321c446e71ad0,0x681191461217a05be160,0x853d144c4e012fc48311,0x1c40b0f603a50dc832d0,0xbe82be0a0824f08041c5,0x624156048c0cc026406,0x600f0000dfd855c765df,0xf815da65dfd815da65bf,0xd81dd165bff815d165df,0xf84dc565dfd84dc565df,0xf74dc565dfd74dc565f7,0xf855c565dff745c565df,0xd745c565fdf835c565ff,0x7715c565dff815d764df,0xd815d764dfe855c764df,0xd855c764bfd8199564bf,0xf8159564f7f8159754f7,0xd8159754f7f8159554f7,0xd8159554bff8159554df,0xd86dc554dfd65dc554fd,0xf8159563fdd8159563fd,0xf7559163fde7559163fd,0xd7559163fdc7559163fd,0xd64dc563fdd645c563df,0xd84dd561bfd869d561fd,0xf835d561ff7815d561ef,0xd75d9561bfd8799561ef,0xf7559561eff8459561ef,0xd8459561dff7559561ff,0x78159561bfd85dd161df,0xe75dd161dfd75dd161ef,0xd65dd161bff855d161df,0xf755d161dfe755d161df,0xd755d161dfc755d161ef,0xd655d161dff7559161ef,0xd6559161bfd87d5161bf,0xf8755161dff7555161ef,0xd6555161fdd7558d61df,0xf845db51dfd845db51f7,0xf8459751f7d8459751df,0xd7659351f7d6559351ff,0xb8059351fdd6458f51bf,0xd849d951dff855d951df,0xf845d951dfd845d951f7,0xf855d951bff845d951ff,0x7815d951bfd84d9551f7,0xf8459551f7d8459551bf,0xf8459551ff78159551bf,0xf865d151dfd765d151f7,0xd655d151ff7815d151bf,0xd87d9151bfd85d9151bf])) else (if j<3 then (word80 [0x62703821,0x71d10c3603130420e085,0xc80bc1b89c0e08686830,0x5f05c4e070434385f898,0x2e07060c1a1c2dc4c105,0xf81c183068824c1b89c0,0xe08686e07042e1a1205c,0xe085c342f0382170d09,0x40417042e201781c10b8,0x684a270382170d0bc0e0,0x85c3420710dc022f0b83,0x831f801ce086846161b8,0x9c0e08686c370385c10d,0xbc0e085c34202c91c46,0x17008bc10e11c4e00689,0xa1c1782200d07040e700,0x2fc222f07063a27801ae,0x87050e1278106e08686,0xbf0a0c45e070706385c,0xc05e070438305f8506e,0x7050631178489e041b8,0x3831d061c24f0385c183,0xf83e17038217170744e,0x17042c2a288f85835138,0x5c1c191c00bf04342700,0x2fc10d0803e17008bc10,0xb8c1ca270b0620e09147,0xe07042e1a1289c10b068,0x4e17002fc10d8bc2e070,0x42e1b143805e17030744,0xe085c80bf1381c10d070,0x6830702f42e2703821a2,0x12442e07042e1a198ac4,0xe005f822118404862d09,0x8983e0f002e487189c0e,0x85c34322789c0e08683,0x8307308c40bf03821a1e,0x4c0c1f042e20182fc4a,0x170383060d0e8902f0b8,0x1c10e0d44e17010bc123,0xc1ca2703858342f048c,0x403c0f06a260f85c1c29,0x89e260f81c12305070e,0x5f89c0c1f048c14202f,0xc023704342e0f8409027,0x3821a1c35c20e7044e2,0x30b81c10d0a1ae0f0830,0xe704341e0c1204e17038,0x21a1c2e83e011b821a18,0x2fc023704342a0f85c10,0xd09c2e086830460c3846,0xe070a89c1210b44e070b,0x8383230f44e00700bc2e,0x91870781e0d85a260f8,0x3c22385c10d86846260f,0x81c10a31866371307c0e,0x85066270307c10a3186,0x633138183e085064960d,0x8cc4e050b8208210a08c,0x1b1381c1630e08632170,0x7c16270076331307c0e0,0x8506e260d8d42e070432,0x3b1381c10cb185a13138,0x1c10c8bc063704322311,0x8c18e07043230708c89a,0x171381c10d1017e27038,0x2460d0dc2e0870342710,0x7c0e087034305e07c02,0x370434305c07c0237043,0x430648dc40bf0207c2e0,0xa149e205f8503e070434,0x46238146e086440e05f8,0x9c0e0918343f0b8183e0,0x85c5e17002fc1090bc0e,0x160f82171785c0c1f042,0xe2f0382170d09c00d704,0x2e921709c0e085c34287,0x385c0097042e300f85c0,0xc27042e361786078370b,0x83441f0dc40441781c1a,0x18e05e1e1385c10b0d85,0xe1f0b8017088d85e1e13,0x85c10b0dc4e011782101,0x781c10a8404c360b89c0,0xa704203f042e1a0f0d8,0x2e27009a1a1b0d82e270,0x3821a1b82160d0615e07,0x43427102fc0e08685e2,0x5f81c10d0a17e260b81,0xc10d0c17e2703821a178,0x9c0e086840a704261013,0x40ea205382101b04472,0x7f0e0dc1a20fc0e085c3,0x427028820e08685e0858,0x341e0a881ae07042e301,0xf0706e17068837102f83,0xe07042837102fc0e0868,0x5e205f81c10d0a1ce270,0x3821a144217e250b81c1,0xd0fc4e060f8214142fc,0x4c1f0382141a8dc4c1f0,0x382141a8983e17042c2d,0x98c08c2f1307c0e0914]) else (word80 [0xc2a186830306820e3,0x83418702ec3a2081f0d,0xb0c304b10204b0580c41,0x1244a186120491182c0,0x143543e10612a10409a1,0x3058044a18c420d05420,0xd040661841c6130c30e0,0x20561070321600240913,0x1204861f0d04c20d04,0x8902a1187061434c3612,0x27082868121223081b0b,0x841c0d412861b160d456,0x1861c832083420509340,0xa26085a0126881b0e804,0x9a2081624d1186c1a030,0x1041f242049a1b018982,0x1a17436012588282580c,0x40c3886e106842106820,0xe06b841e0d841a0c3842,0xd0606c191436260c2e1,0x880361760b030630681e,0x120e0c18143817a20800,0x6d84151106170c3e1222,0x861b049128020168009a,0x20809615008b44141283,0x6130680c0100e200b916,0x801214360481d00122a0,0xe80171008170d0417043,0x409a207830d85c8a2072,0xc420d080962041b04b0,0x580c41588890836c1600,0x74004d10384d003e1900,0x3e090d88c04487c4c1f0,0x88009620bc20d0409e13,0x1030d02582c0627086e1,0x682c1f0812c413841a0,0xb07822007c122b130706,0xc3ec16060c40960f050,0x6620b820d041b0801689,0x830bf082440270742611,0x1835441c2446e1068409,0x708341843061ce108064,0x2e0b0620401383e1081f,0x860c8240e10c82a0026,0x88220a8009a20809c160,0xc384a0e801f121283a00,0x7c42360f84120c8b8220,0x7c12205f05440d881fc,0x1104818315041a04d104,0xc1e088c1a1009826060c,0x322b1989838106456260,0xe04c00c8ac4c1b01121f,0x16061a0a06c20e0684e1,0x118341b1038107c25066,0x21450d8488dc20d0a89,0x82b003e240c361a0c2e0,0xe102e106824890308894,0x240e0c206913840c34c2,0x44e1040d22708c260b00,0x242023840902703821a1,0xb81c282f042e287289c2,0xe07042e361787c2e0074,0x5c2f0e89c2e08586c371,0x38143e0850661e1381c2,0xe0c186c270b81c10e0a0,0x961f0b8220178543e088,0x407c1d87c2c221b82c5,0x220ec32670b09c1430e1,0xfe005f821a143ec3e070,0xb82171b81c10b86c4820,0x1785c0e085c60f86e87c,0x2e07042e3f0b81c14285,0xc50e612861be17038217,0x2009c2a1f0382171893c,0x422f038286080f4524f1,0x305c0e0a182041158782])))
def g247H8 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0xd56c0780df6,0x236038001c1707e37bb0,0x85901ebf000642edde00,0x148c88790c51d,0x4001a6cd2b8002630000,0x503000398ae2e014c1fc,0xe3100019361137,0x559e3998ce8000412d4,0xfa000c02ba2511970f80,0x649ced0710ce04db2740,0x925d22178c3811cfcb8e,0x54208f911a57ce30e436,0xc0b80009b54fb32d0,0x3d4371db8a14269e40,0x3dc400000023,0x3f9c9cd1e5ea0d800000,0x7598003c70000572fb9,0xc8dba0211e000282c801,0x3a3c6ac91043fb,0xc76affc1c80500000000,0x6c8d94c000e5a1c892,0x1a8a000000000000000,0x255e0000006b2000,0x103a000694043442d000,0x226896323d042040d56d,0x8c6401e3e3022e82e408,0x201e0000000000000c,0xed0000001c4b04300024,0x2985e0008810105c3845,0x480c800008ee9c00042d,0xed4a000000094cdc7eb9,0x34f717cd1e000d519000,0x12cee8b49935a58d8b,0x1bf17bc21e8d1875c84d,0xaaa97b6b800384c4f306,0xb3985c6869f332e915d8,0x5f10a52537f8ee000a7a,0x41e60ac20e40ff9edcd3,0x83f00052f3d7148b0782,0xc47636524f1a91a920c4,0xbe16a000000004ea6383,0xd400000042c584c00190,0x50000000000c22948821,0xb582a7276e8002895492,0xc4ec9218645170198000,0x45b535b3ab1d22ba8,0x6b95442b08e00053f55,0x2b2c4a3380015b2000b2,0x8fc49c56cee00000001d,0x6231e788001deda70000,0x3a20000000155211295d,0x24d420000015200094cb,0x1db0c6d1fe4980034540,0x5480b2c00000068380,0x1adb382000114126,0x9389c05557824f86800,0xc760002194000,0x99058749810de53422c1,0x4b9cb500079980006522,0x4c189c49ec4900000005,0x9bcb237080009b8000e5,0x420b000000053a5b80e2,0xb6e610900faa338a7f68,0x62500f426ed7d0001851,0x496142da8800184c0000,0xd77ed3d2c87861c00,0x1000db8d08c8c220e281,0x840e1418428144020401,0x8140c58802000c183380,0xc80102200034e2880400,0x403000408a0c0c3030,0x38902100021404386])
def g247D9 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then (word80 [0xc017206c,0x5d0f030b061071786c48,0x2c0c11a1c5e1a0b13011,0x70440817864382c4c014,0xc110245e19110c1b120b,0x30468a4417c006c11a1,0x81a0b105f03046878244,0xc0c11a17185307005c40,0x5448240c317c1201c191,0x307005c6868244c0c11a,0x17185e190f120b030468,0x817860bc4c0c14314231,0x5e0f0b030418706c4c2,0x83c017c11a2000270a0f,0x48061c0945c4c0c2c18,0x3220f0b101b005f04688,0x6c445c0c2c1831c170a,0xf03045c61c830642c41,0x7c0c11a251827120f030,0xb041481746c4c08305c2,0xc121120f0b03045c6174,0x64206c4c083c11424251,0xb0b130304687094683c4,0xc2c0c11a205f100f091b,0x3046880517c446c283c,0xc11a25130a0f03045c6,0x8302c4c0c119185d1a0d,0x81b1303046890617050,0x3c446c2c0c11a2b0b030,0x45c485058483c2c1c017,0x1d145f030b044861283c,0xc2c1171b0a0f03045c5,0x504c283c0c1171e110a,0xf0304685c70384c2c0c,0x117185f13001b0468609,0xc00605c2c1201c5f1043,0x141b04717c4c3c2c00,0x60d1c5f130b001704187,0x17c4c3c2c1060c1c1b02,0x13046850f0786c3c284c,0x11c5b0e130b0430617c4,0xc006c11a181a0b130304,0x68617c41406c0c1831c2,0xc5f120f001b046880642,0xc483c0c11a1c22171302,0xf046dbb6cc35d5aa4d3,0x368a33c59accb364831a,0x587cc175f62f3574cb87,0x5b22d0563caf756a2ad5,0x51ca6b52228853ec9cf4,0xd826352dc94f49624351,0xdc8cf45622550e485341,0x82054ffc7e33e41ea4f1,0xc76f3a61cc4e246ef368,0x1ac4d1c66731e1884c04,0x5e72e816c4b2c57b2ac1,0x4d4a2c4f326c12d49244,0x7322c10c481c3eb1e80e,0xa47143671a20c746042e,0x71600a544fc25f12208a,0x44241f30ea06e433c17f,0xb005042441030760334,0x16409703e017407401b0,0x3ffba2cbff5d165ffe,0xe2b2ffd71597ff32ac9f,0xf59564ffacaaa7ff7155,0x3ffbaac3ff9d561ffaea,0xb0ffc75587ff32ac3ff5,0x9561ffee8b0ffd74587f,0xeb22c3ffd5161ffaa8b0,0xfff64d47feb26a3ff9d9,0x51ffaeca8fff65547feb,0x2aa3ff5d151ffec8a8ff,0xd64547feaa2a3ff99541,0xffacaa0dfd74d96feb8e,0xcb7f5da65bfae932dfd7,0x1996ffba2cb7fdc565bf,0xae832dfd71196febaec9,0x7f5c764bfeeab25ff715,0x93fdb82c97f5db54efac,0xbaa5fd71d52ffbb2a97f,0x5d954efccaaa77d65553,0xdeb22a97fdc554fbeeab,0x1fde7558feebaac7f71d,0x563fbccab1fdd6558fef,0xba2c7f75d163fbac8b1f,0xdf5458feeaa2c7f7dc56,0x3fbae2b1dfd75d877eb2,0xec37f5d361bfeeab0eff,0x655877eb2ac37fdd161f,0xbac6b0dfd76d47beb2ea,0x37f5d351fbac7a8dff76,0x546febb2a3df99551efa,0xcaa8dff74547efb9aa3f,0x758d51feac2a8dff7650,0x6febb2837fdd541bfaea,0xa0fbd64507deaa283f75,0x8d41feac2a0ddd73d96d,0xeba0cb775cc65bdae432,0xdf571196fcb80cb775cf,0x64bf6e0b25f970d536fb,0x2ac7b759563bbae7b0ed,0xd63d876eb1ac377dcd51]) else (word80 [0x85c344c2c0c1171c8217,0xd130b03045c817c4868,0x5c0c2c143205e1b110f0,0xb03046884380c2c14517,0x201e01150f0b045c8070,0x605c384c0c2c117210f0,0xb03045c6c61745c483c2,0xc0c11c20705f0a1b1303,0x468817861cc483c2c0c,0x11a245f110819100f030,0x46870a1c4484060317c0,0xc11a241473105d170b03,0x60c18a4544c2c0c1171,0xc1c8049160d130b07005,0xc9408583c2c117201c70,0x19100f07005c6881c054,0x483c2c0c11720520d130,0x30b061518820094683c2,0x44c1c085245e0f130b03,0x5186888346c4c2c0c11,0xa1c5e11120f0b0305186,0x891705c2c446c0c11a20,0x5d120d1b084b03046898,0x51a44c083c1c246211a1,0x424806a0f01130b04a1b,0x868346c2c044c11a244a,0xf0b0305145c7124584c,0x283c0c1172214030c270,0xb0480706c417c0c2c143,0x1c1817130f005f0b0484,0x40305c2c0c1171c261b0,0xb1303046878544c3c2c0,0xc1171c261a1713030709,0xc80905c2c120145f101,0x41b030b050c845c306c2,0xc0c1841c7016101b0b03,0x50c80945c3c2c120181,0x50f0b0480500c309c2c1,0x1f180f0b0017045c6200,0x5c3c2c0c1171c1b0b021,0x3046868584c3c2c0c117,0x1c8216130f0b03045c88,0x4c205c0c11718170e130,0xb03045c70504c385c2c1]))
def g247H9 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then (word80 [0x2949f,0,0,0x92c083c0008570000,0xc7c00040a0004a140008,0x48000008384600000000,0x121a0000000000c1,0x811c25637da5,0x8001cd6e7fdb9400120e,0x636000000000094c8003,0x62c43500000f4001eb50,0,0x8e491a53f0c5800000,0x1814b750002c0,0x8cd20001468000000000,0x3982,0xef30000003c520000000,0x354000040f800116c0,0x38fd80e61200000,0,0x882756000,0x144100000011fc000,0xb9180029280000001298,0x1105000214c5b20db8,0x4200031ce00000000000,0x188cd2100,0x1038000000000000,0x679989000209e000000,0x74700000000000000000,0x218001c8e0000000,0,0x10cc00000000000,0x406821b2052ecc5400,0x4a2,0xb13,0x52569e3492d6ab228,0xcf0a3996079f80000000,0x706400000000000031,0xe4000000000000000000,0x10f8000c11428497000,0x378001055000,0xdc600000043dc000,0x81600000038600000000,0x106827b2bee0ba0,0x11013800000000000,0x28c0000000734c00000,0x2588234cf4ca8000000,0x195b8ee0000000000000,0x3c94000c2b0002,0xc36c6d000317c0004c40,0x7a4e95d2010003a5c0,0x34c857c2681700,0xe9f613800000,0x30c20e6204,0xd36353c2fdf2d7324000,0xcab47a0000000000b594,0x38109600000000016320,0x96a000000000000000,0x27400000,0xb3dfc3fe18000000000,0x1cbc000b3e0000000000,0x1ccd0001b44,0x183200000001d20000,0xc2f00000000,0x1a7f000229000000000,0x4998000000000000000,0x2510000000000000000,0x18b70000000000,0xc33c2cf5f281e0000,0x1ca800000000000000,0x1e0904d13180,0x11f400071400001d000,0x1e5200021c,0x491c0000000000001abf,0x63724ca6386618002,0x5bac8c963529d1700000,0x1d7a00011b80180,0x2195c7200,0x2c7,0x8000f70f8b8000000090,0x7c780010be0000000000,0x1e0e0000007,0xa8c001cd05358000000c,0x59a12000000161800014,0x2800126e000430800000,0xf678000001f22000000,0x1f170000000ce0000,0xf50800121dc737888003,0x12200000000000017000,0,0x1e10f1500,0x6494000c9a00002d000,0x11d800011e000000,0x1b1d997ebcd1d18778b7,0x4af00048d80000000000,0xc5290230100000000000,0xe71000316131800018,0x2c0a000000000000000,0xd5c8000001e8743a800,0x11302359630,0x3210000010161002040b,0x20a13012000008100002,0x30111030110000000]) else (word80 [0x8df0002a0c000c2df458,0x1e,0xeda05800000000000604,0xc000702000000000182,0xb7316a004992c8222000,0x214400000039abdb4000,0x21740000003114,0xc04000f4e0002cc9b1df,0x431c6c00130d677a9d00,0x7a6c001ca9e6,0xb8002d134f0f1301f506,0x2490f760000000000000,0x3d540006849924000,0x20eff0b0000,0xd24a75ea600000,0x171058300,0,0x59c000000000,0x7834000000,0x43b2b30,0x27a8003c842c50]))
def g247D10 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x170b121c08,0x5043101a24385020851e,0x2430c1604282397880c2,0x430b0a0410c505861214,0x821870c144c30902141,0x404970d0c24283002901,0x82c32e12140824052f12,0x385043101434407021,0x411c34407021410a3860,0xb101c28104d10483052e,0xc24085049041a243810,0x46c46daa8e57881db675,0x5f484ea2cc750c000ffd,0x97fe65ff597fc65ffd93,0xfd64ffd53fd54ffd87fd,0x61ffd47fd51ff507dd63])
def g247H10 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x3a609fb89a8d969cb,0x94d01c00401ca762f9f8,0x908e6c987587240,0x5338e46871655e8c,0x3de215b814d2ab264767,0x696924006b3b3d30800f,0xa3c11640003b6e2554bd,0x8a4126801e0cbca874d9,0x60a1577ddde6b304577,0xa936ca6e001f37218a94,0x716f7ca52939d7192e37,0x56348889274564c6bb1b,0x41df8867000a4f9a45aa,0x5acabb1b42d90c0c65ea,0x3eb80000020462a187ad,0xa34000356000003bd51f,0x7a800000ada2a060800f,0xb911718fbe43cc59c914,0xd030b4a1c48862000811,0x620109086878f0074004])
def g247D11 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x81801022ff
def g247H11 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x9c1770,0x660000880000,0xc5005d00e3,0xa2d16bf984006a0000])
def g247L : Nat → Packing
  | 5 => (6,6,6,0,0,5,0,g247D5)
  | 6 => (101,5,6,0,0,10,0,g247D6)
  | 7 => (293,4,6,0,0,13,0,g247D7)
  | 8 => (294,3,6,0,0,14,0,g247D8)
  | 9 => (110,2,6,0,0,13,0,g247D9)
  | 10 => (14,1,6,0,0,10,0,g247D10)
  | 11 => (1,0,6,0,0,0,0,g247D11)
  | _ => emptyPacking
def g247I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 17 0 7 3 0 g247H6
  | 7 => lookupWord 25 257 4 11 7 0 g247H7
  | 8 => lookupWord 73 401 7 13 9 0 g247H8
  | 9 => lookupWord 73 739 4 13 9 0 g247H9
  | 10 => lookupWord 27 127 7 11 7 0 g247H10
  | 11 => lookupWord 3 37 0 8 4 0 g247H11
  | _ => fun _ => none
def g247 : Forest := ⟨247,11,fun i => g247Y[i]?.getD (0,0),g247C,g247A,g247L,g247I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P5_0 : block g247 5 0 6=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g247B5 : block g247 5 0 6=true := g247P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P6_0 : block g247 6 0 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P6_96 : block g247 6 96 5=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g247B6 : block g247 6 0 101=true := (@block_merge g247 6 0 96 5 g247P6_0 g247P6_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P7_0 : block g247 7 0 5=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P7_5 : block g247 7 5 37=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P7_42 : block g247 7 42 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P7_138 : block g247 7 138 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P7_234 : block g247 7 234 59=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g247B7 : block g247 7 0 293=true := (@block_merge g247 7 0 42 251 (@block_merge g247 7 0 5 37 g247P7_0 g247P7_5) (@block_merge g247 7 42 96 155 g247P7_42 (@block_merge g247 7 138 96 59 g247P7_138 g247P7_234)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P8_0 : block g247 8 0 45=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P8_45 : block g247 8 45 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P8_141 : block g247 8 141 32=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P8_173 : block g247 8 173 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P8_269 : block g247 8 269 25=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g247B8 : block g247 8 0 294=true := (@block_merge g247 8 0 141 153 (@block_merge g247 8 0 45 96 g247P8_0 g247P8_45) (@block_merge g247 8 141 32 121 g247P8_141 (@block_merge g247 8 173 96 25 g247P8_173 g247P8_269)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P9_0 : block g247 9 0 15=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P9_15 : block g247 9 15 64=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P9_79 : block g247 9 79 31=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g247B9 : block g247 9 0 110=true := (@block_merge g247 9 0 15 95 g247P9_0 (@block_merge g247 9 15 64 31 g247P9_15 g247P9_79))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P10_0 : block g247 10 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P10_1 : block g247 10 1 13=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g247B10 : block g247 10 0 14=true := (@block_merge g247 10 0 1 13 g247P10_0 g247P10_1)
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
  · exact g247B5
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
theorem low247 : Lower true (varsX 247) (graphGoal 247) 12 := lower_forest (g:=g247) (i:=0) (hints:=16844101) (before_sound K239 V239) g247G g247T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K247 := extendKnown K239 12 [(247,[]),(251,[80,50])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V247 : Known true K247 := extend_ok (m:=247) V239 low247 (by decide +kernel)
def g253Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfff406e6a2e38f7010,0x230c000003f000000fff])),(BitVec.ofNat 152 (word80 [0x48004e602628b6000,0x210c9249249249249249]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x4530180a85ebff,0x11a80000fc0000fff000])),(BitVec.ofNat 152 (word80 [0x9c00130000a8563bd,0x118830c30c30c30c30c3]))),((BitVec.ofNat 152 (word80 [0xffecb03003c9678551,0x1ed0003f00003f00003f])),(BitVec.ofNat 152 (word80 [0x510c30100189248151,0x1ec06186186186186186]))),((BitVec.ofNat 152 (word80 [0x6bb3edeaa888214,0xc5c00000000fc0000000])),(BitVec.ofNat 152 (word80 [0x9e04bb3eda8a888214,0xc5c279e79e79e79e79e7]))),((BitVec.ofNat 152 (word80 [0x10b8c759f40b063,0x2c600fc000000003ffc0])),(BitVec.ofNat 152 (word80 [0xe0000a007595409042,0xc614514514514514514]))),((BitVec.ofNat 152 (word80 [0x22c13057070590e,0xe157f000000ffffc0000])),(BitVec.ofNat 152 (word80 [0x204010470401802,0x20158618618618618618]))),((BitVec.ofNat 152 (word80 [0x19d049c814980680,0x9c8ffffffff000000000])),(BitVec.ofNat 152 (word80 [0x11c0088800100400,0x80020820820820820820]))),(0x0,0x0)]
def g253C : List ColumnInfo := [(16,0,237,0,11)]
def g253A : List (List Nat) := [[],[80,50]]
def g253D11 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xff
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
theorem g253G : graphValid g253 (boundsBefore K247) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low253 : Lower true (varsX 253) (graphGoal 253) 12 := lower_forest (g:=g253) (i:=0) (hints:=33948931) (before_sound K247 V247) g253G g253T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K253 := extendKnown K247 12 [(253,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V253 : Known true K253 := extend_ok (m:=253) V247 low253 (by decide +kernel)
def g255Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x7fc00000000,0x1ff007fd023c246613])),(BitVec.ofNat 152 (word80 [0x48a45229148a452291,0x48a4522915001c242603]))),((BitVec.ofNat 152 (word80 [0xff8000000007f,0xc0000ff8000400078666])),(BitVec.ofNat 152 (word80 [0xc26130984c26130984,0xc26130984c0000058206]))),((BitVec.ofNat 152 (word80 [0x1ff000000000ff80,0x3fe00000000800381937])),(BitVec.ofNat 152 (word80 [0xc1e0f0783c1e0f0783,0xc1e0f0783c0000080937]))),((BitVec.ofNat 152 (word80 [0x3fe000000001ff0000,0x7fc104040009e])),(BitVec.ofNat 152 (word80 [0x8743a1d0e8743a1d0e,0x8743a1d0e8000000009c]))),((BitVec.ofNat 152 (word80 [0x3fe000000,0xff800018f80e72d])),(BitVec.ofNat 152 (word80 [0x2592c964b2592c964b,0x2592c964b00085086529]))),((BitVec.ofNat 152 (word80 [0xc00000000000000000,0x3ffff0000221f000f8c8])),(BitVec.ofNat 152 (word80 [0x160b0582c160b0582c,0x160b0582c201e000d0c8]))),((BitVec.ofNat 152 (word80 [0x3ffffffff,0xc000000003c1ffff00c0])),(BitVec.ofNat 152 (word80 [0x180c06030180c06030,0x180c060303417a720040]))),((BitVec.ofNat 152 (word80 [0xfffffffffc00000000,0x3fe00000109])),(BitVec.ofNat 152 (word80 [0x201008040201008040,0x2010080400be00000000]))),(0x0,0x0)]
def g255C : List ColumnInfo := [(2,0,253,0,12),(4,0,251,0,12),(8,0,247,0,12),(16,0,239,0,12),(1,0,254,0,11),(32,0,223,0,11),(128,0,127,0,11),(24,0,231,0,10),(64,0,191,0,10),(0,16,173,66,9),(5,0,250,0,9),(40,0,215,0,9),(80,0,175,0,9),(0,1,86,168,8),(0,32,90,133,8),(2,16,173,64,8),(17,0,238,0,8),(33,0,222,0,8),(48,0,207,0,8),(64,16,173,2,8),(65,0,190,0,8),(96,0,159,0,8),(129,0,126,0,8),(144,0,111,0,8),(160,0,95,0,8),(1,16,172,66,7),(1,32,90,132,7),(4,1,82,168,7),(8,1,86,160,7),(32,1,86,136,7),(66,16,173,0,7),(73,0,182,0,7),(100,0,155,0,7),(128,1,86,40,7),(128,32,90,5,7),(40,1,86,128,6),(65,16,172,2,6),(128,16,45,66,6),(129,32,90,4,6),(132,1,82,40,6),(160,1,86,8,6),(161,0,94,0,6),(192,0,63,0,6),(144,2,45,64,5),(168,1,86,0,5),(192,16,45,2,5),(196,0,59,0,4),(208,2,45,0,4)]
def g255A : List (List Nat) := [[],[80,50]]
def g255D6 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0xf624c302591fa6e,0x572d110cbb2e92c2fd5,0x725b0688865d9749647e,0x9b92d8344432ecba462b,0xf71a86c8965d974542b1,0x1fa6d43644b2ecba2a15,0x8a7d26a1b1259765d150])
def g255D7 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0xf08102b3c53c23,0xc010f10102e040000ec4,0x40ec2ac10800006c207,0xb081ec207313b082cc4e,0xc20800004c2077081cc2,0x73081cc204000000638,0x634201e08e04201e09e0,0x42fc007f001fc004c781,0x9aa5888a107f9f87c9ec,0x769d46d9b06a9a464980,0x5b9504c92c49920438fc,0x3a8d8318c02e8b42b890,0x2286c198480d82404800,0xac9fc36c2a9219765d2b,0x2b702b9688865d974aca,0xdc96c1a2219765d332ba,0xe5b0688865d974ccadca,0x6c886e41765d2b2770c8,0x6697905d974acadc2219,0xa5e41765d2b2d7048669,0x7905d974cc9fc3ae8866,0x41765d332bb29b221990,0x5d974dca9c06c8866417,0x65d2b2770c86e95905d9,0x74acadc221ba5641765d,0x2b2d70486e95905d974b,0x49dc321b95641765d2d2,0xb70886e55905d974b4b5,0xc121b95641765d2d2b70,0x886655905d974b4b5c12,0x1995641765d2b27b2c86,0xe8d905d974ac9ec921ba,0x3641765d2b63f0995e8d,0x905d9749c9ecb21ba364,0x1765d2b27b2886e8d905,0xd974bc1dc521ba364176,0x5d2f2370886e8d905d97,0x4bc95c121ba3641765d2,0xa6bf09b869e965d150b8,0xafc26a3965d97454262f,0x72ea8259765d15098bfc,0xb6a0965d974542e2bf09,0xa8259765d150d8aea86c,0x8965d97454362b6a1b22,0x59765d150d8b6a86c496,0x5d97454362d6a1b12597,0x65d1508c9ecb21ba3641,0x765d2b0771486e8d905d,0x974ac8dc221ba3641765,0xd2b2570486e8d905d974])
def g255H7 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x9000aa00000043,0xa200000500000000,0x8000000000000000000,0x81000000640059000000])
def g255D8 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x170813,0x89708238408cd788f083,0x2e34467063386e85f08,0x1504337616c40c670237,0x46705b0811ba36b61073,0x1361043746d4c4d84218,0x762e13c544c131878214,0xc2627e0c319b3082e898,0x5c2c8da20201c1381088,0x4b0309c1381212c0c4f0,0x86342044084231c635c1,0x38112cc786783d13e07c,0x31be0e09c91f00460cf1,0x3c1dc1055f0be006020e,0x502a78904fe07c20c038,0x551b444fe0ec4f85f001,0x511b140bfc1f800a82f8,0xc05d656c5227b13e17c0,0x544017d8bf07627c223,0xc0a87054338067c1d89f,0x3e10f22562f83055f04,0x6d7c0f844683055b17e0,0xfc00be3489055b1560f8,0x3d89f03e1100ab62fc1d,0x8847be10df018bb130d1,0x37c1043f01898be12148,0x22f85f03098d0630bf43,0xf09f0be04281fc2f4304,0xff0be00a0abc2053f81f,0x8500c0abc2f84f83f08,0x2f0d28127526924720f1,0xed19f1511190e1093071,0x39016fc8f90f2cef4eb,0xce84e36dfedc6d8ed82d,0x4ad12caec76c3ebdab4a,0xae6a2a9848c883877c6d,0x66305744e442839834a2,0xd024019a1200900015f3,0xec985e4d805daadedaf4,0xcbd0cba55bfb568197a,0x1974cb7f4ad032f432e9,0x96f695a065e865d3acfd,0x9b40cbd0cba6cbdb0aa4,0x865d974d97f0cd2f20bb,0x2e9b2f219a5e41765d2e,0x5f5d10cc82ecba5cbeb9,0x219905d974d97f0dd2b2,0xbb2e9b2f21ba5641765,0xd3a5fc372ac82ecba74b,0xc86e55905d974e97f0cc,0xab20bb2e9d2f21995641,0x765d36ce5c746c82ecba,0x6d9f95e8d905d974db3b,0x2bd1b20bb2e9f27e1ba3,0x641765d3e4e43746c82e,0xcba5dafb269576e0174b,0xb5f64d2aecba2c1a6fae,0x1a7a59745434dedc34f4,0xb2e8a878bea8e59765d1,0x50f17b51cb2ecba2a172,0xfae8965d974543c5f541,0x2cbb2e8a878bda825976,0x5d150a79f64c2f26c02e,0xd567ecda065e865d3657,0x5cb44432ecba6cadb068,0x8865d974b87b6a43720b,0xb2e97276cc86e41765d2,0xe56d910dc82ecba5cb5b,0x121b905d974997d74433,0x20bb2e970f6d48664176,0x5d2e4ed990cc82ecba5c,0xadb2219905d974b96b62,0x43320bb2e9b27e1ba364,0x1765d364e43746c82ecb,0xa5cafb2695765d360b95,0xf64d2aecba2c166bec9a,0x85d974542e56d912cbb2,0xe8a85cb5b1259765d150])
def g255H8 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0xe,0x740051ca4771c0000000,0xb1800000,0x11000000264000,0x63e004000000000038,0xdf870000000000000113,0x90c002a5800000,0x110aa5000a60000000,0x23800000b48e200000,0xe2a0000000000000000,0,0xbb00,0x4020000000000000,0xc800064e00000000,0x90000000000000e68000,0x80a000007d90000024,0x790492904800000001a8,0xe2f80c00000000,0x286800000000000000,0xa18000e400,0x2ac24fc5b8a00000000,0x691000000,0,0x1e240071e00,0xc580000000000000000,0x1e98004570024c0100])
def g255D9 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then (word80 [0xf07c0f08,0x280988c4ec4e0e1670bc,0x1f00282016f0428f0bc0,0xb4608b4670629e13c2f,0xfc08549717c1f0bc084,0xc261829717c1f0bc084c,0x261e1870615e13c0f0fc,0x28a08f06c608fc0f0f15,0x1a1715c8861343f07c0f,0x828098a85d4961343f0,0x7c0f08280989613c1f0b,0xc084c28189590f84f07c,0xf08570a0850fc2f0094,0xa0950987c105845946f,0xfc1257c2f02142b48e1,0x7c3f03c209c6e178451b,0xc3f07c2f007e178451bc,0x3f07c0f08709785124c8,0xe13c1f0bc0238514f84d,0x1bc1f084f1f43e1053d1,0xbc2f00a01f43e1784f07,0x46f085e1f85f0421f0bc,0xb4642743087c1f03c2,0x644742429e1743f07c2f,0x21208801bc1647c2f0,0x2d1c176342dd0f85e13,0xc1f03c214ca0842ae142,0x2e13c1f03c214c901b84,0x87c1f0853f019121912,0x564614fc1f0bc0250808,0x821f17c40a813f07c2f0,0x9e0fc1153c0f082819c,0x2e0e16c4fc1f002c1e48,0xe1bc1f0fc00706839c2d,0x1784f0786f0fc022c504,0xf84f07c2f00221d8484f,0x43f07c0f08281c1805f4,0x3f06c5f03c2250804fc1,0xf0bc0098505818254ce3,0x1614c37c3f0bc1f00bd1,0xb85f0fc2f001b18c805f,0x43e17c1f03c2084823a1,0x88590d723c3f07c0f081,0x128118100623bc3f07c0,0xf090d25c1f1013183c2f,0x6f17c4f07c20785084,0x54f1413f07c2f0070889,0x504f84f07c2f007a5151,0xaa8793fa9e14e7a6e134,0xc9804aaa4bd1fe8d9459,0xa1f909281e3f99f0cf26,0x76d3a11c5cdec6c63529,0x9fcca86332ff1738b5a5,0x822ae149ca0c4e025d12,0x3c8d244320e8ff07ac3a,0xb1c28d406402f51650a6,0x84f2253119081c3c21bb,0xc805d027411907702e4,0x1120680260098000df7e,0x179360176df761793601,0x76f6fe55905d974f6f65,0x5905d974f6f69576e017,0x4bfbe89955d960f6fe95,0x765d160f6f695765d160,0xcf7e179360176cf76179,0x360176d6fe8197a1974d,0x6f68197a1974deb68192,0x21974f2fe1b905d974f2,0xf21b905d974b6f697905,0xd974d6fe57905d974f2f,0xe19905d974f2f219905d,0x974b6fe95905d974d6fe,0x55905d974d6f655905d9,0x74f67e8d905d974f6ee4,0x1905d974bbbe89955db6,0xf2fe95765d360f2f695,0x765d360bbbe89955d960,0xaf7e8d8759560f2fe957,0x65d160f2f695765d160f,0x6ee81765d160f2f5db95,0x5d160f2f5d9655d160f5,0xe5d5655c160afbe89985,0xd950a7f69f865d950a7f,0xe9d865d950b6f69e965d,0x150bede85965d150beb6,0x88965d150bed684965d1,0x50e6fea1765d150e6faa,0x1765d150e6f6a1765d15,0xe6f2a1765d150f2fe59,0x765d150f2f259765d150,0xe6fe19765d150e6f6197,0x65d150b2faa4865d974b,0x2f680865d974b67e8d90,0x5d9748f7e8d98a19708f,0x7e8d96e1570e2f5d9855,0xd360f2ee81765d160e2f,0x5db855d160b2f69f655d,0x160f1e5d5655c1608fbe,0x89985d950e2f619765d1,0x50e5ee19755c150e5e61,0x9755c150b2b688865d97,0x4b2d684865d974b2e680,0x865d974e0f5d9855d360]) else (word80 [0x7152,0x6092666195705c514d1b,0x8280984316c2704c40a,0x261898d11c146617178,0x48a3140d91610260a047,0x7840a03544c2717c1f0,0xfc04987660cb71544f07,0xc0f0d2621c5713c1923c,0x2f00251e09095c5921c4,0xe0fc1f03c2278371213e,0x1bc2f00601ec545fc1b1,0x3c2f002d1c2605ec5087,0xc144ec4f0bc00a8a05c8,0x906383b13c1f09c5f002,0x22828314c4f0426f0bc0,0xb480b6c5f06c445fc0f,0x91320260842ab17c1b1,0x3c0f09132492226c4e0f,0xc1f0bc0714222517a0fc,0x1f03c2098281cc4a0d83]))
def g255H9 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x1c6e928866,0x2c27c13ddea18007e500,0x9b0004213920004dd5b,0xb2be44000009080bc0fa,0x8200283c00789894e771,0x372d0000014600000133,0x79ea1c00c00198e0a,0xa93747b0a0f0ab440000,0x31d13a1c5280028b00,0x1a89f26df00000000,0x2b001a970825ce01308,0x50a0012b956532889a,0x5d4c800d52ea3272a3d6,0x3c6a1000028200050621,0xd050220810023c6043])
def g255D10 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then (word80 [0x385c1631,0x248c2f0e8dc2e0f001a4,0x70787c0e10544230230b,0xc3e0d1b85c0069029a36,0x1787c0e17041a41200d8,0x5e1f0385c11090210be1,0x28653a370781c2489417,0x48d0ca785e1707802125,0x1017c8d0c438529e1383,0xc2e0160d8b51b87c1e07,0x82240478785e0707854,0x60691c5e20278248e170,0x7e2f101fc1c3708263e,0xd83c43061b85c00991c,0x5c1f138386e107871095,0x38bc1c370b8013238a17,0xe270785c0098fc5e2707,0x85c0098dc1e070820131,0x444156361383c3e17008,0xe0f0b8028098a16e2e13,0x83c2e004c7c27068dc2e,0x4c68b6228dc1e1f004,0x63a5286210bf1427c1c2,0x703845058228e42c3431,0x4e1f0b83c02e1cc85fa,0x15d84aa0d381f202e7f8,0x1f897cedef67ac5e6c78,0x79dd075c1d347375c8f7,0xe1bea6e4db3c6bb9aa0,0x69499fb66b5944636d87,0x260257b25d917285bb16,0xb059415f956ad55d54a9,0x4e5528145250353c84da,0x13234b792a2497520f47,0x2917c44b90e042490564,0x20fba3db0f1e3b64e94,0x3918e0a3714d8034c8cd,0xb327cc5a3054bc72e08b,0x2b2b74a6b28749b42598,0x906232887c20dc7f21ed,0x875f1c446d51a1c63917,0xac58b14d04cb11f442f0,0xfa83a50d5c3120b1027f,0x90c210070818f052810,0xe03240690003fff0ac02,0xedffd8560176fffcaaec,0xb07ff65576582ffb2bc0,0x2edbff85e0176bffcab0,0xbb6ffe15805db7fb0ac,0x2edfdf9360176ffdc03,0xbb7bfe5576d83dfb2a,0xbb6c1eff955d960f7eca,0xaecb05ffe5576583ff72,0xbb2c1bfd8759560f7eb,0xb2cab07efe5574583f7a,0xcaba2c1ff9655c160dff,0xcc2eca86ffa61765437f,0xb30bb2a1bfc985d950df,0xfc32eca86ff61976543f,0x7f2cba2a1fbe965d150f,0xdecb2e8a87ef25974542,0x7fb2bc02ed7df9360176,0xbdec850cba5efe41865d,0x2f7b20432e9dbf905d97,0x4edec82ecba5ef65b805,0xd3b7aedc02e97bd95e01,0x74bdfcab00ba6efe1580,0x5d27fb2bc32e13fd98a1,0x970afecbd0cb85df6568,0x65c2ff321432e17df936,0x1970bfdc830cb84ff65b,0x855c27ff2ac3ec16ff95,0x5db60dbecbb0bb06bf5d,0x985d827fb30baec1b7d8,0x55d760ddec2ae9b04ff6,0x57875827ff2ac3ac1bdf,0x9361d60dfdc830eb05f7,0xe4d87582dfb2b3b2c16f,0xf955d960f7dc82ecb05f,0xee41765827fb2fc2ac1a,0xfd76e1560bfdc82eab05,0xbf65f655835fb0fb2ac1,0xaff8759560d7ec3acab0,0x76f5d97458377f0aba2c,0x1ebf655d160f5eb2ae8b,0x6fee1570583bf2eab82,0xc1efb655c160f7cb2ae0,0xb04ff65b875427ff2cc3,0xaa13fd97e19509fecc50,0xca85fe642865427ff2ec,0x32a13fd989d950d7ec34,0xeca84ffe61765427fb30,0xbb2a1afd865d950ddfc3,0x2e8a86ef61974543b7ae,0xcba2a1bfb865c150dfcc,0x32e0a856f65e865d2f6f,0x22c32e97ad9221974bda,0xc890cba5ee640865d397,0xf0cbb2e9cbc865d974ad,0xfcbb00ba69f5d985d833,0x7b0eba6c1cbd765d360d,0x9ec2ae9b04f7e4d87583,0x97aecba2c1d79755c150]) else (word80 [0x51a14505026152a,0x45a13062844140988134,0x5050186982158a0a050c,0x6218bc1a270f85c01113,0x882291383c0e1f085026,0x271144e1f0780c5e1088,0x808e2383c0e1f084c282,0x310452270387c1e10a04,0xc4c5a28c2a270781c314,0x10160a70787c0e10a078,0x431783c3e07084c38a42,0xbc1e1f0384261e1084e0,0xf0387c21409880aa1381,0xc3e0f085026201ac508c,0x2383c3e070a8c1a2b83c,0x3e07082828181c058431,0xb83c3e07083a485429c1,0xe070f842813109410e11,0x8bc1e070826572709c10,0x9d1b85c04aa50806c5b8,0x346e1f0384144a920648,0xd230bc1e1f0384212690,0x21a370787c0e12448a40,0xa70bc3e0707842122902,0x1e0f0f81c2a32448c212,0x43c3e0f038546489291,0x370f83c0e105442405d,0x1a4348e1709c1a370b80,0x532e862148e149346c27,0x785c064162226244438,0x5a361383c2e014cb1124,0x68621c2e138346e1700a,0x658618b86e151383c3e0,0x389c34598514e0f0386,0x2c2013c1e07084254182,0x7c1e070842191827c1e1,0x7004254198b838985c51,0xc0e0b13842f298ac4c1c,0x4c2c28e0f038448888a1,0x3e085f85c00c902fa271,0x42fc1e170048470785c0,0x110905a261b82c5e1700,0x2639468986e0f0384131,0xd8b84e1e1b85c1e00388,0x2461b83c3e07083a3923,0x9c3e0f03841d1d8b840,0xd1230dc1e1f03840d2b0,0xdc1e1f0029c20e8f848a,0x70787c00ec587e1f0780,0x16e107460761b83c3e07,0x83a382309c3e17068dc,0x711c38451b85c1e006,0x878461387c263707800e,0x201145c270f85c1e0088,0x84451b09c2e1f07800e2,0x11184e1f0b83c0a30388,0xc27068dc2e004c608e13,0x8746e1707800e218b84a,0x370f85c1e003888b00a8,0xc1de0f0f801c202816a3,0x70787c0e107488b51b83,0xc3e0076283d1b83c3e17,0x2a141e1011e1d1b85c,0x1e006880a70f83c0e10a,0x6a37078614e07083a3b,0x1a8bc1e1f0384141c30c,0x6a2f0781c3e105084202,0x28d45e1f0781c2069214,0xe1f0781c2130cc6e0f0f,0x8014e107470ab1b83c2e,0x70c283c200ac6e1f078,0x1c20e9046e284f83c2e0,0x25070b826874662f0785,0xc04a1291423178346e17,0x26427535434aa50274,0x662f0b83c0c21816a370,0x58bc3e07082841603418,0x86c502dc3e0f0384c52c,0x2d46e0b1787c0e105088,0x68562c14e1d1b83c0e13,0x14ae1d1b83c0e1044606,0xe1709c3a370781c22042,0xc6e0f0387c2088e48c2f,0xf81c2e08847e1f0385c,0x108884606c470b84e1f0]))
def g255H10 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [4,0xa800000001812ca23f22,0xe1ff0a38131070381600,0x617c41e11da9f3c63af,0x1e000000c07000609c2b,0xfb931489b9aa442b3770,0xc1280000002b50005380,0,0x9bca247b298,0x75bd50fa2000020e21b4,0xbf000000829000000e00,0x619000f31dba00,0x7a0d25c3b5045,0x3de12000000bc2000000,0xb35000000000000bab5a,0x3534c2d001a300007a59,0x2ea43e2a927802b0d7b8,0x53f74031d0007be921e1,0x55af3a600080b00031c0,0x5913000db6000000,0x326000c06000d9,0xdb10000003c1d890000,0xd39932e83,0x21a536000e2f000a3,0x360843e0000804014033,0x53f015092042c1603c0d])
def g255D11 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x2a45888644c1c3c2c0,0x282a1915105853070f03,0x8a0a4584c3c1c0c2161,0xd2210530f07030858748,0x18161184450dc3c0c1c2,0x292c68611916130f0b07,0x220a1646c1c3c0c2141,0xd2023151b070f0308508,0x151145c3c1c0c2142124,0x621114530f030708a09c,0x6c1c2c3c015141c60584,0x61118370f030b04a4b84,0xc3c0c2c111211c561453,0xf030b04448492111858,0x4c146c3c2c0482820461,0x122451a170f07030884c,0xc586c1c3c0c2141e2015,0x10770f07021b089c5c48,0x3c1c2c01317220f17121,0x827070b012090cc5c486,0xc1c2c013231511160f13,0x61b0b004ca13c544c1c,0x2c0171d161913070b004,0xc726c5c3c1c0c2161c21,0x170f030b045871d1a181,0x6c345c2c1c08428151b0,0x70c230308a0816c54684,0x8c1c3c0c2271a13070b,0xf005478584c146c2c01,0x31c151b07030f0850784,0x140516461dc1c3c0c22b,0x17051b030f0850721081,0x4c584c3c1c0c24628191,0x7070f0b005070445c1c3,0xc2c0141c746854531917,0xf0b070210b43211794c,0x5841346c1c0c22c37145,0x8530f0703091890846c3,0xc1c0c2111c5844602214,0x351b0f0b0700a4c4884c,0x6c3c1c0c211205484504,0x71a16130f0b0700b4317,0x9882191858446c2c1c0,0x30584436170f03070918,0x90683c5c413c1c2c0205,0x7182213070f0b008df2d,0x9cd56d10cb2c5cc16bd0,0xb82b34af6a98a5aa0c9b,0x69509128c487e8307ea7,0x947567186da69c646600,0x5b25745364f84a246440,0xe3d03923342d628824a1,0xe419e1400da08c046000,0xfff805dbff60176ffe86,0x5c3ff61970ffd855c3ff,0x5d760ffd87583ff5d960,0xffd85583ff5d560ffd65,0x583ff61d50ffe86543ff,0x61950ffe76543ff5d950,0xbfd809daffe0176fbf86,0x5d3efa1974fbd865d3ef,0x21974fbf805d3ef60174,0xbff865c2ffe1570dfd75,0x5c2ff61f60efd76d82ff,0x61760fbd74d82ffe1d60,0xbfd87583bf9d960efd76,0x582ffe1560eff65583bf,0x59560fbd74583fe5c160,0xbff87542ff61d50bff86,0x542ff61950fbd74543fe,0x5c150dbd765d2df61760])
def g255H11 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0xf2a42176a1,0x1c5a700043d000e4bdef,0x7e563e0000000002387e,0x150000d1784ebe4a654,0x5923599ad4996981ea48,0xfa668400000000a000d8,0x1a5e7aa000a31f288660,0xe2e555211c4a4e6b4c,0x80fe360006cd033f2,0xba6f46c86400070571f7,0x436ea000000a6323208f,0x434d10000000d00e3,0xa237c6ec71590a1695c0,0xc18e70567bab91ba19,0xbb1000000000000fa0c0,0x912f00098a00084d000f,0x9f76b947000361020000,0x2ce15142200000050311,0xa1dc0121060009c90000,0x442000,0xbccbf1a27a0c000dcb00,0x8c14441039000f5bc609,0x68000e5623b5c6145000,0xa07fa41de00040e00,0xf23329d4f000e1d0000,0xd0215d66dd5f000,0xccf0007b082451,0x35629539529e2b043575,0x46444c582a140d6a8454,0xb0168c30b43c03ffe36a,0x901582cf5a0bc1ee000e,0x2d340c25000d26430000,0x6be3c724c20000108,0x202115204180010e1036,0x45040a07000150089051])
def g255D12 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x458,0x9043428700410222c40d,0x61c2804082d14304830,0xe042242c68a120c38500,0x412504468a120c381089,0x1046305090e141804838,0xb1034185007c4d2e0cc1,0x3e0dc01ff9dbfebb7fd7,0xffec1ff583fea87bd74])
def g255H12 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x728000000000,0x3848000000000068,0xb000000cb29500000000,0x538f500000000d,0x48800000a1c0060c0000,0x34dd1f000000000c200,0x2d385000000000,0x217cad000000000,0x3480034558192449c0,0x5200000014d000e5200,0x3cc00000000000,0x71744492dec8004,0x4c000000000000000011,0x16680000000000,0x65c66000000b54002,0xf7800c1c001688000000,0x11e0000000000000,0x10c800,0x723000000001,0x86000000000000000000,0x4880000000000000000,0xedc,0x204592002c10000,0xe94078000000000000,0x5bc97c0000000000000,0x1e3400000000000,0x72b000000000000000,0x2ce800000003f400062,0x60000000000000000000,3,0x5b58000000000009600,0x44f0000000000000000,0x42100000000000738,0xa0000000000103018401])
def g255D13 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1851010c2007ff
def g255H13 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0xfc60139a00,0xb1447b95000082a60008])
def g255L : Nat → Packing
  | 6 => (6,7,6,0,0,5,0,g255D6)
  | 7 => (40,6,6,0,0,10,0,g255D7)
  | 8 => (51,5,6,0,0,12,0,g255D8)
  | 9 => (68,4,6,0,0,13,0,g255D9)
  | 10 => (114,3,6,0,0,14,0,g255D10)
  | 11 => (48,2,6,0,0,12,0,g255D11)
  | 12 => (7,1,6,0,0,9,0,g255D12)
  | 13 => (1,0,6,0,0,0,0,g255D13)
  | _ => emptyPacking
def g255I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 2 37 0 8 3 1 g255H7
  | 8 => lookupWord 12 181 3 11 6 1 g255H8
  | 9 => lookupWord 17 97 6 11 6 1 g255H9
  | 10 => lookupWord 24 157 5 12 7 1 g255H10
  | 11 => lookupWord 38 211 6 12 7 1 g255H11
  | 12 => lookupWord 16 241 3 11 6 1 g255H12
  | 13 => lookupWord 2 17 4 8 3 1 g255H13
  | _ => fun _ => none
def g255 : Forest := ⟨255,13,fun i => g255Y[i]?.getD (0,0),g255C,g255A,g255L,g255I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P6_0 : block g255 6 0 6=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B6 : block g255 6 0 6=true := g255P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P7_0 : block g255 7 0 4=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P7_4 : block g255 7 4 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B7 : block g255 7 0 40=true := (@block_merge g255 7 0 4 36 g255P7_0 g255P7_4)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_0 : block g255 8 0 20=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_20 : block g255 8 20 31=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B8 : block g255 8 0 51=true := (@block_merge g255 8 0 20 31 g255P8_0 g255P8_20)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_0 : block g255 9 0 4=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_4 : block g255 9 4 14=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_18 : block g255 9 18 42=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_60 : block g255 9 60 8=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B9 : block g255 9 0 68=true := (@block_merge g255 9 0 18 50 (@block_merge g255 9 0 4 14 g255P9_0 g255P9_4) (@block_merge g255 9 18 42 8 g255P9_18 g255P9_60))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_0 : block g255 10 0 15=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_15 : block g255 10 15 67=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_82 : block g255 10 82 28=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_110 : block g255 10 110 4=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B10 : block g255 10 0 114=true := (@block_merge g255 10 0 82 32 (@block_merge g255 10 0 15 67 g255P10_0 g255P10_15) (@block_merge g255 10 82 28 4 g255P10_82 g255P10_110))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_0 : block g255 11 0 2=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_2 : block g255 11 2 30=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_32 : block g255 11 32 16=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B11 : block g255 11 0 48=true := (@block_merge g255 11 0 2 46 g255P11_0 (@block_merge g255 11 2 30 16 g255P11_2 g255P11_32))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P12_0 : block g255 12 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P12_1 : block g255 12 1 6=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B12 : block g255 12 0 7=true := (@block_merge g255 12 0 1 6 g255P12_0 g255P12_1)
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
  · exact g255B6
  · exact g255B7
  · exact g255B8
  · exact g255B9
  · exact g255B10
  · exact g255B11
  · exact g255B12
  · exact g255B13
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255G : graphValid g255 (boundsBefore K253) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255R : Impossible true graph 13 sevenInputs.toFinset := by
  rw [show graph = targetOf g255 by decide +kernel]
  exact root_index (g:=g255) (top:=13) (i:=0) (before_sound K253 V253) g255G g255T (by decide) (by decide +kernel)

end PEqualNP.Outside.L_meta_32321

open PEqualNP.Outside.L_meta_32321 in
theorem PEqualNP.Outside.L_meta_32321 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 2, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 2, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o fit _ correct
  exact replaceShort g255R gates o fit correct

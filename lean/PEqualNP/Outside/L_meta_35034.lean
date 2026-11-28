import PEqualNP.Defs

-- The two-mode live-state and cofactor checker follows L_meta_1674 and L_meta_670.
-- The graph, restrictions and all search certificates below are for L_meta_35034.

-- Shared forest and cofactor certificates from L_meta_1674 and PR 11111 for L_meta_1677.
-- The original credit line is retained below. The two root certificates here cover the unpinned graph.

-- The checker and the bound certificates are adapted from PEqualNP/Outside/L_meta_1667.lean (Apache-2.0).
-- Two modes: u=false are monotone runs (AND, OR); u=true are runs up to complement, where negation is free.
namespace PEqualNP.Outside.L_meta_35034
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
def graph : Sig := (BitVec.ofNat 512 (word80 [0xffffffff,0xfffffffffffffffffffe,0xfffefffffffefffffefe,0xfffefffceeeeaa00ffff,0xffffffffffffffffffff,0xfffefffefffffffeffff,0xfefefffefffceeeeaa00]))
def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 5) || (x 3 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 2 && x 6) || (x 4 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 2 && x 7) || (x 3 && x 7) || (x 5 && x 7) || (x 6 && x 7)
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
  (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 1 &&& x 5) ||| (x 2 &&& x 5) ||| (x 3 &&& x 5) ||| (x 0 &&& x 6) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 4 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 2 &&& x 7) ||| (x 3 &&& x 7) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)
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
  (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 1 &&& x 5) ||| (x 2 &&& x 5) ||| (x 3 &&& x 5) ||| (x 0 &&& x 6) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 4 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 2 &&& x 7) ||| (x 3 &&& x 7) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)
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



def target (x : Fin 8 → Bool) : Bool := decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
def smallCircuit : Circuit := ⟨[⟨.or,[0,6]⟩,⟨.or,[1,8]⟩,⟨.and,[4,9]⟩,⟨.or,[8,5]⟩,⟨.or,[6,3]⟩,⟨.or,[1,2]⟩,⟨.or,[13,0]⟩,⟨.and,[12,14]⟩,⟨.or,[7,15]⟩,⟨.and,[11,16]⟩,⟨.or,[3,13]⟩,⟨.or,[5,7]⟩,⟨.and,[18,19]⟩,⟨.or,[17,20]⟩,⟨.or,[10,21]⟩], 22⟩

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
def g81Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3ff63ff63ff63ff63f,0xf63ff63ff63ff63ff63f])),(BitVec.ofNat 152 (word80 [0x492049204920492049,0x20492049204920492049]))),(0x0,0x0),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xc7fbc7fbc7fbc7fbc7,0xfbc7fbc7fbc7fbc7fbc7])),(BitVec.ofNat 152 (word80 [0x924092409240924092,0x40924092409240924092]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xf8fdf8fdf8fdf8fdf8,0xfdf8fdf8fdf8fdf8fdf8])),(BitVec.ofNat 152 (word80 [0x248124812481248124,0x81248124812481248124]))),(0x0,0x0),(0x0,0x0)]
def g81C : List ColumnInfo := []
def g81A : List (List Nat) := [[],[100],[64],[64,96],[96,64],[96]]
def g81D3 (j : Nat) := if j=0 then 0x7 else 0
def g81L : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,g81D3)
  | _ => emptyPacking
def g81I (_ _ : Nat) : Option (Nat × Nat) := none
def g81 : Forest := ⟨81,3,fun i => g81Y[i]?.getD (0,0),g81C,g81A,g81L,g81I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g81P3_0 : block g81 3 0 1=true := by
  apply cellsBlock (ar:=3) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g81B3 : block g81 3 0 1=true := g81P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g81T : checkedTables g81 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g81 0 0 0 = true)
  · exact (rfl : block g81 1 0 0 = true)
  · exact (rfl : block g81 2 0 0 = true)
  · exact g81B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g81G : graphValid g81 (boundsBefore []) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low81 : Lower true (varsX 81) (graphGoal 81) 4 := lower_forest (g:=g81) (i:=0) (hints:=4) (before_sound [] baseKnown) g81G g81T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K81 := extendKnown [] 4 [(81,[]),(82,[16]),(137,[67,118]),(162,[16,84,118]),(164,[32,16,84,118]),(168,[48,16,33,84,118]),(193,[100,84,117]),(194,[16,100,84,117]),(196,[32,16,100,84,117])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V81 : Known true K81 := extend_ok (m:=81) baseKnown low81 (by decide +kernel)
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
theorem g27G : graphValid g27 (boundsBefore K81) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low27 : Lower true (varsX 27) (graphGoal 27) 4 := lower_forest (g:=g27) (i:=0) (hints:=67) (before_sound K81 V81) g27G g27T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K27 := extendKnown K81 4 [(27,[]),(43,[80,16,49,67]),(45,[80,16,33,50,67]),(51,[16,83]),(54,[16,32,67,83]),(57,[48,65,33,80,32]),(58,[16,48,32,66,82]),(75,[100,84]),(99,[16,83,100]),(101,[32,16,83,100]),(105,[81,33,99,67]),(106,[16,48,32,98,84,66]),(116,[32,65,83,97,49]),(150,[16,32,67,115,83,101]),(154,[16,48,32,66,114,82,101]),(177,[112,65,33,83,32,50,99]),(216,[96,49,32,65,113,81]),(240,[112,65,32,83,97,49,50])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V27 : Known true K27 := extend_ok (m:=27) V81 low27 (by decide +kernel)
def g83Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfe7d01c7fc0fc7cfe7,0xd01c7fc0fc7cfe7d01c7])),(BitVec.ofNat 152 (word80 [0x51d124928a290a051,0xd124928a290a051d1249]))),((BitVec.ofNat 152 (word80 [0x3f8b8e38fff007f3f8,0xb8e38fff007f3f8b8e38])),(BitVec.ofNat 152 (word80 [0x884b924930c3210884,0xb924930c3210884b9249]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x3fe7703ffffff803fe,0x7703ffffff803fe7703f])),(BitVec.ofNat 152 (word80 [0x100024924104020100,0x2492410402010002492]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xc018ffc0fffffffc01,0x8ffc0fffffffc018ffc0])),(BitVec.ofNat 152 (word80 [0x200049248208040200,0x4924820804020004924]))),(0x0,0x0),(0x0,0x0)]
def g83C : List ColumnInfo := [(1,0,82,0,4)]
def g83A : List (List Nat) := [[],[100],[16],[16,100]]
def g83D4 (j : Nat) := if j=0 then 0x1f else 0
def g83L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g83D4)
  | _ => emptyPacking
def g83I (_ _ : Nat) : Option (Nat × Nat) := none
def g83 : Forest := ⟨83,4,fun i => g83Y[i]?.getD (0,0),g83C,g83A,g83L,g83I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g83P4_0 : block g83 4 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g83B4 : block g83 4 0 1=true := g83P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g83T : checkedTables g83 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g83 0 0 0 = true)
  · exact (rfl : block g83 1 0 0 = true)
  · exact (rfl : block g83 2 0 0 = true)
  · exact (rfl : block g83 3 0 0 = true)
  · exact g83B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g83G : graphValid g83 (boundsBefore K27) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low83 : Lower true (varsX 83) (graphGoal 83) 5 := lower_forest (g:=g83) (i:=0) (hints:=68) (before_sound K27 V27) g83G g83T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K83 := extendKnown K27 5 [(83,[]),(166,[16,32,84,118]),(169,[81,33,50,67,118]),(170,[16,48,32,84,118]),(172,[32,49,84,118]),(195,[100,84,117]),(197,[33,100,84,117]),(198,[16,32,100,84,117]),(201,[48,97,33,32,64,84,117]),(210,[64,113,32,50,49,83]),(226,[80,97,32,50,65,116]),(228,[80,97,32,49,66,67,116])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V83 : Known true K83 := extend_ok (m:=83) V27 low83 (by decide +kernel)
def g85Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfdf00fff81fc7e3ffb,0xe01fff03f8fc7ff7c03f])),(BitVec.ofNat 152 (word80 [0x45c09245142904808b,0x81248a28520901170249]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xe6a8703ffe007fc7cd,0x50e07ffc00ff8f9aa1c0])),(BitVec.ofNat 152 (word80 [0x96a9b6d618b228112d,0x536dac316450225aa6db]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfbb781ffffff8007f7,0x6f03ffffff000feede07])),(BitVec.ofNat 152 (word80 [0x235249820c0312204,0x6a49304180624408d492]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x64ffe3ffffffff80c,0x9ffc7ffffffff0193ff8])),(BitVec.ofNat 152 (word80 [0x249204100400400,0x4924082008008000924]))),(0x0,0x0),(0x0,0x0)]
def g85C : List ColumnInfo := [(4,0,81,0,4)]
def g85A : List (List Nat) := [[],[64]]
def g85D4 (j : Nat) := if j=0 then 0x1f else 0
def g85L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g85D4)
  | _ => emptyPacking
def g85I (_ _ : Nat) : Option (Nat × Nat) := none
def g85 : Forest := ⟨85,4,fun i => g85Y[i]?.getD (0,0),g85C,g85A,g85L,g85I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g85P4_0 : block g85 4 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g85B4 : block g85 4 0 1=true := g85P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g85T : checkedTables g85 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g85 0 0 0 = true)
  · exact (rfl : block g85 1 0 0 = true)
  · exact (rfl : block g85 2 0 0 = true)
  · exact (rfl : block g85 3 0 0 = true)
  · exact g85B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g85G : graphValid g85 (boundsBefore K83) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low85 : Lower true (varsX 85) (graphGoal 85) 5 := lower_forest (g:=g85) (i:=0) (hints:=1540) (before_sound K83 V83) g85G g85T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K85 := extendKnown K83 5 [(85,[]),(86,[16]),(89,[64,50,96]),(114,[64,16,82,50,97]),(139,[33,67,118]),(141,[67,118]),(153,[48,66,32,112,96]),(163,[16,32,84,118]),(165,[32,84,118]),(178,[80,16,66,50,115,49,97]),(202,[16,50,100,84,117]),(204,[32,16,49,100,84,117]),(212,[32,16,65,49,115,83]),(225,[82,50,100,116]),(232,[48,16,98,84,66,116])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V85 : Known true K85 := extend_ok (m:=85) V83 low85 (by decide +kernel)
def g47Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x1fff0007ff803ffc01,0xfffffffffff245f3f007])),(BitVec.ofNat 152 (word80 [0x502a8350250681482d,0x550950a414040f37b6d]))),((BitVec.ofNat 152 (word80 [0x1ffffff800003fffff,0xffe001ffe001b15bc038])),(BitVec.ofNat 152 (word80 [0x854c2a62b62b159148,0x2986d84c8661a159c6db]))),((BitVec.ofNat 152 (word80 [0x1fffffffffffc00001,0xfffffe00000ce425d1c0])),(BitVec.ofNat 152 (word80 [0x6703383384c19e270,0x4e04e06f0b88a425d6db]))),((BitVec.ofNat 152 (word80 [0xe00000000000000001,0xfffffffffff22fedae07])),(BitVec.ofNat 152 (word80 [0x7803c03c0701e0380,0x700700700c022d0c8492]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffffffffffffe,0xdfa9e5ff8])),(BitVec.ofNat 152 (word80 [0x1800c0040000200001,0x80180180100452820924]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
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
theorem g47G : graphValid g47 (boundsBefore K85) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low47 : Lower true (varsX 47) (graphGoal 47) 5 := lower_forest (g:=g47) (i:=0) (hints:=1049939) (before_sound K85 V85) g47G g47T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K47 := extendKnown K85 5 [(47,[]),(62,[64,33,49]),(79,[48,101]),(158,[64,33,49,117,101])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V47 : Known true K47 := extend_ok (m:=47) V85 low47 (by decide +kernel)
def g55Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xe001ffc07ff01ffe00,0x3fffff80ffd35632000f])),(BitVec.ofNat 152 (word80 [0x48d4128d0522c8549a,0x92522916299346225555]))),((BitVec.ofNat 152 (word80 [0xfffe00007fffffffff,0xc007ffff01a3adc80ff0])),(BitVec.ofNat 152 (word80 [0x80981b160644809813,0x36032244d030cc81111]))),((BitVec.ofNat 152 (word80 [0xffffffff80001fffff,0xfff80000003f407df000])),(BitVec.ofNat 152 (word80 [0x2e05c18178702e01c,0x380bc387033007d3333]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1fffff,0xfffffffffe663f7600ff])),(BitVec.ofNat 152 (word80 [0x130160205808130120,0x2404c00000643114aaaa]))),((BitVec.ofNat 152 (word80 [0xffffffffffffe00000,0x19dd38dff00])),(BitVec.ofNat 152 (word80 [0x1c01800060001c01c0,0x38070040808cd300cccc]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g55C : List ColumnInfo := []
def g55A : List (List Nat) := [[],[32,84]]
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
theorem g55G : graphValid g55 (boundsBefore K47) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low55 : Lower true (varsX 55) (graphGoal 55) 5 := lower_forest (g:=g55) (i:=0) (hints:=1049924) (before_sound K47 V47) g55G g55T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K55 := extendKnown K47 5 [(55,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V55 : Known true K55 := extend_ok (m:=55) V47 low55 (by decide +kernel)
def g59Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xf003ff0ff87ff007ff,0xff87fffcd47c560003ff])),(BitVec.ofNat 152 (word80 [0xa4280a201120a45214,0x81102080501c1694a529]))),((BitVec.ofNat 152 (word80 [0xfffc000ffffffff801,0xfff87fc35353a20ffc00])),(BitVec.ofNat 152 (word80 [0xc0302c40a002c06058,0xa01010a425122318c63]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffff0007ffffffe,0x7ffcafd11df0001f])),(BitVec.ofNat 152 (word80 [0x140b002c20b008060,0x2c220a00a741086318c6]))),((BitVec.ofNat 152 (word80 [0x7fffffff,0xffff80004d2fe8007fe0])),(BitVec.ofNat 152 (word80 [0x982c08b044c090481,0x30004c100d22c94a5294]))),((BitVec.ofNat 152 (word80 [0xffffffffff80000000,0x33aa61bff8000])),(BitVec.ofNat 152 (word80 [0xe03000c00700e0701,0xc044702118a6118c6318]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g59C : List ColumnInfo := [(1,0,58,0,4),(2,0,57,0,4),(8,0,51,0,4),(16,0,43,0,4),(32,0,27,0,4)]
def g59A : List (List Nat) := [[],[81,67],[16,83],[16,48,64,80],[48,84],[48,65,80,16],[64,49],[64,81,48,49],[80,16,49,67],[80,65]]
def g59D4 (j : Nat) := if j=0 then 0x57d4d10 else 0
def g59D5 (j : Nat) := if j=0 then 0xc1a0fd20fd10 else 0
def g59H5 (j : Nat) := if j=0 then 0xb0 else 0
def g59D6 (j : Nat) := if j=0 then 0x23440bf else 0
def g59H6 := limbs80 #[#[0x9200003a00003195,0x0,0x40002e36030000002b,0x2700]]
def g59L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g59D4)
  | 5 => (2,1,3,0,0,4,0,g59D5)
  | 6 => (1,0,3,0,0,0,0,g59D6)
  | _ => emptyPacking
def g59I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 4 0 0 g59H5
  | 6 => lookupWord 2 37 0 8 1 3 g59H6
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
theorem g59P5_0 : block g59 5 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g59B5 : block g59 5 0 2=true := g59P5_0
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
theorem low59 : Lower true (varsX 59) (graphGoal 59) 7 := lower_forest (g:=g59) (i:=0) (hints:=1048643) (before_sound K55 V55) g59G g59T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K59 := extendKnown K55 7 [(59,[]),(107,[100]),(109,[33,100])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V59 : Known true K59 := extend_ok (m:=59) V55 low59 (by decide +kernel)
def g87Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffc00ffc07fe03fff,0xe00ffffe07f469d401c7])),(BitVec.ofNat 152 (word80 [0xa0a86a128d0a458a05,0x46a250a4b29029d49249]))),((BitVec.ofNat 152 (word80 [0xfffff00007fffc07f,0xfff007fff813a68c0e38])),(BitVec.ofNat 152 (word80 [0xc1304c1b160c891309,0x84c360c924d1a28c9249]))),((BitVec.ofNat 152 (word80 [0xfffffffff8000007f,0xfffff800000bc8b47000])),(BitVec.ofNat 152 (word80 [0x5c1705c182f0e1c2e,0x70382f1c70bc8b5b6db]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xf0000000000000007f,0xffffffffffe6fe67803f])),(BitVec.ofNat 152 (word80 [0x60180602030102030,0x8040300000654212492]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffffff80,0x1911bbffc0])),(BitVec.ofNat 152 (word80 [0x80200800040000040,0x10080400000000024924]))),(0x0,0x0),(0x0,0x0)]
def g87C : List ColumnInfo := [(1,0,86,0,5)]
def g87A : List (List Nat) := [[],[16]]
def g87D5 (j : Nat) := if j=0 then 0x3f else 0
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
theorem g87G : graphValid g87 (boundsBefore K59) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low87 : Lower true (varsX 87) (graphGoal 87) 6 := lower_forest (g:=g87) (i:=0) (hints:=1604) (before_sound K59 V59) g87G g87T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K87 := extendKnown K59 6 [(87,[]),(167,[16,32,84,118]),(206,[16,32,48,100,84,117])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V87 : Known true K87 := extend_ok (m:=87) V59 low87 (by decide +kernel)
def g91Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffc03ffff0fffc03f,0xfff0fffff9560600f0ff])),(BitVec.ofNat 152 (word80 [0x202828140220028281,0x40220020980602111111]))),((BitVec.ofNat 152 (word80 [0xffffc01fff0ffffc0,0x1fff0ff01cb5390f0f00])),(BitVec.ofNat 152 (word80 [0x40b0305814020b0305,0x81402042189511333333]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffe0000ffffff,0xe0000fff23b56600000f])),(BitVec.ofNat 152 (word80 [0x8ac141615844ac2426,0x15844a8023b164eeeeee]))),((BitVec.ofNat 152 (word80 [0xf00000000000ffffff,0xfffff000134bf8f00ff0])),(BitVec.ofNat 152 (word80 [0x30181806088300808,0x6000304014868444444]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffff000000,0xcea8c5fff000])),(BitVec.ofNat 152 (word80 [0xc0202018000c03030,0x18088c08462084888888]))),(0x0,0x0),(0x0,0x0)]
def g91C : List ColumnInfo := [(0,8,82,1,5),(2,0,89,0,5),(8,0,83,0,5),(1,8,82,0,4),(16,0,75,0,4),(64,0,27,0,4)]
def g91A : List (List Nat) := [[],[100]]
def g91D4 (j : Nat) := if j=0 then 0x5dd4543 else 0
def g91D5 (j : Nat) := if j=0 then 0x108404fd43 else 0
def g91H5 (j : Nat) := if j=0 then 0xd else 0
def g91D6 (j : Nat) := if j=0 then 0x2c458bf else 0
def g91H6 (j : Nat) := if j=0 then 0x1 else 0
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
def K91 := extendKnown K87 7 [(91,[]),(115,[16,83]),(182,[16,32,67,83,118]),(185,[81,33,67,118]),(186,[16,48,32,66,82,118]),(218,[112,65,32,82]),(241,[112,65,33,83,32,50]),(244,[96,81,32,67,50,115])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V91 : Known true K91 := extend_ok (m:=91) V87 low91 (by decide +kernel)
def g93Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffe007ffffe03fffff,0xffffffffff9aab9d81ff])),(BitVec.ofNat 152 (word80 [0x140500a00408000a0,0x14010000800003899249]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffff800ffffc07ff0,0x1ff80ffc0658e0e8e00])),(BitVec.ofNat 152 (word80 [0x558a62ac2a8a150ac3,0x584a1a290b458e0cb6db]))),((BitVec.ofNat 152 (word80 [0xffffffff0000007fff,0xfe0000ffff9f8a630007])),(BitVec.ofNat 152 (word80 [0x660c8330b31326530a,0x616c2cb2121f88626db6]))),((BitVec.ofNat 152 (word80 [0x7fff,0xffffff000009f56c7038])),(BitVec.ofNat 152 (word80 [0x780f03c03c1c381c03,0x8070303c1c09e4442492]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffff8000,0x6754f2ffc0])),(BitVec.ofNat 152 (word80 [0x80100400c00000600c,0x18040c0202210324924]))),(0x0,0x0),(0x0,0x0)]
def g93C : List ColumnInfo := [(4,0,89,0,5)]
def g93A : List (List Nat) := [[],[96,50]]
def g93D5 (j : Nat) := if j=0 then 0x3f else 0
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
def K93 := extendKnown K91 6 [(93,[]),(157,[67,118]),(220,[96,16,50,66,81,117])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V93 : Known true K93 := extend_ok (m:=93) V91 low93 (by decide +kernel)
def g103Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xe003ff80ffe03ffff0,0x1ff80ffc0009ede81c0])),(BitVec.ofNat 152 (word80 [0x45a8a51a2a458a12a2,0xd4251a148b009e8eb6db]))),((BitVec.ofNat 152 (word80 [0xfffc0000ffffc07fff,0xfe0000fffff8da218e07])),(BitVec.ofNat 152 (word80 [0x8130362c0c891304c0,0x98362c191248d2019249]))),((BitVec.ofNat 152 (word80 [0xffffffff0000007fff,0xffffff00000ff10e7038])),(BitVec.ofNat 152 (word80 [0x1c038300f0e1c0700,0xe038301e1c0ad10a1249]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x7fff,0xffffffffff99af6d003f])),(BitVec.ofNat 152 (word80 [0x1602c040b01020580b,0x14000a000112c646db6]))),((BitVec.ofNat 152 (word80 [0xffffffffffffff8000,0x6754f2ffc0])),(BitVec.ofNat 152 (word80 [0x18030000c00000600c,0x18040c0202500704924]))),(0x0,0x0),(0x0,0x0)]
def g103C : List ColumnInfo := [(2,0,101,0,4)]
def g103A : List (List Nat) := [[],[33]]
def g103D4 (j : Nat) := if j=0 then 0x3f else 0
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
theorem g103G : graphValid g103 (boundsBefore K93) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low103 : Lower true (varsX 103) (graphGoal 103) 5 := lower_forest (g:=g103) (i:=0) (hints:=1049942) (before_sound K93 V93) g103G g103T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K103 := extendKnown K93 5 [(103,[]),(110,[48,101]),(151,[32,16,84,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V103 : Known true K103 := extend_ok (m:=103) V93 low103 (by decide +kernel)
def g117Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xf003ff87fe1fffc01f,0xfff87fffe474a4007c1f])),(BitVec.ofNat 152 (word80 [0xa12845108440228940,0xa01108826014a45294a5]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffc0007ffe1ffffe0,0xfffffc0335be20f83e0])),(BitVec.ofNat 152 (word80 [0xc030162028040b0182,0xc0a00108225922318c63]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffff80001ffffff,0xf0007ffccfd11df0001f])),(BitVec.ofNat 152 (word80 [0x240980130884c0203,0x2c2120087c108a5294a]))),((BitVec.ofNat 152 (word80 [0x1ffffff,0xffff80004d2fe80003e0])),(BitVec.ofNat 152 (word80 [0xb82e045c111702c14,0xb005c104d26c9ce739c]))),((BitVec.ofNat 152 (word80 [0xfffffffffffe000000,0x33aa61bfffc00])),(BitVec.ofNat 152 (word80 [0xc0300060001803018,0xc046021182211084210]))),(0x0,0x0),(0x0,0x0)]
def g117C : List ColumnInfo := [(0,32,81,4,5),(32,0,85,0,5),(1,0,116,0,4),(4,32,81,0,4),(16,0,101,0,4)]
def g117A : List (List Nat) := [[],[64]]
def g117D4 (j : Nat) := if j=0 then 0x5bd4940 else 0
def g117D5 := limbs80 #[#[0x240d140ff40fd40fd20,0x2012]]
def g117H5 (j : Nat) := if j=0 then 0x90 else 0
def g117D6 (j : Nat) := if j=0 then 0x18989f else 0
def g117H6 := limbs80 #[#[0xb403e7400000,0x59d]]
def g117L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g117D4)
  | 5 => (3,1,3,0,0,5,0,g117D5)
  | 6 => (1,0,3,0,0,0,0,g117D6)
  | _ => emptyPacking
def g117I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 4 0 0 g117H5
  | 6 => lookupWord 1 13 0 7 2 1 g117H6
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
theorem g117P5_0 : block g117 5 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g117B5 : block g117 5 0 3=true := g117P5_0
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
theorem g117G : graphValid g117 (boundsBefore K103) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low117 : Lower true (varsX 117) (graphGoal 117) 7 := lower_forest (g:=g117) (i:=0) (hints:=2098436) (before_sound K103 V103) g117G g117T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K117 := extendKnown K103 7 [(117,[]),(121,[64,50,96]),(122,[64,16,82,50,97]),(181,[32,84,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V117 : Known true K117 := extend_ok (m:=117) V103 low117 (by decide +kernel)
def g118Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0xff007fe1ff0fffc03f,0xfff0fffff95e0200f0ff])),(BitVec.ofNat 152 (word80 [0xa0501440220028281,0x40220020980602111111]))),((BitVec.ofNat 152 (word80 [0xffff8001fff0ffffc0,0x1fff0ff01c35b90f0f00])),(BitVec.ofNat 152 (word80 [0x2c06058814020b0305,0x81402042183511333333]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffe0000ffffff,0xe0000fff23b566f0000f])),(BitVec.ofNat 152 (word80 [0xb028160058442c0406,0x5844280213164666666]))),((BitVec.ofNat 152 (word80 [0xffffff,0xfffff000134bf8000ff0])),(BitVec.ofNat 152 (word80 [0xc0b058116088b02828,0x16000b040348e8cccccc]))),((BitVec.ofNat 152 (word80 [0xffffffffffff000000,0xcea8c5fff000])),(BitVec.ofNat 152 (word80 [0xc060018000c03030,0x18088c08468880888888]))),(0x0,0x0),(0x0,0x0)]
def g118C : List ColumnInfo := [(4,0,114,0,5)]
def g118A : List (List Nat) := [[],[97,82]]
def g118D5 (j : Nat) := if j=0 then 0x3f else 0
def g118L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g118D5)
  | _ => emptyPacking
def g118I (_ _ : Nat) : Option (Nat × Nat) := none
def g118 : Forest := ⟨118,5,fun i => g118Y[i]?.getD (0,0),g118C,g118A,g118L,g118I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g118P5_0 : block g118 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g118B5 : block g118 5 0 1=true := g118P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g118T : checkedTables g118 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g118 0 0 0 = true)
  · exact (rfl : block g118 1 0 0 = true)
  · exact (rfl : block g118 2 0 0 = true)
  · exact (rfl : block g118 3 0 0 = true)
  · exact (rfl : block g118 4 0 0 = true)
  · exact g118B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g118G : graphValid g118 (boundsBefore K117) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low118 : Lower true (varsX 118) (graphGoal 118) 6 := lower_forest (g:=g118) (i:=0) (hints:=17892672) (before_sound K117 V117) g118G g118T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K118 := extendKnown K117 6 [(118,[]),(155,[32,16,83,67,118]),(179,[32,84,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V118 : Known true K118 := extend_ok (m:=118) V117 low118 (by decide +kernel)
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
theorem g143G : graphValid g143 (boundsBefore K118) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low143 : Lower true (varsX 143) (graphGoal 143) 6 := lower_forest (g:=g143) (i:=0) (hints:=1907) (before_sound K118 V118) g143G g143T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K143 := extendKnown K118 6 [(143,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V143 : Known true K143 := extend_ok (m:=143) V118 low143 (by decide +kernel)
def g171Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfe1ff00ff87f87ffc0,0x3fc7f1ffd31dc000f00f])),(BitVec.ofNat 152 (word80 [0x1448a4a45121102292,0x82902488430dc5555555]))),((BitVec.ofNat 152 (word80 [0x1ffff0007ff87fff,0xc007fffc23ba600f00f0])),(BitVec.ofNat 152 (word80 [0x5882c0c1620a010b03,0xb214011219a63333333]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1fffffff80007fff,0xfff801ff9c1f30f00f0f])),(BitVec.ofNat 152 (word80 [0x61030101800c220c04,0xc0188201c1222222222]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffe000000000007fff,0xfffffe000be4bf000ff0])),(BitVec.ofNat 152 (word80 [0x800c06060430443018,0x100200c2026494444444]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffff8000,0x6442cffff000])),(BitVec.ofNat 152 (word80 [0x1008080040004020,0x20040100000008888888]))),(0x0,0x0)]
def g171C : List ColumnInfo := [(1,0,170,0,5),(2,0,169,0,5),(8,0,163,0,5),(32,0,139,0,5)]
def g171A : List (List Nat) := [[],[16,83]]
def g171D6 (j : Nat) := if j=0 then 0x2709f else 0
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
theorem g171G : graphValid g171 (boundsBefore K143) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low171 : Lower true (varsX 171) (graphGoal 171) 7 := lower_forest (g:=g171) (i:=0) (hints:=1048659) (before_sound K143 V143) g171G g171T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K171 := extendKnown K143 7 [(171,[]),(173,[33]),(203,[16,48,96,80]),(205,[32,49,16,96,80]),(213,[32,65,16,115,48,80,101]),(214,[32,65,115,49,81,101]),(217,[48,65,33,112,101]),(227,[81,99,67]),(229,[81,33,99,67]),(233,[80,97,33,66]),(234,[48,97,32,82,66,65]),(242,[64,81,32,99,113])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V171 : Known true K171 := extend_ok (m:=171) V143 low171 (by decide +kernel)
def g174Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0xc07fc01ff03fe07fff,0x7fc0ff81fed6800e07])),(BitVec.ofNat 152 (word80 [0x950a8d44a68a4b282a,0x35129a292ca6d6849249]))),((BitVec.ofNat 152 (word80 [0x7fffe0003fff81ff,0xff8000fffe0725a07038])),(BitVec.ofNat 152 (word80 [0x26130986cb0c924c4c,0x261b2c32493725a49249]))),((BitVec.ofNat 152 (word80 [0x7fffffffc00001ff,0xffffff0000074b4381c0])),(BitVec.ofNat 152 (word80 [0x381c0e070c0f1c7070,0x381c303c71c74b449249]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xff80000000000001ff,0xfffffffffffacd3c01ff])),(BitVec.ofNat 152 (word80 [0x2010080010000080,0x40200040000000092492]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffffffffffe00,0x532dffe00])),(BitVec.ofNat 152 (word80 [0x4020100020000100,0x80400080000000124924]))),(0x0,0x0)]
def g174C : List ColumnInfo := [(2,0,172,0,5)]
def g174A : List (List Nat) := [[],[117],[50],[50,117],[33],[33,117],[33,49],[33,49,117],[49,33],[49,33,117],[49],[49,117]]
def g174D5 (j : Nat) := if j=0 then 0x3f else 0
def g174L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g174D5)
  | _ => emptyPacking
def g174I (_ _ : Nat) : Option (Nat × Nat) := none
def g174 : Forest := ⟨174,5,fun i => g174Y[i]?.getD (0,0),g174C,g174A,g174L,g174I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g174P5_0 : block g174 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g174B5 : block g174 5 0 1=true := g174P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g174T : checkedTables g174 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g174 0 0 0 = true)
  · exact (rfl : block g174 1 0 0 = true)
  · exact (rfl : block g174 2 0 0 = true)
  · exact (rfl : block g174 3 0 0 = true)
  · exact (rfl : block g174 4 0 0 = true)
  · exact g174B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g174G : graphValid g174 (boundsBefore K171) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low174 : Lower true (varsX 174) (graphGoal 174) 6 := lower_forest (g:=g174) (i:=0) (hints:=269505872) (before_sound K171 V171) g174G g174T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K174 := extendKnown K171 6 [(174,[]),(199,[48,16,33,101])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V174 : Known true K174 := extend_ok (m:=174) V171 low174 (by decide +kernel)
def g211Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x1fe1fe03fff1ffc03,0xfc3f87ff1dd5460381c7])),(BitVec.ofNat 152 (word80 [0x141441428502402828,0x28811002415106249249]))),((BitVec.ofNat 152 (word80 [0xfe001fffc07fe3fffc,0x3ff87fe358b11c0e38])),(BitVec.ofNat 152 (word80 [0x181881830604083030,0x31020104095811249249]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1fffff8003ffff,0xffc0007ffce6b400703f])),(BitVec.ofNat 152 (word80 [0x212112040848924242,0x4024224800a6a0924924]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffe000000003ffff,0xffffff80003b08e07fc0])),(BitVec.ofNat 152 (word80 [0x404004081010008080,0x80080010000000492492]))),((BitVec.ofNat 152 (word80 [0xfffffffffffffc0000,0x3066bff8000])),(BitVec.ofNat 152 (word80 [0x818018102060030303,0x2304460920668924924]))),(0x0,0x0)]
def g211C : List ColumnInfo := [(1,0,210,0,5)]
def g211A : List (List Nat) := [[],[116],[16],[16,116],[64,113],[64,113,16],[112,65,16],[112,65]]
def g211D5 (j : Nat) := if j=0 then 0x3f else 0
def g211L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g211D5)
  | _ => emptyPacking
def g211I (_ _ : Nat) : Option (Nat × Nat) := none
def g211 : Forest := ⟨211,5,fun i => g211Y[i]?.getD (0,0),g211C,g211A,g211L,g211I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g211P5_0 : block g211 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g211B5 : block g211 5 0 1=true := g211P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g211T : checkedTables g211 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g211 0 0 0 = true)
  · exact (rfl : block g211 1 0 0 = true)
  · exact (rfl : block g211 2 0 0 = true)
  · exact (rfl : block g211 3 0 0 = true)
  · exact (rfl : block g211 4 0 0 = true)
  · exact g211B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g211G : graphValid g211 (boundsBefore K174) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low211 : Lower true (varsX 211) (graphGoal 211) 6 := lower_forest (g:=g211) (i:=0) (hints:=68) (before_sound K174 V174) g211G g211T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K211 := extendKnown K174 6 [(211,[]),(230,[16,32,84,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V211 : Known true K211 := extend_ok (m:=211) V174 low211 (by decide +kernel)
def g63Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffffffffffffffffff,0xd925ba38c873c00003ff])),(BitVec.ofNat 152 (word80 [0x28802a40252014805,0x1925322080239294a529]))),((BitVec.ofNat 152 (word80 [0x1ffff00007fffc00,0x3ed8224bb06c800ffc00])),(BitVec.ofNat 152 (word80 [0x14c014c01b60099019,0xba58224b006086318c63]))),((BitVec.ofNat 152 (word80 [0x1ffffffff8000000,0x73623e14bd881f00000])),(BitVec.ofNat 152 (word80 [0x6702a7015380ade0ae,0x63623614ad88e739ce7]))),((BitVec.ofNat 152 (word80 [0x1fffffffffffffff,0xc858e56c4e4f7e00001f])),(BitVec.ofNat 152 (word80 [0xb80338019c00ce0130,0x58c14c4a4c4c6318c6]))),((BitVec.ofNat 152 (word80 [0xffe000000000000000,0x4579a17773c00007fe0])),(BitVec.ofNat 152 (word80 [0xc013c009e004f001c0,0x4028814771c294a5294]))),(0x33aa5dc49781bfff8000,(BitVec.ofNat 152 (word80 [0x1c000e0007000200,0x1801c809501318c6318]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g63C : List ColumnInfo := [(4,0,59,0,7)]
def g63A : List (List Nat) := [[],[64,49]]
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
theorem g63G : graphValid g63 (boundsBefore K211) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low63 : Lower true (varsX 63) (graphGoal 63) 8 := lower_forest (g:=g63) (i:=0) (hints:=1049923) (before_sound K211 V211) g63G g63T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K63 := extendKnown K211 8 [(63,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V63 : Known true K63 := extend_ok (m:=63) V211 low63 (by decide +kernel)
def g95Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3ffffffffffffffff,0xfe98ba2e079c9000f0ff])),(BitVec.ofNat 152 (word80 [0x5805000a8012801480,0x5290a82c040881111111]))),((BitVec.ofNat 152 (word80 [0xfc003fffc0003fffc0,0x1e50ab87c19600f0f00])),(BitVec.ofNat 152 (word80 [0x9029805300db009901,0x99a50aa8641843333333]))),((BitVec.ofNat 152 (word80 [0x3fffffffc00000,0x738da5275700f00000])),(BitVec.ofNat 152 (word80 [0xe0ce0a9c0a9c0ade0a,0xe0718ca5275707777777]))),((BitVec.ofNat 152 (word80 [0x3fffffffffffff,0xfc85179497b3d000000f])),(BitVec.ofNat 152 (word80 [0x1702ce02ce02ce013,0x5179093b35eeeeeee]))),((BitVec.ofNat 152 (word80 [0xffffc0000000000000,0x45f462f96d0f000ff0])),(BitVec.ofNat 152 (word80 [0x1800f000f000f001c,0x401442994504444444]))),(0x0,0x0),(0x33a4dd980e26ffff000,(BitVec.ofNat 152 (word80 [0x20030003000300020,0xa411000a028888888]))),(0x0,0x0),(0x0,0x0)]
def g95C : List ColumnInfo := [(4,0,91,0,7)]
def g95A : List (List Nat) := [[]]
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
theorem low95 : Lower true (varsX 95) (graphGoal 95) 8 := lower_forest (g:=g95) (i:=0) (hints:=1603) (before_sound K63 V63) g95G g95T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K95 := extendKnown K63 8 [(95,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V95 : Known true K95 := extend_ok (m:=95) V63 low95 (by decide +kernel)
def g111Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfc00ffffffffffffff,0x4c25363f4a4801f0001f])),(BitVec.ofNat 152 (word80 [0x481610542128429029,0x4804363e02414a5294a5]))),((BitVec.ofNat 152 (word80 [0xfffffffe0003fff800,0xf0155d26a8b03e0003e0])),(BitVec.ofNat 152 (word80 [0x90a402980db01320cc,0xf015542288a0c6318c63]))),((BitVec.ofNat 152 (word80 [0xfffffffc000000,0x39c4d2d30f87c0007c00])),(BitVec.ofNat 152 (word80 [0xe13804e009c01bc170,0x388452830f80c6318c63]))),((BitVec.ofNat 152 (word80 [0xfffffffffffffe,0x428bca0bd9e8000f801f])),(BitVec.ofNat 152 (word80 [0x1c047008e011c0180,0x89c801d9aa94a5294a]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffff00000000000000,0x22fa317cb680000fffe0])),(BitVec.ofNat 152 (word80 [0x98013002600200,0x262215c2005294a5294]))),((BitVec.ofNat 152 (word80 [1,0x9d26ecc07137fff00000])),(BitVec.ofNat 152 (word80 [0x200e001c003800400,0x52288407016318c6318]))),(0x0,0x0),(0x0,0x0)]
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
theorem low111 : Lower true (varsX 111) (graphGoal 111) 8 := lower_forest (g:=g111) (i:=0) (hints:=1049939) (before_sound K95 V95) g111G g111T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K111 := extendKnown K95 8 [(111,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V111 : Known true K111 := extend_ok (m:=111) V95 low111 (by decide +kernel)
def g119Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfff0007ffffff00ff5,0xb361d03e280001f0001f])),(BitVec.ofNat 152 (word80 [0x42a135092845216141,0xb261d01428294a5294a5]))),((BitVec.ofNat 152 (word80 [0xffffff8003fffff002,0x16e8554587003e007fe0])),(BitVec.ofNat 152 (word80 [0x4c02601b006424262,0x10605505810842108421]))),((BitVec.ofNat 152 (word80 [0xfffffffffc00000009,0xd8c2c299d107c00f8000])),(BitVec.ofNat 152 (word80 [0x17003801c017838381,0x98c24019d118c6318c63]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffffffffffffa,0x4fe283ab8f8000003ff])),(BitVec.ofNat 152 (word80 [0x980240120098000008,0x48a282a105294a5294a]))),((BitVec.ofNat 152 (word80 [9,0x1711a3877600000ffc00])),(BitVec.ofNat 152 (word80 [0xe00b805c02e0040408,0x711a28226e739ce739c]))),((BitVec.ofNat 152 (word80 [4,0xe9177e4005fffff00000])),(BitVec.ofNat 152 (word80 [0xc00600300080804,0x41140240048421084210]))),(0x0,0x0),(0x0,0x0)]
def g119C : List ColumnInfo := [(2,0,117,0,7),(4,0,115,0,7),(0,32,81,6,6),(1,0,118,0,6),(32,0,87,0,6),(16,0,103,0,5),(33,0,86,0,5),(64,0,55,0,5),(18,0,101,0,4),(65,0,54,0,4)]
def g119A : List (List Nat) := [[]]
def g119D5 := limbs80 #[#[0x31fb2aa8987595354130,0xeb2a7a86613edc1654c,0x4f3cb2ea1985d973d433,0x53d72a9b02a77c5c4605,0xe35cafb299a06ba54d81,0x183b]]
def g119D6 := limbs80 #[#[0xb58853bd58453be58053,0x54130d7d4e53bed8153b,0x5130f794d30f754d30fe,0x330bfd9530bf59530ef5,0x30ef55330f754f30fed4,0xdf54f50df54d50bf597,0xfed8153fe18153bf58f5,0xf95153ef55153bfd8153,0x95253ef55253bf58253e,0x481e0a83000bf59653ef,0x509c4b241147e3c1b0c0,0xf1d4e46c34998c05a2b9,0x39010b80e1c9a350e843,0x608e08a3e01e008f804,0x60860800060800003820,0x38204608f18400608000,0x182382]]
def g119H6 := limbs80 #[#[0x348036283d5d800015c4,0x4f04009]]
def g119D7 := limbs80 #[#[0xd50ff987f4c37ca9bd54,0xa7fe53fea9ff14ffea1f,0xd0bf4d9f0ba3e0f803fe,0x478c0c291228c059d445,0x82453c60628a72c60614,0x828c1239451818e314d1,0x8a3028e410ce58c07194,0xa41460918e41]]
def g119H7 := limbs80 #[#[0xa5db74307641c1000161,0x65792c5006619b721,0x743831fc2a5d64000,0xc3b30028ec8ea830000,0x1b863370000]]
def g119D8 (j : Nat) := if j=0 then 0x3421017f else 0
def g119H8 := limbs80 #[#[0x62009177005800003300,0xd5000000000000d60000,0xd400000000e000,0x190000]]
def g119L : Nat → Packing
  | 5 => (9,3,4,0,0,6,0,g119D5)
  | 6 => (27,2,4,0,0,9,0,g119D6)
  | 7 => (10,1,4,0,0,9,0,g119D7)
  | 8 => (1,0,4,0,0,0,0,g119D8)
  | _ => emptyPacking
def g119I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 2 13 3 8 4 0 g119H6
  | 7 => lookupWord 6 37 5 9 5 0 g119H7
  | 8 => lookupWord 2 37 0 8 4 0 g119H8
  | _ => fun _ => none
def g119 : Forest := ⟨119,8,fun i => g119Y[i]?.getD (0,0),g119C,g119A,g119L,g119I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P5_0 : block g119 5 0 9=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g119B5 : block g119 5 0 9=true := g119P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P6_0 : block g119 6 0 5=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P6_5 : block g119 6 5 22=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g119B6 : block g119 6 0 27=true := (@block_merge g119 6 0 5 22 g119P6_0 g119P6_5)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P7_0 : block g119 7 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P7_2 : block g119 7 2 8=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g119B7 : block g119 7 0 10=true := (@block_merge g119 7 0 2 8 g119P7_0 g119P7_2)
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
def K119 := extendKnown K111 9 [(119,[]),(183,[32,84,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V119 : Known true K119 := extend_ok (m:=119) V111 low119 (by decide +kernel)
def g123Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffffff83fffff628eb,0x10b3680003f800003fff])),(BitVec.ofNat 152 (word80 [0x10a0810801040220a2,0x10816812244891224489]))),((BitVec.ofNat 152 (word80 [0xffffc1ffe02d788,0x15ccc201fc000fffc000])),(BitVec.ofNat 152 (word80 [0x2c00a004008225088,0x150c40060c183060c183]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfff000001ffffbd84c,0x8b211e000007f000007f])),(BitVec.ofNat 152 (word80 [0x83042c10885001d84c,0x920164c993264c99326]))),((BitVec.ofNat 152 (word80 [0xffffffffe0000804f4,0x691ab3fe0000001fff80])),(BitVec.ofNat 152 (word80 [0x240130000260480440,0x2812932850a142850a14]))),((BitVec.ofNat 152 (word80 [0x91713,0xa28774000007ffe00000])),(BitVec.ofNat 152 (word80 [0x3809c0211380880713,0xa28320b162c58b162c58]))),((BitVec.ofNat 152 (word80 [0x4e917,0x7e4005fffff800000000])),(BitVec.ofNat 152 (word80 [0xc00e00421c01048915,0x424004c183060c183060]))),(0x0,0x0),(0x0,0x0)]
def g123C : List ColumnInfo := [(1,0,122,0,7),(2,0,121,0,7),(8,0,115,0,7),(16,0,107,0,7),(32,0,91,0,7),(64,0,59,0,7),(0,8,82,33,6),(0,32,81,10,6),(1,8,82,32,5),(2,32,81,8,5),(8,32,81,2,5),(9,0,114,0,5),(40,0,83,0,5),(17,0,106,0,4),(18,0,105,0,4),(24,0,99,0,4),(33,0,82,0,4),(33,8,82,0,4),(48,0,75,0,4),(65,0,58,0,4),(66,0,57,0,4),(72,0,51,0,4),(80,0,43,0,4),(96,0,27,0,4)]
def g123A : List (List Nat) := [[],[100],[16,83],[16,83,100]]
def g123D5 := limbs80 #[#[0x54d30443d454d514c110,0x44237e0d7654d10e5965,0x54f6154130c5f731d563,0x304085b5460396]]
def g123D6 := limbs80 #[#[0x3aca9aa09847f7558d10,0xfb2a698221fc5453044,0x437cb2a60887db634c11,0x10bf2ea98221bed95304,0x4436eb1aa6885fb754c1,0xd109fceca9a213f5d953,0x3442bfbaac6886df6358,0x8d10cfeeab1a219f1d56,0x504c27ebaec6884ff755,0x58530ebaa6a8a61bed85,0xf614c2bfbaac2985df73,0x5551309faebb0a61b754,0xc7654c27fb8aca9867f6,0x7054d40ddaa7b12813f5,0x5c7654ca7ebaec2995fb,0xb70589539fae3b02a73f,0x168983e1c0c85806005f,0x602c958a64c229087634,0x1e88429f8f674369a8c6,0x3100b458ab956a04ca49,0x68c1030400006605804,0x1a3040050704101,0x1000010d040650400504,0x30826305841001010014,0x30c1000001]]
def g123H6 := limbs80 #[#[0xc0000002400000012c,0x87ca0000052000018400,0x17900208]]
def g123D7 := limbs80 #[#[0xf58d10fe4c110bbd8940,0xd8530fe54130bfd8d10b,0x9530bf59530f754d30bf,0x153bfd9532bfd8532bfd,0x10ff58d10ff54d10bfd8,0xff54d20ff4c520ffd8d,0xff55130ff58530ff5453,0xf54d40ff59530ff59130,0x58953ff58153ff54d42f,0x28898ea15818014800ff,0x50a7f49087cfb1bf2f45,0xb57686c8586af25bcb0d,0x1a0091607be6796ea5c3,0x5286e44e88423823e5c6,0xc12070d0e18223050600,0x6884b0c5801c30405951,0x9460e18284048468e4c,0xe18202030092c353038,0x50e182024b8468e5898d,0xc384022078a14229103c,0x200b081c30403890161,0x1820201186386a546223,0x6a5422141a1231618316,0x8488080e8920c1cb8438,0x3068e10720216263528,0x868110c5898d86805463,0x54786]]
def g123H7 := limbs80 #[#[0xc0240088063000280087,0xa1086648042800000240,0x41c2000206c000c01c3c,0x6831074000c4b82c0020,0x1f719470003c7a519d2,0x2d1504703481230d548,0xc001c0bf174190540000,0x47e20e05800386bc5,0x110d21c001c50,0x141703ac6000100544c0]]
def g123D8 := limbs80 #[#[0xd32fea07f4c3fa41fd10,0x3288cc36007f54ffa85f,0x70658e22242402234f66,0x9228432099638642862c,0x32079428c94451cd025,0x50c996330920594284a9,0x1c65a48a180]]
def g123H8 := limbs80 #[#[0x3d080000108880003,0x6a600,0x2800000000003810000,0x900000000511d08060,0x61c0000000000000,0xe78030015840000,0x485220,0x752f00000000000000,0x946001850990b000,0x38e254003140014b40,0x13980000080ae08,0x25700022e021eb280,0x3f330000006590680000,0x6001318000000016,0x10c225f6400000f1652c,0xe260000000000000068]]
def g123D9 (j : Nat) := if j=0 then 0xa4188201bf else 0
def g123H9 := limbs80 #[#[0x85b364c0004005,0x78800d40000000000,0x4000000035dc0020f540,0xa00035800000032,0x162006080]]
def g123L : Nat → Packing
  | 5 => (5,4,5,0,0,6,0,g123D5)
  | 6 => (33,3,5,0,0,9,0,g123D6)
  | 7 => (26,2,5,0,0,11,0,g123D7)
  | 8 => (7,1,5,0,0,9,0,g123D8)
  | 9 => (1,0,5,0,0,0,0,g123D9)
  | _ => emptyPacking
def g123I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 2 23 0 9 3 2 g123H6
  | 7 => lookupWord 11 61 6 12 6 2 g123H7
  | 8 => lookupWord 11 113 3 11 5 2 g123H8
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
theorem g123G : graphValid g123 (boundsBefore K119) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low123 : Lower true (varsX 123) (graphGoal 123) 10 := lower_forest (g:=g123) (i:=0) (hints:=1048643) (before_sound K119 V119) g123G g123T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K123 := extendKnown K119 10 [(123,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V123 : Known true K123 := extend_ok (m:=123) V119 low123 (by decide +kernel)
def g126Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0x3ffffffffffffffff,0x451d37930c4801f003ff])),(BitVec.ofNat 152 (word80 [0x581400540128029029,0x40141692044042108421]))),((BitVec.ofNat 152 (word80 [0xfc00fffe0003fff800,0xfa255c2e0c903e007c00])),(BitVec.ofNat 152 (word80 [0x90a602980db01320cc,0xea055c220c80c6318c63]))),((BitVec.ofNat 152 (word80 [0xfffffffc000000,0x39c4d2d3ab80000f8000])),(BitVec.ofNat 152 (word80 [0xe13844e089c11bc170,0x3944d293a982d6b5ad6b]))),((BitVec.ofNat 152 (word80 [0xfffffffffffffe,0x428bca0bd9efc000001f])),(BitVec.ofNat 152 (word80 [0x1c017002e005c0180,0x2894809d9898c6318c6]))),((BitVec.ofNat 152 (word80 [0xffff00000000000000,0x22fa317cb680000fffe0])),(BitVec.ofNat 152 (word80 [0x98013002600200,0xaa214c1205294a5294]))),((BitVec.ofNat 152 (word80 [1,0x9d26ecc07137fff00000])),(BitVec.ofNat 152 (word80 [0x200e001c003800400,0x1522a0402036318c6318]))),(0x0,0x0),(0x0,0x0)]
def g126C : List ColumnInfo := [(4,0,122,0,7)]
def g126A : List (List Nat) := [[]]
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
theorem g126G : graphValid g126 (boundsBefore K123) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low126 : Lower true (varsX 126) (graphGoal 126) 8 := lower_forest (g:=g126) (i:=0) (hints:=17913152) (before_sound K123 V123) g126G g126T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K126 := extendKnown K123 8 [(126,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V126 : Known true K126 := extend_ok (m:=126) V123 low126 (by decide +kernel)
def g159Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3ffffffffffffffff,0xfe98baae071c9000f0ff])),(BitVec.ofNat 152 (word80 [0x5805000a8012801480,0x5290a82c040881111111]))),((BitVec.ofNat 152 (word80 [0xfc003fffc0003fffc0,0x1e50b787c19200f0f00])),(BitVec.ofNat 152 (word80 [0x9029805300db009901,0x99a50b38641803333333]))),((BitVec.ofNat 152 (word80 [0x3fffffffc00000,0x73cd25275700f00000])),(BitVec.ofNat 152 (word80 [0xe0ce0a9c0a9c0ade0a,0xe071cd25271707777777]))),((BitVec.ofNat 152 (word80 [0x3fffffffffffff,0xfc85171497b3df00000f])),(BitVec.ofNat 152 (word80 [0x1700ce00ce00ce013,0x51710939316666666]))),((BitVec.ofNat 152 (word80 [0xffffc0000000000000,0x45f4e2f96d00000ff0])),(BitVec.ofNat 152 (word80 [0x1802f002f002f001c,0x4054c299650ccccccc]))),(0x0,0x0),(0x0,0x0),(0x33a4dd980e26ffff000,(BitVec.ofNat 152 (word80 [0x20030003000300020,0xa00c0006068888888]))),(0x0,0x0)]
def g159C : List ColumnInfo := [(2,0,157,0,6),(4,0,155,0,6),(16,0,143,0,6),(6,0,153,0,5),(8,0,151,0,5),(5,0,154,0,4),(9,0,150,0,4),(128,0,27,0,4),(128,4,27,0,4)]
def g159A : List (List Nat) := [[]]
def g159D4 := limbs80 #[#[0x2f0b86a4887315454110,0x99ee6b06a52d1d95444,0x930c]]
def g159D5 := limbs80 #[#[0x958910f9d4910fc54110,0xd8d50edd9110ed55110f,0x8f52bb58352cf55150b7,0x82a4848600edd8554bb5,0x3c820140674884d9,0x2010]]
def g159H5 (j : Nat) := if j=0 then 0x16d00000ac0640000 else 0
def g159D6 := limbs80 #[#[0xd54f7a97b4cbda41f510,0x2a22150d007f54ffaa1b,0xa08308540408c8c241b7,0x28088140628c10240e14]]
def g159H6 := limbs80 #[#[0x120000000000000000,0x0,0x94000001000000000085,0x4900007000760000,0x87a3b800000000000000]]
def g159D7 (j : Nat) := if j=0 then 0x8620117f else 0
def g159H7 := limbs80 #[#[0x10000000540000070,0xf4000020000000000000,0x75b01]]
def g159L : Nat → Packing
  | 4 => (4,3,4,0,0,5,0,g159D4)
  | 5 => (10,2,4,0,0,7,0,g159D5)
  | 6 => (7,1,4,0,0,8,0,g159D6)
  | 7 => (1,0,4,0,0,0,0,g159D7)
  | _ => emptyPacking
def g159I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 11 0 6 2 0 g159H5
  | 6 => lookupWord 2 53 0 8 4 0 g159H6
  | 7 => lookupWord 1 29 0 7 3 0 g159H7
  | _ => fun _ => none
def g159 : Forest := ⟨159,7,fun i => g159Y[i]?.getD (0,0),g159C,g159A,g159L,g159I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g159P4_0 : block g159 4 0 4=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g159B4 : block g159 4 0 4=true := g159P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g159P5_0 : block g159 5 0 10=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g159B5 : block g159 5 0 10=true := g159P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g159P6_0 : block g159 6 0 5=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g159P6_5 : block g159 6 5 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g159B6 : block g159 6 0 7=true := (@block_merge g159 6 0 5 2 g159P6_0 g159P6_5)
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
  · exact g159B4
  · exact g159B5
  · exact g159B6
  · exact g159B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g159G : graphValid g159 (boundsBefore K126) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low159 : Lower true (varsX 159) (graphGoal 159) 8 := lower_forest (g:=g159) (i:=0) (hints:=1859) (before_sound K126 V126) g159G g159T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K159 := extendKnown K126 8 [(159,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V159 : Known true K159 := extend_ok (m:=159) V126 low159 (by decide +kernel)
def g175Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x7ffc01ffffffffff,0xffc035677a50000f000f])),(BitVec.ofNat 152 (word80 [0xd01482c82a4252148,0x29c035454a5555555555]))),((BitVec.ofNat 152 (word80 [0x7ffffffff0007ffc,0xf354385e8000f000f0])),(BitVec.ofNat 152 (word80 [0x5615914814c1b60990,0xccf304385e8333333333]))),((BitVec.ofNat 152 (word80 [0xff800001ffffff8000,0x26278cbf400f000f00])),(BitVec.ofNat 152 (word80 [0x9819e2702701380de1,0x7026078c3f4333333333]))),((BitVec.ofNat 152 (word80 [0x1ffffffffff,0xfe580f6a35b0f000f00f])),(BitVec.ofNat 152 (word80 [0xe01e03803801c00e01,0x80180a2a358222222222]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffe0000000000,0x24f859c3ef0000fff0])),(BitVec.ofNat 152 (word80 [0x200000c006003002,0xf041802444444444]))),(0x0,0x0),(0x19b82850c0fffff0000,(BitVec.ofNat 152 (word80 [0x4000010008004000,0x888888888]))),(0x0,0x0)]
def g175C : List ColumnInfo := [(2,0,173,0,7)]
def g175A : List (List Nat) := [[],[33]]
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
theorem low175 : Lower true (varsX 175) (graphGoal 175) 8 := lower_forest (g:=g175) (i:=0) (hints:=1049939) (before_sound K159 V159) g175G g175T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K175 := extendKnown K159 8 [(175,[]),(207,[48,101])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V175 : Known true K175 := extend_ok (m:=175) V159 low175 (by decide +kernel)
def g187Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3fffffc1fffff620e,0xa0acdb00000fc0000fff])),(BitVec.ofNat 152 (word80 [0x28428408401040220a,0x20a05a09249249249249]))),((BitVec.ofNat 152 (word80 [0xfc003fffe0ffe02962,0xe663308003f000fff000])),(BitVec.ofNat 152 (word80 [0x300b00500200822902,0xa44310030c30c30c30c3]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffc00000ffffbd84,0x915842c0fc003f00003f])),(BitVec.ofNat 152 (word80 [0x400c01608405001984,0x81580086186186186186]))),((BitVec.ofNat 152 (word80 [0xffffffffff0000804d,0x6956a9c000000003ffc0])),(BitVec.ofNat 152 (word80 [0x8290298000a6048045,0x4914a1f4d34d34d34d34]))),((BitVec.ofNat 152 (word80 [0x9171,0x18b1dc3f00003ffc0000])),(BitVec.ofNat 152 (word80 [0xe00e010838088060,0x18a0cc18618618618618]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x4e93,0x4f80057fffffc0000000])),(BitVec.ofNat 152 (word80 [0x300300210c0104411,0x42000160820820820820]))),(0x0,0x0)]
def g187C : List ColumnInfo := [(1,0,186,0,7),(2,0,185,0,7),(16,0,171,0,7),(128,0,59,0,7),(0,16,168,3,6),(8,0,179,0,6),(32,0,155,0,6),(1,16,168,2,5),(2,16,168,1,5),(9,0,178,0,5),(17,0,170,0,5),(24,0,163,0,5),(34,0,153,0,5),(48,0,139,0,5),(3,0,168,0,4),(3,16,168,0,4),(10,0,177,0,4),(19,0,168,0,4),(25,0,162,0,4),(33,0,154,0,4),(50,0,137,0,4),(129,0,58,0,4),(130,0,57,0,4),(136,0,51,0,4),(144,0,43,0,4),(160,0,27,0,4)]
def g187A : List (List Nat) := [[],[16,83]]
def g187D5 := limbs80 #[#[0x485404427c61f41c8110,0x443cc5515150110fa142,0xe157650910e696254950,0x501208bf845d9524421f,0xd697554940483ca55152,0x549504839a5915254120,0x483965915354120d6b74,0xe156454d20e2d6455152,0x547208ef825d95448297,0xe2d6455152c822fe1176,0x5095050297e156454f20,0x503c654d4254140f2952,0x54f4254140dab72d0950,0x48540e5953d8950503c6,0xe2d65549425032bdd362,0x54942d0347dd55350940,0xd0347dd55350b40e2d65,0xdd55358b40e2d5458952,0xd0950c5f7654d4254317,0xd59535c3425433ad8970,0x59153542ab61362d0950,0x50ad66026454d50b4f82,0x5537154942e2d5454b60,0x54a42a5d80d955350b4b,0xa5f855915390b8b59154,0xc27030022fe1171d8152,0xcf06931974ae51259146,0xadd62ab52a7d329346a1,0x76b9dc2db6ab3d92c35e,0x238ec5e230b82bfdf2f3,0x8241078441080604be53,0x6080c100000000001]]
set_option maxRecDepth 16000 in
def g187D6 := limbs80 #[#[0x3b4a92a0904dd75d8d10,0xeb2a6a8281d654d5048,0xa6fbb2a7a04ef725954,0x42cbacaa9885b654d601,0x50b2eb9aca214df7654c,0xa42cbecaa9a85cb55152,0x443f9a0e408878d53d0,0x8110fd2a590221fc5472,0x40442fcbae40885f974c,0x50110fe2a2a0221fc485,0x1404437cb1280887b942,0x550110df2caa0221ee55,0x4950442fdbaa80885f97,0x6454110df2c4a8221de5,0xdc142442fdba2a0886f9,0xd7650910dbec6a12217e,0xedc1524427fbb284884f,0xdf6354910ddac4a92217,0x3fdd1624427ebb2a4886,0x4ff72595109feeab1221,0x1f654d40483f4a928090,0x7ba5450120f72a8a024,0x417e5d5404837cb2a809,0x906f96454120bf6eaa02,0xa417e5c341482fdba2a0,0x49076d54549209faeda0,0xa241b75915348376b22a,0xa8904fd7655120d7ac8a,0x2a241af59254482fcb84,0xac8906fb70591209faed,0x2b2a413fdd5644827fb8,0xb683904ff74595209fee],#[0xeca8e41bd58551c827eb,0xaa2a5906ed52587209fa,0xac8a9e41bb59152c83b6,0xeb2aa9906bd6455320db,0x7ac92a6413f5d954c833,0x7fb8ac9904fd7695320d,0xdf6c2a82813fdd564c82,0x3dca12a0a05fb7154140,0xef2a4a8281eed095050,0x2fdb92a0a06fb625414,0x40ddec490a81eb509215,0x502dfba2a2a073d54545,0x540d7aa9b0a813f5cb61,0x2502fdb8284a04fd75d8,0x940f5aa4a1281eedc14,0x425035eb2a84a079d535,0x50940b7aeaa1281afd95,0x742503cea9e84a05bf75,0x454940b7aeba1281af59,0xc7625033eb2aa4a073d5,0x54d8940dbaa7b12813f5,0xdc9545027ebaec4a06bd,0xf7259540b7ae52a2816f,0xb1c9655027fb8acaa05e,0xff7259540ddee4b2a81b,0x3f5cb655027eb8ecaa04,0x79d5350b40f5aa4a1681,0x16f5d542d035eb2a85a0,0x6ed6254b40b7eeaa168,0x81cf55152d036eb1aa5a,0xa04fd7654b40cfacaa96,0x681af55162d036ea9ac5],#[0x2a84fd72d85509feeab1,0x12a1db549425427eba6c,0x84a84ff7650950ebaa6a,0xa12a1bbd8b42542fcb86,0x2a4a84fd76d0950ebaa7,0x3b12a1d754d625433fb2,0x22a6a84fd74d89509fae,0xe4b22a1d799153543aeb,0xbacc8a85f97099150bde,0xae3b22a13f5da64542be,0x7b92a8994fd72d91509f,0xdee4aa465bd551618caf,0x3eb2aa9196bd6455232b,0x9feeab24653f5d9548cb,0xb76a96c0a14fd71d8142,0x2d7aa9b0285b754f6050,0xa7ebaec0a16be54d814,0x42cfecaa9285cf551525,0x50bb7b2aa4a15ef71549,0xd42cfecaa9a857b5c652,0x550b3fb2acaa175f6554,0x86429fae1b2a853fdc16,0x5290b6ea9ac3216ed525,0x54e42ddac8a9485db551,0x95490b3eb2aa9216dd64,0x1d81529feeab24853f5d,0xd16154a7eba6c0a94fd7,0x70d8552b7ee8b0aa56f1,0x5d36154b3eaa6c2a94fd,0xd7299152bf6e0b1aa53f,0xf5c76454a7eb86c8a95e,0xfd74d89539fee2b24a53],#[0x775d36254eeeba0c4a9c,0x280dc0c009405801c001,0xc2802642281ec1a01641,0x36432831c3002f42d82c,0x9848c4604243f83cc390,0xc55054452850c4e04b44,0x65464860c6005e45b858,0xe86cc6c06b469868c680,0xc76075473872c7107046,0x7f47e87cc7c07a478876,0x5884c84083482881c800,0xc8f08d48c88bc8a08848,0x96495894c94093492890,0xf89ec9d09c49b89ac980,0xcab0a94a78a5ca40a249,0xb34b28b0caf0ae4ad8ab,0xc8bacb90b84b68b5cb50,0xcc60c54c38c1cc00bf4b,0xce4cd8cacca0c84c78c6,0x48d3cd20d14d08cfccf0,0xcdb0da4d98d7cd70d54d,0xe34e28e0ce00de4dd8dc,0x8eccec0e94e68e5ce50,0xcfc0fb4f98f6cf50f44f,0x5503901d000ff4fe8fc,0xc90bd0b10a508907d061,0xd15113512910d1010e50,0x1f51d91cd1b11a519916,0x8927d26125524922d211,0xd2e12d52c92bd2a12952,0x20336933d3313253092f,0xa1e10a87c486c8061218],#[0x31448649814698251822,0x1a624d151894498921c6,0x18804083029186c51912,0x600082007820314644b,0x1612080061e4c1136108,0x841e0c841e120840c84,0x8781841e06100020128,0x8041020181060008202,0xc0804180060e10084,0x820c0800428200008041,0x82060800028200182002,0x4820000a08006081,0x80001820c08781840000,0xe0800000000a08182060,0x88040518200000783041,0x608002000898202090,0x800a0c0020000008,0x201040a089820028200,0xa08000006002c60b1820,0x18200000000008041000,0x2000060800a08000,0x8400112080060802a080,0x6322a92180080410bc4,0x2820c481000200a9211,0x1020808182000040800,0xe0828200000182000020,0x322e10182040800a0802,0x8182060828200182000,0x820000030200000,0x1a0610003082000020]]
def g187H6 := limbs80 #[#[0x9c00183c000433040000,0xe9600000000000003489,0x67900000000020b2be95,0x24c00000070c00000ac,0x784e1c0018a0420,0x800a1a00000000001e48,0x102000000d6981,0x51241c719700004f4600,0x8eca0000004958b0003,0xf3b,0x35300000000,0x0,0x49c040022000086c000,0xc065429df000000005dd,0xd29c0000023,0x1a7e912090000,0xb00000000000000868,0xca0000000000096180,0x400]]
set_option maxRecDepth 16000 in
def g187D7 := limbs80 #[#[0x754d50b758f40b7d8d10,0x58c42be58042bd58632d,0x8110ebd0a429f59442b7,0x910fe54110fe50110fec,0x20fe50120bf59510bf58,0xf754d20fb54920fe541,0xbf58720bf59520bf5912,0xf59320f754f20fb54b20,0xd8540fe54140bf59720b,0x8940efd0940ef50940bf,0x140f794d40f754d40bfd,0x40bf59540ef95140ef55,0xbf58b40ef50b40bfd95,0xbf59740ef55340f754f4,0xfd8950df54950bfd8550,0x59632bf59232bfd9150b,0x8142bf59442f754c42bf,0xd42fb94942fb54942bfd,0x42bf59542f794d42f754,0x2fb54a42bf58642bfd95,0xbf59642bf59242f754e4,0xf55152bfd8552bfd8152,0x59252bf58652bfd9152d,0x8953f718953bfd8953bf,0x520ff54910ff50910f7d,0x20ff54520ffd0520ff50,0xffd0720ff95120ff551,0xff95320ff55320ff5472,0xf54540ff48540ff55130,0x54940ff50940ff58540f,0x9540ff55140ff58940ff,0x950ff58550ff54b40ff5],#[0x50ff58950ffd0950ff50,0x2ff55132ff99150ff591,0xffd8142ff58142ff5523,0xf58d42ff54d42ff54942,0xd9542ff59542ffd8d42f,0x8552ff58152ff55242ff,0x152ff59152ff58d52ff5,0x60ab07b059030000ff99,0x18416213211e1030e80c,0x872652432211ff1e41b4,0xb38b35b3393172ee2c52,0x48e46c44a4284063e43b,0xc95a758556a53a4f54cc,0x86bf69666663d61b5eb5,0x7d07b579377874f7116e,0x128db8c089786082980e,0x8a089df9c49949649349,0xafdae2aceaaca83a61a3,0xacb91b76b5bb47b2cb11,0xec5cc2cc11befbdbbc0b,0xd27d05ce3cbaca6c92c7,0xdddc2daed93d71d56d3b,0x5e6ae56e3be20e05df1d,0xf27f13ef1ecfeb4ea0e8,0x1c01a205938e08499006,0x58c4050e3032b2478927,0xc310185871048c161cd8,0xf1958f0848c16189182,0x3c62a9518f1099184946,0xc54305223c6201819112,0xc488543a312261264832,0x6049091a4a31e217488],#[0x78a5ca86088c10112413,0xe215488e005145860640,0xc02e30303005891a2a31,0x29545849874630608080,0x3109864248422141931e,0x518f100e3244c4183449,0x488602322312464448d1,0x1929310c464c5324f106,0x519318c932a101010b01,0x1a246083448c0c284040,0x3248030c891518798203,0xa1828f2a205080068c32,0x4040449518b95480c48,0xc4050e2850808095143,0x44732490181080e5c51a,0x83082458c2e298450600,0x328c4861431746203024,0xa120d11809060468a8c8,0x8c7325c223040400e8c,0x63048b202860a101010,0xc46088a0a392386125c3,0x80c101125c6062c60910,0x4045c60c100e2405c60,0x80612e285325c30c840,0x1862450c131098640608,0x21874a286101cc081010,0x8e0e10e093080e6044c2,0x125830c844863048508b,0x190850d1890c1991210f,0x105461830a6421e14b06,0x62c4c786860132020a08,0x8305804c426386074484],#[0xc4a3149990898908b930,0x2a887890a0062e2192a4,0x5ca890ca890c1862a116,0x20b083a22a1991254988,0xb86150044c485042990c,0x208684161a2086030c14,0x66420c1518664ba30c22,0x5885cb10422172a2434,0x2e0992e118088]]
def g187H7 := limbs80 #[#[0x604010b1d0000090301,0x12030110020005010017,0x100020200070f000801,0x190f020e4b04264c0031,0x44161f22020125000707,0xa061c04160904702e04,0x15dd70000054ce80923,0xf4660000000000c56000,0xef2f2626000cbde02e12,0x8440ea8d9b06c9a36065,0x360deb81f6a5357c05dc,0x6ca3172900ca08a0002,0xa0e7095e8b4b0492da60,0x8000000e390aef364c3b,0xe84d89f923d0a7c48c20,0x107a0009dabef76dda1,0x5f738e16000000500000,0x68c001761230a2172736,0x63adc4800105486e0006,0x2b800120789db09c471,0x30b7e3a50cc48e565000,0x24c5f533e93e28ba7dc3,0x216063536826e6d26d75,0xb20002547e59d5b52269,0x98d04cb8ad2b16640003,0xc50800000116399269e7,0xcccb478b1e2a82805639,0x82a38bd21da5bf2ea9c,0xe074ed1c84338a1434cc,0x6620889a0f67d88c9d7c,0xa3800180362d710d45b9,0xcaa659800000061f43b1],#[0x220351000089a6003529,0x208bf55c30ac92000000,0xb80016ce158f8c489a6b,0xf739b84a9042cd2241d1,0x3ed26aaae0001b4988f0,0xd6a86b0004ac42fc0007,0x44e88580010838057034,0x800131402afaa04f4c08,0xb40b057adf460b0c7e9,0x2f44e131159810c9e00,0x7fdd7b94e318baeb4b00,0xa326f0050e243a1cb32c,0xe2c000524ac69e9e414f,0x8eac1bc5d0e2d51b,0xd84b32018c109c187123,0x2c957cfa9b060002c5,0x7e000156800143b47700,0x8b52a6cdfa62a4e7929d,0xc458c5b0a5a8ae6f9a45,0x7b478930c8000a00d081,0xcc882c3b1f297260de70,0xf8091c8ecf8621131dcc,0x1006a00000000014bcc3,0xb9d3384a2514a6a9427b,0x2ad211e6]]
def g187D8 := limbs80 #[#[0xf20fe907f443bca7dd53,0x65fd50ffa07f503fa61f,0xbfc85fd42fe217f8cbfa,0x780c001fd53ff297f54,0x300ae24c7e18c5410833,0x419e1cd523438ff3c0d8,0x88461319e304a241a228,0x2420d1c201628d1c2908,0xa3429931c43980106c64,0xa8114248e19011319801,0x9b18a40e39b19058e28c,0x6a242040801926163840,0x308bc21a434661258824,0x1a58419038c34258648a]]
def g187H8 := limbs80 #[#[0x840db000080040005082,0x20b51c45400814d24,0x8370043dc3c30021dd01,0xca3a9400152901897a5,0xec8000d50001380f0d00,0x21a00034b0585c7519f,0xa8968e9391d0dd6b7400,0xb6e8c74d0560002a54b4,0x380038bf8f400208559a,0x5119b8000d4f098d313,0xa2c000cfc78c53b89000,0x500000ef5a935c0b647e,0xce0b37c09d36189165c,0xc24d1ddae71800,0xf0003842414003997610,0x4700000008880004db4,0x554f71575642a45d2c00,0xce2861b40024a4000000,0x346b8ca70a66905b0,0x147d0703000000,0x38003b20000000000000,0x786d0100010c3ac68604,0x199233de7ea7bc6645,0x8ca6ff294e4000,0x37268800013875169400,0xfab80493c0029bc62400,0x368ef1395c0024d516d,0xdc7a49d1480000000000,0x2d1bda64ac00000001,0x15712094236e4c2c,0x6200011b0958002e980,0xf2cc5f9080020fa444ac],#[0x2bc36389750000000000,0xf8aa502e828480026750,0x98c001d23cd,0xd7f44d62bc0c002d24,0x2c3ccb80]]
def g187D9 (j : Nat) := if j=0 then 0x1882013f else 0
def g187H9 := limbs80 #[#[0x229c01801170e600012e,0x246c549724fde00080c,0x45d0866cd72b84004a00,0x7d020040d0680000249e,0x54daf3801e380142a538,0x1b]]
def g187L : Nat → Packing
  | 5 => (41,4,5,0,0,9,0,g187D5)
  | 6 => (199,3,5,0,0,12,0,g187D6)
  | 7 => (112,2,5,0,0,12,0,g187D7)
  | 8 => (17,1,5,0,0,10,0,g187D8)
  | 9 => (1,0,5,0,0,0,0,g187D9)
  | _ => emptyPacking
def g187I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 13 131 3 11 6 1 g187H6
  | 7 => lookupWord 65 307 8 13 8 1 g187H7
  | 8 => lookupWord 39 223 6 12 7 1 g187H8
  | 9 => lookupWord 7 37 5 10 5 1 g187H9
  | _ => fun _ => none
def g187 : Forest := ⟨187,9,fun i => g187Y[i]?.getD (0,0),g187C,g187A,g187L,g187I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P5_0 : block g187 5 0 41=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g187B5 : block g187 5 0 41=true := g187P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P6_0 : block g187 6 0 13=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P6_13 : block g187 6 13 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P6_109 : block g187 6 109 90=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g187B6 : block g187 6 0 199=true := (@block_merge g187 6 0 13 186 g187P6_0 (@block_merge g187 6 13 96 90 g187P6_13 g187P6_109))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P7_0 : block g187 7 0 8=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P7_8 : block g187 7 8 61=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P7_69 : block g187 7 69 43=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g187B7 : block g187 7 0 112=true := (@block_merge g187 7 0 8 104 g187P7_0 (@block_merge g187 7 8 61 43 g187P7_8 g187P7_69))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P8_0 : block g187 8 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P8_2 : block g187 8 2 15=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g187B8 : block g187 8 0 17=true := (@block_merge g187 8 0 2 15 g187P8_0 g187P8_2)
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
theorem g187G : graphValid g187 (boundsBefore K175) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low187 : Lower true (varsX 187) (graphGoal 187) 10 := lower_forest (g:=g187) (i:=0) (hints:=1048643) (before_sound K175 V175) g187G g187T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K187 := extendKnown K175 10 [(187,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V187 : Known true K187 := extend_ok (m:=187) V175 low187 (by decide +kernel)
def g190Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0xf003ffffffffffffff,0xfa60e8c0fd89000f00ff])),(BitVec.ofNat 152 (word80 [0x20581400a804a01481,0x4a40a080cc0911111111]))),((BitVec.ofNat 152 (word80 [0xfffc00fffc000fffc0,0x7910c8d4cb300f00f00])),(BitVec.ofNat 152 (word80 [0x4290a6053036c09906,0x679108894c9133333333]))),((BitVec.ofNat 152 (word80 [0xfffffff00000,0x1cf23909ad10f00f000])),(BitVec.ofNat 152 (word80 [0x84e13809c02700de0b,0x81c322909a9133333333]))),((BitVec.ofNat 152 (word80 [0xffffffffffff,0xf2153f683bb80000000f])),(BitVec.ofNat 152 (word80 [0x701c0ae02b80ae00c,0x151f6833b0eeeeeeee]))),((BitVec.ofNat 152 (word80 [0xffffff000000000000,0x116d0a38776f000fff0])),(BitVec.ofNat 152 (word80 [0x3000c0030010,0x44020016644444444]))),(0x0,0x0),(0xce9177e4005ffff0000,(BitVec.ofNat 152 (word80 [0x80200c003000c0020,0x281546000088888888]))),(0x0,0x0)]
def g190C : List ColumnInfo := [(4,0,186,0,7)]
def g190A : List (List Nat) := [[],[117],[50],[50,117]]
def g190D7 (j : Nat) := if j=0 then 0x7f else 0
def g190L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g190D7)
  | _ => emptyPacking
def g190I (_ _ : Nat) : Option (Nat × Nat) := none
def g190 : Forest := ⟨190,7,fun i => g190Y[i]?.getD (0,0),g190C,g190A,g190L,g190I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g190P7_0 : block g190 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g190B7 : block g190 7 0 1=true := g190P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g190T : checkedTables g190 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g190 0 0 0 = true)
  · exact (rfl : block g190 1 0 0 = true)
  · exact (rfl : block g190 2 0 0 = true)
  · exact (rfl : block g190 3 0 0 = true)
  · exact (rfl : block g190 4 0 0 = true)
  · exact (rfl : block g190 5 0 0 = true)
  · exact (rfl : block g190 6 0 0 = true)
  · exact g190B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g190G : graphValid g190 (boundsBefore K187) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low190 : Lower true (varsX 190) (graphGoal 190) 8 := lower_forest (g:=g190) (i:=0) (hints:=269571392) (before_sound K187 V187) g190G g190T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K190 := extendKnown K187 8 [(190,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V190 : Known true K190 := extend_ok (m:=190) V187 low190 (by decide +kernel)
def g215Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x807ffff800fffffe03,0xfa8b3a513a000f000f0f])),(BitVec.ofNat 152 (word80 [0xb0a01506a0940a458,0xa28b0a50321111111111]))),((BitVec.ofNat 152 (word80 [0xff807fffff001ffffc,0x1db89984500f000f0f0])),(BitVec.ofNat 152 (word80 [0x121302604c0d80c891,0x319b8810451111111111]))),((BitVec.ofNat 152 (word80 [0x7fffffffe00000,0x6b760c4a50f000f0000])),(BitVec.ofNat 152 (word80 [0x1c1c0b80700e02f0e1,0xc6b360c0a53333333333]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x7fffffffffffff,0xf96279a7230000f000ff])),(BitVec.ofNat 152 (word80 [0x20204c048090130000,0x6071a700aaaaaaaaaa]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffff80000000000000,0x98c46290f000ffff00])),(BitVec.ofNat 152 (word80 [0x10010020040000,0x4444444444]))),(0x665163c4cffff000000,(BitVec.ofNat 152 (word80 [0x4040600600c0180102,0x44142c088888888888]))),(0x0,0x0)]
def g215C : List ColumnInfo := [(1,0,214,0,7)]
def g215A : List (List Nat) := [[],[16]]
def g215D7 (j : Nat) := if j=0 then 0x7f else 0
def g215L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g215D7)
  | _ => emptyPacking
def g215I (_ _ : Nat) : Option (Nat × Nat) := none
def g215 : Forest := ⟨215,7,fun i => g215Y[i]?.getD (0,0),g215C,g215A,g215L,g215I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215P7_0 : block g215 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g215B7 : block g215 7 0 1=true := g215P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215T : checkedTables g215 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g215 0 0 0 = true)
  · exact (rfl : block g215 1 0 0 = true)
  · exact (rfl : block g215 2 0 0 = true)
  · exact (rfl : block g215 3 0 0 = true)
  · exact (rfl : block g215 4 0 0 = true)
  · exact (rfl : block g215 5 0 0 = true)
  · exact (rfl : block g215 6 0 0 = true)
  · exact g215B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215G : graphValid g215 (boundsBefore K190) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low215 : Lower true (varsX 215) (graphGoal 215) 8 := lower_forest (g:=g215) (i:=0) (hints:=1604) (before_sound K190 V190) g215G g215T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K215 := extendKnown K190 8 [(215,[]),(231,[16,32,84,118]),(238,[16,32,48,100,84,117])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V215 : Known true K215 := extend_ok (m:=215) V190 low215 (by decide +kernel)
def g219Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xf801fffff83ffffee8,0x4d60a4140007c00f83ff])),(BitVec.ofNat 152 (word80 [0x5014028010800102c0,0x48400014210842108421]))),((BitVec.ofNat 152 (word80 [0xfffe003fffc1ff81d5,0xe341508800f801f07c00])),(BitVec.ofNat 152 (word80 [0x60180b00a0040209d0,0xe14140006318c6318c63]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffc00001fffc97,0x85b447441f000000001f])),(BitVec.ofNat 152 (word80 [0x81204c0ac108540015,0x85344741ce739ce739ce]))),((BitVec.ofNat 152 (word80 [0xfffffffffffe000021,0x2edc7a2000003e007fe0])),(BitVec.ofNat 152 (word80 [0x44110230001181021,0x68c3a0294a5294a5294]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x44,0x903f89b3e0003fff8000])),(BitVec.ofNat 152 (word80 [0x180600c0210602004,0x103081a1084210842108]))),((BitVec.ofNat 152 (word80 [0x33a,0x528a034bffffc0000000])),(BitVec.ofNat 152 (word80 [0x6018030042180402a,0x28a000a108421084210]))),(0x0,0x0)]
def g219C : List ColumnInfo := [(1,0,218,0,7),(2,0,217,0,7),(16,0,203,0,7),(128,0,91,0,7),(0,8,82,129,6),(8,0,211,0,6)]
def g219A : List (List Nat) := [[],[112,65]]
def g219D7 := limbs80 #[#[0x8156a6e05d03dc85ed42,0x4a9b]]
def g219D8 (j : Nat) := if j=0 then 0x2c4581bf else 0
def g219H8 (j : Nat) := if j=0 then 0xaa else 0
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
theorem g219G : graphValid g219 (boundsBefore K215) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low219 : Lower true (varsX 219) (graphGoal 219) 9 := lower_forest (g:=g219) (i:=0) (hints:=67) (before_sound K215 V215) g219G g219T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K219 := extendKnown K215 9 [(219,[]),(243,[16,83]),(246,[16,32,67,83,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V219 : Known true K219 := extend_ok (m:=219) V215 low219 (by decide +kernel)
def g221Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffffffffffffffffff,0xea83289b8ca000f00fff])),(BitVec.ofNat 152 (word80 [0x50028008000080,0x28020090848111111111]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfff8003ffc03ffc0,0x1d093584cf400f00f000])),(BitVec.ofNat 152 (word80 [0x2a05606b0250682905,0x9d012084cf4333333333]))),((BitVec.ofNat 152 (word80 [0xffffffc00003ffff,0xcd31ae4e2190f000000f])),(BitVec.ofNat 152 (word80 [0x4c29814c0b60b0b209,0x511ae4e210666666666]))),((BitVec.ofNat 152 (word80 [0xfffffffffffc0000,0x2535845bb50000f00f0])),(BitVec.ofNat 152 (word80 [0x708e04702380c23c0e,0x20158453b5aaaaaaaaa]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xff0000000000000000,0x45c463c762f000fff00])),(BitVec.ofNat 152 (word80 [0x3001800c0100c010,0x5c0608002444444444]))),(0x33a4d3e0015ffff00000,(BitVec.ofNat 152 (word80 [0x80c006003002030020,0x2a05120001888888888]))),(0x0,0x0)]
def g221C : List ColumnInfo := [(4,0,217,0,7),(8,0,213,0,7),(16,0,205,0,7),(1,0,220,0,6),(64,0,157,0,6),(128,0,93,0,6),(68,0,153,0,5),(5,0,216,0,4)]
def g221A : List (List Nat) := [[],[67,118],[96,50],[96,50,66,112],[112,66,50,96],[112,66]]
def g221D3 (j : Nat) := if j=0 then 0x1d017554d4250110 else 0
def g221D4 := limbs80 #[#[0x50940443e054d4250110,0x443685d54250110f8373,0x5515350110da37550940,0x624c303c4]]
def g221H4 (j : Nat) := if j=0 then 0x10 else 0
def g221D5 := limbs80 #[#[0x3e8a9a80887a14250110,0xf62a8a0221f4dcd4044,0x42f9baa80885f1755011,0x109eeecaa221f154d424,0x5039caa2a0a05d773591,0x6009eee2b2a81375d763,0x819d2213c6cc151e3048,0x40000e]]
def g221H5 := limbs80 #[#[0x58800000008c0000,0x82e80000000,0x7139400d05e0]]
def g221D6 := limbs80 #[#[0x7d8d40f950910fc50110,0x54140fd59110fd55110b,0x9540bf59540f7d8d40fe,0xf7a6f645449391a00bfd,0x34985a4c1931727d3048,0x4088200c40901518238]]
def g221H6 := limbs80 #[#[0x1dc0c93001826613eb20,0xd1e43610cad828005141,0x122607c2e28e91d4b60b,0x6d4892ed8f8000000142,0x1313c3e0]]
def g221D7 := limbs80 #[#[0x7dc3a91e203fa81f510,0x15224e86]]
def g221H7 := limbs80 #[#[0x30300000007,0x84000000ca000b020000,0x1014000,0x0,0xf1280000f8410400000,0x13,0x80000000000000000000,0x1a4641,0x4000000000000008000,0xa8000000000000000008,0x1]]
def g221D8 (j : Nat) := if j=0 then 0x2c6881bf else 0
def g221H8 := limbs80 #[#[0x1400000000000000f300,0x37000000000000000000,0x60a8000000,0x0,0x0,0x8100]]
def g221L : Nat → Packing
  | 3 => (1,5,3,0,0,0,0,g221D3)
  | 4 => (5,4,3,0,0,5,0,g221D4)
  | 5 => (12,3,3,0,0,7,0,g221D5)
  | 6 => (9,2,3,0,0,8,0,g221D6)
  | 7 => (2,1,3,0,0,6,0,g221D7)
  | 8 => (1,0,3,0,0,0,0,g221D8)
  | _ => emptyPacking
def g221I : Nat → Nat → Option (Nat × Nat)
  | 4 => lookupWord 1 2 0 4 0 0 g221H4
  | 5 => lookupWord 2 23 0 9 3 2 g221H5
  | 6 => lookupWord 6 29 5 11 4 3 g221H6
  | 7 => lookupWord 3 79 3 11 4 3 g221H7
  | 8 => lookupWord 1 53 0 8 1 3 g221H8
  | _ => fun _ => none
def g221 : Forest := ⟨221,8,fun i => g221Y[i]?.getD (0,0),g221C,g221A,g221L,g221I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P3_0 : block g221 3 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g221B3 : block g221 3 0 1=true := g221P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P4_0 : block g221 4 0 5=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g221B4 : block g221 4 0 5=true := g221P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P5_0 : block g221 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P5_1 : block g221 5 1 11=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g221B5 : block g221 5 0 12=true := (@block_merge g221 5 0 1 11 g221P5_0 g221P5_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P6_0 : block g221 6 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P6_3 : block g221 6 3 6=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g221B6 : block g221 6 0 9=true := (@block_merge g221 6 0 3 6 g221P6_0 g221P6_3)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P7_0 : block g221 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P7_1 : block g221 7 1 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g221B7 : block g221 7 0 2=true := (@block_merge g221 7 0 1 1 g221P7_0 g221P7_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P8_0 : block g221 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g221B8 : block g221 8 0 1=true := g221P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221T : checkedTables g221 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g221 0 0 0 = true)
  · exact (rfl : block g221 1 0 0 = true)
  · exact (rfl : block g221 2 0 0 = true)
  · exact g221B3
  · exact g221B4
  · exact g221B5
  · exact g221B6
  · exact g221B7
  · exact g221B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221G : graphValid g221 (boundsBefore K219) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low221 : Lower true (varsX 221) (graphGoal 221) 9 := lower_forest (g:=g221) (i:=0) (hints:=1539) (before_sound K219 V219) g221G g221T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K221 := extendKnown K219 9 [(221,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V221 : Known true K221 := extend_ok (m:=221) V219 low221 (by decide +kernel)
def g222Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0xf003ffffffffffffff,0xfa62e8c07cc9000f00ff])),(BitVec.ofNat 152 (word80 [0x20581400a804a01481,0x4a42a0804c0911111111]))),((BitVec.ofNat 152 (word80 [0xfffc00fffc000fffc0,0x7810c8dccb300f00f00])),(BitVec.ofNat 152 (word80 [0x4290a6053036c09906,0x66810889ccb133333333]))),((BitVec.ofNat 152 (word80 [0xfffffff00000,0x1cf23b09ad10f000000])),(BitVec.ofNat 152 (word80 [0x84e13829c0a702de0b,0x81c722b09ad177777777]))),((BitVec.ofNat 152 (word80 [0xffffffffffff,0xf2153f483bb80000f00f])),(BitVec.ofNat 152 (word80 [0x701c08e023808e00c,0x11f4833b0aaaaaaaa]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffff000000000000,0x116d0a38776f000fff0])),(BitVec.ofNat 152 (word80 [0x3000c0030010,0x1144020004644444444]))),(0xce9177e4005ffff0000,(BitVec.ofNat 152 (word80 [0x80200c003000c0020,0x281546000088888888]))),(0x0,0x0)]
def g222C : List ColumnInfo := [(4,0,218,0,7),(8,0,214,0,7),(0,8,86,128,6),(2,0,220,0,6),(16,0,206,0,6),(4,8,82,128,5),(10,0,212,0,5),(12,0,210,0,5),(18,0,204,0,5),(24,0,198,0,5),(64,0,158,0,5),(128,0,86,0,5),(128,8,86,0,5),(6,0,216,0,4),(68,0,154,0,4),(72,0,150,0,4),(132,0,82,0,4)]
def g222A : List (List Nat) := [[]]
def g222D4 := limbs80 #[#[0xd4940442e86135250110,0x442e8e1162501109e187,0x5d55350110f115454d40,0x541109d08754d4044354,0x9e3845c35244354dd153,0x54d5050239e1974d4910,0x5023361f63d4940a5886,0xe0576d4b408e7815db52,0x593528e7815db43d4a39,0xb19801915454e3960371,0x90c0c02c56046455153,0x666c16aa4e9109e364e6,0x9011202000001cb]]
def g222D5 := limbs80 #[#[0xaf0b86a4887515354110,0xfc284a022139dc564d4,0x43f0b1280887e3525011,0x10fa2a6a0221f85c9404,0x443d8aa280887d373501,0x110be2eaa0221ec95140,0x443b8aa2a0885f37550,0x4910bceeca12217cdd15,0x62442f2bb6a4885e574d,0x54d10bcee8b1221b9991,0x954443aaaa2a6887d370,0x359110be2e12a2213ddd,0x4d50502f8b84c8885d77,0x6350940e72a8a8281d65,0xd8f52502f4b86a4a06cf,0xd76d4940b5ae9a9281b3,0x75515350367b1ac4a04e,0xdc7654d40cbacaa9a81c,0xb35cb635026f3b2a6a04,0x4f771595409baebb1a81,0x16b5d352d026fb9acaa0,0x71d5454f409daeda968,0xa13ddc565d032eb2aa7a,0xa965f6454d50eb6e0a9a,0x6a53b5db43d4a77ba2c1,0x6a1ee771593529dee0b2,0x2a873edc16550f2fb2aa,0xa7a1d9f7454f439eee2b,0xaa2a73ddc565d0f2eb2a,0x2a8a9f577155153abee0,0x322a7c7d915454f8e32,0x82c8a9dd57119153bb2e],#[0xc9322a775dc56454eedb,0xb9ac12a4f570d8554d3e,0x1d0561203a0b01e0026f,0x390d6320b22b09e2408a,0x511364a11a430fe3e0ea,0x6518e6217a5b15e5614a,0x791de741c26d1a66819a,0x87216822027f1f67c1ea,0x9524e922428f2368c222,0xa52869e2729b2669825a,0x10ec6b02baad2aeaa2a2,0x3a4069018b04ac1242ce,0x3412404088060836901c,0x14100b0124049000200,0xb0124041c121041410,0x3081c20490100901,0x404101c204241000,0x1881000c2040000000,0x18c04000000000000000,0x620588]]
def g222H5 := limbs80 #[#[0x39c00000015400,0x0,0x29800000000064d0ebc,0x0,0x60ec00000003d0000,0xb2800000,0x4240,0x80000000000000000000,0x569c0000023,0x708000093000008b]]
def g222D6 := limbs80 #[#[0x950910fc54110fc50110,0x54d10f958910f9d4910f,0x8142d754d50b7d8d40f5,0x153bb59352bb58352bbd,0x10fd55110bdd8554d755,0xfd99110fd59110fd951,0xfb50940fe54140fd5951,0x754d40fb58940fbd4940,0x95140ef55140f7d8d40f,0x4b40bfd9540bf59540ef,0x740ef55340f754f40fbd,0x42bfd9150df55150bf59,0x3fbd0f52fb50f52fb50d,0xbfd9543bf59543f754d4,0xf55153bf59743f754f43,0xd8153f758153bfd9153d,0x9153f759153f719153f7,0x554bfd8154f7d9153f79,0x54bf58254bfd8d54fdd8,0xe07a0be0f40d800bf58e,0x7c2b4518959091c03144,0x464879019ef38c6acc81,0xcb315faab52e9f130a4d,0x5b6b5967ccc58b3095d,0x33eb7a0eb9d0b8d70ee,0x4e6989252394578790a2,0x44075ceac552a6f4727d,0x430242c106e110b041b8,0xd60a1e40d5824090ac3,0xc23218b821e10d240c3,0x616016a03478078c1026,0x560786604130e0182601],#[0x1c352224228342b03423,0x4218a8411042b0344842,0xa0863e4060e202087c4,0x4009081070820984217,0x5c282182042020218404,0x1010818c08101001c204,0xc1010020b0520208000,0x10100242822c30808086,0x24220316080863020410,0xc223448500c111a24222,0x22422224212344850082,0x860610130304040062c2,0x8080]]
def g222H6 := limbs80 #[#[0x4424510d11212e231040,0x1659e87c4000b1200000,0x3667c0000000164ae008,0x29880000000000000f,0xc0013500000000000528,0x12b,0x87000000000000000000,0x450a34006bf000000000,0x53400000490,0x216d03f76000000b000,0x5e000b5c003858000000,0x80000088a907320002e9,0xed5603183000087ed0c8,0x112000001e940059,0x80800000000000001bd0,0x28ab29001,0x8880000048042600,0xd2c0000048f0000000,0x4540030efb374c000000,0xc00000000000a28003a3,0xb6e7,0x0,0xfb7a83ee000000000000,0x38c904000001dc,0x2e11400000b4ec17cc00,0x4700038e4]]
def g222D7 := limbs80 #[#[0xd53f7a97b50bda41f510,0x87fd50ffa07f503bca7d,0x3fca9fd54fea9ffd0ffa,0x451d4c0511f8cc421200,0xdb21205ea6ab0d5c9c,0xb0c12a880c146808304,0x686030810486380c1688,0x2c282120a1822ca82120,0x62ca8602052a1808305,0xc18a86030814b0a084a2,0x40e180a3062840e180]]
def g222H7 := limbs80 #[#[0xc20500a1003240002040,0xc00312af4c28c08c0025,0x3070005b17400c858ea4,0x800f5000000a80028932,0x4000014f9d92900000f4,0x4850285153400e55c6d6,0x650ab350000076b26cb,0xc00090ec5d2b2c6000f7,0x2b3c42c2f80000016e22,0xc710019f006a20580000,0x3ac03c780049]]
def g222D8 (j : Nat) := if j=0 then 0x6200113f else 0
def g222H8 := limbs80 #[#[0x28000000000003600004,0x6d80000000001300000,0x36803b80000042000,0x6c800039d1000000000,0x2000001d3440800]]
def g222L : Nat → Packing
  | 4 => (17,4,5,0,0,7,0,g222D4)
  | 5 => (70,3,5,0,0,10,0,g222D5)
  | 6 => (55,2,5,0,0,11,0,g222D6)
  | 7 => (14,1,5,0,0,9,0,g222D7)
  | 8 => (1,0,5,0,0,0,0,g222D8)
  | _ => emptyPacking
def g222I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 4 89 0 9 5 0 g222H5
  | 6 => lookupWord 17 179 4 11 7 0 g222H6
  | 7 => lookupWord 13 79 6 10 6 0 g222H7
  | 8 => lookupWord 3 53 1 8 4 0 g222H8
  | _ => fun _ => none
def g222 : Forest := ⟨222,8,fun i => g222Y[i]?.getD (0,0),g222C,g222A,g222L,g222I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g222P4_0 : block g222 4 0 17=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g222B4 : block g222 4 0 17=true := g222P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g222P5_0 : block g222 5 0 3=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g222P5_3 : block g222 5 3 67=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g222B5 : block g222 5 0 70=true := (@block_merge g222 5 0 3 67 g222P5_0 g222P5_3)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g222P6_0 : block g222 6 0 13=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g222P6_13 : block g222 6 13 42=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g222B6 : block g222 6 0 55=true := (@block_merge g222 6 0 13 42 g222P6_0 g222P6_13)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g222P7_0 : block g222 7 0 6=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g222P7_6 : block g222 7 6 8=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g222B7 : block g222 7 0 14=true := (@block_merge g222 7 0 6 8 g222P7_0 g222P7_6)
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
  · exact g222B4
  · exact g222B5
  · exact g222B6
  · exact g222B7
  · exact g222B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g222G : graphValid g222 (boundsBefore K221) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low222 : Lower true (varsX 222) (graphGoal 222) 9 := lower_forest (g:=g222) (i:=0) (hints:=285308480) (before_sound K221 V221) g222G g222T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K222 := extendKnown K221 9 [(222,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V222 : Known true K222 := extend_ok (m:=222) V221 low222 (by decide +kernel)
def g235Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xe003ff87fe1fff9ac2,0x103df000000fc0fc003f])),(BitVec.ofNat 152 (word80 [0x412805100441101ac2,0x1f145145145145145]))),((BitVec.ofNat 152 (word80 [0xfffc0007fffff8390f,0xb482500003f03f000fc0])),(BitVec.ofNat 152 (word80 [0x80301620280021380f,0x940040c30c30c30c30c3]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffff8001fffd03d,0x79312000fc000003f03f])),(BitVec.ofNat 152 (word80 [0x4409801308440001d,0x7930028a28a28a28a28a]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffe000462a,0x8b87903f00000003ffc0])),(BitVec.ofNat 152 (word80 [0x98120024009824620,0x2879514514514514514]))),((BitVec.ofNat 152 (word80 [0x4984,0x67ec8fc000003ffc0000])),(BitVec.ofNat 152 (word80 [0xe01c043810e044100,0x63ec0618618618618618]))),((BitVec.ofNat 152 (word80 [0x2651,0x42404fffffffc0000000])),(BitVec.ofNat 152 (word80 [0x100200040010000000,0x820820820820820]))),(0x0,0x0)]
def g235C : List ColumnInfo := [(1,0,234,0,7),(2,0,233,0,7),(8,0,227,0,7),(32,0,203,0,7),(64,0,171,0,7),(128,0,107,0,7),(3,0,232,0,5),(9,0,226,0,5),(10,0,225,0,5),(33,0,202,0,5),(34,0,201,0,5),(40,0,195,0,5),(65,0,170,0,5),(66,0,169,0,5),(72,0,163,0,5),(96,0,139,0,5),(41,0,194,0,4),(42,0,193,0,4),(67,0,168,0,4),(73,0,162,0,4),(98,0,137,0,4),(129,0,106,0,4),(130,0,105,0,4),(136,0,99,0,4),(160,0,75,0,4),(192,0,43,0,4)]
def g235A : List (List Nat) := [[],[81,99],[16,83],[16,48,96,80],[48,101],[48,97,80,16],[80,16,49,99],[80,97],[96,49],[96,81,48,49]]
def g235D4 := limbs80 #[#[0x10c8ae1192d915254110,0x4110c8ae1192d5162541,0xc60c68613915c8725]]
set_option maxRecDepth 16000 in
def g235D5 := limbs80 #[#[0x90221c69765495048110,0x71543204421bf26c3aca,0x90aa284a8e4088758549,0x221ba38450951c8110f,0x454720443a62e8aa2a39,0x1c3b02a96408866ce117,0x2215e39760552c8110cf,0x553204425d325c32a990,0xca26490a608843e65f86,0x21ec1654c9214c110be0,0x8530443d86ca99242982,0xaa6490a60887705d5324,0x1f8143509214c110be0c,0x530443e82a6a92429822,0xaa710a60887585d55248,0x1f3985d6214c110da8c2,0x30443c62caaa28298221,0xeb20a60886d461553905,0x5153589514c110ad9ca2,0x443ca2a7b12a298221e,0x6a8a60886d454f825453,0x19220d514c110ba8caca,0x442f232841aa2982217c,0xa8a608874c5d15454530,0x84dd1514c110ba8c9ea8,0x438d2eab12a4982219b3,0x2a60886a621383595304,0x7e09518c110c5c43f08b,0x32e70ea9aa3182211f19,0xc608871a5d56254a3044,0x54d51cc1108f8cbf02a9,0x17b2fc22cb98221d1574],#[0x80885cc6535354540442,0x4d5190110f19c8acaaa2,0x62ebc22a320221d51735,0x884ece5181d4a404433,0x165901109d9ca303a9c8,0xf0bb92c4a82218bb87e1,0x8879858952545504430d,0x5154110db1c12a4a8aa0,0xe8aa2a2a8221e3164551,0x866ce137454550443a66,0x154110f30b12a528aa08,0x4a90e2a8221b618254a5,0x57824973dc5504436c30,0x54110d34c32a4992a088,0xa9464a8221b615260632,0x8ad9152509504434d30c,0x4110d1cc32a8a12a0887,0x9484a8221b6152606425,0xadcd62549504434d30ca,0x110b35c9ac4a92a08871,0x2a4a8221729949895254,0x64c7254950442ec32239,0x10b94ca0e4a92a0885d2,0xa4a822166992d8d52541,0x136454950442cd325b22,0xb35c92c7a92a08868ee,0x4a8221a3984593525411,0xb5458950442d5328392c,0xd1dc26a8b12a08859a64,0xa8221639942156254110,0x721c950442bc722b90e4,0x59b2702a1aa08866a611],#[0x8221669922156354110d,0x1dcd50442bc32540ee6a,0xdb2305aa2a08855c6568,0x2214eb92595700c910d1,0x5c0324429b726b2ae019,0xcc2caba0648852ee5165,0x2186d75e09650c91085f,0x943244307aebc22ca192,0xa30eb28648842f65f845,0x143f94619750c91085fc,0x1324420ff2ac3ac89922,0x30eb2a648852ee4174d9,0xbf9461d658c91085fca,0x4244296f28b2ae321221,0xe2382a4884ab64b84596,0xb1845c47054910ce8c1a,0x24423e730b88e0a92219,0xc382a4886365d9831c15,0xf9461b735491087dcc2e,0x44315ee8c16c8a92210b,0xb22a48852d64774d9152,0x84e01765491086fc9b0f,0x430f70bc02eca92218b8,0xb2a48861de17815d9524,0x4e0d7654910c4fc2106b,0x29d724b1ae1a922189f8,0xea488539e49635c75244,0xe0963d4910c66b9f04b1,0x17f28c3ac7a922126d95,0xc48842fe518759352442,0x11659891083fcc2ea3aa,0x7709c02ecaa2210bd97e],#[0xa8872cdd371dc1654431,0x17259510877cc2e4392c,0xee841ae4b2a218b874e0,0x886271d3835c96544313,0x7259510c4fba706b92ca,0x26c16e8b2a210be981d1,0x852d64482dd1654421bf,0x459510c56c1105ba2ca8,0x6c16e8b2a2149c9360b7,0x6a6e11635c55084293f2,0x54210b65c92e6b1aa108,0xaa2c6a842165b9560563,0x956595354531843c3308,0xc610b2bcb2a6a8a63085,0x6e4a8c214db905d5634,0x56158158d518431b2c6c,0x610a67c930eb1aa30869,0x6e6a8c2149f9461d6354,0x58d80dc55284217f28c3,0x10a6cc86e8b1aa708636,0xa8b1c212d990e0d5458e,0x4587591530825af22c3a,0x87bc8b09bb2a61052de,0x9a98414db905d163d4c2,0x7805d35308297720ba2c,0xd34c32a518aa09061e59,0xa8241a698654a5154120,0x725c55048365708a92e2,0xa5b9aa6a92a09056a650,0x8a4166991d8d5254120e,0x6dcd5148217f28c3acb1,0xbcc2e238aca9042fe518],#[0xc418f371602715952087,0xd4d6188217f28c36e6a8,0xc8b07bb2a91042fe5187,0xa10bf9461f629455087b,0x486154316f0fc22c230a,0xa306312c2a855a641725,0x189f74a0c6258550c4fb,0xd6154217f31ba0c4b0aa,0x704b1ac2a862bdd08258,0xbd98dd26358550c57ba,0x615432d30ac02e530aa1,0xcb94c2a8533e4d865ca,0xd99320172d8550a57ca3,0x25423b726c0ee0a92a14,0x2382a4a84da649811c15,0xb936077054950db0c930,0x54255f28c0ec5292a135,0xba2c3a862b5d38158862,0x20380300300086fc9b05,0xc01682a04e0680b81402,0x430830ce1682904f08e0,0x8aa14e2904e09912c238,0x71883045f0bb1702c056,0xb83646b0d31a0334650c,0x3d8798f01d0394710df1,0x48d11221441c7f8fc1f2,0xe13926c4b89592824047,0x5129c52ca41452844fc9,0x2cc58cb015d2b455caa1,0xc5ecbc1752e45bcb6169,0x4cc818d31461cc21812f,0xd41a534467cce19932c6],#[0x1c737e6dcda1b135c6ac,0x43c2778ed9d83aa748e5,0xf27d8f99f03da7a8f39e,0x83905a0840a808ff9fc3,0x911a2043a8690ba14422,0xda3846a8c917a2c45289,0x5049a92923a444828f91,0x4ca9892fa5c4b295929a,0xa9e93ba744e29b935a68,0x4947a8c512a1941a804f,0x53aa4542a794da9852aa,0xabc572ad959ab055aaa9,0x1000b3965ac858ab095f,0x2b0202000000400,0x20101c40608710412004,0x98204881906144120020,0x104100010410881008,0x10410000,0x9041000000000000,0x81810141000504000,0x141000a001,0x0,0x0,0x40904000000000000000,0x710100090]]
def g235H5 (j : Nat) := if j=0 then 0x19598 else 0
set_option maxRecDepth 16000 in
def g235D6 := limbs80 #[#[0x48420443705cd2108110,0x443785d52108110d6175,0x5d15108110dd17354420,0x8110d7175544204436c,0xd71815d4204427ce1d51,0x54530443f04c9214c110,0x4427ce1d518c110f5153,0x5955450110f315454540,0x54110bb384546404438e,0xe6962549504422fe1176,0xd51504438e5915454110,0x4432ed937050910e3b64,0xe1176d49108df835d952,0xd5110cbb645c3544422f,0xe3965551408428f61764,0x549508439a5895254210,0x8439658f5254210e5963,0xd516354210e595458d50,0xd4610e39645515084396,0xcd9635c3528433658d70,0xd51638433658d70d4e10,0x833358f7254c20ad980,0x5977254c20cad64dc953,0x54120e6952d85504831b,0xd6b73549504839ad8d52,0x1c950482da6165254120,0x882da60b5454120ba984,0xe117654620e396455150,0x549508f787584615422f,0xb59831c152542dc60470,0x58862542ce6107054950,0x5423be1d6218950cad74],#[0x5d551081108bf845c762,0x48110df1815d4204437c,0xcf97654120443da54950,0x595204433d5d95148110,0x442afe116548110aef82,0xe0175481108fd8759520,0x481109f7815d5204427e,0xdf171543204423fe1576,0x54320442fce0550c8110,0x4435e5d550c8110f6952,0x54b50c8110bf181d4320,0xc8110be982d4320443da,0x9f587547204435e5d750,0x5c7204427de1d51c8110,0x4433d59571c8110de552,0xe1165c8110aef8259720,0xc81108ff8759720442af,0xfb15450720443f854941,0x507204437c5d541c8110,0x443f850951c8110bf185,0x55151c8110fe15254720,0xc8110f735454720443dc,0xbf384547204437c5d151,0x50b204437c5d551c8110,0x4437a5d542c8110fa954,0x60552c8110be98550b20,0xc8110de97454b20443f8,0xdeb8754b20442fae1152,0x553204436e5d154c8110,0x4427e61d54c8110afb86,0x60b54c8110bf181d5320,0xc81109f987d5320442fa],#[0xbbb8459720442fae0965,0x997204427ee1d65c8110,0x4427e61e65c8110be982,0xe1175c8110df1815d720,0x4c110bf381541304427e,0xbf181d4130442be61950,0x59530443d554d514c110,0x442afe11654c110adf83,0x549214c110fe14248530,0x4c110df17448530443f8,0xef36548530443bc59521,0x885304437c5d5214c110,0x443bc596214c110fd153,0x616214c110df17588530,0x4c110fd13250530442fc,0xfb15450530443f454d41,0x50530443bc595414c110,0x4437cdd5414c110df175,0x54e414c110bf18550530,0x4c110ef16590530443f4,0xdf375905304437c5d641,0x54530442fc616414c110,0x442f6e0d514c110f5953,0xd89514c110ef16254530,0x4c110bf38254530443bc,0xfd25354530443f454d51,0x54530443dcd4d514c110,0x443f4e0d514c110fd083,0xd51514c110f715454530,0x4c110df17454530443dc,0xbf384545304437cdd151,0x545304437c5d5514c110],#[0x4437c5d6514c110df375,0x616514c110df37594530,0x4c110bd983d4530442fc,0xee962509304427e61f51,0x54930443ba589524c110,0x442be619524c110d7975,0x607524c1109fb8754930,0x4c110bd983d4930442fc,0xaf986d49304435e5d752,0x589304427e61f524c110,0x443b6e0d624c110bdb83,0xe15624c110cf97558930,0x4c110cf975d8930442be,0xbdb8359530442be61762,0x59530442eee11654c110,0x442bee05654c110ef381,0x20d654c110afb8259530,0x4c110edb8359530443b6,0xebb8459530443ae21165,0x995304433e21d654c110,0x442be60b654c110bd983,0xe09518c110ef16254630,0x8c110f715354630442fc,0xdf17554630443dcd4d51,0x54a30443ba589528c110,0x442be619528c110d7975,0x607528c1109fb8754a30,0x8c110d7975d4a30442fc,0x9f987d4a30442be61b52,0x58a304433e5d5628c110,0x442fce05538c110afb85,0x607538c110d797554e30],#[0x8c110d7975d4e30442fc,0xafb8259630442be61b53,0x59630443aee11658c110,0x4437c605758c110cfb87,0x5d150cc110df17154330,0xcc110d7975543304436e,0xdb57454730443d554d51,0x547304435d5d551cc110,0x4427de1d51cc1109f587,0x59571cc110dd5535c730,0xcc110d9d7454f304433d,0xadf83597304432f59574,0x59730442afe1165cc110,0x4423fe1d65cc110c7d75,0xe095150110fb14254540,0x50110f715354540442fc,0xfb15454540443dcd4d51,0x509404437c5d55150110,0x4436e5d54250110eb965,0x60752501109fb8754940,0x50110bb984d4940442fc,0x9f987d4940442be61b52,0xd4d40442fce055350110,0x442ee6135350110bf181,0x61f5350110af986d4d40,0x50110fb181551404427e,0xeb96555140442eee0954,0x59540443bce056550110,0x4437ce057550110ebb84,0xe1175501109fb835d540,0x90110bf382546404436e,0xf735354640443dc54d51],#[0x546404437c5cd5190110,0x4437c5d55190110fb384,0xe1d5290110d797554a40,0x90110bf181d4a404427e,0xaf986d4a404435e5d752,0x54e404427e61f5290110,0x443765cd5390110bf381,0x60753901109f98754e40,0x90110af986d4e40442fc,0xcf9655ce404427e61f53,0x59640443aee116590110,0x4427ee0d7590110cfb87,0x58952541109f582dc550,0x54110cef72589504439b,0xa7f8558d504429fe1562,0x5d950442afe116554110,0x4432fe1176541108ff82,0x5895154110f715254550,0x54110ef36254550443bc,0xf715454550442fce0951,0x54550443bc5915154110,0x4437cdd15154110ef364,0x58a5154110f715294550,0x54110bf18294550443bc,0xdf37394550443bc58e51,0x1c550443dc5487154110,0x442eee117154110bf182,0x9cb7154110f7152dc550,0x54110bf182dc5504437c,0xf7154dc5504437c5cf71,0xdc5504437c5d37154110,0x442fc6043254110bf184],#[0x6143254110bb9840c950,0x54110af9860c950442de,0x9fa870c9504427e61c32,0x4c950443da5493254110,0x442fc6063254110af986,0x6163254110f69528c950,0x54110af9868c950442de,0x9f987cc950442be61b32,0x509504427ea1f3254110,0x443ce5514254110f6952,0x6154254110ebb6450950,0x54110af98650950442de,0xf695290950442fc60642,0x90950442de6164254110,0x443ba5895254110af986,0xa055254110f718154950,0x54110f696254950443dc,0xe7b6254950443da98952,0x54950443da1c95254110,0x4439e58d5254110f6b72,0xdcd5254110e7b6354950,0x54110e7964549504435e,0xb7b84549504439ed9152,0x94950442fc6065254110,0x442de6165254110ee962,0x58b5254110af98694950,0x54110e7b62d49504439e,0xe7b63d49504439e58f52,0xd49504435edcf5254110,0x4439ed935254110e7964,0xe156254110b7984d4950,0x54110ee87258950442de],#[0xcfb7358950443badc962,0x58950442bee0d6254110,0x4439ed516254110e7954,0x2156254110afb8458950,0x54110e7b85589504439e,0xb798598950442ee61262,0xd89504433edcf6254110,0x442fc6047254110af983,0x60c7254110de9721c950,0x54110bda831c950442f6,0xbf3815c950442ee61072,0x50d50442fc6067254110,0x443aed914354110bf381,0xa1d4354110dbb7450d50,0x54110af98690d504427e,0x9fa8790d504427e61e43,0x54d50442fce055354110,0x44376dce5354110ddb73,0xe156354110af98694d50,0x54110afb8258d50442de,0xe7b8558d504439e21563,0x98d50442ee6126354110,0x442be60b6354110b7985,0x2097354110bf3815cd50,0x54110beb825cd50442fa,0xbb9849cd50442fc60673,0xdcd50442fc6077354110,0x4437ca077354110df181,0x59154541109f984dcd50,0x54110dbb7455150443ae,0xb7b8255150443dc60554,0xd5150443cedd15454110],#[0x442be60b6454110b7982,0xdd36454110af983d9150,0x54110bf3815d150443ae,0xcfb8758a504427e60f74,0x54e50442fce055394110,0x4433ee1d6394110dd973,0xe0971d4110cf5625c750,0xd4110cf5635c7504427d,0xa7f8558b504433b5c962,0x5c0324429fe1563d4110,0x4433ed95700c910cf965,0xd95740c910cbd655d032,0xc910aef82594324432f,0xc7d7559432442afe1165,0x594324423f61d650c910,0x4431f5d7650c9108ff87,0x601750c9108fd87d9432,0xc910c7d865d4324435e,0x8ff855d8324431fa1975,0x59132443d354d524c910,0x4432f5d3644c9108fd87,0xe01744c9108fd87d9132,0x4c9108ff865d1324427e,0x8fd8759532442afe1165,0xd95324423fe1d654c910,0x4427ee01754c9108fd87,0xe09764c9108ff865d532,0x4c9108ff845d9324433b,0xde5525c6324423fe1576,0x5c6324433d595718c910,0x4433b5d9528c910cf765,0xe11658c910adf8359632],#[0x8c9108fd8759632442af,0x8fd87d96324423fe1d65,0x5da324427ee01758c910,0x4427e60f70509108ff85,0xe1165509109f985dc142,0x909108ff8759542442af,0xcf5655c6424437954971,0x54a42442fae015290910,0x442afe116590910ced76,0xe1d65909108fd8759642,0x909109fb805d6424423f,0xdf1711c1524423fe1576,0x1c152442f660c7054910,0x4433e5d87054910bb984,0x9c77054910df171dc152,0x54910cf976dc1524437c,0x9f581dc1524433e9db70,0xdc1524437c6077054910,0x4433ed8b7054910df281,0x61370549109f983dc152,0x54910cf965dc1524427e,0xcfa86dc1524433ed9770,0x989524427e6037154910,0x4429f6176254910bad84,0xe1d6354910b7980d4d52,0x54910aed82d8d524423f,0x8fd87d8d5244337dcf63,0xdcd524427d6077354910,0x442bb60b64549108fd86,0x61f6454910cbf74d9152,0x549109f581dd1524423f,0xaef82595524423f61b74],#[0xd9552442afe116554910,0x442b7e0d7654910aed82,0xe0d7654910abf845d952,0x549109bf845d95244277,0xcf7815d9524433ee0176,0x5d9524423fe057654910,0x44337e0d7654910cdc83,0xe1576549108ff835d952,0x549108fd80dd9524431f,0x8fd84dd9524423f60f76,0x5c6524433d5957194910,0x442bbe096594910cf765,0x60b6594910abf8459652,0xd4910cfb625c352442bb,0xcfb635c3524433e58d70,0x5c3524427ee0d70d4910,0x4433ed9170d4910cf964,0xd8971d49109fb845c352,0xd4910cf5635c7524433d,0xcf5645c7524433dd8d71,0x5c7524433dd9171d4910,0x4429f61762d49109f784,0x5cd63d4910aef8258f52,0xd49108fd8758f5244337,0x8fd87d8f524423fe1d63,0x593524427de0573d4910,0x4423f61d64d4910cbd74,0xe1176d49108fd87d9352,0xd49108ff835db524426f,0xcbf845db524432f21176,0x58d624423fe1176d4910,0x442bbe096558910aef82],#[0xdd56558910abf8459562,0x58910aed82995624431f,0x8fd84dcd624431fdd665,0x1d5624423f6177358910,0x4431f5d47558910add83,0xe0d7558910af7815d562,0x58910af5819d562442b7,0x8fd83dd5624431fdd675,0x596624432f5957498910,0x442afe116598910aef82,0xe1573d8910c7d7559662,0x551108ff835d7624423f,0x9f980dc9544437c5c570,0xdc9544427d6077255110,0x442afe1165551108fd86,0xe116555110e7b8059554,0x55110cfb805d9544438f,0xcbf845d9544423fe0976,0x5c3544423f60b7655110,0x4427ee0172d51109fb83,0xe1165d5110cbf645cb54,0xd51108ff825db544438f,0x8ff835cb644432fe1176,0x5d7644423fe1572d9110,0x4432fe1175d91108ff82,0xdd37059510df371dc165,0x59510dbb80dd1654436e,0xef371dc1654432fdd370,0xdc165442be60f7059510,0x443aedd37059510eb874,0x5c87259510af984dc165,0x59510cbf741c9654433b],#[0xaf7815c965442bee0172,0x5c965442b720d7259510,0x4432f1d17259510adf83,0xe117259510cbf745c965,0x59510af9809c965442af,0xcef729c965442bd60672,0x9c9654432fdd27259510,0x4432f1d37259510abd84,0x60f7259510cbf74dc965,0x595108fd84dc9654423f,0xebb80dd165442bee0174,0xdd1654423f60b7459510,0x4432fe037459510cbd80,0x60b7459510cbc82dd165,0x59510cbe82dd1654432f,0x8ff835cb654432fe0b74,0xd4d40842ee6135350210,0x8427e61f5350210af986,0xe0d7550210eb96555140,0x54210cfb865d5408427e,0xef16154550843b658d31,0x5c550843b658d5154210,0x842eee117154210ed963,0x58d5254210ee96254950,0x54210e7b7654950843b6,0xed9635c9508439e58752,0x54d50842bee197254210,0x843b65cd6354210ed963,0xd516354210e795458d50,0x54210ed98158d508439e,0xed97458d50843b655163,0x58d50843b66116354210],#[0x842fae097354210ed985,0x6137354210afb865cd50,0x54210eb964551508427e,0xafb865d1508439edd954,0xdd9508427e60f7454210,0x842be60f7654210af982,0x54d514c610af984dd950,0x4c610ed56354531843d5,0xadd8654d318439d59551,0x58d31842b7e19534c610,0x8427ee01754c610cdd75,0x60372546109f983dc151,0x54610cdd63dc9518427e,0x8fd86dc9518431f59772,0x54d518439758d5354610,0x8429fe195354610a7d86,0x61b5354610e5d63d4d51,0x54610cdf7358d518429f,0xe5d8558d51843b560563,0x58d5184397a156354610,0x84337a1d6354610cdd87,0xe0d65546108fd86dcd51,0xd4610cf9625c3518429f,0xced7258b518433e58d70,0x5cb518427ee0172d4610,0x8431f59572d4610cdd63,0x61953d4610e5d6354f51,0xd4610cdd7358f518429f,0xcdd8758f518439761563,0xd4961842be6035258610,0x8423f61f5258610af581,0x5977054a10ee962dc152],#[0x54a10cf976dc1528439e,0xcf986dc1528433e59770,0xdc5528427e6037154a10,0x8433758f7154a10ced62,0x58d71d4a10c7d65dc552,0x54e10c7d655c75284337,0xcdd63dc5538427e60371,0xdd15384337dd16354e10,0x8423f61b7454e109f980,0x6137654e108ff845d953,0xd4e10cf9645c3538423f,0xcdd7458f538433758d71,0x593538432f5d164d4e10,0x842b7e0d5458e108fd87,0x60f5458e10af980d5163,0x58e108fd87d5163842b7,0xadf855c563843375d571,0x55163843a75d15458e10,0x842b7e1d5458e10add87,0x5d57458e10add87d5163,0x58e10adf855d16384337,0xadf845d563842b7e0575,0x9d563842b76067558e10,0x8427e6037355210add84,0xe0d76552108fd86dcd54,0x596108fd83dd9548423f,0x8fd84dcd65842afe1171,0x54d610823f60f7459610,0x82bd6135358420af784,0x5937254c20ecd63dc953,0x54c20e6d65dc953083ab,0xced64dc9530833b5db72],#[0xdc9530833b5977254c20,0x8337dd16354c20ced86,0x60d6454c20cbf7459153,0x54c20cbd8759153083a7,0xc7d65dd1530832fa1d64,0x5d9530823f61b7454c20,0x823f6137654c208ff84,0x5d164d4c20cdd7458f53,0xd4c208fd87593530832f,0x9fb805d3530832f61d64,0x5d1630831f59574d4c20,0x82b7e157458c20cdd75,0xe117558c20ecf825d563,0x59420add849d563082b7,0xe6f825cd650823f61373,0xdcd650829fe117359420,0x483da6015254120a7d84,0x5493154120f6b8054950,0x54120f69528c550483da,0xf395450550482be61a31,0x54550482be61a4154120,0x483da54a5154120f6952,0x5496154120af98694550,0x54120b7b8558550483da,0xb798598550483da54a61,0xd8550483ba54b6154120,0x483da5487154120eeb72,0x1c97154120f69525c550,0x54120beb825c5504837a,0xf69529c550482eee1171,0xdc550482fa60a7154120,0x483da54d5254120f6952],#[0xdcd5254120eeb6354950,0x54120f6973549504837a,0xf698354950483dadcd52,0x54950483dae0d5254120,0x4837a5cf7254120f6887,0x6137254120f6954dc950,0x54120ddb7354d50482fa,0xbeb825cd50482be60763,0x55150483da6095454120,0x482be6076454120f3b74,0xe1d654c520beb825d150,0x8c520cf576546314823f,0x8fd8759631482b7e0d65,0x5da314823fe1d658c520,0x4827b60b70545208ff85,0x6076354520a7d85d8551,0x54520cdf73d8d51482bd,0x8fd86dcd514823f61f63,0xd9551482bde056554520,0x482b7e0d7654520af581,0x60f76545209df835d951,0x94520af781596514823f,0xcfb615c351482bd60765,0x5c3514833ed8d70d4520,0x4835e55170d45209fb83,0x61761d4520cfb645c351,0xd45208fd87d8f514829f,0xc7f75595614823fe0d76,0x596614831fdd66558520,0x4831f5d56598520af781,0x61b7154d209f980dc553,0x54d209f980dd1534823f],#[0xadf83595534823f61b74,0xdd9534823f6077654d20,0x4827be1172d4d208fd84,0xe1176d4d208ff815db53,0xd8d208ff855c7634823f,0xdeb72dc1654823fe0575,0xdc1654833edc77059520,0x482be60f7059520eeb72,0xe017159520cf5711c565,0x59520adf835c565482be,0xcf7719c565482be60271,0x5cd654823f60f7159520,0x482bbe097359520afb80,0x61373595208fd81dcd65,0x54220ef161545508823f,0xe7b52585508839e54961,0x5c5508833edcd6154220,0x8833edd97154220bbb84,0x5895254220afb865c550,0x54220beb8254d50883ba,0xe795458d50883b658d53,0x5cd508839ed516354220,0x882bee197354220beb82,0xdd95454220eb96455150,0x54220afb865d1508839e,0xaf983dd950882be60776,0x58551882be6137654220,0x8839d54d6154620cf772,0x6037254620e775358551,0x54620e5d6354d518827e,0x8fd86dcd5188337dcd63,0x5d951882afe117654620],#[0x8832fe1176546208ff83,0x58970d46208fd83dd951,0xd4620cf9635c3518833e,0xe5d6354f518823f61d62,0x58f51883375cd63d4620,0x8827be0973d46208fd87,0x6035258620afb8054961,0x58620af581d4961882be,0xaf980d4d61882bde0553,0xd4d61882bd6075358620,0x8823f61b7154a208fd87,0x6037154e20deb725c153,0x54e208fd86dc5538827e,0xced76dc953883b358f72,0xdc9538837a6037254e20,0x8833b5937254e209ed81,0x61b7254e20ced65dc953,0x54e20cdf7458d538833b,0x8fd86dd1538827e60374,0x5d9538823fe057654e20,0x8823fe117654e20cef82,0x6137654e208fd81dd953,0xd4e20cf9645c3538823f,0x8fd87593538832f5d164,0xd5163882be6035458e20,0x8823f61f5458e20add83,0xe0d76552208fd86dcd54,0xd52208fd83dd9548823f,0xabf845c5658827be0973,0x5cd658823f60f7159620,0x8823f6077359620aef82,0x60f74596208fd84dcd65],#[0x54550d7952dc1515423f,0x9f983dc1515427e60b70,0xdc1515435e5537054550,0x5438fd9154545509f984,0x5497094550cbf74d9151,0x94550cfb635c2515435e,0xaf582d86515439d54b61,0xd8a51542bd60f6194550,0x5423f61f6294550ced72,0x5c961185508fd87d8e51,0x18550eb784584615433d,0xd6d72548615433de1d61,0x5c8615423fe1d6218550,0x542bbe0963185509f980,0x60173185508ff8758c61,0x58550db874dc1615427e,0xd6f72549615436edd370,0xd49615434fdd15258550,0x5425fa1f5258550d3f74,0xa0c6258550add8318961,0x58550cbf7418961542b7,0x8fe8718961542af61062,0x989615432fdd16258550,0x5432fdd26258550cef72,0x2096358550cbf74d8961,0x58550aef8258d61542bb,0xcbf7498d6154337dce63,0xd8d61542af6126358550,0x5432fdd36358550cbc74,0xdd15458550e3f6455161,0x58550d3f74d51615434f,0xe7552d86615436ee0374],#[0x54a61542bd60b6198550,0x5435e5c35298550d6d72,0x61f5298550d6d72d4a61,0x98550af78158a615425f,0xcef635ca615437a60172,0x5ca615435b6157298550,0x542bee0162d8550ced86,0xe0172d85508fd8794b61,0xd8550cf8805cb61542be,0x8ff835cb615433ee0172,0x5cf615423fe1172d8550,0x5423fe1173d85508ff82,0x61273d8550af9809cf61,0xd8550a7d859cf61542af,0x8ff835d3615423fe0974,0xdc1525427e6077054950,0x5427e61370549509f983,0xa187054950b79811c152,0x54950b7981dc152542de,0xb7983dc152543dad8b70,0x5cd52542de6137054950,0x5433bd897194950b7b80,0x6017118950aed81d8a52,0x18950df1805c4625427e,0xcef8758862542bbe0562,0x5c7625433bd897198950,0x542afe1171d89509bf84,0x21171d89508ff835c762,0xd8950cbf845c7625432f,0x8ff815cf625423fe1171,0x5d3625423fe1173d8950,0xd423fe0d74d89508ff81],#[0x20d7258750abf845c161,0x58750adf835c961d42b7,0xabd849c961d42bd60672,0xdc961d423f60f7258750,0xd42bd60673587508fd84,0x61373587508fd82dcd61,0x587508fd82dd161d423f,0xadf835c562d423f60f74,0x9c562d42be6027158b50,0xd423f60f7158b50aed82,0x6077358b508fd84dc562,0x58b508fd84dcd62d423f,0x8fd81dd162d42bee0174,0x1800023f60f7458b50,0xa80240078018004800c,0x65053412c04500ea0300,0xc07501bc069017a05d01,0x8dc21f084020107c81e,0xbac2ca0ac829109e4258,0x5c33f0cc03210c483030,0x83ea0f243ba0e4036f0d,0x471114044110ec41a100,0xf813a44e313504b31248,0x2153053d14b851f141c4,0x167458e162057915a855,0x74c5cd171c5b816c85a3,0xb4627183c60017e85e21,0x864b191463f18e463318,0x68a1a106751998660196,0xdb1b0c6b41a946961a40,0xa1c5070e1bfc6f01ba86,0x1d2873b1cd472f1ca471],#[0xe9078c1e1876e1d7c759,0x887ef1fa47da1f2c7bc1,0x486d2178858212483120,0x8eb234c8b2228c894221,0x3c24b4915243c90023c4,0xd25f896f258095a252c9,0x273c9c026c4999264c98,0x85ca11282ca0527b49de,0xe8a742970a4d28b0a1d2,0x8ad72b44ab02a60a8929,0xb4c2cf4b2e2c58afe2b9,0x9d2e5cb882e08b732d90,0xe2f7cbd02f04bb22eb0b,0x309cc183024c032fd0be,0x198c573144c4b3114c36,0xcb13264c8a3210c753,0xccf933ccce43354ccf33,0xd4134c8d2c3474d0533f,0x92360cd743594d56351c,0x1372cdbc36d8da73660d,0x3828e0437d4def3780dd,0x96ce4c38f4e2e387ce10,0xb0e9d3a14e76399ce613,0xcee53b58ec73ae0eb23a,0xf2d3c9cf0f3c00ef13ba,0x7e3dbcf603d68f4b3cf0,0xd3edcfb13e88f9c3e34f,0x3fb4fde3f60fd23f30fb,0xb101d405d0083fe4ff3,0xf506e417d05041050324,0x90c843090b3429109541,0x122444d10443d50dd433],#[0x8545d91674585152450d,0xd46f91b846c91a346511,0x48191f747c51e247711c,0x9a525a4909233486d20c,0xe92b44ab929f4a412814,0xd3054bd92e74b612c94a,0x3564d1d3384ca53114c2,0xc24ea93894de936b4d71,0xc50353fe4fe13e94f693,0x510d43d50dd43150ad41,0x25148e51fd4705185452,0x4d4cd52f94b852c94a35,0x550353f54f753a14d953,0x54254cd524545550f542,0x8155c956c557554e5521,0xb57555bd56b95a856415,0x58bd61758215f957a95d,0x995656594164158ed635,0x6d6955a3d68959e966b5,0x16dd5b396bf5ae56aa5a,0x7375ca17195c056f25bb,0x765d9d7585d4974c5cf5,0xc5e997975e4578b5df17,0x5fdd7e85f657ca5eed7a,0xfd83960cd8246079806,0x618c962e98a262058606,0x1935647591764458f063,0x97d65dd9686565953651,0xbc66b59a766619926631,0x267b19e667399c867099,0x6865a1368359fe67e19f,0x961a52690da3d68b9a28],#[0x81a916a09a7c69d9a5e6,0xdaf46b95acd6b1dab86a,0xb4e6d21b306ca9b126c0,0x8d6e1db786dc9b6c6d75,0x56f19bc06ec5bab6e95b,0x6ff1bf66fc1be16f6dbd,0x135c3e70bdc297069c0b,0xdc7d71ddc687189c537,0x9cb372b5c9e723dc8972,0xcfb73d5ce6735dcd1730,0x4c74f5d2e747dd197405,0x47639d7f75c1d617549d,0x7735dbe76e1da97669d9,0x831dfd77b9de87765dd3,0x9e3c78d9e277861e127,0x1e69798de547939e4879,0xeb17aade9c7a35e8779e,0xe77b85ed27b31ec67b01,0xd7c5df117c09efc7bd9e,0x7d7df507ce1f327cb1f1,0xf2dfbc7e6df8c7df5f6e,0x4e00d7fd5fe67f81fd17,0x203a80d202e80a202280,0x8281f206d817a04f810,0xca82ee0b5829a0978246,0xb843210683ba0df83420,0x8576157852213984aa11,0x67218d861e18185ca163,0xb61de87621c986ea1ab8,0x620b88161ff87e61f387,0x24a88ee2238876217884,0xad8a7a2868a022688966],#[0xe8b9a2d78b462c28af22,0x8d2633a8cae3138c362f,0xdfe3708daa3648d7a34f,0xfa3b88eca3ac8e7638e8,0xe4008fc63e28f723cd8e,0x43690c2421906e415903,0x6c919a460916a44b90f2,0x693024a8928a49391ee4,0x94224f993ce4e4937a4c,0x4d6526948251a945250e,0xf656e957e550950653b9,0xe5ad967a598964a58395,0x5e397525ce97225c296c,0x22982a60497fa5f897a6,0x8992664398d262e98a26,0x9a6a68299ce66d997a65,0xb8a6dc9b366c79ae26a9,0x627099c0e6fd9bde6e89,0x673f9ce67339cb671e9c,0x77e9dbe7609d4674b9d1,0xbd9e967969e4278a9e12,0x79ffe7f99faa7e49f7a7,0xa166853a112835a09a81,0x2aa89ba256886a202868,0x7e8fea3768cea3228b9a,0x2961a54a94ca4f692ea4,0x9d6a71e9b8a63a97fa5c,0x39a8aaa09a7ea9eba772,0x5aa36a75a99aa57a922a,0xac2eaeaab6eac3aad2aa,0xddeb71ad8ab53ad12b23,0x22bb9aeceba4ae56b7da],#[0xabf8afcabe3af76bceaf,0xc37b0c6c2bb072c0daff,0x76b1c2c6ab192c55b11a,0xcb29aca0b26ac94b216c,0xb372ccdb31ecc1b2caca,0x46ed0cb41acf7b3a2ce2,0x46d4bb516d3fb4e6d2ab,0xed78b5cad63b576d57b5,0xdb7b6a2da2b64ed8db61,0xf6b79ede1b74adc3b6f6,0xeb89ae20b86ae14b816d,0xb9bae68b966e53b912e3,0xa92e9eba3ee80b9eae74,0x8eeddbb3aebfbac2eaab,0xaf1cbc5af07bbe2ee9bb,0xf5bbd56f4fbd02f31bc8,0x88be0af7cbddaf70bd86,0xbf2afbbbeb2fa6be5ef,0xc026ffabfd2feebf7efd,0xdb027c08701bc05700f,0x8f054c13b048c10b03cc,0x708ac21307ec1bf069c1,0xc9c30f0b4c2bb09fc26,0xedc39f0e1c36f0d5c33f,0xec49b120c44710bc3f30,0xc603171c58b15cc53713,0x7471cbc7171b6c67b18f,0x67213c8131f5c7bf1e0c,0xb264c957246c8df228c8,0x2b5ca9b28ec9ff270c9a,0xfdcb972dfcb672d3cb37,0xcccdb327cc63309cc0f2],#[0xce4338acdcb36ccd5333,0xef73b7cec73abce97396,0x3b3ffcfe73e1cf4b3ccc,0x343ed0bf429d06b414d0,0x462d173456d14344ad11,0x98d22747ad1d346ed1a3,0x2d3b34ddd3174b6d29f4,0xd4d3525d47f510d4074f,0x587552d533546d50353a,0x3b588d5e7573d5b7567d,0x35b5d6bf5a9d66b594d6,0x5f4d7bb5dfd7675d3d71,0x21d86f615d83f600d7eb,0x42090442d8cf62dd89f6,0x84820884820904420904,0x8848208848208848208,0xc0581206100dc4088404,0x60904190b04830b04820,0x482038200c0510083021,0x25040171182064942028,0x84c20184c24104819283,0x987250984100a84c30a,0x10482a130d4a13082415,0x441328210064a084a4a,0xb04c201845801045801,0x13080610042e150804c4,0x24130c0a13082a13080a,0x986100a84c309020054,0xbd8c0e18402a130c2015,0x81c0c10181a082001c10,0x40803080000205040a0,0x41000008022040000201],#[0x2001004600080c080020,0x800000000310041,0x402c1040000808301040,0x8881001008ac10101810,0x60c08000081040020c0,0x308c2005608080208001,0x80000482088c12200c20,0x4048905120803312462,0x20209208408040620323,0x10ae00800c12088816,0x22300040288122020136,0x482088c1014409101208,0x90412082a20484000060,0x20000002320840604460,0x10042918323510043118,0x20c31100422082230405,0x108880308440810922,0x200c2110241044722082,0x1102002010082080412,0x3c100060818183024104,0x41041e09101078200,0x84000400082160482080,0x4122020058103024401,0x440400b0206918400000,0x8a080010302060488080,0x20820000102000904102,0x408080410000782000c1,0xe0402080010410602800,0x20810100000822240840,0x50010041020200081040,0x80410024081810202003,0x20006304020820004240],#[0x81a08200004040000000,0x81810202840400202008,0x100820580040004020,0x28300030404040000008,0xa081a03000c0e081410,0x14151020505000812504,0x410400a8341040010008,0x208890210541002a080,0xc282220084050445810b,0x41028200040000a08401,0x22e9284000010402081,0x40a0800101020814100,0x60a4480082f22080605,0x10b8215040800300040e,0x20504440800000200,0x40010008141000a08041,0x20014002001250,0x20504003020818103020,0x40110542c28215040c28,0x82010682080810004220,0x820000614021004102,0x8000106040a08005040,0x8385070a08185070a,0x20048183021202840604,0x881014a081410000a8,0x82030400081410282080,0x38101880308000800100,0x4401808392e070018000,0x2020408020808030107,0x4000c401808311304201,0xc10082002c1028211080,0x802000410000202002],#[0x404000001880208000,0x80000408001040008200,0x820203810400108020,0x18103020991040004102,0x40620042002006098808,0x40084000410000802230,0x282000000400082000c,0x40608005040808001000,0x80000000010000080000,0x8003041e0800004000,0x404080c4000400001040,0x80412002050400103250,0x5040028241040000a0,0x1000020205040010200,0x200101000000000a080,0x20000100020000100,0xe040000a08000040000,0x80412090020000002000,0x560c1858100020204000,0x84010400902004810b0,0x99410000000024081840,0xc08006040608306040c0,0x80008001001608106060,0x212041c083c1001e0b0,0x20014104240800038100,0x40600203042408001008,0x18100000000000000c10,0x60182a0820504140854,0x70400a8325044405080,0x4a1000c041207080a080,0x14a0800c054a0829,0x40000110215042a08141],#[0x19282010400502830,0x20c04100000020000,0x82010208294a10001000,0x2008810008000805228,0x820000004000000000,0x40000008022040808001,0x2008810000000080010,0x100000020008000000,0x88208000040000200,0x3282000012082650414,0x104001820000000100,0x408081010200000000,0x10006a58104000400000,0x80400100000400004a,0x82000200001000200040,0x2000400080020403220,0x4800c0a0200060004001,0x5040028207040e08140,0x184a071004081c10b02,0x50008141004a0818104,0x41030280042c13030607,0x808048042858504840e1,0xe0a0860201040102821,0x10020a1c160410601680,0x9c2840000c042a090810,0x50400602005410c820,0x141000200040000808,0x10400000002000408080,0x20000104000000000820,0x8081000408041000000,0xe080000000000000406,0x10000080001c100],#[0x205040008010040008,0x82001410018060800000,0x2a0814100000002,0x1908200021040008541,0x810002040400008080,0x800100000000020000,0x4081c1000808001000,0x80000000070400,0x4000000800000100000,0x41000608000,0x10800b02061410b02000,0x82c0040200340042b2,0x10408010a8008041,0x82061410282050010902,0xa0021606800d00102,0x840e068a12081c08381,0x820000e9184000000040,0x20a890202800848190,0x140040010cc50800b5,0x800d0504c00406282000,0x20800004000020,0x810a8207040000000000,0xc02190b8418042a085,0x3820314102820204,0x10200000004040000,0x80000010082000000400,0x100000060,0x408]]
set_option maxRecDepth 16000 in
def g235H6 := limbs80 #[#[0x10150410016102100370,0x10a0000221016102000,0x14120110030311151001,0x2110003818700203303e,0x8200000000d21b010271,0x590000a4a300000000e0,0x8222b4470000104d12,0x820a0000c43100,0xb9000000000000000000,0x11402a00000000103144,0x76605be0141071b05c20,0x18000000000000107a30,0x4127d09622,0xf0000000060a6811500,0xc25af039000050,0x2a00000000509c000000,0x41c0b2a40a0000000092,0x27342630150000000049,0x6b605d00250000601f40,0xb412c4,0x802200,0x260e0000c0aa00,0x323500000000000000,0x28717a000000000000f2,0x40af00000000d0,0x0,0x902000004006000000,0x0,0x530000008c3223000000,0x50440000000005,0x0,0x800861184278000000],#[0x1442e0bb00,0xf09e0000000000,0x9d0000f0540000b04800,0x81240000d0,0xa80000510df01ed03200,0x2212000000002121a4,0x846900002097610e00,0xb02ba05ee08f00,0x40000838e0000121f00,0x693e404fb2,0x3086000000,0x57000000000000000000,0x200e000060,0x0,0x0,0x70bf0000000000,0x203cd0090001f0a000,0x1000010b6150a000000,0xa216b2,0x54070000421520a500,0x11203ba056d051000000,0x70a412383050a47333,0xb0000000002253490400,0x600330,0x33000000000000000000,0x212e0000000094,0x10000000000000000000,0xd058000090,0x8e000000000000331c00,0xf3160262000082,0xba00330000e30f040100,0x800000000401c10b750],#[0x66b06000000000000034,0x71000000005318c80ad0,0x94,0x3000000000,0xe085805a906f00,0x5fb03d00000000000000,0x0,0xc6800000000000,0x980000e47a122b000000,0x625cd6120000743f90,0xe0387470930c00,0x1e0000e30e6328402c00,0x71,0x0,0x0,0x3bd06140950000000000,0x945000000000a4,0xf040000000,0x2c000000490421000000,0x531f0000208121,0x82130000300b000000,0xab00001047967a000000,0x2420726402207c501270,0x680000907e0000c46790,0x90ac0000508020a230,0xe0943035000000,0xd0a8a00c000000,0x520e0000e4ba000000,0x50b5000000,0x1d000000008219000000,0x1a000000000000000090,0x6a0000000000000000b1],#[0x64bb0000c052d4,0x0,0x90180000000000,0x0,0x306900,0x1315393c000000,0xc0a92087b32000,0x231d0000000000,0x7de903315550a1604e00,0xb254384c307f0000c0,0x0,0x231700,0xd22f0000000000,0x3a321a00003084f07900,0x21,0x7800000000000064bc00,0x411170000b03ab0,0xa3608d00000000000000,0xf0ad00006126e3,0xb21de0b8b13400,0x851e00,0x7091000000,0x0,0xd12f908ac445c23300,0xb29f000000,0x2d000000007073000000,0x59531400000000000060,0xa7000000000000e70b80,0x5017930b000070,0xc01a000000,0x6d000060b30000000000,0xa204100000000000030],#[0x69,0x50160000d31300,0x602e00,0xd14c00000000206700,0x595800,0xe1540000000000,0x108b0000b446200700,0xe04b00,0xa6065f27d411f308300,0x50000000034a4107030,0xa0aec0555119c4,0xd156806a20b1000000,0x506e00,0xa3b0bd90050000000000,0x6b31ac0460000000080,0x2f7468004ab029000034,0xb4000000000000e11120,0x770000000070190000c0,0xd093721ed036b045a0,0xa44ed026503e00,0x99000000000000000000,0x7b810a6390f09f000000,0xa0210000000010,0xa08e0000000000,0x304c000000,0x75000000000000000000,0xbe000000000000000010,0x4fc023000000000000c0,0x4e000010899043000036,0x29096,0x9f00000000712be06c00,0xb0b90000000064],#[0x3ff06400000000000000,0xe12d0000b10f0000c0,0xd10cf092000000,0xbc793db52a0000000000,0xe08800000000b0,0x9a70340000c062000000,0x4d00000000d030f443b0,0x205374,0x590000b438000001b200,0x9b000000000000409039,0x400000a013213b000090,0x59,0x1b621c0000c063000000,0x37006bf00d8803804290,0x250000000080740000e0,0x900200000000000031]]
set_option maxRecDepth 16000 in
def g235D7 := limbs80 #[#[0x2ecb9840887e12108110,0xaf2ea102216e5d02044,0x836cb1aa1084bf745951,0x10ddac4a9021da549504,0x427ebb2a40867d65548,0x810cfacba90213fdd952,0x40435eb22a8084fd76d4,0x50109faecaa0219f5955,0x540433eb2ea8084ff765,0x594109fee4b28213f5db,0x420443f8a8840884ff74,0x1c81109faec902217e5d,0x4720443f8a0e40885f57,0x52c8110fd28590221fc5,0x5d720442fcba640887e9,0x2214c110fe242982217e,0xc90530443f8a0a60887f,0xf2514c110fe2a298221f,0xbed89304437cb1260887,0x6fb654c110df2ca98221,0x1be58a30443f8a8c6088,0x86f9658c110bf2e71822,0x217d5c730442fcbac608,0x887f15150110b7ae9982,0x221ee55140443dca1280,0x885f97550110df2caa0,0x2217e5ce40443f8a8c8,0xa0885f97590110df2cb2,0xa82213f5d950442fbb8a,0xaa0887f25154110fe2a2,0x4a8221fcdc550443f838,0x12a08877b5254110ef2a],#[0xc6a8221bed89504437cb,0xb9aa0886fb6354110df2,0x6a8a8221de55150442fd,0xdb22a0886f96454110ef,0xf2c5282217edd1504437,0xfcb9ca0886f96394110d,0xbeae3a82217e5d650442,0x2deba064885f9700c910,0xafcea192215f5d43244,0x427ebb264884fd760c91,0x109faed192217d5c6324,0x442fab8c84885fb70509,0x910bf2e0292213f5da42,0x2442eeb98a4885f57114,0x4910b7ae829221779cc5,0x52442fdb82a4884fd761,0x949109feeca92213f5d9,0xa52443b7a94a4885f571,0x1d4910bf2e1a92213f5d,0xcd624427ebb6a4885f57,0x74989109feeab12213fd,0x5d7624427eb9ec4885bd,0xd6555110d7ac8aa2213f,0xfdd9544427ebb2a88867,0xbf64d5110bf2e1aa2213,0x3f5db544433eb2ea8886,0x4fd75d91109fae5b2221,0x1bedc165442dfba2ca88,0x84ff72595109fee0b2a2,0x21afdd1654435e3a2ca8,0x84fd72d95109fee8b2a,0x4217e5d720843f4a9641],#[0x1086f96550210f72a8a0,0x8421de54950842fcbaa8,0xa1086f96254210ef6a4a,0xa84217edcd508437cb1a,0x2a10877b5454210ef2a8,0xca84217edd1508437cb2,0x82a3086dd634c610df6e,0xc6a8c21b758d51842fdb,0xb86a30867d6554610dbc,0xcc7a8c21b758f51842fc,0xdb82a50867d65d4610db,0xbac6a9421bb58952842f,0x3eb2aa5086de6354a10d,0x9feeca94213f5d952843,0x36eb1ea5085f970d4a10,0xcfacba9421b798f5284,0x436eb1aa7084fd76d4a1,0x109feeca9c213f5d9538,0x8436eb1ea7085f970d4e,0xe10dbae2b1c213f5db53,0x38436faa2c7086dd5458,0x8e10dbaeab1c21b75d16,0x638436eaa4c7086de755,0x55210d7ac8aa421b7d52,0x9548427ebb2a90867d65,0x5d5210bf2e1aa4213fdd,0xc9658427ebb6a90867d6,0x74596109fee6b2c213fd,0x58d510837ab0aa2104ff,0xd6554420dbcc6a8841b7,0xfdd9510827ebb2a21067,0xdd63d4420deac3a88413],#[0x9f597510836f31ea2106,0x6f553584209faeda8841,0x1bd5d5610837ba9ac210,0x6f55398420deceab084,0x417bdc9530837ba9cc21,0x106bd6454c20dbac6a98,0x8419f595530835f322a6,0x6104ff7654c209faeca9,0x9841af593530836eb1ea,0xa61067d65d4c20d7cc9a,0xb1841b75d1630827ebb6,0xaca106de7558c20dbaea,0x2b28413fdcd650827fb8,0x9aca1067f7159420cfae,0xa4a82419fdcd650833eb,0xbb2a0905ef7254120eda,0x2a4a8241bed85504827e,0xda92a0907ea5254120fd,0xd6e4a8241fa1c950483b,0xfdb9aa0906fb6354120f,0xef6a8a8241de55150482,0x2fcbaca0906fb6454120,0x9faed18a417b5cb5048,0x82eeb98a2905f9701452,0x209feeca8a413f5d8514,0x4827ebb4a29077751945,0x5209faeda8a417e5c351,0x34827fbb2a6904fd75d8,0x4d20bdae5a9a417e5c35,0x634827eb8ec6904fd76d,0x59520df6e0b2a413f5d7,0xd654827fb8aca904ff70],#[0x1542209fae3b2a413fdc,0x4950883bca92a1106f96,0x7354220df2c6a8441ded,0xd5150883bcaa2a1105fb,0xb7654220df2c8a8441de,0xf5d9518837ab0aa3106f,0xf970d46209feeca8c413,0x7edc1528827ebb6a3105,0x5f970d4a20cfacaa9441,0x17bdc9538833eb2ea510,0x4fd7654e20dbac6a9c4,0x417e5c3538827fbb2a71,0x106bd64552209faeda9c,0x4413f5d9548833eb2aa9,0x9105f970d52209feecaa,0x2c413f5db548833eb2ea,0xcb104ff73596209fee2b,0xb08a1bd5c9611427fba2,0x2a2a86ed7158850deae6,0x328aa17e5c251542fdb8,0xa2c2a86f56118550deec,0xc330aa16fdd161542de3,0x394c2a85ed7298550dee,0xae7b0aa13f5cb61542f7,0xfaa6c2a867d54d85509f,0xf6e0a92a13f5d3615433,0xbdb82a4a87787054950b,0xddec5292a17e5c252543,0x2beba6a4a857d7594950,0xbece2312a17d5c46254,0x42eeb98c4a86ed621895,0x50b7ae8312a1779cc625],#[0x54377b14c4a85be74189,0x9509fae7b12a13f5c762,0x1d427fb92c3a84fd74d8,0x8b509fee8b0ea13fdcd6,0x62d427fb9ac5a84ff715,0x54810dfacaa90213fdd1,0x9540437eb2aa8086fd76,0x459410dfae4b2821bf5d,0x4520443fca8240886fd7,0x6548110fdaa490221fd5,0x54320442febaa40886fd,0x551c8110ff6a190221fe,0xf59720443f6a9640887f,0xf954c8110bfaeb90221b,0xfe59720443fdaa640887,0x7f9504c110ff4cb90221,0x1fd54530443fda826088,0x87f9514c110dfaca9822,0x21fe5c530443fda8a608,0x887f9524c110ff284982,0x221fe58930443fda9260,0x887fa654c110ff2ca98,0x8221fed4a30443fca946,0x60887fb538c110ff2a71,0x98221fd54730443fca86,0xe60886fd65cc110fbaa7,0x4a0221fe4c940442feba,0x9a80887fb5250110ff2a,0xa520221fed4d40443fca,0xa9c80887fb5290110ff2,0xaa2a8221fed4e40443fc,0xfa92a08877d5254110fe],#[0xfee4a8221bf58950443b,0xffb9aa0886fd6354110b,0xff2e2a8221bf59550442,0x3fc192a0887fb7154110,0xff464a8221fe4c95044,0x43fca12a0887fb325411,0x10ff2a4a8221fe909504,0x443fcb12a0887fa52541,0x110ff0e4a8221fe98950,0x443fd392a0887f97254,0x4110ff286a8221fedc95,0x50443fca9aa0887fa435,0x54110ff2c6a8221fe94d,0xd50443fc39aa0887fa63,0x354110ff4e6a8221fe5c,0xd150443fcaa2a0887fb7,0x5294110ff6e8a8221fe5,0x54b50443fca9ca0887f9,0xd72d4110dfac5a8221df,0xf5cf504437eb1ea0885f,0xff650c910dfaca192217,0x7f5d832442feba864886,0x6fd644c910fdaa499221,0x17f5d1324437fb226488,0x86ff654c910dfaca9922,0x217f5d932442febaa648,0x886fd658c910fdaa5192,0x2217f5d6324437fb2c64,0x4886fd6550910bfaed19,0x1221bf59642443f6a948,0xa4885fd7614910bfaeb2,0xa9221fedc152443fc382],#[0xaa4887f57154910bfee0,0x4a92217fdc552443fb38,0x12a4887ee6254910fdac,0xa6a9221df54d524437fb,0xb1aa4886fd6354910efe,0xac8a92217fdcd524437f,0xfba2a4886ff6454910df,0xfecaa9221bf59552442f,0xfebb2a4886fd7654910d,0xbfeeca9221bf9d952442,0x37eb2ca4887ed6294910,0xbfaeb29221bfd965244,0x42feb86a4885fd769491,0x10dfec5a92217f5c7524,0x4437fb1ea4886fd63d49,0x910dfac9a92217f5cf52,0x2442feba6a4886ff64d4,0x8910dfac6b12217f5db5,0x624437eb2ac4885ff735,0x58910bfeeab1221bf995,0x5624437fb9ac4886fd73,0x558910dfaeab1221bf1d,0x96624437fbaac4886fe7,0x7055110bfaeb31221bf5,0x59554442ffb92a8887f9,0xd72d5110dfaecaa221bf,0xfdc965443fdb82ca885f,0xff7059510f7ee8b2a217,0xbf5c9654437e392ca886,0x6ff7259510dfce4b2a21,0x1bfdd1654437eba2ca88,0x87f95350210bfae532a2],#[0x21fe4c550843fda9a810,0x87f97154210ff2a2a84,0x421fe5c950843fca92a1,0x1087f97354210ff2a6a8,0x8c21fe5d150843fcaa2a,0x63087dd534c610feaa29,0xa8c217f5d5318437eb2a,0xaa3085ff7254610dfac4,0x6a8c21dfd4d51843bea9,0x2aa3085ff7354610dfac,0xe5a8c21bf58b518437eb,0xb1ea30877d53d4610bfa,0xea4b0c217f5cf518437e,0xfb8aa5087fb7054a10df,0xfaeca9421bf59552842f,0xfcb82a7085fd71d4a10d,0xdfac8a9c217fdc553843,0x37eb2aa7085ff7454e10,0xbfae3a9c21bf5d95384,0x42feba6a7086fd64d4e1,0x10dfea8b1c21bf551638,0x842ffb9aa9087f970552,0x210dfaecaa421bf59554,0x58437eb8acb085fd73d5,0x9610dfae6b2c21bf5c96,0x510837eb2aa2106fd745,0x54c20fdee4a9841bf5d9,0x553082ffba2a6106fd64,0x4d4c20dfaeca9841bf59,0xc565082feba6a6106fd6,0x7154120dfae6b2841bf5,0x59550483f6a92a0905ff],#[0xa3154120ff262a8241bf,0xe90550483fca0aa0907f,0xfa5154120ff2a2a8241f,0xfe98550483fcb0aa0907,0x7f97154120ff0e2a8241,0x1fedc550483fd38aa090,0x7fb7254120ff2e4a824,0x41fe5cd50483fca9aa09,0x907f95454120ff6e6a82,0x241fedd150483fcba2a0,0x2905fd71d4120ff2a328,0x8a41fd546314837eb2a6,0xa2905fd758c520dfacb1,0xa8a417fdc151482febb0,0xaa2907f66154520feac2,0x6a8a41df54d514837fb0,0x9aa2906ff6354520efea,0xcaa8a41bf59551482ffb,0xbb2a2906fd7654520dfe,0xeeca8a41bf9d951482fe,0xeb2ca2907f56194520bf,0xfaeb28a41bfd96514837,0xfeb86a2905fd7694520b,0xefaa7a8a41bfd8751482,0x2feb9ea2906ff63d4520,0xdfacab0a417f5db5148,0x82ffbaac2906fe655852,0x20bfaeb30a41bf596614,0x482ffb8aa6907f97054d,0xd20dfacaa9a417fdd153,0x3482feb8ea6906fd7654,0x9520ff6e0b2a417f5d35],#[0x654837fb82ca905ff715,0x59520dfae2b2a41bf1c5,0xd654837fb8aca906fe71,0x199520dfee6b2a41bf5c,0xc550883fca8aa1105fd7,0x7254220ff2a4a8441fe5,0x5cd50883fca9aa1107f9,0x97454220ff2a8a8441fe,0xf54d51882ffb92a3107f,0xfd6354620efea6a8c41d,0xbf59551882ffb9aa3106,0x6fd62d4620dfaeca8c41,0x1df54f51882feb96a310,0x5fd73d4620dfac7a8c4,0x41bfd49618837ea92c31,0x106ff5358620dfaa6b0c,0x441bf59552882ffb8aa5,0x7107f97054e20bfae3a9,0x9c41fbdc953882ffb8aa,0xa7105ff7454e20dfac8a,0xa9c41bf5d9538837eb2a,0x6a7106fd64d4e20bfae3,0x8b1c41bf55163882feba,0x2aa9105ff7355220dfea,0xe7aa441bf5d9548837eb,0xb92cb106fd7159620bfa,0xae8b2c41bf5cd658837e,0xea92a2a85ff7054550df,0xfee4a8aa1bfd8951543b,0x7fb22a2a877d5454550b,0xdfec528aa1df54a51543,0x37fb1ca2a85fd7294550],#[0xefaa430aa17f5ce5154,0x42feb90c2a86fd621855,0x50bfae630aa1bf58c615,0x543bea92c2a87fb70585,0x550df8c4b0aa1dfd4961,0x15437f312c2a86fd6258,0x8550bfee4b0aa1bfd896,0x615437f31ac2a86fd635,0x58550bfee6b0aa1bfd8d,0x161543bfaa2c2a877d54,0x458550dfec8b0aa1bf59,0xd161543dfba2c2a87bc7,0x5298550efaa530aa17fd,0xd8a615437eb14c2a877f,0xf6398550bfae530aa1bf,0xf54b61542feb9cc2a86f,0xfe62d8550dfac5b0aa1d,0x7f5cf61542feb96c2a86,0x6fd64d8550efaa9b0aa1,0x1bf54b61542feba6c2a8,0x86fd72d8550dfca5b0aa,0xa1bf5cf615437f396c2a,0xa86fd54d8550dfce7b0a,0x2a17fdc1525437eba6c2,0x4a877d7054950bfee6a9,0x92a1df5cd52543bfb82a,0xa4a877c7654950efee6a,0xa92a1df58b52542feb8c,0x2c4a85fd7118950efac9,0x6b12a17fdc562543fdb8,0x22c4a86fd6458950bfee,0xe3312a17fdd1625437fb],#[0xb9ec4a85fd71d8950bfa,0xae3b12a17f5d362542fe,0xeb9ec4a86fe71d8950df,0xfae0b0ea1bf5d3625437,0x7f392c3a86fd7258750d,0xdfce6b0ea1bf5cd61d43,0x37eb82c5a86fd7458750,0xdfce2b16a1bf5c562d4,0x37eba2c5a86fd7358b5,0xdc0160021002c002c00,0x13c022c03c006500940,0xf101c4034c06000ad,0x52c09e01290234042c08,0x324061c0bc016502b40,0xe01e903b4071c0dc01a5,0x92c11e02290434081c0f,0x5340a1c13e026904bc0,0xa02e105a40b0c15a02a9,0xcfc198032506340c1c17,0x7140dec1b4035d06a40,0x603f107c40f4c1de03a1,0x19c22a04410864107c20,0x964128c24c048908f41,0x804fd09d4137c26804c1,0x5bc2ae05490a6c148c28,0xb9416dc2d205910b041,0xe06290c2c180c2f805dd,0xa2c33e066d0cc4193c31,0xdec1b6c36206b10d3c1,0xe07510e841ccc3900709,0xe9c3ce07890eec1d9c3a,0x100c1fec3f407d50f741],#[0x40855109c20fc4120811,0x2cc4540899111421dc43,0x120c23cc47208d511842,0x20955128c24dc4940915,0x6dc4d40999130c25dc4b,0x140427cc4f409d9138c2,0x40a55148428cc5120a11,0xaec5560a9d151c29ec53,0x162c2c0c57a0ae1159c2,0x20b7116c42d3c59e0b29,0xf6c5e60bbd17542e5c5c,0x1864307c6080c0117dc2,0xe0c8918f431ac62c0c45,0x39c66c0cc9197432ac64,0x1a7c34ac68c0d0919f43,0xd8d1b0435bc6ae0d4d,0x7fc6f60dd91b8c36cc6d,0x1cac391c71c0e251c243,0xc0ea91d343a2c73c0e65,0xc1c77c0ee91db43b1c75,0x1ed43d5c7a20f2d1e3c3,0xc0fa91f343e4c7c20f79,0x2c7fe0fe91fac3f1c7d,0x20ac411c81c102920344,0x10b12144423c8401065,0x45c88210f921d4436c86,0x22ec458c8a8114122644,0x811c12364467c8ca1185,0x89c90c120523e4477c8e,0x24f449ac92e124924744,0xa12c1256c4a8c9481281,0xc9c98c130525e44b8c96],#[0x27044dbc9ae1349266c4,0xc13cd277c4ebc9d01391,0x7ca06140127ec4f8c9e,0x28ec51aca301449285c5,0x14d1298452cca4e1489,0x4eca96151d2a1453dca7,0x2b24560caba15612a9c5,0x615f92bcc574cae015ad,0x97cb2a16452c64587cb0,0x2d345a3cb4216792cdc5,0x816e52dac5b2cb5c16a9,0xcccb9217152e0c5bdcb7,0x2edc5d8cbac174d2e845,0x417b12f4c5e6cbc61779,0x4cc0417f92fcc5f5cbe,0x30bc614cc22183130446,0x8189d3124621cc3c186d,0x3ccc7418d9319462ecc5,0x325c648cc8a190931fc6,0x4197d32d4656cca6193d,0x76cce419b5334c664ccc,0x3464687cd0819fd33dc6,0x61a8134e4698cd281a41,0xb3cd621ab135446a5cd4,0x36346c2cd801af535c46,0x41b59369c6cfcd981b25,0xedcdd41b9137046dccdb,0x37f46facdf01bd537946,0xa1c2d3844706ce081c05,0x1cce341c5d38a4711ce1,0x3964728ce4c1c8938fc7,0x61cfd39e4737ce681cc1],#[0x4fce9a1d2d3a44744ce8,0x3b1475eceb61d613aa47,0x81dcd3b8476cced21d99,0x86cf081e013be4777cee,0x3cbc793cf201e313c4c7,0x61ea53d2c7a2cf3e1e6d,0xbacf701ed13d8c7adcf5,0x3e647c7cf8c1f093dec7,0xa1f6d3ec47d5cfa61f41,0xebcfd21f953f147e0cfb,0x3fcc7f7cfe81fc53f747,0x4201d4024801d0001ff5,0x1ad02e204d408c80dd01,0x4144825d048208540f48,0x820e141a4831d05c20ad,0x4cd096211d421c83fd07,0x42ec859d0ae214d42848,0x221b9435c867d0c82185,0x81d0fc21e943bc873d0e,0x44a4890d11a2225442c8,0x2295451489dd1362261,0xb8d16822c545748aad15,0x46648c8d18a230545e48,0x237546cc8d6d1a6233d,0xebd1d2239d472c8e2d1c,0x47ec8fad1ec23cd47848,0xa242d4844905d20423fd,0x1cd234246148ac910d21,0x4944925d246248148f49,0x624e549ac931d26024ad,0x4cd29225154a1493ed27,0x4acc955d2a425454a849],#[0x625a54b2c962d2c02575,0x79d2ee25d14b8c96ed2d,0x4c44985d30626014bec9,0xc26514c8c98ed31a262d,0xa2d34226754cdc998d32,0x4d6c9abd35226994d249,0x426fd4ddc9b6d36626c1,0xcfd39827294e349c3d38,0x4f0c9ded3b6275d4e9c9,0xc27c94f749ead3ce278d,0x8d40a28054fec9f9d3e,0x50dca16d4282841506ca,0xc28a9513ca24d4422879,0x3ed47628dd51a4a30d45,0x5284a4cd49229195214a,0xe298d52fca5ad4b22955,0x76d4ea29c1536ca6ad4c,0x543ca84d50229f953d4a,0x62a5d549ca90d51c2a29,0xa8d54e2a8d5504a9dd53,0x55c4ab5d5682ab95564a,0x42b19561cac0d57c2aed,0xd5d5a82b495674acbd59,0x573cae3d5c22b7556cca,0x2bd55794af0d5dc2bad,0x7d6082c0557ecafad5f,0x58c4b15d6242c39585cb,0xa2ca95934b22d63e2c71,0x3bd66e2cd1598cb2ed65,0x5a64b49d68e2d0d59fcb,0xa2d6d5ac4b55d6a62d3d,0x6ed6d62da15b24b60d6b],#[0x1084448212110848442b,0x6131512101296182121,0x513411010080094144c4,0x1541131010544d044040,0x40413254110104d04403,0x4504c30514130c944d04,0x14130c504c21514130c5,0x3138110151094504c325,0x484421611120c4c5054,0x12082040483080512101,0x86112e1058041844411,0x4380862e111200184438,0x4048206c411101200184,0x610244448309a2141210,0x111010244844316a2090,0x21644030610404820644,0x44840316a22312102448,0x22120c540c4831210084,0x486c51410102848403a3,0x8214101312105a898c48,0x12106488483161208644,0x4841512084048216a263,0xc084852315120c542488,0x5010063a206251858540,0x436315120d8c02889448,0x4250522170610198c185,0x83080605071018544094,0x544840a0906051054884,0x49448363228006118c00,0xa5120c144821525120c6,0x4030512100c548848315,0x2488544841210081448],#[0x1314208c4c4162325121,0x3105c208c4c4c5082313,0x101014208c4c4c125231,0x513101020404c3110504,0x81210104314b8484080,0x113251010201448404c5,0xc113251010204c944040,0x4c11325101304948c4c4,0xc222c4011010204c9440,0x10204c4030403170c100,0x51020144c404c1132510,0x188e8800589451501102,0x41410404161503020425,0x4e184040804030706144,0x2080c084830510120c5c,0x86440302120c94482051,0x1a94215222512100c084,0x4940c084861615251211,0xc084841305031210585,0x212161018582a5860994,0x120c585418100c086030,0x483a5030212104810f0e,0xc2040315081310100c08,0x13120c4c4821913120c4,0x31315100c5c544c40415,0x44030cc115101054404c,0x48544c31915121310045,0x6150c88544831215130c,0x2216120e944828404001,0x483a512110c269688484,0x6884a9442212150c5854,0x1130c54482a512110c2],#[0x3a581131010144c40310,0x44c4041513100e944c44,0x4c405440110171310540,0xe944c4438113a5101004,0x811010944c4031325100,0x118101054100440405a4,0xa481a510100454403040,0x40a65121010100454404,0x3091365121025944c48,0x41944656441101194484,0x60c48465138312119104,0x10544c4830513120c4d9,0x50c0c644c48415031312,0x131512104c9448313121,0x401101510044c4054403,0x430512110c0c4c544840,0x48443a54243121294484,0x10e94484431512110c54,0x43a512129448443a5121,0x4441512110c544844342,0x84436480651111959200,0x9602085046512110d944,0x1110462428082651411,0x40111032950044405a44,0x4401110569100444a544,0x40a51110110060444150,0x440a51110310294444a4,0x4430415110e90544434,0x1944446564801111943,0x10c10544431512110d92,0x64801110544844315121,0x4032513100d905444315],#[0x4c31715011310144c54,0x404c4130200102514544,0x544c315102513100014,0xc3100440544c30715080,0x54404c31525130c64944,0x105c40944c41510130c,0x25110c48944430805121,0x4430403160c944844312,0x808549430512110c4894,0x44c4031715040301251,0xc54944030401101810,0xc5c5494100440617251,0x4171308044c403051113,0x15070403011804405c4c,0x4840113100c100440317,0x44031715131010260854,0x1310544020615100c4c5,0x215130c48544c3191512,0x84c205a31210305c5431,0x4830302161210540c084,0xc4c40303021512100854,0xc4c5440317151310105,0x40405a1100e241131510,0x44020401181010541004,0xc144c48304011510105,0x91310540c4c484151312,0x1325120c48544c303121,0x403021215100c4c54484,0x3031315121010044054,0x14484031285100e14484,0x5120b08544831540160e,0x44820fc5121310584821],#[0x100c28231448415120b1,0x5145c541c100c046c512,0x15120854482180402091,0x515c4401710540c08484,0xc30540170c5c1454404c,0x144c4051315100c54404,0x544c419150513105c54,0x105d8c4c3c510120c204,0x310208c544c408101513,0x15130f14484030810151,0x110105854180c10086a3,0x1610540c044c415040,0x21612101008005840403,0x1101710100c005c4030,0x20240150c0c044c5c404,0x708543020440150c541c,0x81c18306070854302150,0x85912000840722060e8,0x18122060894881831701,0x60d12040830280060c,0x8281412e0e0418883178,0x906082418206220818b,0x24183164480031024182,0xe4e11142418209060858,0x2206100c881840314102,0x1821623120c1c8c20184,0x6101e041832281060c8c,0x2512088e041831881230,0x94480c3030608948c483,0x281410c1204402180608,0x185030c81410c184c22,0x4109081c1822241000c3],#[0x9081a00305800824182,0x34215060c20160030680,0x5101840580060c2a0014,0x81121015042151208585,0x5810622101a044032522,0x2581062e10188a058c42,0x88317062225109488483,0x89448307250806101894,0xc5e141d0442215120c8,0x28106088800543852241,0x61018958c31806098c48,0x85256310944820a09250,0x54285120860261504406,0x51208644821925120d04,0x81820918060c5c188831,0x50a0c5c1828005080d0,0x54403120214602418380,0xc2080717061094084832,0x24060c482c2111008201,0x42c182440b09101820b,0x100e0408422044440206,0x3820807085c182020609,0x722060c4808217220a04,0x4008834106220c201c21,0x61040205c31740010d0,0x10807060c5c002170840,0x21104444020622050c18,0xc401832340170612045c,0x17060c18905c31217085,0x110c3060209101808344,0x20300190421724230c19,0x41808325440602101c18],#[0x11508201c21722060c9,0x4144030522060c00582,0x5120c60401830510060e,0x5431906084c1a943130,0x1225220c204021004589,0x8444020807250c14882,0x210050c2014484040810,0x89438308050706101411,0x82190608644821725084,0x821206105c1831204944,0xe0854482a524860c548,0x5409043120e084808241,0x30117220858544831204,0x18305410800282090c08,0x5800c1c11722250c3058,0x28019150c54241c3181,0x2150a08281450a08543,0x8108461400307160a0c0,0x5838116090c150e04343,0xc16041c31640250d0c00,0x28109a50c6011100170,0x170c890020705060c600,0x58315070809005431100,0x808600021815100c4400,0x45420340150c600020c1,0xc24143038300160c2,0x30c65090c64302438319,0x1005431943000c645430,0xc15061060002150c081,0xc54302150908541c216,0x30402c0085418240a115,0x28c5440014180c600824],#[0xc24329431509420c090,0x30215090c54182140019,0x85c541c32580081e0214,0x44c10782081e08207820,0x4208062507101c942160,0x8581a144c40785081c9,0x550831507085418542,0x944c3150460402181008,0x604544c2190c85421064,0x20301080410a041c5821,0x7061058082080608581c,0x48430721050c1c125080,0x43070c1c8c58381050e0,0x110c30725010c1c04216,0x1c201830001624230c1d,0x716081c940430725010c,0x484141c3021508201820,0xc54218070844141c3430,0x806250c148422521085,0x7086040216250894042,0x716084011004601c218,0x150708148420704641c2,0x101040411310010c041,0x1821604845821710084,0x428010545c1c30225083,0x30119250855082431815,0x24381050e04843160008,0xc05005431643000c5818,0x170818141c31544060,0xc08600030605090d0c1,0x809060c1508183174206,0x9438521000c24141831],#[0x1060544032100160c5d0,0xc82180c0b00218024100,0x44020382401510600020,0x190824143030016085,0xc640020c05090c64242,0x30218000c54302044015,0x5082431715070c543018,0x22800c5605003150c085,0x11621070c20890054440,0xd008a0031524400d1048,0x40150818201c32240150,0xe141052280401028242,0x32315082216003012215,0x20c584c2130608585418,0x44c3210e08844c2450e1,0xf088c8421606220c205,0xc4811621230c2900212,0xd4524401514481161512,0x2208584822486084810,0x20c88542220108548824,0x6005430a230840106082,0xc5431722150e00108041,0x120c360020515120c608,0x54280150822005431915,0x4821215080c542150408,0x71008560900315120854,0x2c20517400c545d0031,0x809005c5431705100d0,0x845431913085c541c306,0x85c888431715070c20,0x8085c4c20e15084c1171,0x1815100c589018544210],#[0x885420115130c64544c3,0x21516120c544c2151008,0x31604605821216085c58,0x5c5831517070c645848,0x17130c605c4034017084,0x19]]
set_option maxRecDepth 16000 in
def g235H7 := limbs80 #[#[0x30800200010842000425,0x18020080410040110423,0x11420000001802d38820,0x804028400100a030020,0x8a010c010140500000,0x180108401000a311000,0x10400088231000010081,0x80010004908061,0x2840100c011000003001,0x18420004003886400404,0x3004400804808402,0x8809100000846108020,0x1480080221048108804,0x104200040a0040c18080,0x300108000080c100800,0x4a0038211080608400,0xe2014471800020040,0x10400000000040018c03,0x8481080c20008218c21,0x423000011086010c40,0x8885184611044850000,0x8a2480a54080208023,0x80e0001250000018041,0x2880010c020800100cc1,0x861180010848128424,0xc01014212940019000,0x3588e708dc100464,0x40447104010020008401,0xc40000c020004018004,0x80b18c2300000004a1,0x102424cc53ac93c,0xd4f02e6e462000000000],#[0x623,0x3043c80,0x80000e037a0000081df8,0xe3215c221950038ec87b,0x482950000000001c0b,0x15b80000000000000000,0x10,0xe6f0,0x1444580000000000000,0x60c093ca0290c2548000,0x10165e91330000082,0x0,0x0,0x661f00000000000000,0x0,0x24e60000000007b22a00,0x7,0xe0000000000000000000,0xe8000000000000001000,0x97a00000000000000182,0x318000006104400dcca,0x882104211d223d000004,0xc00000a02e4ca03090d1,0x180a6141c,0x512d3118000013276000,0x40449882a1041a000000,0x705c2401a0,0x0,0xe20c2000,0x2808d0000000,0x0,0xc000034c698000000000],#[0x9e00000000000000f077,0x17a00002c13400000f00,0x120c700000383c420,0xe0e2c0000711fc0,0x30039000002c48080000,0xb0e06db861e000000841,0xdc9b43b,0x422a0000000000000000,0x380fb000000000000004,0x2089f00208000000000,0x321a6107b600000000,0x3e00000000000000000,0x0,0x60430,0x493e40121106600000,0x0,0x30182305ac00,0x808d9015a00000440940,0x80452,0xa800000000011ad6b06c,0x32e00000000000000e01,0x70,0x0,0x40000000000000000000,0x1d47e3001,0x7900000263780000000,0x8261000000000280bf38,0x18308000000000000006,0x4007f00000e61fbc460,0xfc00000000018436c000,0x281ec000000000000,0xc89cc19807008c000000],#[0x1,0x40e0000,0x3027300000000,0x280810000000,0x407b4000000000000000,0x288388000000000,0x0,0x2a402b0003000000000,0xc0,0x403bc0000000000,0x6c07d400002811a00000,0x700260000000007919,0x92000004a8640000000,0x946bc00000000020,0x280d314237c02e251650,0x5203500000000000000,0xc263c000,0x4120be0bac00,0x415020160b0004000000,0xc0000000000000142fe2,0x1a3cd00000800d,0x683cde21f2000,0x46140000588b1652f800,0xa,0x2105400000000070298,0x20449e4e6800000000,0x3184580000000,0x150178000000,0xe01e484157e42c800000,0x9000000000381c380000,0xa02ae000024039f987,0xb4100000000000000000],#[0x93a2000000000000005a,0xc21e80000000007,0x8000000000000000000,0x1f18396421e760e3ac44,0x18092d41,0xe26500,0xc8390188fa033fc0a30,0x0,0x32301410000000000000,0x310ec22,0x4034807fa11a8804bc0,0x7b9c2a0136,0xc288d524214800000000,0x73dc9075a12380000f03,0x1402a8000010,0xb21e3e0c680000000000,0xa101000000000000000,0x240a40000,0x3b40000020279c0b6800,0x3820000000000000050,0x743c00000000003,0x404f0000060c800000,0xd316461088000,0x0,0x84614032300000000000,0xc0000000000000000000,0x5093b8000000001a232,0x3889800001c11,0x5a1ec810ea00,0x1520f800004045e0,0x0,0x709020000],#[0x2c1c7c83e9000,0x8487f018300,0xa08cbe4f9800000,0x0,0x982880000000000000,0x801a80000000,0x0,0x583690000008d5c00000,0x2010200000000000000,0x42c82575075c20e64000,0x70094851df406c104,0x41180000000001080140,0x940951180800000e096a,0x2649d80000a07f5e07a,0x0,0x3422800,0xa2608000000000000000,0xa0000048c48000000001,0x5077,0x465a4940000000000000,0xc4,0x206f60000000002b04d0,0x0,0xa100000c034800000000,0xc599011,0x842a00000a2480000000,0xf049a0000101d2f,0xf080e40000000000c05a,0x7,0x622092077340d6800,0x801f00000302c4000000,0x7023f44426],#[0x2c000000000000004475,0xf079d447,0x8cc000000000105a800,0xa0a4681bd2204800001c,0x1e025800000000000001,0x0,0xa01ac000000000000,0x0,0x440cb000840000000000,0x912238a105a0193f8438,0x36e04ee000010154812c,0xbe00001327e0000008b,0xf0216e2448000011,0xe42ce00003888e8,0x76001af133c000000000,0x919b0000100e90c4c,0x5025fe80fc00,0x3b26d76232000000,0x88fabc9dd00000a0764,0x988847f835900001487c,0x1807,0x10080000000000000000,0xc03e8000000000805eae,0x98635e81b20000000000,0x381e0c00983217,0x140c1c0000392ae000,0x319e90000000,0x180b6e0f1d0074000000,0x55034600000000000000,0xf46031580a6a40b5d807,0x3f6105b1eacec0000381,0x890800001c0d45c865f0],#[0x100e6800002,0x6000000000000cfb5064,0xea800000000000000c8e,0x44b000000000088d4a01,0x804750,0x836800000ce5fc,0x1c07b000009058c0000,0x0,0x380a5000000000000,0x0,0xe0000180970000000000,0x38358521b,0x182394000041070000,0x46940000289216808b00,0x28dd600000d,0x9b013a00002d10310130,0x37000000000000001041,0x4a7881628038282,0x80c0000000000821d80,0x80fb000007,0x681f600000000024187,0x5b221eff010920a98000,0x166b10e3000000000281,0x409b8000000000000038,0x1c01e410e52062e00001,0x2400004a116000000000,0x18448000000000060d,0x2002c80000a51ec00,0xa0aefc93100000000000,0x608f3c4653024f80060,0x1a000008016800000000,0x6],#[0x43c60035800001020600,0xe0a180000000003,0x1b7918a4,0x1000000000000000000,0x1e07cc0000684,0x16017c000000,0x283b6000000000000000,0x203e0403294009b821d,0x0,0x0,0x88700000000000000000,0x40000000007230200003,0x16c00001005e,0x0,0x0,0x8852d0135f8196000000,0x6242d800000000000001,0x9063,0x0,0x0,0x1267d00000703710,0x0,0xa06846009149528000,0xe124c000000000000,0x0,0x78106000000000000000,0xd2248000000000,0x3200000001c200000000,0x3018600000d0,0x0,0x188c10000000000,0x2c93f00000000000000],#[0x40ebe028500000000,0xc0dc0000302518150400,0x8262c000000000000012,0x1,0x1e035c0000000000000,0xc998000029345000,0x180d20016d8000000,0x60182000012008000000,0x494060e438800001814d,0xbc0000008c15847c29b6,0xe033a000018829200,0x420f80,0x0,0xe4925d83110606200000,0xb0e02878268e48ce3c1c,0x8500000c048d8227081,0x30,0x589603013f28300,0x3c19b80000a08420000,0x141bf40a1600000000,0xc72fa00,0x0,0x10480,0x9ba0b835198800000000,0x401a5843d818a1701,0x1d38057800000000000,0x1c41a00000521592,0xa00ad2a5e5414e80000,0x1087ce0fdc00000000,0x508100000240af800,0x0,0x81a00001c1968],#[0x9c9a,0x4c827f0000000000000,0xf080000703560000380,0x1523000000000000002d,0x1401c203d60000000003,0x4304798bb65000000000,0x20d,0x8263800,0x6029b40a000000000000,0x32082800000000020050,0x1809f9447ee01d4f026,0x18005cc4cb32a82000,0xc8da781c700,0xd3147046a400001099d0,0x400001a0a3c00001027d,0x7600000cc9d80000508c,0x25200000000000000680,0x80c90000000001c073f8,0xd02f6e877f49e78,0x7815d6242c000000000,0x0,0x6015b0000068ca800,0x183a6034600000000000,0x0,0x2a2d0000000000,0x70b3580830000,0x8466800000000000,0x40844000000000000000,0x260975c1d98000000001,0x1090980000862d,0x20ee0000000000000,0x0],#[0x32e0,0xf20ae00003e1ad00170,0xf04e8e811800000000,0x10461c0000000,0x1990000000000000000,0x80000a21fea032c00004,0x15405,0x26a82b90000000000000,0x280,0x1fe5889300000000000,0x119a5811b9039200002,0x182814006a0000,0x11400000000000000000,0xa8c0000000000000081,0x6ec3d18353013400000e,0x1e2428c86b0822a00000,0x483400001397e0000,0x0,0xe5ec87e8000000,0x8060280e6c00002029f0,0x7034200000000000000,0x906960000000000000,0xc450000,0x83cfe075200000000000,0x111080000000005,0xb800000000000001c81e,0xe001400001802,0x9580000f249be832400,0x6804a00000000024,0x62255a2038,0x6820fa65800000,0xd3d08740000000000000],#[0x2e4000060431d00a120,0xe814c0000000005131a8,0x4000000000302d100001,0xd80000245fa800009044,0xf04,0x0,0xa2de800004831e0,0x5c02b3c2034000000000,0x6888400000c94,0x6310c000000000000,0xc947a0889a0197495300,0x8000050866ea3ee843ff,0x1581ee624d6c0749c0dd,0x4a102e9703fd424e4019,0x1a0678c8,0x2125c80654806700,0x3809e00000522bc205d8,0x1e10f,0x6834300000000,0x20a0845000000000000,0x60b889195a00a3000018,0x7e025c00003841d546b7,0x5760e18000000000990b,0x16006ce12400000607,0x7760000000006198100,0xe063c000000000f,0xa000000000384547a06b,0x180000100bec00003934,0x1b27f800000a4,0x0,0xd90bb00001603c341170,0x7000007051cc0f14c185],#[0x100fdd079800000012,0x84480000f01ea0000000,0x4,0x80000683d1001e8c23c4,0x1049e,0x3d19b0000000000000,0x8002800000000000,0x0,0xfe0c1400005111b00000,0x104412906ea03e,0xc16e80000000,0x1165090670212f82ab00,0x819c800008,0xb3227e000000000088e6,0x508240000000001007,0x14100000000000000000,0x83b5d209a00000000008,0x20d335023f,0x7308a272264000000000,0xa1800000000000003c13,0xcd80000089290e0ca560,0x8c55902f3c343b807619,0x3,0x0,0x84000000000000000000,0x141100000000000ec,0x3855000000106e60,0x128ccc00000000000000,0x4908000000000,0x2a400000000000000000,0x32,0xb21a12cb280000000000],#[0x10229bc09258436,0x5f011320000000000000,0x403,0xc1f100,0xf120c0000249390,0xa066c000000000,0x82f1b060c00000000,0x7580000000000000000,0x603c0010d2c,0x2c12180000c035000000,0x0,0x0,0xd50000000000e215600,0x8c9348203000006350cc,0x3b09480000090ce90435,0x5b24200021f80000b54a,0x4014800005842cb21,0x0,0x0,0x402a5,0xa07640000000000000,0x39c00000000000000000,0x3a8a04b30886040c36a,0x1840b000000000050514,0xc20b34c01764e6e00000,0x5680000523290091c483,0x13e00000e06490433244,0x80901a1e800001a04638,0xc0000000005076200003,0x1bc05ab0961040aea47d,0xb78800fd98dc00000246,0xa0],#[0xc10e4000000000c20180,0x7041d,0x0,0x0,0x64f24ce5088318000000,0x160b640000421e42,0x4000018099d894300000,0x940c00000000003815,0x0,0x82b200001888ff814a00,0x7,0x8aa000000,0x0,0xedd0385000000000000,0x3c,0x4000000000f137f641d4,0x482da724da0011,0x0,0x4980000052044b058400,0xa4461447400000520130,0xe60f9c00000a14c1034e,0xc4c7a080ac02722011,0x58000,0x209c0000000000000000,0x8c1a000c6800007,0x6224680624c1e980000,0xc75b2643c800000000,0xc500000000,0x60660000000,0x0,0x0,0x8b3fb40bcc87b4000],#[0x1598135b059dc0a8800,0x3d800001c05120,0x800002836a0000000000,0x16254,0x0,0x4979820da02380000000,0xc80180000183f3000006,0x800000000000000a0322,0x3340388000000000a655,0xf01,0x7122500,0x20145800000,0x1c0328000000000,0x0,0x0,0x3476084e00003448380,0xd22fc0000000006,0x0,0x14518850000000000000,0x702038039b8011042,0xe0e4c0,0x302081808a0000000000,0x10102800000000180fa,0xbe80000293d000000000,0x70175e0,0x3f0519780000000000,0x40c30820b8215a91324,0x166aa9c17e290b80000,0x56600000000000000000,0x6c620bb7cc4c0000040,0x2,0x0],#[0x0,0x2c0c6000,0x205c0000000003021680,0x5,0xfa2325123e9205c6c126,0xa054200000102,0x90f80000d23060000000,0xb081e000015,0x3a040003ad622f0,0x41231000000000,0x96400000000000000000,0x224200000004,0x0,0x276cc,0x520000281a95a0070000,0x18000780da00000902,0x42a2000011cd78000000,0xb07c240170000000000b,0x2061f261bb8130682be,0xd0396ae4dd80ab0000,0x21d00000000000000000,0xb93af64404000070,0xb01ca402f5c0d7100598,0xe0000000001e02b4045f,0xb043de00bf08d,0x21180000b01520000000,0x3c,0x2005bd02cc00000c0168,0x96406f6107a000000000,0x140ba00000a03d6a04,0x44d298aa801f10000000,0x24a9c0000290bd00000e],#[0x4e0ee8000000000c07f3,0x202029000000c0e3d02d,0x28392810,0x32446808c408000000,0xf,0x3038400000000000000,0x70000000000000000000,0x11500000000000000723,0xa010c00000000010,0x2042ca41f000000,0x60080e014e40ac00000,0xb0a01e3a07a9204f8000,0x1a025640,0x782179312a000000,0x80000318960000000000,0x580000198d51043968d6,0x2c400000000000000a0c,0x4b280000682ba00001e4,0x904ede,0xdc0be1c018b906a00000,0x168812400002988a5055,0x606c08a00000703,0x21020037000000000000,0x14052681a280000d,0x1c1f680000,0x0,0x1193222000003003a000,0x8832125c00000000069,0x98dd0037000001c87ae,0x18000000000ca6500000,0x13,0x0],#[0x43700000000000,0x0,0x0,0x854000028be35015c000,0xa0,0x60e0e8c3d80000000000,0xe0000101680000047369,0x6b0000000000101e,0x70187000,0x3583ac910d00,0x0,0x78279,0x9a000000000200a88000,0xa10f000000000020a,0x905e800000000000,0x80000000000000000000,0x10057,0x0,0x0,0x91aa02071e0cec0,0x582b104008e8dc8,0x38088f1097000000443,0x600ee000,0x9280000180f30000000,0x16,0x200f400000000070538,0x8ee223dc93c00000a021,0x1ce70c00006829b100,0x1e0d0000000000000,0x9214c000000000000000,0x0,0x428a0000000000000],#[0x0,0xa929200000000000,0xe836cd01b4e21b800000,0x38000040794e0f9b0084,0x18012550f,0x8980000393b3c099800,0x1409574,0x18184f023d0000000000,0x0,0x79179b47ac000,0x9e80000611a50000000,0x441d000000241b604a16,0xa00000019d0000000001,0x1a0abc000000000902f,0x180464808180000000,0x23de4f4400000926100,0xb367b62218242d301ccc,0x180108000000000,0x7928dd03a6c0330000,0x210f2800,0x0,0x1c85ac00000,0xd049d624638000000000,0x408fb0000080ddc008,0x10426000000000000,0x10062f0488000000,0x9059200000,0x2419af1223000000000,0x80856000,0x0,0x1519b80000000000,0x80000000000000000000],#[0x3085a00000d07c,0x4d400000000000000000,0x63ac0b28086c8000060,0x104c990302f,0x0,0xf392820000000000000,0x780,0x9001a00000000000,0x300480000000003015e0,0x78000000000000000000,0x721420000181d,0x383e3b067e0000000,0x80542843200000000000,0xc0870000000001e0c48,0xf02a40000,0xd074164701c4f21ce000,0xf310fc0,0xe08a398a2c81c5000000,0x8019e8842f0063c02a6,0x10c4e290540000,0x26c00000000000000000,0x82,0x70728000000000308fe0,0x1e0bdf64e900000,0x14074409258000,0x401f2000000000000,0x82e70000000000000000,0xd313580e2154cae,0x6015000000000000000,0x2aa400bda0ae0000,0x601420000000,0x8172e80ec000014625c0],#[0xb80a180000042a0c06d9,0x28919d0313000000493,0x56102070000000000000,0xa0,0x41ed802a28010000000,0x0,0x0,0x1dd408e4000019255000,0x29fc23c0000000000a0,0x40d4f82cf2,0x1080a0000240197a353,0xc620000000000,0xb008600003cc49000,0x120610000000,0x3485200001a02c000000,0x680b100000a09a401af,0x3a21135303c8804e8000,0x701bf306504414410,0xa0582866fc0,0x3419a000000000000000,0x0,0x1f80000000008609c000,0x2029ea408504,0xa10000000392aa000000,0x10487640ef8000000001,0x0,0x58e00003487f00000000,0x1a8dd400007a376d0,0xd09c881a50,0x280e9f03a1,0x4d000000000000000000,0xb0044000000000703],#[0x1e024c000000,0x0,0x102f880000,0x10b893255640288000,0x100e21e2000000000000,0xc033a4,0x0,0x0,0x100378000000000000,0x1005800,0xc36640,0x0,0x188c60000,0x1ee0000141be62043000,0x30f4e21b680fd0000045,0x10400000e,0x601d0,0x6018e0000000000000,0x0,0x820b0000000000000000,0x464336111d81935,0x5813b453300000288c5,0x12f01640000026294000,0xc03e5e0bb9cd,0x3001d3024e000000,0x0,0x78000000000000000000,0x240000021894b20fb64e,0x24461f80c8c441aa4,0x408900,0x20000000000000000000,0xf62c],#[0x602c5000,0x60dc800e33801200,0x8137820450,0x180000301ff,0x2c1ce8000,0x180230c0c2800,0x0,0xf422b32722c19e8,0x6211b60dc00000,0x5c800000000180de4000,0x601400000048,0x41908000070586000000,0x6089a0000000001,0x56000580000000000000,0xc017001fd6121ac06,0x82800,0x1131d000000,0xc0000000000000000000,0xc44078258924e,0x53200000000000000000,0x3bd4056aa4e9b898ce0,0x391f35,0x162fd0000000000,0x330e20000000000000,0x0,0x0,0x0,0x0,0x3958623800000000,0x306620000000,0x409f8000034637049a80,0xc0000702f90000000003],#[0x50720006d,0x9c000000000000000000,0x83033019f60,0x78200000000,0x2e4f800000000000000,0x2048c000000000,0x0,0x1645f5c0680000000,0x5000f40e04d19a8a0270,0x63648c4980000,0x1c1c88000,0x3aa00000000000000000,0x3547ae0,0x231a800312c1b38,0x943d2000000000,0xfe800000000000000000,0x68142000014498c24,0xe0412000000,0x0,0x400000000004055a0000,0x2009da06,0x34063002c40000000,0x0,0x1aa3ac00000000000000,0x5127b0000,0xe906800000205d000,0x0,0x1400ec0000000000,0x2000000000000007a04d,0x804f60000000005026,0x40239c4219044a800,0x0],#[0x0,0x0,0x0,0xc4c983d2000000000000,0x1206f641e60,0x5209e00000,0xc04360000,0x6c62610d821f157f7201,0x6f80000000000000160,0x710f8000004,0x29aa70045a,0xde000000000211c20000,0x7a424754017f00000805,0x458000028075210f092,0x2407c000009,0x3134a000000000218a8,0x9c000000000000000000,0xbb6c05c6000004182200,0xe77680000100800b,0x80000000000000000000,0x140f2,0x13c88c723340c0d88000,0x1035e0000281,0x862440,0x403c3e9271a00cc,0x3410600000d269e0000,0x1c1494127d300ba000,0x3c10c800000000000,0x804358437d03a71118a0,0x52079cc14b8000000000,0x6a000000000202029071,0x14008cc47d3835b872],#[0x75a0000280ee0000000,0xa0408e22af8900003de8,0x400000401b4000032034,0x7834,0x93a596f3c80ded091800,0x380962c,0x6a041000000000000000,0x2c05900000000000000,0xe380000c12a800000000,0xc41000000000000003a4,0x2c,0x6491200000d00fa00000,0x68c0de0090c462492668,0x1407,0x0,0x4000c000000000000000,0x1,0x0,0x140b99083380000000,0x3018000,0x34008e82210,0xc0000000000000000000,0xdd203aa807a2c47fc81f,0x8a600000000000000300,0x301f771,0x1010e0000290130,0x59b8500000000000000,0x0,0x12859800,0x5022b00000000000,0x86d8c,0x149e700000802ea0000],#[0x803e0000,0x85b60146903f80000000,0xe0851c5425a1eb000002,0x148282403f5126501176,0x4482682ec0000,0x26600000000000000000,0x464600000c0288000067,0x6041a2,0x3355200000000000000,0x12e4cb4068bc34,0x37600000000000000000,0x20e8c000028,0x0,0x482dc72124000000000,0x0,0x5a3323153880bc800,0x44980,0x3406d800000000000000,0xb8000000000000000000,0x64f011880000900f5a80,0x682acc05a760,0xa209fc89280000040260,0x2c40400000608bd00000,0x340c,0x760604d8000000000000,0x1410d4000000000e0,0xb235b807380000000000,0x21bb9,0x8024000000000,0x7100000000000000000,0x103a751e800001408860,0x483a7aa3b800004],#[0x4824100000000000000,0x54800000000080848000,0x41902840000000000c9,0x30,0x803200000f06bbc0414,0x97811300000000000000,0x2c1e30000000001809,0xff40000000000000000,0xc0d9acd1200000401aac,0x1823dd4029800000085d,0x24192800000000,0x2c600000000000000000,0x16041d55420032b90,0x70270c0af540a3449f90,0xae42d44037e55e900000,0x12110c80a800001830,0x88d05fe00003c0ae000,0x3654036a00000000020,0x6636ac20f5,0x1a0de00000,0x5085e00000000,0x20887000000000000,0x7017f840ec0,0xf496400000000018070c,0x1000003b0bb0000048c9,0x1c01c80000155e5a47,0x0,0x59ec09e80000921080,0xa0000000000000000000,0x100ccc000000000b046,0x1c06c80000000,0x5812600],#[0xc02aa00000c025800000,0x20485a084fc84ed8420,0x72300a05b981beb090,0x1a050860000000000000,0x3c84212780aa0000010,0x489,0xd0000000000000000000,0x3843,0x1a24801800001e461000,0x81a71088900000c21cf1,0xc144000000000000002,0xd551ba00000c21b80000,0xdab901c80000220a6007,0x1b0000008300353742e,0x402d840613c24920135e,0x9c422e91a16021800001,0xdde097d485a820acf04b,0x2c099f8147f06,0x503a000,0x60475642300000000000,0x4831c4ee6d7012288440,0x9003900d58c1e58822,0x24140000,0x0,0x581ad000000000000000,0xd00000c0264000004059,0xfcc9db0000000000001,0x806ce95,0x10b4e03745073e000000,0x407888b43d071800003,0x1403c403f1b77620000,0x488c11294194b2122000],#[0x87e0000000,0x20edf0026583f54014a0,0xb6636c00000908363136,0xc40000081e4a843d307b,0x2cc48703fba03,0x1a0f0800000000000,0x301d1000000,0x301d61a20b,0xa4a40c46413000000000,0x18891401,0x0,0x0,0xc119c0000381f8,0x5200000304e200000000,0x19600000000000000201,0x80d5000000000000002c,0x7885bc80040000026386,0x81b59899000001a018,0x5b20d00000000,0x24938000000000000,0x84a380000210e6000000,0x95150000000001,0x42000014060508e40000,0x4da21030000000000911,0x7a0c270,0x4035d8023b1cd4a00000,0x7012066886d50d380000,0x6c500e40000318280811,0x3818ad21,0x0,0xc957f05800000348ed0,0x22189e107e4908a40000],#[0xa073c01c,0x290e4000000000000,0x81418000000000000000,0x24201a81390000000002,0x0,0x0,0x51400,0x354bd80000404f00,0xc0fd00000000007114e,0x2c8238803f0000,0x390b28a056000,0x3ba00002cc4e8206300,0x1e07bd8451d80e02,0xe0808000000000083a6,0x0,0x3c015000,0x4070000000000000000,0x610b2000000000000005,0x0,0xaa800007032400000000,0x16b80000506a600001c4,0x907ca481b38,0x146210,0xfd01ee00000e063e0000,0x94c0000101ba000010e4,0xb51d864,0x1d408000e6302d00,0x6620c000031bab00000,0x6a39c0000000000000,0x48991000,0x46090007800000000000,0x1e0a4c00005a3790],#[0x7447200000000000000,0x0,0x340a0780000000000000,0x288ad52,0x1000c6022c0000000000,0x5a02b500000a0fbc0000,0xd1101e90000060dd401f,0xfc80000000004031480,0x103a8000000001888f1c,0x7029c00001,0x60000000000194506070,0x1042,0x88d40000000000000000,0x1c,0x40428000000000,0x120bd80000000000000,0x0,0x0,0x104c8a226d413a800000,0x0,0x7f000000000000000000,0x9c00000000000000083,0x49,0x6130ac0bc000000,0x0,0x14c02490000000000000,0x1e095a00,0xb06aa000000,0x8933000000000000000,0xb5547900000000000000,0x5e00000403d0e222f203,0x5980000103805006c60],#[0x244af00000800b62,0x1109500000,0x0,0x0,0x826635800000000000,0xe2022602aad08c800001,0x1e0bf4000000000,0xe500000c8de000005031,0x248d6640a0ce1c1ebf00,0x83ff61199e8154000038,0x200ccf03820000000004,0x105be000010205,0x7203d0000000000000,0xa8a400,0x0,0x3c221800008054f20a58,0x1a109,0xe07b4000,0x580000000000000000,0x222f800007b9bd000006,0x80000000007816f00000,0x1015f80000c083,0x0,0x0,0x416a800000,0x2107f,0x0,0x33c00000000000000000,0x23f0000000000000040,0x3400001f051400005,0xd20e60000118b5,0x281230000000000000],#[0x8028a0000000,0xb26b3209500,0x1a04a0,0x1012dd10af000000000,0x0,0x0,0x3814b000000,0xc0000000005034a00000,0x1e00000000000000e00d,0x38894e02,0x14002000006010100,0x1c0a240000000000,0x20160000000004909e,0x2002,0x30c6c000,0xc0c64000000,0x831120000184858,0x2c169,0x9e8017740813a2028000,0x1ab9220a893a1e066be4,0x283894121c000004,0x80000481a63464000000,0x3502a439ab000011272,0x3c223000004578c000,0x36000004111ee02d200,0x3c17200000e0664a,0x68000000038b3aa2562,0x34405fc0000000000000,0x31ce8c76e4d4d01b2421,0x1c1c68819bb0,0x103f6000000000704420,0x1804b4000000000],#[0x23913320000000000000,0x502,0x2818880,0x190b0000000000000000,0xa07fc000000000,0x207b200000000,0x16a80000f07be0000000,0xc05f00000000002234a1,0x2411d800000000000000,0x5c197000000000,0x0,0x5476800001376800,0x844f981de00000000000,0x1d251000000000000001,0x4a662340000000000000,0x400,0x65f00ba81ca00000000,0x560a20000140b2f00275,0x780ab]]
set_option maxRecDepth 16000 in
def g235D8 := limbs80 #[#[0xd58420b798e10b758e10,0x98c20b758c20bd98420b,0x84509f994209f59420b7,0x850bb58850bd98450bd5,0x10bf58810ded4250bb98,0xfe08110bf59410bf590,0xfe8c110fe4c110fec811,0xe54110fe90110fe50110,0xd8910bf58910fe94110f,0x9510bfd9110bf59110bf,0x210fec8210bfd9510bf5,0x10bf58610fe54210fe50,0xbf59210bf58e10bf58a,0xbf58c20bf58420bf5961,0xe94120fe54120bf59420,0x59520bfd8d20bfd8520f,0x8620fe54220bfd9520bf,0x220bf58e20bf58a20bf5,0x50bf58450bf59620bf59,0xdf54950bfd8550bf588,0xbf58650bfd8950dfd495,0xf58750bf59650bf58a50,0xd4810ff54810bf58b50b,0x8110ffd5010ff55010ff,0x110ff4c110ffc8110ff4,0x10ffd4110ff54110ffcc,0xff8c910ff4c910ff0c9,0xff14910ff90910ff5091,0xfd4910ff94910ff54910,0x55110ff98910ff58910f,0x9510ff59510ffd5110ff,0x610ff54610ff4c610ff9],#[0x10ffd4a10ff54a10ffd4,0xff55210ffd4e10ff54e,0xffd4420ff54420ffd521,0xf54120ffd4c20ff54c20,0x8c520ff4c520ffd4120f,0x4520ff54520ff14520ff,0x520ff58520ffd4520ff9,0x20ffd4d20ff54d20ff98,0xff54620ff99520ff595,0xffd4a20ff54a20ffd462,0xf55220ffd4e20ff54e20,0x94550ff54550ffd5220f,0x8550ff58550ff18550ff,0x950ff54950ffd8550ff9,0x50ff58950ff18950ff94,0x2c044000ffd8950ff989,0x1e07a834c16208f03681,0x8343d61c20cc85c02801,0x2e015f0a544e62581140,0x8f0473036f1a68c90612,0xc486235914085c4051f1,0x1159ca7c51c280936096,0xb863a30c17d8b9a5a42c,0x979c50de46d035019f8c,0x207e73db9e54ef47513,0x47c233d13e87d43120c9,0x13dc9c54d525e92b0921,0xb5722ad1516a54519284,0xed824bcd5d22ded696b1,0x5469933ed96cc9463930,0x9b5c96e146f5b6b5b08d,0xf8d7b5bcede24ed47523],#[0x42b611705b8193fedf96,0x31db8dcc64229712986b,0x94bd2597294935c92643,0x23430a03cf2673335b99,0xf15676adb536a86d33e9,0x24404b54d9e6ca1619a,0x801222213240c0111498,0x848100222010400a080,0x4888a481002220006089,0x5284062648290101000a,0x888a4c0120a405260400,0x202130014910141000a4,0x995024060a5098614981,0xa0401222201244432800,0x85440481210094224880,0x4a485444090688094264,0x812222a24a4090815100,0x84c90815101204852614,0x3049490a14a13242052,0x24190104c30609292102,0x812109852a0091018493,0xa4880614041264051014,0x93005491014289264840,0x4450a3001110292221,0x99010280269480a54902,0xa44813102a1264040c94,0x60294990100a5264040,0x102c2204842614015244,0x49324205244030a18990,0x8402920c9802a4880a14,0x80060829524313241480,0x18a930a4040400293202],#[0x809148120c0010a4ca90,0x42932a00292203068a4c,0xe04b930a4050608b052,0x9c14a4042e1412527048,0xa94a130cc850894a1318,0x48a94812122a5444090,0x4a4878a94812122a5244,0x684884a5242958488009,0xa2c4224074b14412464c,0x243258a1880826325481,0x58a95112202948a94813,0x11414a18812209252640,0x4a3864a4c41014117889,0x44a2081211244441a090,0x21c2468929224ba52048,0x102434709125243990a1,0x5305d1a24a4864689292,0x52a31014911152921440,0x26407868c42524296860,0x80f049a5202170a092c1,0x1c14a40631101a44b04,0x14c85090d1a526488889,0x60a0529222343464d292,0x1a44b00890052922221,0x263c4480e025223180b1,0x1424129314ac14201290,0x5292202454b112112034,0x80950872c9904a4888b1,0x74a4888804b44490d1c2,0x5488e243430a0074a48,0x204164a4880894413244,0x1429480c6220382910a5],#[0x49a5202a14a4c8091124,0x2429686051a5844872c8,0x2829508526408868e125,0x10a520441424d29014b8,0x11241429480c62203829,0x5242990a121a34a4c911,0xc2445a0210014d868c9a,0x1c2001491004ac4490d1,0x840546880122a415468a,0x14222921d1a22b1490a2,0x292151a20048a8c551a2,0x48131c1158284b802640,0x84280205498e550c1001,0x88a4098c84a938a40510,0x840130a40a8c5508]]
set_option maxRecDepth 16000 in
def g235H8 := limbs80 #[#[0x11000040202621001040,0x124001400100000,0x831000048040000001,0x208010001240008208,0x9010081a102008401482,0x628000059000c0000808,0x254004024040a031400,0x12410000800044020480,0xd2cc60820502020424,0x20086c6000601001048,0x82200404014010080006,0x1412006400190690004c,0x904c024880500100b00a,0x2a004e0a0,0x0,0x813f8000000000000000,0x2c4000000001,0x0,0x2010200000,0x0,0x200002a4500000000000,0x493d38067f801,0xe07000,0x88719fc0000,0x187370000000,0x0,0x0,0x0,0x7f80000000000000000,0x1c055d85ca0000584570,0x32ac18d0000000000000,0x602f000002c],#[0x1c06f,0x0,0x2ce06b00000000000000,0x86,0x1a4ce00000000000000,0x0,0x18830004b20,0x0,0x21b0000000,0x1016ca80340000,0x0,0x7200002bba5241a00000,0x25100063e0000782,0x605a80001812b8,0x783040000301f0000,0x0,0xdacc06e3888c00000000,0x23b40000000000000030,0x0,0x161568000000,0x6a0ce,0xe92b0000002ff000,0x30853215d0000000000,0x180860252e000,0x1a527800000000000000,0x40150240a8000,0x80000000000000000000,0xa414,0x1859400000000000,0x58286,0x938c0000000000000000,0x62b05e1756],#[0x16bc138344c080000000,0x6000012d9800007143c0,0xaee0000000000000481e,0x10,0x28b26058e0000,0x0,0x142d500000,0x0,0x0,0x25e0451e4239005c000,0xc,0x180d10837000000000,0x0,0x785e6000072cc00000,0x40038000000000000000,0x1,0xf00000000000123800,0x2801400000000000001,0x4a90ae02900000000,0x40000000000000000000,0x1e4ed8000061198a2c,0x80000000000000000000,0x604062e0000000002e28,0x121,0x1842c000000000,0x18d0e000,0xa0000006178000000000,0x618,0x0,0x841a8000000000000,0x0,0x1ab1e],#[0x1809000,0xca000040064000000000,0xb4c0000000000000703,0x30000000000000065318,0x124b,0x0,0x1c4ba0000000000000,0xc15500000000000,0xda800000000000000000,0xa502000000000000006e,0x80000000000000000000,0x4bb200002062120f4601,0x50dcfeced72567c8641,0x27a000000000000,0x0,0x550000000000a2c70000,0x72dc86825e8,0x39705d02112a088bcb06,0xc03700000085fa227660,0x180f000000000010327,0x0,0x40000000004941d00800,0xbd0c8ba0000782d644f,0xc216664e0e0000000018,0x100e,0x3022a0000013e2000000,0x39192c80000000000000,0x165,0x807cf8596,0x590400000000,0x248c00000000000000,0x7539afa000060a1a000],#[0x38dcb4,0x1e1800000000000000,0x0,0xb7080bc0000000000000,0x1861b00,0x0,0x9af6000000000001f000,0x2931fa5138000000005,0x505cc000000000000,0xa0000000000000000000,0xb9f,0xf1042000000000c16400,0x12053e03a16083,0x0,0x104e00000004a8,0x8011800,0xe5280,0x611f4000000000000,0xca000050ba80,0x421a745370000,0x1402f80,0x1e350000000000,0x1b8a000000000000,0x144f610522000000000,0x18022800000000000,0x622bbe01cc843000000,0x16f1a80000000,0x80000000000000000000,0xf80000000000000394e,0x38,0x0,0x519fba0fa0000000],#[0x10179352000000000,0x0,0x0,0x0,0x0,0x22e0000682838137d810,0x42,0x27c093f800000000,0x0,0x0,0x0,0x0,0x868684ea000,0x1e02a800000,0x7901740d68000,0x0,0xdf000000000000000000,0x100,0x28d3c,0x0,0x9ad7660f8000101870,0x348b088af80000000,0x29d160000000000,0x44b58000000000000,0x493fa000000,0x0,0x0,0x0,0x0,0x18000000000000000000,0x618c80001403,0x122860000000003bb660],#[0x0,0x60ef80000000000,0x8a800000000000000000,0x28620000000001a1e1c1,0x603f0,0x0,0x593aeaa388000000000,0x0,0x10864800000000000000,0x161200000000000000,0x1a32f80000000000,0x405c20000,0x80cdc019600,0x3aa10580000000000000,0x112a0000000014f45906,0xe800006e671864a20254,0xc50,0x1a2d9000000,0xa4800000000000000000,0x5959a28e4f009ba411b2,0x17394d40000419200000,0x61283801aa7,0x225a6,0x12dda4b2800000000000,0x1e1588000000005,0x87780000000000000000,0x6adc00000000000001a,0x100140000,0x0,0x1a800000000000000000,0x311eb20,0x0],#[0x2106c059380d8800,0x69828,0x381b4000,0xea390000022d4800000,0x0,0x18415c03c2000000,0x0,0x0,0x0,0x1c480000000000000000,0xb00000c17d00000aa3b1,0x28656f5,0x0,0x10400000000000000000,0x6003a82f412,0x0,0x0,0x0,0x80ab800000000000,0x120e28000000000,0x0,0x80000000000000000000,0xa,0x80000000000000000000,0x21d6a854c,0x20ea0000000000000000,0x5200000000000004836c,0x281,0x70000000004b54200000,0xc151f88ab441,0xe0a8000000140800000,0x141360000000000000],#[0x502c2000000000000000,0x0,0x0,0x0,0x1c02d000,0x20da8000000000,0x0,0x0,0x3428144e057d73458000,0x80000000000000000031,0x385ea0000521ad2ec8,0x2017a00,0x54000000000000000000,0x244009d,0x1000018189784ab804c0,0x78dc8e09,0x0,0x4bc0000000000000,0x8f300,0x501060000000000000,0x0,0x313f8000000000,0x0,0x47600006136200000,0x0,0x362d5800000000000000,0xb4,0xa85ec000000000000000,0x1c416310ee2078,0xa0448000000000000000,0x1a70730482,0x140aca88e20000000],#[0x40000000000000000000,0xa56,0x0,0x0,0x182b500000000000,0x0,0x0,0x383a6000030040,0x1a03a000,0x30eb8000166108,0x40232000,0x14131800000000000000,0x1d200000000000000000,0x6038a93c2000018,0x34b27814a000000000,0x4ee00,0x0,0x0,0x5a22c000030d3e00000,0x0,0x7930c0000303180,0x0,0x6020c000000000000000,0x1c0f5800000000,0x5032a00000000000,0x0,0x839c0000000000000000,0x7,0x0,0x392f40,0xe2200000000000000000,0x1a41bd05e14345a8],#[0x1fb80f5000008000,0x624cc00000000000,0x9d60c380000000000000,0xc,0x188af0000000000,0x29e000000000000,0x60000000000000000000,0xe8409086,0xb829ae18180000000000,0x78b04af22,0x2804527440000000,0x7dc0451a27a000000000,0x301,0x0,0x0,0x1837100001047c800000,0x120908000000000000,0x10abf80,0x3a4c60000000000000,0x8077603ee41858000000,0x8000000000000000000,0x3b7e4d25056760e0200,0x141565,0x20f91819c000,0x5a03c800000000000000,0x1256,0x0,0x7b80000000000000cd68,0x1c1,0x0,0x0,0xe8000000001025000000],#[0x5a1d1c15a8000020c,0x1c03178ada0,0xe0210000,0x0,0x7c8be0000000012022,0xc15fb83ba00,0x2932360bf00000,0x222647b8000066be000,0xe800000000490f460aa7,0xa34,0x1611c800000000000000,0x40200000000000000000,0x1e15c8185c000011,0x2060da8e5d84be0000,0x1c1817005400,0x504100000504ba,0x23c60000000000000000,0x19a00004,0x70518000000000000,0x0,0x1884,0x0,0x0,0x8654000000000305a400,0x3a000000000000000001,0x5a39a000051c,0x0,0x40448000,0xc0000000000000000000,0x1252,0x0,0x701e40000],#[0x0,0x5c000000000604700000,0x2556000000000523,0x0,0x0,0x682140,0x0,0x0,0x0,0x0,0xfc00000000000a900000,0x84,0x0,0x0,0x0,0xd2ca8000000000000,0x0,0x5140e0000084f00000,0x0,0x0,0x0,0x0,0x0,0x506480,0x1ca398000120fb0000,0x0,0x585100000,0x1668f5858600,0x40000049d45e04b30236,0x5a1,0xce086e000000001d22b8,0x18b1],#[0xc0000000000000000000,0x3ea00000000104bbc8b0,0x10,0x4842e0000000000131,0x685da00,0x186b500001c81280000,0x0,0x2000000000505a200000,0x1a00900000415,0x6000041ada0000000000,0x142b96048,0x80001216a5851dc08680,0xc900000000000001a958,0x1824a00000000140,0xd4000000001a16da8358,0x200,0x4ad8600002030dc0778,0x4140a000,0xf20da683e0000063a000,0x1b232a984,0x1c070b104e000000,0x0,0xa8ad0000000,0xc92975800000000503cc,0x1e4b9d00,0x8b8000000000,0x0,0x60000000000000000000,0x184d00000000005a1c,0x0,0xf800000000000000000,0x604b80001c0],#[0x0,0x306100000000,0x504f400000,0x3930a000000082000,0xa179000000000000000,0x0,0xa053a0000303ae000000,0x120cc,0x1e4ea8000000,0x7a916000000000,0x682c0e080800,0xa0000000000000000000,0x6016c000000000847,0x60000000000000403600,0x483,0x49ae000001858a000000,0x303720000,0x0,0xee0000000000000704b6,0x102,0x70000000000000000000,0x1052c00004840b602,0x884e81a1e00bd84e20,0x1014dc93e8000,0x6a0c2a07100,0x0,0x53c6000,0x0,0x0,0x782ce00000000000000,0x404a2000010ae8000,0x4b1c3839a0000000000],#[0x17200000000000000000,0x1e226d9b5a000008,0x14983283020000,0x0,0x1401e881ee,0x8081009a800010024800,0x6,0x0,0x2183800000,0x0,0x0,0x5a501c17e,0x845200000863000,0x8400000000000004852e,0x812c00000000034b,0x0,0x0,0x800000000000000cb6e0,0x87000000000000002856,0x40,0x9800000000000000000,0x4,0x0,0x0,0x0,0x816100000000,0x0,0x274000000001817f0000,0x38289650000000000030,0x0,0x68b5000,0x48006000000000],#[0x9cba0000304138213800,0x60ae2011e00004,0x2857b20b680000000,0x6160800000000000000,0x0,0x0,0xc801f04c00000,0x8700000609f8000000,0x160ec80001,0x0,0x0,0x0,0x739ffa13cf008c0,0x0,0xe44899045018280,0x3400000000000001e8b0,0x48c44043c00000000088,0x60b1a,0x0,0xa0000000000000000000,0x28213a0c,0x0,0x1202b0000,0x1614980000000000,0x3ff0081,0x111f1e0a28000000,0x7260e200000000000000,0x6018a211b690,0x1c1410000000000,0x6c8ac000000000000,0xa0000000000000000000,0x12f92496d92d],#[0x0,0x0,0x4038400,0x16800002214385f0,0x0,0x160b78,0x1604228350000,0x20000380fd6003000000,0x2034,0x405396191413a8000000,0x584640000005bee145,0x40600006003600,0xe2000000000000000000,0x854a000000000000019a,0x54055200ef6852400002,0x180b,0x1808f800000,0x0,0x6890a000000,0x381480000,0x840c00,0x16c3d80000,0x0,0x1850a000000000a0730,0x1ad8000000000000,0x101240000040f3a031a0,0x3d32158000008abf0000,0x80001606c00000000020,0x64f1,0x201f800,0x28ed00000,0x0],#[0x0,0x0,0x9e111721f512cb505ba0,0xa0bb30613e06bf02e,0xa0dfea0d2000000,0x700780000,0x9491099c14d0000000,0x1a29cda1c9,0x5cb7e6002800,0xc8bc2cf58,0x7a1c2000000000000,0x7e11a181f404ec000000,0x293a,0x4025c000000000000000,0x131815e0000000000000,0x4000000000001805900,0x10c18000000000,0x301e8e7000000000000,0x485786060c,0x4ce000000000000,0x1caff800000000000000,0x594d000000000,0x0,0x27800000000302460000,0x17904dc000071af4c1,0x1,0x0,0x29848,0x19a8291c82d80000000,0x18f218000140d5884c8c,0x1014f8000,0x692a00000000000],#[0xe4902560000000000000,0x20,0x58848000029010,0x0,0x0,0x0,0xa378000000000000000,0x0,0xe0458000000001012580,0x130000000006a8690023,0x181,0xcc000000000128200000,0x5056400005a0,0x0,0x521bc000,0x800000000000002a49a0,0x58,0x0,0x0,0x411fa92d800000000000,0x7e000000000011700001,0x280,0xe8000000000000031000,0xdf05dc000000001c0f,0x5846e1,0x1e80d4040,0x85e3c91600000000000,0x29800000000000002419,0x4ac2ac02e9207ee5,0x0,0x0,0xd824c806a0000100598],#[0x15c00000a17d80001819,0x2,0x0,0x0,0x0,0x40900000000000000000,0x0,0x4ac0800000000000,0x0,0x94d800000000200a6000,0x8c746800000000391e74,0x4033,0x1617660506000000,0x6877000000000,0x60dd8000000000000000,0x0,0x0,0x160518,0x0,0x3029c0000000000,0xe1060000000000000,0x401b6000000000450b80,0x0,0xa0bcf81e000000000000,0xe000042030000000000,0x781,0x701ca00005a35e00000,0x0,0x21a000,0x2baa08b0000000000000,0xa4d17cbd4000038,0x16096],#[0x1803000,0x0,0x205080000000,0x180001215300001a08a0,0x61,0x204a7e12e000000,0xdc2c929382fa00000000,0x50,0x7031e0000000000000,0xe7168000160cf8000000,0x1eedd000000000103e2,0x44e0000000000000000,0x60000000000000140083,0x1cf4,0x1a11e000016052b05ac0,0x5330000000000000,0x80000000000000000000,0x605442012,0x70858600b0000000,0x140b900000000000000,0x80d840ee700d00000000,0x162bc0000000005,0x1d00000000000000000,0x6507e01680000000008,0x613d8000000000000,0x202c000000000000000,0x4600000e10f800000000,0x187,0x183d8,0x0,0x58000000002001800000,0x100d480000004],#[0x186ea000000000000000,0x6005600000000,0x0,0x487a5f56879000000000,0x610380000a1878000084,0x1,0x1e14d982600000000,0x0,0x368800000000503a2000,0xa0000000000000000004,0x1600000000000000603a,0x60,0x5a000000000000000000,0x1e04880000c7,0x0,0x0,0x0,0x1e07da001e000,0x7a0ba800000000000000,0x10462e01a4001,0x6026584bc000000,0x28a700000,0x0,0x0,0x0,0x0,0x30426a073a00c0000,0x20000683a40000000000,0xa0630000000001819,0x0,0xaa7040fcda5b3a0e4,0x7059e492a8000000],#[0xfe000000000600080000,0x2,0xe00000eb06e826400000,0x1041,0x8edc123e800004a18a0,0x0,0x0,0x801000000000,0x0,0x1200f00000000000000,0x80f520f10bd1c0000000,0x1037c00000213a3,0x803593032000,0x100b85168878b824e0,0x28c6044000000000380e,0xb24dde87aba3b8000050,0x10b6000001a0f9,0x682b600006c8b400,0x862a80000,0x1c14c014cac02e000,0x89350,0x4e000001842828890000,0x190f8417e80000c,0x0,0x80000000000000000000,0x4801c0af5,0x185010000000,0x1e000000000000049090,0x405,0xcca49600000000000000,0x3080000000000001c14,0xa],#[0x5850000000000,0x1c388000000000000000,0x584d40000,0x0,0x2b8a9a42780000,0x8398e116800000000000,0x505a0854080001c2474,0x0,0x705c40,0xb3e00000000000000000,0x1a4ed6a,0x0,0xe85f0000000,0x28000000000000000000,0x33c20000512f60000413,0x78000000000000000005,0x781d6000000001c0d,0x12b40,0x0,0x0,0xc05c000000000,0x28ad80000792a600,0x3846a000000000,0x0,0x182788,0x781ba000,0xe0000000016246000000,0xa1b404600000a08c600e,0xa06a985d600005a,0x0,0x31bd000000000000,0x1c050984ac],#[0x604e800,0x9af3a1888000000000,0x785a60000484ec000,0x701c80000000000,0xc0660000000000000,0x80000000000000000000,0x5280000047d80001e940,0xe0cbb810c00000000025,0x1c27780000000000001,0x68c5000,0x0,0x0,0x1a1482853c0,0x0,0x0,0x148b200006232e00b3,0x51cca00,0x1e01200000000000000,0x13c42092000000000000,0x3,0x0,0x0,0x278000000000aedd8000,0x38,0x0,0x44b00000000000000000,0xc7608900000000000000,0x703,0x1c5518,0x4db800014109000b2000,0x185ce000031c300,0xa200000000000000000],#[0x8000000006a4c0000058,0xe610144000000001684c,0x38440051300001e8,0x1880e80001411180000,0x86180000000,0x1e0560000000000,0x140b200000000,0x0,0x0,0x2ca82000000,0xec48b06000000001882e,0x48b2f05434533880eb60,0xde000000000093880001,0x24,0x0,0x5500000000000000000,0x40000000000000382984,0x8f5ef818,0x6047a000000000000000,0x0,0x0,0x132e3d8b4e,0x1280000000006008800,0x1,0x0,0x1621680000c610000000,0x1c1438000180e08042,0x80000000000000000000,0x38b4bb2e2,0x2a4ca00,0x1c17ff130f20cf00000,0x13180000000000000000],#[0x1,0x39c260000284a4000,0x4000000000000000,0x29300c54a5e400000000,0x5030a000028,0x323940000000000000,0x0,0x5c000000000000000000,0x181620000701,0x0,0x30474000000000000,0x0,0x5b8000000000a03f8000,0x1e88200000000008,0x73b7a0000000000000,0x0,0x20227213300000,0x42a0000403160000000,0x1c18e0000000005,0x21a4a1d2000000000000,0x6a2780,0x4033400000000,0x0,0x0,0x0,0x1c0be00000,0x18e0000000000000000,0x5,0x6180000a03380000000,0x1a,0x1a0db8000,0x212fc000000000000000],#[0x0,0x3bb2400,0x0,0x6167000002612800,0xf00000000000000c74e8,0x42c037500b8da516c04,0x1c0c8a83132,0x294e0840000122180000,0x1e38000001607f48,0x2d000000000785f20000,0x21,0x84e200000,0x82540000000000000000,0x7cb8000002834c00004,0x5a906000000000000,0x849700001202c000000,0x4e00000000000000000,0x16b8000000000030,0x0,0x203980000000028b0200,0x6061181a083e0b980000,0xcd80afc80620000310,0x3,0x520ca000038120000,0x0,0x1e0f26039fa0468000,0x150f580,0x0,0x1265887560410000000,0x0,0x0,0x3821e000000000803e8],#[0x82b580000000,0x83fc0,0x4815a00000000,0x3051a80b280000000000,0x1a0968a4b60000,0x0,0x59012000000000,0xc13098b080000000,0xe07a0,0x284d6000018917a2a,0x0,0x122b80935a00000000,0x182aa000000,0x688ea000000001e076,0xc04d8000000,0x482b0,0x0,0xe04cc820600000,0x0,0x0,0x5d200000000000000000,0x847b00,0x4a800000000043fa0000,0x600f6c27769129e0,0xb6000000000000000000,0x400,0x2b4e4146a45200000,0x866082ac000000000000,0x1c10c800014,0x162d1203f800000000,0x80000000022607e06200,0xc30b00001c565],#[0x3668000000000000000,0x1835c000000001,0x0,0x80e38000000000,0x1041d2210f043a000,0x681656add621a20,0x0,0x181c6000000000000000,0x0,0x48a690c400003141000,0xc55100000000028641,0x0,0xe4b38,0x4f5c8cc20000313ba000,0xab4f800000000000008,0x0,0x0,0x1404e,0x405e0000000002058c00,0xda04cf9a2c7a11500001,0x683098d11b84,0x0,0x722b60000184ca000,0x12a38000000000210e60,0x0,0x5a51e00000bb28000000,0x704e62108800000000,0xc1210000000000000000,0x2832c000060c28,0x886a000000000e17a000,0x1,0x1b80000000000000000],#[0x1a88c00002823d6,0x1c0828000000000000,0x713e4000000,0x0,0xa0490000000000000000,0x30348a18d8210c,0x52f6800000000000,0x0,0x634a2000000000000,0x7e2c2800000000000000,0x84be32f302bc02456062,0x584fa000021c66000078,0x0,0xe15780001c1220000000,0x884134e0492492700001,0x80a58000020697cb,0x0,0x39032000,0x124ae000000000000000,0x1205d0000000000000,0x80000000000000000000,0x6166,0x281a200000000000,0xcafe00000000000000,0x9b420000000000000000,0x6276f,0xb480000000000000000,0x15d800016,0x1c04f8000000000000,0x69088000000,0x4837a0000000000000,0x15000000902c2845e00],#[0xde00000000000001828e,0x680,0x2817600000,0x0,0x0,0x56e00000000000000000,0x78,0x532049800000000,0x62b88000108730000000,0xbf80d280000000000000,0x403b58110d01,0x0,0x0,0x0,0x19d7600000000,0x0,0x0,0x1078000000,0x20280,0x794340000000,0x98000000b87809e44120,0x180000000006831140a,0x6,0xa3460d00000000000000,0xa959400000000000000b,0x585560000000008866,0x200e0000000,0xc4000000001003680000,0x1000cd92,0x0,0x0,0x0],#[0x1c11f0000000000000,0x80000000000000000000,0xc86b,0x8948a15a400000000000,0x84e4000000001,0x82340000000000000000,0xa1c400005,0x3849c0000582f6000,0x0,0x129288000,0x608440000000000f4500,0x0,0x0,0x108b080000000000000,0x0,0x31d12e0500,0x0,0xab7b800000,0x0,0x0,0x2938,0x0,0x0,0x826c0000000000000000,0xd0000121850000000006,0xc40,0xa000000001e612721e80,0x20c0000000000000781e,0xa4880000000012a5b92,0xa238,0x1050000000000000000,0x1884600001a03d],#[0x931c416f334a4e10a000,0xb0000000000000000003,0xc828284000000001f2e,0xe0000000000000000016,0x1a0c719cf,0x0,0x25728de605bd4bc60000,0x4c90000000000000022,0x5400000000000005826e,0x1488c4a0,0x700000000000000e0fd8,0x782d9822,0x0,0x1e16a8000000000000,0x68087603480000e53e80,0xa0b4,0x0,0x9480f700000000000000,0x243d80000c0d1c83,0x140f78863d03730,0x0,0x6a77785b40,0x7000000000000000000,0xe4e06000064ba620fd60,0xab00a89f000002177,0x40988000000000000000,0x809980001,0x88e0000000000000000,0x10076000068c2a00007,0xa80000000000000000,0xd538358aea0000310872,0x1810d0043800001055],#[0xd500000000000,0x6102e0000000000000,0x70dee00007934600,0x28306000000000,0x1a36600000405f800,0x3202a00000000000000,0x0,0x0,0xe0d98000,0x80000000000000000000,0x30000006ebf30602e510,0x930400000000003,0x8a000000000000000000,0x404,0x0,0x427000000000705c0000,0x201d0c11c309ca2,0x4160000000010e290000,0x61,0x0,0x4086c00,0x7b8a6,0x90660000000000000000,0xc720c6606cba4a72d54f,0x15b00001c72780000016,0xc2b9b03ac0000000008,0x1a1268000000000000,0x0,0x172,0x128fa8000000,0x0,0x10920000000000000000],#[0x7,0x104f8000038042000,0x0,0x188f28000000000000,0x181718000004ab80,0x24000000000400a00000,0x2a1a56c,0x0,0xa09d800000000000,0xc0f6a027000000,0x835000000000082c6000,0xc000078408a10d800016,0x400a00000a1919abf,0x0,0x81800000000000000000,0x412d588,0x70000000001206400000,0xb3ae00000000000001bd,0x98000000000000000003,0x6ab52000000001830,0x80de002a20,0x0,0x0,0x5852a0000000000000,0x69838000000005242200,0x4c00005a490000042038,0x2076800000000708,0x3280ae80826159200000,0x50,0x14308855e08e000000,0x0,0x1c0e1e8396000000],#[0x31000000000000000000,0x32e300001e32ea000543,0x5848c000000000,0x81ec0000000000000000,0x980000000000001c0d39,0x53596800,0x0,0x84230000,0x0,0x118448538800000000,0x0,0x10194000000000,0xcaeb800006287000,0x1e53d8000000000,0x208e80000000,0x0,0x0,0x0,0x0,0x0,0x813400000,0x0,0xc8ae0000000000,0x6980000000000000000,0xc,0x0,0x70364000000,0xa2bb000000000,0x670d20e1600,0x20494,0x38c0000094dfc0cc000,0x7],#[0x8321a604c04d00000000,0x5083e000000001c,0x58c1a80978000,0x3c2deaf2480000000000,0x53a806c0000082680000,0xe0858000168d600001c1,0x1,0x218200001e4fd000]]
def g235D9 := limbs80 #[#[0xd20fe107f843fa21fc10,0xa1fe50fea87f143fc41f,0x19508a379506c1e003fe,0x4c5103090054009f96db,0x814900091440c2040487,0x51030520910084c51030,0x4900091440c10804d020,0xc20524050094c5103081,0x24002440c20450064c40,0x10308100519310308115]]
set_option maxRecDepth 16000 in
def g235H9 := limbs80 #[#[0xc2053003000107040182,0x304014000024b0800841,0x48801b2c40092c00c928,0xc1bc02400400c4003081,0x30671c61001271c10012,0x53640142041d42d206,0x183051e0761057d03b00,0x151084804b0000000012,0x4f0184713b0000e77052,0x110a0000e2,0x290000f078f041406e00,0x3e913924661252e95151,0x480000e014c263607cd0,0x60b00d0000f0282037f2,0x4c613c70180000735f18,0x70346048557a505de0,0xa5551180d009000000,0x590000a9526470817e00,0x40f07462131079304d70,0x1020703765b007c347e9,0x868441f95c00000000b2,0x9c07e800ad022016780,0x20630000000061,0xf560302c1181f40500,0x894f3024d046474a00,0x4800000000804e000000,0x43000000000000801c41,0x5240710000013e575e80,0xe24e40,0x206bd26b0000c03f00,0x83b24624509035000000,0x7483624402170000b9],#[0x3f24c00000000000000,0x5186407790664410b0,0x78767db04f751a204400,0x61000000000000d00f67,0x1dc03d0000b445845de0,0x2f00000000c404e02620,0x106f626950214135d1,0x902060150000000000,0x8725a1370d274200e00,0x3200000000e01a0000e1,0x727d612ac7713365c0,0xd0134120942c00,0x6401139087401b000000,0x3000000000d064b00b14,0x190137c033746790,0x38467490688016e11a00,0x61d056e4441023d245a0,0x5d687a000000000000e8,0xc9,0x7b00000000c542000000,0x802fe138b000000025,0x656116d07b0000400100,0x1976804791877556f0,0x2b80318378f012808500,0x5e41e2216102ef65ac0,0xa47632590000000000,0x45b941d0620000906900,0x4e00000000405bd36830,0x1500003451806a114969,0x7fc5610000011f0000f1,0x490000c4290000000051,0x5f000000000000000030],#[0x710000e26c9040e26227,0x2900000000803a000004,0x52b136610b5025935eb0,0xa26d300600000000f4,0x42000000003779000000,0xd0360000a058d0,0x216600000000000000,0xc950203c0000576400,0x72211460670000718500,0x403249f05c0000c00840,0x2ae2123251a440826a92,0x7073d44f000004,0xe04a000000,0x53a275307d520d813a00,0x7d100200003080601ea2,0x4c00000000200c3075a1,0x41713f0000524d901759,0xf039446920810000b2,0x425bf05e00,0x5450820000411c000000,0x2d0053d21400000000e2,0x597117e0501675306070,0x51470277439000053,0x71541100000000000000,0x9182387b606d0000e3,0x11000095430000105f00,0x4b00005011c65ba45c02,0xb465f05a3247f01087,0x1f517c00002055918300,0x2d100400005379e97755,0x27e01f00000000b93961,0x6c207ac02a1054747764],#[0x19807fe25090830000f0,0xb2]]
def g235D10 (j : Nat) := if j=0 then 0x3f else 0
def g235H10 := limbs80 #[#[0x298231156208034a0060,0x7a41a8f98233dc971,0xc38c3644a898001a2800,0xa000000284213e416830,0x5440000006b491,0x2b8883800000000501,0x18a0aaa4e397385290,0x400a3400000000051480,0xa30a8208702800011d93,0x9d0931991118a0120005,0x6c2d08e2ac21000284ea,0x3aa30000000064a800,0x0,0x9460278180000000000,0x238005b2833231000000,0x73af9909aa]]
def g235L : Nat → Packing
  | 4 => (3,6,5,0,0,4,0,g235D4)
  | 5 => (192,5,5,0,0,11,0,g235D5)
  | 6 => (1097,4,5,0,0,14,0,g235D6)
  | 7 => (806,3,5,0,0,15,0,g235D7)
  | 8 => (136,2,5,0,0,13,0,g235D8)
  | 9 => (10,1,5,0,0,9,0,g235D9)
  | 10 => (1,0,5,0,0,0,0,g235D10)
  | _ => emptyPacking
def g235I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 3 0 6 2 0 g235H5
  | 6 => lookupWord 86 863 4 16 8 4 g235H6
  | 7 => lookupWord 480 4801 5 19 11 4 g235H7
  | 8 => lookupWord 361 5381 3 18 10 4 g235H8
  | 9 => lookupWord 76 457 6 16 8 4 g235H9
  | 10 => lookupWord 15 97 5 12 4 4 g235H10
  | _ => fun _ => none
def g235 : Forest := ⟨235,10,fun i => g235Y[i]?.getD (0,0),g235C,g235A,g235L,g235I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P4_0 : block g235 4 0 3=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g235B4 : block g235 4 0 3=true := g235P4_0
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
theorem g235B5 : block g235 5 0 192=true := (@block_merge g235 5 0 96 96 g235P5_0 g235P5_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P6_0 : block g235 6 0 2=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P6_2 : block g235 6 2 50=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P6_52 : block g235 6 52 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P6_148 : block g235 6 148 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P6_244 : block g235 6 244 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P6_340 : block g235 6 340 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P6_436 : block g235 6 436 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P6_532 : block g235 6 532 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P6_628 : block g235 6 628 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P6_724 : block g235 6 724 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P6_820 : block g235 6 820 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P6_916 : block g235 6 916 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P6_1012 : block g235 6 1012 85=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g235B6 : block g235 6 0 1097=true := (@block_merge g235 6 0 436 661 (@block_merge g235 6 0 148 288 (@block_merge g235 6 0 2 146 g235P6_0 (@block_merge g235 6 2 50 96 g235P6_2 g235P6_52)) (@block_merge g235 6 148 96 192 g235P6_148 (@block_merge g235 6 244 96 96 g235P6_244 g235P6_340))) (@block_merge g235 6 436 288 373 (@block_merge g235 6 436 96 192 g235P6_436 (@block_merge g235 6 532 96 96 g235P6_532 g235P6_628)) (@block_merge g235 6 724 192 181 (@block_merge g235 6 724 96 96 g235P6_724 g235P6_820) (@block_merge g235 6 916 96 85 g235P6_916 g235P6_1012))))
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
theorem g235P7_295 : block g235 7 295 44=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P7_339 : block g235 7 339 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P7_435 : block g235 7 435 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P7_531 : block g235 7 531 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P7_627 : block g235 7 627 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P7_723 : block g235 7 723 83=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g235B7 : block g235 7 0 806=true := (@block_merge g235 7 0 339 467 (@block_merge g235 7 0 103 236 (@block_merge g235 7 0 7 96 g235P7_0 g235P7_7) (@block_merge g235 7 103 96 140 g235P7_103 (@block_merge g235 7 199 96 44 g235P7_199 g235P7_295))) (@block_merge g235 7 339 192 275 (@block_merge g235 7 339 96 96 g235P7_339 g235P7_435) (@block_merge g235 7 531 96 179 g235P7_531 (@block_merge g235 7 627 96 83 g235P7_627 g235P7_723))))
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
theorem g235G : graphValid g235 (boundsBefore K222) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low235 : Lower true (varsX 235) (graphGoal 235) 11 := lower_forest (g:=g235) (i:=0) (hints:=1048659) (before_sound K222 V222) g235G g235T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K235 := extendKnown K222 11 [(235,[]),(237,[33])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V235 : Known true K235 := extend_ok (m:=235) V222 low235 (by decide +kernel)
def g245Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xc007ffffe0ffff72a6,0xa10baa00000fc003f03f])),(BitVec.ofNat 152 (word80 [0x82500a004204403202,0x21032a05145145145145]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfff800ffffffe03d4a,0x8666308003f000fc0fc0])),(BitVec.ofNat 152 (word80 [0x602c02800082350a,0x844210030c30c30c30c3]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffff0000ffffad84,0xb85846c000003f00003f])),(BitVec.ofNat 152 (word80 [0x2084308b0489000d84,0x985804eaaaaaaaaaaaaa]))),((BitVec.ofNat 152 (word80 [0xffffffffff0000804d,0x6156adc0fc0000000fc0])),(BitVec.ofNat 152 (word80 [0xb01402c002e048045,0x2114a9dc71c71c71c71c]))),((BitVec.ofNat 152 (word80 [0x9171,0x18b1d83f00003ffff000])),(BitVec.ofNat 152 (word80 [0xc0180300830088071,0x20c010410410410410]))),((BitVec.ofNat 152 (word80 [0x4e93,0x4f80057fffffc0000000])),(BitVec.ofNat 152 (word80 [0x300600c010c0104880,0x4a800420820820820820]))),(0x0,0x0)]
def g245C : List ColumnInfo := [(1,0,244,0,7),(4,0,241,0,7),(16,0,229,0,7),(32,0,213,0,7),(64,0,181,0,7),(128,0,117,0,7),(0,16,164,65,6),(0,32,81,132,6),(1,16,164,64,5),(4,32,81,128,5),(17,0,228,0,5),(33,0,212,0,5),(48,0,197,0,5),(64,16,164,1,5),(80,0,165,0,5),(128,32,81,4,5),(160,0,85,0,5),(5,0,240,0,4),(49,0,196,0,4),(52,0,193,0,4),(65,0,164,0,4),(65,16,164,0,4),(68,0,177,0,4),(81,0,164,0,4),(129,0,116,0,4),(132,0,81,0,4),(132,32,81,0,4),(164,0,81,0,4)]
def g245A : List (List Nat) := [[],[32,84,118]]
def g245D5 := limbs80 #[#[0x55140443cc5515150110,0x443cc5514154110e3965,0x5537154140e396455150,0x50d50ccf73d89515034e,0x40b6785b54603c6e0154,0x40]]
def g245D6 := limbs80 #[#[0x3b4a92a08870d5450d52,0x9daebb1281ce5515050,0x43f8a8a808871d5450d5,0x10df2caa0221ee551404,0x442fcbaa80886fb65501,0x110ef2a8a8221fc50550,0x4437db22a0886f96454,0x5110d7ac8aa2217edd15,0x644427fbb2a8884fd765,0x545209faebb22213fdd5,0x951502fdb8aa0a05df73,0x3d8940e7aa8a8a81bbd8,0xc165503ddb82a8a06ed5,0x54505509fee2b2a81bed,0x55361543b6a92c2a873d,0xb70551509fae9b0aa19f,0xf5c764542fdb82c8a877,0x6f7155152edae2aa2a53,0x5a0f0160027eb8ec0aa7,0x123f0de340c22b0961c0,0xaa6518e5a15251136481,0x127d1e6781da731c6701,0x929f266962529121e862,0x1f8c605441a150ab6aa2,0x6c01a101b102c705150f,0x4041011511098e88204c,0x5086811a150854880430,0x30210541421504541150,0x1c0c2060208007060,0x1817150c541000a304,0x2050401a04643e8e8440,0x21a058c6820703086054],#[0x1c0c]]
def g245H6 := limbs80 #[#[0x6e00002,0x3bc08300000,0x19000,0xc400000086000045e10,0x72000]]
def g245D7 := limbs80 #[#[0x350d52db54950bbd8940,0x90e52db55152f390d52f,0x4910fe54110fe50110f3,0x110bf59110fb94910fb5,0x40ef55140fe54140bfd9,0xf750d50bfd8550bf595,0xbfd9150df55150f790d5,0xfd8154fbd8552bfd8552,0x54520ff59110ff55110b,0x550ff54d40ff54540ff,0xd42ff59150ff58550ff5,0xffd8154ff58154ff54,0x1f8314550880da164180,0x686d001de35c5c0a712c,0x55962fc5a6a8d47a7b49,0x21c2180cf91e4b996fcd,0xc3003441a5eca291d1ce,0x19a2a118c38c795172e3,0x548483c38c795122a32a,0x841a18b914f8d1412a3c,0x4a5c4c72529510d98228,0x62c460870a0cb9522092,0xcc474a5442e1c2832a44,0xc60383025ca8d1d2950,0x6ca8468a846c3040468c,0x30260a8a623261f0120c,0x228d143838a2210d1838,0x2a4438a1c1812a2a3522,0x18a0c19628444224831a,0x52c242201c34708c9411,0x8a8664c111e8d08c68c1,0x52a118445431c182308]]
def g245H7 := limbs80 #[#[0xc2800000e000b21a7396,0xc0000000000000013001,0x580054600000002898c3,0x8a800000000000003e,0xe2ea48004c49c9e54000,0x29686800,0x915058811627841800c9,0x909993026000d800a214,0xb96b38719b1994f1d01c,0x810be1aa7800518076e4,0xac0000039f000c440009,0xc6942000000f1e911096]]
def g245D8 := limbs80 #[#[0xd30fe907f443dca5ed52,0xa5fd42fe997f543fa81f,0xd257240a82a007f553fa,0xf8e11551b557aae4fa04,0x22324024f8c28455c608,0x4b3c5961352111065922,0x81495c70a58e15472222,0x10c3492046009228633c,0x83e3842148347953388,0x218233e23451]]
def g245H8 := limbs80 #[#[0x797c32c30061ba0c0120,0xc60ea2e2860db49e9d63,0x56c8c002e279a40912e6,0x19af230e00061040b0b4,0x5c63c850f0002740cb80,0x51ad8832c1479a8c0512,0x88d95319a04e56610016,0xcc3000000003d2815e7f,0x370e083a868900191fc5,0x1566c349]]
def g245D9 (j : Nat) := if j=0 then 0xa4188201bf else 0
def g245H9 := limbs80 #[#[0x1f000c80,0x4000039279820018a230,0xc080001d,0x41700a0484a8000,0x23e74b00001660000,0xf9800000000628000000]]
def g245L : Nat → Packing
  | 5 => (7,4,5,0,0,6,0,g245D5)
  | 6 => (38,3,5,0,0,10,0,g245D6)
  | 7 => (34,2,5,0,0,11,0,g245D7)
  | 8 => (11,1,5,0,0,9,0,g245D8)
  | 9 => (1,0,5,0,0,0,0,g245D9)
  | _ => emptyPacking
def g245I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 2 53 2 8 3 1 g245H6
  | 7 => lookupWord 12 83 4 11 6 1 g245H7
  | 8 => lookupWord 13 61 6 11 6 1 g245H8
  | 9 => lookupWord 4 53 3 9 4 1 g245H9
  | _ => fun _ => none
def g245 : Forest := ⟨245,9,fun i => g245Y[i]?.getD (0,0),g245C,g245A,g245L,g245I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g245P5_0 : block g245 5 0 7=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g245B5 : block g245 5 0 7=true := g245P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g245P6_0 : block g245 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g245P6_1 : block g245 6 1 4=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g245P6_5 : block g245 6 5 33=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g245B6 : block g245 6 0 38=true := (@block_merge g245 6 0 1 37 g245P6_0 (@block_merge g245 6 1 4 33 g245P6_1 g245P6_5))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g245P7_0 : block g245 7 0 6=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g245P7_6 : block g245 7 6 17=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g245P7_23 : block g245 7 23 11=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g245B7 : block g245 7 0 34=true := (@block_merge g245 7 0 6 28 g245P7_0 (@block_merge g245 7 6 17 11 g245P7_6 g245P7_23))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g245P8_0 : block g245 8 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g245P8_2 : block g245 8 2 9=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g245B8 : block g245 8 0 11=true := (@block_merge g245 8 0 2 9 g245P8_0 g245P8_2)
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
theorem g245G : graphValid g245 (boundsBefore K235) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low245 : Lower true (varsX 245) (graphGoal 245) 10 := lower_forest (g:=g245) (i:=0) (hints:=2098436) (before_sound K235 V235) g245G g245T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K245 := extendKnown K235 10 [(245,[]),(250,[80,16,98,50,67,65,113])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V245 : Known true K245 := extend_ok (m:=245) V235 low245 (by decide +kernel)
def g127Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfb02da18b421cc2951,0xe0c00001fc0000003fff])),(BitVec.ofNat 152 (word80 [0x4102d81094204c0841,0x80c48912244891224489]))),((BitVec.ofNat 152 (word80 [0x1228d2402d89e9fc1,0x1b0000fe00000fffc000])),(BitVec.ofNat 152 (word80 [0x61008c2402188c1fc1,0x90183060c183060c183]))),((BitVec.ofNat 152 (word80 [0x758ad02f634115537,0x8407f000007f0000000])),(BitVec.ofNat 152 (word80 [0x87188d02f634105513,0x803870e1c3870e1c387]))),((BitVec.ofNat 152 (word80 [0xf25c4ce7abc3f04140,0x6900000003f80000007f])),(BitVec.ofNat 152 (word80 [0x25c04e623c3904100,0x6913264c993264c99326]))),((BitVec.ofNat 152 (word80 [0x85814f63a014663a,0xd6bf80000000001fff80])),(BitVec.ofNat 152 (word80 [0x5010b618010603a,0x520a142850a142850a14]))),((BitVec.ofNat 152 (word80 [0x116669158062bf0a8,0x15c0000003ffffe00000])),(BitVec.ofNat 152 (word80 [0x26211080023a028,0x14ec58b162c58b162c58]))),((BitVec.ofNat 152 (word80 [0xce93272055b22080f,0xc3ffffffc0000000000])),(BitVec.ofNat 152 (word80 [0x8e022400043220004,0x43060c183060c183060]))),(0x0,0x0),(0x0,0x0)]
def g127C : List ColumnInfo := [(4,0,123,0,10)]
def g127A : List (List Nat) := [[]]
def g127D10 (j : Nat) := if j=0 then 0xff else 0
def g127L : Nat → Packing
  | 10 => (1,0,1,0,0,0,0,g127D10)
  | _ => emptyPacking
def g127I (_ _ : Nat) : Option (Nat × Nat) := none
def g127 : Forest := ⟨127,10,fun i => g127Y[i]?.getD (0,0),g127C,g127A,g127L,g127I⟩
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
  · exact (rfl : block g127 7 0 0 = true)
  · exact (rfl : block g127 8 0 0 = true)
  · exact (rfl : block g127 9 0 0 = true)
  · exact g127B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127G : graphValid g127 (boundsBefore K245) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low127 : Lower true (varsX 127) (graphGoal 127) 11 := lower_forest (g:=g127) (i:=0) (hints:=1049923) (before_sound K245 V245) g127G g127T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K127 := extendKnown K245 11 [(127,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V127 : Known true K127 := extend_ok (m:=127) V245 low127 (by decide +kernel)
def g191Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfff607e0a2c1077115,0x328c000003f000000fff])),(BitVec.ofNat 152 (word80 [0x28206e08241036104,0x300c9249249249249249]))),((BitVec.ofNat 152 (word80 [0x2c634900e8de8fa,0x41280000fc0000fff000])),(BitVec.ofNat 152 (word80 [0xcc2823090088d60f8,0x410830c30c30c30c30c3]))),((BitVec.ofNat 152 (word80 [0xfb23483c9688551,0x5c50003f00003f000000])),(BitVec.ofNat 152 (word80 [0x570fb23483c9288051,0x544071c71c71c71c71c7]))),((BitVec.ofNat 152 (word80 [0xffe4b93a5eaa878214,0x7400fc0000fc000003f])),(BitVec.ofNat 152 (word80 [0x9804b912508a848210,0x7406186186186186186]))),((BitVec.ofNat 152 (word80 [0x10b8c759f40b063,0xace0000000000003ffc0])),(BitVec.ofNat 152 (word80 [0xe001090c6596409003,0x8ce34d34d34d34d34d34]))),((BitVec.ofNat 152 (word80 [0x22c13057070590e,0xe157f000000ffffc0000])),(BitVec.ofNat 152 (word80 [0x4010420401906,0xa0158618618618618618]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x19d049c814980680,0x9c8ffffffff000000000])),(BitVec.ofNat 152 (word80 [0x1040080814100400,0x8820820820820820820]))),(0x0,0x0)]
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
theorem low191 : Lower true (varsX 191) (graphGoal 191) 11 := lower_forest (g:=g191) (i:=0) (hints:=1049923) (before_sound K127 V127) g191G g191T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K191 := extendKnown K127 11 [(191,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V191 : Known true K191 := extend_ok (m:=191) V127 low191 (by decide +kernel)
def g223Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfffff7085924c03dd8,0x11f0200000f8000f83ff])),(BitVec.ofNat 152 (word80 [0xa401450051008031d0,0xd02084210842108421]))),((BitVec.ofNat 152 (word80 [0xfe000944a3c2133972,0x741910001f0001f07c00])),(BitVec.ofNat 152 (word80 [0xc8066104a382103950,0x7019118c6318c6318c63]))),((BitVec.ofNat 152 (word80 [0x73661d9e08325,0x50b51003e0003e000000])),(BitVec.ofNat 152 (word80 [0xf02b872661d0c08325,0x50b5139ce739ce739ce7]))),((BitVec.ofNat 152 (word80 [0xfffff2978db2dd88e2,0x9106107c00000000001f])),(BitVec.ofNat 152 (word80 [0x4c02968cb2598822,0x91061739ce739ce739ce]))),((BitVec.ofNat 152 (word80 [0xcc585e4d4135,0x662680000007c0007fe0])),(BitVec.ofNat 152 (word80 [0x7000c8085c450025,0x6268a5294a5294a5294]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x11220b03a6606,0x8a8aef800007ffff8000])),(BitVec.ofNat 152 (word80 [0x80001000202a4402,0x88000421084210842108]))),((BitVec.ofNat 152 (word80 [0xce98609049009,0x8855dffffff800000000])),(BitVec.ofNat 152 (word80 [0x10008490009040008,0xc842108421084210]))),(0x0,0x0)]
def g223C : List ColumnInfo := [(1,0,222,0,9),(2,0,221,0,9),(4,0,219,0,9),(8,0,215,0,8),(16,0,207,0,8),(64,0,159,0,8),(128,0,95,0,8),(0,8,86,129,7),(20,0,203,0,7),(0,4,27,192,6),(24,0,199,0,6),(80,0,143,0,6),(128,8,86,1,6),(136,0,87,0,6),(144,0,79,0,5),(192,0,27,0,4),(192,4,27,0,4)]
def g223A : List (List Nat) := [[]]
def g223D6 := limbs80 #[#[0xb2ac8a9f83e496559153,0xa9757916116554fc9f24,0x4b815d954cf3c1702bb2,0x5593c5eebc12cab2679e,0x3c9702baac9ba782e057,0x6e4b2d79e4574dc965dd,0x4884f1b274202bcf22c2,0x30a080e2f0f803c7767,0x18b040000]]
def g223D7 := limbs80 #[#[0xe5d6559153e1d6559153,0x9f7815d954f4f8259553,0xeaf82595649ef825d954,0xbb7815d564e3f7559564,0xf5d8459553baf825d564,0xdef825d954df7815d954,0xbf7815d564eef8259564,0xfb7815d564bef825d564,0xded74dc965faf825d564,0xbf7815d165ded84dc965,0x549243b8c8288740d800,0x8aa1c83a007a9d469980,0x4338b87806a8a8c9da50,0x545e20c10e1a4e01e911,0xc4e2c5e012158b878230,0x28ce1e0a51b138717804,0xa5e0159c978b87805c46,0x26117129787804e2618b,0x102e10b88042100b856,0x448ba5e22113101c4071,0x99184208610a2e948b8,0xc5e2]]
def g223H7 := limbs80 #[#[0xe3000000020700,0x840000000000000010,0x68050056000051000000,0xd90000]]
def g223D8 := limbs80 #[#[0xd6554fcf322a7e759153,0x2ac9e799253f3ac929f5,0x53bfee8a9def725975eb,0x7dd6494fefba2a7f7591,0xeb2ac97f5d954f7ac8aa,0xd564f7aeab25ff755937,0xb1dff74597f7b92cbefd,0x3feba2cbff5d564ffaa8,0x99351fc31c4b86006000,0x257a9e11d2033a668cb,0x8b30c20e3ec76addd9cb,0x324c3806498a2e1c0306,0x3100b93161c03078789,0x4c930e2c03a48717161c,0x111318cc5870251e2c3,0x61e018309c9331c6c317,0x18324c5170e018345c58,0x28b0f0e0483a4c5170e0,0x491d1e1a6c58700b2136,0x96212407450e0f10bc18,0xb8700e1c80ec633161c0,0x4e8c5e24b830901c1e24,0x78e9c223c5852e01c40e,0x1e1c0406c98c14cc380,0x8c40722422c51a1c20e9,0x3a2a121885]]
def g223H8 := limbs80 #[#[0x28000000161002528,0x1a5757329fe92771,0x86a0e22e7130000000b1,0x140e902f6670]]
def g223D9 := limbs80 #[#[0x43ef993bd64f794fdd53,0xfd64ff553fd63ff54ffd,0x69d4c64b1806000ff597,0xc390c1628601f6d7aa54,0x31a28602269050e28601,0x30532388612180712532,0x471031628603078a180a,0x68e28602c79641e28603,0x4093869633228601091e,0x9068c588c860]]
def g223H9 := limbs80 #[#[0xd04c8e7490102e,0x70e0e00003b8012c000,0x13c000000b288c000,0x1518281000abf1550200,0x35000355]]
def g223D10 (j : Nat) := if j=0 then 0x3148310403ff else 0
def g223H10 := limbs80 #[#[0x4300006200000000,0xa8000041b5000084,0x96006720000039000000]]
def g223L : Nat → Packing
  | 6 => (10,4,5,0,0,7,0,g223D6)
  | 7 => (20,3,5,0,0,10,0,g223D7)
  | 8 => (22,2,5,0,0,11,0,g223D8)
  | 9 => (10,1,5,0,0,9,0,g223D9)
  | 10 => (1,0,5,0,0,0,0,g223D10)
  | _ => emptyPacking
def g223I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 2 37 0 8 4 0 g223H7
  | 8 => lookupWord 5 31 3 9 5 0 g223H8
  | 9 => lookupWord 5 37 4 9 5 0 g223H9
  | 10 => lookupWord 2 37 0 8 4 0 g223H10
  | _ => fun _ => none
def g223 : Forest := ⟨223,10,fun i => g223Y[i]?.getD (0,0),g223C,g223A,g223L,g223I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P6_0 : block g223 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P6_1 : block g223 6 1 9=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g223B6 : block g223 6 0 10=true := (@block_merge g223 6 0 1 9 g223P6_0 g223P6_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P7_0 : block g223 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P7_1 : block g223 7 1 8=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P7_9 : block g223 7 9 11=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g223B7 : block g223 7 0 20=true := (@block_merge g223 7 0 1 19 g223P7_0 (@block_merge g223 7 1 8 11 g223P7_1 g223P7_9))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P8_0 : block g223 8 0 7=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P8_7 : block g223 8 7 12=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P8_19 : block g223 8 19 3=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g223B8 : block g223 8 0 22=true := (@block_merge g223 8 0 7 15 g223P8_0 (@block_merge g223 8 7 12 3 g223P8_7 g223P8_19))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P9_0 : block g223 9 0 4=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P9_4 : block g223 9 4 6=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g223B9 : block g223 9 0 10=true := (@block_merge g223 9 0 4 6 g223P9_0 g223P9_4)
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
def g239Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfff64e00931d7ac265,0x40000000fc003f00003f])),(BitVec.ofNat 152 (word80 [0x81464a00811d78c204,0x45145145145145145145]))),((BitVec.ofNat 152 (word80 [0xc00bf004ccb6440657,0x4000003f000fc0000fc0])),(BitVec.ofNat 152 (word80 [0x66bf004c4a4400647,0x430c30c30c30c30c30c3]))),((BitVec.ofNat 152 (word80 [0x13af0e540702ce4,0xc0000fc003f00003f000])),(BitVec.ofNat 152 (word80 [0xb813a60e540502c64,0x430c30c30c30c30c30c3]))),((BitVec.ofNat 152 (word80 [0xfff94163f1a3839461,0x8003f000000000fc003f])),(BitVec.ofNat 152 (word80 [0xc09006370a2830461,0x8a28a28a28a28a28a28a]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x215f0a957c7488,0xfc0000000000ffffc0])),(BitVec.ofNat 152 (word80 [0x100001180a112c5088,0x14514514514514514514]))),((BitVec.ofNat 152 (word80 [0x49ca952220d1b94,0xbf00000003ffff000000])),(BitVec.ofNat 152 (word80 [0x200004891202051190,0x98618618618618618618]))),((BitVec.ofNat 152 (word80 [0xb0208244881410a,0x7ffffffffc0000000000])),0x20820820820820820820),(0x0,0x0)]
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
theorem low239 : Lower true (varsX 239) (graphGoal 239) 12 := lower_forest (g:=g239) (i:=0) (hints:=1049939) (before_sound K223 V223) g239G g239T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K239 := extendKnown K223 12 [(239,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V239 : Known true K239 := extend_ok (m:=239) V223 low239 (by decide +kernel)
def g247Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfeca221f9d2a55c200,0x4000003f00003f00003f])),(BitVec.ofNat 152 (word80 [0x28ca2207902a458200,0x45145145145145145145]))),((BitVec.ofNat 152 (word80 [0xa02ac2f05023b813,0x40000fc0000fc003ffc0])),(BitVec.ofNat 152 (word80 [0x4ca02042b04003a003,0x41041041041041041041]))),((BitVec.ofNat 152 (word80 [0x1ecb4d6808388026b,0x3f00003f000fc0000])),(BitVec.ofNat 152 (word80 [0x71e834d68080800223,0x30c30c30c30c30c30c3]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfe504d90dea41e102e,0x80000000fc0000000fff])),(BitVec.ofNat 152 (word80 [0x104d904e8018102c,0x2aaaaaaaaaaaaaaaaaaa]))),((BitVec.ofNat 152 (word80 [0x112b6d083f8128ec,0xfc0000000000fff000])),(BitVec.ofNat 152 (word80 [0x80110a29083f00084c,0x1c71c71c71c71c71c71c]))),((BitVec.ofNat 152 (word80 [0x2e542b025400c554,0xbf000000ffffff000000])),(BitVec.ofNat 152 (word80 [0x400280014004150,0x90410410410410410410]))),((BitVec.ofNat 152 (word80 [0x191c1206588680781,0x7fffffff000000000000])),(BitVec.ofNat 152 (word80 [0xc1004500280480,0x20820820820820820820]))),(0x0,0x0)]
def g247C : List ColumnInfo := [(2,0,245,0,10),(1,0,246,0,9),(4,0,243,0,9),(64,0,183,0,9),(128,0,119,0,9),(16,0,231,0,8),(32,0,215,0,8),(0,16,164,67,7),(0,32,81,134,7),(5,0,242,0,7),(20,0,227,0,7),(33,0,214,0,7),(65,0,182,0,7),(132,0,115,0,7),(1,16,164,66,6),(4,32,81,130,6),(17,0,230,0,6),(36,0,211,0,6),(48,0,199,0,6),(64,16,164,3,6),(68,0,179,0,6),(80,0,167,0,6),(128,32,81,6,6),(129,0,118,0,6),(160,0,87,0,6),(21,0,226,0,5),(49,0,198,0,5),(52,0,195,0,5),(65,16,164,2,5),(69,0,178,0,5),(81,0,166,0,5),(84,0,163,0,5),(96,0,151,0,5),(132,32,81,2,5),(133,0,114,0,5),(144,0,103,0,5),(161,0,86,0,5),(164,0,83,0,5),(192,0,55,0,5),(53,0,194,0,4),(85,0,162,0,4),(97,0,150,0,4),(148,0,99,0,4),(165,0,82,0,4),(193,0,54,0,4),(196,0,51,0,4)]
def g247A : List (List Nat) := [[],[32,84,118]]
def g247D5 (j : Nat) := if j=0 then 0x1b82689a05955458d20 else 0
def g247D6 := limbs80 #[#[0x6558fe095458d5258120,0x9563541208a7ea584211,0xa6896555160483e49a25,0x483e19a05955458d20f8,0x6558d20f0769d6555163,0x8986dd5544c36c992641,0x3c1da75955458f40b4be,0x58150f075d59459563d0,0x9459563542e6ba265165,0x4fa26516558d50b96e81,0xd50b36e81945d963542e,0x5516310eccfa26517658,0xa824d6555163f0769d65,0x3f0721e935955458ee1e,0xd6558ee1ea8a4d655516,0x6108459563ab3e8984a0,0x87649905955458e2bfa9,0x558fa1d85651651d163d,0x38059563ab3e89846016,0xe8994e016558eacfa261,0x8f29e976108459563ab3,0x459563d93dd792611655,0x697e116558fa1f75e128,0x9eba25d3805cd6599769,0xa54692461ecd4591e802,0xabbdd2e36eb5da2c057a,0xca350275298c44a19067,0xd05c07e00b6faf562a54,0x20b0107e00210963545,0x828101000304080e0816,0x840400000000380,0x6080000000020404e082],#[0x68]]
def g247H6 (j : Nat) := if j=0 then 0x1 else 0
set_option maxRecDepth 16000 in
def g247D7 := limbs80 #[#[0xb1aa09079a5956254120,0x41ad98658d50483cb2ca,0x8d5258120e3cbb2caa82,0x483cd2caa92c0907b25,0xcbaac6b0241e995458d6,0x2c090736e5d6358120e6,0xc797559560483c72caaa,0x6558d20f0eb2aa8b1a41,0x3c3acaaa2c7a07175d5,0x2f04b02a1c5d7559563d,0x6a8796e416558d50d3cb,0xd5458d525839b720bb2c,0x58d60e1eb2aa9b92c1e1,0xdb720baac6b05b664273,0xcaaa2c1e3b9059554582,0x1f0fe1d6555160e1e43a,0x55956310fc3acaaa2c62,0x163e1eb2aa9b92c7c5d7,0xaca41aa8b1e1f21d6555,0xaa2c7e1c935955458fc3,0xf21d6555163f0f49aca,0x537258ecbb2b41acab1f,0x3e2fbaacbb92c7e1d655,0xb2aa8b1f87641655516,0x2c7e1c875955458fc3f2,0x6108459563d2ec2aca3a,0x6558ed9f24c22cab1ea7,0xefcc2e639acba9f84a11,0x2ac0907da64965541208,0x1ed99059563483dd324b,0xd6558d20f66c92cab1a4,0x4c37d304c02ca9073765],#[0xc930caa261f596454d50,0xa89878fe1965551309f7,0x3f86dd5544c3a7b0dbaa,0x655330bd7c930caa261d,0x27df24c32a9984fee418,0x2caaa661f3b9059554cc,0x985eee418655330f1fc3,0x64e0153502f5f24c32a9,0x8f40f4eca2cab1e81bb9,0x7b2eb2aa9a073765d655,0xab02a1d3d7561165d03a,0x79e6516558150f3cc92c,0x59563543cbb24b2ac6a8,0x50e6ec92ecb1aa1e5d94,0x20c22caa87376517658d,0xb2a176f9261165542ef7,0xbe49845d950afdc8308b,0x554583d3f2eaa2c6b057,0xf1ec92caaa2c1e7b9059,0xc3aa8b078fe1d6555160,0xc16fb9061165582d7b2d,0x5d6558c43b77c9308b2a,0x54f9bb2eb2ac721f376,0xe49acaaa2c75fb905937,0xaa8b1f97a4d6555163f2,0xe3f925955458fc7b24b2,0x8359563d6ec2506b2ac7,0x8f57b08422cab1eb7e12,0x2508b2ac76ef92611655,0x8b1fa7651651d163d5fc,0xd826016558fd3d28b2ee,0x59563d6ec2300b2ac7ad],#[0x5bb29c02cab1eb761380,0x4b2ac7e5f756096558f,0x1f97dd48459563f2fbaf,0x6116558edbd2e422cab,0x563f2fbab08b2ac76df9,0xeeb422cab1db725d8459,0xb2ac76de97a116558fcb,0xb7a5f8459563f2fbaf08,0xd370596bdf24ba2e0b2d,0x5af7c9309b82cb5ef925,0xba0e6b2d7be49741cd6,0xacb9f974e01735963ff3,0xdd3805cd65cfd3a700b9,0x6098039011c04c00067e,0x5852825211207b037c18,0x121f70e886fc3461870b,0x4e8a184de25811e08804,0x6943291868bc45aa2b91,0x1f40f307603941bc0d84,0x493448322e910484a3ff,0x328313d09ce4da26692c,0x34a7653329814a0a3651,0x7d2ba95b4ad45622ad15,0x6a0b405982c81620b0a5,0x61930617d4bd05cc2da9,0x1938c8c64331d98ccc4c,0xa68d34019cccd665e32b,0x41b6cd9c6b73529a74d2,0x3a7153891c14dfa6fa37,0xb09d50e8e73a3969c94e,0xf727ac3ca9e0cef676e3,0x3f99fc0fda7db3e99f2c],#[0xf00780c404a004ffc7f6,0x70609a0f8388d43209,0x43f03822026c3f0bc27c,0xfc0830705e0ec2c450b3,0x27c0b0c8c3c0d0241761,0x827c014215141731ec68,0x585fc00841c102605c14,0x7c0070442588013c0070,0x981c45c21f0309198842,0x914140258807244f0060,0x4f001c14260841cf038,0xc260841ca1bc01494620,0xb0a47433c01c25f001c0,0xc0102df001c0c170528f,0x81c087c047450b417073,0x70405307f002145c588,0x432022f001c104af001a,0xfc0084971484073c00b4,0x142161f81f0020142661,0x3f018b142604e8bf030a,0x14c2bc00702114044281,0x284098230841cf002018,0x2101cf018a1026073c0a,0x20070552012f001c6285,0xcc822bc0070509821f00,0x70409b0a073c0084540,0x21314bf002c1c5408fc0,0x8452fc00702d1548615c,0x14b1d8509821f001c14,0xf00211148c1e85094c3f,0x211618c13c0d0c4d0ccb,0x42f001c0812d0ccbf00],#[0x209817e0830350108144,0x8041208810822040d624,0x1206089021dc20d87040,0x58e041c04001c1c0c17,0x8010601060120410087,0x450500d70b0111040802,0x11c20b4208018621c2c0,0x24082d08820618870981,0x10008078104200042708,0x7049705820b415201058,0x4180704e04206304089,0x1461148519850c070416,0x61d8a0987628208c1252,0x13030a04040015c23183,0x8c6082d04160418040c,0x2321c232dc208c670827,0x10c23060410c2b094308,0xc2322c208c871018c10c,0x30423042321c160f0408,0xc0c1000001604b430d4,0x1c204]]
def g247H7 := limbs80 #[#[0x77291551e078420006a0,0xa3000001c3a8400d0b63,0x7278100000f2e1851407,0x4c800f995a000000014e,0xb64005c6d5ba3d323f88,0xc5800000c600000,0x37bd236d4d2cc0047417,0xa2b90301a4910002d2f0]]
set_option maxRecDepth 16000 in
def g247D8 := limbs80 #[#[0xed96358120e1d6555163,0xcdf7658d30f595354130,0xed96358140d3f7555130,0xe796558150ed96358150,0xcdd7658d50e5d6558d50,0xe9d5458d60edb8058d60,0xcdf7558d60e9e5458d60,0xcdf7658d43e3d6555160,0xd3d7555243b9f8355243,0x9fb805d953cdf7658d53,0xe9d5498d63add8098d63,0xadd8598d63e9e5498d63,0xd9f749d163e3d6555163,0xe5f7559563adf8059563,0xfe95250120bdb805d563,0xfd96354120fe96254120,0xdf97654120f796554120,0xfe95258120bf98654120,0xfb95458120ef96358120,0xdf97558120ef96558120,0x9ff8758d20bfb8058d20,0xf9d5458d20fdb8058d20,0xddd7558d20edd6558d20,0xd7d7559520ddf8758d20,0x9ff87595209fd8759520,0xddd63dc930f796554130,0xf3d65551309fd86dc930,0xf3d65553309ff825d930,0xef96358140bfb8059730,0xbfb8054d40ef96558140,0xf3d5454b40edd6558d40,0x9fd8754b40d7d7554b40],#[0x9ff8758f40dbd545cb40,0xedd6558f40f9d5458f40,0xddf8758f40ddd7558f40,0xddd7598f40f9d5498f40,0xdbd7655340f3d6555340,0xbbf8655340bbd8655340,0xd7d7559740dbd7559340,0x9ff87597409fd8759740,0x9ff865d7409ff825d740,0xf795358150bfb8258150,0xf7b8059550e7d6558950,0x9ff825d950dfb805d950,0xe7d6554960edd6354960,0xcfd65dc960dbd54dc960,0xedd6390d609fd85dc960,0x9fd8790d60afd8690d60,0xedf8258d60ede7358d60,0xedf8458d60edd5458d60,0xbfb805cd60edd7558d60,0xe7d6555160bf9809cd60,0xdbc87551609ff8755160,0x9fd85dd160dbf8755160,0xbfb805d560efb8059560,0xedd6558c43f9d5458c43,0xd7d7559443ddd7558c43,0x9ff87594439fd8759443,0xf9d65d0e43ddd635c243,0xedd6558e43f9e5458e43,0xdbd7695243ddd7558e43,0x9fd8759643cfd7659643,0xddd63dc9539ff8759643,0xbdf8258d539fd86dc953],#[0x9fd80dc9639ff825d953,0xdbe54dc963dbd54dc963,0x9fd85dc963cfd65dc963,0xedf7498d63edd5498d63,0x9fc8755163e7d6555163,0xdbc8755163f9c8355163,0x9fe8795163dbf7495163,0xdbe8795163f9e8395163,0x9fd85dd1639fd80dd163,0xede8359563edc8359563,0xbdd80dc963bdf825c163,0xf9e54dc963f9d54dc963,0xddd75dc963edd65dc963,0xbdd85dc963ddf75dc963,0xf9f7495163f9c8755163,0xf9e8795163bde8795163,0xbdd851d163edd651d163,0xedd65dd163bdd80dd163,0xedd8059563bdd85dd163,0xedd8259563edf8059563,0xedc8459563edf8259563,0xede8459563edd8459563,0xbdf825d563edf8459563,0x9fd82dc165bdd859d263,0xbfb805cd65ddd731cd65,0xddf739cd65b7f855cd65,0x9fd82dcd65b7d859cd65,0xdfd8759520ff98059520,0xfdd6454d30ff96454130,0xf7d6555130fbd6455130,0xbff8655130bfd8655130,0xfbf8655130fbd8655130],#[0xbff8459530dfd7559130,0xfbd6455330fdd6454f30,0xbfd8655330f7d6555330,0xfbd8655330bff8655330,0xdfd7559330fbf8655330,0xbff8459730ffb8059730,0xfbd6454d40ff95358140,0xfbd6454f40dfd7654d40,0xfbd8459740dfd7654f40,0xdfd825d740dfd8759740,0xf7d6454d50dfd865d740,0xf7d8459550f7d8259550,0xdfd845d950dfd825d950,0xfbf8755160dff7454d60,0xefd8459560efd8259560,0xdfe8759543dfd8759443,0xdfd64dc153dfd8759643,0xdfd80dc963dfd64dc953,0xefd8259563dfd85dc963,0xefc8459563eff8259563,0xefe8459563efd8459563,0xfdd80dc963eff8459563,0xdfd725c165fdd85dc963,0xdfd74dc165dfd745c165,0xdfd741cd65dfd84dc165,0xdfd745cd65bff825cd65,0xdff745cd65dfe745cd65,0x5d00cc000dff749cd65,0x7d04e010e03900ba0264,0x9096023708101da06c01,0xd983450c6c2f10b1c27,0x1ac43810383e40ee8399],#[0xe455814944f212fc4951,0x46e41a1062417e85b515,0x85e20ac7ef1ef076e1ca,0xab25e094524008c4228c,0x32b80aad29c4a5028089,0x3024bd62eb0b8b2d60b1,0x4c8cff330cc903198c3c,0x70df23720da735f4d5c3,0x4f513c54ed03a2ce4638,0xcb421904a4038fc93e3,0xe2467516a452511643d5,0xe4cc92e44a7d26348791,0x51b54434ff93cb4e8536,0x63555a549d4f45329497,0x8d6b059d164157f15c95,0x97f45f0578e5d4971f5b,0x90b63858b76211851607,0x5868719e0669196864f9,0xe6da5b2d6c0dae26a75a,0x7291c68711dc146f85ba,0x735da375c1d3d7429cce,0x69ef97ad1e7878cddf77,0x202b7f99fc57e25f3b7c,0x130841a0d382a6076813,0x6288521e1867217b8546,0x78eca3888cea2ec8a9e2,0x93b64cc928a47890863f,0x7825d196e658f954e517,0xe2685999264398425ef9,0xe7429caa7249c326eb9a,0x81a9fe67cf9e967849d8,0xb3a29288ca1ae84aa0ca],#[0x5a51a925a4128eca32e8,0xa8569fda74e9a9a5da95,0xb02aa8aa42a78a916a2d,0x3eb6ead36b23abe6ad8a,0xac7cb14ac28affabc2ae,0xd54b4f2d1bb3c6cc7b29,0x39c016e05b7b6dbab5fa,0x311439c015888421884,0x4c321c2c0287e27005,0x7004224138813e02644e,0x182b1c2dc01587040e,0x2c15f00382858581e0e7,0x158704160af801c102c,0x15868b91087801c142dc,0xf01444700441c0f801c,0x801207090b16078421cc,0x16450943e003914204f,0x83e00385e00383e18578,0x850704e0068381f0a89,0xe007048530f801a1025c,0x5888401887801c142a0a,0xa2d15f0038204f80162,0x943e003850b10f85c00e,0x280c1d0be0074422f0b0,0xc3e1709e031038370056,0xa041342e1ec4e0072123,0x456270019822a1fc0110,0x5118609282f0b1607090,0x41c1c2e1463514421ce0,0x30c42385e16090b7011,0x2fc061c2488bc268a1ce,0xe702881d144d0b10870],#[0x18a8b2470288890e0c88,0x89c04487070401b801c1,0x21c1b80210e068f45916,0x3702881c1c4d8b10f031,0x1086e0070462a5112884,0x5c00e92880e702881d15,0x988168b01007030144,0x26280c1007c1607178ae,0xc2c220cc4e004c203700,0x2700262815881aa17003,0x1006a2607808a098e466,0x18a0e064662703141c14,0xc08588450b700381a138,0x113080ee022cbe285c1d,0x143bc00d88440e703162,0xf03c0128c200df003a25,0x4c0b0f801b108a20a186,0x82700421c0e89c00d870,0x1c1380250e0626e00943,0xb1381444606c412f0046,0x43906e00847a2703021,0x85c0d0c31c0108e26c2e,0x11e0c01a1b13800f1d0e,0x4a311c0306a1f00423,0x1ce06044a304a1cc3c0f,0x50c0e05c0f004a38828a,0x806038170225e0098610,0x25e008070186f03c0128,0xa3f80171408070280f02,0xb459c0158a05e0038501,0x2e1ee00b45e00705a18,0x60401c0ac2c5f0058387],#[0x110747a3088421ce0474,0xf80218b8c2d1608439c0,0x710d0b80c30b8f0782b0,0x1c0c0561d0b801720290,0x850ba1217c0250706040,0xa0b7003c201095c00b07,0xe007078212b801c0d0a4,0x3802410882322b191221,0x45c0160a8be008438207,0x1e1491c011070412070,0xb84f810b108a4a2405f8,0x852e301c0bc01088050,0xe85e0084402a1d0b43e0,0x281c0ac3c0e13800f1d0,0x50f80221838160bf005a,0xd444584f810a143c1c24,0xc0098a262242b8013c58,0xd11148be005460551117,0x2d1428602bc045a28501,0x850505b801c128943e02,0x345f02142b1187c085c2,0xe08260b702141c16081,0xf0b43e042d1420282dc0,0x1416e007840222b80160,0x60e1a88064422b801e19,0x350b801e1a1106627030,0x288fa2703060e1988080,0x838200d44c1f001cc21d,0xe084311d081006c27003,0x428383613801b0e09c00,0x6c270038388c2821e0,0x284e15c00b068511d081],#[0xf00421c141d0a09f0024,0x1141c1b80210e060401,0xc60e7004220102408c27,0x986c503e1287c02583,0x1509c00992d142e1097c,0x3800f0e098425f00261b,0x808a0e0d8407f0038261,0x8204b808a0e0e1663413,0xc9046c25078013182cc6,0x42188e844823613801c1,0x3c00e11c0128703e0070,0x1f001c308e8426855184,0x707e008c3819509f846,0x210e0623a11208d84e0,0xc00988c525f002621138,0x3a58a4be004c4a209497,0xc97c009894413097801,0xe0626e0084382700421c,0x2ccbe1073802c1f80210,0x2d202ccbe00705a285c,0xb0743b1984c1450878,0x97c0130ec621a2842c2e,0xc50f802120240421895,0xa86cbe009481321d84c1,0x721f00422c104c124385,0x8508482361287c061038,0x99584c1f02824e13804b,0x4c212b801c104c080381,0x82700541c0f8584e0070,0x412b09c00f0d84e01283,0x88080361307c0070c262,0x60608883a10982e0c44],#[0x32408c13150e240d0701,0x8400ec40c84100387088,0x410ec4144903612410e2,0x200708300803864681a,0x5070646c287030409020,0x612151c20380ac40c840,0xa8381019191c85620824,0x42a8383070142c287020,0x447042a070a028123870,0xc4018084c200c0615038,0xc0411060430188302110,0xa430886160450a3085a1,0x410c212082d160883a20,0x8345a125c2c10540e10a,0x830150840186105b022,0x80c2a0e082a16082c13,0x3a1082383d0982210830,0x43a28306a1d14188e0ec,0x3a1460210c2487428a04,0x2c1243a1440c41206c24,0x707a1304443a16061610,0x41168b038390e8423104,0xb041198420218446a089,0xac21206c20810c225860,0x4119854103914611e0c2,0x4a8210580d410391450]]
def g247H8 := limbs80 #[#[0x60a000d0202002b0a00,0x4c4130a01190d003901,0x17000c06000504070010,0x680b29000a0200022a03,0x7cb92c000a26033c341d,0x335d497780007ba,0x6000e041f50001615da0,0x6572486db430000a39f0,0x2ae3800044eb245257d6,0xc23b000971000da853a3,0x6b45569310005a551efa,0xfaf11cf0b27274d8b9,0x6eade891dfb69d18a4f0,0xaae75c37c2f75806a49,0x650007403f131627738d,0x9a8458ad17c467f63235,0x68c9cad0961f000a44e5,0x53c05dd88d3627dd7167,0x7d1ae3ec86c63564708a,0x84abbcb9da2dd4b30dbb,0x313000000274000000,0x2f4c0000000000b00000,0xcb3510c6bc45000e5232,0x41e5e447a150003defa2,0xe2a9d4200083ccb85c13,0x10706f00096c00043df9,0x14f9f2f465b000ad4c5d,0xa4a34a431bb6705114,0xa5cf01b2000000041900,0x6ee51d60e54000dc9c62,0x10c0290000000001cfa,0x53f603000232b6855],#[0xedd0000007f2d12,0x3deab6dcd200005f1210,0x2761ce000b00e1df3657,0xd98e2c6630f25a6bde0e,0x8d8313341b22ef02f0ac,0x455000e2822b19]]
set_option maxRecDepth 16000 in
def g247D9 := limbs80 #[#[0xe6358fcfa1c87b758d60,0x2ac7e795163f3aa8b1ed,0x20ff2809079e5498f6eb,0x7dd63483fcb0241fe541,0xebaa417f5cd20fbcc690,0x4d30bfee4987f9504c2f,0x987dd634c3ef29a61f75,0x3df2a261ef55130fbcc6,0xf5d530bfee8985fd744c,0xec985fd764c2ffbaa617,0xcc3eeb1e61f754f30bfe,0x17f5d330f7ca9987bd54,0xf2c0a05fd76cc2febae6,0x63503eeb1a81ef50d40f,0xa81ef59140f7aa8a07de,0xbfae5a05fd76502feba,0xde63d03eeb1e81ef50f4,0xb2681ef55340bfae7a07,0x150bfaeda05fd75d03de,0x87dd63543bea9aa1fe58,0xfebb2a1df59550fbcc6a,0xdcd60dfac6b05ff72582,0x8b07be54583deaa2c17f,0xeffbaac1bf59560bfee,0x7fdc143bfaea21fdd631,0xaeaa1fde6350feeb1a87,0x390efeb84877fdd543bf,0x87ef95243f7aa921fdd6,0xbfaed21dfd7590efeba4,0xd6354effb92a77fdc153,0xb2a77fdd153fbcc6a9fd,0x53bfae129dff7654efeb],#[0xdfd7694efeba4a7f758e,0xeaa2c77fdc963bfee0b1,0x9563bfee8b1fbe5458fd,0xb1fdd7058effbaac7bf5,0xfefb92c7f75c963fbee0,0x75d163fb8e8b1fde5458,0xeab1fdf7458fef3a2c7f,0x98efeb84c7f7dd563fba,0x77f5d663bfae931fbe54,0xbce931fdd7498feeb84c,0x73596ffb82cbf75d663f,0x261ff59520ffac6905ff,0xffac8987fd544c3feb1,0xfd64cc3feaa661ff5953,0xa9a81ff54940ffacb987,0xb40ffacaa07fd63503fe,0x7fd63d03fea9e81ff54,0xfeb22a1ff58950ffacba,0x90d60ffa86b07fd52583,0x6b07fe53583fea9ac1ff,0x83feaa2c1ff9cd60ffae,0xff59543ffaca21ffd755,0xcc8a9ffd6454ffeb2c87,0x458ffeaa2c7ffdc963ff,0xcbffdd163ff8e8b1ffe5,0xff8e6b2fff70597feb82,0xf73597ff39acbff5cd65,0xc05c0114032006c0007f,0xe2033c0b4028408e01c,0x5c051412a045c10803d4,0xe077c1c406b418a05dc1,0x97424208bc21808141e],#[0xb8c2cc0ae42a20a3c274,0xc43620d2c3340c642fe0,0xc3f40f743c60e9c38c0d,0x47e118c44410c441a100,0x2c14444f6136c4bc1284,0x616fc5a81624572153c5,0x19e465e18fc61c17f45e,0xbec6e41b346ba1a8c694,0x3476e1d5c7401ca47121,0xc8101fd47d61eec7a41e,0x89e221c8742184846208,0x38248490623cc8d022e4,0xa271c9a82634972254c9,0x2964a4628cca2028149e,0xbfcae42b34ab62a7ca7c,0x84b822d6cb402ca4b162,0xcc343064bfe2f9cbc02e,0xcc232acc9431f4c62312,0x5434c4d1a340ccf03364,0x6373cdbc36a4d82358cd,0x39c4e5638cce183804de,0xcccf143bd4ebe3a8ce8c,0x84fc23e6cf843d94f4a3,0x8e60158d05640bd0083f,0x50989878016142828240,0x8b088642398028d600e0,0x9848780383420e21e015,0x80424e24221e013880a0,0x56207858195e0140c05,0x88502050e60158804518,0x5780502600993864f80,0x803c28589e201e0140c1],#[0x458083e260140c088435,0xa260138990158026342,0xc341489803c28b43414,0xb80264e18581e209e014,0x2d801e3c2408b6007898,0x3802634245e203e0140a,0x803c28440a26013898c3,0x45e205600a870c343289,0x5e260450e0a898014382,0x5600b070a1781143820,0xe0d178815802a1c309,0x9878042483040322056,0x116422808b60078d0a34,0x80162c3600d108634398,0x8d00e1e007920c1c861f,0x7920a0e0a861f80162c3,0x86063703804a28d61e00,0xd8a250380384a2e00e0d,0xf03802636241c0a2600,0x3804a342890e03601086,0x192c0e00e0d90241d870,0xe0e258703804a310032,0x3805030b0f220e601586,0xb40a260158e0d161d880,0x1586102d0d0380885030,0x839805640b160f220e60,0x3a16014120a5810883c1,0x910a4e080a4845803838,0x43c87804238484036009,0x3c28e6021958a1703094,0x2195900e35870980161e,0x8878044382160f408e60],#[0xb09a20560458c100c3c3,0xe0d8608061580162a30,0xb0d080827801c422e0,0x98d0a862d801e1c2856,0xb0a081417803c2818de0,0x715802c3c28c05600e0,0x78026242c221e005c50a,0x28201c30405600f0e141,0xe260070f8a083d80142c,0x70e10378885803c325,0x1489803c30b43612241e,0x7801c40b60078f082d0c,0xfa2600f0c100c0384890,0x50e0815802634204030,0xe0c142d8026242a260,0x104f0980382840322056,0x8221118dc2108e600510,0x3610dc2600e0d0980423,0xe1600e0c0b0980381e2a,0xc87850980383828201,0x563830b4220e015898c1,0x5076010898e2c0b0980,0x446844b0980384242321,0x804a30909a5a1e0128c1,0xa209e00710882c242697,0x1c423600e10889780264,0x600e102c8c8385088780,0x509803c28b2302a1e142,0x80342c54221e00d0a341,0x84030542600f0c101509,0x5600b0d08341509803c2,0x42600f0c870980149628],#[0xa823d0639805648b2305,0x403614241e0070e11085,0xc4924316881581123838,0xa5029345c5108e226021,0x403626009938c0e4f809,0x9940a0f068780484e30,0x20d88178114382a32260,0x8981143828441a1e0451,0x3c4e2a28e6045908a8c,0x4228d45e0108e0b081d8,0xc28de00e92888a398116,0x2a2600d8e0b081d80363,0x64d0a8a870239804a40,0xd0a8a118118563e01594,0x32342a2908e60110e921,0xa560120f083580423824,0xd60250e0d0d09801c502,0x8f0c20498044382a1c20,0x8878048424070d25600b,0xf120e6011160d0a8a0c3,0x108e0a4c888781171430,0xa4c0915802c3c3130960,0x140a084230a83a241e01,0xf068897803638c42c12,0x82c2108d876005098e2a,0x225e0098d8c0c0b80423,0x8a100b0897802636382c,0x7843980584a309e00710,0x58e6020968e2e2c823c9,0x8c06263d80944c48f0b2,0x23208ae142600e122c24,0xc8c24270895803c4930b],#[0xb2302e00e168c4c2]]
set_option maxRecDepth 16000 in
def g247H9 := limbs80 #[#[0x440420c020001b084143,0x20030030800001860868,0x490474470010c000338,0x8394200125c221180181,0x104004100a1c15c30410,0x10000200300e10814,0xed100006fa3545e36043,0x6198c4e864dd10fac38f,0x7c000fa1000138e00053,0x97999c0009cd3fb0000b,0xd2200000000000000000,0x66593449121e573d8003,0xe416508000000000,0x64e000,0xbd000534c56600,0x44e40d00,0x2159e40003f1652c0000,0x1defaa8cb3,0x3908044000e64a1257ea,0xe41000128c000000,0x3f86ee2a25373308000,0x1d3a703c7a21e3180e00,0x5e536f4040a0d25f0b4b,0xfd20000007a5400069ed,0x611800000000073c9f2d,0x167b6a80000000130000,0x1c543c1000000,0x1c0c000000000000000,0x1b79918c9e00000000,0x3b21e0000af7800105c0,0x687752f94a8956ca519b,0x40628d1af133bc17bcbf],#[0xc000000116d40a6834e4,0xb800307c00000068e68a,0xf800000018729b8e994e,0x2ad8d3099ee20d596fe8,0x1c8e00000025880000,0xf37a87800152d66ef304,0x8c8b8946289b7d062000,0x34640006eb4ed,0x1c80855c4801d200,0x68b93898000000000000,0x1c796a40000000000b,0x6440006abdfaa00021b8,0x729d9cb3c0713f143927,0x3388000000000000,0x79d4000000b31000000,0xd1bcee6a000241a00000,0x7a5337c02412a5500009,0xeee81000049b7,0xb03d90e240001cb0,0x4001ed5a4b130894758a,0xc0000000000000000296,0x10c7000000062b80005d,0xee36f4fa93cd8c707387,0xae14cc7d189bf82524db,0xe7de0f8003b76d35723e,0xc9025e6a8c405a820000,0x3eed5450001a2bd8615d,0xd08b1d344c30006ade15,0x1a3ef84000c2,0x770000000ce356b00000,0x1e970000c8a772000b,0x6e7bfc4000000d07cc38],#[0xc3326e3750b5c7ce000,0x5de3f14b5803a95a6ea,0xa1ee6d048538400000,0x9060001c22000e2400,0x85c0c26730005ab06ce0,0x5c323b72c4d0d28b4a43,0x2374516000086c001,0xa1afac81b1a3f42a,0x53afc000000000000000,0x14f5534e1fa95b4b91b,0x3d000145e000b5373800,0x15a92fa3b180000007,0x1cc8000c219974,0x29b2000,0x404,0xc8998481fac4b4b80e00,0x26646800117d81534259,0x170000eb6f6780000014,0xc3b51850a0001003b387,0xa31442800000029aea3b,0x40000005d2800000085a,0x1e0a714800212,0x11119720002c5600000,0x6b3b4cacda00000000,0x7e3000053b4ba0,0xd2c00000000001350000,0x8dec70b10b2ef50ae000,0xf4f8001242000c92dd8,0x4c00101d71e800000000,0xeb000014c000000b6830,0x4]]
def g247D10 := limbs80 #[#[0x30ff4c3fd20f798fdd63,0xfd60ff543ff40ff503ff,0x4ffd53ff90ffd43ff10f,0x9003fd65ff98ffd63ff9,0x976d965451338c971482,0x5f1386d2311b328e90a1,0x61c1141200b0e1410900,0x4e52b502c544869e0092,0x143070c1418288a00c0,0x24f0d0c01640b890c0c,0x285051219b0300312142,0x64050278e0b890a00c25,0x802c50a1828286042405,0x3040430542720272a243,0x90604406887a00a2020,0x50e18282021e20380a,0x216104807080c0621a07,0x3c1a0c3341200a203438,0x60b0a08407007]]
def g247H10 := limbs80 #[#[0x3f000700070b0506054c,0xf001c133c23131c050d,0x1040430031e8539061c,0x2548431030006250001,0x4c0029de3b0c05022301,0xcec000c100703b010101,0x62b7950000610e4a8002,0xa8e0b45240dc174e8e66,0x9230ac27c4ba0ee2c2a4,0x38abc490522584f443e1,0x5b000000170629a00052,0x1ac0a469d0004a0d4602,0xf1d000000169c6264,0x50a84cf61c414e1448b4,0x80008850001aea000000,0x60000cba187f044288b0,0x43264923f1098eba9143,0x717000035d794bc557,0x6d448122d080000,0x82cb0cc0000659860000,0x2126663207e66ac01a69,0x6b4da4a1e5804bb1f781,0xc1b685a11ca0be7223,0x14d18bd0cec188db2180,0x679f3ef1f520500882ed,0xe72734491b05978b0001,0x2e8302a307b13e1fdc30,0xd37b0005a672ec437c84,0xbc93c000c7d00018e093,0xdea3f51ee2590f9144bc,0x8b19e4a5520362680010,0x8a17c44fbe0027d1a2a],#[0x20ecdf889c20cd00d82a,0x12cd498a374d542f5e5f,0x454bd86aaf266063d800,0x77eef54270b5925482c1,0x513548ba4bca7868f5e,0x15c00168ac0580038372,0xc228a5921e698c55c1ab,0xc0b42ffe6d51dfcf4a71,0x183453b8c34001a2b947,0xf649103f546fa471fa91,0xddc7a55088442fa595e0,0x93e0bdc7888bd859251e,0x681504212789b00fd31b,0x31469cc8e2c392436140,0x2c640001407a30c94c09,0x4a3ce26825a62698008,0x4e440a64a]]
def g247D11 (j : Nat) := if j=0 then 0x81840802ff else 0
def g247H11 := limbs80 #[#[0x6951e5592309cfd7038b,0x5f0e0014944001b3acb3,0x39b62282f70000021ce,0x286661d957fcc62d460,0x869f4345780604007400,0xe]]
def g247L : Nat → Packing
  | 5 => (1,6,6,0,0,0,0,g247D5)
  | 6 => (31,5,6,0,0,9,0,g247D6)
  | 7 => (121,4,6,0,0,13,0,g247D7)
  | 8 => (247,3,6,0,0,14,0,g247D8)
  | 9 => (163,2,6,0,0,14,0,g247D9)
  | 10 => (17,1,6,0,0,10,0,g247D10)
  | 11 => (1,0,6,0,0,0,0,g247D11)
  | _ => emptyPacking
def g247I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 2 0 4 0 0 g247H6
  | 7 => lookupWord 10 59 5 10 5 1 g247H7
  | 8 => lookupWord 44 223 8 12 7 1 g247H8
  | 9 => lookupWord 82 541 6 13 8 1 g247H9
  | 10 => lookupWord 57 263 8 13 8 1 g247H10
  | 11 => lookupWord 7 37 5 10 5 1 g247H11
  | _ => fun _ => none
def g247 : Forest := ⟨247,11,fun i => g247Y[i]?.getD (0,0),g247C,g247A,g247L,g247I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P5_0 : block g247 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g247B5 : block g247 5 0 1=true := g247P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P6_0 : block g247 6 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P6_2 : block g247 6 2 29=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g247B6 : block g247 6 0 31=true := (@block_merge g247 6 0 2 29 g247P6_0 g247P6_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P7_0 : block g247 7 0 44=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P7_44 : block g247 7 44 77=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g247B7 : block g247 7 0 121=true := (@block_merge g247 7 0 44 77 g247P7_0 g247P7_44)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P8_0 : block g247 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P8_1 : block g247 8 1 28=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P8_29 : block g247 8 29 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P8_125 : block g247 8 125 57=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P8_182 : block g247 8 182 65=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g247B8 : block g247 8 0 247=true := (@block_merge g247 8 0 29 218 (@block_merge g247 8 0 1 28 g247P8_0 g247P8_1) (@block_merge g247 8 29 96 122 g247P8_29 (@block_merge g247 8 125 57 65 g247P8_125 g247P8_182)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P9_0 : block g247 9 0 7=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P9_7 : block g247 9 7 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P9_103 : block g247 9 103 16=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P9_119 : block g247 9 119 44=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g247B9 : block g247 9 0 163=true := (@block_merge g247 9 0 103 60 (@block_merge g247 9 0 7 96 g247P9_0 g247P9_7) (@block_merge g247 9 103 16 44 g247P9_103 g247P9_119))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P10_0 : block g247 10 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P10_2 : block g247 10 2 15=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g247B10 : block g247 10 0 17=true := (@block_merge g247 10 0 2 15 g247P10_0 g247P10_2)
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
theorem low247 : Lower true (varsX 247) (graphGoal 247) 12 := lower_forest (g:=g247) (i:=0) (hints:=1049924) (before_sound K239 V239) g247G g247T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K247 := extendKnown K239 12 [(247,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V247 : Known true K247 := extend_ok (m:=247) V239 low247 (by decide +kernel)
def g251Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x664875b4205000000,0xff0000ff000000ffff])),(BitVec.ofNat 152 (word80 [0x40871a0201090909,0x9090909090909090909]))),((BitVec.ofNat 152 (word80 [0x6081068ee849000000,0xff0000ff0000ffff0000])),(BitVec.ofNat 152 (word80 [0x4081020ec801030303,0x3030303030303030303]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x3184858f9a20000ff,0xff000000ff])),(BitVec.ofNat 152 (word80 [0x2184040f882262626,0x26262626262626262626]))),((BitVec.ofNat 152 (word80 [0x4b78b000a4be000000,0xff00000000ffff00])),(BitVec.ofNat 152 (word80 [0x338200024bc949494,0x94949494949494949494]))),((BitVec.ofNat 152 (word80 [0xa422fe2403b000ff00,0xffff000000])),(BitVec.ofNat 152 (word80 [0xa422bc000330585858,0x58585858585858585858]))),((BitVec.ofNat 152 (word80 [0xbc0950031552ff0000,0xffffff0000000000])),(BitVec.ofNat 152 (word80 [0xac0050011142606060,0x60606060606060606060]))),((BitVec.ofNat 152 (word80 [0x919621a01a05ffffff,0xffff0000000000000000])),(BitVec.ofNat 152 (word80 [0x110400a00004808080,0x80808080808080808080]))),(0x0,0x0)]
def g251C : List ColumnInfo := [(16,0,235,0,11)]
def g251A : List (List Nat) := [[],[16,83]]
def g251D11 (j : Nat) := if j=0 then 0xff else 0
def g251L : Nat → Packing
  | 11 => (1,0,1,0,0,0,0,g251D11)
  | _ => emptyPacking
def g251I (_ _ : Nat) : Option (Nat × Nat) := none
def g251 : Forest := ⟨251,11,fun i => g251Y[i]?.getD (0,0),g251C,g251A,g251L,g251I⟩
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
  · exact (rfl : block g251 9 0 0 = true)
  · exact (rfl : block g251 10 0 0 = true)
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
def g253Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x92cb3890036e138300,0xfe0007f0003fff])),(BitVec.ofNat 152 (word80 [0x12093810022e000100,0xa142850a142850a14285]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x20c61cb70163ca910,0x7f0003f8001fc000])),(BitVec.ofNat 152 (word80 [0x20061c2701638a100,0x60c183060c183060c183]))),((BitVec.ofNat 152 (word80 [0xc7609c0845cc8f4c0,0x3f800000000fe0007f])),(BitVec.ofNat 152 (word80 [0x87601c0845008a4c2,0x44891224489122448912]))),((BitVec.ofNat 152 (word80 [0xc5b327deb8809a0c00,0x1fc0000003f80])),(BitVec.ofNat 152 (word80 [0xc5a201ceb8809a0c09,0x52a54a952a54a952a54a]))),((BitVec.ofNat 152 (word80 [0x10a99a2d2c92ec42a0,0x1fc0000000000fffc000])),(BitVec.ofNat 152 (word80 [0x10899a290880c44205,0x8b162c58b162c58b162c]))),((BitVec.ofNat 152 (word80 [0x6154172348210167df,0xe0000001fffff0000000])),(BitVec.ofNat 152 (word80 [0x2054062100000142d6,0xc183060c183060c1830]))),((BitVec.ofNat 152 (word80 [0x3f00c064938102186f,0xfffffffe000000000000])),(BitVec.ofNat 152 (word80 [0x50000040101021828,0x10204081020408102040]))),(0x0,0x0)]
def g253C : List ColumnInfo := [(16,0,237,0,11)]
def g253A : List (List Nat) := [[],[96,50]]
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
theorem g253G : graphValid g253 (boundsBefore K251) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low253 : Lower true (varsX 253) (graphGoal 253) 12 := lower_forest (g:=g253) (i:=0) (hints:=2098435) (before_sound K251 V251) g253G g253T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K253 := extendKnown K251 12 [(253,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V253 : Known true K253 := extend_ok (m:=253) V251 low253 (by decide +kernel)
def g254Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffb820e824037d258c,0x4a000000fc003f000fff])),(BitVec.ofNat 152 (word80 [0xa2800a804011d2400,0x4a041041041041041041]))),((BitVec.ofNat 152 (word80 [0x48453e101d177349,0x8100003f000fc003f000])),(BitVec.ofNat 152 (word80 [0x3308443e1001173309,0x810c30c30c30c30c30c3]))),((BitVec.ofNat 152 (word80 [0x39fb2e0660128523,0x2d000fc0000000fc0000])),(BitVec.ofNat 152 (word80 [0x5c39eb2e0600128501,0x2d2cb2cb2cb2cb2cb2cb]))),((BitVec.ofNat 152 (word80 [0xff94dc4d9eac4e9988,0x1000000003f00000003f])),(BitVec.ofNat 152 (word80 [0x60145c451a2c429988,0x109a69a69a69a69a69a6]))),((BitVec.ofNat 152 (word80 [0x612c2fa4a934e42,0x2003f000000000ffffc0])),(BitVec.ofNat 152 (word80 [0x80021040a84a804842,0x514514514514514514]))),((BitVec.ofNat 152 (word80 [0x8a90581d3a05810,0xbffc000003ffff000000])),(BitVec.ofNat 152 (word80 [0xa10081d2a04000,0x24618618618618618618]))),((BitVec.ofNat 152 (word80 [0x674430492480a0b5,0x54fffffffc0000000000])),(BitVec.ofNat 152 (word80 [0x44000040240000b4,0x10820820820820820820]))),(0x0,0x0)]
def g254C : List ColumnInfo := [(4,0,250,0,10)]
def g254A : List (List Nat) := [[]]
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
theorem low254 : Lower true (varsX 254) (graphGoal 254) 11 := lower_forest (g:=g254) (i:=0) (hints:=286348608) (before_sound K253 V253) g254G g254T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K254 := extendKnown K253 11 [(254,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V254 : Known true K254 := extend_ok (m:=254) V253 low254 (by decide +kernel)
def g255Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xff000000ff00,0xffff24860da9c9])),(BitVec.ofNat 152 (word80 [0x90909090909090909,0x909090909240204a889]))),((BitVec.ofNat 152 (word80 [0xff000000ff0000,0xffff00000100300e07])),(BitVec.ofNat 152 (word80 [0x30303030303030303,0x3030303030000100205]))),((BitVec.ofNat 152 (word80 [0xff000000ff000000,0xff00000000060042301b])),(BitVec.ofNat 152 (word80 [0x70707070707070707,0x707070707040000001b]))),((BitVec.ofNat 152 (word80 [0xff00000000000000ff,0xff0818004045])),(BitVec.ofNat 152 (word80 [0x262626262626262626,0x26262626260008000044]))),((BitVec.ofNat 152 (word80 [0xff00000000,0xffff0000618381b6])),(BitVec.ofNat 152 (word80 [0x949494949494949494,0x94949494940020830132]))),((BitVec.ofNat 152 (word80 [0xff,0xffff000000b07e03fe28])),(BitVec.ofNat 152 (word80 [0x585858585858585858,0x5858585858a07603fc20]))),((BitVec.ofNat 152 (word80 [0xffffffff00,0xc07ffc0000])),(BitVec.ofNat 152 (word80 [0x606060606060606060,0x6060606060805d680000]))),((BitVec.ofNat 152 (word80 [0xffffffff0000000000,0xff80000030])),(BitVec.ofNat 152 (word80 [0x808080808080808080,0x80808080805b80000000]))),(0x0,0x0)]
def g255C : List ColumnInfo := [(2,0,253,0,12),(4,0,251,0,12),(8,0,247,0,12),(16,0,239,0,12),(1,0,254,0,11),(20,0,235,0,11),(32,0,223,0,11),(64,0,191,0,11),(128,0,127,0,11),(5,0,250,0,10),(33,0,222,0,9),(72,0,183,0,9),(0,8,86,161,8),(0,16,172,67,8),(0,32,81,142,8),(17,0,238,0,8),(48,0,207,0,8),(65,0,190,0,8),(80,0,175,0,8),(96,0,159,0,8),(129,0,126,0,8),(144,0,111,0,8),(160,0,95,0,8),(192,0,63,0,8),(0,4,27,224,7),(1,8,86,160,7),(1,16,172,66,7),(2,16,172,65,7),(4,16,168,67,7),(4,32,81,138,7),(8,32,81,134,7),(64,16,172,3,7),(128,8,86,33,7),(128,32,81,14,7),(49,0,206,0,6),(64,4,27,160,6),(65,16,172,2,6),(81,0,174,0,6),(128,4,27,96,6),(129,8,86,32,6),(132,32,81,10,6),(97,0,158,0,5),(145,0,110,0,5),(161,0,86,0,5),(161,8,86,0,5),(192,4,27,32,5),(193,0,62,0,5),(208,0,47,0,5),(224,0,27,0,4),(224,4,27,0,4)]
def g255A : List (List Nat) := [[]]
def g255D7 := limbs80 #[#[0x42e2bf09a8e59765d150,0x160b89fc36a3965d9745,0x7458372669bb3655745c,0x75d160bcabc26d576641,0x61d74583666ecfb06958,0x9e985d160d98fb3ec9a5,0x5a7a6174582a6bf09b56,0xb8597905d170a99fc36d,0x6ecd85e41745c276af09,0x69bb3617905d170d5999,0x9bc065ba3615745c3366,0xa67f2196e8d855d170ad,0x4d8af86ec9a55d9805d2,0x5d352be5bb2695766017,0xd974c5aea9ec9a55d980,0x301802b2b70386e89955,0xe1c9b199813920d8c078,0x21c170404002725a41f9,0x2f18103718103,0x191c1]]
set_option maxRecDepth 16000 in
def g255D8 := limbs80 #[#[0xe8a859afb26a1765d150,0x55d170582ccfd9b50bb2,0x36dd2ae8b82c1766ecd9,0x6cd976e8d955c160b97,0x574582e75d934abb2e0b,0xd2aecba2c1b2e5d9a0e5,0xafb2695765d160b97760,0x582cddd834ac3ae8b05c,0xeba2c166bec9a561d74,0x3617905d170b33f66d2b,0x6ddd8350b2ae8b85d9bb,0xa2e136bec9a8595745c2,0xb955d170d33b0dd1b0ab,0xd8750cb2e8b84dbbb069,0x952f6daa95d9805d26dc,0x5d974c97f4cbb321c2ae,0x44caaecba55afb265590,0xeee5a65d170543657c37,0x50f87f2cd2aecba2a176,0xa2e0b078bda8e59765d1,0x9a55d970583e5cd332ab,0x9736abb320ba2c1f3aec,0x8b07cafb2695765d160f,0x61d74582eddd834ac3ae,0x66d2b0eba2c176bec9a5,0x79bbb0695875d160bb3f,0x74583cd7d934ac3ae8b0,0x3d30ba2c1e67ecda561d,0xba3e81985d560d37b6ad,0x833e7d1f44cc2eab067d,0xac3ac1af6e8fa0655875,0xe899561d60d3f74fd032],#[0xf7d3f44cab0eb06bcfa3,0x2e1a77e9fa3655875834,0x905d170fa730ab2f20ba,0xc2cbc82e8b85db9b8597,0xd6e65985e41745c2eddd,0xd170db734cc2f20ba2e1,0x6c2ae8b85dbbb561b905,0xe5ba3615745c36cecb74,0xbb7760cb30aba2e1b67,0x2e8b859bfb8659855d17,0xa5619745c2eddd834ac3,0x7d72bb2cac02e976bec9,0xba65bdba5db9560174e9,0xd9805d2ed7d934abb300,0xcd2aecc02e9e2fe19a55,0x5bea96957660174e97f2,0x55d2ed7d934abb700ba6,0xb20bb2e996f6e9766438,0xb2695905d974eb5f64ca,0x2ecfd9b4ac82ecba5daf,0xbb2e9b2fe1ba5641765d,0x89955d974d97f0dd032a,0xed870ccaaecba7caf86e,0x6d45303e429814c002e5,0x90e18cccbd8ab899884c,0x16d55894692c5179058f,0xdadce5c49badab994182,0x420a6035fc5f55ee5e1d,0xa5164fe4ba41e3562361,0x87e78a6ee67e63a5ca55,0x62ac6a56a129ce95e8ee,0xae5ae16dd2d36c6ebd2b],#[0x1ef12708b01afaaf3aec,0xfe17c01f4333972fb2b7,0xf06c50fe1ba1826f09b1,0x29f007c91d0cc66c7f81,0x20aa3f87c2b7188cfc18,0x7c32588dc6215f07e07c,0xc414c21c3fc1d8dc13e0,0x416d0ff0d84fc2f80448,0x49fc1f81f082a8f04ee3,0x18c27c2f83f006323b18,0x9856e37c205bf00629b7,0xe850177c2f83f005f0,0x87830bba1fc205b0b3e,0x7617c29d0ee37c10c1f0,0x83f006c2bf07e048a121,0x4f85f007d8c03f63fc2f,0x7c1f804ec6e8609b63f8,0x645cc5f0b49968685363,0x87d8d71fe0c15f85f00,0x43a91d8e33b847c1f81f,0x1928f4429da23e0fc0f8,0xc023a36c4f83f020afc2,0xa2d8521702dd0705fe17,0xbc307b1929fc262bf005,0xd6062584b8224c342863,0x782097088504e09c090,0xc106013c112614168267,0x6c281e17c281214b8c11,0x2e059f0818fc1170bdc,0x8203185d0b2e37c23823,0x78cf09e0870b8e17c105,0x18201db18201c0817001],#[0x450603b6304038101db,0x9ce11c109a50c578405,0x845057084504134a184,0x8c1bc762a13840467037,0xa5c60f610c608456c2d,0xd8c1821c2f852e308085,0x8214c2c8e0821044ba4e,0x98542b825182b8214c2b,0x25163820c0305480c2e8,0x2f852e3080870be14b8c,0x6188d194054319c0821c,0x3608530a60a53f0]]
def g255H8 := limbs80 #[#[0xf00000d800538000000a,0x3940000002864,0x1604080000000000000,0x800000090802d000e280,0x4b401c6a1003dce054]]
set_option maxRecDepth 16000 in
def g255D9 := limbs80 #[#[0x745c150f4e595745c150,0xe6e619745c150f4e695,0x9765c150f1e5d9655c15,0x50f0f5d9655d150e3e61,0x19765d150b4fe9d955d1,0x150ae7e8d985d150e2f6,0xe89985d950a6fe9d985d,0xc1608f7e8d985d9508fb,0xe699745c160e6ee15745,0x5d160e3e5db855c160f2,0xae659905d160f2e5d990,0x55d160b6ee9d905d160d,0xa6f69f855d160e2f5db8,0x985d160b2fe9d965d160,0xa6f69e985d160a6fe9d,0xb905d170b6e697905d17,0x70b6e69b905d170d6e65,0x81955d170b67e8d855d1,0x970b6ee81965d170b6ee,0xe1976601748f7e8d95e1,0x174d2fe597660174e2f,0xf5db905957496f69b976,0x59574f0f5d98559574d2,0xede859859574b4fe9d85,0x8595749ebe8998595749,0x96f69f985957496fe9d9,0x9761574d2fe597661574,0x496f69b976157496f683,0x3865d974b6be89955d97,0x74b2f697865d974b2f68,0x8995e017696f68397619,0x150f6e659745c1508fbe],#[0xe99745c150f6e699745c,0xd150f5e695765c150f6e,0xfe59765d150f4f695765,0x5d150e6f6a1765d150f2,0x6fe9d965d150beee8196,0x85d950afbe89985d950b,0xa7fe9d985d950af7e8d9,0x745c160f6e615745c160,0xf6ee95745c160f6e655,0xd855c160f3e5d9855c16,0x60bf6e8d955c160b7ee9,0x95765c160f3e5d9955c1,0x160f2f5d9855d160f3e6,0x683955d160e6f61d855d,0xd160f2f5db955d160bee,0xf61f955d160baf69b955,0x5d160cefa63955d160e6,0x2f695765d160aef6a395,0x75d160e6f695875d160f,0x9fee81985d560e6fe958,0x985d5609fbe89985d560,0x9fe683985d5609f7e8d,0xd76615609bf69b985d56,0x60c7fe5d8761560d3fe5,0x89955d960bbee81955d9,0xd60afee819561d60bbbe,0xe8d9561d60afbe899561,0xd170f6e597905d170af7,0xe61b905d170f6e617905,0x5d170f4f615655d170f6,0x6fea1655d170b6f6a165,0x55d170e6f619855d170b],#[0xe6fe1b955d170b6fea19,0x865d170b6f69b955d170,0xb6fe95965d170b6fe95,0x98559570b6fea1965d17,0x709fee819859570f1f5d,0x9d98595709fbe8998595,0x57097f69f985957097fe,0x61b9361570d775db9361,0xd970b7ee81955d970cf7,0xf5d96560174b7be89955,0x60174dafe596560174f2,0x6fe5f9560174d6fe5d65,0x560174d6f5db9560174d,0xd6faa576601749ef69b9,0x7659574f2f5d965e0174,0x4d6faa57661574f2f681,0x990e1574d6f5d990e157,0x74b6fe8176e15749efe9,0x55905d9749efe8196e15,0x974b6fe95905d974d6f6,0xe81955d974f2fe19905d,0xd974f6be89955d974b6f,0xfe5f9561974f2fe19955,0x61d659ef6839561974d6,0xfbe839261d65cfbe4b90,0x75d160afbe898560176c,0xbfbe89985d560f6f6958,0x985d560dfee81985d560,0xdf7e8d985d560dfbe89,0x99761560bfee81976156,0x60bf7e8d9761560bfbe8,0x819561d60fbbe89955d9],#[0xd60bfbe899561d60bfee,0xe819561d60bf7e8d9561,0x1d60efbe899561d60efe,0xfe9d9561d60ef7e8d956,0x5d170f6f659855d170e7,0x6f61b955d170f6fe5985,0x55d970f6f695865d170f,0xbfee819561970f7be899,0x9561970bfbe899561970,0x4f6f6957660174b7fe9d,0x990e1574f6f69576e017,0x74f6f68176e1574def69,0x95905d974def68196e15,0x176efbe898560176f6f6,0xe8d9560176bfbe899560,0x8000b7fe9d9560176bf7,0x21806e016204080ac01a,0xfe0ec835c0c402ce09e0,0xa166054c13d84aa11503,0x1d587001b2068618c05d,0x4508be21f083a1f90798,0x98a9a28e89f826889562,0x8c302f90ba22d80b1e2b,0xdee36b0d5633d8cbe31c,0x243f10f643be8e7c38c0,0x2477119044e90da42110,0x4f093764ca92d44a2123,0x6f157054414b05169418,0x797885c296be59a161c5,0x99c865f192662f18485f,0xbcc6db1b166b29a7e687,0x5277c9d6a73d9c8c70b1],#[0x68001faa7d01ee07a51e,0x87ea1ae85120ee828a05,0x223b28d722fc8a9a250,0x72606967253c939a4689,0x280a9ed274a9baa6b299,0xa2ca78299ea4d28e8a1d,0x6cb05aba2ad5aaeca9ba,0x4b81adb0b592cfab30ac,0xbe22f50bc62ed6baf2e8,0x1fb046c08affebf42fac,0xdb1bec5f3144c3e30b6c,0xb340cc4b2e4ca13238c7,0x4aed18b43ecff33b0ce0,0x8ad74358ed53351ed34b,0x81464d8e71fc1f0bc042,0x23c142bc0f08241ac306,0x550a71fc1f0bc008488,0xe24fc3f07c0f0a0a26c3,0xc3f050af0bc020170528,0xfc1f03c2a28904493923,0x3c2a28907c17a3b4324,0x628815410137c7087c1f,0xa181531f43087c1f0bc0,0xc207c723348f07c007e8,0xfc2f008d0f86e13c1f03,0x7c01c18d2347e1b84f0,0xf09112384d1f48f0c0cf,0x2090805414b0dc6f07c0,0xc21fc6412c3853c1f03c,0x8242016b1811f0fc0f07,0x90721fc6d0d17f07c0f0,0x90621c84d23c1f03c20],#[0x1f0891201503fc1f03c2,0xc6f08805815d0ec6f03c,0x824188ed0f87e13c1f02,0x3c2094505412f07c0f0,0x37c1f002ef088037c1f,0x6f07c2f00241bc6e1f84,0x1471fc1f0bc00687851c,0xa1471fc1f0bc00688f1a,0xfc7b1bc1f00271821f1,0xa2114b1bc1f0bc00906d,0x6087c6453c1b1fc2f001,0x81f1f47e23c3f07c0a28,0x81f23c625f44f07c0f0,0x946087c625f44f07c0f,0x1f0053260d857c1f03c2,0x241c2405414e0ec4f0bc,0x424164611c21f07c2f00,0x23c2f041a1bc1f0bc008,0x6b88f0bc00706d1c1be,0x7d1b47f07c2f001a1b47,0x645f46d1fc2f07c0068,0x8221c97d1bc1f0bc009,0x8424142183615f07c0f,0x4b1bc2f021727c1f0bc0,0xc0f081f20288582d617c,0x3c20906087c685dc4f07,0x7c0f08251a1771bc1f0,0xe22c6f0fc2f00783615f,0x471fc1f03c2c28cd1387,0x1a282e0861509017b0c1,0x52b0e1471fc1f03c2c28,0x1c7f07c0f0b0a1549084],#[0x2bc0f0bc10849084c385,0x87c1628905a14b1fc34,0x5e28805893d0ec7f03c2,0x21241731c21f07c0f085,0x2c436c7d0d8af03c2f04,0xac7d201af07c0f098a20,0x544df07c0f0852e28714,0x70423d23c3f03c2a2881,0x723348f03c3f068a2026,0x84f0d48f07c2f00770b4,0xd0a923c1f0bc00908e1b,0x56c3e1fc1f002c1e1464,0x42bc1f03c2154241dc28,0xaf07c2523c3f00112214,0xc1453c382bc2f00624e0,0x787b1819f07c0f0e1423,0x5bc161fc3f03c28289c4,0xc13c3f03c105c90ac141,0x1f0bc009077185624fc2,0xc1f0bc0090924d17a2bc,0x85509070b917a4d14a2b,0x85509080aac6f07c0f0,0x154241ec690d17f07c0f,0xf0855302fb1bc1f03c2,0x74519190f87b1b84f07c,0x84037c1f03c215480b91,0x2c6f07c0f08552886e1f,0x3c1e10b0bc2a64787e1,0xc493855c6d0c5605fc2f,0xe102ed0fc2f07c00b0a0,0x6f07c0f082e211a85dc6,0x84f0fc2f00715743891c],#[0xf48f0fc08b08d1b48f05,0x748f0fc02746707c208,0xf0bc01f8770b46e104cf,0x3f0bc01d84d23c1e1fc3,0xc8f0bc02187d23c1e13c,0xbc3f009d189784fc1f0c,0x90b80e25c94d1bc1f0,0x4748b1a13f0984f07c3f,0xb589b1bc3f0bc085c94,0x8b1bc1f0bc3f00a84f11,0xc2f0fc02c2e4440e4534,0x2ec440ed21c18b02db1b,0x34870899b1bc1f03c336,0x215262e1831103b17c5,0x1a840502171dc6f07c2f,0x2090771dc2857c1f002c,0xc20849051c6857c1f03c,0x4a05b430508af06c7f03,0xc4de1343b1fc1f03c208,0xfc1f0bc0450d3202734,0xd0dc7f07c00b080844dd,0x4f03c2141141c2e45ec2,0xc1f028af0a151c21f042,0xfc1057c0f0a8a211471f,0x7c0f0a14084a0bc5271,0xf098a1c50136c7d0dc6f,0x2450522215b1fc1087c0,0xc2084808615f1bc1f03c,0xbc0201405917f07c3f03,0x9e2346d1fc1613c3f0,0x21c1d1b8409b47f0fc2f,0xd1bc1d1f84f0fc2f008e],#[0x7d1bc3f0784f0bc02188,0x46f05c7f03c345096234,0x3c1f03c3c28c65d16867,0x12e65f166440e32e1945,0x52c685bc1f0984f0fc02,0xb6c6627c3f0bc085c94,0x3d13c1f03c207ca85b14,0xc0f081f210fe0c2125c5,0x3c243c843c46d1388f07,0x7d0f16c64550db1fc1f0,0xf07c0f082127c0f07c20,0xf0ac62853b19c745744,0x813b83835c7d1388f07c,0x21857c6f07c0f089743c,0xc97b1b44f07c2f011528,0x5fc0f0bc1d18b14c21e0,0x25c70ba1560c21710240,0x2054a08424f0bc1f0110,0xa83c53d1ac4f05c7f03c,0x4771f46f07c0f082a182,0xbc6d19c4f0497f0bc085,0xb13c13346713c1f0bc00,0x45a1454c17e0dc6f0bc0,0x6f03c2f0617084a0c42e,0xc0f08241c90236c4e0dc,0xbc1f02172c17b1915f07,0x21e0e160548d712c6f0,0x5ac6e0cc1f0bc0084302,0xb1053b1bc2f03c145488,0xc62bc1f03c2069121417,0x83835c4d1f88f07c0f0a,0xf48f0ec4f0bc0074713b],#[0x1f86d23c3f0bc00608e1,0x52617b1bc2f0fc031c4e,0x10b058b82da5b14c440e,0xbc11a56038285dc6709c,0x8418b050c42e0b029f0,0x8ba2910bc10b050c62ef,0x84c4c0ec283038294283,0xcc184c300f1303a29c2,0x7c53118bb4815140b911,0x7c11b17c53118bb48171,0x8c1b1870b82c03bc20c,0x30bc10b050c62e8b00ef,0xe0b00eb1bc2f0468b80e,0xd151a16149c7b0a8a142,0x468ad0c7859c7b1ac217,0x709c171890b917855146,0x10c040ac2708617850d3,0xc608511b19141021858c,0x19141021c5f14c46c6d1,0x435c6d11c114c708517b,0x671b447051a85462590f,0xb0325e151c2f3442a0c9,0x1c2a3442f0c2e250d1d1,0x103108617719c27042c,0x14c46c6d106a58c10383,0x717c5311b1b441821c5f,0x21452c645c408]]
def g255H9 := limbs80 #[#[0x101c108020208680dc00,0x83a01c627c90000003,0x800a2b888db4bf861c92,0x30000035000000f05916,0x11e8aa834698e18,0x1d2800001446610000,0x59f000000a4c80000a6e,0x127c20c849e40c001e6,0x94000aae8ebb37640000,0x17b910006b84800024fb,0x15529800000,0xa40000000000361b8d00,0x9a000000000cf6453116,0x80035cc3e5ab8525861a,0x2b362c61c8002164a14b,0x30405e6611dc8]]
set_option maxRecDepth 16000 in
def g255D10 := limbs80 #[#[0x7bf26c3aa1db9745c150,0x7cbb2e0b076e5d170582,0x7b0eba2c1cbd765d160e,0xfc32e8b876ee41745c33,0xaecb2ae95bf9760174cd,0xc82ecba56fe5d855d397,0x2ec32e9cbf865d974adf,0x2ae0a84fbe4987596b7f,0xcb82a1df9765c150fbcb,0xae8a87cf595745437f30,0xba2a1dbd765d150f9eca,0xcaa86ef6617454377b0c,0x2aa1b7d8759550f3ebb2,0xaa85dfe5d65542efb2eb,0x2a177f965d550dbec32e,0xa84ff661765435fb0cbb,0xa1bdf9361d509ffcbb0c,0x6fee15705827ff2cc3a,0x1bbf855d160fdcc82e8b,0x76f61d74583d7b2cba2c,0xbbe985d160ddecc2e8b0,0xff65f855835faedc2ac1,0xfd95e1d609ffcab0eb04,0xf615745c3b7acaba2e13,0xf955d170edecaae8b876,0x659745c3b7b0cba2e1db,0x7659570edfcb2e8b876f,0x5b855c2fbf26c2ae1cfd,0x5601749fecaf0cb84ff6,0x9805d3b7aecc02e97bf9,0x60174ddfc3300ba6ef61,0x805d3b7f2ec02e97bf96],#[0x174edebb700ba5ef657,0x55d2f7b2dc02e9bbd86e,0x574f9ec2acaba5efe416,0x5d2f7f30b2ae97bd9859,0x74edebb30aba5efe4185,0xd3b7f2ec2ae97bf96615,0x4edebb70aba5ef643855,0x3b7b20bb2e97bd96e157,0xbdfc830cba76f655765d,0xb7f2ec32e97bf9561974,0xdecaf0cba5ef643865d3,0xfaedc02cbb7d75e0165b,0xfc82eab2cff65f805975,0xf20c3acb7ef9261d65bb,0xc870eb2efbe49875967f,0x2dc02eb7df93601759fe,0x870cbadfbe49865d67fb,0x4c2aed3fd95e01769fec,0x2e0a84ff643855dafdf2,0xba2a1fbd965d150ffccb,0xeca87df65576543f7f2c,0x82c1ff9855c160dfecc2,0x8b07ef61574583ff32ab,0xac1f7d855d560fdfcaae,0xb05ffe6175582ffb30ba,0xc1bfd8761560f7ebb30a,0x7bf65576582fff2ec2a,0x1bfd9561d60bffcab0eb,0x7df615655c37ff2ac3ac,0x7ff9859570bfecc2cab8,0xff619855c3bfaecc2ae1,0xff9561970efecaaecb86],#[0xfe55805d3f7acac02e97,0xf9561974fdeb2f00ba7e,0xe4187597dfb20bb2cbfb,0x9061975dffc830eb2dff,0x55805db7fb0ac02ed7ff,0x261576bffc830abb5ffe,0xd85583ffb30baac1fef9,0x61970ffecab0eb07ff65,0xe0003ffb2ac02edffd95,0x8281aa054c0f3027004,0xf543870d2c2eb0a7424f,0xc856414584b611a041a0,0x74a1c386b7195c61b16,0x90322f887920d07e61e6,0xce2a00a3227b49962520,0x23108beb2e74b612c28a,0x3954de33654d4733c0ca,0x1590083e7cf3f3be8ea3,0x391e5461513743a50ad4,0x93b04dad3264b3d29349,0x56954914e8524543a4ff,0x225b5168f59295f356b9,0x7639d890609d7c75de57,0x6b11a7668a19e3663194,0x261c5c6ff1ba56da5b09,0xd9dd67621d4c7441cd47,0x9fe07e25f3b7bb5e8478,0x1bd8576121837208e80b,0xf48e2e33d8b0a2628852,0x3967a54793c24ab90e63,0x9ec675a9c326a398ea5e,0x682952a41289ba15a7f6],#[0x16b80ac82ac0a9ca9eea,0x3850a22cb8b162c13af,0xc1e042880ab0c29c7e0f,0xf038424243c0ce3d2387,0x1c3e114c30af1b0e14e0,0x212170a4138c4808f078,0xaa18578d840bf0781c21,0x530f84a1f1b8224e0708,0xc7e305383c0e105470b8,0x9025c663f0781c20a11,0x5c7e30342bc1e07081e4,0x1884a7c40bd1b85c1e01,0x9015e089381c2080c15c,0xa38901fc66270785c00b,0x488e37102fc1e07082,0x85c0238dc40685783c2e,0xe1028ae25203b878b70f,0x880a2398e93a470f83c0,0x1202e1463f0f83c0e142,0x28b820218fc3e0f03842,0x18691c9363d2383c0e12,0x1484e0f038421120c1fa,0xa920494363f0781c2c5,0x686c74570785c0109217,0x8a470781c24507c60a83,0x202e136470f83c0e1428,0x88c251f86c8e0f03840e,0xa1e8e0e6470f81c2e0c2,0x201c3b2387c0e1704270,0xc2e0c2870570f83c0e15,0x70781c2108e0ea470f81,0x9c3e0f03840e208fc345],#[0x370f83c2e03209a3d230,0x1dc3e070456383a8f84c,0xa470f83c0e131c885008,0x18dc3e07078411201d84,0x90ad2383c0e109060a52,0x541b436352381c1e1244,0x848405691c1e07084830,0x206922e0bf1829c1e070,0x34a10a1b0f84a470781c,0xa1a8748c3e1383c0e10,0x2c116470f81c1e142881,0xc3e1191c3e0707854624,0xb0948e1f0781c207100e,0x7c270e91c1e07081c431,0x858f846370781c212198,0x43e0f005840542943698,0x70781c21212166330b8f,0x1c20aa2878a042108463,0x270781c20a1514e3f078,0x81c20d162e0bb1e87c61,0x2228128450f8c84e0b1f,0x898a31f8dc10af038424,0x8528530bf0f83c0e142,0xa8c471e8dc1e1f004e3,0xc245100ec262387c1e07,0xf0842503b1147e1f0781,0xe5c541b836371e89c0e0,0xd118323f1b8344e07083,0x8e0b1f8144e103474b83,0xf9344e0f0384150f8d8,0xc71083c8d44c470781c2,0x1120e15e370781c20787],#[0xb8024202044e0f03842,0xc00a86864bd138dc10af,0xf0785c00a868963f0785,0x9c2e0f00a64884244663,0x17004224182b83126218,0x8f88e1707801a1c8fc1e,0xc451a8fc2e0f00343d1a,0x21210a362383c0e10907,0x74b8411047a370785c01,0xd0e10a362383c2e0090,0x38415202a1fe0f038410,0x2e005491571d8946e0f0,0x2a440d2fc463d1b83c,0xc10b942f63f128dc1e17,0x962e0a31307c61270385,0xb14f89836370b81c10b,0xa8f88e0f03841a246221,0x4a3f0785c01094210911,0xb80120d0f1506e0d8dc,0xc1e0057841f242bc6e0f,0xf038421120e210791989,0x9c3e17078013202047e0,0x270f85c1e004c80a3228,0x89c3e170780131c28c8a,0x6261f87c1e1702905322,0xe91c2e007626303a0c91,0x7a461b87c1e1701884f0,0x70f48e1f0b801d281d8,0x48e0f0384131a2d86e20,0x61a89c3e07043d161b87,0x3b161a89c3e1707801,0xc3e070784161a8fc3e17],#[0xe238744e1707800e228f,0xd13e251b87c2e045cac3,0x470f83c0e15188168a22,0x83c3e0708290a2c1d87c,0xe16283440b8421708b1f,0x3858a2a9021a431f83c0,0x2e0a2842490c42c7e0f0,0x78421202c13a3f0f81c,0xc0a4044a1651d15c3e07,0xb0814c501493e0f0b87,0x241e220a617070fc3e0,0x115448324d15c1a470b8,0x87c2e052122531b83c0e,0xe07092248a4ac1305707,0x8ac9120522e1652383c3,0x64044a1203b83c3e070,0x28d14a5c270ae0f0b87c,0xa44c1c11e0b2381c3e14,0x81c3e13205240b852974,0xe1f0383840b961305707,0x3842e1c6311099598dc2,0x1e070f8460398dc3e0f0,0xf17888385d84a431859c,0x21241cc6e0f0f81c2170,0x92160a02a8fc3e0f0384,0x1394f0947e1f0781c210,0x61221e0f0f81c229a507,0xb4b85a8546e0b1f87c01,0x441d0aa131f83c3e00b0,0xc2e1f0383840b962e4ba,0x70843142063140b318a7,0x3c0e107c96351f87c1e0],#[0x7083e3884a6c6c45138,0x83c2e0454a6362289c1e,0xe106878194c42c663d13,0x785860b96c6c47068fc0,0xe22262e0888589c3e070,0x388c3d2387c1e0709880,0xe230f48e1f0989c0e08,0xd10ec451f87c0e170588,0x49c441c176370b81c3e0,0x383c28b8848188b92d14,0x2e1f078117298d44e1f0,0x423028431689d1989c,0x2c1e2d13e21068dc3e17,0x8a45840c45cc2608a41c,0xd11160e2e8983a8cc260,0x13062853285317613045,0x584a20562710c5e22c66,0x188862f1161304]]
def g255H10 := limbs80 #[#[0x4340003484117040040,0x1015440000810432851,0xb8308a1830935c000208,0x620cc2c03769ad9d4044,0xea79024240038d4d5981,0x86a09d8ed6e858003627,0xaa8001c3853f6439e89,0xe5d1c4ce4001dff64c00,0xdce842456178cc5b6e8f,0x28a80018e8003cc78,0x250000d10dd3c3ccbc22,0x4ca60001dac1bbcb051d,0x149022ce75e56d76d071,0x2140000d5400000000,0x30d37219c0ac18e4b15c,0x2896d44001d7c8985712,0x3589aad81000000108,0x3990000000002580000,0x28ec001a648b40000000,0x1a9c00111953326800,0x40ec480028c8c22c40,0x69ec0008d2060cbb8508,0x8d80015be52ac545518a,0x3b9e34fae34000000002,0xc84c0004700031d74e3a,0xe2bc84e049c8000288d2,0xa127e5cfcf049d5f5162,0xbd94a701b2d3b8fe8764,0x8c0000035e5e6c867d7,0x259f3a139a121d0450c0,0xf85e9f8c7c00248a1a49,0x114000000002e804ae06],#[0x6681c06800167800563d,0xbda80030f707bddad22d,0x59b9c2d09a90000a01e5,0xdc33148001694003968,0x2ddd2a3c281]]
def g255D11 := limbs80 #[#[0x5c150dbd765d36f5d170,0x543df59550fbd74543fe,0xbfd87542ff61950f7d75,0xe1560fbd74583fe5c160,0x582ff61d60efd76582ff,0xdfd765c2ffe1570bff87,0xe0174fbd805d2ffe1970,0x5d3ef61574fbd655d3ef,0xfbf865d3ef61974fbf85,0x5d965f7d75596ffe0165,0x5d6ffe1d65bfd87597bf,0xbff805daffe1975bff80,0x5d560ffd76542ffe1576,0x5c3ff61d60ffd85583ff,0xffd865c3ff61570ffd65,0x60175ffd87597ff60165,0x5dbff60176ffd865d7ff,0x1280e209c04e000ffd85,0x4a30c2b626820a1b416e,0x44fe4c04724343f63983,0x7286e268c64e5f859a55,0x328f48b68788127bc766,0xcb06ab0a629f49ae9709,0xd50cfacacc56c10bbab6,0x510f1f1b070213089da6,0x1783c6c447c2c1c02420,0x31c51230f03070828808,0x2881543c748c0c1c28a2,0xc20a20384d1f0f070308,0x7030828a0e1648c3c0c1,0x1c02c2c4c44851f230f0,0x20916140e48c70ac2c3c],#[0x242850471a1f07030f09,0x474315c68784c1c048c2,0x3c24824211b0f0307084,0x30b0cb1711c684c1c0c,0x111c5c50461f1a112307,0x30b045070648c1c0c2c3,0x7c1c0c3c284241d1b0f0,0x1f030f07085071714c64,0x15c6881f44c1c0c22819,0xf1f19130703085488347,0x153c4474688c2c1c02c0,0x12211b07030890a83152,0xc446c1c0c2151e0c551d,0x571a20691f070b00ac7,0x3c6c447c1c0c215220d1,0x482821130f070b004c70,0xa0e1613c487c3c2c0c1,0x845c4f121b0f0b03052,0x30e87c44886c3c2c0c13,0x11230f0b03044c717161,0x45870744c3c0c1c2161c,0x1c3c0171c111f0f030b0,0x1b0f0307085c70644c2c,0x174748c3c0c1c28a2011,0x8461d1a11230f030708d,0xac1c3c2c011245a44395,0x2307030b0c44a2913c80,0xc1c3c0c22130b85c5319,0x304b0953141388468447,0x3c2142858510b1c2b0f0,0x4c8482e1711c647c1c0c,0xc10e1328442b0f070308],#[0x304b0917164448c3c2c0,0x10e1628585108283b0f0,0x85ca17441347c3c2c0c,0x172cb85047191307030f,0x31211613c446c2c3c0c1]]
def g255H11 := limbs80 #[#[0x3251f1d130e010000,0x36040501070424060d00,0x5e024045094989094788,0xed4a05d0000842090105,0xc09000d3ce3e86eb5cc1,0x8445a56cb06e78000f57,0x632100032768964875b7,0x126d62142e5ee7295,0x1f00086647c920f00681,0x2000e1300067be7a4167,0xc2f000777b50b5,0x46000161329d7d511a87,0x851580c000f4da6300ad,0x749c1a28b05125500073,0x2c000000325f0b03de23,0x361d53a2084331607711,0xe4f00034b17f236569a4,0x59000d7000051b541000,0xe685075e82b6da17637c,0x57e63942af4755883430,0x22e2e940288903c3156f,0x4973f5346a08076bd182,0x10522415404416524590,0x6400003092b08d38ae3b,0x2d79a3f94e786a1990f8,0xd8c001e10468d83b0d91,0x7680296772d24c107274,0xa32a2855fe1471cb358]]
def g255D12 := limbs80 #[#[0x5ffae1ff583fea87bd74,0x3a8f801ff5dbfebaffd6,0xd1044085048c4d11feba,0x13223c3810610a1c1c78,0x1c2248c88c1c241810e1,0xe0c2804948f184048302,0x1a1c08504927222070d0,0xc1c442810e0925a3c410,0xbc48]]
def g255H12 := limbs80 #[#[0x410c9f840066c0047000,0x84f0c003c600022a06a,0xb71ec47f20b00140000,0xb93cc2000d8238ddf87d,0x7001a500000b341e855c,0x9b44b6429001050014,0x20000000000001090000,0x30029a001e7e6c00dabd,0x7d440015bca9b4000036,0x687ac00622d]]
def g255D13 (j : Nat) := if j=0 then 0x81c6103001088ff else 0
def g255H13 := limbs80 #[#[0x800000000007b0000000,0x900030d7,0x4b200]]
def g255L : Nat → Packing
  | 7 => (17,6,6,0,0,8,0,g255D7)
  | 8 => (70,5,6,0,0,12,0,g255D8)
  | 9 => (172,4,6,0,0,14,0,g255D9)
  | 10 => (142,3,6,0,0,14,0,g255D10)
  | 11 => (46,2,6,0,0,12,0,g255D11)
  | 12 => (7,1,6,0,0,9,0,g255D12)
  | 13 => (1,0,6,0,0,0,0,g255D13)
  | _ => emptyPacking
def g255I : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 4 43 1 9 5 0 g255H8
  | 9 => lookupWord 17 107 5 11 7 0 g255H9
  | 10 => lookupWord 43 223 6 12 8 0 g255H10
  | 11 => lookupWord 35 163 8 12 8 0 g255H11
  | 12 => lookupWord 11 71 6 10 6 0 g255H12
  | 13 => lookupWord 1 29 0 7 3 0 g255H13
  | _ => fun _ => none
def g255 : Forest := ⟨255,13,fun i => g255Y[i]?.getD (0,0),g255C,g255A,g255L,g255I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P7_0 : block g255 7 0 17=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B7 : block g255 7 0 17=true := g255P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_0 : block g255 8 0 22=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_22 : block g255 8 22 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B8 : block g255 8 0 70=true := (@block_merge g255 8 0 22 48 g255P8_0 g255P8_22)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_0 : block g255 9 0 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_48 : block g255 9 48 90=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_138 : block g255 9 138 34=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B9 : block g255 9 0 172=true := (@block_merge g255 9 0 48 124 g255P9_0 (@block_merge g255 9 48 90 34 g255P9_48 g255P9_138))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_0 : block g255 10 0 15=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_15 : block g255 10 15 84=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_99 : block g255 10 99 38=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_137 : block g255 10 137 5=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B10 : block g255 10 0 142=true := (@block_merge g255 10 0 99 43 (@block_merge g255 10 0 15 84 g255P10_0 g255P10_15) (@block_merge g255 10 99 38 5 g255P10_99 g255P10_137))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_0 : block g255 11 0 2=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_2 : block g255 11 2 31=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_33 : block g255 11 33 13=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B11 : block g255 11 0 46=true := (@block_merge g255 11 0 2 44 g255P11_0 (@block_merge g255 11 2 31 13 g255P11_2 g255P11_33))
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

end PEqualNP.Outside.L_meta_35034

open PEqualNP.Outside.L_meta_35034 in
theorem PEqualNP.Outside.L_meta_35034 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o fit _ correct
  exact replaceShort g255R gates o fit correct

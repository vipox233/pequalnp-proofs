import PEqualNP.Defs

-- The two-mode live-state and cofactor checker follows L_meta_1674 and L_meta_670.
-- The graph, restrictions and all search certificates below are for L_meta_34948.

-- Shared forest and cofactor certificates from L_meta_1674 and PR 11111 for L_meta_1677.
-- The original credit line is retained below. The two root certificates here cover the unpinned graph.

-- The checker and the bound certificates are adapted from PEqualNP/Outside/L_meta_1667.lean (Apache-2.0).
-- Two modes: u=false are monotone runs (AND, OR); u=true are runs up to complement, where negation is free.
namespace PEqualNP.Outside.L_meta_34948
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
def graph : Sig := (BitVec.ofNat 512 (word80 [0xffffffff,0xfffffffffffffffffffe,0xfffafffffffeffffffee,0xfefefefefefcaa00ffff,0xffffffffffffffffffff,0xfffefffafffffffeffff,0xffeefefefefefefcaa00]))
def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 2 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 3 && x 6) || (x 4 && x 6) || (x 0 && x 7) || (x 2 && x 7) || (x 3 && x 7) || (x 5 && x 7) || (x 6 && x 7)
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
  (x 0 &&& x 3) ||| (x 1 &&& x 4) ||| (x 2 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 2 &&& x 5) ||| (x 0 &&& x 6) ||| (x 1 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 0 &&& x 7) ||| (x 2 &&& x 7) ||| (x 3 &&& x 7) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)
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
  (x 0 &&& x 3) ||| (x 1 &&& x 4) ||| (x 2 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 2 &&& x 5) ||| (x 0 &&& x 6) ||| (x 1 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 0 &&& x 7) ||| (x 2 &&& x 7) ||| (x 3 &&& x 7) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)
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



def target (x : Fin 8 → Bool) : Bool := decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
def smallCircuit : Circuit := ⟨[⟨.or,[0,2]⟩,⟨.or,[1,2]⟩,⟨.or,[1,3]⟩,⟨.or,[4,10]⟩,⟨.or,[4,5]⟩,⟨.or,[3,5]⟩,⟨.or,[6,13]⟩,⟨.or,[0,7]⟩,⟨.and,[12,9]⟩,⟨.and,[15,14]⟩,⟨.and,[6,11]⟩,⟨.and,[7,8]⟩,⟨.or,[16,17]⟩,⟨.or,[20,18]⟩,⟨.or,[21,19]⟩], 22⟩

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

def lowRow (i : Fin 8) : Row := Fin.ofNat 512 (1 <<< ([3, 4, 4, 0, 1, 0, 0, 0] : List Nat).getD i.val 0)
def highRow (i : Fin 8) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< ([3, 4, 4, 0, 1, 0, 0, 0] : List Nat).getD i.val 0))

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
def g73Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3ff63ff63ff63ff63f,0xf63ff63ff63ff63ff63f])),(BitVec.ofNat 152 (word80 [0x492049204920492049,0x20492049204920492049]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xc7fbc7fbc7fbc7fbc7,0xfbc7fbc7fbc7fbc7fbc7])),(BitVec.ofNat 152 (word80 [0x924092409240924092,0x40924092409240924092]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xf8fdf8fdf8fdf8fdf8,0xfdf8fdf8fdf8fdf8fdf8])),(BitVec.ofNat 152 (word80 [0x248124812481248124,0x81248124812481248124]))),(0x0,0x0),(0x0,0x0)]
def g73C : List ColumnInfo := []
def g73A : List (List Nat) := [[],[99],[48],[48,96],[96,48],[96]]
def g73D3 (j : Nat) := if j=0 then 0x7 else 0
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
theorem g73G : graphValid g73 (boundsBefore []) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low73 : Lower true (varsX 73) (graphGoal 73) 4 := lower_forest (g:=g73) (i:=0) (hints:=3) (before_sound [] baseKnown) g73G g73T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K73 := extendKnown [] 4 [(73,[]),(82,[16,67]),(137,[118]),(161,[83,67,118]),(164,[32,16,83,67,118]),(193,[99,67,84,117]),(200,[48,16,33,98,66,84,117])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V73 : Known true K73 := extend_ok (m:=73) baseKnown low73 (by decide +kernel)
def g43Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xe6de3fff03fff1ffe6,0xde3fff03fff1ffe6de3f])),(BitVec.ofNat 152 (word80 [0x648490a2850240206,0x48490a28502402064849]))),((BitVec.ofNat 152 (word80 [0x19e9c0fffc07fe3f19,0xe9c0fffc07fe3f19e9c0])),(BitVec.ofNat 152 (word80 [0x50e8db2c3161408450,0xe8db2c3161408450e8db]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xece607fffff8003fec,0xe607fffff8003fece607])),(BitVec.ofNat 152 (word80 [0x8a7b6b04185892808,0xa7b6b04185892808a7b6]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1b3df8ffffffffc01b,0x3df8ffffffffc01b3df8])),(BitVec.ofNat 152 (word80 [0x891524c08206003089,0x1524c082060030891524]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g43C : List ColumnInfo := []
def g43A : List (List Nat) := [[],[80,49]]
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
theorem g43G : graphValid g43 (boundsBefore K73) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low43 : Lower true (varsX 43) (graphGoal 43) 4 := lower_forest (g:=g43) (i:=0) (hints:=83) (before_sound K73 V73) g43G g43T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K43 := extendKnown K73 4 [(43,[]),(45,[33]),(51,[16,67]),(53,[32,16,67]),(85,[64,16,33,50,101]),(92,[96,33,16,65,84]),(101,[33,99,67]),(102,[16,32,99,67]),(113,[65,33,83,99]),(116,[64,81,32,99,33]),(149,[32,16,67,117,101]),(150,[32,115,67,84,101]),(156,[32,49,65,117,101]),(170,[112,32,66,100]),(178,[80,65,32,115,33,99]),(198,[112,32,50,67,101,84]),(240,[112,65,32,83,99,50])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V43 : Known true K43 := extend_ok (m:=43) V73 low43 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low54 : Lower true (varsX 54) (graphGoal 54) 3 := by
  have q := @lower_count true (vars 54) (graphGoal 54) (proper_of _ (by decide +kernel)) (graphPairs 54 1115200) (by decide +kernel)
  exact q
def K54 := extendKnown K43 3 [(54,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V54 : Known true K54 := extend_ok (m:=54) V43 low54 (by decide +kernel)
def g75Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfdf00fff81fc7e3ffb,0xe01fff03f8fc7ff7c03f])),(BitVec.ofNat 152 (word80 [0x45c09245142904808b,0x81248a28520901170249]))),((BitVec.ofNat 152 (word80 [0xe6a8703ffe007fc7cd,0x50e07ffc00ff8f9aa1c0])),(BitVec.ofNat 152 (word80 [0x96a9b6d618b228112d,0x536dac316450225aa6db]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfbb781ffffff8007f7,0x6f03ffffff000feede07])),(BitVec.ofNat 152 (word80 [0x235249820c0312204,0x6a49304180624408d492]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x64ffe3ffffffff80c,0x9ffc7ffffffff0193ff8])),(BitVec.ofNat 152 (word80 [0x249204100400400,0x4924082008008000924]))),(0x0,0x0),(0x0,0x0)]
def g75C : List ColumnInfo := [(2,0,73,0,4)]
def g75A : List (List Nat) := [[],[48]]
def g75D4 (j : Nat) := if j=0 then 0x1f else 0
def g75L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g75D4)
  | _ => emptyPacking
def g75I (_ _ : Nat) : Option (Nat × Nat) := none
def g75 : Forest := ⟨75,4,fun i => g75Y[i]?.getD (0,0),g75C,g75A,g75L,g75I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g75P4_0 : block g75 4 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g75B4 : block g75 4 0 1=true := g75P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g75T : checkedTables g75 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g75 0 0 0 = true)
  · exact (rfl : block g75 1 0 0 = true)
  · exact (rfl : block g75 2 0 0 = true)
  · exact (rfl : block g75 3 0 0 = true)
  · exact g75B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g75G : graphValid g75 (boundsBefore K54) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low75 : Lower true (varsX 75) (graphGoal 75) 5 := lower_forest (g:=g75) (i:=0) (hints:=99) (before_sound K54 V54) g75G g75T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K75 := extendKnown K54 5 [(75,[]),(83,[16,67]),(86,[16,32,99,67]),(89,[65,33]),(90,[16,48,32,66]),(105,[48,81,33,96,66]),(114,[64,81,32,99,49]),(141,[33,118]),(163,[115,67,84,101]),(166,[32,115,67,84,101]),(172,[32,49,81,65,118]),(180,[80,65,32,115,50,98]),(197,[33,99,67,84,117]),(209,[65,33,115,83]),(210,[16,112,32,67,50,83]),(216,[48,65,32,114,82]),(228,[32,97,83,65,116])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V75 : Known true K75 := extend_ok (m:=75) V54 low75 (by decide +kernel)
def g165Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfe7d01c7fc0fc7cfe7,0xd01c7fc0fc7cfe7d01c7])),(BitVec.ofNat 152 (word80 [0x51d124928a290a051,0xd124928a290a051d1249]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x3f8b8e38fff007f3f8,0xb8e38fff007f3f8b8e38])),(BitVec.ofNat 152 (word80 [0x884b924930c3210884,0xb924930c3210884b9249]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x3fe7703ffffff803fe,0x7703ffffff803fe7703f])),(BitVec.ofNat 152 (word80 [0x100024924104020100,0x2492410402010002492]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xc018ffc0fffffffc01,0x8ffc0fffffffc018ffc0])),(BitVec.ofNat 152 (word80 [0x200049248208040200,0x4924820804020004924]))),(0x0,0x0)]
def g165C : List ColumnInfo := [(1,0,164,0,4)]
def g165A : List (List Nat) := [[],[117],[32],[32,117]]
def g165D4 (j : Nat) := if j=0 then 0x1f else 0
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
theorem g165G : graphValid g165 (boundsBefore K75) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low165 : Lower true (varsX 165) (graphGoal 165) 5 := lower_forest (g:=g165) (i:=0) (hints:=1285) (before_sound K75 V75) g165G g165T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K165 := extendKnown K75 5 [(165,[]),(169,[48,82,32]),(225,[80,98,50,67])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V165 : Known true K165 := extend_ok (m:=165) V75 low165 (by decide +kernel)
def g201Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xdf7ec03c3ffe0fbefd,0x80787ffc1f7dfb00f0ff])),(BitVec.ofNat 152 (word80 [0x820404444444210408,0x8888888420810111111]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1fbf43c3c3fff03f7e,0x878787ffe07efd0f0f0f])),(BitVec.ofNat 152 (word80 [0x40808888888420810,0x11111110841020222222]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xe03fbc03fc3fffc07f,0x7807f87fff80fef00ff0])),(BitVec.ofNat 152 (word80 [0x81011111110841020,0x22222221082040444444]))),((BitVec.ofNat 152 (word80 [0xffc03ffc003fffff80,0x7ff8007fffff00fff000])),(BitVec.ofNat 152 (word80 [0x102022222221082040,0x44444442104080888888]))),(0x0,0x0)]
def g201C : List ColumnInfo := [(1,0,200,0,4),(8,0,193,0,4),(64,0,137,0,4),(128,0,73,0,4)]
def g201A : List (List Nat) := [[],[118],[99],[99,115],[115,99],[115],[48],[48,118],[48,96],[48,96,112],[48,112,96],[48,112],[96,48],[96,48,115],[96],[96,112],[96,115],[96,115,48],[112,48,99],[112,48],[112,96],[112],[112,99,48],[112,99]]
def g201D3 := limbs80 #[#[0x23ea6a1221e12148110,0x8028]]
def g201D4 := limbs80 #[#[0x2fd0910bd42443e48110,0x609085870]]
def g201H4 (j : Nat) := if j=0 then 0x37c0 else 0
def g201D5 (j : Nat) := if j=0 then 0xd1027d10 else 0
def g201H5 := limbs80 #[#[0xb20000000000000000,0xc500580017c8c003cc,0x688016100000]]
def g201D6 (j : Nat) := if j=0 then 0x3904f else 0
def g201H6 := limbs80 #[#[0x280000000,0x8800002c4000000000,0x582880000528]]
def g201L : Nat → Packing
  | 3 => (2,3,2,0,0,5,0,g201D3)
  | 4 => (3,2,2,0,0,5,0,g201D4)
  | 5 => (1,1,2,0,0,0,0,g201D5)
  | 6 => (1,0,2,0,0,0,0,g201D6)
  | _ => emptyPacking
def g201I : Nat → Nat → Option (Nat × Nat)
  | 4 => lookupWord 1 5 0 5 1 0 g201H4
  | 5 => lookupWord 2 23 0 9 2 3 g201H5
  | 6 => lookupWord 1 23 0 9 0 5 g201H6
  | _ => fun _ => none
def g201 : Forest := ⟨201,6,fun i => g201Y[i]?.getD (0,0),g201C,g201A,g201L,g201I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g201P3_0 : block g201 3 0 2=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g201B3 : block g201 3 0 2=true := g201P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g201P4_0 : block g201 4 0 3=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g201B4 : block g201 4 0 3=true := g201P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g201P5_0 : block g201 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g201B5 : block g201 5 0 1=true := g201P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g201P6_0 : block g201 6 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g201B6 : block g201 6 0 1=true := g201P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g201T : checkedTables g201 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g201 0 0 0 = true)
  · exact (rfl : block g201 1 0 0 = true)
  · exact (rfl : block g201 2 0 0 = true)
  · exact g201B3
  · exact g201B4
  · exact g201B5
  · exact g201B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g201G : graphValid g201 (boundsBefore K165) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low201 : Lower true (varsX 201) (graphGoal 201) 7 := lower_forest (g:=g201) (i:=0) (hints:=3) (before_sound K165 V165) g201G g201T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K201 := extendKnown K165 7 [(201,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V201 : Known true K201 := extend_ok (m:=201) V165 low201 (by decide +kernel)
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
theorem g47G : graphValid g47 (boundsBefore K201) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low47 : Lower true (varsX 47) (graphGoal 47) 5 := lower_forest (g:=g47) (i:=0) (hints:=1363) (before_sound K201 V201) g47G g47T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K47 := extendKnown K201 5 [(47,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V47 : Known true K47 := extend_ok (m:=47) V201 low47 (by decide +kernel)
def g55Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xe003ff80ffe03ffff0,0x1ff80ffc0009ede81c0])),(BitVec.ofNat 152 (word80 [0x45a8a51a2a458a12a2,0xd4251a148b009e8eb6db]))),((BitVec.ofNat 152 (word80 [0xfffc0000ffffc07fff,0xfe0000fffff8da218e07])),(BitVec.ofNat 152 (word80 [0x8130362c0c891304c0,0x98362c191248d2019249]))),((BitVec.ofNat 152 (word80 [0xffffffff0000007fff,0xffffff00000ff10e7038])),(BitVec.ofNat 152 (word80 [0x1c038300f0e1c0700,0xe038301e1c0ad10a1249]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x7fff,0xffffffffff99af6d003f])),(BitVec.ofNat 152 (word80 [0x1602c040b01020580b,0x14000a000112c646db6]))),((BitVec.ofNat 152 (word80 [0xffffffffffffff8000,0x6754f2ffc0])),(BitVec.ofNat 152 (word80 [0x18030000c00000600c,0x18040c0202500704924]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g55C : List ColumnInfo := [(2,0,53,0,4)]
def g55A : List (List Nat) := [[],[33]]
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
theorem low55 : Lower true (varsX 55) (graphGoal 55) 5 := lower_forest (g:=g55) (i:=0) (hints:=66629) (before_sound K47 V47) g55G g55T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K55 := extendKnown K47 5 [(55,[]),(103,[32,16,100])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V55 : Known true K55 := extend_ok (m:=55) V47 low55 (by decide +kernel)
def g59Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3fffffc07ffff800ff,0xfffc07fffff27a560f0f])),(BitVec.ofNat 152 (word80 [0x822810810004504a01,0x4008102201300a525555]))),((BitVec.ofNat 152 (word80 [0xc003ffff80ffffff00,0x1fffffff001dadf9f0f0])),(BitVec.ofNat 152 (word80 [0xb005000201600c05,0x8050000404102c993333]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffc000000ffffffff,0xe00007fffe67e88e000f])),(BitVec.ofNat 152 (word80 [0x24c2a61a34a98510a6,0x156165485047e08caaaa]))),((BitVec.ofNat 152 (word80 [0xffffffff,0xfffff800002697f400f0])),(BitVec.ofNat 152 (word80 [0x3703382c58ce0660c8,0x1982467098269364cccc]))),((BitVec.ofNat 152 (word80 [0xffffffffff00000000,0x19d530dff00])),(BitVec.ofNat 152 (word80 [0x3803c03060f00780f0,0x1e038780e08d51048888]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g59C : List ColumnInfo := []
def g59A : List (List Nat) := [[],[16,67]]
def g59D4 (j : Nat) := if j=0 then 0x1f else 0
def g59L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g59D4)
  | _ => emptyPacking
def g59I (_ _ : Nat) : Option (Nat × Nat) := none
def g59 : Forest := ⟨59,4,fun i => g59Y[i]?.getD (0,0),g59C,g59A,g59L,g59I⟩
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
theorem g59T : checkedTables g59 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g59 0 0 0 = true)
  · exact (rfl : block g59 1 0 0 = true)
  · exact (rfl : block g59 2 0 0 = true)
  · exact (rfl : block g59 3 0 0 = true)
  · exact g59B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59G : graphValid g59 (boundsBefore K55) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low59 : Lower true (varsX 59) (graphGoal 59) 5 := lower_forest (g:=g59) (i:=0) (hints:=65603) (before_sound K55 V55) g59G g59T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K59 := extendKnown K55 5 [(61,[33]),(110,[80,97,32,50,67,65]),(124,[96,33,16,84]),(151,[112,65,50,32,82,101])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V59 : Known true K59 := extend_ok (m:=59) V55 low59 (by decide +kernel)
def g87Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x7ff003ffffe03ffff0,0x1ff80ffc0069abc81c0])),(BitVec.ofNat 152 (word80 [0x12a5a94a2a458a12a2,0xd4251a148b029aacb6db]))),((BitVec.ofNat 152 (word80 [0x7ffffc00ffffc07fff,0xfe0000fffff8da038e07])),(BitVec.ofNat 152 (word80 [0x4c1306c0c891304c0,0x98362c19124892039249]))),((BitVec.ofNat 152 (word80 [0x7fffffff0000007fff,0xffffff00000ff10e0038])),(BitVec.ofNat 152 (word80 [0x4701c0708f0e1c4708,0xe138309e1c0fd10a5b6d]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x800000000000007fff,0xffffffffff99af6d703f])),(BitVec.ofNat 152 (word80 [0x180601803010201803,0x40002000102c242492]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffff8000,0x6754f2ffc0])),(BitVec.ofNat 152 (word80 [0x60080200c00000600c,0x18040c0202540504924]))),(0x0,0x0),(0x0,0x0)]
def g87C : List ColumnInfo := [(1,0,86,0,5)]
def g87A : List (List Nat) := [[],[32,100]]
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
theorem low87 : Lower true (varsX 87) (graphGoal 87) 6 := lower_forest (g:=g87) (i:=0) (hints:=66630) (before_sound K59 V59) g87G g87T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K87 := extendKnown K59 6 [(87,[]),(94,[32,48,100]),(121,[64,49,82]),(122,[48,65,82]),(174,[16,32,48,116,84,101]),(188,[48,81,66,118]),(199,[16,116,84]),(248,[64,49,82,16,113,33])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V87 : Known true K87 := extend_ok (m:=87) V59 low87 (by decide +kernel)
def g91Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffc01ff87fc3fff00,0xffff1ffed2e680007c1f])),(BitVec.ofNat 152 (word80 [0x222894451108808a4a,0xa02444252268a5294a5]))),((BitVec.ofNat 152 (word80 [0xffffe0007ffc3ffff,0xffffe11773400f83e0])),(BitVec.ofNat 152 (word80 [0x40b018162050082c0c,0x2c140089146346318c63]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffff80003ffff,0xff001ffce8f541f0001f])),(BitVec.ofNat 152 (word80 [0x84c120980261113010,0x30588900a8d154a5294a]))),((BitVec.ofNat 152 (word80 [0xf0000000000003ffff,0xffffe0005f98fe0003e0])),(BitVec.ofNat 152 (word80 [0x701c0e0438221c060,0x40600e104b9898c6318c]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffffffffc0000,0x3280bbffffc00])),(BitVec.ofNat 152 (word80 [0x80201000400020080,0x80801000000021084210]))),(0x0,0x0),(0x0,0x0)]
def g91C : List ColumnInfo := [(1,0,90,0,5),(2,0,89,0,5),(8,0,83,0,5),(16,0,75,0,5),(9,0,82,0,4),(18,0,73,0,4)]
def g91A : List (List Nat) := [[],[65],[16,67],[16,48,64],[48],[48,65],[64,16,49],[64,49]]
def g91D4 := limbs80 #[#[0x9bd89544426d6215110,0x31825f635474]]
def g91D5 := limbs80 #[#[0x7c54443f280885bd4940,0xfea8885f95110beaa221,0xbd4940bfa8a81fb40502,0xcc8d018160c02faa3a07,0x882188201141080d176b,0xc110204810001]]
def g91H5 := limbs80 #[#[0x900089000000f2,0xb100000058000000]]
def g91D6 := limbs80 #[#[0x540a0380ff40fd40fd10,0x3140cc503]]
def g91H6 := limbs80 #[#[0x314003c93040474d0583,0xdc312000000000000000,0x9019100000001c285,0x4000000000000003c600,0x40000047000000000048,0x96]]
def g91D7 (j : Nat) := if j=0 then 0x1605f else 0
def g91H7 := limbs80 #[#[0x81dd0500112d4c105822,0x54b90054481]]
def g91L : Nat → Packing
  | 4 => (3,3,3,0,0,4,0,g91D4)
  | 5 => (10,2,3,0,0,7,0,g91D5)
  | 6 => (3,1,3,0,0,6,0,g91D6)
  | 7 => (1,0,3,0,0,0,0,g91D7)
  | _ => emptyPacking
def g91I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 19 0 8 2 2 g91H5
  | 6 => lookupWord 4 41 2 10 4 2 g91H6
  | 7 => lookupWord 3 19 0 9 2 3 g91H7
  | _ => fun _ => none
def g91 : Forest := ⟨91,7,fun i => g91Y[i]?.getD (0,0),g91C,g91A,g91L,g91I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g91P4_0 : block g91 4 0 3=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g91B4 : block g91 4 0 3=true := g91P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g91P5_0 : block g91 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g91P5_1 : block g91 5 1 9=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g91B5 : block g91 5 0 10=true := (@block_merge g91 5 0 1 9 g91P5_0 g91P5_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g91P6_0 : block g91 6 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g91B6 : block g91 6 0 3=true := g91P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g91P7_0 : block g91 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g91B7 : block g91 7 0 1=true := g91P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g91T : checkedTables g91 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g91 0 0 0 = true)
  · exact (rfl : block g91 1 0 0 = true)
  · exact (rfl : block g91 2 0 0 = true)
  · exact (rfl : block g91 3 0 0 = true)
  · exact g91B4
  · exact g91B5
  · exact g91B6
  · exact g91B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g91G : graphValid g91 (boundsBefore K87) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low91 : Lower true (varsX 91) (graphGoal 91) 8 := lower_forest (g:=g91) (i:=0) (hints:=65603) (before_sound K87 V87) g91G g91T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K91 := extendKnown K87 8 [(91,[]),(211,[115,83]),(218,[16,48,32,66,114,82]),(236,[32,49,81,100,116])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V91 : Known true K91 := extend_ok (m:=91) V87 low91 (by decide +kernel)
def g93Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffc01ffc3fffffc01f,0xfff87fffd452a6007c1f])),(BitVec.ofNat 152 (word80 [0x228942288840228940,0xa01108824012a65294a5]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffe0003fe1ffffe0,0xfffffc01359fa0003e0])),(BitVec.ofNat 152 (word80 [0xb0190b102850b2192,0xc8a0410812593b39ce73]))),((BitVec.ofNat 152 (word80 [0xffffffffc001ffffff,0xf0007ffcefd1140f801f])),(BitVec.ofNat 152 (word80 [0x4c1204c013084c0203,0x2c21200ad4110a5294a]))),((BitVec.ofNat 152 (word80 [0x1ffffff,0xffff80004d2fe9f003e0])),(BitVec.ofNat 152 (word80 [0x701c07021c10700c04,0x3001c104d06c0c6318c]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffffffe000000,0x33aa61bfffc00])),(BitVec.ofNat 152 (word80 [0x802018002001803018,0xc04602112a009084210]))),(0x0,0x0),(0x0,0x0)]
def g93C : List ColumnInfo := [(0,4,73,16,5),(4,0,89,0,5),(1,0,92,0,4),(8,0,85,0,4),(16,4,73,0,4)]
def g93A : List (List Nat) := [[],[48]]
def g93D4 (j : Nat) := if j=0 then 0x5bd4940 else 0
def g93D5 := limbs80 #[#[0x8240d140ff40fd40fd20,0x2011]]
def g93H5 (j : Nat) := if j=0 then 0x7 else 0
def g93D6 (j : Nat) := if j=0 then 0x16a09f else 0
def g93H6 := limbs80 #[#[0x6003100000000001100,0x9c000050]]
def g93L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g93D4)
  | 5 => (3,1,3,0,0,5,0,g93D5)
  | 6 => (1,0,3,0,0,0,0,g93D6)
  | _ => emptyPacking
def g93I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 4 0 0 g93H5
  | 6 => lookupWord 1 19 0 7 2 1 g93H6
  | _ => fun _ => none
def g93 : Forest := ⟨93,6,fun i => g93Y[i]?.getD (0,0),g93C,g93A,g93L,g93I⟩
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
theorem g93P5_0 : block g93 5 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g93B5 : block g93 5 0 3=true := g93P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g93P6_0 : block g93 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g93B6 : block g93 6 0 1=true := g93P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g93T : checkedTables g93 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g93 0 0 0 = true)
  · exact (rfl : block g93 1 0 0 = true)
  · exact (rfl : block g93 2 0 0 = true)
  · exact (rfl : block g93 3 0 0 = true)
  · exact g93B4
  · exact g93B5
  · exact g93B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g93G : graphValid g93 (boundsBefore K91) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low93 : Lower true (varsX 93) (graphGoal 93) 7 := lower_forest (g:=g93) (i:=0) (hints:=132099) (before_sound K91 V91) g93G g93T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K93 := extendKnown K91 7 [(93,[]),(109,[48,96,84]),(157,[66,118]),(179,[33,65,115,83,101])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V93 : Known true K93 := extend_ok (m:=93) V91 low93 (by decide +kernel)
def g107Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xff007fe1ff0fffc03f,0xfff0fffff95e0200f0ff])),(BitVec.ofNat 152 (word80 [0xa0501440220028281,0x40220020980602111111]))),((BitVec.ofNat 152 (word80 [0xffff8001fff0ffffc0,0x1fff0ff01c35b90f0f00])),(BitVec.ofNat 152 (word80 [0x2c06058814020b0305,0x81402042183511333333]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffe0000ffffff,0xe0000fff23b566f0000f])),(BitVec.ofNat 152 (word80 [0xb028160058442c0406,0x5844280213164666666]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffff,0xfffff000134bf8000ff0])),(BitVec.ofNat 152 (word80 [0xc0b058116088b02828,0x16000b040348e8cccccc]))),((BitVec.ofNat 152 (word80 [0xffffffffffff000000,0xcea8c5fff000])),(BitVec.ofNat 152 (word80 [0xc060018000c03030,0x18088c08468880888888]))),(0x0,0x0),(0x0,0x0)]
def g107C : List ColumnInfo := [(2,0,105,0,5)]
def g107A : List (List Nat) := [[],[96,81]]
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
theorem g107G : graphValid g107 (boundsBefore K93) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low107 : Lower true (varsX 107) (graphGoal 107) 6 := lower_forest (g:=g107) (i:=0) (hints:=83) (before_sound K93 V93) g107G g107T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K107 := extendKnown K93 6 [(115,[16,67]),(118,[16,32,99,67]),(182,[32,115,67,84,101]),(213,[96,33,48,67,84,117]),(214,[96,33,16,49,67,117]),(220,[96,33,16,65,84,117]),(230,[112,32,50,67,101]),(242,[96,81,32,67,50,113,49]),(244,[112,65,32,83,99,50])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V107 : Known true K107 := extend_ok (m:=107) V93 low107 (by decide +kernel)
def g117Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xf003ff0ffffff003ff,0xff87ffc3545d520f83e0])),(BitVec.ofNat 152 (word80 [0xa0a80a209002a0a814,0x910008a445812318c63]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffc000ff87ffffc01,0xfff87ffcd372a6007c1f])),(BitVec.ofNat 152 (word80 [0xc0310c402120c43118,0x8201210052302694a529]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffff0007ffffffe,0x7ffcafd11df0001f])),(BitVec.ofNat 152 (word80 [0x2c05002c20b00c020,0x2c220a00a541186318c6]))),((BitVec.ofNat 152 (word80 [0x7fffffff,0xffff80004d2fe8007fe0])),(BitVec.ofNat 152 (word80 [0xb02608b044c090241,0x30004c100907c94a5294]))),((BitVec.ofNat 152 (word80 [0xffffffffff80000000,0x33aa61bff8000])),(BitVec.ofNat 152 (word80 [0xc03800c00700e0381,0xc04470211aa6018c6318]))),(0x0,0x0),(0x0,0x0)]
def g117C : List ColumnInfo := [(1,0,116,0,4),(4,0,113,0,4),(16,0,101,0,4),(32,0,85,0,4),(64,0,53,0,4)]
def g117A : List (List Nat) := [[],[66,101],[32,100],[32,96,64,84],[64,32,82,98],[64,82],[80,66,98,32],[80,98],[96,84],[96,82,66,64]]
def g117D4 (j : Nat) := if j=0 then 0x57d4d10 else 0
def g117D5 (j : Nat) := if j=0 then 0xc1a0fd30fd10 else 0
def g117H5 (j : Nat) := if j=0 then 0x90 else 0
def g117D6 (j : Nat) := if j=0 then 0x23440bf else 0
def g117H6 := limbs80 #[#[0x4a2200000039b0000000,0x0,0xeb5a100009300000017,0x6600]]
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
theorem g117G : graphValid g117 (boundsBefore K107) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low117 : Lower true (varsX 117) (graphGoal 117) 7 := lower_forest (g:=g117) (i:=0) (hints:=132101) (before_sound K107 V107) g117G g117T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K117 := extendKnown K107 7 [(117,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V117 : Known true K117 := extend_ok (m:=117) V107 low117 (by decide +kernel)
def g155Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xc00fff0ffffffc00ff,0xfff0fffeea3a5303f03f])),(BitVec.ofNat 152 (word80 [0x84a08a210802284a02,0x80220882200a53145145]))),((BitVec.ofNat 152 (word80 [0xfff0000ffc3fffff00,0x3fffffc009adfd000fc0])),(BitVec.ofNat 152 (word80 [0xc42c405090b10c4b,0x11404108092d994d34d3]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffff0003fffffff,0xc000fffd77e88afc003f])),(BitVec.ofNat 152 (word80 [0x90130026104c0100c,0x584120152a08828a28a]))),((BitVec.ofNat 152 (word80 [0x3fffffff,0xffff00012697f4000fc0])),(BitVec.ofNat 152 (word80 [0x2e09c08b8227026090,0x26009c11269264b2cb2c]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffc0000000,0x39d530dfff000])),(BitVec.ofNat 152 (word80 [0x300e000c00380380e0,0x3808e0208d5104c30c30]))),(0x0,0x0)]
def g155C : List ColumnInfo := [(0,2,137,16,5)]
def g155A : List (List Nat) := [[],[115],[65],[65,115],[48],[48,112],[48,65],[48,65,112],[112,48],[112],[112,65,48],[112,65]]
def g155D5 (j : Nat) := if j=0 then 0x3f else 0
def g155L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g155D5)
  | _ => emptyPacking
def g155I (_ _ : Nat) : Option (Nat × Nat) := none
def g155 : Forest := ⟨155,5,fun i => g155Y[i]?.getD (0,0),g155C,g155A,g155L,g155I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g155P5_0 : block g155 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g155B5 : block g155 5 0 1=true := g155P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g155T : checkedTables g155 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g155 0 0 0 = true)
  · exact (rfl : block g155 1 0 0 = true)
  · exact (rfl : block g155 2 0 0 = true)
  · exact (rfl : block g155 3 0 0 = true)
  · exact (rfl : block g155 4 0 0 = true)
  · exact g155B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g155G : graphValid g155 (boundsBefore K117) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low155 : Lower true (varsX 155) (graphGoal 155) 6 := lower_forest (g:=g155) (i:=0) (hints:=65603) (before_sound K117 V117) g155G g155T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K155 := extendKnown K117 6 [(155,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V155 : Known true K155 := extend_ok (m:=155) V117 low155 (by decide +kernel)
def g167Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffc01ff81ffffff00,0x3ff01ff80feae3c40e07])),(BitVec.ofNat 152 (word80 [0xa0a8d4253452502a1a,0x84a342916288e2c49249]))),((BitVec.ofNat 152 (word80 [0xffffe0001ff03ffff,0xc0001ffff0054bb40038])),(BitVec.ofNat 152 (word80 [0xc930993658649a4c93,0x26c5932244c54bb6db6d]))),((BitVec.ofNat 152 (word80 [0xffffffffe0003ffff,0xffffe00000196c9871c0])),(BitVec.ofNat 152 (word80 [0x1c0e0386078e0701c,0x70603c387086c989249]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xf0000000000003ffff,0xffffffffffe47e6381ff])),(BitVec.ofNat 152 (word80 [0x20100400080008020,0x8000400000000012492]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffffffffc0000,0x1b91bffe00])),(BitVec.ofNat 152 (word80 [0xc02018001000300c0,0x30081804081311224924]))),(0x0,0x0)]
def g167C : List ColumnInfo := [(1,0,166,0,5)]
def g167A : List (List Nat) := [[],[32]]
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
def K167 := extendKnown K155 6 [(167,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V167 : Known true K167 := extend_ok (m:=167) V155 low167 (by decide +kernel)
def g171Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffc03ff0fffffc03f,0xfff0fffff5560300f0ff])),(BitVec.ofNat 152 (word80 [0x2028280a2020028281,0x40220020900603111111]))),((BitVec.ofNat 152 (word80 [0xffffc000ff0ffffc0,0x1fff0ff014b579000f00])),(BitVec.ofNat 152 (word80 [0x48b0322c41428b2325,0x9140284214b551bbbbbb]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffff000ffffff,0xe0000fff2bb5260f000f])),(BitVec.ofNat 152 (word80 [0x82c140b005842c0406,0x58442802b9120666666]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xf00000000000ffffff,0xfffff000134bf8f00ff0])),(BitVec.ofNat 152 (word80 [0x30180c08608300808,0x6000304034828444444]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffff000000,0xcea8c5fff000])),(BitVec.ofNat 152 (word80 [0xc0203000800c03030,0x18088c084420c4888888]))),(0x0,0x0)]
def g171C : List ColumnInfo := [(0,2,137,32,5),(2,0,169,0,5),(8,0,163,0,5),(1,0,170,0,4),(32,2,137,0,4),(128,0,43,0,4)]
def g171A : List (List Nat) := [[],[112]]
def g171D4 (j : Nat) := if j=0 then 0x5bd4940 else 0
def g171D5 (j : Nat) := if j=0 then 0xc8404fd40 else 0
def g171H5 (j : Nat) := if j=0 then 0x30 else 0
def g171D6 (j : Nat) := if j=0 then 0x2b2a0bf else 0
def g171H6 (j : Nat) := if j=0 then 0xc else 0
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
theorem g171G : graphValid g171 (boundsBefore K167) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low171 : Lower true (varsX 171) (graphGoal 171) 7 := lower_forest (g:=g171) (i:=0) (hints:=83) (before_sound K167 V167) g171G g171T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K171 := extendKnown K167 7 [(171,[]),(181,[80,65,33,48,50]),(241,[65,33,83,99])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V171 : Known true K171 := extend_ok (m:=171) V167 low171 (by decide +kernel)
def g173Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfe1ff00ff87f87ffc0,0x7fff8fffd8b95000f0ff])),(BitVec.ofNat 152 (word80 [0x1440a0a05101100285,0x5012008488941111111]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1ffff0007ff87fff,0x807ff1fc2b1e600f0f00])),(BitVec.ofNat 152 (word80 [0x5882c0c1620a010b06,0x160a0411291e43333333]))),((BitVec.ofNat 152 (word80 [0x1fffffff80007fff,0xff8001ff941fb0f0000f])),(BitVec.ofNat 152 (word80 [0x610b0505802c222c08,0x182c48a01416b6666666]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffe000000000007fff,0xfffffe000be4bf000ff0])),(BitVec.ofNat 152 (word80 [0x800c06060430443010,0x203000c20260b4444444]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffff8000,0x6442cffff000])),(BitVec.ofNat 152 (word80 [0x1008080040004020,0x40400100000008888888]))),(0x0,0x0)]
def g173C : List ColumnInfo := [(1,0,172,0,5),(4,0,169,0,5),(8,0,165,0,5),(32,0,141,0,5)]
def g173A : List (List Nat) := [[],[80,50]]
def g173D6 (j : Nat) := if j=0 then 0x4e09f else 0
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
theorem g173G : graphValid g173 (boundsBefore K171) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low173 : Lower true (varsX 173) (graphGoal 173) 7 := lower_forest (g:=g173) (i:=0) (hints:=1283) (before_sound K171 V171) g173G g173T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K173 := extendKnown K171 7 [(173,[]),(229,[99,67])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V173 : Known true K173 := extend_ok (m:=173) V171 low173 (by decide +kernel)
def g203Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfe1ff01ff1ffffc03f,0xe1fe1fffd19d300f00ff])),(BitVec.ofNat 152 (word80 [0x1440a140a408028281,0x44044008018931111111]))),((BitVec.ofNat 152 (word80 [0x1fffe001fc7fffc0,0x1ffe1fc4d3aa0000f00])),(BitVec.ofNat 152 (word80 [0x5892c192c8514b2325,0x892805114d3aabbbbbbb]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1ffffffe007fffff,0xfe0001ffbe1b40f0f00f])),(BitVec.ofNat 152 (word80 [0x6103020300620c0406,0x3088203e1002222222]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffe0000000007fffff,0xfffffe000be08f00fff0])),(BitVec.ofNat 152 (word80 [0x800404040080100808,0x400040000004444444]))),((BitVec.ofNat 152 (word80 [0xffffffffffff800000,0x6446ffff0000])),(BitVec.ofNat 152 (word80 [0x1808180100603030,0x118111824046c8888888]))),(0x0,0x0)]
def g203C : List ColumnInfo := [(2,0,201,0,7)]
def g203A : List (List Nat) := [[],[115],[48],[48,112],[112,48],[112]]
def g203D7 (j : Nat) := if j=0 then 0x3f else 0
def g203L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g203D7)
  | _ => emptyPacking
def g203I (_ _ : Nat) : Option (Nat × Nat) := none
def g203 : Forest := ⟨203,7,fun i => g203Y[i]?.getD (0,0),g203C,g203A,g203L,g203I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g203P7_0 : block g203 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g203B7 : block g203 7 0 1=true := g203P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g203T : checkedTables g203 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g203 0 0 0 = true)
  · exact (rfl : block g203 1 0 0 = true)
  · exact (rfl : block g203 2 0 0 = true)
  · exact (rfl : block g203 3 0 0 = true)
  · exact (rfl : block g203 4 0 0 = true)
  · exact (rfl : block g203 5 0 0 = true)
  · exact (rfl : block g203 6 0 0 = true)
  · exact g203B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g203G : graphValid g203 (boundsBefore K173) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low203 : Lower true (varsX 203) (graphGoal 203) 8 := lower_forest (g:=g203) (i:=0) (hints:=99) (before_sound K173 V173) g203G g203T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K203 := extendKnown K173 8 [(203,[]),(205,[33,118]),(217,[65,33])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V203 : Known true K203 := extend_ok (m:=203) V173 low203 (by decide +kernel)
def g227Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfc3fe01ff0fffff00f,0xfff0fff0fe542f0071c7])),(BitVec.ofNat 152 (word80 [0x28814140a20400a0a0,0xa0220022081425049249]))),((BitVec.ofNat 152 (word80 [0x3fffe000fe1ffff0,0xfff0fff015971c00e38])),(BitVec.ofNat 152 (word80 [0x31218190c40850c8c8,0xc840284020587156db6d]))),(0x0,0x0),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x3fffffff001fffff,0xf0000ffff2a37683803f])),(BitVec.ofNat 152 (word80 [0x420a0a050050850101,0x284428002a102892492]))),((BitVec.ofNat 152 (word80 [0xffc0000000001fffff,0xfffff000013c8afc0fc0])),(BitVec.ofNat 152 (word80 [0x800c0c060861060202,0x300030441208a892492]))),((BitVec.ofNat 152 (word80 [0xffffffffffffe00000,0xce2917ff000])),(BitVec.ofNat 152 (word80 [0x3010180080180c0c,0xc088c08844210724924]))),(0x0,0x0)]
def g227C : List ColumnInfo := [(2,0,225,0,5)]
def g227A : List (List Nat) := [[],[101],[112],[112,101]]
def g227D5 (j : Nat) := if j=0 then 0x3f else 0
def g227L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g227D5)
  | _ => emptyPacking
def g227I (_ _ : Nat) : Option (Nat × Nat) := none
def g227 : Forest := ⟨227,5,fun i => g227Y[i]?.getD (0,0),g227C,g227A,g227L,g227I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g227P5_0 : block g227 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g227B5 : block g227 5 0 1=true := g227P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g227T : checkedTables g227 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g227 0 0 0 = true)
  · exact (rfl : block g227 1 0 0 = true)
  · exact (rfl : block g227 2 0 0 = true)
  · exact (rfl : block g227 3 0 0 = true)
  · exact (rfl : block g227 4 0 0 = true)
  · exact g227B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g227G : graphValid g227 (boundsBefore K203) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low227 : Lower true (varsX 227) (graphGoal 227) 6 := lower_forest (g:=g227) (i:=0) (hints:=85) (before_sound K203 V203) g227G g227T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K227 := extendKnown K203 6 [(227,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V227 : Known true K227 := extend_ok (m:=227) V203 low227 (by decide +kernel)
def g233Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x1fe3fc07f8ff1ffe0,0x7fff3fffd461000f0fff])),(BitVec.ofNat 152 (word80 [0x40400810100200041,0x2020020000011111111]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfe003fff800ffe1fff,0x80ffc7f1c7bc00f0f00f])),(BitVec.ofNat 152 (word80 [0x282885020a21404282,0x1414104406b422222222]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x3ffffff0001fff,0xff0007fe31b30f0000f0])),(BitVec.ofNat 152 (word80 [0xb0b116142c05848b04,0x1858a280b1b366666666]))),((BitVec.ofNat 152 (word80 [0xffffc0000000001fff,0xfffff8003bc8f000ff00])),(BitVec.ofNat 152 (word80 [0xc0c018183046090c08,0x20600309394844444444]))),((BitVec.ofNat 152 (word80 [0xffffffffffffffe000,0x2816ffff0000])),(BitVec.ofNat 152 (word80 [0x10020204008001010,0x40800400000088888888]))),(0x0,0x0)]
def g233C : List ColumnInfo := [(32,0,201,0,7)]
def g233A : List (List Nat) := [[],[99],[112],[112,99]]
def g233D7 (j : Nat) := if j=0 then 0x3f else 0
def g233L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g233D7)
  | _ => emptyPacking
def g233I (_ _ : Nat) : Option (Nat × Nat) := none
def g233 : Forest := ⟨233,7,fun i => g233Y[i]?.getD (0,0),g233C,g233A,g233L,g233I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g233P7_0 : block g233 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g233B7 : block g233 7 0 1=true := g233P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g233T : checkedTables g233 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g233 0 0 0 = true)
  · exact (rfl : block g233 1 0 0 = true)
  · exact (rfl : block g233 2 0 0 = true)
  · exact (rfl : block g233 3 0 0 = true)
  · exact (rfl : block g233 4 0 0 = true)
  · exact (rfl : block g233 5 0 0 = true)
  · exact (rfl : block g233 6 0 0 = true)
  · exact g233B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g233G : graphValid g233 (boundsBefore K227) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low233 : Lower true (varsX 233) (graphGoal 233) 8 := lower_forest (g:=g233) (i:=0) (hints:=3) (before_sound K227 V227) g233G g233T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K233 := extendKnown K227 8 [(233,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V233 : Known true K233 := extend_ok (m:=233) V227 low233 (by decide +kernel)
def g63Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xe000ffffffffffffff,0xff6b03babce14900f00f])),(BitVec.ofNat 152 (word80 [0x401604150212810a40,0x142a03aa8c8048555555]))),((BitVec.ofNat 152 (word80 [0xffffffff80003fffe0,0xb02dca6b93160f00f0])),(BitVec.ofNat 152 (word80 [0x80a400a600db004c80,0x66b005ca2a0116333333]))),((BitVec.ofNat 152 (word80 [0xffffffffc00000,0x9cd1cd842de2f00f00])),(BitVec.ofNat 152 (word80 [0x1380138009c006f00,0xb898c1cc8021c2333333]))),((BitVec.ofNat 152 (word80 [0xffffffffffffff,0xffa162d5b1393d00000f])),(BitVec.ofNat 152 (word80 [0xbc0a9c054e02a700a,0xc0816055313935aaaaaa]))),((BitVec.ofNat 152 (word80 [0xffff00000000000000,0x915e285ddcf0000ff0])),(BitVec.ofNat 152 (word80 [0x1200ce006700338013,0x11a2055dc20cccccc]))),(0x4ea977125e06fff000,(BitVec.ofNat 152 (word80 [0x1c00f00078003c001c,0x442811105e00888888]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g63C : List ColumnInfo := [(2,0,61,0,5)]
def g63A : List (List Nat) := [[],[33]]
def g63D5 (j : Nat) := if j=0 then 0x7f else 0
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
theorem g63G : graphValid g63 (boundsBefore K233) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low63 : Lower true (varsX 63) (graphGoal 63) 6 := lower_forest (g:=g63) (i:=0) (hints:=66627) (before_sound K233 V233) g63G g63T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K63 := extendKnown K233 6 [(63,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V63 : Known true K63 := extend_ok (m:=63) V233 low63 (by decide +kernel)
def g95Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfc00fffffffffffffe,0xcf0912f74a48000f801f])),(BitVec.ofNat 152 (word80 [0x481610542128429028,0x450812f642414a5294a5]))),((BitVec.ofNat 152 (word80 [0xfffffffe0003fff801,0x701535aec91001f003e0])),(BitVec.ofNat 152 (word80 [0x90a402980db01320cd,0x701130aa4910c6318c63]))),((BitVec.ofNat 152 (word80 [0xfffffffc000001,0x39c4f2135e8000007c00])),(BitVec.ofNat 152 (word80 [0xe13884e109c21bc171,0x3984f2035e04e739ce73]))),((BitVec.ofNat 152 (word80 [0xffffffffffffff,0x428bea0b89e83e00001f])),(BitVec.ofNat 152 (word80 [0x1c027004e009c0181,0x283a00989aa94a5294a]))),((BitVec.ofNat 152 (word80 [0xffff00000000000001,0x22fa117cb687c0007fe0])),(BitVec.ofNat 152 (word80 [0x38007000e00200,0x26a0154808318c6318c]))),(0x0,0x0),(0x9d26ecc07137ffff8000,(BitVec.ofNat 152 (word80 [0x200c0018003000400,0x88044c00300421084210]))),(0x0,0x0),(0x0,0x0)]
def g95C : List ColumnInfo := [(4,0,91,0,8)]
def g95A : List (List Nat) := [[],[48]]
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
theorem low95 : Lower true (varsX 95) (graphGoal 95) 9 := lower_forest (g:=g95) (i:=0) (hints:=66627) (before_sound K63 V63) g95G g95T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K95 := extendKnown K63 9 [(95,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V95 : Known true K95 := extend_ok (m:=95) V63 low95 (by decide +kernel)
def g111Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3ffffffffffffffff,0x451d37930c4801f003ff])),(BitVec.ofNat 152 (word80 [0x581400540128029029,0x40141692044042108421]))),((BitVec.ofNat 152 (word80 [0xfc00fffe0003fff800,0xfa255c2e0c903e007c00])),(BitVec.ofNat 152 (word80 [0x90a602980db01320cc,0xea055c220c80c6318c63]))),((BitVec.ofNat 152 (word80 [0xfffffffc000000,0x39c4d2d3ab80000f8000])),(BitVec.ofNat 152 (word80 [0xe13844e089c11bc170,0x3944d293a982d6b5ad6b]))),((BitVec.ofNat 152 (word80 [0xfffffffffffffe,0x428bca0bd9efc000001f])),(BitVec.ofNat 152 (word80 [0x1c017002e005c0180,0x2894809d9898c6318c6]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffff00000000000000,0x22fa317cb680000fffe0])),(BitVec.ofNat 152 (word80 [0x98013002600200,0xaa214c1205294a5294]))),((BitVec.ofNat 152 (word80 [1,0x9d26ecc07137fff00000])),(BitVec.ofNat 152 (word80 [0x200e001c003800400,0x1522a0402036318c6318]))),(0x0,0x0),(0x0,0x0)]
def g111C : List ColumnInfo := [(2,0,109,0,7)]
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
theorem low111 : Lower true (varsX 111) (graphGoal 111) 8 := lower_forest (g:=g111) (i:=0) (hints:=1363) (before_sound K95 V95) g111G g111T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K111 := extendKnown K95 8 [(111,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V111 : Known true K111 := extend_ok (m:=111) V95 low111 (by decide +kernel)
def g119Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfff0003ffe01fff00a,0x384d914ae3003e007c00])),(BitVec.ofNat 152 (word80 [0x12a05a80943405216a,0x104c9148e118c6318c63]))),((BitVec.ofNat 152 (word80 [0xffffffc00001fffff6,0xd7c804654907c00f801f])),(BitVec.ofNat 152 (word80 [0x4c01300d858064246,0x50c00045490842108421]))),((BitVec.ofNat 152 (word80 [0xfffffffffffe000001,0xd8e29299950001f003e0])),(BitVec.ofNat 152 (word80 [0x7041c10e060878380,0xd8e29089054a5294a529]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffffffffffff2,0x4fe683ab8f8000003ff])),(BitVec.ofNat 152 (word80 [0x580160050000280000,0x40c6032b0318c6318c6]))),((BitVec.ofNat 152 (word80 [1,0x1711a387760001fffc00])),(BitVec.ofNat 152 (word80 [0x600980260081300401,0x711220212a5294a5294]))),((BitVec.ofNat 152 (word80 [0xc,0xe9177e4005fffe000000])),(BitVec.ofNat 152 (word80 [0x800e00380101c00800,0xa9130e0004c6318c6318]))),(0x0,0x0),(0x0,0x0)]
def g119C : List ColumnInfo := [(2,0,117,0,7),(1,0,118,0,6),(4,0,115,0,6),(32,0,87,0,6),(5,0,114,0,5),(16,0,103,0,5),(33,0,86,0,5),(36,0,83,0,5),(64,0,55,0,5),(17,0,102,0,4),(18,0,101,0,4),(68,0,51,0,4)]
def g119A : List (List Nat) := [[],[32,100]]
def g119D4 := limbs80 #[#[0x5c45350f465517014d43,0x30d1554]]
def g119D5 := limbs80 #[#[0xeeab88a6a1dd97014d43,0x3e3aa829a87735c85350,0xe7db82caa1e5f65d4d4,0x809dee4b24a73ddc5655,0xaa479848c1]]
def g119H5 (j : Nat) := if j=0 then 0x2a011010 else 0
def g119D6 := limbs80 #[#[0xe58243bbd8943af59330,0x59053bd58453be58053b,0x4d30fe54130d7d4e53af,0x730f754f30bf59530f75,0x43bf58f50bfd8d50bf59,0x3f7d4d43f714d43fbd89,0xbfd9543bf59543ef5514,0xf59053bf59643f7d4e43,0x58a53bfd9153bfd8153b,0x1800bf59653bf59253bf,0x41147e391689c3c12060,0xe39198c05a2a1449c4b2,0x19f4ca59269046a1d087,0x48282148c03c01c01c0,0x10450481700f0,0x10031624430c10c10810,0x20400000030400c108]]
def g119H6 := limbs80 #[#[0x2,0x3e4000000000000c0,0x0,0x29ec9d4000000000004,0x0,0x0,0x4c000000023400000000,0x298000000,0x0,0x6800015000]]
def g119D7 := limbs80 #[#[0xd43ffa87f543fe61fd30,0x1fe53fea9ff14ffc87f,0x1604de5d26cf85d1f07c,0xa481854120628a821a09,0x28a829a0714a4820c2a0,0x282c061046b824641e06,0x20628245188]]
def g119H7 := limbs80 #[#[0x2239a000c10022a0905,0xf0026375c00003864480,0x3bd20495b95cbc00e0b0,0x80024d851ca00000b000,0xea0aae3000c14000025,0x95a5537661000351fdc0,0xc3800e2ff036d470034]]
def g119D8 (j : Nat) := if j=0 then 0x764013f else 0
def g119H8 := limbs80 #[#[0x1f1e4e171c0000,0x42000000000000000000,0xd0000040000005500003,0x80000048d32140000492,0x13000000000a,0x20c000,0x32200000000]]
def g119L : Nat → Packing
  | 4 => (2,4,4,0,0,3,0,g119D4)
  | 5 => (8,3,4,0,0,6,0,g119D5)
  | 6 => (28,2,4,0,0,9,0,g119D6)
  | 7 => (9,1,4,0,0,9,0,g119D7)
  | 8 => (1,0,4,0,0,0,0,g119D8)
  | _ => emptyPacking
def g119I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 11 0 6 1 1 g119H5
  | 6 => lookupWord 2 97 1 8 3 1 g119H6
  | 7 => lookupWord 9 53 4 10 5 1 g119H7
  | 8 => lookupWord 4 59 0 9 4 1 g119H8
  | _ => fun _ => none
def g119 : Forest := ⟨119,8,fun i => g119Y[i]?.getD (0,0),g119C,g119A,g119L,g119I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P4_0 : block g119 4 0 2=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g119B4 : block g119 4 0 2=true := g119P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P5_0 : block g119 5 0 8=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g119B5 : block g119 5 0 8=true := g119P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P6_0 : block g119 6 0 7=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P6_7 : block g119 6 7 21=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g119B6 : block g119 6 0 28=true := (@block_merge g119 6 0 7 21 g119P6_0 g119P6_7)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P7_0 : block g119 7 0 9=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g119B7 : block g119 7 0 9=true := g119P7_0
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
  · exact g119B4
  · exact g119B5
  · exact g119B6
  · exact g119B7
  · exact g119B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119G : graphValid g119 (boundsBefore K111) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low119 : Lower true (varsX 119) (graphGoal 119) 9 := lower_forest (g:=g119) (i:=0) (hints:=66629) (before_sound K111 V111) g119G g119T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K119 := extendKnown K111 9 [(119,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V119 : Known true K119 := extend_ok (m:=119) V111 low119 (by decide +kernel)
def g123Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x7fffffe01fffff7,0x22ca982eb80001f07c1f])),(BitVec.ofNat 152 (word80 [0x25002800404022003,0x2080180ca8294a5294a5]))),((BitVec.ofNat 152 (word80 [0xfff8003ffffffff00b,0x942915d9c2003e0f83e0])),(BitVec.ofNat 152 (word80 [0x600b002800004023,0x802815094018c6318c63]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffc00001fffffa,0xd9dc81211e07c000001f])),(BitVec.ofNat 152 (word80 [0x28814c0ab058548288,0x995c8121125294a5294a]))),((BitVec.ofNat 152 (word80 [0xfffffffffffe000008,0x4f46b1ab3f8000003e0])),(BitVec.ofNat 152 (word80 [0x3301900cc0906704c8,0x4d40a12b36318c6318c]))),((BitVec.ofNat 152 (word80 [9,0x1713a2877400000ffc00])),(BitVec.ofNat 152 (word80 [0xbc05e02f00e1780708,0x1713a28214c6318c6318]))),((BitVec.ofNat 152 (word80 [4,0xe9177e4005fffff00000])),(BitVec.ofNat 152 (word80 [0xc00600300101800804,0x40036040048421084210]))),(0x0,0x0),(0x0,0x0)]
def g123C : List ColumnInfo := [(32,0,91,0,8)]
def g123A : List (List Nat) := [[],[16,67]]
def g123D8 (j : Nat) := if j=0 then 0x7f else 0
def g123L : Nat → Packing
  | 8 => (1,0,1,0,0,0,0,g123D8)
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
theorem low123 : Lower true (varsX 123) (graphGoal 123) 9 := lower_forest (g:=g123) (i:=0) (hints:=65603) (before_sound K119 V119) g123G g123T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K123 := extendKnown K119 9 [(123,[]),(215,[112,65,50,32,82]),(238,[80,97,32,50,67,65,116]),(252,[96,33,16,84,113])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V123 : Known true K123 := extend_ok (m:=123) V119 low123 (by decide +kernel)
def g125Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3ffffffc03fffff72,0x28ca85467c003f03f03f])),(BitVec.ofNat 152 (word80 [0x2800a0008080220032,0x8000506385145145145]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfc000fffffffff00bd,0x44b71b85080000fc0fc0])),(BitVec.ofNat 152 (word80 [0x3102c405001004023c,0x4a711010934d34d34d3]))),((BitVec.ofNat 152 (word80 [0xfffff000003fffffad,0x9d88d210e40fc000003f])),(BitVec.ofNat 152 (word80 [0x405301560b05482885,0x1588d200c4a28a28a28a]))),((BitVec.ofNat 152 (word80 [0xffffffffffc0000080,0x4b05b7ecd3f000000fc0])),(BitVec.ofNat 152 (word80 [0x806401981206704c80,0x4b00a6c4d0c30c30c30c]))),((BitVec.ofNat 152 (word80 [0x91,0x75782c5b400000fff000])),(BitVec.ofNat 152 (word80 [0x27809e01c27807081,0x71582858428a28a28a28]))),((BitVec.ofNat 152 (word80 [0x4e,0x937660389bffff000000])),(BitVec.ofNat 152 (word80 [0x3800e002038008048,0x80760038030c30c30c30]))),(0x0,0x0),(0x0,0x0)]
def g125C : List ColumnInfo := [(8,0,117,0,7),(16,0,109,0,7),(32,0,93,0,7),(0,4,73,48,6),(4,0,121,0,6),(1,0,124,0,5),(64,0,61,0,5)]
def g125A : List (List Nat) := [[],[96,84]]
def g125D5 (j : Nat) := if j=0 then 0x4ef7259650 else 0
def g125D6 := limbs80 #[#[0xbd8950b758c50bb58850,0x59650fbd8950ded4250b,0x401813142f3185b400bf,0x1002628]]
def g125H6 (j : Nat) := if j=0 then 0xf else 0
def g125D7 := limbs80 #[#[0x47888807f943faa1fc50,0xa61474365a981d90ea61,0x190e]]
def g125H7 := limbs80 #[#[0x6400000000f1000000,0x0,0x0,0x0,0x120000000000,0x20000000,0x0,0x0,0x0,0xd300000000,0x690000,0xa50000]]
def g125D8 (j : Nat) := if j=0 then 0x468817f else 0
def g125H8 (j : Nat) := if j=0 then 0x30000000000d505300 else 0
def g125L : Nat → Packing
  | 5 => (1,3,3,0,0,0,0,g125D5)
  | 6 => (6,2,3,0,0,6,0,g125D6)
  | 7 => (3,1,3,0,0,7,0,g125D7)
  | 8 => (1,0,3,0,0,0,0,g125D8)
  | _ => emptyPacking
def g125I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 2 0 4 0 0 g125H6
  | 7 => lookupWord 1 113 0 8 3 1 g125H7
  | 8 => lookupWord 1 11 0 7 2 1 g125H8
  | _ => fun _ => none
def g125 : Forest := ⟨125,8,fun i => g125Y[i]?.getD (0,0),g125C,g125A,g125L,g125I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P5_0 : block g125 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g125B5 : block g125 5 0 1=true := g125P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P6_0 : block g125 6 0 4=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P6_4 : block g125 6 4 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g125B6 : block g125 6 0 6=true := (@block_merge g125 6 0 4 2 g125P6_0 g125P6_4)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P7_0 : block g125 7 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g125B7 : block g125 7 0 3=true := g125P7_0
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
  · exact (rfl : block g125 4 0 0 = true)
  · exact g125B5
  · exact g125B6
  · exact g125B7
  · exact g125B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125G : graphValid g125 (boundsBefore K123) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low125 : Lower true (varsX 125) (graphGoal 125) 9 := lower_forest (g:=g125) (i:=0) (hints:=132099) (before_sound K123 V123) g125G g125T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K125 := extendKnown K123 9 [(125,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V125 : Known true K125 := extend_ok (m:=125) V123 low125 (by decide +kernel)
def g126Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffc0007fffffff001f,0xff4f09067e04b00f0f0f])),(BitVec.ofNat 152 (word80 [0xa8035004a005202c0,0x53060806620481111111]))),((BitVec.ofNat 152 (word80 [0xffffff8000ffffffe0,0x1b4baf6011d2000f0f0])),(BitVec.ofNat 152 (word80 [0x131026206c40640480,0x99b408b6001c25555555]))),((BitVec.ofNat 152 (word80 [0xffffffffff00000000,0x777c2b265300f00000])),(BitVec.ofNat 152 (word80 [0x5c05380a7015782f05,0xe0577c2a261303333333]))),((BitVec.ofNat 152 (word80 [0xffffffffffffffffff,0xfc81261697b3df0000ff])),(BitVec.ofNat 152 (word80 [0x6006400c8019804809,0x12600958312222222]))),(0x45d5e0f96d0000ff00,(BitVec.ofNat 152 (word80 [0x8027804f009e00700e,0x41d54099610aaaaaaa]))),(0x33a4dd980e26fff0000,(BitVec.ofNat 152 (word80 [0x38007000e0008010,0x2801d100606ccccccc]))),(0x0,0x0),(0x0,0x0)]
def g126C : List ColumnInfo := [(4,0,122,0,6)]
def g126A : List (List Nat) := [[],[65,82]]
def g126D6 (j : Nat) := if j=0 then 0x7f else 0
def g126L : Nat → Packing
  | 6 => (1,0,1,0,0,0,0,g126D6)
  | _ => emptyPacking
def g126I (_ _ : Nat) : Option (Nat × Nat) := none
def g126 : Forest := ⟨126,6,fun i => g126Y[i]?.getD (0,0),g126C,g126A,g126L,g126I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6_0 : block g126 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g126B6 : block g126 6 0 1=true := g126P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126T : checkedTables g126 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g126 0 0 0 = true)
  · exact (rfl : block g126 1 0 0 = true)
  · exact (rfl : block g126 2 0 0 = true)
  · exact (rfl : block g126 3 0 0 = true)
  · exact (rfl : block g126 4 0 0 = true)
  · exact (rfl : block g126 5 0 0 = true)
  · exact g126B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126G : graphValid g126 (boundsBefore K125) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low126 : Lower true (varsX 126) (graphGoal 126) 7 := lower_forest (g:=g126) (i:=0) (hints:=17916992) (before_sound K125 V125) g126G g126T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K126 := extendKnown K125 7 [(126,[]),(190,[33,84,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V126 : Known true K126 := extend_ok (m:=126) V125 low126 (by decide +kernel)
def g175Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xf003ffffffffffffff,0xfe28e884bd89000f00ff])),(BitVec.ofNat 152 (word80 [0x20581400a804a01481,0x4e08a0808c0911111111]))),((BitVec.ofNat 152 (word80 [0xfffc00fffc000fffc0,0x7d10ea50cb300000f00])),(BitVec.ofNat 152 (word80 [0x4290a6853236c89906,0x67d10ea50c91bbbbbbbb]))),((BitVec.ofNat 152 (word80 [0xfffffff00000,0x1cf2190dad100f0f000])),(BitVec.ofNat 152 (word80 [0x84e13809c02700de0b,0x814b2180da9133333333]))),((BitVec.ofNat 152 (word80 [0xffffffffffff,0xf2153f483bb80f00000f])),(BitVec.ofNat 152 (word80 [0x701c02e00b802e00c,0x151d4033b066666666]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffff000000000000,0x116d0a38776f000fff0])),(BitVec.ofNat 152 (word80 [0x3000c0030010,0x45000016644444444]))),(0x0,0x0),(0xce9177e4005ffff0000,(BitVec.ofNat 152 (word80 [0x80200c003000c0020,0xa0023e000088888888]))),(0x0,0x0)]
def g175C : List ColumnInfo := [(2,0,173,0,7),(4,0,171,0,7),(0,2,141,32,6),(1,0,174,0,6),(8,0,167,0,6),(3,0,172,0,5),(4,2,137,32,5),(6,0,169,0,5),(9,0,166,0,5),(10,0,165,0,5),(32,0,141,0,5),(32,2,141,0,5),(128,0,47,0,5),(5,0,170,0,4),(36,0,137,0,4),(130,0,45,0,4),(132,0,43,0,4)]
def g175A : List (List Nat) := [[]]
def g175D4 := limbs80 #[#[0x50d40483625d54350120,0x482d86174154120d8b75,0xe1561541209e187d0550,0x54120f095450d50482d8,0x9e3855c3414827221d43,0x9956148239e1975d0520,0x5423561f63d0550c6775,0xe0976d07508e7825db41,0x597418e7825db53d0639,0xb19801955450e3960372,0x5c06550ec36086555143,0xe0217e1d6519543c5965,0x6aa4e9109e2d4e84d951,0x480fef1cb666c1,0x90100]]
def g175D5 := limbs80 #[#[0x6f0b8682907894350120,0xf52a8a024139dc965d0,0x82f5baa80905e9755012,0x20fc2a2a8241f8d05504,0x483f0b8aa0907e161541,0x120f96e6a8241f250d50,0x483b5aa2a0907695454,0x520bcaeba0a417add15,0x61482f3bb2a2905e576d,0x50d20bceeab0a41b9995,0x954483c6aa286907cb70,0x359520bd2e1aa2413bdd,0xd50502f4b84ca905cf7,0x7050d40e72a8a8281e65,0xd95435034eb2a86a079b,0xf73595409dee4b2a81a7,0x5d8f41542f8b8682a84d,0xf576d0550aeaeba0aa1b,0xb5d8d615436bb1aa2a84,0x4dc7650d50e3aa8a1aa1,0x1b55c7635426f3b286a8,0x857575d07509bae9b1aa,0xa1c755143d427abb683a,0xa0cef7259350d3ac8a1e,0xe833d5db53d067bbaac1,0x6a1ee772597419eee0b2,0x9a87675d35350ecfba2a,0xcaa1cfb7059543cbecba,0xaa28767dc15450e77b92,0xaa8a1f1c6555143f1ee4,0x432a87765c06550f8fb2,0x82caa1e5d6519543b9ae],#[0xcb32a8773dc96550eedb,0xb86c4aa4ef7259353cbe,0x580f00137dcd60d5276,0x1684f100390c82f0901d,0x2187f1e0751b86b1905d,0x2d8af2b0a52889b2508d,0x388df370d9358cf320bd,0x419033f0f53b8eb3a0e5,0x4891f471194490f43109,0x4e9374d1314b92b4a125,0x5795b561555494b5113d,0x5024857c01da96759161,0x3480804802115831409,0x920204402841b480e1d2,0x40083020c080480801a0,0x20201202015824808382,0x202c4081d1054409,0x80e102120800000000,0x18408000000,0x3102c40c58200000000]]
def g175H5 := limbs80 #[#[0x250039a00033,0x48d3ea426a58014e630,0xc2000240006860d8b0a0,0x12404b31d]]
def g175D6 := limbs80 #[#[0x9d0520fa54120fa50120,0x50d20f958520f954520f,0x8341b7d8d50e750d40f3,0x143bdd8151bd59741bd5,0x20fb55120bbd8954e755,0xfb59520fb59120fbd51,0xef55140fe54140fb9952,0xdd0550bfd9540bf59540,0x50d50fd58550fd54550f,0x5150df55150f7d8d50f7,0xf50fdd0750bfd9150dfd,0x41bf59350df55350f750,0x3fd54d51fdd4f41fd54f,0xef55143f7d4d43f754d4,0x758143bfd9543bf59543,0x59543f719543f7d8143f,0x9153f7d9543f799543f7,0x954bfd8154bf59353bfd,0x54bf58354bfd8d54fbd8,0xe07a0b00f411000bf58f,0x7c2b44e0921091dc3144,0x472895051e138c6acc81,0x4bbd66ab252ea0d37a4d,0xadc83836c2d359931e61,0x14c077e6f61e5bc5762e,0x5099cf34e58c818bf112,0x1589676c157cac351a92,0x890642a0c6e01018dc02,0xd58a1e40d5624141215,0x3c0184c3805c315241c1,0x23c58984505845280f0c,0x558782584130e016223c],#[0x20147205618340ac3403,0x910c086a2401901a911,0x820400208080801018b,0x140107c80a18f8880388,0x3841420610487803150e,0x50e14012182082020018,0x10120208004040070811,0x20200416102448050630,0x48044480406281000c18,0xa01050446890a0182234,0xc504448044480246890,0x10100184040400810100,0x202001800704b0c]]
def g175H6 := limbs80 #[#[0x9f2d50401c00441c0018,0xe001cd5ac60f07831ca9,0x3d77035806149fe2304,0x30b5896300020035e0,0x525d6cc42d911c2304ac,0x0,0x4200261000a86000d480,0xc2400186f548d11cb3d4,0x1da80000183ed871b026,0xbc4602b076d6e02278c9,0xa62104441898a0006815,0x774c880710417d27c004,0x96e0002331020005d899,0x34684100000000712e2,0x1164b896d500]]
def g175D7 := limbs80 #[#[0xd43faa8fdd07da41f510,0x87ff50fea87f503bc87d,0x3fea9fd54ffa9ff54ffa,0x439c8c0511f8b4420f00,0x1458482c4ea6ab015c9c,0x2884b16884a0c136b808,0x58212c810482384b1403,0x18230a8602063208482c,0x532084b20528286020c,0xb18a0a180c20630a8602,0x40e084c2c63040e084]]
def g175H7 := limbs80 #[#[0x800401000,0x8d5ec00005800c880000,0x134800a9,0x800f0800000000000000,0x78536d46002ce63000a0,0x5a800018000000000000,0x1559bc00,0x680000008500000,0x0,0x0,0x592001aa5a0004b,0x91000000000000000,0xed000d700000,0x6ba0900000,0x118,0x743100009a0079c00,0x1c78000000000,0x5054de2800c850600,0x1be0075e00000002ec00,0x3e60000000,0x0,0x2d801ee0000000000,0x800006ae000000000000,0x6580013358,0x24bf20000000000,0x2e40000002,0x83801fa80000]]
def g175D8 (j : Nat) := if j=0 then 0x5a02013f else 0
def g175H8 := limbs80 #[#[0x2d000000002143,0xb36e69c0000034c00000,0xa00000472c03c29801e,0x2080170000]]
def g175L : Nat → Packing
  | 4 => (19,4,5,0,0,7,0,g175D4)
  | 5 => (71,3,5,0,0,10,0,g175D5)
  | 6 => (55,2,5,0,0,11,0,g175D6)
  | 7 => (14,1,5,0,0,9,0,g175D7)
  | 8 => (1,0,5,0,0,0,0,g175D8)
  | _ => emptyPacking
def g175I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 4 29 3 9 5 0 g175H5
  | 6 => lookupWord 17 97 6 11 7 0 g175H6
  | 7 => lookupWord 13 211 3 10 6 0 g175H7
  | 8 => lookupWord 3 37 2 8 4 0 g175H8
  | _ => fun _ => none
def g175 : Forest := ⟨175,8,fun i => g175Y[i]?.getD (0,0),g175C,g175A,g175L,g175I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175P4_0 : block g175 4 0 19=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g175B4 : block g175 4 0 19=true := g175P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175P5_0 : block g175 5 0 3=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175P5_3 : block g175 5 3 68=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g175B5 : block g175 5 0 71=true := (@block_merge g175 5 0 3 68 g175P5_0 g175P5_3)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175P6_0 : block g175 6 0 13=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175P6_13 : block g175 6 13 42=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g175B6 : block g175 6 0 55=true := (@block_merge g175 6 0 13 42 g175P6_0 g175P6_13)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175P7_0 : block g175 7 0 6=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175P7_6 : block g175 7 6 8=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g175B7 : block g175 7 0 14=true := (@block_merge g175 7 0 6 8 g175P7_0 g175P7_6)
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
  · exact g175B4
  · exact g175B5
  · exact g175B6
  · exact g175B7
  · exact g175B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175G : graphValid g175 (boundsBefore K126) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low175 : Lower true (varsX 175) (graphGoal 175) 9 := lower_forest (g:=g175) (i:=0) (hints:=1363) (before_sound K126 V126) g175G g175T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K175 := extendKnown K126 9 [(175,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V175 : Known true K175 := extend_ok (m:=175) V126 low175 (by decide +kernel)
def g183Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfff0003ffe01fff00e,0x3848cd0ae3003e007c00])),(BitVec.ofNat 152 (word80 [0x12a05a80943405216e,0x1848c108e118c6318c63]))),((BitVec.ofNat 152 (word80 [0xffffffc00001fffff6,0xd6ce06254900000f801f])),(BitVec.ofNat 152 (word80 [0x4c41310d858864246,0xd0c40605494a5294a529]))),((BitVec.ofNat 152 (word80 [0xfffffffffffe000001,0xd8e190d99107c1f003e0])),(BitVec.ofNat 152 (word80 [0x7001c00e060078380,0x58e080c9010842108421]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffffffffffff2,0x4ff683ab800000003ff])),(BitVec.ofNat 152 (word80 [0x580960250001280000,0x41b6832b0b5ad6b5ad6]))),((BitVec.ofNat 152 (word80 [1,0x1710a38776f801fffc00])),(BitVec.ofNat 152 (word80 [0x600180060080300401,0x7002002122108421084]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xc,0xe9177e4005fffe000000])),(BitVec.ofNat 152 (word80 [0x800e00380101c00800,0xa0171e0004c6318c6318]))),(0x0,0x0)]
def g183C : List ColumnInfo := [(2,0,181,0,7),(4,0,179,0,7),(0,16,161,6,6),(1,0,182,0,6),(16,0,167,0,6),(17,0,166,0,5),(32,0,151,0,5),(128,0,55,0,5),(33,0,150,0,4),(132,0,51,0,4)]
def g183A : List (List Nat) := [[]]
def g183D5 := limbs80 #[#[0x27db82caa07395454140,0xb72e9a8681ce55350d0,0xf4fb2286a867965d434,0x54bb6e0aa48776dc1545,0xe35cafb299a05e972181,0x183b]]
def g183D6 := limbs80 #[#[0xb58854bd58454be58054,0x54140cfd5254bed8154b,0x4340bf59540ef55140fe,0xd50bf59740ef55340fed,0x50dfd5150df55150f750,0xdf55350f750f50bfd91,0xf7d5143f755143bf5935,0xe18154f7d5243f755243,0x59654bfd8154fed8154f,0x481e0a83000bf58354bf,0x74ae4e25914843f1c8c0,0x8229087e3a9c8d866319,0x36210f88c1d127132934,0x8238c10e3621e208c484,0x1821823461001820001,0xa608c08c9840060c608,0x608018200c]]
def g183H6 := limbs80 #[#[0x940000a500,0x60000000000000000,0xe84700000000,0x230000000000,0x0,0x8100,0xf20000000000]]
def g183D7 := limbs80 #[#[0xd50ffa07f503bc87dd43,0xa9fe54feaa7f153fea1f,0xd0bf50204ba3e0f803fe,0x46844a2910284459ac45,0x28a71422530c72c22814,0x82845039a11394539a11,0xa1140c410ce6844719c,0xc418a1138e72]]
def g183H7 := limbs80 #[#[0x30c53380000,0x33a6e000028a16000000,0x224000000,0x528000000004680000,0x8e0000003076a0000000,0x128000014a11e100643,0x7032c002c00001b9000,0x254e200321bc000c0,0x34000]]
def g183D8 (j : Nat) := if j=0 then 0x3420117f else 0
def g183H8 := limbs80 #[#[0xc26400d9c30500007690,0x17589000d1]]
def g183L : Nat → Packing
  | 5 => (9,3,4,0,0,6,0,g183D5)
  | 6 => (27,2,4,0,0,9,0,g183D6)
  | 7 => (10,1,4,0,0,9,0,g183D7)
  | 8 => (1,0,4,0,0,0,0,g183D8)
  | _ => emptyPacking
def g183I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 2 79 0 8 4 0 g183H6
  | 7 => lookupWord 6 71 4 9 5 0 g183H7
  | 8 => lookupWord 2 17 4 8 4 0 g183H8
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
theorem low183 : Lower true (varsX 183) (graphGoal 183) 9 := lower_forest (g:=g183) (i:=0) (hints:=66629) (before_sound K175 V175) g183G g183T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K183 := extendKnown K175 9 [(183,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V183 : Known true K183 := extend_ok (m:=183) V175 low183 (by decide +kernel)
def g189Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x7fffffe01fffff7,0x22c8d02eb90001f07c1f])),(BitVec.ofNat 152 (word80 [0x25002800404022003,0x2080100ca9294a5294a5]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfff8003ffffffff00b,0x94281dd9c2003e0f83e0])),(BitVec.ofNat 152 (word80 [0x600b002800004023,0x802815094018c6318c63]))),((BitVec.ofNat 152 (word80 [0xffffffc00001fffffa,0xd8de81211e07c000001f])),(BitVec.ofNat 152 (word80 [0x28814c0ab058548288,0x985c8121165294a5294a]))),((BitVec.ofNat 152 (word80 [0xfffffffffffe000008,0x4f66b1ab300000003e0])),(BitVec.ofNat 152 (word80 [0xb305902cc0916704c8,0x4d66a12b3e739ce739c]))),((BitVec.ofNat 152 (word80 [9,0x1711a28774f8000ffc00])),(BitVec.ofNat 152 (word80 [0x3c01e00f00e0780708,0x16118282144210842108]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [4,0xe9177e4005fffff00000])),(BitVec.ofNat 152 (word80 [0xc00600300101800804,0x41026840008421084210]))),(0x0,0x0)]
def g189C : List ColumnInfo := [(8,0,181,0,7),(16,0,173,0,7),(32,0,157,0,7),(0,16,169,4,6),(1,0,188,0,6),(4,0,169,0,5),(4,16,169,0,5),(128,0,61,0,5)]
def g189A : List (List Nat) := [[]]
def g189D5 := limbs80 #[#[0x25fba2ca884ef7259510,0xd9aa7b12a1b3d8a3154,0x277b92c1a8cdd768c75,0xf624c3]]
def g189D6 := limbs80 #[#[0xe54110b759631bbd8950,0xd9510bf59510fd54510f,0x8950bfd8550f78c550bf,0x750f78c750f754d50fbd,0xbf58351bfd8151bf58,0xaa9a8f7f74644a352010,0x7941c32e82ce82d0caba,0x2140118421882010c448,0x100610a830a9008008c]]
def g189H6 (j : Nat) := if j=0 then 0x1a62cbc10eb else 0
def g189D7 := limbs80 #[#[0xf50fea87f443baa7de31,0x38291a0b007fd47faa3f,0x4c338e4530d914a25849,0xa69134e3baca450ce931,0x8314ec33a4c530c]]
def g189H7 := limbs80 #[#[0x1d800000001662,0x347e803cc0100000001d,0x1378ba06c000000000,0x94329c0000000]]
def g189D8 (j : Nat) := if j=0 then 0x680a17f else 0
def g189H8 := limbs80 #[#[0x18c0000000b6000eb880,0x11000000b40000]]
def g189L : Nat → Packing
  | 5 => (6,3,3,0,0,5,0,g189D5)
  | 6 => (14,2,3,0,0,8,0,g189D6)
  | 7 => (7,1,3,0,0,8,0,g189D7)
  | 8 => (1,0,3,0,0,0,0,g189D8)
  | _ => emptyPacking
def g189I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 7 0 7 3 0 g189H6
  | 7 => lookupWord 3 37 2 8 4 0 g189H7
  | 8 => lookupWord 1 19 0 7 3 0 g189H8
  | _ => fun _ => none
def g189 : Forest := ⟨189,8,fun i => g189Y[i]?.getD (0,0),g189C,g189A,g189L,g189I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g189P5_0 : block g189 5 0 6=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g189B5 : block g189 5 0 6=true := g189P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g189P6_0 : block g189 6 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g189P6_2 : block g189 6 2 12=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g189B6 : block g189 6 0 14=true := (@block_merge g189 6 0 2 12 g189P6_0 g189P6_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g189P7_0 : block g189 7 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g189P7_2 : block g189 7 2 5=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g189B7 : block g189 7 0 7=true := (@block_merge g189 7 0 2 5 g189P7_0 g189P7_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g189P8_0 : block g189 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g189B8 : block g189 8 0 1=true := g189P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g189T : checkedTables g189 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g189 0 0 0 = true)
  · exact (rfl : block g189 1 0 0 = true)
  · exact (rfl : block g189 2 0 0 = true)
  · exact (rfl : block g189 3 0 0 = true)
  · exact (rfl : block g189 4 0 0 = true)
  · exact g189B5
  · exact g189B6
  · exact g189B7
  · exact g189B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g189G : graphValid g189 (boundsBefore K183) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low189 : Lower true (varsX 189) (graphGoal 189) 9 := lower_forest (g:=g189) (i:=0) (hints:=132099) (before_sound K183 V183) g189G g189T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K189 := extendKnown K183 9 [(189,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V189 : Known true K189 := extend_ok (m:=189) V183 low189 (by decide +kernel)
def g219Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x1fffff87fff23263,0xf08e8001fc00001fc07f])),(BitVec.ofNat 152 (word80 [0x94028011022022062,0xa08a850a142850a14285]))),((BitVec.ofNat 152 (word80 [0xffe003ffffff0744ad,0x47ca000000000fe03f80])),(BitVec.ofNat 152 (word80 [0x4188b10a020427042d,0x464a23468d1a3468d1a3]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffc0007ffff8b95,0x920180fe0007f000007f])),(BitVec.ofNat 152 (word80 [0x200c02c20480d8381,0x12010a142850a142850a]))),((BitVec.ofNat 152 (word80 [0xfffffffff80000d2f8,0xabd1000003f800003f80])),(BitVec.ofNat 152 (word80 [0x8c110230047040d2d0,0xa9914c993264c993264c]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x12540,0xc337f0003ffffffc000])),(BitVec.ofNat 152 (word80 [0x100200400080000000,0x1020408102040810]))),((BitVec.ofNat 152 (word80 [0xcdc16,0x686c7ffffc0000000000])),(BitVec.ofNat 152 (word80 [0xe01c03804700805c14,0x486460c183060c183060]))),(0x0,0x0)]
def g219C : List ColumnInfo := [(1,0,218,0,8),(2,0,217,0,8),(8,0,211,0,8),(16,0,203,0,8),(128,0,91,0,8),(18,0,201,0,7),(0,2,137,80,6),(0,16,137,66,6),(64,0,155,0,6),(3,0,216,0,5),(9,0,210,0,5),(10,0,209,0,5),(16,2,137,64,5),(64,2,137,16,5),(64,16,137,2,5),(129,0,90,0,5),(130,0,89,0,5),(136,0,83,0,5),(66,0,137,0,4),(66,16,137,0,4),(137,0,82,0,4)]
def g219A : List (List Nat) := [[],[115],[65],[65,115],[48],[48,112],[48,65],[48,65,112],[112,48],[112],[112,65,48],[112,65]]
def g219D4 := limbs80 #[#[0x40c8ae1592d954250110,0x30c4ae17925d542d01]]
def g219D5 := limbs80 #[#[0xa0221a2b6560a5450120,0x6550940442d5325b2a84,0x94aa700a92848868ee17,0x922186f7560b6550910d,0x4dc1524429d324326e0a,0xccc0c9b82a48853664c6,0x2214e992993705491087,0x5c8644421f331326e0a9,0xc1a84a0a809053ae4185,0x41339952116150120dc5,0x94048371706a12e2a02,0xaaa8a12809078a595545,0x16ab965514250120e95b,0x940483c56cb2a284a024,0xecaa12809065ae177550,0x6aa97d954250120f15ba,0x40483a56eabaa84a0241,0xeaa12809072ae5975509,0x2b965515250120d95c2e,0x4832d50ebaaa4a0241e,0xbb92809074add554dc94,0x9929515450120cb4c2ee,0x4834d6cac14a8a024172,0xa0aa09078ad958295140,0x8654b4154120da5c1aa4,0x824ef2ac3682a0a41a69,0x268290517e5564dcd414,0x5e0176d052083fcab0fb,0x287b2a3a2c8b0a418788,0x2a89061ee17805d95448,0x5c97095120c74c1301bb,0xbecbc1ae32a241c6b65],#[0xc89065ae0b80dd564483,0x17159120e35baee5b82,0xb8ebc1ae2b224187875e,0x890617dd7835c5644830,0x3755912083f4c0eab8ac,0xf26c0eeab2241a6b82e0,0xa056ae497550b405028b,0x6258540c9dc2aeaa1680,0xbbaee0a128185f85dcd,0x51ee4175d9742503273,0x558b40b1dc82ebb2e84a,0x90180300186f75e096,0x4210781b060150480f03,0x452114420e8370d02c0a,0x4791d86e1ac681805815,0x4aa29c9f25c8a21c8420,0x8db338cb2f8b62ccb02b,0xfd3e8f73a8e7390e137,0x431094190340,0x500081400200000000,0xc8408002854004060008,0x782048408006840,0x1d18202034150010,0x11801016168011800800,0x1322c81000000006]]
def g219H5 (j : Nat) := if j=0 then 0x70f1008900 else 0
set_option maxRecDepth 16000 in
def g219D6 := limbs80 #[#[0x50940483aa5954250120,0x4836a5d54250120eab65,0x5515250120dab7550940,0x50120d697554940483ca,0xe3b6595140482ea60a54,0x5d9544821fe1576d0520,0x4831ed9570951208fb80,0x1d77059120a3d84d9654,0x50110fa952509404431e,0xebb6550940443eadc942,0x50940442ee6154250110,0x443ae2194250110bbb85,0xa1f6250110af985d8940,0x50510b7b855c940442be,0xcf775d8941442fce0152,0xdc941442bd6176250510,0x442fae0152509109f585,0x60b6550910f2d5454942,0x50910c7f75d9542442bb,0x8fe87d95424423f61f65,0x9d9424427ee017550910,0x4433e1937054910abd84,0x6137054910cfa64dc152,0x54910aed82191524427e,0x8fd8719152442b760c64,0x59152442b7e0d6454910,0x442bb60a64549108ff87,0xe1574d89108fd8799152,0x191108ff845d7624423f,0xced855c8644423fe1572,0xdc9644433be157219110,0x4823fe1572991108fd85],#[0xe0d4150120fa94250540,0x50120fa942d0540482f6,0xfa94258540482fa60b41,0x58540482ee2116150120,0x483ea5097150120bbb84,0xe0d7150120beb825c540,0x50120fa942dc540482f6,0xfaa5450940483ea55142,0x50940483ea9914250120,0x483bad954250120ee965,0xdd54250120de97550940,0x50120fa975509404837a,0xf695454940483eadd542,0x54940483da5d55250120,0x483ea5537250120bea87,0x5d77250120faa54dc940,0x50120deb75dc9404837a,0xf3a5455140482fa61772,0x551404835edd55450120,0x483ea6095450120afb86,0xe195450120f3b7555140,0x50120be98295140483ae,0xfa982951404839ed9654,0xd9540482fa60a6450120,0x482bea1f6550120e7b75,0xdd57550120beb825d540,0x50120deb825d5404835e,0xdeb82dd5404833ee1975,0x50550483da5494154120,0x483da54b4154120bdb83,0x61b4154120be982d0550,0x50520bf180d0541482be],#[0xcdd64dcd41482bd61b41,0xdcd4148337d937350520,0x48337d977350520cdd65,0xdd76550520a7f8559141,0x505208fd86dd5414831f,0x9df835d9414827ee0176,0xdd9414825fe157650520,0x4837a5c970d05209f980,0x59570d0520deb825c341,0xd0520cfb655c3414833e,0xa7f85593414827ee1570,0xd93414823fe1d64d0520,0x4823f61d65d05208fd87,0xe1975d05208fd87d9741,0xd0520a7f855db414823f,0x97f855db414827ee0176,0x5db414833ee0176d0520,0x4831fe1576d0520c7c85,0x61e76d05208ff855db41,0x585209f980ddb414823f,0xcbf74591614832f1d164,0x1d1614829fe156458520,0x4825f61474585209dd83,0x6037155120de9725c154,0x551208fd86dc5544827e,0xe3d6495154482de60254,0x591544829f61a5455120,0x483aee016455120a7f85,0xe017655120e3f8559154,0x55120cfb805d954482be,0xde9725c2544833e60376,0x5c2544839ed957095120],#[0x48277e0d7195120deb82,0xe156495120c7f655c654,0x95120ebb80592544829f,0xa7d84d96544838fe1564,0x5da544833ee017695120,0x4837adcb7059120c7f85,0xdd66459120d7b75dc164,0x59120d7b80dd5644831f,0xeeb72dc1644831fe1b75,0xdc1644839e1d77059120,0x482be6177059120e7b75,0xe0d7159120afb805c564,0x59120c7c755c564482b7,0xa7f855c5644831fdd571,0xdc5644831f1d77159120,0x4829fa1c7559120c7f75,0xe037559120afb805d564,0x59120c7d81dd5644839e,0xc7d84dd5644831fe0775,0x5c6644837a5c97099120,0x503ead8942d01409df83,0xe1542d0140db97550b40,0xd0140b7b8558b40502ee,0x9fb855cb405037a5cb62,0xd894150367dcd4250540,0x5033b5cb62d0540cdf73,0xdc942585409fb805cb41,0x58540d9f73509615036b,0xa7f855896150337dcd62,0x58b6150337dcf6258540,0x5033b5cb62d8540a7f85,0xd8b70509408ff855cb61],#[0x50940db954dc142503ba,0x9f985dc1425036e95370,0xdc1425031fdd76550940,0x503eae0b7050940fab62,0xdd77050940db975dc142,0x50940bb985dc1425036e,0xd3f75d9542502ebe0965,0xd9742503abe0b6550940,0x5027ee0175d0940c7d75,0x5d765d0940baf8259742,0xd0940e3d75d97425034f,0xdbb805d742502eee0175,0xdc1625035e1d77058940,0x5035bdc87558940d7b75,0x60b65d8940d7b80dd562,0x58b40adf835c762502bb,0xafb805d562d02bbe0965,0x5c3415063fe1572d8141,0xd06bee0162583419f782,0x6177258341a7f855c960,0x2dc2a021c1980f00023f,0x5851c4e04c846840833c,0x869c68464860c5d05945,0x81c7e07c87447086f06d,0xc09609248e88ac84c834,0x4b04aa4a8ca74a389fc9,0xca8c90c78c3cc00bc4b6,0x94decdd4d98d5ccfccc0,0xd0d509905cfb4f30ed0e,0x3993392d92792191dd17,0xc96455794f54954593f9,0x987983d7dd7a17657056],#[0xa65a299ed9b19759398d,0x99c39c21be5b85b49ae9,0x5eb5e55dd1d95d59cf9c,0xea0d209605a01dfe1fa,0x4620a1ce19215611a102,0xe3d23ba37e3422be2822,0x52e4f24da4c246244a40,0x8a67263661e5e25a656a,0xa7aa76e75671a7026c66,0x9ba97e9428e28a686a80,0xa6afeac2a86a6ea329f6,0xed32cf6cbaca2c42c06b,0xe8ee76e3adfede6daad6,0x7b03f002fa2f66f2aeee,0xb1bf1a718f12f0cf0930,0x3ab36f33331b2bb2371f,0xe34cb48f45343b4233e7,0x36275eb5af57353751f4,0x73b72370b6cf6b769f66,0xbb87f8438077a778f777,0x39b797b9639278eb8d38,0xb13ad7a9ba5fa47a0b9f,0xb7c9fc63c4bc0fb8bb4f,0xd8c081bd5fd47d0bccfc,0x363b1814e410220f0531,0x4140422e485060f72508,0x82450381f64068a0fa10,0x10a03c2040f1e84207f0,0x2000010682c6058c0b90,0x40d1805001f041000068,0x8181040222a304001a30,0x1000201040200080c0],#[0x800168b0016000810001,0x40400000203a207440e8,0x4008039017202e46004e,0x610e8c800b04084a8d63,0x1048346b082c12200105,0x209010412b1908122024,0x202a16002405182e10,0x10439027202028140028,0x507b92841c01c81008,0x10882b00182810e4a14,0x121040f0400084400105,0x28185020207808201021,0x101820104028007040c,0xa0b001020107f0824159,0x8207d08207b08203000,0x158d04800c040f08107b,0x8441e0a4158500361304,0x1880e8c1d18204041e0,0x1000206040c0e8c1000,0x20485a120060007800f0,0x801080d083c204003020,0x78008001d083c0040000,0x10000081010008080000,0x211002047002e0020018,0x20204051408080208081,0x428080a40748080010,0x40f0a80102348c2a008c,0x1404280a9010309c0080,0x4042810502069010a02,0x90a0a14082810a036461,0x10b185630400002e405c,0xc81d901600200004b084],#[0x5026404071b84245590,0x40c0038004003000f001,0xd0010902010400081400,0x1010000002001a306c80,0x24006800a8a8010003,0x40800102800e0010002,0x7440820101020020100,0x4005028ab21903510340,0x720200001e182000000]]
def g219H6 := limbs80 #[#[0x12130005101d142002,0x200006e0c240915540,0x202eb0dd156000,0x2934cb80a0001c22753c,0xce0a8000b0b4d1db4030,0x79652035074000000210,0xd340074d40000001860,0x98000000000050100004,0x75550000000000000020,0x1803b060000703,0x412570000c0380009040,0xce0b1028f43dc5bf0c40,0x1072b960960600a52,0x4465680305095a0d209,0x201670640000,0x645d805d44dc2400,0x817b068000a05742b000,0x1b05100670cc000b453,0xb9025c38b0c181fa59c4,0x10d5124b473933a0ca40,0x1f41cd569808f479850,0x48c458084000107a2354,0xf0564858000208d848f0,0xd161095413c06,0x1c3670bfc0f109c]]
set_option maxRecDepth 16000 in
def g219D7 := limbs80 #[#[0x26eb98c8884ed7219110,0xf5284a024137dcd6444,0x826eb9ec290769525412,0x208faea322413d5c4644,0x4426fb9ac3a047f75591,0x510df6c4a0221ee50940,0x14437bb1282886f76548,0x8910bf6e0a92217ddc94,0x624427eba6c4884ff755,0x591109fae4322213f5d7,0x9404827eb94c8884ff72,0x250120fd2a4a0241fa50,0x5140483dcaa280907eb7,0x6550120df2caa0241ee9,0xdd540482fcbaa80906fb,0x970d0520bbee6a0a417e,0xf591544827ebb682905f,0xfd7655120d7cc8aa241a,0x7e5c2544827fbb2a8904,0x67f6595120d7ac92a241,0x17edc1644827ebb4a890,0x6fb7059120afeeab224,0x419fdd5644833e3aac89,0x905f970991209feeab22,0xa413f5d6644827ebb4c8,0xa07b942d01409fae9b2,0xa8177dcd41502fcb968,0x84a04fd72d8540bbee6b,0xa1281eedc142502fdb82,0xe84a06bf65d0940d7eca,0xbb12815fdd562502deba,0xaac5a06bd65d0b409fae],#[0xe1a0a833f5cb605067fb,0xa9280884ff7258341bea,0x6e4a0221fe5c940443fc,0x6a9284887f55250510ff,0xfecaa1221ef55142443f,0xffbaa84885fd7550910d,0xdfceca1221bf1d942442,0x37eb22a4886fc6454910,0xdfec8a9221bf9915244,0x83fda0a80907f9415012,0x20ff2e2a0241fe585404,0x483fcaa280907fb71501,0x120ff4c8a0241fe95140,0x483fdbaa80907f97550,0x520ff682a8241fe5055,0x41483fab0a82907f7415,0x50520dfac8a0a41f7dcd,0x5414837eb2a82906ff64,0x650520bfeeaa0a41bfd9,0xc341482ffbb282905fd7,0x64d0520dfac9a0a41fe5,0xd97414837eb2e82906ff,0xd76d0520bfaeba0a41bf,0xf9db41482febb682906f,0xfd6458520bfeeda0a41b,0x7fdd161482fe3a2c2906,0x5ff7155120ff2e0aa241,0x1bf59154483bf2a2a890,0x6ff7655120dfaecaa24,0x417f5c654483fcb84a89,0x906fd7695120dfac92a2,0x2417fdc564483fdb82c8],#[0x89077f7559120dfcc8b2,0x2241bfdc5644837eb8ac,0xc8906ff7559120dfaeab,0xa02817f5c664483fcb84,0x282a07fb62d0140ff2c5,0x5a0a81bfd8941503dea1,0x9682a06ff62d0540f7a8,0xc4b0a81ef50961502feb,0xb92c2a06ff6258540dfa,0xac5b0a81ef50b61502ff,0xeb96c2a06ff62d8540df,0x7aa8a1281fedc142502f,0x7fb2a84a07be5450940f,0xf7ecaa1281ef59542503,0x2febae84a06ff65d0940,0xf7ecba1281ef5974250,0x3fdb82c4a07bd75d094,0x40dfacab1281fbd89625,0x503be3aac4a06ff65589,0x940bfeeab1281dfdd562,0x25037fb2ec4a07fb70d8,0x8940dfae3b12817f5d76,0x625037ebaec4a06ff71d,0x58b40dfacab1681bfdd7,0x562d037ebaac5a05ff75,0x258341dfac4b0683bfdd,0xc960d077eb92c1a0dff7,0x818008a02e0098001bfd,0xa0da06182b0132086039,0xb850026212208984001d,0xba1be0d5866030216a0a,0x2188b04321fe0f787903],#[0x5822ae14b8a104ca2521,0x19b8cb064a30a1738b40,0x7823a61c58df06ca35a,0xe22d912085a4161fb8f9,0x109e24de26392b091a46,0xa62c195c0a9a53228b94,0x880c1a5f62ef9720b6a5,0x67e3379990ca264631d9,0x9ba0db26c63579a40d12,0x275639f9cd0e4271237d,0x79ef0f4a7963bf9dc0ed,0x7a82a40da030ff27e63e,0x4ba24110a872433a1510,0x1da8e646ba3211728a64,0x4a9a51127a926483a3d1,0x13729a24c7a5e12e2966,0x24ffa7c13c29d24e5a70,0x814a2a3e51ba89143aa1,0xbe553aa51512a7a533a9,0xca163ab0e57fabb15aaa,0xb8a5bbada16aab4659ba,0xafa17b2bd25dfaec1732,0x2c32613b051812c025fb,0xbb2318fac6e62fb15188,0xc2cd6665b2e194ac9e64,0x930023144d0a67fb3c19,0xf00345e4e2c00708451b,0x4420e0d80e5141b93881,0x407c2c00d1008039450,0x2850ec2c00d130b00203,0xe4e207c00d15930b0396,0x4c5620d0910018b14344],#[0x84c309850d0c08261434,0x3159034540c5310c001,0x3168824504c50d09128b,0x34462e4c008c515902,0x342870408c562139317,0xe0028214043b938f860,0x383e2835930860e0d14,0x211d1990285474608141,0x1e022993084640fc20c,0x22970840c8807c4c2a1c,0xb029040ac2c004a51500,0x180c045050e0d140c2b0,0x807060301c2c0a4201c,0x28214052839003693086,0xac2c007060301a42091,0x283e3c2e1c08a1500502,0x6c2c08ae3e1641b9308,0x2e1c064238f0b8702299,0x1c3835005040a0706e3c,0x990345c2c00706030114,0x4070603010aa41b0b003,0x47800e620d1038298834,0x1c00d1c309f130a87003,0x8b00101a9462763e4e2a,0x5028842726c440a21429,0x1928841164c0a210383,0xb0060a0ea20d64c0182b,0x301c064a22229938f868,0xa2203b02883440f07060,0x2804c3080706640301c0,0x8b931680508066085101,0x91b045628131090d1421],#[0x24186c18046091029918,0x883422446084e8d8a00,0x9060c1824224020d091,0x601004470d070434244,0x441143a2810614210e89,0x8484a20d090c1a8a004,0xc283094261468215198e,0x151b082120963c210242,0x43d93082040a640880c2,0x86480c2143d930830a0,0x4610f0a8216118e0830a,0xa3c0090a141a8c870048,0x4a306a1108f00481840b,0x8184a312060e8c1a8434,0x40a0644c01214928c4,0x4001b08406c00848908f,0x8406a1140e84144a10a8,0x1284344c00a0c1892842,0x844c0068410624c00c29,0x82423c0090a1d93001a,0x28314068700342c2450b,0x42a90224c0088a101b00,0x40081028230b02905140,0x21406108f0048185a4c2,0xa0f001984314042a90,0x6646361109302283a4c,0x42b0b01904140419842,0x164620a0c8f00198440a,0xa8c2c183a3400d131200,0x92214250a8488440080,0x1144c368c882450842a1,0xc2c1a8c8440664a322a],#[0x30b640a8500343120962,0x2890030d62a10c188a84,0x1208230034424a2c0102,0xa2143d928831164a2c0,0x864102a899030864804,0x282030a08640c501a20a,0x88424a2082810aa20990,0x228928838aa208449302,0xc0a20c890020ac0a2641,0x8420663610c3d9288324,0x40824c0a211901640419,0xc2190240640823019288,0x64620b0401883c122200,0x19882]]
set_option maxRecDepth 16000 in
def g219H7 := limbs80 #[#[0x20101f13213000032101,0x310431700020020100,0x1601110105380130a,0x15502400350013040,0xb10f5b2310102524003,0xd5903021200042,0x7b0000b0a6701f000000,0x30b300000000b0,0x9a000000000000000,0xe05e000000,0x0,0xe01c38ce0000000000,0xc9a409f0c1d550705d00,0xc434a0,0x5ec00f00000000000000,0x5c80eb000084960000e4,0xe5,0x0,0xb0000000000000e05600,0x1e0000000000000000b0,0x82400000000a4bc11,0x747e60c60000000000,0x5f0000000018b3000000,0x29cd0000f0bd000081,0x0,0x0,0x38100a0320000000000,0xb10600000000805514,0x56000000000000b2ad00,0xcbe015c14c0000e06c34,0x640000b43d8495410de0,0x648e70d8000090c7b0],#[0x511098c54f60ab000000,0xa58d00000000c1,0x3e714b00000000000000,0x3e74bbf0000000281a91,0x5e000000000000b2c7d0,0x9031a028e1340000d1,0x44b3f0b5b00d000000,0x40257277000000,0xe0e300000000000000,0x660000b0970000901b00,0x66000000000000d01df0,0xf0db000000000000b1,0x63b075c8cd6a23000000,0xf090f03950e10a0d04,0xcd00000000f0b4000000,0x30000000011c1000054,0x80e7b0,0xa9000000000000000000,0x502b708fa0ca60,0x0,0x80a1f1db0000712a00,0xc5027a1b000000,0x2553a079a0cf00,0xba000074020000000000,0x90d7f4,0x2f0000009eb40cb89d00,0x9ab0aa00004439a996d0,0x440000e05f71e670dc15,0x67a0c5e9487141d05304,0x2a15520180000c00a21,0x604a00000000c0,0x202c000000],#[0x81000000000000000000,0x4475509c90,0x14a74aab810000000,0xe02300000000c06f00,0x46e04100000000000000,0xa4ab40,0xf0d00000808600,0xe03dd0d9615758d400,0x305000000000000000,0xc4cc000000,0x115400000000000000,0xc3d0a400000000000000,0x80d6f09a411a000030,0x702ad0a70000000000,0xa0e94900006077000000,0xc4d400007471000010,0x6436000040e2000000,0x200076504590dd000000,0xa8a04400000000000098,0x44110000000054,0xb01a00000000000000,0x207d749dd08c000000,0x94b54300000000000000,0x500000000103c000010,0x5aa03600000000000061,0xe1c5644320,0x920000d03a88dea12500,0x98000090b10000000048,0x50000d4d30000000074,0x5db0430000b0ba0000f4,0xf23a0000080910e845,0x5014000000],#[0x30000000000000208d00,0xa0bb0000f0d560,0x90c8b23500,0xe606e00000000c55e00,0x51c00892ae000052b5a0,0xc200004176d262c61160,0x54465019000020,0x163a00,0xdff05b948c0000b4d500,0xf14d00000000b0afa0,0xc4000000000000000000,0xe4b400006069f874e0,0xe0e40000000000,0x8163f061304dc0cd00,0x44d7e8950000000000,0x0,0xe9f0a50000b451000000,0xd09280,0xb6308000000000000000,0x4f000010d19994000072,0x20,0xb05c000060a314cf00,0x96000000007004000000,0x248099940ea0b2a29bd0,0x94240a2022146410e500,0x60210000d088404c24,0x106b0000000000,0x3c000000000000000000,0xc0ad258e903ff53e81,0x5017310f0000000000,0x744f9001000000,0x70cc00000000000000],#[0xe974ea00004599000000,0x190000000000000000b1,0x3485000008,0x45000000000000000000,0x680d204e358bb4,0xb83215b1c800,0xce000000001040000000,0x38407300000000503b14,0x15cd00000000000030,0xa035160e055400,0xc900000000c457b07c00,0xa46e30890000d2,0xe4c0620000d81b000000,0x2288b02011,0xa82310b600,0xd2000000005458000000,0x80b70000000044,0x8400000000d0a2c2b000,0x84380000c1c6000070,0x502700,0x10e6407e026b000000,0x65510000000000,0x204b0000000000,0x0,0xa11700006047000000,0xe81600000000e0bc00,0x9a2400000000000000,0x506d34a9000000,0x0,0xb06700000000000000,0x0,0xd01100000000000000],#[0x52000000000000804200,0x50820000b0260000f0,0x0,0xce501300000000000000,0x1,0x78000000004452704900,0x60000311c000090ec10,0x74,0x0,0x52ba1a00000000000000,0xf63d0000000075,0x70000000000000000000,0xf05400000000b0,0xd00c000000,0x0,0xe4a5000040d4007400,0xe05800005005000000,0x0,0x1e000000000000000000,0x103720,0x0,0x7a000000005033000000,0x458f000000,0x706044540000000000,0x805900,0x10bea0da5102000000,0xd6e02e00000000000000,0x21,0xd057d0650000000000,0xf0713010a08a000000,0x93c01200000000000000,0xc00b50bf50ea30],#[0x38daf08e00,0x20160000000000,0x7474a0607f0000000000,0xe091cd000060def0c094,0x206380ce0000000060,0xe0480000a0ae123d00,0x91e56300000000000000,0x3a70a854616237006a80,0x24,0x3087909d4a1000,0x64550000000000,0x8009000000,0xa0d3c07200,0xb08300,0xe00700,0x4233000000,0x646500,0x626000000000e02900,0x49548000000000d1d800,0xb57c0000a58c78,0x4085000000,0x0,0x856d0000656400,0xb9000000000000359700,0x700d22a2000000000a0,0x600000000a2b1f16434,0xd30000a4924143000080,0xd08b18,0xb02d000000,0x680000b0acc15b00,0x34a30000000011bb00,0x60956034000000],#[0x38df4165809b000000,0xd15d0000b09f31c000,0x4c3000000]]
def g219D8 := limbs80 #[#[0xd48510fe50110b7d8d41,0xd8910bf58910fd50510f,0x9110bf59110bf19110bf,0x120fe50120bfd9110bf9,0x20bf19120bfd8520fe54,0xbfd9120bf99120bf591,0xfed0140bfd9520bf5952,0xfd0940ef50940bfd8540,0xd0b40bf58740bfd8940e,0x541bfd8141bf58b40ef,0x910bf58341f7d8d41fdd,0x20ff50520ff54910ff50,0xff55120ff58520ffd05,0xff99120ff59120ff9512,0xf58540ffd0540ff50540,0xd0940ff50940ffd8540f,0x8b40ffd8940ff58940ff,0x2060037000ff58341ff5,0x18615d1340fd0d40ab08,0xc129825a21c2011df1af,0x73b038e36533c30c2e32,0x4eb4bb4994694474173e,0x496195e25a457b54451b,0x87a17637337036d368e6,0x90d8e48ad8688388017d,0x1451a28d0e33262c1047,0x50028d151400a3440193,0x228a245088a0451a2e4c,0x345c808262802228e372,0x917262802228b931408a,0x1c372c228364c51468,0x1a5084a34a0610165282],#[0xac90a065203840404003,0x4a08121401c345081c30,0x48286101c365282870d9,0x68b931001c345101c365,0x5007c995140132628094,0xd911658030ac83b28d4,0x1401a264078834026307,0x480989907401b9510c39,0x624364c5804050c364c,0x34711931208a283c98b0,0x4246c5282c412911408a,0x251c54448189c2809484,0xb1294a0d1120a110a0,0x4704870600d4684a1236,0x2830e090e0c046846942,0xe1b031e12830885031e1,0xa0084a423890a00d2630,0x27262809468e91109890,0x11a8a00f931404a34526,0x89819050e443461d931e,0x8a00e9070d15931e1808,0xb9110e803451c371e1c8,0x3262402228]]
set_option maxRecDepth 16000 in
def g219H8 := limbs80 #[#[0x1d020002407200000606,0x6603160541e030784002,0xc020801000fa0700050,0x187c2228268087800080,0x30783006160104c02000,0x22c6180190250181c382,0x402043a81c2c011b8802,0x1c0aa045381c00000e07,0x11000264206b102cb601,0x25c818d20c081540164,0xa6850901070052c30460,0xa12b813395bc0003c1d0,0x8192c1bb06a341d6028e,0x40f38283a946424d0a3c,0x491fe934c95a813b80f8,0x403981f5816086dc0000,0x1a100940000c9ac0001,0x40d4000000000003d074,0x25029c13cc1760048,0x868b00780a3841ce9150,0x3603841e4ca37c278,0xe285a29314940055095c,0x10673064e01108178,0x956401254476c145420c,0x1a0f6444d4661,0xc041042e6133d49bc164,0x9581810e42d680100003,0x1c382b05038000306e1,0x8990004c0002c6ea,0xc13742dd5274517c41b4,0x2c18a007c0002481b,0x203d0503416880648550],#[0x812e10ed063911f6422e,0x21d5600c2588157559f,0x27dc22985a802621a5b,0xc28480f600da0abc4640,0x6ac9a142b8ca5e8083,0x4102011c0001002b80c4,0xc025c63d019f829f8a52,0x4300003c093057304ed,0x62cc67f800b026e40ed,0x420b048401c44a480003,0xc2ced5e7401f80fd90d0,0x8128000104d702d0c91b,0x201c21900ce61208979,0x8015821642c2546681bc,0x40840000468f42b5c268,0xc9560265c2bf52580002,0x548d058cc15982771279,0x2247846a982940dec568,0xe800009b800028273,0xc23e2149906704284655,0x415c6116d1df8182c65b,0x10b003415f442d82933,0x443995ec40e2845380af,0x418ca9294247e83ec2a8,0x795dc01f381b28580,0x6124864a416fc18400b7,0xd474d5f3829100bb819b,0x864600c0498e9070d165,0x106f814a84f30653605e,0x11068856095f84a14,0x1ddc25140bc10309268,0xd081c681117b451dc022],#[0x82498a29c2cad0e44a43,0x817c516b0512509950ea,0x89d39249c28800039227,0x8574002d49f9c2e19157,0xa94b0455c122c098049e,0xc525c08d14a4425f01db,0x852fc2260063855782a3,0xc2a646748170822182e8,0xc2130633c20400000001,0xe13681a40001d159c666,0x2915047fca4c0044cac1,0x8481c962610d8464c566,0xc58ac074450b45ff127d,0x110e41a98143899ac105,0x147c80ab403dd0c109cd,0xc14fc297051ac1ef4088,0x41ad065ec114d5e302ac,0x242c4d0c47ac25600b3,0xc97d41500000000280eb,0xa18d58ac5c150db505c,0x40a404e201fdc2328636,0x67b516c80e5292642c5,0x9a4a411b60d84a63e45d,0x89b6c09ed1008a084058,0x455fc0c9495141f90a59,0x5ad099512440000c0d2,0xc9b2c03286e50197006c,0xd48a9205c0a2c05e0488,0x5281e94070000145e9,0x15e80002001bd1abc239,0x482be06e840141e009e1,0x1c2e441c8614750ab],#[0x3c434000082368298,0xd0b0]]
def g219D9 := limbs80 #[#[0xd41ffa07f503fa41fd10,0x51b0259b138a803fe83f,0x410202550526488d00,0xd1463a48a500d1a48a5,0x248a02051539228]]
def g219H9 := limbs80 #[#[0x1021000203600100101,0x1806220,0x221b000000000,0x18700000000000,0xa0000000f4a54230000,0x20000000000342500035,0x24b79080002c22000244,0x26000000000000000000,0xc00000000008591a16b,0x3c16a4,0x0,0x0,0x3c4a6a8000000000,0xe00b4a80000000000000,0x3961d164000b458000,0xd87ea1e000240f0,0xe42ea06c000000000000,0x208c0000000281,0x28450000,0x820000000000000,0xc82180ed03000,0x1812,0x401800000000000,0x391e247f803000256200,0xc5940000001d0b000,0x6e02ac0000001c2f3064,0x2427a2a6801e8c7c,0xc02c000000141c000000,0x5fc880000000541c000,0x304e0000000a2870054,0x6811d028000406b49400,0x9000001e404c000118],#[0xa8800006098,0x20a000000000,0x206c411000,0xc0000009204931,0x188400000000,0xc000507400040a800000,0x24080000000113,0x2bc18946f00000000000,0xae8a342c000000000030,0x67fc6d101f85,0x156c30000342940c5ca2,0x52d1b000085700000001,0x10040000000000000090,0x410217c0000000000000,0x28628c00000000000002,0xdf2a80000000d,0xf08400000000008a7c00,0x815a6290001815,0xb4000000000000014240,0x1c1f000142dc21c000c8,0x2018480c000000]]
def g219D10 (j : Nat) := if j=0 then 0x2080513f else 0
def g219H10 := limbs80 #[#[0x2ca8000000000000020,0x7b00000,0xf0600040000320000,0xf0a411d100000000000,0x24000000000000000,0x2149430,0x7d000000000000000,0x14512078200000,0xa3000000003c28400000,0x2409]]
def g219L : Nat → Packing
  | 4 => (2,6,5,0,0,3,0,g219D4)
  | 5 => (57,5,5,0,0,10,0,g219D5)
  | 6 => (237,4,5,0,0,12,0,g219D6)
  | 7 => (187,3,5,0,0,13,0,g219D7)
  | 8 => (50,2,5,0,0,12,0,g219D8)
  | 9 => (6,1,5,0,0,8,0,g219D9)
  | 10 => (1,0,5,0,0,0,0,g219D10)
  | _ => emptyPacking
def g219I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 5 0 8 1 3 g219H5
  | 6 => lookupWord 24 131 6 14 6 4 g219H6
  | 7 => lookupWord 110 1109 4 16 8 4 g219H7
  | 8 => lookupWord 98 431 9 16 8 4 g219H8
  | 9 => lookupWord 28 293 4 14 6 4 g219H9
  | 10 => lookupWord 4 71 2 11 3 4 g219H10
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
theorem g219P5_0 : block g219 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P5_1 : block g219 5 1 56=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g219B5 : block g219 5 0 57=true := (@block_merge g219 5 0 1 56 g219P5_0 g219P5_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P6_0 : block g219 6 0 13=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P6_13 : block g219 6 13 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P6_109 : block g219 6 109 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P6_205 : block g219 6 205 32=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g219B6 : block g219 6 0 237=true := (@block_merge g219 6 0 109 128 (@block_merge g219 6 0 13 96 g219P6_0 g219P6_13) (@block_merge g219 6 109 96 32 g219P6_109 g219P6_205))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P7_0 : block g219 7 0 10=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P7_10 : block g219 7 10 59=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P7_69 : block g219 7 69 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P7_165 : block g219 7 165 22=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g219B7 : block g219 7 0 187=true := (@block_merge g219 7 0 69 118 (@block_merge g219 7 0 10 59 g219P7_0 g219P7_10) (@block_merge g219 7 69 96 22 g219P7_69 g219P7_165))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P8_0 : block g219 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P8_1 : block g219 8 1 30=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P8_31 : block g219 8 31 19=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g219B8 : block g219 8 0 50=true := (@block_merge g219 8 0 1 49 g219P8_0 (@block_merge g219 8 1 30 19 g219P8_1 g219P8_31))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P9_0 : block g219 9 0 6=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g219B9 : block g219 9 0 6=true := g219P9_0
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
theorem g219G : graphValid g219 (boundsBefore K189) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low219 : Lower true (varsX 219) (graphGoal 219) 11 := lower_forest (g:=g219) (i:=0) (hints:=65603) (before_sound K189 V189) g219G g219T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K219 := extendKnown K189 11 [(219,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V219 : Known true K219 := extend_ok (m:=219) V189 low219 (by decide +kernel)
def g221Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xc007ffffe0ffff6266,0xe02b3300000fc003f03f])),(BitVec.ofNat 152 (word80 [0x82500a004204402242,0x20033305145145145145]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfff800ffffffe0290a,0x8f76708003f000000fc0])),(BitVec.ofNat 152 (word80 [0x8612c22802082290a,0x8c7250134d34d34d34d3]))),((BitVec.ofNat 152 (word80 [0xffffff0000ffffbd84,0xb04846c0fc0000fc003f])),(BitVec.ofNat 152 (word80 [0x80300b0409009884,0x804840ca28a28a28a28a]))),((BitVec.ofNat 152 (word80 [0xffffffffff0000804d,0x6156adc000003f000fc0])),(BitVec.ofNat 152 (word80 [0x2304408c008e048045,0x61042decb2cb2cb2cb2c]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x9171,0x18b1d83f00003ffff000])),(BitVec.ofNat 152 (word80 [0xc0180300830080130,0x18308010410410410410]))),((BitVec.ofNat 152 (word80 [0x4e93,0x4f80057fffffc0000000])),(BitVec.ofNat 152 (word80 [0x300600c010c0104401,0x43800420820820820820]))),(0x0,0x0)]
def g221C : List ColumnInfo := [(4,0,217,0,8)]
def g221A : List (List Nat) := [[],[66,118],[48],[48,66,118]]
def g221D8 (j : Nat) := if j=0 then 0x7f else 0
def g221L : Nat → Packing
  | 8 => (1,0,1,0,0,0,0,g221D8)
  | _ => emptyPacking
def g221I (_ _ : Nat) : Option (Nat × Nat) := none
def g221 : Forest := ⟨221,8,fun i => g221Y[i]?.getD (0,0),g221C,g221A,g221L,g221I⟩
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
  · exact (rfl : block g221 3 0 0 = true)
  · exact (rfl : block g221 4 0 0 = true)
  · exact (rfl : block g221 5 0 0 = true)
  · exact (rfl : block g221 6 0 0 = true)
  · exact (rfl : block g221 7 0 0 = true)
  · exact g221B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221G : graphValid g221 (boundsBefore K219) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low221 : Lower true (varsX 221) (graphGoal 221) 9 := lower_forest (g:=g221) (i:=0) (hints:=132099) (before_sound K219 V219) g221G g221T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K221 := extendKnown K219 9 [(221,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V221 : Known true K221 := extend_ok (m:=221) V219 low221 (by decide +kernel)
def g231Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffe000fff807ffc03f,0xf4e3011a0ee000f0f00f])),(BitVec.ofNat 152 (word80 [0x5406a0250d0148585,0x306300180cc111111111]))),((BitVec.ofNat 152 (word80 [0xffffff000007ffffc0,0x1b4b2d207450000f00f0])),(BitVec.ofNat 152 (word80 [0x9904c836164190909,0x9b430d20445999999999]))),((BitVec.ofNat 152 (word80 [0xfffffffffff8000000,0x7718e8d98400f000f00])),(BitVec.ofNat 152 (word80 [0x4e02701381809e0e0e,0x5710e89184333333333]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffffffff,0xc8137847aa90f0000fff])),(BitVec.ofNat 152 (word80 [0x900480240001200000,0x7006a20444444444]))),(0x45c463c772f000ff000,(BitVec.ofNat 152 (word80 [0xe00700380201c01010,0x4184204332666666666]))),(0x33a4d3e0015ffff00000,(BitVec.ofNat 152 (word80 [0x1800c00406002020,0x2848160001888888888]))),(0x0,0x0)]
def g231C : List ColumnInfo := [(2,0,229,0,7)]
def g231A : List (List Nat) := [[]]
def g231D7 (j : Nat) := if j=0 then 0x7f else 0
def g231L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g231D7)
  | _ => emptyPacking
def g231I (_ _ : Nat) : Option (Nat × Nat) := none
def g231 : Forest := ⟨231,7,fun i => g231Y[i]?.getD (0,0),g231C,g231A,g231L,g231I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231P7_0 : block g231 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g231B7 : block g231 7 0 1=true := g231P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231T : checkedTables g231 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g231 0 0 0 = true)
  · exact (rfl : block g231 1 0 0 = true)
  · exact (rfl : block g231 2 0 0 = true)
  · exact (rfl : block g231 3 0 0 = true)
  · exact (rfl : block g231 4 0 0 = true)
  · exact (rfl : block g231 5 0 0 = true)
  · exact (rfl : block g231 6 0 0 = true)
  · exact g231B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231G : graphValid g231 (boundsBefore K221) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low231 : Lower true (varsX 231) (graphGoal 231) 8 := lower_forest (g:=g231) (i:=0) (hints:=1365) (before_sound K221 V221) g231G g231T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K231 := extendKnown K221 8 [(231,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V231 : Known true K231 := extend_ok (m:=231) V221 low231 (by decide +kernel)
def g237Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xe007ffffe1ffff91e0,0x9c1ae000000fc0fc0fff])),(BitVec.ofNat 152 (word80 [0x40500a0044001010c0,0x8c006041041041041041]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfff800fffe1ff8310f,0x7c85500003f00003f000])),(BitVec.ofNat 152 (word80 [0x84612c228044213107,0x7c0542cb2cb2cb2cb2cb]))),((BitVec.ofNat 152 (word80 [0xffffff00001fffda3d,0x31312000fc003f00003f])),(BitVec.ofNat 152 (word80 [0x80300b0881400a3d,0x11110186186186186186]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffe000462a,0x8b87903f00000003ffc0])),(BitVec.ofNat 152 (word80 [0x902404c0009824628,0x3829514514514514514]))),((BitVec.ofNat 152 (word80 [0x4984,0x67ec8fc000003ffc0000])),(BitVec.ofNat 152 (word80 [0xe038070110e044100,0x62ec8618618618618618]))),((BitVec.ofNat 152 (word80 [0x2651,0x42404fffffffc0000000])),(BitVec.ofNat 152 (word80 [0x100400800010000000,0x820820820820820]))),(0x0,0x0)]
def g237C : List ColumnInfo := [(1,0,236,0,8),(4,0,233,0,8),(32,0,205,0,8),(8,0,229,0,7),(64,0,173,0,7),(128,0,109,0,7),(72,0,165,0,5),(136,0,101,0,4),(192,0,45,0,4)]
def g237A : List (List Nat) := [[],[99]]
def g237D6 := limbs80 #[#[0xe5c5243e0372d5454942,0x5]]
def g237D7 := limbs80 #[#[0xf55152bf59542fb54942,0x42a00ff59152bfd9152d,0xc70187cb1570186ae8a5,0x481c5cb15308c82071b2,0x81c60d4c72c071]]
def g237H7 (j : Nat) := if j=0 then 0x9 else 0
def g237D8 := limbs80 #[#[0xa3946061a403faa5fd42,0x1e851ca301c]]
def g237H8 (j : Nat) := if j=0 then 0xc1e30010d214c8 else 0
def g237D9 (j : Nat) := if j=0 then 0x5432101bf else 0
def g237H9 (j : Nat) := if j=0 then 0x9c0e7c else 0
def g237L : Nat → Packing
  | 6 => (1,3,4,0,0,0,0,g237D6)
  | 7 => (5,2,4,0,0,8,0,g237D7)
  | 8 => (2,1,4,0,0,6,0,g237D8)
  | 9 => (1,0,4,0,0,0,0,g237D9)
  | _ => emptyPacking
def g237I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 1 2 0 4 0 0 g237H7
  | 8 => lookupWord 1 7 0 8 3 1 g237H8
  | 9 => lookupWord 1 5 0 6 1 1 g237H9
  | _ => fun _ => none
def g237 : Forest := ⟨237,9,fun i => g237Y[i]?.getD (0,0),g237C,g237A,g237L,g237I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P6_0 : block g237 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g237B6 : block g237 6 0 1=true := g237P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P7_0 : block g237 7 0 4=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P7_4 : block g237 7 4 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g237B7 : block g237 7 0 5=true := (@block_merge g237 7 0 4 1 g237P7_0 g237P7_4)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P8_0 : block g237 8 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g237B8 : block g237 8 0 2=true := g237P8_0
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
  · exact (rfl : block g237 5 0 0 = true)
  · exact g237B6
  · exact g237B7
  · exact g237B8
  · exact g237B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237G : graphValid g237 (boundsBefore K231) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low237 : Lower true (varsX 237) (graphGoal 237) 10 := lower_forest (g:=g237) (i:=0) (hints:=1283) (before_sound K231 V231) g237G g237T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K237 := extendKnown K231 10 [(237,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V237 : Known true K237 := extend_ok (m:=237) V231 low237 (by decide +kernel)
def g243Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x1fffffc1fffe0f32e,0xa645080003f000fc0fc0])),(BitVec.ofNat 152 (word80 [0x54028048400042f10c,0xa20100030c30c30c30c3]))),((BitVec.ofNat 152 (word80 [0xfe003fffe0ffff7480,0xe4aab28000003f03f03f])),(BitVec.ofNat 152 (word80 [0x188310100240807080,0x64821211451451451451]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffc00000ffff25c6,0x9b5842c0000fc000003f])),(BitVec.ofNat 152 (word80 [0x610421608485000546,0x9b4800e69a69a69a69a6]))),((BitVec.ofNat 152 (word80 [0xffffffffff0000084d,0x6156a9c0fc000003ffc0])),(BitVec.ofNat 152 (word80 [0x802805800016040841,0x154a88c30c30c30c30c]))),((BitVec.ofNat 152 (word80 [0x1171,0x18b1dc3f000ffffc0000])),(BitVec.ofNat 152 (word80 [0x3006010818080021,0x30cc08208208208208]))),((BitVec.ofNat 152 (word80 [0xce93,0x4f80057ffff000000000])),(BitVec.ofNat 152 (word80 [0x1c0380210e0100692,0x4c800170c30c30c30c30]))),(0x0,0x0)]
def g243C : List ColumnInfo := [(32,0,211,0,8)]
def g243A : List (List Nat) := [[],[112]]
def g243D8 (j : Nat) := if j=0 then 0x7f else 0
def g243L : Nat → Packing
  | 8 => (1,0,1,0,0,0,0,g243D8)
  | _ => emptyPacking
def g243I (_ _ : Nat) : Option (Nat × Nat) := none
def g243 : Forest := ⟨243,8,fun i => g243Y[i]?.getD (0,0),g243C,g243A,g243L,g243I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P8_0 : block g243 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g243B8 : block g243 8 0 1=true := g243P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243T : checkedTables g243 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g243 0 0 0 = true)
  · exact (rfl : block g243 1 0 0 = true)
  · exact (rfl : block g243 2 0 0 = true)
  · exact (rfl : block g243 3 0 0 = true)
  · exact (rfl : block g243 4 0 0 = true)
  · exact (rfl : block g243 5 0 0 = true)
  · exact (rfl : block g243 6 0 0 = true)
  · exact (rfl : block g243 7 0 0 = true)
  · exact g243B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243G : graphValid g243 (boundsBefore K237) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low243 : Lower true (varsX 243) (graphGoal 243) 9 := lower_forest (g:=g243) (i:=0) (hints:=65605) (before_sound K237 V237) g243G g243T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K243 := extendKnown K237 9 [(243,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V243 : Known true K243 := extend_ok (m:=243) V237 low243 (by decide +kernel)
def g245Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x1fffffc1fffe066ae,0xa0655800000fc0fc0fc0])),(BitVec.ofNat 152 (word80 [0x54028048400042228e,0xa00150030c30c30c30c3]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfe003fffe0ffff2942,0xa6aab28003f00003f03f])),(BitVec.ofNat 152 (word80 [0x182304100210802102,0x24a29209249249249249]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffc00000ffffbd84,0x995842c000003f00003f])),(BitVec.ofNat 152 (word80 [0x610421608485001c84,0x895840e69a69a69a69a6]))),((BitVec.ofNat 152 (word80 [0xffffffffff0000804d,0x6156a9c0fc000003ffc0])),(BitVec.ofNat 152 (word80 [0x804809800026048041,0x1542994514514514514]))),((BitVec.ofNat 152 (word80 [0x9171,0x18b1dc3f00003ffc0000])),(BitVec.ofNat 152 (word80 [0x700e010838088161,0x10a08c18618618618618]))),((BitVec.ofNat 152 (word80 [0x4e93,0x4f80057fffffc0000000])),(BitVec.ofNat 152 (word80 [0x180300210c0104c10,0x4a000060820820820820]))),(0x0,0x0)]
def g245C : List ColumnInfo := [(4,0,241,0,7),(16,0,229,0,7),(64,0,181,0,7),(128,0,117,0,7),(0,16,161,68,6),(1,0,244,0,6),(32,0,213,0,6),(4,16,161,64,5),(17,0,228,0,5),(20,0,225,0,5),(36,0,209,0,5),(48,0,197,0,5),(64,16,161,4,5),(65,0,180,0,5),(5,0,240,0,4),(52,0,193,0,4),(68,0,161,0,4),(68,16,161,0,4),(81,0,164,0,4),(84,0,161,0,4),(96,0,149,0,4),(129,0,116,0,4),(132,0,113,0,4),(144,0,101,0,4),(160,0,85,0,4),(192,0,53,0,4)]
def g245A : List (List Nat) := [[],[80,98]]
def g245D5 := limbs80 #[#[0x54530443e450d414c110,0x443d454d514c110f6152,0x595534c110d6b7554930,0x8c110f61525463044396,0xf51534c550442f4e0d51,0x54d50443cc5514154110,0x4438e5915454110e5963,0x58d5254510e556554d31,0x54510e67635495144399,0xa6f8558d524439558d53,0x5d9534421fe157650d10,0x84237e0d76551108df83,0x595534c210d6b7554930,0x54a10e596354d5084396,0xe5953d85504c29be1563,0x549514c35654f7154130,0x8c29b6076554930c6e76,0x5496154630e596354d50,0x54140a6f8558d528c399,0xe596354d50902cee0d54,0x5d9519032d5d941cc640,0x5429be156354a408df83,0xdcd52581518df835c764,0xc4200d65525c66054753,0x1a4b44b228fc72331689,0x58aad4a9f4ca4d1a7e3c,0xe770b6daacf64b0d7ab7,0x3b1788c2e0aff7cbcdda,0x20000000000586000e0e,0xc10006080c1110]]
set_option maxRecDepth 16000 in
def g245D6 := limbs80 #[#[0x26fb9aca887655254510,0xdcaa4b08613bdd95284,0xc277bb2a41866d655483,0x30eb2a6a82619b5c9650,0x5039caa2a0a066f65549,0x1109daebb1283cb55152,0x443f8a0a60885f7714c,0xc110fe6e298221fc5453,0x30443eca1a60887e9524,0x4c110df2ca98221f654d,0x530442fcbaa60886fb65,0x28c110fe2a3182217edd,0xd6304437cb2c60887e95,0x4154110fe262a82217e5,0x58d50443bca9aa0887f1,0xb7354110df6c6a8221be,0xe59150443bcaa2a0885f,0xf13194110df6c8a8221b,0x7e5ce504437cb1ca0887,0x7d5534c510fcaa498a21,0x1bd59531442faba26288,0x85f5754c510deeca98a2,0x21ed55141443daa1a828,0x886f76550510deacaa0a,0xa21dd54d51442fabaa82,0x2886f76354510deac6a8,0x8a21bd59151442fbb9aa,0xa4885f77454510deec8a,0xa1a21bbd8d5244376b1a,0xaa6884fd7650d10bf6e0,0xca9a219f595534436eb1,0xa2c6886f77158d109fae],#[0xe9b1a213fdd5634427fb,0xb82a8884fd75d8d109fa,0xaecaa221af59154442fd,0xfbaac8884ff73591109f,0xfaebb22213f5cf644427,0x6e39aca885df73595109,0x9fee6b2a21b7dcd65443,0x27eb9eca884ff7459510,0xfd2a4984213f5d36544,0x437cb2a61087d9534c21,0x10bf6ea984217e5d5308,0x8437cb1aa10877953542,0xe10ddaa6b1421bb58d52,0x38433eb2aa7086dd6354,0x4d209feeab1c213f5d95,0x538837aa9ac3105fb705,0x54e20dbac6a9c417edc1,0x5638827ebb2a71067d65,0x554130ebaa6a82613fdd,0xc5504c37db0aa09867f6,0x6454130ef2a8a82617ed,0xd86504c3bdb2aa0986fb,0x76150530bf2e328261be,0xf9d9414c2f7b9282986f,0xfe7654530edaa4a8a613,0x3f5d3614c376a96c2984,0x67f65549309faebb0a61,0x19fd95654c3b7b2aa498,0x84fd71d95309fee2b2a6,0x61de54d508c37cb0aa11,0x186f56154630df2c6a84,0xc6177dcd518c3b6a92a3],#[0x5186ed52586309faeca8,0x9c619f595538c376b1aa,0xa0a04ff7558e309faeca,0x98a816f5d331503bca9a,0x4a6a05bd7494d409faed,0x2b2a816fdcd545027ebb,0xaa1204ff73595409fee,0xa6a8481be58550903dca,0xa0e63206f96354240ef2,0xaa2a0c813f5db31903da,0xeb2a83206bd6350640f6,0xfaeca8c81bd585519035,0x6eb1aa7206ed6354a409,0x9faeca9c819f59553903,0x27ebb4a7206dd6394e40,0x9feeab1c813fdc56390,0x439eaa282a85ef725055,0x50bb8e6b0aa1afd91415,0x5433ea9ec2a85df73585,0x9509fae9b0aa13f5cf61,0x3542fcb84c6a85bf7458,0x51509fae9b1aa13f5c76,0x645427eb8ec8a857f735,0x545419fee2b1ca13f5cf,0x9605467fb82caa0df770,0x198151bbee6b02a3db54,0xd660547b6a94c0a8df57,0x73d81519faed302a35f5,0x58d525467eba6c0a8cfd,0xd74d8d519fae1b1aa3db,0xf5cf645467eb86c8a8cf,0xed73181529fae7b02a53],#[0x8090058002f6b9ec0a95,0x3d83a03282b02181a012,0xe05c85b05385004c8450,0x87106d86c06886706185,0x8187c07a879075874072,0xa09689308f88c0888850,0x8a90a38a209e89d09b89,0xc58c40be8b90b18ae0ac,0xdc8d70d58d20ce8cd0,0x8f90f58ee0ea8e90e58e,0xd90a1049031018fe0fc,0xa12892511f91e1169111,0x93513393213092d12b92,0x4394214093f13d93c13a,0x415295114d94a1489451,0x96516195e15a95915795,0x7397217096f16d96a166,0x818497f17d97a1789771,0x99919599219098d18998,0xaf9ac1a89a51a19a019e,0x1be9bb1b79b61b49b31,0x9cd1cb9c81c69c31c19c,0xd99d81d69d31d19d01ce,0xe1ea9e51e39e01dc9db1,0x9fd1fb9fa1f89f51f19e,0xda0c20aa05201a001fe,0xc21aa19215a14210a0f2,0xa29227a24222a2121da1,0x47a46242a3d235a32230,0xc25aa57255a5024ea492,0xa34d128c116110a61a5,0xc4a14d4a0e358628324c],#[0x148c3618d8a0d352a868,0x9114d0e900c343010418,0x4000898400300041011,0x100181020038280,0x30438122610800018100,0xc10304381c0068c10,0x4006041484202141000,0x180821145091a8438305,0x80a3040c100441484301,0x1000c111050844111030,0x4006040c10403010c00,0x30800163041004200000,0x410042001810043110,0x401080000060400000,0x41030400304000000000,0x4104040c100001040001,0x1410000001504141000,0xc1005810401080020400,0x1815080c10104000040,0x200103040c105040c100,0x504000000040c10000,0x30400000000504,0x4181110308000044410,0x8100000000005040c103,0x100001000000a100080,0xa0c00204000181000000,0x40858908430004016158,0x1080184a08000181052,0xb030800004004]]
def g245H6 := limbs80 #[#[0x79a10586204f406101,0xf0329905d8ec00000000,0x4070000038c,0x2498ff890000024d80,0xb090358e0000,0x3c52c711c0010100082a,0x619680216800000c8600,0xa000032cecc0811788d4,0x364d94e23108002,0x353748000c9821,0x600000000b75da7000c2,0x435c400147bd2d22b1f3,0x263]]
set_option maxRecDepth 16000 in
def g245D7 := limbs80 #[#[0xd58430bd58620bb58a10,0xd89419f59430bb58830b,0xc110fe4c110db54951bb,0x510fe94110fe54110fe8,0x10fd54510fd50510fd4c,0xbf58d10fb94910fb549,0xbfd9110bf59110bfd8d1,0xe4c210bfd9510bf59510,0x58e10fb54a10fe54210f,0x9620bf58e20bf59610bf,0x130bf59430fb54830bf5,0x30bfd8530fe94130fe54,0xbf59530fb94930fb549,0xbf58630fe54230bfd953,0xf59630bf58e30fb54a30,0x55140fb54940fe54140b,0x640fe54240bf59540ef,0xe40fb54a40bf58640ef5,0x50bfd8550bf59640bf58,0xdf55150bfd8d50df54d,0xbf58e50bf58650bfd915,0xfd8151bf59541fd54541,0xd8152bfd9151bfd8d51b,0xc110fbd8152fb18152bf,0xd10ff50d10ff54110ff4,0x10ff55110ff58d10ff54,0xff54e10ff59510ff591,0xff54130ff54e20ff54d2,0xf58530ff54530ff50530,0x58930ff54930ffd8530f,0x9530ff59530ffd8930ff,0x540ff54e30ff54630ffd],#[0x40ff54540ffcc540ff4c,0xffcc640ff94d40ff54d,0xff94e40ff54e40ff5464,0xf58550ff50550ff48550,0x98d50ff58d50ff58950f,0x8151ff58151ff59150ff,0xff59151ff58d51ff9,0x30e10b1096074059029,0xb1eb1c91ae1851471251,0x2ee2c529c27a25823d21,0x143e43c23a037e363333,0x550a4ef4cd4a446643d4,0x6306075ec5b557e56352,0x5d71f6fd6db6b9689667,0x28297f97d77b578c7787,0x94891f8ef8bf89686d85,0x60a37a159f39c399a96a,0xdb02aeeadaab8aa4a82a,0xbdbbc0ba5b91b76b4db1,0x75c61c46c2bc17c03bef,0xdd02ceecdacc6cabc90c,0xdbfd9dd82d67d4cd31d1,0x6ee53e46e32e10deedd3,0x2b1c018205ec6eabe90e,0x41a284072e0e3181438d,0x93600c345080c606101c,0xa21e2032d288892b1c20,0x911404640d1420708382,0xf0d2611a8c70a547610a,0x47074630e8c488898870,0x46487871a2a322216c48,0x485058c78e10703043c4],#[0x324906063888a3830322,0xa31c3151c58202021a02,0x6951040a1a18608080,0x6062050d123230f34449,0x418c161c50c1000d1054,0x88e6ca203010e30a8a1,0x18810688145452f090c0,0xc10f0cc231a1850c55,0x921e1a12e121408d1519,0x118e60a8446080801d1,0x81c2861a5430c1420202,0x178c110c047347063450,0x101810034a8c0c688142,0x6891a6a322215488c688,0x4a86088c0801a419188c,0x31c445904424908a866,0xc042102468a8c888203,0x20804a8a182010108a8c,0x42020380a8a14c150c30,0x8011612a3192b1018d1,0x431a28609846c31c306,0xc1499118b26464440804,0x8a2c306080809614c960,0x30b88182912c20508080,0xc0e5c44c321874a2860e,0x83841c5420c1600e1130,0x488e0c70a08c0e091402,0x1c2918a4070d0e8510c6,0x14c0610405042980cb15,0x1052c121201060a54380,0x2080d0842e1864010e14,0x60a8c33055186110842c],#[0xd0868a09198083160a18,0x63430660684446960c30,0x61180cb0522186841434,0x95201890810547083081,0x8b84442042c54720110,0x28b0e10c951a19504c15,0x9110c1614187425832a,0x3259]]
set_option maxRecDepth 16000 in
def g245H7 := limbs80 #[#[0x808010010000008400,0x18440008200840200843,0x4010944008022000e0,0x8040380000444000803,0x1fb000000000000,0x96200079c0000000db40,0x131b94b7135aa6,0xc5e0000000000000000,0xa04409400,0x1c44000000000000000,0x2a174e9b67c39d9880,0xc3e000000000065a0,0x6a4c0000000000000,0x0,0x7fab894d472d86000000,0x357d24,0x2df08000000000000000,0x16670000000000e,0x8170003144000000f278,0x7221d8b58e0000000000,0x3ea8000000,0x1c71241800000,0x68aa5a800000000000,0x5f9b00000a72a2b80000,0x8fe00000061640000007,0x40580000000000003,0x35705a51156a3f874ebb,0x314061c000000,0x383c000dab24fc00000,0x0,0x2c140,0x19e980000e4cb480],#[0x80000000000000000000,0xc000000621c8ba000592,0x88000000000000000281,0x8a57e599a2b5d610c165,0x2b75fc0000005b580004,0xaf8a3014a800000185c8,0x520aa380006460000000,0xc00000000051e4c0ec15,0x4000515387a000000387,0x5357ad800141,0x809000000000000000,0x1ef90400091a09980000,0x4a2d5d50136210001,0x0,0xc18d2e8000000000,0xa01937a04400,0x520000000000001e3800,0xc5800000000000000024,0x1b7410680000006617,0x0,0x1a0ccb00000000000,0x8bc336800,0x1404000000196600,0x9c31d800388400075400,0x213200000059d8e77c,0xc538000000000b880,0x6c916b133e9967cc8000,0x19b065c000000,0x0,0xf40000003ce400000000,0x24be00073bbca84,0xc480000000000000cc20],#[0x150d2190000000,0x9160001db4000000,0x4a24000000000000,0x8a6b218160a5200,0x3b3e000000000000000,0xa5107938d0007074d682,0x4897127d460270003,0x1abc0008aef370000000,0x20320000000000000ec5,0x12e456e0000000003d2,0xe8b000001aae0e8400,0x50bf40013d00000000,0x40a000f3180000002970,0xe1161d511924b0b98003,0xc0000000000000001131,0x5b548284001e1328ae96,0x84fb64c000e6,0x9d0000003d1a00001b00,0x1400000000000000000e,0x21b00000000000000004,0x94b,0x3c980000000034b0a000,0x5c37e4e000000000131,0xfab03559047800000000,0x73222a80,0x17b50,0x0,0xa693a31200000000,0x3d58c0b935800,0x81c5c00054d800000000,0x68e00036200,0x8d40000000000002c560],#[0x26f11ddec0012280007,0x6aac0000000000001858,0x20fc000000000,0x404000000000000,0xfca8111bd95400158c00,0x4f72f400085289472498,0x5,0x2db00016400000000,0x8b5200004d0003d48000,0x112941e000000228,0x43c51a000000,0x203000000000,0x0,0x3a48272b0c00151df240]]
def g245D8 := limbs80 #[#[0xd20ff087f443dca5ed52,0x81fe30fe987f0c3fc41f,0x7fa43fe50fea87f903fa,0x780c001fd52fea8ff50,0x2f4ae27c901e06013839,0x21a21cd51a414f6390cf,0x54708e68042608691e28,0x9840e28254601a40d11c,0xa51038201718a60e3971,0x69440824691e20408019,0xc34700440a347024246,0xe20d01a19028c22b0069,0x38642609a54688c44661,0x1640219838c2ac045094]]
def g245H8 := limbs80 #[#[0x803c3285080007100243,0x20800403350090c80011,0xc20cc2400400c104109,0x3f56a000000000,0xf21b8266b0007340000,0xc04c6ceae0001c173800,0x530d90a500005c3154,0x7111d92e2a000d4cd360,0x6da55a144e0b3dcb8,0x6e78ed2d00021220cb1a,0xc6526d000c4f30f5,0x8de118e3e0009b2b1000,0xcc000000000345000000,0x16000000b569283644,0x9200000000000007c900,0x5bcc2355e72e601000,0xa000959000ae30000000,0xecdd3b813000f08aa000,0xd358ba267d1d96217000,0xc0000009679390000007,0xc57000e1c000c8600092,0x54b000e4971bdcf,0xd258de5e680000000000,0xa62e1e700a3100099895,0xa800044700094e06674d,0xc31da2bdac000000b53b,0xa0583a122d8c2b895,0xd2235fc4f02000000469,0x1ead151000000000e329,0x2b000070700000000004,0xd29606337b3364623c,0xf7521c790d11918f0000],#[0x21f00054aedfe6194065,0x43000909000000e603e2,0xf2f000aa1e480000004,0xf24000000a2700,0x11400000080e,0x5d5b0000000000000000,0x1589f80354200015,0x250000000004ce03d000,0xb635]]
def g245D9 (j : Nat) := if j=0 then 0x1882013f else 0
def g245H9 := limbs80 #[#[0x2a5033244b4000f03415,0x18548c009b087a2caf3a,0x4c600390000c03a80000,0xc004adc100209108001a,0x6130e18a0f12808b0,0x8340000]]
def g245L : Nat → Packing
  | 5 => (38,4,5,0,0,9,0,g245D5)
  | 6 => (198,3,5,0,0,12,0,g245D6)
  | 7 => (111,2,5,0,0,12,0,g245D7)
  | 8 => (17,1,5,0,0,10,0,g245D8)
  | 9 => (1,0,5,0,0,0,0,g245D9)
  | _ => emptyPacking
def g245I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 12 83 5 11 6 1 g245H6
  | 7 => lookupWord 65 653 5 13 8 1 g245H7
  | 8 => lookupWord 38 251 6 12 7 1 g245H8
  | 9 => lookupWord 7 41 4 10 5 1 g245H9
  | _ => fun _ => none
def g245 : Forest := ⟨245,9,fun i => g245Y[i]?.getD (0,0),g245C,g245A,g245L,g245I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g245P5_0 : block g245 5 0 38=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g245B5 : block g245 5 0 38=true := g245P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g245P6_0 : block g245 6 0 12=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g245P6_12 : block g245 6 12 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g245P6_108 : block g245 6 108 90=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g245B6 : block g245 6 0 198=true := (@block_merge g245 6 0 12 186 g245P6_0 (@block_merge g245 6 12 96 90 g245P6_12 g245P6_108))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g245P7_0 : block g245 7 0 7=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g245P7_7 : block g245 7 7 61=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g245P7_68 : block g245 7 68 43=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g245B7 : block g245 7 0 111=true := (@block_merge g245 7 0 7 104 g245P7_0 (@block_merge g245 7 7 61 43 g245P7_7 g245P7_68))
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
theorem low245 : Lower true (varsX 245) (graphGoal 245) 10 := lower_forest (g:=g245) (i:=0) (hints:=132101) (before_sound K243 V243) g245G g245T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K245 := extendKnown K243 10 [(245,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V245 : Known true K245 := extend_ok (m:=245) V243 low245 (by decide +kernel)
def g246Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffff07fffc1f413e,0x66f130000003f03f03f])),(BitVec.ofNat 152 (word80 [0x40a40210100840401c,0x6051311451451451451]))),((BitVec.ofNat 152 (word80 [0xffff83fffe0e28c,0xa4a0f88003f000fc0fc0])),(BitVec.ofNat 152 (word80 [0x8c08400821002e00c,0xa07805145145145145]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfff000003fffff30ca,0xdb584280000fc0000fff])),(BitVec.ofNat 152 (word80 [0x8108282120a00010c2,0xc94800a28a28a28a28a2]))),((BitVec.ofNat 152 (word80 [0xffffffffc000000d45,0x6156a980fc0000fff000])),(BitVec.ofNat 152 (word80 [0x1201300004c0840541,0x6052808a28a28a28a28a]))),((BitVec.ofNat 152 (word80 [0x1171,0x18b1dc7f000fff000000])),(BitVec.ofNat 152 (word80 [0x1c01c0420701080121,0x10b0c84c30c30c30c30c]))),((BitVec.ofNat 152 (word80 [0xce93,0x4f80057ffff000000000])),(BitVec.ofNat 152 (word80 [0xe00e00843802100a92,0xf000530c30c30c30c30]))),(0x0,0x0)]
def g246C : List ColumnInfo := [(2,0,244,0,6),(4,0,242,0,6),(16,0,230,0,6),(32,0,214,0,6),(64,0,182,0,6),(128,0,118,0,6),(18,0,228,0,5),(36,0,210,0,5),(66,0,180,0,5),(80,0,166,0,5),(132,0,114,0,5),(160,0,86,0,5),(6,0,240,0,4),(48,0,198,0,4),(68,0,178,0,4),(82,0,164,0,4),(130,0,116,0,4),(144,0,102,0,4),(164,0,82,0,4)]
def g246A : List (List Nat) := [[],[114,100],[33,84,118],[33,97,116,84,81],[65,82],[65,114,97,82],[81,66,118],[81,98,116],[97,117],[97,82,65,114],[113,33,84,100,66],[113,66,101]]
def g246D5 := limbs80 #[#[0x50440443685c94110110,0x443f04c93148110d9173,0x60c5148110be18214520,0x4c110bb18414520442f4,0xf914350530443f04c921,0x5cc404436c5cd4110110,0x4427c61f51d0110dd181,0xe0d75d89108df835d952,0xd4520a5f835c56584237,0xad4e84d8c0c022fe1176,0x1808006fd38eed7a32d9,0x2028008000000]]
def g246D6 := limbs80 #[#[0x2f4b9080887b14110110,0xaf2ea20221765cc4044,0x4277b92c8886bb64d011,0x10fe262902219e595308,0x443f828a40887f231481,0x110fd26490221fcd4520,0x442fcbaa40885f97348,0x8110bf2e710221fa54a2,0x30442fbb8a60885f9758,0x4c110fe28298221fc485,0x930443ec99260887f371,0x310110fb286982217edc,0x4740442fcba880885f97,0x75d0110bf2e7a0221fcd,0xdc950443f8a0aa0885f9,0x771549109faec992217e,0xedc1624427ebb2a4885f,0xff75589109fee6b1221b,0x3f5d7624427eb9ec4884,0x4ff7655110bf6e0aa221,0x1bbdc964442f7b92c888,0x84fd73d91109fee6b222,0x219f5c5658427ebaec88,0x106f5614c420cfae6b2c,0x841af991310835eb2262,0x2104fd764c420cfaca98,0x8841b758d510837ab0aa,0xa2106be6454420d7ac8a,0xb08413f5d9510833eb2a,0xaca106f57558420deae6,0xd18a417e5c2314833eb8,0x8ca2905f970945209fae],#[0xeda8a413f5da51483bba,0xbb4a7104fd76cc6209fa,0xeeab1c413fdc5638827e,0xf3b242984fc76485309f,0xfae9b0a613f5cb614c27,0x8ac298901a844078009,0x89143f8f0388dc338c83,0xc96c59960529444d9284,0x89dc719b86a9a4659885,0xea2c89a2086a0c7d9e87,0x4a7c9da6898a5493a488,0x4accafab8acaaca9a98a,0x4b04bfaf8bcaecb7ad8b,0x4b4cd1b40ccb2cc9b18c,0x103832183dab64d7b58d,0xc104018903041006240c,0x201820030a421006240,0x2401080410c040060400,0x2401080000430100401,0xe0401004301810008000,0x308001000250e080410,0x1040c10000000104,0x100291c20004100081,0x400000004000000,0x404000041000410000,0x4000000000]]
def g246H6 := limbs80 #[#[0x149400381a00f1,0xc2c41c002604eec00000,0x2220003c32,0x3d640000000000000000,0x2009c8c00000000000,0x2c05428,0x38340000000000000000,0x1425022a1f43bd6800,0x1092000,0x24160100000000000000,0x340cece2d6ed]]
def g246D7 := limbs80 #[#[0xd584209f996109f59610,0x99020af59020bd98420b,0x84309f994209f59420af,0x110fe48110bd98430bd5,0x10fe8c110fe4c110fe88,0xfe54110fed0110fe101,0xbfd8910bf58910fe9411,0xe4c210bfd9110bf59110,0x59610bf58e10bf58610f,0x8620bf59420bf58420bf,0x530bf59620bf58e20bf5,0x10bf58e30bf58630bfd8,0xff4c910ff54110ff4c1,0xff55110ff58910ff5491,0xf54420ff4c420ff59110,0x54520ff8c520ff4c520f,0xc620ffd4520ff94520ff,0x530ff48530ff94e20ffc,0xa11011000ffd8530ff58,0x88a0125214384588880d,0x2ba273fc754dd1982ec5,0xb4c654c3d732bd5369e5,0x389107dfebd4756e09b3,0x253fa754d69772823f46,0x6cecfd8baef572a0d1fa,0xc261dc1380ef7ddbb8f,0x602102888e1430840447,0x3460210282101c32034,0x8c042052034604040062,0xc2080c1c30420506406,0x21010186083078420181,0x64830510189063120024],#[0x80121860002a470a4008,0x63c4101890c1080c490,0x605063c50a0c60f10605,0x8203120c283023c60a38,0x3120c4062418a101c30,0x18201101480d100860a2,0x2811018406404061828d,0x20c20224183182031014,0xc6000e18b101c3082031,0x30444604346042880c0,0x8a001c31c18608106023,0x6080860838608380141,0x90081800830508086085,0x1c1181c2001]]
def g246H7 := limbs80 #[#[0xc0702719401083400288,0x812000000000491,0x1300000001445c000000,0xc08000050332212b44dc,0x8a474000000000000000,0x1bcd8e00000001d86710,0x18,0xa086000000000000000,0xb0000a064000200a000,0x8a064,0x301f750800000000000,0x1411a4a4800,0x0,0xc12800000000000,0x700b00000000000000,0x0,0xc0000000000000000000,0x201200000000000101,0x95000001807000000000,0x26c480000000,0x9f182500000000000000,0x0,0x0,0x1800800,0xe62c00000,0x301a000000000000000,0x35011f8260000000000,0x14,0xe10800000000000,0x783fc4734008000000,0x46a00,0x5c2b0000],#[0xac84500000000000000,0xb34e00034,0x311c00000000,0x3018000,0x0,0xa03c,0x3888800,0xc0d80005008000000000,0xe07a00000007115f132,0x90920000000000,0x38050001404c0,0x100c400000000000,0x9fd29ad047c0f8000000,0x11000000e0010,0x0,0x4107207c000000,0x3113000000000,0x3c0500000000,0x0,0x34110000000000000,0xa0a400000000000,0x7b400000000000,0x20500700000001e8300,0x6538,0x46800070720000000000,0x789e000000004,0x9b036000000070210000,0xc2160001485701,0x180c0000000000000,0x2940e00b781572361080,0x1c1c521,0xac0],#[0x6074,0x0,0x0,0x6834a05e,0x1b800000000000000000,0x20929,0x1e27508600006536,0x92200000000023800,0x28f700e803c600600000,0x0,0x0,0xc4840000000000000000,0x7077,0x423000000000000000,0x0,0x7b14200038208000091a,0x482,0x10140000000000000,0x0,0x81000000000000000,0xa03094c6804605c00000,0x7012,0x4096f238000000,0x58d000000000,0x30880001893c835a02e,0xd000000000000000000,0x2c1600000001b70c4,0x20000000000000000000,0x3a8]]
def g246D8 := limbs80 #[#[0xd20fe107f843fa21fc10,0x1fe30fe987f0c3fc41f,0x1204f069289084e1b078,0x82121833123c32881c6,0x714304f1050c140d3022,0x8b20718414305030818,0x21218348f]]
def g246H8 := limbs80 #[#[0x83181c001101d489,0x18202083212c081040,0x6189828aa1c100540800,0x5aba5e230898a9501,0xb1c9890624fc608028,0x2bbab50206ce41f30200,0xf6580001723409205283,0x45894f0180000000000,0xb41dfe0a4000000042fc,0xe423000014e2232c4850,0xd8800004950001431e17,0xf0000000d0a1826e001,0x12a00002094000401dc,0x5064a92900cc0c172400,0x3742a94b4c1d0001434,0x28eaa813a08b107358c1,0xe1cc80b8000c7d000034,0x99fa18a5030000000359,0x2a8249112402e874a069,0xa12b252ef0c2410004c5,0x353f88e0002252000391,0x15284ce006c180001817,0x5d6e1cfc16000188dd,0x941b329b00426d204d00,0xc8f708542cb08192fd15,0x47ce08ac28e0a5d090,0x3a04a491a078c020bbc0,0x81274e70002427803903,0x1479a26054d2c000142b,0x5]]
def g246D9 (j : Nat) := if j=0 then 0x3f else 0
def g246H9 := limbs80 #[#[0x1e8240040880001,0x0,0x1c040000000006c4ae20,0x90e00000000000000000,0x120c000000000000,0x1a22000c600000000000,0x0,0x4ac6962052ad25764000,0x8a2000d44000001e,0x0,0x18a0000000000a46,0x0,0x8a600,0x0,0x126a0000000000006e00,0x0,0x609ea8000000,0x18020000000000,0x149,0x4e000000001d4a88a000,0xc,0x166600000091000,0x650000000000000,0x1a800000000002e80000,0x1e0e00000000,0x0,0x50c001a2be8400120a0,0x751611a2600,0x110ba4d864000,0x0,0x4e600,0x244],#[0xa480000000000,0x0,0x0,0x0,0x0,0x1e06000,0x1aea462000001b040000,0x0,0xa28000,0x2e40000000000000,0xd6a00000000000,0x2aa000000000,0x225aa50d00000,0xca00]]
def g246L : Nat → Packing
  | 5 => (15,4,5,0,0,7,0,g246D5)
  | 6 => (76,3,5,0,0,10,0,g246D6)
  | 7 => (53,2,5,0,0,11,0,g246D7)
  | 8 => (9,1,5,0,0,9,0,g246D8)
  | 9 => (1,0,5,0,0,0,0,g246D9)
  | _ => emptyPacking
def g246I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 6 71 3 12 4 4 g246H6
  | 7 => lookupWord 32 487 3 15 7 4 g246H7
  | 8 => lookupWord 30 151 7 14 6 4 g246H8
  | 9 => lookupWord 15 307 3 12 4 4 g246H9
  | _ => fun _ => none
def g246 : Forest := ⟨246,9,fun i => g246Y[i]?.getD (0,0),g246C,g246A,g246L,g246I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246P5_0 : block g246 5 0 2=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246P5_2 : block g246 5 2 13=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g246B5 : block g246 5 0 15=true := (@block_merge g246 5 0 2 13 g246P5_0 g246P5_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246P6_0 : block g246 6 0 7=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246P6_7 : block g246 6 7 69=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g246B6 : block g246 6 0 76=true := (@block_merge g246 6 0 7 69 g246P6_0 g246P6_7)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246P7_0 : block g246 7 0 10=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246P7_10 : block g246 7 10 24=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246P7_34 : block g246 7 34 19=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g246B7 : block g246 7 0 53=true := (@block_merge g246 7 0 10 43 g246P7_0 (@block_merge g246 7 10 24 19 g246P7_10 g246P7_34))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246P8_0 : block g246 8 0 9=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g246B8 : block g246 8 0 9=true := g246P8_0
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
theorem g246G : graphValid g246 (boundsBefore K245) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low246 : Lower true (varsX 246) (graphGoal 246) 10 := lower_forest (g:=g246) (i:=0) (hints:=554763328) (before_sound K245 V245) g246G g246T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K246 := extendKnown K245 10 [(246,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V246 : Known true K246 := extend_ok (m:=246) V245 low246 (by decide +kernel)
def g249Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffffffffffffffffff,0xec83a89398a000f00fff])),(BitVec.ofNat 152 (word80 [0x90010048000080,0x2c020090088111111111]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfff8007ffc03ffff,0xd9693506c3800f00f00f])),(BitVec.ofNat 152 (word80 [0x2a05206a0490682905,0x10613406c10222222222]))),((BitVec.ofNat 152 (word80 [0xffffff800003ffc0,0xd31aecc2d10000f0000])),(BitVec.ofNat 152 (word80 [0x4c89c44c46e0b23209,0x8d21aec42d1bbbbbbbbb]))),((BitVec.ofNat 152 (word80 [0xfffffffffffc0000,0x2535845bb50f00000f0])),(BitVec.ofNat 152 (word80 [0x702e01701700c0bc0e,0x2515845b30666666666]))),((BitVec.ofNat 152 (word80 [0xff0000000000000000,0x45c463c762f000fff00])),(BitVec.ofNat 152 (word80 [0x300180180100c010,0x1c4008122444444444]))),(0x33a4d3e0015ffff00000,(BitVec.ofNat 152 (word80 [0x80c006006002030020,0x1808320005888888888]))),(0x0,0x0)]
def g249C : List ColumnInfo := [(16,0,233,0,8)]
def g249A : List (List Nat) := [[],[112]]
def g249D8 (j : Nat) := if j=0 then 0x7f else 0
def g249L : Nat → Packing
  | 8 => (1,0,1,0,0,0,0,g249D8)
  | _ => emptyPacking
def g249I (_ _ : Nat) : Option (Nat × Nat) := none
def g249 : Forest := ⟨249,8,fun i => g249Y[i]?.getD (0,0),g249C,g249A,g249L,g249I⟩
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
  · exact (rfl : block g249 7 0 0 = true)
  · exact g249B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g249G : graphValid g249 (boundsBefore K246) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low249 : Lower true (varsX 249) (graphGoal 249) 9 := lower_forest (g:=g249) (i:=0) (hints:=393219) (before_sound K246 V246) g249G g249T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K249 := extendKnown K246 9 [(249,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V249 : Known true K249 := extend_ok (m:=249) V246 low249 (by decide +kernel)
def g127Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffff812621a200326f,0xd5dc800003f000fc003f])),(BitVec.ofNat 152 (word80 [0x510026202000106f,0x94d08145145145145145]))),((BitVec.ofNat 152 (word80 [0x48b26659372042,0xf062e000fc003f000fc0])),(BitVec.ofNat 152 (word80 [0x19840b26001322042,0xf06220c30c30c30c30c3]))),((BitVec.ofNat 152 (word80 [0x1d623e025cc0595,0x6d423000000fc003f000])),(BitVec.ofNat 152 (word80 [0x2e1d622e025c40104,0x654224d34d34d34d34d3]))),((BitVec.ofNat 152 (word80 [0xfffc971b196ab0f410,0x701b603f00000000003f])),(BitVec.ofNat 152 (word80 [0x2b008719114ab06410,0x600b628a28a28a28a28a]))),((BitVec.ofNat 152 (word80 [0x21605358e80d19,0xaeb58fc000000003ffc0])),(BitVec.ofNat 152 (word80 [0x4c0001401358080c19,0x895830c30c30c30c30c]))),((BitVec.ofNat 152 (word80 [0x4599a4d6018afc,0xa057000000ffffc0000])),(BitVec.ofNat 152 (word80 [0x7000010904d2018a90,0xa055a28a28a28a28a28]))),((BitVec.ofNat 152 (word80 [0x33a4c9c8156c882,0x3c30ffffff000000000])),(BitVec.ofNat 152 (word80 [0x800238008c80448080,0x3000c30c30c30c30c30]))),(0x0,0x0),(0x0,0x0)]
def g127C : List ColumnInfo := [(2,0,125,0,9),(4,0,123,0,9),(8,0,119,0,9),(32,0,95,0,9),(16,0,111,0,8),(0,4,75,48,7),(1,0,126,0,7),(9,0,118,0,6),(16,4,75,32,6),(33,0,94,0,6),(64,0,63,0,6),(3,0,124,0,5),(17,0,110,0,5),(24,0,103,0,5),(66,0,61,0,5),(80,0,47,0,5),(82,0,45,0,4)]
def g127A : List (List Nat) := [[]]
def g127D6 := limbs80 #[#[0xc04eca0477e4d87d8140,0x81de1925c5609023bf26,0x19825c640ee9c1ae2b04,0x182be321432e320679a,0xd4c2e6b00c1dd3835c56,0xac0307665d38358060ae,0x9db93e1d601833b70fc1,0x87d9260e6dc9b0fb04c1,0x273f26c06c8b2477e4d,0x213c6cc15243c6090c0c,0x9d2]]
def g127D7 := limbs80 #[#[0x9dd831d9409f5811d940,0x9df835d94097d851d940,0xde5825c640df17158240,0xdd97358060df17158060,0x9fb8758060db97458060,0xcf987d8260de5825c460,0x9df835c3649df835da60,0xbbf8458140bdf8358140,0xfb96458140fdb8358140,0xfb96498140fbb8458140,0xbbd84d8140bf98698140,0xbdf835d9409fd87d8140,0xdbf845d940ddf835d940,0x9fd809d940bf9809d940,0xdf5865c640fdb8358240,0xfdb8358060df6865c640,0xddf73d8160dfb8758060,0xfdb80dcd60fdb73d8160,0xddf74dcd60ddd74dcd60,0xddd64dcd60ddf80dcd60,0xddd84dcd60ddf64dcd60,0xdbf7459160ddf84dcd60,0xdbd7459260bdf835d160,0xddf835da609fd87d9260,0xbdf835c1649ff845da60,0xafd869c164bf5819c164,0xbdf835c364bbd80d9164,0x1684407800ddf835c364,0x5c944478f8368bc23868,0x7c9ec779d0709bc67990,0x98a548fa308aa1c83a00,0xb0ab4a9a90a2a7c9da70],#[0xc8b1cc3b00beaecb9ad8,0xe0b7cddb70d8b4ccfb30,0x80284c4e30e0fa4e5b90,0x6e3e2138010ce008338f,0xe20e0f138f89842c5e10,0x406e1e2e01387801c306,0xe3e261a010141b878b80,0x3138f803e007878b803,0x1040418100281c404301,0x43c30202040020400,0x18106e20800b04000081,0x40070400d05188828606,0x800122043c101901640,0x10100001000000810402,0x207]]
def g127H7 := limbs80 #[#[0xb0073a2fa8c5900b40a1,0x5dd00000100300600002,0xe8570000b]]
def g127D8 := limbs80 #[#[0x571182f6b94817d5c640,0xa0c1775cc60bdae4305f,0x60bbee6b057d75182deb,0x7fa60503fcb0281bed82,0xebb2817f1d940f7ac8a0,0x8240bfeeca05fe76502f,0x305fe76902febb481fe5,0x2ff3b0c17f5d060ff2c0,0xfdd160fbee6b07fb6058,0xed305fd74983fdb04c17,0x592ffb82c97f5d360bfa,0x1ff58140bfae1b27bf64,0xfceca07fd76503ffb028,0x64583feb22c1ffd8160f,0x4c1ffdd160ffae8b07ff,0x4ffae0b27ff64983feb2,0xfe70d93feb86c9ff9c16,0x21636c590890c00c0007,0xc9f91ca023a4650b2134,0xdde3b9e6cecdd83ade55,0xa75179cf2de4045084ef,0x65fc898c3075d7b4f5fa,0x2e1dbeb6febdd37a0336,0x1b1e2c3106f03d7f9ef2,0x6c24050c171e28980616,0x700714363c58040b8f10,0x1228f0d8f161c030fc78,0x64592363c38061f8b0e0,0xc662c11081e1b1e2c380,0x1c563c38b00c18361158,0x1c7806121b1e2c23c660,0x8cc78716018305082b16],#[0x8b00c16262c38f00a187,0xc363c23f1600c363c3,0x86c78b044143c4c38f16,0x8b0e01e306c38b00f170,0x1e2e10d8f1601e306c7,0x7c986322c7806c61b16,0x871601e30a0d8b0e3498,0xc4386c38f16048306c7,0x63c38b00f185040d871e,0x1318ac0363c38b00f142,0xc1030ac38e262c03e2c2,0x80a21e30388302148830,0x124214206843c3841821,0xf085624818f18931083,0x42807888878c0d20a092,0x1105041a22214208]]
def g127H8 := limbs80 #[#[0x13040544a439d4090002,0x84a5b698ccfaa0000000,0xa950d6db71c287c7690d,0xfee3000004a9e39da473,0xc4b0014300765153d9a4,0x8560011cb5d820004f17,0x19047400137048bf066c,0xf2bf2000002265472c00,0x8582630a8400133f478,0x96a62f8]]
def g127D9 := limbs80 #[#[0x60ff583fc60ff903fd40,0x6000ffd93fd64ffd83fe,0x8a18079f439bcb445168,0x61e3884860186306123,0x69068638221843e38a18,0x1a18e280f1e48e18a018,0xa38601c63c48e28601c4,0x62848]]
def g127H9 := limbs80 #[#[0x1d1000004140c240,0xa7178003a40000000000,0xd714bd0c9f00000633,0x2a8005ac00000,0x13000006100026400000,0x11d0031b0000072b,0x1600088800000,0x0,0x2235080000000000,0x154,0x1c00000,0x0,0x1ed000,0xa5000ac71828000,0x0,0x900019b14000,0x624000000058000158,0xe340000000a0400f5c,0x34800000003eef40,0xa1000000000000000000,0xa6800c3c00e3a,0x148]]
def g127D10 (j : Nat) := if j=0 then 0x8310402ff else 0
def g127H10 := limbs80 #[#[0x1040280000e46,0x5cd80000000001486800]]
def g127L : Nat → Packing
  | 6 => (14,4,5,0,0,7,0,g127D6)
  | 7 => (55,3,5,0,0,10,0,g127D7)
  | 8 => (47,2,5,0,0,11,0,g127D8)
  | 9 => (8,1,5,0,0,9,0,g127D9)
  | 10 => (1,0,5,0,0,0,0,g127D10)
  | _ => emptyPacking
def g127I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 3 23 4 8 4 0 g127H7
  | 8 => lookupWord 13 67 6 10 6 0 g127H8
  | 9 => lookupWord 11 179 2 10 6 0 g127H9
  | 10 => lookupWord 2 23 0 7 3 0 g127H10
  | _ => fun _ => none
def g127 : Forest := ⟨127,10,fun i => g127Y[i]?.getD (0,0),g127C,g127A,g127L,g127I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P6_0 : block g127 6 0 14=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B6 : block g127 6 0 14=true := g127P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_0 : block g127 7 0 14=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_14 : block g127 7 14 41=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B7 : block g127 7 0 55=true := (@block_merge g127 7 0 14 41 g127P7_0 g127P7_14)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_0 : block g127 8 0 9=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_9 : block g127 8 9 23=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_32 : block g127 8 32 15=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B8 : block g127 8 0 47=true := (@block_merge g127 8 0 9 38 g127P8_0 (@block_merge g127 8 9 23 15 g127P8_9 g127P8_32))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P9_0 : block g127 9 0 8=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B9 : block g127 9 0 8=true := g127P9_0
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
theorem g127G : graphValid g127 (boundsBefore K249) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low127 : Lower true (varsX 127) (graphGoal 127) 11 := lower_forest (g:=g127) (i:=0) (hints:=66627) (before_sound K249 V249) g127G g127T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K127 := extendKnown K249 11 [(127,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V127 : Known true K127 := extend_ok (m:=127) V249 low127 (by decide +kernel)
def g191Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfffea966212202326d,0xd55c800003f000fc003f])),(BitVec.ofNat 152 (word80 [0x500066202002106d,0x95508145145145145145]))),((BitVec.ofNat 152 (word80 [0x4aba6259772040,0xf0e2e00000003f000fc0])),(BitVec.ofNat 152 (word80 [0x1984aba6001362040,0xf0e224d34d34d34d34d3]))),((BitVec.ofNat 152 (word80 [0x1d42370258c0517,0x6d423000fc0fc003f000])),(BitVec.ofNat 152 (word80 [0x2e0d4226025800106,0x654220c30c30c30c30c3]))),((BitVec.ofNat 152 (word80 [0xfffc97130deab0f410,0x701b603f00000000003f])),(BitVec.ofNat 152 (word80 [0x2b00951101cab0e410,0x600b628a28a28a28a28a]))),((BitVec.ofNat 152 (word80 [0x216057d8e80d19,0xaeb5800000000003ffc0])),(BitVec.ofNat 152 (word80 [0x4c00214017d8480c19,0xa158b2cb2cb2cb2cb2c]))),((BitVec.ofNat 152 (word80 [0x4599a056018afc,0xa057fc0000ffffc0000])),(BitVec.ofNat 152 (word80 [0x700001018052018a10,0x8055208208208208208]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x33a4c9c8156c882,0x3c30ffffff000000000])),(BitVec.ofNat 152 (word80 [0x80032a081c00440080,0x2800c30c30c30c30c30]))),(0x0,0x0)]
def g191C : List ColumnInfo := [(2,0,189,0,9)]
def g191A : List (List Nat) := [[]]
def g191D9 (j : Nat) := if j=0 then 0xff else 0
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
theorem low191 : Lower true (varsX 191) (graphGoal 191) 10 := lower_forest (g:=g191) (i:=0) (hints:=66627) (before_sound K127 V127) g191G g191T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K191 := extendKnown K127 10 [(191,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V191 : Known true K191 := extend_ok (m:=191) V127 low191 (by decide +kernel)
def g223Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xd202c52ea81f80eb54,0xfe00000fe0007f])),(BitVec.ofNat 152 (word80 [0x202c50e800f80c844,0x142850a142850a14285]))),((BitVec.ofNat 152 (word80 [0x6c5ccf41047685680a,0xc00000000007f0003f80])),(BitVec.ofNat 152 (word80 [0x605ccf00043685600a,0xc8d1a3468d1a3468d1a3]))),((BitVec.ofNat 152 (word80 [0x39c86d8492226aa16d,0x40007f000000001fc000])),(BitVec.ofNat 152 (word80 [0x38c86d0490022a216d,0x44c993264c993264c993]))),((BitVec.ofNat 152 (word80 [0x90e270355411d5262a,0x603f800003f80000007f])),(BitVec.ofNat 152 (word80 [0x10e010215410552228,0x42850a142850a142850a]))),((BitVec.ofNat 152 (word80 [0x6261ae31f8268c8c0,0x60000001fc00001fff80])),(BitVec.ofNat 152 (word80 [0x62210e30b00408880,0x33264c993264c993264c]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x8b92402c1cc0c1599,0x9fc00001ffffffe00000])),(BitVec.ofNat 152 (word80 [0x801200000c0080511,0x4081020408102040810]))),((BitVec.ofNat 152 (word80 [0x6741939828201310a7,0xbffffffe000000000000])),(BitVec.ofNat 152 (word80 [0x450002902820001082,0xb83060c183060c183060]))),(0x0,0x0)]
def g223C : List ColumnInfo := [(4,0,219,0,11)]
def g223A : List (List Nat) := [[],[48]]
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
theorem low223 : Lower true (varsX 223) (graphGoal 223) 12 := lower_forest (g:=g223) (i:=0) (hints:=66627) (before_sound K191 V191) g223G g223T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K223 := extendKnown K191 12 [(223,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V223 : Known true K223 := extend_ok (m:=223) V191 low223 (by decide +kernel)
def g239Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffd820f824037d052c,0x4a000000fc003f000fff])),(BitVec.ofNat 152 (word80 [0xa0800b804011d0420,0x4a041041041041041041]))),((BitVec.ofNat 152 (word80 [0x68413e181d17d349,0x85000000000fc003f000])),(BitVec.ofNat 152 (word80 [0x3368403e1805179309,0x858e38e38e38e38e38e3]))),((BitVec.ofNat 152 (word80 [0x39fb2e0660122523,0x3900003f000000fc0000])),(BitVec.ofNat 152 (word80 [0x5c38eb2e0620122520,0x392cb2cb2cb2cb2cb2cb]))),((BitVec.ofNat 152 (word80 [0xff94dc4d96ac4e9988,0xfc003f00000003f])),(BitVec.ofNat 152 (word80 [0x60145845122c421988,0x186186186186186186]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x612c2fa4a934e42,0x2003f000000000ffffc0])),(BitVec.ofNat 152 (word80 [0x80061040a04a804842,0x514514514514514514]))),((BitVec.ofNat 152 (word80 [0x8a90581d3a05810,0xbffc000003ffff000000])),(BitVec.ofNat 152 (word80 [0xa10081d2a04000,0x30618618618618618618]))),((BitVec.ofNat 152 (word80 [0x674430492480a0b5,0x54fffffffc0000000000])),(BitVec.ofNat 152 (word80 [0x4104004800008015,0x4820820820820820820]))),(0x0,0x0)]
def g239C : List ColumnInfo := [(2,0,237,0,10)]
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
theorem low239 : Lower true (varsX 239) (graphGoal 239) 11 := lower_forest (g:=g239) (i:=0) (hints:=1363) (before_sound K223 V223) g239G g239T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K239 := extendKnown K223 11 [(239,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V239 : Known true K239 := extend_ok (m:=239) V223 low239 (by decide +kernel)
def g247Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x42c023883f343e8510,0x7f0003f8001fc000])),(BitVec.ofNat 152 (word80 [0x428020802e143a8510,0x60c183060c183060c183]))),((BitVec.ofNat 152 (word80 [0x48af1080c74f01b830,0x1fc000fe0007f])),(BitVec.ofNat 152 (word80 [0x48830080070f013834,0x2850a142850a142850a1]))),((BitVec.ofNat 152 (word80 [0xced768910010d03340,0x3f80000007f0003f80])),(BitVec.ofNat 152 (word80 [0x4ad760900010402341,0x22448912244891224489]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x9532249ab0cc92cc80,0xfe000000003fff])),(BitVec.ofNat 152 (word80 [0x95200408b0c0928488,0xd1a3468d1a3468d1a346]))),((BitVec.ofNat 152 (word80 [0x10a999692492e442a0,0x1fc000000007ffffc000])),(BitVec.ofNat 152 (word80 [0x102819690000844082,0x850a142850a142850a14]))),((BitVec.ofNat 152 (word80 [0x6154152740210967df,0xe00000fffff800000000])),(BitVec.ofNat 152 (word80 [0x5411274020004243,0x60c183060c183060c18]))),((BitVec.ofNat 152 (word80 [0x3f00c2649b8102186f,0xffffff00000000000000])),(BitVec.ofNat 152 (word80 [0x25008200918100182c,0x183060c183060c183060]))),(0x0,0x0)]
def g247C : List ColumnInfo := [(1,0,246,0,10),(2,0,245,0,10),(4,0,243,0,9),(32,0,215,0,9),(64,0,183,0,9),(128,0,119,0,9),(16,0,231,0,8),(36,0,211,0,8),(0,16,161,70,7),(68,0,179,0,7),(2,16,161,68,6),(4,16,161,66,6),(17,0,230,0,6),(20,0,227,0,6),(48,0,199,0,6),(64,16,161,6,6),(80,0,167,0,6),(132,0,115,0,6),(160,0,87,0,6),(68,16,161,2,5),(84,0,163,0,5),(96,0,151,0,5),(144,0,103,0,5),(161,0,86,0,5),(192,0,55,0,5),(196,0,51,0,4)]
def g247A : List (List Nat) := [[]]
def g247D6 := limbs80 #[#[0x5494f61d965948355143,0x1b8355253d4765d64e0d,0x7690935955458eb5ba06,0x5529f3a05db815cd54b8,0x835955487de8598dda73,0xa58320d65552b1fa460c,0x38bb76e13805d9548d7e,0x5d954a7ce8583e017655,0x83e01765529eba260f80,0xbb96e53805d95487e6a6,0x954c7664c93e01765534,0xe01765529f3a164f805d,0xa960c835d954a7ae8993,0x4a7ae8175e09735921df,0x2735932b996651809cd6,0x65d809cd6487eea57560,0x7e6a3905d6735929eba2,0x40032bb96e53805d5648,0x311900e8d0b8a0887058,0x4a3219d9c1a991796149,0x2830662,0x9801000000000000]]
set_option maxRecDepth 16000 in
def g247D7 := limbs80 #[#[0xb98e6aa55765f8355253,0xcb8bf76e11765523bf30,0x9483551438efcc2e639a,0x450ef3b2c41aa8a1fc75,0xfc32caaa287f1c935955,0xacaa1deee418655143f1,0xcdd76e0d6590eafb2b43,0x855da43ceec3f06b2c87,0x4ebf720c3ac8a9d77e4d,0x930eb22a75f79161d645,0x8a9d6fe518759153af7c,0xd94a1d6454e9ff2cc3ac,0x55253a7ecb50eb22a75b,0x6bb0dc1aa929fc759383,0xc8aa4a775d96e0d5494f,0x9ddee418655253f1fc32,0x261d6494ee7f28c32a92,0x163f2eb2d06aa2c75ef9,0x926b2aa8b1dd76568355,0xaa2c7e3f945955458fcb,0xb76508359563abecad0e,0xcc73552df720c22cab1d,0x4d3ec32ca39aa99dd865,0xbb0e6aa57ee41761cd5,0xaa93bd94618735523ff3,0x597815cd54ddab2702b9,0x735533eaedc0ae6aa6dd,0x5fc32c8b9aa99f776e05,0xb2e6aa69fe19655cd54d,0x98ff865d973552bf720b,0x7739cd54eceb26e739aa,0x552bbb2db9ce6aa75759],#[0xc32c939aa9b3d8559273,0xe6aa69f619659cd54d5e,0xfb905da735526fb30b2c,0x69cd54c7ec32ed39aa95,0x26ff30b2ee6aa47f6637,0x306b22a95fb905db7355,0xaa5cfe558359154bd7c9,0x95a0d64552f732141ac8,0x9154b5ecb506b22a973d,0xbb0641acaaa56f65e835,0x6b2aa973d9420d655536,0x6d7e0e8359554b9fca30,0xa0d6555367f0941acaaa,0x54abecbd06b2aa973d94,0x9c02ecaa78fddb84595,0xb2a9cfb76e0176553777,0xfddb845d954dddca700b,0x1765533f107c02ecaa72,0xcfd41f00bb2a99f983e0,0xc02ecaa67ee0f805d954,0xa9dbb94e0176553b7709,0x4f805d954e7dcb700bb2,0x65533f327c02ecaa67e2,0xdc9f00bb2a99fa93e017,0xaecaa67760c835d954cf,0x5f79160d76552bf720c1,0x835d954af7c9306bb2a9,0x52aff2ac1aecaa56fe51,0x1d06bb2a95f990a0d765,0xcaa56f652835d954cefc,0x79160f76552afb2b41ae,0x5cd64dd7c2704b9ac95f],#[0x3daebc12e6b26ebe5382,0xeab9ac93bd95e1173593,0x26ee651809cd64afdc82,0x6602735933f2eac04e6b,0xd64cfccbb0139ac9af99,0x720bace6b266f5d5849c,0x39ac95df935d673592bf,0xeee13805d564c7ec32eb,0x1755935f70dc02eab26,0x4d7dcb700baac9bbb94e,0x8b98e6b2eafe1b845d56,0xacb5fb905d073596bbf2,0xe41745cd658ffcc2e839,0x735972ff0aba2e6b2d7e,0xeec26e739acb97f85dd1,0xa4e6b2d7ee41749cd65c,0xb5fb905d3735963fb31b,0xb805d165d7dc3700ba2c,0x2aff2ac1ee8b2ebee5,0x84f8901021c83184b066,0x98ed1ce384690cc17a2b,0x532884d4931172103e47,0x35466cc197d2ee5a0b11,0x804f91ec3ba75ce41b0,0x792c2524868d112a1642,0x51a9451ca21412734c89,0x3035d6b4d622be55eaa5,0x76a2d099e33664ec8589,0x4ae59c3b786e4db1b335,0x5e08bf07d4f49e1bb47,0x63bc718b314e1dc2c83b,0xecce97f2c250c929071f],#[0x3da5d45a83d019e538e6,0xb5f65ebfd70ac354aa1d,0xd83f005f1bc574edddb5,0x8f2ee57c9190b19e24c3,0xe8c5d39a133ae6fcd39,0xd1fc0103fc2178bc00ff,0x59008901120283041e0,0x2000000030400003a4,0xb8017282000400080010,0x8083d08100060c101ca0,0x40c202000c1644102010,0xb0c1620204040c203430,0x100e84100001c00,0x402158010006080000c1,0x88081c40706080c1e101,0x98100001860800404003,0x8c00a481300343040608,0x20000c7138430025e00,0xe270840248c01180149,0x8201f003e004c008000,0x100800007c0080600410,0x2600744080e0051c6208,0x11c0105dc415801060,0x130029205240812c0100,0x20100060e10100240980,0x491802300200000000]]
def g247H7 := limbs80 #[#[0xc400e0152cfca0059403,0x3126c5ac75cc91000002,0x43fbc00160050da0816,0xa0000002680000410000,0x18dc70036]]
set_option maxRecDepth 16000 in
def g247D8 := limbs80 #[#[0x9ef825d9439f7815d543,0x9fb805d954b5f8355253,0xf6d5358952f6d6554932,0xdef825d952f6f8259552,0xbed829cd62bef825cd62,0xf9d5498d43bef825d562,0xf9c8355143ddd7598d43,0xdbf7655143f3d6555143,0x9fd85dd9439ff865d543,0xddd7558e43edd6558e43,0xcfd7659643bdf8359643,0x9ff87596439fd8759643,0xddf7458d539ff855da43,0x9ff845d9539fd86dd153,0xf5d5458e539fd84dd953,0xf3d6455253f5f8355253,0x9ff845da53d7d7655253,0xd7f7555163e7d6555163,0x9fe87551639fc8755163,0xedc83595639fd85dd163,0x9fd8755263dbd7455263,0xddd731cd549ff8755263,0xddf739cd54bf7815cd54,0x9fd86dcd54b7d859cd54,0xf3f8459554ebf7659154,0xbfb805d954e7f7659554,0xcff765d954bbf845d954,0xdbf845d954dfb805d954,0xbbf845cd64bef825cd64,0xbbd849cd64bf9809cd64,0xbfb805d564afd869cd64,0xaff865d564bbf845d564],#[0xb7f855cd65ddd731cd65,0xb7d859cd65ddf739cd65,0xbfb805d1659fd84dcd65,0xfbd8655143aff865d165,0xfdc8359543fbf8655143,0xfdf8359643dfe8759543,0xdfd855da43dfd8759643,0xdfe8759153dfd8759153,0xf7f8655253f7d8655253,0xfde8355163dfd8759253,0xdfd85dd163dfe8755163,0xeff8459563efd8459563,0xdfd8755263fdd8355263,0xf7d651cd54fbd641cd54,0xbfd861cd54dfd761cd54,0xf7d655cd54fbd645cd54,0xdff765cd54dfd765cd54,0xfbd649cd54bff865cd54,0xdfd769cd54f7d659cd54,0xbfd869cd54dff769cd54,0xf7d65dcd54fbd64dcd54,0xbfd86dcd54dfd76dcd54,0xfbe8359154fbd8359154,0xf7d8359554f7c8359554,0xf7f8359554f7e8359554,0xfbf845d954ffb805d954,0xdfd835d954dfc835d954,0xdff835d954dfe835d954,0xdfe83dd954dfd83dd954,0xfbf845cd64fef825cd64,0xbff855cd64dfd755cd64,0xbfd859cd64dfd759cd64],#[0xbff835d564ffb805d564,0xeff865d564fbf845d564,0xbfd841cd65dfd741cd65,0xdff745cd65dfd745cd65,0xdfd749cd65bff845cd65,0xbfd849cd65dff749cd65,0xbfd84dcd65dfd74dcd65,0xeff865d165ffb805d165,0xdfe83dd165dfd83dd165,0x1ac0a8041015004c000,0xfd073033c17009d045,0x106ac3201750a904dc23,0xc824d11b086c4001e10e,0x7b0b6c5882a914b09ec4,0x7303811b10d2c6603111,0x21d107c8083ed1e90eec,0xc9a04b9251122c8d0455,0xd2b3154ca6851927f139,0x3cbf05e12e316bcb2857,0x89339197cc9863531118,0xc7ce106ed3691adcd386,0x7693ab1d2ce807353951,0x1eccf587a13c91e0cee0,0x82540b202cff07e13e3,0x5225d100869429210d07,0x88f9477236d1908b945,0xb9257d290935493245d2,0x3b09c54db269d3309894,0x51b28ad438a0d4ff279d,0xd530a8d53b29ad4a8a45,0xd5752b7d598ac155b2a9,0x3d678b2d5932c4d608af],#[0xac712e3d708b715b12d,0x1a716970f87802c5a4e0,0x14169713871c40846e0e,0x78780261c2c787e1e00f,0x8780246e1e0471310469,0x5e113e01147151c4c47,0x3e1e01147144783851c5,0xe1081c5697811f843861,0x3821f843868605c7e064,0x8460465e1e0870f21229,0xc76518559787821c3861,0xe97831f84385a408e1e0,0x843c71825e0e1c7860f1,0xc7e1a40818189297831f,0x7145b871f811a906e046,0x1b8386971c51610e1e0c,0x19f8710664e1e0c71615,0x819c610e1e0a71297802,0xa5e1e010671697102387,0x1e01518569783859c3c6,0x1387809d97187e5a746e,0xe9451265e0e1a70f1848,0x504e1e0a70f1c3f87819,0xc515231783869c3c5150,0xf8780585480604a7e1e0,0x4c516c50fe1e0a71a929,0xc5e127e00e1a15878118,0x515183b17829f8440604,0x2383843c384e0a746e1c,0xc3c59008e5618ec4e0c7,0x515e0e1c710149b87831,0xe112e08717138780231c],#[0x1e0c7183d1f8780605c4,0x49831386971c60f8425e,0xf80415c428a5e1e0471e,0x805a59260e1c717844b1,0xe48ee1e0921a951f844b,0x1c7921b844b811c58547,0x143b844b811c526e460e,0x3871e9248445e112e0c7,0x93844b831c5e1e012471,0x78780584c426c5e00f12,0x638780504c5e126e0131,0x7169c608c4e1e0c56718,0x828e145e0a71a4983138,0x3a414499581211a9061,0x1820e0f08383c2484665,0x24140105840216100891,0x454383600f4610201104,0xf04543c216420e0c119,0x4636048461a202010584,0x610e11211816118c5128,0xc41244a60c403821510,0x4984854384600894120d,0x3c9684385100ec4a1651,0x9a84408a16026651440,0x1097103c3100e650c582,0x60819803d9440f264325,0xc365840344103d9420f0,0x3c485441683600e0d0c3,0x183104160e6212c41460,0x430c318262504c31448a,0x50c9b0c3c30f26c30c58,0x6e00c544a978049220a],#[0x806e00c2019898780508,0x5420661150c201b8030,0x6414391c48322928e0c2,0x6064145990208a26026,0x39220a40c219020806a,0x601380482e01208201a9,0x860266310618c20f0684,0x9803d8c40816630c3810,0x826601020198c363041,0x49220a30c543c8c6040e,0x20602061808604a8f80]]
def g247H8 := limbs80 #[#[0x290801c04400462000f,0x700041c28422641030,0xa628115c18d023531346,0x102301c2230c44957d86,0x8000000f61000000000,0x609000000000573c,0xa00b2b056b3d95e00,0x41636842c4400076053e,0xaa35a10000000d380006,0x870f4672136da1205464,0xe4da3752e03300050e,0xe96cb7700090b82af1a0,0x94e234a5300081f91,0x5b57e5537b05b57e74c,0xbb32f48000018d2cc1dd,0x20d000119000f5861,0x23106d5052f07844b000,0x180f5cc3f66f607a401,0x87a93986e125367a5a00,0x5200033146bf3b181d51,0x1000000730965000759d,0xe13f03c47d16e29c76f1,0x4f817c04d0a77283a000,0x42741cb6485d668b629,0x879000569d7ca2d915d2,0x3c275000826f45d7fe5f,0x4e63a0f743174071f14e,0x56672]]
set_option maxRecDepth 16000 in
def g247D9 := limbs80 #[#[0xe634cbeeb1a65fb54932,0xb2657fdd532bfaea997d,0x32fbac7995ff764cafeb,0x7ed6254afebb6657f5d7,0xebb2a5df59552efaa6a9,0xd562bfee6b16fd6358af,0xa1fde6350feeb1a877fd,0xeffbaa877f5d543f7aa8,0x758e43bfeeca1dfd7650,0xe4a9dfd7690efebac87f,0x54fef31aa7f758d53bfe,0x77fdd953bfaeca9dff74,0xfaa929fdd6394efeb94a,0x7258efebb4a77f5d253e,0xac7bf59563bfee8b1dff,0x3bfae931dfd7298effba,0xbd64552ffb9aa97f5d66,0xbb2a97f5d954efacaaa7,0x965bfeeab25ff73592ff,0x95ff74596ffb9acb7fdc,0xfea9ac5ff59732ffaca9,0x9cd62ffae6b17fe5358b,0xb21ffd6550ffebaac5ff,0x8ffeb24a7ff59153ffac,0xff55263ffee8b1ffd545,0xce6aa7fd73553fe39aa9,0x6553febb2a9ffdcd54ff,0xc9ff9cd64ffae6b27ff7,0xffee4b2ffd72597febaa,0xe73597feb9acbff1cd65,0xa2cbff5d165ffee6b2ff,0x2ac1040590180003ffb],#[0xe1a10bc053c24c0fd06a,0xf8b2053e26f11f88203b,0x223e81dc0e206b032817,0x9894209be4a823f91048,0xc4e5fe2ea96b0af85532,0x39c9c24da46a9340195c,0xd0968143f21eecf16762,0x74c3a55d2408f745ca1e,0xb1578a8552aa8953ea9b,0x446032f05714b5358e2b,0x68dacad2067132ad904c,0xeed75eba19cace1f6ed3,0x40de00efd07ccbd89e56,0x8e3c5083f0610e50683e,0x94170474b84a0b812e1,0xe3c5c11f08f1a2888f83,0x93152e1c11ca0a970e08,0x4c58f87010162c74b830,0x24d2e1c01c490963e0c2,0xe0271c717823e1282942,0x31129849e08e30428970,0xb870471e2910b830c726,0xc71e286484e3e1c04478,0x3c64897047c23864b830,0xa930618e206ca930610e,0x618e3c549823e11e3860,0x86390112e1c11c70c970,0xb830c7202921e97206c1,0x27202964b90361c11c70,0x84a0897044c22c517870,0xc22c60b830a7202a5c1,0xc78a0d2e1c0505069626],#[0x8c3064b83093146e0c29,0x51d830a71e284cb87027,0xe2e1c09c98a0d2e0c24c,0xc18498c584648b870271,0x394141c5c18498a14263,0x82848b870271c345c185,0xb13061111c607170e02,0xe08e30f24970e00f107,0x84064b130e08e4260897,0x1e295101a225c3823904,0x80c923e1c04878b830c7,0x226116344284f0614e30,0x604068b130e04e4038b8,0x1c11898c963e1c03ca0c,0x898f170e08e2ca0c963e,0x87047224c649170e08e9,0x8e6471787047225061b,0xe4b870471e39423849e,0x8539261261c0963c61cc,0x3813c62094620212c4c1,0x9170614e3c8243d2c4c,0x278c3c5c18538f14a86,0x32e1c11d31520aa48b87,0x548441d970618e3c9101,0xf2a3951f96261c11d310,0x444b8704725365c38238,0x30fc3823a52a395243d3,0xf813121f20ec38239219,0x90992618f8090c232618,0x273039828449a7c3804,0x7e3c380a181c2942787,0xc05073117190c38098e1],#[0x6c787013303188b8c7e1,0x730487a689170e04e48,0xf4c170e04e6]]
def g247H9 := limbs80 #[#[0x40104c402c0c5302f4,0x128038129081ff10739,0x51ff54d1c302f5427,0xc3800020b000c5fb85,0x286750da4964df11c7f0,0xc72d51223b000f1604,0x3651786e0f000e3c000,0xc00000031a00032b63f8,0xa21687837000627c5,0x52000000064000000e04,0x700068375a000009059f,0xe1847100037000097d47,0x4c836c1d17ee69084000,0x650c44b480190009103,0x96154ec4554ff5300,0x7ab9096f576a3946c02c,0x5000c8eb2030197c12f3,0xc6df1ec2a000041e1432,0x78b47a07a31000000000,0xad08d3500000000020e7,0x96033408d83051b24,0x8bd66000e5bb58000856,0x714637926e3330000008,0x37307444071300000075,0x15c7545e42923a00024b,0x72318f00000003e6059,0xf2e00017b00008900000,0x3d206b6a622000000,0x2000000462b0a3724170,0x943791324400c8100008,0x55f32988863d65428026,0xa668000c6b08018c45d9],#[0xf8]]
def g247D10 := limbs80 #[#[0x43ff58bfd52ffccbfd32,0xfd63ff94ffd53ff90ffd,0x3fd65ff593fd54ff98f,0x195c498fc31896180360,0x9648211c890210799b66,0x72489648601c618d206,0x64641618071d44c69618,0x8071863881a592084720,0x8640694b9c4821225921,0x41a78058531e59e18041,0x1218071949271618061c,0x218061929058601c71a5,0x61671]]
def g247H10 := limbs80 #[#[0xe0b66719507302731cd0,0xb11a84003987,0x14170c000000000ce140,0x1a1984b0001be97200,0x102000d89a80000000,0xb6427fa5800001ee8000,0x20016304da2400000643,0xf0ec18006ad9a,0x3598001140,0x5a5000e258880036c000,0xe5e425d526800000,0x3bc640054f7a5a900000,0x151800593c9c0041ea,0x86073500000000000b4c,0xeb53a208fd8e0000016b,0x3a8811c8ae3b7832519,0xd5262c0072ae9588b15b,0xf0380029b2260019e7d0,0xc047c4838ae5ac034295,0x82800b710375b8000012,0x353]]
def g247D11 (j : Nat) := if j=0 then 0xa438402ff else 0
def g247H11 := limbs80 #[#[0x706c0015004100b3,0x5800000000,0xe900a2006a34008b0017,0x26000000]]
def g247L : Nat → Packing
  | 6 => (23,5,5,0,0,8,0,g247D6)
  | 7 => (130,4,5,0,0,11,0,g247D7)
  | 8 => (146,3,5,0,0,13,0,g247D8)
  | 9 => (86,2,5,0,0,13,0,g247D9)
  | 10 => (13,1,5,0,0,10,0,g247D10)
  | 11 => (1,0,5,0,0,0,0,g247D11)
  | _ => emptyPacking
def g247I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 5 37 4 9 5 0 g247H7
  | 8 => lookupWord 32 163 7 12 8 0 g247H8
  | 9 => lookupWord 36 199 5 12 8 0 g247H9
  | 10 => lookupWord 21 139 4 11 7 0 g247H10
  | 11 => lookupWord 3 37 0 8 4 0 g247H11
  | _ => fun _ => none
def g247 : Forest := ⟨247,11,fun i => g247Y[i]?.getD (0,0),g247C,g247A,g247L,g247I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P6_0 : block g247 6 0 23=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g247B6 : block g247 6 0 23=true := g247P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P7_0 : block g247 7 0 4=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P7_4 : block g247 7 4 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P7_100 : block g247 7 100 30=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g247B7 : block g247 7 0 130=true := (@block_merge g247 7 0 4 126 g247P7_0 (@block_merge g247 7 4 96 30 g247P7_4 g247P7_100))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P8_0 : block g247 8 0 4=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P8_4 : block g247 8 4 67=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P8_71 : block g247 8 71 75=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g247B8 : block g247 8 0 146=true := (@block_merge g247 8 0 4 142 g247P8_0 (@block_merge g247 8 4 67 75 g247P8_4 g247P8_71))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P9_0 : block g247 9 0 55=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P9_55 : block g247 9 55 31=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g247B9 : block g247 9 0 86=true := (@block_merge g247 9 0 55 31 g247P9_0 g247P9_55)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P10_0 : block g247 10 0 13=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g247B10 : block g247 10 0 13=true := g247P10_0
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
theorem low247 : Lower true (varsX 247) (graphGoal 247) 12 := lower_forest (g:=g247) (i:=0) (hints:=66629) (before_sound K239 V239) g247G g247T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K247 := extendKnown K239 12 [(247,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V247 : Known true K247 := extend_ok (m:=247) V239 low247 (by decide +kernel)
def g251Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x1a2a8a2b7e919100,0x7f000007f01fc07f])),(BitVec.ofNat 152 (word80 [0x228022a2e101100,0xa142850a142850a14285]))),((BitVec.ofNat 152 (word80 [0x8aa5a91057047e8150,0x3f80fe03f80])),(BitVec.ofNat 152 (word80 [0xa05a8104704228144,0x68d1a3468d1a3468d1a3]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xac75084805cacee20,0x3f8001fc000000007f])),(BitVec.ofNat 152 (word80 [0x2c550840050accc21,0x42850a142850a142850a]))),((BitVec.ofNat 152 (word80 [0xd122249fb080be5c80,0xfe000000003f80])),(BitVec.ofNat 152 (word80 [0xd122008fb0809c5c09,0x93264c993264c993264c]))),((BitVec.ofNat 152 (word80 [0x14b9996d2492c842a0,0x1fc0000000000fffc000])),(BitVec.ofNat 152 (word80 [0x14b8112d0010c842a3,0x60c183060c183060c18]))),((BitVec.ofNat 152 (word80 [0x6154152340210167df,0xe00000fffffff0000000])),(BitVec.ofNat 152 (word80 [0x201005200000012292,0x4081020408102040810]))),((BitVec.ofNat 152 (word80 [0x3f00c2649b8102186f,0xffffff00000000000000])),(BitVec.ofNat 152 (word80 [0x9008240918102004c,0x183060c183060c183060]))),(0x0,0x0)]
def g251C : List ColumnInfo := [(32,0,219,0,11)]
def g251A : List (List Nat) := [[],[112]]
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
theorem low251 : Lower true (varsX 251) (graphGoal 251) 12 := lower_forest (g:=g251) (i:=0) (hints:=65603) (before_sound K247 V247) g251G g251T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K251 := extendKnown K247 12 [(251,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V251 : Known true K251 := extend_ok (m:=251) V247 low251 (by decide +kernel)
def g253Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x20a298a737e938010,0xfe0007f01fc07f])),(BitVec.ofNat 152 (word80 [0x2022802622e120000,0xa142850a142850a14285]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x82a5781044047cae50,0x7f0000000fe03f80])),(BitVec.ofNat 152 (word80 [0x2057810440420a452,0x64c993264c993264c993]))),((BitVec.ofNat 152 (word80 [0xcd70285805cacb1a0,0x3f800003f80000007f])),(BitVec.ofNat 152 (word80 [0x89102858050aca121,0x42850a142850a142850a]))),((BitVec.ofNat 152 (word80 [0xd532269eb880be4c00,0x1fc0000003f80])),(BitVec.ofNat 152 (word80 [0xd532028eb0809e4809,0x93264c993264c993264c]))),((BitVec.ofNat 152 (word80 [0x10a99b6d2c92c842a0,0x1fc0000000000fffc000])),(BitVec.ofNat 152 (word80 [0x10a8036d0810c842a5,0xa142850a142850a1428]))),((BitVec.ofNat 152 (word80 [0x6154172348210167df,0xe0000001fffff0000000])),(BitVec.ofNat 152 (word80 [0x2044152008000106d6,0xc183060c183060c1830]))),((BitVec.ofNat 152 (word80 [0x3f00c064938102186f,0xfffffffe000000000000])),(BitVec.ofNat 152 (word80 [0x50080001181001808,0x10204081020408102040]))),(0x0,0x0)]
def g253C : List ColumnInfo := [(8,0,245,0,10),(16,0,237,0,10),(1,0,252,0,9),(4,0,249,0,9),(32,0,221,0,9),(64,0,189,0,9),(128,0,125,0,9),(17,0,236,0,8),(20,0,233,0,8),(36,0,217,0,8),(48,0,205,0,8),(0,4,73,176,7),(0,16,169,68,7),(12,0,241,0,7),(80,0,173,0,7),(96,0,157,0,7),(144,0,109,0,7),(160,0,93,0,7),(4,16,169,64,6),(5,0,248,0,6),(16,4,73,160,6),(32,4,73,144,6),(32,16,137,68,6),(33,0,220,0,6),(40,0,213,0,6),(64,16,169,4,6),(65,0,188,0,6),(128,4,73,48,6),(132,0,121,0,6),(68,0,169,0,5),(68,16,169,0,5),(129,0,124,0,5),(148,0,105,0,5),(192,0,61,0,5),(97,0,156,0,4),(161,0,92,0,4),(176,4,73,0,4)]
def g253A : List (List Nat) := [[]]
def g253D6 := limbs80 #[#[0x60502eaba26156458140,0x5d6558d409eae8995e11,0x76969759563502ccfa26,0x5031bb94e418759540b1,0x845d94087be8998a1d65,0x8995e11765023afa2657,0x365965e4d715815096be,0x58150d8e597946056054,0x96551605436596564f81,0x5ba36456558150d8ee91,0xd50a73e8976e0d71542e,0x5956354365994e416558,0xa06516558d50b96e8191,0xcdae5790e0976542e5b,0x57654396b85e0b805d95,0xe09815d950c73e4f8260,0x5ae5790e09765431af94,0x65429cfa3647825d950d,0x7845c560a6be9191e097,0xe897560f715829afa25d,0x82e3ba05d56455160a73,0x558d519abe8995dd1645,0x9905955458ee4fa26416,0x61f946416555163b93e8,0x5163b87e91905955458f,0x16016558ee1da0e51655,0xf92e058059563cb3e498,0x63d93e57926016558f2c,0xc57059764fa5e4980595,0xe18120c0600c73e4f825,0xa544e48423c36302a241,0x6908a847e78726c66605],#[0xdd7c6c0bab4aea8a29c9,0xe9e3d,0x0,0x5810400000000000000]]
set_option maxRecDepth 16000 in
def g253D7 := limbs80 #[#[0xb1ac288735dd56358510,0x81e3965551605035af0a,0xd56458140b5ccb2a8b02,0x503976eab22c0a072e5,0xeb2aa8b1a81c79755956,0xacaa07175d56558d40f0,0xe3964551605423df24c3,0x7458150b3ccb2a8b02a1,0x42cf728b2ac0a871e597,0x82cab1aa1c5d65dd1635,0x8b065ee17805d950f2dc,0xf945955458e3df24c2ee,0x59563b67c9300b2ac7e1,0xcf70ab2ac088597e5580,0xcab1a217eb9261560443,0x53f65a8759510e6f4ba,0x559160503e730aaa2c0a,0x140f5cc2ac8b0281eb97,0x32bc22c0a07ae5978458,0xb0281eb99459560502f7,0xfae498558140f3cbaaca,0x9563502f7728c2ac0a05,0xf2ebaacab1a81e9d945,0xeb2ac6a073765d6558d4,0xa81bbb90619545039bd2,0xe418759540af7c930eb2,0x655027df24c3acaa04fe,0xfdc830eb2a813bf9461d,0x3acaa067be498759540c,0x157d95a1d6550337f28c,0x28759540a7ecb50eb2a8,0x5027f321c3acaa047f66],#[0xc830cbaa813bd94e1d65,0xeaa057be49865d540afd,0xbd95e1176502b7f28c32,0x55d940adecaf08bb2813,0x2bdf24c2aeca057ee418,0xae2b02a15bf946157650,0xa879e5957158150bedc9,0x9460560542df72cb8ac0,0x8150f3cb2b02b02a17bb,0xb327c0ac0a85dee55815,0x8b02a1e7965e0560542f,0x7ae5d16458150f9cc22a,0x5d160543d7708b22c0a8,0x50f3cb2b08b02a1e7965,0x22b2ac0a879e59784581,0x2a1e7b9159560543cf3,0xee516558150f3cca2cab,0xd61543daac6b8ac2a879,0x9f7c930eb0aa13fb9061,0xc3ac2a84efe518758550,0xa13f990e1d615426ff2a,0x95635c5509becaf0eb0a,0x15436bacbc1ae2a87975,0xecb706b8aa19dd76e0d7,0x2e2a869fe19655c5509e,0x8ff865d971542bdf24bb,0x6558d50f2eb2ae8b1aa1,0x43cbf22b2ac6a8797645,0xa2cab1aa1e5d94595635,0x8a85dee417655150f2fc,0xf945d954542edf24bb2a,0x55150ebdc82ecaa2a173],#[0xa7f28bb2a8a875be4976,0xcaa2a1b7b9061954543,0x84fee418759150d9fca3,0x25d9745427df24c3ac8a,0x550dbcc2700b2aa15ef9,0xf26c0acaa85dee418159,0xbb2a177b9061165542eb,0xdee17805d950df5c1700,0x9765436df0bc12eca86,0xdb7caf04bb2a1beb90e,0xbc02eca877ae0b805d95,0x2a15fb9060576543af70,0xe49815d950cf7c1302bb,0x76542bbf26c0aeca857b,0xbfcab02bb2a15bf94605,0x12eca867be0b815d950a,0x19ed84e0976543bd721c,0x7825d950cf7c2704bb2a,0x543adf2bc12eca875be1,0xc8f04bb2a19ed91e0976,0xeca867b653825d950cf7,0xfb90611765433df29c12,0x554560af7c9308bb2a15,0x25fb2dc3aa2b079ee416,0xf08b8ac1abd65e117158,0xb066fdd7845c560cdeba,0x925d5715834ff0ab2ae2,0xc560d6eb2b07b8ac15ef,0xdf24baee2b06775d583d,0x8aa2c1e3d7559154582b,0x74f5d57455160f1eb2ae,0x59554583cf720b2aa8b0],#[0x60bbdc82eaaa2c1e3f94,0x28c32a8b06bee4186551,0xa2c13fb9061d5458357f,0xf65774591609f7c930ea,0x564582df720baac8b05a,0xb5fca2eab22c16ef925d,0xbaee8b057be49755d160,0xc13ef9261774582bdf24,0x4985dd160af7c930bba2,0x55835f309c02cab067be,0xdbaf00b2ac16f994e016,0xacab05bee418159560f3,0x6fb9061165582dbf26c0,0x805d560df5c1700baac1,0x837d721c12eab04fe653,0x82cab1aa35bf94607755,0xaa8f97e416558d51f2ec,0xd905955458eedf24c02c,0x59563f2fc82caaa2c7e5,0x5bf02c02cab1eb760580,0xb2ac7ecf926016558f,0x1eb7e118059563d6ec23,0x56016558edbf28c02cab,0x563d6ec0f00b2ac7e5f9,0xb29c02cab1eb76138059,0xb2ac76df906056558edb,0xb7e418459563b6ec8702,0x165552dbb21c22cab1d,0x4d9fc2300b2aa976f926,0x1c22caaa5cfe51805955,0x2a95ef9260176552e7b2,0x643845d954adfca300bb],#[0x705973df04b8ae0b2d6f,0xf7c16e2b82cb5df935c5,0x12e0b2edbe17825c165c,0xb9ef74e09705973dae9c,0xd71dc165db7caf04b82c,0x2bbf26c0ee0b2d77e4,0x1820a003f816407a0210,0xaf850c24411a07f0388,0x83be1c80dd8690310176,0x411e08d045822410407d,0x7051e28713f89a04a224,0xe01698b185722b11548a,0xc045f22f61770bac5c62,0x34019c0cc065031b1898,0x8d986c635b1ac0d40690,0xa3a51c20df06e83711b4,0xd8fb87ae3cf1e38ed475,0xc444b21c909c82a40d1f,0x5812b494a49824591d08,0x9d44dd265930c9764b32,0x28f9448a1450227a93c8,0x4ae456a2b11554a90536,0x2cc1640b105852be95d,0x18b7c5b12d49698b465a,0xf62f71798bbc5d62e717,0x8d4c5a62530e982cc065,0x66032c1954c9a64031e9,0x9a54d1a68a34119fccda,0x6c035e9ad4d5a6a534e,0xe9bc0dd06e036c1b40d9,0x6e72a38e9c68e2470a37,0xb11d68ea474a3a11cfce],#[0xf0677b3b99dc0ed07653,0x3dc1ec0f507a03cc1e40,0xd0027f93f11f2cf907bb,0x742a213107e837410204,0x81126886441a1d90c885,0xdf46e23651a28c445ba2,0x4151fa8f547923a91ce8,0x926491a4592269104842,0x9161204309f010be086,0x41723fc0144ef021242f,0x440fa26c5f03021c1f08,0x680f05e89f024618210,0x46181f04689717c005c6,0x8fa2450681703f89f02,0x688fe2410f0050870cf0,0xf068c91448ff006d1812,0x41a101103ec9f0302141,0x2685f01c905c3f0011b2,0x560bc0084404410f02c9,0x3c3f0786d104f0346088,0xb0b10d143117c0085491,0x8162c10840e32fc008c5,0x17101a23c2000106c1c1,0x421069c021040680f118,0x1a05c204421081a041f0,0xa23c204582081a078404,0x1000f04008d80089,0x20800042308bc00c0004,0x100010001000108c2,0x23040002204008810001,0xbb0ec11186c14108c100,0x70130f850413041d04e8],#[0x2b05061385041306c40,0x41a05c510c1723c2b0d,0x17044850c1a03c170c1f,0x741c7070212c4419020c,0x103dc4c08470f0281830,0x41e84c271206081,0xc2c1e0c0004000400040,0x74190807001065820850,0x782109a23c202c1d0410,0x608270f8281830701950,0x40d1010681710210811,0x103c103c10344041a,0x103c106782081d040000,0x13001300146810681868,0xb12c10c0b041af002868,0xb07c007c004c0040d,0x300246810018051a3002,0x40710101c470dc10d1a,0x5820400054b04c007c0,0x70016081d101070101c0,0x1444081113c213c1d041,0x44208411080084108411,0x8108410841000004210,0x10400040d1010000841c,0xe0810701a08108411082,0x3100468c008030010441,0x8b60dc28184709c062d8,0x70821081f701440f8305,0x8c00ac0044b606c03084,0xc2f00307cc40803081b0,0x208113082004b6042086,0x4c2081f30c1b7084071c],#[0x210400384041f310204,0x3001034006c104000010,0x11a3002000]]
def g253H7 := limbs80 #[#[0x35872c5b0e001311201,0x1743f655463e04528000,0xa4cd45090438eb5a1cd,0xf340055c0008d88c,0x4e06c89e444800a84870,0x2db2941e96840e54412,0x7740007ee00]]
set_option maxRecDepth 16000 in
def g253D8 := limbs80 #[#[0x9df835d510ed56358510,0xeb964581409bf845d910,0xe5d6558d50e796558150,0x9dd83dc5609ef825d950,0xe5d6558d51ed56358551,0x9de8758d51cdd7658d51,0x9df835d9519dd86dcd51,0xe5d6555163cdf7558d61,0xadf8159563bd7815d163,0xdfb7558110ef96558110,0xbf78558510df77558510,0xddf7558d10edd6558d10,0x9ff855d9109fd86dd510,0xfbb8458140fb95458140,0xdf97558140ef96558140,0xf9d5458d40dfb7558140,0xddd7558d40edd6558d40,0xf3d6555140ddf7558d40,0xdbf7655140dbd7655140,0xdbd7559140bbd8655140,0xd7d7559540dbf7559140,0x9ff87595409fd8759540,0x9fd86dd5409ff865d540,0xdbf845d940bbf845d940,0x9fd85dd9409ff855d940,0xef96458150f795458150,0xf7b8558150dfb7458150,0xbdf835c550edd6358550,0xddf7458d50f5d5458d50,0xd7d7655150f3d6455150,0xb7d8655150d7f7655150,0x9fd86dd150d7d65dd150],#[0xb7f8459550f7b8059550,0xbef825d950bfb805d950,0xdfb805d950b7f855d950,0x9ff845d950def825d950,0x9fd84dd950d7f855d950,0xe7d6554560bdf8354560,0xbdd83dc560bbf845c560,0xebd64551609fd85dc560,0xafd8655160e7d6555160,0xebf74591609fe8755160,0xefb80595609fd85dd160,0xe7f7559560aff8459560,0xbef825d560bfb805d560,0xdf561dc1519fd84dd560,0x9fd86dc151d7d65dc151,0x9ff805d951bf78058551,0x9fd80dd5619fd85dc161,0xedf8059563edd8059563,0xedf8159563edd8159563,0xedf8459563edd8459563,0xb7f8059554bdf805d563,0x9ff805d954f3f8459554,0xbef825c165dbf845d954,0x9fd84dc165b7f855c165,0x9fd80dc565bdf835c565,0xff985581109fd80dd165,0xdfe8759510ffb8558110,0xff98558140ff97558140,0xfbd7655140fdd7558d40,0xfbd8459540fbd7559140,0xdfd8759540f7d7559540,0xdfe8759540bfd8759540],#[0xdfd765d540bff8759540,0xdfd855d940dfd865d540,0xff98158150ff97158150,0xff97458150ffb8158150,0xffb8458150ff98458150,0xbfd8758550ff57158550,0xfdd635c550bff8758550,0xf7d655c550fdf835c550,0xbff865c550dfd765c550,0xf7d7655150fdd7458d50,0xbfd8759150fbd7459150,0xdfd765d150f7d655d150,0xf7f8159550f7d8159550,0xf7f8459550f7d8459550,0xbff815d950ffb805d950,0xbff845d950fef825d950,0xdfd815d950f7f855d950,0xdfd845d950dff815d950,0xbff8754560dff845d950,0xdfd755c560efd655c560,0xbff855c560dff755c560,0xdfd75dc560efd65dc560,0xfbd7455160bfd85dc560,0xbfd8755160f7d7555160,0xefd655d160efd7559160,0xefd65dd160dfd755d160,0xbfd85dd160dfd75dd160,0xefd8159560dfd85dd160,0xefd8459560eff8159560,0xffb805d560eff8459560,0xbff845d560fef825d560,0xf7d8059551dfd81dd560],#[0xf7d8059554f7f8059551,0xdfd805d954f7f8059554,0xdfd715c165dff805d954,0xfef825c165dff715c165,0xdff745c165dfd745c165,0xf7f855c165bff845c165,0xdfd74dc165dfd71dc165,0xdfd81dc165bfd84dc165,0xbff805c565dfd84dc165,0xbff805d165bfd80dc565,0xdfd80dd165bfd80dd165,0x4d40f002ac07800f0000,0x823d08281e006b417a0,0x83930d5c31b0ba02b50a,0x504132048c111c4020f1,0x90199862a17945a91548,0x71f8079b1d347111b306,0x266495d24848d3221483,0xc4cae02ab4a6828689de,0x5cc122f7cbb52de4b462,0xd7a351ccf9333cc9c31,0xf183b4ce973948e0d372,0x534080ff63ec4f873d50,0x5454913143d50a741f50,0x4b55299499920f472918,0xad3ef4f153924d59311,0x2954553dd4c452454555,0x16ad59a162c57e55bd56,0x84b60197af5da97135b8,0xc5662595664458d56265,0x66be9ac76a09a4667e19,0x7045bf06f85bae6dc9b3],#[0x381cbf7279c7d7171c3b,0x9dd3d7495d1f7465d017,0x5e397861dee7711d9175,0xeff7b55ec67a4de72794,0xd7f8dfc27e3df5c7ca5,0xc82ee09181c204f80de0,0x859a14584b611583f60d,0x8d621487aa1c9865a17e,0x7e2f58b522aa89de2448,0xe3d68efa39d8dce3408c,0x4ae91ca45190c240f8fd,0x8f9596544948e502933e,0x2996262597ca5d196c25,0x9d0a72a9bde6cd9a8e68,0x467e79ef67a59e12763,0x828ada232874a14e832a,0x305c084c2c6a4ae901a3,0x50a51705c00662460914,0x8f01123e0b83c0a3054,0x835c9e0f0071185f8bc1,0xa0c94393c0838e1b8111,0xa48b85c1727834614369,0x781098587840660b0dc0,0xa8bc48fc20de27801e1,0xa3617818914031228703,0x362450a31b0bc0c48a0c,0x201c62f031230330bc0a,0x428678490e013e92344a,0x5f028ac91a89c00ce182,0x27c162f03121b1d25102,0xfe258bc1e0518263884,0x4d18605c2783c0c15186],#[0x80c5c486c80102f83c08,0xc17028d8924438289143,0x780c6098c8ba08418b12,0x2a370713c0628f45e0e2,0x103e890bf028c8f18178,0x447c062e24644f002e1f,0xa628882f89e051878108,0x47901fc4b1781460b8c1,0x7123a5e830cc17011346,0xc4d18910c330450e031,0x192e42692f41080311fc,0xc6079010065058b89e05,0x8468a40842f82e0f0212,0x2c60b8c17c108f83c084,0x7c278011c10dc107f021,0x2f821103e13c0a30e210,0x1462022c584f028c1718,0xf0070d60b8222c483f8,0x8189108a22c108e8d89e,0xe2b1b13c1e00885c1707,0x2242e1f1713c1e03182,0x881f0bf078089088dc1e,0xfc1c4f028c2e2783c011,0x387d93c10d7028c8f1c2,0x6851186a04c9c2f00a2,0x1c10d70046204780c9a3,0x2870a50bc11438185a49,0xe0a8c8f238c19e052634,0xc9a326874d50433c064,0x927800f288e10065078,0x821ac131b81491c3582e,0x4383f82c6e052434307f],#[0x3068608f041f49637030,0x821ae0524508f0693c06,0x182a30fc10d70042231b,0xd1b801a102f05e0b278,0x70046271387c1a34685e,0x580406b0b46e009c10d,0xc1648d46c161789c38d7,0x6143423e00782c2d1b81,0x178186a48e1ae0b27814,0xc1c1702921b1c19822a5,0x71705c1a1f030c487c0b,0xdc548702921f16391362,0x11278d82c302f83c0a48,0xf0705c0278e1fc170092,0xf4508f029382183e86a4,0x490f8945e0706921f141,0x6083f86e0f0292304780,0x19345c10c820df00422,0x4522f0437c0118a1710f,0x1c15170c407c9682e008,0x2783c0a28f1a6071387c,0xb44b1b801e143f82c33,0xf0a1fa162780c60f0c,0x2f8146e0c246e0e2685c,0xbc2d1b83c0c4b087028,0x9e00705e0d0b13c00e0a,0x1187458830b804f068b8,0xc3887010e211c421b463,0xf0b0345e032436486d88,0x41b4470192211c39100c,0xa318411e04419244438,0xc456170220c9108d451],#[0x146c48f860b51780c209,0xf011221141fc110b0b8,0x8b85a362783c0610c0fe,0xbc1a1618810a27800f08,0x2f0780231a34c0e270f0,0xb8664f0781421c424b4,0x1491b8586e0524322887,0x370781491b0b8605f078,0x350662b011783184385c,0x8830d828b62a0e050614,0xd1e188434c0c2081a0b8,0x2e0f1106170888c34d25,0x8830d03c2e18441e210c,0x23110400021200423400,0x3113018a208c44c06308,0x6261440e84d82460d0a2,0xd0883c2b0d8306103813,0xa0d89020f86171184170,0x4381922104802878261,0x59043c244ca10b0f080b,0x50c50f04e82460d0b130,0xa192084d8c282e82c023,0x1f6006a8822692e8f0c3,0x4419004610682e0f2888,0x8c1c108066008830d03c,0x1107e08361e0a0c18783,0x60b6185c00d04c41084,0x17801a083ec40a3440a3,0x17c061860b6230587c0,0x821fe031031188989c01,0x168628703645a204c50d,0x430e82e8843101744601],#[0x801d0d05410d881c09b1,0xe20843e1b62d0c50ed05,0x22083e1a27861f0b8449,0x461844461111801a0c80,0xec00f8606a207c302b00,0xc50c421f0d1018b44181,0xb0c3a1c0db0704287d80,0x62084307847041b0f041,0xd1028a187c3545e00806,0x31416c46186210d31038,0x1506c2830a1a61301178,0x584210c3e1a606104458,0x220f6108231130184201,0x7400816c1a010e842884,0x3a0110841c6881420c2,0x3542e0081f6204176250,0xe21a106130590d822084,0x205b058618441e210c2,0x36c2a18a1d0e308310b1,0xec2a2081107b0831087c,0x858410843]]
def g253H8 := limbs80 #[#[0x4028108504f3402c0000,0xe74200550348f2600001,0x14900e6c204018d17d10,0x8f0f810114101307608a,0x500089b339aa05c2703b,0xf1f000525942000eb243,0x4d095988d367309000,0xe2069bc34f92397ccc90,0xa38000118b2c0005b437,0x518bf958029f0ba0f919,0xb270000c63000e4ad17a,0x944000cc3e9dca322,0xb679c447e9f2d185d13d,0xb8520000007280000002,0xc0809a000d5036,0x549c6539623c800074,0xb8bc54db34ced450,0x47f080000e76f5ca0200,0x7000000bc77adcb1781,0x3953401205af4bb4434,0xc8700046070100000,0x26234462641a6af73,0x8214e2ed316c8532e4d0,0xb0e000d8e598c9228a5a,0x379a6d4c933000000000,0xdb886f000fbe000386d,0x8663bd00,0x5f704a36000264871977,0xaa8801200086c0100567,0xe2449e10c405e1b00041,0x3469cf4b0aaa64e,0x143a000ec4ea24c00000],#[0x811000d6e0000005caea,0x63fd5b78c469000f1c,0xe00012a10d185b680000,0xa2f9c5a7dc2d0001cdc3,0x55000ca92cc2169c6ab7,0xaa4f5a74800000031da,0x91000482897bbaa6100,0x1e000000f84f79000000,0x9c22000fb9813a530002,0x30f6d000294a7868,0xabe27a21000490975000,0x7a4b000000000615000c,0xac170a17b00000035,0xa547a000f9945eeac000,0xe27200099313b000db5f,0x9834cb0a70009a]]
set_option maxRecDepth 16000 in
def g253D9 := limbs80 #[#[0xd6558f6eb1ac377dcd51,0xa21fd54510ff2c0886d,0x10bfaea887dd63443fab,0x5ff76442febb2217fdd5,0xeaa281f758d40ff2c0a0,0xd540bfaeaa07bd64503d,0xa85ff76502febb2817fd,0x3eeb1aa17fdc550ff2c0,0xf59550bfee8a877d5454,0xe2b05ff76542febb2a1d,0x582ffba2c1bf59160bfe,0x37fdc151bfeeab06fd65,0xbee6a8fdd63547fab0aa,0x76546febb2a3df59551f,0x2c77fdd561bfee0b0dff,0x3fbaa8b1fdd7158feeb8,0xbd64553eebaac7f75d16,0xb82cb7f5d954efacaaa7,0x510bfee8b2dff71596ff,0x7fd75503feb2a81ff59,0xfeb8aa1ff58550ffaeca,0x5d950ffae8a87fd64543,0x2b07fd71583fea8ac1ff,0x83feba2c1ff55160ffee,0xffdd560ffaeab07ff745,0xae2b2fff70597feb82cb,0x4597feba2cbffdc565ff,0x7c02e810803e0007ff7,0x84a82160f006a82c812e,0x61f00e486a83161640a0,0x68ab850626c12488b841,0x63641a28ca860e2e416],#[0x1690587f63e01de8e887,0x9964b024a91f88be4442,0x2b69558a6e52027e9398,0x8c4e6042f29718b46588,0x43789b48d6668c336992,0x38f5e7903ba9d48e5e71,0xa8442a18906e8183f69f,0xcc6c285c0891e3891868,0x704a2f17084302248140,0x2246c719c210c9c04518,0x2c0c1091b18180b17070,0x1b220b030425182c6058,0x6246c68541501282c089,0x64589c0c11319160b030,0x13141609182f07022470,0xf1707011a248c1c0891b,0x650c582c04689248c085,0x185e0b0700243c797411,0x2249c51782c1c009111f,0x171888685e0b183f070,0x14470702248064589c1c,0x54689c1c017188c5e0b,0xb14086c6b27061701188,0xb24651b00a82c0c1491,0x49c1c00f1d046e6a1542,0x6201b030524685c61a82,0x7008051b1ac9c182c04,0xc1c01a18682e091a1727,0x60a182f03052470bc946,0x24723c511c182c0491c1,0x45c082187e0b161b0305,0xe1b270517008c806c9c1],#[0x2c606c14289c01e1a082,0xc0891b1e161703042518,0x1891b180702246c74510,0x15182f030624705c2c0c,0x70070601c0891b1e140a,0x24589c1c01c18150b062,0x1920141c5b0064404860,0x640661b01253c80849c0,0x404870a43c01924150a0,0xc0090f11143909145b00,0x891b091a2707003c6c1,0xb2707021880fc211c1c,0x850b86c0c1491c842e15,0xb2086170a1b030524702,0x1a24821134582c1c0891,0xc1c02220845e0b051701,0x70627008c71a17c60f89,0xb854682c1c049245f144,0x784f1b0305246871a1c0,0x8881a85c149c082511c,0x1c01a18685c3f1927070,0x9170701246c8c4c346c,0x13c582c1c0491b207c7a,0x64f1f146f0701247c61c,0x527008c71f82c149c08,0x2c5c1c0491f1c5c4717,0xc6b130e0b06191700a06,0xa021bc3c1c045231c7c6,0x846c6a1b130e17050b00,0xc8051bc4c3c1c0422120,0x9211878730a170701246,0x3f052700447c21bc1c04],#[0x6c2c1c04921188708]]
def g253H9 := limbs80 #[#[0xc5b48d182818c000428a,0x140e80001010408c813,0xc01106803013834c832c,0x20d019409c44189830a0,0x824b00b831e646820402,0x26480005ec8ea5324d50,0xa601ec483cf2b4000000,0x785a54c570578003,0x5d9fc11540007b300000,0x28624c1c3600002047b5,0x3bb52c80024fa4af81e,0x6499a6e370004317e180,0x96b437afc39910dc8800,0x936461380045b91d0000,0x1121e7c51e0900071,0x8a0003809e883c721e9b,0xf80034ba6a65ac0503ba,0x80000028d81480781a59,0xa5e2a8006c553d452427,0xde4e1236a53ccd2f28b4,0x73e14c03ce88edc6c745,0xd66ce9d541a8b2a2d944,0x17957a3938fd3b89b638,0xe8ab201e22b180013038,0x5a65f6907c249cb8683f,0x1161e5337fd8d95fac3,0x9bedb82abf6a8d13692d,0x7a0ebd9e69e2e84de0,0x318caab39f3c5f9e5670,0x6684dd1a103938d43ac9,0x6b68528001cdddb4c0,0x258f5aa612c4692d6bf0],#[0x5d0d003a2eb3c6348,0xc0c0c62263249700fc46,0x1827328cb605820e7558,0x956c5fb49399d3a2a99c,0xb5800103f18aaea34ec3,0x55cc832110666ae1029,0x80000046100040771180,0x9dec4b47be984a559342,0x859bf97a658000860b0b,0x2415e0005a971411]]
def g253D10 := limbs80 #[#[0x60ff543fd40ff443dd63,0xfd64ff553fd61ff547fd,0x4626e3561d46e00ff597,0x484585243401fdfbfc7d,0x12393171a28281044900,0x292160c01cbc68a0a0c0,0x449114149821a00c6a30,0x1a0411241e0d08d85810,0xd1a140130478c705c584,0x490b0600d16141802488,0x1083]]
def g253H10 := limbs80 #[#[0x880005f0700077e01c,0x93ea6800187001c65520,0x6e500069393a4b000506,0x37214006b981,0x19000000420000002400,0x2a3000001320,0x30012d25380029360160,0x6143fdb22e477af860ab,0xe558763ae94002158b19,0x800000000c72091a8085,0x7a98c7ab0e56d0c70802,0xa567e00151800f88d1f9,0x96a2e380829706003cb6,0x437d152a613447dbc1e,0x7210000000000000,0x48717000002c152678a0,0x43c000001]]
def g253D11 (j : Nat) := if j=0 then 0x30a11200237f else 0
def g253H11 := limbs80 #[#[0x3d2c524025840011c01,0x14802a2140000cc]]
def g253L : Nat → Packing
  | 6 => (38,5,6,0,0,8,0,g253D6)
  | 7 => (210,4,6,0,0,13,0,g253D7)
  | 8 => (214,3,6,0,0,14,0,g253D8)
  | 9 => (75,2,6,0,0,13,0,g253D9)
  | 10 => (10,1,6,0,0,9,0,g253D10)
  | 11 => (1,0,6,0,0,0,0,g253D11)
  | _ => emptyPacking
def g253I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 9 47 6 10 6 0 g253H7
  | 8 => lookupWord 52 293 6 12 8 0 g253H8
  | 9 => lookupWord 53 251 7 12 8 0 g253H9
  | 10 => lookupWord 18 113 4 11 7 0 g253H10
  | 11 => lookupWord 2 17 1 8 4 0 g253H11
  | _ => fun _ => none
def g253 : Forest := ⟨253,11,fun i => g253Y[i]?.getD (0,0),g253C,g253A,g253L,g253I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P6_0 : block g253 6 0 38=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g253B6 : block g253 6 0 38=true := g253P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P7_0 : block g253 7 0 21=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P7_21 : block g253 7 21 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P7_117 : block g253 7 117 93=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g253B7 : block g253 7 0 210=true := (@block_merge g253 7 0 21 189 g253P7_0 (@block_merge g253 7 21 96 93 g253P7_21 g253P7_117))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P8_0 : block g253 8 0 18=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P8_18 : block g253 8 18 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P8_114 : block g253 8 114 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P8_115 : block g253 8 115 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P8_211 : block g253 8 211 3=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g253B8 : block g253 8 0 214=true := (@block_merge g253 8 0 114 100 (@block_merge g253 8 0 18 96 g253P8_0 g253P8_18) (@block_merge g253 8 114 1 99 g253P8_114 (@block_merge g253 8 115 96 3 g253P8_115 g253P8_211)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P9_0 : block g253 9 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P9_3 : block g253 9 3 49=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P9_52 : block g253 9 52 23=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g253B9 : block g253 9 0 75=true := (@block_merge g253 9 0 3 72 g253P9_0 (@block_merge g253 9 3 49 23 g253P9_3 g253P9_52))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P10_0 : block g253 10 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P10_1 : block g253 10 1 9=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g253B10 : block g253 10 0 10=true := (@block_merge g253 10 0 1 9 g253P10_0 g253P10_1)
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
  · exact g253B6
  · exact g253B7
  · exact g253B8
  · exact g253B9
  · exact g253B10
  · exact g253B11
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253G : graphValid g253 (boundsBefore K251) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low253 : Lower true (varsX 253) (graphGoal 253) 12 := lower_forest (g:=g253) (i:=0) (hints:=132099) (before_sound K251 V251) g253G g253T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K253 := extendKnown K251 12 [(253,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V253 : Known true K253 := extend_ok (m:=253) V251 low253 (by decide +kernel)
def g254Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffff12192e9381221b,0x4a88000000003f03f03f])),(BitVec.ofNat 152 (word80 [0x14f00102c9100221a,0xa891451451451451451]))),((BitVec.ofNat 152 (word80 [0x903d42da4465c24,0xab100000fc0000fc0fc0])),(BitVec.ofNat 152 (word80 [0x26103142d80045404,0xaa105145145145145145]))),((BitVec.ofNat 152 (word80 [0x725cb6c123cc8d4,0x24c0003f000fc0000000])),(BitVec.ofNat 152 (word80 [0x178304cb6c122c48d4,0x20c030c30c30c30c30c3]))),((BitVec.ofNat 152 (word80 [0xfff2848a9aea823ba4,0xc460000003f000000fff])),(BitVec.ofNat 152 (word80 [0x2400848a92628208a0,0x446228a28a28a28a28a2]))),((BitVec.ofNat 152 (word80 [0xdc475463f04d19,0x19000fc0000000fff000])),(BitVec.ofNat 152 (word80 [0x38009c434062f00901,0x1100a28a28a28a28a28a]))),((BitVec.ofNat 152 (word80 [0x117248058398182,0xb33ff00003ffff000000])),(BitVec.ofNat 152 (word80 [0x400013040008118100,0x9114c30c30c30c30c30c]))),((BitVec.ofNat 152 (word80 [0xce8327305040262,0x14f7fffffc0000000000])),(BitVec.ofNat 152 (word80 [0x800c60201205000222,0x4230c30c30c30c30c30]))),(0x0,0x0)]
def g254C : List ColumnInfo := [(8,0,246,0,10)]
def g254A : List (List Nat) := [[],[33,84,118],[65,82],[81,66,118]]
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
theorem low254 : Lower true (varsX 254) (graphGoal 254) 11 := lower_forest (g:=g254) (i:=0) (hints:=554787904) (before_sound K253 V253) g254G g254T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K254 := extendKnown K253 11 [(254,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V254 : Known true K254 := extend_ok (m:=254) V253 low254 (by decide +kernel)
def g255Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x7f8000007f800,0x7f80007f80c8d4ee41f])),(BitVec.ofNat 152 (word80 [0x282828282828282828,0x282828282804880ac013]))),((BitVec.ofNat 152 (word80 [0x7f80007,0xf80007f800300010c063])),(BitVec.ofNat 152 (word80 [0x1a1a1a1a1a1a1a1a1a,0x1a1a1a1a1a1000004023]))),((BitVec.ofNat 152 (word80 [0x7f80000000007f8,0x7f800000160230043])),(BitVec.ofNat 152 (word80 [0x989898989898989898,0x98989898980020010043]))),((BitVec.ofNat 152 (word80 [0x7f8000007f8000000,0x7f8c2118c37ad])),(BitVec.ofNat 152 (word80 [0x505050505050505050,0x505050505040000037ac]))),((BitVec.ofNat 152 (word80 [0x7f800000000,0x7fff804fc1e0fc908])),(BitVec.ofNat 152 (word80 [0x646464646464646464,0x6464646464ec0c0a8908]))),((BitVec.ofNat 152 (word80 [0xf800000000000007ff,0xfff80000000060300830])),(BitVec.ofNat 152 (word80 [0x414141414141414141,0x41414141400040300000]))),((BitVec.ofNat 152 (word80 [0x7fffffff800,0x7007fc031c2])),(BitVec.ofNat 152 (word80 [0x818181818181818181,0x81818181810062c00040]))),((BitVec.ofNat 152 (word80 [0xfffffff80000000000,0x7ff80003e00])),(BitVec.ofNat 152 (word80 [0x60606060606060606,0x606060606bb00000800]))),(0x0,0x0)]
def g255C : List ColumnInfo := [(2,0,253,0,12),(4,0,251,0,12),(8,0,247,0,12),(32,0,223,0,12),(1,0,254,0,11),(16,0,239,0,11),(128,0,127,0,11),(9,0,246,0,10),(64,0,191,0,10),(3,0,252,0,9),(17,0,238,0,9),(66,0,189,0,9),(72,0,183,0,9),(80,0,175,0,9),(130,0,125,0,9),(136,0,119,0,9),(0,2,141,112,8),(0,4,75,176,8),(0,16,169,70,8),(24,0,231,0,8),(144,0,111,0,8),(2,16,169,68,7),(64,16,169,6,7),(65,0,190,0,7),(128,4,75,48,7),(129,0,126,0,7),(72,16,161,6,6),(81,0,174,0,6),(133,0,122,0,6),(161,0,94,0,6),(192,0,63,0,6),(89,0,166,0,5),(131,0,124,0,5),(145,0,110,0,5),(208,0,47,0,5),(129,8,54,64,4),(26,128,0,101,3),(193,8,54,0,3)]
def g255A : List (List Nat) := [[]]
def g255D7 := limbs80 #[#[0x33a6edbb4e8d9758140,0xd60cadbb8edba365d605,0x87583a36e1fa6e839361,0x361d60c6dba66d3a0e4d,0xe41875831b6e9bb06939,0x839361d60d8dbb7edb93,0xba0e4d87583a36e9f96e,0xb06939361d60e8dba7e9,0x6ec3a3651875832b6e9b,0xeebb06199321970cadbb,0xdbc0ee98664c865c38b6,0xc96ecfb06199521970e2,0xf25bc0ecd86654865c3,0x5c34b6ee7b0e8d862197,0xd974d2dbb3ec3a961886,0xd805db327edbb4e8d905,0x9360176e4dba7e5ba0e4,0x6c1803003936e5fa6e83,0x918cb44b210cc54210f0,0x6100815ca551265147b3,0x66103384080066156104,0x3384b841361039855841,0x78413e10282ed0e13610,0x8e080f840ce12e10482f,0x623838]]
set_option maxRecDepth 16000 in
def g255D8 := limbs80 #[#[0xe0b064f176687945c160,0xe4d87583678bb343ca2,0x74dd0726c3ac19b6e9ba,0x69dba7e839361d60d5b,0x7845c346fd3f4dc9b0eb,0x43720bb2e14f5ecd8664,0xd9b321b905d970b9d364,0x5c2e3cda90dc82ecb85c,0x26432e1cb6ec18664c86,0x6199521970c5bf74c33,0x92fd9b0cca90cb8727bb,0x32e18b7ea7a3618865c3,0x39361970c5bf67d4b0c4,0xd3f4dc9b00bb65dba7e8,0x1be6e93a365d6050326f,0x58140ddb74dd1b2eb028,0x46cbac0a06bdba8e8d97,0x6edba365d605037cdda7,0x40d7b771d1b2eb0281bb,0xbac0a06ebba6e9197581,0x1a45d97058357dd474cc,0x97760bb308ba2c1f2ee9,0x8b06b9fa4e8d8761160f,0xe41875835cfda746c3b0,0xfc9f20c3ac1db6e5b93,0x67d9a4e4f9061d60f3b7,0x87583b6ddb727c830eb0,0xa720c3ac15f6ecd94e41,0xb966939061d60adf76cc,0x83c7dc3f2dc830eb066f,0x6c3ac1db6e5ba0e4d875,0xe839361d60ddb74dd072],#[0xedd8329c9b0eb079db87,0xac15b7ed994e4d87582b,0x9361d60f1bf0fcb726c3,0xa741c9b0eb078df87e9b,0xdb6e9ba0e4d87582becd,0x1d60cfb74dd0726c3ac1,0x9c9b0eb057dbb0693936,0xed9a4e4d8758336fd334,0xcdbf4dd2726c3ac15b7,0x30eb066fb96e819461d6,0x93e418758336fcb746ca,0xb72dc9f20c3ac1eb6e5b,0xb07adbb6e4f9061d60e7,0x4187583ceddbf27c830e,0xcca720c3ac16f6ecd94e,0xadb96e839361d60b5f76,0x75839edcb741c9b0eb07,0x726c3ac1eb6e9ba0e4d8,0xa7e839361d60d7b74dd0,0x2dedd8329c9b0eb079db,0xc3ac1ce7e5194e4d8758,0x539361d60b5bf6cca726,0xfd2329c9b0eb073dbb06,0xc1cb7ed994e4d875839c,0x361d60e73b49ca726c3a,0x349c9b0eb05bdbb06939,0xb7ed9a4e4d8758356fd3,0xd60d5bf4dd2726c3ac16,0xc9b0eb078dfa7e5b9361,0x91a4e4d87583c6fd3f4d,0xd7b747d0328c3ac1ce7e,0xeb06bbba4e819461d60],#[0x6518758357dd3740ca3,0xf4dd1b28c3ac1abee5ba,0x6bdbb0e8d9461d60d5b,0x18758356fcb746ca30eb,0xca328c3ac1ab7edba365,0xdba3e819859170d57f4d,0x5c33ddd2740cc2c8b867,0x31b22e19f6ec3a366164,0xe8d98d9170cfb747d03,0x9edd1f40cc6c8b867dbb,0x22e1cf6ec3a3663645c3,0x17661170f1f70dd02ecc,0xd2746c3308b874fb96e8,0x1ae7ed3a3619845c35cf,0xe1170ebe760bb323c22e,0xcc8f08b873f3b061991,0xee1ba0651765c39ebd9b,0x70f5b747d030c432e1b3,0x310cb872fba9e8186219,0x7a3618865c3d6dd8746c,0x5bf73d1b0c432e1cb7ea,0xcb872fbb0ea58621970e,0xe41865c396fd9f52c310,0x6fc9f20c32e1d76e5f93,0x57dbb36539061970ebb7,0x865c3aedcbf41c9b0cb8,0xa726c32e1b76e9fa0e4d,0xba7e839361970afb760c,0xc2bedd8349c9b0cb875d,0x1432e19f6ec3a3662865,0xe819760364e7b761d1b3,0xedd8746cbb01b26bdba3],#[0x2e9b67e93a3641765d35,0x905d974d9bf4dd1b20bb,0xa746c82ecba6d9f94e8d,0xb37edba3641765d36cfd,0xd974d3b971d1b20bb2e9,0x8c82ecba6cbfa6e51905,0xe5b93e01805db65fd374,0x6ebb72fc9f00c02eddb6,0xb00bb74fb97e5b806017,0xa0e4d805dbb6dcb741c9,0xb72fd0726c02edbb6e9b,0xbb6ddba7e839360176eb,0x4d805db9cfca309c9b00,0xfcb726c02ed5b7ed994e,0x4dfa7e5b9360176e9bf2,0x5dba6fcbf4dc9b00bb7,0x726c02edb37e9fa6e4d8,0xa46139360176e73f08c2,0xb36fd3349c9b00bb739f,0xc02ed5b7ed9a4e4d805d,0x9b9360176cdbf4dd2726,0xfcb746ca300bb74dfa7e,0x5cc4d83e42c414c00336,0xfcbb0abc9c88a87886c0,0x530d1ed0ccfacee4df0c,0x40d3f53b139938133d32,0xe95a558d549505495425,0x57557116cd6b56716015,0x9b597192d8e98a58617c,0x39af5ab1a99a55a119cd,0xdc4dc09bc5badb95b51b,0xed9e95e25de1d71d2dcb],#[0xb607202dfe9fa5f61f1d,0xe27a2361f21ae16a0fa0,0x4da46a4263e23463022b,0x6672268666e62a5e654a,0x29ae96a9268b68468027,0xbb6b72b2eaeaaa6a369f,0xc6e2ade6d1ecdac6ac26,0x71931230b306efa6f0ae,0x39b3573132cf28b2471d,0x4b53351b4d749344f3df,0xb6b767362f5eb5a75635,0x8bf87b83779b7577136f,0xbe1a8d1f9fb9b7947903,0xf0fe111424a7704f83f0,0x8c35c0710d1b62fc1e09,0xf862d84f83b0be07c3e,0xec2f81f0c5e8db0be0fc,0xc26c2f83f03e18a45fe0,0xf87f086f0de13e0fc313,0xc0f8653061a3b17e0684,0xfc0f840745d8ba13e0f,0xc0bfc1f81f0e260bb17e,0xe1bc2417d85f07e07c31,0x41d140bfc1f80077e10b,0xe0fc0f862417785f07e0,0x19e1784f83f03e18d70b,0xc613e0ec2f81f0c8b8de,0xe1b617c1f87f008d8,0x5e08100030804001c282,0x805081436081788c11c,0x20206c0050bdc2080b84,0x4c25841917d8417c2064],#[0x7610270013800ec207a3,0x401840c8707610206c20,0x8408003c004022e08c20,0x3717e10470b60057081b,0x258416c2048bec20b610,0xec2040f83b081d840cc,0xd84091b040f8207c103e,0xec2040f83b081236b082,0x841fc205e1027141d840,0x77082b840fc204096c5f,0x8234377083984f00243,0x50db86b841816101f84,0x8413c2050bb86b841d84,0x2d00100c0a4868a1217b,0x1384091bf841019040f8,0xa17b8415c005e103210,0x11e10805c142f7082b84,0x1950970835080c17f0de,0x2584211930db083d080a,0x8c26c208c20245cc24c,0x800a1930e118704c36c2,0x170a0b8505c2837081b,0xa0d0607c28285dc28409,0x311c188e0c4704000010,0x40ec204038009c006238,0x308131a0f44984b083d8,0xd8409c503e10c2048d82,0xf001]]
def g255H8 := limbs80 #[#[0x58848970a005c30a4008,0xb7003cee3006300000,0x9200a0fb401c41360950,0xef00002]]
set_option maxRecDepth 16000 in
def g255D9 := limbs80 #[#[0x7658140f2e5d97458140,0x8f7e8d985d940e3e61d,0xb945c1609fc687945c16,0x60bb668c965c160d3e5d,0x869859170b9e694965c1,0x1708f7e8d98d91708fd6,0x688865d970c7d5d991e1,0xd970b3768c865d970b3b,0x76199321970b1f694865,0x21970c9f6199521970cb,0xf7e8d98a19708bfea586,0x458140fae5db94581408,0xfae6917658140bee69f9,0x9758140ebeea17658140,0xbbee999758140bf6e8d,0x9985d940af7e8d985d94,0x60aef69f9461940abfe9,0xdb845c160f3e5d9845c1,0x160f3e5d9945c160f3e5,0xe99945c160dbee59945c,0xc160bfc687945c160bbe,0xee59765c160f3e5db945,0x5c160f3e691765c160f3,0xbeaa0965c160f3ee9176,0x45d160f3ee1f965c160b,0xf3ee81765d160f2f5d98,0x985d160f2fe91765d160,0x9f7e8d985d1609fee81,0xb985d1609bfe99985d16,0x60af7e8d87611609bf69,0x8197e1160af7e8d87e11,0x960e7ee1f905d9609fee],#[0xe1f905d960bbe693905d,0x1d60bbee81945d960f3e,0xee5b9061d60df6e4f906,0x61d60e7ee1f9061d60db,0x77e1f9361d60db7e5b93,0x361d60df6e839361d60e,0xe3fe1f9661d60db7e9b9,0x9061d60ef6e4f9061d60,0xcfee5b9061d60ebee5b,0x39361d60ef6e839361d6,0x60cf7e539361d60cf765,0x5b9361d60eb7e5b9361d,0xd60eb7e9b9361d60cf7e,0x6939361d60e77e9f9361,0x1d60cf7e939361d60cf7,0xee819461d60cf7e9b936,0x61d60af7e8d9461d60af,0xfee819859170abfe9994,0x7d91709f7e8d98591709,0x9fee8198d9170d7ee819,0x98d91709f7e8d98d9170,0xcf7e8d98d9170cfee81,0x97661170e3fe19766117,0x70af7e8d8661170d3fe5,0x1991e1170d7d5d991e11,0x970af7e8d86e1170cfd6,0xe1b905d970f3e21b905d,0xd970b7ee81945d970f3e,0xee818621970b3faa4865,0x21970eb7e8d8621970eb,0xf6e4f9061970cbfea586,0x361970d7ee5f9061970d],#[0xdf6e839361970d77e5f9,0x98a1970d77e9f9361970,0x4cf7e8d98a19709f7e8d,0x19760364aef6839461d6,0x64af7e8d9760364afee8,0x8d905d974af7e8d9061f,0x974b3fe99905d974b77e,0x6839461974b6f683945d,0x176dbee5b80601769ef,0x7e5f9360176db7e5b936,0x60176cf76139360176d7,0xb7e9b9360176cf7e1393,0x660176d77e9f9360176d,0xafe68384e0176d3fe5f9,0x9758140ff6e8d9758140,0xfbee999758140feee91,0x9845c160efeea1975814,0x60fbee5b845c160fbee5,0x818761160fbee8176611,0x160ef7e8d8761160efee,0xe998761160eefe918761,0x1160fbee8176e1160ebf,0x7e8d87e1160efee8187e,0xe1160ebfe9987e1160ef,0xafe51945d960dfee8197,0x61d60ff6e4f9061d60f,0xdfee539061d60dfe6539,0x9061d60bfe6939061d60,0xdfee5b9061d60fbee5b,0x39361d60ff6e839361d6,0x60df7e539361d60df765,0x5b9361d60fb7e5b9361d],#[0xd60fb7e9b9361d60df7e,0xe939361d60df76939361,0x1d60df7e9b9361d60df7,0x7e8d9461d60bfee81946,0x61d60dbfe599461d60bf,0xbfe5b9461d60bbfe9994,0x61d60efe6539061d60d,0xefee5b9061d60efee539,0x9361d60ef76539361d60,0xef76939361d60ef7e53,0xb9361d60ef7e939361d6,0x60ef7e9b9361d60ef7e5,0x8d9461d60efee819461d,0xd60eefe519461d60ef7e,0xe999461d60ebfe599461,0x9170ebfe5b9461d60ebf,0x7e8d9859170dfee81985,0xd9170defe919859170df,0xf7e8d98d9170dfee8198,0x661170f7ee817661170d,0xbf7e8d8661170bfee818,0x8661170befe918661170,0xef7e8d8661170efee81,0x19661170eefe91866117,0x70bf7e8d9661170bfee8,0x8176e1170dfd69991e11,0x170efee8186e1170f7ee,0xe1b905d970ef7e8d86e1,0xd970f6fe51945d970f7e,0xfe1b945d970f3fe19945,0x61970ff6e4f9061970f3,0xfee539061970dfe65390],#[0x361970f7ee5f9061970d,0xdf76539361970ff6e839,0x9361970df7e539361970,0xf77e9f9361970f77e5f,0x39361970df7693936197,0x70bfee819461970df7e9,0x8d98a1970bf7e8d94619,0x364efee819760364df7e,0xe8d9061f64ef7e8d9760,0xd974f77e8d905d974ef7,0xfe91905d974f6fe51905,0x60176f3fe99905d974f6,0xbee5b8060176ff6e4f80,0x360176f7ee5f8060176f,0xef76139360176ff6e839,0x9360176ef7e139360176,0x6df7e539360176df7653,0xb9360176fb7e5b936017,0x76fb7e9b9360176df7e5,0x9f9360176f77e5f93601,0x176df76139360176f77e,0x6939360176df7e139360,0x176df7e939360176df7,0xfe118460176df7e9b936,0x60176dbfe598460176ee,0xbfe598460176eefe5184,0x460176dbfe5b8460176e,0xbf7e8d9460176ebfe5b8,0x9460176dbfe599460176,0x6dbfe5b9460176bbfe99,0x38461176f3fe5f966017,0x403e00ac0158000bef68],#[0xad826a08a01e6066814,0x18041e0f4839a0d38302,0x505c815f053a13b84ac1,0x877c1cc06ee1ab066018,0x94e24088c021f881e1f4,0xc2b28a7e28a09dc2668,0x83298c643060bcc2db0b,0x3918dfa36b8d6234a8ce,0xfc0fb83d88f163b50e92,0xc913a44090b641f90463,0x12c649e923848011b445,0x45c50693ce4e593544c2,0x4c57b15aa55514f452a1,0x85f717865d116e45a616,0x666996264598d461f982,0xdb1b206b79a9269199f0,0x49cfc72c1c5a7039bb86,0x9ec479b9e2c7781d9475,0xb481ca0267f19f7a7c6,0x7288ea1e4866214c842a,0xa8dda3488c923008ad22,0x90ea4028f7a3c48eaa39,0x3d24da93024a69232468,0x3259495c255694ca50e9,0xa662992262e982a5f097,0x7449c5a6f29b3a6aa9a1,0x129fba7d49ec27969da2,0x2a2a2884a1aa850a0da8,0xa60295ca4928f6a3728c,0x9b2a3ea8429eca72299a,0xc2b0caba2aceaaaaa86a,0x2bf8af52bb0ae32b5eac],#[0xce4b302ca6b1e2c54b07,0xbcb63ad74b542d2cb422,0x2ba12e56b8a2e04b782d,0xbe3af74bd1af0ebbaaeb,0x1eb042c07b004bf5afb2,0x5b0fcc3630c8c2bb094c,0xb198c5fb164c52b130c4,0x25cc893200c79b1ccc6c,0x3ecc6b2f6cb732c2ca53,0xd01b3ecced3390cd633,0x682bc0f0bc1f0c162342,0xaf0bc1f03c3058805cc,0xb84f07c0f0f0d1c08319,0x1346f07c2f0e8d1c12d1,0xc13c1f0bc0f0c16214ec,0x6237c1f0fc023075180d,0x17237c1f03c2074605f4,0xc7e1b84f0bc1f0e4d18,0x5347e1b84d1648f07c0f,0x3f087a2586e13c2f07c3,0xc31307061c1e13c0137c,0x3c20745c1b84137c1f03,0x37c1f03c31307137c1f0,0x137c1f03c2074605f841,0x6e13c1f004df0fc21c17,0x87e1b84f07c0f0e4d1b8,0x5c682bc105fc0f0fc205,0xf08161e0af07c0f0fc20,0x3f08161c1bf07c3f010a,0xc0f0f0a1c1bf07c042bc,0x3c3f0b0a1e17b1b0df07,0xfc0a281a1817067c1f0],#[0xf07c3f03c2a286d1bc1f,0xdf0012f060af0bc31d48,0x46f048df03c3f0a0a220,0x3c1f008df0fc205c705d,0x508df07c0f0fc2828915,0xf07c3f03c20646058191,0x706fc1f03c3f0a0a181b,0x4786dc0f068df0fc2064,0x34605bc1f0fc0f088d06,0xf088d1fc1f0fc0c13c22,0xf090a2054c13c1f0fc0,0xc2c1072220891bc1f0fc,0xfc206c6f1746f07c0f0f,0x3c3f08162704f07c0f0,0xf0fc2278405c0d51bc1f,0x61f4505d8405bc107bc0,0xc21c1e42bc1f0fc0f081,0xc1a1b45d1bc0613c1f0f,0xfc24346e1346f07c0f0,0xf07c0f0d0d1b46f07c0f,0x7b1bc1f03c386c5d1bc2,0xc750a54d17c1f03c385c,0x87d17c1b1bc0f0fc205,0x587a130d51bc1f03c3f,0x206c6717c106fc0f0fc2,0xc3f0a0d1946f07c0f0fc,0x684f03c3d18706fc1f03,0x7c0f0f46f08885dc2f0,0xf07c0f0fc21417f1684f,0x7b0bc1e13c0f0f46201b,0xc5b0bc1f0117f0c56211,0x1bc3e107d1bc1f03c321],#[0xf03c3f085622c2f07c0d,0x6d19c2f07c0f0c506fc1,0xfc21f46f17c1f03c3f08,0xec21746f1684f07c0f0,0x7fc0f07c31b46f07c0f,0x6e13c1f03c36347e118d,0x46e13c1b0bc0f0c630b4,0x917e12c2f07c0f0d8d1f,0x45c5d1b84f07c0f0ec21,0x1f0fc06347b0bc1f03c3,0xc1f0fc06346d1b84b0bc,0xb84f07c3f018d1f46e13,0x6e8df03c1f0fc21f46b0,0x86dc2f07c0f0e8d24120,0x5f03c1f0fc22012e1025,0xc0f0fc2428604b8406ec,0xa4df07c0f0f0a264df07,0xa48f03c31c2386dc2e1,0xf03c3f0b861f45613c1f,0x1f0384923c32584f0648,0xc0f0fc21a1770b86d17c,0xb45f07c0f0c805e48f07,0xfc2f00191f849221770,0x853c3f07c22214137c1f,0x1f03c3934832345e13c0,0x4df0819181f86714c2bc,0x419f0d4df087b03c1f0d,0x7c3f024d864546cc0f0,0x71506f07c0f0fc20648f,0x5c1bc1f03c3f081922c5,0x84f07c3f03c29347716c,0x7c1f0306f0fc2e107851],#[0x1c17f07c0f0e48f086f1,0x21f8485fc170bc0f0e48,0x86238405c4df07c0f0fc,0xc7b1619a11c2f07c0f0f,0x5c806484f07c0f0fc206,0x1fc5b091961bc1f03c34,0x7211971786f07c0f0c87,0x661bc5612c2f07c0f0d1,0xfc31f86f064df03c361c,0x7c31f868664df07c061,0xf081719c404bc0837c2f,0x6f0344f0c8e17c1f03c3,0xc0f0f0821c2e1708f06c,0xfc0c34985dc2e16c4f07,0x64785f14e1706b13c1f0,0x83490890df07c3f0bc00,0x7a14a15c4f07c0f0fc2,0x6049c4f07c0f0fc28347,0xf442244f07c3f03c2088,0x6c6621c5b0b86f07c0f0,0xf07c31d86b0bc1f03c34,0xf0d4a1c1f6518dd13c0,0xc3f0386218d30b86f07c,0xfc046c5621c5d12c2f07,0x7c3f03c206c623fc1f0,0x4bc1f03c3f081e1d86f,0xc6217c20ec630b850c1b,0x1bc2614305ec6f0b8512,0xc3d141b0904234206c1b,0x6f0d30a46c28542bc206,0xdf081b0c1b437c242848,0x50c20817f082d1417090],#[0x84034305f450817f0829,0xdc206c285f46708305b,0x2d19c5f0884141b149c5,0x83700170817d1bc20c5,0x3519c5095414c245f46b,0x8345f46620345f46b08,0x7d183551c5b08345f46b,0x81b0d8851b84b0847151,0x6c205b4610a1b1016f0,0xc306ec50816f081b0ec2,0xf08206dc5f083717c206,0x6c20ec271427141f0817,0x20917b0827141f091b71,0x5c2141b04ac5f08445ec,0x825f081b0c2586c12b1,0xc20c1b04ac5f084f081b,0xa1b1021f081b0c1bb17,0x708250878406c4097841,0x864283e104285c3f081,0xa0e19c530a0c21428292,0x44923c206f4510214510,0xf84f09450f8430a48d1,0x4d0f1404b0a0c120850a,0xe4881b400650a161932d,0xe10c2d024d13c2d001b0,0x4d0c14e104d0d48a102,0xa11c20d061368a0d06a1,0x84a11c508217081b0e19,0xd1961ac20c1905c84f0,0xc21148e11c50c53e111b,0x11945d84b08446517612,0xb0b84534546f84536c21],#[0x429345f081b934309119,0xb8610a19e1040961be10,0x2b10385cc2b183f08170,0x88a0a17b10c2e14485cc,0xb13c2e145b13c26143b0,0x82913c20942910208817,0xa0a42717440c470644f0,0x8245dc5085346c29094,0xc20b44b082d11880b44b,0x71426518d0b44b082d12,0x1f09344151b52ac20d88,0x11762144e1ac21586714,0x5088d08822508dd084a1,0x286b143f0a4406c3f08c,0x5ac5d10c217c206c222,0x44f0ac51422b081b0e1b,0xf44f08205ec5081b05b,0x21407a0d]]
def g255H9 := limbs80 #[#[0x802016090602c0001000,0x20000520,0x31e43a800,0x0,0x0,0x6ae141e8e800000000,0x28000000000000000000,0x48300000049,0x799800034800000000,0x1961320000000,0x10b00000000000000,0x30c000000000000000,0x0,0x58f80000009082f5a200,0x287800000000000000,0x5b50000000920,0x50d0000000004bf80000,0x786,0x7f194090000000000000,0x39b83,0xac80000000041112a000,0x2,0x21533800019,0x0,0x11d8000005130000000,0x34030189380000000000,0x3b1000000,0x18488000000000000000,0x23d80000000002b8001b,0xe38200000000000011f,0x0,0x3900000],#[0xa043e000000000000000,0x2228000000001,0x0,0x48004af800000000,0x4a48,0x20700040380000000000,0x1be94780000078beb7,0x7bc10000007050460000,0x3c768deb42a,0x0,0xc00000000000000034a8,0x22d3c39b000000000023,0xa70006c8000000423000,0x0,0x31180000000002900000,0x10000000004a6000000,0x1b0005,0x33b80,0x3080000028cfaa800000,0x140000003170000005,0x0,0x488000120800,0x5968058000005338,0x3f00000000,0xb62ba000000240800000,0x46c580000038a00061e9,0x3a163599fe98f8,0x0,0x0,0xc980000000000000000,0x88002a4000000,0x3ac00000000033d0000],#[0xb300000000000,0x3ce4a000000000000000,0x1a880032d800315d,0x38028980000000000,0x7b280000000000021a,0x2238000448008,0x482a0f00052580000,0x49000000000000129800,0x43b00000019a8000000,0x0,0x14e1c0002a68004ae800,0x3451388000000000003,0x2398005b680060680,0x642a0a800000000000,0x300069c8000000000000,0x1ab0000000000001c,0x128000397ca5000,0x19d0000000000000,0x2440000007c200000,0xa1800000000000000000,0x4c68000004987]]
set_option maxRecDepth 16000 in
def g255D10 := limbs80 #[#[0x7bf26c3ac1cf9765c160,0xdcba2c0a04fd647845c2,0xf2ecb0281fbb9458140f,0xec3ac8a06fe61d60503d,0xaecba2817bd9759140dd,0xcb2e8a06ef61974503b7,0x30bb2819fd875d940bdf,0xa30ca04ffe61765027fb,0x8c3a813ff9761940ddfc,0x2e0b04ffe598750377f2,0xb82c1df9765c160bfdca,0xe0b07bee5970583df12c,0xa2c1cfd765d160efdc3a,0xcb04ff65f845827fd30b,0x2c19ff875d960bfdc82e,0xb073fe1d76583df720bb,0xc17df9361d60b7f4c4ec,0x67fe1d87582dff2cc3a,0x1bdf9361d60dfdc830eb,0x6bfe59875827ff28c3ac,0x3fd94e1d609ffcb30eb0,0xffa61645c35ff30bb6c1,0xfd97d9170bfcc86c8b84,0xfa63645c27fb31b22e15,0x591e1170bfac8f08b84f,0x65b845c33faedc22e1bf,0x865d970efdc82ecb84ff,0x44865c39ff0cbb2e1cfc,0x321970bf6c910cb85fd6,0x4865c2f7b28432e17dd9,0x61970d7ec310cb85df65,0x865c2fbf26c32e17fb90],#[0x1970bfcc850cb857fe5d,0x65c2bfb2f432e1aff86a,0x1649feca70cb84ff6628,0x5927ff20c3ac97bf905d,0x649ffcbb01b26efe5187,0xd2f7f28c02e93ff9061f,0x49fecb700ba67f5db805,0x2f7f28c32e9dbf945d97,0xbefc9b00bb4ff643865d,0x7fb29c02ed6ff9660176,0xfccbac0a04ff643845da,0xfb30bb281fbd945d940f,0xcc22e0b06ffe61765037,0x328b82c1ffb845c160ff,0xcb2e0b07fee5170583ff,0x30ba2c1fbd845d160ffd,0xb308b05ffe6174582ffb,0xdc22c1bfd8761160f7eb,0xf08b06ff61f84583dfae,0xbb2c1bfd97e1160bfecb,0xecb07bf65176583ff720,0x3ac1ffb9061d60f7fca2,0xeb05ffe5187583fbf26c,0xac17ff9661d60f7fcb30,0xb06ffe51875837fb28c3,0xe1fbd8459170dffcb30e,0x85ff663645c2ffb30b22,0x1bfd8661170efebb308b,0x5ffe59845c37ff0cc22e,0xbfd86e1170efebb708b8,0x7f651765c2ffb2dc22e1,0xff865d970effca2ecb87],#[0x7e4d865c3ff720c32e1d,0xf9761970bffca30cb87f,0x653865c2ffb31432e1df,0x9061d64dfeca70cb85ff,0x4187d937fb2ec06c9bff,0x5d974dffc830fb26ff6,0x1865d3bff20bb2e9dfd9,0x60176ffdc0300bb5ffe4,0x805db7fb08c02edfdf93,0x176bffca300bb6ffe11,0x5dafff2cc02edeff966,0x176dfec2700bb77fe5d8,0x5daffb29c02edbff84e0,0x76dffca700bb6ff65380,0xdbf7f08c22ed7ff90611,0xdfec8708bb5ff643845,0x3fff28c3ac1ffd9461d6,0xffec3308b87ffe598758,0xffb28c32e1ffd9661170,0xfec2300bb7ffe51865c3,0xfb28c02edfff8460176f,0xfcb300bb7ffe51805dbf,0x60270001ffd90e1176ff,0x10c83960be8282075012,0xdb86e419685d015184bc,0x80a4426e891e225080a1,0x8dc834f8ca23018b7c2b,0x15e43090383e70f1239d,0x764ff93984c3927247a1,0xe5c5967a580958a54014,0x69d99ec65418b4606178,0x879d827399c4a6eb9b12],#[0x220d08119fbc7d11eba7,0x24308e9a31c8a021d285,0x7909c1a66a973a53292a,0xf0a99a9caa54a8b6a0b2,0xb71ad3cb282c28ae7aa,0xc5bb0e4c122f9abbb2e5,0x53349ed053378ca531f8,0x1b87cdef370eda135e8d,0xbc36ee23ac8e8b3990e4,0xff0fd53ecaf873d80f34,0xf30ccc285075c129027b,0x31d1c6ab183c573135c3,0x2c04a53269491b21fc7e,0x9ccdd7357ccc3309cb9d,0x8d1c744ad0473eacefd3,0x558153954374ddd2db49,0x8e161157a95c7d6a7587,0xad6ffdb3f6a8da0765f5,0x57b3de4576edd677405c,0x84ce0cd819e0137e25f3,0x371609c1e070f8446199,0x8546c263783c0e18e882,0x85370d84e17068bc325,0x208c6e170781c30b1215,0x80bf0b83c0e185860b85,0x2036486370781c3e1428,0x47820218dc2e0f0f8016,0x850e120570b83c3e043,0x214161c240de170787c,0xc1e070c24391b85c1e1f,0x70781c30a4287a37081b,0xdc2e0f0f808a0b0e0de1],#[0x6d1b09c2e0f038612208,0xe1286f0b83c0e1a2878,0x50a201a0ae170781c309,0x587094358dc1e070f8,0x87c04690140570b83c3e,0xe1f002c404a8d84e1707,0xf81c2468e0d8251b85c1,0x1e070f8419208d04e0f0,0x781c3e106480b8111bc,0xc1e070f841b1d1004e2f,0x15383c0e1f0a1448108d,0x9c2e0f03870d208c170b,0x270781c3e14347a304b0,0x946e0f0387c2869012c,0x2361383c3e070a1a385d,0xe1084a370781c3e10888,0x838208dc1e070f841b1,0xe1c6c8a303783c0e1f0b,0xf84191d858dc27078146,0xe1f08362a2037c1e070,0x1e8dc1e070f84221b83c,0x11a3d1b08c2c6f0781c3,0x3e10646c204b85c1e1f0,0x787c0e12346e2f0781c,0x8da370b83c0e1a288c27,0xd1f09c1e1f03840d1824,0x890461025c2e0f0f804,0xc2241017c351783c0e1f,0x70f84421b0945e0f0387,0x7c2240e17c21238345e0,0xf0f8419230945e0f038,0x85c1e18588103029b45e],#[0xe0f0f8016230cc0c2517,0xb83c3e013484313709c2,0x1e070f8422202586c270,0x781c3e10648e2c1909c,0xc1e070f8419200cc526f,0x13783c3e112c72401b8b,0xf84e070f844d0e0d86c2,0x4d1f084de0f03864c0c8,0x1343a361b09c1e1f0384,0x3c0e1f089a3e1383c0e1,0x270781c3e108890be138,0x9bc1e06138646188a194,0xe0f0387c20d8f196161a,0x509c1e070f844d1c3286,0x9a3f0781c3e113432306,0xe113480ca1b83c0e1f08,0xf804d203386c270781c3,0x3e043480961b09c2e0f0,0xf850d1c25466270b83c,0xc1e070c24404989c1e07,0xf0387c20b8e14a303785,0x1c1e070f8546218d85e0,0x170787c00a0586c2b121,0x2e148570b83c3e02348e,0xc485289c2e0f0f808d1c,0xc3d0642f1385c1e1f002,0x1a30481bc2e0f0f80141,0xe070e88405385c1e070e,0x387c20c8fc5616370dc1,0x2e0f03868d1d11c5e0f0,0x1383c0e1f0a1a404a89c,0xc16370387c2851212c33],#[0xf0f81c24505890b4342f,0x7c0457082c40501b46e0,0x1f03848a0b0e1ba37078,0x83c0e1d1b841b1e8dc1e,0xa37051bc0e1f082e402b,0x1546e0f0f81c2469854,0xe123432408436160c95,0x38546468e1b0b70787c,0xc0e1d1b8416242fc1e1f,0xf0387c20b100d0b82b83,0x3c0e1f08a841530946e0,0x70d8dc20d8f0dc205b8,0x8dc1e070f841b241bc1e,0xa2f0387c20b941286c29,0x387c20b8e54044118dc1,0xe1b1b84171ca945e0f0,0xb83c3e043424451783c,0xc1e1f028dc2869184637,0x70787c0e103708505d09,0x3c3e070914486c45462a,0x70e8dc220361e8451b8,0x83c0e1d1890bf1509c1e,0xe12342c46222fc561613,0x38746e11384a370787c0,0xde105c74405f8b84e0f0,0x383c3e11184e0f0f808,0xc3e07091a484b081b46f,0xf03848d1c3612a361383,0x3c3e07089a485f09c1e1,0x70f850a2442190a02b8,0x8648e112210de189bc1e,0xe1134a0be1b0945e0f03],#[0x4c1085832148570787c0,0x4833868570787c0e113,0x3c3e07089a1920421b8a,0xf0f81c22688488a42b8,0x83c3e07089a1920290ae,0xe0f0f804de106480b42b,0xb83c3e07089a19203784,0x4e0f0f81c2c213480b42,0x1b83c3e0137848a20441,0x6e0f0f81c2c213470f4,0x21033c5e0f038786e113,0xdc5a430b8384e070c9a4,0x361383c3e07089a44670,0xc19e0f0387c20d8e12c,0xc3613824de070f841921,0x9288ae0f0f81c2268648,0x1a122383c3e07089a191,0xe105c7a331385c1e1f02,0xf81c2c292c6c2f0781c3,0x3e107880f4218817e0f0,0x3850d3011856270781c,0xbc530a228305989c1e1f,0xc16e0f0f81c24508880,0xc331385c1e1f00250d20,0x1d1082270787c0e10886,0x848d2b10c2e2e1b83c0e,0x2528121106e89c1e1f03,0x1e0da370dc1e1f03844a,0x61a89c1e1f0b80c50b10,0xe88c371783c0e1d13844,0x1b183dc1e1f0289c2468,0xf0384221d0dc1e1f0384],#[0xbc0e1f083c404895c1e1,0x1f0b808d0b1012a27058,0x83c0e1f0844425289c1e,0xe070c95c20f0e1262d13,0x783c3e070988222025c1,0x406f0781c3e107880a03,0x1989c1e1f03850d2b881,0xc1e1f021a12243c1ba2e,0x858a9c20d8986a2b1385,0x202f84103616e15198a2,0x210db083314851347e12,0xd14421b8a049850a268e,0x6f09c2268821c206f844,0x840d8592942115111a38,0x20b06f844a143d420d92,0x4451050b513841b628a2,0x8370d6205a8a30782fc2,0x7]]
def g255H10 := limbs80 #[#[0xa522428e00040418422,0x590c2034e010e0201440,0x7042200622f5f76806e,0x7a401014022012011802,0x83a10c0000007401a2a4,0x1a120000000e69e467d,0xa001fcc0005aeb060000,0x96bc56001cbf7d7998ea,0xb78000767e07116000,0x3155b82793f500000000,0x66ef4a0018742f60006a,0xc0ab4000000000000001,0x50acd49d693e60008b26,0x81943e00000000143,0x169251ea5a000,0xa220c0dd5f8943db4f40,0x11d2000000f1bb21a8,0x1bbce152de00130b49e,0x2fe000001356d9a0000,0x12ef9c00000000000000,0xe2944001a62000000000,0x78ca8f88520012efe61f,0x3adbc2000001f2,0x4c6160006f0a5537d194,0xea445c57ce000000001d,0x1f4,0xb27e8800000019be000,0x112000000538a,0xb70ddd588ace0e5cf200,0x32001c7bb2a2af5ca001,0x1d7254286ced4000001c,0x17a5a1c001ad0001b8],#[0x1aba6c413a,0xe000001c1ee4a98c0000,0x5a600142c000001467f8,0x12ec4720003a1642427,0xebe03d5c10c87f65f8a0,0xf104a4e9014755cdd,0xfd704e6a000000001804,0x1314001c36fc6f6c0000,0x722bab2a00016a917a00,0x98000001fb800197453f,0xe78000001a3d81a000c,0x25c000000000e9a56fb6,0xf0f729,0x8000b09e30e28400d180,0x15250c800000088c2d,0xfa25932db3600062a000,0x18e15c9776584e515630,0x7b5ae80008dc4e3dba00,0xd9f96665c77622000900,0xd71c5a9fe9552068000d,0xe5f1b00000000000000c,0x582b6000001db2000000,0x1f0200155a0013,0x69c00048200000,0x3d184c0004088c6202,0x6e4800179e0b87300000,0x18d2000a0e00000089,0x901c00014d7d3c488000,0xf64e735787ec2933d7fb,0xfb6e71838285eda00008,0x10b00bd824c2f2a6eeb]]
def g255D11 := limbs80 #[#[0x5d140fbd64503fe58140,0x582ff61d40bfd86503ef,0xefd76582ffe1160ff970,0xe1d60bfd87583bf9d960,0x5c2ff61f60efd76d82ff,0xbff865c37f5d970bff84,0x60364bfd87593ef5d164,0x5d2ffe0174bfd87d92ff,0xbff805daffe1974dfd76,0x5d940bfd809daffe1176,0x583ff61160ffd74583ff,0xffd87583ff5d960fff84,0xd9170ffd645c3ffe1d60,0x5c3ffe1170ffd845c3ff,0xffe865c3ff61970ffc86,0x61974ffd805d3ffe1970,0x5dbffe0176ffd805dbff,0xf0118003ffe1176ffd84,0x88a07886705784403081,0xfc8eb0d78ca0ba8a9099,0xf16995a14893512190e0,0x9e61ce9bf1b199e18e97,0x60a4d23ba2a218a071f7,0xf2cfabe2aca9b287a762,0xc30a232b315b022f0ad,0xf00283461bc60dc2c1c,0x1446c2c1c0c30a230b07,0xc48371b0b07030c28912,0x416468dc2c1c0c30a246,0xd20123707030f091871,0xf0a1081284c6c2c1c0c3,0xc3c20d1c23151b07030],#[0x123707030f0870446c1c,0x48d46c1c0c3c21b211a,0x20d181b0613030f08347,0xb070f0114984c1c0c3c,0xc1c0c3c284205a193613,0x9370613030f088c5064d,0x6c414c2c1c3c00d24661,0x491b130b070f00349124,0xc60885c1c0c2c3442450,0xd1b10230b070f0214817,0x34a0844c2c1c0c3141,0x141c581a1453130b070f,0x30d13087040dc2c1c0c3,0x4c2c1c3c00d261a37070,0x1b07030f08346124586c,0x834b0d46c1c3c0c28a1e,0x5d5050591a13070f030,0x5c70dc60ac1c0c3c21b2,0xc2840d231b0437030f08,0x7030f086c81746c1c3c0,0x1c0c346c21b2236111b0,0x1a13070f03093480804c,0x868445c1c0c3c2482466,0x66193707030f0828a19,0x44dc145c3c0c21920845,0x141a13070f0309346498,0x481986844dc1c0c3c221,0x21920661a1307030f093,0x5058706844dc1c0c3c,0xc1c3c01214202b0b070f,0xa351307030f088440dc2,0xd86c1c0c3c2442227161],#[0x521b13070f030834ac58,0x86c4c1c3c0c20d245888,0x451e]]
def g255H11 := limbs80 #[#[0x851804140304020a044,0x3720005880,0x36024003d3c0000031b4,0x8400000014f7e,0x1c202c00000000000000,0x251c003a58001e4c001,0x4588000001c600000000,0x464000000d6349,0xd8fe440000029d4000,0x1a0c0000aa0300000000,0x576684e9400000000,0x1a8c000000,0x7c0000000000004c40,0x23800000000,0x24ca250000000,0x123e9fc0038680000,0x211800000,0xcc0000000000030359a0,0x15,0x194400000098,0x38179dd15f4e4000000,0x1e90000003ce80,0x9e4000d7000000000000,0x48c003134000002e1d,0x8003e640000000000000,0x948000d540000008fe04,0x25c400303c000,0x36540000000000,0x0,0x1ca7828000000,0x6100000000000,0x244400000],#[0xd000222c0039f400186c,0x15dbdac000000003c,0x2668000002e8,0x0,0x5f007914c0000000000,0xd10000003e2162800000,0x3,0x1e2400000000125c0,0x5800000359400000000,0x289b4df,0x28022180,0x2d2f81000000000,0x0,0x0,0x0,0xc0000000038f0000,0x3c846400000000000000,0x0,0x2130000000128000000,0x24080000000010b80000,0x38d800000000,0x25080180018b0003038,0x21e80000000000000000,0x0,0x244c000,0x19780000000000000000,0x48800000000000000,0xc5c003d00000,0x18bc0,0x2dd0000000000d5800,0x21590000001a075650c0,0x1c],#[0x9691e00000000025ec54,0x210ac000000000000001,0x40000000000000000001,0x3a000031a,0x2248,0xc0000000000000000000,0x227,0x3950000,0x0,0xc9000000000327800000,0x980028cc124000000001,0x35,0x4ec00000000000000000,0x1c54000001,0x3d84001d0c0000000,0x26ddbe8e000000000000,0x2d1400256c000000676,0x1c500000000000000,0x11fb8fa073083a3,0x0,0xc0000000000000000000,0x34b799,0x31b8000000000000,0x12080039040000,0x1c04003ea393b1b000,0x72e14000000000a63a9c,0xc0000000000000000002,0x181c000000cd400017,0x0,0x29c80000000000,0xe9800000000000000000,0x3c745a80030a1c9e688]]
def g255D12 := limbs80 #[#[0x4ffae1ffd83feb07fd40,0x76ffaedff5d3ffb27fd6,0x76b11a71a94dc37007fe,0x8438d8d0a0c086287ede,0x2830218d1e30d0906043,0x888a18241810e1101824,0x21882234485061c01a3,0xc16141810c98d102c283,0x8834341810e110506c40,0x20685061c01a3c5]]
def g255H12 := limbs80 #[#[0x612002cae0002d02685,0x3bd68b8314f9298deb80,0x1abf665cacd5400311d,0x352e1647860000079e0,0xe801300256549dc0bcd8,0x51a0048d54001c98c2e,0xad0000038e004440,0x120a593c005ca000000,0x2f860000088800000000,0x1f6f2c022c8c]]
def g255D13 (j : Nat) := if j=0 then 0x1851020400c7ff else 0
def g255H13 := limbs80 #[#[0x975b4000e00088019c5,0x304014c5]]
def g255L : Nat → Packing
  | 7 => (19,6,6,0,0,9,0,g255D7)
  | 8 => (150,5,6,0,0,12,0,g255D8)
  | 9 => (245,4,6,0,0,14,0,g255D9)
  | 10 => (169,3,6,0,0,14,0,g255D10)
  | 11 => (47,2,6,0,0,12,0,g255D11)
  | 12 => (9,1,6,0,0,9,0,g255D12)
  | 13 => (1,0,6,0,0,0,0,g255D13)
  | _ => emptyPacking
def g255I : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 4 29 2 9 5 0 g255H8
  | 9 => lookupWord 37 557 3 12 8 0 g255H9
  | 10 => lookupWord 61 397 5 12 8 0 g255H10
  | 11 => lookupWord 42 631 3 12 8 0 g255H11
  | 12 => lookupWord 11 71 5 10 6 0 g255H12
  | 13 => lookupWord 2 13 3 8 4 0 g255H13
  | _ => fun _ => none
def g255 : Forest := ⟨255,13,fun i => g255Y[i]?.getD (0,0),g255C,g255A,g255L,g255I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P7_0 : block g255 7 0 19=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B7 : block g255 7 0 19=true := g255P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_0 : block g255 8 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_1 : block g255 8 1 17=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_18 : block g255 8 18 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_114 : block g255 8 114 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B8 : block g255 8 0 150=true := (@block_merge g255 8 0 18 132 (@block_merge g255 8 0 1 17 g255P8_0 g255P8_1) (@block_merge g255 8 18 96 36 g255P8_18 g255P8_114))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_0 : block g255 9 0 17=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_17 : block g255 9 17 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_113 : block g255 9 113 7=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_120 : block g255 9 120 96=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_216 : block g255 9 216 29=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B9 : block g255 9 0 245=true := (@block_merge g255 9 0 113 132 (@block_merge g255 9 0 17 96 g255P9_0 g255P9_17) (@block_merge g255 9 113 7 125 g255P9_113 (@block_merge g255 9 120 96 29 g255P9_120 g255P9_216)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_0 : block g255 10 0 3=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_3 : block g255 10 3 80=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_83 : block g255 10 83 73=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_156 : block g255 10 156 13=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B10 : block g255 10 0 169=true := (@block_merge g255 10 0 83 86 (@block_merge g255 10 0 3 80 g255P10_0 g255P10_3) (@block_merge g255 10 83 73 13 g255P10_83 g255P10_156))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_0 : block g255 11 0 26=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_26 : block g255 11 26 21=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B11 : block g255 11 0 47=true := (@block_merge g255 11 0 26 21 g255P11_0 g255P11_26)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P12_0 : block g255 12 0 9=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B12 : block g255 12 0 9=true := g255P12_0
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

end PEqualNP.Outside.L_meta_34948

open PEqualNP.Outside.L_meta_34948 in
theorem PEqualNP.Outside.L_meta_34948 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o fit _ correct
  exact replaceShort g255R gates o fit correct

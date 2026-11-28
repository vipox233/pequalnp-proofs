import PEqualNP.Defs

-- The two-mode live-state and cofactor checker follows L_meta_1674 and L_meta_670.
-- The graph, restrictions and all search certificates below are for L_meta_34796.

-- Shared forest and cofactor certificates from L_meta_1674 and PR 11111 for L_meta_1677.
-- The original credit line is retained below. The two root certificates here cover the unpinned graph.

-- The checker and the bound certificates are adapted from PEqualNP/Outside/L_meta_1667.lean (Apache-2.0).
-- Two modes: u=false are monotone runs (AND, OR); u=true are runs up to complement, where negation is free.
namespace PEqualNP.Outside.L_meta_34796
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
def graph : Sig := (BitVec.ofNat 512 (word80 [0xffffffff,0xffffffffffffffffffff,0xfffefffffefefffffefc,0xfefefafaeeccaa00ffff,0xffffffffffffffffffff,0xfffffffefffffefeffff,0xfefcfefefafaeeccaa00]))
def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 3) || (x 1 && x 4) || (x 0 && x 5) || (x 2 && x 5) || (x 1 && x 6) || (x 2 && x 6) || (x 4 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 2 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 5 && x 7) || (x 6 && x 7)
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
  (x 0 &&& x 3) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 2 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 4 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 2 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)
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
  (x 0 &&& x 3) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 2 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 4 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 2 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)
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



def target (x : Fin 8 → Bool) : Bool := decide (∃ i < ([0, 3, 1, 4, 0, 5, 2, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
def smallCircuit : Circuit := ⟨[⟨.or,[6,7]⟩,⟨.or,[3,5]⟩,⟨.or,[0,6]⟩,⟨.or,[0,7]⟩,⟨.or,[1,8]⟩,⟨.or,[5,8]⟩,⟨.and,[11,9]⟩,⟨.and,[12,4]⟩,⟨.and,[13,2]⟩,⟨.and,[8,1]⟩,⟨.and,[7,10]⟩,⟨.or,[14,15]⟩,⟨.or,[19,16]⟩,⟨.or,[20,17]⟩,⟨.or,[21,18]⟩], 22⟩

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
def g82D3 (j : Nat) := if j=0 then 0x7 else 0
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
def K82 := extendKnown [] 4 [(82,[]),(137,[16,67,118]),(146,[118]),(164,[33,84,118]),(194,[100,84,117]),(196,[33,100,84,117]),(208,[65,33,50,99,83,117])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V82 : Known true K82 := extend_ok (m:=82) baseKnown low82 (by decide +kernel)
def g45Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xe6de3fff03fff1ffe6,0xde3fff03fff1ffe6de3f])),(BitVec.ofNat 152 (word80 [0x648490a2850240206,0x48490a28502402064849]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x19e9c0fffc07fe3f19,0xe9c0fffc07fe3f19e9c0])),(BitVec.ofNat 152 (word80 [0x50e8db2c3161408450,0xe8db2c3161408450e8db]))),((BitVec.ofNat 152 (word80 [0xece607fffff8003fec,0xe607fffff8003fece607])),(BitVec.ofNat 152 (word80 [0x8a7b6b04185892808,0xa7b6b04185892808a7b6]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1b3df8ffffffffc01b,0x3df8ffffffffc01b3df8])),(BitVec.ofNat 152 (word80 [0x891524c08206003089,0x1524c082060030891524]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g45C : List ColumnInfo := []
def g45A : List (List Nat) := [[],[80,50]]
def g45D3 (j : Nat) := if j=0 then 0xf else 0
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
def K45 := extendKnown K82 4 [(45,[]),(101,[32,99,67]),(102,[32,16,83,67,100]),(116,[32,16,65,83,99])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V45 : Known true K45 := extend_ok (m:=45) V82 low45 (by decide +kernel)
def g86Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfdf00fff81fc7e3ffb,0xe01fff03f8fc7ff7c03f])),(BitVec.ofNat 152 (word80 [0x45c09245142904808b,0x81248a28520901170249]))),((BitVec.ofNat 152 (word80 [0xe6a8703ffe007fc7cd,0x50e07ffc00ff8f9aa1c0])),(BitVec.ofNat 152 (word80 [0x96a9b6d618b228112d,0x536dac316450225aa6db]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfbb781ffffff8007f7,0x6f03ffffff000feede07])),(BitVec.ofNat 152 (word80 [0x235249820c0312204,0x6a49304180624408d492]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x64ffe3ffffffff80c,0x9ffc7ffffffff0193ff8])),(BitVec.ofNat 152 (word80 [0x249204100400400,0x4924082008008000924]))),(0x0,0x0),(0x0,0x0)]
def g86C : List ColumnInfo := [(4,0,82,0,4)]
def g86A : List (List Nat) := [[],[65]]
def g86D4 (j : Nat) := if j=0 then 0x1f else 0
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
def K86 := extendKnown K45 5 [(86,[]),(139,[32,16,67,118]),(141,[16,67,118]),(147,[32,118]),(153,[16,66,50,118]),(154,[50,118]),(163,[32,16,84,118]),(166,[33,84,118]),(172,[33,49,84,118]),(195,[32,100,84,117]),(197,[16,32,100,84,117]),(201,[16,98,50,67,84,117]),(202,[50,100,84,117]),(216,[65,50,33,98,82,117])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V86 : Known true K86 := extend_ok (m:=86) V45 low86 (by decide +kernel)
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
theorem g165G : graphValid g165 (boundsBefore K86) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low165 : Lower true (varsX 165) (graphGoal 165) 5 := lower_forest (g:=g165) (i:=0) (hints:=1285) (before_sound K86 V86) g165G g165T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K165 := extendKnown K86 5 [(165,[]),(169,[48,82,32]),(198,[16,101]),(228,[80,16,98,49,67,66])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V165 : Known true K165 := extend_ok (m:=165) V86 low165 (by decide +kernel)
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
theorem g210G : graphValid g210 (boundsBefore K165) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low210 : Lower true (varsX 210) (graphGoal 210) 7 := lower_forest (g:=g210) (i:=0) (hints:=285278272) (before_sound K165 V165) g210G g210T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K210 := extendKnown K165 7 [(210,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V210 : Known true K210 := extend_ok (m:=210) V165 low210 (by decide +kernel)
def g91Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xff003ffffc3ffc00ff,0xfff0fffc7a695700003f])),(BitVec.ofNat 152 (word80 [0x8a9288a10892294a42,0x90224880380957555555]))),((BitVec.ofNat 152 (word80 [0xffffc00fffffffff00,0x3fffffc289acf903ffc0])),(BitVec.ofNat 152 (word80 [0x2c0302c05000b00c0b,0x140010a002c990c30c3]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffff0003fffffff,0xc000fffd77e88a00003f])),(BitVec.ofNat 152 (word80 [0x3024130a6124c2108c,0x2584920147e088aaaaaa]))),((BitVec.ofNat 152 (word80 [0x3fffffff,0xffff00012697f4fc0fc0])),(BitVec.ofNat 152 (word80 [0xc0381c038207006010,0x6001c1122836030c30c]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffc0000000,0x39d530dfff000])),(BitVec.ofNat 152 (word80 [0xc0200c00380380e0,0x3808e0209d5004c30c30]))),(0x0,0x0),(0x0,0x0)]
def g91C : List ColumnInfo := [(0,1,82,8,5)]
def g91A : List (List Nat) := [[],[100],[65],[65,97],[97,65],[97],[48],[48,100],[48,65],[48,65,97],[48,97,65],[48,97]]
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
theorem g91G : graphValid g91 (boundsBefore K210) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low91 : Lower true (varsX 91) (graphGoal 91) 6 := lower_forest (g:=g91) (i:=0) (hints:=16842819) (before_sound K210 V210) g91G g91T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K91 := extendKnown K210 6 [(91,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V91 : Known true K91 := extend_ok (m:=91) V210 low91 (by decide +kernel)
def g103Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xe001ffc07ff01ffe00,0x3ffc07ffffd37a12000f])),(BitVec.ofNat 152 (word80 [0x48d4128d0522c8549a,0x9128d25229934a125555]))),((BitVec.ofNat 152 (word80 [0xfffe00007fffffffff,0xc00007ff01a3a9cc0f00])),(BitVec.ofNat 152 (word80 [0x82985b161644829813,0x5b160644d2329c83333]))),((BitVec.ofNat 152 (word80 [0xffffffff80001fffff,0xfffff800003f4479f0f0])),(BitVec.ofNat 152 (word80 [0xe01c18078700e01c,0x1c18078701304591111]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1fffff,0xfffffffffe663f7600ff])),(BitVec.ofNat 152 (word80 [0x130160205808130120,0x2600048000643124aaaa]))),((BitVec.ofNat 152 (word80 [0xffffffffffffe00000,0x19dd38dff00])),(BitVec.ofNat 152 (word80 [0x1c01800060001c01c0,0x38020700808cd204cccc]))),(0x0,0x0),(0x0,0x0)]
def g103C : List ColumnInfo := []
def g103A : List (List Nat) := [[],[16,101]]
def g103D4 (j : Nat) := if j=0 then 0x1f else 0
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
theorem g103G : graphValid g103 (boundsBefore K91) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low103 : Lower true (varsX 103) (graphGoal 103) 5 := lower_forest (g:=g103) (i:=0) (hints:=16778597) (before_sound K91 V91) g103G g103T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K103 := extendKnown K91 5 [(103,[]),(109,[48,97,82,16,32])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V103 : Known true K103 := extend_ok (m:=103) V91 low103 (by decide +kernel)
def g118Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0xf003ff87fe1fffc01f,0xfff87fffe474a4007c1f])),(BitVec.ofNat 152 (word80 [0xa12845108440228940,0xa01108826014a45294a5]))),((BitVec.ofNat 152 (word80 [0xfffc0007ffe1ffffe0,0xfffffc0335be20f83e0])),(BitVec.ofNat 152 (word80 [0xc030162028040b0182,0xc0a00108225922318c63]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffff80001ffffff,0xf0007ffccfd11df0001f])),(BitVec.ofNat 152 (word80 [0x240980130884c0203,0x2c2120087c108a5294a]))),((BitVec.ofNat 152 (word80 [0x1ffffff,0xffff80004d2fe80003e0])),(BitVec.ofNat 152 (word80 [0xb82e045c111702c14,0xb005c104d26c9ce739c]))),((BitVec.ofNat 152 (word80 [0xfffffffffffe000000,0x33aa61bfffc00])),(BitVec.ofNat 152 (word80 [0xc0300060001803018,0xc046021182211084210]))),(0x0,0x0),(0x0,0x0)]
def g118C : List ColumnInfo := [(0,32,82,4,5),(32,0,86,0,5),(2,0,116,0,4),(4,32,82,0,4),(16,0,102,0,4)]
def g118A : List (List Nat) := [[],[65]]
def g118D4 (j : Nat) := if j=0 then 0x5bd4940 else 0
def g118D5 := limbs80 #[#[0x240d140ff40fd40fd20,0x2012]]
def g118H5 (j : Nat) := if j=0 then 0x60 else 0
def g118D6 (j : Nat) := if j=0 then 0x18989f else 0
def g118H6 (j : Nat) := if j=0 then 0x2051600028b50000000 else 0
def g118L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g118D4)
  | 5 => (3,1,3,0,0,5,0,g118D5)
  | 6 => (1,0,3,0,0,0,0,g118D6)
  | _ => emptyPacking
def g118I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 4 0 0 g118H5
  | 6 => lookupWord 1 11 0 7 2 1 g118H6
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
theorem g118P5_0 : block g118 5 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g118B5 : block g118 5 0 3=true := g118P5_0
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
theorem g118G : graphValid g118 (boundsBefore K103) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low118 : Lower true (varsX 118) (graphGoal 118) 7 := lower_forest (g:=g118) (i:=0) (hints:=18941248) (before_sound K103 V103) g118G g118T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K118 := extendKnown K103 7 [(118,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V118 : Known true K118 := extend_ok (m:=118) V103 low118 (by decide +kernel)
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
def K143 := extendKnown K118 6 [(143,[]),(174,[32,48,80,64]),(188,[32,49,64,81])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V143 : Known true K143 := extend_ok (m:=143) V118 low143 (by decide +kernel)
def g155Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffc01ff87fc3fff00,0xffff1ffed2e680007c1f])),(BitVec.ofNat 152 (word80 [0x222894451108808a4a,0xa02444252268a5294a5]))),((BitVec.ofNat 152 (word80 [0xffffe0007ffc3ffff,0xffffe11773400f83e0])),(BitVec.ofNat 152 (word80 [0x40b018162050082c0c,0x2c140089146346318c63]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffff80003ffff,0xff001ffce8f541f0001f])),(BitVec.ofNat 152 (word80 [0x84c120980261113010,0x30588900a8d154a5294a]))),((BitVec.ofNat 152 (word80 [0xf0000000000003ffff,0xffffe0005f98fe0003e0])),(BitVec.ofNat 152 (word80 [0x701c0e0438221c060,0x40600e104b9898c6318c]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffffffffc0000,0x3280bbffffc00])),(BitVec.ofNat 152 (word80 [0x80201000400020080,0x80801000000021084210]))),(0x0,0x0)]
def g155C : List ColumnInfo := [(1,0,154,0,5),(2,0,153,0,5),(8,0,147,0,5),(16,0,139,0,5),(9,0,146,0,4),(18,0,137,0,4)]
def g155A : List (List Nat) := [[],[65],[16,67],[16,48,64],[48],[48,65],[64,16,49],[64,49]]
def g155D4 := limbs80 #[#[0x9bd89544426d6215110,0x31825f635474]]
def g155D5 := limbs80 #[#[0x7c54443f280885bd4940,0xfea8885f95110beaa221,0xbd4940bfa8a81fb40502,0xcc8d018160c02faa3a07,0x882188201141080d176b,0xc110204810001]]
def g155H5 := limbs80 #[#[0x490000280000710000f2,0x90]]
def g155D6 := limbs80 #[#[0x540a0380ff40fd40fd10,0x3140cc503]]
def g155H6 := limbs80 #[#[0x308000000000070b41,0x3240051800d1c0000000,0x18590cd9e100004400,0xa4c0025c000000000000,0x95200c84000000000000]]
def g155D7 (j : Nat) := if j=0 then 0x1605f else 0
def g155H7 := limbs80 #[#[0x60027400a12a53200006,0x2200000214d8ba801041,0xb]]
def g155L : Nat → Packing
  | 4 => (3,3,3,0,0,4,0,g155D4)
  | 5 => (10,2,3,0,0,7,0,g155D5)
  | 6 => (3,1,3,0,0,6,0,g155D6)
  | 7 => (1,0,3,0,0,0,0,g155D7)
  | _ => emptyPacking
def g155I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 11 0 8 2 2 g155H5
  | 6 => lookupWord 4 41 0 10 4 2 g155H6
  | 7 => lookupWord 3 19 1 9 2 3 g155H7
  | _ => fun _ => none
def g155 : Forest := ⟨155,7,fun i => g155Y[i]?.getD (0,0),g155C,g155A,g155L,g155I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g155P4_0 : block g155 4 0 3=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g155B4 : block g155 4 0 3=true := g155P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g155P5_0 : block g155 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g155P5_1 : block g155 5 1 9=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g155B5 : block g155 5 0 10=true := (@block_merge g155 5 0 1 9 g155P5_0 g155P5_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g155P6_0 : block g155 6 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g155B6 : block g155 6 0 3=true := g155P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g155P7_0 : block g155 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g155B7 : block g155 7 0 1=true := g155P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g155T : checkedTables g155 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g155 0 0 0 = true)
  · exact (rfl : block g155 1 0 0 = true)
  · exact (rfl : block g155 2 0 0 = true)
  · exact (rfl : block g155 3 0 0 = true)
  · exact g155B4
  · exact g155B5
  · exact g155B6
  · exact g155B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g155G : graphValid g155 (boundsBefore K143) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low155 : Lower true (varsX 155) (graphGoal 155) 8 := lower_forest (g:=g155) (i:=0) (hints:=65603) (before_sound K143 V143) g155G g155T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K155 := extendKnown K143 8 [(155,[]),(182,[16,32,67,83]),(203,[100,84]),(217,[65,33,98,82]),(227,[83,100])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V155 : Known true K155 := extend_ok (m:=155) V143 low155 (by decide +kernel)
def g167Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffc00ffc07fe03fff,0xe00ffc0ffff447d401c7])),(BitVec.ofNat 152 (word80 [0xa0a86a128d0a458a05,0x46a129a2929043d49249]))),((BitVec.ofNat 152 (word80 [0xfffff00007fffc07f,0xfff0000ff81386ac0e00])),(BitVec.ofNat 152 (word80 [0xc5314c5b162c891329,0x84c5b2c324d386adb6db]))),((BitVec.ofNat 152 (word80 [0xfffffffff8000007f,0xfffffff0000be8947038])),(BitVec.ofNat 152 (word80 [0x1c0701c180f0e1c0e,0x701c303c709e0949249]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xf0000000000000007f,0xffffffffffe6fe67803f])),(BitVec.ofNat 152 (word80 [0x60180602030102030,0x806000400061c212492]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffffff80,0x1911bbffc0])),(BitVec.ofNat 152 (word80 [0x80200800040000040,0x10080008000000024924]))),(0x0,0x0)]
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
theorem low167 : Lower true (varsX 167) (graphGoal 167) 6 := lower_forest (g:=g167) (i:=0) (hints:=1397) (before_sound K155 V155) g167G g167T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K167 := extendKnown K155 6 [(167,[]),(171,[48,82,32]),(199,[16,101]),(236,[80,49,98,16,65,66])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V167 : Known true K167 := extend_ok (m:=167) V155 low167 (by decide +kernel)
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
theorem g173G : graphValid g173 (boundsBefore K167) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low173 : Lower true (varsX 173) (graphGoal 173) 7 := lower_forest (g:=g173) (i:=0) (hints:=1283) (before_sound K167 V167) g173G g173T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K173 := extendKnown K167 7 [(173,[]),(229,[32,99,67]),(230,[32,16,83,67,100]),(244,[32,16,65,83,99])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V173 : Known true K173 := extend_ok (m:=173) V167 low173 (by decide +kernel)
def g211Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfe1ff007f87f87ffc0,0x1fc7f1fc431ee000f000])),(BitVec.ofNat 152 (word80 [0x544aa5525129102a95,0x42912489431ee7777777]))),((BitVec.ofNat 152 (word80 [0x1ffff8007ff87fff,0xe007ffffb3b9400f00ff])),(BitVec.ofNat 152 (word80 [0x1880c0606202010301,0x83204010218941111111]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1fffffff80007fff,0xfff801ff9c1f30f00f0f])),(BitVec.ofNat 152 (word80 [0x61030180800c220c06,0x40188201c1602222222]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffe000000000007fff,0xfffffe000be4bf000ff0])),(BitVec.ofNat 152 (word80 [0x800c06030430443018,0x80200c20260b4444444]))),((BitVec.ofNat 152 (word80 [0xffffffffffffff8000,0x6442cffff000])),(BitVec.ofNat 152 (word80 [0x1008040040004020,0x10040100000008888888]))),(0x0,0x0)]
def g211C : List ColumnInfo := [(1,0,210,0,7)]
def g211A : List (List Nat) := [[],[100],[65],[65,97],[97,65],[97]]
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
theorem low211 : Lower true (varsX 211) (graphGoal 211) 8 := lower_forest (g:=g211) (i:=0) (hints:=16842823) (before_sound K173 V173) g211G g211T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K211 := extendKnown K173 8 [(211,[]),(218,[48,32]),(242,[80,32,50])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V211 : Known true K211 := extend_ok (m:=211) V173 low211 (by decide +kernel)
def g214Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0xff0ff01fe3f8ffe0,0x3fc7f1ffd675000f00ff])),(BitVec.ofNat 152 (word80 [0xa0a20a14148120142,0x82902402163411111111]))),((BitVec.ofNat 152 (word80 [0xff000fffe003ff1fff,0xc007fe3f317a00f00f00])),(BitVec.ofNat 152 (word80 [0x2c2c42c18590a04583,0xb214084b17a33333333]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffc001fff,0xfff8003fede10f00f00f])),(BitVec.ofNat 152 (word80 [0x303083020600c48604,0xc01890829c122222222]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffff0000000001fff,0xffffffc01388f000fff0])),(BitVec.ofNat 152 (word80 [0x404004040801000808,0x10020010000044444444]))),((BitVec.ofNat 152 (word80 [0xffffffffffffffe000,0x2816ffff0000])),(BitVec.ofNat 152 (word80 [0x808008081002001010,0x20040020000088888888]))),(0x0,0x0)]
def g214C : List ColumnInfo := [(4,0,210,0,7)]
def g214A : List (List Nat) := [[],[118],[65],[65,118]]
def g214D7 (j : Nat) := if j=0 then 0x3f else 0
def g214L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g214D7)
  | _ => emptyPacking
def g214I (_ _ : Nat) : Option (Nat × Nat) := none
def g214 : Forest := ⟨214,7,fun i => g214Y[i]?.getD (0,0),g214C,g214A,g214L,g214I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g214P7_0 : block g214 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g214B7 : block g214 7 0 1=true := g214P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g214T : checkedTables g214 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g214 0 0 0 = true)
  · exact (rfl : block g214 1 0 0 = true)
  · exact (rfl : block g214 2 0 0 = true)
  · exact (rfl : block g214 3 0 0 = true)
  · exact (rfl : block g214 4 0 0 = true)
  · exact (rfl : block g214 5 0 0 = true)
  · exact (rfl : block g214 6 0 0 = true)
  · exact g214B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g214G : graphValid g214 (boundsBefore K211) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low214 : Lower true (varsX 214) (graphGoal 214) 8 := lower_forest (g:=g214) (i:=0) (hints:=285279808) (before_sound K211 V211) g214G g214T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K214 := extendKnown K211 8 [(214,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V214 : Known true K214 := extend_ok (m:=214) V211 low214 (by decide +kernel)
def g63Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffffffffffffffffff,0xfb944e4fa4fd6803f03f])),(BitVec.ofNat 152 (word80 [0x282a00a12802852021,0x4b844c0320dc00145145]))),((BitVec.ofNat 152 (word80 [0xffff000003fffff000,0x76ab5eb70a632000fc0])),(BitVec.ofNat 152 (word80 [0x14c280db0a0264206,0x6762344a50a4324d34d3]))),((BitVec.ofNat 152 (word80 [0xfffffffffc00000000,0x67c4351bd4f7fc0000])),(BitVec.ofNat 152 (word80 [0xb27002c9c00b37804b,0x8026c43508d4f33cf3cf]))),((BitVec.ofNat 152 (word80 [0xffffffffffffffffff,0xf58b1674957bf000003f])),(BitVec.ofNat 152 (word80 [0xc380b30e02cc38048c,0x40b12749523f0ebaeba]))),(0x48afbb7e9c20e000fc0,(BitVec.ofNat 152 (word80 [0xfc00c3f0030fc008f0,0x88cbb5a9420cb2cb2c]))),(0xe754a985f269dfff000,(BitVec.ofNat 152 (word80 [0xfc0003f0000f00,0x451028857220cc30c30]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g63C : List ColumnInfo := [(0,2,45,16,5)]
def g63A : List (List Nat) := [[],[65],[80,50],[80,65,50]]
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
theorem g63G : graphValid g63 (boundsBefore K214) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low63 : Lower true (varsX 63) (graphGoal 63) 6 := lower_forest (g:=g63) (i:=0) (hints:=66883) (before_sound K214 V214) g63G g63T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K63 := extendKnown K214 6 [(63,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V63 : Known true K63 := extend_ok (m:=63) V214 low63 (by decide +kernel)
def g95Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3fffffffffffffffff,0x3a44c8be57b2c000003f])),(BitVec.ofNat 152 (word80 [0x914152284a450a4214,0x3a444096473255555555]))),((BitVec.ofNat 152 (word80 [0xfffff80000ffffe000,0xb5bb4067c1ae0003ffc0])),(BitVec.ofNat 152 (word80 [0xa60036c004c8066,0xb4234025018e030c30c3]))),((BitVec.ofNat 152 (word80 [0x3fffffffff00000000,0x668749bbd8b00fc0000])),(BitVec.ofNat 152 (word80 [0x59380b270166f04b8,0x468609bbd8b0f3cf3cf]))),((BitVec.ofNat 152 (word80 [0x3fffffffffffffffff,0x58b1cca9bed48000003f])),(BitVec.ofNat 152 (word80 [0x261c04c380987008c0,0x40b18c29b8c4aaaaaaaa]))),((BitVec.ofNat 152 (word80 [0xc00000000000000000,0x48af2b5ecc4a7f000fc0])),(BitVec.ofNat 152 (word80 [0x7e000fc001f800f00,0x888295acc404c30c30c]))),(0x0,0x0),(0xe754b7112b657ffff000,(BitVec.ofNat 152 (word80 [0x3800070000e0001000,0x43149600022030c30c30]))),(0x0,0x0),(0x0,0x0)]
def g95C : List ColumnInfo := [(0,1,86,8,6)]
def g95A : List (List Nat) := [[],[65],[48],[48,65]]
def g95D6 (j : Nat) := if j=0 then 0x7f else 0
def g95L : Nat → Packing
  | 6 => (1,0,1,0,0,0,0,g95D6)
  | _ => emptyPacking
def g95I (_ _ : Nat) : Option (Nat × Nat) := none
def g95 : Forest := ⟨95,6,fun i => g95Y[i]?.getD (0,0),g95C,g95A,g95L,g95I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P6_0 : block g95 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g95B6 : block g95 6 0 1=true := g95P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95T : checkedTables g95 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g95 0 0 0 = true)
  · exact (rfl : block g95 1 0 0 = true)
  · exact (rfl : block g95 2 0 0 = true)
  · exact (rfl : block g95 3 0 0 = true)
  · exact (rfl : block g95 4 0 0 = true)
  · exact (rfl : block g95 5 0 0 = true)
  · exact g95B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95G : graphValid g95 (boundsBefore K63) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low95 : Lower true (varsX 95) (graphGoal 95) 7 := lower_forest (g:=g95) (i:=0) (hints:=16844355) (before_sound K63 V63) g95G g95T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K95 := extendKnown K63 7 [(95,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V95 : Known true K95 := extend_ok (m:=95) V63 low95 (by decide +kernel)
def g111Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffffffffffffffffff,0xf9961e5fa29d940003ff])),(BitVec.ofNat 152 (word80 [0x5040150804a100a400,0xa192124c20199094a529]))),((BitVec.ofNat 152 (word80 [0x3ffff80000ffffe00,0x7eda2413e0f220f8000])),(BitVec.ofNat 152 (word80 [0x9814a602b6c054c813,0x35e502413e0e22739ce7]))),((BitVec.ofNat 152 (word80 [0x3fffffffff0000000,0x7343e45dec59f07c00])),(BitVec.ofNat 152 (word80 [0xe0013800270006f005,0xc023024419ac58318c63]))),((BitVec.ofNat 152 (word80 [0x3ffffffffffffffff,0xfa858e25cdf6a400001f])),(BitVec.ofNat 152 (word80 [0x299c053380a6700a6,0x2058c21cde6256b5ad6]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfc0000000000000000,0x245795af66252007fe0])),(BitVec.ofNat 152 (word80 [0x31e0063c00c780138,0x2446912c642034a5294]))),(0x73aa5b8895b2bff8000,(BitVec.ofNat 152 (word80 [0x3e0007c000f8001c0,0x218a5b88051018c6318]))),(0x0,0x0),(0x0,0x0)]
def g111C : List ColumnInfo := [(0,2,45,64,5),(0,8,102,1,5),(2,0,109,0,5),(8,0,103,0,5)]
def g111A : List (List Nat) := [[],[96,49,82]]
def g111D6 (j : Nat) := if j=0 then 0xe413f else 0
def g111L : Nat → Packing
  | 6 => (1,0,2,0,0,0,0,g111D6)
  | _ => emptyPacking
def g111I (_ _ : Nat) : Option (Nat × Nat) := none
def g111 : Forest := ⟨111,6,fun i => g111Y[i]?.getD (0,0),g111C,g111A,g111L,g111I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P6_0 : block g111 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g111B6 : block g111 6 0 1=true := g111P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111T : checkedTables g111 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g111 0 0 0 = true)
  · exact (rfl : block g111 1 0 0 = true)
  · exact (rfl : block g111 2 0 0 = true)
  · exact (rfl : block g111 3 0 0 = true)
  · exact (rfl : block g111 4 0 0 = true)
  · exact (rfl : block g111 5 0 0 = true)
  · exact g111B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111G : graphValid g111 (boundsBefore K95) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low111 : Lower true (varsX 111) (graphGoal 111) 7 := lower_forest (g:=g111) (i:=0) (hints:=16778595) (before_sound K95 V95) g111G g111T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K111 := extendKnown K95 7 [(111,[]),(125,[96,49,82,65])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V111 : Known true K111 := extend_ok (m:=111) V95 low111 (by decide +kernel)
def g119Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffffffc0003fffc00a,0xd27ec6ac340000000fc0])),(BitVec.ofNat 152 (word80 [0x25104a90da9094856a,0xc27ec2a03404d34d34d3]))),((BitVec.ofNat 152 (word80 [0x3ffffffffffffff7,0x20988afa71b000fc003f])),(BitVec.ofNat 152 (word80 [0x98213021302190243,0x209888e801a145145145]))),((BitVec.ofNat 152 (word80 [0x3fffffffc0000009,0xcd1cb9421e203f03f000])),(BitVec.ofNat 152 (word80 [0x4e009c009c00de0b88,0x441cb8421c20c30c30c3]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x3ffffffffffffffa,0x162d5a1393dfc000003f])),(BitVec.ofNat 152 (word80 [0x7004e004e004e00c08,0x1625121312128a28a28a]))),((BitVec.ofNat 152 (word80 [0xffc000000000000009,0x15e285ddcf000003ffc0])),(BitVec.ofNat 152 (word80 [0x2700270027001001,0x1180051dc30b2cb2cb2c]))),((BitVec.ofNat 152 (word80 [4,0xea977125e06ffffc0000])),(BitVec.ofNat 152 (word80 [0x803800380038002004,0x88024104e04c30c30c30]))),(0x0,0x0),(0x0,0x0)]
def g119C : List ColumnInfo := [(1,0,118,0,7)]
def g119A : List (List Nat) := [[],[65]]
def g119D7 (j : Nat) := if j=0 then 0x7f else 0
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
def K119 := extendKnown K111 8 [(119,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V119 : Known true K119 := extend_ok (m:=119) V111 low119 (by decide +kernel)
def g123Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfffffffc003fffffff,0x18ebdc6300bfc003f03f])),(BitVec.ofNat 152 (word80 [0xa100080084022000,0x1003d40000bf134d34d3]))),((BitVec.ofNat 152 (word80 [0xffffffffffff000,0xb7046baed4a300fc0fc0])),(BitVec.ofNat 152 (word80 [0x52c014501200504046,0x130449a6842205145145]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfff00000003fffffff,0xde763864e810c000003f])),(BitVec.ofNat 152 (word80 [0x630a59612729648494,0xce742864e800ecb2cb2c]))),((BitVec.ofNat 152 (word80 [0xffffffffffc0000000,0xc0b3c0dcffc43f000fc0])),(BitVec.ofNat 152 (word80 [0x840061804401870118,0xc0b3805851800a28a28a]))),(0xc8ad2f1b8c4a4003f000,(BitVec.ofNat 152 (word80 [0xf80c7e027831f809e0,0xc8ac2b1b8c406cb2cb2c]))),(0x6754b7112b657ffc0000,(BitVec.ofNat 152 (word80 [0xf8003803e000e00,0x244036012a4570c30c30]))),(0x0,0x0),(0x0,0x0)]
def g123C : List ColumnInfo := [(0,1,82,40,6)]
def g123A : List (List Nat) := [[],[100],[83],[83,100],[65],[65,97],[65,83],[65,83,97],[97,65],[97],[97,83,65],[97,83]]
def g123D6 (j : Nat) := if j=0 then 0x7f else 0
def g123L : Nat → Packing
  | 6 => (1,0,1,0,0,0,0,g123D6)
  | _ => emptyPacking
def g123I (_ _ : Nat) : Option (Nat × Nat) := none
def g123 : Forest := ⟨123,6,fun i => g123Y[i]?.getD (0,0),g123C,g123A,g123L,g123I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P6_0 : block g123 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g123B6 : block g123 6 0 1=true := g123P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123T : checkedTables g123 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g123 0 0 0 = true)
  · exact (rfl : block g123 1 0 0 = true)
  · exact (rfl : block g123 2 0 0 = true)
  · exact (rfl : block g123 3 0 0 = true)
  · exact (rfl : block g123 4 0 0 = true)
  · exact (rfl : block g123 5 0 0 = true)
  · exact g123B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123G : graphValid g123 (boundsBefore K119) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low123 : Lower true (varsX 123) (graphGoal 123) 7 := lower_forest (g:=g123) (i:=0) (hints:=16842819) (before_sound K119 V119) g123G g123T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K123 := extendKnown K119 7 [(123,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V123 : Known true K123 := extend_ok (m:=123) V119 low123 (by decide +kernel)
def g159Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x8007ffffffffffffff,0xff09a486fdc800007c1f])),(BitVec.ofNat 152 (word80 [0x10b0a0a85094285221,0x4f09a00685c94a5294a5]))),((BitVec.ofNat 152 (word80 [0xfffffffc0001ffff00,0x6be951ba530000f83e0])),(BitVec.ofNat 152 (word80 [0x520053006d8026406,0x66ae8512a030c6318c63]))),((BitVec.ofNat 152 (word80 [0x7fffffffe000000,0xde23f737001f00000])),(BitVec.ofNat 152 (word80 [0x29c2c9c164e0b3784b,0x800de23f7373def7bdef]))),((BitVec.ofNat 152 (word80 [0x7ffffffffffffff,0xf3d6aeb878483e00001f])),(BitVec.ofNat 152 (word80 [0x4e030e018700c3808c,0xd60eb8780294a5294a]))),((BitVec.ofNat 152 (word80 [0xfff800000000000000,0x11659ef95e7c00003e0])),(BitVec.ofNat 152 (word80 [0x7003f001f800fc00f0,0x11058ed15c318c6318c]))),(0x0,0x0),(0x0,0x0),(0xce94a740297fffffc00,(BitVec.ofNat 152 (word80 [0x400020001000000,0x421084210]))),(0x0,0x0)]
def g159C : List ColumnInfo := [(4,0,155,0,8)]
def g159A : List (List Nat) := [[],[65],[16,67],[16,48,64],[48],[48,65],[64,16,49],[64,49]]
def g159D8 (j : Nat) := if j=0 then 0x7f else 0
def g159L : Nat → Packing
  | 8 => (1,0,1,0,0,0,0,g159D8)
  | _ => emptyPacking
def g159I (_ _ : Nat) : Option (Nat × Nat) := none
def g159 : Forest := ⟨159,8,fun i => g159Y[i]?.getD (0,0),g159C,g159A,g159L,g159I⟩
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
  · exact (rfl : block g159 3 0 0 = true)
  · exact (rfl : block g159 4 0 0 = true)
  · exact (rfl : block g159 5 0 0 = true)
  · exact (rfl : block g159 6 0 0 = true)
  · exact (rfl : block g159 7 0 0 = true)
  · exact g159B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g159G : graphValid g159 (boundsBefore K123) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low159 : Lower true (varsX 159) (graphGoal 159) 9 := lower_forest (g:=g159) (i:=0) (hints:=67395) (before_sound K123 V123) g159G g159T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K159 := extendKnown K123 9 [(159,[]),(190,[16,32,48,64,80])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V159 : Known true K159 := extend_ok (m:=159) V123 low159 (by decide +kernel)
def g175Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffffffffffffffffff,0xfff0ddac7c810000f0ff])),(BitVec.ofNat 152 (word80 [0x1480a002a00940148,0xa70450c508111111111]))),((BitVec.ofNat 152 (word80 [0xfffc007fff0001fffc,0x3df4671468000f0000])),(BitVec.ofNat 152 (word80 [0x959153294c56d8a991,0x333df467146877777777]))),((BitVec.ofNat 152 (word80 [0x7ffffffe0000,0x86517cfdc00f00f00])),(BitVec.ofNat 152 (word80 [0x19e09c027004e00de0,0x5c0065164edc33333333]))),((BitVec.ofNat 152 (word80 [0x7fffffffffff,0xff968d73ae0b0f00000f])),(BitVec.ofNat 152 (word80 [0xde02e033806700ce02,0x60068873ae0a66666666]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffff800000000000,0x8bacf93a6f0000ff0])),(BitVec.ofNat 152 (word80 [0xe003003c007800f003,0x80089ac1812244444444]))),(0x0,0x0),(0x674250407afffff000,(BitVec.ofNat 152 (word80 [0x400080010000,0x88888888]))),(0x0,0x0)]
def g175C : List ColumnInfo := [(2,0,173,0,7),(1,0,174,0,6),(4,0,171,0,6),(8,0,167,0,6),(32,0,143,0,6),(0,2,45,128,5),(3,0,172,0,5),(6,0,169,0,5),(9,0,166,0,5),(12,0,163,0,5),(34,0,141,0,5),(36,0,139,0,5),(11,0,164,0,4),(128,0,45,0,4),(128,2,45,0,4)]
def g175A : List (List Nat) := [[],[80,50]]
def g175D3 := limbs80 #[#[0xa82419818750f5150120,0x85585504826832642ac2,0x6304c8650]]
def g175D4 := limbs80 #[#[0x50d50443c45514354110,0x442a56126550d109d087,0x60275485208e7825d265,0xd45209e3805cb5148278,0x8b7845db5148235e0d76,0xd4540483e050f5150120,0x4827861f5150120ba184,0xe116150120f814358540,0x50120f81435c540482e8,0xd8b7550d40483625d543,0x5855048398d956154120,0x483c25514354120b6085,0x60c65541209c88750d50,0xd4520b298419550482d2,0xdc3835c3514837050d70,0x5d35148278e1170d4520,0x48271e0d76d45208e786,0xdd143585209a7845db51,0x585209c5831d56148361,0x9e180dc5544826961075,0x594654830b5957419520,0x54239e0976d454086f87,0xe0d70995218e7825d361,0xd85528d584dcd60d4635,0xf060240c0300235e0d70,0xc2b140843c1b0c054240,0x4a44f26114843f1e0e45,0x1c4dc6b32184bc5b2c15,0x10c83401f4f4773a,0x40010e0800000000000,0x26080000009a1,0x238200000]]
def g175H4 := limbs80 #[#[0x40000d80000000900000,0x9]]
def g175D5 := limbs80 #[#[0x6f0b86a2907894350120,0xfa286a822135dcd60d4,0x43b8aa2a0887d3735411,0x10f2aa8a1a21f4dc1434,0x4436abb286886d66550d,0x5109eae532a2179dc954,0x1483f090aa0904f57499,0x8520dceca90a41b95952,0x51482f8b86a2905e6754,0x549209eaeda8a41795cb,0x352482f3b8aa4905eb70,0x359520cdecba92417a5c,0x45404825fba2ca904df7,0x7150120fc2c2a0241f8d,0xd9140483d4aa280907e1,0xb7550120bd2eaa0241ea,0x858550483f1a8aa0905e,0xc94354120fc6e2a8241f,0xda55150483e5b9aa0907,0x5eb7454120ed6a8a8241,0x1dad9550483b432aa090,0x7c543d4520fc2e1a8a4,0x41795db51482f2ba6a29,0x907c54358520bceeda8a,0xa41b959561482f3ba2c2,0x6905e47558520dcecab0,0xa24179dc554483e5b828,0xa8904ef76551209d8eca,0x32a41795c764482f4b86,0xca905cd7319520bcae2,0x2b2a419b59465482d6ba,0xa2ca905cf7359520bcee],#[0xe3b2a419bd9665482d7b,0xb86a2a07395454140bca,0xee4b2a813d5db51502f8,0xbb1ea2a86d763485509d,0xeae5b0aa1b5d8f615436,0x6bb8ec6a84f574d85509,0x9dee4b26a1375d363543,0x67ab84ca90de77054921,0x19eee4b06a375dcd60d4,0x467bba2c1a8ed7735835,0x529eae1b0aa53ddc162d,0x2106a14036004df73583,0x4a91e448f83b0d22e09e,0x6d1a8671906117854136,0x8c216829fe7c9e6731c0,0xc02e6afa96a2a6295a4a,0xe2b70d9358cfb32c9b0c,0xfc3302be2eebaee8b96,0x394d92fca52647f1cc59,0x54d394b521455093f4f1,0x705b56a59d645855e56d,0x8be2385e0b7c5e5765cd,0xa01270b80797e5391e3b,0x3205002381c00c006882,0x900054c1000006020,0x1c100000026080000000,0xc20d4c20098208000302,0x4c1000260812010f4,0x83b40a3b408000001982,0x80081009821c101a100,0x3820000000000001c126,0xe04],#[0x302]]
def g175H5 := limbs80 #[#[0x4a740240601040670846,0x44b51ec978c80011dc7f,0x19640f00091334f04,0x3481460001492100000,0x15f000002ab0000,0xb6570200061800000638,0xc000792c4000000c8366,0xaa2738a8298d73a201c,0xf168870d800b25e5c005,0xe0000072394c00000403,0x4a200125448a9640]]
def g175D6 := limbs80 #[#[0x550d10bd58910fc54110,0x48520bd99510bd59110f,0x4520fa54120fa50120f9,0x720f350d20f958520f9d,0x21b7d8d50bdd8550f9d4,0x1bd58351bd99521f9549,0xfd54910bdd8552bd58b5,0xdd4520fe54120fd55110,0xd4920fb54920fd58520f,0x5120bfd9520bf59520fb,0x120fb59120fbd5120fb5,0x20fb59520fb19520fbd9,0xfe54140fbd9520fb995,0xbf59540fd58540fdd454,0xdd4550fd48550bfd9540,0xd8d50bfd8950fdd8550f,0x9150dfd5150df55150f7,0x351bf59350bf58b50bfd,0x52fd58b51fd54b51fd58,0xbf58352fdd8552bfd81,0x50228390600900c00c00,0x558a212c2283c06c0c01,0x8fc1e039c6c0cc1862dc,0x62944f89792623a45085,0x4e66cca9892ee5acb115,0x7b0f01d43966f0d99ad3,0x518a2843885906a013f0,0x31c1cda9852aa4f48c8f,0x3741c1a6dcc1d0d9c190,0x185810a0858f40741a1,0xa422e83d01c485018581,0xe01002d01a14561a7160],#[0x619ac0549b5867163870,0x91c18c7054802d621acb,0x430e10b10498581c20c,0xa08018a2060088021207,0xa068161280a01a80a018,0x2a26806a2610280a120,0x2143042827021028068,0x18c1c670e18a00428610,0x841c380628011a05019b,0x70601c10a18019c0880,0x28200628268e12628410,0x60807086c4006]]
def g175H6 := limbs80 #[#[0x11e28003103101301000,0x80000000000000204200,0x5ad00000000000004,0x24e1a000000000000000,0x5aa4000000c580000008,0x387000e120410008162c,0xc3e935000000130,0xe5513f000583000f040,0x15c2000000000,0xd00000000000004ee40,0xc1900000000043b1,0xd3100000000039c00000,0x9d000000639d3af22000,0xc0000000000000000001,0x10192ae03a1855280,0x27a0bf1e00004b000000,0x70000000006b0007a4c9,0x317000f060000002c,0xf00000000000000000,0xe560000000000000,0xb4360f6a600000000,0x91c000,0x1854330000000000000,0x7143518b90004b844500,0x91d00000003db49,0x601b93c347000000b340,0xa0e000037228e2c84,0x5492b000000000000832,0x12eb9ff,0x900000000,0x2600000000074fe36000,0x1000000000738000188c],#[0xe4a000000710000c2,0x29000000d13000000f89,0x110000000005080002,0x79a00045700000000,0x0,0xfb500082d0000000000,0x82500011f00000000,0xb6000000000000000000,0x20005a0f23e2f54418ad,0x20500000000045000044,0x4d10aa86000753,0xc020]]
def g175D7 := limbs80 #[#[0x751fa90fbc83da41f510,0xa5ff50fea87f503fa41f,0x8734124681a007fd4bfa,0x476d061230f96d2ed42,0x815d14ace2c10b0c5482,0xae82d023a0858990377,0x14c16290504385710504,0x14c16e15c]]
def g175H7 := limbs80 #[#[0x2c80027a2100283040a,0xf105879e160f001ccc33,0xce05c26b14710c9,0xca424000001694000000,0x8007a7aeb0300060425b,0x35810000028b80000085,0x28000003e7d0881521b9,0x45c074000009a1e4c001,0x24495065db7083400403,0x2cb0006c00073401,0xa14000000000,0xb6eab0000000015cc,0x19005d3ea00000000000,0x1629348156f1c0018c3b,0x31000000b282bc000001,0x33600000000a2a,0x8ee4000002b57ef53200,0x36000518002ab00e4a80,0x31a46508f913]]
def g175D8 (j : Nat) := if j=0 then 0x9b8013f else 0
def g175H8 := limbs80 #[#[0x3c7e10066609100401,0x9a803303300000400064,0x31eb80001307302400ba,0xa1014008a0034b0e]]
def g175L : Nat → Packing
  | 3 => (3,5,4,0,0,4,0,g175D3)
  | 4 => (39,4,4,0,0,9,0,g175D4)
  | 5 => (89,3,4,0,0,10,0,g175D5)
  | 6 => (57,2,4,0,0,11,0,g175D6)
  | 7 => (11,1,4,0,0,9,0,g175D7)
  | 8 => (1,0,4,0,0,0,0,g175D8)
  | _ => emptyPacking
def g175I : Nat → Nat → Option (Nat × Nat)
  | 4 => lookupWord 1 17 0 6 2 0 g175H4
  | 5 => lookupWord 12 73 5 11 6 1 g175H5
  | 6 => lookupWord 27 281 4 12 7 1 g175H6
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
theorem g175P4_0 : block g175 4 0 39=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g175B4 : block g175 4 0 39=true := g175P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175P5_0 : block g175 5 0 3=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175P5_3 : block g175 5 3 86=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g175B5 : block g175 5 0 89=true := (@block_merge g175 5 0 3 86 g175P5_0 g175P5_3)
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
theorem g175G : graphValid g175 (boundsBefore K159) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low175 : Lower true (varsX 175) (graphGoal 175) 9 := lower_forest (g:=g175) (i:=0) (hints:=1395) (before_sound K159 V159) g175G g175T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K175 := extendKnown K159 9 [(175,[]),(189,[65]),(238,[32,49,16,80,64,100]),(252,[32,49,64,81,97])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V175 : Known true K175 := extend_ok (m:=175) V159 low175 (by decide +kernel)
def g183Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfffffffff0003fff00,0x539ebc14d000000f83e0])),(BitVec.ofNat 152 (word80 [0x2a925012a0da82522b,0x530e3c14d018c6318c63]))),((BitVec.ofNat 152 (word80 [0xfff803ffffffffffff,0xba7524be130001f0001f])),(BitVec.ofNat 152 (word80 [0x3209884c213086412,0x3a75041213294a5294a5]))),((BitVec.ofNat 152 (word80 [0x3ffffffc00000,0x4a67074dcc003e007c00])),(BitVec.ofNat 152 (word80 [0x33c4e027009c03785c,0x4267064ccc18c6318c63]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x3ffffffffffff,0xd48f73ae0907c000001f])),(BitVec.ofNat 152 (word80 [0xbc07013804e0138060,0x448a73ac085294a5294a]))),((BitVec.ofNat 152 (word80 [0xfffffc000000000000,0x48b8cf93a6f800007fe0])),(BitVec.ofNat 152 (word80 [0xc00001c007001c0080,0x890c183226318c6318c]))),(0x0,0x0),(0x274250407affffff8000,(BitVec.ofNat 152 (word80 [0x2000800200000,0x8421084210]))),(0x0,0x0)]
def g183C : List ColumnInfo := [(1,0,182,0,8)]
def g183A : List (List Nat) := [[],[65],[32],[32,65]]
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
theorem g183G : graphValid g183 (boundsBefore K175) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low183 : Lower true (varsX 183) (graphGoal 183) 9 := lower_forest (g:=g183) (i:=0) (hints:=66885) (before_sound K175 V175) g183G g183T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K183 := extendKnown K175 9 [(183,[]),(187,[48,82,32])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V183 : Known true K183 := extend_ok (m:=183) V175 low183 (by decide +kernel)
def g219Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x1fffff87fff78721,0xf09a80000007f000007f])),(BitVec.ofNat 152 (word80 [0x294428811122078520,0xe08a952a54a952a54a95]))),((BitVec.ofNat 152 (word80 [0xffe003ffffff0221ed,0x27c3000003f8001fff80])),(BitVec.ofNat 152 (word80 [0x180b00a000422206d,0x224203060c183060c183]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffc0007fffb1ad1,0x9a518001fc000000007f])),(BitVec.ofNat 152 (word80 [0x4208c12c2248081ad1,0x1a512a54a952a54a952a]))),((BitVec.ofNat 152 (word80 [0xfffffffff80008caba,0xc38c00fe00000fe03f80])),(BitVec.ofNat 152 (word80 [0xc010030007048c292,0x81880c183060c183060c]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x92d42,0x4c3f7f0000000fffc000])),(BitVec.ofNat 152 (word80 [0x700e01c04380810d00,0x4c353060c183060c1830]))),((BitVec.ofNat 152 (word80 [0x4d414,0x28607ffffffff0000000])),(BitVec.ofNat 152 (word80 [0x801002000400000000,0x4081020408102040]))),(0x0,0x0)]
def g219C : List ColumnInfo := [(1,0,218,0,8),(2,0,217,0,8),(8,0,211,0,8),(16,0,203,0,8),(64,0,155,0,8),(9,0,210,0,7),(0,1,82,136,6),(0,8,82,129,6),(128,0,91,0,6),(3,0,216,0,5),(8,1,82,128,5),(17,0,202,0,5),(18,0,201,0,5),(65,0,154,0,5),(66,0,153,0,5),(80,0,139,0,5),(128,1,82,8,5),(128,8,82,1,5),(82,0,137,0,4),(129,0,82,0,4),(129,8,82,0,4)]
def g219A : List (List Nat) := [[],[100],[65],[65,97],[97,65],[97],[48],[48,100],[48,65],[48,65,97],[48,97,65],[48,97]]
def g219D4 := limbs80 #[#[0x51c85e1193d915354510,0x30c45e13935d153d45]]
def g219D5 := limbs80 #[#[0xa8a21a176460f5454531,0x6454d51442cab27b22a6,0x8aaa2a7b8a868868de13,0x1a214e5921977150d10e,0x5dc5434429ab2632ee2a,0xac9ccbb8a868843d6606,0xa210f5989977150d10a6,0x5cc6544313ee8c1ec8a9,0xca30e98ea0a8535e4584,0xa1e8543d89414c5508dd,0x8931543c8aa7b12a298a,0xb286a0a63a852be5175d,0x10bf9461b754c750e4ab,0x5604c716909c0aec98ea,0xeab2ac098d4d6507554,0xc97975954350531a1eca,0x414c7c2f2caa2a6a0a63,0xeaa9a8298f45e517554d,0x4553e097054531e2bcb2,0x14c7c2ac8aa2a6a8a63b,0x8a9aa298f45dd15454d5,0x764d515354531b2bcb2a,0x4c732f09ba2a6a8a63e1,0xa9aa298f85dd36454d51,0x84dd15354531b2b4bec8,0xc7a2ee8aa6e6a8a63b17,0xa2a298e6561374dcd514,0x460f5454531b8ac9ea8a,0x7c2ec8c1ea8a8a63a976,0x2a898e2de13815d9544c,0xe0970d5131c6ac1b03bb,0x92ec8b9ae3aa2638af64],#[0xca98e65e0f81dd1654c7,0x97059531c5a3a702b82,0x5ee9c12e0b2a638ac74e,0xa98c2fa60745c1654c71,0x77459531e4bba6e7b8ac,0xf24c06e8b2a63a9783e0,0xa8d2be5163dc96054695,0x53d4551aabc9ae8a9ea2,0x9ba6e2a9aa3937845d1,0x8d2de4574d935354726b,0x458f51b1bc8ae9b26a6a,0x90180300189f74e0d6,0x4210781b060150480f03,0x45213c4c124410f8360a,0x87e1ec781c0681805d15,0x4aa2889f270992588921,0x8db338c12f8b62ccb02b,0xfd3e8f73a8e7390e137,0x431094190340,0xa469085e10200000000,0x81920200000002020242,0x60208003020e860e860,0x1c08000002874084,0x19821587a08401820800,0x1322c81000000006]]
def g219H5 (j : Nat) := if j=0 then 0x3e800002c88 else 0
set_option maxRecDepth 16000 in
def g219D6 := limbs80 #[#[0x50d414c62fe11764c750,0x4c7c55515350531e9565,0x5915354531d557554d41,0x54531e576454d514c795,0xb5583d51514c755dd153,0x5d9544c78dd935454531,0x4c72dd9171d51318f781,0x1d37159531a3d85d9354,0x54110bf38150d504432d,0xaf984d8d504433edd363,0x50d514427e6137354110,0x442dd6154354510f5553,0xd915354510f577354d51,0x54510b778454d514439d,0xaf584d8d514439d21953,0x5cd51442bda1f6354510,0x4437554f7150d10bb784,0x9977150d10cf465dc543,0x50d109f585dc5434433d,0xaed8219543443c755153,0x19543442b760c6550d10,0x442bbe096550d108fd87,0x60e6550d108ff8759543,0x50d108fd8799543442b7,0xadd83d91534427de0575,0xd91534432fdd36454d10,0x4423fa1f6454d108fd87,0xe1574d8d10a7d859d953,0x195108ff845d7634423f,0xcdd845cc654423fe1173,0xdcd6544337e117319510,0x5423fe1173995108fd84],#[0x61d31d4150df1714c750,0x4c5509fb835c7505427e,0xf954350531543b9d8941,0x54531543b9d89514c550,0x5433b5d3624c550f5553,0x5d7624c550cef74d8931,0x4c550cef75d89315433b,0x8fd87d91315432fdd364,0x5d9315426fe11754c550,0x542bbe09764c550af781,0x606764c550abf845d931,0x54550e6d53d8951542bd,0x8ff845cf615433bdcf62,0x50531d43e550d414c750,0xd433d5d9414c750ed563,0x58d514c750f555354531,0x4c750ed56358531d43b5,0xcf57458531d43b5e0d61,0x58531d433ddd1614c750,0xd423f61d644c750af784,0x61b744c7508ff8759131,0x4c7509bf845d531d423f,0x8fd86dd531d423fe1975,0x5d931d42bde05764c750,0xd426fe11764c750abf84,0x211764c750cf7815d931,0x4c750cbf845d931d432f,0xaf5819d931d423fe1176,0x58d51d423f61e764c750,0xd4337dcd6354750af781,0xe117358750af78158d61,0x581318fd84dcd61d42af],#[0xd7475545604c7d554d51,0x595604c75ddd55158131,0x4c71f1d56558131abf84,0x6087558131c7f7559560,0x505319bd841d5604c67b,0xf958454d414c7e555153,0x54d414c7755d55350531,0x4c7b5e0d6550531dd787,0xe1d6550531eb78459541,0x54531be7825c1514c73d,0xbd7835c1514c7d554d70,0x54d514c7d554f7054531,0x4c7d5d515354531f5554,0xd915354531ed56454d51,0x54531dd77454d514c7b5,0xf557454d514c7d599553,0xdcd514c7d5dd15354531,0x4c7d5d537354531f5554,0xdd37354531dd574dcd51,0x54531bd584dcd514c775,0xdb774551514c7cdd5154,0x551514c6bde195454531,0x4c7cddd15454531f5583,0x60f5454531e778655151,0x54531eb764d51514c6f5,0xeb774d91514c7d560f54,0x5d1514c6bda1f6454531,0x4c775e0f7454531bd783,0x6077055131bd58399551,0x551318fd86dc1544c67d,0xbb581d51544c7755cd71,0xd51544c78f5975455131],#[0x4c6afe116555131abd86,0xe116555131e778159554,0x55131af7815d9544c78f,0xcf581dd9544c73de0576,0x5c3544c67be0970d5131,0x4c7755cd71d5131cbf64,0xe0d71d5131eb7645c754,0xd5131abd85d93544c775,0xe7781597544c6af61f64,0x5db544c78fe1165d5131,0x4c72fe1176d5131cf781,0xdcf7159531cbf845d764,0x59531db774dc5654c775,0xdb781dd1654c72fddb74,0x5c1654c72fe1b7459531,0x4c6bbe097059531af781,0xdd17059531cbc745c165,0x59531abf845c1654c72f,0xcbf74dc1654c72f1d370,0xdc5654c7b5dcf7159531,0x4c7addd37159531eb474,0xa1c7459531af584dc565,0x59531af7815d1654c6af,0xcbd80dd1654c7ade0774,0x5c2654c72fe037459531,0x547755cd71995319ef82,0x58f7258151d6d53dc960,0x58151cef63dc9605473b,0xabf8458d6054757dcd53,0xd8f60546afe1163d8151,0x5463fe1173d8151cdd73,0x5d153d4551f576354f51],#[0xd4551b778454f515475d,0xdd573d8f51546ede1163,0xdc5535467de1173d4551,0x5475d5537154d51ed763,0x6137154d51d7754dc553,0x54d51cbf74d91535467d,0xf5783dc553547d5d8f71,0xdc5535475d5d37154d51,0x546dd6137154d51d7774,0xdd36454d51b5f8359153,0xd4d51e5f83d91535474f,0x9f7815d3535472f5d364,0xd9353546d7e0d64d4d51,0x5478f5d364d4d51d3d74,0xe0574d4d51b77815d353,0x58d51db474dc5635475d,0xd9f731d1635476ddd371,0xd93635476de077458d51,0xd46bbe0970d8d51add83,0xe057458f51adf8359163,0x2701800fc0c0060002bd,0x5851c4e04c846839c318,0xc6c068466c6306185945,0x7f87e07c878c7747386f,0x789188b88a088884c834,0xb04aecab0a74a389d89,0xca8c90c54bf4bb8b7cb4,0x28decdd4d98d5ccfccc0,0x1068fc0f84f00ea0e64e,0x1a11651290ed0d509908,0xfd2e52cd2912552191dd,0x95cd5494c54654293ed2],#[0x7056ed6b169965d64560,0xa986d8317f57b9759741,0x59c998d9519158fd8c18,0xbb5b79b3da95a59a41a0,0x7dd41cbdc5dc21be5bcd,0x9f51f15ed9e79e19db9d,0x23a1da17a11a0ba059ff,0x224c248644a37e2fa29a,0xe6d269665a61e5be55e5,0x8be8a686a82e7ce74a70,0xf2a92a329f69ba95a91e,0x2c36c1ebe2ba6b6ab2ea,0xe6ae2edced26d0ecaec7,0xeafaef96f5af1eee2ea6,0xb1531170db07b063026f,0x2d329727f2672071a716,0x74a74233e73ab36f30f,0x362760f5d359755b51f5,0x75f74770b6f36b769f66,0x7385b81f8077ef7b3777,0xf9b799f9639278eb88b8,0xaefad7a9ba5fa47a0b9c,0x6fc33bf7bbbb7fb43b2b,0xbc5c00bd83d47d2fcf3c,0x8181da4a186120419240,0x1818e4101e0e0631d8c0,0x41d64080a0f72430363b,0x10903c30400770c24604,0xc081a2040d1204001b90,0x80200401630201068,0x211e1820002082070010,0x8c1d18042c08102d1e04],#[0x3020804000800407460e,0x40400000080400101810,0xe102039017202e46084e,0xf84210e49230b840f081,0x100009e1b84211246088,0x20107840818103020290,0x8c000a104020e841d08,0x10107020f0703047c01,0xe008430088f801e18421,0xa1040d18200181018223,0x42080410200020380081,0x402080040400003c007,0x23901000008001000204,0x8000241048386d002c12,0xc0ca18608e085c1040c0,0x669020700c2018212041,0xc40913860e9010629020,0x4240d1820480c20990e,0x43902720202808202a1e,0xe7250c381c04280b9020,0xc0804106021c943808a0,0x4040e018403041e43081,0x20805020e0c186030c0,0x4020ee18483b2020304,0x1e04201820e618406041,0x18080886410800080c14,0xa407480800102020405,0xe8220184e084c1042408,0x84810183c3a08408d230,0x52020690109021206480,0x8481b230c2021808301,0x12c01036c4158810000],#[0x7202e486050c04180800,0x9c01232c8640ec80b801,0x80e4058208301e082038,0x60410000081a204260,0x42000620200181070208,0x820004104820d04151d0,0x402000c1000205041c0,0xa306c00e8c1040203040,0x800c0519643206]]
def g219H6 := limbs80 #[#[0x18840008011004212020,0x108001d8001,0xe0006021602800000000,0x6160000852881c000592,0x58480000001,0x90000c2b000186d00000,0x486a00000000000000c0,0x3200000000000000000,0x8b80000007,0x400800000,0x12a0007168000000,0x7d072178000,0x98005e8a1aae00000000,0xfa072678000000000003,0x1818800000049cf09a,0x5761c494800000000000,0x86bb83460be864208c0,0xe208000a840000000000,0x2800008520000001,0x68006018000a0a80000,0x0,0x86e0006847c1b0000000,0xe4fd,0x1470c060e06000000000,0xc2a813c817000,0x238000000081f22b8000,0x1a14000000059ab6,0x21070c4000486600,0x0,0x680000000000000144a0,0xbc00c1564048001e0dd8,0x181b40f008],#[0x594600060540005900,0xb0000000000000000000,0x1448e83946,0x0,0x10160000,0x1c13683e000284a45980,0x2c000009e000000,0x85000000000000,0xe884e0000001c09d9240,0xa0458b7644000160,0x380000000aa8000,0xc03000124d0,0x1e0c69c6e0500,0x1010b05a000000,0x4844000696a]]
set_option maxRecDepth 16000 in
def g219D7 := limbs80 #[#[0x26eb98ca884ed7219510,0x19dae5b02633bdc96544,0xc7aaa9aa298f95435053,0x3197ae832a633e5c0654,0x44277b92c1a8cbf74595,0x110df6c6a8221bed9130,0x1443baa9aa2885fb7354,0x8d10beee2a1a21bdd8d5,0x634427eba6c6884ff745,0x595109fae632a213f5d7,0x7505427eb9cca884ff73,0x254550ddec498aa17e5c,0x8531d427eb9ec2a86ef6,0x73587509faec98ea1bd5,0x595414c7eaa9a8298cff,0x77354531faaa6a8a63bd,0xdd51514c7baaa2a298fd,0xf76454531deac8a8a63d,0x9f595544c6fbba2a298e,0xcfd7655131cfccaaa263,0x37d5c7544c67fbb2a898,0x8e7d65d5131d7ec9aa26,0x633f5d7644c67ebb6a89,0x98dbf7459531beee2b2a,0xa63af1d1654c77bb8aca,0xa98cff7459531d7ee8b2,0x2a633f5da654c6fab8cc,0xc0a8def72581519fae93,0xa8aa3dd54f515467eb9e,0xaa6a8df77154d51beae7,0x9a9aa39fd9153547bbb8,0xa2c6a8d7d74d4d51cfec],#[0xc9a9ea33f5d363546dfb,0xa1aa0884ff7458f51cfa,0xae6a8a21fd50d51443fc,0xea9a86887f77354510fe,0xfacaa1a21bf19543443e,0x7fb2a86886fe6550d10d,0xefaa8a9a217f5d543443,0x2ffba2a6886ff6454d10,0xdfceca9a21bf1d95344,0x43fcb8262a87f931d415,0x50feaa298aa1fd505315,0x5437fb2262a87ef624c5,0x550bfee898aa17f5d131,0x1542ffbaa62a85fd754c,0x4550dfcec98aa1bf5d93,0x31d42ffb9aa2a877d535,0x4c750feaa298ea1fd505,0x131d437eb2263a87f561,0x54c750bfee898ea17f5d,0xd931d42ffbaa63a85fd7,0x764c750bfaec98ea1bf5,0x54d51d42ffbb263a86fe,0xf7354750dfac6a8ea1df,0xfdcd61d437eb1ac3a85f,0xff7358750dfae6b0ea17,0xbf595604c7faa8ac098e,0xdff7558131bf8eab0263,0x3fddc1514c7fab82a298,0x8ff75454531feaa8a8a6,0x63fddd1514c7faba2a29,0x98dff7055131feccaa8a,0x263efd51544c7fab8aa8],#[0x898efd7655131dfacaaa,0xa2637f5c3544c77fbb2a,0xa898efd65d5131feae3a,0xb2a637fdc1654c77ebb6,0xaca98fbf7459531feee2,0xb2a63bf5c1654c77f32,0xa2ca98efd7459531dfee,0xe332a637f5c2654c77fb,0xb1ac0a8f7d5358151fea,0xee6b02a3bfd8d605477e,0xeb1ec0a8f7d53d8151bf,0xfae7b02a3bfd8f605477,0xfbb1ea2a8ff563d4551b,0xefaa8a9aa3fddc553547,0x77fb22a6a8f7f5454d51,0x1efec8a9aa3df5915354,0x46feba6a6a8eff64d4d5,0x51efec9a9aa3df593535,0x547fbb8ac6a8f7d74d4d,0xd51dfac8b1aa3f7d8d63,0x3547de3a2c6a8eff6458,0x8d51bfee8b1aa3efdd16,0x635477fb26c6a8ff771d,0xd8d51dfae1b1aa37f5d3,0x3635477eba6c6a8eff70,0x458f51dfac8b1ea3bfdd,0xd163d477eba2c7a8dff7,0x816008a02e00d8001bfd,0xa0da06182b0132086035,0xb850026211e08583f01d,0xa21be0d5866030216e0a,0x2f892046221e10787c03],#[0x5922ae14f8a504ea2661,0x19f8ca06323061798b70,0x79a3b21c78e206fa362,0xa22b90d08323fe1f78f6,0x9da4da25f928091246,0x862b59540a7a52a28b94,0x8a0c225fa2ef96f0b525,0x69e34799f0cca64631d9,0x9ba0dc26d63639ad0d52,0xa75e3a39cd0e4271237d,0x99f00f6a7a23c99e00ed,0x82832411a040ff27e23e,0x45a2110ea86642fa1510,0x1ca8d6463a2d113a8924,0x4a9a4f123a90a47da3c1,0x13829aa4cda6212e2966,0xa501a7f13e29de4eba72,0xb14caa56525a911462a1,0xc2557aaa153aa8a53da9,0xcb163ab0a579ab715aaa,0xb7a5b9ad916aab4659da,0xaf9179abbe5d5ae71712,0xac36615b07181ac065f9,0x9b2218eac6662db12187,0xb2cd2665b301962ca264,0x41c21146d0a67fb3b19,0xf04405e4c108c513938f,0x9448407c3c11013938c1,0x8443111081e512180c07,0x30511c3c110130f04202,0xe4e307c11015930f0796,0x5030985100c0c2614404],#[0xc402440163c510100418,0x7159040541c52f0f158,0x4402446408c5a309168f,0x440463e4c108c514131,0x9861440408c563139317,0x70a8807a4a3c0a11c201,0xa1140c291e928f028440,0x3a104c5148423168c404,0x31204218f93168450ca,0x1e4e2e081100c1f0c329,0x1930c61110120e043021,0x3054746081210443a304,0x4818c64c310211d1990,0x4851110120c330f069,0x60200c3c1a4201c1808,0xc0930450442930c60807,0xc107060200a420481244,0x2081c180800329060cc3,0xc30c0f0f8b8306305411,0xc641b0f06338b81906e4,0xf8b0781908c3e2c1e08,0x4871110411210301c1b,0x1116410170f041c18080,0x189d8b938e8304407c3c,0x4318c4040c63c10406a5,0x9b11068c581116310104,0xd93068c4111041a3109c,0x8c41930460cc164a3103,0xc88c64e2e0a3c1183046,0x31010381c180b0401928,0x1c19900803068c811c1a,0x44051463a28109061820],#[0x40c646346c0158e00bc2,0x5003c724860a07011824,0xfa342800614228d0a050,0x42a310090c1a8e043c40,0xc900c40244231008182,0x86004100700402440906,0x88c30bc2a1090c141b09,0x844c1848623c21310930,0x84c1830c0624a113150a,0x93081b00444c21306130,0x1084d110a844c206c00c,0xc20b060f08844050406a,0x3c0862314930038308c5,0x24a10c0c07001a8c4098,0x20644c00c101b00483,0xc24c00c1912843c00493,0x9c0231484202c0068410,0x23210c248f010c408430,0x198c264630807018c3c0,0xc1d93041a804090b0c0c,0x402c2450b082422c1090,0x51b0c2130962c3130680,0x39930c2040c640881c31,0x4302192070c50e64c30c,0x42230412041b043030c0,0xc3c1a4144810ca408930,0x10812108b044c1850c08,0x4198030ca408481a4c34,0xa4c10c0c930630312070,0x10481066008199189804,0xc048b04198040cc3c164,0xa223a01450408e882450],#[0x309630c2c1a888040664,0x88e8030b640906804031,0x8105918c3031063a00c1,0x434424a3c110228d043,0x9928c30f64a3c1120c23,0x328d90308648141a3143,0xc08640c481a30c086410,0x3083010ca30990302030,0xc38ca3083c93068c424a,0x8d0420cc1a3641230928,0x2600c39928c324c1a30c,0x1a311901640419802066,0x4164082305928c40824c,0x21902]]
set_option maxRecDepth 16000 in
def g219H7 := limbs80 #[#[0x24001000600004000423,0x10020008c208c4010022,0x200030902128c0010021,0x802038c000806018000,0x4402080001c8018840,0x10860000e000ce310423,0x803284060006500040,0x7acf80000000000,0xc0000000000198000000,0x7a139800000000000205,0x19039109b087285d222,0xa5820389980000000000,0x34b5b6213182a00005b5,0x3010f06b20442151e85,0x0,0x20000000000000000000,0x612,0x300002b25e03e0000000,0xd0000000000000000402,0x700,0xb4003000000000000000,0x96580004944a81e184,0x0,0x0,0x28000000000005802000,0x82820c01638558000707,0x7048f822c00,0x11370000789,0x9d8210000782b3850000,0x540,0xa8000100780000000000,0xd8000187271808000332],#[0xe000020010016884af94,0x5080a901280000158804,0x18000000058310000205,0xb580180000000000028e,0x5925484631c,0x2d0ed063000,0xa0000000000003181800,0x4d8578000701d0000783,0x28c88000002981c,0x126c80000000000,0x295d00000000000,0x48c5800,0x38c67a6c00000000000,0x706680007509000,0xa1832800068318000000,0x584a000000000000096,0x6835000000000000000,0x2a69905fe1030000000,0x70c3b000021d0314f000,0x18000485800000000580,0x48000000000000000101,0xa,0x385b800,0xe8927e85280000000000,0xc80005818800000002ac,0x7073e20ee86,0x1b02c000000000000000,0x4000000000000690a902,0x324f28e2fa6f910,0x496c800000000000000,0x0,0x304c50e9514a116e000],#[0x2a09484b80000000000,0x1957d00eb93a0000000,0x60000000059262842800,0x80,0x309380000000000,0xcf938616680000000000,0x9c58000283,0x1023800000000000000,0x98000505a00000000000,0x314e80000000000001a,0x40e2000000000000000,0x616c70438000000,0x102f800059ca0000000,0x400002c0a9a06b851800,0x8bd80000000700,0x4130ca0190000182b800,0x169f8520000693,0x0,0x3874800008148000000,0x700000000501b304d000,0x146000068268000702,0x480e08240000000,0x629cb800000000000000,0x4c9e9000058698000485,0x5056e24d80000000410,0x712f800,0x405ca9b8800,0x7359800000000000000,0x48320000000058a2800,0x0,0x200000000731b8000000,0x283e90680000089],#[0x4834000030a88000000,0x7905106bc2048000000,0x1860c03d8000000,0xa8029682489060000000,0x70000401858362041401,0x686e000000000000004,0x10760000681bf919800,0x5f0390000504f0000000,0x9902c8000683a8000487,0xc0000480b80000837783,0x80000780a00000000180,0x3870a0baa82,0x196b800,0xf8000606480004038000,0xa800800000000000400,0x795e8000319f88e6292,0x19b800000000000,0x650e08c2000038ee800,0x0,0xd800000000000712c000,0x70c1800069bcc02e486,0x7a0e0000000058a3000,0x0,0x459d1000000003067800,0xe40c08b3b51568000587,0x700004324000060f0785,0xec15c800000000000301,0x3833683c0014493,0x793b602d000,0x0,0x504e80000000000,0x58000000000000000000],#[0x481300007c3c40f,0x7068800,0x5b33000000000000000,0x7f09e000000003025000,0xa780b00001d0d0000204,0x680004145800048a511b,0x3c01a0000505b0881f94,0x4034800041c39124936,0x6000070640000184c800,0x306,0xa0000303080006b60000,0x109,0xf8000600480000000000,0x96010283b00000000193,0x304,0x391c000000000000000,0xa0000000000006334800,0xf700c800000000000106,0x38224149e80,0x23030000000000000000,0x59d,0x39470000000,0x68000000000002045800,0x900004954b15d8000584,0x702d8000520d496,0x38000000068598000000,0x1100006094a85,0xd3063800000000b3c000,0xb80000000000051a5016,0x5867000000002b5,0x588a206900001930800,0x0],#[0x48f4981c00000000000,0xf800061cc80000838800,0x50000488880000000614,0x509c000000001005301,0x185e8000000,0x90000000000000000000,0x4a6,0x88000000000000000000,0x136400007002c96,0x5073000000000000000,0x38000000000003075000,0x880003a72081ee840f93,0x7871d015f03bf85,0x98000000000000000000,0x7800008600000000028e,0x2931800078378000213,0x30262859000,0x3871000021010000000,0x0,0x0,0x0,0x58000000000000000000,0x21a4d03,0x8800,0x88000081d80006845000,0x40862a95380b8b0c9650,0x3a05141433054285f09c,0xd833882780000000580,0x2283f00006061682f2b5,0x38ba1006f06,0x0,0x0],#[0xf69406ae928ed8000000,0x406180000000381,0x34883bb5f80508000000,0x69c,0x68420000000,0x8138000000,0x3a538000000020c4000,0x21280000502e800,0x854c049d0120000000,0x1139000,0x329b7800030570000000,0x204,0xa800029389a089d0f000,0x300961c5605,0x820407844f805e825800,0x70b80000684,0xf80005a7180000000000,0x312d800000000000184,0x18000605d80000000000,0x40bc80000000004,0xf0000711b00000000000,0x695,0xc8809800000000000000,0x8800000650000306d531,0x80002836b8178000602,0x71662513786f99cc388,0x383fe86a8000000,0x0,0x702a8000000,0x593c00000901b944000,0x4a89ac81c80000000000,0xd520f000000b9583d12d],#[0xdf04d800030c7294bb08,0x386f380,0x828007065b01fa070000,0x320,0x106c00005b200000000,0x188200000000000,0xa98c1000000000000000,0x425e886ed1c]]
def g219D8 := limbs80 #[#[0xe54110fe4c110bbd8950,0xd8d10bf58d10fd54510f,0x9510bf59510bf19510bf,0x550fed4150bfd9510bf9,0x31bf58750fbd8950bfd8,0x1fd54531fd50531bfd81,0xbf19531bfd9131bf5913,0xfd9531bf99531bf59531,0x54d51fdd4551bfd8151b,0x8351bfd8d51dfd4d51df,0xd10bf58f51dfd4f51bf5,0x50ff4c550ff54d10ff50,0xff54750ff4c750ff545,0xff55131ff58131ff5875,0xf99531ff59531ffd5131,0x54d51ffd8151ff58151f,0x8d51ff58d51ffd4d51ff,0x2059037000ff58f51ffd,0x18615d1340fd0d40ab08,0x9727525a2312011df1af,0x73c539c35e3202f02c72,0x4f24c249245b4394103e,0x496125e25a456d544514,0xa79a76a7256e06b06876,0x90d8d689186182a8017c,0x85202100e2b263c3007,0x98e29017263821480a8e,0x238a245088e0c520281c,0x405c80c263822228e432,0x917263822228b931c18a,0x64c7844050c364c71480,0xb263c21898d931a1282],#[0x908948120c464c68628a,0x428122432c3243040794,0x101c36548306101c3652,0xe520384060400220488,0x21c122405081c30cc90e,0xc98e0a5202870d949081,0x3e4ca8e0899318122405,0x88f2c118664239482382,0x9013202c61a09418386c,0x485c846090ca8c6228e0,0x825223831480e8c4908a,0x14186444818a23431488,0x20c108d0c51e12446848,0xa2c48625223422229111,0x21045894a486c98d0888,0x91244242830082240489,0xb0121888485060224040,0x1c890838b01218443838,0x3829480a504e4c705290,0xc80c47262c0411c11f26,0x33262c1051930720c228,0xa44862c1911c11d21120,0x3223230480]]
set_option maxRecDepth 16000 in
def g219H8 := limbs80 #[#[0x5020403150000031,0x10100010120200000,0x10507010330003010000,0x10019001000400001,0x400211000004058100,0x33901100005148000000,0xc03c0000b03830,0x0,0x7451f06300,0xf35800,0xaa4c7008000000,0x6e000000000000000000,0x16950000316fa1,0x0,0x0,0x0,0x2e507100000000b07900,0xf27f8052a088000070,0x6100000000a06750aa00,0x6194717b91,0x0,0xd0000d1010000000000,0xc023e1,0x0,0x9b320d00000000000000,0x1700005449801be21830,0x39000000000000000073,0x5d000000000000000021,0x16,0x802ca056000000,0x21000000000000000000,0xac0000f19c0000000051],#[0xd0,0x68f00000000000000,0xd2a10000006e00,0x80830000f04600,0xe03700000000067000,0x8e000000000000000000,0xa21e000006,0x87000000000000000000,0xd3,0x99c072d11dc094000000,0xd000000000000000061,0x40,0xf0042090000000,0x0,0xb23e205a0000000000,0x26000000000000000000,0xa8602800000000000060,0x94,0x4f000000000000000000,0x64,0x0,0xe66300,0x0,0x0,0xd1ac6042d059000000,0x0,0x7f000000000000f35900,0xa6027cd3895423308950,0x80,0xe446000000,0x0,0x9667b0b30000615700],#[0x0,0x0,0xe11c0000015800,0xf0730000f08e00,0xc00c00,0x490164210b0000941600,0xe2220000644c000081,0x721ad19d0000000000,0x0,0xb07d000000,0x201400000000000000,0xd0ada17d0000f08a00,0x610ae27b00,0xc044f69600,0x3656f66e0000000000,0x0,0x54000000000000000000,0x6f901600000000000013,0x1781a43012419a666c34,0x81,0x290000000010af000000,0xf3,0x0,0x2100000000613a000000,0x904700000000c2,0x1a000000000000000000,0x60,0x205000000000000000,0xda4e00000000000000,0xd67900000000000000,0x613f0000000000,0x68b65ad0690000000000],#[0xb0b100000000000001,0x0,0x0,0x73820000607cc0a200,0x60a700,0xd05cf23c61a100,0x9898d05f000000,0x6f11a00000c195000000,0xa23a0000000092,0x0,0x236500,0x74000000000000000000,0x51,0x8000000000c03a000000,0xe3,0x4022b20ab10e000000,0x413e0000000000,0x907e840f000000,0x0,0x811b00000000000000,0x0,0x1f0000000000b5407b00,0x50360000d0,0xe6940000307600,0xb010704a621d00,0xb06d380d00,0x0,0x0,0xa000000000908c000000,0x117a0000506b000070,0x6f000000000000303500,0x0],#[0xd03000000000822400,0x202100,0x86b0050000b081000000,0x56,0x0,0x7b00000000960d000000,0x93,0x7010b4f0820000f04e00,0xe1,0x54000000000000000000,0x10530000000021,0x8100005287b007a0a300,0x817e00007235911992,0x50310000c669000000,0x9f000000000000325700,0x6a000000000000a19650,0xc2560000e0,0x2180020000904390b600,0x90000404c0000000073,0xa00600000000f06290,0x0,0xe04d6676000000,0x665c00000000000000,0x319700,0x704800000000000000,0x9c000000000000000000,0x60b800000000b0b710,0x0,0x510000f31d0000000000,0x4b22310000a68a0000ba,0x5550ae0000000000006a,0x92750000f173000060],#[0x5e000000000000e02d00,0xa6,0x90410000000000,0xb20c706600,0x3900000000809900,0xb17200000000000000,0xb06100002080000000,0x140c000000,0x0,0x2087e024000000,0x0,0x404b0000000000,0xc6924264000000,0xc00009a490000000000,0x91,0x0,0x0,0x47000000000000000000,0xe6,0x63419b00000000000000,0x5000000000000000b1,0xa6a69900004386000000,0x800000000000000000a1,0x62160000905716,0x0,0xc051000000,0xd6b43058000000,0x902b71887179416000,0x0,0x5e306400000000000000,0xe662c3810000000090,0x908500000000000000],#[0x813b0000389400,0x7171405b0000000000,0x70b9e00f10a800,0x0,0xa3270000000000,0x0,0x700a0000000000,0x2c81a20000aa4f000000,0x75000000000000000051,0x838400000000f0,0xd027000000,0xb01700,0x0,0x0,0x0,0x666600000078000000,0x60000080b2c44b000000,0x460000000000000000a0,0x2a,0x0,0x0,0x811e000000,0x0,0x516ba032701e00,0x466100,0x0,0x43000000000000206800,0xa0910000f09d42,0x0,0x0,0x631e000000,0x34000000000000000000],#[0xe0,0xe0950000000000,0x97b18300000000000000,0xa2000050a40000000040,0x62,0x609a000000,0x0,0x267500,0xe01c26570000000000,0xb000000000000000000,0x4e0000000000004150a0,0x40924113000084,0x18000013850000000000,0x409e0000000070,0x26000000000000000000,0x3f0000e0200000000091,0x20190000022a000030,0x0,0x8fd65b00000000000000,0xc64840,0x0,0x7a000000000000000000,0x81a70000869a014340,0x0,0x0,0x98000000000000000000,0x203d000000000000f1,0x0,0x60604a5000000,0x129e6025000000,0x0,0xd01d00000000232a00],#[0x47000000000000000000,0x61,0x6082639294506c505400,0x808436,0x6200000000b08b000000,0xfe29800000000000012,0x7a1668000000000000ca,0x211a66,0x61a3f02f0000e44000,0xf23d000000,0x90a100000000000000,0x0,0x8d000000000000000000,0xb0010000000080,0x5cd02a705d0000606500,0x15217c000000000000a1,0x5223000050980000d0,0xb00300,0x2d507460290000000000,0x300e0000b445000023,0x83609300000000828b00,0x32a30000f3,0x703e00000000000000,0x0,0x5125c22f0000000000,0x77000000000000000000,0xe0a5000020,0x4500000122e0ab000000,0x49808600000000007050,0x6b3000080,0x0,0x0],#[0xd32676980000000000,0xba00000000000000,0x13000000000000000000,0x1140000c096a29380,0x0,0xa900007418404f80b000,0xc040f03b70,0x811500]]
def g219D9 := limbs80 #[#[0xd51fe98ffd43faa1fd10,0x51aea71e150a803fea3f,0x1549238501462648d004,0x411040c19521648e1205,0x119239414069239]]
def g219H9 := limbs80 #[#[0x200028e40d3020e00780,0x563013cb41802a7da8b1,0x14aec1c70e3fe50113bc,0xc0d8104845507a008629,0x6f949485eb0c21a2120a,0x8f099c50501fc12560c4,0x7096d02201bda100128e,0xba41a303391a704e423,0x6c424c1c111fe6ae42ae,0xf02bc077c9a769019c51,0xe20805c42d108881820b,0x5a318006da22d8e76043,0x40829a6648a01cb0654,0xf0280002296d84523540,0x5c5530a3c2c0002d08,0x5cc0e728a409c480000e,0xac61c059a9fe42c000c6,0xd870002815a18c000d00,0x36b300b91768596111,0xf63ac6ed21c000641c0,0x24219150000f03c00,0x1524ea830e10003005,0x40031e68c000b22241f0,0x23cd2e100cc1bb2,0xc27c4364292283188a05,0x28110001]]
def g219D10 (j : Nat) := if j=0 then 0x20c2513f else 0
def g219H10 := limbs80 #[#[0xd8000236002c000048,0x993b1b02e08000000000,0xc48003,0xd1600000,0x4a000007850000000005,0x40f4a00000000150010f,0x415000001025c0000]]
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
  | 5 => lookupWord 1 17 0 7 1 2 g219H5
  | 6 => lookupWord 25 257 5 14 6 4 g219H6
  | 7 => lookupWord 111 1123 5 16 8 4 g219H7
  | 8 => lookupWord 98 1459 4 16 8 4 g219H8
  | 9 => lookupWord 28 131 7 14 6 4 g219H9
  | 10 => lookupWord 4 53 2 11 3 4 g219H10
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
theorem g219G : graphValid g219 (boundsBefore K183) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low219 : Lower true (varsX 219) (graphGoal 219) 11 := lower_forest (g:=g219) (i:=0) (hints:=16842819) (before_sound K183 V183) g219G g219T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K219 := extendKnown K183 11 [(219,[]),(243,[83])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V219 : Known true K219 := extend_ok (m:=219) V183 low219 (by decide +kernel)
def g231Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3ffe001fff01ffffc,0xdf89c505600001f0001f])),(BitVec.ofNat 152 (word80 [0x588544d444a344a450,0xdf89810465294a5294a5]))),((BitVec.ofNat 152 (word80 [0xfffffffe00001ffe01,0x98b571b240003e007c00])),(BitVec.ofNat 152 (word80 [0x9029809816c580c899,0x989560b24318c6318c63]))),((BitVec.ofNat 152 (word80 [0x3ffffffffffe00002,0x54da2874c007c00f83e0])),(BitVec.ofNat 152 (word80 [0xe00e00e0070600f0e0,0x549a0830c10842108421]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x3fffffffffffffffe,0xa08ef66320f8000003ff])),(BitVec.ofNat 152 (word80 [0x13009009800090002,0x200476430a5294a5294a]))),((BitVec.ofNat 152 (word80 [0xfc0000000000000002,0x4970938fdf00000ffc00])),(BitVec.ofNat 152 (word80 [0x1c00e00e0080e0102,0x160930d0c6318c6318c]))),((BitVec.ofNat 152 (word80 [1,0x37050a181ffffff00000])),(BitVec.ofNat 152 (word80 [0x20010010000100000,0x108421084210]))),(0x0,0x0)]
def g231C : List ColumnInfo := [(4,0,227,0,8),(1,0,230,0,7),(2,0,229,0,7),(32,0,199,0,6),(64,0,167,0,6),(3,0,228,0,5),(33,0,198,0,5),(34,0,197,0,5),(36,0,195,0,5),(65,0,166,0,5),(66,0,165,0,5),(128,0,103,0,5),(35,0,196,0,4),(37,0,194,0,4),(67,0,164,0,4),(129,0,102,0,4),(130,0,101,0,4)]
def g231A : List (List Nat) := [[],[16,101]]
def g231D4 := limbs80 #[#[0x32a8798b746087054d43,0x80dc96550f1c302c02e4,0x73c930db8aa921e38e07,0x2a74e39159172181538,0xf624c3021d730b22e43]]
def g231D5 := limbs80 #[#[0x5d9544c3965915354130,0x4c23de0576551308fb80,0xe0176d51308ef825d954,0x503308f7815d2654c23e,0x9f3815d350cc27660e75,0xdc154cc27660f7055330,0xcc23de057655330cb964,0xe0574997308ef825d954,0xd4d40f195350d505023d,0xa9f8654d43d023de0576,0xdc153d033658f7054f40,0xd03275d163d4f409b984,0xe055458f40a5f8558f53,0x58f40ad9801d563d03a5,0xacd821d563d02b560475,0x9d563d02b6e017558f40,0x5427ce0574d4150c5f75,0x54f7050f508f7815d363,0x50f50cd963dc143d4356,0x97985dc143d432e59370,0x5d943d423de057650f50,0x50f0fd977454d438ef82,0x6086554d43a798019553,0x54d438ef825d95350e9b,0xd9b741c15350ef260870,0x1955350f361db7054d43,0x50ed36086554d43b5980,0xe1d6519543c6d655c865,0x59543ce9805c86550e1f,0xceb721c16550f3cdc470,0xdc16550f3cdc77059543,0x50f3a2037259543ceb72],#[0xdd37359543ceb80dc965,0x58643ed38054d6190f27,0x8f586dc55490eb560f54,0x5516014f36e1d5358053,0x14fb4e015358453af381,0xe0153588538f78755161,0x54c53ae7815516214fb2,0xcdb76dc15314fa659370,0x5c86054f36e037654c53,0x54f3ad917218153ce964,0xe096418153af38159060,0xd81538fb875906054eba,0xaeb825936054ebce0564,0x5d36054e3de0574d8153,0x54ebce0554d81538ef82,0x60c74d8153e3b5495360,0xd8153cb9741d36054eb6,0xaeb825d36054ebce0574,0x5906454e75e0574d4d53,0x94e75e0574d4e538bf87,0xe0176d4e53b57815d353,0x3c00ae5821c564d4f96,0xfc390cc2d09c2106c15,0x1e0721b06615c5112c45,0x2a0a2270962408a2107e,0x360d2330c6300ba2d0ae,0x4450b414f63c0ea390de,0x5053b4d52f4a52347517,0x5c56b5955f5655353547,0x6859b6558f625835f577,0x7b1e6781da751ce721b9,0x872168420a811fe7e1f2],#[0x2418d22e8a222,0x1020800000000000,0x0,0x90400000000000,0x0,0xe2300400000000000000,0x6182]]
def g231H5 := limbs80 #[#[0x4011806a000000003c00,0x7c62000007]]
set_option maxRecDepth 16000 in
def g231D6 := limbs80 #[#[0x27db82ca987595354130,0xbb2e7a8661d654f50cc,0x27bb8acaa067965d433,0x439eee2b26a1a755163d,0x50e76b90caa1cf970195,0x6439dee4b2a873edc165,0x114f6ca9ac029ed55358,0x4c53d9aa6b10a7b554d6,0x6054e6fbb2a629e9d645,0x59353cbaeda9ca77a5c8,0xd504c3f8a8aa0884f771,0x54d30df2c8a8261f654,0xc5544c36eb22a6987db7,0x7655130d7ac8aa2617dd,0x5c3544c27fbb2a8984fd,0xd76d5130bbae7aa2617e,0xfdd5644c37db82c8984f,0xff7459530df6e0b2a613,0xf654d40cc27eba4ca984,0x6f96550330f72a8a0661,0x1f654f50cc2fd3aa8198,0x85f974d4330fb2e7a866,0x61be5db50cc37cb2ea19,0x986dd6454f30fb6e0a9e,0x6617ddc554cc2fdb82a9,0x9984fd7655330d7ac8aa,0xa661775cf54cc27fbb2a,0xcb984ff75593309faeda,0x32e613fdd165cc37db82,0xaa0a07b943541409fae9,0x8a8281ded4d50503bca9,0x9a86a07bb7050d40f72a],#[0xeaa1a81af59543503cea,0xb82a6a05bf7550d40b7a,0x2e1a9a813fdd953502fd,0xebb6a6a05bd74d4d40bf,0x6ee2aa281eedc1545027,0x7db82caa05bf7355140f,0x9fee6b2a81bddc565503,0x3cea9a87a04fd7399540,0xb7aeaa1e81af59543d0,0x2fdb82a7a05bf7550f4,0x409faeca9e81b758d53d,0xd036eb1ea7a04ff7654f,0xf409faeda9e816f5d353,0x3d027fbaac7a06bd5458,0x8f40dbaeab1e81b71d56,0x54d036fbaac7a06de755,0x59740b7ee6aa681eddc5,0xf505427eb9ccba04ff73,0x4d4150bf2e7a82a1de54,0x8d43543aea9a86a85f97,0x7054d509feeca1aa1b7d,0x5d363543bdb82a6a85fb,0x77155150bf6e0aa2a13f,0xf5cf64542fbb8ac8a85f,0x5d5350f50bf6e0a1ea13,0xaf59143d436eb1a87a87,0x4ff7650f509faeca1ea1,0x1bedc163d43bdb82a7a8,0x85f771553509fee8b1ea,0xa1bddc564d42fbb8ac9a,0xa1edd53d81439fee6b26,0xa873f5d76050f5eaa6c0],#[0x6a1dbf7454d43bf6e0a9,0x9a879fd955350f3e32aa,0xa6a1fd87054d439faeca,0xa9a8777dc55350fedb82,0x2a6a1f9e5454d43f3aa8,0xaa9a87e7dd15350fce3a,0xb2a6a1f5f6554d43eb8c,0xeb29a87e79525350f6e3,0xba6a6a1dde7694d43bba,0x2e032a879fd975350ede,0xeb28caa1ded7219543bf,0xf6e0b2a873f9d86550f3,0x3fb2acaa1def7259543b,0xdf6e0b2a87be1c16550f,0xf77b92caa1cff7059543,0x39fee6b2a87b7dcd6550,0xe7eb9ccaa1e7f659954,0x43deaa8b0c873f5c3655,0x90fedb82a721ef754586,0x243beee2aa487b7dd953,0x490f3eb2aa921ddf7355,0x5243bbae7aa4879f9955,0x6014f7caa2c029e7d65d,0x58453deaa8b08a7be951,0x16214f76aa2c429ef654,0x454c53fb6e0a98a7bb95,0xc55414f6fbb2a629edd6,0x64950539feecaa0a77dd,0x5906054e7ebb4a829ebd,0xa7618153df6c8302a7be,0xed876054f7cb0ec0a9df,0xfb63d8153fb6a7b02a7b],#[0xbe1936054fedb9ec0a9e,0xefa64d8153df2c9b02a7,0x73f5d36054f7db26c0a9,0x9efb71d8153df2e3b02a,0xa7be5536054f7db9ec0a,0xa9efb54d8153df4a9b02,0x2a7be5d36054f7c3a6c0,0x2a9efb74d8153df4e9b0,0x9aa73f5d36154efdb82c,0xa8a9ddf7355153bbae9a,0x2a2a7cfd525454eeeb9c,0x2c8a9ebd6419153d7ec9,0x4b22a77ddc56454efdb8,0x24c8a9df97099153bdee,0xe3b22a73f5c36454f5fb,0xba6a729f5e54d4e539fa,0xce9a9ca7d75d35394eee,0xbb8ac9a9ddd7395253eb,0xe8e2b26a73fdc164d4ef,0x7fb8ac9a9ef77159353d,0x101d81801280b0078002,0x83c03a83703182c02682,0x6685d05785204c847041,0x508187c07887506f86c0,0x89809489108f88a08688,0xaa8a70a38a209e89d099,0xf0bb8ba0b68b30b18b00,0x8d40ce8cd0cb8c80c28b,0xe68e50e18e00de8db0d9,0xf0fb8f80f48f10ed8ea0,0x91210e90d1099081048f,0x2a92712191e11a919115],#[0xd13993813493112d92c1,0x95415094f14b94614293,0x6c96b169966162959155,0x317f97e17897316f96e1,0x99a19699318d98a18698,0xb09a91a59a21a099d19b,0x71c39c01be9bb1b79b61,0x9d81d69d51d19ce1ca9c,0xf29ef1eb9e81e09dd1db,0x9205a04202a011ff9fa1,0xa2021ea1b217a1220ca0,0x32a2d229a28226a25223,0x7243a42240a3d239a382,0xa5c258a55251a4c248a4,0x74a7126da6a264a6325f,0x9285a84282a7f27ba782,0xaa62a2a9d299a98292a8,0xbcabb2b5ab22aeaad2a9,0x32cface2ccac72c5ac42,0xae42e2add2d9ad82d6ad,0xf6af32efaec2eaae92e5,0x7305b02300aff2fbafa2,0xb1a316b1330fb0c30ab0,0xe00c0f27b24322b1f31d,0x83f8020f06e00f8010b,0xb078020ae00b80106e0,0x6e0080e004403c2e00b,0xe0081820206e0081b802,0x8020f090c0d101b80206,0x82c10b0408042e0041b,0x400200082c1002410341,0x81001810018100041030],#[0x4106040001004209040,0x81043d042810418102,0x10400200080e8820,0x10904241230408101041,0x41034209041410424,0x4100081010410100101,0x504100002043c2420107,0x4104810a0c100041030,0x101000c100101030108,0x4105041046260061,0x41002d0c20b430804100,0x2042d042830410104050,0xc1014104001040003c10,0x10418100080020342c10,0x21040410207041c10404,0x4003000400004002841,0x8a842c30404841090408,0x20b0424100000004a109,0x4003048810321081084,0x80205e0080010000000b,0x10004100000040010007,0x610103048414403081c,0x588104040c8420000103,0xb058810b048810b0,0xc0828442c1c010181,0x14160050c16260080c1,0x89803010c84243050c10,0x20418100002000800025,0x8410006260090c10006,0x4100101c107041000400,0xc10b0400304021040008,0x400304003042c162040],#[0x2]]
def g231H6 := limbs80 #[#[0x80340802050c0208040,0x2000e2471c1042070402,0x21000000000000b1174,0x5a8833000000b17000,0x2230000003b10,0x53900000000000000000,0x43000020000000008,0xe000e0c0000000,0xf5000071a2b300000,0x563c000000000f19000,0x461bd44000000000e407,0xc13c1451205,0x22c3a000000000000000,0x9b204bcae8,0x55500000000000000,0x132000000000a01000,0x8a4c4aa510000000,0x0,0x2eaad00000012623f000,0x50f0000000000007,0x60935300000013000,0x63d000000152f2a,0x42f0000000000000000,0x32944100000000000,0x116e31000,0xb024180000,0x22b00,0xd15000000,0xf000000000135c0d51e0,0xf8193b00000000024dea,0x432dda2000000000000,0x440a5aa336137b1dd0bf],#[0x400b46788000000000a3,0x384827a48,0x43e000000b380,0x749b2800000000,0x45c2584700000000064e,0x51f000c070000009,0x803d0634fe1082c00000,0x14c]]
set_option maxRecDepth 16000 in
def g231D7 := limbs80 #[#[0xd58643b798f40b758f40,0x58453be58053e7d0e43b,0x9053af59053bb58853bd,0x110d7d4e53bed8153af9,0x30bf99510bf59510fe54,0xbf59130f754d30fe541,0xfe50330bf99530bf5953,0xf59330f754f30fed4330,0x54140bf99730bf59730b,0x9540ef55140ef50d40fe,0xf40ef50f40bf99540bf5,0x40bf59740ef55340bf58,0xbfd8550fed4150bf997,0xbfd8d50dfd4d50df54d5,0xf54f50bf58750bfd9150,0x59350bf58f50dfd4f50d,0x8143bf99443bf59443bf,0x543f794d43f754d43bfd,0x43bf99543bf59543bf19,0x3bf59243f754e43bfd95,0xf754c53bf99643bf5964,0xe18153bf99453bf59053,0xd8553bfd8153fed8153f,0x4e53bfd9153f7d4d53bf,0x353bf59653bf59253f7d,0x30bf59353bf58753bf58,0xff55330ffd5130ff551,0xffd4d40ff54d40ffd533,0xf54550ffd4f40ff54f40,0x54d50ff50d50ff58550f,0x9150ff55150ff58d50ff,0xf50ff54f50ff50f50ff5],#[0x43ff59350ff55350ff58,0x3ff54d43ffd8143ff581,0xff59543ff19543ffd4d4,0xf55243ffd9543ff99543,0x95053ff55053ffd5243f,0x8553ffd8153ff58153ff,0x153ffd4d53ffd8553ff5,0x53ffd5153ff95153ff55,0x3ff99153ff59153ff191,0xffd5253ff95253ffd915,0x1b000ff99353ff59353,0x90e70c50a308105f03d,0x1d51b318a16814612b1,0x2a728c27124f22d20b1f,0x8e37335833630d2eb2c9,0xc45343140f3ed3d23b03,0x53a5184f64db4c049e47,0x1a5f85d65b459257755c,0xb7026e76cc69566c63c6,0x8137ea7c879f77d75472,0x18d88b689b88085e83c,0x69db9b299096e9459239,0xa98a7da62a4ea33a119f,0x55b33b1fb0bae9aceab3,0x4bf0bd5bbaba6b92b70b,0xcb4ca7c85c55c3ac18c0,0x94d79d65d3cd13cf1ccf,0x5e21e0ddf2dd0dbcda8d,0xec2ea7e9ae86e6be57e3,0x80309042600e241c0283,0xb0f803081c2600c2440f,0xc20b0e184082c3e00c20],#[0xc7c018709803082c3e00,0x1478ec0304161f006110,0x6063b00b182101e3b00c,0x82c4e01820bc03031f80,0x63861300c1620f098060,0x883f0410e201c11c3c02,0x1c58a130410e20bc0243,0x12303463f00e10241c0,0xc2c41e0f00e105e01c1e,0xbc028309805060c1e01,0x162838380509047e0142,0xe12181c0404070700a,0xc107e01818fc03031e33,0x80c1018ec03c4083f00,0xc105e00c18bc03031d8,0x1300610583c038416130,0x6162700c10384c01840e,0x587c0185c42d0830980,0x38032004104078078e1,0x28202101e0148601e182,0x82c207c018516103e00c,0x84081f006162840f8030,0x16284161f00614587c01,0x1e010789c0304081c360,0xf1026018184c0303c486,0x5880808b07805200f00,0xf8030a103600e2070d8,0x26020304098078c10584,0x60c2220c18104105e014,0x85890618444041882c48,0x307042062c3090c1890,0x88407850e0901e18b0c1],#[0x1e20f0c10f0c10407047,0x203170441e8848611141,0x4862d1090c5860858608,0x1080c4068420c2421688,0xd121401018c0c5840c5a,0xb080c31608b44850082,0x802c2161018812122062,0x3042c242830050909141,0x21630220302160d0863c,0x5042030d141080c4820c,0x210444850080c4850458,0x618b0420308584061a11,0xb042221]]
def g231H7 := limbs80 #[#[0x181040400d0010180,0x4010208009010e000120,0x9104041870f000828310,0x40012041000050000200,0xa049c1800a2e98b14e0,0xc181411a5c7408b0d08c,0xb4bf066318301123808,0x1ba0001ada56619b000,0x446dca4bdb5800000000,0x19012175b025e1c08d5b,0x4de3da000438045a86e5,0x5338adc0016c30000001,0x86087e51f,0xb08532b79a6a34000000,0x3c000e5e9536a54bb26a,0x4e3156b8c5d6e0403ad2,0x874f4a000f9978f00006,0xa6dc3c39e4637237304a,0x1e8a2a190cc000,0x544185b00001d579b000,0x22c8088a9d2a15d2b77,0x4000cd3412e90348b00,0xce18ec0a7a4,0x8a484d6731df00018400,0x2cfa000648eab0,0x11772760006a4f579c98,0x5b3c000f81b3d800,0x835600000001b2800000,0xd4f800150800083f1e,0x94469a0000003ea80,0xec700029680000005988,0x208273c3bbc264a48001],#[0xf63657de8f1c40001c8,0x1ad2b5e000000000000,0x72ad792118440016de00,0x18be18000f1d71b0002c,0x96b2278e7186dcb6e3bc,0x299665cf518003,0x8001ad400062a4000488,0x61e800296227a00062a,0x280d60bf2f26b6400000,0x54411398603400070a08,0x1c60a82000197c000a,0x603b39696007d0baf288,0x698b97260170f31a280c,0x989b4434422688e12000,0x2fa01d1cc730000b3bd4,0x280c2302a23400079112,0x9b0d3102d0a51c216b09,0xc956ae360f9f26410cdd,0xc6ec10e8a1c9638d720f,0x7b2df8ce509e5ecfe64f,0x3e0e103c5b0000d38605,0x648174a0000089237b2b,0x7400060a0cd226300042,0x36d0fcc0d0be8bcc46a,0x648519a801ec80007,0x3d4c00125da53d3b5492,0x1e60a7643429c8a57d4e,0x56174d498f0004066ae,0xd3562aca800000142100,0x6fd2f618800000000031,0xfd0cd282b0000000000d,0x9233c7b0740007084d36],#[0x14574c500000000006d5,0x605f704d8ef4e5000000,0x1120000005e7cd19c2,0x1cd16000145c0007c980,0x7e00e000742911fcc81,0x6713148000001c0862ad,0xc2e25a22a80006838ad6,0x1a5300005bef562db573,0x3992459932800000]]
def g231D8 := limbs80 #[#[0xf40fea07fcc3fa61fd10,0x87fd43fe21ffd43faa1f,0x3fea7fe53fea9ff14ffc,0x3a998a8421989c300c00,0x3033a0303cc5eab92c84,0xa10680e0c90601c4260,0x3a030504f3a03051818,0x18528980c10712018405,0x410204b1e01870841e0,0x43e03051078061011203,0x40]]
def g231H8 := limbs80 #[#[0x60a0a2802288001,0x399800000002280002,0x1ba78f0000001370,0x2d600000,0xb8000000000000000,0x0,0x3d040000000,0x2900002d4400,0xc94000000000000,0x40000000000000034740,0x7c1675f98000000001c4,0x3c3c000000000003,0x0,0x28cc00,0x2edb80000029899541d4,0x16,0x296400,0x2460000000000,0x0,0x245800000000,0x19c8000003940000,0x0,0x1a092e9e000000000000,0x2c43,0x2d780,0x2878002e4000,0xe9048000000000002f78,0x1ca40000000024,0x34d7c3af6400000,0xc2c0001cc003590000,0x0,0x0],#[0x0,0x0,0x1dd000000000000,0x50000000000000000000,0x20,0xf3400000,0x0,0x1d0c00288c0,0x1db08f755000000,0x30b8000000000000984,0x2c57e8000287014c0000,0x8f800000000000000000,0xfc00180c000000000001,0x8,0x908001cb400000000000,0x0,0xc0000000000011280000,0x253c0027d,0x1b30000000,0x28c000000000205c0000,0x0,0x340000015184e697c000,0x25e5cd15839,0x1d8c00000000,0x0,0x8040000,0x3d7000000000000,0x0,0x0,0x31c112400000000000,0x313b07c000,0x8b00000000000000000],#[0x1e6c00000000,0x3a70000000000000000,0x0,0x206a2c800,0x7b94bc8209c000000000,0x2d21a,0x242400000000000,0x21c4,0x0,0x42800000000000,0x22c0000000,0x237c0000,0x0,0x0,0x30d80000000,0x13319400111,0x30e0,0x3c20003c300000000,0x95c000000001b5c00,0x1fc40000020dc000,0x0,0x0,0x30c4000,0x0,0xc14fa000000000001800,0x30ac000001d5b,0x3a680000000000000,0x0,0x2008000000000000,0x39d88bf8a00000000000,0x1d14000002d9cc0000,0x0],#[0x29bc0000000000,0x3f8400000000,0x0,0x1db40,0x8100000000009ac81c00,0x1174003,0x487dabca8001ac40000,0x1f2e9dc00,0xec001834000000000000,0x18,0x35a400,0x44c000000000000000,0x96b7500000000,0x46c00000000000000000,0x3,0xc640,0x0,0x3c98000000000000,0x14900000,0x351c000000f9c00000,0x2b2a488000000,0x0,0x3d6c0000038c800000]]
def g231D9 (j : Nat) := if j=0 then 0x8200ff else 0
def g231H9 := limbs80 #[#[0x50008c00000000000204,0xcad080000004f0012c7,0x1d1000030a0000000000,0x2b20019800003d000000,0x382003200000001900,0xa0002503b6d,0x895b58c00008a000016d,0x71c56000000000]]
def g231L : Nat → Packing
  | 4 => (6,5,5,0,0,5,0,g231D4)
  | 5 => (86,4,5,0,0,10,0,g231D5)
  | 6 => (238,3,5,0,0,12,0,g231D6)
  | 7 => (122,2,5,0,0,12,0,g231D7)
  | 8 => (14,1,5,0,0,9,0,g231D8)
  | 9 => (1,0,5,0,0,0,0,g231D9)
  | _ => emptyPacking
def g231I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 17 0 7 3 0 g231H5
  | 6 => lookupWord 24 251 5 12 7 1 g231H6
  | 7 => lookupWord 74 409 7 13 8 1 g231H7
  | 8 => lookupWord 38 787 3 12 7 1 g231H8
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
theorem g231P5_0 : block g231 5 0 86=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g231B5 : block g231 5 0 86=true := g231P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231P6_0 : block g231 6 0 21=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231P6_21 : block g231 6 21 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231P6_117 : block g231 6 117 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231P6_213 : block g231 6 213 25=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g231B6 : block g231 6 0 238=true := (@block_merge g231 6 0 117 121 (@block_merge g231 6 0 21 96 g231P6_0 g231P6_21) (@block_merge g231 6 117 96 25 g231P6_117 g231P6_213))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231P7_0 : block g231 7 0 11=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231P7_11 : block g231 7 11 63=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231P7_74 : block g231 7 74 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g231B7 : block g231 7 0 122=true := (@block_merge g231 7 0 11 111 g231P7_0 (@block_merge g231 7 11 63 48 g231P7_11 g231P7_74))
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
def K231 := extendKnown K219 10 [(231,[]),(237,[48,97,82,16,32]),(245,[65,49])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V231 : Known true K231 := extend_ok (m:=231) V219 low231 (by decide +kernel)
def g246Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0xff801ffffe1fff9ae2,0x181cf000000fc003f03f])),(BitVec.ofNat 152 (word80 [0x450940500441101ac2,0x800f145145145145145]))),((BitVec.ofNat 152 (word80 [0xffffe007fffff8390b,0xb483500003f000fc0fc0])),(BitVec.ofNat 152 (word80 [0x160181602800213803,0xb40140c30c30c30c30c3]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffff8001fffd03d,0x39712000fc003f00003f])),(BitVec.ofNat 152 (word80 [0x98020180b082400039,0x3171028a28a28a28a28a]))),((BitVec.ofNat 152 (word80 [0xffffffffffe000462a,0x8bc7903f000000000fc0])),(BitVec.ofNat 152 (word80 [0xe02c0a02c00b824628,0xbc6971c71c71c71c71c]))),((BitVec.ofNat 152 (word80 [0x4984,0x67ac8fc000003ffff000])),(BitVec.ofNat 152 (word80 [0x300c03010c044104,0x428c0410410410410410]))),((BitVec.ofNat 152 (word80 [0x2651,0x42404fffffffc0000000])),(BitVec.ofNat 152 (word80 [0x4010040010000000,0x820820820820820]))),(0x0,0x0)]
def g246C : List ColumnInfo := [(4,0,242,0,8),(32,0,214,0,8),(64,0,182,0,8),(2,0,244,0,7),(16,0,230,0,7),(128,0,118,0,7),(18,0,228,0,5),(130,0,116,0,4),(144,0,102,0,4)]
def g246A : List (List Nat) := [[],[65]]
def g246D6 := limbs80 #[#[0xe3c1243e437695254120,0x5]]
def g246D7 := limbs80 #[#[0xf54950bf59520fe54120,0x42a00ff58950bfd8950d,0xc32187c70572186ae8a5,0x481c5c705328c82071b1,0x81c60d4c70c871]]
def g246H7 (j : Nat) := if j=0 then 0x20 else 0
def g246D8 := limbs80 #[#[0xa38c2461a403faa1fd20,0x1e851c6121c]]
def g246H8 := limbs80 #[#[0xf2d8230000000000d1,0x80000000000004]]
def g246D9 (j : Nat) := if j=0 then 0x5431021bf else 0
def g246H9 (j : Nat) := if j=0 then 0x9ec8 else 0
def g246L : Nat → Packing
  | 6 => (1,3,4,0,0,0,0,g246D6)
  | 7 => (5,2,4,0,0,8,0,g246D7)
  | 8 => (2,1,4,0,0,6,0,g246D8)
  | 9 => (1,0,4,0,0,0,0,g246D9)
  | _ => emptyPacking
def g246I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 1 2 0 4 0 0 g246H7
  | 8 => lookupWord 1 17 0 8 3 1 g246H8
  | 9 => lookupWord 1 3 0 6 1 1 g246H9
  | _ => fun _ => none
def g246 : Forest := ⟨246,9,fun i => g246Y[i]?.getD (0,0),g246C,g246A,g246L,g246I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246P6_0 : block g246 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g246B6 : block g246 6 0 1=true := g246P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246P7_0 : block g246 7 0 4=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246P7_4 : block g246 7 4 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g246B7 : block g246 7 0 5=true := (@block_merge g246 7 0 4 1 g246P7_0 g246P7_4)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246P8_0 : block g246 8 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g246B8 : block g246 8 0 2=true := g246P8_0
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
  · exact (rfl : block g246 5 0 0 = true)
  · exact g246B6
  · exact g246B7
  · exact g246B8
  · exact g246B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246G : graphValid g246 (boundsBefore K231) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low246 : Lower true (varsX 246) (graphGoal 246) 10 := lower_forest (g:=g246) (i:=0) (hints:=287376704) (before_sound K231 V231) g246G g246T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K246 := extendKnown K231 10 [(246,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V246 : Known true K246 := extend_ok (m:=246) V231 low246 (by decide +kernel)
def g127Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xf9a5a000db32e0d7d4,0x62eb6200000000ff00ff])),(BitVec.ofNat 152 (word80 [0xa0a50000d922a05554,0x420a6045454545454545]))),((BitVec.ofNat 152 (word80 [0x6ccc7fd8618016456,0x1b04730000ff0000ff00])),(BitVec.ofNat 152 (word80 [0x308cc7ec0218010456,0x3044313131313131313]))),((BitVec.ofNat 152 (word80 [0x19f1f444d849bdc21,0x17120e00ff00ff000000])),(BitVec.ofNat 152 (word80 [0xc18d1d044d8089d421,0x13100a0f0f0f0f0f0f0f]))),((BitVec.ofNat 152 (word80 [0xfd7879c0423a1cbac8,0xb7d492000000000000ff])),(BitVec.ofNat 152 (word80 [0x55879c002181caa88,0xb5d492bababababababa]))),((BitVec.ofNat 152 (word80 [0x4132c9a746184c519,0xb91db9ff00000000ff00])),(BitVec.ofNat 152 (word80 [0x4132812546080c009,0xb819382c2c2c2c2c2c2c]))),((BitVec.ofNat 152 (word80 [0x49a926913c9e72a08,0x6cb54c000000ffff0000])),(BitVec.ofNat 152 (word80 [0x41282690249462a08,0x2ca504b0b0b0b0b0b0b0]))),((BitVec.ofNat 152 (word80 [0x2654927a84d3e2baf,0x802a80ffffff00000000])),(BitVec.ofNat 152 (word80 [0x2600001a005362b80,0x2280c0c0c0c0c0c0c0]))),(0x0,0x0),(0x0,0x0)]
def g127C : List ColumnInfo := [(0,8,118,1,8),(8,0,119,0,8),(0,1,86,40,7),(1,0,118,0,7),(2,0,125,0,7),(4,0,123,0,7),(16,0,111,0,7),(32,0,95,0,7),(0,2,45,80,6),(0,16,45,66,6),(0,32,82,5,6),(8,32,82,5,6),(64,0,63,0,6),(2,16,45,64,5),(18,0,109,0,5),(64,2,45,16,5),(64,16,45,2,5),(66,16,45,0,4)]
def g127A : List (List Nat) := [[],[65]]
def g127D7 := limbs80 #[#[0x802a02feb96c36fdd161,0xc3]]
def g127D8 := limbs80 #[#[0x62ffd87fd61ff507fd21,0x58e44e1c89000ffd8bfd,0x18a18336712286014f2e,0xc612180844624486020e,0x52ca1c61430a13448082,0x14c3071840c2850acf80,0x2481840eb9e2860]]
def g127H8 (j : Nat) := if j=0 then 0x7740 else 0
def g127D9 (j : Nat) := if j=0 then 0x2b398a410c04ff else 0
def g127H9 := limbs80 #[#[0x228a,0xa100130000000030c8,0x2bb4a5]]
def g127L : Nat → Packing
  | 7 => (2,2,5,0,0,5,0,g127D7)
  | 8 => (6,1,5,0,0,9,0,g127D8)
  | 9 => (1,0,5,0,0,0,0,g127D9)
  | _ => emptyPacking
def g127I : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 1 3 0 5 1 0 g127H8
  | 9 => lookupWord 2 23 0 8 3 1 g127H9
  | _ => fun _ => none
def g127 : Forest := ⟨127,9,fun i => g127Y[i]?.getD (0,0),g127C,g127A,g127L,g127I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_0 : block g127 7 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_1 : block g127 7 1 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B7 : block g127 7 0 2=true := (@block_merge g127 7 0 1 1 g127P7_0 g127P7_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_0 : block g127 8 0 6=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B8 : block g127 8 0 6=true := g127P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P9_0 : block g127 9 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B9 : block g127 9 0 1=true := g127P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127T : checkedTables g127 9 := by
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
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127G : graphValid g127 (boundsBefore K246) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low127 : Lower true (varsX 127) (graphGoal 127) 10 := lower_forest (g:=g127) (i:=0) (hints:=16844099) (before_sound K246 V246) g127G g127T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K127 := extendKnown K246 10 [(127,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V127 : Known true K127 := extend_ok (m:=127) V246 low127 (by decide +kernel)
def g191Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfe6062606e60f5e792,0xa68000000007f01fc07f])),(BitVec.ofNat 152 (word80 [0x282002406460b46692,0x8282850a142850a14285]))),((BitVec.ofNat 152 (word80 [0x1aa5f1b12985e7734,0x240000003f800003f80])),(BitVec.ofNat 152 (word80 [0xccaa5f180288567334,0x4993264c993264c993]))),((BitVec.ofNat 152 (word80 [0x7f83886cb68a3d55,0x91000001fc000fe00000])),(BitVec.ofNat 152 (word80 [0x707b02886cb68a3d51,0x80078f1e3c78f1e3c78f]))),((BitVec.ofNat 152 (word80 [0xff4f37e5aba9780940,0x344000fe00000000007f])),(BitVec.ofNat 152 (word80 [0x814f35a58b89480940,0x345d3a74e9d3a74e9d3a]))),((BitVec.ofNat 152 (word80 [0x114bcc759f40b0e3a,0x8e007f00000000003f80])),(BitVec.ofNat 152 (word80 [0x114a0c75974090c0a,0x8e162c58b162c58b162c]))),((BitVec.ofNat 152 (word80 [0x126c53057070598ee,0x557f800000000fffc000])),(BitVec.ofNat 152 (word80 [0x104c530130101802c,0x55583060c183060c1830]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x99009c8149806009,0xc8fffffffffff0000000])),0x204081020408102040),(0x0,0x0)]
def g191C : List ColumnInfo := [(1,0,190,0,9),(2,0,189,0,9),(4,0,187,0,9),(8,0,183,0,9),(16,0,175,0,9),(32,0,159,0,9)]
def g191A : List (List Nat) := [[],[65],[80,50],[80,65,50]]
def g191D10 (j : Nat) := if j=0 then 0x468d037f else 0
def g191L : Nat → Packing
  | 10 => (1,0,3,0,0,0,0,g191D10)
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
theorem low191 : Lower true (varsX 191) (graphGoal 191) 11 := lower_forest (g:=g191) (i:=0) (hints:=66883) (before_sound K127 V127) g191G g191T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K191 := extendKnown K127 11 [(191,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V191 : Known true K191 := extend_ok (m:=191) V127 low191 (by decide +kernel)
def g223Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xf9a680583cdcb8eff0,0x3f80000007f])),(BitVec.ofNat 152 (word80 [0xa0a6805828dc18cef0,0x54a952a54a952a54a95]))),((BitVec.ofNat 152 (word80 [0x997f4100a84dfb3c,0x1fc00001fff80])),(BitVec.ofNat 152 (word80 [0x30984f4000280c733c,0xc183060c183060c183]))),((BitVec.ofNat 152 (word80 [0x780d966b86d07a456,0x200000fe00000fe00000])),(BitVec.ofNat 152 (word80 [0xc780d946b86d07a414,0x23c78f1e3c78f1e3c78f]))),((BitVec.ofNat 152 (word80 [0xfd4963faf542bb210c,0x7f0000000000007f])),(BitVec.ofNat 152 (word80 [0x54963a2d502a3210c,0xa952a54a952a54a952a]))),((BitVec.ofNat 152 (word80 [0x46156951a5f27c881,0x403f80000007f0003f80])),(BitVec.ofNat 152 (word80 [0x46110151a47238880,0x43060c183060c183060c]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x482a8ae46964012cf,0xbfc000000007ffffc000])),(BitVec.ofNat 152 (word80 [0x220a84490400043,0x8c183060c183060c1830]))),((BitVec.ofNat 152 (word80 [0x27e0100c921020430,0xdffffffffff800000000])),0x10204081020408102040),(0x0,0x0)]
def g223C : List ColumnInfo := [(4,0,219,0,11)]
def g223A : List (List Nat) := [[],[65],[48],[48,65]]
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
theorem low223 : Lower true (varsX 223) (graphGoal 223) 12 := lower_forest (g:=g223) (i:=0) (hints:=16844355) (before_sound K191 V191) g223G g223T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K223 := extendKnown K191 12 [(223,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V223 : Known true K223 := extend_ok (m:=223) V191 low223 (by decide +kernel)
def g239Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffff30b0c924d1974d,0xee200000000fc0000fff])),(BitVec.ofNat 152 (word80 [0x801410908904510748,0xce009249249249249249]))),((BitVec.ofNat 152 (word80 [0xc000172d3a01164d3f,0x7780000003f000fc0000])),(BitVec.ofNat 152 (word80 [0x26617292a0104453f,0x778071c71c71c71c71c7]))),((BitVec.ofNat 152 (word80 [0xf01b2ed60d04b4,0x8ac40000fc003f03f000])),(BitVec.ofNat 152 (word80 [0xb8701928540d0494,0x828430c30c30c30c30c3]))),((BitVec.ofNat 152 (word80 [0xffffa12c7d5fa8f324,0x2190003f00000000003f])),(BitVec.ofNat 152 (word80 [0x14c0a12c745ba8f024,0x21916596596596596596]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x846ad2ab4be4b9,0x10280fc000000003ffc0])),(BitVec.ofNat 152 (word80 [0x2700846252ab02e021,0x10294514514514514514]))),((BitVec.ofNat 152 (word80 [0x985515c8d2c842,0x59f7f00000003ffc0000])),(BitVec.ofNat 152 (word80 [0x380088441588d28840,0x8718618618618618618]))),((BitVec.ofNat 152 (word80 [0x4fc02019242040,0x861bffffffffc0000000])),0x20820820820820820),(0x0,0x0)]
def g239C : List ColumnInfo := [(2,0,237,0,10)]
def g239A : List (List Nat) := [[],[96,49,82]]
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
def K239 := extendKnown K223 11 [(239,[]),(253,[96,49,82,65])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V239 : Known true K239 := extend_ok (m:=239) V223 low239 (by decide +kernel)
def g247Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x5b934e134a00e37d0,0x1fc0000003f80])),(BitVec.ofNat 152 (word80 [0xc5b134c134a00c36d2,0x64c993264c993264c993]))),((BitVec.ofNat 152 (word80 [0xfe60448719d51f4480,0xfe00000fe0007f])),(BitVec.ofNat 152 (word80 [0x9e60448519c10a4000,0xa142850a142850a14285]))),((BitVec.ofNat 152 (word80 [0xb86868544e261eac0,0x7f000007f01fc000])),(BitVec.ofNat 152 (word80 [0x882068504e261e2c0,0x60c183060c183060c183]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xe40b175eac0f052aa0,0x3f800003f80000007f])),(BitVec.ofNat 152 (word80 [0xb131aa406052a81,0x42850a142850a142850a]))),((BitVec.ofNat 152 (word80 [0x20af92a4bf84a1b00,0x1fc000000000001fff80])),(BitVec.ofNat 152 (word80 [0x208c92a4b18020905,0x8b162c58b162c58b162c]))),((BitVec.ofNat 152 (word80 [0x1d50ac8d518b0552f,0xe000000003ffffe00000])),(BitVec.ofNat 152 (word80 [0x11408404018901526,0xc183060c183060c1830]))),((BitVec.ofNat 152 (word80 [0x18304911220280a05f,0xfffffffffc0000000000])),(BitVec.ofNat 152 (word80 [8,0x10204081020408102040]))),(0x0,0x0)]
def g247C : List ColumnInfo := [(4,0,243,0,11)]
def g247A : List (List Nat) := [[],[65]]
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
theorem low247 : Lower true (varsX 247) (graphGoal 247) 12 := lower_forest (g:=g247) (i:=0) (hints:=16844101) (before_sound K239 V239) g247G g247T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K247 := extendKnown K239 12 [(247,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V247 : Known true K247 := extend_ok (m:=247) V239 low247 (by decide +kernel)
def g251Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfc05d6710488bea1be,0x2000000003f8001fc07f])),(BitVec.ofNat 152 (word80 [0x4066004881e203a,0x24c993264c993264c993]))),((BitVec.ofNat 152 (word80 [0x900844b2d869ff61,0x60000001fc000fe03f80])),(BitVec.ofNat 152 (word80 [0x18100040a2d869c560,0x4142850a142850a14285]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xff00ed974111b95dc2,0xc00000fe00000000007f])),(BitVec.ofNat 152 (word80 [0x5300e9974111a15dc0,0xcb162c58b162c58b162c]))),((BitVec.ofNat 152 (word80 [0x2e166cb3567017818,0x7f000007f0003f80])),(BitVec.ofNat 152 (word80 [0x60e166811525003810,0x2850a142850a142850a]))),((BitVec.ofNat 152 (word80 [0x22b53b4d25f259085,0x403f80000000001fc000])),(BitVec.ofNat 152 (word80 [0x822b5194d257219085,0x4b162c58b162c58b162c]))),((BitVec.ofNat 152 (word80 [0x242a8ae4e964202cf,0xbfc000000007ffe00000])),(BitVec.ofNat 152 (word80 [0x202882e480202028f,0xac183060c183060c1830]))),((BitVec.ofNat 152 (word80 [0x13e0100c921020430,0xdffffffffff800000000])),0x10204081020408102040),(0x0,0x0)]
def g251C : List ColumnInfo := [(8,0,243,0,11)]
def g251A : List (List Nat) := [[],[100],[83],[83,100],[65],[65,97],[65,83],[65,83,97],[97,65],[97],[97,83,65],[97,83]]
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
theorem low251 : Lower true (varsX 251) (graphGoal 251) 12 := lower_forest (g:=g251) (i:=0) (hints:=16842819) (before_sound K247 V247) g251G g251T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K251 := extendKnown K247 12 [(251,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V251 : Known true K251 := extend_ok (m:=251) V247 low251 (by decide +kernel)
def g254Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffe688028392df1bf,0xac280000000fc003f03f])),(BitVec.ofNat 152 (word80 [0x428280028312c309b,0x8c285145145145145145]))),((BitVec.ofNat 152 (word80 [0x244fb2c0d41c5f,0xaa84000003f000fc0fc0])),(BitVec.ofNat 152 (word80 [0xcc2443b00094144e,0xaa0430c30c30c30c30c3]))),((BitVec.ofNat 152 (word80 [0x1e2ecf33da20e36,0xc340000fc0000000000])),(BitVec.ofNat 152 (word80 [0x4971e2ecf33da20e36,0xc35f7df7df7df7df7df]))),((BitVec.ofNat 152 (word80 [0xffff52717c5eb17a44,0x3100003f00003f00003f])),(BitVec.ofNat 152 (word80 [0x11805071544c914a44,0x2100a28a28a28a28a28a]))),((BitVec.ofNat 152 (word80 [0x1194b4bed2a4d39,0x19c00fc0000000000fc0])),(BitVec.ofNat 152 (word80 [0x9e0119084bed2a4931,0x11c1c71c71c71c71c71c]))),((BitVec.ofNat 152 (word80 [0x122a456034e8160,0x53fff00000003ffff000])),(BitVec.ofNat 152 (word80 [0xe00102840202428120,0x50d10410410410410410]))),((BitVec.ofNat 152 (word80 [0x9d108124920282,0xc453ffffffffc0000000])),0x20820820820820820),(0x0,0x0)]
def g254C : List ColumnInfo := [(8,0,246,0,10)]
def g254A : List (List Nat) := [[],[65]]
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
theorem low254 : Lower true (varsX 254) (graphGoal 254) 11 := lower_forest (g:=g254) (i:=0) (hints:=287405376) (before_sound K251 V251) g254G g254T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K254 := extendKnown K251 11 [(254,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V254 : Known true K254 := extend_ok (m:=254) V251 low254 (by decide +kernel)
def g255Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xff0000000,0xff803ff22ccec4f26e])),(BitVec.ofNat 152 (word80 [0x54545454545229148a,0x45229148b224cec4f024]))),((BitVec.ofNat 152 (word80 [0xff0000003fe,0x7fc0003300f2bc27])),(BitVec.ofNat 152 (word80 [0x313131313130984c26,0x130984c2602000529007]))),((BitVec.ofNat 152 (word80 [0xff0000007fc01,0xff0000000040070b0115])),(BitVec.ofNat 152 (word80 [0xf0f0f0f0f0f0783c1e,0xf0783c1e00003000115]))),((BitVec.ofNat 152 (word80 [0xff0000000000000,0x3fe0800800425f])),(BitVec.ofNat 152 (word80 [0xabababababa5d2e974,0xba5d2e9740000000025b]))),((BitVec.ofNat 152 (word80 [0xff00000000ff80000,0x7fc00303f00c7c89])),(BitVec.ofNat 152 (word80 [0xc2c2c2c2c2c160b058,0x2c160b058200600c6808]))),((BitVec.ofNat 152 (word80 [0xf00000000000000001,0xffff80000404000f8090])),(BitVec.ofNat 152 (word80 [0xb0b0b0b0b0582c160,0xb0582c160000000b0080]))),((BitVec.ofNat 152 (word80 [0xffffffe,0x1807fff000e0])),(BitVec.ofNat 152 (word80 [0xc0c0c0c0c06030180,0xc060301810068ca000c0]))),((BitVec.ofNat 152 (word80 [0xfffffffffff0000000,0x1ff800000100])),(BitVec.ofNat 152 (word80 [0x8040201,0x8040200dd800000000]))),(0x0,0x0)]
def g255C : List ColumnInfo := [(4,0,251,0,12),(8,0,247,0,12),(32,0,223,0,12),(1,0,254,0,11),(2,0,253,0,11),(16,0,239,0,11),(64,0,191,0,11),(128,0,127,0,10),(0,8,118,129,9),(3,0,252,0,9),(10,0,245,0,9),(17,0,238,0,9),(18,0,237,0,9),(24,0,231,0,9),(65,0,190,0,9),(66,0,189,0,9),(72,0,183,0,9),(80,0,175,0,9),(0,1,86,168,8),(1,8,118,128,8),(128,8,118,1,8),(0,2,45,208,7),(0,16,45,194,7),(8,1,86,160,7),(82,0,173,0,7),(128,1,86,40,7),(129,0,118,0,7),(129,8,118,0,7),(130,0,125,0,7),(144,0,111,0,7),(2,8,116,129,6),(2,16,45,192,6),(16,2,45,192,6),(16,8,102,129,6),(19,0,236,0,6),(64,2,45,144,6),(64,16,45,130,6),(67,0,188,0,6),(81,0,174,0,6),(128,2,45,80,6),(128,16,45,66,6),(192,0,63,0,6),(66,16,45,128,5),(80,2,45,128,5),(83,0,172,0,5),(130,8,116,1,5),(130,16,45,64,5),(144,2,45,64,5),(146,0,109,0,5),(192,2,45,16,5),(192,16,45,2,5),(131,0,116,0,4),(131,8,116,0,4),(145,0,102,0,4),(145,8,102,0,4),(194,0,45,0,4),(194,16,45,0,4),(208,2,45,0,4),(210,0,45,0,4)]
def g255A : List (List Nat) := [[],[65]]
def g255D7 := limbs80 #[#[0xc3ca565d64e0d6150570,0x570ea95a759383585415,0x415c3e255d974e0d6150,0x150570e995a75d383585,0x5c5415c3c3565d76e0d6,0xd7150570f195965d383,0xb835c5415c3a65e9974e,0xb95db8350570f0d5965d,0x4593835c5615c24f5f05,0x71d64e0d7158570f8957,0xd576e93835c5615c2e35,0xe35f1176e0d7158570e8,0x1d394b4ec597e0d615c2,0x506f25f0db05d9745854,0x8541ce95a4ecda05d961,0x97150763561fb3681765,0x765c541cd95a4ecda05d,0x36417650763561bb3681,0x5db945c561a3d7c1663a,0xcda05d971586d35f0db0,0x3b3681765c561ccd5a4e,0xc36c3a45d971587335e9,0x5253b36839161d61acd7,0x397a129393605805db4e,0x271206c300f0600c00e,0xcb45124114843f1b0cc6,0x2351487421ecf0753618,0x10081c10091410091410,0xe0c0400002440400081c,0x60705c10160605c101,0x1c1010]]
set_option maxRecDepth 16000 in
def g255D8 := limbs80 #[#[0xe28859b7b6611745c510,0x3585415c2c7bda30cbb2,0xae9c1ae2a0ae1ea55938,0x878d576e0d7158570f32,0x541dc29cfda32fc1ac2b,0xb22c2a0ee1cad6616458,0xf7b16a58650770d56b50,0x5071da52742cc2c3b843,0xe8b0a83cadee19759161,0x665d7458541f16f70bb2,0x8dbdc32eba2c2a0f4b7b,0x8a83e2ded1875d961507,0x9745c541db2ae9d1b20b,0xcb2ecba2e2a0f8b5865d,0x366dee1765d171507a5b,0x5c561d9aaedd1b20b8ac,0x28ba2e2b0ecb7b469d64,0xded1765d171587a5abb7,0x61b9af66d02ecb8ac372,0x8aecb0ecb7a4e85765d1,0x3a16418758735ad2729c,0x73929d1b20c3ac38ed25,0xeb0e39f94e8d9061d61c,0xe51875861df5d128c830,0x66d0728c3ac3aade9ba1,0xd39fb461b9360171a73f,0x765c66dbda34dc8ae8b8,0x9b02c02ed96d69394e45,0x1745c5415c160c73f49c,0x83e78bb2e2a0ae0b07db,0x2b82c1b3e69d76505705,0x5d9715c160d9f2edd22e],#[0x5dda342bb2e0b07cf3b1,0xac1f2d5d9745c541582f,0x7150560f36b0eba2e2a0,0xa2ecb8a82b07cb576e91,0xd3dee5765c541583e5ad,0x560dd6b48d0aeca0ac1,0x2bb282b074f7b165d765,0xea7a361d41582b7bd8b5,0xd9eaedd0ae8b8ac18f7,0x2e2b06cf7b169b745c56,0xa15d97158367ad2742bb,0xeb69d0aecb8ac1b3de93,0xb05cf7b1691765c560b9,0x4576583a5fda2ecca6e2,0x9c9f22c3ac1bade84a46,0xe9564e0d6150570c7bb4,0x15c3dcaba706b0a82b87,0xac2a0ae1eb55db835854,0xa7e0d6150570e7ab2fc1,0x3b5acbac8b0a82b86bd5,0xa0ae1bad69d64585415c,0xd16150570f96aecba2c2,0xacbaecb0a82b86db5a75,0xe1e755db835c5415c3a7,0x150570e7ab2dc1ae2a0a,0x2e8b8a82b86bd7a6e0d7,0x6de99745c5415c3adacb,0x570e9eb2cbb2e2a0ae1b,0xc1a82b853dfb961b8350,0x5d76e0d415c396ecb2ed,0xa7bb72bb706a0ae1c776,0x82b853dfb95db8350570],#[0x7e0d415c29efdcb4dc1a,0xf62d4aeca0ae14f7ed99,0x87ad564e0d71585708fe,0x5615c3ceaba706b8ac2b,0xb22e2b0ae1af5e93835c,0xf5b75917158570f96ae8,0x5c367abb748b8ac2b85c,0x6b0ae173ded1765c561,0x65d38358570e5bb2eb27,0x8eecbae9c1ac2b878dd7,0xae1eb5ec576e0d615c3,0xf8358570b5bf68bb706b,0x5a32fc1ac2b873d7b165,0x1ce7ed197e0d615c39ce,0x58570a7bf68cbf06b0ae,0xe9c1ae2b867b4a4e8597,0x75db94e0d715c38efcb2,0x70a7bb6dca706b8ae1c7,0x1ae2b879d7b15db835c5,0x596e0d715c2cefda2edc,0x73f68cb706b8ae16f5ec,0x2b853ddb4e5b835c570b,0xe0d815c29eedb729c1b0,0x69d0b0dc1ae14f76d396,0x4bddb6e9191e0d7097bb,0x835c25eeda74cc8f06b8,0xaedc1ae16e7ed1a15db,0xdb4e8596e0d7097bb69d,0x7e5ad82ecba2c2a0cbd,0xcb0a837b5ecda05d9615,0x6817658541dd6b48d02e,0xebd9b40bb2e2a0f8f587],#[0xa83b6d691a05d971506e,0x905d941f1eb0cd02ecb8,0x3746c82eca0e7d7a3645,0xa7761fa36417650756ec,0xd941c7bb31d1b20bb283,0xc82eca0e3df98e8d905,0xecda0e61765069fbd8b3,0x1d9eb60d36e8b8ac34f7,0x2e2b0f4f5b05db945c56,0xa05d971587e6bd9b40bb,0xef48d02ecb8ac3b3d691,0xb0dcf5b0e91765c561d9,0xd97458767ad8748bb2e2,0x1d22ecba2c3737ecda05,0x4f5b05d991dd161b97b6,0x658776bd1f22c82ecb0f,0xb20bb2c3bb5e8fa16417,0x94e8d905d961cdbb29d1,0x6f6bd9b41c8aecb0e6df,0xc3ac35b7ecda0e517658,0x839161d61b7af66d0722,0xfd9b40bb708b8f3b4946,0xe3b75e8f91641765c6ce,0x5d971dbaf47d0b20bb2,0x746c82ecb8e5dd94e8d9,0x75ecda0e45765c72efca,0x971cbeb28d0722bb2e37,0xc8aecb8e5f794683915d,0xcda0e51765c767bc3341,0xabeb61d0f28bb2e3577e,0xcb8e7b4946839161971,0x1e51865c73dbca341c8b],#[0xf27c0b02c02ed5ed6c3a,0xb679fa4e4d8160176e7a,0x5805db9ebc9f22c0b00b,0xc9b02c02edae7e939360,0x9fa4e4d8160176e73949,0x5db1efd2726c0b00bb73,0x2c02edaede84a460580,0x4e8d90e0576c7bb49c9f,0x1efca746c8702bb63dd9,0xae845419a0850240003,0xc5ee2af13388a83ae184,0x823810cc7ec3b91b88cf,0xf8c565e32cd954ca164b,0xe13d21dc8e6a6f835d99,0x5ed292901451a1c50687,0xaa7540293944e9f54dc2,0x2e456beb43593ac5959c,0x4c2e6092fd979ebbe5d1,0xeb35998aca9646b19989,0x8d5d69b3495a28d0e67,0x5b7e9bd2dd86de3681b,0xd66ea2748ba01c9ce3d7,0x797bca5e1af07775bb69,0xdf6cfa57ca3de1ea2f40,0x2808c001fdefde7e6bf1,0x220ef06682ac0e606702,0xee86ec35e18d0b585242,0x4fa271132890c4161e90,0x212900c76a33b18c8ad4,0xcb42553298943c9da473,0xb3c59c44d5a61d2fd970,0xc536e9694aea43d0fe81],#[0x3f58eab95586aa1534a8,0x135856bf35ddae656c2b,0xd9d6bdb50da16ca7637b,0xb9fdce6e5170cb7ddbaa,0xefa37aabd25e4ef0575b,0x70c97c0f85f046bf45f5,0xdf00147c2f82480503a0,0x60c94526783f81f09278,0x9278d423c1a07f81f092,0xf03e107423c1a07f81f0,0xde0fe07c2f828547f07,0x5f07f03e17c142a3b870,0x687f07f03e17c115c380,0x43687f07f03e17c178a3,0xf8437c381fa17e0fc0f8,0xc1f842411a1e833e0fc0,0x2fc1f80457e10c457e07,0x7237c1f81f088a8bd1b4,0x20302ec3f80c33e14231,0x7c0f83f086033f07e07c,0x827c0f85718705204706,0x3fe07c28403192d0bf07,0x3f07827c0f8430c8d86c,0x22c3fe17c1f80301d02,0x1d019f0687fc0f84301d,0x4148c0f70fe07c2c1e38,0x842a1191ff07e07c214c,0x1f84f145f87f0488fc0f,0xcc8f81f09e28bb0fe07c,0x5f045d87323e07c21361,0xf83f03e10fb0c107c0f8,0xc3f81f08521f233e1a91],#[0x4743c91f03e109c3ce45,0x8065c6d09f07e07c20ac,0xd1942056f83f03e10c34,0xf060342f43a91f03e109,0x9306e82c0c5c24313a0,0x61c1d06e8203a818806b,0xc300fc0fa0d061205f41,0x41a223830321f41c0fc0,0x383050a894625115c0c4,0x832882312f061244f061,0x40743f830b4703a1ca2f,0x80cf8309874927061f4,0xcc97830b03b8308a2383,0xc184067c185838c97830,0x782912c0f830de283c1f,0x4237830d22829181012,0x42099e042f02117c187e,0x382930108de042f0211,0x828558978100e224505,0x83d10142ac4803f8113c,0x4404ac01720619460483,0xe081e07c1840744f0617,0x11020a213fc087d18149,0x282014507c083e041f02,0x6a78253c1e88094604a,0xbc604a283e07c1840145,0x4a203d10120e510278c0,0xde304f14101e30207440,0xc11e2f8308003c183e0,0x705820bc301048f0de0e,0x370ee080e0c4b44e219,0xf70ee08a25ae0b040f86],#[0xc18160e0d85048a90c40,0x3b6085e10163005d4186,0x54786f048750f1bc2039,0xc105786f0412220100d0,0x870c0f8d06a071c1b87,0xe3877068209038e2dc16,0x8542187048abc3c1e340,0x5478609c301e1bc141c1,0x61020a8f0de0a1591e28,0xbc202e10181d6102a0d,0x836382c1e0f840783684,0x306ac20541ec205b181b,0x43862707d08178405c20,0x524205052420415a0a28,0x280c94048a3c30bc2030,0x12d8a10123c1a1e65029,0x58a0e8f068df0ea8218,0xd10178a081c3924f410c,0x1]]
def g255H8 := limbs80 #[#[0x758000011500a0100302,0x387,0x4bc0052400f200000000,0x52908d0,0x48c00da0000000008800,0x14c00000000000000000,0x143002ce0014500000,0x2bb27000000000000000,0xf1800590006474b03400,0x8a002618abf3,0x361f143000,0x49800303b226400,0x95c0001041000007c3d4,0x2cf]]
set_option maxRecDepth 16000 in
def g255D9 := limbs80 #[#[0x7158110f6c5d17150110,0xe6d611745c510f3c5d9,0x1985d910e3d619765c51,0x418efe9198587708efe9,0x5d6458541ead61d64585,0x541f2d5d97458541dad6,0x61d7658541d6d65d7458,0xc541e6d619745c541e3d,0xd619765c541d6de59745,0x5d941b6d693765c541e3,0x2d5d1645c5618fde8598,0x45c561b3d69d645c561f,0xd3d5db945c561b3d69b7,0x91dd161b3de91765c561,0xced2539161d61d3d5d9,0x98750110f7c5d9715011,0x10f7c5d17158110afee9,0x918758110f3e5d974581,0x1109fee919758110afee,0x5d9715c110f7c5d1715c,0xc110cfee59845c110f7c,0xe61b945c110afee99845,0x5c1109fe69b945c110cf,0xfe693965c110afee9186,0x5c510f7c5d3905c5109,0xf7c5db905c510bfc6939,0x645c510bfc69b905c510,0xf3d5d9645c510f6d5d1,0x1745c510b7d69d645c51,0x10f6de51745c510f7c68,0x99745c510e7d619745c5,0x510b7d69b745c510b7de],#[0xe99845c510e7d5d9845c,0xc510f7c681765c510afd,0xde59765c510b7de91765,0x5c510e7dea1765c510f3,0xfde91865c510b7d69376,0x459110bede91965c510a,0xaf7e8d8759110f2f5d97,0x97591108ffea58759110,0xe3f619765d1109fde85,0x1875d110b7d687765d11,0x108ffe99985d110aefe9,0xd991dd1108ff69b985d1,0x1108ffe9998dd110d7d5,0xe91865d9108ff69f9661,0xd910abfe99875d910abf,0xfe91985d910aefe91985,0xdd9108ff693985d9108f,0xff69f94619108ffe9198,0x61d10afe6939061d108,0xcf7e539361d10afe69b9,0x9461d10cf7e5b9361d10,0x8ff6939661d108ff69b,0x3915c160f3e5d9715c16,0x60f6d5d171505609fe69,0x5d7650560f3d5d971505,0x560af7e8d8750560d3f6,0x5d9905c5608ffea58750,0xc560b3f69b745c560f3e,0xee81765c560d3f5db945,0x5c560f3de85765c560f3,0xefe91985c560afde8587,0x4dc5608ff693985c560a],#[0x8ffe9198dc560d3f5d99,0x915d960bbe687905d960,0xafe6879061d60bafe91,0x39161d60cf7e4f9161d6,0x70ef5e0d61505708ff69,0xd7150570fad59161505,0x570f6d5d17150570ef5e,0x65f8350570cf765b8350,0x85708ff6a78650570cf7,0xd5d97158570ef5e0d715,0x58570eb75938358570f3,0xf765f8358570eb75db83,0x7585708ff6a78458570c,0x9fe693905c5709efe919,0x835c5709fe69b905c570,0xcf7e53835c570e775d3,0xb835c570e775db835c57,0x70cf7e538360570cf7e5,0x9994e0570cf7e5b83605,0xd708ffe9196e05708ffe,0xe9191e0d70af7e8586e0,0xd70af7e9991e0d70af7,0x7e8596e0d70af7e8576e,0xe19709fe687905d970af,0xad59161507708ffe9191,0x150770eed6116150770f,0xcfd6616150770ebd6196,0x8150770afd6a16150770,0xafde998150770cfd659,0x58650770cbf659865077,0x708ffea586507708ff6a,0x9181587708ffe9998507],#[0x770afde918158770ebd5,0xe858658770cbf6616458,0x8770abfe918658770ebd,0xf2919858770cfde85985,0x58770cefe919858770ce,0xff69b94607708ffe9198,0x660770afde8596607708,0x8ff6939660770aefe919,0x9161b70aefe919161b70,0x1fad5d974585418ff693,0xd7458541fad699745854,0x41fad6917658541ded65,0xa17658541ebd61d76585,0x541eede918758541ebde,0xe919758541ebde998758,0x8541dbde999758541ded,0x5e8d905c541cfdea1975,0x5c541f6d5d1905c541bf,0x6d5d3905c541bede9190,0x45c541f6d5d9745c541f,0xdede59745c541eed6197,0x745c541f6d659745c541,0x1f6d5db945c541f6de59,0xb945c541ded65b945c54,0x41ebd619765c541bed69,0xa1765c541dbde59765c5,0x541f6d691765c541afde,0xea1765c541f3de59765c,0xd941bede91965c541e7d,0xf6a3905d9419fd687905,0x5d941ded651915d9418f,0x7de85875d941abfe9987],#[0x85d941e3fe99875d941e,0xcfde85985d941afde859,0x985d941cbfe99985d941,0x19f7e8d90dd941cfd687,0xd9061d41afde859061d4,0x418ff69b9061d41af7e8,0x9b9161d41eede539161d,0x561afde859661d41afd6,0x5d9905c561bf5e8d905c,0xc561bbde99905c561f3d,0xd5d1645c561f3d5db905,0x5c561fad651645c561fa,0xede51745c561bbd69d64,0x45c561f3d5d9745c561d,0xf3de59745c561f6de517,0x945c561f3d699745c561,0x1dbde59945c561f3d5d9,0xb945c561bbde99945c56,0x61dbd5db945c561f3d5d,0x81765c561bbde91765c5,0x561f3de81765c561f3d6,0xe91765c561f3d691765c,0x9161bbd693965c561f3d,0xfe918759161ebde85875,0x5d1619fd687905d161ea,0xff6a3905d1619bf69b90,0x15d161f3d5d9915d1618,0xbafe91765d161dbd6599,0x765d161f3de85765d161,0x1aefe91875d161f2fe91,0x1875d161e7de85875d16,0x61e3fe99875d161e6fe9],#[0x8d90dd161afde85985d1,0x161f3de8576dd1619f7e,0xe8587dd161dbde8596dd,0xd961cfde8598dd161e7d,0x7e8d905d961bbde85905,0x5d961dbd653915d961bb,0xbd693915d961dbde5391,0x45d961bbde85945d961b,0xafde859061d61dbde879,0x9061d61af7e8d9061d61,0x1cefe519061d61cef251,0x99061d61aefe919061d6,0x61cef2539061d61abfe9,0x939061d61cefe539061d,0xd61eed2539161d618ff6,0x6939161d61eede539161,0x1d61ebde5b9161d61afd,0xfaa49461d61eafe58946,0x61d61afde859461d61ae,0xede879461d61abfe9994,0x461d61eafe5b9461d61e,0xcef6839461d61eafe9b9,0x9661d61cefe839461d61,0x1d775d39360171abf693,0x39360171cf7613936017,0x71d775db9360171cf7e1,0x1b9360171cf761b93601,0x171d6fe517460171cf7e,0xe918660171d3fe597660,0x171aefe9186e0171aef,0xfe9994e01719fde8596e,0x5d1718ffe9196e01718f],#[0xfd69b915d171d7d5db91,0x65d171b7de85765d1719,0xb7d683915d171e3fe197,0x915d171f6de13915d171,0x1b7d69b915d171d7d65b,0x586dd171b6fe91865d17,0x71d7de8596dd171b7de8,0x597661171e3fe1976611,0x1719fde8596e1171d3fe,0xe9990e1171af7e8d90e1,0xd971ebde1b915d9718ff,0xf693865d9719fd693915,0x5d971b7de85905d971ab,0x7d683915d971b77e8d90,0x15d971d7d653915d971b,0xb7d693915d971d7de539,0x945d971f3de1b915d971,0x1d7de87945d971b7de85,0x3865d971b3f683865d97,0x71ded2539161971b3f69,0x879461971dede5391619,0x971af7e8d90e1971dede,0x69b90613718ffe9190e1,0x1371e6fe9176613718ff,0xf6939061b71aefe91966,0x60176cf7e4d81601768f,0xf7e4f8160176aefe9181,0x1e0176aefe9181e0176c,0x8ffe9191e0176cfd6478,0x9460576dede449460576,0x6dafe5b9460576dafe58,0x784e0576dafe9b946057],#[0x76af7e8d90e0576afd68,0x9390607768ffe9190e05,0x160ff6593935c1108ff6,0xe4d415c160ffc5c5415c,0xc160fbe5d9415c160ff6,0xe5d1715c160bfe69d415,0x5c160bfee91715c160f7,0xbee85765c160fbe68576,0x150560fed5d17150560f,0xfbd5d97150560fede917,0x7650560efd61d7150560,0xdbf65d7650560fbd685,0x57650560dbf6a5765056,0x60ef7e8d8750560dbfea,0xa58750560cff65d87505,0x560dfde859750560cffe,0x5d9745c560bfde85745c,0xc560e7f61d745c560f3f,0xf5d9945c560f7de85745,0x5c560f3f5db945c560f3,0xff61f945c560dbf5db94,0x65c560fbde85765c560c,0xf3fe91765c560f3f6917,0x76dc560f3f69176dc560,0xdbf69196dc560f3fe91,0x5915d960dbfe9196dc56,0x60dbf651915d960fbde4,0x91915d960dbfe51915d9,0x960fafe91915d960faf2,0xe53915d960bbfe91915d,0x1d60bbf693915d960dbf,0xf6939161d60cffe53916],#[0x50570ff5e0d6150570af,0xbd5d96150570fed5d161,0x150570dfd65d6150570f,0xf7d5d97150570bfd69d6,0x7150570dfd6597150570,0xef761b8350570bfde99,0xb8350570df765b835057,0x70ef769b8350570ef75d,0x5d7650570dbf65976505,0x5709ff6a57650570d7f6,0xea586505709ffea57650,0x85709ffe9997505709ff,0xd5d17158570fbd591715,0x58570bfde917158570f7,0xf76138358570fb759383,0x358570ef75d38358570e,0xdbf65d6458570ef76938,0x7458570f3f5d97458570,0xfbde857658570d7f65d,0x59758570bbfe91765857,0x70def2919758570dfde8,0x919758570defe9197585,0x570ef7653835c5709ffe,0xe59745c570ef765b835c,0xc570d7f5db945c570d7f,0xde85765c5709ff69b945,0x5c570b7fe91765c570f7,0xefe91965c570bfde8596,0x4605709ff693965c570b,0x9ff69396605709ff69b9,0x76e0d70ef768576e0d70,0xbefe91915d970ef7e85],#[0x391619709ff693915d97,0x41fbd68176585419ff69,0x45905d941f7d681765c5,0x941bf7e8d905d941dfd6,0x61d905d941ebf619905d,0xd941cff661905d941e7f,0xf683985d941cffe61905,0x5d161fbd681765c561cf,0x3f68176dd161f3f68176,0x5d961dbf68196dd161f,0xfbde85905d961fbde459,0x905d961fb7e8d905d961,0x1dbfe51905d961dbf651,0x3945d961fbd683915d96,0x61dbf683945d961bbf68,0x8196dd171efd6839161d,0x971e7f68176e1171d7f6,0xe19905d971dfde45905d,0xd971dfd683915d971ebf,0xde85905d971f7de45905,0x5d971f77e8d905d971f7,0x7fe51905d971d7f65190,0x15d971f3fe19905d971d,0xb7f683945d971f7d6839,0x9161971d7f683945d971,0x1e7f6817661371bfd683,0x1905db71d7f651905db7,0x71d7f683945db71d7fe5,0x519061b71cff6519061b,0x176cff6839461b71cffe,0xe4d8160176efde058160,0x176befe918160176df7],#[0x7e4d8160176efde45816,0x60176eef2918160176ef,0xffe918160176eefe9181,0x160176ebfe998160176a,0xef7e4f8160176df7e4f8,0x9160176aff6938160176,0x6aff6838460576df7e4f,0x190e0576bf7e8d90e057,0x76ef7e8d90e0576cffe1,0x5190e0576cff65190e05,0xaff68394e0576cffe,0x186014400f800a200560,0x366031a02b0024601d20,0x53204be0468041c03c60,0x70806b2064805f205880,0x8980856081407be075e0,0x9ec09aa0968092608da0,0xb0e0ad60a9e0a660a2e0,0xc440c020bc00b7e0b460,0xdca0d7e0d280ce60c860,0xf640efa0eae0e6c0e160,0xcc108a103e0ffc0fb00,0x23e11fc11b0116411221,0x3c41382132c12d6128a1,0x52214ea149e145214101,0x69e165c161a15ba15821,0x81017ce178c174a16f41,0x96e193618ea189e18521,0xb301ada1a8e1a3819e21,0xcca1c6a1c281bc81b7c1,0xe5a1e041dae1d621d0c1,0xfae1f621f201ed41e921],#[0x13420e82088203c1fe61,0x2a6226e221821cc218a2,0x41823cc2376233422e82,0x5c62570251a24c424642,0x70626b02678263625fe2,0x882282227d6278a27482,0xa1229bc297a291a28c42,0xba22b422b002ab42a682,0xd642d0e2cae2c4e2bf82,0xefe2e942e3e2df22da62,0xc0306a300a2fbe2f5e2,0x278322c31cc318031203,0x42633d0337a332432c43,0x5ac3560351e34d2347c3,0x71e36c8367c363035ee3,0x89a384e380237b6376a3,0xa2a39de3992393238e63,0xbce3b643b183acc3a803,0xd4a3cfe3cbc3c703c243,0xebc3e7a3e2e3dd83d8c3,0x383ff63faa3f5e3f123,0x1c84168410840c640844,0x358430242b6426a420a4,0x4d444924450440443a44,0x66e460e45cc4576452a4,0x7f447a8475c471046c44,0x984492448ce488248364,0xb144abe4a724a1c49d04,0xc904c444bf84bac4b604,0xe0c4db64d7e4d3c4ce64,0xf7e4f324ef04ea44e584,0x10450b8506c50164fc04],#[0x262521651ca5174513c5,0x3ca537e533c52f052ae5,0x55054fa54ae546254165,0x6b85676563455de559c5,0x82a57e85792575057045,0x96a592858e658a4586c5,0xb2c5ae05a805a2a59c05,0xcbc5c705c105bc45b785,0xe565e145dbe5d5e5d125,0xff05f9a5f445eda5e985,0x1b2614860fc60a660465,0x33862ec62a0625e61f46,0x4be6472643063e4638e6,0x66c662065ca656a65146,0x7de679c6746670e66c26,0x95a690e68b86876682a6,0xae06a946a3e69e869a66,0xc3e6c106bc46b826b366,0xd566d286cfa6cc26c806,0xe826e4a6e086dda6dac6,0xf7c6f4e6f2a6ef26ec46,0xb2707a7042700a6fbe6,0x1a27174713c711870e07,0x292726e7240721271da7,0x3647340731272ee72c07,0x472744e740c73ca73927,0x530750274de74ba74967,0x634760675ce759675727,0x738770076be769a766c7,0x828780477cc77a8777a7,0x8e678c2789e787a784c7,0x9b879947970794279147],#[0xa807a5c7a387a1479e67,0xb5c7b2e7b007ad27aae7,0xc567c287bf07bc27b8a7,0xd1e7cf07ccc7c9e7c7a7,0xe187df47dc67d8e7d4c7,0xf1c7eee7ec07e887e467,0x27fde7fba7f827f407,0xfc80ba8096806880308,0x23281f081a4814e812a8,0x340830882d082a2826a8,0x462840c83d4839c836e8,0x58e8556851484c8849a8,0x6928664863685fe85bc8,0x796875e871c86e486b68,0x8a4886c8848881087ce8,0x9c6897a8956890088dc8,0x7c206488a5a8a2289ea8,0xe4191c2b8250b0abc0f0,0xf0819210e827c0f07c20,0x906472900742523f03c1,0xc10646e0c07f03c2f043,0xfc0f0bc11f46e13c0f0b,0x7c0f083a2f46d1287e0,0x281d071158440cf0e0ff,0x8440ff0e0cf07c0f0838,0x343fc1f03c2830a07115,0xc0f08381c310bc24077c,0x7c0f083a242f43e0cf07,0x818201d457c34320ff0,0xf0870bc2e067c3f07c0f,0x20608291230c3c1f0091,0xc2c2e0c419f0fc1f03c],#[0x1c25819f0e0ff03c1f09,0xfc3f07c0f0b112223074,0x47c2f07c083ca07c15d1,0xf0039201d0702f0bbc32,0x243ca074910ba0ff0bc1,0xa8801c067c3833c1f03c,0x32f0c91f0bc1f010f202,0xbc3433c1f03c283c8880,0xd11f07c0f088f25200b,0xf07c0f09c5201c0c419f,0x2f04190ac605747f0f86,0x84f03c2f04191b0bf03c,0xf0ef03c2f04190ac6d17,0x1ac50c7c0f0bc1c24191,0x10646e1346f03c2f0419,0xc206c391b46e13c0f0bc,0x7c0f081b0e4606741f03,0x1609f03c1f08191419d0,0x2f041917c0f0a8cf0419,0xc5c27c0f081b1509f03c,0x81b17c0a3fc2f041916,0xf0bc10702b1ac6c27c0f,0x3f03c1f081c0ac6813c0,0xc6813c0f0bc10702b1a8,0x242b2683f03c2f041c0a,0x182f07c51067c2f03c1c,0x90ac8067c2f0309f0439,0x2a1c310bc1ff0bc0f070,0x42b1c1bb17c0f0bc1424,0x420201ff0bc0073c1c2,0xbc6e0c1d71bc0067c2f,0x1c24191dc6f03c2f0709],#[0x19f0823281cb17c0f0bc,0x870a42201f83b17c0f04,0xe47071c6f0019f0bc108,0xc4606c19f03c2427c10,0x9070311dc5f03c1f0b09,0xc14242b182bf03c2f070,0x3c2f07090648067c0f0b,0xbc108019181cb19c5f0,0xf03c2f0427c247a3bc0f,0x1f0bc0f07890e470820f,0x83e13c2f0094d4460645,0xf46e0f84f03c2f04281f,0x2346d17c0f0bc1624271,0xd141d23831f03c2f0419,0xcb1b45f03c2f05890648,0x47e13c0f0bc106424181,0x246d178471bc0f0bc106,0xa24191f45067c0f0bc1a,0x2f07c21c1cd17c0f0bc1,0xc2f04221745e1247f001,0x7c0f0bc1a242826c6f03,0x7c0f0839141d919c506,0x6746f03c2f06892783f,0xf07c2714161828091c5,0x46067c0f0bc1a246e0fc,0x1291f46717c0f07c223,0x1b84b17c0f0bc10648e1,0x4a09f03c1f082b1816d,0x2b1812827c0f0bc10ac6,0xb090ac606417f03c2c24,0x3c2f04241c1905fc0f0,0xf03c1f08281dc6e0ec5f],#[0x43bc20641b1f84e0ec6,0xc4c3bc0f081b1741b13c,0x223067c0f07c21338e2e,0xbc19318e201d0738349,0xf07c2a38807031067c0f,0x22534c1c30d13450c7c0,0xc20554c2344e0f86f03c,0x48e0ac7d1016e0fc0f07,0x419638706f44f03c2f0,0x43fc16389b1744f03c2f,0x20e060ac11b1432f03c2,0xc2f068e241923bc1f03c,0x42018230701951032f03,0x68e0548e1bc0f0bc106,0xf08191dc507f44f03c2f,0x10658e2383d1386f03c1,0xc1f08803ec5d13c0f0bc,0x838178604a47d11c5f03,0x3c2f070e1a0ef07c0f0,0xf0012f0bc10c470ca0ff,0x9f17c0f0817c38683832,0xc5e0fc0b13c2f04201c1,0x44f2383933c0f0a4f15,0x9307e1c5113383f03c2f,0xc26c987108e0e87f03c2,0x70741c06786e07c0f084,0x8805c0841f83f03c2560,0x91d470945194cf0383f0,0x93c7d16c6f0015f089b1,0xf26c887108e0e87f03c2,0x4f1419e17810e3c0f084,0xfc0f094f1b83547c2f01],#[0x154fe0fc0f0878238361,0xf03c253c1526c6470945,0xb0a383f03c2f064f22c5,0x28a0fc0f0bc10c07a698,0xb440ba83f03c2f047048,0x2107f01c5e0fc2d10904,0xf1b83f03c247084751ca,0x71bc2e0f44204a021c5,0x83f03c247084728841fc,0xbc0f0833144a021c6517,0x194504bc0f08331412f1,0xc86c505b44b17c0f0a1b,0xc0713c205c805bc0f094,0x3c205c1e1b83066c6f17,0x53c0f08170786f1a14f0,0xa1fc5b1bc0f09891cc58,0x3b1bc5f03c205e141c50,0xc4d1a83f03c2f0427278,0x15d1bc0f0a1b1828049,0xc4cf03c2f044fe1c801,0xe0d87f03c1f0a4f2451e,0xcf03c1f0831181d4584c,0x1561fc0f07c2b188e0e4,0xf45f03c1f08152345e0c,0x57c0f0bc1a1c7b1b8361,0x71bc0f07c20707133830,0x3a1fc0f0bc1160603383,0x45a1f83f03c2f0415278,0xbc0a1fc1f08152008b1b,0xdc6f03c2f048d1783b1,0xf0bc0f0551274505687e,0xf064f241c8544fe0e87],#[0x202096055c5e0e87f0bc,0xc691b8301587f0bc0f04,0xa4f1d44e0fc0f0bc10b,0xf04201f8307e87f03c1f,0x1714152346a1f83f03c2,0xc1054ad1a87e0fc0f0bc,0x1cd1287d19c5e0fc0f0b,0xb44a1f83f03c2f05c526,0x1f83b17c2f03c12415d1,0xf03c2f04201c16d11c6c,0x3f03c2f041526c6e0f07,0xc2f04162307716c6d138,0xbc1e0c9d1383b1b07f03,0x498734671707b13c0f0,0x574671707e0fc2f02c4f,0xf0d0ff060cf03c209c70,0x1f0d0ff07c0f08960bc9,0x85f050ff03c209c70741,0x7c3f050cf03c20c47f0e,0x1fc3433c1f03c283c904,0xf050cf03c209c80741c3,0xcf07c0f0b462029f0e46,0xc1f03c208c8033c30541,0x7c0f0820201c01bc3833,0x7c2070807185f0e0ff0,0xf08271c0ff0f85057c0f,0x2c30231bc3d1bc1e17c0,0xc1f0a0988c7b0fc0153c,0x3c1f0a0908c606985f03,0x1fc022fc2f04381985f0,0x75c3f07c0f0a0c0c474,0x8067c3f07c0f0a470607],#[0x11f0e0c71bc0f07c2070,0xd0ff07c0f0a0c454381c,0x1e0c71bc1f03c2071231,0x11d0f70fc1f03c20720c,0x1c1fc3057c1f0bc00709,0x8181fc3833c1f03c243c,0x82e1c19f0e47f07c0f0,0xf081524c6f0f0cf03c1f,0x11c92f0ec6e17c1f0247,0x2e1c32f0d0cf07c0f083,0x82920230730cf03c1f08,0x307f0c23067c1433c0f0,0x9c7057c3f07c083fc24,0x109c7d1ac3e17c0f07c2,0xc283cae1746f02c3f0bc,0x2f0b829447c3233c1f03,0xbc3e1784f0546f03c220,0xf46077c1f03c208c724,0x741cf03c1f08230c07d,0x3a1fc3e17c1f03c20c46,0x83a1818057c3f07c0f08,0x10ff087063c3f07c0f0,0xf0247f088e17c305bc1f,0xf08231f85122c3d1b84,0x54f08231812432c3f07c,0xbc0f0bc1b0c8e16c3f00,0x3c1f08301c18e178404,0x71bc0f081f1c0cf0c23f,0x3f07c0f083a1e0cf0fc1,0xff03c2150201815b1bc,0x886f03c2f06098807b0f,0x1986f03c2f0609080606],#[0x83c941c8ef03c2f0438,0x90741c51fc3247c2f07c,0xcf0c91f07c0f09150b8,0x7c383fc1f0bc00b86070,0x17c315a47f0bc1f030f2,0xf07c043fc20bc381c1d3,0xff0bc1f030f070201c1d,0xc30710ff03c1f082e201,0x504f07c0f081f0bc7b16,0x7c0833c20ea150e0907,0x247c0f07c2070707586f,0x3833c1f03c243c6f0c15,0x843fc1f0bc0072201bc,0xc11f0ec5f0bc1f010f07,0x21c5f0fc1f020ff082e1,0x7141a0e3c0f088ef060f,0x382407f03c2427c10e06,0x1df0c91f0704f03c20e4,0xfc3717c1f03c283c3120,0xe0ff010cf07c2070701,0xf0c0fd17c1f0bc00bc7f,0x7f0e0f517c1f0bc00807,0xc6b0f86d17c0f07c209c,0x4271ec3e13c2f03c10b,0x902f1f86d16c3f03c2f,0x283056201d21bc1f03c2,0xc2a3c9447c323fc1f03c,0x8707545f0c5691fc1f03,0xc47d174323fc1f03c20c,0xbc801fc3f07c0f082a0,0x21c05e13c3f07c0f0816,0x2a2020d0f45f07c0f083],#[0x8707145f0fc1f03c2080,0xbc707343f07c0f08200b,0xe3c7f0f11f07c0f08160,0x223c712345b0fc091fc2,0xc223c791f43847c1f03c,0x3c2060891fc3d17c1f03,0x88f201c23e47d0fc1f0,0xbc605647f0f45f07c0f,0x21530f148483bc1f03c2,0x11f07c2f008c22c3f03c,0x3c1f03c20a470a60ff0d,0x47c2f07c083c7f0e0f23,0xf07c0f090f09c70a7c34,0x3233c1f03c21586f0e11,0x1243ec3f07c0f08201fc,0x548e1ac3f03c21502018,0x2225e1ac3f03c2f05c50,0x2f86b0e25f03c2f0420,0x70170fb0fc1f03c20807,0xc50490fb0fc1f03c2080,0xbc10dc5b0fc0f0bc10d,0x4bc0f0bc1b0c8b0fc0f,0x3f07c0f08371c18e1b84,0xff07c0f08201c1583fc,0xe0ff07c2f00201dc5f0e,0x3fc3f07c0f082019c5f0,0x57c343fc1f03c2b1470,0x381fc3f07c0f08150dc6,0x3c21ec5f0fc1f03c2054,0x8201d0ff0c15b17c1f0,0xf03c21c8cf0d0ff07c0f,0x2f00201ec5f0c15f050f],#[0xc2f04202091f0d0ff07c,0x70f0a07e18c570d25f03,0x3c2080651dc3f03c2f0,0xd0fc0f082b23c3073c1f,0x853c208c661dc592384,0x43f03c24702b19c5d0fc,0xe48e1343f03c20ac7923,0x19c5d0fc0f0a14080761,0xa2248d0fc0f082b47067,0x606805d0fc0f0bc10802,0x4201b43e13c0f0a1b0ac,0x64e8705b1b09f03c2f0,0xf03c2f04200706f03c2f,0x671b43f03c2f04301909,0x88f2384f03c2f054b0a0,0x8a0641c70fc1f001df0,0x4452f0f4571bc1f0284f,0xd0d0cf07c0f083220154,0x3d17c0f07c20b8907019,0xc0f081d0a870c81c0674,0x3c1f082007c70501af07,0x7c0f081d07c7077c007,0xf07c0f081d07c770c8ff,0x3f07c0f082007c906484,0xcf03c20707016c6c13c,0x3c1f03c24308d0c19f05,0x7c2070231ec6067c307,0xf03c1f08232446d0fc0f,0x20541c201df0c19e1345,0x1c0ac614bc3433c1f03c,0x3c2f041918c8b0fc0f0a,0xfc1f03c20c86d1784f0],#[0xd19c5f0a84f07c02a84f,0xf07c207080551114bc3,0xc0f082b21c5f0c9291bc,0xfc2e10806b07212c3f07,0x419242dc1cc8f0346b0,0x201a05032d1a84f03c2f,0xbc2970c8cf07c2f002b,0xa011c30a7c1f03c20ac7,0x19c1c84f0fc1f0bc00ac,0xfc1f03c20702b1829074,0x17c3613c1f03c208caf0,0xf07c0f0856181d06707b,0xaf03c1f081c0ac7f0c8c,0x1df03c1f081c08c70501,0xa84f0fc1f03c20dc8064,0x57c3f07c0f0a0f2015d1,0xf048cf03c243c7871c50,0x8b0fc0f082b8706057c3,0x84d1bc0f0bc1058191cc,0x412c1f84f0bc0b0fc123,0xec6e13c1f001df088d1,0xb1b84f07c0f0b072419f,0x4f03c2b0fc12019f0c16,0x8ff03c24507d1812c1f8,0x3c0f0b0ef0480b6c5d0e,0xfc0f09141f1b52c32b1,0xf0bc1924311786f16c4d,0x6d0c20f03c2f042723c0,0x86f03c2f054b0a0604b8,0xd44f0fc1f03c2b15291f,0x191cf0fc1f03c2b14311,0xe48f0fc1f03c20b831],#[0x271d1c43cc5f0fc1f0bc,0x8941fc3b17c143fc0f08,0x594c1b86f1744b0fc0f0,0xf07c2b0c8067c0f07c20,0x104b84234404b07e1bc0,0x60687069d142707c0e4,0x412e1888490731703d07,0x1f031c1a83b07b130350,0xc1b03180eb134106a124,0x1064c406c70480e41f41,0xbd0412c3848390e3174,0x1c644a0771741c0c8f18,0xe3819148671303d06068,0x411444e0f8e108711383,0x47606452087d1783064,0x1d4ce0c4054944498e03,0x2e0c60391221f83100fa,0x86a1f83141844e875051,0xf4cd1081a38121912d12,0xf068e149403281a38426,0x8e104ce0f8e0c1203344,0x88e60f4406461138324b,0x1581066440801f1e4543,0xe168511019e382a14149,0xc50ad8e141c066c508d8,0x58541e12b158e101c066,0x81f8306434518e604200,0xf0c440460e715440e45,0x49181c1906383160e716,0x24783101903dc581f831,0x830c1971607e0c481c19,0xc4c1cc531383130703f],#[0x7138383c370cc5c1ec4e,0xc4e0e0f0c833178383c3,0x1c922278314c5b1307e0,0x581560c12316c41811c,0x830c1604b0ef04c47146,0x7830c4fe07830d81917,0x1117830f8111b830c4ce,0x407e0c60644ce049b138,0x1445e07830c1805512e0,0x2e0d5814905334463812,0x8541d46d114c101aa041,0x783068453008d101763,0x104b831846e049b0d12e,0x8106812e0c516048e044,0x1203344f06c6e0c6d13,0x14781e0c3e040e04b831,0x46e0c30e01913f8126c5,0x2c35048451281e0c3e07,0x105d8b0dc54754f0c8d6,0x19e049b1381117830c2,0xe07831038e044526c40e,0x81e0c3e0744e0c311844,0xdf831037e064fe0c413f,0xc5303e058b0a03117810,0x78186c4471c553c34751,0x4a8b11c6e051b0c2e11,0x1b10191138186c471b81,0x492e078302440c781d12,0x4b83121ce0427d13831,0x471bc1e0c12b145e040e,0xc9c714cf0fc104b83b18,0xc6f81e0c311087319c40],#[0xc1e0c12b104e0412a243,0x70c70c609dc113b0c13,0x9388cb0585142316c197,0x4e0683c1f06e138c1015,0x4a4e185bb06c30384b04,0xe12c1938546093b05810,0x8e1012e11c1538408812,0x3c67042f0e03151c1068,0x23a8f1426151c370427a,0xe0ec1838890c5470427,0x385868c183b8413c1612,0xb060ee104b042f6101f8,0xc309f0f1a847050e0c2f,0xc2f7050ee1041500e305,0x7048ee11c3220f7058e0,0x57042470c70ac1a06414,0x4e026c161060989bb194,0x43185284b044e161414a,0x6489111414a847054e1,0x5066c3f058486c586ec1,0x1f0e440660e3041be10,0x138512ec10c78412c161,0x10668470c541ec10c42d,0x1430423e11c3230846dc,0x8c10dc1e1031141a064,0x914570c72505270e0f1,0x4b04c3460606819051c1,0x258504b30ec1162507e1,0x5519386495c1451c312,0x480bb064e141685012b,0x411244450127054e1214,0x70e102db168f0c8fc3b],#[0x4b0eb17c131050c71bd,0xe151b04ac5506c4c386,0x7410df0e143705741a3f,0x380b3134151432181531,0x6b1030b415d048f4385c,0x4546c12c39419245a1e8,0x6a0eb10304b4105b0e71,0x914c125012d114323888,0x4104a441f87e1b440c15,0x4123068e0e148380b30e,0xb068e141604ac1a39c51,0xe30494049c3141202f44,0x8]]
def g255H9 := limbs80 #[#[0x26c08a0600688040550c,0xc39c402cd0458584930,0x80805a580810c2c08620,0x1b02ce0786040805b0c3,0x62165865a0c300a63c,0x780003e64000c9100340,0xd5201ac80dc961a2e1af,0x8ac62d70b64540580007,0x1c94000c6900042814a1,0x763e0002cc0caaa01000,0xa101b0cfc883a110e8f3,0x3c8a28bdda0dc94c1244,0x54bda591c07a61e80038,0x84da35a38e5e8c40d4a9,0xa0f800185f08a10c805e,0x20c6e9bf428000d08000,0xd45568fc000000a21512,0xb202a0000910002a5a33,0x451d12cc67131a15f9,0xf14003d060003c080,0x660e1950756660002058,0x5189851f2eb5418d0c6c,0x8a9a6bb067b49858c74f,0x5b973517d9fa3ca92753,0x8c0230011a3c463cadd8,0x9a80004d4538835cd164,0xd4de1163a8003c59b558,0x64ac11c00053684670ef,0x512fc70f0069bf0e4721,0xa9a5f4450a4e306ac2d9,0x1567de149482a9d431b0,0x750006823a6855bac7f8],#[0x1950b3a7892df2374883,0xa642ae68dd812682c2bb,0x8456043893d2f09d1a28,0xb05f240e134d5718b443,0xc91cc688a3979ff88b4f,0xcca1c00021840801189b,0xaff9510153810004a254,0x4efca1c0d104f4209163,0x5a94001107312a1b8,0x893e000d523d1f90c990,0x300009f242ce38f2881f,0x400100ef27000007955,0x99336983c00107b8bbb1,0x89c2bac2914e915a28ce,0x407721ee60000298e127,0x4248000000000786d2f8,0xe653b3b1d010ff919000,0xb78bb88a5434876174c9,0x708c4]]
set_option maxRecDepth 16000 in
def g255D10 := limbs80 #[#[0x7bf26c3ac13df9361d10,0xdaba2e2a0fad59161506,0x7f28c3ac3cf5765c561e,0xfc9b01bb4f7e4d80dc67,0x30ca0221ff171501109e,0xb8ac0886fe61d404437f,0xecb0221bf98458110ff8,0xbac0886fe61d60443df2,0x6b8221ff1715c110bfcc,0x2e0886fe61170443fb72,0xb8221bf9865c110bfdca,0xe2887fce4171442ff72c,0x8a21df7745c510efaba2,0x28877d5d9714437eb08b,0x221bf5865c510efbbb2e,0x884ff661744427fb30b2,0x217f990dd1109ffcc2e8,0x84ff66374442feb23ba2,0x13ff97611109ffcb3088,0x4ff661764435fb0cbb22,0x7f990dd9109ffcc2ec88,0xff66376442feb23bb221,0xff97619109ffca30c884,0x7e4d874437f720c3a213,0xf9661d109ffca30e886f,0xe4d70582ff722b82c13f,0x765c560f7cbb2e0b07f6,0x43715827ff30b8ac1cfd,0x6dc560e7ebb6e2b05fe6,0x1765827fb31b8ac16fd9,0x61d60dfdc830eb07bee4,0x415c37bf26c3ac13ff91],#[0xc570defc1ac2b86f7e0d,0x15c37bf06b8ae17fb905,0x5709feca702b86f7e0d8,0x5c37bb0dc1ae13fd96e0,0x70deebb706b86f764783,0xc2ff720bb2e1bdd96e0d,0xdfac0a83b84ff647865,0x37eb02b0ee13fd985077,0x9fecc2c3b86bf61961dc,0x7ff2cc0ee13ff9460770,0xdaba2c2a0cffe4586dc2,0xeb0eb0a83ef57658541f,0xaba2e2a0dfd65d615077,0xaecb8a83fb7945c541fd,0xc32e2a0f7ddd971507be,0xcbb2837f7965c541dfa,0xc2eca0e7f61d765075fb,0x3bb2833ff985d9419fec,0x6eca0e7f61f76506feb2,0xc3a833ff9061d419fecc,0xe2b0cffe59875077ef22,0x8ac3df5745c561f7ab22,0x2b0dfde5171587beee8b,0x2c3ef7965c561f7abb2e,0xb0f3f5d9745875fb0eb2,0xc33ff985d161cfec3ae8,0xf3f5db74586feb23ba2,0x39fd87dd161b7ecb6e8b,0xfbde45765867fb31ba2c,0x3ff9061d61b7fca2ecb0,0xef251875877ef22c3ac3,0xff9461d61ddfca30eb0e],#[0x7e4d805c75ff2cc3ac33,0xd96e01719feca700b8df,0xe45745c6fef22ba2e33f,0x86dd171cffc32e8b8f7d,0x43845c6bfb2dba2e39ff,0x6e1171cfebb708b8cff6,0x5765c67fb2dc22e39ff7,0x5d971d7fc32ecb8dfde4,0x765c6bff28bb2e3df791,0x1971afeca6ecb8f3fe19,0x65c67fb21c32e37bf946,0x3719ffc8309b8cff6538,0xdc67ff2cc26e39fd7661,0x719ffc830db8d7fe5176,0xdafbf26c02ed3ff9461b,0x6bdfca302bb4ff647805,0xa7fb29c0aed3fd90e057,0x9ffca303bb4ffe4181dd,0xff2e8b0221ff97650110,0xfcba2e0887fe59170443,0xeac8b8a21ff9765c110f,0xaca2e2887fd5d171443f,0xaecb8a21ff7945c510ff,0xcb2e2887fd65971443fe,0xecb2221fbd7459110ffb,0xbac8886ff61d64443dfa,0xcba221ff9905d110bfec,0x2e88877fdd974443bfae,0xba2217ff965d110dfec3,0xe8886ff661744437fb0e,0x22217fd96dd110efebb6,0xc887fe641764437faecc],#[0x221bfd875d910bffca2e,0x886ffe61764437fb30bb,0x21bff9461d10bfeca6ec,0x7fe505705837ff2cc3a,0x1ff57150560ffcb8ae0b,0x6ff61d41583dfaeca0ac,0xff9905c560bfecba82b0,0x7fdd171583bfae8b8ac1,0xfd765c560bffca2e2b07,0xf661715837fb0eb8ac1e,0xd915d960bfeca6e2b06f,0xe4587583dff22bb2c1ef,0x7150570ffab0a82b86ff,0x19415c3fbf06a0ae1ff5,0x750570bfecb282b86ffe,0xd615c3feae2b0ae17fd9,0x58570f7eb22c2b87f7e0,0x615c3dfaecb0ae1bff84,0xc570efeba2e2b85ff65d,0x15c3bfaecb8ae17ff945,0x570bffca302b85ffe597,0x5c3ff720bb2e17ff9660,0x70bffc8b0cb85ffe4576,0xc37fb0ca0ee1ff561507,0xf7eb22c3b85ff65941d,0x37fb28c0ee1bfd845877,0xdfec8b0db86ff65981dc,0xfeb20b8a83bff9161b70,0xfabb2e2a0ffde4171507,0xef2cb8a83ff5965c541f,0xac8aeca0dffe4176507f,0xb30bb283bfd875d941ff],#[0xc86eca0effe61765077f,0x20c3a83bfd9061d41bfe,0xb30ea0eff659875077ff,0xb8ac3ff5905c561dffc,0x2e2b0ffd5d171587fef2,0xba2c3ff7945c561ffaca,0xe8b0ffd64574586fff20,0xa2c3efd965d161f7ebb2,0x8b0eff661745877fb0eb,0x2c3efd905d961bfec86e,0xb0fbf65176587dff20bb,0xc3bfd9061d61f7fca2ec,0xeff651875877ff20c3a,0x3fdf9360171dffca30eb,0xf7fdd1805c7bfae8c02e,0xbff8460171dfec2300b8,0x7f5d9805c6fff28c02e3,0xfd8660171effbb300b8f,0xfe59805c77ff0cc02e3b,0xd84e0171efeba700b8df,0x5db805c6ffb29c02e3bf,0x96e0171dfec3700b8f7f,0x53805c77fae9c02e37fd,0x6e0171dfebb700b8eff6,0x9745c7bfaecba2e3bfd9,0x5d171efec32e8b8effe1,0x845c7bfb0dba2e3dff86,0x1171ffbc8b08b8dffe41,0x45c7bfeecc22e3dfd766,0x171dffc3308b8eff6198,0x5c6ffb21c22e37ff9661,0x71dfec3708b8f7f5db84],#[0xc77fb21c22e37fd96e11,0x1dfecb708b8eff5db845,0x7fef22bb2e37ff905d97,0xefec82ecb8dffe51765c,0xbfb28bb2e3dff905d971,0xffc830cb8f7fe51765c7,0x7928c32e3ff79161971b,0xfca30cb8fefe51865c7f,0xb29c32e37fd90e1971bf,0xca70cb8eff643865c6ff,0x2cc26e3bfd9061371dfe,0x82edb8f7f64176dc77fb,0x8bb6e3dfd945db71effc,0x30db8eff64186dc7bff2,0xc36e3bfd9461b71dffc8,0xbb7fee01805db7ff28,0x2edbff8160176dfec0b,0xbb7f7e4d805dafff22c,0x2edbff81e0176dfec0f0,0xbb6ff647805daffb23c0,0xedff78160576bffc8302,0xb6ffe11815db7fb08c0a,0xdfbf9460576fde4a302b,0x7bfe59815dafff28c0ae,0xbff84e0576bfec8702bb,0xff643815daffb29c0aed,0xfd94e0576dffc8702bb6,0xf64181ddb7ff29c0aedb,0xd745c560dfeca303bb6f,0xe5171583ffb28b8ac1ff,0x8650570ffebb282b87ff,0x11615c3ffae8b0ae1ffd],#[0x65c570ffeca2e2b87ff6,0x5765c3ffb22bb2e1ffd9,0x5d971ffec82eca0fffe4,0x805dbffb02c02edffd90,0x576fffc8b00bb7ffe05,0x33c04500450001ffd90e,0x462078c0ca815902280,0xa036f06660bb81590276,0x3ec25f847108580fc01d,0xc4e17642ce856a0a5c1,0xd87b60ed01c44366067e,0x62849988dc112e21483f,0x15c62a7852389f9138c2,0x50c4518242f585bf8b28,0x7f86d80d7d1a5e338464,0x1ed23c9076f8e9a1c983,0xe90ef2142414c8028fae,0xb54943923923c4465089,0x286e4fc89d6935f26464,0xa15c62aba543ca69947c,0xe68ba196fe2d725964b0,0x329a636cc4698362fe25,0xe1aee35406924cf49992,0x428e551c4a37d46e4cd9,0x3d9e79e0f109dca3b0a7,0x5a08b407a7f74fc79f2f,0xa9d12821f04344852d07,0x48b490311e3a35e45fc8,0xba5e94b1294ed276a49f,0xf613c0a7214da69a1531,0x5304a4ad46ea87d50709,0xf2b4755e0aa41513a9c7],#[0x58d681acb558bcaff95c,0x5e1abad972fae115b74b,0x2b0a560aec0017d92f6d,0xa2d91a31ef6354c57188,0x67eccea19b1b31565a0c,0xeb5586a26d35da40343b,0xbd9b5d36756c4ed7adac,0x708ce029bde376e6e52d,0x239967290e40dc5ab882,0xcf5d733aa174b8e881cf,0x79bcf21de183be27716e,0xd3e9a7c98f78decf3d2c,0x1de0193fe47f2cfd45f7,0x83e9069a0b5411381790,0x6439586b30c521634266,0x67e2a444f1895911561f,0x8e4b1b5e340463b8bdb1,0x3c8a290731fd23dc476a,0x94a50b49c8930724d647,0x978d2e06599cae5952f2,0xacd799a57330a635cc1d,0xcee7724ea89cb537ea6d,0xa1b942168174fe09f373,0xa5298a49547868c55133,0x146a0653d0a6f34cae96,0xabaf564aa9dd4f6a9515,0xcd754ae0d5abeb35561c,0x3eec5b585fb0595f9ebc,0xb485681ace0d985b26f6,0x8dbdab7076cd6d6f5a87,0x726eb95d1bb98971b6e1,0xbee77c72f62de77bc417],#[0xf60e7c15781770035fca,0xb1313b6228c3d9867b09,0xc85f8f871c9e34ec6018,0xae5becacf946726ee47d,0xf233b4671acd8799fb30,0xd2d3a42745de86dd02d9,0xcead4d51fa94f502e9c0,0x1ef616ebdfd735ad7b58,0xdc15b6ab6b2ed0ed981b,0x66f87de85bbd37536e4f,0x4bb87970bfe107c08f7e,0xe533c953907f1c1e2f9c,0x773e9e749cd7f99672de,0x7c0e10507e93bd1aba1,0xc360f81c20a0fc6e2e13,0xc220ce0707840f1f8bc4,0x703f1b87c0e0f08183f0,0x878c07e2f0f83c0e103c,0xf81c2a19147e1f0781c2,0x7e070a86471b8a08c241,0x385c10c8fc5e20230d0,0xc085f0b821918122b85f,0x91f090be070b82191813,0x3032302457c0e17061c1,0xc2e0c24323f021dc2e0a,0x7021dc2e08646070e781,0x6c7a37038509e08646c2,0x90d11410c82781c21c8,0xa3032371883c50970385,0xbc0e142436281f81c2e0,0x1b140fc0e17051e19198,0x70b822b0c8cc6e070a12],#[0xec5e070b8239849009e0,0x342419c0e17043248748,0x47c045f07841920401ce,0x6370385c11cc24703c10,0x38b0907f0385c10c9247,0x41070385c14706481187,0x1a8b84e070b82191c0f0,0x6c1d1709c0e0f08324d,0x81a8bc044f0784191c10,0x6492084a8bc0e1224363,0x48702bc6a2a2781c2e08,0x1006a291c25c0e170512,0x22c140ec6e070b822218,0x70b82890c91c0e17043,0x9c0e170432481c8c39e,0xe170512191c118302d1b,0xa8dc0e12243638168dc0,0x5a322781c2e086492084,0x1c25c0e17051248702bc,0xc5e070b8225181005a31,0x10c8fc0e1704322c1432,0xaf8417243609e00af85c,0x32849109e3714021be00,0x8e612404b8cc5e070b82,0x50e0d8a1202b1b81c2e0,0x204b81c2870688627038,0x33c407703841b238a41e,0xe2d1381c2e0a388a0f14,0x689c04770b82191c3847,0x72084a89c0e123836381,0xc8fc54703f81c2e0864,0xb828e278b444770385c1],#[0x10c900802d108e12e070,0x4324710640e18f0385c,0x2f87101b18f101dc0e17,0x7082e404b8ac4e070b82,0x7c2a61201e2f10370ee0,0x153c80bd111187e37030,0x841b242e88c3f178183e,0xa1083c0f16881217703,0x82e44738dc5a260f81c2,0x20d900ae37143309e070,0xac3630802cc5e351381c,0x8ee07082e401689c0e10,0x70384890b8e10e2f1032,0x8c6c1f0384141f8dc50a,0x2f111dc0e10502e3f178,0x346e204863c0e106c9e,0x840144146e070836320f,0x116150e21f07c0e17049,0xc035110f4511f038383e,0x710f83e070b824f203a1,0x3843e0f81c2e093c70a8,0x150f461070385c1c194,0xcc5c1f0385c10e0e1ca2,0x48158d83e070b821c1f8,0x89c58388307c0e17068c,0xe8bf860ce0f03850f25,0x463c307f0781c2860e24,0xd0a8eb860ce0f03850f2,0x5471c307f0781c286101,0x1ce370c8fc0e0f081860,0x70385c10e0e191409c3a,0x6c6e0f03850c278dc306],#[0x7f0383c28614381891f8,0x81c20c12230c87386470,0xe14308170642b47e1f07,0x3841820461ce1b1b81c1,0xe12309188668fc3e0f0,0x43048e88e31e1d1b83c,0xc2282a08090eb87c0e17,0x2a12a3f0f0b84e0f028d,0xe70e8c47e0707848c28,0x8fc3e0f038418283215,0x1e051b84303460230e87,0xe1d0e0542585c211f87c,0x1d240cc3e070b830c0c8,0x12300671b8623e070784,0x118c025c36370781c286,0x382ee183f83c2e02449,0xf23f0d8bc1e070a1e508,0x1c19c1e070a1e5074702,0xc2e0f021e4080321ce19,0xf001fc21c14200e70d8b,0x3c20e10270cf178647e0,0x17021850bb8bc307f038,0x1e5080391107f0c71c1e,0xbc3a3823f0e8bc1e0709,0x3817f0e8bc1e07091e48,0x70f0986e0707841d208e,0x9c3a291f83c0e123ca09,0x384783c0e123c90c8543,0x8fc1e07091e48c433c32,0xe0f038418285419e1d14,0x3848f2c70200e23c8fc3,0x8a838150911f8745e0f0],#[0x3c81970c1fc1e07085e3,0x191c3f47e1b1783c0e14,0x70870401587c0e17061e,0x1c2879015e283f87c1e0,0x70a1e40546fc362f078,0x81c28794201bb1787c1e,0xe10200b51c25c362f07,0xc28470c1e381070383c2,0x14611c6e2e1287c0e10a,0x51e40480c32a1f0385c,0xc20e9412028e287c0e17,0x92190aa1039c3e370383,0x1701d09c315f0383c20e,0xc541ce1e1383c0e1144a,0x36351781c1e10707180a,0x1c39c36370781c28615c,0x45e070913c10c902b150,0x70ca3c2e0f011e48200d,0xac6e070b821c1c642b0e,0x970e8bc2e0f011e570e8,0x8dc1e0708645890401c0,0xe1070a0a87033c54270e,0x9188648c2ee2f0f81c1,0x8ae0e84e1d1b83c0e10e,0x7071770d19c1e070a1e4,0x30bb8bc3e0707841c285,0x86c5e0f03850f2862072,0xe0f03850f24561f0e873,0xb82890c90c51061c5dc3,0xe0f091850200b46e070,0x42448c02c1c0970e8dc,0x8f240cc3c241e8bc0e17],#[0x9007190778745e0f0384,0x4484b86c6c270385c10e,0x43f46e1b1709c183f038,0x561e120f46e070b82122,0x17878483f0781c2a3140,0xc4c350f81c20a0e16093,0x145f43e070b828f238b,0xb871970f83c0e143c909,0x2d1381c2477043240e58,0x25c3a270785c04894080,0xa270385c10912200b61c,0xb81c2e0870802b0f0d07,0x2e0c2e12191c25c362e1,0x385c187424323b1b81c,0x1b0970b8109e08e4962f,0x86613c0e106c723b458a,0x1410cc2781c20d8e47a0,0x3b14a219e170383091c9,0x88c80386781c2e0c2472,0x82b1c4e19e003383c284,0xc24723b1781c2e0c243,0x85c18489c90386781c2e,0x84870563314320f10703,0x785c0e0e24723f0385c1,0x928f0b81c1c48e470c94,0x468a12c1f0b81c11c901,0x454404b85c0e0e247230,0x91c8e1b05a2781c2e086,0x471219190d45e070b838,0xc0e1704322c1781c2e09,0x9218c12e070b8389178f,0x9080c8528bc0e1705123],#[0x191844140cf0385c1448,0x70712191b81c2e094712,0x1c0e1704322c168bc0e1,0x386c1c19e070913c11c9,0x8e486284b81c1e162462,0x2392032140370385c144,0x48c86128510a89e070b8,0x85c1c486460cf0385c14,0x62f0385c10c8ac7a3703,0x612c6e070b8219158f09,0xb6204a37c0e17061ccc2,0x58ac40cf03850e0d901,0x230e06781c2e09331c4d,0xc433c0e17051d4c2306,0x89b0970385c1475309a2,0x184899c0e0f0b1c48c68,0x1dc0e1704322b2306301,0xe07098bc1a2638c0d825,0x31c191c3a1cc18ac5447,0xa27071c5e0f81c2e093,0x6480b41f062b0931785c,0x19280fc5a270385c1470,0x5c1442d1689c0e17051c,0xa21433c0e17051c2024,0x30744e070b838e0c8e25,0x80cb1471c0e17041f0e2,0x1c33c519703850ee0a24,0x9e3b138bc0e17061c19,0x22626c9c3e0f81c2e093,0x313448670d810e60f81c,0x9b1a88810971b07c0e15,0x70b82582288c6e070a98],#[0x1c22626cc0d04b0f83e0,0x8601d0e04b0d812360f8,0x9c2e070638e07089e9b2,0x4b8b83e070a9e9a20381,0x87c1f0b81c12893c7408,0xf4d934462f03854f4d8d,0x6cb0ce1703831c703844,0x961703831c11781c227a,0x3a1ce07098b440d921c0,0xe322f81c20e46c7c3604,0x70238e07098d440d9381,0x11723b81c20e46c90e61,0xd8bc0e10486846148b8,0x46c1f0384121a11c1e36,0xa0c65c0e106c62391782,0x232e2d1b81c244c6c9c0,0x1d1b8bc0e104a36404b0,0x7c0e1704984fc38fc1c,0x2351307c0e1706983123,0x7e1c7c1f0385c1c39606,0x8383a79783e170382512,0x1c49440f8758a87e070b,0x40407707c0e0f083823,0x11c100662e0f81c2e087,0x46438718ac4c1f0385c,0xc28608c803b1307c0e17,0x7051638184e1ae002783,0xfc1e070a18311e0fc0e1,0x7f0781c28605470470c8,0x87c1e043384230e11c30,0xc230f81c2e0e3062431b,0x41fc3e0f03848c188e12],#[0x923d1b87c14670384312,0x6429c30c70385c118901,0x840cf0f83c0e12305248,0x5188fc0e1705878c2c0d,0x7c0e0f0846416b081a09,0x30f85c11d0c12114318,0x8618e0f0384151d0e12e,0x670f82c6e070846302b,0x441c0e17061e27203a1c,0x983f0385c1470e060d02,0x778647e0f03850f178e0,0x150670e1fc1e07087050,0xf0785c0878704038e83a,0x58461f0385c1c78bc8e1,0x1833828fe0708482f242,0x8fc1e07091e2f1c121de,0xe0f03848f0f8bc90ef0c,0x68bc0e10bc7048778611,0x2e08602c2f241e47e1f0,0xb82c3c796190a70f81c,0xf20b5840d04a8a47e07,0x8e066286871c0e17041d,0x1c21c8e0903f0385c144,0x143c62407423c3c27078,0x85c1101207e1b1783c0e,0xe08e06093144b0f61f03,0x781c20a8e870970384c3,0x1e070a1e201c13c30c70,0x8381c20d88c80e70d8bc,0xc0e1706122b1c2509208,0x8b81c2e087056486d8b,0x9c0e0f0a12231c341442],#[0x5c2781c2e08705638491,0x34c5e070b8309170ac80,0x6491837c0e1706122b1c,0x34144209781c2e08705,0x7093151fc0e170612202,0x18900e84f0385c10e0ac,0xc7038698c2be070b8309,0x2e08e050387381c2e092,0x1781c2e0d0c704f0097c,0xc0e17049c381c3a1cc23,0x3149dc0e170470301c39,0xc1cc231b81c2e0d0c704,0xc11c0e19e070b824b1c0,0x7049c381824c5e050f85,0xd43e070b82381c33c0e1,0x2f0709c0e10e47048498,0x87c1e0708a22e2586c6a,0x47f0384201c10300c873,0x781c20e0ac5c4d0e8bc1,0x1e07083820240f436370,0xb82c31d0c1947f0c31c,0xce0f038423171219e07,0xc3383c0e10e091807386,0x3c0e10704648e846c6e1,0xf038438243a19e18638,0x842318123a0a91b870ce,0x118c090e04787c186703,0x56407786c6e0f03850c,0xc15921a0a22781c2e087,0xe0903d15868fe0f0b801,0x48738651e0f011fc2100,0x3345e1f0785c04787040],#[0xe322513c0e1704382b18,0x210190e14787c1e17011,0x70370f82c6e070838201,0xe070864486781c2e0a24,0x91831283819e1c1d09c1,0xe205c1983c3f87c1e070,0xe066286c71c0e1707084,0xc21c8e0803f0385c1448,0x7091831238651c270781,0x5c1618e0603c3f87c1e0,0x7f0781c20a8e080cf038,0x830fe07082a371c39c30,0xe1f061fc0e10546e470f,0xd8bc1e070a1e20171045,0xa0a70113c2e087056470,0x1b868ce0f03841c11941,0x89e070b821c158c1d0cd,0x87386c5e0f0384231810,0x414c212f81c2e0874484,0x270ca3c1e07082c1d243,0x8ac3e070b830f0c9619c,0xe170586321c64250d051,0xf83c0e106064486709c0,0x1e043f8429203a1928f0,0x385c127064a0cf0d8bc,0xc10c8ac8190682984e2f,0xf0b802b240e4661f0385,0x50711901d0cf0ca307e0,0x170462406786c5e0f038,0x85c187141b0c8c81dc0e,0x24931b095158a3847f03,0x478d84865c58770385c1],#[0x90d901a6270385c1870e,0x47031078bc487703841,0xc2e0d0c643b1493c0e17,0x70385c1a18e070931381,0x4c4e050f85c11c0e1c62,0x311c33c0e17058638182,0xe470470c1e32e0f0384,0x1c21c11c322f0689c0e1,0x7086e38c689c3267078,0x83c0e10dc818c3f87c1e,0xe07098a3224624587f0f,0x384311c0e1c0cf0e1fc1,0xe17051c19281fc3e0f0,0xa88291c641a0a71689c,0xc2e0510644f0f82c5e07,0x70b828e203a1948f0f83,0x5c12489c8090cb8b44e0,0x70840321c2586107038,0x82c5e07084e3f0d8bc1e,0xe012785c10e0809e1e1b,0xb81c1e10543850682986,0x5a263832307432c5e1e1,0x183819c713046281f064,0xc983120381962d131c2b,0xb0923878611a8981c1a6,0xe09e2f4d903126513829,0xc14d849163d1307810e8,0xe044e1cc1930717d106d,0x2c5c089c3983278e1d0c,0x8872361962e049f83203,0xc718391b031b14a2451,0x3840c93872dc1f08c127],#[0x2d04628f870e310d0518,0x531ba08661c491a36196,0x344470dc18db10330e14,0x294db043]]
set_option maxRecDepth 16000 in
def g255H10 := limbs80 #[#[0x1028081c01388001e00,0x30000180800204601006,0x142a0017004060c00008,0x607c2027008040001010,0x11a004000f1b000540a1,0x4540580c0c4203014840,0xc045d00014260330004d,0x1c0607010000e0000,0xa0041800061e4a02f0a,0x5021940e0b238a8660f,0x2d250100006240cc00,0xa402641a098601e09034,0x30485a1b2400c08301b8,0xa008001807030748c004,0x2a60d0084c060081c2e0,0x70f11d1f55448051682,0x9706c002e800060235a6,0x4c0780e0d0013c0c15d6,0x9699e0780b648247401,0xc21be87480c4001a34d2,0x19dbdd7773b000086fbb,0xc59c4c7e5b246b5a3000,0xda000072d40d02ea671f,0x23a3477b00031940002f,0x3823c8ac18770eb59,0x13217000018970010221,0x946b46139c093348702e,0x380be197006c12038a14,0xebc57dfc3010431a2d5d,0xe9d6083ccf2b2ec983bc,0xf96c8c662aa585415f2c,0xb8b08fe37570585e8316],#[0x38d4f4d46d9378ad45da,0xd044290644f1d9d347a0,0x61c0b17b0f5583f53a57,0x6f3ba981acaa07215655,0xdc46f4c73d1f0043f528,0xb538750ba2415229d397,0xc318a190002c6a003ed9,0x7359e35759aff86db069,0xb5d65120513be7ad7ea1,0xb38200a1cf9d7200006f,0x358241094fa767d77a54,0xfb8d91548962f88957a0,0xe80e3a1793105f9f47ac,0x699e8c8407afcee58598,0xee0caaa2af461dafb8c2,0xb7aa25113c95f0e7cfd9,0x96bb618d7d12fd6b8c26,0x3f8640048886561a50cf,0x88e5e759074e4ea78389,0xe104e4825126643d3b6d,0x94cf8f8a677dfa57430a,0x615e0a8a2fdaa345637d,0x1a825e36ecd4cba296b3,0xf9b9e2ccd7897d6de01b,0x560b56100e336b774c28,0x8f95b40ad5b3f15d3092,0x9aa5fc2282c7a2993793,0x469d1b4a55d0bbd48c19,0x72c4681be8cddf7f3467,0xb2c5cd42a5a9742182a5,0x2b2e067000040c6dd88a,0xf4200000008dc292f221],#[0xe500000007cae52de542,0x383f16d07f404d1d27ad,0x34000031575d7d05edf,0xacc7dfb1f79c3c3378a8,0x29df0e0d60ee000319fb,0x741682e25540b6608567,0x5779c8c00000e6d5d,0xcce62444dbe934dcd4b8,0x856365933be70a0e0f31,0xa03383f241f26bd4650e,0x20fc124837cb7b140000,0xc61a83a93e2f6746a083,0x409fe43a22e833d4c3f5,0x9dea9b7f4d80008ae,0x636f966c4b750a0eff80,0xf406fdd3c248ca26b735,0x610000a5ec000dcc4c2,0xbb8000045950d4052487,0x724c90057f8e13ab10f1,0x3c1a065f0be00014cb02,0x3f642c3526e3cc000000,0x6a0ee4d33d71e0c0003,0x7b09b096eb6867500009,0xf3611ef82ff510d1e776,0x71b55ab59b89d8eb8e32,0x24000b0ae6a8c2d89243,0xe06e00029f2de841cfa7,0x912a5f40000000000df6,0xb93658000247c000049c,0x4a8f846a0d81539645c,0xb7c7afec47615e524400,0x285d34f8258a94008000],#[0x1d69b2f1d11b203c089,0x7ce764b044b9a2837c00,0x8b9015d098a276d69dc,0x5a1062d0691b28d717,0x13483853b1ad22a1da00,0x2286eb2c7b9b4f118,0x188000363f9dcf299d35,0x839e4b6ba6ef0002401a,0x782cc7da02063cb8b471,0x2690e94fcdd6cc2fb72f,0x257c4f60000cd6a1d2,0x84367dbb9b0348600000,0xd38d000cebb0b99b,0xd4109aa518051dbdc000,0x8e55b666b83d24724ec1,0x8000dfca983fef60214f,0x5e1a3fcd14d1e1121133,0x850000000a81ffb25e9d,0x6e58a5ce4618d2912bce,0xe633bf36297f634c0707,0x7880290001ca70000a1d,0xeb14df35d4948cf6fa3a,0x2418000241dc6d6b2786,0x28c653918ad5089a1000,0x13000362415b27be37b6,0x325cdc75916cad7e5cad,0x20c8549f40de1a000243,0x37d0c54ac9ea13168f7,0x6d027d5bb167c55b9ee3,0x6944cbd8037960152ae2,0x25380b7b4156c4c45c41,0x93e32a63f5e77d3e44ca],#[0x1bc665653ea2ae00010,0x41cbeeb2974000950307,0x28710002d3f515d517,0x9e3c9000088f0e373e40,0x7aeda4c0369838048d17,0x72961f949816c03c7510,0x6d95a8000b028e3a0003,0xc552edbfb045164aac04,0x85200015e6f507cc,0xd7a40008e8984a,0x7400058f5e7357135a00,0xba110002102000000081,0x14c2ca8f8b25d,0x68f10155c2f4c5ab0000,0x3c4f000299ec7b01,0x21984efe712999000,0x1b0000c1fc39c0000000,0x8000d37d0d5069843e3,0xf4a1ce5a29057f57,0x8995b1c3c80b6,0xc712cb48a3bf467b0460,0x15eb01f000379043900,0xb304cba88880000001cc,0x4f46ec0003943f7ed57e,0xd61bcd23800000020566,0x55afa07105f851d8f012,0x85a0000047c01eef8451,0x1c81df6660001951b00d,0x471ec0005a4d2314a54e,0x2559a4051f88a9786,0x7765df0000000870763e,0x8]]
set_option maxRecDepth 16000 in
def g255D11 := limbs80 #[#[0x58110ff940442f7e0d70,0x443fd5c510ff970443fe,0xbfd87442ff61910bfd84,0x61d60efd76583fe5c160,0x5c3f7e0d70bff815c2ff,0xbfd86dc2ff60770bff86,0x61941ff571507fd58541,0x587fd5c561bfd87506ff,0xbfd87587bf5d961efd64,0xdd171dfd745c6ffe0171,0x5c77f5d971bff845c77f,0xbfd80dc6ffe1971dff76,0x61b71dfd76dc6ff61371,0xddaffe0576bff805daff,0xffd64442ff60776bfd80,0x5d910fff74443ff5d110,0x583ff50560fff76443ff,0xffd415c3ffdc560ffd71,0x60570ffd715c3ff58570,0xdc3ff61970ffd765c3ff,0xffd76507ff58770ffd41,0xdd161ffd74587ffdd941,0x5c7ffe0171ffd805c7ff,0xfff845c7ff61171ffd74,0xe1971ffd865c7ff5d971,0x5dbffe0176ffd805dbff,0x40230003ffe0576ffd81,0xe03e419c0a3042018408,0xb41bf0ce06042bc13f08,0x4c09e44bc23f11208043,0x6bc33b18a0bc45a42b71,0x21810347d43c71d20e04],#[0x4a0c4e326012648ec457,0x72f016f4b345772a814b,0xf4db46b33421954c5c60,0xdb3da1e24ecc7433901b,0x3b518488f43220d501c7,0x9eb4e026752e494348a2,0x443e362e26041e11142c,0x48e338d818582161238,0x184361240ce2e0616087,0x2e06160848e258d8b838,0x8c321781838412523e36,0x8c87606160849444180f,0xd8b818582124128783e2,0x2e260e0610d871024378,0x108f8b898185821c3896,0x4363090de2e260616087,0x2e260610d118d8a89818,0x8b888d818436300c1e36,0xe6362a203e06160c193,0x78d8b888c0f818583064,0x818384183e1e060e1060,0x83e1e060e10c0c8f8d87,0x1078e8f8d87818384183,0x8582221e323e2e1e0e06,0x23e2e1e0e061078f8781,0x1920a8f8b878381841e4,0x840943e362c2606160a,0xe106100f8d868b818385,0x185830840e636183e060,0x360e0614210398d868b8,0x860f8381841e403e2e1a,0x62e1a36060e14210398b],#[0x286038d8b0981843640e,0x38ee361c203e060e1229,0x6123118b860f8381841e,0x18582864e2e1c203e0e0,0xe0612210250f8b890d8,0x890d818436443e2e1c36,0xc303e060e1221286038b,0xe8b81858312a240e62e1,0x3e31ca2e06160c4930e8,0xe8c8b818583123240ea,0x2423e2a36061609cc490,0x647120e8a8d818583123,0x831c4c3a3a241e06160a,0xc70c9239068f8a898185,0x53698583a2c1a2606160,0x7963624890f8d0783818,0xd892243e2c1e0e0614da,0x306398d8a8981843648,0x646360e284e061090d91,0x90d9103078b888d81843,0x830e98462e0e20760610,0x6160c3a790898d078185,0x68d8381851852262c1e0,0x60e123c612620f088f8,0x8b8381851e60cc261a36,0x23c7925e543a0f088f86,0x2561258cc261a2e0e061,0xe14625e398d8a3781858,0x61703c26362e06160a18,0x5f8d860e8b098183845c,0x636198e060e106143a38,0xd87808b858238498438e],#[0x3a360c260611c160f098,0x5f8381841e5988e62e18,0x60e10e148a710e398b86,0x5821c41703c262e1e023,0x160a1989436338b89818,0x81841e51943e262c3606,0x221912628b0f8b867183,0x43e2e1c360e061]]
set_option maxRecDepth 16000 in
def g255H11 := limbs80 #[#[0x61800702381860200209,0xc28408240021a2418a2,0x93030208002040c69212,0x1840010d035620d87220,0x25020008106081030a04,0x80218482000800114001,0xe0c205200c089000000,0xc081040c08708ec388,0x1018000082210a1c1050,0x84820000102020c09a04,0x38a12100040028708082,0x1000400263800440,0x2717626226e821888a7b,0x25e0b6820e1312d683eb,0x42d3967638411743bb2,0x457fc09d1f2ea8fab,0x58c9d20b2dabfa2b0000,0x47ad5bbab0645876c4d7,0x711827298f6c21c613d7,0x592048c1c000005a000,0x3ac5249d6c33229ee4dc,0x2e88e18f60d802b241a1,0x3bd09d55ac149f8108a9,0x25c0526b01560d5ad89d,0x672f44630a4949d326f5,0x3a4c000798160d000105,0xc36ab00000000000000,0x7994000411d26a7,0x40001a94000000000000,0xa761adc61c51e5f08817,0x1,0xa1efd017800000000000],#[0x8b3ab30a9d54b1872a8,0x1738001a67e22166b,0x10bf31ef2319a1e05e8,0x85a000159598088a680,0x8b2357ba7d59f8000000,0x2dc301a741914d5b526d,0x7a730666ad2a1ae91b1,0x4da00000ae7264821a00,0x2a990680000000001c3f,0x4a50499bb05b69e35661,0xe10a0825569462ad2af5,0x94698ffaa2c083838d04,0x6ca1fdd6d49da2738000,0x988956bd8000aa3a2026,0x3938000028666e0000d3,0x9e013380015208000000,0x100c5e0e00000000006,0x7ab600000,0x2857e144b13c85b10800,0x95c00007a8e120,0xa80000006a1847e80000,0x5266829ea5c00011bd6a,0xc780003ce2f840000000,0x7b7a78001a51d9a5c9de,0x1a4ab64a000428965962,0x5040e93b285e32ba0,0x5b800000070a0a1b1a46,0xf00008030001732ba540,0x3abc734000040b800168,0x2aea2a997d4408000000,0xe1ba129540000985ea5e,0x40004c2f254e8047bfac],#[0xeb79a80a670001140c4b,0x79f996913800000059e9,0x80000b3d0460005c7fe,0x3238e230000ba049fec7,0x440e91029968dc0e489a,0x1229516345e469de01f,0x783e000000103480,0x4b8c494e967d07170800,0x92600000002a32029,0xa086200048c518f88d60,0x8bf8000dac8001d5,0x10501ef1440005a7df6a,0xe16bc800000000000006,0x80007078f2cc5040003a,0x1808800153a209,0x10d043738e859f8000,0x4d42c488ec4f0500000,0x80000005234000000000,0xafa000000109e0000c8c,0x124b81b059f00000002,0xdf144eb6eac800000000,0x2905678712a033509ed7,0x2f12ea00020b8e4d6e16,0xd0000000027fc5780010,0x1600fa1681,0x410c0000000000,0x2378001ebb481b2058,0x951386600000,0xc92e5a365c203a653800,0x90a60c000000185cb9ab,0x125f85a6f53299a2,0xb845615b2512775cac00],#[0x9b735d8ab5407309173b,0x9a176506ed36b6ae0005,0xe0001aa0381000124a3d,0x26880000003c9c88b99a,0xa8000196f014cf18aaa4,0xfac5536e000000000001,0x2eed3079011a6,0x23ee4482f0d3098e7035,0x8886282ba25a951e0007,0x60000000000000000021,0x7af0001a2be09,0x97a132e8b2ef31780000,0x50000000181400041dfa,0x6ce400060480001c3fb9,0x84a00009b40005682000,0x600038399577e0b4503,0x4000000000000009879a,0x5d6fcbe45484496ae,0xae110000000044079a6,0x325ee0002de7986a07c5,0x8a2a00000000007a1ca8,0x94a1be0000256fefbf3a,0x20e0810,0x0,0x1f6e8001806000,0xc2280000001574,0x680000000000c26ccde0,0x31f0000115cc1700016b,0x9c40000000e98a4a4000,0x67f9674a600000000004,0x180e00074a867005,0x827f2c304c4e18000000],#[0x1bb83d643fa1202148ce,0xaf8004990000c42f9c83,0x8b622e8000000707f23,0x2290847aa5a000,0x560003d580005ad874d0,0x8c540001c3d3d5b50ce1,0xe582187cbb8001050857,0x713c0000001a4b0000,0x5000121a30f8d61d0ec0,0x605023c22d000011eb36,0xbec980000000,0x30000750b036ea3a0000,0x92338938155c68c9aba,0xa0280004a08000000000,0x1a53e95e6b862c71a1,0xd80000000ab800000000,0x620bc321983b51adde25,0x5d65f7322e8836,0xcd064355f6200001a2a0,0x213e000000000021,0x21d800000039f6000000,0x606000000017110000,0x5aa723c800122880000,0x32119ae98c0c07c41000,0x8fc420000eb1d1c6000,0x64dc0001]]
def g255D12 := limbs80 #[#[0x1ffee1ff5c3feb07fd10,0x76ffee3ff5c7feb0ffd4,0x3e0ba1d437003ffbb7fd,0x10a0891e2e7c1b25d136,0x71624085047101e3458,0x80f1a2c4820e04236487,0x610c22345880e042821c,0xe041843c80e12343810,0xf1a2c309020c2203848b,0x42223458612041841c80,0x41841c80f162430d060,0x22c4861a]]
def g255H12 := limbs80 #[#[0x904d010208002,0x35d00000000,0x204800000280000000,0x5158005110003888000,0x30680000000,0x0,0x19b0000000000000000,0x48980000000000000,0x5d9305000000000000,0x69a8000000,0x0,0x5d3000000000000,0x0,0x80000000045380000000,0x4160002cb00050d,0x84020006858000000000,0x38ba1300000009,0x0,0x2925978060000000,0x3c580000000000,0x0,0xf00000000010f8000000,0x5db00058,0x1c800000000000000000,0xa4038000000000000007,0x19280040c80000000009,0x396800000000000,0x2d68000000000000,0x5628d400,0x0,0x19f7c1518d890000000,0x4d800000000000],#[0x4000000000000458800,0x1220000003630000004,0x14180040c00,0x443000000000,0xb80021f80000000078e0,0x6ce79,0x49400039ec5c800000,0x3550a0800513e828,0x48100000000000,0x180800000199000000,0x300001d0000000007998,0x2a180068,0x50d601800000,0x82cd00030a8000002a10,0x3d700000000000068,0xed87800000000000217,0x40700000075480011dc,0x66000041c01500034ef2,0x7c3800,0x54bfd5b22bc70000000,0x0,0x7486c8a23,0x0,0x80000000000000000000,0x1191e61080035260b7d0,0x5948000000001900001,0x60a00]]
def g255D13 (j : Nat) := if j=0 then 0x185103001087ff else 0
def g255H13 := limbs80 #[#[0x2000e182128034c00800,0x70000001a00078f4200c,0x4a6500023fd6acd]]
def g255L : Nat → Packing
  | 7 => (26,6,6,0,0,9,0,g255D7)
  | 8 => (174,5,6,0,0,13,0,g255D8)
  | 9 => (509,4,6,0,0,16,0,g255D9)
  | 10 => (385,3,6,0,0,15,0,g255D10)
  | 11 => (71,2,6,0,0,13,0,g255D11)
  | 12 => (10,1,6,0,0,10,0,g255D12)
  | 13 => (1,0,6,0,0,0,0,g255D13)
  | _ => emptyPacking
def g255I : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 10 101 4 10 5 1 g255H8
  | 9 => lookupWord 60 277 7 13 8 1 g255H9
  | 10 => lookupWord 174 797 9 14 9 1 g255H10
  | 11 => lookupWord 135 809 7 14 9 1 g255H11
  | 12 => lookupWord 25 383 3 12 7 1 g255H12
  | 13 => lookupWord 3 23 4 9 4 1 g255H13
  | _ => fun _ => none
def g255 : Forest := ⟨255,13,fun i => g255Y[i]?.getD (0,0),g255C,g255A,g255L,g255I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P7_0 : block g255 7 0 26=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B7 : block g255 7 0 26=true := g255P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_0 : block g255 8 0 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_36 : block g255 8 36 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_132 : block g255 8 132 42=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B8 : block g255 8 0 174=true := (@block_merge g255 8 0 36 138 g255P8_0 (@block_merge g255 8 36 96 42 g255P8_36 g255P8_132))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_0 : block g255 9 0 23=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_23 : block g255 9 23 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_119 : block g255 9 119 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_215 : block g255 9 215 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_311 : block g255 9 311 37=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_348 : block g255 9 348 96=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_444 : block g255 9 444 65=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B9 : block g255 9 0 509=true := (@block_merge g255 9 0 215 294 (@block_merge g255 9 0 23 192 g255P9_0 (@block_merge g255 9 23 96 96 g255P9_23 g255P9_119)) (@block_merge g255 9 215 133 161 (@block_merge g255 9 215 96 37 g255P9_215 g255P9_311) (@block_merge g255 9 348 96 65 g255P9_348 g255P9_444)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_0 : block g255 10 0 8=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_8 : block g255 10 8 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_104 : block g255 10 104 56=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_160 : block g255 10 160 96=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_256 : block g255 10 256 96=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_352 : block g255 10 352 16=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_368 : block g255 10 368 17=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B10 : block g255 10 0 385=true := (@block_merge g255 10 0 160 225 (@block_merge g255 10 0 8 152 g255P10_0 (@block_merge g255 10 8 96 56 g255P10_8 g255P10_104)) (@block_merge g255 10 160 192 33 (@block_merge g255 10 160 96 96 g255P10_160 g255P10_256) (@block_merge g255 10 352 16 17 g255P10_352 g255P10_368)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_0 : block g255 11 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_1 : block g255 11 1 38=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_39 : block g255 11 39 32=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B11 : block g255 11 0 71=true := (@block_merge g255 11 0 1 70 g255P11_0 (@block_merge g255 11 1 38 32 g255P11_1 g255P11_39))
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

end PEqualNP.Outside.L_meta_34796

open PEqualNP.Outside.L_meta_34796 in
theorem PEqualNP.Outside.L_meta_34796 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 2, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 2, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o fit _ correct
  exact replaceShort g255R gates o fit correct

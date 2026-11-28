import PEqualNP.Defs

-- The two-mode live-state and cofactor checker follows L_meta_1674 and L_meta_670.
-- The graph, restrictions and all search certificates below are for L_meta_35030.

-- Shared forest and cofactor certificates from L_meta_1674 and PR 11111 for L_meta_1677.
-- The original credit line is retained below. The two root certificates here cover the unpinned graph.

-- The checker and the bound certificates are adapted from PEqualNP/Outside/L_meta_1667.lean (Apache-2.0).
-- Two modes: u=false are monotone runs (AND, OR); u=true are runs up to complement, where negation is free.
namespace PEqualNP.Outside.L_meta_35030
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
def graph : Sig := (BitVec.ofNat 512 (word80 [0xffffffff,0xffffffffffffffffffff,0xfffafffffffefffffffc,0xfffefffaeeeeaa00ffff,0xffffffffffffffffffff,0xfffffffafffffffeffff,0xfffcfffefffaeeeeaa00]))
def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 4) || (x 0 && x 5) || (x 2 && x 5) || (x 3 && x 5) || (x 1 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 4 && x 6) || (x 0 && x 7) || (x 2 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 5 && x 7) || (x 6 && x 7)
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
  (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 2 &&& x 5) ||| (x 3 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 0 &&& x 7) ||| (x 2 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)
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
  (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 2 &&& x 5) ||| (x 3 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 0 &&& x 7) ||| (x 2 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)
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



def target (x : Fin 8 → Bool) : Bool := decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
def smallCircuit : Circuit := ⟨[⟨.or,[5,7]⟩,⟨.or,[2,7]⟩,⟨.or,[4,6]⟩,⟨.or,[10,5]⟩,⟨.and,[9,11]⟩,⟨.or,[3,12]⟩,⟨.or,[13,0]⟩,⟨.or,[2,14]⟩,⟨.and,[8,15]⟩,⟨.or,[0,6]⟩,⟨.or,[13,4]⟩,⟨.and,[17,18]⟩,⟨.and,[1,10]⟩,⟨.or,[19,20]⟩,⟨.or,[16,21]⟩], 22⟩

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
def K41 := extendKnown [] 4 [(41,[]),(82,[16,67,101]),(137,[117,101]),(145,[67,117,101]),(161,[83,67,116,100]),(164,[32,16,83,67,116,100]),(168,[48,16,33,82,66,116,100]),(196,[32,16,99,67,117]),(208,[64,16,33,99,117])]
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
def K27 := extendKnown K41 4 [(27,[]),(51,[83]),(53,[33,67,83]),(75,[96,16,49,67,84]),(77,[96,16,33,50,67,84]),(85,[96,16,33,50,83]),(101,[32,16,99,84,67]),(113,[64,81,33,99]),(116,[32,65,83,97,49]),(120,[48,65,32,82,97,33]),(150,[112,32,50,83,101]),(154,[112,32,82,101]),(178,[112,32,83,50,99]),(195,[96,16,49,116,83,84]),(226,[112,32,83,100,50,67])]
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
def K45 := extendKnown K27 5 [(45,[]),(57,[48,66,80]),(83,[16,32,99,67,84]),(90,[16,50,66,101]),(105,[98,83,66]),(141,[117,101]),(147,[33,115,67,84,101]),(149,[67,117,101]),(180,[32,16,65,83,115,99]),(197,[32,99,67,117]),(198,[32,16,115,67,101,84]),(225,[98,83,66,115,67]),(240,[64,16,82,99,114,50])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V45 : Known true K45 := extend_ok (m:=45) V27 low45 (by decide +kernel)
def g153Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffe701fffc1f9f9ffe,0x701fffc1f9f9ffe701ff])),(BitVec.ofNat 152 (word80 [0x40012490841010040,0x1249084101004001249]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x3e7d0e07ffe01fe3e7,0xd0e07ffe01fe3e7d0e07])),(BitVec.ofNat 152 (word80 [0x891d2492508a4a0891,0xd2492508a4a0891d2492]))),((BitVec.ofNat 152 (word80 [0x3f8bf038ffffe003f8,0xbf038ffffe003f8bf038])),(BitVec.ofNat 152 (word80 [0x104ba492610c0c5104,0xba492610c0c5104ba492]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xc018ffc0fffffffc01,0x8ffc0fffffffc018ffc0])),(BitVec.ofNat 152 (word80 [0x200049248210100200,0x4924821010020004924]))),(0x0,0x0)]
def g153C : List ColumnInfo := [(8,0,145,0,4)]
def g153A : List (List Nat) := [[],[67],[112],[112,67]]
def g153D4 (j : Nat) := if j=0 then 0x1f else 0
def g153L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g153D4)
  | _ => emptyPacking
def g153I (_ _ : Nat) : Option (Nat × Nat) := none
def g153 : Forest := ⟨153,4,fun i => g153Y[i]?.getD (0,0),g153C,g153A,g153L,g153I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g153P4_0 : block g153 4 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g153B4 : block g153 4 0 1=true := g153P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g153T : checkedTables g153 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g153 0 0 0 = true)
  · exact (rfl : block g153 1 0 0 = true)
  · exact (rfl : block g153 2 0 0 = true)
  · exact (rfl : block g153 3 0 0 = true)
  · exact g153B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g153G : graphValid g153 (boundsBefore K45) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low153 : Lower true (varsX 153) (graphGoal 153) 5 := lower_forest (g:=g153) (i:=0) (hints:=3) (before_sound K45 V45) g153G g153T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K153 := extendKnown K45 5 [(153,[]),(165,[80,50,32,66]),(172,[80,16,33,50,67]),(177,[67,83]),(201,[48,100,84]),(204,[96,16,33,50,67,84]),(209,[64,48,99,83]),(210,[64,16,49,115,83,101]),(216,[96,16,33,82]),(228,[32,16,83,100]),(232,[48,16,33,82,100])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V153 : Known true K153 := extend_ok (m:=153) V45 low153 (by decide +kernel)
def g169Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xdf7ec03c3ffe0fbefd,0x80787ffc1f7dfb00f0ff])),(BitVec.ofNat 152 (word80 [0x820404444444210408,0x8888888420810111111]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1fbf43c3c3fff03f7e,0x878787ffe07efd0f0f0f])),(BitVec.ofNat 152 (word80 [0x40808888888420810,0x11111110841020222222]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xe03fbc03fc3fffc07f,0x7807f87fff80fef00ff0])),(BitVec.ofNat 152 (word80 [0x81011111110841020,0x22222221082040444444]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffc03ffc003fffff80,0x7ff8007fffff00fff000])),(BitVec.ofNat 152 (word80 [0x102022222221082040,0x44444442104080888888]))),(0x0,0x0)]
def g169C : List ColumnInfo := [(1,0,168,0,4),(8,0,161,0,4),(32,0,137,0,4),(128,0,41,0,4)]
def g169A : List (List Nat) := [[],[117],[83],[83,115],[115,83],[115],[48],[48,117],[48,80],[48,80,112],[48,112,80],[48,112],[80,48],[80,48,115],[80],[80,112],[80,115],[80,115,48],[112,48,83],[112,48],[112,80],[112],[112,83,48],[112,83]]
def g169D3 := limbs80 #[#[0x23ea6a1221e12148110,0x8028]]
def g169D4 := limbs80 #[#[0x2fd0910bd42443e48110,0x609085870]]
def g169H4 (j : Nat) := if j=0 then 0x22e else 0
def g169D5 (j : Nat) := if j=0 then 0xd1027d10 else 0
def g169H5 := limbs80 #[#[0xa00716920c004c5720,0x241410000]]
def g169D6 (j : Nat) := if j=0 then 0x3904f else 0
def g169H6 := limbs80 #[#[0x0,0x88274228000000002a0,0x281]]
def g169L : Nat → Packing
  | 3 => (2,3,2,0,0,5,0,g169D3)
  | 4 => (3,2,2,0,0,5,0,g169D4)
  | 5 => (1,1,2,0,0,0,0,g169D5)
  | 6 => (1,0,2,0,0,0,0,g169D6)
  | _ => emptyPacking
def g169I : Nat → Nat → Option (Nat × Nat)
  | 4 => lookupWord 1 2 0 5 1 0 g169H4
  | 5 => lookupWord 2 13 3 9 2 3 g169H5
  | 6 => lookupWord 1 23 0 9 0 5 g169H6
  | _ => fun _ => none
def g169 : Forest := ⟨169,6,fun i => g169Y[i]?.getD (0,0),g169C,g169A,g169L,g169I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g169P3_0 : block g169 3 0 2=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g169B3 : block g169 3 0 2=true := g169P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g169P4_0 : block g169 4 0 3=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g169B4 : block g169 4 0 3=true := g169P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g169P5_0 : block g169 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g169B5 : block g169 5 0 1=true := g169P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g169P6_0 : block g169 6 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g169B6 : block g169 6 0 1=true := g169P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g169T : checkedTables g169 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g169 0 0 0 = true)
  · exact (rfl : block g169 1 0 0 = true)
  · exact (rfl : block g169 2 0 0 = true)
  · exact g169B3
  · exact g169B4
  · exact g169B5
  · exact g169B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g169G : graphValid g169 (boundsBefore K153) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low169 : Lower true (varsX 169) (graphGoal 169) 7 := lower_forest (g:=g169) (i:=0) (hints:=3) (before_sound K153 V153) g169G g169T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K169 := extendKnown K153 7 [(169,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V169 : Known true K169 := extend_ok (m:=169) V153 low169 (by decide +kernel)
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
theorem g55G : graphValid g55 (boundsBefore K169) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low55 : Lower true (varsX 55) (graphGoal 55) 5 := lower_forest (g:=g55) (i:=0) (hints:=1348) (before_sound K169 V169) g55G g55T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K55 := extendKnown K169 5 [(55,[]),(103,[32,16,84,100])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V55 : Known true K55 := extend_ok (m:=55) V169 low55 (by decide +kernel)
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
def K59 := extendKnown K55 7 [(59,[]),(107,[48,100]),(115,[64,81,49,99]),(118,[96,81,32,49,66,67]),(122,[96,81,32,49,67]),(182,[112,32,50,99]),(186,[112,32,98]),(227,[112,48,100,67])]
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
def K61 := extendKnown K59 6 [(61,[]),(87,[96,49,32,66,84]),(151,[112,49,33,32,66,84,101]),(199,[96,49,32,33,65,117])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V61 : Known true K61 := extend_ok (m:=61) V59 low61 (by decide +kernel)
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
theorem g79G : graphValid g79 (boundsBefore K61) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low79 : Lower true (varsX 79) (graphGoal 79) 5 := lower_forest (g:=g79) (i:=0) (hints:=16778851) (before_sound K61 V61) g79G g79T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K79 := extendKnown K61 5 [(79,[]),(158,[16,32,48,64,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V79 : Known true K79 := extend_ok (m:=79) V61 low79 (by decide +kernel)
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
theorem g91G : graphValid g91 (boundsBefore K79) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low91 : Lower true (varsX 91) (graphGoal 91) 6 := lower_forest (g:=g91) (i:=0) (hints:=16777283) (before_sound K79 V79) g91G g91T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K91 := extendKnown K79 6 [(91,[]),(109,[32,16,99,84]),(121,[64,81,33,99])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V91 : Known true K91 := extend_ok (m:=91) V79 low91 (by decide +kernel)
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
def K93 := extendKnown K91 5 [(93,[]),(110,[80,16,33,50,67]),(124,[80,16,66,50])]
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
def K94 := extendKnown K93 6 [(94,[])]
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
def g155Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffc03ff0fffffc03f,0xfff0fffff5560300f0ff])),(BitVec.ofNat 152 (word80 [0x2028280a2020028281,0x40220020900603111111]))),((BitVec.ofNat 152 (word80 [0xffffc000ff0ffffc0,0x1fff0ff014b579000f00])),(BitVec.ofNat 152 (word80 [0x48b0322c41428b2325,0x9140284214b551bbbbbb]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffff000ffffff,0xe0000fff2bb5260f000f])),(BitVec.ofNat 152 (word80 [0x82c140b005842c0406,0x58442802b9120666666]))),((BitVec.ofNat 152 (word80 [0xf00000000000ffffff,0xfffff000134bf8f00ff0])),(BitVec.ofNat 152 (word80 [0x30180c08608300808,0x6000304034828444444]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffff000000,0xcea8c5fff000])),(BitVec.ofNat 152 (word80 [0xc0203000800c03030,0x18088c084420c4888888]))),(0x0,0x0)]
def g155C : List ColumnInfo := [(0,2,137,16,5),(2,0,153,0,5),(8,0,147,0,5),(1,0,154,0,4),(16,2,137,0,4),(128,0,27,0,4)]
def g155A : List (List Nat) := [[],[112]]
def g155D4 (j : Nat) := if j=0 then 0x5bd4940 else 0
def g155D5 (j : Nat) := if j=0 then 0xc8404fd40 else 0
def g155H5 (j : Nat) := if j=0 then 0xc0 else 0
def g155D6 (j : Nat) := if j=0 then 0x2b2a0bf else 0
def g155H6 (j : Nat) := if j=0 then 0x5 else 0
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
theorem g155G : graphValid g155 (boundsBefore K117) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low155 : Lower true (varsX 155) (graphGoal 155) 7 := lower_forest (g:=g155) (i:=0) (hints:=67) (before_sound K117 V117) g155G g155T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K155 := extendKnown K117 7 [(155,[]),(179,[83]),(203,[48,100,84]),(234,[48,32,82,100]),(242,[64,81,32,49,114,50,99])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V155 : Known true K155 := extend_ok (m:=155) V117 low155 (by decide +kernel)
def g157Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3ff801ffc07fe03fff,0xfffffffffff6ef4401ff])),(BitVec.ofNat 152 (word80 [0x805014028100408001,0x40500800101063409249]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x3ffffe00007fffc07f,0xe007fc0ff810c6bc0e00])),(BitVec.ofNat 152 (word80 [0x156298ab162a8a1515,0x8d6251a522d0c6bdb6db]))),((BitVec.ofNat 152 (word80 [0x3fffffffff8000007f,0xfff8000fffee16747007])),(BitVec.ofNat 152 (word80 [0x198320cc2433132626,0x98362c6448e14352492]))),((BitVec.ofNat 152 (word80 [0xc0000000000000007f,0xfffffff00003f8a78038])),(BitVec.ofNat 152 (word80 [0x1e03c0f0383c1c3838,0xe038307870398a52492]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffffff80,0x1911bbffc0])),(BitVec.ofNat 152 (word80 [0x200401000040000040,0x10040008000000024924]))),(0x0,0x0)]
def g157C : List ColumnInfo := [(4,0,153,0,5)]
def g157A : List (List Nat) := [[],[67]]
def g157D5 (j : Nat) := if j=0 then 0x3f else 0
def g157L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g157D5)
  | _ => emptyPacking
def g157I (_ _ : Nat) : Option (Nat × Nat) := none
def g157 : Forest := ⟨157,5,fun i => g157Y[i]?.getD (0,0),g157C,g157A,g157L,g157I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g157P5_0 : block g157 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g157B5 : block g157 5 0 1=true := g157P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g157T : checkedTables g157 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g157 0 0 0 = true)
  · exact (rfl : block g157 1 0 0 = true)
  · exact (rfl : block g157 2 0 0 = true)
  · exact (rfl : block g157 3 0 0 = true)
  · exact (rfl : block g157 4 0 0 = true)
  · exact g157B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g157G : graphValid g157 (boundsBefore K155) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low157 : Lower true (varsX 157) (graphGoal 157) 6 := lower_forest (g:=g157) (i:=0) (hints:=1795) (before_sound K155 V155) g157G g157T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K157 := extendKnown K155 6 [(157,[]),(206,[112,16,33,50,67,84,101])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V157 : Known true K157 := extend_ok (m:=157) V155 low157 (by decide +kernel)
def g173Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xff0ff01fe3f8ffe0,0x3fc7f1ffd675000f00ff])),(BitVec.ofNat 152 (word80 [0xa0a20a14148120142,0x82902402163411111111]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xff000fffe003ff1fff,0xc007fe3f317a00f00f00])),(BitVec.ofNat 152 (word80 [0x2c2c42c18590a04583,0xb214084b17a33333333]))),((BitVec.ofNat 152 (word80 [0xffffffc001fff,0xfff8003fede10f00f00f])),(BitVec.ofNat 152 (word80 [0x303083020600c48604,0xc01890829c122222222]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffff0000000001fff,0xffffffc01388f000fff0])),(BitVec.ofNat 152 (word80 [0x404004040801000808,0x10020010000044444444]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffffe000,0x2816ffff0000])),(BitVec.ofNat 152 (word80 [0x808008081002001010,0x20040020000088888888]))),(0x0,0x0)]
def g173C : List ColumnInfo := [(4,0,169,0,7)]
def g173A : List (List Nat) := [[],[117],[48],[48,117]]
def g173D7 (j : Nat) := if j=0 then 0x3f else 0
def g173L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g173D7)
  | _ => emptyPacking
def g173I (_ _ : Nat) : Option (Nat × Nat) := none
def g173 : Forest := ⟨173,7,fun i => g173Y[i]?.getD (0,0),g173C,g173A,g173L,g173I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g173P7_0 : block g173 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g173B7 : block g173 7 0 1=true := g173P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g173T : checkedTables g173 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g173 0 0 0 = true)
  · exact (rfl : block g173 1 0 0 = true)
  · exact (rfl : block g173 2 0 0 = true)
  · exact (rfl : block g173 3 0 0 = true)
  · exact (rfl : block g173 4 0 0 = true)
  · exact (rfl : block g173 5 0 0 = true)
  · exact (rfl : block g173 6 0 0 = true)
  · exact g173B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g173G : graphValid g173 (boundsBefore K157) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low173 : Lower true (varsX 173) (graphGoal 173) 8 := lower_forest (g:=g173) (i:=0) (hints:=1283) (before_sound K157 V157) g173G g173T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K173 := extendKnown K157 8 [(173,[]),(185,[48,66,80]),(233,[98,83,66])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V173 : Known true K173 := extend_ok (m:=173) V157 low173 (by decide +kernel)
def g181Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfe1ff00ff87f87ffc0,0x7fff8fffd8b95000f0ff])),(BitVec.ofNat 152 (word80 [0x1440a0a05101100285,0x5012008488941111111]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1ffff0007ff87fff,0x807ff1fc2b1e600f0f00])),(BitVec.ofNat 152 (word80 [0x5882c0c1620a010b06,0x160a0411291e43333333]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1fffffff80007fff,0xff8001ff941fb0f0000f])),(BitVec.ofNat 152 (word80 [0x610b0505802c222c08,0x182c48a01416b6666666]))),((BitVec.ofNat 152 (word80 [0xffe000000000007fff,0xfffffe000be4bf000ff0])),(BitVec.ofNat 152 (word80 [0x800c06060430443010,0x203000c20260b4444444]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffff8000,0x6442cffff000])),(BitVec.ofNat 152 (word80 [0x1008080040004020,0x40400100000008888888]))),(0x0,0x0)]
def g181C : List ColumnInfo := [(1,0,180,0,5),(4,0,177,0,5),(16,0,165,0,5),(32,0,149,0,5)]
def g181A : List (List Nat) := [[],[80,66]]
def g181D6 (j : Nat) := if j=0 then 0x4e09f else 0
def g181L : Nat → Packing
  | 6 => (1,0,2,0,0,0,0,g181D6)
  | _ => emptyPacking
def g181I (_ _ : Nat) : Option (Nat × Nat) := none
def g181 : Forest := ⟨181,6,fun i => g181Y[i]?.getD (0,0),g181C,g181A,g181L,g181I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g181P6_0 : block g181 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g181B6 : block g181 6 0 1=true := g181P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g181T : checkedTables g181 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g181 0 0 0 = true)
  · exact (rfl : block g181 1 0 0 = true)
  · exact (rfl : block g181 2 0 0 = true)
  · exact (rfl : block g181 3 0 0 = true)
  · exact (rfl : block g181 4 0 0 = true)
  · exact (rfl : block g181 5 0 0 = true)
  · exact g181B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g181G : graphValid g181 (boundsBefore K173) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low181 : Lower true (varsX 181) (graphGoal 181) 7 := lower_forest (g:=g181) (i:=0) (hints:=1284) (before_sound K173 V173) g181G g181T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K181 := extendKnown K173 7 [(181,[]),(205,[96,32,67,50,83]),(211,[96,33,16,65,117,84]),(213,[96,32,66,84]),(214,[112,16,33,66,84,101]),(218,[112,16,33,50,67,84,101]),(229,[32,100]),(241,[64,82,50,96,48]),(244,[32,16,65,49,83,99])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V181 : Known true K181 := extend_ok (m:=181) V173 low181 (by decide +kernel)
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
theorem g217G : graphValid g217 (boundsBefore K181) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low217 : Lower true (varsX 217) (graphGoal 217) 6 := lower_forest (g:=g217) (i:=0) (hints:=50331651) (before_sound K181 V181) g217G g217T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K217 := extendKnown K181 6 [(217,[]),(236,[32,16,83,100,67])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V217 : Known true K217 := extend_ok (m:=217) V181 low217 (by decide +kernel)
def g220Y : Array (Bits × Bits) := #[(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xc07fc01ff03fe07fff,0x7fc0ff81fed6800e07])),(BitVec.ofNat 152 (word80 [0x950a8d44a68a4b282a,0x35129a292ca6d6849249]))),((BitVec.ofNat 152 (word80 [0x7fffe0003fff81ff,0xff8000fffe0725a07038])),(BitVec.ofNat 152 (word80 [0x26130986cb0c924c4c,0x261b2c32493725a49249]))),((BitVec.ofNat 152 (word80 [0x7fffffffc00001ff,0xffffff0000074b4381c0])),(BitVec.ofNat 152 (word80 [0x381c0e070c0f1c7070,0x381c303c71c74b449249]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xff80000000000001ff,0xfffffffffffacd3c01ff])),(BitVec.ofNat 152 (word80 [0x2010080010000080,0x40200040000000092492]))),((BitVec.ofNat 152 (word80 [0xfffffffffffffffe00,0x532dffe00])),(BitVec.ofNat 152 (word80 [0x4020100020000100,0x80400080000000124924]))),(0x0,0x0)]
def g220C : List ColumnInfo := [(4,0,216,0,5)]
def g220A : List (List Nat) := [[],[118],[67],[67,118],[50],[50,118],[50,66],[50,66,118],[66,50],[66,50,118],[66],[66,118]]
def g220D5 (j : Nat) := if j=0 then 0x3f else 0
def g220L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g220D5)
  | _ => emptyPacking
def g220I (_ _ : Nat) : Option (Nat × Nat) := none
def g220 : Forest := ⟨220,5,fun i => g220Y[i]?.getD (0,0),g220C,g220A,g220L,g220I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g220P5_0 : block g220 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g220B5 : block g220 5 0 1=true := g220P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g220T : checkedTables g220 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g220 0 0 0 = true)
  · exact (rfl : block g220 1 0 0 = true)
  · exact (rfl : block g220 2 0 0 = true)
  · exact (rfl : block g220 3 0 0 = true)
  · exact (rfl : block g220 4 0 0 = true)
  · exact g220B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g220G : graphValid g220 (boundsBefore K217) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low220 : Lower true (varsX 220) (graphGoal 220) 6 := lower_forest (g:=g220) (i:=0) (hints:=570844672) (before_sound K217 V217) g220G g220T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K220 := extendKnown K217 6 [(220,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V220 : Known true K220 := extend_ok (m:=220) V217 low220 (by decide +kernel)
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
theorem g63G : graphValid g63 (boundsBefore K220) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low63 : Lower true (varsX 63) (graphGoal 63) 8 := lower_forest (g:=g63) (i:=0) (hints:=1347) (before_sound K220 V220) g63G g63T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K63 := extendKnown K220 8 [(63,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V63 : Known true K63 := extend_ok (m:=63) V220 low63 (by decide +kernel)
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
def K126 := extendKnown K125 8 [(126,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V126 : Known true K126 := extend_ok (m:=126) V125 low126 (by decide +kernel)
def g159Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3ffffffffffffffff,0xff8aba26071cb000f0ff])),(BitVec.ofNat 152 (word80 [0x5805000a8012801480,0x5382a824040881111111]))),((BitVec.ofNat 152 (word80 [0xfc003fffc0003fffc0,0x1f50ab07c5b20000f00])),(BitVec.ofNat 152 (word80 [0x9029a05320db209901,0x99b50ab0645a2bbbbbbb]))),((BitVec.ofNat 152 (word80 [0x3fffffffc00000,0x738dada715000f0000])),(BitVec.ofNat 152 (word80 [0xe0ce0a9c0a9c0ade0a,0xe0538daca71507777777]))),((BitVec.ofNat 152 (word80 [0x3fffffffffffff,0xfc85179417b3d0f0000f])),(BitVec.ofNat 152 (word80 [0x1700ce00ce00ce013,0x5179013b116666666]))),((BitVec.ofNat 152 (word80 [0xffffc0000000000000,0x45f462f96d0f000ff0])),(BitVec.ofNat 152 (word80 [0x1800f000f000f001c,0x401442992504444444]))),(0x0,0x0),(0x0,0x0),(0x33a4dd980e26ffff000,(BitVec.ofNat 152 (word80 [0x20030003000300020,0x284001004268888888]))),(0x0,0x0)]
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
theorem g159G : graphValid g159 (boundsBefore K126) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low159 : Lower true (varsX 159) (graphGoal 159) 8 := lower_forest (g:=g159) (i:=0) (hints:=1859) (before_sound K126 V126) g159G g159T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K159 := extendKnown K126 8 [(159,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V159 : Known true K159 := extend_ok (m:=159) V126 low159 (by decide +kernel)
def g183Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfff0007ffffff00ff5,0x7260457c2a0001f07c1f])),(BitVec.ofNat 152 (word80 [0x2a035012805216141,0x70604514080842108421]))),((BitVec.ofNat 152 (word80 [0xffffff8003fffff002,0x96eae6478100000003e0])),(BitVec.ofNat 152 (word80 [0x44c92649b246424262,0x9262e64781ad6b5ad6b5]))),((BitVec.ofNat 152 (word80 [0xfffffffffc00000009,0xd8c1d099d1003e0f8000])),(BitVec.ofNat 152 (word80 [0x17003801c017838381,0xd0c1d018d018c6318c63]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffffffffffffa,0x4ff083ab807c00003ff])),(BitVec.ofNat 152 (word80 [0x980240120098000008,0x4990828305294a5294a]))),((BitVec.ofNat 152 (word80 [9,0x1710a38776f8000ffc00])),(BitVec.ofNat 152 (word80 [0xe003801c00e0040408,0x7100283226318c6318c]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [4,0xe9177e4005fffff00000])),(BitVec.ofNat 152 (word80 [0xc00600300080804,0x8062040058421084210]))),(0x0,0x0)]
def g183C : List ColumnInfo := [(1,0,182,0,7),(2,0,181,0,7),(4,0,179,0,7),(0,2,165,16,6),(32,0,151,0,6),(16,0,165,0,5),(16,2,165,0,5),(128,0,55,0,5)]
def g183A : List (List Nat) := [[]]
def g183D5 := limbs80 #[#[0x67abb6a998de77255331,0x39f6e0b2a8779dc95454,0x277b92c9a9cef725954,0xf624c3]]
def g183D6 := limbs80 #[#[0xd55331bbd8954bd59731,0x54d43fd55151fdd5331f,0x9543bf59543ef55143f7,0x954bf59353bfd9153bfd,0xbf58f54bfd8d54fbd8,0xa59f8f75604b3b2b2010,0x61281ce022e02cbbbb0,0x41008ac9c331121b1413,0xc210c2108110200c210c]]
def g183H6 := limbs80 #[#[0x3801c80000002600,0x290001df50]]
def g183D7 := limbs80 #[#[0xf53fea9ff50feaa3f731,0x38291a0b007fd53faa9f,0xc338e5430d950a25647,0xc8350ec33a4d430ce935,0xa69530e3baca540]]
def g183H7 := limbs80 #[#[0xc144077a88ede9463b0,0x8c00f500f3cb00720]]
def g183D8 (j : Nat) := if j=0 then 0x688817f else 0
def g183H8 (j : Nat) := if j=0 then 0x1dae00d000045820215b else 0
def g183L : Nat → Packing
  | 5 => (6,3,3,0,0,5,0,g183D5)
  | 6 => (14,2,3,0,0,8,0,g183D6)
  | 7 => (7,1,3,0,0,8,0,g183D7)
  | 8 => (1,0,3,0,0,0,0,g183D8)
  | _ => emptyPacking
def g183I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 17 0 7 3 0 g183H6
  | 7 => lookupWord 3 17 4 8 4 0 g183H7
  | 8 => lookupWord 1 11 0 7 3 0 g183H8
  | _ => fun _ => none
def g183 : Forest := ⟨183,8,fun i => g183Y[i]?.getD (0,0),g183C,g183A,g183L,g183I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183P5_0 : block g183 5 0 6=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g183B5 : block g183 5 0 6=true := g183P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183P6_0 : block g183 6 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183P6_2 : block g183 6 2 12=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g183B6 : block g183 6 0 14=true := (@block_merge g183 6 0 2 12 g183P6_0 g183P6_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183P7_0 : block g183 7 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183P7_2 : block g183 7 2 5=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g183B7 : block g183 7 0 7=true := (@block_merge g183 7 0 2 5 g183P7_0 g183P7_2)
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
theorem g183G : graphValid g183 (boundsBefore K159) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low183 : Lower true (varsX 183) (graphGoal 183) 9 := lower_forest (g:=g183) (i:=0) (hints:=1348) (before_sound K159 V159) g183G g183T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K183 := extendKnown K159 9 [(183,[]),(231,[32,100])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V183 : Known true K183 := extend_ok (m:=183) V159 low183 (by decide +kernel)
def g187Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3fffffc1fffff622c,0xa62d1a00000fc0fc0fff])),(BitVec.ofNat 152 (word80 [0x280280084000402208,0x24011201041041041041]))),((BitVec.ofNat 152 (word80 [0xfc003fffe0ffe02d40,0xafe2f08000000003f000])),(BitVec.ofNat 152 (word80 [0x324b24500290822d00,0xafe2d02baebaebaebaeb]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffc00000ffffbd86,0x905842c003f03f00003f])),(BitVec.ofNat 152 (word80 [0x400c01608405001406,0x805840c6186186186186]))),((BitVec.ofNat 152 (word80 [0xffffffffff0000804d,0x6156a9c0fc000003ffc0])),(BitVec.ofNat 152 (word80 [0x809009800026048045,0x1429d4514514514514]))),((BitVec.ofNat 152 (word80 [0x9171,0x18b1dc3f00003ffc0000])),(BitVec.ofNat 152 (word80 [0xe00e010838088161,0x10a08c18618618618618]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x4e93,0x4f80057fffffc0000000])),(BitVec.ofNat 152 (word80 [0x300300210c0104890,0x4b000020820820820820]))),(0x0,0x0)]
def g187C : List ColumnInfo := [(0,2,169,16,8),(2,0,185,0,8),(1,0,186,0,7),(8,0,179,0,7),(16,2,169,0,7),(32,0,155,0,7),(128,0,59,0,7),(40,0,147,0,5),(9,0,178,0,4),(33,0,154,0,4),(136,0,51,0,4),(160,0,27,0,4)]
def g187A : List (List Nat) := [[],[83],[112],[112,83]]
def g187D5 := limbs80 #[#[0x50940483aa5954250120,0x482ea6154250120eab65,0x5d55250120f295454940,0x54120f2954509504835a,0xe6b6454950482da61542,0x5d9544835add15254120,0xc032b1d372595208ef82,0xa0d49d221344c80d141,0x408402000000]]
def g187D6 := limbs80 #[#[0x3b4a92a0907a94250120,0xfd2a4a02412fdd16548,0x837db2a80906f9655012,0x20fd6e4a8241fa509504,0x4837cb22a09077954541,0x920bf6e8a8241bed9150,0x248376b2a84907ad5450,0x4920bdaeaa1241bbd954,0x644827ebb2a8906ef645,0x595209faebb22413fdd5,0x965482dfba2ca905ef72,0x459520d78e8b2a41bbdc,0xd3654827fba2ca906bf7,0x74589509fceca12a13f5,0xe4b110027eba6c4a85bf,0xd64a54c22cfc7839194b,0xc822706803cdccd9662f,0xcadeabf59a9d1a813396,0x1710c8fa4217882e81c4,0x811008204000282071e0,0x204282141100e306b021,0x100802016c0f0040ac08,0xb8f00e98100180005040,0x1a838]]
def g187H6 := limbs80 #[#[0xc50008a2b,0x20749c000000000,0x1940000000,0x499b8900000000a072,0x2460000000,0x27600c00000420001100,0x1d90000010400a4]]
def g187D7 := limbs80 #[#[0xb50920fe54120fe50120,0xd9120bf59120fb54920f,0x8950bfd9520bf59520bf,0x520ff59120ff55120bfd,0x50ff58950ff50950ff59,0x360a81f85a0c000ffd89,0x799bc679865d14a4b0fc,0x48d61892310b45631e16,0xd16886231d221c52310b,0x81492221b11f41ca203,0x810a2235858b41d5c76d,0x2c8093c758a6d06156d0,0x6088718a2155842481c3,0x885288562c704c71938,0x193c7]]
def g187H7 := limbs80 #[#[0x4000f584ad018d618820,0x289000e1,0x8e34755ab18d378f0000,0xda4d0000241c9bf35856,0x70014380038c302e1cc9,0x3ba1583523000f3f21c9,0x10b36600102f88800d,0x415800001c40c6b89c10,0xc658246f00089,0x18001d25ca1d0e040000,0x988000004]]
def g187D8 := limbs80 #[#[0x79aa407f50bfaa1fd20,0x38d1accc2a0d145aa315,0x3b4654]]
def g187H8 := limbs80 #[#[0x3c800003c00000116c22,0x41347003a47040068800,0xc21d65180098409,0x1752060d19391d23431,0x34b00e82d7b0a001cc]]
def g187D9 (j : Nat) := if j=0 then 0x1653241bf else 0
def g187H9 := limbs80 #[#[0x0,0x11144218000000007c00,0x20]]
def g187L : Nat → Packing
  | 5 => (11,4,4,0,0,7,0,g187D5)
  | 6 => (30,3,4,0,0,9,0,g187D6)
  | 7 => (15,2,4,0,0,10,0,g187D7)
  | 8 => (3,1,4,0,0,7,0,g187D8)
  | 9 => (1,0,4,0,0,0,0,g187D9)
  | _ => emptyPacking
def g187I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 4 53 2 10 4 2 g187H6
  | 7 => lookupWord 11 71 5 11 5 2 g187H7
  | 8 => lookupWord 6 37 5 10 4 2 g187H8
  | 9 => lookupWord 1 23 0 8 2 2 g187H9
  | _ => fun _ => none
def g187 : Forest := ⟨187,9,fun i => g187Y[i]?.getD (0,0),g187C,g187A,g187L,g187I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P5_0 : block g187 5 0 11=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g187B5 : block g187 5 0 11=true := g187P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P6_0 : block g187 6 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P6_3 : block g187 6 3 27=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g187B6 : block g187 6 0 30=true := (@block_merge g187 6 0 3 27 g187P6_0 g187P6_3)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P7_0 : block g187 7 0 9=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P7_9 : block g187 7 9 6=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g187B7 : block g187 7 0 15=true := (@block_merge g187 7 0 9 6 g187P7_0 g187P7_9)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P8_0 : block g187 8 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g187B8 : block g187 8 0 3=true := g187P8_0
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
def g189Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xe03fffffffffffffff,0xff02e9c1330000f00fff])),(BitVec.ofNat 152 (word80 [0x408000500500200008,0x7002840121111111111]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffc07ff8007ff01ffc,0x34f235689000f00f000])),(BitVec.ofNat 152 (word80 [0x8a150560d609434290,0xb34f2356013333333333]))),((BitVec.ofNat 152 (word80 [0x7fffff80001fff,0xf9b3019f4600f00f000f])),(BitVec.ofNat 152 (word80 [0x13260980980d858321,0x20330197442222222222]))),((BitVec.ofNat 152 (word80 [0x7fffffffffe000,0x627abc690f000000f0])),(BitVec.ofNat 152 (word80 [0x1c382e02e02e060bc1,0xc06252bc696666666666]))),((BitVec.ofNat 152 (word80 [0xffff80000000000000,0x98c67ad8f0000fff00])),(BitVec.ofNat 152 (word80 [0x30030030080c02,0x80c428884444444444]))),(0x0,0x0),(0x665142404fffff00000,(BitVec.ofNat 152 (word80 [0x40040040001000,0x8888888888]))),(0x0,0x0)]
def g189C : List ColumnInfo := [(4,0,185,0,8)]
def g189A : List (List Nat) := [[],[80,66]]
def g189D8 (j : Nat) := if j=0 then 0x7f else 0
def g189L : Nat → Packing
  | 8 => (1,0,1,0,0,0,0,g189D8)
  | _ => emptyPacking
def g189I (_ _ : Nat) : Option (Nat × Nat) := none
def g189 : Forest := ⟨189,8,fun i => g189Y[i]?.getD (0,0),g189C,g189A,g189L,g189I⟩
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
  · exact (rfl : block g189 5 0 0 = true)
  · exact (rfl : block g189 6 0 0 = true)
  · exact (rfl : block g189 7 0 0 = true)
  · exact g189B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g189G : graphValid g189 (boundsBefore K187) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low189 : Lower true (varsX 189) (graphGoal 189) 9 := lower_forest (g:=g189) (i:=0) (hints:=1283) (before_sound K187 V187) g189G g189T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K189 := extendKnown K187 9 [(189,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V189 : Known true K189 := extend_ok (m:=189) V187 low189 (by decide +kernel)
def g190Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfc00fffffffffffffe,0x5a0916775b580000001f])),(BitVec.ofNat 152 (word80 [0x48169055212a429028,0x5808167653556b5ad6b5]))),((BitVec.ofNat 152 (word80 [0xfffffffe0003fff801,0xe415b52ec810000f83e0])),(BitVec.ofNat 152 (word80 [0x90a402980db01320cd,0x6415b02a4810c6318c63]))),((BitVec.ofNat 152 (word80 [0xfffffffc000001,0x39c472934e8001f07c00])),(BitVec.ofNat 152 (word80 [0xe13804e009c01bc171,0x288472834e00c6318c63]))),((BitVec.ofNat 152 (word80 [0xffffffffffffff,0x428bea0b89e83e00001f])),(BitVec.ofNat 152 (word80 [0x1c027004e009c0181,0x283e00988aa94a5294a]))),((BitVec.ofNat 152 (word80 [0xffff00000000000001,0x22fa117cb687c0007fe0])),(BitVec.ofNat 152 (word80 [0x38007000e00200,0x26a0154808318c6318c]))),(0x0,0x0),(0x9d26ecc07137ffff8000,(BitVec.ofNat 152 (word80 [0x200c0018003000400,0x91000c00310421084210]))),(0x0,0x0)]
def g190C : List ColumnInfo := [(4,0,186,0,7)]
def g190A : List (List Nat) := [[],[50]]
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
theorem g190G : graphValid g190 (boundsBefore K189) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low190 : Lower true (varsX 190) (graphGoal 190) 8 := lower_forest (g:=g190) (i:=0) (hints:=539055424) (before_sound K189 V189) g190G g190T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K190 := extendKnown K189 8 [(190,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V190 : Known true K190 := extend_ok (m:=190) V189 low190 (by decide +kernel)
def g207Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfffc00ffffffffffff,0xfe2828a5b8eb000f000f])),(BitVec.ofNat 152 (word80 [0x1481620a884a21481,0x4e0820a1886b55555555]))),((BitVec.ofNat 152 (word80 [0xfffffffffc000fffc0,0x7c1de850a93000000f0])),(BitVec.ofNat 152 (word80 [0x9590a4853236c89906,0x67c19e850a91bbbbbbbb]))),((BitVec.ofNat 152 (word80 [0xfffffff00000,0x1cf2190dcd100f00f00])),(BitVec.ofNat 152 (word80 [0x19e13809c02700de0b,0x814d21805cd133333333]))),((BitVec.ofNat 152 (word80 [0xffffffffffff,0xf2152f483bb80f00f00f])),(BitVec.ofNat 152 (word80 [0x1e01c00e003800e00c,0x50d40339022222222]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffff000000000000,0x116d0a38776f000fff0])),(BitVec.ofNat 152 (word80 [0x2000003000c0030010,0x124020802644444444]))),(0xce9177e4005ffff0000,(BitVec.ofNat 152 (word80 [0xc00200c003000c0020,0xa0121e000088888888]))),(0x0,0x0)]
def g207C : List ColumnInfo := [(2,0,205,0,7),(4,0,203,0,7),(0,2,141,64,6),(1,0,206,0,6),(8,0,199,0,6),(3,0,204,0,5),(4,2,137,64,5),(6,0,201,0,5),(9,0,198,0,5),(10,0,197,0,5),(64,0,141,0,5),(64,2,141,0,5),(128,0,79,0,5),(12,0,195,0,4),(68,0,137,0,4),(130,0,77,0,4),(132,0,75,0,4)]
def g207A : List (List Nat) := [[]]
def g207D4 := limbs80 #[#[0x50d32502e2615434c940,0x503c2551534c940b8b85,0x6086555140ac88654d32,0x19540b198319554502ca,0x87b87594655031659573,0x54d32d0639e0976d0750,0xd06b1619534cb41e4565,0xe1d654cb41ac78558d32,0x54f418f186dc153d0639,0x8e7825db53d0639e0976,0x54d614ca3960f7259741,0xe0319dd66558532d4775,0x6aa4e9109e3660a8d951,0x304000860fef1cb666c1,0x4]]
def g207D5 := limbs80 #[#[0x762b1a65a0f89434c940,0xb76e8a828139dc965d0,0x33db2ea0a05b974d414,0x409bee6b2a813bdc9655,0x503e5b1a64a07c9534c9,0xd40f32a6a1a81ea55132,0x3502dcbaa86a079b6350,0x4d40e72a8a9a816edd54,0x535027dbb2a6a04f8765,0x55140b72e9a9a81ce553,0x554502ddb9aa8a07ab72,0x219540e76caaa281ce19,0x9465502ecb98caa05e97,0x7359540bd6e4b2a819e5,0x5db41d433db2ccaa05db,0x5534cb419dee4b26a13d,0x95d932d0772b2a65a0fc,0xd56354f41be6e0a9e83b,0x3d5d953d073ab2aa7a0e,0xcf576d4f41ceacba9e83,0x3b9dc965d067bbaac7a0,0x8fc5534c9519eee6b2e8,0x657cdc153547733b264a,0x996e66558532f8aa6b0a,0xa65e3551434caf3baac2,0x6995cf7550d32b9aeaa1,0x9a65f15c5534cbe5b82a,0xa69974f5454d32e9aa8a,0xaa2653bdd9544cae7ba2,0xcca995eb7059532b9ae7,0xb2a87c75515350ee6b9,0xec0a9cef72595439f6e],#[0xe9b02a7bc5c76054f78b,0xb9ec4aa4ef72593539f2,0x580f0013edc163d5276,0xd82f0b029098230801d,0x19863170551484b1103d,0x2388b220811e8771c06d,0x2a8a72809d2689725091,0x318c3300bd2e8b72d0b1,0x3e8f33b0dd368d3330c9,0x4c92b4a1214590f43101,0x57957551515193f4f135,0x5028697c01da96759161,0x960a182000000001140a,0x60d10200182c40b102,0x3102c4081160814408,0xc080c608000000000,0x302c60800000000000,0x84560838240086b18386,0x20068213101118201180,0x94411182011820118,0x2820]]
def g207H5 := limbs80 #[#[0x9640000000000da00028,0x100000029324a,0xd4000dd0ce5000c40,0x24200000000183000000,0xd600c8f144e000000,0x186000015e0000]]
def g207D6 := limbs80 #[#[0xe55140ee50d40fa4c940,0x59741bd58f41f94cb41e,0x8532bdd8d51f94c951bd,0x153f354d32f350d32f95,0x40fe54140bbd8954bed8,0xbf59540ef55140fed41,0xfed4d40fe54d40bfd954,0xe19540fed8d40fe58d40,0xd9540fe99540fe59540f,0x9150fd54550fdd0550fe,0xf41bf59350fdd0750bfd,0x32fd54d51fdd4f41fd54,0x2fb59132fbd5132fb551,0xf754d43fb99532fb5953,0xfd9543bf59543ef55143,0x55153fd58553fed8153b,0x5353bfd9153dfd5153df,0x954bfd8154bf59353df5,0x54bf58354bfd8d54fbd8,0x508f0e814814800bf58f,0x7c2c2518921021c02f85,0x456824f71cc370674c81,0xc49782dc574a293424d,0xc9cbb836ded359cb1e63,0x37c5b88f0b201be879ae,0xd1ea073be6dcc094b246,0x258b622c1567a9951a95,0x16203c3805a4161a1c09,0x16114a0342a25060f0e0,0x4c23c588860289626114,0x18dc0215881e40d5622,0xc60382585862600c6e01],#[0x8404040082c1848900a0,0x44804149112010502001,0x3240689008890080c524,0x4911214020a480d12140,0x20018000a06890088900,0x60820608080121820818,0xd00d5618f47003480824,0xa3448051c815861102b0,0x82c2443021a89006406,0x101e00c1000818202004,0x309082841021f20487,0x82586002020038408304,0x6080060020200303]]
def g207H6 := limbs80 #[#[0x9a9b018f5e18f065646,0xc001d5280f5e00047461,0xe400633a880c492d81b5,0xc580023c8d2541bf38aa,0xe7c2ae4a93a1350c1,0x3804a345e5a10006d8ca,0xc30f474b720f8900078,0x2828219721084e0c68c9,0x709010858cb54cd85001,0x56278138d4632a900007,0x3821f86cdda42000a72c,0x66445800341c47af70fd,0x7a2c22299e0000]]
def g207D7 := limbs80 #[#[0x551fba0fd4c7f481f940,0x87ff50fea87f503da65f,0x3fea9fd54ffa9ff54ffa,0x421c8c04e1e0c0421200,0xe09212c5ea6ab015699,0x2128326120b12084b204,0x504dae020500ca212c5a,0x20630a86020532084b20,0x818c82120b14a0a180c,0xb18a0a180830608c2a18,0x40e084c2c63040e084]]
def g207H7 := limbs80 #[#[0x790da000000004a0540,0x3c,0x259003c757c002980,0x21998000000000,0x10000000000000000000,0x2c90000000000003c,0x214003efb2c0,0x12d0000,0xcf71000008a40,0xe0c0000000000001300,0x1c4f0800000000000,0x8d80,0x6b000b4c00000000000,0xe08800f4000002c80000,0x10,0x0,0x2d18140,0x80000000000000000000,0x3342,0xa000ee54800000000000,0xf6959b75400003eb7d2e,0xa82b5000961718,0xd0000000221000000000,0xe000000000000000000d,0x4c86700000000000035,0x0,0x9c317f8c000280]]
def g207D8 (j : Nat) := if j=0 then 0x5a02013f else 0
def g207H8 := limbs80 #[#[0x120000003ad34022a8,0x3e400000803c,0x39002840000000000940,0x10d580132dc00000]]
def g207L : Nat → Packing
  | 4 => (19,4,5,0,0,7,0,g207D4)
  | 5 => (71,3,5,0,0,10,0,g207D5)
  | 6 => (55,2,5,0,0,11,0,g207D6)
  | 7 => (14,1,5,0,0,9,0,g207D7)
  | 8 => (1,0,5,0,0,0,0,g207D8)
  | _ => emptyPacking
def g207I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 4 53 3 9 5 0 g207H5
  | 6 => lookupWord 17 83 6 11 7 0 g207H6
  | 7 => lookupWord 13 211 2 10 6 0 g207H7
  | 8 => lookupWord 3 37 2 8 4 0 g207H8
  | _ => fun _ => none
def g207 : Forest := ⟨207,8,fun i => g207Y[i]?.getD (0,0),g207C,g207A,g207L,g207I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g207P4_0 : block g207 4 0 19=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g207B4 : block g207 4 0 19=true := g207P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g207P5_0 : block g207 5 0 3=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g207P5_3 : block g207 5 3 68=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g207B5 : block g207 5 0 71=true := (@block_merge g207 5 0 3 68 g207P5_0 g207P5_3)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g207P6_0 : block g207 6 0 13=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g207P6_13 : block g207 6 13 42=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g207B6 : block g207 6 0 55=true := (@block_merge g207 6 0 13 42 g207P6_0 g207P6_13)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g207P7_0 : block g207 7 0 6=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g207P7_6 : block g207 7 6 8=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g207B7 : block g207 7 0 14=true := (@block_merge g207 7 0 6 8 g207P7_0 g207P7_6)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g207P8_0 : block g207 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g207B8 : block g207 8 0 1=true := g207P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g207T : checkedTables g207 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g207 0 0 0 = true)
  · exact (rfl : block g207 1 0 0 = true)
  · exact (rfl : block g207 2 0 0 = true)
  · exact (rfl : block g207 3 0 0 = true)
  · exact g207B4
  · exact g207B5
  · exact g207B6
  · exact g207B7
  · exact g207B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g207G : graphValid g207 (boundsBefore K190) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low207 : Lower true (varsX 207) (graphGoal 207) 9 := lower_forest (g:=g207) (i:=0) (hints:=16778851) (before_sound K190 V190) g207G g207T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K207 := extendKnown K190 9 [(207,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V207 : Known true K207 := extend_ok (m:=207) V190 low207 (by decide +kernel)
def g215Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfff8007fffffc03f,0xf4fb0703c0c000f0000f])),(BitVec.ofNat 152 (word80 [0x162151351251148585,0x347b060140c555555555]))),((BitVec.ofNat 152 (word80 [0xffffffff8007ffffc0,0x1b4b6910587000000ff0])),(BitVec.ofNat 152 (word80 [0x248264264364190909,0x9b434110585999999999]))),((BitVec.ofNat 152 (word80 [0xfffffffff8000000,0x7618c8d9d400f00f000])),(BitVec.ofNat 152 (word80 [0x380b803803805e0e0e,0x56108859d4333333333]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffffff,0xc8133847ab90f00f00ff])),(BitVec.ofNat 152 (word80 [0x400c00400400600000,0x3806830222222222]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xff0000000000000000,0x45c463c762f000fff00])),(BitVec.ofNat 152 (word80 [0x3001801801801010,0x1c0608202444444444]))),(0x33a4d3e0015ffff00000,(BitVec.ofNat 152 (word80 [0x80c006006006002020,0x280c160001888888888]))),(0x0,0x0)]
def g215C : List ColumnInfo := [(1,0,214,0,7),(2,0,213,0,7),(4,0,211,0,7),(16,0,199,0,6),(64,0,151,0,6),(128,0,87,0,6),(17,0,198,0,5),(65,0,150,0,4)]
def g215A : List (List Nat) := [[],[33,116],[16,118],[16,32,100,116],[32,16,116,100],[32,100]]
def g215D3 (j : Nat) := if j=0 then 0x17019550d3254540 else 0
def g215D4 := limbs80 #[#[0x50d51503e050d3254540,0x502cc6154354540f1153,0xe0d5454540f238255151,0x624c302cc]]
def g215H4 (j : Nat) := if j=0 then 0x7 else 0
def g215D5 := limbs80 #[#[0x3f0992a2a07315454540,0xf66e2a1a81ec50d5150,0x2dcbaa86a07995350d4,0x409f6eca9a816edd5435,0x50e7abaec2a1df37158d,0x6009f6e0b2a87c755153,0x819d2213c6cc121e3048,0x1000000e]]
def g215H5 := limbs80 #[#[0x1839400001200002e0,0x2a0000000109410043,0xd5000000000000000000,0x34400]]
def g215D6 := limbs80 #[#[0xdd8543ee50d40fc54540,0xd8543fe58d40fe54d40b,0x9543bf59543f754d43fd,0xf7a6f645449391f00bfd,0x34985a3e56269306d058,0x2088200c80841324238]]
def g215H6 := limbs80 #[#[0x4e000000002020018188,0x4a18a001600000009,0x1c2800000003041c2000,0x24b0000000000000000,0x45000000000006160000,0xc45c92c8209001e0c006,0x702c5600000586,0x12980700,0x3c22a50ac0]]
def g215D7 := limbs80 #[#[0x7db4a91e203fa87f940,0x152a0e46]]
def g215H7 := limbs80 #[#[0x15b594b100009,0x380800000000000,0x23,0x0,0x0,0xa20000,0x808c0c0000000000000,0x22000000000000000000,0x3053,0x207001c00c12d1000,0x10c0000000000000]]
def g215D8 (j : Nat) := if j=0 then 0x2c6881bf else 0
def g215H8 := limbs80 #[#[0x150000000000000000,0x380000000000000000,0xa100000004a300000000]]
def g215L : Nat → Packing
  | 3 => (1,5,3,0,0,0,0,g215D3)
  | 4 => (5,4,3,0,0,5,0,g215D4)
  | 5 => (12,3,3,0,0,7,0,g215D5)
  | 6 => (9,2,3,0,0,8,0,g215D6)
  | 7 => (2,1,3,0,0,6,0,g215D7)
  | 8 => (1,0,3,0,0,0,0,g215D8)
  | _ => emptyPacking
def g215I : Nat → Nat → Option (Nat × Nat)
  | 4 => lookupWord 1 2 0 4 0 0 g215H4
  | 5 => lookupWord 2 29 3 9 3 2 g215H5
  | 6 => lookupWord 6 61 3 11 4 3 g215H6
  | 7 => lookupWord 3 79 2 11 4 3 g215H7
  | 8 => lookupWord 1 31 0 8 1 3 g215H8
  | _ => fun _ => none
def g215 : Forest := ⟨215,8,fun i => g215Y[i]?.getD (0,0),g215C,g215A,g215L,g215I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215P3_0 : block g215 3 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g215B3 : block g215 3 0 1=true := g215P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215P4_0 : block g215 4 0 5=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g215B4 : block g215 4 0 5=true := g215P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215P5_0 : block g215 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215P5_1 : block g215 5 1 11=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g215B5 : block g215 5 0 12=true := (@block_merge g215 5 0 1 11 g215P5_0 g215P5_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215P6_0 : block g215 6 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215P6_3 : block g215 6 3 6=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g215B6 : block g215 6 0 9=true := (@block_merge g215 6 0 3 6 g215P6_0 g215P6_3)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215P7_0 : block g215 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215P7_1 : block g215 7 1 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g215B7 : block g215 7 0 2=true := (@block_merge g215 7 0 1 1 g215P7_0 g215P7_1)
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
  · exact g215B3
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
theorem low215 : Lower true (varsX 215) (graphGoal 215) 9 := lower_forest (g:=g215) (i:=0) (hints:=16778820) (before_sound K207 V207) g215G g215T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K215 := extendKnown K207 9 [(215,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V215 : Known true K215 := extend_ok (m:=215) V207 low215 (by decide +kernel)
def g219Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xf801fffff83fffff88,0x8d45258c0007c00003ff])),(BitVec.ofNat 152 (word80 [0x511442881080410380,0x88450185294a5294a529]))),((BitVec.ofNat 152 (word80 [0xfffe003fffc1ff8197,0x2149d2980000000ffc00])),(BitVec.ofNat 152 (word80 [0x64190b20a005020996,0x2149421a739ce739ce73]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffc00001fffcd7,0xc5b0444400f801f0001f])),(BitVec.ofNat 152 (word80 [0x80200c02c108140047,0x45904400c6318c6318c6]))),((BitVec.ofNat 152 (word80 [0xfffffffffffe000021,0x2ed47a201f003e007fe0])),(BitVec.ofNat 152 (word80 [0x4010030000181021,0x4903800842108421084]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x44,0x903f89b3e0003fff8000])),(BitVec.ofNat 152 (word80 [0x180600c0210602000,0x902481a1084210842108]))),((BitVec.ofNat 152 (word80 [0x33a,0x528a034bffffc0000000])),(BitVec.ofNat 152 (word80 [0x60180300421804018,0x20a024a108421084210]))),(0x0,0x0)]
def g219C : List ColumnInfo := [(1,0,218,0,7),(8,0,211,0,7),(16,0,203,0,7),(64,0,155,0,7),(0,2,137,80,6),(2,0,217,0,6)]
def g219A : List (List Nat) := [[],[48,100]]
def g219D7 := limbs80 #[#[0xa15662e85d03eca3f551,0x498b]]
def g219D8 (j : Nat) := if j=0 then 0x2c21a1bf else 0
def g219H8 (j : Nat) := if j=0 then 0x315 else 0
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
theorem low219 : Lower true (varsX 219) (graphGoal 219) 9 := lower_forest (g:=g219) (i:=0) (hints:=16777283) (before_sound K215 V215) g219G g219T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K219 := extendKnown K215 9 [(219,[])]
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
def K221 := extendKnown K219 8 [(221,[]),(252,[80,16,66,50])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V221 : Known true K221 := extend_ok (m:=221) V219 low221 (by decide +kernel)
def g222Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffe007ffffffffffff,0xfecd053771d0000000ff])),(BitVec.ofNat 152 (word80 [0xa40b02902a8254148,0x28cd051541d999999999]))),((BitVec.ofNat 152 (word80 [0xfffff801fff0007ffc,0x704ce4d5e000f00f00])),(BitVec.ofNat 152 (word80 [0xac85214c14c1b60990,0xcc704ca4d4e333333333]))),((BitVec.ofNat 152 (word80 [0x1ffffff8000,0x1851f8cb6400f00f000])),(BitVec.ofNat 152 (word80 [0xcf09c2702701380de1,0x70051f8cb64333333333]))),((BitVec.ofNat 152 (word80 [0x1ffffffffff,0xfe7a2f223e10f00f000f])),(BitVec.ofNat 152 (word80 [0xf00e03803801c00e01,0x80322a22360222222222]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffe0000000000,0x24f811c24f000ffff0])),(BitVec.ofNat 152 (word80 [0x4002001000,0x444444444]))),(0x19b82cd0daffff00000,(BitVec.ofNat 152 (word80 [0x100401800c006002,0x1888041090888888888]))),(0x0,0x0)]
def g222C : List ColumnInfo := [(4,0,218,0,7)]
def g222A : List (List Nat) := [[],[50]]
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
theorem g222G : graphValid g222 (boundsBefore K221) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low222 : Lower true (varsX 222) (graphGoal 222) 8 := lower_forest (g:=g222) (i:=0) (hints:=553739840) (before_sound K221 V221) g222G g222T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K222 := extendKnown K221 8 [(222,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V222 : Known true K222 := extend_ok (m:=222) V221 low222 (by decide +kernel)
def g237Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xff003ff87fe1fffff4,0x12d331000007c00003ff])),(BitVec.ofNat 152 (word80 [0xa22885110440420d4,0x12131114a5294a5294a5]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffc0007ffe1ff057,0x2c4b828000f801f07c00])),(BitVec.ofNat 152 (word80 [0x2c0301620280404253,0x2c4b000c6318c6318c63]))),((BitVec.ofNat 152 (word80 [0xffffffff80001fff28,0xf4691c001f003e0f801f])),(BitVec.ofNat 152 (word80 [0x300401800308808028,0xe4480008421084210842]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffe00010,0xab842f83e000000fffe0])),(BitVec.ofNat 152 (word80 [0x404812002400090400,0x1842ea1084210842108]))),((BitVec.ofNat 152 (word80 [0xe,0x11bac77c00003ff00000])),(BitVec.ofNat 152 (word80 [0x80701c0438110e0804,0x11b0c7318c6318c6318c]))),((BitVec.ofNat 152 (word80 [0xc1,0x4514407fffffc0000000])),(BitVec.ofNat 152 (word80 [0x8020004000100000,0x42108421084210]))),(0x0,0x0)]
def g237C : List ColumnInfo := [(4,0,233,0,8),(64,0,173,0,8),(8,0,229,0,7),(32,0,205,0,7),(68,0,169,0,7),(1,0,236,0,6),(128,0,109,0,6),(5,0,232,0,5),(9,0,228,0,5),(12,0,225,0,5),(33,0,204,0,5),(36,0,201,0,5),(40,0,197,0,5),(72,0,165,0,5),(96,0,141,0,5),(132,0,105,0,5),(192,0,45,0,5),(41,0,196,0,4),(76,0,161,0,4),(100,0,137,0,4),(136,0,101,0,4),(160,0,77,0,4)]
def g237A : List (List Nat) := [[],[98,83]]
def g237D4 := limbs80 #[#[0x9924338798595434c921,0x7550d32486b0b2f32a86,0x83caac6a1aa490f60e41,0x924370593a154354921b,0x750d52486b0f26c3a86a,0x81c6564cb0c056164e8,0x5282000014a094a]]
def g237D5 := limbs80 #[#[0x50d52487615d5434c921,0x882f8e017548620f0553,0x6027548620ba7845d521,0x48550ae5869d521882f8,0xae7825d921543d854970,0x5d921542b5e0d7648550,0xd42b960a7648550ab784,0xdd55258121ab7845d921,0x4c921f856550d3248759,0xf456554d32487e199543,0x59532487d1995534c921,0x486e9e11654c921bc783,0x61e654c921bc58399532,0x54921de3805d53248679,0xf856350d52487e154d43,0x50d52487e15cd4354921,0x487c9a154354921f2585,0xa1d4354921da58750d52,0x54921f456354d5248769,0xbe3805cd52486d9e1563,0x5c943487695d57250d21,0x4866de1d6550d21ba785,0x60e6550d21ba58299543,0x54d21e556558d53486e5,0x9f3805d953486d960a65,0x5d95348679e097654d21,0x4867960b7654d219b784,0x60f74595219b7845db53,0x8a2d138843615078026d,0xa13281391b0cc572892c,0xec15dade67b0174b4572,0x9bd5d2dd68acd4e77358],#[0x1b9d9eb74fa1cde571f8,0x3208200000000220f3b9,0x88c21702000000400002,0x225044a080000008c144,0x8224206220205a242c10,0x8200000981014a800801,0x94100000000000006]]
def g237H5 := limbs80 #[#[0x76eb0000f000001400,0xd10000850000005c8e00,0x42000000,0xfd000000000000e3]]
def g237D6 := limbs80 #[#[0x3b4a92a090785434c921,0xdcaca90c41f84855088,0x4373b1242a8765524855,0x21dcac490ea1d954921d,0x486f2baa6490fc5534c9,0x921ecaa6a9243e950d52,0x3486f3b9aa490f675354,0x9521bcae5a9a43e95c94,0x524caf2b94ca90db7745,0x541209f6e0b2a65d354d,0x965483f5b92a0907e952,0x548620fcaea90c41bbdc,0x4921543f8b8242a87e67,0x7648550fcec490aa1f95,0xd89525437b3b242a86f5,0x57648750edec4a92a1bb,0xd59560487f2a92c090ef,0xe5654c921beeeab0243b,0xf95c152487f332a6490f,0xfe56354921fcaa6a9243,0x3ed59543487f2b9aa490,0xfb57650d21f6ccaa1a4,0x43f558d53487f2b92a69,0x90f766554d21eeacaa9a,0xa437ddd953486fabb2a6,0x690df576d4d21eeacba9,0x2a437ddd5634877ab2ac,0xca90df77359521beee0b,0x32a437d5c265487dbba2,0x2ca997cd5354932beae7,0x260017edc16354b7db8,0xe2403e86a0b61201c826],#[0x90888fa1ce350608b213,0xbc9722d6590ac9462664,0x9ca38e6f0d89a632e630,0xa43e831009f23c6760e8,0xfe9c132a5a4968f118a2,0xaf15aab254ea914ca8e4,0x182afe5e6b916cace58e,0x444442e8911131a626c3,0x52831409e18a13801b84,0x3844431409e11110278,0xd1b840044409e1461110,0x110c50038444409e1110,0x12611105027844446189,0x4984111427845044409e,0xfc0c20c9b84004442e0d,0x6e1e011109427845048,0x43c4080414106070f082,0x81d1a08309450825158,0x40434109148824645,0x260c24981c30f4108181,0x20f096123101c082c261,0xb09260e085020804248c,0xd248c24f2e0850302030,0xb260850a83031384120,0x1083c10094842003c8c2,0x10c3c0820b02088c10f2,0x60408102063c8420f022,0x1410]]
def g237H6 := limbs80 #[#[0x101028801410856801c5,0xa398e000000000000006,0x4000820000000051de01,0x2824026002cfea3d19d3,0x5bb4a00000655d14003c,0x3540000018b53523d30e,0x80012d0004b800000000,0x6400117f2a0010821880,0x53693913000f113,0x3c0885159015aecb0,0x9e33e198b01252802510,0x22c1c91428ab087846ca,0x189c018008]]
def g237D7 := limbs80 #[#[0xb58850bd58450f948620,0x54921f94c921ded4250b,0x4920fe54120ed50d21f9,0x620fe54220bf59520fb5,0x50df54950fd48550bf59,0xbf59650bfd8950dfd49,0xbf58b50df54b50fd4875,0xdd4d21fd54d21fd58121,0x99521fd59521fd58d21f,0x8152bf59532fb54932fd,0xd52dfd4d52df54d52bfd,0x50bf58f52bf58352bfd8,0x2ffd8950ff58950ff549,0xff58d52ff54d52ff5815,0xc3144e0810be0f40d800,0xc4e419f2fa550991101d,0x76ac4544a012ba2e4267,0x40c7c6f05cc36867ec59,0xca1139a624a290117a17,0x10209c3283acd52e9bd1,0x30a102600c284098430a,0xb00a0923845138488780,0x44c01b091110c05d2488,0x84285298309113014c24,0x361222e1c10850853061,0xd8488850360c24454026,0x86c380508170e0221e00,0x130610c44412830c6222,0x88a1d309c24450d87011,0x22898185311160094d84,0x809518fc224616984e12,0x294c184888951e112985],#[0x11b0e0284442a530e022,0x44c38031110a940d8701,0xc04440d87011130e0284,0x883282020c1511410361,0x40c1211528194101060a,0x2a50]]
def g237H7 := limbs80 #[#[0x245838a280000,0x0,0xbc00000000000000000,0xc002940006d4a4127032,0x3d45970002e,0xb380000,0x0,0x5b00000000000000,0x3087b67dd40000000000,0x1280000000000000000c,0x122b,0x0,0x0,0x204224000000000000,0x44000000000000,0x82cf00046c0000000000,0x3828000000030,0xce489534000000000,0x103,0x29b8000010130f80000,0xc4f8062a0025d4ae0000,0xbabd7000000000000000,0x1de800000000d4,0x2196310000000000,0x88f1663300122c000000,0xbd50000010b400000c02,0x88007920000000000072,0x7da0000004e0010880,0x8840058e000000f58,0x8580000000000000000,0x9800000000000006cb00,0x0],#[0x343800000000,0xa769e00000000000,0x0,0xd0000,0x40981e001418003b0000,0x3e000463c100000043]]
def g237D8 := limbs80 #[#[0xd50fe287f883fa41f521,0xa5fd52fe997fd43fca1f,0xecd85a258cc4212003fe,0x8214440090a14459f451,0x862a08481c60a180a146,0x41a180a2051a18111030,0x8214461a181112181118,0x2821446154086]]
def g237H8 := limbs80 #[#[0x20ea01d0021c0045140,0x1a170700000145cc1,0xc626c002190a20000000,0x25b6531500150b9111ae,0xec0421001004003243ab,0xf6259c413c41a5a3a611,0xb08841c658702887fc,0xa8924f8960600003c000,0xb87400498000d918e0d6,0x2dc57cc000a2000109d1,0x62682330669000abca,0x32089a00000527792000,0x84680ae7]]
def g237D9 (j : Nat) := if j=0 then 0x1882013f else 0
def g237H9 := limbs80 #[#[0xa200000e5a4648920c,0x80009384400000000000,0x2600000001c7796088a,0x2b0a6000]]
def g237L : Nat → Packing
  | 4 => (7,5,5,0,0,6,0,g237D4)
  | 5 => (45,4,5,0,0,9,0,g237D5)
  | 6 => (63,3,5,0,0,11,0,g237D6)
  | 7 => (40,2,5,0,0,11,0,g237D7)
  | 8 => (10,1,5,0,0,9,0,g237D8)
  | 9 => (1,0,5,0,0,0,0,g237D9)
  | _ => emptyPacking
def g237I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 2 41 0 8 3 1 g237H5
  | 6 => lookupWord 14 83 6 11 6 1 g237H6
  | 7 => lookupWord 18 271 3 11 6 1 g237H7
  | 8 => lookupWord 15 83 6 11 6 1 g237H8
  | 9 => lookupWord 3 29 3 9 4 1 g237H9
  | _ => fun _ => none
def g237 : Forest := ⟨237,9,fun i => g237Y[i]?.getD (0,0),g237C,g237A,g237L,g237I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P4_0 : block g237 4 0 7=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g237B4 : block g237 4 0 7=true := g237P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P5_0 : block g237 5 0 2=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P5_2 : block g237 5 2 43=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g237B5 : block g237 5 0 45=true := (@block_merge g237 5 0 2 43 g237P5_0 g237P5_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P6_0 : block g237 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P6_1 : block g237 6 1 19=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P6_20 : block g237 6 20 43=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g237B6 : block g237 6 0 63=true := (@block_merge g237 6 0 1 62 g237P6_0 (@block_merge g237 6 1 19 43 g237P6_1 g237P6_20))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P7_0 : block g237 7 0 7=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P7_7 : block g237 7 7 27=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P7_34 : block g237 7 34 6=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g237B7 : block g237 7 0 40=true := (@block_merge g237 7 0 7 33 g237P7_0 (@block_merge g237 7 7 27 6 g237P7_7 g237P7_34))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P8_0 : block g237 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P8_1 : block g237 8 1 9=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g237B8 : block g237 8 0 10=true := (@block_merge g237 8 0 1 9 g237P8_0 g237P8_1)
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
  · exact g237B4
  · exact g237B5
  · exact g237B6
  · exact g237B7
  · exact g237B8
  · exact g237B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237G : graphValid g237 (boundsBefore K222) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low237 : Lower true (varsX 237) (graphGoal 237) 10 := lower_forest (g:=g237) (i:=0) (hints:=33555715) (before_sound K222 V222) g237G g237T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K237 := extendKnown K222 10 [(237,[]),(249,[80,66])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V237 : Known true K237 := extend_ok (m:=237) V222 low237 (by decide +kernel)
def g238Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffff8003ffc03ffc0,0x19612710af7000000f00])),(BitVec.ofNat 152 (word80 [0x1489545aa1286a1485,0x996127108f5bbbbbbbbb]))),((BitVec.ofNat 152 (word80 [0xffffffc00003ffff,0xfad9290254c000f0f00f])),(BitVec.ofNat 152 (word80 [0x2602601301b0b01909,0x3a41080054c111111111]))),((BitVec.ofNat 152 (word80 [0xfffffffffffc0000,0x7638c8d98400f0f00f0])),(BitVec.ofNat 152 (word80 [0x3803801c01c0c01e0e,0x2630c88904111111111]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffffff,0xc8137847ab90f00000ff])),(BitVec.ofNat 152 (word80 [0x402c01600a0000a000,0x1070072a1666666666]))),((BitVec.ofNat 152 (word80 [0xff0000000000000000,0x45c463c762f000fff00])),(BitVec.ofNat 152 (word80 [0x3001800c0100c010,0x41c4004202444444444]))),(0x33a4d3e0015ffff00000,(BitVec.ofNat 152 (word80 [0x80c006003002030020,0x1808360010888888888]))),(0x0,0x0)]
def g238C : List ColumnInfo := [(4,0,234,0,7)]
def g238A : List (List Nat) := [[],[50]]
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
theorem low238 : Lower true (varsX 238) (graphGoal 238) 8 := lower_forest (g:=g238) (i:=0) (hints:=555767136) (before_sound K237 V237) g238G g238T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K238 := extendKnown K237 8 [(238,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V238 : Known true K238 := extend_ok (m:=238) V237 low238 (by decide +kernel)
def g243Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3fffffffffc1f430c,0x26ae7a00000fc003f03f])),(BitVec.ofNat 152 (word80 [0x284284100408400308,0x4a47209249249249249]))),((BitVec.ofNat 152 (word80 [0xfc003ff83fffe02468,0xef61b080000000fc0fc0])),(BitVec.ofNat 152 (word80 [0x32132020a090022408,0x6f41b0238e38e38e38e3]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffc0003fffffb48e,0x905842c003f03f000fff])),(BitVec.ofNat 152 (word80 [0x400401410120001006,0x801800c4104104104104]))),((BitVec.ofNat 152 (word80 [0xffffffffc000008945,0x6156a9c0fc000003f000])),(BitVec.ofNat 152 (word80 [0x8098098009c0848845,0x605288d6596596596596]))),((BitVec.ofNat 152 (word80 [0x9171,0x18b1dc3f00003ffc0000])),(BitVec.ofNat 152 (word80 [0xe00e020e01088161,0x10a04c18618618618618]))),((BitVec.ofNat 152 (word80 [0x4e93,0x4f80057fffffc0000000])),(BitVec.ofNat 152 (word80 [0x30030043002104490,0xb000120820820820820]))),(0x0,0x0)]
def g243C : List ColumnInfo := [(1,0,242,0,7),(2,0,241,0,7),(16,0,227,0,7),(32,0,211,0,7),(64,0,179,0,7),(128,0,115,0,7),(0,2,161,80,6),(0,32,82,129,6),(1,32,82,128,5),(3,0,240,0,5),(16,2,161,64,5),(18,0,225,0,5),(33,0,210,0,5),(34,0,209,0,5),(64,2,161,16,5),(128,32,82,1,5),(17,0,226,0,4),(35,0,208,0,4),(65,0,178,0,4),(80,0,161,0,4),(80,2,161,0,4),(82,0,161,0,4),(129,0,82,0,4),(129,32,82,0,4),(161,0,82,0,4),(192,0,51,0,4)]
def g243A : List (List Nat) := [[],[96,81,116]]
def g243D5 := limbs80 #[#[0x54940483ca5515250120,0x4839a5915254120d6975,0xe015254520e6b6454950,0x50950f295250950503d8,0xb6785b3060335d8f71,0x1410]]
def g243D6 := limbs80 #[#[0x3e49928090745524c951,0xecaa4a8a41da5495048,0x83f4a9280904dd72d8d5,0x20df2caa0241ee551404,0x482fcbaa80906fb65501,0x120df2c8a82417edd540,0x2483e6b2264906fb6454,0x4920edaa8a9241fadc15,0x5448377b22a4906ed645,0xd91209feeab22413f5d9,0x165482fdb82ca904fd75,0x4d95209fee8b2a41bedc,0x950502fbb8a84984fd7,0x6254140ef2a4a8281ee5,0x5d7625027fbb2a4a06fb,0x77150950dbec690aa13f,0xedc152543b6a9284a85f,0x777054951eeae0a92a3d,0x520d0160027eba6c0a97,0x23d0de340b22708e1e0,0x9a5d1665414a4f116441,0x22832067c1ea731b66c1,0x8a9f2769a262932468e2,0xc40505c317140aaea82,0x7c508171f00504a60217,0x7045c110c31714085010,0x918440014117045c0821,0x10501140508002044c29,0x5c402001804207060301,0x6108006010801817100c,0x40070308005045c482a3,0x4217058c5c217040c30],#[0x18]]
def g243H6 := limbs80 #[#[0xa325002096c2817a80,0xa944]]
def g243D7 := limbs80 #[#[0x54c951b7d8d50f34c920,0xcca51dd54951f5cc951f,0x4520fe54120fe50120f5,0x120fb54920fd94520fd5,0x20bf59520bfd9120bf59,0xfd54540fe54140bfd95,0xdf54950bfd8940fd9454,0xfd8152fdd8151bfd8151,0x59520ff59120ff55120b,0x8940ff54940ff50930ff,0xd21ff50950ff48550ff5,0xffd8152ff58152ff54,0x1ea314550880da164148,0xc834ee9ad2de4fc95917,0x3992af55b4aa947a6d46,0x2541a7fef91e4b996eed,0xc984517165b49b90f196,0x19728164c5860078a310,0x544443c18c794122a328,0x13422e21524421882834,0xa7150128c54b845ca044,0x31221003850654a10423,0xc100982e3150e1419420,0xe1885c70c10097202900,0x44a878e4252821824991,0x6445c32a1c283284864a,0x7451428707147411434,0x2e5080908304025c546a,0x8232e193244052148319,0xe428862e50906846070c,0xd0962624316183264880,0x45c2208cb862c3050]]
def g243H7 := limbs80 #[#[0x1c00000000040020089,0xe9200000000,0x7d00800000002e0800dc,0x12200000412001c,0x19d00003400000943c14,0xa1060000034b00104c00,0x764000000000000068,0x2040000,0x14600000000000000000,0x584000e794e000001a6,0x180000000c580,0xc2a000000,0x31100000000000000,0x40e0024800000,0xa5000000000007460,0x800000d1c00000000000,0x959400000120c120028d,0x6147b765c8349,0x68b000000000000,0x89000000000,0x0,0x0,0xf1e002cd000000000000,0x201000a8a00000250]]
def g243D8 := limbs80 #[#[0xd30fe907f443eca3f551,0xa3fd31fe90ff543fa81f,0xd25a1e0a82a007f54bfa,0xf8e01541b557aae4fa1c,0x8ce24a14f8c180554604,0xd111002592384a202248,0x74849628c884e0099223,0x12544e2c46060e48a15c,0x883e380114e28734e288,0x248233e12850]]
def g243H8 := limbs80 #[#[0x200800,0x44000000,0xb0000000000000,0x70c000000000000,0xb3e00000000000,0x9b0000000075600000,0x0,0x0,0x0,0x2a27a10000000000000,0x45a000000000000000,0x0,0xdc341c00,0xf240020400,0xb3432c000000,0x0,0x0,0x3180000000,0x0,0x0,0x0,0xc3c001078000000,0x349910000000,0x0,0x18cd020000000000,0x0,0x3800000000000,0xa0000000000000000000,0xca000824000000000008,0x3,0x5d300000000000,0x0],#[0x0,0xa0400000001800,0x79e00000,0x0,0xd8c000000000,0x388c8300153400000000,0x0,0x0,0x168000000001a18,0x70e00000000000,0x0,0x0,0x270000000000,0x110000,0x30200083a82c0000,0x0,0x0,0x0,0x0,0x115000000000,0x103000,0x712880041a0014280000,0x117000003a90000019,0x0,0x0,0x38a0000000000]]
def g243D9 (j : Nat) := if j=0 then 0xa4188201bf else 0
def g243H9 := limbs80 #[#[0xb300000000000000008,0x40005c40193fc800000,0x38400f7da0000,0x14a030000001d0b400,0x1120023803545272,0x36005080000000000000]]
def g243L : Nat → Packing
  | 5 => (7,4,5,0,0,6,0,g243D5)
  | 6 => (38,3,5,0,0,10,0,g243D6)
  | 7 => (34,2,5,0,0,11,0,g243D7)
  | 8 => (11,1,5,0,0,9,0,g243D8)
  | 9 => (1,0,5,0,0,0,0,g243D9)
  | _ => emptyPacking
def g243I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 2 11 4 8 3 1 g243H6
  | 7 => lookupWord 12 179 3 11 6 1 g243H7
  | 8 => lookupWord 12 431 2 11 6 1 g243H8
  | 9 => lookupWord 4 53 1 9 4 1 g243H9
  | _ => fun _ => none
def g243 : Forest := ⟨243,9,fun i => g243Y[i]?.getD (0,0),g243C,g243A,g243L,g243I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P5_0 : block g243 5 0 7=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g243B5 : block g243 5 0 7=true := g243P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P6_0 : block g243 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P6_1 : block g243 6 1 4=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P6_5 : block g243 6 5 33=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g243B6 : block g243 6 0 38=true := (@block_merge g243 6 0 1 37 g243P6_0 (@block_merge g243 6 1 4 33 g243P6_1 g243P6_5))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P7_0 : block g243 7 0 6=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P7_6 : block g243 7 6 17=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P7_23 : block g243 7 23 11=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g243B7 : block g243 7 0 34=true := (@block_merge g243 7 0 6 28 g243P7_0 (@block_merge g243 7 6 17 11 g243P7_6 g243P7_23))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P8_0 : block g243 8 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P8_2 : block g243 8 2 9=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g243B8 : block g243 8 0 11=true := (@block_merge g243 8 0 2 9 g243P8_0 g243P8_2)
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
def g245Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xe007ffffe1ffff9164,0xdc16e000000fc0000fff])),(BitVec.ofNat 152 (word80 [0x44510a204404101144,0xcc00e249249249249249]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfff800fffe1ff8318b,0x3c89500003f000fff000])),(BitVec.ofNat 152 (word80 [0x80602c028040213083,0x3c0140c30c30c30c30c3]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffff00001fffda3d,0x31312000fc003f00003f])),(BitVec.ofNat 152 (word80 [0x80300b0881400a39,0x31110186186186186186]))),((BitVec.ofNat 152 (word80 [0xffffffffffe000462a,0x8b87903f00000003ffc0])),(BitVec.ofNat 152 (word80 [0x902404c0009824628,0x3861514514514514514]))),((BitVec.ofNat 152 (word80 [0x4984,0x67ec8fc000003ffc0000])),(BitVec.ofNat 152 (word80 [0xe038070110e044104,0x42ec8618618618618618]))),((BitVec.ofNat 152 (word80 [0x2651,0x42404fffffffc0000000])),(BitVec.ofNat 152 (word80 [0x100400800010000000,0x820820820820820]))),(0x0,0x0)]
def g245C : List ColumnInfo := [(1,0,244,0,7),(4,0,241,0,7),(16,0,229,0,7),(32,0,213,0,7),(64,0,181,0,7),(128,0,117,0,7),(5,0,240,0,5),(17,0,228,0,5),(20,0,225,0,5),(37,0,208,0,4),(49,0,196,0,4),(81,0,164,0,4),(129,0,116,0,4),(132,0,113,0,4),(144,0,101,0,4)]
def g245A : List (List Nat) := [[],[98,84],[32,100],[32,64,80,96],[64,101],[64,82,96,32],[80,66],[80,98,64,66],[96,32,66,84],[96,82]]
def g245D5 := limbs80 #[#[0x54950443cc5515150110,0x54237e0d7654910e6962,0x841d51c08df835c762]]
def g245D6 := limbs80 #[#[0x3b4a92a0904df7359510,0xdf2caa0221fc5454044,0x437cb12a088779525411,0x10bf6e8a8221be591504,0x4427ebb2a4885fb70549,0x5109fee4b2a213fdd562,0x15427fb8aca906df7359,0x85509fae5b0aa177dcd6,0x418027eb8ec4a84fd74d,0xe765e0dd9a5713d08b88,0x8516283033f26f2dac28,0x208504282001088c2280,0x4000182000101840410,0x182000]]
def g245H6 := limbs80 #[#[0xa0000000088000000000,0x830000001013100001,0x5200000]]
def g245D7 := limbs80 #[#[0xf58910fe54110fe50110,0x59520fe54120bf59510b,0x8950df54950bfd8550bf,0x550ff54520ff54910bfd,0x2a0d82400ff58950ff58,0x62a24ca34fc6c2e92c78,0xa496219a24a92296485,0x42985aa50869820448a4,0x29650a20449821c60259,0x9a11c90c182518588718,0x1c60e19a6263083]]
def g245H7 := limbs80 #[#[0x32040002050000eec104,0x785846b22d11e8800052,0x6d0d902f0e000000,0xc64900030b008000b840,0x76280762790900026320,0x42f0310a54b40f000e43,0x300000a107011]]
def g245D8 := limbs80 #[#[0x489a3407f543fa41fd10,0xa600ab48d58ad424aab]]
def g245H8 := limbs80 #[#[0x20000000000020200a08,0x1c44001a0000000000a,0x280000f19c1f548000,0xecc51781205000000000,0x500000000000000d2ac4,0x1820003035889e45,0xc14008000,0x60000000000000000000,0x828000000000049c23,0x8580000000024d8412c0,0x141a50800000000]]
def g245D9 (j : Nat) := if j=0 then 0x5432101bf else 0
def g245H9 := limbs80 #[#[0x71000754000000000000,0x403c2f2800,0xa3000003da,0x890000000000f4a62,0xb70050000000000,0xd5000000000000000000,0x40400f340000000]]
def g245L : Nat → Packing
  | 5 => (4,4,4,0,0,5,0,g245D5)
  | 6 => (18,3,4,0,0,8,0,g245D6)
  | 7 => (13,2,4,0,0,9,0,g245D7)
  | 8 => (3,1,4,0,0,6,0,g245D8)
  | 9 => (1,0,4,0,0,0,0,g245D9)
  | _ => emptyPacking
def g245I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 23 0 9 2 3 g245H6
  | 7 => lookupWord 7 43 4 12 5 3 g245H7
  | 8 => lookupWord 7 79 3 11 4 3 g245H8
  | 9 => lookupWord 3 59 0 10 2 4 g245H9
  | _ => fun _ => none
def g245 : Forest := ⟨245,9,fun i => g245Y[i]?.getD (0,0),g245C,g245A,g245L,g245I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g245P5_0 : block g245 5 0 4=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g245B5 : block g245 5 0 4=true := g245P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g245P6_0 : block g245 6 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g245P6_2 : block g245 6 2 16=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g245B6 : block g245 6 0 18=true := (@block_merge g245 6 0 2 16 g245P6_0 g245P6_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g245P7_0 : block g245 7 0 9=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g245P7_9 : block g245 7 9 4=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g245B7 : block g245 7 0 13=true := (@block_merge g245 7 0 9 4 g245P7_0 g245P7_9)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g245P8_0 : block g245 8 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g245B8 : block g245 8 0 3=true := g245P8_0
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
theorem g127G : graphValid g127 (boundsBefore K245) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low127 : Lower true (varsX 127) (graphGoal 127) 11 := lower_forest (g:=g127) (i:=0) (hints:=16778563) (before_sound K245 V245) g127G g127T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K127 := extendKnown K245 11 [(127,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V127 : Known true K127 := extend_ok (m:=127) V245 low127 (by decide +kernel)
def g191Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfff647e0a2c1076c99,0x2200000003f000fc0fff])),(BitVec.ofNat 152 (word80 [0x28202e08241036488,0x1041041041041041]))),((BitVec.ofNat 152 (word80 [0x25634900a8df1f6,0xd9a4000000000003f000])),(BitVec.ofNat 152 (word80 [0xcc2563090088d71f4,0xd986baebaebaebaebaeb]))),((BitVec.ofNat 152 (word80 [0xea234c3c9688551,0x54d80000fc003f000000])),(BitVec.ofNat 152 (word80 [0x5706a234c3c9208551,0x14c871c71c71c71c71c7]))),((BitVec.ofNat 152 (word80 [0xffe4b93a1eaa878214,0x7c0003f000fc000003f])),(BitVec.ofNat 152 (word80 [0x9804a91a108a848214,0x6c06186186186186186]))),((BitVec.ofNat 152 (word80 [0x10b8c759f40b063,0x2c600fc000000003ffc0])),(BitVec.ofNat 152 (word80 [0xe000090c6596408003,0x24614514514514514514]))),((BitVec.ofNat 152 (word80 [0x22c13057070590e,0xe157f000000ffffc0000])),(BitVec.ofNat 152 (word80 [0x4010430401802,0x61158618618618618618]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x19d049c814980680,0x9c8ffffffff000000000])),(BitVec.ofNat 152 (word80 [0x1950000800180000,0x88020820820820820820]))),(0x0,0x0)]
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
def g223Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfffffb005b05e209de,0x91f8000000f8000003ff])),(BitVec.ofNat 152 (word80 [0xa40141005301a201d6,0x80d804a5294a5294a529]))),((BitVec.ofNat 152 (word80 [0xfe000d0ea3ca038d70,0x7419a0000000000ffc00])),(BitVec.ofNat 152 (word80 [0xc8066d0ea38a008950,0x7019a9ce739ce739ce73]))),((BitVec.ofNat 152 (word80 [0x7bc61d1e03320,0x50b710001f0001f00000])),(BitVec.ofNat 152 (word80 [0xf02b879c61d1e03120,0x5036139ce739ce739ce7]))),((BitVec.ofNat 152 (word80 [0xfffff21f8db2dd88e2,0x11041003e0003e00001f])),(BitVec.ofNat 152 (word80 [0x4c021e8cb24d0820,0x11041318c6318c6318c6]))),((BitVec.ofNat 152 (word80 [0xc4585e4d4135,0x6626007c0007c0007fe0])),(BitVec.ofNat 152 (word80 [0x7000c008544d0020,0x6260210842108421084]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x11220b03a6606,0x8a8aef800007ffff8000])),(BitVec.ofNat 152 (word80 [0x8000000000124606,0x88800421084210842108]))),((BitVec.ofNat 152 (word80 [0xce98609049009,0x8855dffffff800000000])),(BitVec.ofNat 152 (word80 [0x10008210008008009,0x1c842108421084210]))),(0x0,0x0)]
def g223C : List ColumnInfo := [(4,0,219,0,9),(8,0,215,0,9),(16,0,207,0,9),(1,0,222,0,8),(2,0,221,0,8),(64,0,159,0,8),(128,0,95,0,8),(0,2,141,80,7),(5,0,218,0,7),(0,4,27,192,6),(3,0,220,0,6),(64,2,141,16,6),(66,0,157,0,6),(129,0,94,0,6),(65,0,158,0,5),(192,0,27,0,4),(192,4,27,0,4)]
def g223A : List (List Nat) := [[]]
def g223D6 := limbs80 #[#[0xb2ac2a8798e496558550,0xa19cf83e0976543ccf24,0xdb8259550ce7c9706bb2,0x654379707c12eca879ad,0xbc9b00b2ac3bcb92e0d7,0x6e4b2e73e0f725c165b6,0x3f72cd6a74202b9f26c0,0x1e1707883c7767,0x186071a08]]
def g223D7 := limbs80 #[#[0xe756558550e716558550,0x9df835d9509ef825d950,0xe7b7659550f6b8259550,0xbdb835d950beb825d950,0xf6f8259550ee78259561,0xbdf835d950bef825d950,0xddf835d950def825d950,0xfdb835d950feb825d950,0xdef725c165ef58059561,0xded80dc965bdf835c165,0x529243d8c0268740d800,0x889fc799d0709b469978,0x82f8783886a8a8c9da48,0x410260be1e0c3e21f0c9,0x86c3e0a6e2130e9b8788,0x6e1e0e2170d822f878a9,0x8da6e2170e9b87884672,0x1c3061983878a2c561e0,0x80401e00b84002c3070c,0x58058da621e012369b84,0xb1b80208a1084036198,0x6361]]
def g223H7 := limbs80 #[#[0x5800000000000000b0,0x3000000000000000000,0x32f9000000000000,0xd7000000000000,0x75000000000000004600,0x3400000000000000,0x0,0xd10000]]
def g223D8 := limbs80 #[#[0x965543f930aa1fc58550,0x2ac3fc98650fe2c32877,0x50ff2c0a85ef725977ab,0x77d65543fb30aa1fd585,0xcbb2a17fdd950bfaeca8,0xc161bfee0b0ffb76543f,0xa87ef72596ffb82cbfdd,0x3feb82cbff54560ffaec,0x99351fc31c4b86006000,0x105a4a6d2ea183c26c4b,0x8a50fa0abde75cdf9a73,0x360c38868781361c42c6,0x4343c82f061c49878691,0x8b0f0e2c03a48b0f0e0c,0x11040363c38310b1d324,0x30e21a40997931c6c317,0xf026c38858c393a48b8,0x24d0c98b81324c38a18f,0x601b8b0904076417830e,0x384c09b0e21c3901c1c2,0x43881c9d20dc09b16120,0xc31310b193a407830a6c,0x110191e08d8710b1a360,0x3180978710f1c3844787,0xd186070880e428068b9,0x74642430]]
def g223H8 := limbs80 #[#[0x9499c133f27e0005b402,0xd3c1dbc0d22973,0x12000d09200003d6d10,0x8dc5000002]]
def g223D9 := limbs80 #[#[0x10fd987f561fe943f950,0xfd61ff547fd60ff543fd,0x99d4c64b1986c00ff597,0xe62e4160862236d86ab4,0x68218872e41438608870,0x2c59631848608871232c,0x859a42e08620c982188a,0x8623071e59208623473,0x4090c41a08622c79a31e,0x1648c680b862]]
def g223H9 := limbs80 #[#[0x45800000018000002,0x11c0000005980,0x1c80000ca80000000000,0x1bb52000000286005a,0xf00000000000003c200,0x44000000001ea0000000,0xe60000000580000000,0x28000011568000000000,0x1e00000249a84]]
def g223D10 (j : Nat) := if j=0 then 0x3148300443ff else 0
def g223H10 := limbs80 #[#[0xd300b0660000000000,0x682200000000c10000d5,0x17000039000000,0x9400000000]]
def g223L : Nat → Packing
  | 6 => (10,4,5,0,0,7,0,g223D6)
  | 7 => (20,3,5,0,0,10,0,g223D7)
  | 8 => (22,2,5,0,0,11,0,g223D8)
  | 9 => (10,1,5,0,0,9,0,g223D9)
  | 10 => (1,0,5,0,0,0,0,g223D10)
  | _ => emptyPacking
def g223I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 2 83 0 8 4 0 g223H7
  | 8 => lookupWord 5 29 4 9 5 0 g223H8
  | 9 => lookupWord 5 83 1 9 5 0 g223H9
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
theorem low223 : Lower true (varsX 223) (graphGoal 223) 11 := lower_forest (g:=g223) (i:=0) (hints:=16778819) (before_sound K191 V191) g223G g223T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K223 := extendKnown K191 11 [(223,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V223 : Known true K223 := extend_ok (m:=223) V191 low223 (by decide +kernel)
def g239Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffd820b824125c536e,0xc5000000fc0000000fff])),(BitVec.ofNat 152 (word80 [0xa0820b804121c1222,0xc5249249249249249249]))),((BitVec.ofNat 152 (word80 [0x6c493e0a5c368749,0xb200000000003f000000])),(BitVec.ofNat 152 (word80 [0x336c493e0a0c168749,0xb29e79e79e79e79e79e7]))),((BitVec.ofNat 152 (word80 [0x39f32e0421132d23,0x900003f000fc003f000])),(BitVec.ofNat 152 (word80 [0x5c38f12c0421132522,0xc30c30c30c30c30c3]))),((BitVec.ofNat 152 (word80 [0xff90dc4d96ac4e9188,0xfc003f000fc003f])),(BitVec.ofNat 152 (word80 [0x6010d845002c420188,0x82082082082082082]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x612c2fa4a934e42,0x2003f000000000ffffc0])),(BitVec.ofNat 152 (word80 [0x80020202ba40804840,0x20514514514514514514]))),((BitVec.ofNat 152 (word80 [0x8a90581d3a05810,0xbffc000003ffff000000])),(BitVec.ofNat 152 (word80 [0x81d2a05800,0xd618618618618618618]))),((BitVec.ofNat 152 (word80 [0x674430492480a0b5,0x54fffffffc0000000000])),(BitVec.ofNat 152 (word80 [0x4504004000008015,0x10820820820820820820]))),(0x0,0x0)]
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
theorem low239 : Lower true (varsX 239) (graphGoal 239) 11 := lower_forest (g:=g239) (i:=0) (hints:=16778595) (before_sound K223 V223) g239G g239T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K239 := extendKnown K223 11 [(239,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V239 : Known true K239 := extend_ok (m:=239) V223 low239 (by decide +kernel)
def g247Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x809c7c90734a243250,0xfe0000001fc07f])),(BitVec.ofNat 152 (word80 [0x80945c90520a203052,0x24489122448912244891]))),((BitVec.ofNat 152 (word80 [0x55ab449950b6138090,0x7f0003f80])),(BitVec.ofNat 152 (word80 [0x5589449950b6120008,0xb162c58b162c58b162c5]))),((BitVec.ofNat 152 (word80 [0xcac72dc01410da7100,0x7f0003f80fe00000])),(BitVec.ofNat 152 (word80 [0xc2822dc01410903100,0x60c183060c183060c183]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x843223dea84c988c00,0x3f8001fc0000003fff])),(BitVec.ofNat 152 (word80 [0x2221462840888801,0x42850a142850a142850a]))),((BitVec.ofNat 152 (word80 [0x10a99a2d2c92ec42a0,0x1fc0000000000fffc000])),(BitVec.ofNat 152 (word80 [0x1029822d28004c4285,0x8b162c58b162c58b162c]))),((BitVec.ofNat 152 (word80 [0x6154172348210167df,0xe0000001fffff0000000])),(BitVec.ofNat 152 (word80 [0x2054122000000146d6,0xc183060c183060c1830]))),((BitVec.ofNat 152 (word80 [0x3f00c064938102186f,0xfffffffe000000000000])),(BitVec.ofNat 152 (word80 [0xd0000008181020028,0x10204081020408102040]))),(0x0,0x0)]
def g247C : List ColumnInfo := [(1,0,246,0,10),(2,0,245,0,10),(4,0,243,0,10),(16,0,231,0,9),(32,0,215,0,9),(64,0,183,0,9),(128,0,119,0,9),(0,2,165,80,7),(0,32,82,133,7),(18,0,229,0,7),(34,0,213,0,7),(130,0,117,0,7),(1,32,82,132,6),(16,2,165,64,6),(48,0,199,0,6),(64,2,165,16,6),(96,0,151,0,6),(128,32,82,5,6),(160,0,87,0,6),(80,0,165,0,5),(80,2,165,0,5),(144,0,103,0,5),(192,0,55,0,5),(162,0,85,0,4)]
def g247A : List (List Nat) := [[],[32,100]]
def g247D6 := limbs80 #[#[0x5358725795e4d8654d61,0x516354d61bb4e819458d,0x5e579361953586e57a56,0x586af3a06518654d61e9,0x8458d61ab5e8d9461953,0x1790611635872f185e41,0xeaf3a06538558d61cbce,0xdc553f155957458f7154,0x975937154e5f3a065d64,0xf79661974dc55387d6a3,0x553d55e57935db7154f0,0x5937154f35795e4d86dc,0x9661984dc55397ce8198,0x3a7ce819461b7154f0f7,0x57654f65965e418458d5,0x613815d953e55e1783e0,0x7ce8575e017458e9f3a0,0xe5852423c2c120c0600a,0xea8a29c968676706a645,0xf04104fc1080000c4bea,0x41304000000001c1040,0x130400000013]]
def g247D7 := limbs80 #[#[0xb1aa6b0eb5e156350d61,0xc3ad79361953587caf2a,0x4d8558d61b79c8308b1a,0x654fcaacab1ee2a9db5e,0xacaac6a1ac395f85e0d7,0xa86b0fb5e556350d61f6,0xed59458d535875ed30b2,0x8654d61f6bca2c6a9ac3,0x875ef28c32a6b0ebd651,0x2b08b1ac3af585611635,0x6b0dbde558458d61d7bc,0x595e11635875eb0bc22c,0x58d61f6bc9b0ab1ac36f,0xcbf0ab2ac6a1ebd65385,0xeb2a877d7916156350f,0x9f755d163dc553a7ecb5,0x45937154feaf2ab1ee2a,0x553afacbac9b8aa7db57,0xb0cba6e2a9d7de5d64dc,0xb8aa75f7965d37154f3e,0x7de5176dc553eebc9aed,0x937154f7af26c36e2a9d,0x3afacc2c9b8aa7db5845,0xcc26e2a9d7de6164dc55,0xaa75f7966137154f3eb0,0x65186dc553afbca30db8,0x6354f3ef28c36e2a9e7d,0x6fcb2e8b1aa7e5d655d1,0x22c6a9df6e418458d53b,0x775f956116354fcbacac,0x18759153f2eb2f08b1aa,0x54e7bf26c3ac8a9cfee4],#[0xc32ecba2a73dd93e1d64,0xeca9ed7e17835d953c7f,0xf584e057654fbaf07c0a,0x35d953cfbc2702bb2a79,0xebf720c22eca9f57e178,0xf00ba2c75df936117654,0xb1e7e5d7805d163d7cb2,0x855957458f3f6ebc02e8,0xd163afbc8aeaba2c7a7f,0xbeebc1acab1d7de4575d,0x9baac7bd783e057558fc,0xde1561e022800afdc830,0x3c06fcd81862b85108d0,0xcab14ea7c4c890d159f8,0xb1aeb4566cc7987af75a,0xf83ea7b6f0dd5ba5708d,0x46b8b91361ac2f82effd,0xda39436764dd98b24a46,0x956a6cd582ad556ea653,0x8ab12615c0d7def45d0b,0xf06907ceb97727648c73,0xbc0a5918a158682d51e2,0x46284f4bc1f1780509f8,0x3478bc1651a2564f162f,0x378423378bc013102a09,0x3954906101ac1546904d,0x724182093814a1844154,0x1b93821235c8e2707045,0x2b208c332580260d80c8,0x7c10c2c1508d90460821,0x41bc409900b91c010542,0x30519820982133304000],#[0x28cc1028cc1001731180,0x8c0101ccc104c1002608,0xc01b901b202663204018,0x4100709bc21414072389,0x70360090383e2820e068,0x8001f0836441a1830,0x70061407c214091a0808,0x4100f8410a78420014e2,0x3040d002120407082c30,0x1370054]]
def g247H7 := limbs80 #[#[0x32a721e200101db0a36,0x85f00460ca37ea40,0x890fd501a84704474020,0xa78a29a87e7aa0453922,0x1a8e250df]]
set_option maxRecDepth 16000 in
def g247D8 := limbs80 #[#[0xed56354d61ed56350d61,0x9f78754d61af58654d61,0x9f7815d543af78558d61,0x9f586dc5539fb805d943,0x9f7815d953e5d6558d53,0xbf78550d61ef56550d61,0xef78458d61ef58458d61,0xef78558d61ef58558d61,0xddf7558d43edd6558d43,0xbbf8559143dbf7559143,0x9ff855d9439fd86dd543,0xdf574dc553fd563dc553,0xbf586dc553df576dc553,0xdf584dc553df564dc553,0xf5f8558d53df586dc553,0xdf7815d953bdf835d953,0xbfb805d163ddf835d953,0xedf83595639fd85dd163,0xbdf835d563bf7815d563,0xfdd8558d439fd85dcd64,0xdfe8759543fdf8558d43,0xfdd7458d53ff564dc553,0xfdf8458d53fdd8458d53,0xbfd8759153fbd7459153,0xdfd765d153bff8759153,0xfdf835d953bff865d153,0xdfd845d953bff845d953,0xefd655d163dff845d953,0xdff755d163dfd755d163,0xefd65dd163bff855d163,0xbfd85dd163dfd75dd163,0xfdf835d563ff7815d563],#[0xa06c03e000dfd84dd563,0x2161d01921641360f00b,0x283e238433e2f029a24c,0x258c54e5184e24ac46e4,0x7266e069a65c62e5f85b,0xa886a82c7de7a877a754,0xa9bc9ae9809529248de8,0xac6aa8a7aa4ca2ea089d,0xe0bb2b94b5eb40b2aafc,0xacb4c86c70c52c34c0eb,0x9690352f8b80447cf0cc,0x6378b80911e4e2e01417,0x5e2e0a3184d2f928f069,0x362f9197838a8c807c6a,0x698305a5c3e2e0111456,0x7e466c5c3e2e01f0f8b8,0x18460f93849b8b805080,0x1968c449c5c307e2e0a6,0xe2c6a3285a1e912f8b8,0x8b8044928c10b658da4e,0xe0111520491d968d922f,0xf05978b80b6564238be2,0x6515204c5444362f928,0x8b831044811e4a38be2e,0xe1e0e2a60e1c580f8597,0x61b878388230e9861565,0x8b8198386e1c308e0e2a,0xc308a6e0e1e2651e9787,0xa66e2e013238b81984c4,0x84ad938b804c6504e642,0xf8b81907e4e2e0661316,0x664e2e0a107201d9b170],#[0xd9b938b82841c8c5c36,0xa98504e1e2e0a6141717,0x80506e461e2e01417838,0xc3e1e2a4c6269b178b87,0x823878b82907928e60e5,0x611e18643e2e0a51f0f1,0xa5e0c623931b8a978034,0x68f8b804851543e128e2,0x120e18514656148c4178,0x1141592044c311052195,0x860c483983144100e26e,0xe114409b84384c5c564,0x14a4183423843120d222,0x840343b8598508a16126,0x6064e11b8421903e1140,0x5a00e142385903140862,0xa0102186809690512112,0x443110c4839943100824,0x216151165a41441842a,0x21819031514a5e110845]]
def g247H8 := limbs80 #[#[0x15843340112003133d4d,0x8000c26c19a2ce0dc98,0xee10cafb1d5b10350002,0x72a9b08abb2,0xc2100094200072f,0xdf410000000001050000,0xc3c61c000122502000f2,0x3d000fb561820171ed9f,0x7000000cba000240d04c,0xa3f00b0b922bc03014b1,0xaf34b29000813043000,0x41b6360000000008008,0x382000331db2000216c3,0xc09027d20f25f37,0x300043b000b950006280,0xb06000c1af24111cad33,0x3800000090e000000815,0xfa143e0000006,0xe1f000000b2300090f00,0x112339107f32a3a50c]]
def g247D9 := limbs80 #[#[0x543586fbb8aa7bd58d61,0xa2c3fd5cd61feaa6b0ff,0x43f7aa8a1fdd6350ffab,0xdff7550efebaa87ef591,0xbb8aa77fdd943bfaeca1,0xd953bfee8a9fdd6354ff,0xb1dff7458effbb2a77f5,0xeffb9ac97fdd563dfaca,0xf5d153ffac8a9ffd6550,0xe8b1ffd7458ffebb2a7f,0x3ffbaac7ff5d563ffe,0xcc79582503a85986e06e,0x5ae656ca3527a1f3de6f,0xba915116073d7740d6d9,0xd038d6ff5b9b1352e7fc,0x1608638dcb905e2c08c7,0x658d478b011243e6c917,0x2088b498b046283a5490,0x1e3462225223c58058f,0x3cb130e2c0447149316,0x8b02610325c30f160223,0x11c325878b0e02236187,0x434d87160104064b8316,0x8b0131b0e2c04470a162,0x3922e1c581314240e6c9,0x60284a4c30f160223032,0x362c050711161e4c29b1,0xc2c3c38a360103880805,0xc38a3121b262c3812c31,0x3c58701218a8887912e0,0x1688392e18783111242a,0x41324222a4878b0614c5],#[0x580a0c90866c23b16028,0xcb0d261c580893930a6c,0xa1595262c3808951c90e,0x4a90548c3c91b0a5c580,0x32393161c09]]
def g247H9 := limbs80 #[#[0x11000020124b6130071,0xc0f00000000000000,0x708000,0x3b3000000000a2d0,0xe3af19e0400000000,0x81000b24000c37596000,0x31740c00001ec40015e,0xd1b138731d0900000,0xd14000000b1c110,0xe30e16000900c1d9350,0x701427a9,0x32000e9ee21006000429,0x93480a0000000000000,0x1a0000000000005bb00,0x3000000000000000339,0x93b0006280008120001,0xd2300000000000000,0x10d03f0009ab000000,0xe220e3c311a8a00073d0,0x39300092200000072,0x5000000000000000000,0x3000000c2c0000000008,0xa0b00000022b22aba,0x0,0xc071b700021890e0a00,0xb3600062fb0200,0xb25000000f3e000,0x43300011f0000000,0x61322600]]
def g247D10 := limbs80 #[#[0x64ff58ffd53ff50ff561,0x8c68a02362a1c8d803fd,0x889a50c486280904b964,0x28601e69050e18a05083,0x2258c61218a02659060e,0x12]]
def g247H10 := limbs80 #[#[0xaac0004d01164a008020,0x4801eb000004a600001c,0x13aa9eae800000966,0x4000927b32de9a007840,0x55c7b000007c5ea0af4,0x3001c3e9c006b86968a0,0x283818000052335d300,0xd2940000186480a23a00,0xc]]
def g247D11 (j : Nat) := if j=0 then 0x3148310023ff else 0
def g247H11 := limbs80 #[#[0x3000000490000b1,0x0,0x9400820000000000002b]]
def g247L : Nat → Packing
  | 6 => (22,5,5,0,0,8,0,g247D6)
  | 7 => (68,4,5,0,0,11,0,g247D7)
  | 8 => (65,3,5,0,0,12,0,g247D8)
  | 9 => (30,2,5,0,0,11,0,g247D9)
  | 10 => (5,1,5,0,0,8,0,g247D10)
  | 11 => (1,0,5,0,0,0,0,g247D11)
  | _ => emptyPacking
def g247I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 7 37 5 10 5 1 g247H7
  | 8 => lookupWord 20 127 4 12 7 1 g247H8
  | 9 => lookupWord 19 193 4 12 7 1 g247H9
  | 10 => lookupWord 9 61 5 10 5 1 g247H10
  | 11 => lookupWord 1 37 0 8 3 1 g247H11
  | _ => fun _ => none
def g247 : Forest := ⟨247,11,fun i => g247Y[i]?.getD (0,0),g247C,g247A,g247L,g247I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P6_0 : block g247 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P6_1 : block g247 6 1 21=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g247B6 : block g247 6 0 22=true := (@block_merge g247 6 0 1 21 g247P6_0 g247P6_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P7_0 : block g247 7 0 7=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P7_7 : block g247 7 7 61=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g247B7 : block g247 7 0 68=true := (@block_merge g247 7 0 7 61 g247P7_0 g247P7_7)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P8_0 : block g247 8 0 10=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P8_10 : block g247 8 10 29=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P8_39 : block g247 8 39 26=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g247B8 : block g247 8 0 65=true := (@block_merge g247 8 0 10 55 g247P8_0 (@block_merge g247 8 10 29 26 g247P8_10 g247P8_39))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P9_0 : block g247 9 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P9_2 : block g247 9 2 20=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P9_22 : block g247 9 22 8=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g247B9 : block g247 9 0 30=true := (@block_merge g247 9 0 2 28 g247P9_0 (@block_merge g247 9 2 20 8 g247P9_2 g247P9_22))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P10_0 : block g247 10 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P10_1 : block g247 10 1 4=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g247B10 : block g247 10 0 5=true := (@block_merge g247 10 0 1 4 g247P10_0 g247P10_1)
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
def g251Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x6cd87dc5040000000,0xff00000000ff00ffff])),(BitVec.ofNat 152 (word80 [0xc9031c1040212121,0x21212121212121212121]))),((BitVec.ofNat 152 (word80 [0x60b16689ea48000000,0xff0000ff0000])),(BitVec.ofNat 152 (word80 [0x60b12688ca008b8b8b,0x8b8b8b8b8b8b8b8b8b8b]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x300085ae9a3000000,0xff0000ff00ff000000ff])),(BitVec.ofNat 152 (word80 [0x3000042e083060606,0x6060606060606060606]))),((BitVec.ofNat 152 (word80 [0x4b789000a4be0000ff,0xff00000000ffff00])),(BitVec.ofNat 152 (word80 [0x300800024be141414,0x14141414141414141414]))),((BitVec.ofNat 152 (word80 [0xa422fe2403b000ff00,0xffff000000])),(BitVec.ofNat 152 (word80 [0xa422dc000330585858,0x58585858585858585858]))),((BitVec.ofNat 152 (word80 [0xbc0950031552ff0000,0xffffff0000000000])),(BitVec.ofNat 152 (word80 [0x8c0850011140606060,0x60606060606060606060]))),((BitVec.ofNat 152 (word80 [0x919621a01a05ffffff,0xffff0000000000000000])),(BitVec.ofNat 152 (word80 [0x101420a00800808080,0x80808080808080808080]))),(0x0,0x0)]
def g251C : List ColumnInfo := [(1,0,250,0,10),(2,0,249,0,10),(8,0,243,0,10),(16,0,235,0,10),(64,0,187,0,10),(0,2,169,80,9),(32,0,219,0,9),(128,0,123,0,9)]
def g251A : List (List Nat) := [[],[48,100]]
def g251D10 := limbs80 #[#[0x775a8bc1bc0ff593f561,0x19e72ea0]]
def g251D11 (j : Nat) := if j=0 then 0x3e68183ff else 0
def g251H11 (j : Nat) := if j=0 then 0x11b else 0
def g251L : Nat → Packing
  | 10 => (2,1,3,0,0,5,0,g251D10)
  | 11 => (1,0,3,0,0,0,0,g251D11)
  | _ => emptyPacking
def g251I : Nat → Nat → Option (Nat × Nat)
  | 11 => lookupWord 1 2 0 5 1 0 g251H11
  | _ => fun _ => none
def g251 : Forest := ⟨251,11,fun i => g251Y[i]?.getD (0,0),g251C,g251A,g251L,g251I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P10_0 : block g251 10 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P10_1 : block g251 10 1 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B10 : block g251 10 0 2=true := (@block_merge g251 10 0 1 1 g251P10_0 g251P10_1)
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
def g253Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffc6086b63c1b29c00,0x3f00000003ffff])),(BitVec.ofNat 152 (word80 [0x8006080a20c1928402,0x49249249249249249249]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xc01e730d063d431410,0xfc0000fc0fc0000])),(BitVec.ofNat 152 (word80 [0x59e520d062d011410,0xc30c30c30c30c30c30c3]))),((BitVec.ofNat 152 (word80 [0xffcb4ec51e023502c0,0x3f00003f03f00003f])),(BitVec.ofNat 152 (word80 [0x90842c51e02250080,0x82082082082082082082]))),((BitVec.ofNat 152 (word80 [0x2096ff30340139a0,0xfc0000fc0000000fc0])),(BitVec.ofNat 152 (word80 [0xe2096f51034013881,0x86186186186186186186]))),((BitVec.ofNat 152 (word80 [0x2115305553c94310,0x3f00000000003ffff000])),(BitVec.ofNat 152 (word80 [0x102105304110484305,0x14514514514514514514]))),((BitVec.ofNat 152 (word80 [0x14ea12c020c6c3ef,0xc0000000ffffc0000000])),(BitVec.ofNat 152 (word80 [0x20002802c000c2c366,0x18618618618618618618]))),((BitVec.ofNat 152 (word80 [0x280084888c08e40f,0xffffffff000000000000])),(BitVec.ofNat 152 (word80 [8,0x20820820820820820820]))),(0x0,0x0)]
def g253C : List ColumnInfo := [(4,0,249,0,10)]
def g253A : List (List Nat) := [[],[80,66]]
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
def g254Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfff401791c067c476a,0x98000000000000fc003f])),(BitVec.ofNat 152 (word80 [0xa6401790c063c0662,0x18965965965965965965]))),((BitVec.ofNat 152 (word80 [0x4848bf221914834d,0x6a000000fc003f000fc0])),(BitVec.ofNat 152 (word80 [0x330848bf0018148309,0x4a0c30c30c30c30c30c3]))),((BitVec.ofNat 152 (word80 [0x39f32f0460132523,0x300003f000fc003f000])),(BitVec.ofNat 152 (word80 [0x5c18f12f0420112123,0x20c30c30c30c30c30c3]))),((BitVec.ofNat 152 (word80 [0xff90dc4c97ac4e9988,0x2000fc003f00000003f])),(BitVec.ofNat 152 (word80 [0x6010d80413a8428988,0x228a28a28a28a28a28a]))),((BitVec.ofNat 152 (word80 [0x612c2fb4a934e42,0x2203f00000000003ffc0])),(BitVec.ofNat 152 (word80 [0x80020240bb42824c40,0x2071c71c71c71c71c71c]))),((BitVec.ofNat 152 (word80 [0x8a90580d3a05810,0xbdfc000003fffffc0000])),(BitVec.ofNat 152 (word80 [0x8041805010,0xa1410410410410410410]))),((BitVec.ofNat 152 (word80 [0x674430492480a0b5,0x54fffffffc0000000000])),(BitVec.ofNat 152 (word80 [0x6504004004000004,0x14820820820820820820]))),(0x0,0x0)]
def g254C : List ColumnInfo := [(4,0,250,0,10)]
def g254A : List (List Nat) := [[],[50]]
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
theorem low254 : Lower true (varsX 254) (graphGoal 254) 11 := lower_forest (g:=g254) (i:=0) (hints:=555832640) (before_sound K253 V253) g254G g254T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K254 := extendKnown K253 11 [(254,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V254 : Known true K254 := extend_ok (m:=254) V253 low254 (by decide +kernel)
def g255Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x7ffec01d60ce405ca,0x304995890234511b807])),(BitVec.ofNat 152 (word80 [0x8824282000009201af,0x80401118100145009007]))),((BitVec.ofNat 152 (word80 [0xf80000e01470849200,0xc1f81cd94004012047ef])),(BitVec.ofNat 152 (word80 [0x1d7160e01050859300,0xc1d01cd90004002047a7]))),((BitVec.ofNat 152 (word80 [0x100880412004,0x55201bdc0408646009f])),(BitVec.ofNat 152 (word80 [0x38e0e0000080402004,0x55201bcc0008002009f]))),((BitVec.ofNat 152 (word80 [0x1fe0000800010c00,0x59200a6c08008880801])),(BitVec.ofNat 152 (word80 [0x30c0c0000800010c00,0x59200a6c00000000800]))),((BitVec.ofNat 152 (word80 [0xffe011696f33b85243,0x7a2002b6c518f0f07118])),(BitVec.ofNat 152 (word80 [0x608280140d20480440,0x2e242026c50880d02018]))),((BitVec.ofNat 152 (word80 [0x7f089bc0a58c4,0x35ac0b261f00ff8250])),(BitVec.ofNat 152 (word80 [0x430b00100040001210,0x3a25a801241e00fd0240]))),((BitVec.ofNat 152 (word80 [0x198ef0c0cc9031,0xb40a5120381fff000462])),(BitVec.ofNat 152 (word80 [0x820c000080020000bb,0x1009800038136f000040]))),((BitVec.ofNat 152 (word80 [0x1e0f0103136138,0x8c166443fe000000784])),(BitVec.ofNat 152 (word80 [0x41014c1220804c000,0x4000464002e000000500]))),(0x0,0x0)]
def g255C : List ColumnInfo := [(4,0,251,0,12),(8,0,247,0,12),(1,0,254,0,11),(2,0,253,0,11),(16,0,239,0,11),(32,0,223,0,11),(64,0,191,0,11),(128,0,127,0,11),(0,2,173,80,10),(18,0,237,0,10),(16,2,173,64,9),(48,0,207,0,9),(64,2,173,16,9),(66,0,189,0,9),(130,0,125,0,9),(0,32,82,141,8),(3,0,252,0,8),(17,0,238,0,8),(33,0,222,0,8),(34,0,221,0,8),(65,0,190,0,8),(80,0,173,0,8),(80,2,173,0,8),(96,0,159,0,8),(129,0,126,0,8),(144,0,111,0,8),(160,0,95,0,8),(192,0,63,0,8),(0,4,27,224,7),(1,2,172,80,7),(1,32,82,140,7),(4,32,82,137,7),(8,32,82,133,7),(32,2,141,80,7),(128,2,45,80,7),(128,32,82,13,7),(5,32,82,136,6),(9,32,82,132,6),(49,0,206,0,6),(64,4,27,160,6),(128,4,27,96,6),(129,32,82,12,6),(136,32,82,5,6),(161,0,94,0,6),(81,0,172,0,5),(81,2,172,0,5),(97,0,158,0,5),(112,0,141,0,5),(112,2,141,0,5),(133,32,82,8,5),(137,32,82,4,5),(145,0,110,0,5),(176,0,79,0,5),(192,4,27,32,5),(208,0,45,0,5),(208,2,45,0,5),(224,0,27,0,4),(224,4,27,0,4)]
def g255A : List (List Nat) := [[]]
def g255D7 := limbs80 #[#[0x272e71fba5957458140,0x140bcabc26d5765d1605,0x60502d6af09b565d7458,0x45c140b59bc36d5975d1,0x5d57050256e727b85957,0xd9655d140b93bc46d586,0xba065574502b2e703a85,0xa5681765d140e8b9865d,0x6ec9a55d974502b6af09,0xf09b869f9159150d8ad8,0xd7c36e1a7e45645428f9,0x87df1db869f9159150a3,0xa1f5c7ae1a7e4564542,0x54262f72ea85d9745915,0x9150b8afc26e1765d164,0x164542e27f0db85d9745,0x645c160a8bdcaae1765d,0x55d164582f0ef11855d5,0x61d7459160d8b987ec1a,0xd5875d164582e2ef01b5,0xdb561d7459160b8afc26,0xc2695a065f81592e27f0,0xbf09a5681765d164a3e7,0xc0a890786048301802b2,0xb199816951392108f0d8,0x2422a11f9e1c9]]
set_option maxRecDepth 16000 in
def g255D8 := limbs80 #[#[0xe0a074b9975957458140,0x55d170502cdddb30aba2,0x76cc2aeab828166e6db8,0x5db3b0695745c540b2f,0x17054345ed32edc2ae8a,0xc32a8b82a1e4ee197455,0x7175e85645c150d2f34f,0x542cdcda70cba2e0a86d,0xeab82a1a5e69975e1170,0x4619755c150d2f30dd22,0xcbcda70cbaae0a8597bb,0x8aa1679ec9a85d971542,0x5745c160b3af66d42ecb,0xbaf48b2ae0b059b9b4e1,0x171eed1755957058363c,0x5c560b9e760d2aecb8ac,0x49c2ae8b05ce7b269576,0xe5d5a0e51655c345ebb3,0x64a7cf64d2b2fc0ac995,0xa2c0a05cafb2695765d1,0x98755160502f9ddcaeaa,0x5776cc3aa8b02817aeed,0xa07cb9975957458140f,0x5d160502f5ddd2caba2c,0x2ec2ae8b0281f2e5d985,0x7cb9766557458140eb73,0x60503adccbb2aba2c0a0,0x2ae8b0281f2e5d9a55d1,0x9976957458140dd734cd,0x3e5cdaaecba2c0a075b,0x8b0281f2e6e1765d1605,0x65d7458140f9732ed32e],#[0xdddab2eba2c0a075b9b5,0x2817aeed19759560503a,0x7558140ed7768cbacab0,0xb350baac0a05f3bb4655,0x3be6dba85d56050277dd,0x81408ff373d42eab0281,0x2baac0a04febb26a5755,0xed1a95d5605027edd9b5,0x9f7369d4aeab02813ee,0xac0a04bf9b8ea5755814,0xa46556050375cbb748ca,0x736fd232ab02819ee65f,0xa06cfba75d995581409f,0xd9605032fdd3b2ecaac0,0x8d42ecb02817baec9a55,0xafbb66958758140bd776,0x502bf5d934acbac0a05,0xb2eb02815f6ecda565d6,0x865d5545c140af7768d2,0x36dcd3b0caa2e0a07d39,0xb828176eee1655d17050,0x15745c140bb7774b2ae8,0xcd330aba2e0a079b9866,0x81e6e69b855d170503cd,0x45c140f3730ccaae8b82,0x32aba2e0a079bb866557,0x6e619a55d170503adccb,0x140f3770cd2ae8b8281e,0xba2e0a06db9a6695745c,0x1ba55d170502edddb34a,0xf3736ac32e8b8281b6e6,0xe0a06d7ba85d5655c140],#[0x8595705026fcdbf50b2a,0x30cc2aeab82811fe6e7a,0x7979b5619755c140f2f,0x970502eddda32cbaae0a,0xd2b0cb82816eeed1a561,0xb9b0ea17655140b3f76e,0x503e5cd82ecb2ae8a04f,0xcaba281b2fea17659574,0x7ea1655d1409f7361d42,0x7dcd8752b2ae8a04dbdb,0xa28136f6dfa959574502,0x1955d140f17b0cbb30ab,0xc3740caae8a06db976e8,0x1aeee1ba0655745035dc,0x5d140f17b0cbb32aba28,0x40bb2e8a06cbfa65d995,0xe619a05d9745036dcd2b,0x40bb5f64d2aecba281f2,0xb2e8a078bd86695765d1,0xda561974503c5edab0cb,0xef361cc2eab2a8166fed,0xaa056f9b0e617659540a,0x61d65502c7edbd50bb2c,0x6fcc30eb2a814fe6c398,0x53f9b0aa58759540a3fb,0x655023fcd8750cbacaa0,0xc30cbaa811feedda0e61,0xfb6661865d540a7f760c,0x297edb730c32eaa052f,0xcbaa816cfed1a5619755,0x6a5865d540a7f760d4b0,0xefd9b52c32eaa053efb2],#[0xa814efed1a9619755029,0x865d540a7f36154b0cba,0xab51cb2eaa053bdb4aa5,0x47f6dea95d9855031bfd,0xd940afd764cab20bb281,0x4caaeca06aed86e89955,0xa63a2655765031f6cc74,0xb57f68d2b0cbb2818fb,0x2eca058ffb7695865d94,0xa46617650355fd3748cc,0xf760d2b30bb281cafe9b,0xa053efb2695985d940a7,0x61765029efd9b4acc2ec,0xcd2b30bb2814efed1a56,0x1ffb7695985d940a5ff6,0x65031dfda3534c2eca05,0x32ec32812ef6dfa46558,0xb069597e1940d57f4dd2,0x23dfda34dcab0ea053fb,0xc3a818fe65ba06558750,0x9b9561d40c7f72dd032a,0xdd834bcb30ea04bbfb46,0xa1f4e6d974551705429f,0x45c150fa736aba2c8b82,0x2eab22e0a87cb9965d16,0x5e6a57559170543e3ccb,0x150f2f70cd2ae8b82a1b,0xba2e0a86d79a6695745c,0x597565170542eddda32c,0xdaf74cbab28b82a1d5e6,0xa8a85d7bb4659755c150,0x85d954543c9f5c2ecba2],#[0xb70d3f22b22a165f6dea,0x863f6b869f9159150c7e,0x164543e1ebb34aba2c8a,0xbb2e8b22a1e2f6a1765d,0xbdb85d97459150f17d50,0x543c5f5c2ecba2c8a878,0xe8b22a16afed9a85d164,0x7aa17459150b57b6d542,0xd77d9350bb2c8a859bdb,0x22a16b7ecda85d964542,0x17659150b57f68d42ecb,0xda550bb2c8a858ffb76a,0x163f6dea85d964542d5e,0x59150a7df64d432eb22a,0x50cbac8a853dfb36a197,0xfed9a865d645429dfda3,0x50a3ff6ed432eb22a14b,0xbac8a853bdb4aa197591,0xea865d6454297edb550c,0x1ff6ccc2ecba2a147f6d,0x8a858fdb6a61765d150b,0x5d9745424fedd530bb2e,0x66d42ecba2a167bec9a8,0x59bfb46a1765d150b3bf,0x74542cdeda550bb2e8a8,0x4b0cba2a147f6e6a85d9,0xfb2661945d95093fb6fd,0x829efd9b30ca2eca853e,0x8b82c1f2e6d974551705,0x5d1645c160f9730aba2c,0x5cdaae8b22e0b07cb995,0x2c1f1e6157559170583e],#[0x645c160bd7768c2ac8b8,0x2b08ba2e0b05cfbb7615,0xe6e615845d170583e5cb,0xc160f9734cc22e8b82c1,0xaba2e0b05cfbba595745,0x5d5656117058367cd334,0xf2f30abab08b82c1f1e,0x2e0b059fbb7615845c16,0xa45d57058367dd32eaca,0xf768c2aeab82c1b5e617,0xb07cb9766817455160ba,0xd15458375cd3340ba2a8,0x1d42eaaa2c166f6dea85,0x7f9b0ea197551609ef36,0x458375cd2b40ba2c8b04,0xae8b22c1e2f61d855d16,0x876957459160bd7760d2,0x3c5edab0eba2c8b078bd,0xb22c1e2fed5875d16458,0xa17559160bc7f68c2aea,0x7d9350baac8b04efbb06,0xc13b7ecda85d56458277,0x5591609d7f68d42eab22,0x750baac8b04ef9b0ea17,0xaf61fa46156458275eda,0x1609d7b6fd230ab22c1a,0xc3ac8b068ffa761d8559,0xc9a561d64582d7dd834a,0xb5bf66d2b0eb22c16bbe,0xc8b05abfb46958759160,0x565d64582b7dd834acba,0xf68d2b2eb22c15bbec9a],#[0x7cb976611905d160ad7,0x174582b7ddcacac82e8b,0xb2b08ba2c1d3e5d99564,0xbd76615845d160f17b0e,0x583c5ec3b2cc22e8b078,0xcaba2c1e2fed18759574,0x7ea5655d160adf361cc2,0x67cbb740caae8b04cfdb,0xa2c19be65ba065574583,0x1955d160d3f30fd032ab,0xd834abb2e8b063fa98e8,0x173bec9a55d974582e7d,0x5d160b97f68d2aecba2c,0x4ac3ae8b05cbfb466176,0xbec9a561d74582cfdd83,0x60b3bf66d2b0eba2c167,0xc2e8b059bfb4695875d1,0x9a85d58458335fd3748c,0x7bf66d42eac22c12fbec,0x8b068ffa75d985611609,0x65f84582d77d934abb70,0x66d2b2fc22c14fbec9a5,0x56fbb0655945d960a7bf,0x87582b77d932aca2ecb0,0xab28c3ac1aafe9b94651,0xfb36559461d60a7df64c,0x829f7d932bca30eb053d,0x8c3ac14f7ecd95e51875,0x6979461d60a77b69caf2,0xefd9b4bca30eb053efb2,0x2e1e2f619855d1645c29,0x7459170bb7760d2ae8b2],#[0xa34dc2ac8b85cbfb6695,0x8efed1a9e15645c355fd,0xd1709bf361d4acaba2e1,0xcca70ab849fdb8ea5655,0xec9a5641765c69dfda34,0x4bbaf66d2b20bb2e3779,0xf02b26cbfa65d9905d15,0xa065f815931fad2b40cb,0xef60d2b2fc0ac94fded5,0xb273e7b269597e0564a7,0x4174593a5ebb32ac82e8,0xdd032aba2c9b2f5dba56,0xebdb0e99955d164d97ae,0x459365ed2b40bb2e8b24,0xaecba2c972fed5a05d97,0xb2695765d164b97f60d2,0x2b77d932ac82ecb27caf,0xc3ac95afed1956417659,0x559061d64d57f4dd2320,0x7d3744cab0eb253efb26,0xc9aafe9ba46558759357,0x56017495fb61d332ac3a,0x340bb2caba47bfb469b9,0x7fec1a7e61655d2e5fda,0x974a9fb61cb2ecc2ae91,0xc82ecba55efb2655905d,0xc3a4655765d2adfda32a,0xa6ff6ad0329c32eb36f6,0x8bb53efb26179460176,0x5643845da9f7d934ac87,0x66812002980014f7ecda,0x883e60db02f209e02140],#[0x71a19d05fa165851c12,0x9f625f090222207f81e5,0x4e30b0b9c2d90ad42968,0x234e8d023380cbe3218c,0x3a80e523810db63650d7,0x1d105240c0fa03da0ed8,0x510f243410c442e10ac4,0x11be461914e450913644,0x2b649f925c48911ec478,0x1c4ee133e4c712fa4b61,0x6579159654c94b852014,0x5d296d05a0964a58a160,0x4d191263c18ce60497ae,0x11a786959a3468499986,0x9b2e6c31b006b79aa66a,0xc527069be26ea9b886ce,0xe474a1cf07391cac71d1,0x7a39e6c7981e3e78c9d,0x7d11f227c01ef47b49eb,0x9a0047f31f947dc9f66,0x220d082ba08c81aa0488,0xa1de86f2184853214084,0x2c08a7a27c891220c87a,0x4a8ca231c8c423048b8a,0x2902a3a68e6a3788db23,0x967254e945a4b291ea44,0xa52688999a62e97da5be,0x427969d7a7109b626cc9,0xa8d0a2ba8a2a202848a0,0x9b2a5ea96ea53292aa3c,0xaaaa22a66a912a22a7aa,0x6ad52b32ac42aeeab32a],#[0xb0dabfeaf72bbaae62b7,0x5c2d0cb352cb2b242c6e,0x52e72b8eae02b6d2d92b,0x3030bfe2fd6bdcaee2ba,0x13ec473110c30b08ac1a,0xbac903208c743198c583,0xacd3b32ccc2b2fecbcb2,0xcf633b6ceab388cdf335,0x29346cd12b428d01b3e4,0x23590d50b520d3fb4c6d,0x3672d943644d88b5ead7,0x728dc1b6fadb0b6b6da5,0xadffb7c6de93782dd2b,0x6e32b8bee27387ae10b8,0xe6b3974e4f3930e3e38d,0x8db9fee7cb9e6e7139b8,0xb3acaeaa3a86e9eba58e,0xbb96edd3b52ecc3b0eeb,0xc8ef103c1eef9bbaeee8,0x20f7fbd9af58bd2af31b,0x2fb83ebefa73e64f90be,0xfeb3f8afda3f5cfcebf0,0x23c0150023ffcffc3fce,0x140d814d09f02e2829f8,0x8ff822819031f00c7fc1,0x8f917f045032063e01,0x822982b8bf070b08063e,0xf917f045f05f0362819f,0x202f81f04478b0600ca8,0x63385d89f03817c12362,0x1be0018517f045990c1f,0xc110097c0033b13e08b7],#[0x8fb8df04578d04447f,0x80d28bf8171be08e063e,0xe17c1028f83958503004,0x5c5f823782f800ab2b09,0xe0097f82288ff0df000c,0x50888cff81f045031713,0x3110c17c0b8bf070b0a0,0x1af05f045837f070b0,0x982ec4033f03e08db17e,0x7835f070b0df061105d1,0x867e02080f0306ee2c1,0x8a098282c0914050f6c5,0x140c17020b81b8a02c2b,0x2c342c33e81060d04d1,0xa8a78633c00721029134,0x83284a04101b03205008,0x52083905c0ade0bc050,0x80800008780a0433c1,0x84280408003c203e101,0x840b81484002e048b02e,0xc5050b0140b0b020b814,0xe33c3141703e101f080d,0x2ae35c3028205a19ea29,0x23204101e31e71823892,0xf0c451491de198f04c28,0x2a29e18360c8918f514,0x838160682056082b040d,0xa29e1b0238a283481740,0x82c100d01138b02c419e,0xe2c96d1391c8514f19e1,0x3c081e041782e04c63d,0x8e2826714f0c47880101],#[0x170233c104d65847f894,0x605478c6082d82002e04,0x82651f82c3030b02061,0x50262d02c262d02c2068,0xe82040e5e0040d010342,0xb70948e45c003410091,0x98e4060c01702631ef16,0x800040382061604005e0,0x2000100c08000010000,0xbc485a5bc48400010000,0x20141000080005c483a5,0x8706131660e168404000,0xb020b8e4040b90b04038,0x5bc485c5bc4840001008,0xe241000080005c483c,0x10000a08001810040800,0x42605b182424a3c653c3,0x311e21445894082189e1,0x3d653c30e0d01909642c,0x80908f0a42ac408c7822,0xe05c0040023044788b0,0x6081582620c1a44b0410,0x2e056e05c0204141190,0x404ac08264ac10234081,0x20b8105c9582cac0e560,0x2e939582e939582012b0,0xa5604c40295814acd24,0x8082304158262014ac,0x101046082b07a203d101,0x761e560b61e560800020,0x812c1a040ac105c0a1e0,0xb8105c081228f40b620],#[0x8205c63c223d11c0886,0x8619f409810618c188ec,0x23c40b433e466c4d86c0,0xcfa04102e0746147d86,0x830b3514202408144241,0xc1045042582011ea8a85,0x1616096178205c1182c2,0x5c0ade0bc0c882d82016,0x38103c08100003092c20,0x2002e04005c08031410,0xbc105858105c0f4407a2,0x40cc504a3a86090b0385,0x82e91e149e489e08390,0xb40801141036a782b04,0x400720a42002d02c581,0x3d1010720a420360839,0xc2e19d0c2001c82b0ba2,0x16040030b020b81e19d0,0x6185a3361840616d0416,0x15c9a080000002001a33,0x10460b49040068083404,0xa3c1c300e18040002008,0x34c20a109c008000e102,0x516080d0944161c8f054,0x463c2a08c11e01c21013,0xd417381c104034444238,0x2b6184458162c0e84060,0x2c0142a2c0916058b03a,0x41c83a10105608053c13,0x2b0]]
def g255H8 := limbs80 #[#[0xb0000000183d40007612,0x95e42762e9a362c0014e,0x5f0c82c2c3000b400000,0x4b5ff3748018200007,0x22200700026a000]]
set_option maxRecDepth 16000 in
def g255D9 := limbs80 #[#[0x7458140f8e5955458140,0xd6e65d7458140f2e5d9,0xd545c140f4e5d5545c14,0x40e6e615745c140b6e69,0x95745c140e6ee15745c1,0x140e6e619745c140b6ee,0xe59745c140e6ee19745c,0xc540e5e615755c140d6e,0xde15745c540e6d615745,0x5c150e2f619765d140e6,0x5e69d545c150f4e5d154,0x55c150e5e5d7845c150b,0xe5e619755c150b5ee917,0x545c550e5ee19755c150,0xe3d619765c550f4d5d1,0xd985d9508fbe89985d95,0x60f2e5d1645c1608f7e8,0xdb855c560f1e5d5655c1,0x571e2f61d7459160e3d5,0xe89955d971d3d5db9059,0xd154f0f5d9655d154b79,0xbe89985d954e2f619765,0xe0175b2fe81765d1648f,0xfbe8995e11768fbe8996,0x458140fce5d554581408,0xfae5d95458140fce6555,0x5458140eee61d5458140,0xdee65d5458140eeee1d,0xd5458140deee5d545814,0x40fae5957458140bee69,0x997458140beee9574581,0x140f6e65d7458140fae6],#[0x61d6558140f9e5d56558,0x8140ebee1d6558140ebe,0xee5d6558140dbe65d655,0x58140bbe69d6558140db,0xeee919558140bbee9d65,0x758140bbee957658140b,0xebee998758140bbee998,0x9758140beee919758140,0xf6e595745c140deee91,0x5745c140f6e615745c14,0x40f6e695745c140f6e65,0x59745c140f6e619745c1,0x140f6e699745c140f6e6,0x615755c140f5e5d5655c,0xc140e7e619755c140f5e,0xee99855c140e7ee19755,0x5c140afe69b855c140af,0x6d615745c540beee9196,0x555140f6d695745c540f,0xf2f5d9655d140bcfe997,0x855d140e6f5d9855d140,0xe6f5db855d140aefe99,0x1955d140aef69b855d14,0x40f6e681765d140beee8,0x899759540f2f619765d1,0x5408ffea197595409fbe,0x68398595409efe919859,0xd540adfe99855d5409fe,0xf6a3965d5409ef693965,0x5d5409fee81985d5408f,0xfe683985d5408ffe9998,0x6e15408ff69f96615409],#[0x8ff6a576e1540cbf6597,0x955d9409fe683955d940,0xabfe99985d9408ff6a3,0x1985d9409efe91985d94,0x40cbfe99985d940cefe9,0x9e985d940abf69a985d9,0x9408ff6a6985d940a7f6,0x693985d9409fe683985d,0x1940abfe9987619409ef,0xfe919761940aefe91956,0x61d40afee819561d40ae,0xefe919661d408ff69b95,0x15c150f5e5d5615c150a,0xedee19545c150f5e5d59,0x645c150bfce85645c150,0xf5e5d5645c150f6e5d1,0x9745c150f5e695745c15,0x50e7ee19745c150e7e61,0xd5945c150afe69b845c1,0x150f5e659755c150f5e5,0x693865c150afee91865c,0xc550f5d695745c550afe,0xdaa1745c550e7d6a1745,0x5c550e7d6a1765c550e7,0x4f5d97455150e7daa176,0x655150ecfe197455150f,0xadf69f8655150cdf65f8,0x9159150adfe998755150,0xcfd61f9159150ddd5d7,0xf9159150cfde1f915915,0x50f2f5d974591509fd69,0xa5865d150e3f619765d1],#[0x150aef693865d1508ffe,0x69e985d1508ff6a7865d,0x1150cdf65975e1150a7f,0xf6a576e1150cbf65976e,0x5d5508ffe9d96e11508f,0xdfe91865d550cdf61b94,0x65d950adf693865d550a,0xafbe89985d950abfe918,0x985d950af7e8d985d950,0x8ffe91985d950a7fe9d,0xf9461950a7f69e985d95,0x508ff69b9461d508ff69,0x9196e1d508ff6939661d,0x160f6e5d1545c1608ffe,0x69d545c160f5e5d5545c,0xc160f3e5d5645c160b7e,0xe595745c160f6e611745,0x5c160e7ee15745c160f3,0x3e699745c160b7ee9574,0x45c160e7e5d7845c160f,0xbbee91655c160bbee999,0x755c160b7ee91755c160,0xb7ee9d855c160f5e615,0x9855c560afe693855c16,0x60f3d695765c560f3d5d,0x1d7455160f2f5d974551,0x160bdee817555160e6f6,0xea197551609fee819755,0x9160fae68174591608ff,0xee817559160f2f61d745,0x59160bafe918559160bb,0xafe918759160bafe9187],#[0x5d160f3e5d9905d160e,0xf2f5d9845d160dbe6599,0x655d160e6f61d845d160,0xaef693855d160e3f61d,0xf855d160e3f5db855d16,0x608ff6a7855d160a7f69,0x9b955d1609fe683955d1,0x1608ff6a3955d1609bf6,0xe91985d160e6fe91875d,0xd1609bfe99985d160aef,0xf69e985d160aef692985,0x5d1609fe683985d160a7,0x9f5d794595609bf69b98,0x459560cbf61f9459560d,0x9bf69f9459560cbfe1f9,0x9759560b9fe917559560,0x9fe693905d5609bfe91,0x3945d5609bf69b945d56,0x609fee81985d5608ff6a,0x8d985d5609fbe89985d5,0x5609fe683985d5609f7e,0xe5d8761560d3fe5d7661,0xd960cbf5d994e1560c7f,0xbe89955d960bbee81955,0x61d609bf693955d960bb,0xfee819561d60abfe9994,0x561d60afbe899561d60a,0x8ff6939561d60af7e8d9,0x91591708ffe9195e1d60,0xcfde179159170d7d5d7,0xb8559170f2f619745917,0x708ff6a78559170abf69],#[0x91865d170b7ee81955d1,0x5709fe6839459570b6fe,0x6a39459570d5f5d79459,0x9570b5fe9175595708ff,0xfe9994e1570adf693855,0x551718ffe9196e15708f,0x7d655905d171f6d68174,0x55d171b7de95905d171d,0xf3d6817659571b7de819,0x905d971d7d655905d971,0x1b7de81955d971b7de95,0x1765d154f79e89955d97,0x54f4f695765d154b6fe8,0x89985d9549df683965d5,0xd54abfe99985d954afbe,0xe8175e05648ff6839661,0x564cfd68197e0564afd,0xf5d9905d164cfd69597e,0x5d164bafe99905d164f2,0xafe99955d164f2f5d995,0x65d164f2f681765d164b,0xbafe91905d964f2f6957,0x955d964bbbe89955d964,0x4aefe919061d64bafe91,0x99561d64abfe999061d6,0x64aefe919561d64afbe8,0x597660174abfe999561d,0x5748ffe9995e0174d3fe,0x5d98559574d3f5db9059,0x9574b3fe817659574f1f,0xfe9198595749fbe89985,0x6157497f69f98595749e],#[0x6fe91905d974d3fe5976,0x55d974b7be89955d974b,0xadfe9175e0165b6fe919,0x90e11658ffe9197e0165,0x5cbf5d990e1165cdf5d5,0x176e11658ffe9d90e116,0x658ffe8197e1165abfe8,0x939261d65cfbe539261d,0xd658ff6839461d65cfbe,0xe9994e01758ffe9190e1,0x11758ffe9196e01758ff,0xfe8194e19758ffe8196e,0xe0176afbe8985601768f,0xfbe8985611768ffe9195,0x458140fee61d5458140a,0xfee6157458140fee65d5,0x7458140fee6557458140,0xfee6a57458140fee695,0xd6558140fbe61d655814,0x40fde6157558140fbe65,0xa17558140fde65575581,0x140bfeea17558140bfe6,0xea57558140bfe6a57558,0x8140fbe5d98558140bfe,0xe65d8558140efe61d855,0x58140fbe5d99558140df,0xfe65d9558140efe61d95,0x658140bfee9d9558140d,0xfbe6a17658140fbe6957,0x8758140bfee958758140,0xefee958758140efe695,0x59758140feee91975814],#[0x40dfe6959758140bfee9,0x19545c140dfee9597581,0x140bfeea1655c140fee6,0x659755c140f7e619755c,0xc140efe619855c140f7e,0xee19955c140efe619955,0x5c140dfe659955c140ef,0xeee91965c140efe69586,0x655140fcf6197555140f,0xfaf6197655140fee6817,0x7655140bef6a17655140,0xeef61d8655140befea1,0x98755140def65d865514,0x40eef6998755140befe9,0xa1655d140eefe9987551,0x140befea5655d140befe,0x619855d140f6f5d9855d,0xd140eef659855d140eef,0xf5d9955d140eef65b855,0x5d140eef619955d140f6,0xef659955d140eefe1995,0x55d140befe99955d140d,0xf6f695765d140def61b9,0x865d140f6f6a1765d140,0xddfe617559540eef695,0x17659540fbe681765954,0x40ebf6a17659540dbfe6,0x618759540ebfaa176595,0x540cffaa58759540cffe,0x69f98595409ffea19759,0xd540edf619855d5409ff,0xfe61865d540cff661865],#[0x5d540edf695865d540cf,0xffaa5865d540cff6a586,0x85d5409ff6a3965d540c,0x9ff69b985d5409ffe999,0x7661540ebf6197661540,0xaffea17661540aff6a1,0x57661540affe99876154,0x40cff6a576e1540cffaa,0x55905d940feee91905d9,0x940fbe619905d940dfe6,0x619955d940bfbe89955d,0xd940cff661955d940ebf,0xf6a3955d940cffa61955,0x5d940ebf695865d9409f,0xefe91985d940befe9198,0x85d940ebfe99985d940e,0xcff695985d940defe919,0x8761940cffe95985d940,0xeefe919561940affe95,0xd9561940cff65d956194,0x40eefe919761940affe9,0x999761940affe9597619,0xd40cff69597e1940ebfe,0x69b9561d40bfee819561,0x1d40befe919661d409ff,0xfe599561d40cff659956,0x61d40affe999561d40cf,0xff69b9561d40cff65b95,0x661d40eefe919661d40a,0xfbe659645c150cff6979,0x745c150bfe6a5645c150,0xf7e699745c150f7e659],#[0x9945c150dfe659945c15,0x50bfee91965c150bfee9,0xa17655150fcf69974551,0x150dfd61f9159150edfa,0x6a17459150fcf6957459,0x9150eefaa17459150eef,0xfaa17659150ebf6a1765,0x59150cff6a19759150eb,0x5f5d9955d150cffaa197,0x55d150edfe19955d150f,0xe7f661765d150ddf6599,0x765d150e7fa61765d150,0xe7faa1765d150e7f6a1,0x7865d150affea5865d15,0x50cff661965d150aff6a,0x99985d150cffa61965d1,0x150aff69a985d150affe,0x69d96e1150cff6a576e1,0xd950ebf619945d950cff,0xfa61945d950cff661945,0x5d950affe91985d950cf,0xff69f9461950aff69298,0x45c160fbe615645c160c,0xf7e615745c160fbe6556,0x745c160f7e655745c160,0xfbe595845c160f7e695,0x5845c160f7e5d5845c16,0x60efe657845c160efe61,0x55945c160f7e5d5945c1,0x160bfee91855c160dfe6,0x6997455160fee6817455,0x5160f6f61d7455160faf],#[0xfaa17455160eef6a1745,0x55160bdfea17555160ee,0xaf61574591609ffea197,0x459160faf6957459160f,0xf9f6157559160faf6a17,0x7559160bbf6a17559160,0xebf61d8559160bbfea1,0xd8559160dbf65d855916,0x60fafe918759160bbfe9,0x958759160bbfe9587591,0x160ebfe958759160ebf6,0x611905d160dbf6959759,0xd160fbe595905d160fee,0xf595845d160dfe655905,0x5d160eef615845d160fa,0x3f61d655d160faf65984,0x55d160dbf661655d160f,0xbbfea5655d160dbfe616,0x855d160f3f5d9855d160,0xcff661855d160e7f61d,0x7855d160cffe61855d16,0x60bfee81955d160aff6a,0x59955d160f3f5d9955d1,0x160e7f61d955d160dbf6,0xa61955d160cff661955d,0xd1609ff6a3955d160cff,0xf661765d160f3f695765,0x5d160f3f61d965d160f3,0x7f695875d160f6fe9187,0x85d160e7fe95875d160e,0xeefe91985d160befe919,0x985d160defe91985d160],#[0xf9f5d56561160dbfe99,0xd6561160ebf61d656116,0x60bbfe9d6561160bbf69,0x157561160bfee8175611,0x160aff6a17561160edf6,0x5d98561160affea17561,0x1160affe9d8561160ebf,0xfe918761160bbfe95766,0xe1160affe958761160ee,0xff69597e1160ebf69576,0x459560cffe9597e1160c,0xbbfe918759560dbf61f9,0x8759560ebf6918759560,0xddf617945d560ebfe91,0x1855d5609ff6a3945d56,0x609ffe91985d560bdfe9,0xdb94615609ff693985d5,0x560cff61f9461560dbf5,0xe9176615609ff69f9461,0x1560affe918761560bbf,0xf655945d960ebf69176e,0x61d60bbfe91955d960db,0xfee819561d60bbfe9994,0x561d60bfbe899561d60b,0x9ff6939561d60bf7e8d9,0x9461d60eefe519461d60,0xcffe559461d60cff655,0x79461d60ebfe999461d6,0x60cffe579461d60cff65,0x979461d60cff6979461d,0xd60affe919561d60cffe,0x6997455170aff6939561],#[0x9170dfd6179159170f6f,0xf6957459170f6f615745,0x59170f3f6197559170f6,0xbf6198559170d7f66175,0x659170cff6618559170e,0xdefe919859170fafe918,0x855d170b7fea5655d170,0xd7f659955d170e7f619,0x1865d170b7fe99955d17,0x70e7f6197561170f6fe9,0x598561170d7fe5975611,0x170eefe918661170cffe,0xe91865d570befe919661,0x1570affe918661570b7f,0xf69196e1570cff69994e,0x5d171cffe9196e1570cf,0x7d695905d971f7d69590,0x5d154f7de95905d971f,0xdef659905d154f6f5d99,0x765d154befe99905d154,0x4cff6839661d54f6f681,0x5905d164efd68175e056,0x64befe95905d164def65,0x91905d964befe81955d1,0x964dbf655905d964fafe,0xe81955d964bbfe95905d,0x1d64fbbe89955d964bbf,0xf6559061d64eefe91906,0x61d64affe959061d64cf,0xffe819561d64ebfe9990,0x561d64efbe899561d64a,0xebfe999561d64eefe919],#[0x6560174f3f5d96560174,0x4e7f5d98560174affea1,0x98560174cffe59856017,0x74d7f5db9560174affe9,0x9b9560174cff61b95601,0x574befe9196601749ff6,0x6839859574f3f6817659,0x1574d7f5db90615749ff,0xf6839661574cff61b906,0x5d974f6fe91905d9749f,0x7fe95905d974d7f65590,0x55d974b7fe81955d974b,0xcff69590e1974f7be899,0x90e1165ebf69176e0165,0x5ebf68176e1165cff69d,0x1905d965cff68197e116,0x65bbfe91905d965dbf65,0x8196e1175cff6839461d,0x176cff68194e1975cff6,0xe558460176eefe518460,0x176bbfe999460176cff,0xfe918560176cff617946,0x60176bfbe899560176af,0x7fe9d9560176bf7e8d95,0x5611769ff6939560176b,0xefbe898561176affe818,0x90e1176cff69590e1176,0x9ff6839461576cffe95,0x40158011600a20042000,0xe02de0274023201e601a,0xa0446040403ae0380033,0xe05860558052a04fc04b],#[0x6ee06ac064c05f605b,0x60874081407d20786073,0x809a00968093008ee08b,0x60aea0a9e0a480a1009d,0xe0c480bfc0bba0b820b3,0xe000da00d360cea0c9,0x60f900f4e0f020eb60e6,0x2110210b6106010280fe,0x4129c125011fa11ae116,0x6145413f41394133412d,0xe160215b6156014ec149,0x8179c173c16f0169a164,0x4192218d61880183e17e,0x41ac61a8e1a3819c4196,0x21c241bd81b821b401af,0x81d781d361cea1cb21c5,0x61efe1ec61e841e241dd,0xe20521ffc1fb01f781f3,0xa219c215a211820e0209,0xa232c22d62280222a21c,0xa24e42484241023c4235,0xa2674261425d22586253,0xe27dc27a42762271626c,0x6293a28f828ac2856281,0x82ae82a9c2a3c29d2298,0x42c782c402bfe2b9e2b4,0x22dd62d8a2d3e2cfc2cc,0x82f3e2ee82ea62e642e2,0x430ba308230222ff42fa,0xe324031f431a83166312,0xe33b23370330632ba326,0x4353834ec34a0344033f],#[0xa36b43668363a35d0358,0x2382637e437a23756370,0x39983960390a38b4387,0x43b503ad23a683a1c39d,0xc3d303cda3c8e3c423bc,0x3ed43e743e283ddc3d7,0xc40463ffa3fb83f623f2,0xc41d64194413e40f2409,0xe4352431042c44278422,0x44492445a440e43c2439,0x445d2459a4562450c44d,0xa473a46e4468e4660461,0x491048b0486447fa479,0x84aa04a5449fe49c6497,0xc4c1c4bd04b844b424ad,0x4d8e4d424d004cbe4c7,0x44ee24ea04e544e124dd,0x504050124fc64f704f2,0x651e4518e513850ec50a,0xe534c52f652a05268522,0x654aa545e541253d0538,0xc563055d05584554254f,0x6577a574c570a56c8567,0x458e258aa585e580857c,0xc5a545a0859bc5970592,0x25bc65b665b245ace5a8,0x45d385cec5caa5c5e5c1,0x5e8c5e685e305de45d8,0xa5f725f4e5f165ede5eb,0x604e602a5ffc5fc45fa,0x8611660f260d860aa609,0xc622461ec61b4617c615],#[0xa630062dc62b86280625,0xe63d263a46376635c631,0x664c264a8648e6456641,0xa65bc658e654c652864e,0xe66b6667e6650662c65e,0x867b0678c675e673a66e,0xc68be687c6858682067e,0x869a4696c6948691a68e,0xc6aa86a7a6a606a1469c,0xa6b7a6b606b286b046ac,0x46c426c146be66ba46b8,0xe6d146cfa6ce06cbc6c8,0x26dc86da46d8a6d5c6d2,0x6e7c6e586e2a6e066de,0x66f446f2a6f066ece6ea,0x703e70066fd86fb46f8,0xa7188713c70f070ae708,0xc726e7254722671f871c,0xa732c731c72e472c0729,0x6741273ee73b67392735,0x6750274d4749c746e743,0xe75ca759c75827554752,0xc7674765a762c761275e,0x87764772c76fe76d076a,0x67822780877ee77ac778,0x78cc78b2788e786a784,0x2799e797a7942790a78f,0x47a5c7a387a0079dc79c,0xc7b747b287af07aae7a9,0xe7c467c227bfe7bc67ba,0xc7d2c7d087cd07cac7c7,0x87de07da87d7a7d4c7d3],#[0xa7ebc7e8e7e607e467e1,0x67f7a7f607f327f0e7ee,0x88074804680187fea7fc,0x48150812c80ea80bc809,0xc821881fe81d081ac817,0x682fe82d082988260823,0x6840283c08374835a833,0x684de84a6848c844a842,0x85d885aa855e8530851,0x886fa86b886808652861,0x687f487da87a28756872,0xc88ee88c088a6886e883,0x889d489ba89968968891,0xc8a888a5a8a368a1c89f,0x28b6e8b368b088ada8aa,0x48c408c128be48bb68b9,0xe8d268cf88cd48c888c6,0x68df88dca8db08d828d5,0x88eca8e928e788e4a8e2,0x8f9c8f828f548f3a8ef,0xe905a903690088fda8fc,0xc9118910890e490ac907,0xe91f491c69198916a913,0x492c69298927e923c920,0x693ac937e9350932c92f,0xa94569432940e93e093c,0x4954694fa94cc949e947,0x49668961c95d095a2957,0x9758972096f296ce96b,0x9848981a97ec97aa979,0x2992e990a98c898a4988,0xe9a0a99dc99ae998a995],#[0xa9adc9ab89a809a5c9a2,0x49b909b769b5c9b429b0,0xe9c809c529c109bec9bb,0x89d709d389d0a9cdc9ca,0x5bc10a469dfa9de09da,0x9453c0a27c1241122fc0,0xc0f06892f0216e11f149,0x99062114505bc0bc5d1b,0xa47f1a11a27c0f042918,0xa46f1ac584689f03c10,0xf04291fc686689f03c1,0xc0f04291bc671619a27c,0x619f03c1258af1a11a27,0x68926180468908fc50b,0x182386618f141171bc0f,0x90a44063c50a7c0f0496,0x4722fc0f061623c0f078,0x7c0f0491858664891e0a,0x164705bc0f042d2c1971,0xf0429185b8670908f82f,0xf06c90a44f1859327c0,0x5c90ac4f03c1b242b13c,0x17c971bc0f042917c0f0,0xf045623c971bc0f042b,0xc1158906692a3f8222fc,0xc625c9464a47e1782f03,0x1c201bc9d1b82d1fc107,0xf03c12588f2746e0bc0d,0xf04291c29463c516614,0xc1458941a8c40a14f27c,0x782f03c1858906ac5f03,0x51615c606c590a514f1],#[0x86fc10c7161418f02c2f,0x50645bc27c0f04291a1a,0x41ee24501fc005bc10a4,0xa7c070bc10dc5d1b47f0,0xed245f26c6f078709050,0x11f05c70788e1b87f041,0x7c1450291dc8d1b48f02,0x28bf04291c12847c0a2,0xf02c5f04291d1404416f,0xb1411f0429141904746,0x4745148f03c1a2c291bc,0x78804548b17c0f05140a,0x1c14d22c5f021171fc10,0x91c16053c0845c5f0429,0x992814d23c071611f049,0x14846890a7c0c0816f04,0x7c5063c0f0689450906d,0x214f05c7078906c9984,0xb17c10a4872111e2384f,0x1444291c3344406f0389,0xc5f04291c14623c0b17c,0x2c5f0429181b053c0e12,0x21471fc10788e13c005,0xf03c115c291811e2384f,0x845911627c10b8585388,0x8404788f0214717c116c,0x41ef17c0453c1e26c71f,0x4429f17c0b1f8951bc12,0xd181e446c7f05891e188,0x7d182986214f05891e18,0x11715c6a27c0f042922c,0x9c5f0289f04290987064],#[0xa49a27c0f04290ac5f1,0x1688bf1902a27c0f0419,0x9453c5f0247f04112589,0x140a7c0f068906090a68,0x7c0c0bc125897185bf15,0x3c10a460a6897145b06,0xe27c1078262111e12c6f,0x8b17c1658b04bc6863c0,0x84511123f890b01af021,0x1a23dc6f0218b17c1444,0xc18c088ff03c1d1e8b1c,0x1c180b3c023fc1d1d961,0x1211107a14b1b47f0589,0x78659222e47f03c18589,0xc916982067c0f06160a4,0xc1171b09f0382f060bb1,0x241b467c0b17c10a4713,0x719c8f0119e0bc108c8c,0x8067c045bc1d1c26181b,0x1b465c8f0023f05c6844,0xb82067c023fc1d1d161c,0x16c94440bc2429f04341,0x86414447c5063c0f0709,0x9f1429f001691fc1444b,0x46f06c7e24816e190530,0xc1ef0439141f07382d17,0x2447d17c145829100800,0x1d1c6e2582f0345f0716,0xc1d1f8223c0e100fe0bc,0x3c10ac762745f0034b1b,0x7bc10d040d00800ec6f0,0xe080fd1fc0f05c624910],#[0x800bc0f042b1408e1003,0xc602003f01c7f04261c4,0x1490b345f03c125ac71a,0xb384e080800fc008fc1d,0x12004f0346d1fc107870,0x8d1803d1fc007bc1b149,0x4723f82f03c145860d80,0x589144fd1bc1d1d8917,0xdf89d1fc118370b516f,0x723f89f03c145850b516,0x88e088851f84f03c1d18,0xf470d80f01789f03c1c5,0x1b4612182f0347f07841,0x7458513f46f0347f0589,0x89f042e45864502cf06c,0x111627c1b1d16182c445,0xf06c525110d3c10a440b,0x62384e080800c0fd1fc0,0x80cd1127919f0f47f06c,0x7617c0b2702f06c8b34,0xd02f0185b27c113acc21,0xf07472ac4f03c10a4423,0xc6312322c6c0ac4f0385,0xbe1423167c0463c13587,0x1241c8f61702f03c1b58,0xbc0f0423164906818b0c,0x13c108c806a18f1ac9c0,0xf05121c19e15c6f0218b,0x4f07471c1971bc0862c4,0xc9f0429182e063c004ac,0x3c00afc10a49b182bf02,0x48fd1c871a02711c373],#[0xd1d8b1dc40b818f02c6f,0x1958231c1804ac6f03c1,0xc108e56181a067c0e0bc,0xfc0f065664850af82f03,0x142be0bc0f0423958608,0xf04232023f03c195992,0x564487e21c672059e0bc,0xfc1e0860660bf02c7f04,0x2dc7f04121f44f01c703,0x3f82b1fc11ec6223c00,0x4f0382f05c72888f0344,0xc0f04966992923466174,0x876499a661c7d1a48d13,0x499234671f44f03c164,0x2022e1746f0344e09c7f,0x678508fc0e0bc115881,0x816f82d13c0f0423241b,0x3f0023f042e1819e174,0xac7f0347f04560985020,0xac50980800fc0b1bc10,0x404bc1b1c6223c0d13c1,0x2ef03c115ac71c19f034,0x3f0344f042b1f85e08,0xfc071f44f042e1c2e02,0x71bc003f82f074718080,0x471bc0b180fe0bc1d1c6,0x456d1c806bc0b1bc104b,0x65b282e0678223fc0f0,0xa3c4f0dc009f4ce1782f,0xf13c3d3382f002a96c70,0xc0f05c427c0f04230b84,0x42b1408d1b8203fc3d1f],#[0x1fc0f06c42888d1bc0f0,0xac60b808d1b8500f827,0x6f042b180800fc0b13c1,0xc6e0bc108c702003f02c,0x7c032fc10a4702003f02,0x1fc0f04cb0a44d238606,0x61c14b17c0462c4f041e,0x14281e463c0853c17169,0xc9f142904618f03c1259,0xc14b27c0717c10a46164,0x1819f0218716c4f05141,0x61649053c0861c5f0459,0x7862c90a41bf0114f049,0x470688ff0118b13c1850,0x5c707bc5f0347453c1b2,0x1687063c085347f05c92,0xe450a05386f0218713c1,0x804b8cf13c391fc0f041,0x7476587f03c10a42e121,0x51625080602cf008ff0,0x858291d1ba489751fc0f,0x192c291c5a6081bf07c0,0xc192c291a4926c19f03c,0x18292fc1168626fc0623,0x6d12c7f041e1cc8f0,0x200307bc0f04341848f,0x40a5c5047c0f04598588,0x29f141bf03c185914211,0xb85453c0f04dac585164,0xf06c75247527c0f05160,0x853c1524786fc5f0115,0xc061bc1164a456c786fc],#[0x516311b25011b1418d27,0x7490a419d1ec5f0282f0,0x1651fc1250b46e1884,0x858c46c59046490a7c5f,0x927c50a414f0147e0bc1,0xb1749f04291d1b46211,0xc0b17c145b471c1b053c,0x11bb17c0f0494202ce0b,0x1b44e0bc108c706744d2,0xfc008fc1b149223c0e,0x4d1fc107870b386e0808,0x49f06c5e087123c001b4,0xfc007bc1b149f0036d1f,0x63c152470db4402003d1,0xe0bc14586e1829f021b8,0x6d1fc1d2782234723fc0,0x82f03c14586f17c013d8,0x147e1b82f07441c8f527,0x1182f0347f078623c022,0x13f47e0bc1458812045d,0x7b27c171f821f49f17c0,0xc071e17f06c9215af001,0xdc7f06c945060cd1446f,0x2c9f041771f8223c085,0x727c0f078216870e411f,0xf0e6c7f05c9e08705217,0x14713c0f045a07870444,0xf45d1c39f06c9e086120,0xc3902003f02c4f042b1,0xcf0747092941fc107839,0x8cf0347096941fc4f0f8,0x848f0386f042b17c4f0f],#[0xa4526e8cf03c10a42e1,0xf05c7258826fc0f042e,0xc10a439160fe081ad17c,0xb1486f0cf04311514c33,0xf04704bc0b1782f04371,0x90e444509e46fc0d1ec4,0x8cf13c3f04312114f042,0x3c4f0fc00c88c6f14e1b,0xff06c5271bc5386e3,0xe0ac52786e080800f47f,0x2280f02003d1fc0e1bc1,0x892187d1b44f03c17178,0x48d13c0d1bc166076699,0x3c506fc0f04981589716,0x17c0e1fc1d2490a61905,0xf06c555885540f51b82b,0x10a4341433e0b49e1fc0,0xc6f03c1e0949201af03c,0x345b13c1e1c74649e86e,0x13c0f04570a45d182ef0,0x234500f87f03c1b10ab,0x4d1bc0f0429182ed1839,0x46f000fe0b87f047069c,0x1c600f45f03c10cc7223,0x23c3f0382f0787b18902,0xf024bf06160a46d15c40,0x6067c0717c1c58291819,0x7161ec2f01c5f0423c58,0x58291a1986823f01c2f0,0xf07160a4606f45f03c18,0xb0bc108f16181b717c0,0x1a08fc070bc1c587717c],#[0xa1a702c5f07160a4686e,0xa47044c8c2fc116c291,0xac2c806a19c27c0f045b,0x5b1d18b1848f01c2f041,0x516102809c29c5bc1a2e,0x7b47f03c1b189f0029f0,0xe1bc136870d008e10030,0x4f03c1088770b08f0384,0x43f07c008887141de1b8,0x3c1065162386e11c2085,0xbc14586b16c20a611f0,0xf020bf04371b47f0211b,0x802fc0f0434458506ac2,0xc20a7c5253c0f041b858,0x41a7089706fc1f021621,0x1b47b0a14f03c1458671,0x1458685ec50d7c186f16,0xc2f05161ec586e17f03c,0x3c10d9161c36467c0626,0x5ac5f06371d1bd1ec2f0,0xf0036f05161c35e27c2c,0xdbc10d1161919d1ec5,0x18f009bd0bc1e24746fc,0x3f0384f06c5e1c908e,0x23c0f04570a47d080f02,0x46fc0f04990a47b091be,0x6f84d17c10a4606b89,0x8470028f0429c5a991bc,0x1bc0f07841fc0f042945,0x26fc0f04341b4512187d,0x2863c0f0746624806b89,0xc50d7c1e261b1d1908ec],#[0x81a46589f0439161ac66,0x78785c0fb1f42f05961,0x171c702003f0386f06c7,0x1671c7d119a05fc0b0bc,0x3c10b870b819f0017f05,0x27c126c502003d11c7f0,0xdc2d13c10e4670a17d,0x8e19c3d1fc1079c42008,0xc9f0786d1c24070607dc,0x408e1403d1fc0f06c425,0xfc0e1ac2f04231f860e,0xfc0b13c1e1c1e1c080,0x800fc0b1bc1e1c1e1c08,0x70200370b44f0439180,0xc470200370b46f03c10d,0xb149c521bd2344d0fc10,0xd080800c0ff0386f0787,0x50d743d0b16b17c18dc7,0x28b0a430654631429044,0x859120b84859c5098345,0x16149a8588b0d029141e,0x457444290c1b70c330b2,0x4826081b61029b14141,0x2b118407812844c705c5,0x384181e444460c34c10,0x5101ee1020e42b078c13,0x40b0d46098245a1209ac,0xa4140481731d161a12b1,0x5610c7a1050a61205c30,0x450a41211ac50b850a68,0xc2c858515e16700290e,0x5d185c11c5078306c197],#[0x3d18850a430d02b099c,0x70384181e62c28608485,0x2d13840a420e42b0a5c1,0xcc6c101e11c4229c670c,0x145a4518a70c1eb15111,0x30b426141b808c561029,0xe120ac28481a098ab15c,0xa5b8951c2d18296102b0,0xc670c62121486030bc26,0x894d1429105a4544f429,0x13c45191e05814044485,0x4c084f11430dcc830f02,0xac6b0c14160a516c30b4,0x1c1913c45c09c6161582,0x50c370b50a719c347b45,0x8323c478581e101947b4,0xa60b099c6844508e16e0,0x34585429c382c2d09850,0xc670c3645832488f81dc,0x81a10290681931a8202,0x7103445a0ba08445a0ba,0x502d160d0370e824583,0x69c00e434550a719c30b,0x510a91f0470c360cc71,0x20c02e09a16c25470b47,0x4430a6160505b1091078,0xb5838590fd1458591e6,0x469141eb1c58590fd143,0x79c7081e07450a42479,0xc6105a03d8a70c2682c6,0x80fa2ac3b18406a8ab0e,0xe2450c296e25470982c1],#[0x203e96e2430694150296,0x100f71820d1c608340ac,0x830c0fd14425b0b0990f,0x8c205e4731c303f4508c,0x845a140c2ca58230e960,0xc1445830a71670039121,0x45ac00684c5b8286c351,0xc50d83b031603ec51457,0x25470b460d81e0ac003e,0x534745891103009a16e,0x360b7894584459890b43,0x25c518370cc2c4598914,0x3f89714403dc170316e,0x705f0a31d45d0c0f1b16,0x470c02c0980fb1516624,0x1c603e8a62ac370cc7b1,0x6242d102f0b826c5b897,0x2d1316e240f71440dd16,0x1511100f09820dd16e24,0x344430781bb14307918b,0xc103d8a70cc6b1454643,0x315c3143403ec5718405,0x961429718330c1703d8a,0xc0f609c50c370cc2d624,0x320c323f851414313850,0xca70c5050c4e1429102d,0xc29614c4a14408c5b448,0x538523c8b101223f850,0xc495823091243dc31584,0xc0b60a560d9a6619271,0x80958408e56082b09a56,0x349958508e56082b605],#[0x4a08403f499583049816,0x85869560660b10230694,0xac8609832480f70e8255,0x360580d10608e4421830,0xe5608c208f44082e0ac2,0x60c12b0e560c2b958260,0xd56082b099560c0fb0e5,0x6142e0ac20ba560ac308,0x8160256149223d07b0c5,0xad560c0fb0e560c12b0d,0x50ba0f71c308d56082e0,0x82b71430501251c17b10,0xac2449c5b102e0a4544,0x516b867144b0d0291829,0x9c5850723145b12c30b4,0xd470b4516a11a32c307,0x63142915120ac2a32c4b,0x2e0c29a182b0c1940a8,0x10110a61651459141271,0x526e4b0a430641647a4b,0x90fd1430b5838590fd14,0x785b820b840781078185,0x82c85858598212c34111,0x5c1231e82d105061c30d,0x41101e082b304c0d1040,0xd16e0812138231e44510,0x112140c17b14820b8485,0xc170344104fd11c50e1b,0x5b49608371c1852c20ad,0x91147045160c340c1c08,0x340a716314445a117142,0x582e23c3278160538210],#[0xbd1029250491d8205838,0x830dd4850c4f11782181,0x250585b8218c313c45e0,0x4e082e0a4325f440b829,0x8c303ec5094850c0fb14,0x5250516b1612c30b3160,0xc5a083413c50d02316ac,0x3ec5142916a8202c445a,0xe0a8203ec50d83a0b160,0x1b0681770182d1070d81,0xc140454a91dc30d860a4,0x41a1b06e180d4406e820,0x440a420b82b0a5c17034,0x2516141b063821651617,0x6d2445243708360cc2d5,0x4f83344d0d821c370b11,0x445830c5d0c2d105a854,0xd1343b1468560cd13430,0x54470cd0c1510638560c,0x4c0d106c30c7d0c5a03c,0x3f0cd0f44101ac334330,0x32082e1f43458c70b440,0x44d0c261419c30863174,0x174331c6d0c2d0a15833,0x25e16609c0170c02e477,0xc5082e03dc1701c51434,0x2f82103346d14d14403d,0x431c470d1ed14706c4f1,0x140c1b0511e52c40dc2d,0x5dc404830e42b0917448,0x2e0c1e71020e42b71030,0x103066459102e1017258],#[0xf121725b8209840e42bb,0x3470d82258402e471140,0x58390ec3701820de1614,0x8b1514111bb11140c174,0x347131bc6314d1c40791,0xb430cc1eb143c6f18c5,0xcb0dc1700c5b1070dec3,0x496b244a300bb0c303e8,0xc0f02cc5705c014370b,0x203dc1701c5100f316c4,0x1440e42e0adc4100f714,0x5104a70c370c330a5c4b,0xb46149a0ac266998649c,0x781b51282101a0640b60,0xb083752143a084f11468,0xe14094850c0fb144a682,0xb1023e0820dd490b4386,0x4a70e820dc40a61a5102,0x104486e180c44068340d,0xf116824085914c551029,0x103510105e4451030644,0xf101bc084f12c4465115,0x33329c3718402e461140,0x100f71020cccc70dc410,0x5705c00ac60d0237142b,0x4110a4471429083908dc,0x4585a15c34583710c6a1,0x416f0b0a430440b23f85,0x8d8349c2120f03c020d0,0x20d04c588f08c2c58236,0xb160e1b851160f1602cc,0x30b160c8f30b160dc030],#[0x890dc485f1630038101a,0xdc3700c5c5ac21c2d459,0xdc4e271603dc5100fb0,0x7e2434c59c2102d45b89,0x870e63003cc0e26c5c58,0x5870d83003fc00e58945,0xa420d83003ec5f03894,0x4631a42124508f420c57,0xd0505d961140f90850a5,0xf198408c26581403cc50,0x23b14405cc570e426580,0x6c50cd11464961196050,0xc5823708305145610290,0xc3309960d0606a420d03,0x621b0c2b09a960c14915,0x30c29a11c0610c214848,0x40a41a3083913843082,0x103403dc50c23868c00e,0x50e42e71c3479c3e1496,0x42e70830cc9b85894e14,0x23c8b168570d160dc40e,0x390ac20e5c20916e1414,0x50850dec325830d02b08,0x64511b258302ec390a96,0x839129602c45509c003c,0x131bc6314d084044c565,0x3462c546c4c6f18c5342,0xcc5c5856583308ec5102,0x3f4330038c58504645d0,0xf71420e40f705c071450,0x2e0ae960c0]]
def g255H9 := limbs80 #[#[0x61b80002018000a03,0x421e80c0004060e00c,0x4200104004000111004,0x8200100074de35078,0x1000047a120080404030,0x61d0d814040b0602c081,0xc01070685c020e0104c1,0x834000c0181808020387,0x1a2018004c0a806140b,0xb9622e7757c0050ce000,0xb7a49f0cf4000498887,0x34060002220001dd200,0x4550002856000b6980,0x898938c508048001e2e0,0x287397506c26f44d4823,0x217ee0bb2746bb000cae,0x902c00974f6935ade189,0x688a5264000c32388118,0x1818f4a2344000e6217,0x819c1d186ece00011080,0x26a5808a011f469d8,0xa86a16ac7804c835c08c,0x69b6ac7c055b65d7a4fc,0xa668023dc2f476a0eaaa,0x5b46dc5e91f6bdb936c2,0x1c50211e008044366b70,0x8d5463b09d5d616263b5,0x8b5e1d2a135d46740003,0x9c8749c8fb0000000d71,0x4d393141c44dff8b6428,0xeeca1a812efe05b369d6,0x1d28a0004ca55962e2f6],#[0x2b0cbc0010e3d7200010,0x17960c941aafc001c077,0x628c00000022e5865,0x34ca000b575114000313,0x87366bf4cb66e1785800,0x3a3e000000000000064,0x8553cc98347aae664c80,0x2008c53ee1c88d08a46,0xf06945b2ae10392322ee,0x324000062a6034000,0x1309927dbfb2d533,0xec0e3e2102e23f000000,0xe7aee279992de368a7d3,0x9580029672ac97c0001c,0x18dce761853d6f1339,0xe36a240001516346d1d4,0x8e35ae83393c631192f5,0x48cf9c4e1ff366664c9,0x24d0000000000150d23,0x1420000d9800,0x8ff48e29855450eea180,0x70a80000016c80002,0x800152cb3bd693a98000,0x24f0007b1400001ab3b,0xcdc2a5cae88d5a1893e1,0x752be1a0d3cb926000e5,0xe3bf84df91433482c12,0xa4ae257632bc1523eade,0x2370492912802000784c,0xe52e2a10000000000000,0x50916889e58c5334f60b,0x550feea013808b41b0c0],#[0xa51190ca8e3dd0ea6102,0x4f1c3e0f79a11b82d3f6,0xa4ab9c5b2706ee41713f,0x7cd0000ea4b78eb54d45,0x72820004305822f35000,0xcb4fe19a2bb160798d86,0x2be0f52acb2a205b0097,0x2ce2480000000000b3fa,0x1d6e7bc10f23a1a80004,0x2060000003]]
set_option maxRecDepth 16000 in
def g255D10 := limbs80 #[#[0xb6ae8b8a81db9745c140,0x7abb2e2b075e5d570543,0xeaecb2ae3db57455171e,0xebb2e8b24fd65f815939,0xb2fc2a213ef9261d65e5,0xaa2c0a04ff657874427f,0xcab0281fb97458140fdc,0x3ac0a07be5d960503df2,0xeb0281bfb8758140dfcc,0x2e0a05fee5d60502ff32,0xb8281df9755c140fdcaa,0xe0a06fee15705037f30a,0x8281bfb865c140dfcc32,0x2a07ed55171502ff72cb,0x281bf7855c540dfac2ae,0xa07cf5d554503e7acaaa,0x81bbf8755140ddec3aa8,0x6ef61574502f7b2eaa2,0x17bf955d140ddfc2ae8a,0x6ef61974503b7aecba28,0xb7f8559540ddfc32e8a0,0xdf615755027fb30b2a81,0xff96615409fecc2eaa06,0xf65b855027ff2ec2a813,0xd865d9409fecbf0aa04f,0xe55865027fb30bb281af,0x95e19409ffcbb0ca04ff,0x55875027fb2fc32813fd,0x5e1d409ffcb30ea04ffe,0x1705427fb2dc3a813fd9,0x5c150efcba2e0a87de55,0x705437f30cb82a1bfb84],#[0xc550fbaaa2e2a86fee19,0x15437ef08b8aa1df5745,0x550dfac32e2a877d5d97,0x5437eb0d38aa1bf7865c,0x50f9eba2a8a86fde1a71,0x436ff0caa2a1b7d86551,0xdbfc3aa8a86df61d545,0x2fef22b22a177d975515,0x9fecb708a86df5d78454,0xeff28baaa13fd97e1150,0xbfc32eaa86df61975542,0xfb30bb2a1afd865d950d,0xfcbb0ca84ffe51865427,0xb2fc32a13fd94e19509f,0xcb30ea84ffe51875427f,0x2dc3aa13fd94e1d509ff,0xa2e0b07be591705827fb,0x8b82c1bfb845c160efcb,0xae0b07be59570582ff72,0xb8ac1bfb855c160efcba,0xe2b06fde1571583deaca,0xa2c1bf7859c560f7ab2c,0x8b05bf65954583cfacaa,0x2c1afd8759160f5eba2c,0xb05bf65d645835ff0eb2,0xc19fd875d160e7ebb2e8,0x6bf5db845827fb2bc22,0x16ff94595609fecbf08b,0x6bf61d65583cfaeab2ac,0x6fd9759560d7fc3acab0,0xfee4175582dff2eb2ac1,0xfd76e15609feca70ab05],#[0xfe51765827fb2fc2ac1a,0xf9461d60b7fcaaecb05b,0x653875827ff2ac3ac13f,0x74551709fecaf0eb04ff,0x5d545c3afaeaaa2e1dbd,0x459170bfbc8ac8b857f6,0x9745c2bff2aba2e1dbd7,0xe11709fecaf08b867fe1,0x655c3afaeab2ae13fd96,0x1570affca2eab86dfe15,0x65c27fb2dc2ae13fd94e,0x1519fecaf0cb84ff6538,0x5c67fb21c3aa33fd97e0,0x71efacaae8b8f7d64174,0xc7beb20bb2e37f790595,0x4bfbc82cb38f7d655765,0x3e7acaba2a97bf905d15,0xddec32e8aa76f5d97455,0xcfaecb2aa977f9059554,0xbecbacaaa6df61d65553,0xff20baaa977f9759554b,0xfcb2eaaa6df61975552e,0xb30bb2a9afd865d954bb,0xcbb0caa4ffe41865527f,0x2cc3aa93ff9061d549ff,0x82ecb26fd5d7815927ff,0xac3ac93ff9061d64b7fc,0x700ba4ff657805d27ff2,0xc2ae9cfd76595749fecb,0xecba4ff65b855d27fb21,0x32e93fd90e1974affc82,0xb2cff653805967fb2bc],#[0x2cbafd76e0165dbebaf0,0xb2cff643845967fb2fc0,0xcbafd76e1165dbebaf08,0x2ddfe51755967fb2fc22,0xb7ef9261d65b7fc82ecb,0xefbe49875967ff20c3ac,0x3fd90e1d659ffca30eb2,0xff653805d67fb29c3acb,0xfd90e11759fecb700bac,0xbe49865d67fb2dc22eb3,0xd94e19759fec870cbadf,0x657805da7fb29c02ed3f,0x95e11769fec8708bb4ff,0x43855dafdf24c2aed3fd,0x5581409feca70abb4ff6,0x560503ff30ab0281ff97,0x58140ffcc3ac0a07fe65,0x70503ff2cab8281ff997,0xc140ffccaae0a07fe615,0x1503ff32cb8281ff9865,0x140fdebb2a8a07fd6157,0x503f7b0eaa281fbd8655,0x40fdec2ae8a07ef59574,0x3f7b0cba281fbd955d1,0xfbebaacaa07ef659745,0x37fb0eb2a81efd765954,0xbfecbacaa06ffe1d6550,0xffb30b2a817ff9759540,0xbec2aeaa05ffe6165502,0xff0cbaa81bfd865d540f,0xecc2eaa05ffe59755037,0xb0cc2a817ff985d540bf],#[0xbb30aa06ff61d855037f,0x20bb281bfd76e1540dfe,0x32eca05ffe5576503ff3,0xbb281bfd985d940f7ec,0x2eca06ffa6176502ffb3,0xc3281bfd8761940bffcc,0xea06ff65d865037fb2a,0x3a817ff9661d40bffcab,0xea06ffe55875037fb2ac,0x2a1bff9661d40dfecb30,0xa87fe64570543ff2c2b8,0xa1ff9945c150ffcb22e0,0x87df5d561543ff32cb82,0x1bff8758550dfec3ac2a,0x7ef5d164543efaecaa2a,0xefd7659150fbebaac8a8,0xffe1d645437fb0eb22a1,0x7d955d150bfecbac8a86,0xf61974543bfaecba2a1f,0xf965d150dffc32e8a86f,0xa61745437fb30ba2a17f,0x945d950dfebb708a86ff,0x61765437fb30bb2a17ff,0x461950bffca30ca86ffa,0x170583ff2a8b82c1bff9,0x5c160ffcca2e0b07fe61,0x71583ff32ab82c1ff985,0x5160ffac2ce2b07fd615,0x4583efaeaaa2c1fbd745,0x160f7ebb2a8b07df6155,0x5837ff0eaa2c1bfd8755,0x60bfecc2a8b05ff65d54],#[0x83dfb0ab22c1efd75591,0xffcc82e8b07bf61d645,0x3dfacaba2c1fbd845d16,0xbffcaae8b06ffe157458,0xbfb0eba2c1efd965d160,0xfecc2e8b06ff66174583,0xff30ba2c1bfe985d160b,0xec2b08b07bf59584582f,0xb0ec22c1efd7661160df,0xc3acab06ff5d7845837f,0xabaac17ff945d560f7e,0xc2eab05ff66175583efb,0xcc2ac17ff9461560bffc,0xb0ab06ff61d85583dfae,0xbb2c1efd945d960bffcb,0xeb05ffe5187583dfb2a,0x3ac1bfd9461d60bffcab,0xeb06ff655875837ff28c,0xae1dfd7558570dffcab0,0xb877f5d5815c37ff0ab0,0xe1dfd7559170dfec2b02,0x87bf619645c37ff0ab22,0x1dfd655d170bfecc2c8b,0x77f655745c3bfb0aba2e,0xdfd965d170efec32e8b8,0xff615845c3bfaeac22e1,0xff9661170dfec3308b86,0xf619755c2fff28b2ae17,0xf9461970dfec330ab877,0x64174552fff20baac37f,0x905d954fdecb2e8aa7ef,0x6176553efb2abb2a97ff],#[0x5d164dffcb30eaa6ff6,0x175593f7b2aba2c9fbd9,0x5d964f7ec82ecb25ffe4,0x875937fb20c3ac9efd95,0x174dfec2b00ba6ff655,0x5d3bfaecc02e97ff956,0x174bffcb300ba6ff6198,0x5d2fff20b2ae9bfd65e0,0x74bfecc2caba7df61565,0xd2fff20c2ae97ff98595,0x4dfec330aba77f5d9855,0x3bfb20bb2e97ff966157,0xbffca300b2f7f655765d,0xdfb28bb2cbefd905d965,0xffca30eb2dffe5187597,0xff28c32eb7ff9661175d,0xfca300bb6ff611805daf,0xf2ac02edbfd8560176bf,0xc830abb6ff615845daff,0x28c2aedfef9261576bff,0x32eaa07ff61d65502fff,0xabb281ffd7661540ffec,0xb0ea07ff66176503ffb2,0xb0aa1ffd9661d40ffeca,0xe8a87ff61d64543ffb0e,0xa2c1ffd945d950ffecb2,0x8b07ff61574583ffb0ea,0x2c1ffd985d160ffecaae,0xb07ff65187583ffaeac2,0xc1ffd9561d60fffca30e,0x87ff615615c3fff2ac3a,0x1ffd9661170ffec2ac8b],#[0xfffe51865c3ffb28c32e,0xffd905d954ffec82eab0,0xff595805d3ffb20baac9,0xfd9660174ffecab00ba7,0xfe51805dbffb28c02edf,0xf9560176ffecab00bb7f,0x4c01c20126009c0001ff,0x220498040e036002c402,0x2e076e06d2063605ac05,0x40ab009f0098a08ca08,0xda0d080ca20c3c0b8e0b,0x8c10140f8a0f000e880d,0x5012a2122a118e110410,0xa415d21524148813ec13,0x201896181e17a6174016,0xd21b001a7619fe199819,0xa81dfa1d941cf81c921b,0x5a2106206a1ff21f441e,0xd6234c22e6225c220821,0x882622257424d8247223,0x16289e283827ae273626,0xa42b1a2a6c29f4298e29,0xd82d722ce82c942c2e2b,0xf6307e2fe22f342e862d,0x3c32b2324c31d4316e30,0x24359a34fe346233d833,0xc385e37e6374a36e436,0xac3afe3a5039ea398439,0xb83e523d923cf63c243b,0xb24116407a3fde3f543e,0x7643fe436242d8422a41,0x7046d44638459c451244],#[0x4649e0495648a8480c47,0xc24c4a4bf64b5a4aac4a,0x84eb44e184da04d284c,0xde516650ee50644fb64f,0x905406538e52f2525651,0xc5670560a5592551a54,0x1c58a4582c57c6577257,0x3e5ad85a6059e8598259,0x965cfa5c825c1c5bc85b,0x485fac5f345ebc5e445d,0xc46270620a619260e460,0x5264b6643e63ea637262,0x16678c6702667865dc65,0xec6a3e69a2692a68b268,0x7a6cf06c786c126b886a,0xf66f6c6ef46e6a6de06d,0xba721e71a6711c706e6f,0xea753c74b273aa734472,0x8787e77e2776a76bc75,0x267b9c7b247a9a79da79,0x687ea87de87d4c7cc27c,0x8681fc813c80b280167f,0x4a849c84008376831082,0x8c8802876686dc862e85,0x628ac68a4e89c4893a88,0xc88e3e8d6c8cac8bec8b,0x1c918090e490368f528e,0x4c94b093f0936692b892,0xd69816977a96ba960c95,0xd09b349abc9a32999698,0x7e9e9a9e109d2c9c909b,0xc0a224a1aca122a02c9f],#[0xcca50ca470a3f8a36ea2,0x90a7bea734a6cea668a5,0x1aab7eaae2aa34a962a8,0xccae42adb8ad2eac92ac,0xd8b118b06aafe0af44ae,0xf6b46cb3e2b322b274b1,0x80b7c0b6eeb652b592b4,0xc2bb02ba30b994b90ab8,0x16be56bdccbd1ebc82bb,0xd6c1f2c10ec072bfd6bf,0x96c5e8c53ac456c396c2,0x68c9a8c8e8c816c744c6,0x74ccfccc4ecba0caf2ca,0xa4cff6cf6cced0ce10cd,0x9ad35cd2aed224d164d0,0xdcd72ed65cd59cd536d4,0x8eda04d98cd902d866d7,0x52dcc8dc2cdb7edb06da,0x82dfc2df38de9cddeedd,0xfae370e2d4e1f0e11ee0,0x88e5ece562e4eae460e3,0xcae90ae85ce7d2e712e6,0x7cec04eb8ceaf0ea42e9,0xbeeedaee2ced5aece2ec,0x12f29af1daf13ef06cef,0x8ef4f2f468f402f366f3,0xf8f76ef6f6f66cf5e2f5,0x62f9b4f93cf8c4f870f7,0xccfc78fbdcfb88fafefa,0x36fee2fe58fde0fd56fc,0x8f0117009f0026ffc0ff,0x91038102e50291021901],#[0xc386423c6e286381c144,0x704848f143382e07042,0x82161f8c1a0c0491fc9e,0xe085896325037c5c1703,0xf8545e07042c470833c0,0x263e1b09c0e092232b86,0x1785c0e085870408b8bc,0x8ce4e1a8fc1120e1b0cf,0x83d8fc0c1707130c1f0b,0x2c862f0305c1c483e183,0x16211314e384781c10b2,0xa2ca4c8478b14e031f82,0xf624ae14e3c478016e0,0x8b61488f1780c7e08588,0x44c8478ac7e07068d892,0xc49485e031f822d14311,0x188896c29c5a331f81c1,0x44f04523f018fc11688,0x6313c0e0a2c9e331423c,0xc0e0e2452287b8c5a888,0x14b16c5e07071229140f,0x1408e24462de2f028fc,0x2c6022c6e051f8389263,0x8fc514f0382184b0c23e,0xf161d2382e07068e1645,0xa462c3249228be07068,0x5c0e08585233178147e,0xe344613c0e0b1c3c3846,0x83211e351613c0e08a48,0x821e268b09e004782291,0x1191c6a280a2309e031f,0x446401f8d19e042705c1],#[0x10c91c662c6613c008f0,0x6124f1a238262c2781c,0x162c3311e296f80c6c17,0x230911f17042de07068e,0xe2c668fc0e0858224464,0xb08c6e060b82238b0a23,0x8347c483c601e0b81c18,0xc151f81c107e247c1703,0x30b8903f038296130c06,0x8145e08b46c4f0382231,0xa2f0305c1c488c7c481f,0xf8b8216f0383470b1606,0x2a3f03831628b614c488,0x44716146e2d07e278b8,0x501b1f81c1169182e07,0x12705c0e088e2c283c10,0x3307d1b8b89e031f821,0x48198bc0c151f8389079,0x1f82a3f1467c0e0b1b12,0x22d201f89e051f822618,0x48a44078200a03a3f038,0x241864f03828b2781c16,0x23f0382c9158823e3166,0x8ac503e1792c6e07045,0x8182e0d1cac3f258dc0e,0x2ce0b0bc0e095884922f,0xb11c0e0d1d2456172423,0xac4e48465bc2e0b81c12,0x152e944961705c0a3f04,0x28fc1a493c0a3f04ac92,0x1a4a4864ba512585c170,0x278182e088c7637028fc],#[0x86e060b8256118bc62c9,0x107d246a4c2f81c10915,0x25c1a488c5c131f81c,0x3824f018fc1c15241e37,0x21f25c7c2d189182e051,0x48ac383d34c7e0706921,0xc1a48ac5175278fc0e08,0x7078fc0e0b2456201b81,0x3822b1792c6c1703834,0x4ce4e0b81c11193c9637,0x7268fc0e083c92de140e,0x585e0704ac48230b46c1,0x17038223205c0f64f1f0,0x81c12b0986046179346c,0x47268dc0e08ac66481f,0x70456301b81c1648ac5,0x93c0e088c4c28218dc9e,0xc40218dc9e004b82231d,0xb0e298c0538b47e07052,0x9214238a598a06381c14,0x64860811f163147e0705,0x382291c2829e2e1b81c1,0xc37058a52318a14e4f0,0x4522e303c5a8a06393c,0xc0a3f070416239386e07,0xf028fc18b25064ba518b,0x88662f028fc1c1524962,0x2b178147e0d2528325d2,0x7042c291497c0e085852,0x314c131f81c10b1202e0,0x2e098fc0e0c58914f14b,0x80c7e08522c306c2829e],#[0x1bf158fc0e0e082c58a7,0xf05c0e0d2480dc52921e,0x2c3703834928b294e286,0x62c231436590c2538b8,0x9b63f0382140b11c0c17,0xb1f8bc0e085292388f8a,0x3c78a60b81c10b858807,0xa05219c9e031f821e219,0x36148651793c0e08a488,0x21e268bc90a703822918,0x48f14a280a19c963f038,0x825a2228178672781c11,0xe08b464a20b19c9e061b,0xe8bc0e085086481f8145,0x6c170382231d368ce4b1,0x1705c0e086c2c4023938,0xc9c131781c10d901e8a7,0xe0a8f86e070592445219,0x386c17028fc107900fe2,0x40140747e07045a40239,0xdc9c17028fc107920f0,0x258678049e08a4704317,0x48a4525f038349148bc6,0x91c0c151382492f81c1a,0xc170382562331c5c3d18,0xb81c1a48a4414a638a19,0x922b178a29e070430561,0x14f038218a48c0fe0706,0x79082e4d1b81c1148dc5,0x5622239382c3f028dc10,0xc3f0383456493c0e0b24,0xf93c0e0d1491983f8d82],#[0xe0b2430383d99826361,0x278146e08ac6a371453c,0x6a170313c109c30607f,0xe0c588a3f0313c109c3,0x38316206618e2b0833c,0xc18b15c61486b841962f,0xb0837c0e0c587617030f,0x41a1486f83c08b0e18e2,0x291b80c2c3f071257198,0x7042c29170b09e006782,0x4196342781c1859019e0,0x29100fc0e085852296f8,0x42f81c10b0a45e07062c,0x243c331f8146e0e243c3,0xc0e0e24522d198fc0e0e,0x90f0dc00d707121e168d,0x3821a858cc6e07068f8,0x8703f038216148b89637,0x6148808a351f83c0c487,0x1807c0e0c58522f03831,0x58d89200dc0a3f07121e,0x4e07049a383f8434e070,0x6e2c336b84c7c34218b8,0xc2e07046e30a585c0e08,0x3168fc0e0e243c303c0a,0x662f030f42e0e241e4,0x483c100501d0b81c11b9,0x46992bf083789e070616,0x237140dc0c3f07121e18,0x4f0185c11b8802a2f038,0x660f617171346e070432,0xc29130fc0a3707121e18],#[0x4f018fc10b8786e07052,0x37420ba3393c0e08a48e,0xc402392c7e005f821e1d,0xb8e2ea4b0b8e17e07062,0x2e161c1e9a63f0383490,0xe08e6923f0936c7e0704,0xb81c164868863f0b8017,0x90df038229181f17e161,0x23921fa3f043d171b0bc,0xc9046179386e051f821e,0x6330a00c37268e1ee087,0xf4707e1b81c2e08e5924,0x291410c2e485f81c1118,0x61f82c90f0c03e07052c,0xc6e4f0035c10f0e06e0,0x39a48e06e0706922b141,0xf043d1a1d8dc2e006b82,0x346e07045635183f4ce4,0xa70a8dc0e0b243438239,0x83c90781685c0e08dc61,0x238218bc9c350b8187e0,0x4878607b0b8bc0e086e9,0x93c118c6c8c361f83c0a,0xe061f821e1c6b1a8be33,0x80545e07046e28239386,0xa8a44780c7a37058b843,0x45a261c3d88a4321869,0xc5e07045a4e258e12e07,0xf068c112c5d890931c2e,0x248ce28184cf1780c7c4,0xa22182df158fc0e08531,0x52262222c6e062782291],#[0x148ac7097198bc0c4f04,0x3834716961288f0313c1,0x82853180a2298611e2f0,0x21463714b629e0707121,0x324917c0e0d1e2c911e2,0xc2c5a38468bc0e085852,0x3c1088a4863c242dc0e0,0x7042c291c33c6a2f021,0x8109e08a44c43163311e,0x84f038219149519e302f,0x383471695112d02f8c82,0x21b92298c84587c50b70,0x78814c458ac30b703838,0x291c2e91a370313c1638,0xf0452505c3745e07042c,0x238cd3291a285e8dc0c4,0x87870be268dc0e0a445,0x8257148a11a331f8189e,0x1824781c18b0a47e0627,0x83dc7e06278257489043,0x60587b13c0e0d1c4c4c5,0x3f0545e07068e963025c,0xc1a3a4494a24459890d0,0xe24b438681f45c4b1b81,0xfc148878808e098dc0e0,0x4f04b4911c57c6e06268,0x13c0e08985a487b8dc0c,0xc4f044c291d154763c2f,0xf05c0e0a58463a658dc0,0x80de0b81c14b08c61306,0x1d23c50c05381c18b16c,0xd2250458b82e0707125b],#[0x16f8a2c1485381c10b51,0x789c17145bc0e096e2c5,0x3f146fc0e0a462c58d84,0x23c12dc587198b03d89a,0xe0627825b488e23e2f01,0x686c5e031f822d303dc5,0xe08b49198a532988551,0x45a44598a30e3e244dc,0x1e8891161be278bc063f,0xb186647198bc0c4f068e,0x3c114921e0cf178189e0,0x48cc715c644dc662f031,0x81c14b15c662e2781c11,0x199118198a713c51b8b7,0x19a50a433c5c4f018dc1,0xc622502e03268fc1c2b2,0x41011f030bc164861984,0x1c6225c0c2f068ed62a2,0x8d85e032782292024c31,0x61b33802be08a4a15845,0xf8382a4534a630530ac4,0x1a453484d2490bc0a4b1,0x229a921d34984970293c,0xc0e095846331f8149e0d,0xe17818263f04ac404b05,0x40fe060b82c7ab14232c,0x6098fc12b1012a1a692,0x4c7e0706ac608cb785e,0xab0e9a4c24a862b07e17,0xb825630474363f038292,0x9646d490903f0ac7e060,0xc0ba4f0305c11196492d],#[0x288f8182e0b1a88686b8,0xac231f11486460cb659c,0xe09592430670b82e0704,0xb0bc02b704b240668fc0,0x9c170382232c921207e0,0x2781c14916471589b8d4,0x1b63f038256890c23e35,0x481f85e060b82562d90,0x7c4e1d3305c0e096c465,0x270e99c0e0a48b646145,0x8c5e015b8312118a23e,0x9c0e0b2c523e0b81c12b,0x4f1781c1a38b4ba411e2,0x83860c16298c050228c6,0x2c6714089678a29e0327,0xc5e270c2f8ce07042829,0x3170dc0e08a45648488e,0xfc0a3f062c94222812c6,0xbf028fc1a4a508c12492,0x33c025f042c291b04924,0xd61a93c063f04961e20,0x48e170912f81c18b0a47,0x96291d36940b703834b1,0xe0d2c52326d2949e0706,0xb80c7e0d243c425293c0,0x3137038316148e14a2e1,0x518bc0e0b1f051624604,0xc762f0382148b14da0f4,0xf0382148b102ea485c24,0x3c0e0c58b2486c53c563,0x85a8e942866940c7142,0x2c291cb22c148478bc0e],#[0xe0c5928385c28c5e0704,0x781c1c116480cb168fc0,0xe085b0459282986a4b1,0x62c942128361486f8bc,0xc12cc58b2c86f8bc00c7,0x14361988e9382e28b781,0xf5268fc51bf0382948b,0xc47c5e0704b2948b0e2c,0x5a407b8b49e0704b2941,0x169697a385a93c062f04,0x97494328f4963f018bc1,0x50c2dc5e07058e2d285c,0x7c5e031f822d28529b0a,0xb1e931420529b4c4328,0x81c10a0a490d03d8bc0e,0xe0b24b4386f89c386517,0x28fc10f250a0a61b8182,0x14a078a0bf138612c670,0x688a28af89c3c67028fc,0x2e203dc4e1e3381c14a1,0xa4c0ba5825c7e070592,0xa2c4b89c323a3381c10a,0xc298ce05178229313617,0x1148b8a4d91e89436230,0xdca0bf138612c611f81c,0x486e28c30b71705c0e08,0x89c34143383c00d8a4c1,0xe07059314242f146296b,0xf821e8a121e8dc638b47,0xe0a589e270f18c5e051,0x5925c6052c9e28dc5bc,0x10a68f86e2c6e3114e07],#[0xd8ce270d8bc0e08a4bc,0xe1b1781c114942b8dc53,0x70548a6951b8a61b19c4,0x8a68e9a4c21f814962f0,0x24314c258bc0a4f06909,0x49a6129a0707b80c5e0d,0x55894d2481ec50c70383,0xc350c3c9a4c7018bc1c1,0xa60ac450d8bc0e0a62a,0x82564c1429e286c29c0e,0x1490331b8b43d49e2f03,0x4563b163382637038349,0x10c8a490d4678149e08a,0x2430506905c625d2781c,0x546436c6e2a5053c0e0d,0x37182531587c0e0e086e,0xcd198bc0a4f045238a4,0x62348a350f81c1148ac9,0x3618a780c6e0862888c6,0x69b8ca522348645158b4,0xf0678b49e031b8233206,0xf0452570193c12b8a450,0x658ac36c66230d99c0a2,0x928c66431187c0e08a45,0x4e2d1b81c164c6094dc6,0x313c1c416b1a387a371,0xc685f0213c10c8a48617,0x30d8416e070616371c23,0x58523e27805be0e2c523,0xc08b0a460d05d17c0e0c,0xf0382c6c48786418c383,0x2c514b0b81c10cc589a3],#[0xd30817c0e08662c40cc2,0x3d8361703825acb0e340,0x610a78a14e0704371620,0x58a1a6105f83c00dc589,0x28b6278a2de07046e40e,0x2a2d89e10c383c01b8ec,0x116310a8cc5e07071229,0x31713c0a170447192033,0xb11a162781c163064be3,0x2d0b81c11b98334d8628,0x6640cc531888b158696a,0x148e230c0478bc0e0a58,0x62c29142ec6c4f038319,0x905f038316148fc02bf0,0x1c8630e0f022c2918341,0x468408f85c0e095d3316,0x11b8e1ae3627810be08a,0x2f823728681aa170217c,0x341c691a61b092d42e04,0xe2436486817c2e07052c,0x7892a321861714a9c0e0,0x873190d3158457e0f003,0x36292685c064f062e231,0x1b9014e270e1985e0704,0xa2e345d87c20b61781c1,0x1e03243c351f80c9e087,0x1b8149e087a342e1a8fc,0x382372e8dc064f043d1a,0x8a6311462b0d2d45a170,0x4238c71629c0e0c6d2c4,0x250c378c62f078029328,0x81c111c6c98a3118642a],#[0xe0f006e5b1789c3c650b,0x481ca692f43a145984c5,0x82b89c30d63085c1148e,0x517e270c818ca2f04523,0x29103417e17052c391a3,0xb0d281e2d24484c95d22,0xf124b42c4c29152a8aa2,0x9120b516600e4ae292d8,0x89841b0cc59476196e2c,0x8a618ce22371c3d1915,0xd261254363d369038b23,0x95874d50c56984903c64,0x45b2b0c5bc2b0c46922c,0x326d294b1488596188d2,0x12c52325d2516628b852,0x7822ca522c496905161a,0x88798b14206c331651d8,0x88c38a0dc78ac32865a8,0x6446e291862082c8c231,0x2882e0f46d8ac1604505,0x254362d229a3c6e28296,0xf26a86924c55874d261,0x68e4a618dc6718168c2b,0x28c410664c6230c6f181,0x2c14b06c2c6e2078dc62,0xd03c62dc58a98b148a5a,0x8b192b8a462c60c56522,0x1a08d8a2b8c89864b445,0x68c3619c6187194b0b47,0x37144b08368c30e36961,0x11c518ac16046c564462,0x46e28c5148839]]
set_option maxRecDepth 16000 in
def g255H10 := limbs80 #[#[0x10042828000c6020000,0x80003002708420,0x18a3080210088049020,0x423000c012024000a3,0x100202004500000004c2,0x840100c8d3042008001,0xa1484200000120041,0x9843088001840500002,0x9c40004621800410060,0xac093246158c2600000,0x384fb4f86048121000a4,0x96b0003ccd3790000000,0x3,0x74cc000109122200000,0xfa5dca50003a4bc23000,0x58c0000001a309418a34,0xb0000e63800000000004,0x2c74f1bf29e59b4e0224,0xb93,0x0,0xd2b5c4c702400000000,0x45f590a000116663f400,0x0,0x0,0x0,0xa98000393a1129284000,0x6401476000384944c0,0x789ee87b9bc000c6140,0x17d1da50000000976c00,0x8526c970001893,0x878510000000c0b40000,0x400000004537292c7c00],#[0xd2dc149d29000386e86c,0x10000000000008a60a36,0xb743c0000003d650001c,0x626a53426ac9cde6d58f,0x4600002724000d5f8077,0x5aa00000000a624000f,0x25bb0002c0655d800043,0x3155a710000000,0x7f5cc08900035df52b8,0x98e76,0x15d30000000000000,0x78ae0e5,0x6d5dd000000000010450,0x241aca5592716,0x0,0x1a6c000d01f5090000,0xf000000000000000000,0x93ac0000002d22000000,0x7c2d0bb89714055f0000,0x89ce750a70af699603a5,0x57552e4000597400022,0x48bc0000000000000,0x907c0004aa80000000,0x3cbd000000000000,0x247c99800020dd000000,0x74bd6a7704c041,0xf4724fcc9700000,0xc188518fe05f36400000,0x48d7a640000000b8f,0x5497e09ed0000151f784,0x54ab190b592c2e00001,0xda64000495824aa9b800],#[0x314000881800066ab56e,0x4431a8a3b6,0x3519a08993900024b500,0x520c91c0000000000000,0xd2a062e8498000aa15,0x860724f4a7fc2600000,0x2df20000000250800,0x7c79410002a8ad76b60a,0x6cf058000819cd487,0x0,0x2248e240000000,0x38fa6a900000005320,0x39a7682c0,0xe50c0000000000000000,0xe1900000000000,0x37040000656a960,0xc0000000e45000000000,0x12e000000035cc906,0xf17400000000000000,0xc8e000000000,0x35f5452a28,0xd9c8000,0x0,0x0,0x13c00000000000000000,0x87f76000000000000001,0x2da2000000000030,0xd9f55ab8e0000000,0x8440000003d0c360ea7d,0x7a00dd15ae20951ccf7f,0xb5dce274000234c000e3,0x154b000000022f],#[0x9126fc00000000000000,0x212c0cff968a,0xf34800,0x372ea76c008000,0x7400008cc000347941c0,0xf58458700021bc25,0x31a725b41698e8000,0xff000000000000000000,0x6466a4ccb19a1ea00015,0x287847bf66,0x1f7978629c0000000000,0x2e7900000003,0x61a00,0x3830730,0x0,0x90000000000000046f80,0x161df46ed7,0x2db30000000000344d,0x188441d49780000,0xc0000000000694000000,0x5b900000000000000286,0x20d800075a696c0000,0xa718000000018f100000,0x33181150001c5524740e,0x30b296df0460000000,0x21e6528c00000004d60,0xaa04000e68400000,0x450c0498590001e86000,0x8458,0xc000000091cb93d00000,0x3a2,0x68a00000000000],#[0x8b3000344e00000000,0xfcf40014000000190100,0x26a0000000000186529e,0x2,0xe853c14089800000000,0x315ee9fd652000000,0x29450001a290000000,0x29d2000000060200000,0x59e0002a16000000000,0x0,0x35520000,0x80dc00000000,0x0,0x92140000003480,0x0,0xd204000000066c00,0x20ac0000000000,0x46c0,0xb7400000003862e9a40,0xe37c00,0x3e400000000000000000,0x980000002136a690000a,0x4000000244841e4000fa,0x92308c000d9f9ce657a,0x35f7a0000000343946be,0x12707aa000000001,0x1d1e344000000000,0x5e50000000,0xf43800000000000,0x0,0xe0d743df95c000000,0x631000069e8],#[0xb00000000003c8400000,0x787aa08c97c00000008c,0x4410000362c000,0x2293b5e821700000000,0x64d000000000,0x873e238000953bd94000,0x2,0xf55c00081f800000000,0x573800058b400087e400,0x39a800034718064000,0x20f82a9000000000000,0xf43400000,0x62300001e7000315bf83,0x8ed7140001228000a571,0x1913000000000026,0x59640000000000000000,0x5b500a00000000000000,0xc80dc000198a76e80009,0x296f19ce1960002e88b3,0x0,0x544588000000185e0000,0x50000000417c00054176,0xcd5c838e03000021,0x0,0x300002a86592c64c0000,0xc0000000000f54f831d0,0x5b59a,0x28bae26c1a90000,0xd10fad0300019cf00000,0x21c800000000002e3,0x22dc9900000000000000,0x2427216000000000007],#[0x246d0000000049014c00,0x43fc000000,0x88384b85700000000000,0xb0002537000292100018,0x8c800071ec000b2c0a8,0x3cee00000000003c04,0x60000000000000000000,0xa0ef0000000361000029,0x503d69ae2a,0x13d80000000,0x30000000000000000000,0x60f00004537cc,0xb2c4000,0x382b928400000000000,0xc864642e51800000,0xdf30000000000282f000,0x1,0xcd0b000096f6a4315c00,0x4a09d500014e,0x7f000000000540002d5a,0x4,0x845c000000000000,0x96640000000000000,0x86f8378e946e00000000,0xaa8f92377df96011d65,0x86340000000000000000,0xa9400019a1e400000000,0x84000a91000000000033,0xec7000028b6000000089,0xe2af2a40000000000e41,0xd0000166200015770002,0x100025a6000000000018],#[0x43b45320000000276641,0x0,0x1d70002d3100000000,0x54ec000000000000,0x45c094c0000000000000,0x51000061f00001fe6a76,0x24b704af2,0xb2080000000000000000,0x5a000000022136063825,0x1140000d1123d5a416,0x18ce00,0xa3c00000000000000000,0x24ca00000000002,0x983c00000000,0xb2500000000000000000,0x523f95f0000000,0xb99c0000,0xc000000368f9103cd400,0x10320000000838,0xa2000000000000000000,0x4000000000034d7572be,0xc44800000021e0e5c99b,0x3197,0x16740001da300000000,0x0,0x830000000932549695d,0xfa3000000000000779,0x57f4d25d07bcdb00000,0x56304a,0x3e800080d2086e38629c,0x8000000046802fd038a,0x35fa000081545628f0d3],#[0x3718c0ee40807f000,0x12717670,0xa5c4000b810000d7b00,0x9adb05c00,0xa63c0000000000,0x6ca0bc0,0x29440000000d93ba9000,0x114fe42,0x82a278e1cf67751a4368,0x50000000531e43f811e6,0xc235a7,0x9f000000000000000000,0x1289000000000000002,0xfc4200034e22a5000000,0x770c0000002609d98,0xe4f71c4910000,0xa6d80000002e3a00000,0xd7f0000000000000,0x68000017d8000a78e150,0x56a360000000c8dc000c,0x2a0c00089,0x87580000000000000,0x1d3f627c0000000,0xf8600,0x39800003080000000000,0x0,0x2780,0xc000e60b9590003dd487,0x80b0000000680000077e,0x289561ac,0x24fe00000,0x0],#[0x71875c25260000,0xd3001000102800000000,0x2e1000010d8000000032,0x152e0000000000,0x0,0x959c0,0x283b0000000e891d8,0x0,0x24bb0,0x46b0000000000000,0x1e2a2ac0000000000000,0x8645,0x80a800000000,0xdae49240007a4800,0x23cc000910c97b,0x40cc00000000000,0x3c9c4804000000000000,0x255987ab7ac000000,0x46000000017b8000f9dc,0x3e,0x1510a8c4000b4e000]]
set_option maxRecDepth 16000 in
def g255D11 := limbs80 #[#[0xe0564df5765c77d5d171,0x502ffe1d10bff85442fd,0xff571503fe5c140ff960,0x61540fbd74503ef55140,0x502ff61940bff85502ff,0xbff87502ff61d40bff86,0x9c550ff571543fe5c150,0x542ffe1150f7d54543fd,0xbff86542ff61950f7d75,0x5c160bff87542ff61d50,0x583fd9c560ff571583fe,0xefd65582ffe1160efd64,0x61d60efd76582ffe1560,0x5c37f5d170bff87582ff,0xbff855c37f5d570bff84,0xe1d51bff80546ffe1970,0x9c7fd59571ff5545c6ff,0xf7d65553ef5d154ff565,0x61d54bfd86553df5d554,0x593bf5d964fbd74592ff,0xbff855d2ffe0174bfd87,0xe0165bff865d37f5d974,0x597df5d565bff84596ff,0xbff87596ff61d65efd76,0xe1975bff845d6ffe0175,0x5daffe1176bff805daff,0xffd65503ff5d510bff85,0x5d940ffd85503ff5d540,0x543ff61d40ffd86503ff,0xffd81543ff5c550ffd61,0x61150ffd74543ff59150,0x543ff61950ffd76543ff],#[0xffd74583ff55160ffd87,0x61560ffd75583ff61160,0x5c3ff54570ffd87583ff,0xffd545c3ff60570ffd61,0x59570ffd845c3ff59170,0x587ff61970ffd855c3ff,0xffd75593ff5d954ffd75,0x61574ffd655d3ff60174,0x597ff60165ffd865d3ff,0xffd805d7ff61d65ffd84,0x61975ffd845d7ff60575,0x5dbff61176ffd805dbff,0x30807c00f8000ffd85,0x938208072818404f810,0x883cc0e383380be829c,0x585a0154850412b84601,0x87741cd86c81a2862417,0x920232888c21188001f0,0xcc2a38a4828289ac2578,0x83088be42e98b582c68a,0x3718d7834c8cec3278c5,0xde8f3c3b98ea839a8e14,0x190b041c90343ff8fb83,0x927448f9200470915c44,0x4204ee93644c992f04ac,0x1c573957854a94d45219,0x5e8975c5bd96a059696,0x669995864098b4617981,0xe49b446bd9ac069c9a14,0xf9d287349c7c7099bd06,0x9f1c7af9e687849dcc75,0xf8828a0548039fc07dc],#[0x87899a218872a17c84da,0xc1161c1c67170b03045,0x18230213048071bc5c2c,0x4589c0c10c101f1f170a,0x620151f0227043040707,0x6248891411c7c5c0c11,0xc147161c60471b17011f,0x60b0027042c891c582c0,0x6c582c0c10947271f184,0x2f1a088f030624b1911c,0x45c089c1111c9848441c,0x6271f160b030458ac7c6,0x9c7c5c0c116111c5044b,0x60471b151e0b030624a8,0xc9c6c589c047c1111c64,0x6288c604b1b261703051,0x94323924e8285c047c15,0x248e4b1a160b011f0524,0x86c7c60f128249c0c10b,0x2c0c147271f1b0305244,0x17270304cc61a120fc98,0x121c5c50481d308d1a0a,0x70304acd4cc746c9c0c1,0xc6860482216083d1f1b2,0x51c908c6c947c0c1121,0xc1161c60523317261b03,0xb011f052489482c5c047,0x4c582c0c11622521b160,0x5b1f1703052450749c71,0x1714c70cc9c045c18228,0x726331f251703045071e,0x4b1b14c50cc9c082c14],#[0x6c605233160a191f2703,0x52488cc5c947c0c1141c,0x149181c64631b17020b0,0x2701170608929c6c5c0c,0xc945c0c1181c7868631b,0x423151b27030460908c6,0x70742c089c10c131c0ca,0x164b18091f022704304c,0x70b021f0458842c087c1,0x6c245c087c189248d5d1,0x86427011f042c823574,0x1789820bc0c12916231b,0x71b083c691e2703042c9,0xa170b070289c0c129162,0x68640b18791c2f030624,0x4587c5c21947c0c1161c,0x7c0c1162b17086d1f030,0x3046471b193789c5c24,0x4589c0c1191f1b150a27,0xc67170b011b06248c6c2,0x45c7c5c2c0c11619186,0xc0c149171e331f27010b,0x86b263303051ca16c7c2,0xcc985c0c1472a185c3f0,0x1c7b270700c231b17c20,0xc1171c6c685c0a163219,0x50b03046878cc2c947c0,0x7c6c2c0c1491a18231b2,0xc11b1d33091b27030468,0xb0304586c68cc542c9c0,0xa8cc245c9c0c11b1f170,0x683c411d160b03062630],#[0x1791c782451ec0c11630,0x91e0b01170624c118957,0x89c126246a4445687b1,0xb030458a12110bc7c6c,0xc0c12d24456c6e47151e,0x2270444a141189c716c5,0x9c14d24cc64631b151f0,0x53138792c7488582c04,0xc0c112492322160b0127,0x71e160b030558a13104c,0x2c02382c14932483c492,0x48c98859121985c6479,0x82c0c1233448442f0127,0xc95b12851b464792c94c,0xb29205c511b270304488,0x91a181247c6c90fc0c12,0x2a5124531e0b0304592c,0x14591994c54782c0c116,0x450445b1d27170304b49,0x64582c9478cc0c15a1e3,0x172700a70450b1a94148,0xc9c0c11424b85c491e31,0x3052530a461b188cc547,0x5488287c049c14d244f0,0x403b170305253060998c,0x8a86184bc0c149291ca4,0x8a6610c63160a1f03055,0x31911c629c5c0c149182,0x9306117251b0304a4a3,0x1245c62bc9c0c129285e,0xb14a53327030460a1a18,0x8454789c0c18d246c511],#[0x6f091f03045a2c85ac28,0x831ac24547c0c196296c,0x71b150b02270464a5a0f,0x2874523c0c1162ccc604,0x270304a464a99171957c,0x16c0c13724d0690b182e,0xb03045c8c91b1943c5c2,0xec0c1162320504923250,0x251f07005c789170b431,0x42c90fc0c12b286c6923,0x5330304387871a1812c6,0x90b46c0c11a491e204d2,0x6c5d211b270700687891,0x1814c58c42c9c0c11b24,0xc6c650f17085b0304dc9,0x51a42178c29c9c1c01b2,0x394]]
set_option maxRecDepth 16000 in
def g255H11 := limbs80 #[#[0xa045841a5400e1e08782,0x140810049680061801b0,0x41970400026066211b0a,0x58000900020018011020,0x83000c18b0ecc4040618,0x32620881001820a1cd43,0x48300012e10906064810,0x96e0e000cee30070090,0xc13e00c8081041ce890,0x1a00585001c1897e,0x1d8ec000000fb4cc7603,0x860000000ea1c501a3c7,0x53abdc199f0002d2dc,0x86efc0000756988adbf0,0x2c323712162013a41bd9,0x3215a3481ce0a5d6b165,0x5000562ed6c163342d26,0x71cb52239d28003f4394,0x504030003ea695582c10,0x3f34000cca4bcd0571,0x1ade4d42c9336aa8bb50,0x80000006a1189cd5e268,0x1ac200066a800000094d,0xea0790a092afbb800000,0x9bc390800010039,0x3e5000039880000,0xacf11bf61ac1bb5e0000,0xaa80012cc537cb5a,0xfc9400000045c8000000,0x1043c648f48cef326194,0x22d8bb545818ae58fb6f,0xfe0002ab4001f39959ac],#[0x5e4001b3ab3c6dacac90,0xdee0000003,0x34feb8f59b1920000,0xf5e0ec0001d5b000,0x31c8001854e5fd4b800,0xdb32f000000150c6e600,0x33f8d9941fa200068f55,0xe6ea2562fc0599f920f0,0x70038c400030e7c40003,0x5c193b50003b5d842cc4,0x7dd92d10ddf7d3019c4,0x8271a78486fdea400000,0xa39d28001693964d0,0x32ad4c265ea48000aec0,0x48b00032e0000248d,0x3abdcc000000000008e8,0x20000004344000000000,0x4c68001aae147000341,0x6400000012ac00000000,0x2ca67ad24000a1780004,0x5497970000000000000b,0xac8cdf05d87732208ec7,0xe1b685d0000587a0f92d,0x9fa8d3856e9f9849f01d,0x2e867e6ab81340541d98,0x2290001d3300b00063,0x1c000a00000009e80000,0xc1b0000000001ad90000,0x660da6400094b69a4001,0x1196035d50e5535bc000,0x749400162e9642aec00,0xba12c0007848a3000000],#[0xdec81000000026c4342a,0x47e000aa328888c24148,0x2a420000001c51,0x6d4556e7310003119c4d,0x60000003d1048000041c,0x7400000098fda2800046,0xcf4db000000000055e93,0xdfb0e6000ea2200a928c,0x11309a25fa24be980,0xd64192e682a6a2348000,0xfa1d8af14918c7ae20d9,0x6cc739080000cef657b4,0x838475bd00012be8e783,0xa780014aacfa80d1c3fd,0xb33e07000000043ff580,0x775dae00000000005e33,0xc0000000005eac000000,0x681e000000000053da29,0xd1a46762722000169b76,0x42428b5bfed8000c3aee,0x64d02b22727da102b65b,0xabab785ce3e7602d0003,0xb4d622fd7fdc083a5e21,0xec7f180044f7d552c99,0xa8001a98c463a0f35570,0x818ce09f89d8000a5b98,0xb8fa731d163af1c1c8aa,0xf32d3ddcea402eb7baf,0x3790225c9ee7c42b6e70,0x60c922cc9395ec1cbe0a,0xd2866add91fb29b2baa0,0xd1df3619d4f2d5802fb0],#[0x9b408939605ae084e3,0x38fc000ab03a8f9f00,0x1d024f2b14000f2f0,0x6a9400008b36f0001eda,0xc0000004478000000000,0xca820a24504e09c53b49,0xb8fb7bc2800193e6cdaa,0x634c145c9aee68ce60b0,0xa5f7e3ad062104,0x769ad1a89d5561924,0xa568f5358a0d7f0e95c,0xc00049b15b5cff0dc000,0x9b52ba3ec0684824541a,0x76024]]
def g255D12 := limbs80 #[#[0xffa81ff443fb38ff571,0x61ffaa3ff5c3feb07fd5,0xd74ffac9ff553feb8ffd,0xf800ffaedff5d7feb2ff,0xb9f06e5744bcea2b0750,0x2588e6f56c46d3a72658,0x801e0891c18e8b0a0078,0x88f14140822460f1a2c2,0x941248c78d141408224,0x26002824888f18105930,0xa1e4c005049291c34519,0x8f082c0822460e20c468,0x70c1e3c5842200982348,0xa140130458f161401304,0x124098f16140825878f1,0x90b0209266345841e041,0x7921604124b868f0864,0x2c219243c082488351a1,0x361a]]
def g255H12 := limbs80 #[#[0x81420602020c00,0x2cf,0x0,0x6e8000e10b15830000,0x7a4ae8,0x0,0x5c6000002aa00,0x0,0x79a00000000000,0x0,0x4cc0018540,0x0,0x69400000000ce233000,0x8220000000000,0xd7d420011bc000000000,0x2,0x11a800,0x420000022e001a380000,0x30003e28004,0x2a500000000000000000,0x28970f36e00,0x0,0xac00000000932fb0000,0x200000000c2e00000000,0xf3c00004357d7,0x71000000003090000,0xc692f0,0xcc200000,0x474fc60000000,0xfb800432000001560000,0x2eb00000000000000,0x7c80000000000000000],#[0x0,0x1d6665800000003368,0x40000000000000000000,0x359c580000000000030,0xaa8000000000000075a0,0x5b6000876,0x4be00092,0x214000000000000000,0x68c000000000000,0x0,0x36700000,0x2d50000000000,0x42c00000000ad4000,0x8a600000000,0x0,0xa4cb44000000000,0x0,0x4bc0000000000000000,0x0,0x0,0x0,0x9cc0000000000cea7600,0x143000000001b,0x0,0xf50d6e000000000000,0x0,0x0,0xe50,0x2d807000000000,0x1004000000000000000,0x32e000000002248000,0x1d5969000000ba800000],#[0x723eb71400028000000,0x0,0x1568000,0x41f00000000000,0x28000000018a40000000,0xa3800345b05868000018,0x6a700000000000000997,0x243800001e5800,0x0,0x41b000000000000,0x0,0x3d03f200000,0x0,0x0,0x6fc0000000000000000,0x42140002c8000007be00,0x130c0051c0006,0x0,0x1a4c00231000002e2,0x2ee8000000000000]]
def g255D13 (j : Nat) := if j=0 then 0x1c6142240047ff else 0
def g255H13 := limbs80 #[#[0xb000210000be4c12c6,0x9516ba009497233f0029,0x880d00bb]]
def g255L : Nat → Packing
  | 7 => (25,6,6,0,0,8,0,g255D7)
  | 8 => (323,5,6,0,0,14,0,g255D8)
  | 9 => (683,4,6,0,0,16,0,g255D9)
  | 10 => (449,3,6,0,0,16,0,g255D10)
  | 11 => (118,2,6,0,0,14,0,g255D11)
  | 12 => (16,1,6,0,0,10,0,g255D12)
  | 13 => (1,0,6,0,0,0,0,g255D13)
  | _ => emptyPacking
def g255I : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 6 41 3 9 5 0 g255H8
  | 9 => lookupWord 80 397 9 13 9 0 g255H9
  | 10 => lookupWord 170 1709 5 14 10 0 g255H10
  | 11 => lookupWord 112 613 7 13 9 0 g255H11
  | 12 => lookupWord 29 607 2 11 7 0 g255H12
  | 13 => lookupWord 4 23 2 8 4 0 g255H13
  | _ => fun _ => none
def g255 : Forest := ⟨255,13,fun i => g255Y[i]?.getD (0,0),g255C,g255A,g255L,g255I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P7_0 : block g255 7 0 25=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B7 : block g255 7 0 25=true := g255P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_0 : block g255 8 0 25=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_25 : block g255 8 25 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_121 : block g255 8 121 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_217 : block g255 8 217 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_313 : block g255 8 313 10=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B8 : block g255 8 0 323=true := (@block_merge g255 8 0 121 202 (@block_merge g255 8 0 25 96 g255P8_0 g255P8_25) (@block_merge g255 8 121 96 106 g255P8_121 (@block_merge g255 8 217 96 10 g255P8_217 g255P8_313)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_0 : block g255 9 0 37=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_37 : block g255 9 37 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_133 : block g255 9 133 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_229 : block g255 9 229 88=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_317 : block g255 9 317 96=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_413 : block g255 9 413 96=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_509 : block g255 9 509 96=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_605 : block g255 9 605 78=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B9 : block g255 9 0 683=true := (@block_merge g255 9 0 317 366 (@block_merge g255 9 0 133 184 (@block_merge g255 9 0 37 96 g255P9_0 g255P9_37) (@block_merge g255 9 133 96 88 g255P9_133 g255P9_229)) (@block_merge g255 9 317 192 174 (@block_merge g255 9 317 96 96 g255P9_317 g255P9_413) (@block_merge g255 9 509 96 78 g255P9_509 g255P9_605)))
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
theorem g255P10_201 : block g255 10 201 15=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_216 : block g255 10 216 96=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_312 : block g255 10 312 96=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_408 : block g255 10 408 6=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_414 : block g255 10 414 35=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B10 : block g255 10 0 449=true := (@block_merge g255 10 0 216 233 (@block_merge g255 10 0 105 111 (@block_merge g255 10 0 9 96 g255P10_0 g255P10_9) (@block_merge g255 10 105 96 15 g255P10_105 g255P10_201)) (@block_merge g255 10 216 192 41 (@block_merge g255 10 216 96 96 g255P10_216 g255P10_312) (@block_merge g255 10 408 6 35 g255P10_408 g255P10_414)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_0 : block g255 11 0 3=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_3 : block g255 11 3 67=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_70 : block g255 11 70 48=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B11 : block g255 11 0 118=true := (@block_merge g255 11 0 3 115 g255P11_0 (@block_merge g255 11 3 67 48 g255P11_3 g255P11_70))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P12_0 : block g255 12 0 2=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P12_2 : block g255 12 2 14=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B12 : block g255 12 0 16=true := (@block_merge g255 12 0 2 14 g255P12_0 g255P12_2)
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

end PEqualNP.Outside.L_meta_35030

open PEqualNP.Outside.L_meta_35030 in
theorem PEqualNP.Outside.L_meta_35030 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o fit _ correct
  exact replaceShort g255R gates o fit correct

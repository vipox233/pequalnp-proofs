import PEqualNP.Defs

-- The two-mode live-state and cofactor checker is adapted from PEqualNP/Outside/L_meta_8459.lean (Apache-2.0),
-- which follows L_meta_1674, L_meta_670 and L_meta_1667 (Apache-2.0).
-- The graph, restrictions and all search certificates below are for this row.
-- The handling of lists with a NOT gate follows PEqualNP/Outside/L_meta_10458.lean (Apache-2.0).

namespace PEqualNP.Outside.L_meta_52652
open PEqualNP.CircuitLowerBounds
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

def inputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000]
def graph : Sig := 0xfffffffffffffffffffffffefffffffefffffffefffffffafffefffeffeeaa00fffffffffffffffffffffffefffffffefffffffefffffffafffefffeffeeaa00
def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 4) || (x 3 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 2 && x 5) || (x 3 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 4 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 2 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 6 && x 7)
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
  (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 3 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 2 &&& x 5) ||| (x 3 &&& x 5) ||| (x 0 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 2 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7) ||| (x 6 &&& x 7)
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
  | 0 => 0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001
  | 1 => 0x1000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001
  | 2 => 0x100000000000000010000000000000000000000000000000000000000000000010000000000000001
  | 3 => 0x10000000000000000000000000000000000000000000000000000000000000001
  | 4 => 0x1000000000000000100000000000000010000000000000001
  | 5 => 0x100000000000000000000000000000001
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
  (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 3 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 2 &&& x 5) ||| (x 3 &&& x 5) ||| (x 0 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 2 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7) ||| (x 6 &&& x 7)
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
  let n := v.toNat % 2305843009213693951
  (n*(n+971)) % 2305843009213693951
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
  let n := v % 2305843009213693951
  (n*(n+971)) % 2305843009213693951
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

def nineInputs : List Sig := vars 255
def sampleNine (r : Row) (i : Fin 8) : Bool := bit r (nineInputs.getD i.val zero)
def nineEdge (x : Fin 8 → Bool) := (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 4) || (x 3 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 2 && x 5) || (x 3 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 4 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 2 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 6 && x 7)

theorem nineTable : ∀ r : Row, bit r graph = nineEdge (sampleNine r) := by decide +kernel
theorem nineList : List.ofFn (fun i : Fin 8 => nineInputs.getD i.val zero) = nineInputs := rfl
theorem nineSampled (r : Row) : List.ofFn (sampleNine r) = nineInputs.map (bit r) := by
  rw [← nineList, List.map_ofFn]
  rfl

theorem nineEval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates nineInputs).getD i zero) =
      (C.wires (List.ofFn (sampleNine r))).getD i false := by
  rw [← b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),nineSampled]
  rfl
def neighborRow (i : Fin 8) : Nat := [3,4,5,0,0,0,0,0].getD i.val 0
def absentRowRow (i : Fin 8) : Row := Fin.ofNat 512 (1 <<< neighborRow i)
def presentRowRow (i : Fin 8) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< neighborRow i))

set_option maxHeartbeats 1000000 in
theorem requiredInputs :
    (∀ i : Fin 8, bit (absentRowRow i) graph ≠ bit (presentRowRow i) graph) ∧
    (∀ i j : Fin 8, i ≠ j →
      bit (absentRowRow i) (nineInputs.getD j.val zero) =
      bit (presentRowRow i) (nineInputs.getD j.val zero)) := by decide +kernel

theorem binaryLower (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : PEqualNP.MetaComplexity.circuitFun 8 C = nineEdge)
    (no : ∀ k, k ≤ 13 → ¬Live true graph k nineInputs.toFinset) :
    14 ≤ C.gates.countP (fun g => !isNot g) := by
  have goalEq : (execute C.gates nineInputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (nineEval C legal C.output r).trans ((congrFun computes (sampleNine r)).trans (nineTable r).symm)
  have out := get_rep (u:=true) (execute C.gates nineInputs) C.output
  rw [goalEq] at out
  unfold Repr at out
  have pg : bit 0 graph = false := by decide +kernel
  rw [nrm_id pg] at out
  obtain ⟨k,S,hk,run,sub⟩ := extract C.gates nineInputs legal (by simp) graph_proper
    (out.resolve_right (fun h => h graph_proper))
  have ns : nineInputs.all plainWord = true := by decide +kernel
  rw [nrm_map ns] at sub
  have idx (a : Sig) (ha : a ∈ nineInputs) : ∃ i : Fin 8, nineInputs.getD i.val zero = a := by
    rw [←nineList] at ha
    exact List.mem_ofFn.mp ha
  have eq : S = nineInputs.toFinset := by
    ext a
    constructor
    · exact fun h => List.mem_toFinset.mpr (sub a h)
    · intro ha
      obtain ⟨i,rfl⟩ := idx a (List.mem_toFinset.mp ha)
      apply raw_required run nineInputs (nineInputs.getD i.val zero) sub (absentRowRow i) (presentRowRow i)
        (requiredInputs.1 i)
      intro v hv hn
      obtain ⟨j,rfl⟩ := idx v hv
      apply requiredInputs.2 i j
      rintro rfl
      exact hn rfl
  by_contra! small
  exact no k (by omega) (eq ▸ run)


def g25Y : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffdd,0xffffffffffffffffffffffffffffffffffffd1),(0x0,0x0),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffe7,0x24),(0x3a,0xa),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g25C : List ColumnInfo := []
def g25A : List (List Nat) := [[]]
def g25D3 (j : Nat) : Nat := 0x7
def g25L : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,g25D3)
  | _ => emptyPacking
def g25I (_ _ : Nat) : Option (Nat × Nat) := none
def g25 : Forest := ⟨25,3,fun i => g25Y[i]?.getD (0,0),g25C,g25A,g25L,g25I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g25P3_0 : block g25 3 0 1=true := by
  apply cellsBlock (ar:=3) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g25B3 : block g25 3 0 1=true := g25P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g25T : checkedTables g25 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g25 0 0 0 = true)
  · exact (rfl : block g25 1 0 0 = true)
  · exact (rfl : block g25 2 0 0 = true)
  · exact g25B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g25G : graphValid g25 (boundsBefore []) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low25 : Lower true (varsX 25) (graphGoal 25) 4 := lower_forest (g:=g25) (i:=0) (hints:=3) (before_sound [] baseKnown) g25G g25T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K25 := extendKnown [] 4 [(25,[]),(41,[84]),(73,[100]),(81,[67,99]),(88,[67,48,96]),(137,[116]),(145,[67,115]),(146,[67,115,16]),(193,[116,99]),(196,[116,99,32]),(200,[116,48,96]),(208,[67,64,115,96])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V25 : Known true K25 := extend_ok (m:=25) baseKnown low25 (by decide +kernel)
def g53Y : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffffd87f7,0xfffffffffffffffffffffffffffffffffc8215),(0x0,0x0),(0x2f838,0x9ab8),(0x0,0x0),(0xffffffffffffffffffffffffffffffffff01bb,0x355aa),(0x3fe4c,0x36540),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g53C : List ColumnInfo := []
def g53A : List (List Nat) := [[]]
def g53D3 (j : Nat) : Nat := 0xf
def g53L : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,g53D3)
  | _ => emptyPacking
def g53I (_ _ : Nat) : Option (Nat × Nat) := none
def g53 : Forest := ⟨53,3,fun i => g53Y[i]?.getD (0,0),g53C,g53A,g53L,g53I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g53P3_0 : block g53 3 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g53B3 : block g53 3 0 1=true := g53P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g53T : checkedTables g53 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g53 0 0 0 = true)
  · exact (rfl : block g53 1 0 0 = true)
  · exact (rfl : block g53 2 0 0 = true)
  · exact g53B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g53G : graphValid g53 (boundsBefore K25) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low53 : Lower true (varsX 53) (graphGoal 53) 4 := lower_forest (g:=g53) (i:=0) (hints:=1284) (before_sound K25 V25) g53G g53T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K53 := extendKnown K25 4 [(53,[]),(54,[16]),(60,[48]),(86,[96,80,64,32,16]),(99,[100,33]),(102,[100,32,16]),(114,[84,98,16]),(116,[84,66,32,96]),(180,[84,66,32,112]),(226,[84,116,98,16])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V53 : Known true K53 := extend_ok (m:=53) V25 low53 (by decide +kernel)
def g89Y : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffff7437,0xffffffffffffffffffffffffffffffffff0013),(0x0,0x0),(0x0,0x0),(0xbb86,0x304),(0xc2f8,0x30a8),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffed49,0xcc40),(0x0,0x0),(0x0,0x0)]
def g89C : List ColumnInfo := [(16,0,73,0,4),(8,0,81,0,4),(64,0,25,0,4),(1,0,88,0,4)]
def g89A : List (List Nat) := [[],[100],[67],[99],[48],[64],[96],[48,100],[64,99]]
def g89D3 (j : Nat) : Nat := 0x8028023ea6a1221e12148110
def g89D4 (j : Nat) : Nat := 0x4088058702fd0910bd42443e48110
def g89H4 (j : Nat) : Nat := 0x2c300000000000
def g89D5 (j : Nat) : Nat := 0x83227d10
def g89H5 (j : Nat) : Nat := 0x20400002c5b739000000002c400000d024600000000000000000242
def g89D6 (j : Nat) : Nat := 0x3904f
def g89H6 (j : Nat) : Nat := 0x144004280000d600001c0006c28c00
def g89L : Nat → Packing
  | 3 => (2,3,2,0,0,5,0,g89D3)
  | 4 => (3,2,2,0,0,5,0,g89D4)
  | 5 => (1,1,2,0,0,0,0,g89D5)
  | 6 => (1,0,2,0,0,0,0,g89D6)
  | _ => emptyPacking
def g89I : Nat → Nat → Option (Nat × Nat)
  | 4 => lookupWord 1 9 0 9 1 4 g89H4
  | 5 => lookupWord 1 23 0 10 2 4 g89H5
  | 6 => lookupWord 1 19 0 9 1 4 g89H6
  | _ => fun _ => none
def g89 : Forest := ⟨89,6,fun i => g89Y[i]?.getD (0,0),g89C,g89A,g89L,g89I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g89P3_0 : block g89 3 0 2=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g89B3 : block g89 3 0 2=true := g89P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g89P4_0 : block g89 4 0 3=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g89B4 : block g89 4 0 3=true := g89P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g89P5_0 : block g89 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g89B5 : block g89 5 0 1=true := g89P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g89P6_0 : block g89 6 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g89B6 : block g89 6 0 1=true := g89P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g89T : checkedTables g89 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g89 0 0 0 = true)
  · exact (rfl : block g89 1 0 0 = true)
  · exact (rfl : block g89 2 0 0 = true)
  · exact g89B3
  · exact g89B4
  · exact g89B5
  · exact g89B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g89G : graphValid g89 (boundsBefore K53) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low89 : Lower true (varsX 89) (graphGoal 89) 7 := lower_forest (g:=g89) (i:=0) (hints:=3) (before_sound K53 V53) g89G g89T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K89 := extendKnown K53 7 [(89,[]),(153,[118]),(201,[100,116]),(209,[100,67,115]),(216,[100,67,48,112])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V89 : Known true K89 := extend_ok (m:=89) V53 low89 (by decide +kernel)
def g61Y : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffff4441fe49b,0xfffffffffffffffffffffffffffff04010a00b),(0x0,0x0),(0x2781191e4,0x2d955e1e0),(0xb83e1eb58,0x280614250),(0xfffffffffffffffffffffffffffffc03fe11e1,0xd378e11a0),(0xffc001e26,0xd26081c04),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g61C : List ColumnInfo := [(32,4,25,0,4),(20,0,41,0,4),(8,0,53,0,4),(1,0,60,0,4)]
def g61A : List (List Nat) := [[]]
def g61D4 (j : Nat) : Nat := 0x57d4d20
def g61D5 (j : Nat) : Nat := 0x2043fd20
def g61H5 (j : Nat) : Nat := 0x1c000
def g61D6 (j : Nat) : Nat := 0x7209f
def g61H6 (j : Nat) : Nat := 0xa00000000
def g61L : Nat → Packing
  | 4 => (1,2,2,0,0,0,0,g61D4)
  | 5 => (1,1,2,0,0,0,0,g61D5)
  | 6 => (1,0,2,0,0,0,0,g61D6)
  | _ => emptyPacking
def g61I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 8 0 6 1 1 g61H5
  | 6 => lookupWord 1 8 0 6 1 1 g61H6
  | _ => fun _ => none
def g61 : Forest := ⟨61,6,fun i => g61Y[i]?.getD (0,0),g61C,g61A,g61L,g61I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g61P4_0 : block g61 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g61B4 : block g61 4 0 1=true := g61P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g61P5_0 : block g61 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g61B5 : block g61 5 0 1=true := g61P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g61P6_0 : block g61 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g61B6 : block g61 6 0 1=true := g61P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g61T : checkedTables g61 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g61 0 0 0 = true)
  · exact (rfl : block g61 1 0 0 = true)
  · exact (rfl : block g61 2 0 0 = true)
  · exact (rfl : block g61 3 0 0 = true)
  · exact g61B4
  · exact g61B5
  · exact g61B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g61G : graphValid g61 (boundsBefore K89) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low61 : Lower true (varsX 61) (graphGoal 61) 7 := lower_forest (g:=g61) (i:=0) (hints:=1283) (before_sound K89 V89) g61G g61T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K61 := extendKnown K89 7 [(61,[]),(107,[100,33]),(242,[66,64,115,98,80,16]),(244,[115,82,96])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V61 : Known true K61 := extend_ok (m:=61) V89 low61 (by decide +kernel)
def g118Y : Array (Bits × Bits) := #[(0x0,0x0),(0xffffffffffffffffffffffffffffc80cfe4c9d,0xffffffffffffffffffffffffffffc81453cc0d),(0x307700bd5a,0x1014021c52),(0x0,0x0),(0x1f881f0b74,0x11890c0170),(0xffffffffffffffffffffffffffffe00fe073e1,0x254ba823a0),(0x3ff001c6aa,0x2e62d1c288),(0x0,0x0),(0x0,0x0)]
def g118C : List ColumnInfo := [(32,0,86,0,4),(64,0,54,0,4),(16,0,102,0,4),(4,0,114,0,4),(2,0,116,0,4)]
def g118A : List (List Nat) := [[],[98,84],[33,100],[65,101],[81,66],[97,82]]
def g118D4 (j : Nat) : Nat := 0x57d4d10
def g118D5 (j : Nat) : Nat := 0x1a0fd20fd10
def g118H5 (j : Nat) : Nat := 0x500000000000
def g118D6 (j : Nat) : Nat := 0x23440bf
def g118H6 (j : Nat) : Nat := 0x6800316a0000000096000023b0000000000000000000000000003500fb000000c90000007200000000000000002
def g118L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g118D4)
  | 5 => (2,1,3,0,0,4,0,g118D5)
  | 6 => (1,0,3,0,0,0,0,g118D6)
  | _ => emptyPacking
def g118I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 8 0 8 1 3 g118H5
  | 6 => lookupWord 2 47 2 8 1 3 g118H6
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
theorem g118P5_0 : block g118 5 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g118B5 : block g118 5 0 2=true := g118P5_0
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
theorem g118G : graphValid g118 (boundsBefore K61) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low118 : Lower true (varsX 118) (graphGoal 118) 7 := lower_forest (g:=g118) (i:=0) (hints:=34669888) (before_sound K61 V61) g118G g118T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K118 := extendKnown K61 7 [(118,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V118 : Known true K118 := extend_ok (m:=118) V61 low118 (by decide +kernel)
def g214Y : Array (Bits × Bits) := #[(0x0,0x0),(0xffffffffffffffffffffffffffffffe5465d13,0xfffffffffffffffffffffffffffffff57e5411),(0x6985e2c,0x68a1c24),(0x0,0x0),(0xffffffffffffffffffffffffffffffc8e68ce3,0x8800862),(0x0,0x0),(0x30f970cc,0x31746088),(0x3f01a330,0x18300),(0x0,0x0)]
def g214C : List ColumnInfo := [(68,0,146,0,4),(18,0,196,0,4)]
def g214A : List (List Nat) := [[]]
def g214D6 (j : Nat) : Nat := 0x105f
def g214L : Nat → Packing
  | 6 => (1,0,1,0,0,0,0,g214D6)
  | _ => emptyPacking
def g214I (_ _ : Nat) : Option (Nat × Nat) := none
def g214 : Forest := ⟨214,6,fun i => g214Y[i]?.getD (0,0),g214C,g214A,g214L,g214I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g214P6_0 : block g214 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g214B6 : block g214 6 0 1=true := g214P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g214T : checkedTables g214 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g214 0 0 0 = true)
  · exact (rfl : block g214 1 0 0 = true)
  · exact (rfl : block g214 2 0 0 = true)
  · exact (rfl : block g214 3 0 0 = true)
  · exact (rfl : block g214 4 0 0 = true)
  · exact (rfl : block g214 5 0 0 = true)
  · exact g214B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g214G : graphValid g214 (boundsBefore K118) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low214 : Lower true (varsX 214) (graphGoal 214) 7 := lower_forest (g:=g214) (i:=0) (hints:=302057024) (before_sound K118 V118) g214G g214T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K214 := extendKnown K118 7 [(214,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V214 : Known true K214 := extend_ok (m:=214) V118 low214 (by decide +kernel)
def g217Y : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffff1203f,0xfffffffffffffffffffffffffffffffff0001d),(0x0,0x0),(0x0,0x0),(0xfffffffffffffffffffffffffffffffff243c3,0x1c2),(0x48f24,0xe20),(0x0,0x0),(0x8f448,0xf000),(0xf1890,0xf0000),(0x0,0x0)]
def g217C : List ColumnInfo := [(128,0,89,0,7),(64,0,153,0,7),(16,0,201,0,7),(8,0,209,0,7)]
def g217A : List (List Nat) := [[]]
def g217D8 (j : Nat) : Nat := 0x7209f
def g217L : Nat → Packing
  | 8 => (1,0,2,0,0,0,0,g217D8)
  | _ => emptyPacking
def g217I (_ _ : Nat) : Option (Nat × Nat) := none
def g217 : Forest := ⟨217,8,fun i => g217Y[i]?.getD (0,0),g217C,g217A,g217L,g217I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g217P8_0 : block g217 8 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g217B8 : block g217 8 0 1=true := g217P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g217T : checkedTables g217 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g217 0 0 0 = true)
  · exact (rfl : block g217 1 0 0 = true)
  · exact (rfl : block g217 2 0 0 = true)
  · exact (rfl : block g217 3 0 0 = true)
  · exact (rfl : block g217 4 0 0 = true)
  · exact (rfl : block g217 5 0 0 = true)
  · exact (rfl : block g217 6 0 0 = true)
  · exact (rfl : block g217 7 0 0 = true)
  · exact g217B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g217G : graphValid g217 (boundsBefore K214) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low217 : Lower true (varsX 217) (graphGoal 217) 9 := lower_forest (g:=g217) (i:=0) (hints:=3) (before_sound K214 V214) g217G g217T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K217 := extendKnown K214 9 [(217,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V217 : Known true K217 := extend_ok (m:=217) V214 low217 (by decide +kernel)
def g119Y : Array (Bits × Bits) := #[(0xffffffffffffffffffff90e76076406108b251,0xe120160060088210),(0x80b18bb9ca9606f8,0x8ca308b11628202f0),(0x60f83e0c0034e5e286,0x20e0320c4030e5a204),(0x0,0x0),(0xffffffffffffffffffff8f00c00ffea22e6b0d,0xffffffffffffffffffffa3004520c89064680d),(0x7000fff03dd810dd26,0x5214cd60ae88105d02),(0x7fff00003e05e30df0,0x5c1e8841330d0205e0),(0x0,0x0),(0x0,0x0)]
def g119C : List ColumnInfo := [(38,0,81,0,4),(66,0,53,0,4),(1,0,118,0,7),(20,0,99,0,4),(17,0,102,0,4),(65,0,54,0,4)]
def g119A : List (List Nat) := [[],[33,100]]
def g119D4 (j : Nat) : Nat := 0xd15545c45350f465517014d43
def g119D5 (j : Nat) : Nat := 0x9eee2b24a73ddc56550e7db82caa1e5f65d4d43e3aa829a87735c85350eeab88a6a1dd97014d43
def g119H5 (j : Nat) : Nat := 0x15000000f00000bc0000
def g119D6 (j : Nat) : Nat := 0x1002080200200410902d02996264c9932c4cb23b758b16264cb13264c6c00b1600000bf59653bf59253bf58653bfd9153bfd8553bf59053bf59643f7d4e43bfd9543bf59543ef55143f7d4d43f714d43fdd8543bf58f51df54f51df54d51bf59731bfd9531bf59531fd54531af59053bd58453be58053bb58a43bdd8543af59351
def g119H6 (j : Nat) : Nat := 0x2163000000a70000002a0000ee0000a0000000e400001200a8d6252
def g119D7 (j : Nat) : Nat := 0x260821885086420828820660a19d0808280198d00924f8c4a0007c502c01fe53fea9ff14ffc87fd43ffa8ff547fe63fd31
def g119H7 (j : Nat) : Nat := 0x2571b39187206e8cce0059ecb801a53c80c684a488ac92006698ce3e2a4b7de2ce28ed00085e880022189f660010200118003dc1507c03d105
def g119D8 (j : Nat) : Nat := 0x100bf
def g119H8 (j : Nat) : Nat := 0x3c000463a8030a00440cc0000811e04e0000000000000000000000000000000000000000000e8000000000000000187c4000000000d000000b10050400b2290
def g119L : Nat → Packing
  | 4 => (2,4,3,0,0,0,0,g119D4)
  | 5 => (8,3,3,0,0,0,0,g119D5)
  | 6 => (27,2,3,0,0,7,0,g119D6)
  | 7 => (9,1,3,0,0,8,0,g119D7)
  | 8 => (1,0,3,0,0,0,0,g119D8)
  | _ => emptyPacking
def g119I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 13 0 6 1 1 g119H5
  | 6 => lookupWord 2 29 2 8 3 1 g119H6
  | 7 => lookupWord 7 42 5 10 5 1 g119H7
  | 8 => lookupWord 3 55 4 9 4 1 g119H8
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
theorem g119P6_0 : block g119 6 0 6=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P6_6 : block g119 6 6 21=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g119B6 : block g119 6 0 27=true := (@block_merge g119 6 0 6 21 g119P6_0 g119P6_6)
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
theorem g119G : graphValid g119 (boundsBefore K217) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low119 : Lower true (varsX 119) (graphGoal 119) 9 := lower_forest (g:=g119) (i:=0) (hints:=1348) (before_sound K217 V217) g119G g119T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K119 := extendKnown K217 9 [(119,[]),(126,[48])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V119 : Known true K119 := extend_ok (m:=119) V217 low119 (by decide +kernel)
def g219Y : Array (Bits × Bits) := #[(0x8ce30fec5feec002ec40d8,0x102000c008408001cc0090),(0xfffffffffffffffe328008306632134d5cc739,0xf7e45a95bce0534d5cc538),(0x0,0x0),(0x313f03f87d060b64325a8,0x18018048080023e010128),(0x13c1c003ff8040c4d912a56,0x1210003000400002246),(0x0,0x0),(0x1c01fffc000296c9014d422,0xe6444211142958c010c400),(0xffffffffffffffffffe000000033b7202a9905,0xffffffffffffffff081a842a40162000221801),(0x0,0x0)]
def g219C : List ColumnInfo := [(144,2,73,0,4),(73,0,146,0,4),(19,0,200,0,4),(10,0,209,0,7),(130,0,89,0,7),(3,0,216,0,7),(26,0,193,0,4),(18,0,201,0,7),(66,0,153,0,7),(131,0,88,0,4),(138,0,81,0,4),(82,0,137,0,4),(11,0,208,0,4),(194,0,25,0,4),(74,0,145,0,4),(2,0,217,0,9)]
def g219A : List (List Nat) := [[],[116],[99],[48],[96],[48,96],[96,48],[99,116],[48,116],[96,116],[48,96,116],[96,48,116]]
def g219D4 (j : Nat) : Nat := 0x50200000c21084210842d080210842108421084000e0a5437460b6454930d03dd192d915354930d82e5364549325413082de91989db7154d20c2c2539061b7154d209a869b9154d4250120c8665784d91534c120e42e137454d524c120d82e536454d524c120f025957454d424c120e4261574551324c120f0259574551324c120f025d564551324c12083c6a39654f705091093868b9654f7050910ad0e818554d424c910ae0e818550d424c910cd065553e01424c910ec055153e01424c910ce065543e01424c910e60dd543e01424c910e605d543e01424c910e505d784549324c110ec061154549324c110d5065575509324c110ec061554509324c110f405d554509324c110
def g219D5 (j : Nat) : Nat := (if j<1 then 0x304838b2cbba2a698241c59655d1534c120b2ccaec8a9a60906a6e136454d30482cb32caa2a698241e5165e05534c120be0c9702a9a60906f060b8154d3048279325c2a8698241a5985595434c120e8cbaaa8a1a60907865955450d30482ad32bba2a4982419ab84dd1524c120ba5ca2a6a926090752dd15354930483c96c8a9aa498241e496454d524c120fa1c8aa6a9260905d26554354930483e12a8a1aa4982415a994dd5424c120ad5caae8a12609072a5957450930482b532eaa28498241b498554d424c120f24b2aa6a1260907625d15350930483e12a8a9a8498241d8b7550d424c120ec4baa86a1260907a25954350930482b9329baa64982417c3915d5324c120ae5ca2ea9926090770e45754c930482d9728b2a64982415c995dd1324c120ce5c2ee89926090672617744c930483992cbba264982415cb955d1324c120ce5c2ae89926090672615744c930483992caba264982416c995d91324c120e65baec899260907325d7644c930483996eab226498241cc975591324c120ae4cbaa899260905b2659544c930483a92eaaa26498241e4965551324c120ec4ba2a899260907a2591544c930482da726b2ac298241e516554d614c120fa0a9aa4b0a6090770dd53258530483b82ea992c298241ec1654c9614c12087bca305bb2a68843d65f8654d424425cb25c32a6a12211f39560f70509108f8cc2a7b82848853ce5953dc1424433a306a9ee0a12211f390613754c9108f8caf00ba2648847ce418755132442ba720ba2a699221d477454d524c910ba2caa86a9264887c155143549324427c720c2a8499221b458554d424c910f82aa2a6a1264886e16154350932443b0eeaa1a8499221d857550d424c9109f0caf00a126488678dd780509324433c2ebc028499221ba154e01424c910de0a9f00a12648856ce51825d5304432e70abaae498221b538554d724c110b71c92e8b1260884f464f875493044276728c3aa4982213d39361d524c1109e8c9f08a9260886d4e115354930443ac2eab92a498221f41535c9524c1108f9cbb0aa1260886d46155350930443b42e8b928498221f2154549424c110fa0a9aa4a1260884f4653854c9304427a728c2a64982217c3925d5324c110ee1c92ea99260884f4657844c9304433a6ebc2264982219d175e11324c1109e9cab089926088674dd5844c9304433a2eac2264982217c3925d1324c1109e8cc2a899260886d4615544c930443aa2eaaa26498221ec174589324c110fa0baaa499260885f0e51524c93044378708a926498221bc184549324c110fa0aa2a499260885f0655424c9304437870aa126498221bc185509324c110ee1baa8499260887705d5424c930443f02e8a126498221f8154509324c11085bca30db8aa6906e050f8050932442d8728b126498221d4175549324c110 else 0x6c02c50005940746088c14180820502a300040c000402060403040c000802000b4808000217141010002010200041000209e28080123174e5128944a23328944a23328944663319998a25128944a38f28944a25128944a25128944a25128947005128dc4a25128944a251b8944a257b8944a251b1144a25128944a25128944a34a2894466519d944a23319944cc51288cca242288ccae331999866332114676422b944a25128944a25133146465128944a251289448451288cc663319908a23328944665185bcca2e421144a25128944a25128944a251288cca25119b30a2335a144a251289454a5128908ae512895ca2572b944ae42468cca27e19998ae5128944a2422895c66332115ca251288cca233198cc66421994484330043d653825c36154e96f28c12e1b0aa74f39060970d8553c72c16e5b0ac0a9c7ce4182dc5654c25e720c16e2b2a618e582dcb7159530a5bca2e5b8aca9843de5182dc5654c27a720c16e2a9a618af7460b6454930e0fba6c8a9aa49859364b6454d524c26b329c12a6a826175192e055354130da8c1702a9aa098596e5153d89504c34b308a9ec4a8261c5b7454f6254130f29c8aa7b12a0984d6e51854c9504c36a722c2a64a826135995e113254130ccdc26e8992a09857264b744c9504c34b30bb2264a8261e4b645493254130c5bc8f08bb2a690617e17835d95348316f09c0aeca9a418b484e057654d20c5c42700bb2a690636e0f805d9534831d705c02eca9a414b990dd36454d20c4fba307b22a6904ade5186dc5534821eb313b6e2a9a414b7945db7154d208dbca30db8aa69047ce4186dc55348296f28c36e2a9a410f79461b7154d20c5bca30db8aa69062d25186dc5534831e720c36e2a9a410f7966137154d2087acc6c9b8aa69043d66164dc5534833c304c06e2a9a411f3946037154d20c79b2301b8aa69063c59180dc5534833c724c06e2a9a415e192dc57054d20c75c1700bb2869043d65b815d5434823e321c0aeaa1a410fb9061d6550d20d0ec32a8a9a869043d65b8754d614823e321c3aa6b0a412b7946195358520978cb702a9a80904f864b8154d40482f4722a9a84a024165b94595534c120d2cb2f08a9a60904f264b8454d)
def g219H5 (j : Nat) : Nat := 0x180c000000000009100000029800000000000000000000000000000000000000000000000000000000000199000000000000000000000000d4000000000063ac001c38000388800000000000000000000000000000000000000148acc60000000000000000000250e000d000000000000000000000000000000018080000000000000b1000000000000000007838000000000000000044c0000000000000000002a84200000000000000000006a28001a06f095b0800021a00000000000000000000000841000000000000000000000000000000000000000b1480000000000000000828000491b338000000e028000000000000000000180b501645000000000000000000000000000c1a69500000000000004080003c23e6fd3b20d00004e200000000016550000000000000000000000042b00000000000000000000000000000000381e0000006864c3000090ab3200002070000000001a46000000000000000000000008010000000000000000000044b817762800011b213000258400000000058900012c96370c640000000000000000000000308c000216000000000000000019b4000000e04682480600000000019d200000079c000000000000000000000000000000000d658000840054
def g219D6 (j : Nat) : Nat := (if j<1 then 0xd7558d43483a7e116350d20e9d5458d43482b76195350d20cdd7654d43483975955350d20f1d5454d434837a5c97050d20af78558d614827de1d5358520af58654d61483b558d5358520bf38154d40483ea54d42501209f984dd530482fae09754c120bf3815d5304827ee11754c120deb825d5304837ce05754c120bdb8359530482bee11654c120edb83595304827e617744c120cf965dd130482fae09744c1209fb855d1304833e595744c120deb825d130482be617644c120cfb75d91304833e5d7644c120cfb75591304833e5d5644c1209f98755130482be619544c120e796555130483d6595534c120bdb8454d3048376dd1534c120dd97454d30483b6d91534c120ed96454d30483d6551534c120fc98254d30483f4e05534c120bdb8550d30482f6615434c120ddb7550d30483765d5434c120ed96550d30483e6551434c120fc98250d304837add1524c120eeb6454930483ba591524c120fc98354930483f250d524c120be985509304837add5424c120de97550930483ba595424c120fa97450930483ea551424c120fc95350930483f25d5324c120fc9654c930483f25d1324c120fc9544c9304837cdd5614c120df17558530483bc595614c120fd15358530483f8549614c120af78654d424437c54f70509109f584dd5324427de11754c9109f585dd132442fce01744c9109f7855d1324437ce01744c9109f5875513244375dd1534c910dd57454d32443d5551534c910dd77550d32443755d5434c910de77454932443f150d524c910be5855093244379dd5424c910de57550932443e9551424c910fc55350932442fce09754c110df3825d5304437c609754c110bf3855c9304437c5d5724c110bf3845c9304437c5d1724c110fd1535c930443bc5d1624c110bf38754930442fc61d524c110f717554930442fce11524c110f715454930443f460d524c110fe17254930442fc61d424c110bf185509304437cdd5424c110df17550930443f454d424c110fe17250930443f8549424c110fd1854c930443f45d5324c110fd1844c930443f45d1324c110fd1544c9304423de0970d85538f582dc5654c2d6e095354130f538154d504c39654f6254130b59854c9504c3d254932541308bf845d9534823d61b7154d209f180dc55348396595534c120f4953549304836a5d1424c120f89435093048372dd5324c120dc9754c930483b2d95324c120ec9654c93048372dd1324c120dc9744c930483b2d91324c120ec9644c930483f04c9614c1208f582dd9534427c60f70509109f3805d132443d154d524c910f854350932442f8e01424c910af38458930443d454d524c110bd3854c930442f4615324c110dd3754c930443745d5324c110bd3844c930442f4611324c110ed1644c930443f0549324c110fc1424c930443b0589324c110 else (if j<2 then 0xdc6926dc5c2a308ea6dca1a6dc6dc5c2a046dc5c26929f69c85c29b29a498696895292c5c28b84ca91e9008ea8dc8ce8b85c26dc5c25c27f62be6dc6926926926925c26926dc89a6926dc6dc69269269287c6926926926926926dc69256063a69269285e69263a5c25c26dc2be6dc6dc84081a2a002e63a8047f67d82be7ba79c5c27864ca5c25c25c277069269254a69267c6dc69269267c67c54a69275a73471667c7005c25c26e25c26dc6c66a069267c65e6485c263a6145ee5d05c22645a457e5602be54a51c4fe4e04ca4ac47e45043a4243f63c839a3742a034e3203022d42be2a027a26423e22020a1b81ec1ce1b819a17414e12810a0dc0be09807a05402e0009f7825c36154ebde0970d8553cf5725c36154f3de0970d8553cf5825c36154e3fe1172d8153af582d856054f3ddcb61581538ff845cb654c27d60b71595308fd84dc9654c33de077259530abf845c9654c2bee017259530af582dc5654c33ddcb7159530cf572dc5654c2776137254d30bdb805c9534c2f560b7154d30dd572dc5534c23fe1175d8930cf7815d7624c23fe1574d8930adf8454f624c3375d153d8930ed78154f624c31fdd56558930af781595624c357dd55358930a7d859d9524c2bb60a7654930a7f855d9524c2afe117654930aef825d9524c23f61f6454930a7d85d91524c32fdd36454930aed82d91524c2d7e115354930e5f6454d524c3d5e055354930dd9735c1524c3d654d7054930add84d95324c2f3e09654c930bd781595324c2b7e11654c930ecf82595324c3b5e05654c930add85d91324c337dd7644c930cdd75d91324c2f3e09644c930e5d65551324c3d66095354130af984d89504c33edd36254130b7b85589504c3d654d6254130f59854c9504c2f6e113254130ddb744c9504c3b6d913254130f59544c9504c3f25c932541308ff855cf644823f6137558d20abf845d563482b7e0d7558d20af7815d563482bee017558d208fd85dd163482bee017458d209f980dd9534823f61e7654d20add839d9534826fe117654d209f7815d9534827ee017654d20abf845d953482b7e0d7654d208ff845d9534832fe117654d20cbc845d95348337e0d7654d20cf7815d9534833ee017654d208fd86dd1534827e6037454d208fd87d91534832fdd36454d20add83d9153483975956354d20e5f8558d53482b7e116354d20cdf7458d53482bd61b7154d20cf676dc5534833d5db7154d20ed563dc553482fc6037154d20cf686dc5534827d61b7154d20cf586dc5534827d6137154d20cf764dc5534833d5937154d20df180dc5534837a5c97054d20df3715c153482afe117650d208ff855d9434833ee017650d208fd86dd5434827e6037550d208ff865d5434827de057550d208ff87595434823f61d6550d20adf8558d4348337dd56350d20cd else 0xc453094c100530960113020a541007808cc138030824282d3054c0020a06c500101804095040100060c04242007408002020063080350201d408101e301140f501940430a02a394000e8c0022804a28c200a3080b500032302000c038c2040008180820b04342f8cd0005c3000b0c10100c30c330c00348430809d28c044e3042408043630008241d704240420901970c1b1400306000a0c24000830a09970110080c20a040800303c302000c959004300e508000820900082408018c46800630c059020100020c0002808268c000840004040020645000c0408202068c0400084a3020e00128f140030104180800309010002102c1804306000b631f12554c5a500330c05cc0030200082acc0830a0600b3c51550282418085e5e30a968c297029400a3142824078e5c50a01023400142f5c0804474000a02102409d0028c57400010c282405d25c50201082c08043a30b00011000042000c1701118e940036701080794003e400010f1c0420c01000f140a8c004c5020006101a8f14004a302000c27140a8c0050206010c2c18080440201000f1418080040602000110188c0804005d06cf8cf8ce2cd4a1acbecb06dc6dcc9ab40b14692c8cb06c7669254a6924caa1ab406dc6dc6926926926dc54a6926926926dc692a1a5c26dc69269263a4ca7f6c606dc6924cac524cac3c6dc6dc6dc9f66dcc166926dc67cbf0bd26dc6dc6dc6dcbbc6dc6dc6dc6926dc692ba669267cb9069291eb7a5c2b14692b64b4eb14692b40692a1a67ca1a6dc692b225a4b146dcb066dcaf0692ad26dcabcaaea98692692a82a64a466926))
def g219H6 (j : Nat) : Nat := (if j<2 then (if j<1 then 0x818700000000000013b00000563b00000000e0b5c0890000300064235876c113000000000000e30b000000000000b076000000009259a1b70000000000000000000000000000000000000000000000000000000000008441035d000000000000460400000000e3a20000000000000000000000000000b55b0000000000000000888200000000000000001354615391330000000000000000000052850000000000002606225b0000000000000000000000000000000000000000000000001097b39700002029000000000000000000007750000000000000000000000000000000000000b8290000d8830000000000000000325400000000000000000000b63700000000a08000000000c039f06000000000000000000000000000000000804600000000b20b0000000000c6000000007091000000000000b06f00000000000040257072d09e0000f27a60670000a08c00000000000000000000000020c1f1060000000000000000000000000000a031000000008021000000000000000000000000000050880000000021b200000000000000000000000000000000000000000000000000000000000050c4b17a000000000000000000000000000060960396b30d0000c78000000000000000000000000000000000c634000000000000246e0000000000000000000000000000000000000000000000000000000000000000c0b4000000000000000070b30000938a4824000000000000a0171062a10e0000000000001063000000000000cb0b00000000000000000000000000000000a08a00000000000012b70000f55a40655738000000000000f12200000000000000000000f8c0000000000000000000580000d079b97c0000d7b2625a304c00000000b3866553000000004759000000000000000000000000420c037b301100000000000001b1000000000000804e12140000d253000000000000e002000000000000000000000000000000000000000000000000104d0000000000000000000000000000e095000000000000000000000000088700000000b13900000000338b000000000000f0c0000000009019000000500000000000000000307f00007007000020340000b04300000000a08b00008417000000000000000000000000302e00000000000096339026000000000000000000000000103e00000000000000000000000000000000d2bb0000000000000000039000000000000000000000000000000000635100000000f1620000f1631030000000000000000010c500000000000000000000000000000000308d0000000090af000000000000000040ae000000000000000000000000020200601001000010000001300000021001800010060000100210220000002102321100100003510000100120100000 else 0xd14100000000000000000000000000000000076a00000000000000000000e21f00000000000000000000627c0000000092310000000000000000604700000000000000000000e63140770000000000000000007e0000000000000000835b601500005061000000000000f01e0000a054000030c9000000000000e0ac0000212f057a00004a7a43840000000000000000514c000000000000200b0000831d4b6b0000811b0000636a000000000000000000000000f35e000000000009000000000000b31e000000000000000000000042c028d7ba3359000000003156804a000000000000000000000000482700000000000000000000d0a8b3ab00000000000000000000000000000000513400000000f1080000000000000000d57100000000b26a000000000000000004020000000000000000000050bc0000e63900000000605b0000000000000000000000000000000030480000d32b00000000000082bc000000000000c02d00000000000000000000000000000000000000000000000000000000b03fb640018200000000773300000000000000000000000000000000000000000000a37f8298000000000000000000000000628b00000000000000000000000001150000934900000000b05f00000000d49200000000a13c8154000000000000000000000000000000000000000051837071000000000000000093919b1f348f0245000048807293086a0000e0700000000000000000000093b4900e955c0000000030c800000000000000000000743d000000000000000060a90000000031a70000000000000000025c538d00000000000000000000408e00002559d7060000000000008481000000000000000000000000000000009204000000000000000000000000c01d0000000000000000000000000000910cb05700000000000000000000000000000000077c00000000725200000000000000000000000000000000c8887208000000000000000000000000aa4fe607000000000000000084960000000000000000000000000000000000000000000000000000502400000000c03b0000000000000000000000000000a3820000887f0000001f0000196b8053000010ad0000b58ab3b50000000067040000b3b60000228050b1000000000000d12d0000000000000000000000000000e0810000000000000000228a00000000463200000000034ff051f09c000083c500000000000000000000000000000000d84cc3560000c016000000000000a3180000d22f00000055000000a00000686c0000000000640000000000000000016a000000000000000064900000d0ba000000000000000000000000000000000000644410a400000000535f30180000206e000014214099000000000000100683109739) else (if j<3 then 0x384d0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000d41500000000937e00004357000000000000000000000000000023190000000000000000000000000000d06c000000000000f083a09f4413807ac02000000000000000000000f20700000000000000000000a01453000000000000000000000000000000000081b00000000010900000727400000000c0b20000502b0000000014420000000000000000000000008092287c0000901c0000000000000000000000000000000000000000000000000000104b9920d787000000000000000000000000149ca0690000000000000000000000000000000000000000b0be20aa0000304400000000000000000000000023c100000000000000000000000000000000000000000000235a00000000000093550000e66b000000000000000000000000000000000000000000000000000000000000823400000000000000000000000022ba00000000000000000000c655000000000000072f00000000297a0000000000009881000000000000000000000000303c0000000000000000787e00000000000000000000000020490000a57d00000000000000000000000000000000f4680000000078aa000000000000000000000000822b000063120000200d000000000000e26d000062be000000000000000000b9206a000000007084f62f0000000000000000000000000000a09d00002032e003000000000000000000000000000000000000e0520000000000000000000000000000343e00000000000000000000a609000050ab0000558b00000000000000000000000000000000336d0000a04000000000000000000000000000000000000000006422907d08c1000080c30000000000000000c08500000000c85a4075000000000000000028260000000000000000000000000000000000000000000000000000000000000000000000000000560a000000000000000090100000000010b767540000a20a00002027206d0000000000000000000000000000657b224e00000000e07800000000000000000000a30f00004828402f00000000c180000000000149000000000000d02c0000000000000000000091670000a01b00000000000000000654000000000000d0a10000000000000000c3c800000000409300000000804500000000000000000000c6380000000050560000000000000000000000000000631a102200000000000000000000000000000000000040a50000907410a734670000f023000000000000000083aa807c00000000c03a00000000610b0000000000000000000000000000a0bf0000a03541880000000000000000d01a0000000000000000a098000000004b120000d37d0000 else 0x877a739d000000000000000000000000000000000000000003538b0c000000008886707b000000000000082a0000000000000000000000000000f394700800000000000000000000594e41270000000070598255000000000000000000a30000000000000000b14d000000000000000000000000000078b0a0410000000001b30000000082860000000000000000d0b000000000000000000000000000000000000050caa212b068363c920600000000000000008082000000000000000000000000d05a0000000000000000a0b6b09a287a746c00000000b036c05d00000000000000000000000000000000000000000000f2b1000000000000000000000000302ae66c000000000000000000000000000000000000000000000000606600000000000000c7c00156053443a17c00000000163500000000000000000000000000000000000000000000000000000000205e00000000c0c2530e708fd43a00000000000000000000000000000000203800000000000000006138000021200000000000000000000000000000000000000000109400000000000000000000857c400f005c0000d6300000c436000000000000000000009416000071183287d06b0000100a0000500c00000000000000000000000020bb0000000080050000134a00000000000000000000b7b700000000000000007981323b000000001181d1120000000000000000a3b3b126f0370000b09b000000a2000050879086911f0000000000000000000000000000000000000000000000000000000000005572d0330000000000000000000000000000712300000000000000000000e0040000000000000000b0a60000c75100000000000000000000000000000000000000000000000000000000000000004608000000000000000000000000b5910000443f00000000000000000000000000000000000000000000c205000000000000000000000000000000008073000000000000746b000000000000000000000000c03d00009012404f00000000000042350000000000000000311d00000000d0bd000000000000000000000000000000000000000000000000000074706466000000009151000000000000000000000000b82500000000000000000000000000000000e0b8000040130000000000000000000000000000))
def g219D7 (j : Nat) : Nat := (if j<1 then 0x215703971b417a5702180af53281c6306020b2e3a83282e5002546306c6080881a1820030b811c080698c10a24100aed318d5da000220a1205a63ae3020210b055c0880805702200ae0430201a02c628bc60808800502ae05a0c0ab810c00c045c08a040650c20a0d0c0e50030200043082c347019408c1a1e50020b0c0008828301ca0050c0238113463120400218023020848a080a3002a304022c70234789629802a338669400824078e608a0c00085dc2f44604505d0301462e8c694008300010c0800b3e44a044d18c10010482d1171801b445c60800a080a3002060404045463793f82f75767f56f4973872ae85720de66bef1df10702ef1ee0ecfd3c677ebeeadea068f685677de666de63e56645634626e26e126015ecde65d55c45b6da259153c57cd6bd5ad49d3c413d27d16d094fbce04cf4be4a649548446c454443435c21413c02bee3dd3c52923b439fb92388373b6634e33631e262b0d2f1add2c52b429c292281270262a4e23d225217a031f21da1c91b10779a018f17a96995194092c1140fc0eb0d30778c90b48a008f08187786685583d8290180005ff7258153dfac4b02a77fdc9654c3fbb8aca986ff7259530dfae4b2a61f75c9534c2ffbaac4986fd6558930bfee8b1261bf591624c3eea9ac4986fe7654930dfaeca9261bfd91524c3eeb9aa4987f97054930fbaca99261f7591324c3eeaa264987f96254130bfeeab1a41bf595634837fbaac6906fd7558d20dfee8b1a41bf5d163482ffbb2a6906fe7654d20bfaeca9a41bf5d953482ffba2a6906ff6454d20dfac8a9a41f758d53483fbb8aa6907f97054d20dfaeca1a417fdd543482febaa86906fd6550d20f7aa8a1a41f754d43483fcb8286907f55358520ff2a6a0241fe5d530483fcb2a60907f9744c120ff2a898241fd54d42443fabaa64887f5744c910feaa8992217d5c36154f7ab86c2a9cfd72d8153deec2b02a73f5cb654c2fbb8aca984ff7259530deee2b2a6177dc9534c3ebb8aa6984fd75d89309fae9b1261b754f624c3aea9aa4986df654c930dbaca99261b7d91324c37db12a0987d932541309fae7b22413f5d7634827fbaac6904ff7458d209faeca9a41b758d53482fbb8aa6904fd7650d20dbac6a1a41bd58d61482fdbaa60905f9754c120df6ca98241be59530482fdba260905f9744c120df6c898241be59130483eca9a60907d9434c120fd2a498241fa50930483f8b0a60905f7754c910beaea992217ddd132442faba264886f5644c910faaa699221f550d32443f2a9264887e5424c910fe2ea98221fc5c930443f8a9260887f1424c1109eae1b0aa73ddc5654c3aca9aa0984f571d91209eae3b1a41ea50940483e499260904f77654d109eee8b12213d5d942442f9b8284885f3754c110be2ea98221f454d3044378b1260887d1324c110 else 0x9c8001331720200cc41201986241000c48200cc47001986283650020602d030c0420010050181140830d9400a104e702284120008210301000840d8c13413182681860405a0805a04181010c0630805408080c61a80202a08a00e300254020030d8c101a82a5288c00826a02c6005020e300045892318018214022c31a2f1b4002e31601a0808a430030590d318110481000841426b8110582021c3499408014506040041618086343000c4d8a60a215003d8a654008cc0d5002090460995003330350108e198200200f19ea656630904e19a5003016794008092800da00034c10a001010c05368084140b280a6286694c10824100699698c259d4042090d5013314037021d70)
def g219H7 (j : Nat) : Nat := (if j<3 then (if j<1 then 0xc4e400000000000004230000000000000000000000393f8000080d20000000000002c1a2601f0000000000001407a0000000000001447b2086a011e58d0000000000000000000000962a8000000000000000000000000000000000200be4a0200000000000000000000000000000000000000000000000000000006025e814c00002d0a000000000000000000000000004212000053550000141f0000000000000019a800000000000000000000000000000000000000708380002a0efa62b00000000000000000000000000000000000000000000000000000000000000000000a0818000000000000000000000000000000000493bc000000000000619f6412942d10000000000000a44400000000000000000a30e0000000000000000000000000000000000312f3cdce0000228e0000000000000027400000822c00000000000030c780000d0068000000000000301f8000000000000a37489108000000000000291a800000000000000000000000000000211318dd5e89e00000000209ea204a0000000018224000000000000341f200000000000034030000000000b030000000000000000000000000000000000000000000f28d00000000044396b17380b80000000000000000000000000000014a0341f40eee0000000000000000000000000000000000000000000000000000000209e0000102eca02de80d8000000000000000000000e2a300000000000000000103c8000382160000223c49044000120fd000000000000000000000000000000000000002a18c000180250000000000000000070375035c0000000073560000004930055e065ea2a0000000000000000000000000000000000000000000000000000000100b60044800000000000000004c9e40000000000000000000000000788580000004442c10000099d400000000225c281d8000000000000000000000000000000000000000a1545380000000000000721780001cc320000000000001481000000000000000000000000000000000000000f00f241fe9dbfa8654061000018176e0a30000000000001e049000000000000000000000000000000000000000000289260000000030b2000000000302c00000805600004451800000000e091727600000000180990000181e00598000000005a280c88608a400000000000000000000009228000000008052800000000000000000000000000000f008000010182000000000000000000000000011a100000000000000000000000000d14f80000000000000000000000000000001100111101001004110001011110230510010202300001060010110001000003101000005113000060000000401300020100100003140210001211000001500010000081021003000313701010000200200 else (if j<2 then 0x5033b0962000000000000000000000000000000000000000000000000000000000006921c00000000000038a380001880f927d00000000000009087d02a80001a21c00001598e8da80000000000000000000000000000000000000000000000000000000000000001015000000000000000001402700000000345c400000000000000000000000000000000000000000000000000000000000000000001a02c7104080035a1800000000000000000000000000000000000000800500000000000000000000010100e05700000000000000000000000000000184e9000000000000180300000000028108000000000000181e200000000280e00000c302000030214c84985140000000034470000013390000000000000c24080000c022000000000000000000000904f00000000000000000600d400000000000000000000000000000000000000000000000000185c200004722a020400000000000000000000000000000601f00000265b0000000000000a04f000000000000000000000000020cf20000000000003421c800f000060474000000000000280240000000000000000000000041000000000000000000000000000000000000000000000000000527a0007000000000000000000000000002080800000000000000006a2080000000000007188c00000000e01680000000000008112000000000000000004987c0000906900000000094e800000000408dc00018676000000000000126dd000000000000000000000729d400000000e21180000000000000000000000000000000000000000000000000000000000000000000000000000000000000006d01780000000000000000000000000000000000000000000000341cc00000000000000000000000000000000000000000000001c0e8000000000000100d40000102e00000000000000000000012cfe000000000000000000000a02e8000000000000104100000422200004106490f00000000000003017b82200000c434800000000e2330000000000001a083781c0000000000000000000000000000000000000008042000000002a0c320e100d200000000155120000000000000c8740000c00300000000000000000000000000000000001199d812420ab00004001c00000000a287d39eca2140000000000000000000000000000000000e02900000000000000000174f282bc000000000000000000000000000000000000000000000000002c84e00000000589fc00000000040223128000000000000000000000108e000000000000000000000000000000289c000000003585f280d2401800000000a6970000000000000000000000000109ec000000000000000000000a03f00000000000000000501fc0000000000000000000000000000 else 0x800000000000000000000000000000000000001820c0000000000000000000000000000000000000000000000000000000f07b80003c01c000001260000000000000000000001513b042c00000000000000000302280002c23246e0627700003c1a60000a56200000407a0000b23e800014079c0b0000018a3f04971076000000001892a00000127f313800000000000000000000000000000000000000000000000000145b8000000000000000000000822380000000000005056000000000000000000000000000e1e0000000000001210400000000000000000000000000000000000000000015c48003400000000000000000641a000000000000050720000000010602000000003d0f320e30000502e0000000000000000000000000002140000000000000903d902dc0001250900000000000000000000000000000000000000000000000000000000000081da0000000000001c1c2000000000000000000000000000001918a0000000000000000000000000013780000000000000000000004093000040818000000000000000000000000000000000000000000c0090000000002202000000010a03d803100000000000000000300980000000000000000180df58a900320000000000000a22e0000329ed50d105160000000000000000000000000000000000000000000000000000000000000000000000000000000000000d282d845000000000c051719d00000000000000000000000000304580000000000000000791f0000000000000000000000209d00000000000000000b0728000000000000b388000000000000000000000000000000c028800000000000000000000000000000000000002413400000000722ac0001a6d37249000000000000000006c0e80000000000002dc25c0d604b500000000000000000000000000000000000000000000001e0f20000000000000000000000000000000000006e80001c80ca0be50060000000000000000000000000000000000000000000640700003146c00004c4c0000000000001043d0000000000000000000000a9aac140000000007313400000000000000000000000000000000000000000000006946400000000000000000000000000000000000000041e00000000000000c010000000000000000000000000000000000024580000000000000000081954118000080748000000000000883e840ec0000000000000000149f3e6e100000000108060000000000000000000000000000000000000000000000000000000000000000000160503138099e8000000000000000000001c077c419f51e00001866000000024008d8000000000000380ac000000000000000000000904300000000000000000000000001908f00000000150a600000000000000000000000000000341a)) else (if j<4 then 0xc2460000000000000405e80003054e0000000000000000000000000000000001570a0000000000000250d622680000000000000000000000000c6080000000000000e1020000000000000000000002096c0000000000000000000004609a83a60020000000000000589e40000000000001842200c3c0010000098a4000000000000000000000000000000000000000000000000000000000008059800000000000000000000000000000000000000000000006105000039dc40000000000000000000000000000000000000000006010c00000000000000000000120de000000000000000000000000000000000000000000000000000f13b0000000000000e00b000000000000000000000000000000000000000408000000000000000001424aa20980001c0c400000000000000000000062857423400000000301d10074000020ee3805800000001e0d900000000120b8000000000000000000709c06b0000000000000603180000000000000000000000000000000000000000000000f83700000000000000000000000000000000000000000000000000000000000000009052512f4000000009543800000000000020150000000000000804d800000000008800006802c0000000000000000000000000000020320a06b066f0000000000000000000000000000000000c07b6c1e80001e67b00000000381ce0000000000000000000000000000038198650e0000000018d9daa71000000003cc34000000000000000000000910f000000001840c00000000049c4c03b00000000148940000000000000000000000000293c4000000000000001c400000000c23b00000000000000000000000000000000000000240e50662b21700000000000000000782c80000000050398000360fc000000003213d506400000000000000000000000000000000010a810000000000000e09c0000103f00000000000000000000000000000001ae0000102a10000000000000000007760000000000000c87ada80c000000000000000018e2e0000608e0000000000000901c80002015c80f004332046c0000a4e60000000000000000047248000000002c46000000000000070f2781c800000001b0800000000000000000000000000000000000000000001c0de000000000998c000000000000000000000000000000000000000000000000000000000000000000000000a0c3000000000000020420000184680000000000000000000000000d00bb840000000000000000000000000000000000000000cc67600cc1100000000000000000000001e0cac06340284646e6e1ce05a90069800b8014d82d800000000000000000000000000000f026c833520f2c4ba00000817fc4fa000000000000281140000e281 else (if j<5 then 0x14802000000000000000000000000000000000061130000000000000000000007009000000000c3578000000000000000000000000160e092148000000000000415c800028d62000000000000000000000f027408d9ae180000804b81858000000000000182fc00000000000000000000000000000000000000000000000000000012098000000002d8a1a677000000000000000000000000000001e8830000339fc000000000000603fc0000000000000000000000000b06f800000001c8b4b00a8000000000000000000000000000000000000000000000000001b1580000000000000000000000000000000002c1f600000000000000000000000000000044e80000402d0000000000000b684800000001409500000000000000000b0360000000000000405c80002c1b9e0d50000000000000000000000000000000000502a1219c000000004305800000000000000000000000012075c537c8234000000eb00000000000000000600100000000000000000000010214000000000000000000000000000000000000000000000000000000084548000000000000004700000000088590000010280000000000007181760c600000000380cec1d8000000000b8a40000429e00000000000000000000000001cc5aa28d7338800000001ac0e00005082c000000008363593af5896500ab12e000000000e51d00000000000004046628b800000000a8a10000108649554000000000000340cc0000000000000000000000000000000000000000005185580ce0000a02c80000000000000000000000000000066228000360d400000000101a0000060f3204f800028e16000000000000000000000000000000000080b1e210413dfa10c0000000000000000000000000000000000000000004a14800000000413d000000000000000001829b808800000000000000000c68800000000000000000000040353c48a0000000000000000000000000000000000000000004318e2ccc000000000000000000000634080000000000000000000010d8800000000583100000600300000000000000000000000000000000000000311c5c19f80f40000000000000000000000000000000000c25780000000082bd413f0000000000000000000000000000000000000000000000000000000000000000d0438000000000000320a8000000000000000000003c940000080380000000000000000000000000000000000000000000000000004214400000000110800430000000000000203621c1980480000000000000000000000000385db02d8000000000000000000000592e7c192488000000000281c40000000020a00000000000000202b4000000000000511140000000000000000000000000000000001022a70f30000283140001441f9633000000000 else 0xc1ea000000000000000000000000000000000000000000189ec000000000000000000000a0e87029484140000000000000000000000000605d120c400000000000000000000000000000000000000000000000000000000000000030369022e00000000300f80000a8ac0000000000000000000006018000000000000000000000000000000483000000000000000381800000000a0130000000000000000000000000000000000498380000a096000000000000000000000000000000000000000000000000000000000000014e0000523920a800000000000003013001d40000000000000000000000000091cc00000000000000000000120c76215799c00000000000000000098ae00004014000000001ac49000000000000140fee0548000000000000e673b311c0000000000000000008380000538528a18000148100000281900000000000001312000000000000000000000040b4000000001011e806d000000000000000000000000000000a2df6118000034db8000000005909800000000000000000000000000000000000000000000000000000000000f6348000000000000132eb924000000000d077c1b580001cd173835e41e20d0522980000000000000000000000000150b0000000007499a09120000c010000000000000000000000100fa000000002808c00000000c8848000000000000000000000000000db000000000000000000000000000000000000000000000000000000000001e038000000000)))
def g219D8 (j : Nat) : Nat := 0x9090b8cd5007e332400540871b44c10852820675254c78c60b45c11a80015e55231e32f45c11446154c0178cd5004e33502109080e339d4948e33080954181d130841820749531b8cc90a7506df460c137d23044017043182d255c18c71570d4301188df48c11740815e3144a239401439e49411461c10039461c46154c018c1430401688c2007146828f91e03906cccd9892ee5a0ac93e252468828f01c2348630ae13221c3a8630a20f013815000ff58153ff59530ff58930ff54930ff58d20ff54d20ff50d20fdd8553bfd8153bfd9530bf59530f754d30bfd8930f74c930fe54130bfd9120bf59120bfd8d20bf58d20fd58520fe50120fe4c120fd54d10fd50910fd4c910bdd8553bd58910fc4c110
def g219H8 (j : Nat) : Nat := (if j<1 then 0x5a56000000000000000725ece5000000005201069000079d8b2f6000003980009420000249b00000000000000000000000000100e8000000000000005844189741b4000000000000000000000000006530000000000000000000000000000000000705200000000000000000000000000000000000000000000000000000000000000000000000000062252154000000000000000000000000000000000000000000000038000008dc0000000492800000003a1f0000000000000930000000160cc00069a00000657b83400000000000000000000000000000000000000000292aa1be000000000000000b05f419c0000000000000000000000000000e00000000c00c0000000000000000000000000000000000000000000000000000000000010c54014f2d10000000006d5935000122a80000000768e00000000000000000026df0000000000000000000000141b8000680100000000000000000000000000082c000000000000000000000000002958000000000000000000000000000000000000000000000000000000000000000000000006901000122dde360000e24b62d400000000000827792280000000e1780001a22000000000000000342c81c400044a200000003c1b8000b02000000001856606c0000000000000000000000184f4132000000000000000000000000003629670c000000000000000000000000000003c147317604a0000000183100000000000000000000000000093a000000000000000906a8edc00000002056000000000000000000000048ae18e080448cf0000000000000000000000000000000000000000001a480000000b1db60e90640000000000000004064000000000000001229c000000000000000000303d0000000000000000000000000060b30000000000059f630e481738333860000000000000000000000000000000000000000000000414200000000000000000038e78000d1020002c2c00000001e444000196e00000000000000080c400000000000000017d800000000001c1140000000000000028db800033460002c520000000000000000000938a00000000000b005e0e80000000000123340000000000000000000000000000000000000000000000000000000000000000000284e000000058900000000000000000000000000000000001606c88c0000c27dc34b409800000000002cf580007730000000000004060000000000000001b087411486c0001419400000000000d004000000000000000000000000000000000000000000000000000000000000000023d7248000183b7a2b334385e800000000000000000000009268000000000000000000183c800000005137024da4382d20000000000011111013101001610010000033215017811410306101002400002006300020 else (if j<2 then 0x7050000000000000000000000000000000a2360000c968000000000000004c11000000000000000d69000030a5e0410000a964000480f90e800000001853000000018cb8000e4a60000000000000000000000218f000105e0000000000000000000699d00000000000297600000000000000000000000000000000000000000000000006c6c00000000000b0880000000839200000000000000000000000000000000014c00000000077bc000000082400000000000010080000000000000000000cc400000000000000000000000000000000000001e5640000000000000000000000000000000000000000090f400000003242000345a2846804c0002c21f051000121e000000000000f52c00601c60000000000060180000000000070050000000000051bd000000000002252a02400000000000306800000000000000000000000000000000000000000529c00000000000000000000000000000000000000000000000000000000000000024168000000000000000000f97b0c680003181000000000003c6f0000000c00043b490466a8000000005095a6d8000580779d2000000000004122000000000bd00000000000000000000003525000000000000c0f0000000000000000000205480340000000000000000000000000000038e8e869d7480003ca000003072000000000000000000000061b4000120fd00a0000000000000000000d4afc06800000000000000342580000000000000000000000000000000000000000000000000000000142ce01fb0f600016368000b0dea2080000000967c000000070475288000104bd83e527120840000000000000035d30000000000000006815000000000000000b0d600031ea7139000005dc0000000000000000000000008000000005017000000000000000000000000000000000000000000000b09d65f00000000f0ea000000000000000000000040090000000000000000bda40ec00063e8e2d400000000000000000000000000f72e0000000000000000000000000b000000000000000000000000000000000104ac0000000000101080000000d0a800024518000000161740000c1ed3380000000000000000000000000000000000000213700010090000000000000001c2b8000000000000000000325c0000000385b000000000000000335181f000000000001e18503b80000000000000000000000000000000000000000000040cb0000000000000000000000050c8000000000000070000000000000002974000000000000000000000000000000000000000000000000000018d152050000000000000000000000000000000000000000000000000508c82fd142a25200000000000000000000000000000000000000000000000001bb619be410000048a7a5d000000000 else 0x304e000000000000000000000000000001c168000480a31280000000000000000000000000000000001d2a0000f159e06400000000001283c00079ea92d0000000000000000000045300000000000398f000041d0000000000000000000000000003b3c000000000000000000000000000000000303d0000000000000000000000000000000000000000000000000000000000000000937000000caf00815480000000000000906080000000000000002516800000000000000000000000000000000000000000000000000000000000000000000000000000040d4000100b000000008c700004b37507963500000000000000000000000548c00000000000a0c6000102603b5a039828aa13016b000000000000000000000000000000f2e20000000784d00000003c8b80000000e0b80000000943c000000000000))
def g219D9 (j : Nat) : Nat := 0x31599c830b1499ca322f42846320e41945cf0cf80fea9ff4c3fa41f510
def g219H9 (j : Nat) : Nat := 0x1012c9500000020ca000000000000020400054c00007060004a580000003068000001059820f925810684727f08000000000000000004050000000000000003a02ed276009270001854000138f80cc0565800000000002156718848000d103338000000000d3d8003120000e054830001e14000683c0000000000000402ec3b2b384d06e000e398000000e30000000108d417b08a068000000b48b8604cc0000005214000000000604084602600000000000000002058086e1b0004838000e9b0000000000000d03318c0000000000000000000f14800000000000061c0001a1971aa006683048
def g219D10 (j : Nat) : Nat := 0x87543f1bf
def g219H10 (j : Nat) : Nat := 0x29800000006080000000638000000000000000d000000000000000000000000000000000000000000000000000000e2000008240000000000000000000000e0400000835480000000000000000000000000000000000000000000000000180000000014c00306000000000000000001d100000000000000000000
def g219L : Nat → Packing
  | 4 => (27,6,4,0,0,5,0,g219D4)
  | 5 => (203,5,4,0,0,9,0,g219D5)
  | 6 => (286,4,4,0,0,12,0,g219D6)
  | 7 => (125,3,4,0,0,12,0,g219D7)
  | 8 => (28,2,4,0,0,11,0,g219D8)
  | 9 => (4,1,4,0,0,7,0,g219D9)
  | 10 => (1,0,4,0,0,0,0,g219D10)
  | _ => emptyPacking
def g219I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 13 283 3 13 5 4 g219H5
  | 6 => lookupWord 96 1939 4 16 8 4 g219H6
  | 7 => lookupWord 164 2635 4 17 9 4 g219H7
  | 8 => lookupWord 62 1251 4 15 7 4 g219H8
  | 9 => lookupWord 13 139 3 13 5 4 g219H9
  | 10 => lookupWord 2 111 0 10 2 4 g219H10
  | _ => fun _ => none
def g219 : Forest := ⟨219,10,fun i => g219Y[i]?.getD (0,0),g219C,g219A,g219L,g219I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P4_0 : block g219 4 0 27=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g219B4 : block g219 4 0 27=true := g219P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P5_0 : block g219 5 0 4=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P5_4 : block g219 5 4 48=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P5_52 : block g219 5 52 48=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P5_100 : block g219 5 100 48=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P5_148 : block g219 5 148 48=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P5_196 : block g219 5 196 7=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g219B5 : block g219 5 0 203=true := (@block_merge g219 5 0 100 103 (@block_merge g219 5 0 4 96 g219P5_0 (@block_merge g219 5 4 48 48 g219P5_4 g219P5_52)) (@block_merge g219 5 100 48 55 g219P5_100 (@block_merge g219 5 148 48 7 g219P5_148 g219P5_196)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P6_0 : block g219 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P6_1 : block g219 6 1 40=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P6_41 : block g219 6 41 48=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P6_89 : block g219 6 89 48=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P6_137 : block g219 6 137 48=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P6_185 : block g219 6 185 48=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P6_233 : block g219 6 233 48=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P6_281 : block g219 6 281 5=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g219B6 : block g219 6 0 286=true := (@block_merge g219 6 0 137 149 (@block_merge g219 6 0 41 96 (@block_merge g219 6 0 1 40 g219P6_0 g219P6_1) (@block_merge g219 6 41 48 48 g219P6_41 g219P6_89)) (@block_merge g219 6 137 96 53 (@block_merge g219 6 137 48 48 g219P6_137 g219P6_185) (@block_merge g219 6 233 48 5 g219P6_233 g219P6_281)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P7_0 : block g219 7 0 16=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P7_16 : block g219 7 16 48=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P7_64 : block g219 7 64 7=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P7_71 : block g219 7 71 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P7_119 : block g219 7 119 6=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g219B7 : block g219 7 0 125=true := (@block_merge g219 7 0 64 61 (@block_merge g219 7 0 16 48 g219P7_0 g219P7_16) (@block_merge g219 7 64 7 54 g219P7_64 (@block_merge g219 7 71 48 6 g219P7_71 g219P7_119)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P8_0 : block g219 8 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P8_3 : block g219 8 3 18=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P8_21 : block g219 8 21 7=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g219B8 : block g219 8 0 28=true := (@block_merge g219 8 0 3 25 g219P8_0 (@block_merge g219 8 3 18 7 g219P8_3 g219P8_21))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P9_0 : block g219 9 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P9_1 : block g219 9 1 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g219B9 : block g219 9 0 4=true := (@block_merge g219 9 0 1 3 g219P9_0 g219P9_1)
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
theorem g219G : graphValid g219 (boundsBefore K119) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low219 : Lower true (varsX 219) (graphGoal 219) 11 := lower_forest (g:=g219) (i:=0) (hints:=67) (before_sound K119 V119) g219G g219T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K219 := extendKnown K119 11 [(219,[]),(221,[100,33]),(249,[99,115,81,64])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V219 : Known true K219 := extend_ok (m:=219) V119 low219 (by decide +kernel)
def g246Y : Array (Bits × Bits) := #[(0x0,0x0),(0x846887b941c36d2831a9e,0x100020a30193200030296),(0xfffffffffffffffff08b319c6061492473a833,0xffffffffffffffffe000000800300124338811),(0x0,0x0),(0xb3c6e10d9e8248398d64,0x1010050ca00444308c60),(0xfffffffffffffffff0c3f8fec164e4d34c95e9,0x1efffdf4c444c4d34c1568),(0x1f03ff008a0389012c5696,0x134027a222431a100c1286),(0x1ffc0000f384902d966348,0xcafc850c104c089806108),(0x0,0x0)]
def g246C : List ColumnInfo := [(50,0,196,0,4),(100,0,146,0,4),(6,32,208,0,4),(128,0,118,0,7),(144,0,102,0,4),(66,0,180,0,4),(130,0,116,0,4),(192,0,54,0,4),(132,0,114,0,4),(2,0,244,0,7),(160,0,86,0,4),(20,0,226,0,4),(4,0,242,0,7),(32,0,214,0,7),(38,0,208,0,4)]
def g246A : List (List Nat) := [[],[33,100]]
def g246D5 (j : Nat) : Nat := 0x8182040828081060000000000000000000000000000040000000000000000001932000000000019240c022fe1171d8152a5f855915390b8b5915454a42a5d80d955350b4b5537154942e2d5454b6050ad66026454d50b4f82591535435654d70d0950ceb625c34254317dd95350950c5f7554d62d038b5516254b40d1f7554d42d038b5955250b40d1f7554d425038b5955250940e5953d8950503c654f4254140dab72d0950503c654d4254140f29525095050297e156454f20e2d6455152c822fe1176547208ef825d95448297e156454d20e2d6455152483965915354120d6b74549504839a5915254120d697554940483ca55152501208bf845d9524421fe157650910e696254950443cc5515150110fa142485404427c61f41c8110
def g246D6 (j : Nat) : Nat := (if j<1 then 0x305952d0c1304b4304c1580c145cc1621745814c30400001384e0000012b45cb42d1033bcdb00000304c7304b426485214851c45d1403c0840d0027eba6c4a9ddd74d8953bbae8312a73fdc56494a7eb8ec8a94fd70d9152bdae5322a57edc16354a7eba6c2a967d54d85529fae1b0aa56fdd16154ade3a2c2a94fd74d81529fae3b02a53fdd56490a7ebb2a92167d6555242dbac8a9c85bb5915290bb6aa2a5216dd5358642ddaa4b0c853f5c36550b3fbaacaa14ff7059542cfecaa9a85d7d955350af6b8ca4a167f6554942edecaa9285db5515250af7b8aa4a14fd75d8142d7ca9b0285af5536050b6ea9ec0a16ed52d81429fae3b02853fdd5648ca7ebb2a91967d6555232d7ac8aa4657bdc9548cb7aaa2c3195ef72551329fae5b22a13f5c7645427ebb4c8a857d7599150bf2e1322a17bdc964543af322a6a875d6454d509fae9b12a13f5c762543aea9ac4a867f64549509faeda12a1d754f4254377b1684a85f970d09509feeca12a1d754d42543b6a9284a84fd74d85509fae5b0aa13fdd562d035eaa2c5a06dd5358b409faeca96819f59552d039eaa2a5a06dd6354b40ddac4a96816fdd542d02debaa85a06bd6550b40f3aa6a1681eb54942d027eb96caa04fd71d9540bdee4b2a813fdc96550377b92caa06ec72595409fee2b2a816f5ca54502dfb92a8a04fd75d8940d7aa9b1281b754f625027eb8ec4a067d6554940e7aa8a92816f5d7425035eb2e84a079d53d0940bf6e0a12816fdd542502debaa84a06bf6550940d7acaa1281e754d42503d6a9284a07bb70509409faebb0a81af553615027eb96c2a05bf7454540e7aa8a8a81bbd8921503d6a1242a05fb7254140df6c4a8281de54950503dda12a0a07b94254140bf6e2a8281bed85505027fbaac9904ff71593209faed2a641af59254c827ebb2a99067d6555320d7ac8aa641b759153c8376b22a59076d5454b20ddaa4b0e413f5d951c837ab0aa3904fd76d07209fee8b2a413fdc5654827fbaac8904ff7159120df6e0b22413f5da544835eb24a8905f970951209faecaa241af591544836eb22a6906ed6454920edaa8a92413f5db41482fcb8682905fb7454120df2c8a82417edd540482fcbaa80906f96550120f74a8a0241ee55140483eca9a80907e952501209fee4b2a213fdd5624427fba2c4884fd7654910dbec6a9221bb58952442fdb82a4884ff76509109faeca1221b7d8d42442fdb8284885fb7454110df2c8a8221be58950443bca92a0885fb7550110bf2eaa0221be59540443dcaa280886f96250110f7284a0221fc54540443f890a80885f975c8110bf2e990221fa54b20443f8a8e40887f341c8110cbecaa9a85cb5515250b2eb9aca214df7654c42cbacaa9885b654d6010a6fbb2a7a04ef7259540eb2a6a8281d654d50483b4a92a0904dd75d8d10 else 0x20c27808708106000830e1800610004181d20b3042021410a0820008304002080820810a08182085820808408004082842c08420104001040012618002101001020e1530430208006041830010204c1306623065530400304c130400304c1304b4304c100188620b43058830641304b4620c170d952d0c1304c13058830400304b400000304c12d0c130595580003062682cc1581f7304c1000c1620c17a8c130400304c1620c12d0c130588304c1304c1304c1580c130595304c1305dd741d030560655c330595304003040065595655c3304c162000001b6001a230450304c130560000c1304c1304c12d188620c1305882d138304c1304c130400304c12d0c162188620c1304b430588)
def g246H6 (j : Nat) : Nat := 0x822000004a400000000000e960008afa1000000000000000000040900000000000b320000028a000000000000000000000063e0028000040b98800000000c1cd1e0100000000522001d78000000000000000000000000510000000000000000000000000000000000000018000003072994f00000000000000c09a4a4df94218000000000000000008e0000000021d001f840000000000000000001c4c000000340000000051a000000000000000000040400000000d2e00205800001e80003a500000044000000002ae00000000000000000000000000000000000000000000316f840000000f000f0c0000000000000000f31f8c00000000b5b8e00000000000000000000002d900155c000000000000603004
def g246D7 (j : Nat) : Nat := 0x1011c408a0800cb2040d31c20014c31c44c30810800810c00531040010401c30800870061441840031800430460881800840011031c61404c54c51c31400851021410832050832c50831010801c204b0870020802030810031000830420812820c108a0c28c00c12e300407c0841011c40dc0421042810930050401032c30401000424c41c40530850130432820014c51d30030011131021000442930800450440801010c20040021830401831840c0100042184002a411c5a411c30130811030010c00931441c51a94c20071530431c5081a531930010c00530840b30051050400c11050841460424c50440032000811020c40020872c01061130401452000c14c200411300319300308500320638004218b1c20041804c2105001084002080042001083040081cc00840c600213300108498497295a94284c9309189008ee8d66728b88ac79e89488244486484c8348228047ec7c87b079e78c28277475c7440967327206e470e2d66fc6e46cc0846b46a268a68a67265a63c61e6065e85ac5ac37e5c45ac58e57054c5345104f84da2164bc49847a45c44442c40e3f03cc3b439637e0843603303182ee2d62b829a2822822642402282161fe1ec1ce1aa19217415c14412c1020e40c60a809608406c05a03c01e000000ff99152ff59152ff58d52ff58552ff58152ff55242ffd9542ff59542ffd8d42ff58d42ff54d42ff54942ffd8142ff58142ff55232ff55132ff99150ff59150ff58950ffd0950ff50950ff58550ff54b40ff59540ff55140ff58940ff54940ff50940ff58540ff54540ff48540ff55130ff95320ff55320ff54720ffd0720ff95120ff55120ff54520ffd0520ff50520ff54910ff50910bfd8953f7d8953f718953bf59252bf58652bfd9152df55152bfd8552bfd8152bf59642bf59242f754e42fb54a42bf58642bfd9542bf59542f794d42f754d42fb94942fb54942bfd8142bf59442f754c42bf59632bf59232bfd9150bfd8950df54950bfd8550bf59740ef55340f754f40bf58b40ef50b40bfd9540bf59540ef95140ef55140f794d40f754d40bfd8940efd0940ef50940bfd8540fe54140bf59720bf59320f754f20fb54b20bf58720bf59520bf59120f754d20fb54920fe54120fe50120bf59510bf58910fe54110fe50110fec81109f59442b758c42be58042bd58632d754d50b758f40b7d8d10
def g246H7 (j : Nat) : Nat := (if j<1 then 0x168945c00000f200000000004ece340001002c8400000000000019684b2f9e00000000000000001d1700000000000000000000000000000358944c00000000000000000000003a4905e000000080800000008240012a0000000000000000000038e80000000000001471000000000000000000000000000000000000a190000000000000f0580000000000000000000ea50000000960000000000000000000000000000000000000000379a28269ab5000000000000016c50000000000000000000157662b0004a1c000000000000206200085b3628000da30000000000c9a000000000000000022a80000007620003d7e0000000000000000000000000000020f812c001a7c6010000000000000000205200000069940940000007c74000e9c0000002936285000000000000000000000000005898000000000000000000000000000000000000000000000000000000000000000000000000000005e9c0000000000003778fa1f0ee4cd48c00000000000000000000000000000daf0000000000a61000000042c0000000001c6100038f156fe5d0003257c54f9800000000000000000003cfa849000000000000000000300000000000000000000000000253000000061000000005548003e8833700000000000000004abc00000000000000000000001b04000000449800308e00085eaa58001c9f00040ca507a3f798b0c0000000000106c0000000007acc0000005040000000c33000000281c000000000255d5ae791000000000000000015794ad0005a9c001494000000000000000005f40015b4000000340200002b8000001757626397d8c00000007d60000000000299bc5000000019c8000000000000000000000000000000000004840001a7e000000000000043d0000000000b0a36cb2280000000000000000000000000000069d4c9c0016ab70ab62397ca1342ce16d8ddda2c228000001c0759c80000000000000000ec2843000000000000000048f5cfff3286038800000000000000000b5671c00000000000000001c1a0000000000000000bb37068001288000188c00000064cd81800076400000020a5c1c000000302385400000000000007402de9c5ac2e00000000000000003096c77a6700001cc00125685300000000000000000000000000000157400000034d40000000002ad400000000032cb20c00000000000000000000002586000db77ad30720000000000001f12000000033410d32700000012370000000000000faf99bd0140000007a11118000000090715905a00072040006920000000514000a108000000000000000394746c0000000000235d3859dd23400000049a4000000dc3d1b481e00030b4a3c0000000007db644800000000008440001032103352321850130100140010000505024104112135605140 else 0x28b00000000001950000000000000000013180018d40000000000000000250800000000000061344c4000e32625c0000000000000001e8b000000085e00000041d4001a18000705d51c000000000000000000034e000000071b0000000612a52000030c000a1d00000000000000d9c001053000191000104fbbbf2340000000000000001a7b38a80034d6051ad88000000000000000000000000000000014559510000000000000000213c00000064d8000000348a62c001a9000042080072270000000000000a1f1171f580004347c6c00000022400000000000000000000d230006ac7e2c81e00000000000000000000000000000000290c0000007814000000000000000000000000000016b9c4e8000000000000000)
def g246D8 (j : Nat) : Nat := 0x168c42878300820938300d3080314c0111ac48c01199308042cc2010813246010cd4cc0114a9980221a6110040cc4011cd9802219cd18022b4620f7ba3bfdaaa12c86bcd9eb0461c8b0581a05401fd53ff297f54bfc85fd42fe217f8cbfa65fd50ffa07f503fa61ff20fe907f443bca7dd53
def g246H8 (j : Nat) : Nat := 0x1e66000668000000000000000262000000000000001e4c00000000000000000000000000041a000000ec638e000000000000aca00000000000000000000052800000000063800000000000163a878000f34000001594000e40115e180000d7c420000000000000000000000000010440000000c259a0000006a8000001e8744efbea9360e000c2e00049c00000000000000079fbc60000d4000000000000000000000001a6a000000000000001880001108001b100008719a6a8cc008c92cea540003200018aa000000000001c7f93c05875f7a20000019040000000000000000000012ad9900000014316480000000000000000000000000720016460050a0000000000000cbe000001984a9885e000c946069c00000012bc00000000154b6b0000583a080019613418b7426051a0b8ba68a000001802000000000000000000c12000000000000000000000000000000000000000000000a960000000014d2e524a46d12ae00005d22200000000000061000000000000103c000000000000000000fc2000001d9c0000000000000013c538a0000000000012900240000000000000000000000003b40005130cc000000000000001c1c000000000001b62000000000000000000c60001d38ab54c4000000d3a00000000000000000000113ff1e0000010d928e000000000000000e1600000169e001aa200000103450fdac0000004a723f0836db66cb86000000001f9362cedc00000019800194805a00004a000cc0000000001828000001f70000000000000000000000000000a7c000001a75cb8000000000000000000000000000000e8400000173200000140c000001fd2000000000000001db600000000000000000000000000145600000000000000000003742a00000000000162000000066e000000000232000000000000000000000001344000000001a7600000000000101400000001e0000004880000000000016b327ae6449a004c8680400314312e01072
def g246D9 (j : Nat) : Nat := 0xdc9313f
def g246H9 (j : Nat) : Nat := 0x14700000084002cea50000000000000000000000003000000000000000000e075400000001c8f364b81800006d000000a68019480151800000014800000000000000049f4408e97800000012080000001620000000000001c28dc4580000000007180000044800000000075a000000000040a10
def g246L : Nat → Packing
  | 5 => (39,4,4,0,0,7,0,g246D5)
  | 6 => (198,3,4,0,0,10,0,g246D6)
  | 7 => (111,2,4,0,0,12,0,g246D7)
  | 8 => (17,1,4,0,0,9,0,g246D8)
  | 9 => (1,0,4,0,0,0,0,g246D9)
  | _ => emptyPacking
def g246I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 10 207 3 11 6 1 g246H6
  | 7 => lookupWord 52 787 4 13 8 1 g246H7
  | 8 => lookupWord 31 478 3 12 7 1 g246H8
  | 9 => lookupWord 7 91 3 10 5 1 g246H9
  | _ => fun _ => none
def g246 : Forest := ⟨246,9,fun i => g246Y[i]?.getD (0,0),g246C,g246A,g246L,g246I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246P5_0 : block g246 5 0 39=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g246B5 : block g246 5 0 39=true := g246P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246P6_0 : block g246 6 0 12=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246P6_12 : block g246 6 12 48=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246P6_60 : block g246 6 60 48=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246P6_108 : block g246 6 108 48=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246P6_156 : block g246 6 156 42=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g246B6 : block g246 6 0 198=true := (@block_merge g246 6 0 60 138 (@block_merge g246 6 0 12 48 g246P6_0 g246P6_12) (@block_merge g246 6 60 48 90 g246P6_60 (@block_merge g246 6 108 48 42 g246P6_108 g246P6_156)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246P7_0 : block g246 7 0 7=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246P7_7 : block g246 7 7 48=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246P7_55 : block g246 7 55 13=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
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
theorem g246B7 : block g246 7 0 111=true := (@block_merge g246 7 0 55 56 (@block_merge g246 7 0 7 48 g246P7_0 g246P7_7) (@block_merge g246 7 55 13 43 g246P7_55 g246P7_68))
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
theorem g246G : graphValid g246 (boundsBefore K219) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low246 : Lower true (varsX 246) (graphGoal 246) 10 := lower_forest (g:=g246) (i:=0) (hints:=303105344) (before_sound K219 V219) g246G g246T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K246 := extendKnown K219 10 [(246,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V246 : Known true K246 := extend_ok (m:=246) V219 low246 (by decide +kernel)
def g127Y : Array (Bits × Bits) := #[(0xfffffffffffffff20043e41446067fc011510b,0xfffffffffffffff00042201440061540014009),(0x28820918794b8ce82b7c84,0xaa928118594a8ce8037480),(0x430fc021f818c0f100dc790,0x30c4021c81ac4f1009c380),(0xfffffffffffffff83f0013e001f00fc6402283,0x3800032001c00a86000082),(0x1c0001c0001fff03b8cc364,0x40001c41023160108c8324),(0xe00001ffffe000001f68898,0xf44211cc326010001f40810),(0xfffffe0000000001d833c60,0xf8739c08234000029023c40),(0x0,0x0),(0x0,0x0)]
def g127C : List ColumnInfo := [(38,0,89,0,7),(8,0,119,0,9),(1,0,126,0,9),(86,0,41,0,4),(66,0,61,0,7),(20,0,107,0,7)]
def g127A : List (List Nat) := [[]]
def g127D9 (j : Nat) : Nat := 0x8a9313fd64
def g127D10 (j : Nat) : Nat := 0xb1102ff
def g127H10 (j : Nat) : Nat := 0x3c000000
def g127L : Nat → Packing
  | 9 => (1,1,3,0,0,0,0,g127D9)
  | 10 => (1,0,3,0,0,0,0,g127D10)
  | _ => emptyPacking
def g127I : Nat → Nat → Option (Nat × Nat)
  | 10 => lookupWord 1 8 0 6 1 1 g127H10
  | _ => fun _ => none
def g127 : Forest := ⟨127,10,fun i => g127Y[i]?.getD (0,0),g127C,g127A,g127L,g127I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P9_0 : block g127 9 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B9 : block g127 9 0 1=true := g127P9_0
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
  · exact g127B9
  · exact g127B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127G : graphValid g127 (boundsBefore K246) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low127 : Lower true (varsX 127) (graphGoal 127) 11 := lower_forest (g:=g127) (i:=0) (hints:=1347) (before_sound K246 V246) g127G g127T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K127 := extendKnown K246 11 [(127,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V127 : Known true K127 := extend_ok (m:=127) V246 low127 (by decide +kernel)
def g247Y : Array (Bits × Bits) := #[(0xffffffc00809a410f20bd98280240b803a3021,0x880101200580080240980123000),(0xc004e40000f0c3e3159fd940a233c8c,0x24a010453043819012d0402223884),(0xffffffd03070081f03f02000800148349674c3,0xffffffc0105000511310310080010814963441),(0x0,0x0),(0xffffffe2478077e00c003fc6d78a0141c64d51,0xffffffe4118000e00020838240900015844451),(0x3c780078000fffc0731cf2d22951c374,0x3fed257e888ceb82621ad2d22941c330),(0x3f80007ffff000007c22476087659aa4,0x18c200010ee441005d220854026188a4),(0x3fffff8000000000783c022c5288a31a,0x32c257e00088a04201c02a04008030a),(0x0,0x0)]
def g247C : List ColumnInfo := [(194,0,53,0,4),(51,0,196,0,4),(128,0,119,0,9),(38,0,209,0,7),(148,0,99,0,4),(102,0,145,0,4),(7,32,208,0,4),(166,0,81,0,4),(1,0,246,0,10),(101,0,146,0,4),(145,0,102,0,4),(54,0,193,0,4),(193,0,54,0,4),(129,0,118,0,7)]
def g247A : List (List Nat) := [[],[33,100]]
def g247D5 (j : Nat) : Nat := 0x896f62d4f0fbb2c8a9c4bbb06a787dd96454e85b5c90eb2302a9ac388dea39659153d4551
def g247D6 (j : Nat) : Nat := (if j<1 then 0x43c7361d9220d6550f38d846488359543ce56119120d6550f1d9876408359543ce66119020d6550f07f96e157558d43c1fe1b955d95350e6b5a3e457559161c4fe15949d5735872b595593815cd61e35dd56360653586ab5a1e1d6454d61e2d6878759153586ab7a161d6454d61a2faa08759153586e35a19d56454d61b8de8575591535878b787e456454d61b956849558d53586e59a02556354d61b956867558d53586e57a15d56354d6187daa487605535878b4875918154d61e3521d63605535878b587e456414d61ea9e856460853587ab3a15918014d61c2fe5f8659173d470bd97e19645cf51f07595745cd63d468bfa661d6494f51a8fe998559253d4785d766156394f51e1761d6558e53d470bf97e196454f51c2f65f8659153d47c1d655d16354f51c1fe5f9661953d4693fa76197454f51c8fe5f8659153d4723d97e196454f51f076917658d53d47c1d765d16354f51a8fe9985592735478b7a1651861cd51e2d61b91590735479b3a1591801cd51d175d9959cd63546a3fa66156494d51e175d98558e535478d57658d8194d51e955956360653547a556558f8154d51e8de878659153547a3786e456454d51b95e857658d53547c57a15d96354d51c9d65b86e0553547a37865938154d51e95e1963e05535474b5975928358551d8d65564a0d61547637955918358551d8d655649cd61546e55a3a556358551b956967358d61547635955925358551d956556394d615472b7985915358551e8de616454d61547a34985915358551e95e616354d61547a549858d5358551cade596460f51547a556560d63d4551c9de598654f51546b37a859153d4551d8de596454f51547a558658d53d455192fe99979d564cc64bfa664e7559331b2de9975e0564cc6c5da39d56558f31b1769e7559563cc68bfa661d64d4f31e1761d6558f53cc713f85652855d93185fea585215764c693fa55d9849d531c1fe5b9561d654c70f796e4587595319a7e99939d5644c64bfa664e7559131b1768e75595634c6e4da22156558d31b9568485595634c6e59a02156558d31f15e8575595634c68bfa661d64d4d31e1761d6558f534c7a556558d81d4d31e9559563e05534c6cb5a7a156458531ba568e85591614c6e95a39d56458531e2dea175591614c765795a556358531ba56909558d614c6ec5a22556358531bb46809558d614c6ad5a8a156358531b3569e8558d614c6e95a4a1563585319b56a67558d614c6e95a49d56358531e35ea17558d614c74b5975935358531cb566163d4d614c74d59758f5358531cade616454d614c72d79858d5358531d9565963d4d514c7a558658f5354531d8de596454d514c76579658d5354531e956196354d514c6ab7a661564cc531ab5e998558f314c7a558559563cc531e2c619646057014f9a164609815c053 else 0x38201040a0824100020404005024200824230453045303045304545454530303030303030303030303030303030453030303030303030303030303045303030813030303030303030303030303063303030303030303030303072303030303030306354303030303030303030303030303030303030303636303630303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303045304530304530303030304530303030303030303030453030303030303030363030301800c67e63535cc7359307fa6e61751d563c1fe63965d47558f877a65d5811d563a5de91756047558f2d59664d811d563e1ee99756007558e97ba45d5801d563d936959220d6558ec6da21d5655d163b1d684755957458ec79a01d5655d16387daa475e057458e9e5a21d7815d163a7c68075e057458e4bda1e597559253b17e85755956394f85d755978258e53aa7e99875935394f85f86e17835d95383f6a787dd96454e1bda9e1f745915386faa4875d16454e1bfa961c875915392f6a787dd96454f61f95e4f7659153b2de8598dd96454ecbba0663765915398f69a95e0d6454e735a1a578359153e27ddb83a0d6454f4af7664a8359153d0fddb9560d6454f43f762558359153d2dddb9160d6454f655a66448558d53d95dd9912156354f65b766408558d53b87690855956354ee4da22156558d53b95684855956354ee59a02156558d53b87690985956354eb55a12158458d53ad6680856116354f65565e458458d53d8759594e096354fa1d656538258d53c9765986dce5354ecb5a1e1964dc553b356878658f7154ecb7a164d845d853e2de85846057614f4b576e458359053c2fa61945d95314f0bf97e196454c53c2f65f865915314e8bea85d96454c53f075957458d5314f49e986517654c53f07695945d95314ec5ea85d96554c53e27e9b875915314f89f87e196454c53b27aa1765915314fc1d766556454c53e2de61865917114eda7a2655645c453a6dea1935917114f4b796591535c453f155956354d7114fc3796591535c453f4568d6454d7114fc579658d535c453e2ee61865917014edb3a164d645c053d2ee596454d7014fc596558d535c053f16e596554d7014fc9b96591535c053f466956454d7014f9b1a8591815c053877ea58720d6590f1cd876488359643d335d99220d6590f54d756488359643d355d99120d6590f1d9876408359643d365d99020d6590f559756408359643b27e8d955d96490f29f86e4d6454e4397369f935957290e5cfa3661655ca43e1b619855957290f4af96591535ca43f135956354d7290e95fa565f8359543877ea58720d6550e39fa961083595)
def g247H6 (j : Nat) : Nat := 0xe003100019c880006c000
def g247D7 (j : Nat) : Nat := (if j<4 then (if j<2 then (if j<1 then 0x56458531f5b3aac8b0a63eb575591614c75ef0ab1ac298f3d5d56358531f6bcaac6b0a63ed69558d614c7dab2ab1ac298fb52556358531f6b42ac6b0a63ed58558d614c7daceab1ac298fb55d563585319facc6a6b0a635f597d4d614c7d6ac9a9ac298fb558f53585319fbcc2a6b0a63eb56454d614c7daac6a9ac298ddde557654531cfa4c2eca8a63d77955d9514c7ae92abb2a298ddd64e6554531bbbc9acaa8a63af58658d514c7ceacab1aa298fb56196354531fab4aac6a8a63f559558d514c7daacab1aa298ddd65b5354531dbac36a6a8a63d7576d4d514c7e6ac9a9aa298fd558f5354531bbbcb2a6a8a637759654d514c76ef0ca9aa298edd6195354531ebabb2a6a8a63f356454d514c7eaac6a9aa298cfde5985cc5319facc4cb98a63b7585997314c67eb30b2e6298ebd61965cc531dbac2acb98a63bb585593314c77ab0ab1e6298fb559563cc53195ecb50bb9ac93b591a177359237f30b98e6b245fe61751d563cbabab023aac7979756007558ed9b2441acab1db56448359563b6cc8106b2ac74bf965d56494f17b0cb24e729e6e591809ce53e2ebaacab1ca795f85e0d7654e97b23bb2c8a9e1fddb8558d539bac890ab1aa7379902156354eeab2242ac6a9dd66408558d53d2eb2f04b1aa7c5d6558f7154e97b29c0aec29e2f613815d853c5ec2302bb0a78bd865da7414f17f0ebb2c829e2f6617659053a5fc8aecb20a7c9d945da5314f93aecb24a629f276517654c53e2ebb2caa98a799f875915314f93aecb22a629f2d651769c453e5abb2c9388a7cb5945d97114eb6b2d3a2e229d6de5d645c453adacbac8b88a7cb5765917114fb4ac9392e229f69591725c453e5ac32c8b88a7d3564d4d7114fa6ac8a9ae229f5558d535c453e5cca2ecb80a75b9969d17014eb772eb22e029d6e65d645c053e5cbb2c8b80a7db1649c57014fb62c8b8ae029f2e619645c053eccb24a6b80a7d596554d7014fb32c8a9ae029f6c592815c053cf8c3302b80a7db1646057014e37b2fc1ac921dad6467559161b5bc8aeab22c3ab5646067358756ac9c0ae6b0ead59181d4d61d5ab230329ac3ad5636065358717f0eb22a6b0e2f61d6414d61d56b230429ac3ab56460453587572c8c00a6b0e2fe19645cf51e2eb2ae6b1ea3a3f8659153d478baecb1aa7a8e2f651861cd51c5ec32c839aa39ad6460873547372c8c00e6a8e8fe196454d51e2ebb2c6a9aa3cb564dcd61547c6ac9a9ac2a8f8d5915358551f2ab1aa6b0aa33b7985935154717b28c30eb98d2fe597559331a5ecb0eab26635ad921d564cc6b73203aac998f175d56558f31a5fcb2eab22634bd961d5644c78baeab2ac698f2ddd56458531e5abaac8b0a63ad78558d614c79aeeab1ac298f355d56358531cda43ac8a8a63ad58658d514c7caacab1aa298e78609815c053 else 0x2a8c7fe59879d731c7ec32ed3ae631ff9660e75cc71ff0cbb2eb98d5f6568759731c7fcb30eb2e631fd98dd565cc69fb2dbaacb98d5f65e7559731e3ebb4eab2e634ff965d565cc78faecbaacb98f1fe5975597318fecbf06b2e635bd979d564cc6b7b273aac998dafe597559331e5fcb2eab2663db775e0564cc7b6aebc0ac998d3f65a7558f31aeec9ceab1e631fd985d563cc69ff2cbaac798f1f9d56558f31e3ebaacab1e635dd97a1563cc6bbb2f3aac798db765a7558f31b6fcb2eab1e63cdf965d563cc79beeab2ac798f979d56558f31e6ebaacab1e63e5d7559563cc63ff2cc3ea798c7f66176d4f31c7ec32eda9e6397d8759753cc78faecb2ea798e6f61d64d4f31ceec3ac7a9e63add8658f53cc7cbacab1ea798e3fe197654f31e3ebb2caa9e63abf8659153cc75bf0cb1aa798f975956354f31cbfc2d0abb2635bd94a15764c6bbb2742aec98d7d646855d931afbc8b0abb26397d85215764c6beb2bc0aec98e3f619769d531abfcaaed3aa639bd76612754c67bf2cc1cea98e775d9839d531debc8b073aa631ff9660e754c71ff0cbb2ea98d5fe55865d531afbc8b0cbaa635f596e05754c73ef22c3cca98e5fe617599531ebbc8aeb32a633f79160e654c67bb27c3aca98c7f64f8759531abecad0eb2a6357f9561d654c71ff2cc3aca98c7fe558759531cbfcab0eb2a639f79161d654c69fb2dbaaca98dd764e7559531abec9ceab2a634ff965d5654c78ff2cbaaca98f5de4575595319fac8f06b2a6379d939d5644c6b7b273aac898dafe597559131e5fcb2eab2263db7915d5644c7baf22bacc698c7f6627558d31a7ecb4eab1a635bd949d5634c6bbb273aac698d3fe597558d31e3f3aacab1a63c7d75595634c67eb2bc0ac698d7765e8558d31dafc2d0ab1a637d591a15634c6faf22c2ac698de76508558d31be6c910ab1a637d591215634c6fb32042ac698cf76627558d31b6ecb4eab1a6379d949d5634c6dbf2cbaac698f37e597558d31eebc8aeab1a63e5f85595634c7cb90ab2ac698f37dd56558d31f2f3aacab1a63cdd75595634c7cbaeab2ac698fb56456558d31beacaf02b1a63ed565e05634c63ff2cc3ea698e7de4587d4d31abfcaaeda9a6397d87597534c737b0eb26a698e7761d63d4d31d6ec32c7a9a6375f9558f534c7cbacab1ea698e7d5d981d4d31dbab2b03a9a63bb564607534c77aac6c0ea698cfde458654d318fecc2eca9a6357f955d9534c6eeb2332aa698eafe196454d31d6fc32c6a9a63e5d6558d534c67eb2dc0aa698edd9978154d31dbab2f02a9a63bb564e05534c77aac7c0aa698cfd6628558531afacbd0ab0a636f596a15614c6f6b2942ac298df564e8558531b7acb4eab0a637b5949d5614c6fab273aac298dbde597558531cfbcc2eab0a63cf7965d5614c7d6d0ab22c298fad61) else (if j<3 then 0x3ae931aa7a8f375d96354f51f2eb2ac6a9ea3d9d7458d53d46aff2ec32a7a8cdfe5d8654f51cbfcbb0ca9ea3a7f9661953d46afd31bb2a7a8e9fe197654f51e3fc32eca9ea3d3d945d953d4767f0cba2a7a8ecf6197454f51e9ebb2e8a9ea373f9759153d46e7b2eb22a7a8f8fe196454f51f8eba4c6a9ea3a7f8658d53d478faecb1aa7a8f97e196354f51f2ebb2c6a9ea3f1d7458d53d46afb2b41aeca8d7d646835d951abfcab06bb2a35f79160d76546beb27c0aeca8edde4583995519fac9f02b2aa357d97a0d65546eeb2341acaa8ddde458359551bbac9f02b2aa3b7583e05655471fb0cbb4e6a8cdfe59859cd51cbebb30b39aa3b7791616735466fb30b2ce6a8e9f619659cd51d9ec2ac939aa38ff865d9735474ff0cb2ae6a8eafe19645cd51edbc8ac839aa39f79161e635467ef22c2cc6a8edde458598d519becaf0eb1aa31fd95e1d63546bbb2743ac6a8cdfe558758d51e7bc8aecb1aa33f591e1563546ebb2742ac6a8dbde456558d51f3bc8acab1aa34fd96dcd635478facbb9ac6a8f375da7358d51baecace6b1aa3e5d659cd635479baecb9ac6a8f975957358d51dbb42b02b1aa3b758560563547ceacac0ac6a8fcde4564d4d51d3ec32c7a9aa3c7d7658f535471fb0cbb4a6a8cdfe598594d51cbebb30b29aa3b7791616535466fb30b2ca6a8e9f6196594d51d9ec2ac929aa3cdd7658e535476bb0ab1ca6a8f975956394d51cfabb30329aa3b75656065354776ac8c0ca6a8ef558d8194d519fbc8b0ca9aa3a7f865955354757f0cb22a6a8f375d96354d51f2eb2ac6a9aa33f596e05535476eacbc0aa6a8eed5938154d51deb31f02a9aa3bd563e05535476ef23c32a6a8ddde458654d51d3fcb30ca9aa3b779161953546eef22bb2a6a8f5de457654d51f1fc32c8a9aa3f3791591535474ff0cb1aa6a8f1f5d96354d51f2fc32c6a9aa3e5d7658d53547eab22b1aa6a8ddd65b8154d51dbbc3702a9aa3b7586e0553547e6ac9c0aa6a8fd598f8154d51faab1f02a9aa33f598a0d61546beb2f41ac2a8dbd65a8358551bbacad06b0aa3eb564a0d61546eef2ac1ac2a8fad5918358551b7acb4e6b0aa3775959cd61547d6ac939ac2a8dbde597358551f5ab22e6b0aa3e769558d61547ceb2ab1ac2a8f3ddcd6358551f6b39ac6b0aa3ed57358d61547ceac7a9ac2a8cfd6625358551b7acb4a6b0aa37759594d61547d6ac929ac2a8fb558e53585519fbcc2a6b0aa3eb56454d61547daac6a9ac2a8edde615358551dba4c2a6b0aa3b778354d61547ceac6a9ac2a8cfde5983d4551dbab2b07a8aa3bb56460f515467eb3131ea2a8ddd65663d4551deac1cc7a8aa33f59858f515475eb0cb1ea2a8f9d59563d4551deac1ac7a8aa37779654f51546eeb2ca9ea2a8edd61953d4551f9ab22a7a8aa3f566354f51547eaac6a9ea else 0xd95350eaff2abb2a6a1d7de457654d43d5fc32c8a9a87e5d6558d5350e77f2cc2c86a1cef6626590d43d9ec2ccb21a873bd985964350f57b0cb2c86a1ecf6156590d43bcfc9acb21a873f593e0575586d7b273aac8b0e5f616759cd61adeca4eb39ac35dd939d6735871fb0cbace6b0eaf615649cd61e5f3aac939ac39f575606735869fb2d3aae6b0e5fe16755cd61adeca4eab9ac35f5919d57358757f0ab22e6b0f2f5d5645cd61f5ab2702b9ac33f595e05735874ff0b42ac6b0db764e8558d61b7ac8d0ab1ac36f79161563586d7b2842ac6b0dbb6488558d61b7ac890ab1ac36f990215635865fb313aac6b0d3f65e7558d61b5eca4eab1ac36dd939d563586deb233aac6b0dbde457558d61b7acaf02b1ac3eb791593535871fb0eb1ea6b0ebd58d81d4d61c7ec36eb29ac35dd93dd65358757b0eb24a6b0eaf6156494d61f5bc8ac929ac3add8558e535879beeab1ca6b0e7ddd58194d6197ecb70ea9ac33f591e1d535871fb2dc3aa6b0e7d6478754d6197fcb30ea9ac33f79161d535863fd3043aa6b0d7764f7554d61b3ecb4eaa9ac3775919d553586eef22baaa6b0eafe1d6454d61e5fc3ac8a9ac3abd87591535879790eb22a6b0f8f9d56454d61f1ebaac8a9ac3eb79159153586afb2bb9aa6b0e3fe1d6354d61e6fc3ac6a9ac3cdc8758d53587cbf2ab1aa6b0f972556354d61e6fbaac6a9ac3e5e7558d53587cbaeab1aa6b0fb5e456354d61cfa43b02a9ac3eb56460553587daac6c0aa6b0fade456414d61abecad06bb6a39bd84a0d76d4737b08c1aeda8d5f65e8359751abfcbb06b2ea38fd865da73d474fb0cb2ce7a8e6f619749cf51adfcbac939ea35bd9759273d471fb0cb2ce7a8e3fe19765cf51cdfc32e8b9ea3d3d655d173d46b7f2eb22e7a8d6f65d645cf51d5fc32c8b9ea3cbf8659173d4737b0eba4c7a8ecf6157498f51cdec2ae931ea3d9d745ce63d46b7b2943ac7a8d7764e8758f51c7fcb30eb1ea3cbd945d963d463fb2fc2ac7a8dd764e8558f51cdfc3ae8b1ea39bd875d163d4797aecba2c7a8f8f5957458f51cdfc2ae8b1ea3cbd655d163d479baed39ac7a8f975967358f51eceba4e6b1ea3cdd659cd63d469ff2cb9ac7a8f1f5957358f51e6ebb2e6b1ea3e5d655cd63d47b3ae8b9ac7a8f37e597358f51e6eb2ae6b1ea3a7d8658f53d478faecb1ea7a8c7fe598794f518fecc2ed29ea38fd865da53d466ff2cc2ca7a8e5f5d98594f519becc2cb29ea397d8759653d474fb0cb2ca7a8e6f6197494f51adfcbac929ea35bd9759253d4737b0eb24a7a8ecf6156494f51ceec3ac729ea3cdd7658e53d476bb0ab1ca7a8f975956394f51eceba2c729ea31ff9761953d471ff0cbb2a7a8e9fe196554f51cdfc32e8a9ea39bd865d153d47a7acaba2a7a8d6fe5d6454f51adecbac8a9ea3abf8659153d47b)) else (if j<6 then (if j<5 then 0xa75dd96e1d5314f3bf2dc3aa629e7765b8754c53cefc3f0ca98a75df976195314f3bf0ec32a629d77a617654c53e6fc32eca98a7cde985d95314f9bb30bb2a629f57e1d6554c53f2fc32caa98a7d9f875915314fd3f0cb22a629fc76556454c53edbc8ac8b88a7db5915917114fb6f2eb22e229f6d65d645c453edbcc2c8b88a7db5985917114fb6f2ab22e229f6d655645c453edbc9ac8b88a7db5935917114fb6f24b22e229f6d649645c453e7ab2ac6b88a75f79654d7114ebeb2ca9ae229f5d595535c453edab22a6b88a7dd56354d7114faef2ca9ae229f5d659535c453eddcbac8b80a7db9975917014fb7730b22e029f6e661645c053eddc9ac8b80a7db9935917014fb7722b22e029f6e645645c053e7cb2ac6b80a75fb9654d7014ebf32ca9ae029f6e591535c053eecb1aa6b80a7ddb9654d7014fbb32ca9ae029d77e4d855da43cdec2b08bb4878fd865da7590f1ff0cbb2eb21d5f6568759643af6c950eb2c878ff9661d6590f97b28bb2cb21f1f5da7559643a7fcb2eab2c87c7d765d56590f8ff2cbaacb21c7f65f8359643cef43f06b2c879dd87e0d6590f9baedc1acb21f575d783596439eecbf06b2c879dd97e0d6590f3baebc1acb21e7761c8359643e6ebb106b2c87d5d7520d6590ef9b2441acb21df56448359643becc8106b2c87cbe955d96490f97b2abb2c921e6f5d78359243a7ecb4eab1c87c7e755956390f8faeab2ac721c7fe5987d4e438fecc2eda9c878fd865db5390f2fb0eb2ea721f1f5d965d4e43cdec3ac9a9c87cbd765935390ef3f26b26a721c7fe5d8654e439efc9b0ca9c878ff865d95390f8faecb2aa721eafe196454e43e5ebb2c8a9c8779f935915390fcbacab1aa721d7b65a755ca43af7cb2eab94875ed979957290fadaeb32ae521d7be5d655ca43af6cbacab9487ced765957290fadceab2ae521f5b5d5655ca43be7c9acab94875ed96a157290ebdf2cc2ae521e7b619855ca43af6cc4cab9487d6d859957290ebdb2732ae521d7be61655ca43af6cc2cab9487ced865957290fadd0ab2ae521f5b615655ca43af7c9acab9487ced6558d7290ebdb2da9ae521f5b597535ca43ed6b26a6b94875ef9654d7290ebdb2ca9ae521f5b995535ca43eb6b2aa6b9487dad6454d7290fb9ac6a9ae521e6fe5185dd9438ffcb3073aa8757d95a1d6550eaff2ac3acaa1d7be498759543afbc8b0eb2a875fb9061d6550e9fb2dbaacaa1de724d8459543cef43f06b2a87b9d84e0d6550f3bb2fc1acaa1e77dd78359543dceca706b2a879dd8720d6550f73b0841acaa1df36488359543beac8906b2a877d99020d6550e3fb313aac6a1d3f65a7558d43cbfc2ceab1a875dd939d56350ebeb233aac6a1d3fe597558d43cbfc2aeab1a87b3f855516350eaff2abb6a6a1d7de4576d4d439efc9b0ca9a878ff865 else 0xc8b0eb22a73fb9061d6454f1ff0fbb2c8a9e3f6637659153e5eca6ecb22a79bf87dd16454f97eedba2c8a9e6f21d7459153e5fbb2e8b22a78ff76e0d6454e6fb2bc1ac8a9e6fe1e8759153b5ecb50eb22a76bf9661d6454ef6f22c3ac8a9deee418759153cdec390eb22a7cbf87dd96454f9790fbb2c8a9fa7e4f7659153b5ec8eecb22a7cbf98dd96454f97d31bb2c8a9f2f6637659153e5fc9eecb22a7cbf91dd96454f97b23bb2c8a9f2fddb8359153b9f4af06b22a773d95e0d6454eb7d2f41ac8a9f2fdda8359153dcfc1d06b22a77ad92a0d6454f97eecc1ac8a9dcfe558359153b9e4ab06b22a77b79160d6454eb7d2e41ac8a9f2fdd88359153e5fbb702b22a7cbf766056454e7bb2543cc6a9e77a1f7498d539efcc2e931aa79de875d26354e9fb23bb2c6a9e3fddb8558d53d3fbb70ab1aa737d91e156354e6fd2e42ac6a9e3fddb8458d53cbfc2ee8b1aa73bd94e096354edbd2fc32c6a9f97e577658d53b6ec8eecb1aa7e5f76e156354eebb23c2ac6a9ed7e168558d53aef4b90ab1aa779d942156354ef9b2442ac6a9df56448558d53becc810ab1aa775e972156354fcbeec42ac6a9dd76448558d53f2fc2acab1aa7e5c855956354edbf22b2ac6a9f972616558d53f2f43acab1aa7e5d65e116354eebf2ac22c6a9dd72558458d53dae42b08b1aa7e5d656116354efaf22c22c6a9f975977458d53b6fcb2e8b1aa7e5d655d16354fcbacbc12c6a9de76538258d53d6eb2f04b1aa7b9d94e096354fcbacac12c6a9f975978158d53bafcab02b1aa775c956056354fcbacac0ac6a9e3f61b7694d53d3ec32cb29aa7cbf765925354f9beecb1ca6a9f975956394d53d3ec36ed29aa775f935da5354fc7eecb24a6a9ed761b7394d53f8eb26e729aa7e5f7658e5354f1fb0dbb6e2a9ddd64665dc553e3fbb2cbb8aa7cbf765937154f9beecb1ee2a9f9759563dc553afac8f0db8aa7cbf865937154fb6f22b26e2a9f1f59563dc553e6fc32c7b8aa7cdd6558f7154f1ff0cbb2e2a9cdfa62655c553d3fc32cab8aa7c7f765957154f57f0cb22e2a9f2fdd9645c553d6fc32c6b8aa7cdf7658d7154fcbacab1ae2a9f2fe5d845d853e5fc9b08bb0a7cbd936117614f97f22c22ec29f2f645845d853cdecbb0d3a0a79bf9761d6414f97f0ebb2c829f2f6617659053adecbf06b20a7cbd76e0d6414eb7f2ec1ac829f2f5d98359053bdbc8b06b20a7cbd76e056414f97aecc0ac829d3f65a7558c53c7fc3acab18a7cbd655d16314f9bacb39ac629c7f65b8754c538ffcbb0ca98a71fe985d95314f1ff0cbb2a629e3fa617654c53c7ecc2eca98a7cbd945d95314f37f0cba2a629e6f6197454c53adfcbac8a98a75bd975915314f37f0eb22a629eafe196454c53e5ebb2c8a98a79df8758d5314f9baecb1aa629f975956354c53eceba2c6a98) else (if j<7 then 0xa0c0000000000e40e40000000e40006500009d099400000000000000000000095800091c91c2f88e08a487883c8107e47b877c7407045606506c868c6505606045d858c2f82f82f82f85605144c847c4303f43c80e43240e439c0e43503242f829c2601f41a816c1100e408802c0019bd85dce7359357f2cc28e6b266f615731cd64ecfa9ae639ac93f7916137558ebef22c26eab1d5f663759d563e3ec36eb3aac757d91dd67558f2feeac24eab1eb7619839d563eafbab073aac7adf9660e7558e7bf24c1ceab1cf7e45839d563d6fc3706baac73dd92e0d7558e3ff30ba8eab1e5fe61751d563e3fcb2ea3aac757f945d47558f37aeac20eab1e7b5d5821d563cbebab023aac7af5966047558f3eaeac08eab1ef564d811d563cfcbab003aac76bd9421d6558fcbeebc1acab1db764b8359563b3ecad06b2ac7adf83a0d6558e9fd2e41acab1daf6508359563b76c9106b2ac76f59120d6558edf32041acab1db7a5c8359563b6ec9106b2ac73dd93a177458e3fb313aee8b1d77e4d75dd163cbfc2ceaba2c797c855d57458ebbf26baae8b1c7fa60755d163af6c90eaba2c75f5911d57458ebf3203aae8b1e9fe15655d163d3e42acaba2c7c7c755957458f3eeebc0ae8b1e7d9d7815d163cfabaf02ba2c79f475e057458f5eacbc0ae8b1db764e7598d63b6fc9aeb31ac73dd93a177258e3fb313aee4b1d7764e75dc963cdf3ab09b92c79bd756137258f57acac26e4b1d3f65a85dc963aeec9d0bb92c79be856137258f37b0ac26e4b1f2f59584dc963aeec9ceab92c73dd93a177158e3fb313aee2b1e5fe16755c563cbe42aeab8ac71fe981d57158eb7b283aae2b1d7b648755c563afcc80eab8ac7a7f855957158f4f90ab2ae2b1d7de45845da538fec8f0cbaca71fd96e057594f1ff2cc3acb29c7fe458759653a7fc92ecb2ca71fd97e116594e7bb2fc1acb29cf764b83596538fecbf04b2ca71fd97e056594f1faedc0acb29cef6538159653aefc9acaba4a73dd93e156494e9ff2cbaac929dede458759253bcec9f0ab24a7b3f85a156494ef6b2342ac929de7e4d8559253bd7c930ab24a7cbf965d56494eb7f22baac929dede458359253a7fcb2eab1ca7cdf965d56394ebbf24baac729d77e457558e53e6ebaacab1ca76df915956394ebbf2ec22c729e77e1d8458e53bebc8b08b1ca79dd75e096394f5bacbc12c729e3f61976d4e53d6ec32c7a9ca73df9661f5394e7bb30bb6a729e7761d76d4e53d6ec32eda9ca7b9d875935394fe3f2ab26a729f6be49645ca53e6eb2ac6b94a7cdd6558d7194f6bf0bc1eeca9ed7e17835d953c7fc3708bb2a75df936117654ebef22c22eca9d7ee41845d9538fec9706bb2a7cdf86e0d7654fabf0bc1aeca9e77e13835d953aeec9706bb2a757f956057654f1fb0dbb6e8a9e3fe19765d1539fb else (if j<8 then 0xc90ed3c8d00d1ce4cd54d54d54d1cd54e4cd54d54d00d1cd1cd1ce4cd1cd1cd1cd1cd1cd1cd1cd1cd00d1cd00d1cd00e4cd70d71030d1cd1cd54d1cd1cd1cd1cd1cd1cd1cd5503138d360e4d030d1cd1cd1cd1cd1ce4cd54d1cd54d1cd1cd1c878d1cd1cd1cd1ce4cd54d1cd54d1cd00d1cd1cd1cd1cd1cd1ce4ce4ce4cd70d1cd54d54d1cd1cd1cd54d1cd1d334e4cd1d318d1cd00e68e68e68d70d54d1cd54d1cd54e4cd1cd1cd1ce4ce4cd54d1ce4ce68d1cd1cd1ce4cd1cd01088d1cd54d1cd1cd1cd70d54e4cd70d70d1cd70d70cd4d70e4cd1cd1cd1cd1cd70d54d70da8d70d54d70d54d1cd1cd70d70878d54d1cd1cd1cd00d70878d1cd1cd1cd54d54d54d54d54d54d1cd54d70d1cd1cd1d2ecd1d2c0d70d71294d54d54d0122cd00e68d1cd1cd70d00d1d25922c878d1cd54d1cd1cd70d54d1cd1cd70d54d54d70d1cd1cd70d70d1cd70d1cd1cd1cd1cd1cd54d70d70d1cd1cd54d1cd70d1cd1cd70d70d1cd1cd70d54d1d2011e4d70d1d200d1cd70d1cd1cd54d1cd1cd1cd1cd1cd1cd70d1cd70d1cd1cd1cd1cd1cd1cd1cd54d70d1cd1cd70d70d70d1cd1d2011e4d70d1cd1cd70d70d70d1cd710a4d1cd1d0a4d1cd1cd1cd1cd00d00e691e4d1cd54d54d70d70d1cd1cd1cd70d1cd1cd71170d54d1cd70d1cd54d70d54d70d70d1cd54d54d54d1cd54d1cd54d54d70d54d1cd1d1b8d54d70d70d1cd70d70d70d70d010ed0a4d70d70d54d1cd70d1cd54d70d54d70d1cd70d70d1cd54d1cd54d71170d7118cd1cd1cd54d70d1cd1cd1cd70d1d0a50a5171154d1d030d00d70d28d1cd1cd1cd1cd1cd1cd70d70d1cd1cda8d1d118d1cd1cd1cd1d004d1d0ecd1cd1d004d1cd70d1cd1cd70d1cd710c1088d1cd1cd1cd1cd1cd70d70d1ce68d70d1cd71088d710890890a4d1ce69088d1cd54d1cd00d54d00d1cd54d70d70d5505cd1cd54d70d70d1cd70d54d1cd54d70d1cd00d71030d1cd1cd1cd1cd00d1cd1cd1cd00d1cd54d54d70d70d70d1cd1cd1cd01030d1cd1cd00d1cd70d54d54d54d1cd1cd70d1cd70d1cd70d1cd1cd54d54d54d1cd54d70d1cd54d54d1cd54d54d70d1cd70d70d54d1cd1cd54d70d1cd54d54d70d1cd70d54d70d1cd54d1cd70d54d1ce4cd1cd54d1cd1cd1cd54d71004d70d54d1cd54d1ce68d1cd00fe8d1cd1cd707e4da8d1cd00d1cd54d1cd70d70d70d1cd1cd1cd70d1cd54d1cd54d1cd54d00d1cd1cfbcd1cd1cd1cd54d1cd70d70d54f90d1cd54f90d1cd70d70d70f54da8878f18d00e4cd00e4ceecec0e68da8e4ce84d70d70e68e4cd70e10dd4d1cd1cd1cd1cd1cd1cd00d00da8d1cd00d8cd1cd70d70d70d1cd1cd54d00d00d00d00d28d1cd1cd1cd1cd1cd1cd1cd1cd003c839ccd4b54b54b54c98c98c98c6c000000c20c04bd8bacb80b80b54b54b18adcab0a746500000000000e4000a4891c91c39c else 0x18408100838306080e10582240a16902a62413c2984a60828005260a1498385260bc3984e608001d9808386a408082a907660e159820424081499905a608903a6020064259025b46111020007d1c610482e40820005460a441828204c60213183460011100040c0e10091000602441718005c60b1800401c61518246082038006000812180040a0e182a4081718204020014903c6021000304000c02183800086000e1008384000324180820e0a1808387860e02183800464080020c080820400202080c1000206060ff010200497c08140fc298408141028504001415982fc07f00fa6180008408000218204840a0818180058506000214180008486080a181b9048086e40212183830401f00e18386040e0210503840ff00a1918380874600021800082860e0a021800280860e01f1c6251fc040a03c7f027c5185c60201f020283fc0008000df00a203007c21880801f0183848400121497c027189f18610280840201c7f1242c1838087250602000ff0300827c03898600021806180fc490a08021618380807c0b86020801f02808484e4cd70d00d1cd1cd1cd1cd1cd1cd1cd1cd1cd1cd1cd1cd70d1cd00d70d70d1cd1cd00d1cd70d1cd70d00d70d70e4d8ecd1cd70d713c93c93c8d01118d70d1cd1cd1cd1ce4cd70d70d70d70e4ce4cda8d1cd1cd1d8b0e68d1cd1cd54d1cd1cd1cd1cd00d1cd1cd54d1cd00d54d54d54d1cd00d54d1cd1cd1cd71884d1cd1cd1d3c8d1cd1cd1cd1cd1cd54d1cd1cd1cd1cd1ce4cd1cd1cd1cd1cd1cd1cd70d70d1cd00d00d1cd1cd70d1cd1ce68d1cd1cd1cd54d1d3f4d70d00d1cd1cd1d868d70d1cd70d70d1cd54d1cd1cd1cd1cd1cd1cd1cd54d54d54d1cd1d528e4cd1d0a583cd1ce4d528d557ad0a5529821820d1cd1ce4d5297f57ad7ad7c8d017acd1cd1cd70e4d781754e4ce4d728d54d1ce4cd1cd1d70ce4cd1cd1cd1ce68d1cd1cd1cd1cd1cd1cd1cd1d529528e68d00e68d1cd00d70d013c90ecd00d1cd28d016e15296a53c8d00e68e68e69668e4d64ce696115e4e4cd70d1d5b8d00e68d28ec0d0158cd1d3c8d00d00d1d528d70d1cd00d00d1cd1d560d1ce68d54d70d55544d1d544d54d1cd70d71528d70e68d1d4dd0a4d00e690a50a50a50a4e4d0a4d54d00e68e688790a4e4cd54d70d70d70d1cd714c0d8d3c8d1d3c8d1cd1cd70d70d714953c8d0145942cd70d70d713c8d1cd70d00d713c93c8d00d70d1cd70d1d0a50a50a50a50a50a50a4d710a4d00e690a50a4d70d00d1cd70d713c90ecd710a50a5411410d00e690a50a4d713f4d1d3))))
def g247H7 (j : Nat) : Nat := (if j<1 then 0x72290002a9c82c000b57937c00000071a80026a24b5000000011c0000002104000000000482c00000000000000000007170000000000000000000004e000000000000002f80028c2000000000000000082a81880000000000000000000000154800000000000000000d900002b800059750a7a7c0000000000003d3caa50002e040000005080000000000000000000000000000000014a30000000001e6d0000000000000a1da233880000718b96c000000000000000000000000000000000000000000000a2c8000000aaca2480000000006d200034880000005b900002560000000000000aebe2fd106000f180000000000000000043c0005648000000e42a02c1c49120000002228000c3a00000021ca0000000000000000f000000d388bd00061cc0000000000000000000000591c16200000000000000006060000000000000000000000073a000000000000000000000000000000000000000000000147f00010940000000000000000000000000000000000000000000000002810000123b1300009ac0000006132e4800000046fac2bc2a00041800000000000a480000000000000000000000000352b99f54400000000000000000000000f3a80000000009118000000000000000000000000000033ac000c650000001645761800000000000059775c5fdc0000000000000000687252e2ccccf689cb2b2cb0000003468cb300075fc000000000331c000000023000000000016030080000000000000d60000000182800000000019dc3be000d7300000000000000c78000000f0d00000b1aad06372e4001417d6aca64000000e0e800000140743e2e000004bc0003b351c0000f3b6d8c001a86f2bdb440000000002210dba0000000000001e1900000000cc00000066800000000000000000000000000000005113ed1e80000000000000000000000000000044f0000000000000000000000103f00000018f200000000027b18e70003a4253168f0000000000ea80000002458ed82d30002cd9e5e15c506c0000000000001f440000000002d0500de120000000000000000000000000000019020000000003f540000000002c67e3883f00000000009df800000000000000000000006376314001236a2e40e400089b4e000008242a281400000000000000b38000000000613400000000000000004651378000001287000000256c0000000000000000b21e0fad160000ee8000000000000000000124b00000000017de0001acbc060000004a140014be00000000012e100000000005abda5731000000000000021bc0000000000000000c17800000000000031c00016630000000001dcd00000000000006500001aea00000058ac001067000000000000010c00000000003013000401010220601341225001000021032a25240222130141237 else 0x36b8000000000000794800101101ef1a80016a9c0480018260000000003f0c000000508000000073200000000000000000000000000000000000010ff23400000000000005a0208e67e00400157e00001e000147b0003b6800000000000000004b4b499a74000e94853170792d83c00000005b70c100000000000000000000c0cc9100000000000000000001844000000092000000000000000016a4000000000100fc075684000cb74610000000000000000000000000058c80000000000000304000b391884000000340000345b44a00079680017c79698e1000000000000000000000000000000ed20000003d740000002aa8000e9a450800000000043580000000000000002ad390100000000000000000000000869e283e0d9c60000005614000000b8ff658000ec8d6a0003d7600000000000000000000002156000000000000145491b83700000000000000000000000000000000000000000000000000000001f2200009a1afa00000000030a)
def g247D8 (j : Nat) : Nat := (if j<4 then (if j<2 then (if j<1 then 0x78159551b7f8359551f778159551fb781591519fd86dcd51d7d65dcd51dbd64dcd51b7d859cd519fd861cd51dbd641cd519fd8798d51b7d8598d51bf58198d519ff8758d51cfd7658d51e7d6558d51b7d86d4d51d7d76d4d51f3d64d4d51b7d8594d51bf58194d51bf78154d51b7f8654d51b7d8654d51d7f7654d51d7d7654d51f3d6454d51f5e6354d51f5d6354d51f778154d51bf78358551df77358551ef56358551f775358551f755358551bf586d4551f7565d4551fb564d4551bf583d4551f7553d45519fd85ddb319ff855db319fd86dd7319fd879d7319fd869d7319fd839d7319ff865d7319fd861d7319fd8799731d7d75997319ff87597319fd8759731cfd7659731d7e7559731d7d7559731dbf7559331dbe7559331dbd7559331dbc7559331fb78159331ddd7598f31ddf7558f31ddd7558f31edd6558f319fd87d4f319fd85dd9319ff855d931df7815d9319fd86dd531bbd849d531bdd839d5319fd869d5319fd839d5319ff865d531df7815d5319fd861d5319fd8799531d7d7599531bf581995319ff87595319fd8759531d7e7559531d7d7559531dbf7559131dbe7559131dbd7559131dbc7559131ddd7598d31bf78158d31ddf7558d31ddd7558d31edd6558d31fd78158d319fd87d4d31bf581d4d31bf78154d31bf78558531df77558531df57558531ef56358531bf78654531bf58654531df77654531df57654531f766554531f756554531fb56454531fd66354531fd56354531f775354531f755354531bf586cc531bf585cc531fb564cc531fd563cc531d9f739cd64bad829cd64bb7815cd649bd841d5639ed821d5639f5811d5639f9801d5639bd84dc9639f9809ce53b5e8598e53cbf7659153e5d6558d539bd84dd8539f581dd8539f980dd8538fd879d853cbe845d853cbd845d853cbe769d053cbd769d053cbe765d053cbd765d0539bf865d0539bd8799053cbd76990539bf87590539bd8759053cbd7659053cdd7694c539df8754c53cdd7654c53cf6769c453cf5769c453db5749c453cf6765c453cf5765c453db6745c453db5745c453de6725c453de5725c453db6645c453db5645c453d77535c453d75535c453cfa765c053cf9765c053dba745c053db9745c053df2715c053df1715c053dba645c053db9645c053dda535c053dd9535c053df2815c053df1815c0539ed82dda438fd861d6439f5811d6439f9801d643cbd7659243b9f8359243dad645ca439f7815d9439f5819d543cbf76591439bc8755143eb7815916197e851cd6197d851cd619bd841cd619ed821cd619f9801cd619bd84ddb519bf865d3519bf87593519bd87593518fd861cd519bd841cd519ed821cd519f9801cd51eb564585518fd861d7319bd841d7319ed821d7319f9801d7319bd849d531eb56458531ed563585319f48754531 else 0x1dd953cff865d9539ff835d953ddf835d9539ff815d9539fd86dd153cff7659153ebf76591539fe8798d53bde8798d53dde8798d53bdd8298d53cff7658d53b7f8558d53b7c8558d53edf8658d53edf7658d53f5f8558d53f5c8558d53edd6558d53bdf8258d53b7d8694d53f3d6494d53f5f7394d53f5d6394d539fd86dc553d7e65dc553d7d65dc553dbd64dc553dde63dc553ddd63dc553dbe845d853dbd845d8539ff815d853ebd845d853cff845d853cfd845d853cff815d853cfd815d853bbd869d053dbd769d053dbd765d053cfd7659053bbf8759053bbd8759053ebd76590539fd869cc53dbd649cc539ff8758c53cfd7658c53dbd7458c53dde7358c53ddd7694c53f9d6494c539ff8754c53cfd7654c53dbd7454c53ddf8754c53ddd7654c53f5d6554c53f9d6454c53df5769c453fb5649c453dbd645c453df5765c453fb5645c453df5865c453df5655c453df5645c453df5635c453df5535c453df9765c053fb9645c053df9865c053df9645c053df9635c053df9535c0539fd85dda439ff855da43dbd845da439fd869d6439ff865d6439fd861d6439fd8799643d7d75996439ff87596439fd8759643cfd7659643d7e7559643d7d7559643bdf8359643dbe7559243dbd7559243bbf83592439fd87d4e43ded765ca43dee755ca43ded755ca43ded865ca43dee855ca43ded855ca43dee655ca43ded655ca43ded635ca43def535ca43ded535ca439fd85dd9439ff855d9439fd86dd5439fd869d5439fd839d5439ff865d5439fd861d543bdf8359543bbf8559143dbf7559143dbc7559143dbf7655143bbd8690d43bbd8590d439fd83dd5619fd879d561afd869d561bbd849d561bf5819d561bf7815d5619fd831d561ebe7559161ebd75591619fd85dcd619fd879cd61afd869cd61ebd649cd61bf5819cd61ebd645cd61bf7815cd619fd851cd61cff7558d61ef78158d619fd87d4d61ebd64d4d61bf581d4d619fd8794d61afd8694d61ebd6494d61edd6394d61bf58194d619ff8754d61ebd6454d61edd6354d619fd8714d61afd8614d61bbd8414d61ebd6414d61bed8214d61bf58114d61bf98014d619fd83ddb51dbd845db519ff835db51b7d8399751b7f8359751dbd765d351f3d655d351dbd655d351bbf8759351bbd8759351dbd749cf519fd869cf51dbd649cf51dbd745cf519ff865cf51d7e655cf51d7d655cf51dbd645cf519fd8798f51b7d8598f51dbd7498f51ddd7398f519ff8758f519fd8758f51cfd7658f51e7d6558f51dbd7458f51dde7358f51ddd7358f51b7d86d4f51d7d76d4f51f3d64d4f519fd8794f51b7d8594f51dbd7494f51dbd7454f51b7f8654f51b7d8654f51d7f7654f51d7d7654f51f3d7454f51f3d6454f51f5e6354f51f5d6354f519fd83dd9519ff835d951df7815d951b7d8399551bf) else (if j<3 then 0x8d51efd7658d51bff8558d51f7e8558d51f7d8558d51efd6558d51dff7358d51fde7358d51fdd7358d51ff58158d51f7d63d4d51bfd8694d51dfd7694d51f7d6594d51fbd6494d51fdd6394d51bff8654d51bfd8654d51dfd7654d51f7d6554d51fbd6454d51fde6354d51fdd6354d51ff78154d51f7f8654d51f7d8654d51f7d7654d51f7d6354d51ff68358551ff58358551ff67358551ff57358551ff65358551ff55358551ff663d4551ff563d4551dfe855db31dfd855db31bfd869d731dfd769d731bff865d731dfd765d731dff865d731dfd865d731bfd8799731f7d7599731bfd8399731bff8759731dfe8759731bfd8759731dfd8759731efd7659731dff7559731f7e7559731dfd7559731f7d7559731bff8359731fbe7559331fbd7559331dfe7558f31dfd7558f31efd6558f31fde8558f31fdd8558f31fde7558f31fdd7558f31bfd86d4f31dfd76d4f31f7d65d4f31fbd64d4f31fdd63d4f31bff8654f31bfd8654f31dfd7654f31f7e6554f31f7d6554f31fbd6454f31fdd6354f31bff855d931ff7815d931dff855d931dfe855d931dfd855d931dfc855d931bfd869d531dfd769d531bff865d531dfd765d531ff7815d531dff865d531dfd865d531bfd8799531f7d7599531bfd8399531bff8759531dfe8759531bfd8759531dfd8759531dff7559531f7e7559531dfd7559531f7d7559531bff8359531ff58159531fbe7559131fbd7559131bff8558d31dfe7558d31dfd7558d31efd6558d31fdf8558d31fde8558d31fdd8558d31fdc8558d31fde7558d31fdd7558d31bfd86d4d31dfd76d4d31f7d65d4d31fbd64d4d31fdd63d4d31bff8654d31bfd8654d31dfd7654d31f7e6554d31f7d6554d31fbd6454d31fdd6354d31ff78154d31ff68558531ff58558531ff67558531ff57558531ff75358531ff55358531ff58654531ff57654531ff56554531ff58354531ff56354531ff55354531ff665cc531ff565cc5319fd85dcd649fd851cd64bbe85dcd64bbd85dcd64bbe859cd64bbd859cd64dbf739cd64bbf855cd64bbc855cd64dbf755cd64bbe851cd64bbd851cd64dbd731cd649ff825d6639ff815d6639fd82dd5639fd81dd563d7f759d563bdd839d563bdf835d563d7d751d563bbd841d563bed821d563bf5811d563bf9801d563edf8359563edc83595639fd85dd163bf7815d163afd8598d63bbd84dc9639fd85dc963cfd65dc963dbd84dc9639fd85dc5639fd85dda539ff825da539ff815da539ff865d6539ff815d6539fd87996539fd8759653cfd7659653bdf8359653dbd7599253dbd75592539fd869ce53dbd649ce53ddd7598e539ff8758e53bdf8758e53ddf8758e53ddd7558e53edd6558e53bdf8258e53bdd87d4e53bdd86d4e53f9d64d4e53dbd645ca53ddd635ca53dbd645c653ddd635c6539fd8 else 0x53f7d7694d53bfd86dc553dff76dc553dfd76dc553f7e65dc553f7d65dc553fbd64dc553fde63dc553fdd63dc553dff86dc553dfd86dc553dfd65dc553dfd63dc553bff865c553dff765c553dfd765c553f7e655c553f7d655c553fbd645c553fde635c553fdd635c553ff7715c553dfd845d853fbf8759053fbd8759053fbf8359053fbd8359053fbf8159053fbd8159053dfe7558c53efd6558c53dff8754c53bff8654c53bfd8654c53dfd7654c53fbd6454c53fdd6354c53fdf8654c53fdd8654c53dfe855da43dfd855da43bfd869d643dfd769d643bff865d643dfd765d643dff865d643dfd865d643bfd8799643f7d7599643bfd8399643bff8759643dfe8759643bfd8759643dfd8759643efd7659643f7e7559643dfd7559643f7d7559643bff8359643fdf8359643fdc8359643dfe7558e43dfd7558e43efd6558e43bfd86d4e43dfd76d4e43f7d65d4e43fbd64d4e43bff8654e43bfd8654e43dfd7654e43f7e6554e43f7d6554e43fbd6454e43fdd6354e43fee655ca43fed655ca43bfd8399543dfe8759543dfd8759543dff7559543fbd8459543bff8359543fdf8359543fdc8359543bff8558d43dfe7558d43dfd7558d43efd6558d43fbd5458d43bfd86d4d43dfd76d4d43f7d65d4d43fbd64d4d43bff8654d43bfd8654d43dfd7654d43f7e6554d43f7d6554d43fbf8454d43fbd6454d43fbd5454d43fdd6354d43fbe6590d43fbd6590d43bfd839d561bfd859cd61dfe759cd61dfd759cd61bff855cd61dfe755cd61dfd755cd61ff7815cd61eff8558d61efe8558d61efd8558d61efc8558d61efe7558d61efd7558d61efd63d4d61bfd8794d61bfd8594d61dff7594d61bff8754d61dff8754d61dfe8754d61bfd8754d61dfd8754d61dfc8754d61dff7554d61f7e7554d61f7d7554d61dff7354d61efd6354d61ff58154d61dfe835db51dfd835db51f7e8359751f7d8359751bfd869cf51dfd769cf51f7d659cf51fbd649cf51dfd659cf51bff865cf51dfd765cf51f7d655cf51fbd645cf51dff865cf51dfd865cf51dfd655cf51bfd8798f51bfd8598f51fbd7498f51fdd7398f51bff8758f51dfe8758f51bfd8758f51dfd8758f51efd7658f51bff8558f51f7e8558f51f7d8558f51efd6558f51fbd7458f51fde7358f51dfd7358f51fdd7358f51f7d63d4f51bfd8694f51dfd7694f51f7d6594f51fbd6494f51fdd6394f51bff8654f51bfd8654f51dfd7654f51f7d6554f51fbd6454f51fde6354f51fdd6354f51f7f8654f51f7d8654f51f7d7654f51f7d6354f51dfe835d951dfd835d951f7e8359551f7d8359551bfd869cd51dfd769cd51f7d659cd51fbd649cd51bff865cd51dfd765cd51f7d655cd51fbd645cd51ff7815cd51bfd8798d51bfd8598d51fdd7398d51bff8758d51dfe8758d51bfd8758d51dfd875)) else (if j<6 then (if j<5 then 0x208082020809b823e082021c000020806f8088022008807d019607641be01981aa0220196060813f059c15304fc12404240ee034c000022000000000a30000088000000001980360050000dfe755d663dff845d663dfd845d663dff825d663dfd825d663dff815d663dfd815d663bfd84dd563bfd81dd563dfd84dd563dfd81dd563efd869d563dff759d563bfd849d563bfd839d563fdd839d563bfd829d563bfd819d563eff865d563dfe755d563bff845d563bff835d563fdf835d563bff825d563bff815d563dfd751d563bfd841d563bfd811d563efc8759563eff8359563efe8359563efd8359563efc8359563bfe85dd163bfd85dd163dfe75dd163dfd75dd163efd65dd163bff855d163bfc855d163dff755d163dfe755d163dfd755d163dfc755d163efd655d163ff7815d163efe7598d63efd7598d63bfe85dc963bfd85dc963dfe75dc963dfd75dc963efd65dc963dfe85dc963dfd85dc963dfe755c963dfd755c963efd655c963bfe85dc563bfd85dc563dfe75dc563dfd75dc563efd65dc563dfe85dc563dfd85dc563bff855c563bfc855c563dff755c563dfe755c563dfd755c563dfc755c563efd655c563dfd855da53dfd845da53dfd815da53dff865d653dfd865d653dff845d653dfd845d653dff815d653dfd815d653bfd8799653bfd8399653dfd8759653efd7659653bff8459653bff8359653bff8259653bff8159653dfd655d253bff8559253dfd7559253fbf8759253fbd8759253fbf8559253fbe8559253fbd8559253fbc8559253fbf8359253fbd8359253fbf8259253fbd8259253fbf8159253fbd8159253dfd7558e53efd6558e53fde8558e53fdd8558e53fdd8458e53fdd8158e53dfd76d4e53fbd64d4e53fdd63d4e53fdd76d4e53dfd655ca53dfd655c653bfd84dd953fdf83dd953bfd81dd953dff84dd953dfd84dd953dff83dd953dff81dd953dfd81dd953eff765d953bff845d953fdf835d953bff815d953dff845d953dfd845d953dff835d953dff815d953dfd815d953bfd86dd153dff76dd153dfd76dd153bff865d153dff765d153dfd765d153fbf745d153bff8759153bfe8759153bfd8759153bfc8759153eff7659153fbf7459153fbd7459153bff8359153fbf8759153fbe8759153fbd8759153fbc8759153fbf8359153fbe8359153fbd8359153fbc8359153fbf8159153fbd8159153bfe8798d53fde8798d53fde8598d53fdf7498d53fdd7498d53dfe8758d53eff7658d53bff8558d53efd6558d53bff8458d53dff7458d53bff8258d53bff8158d53fdf8558d53fde8558d53fdc8558d53fdf8458d53fdd8458d53fdf7458d53fdd7458d53fdf8258d53fdd8258d53fdf8158d53fdd8158d53bfd8694d53dff7694d53dfd7694d53f7e6594d53f7d6594d53fbd6494d53fdd6394d53f7f7694d else 0xacea9d7b8d2e19b136c1e9db69bda6f689ca7929e4ac669d7a2c28df9c8edfeb78e9ca9c8edc8b6b67239c8e7239c8e7239c8ed8bb5de723b556d3aa272d18b412ce2b31ecb3b22a8b0b1a29cab136723b0cac1eb02ab19ac9ab3aac9aa3aafa2bd4af029d7ac9a9eaa7929e4a75eb19aeb29ca9c8eb91adda9d7ac66b26ac9ab54ac9ab19a75eb4704feb3aac9ab26ac66b19a8ea9d7abc2737ab3aab3aa7ea8404fea69a2c29d7a2c2a4e9f66a3aa898000a82e9f7a75e76da7a8196a7929d7a6f69caa6f69a2a61e8df9fb696ca5469369f6691ba41e8eca37e874a3127d959467d9a2c289ca2727d9a222874a18276da116823a020707054e7ed9f6565104fc6869efa79c9e0676d9d2e7379c8e7239b7c13f9c066df69466bd04fe69b99c97e7995e63507d261a97fe5e496ee5a796165637d2a541949a526949a50b93a64c7927a47c918640290fe42b900a3e78f163aa8e2071b4f9a35f8cf63294f9a2f9709a2d08aba28c6d4e26a890621f8811b3822ee1f0871e1ac860e16184e212b84260ee83160a3822206680c204b80c200e7fcdfd87ef5f9b7e01f5e7d29f217be1edd7b749947aede9279dde4e785ddfc774dd9676c5d9675d1c8c2651c8c5071d44709826e2651d147391cc26d4d36531cdca06d4db537231c6a6ce1c48265021c2e30b8c2e31c262ce9bfd2651bcd5070b8c1c6db536ec89946e25b6e2651b536ce1b1d2b19afb3160c2f6b813e66af8bf92f41a952e31a6c6025a5168a013f1c6da0667919c966b998c65a9948647d90463a58c729818a5620c847618583f60918095f9d7cc5ea978812d977403b96a95d4973e364172a5c596ed5b2d6a95a1d66c594413f58a161404fd5f9577901156b8d31561556a54e951853f54d45275474507145250dc7e7507141c50713e650048f14f98bf94f108bb4ea538e211c71b31cd3654d2932104252f84b04a6029812981f14ac649bcf4b491921647ed1d222ecb8c46c0994000071b463896b45b114a44851064358df6429892e41a508424b88bb41a504e40cd01135d4fe80000c0d3efca602980f9d2b18f743d2cd313ca4f0000000003b94ec33a68e783920e1837d8dc636acd9035d4d4c34c4d0822ecced332ccb03238a602b18c731c6cc581c6cc2f303492e2430bf92f40ba72e30b631328b3a2c0cada0658a602b18a9d29ec71b2980a3028389f3274400026bc99425ac9491c6c92e24b890c23c48cf22ec89221a484720407e71f144b61e8c77a1d447361c6c0001c1c6ec1b286a11a1866418b454b17d85d4169056d152c51b000050012d84ec13284b60658451128848711b046c11b045108203d010bc40604903eb0f4020808203a0060820809b82080e1438508203630d0430a08202ef087018208200880b50208000020800002080b502ab082028909b82080820) else (if j<7 then 0x304f14a18e003040e045c62820213c52c6280f0131898e9010c20701e2963180840e284c6c808600305022070c14608000890c080f0cb18a042a3f0278a414309e290510363181d201e318814604042e3f14850e1a1d2022870c00488043800de21d21c0060e1408a031d2022630148088000e3f14850e000f8c62814628300140868c08407c070e180a404402021f8a42c30e04309e19051028701e00b2863810a11978010c703e190510085f001943183830de0085643c300c808810078030d90d0c2810e181083860804408042c41820b88306171090c2620c187254fc0804292f1cc5a414087480890c08401e0505183011218401e0388100520c2010e10078141470a00486c82810c5b2f02828a14584022320224308044b21414602140091008908206082320c181a4183021820e1820e242021c306043841c084169060c2b212180f01c30148306003030be038c102860c0800a184240c30bf01c6021fc43102810a89c5dd1774ebd7e68a6f69bda3b28eceb1bbc09c8fe5bc2c3e479c8faf5ebd7c54ac67ac6f91fe2cf863e18f7f7ac6f76fdc0f696723f697d83ac9bd61a7929eaac67c39f05fd46f4afd17f3d7cdae202723f336b26f1a29eaf2e7c9ed90bc68ac9bc68f20eb26f1a2b19ac9bc54ac66b26f0e7c17ac9bc03f00c153a2727235dd04b6a8eaa3ac2c3be8a6f676def527379c8f836a72a9ca9c8f1955dd3b9ee12bbc004ff50aa6f7b9ea75eb19a6f7b83ee0e96c40cfb61ac9ab199c8e9bdb07ab3aa75eb26acea723b07bb38a72bb16eb1bac6ec0baf5ebd7699eb6a9caea5fac6eaaeb19ea5fa83e9a3a0240cfa3fe877a029db78cae79f9bee68f98fe5d3952e32b930e4578ece32b8b6e28b880ad1f865e12a89ca6f69bda7929bdaeb3836e06e76ddfe77d0debb78cddaa723dd23719dcb69caa68b719dbfb6e3054ee34a8ea9d7a7ab6c89c8f6a6a89b699d9fb66ad95b642a6f7627a6f760caceab3ad7ab5c8a82f5ada89a9ead5a758ba2735699db6860d51f525d4299c940cd033ac9b4ef9db74d4d3034a5d20f4619c8eb199c8eb76d11b42bd0433eecf6b3bfa7ab0b0a7aa8dfccfe874ceaedfece43375cd4e8dfac6733fac9b316cbeea26aceb2e0b2cf2c5a37f2a3a7ab281c97f24bc2c3230c2c0167c8571fac763101c71013fc6a67d9c6569bdc5eb15fc513130a5b3115c4070dfa6f69bd5dd296cc2c30c4c2c309ca75e9d7a272723bc8689c9c8c153c2228dfa1d28c4a2728b09f66a9fb2ce723a792f94a7929e4a75f066a2729d7b2ce860a02304bb07b030a75e9d7a82ec1ea75e9d79c8f00ebf96fd1bedaa3aa7def94a6f69bda27289ca37eb47b5de9d7b78e8dfac66723bde6f5ebc8691bbcf2b26b8d2a26a75e9d7bc86f06a37eee4bb26eaea272e8ca82e9d7b9aabe8a75e7239c8ee48acea723 else (if j<8 then 0x2080e30201104171a200104460020604204102870c207001870cc8300c820ac820201906c800414100003481020810b4830e000861c3010c38100180081c302029078c084043840f182000870c380080010828708063080050b180021a30e000898c3810c287001800e1070a0030800281119000a1810a1056410088102841000410307122040de0388002620c2040f88308103800c245081c486142780e278c42c36788087e19840c384f18998a1050400262f02040e0060818205142040a28304006060820018262014c3081c0e2f04c51612101103931418401e29884c50400262f14c517480860033314200662830c17c3210380a41bc0a10012f0200181040e182f8a43000c043891400ba4044081800110084002840210078a42850803c081000a0c0090838609e058be05840c38626c808b4c2320220101e293317c02180331820024303080297866284014c3084bc530c9d325e0400046062c0010c078a42c409e09061090a0c0851418b2410088049780c092082840028203cc292f02840acfc521490b14185242c50810032f14c5f0c828614078654c50800386f0c898f4d9010c084f0ca98a10005142060a283f14808913c000c043891bc06081c0091a90708180091bc1202244040058a1028a0800608244080008910300022440e19905022f86418200123040224364182001228112283002c507c80890c352021810e10308040060e905082440c00278c628509e2963142000c1c30012906142b2081840210286103810c185081831610286102871618464142091028465e218a1618a0c38b121850e2c088103d20c206c6c808804006122010ac83081858c0e978c6184001c309483010c0010c244640008610301083780e004001820e302121c2021bc070a281f00038813c0700204001c088103810c007021a20203c0714507082780e18746283021c300f0146c413187022e308043081c30046046c610001111e2021e2f0044e3151060e04078463a2021fc6314305000440c00086140010c2a318185a4243021800910085181860e3030e00304022800a2430201978c628565e0063142070c03c324638646169011425201e318a10380f18c502182f8a48c6018c50604078c7485081918c100800a2446403c63102846424402171f8642850224300180f8648c600100e3f0c86460028c13c6300180463030a1c3061fc05002070c17c00140060a1c08a8c0520220703e006314284f00318a14278002040c17c00151f80a18065e318810032f18c508cbc051028165e00631830401e19231b180640440210078658c60be1187e03800c2f80018401e03c317c050018501e2943161851818700184890c2890c0c3f014400100861c28c0c28465e318a180050226318100a413c6314280f01318a1028c0c284f18e90a1038600245001c else 0xb0710213104880040c0330a684a61810e00208cc2000e104001841acc00800353082530a103001a9861a984043800c2530e04384085a615344103a61c2074c0040d104080840e181001c20802984043050c05208304082870c1040e18586040520823302182d215981014840948266086674830ccc2701998611984cc0041a9b20e9810c1590a149070c2060ac83a61c306269070d4c5241c3061e9841c3520c0860b4842648307129070c1b8a41c313142920c1c40c1c2261022604307103130e1850c1c3084820802906cc284a4233a41c305159840b484660090410092001040075984119810e1b30810b6610302cc206100320c28100104240b2094c3a6c82a60020a10208c89874c2320e98508004a600087102806419302c80094c080642780c1c289483850c2040e183d003187a31b20d6e308085641845a8c008016e3082050ec830c002078c0320c0320c1040cc820ac82061c204140040c281a41e3a400208103858e9060a105c61c206142320f185641e30a0590815163082230a882098c204c83840c0890e1810d4834614380100e30828608185a41050c043641c3061c3000d901091070c186c61010a18388143810c3050a1840a104080854400402880078c2000f18002c840ac8263002e30012308003c61420013187001d20e003a41318010084001e302c83c6042b2131b2001a30200302031b213181641448410063100b209904001e300103c648007480800c080081e36404008131858c0320a20446003098d9001118508263641440803186140058d900080450210007100800a1c3001430200286002020190410232099040890408284a41d200103c60008410382c810010))))
def g247H8 (j : Nat) : Nat := (if j<5 then (if j<2 then (if j<1 then 0x3186e0b5000000000000906d00000000000000000000000000004b930000000000000000b39000000000d0b7d10d0000000000000000b3bf000000000000000000000000e8030000000010d900000000000090d7ebc7a0aa0bba0000309200000000000009be000052d60000000038090000c422000094200000000000000000c99500000000000000000000000000000000000000000000d331abff000000000000f30251090000000000000000000000000000a19e606ec2a700000000000061520000000000000000000000000000c24f00000000000000000000000000000000f8fd000000000000000000000000000000000000000000000000000000000000000022630000000070040000619bd3d53a92b999000000000000000002f3000000000000000000000000a0df00000000000000000000b0d500000000000000000000000000000000000000000000000000000000c30300000000000000000000000000000000000000000000000000000000000000007a91000099c80000000000000000dbf8000000000000000000009b44000000000000000000000000000000000000f170000000000000c2c961b00000000000000000000000004007000000000000000000000000000000000000d2f40000000023b200000000907ee1d500000000a2ce000000000000f1760000000000000402000000000000b85d00000000000000000000000070530000000000000000000000000000d3ff000000000000000083850000000093e700000000000020b0814a000000000000a2b70000000000000000942600000000701c000000000000000000002864000000000000000000000000da7e000000000000000000000000c251000000000000d17d0000e00f000000000000000000000000000000000000000013a3544c000000000000000000000000000000000000000093ab000000000000140a00000000000000000000000000009333928f00000000426f0000f18300000000000000000000000000000000000000000000000000004312000032a4f26b000000000000a3830000e16c000043d40000000000000000d2a6000000000000000000000000000000000000000000000000a40f51394863000000002ba90000000000000000000000000000000000000000000000000000c363000000000000000000000000611600003210000000000000215b52f8000000007011000002340141000100140642003144040151030000600230120310001030110202105051150100101000000802003200070201003220050611310211002000011000610300014210101031007000120101220000001040021010240100201201100251050452055100101305310010401150230005261010040d0231011020500045010002019 else 0x233000000004306d00200000000627e0000000000000000000000000000000000000000000000008336000000000000e98900000000000000000000000000000000000000000000000000000000a2ac53e3b3e90000000071b90000b82500000000000023260000d278dc32000073fe31ae0000000000000000108c52614256c3f752f6819563e8612fc0c0125f00000000000000000000000000000000000000000000000000000000000000000000000001ef0000000000000000000000000000000023ce42300000000000000000000000000000000000000000c358827a0000000000000000000000000000d25c00000000000000000000000000000000844800000000000000000000000000000000000000008bf50000cbf4f3290000d3f8000000000000000000000000121f000000000000000000000000000090c10000000010ed00000000000000000000000000000000000000000000000000000000740c0000d1f153d3000091000000000000000000000000004417000000000000000000000000e024000000000000000000002baa000000000000000069bf00000000000092c3000000000000000000000000000000000000000000000000000000000000000000000000a34900000000000000000000000000000000000000000410000000000000537a00000000320d00000000000000000000d8b5000000000000000000000000a16f0000c3520000814b2081f23e000008b2835f0000000000000000000000004b0500000000734700000000000000000000000000000000504cd098000000000000129b21e000000000d29c63f1000000000000b142000000000000737c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000038f0000c0e40000a11d00000000000000000000000000000000000053d871710000000000000000000000000000000000000000000000003174c2710000c3090000000000000000000000001bde0000000000000000000000000000a0ca428ea0f9000000000000000000000000742e0000910300000000000000000000a3b10000d32a00000000000000000000881700000000a375a18200000000d298022f000000000000019900000000000000000000000000000000000000000000000052b10000000000000000daf9000000000000c1ce0000000000000000208000000000b8fa936a00000000000000000000000000000000000058570000000000000000000000000000000000000000a3fa49d00000000041b200000000000000005be20000000000000000f8c000000000000000000000000000000000000000000000000000000000739e7184f15100000000000072d500000000ab46000042240) else (if j<3 then 0x338d931a00000000000000000000000000000000000000000000ebebe3ad135b72900000615d91c6000000000000000000000000000000000000000000000000000012c6000000000000000000000000000000000000000000000000200a93940000000091b80000000000002a8f71d7000000000429520f0000e0967101e02e0000000000000000000000008137000000005351424d0000000000000000000000000000f0220000bb170000000000000000000000000000f2460000000000000000000000000000938600000000000000000000000000004335538400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000f865000000000000f34e920c000000000000000000000021000000000000930fd28108ebb0a0b44a51ff41810000000060b20000c25b00004a8e000000000000000000005b9ce0c50000f1730000000000008b1500000000000000000000114d00000000000000000000000081df00000000000000000000000000006106719f000079c500000000e33e000051be000000000000000071e900000000c04900000000000000000000d111f070000000000000000000000000000000006269a3a600000000000000000000712b00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000a1ab0000726a00009078000000000000000000003ba60000000000000000b3a50000000000000000000000000000000000000000000000000000000000000000000082aa000000000000000000000000342b0000000000000000000031470000000062c8a11200000000407500000000000000000000000000000000d2df4131025833438328c34f4073000000000000000000000000000000000000000000006141f8bd9845f20500000000f00b000040b6000000000000000000000000000043010000404e0000000000000000000000008bee00000000000011ee0000000058b7aa450000000000000000482e00000000241a0000000000000000000000000000000000000000000000000000a3cd6bcd014e000000005057242d000000001076d33dc22900000000000000000000000022030000000000004072000090ac000000000000000000000000000000000000940b000041a9000031430000000000001b3c198a00000000000000000000000000000000000051cb000000000000000000000000e3e4000070da00000000000000000000000000000000000000004b110286000000000000d17800000000b39b00000000c0eeb1f493df000011050000000091220000034600000000620a89a8805a00002b6340f40451ab01443ed412b0c990e300005 else (if j<4 then 0x738b419a000000000000b2d10000000000000000000000000000000000000000000000000000000000000000000082c40000000049f7e1a000001be90000000000000000000000000000000040ce000030140000000000000000542f92c773ac000000000000000093bb000000000000000000000000c06b0000000033fd00000000b267000000000000000071c30000000000000000000082950000fb5caa87000000000000000000000125000000000000000043af51fbb44e000000002b58b28c8c2e0000000000000000000000000000a4130000000000000000000000000000d1e800000000000060a80000f1fcf2b80000c37800000000000030f6530b02260000000000000000b22a00000000000000000000f2d300000000000000000000000000000000000000000000f046c13ec36d00000000926c0000000092b600005b9a000000000000000000000000000000000000000000000000d1320000a08a000000000000a2bb00000000000000000000000062fb0000000000000000000000000000000000004031000000000000ac2d0000000000005011939f0000f37700003289003b00000000000008f8b8280000000000000000000000000000000000000000000000000000000000000000e397907b00000000000000000000000060eb000000000000000002ca2b540000000000000000000062d400000000000032c0000000000000000000000000b14600000000000000000000024c71ec00000000337f0000000042220000000000000000000000000000000000000000db8c000000000000b04d0000a848000000000000000000000000000000000000a381000000000000d2b00000000000000000abe600000000a1c2000082020000000000009068a25a00000000000000000000000000000000d062000000000000000000000000c11740a3912800000000000023ef000000000000000000008a54000000000000f0c4085400000000000070e1830c0000000000000000000000000000000000000000a1d80000000000002257000000000000000000000000000000000000a0d88b10716100000000e11f00000000a1ed60d6884100000000000000000000000000000000000000000000939300000000000072750000000000000000c3ca0000733c000000009afa000000000000000000000000000000009118000000000000000000006414d17900000000000000000000000000000000000000000000000040e900000000009d00002319301b716b0000000000000000000063c7abe70000000002fd0000436480a9c3960000000000000000000000000000000000000000000000000000b99c71f00000000000000000000000000000e27900000000a43b00003449000000000000205500000 else 0xc4240000000000000000000000000000000000000000000000000000000000002ba000000000000090ff0000000000000000b40e0000000068cd00000000000062250000000000000000000000000000000000006b94000000002012fb7b00005bce00004259f27d000000000000000000000000b8c200000000000002bae09400000000000000000000000000000000000000000000000000001b76000000000000000058bf00000000000000003318604200000000c05e03cb000000000000000000000000fb677b04000000000000000082dd744b604ac1ea0000000071fa00000000000000000000000000000000000000000000683000000000b0f8e38243ba000000000000000000000000000001b500000000000000000000b8ce0000000088c10000913f70370000000000000000b09e00000000212981ac9371000000000000000000000000000000000000000000000000000031ad0000000000000000b1a53093e1500000000000000000000000000000000000000000000000004b030000000042850000000091870000e97870c70000e0f5d0bd000000003823c0820000000000007a550000000071af42349b490000000061da000000000000000040a21bd5200518470000a41900000000f15300000000000000000000305b00000000b4440000a2910000c3c60000d42c00007b69000000000000000000000000b37d000000000000000064300000a2cd0000000048210000000000009401108801490000000000001bef303398c8e3870000f36900000000008f0000d22dd22000000000784f00000000000000000000000000000000000052230000000000000000000000000000000000000000007f000000000000000000000000f008f1f900000000000000000000a35500000000c0fc53bc33b300000000000000000000000000000000000000000000000000000000e30a0000000000000000000060f1000000000000e064f296b07ce2070000000000000000000000007a820000000098de000000000000000000000000d3f300003221215aa22e000072550000000000000000000013890000000072a0b0c3000000000000cb0800000000000000660000b121113d305100000000f2fa0000000000000000000000001baf00000000000000000000f307000000000000000000001360000000000000cb6400000000d175000000000000a2f1f4460000000051c900000a8c0000000000000000807d0000000000000000c29d000043e50000000000000000000000006013000000000000000000000000000000000000000000000000000000000000329202f70000000000000000000000000000000012434238000000000000283c001e0000c99300000000000000000000000002880000000000000000000000000))) else (if j<8 then (if j<6 then 0x534d000000000000523100000000d910432c00000000d1f5000000001a96000000004b68000000000000122c0000cb060000000000000000b2a300000000000000000000000058b90000000000000000534422b90000000000000000000000000000000000000000000000007376516a0000e0ab00007b6c00000000000000000000000000000000782f32410000e035000093c100000000000000000000000000000000000000000000a015000000000000000000000000223b831c000013ec0000000000000000000000000000000000008ac1000000000000000000000000000000000000000000000000000000000000e18a000000000000c1670000000000000000000000000000000000000000e35400000000000082fc000000000000000040850000000000000000000080410000000000000000bb7e00000000000061130000000092ef784c000000000000000000a4000041cd6148e1b372ebe3db00000000000000000000000043a40000000000005054000000000000000000000000b2b4000000000000000000000000000000000000000000001a3f9836b36f0000000000000000a36739c000000000000061bf0000000000000000b97f0000000000000000000091e50000b1660000210200000000908d000000000000000000000000000000000000000000000000000000000000d0d000000000c0de0000da8b0000bb2300000000000000000000000000000000000000000000f1dc0b7f00000000000000000000000000008190c3170000d99a00000000000000005108000000000000d1200000000000000000000000000000f0a600000000000000000000000000001bca0000000000000000000000000000705000000000000000000000a3b5a044608e6bb5a2534998000043eb0000000000000000000000000000a3e203700000000013e10000a0e70000926472170000d2820000c31d000000000000000000000000e29f000000000000000001970000a0bc0000ab380000000000000000000000009063000000000000000000000000000000000000000000bf00006299b039000000000000c33a000000bb402b13c2a2bc497c00000000000000000000b191000099e830200000ba7f099700000000000000003321fa900000a12c0000000000000000000000000000000000000000000000000000e33f0000000000000000000000000000000000004017406c000000000000000000000000000000000000000093c800000000000000000000000000000000000000000000000000000000e07400000000c1dd00000000000013d7000050cc0000820bf24a0000000000000000b3740000000061d30000000000000000000059c4000081930000000069e27350000058180000e0ec41620000000000008b61000000000 else (if j<7 then 0xc39d184b000000009293f1350000000000000000000000000000299b726ec0650000000000000000000000000000000000001b73000000008025f41e720412b200000000e09700000000f2e9b33000000000427b0000000000000000000000000000000000000000f1a20000000000000000000000000000000000000000000000000000000000000000000000006b3900000000000000000000000070dc000000000000000080fac9150000000000000000000000000000e8490000115e00000000000000006123a1bd427f000000000000000013ee00000000702300000000d359709bc04f000022da000000000000a9c300000000528312bff441b0a1b0676452000000000000000051d400000000000000000415310400000000000000000000000000000000000000000000e4350000000000000000000024270000000000000000000031540000000073da00000000000090f00000b3220000029a0000000000001a88e196d2b5000000000000e163f3aab39a0000000090d1d2dc31300000000000000000a35a000000000000000000008c1e0000000091bb00000000000049c600000ac90000000000000000635d0000000000000000717f00000000bb2500000000000000000000b34a00000000000011c1e0430000000000000000000000000000e061d34872e0000090c600000000b22741a3000000000000000000000000000052664215e02a0000102f0000000000000000000000000000000000000000000000000000000060e8000032e6a3dd0000000000000000000042a500000000b43200000000000000000000f03800000000000000000000000000000000000022e200000000940d00003313000000000000315700000000328b80d2908301980000834c000000000000d38040340000e2800000000000000000000000000000000011b7000000000000000000000000921e00000000000070f700000000000000009408000044090000000000008ba8000050f34428e8b4000000000000000013fb000042f900000000000000000000000000000000b44d5b450000d16d000000000000b85300000000000000000000a37b4212000000000000ab71000000000000000000000000d3de544700000000000000000000000000000000000000000000834b72ee000062b37be370060000000000000000000000000000000000000000e2d20000000000000000a0af9c3071a6b3e000000000000000000000000000005c2f00000000000000000000000000000000000000000000c12da3f6000000000000b3a7418e000050b80000da950000f287000000000000000000000000000000000000000021e60000000000000000000000000000000010181418000063200000000000000000d17c00000000a21841c40 else 0x314400000000000000000000000000000000000000000000e194d85c503d00000000000000000000000000000000000071ba000000000000f0e500009395f3f40000000000005140000000000000000000009052000000000000000080cb53f900000000b126000091cc0000000000000000eaf8000023660000121300000000000022a832dbc06f13b903f5f36bf1a10000e10b00006831f42a629700000000000064045133000000000000443c00000000000000000000000033f0000000000000000000000000000092400000000000000000abb9000000000000802c00000000000000000000000000000000000000001099000000000000024b00000000000000000000000000000000000000000000000000000000000061d022e500002304000000007254000000000000db0d0000000000000000000000000000b83d00000000000000000000000050030000104870b300000000784600000000434144330000000082e10000000000003b9b0000f0be0000e84e000000008403000000006437527c311cd119000000003164a31b30890000d2ea000000003af36010b1fd000000001c34c41d00000000000000000000000039a70000000000000000dbfc000060603058610794500000000091a800000000d20600000000000000000000e16000000000000000000000000000001bdb000000000000000000000000d19da3d902480000000000000000717a40b45a93c15500000000000072ab000000900127000000000000b35793cc744f00000000000000000000a3c40000000000000000000000000000000061e200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000e8be000000000000000000002824f2399000000000000000000000000000000023140000ebc80000000000000000000000000000400e00003136000002730000000053ed00000000915600000000d091e12441db00000000000000000000000000000000724500000000000000000000000000000000000000000000000000000000d8bc0000000000000000000000000000341600000000000000000000000000000000ea8a00000000000063e600000000000000000000000000000000525deb62000000000000000000000000000000000000000000000000000000000000000000000000000000000000b2cf00000000000000000000000000000000000000000000000032e30000000000000000000020c80000c41f000049f0b0719a8d000000000000000000000000912e63b00000000000000000000000000000000000000000000000000000631e0000432fc06a2270000000000000b33b0000a20933ea000000000000000000000000000000000000000000000000000000000)) else (if j<9 then 0xcb3700000000000000000a560000000000000000000000001be50000000000000000714c0000ab66000000000000000000000000103a0000000000000000000000000000000063b800000000000000000000c1340000c3fc000000000000000090ba000071f8000000000000000000000000000000000000000000000000000000000000000000000000000061720000000000000000a0cf0000000000000000000000000000000000000000000083400000000000000000837e0000000000008047b31150560000026d000000003b5b0000e8425b260000b0010000000000000000000062bd00000000000000000000000000000000133800000000000000000000584d438a0000f0c2b01d000000000000000000000000b06900000000000031f6b97b000000003b7a00000000000000000411c2ff000000002aca32de000000000000000000000000000070e600000000d2360000000000000000000093f2000011b6a02930fe0000000022f20000f2c5000000000000000000000000000039da0b5a0000000062e800000000000000000000201a000049ab0000000000000000000000000000000000000000122800000000000030090000641b00009a2100000000000000000000a0d4000000000000a83e0000b1e30000000052a900000000a18800000000d1d90000000023d00000724700000000a23db300000000005407000000000000000000000000c31600000000a1e10000000000000000000000000000000000000000000000000000000000000000000000000000c9f900000000000000000000724200000000000000000000000000000000000000000000000000000000000000008b14000091b40000000000000000024ef09c000000000000000000000000000000008265535e000000000000000000000000000000000000b158000000000000000000002b47000000000000000081800000000000000000000000000000000000000000000000006b0c000000000000dad800005284011b0000b1100000000000000000000000000000e0a70000000000000000f13c00008379a2f09324000000000000000002080000000023a20000000002141b000000330ecb9d5274d250b305000011aaa20e00000000000000000000000000000000236100000000000043dc000000000000000000000000000000008159b13b00000000803cc2d800007b0700000000000032cb000033620000000000000000000000000000000000000000000000000000000000000000d81eeb350000c2f500000000000000000000000000000000d1857084fad753a00000e3b75365000000000000000000000000000000000000000000000000b2ae1019000098320000000000000000c02d00000000d308818b00000000e2720 else (if j<10 then 0x518f000072ade01fcbec00000000000000000000f31000001a50000000000000e10f0000000060ad0000000000000000000000000000504000002079000000000000213a0000000000000000000000000000000000002391010ee235000092d0018c000000000000c03e0000312aa1770000000000000000223c000090e2000000000000000093bd000000000000000002fe0000000000000000a399db7d003692c1000000000000000000000000c200ab8f6835000000000000431f0000c339000000000000000000000000000000000000000000008bf230ae00000000a3720000d83318bb000072a19434a332f0b1215f0000b0dd00000000000071d60000000000000000007a00000000000071c0d18d00000000000000000000dbab0000717b0000000000000000d0db0000000000000000dc2b00000000743a0000000000002145f02600000000000000000000143100000000515c00000000fba100000000921a00000000d3be000000000000036c000000005086c244000000000000204b000000000000000000000000e2e7000050f2000000000000000042a2f165a337c40600000000e8bab03000000000000000000000411e0000dc33ab4e0000000000000000000000000000000000000000000000000000e09ac0a500003168000000000000000000000000000000000000000000000000c027000081b1c1e4743800000000000071c50445000000000000000000000000000000000000000072be000000009b3e0000000052ed00000000000000000000000041fe000000000000000000000000000000000000000000007189000000000000a92b00000000e19c0000000063c50000539251de00007b4ca1f2a2e40000797d0000000000000000919200000000000000000000c342d276000042c20000291600000000000000000000000000000000b3d600002844000000007323000000000000000000000000000010770000000000000000b21c00000000c21b7277a16900000000000000000000e42390cd81a77440c38800000000614f0000000000000000000000000000000000000000e05f000000000000a21600000000e3c0e1d1000070d30000000000000000000000000000000000000000000000000000000000001b60028d00000000000000000000000000000000000000000000d1cf000000000000000023ae00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000072d7531500000000000000000000000000000000000000000000000000000000d32e00000000000000000421c0b9004500000000000000000000c398000000000000000000000000000000000000410c000000000000000000000000636e00000000116e000000000 else 0xd05d0000335c00004b3a7ba4b85600000000000001a400000000a2d90000123700000000b91200000000000000000000b0950000000030870000d373000000000000643f00000000000000000000000000000000832b00000000000000000000000000000000000000000000a3c9000000000000000000000000000053a183d170fd13c3dbc3313800000000000000000000000000000000000000007114000000000000000000000000000000000000a0320000000000000000c23a642500000000000000000000503f0000100d00000000e23f00000000030d809f000000006ac493b491bc00000000b028d334a3b6aad9000000000000dae3000061f7628ab36800001268000000000000000000000000000062cc00000000000000000000aa86a1e70000000000000000000000000000700c0000000043a9017e0000000000000000000000000000c4000000684300001afb0000438ef3cf00000000c32d00000000b252000000000000000000000000000000000000e2ec000014430000000000000000000021c800000000000000000000000000000000000000000000000000000000201600000000000000000000000000000000000000000000d8df00000000732500000000422b3219b442000000000000000083530000000000000000b1f30000bb09000000000000341c00000000000000000345000079c181c70000000000000000000049c2000020ea000000000000000000000000000000009a81000000000000000000000000000000000000000000000000b262000000000000000032600000c21d00000000e10a0000000000009b6da39c00000000000041eb00000000729e0000000000000000000000000000432700000000aba523d2f11a205c53562115000000000000038cf1d20000000000000000000000000000000000007405124900000000a0ef12af308b0000543d000000009bed52010000000014390000f29400000000000000000000a0e0721100000000c3a800000000843600000000000000000000000000000000000000000000e059000000000000000081ca0000000000000000000000000000000000000000523200000000a9fe00000000525e000000000000000050fb00000000000000000000000000000000000000000000dbb0000000000))))
def g247D9 (j : Nat) : Nat := (if j<1 then 0x11400f9096210d14089143fa1a8888858096210d06e82540b11102107d73e1201c8887a13fa9110fcc7d73e11ec08887a13c61df4ee275f3a81d04e6a7353931c44e0a6f63739b48d7a6ab34c9a28cf0678336195cc8a636313983c3de6002f59770b9a5be2d49668b105762b21548a8653429114409cc4f527313509904b625212308fa471231114088843221190447f80f90ba0fa87b63cc0cd8edc74a3931c0836c6e43631aa0d1466c3241890c005e22dc1680aec55e29a0840a204f226712c090046822210687f83de1e00e706e435419b0c304201f21740b2854017413b096045c2100f9073836c18c0ba055826410e07b034815c08a0330120048000ffceb31ffd7598fffbaac7ff9d563ffaeab1ffc7558fffba2c7ff5d163ffee4b1ffd7258fffb8ac7ff5c563ffaed29ffe6594ffeb2ca7ff59253ffac729fff5394fffbb2a7ff5d953ffee8a9ffd7454ffeb22a7ff98d53ffac6a9ffe5354fffb8aa7ff5c553ffaec29ffd6414ffeb18a7ff54c53ffaed21ffe7590ffebac87ff99643ffacb21ffd6390fffa9c87ff54e43ffccaa1ffd6550ffeb1a87ffd4d43ffaa6a1ffe75587febaac3ff9cd61ffae6b0fff53587ff29ac3ff54d61ff8a6b0ffd76d47feb2ea3ff9cf51ffae7a8ffe63d47feb1ea3ff94f51ffaa7a8ffd76547feb2aa3ff9cd51ffae6a8ffe63547feb1aa3ff94d51ffaa6a8ffd76cc7ff3ae63ff5d731ffccb98ffd65cc7feb1e63ffd4f31ffaa798ffd764c7ff3aa63ff5d531ffcca98ffd654c7feb1a63ffd4d31ffaa698dff73592fe39ac9efdcd64f7ce6b27bd73593de39ac9efdc564f7ae2b25fe7598efebacc77f5d263bfae531dfd7198effbaac77f1d563dfacab1dff7458f7f31ac77fdc963bfee2b1dff7694efebb4a77f5d653bfae929fbe6494fdeb24a77f9ce53fbcc729fdd6394fefa9ca77f5ca53bfae329dff7654efebb2a77fdd153f7cc8a9fbd6454fef31aa7f758d53efca6a9dff7154effbb0a7bf9d853bfaec29efd7614fdf3a0a77f5d053f7ae829fbe6414fdeb20a77f9cc53fbca629fdd5314ffb388a77f5c453feae229ff97014effbb4877f5da43bfceb21dfd7590efe3ac87ef59243fdae521dff7650efebb2877fdd543bfceaa1dfd7550efe3aa87ef59143f7aa8a1fbe4350effbaac37f1d561bfee6b0dfc735877eb1ac37fddb51bfaeda8f7e65d47beb2ea3ef5d351f7ac9a8dfe73d46feb9ea3dfd4f51efaa7a8dff76546febb2a3df99551efacaa8fbd64546ffb9aa37f1cd51efea6a8f7d53547fab0aa3fdd4551bfeed98dfd76cc6ffbae637f9d731bfaeb98dfc75cc7deb2663f798f31fbac798dff764c6febb2637fdd531bfcea98dfd754c6fe3aa63ef59131fbcc698fdd634c7fab0a63fd54531fee6298cfd7614edeba0a77d5c453bf2e029ded7290f5eb22c36f5d351 else 0xb8810c52e2044045884cca185122cf81451338b814d1054ca1464ca0c6107062e131c74ca0cb1f84c41411d3284107062e131921010c1038152147146493046144043045cf8485cd2e031b2045e13187045192e131c1144cf8486c850784c5c811784c5e004850454861c504500d8cb285a228f21411a3152106163172181141485244140052e231a31471840460464a32451401814b88c71061528c1186c850441b21630450780071011780071400470e3880e011c6047e050051c58a30451470408b88c76078c00458c14802458c11c0245c81243c818c91011f8005163052e001468f2e011450441784a31b20450e3c81e051454840441471011054a31c1163c85044078485105001e128c61054a3045c858c11050860781c6142047106e070c31c48861431e2184184e071031c60c11622441462f88811a20460c5e222c41538811051a2cf81062010c5889181142e3315314188614408b044162e0a4c548b043cc61384811862f2e05145c811841534811041c64f84811c52d2044cc54b8101181c85244172e0b105c930440451b84b31864b8cc4045c931850454b84c51c64d2e0514be12045178cd211210b044045cb84c52120c50450c0181138485238485044e070c5045045183e03c85045a034850450c718b4b81471722c11020490c1140244e070c1245c85043e03c812452321411031520461411444b88c60cd0451850c4486103c811841470634861851b28c1143072146163045c86147052184c81146103101184040e071010891c40450381c514d0c11c50811f88c5063489101152e0c8c6152243147e123231b20c90c7e1218c0c60721788c50018c9132141e231414b81441411d20388c7e12143140e128c5007192e03181cb8144343141100078144c811788c51c54b80031830052441528c1101152e0a8c61720788c50cd141107e1218a0c6047e122a31858d20441411d2e23185ca30440728c9101172e231471410c11c64b80c68d20430784a3107e12043172e050431440c10cb4b80451722f814614bcb804514b2720451722f80c40861f80c5c86e090c5beb5ee2f1d76aba35c8ae156dab615a7ad01656b1f1682c355f0aec2222b6959cab955caa84c00a8c23ea9e94d0a5652228c943aa0b4b927e53d49d54e01110f429ae4cb26052e49604a8a4fd26691e48623e91c48d045f22b)
def g247H9 (j : Nat) : Nat := (if j<2 then (if j<1 then 0x3e6c0003d7400000001cca00000000000000035528000000000000005a3a0000000000060cc92a00000000000002ae000038b661e5210f4a29e10000000000000004e559218000000059560000cb9400011ad000000018730000742e00035b12b9db38384878ed800000004a7f7776bb0c62a00000006f4e356f22f5bc00102a17200000000000c23d61000000d03b3f8b097eca8000f66ec98d0ddabd50000000000000000000d7ec00008bb0000000000001448d518f7800000009ae8a9a8c2859cb6072ab348e07b22106d8a900001352a3f20000000000000000003375000000000000000000000000003464f3cd00001e640000000000000000003c7b5deee638000000000000001cde801d116dabe59060000e4e200010c500006a0a4b600007f9800000001bab800070daaf3c000000000000000000758c21e2071800069bef4a60000d026a962aca00000000000da0200003c5fe7600000003ba7800023db7c8c000000000000000000514f34d800000003bae0000c56c0000000da00ae040580000000081cc11a800012b00000000522f000027e00000000000000000001068000000035b3000000d8c8f0000106600000000435399764f000000002293000000032b98000f67000008b5918400000003371e60913cf2caef676afef6654a6ac9380000001443fd91800000000003fc90a4f8924000000000000000000207e8000739400000006bcee4a520a00000cce000000008948000444193e39078000909c0000000000045b3936eb97f923d023c0a51578000902f738f80791256d6c00000000000ec4800000000000000151ffb77d1b28d53a07c00041469458000000036bbc23000039b480000000ce3c000000024d22e700000000d7ae0002427adec00000000000000000011d74000000034f80003cdc1a8331460000000000094be732c0000000c754880400000000000000000069c400000000a5e8000e58672e74431cd8415c000383a8000410fbdd800070c7570a0003f3be2ec000088c400013c80000bd300000000000000000005874eace9088000595c1788fb7096900002a042d6c000000062b2000000023830000000000000006312e47e6bff48d10bee20c00000000000000000011e3d2070dc000000000000000010410003440c004814025308104f04328318200814000b64738a1c00432023cc0852c400008f04b00b01f0c51001400c80881414011002440411000020c921a0070820c63c50000a03011c870018818016400000114000a0800002550860830021431820051411c70804000820001030000452800400810270401000010461430c10830061192c03cd1051100127001836860022401460423800c00400400020020422c61492402800890040c00c24040021c32811810cf0010440470000470c200a else 0xdb00000000274cc90c0000000000000000000000f60e00004233164af4370d91b380000001620a0b50000000000000004b5d83068244000790a80ee685079080000000ac09108c0fe0000eae199c8000000176b609900003792cccc00073a3a2d0cc90ca6ae0000019f40c9e800000000000d490000927e4a3dd1b25f9428675f7d2a77b7d11000000006a3d000090eb8603afc7eacc86cd9f8000000000030922621bdca00000000f30c04c708c00000000000000180f7b9960a558080482b34e4cf8fc15702b1e2472642c00021d301d80002eac0000e04a0000000000000000000000726b0001480fb8c000041f4e27400000000e5b834d5b5000040d200006cf80f685ed8b6f2f6cf3786e607bace65284c756000000071ce000149f400000002dae000018800000001ef5000000000000000000048aa000000000004afd00000b700000000e3f5cbdc000000000000000000000000000002468000054354de8da1a6d3000000011a0482b00006e308a5000000000003435dde994fc0001f70cf27ed6600025634af438506058000596500000000000392ed25be3add2ae19f749b6d54000096d000000000000000cedb27f80000000000000000005139000000011f10000a3c000000000000000000008a7000000000000000620ad690e2680003a3f00005bac0000b75326a00000000000e6fc000000048f0d1f249e800018dc30ca000000000000000c5c40000000000000000005af127120001c3f00000000000000000000000000000015270001d7b8000000015ae8d83cce628718fc049800000000000000000000000000000000000000ab2000000000001116000000000000001af740005b720000c8e19680000000141d8924000000000002df6800000000000000000090c7e8498588a7977b800002d3aa8c000000000003b7f00000002a7fa0a1c75800005c7797f00014f040002105000000028d58000000000000000000000000010218000000000000006d83551d85de46fef9a46dd6405c3e000011c868fb9a8fba88047e76b98228fb0001b7bc000000000000001cda7004cf0f6a1a179ee05c1300000000590072382695931000000017ccf61e8acab2d220e00004ac70000c76491200000001e3200000000c06800000000000559d0189b1b4e7c0001add00000000000000009040000000000000000000c29800000004b9b6ad400039e600000000000251800004e730d6400036d80001091a0c100003c71d5e00007057600006b981702ee104308600006294848e0000dae7847c40a00000004c37a11c6a81d410000a583296c2cb000000014ab40000000000000000000000e22a00027a9c9346df00000b4180005de7b5900000000000150c51f653da00001937c8b800000000fa80000000976becc40000000000045bc00000) else (if j<3 then 0x115400010f8396400000001c08b92b0000b1bae1f40004506e49c0002cf28000000000000000000000148cd5d893bb00019e7630e000043cc000255f6be4d115e70c0000000019f556800040a0000027a33e956d0a4e60000000000000018bcadbddabcfb6ecaa400028d7000000029158000c4f7e20787e536300002bec0006a50222400000006bd050320001110800000000000f6f800000000003bd4c0ab00010894de98000000000000000000e43cc04935cbd890766000300500007b1a0003956274b0000000000031d77031c037778237700015e3fd9d636de26d65e3ddee3ef00000003ae768b893c200000005bd916f2000192593b8119aa468545025981d14109a1ca97500018910c6200007a1ac61b044faa1772200000001b4400000000000030594e49ef0000000000000000000092a0001e6b00000000d796000000052a862c2000081073490000000013780000000000000009c70000fc88904e309a0ad4014000000000000000a69800050a600000000265954caae80000000000000000000597e5a200018c9009f0001ad94000018c2079f6f80003ba7969df61bcd82ad610920000d3ab55b000000004320e8f563400000000000c69a0000000486700000000000000000000000000067dcdaa0002d8fa227d1780000c8680006016e4e88f9839466a800000000000000049b537b7758c0b2a30ea37662eb57be96000032aa000000004eac661000048980000000f4dc000080a5e2900006f6e65911b787bee6c5b97317411508c9400071f203ea0bfc0000000785d2b2c0004e84076800000002342a16800000006b17000000000007bbe5e32f93b07c000054168b557c42cbe000000021ab534f0001d0a40003434464e63649dca32d972c0001417b1881bd400038ffa967f4ff47200001b0be00c00031a631a300000003c2d8976000000000001e1f00000000803800000011a04000297bf630a92400072d3e56c000032b0400000000018258000a6f800033876b290000a8b8b454930000000000000000000165880004abb0000000000000000000029c00000000000000248b0000a02b6eff6af0000000000021f280000000000000000000000586c0000000860cadd800e69cf922866500000000711acc4e98e7e5320377e82eae303d9cb84254000498500006cb0000203e000000034e4800000000002ecc80000001a48923be4b316f1829243d00004450000000000000000000000000000000e51c000000000012ad000000000001ae880000000b61e00005e2f37d900600039c3c8bea2aa000000051b3000085000000000f32a00004798000d55c00004d0799a000000039dd60a22e48d1300007ba0000000017100000b532c5e8000000000000000000000000004388000000000012e10000700200008 else (if j<4 then 0x46b3a980000000000073820000cc67870000063260000000000000006c6c000000000000000000000083e80000000000054b80001d51994900016f600a8f276000000034cb339ec36a00000004ac0401ca3c800000006f960000000000000000001c2400000000000397100000001038400014f904b4c9140000000834c0000000000004e1be6c000000000000000000000095450e4000072dd0000000356d000000000000000000000000000000799d0000000000003030001c0cc0000000d7ce063c00000000001c157ed648ea0000000000000000000000042f185d000007d800000000001d6880000000000000000003ef2000000000000b61000000000006af5703400000007ac5999ba740000000000000000000178200000002e6baf8cf33000035f18000320800000000000c6c80b2542a5b5723738a78000312c55a8000000000001133c6e8000000000000000000589600000000368dd240000000000065f00000000000031cd4d9e0000000000016a00000000191ba50a032c000024ae348000000000000000000246a8000472a000000031dd34a20001fc800008a7e0000000787b942c043800002ea00008b30000000052a40000500632e296a0000000000000000000000386013000000000292f0000000000059e23256e1040000000e584a6d8000000067dd0f49159800000000000000000000002f180000000515a0000000000000000000000000064680000a0fd09300006f280000000826200000000000000000000000000000000000000000b32000000000000000000000001871c7d2d358000000000000000000000000013431e6600000000000095c80000000000000001f70001c1e03bbe0f73e6a00000007ae9000000000000000b3c81dec0de7a5d172e0000000000000008f58000000032a7ae930bc8000512e000043f8000456aa4250c8ef6e31956c331e880000000c5200000000000000037b900000000474800000000001e56800000000001c0300001295e33c0000545e14557878cbf1d6f6ff00012b980002555c4d16ea70f5800003b80000000702dc0608b8c00038580000000000000000000000151b80000000000118880000001c50800066e904540000000000000000000000270c00000001c7a0000000000013700000f2e4000366fa0854129e09c5080000b51a000000000003db4f6780006cca34cc30e23cb2755523200000000bc774c99b640000000553a47a487fb261000000000003c7843f60c0400001df943a00000004288000000000000000000000033b880008866000314dfbc0c1d260c8437538bb2f800030d38000906a00000000000e43882320838bb654446d68c5bc0ed49782faef6a000000000000c578000000002c8000000000000000000000000008e0099d8000f2dc000103c8 else 0x203b0000000000000000000e134000295e996d0a5c000000000010931507736800017b5b0ea3da3ca1c00008fe8000f9015e458bf6f6c0000000000067d3000061139f30000000000004695009b185c63792bc8a5f2218318c4d8000000017c4000122d0000000392f714b000000000006b4b0001204000001060000ae680000000f2c000000000000c69400031d0800000006ac00000000000000000000000d09503780000000975e000361d80007682000000042ebd3b1ebc19720000d8fa000000041af00e00000000000015200000000000000000000000000063540000affd0f542ba8a9c000000082c60000d8a705ad8dece63053130d41ce000000039a252fbe4463400000307400000001f9e00008e94000220736600000955f037470c000155880000000000356216de000048ec000000099fae5cc000000000000000f9911d1a17e000352169a824c000000000000046401319206d5d6be5e0c4099db12000055a1144800000000000b0d0000e5de0000da2800039ba00000005f0d0000c3b8437e7b2000000000007e5200000000000000000000000447e024a7c20000000132a6384ee28000582a0001afa2176ed53ca5704dc0000000f72400008898000137e000000065b0000000000000000ce7000000000000000000000007fc40da40000c670000000071e8000530e15cf9c040000000b64d8e2217080004db7c4a34ef54ba00000002cf880000000a144000273f58480dac0003430541bd6f7cc5f99b00000002217800011662481a3880006e2aa36e5c6a0e300003d5199b68c5d00200023bd32020000000079021d641b400019908000000000024af8000068c2a44000313c00008279cb30000c611eec9c3950080000e6040004170f61547a8000000000011c5c4f80afa0001ab7b9678000957f05b000000c1c6e3088f9de157efeeb553b514aeedf68e0000d6fe2150001a1845db80002ca800000000000000000021800a06c1b06d780002013b0b846a4e1aaf48773fa24a042155f0000bd000000000000078881a9e03f00000003c5d0000a48200000000000d38b0504000528152710c7559ab213c33200000000000000142014c380005640000206a51a1caac00000000000d976a87c000047cc6de0000000000000000002c68d2770000000000052740000000000048b50000ec580000000000000b000001ef00001cb000000000000000000000000001c4740000000d15200000007b5866780003d5900ac000000000000000000000000000000000000028f6000000000000000221900000000000093b567daa70000235f950182700000000727c0002ef478e5867b63bc0000000000000035c98845f5f0)))
def g247D10 (j : Nat) : Nat := 0x1cc2c0c55e26208a2c4c35cb1308b2c4c31486bc1463065818a71606216581881960620b030c43c0723823bda0bb4b8a8f05e22110542a0a803fd64ff98ffd63ff94ffd53ff14ffe43ff50ffd61ffd47fd51ffcc7fd31ef993bd64
def g247H10 (j : Nat) : Nat := (if j<1 then 0x21bc0000007820001c7c000000000000196600079c40000000000002c20000b15000000000000039e4000000000119800000000000000000000000001104c0f00000000000000000001128000000000000107ed1380000f00009d68d2b00200063480004a800000000000000000000d9400000000000000000000000001e44000000000000000000039948da00080439ab8400000000000911e8b000132572e000000561c4b9c520000001c9c0000000000000000000000000000052c38e9865eae817800000068671e800000000000000000000007860000000000000000000000000000000000005068000000842000000000000065880000016747550001909c6e000796f09b02b0001a58000641c680000000000696800352a000a240b2100a0000000000000e7741ab6b00000000000000000000b2fe2dc0000000000002c32e800000003ef2b4844180000016180003174000000463800087800000021680000000000000000000000000000077c00000000000000000002a8e000000108e194031543cb2c000000000000142c0000000000000000a4e043c000bc50000002d2400000000000000000000000001795a8a8001656000d925b0c00000000000034c60000002eac00000000000030aa0000000000001a7b3218001565e9300045ec000000000000000000000000000000006098000000000000000284a0000005e08000000a540000000eab000000000000065780010d6000000000000000000000000000000000000000000c4c82d4001fc400051fc000e9e31a3241a800000001184000a3956200000014040000000000000000447c00000000020840012670d41de0806000000000000000000000000018bf000000083488c00000000014750000c5800147685df5a943ee4fe1d92f884945950a8000000000308a4c00000000000002c140004a48000000000000000000000000000000000000000000000000000000296d97a000000000000000000034fa0006070003496000c306b488a139d0000000000e49ec518c0000000004dcbb5a6000000000354e000a928000000000b360000000000000000098a68f0007d5c000f4c000000000000095692f59602c00000000000b1e52f7958001ba733e00034980000000000000000000000000000000000028180000000003744000000000000000000000000000000000000000000b52800000000000039ceb5e000000000000000080f57180013560000000000fb599d8000d3a00000034a0000000000000061c0000000000000000000000000000000000008f446400051280000000007338000000114800348e00000000000000000000000b3f21d9448001ce4000b0a000108c0000006028220206231000813341302031006060000050200010303164112 else 0x76ec000000fc18000000c1c00000000000000000000000e2d642800000000035180012fa00000049a243600046100000016acc1c02680000008bf00000002c60000000000e379d0108b5a22510000000000000000000000000000000000000000000000000000000000000075835364e00000000000000000000000149d91a00000000000000000000003178000000000000000000000000000007516a04000000ac04d84001e0b00000000004450006d140000000000000001aa100000000000b8000501c001577b8080000000000000002d3000000000000000000000000000000b0300000000002c5800000000000000000000000000000001c2c0000000774acc00000000014120000003b78000000209bd83d4b95c800000101761b50a1f1e00000038b9d740000000000000000000780800049f00008fc000000b206334001e8a000000000000000000000000000000003d3600000079c000000000000000000a900000000000000001ee4000f7fed80000000000929b244eb2000bdc0000000000dc400022474a44678002941857d198cf400000000000020c41aab22000316800084beacf51c00)
def g247D11 (j : Nat) : Nat := 0x5061ff
def g247H11 (j : Nat) : Nat := 0xa31e000001e000da0000001ca1d003a801d2da8000000000000000000000188000017737000039200b1802e9820000000000013b8f8c79d100000000d85600e0c218
def g247L : Nat → Packing
  | 5 => (4,6,4,0,0,0,0,g247D5)
  | 6 => (232,5,4,0,0,8,0,g247D6)
  | 7 => (1107,4,4,0,0,12,0,g247D7)
  | 8 => (1009,3,4,0,0,14,0,g247D8)
  | 9 => (212,2,4,0,0,13,0,g247D9)
  | 10 => (15,1,4,0,0,9,0,g247D10)
  | 11 => (1,0,4,0,0,0,0,g247D11)
  | _ => emptyPacking
def g247I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 12 0 7 2 1 g247H6
  | 7 => lookupWord 55 844 4 13 8 1 g247H7
  | 8 => lookupWord 273 5479 4 16 11 1 g247H8
  | 9 => lookupWord 259 2605 6 15 10 1 g247H9
  | 10 => lookupWord 58 877 4 13 8 1 g247H10
  | 11 => lookupWord 5 57 3 9 4 1 g247H11
  | _ => fun _ => none
def g247 : Forest := ⟨247,11,fun i => g247Y[i]?.getD (0,0),g247C,g247A,g247L,g247I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P5_0 : block g247 5 0 4=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g247B5 : block g247 5 0 4=true := g247P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P6_0 : block g247 6 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P6_2 : block g247 6 2 48=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P6_50 : block g247 6 50 48=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P6_98 : block g247 6 98 48=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P6_146 : block g247 6 146 48=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P6_194 : block g247 6 194 38=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g247B6 : block g247 6 0 232=true := (@block_merge g247 6 0 98 134 (@block_merge g247 6 0 2 96 g247P6_0 (@block_merge g247 6 2 48 48 g247P6_2 g247P6_50)) (@block_merge g247 6 98 48 86 g247P6_98 (@block_merge g247 6 146 48 38 g247P6_146 g247P6_194)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P7_0 : block g247 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P7_1 : block g247 7 1 48=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P7_49 : block g247 7 49 48=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P7_97 : block g247 7 97 11=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P7_108 : block g247 7 108 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P7_156 : block g247 7 156 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P7_204 : block g247 7 204 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P7_252 : block g247 7 252 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P7_300 : block g247 7 300 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P7_348 : block g247 7 348 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P7_396 : block g247 7 396 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P7_444 : block g247 7 444 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P7_492 : block g247 7 492 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P7_540 : block g247 7 540 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P7_588 : block g247 7 588 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P7_636 : block g247 7 636 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P7_684 : block g247 7 684 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P7_732 : block g247 7 732 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P7_780 : block g247 7 780 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P7_828 : block g247 7 828 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P7_876 : block g247 7 876 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P7_924 : block g247 7 924 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P7_972 : block g247 7 972 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P7_1020 : block g247 7 1020 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P7_1068 : block g247 7 1068 39=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g247B7 : block g247 7 0 1107=true := (@block_merge g247 7 0 492 615 (@block_merge g247 7 0 204 288 (@block_merge g247 7 0 97 107 (@block_merge g247 7 0 1 96 g247P7_0 (@block_merge g247 7 1 48 48 g247P7_1 g247P7_49)) (@block_merge g247 7 97 11 96 g247P7_97 (@block_merge g247 7 108 48 48 g247P7_108 g247P7_156))) (@block_merge g247 7 204 144 144 (@block_merge g247 7 204 48 96 g247P7_204 (@block_merge g247 7 252 48 48 g247P7_252 g247P7_300)) (@block_merge g247 7 348 48 96 g247P7_348 (@block_merge g247 7 396 48 48 g247P7_396 g247P7_444)))) (@block_merge g247 7 492 288 327 (@block_merge g247 7 492 144 144 (@block_merge g247 7 492 48 96 g247P7_492 (@block_merge g247 7 540 48 48 g247P7_540 g247P7_588)) (@block_merge g247 7 636 48 96 g247P7_636 (@block_merge g247 7 684 48 48 g247P7_684 g247P7_732))) (@block_merge g247 7 780 144 183 (@block_merge g247 7 780 48 96 g247P7_780 (@block_merge g247 7 828 48 48 g247P7_828 g247P7_876)) (@block_merge g247 7 924 96 87 (@block_merge g247 7 924 48 48 g247P7_924 g247P7_972) (@block_merge g247 7 1020 48 39 g247P7_1020 g247P7_1068)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P8_0 : block g247 8 0 48=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P8_48 : block g247 8 48 42=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P8_90 : block g247 8 90 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P8_138 : block g247 8 138 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P8_186 : block g247 8 186 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P8_234 : block g247 8 234 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P8_282 : block g247 8 282 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P8_330 : block g247 8 330 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P8_378 : block g247 8 378 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P8_426 : block g247 8 426 46=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P8_472 : block g247 8 472 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P8_520 : block g247 8 520 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P8_568 : block g247 8 568 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P8_616 : block g247 8 616 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P8_664 : block g247 8 664 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P8_712 : block g247 8 712 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P8_760 : block g247 8 760 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P8_808 : block g247 8 808 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P8_856 : block g247 8 856 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P8_904 : block g247 8 904 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P8_952 : block g247 8 952 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P8_1000 : block g247 8 1000 9=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g247B8 : block g247 8 0 1009=true := (@block_merge g247 8 0 520 489 (@block_merge g247 8 0 234 286 (@block_merge g247 8 0 90 144 (@block_merge g247 8 0 48 42 g247P8_0 g247P8_48) (@block_merge g247 8 90 48 96 g247P8_90 (@block_merge g247 8 138 48 48 g247P8_138 g247P8_186))) (@block_merge g247 8 234 144 142 (@block_merge g247 8 234 48 96 g247P8_234 (@block_merge g247 8 282 48 48 g247P8_282 g247P8_330)) (@block_merge g247 8 378 48 94 g247P8_378 (@block_merge g247 8 426 46 48 g247P8_426 g247P8_472)))) (@block_merge g247 8 520 240 249 (@block_merge g247 8 520 96 144 (@block_merge g247 8 520 48 48 g247P8_520 g247P8_568) (@block_merge g247 8 616 48 96 g247P8_616 (@block_merge g247 8 664 48 48 g247P8_664 g247P8_712))) (@block_merge g247 8 760 144 105 (@block_merge g247 8 760 48 96 g247P8_760 (@block_merge g247 8 808 48 48 g247P8_808 g247P8_856)) (@block_merge g247 8 904 48 57 g247P8_904 (@block_merge g247 8 952 48 9 g247P8_952 g247P8_1000)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P9_0 : block g247 9 0 7=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P9_7 : block g247 9 7 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P9_55 : block g247 9 55 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P9_103 : block g247 9 103 24=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P9_127 : block g247 9 127 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P9_175 : block g247 9 175 37=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g247B9 : block g247 9 0 212=true := (@block_merge g247 9 0 103 109 (@block_merge g247 9 0 7 96 g247P9_0 (@block_merge g247 9 7 48 48 g247P9_7 g247P9_55)) (@block_merge g247 9 103 24 85 g247P9_103 (@block_merge g247 9 127 48 37 g247P9_127 g247P9_175)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P10_0 : block g247 10 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P10_2 : block g247 10 2 13=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g247B10 : block g247 10 0 15=true := (@block_merge g247 10 0 2 13 g247P10_0 g247P10_2)
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
theorem g247G : graphValid g247 (boundsBefore K127) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low247 : Lower true (varsX 247) (graphGoal 247) 12 := lower_forest (g:=g247) (i:=0) (hints:=1348) (before_sound K127 V127) g247G g247T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K247 := extendKnown K127 12 [(247,[]),(254,[48])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V247 : Known true K247 := extend_ok (m:=247) V127 low247 (by decide +kernel)
def g255Y : Array (Bits × Bits) := #[(0x24680143c40c20e071ffe3e50061c20290,0x24200140400c2000704d20c40060420080),(0xf8054780618018103f049e0300883845727c91,0x544a4699148182504d22b80881845527890),(0x46781081fc081fc018e03c0401c05056cc9c,0x6682081c4481c401ae13c8401805052c498),(0x878000fe002fe0001f003fe4000106184092,0x70000a2000820000d0032c4000104104010),(0x38000700003000001fffc0181312d81ca668,0x1800010000308082520d80080180900c8628),(0xf8c0001800003fffffe000001626668ce5122b,0xfef09259102237c39ae0080012326688a50223),(0x700001fffffc0000000000018b20ca921f902,0x30000165c3b81010c80000010381809213802),(0xffffffe00000000000000000114a8f12830165,0xfce09348000006021000000003020602800145),(0x0,0x0)]
def g255C : List ColumnInfo := [(8,0,247,0,12),(1,0,254,0,12),(54,0,201,0,7),(214,0,41,0,4),(180,2,73,0,4),(102,0,153,0,7),(128,0,127,0,11),(194,0,61,0,7),(15,32,208,0,4),(166,0,89,0,7),(148,0,107,0,7),(36,0,219,0,11),(109,0,146,0,4),(226,4,25,0,4),(6,0,249,0,11),(118,0,137,0,4),(201,0,54,0,4),(59,0,196,0,4),(34,0,221,0,11),(55,0,200,0,4),(38,0,217,0,9)]
def g255A : List (List Nat) := [[],[48],[33,100]]
def g255D7 (j : Nat) : Nat := 0x20100c0b80d967b2ec5a9e1d75593c5865d756499160064
def g255D8 (j : Nat) : Nat := 0x8081a0205f0fc00206068080606098201008060502fc00800826255434331172417006f67a2e85985d564f2ef62d4f0ebaac965dec5a9e1d755934bbc3f42ca2eab25979b7aa57560064f2e32ebab22c00c9cf865d9264580193db0bab24c8b00327171975d59160064
def g255H8 (j : Nat) : Nat := 0x5200000
def g255D9 (j : Nat) : Nat := 0xf0680c082787c00d02080d02787c00317c3e001810401f87c004101a04060702067801a04140905088602f0f80062787c0030c0608081e08080808080807f004204281c2210320be008010502f80180410220c0a7993dc8871f2721a75d15330129420f0360c01d48d1d44206000fdde85985d564bdbe89965d664bdde85985d564e5f6a7875d564e5fe1d945d564bdde85945d564edeaa57560064ede6a57560064efc65d9160064adde85985d664a5fe9d865d664e2f619765d264a5f69e985d564a5fe9d985d564adde85985d564afc6879760064e5e65d7560064cfce5d9160064cfc65d9160064edc5d59160064ef86499160064
def g255H9 (j : Nat) : Nat := 0x62000000000000039c0000003000000000000000003200024400000001053180000000000000000088c0079800000000000000000000c2000002040000000000000014000007
def g255D10 (j : Nat) : Nat := 0x508e1e0040d1a98343c1387800c72902e1e003041a278780200c508e1e0041008240c20403e1e00f110b87800c4e1e0030c20082787800c605e1e00313ac281f87800c603080834100ca420529e1e003102a0b87800c502e1e003111787800c40204080d9a083030ce00782102787802820086e1e0090210081387802024629eee1e00314140bb89baf87800c8e1e00807021787801c08404e0070210178010300859bd2823543c82cfc0f9386794e91c31f26a0ca91b2f45bcac14525c46c840f91d435c5e0a911c1dc2a02a07a0a815017000fbecb2eb327df66175593efb28baac977d96a1175bbfcb308baedf619845d7eef22c22eb7bd94a19749ffcbb0d324ff661769933fb0ebb4c9b7d985d664dbec32eb326ef61974993b7aecba4c99ff9761d64dbf4c2eab26df66175593aff0ebaac99ff875d164edfc3ae8b276f5d9745936fb30ba8c9bfb9760064dfccbb003255f65e845d6edb25422eb7779161175cbfc3aeab272f5d9745932fb2ac38c937d985d464cbec3aea326dd5d5811936f2eac00c9bf19160064
def g255H10 (j : Nat) : Nat := 0x5000000014380e00000000d240000000088c4200058200000000000000000000000000000000060c03c0060e000000000000000000068b0000000050100000000000000000001d3000000005cc0000000030500000000791000000000000000000000000050800000c0600000000000e3400000000003050000000000000090800000000000000000003a830662a099a0000000000000000000000000000793128000000000000000005200000000000519a401
def g255D11 (j : Nat) : Nat := 0x14970e00628a0faf0e0063078587003142824daf0e00638a0e9b5e1c00c74c14502c38018e170e0120851010282c38048f1b0e004261c1c85080b70a0faf0e006405c380502142830f87002194a60f87002182e1c00850a1416bdc9b0e01e40a0e9b761c1ac190154824dbb0e0064074d870021410515ad361c1c81938700704209c380382142e1c0084cc170021224c197e0ee5c134b644bad64aa74d2901081e036e5e49d8fd1a823c3684404408811000ffe865d3ff61974ffd76993ffe1d64ffd87593ff5d164f7e845d7df61175bfd869d2ffe1974dfd765d2ff61e64bfd86993df5d664fbd74992ffe1d64bfd87593df5d564fbe74593ef5d164bfd87193df5d4649fd87192df61464bf581192fe60064
def g255H11 (j : Nat) : Nat := 0x2438000000458000e8d806a65a3c00000123bc64000001040c7f600078c8c00000000000000000000000142fd06854000000000000000000000000003c0800283fa5aa0800000281e414003c1bc8584c001a41447812c0386ce8400000085206000000002400340c000001076654000000000028000001c4800000000000203400107345c00000288000088843286800042000000020848890c0
def g255D12 (j : Nat) : Nat := 0x1468600852850ab1a182e22616180216b9850a182e1c65058600862c91a182e1b7aa21150a803ff3a7fd74ffcc9ff593fe3277d75
def g255H12 (j : Nat) : Nat := 0xe8200000000c300000000000000000000000002090000000000000000000000000000000000006120000000000000000000000000000000000000000000000000000000a1c0000000000000000000000000007a4000003a00000000000000000000000000000e3c0500182800000000a44000000000000000093200000000000000000000000000000000000000293e094200000000000000000ea600000000104c5000000001a4000000000000000000019300070c0000000000000000000457000034000000016040000000000000000c1e000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000306000000000000000540000000000000000b06000000000000000000000000087000a1600000000da80000000000000000000000000000000011180000000000000000c000000000012e0018b0000000000000000000000000000000000000000000000000000000000000000000000000000002
def g255D13 (j : Nat) : Nat := 0x19610385ff
def g255H13 (j : Nat) : Nat := 0x9786000200000b400708000049dd4000030d000000000000000
def g255L : Nat → Packing
  | 7 => (2,6,5,0,0,5,0,g255D7)
  | 8 => (9,5,5,0,0,8,0,g255D8)
  | 9 => (21,4,5,0,0,10,0,g255D9)
  | 10 => (36,3,5,0,0,11,0,g255D10)
  | 11 => (26,2,5,0,0,11,0,g255D11)
  | 12 => (6,1,5,0,0,8,0,g255D12)
  | 13 => (1,0,5,0,0,0,0,g255D13)
  | _ => emptyPacking
def g255I : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 1 9 0 7 1 2 g255H8
  | 9 => lookupWord 2 59 0 10 4 2 g255H9
  | 10 => lookupWord 6 131 1 11 5 2 g255H10
  | 11 => lookupWord 9 101 6 12 6 2 g255H11
  | 12 => lookupWord 7 287 1 11 5 2 g255H12
  | 13 => lookupWord 1 25 0 9 3 2 g255H13
  | _ => fun _ => none
def g255 : Forest := ⟨255,13,fun i => g255Y[i]?.getD (0,0),g255C,g255A,g255L,g255I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P7_0 : block g255 7 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P7_1 : block g255 7 1 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B7 : block g255 7 0 2=true := (@block_merge g255 7 0 1 1 g255P7_0 g255P7_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_0 : block g255 8 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_1 : block g255 8 1 6=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_7 : block g255 8 7 2=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B8 : block g255 8 0 9=true := (@block_merge g255 8 0 1 8 g255P8_0 (@block_merge g255 8 1 6 2 g255P8_1 g255P8_7))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_0 : block g255 9 0 12=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_12 : block g255 9 12 8=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_20 : block g255 9 20 1=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B9 : block g255 9 0 21=true := (@block_merge g255 9 0 12 9 g255P9_0 (@block_merge g255 9 12 8 1 g255P9_12 g255P9_20))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_0 : block g255 10 0 11=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_11 : block g255 10 11 22=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_33 : block g255 10 33 3=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B10 : block g255 10 0 36=true := (@block_merge g255 10 0 11 25 g255P10_0 (@block_merge g255 10 11 22 3 g255P10_11 g255P10_33))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_0 : block g255 11 0 4=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_4 : block g255 11 4 16=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_20 : block g255 11 20 6=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B11 : block g255 11 0 26=true := (@block_merge g255 11 0 4 22 g255P11_0 (@block_merge g255 11 4 16 6 g255P11_4 g255P11_20))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P12_0 : block g255 12 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P12_1 : block g255 12 1 5=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B12 : block g255 12 0 6=true := (@block_merge g255 12 0 1 5 g255P12_0 g255P12_1)
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
theorem g255G : graphValid g255 (boundsBefore K247) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255R : Impossible true graph 13 nineInputs.toFinset := by
  rw [show graph = targetOf g255 by decide +kernel]
  exact root_index (g:=g255) (top:=13) (i:=0) (before_sound K247 V247) g255G g255T (by decide) (by decide +kernel)

def flatValue (x : Fin 8 → Bool) : Bool := decide (∃ i < ([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem flat_correct : ∀ x : Fin 8 → Bool, nineEdge x = flatValue x := by decide +kernel

def monoWitness : List Gate := [⟨.or, [0, 3]⟩, ⟨.or, [7, 8]⟩, ⟨.or, [2, 4]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [8, 11]⟩, ⟨.or, [1, 9]⟩, ⟨.or, [5, 7]⟩, ⟨.or, [9, 10]⟩, ⟨.and, [12, 14]⟩, ⟨.and, [3, 0]⟩, ⟨.and, [4, 13]⟩, ⟨.and, [6, 15]⟩, ⟨.or, [16, 17]⟩, ⟨.or, [20, 18]⟩, ⟨.or, [21, 19]⟩]

theorem monoWitnessBasis : ∀ g ∈ monoWitness,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [monoWitness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem monoWitnessCorrect : ∀ x : Fin 8 → Bool,
    Circuit.eval ⟨monoWitness, 22⟩ (List.ofFn x) = flatValue x := by
  decide +kernel

theorem lower_with_not (gates : List Gate) (o : ℕ)
    (legal : PEqualNP.MetaComplexity.FanInTwo ⟨gates, o⟩)
    (hnot : ∃ g ∈ gates, g.op = GateOp.not)
    (comp : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = flatValue x) :
    15 ≤ gates.length := by
  have low := binaryLower ⟨gates, o⟩ legal
    (funext fun x => (comp x).trans (flat_correct x).symm) g255R
  obtain ⟨g, hg, ho⟩ := hnot
  have lt : gates.countP (fun g => !isNot g) < gates.length := by
    rcases Nat.lt_or_ge (gates.countP (fun g => !isNot g)) gates.length with h | h
    · exact h
    · have eq := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length h) g hg
      simp [isNot, ho] at eq
  change 14 ≤ gates.countP (fun g => !isNot g) at low
  omega

end PEqualNP.Outside.L_meta_52652

open PEqualNP.Outside.L_meta_52652 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_52652 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o legal _oneNot computes
  by_cases hnot : ∃ g ∈ gates, g.op = GateOp.not
  · have large := lower_with_not gates o (fun g hg => ⟨by
      rcases (legal g hg).1 with h | h | h <;> simp [h], (legal g hg).2⟩) hnot computes
    have hw : monoWitness.length = 15 := rfl
    exact ⟨monoWitness, 22, monoWitnessBasis, by omega, monoWitnessCorrect⟩
  · refine ⟨gates, o, ?_, le_rfl, computes⟩
    intro g hg
    obtain ⟨ops, hlen⟩ := legal g hg
    refine ⟨?_, hlen⟩
    rcases ops with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact False.elim (hnot ⟨g, hg, h⟩)

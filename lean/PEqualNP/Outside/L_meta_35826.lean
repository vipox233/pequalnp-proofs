import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_35826.Core7
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
def graph : Sig := 0xfffffffffffffffefffefffaffeeaa00fffffffffffffffefffefffaffeeaa00fffffffffffffffefffefffaffeeaa00fffffffffffffffefffefffaffeeaa00
def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
 (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 4) || (x 3 && x 4) || (x 0 && x 5) || (x 2 && x 5) || (x 3 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 4 && x 6) || (x 5 && x 6)
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
 (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 3 &&& x 4) ||| (x 0 &&& x 5) ||| (x 2 &&& x 5) ||| (x 3 &&& x 5) ||| (x 0 &&& x 6) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 5 &&& x 6)
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

def target (x : Fin 7 → Bool) : Bool := decide (∃ i < ([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)
def smallCircuit : Circuit := ⟨[⟨.or, [1, 0]⟩, ⟨.or, [3, 2]⟩, ⟨.or, [5, 4]⟩, ⟨.or, [0, 6]⟩, ⟨.or, [3, 7]⟩, ⟨.or, [6, 5]⟩, ⟨.or, [3, 9]⟩, ⟨.and, [12, 8]⟩, ⟨.or, [6, 4]⟩, ⟨.and, [13, 10]⟩, ⟨.and, [15, 11]⟩, ⟨.or, [16, 14]⟩, ⟨.or, [18, 17]⟩], 19⟩

theorem witnessMonotone : ∀ g ∈ smallCircuit.gates,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [smallCircuit,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ⟨Or.inl rfl,by decide⟩ | exact ⟨Or.inr rfl,by decide⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem witnessCorrect : ∀ x : Fin 7 → Bool, smallCircuit.eval (List.ofFn x) = target x := by
  decide +kernel

theorem witnessSize : smallCircuit.gates.length = 13 := rfl

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

def sevenInputs : List Sig := vars 127
def sampleSeven (r : Row) (i : Fin 7) : Bool := bit r (sevenInputs.getD i.val zero)
theorem sevenList : List.ofFn (fun i : Fin 7 => sevenInputs.getD i.val zero) = sevenInputs := rfl
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

def lowRow (i : Fin 7) : Row := Fin.ofNat 512 (1 <<< ([3, 4, 5, 0, 0, 0, 0] : List Nat).getD i.val 0)
def highRow (i : Fin 7) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< ([3, 4, 5, 0, 0, 0, 0] : List Nat).getD i.val 0))

set_option maxHeartbeats 1000000 in
theorem allSevenRequired :
    (∀ i : Fin 7, bit (lowRow i) graph ≠ bit (highRow i) graph) ∧
    (∀ i j : Fin 7, i ≠ j →
      bit (lowRow i) (sevenInputs.getD j.val zero) =
      bit (highRow i) (sevenInputs.getD j.val zero)) := by decide +kernel

theorem physicalSigned (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x)=target x) :
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
  have idx (a : Sig) (ha : a ∈ sevenInputs) : ∃ i : Fin 7, sevenInputs.getD i.val zero = a := by
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
    (lower : Impossible true graph 11 sevenInputs.toFinset) (gates : List Gate) (o : Nat)
    (fit : ∀ g ∈ gates, (g.op=GateOp.and ∨ g.op=GateOp.or ∨ g.op=GateOp.not) ∧ g.inputs.length≤2)
    (correct : ∀ x : Fin 7 → Bool, (Circuit.mk gates o).eval (List.ofFn x)=target x) :
    ∃ (gs : List Gate) (out : Nat), (∀ g ∈ gs, (g.op=GateOp.and ∨ g.op=GateOp.or) ∧ g.inputs.length≤2) ∧
       gs.length≤gates.length ∧ ∀ x : Fin 7 → Bool, (Circuit.mk gs out).eval (List.ofFn x)=target x := by
  classical
  by_cases big : 13 ≤ gates.length
  · exact ⟨smallCircuit.gates,smallCircuit.output,witnessMonotone,(by simpa only [witnessSize] using big),witnessCorrect⟩
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

def paidSliceChoices (d : Sig) (pool : List Sig) : List Choice → List Choice
  | [] => []
  | c :: hist =>
    if availableB true d pool (choiceVal c) then paidSliceChoices d pool hist
    else c :: paidSliceChoices d (choiceVal c :: pool) hist

def zeroSliceOK (m s : Nat) : Bool :=
  let fixed := m - s
  let moves := fixRows fixed 0
  properB (graphGoal s) && (movedWord moves (subcube fixed 0) == one &&
    checkMap moves (vars m) (graphGoal m) (vars s) (graphGoal s))

theorem zeroSlice_sound {m s l} (ok : zeroSliceOK m s = true)
    (prior : Lower true (vars s) (graphGoal s) l) :
    Slice true (vars m) (graphGoal m) (subcube (m - s) 0) l := by
  simp only [zeroSliceOK, Bool.and_eq_true, beq_iff_eq] at ok
  exact slice_correct ok.2.2 ok.2.1 (proper_of _ ok.1) prior

def mixedPairs (support hints : Nat) : List (Sig × Row × Row) :=
  (selected support).map fun (i, w) =>
    let j := (hints >>> (4 * i)) &&& 15
    let r : Nat := if j < 9 then 1 <<< j else 0
    (w, Fin.ofNat 512 r, Fin.ofNat 512 (r ||| (1 <<< i)))

def mixedColumnOK (m z o q support hints L base : Nat) : Bool :=
  let ms := fixRows z o
  let free := colFree m z o
  let G := movedWord ms (graphGoal m)
  let xs := mixedPairs support hints
  let count := (xs.map Prod.fst).toFinset.card
  properB G && checkMap ms (vars m) (graphGoal m) (vars free) G &&
    (movedWord ms (subcube z o) == one) &&
    (if q = 0 then checkEssential G (vars free) xs && decide (L ≤ count - 1)
     else properB (graphGoal q) &&
       checkLift (fixRows (colFree free q 0) 0) G (vars free) (vars q) (graphGoal q) xs &&
       decide (L ≤ base + count))

theorem mixedColumn_sound {m z o q support hints L base : Nat}
    (prior : Lower true (vars q) (graphGoal q) base)
    (ok : mixedColumnOK m z o q support hints L base = true) :
    Slice true (vars m) (graphGoal m) (subcube z o) L := by
  let ms := fixRows z o
  let free := colFree m z o
  let G := movedWord ms (graphGoal m)
  let xs := mixedPairs support hints
  change (((properB G && checkMap ms (vars m) (graphGoal m) (vars free) G) &&
    (movedWord ms (subcube z o) == one)) && _) = true at ok
  simp only [Bool.and_eq_true, beq_iff_eq] at ok
  apply slice_correct ok.1.1.2 ok.1.2 (proper_of _ ok.1.1.1)
  intro p bank hr ha
  have h := ok.2
  by_cases hq : q = 0
  · simp only [hq, if_true, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.2.trans (lower_count (proper_of _ ok.1.1.1) xs h.1 p bank hr ha)
  · simp only [hq, if_false, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.2.trans (lift_ok h.1.2 (proper_of _ ok.1.1.1) (proper_of _ h.1.1) prior p bank hr ha)

theorem mixedBaseZero : Lower true (vars 0) (graphGoal 0) 0 :=
  fun _ _ _ _ => Nat.zero_le _

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

abbrev Bits := BitVec 1024
abbrev Signals := Bits × Bits
abbrev Decor := Sig × Signals

def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def pairSig (r s : Fin 1024 → Row) (a : Sig) : Signals := (ofRows r a,ofRows s a)
def properPairs (T : Sig) (r s : Fin 1024 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 1024 r s (pairSig r s) := by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩
def faithful (r s : Fin 1024 → Row) (x : Decor) := x.2 = pairSig r s x.1
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

def asRow (cols : Nat → Bits) (i : Fin 1024) : Row :=
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
theorem asRow_bit (cols : Nat → Bits) (i : Fin 1024) (j : Fin 9) :
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
 (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 3 &&& x 4) ||| (x 0 &&& x 5) ||| (x 2 &&& x 5) ||| (x 3 &&& x 5) ||| (x 0 &&& x 6) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 5 &&& x 6)
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 1024) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then v j.val else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · simpa [vertex,hh] using asRow_bit v i j
  · simp [vertex,hh,bit_zero]
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 1024) :
    bit (asRow v i) (graphGoal m) = (liftGoal m v).getLsbD i.val := by
  have pos (j : Nat) (hj : j<9) : (vertex m j).getLsbD (asRow v i).val = ((if m.testBit j then v j else 0) : Bits).getLsbD i.val := bit_vertex m v i ⟨j,hj⟩
  simp only [bit,graphGoal,liftGoal,BitVec.getLsbD_and,BitVec.getLsbD_or]
  simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide),pos 6 (by decide)]
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
    if (rs ||| column d z.2) != BitVec.allOnes 1024 then true else
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
  have be : ((restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 1024) = false := by
    simpa using sep
  change (if (restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 1024 then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
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

def compactNext (path : Nat) (ws : List Decor) (hist : List Choice) :
    List Decor × List Choice :=
  let a := ws.getD (path &&& 31) defaultDecor
  let b := ws.getD ((path >>> 5) &&& 31) defaultDecor
  let d := (path >>> 10) &&& 3
  (ws ++ [dbin d a b], hist ++ [(d, a.1, b.1)])

def walkCompact : Nat → Nat → List Decor → List Choice → List Decor × List Choice
  | 0, _, ws, hist => (ws, hist)
  | depth + 1, path, ws, hist =>
    let next := compactNext path ws hist
    walkCompact depth (path >>> 12) next.1 next.2

theorem walkCompact_faithful (depth path : Nat) (ws : List Decor) (hist : List Choice)
    {r s} (base : ∀ v ∈ ws, faithful r s v) :
    ∀ v ∈ (walkCompact depth path ws hist).1, faithful r s v := by
  induction depth generalizing path ws hist with
  | zero => exact base
  | succ depth ih =>
    apply ih
    intro v hv
    rcases List.mem_append.mp hv with hb | hz
    · exact base _ hb
    · obtain rfl := List.mem_singleton.mp hz
      exact faithful_bin _ (faithful_get base _) (faithful_get base _)

def rowWires : List Decor → Nat → List Decor
  | [], _ => []
  | v :: bank, mask =>
    if mask.testBit 0 then v :: rowWires bank (mask >>> 1)
    else rowWires bank (mask >>> 1)

theorem rowWires_faithful (bank : List Decor) (mask : Nat) {r s}
    (base : ∀ v ∈ bank, faithful r s v) :
    ∀ v ∈ rowWires bank mask, faithful r s v := by
  induction bank generalizing mask with
  | nil => simp [rowWires]
  | cons v bank ih =>
    have hv := List.forall_mem_cons.mp base
    unfold rowWires
    split
    · exact List.forall_mem_cons.mpr ⟨hv.1, ih _ hv.2⟩
    · exact ih _ hv.2

def compactPool (m : Nat) (domain : Sig × Nat) (hist : List Choice) : Option BoundPool :=
  materialize true (vars m) (paidSliceChoices domain.1 (vars m) hist) domain.1 domain.2

theorem compactPool_sound {m : Nat} {domain : Sig × Nat} {hist : List Choice} {pool : BoundPool}
    (slice : Slice true (vars m) (graphGoal m) domain.1 domain.2)
    (ok : compactPool m domain hist = some pool) :
    ValidPool true (vars m) (graphGoal m) pool :=
  materialize_sound slice ok

abbrev CompactGrid := Nat × Nat × (Nat → Bits) × (Nat → Bits)
def CompactGrid.mask (g : CompactGrid) := g.1
def CompactGrid.top (g : CompactGrid) := g.2.1
def CompactGrid.pos (g : CompactGrid) := g.2.2.1
def CompactGrid.neg (g : CompactGrid) := g.2.2.2

abbrev CompactTable := (Nat → Nat) × (Nat → Nat → Nat) × (Nat → Nat → Nat) ×
  (Nat → Nat → List Nat) × (Nat → Nat → List Nat)
def CompactTable.count (t : CompactTable) := t.1
def CompactTable.path (t : CompactTable) := t.2.1
def CompactTable.live (t : CompactTable) := t.2.2.1
def CompactTable.picks (t : CompactTable) := t.2.2.2.1
def CompactTable.bucket (t : CompactTable) := t.2.2.2.2

def chartAt (g : CompactGrid) (t : CompactTable) (k i : Nat) :=
  let bank := walkCompact (g.top-k) (t.path k i) (rawDecor g.mask g.pos g.neg) []
  (rowWires bank.1 (t.live k i), bank.2)

def wordsAt (g : CompactGrid) (t : CompactTable) (k i : Nat) :=
  (chartAt g t k i).1.map Prod.fst

abbrev Domains := Array (Sig × Nat)
abbrev Perms := Array (List Nat)

def selectedHistory : List Choice → Nat → List Choice
  | [], _ => []
  | a :: rest, mask =>
    if mask.testBit 0 then a :: selectedHistory rest (mask >>> 1)
    else selectedHistory rest (mask >>> 1)

def poolList (m : Nat) (dom : Domains) (h : List Choice) (picks : List Nat) :=
  picks.filterMap (fun j => dom[j % dom.size]?.bind (fun d => compactPool m d (selectedHistory h (j / dom.size))))

theorem poolList_valid {m dom h picks} (valid : ∀ d ∈ dom, Slice true (vars m) (graphGoal m) d.1 d.2) :
    ∀ pool ∈ poolList m dom h picks, ValidPool true (vars m) (graphGoal m) pool := by
  intro pool hp
  obtain ⟨j,_,hj⟩ := List.mem_filterMap.mp hp
  cases e : dom[j % dom.size]? with
  | none => simp [e] at hj
  | some d =>
    simp only [e,Option.bind_some] at hj
    exact compactPool_sound (valid d (Array.mem_of_getElem? e)) hj

def applySwaps : List Nat → List Sig → List Sig
  | [], xs => xs
  | p::ps,xs => xs.map (movedWord ((p::ps).map swapRows))

theorem applySwaps_valid {T k xs} {p : List Nat}
    (ok : autoOK T (p.map swapRows).reverse = true)
    (ih : Impossible true T k (List.toFinset xs)) :
    Impossible true T k (applySwaps p xs).toFinset := by
  cases p with
  | nil => exact ih
  | cons a p =>
    have := rotate_excluded ih (((a::p).map swapRows).reverse) ok
    simpa only [List.reverse_reverse,applySwaps] using this

def linkedCandidates (g : CompactGrid) (t : CompactTable) (perms : Perms) (k tag : Nat) :=
  (t.bucket k tag).filterMap (fun code =>
    let name := code / perms.size
    if name < t.count k then
      perms[code % perms.size]?.map (fun swaps => applySwaps swaps (wordsAt g t k name))
    else none)

theorem linkedCandidates_valid {g t perms k}
    (autos : ∀ p ∈ perms, autoOK (graphGoal g.mask) (p.map swapRows).reverse = true)
    (prev : ∀ i < t.count k, Impossible true (graphGoal g.mask) k (wordsAt g t k i).toFinset) :
    ∀ tag xs, xs ∈ linkedCandidates g t perms k tag → Impossible true (graphGoal g.mask) k xs.toFinset := by
  intro tag xs hx
  obtain ⟨code,_,he⟩ := List.mem_filterMap.mp hx
  dsimp only at he
  split at he
  next small =>
    cases eq : perms[code % perms.size]? with
    | none => simp [eq] at he
    | some p =>
      simp only [eq,Option.map_some,Option.some.injEq] at he
      subst xs
      exact applySwaps_valid (autos p (Array.mem_of_getElem? eq)) (prev _ small)
  next => contradiction

theorem cachedLiveSize {u target k S} (h : Live u target k S) : S.card ≤ k+1 := by
  induction h using Live.ind with
  | stop hp => simp
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    omega

abbrev NodePool := BoundPool × List Sig × List Sig × Nat

def cacheOnePool (u : Bool) (front : List Sig) (p : BoundPool) : NodePool :=
  (p, front.filter (fun a => !(availableB u p.domain p.wires a)),
    p.wires.map (masked p.domain), front.countP (isMaskedConstant p.domain))

def maskedAvailable (u : Bool) (d : Sig) (pool : List Sig) (a : Sig) : Bool :=
  let m := masked d a
  m == zero || m == d || pool.any (fun v => v==m) ||
    (u && (let c := masked d (neg a); pool.any (fun v => v==c)))

def cachedPoolCut (u : Bool) (a : NodePool) (k : Nat) (rest : List Sig) (op : Choice) : Bool :=
  let (c,missing,bank,maxCon) := a
  if c.bound + maxCon + 1 ≤ k + c.paid then false else
  let z := choiceVal op
  let con := c.bound + (z::rest).countP (isMaskedConstant c.domain)
  if con ≤ k+c.paid then false else
  let extra := !(maskedAvailable u c.domain bank z)
  (decide (k+c.paid+extra.toNat < con) &&
   missing.all (fun w => !(rest.contains w))) &&
    (!extra || (allowedB u op.1 && (!missing.contains op.2.1 && !missing.contains op.2.2)))

theorem cachedCut_ok {u p k rest op front}
    (sub : ∀ w ∈ rest, w ∈ front) (ha : op.2.1 ∈ front) (hb : op.2.2 ∈ front)
    (ok : cachedPoolCut u (cacheOnePool u front p) k rest op = true) :
    scalarPoolCut u p k rest op = true := by
  let miss := front.filter (fun a => !(availableB u p.domain p.wires a))
  let extra := !(availableB u p.domain p.wires (choiceVal op))
  have know (w) (hm : w ∈ front) (hn : w ∉ miss) : availableB u p.domain p.wires w = true := by
    by_contra h
    apply hn
    apply List.mem_filter.mpr
    exact ⟨hm, by simpa using h⟩
  dsimp only [cachedPoolCut, cacheOnePool] at ok
  split at ok
  · contradiction
  split at ok
  · contradiction
  change ((_ && miss.all (fun w => !(rest.contains w))) &&
    (!extra || (allowedB u op.1 && (!miss.contains op.2.1 && !miss.contains op.2.2)))) = true at ok
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', List.all_eq_true] at ok
  change ((_ && rest.all (availableB u p.domain p.wires)) && (!extra || choiceOK u p.domain p.wires op)) = true
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', List.all_eq_true]
  refine ⟨⟨ok.1.1, ?_⟩, ?_⟩
  · intro w hw
    apply know w (sub w hw)
    intro no
    have contra := ok.1.2 w no
    simpa [hw] using contra
  · rcases ok.2 with h | ⟨allowed, ah, bh⟩
    · exact Or.inl h
    · right
      simp only [choiceOK, Bool.and_eq_true]
      exact ⟨allowed, know _ ha (by simpa using ah), know _ hb (by simpa using bh)⟩

def cachedClose (u : Bool) (pools : List NodePool) (links : Nat → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) : Bool :=
  pools.any (fun p => cachedPoolCut u p k rest op) ||
    (let ws := choiceVal op::rest; (links (keySet ws)).any (sameWords ws))

theorem cachedClose_sound {u raw T} {pools : List BoundPool} {links k rest op front}
    (pValid : ∀ p ∈ pools, ValidPool u raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → Impossible u T k (List.toFinset xs))
    (nd : (choiceVal op::rest).Nodup)
    (sub : ∀ w ∈ rest, w ∈ front) (ha : op.2.1 ∈ front) (hb : op.2.2 ∈ front)
    (ok : cachedClose u (pools.map (cacheOnePool u front)) links k rest op = true) :
    Impossible u T k (choiceVal op::rest).toFinset := by
  simp only [cachedClose,Bool.or_eq_true,List.any_eq_true] at ok
  rcases ok with ⟨c,hc,cut⟩ | ⟨w,hw,eq⟩
  · obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hc
    exact scalarPoolCut_sound (pValid p hp) nd (cachedCut_ok sub ha hb cut)
  · rw [sameWords_sound eq]
    exact lValid _ _ hw

abbrev cached_NodeContext := Nat × Nat × List Decor × CovPair × List NodePool × (Nat → List (List Sig))
def cached_evalMove (c : cached_NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
  let (cap,n,ws,cov,pools,links) := c
  let len := 1+(n - (if ka then 0 else 1) - (if kb then 0 else 1))
  if len>cap then true else
    let d := !cov.2
    let rs := restCov cov.1 (column d a.2) (column d b.2) ka kb
    if (rs ||| column d z.2) != BitVec.allOnes 1024 then true else
    if !properB z.1 || ws.any (fun v => v.1==z.1) then true else
      let rest := (delTwo ws a b ka kb).map Prod.fst
      cachedClose cov.2 pools links (cap-1) rest (movedChoice op a b)

def cached_moveFront (ws : List Decor) (op : Nat) (a b : Decor) (ka kb : Bool) :=
  (dbin op a b).1 :: (delTwo ws a b ka kb).map Prod.fst
theorem cached_evalMove_sound {u raw T r s ws} {pools : List BoundPool} {links cap a b op ka kb}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a≠b) (hcap : 0<cap)
    (pv : ∀ p ∈ pools, ValidPool u raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible u T (cap-1) (List.toFinset xs))
    (pro : proper (dbin op a b).1) (fresh : (dbin op a b).1 ∉ ws.map Prod.fst)
    (test : cached_evalMove (cap,ws.length,ws,preCov u ws,pools.map (cacheOnePool u (ws.map Prod.fst)),links) op a b (dbin op a b) ka kb = true) :
    Impossible u T (cap-1) (cached_moveFront ws op a b ka kb).toFinset := by
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
  have hsz := cachedLiveSize h
  change child.toFinset.card ≤ k+1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have len : child.length ≤ cap := by omega
  unfold cached_evalMove at test
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
  have be : ((restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 1024) = false := by
    simpa using sep
  change (if (restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 1024 then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
  rw [be,pp,fr] at test
  exact cachedClose_sound (op:=movedChoice op a b) (rest:=rest.map Prod.fst) pv lv ndc (sub.map _).subset (List.mem_map_of_mem ha) (List.mem_map_of_mem hb) test k hk h

def cached_testPair (ctx : cached_NodeContext) (a b : Decor) (op : Nat) :=
  let z := dbin op a b
  let attempt := cached_evalMove ctx op a b z
  attempt false false && attempt true false && attempt false true && attempt true true
def cached_opsOf (u : Bool) : List Nat := if u then [0,1,2,3] else [0,1]
theorem cached_opsOf_mem {u d} (h : allowed u d) : d ∈ cached_opsOf u := by
  rcases allowed_four h with rfl | rfl | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · cases u <;> simp [cached_opsOf]
  · cases u <;> simp [cached_opsOf]
  · simp [cached_opsOf]
  · simp [cached_opsOf]
def cached_testRow (ctx : cached_NodeContext) (a : Decor) (bs : List Decor) :=
    bs.all (fun b => (cached_opsOf ctx.2.2.2.1.2).all (cached_testPair ctx a b))
def cached_testAll (ctx : cached_NodeContext) : List Decor → Bool
  | [] => true
  | a::bs => cached_testRow ctx a bs && cached_testAll ctx bs

theorem cached_all_binary {ctx ws} (h : cached_testAll ctx ws=true) {a b : Decor} (ha : a∈ws) (hb : b∈ws)
    (ne : a≠b) : (∀ d, allowed ctx.2.2.2.1.2 d → cached_testPair ctx a b d=true) ∨
      (∀ d, allowed ctx.2.2.2.1.2 d → cached_testPair ctx b a d=true) := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [cached_testAll,Bool.and_eq_true,cached_testRow,List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | haTail
    · have bm := (List.mem_cons.mp hb).resolve_left (Ne.symm ne)
      exact Or.inl fun d hd => h.1 b bm d (cached_opsOf_mem hd)
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · exact Or.inr fun d hd => h.1 a haTail d (cached_opsOf_mem hd)
      · exact ih h.2 haTail hbTail

theorem cached_testPair_at {ctx a b d} (h : cached_testPair ctx a b d = true) (ka kb : Bool) :
    cached_evalMove ctx d a b (dbin d a b) ka kb = true := by
  simp only [cached_testPair,Bool.and_eq_true] at h
  cases ka <;> cases kb <;> first | exact h.1.1.1 | exact h.1.2 | exact h.1.1.2 | exact h.2

theorem cached_keep_mem {v : List Sig} {w : Sig} (a : Sig) (k : Bool) :
    w ∈ kept k a v ↔ (w=a ∧ k=true) ∨ w∈v := by cases k <;> simp [kept]
theorem cached_mem_delone {v : List Decor} (nd : v.Nodup) (a w : Decor) (k : Bool) :
    w ∈ delOne v a k ↔ w∈v ∧ (w≠a ∨ k=true) := by
  cases k <;> simp [delOne,nd.mem_erase_iff,and_comm]

theorem cached_unique_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
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

theorem cached_kept_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a ∈ ws) (hb : b ∈ ws) (ka kb : Bool) (v : Sig) :
    v ∈ (delTwo ws a b ka kb).map Prod.fst ↔
    v ∈ ws.map Prod.fst ∧ (v≠a.1 ∨ ka=true) ∧ (v≠b.1 ∨ kb=true) := by
  have wn := nd.of_map
  have dn := wn.sublist (delOne_sub ws a ka)
  simp only [delTwo,List.mem_map,cached_mem_delone wn,cached_mem_delone dn]
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact ⟨⟨_,hw.1.1,rfl⟩,hw.1.2.imp (fun ne eq => ne (cached_unique_value nd hw.1.1 ha eq)) id,
          hw.2.imp (fun ne eq => ne (cached_unique_value nd hw.1.1 hb eq)) id⟩
  · rintro ⟨⟨w,hm,rfl⟩,h1,h2⟩
    exact ⟨w,⟨⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,
        h2.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩

theorem cached_binary_front {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (ne : a.1≠b.1) (d : Nat) (ka kb : Bool) :
    (cached_moveFront ws d a b ka kb).toFinset =
      (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
  ext v
  have av := List.mem_map_of_mem (f:=Prod.fst) ha
  have bv' := List.mem_map_of_mem (f:=Prod.fst) hb
  simp only [cached_moveFront,childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    cached_kept_value nd ha hb,cached_keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,dbin]
  by_cases va : v=a.1 <;> by_cases vb : v=b.1 <;> cases ka <;> cases kb <;> simp_all

theorem cached_childTwo_swap {u} (v : List Sig) (nd : v.Nodup) (a b : Sig) (d : Nat) (hd : allowed u d) (ka kb : Bool) :
    (childTwo v a b d ka kb).toFinset = (childTwo v b a (flipOp d) kb ka).toFinset := by
  ext x
  simp only [childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    cached_keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,bin_flip hd a b]
  tauto

theorem cached_node_sound {u raw T r s ws} {pools : List BoundPool} {links cap}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools, ValidPool u raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible u T (cap-1) (List.toFinset xs))
    (checks : cached_testAll (cap,ws.length,ws,preCov u ws,pools.map (cacheOnePool u (ws.map Prod.fst)),links) ws = true) :
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
      (test : cached_testPair (cap,ws.length,ws,preCov u ws,pools.map (cacheOnePool u (ws.map Prod.fst)),links) a b d = true) :
      Impossible u T (cap-1) (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
    rw [←cached_binary_front nd aa bb ne']
    exact cached_evalMove_sound pairs faith nd aa bb (fun e => ne' (congrArg Prod.fst e)) hc' pv lv
      pr fr (cached_testPair_at test ka kb)
  rcases cached_all_binary checks haW hbW ab with hh | hh
  · exact one a b d haW hbW ne ka kb pro fresh (hh d hd)
  · rw [cached_childTwo_swap _ nd _ _ d hd]
    exact one b a (flipOp d) hbW haW (Ne.symm ne) kb ka (bin_flip hd a.1 b.1 ▸ pro)
      (bin_flip hd a.1 b.1 ▸ fresh) (hh _ (flip_flip hd).1)

def compactNode (g : CompactGrid) (t : CompactTable) (dom : Domains) (perms : Perms) (k i : Nat) : Bool :=
  let state := chartAt g t k i
  let ws := state.1
  let words := ws.map Prod.fst
  let pools := poolList g.mask dom state.2 (t.picks k i)
  let links := linkedCandidates g t perms (k-1)
  decide words.Nodup && (!(words.contains (graphGoal g.mask)) &&
    (if k=0 then true else cached_testAll (k,ws.length,ws,preCov true ws,pools.map (cacheOnePool true words),links) ws))

theorem compactNode_sound {g t dom perms k i}
    (pairs : properPairs (graphGoal g.mask) (asRow g.pos) (asRow g.neg))
    (valid : ∀ d ∈ dom, Slice true (vars g.mask) (graphGoal g.mask) d.1 d.2)
    (autos : ∀ p ∈ perms, autoOK (graphGoal g.mask) (p.map swapRows).reverse = true)
    (prev : 0 < k → ∀ j < t.count (k-1),
      Impossible true (graphGoal g.mask) (k-1) (wordsAt g t (k-1) j).toFinset)
    (check : compactNode g t dom perms k i = true) :
    Impossible true (graphGoal g.mask) k (wordsAt g t k i).toFinset := by
  simp only [compactNode,Bool.and_eq_true,decide_eq_true_eq] at check
  have out : graphGoal g.mask ∉ wordsAt g t k i := by simpa [wordsAt] using check.2.1
  by_cases hz : k=0
  · subst k
    intro n hn run
    obtain rfl : n = 0 := by omega
    exact out (List.mem_toFinset.mp (run.1.symm ▸ Finset.mem_singleton_self _))
  · have f : ∀ v ∈ (chartAt g t k i).1, faithful (asRow g.pos) (asRow g.neg) v :=
      rowWires_faithful _ (t.live k i) (walkCompact_faithful (g.top-k) (t.path k i)
        (rawDecor g.mask g.pos g.neg) [] (raw_faithful g.mask g.pos g.neg))
    apply cached_node_sound pairs f check.1 out (poolList_valid valid) (linkedCandidates_valid autos (prev (by omega)))
    simpa only [hz,ite_false] using check.2.2

def chartBlock (test : Nat → Bool) (start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => test (start+n) && chartBlock test start n

theorem chartBlock_at {test start n} (ok : chartBlock test start n = true) (i)
    (a : start ≤ i) (b : i < start+n) : test i = true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [chartBlock,Bool.and_eq_true] at ok
    by_cases h : i=start+n
    · simpa only [h] using ok.1
    · exact ih ok.2 (by omega)

theorem chartBlock_join {test start a b}
    (left : chartBlock test start a = true) (right : chartBlock test (start+a) b = true) :
    chartBlock test start (a+b) = true := by
  induction b with
  | zero => simpa using left
  | succ b ih =>
    simp only [chartBlock,Bool.and_eq_true] at right
    simp only [Nat.add_succ,chartBlock,Bool.and_eq_true]
    constructor
    · change test (start + (a+b)) = true
      rw [← Nat.add_assoc]
      exact right.1
    · exact ih right.2

theorem compactAll {g t dom perms}
    (pairs : properPairs (graphGoal g.mask) (asRow g.pos) (asRow g.neg))
    (valid : ∀ d ∈ dom, Slice true (vars g.mask) (graphGoal g.mask) d.1 d.2)
    (autos : ∀ p ∈ perms, autoOK (graphGoal g.mask) (p.map swapRows).reverse = true)
    (blocks : ∀ k ≤ g.top, chartBlock (compactNode g t dom perms k) 0 (t.count k) = true) :
    ∀ k ≤ g.top, ∀ i < t.count k, Impossible true (graphGoal g.mask) k (wordsAt g t k i).toFinset := by
  intro k
  induction k with
  | zero =>
    intro h i hi
    exact compactNode_sound pairs valid autos (by omega) (chartBlock_at (blocks 0 h) i (by omega) (by simpa using hi))
  | succ k ih =>
    intro h i hi
    exact compactNode_sound pairs valid autos (fun _ => ih (by omega)) (chartBlock_at (blocks _ h) i (by omega) (by simpa using hi))

theorem compactPairs {g : CompactGrid}
    (yes : liftGoal g.mask g.pos = BitVec.allOnes 1024) (no : liftGoal g.mask g.neg = 0) :
    properPairs (graphGoal g.mask) (asRow g.pos) (asRow g.neg) := by
  intro i
  constructor
  · rw [bit_liftGoal,yes,BitVec.getLsbD_allOnes]
    exact decide_eq_true i.isLt
  · rw [bit_liftGoal,no]
    simp

abbrev SliceSpec := Nat × Nat × Nat × Nat × Nat × Nat × Nat

def specDomain (s : SliceSpec) : Sig × Nat :=
  (subcube s.1 s.2.1, s.2.2.2.2.2.1)

def certifiesSlice (m : Nat) (earlier : List (Nat × Nat)) (s : SliceSpec) : Bool :=
  let (z,o,q,support,hints,L,base) := s
  ((q == 0 && base == 0) || earlier.contains (q,base)) &&
    ((z == m-q && o == 0 && L == base && zeroSliceOK m q) ||
      mixedColumnOK m z o q support hints L base)

theorem certifiesSlice_sound {m earlier s}
    (prior : ∀ e ∈ earlier, Lower true (vars e.1) (graphGoal e.1) e.2)
    (ok : certifiesSlice m earlier s = true) :
    Slice true (vars m) (graphGoal m) (specDomain s).1 (specDomain s).2 := by
  obtain ⟨z,o,q,support,hints,L,base⟩ := s
  simp only [certifiesSlice,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq,
    List.contains_eq_mem,decide_eq_true_eq] at ok
  have lower : Lower true (vars q) (graphGoal q) base := by
    rcases ok.1 with ⟨rfl,rfl⟩ | he
    · exact mixedBaseZero
    · exact prior (q,base) he
  rcases ok.2 with ⟨⟨⟨rfl,rfl⟩,rfl⟩,h⟩ | h
  · exact zeroSlice_sound h lower
  · exact mixedColumn_sound lower h

theorem compactDomains_valid {m earlier specs ds}
    (prior : ∀ e ∈ earlier, Lower true (vars e.1) (graphGoal e.1) e.2)
    (ok : List.all specs (certifiesSlice m earlier) = true)
    (matchDs : (specs.map specDomain).toArray = ds) :
    ∀ d ∈ ds, Slice true (vars m) (graphGoal m) d.1 d.2 := by
  subst ds
  intro d hd
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp (List.mem_toArray.mp hd)
  exact certifiesSlice_sound prior (List.all_eq_true.mp ok _ hs)

theorem compactAutos_valid {T : Sig} {ps : Perms}
    (ok : ps.toList.all (fun p => autoOK T (p.map swapRows).reverse) = true) :
    ∀ p ∈ ps, autoOK T (p.map swapRows).reverse = true := by
  intro p hp
  exact List.all_eq_true.mp ok _ (Array.mem_toList_iff.mpr hp)

theorem compactRoot {g t dom perms}
    (pairs : properPairs (graphGoal g.mask) (asRow g.pos) (asRow g.neg))
    (valid : ∀ d ∈ dom, Slice true (vars g.mask) (graphGoal g.mask) d.1 d.2)
    (autos : ∀ p ∈ perms, autoOK (graphGoal g.mask) (p.map swapRows).reverse = true)
    (blocks : ∀ k ≤ g.top, chartBlock (compactNode g t dom perms k) 0 (t.count k) = true)
    (existsRoot : 0 < t.count g.top)
    (root : wordsAt g t g.top 0 = vars g.mask) :
    Impossible true (graphGoal g.mask) g.top (vars g.mask).toFinset := by
  rw [←root]
  exact compactAll pairs valid autos blocks _ (Nat.le_refl _) 0 existsRoot
def readCompactBits (table : Nat → Nat) (start width : Nat) : Nat :=
  let i := start / 4096
  let j := start % 4096
  let low := table i >>> j
  let result := if j + width ≤ 4096 then low else low ||| (table (i+1) <<< (4096-j))
  result &&& ((1 <<< width)-1)

def compactIDsFromBits (bits width : Nat) : Nat → List Nat
  | 0 => []
  | n+1 => (bits &&& ((1 <<< width)-1)) :: compactIDsFromBits (bits >>> width) width n

def samplesP25 : Nat → Bits
  | 0 => 0xbfae
  | 3 => ~~~(0x1128 : Bits)
  | 4 => ~~~(0x2086 : Bits)
  | _ => 0

def samplesQ25 : Nat → Bits
  | 0 => 0x420a
  | 3 => ~~~(0xebfa : Bits)
  | 4 => 0x2830
  | _ => 0

def compactPerms25 : Array (List Nat) := ([[], [67], [48], [48, 67], [64, 67], [64]] : List (List Nat)).toArray

def compactDomains25 : Array (Sig × Nat) := ([] : List (Sig × Nat)).toArray

def compactWords25 : Nat → Nat
  | 0 => 0x7
  | _ => 0

def compactCount25 (k : Nat) : Nat := match k with
  | 3 => 1
  | _ => 0

def compactPath25 (k : Nat) (i : Nat) : Nat := match k with
  | 3 => 0
  | _ => 0

def compactLive25 (k : Nat) (i : Nat) : Nat := match k with
  | 3 => readCompactBits compactWords25 (0 + 3*i) 3
  | _ => 0

def compactPoolIDs25 (k : Nat) (i : Nat) : List Nat := match k with
  | 3 => let v := readCompactBits compactWords25 (3 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords25 (3 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket25 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP27 : Nat → Bits
  | 0 => 0x5ef9f1efddbe0e9a
  | 1 => 0x6cfe360dafc07f24
  | 3 => ~~~(0x6003741843078b4 : Bits)
  | 4 => ~~~(0x80800a0098e060a : Bits)
  | _ => 0

def samplesQ27 : Nat → Bits
  | 0 => 0x21224a0414921a12
  | 1 => 0x1382d13c8a16bf04
  | 3 => ~~~(0x79bf6bb7bebb5af6 : Bits)
  | 4 => 0x8100083200000e0
  | _ => 0

def compactPerms27 : Array (List Nat) := ([[], [48]] : List (List Nat)).toArray

def compactDomains27 : Array (Sig × Nat) := ([(subcube 2 0, 4)] : List (Sig × Nat)).toArray

def compactWords27 : Nat → Nat
  | 0 => 0x4f
  | _ => 0

def compactCount27 (k : Nat) : Nat := match k with
  | 4 => 1
  | _ => 0

def compactPath27 (k : Nat) (i : Nat) : Nat := match k with
  | 4 => 0
  | _ => 0

def compactLive27 (k : Nat) (i : Nat) : Nat := match k with
  | 4 => readCompactBits compactWords27 (0 + 4*i) 4
  | _ => 0

def compactPoolIDs27 (k : Nat) (i : Nat) : List Nat := match k with
  | 4 => let v := readCompactBits compactWords27 (5 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords27 (4 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket27 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP118 : Nat → Bits
  | 1 => 0xdd7efeb1f3b642febf9fcd1adcd9e1921f7e73b26f38a2a68df18a4
  | 2 => ~~~(0x7008030ab31fa00980870125cf06f93d02472c42660e3beb524eec : Bits)
  | 4 => 0xf6bf9f7e6f1388f3fe7ff12e3ff2078096fff1cde1e4208eb37e464
  | 5 => 0xbf3fe5f98f6d30fdf9fb32d5ed35d8216fedbe7c1ee345114f2d318
  | 6 => ~~~(0x10000409470600002013810cad1191a03648b13849a32487cb79134 : Bits)
  | _ => 0

def samplesQ118 : Nat → Bits
  | 1 => 0x2291890c080899a211024305513a04284b0e20a2050085e0ccb1084
  | 2 => 0x705a0108211f098244054414552a900815b090908110c6298da012
  | 4 => 0x960309110606651801494628444d05104f1404040a5680b134e420
  | 5 => 0x40c8198220820f6048818326902c42061ea490141200e1894725108
  | 6 => ~~~(0xeffdffffbafbfffbfdd7ffffffffff7fdffff9ff5fb7ffffffff5be : Bits)
  | _ => 0

def compactPerms118 : Array (List Nat) := ([[], [82], [33, 84], [33, 66, 84], [65], [65, 82], [81, 82, 84], [81, 66]] : List (List Nat)).toArray

def compactDomains118 : Array (Sig × Nat) := ([(subcube 2 0, 5), (subcube 4 0, 5), (subcube 16 0, 5), (subcube 32 0, 5), (subcube 18 0, 4), (subcube 36 0, 4)] : List (Sig × Nat)).toArray

def compactWords118 : Nat → Nat
  | 0 => 0x3dda25a3a7f8011efeb53807c9fd3922c13b4a319a226e853930267df79c04a11186a95a10cec5eadfe0ff07f83fc1fe0ff0486000a1812f3736e61d984261252200a50c0205220089cfb96bea795597f807009fe03fc060a9c65e0882b56ad2b779c683dda58149c86c228f3924ec7884430c4bca1e43ff01fe03fc00b8a313ec0e4e5a569ca191bf17fc00d0c884d4ced290de4d5c95a25a543ff8087345ece9474a3de204ea9e70bf106b624fc968587f8091823333fc013bfff01fe03d9bf1cba0400000020a04000c06cd0a14a13060c920192140991900dff76effefd7efdfbf250b944e513942e50080865211482520149008808802c958527737fc10d7343ff80e977d1ff07f8079ffe0ff0239b3a6022d34a04133551008321403124098325401ffffe0110110068ae11f
  | _ => 0

def compactCount118 (k : Nat) : Nat := match k with
  | 7 => 1
  | 6 => 3
  | 5 => 10
  | 4 => 3
  | _ => 0

def compactPath118 (k : Nat) (i : Nat) : Nat := match k with
  | 7 => 0
  | 6 => readCompactBits compactWords118 (26 + 12*i) 12
  | 5 => let v := readCompactBits compactWords118 (469 + 14*i) 14
    (readCompactBits compactWords118 (433 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | 4 => let v := readCompactBits compactWords118 (1919 + 14*i) 14
    (readCompactBits compactWords118 (1847 + 24*(v >>> 12)) 24) ||| ((v &&& 4095) <<< 24)
  | _ => 0

def compactLive118 (k : Nat) (i : Nat) : Nat := match k with
  | 7 => readCompactBits compactWords118 (0 + 5*i) 5
  | 6 => readCompactBits compactWords118 (62 + 6*i) 6
  | 5 => readCompactBits compactWords118 (609 + 7*i) 7
  | 4 => readCompactBits compactWords118 (1961 + 8*i) 8
  | _ => 0

def compactPoolIDs118 (k : Nat) (i : Nat) : List Nat := match k with
  | 7 => let v := readCompactBits compactWords118 (20 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords118 (5 + 3*(v &&& 7)) (3*n)
    compactIDsFromBits bits 3 n
  | 6 => let v := readCompactBits compactWords118 (156 + 9*i) 9
    let n := v >>> 5
    let bits := readCompactBits compactWords118 (80 + 4*(v &&& 31)) (4*n)
    compactIDsFromBits bits 4 n
  | 5 => let v := readCompactBits compactWords118 (727 + 7*i) 7
    let n := v >>> 4
    let bits := readCompactBits compactWords118 (679 + 4*(v &&& 15)) (4*n)
    compactIDsFromBits bits 4 n
  | 4 => let v := readCompactBits compactWords118 (1985 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords118 (1985 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket118 (k : Nat) (i : Nat) : List Nat := match k with
  | 6 => let d := readCompactBits compactWords118 (183 + 4*(i % 4)) 4
    let off := ((i/4 + d) % 18)
    let v := readCompactBits compactWords118 (199 + 13*off) 13
    if v >>> 5 == (i/104729)%251 then [v &&& 31] else []
  | 5 => let d := readCompactBits compactWords118 (797 + 5*(i % 18)) 5
    let off := ((i/18 + d) % 64)
    let v := readCompactBits compactWords118 (887 + 15*off) 15
    if v >>> 7 == (i/104729)%251 then [v &&& 127] else []
  | 4 => let d := readCompactBits compactWords118 (1991 + 4*(i % 8)) 4
    let off := ((i/8 + d) % 31)
    let v := readCompactBits compactWords118 (2023 + 13*off) 13
    if v >>> 5 == (i/104729)%251 then [v &&& 31] else []
  | _ => []

def samplesP57 : Nat → Bits
  | 0 => 0xbffd3b7dedcc78e
  | 3 => ~~~(0x8103241258c788 : Bits)
  | 4 => ~~~(0x14286d5408da2e6 : Bits)
  | 5 => 0xdbfa64773e9aee0
  | _ => 0

def samplesQ57 : Nat → Bits
  | 0 => 0x40408404440008a
  | 3 => ~~~(0xf77fdded7ffffda : Bits)
  | 4 => 0x162448691095d10
  | 5 => 0x252411a02a95e40
  | _ => 0

def compactPerms57 : Array (List Nat) := ([[], [48], [84], [84, 48]] : List (List Nat)).toArray

def compactDomains57 : Array (Sig × Nat) := ([(subcube 16 0, 4)] : List (Sig × Nat)).toArray

def compactWords57 : Nat → Nat
  | 0 => 0x4f
  | _ => 0

def compactCount57 (k : Nat) : Nat := match k with
  | 4 => 1
  | _ => 0

def compactPath57 (k : Nat) (i : Nat) : Nat := match k with
  | 4 => 0
  | _ => 0

def compactLive57 (k : Nat) (i : Nat) : Nat := match k with
  | 4 => readCompactBits compactWords57 (0 + 4*i) 4
  | _ => 0

def compactPoolIDs57 (k : Nat) (i : Nat) : List Nat := match k with
  | 4 => let v := readCompactBits compactWords57 (5 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords57 (4 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket57 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP115 : Nat → Bits
  | 0 => 0x6efeffad617e97be7f7de5e68eb0b14f6d38fbd878c21f49e5c4
  | 1 => ~~~(0x580162511e3d824012ee4822cf6bbcc011155c94ad39f82afd6 : Bits)
  | 4 => ~~~(0x2040091d4217a0180c0513c609f0c7984424ca4e3677172973e2 : Bits)
  | 5 => 0x773f5f75db91077fbdefd2cb29c08386fcc5d4cff253143fa302
  | 6 => 0x7dffbfdf16e7effdcfb63f967d764e9dd7374f6f063583a25af2
  | _ => 0

def samplesQ115 : Nat → Bits
  | 0 => 0x1121021084810920085446011048081305008850408425414184
  | 1 => ~~~(0x7a7a6dfeeebe24eeddf3b8ec4f5bdf7ca35ddffbdb61da92bfde : Bits)
  | 4 => 0x2048088402162442410108a00500430ca2091100834088128c08
  | 5 => 0x8c2988a2022f608902909b2a5121424f8404482175a883ea002
  | 6 => 0x210002048080084048000000001804000140229000000001250
  | _ => 0

def compactPerms115 : Array (List Nat) := ([[], [81, 64]] : List (List Nat)).toArray

def compactDomains115 : Array (Sig × Nat) := ([(subcube 1 0, 5), (subcube 2 0, 5), (subcube 16 0, 5), (subcube 32 0, 5)] : List (Sig × Nat)).toArray

def compactWords115 : Nat → Nat
  | 0 => 0x41c9f
  | _ => 0

def compactCount115 (k : Nat) : Nat := match k with
  | 6 => 1
  | _ => 0

def compactPath115 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => 0
  | _ => 0

def compactLive115 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => readCompactBits compactWords115 (0 + 5*i) 5
  | _ => 0

def compactPoolIDs115 (k : Nat) (i : Nat) : List Nat := match k with
  | 6 => let v := readCompactBits compactWords115 (13 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords115 (5 + 2*(v &&& 7)) (2*n)
    compactIDsFromBits bits 2 n
  | _ => []

def compactBucket115 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP87 : Nat → Bits
  | 0 => 0x6ecfbfd6950f6237fdfe5b4e6cf1ab101967fdd3e3f62ec71046793388
  | 1 => 0x774fd9fd29d3b447cefbfdb7172673ab6009defd3d9875702ba876a854
  | 2 => ~~~(0x21d0191091db3ef8048209866c2733bf7dee080b699434473bef902ffc : Bits)
  | 4 => 0x7dbfff3df6ff1a8fbfc7ffccfe0f5f0f54e5bb7afd05dfcf01e9b3d63c
  | 6 => ~~~(0x4000005240712000840504c16004b0b50649050b5004fc701e833921c : Bits)
  | _ => 0

def samplesQ87 : Nat → Bits
  | 0 => 0x1132441912b091ca81a063438f115068451d5d1606822cc11872792108
  | 1 => 0x8b4070a54380b1b43c028cd0a10b47453058cb50d0a21c10e2a74a044
  | 2 => 0x21d14b5091721ef5a191309ea543e5e249c5f3e4144322e256d8efd002
  | 4 => 0x2480840080064240806041020420100a0022248a004400a4080825610
  | 6 => ~~~(0x7bff7fffdffaffffebf77ffffffffffeffdfffffbfcf6feffffffff75e : Bits)
  | _ => 0

def compactPerms87 : Array (List Nat) := ([[], [16]] : List (List Nat)).toArray

def compactDomains87 : Array (Sig × Nat) := ([(subcube 1 0, 5)] : List (Sig × Nat)).toArray

def compactWords87 : Nat → Nat
  | 0 => 0x9f
  | _ => 0

def compactCount87 (k : Nat) : Nat := match k with
  | 5 => 1
  | _ => 0

def compactPath87 (k : Nat) (i : Nat) : Nat := match k with
  | 5 => 0
  | _ => 0

def compactLive87 (k : Nat) (i : Nat) : Nat := match k with
  | 5 => readCompactBits compactWords87 (0 + 5*i) 5
  | _ => 0

def compactPoolIDs87 (k : Nat) (i : Nat) : List Nat := match k with
  | 5 => let v := readCompactBits compactWords87 (6 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords87 (5 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket87 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP55 : Nat → Bits
  | 0 => 0x5edfbff5d1d1767fffcfbe6cfd8bd8e89c2ecf6def1b4edc4f9d9155e28be4
  | 1 => ~~~(0x8b01300738546f800882269cda38cc4853fd90140924754c67dd3764893f6 : Bits)
  | 2 => 0x7c3ff37bef84cc87efb9efdbc2f7ac45e11117bfdb96f337d2604223d9b512
  | 4 => ~~~(0x44020600440e4b006000c06a0936860653390248203728213e4d267520cb2 : Bits)
  | 5 => 0x6fefffee766fe6b7f6fe7fe7adb36ff6653395f7f6e377c2b7e4d2675e5eb2
  | _ => 0

def samplesQ55 : Nat → Bits
  | 0 => 0x212142061a2681829411304f011c089102431c4d030382985c050385e08824
  | 1 => ~~~(0x774bfc7c8ef8fb24ceebf695ac5bf781fba5e18b6abf557ea6fe8f704d93fe : Bits)
  | 2 => 0x3c0c5a4104e137592308245541901e728e25f0b9a04c386582c4709d1b102
  | 4 => 0x44824300400602448c04010a401b1002900818268180420a02a84300d1348
  | 5 => 0x1012201140900808600a04b0a2a0b008000420b064a010400282b0320e4690
  | _ => 0

def compactPerms55 : Array (List Nat) := ([[], [33, 84]] : List (List Nat)).toArray

def compactDomains55 : Array (Sig × Nat) := ([] : List (Sig × Nat)).toArray

def compactWords55 : Nat → Nat
  | 0 => 0x1f
  | _ => 0

def compactCount55 (k : Nat) : Nat := match k with
  | 4 => 1
  | _ => 0

def compactPath55 (k : Nat) (i : Nat) : Nat := match k with
  | 4 => 0
  | _ => 0

def compactLive55 (k : Nat) (i : Nat) : Nat := match k with
  | 4 => readCompactBits compactWords55 (0 + 5*i) 5
  | _ => 0

def compactPoolIDs55 (k : Nat) (i : Nat) : List Nat := match k with
  | 4 => let v := readCompactBits compactWords55 (5 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords55 (5 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket55 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP51 : Nat → Bits
  | 0 => 0xbfff3bb9fbda7afa
  | 1 => ~~~(0x142c0b80325a707a : Bits)
  | 4 => ~~~(0x8120880818a52a8 : Bits)
  | 5 => 0xdbfec8beb78a57e8
  | _ => 0

def samplesQ51 : Nat → Bits
  | 0 => 0x404444208a10988a
  | 1 => ~~~(0xeadb95d3bee9647e : Bits)
  | 4 => 0xa11009124282454
  | 5 => 0x24b1215a10ae2760
  | _ => 0

def compactPerms51 : Array (List Nat) := ([[], [81, 64]] : List (List Nat)).toArray

def compactDomains51 : Array (Sig × Nat) := ([] : List (Sig × Nat)).toArray

def compactWords51 : Nat → Nat
  | 0 => 0xf
  | _ => 0

def compactCount51 (k : Nat) : Nat := match k with
  | 3 => 1
  | _ => 0

def compactPath51 (k : Nat) (i : Nat) : Nat := match k with
  | 3 => 0
  | _ => 0

def compactLive51 (k : Nat) (i : Nat) : Nat := match k with
  | 3 => readCompactBits compactWords51 (0 + 4*i) 4
  | _ => 0

def compactPoolIDs51 (k : Nat) (i : Nat) : List Nat := match k with
  | 3 => let v := readCompactBits compactWords51 (4 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords51 (4 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket51 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP119 : Nat → Bits
  | 0 => 0xdedbfeffd7d725ed3d4aaaa4fdfe7ff2ff6da9eebfe7d17dc66b809bb0208a7d4f093154eff7bbfa99ffa3b5eeb8bf4e4c97a6614bd98cfa832c8d0c019e0950fddec9f66789592e75ecb7809c655222054d3f0509e5620
  | 1 => 0xf66bfdb3feee587f4e2702c8fee7bfdf7ef5d6d78f9b7b8e98161e44f1bb540f92900220ffeffd57cf3cbf5bf3e1dcb58666700cbc8f3323b0f23ea21a2020053e6deedbf7b70eb1c4b06a3c7362209932103adeca90144
  | 2 => ~~~(0x403c003210c120366df79a8f008220103035c0e602e441089e1b8ad0f9b3c75d63dbff7e2102001085992c11c230d106f407a469d8cb23b3bab88fbefbbf3dd5c0884242852f1ce466a8bb195867f2fbf75dc25499bf7ec : Bits)
  | 4 => 0xfdb7ff7e7c6bf79efcf49d31ff9ffc7ffe9ff9fc51fc7d95bf0ce6a35fd2e575a1ca0412ff7ef6baf5877cfbb0b773ffb913cc76cc116385fad4cc027a190454adb9d72fbcee5ad06a0bce87d88530107650ca33f54c0e4
  | 5 => 0xef3ffbffb99dee72ffb1d30effffefbff1fbe7276e6ce66b7f991978edc79b8a6520d848fb9fdf952efb7c65cf5fff3a778d878b336ec3d34c89331181c413a21baf3fe38f46a56dba80917b6c78c342898a24f4bb23818
  | 6 => ~~~(0x4000800000e44481c20832000040c0240c9a1040d087005030c142bf5c2982f85a810504a04901208263061a0813e3b0f97c6062f1dc3c3c0c43d031bdc03768d2d8da326c64b39f880c6a6fc7d73123fda2eb7eb65874 : Bits)
  | _ => 0

def samplesQ119 : Nat → Bits
  | 0 => 0x2126010818083210c2a4511b298062030890300b40046380449c01e04252350050a6420a88c62a101b8080447008b04c4f003c017c0090890650007202050a0bb84ac9140398013214843600b80050280e293f010881420
  | 1 => 0x994220e0c10a500e1d0ed33b04168412136612d9094b481414841d20842a4c0446c6c579b635950531408411128882aca1a560254a2a05bc9b2416842548882be0d68d1d595009150942014b042115f021b3accca80104
  | 2 => 0x403d011690412022c9359a8f5810610945a2d34654a143200c0889c08162660461da9b4cd6b4273413201248188c82089532a8a1292215c257e054e093060c42bd52a58d7a108218198620a0b20945251c307d8b6440012
  | 4 => 0x2484090c1800841000b02c446041030004082502721003288011004000508080a1191a064188482240220900011008110a480b081550500100196010420110041b0162a28204840200840024089a60050c04032354c040
  | 5 => 0x10c0128046220084004a24608420840090440030a31094138022220110080010800124b12109d0800048442080400513008c421280d52010880382042008600402a5126284420004820080480422a25240c200749320808
  | 6 => ~~~(0xfbff7ffffffbbff7ebfffffffff5ff7bfdfffffffffffffffdfffbf7db7fffdcfffffffffffffff67ffefefdf9fdbffffffffffffffffffffffffffff77fffcfffffffffffffcbffff9ef6fefeffffffffffffffffedd7e : Bits)
  | _ => 0

def compactPerms119 : Array (List Nat) := ([[], [33, 84]] : List (List Nat)).toArray

def compactDomains119 : Array (Sig × Nat) := ([(subcube 1 0, 8), (subcube 2 0, 7), (subcube 4 0, 7), (subcube 16 0, 6), (subcube 32 0, 6), (subcube 64 0, 5), (subcube 6 0, 5), (subcube 17 0, 5), (subcube 18 0, 5), (subcube 20 0, 5), (subcube 34 0, 5), (subcube 36 0, 5), (subcube 66 0, 4), (subcube 68 0, 4), (subcube 19 0, 4), (subcube 22 0, 4), (subcube 38 0, 4)] : List (Sig × Nat)).toArray

def compactWords119 : Nat → Nat
  | 0 => 0xffef7ffffdfdfdfdefbfffffbffffffdfffdfffdfffdfffdfffdfdffffffbdfdffbd7dfd7fffffbfddfdffbfffffbfedfdffedffffffbfedfdfdffedfdfee42ea626642e632e462626262626261e2616260be42bc42ba42be623e623c623a6238623e61be61be613e613a613e60be60be60be60ba60b8608e428a428a328c628c620a620a620a610a608a604a42cc32ca32ca32ca624a624a61ca61ca612242a432a232a232a222a66222622661a261a66122612660da42dc32da32dc62da62da61da60b632b432b232b232b412b212b662b662b462b462b262b262b062b062b660b660b26084628262d442d242d232d462d262d2325462526252622c42aa42aa32aa22ac62aa62aa324442c242c232c412c462c262c21242621c429a429a329a129c629a629a62121294629262e32c32c32421c12c11a32a32221a12a11a110328323b22a365e2266d1d15b0f25c581c9ffc1e75624deebfc12242c8ff82cd7fe0957ff83fc1c16773770575d612c09ff8042ffe0461bc6400980030048fcab44609af92f1fc37a5ae9a0f397721022001020926282344104e4f64482006727c4820940944470790620291368630790620291360620185525c48b5082024e4f884035ca2a22c2014a2822c20945e45012188c8a102638bc6083cc1147ffffffffffffffffffffffffc65865465065825425864464064843443823423422c93f
  | 1 => 0xe641a20a08199e6081002e67c61882871a718620a1882861020099a452692220651019a88199829e12620206679a9a411e18a0a5a8810009f9a40ea94b9a55cbae6418902519a9f9a42491c42489c710a491986888484080291993ae8409989ae810200a4e640a4eba1198a4e8466293ae640a4ea46838a994a1018b9c608a41e2e642620a2860040c79a11a818a20a1000c799e68818080a0e67c662718809878b9901c660260609f9c661b18408610060284799898850810060319f9981907a60200c799831899a12201199a2869945e62462891a420610200a5e65061020179942222eba040804919975ea5662242904e618a22428626a90a18998890608a22419828818408020798a68206662692228408198a9a488620409a60620198a18290a50400399e9105029040804899901020122664082862041c86e640810200b2664081020499904461e65901e92099962e81020499912684662922122859c879aa8a7e619220200b99e68800399e5ab1862047e72022862260860926071e60d79ca20400a0c64e62040039931d656624a50ba840031e648a40899018a7839c661e2e619024601f98a64620401f98a50404799ea182a198521f2460207e62881986808667ffdffffbffffdfdfdfdfffffffffdffffffffffbffdfffffdffedefffefffffbdfd7dfd7dddedf7fefffefffdfffdfdfffefffefffdfffdfffdff
  | 2 => 0x1611eb25c87158a44a420b5320c218523459e764d7912c36e48b3785480df77090123bf408eff0071a7021be0e0f53169eada1eff00df35a33fff0005381c7193906997ff00870f03c06763ff0064a910e1ff00394c5842e8d3b255ff003c2bc32921283109a8721ea20c2669dfff0039dbff00efecad32d81aa803780ecbadff00ff00b6b447a8ff00ff009025b2b8518c3f92b85f6fe471640f980469ad41ff00911156aec02c9c65501778afff00a0eb223bbe18416039b197274d683b9d8d361d748fbdbf3eb81510a12bc4c782abd221a6151000500282803648d000c1458b100008f0c841000401016061010b180c0822a081000008083060008b0004004041818820001000030389081c30406142860408214f913a14e4b3694d673434c512d3ca6f261c92723248471fbc7051b24645180c5ed14a44ab102c3690bc41eb052c0a900b3f68fbabe4af6cbc8cef53a8ce72b92ae2337c6ddbb684d9235c6d5c3468cfc32f4c6ab10ac1a2fecbcaae90b622d10b01abb0aaaaa0aa5ba886a09a7d09b3a5f6922a3ee8c122c8893218a83a20668031f427ca9e887821d8c7349ba66d41a4867398ee60197a65d216d057394ea513139249a11e4469116a4338fec3cb0e723518ce831b0ba82cc0a2e25288b21e107461bb062c15b04ae0f382f007b81100006209a840804e640a21240798a28898828200420b9a2204012
  | 3 => 0x8438c58238c54648c54438c54238c44658858438858238854438854238658648654648258238254644c58644c58434c58234c54644c54434c54234c4c654c48654c48434c48254c48234c44654c44254c44234c40654c38254c34254c24654c20654c18644c10654c00654858644858434858254858234854434854254854234850654658644658434658254658234654644654434654254654234650654648434644434454434254644254234254224248230c54640c44650c1465874f032a36c72c3c069bda14e2b6d1ef253ae2349fc8ff00e2e57caa949999c1ba1fcd81ff0007130a844e91235b43b3aee2e266de4b493d2343c6479be70967ff00ff00ff0086ba0bde8e57b8acf10471ce800aff00ecb01173b3bec421778fff003e9364377f1c74edff0018519ccf66abff000c20565e977e31e66ba3ef9655dcff009b7b0e076e9fbd19ff00de33704dff00ff00266d14d0b939af5d05e36708ff0020597a2d5bd7009cb9c9a28b6d8919bba510c69a9d837875071679ccff0063d5dd062ba0ff00ff0057c2c9dd7322bac5ccb7ed2ec37fff00ff00ff003a23477dff00ff009a49ff00a8b9706269953c9e6670ff00d1bcff00a1cac3d87a05f4da842f937cff00ff00111256e9eb0b53d15a94ad6f0624a4a587cdccd94c6ed48d76c6ff00eecb7de8ff009e6a2653cd0d6a6bdb88a84aec409a1d5930f6d4397a5
  | 4 => 0x990b122162242c4865899c9123922272440e4899c71338a227100cc400988013800473414e6279c44f39856708ace6159cc891951232a2ce53d90a79214f2329cc853890a71194de429b485368ca633888670a7ce24f9c69f3893e7121ce4439c2573886670c84e3499c493386327220ce1848cb0939212719ace2359ccd1390967212ce17e8cac219582329d4853b0ca751960642c08e6669c63b38476428e4851d9c83839076710ece11c1c2383998a32b14e4629c6c63998a73064650d9c7291965432ca465949c2f3315e271bc4e6789c6b738d6e70adce05b9cab738d6e71adce15b9c2b73856870adce05b9c0091941262824e1049c00a3981232824e1049c10d2161a32c3825879cb0d395c271b84e6339c4673988e7211ce17c9c8bf3904a42894c5139ca253954442a8485508caa33954272a8465519caa23954272a80e56c9c6d9389b27316ce22d9cc373906e710dce10f10a1d2143a32bb4e4599c8b33896670acce11090a21114426288ce5109ca23389ba71b74e62f9c45f384be730fce1648cac91959272324e3649ccf53917412aece45d9c20d2141a32834c5071ca992153232a6ce54c9cad538daa70b54e6299c4533985e70854650a8cae93915e722bce1579c28d2151a32a3425479ca8d3951e7084445cc5464cc4465cc4425cc3465cc3425cc2465cc1465cc1464cc1425c85065c654648c58648c5
  | 5 => 0x2481006acc5334a483356acd2884ad598a19e47b31ccc1c8cf992040420477ee20988eed7b886a1c4231004082cfdc2a3020010800140851004993002fb841448904ac102b5ac101842428512ac4c1840400904004800202000800003b81ee1bb800bdc28d195890409202020410103480c182ee21224062d2346608181060b4020a0c10003dd2154610124028c60110304778a084040229a834608001060d18506047858a0c401ee080770a142820000101d7def6f3fddcef773fd7cfe7fafbbdf6ef7bbedfb5f779fdf67fbddeef77bf5faef77bbddeef77bbddeef77bbddeef77bbdbe5f67f7b9ffd76f37dbe9f5fbbddecf7bbddaefb7db6bdf76f73fddcee7fbdbdf767f7bbecfefbddbedf7d7afb7dbefb9fcfe7f5bbddef9eef77bef9fcfe7f3ddfebf5dbf5edf779fcffaf77ebe7f3f3fcfdde7f3fbbdf6fd9f9fede7fbd9eef77d3eebe7efb7e9fe7e7b3ed7edf7b3f9fdde7f7b9fddfeb3f9ff9f6f77bbebf5fb79fcff4fafd7ebf5f77bdcfef73fbbfcfebdbedfce7f3fddef67be7f9edeef77f9dde7f7bbecffebf5eadf7ebbd9fef67fbdf6fd77b7dd7ede7f3fbbdf67f7b9ffd7ebd59fcff7b3dd7edf7b3f9fef7f2ab2154e7129c65539c4a73894e71290e2539c3272164a71494e173988e538dca70a5ce34b9c4973852e70014c48e9c915390fe70c44e489989123122262440c4899871338e2661444c28
  | 6 => 0x6011a11f7f8008d7bfe00be211a5323dc5fe00032c5737d90c1fe00f915ff803fc00402cff007f801478b98eb1cc97f803fc01fe0000256a4120081426045230030cc800005b20a01186328c0870e55887000c6a2020402036181834c040a4000800e005c700060010000005800600102020c3800045c850604022020870000d819000480800c08d8f62381090a0840348141842a2c580002c380120220b060cb80044c00f0a34c81089c68020480020e0040100043000c2c6b8d71ae35ceb1d51aa7506a0d43a634d68acf39c339660cc198330662ca590320643c518a711610c2382304609c0180300602be37a6f05e0bc376ae7599b23632b5558ab354aa0542a614c298d2aa3146689500a033ea744eb9a134664cc29612c2584b29432624cc919151ea3446b8a312224c40881102204418750a610c1883304a004027eaf21e43c9782ee5d8ba9746e25c03826e2da5b03606c2d61ac35a696cc594b20640c858c319620c4980afa5d2b81702e05c0b856c2d85b4b295cab1550aa5502a0542a6549280500a053c2784f29c138a694c494128a494848c118a2944a7e4f89e93c2760ec9d03a2720e49c33506a0d49a1332644c49822e05c4b49612b0560ac1582b65049d9202424608c911210420850f91e03c0790e11b0368648c11702e05c0ba15625c2c8500a2124208390620a015019024000bb84082801202000920
  | 7 => 0xdb132162e1e199548ae2682824655c133ec13048b3c478ebdec8650933cf25919ebed92e1bc1c21c33a73208cab335d7d8f81bcc2696f8d5e47f801b4ed0c0e921749050641ffe00573441b6ec141b217ff004d0d6eddab569ff007f801438dfe00ff007f803fc0124646474d7e8aea8de8a62a12d3d96e52aacfaff007f800ca6c460c043d7f803fc0079977d00ee49ac69b3a2608d613bfd1934dbaddf7774c53fc00141bd8ba590875b01beaaafa013a861c535a2701308426e446726444436286e3c55fa6c9ff007f8012c2b932eff0023e22aa9161a589260ecf7ba37fe0013e3c865ab074816d965817213a568ac75ff004e67ade9565358e2e554c4e5d1a6d9139c80b45107fc6078f32ff8024125a97d89de4a8c6671da98dff0070c57fc01fe005ab07f80144641ef2ff007f801118274e6d094d01f3fc007e1dff007f802ff65fe0030107f8033b7561321990ff800a4554110ff00038b4c27c2f0c49b672d563a1685aef74431469071e2f9a2444b832c4159fe00c97b5688c1da6593895a841dd66f9b795dc7c0e2cae79274b9b618035569c8e7fe007233ff803a4a16da4e4b7ff80253760725a8bcdeeaed605fe00d6317f80389cb5b78c6b22841bfc00852a9bd4c6d5148da9034c35c4a825e8f7fe00076ea110f894922a9ccaca74286f066a30a5b1d2c36adab71858b3a7f801d8abfe00c679fc69829c7
  | 8 => 0x34051b84e4fe01c5005c6f6697afd70874658499c3d9b1dc82ff801356f1f99062b1a5784b05fe008fb9ad84b0805fe0058087f803a688c2caff002d476eb29fe00deb3fb4ddc6fdfe00ff003a700d6f87d9357ac499772c91fe00dee4e6f31a77eeedcde61ff802634327535d8fff803fc00284e27207b0bc38829b1747143c68e3a5fbf18cc9d37928b589a372761e98a3a7f0cf2812a3cb5bc15180bd166787d53a9f23d0ef5b184b667ec4e0c98b1c3ffb50d14a80dcaf166ade777876604b8d2c8de472373b6474342f2b4255efdf57e0041520fe8a5ea78ecc3bd86010c6bfc49352aa27d255cd44faf1b2e94efb696b9cc73ea397ae20e2d037d3595d1e2944dd7f5706e5516936cf299056f5a4647f305c918fa13921e3cafad2724df7f800918bc07e024b6e22f76d443a04c3924b69a4349a03f2967f800a1210b4b7dd9a4b3b4e385db7a622a3b1da29d90bbf838f716ecab7a2224e90623b364bfd73b26b716ad658b55a1e3d917f800149bacad0b7a14a365eb95c77ff007f801e9af1069411b9f124a5de8da740921aed7c25aa63c324f6272ebf2b2e247d289f8e4c6cc8c16d95fdd5589a93fe00b35c82a50df61fe00ff007f80308de9e0b294542ea3a1a9335f5588d6233fc01fe00af7e7f803fc00560a69c6145c2daa24a8f130cceaea98cd8005f8c870ddcdc3f88865353e7c12da60b680f2c279be7
  | 9 => 0x71dc7d5cd795cd735e56b5cd791ee799e66b9af4b1df635ce6b5d7691dcf31ef5356ecb7a66b1dc7d1f6739ce799e6799e43faaead8f63b8f679cad4fd2d4f55d5756d5d1ef873cc771dc7d1ec77cac771ec7d763284a00a683c1a04f6813da00ae812ba0096813da04f68006a069e8127a009e83af988ba625f9c37e8097a028e8395a027e8113a0e768111a02fe813ba05628321a054a82019c802800b9c3268149a013e805b9c40e71579c35870d7a035880ada0eca32b08cac262b28cac232b0a0342329ba0c6680d4a071e8108a04228088a0136808e90ad68139a05168145a012e80b7a043232c3a050e80c3a019cc8ca0cb9c49890cb9c298a8c99c28cb0c99c098a8c91ca9890870ca9830c904b9828c89cd18a8c89cd10a8869cd10a8469cd04a8c89ca9890869ca9890469ca9888469c99868ca9c998684a9c99828ca9c998284a9c918b0469c918a8469c904b0469c218a8c89c018a8c89c01828ca98a18a8c89899828ca9881888ca9881828ca90b9828ca90a9840ca90a9830c890a9820ca90a9800ca90a8c90868ca9890868ca9880ca8ca9840ca8ca9820ca8ca9800ca88a8c888684a9888461cc8ca8c81ca9890861c99828ca1c49890ca1c298a8c81c28ca8c9fe00e773822c71a829a6aff007f8024b55586eb7b58d276e43900a330027f800a2edfe0077693e5a0615029bde791d5d3ee1997b3f5abd7
  | 10 => 0xff0ff0061b552fb969307ff0e9aff0f84f385c367642000a710f21e664c718e06910d287a4073926812502d01ce04c5464506ce14658645014e00c54645000e14654644c44e00c14650b773561d013d0389254e531f42da42f3b7f027849705e12ff009b28b375693c0f1ec211955f931bb536c718d788051f0a5c8f84b30fe10a59585280a55127854743ff004a6fa715986b101dff005f6dff001e6a460bff00823ac201c589e2106a6e71392f598164ff001b20c549226891535766ff000e04835572093c245033c121f1037873ff00ff00e925ff00f406bf8be40c4317f3727c1a8d16ff005c5b1941ff007362ff001182a223ff00ff00073f313e8767ff00ff000e52f645c57db257814eff00ff00c25e5b60ee37ff008e2b510d0a7b9500ce05ff006c8aff00387cd34f9914a10743765508625031357f5d230e5056b8029d5a878183830647e82228656269034dff00ff00bd63ee30a36c0771ff004e44632abc463d1907794986074cd92c674a6832903bda4b5e29b9875548a33d2b74ff00aa261027e37eff00cb1c0c500528398758020e03c040b0c0003800420117ce1c228100238000414024100538a5294a5294a5294a52b242108421084210842109210842108421084210842108421084210a0000000000000d3e598a4999d7517ce
  | _ => 0

def compactCount119 (k : Nat) : Nat := match k with
  | 9 => 1
  | 8 => 14
  | 7 => 120
  | 6 => 231
  | 5 => 70
  | 4 => 6
  | _ => 0

def compactPath119 (k : Nat) (i : Nat) : Nat := match k with
  | 9 => 0
  | 8 => readCompactBits compactWords119 (16 + 12*i) 12
  | 7 => let v := readCompactBits compactWords119 (1683 + 16*i) 16
    (readCompactBits compactWords119 (1515 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | 6 => let v := readCompactBits compactWords119 (16684 + 19*i) 19
    (readCompactBits compactWords119 (14884 + 24*(v >>> 12)) 24) ||| ((v &&& 4095) <<< 24)
  | 5 => let v := readCompactBits compactWords119 (39037 + 18*i) 18
    (readCompactBits compactWords119 (37309 + 36*(v >>> 12)) 36) ||| ((v &&& 4095) <<< 36)
  | 4 => let v := readCompactBits compactWords119 (44484 + 15*i) 15
    (readCompactBits compactWords119 (44244 + 48*(v >>> 12)) 48) ||| ((v &&& 4095) <<< 48)
  | _ => 0

def compactLive119 (k : Nat) (i : Nat) : Nat := match k with
  | 9 => readCompactBits compactWords119 (0 + 6*i) 6
  | 8 => readCompactBits compactWords119 (184 + 7*i) 7
  | 7 => readCompactBits compactWords119 (3603 + 8*i) 8
  | 6 => readCompactBits compactWords119 (21073 + 9*i) 9
  | 5 => readCompactBits compactWords119 (40297 + 10*i) 10
  | 4 => readCompactBits compactWords119 (44574 + 11*i) 11
  | _ => 0

def compactPoolIDs119 (k : Nat) (i : Nat) : List Nat := match k with
  | 9 => let v := readCompactBits compactWords119 (12 + 4*i) 4
    let n := v >>> 2
    let bits := readCompactBits compactWords119 (6 + 2*(v &&& 3)) (2*n)
    compactIDsFromBits bits 2 n
  | 8 => let v := readCompactBits compactWords119 (887 + 11*i) 11
    let n := v >>> 7
    let bits := readCompactBits compactWords119 (282 + 5*(v &&& 127)) (5*n)
    compactIDsFromBits bits 5 n
  | 7 => let v := readCompactBits compactWords119 (8391 + 14*i) 14
    let n := v >>> 10
    let bits := readCompactBits compactWords119 (4563 + 6*(v &&& 1023)) (6*n)
    compactIDsFromBits bits 6 n
  | 6 => let v := readCompactBits compactWords119 (24657 + 11*i) 11
    let n := v >>> 8
    let bits := readCompactBits compactWords119 (23152 + 7*(v &&& 255)) (7*n)
    compactIDsFromBits bits 7 n
  | 5 => let v := readCompactBits compactWords119 (41032 + 5*i) 5
    let n := v >>> 3
    let bits := readCompactBits compactWords119 (40997 + 7*(v &&& 7)) (7*n)
    compactIDsFromBits bits 7 n
  | 4 => let v := readCompactBits compactWords119 (44640 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords119 (44640 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket119 (k : Nat) (i : Nat) : List Nat := match k with
  | 8 => let d := readCompactBits compactWords119 (1041 + 5*(i % 9)) 5
    let off := ((i/9 + d) % 33)
    let v := readCompactBits compactWords119 (1086 + 13*off) 13
    if v >>> 5 == (i/104729)%251 then [v &&& 31] else []
  | 7 => let d := readCompactBits compactWords119 (10071 + 7*(i % 75)) 7
    let off := ((i/75 + d) % 268)
    let v := readCompactBits compactWords119 (10596 + 16*off) 16
    if v >>> 8 == (i/104729)%251 then [v &&& 255] else []
  | 6 => let d := readCompactBits compactWords119 (27198 + 7*(i % 150)) 7
    let off := ((i/150 + d) % 533)
    let v := readCompactBits compactWords119 (28248 + 17*off) 17
    if v >>> 9 == (i/104729)%251 then [v &&& 511] else []
  | 5 => let d := readCompactBits compactWords119 (41382 + 6*(i % 45)) 6
    let off := ((i/45 + d) % 162)
    let v := readCompactBits compactWords119 (41652 + 16*off) 16
    if v >>> 8 == (i/104729)%251 then [v &&& 255] else []
  | 4 => let d := readCompactBits compactWords119 (44652 + 2*(i % 4)) 2
    let off := ((i/4 + d) % 14)
    let v := readCompactBits compactWords119 (44660 + 12*off) 12
    if v >>> 4 == (i/104729)%251 then [v &&& 15] else []
  | _ => []

def samplesP89 : Nat → Bits
  | 0 => 0x5ff532fedaa69a
  | 3 => ~~~(0x4202ed80a3ed0 : Bits)
  | 4 => ~~~(0x811714681a2ae : Bits)
  | 6 => 0x6ff86d5fad3ae4
  | _ => 0

def samplesQ89 : Nat → Bits
  | 0 => 0x20820512100212
  | 3 => ~~~(0x7affd5fabfffd6 : Bits)
  | 4 => 0xa0050600c0d00
  | 6 => 0x10418088a000c4
  | _ => 0

def compactPerms89 : Array (List Nat) := ([[], [100], [67], [67, 100], [99, 100], [99], [48], [48, 100], [48, 67], [48, 67, 100], [48, 99, 100], [48, 99], [64, 67], [64, 67, 100], [64], [64, 100], [64, 99], [64, 99, 100], [96, 99, 100], [96, 99], [96, 100], [96], [96, 67, 100], [96, 67]] : List (List Nat)).toArray

def compactDomains89 : Array (Sig × Nat) := ([(subcube 1 0, 4), (subcube 8 0, 4), (subcube 16 0, 4), (subcube 64 0, 4)] : List (Sig × Nat)).toArray

def compactWords89 : Nat → Nat
  | 0 => 0x3fc00a5252ebcbdf56bc3bfc04a9bfc0ff00aec315ffc01013e23908b946904802804803e4b7fc011afff002693cd7661f7f6a6a99f565346d97d7513fc07f80d13d0caffc0330eff00ea5d220ff80862964d3fc07f80ff01fe00193fb16ff0136e83957f80cd4bfe002607f80dc65fe014e3d3bb5c71810012293fd7de8059049048025373daff83b4ffe0bb6c84fe5ffe0ff009070fd0060e4f
  | _ => 0

def compactCount89 (k : Nat) : Nat := match k with
  | 6 => 1
  | 5 => 1
  | 4 => 3
  | 3 => 2
  | _ => 0

def compactPath89 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => 0
  | 5 => readCompactBits compactWords89 (18 + 12*i) 12
  | 4 => let v := readCompactBits compactWords89 (197 + 12*i) 12
    (readCompactBits compactWords89 (185 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | 3 => let v := readCompactBits compactWords89 (997 + 13*i) 13
    (readCompactBits compactWords89 (949 + 24*(v >>> 12)) 24) ||| ((v &&& 4095) <<< 24)
  | _ => 0

def compactLive89 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => readCompactBits compactWords89 (0 + 4*i) 4
  | 5 => readCompactBits compactWords89 (30 + 5*i) 5
  | 4 => readCompactBits compactWords89 (233 + 6*i) 6
  | 3 => readCompactBits compactWords89 (1023 + 7*i) 7
  | _ => 0

def compactPoolIDs89 (k : Nat) (i : Nat) : List Nat := match k with
  | 6 => let v := readCompactBits compactWords89 (12 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords89 (4 + 2*(v &&& 7)) (2*n)
    compactIDsFromBits bits 2 n
  | 5 => let v := readCompactBits compactWords89 (43 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords89 (35 + 2*(v &&& 7)) (2*n)
    compactIDsFromBits bits 2 n
  | 4 => let v := readCompactBits compactWords89 (257 + 4*i) 4
    let n := v >>> 2
    let bits := readCompactBits compactWords89 (251 + 2*(v &&& 3)) (2*n)
    compactIDsFromBits bits 2 n
  | 3 => let v := readCompactBits compactWords89 (1041 + 4*i) 4
    let n := v >>> 2
    let bits := readCompactBits compactWords89 (1037 + 2*(v &&& 3)) (2*n)
    compactIDsFromBits bits 2 n
  | _ => []

def compactBucket89 (k : Nat) (i : Nat) : List Nat := match k with
  | 5 => let d := readCompactBits compactWords89 (49 + 3*(i % 2)) 3
    let off := ((i/2 + d) % 10)
    let v := readCompactBits compactWords89 (55 + 13*off) 13
    if v >>> 5 == (i/104729)%251 then [v &&& 31] else []
  | 4 => let d := readCompactBits compactWords89 (269 + 2*(i % 10)) 2
    let off := ((i/10 + d) % 44)
    let v := readCompactBits compactWords89 (289 + 15*off) 15
    if v >>> 7 == (i/104729)%251 then [v &&& 127] else []
  | 3 => let d := readCompactBits compactWords89 (1049 + 1*(i % 3)) 1
    let off := ((i/3 + d) % 13)
    let v := readCompactBits compactWords89 (1052 + 14*off) 14
    if v >>> 6 == (i/104729)%251 then [v &&& 63] else []
  | _ => []

def samplesP121 : Nat → Bits
  | 0 => 0x6fffdac6bbb77dbfa76b233c28f76d75e6298706a92a
  | 3 => ~~~(0x20010a056a81401264438bbab0f04a58e52d378fe9b0 : Bits)
  | 4 => ~~~(0x302828e15e425009266bb755da2a5603687ad427d5e : Bits)
  | 5 => 0x76fbbbaf4c1feff2f2c69910549eb2587fb52c5e7410
  | 6 => 0x7bffe61d77ddf75f5c778ae39138cfeab5c6318949d4
  | _ => 0

def samplesQ121 : Nat → Bits
  | 0 => 0x100801104401042400004800c1006101202000002822
  | 3 => ~~~(0x5feffffaf5ffdd77ffff7edddffdeb7bff7ffffffbb6 : Bits)
  | 4 => 0x342420a10fa10108945104410bd021088451a3d8200
  | 5 => 0x922444021f48802894502890a1c004852151a3e1010
  | 6 => 0x48008a0800041410000241004408822050000004184
  | _ => 0

def compactPerms121 : Array (List Nat) := ([[], [99], [48], [48, 99], [96, 99], [96], [84], [84, 99], [84, 48], [84, 48, 99], [84, 96, 99], [84, 96]] : List (List Nat)).toArray

def compactDomains121 : Array (Sig × Nat) := ([(subcube 16 0, 7)] : List (Sig × Nat)).toArray

def compactWords121 : Nat → Nat
  | 0 => 0x9f
  | _ => 0

def compactCount121 (k : Nat) : Nat := match k with
  | 7 => 1
  | _ => 0

def compactPath121 (k : Nat) (i : Nat) : Nat := match k with
  | 7 => 0
  | _ => 0

def compactLive121 (k : Nat) (i : Nat) : Nat := match k with
  | 7 => readCompactBits compactWords121 (0 + 5*i) 5
  | _ => 0

def compactPoolIDs121 (k : Nat) (i : Nat) : List Nat := match k with
  | 7 => let v := readCompactBits compactWords121 (6 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords121 (5 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket121 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP93 : Nat → Bits
  | 0 => 0x5efefdd70ef595fde7bee9e99f28aa33dedeeb8e4b18aa4e5a68
  | 2 => ~~~(0x3c0c511a653fe0020ab096e1d3fbfba00cfa580139faf803ffc : Bits)
  | 3 => 0x7bbfdf6ba74e8bcffdfb6d1e59ff2089b7a7b513f8972c3704bc
  | 4 => 0x777fe7f0fe9873f27ffd1fe67e161731f9f935ec370685a9f544
  | 6 => ~~~(0x100000620e8c920045106d805a3e223190b0310e6b16ac2f546c : Bits)
  | _ => 0

def samplesQ93 : Nat → Bits
  | 0 => 0x2109010091082a4404260310441004848a4241084008984a0848
  | 2 => 0x3c54d912403ffe11103bbb2cd640929ff200845092bfcffc002
  | 3 => 0x45004844811508a4081988001009241050520122001641500a4
  | 4 => 0x8a0480a00628500225020228841600270901080152200a0f400
  | 6 => ~~~(0x6ffdffdffd7bffef77f7fffffff5ffeffff779df7ffffffffcee : Bits)
  | _ => 0

def compactPerms93 : Array (List Nat) := ([[], [67], [48], [48, 67], [64, 67], [64]] : List (List Nat)).toArray

def compactDomains93 : Array (Sig × Nat) := ([(subcube 4 0, 7)] : List (Sig × Nat)).toArray

def compactWords93 : Nat → Nat
  | 0 => 0x9f
  | _ => 0

def compactCount93 (k : Nat) : Nat := match k with
  | 7 => 1
  | _ => 0

def compactPath93 (k : Nat) (i : Nat) : Nat := match k with
  | 7 => 0
  | _ => 0

def compactLive93 (k : Nat) (i : Nat) : Nat := match k with
  | 7 => readCompactBits compactWords93 (0 + 5*i) 5
  | _ => 0

def compactPoolIDs93 (k : Nat) (i : Nat) : List Nat := match k with
  | 7 => let v := readCompactBits compactWords93 (6 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords93 (5 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket93 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP91 : Nat → Bits
  | 0 => 0xbeffe51a6fe4deef7caf3374858c5edfae9e5293419d3432
  | 1 => 0xdcf8ff6bd300ffbeafd03cb24a00afe4c733fb0c8e3f8244
  | 3 => ~~~(0x600c009cba7100604283cb2ef58f82ec615409c8fd1f764 : Bits)
  | 4 => ~~~(0x800212a15540a802387300496a5b6052b129a6fc1ad969a : Bits)
  | 6 => 0xeffff8ad9dd7fbd7f72ffc80b671bf2f7b558c6c81e1d788
  | _ => 0

def samplesQ91 : Nat → Bits
  | 0 => 0x41110a0490194208451900c840112a4822084210c2951022
  | 1 => 0x23434890087fe402211b55d0a1260fc445022035d6bf0204
  | 3 => ~~~(0xf9ddbff6bf5976defffdaaedfbb77a7eef7f6edaebd5ff6e : Bits)
  | 4 => 0x88000220500004488000000128010308024040000006840
  | 6 => 0x100801402200109010000005080040020851080000008508
  | _ => 0

def compactPerms91 : Array (List Nat) := ([[], [100], [48], [48, 100]] : List (List Nat)).toArray

def compactDomains91 : Array (Sig × Nat) := ([(subcube 2 0, 7)] : List (Sig × Nat)).toArray

def compactWords91 : Nat → Nat
  | 0 => 0x9f
  | _ => 0

def compactCount91 (k : Nat) : Nat := match k with
  | 7 => 1
  | _ => 0

def compactPath91 (k : Nat) (i : Nat) : Nat := match k with
  | 7 => 0
  | _ => 0

def compactLive91 (k : Nat) (i : Nat) : Nat := match k with
  | 7 => readCompactBits compactWords91 (0 + 5*i) 5
  | _ => 0

def compactPoolIDs91 (k : Nat) (i : Nat) : List Nat := match k with
  | 7 => let v := readCompactBits compactWords91 (6 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords91 (5 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket91 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP59 : Nat → Bits
  | 0 => 0xbefff3f2cdee67fbfef3ef8e9c72e17726dfcb39e6cef4870aaae1a
  | 1 => 0xec7eff4e3f5800fedd7f5a511fcdca001fef33e6756d08680bfd024
  | 3 => ~~~(0x600c002398c46008c108c801fc0eb6432093330a18fc8ef093ae34 : Bits)
  | 4 => ~~~(0x8402046066aa50800626b0d9809259b24c089c4464c7495e2adb8a : Bits)
  | 5 => 0xdf3fecf732af84fdaffeadadfb8925882ff9bdd48b9c4095e53fb80
  | _ => 0

def samplesQ59 : Nat → Bits
  | 0 => 0x410304091200888810900090808312080242090120c084090888212
  | 1 => 0x139146908083feb20848d1b4a9d360c287e720a050089da9aafd004
  | 3 => ~~~(0xf9fbbfeddefbbbebbdfdfffbd6efb6fbff5b7bf3fbdfeedfddbef76 : Bits)
  | 4 => 0x860104404280141810128030404041028184212090140121502460
  | 5 => 0x20c812c0485033602424f923044400215d191040821548929536900
  | _ => 0

def compactPerms59 : Array (List Nat) := ([[], [48]] : List (List Nat)).toArray

def compactDomains59 : Array (Sig × Nat) := ([(subcube 2 0, 5), (subcube 32 0, 5), (subcube 0 2, 5), (subcube 1 0, 4), (subcube 8 0, 4), (subcube 16 2, 4)] : List (Sig × Nat)).toArray

def compactWords59 : Nat → Nat
  | 0 => 0x39227e522010fd0397e8058231d1f
  | _ => 0

def compactCount59 (k : Nat) : Nat := match k with
  | 6 => 1
  | 5 => 1
  | 4 => 1
  | _ => 0

def compactPath59 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => 0
  | 5 => readCompactBits compactWords59 (29 + 12*i) 12
  | 4 => let v := readCompactBits compactWords59 (83 + 12*i) 12
    (readCompactBits compactWords59 (71 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | _ => 0

def compactLive59 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => readCompactBits compactWords59 (0 + 5*i) 5
  | 5 => readCompactBits compactWords59 (41 + 6*i) 6
  | 4 => readCompactBits compactWords59 (95 + 7*i) 7
  | _ => 0

def compactPoolIDs59 (k : Nat) (i : Nat) : List Nat := match k with
  | 6 => let v := readCompactBits compactWords59 (23 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords59 (5 + 3*(v &&& 7)) (3*n)
    compactIDsFromBits bits 3 n
  | 5 => let v := readCompactBits compactWords59 (55 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords59 (47 + 2*(v &&& 7)) (2*n)
    compactIDsFromBits bits 2 n
  | 4 => let v := readCompactBits compactWords59 (102 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords59 (102 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket59 (k : Nat) (i : Nat) : List Nat := match k with
  | 5 => let d := readCompactBits compactWords59 (61 + 1*(i % 1)) 1
    let off := ((i/1 + d) % 1)
    let v := readCompactBits compactWords59 (62 + 9*off) 9
    if v >>> 1 == (i/104729)%251 then [v &&& 1] else []
  | 4 => let d := readCompactBits compactWords59 (104 + 1*(i % 1)) 1
    let off := ((i/1 + d) % 1)
    let v := readCompactBits compactWords59 (105 + 9*off) 9
    if v >>> 1 == (i/104729)%251 then [v &&& 1] else []
  | _ => []

def samplesP123 : Nat → Bits
  | 0 => 0x6fdffff3761baf7cf62ffe7ef7fd7e5fcf63d9e741d333815c87f5cc8cb1f7765de7f39f93f8cfbe0f12364fe87450ed21a0dc0b092d6adbd52f14f91f893067063240ec12a5a54852
  | 1 => 0x7b8fe8ffcee8fed4104bf7ffdf76a7bafad461f8cf4ca7d6e868a4200041fffb7b365e3be69f75e8ba09c988f1ef271e1042201004d7ef7fe8c9c72a716ce2b6898c0d0037f6d00484
  | 3 => ~~~(0x204000c060085a67b40402400230a61c0c2001d905c8b7677216e528deea910012471c0b82c448330c138a8cf1ff81af95fafa5c0fe9211cc9cde4bc16c9c8c7cfcc7dee153dbf4ee4 : Bits)
  | 4 => ~~~(0x1800820542884985a4c3022800001238b0329a04dd43299ad4996f5ddd404504c26c084e21a054edbc1b1cfc8702c93ada5e5b79e664a50722a97ca51b1f626f3f662bda6a6f3ed3a : Bits)
  | 5 => 0x776fdfed7dbcd3af2887ffefbebbc7259dab3fbf0cf0d62db750da3054019ffee6cf9dc7ff5e79574dd5b1f4c1988c938c2140248a1fdd9cf2f0a7944293dcce424062b18d3f63a020
  | 6 => 0x7dfffffef16f5cfbdf57fbf3ebffb9ff2f3fafd8358c387b231f07e1dbcefddd9e7fececeae78e63d0e38a8f1e73a9a2859ca3d4166a33746b0ef8ce94f1cf00f1c4300e24089a4f28
  | _ => 0

def samplesQ123 : Nat → Bits
  | 0 => 0x1020410408441081089082020441c06000a4080084200c028018021130032110406000908100c022101042c00808015044400060104128414120140808880060040601241084814042
  | 1 => 0x472134611120023afb7a1084020ea6e21ed1a8a200210201104189f7eaf75fb010408024090241a7154d2d95abdb155011111024207ee77e08842220104800494dec534b6f6c00404
  | 3 => ~~~(0x5fbf7dbfdff7bdbddbfaffdeeef7f5f7fffefd75ffbf5fbebdffbed7bb77bfb5d7ef7dbfefddfeffffbf6feebd5eeffb6fdf7df7fbfdb9ddefedf7febfdfdbefef6f7bff5dbfbfdeee : Bits)
  | 4 => 0x18408104020840850484410220200814800a060088400882401840081508a04828030080441008408200d0420000a2208042404083811880c012010240201804a00124049090c1080
  | 5 => 0x891181282010810d36a5084009020876948b06011090110082200468b749ea4040a05012008181c69240d0c3014aa2200880891209c919ca04001840210500aca4852504d3b208020
  | 6 => 0x2080000048021040000084088040000000000014210420400c0200000000000100140240a040240000000000000000022024000810000000204804090410a00000000000000120a08
  | _ => 0

def compactPerms123 : Array (List Nat) := ([[], [48]] : List (List Nat)).toArray

def compactDomains123 : Array (Sig × Nat) := ([(subcube 2 0, 8), (subcube 16 0, 8), (subcube 32 0, 8), (subcube 1 0, 7), (subcube 8 0, 7), (subcube 64 0, 7), (subcube 0 2, 6), (subcube 3 0, 5), (subcube 9 0, 5), (subcube 64 2, 5), (subcube 65 0, 4), (subcube 72 0, 4)] : List (Sig × Nat)).toArray

def compactWords123 : Nat → Nat
  | 0 => 0x7fbfda5ff2282ecd044e2405401ff0f954dcf01ff0ff0967449293f6dff09721948ebff0ff0ff0ff09f0ff000fcd86a728519dc0cc29c120c4560954155992c51106243d6aaa0426515a00736d94d5b7f6b5f2fee7f378b390a22bce479c811142714405cc24014c54024c2405405402405401461ff83fc09adff07f81c1d0a7035d03224dd44ff07f80655fe0ff07f83fc1fe0da13d85f0bc0f228f4a48a0549c7acde575a3c2f23a42a8028590b0c49a56d00811409a475b12529020e2902c428915198494870804a00b09c6e49a560e35e24698742545b0c06262a82654461e90189a56d02654066f7efffffafff7f2f6f6445b30a4c250154c5111440533084c2405402401557fe3fc505f3854338ff82e32880082402a0e68d8528820735844440e30e0d3fffff50150090070b1323f
  | _ => 0

def compactCount123 (k : Nat) : Nat := match k with
  | 9 => 1
  | 8 => 3
  | 7 => 9
  | 6 => 7
  | 5 => 1
  | _ => 0

def compactPath123 (k : Nat) (i : Nat) : Nat := match k with
  | 9 => 0
  | 8 => readCompactBits compactWords123 (30 + 12*i) 12
  | 7 => let v := readCompactBits compactWords123 (380 + 14*i) 14
    (readCompactBits compactWords123 (344 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | 6 => let v := readCompactBits compactWords123 (1648 + 15*i) 15
    (readCompactBits compactWords123 (1528 + 24*(v >>> 12)) 24) ||| ((v &&& 4095) <<< 24)
  | 5 => let v := readCompactBits compactWords123 (2376 + 12*i) 12
    (readCompactBits compactWords123 (2340 + 36*(v >>> 12)) 36) ||| ((v &&& 4095) <<< 36)
  | _ => 0

def compactLive123 (k : Nat) (i : Nat) : Nat := match k with
  | 9 => readCompactBits compactWords123 (0 + 6*i) 6
  | 8 => readCompactBits compactWords123 (66 + 7*i) 7
  | 7 => readCompactBits compactWords123 (506 + 8*i) 8
  | 6 => readCompactBits compactWords123 (1753 + 9*i) 9
  | 5 => readCompactBits compactWords123 (2388 + 10*i) 10
  | _ => 0

def compactPoolIDs123 (k : Nat) (i : Nat) : List Nat := match k with
  | 9 => let v := readCompactBits compactWords123 (24 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords123 (6 + 3*(v &&& 7)) (3*n)
    compactIDsFromBits bits 3 n
  | 8 => let v := readCompactBits compactWords123 (227 + 9*i) 9
    let n := v >>> 5
    let bits := readCompactBits compactWords123 (87 + 5*(v &&& 31)) (5*n)
    compactIDsFromBits bits 5 n
  | 7 => let v := readCompactBits compactWords123 (1076 + 11*i) 11
    let n := v >>> 7
    let bits := readCompactBits compactWords123 (578 + 6*(v &&& 127)) (6*n)
    compactIDsFromBits bits 6 n
  | 6 => let v := readCompactBits compactWords123 (2033 + 9*i) 9
    let n := v >>> 5
    let bits := readCompactBits compactWords123 (1816 + 7*(v &&& 31)) (7*n)
    compactIDsFromBits bits 7 n
  | 5 => let v := readCompactBits compactWords123 (2398 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords123 (2398 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket123 (k : Nat) (i : Nat) : List Nat := match k with
  | 8 => let d := readCompactBits compactWords123 (254 + 1*(i % 2)) 1
    let off := ((i/2 + d) % 8)
    let v := readCompactBits compactWords123 (256 + 11*off) 11
    if v >>> 3 == (i/104729)%251 then [v &&& 7] else []
  | 7 => let d := readCompactBits compactWords123 (1175 + 3*(i % 5)) 3
    let off := ((i/5 + d) % 26)
    let v := readCompactBits compactWords123 (1190 + 13*off) 13
    if v >>> 5 == (i/104729)%251 then [v &&& 31] else []
  | 6 => let d := readCompactBits compactWords123 (2096 + 1*(i % 4)) 1
    let off := ((i/4 + d) % 20)
    let v := readCompactBits compactWords123 (2100 + 12*off) 12
    if v >>> 4 == (i/104729)%251 then [v &&& 15] else []
  | 5 => let d := readCompactBits compactWords123 (2400 + 1*(i % 2)) 1
    let off := ((i/2 + d) % 5)
    let v := readCompactBits compactWords123 (2402 + 9*off) 9
    if v >>> 1 == (i/104729)%251 then [v &&& 1] else []
  | _ => []

def samplesP95 : Nat → Bits
  | 0 => 0x5f76fdffed7b60bdfee54afc14bfef9beffdfa6f3faff0fd1b9e74440f74a374e0bf95691860c5fff3ef1faddfdc55fc3cfca3be6879d41f848e8ed07d70e58881193830ddf676d57f2d65f13d56c5362330d90e8024b2b7434cd0c8
  | 1 => 0x6f94fe6dff9d7ece73897310803ffdffb63eff71cfd0c3e3e3efbe387180c1c70343e610200309bfddfff1f1e3e07f9fcf7f3dc78781e860f8f303c78380f8304e6000411ffb9fdf9bce871e4e0d07d83c3f003105c903fd748a0910
  | 2 => ~~~(0x1b700612858346c226dfbdecfc0008124188c0f2b80e31183c23d345d1cf9c7e397c75fbefffe14000020a1e1885a1808488a97b401f076cccef3c3f9d0ffbfff7fbf7dc000024612074773af2e85d82c781f3ff7edfc0d600bfffc : Bits)
  | 3 => 0x7db9fff3fbc6f57ea5fec546c87ffff77ffb8defa8577f179f53fdb2d83db810f5844ae28a3c21fc7fdfe2677dbffa547ac7ffb4b43ab771cb4ef3207057078f100a130c0fafd9fe56753e21a3aa0c4bedd8c60cf204c359e960226c
  | 4 => 0x7befffff3ffa9ffd4b74be8bfbbf53fffdfff49fffe8af1afffc6bbf6c4a5caffabb819c14d83bffaefaeddba21bea7bbff8da7f504513fe76e0712ffae8e2276e54a63093c5e72af39b5adec9aab2bc12e8390071e94d24a6b5a594
  | 6 => ~~~(0x80000000182409c4184460098804112002000618c4000021b1c7eba68608034f0ab80b81878282800ca4141021060543ef4312440799779f2e203247260e7af4e58323081e7d598530d3e9c498a063e33b8d90cf1edc335e7e4a1dc : Bits)
  | _ => 0

def samplesQ95 : Nat → Bits
  | 0 => 0x208912100a40934201029502a96420140c0589806870101280b0080a440824800f802a908195228d1229004cc044105005c0260a64004c9045a182300ac0025840408903949246152228e4015402413003300103802a92a642484088
  | 1 => 0x106b4097026a016104360ca77ff240058293a104216a9445ac7461434c452a595ab10a4cd3389795d99a30598b2519051bd8048145532d01d664a05125ca495aa4525a04bfeb13471accaf064a0145089a224315ac8913fd70880810
  | 2 => 0x1b70a236c782548006df3dccfdd08460191eeb34c99a13f05c2f02644143b4bcaa34a173eef6deaa777c84899071d0339f2050138cf70bb8bd317249f193d5e0c410c2cbfdcfdb8edb4be0c404061058a26c8421e77c7f29ff40002
  | 3 => 0x2462084242908800a212a29168a910060902615050224482806020003064a6d4061010944429930688482222911490158149000191411081816214520124922050420c42b2508ca14540a2481000842a88a42142294415929200244
  | 4 => 0x410802040044000b00840500001028810200022008101200100800090a08000000414022800404204400100000820280000486400880022000014009001200010a800004000a020c10300900088820000402840104004008415a100
  | 6 => ~~~(0x77fffbffff7fffebbf7ffffffffffbdfffb7effffffffffffffffb6fdfffffffdff77fdffffffffffffffb7ffb7f7d7f7ffeffefffffffffffffffffffffff7efdffffefffffffffffffffbfdfcbef7fbbfefffffffffffffffdebde : Bits)
  | _ => 0

def compactPerms95 : Array (List Nat) := ([[], [48]] : List (List Nat)).toArray

def compactDomains95 : Array (Sig × Nat) := ([(subcube 2 0, 8)] : List (Sig × Nat)).toArray

def compactWords95 : Nat → Nat
  | 0 => 0x13f
  | _ => 0

def compactCount95 (k : Nat) : Nat := match k with
  | 8 => 1
  | _ => 0

def compactPath95 (k : Nat) (i : Nat) : Nat := match k with
  | 8 => 0
  | _ => 0

def compactLive95 (k : Nat) (i : Nat) : Nat := match k with
  | 8 => readCompactBits compactWords95 (0 + 6*i) 6
  | _ => 0

def compactPoolIDs95 (k : Nat) (i : Nat) : List Nat := match k with
  | 8 => let v := readCompactBits compactWords95 (7 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords95 (6 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket95 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP63 : Nat → Bits
  | 0 => 0x5fee7fff6efee4cbf7ed919fc9a75fff5ffbfcfe3ff8efdc3fc52e76bddf04a5347dc1c7e0bbca98d9e9fdf3efdf2d79cbf1afee4ff64fe7c61ffd88bac2287dc1ab0711c3e9105e7053b9f26e9677cdeec33489ca714ccc73e76c8815a82bc85529782a
  | 1 => 0x77273fdffd9a3fd6bc83c6b100710ffdf7edcf7fe6f5d0e8f97df3ebf471cb380807d83d070f21000005ffdd7ffdcf9f0f9f5a7b3bbb7d3c93c0ca160730f08f8ece80663f8426800009fb5fbfdf9c79fc0e9af70398e3a1d860820388403f58fa8e8044
  | 2 => 0x7e9a3feebfe7c9e7cf164842138e0ffef9f6f7bfef0f7f273b9a7d8cffa071d0c0f827c81ad02c220001bfffbf7ef1ee73ee7793d3cf8fda3cbf02e0dc3d40f27030f8835c0008208225fdefcde7bfb6b9702f1e740f0f3e8398100422023f970df24210
  | 3 => ~~~(0x28440c0200209830685871b9305500040c0043068e860803b196000b82065b088f7bd2e029babb291e424802808090803dc1462030c4e1b36b8f208943860ff6f2ec0435fc43efac27e098829832660e90c3e9fe2294b39e27ff20fbf620ad49ecb7a74 : Bits)
  | 4 => ~~~(0x422000c00822044e50040a740bb60080000c00a27010e6438c00382c54118b5444d42d986cc48ee69ca10510440247e4b02021010f20da0cb978c90cec4c86ed0a938313c6b1967be6580560e169514364305ee531687c493f93d8c66bbad9a512eaf1a : Bits)
  | 5 => 0x6ff5fffdf3ff3b3d67fde72ff6196ffbeedffffb79eb2ef7fefbc393cb6e3cb7cfc73e3a86ccdae621c3f6fffcebbe7eff5e9474b47cfebb6bb0b419c4cccf6e7f2d78793c4219638e65ce9c3b3be776730d45eef3269351a679310c66338cb6924faf10
  | _ => 0

def samplesQ63 : Nat → Bits
  | 0 => 0x2011820051051134000a22602248a210210304c250099004042150064200854a04820630026405422410c51220502c88480038025c06400206a000886100688041940012a01120830206980260923005284304904241400cf001408038282ac044280822
  | 1 => 0x8d8d0701a248039013c994a7f0ef8d424809ad0914a348510eee4145c94244965612ca23075587f8f61d6d9129d08b55d8412c9592028138dca46a98b591a84542e5240a94943b22527f9533f5a84395c5a82554212a128c0c056a90872bf58728e8004
  | 2 => 0x165c13561082230106db6bdc451fe28a02038f04231e2904ec392a382b3064d07453c2064770384fad7a9a7356648f07f0c11985b0003022b2951127e01712083f9c95b04a9c6c20c37f9a4c4e53da6b4728a1862068b08c18b1114b0cc3f930df04010
  | 3 => ~~~(0x7d7bbbbedfddf7fdfd5b7aed6ffaabbfefe7e7e6ffafbbeeedf7f9fe6fdbbf5e76bed6f3dfee7f4feefaf797f9deedcfead8ff73fe7eff5fdffdfecfebaffdfb7bbe6df6f6f3adff3bde9f9afdf3f6e5f9ef3dffe6fd7a7df77ffadaff7b6af5deef7ef6 : Bits)
  | 4 => 0x4222006008800406400408500b001234004000422200328490000a8014218100008400080880000408a2004c902810080504000a00800445011900200068133020009840482080400400688802142c08080300084881011000aa010c3004025884150c0
  | 5 => 0x100a08020a8044808800080009a201800a404100a1020128010420180d400000101080410900200900281200c88880020000842000509409d0508601800e80131002008400000008108806181900c24041040122002000400620a2084312402492072600
  | _ => 0

def compactPerms63 : Array (List Nat) := ([[], [48], [33, 84], [33, 48, 84]] : List (List Nat)).toArray

def compactDomains63 : Array (Sig × Nat) := ([(subcube 2 0, 7)] : List (Sig × Nat)).toArray

def compactWords63 : Nat → Nat
  | 0 => 0x13f
  | _ => 0

def compactCount63 (k : Nat) : Nat := match k with
  | 7 => 1
  | _ => 0

def compactPath63 (k : Nat) (i : Nat) : Nat := match k with
  | 7 => 0
  | _ => 0

def compactLive63 (k : Nat) (i : Nat) : Nat := match k with
  | 7 => readCompactBits compactWords63 (0 + 6*i) 6
  | _ => 0

def compactPoolIDs63 (k : Nat) (i : Nat) : List Nat := match k with
  | 7 => let v := readCompactBits compactWords63 (7 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords63 (6 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket63 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP79 : Nat → Bits
  | 0 => 0x76bbfaffbfbe03847fffefd2d8d9c77fc39d601edfdbfdd6898c1d0beb9d94
  | 1 => 0x7ac3ff2df20cf4019fa8f7ffe71e699c8c20045fffad86670ef062407dc640
  | 2 => ~~~(0x10dc1021b3aca6d7e028c400741c675ccfbf77400a09f6470e837f6b8587fc : Bits)
  | 3 => 0x5f57f7f3f1e3af561f7fdc7ff4f5f7507392531dfe7b720dff8f192a5db83c
  | 6 => ~~~(0x2000200300201040000005280d1c11003904004d40b0004898c190a499814 : Bits)
  | _ => 0

def samplesQ79 : Nat → Bits
  | 0 => 0x945151000219c4a89182c03140b10d2007030ca87172c1201800706e28d04
  | 1 => 0x53c245708f60e7c7c829d414567c247957ae13dcbaf823624252bc0fdc440
  | 2 => 0x10dc9903a1bc2c97a7068f09982cf991cf71233b74df0112646c04fe7a7802
  | 3 => 0x20aa0844869440a15262813009402b0455040d3438684009ac2528381d3030
  | 6 => ~~~(0x7dffbfffeffffefffffebf7bffffffffff7fffffffffef3fedeffffffffd76 : Bits)
  | _ => 0

def compactPerms79 : Array (List Nat) := ([[], [48], [33], [33, 48]] : List (List Nat)).toArray

def compactDomains79 : Array (Sig × Nat) := ([(subcube 2 0, 5)] : List (Sig × Nat)).toArray

def compactWords79 : Nat → Nat
  | 0 => 0x9f
  | _ => 0

def compactCount79 (k : Nat) : Nat := match k with
  | 5 => 1
  | _ => 0

def compactPath79 (k : Nat) (i : Nat) : Nat := match k with
  | 5 => 0
  | _ => 0

def compactLive79 (k : Nat) (i : Nat) : Nat := match k with
  | 5 => readCompactBits compactWords79 (0 + 5*i) 5
  | _ => 0

def compactPoolIDs79 (k : Nat) (i : Nat) : List Nat := match k with
  | 5 => let v := readCompactBits compactWords79 (6 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords79 (5 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket79 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP127 : Nat → Bits
  | 0 => 0x302216585c2c0289faf44c5d4c1184a2c1a504effcebfb47f33cfb9af5eb47e2bcd8dd1f7ff3c0365ef6372c5adbe0b4c33f8b8be20d842ebe8a08ab8588c143cf9c118de5600b291b980745823401338c0b802281bb74bd89dd62623afb8de36726195c851e74566c6c14d01818723651487108012caa0b3a90928a36524248
  | 1 => 0x3481dc83eb003d140fa9860280020000220820ff3fcffd7abddfffdffe3e953fca1fb142fcb487ed79b9c7f687be853f6df2c0fd4c20f3c0a5c416003e660f84a1f92076c1d704066c407fb028081c44001000080a3ffdcefe7bf3e3cfccf9767e50750761e1c485d03a4e01f4a1d9c620830a023841000ff671f54359002410
  | 2 => 0xc90621fc8013ca274108e8a810441000004001ffd7bedff7efeaf7ecff77e6cf73eb269d661e7e485f5bf887d93cff48f43b7d6218492dff4107a0dce07134073846a1811e18705830e7b8004002008801a00451147ffeef6f9ed8df5cbf57bdd49380e1c83399321791907f861c83f9803400140292040ff8ce2eecc4040103
  | 3 => 0xd0f801190c7f74381411333c25a8a2350403507fe5f716fcf7f35b7fc7bcf8707c73c7ef80e7787fa49478fb2dc0c7f17ec3be9c6076520e467bd7608783b8f80608de0608207f93c10bc00793c02200b0433b80602feb0bbf2b1f6c6f121ec59b2b9e080ec401e9a0a1eb1e18ee1c30060065e04404707cd516c88d0809886c
  | 4 => 0x2f1de84653af8549e2ea10618a2148940806a29f7adfe3bf4aff27f5adddbb92c3a4dae0870bbfb9a7e9b62facdb18cabbcc4b6b9d8a18213909ef2b4274e1bc08130e7a0adf8b34e594070221c8dc43420843028914e7b147e0fd15b527ea7a84e5e65572206a68ab52174007176c0850c008e0b9491194230b4774a4c09614
  | 5 => 0xb41e323b4d03ae20d56198370c00348d03018fcbf3c7efd3e1fbc3f3bcf693d351f6eb2fb4887d281460fd977657a3f91fd34f6b3d0ec109a3019d439990e7b51e6c07931a8f0c7922078c81407023808643c35042c1f70f0758f9bf0f0f60a79886aa299d9bb050045a9a1eb41a607890c840d0630c462896d11336a3d0180
  | 6 => 0xc6fe1ea423c0c1d6b007e7d6031e7d4b3fd8cff3cb71ad8bdde5cce35af31ecd8fe4397d19fd7987fa2fc950f2273fc70e04f71507b703d140f46017580e5200f6217f80f60784e80e7f80b84c31e1847794c0cc72d39856108624bc834d219da85c01ba360e069a5f8e60ae61e201c82e339213c0820b8144a0281091a278a3
  | _ => 0

def samplesQ127 : Nat → Bits
  | 0 => 0x2429030000c9780404a320a0481a1902020aa5202b0944012c008a9060412040c83d02001040060582010489c02004c7000103020caa0000862860020857440004300c0c800061250040024e0800400a40848017193404094462021a0904416416180085221404240c14000018f000014013000342a20b2a80820a10120208
  | 1 => 0x8a2aa416114a812b84943a103eed313e9924c7ff274d7562b187ce53b60a15045292b486b48453051111146289aa202404a09052c65872b4635689808eb062d492a5942165caa60c0d4552514aa08a4a29029214257ffcca9c79b3a243c879563e12d50060a1508414288a04c490c0942245ab5a1041c62ff670f14358002010
  | 2 => 0x83bb4060328a1a906872201c393eae572b23cffd2b2ce17646a51ec4d72830c7090368ee0807605510930a0c9983404040a301214c7c86368c8326da40a35893028629f1939116db80c89354b8118600c00f012657ffca7238e58cd1c9747b9d2139481403018140609884d8090c1b0911414364b87308ff8c62eec84000102
  | 3 => 0xc0a8644c188000500c000c258144180a110a05a81d01220c4801a0540182054183000c4a0c21261900150280008828120011090100300850018900828a2001022884422503222009009121920840900402810582066c8093403016805101a8483008608420001410080c81490c408900201244450841024d414488408010844
  | 4 => 0x1040002024000200180044000102844044c91000580080990a50212009850802010440000201800802200001040100480800480828800442880042054005880948500290000111904030898010022084800400200080033042800c15a026802800600044100020208810010002030008989800208c180090010b0430a4c08400
  | 5 => 0x608000880801040020080004042004020c4d41000c0420881a11a41022850000040100300808009000400a100004401010540020e81014108300418040158800c85180002040849040700080001040011091010008000350c0308410e060a00208802000084882000040202028000602288888088418441001291111620c0080
  | 6 => 0x10040000014100041200008000000000000000000000000000000000000008180000001012008002804800032000902000006040000000000000000000000000000000000000000000000008040041000000801800000000000000000000000000800320004000a410200820120004000000000000000000000000001205021
  | _ => 0

def compactPerms127 : Array (List Nat) := ([[], [48], [33, 84], [33, 48, 84]] : List (List Nat)).toArray

def compactDomains127 : Array (Sig × Nat) := ([(subcube 1 0, 10), (subcube 2 0, 10), (subcube 4 0, 10), (subcube 8 0, 10), (subcube 16 0, 9), (subcube 32 0, 9), (subcube 64 0, 8), (subcube 34 0, 8), (subcube 0 2, 7), (subcube 0 4, 7), (subcube 48 0, 6), (subcube 16 2, 6), (subcube 80 2, 5), (subcube 96 4, 5)] : List (Sig × Nat)).toArray

def compactWords127 : Nat → Nat
  | 0 => 0x8bb3098d386ceff25eeb9e1c3fe079db2fbd94b76bff80725e21f38da2abfe07f81fe07f81fe06647efab703f42ad571669c0e2721e2e04cfccf0ee36cd6b789fe8146d459a3ec3322120ee00fac4bcb8f1421a42263965d665978f1444c1d4ad54316642b971405aa9620cb614e4c455308b0b552c1f1f2e4c4bc50d591de0c0884a650c17263c50878c562f23ecb8ac8a02147e4cb67163182848806001011b97263198a145c93078c845a6585767265c5093818a315e4cb88459b0af2e4c53dff77defbbeefbe7fdb77cfffedfbbecfab408e811d02a9cb529aa8284a61a031412283bd017a02f405e80e70a43473242a73242a72c43272a43243242dad6c94c3b3ae1ff81a87ff80d03ff81fe01e2bfe07f81fe07f802339322c30a2b7fe00ea64eee52fa05cf46a4fc4012a7a934356da9c84641f30c9a4ab1a785ac0050c1002b6caea35f45e3dc39076d10d16caea3204c4303081005813b6caea14a3513903ecb53aea301be23ccb6caa222f3e0b6ca8428c3c6154b6caea844283081005821b6caea4503ce1acaeda942a084644e40f50c34ab2bb6a0c028204c36db2baaffffbfffffb7df7dffffffbfc9caa5339caa72b9c2e70890c67311cc27309cd10c90c90bfe1ae65b782f2ca193fe1fe1fe1fe1fe1fe1fe056ce99801462080868c1ee28c400b2643460f728c3104042c60f77fffffc43243242e162647f
  | 1 => 0x16cf319ff03efffc1777ff05bbffc1fe029eff82cdbfe0ca1dd4d6d67f1ecdff83fc1fe0ff00ad56a4c440889042966ae96ae916645beae94db26ae9779af35e7bcd79df3de73cba44e911a456915a45e817a05e81680a73242a82e70a43272e70a43253670a437d13ae98d4f914
  | _ => 0

def compactCount127 (k : Nat) : Nat := match k with
  | 11 => 1
  | 10 => 3
  | 9 => 11
  | 8 => 14
  | 7 => 8
  | _ => 0

def compactPath127 (k : Nat) (i : Nat) : Nat := match k with
  | 11 => 0
  | 10 => readCompactBits compactWords127 (31 + 12*i) 12
  | 9 => let v := readCompactBits compactWords127 (497 + 14*i) 14
    (readCompactBits compactWords127 (461 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | 8 => let v := readCompactBits compactWords127 (2211 + 15*i) 15
    (readCompactBits compactWords127 (2067 + 24*(v >>> 12)) 24) ||| ((v &&& 4095) <<< 24)
  | 7 => let v := readCompactBits compactWords127 (4295 + 14*i) 14
    (readCompactBits compactWords127 (4151 + 36*(v >>> 12)) 36) ||| ((v &&& 4095) <<< 36)
  | _ => 0

def compactLive127 (k : Nat) (i : Nat) : Nat := match k with
  | 11 => readCompactBits compactWords127 (0 + 7*i) 7
  | 10 => readCompactBits compactWords127 (67 + 8*i) 8
  | 9 => readCompactBits compactWords127 (651 + 9*i) 9
  | 8 => readCompactBits compactWords127 (2421 + 10*i) 10
  | 7 => readCompactBits compactWords127 (4407 + 11*i) 11
  | _ => 0

def compactPoolIDs127 (k : Nat) (i : Nat) : List Nat := match k with
  | 11 => let v := readCompactBits compactWords127 (25 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords127 (7 + 3*(v &&& 7)) (3*n)
    compactIDsFromBits bits 3 n
  | 10 => let v := readCompactBits compactWords127 (271 + 10*i) 10
    let n := v >>> 6
    let bits := readCompactBits compactWords127 (91 + 5*(v &&& 63)) (5*n)
    compactIDsFromBits bits 5 n
  | 9 => let v := readCompactBits compactWords127 (1542 + 13*i) 13
    let n := v >>> 8
    let bits := readCompactBits compactWords127 (750 + 6*(v &&& 255)) (6*n)
    compactIDsFromBits bits 6 n
  | 8 => let v := readCompactBits compactWords127 (3485 + 12*i) 12
    let n := v >>> 8
    let bits := readCompactBits compactWords127 (2561 + 7*(v &&& 255)) (7*n)
    compactIDsFromBits bits 7 n
  | 7 => let v := readCompactBits compactWords127 (4615 + 7*i) 7
    let n := v >>> 4
    let bits := readCompactBits compactWords127 (4495 + 8*(v &&& 15)) (8*n)
    compactIDsFromBits bits 8 n
  | _ => []

def compactBucket127 (k : Nat) (i : Nat) : List Nat := match k with
  | 10 => let d := readCompactBits compactWords127 (301 + 2*(i % 2)) 2
    let off := ((i/2 + d) % 13)
    let v := readCompactBits compactWords127 (305 + 12*off) 12
    if v >>> 4 == (i/104729)%251 then [v &&& 15] else []
  | 9 => let d := readCompactBits compactWords127 (1685 + 3*(i % 6)) 3
    let off := ((i/6 + d) % 26)
    let v := readCompactBits compactWords127 (1703 + 14*off) 14
    if v >>> 6 == (i/104729)%251 then [v &&& 63] else []
  | 8 => let d := readCompactBits compactWords127 (3653 + 4*(i % 9)) 4
    let off := ((i/9 + d) % 33)
    let v := readCompactBits compactWords127 (3689 + 14*off) 14
    if v >>> 6 == (i/104729)%251 then [v &&& 63] else []
  | 7 => let d := readCompactBits compactWords127 (4671 + 1*(i % 4)) 1
    let off := ((i/4 + d) % 23)
    let v := readCompactBits compactWords127 (4675 + 13*off) 13
    if v >>> 5 == (i/104729)%251 then [v &&& 31] else []
  | _ => []
theorem compactHalves {test : Nat → Bool} {start n : Nat}
    (first : chartBlock test start (n / 2) = true)
    (last : chartBlock test (start + n / 2) (n - n / 2) = true) :
    chartBlock test start n = true := by
  have eq : n / 2 + (n - n / 2) = n := by omega
  simpa only [eq] using chartBlock_join first last

def grid25 : CompactGrid := (25, 3, samplesP25, samplesQ25)
def tab25 : CompactTable := (compactCount25, compactPath25, compactLive25, compactPoolIDs25, compactBucket25)
def check25 (k : Nat) := compactNode grid25 tab25 compactDomains25 compactPerms25 k
def sliceSpecs25 : List SliceSpec := []
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains25 : ∀ d ∈ compactDomains25, Slice true (vars 25) (graphGoal 25) d.1 d.2 := by
  apply compactDomains_valid (earlier := []) (specs := sliceSpecs25)
  · simp
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs25 : properPairs (graphGoal 25) (asRow samplesP25) (asRow samplesQ25) :=
  compactPairs (g := grid25) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos25 : ∀ p ∈ compactPerms25, autoOK (graphGoal 25) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c25k3p0 : chartBlock (check25 3) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev25k3 : chartBlock (check25 3) 0 1 = true :=
  c25k3p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded25 : Impossible true (graphGoal 25) 3 (vars 25).toFinset := by
  apply compactRoot (g := grid25) (t := tab25) (dom := compactDomains25) (perms := compactPerms25) pairs25 domains25 autos25
  · intro k hk
    change k ≤ 3 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · exact lev25k3
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound25 : Lower true (vars 25) (graphGoal 25) 4 :=
  plain_low (hints := 3) (by decide +kernel) excluded25

def grid27 : CompactGrid := (27, 4, samplesP27, samplesQ27)
def tab27 : CompactTable := (compactCount27, compactPath27, compactLive27, compactPoolIDs27, compactBucket27)
def check27 (k : Nat) := compactNode grid27 tab27 compactDomains27 compactPerms27 k
def sliceSpecs27 : List SliceSpec := [(2, 0, 25, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains27 : ∀ d ∈ compactDomains27, Slice true (vars 27) (graphGoal 27) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(25, 4)]) (specs := sliceSpecs27)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound25
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs27 : properPairs (graphGoal 27) (asRow samplesP27) (asRow samplesQ27) :=
  compactPairs (g := grid27) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos27 : ∀ p ∈ compactPerms27, autoOK (graphGoal 27) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c27k4p0 : chartBlock (check27 4) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev27k4 : chartBlock (check27 4) 0 1 = true :=
  c27k4p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded27 : Impossible true (graphGoal 27) 4 (vars 27).toFinset := by
  apply compactRoot (g := grid27) (t := tab27) (dom := compactDomains27) (perms := compactPerms27) pairs27 domains27 autos27
  · intro k hk
    change k ≤ 4 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev27k4
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound27 : Lower true (vars 27) (graphGoal 27) 5 :=
  plain_low (hints := 67) (by decide +kernel) excluded27

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound116 : Lower true (vars 116) (graphGoal 116) 5 :=
  carry_of (old := 116) (rep := 27) (swaps := [32, 65, 83, 97, 49]) (by decide +kernel) bound27

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound114 : Lower true (vars 114) (graphGoal 114) 5 :=
  carry_of (old := 114) (rep := 27) (swaps := [16, 67, 80, 99]) (by decide +kernel) bound27

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound102 : Lower true (vars 102) (graphGoal 102) 5 :=
  carry_of (old := 102) (rep := 27) (swaps := [32, 83, 100]) (by decide +kernel) bound27

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound86 : Lower true (vars 86) (graphGoal 86) 5 :=
  carry_of (old := 86) (rep := 27) (swaps := [16, 32, 67, 99]) (by decide +kernel) bound27

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound100 : Lower true (vars 100) (graphGoal 100) 4 :=
  carry_of (old := 100) (rep := 25) (swaps := [32, 83, 100]) (by decide +kernel) bound25

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound82 : Lower true (vars 82) (graphGoal 82) 4 :=
  carry_of (old := 82) (rep := 25) (swaps := [16, 99]) (by decide +kernel) bound25

def grid118 : CompactGrid := (118, 7, samplesP118, samplesQ118)
def tab118 : CompactTable := (compactCount118, compactPath118, compactLive118, compactPoolIDs118, compactBucket118)
def check118 (k : Nat) := compactNode grid118 tab118 compactDomains118 compactPerms118 k
def sliceSpecs118 : List SliceSpec := [(2, 0, 116, 0, 0, 5, 5), (4, 0, 114, 0, 0, 5, 5), (16, 0, 102, 0, 0, 5, 5), (32, 0, 86, 0, 0, 5, 5), (18, 0, 100, 0, 0, 4, 4), (36, 0, 82, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains118 : ∀ d ∈ compactDomains118, Slice true (vars 118) (graphGoal 118) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(116, 5), (114, 5), (102, 5), (86, 5), (100, 4), (82, 4)]) (specs := sliceSpecs118)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl
    · exact bound116
    · exact bound114
    · exact bound102
    · exact bound86
    · exact bound100
    · exact bound82
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs118 : properPairs (graphGoal 118) (asRow samplesP118) (asRow samplesQ118) :=
  compactPairs (g := grid118) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos118 : ∀ p ∈ compactPerms118, autoOK (graphGoal 118) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c118k4p0 : chartBlock (check118 4) 0 3 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev118k4 : chartBlock (check118 4) 0 3 = true :=
  c118k4p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c118k5p0 : chartBlock (check118 5) 0 10 = true := by
  iterate 2 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev118k5 : chartBlock (check118 5) 0 10 = true :=
  c118k5p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c118k6p0 : chartBlock (check118 6) 0 3 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev118k6 : chartBlock (check118 6) 0 3 = true :=
  c118k6p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c118k7p0 : chartBlock (check118 7) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev118k7 : chartBlock (check118 7) 0 1 = true :=
  c118k7p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded118 : Impossible true (graphGoal 118) 7 (vars 118).toFinset := by
  apply compactRoot (g := grid118) (t := tab118) (dom := compactDomains118) (perms := compactPerms118) pairs118 domains118 autos118
  · intro k hk
    change k ≤ 7 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev118k4
    · exact lev118k5
    · exact lev118k6
    · exact lev118k7
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound118 : Lower true (vars 118) (graphGoal 118) 8 :=
  plain_low (hints := 18941248) (by decide +kernel) excluded118

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound41 : Lower true (vars 41) (graphGoal 41) 4 :=
  carry_of (old := 41) (rep := 25) (swaps := [84]) (by decide +kernel) bound25

def grid57 : CompactGrid := (57, 4, samplesP57, samplesQ57)
def tab57 : CompactTable := (compactCount57, compactPath57, compactLive57, compactPoolIDs57, compactBucket57)
def check57 (k : Nat) := compactNode grid57 tab57 compactDomains57 compactPerms57 k
def sliceSpecs57 : List SliceSpec := [(16, 0, 41, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains57 : ∀ d ∈ compactDomains57, Slice true (vars 57) (graphGoal 57) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(41, 4)]) (specs := sliceSpecs57)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound41
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs57 : properPairs (graphGoal 57) (asRow samplesP57) (asRow samplesQ57) :=
  compactPairs (g := grid57) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos57 : ∀ p ∈ compactPerms57, autoOK (graphGoal 57) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c57k4p0 : chartBlock (check57 4) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev57k4 : chartBlock (check57 4) 0 1 = true :=
  c57k4p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded57 : Impossible true (graphGoal 57) 4 (vars 57).toFinset := by
  apply compactRoot (g := grid57) (t := tab57) (dom := compactDomains57) (perms := compactPerms57) pairs57 domains57 autos57
  · intro k hk
    change k ≤ 4 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev57k4
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound57 : Lower true (vars 57) (graphGoal 57) 5 :=
  plain_low (hints := 3) (by decide +kernel) excluded57

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound113 : Lower true (vars 113) (graphGoal 113) 5 :=
  carry_of (old := 113) (rep := 57) (swaps := [99]) (by decide +kernel) bound57

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound99 : Lower true (vars 99) (graphGoal 99) 5 :=
  carry_of (old := 99) (rep := 27) (swaps := [83, 100]) (by decide +kernel) bound27

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound83 : Lower true (vars 83) (graphGoal 83) 5 :=
  carry_of (old := 83) (rep := 57) (swaps := [64, 81, 99, 83]) (by decide +kernel) bound57

def grid115 : CompactGrid := (115, 6, samplesP115, samplesQ115)
def tab115 : CompactTable := (compactCount115, compactPath115, compactLive115, compactPoolIDs115, compactBucket115)
def check115 (k : Nat) := compactNode grid115 tab115 compactDomains115 compactPerms115 k
def sliceSpecs115 : List SliceSpec := [(1, 0, 114, 0, 0, 5, 5), (2, 0, 113, 0, 0, 5, 5), (16, 0, 99, 0, 0, 5, 5), (32, 0, 83, 0, 0, 5, 5)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains115 : ∀ d ∈ compactDomains115, Slice true (vars 115) (graphGoal 115) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(114, 5), (113, 5), (99, 5), (83, 5)]) (specs := sliceSpecs115)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact bound114
    · exact bound113
    · exact bound99
    · exact bound83
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs115 : properPairs (graphGoal 115) (asRow samplesP115) (asRow samplesQ115) :=
  compactPairs (g := grid115) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos115 : ∀ p ∈ compactPerms115, autoOK (graphGoal 115) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c115k6p0 : chartBlock (check115 6) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev115k6 : chartBlock (check115 6) 0 1 = true :=
  c115k6p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded115 : Impossible true (graphGoal 115) 6 (vars 115).toFinset := by
  apply compactRoot (g := grid115) (t := tab115) (dom := compactDomains115) (perms := compactPerms115) pairs115 domains115 autos115
  · intro k hk
    change k ≤ 6 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev115k6
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound115 : Lower true (vars 115) (graphGoal 115) 7 :=
  plain_low (hints := 68) (by decide +kernel) excluded115

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound117 : Lower true (vars 117) (graphGoal 117) 7 :=
  carry_of (old := 117) (rep := 115) (swaps := [33, 84]) (by decide +kernel) bound115

def grid87 : CompactGrid := (87, 5, samplesP87, samplesQ87)
def tab87 : CompactTable := (compactCount87, compactPath87, compactLive87, compactPoolIDs87, compactBucket87)
def check87 (k : Nat) := compactNode grid87 tab87 compactDomains87 compactPerms87 k
def sliceSpecs87 : List SliceSpec := [(1, 0, 86, 0, 0, 5, 5)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains87 : ∀ d ∈ compactDomains87, Slice true (vars 87) (graphGoal 87) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(86, 5)]) (specs := sliceSpecs87)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound86
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs87 : properPairs (graphGoal 87) (asRow samplesP87) (asRow samplesQ87) :=
  compactPairs (g := grid87) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos87 : ∀ p ∈ compactPerms87, autoOK (graphGoal 87) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c87k5p0 : chartBlock (check87 5) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev87k5 : chartBlock (check87 5) 0 1 = true :=
  c87k5p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded87 : Impossible true (graphGoal 87) 5 (vars 87).toFinset := by
  apply compactRoot (g := grid87) (t := tab87) (dom := compactDomains87) (perms := compactPerms87) pairs87 domains87 autos87
  · intro k hk
    change k ≤ 5 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev87k5
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound87 : Lower true (vars 87) (graphGoal 87) 6 :=
  plain_low (hints := 1604) (by decide +kernel) excluded87

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound103 : Lower true (vars 103) (graphGoal 103) 6 :=
  carry_of (old := 103) (rep := 87) (swaps := [33, 84]) (by decide +kernel) bound87

def grid55 : CompactGrid := (55, 4, samplesP55, samplesQ55)
def tab55 : CompactTable := (compactCount55, compactPath55, compactLive55, compactPoolIDs55, compactBucket55)
def check55 (k : Nat) := compactNode grid55 tab55 compactDomains55 compactPerms55 k
def sliceSpecs55 : List SliceSpec := []
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains55 : ∀ d ∈ compactDomains55, Slice true (vars 55) (graphGoal 55) d.1 d.2 := by
  apply compactDomains_valid (earlier := []) (specs := sliceSpecs55)
  · simp
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs55 : properPairs (graphGoal 55) (asRow samplesP55) (asRow samplesQ55) :=
  compactPairs (g := grid55) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos55 : ∀ p ∈ compactPerms55, autoOK (graphGoal 55) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c55k4p0 : chartBlock (check55 4) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev55k4 : chartBlock (check55 4) 0 1 = true :=
  c55k4p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded55 : Impossible true (graphGoal 55) 4 (vars 55).toFinset := by
  apply compactRoot (g := grid55) (t := tab55) (dom := compactDomains55) (perms := compactPerms55) pairs55 domains55 autos55
  · intro k hk
    change k ≤ 4 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev55k4
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound55 : Lower true (vars 55) (graphGoal 55) 5 :=
  plain_low (hints := 1348) (by decide +kernel) excluded55

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound101 : Lower true (vars 101) (graphGoal 101) 5 :=
  carry_of (old := 101) (rep := 57) (swaps := [64, 82, 83, 100]) (by decide +kernel) bound57

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound85 : Lower true (vars 85) (graphGoal 85) 5 :=
  carry_of (old := 85) (rep := 27) (swaps := [33, 67, 99]) (by decide +kernel) bound27

def grid51 : CompactGrid := (51, 3, samplesP51, samplesQ51)
def tab51 : CompactTable := (compactCount51, compactPath51, compactLive51, compactPoolIDs51, compactBucket51)
def check51 (k : Nat) := compactNode grid51 tab51 compactDomains51 compactPerms51 k
def sliceSpecs51 : List SliceSpec := []
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains51 : ∀ d ∈ compactDomains51, Slice true (vars 51) (graphGoal 51) d.1 d.2 := by
  apply compactDomains_valid (earlier := []) (specs := sliceSpecs51)
  · simp
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs51 : properPairs (graphGoal 51) (asRow samplesP51) (asRow samplesQ51) :=
  compactPairs (g := grid51) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos51 : ∀ p ∈ compactPerms51, autoOK (graphGoal 51) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c51k3p0 : chartBlock (check51 3) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev51k3 : chartBlock (check51 3) 0 1 = true :=
  c51k3p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded51 : Impossible true (graphGoal 51) 3 (vars 51).toFinset := by
  apply compactRoot (g := grid51) (t := tab51) (dom := compactDomains51) (perms := compactPerms51) pairs51 domains51 autos51
  · intro k hk
    change k ≤ 3 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · exact lev51k3
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound51 : Lower true (vars 51) (graphGoal 51) 4 :=
  plain_low (hints := 68) (by decide +kernel) excluded51

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound53 : Lower true (vars 53) (graphGoal 53) 4 :=
  carry_of (old := 53) (rep := 51) (swaps := [33, 84]) (by decide +kernel) bound51

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound97 : Lower true (vars 97) (graphGoal 97) 4 :=
  carry_of (old := 97) (rep := 25) (swaps := [83, 100]) (by decide +kernel) bound25

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound81 : Lower true (vars 81) (graphGoal 81) 4 :=
  carry_of (old := 81) (rep := 25) (swaps := [99]) (by decide +kernel) bound25

def grid119 : CompactGrid := (119, 9, samplesP119, samplesQ119)
def tab119 : CompactTable := (compactCount119, compactPath119, compactLive119, compactPoolIDs119, compactBucket119)
def check119 (k : Nat) := compactNode grid119 tab119 compactDomains119 compactPerms119 k
def sliceSpecs119 : List SliceSpec := [(1, 0, 118, 0, 0, 8, 8), (2, 0, 117, 0, 0, 7, 7), (4, 0, 115, 0, 0, 7, 7), (16, 0, 103, 0, 0, 6, 6), (32, 0, 87, 0, 0, 6, 6), (64, 0, 55, 0, 0, 5, 5), (6, 0, 113, 0, 0, 5, 5), (17, 0, 102, 0, 0, 5, 5), (18, 0, 101, 0, 0, 5, 5), (20, 0, 99, 0, 0, 5, 5), (34, 0, 85, 0, 0, 5, 5), (36, 0, 83, 0, 0, 5, 5), (66, 0, 53, 0, 0, 4, 4), (68, 0, 51, 0, 0, 4, 4), (19, 0, 100, 0, 0, 4, 4), (22, 0, 97, 0, 0, 4, 4), (38, 0, 81, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains119 : ∀ d ∈ compactDomains119, Slice true (vars 119) (graphGoal 119) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(118, 8), (117, 7), (115, 7), (103, 6), (87, 6), (55, 5), (113, 5), (102, 5), (101, 5), (99, 5), (85, 5), (83, 5), (53, 4), (51, 4), (100, 4), (97, 4), (81, 4)]) (specs := sliceSpecs119)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact bound118
    · exact bound117
    · exact bound115
    · exact bound103
    · exact bound87
    · exact bound55
    · exact bound113
    · exact bound102
    · exact bound101
    · exact bound99
    · exact bound85
    · exact bound83
    · exact bound53
    · exact bound51
    · exact bound100
    · exact bound97
    · exact bound81
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs119 : properPairs (graphGoal 119) (asRow samplesP119) (asRow samplesQ119) :=
  compactPairs (g := grid119) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos119 : ∀ p ∈ compactPerms119, autoOK (graphGoal 119) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c119k4p0 : chartBlock (check119 4) 0 6 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev119k4 : chartBlock (check119 4) 0 6 = true :=
  c119k4p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c119k5p0 : chartBlock (check119 5) 0 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c119k5p1 : chartBlock (check119 5) 32 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c119k5p2 : chartBlock (check119 5) 64 6 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev119k5 : chartBlock (check119 5) 0 70 = true :=
  (chartBlock_join (a := 32) (b := 38) c119k5p0 (chartBlock_join (a := 32) (b := 6) c119k5p1 c119k5p2))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c119k6p0 : chartBlock (check119 6) 0 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c119k6p1 : chartBlock (check119 6) 32 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c119k6p2 : chartBlock (check119 6) 64 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c119k6p3 : chartBlock (check119 6) 96 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c119k6p4 : chartBlock (check119 6) 128 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c119k6p5 : chartBlock (check119 6) 160 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c119k6p6 : chartBlock (check119 6) 192 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c119k6p7 : chartBlock (check119 6) 224 7 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev119k6 : chartBlock (check119 6) 0 231 = true :=
  (chartBlock_join (a := 128) (b := 103) (chartBlock_join (a := 64) (b := 64) (chartBlock_join (a := 32) (b := 32) c119k6p0 c119k6p1) (chartBlock_join (a := 32) (b := 32) c119k6p2 c119k6p3)) (chartBlock_join (a := 64) (b := 39) (chartBlock_join (a := 32) (b := 32) c119k6p4 c119k6p5) (chartBlock_join (a := 32) (b := 7) c119k6p6 c119k6p7)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c119k7p0 : chartBlock (check119 7) 0 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c119k7p1 : chartBlock (check119 7) 32 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c119k7p2 : chartBlock (check119 7) 64 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c119k7p3 : chartBlock (check119 7) 96 24 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev119k7 : chartBlock (check119 7) 0 120 = true :=
  (chartBlock_join (a := 64) (b := 56) (chartBlock_join (a := 32) (b := 32) c119k7p0 c119k7p1) (chartBlock_join (a := 32) (b := 24) c119k7p2 c119k7p3))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c119k8p0 : chartBlock (check119 8) 0 14 = true := by
  iterate 2 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev119k8 : chartBlock (check119 8) 0 14 = true :=
  c119k8p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c119k9p0 : chartBlock (check119 9) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev119k9 : chartBlock (check119 9) 0 1 = true :=
  c119k9p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded119 : Impossible true (graphGoal 119) 9 (vars 119).toFinset := by
  apply compactRoot (g := grid119) (t := tab119) (dom := compactDomains119) (perms := compactPerms119) pairs119 domains119 autos119
  · intro k hk
    change k ≤ 9 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev119k4
    · exact lev119k5
    · exact lev119k6
    · exact lev119k7
    · exact lev119k8
    · exact lev119k9
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound119 : Lower true (vars 119) (graphGoal 119) 10 :=
  plain_low (hints := 1348) (by decide +kernel) excluded119

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound126 : Lower true (vars 126) (graphGoal 126) 10 :=
  carry_of (old := 126) (rep := 119) (swaps := [48]) (by decide +kernel) bound119

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound88 : Lower true (vars 88) (graphGoal 88) 4 :=
  carry_of (old := 88) (rep := 25) (swaps := [96]) (by decide +kernel) bound25

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound73 : Lower true (vars 73) (graphGoal 73) 4 :=
  carry_of (old := 73) (rep := 25) (swaps := [100]) (by decide +kernel) bound25

def grid89 : CompactGrid := (89, 6, samplesP89, samplesQ89)
def tab89 : CompactTable := (compactCount89, compactPath89, compactLive89, compactPoolIDs89, compactBucket89)
def check89 (k : Nat) := compactNode grid89 tab89 compactDomains89 compactPerms89 k
def sliceSpecs89 : List SliceSpec := [(1, 0, 88, 0, 0, 4, 4), (8, 0, 81, 0, 0, 4, 4), (16, 0, 73, 0, 0, 4, 4), (64, 0, 25, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains89 : ∀ d ∈ compactDomains89, Slice true (vars 89) (graphGoal 89) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(88, 4), (81, 4), (73, 4), (25, 4)]) (specs := sliceSpecs89)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact bound88
    · exact bound81
    · exact bound73
    · exact bound25
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs89 : properPairs (graphGoal 89) (asRow samplesP89) (asRow samplesQ89) :=
  compactPairs (g := grid89) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos89 : ∀ p ∈ compactPerms89, autoOK (graphGoal 89) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c89k3p0 : chartBlock (check89 3) 0 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev89k3 : chartBlock (check89 3) 0 2 = true :=
  c89k3p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c89k4p0 : chartBlock (check89 4) 0 3 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev89k4 : chartBlock (check89 4) 0 3 = true :=
  c89k4p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c89k5p0 : chartBlock (check89 5) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev89k5 : chartBlock (check89 5) 0 1 = true :=
  c89k5p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c89k6p0 : chartBlock (check89 6) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev89k6 : chartBlock (check89 6) 0 1 = true :=
  c89k6p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded89 : Impossible true (graphGoal 89) 6 (vars 89).toFinset := by
  apply compactRoot (g := grid89) (t := tab89) (dom := compactDomains89) (perms := compactPerms89) pairs89 domains89 autos89
  · intro k hk
    change k ≤ 6 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · exact lev89k3
    · exact lev89k4
    · exact lev89k5
    · exact lev89k6
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound89 : Lower true (vars 89) (graphGoal 89) 7 :=
  plain_low (hints := 3) (by decide +kernel) excluded89

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound105 : Lower true (vars 105) (graphGoal 105) 7 :=
  carry_of (old := 105) (rep := 89) (swaps := [84]) (by decide +kernel) bound89

def grid121 : CompactGrid := (121, 7, samplesP121, samplesQ121)
def tab121 : CompactTable := (compactCount121, compactPath121, compactLive121, compactPoolIDs121, compactBucket121)
def check121 (k : Nat) := compactNode grid121 tab121 compactDomains121 compactPerms121 k
def sliceSpecs121 : List SliceSpec := [(16, 0, 105, 0, 0, 7, 7)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains121 : ∀ d ∈ compactDomains121, Slice true (vars 121) (graphGoal 121) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(105, 7)]) (specs := sliceSpecs121)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound105
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs121 : properPairs (graphGoal 121) (asRow samplesP121) (asRow samplesQ121) :=
  compactPairs (g := grid121) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos121 : ∀ p ∈ compactPerms121, autoOK (graphGoal 121) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c121k7p0 : chartBlock (check121 7) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev121k7 : chartBlock (check121 7) 0 1 = true :=
  c121k7p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded121 : Impossible true (graphGoal 121) 7 (vars 121).toFinset := by
  apply compactRoot (g := grid121) (t := tab121) (dom := compactDomains121) (perms := compactPerms121) pairs121 domains121 autos121
  · intro k hk
    change k ≤ 7 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev121k7
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound121 : Lower true (vars 121) (graphGoal 121) 8 :=
  plain_low (hints := 3) (by decide +kernel) excluded121

def grid93 : CompactGrid := (93, 7, samplesP93, samplesQ93)
def tab93 : CompactTable := (compactCount93, compactPath93, compactLive93, compactPoolIDs93, compactBucket93)
def check93 (k : Nat) := compactNode grid93 tab93 compactDomains93 compactPerms93 k
def sliceSpecs93 : List SliceSpec := [(4, 0, 89, 0, 0, 7, 7)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains93 : ∀ d ∈ compactDomains93, Slice true (vars 93) (graphGoal 93) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(89, 7)]) (specs := sliceSpecs93)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound89
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs93 : properPairs (graphGoal 93) (asRow samplesP93) (asRow samplesQ93) :=
  compactPairs (g := grid93) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos93 : ∀ p ∈ compactPerms93, autoOK (graphGoal 93) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c93k7p0 : chartBlock (check93 7) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev93k7 : chartBlock (check93 7) 0 1 = true :=
  c93k7p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded93 : Impossible true (graphGoal 93) 7 (vars 93).toFinset := by
  apply compactRoot (g := grid93) (t := tab93) (dom := compactDomains93) (perms := compactPerms93) pairs93 domains93 autos93
  · intro k hk
    change k ≤ 7 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev93k7
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound93 : Lower true (vars 93) (graphGoal 93) 8 :=
  plain_low (hints := 1539) (by decide +kernel) excluded93

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound107 : Lower true (vars 107) (graphGoal 107) 8 :=
  carry_of (old := 107) (rep := 93) (swaps := [33, 84]) (by decide +kernel) bound93

def grid91 : CompactGrid := (91, 7, samplesP91, samplesQ91)
def tab91 : CompactTable := (compactCount91, compactPath91, compactLive91, compactPoolIDs91, compactBucket91)
def check91 (k : Nat) := compactNode grid91 tab91 compactDomains91 compactPerms91 k
def sliceSpecs91 : List SliceSpec := [(2, 0, 89, 0, 0, 7, 7)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains91 : ∀ d ∈ compactDomains91, Slice true (vars 91) (graphGoal 91) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(89, 7)]) (specs := sliceSpecs91)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound89
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs91 : properPairs (graphGoal 91) (asRow samplesP91) (asRow samplesQ91) :=
  compactPairs (g := grid91) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos91 : ∀ p ∈ compactPerms91, autoOK (graphGoal 91) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c91k7p0 : chartBlock (check91 7) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev91k7 : chartBlock (check91 7) 0 1 = true :=
  c91k7p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded91 : Impossible true (graphGoal 91) 7 (vars 91).toFinset := by
  apply compactRoot (g := grid91) (t := tab91) (dom := compactDomains91) (perms := compactPerms91) pairs91 domains91 autos91
  · intro k hk
    change k ≤ 7 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev91k7
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound91 : Lower true (vars 91) (graphGoal 91) 8 :=
  plain_low (hints := 67) (by decide +kernel) excluded91

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound122 : Lower true (vars 122) (graphGoal 122) 7 :=
  carry_of (old := 122) (rep := 115) (swaps := [48]) (by decide +kernel) bound115

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound58 : Lower true (vars 58) (graphGoal 58) 4 :=
  carry_of (old := 58) (rep := 51) (swaps := [48]) (by decide +kernel) bound51

def grid59 : CompactGrid := (59, 6, samplesP59, samplesQ59)
def tab59 : CompactTable := (compactCount59, compactPath59, compactLive59, compactPoolIDs59, compactBucket59)
def check59 (k : Nat) := compactNode grid59 tab59 compactDomains59 compactPerms59 k
def sliceSpecs59 : List SliceSpec := [(2, 0, 57, 0, 0, 5, 5), (32, 0, 27, 0, 0, 5, 5), (0, 2, 41, 16, 983040, 5, 4), (1, 0, 58, 0, 0, 4, 4), (8, 0, 51, 0, 0, 4, 4), (16, 2, 41, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains59 : ∀ d ∈ compactDomains59, Slice true (vars 59) (graphGoal 59) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(57, 5), (27, 5), (41, 4), (58, 4), (51, 4)]) (specs := sliceSpecs59)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl
    · exact bound57
    · exact bound27
    · exact bound41
    · exact bound58
    · exact bound51
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs59 : properPairs (graphGoal 59) (asRow samplesP59) (asRow samplesQ59) :=
  compactPairs (g := grid59) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos59 : ∀ p ∈ compactPerms59, autoOK (graphGoal 59) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c59k4p0 : chartBlock (check59 4) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev59k4 : chartBlock (check59 4) 0 1 = true :=
  c59k4p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c59k5p0 : chartBlock (check59 5) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev59k5 : chartBlock (check59 5) 0 1 = true :=
  c59k5p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c59k6p0 : chartBlock (check59 6) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev59k6 : chartBlock (check59 6) 0 1 = true :=
  c59k6p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded59 : Impossible true (graphGoal 59) 6 (vars 59).toFinset := by
  apply compactRoot (g := grid59) (t := tab59) (dom := compactDomains59) (perms := compactPerms59) pairs59 domains59 autos59
  · intro k hk
    change k ≤ 6 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev59k4
    · exact lev59k5
    · exact lev59k6
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound59 : Lower true (vars 59) (graphGoal 59) 7 :=
  plain_low (hints := 67) (by decide +kernel) excluded59

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound120 : Lower true (vars 120) (graphGoal 120) 5 :=
  carry_of (old := 120) (rep := 57) (swaps := [96]) (by decide +kernel) bound57

def grid123 : CompactGrid := (123, 9, samplesP123, samplesQ123)
def tab123 : CompactTable := (compactCount123, compactPath123, compactLive123, compactPoolIDs123, compactBucket123)
def check123 (k : Nat) := compactNode grid123 tab123 compactDomains123 compactPerms123 k
def sliceSpecs123 : List SliceSpec := [(2, 0, 121, 0, 0, 8, 8), (16, 0, 107, 0, 0, 8, 8), (32, 0, 91, 0, 0, 8, 8), (1, 0, 122, 0, 0, 7, 7), (8, 0, 115, 0, 0, 7, 7), (64, 0, 59, 0, 0, 7, 7), (0, 2, 41, 80, 252641280, 6, 4), (3, 0, 120, 0, 0, 5, 5), (9, 0, 114, 0, 0, 5, 5), (64, 2, 41, 16, 983040, 5, 4), (65, 0, 58, 0, 0, 4, 4), (72, 0, 51, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains123 : ∀ d ∈ compactDomains123, Slice true (vars 123) (graphGoal 123) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(121, 8), (107, 8), (91, 8), (122, 7), (115, 7), (59, 7), (41, 4), (120, 5), (114, 5), (58, 4), (51, 4)]) (specs := sliceSpecs123)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact bound121
    · exact bound107
    · exact bound91
    · exact bound122
    · exact bound115
    · exact bound59
    · exact bound41
    · exact bound120
    · exact bound114
    · exact bound58
    · exact bound51
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs123 : properPairs (graphGoal 123) (asRow samplesP123) (asRow samplesQ123) :=
  compactPairs (g := grid123) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos123 : ∀ p ∈ compactPerms123, autoOK (graphGoal 123) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c123k5p0 : chartBlock (check123 5) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev123k5 : chartBlock (check123 5) 0 1 = true :=
  c123k5p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c123k6p0 : chartBlock (check123 6) 0 7 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev123k6 : chartBlock (check123 6) 0 7 = true :=
  c123k6p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c123k7p0 : chartBlock (check123 7) 0 9 = true := by
  iterate 2 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev123k7 : chartBlock (check123 7) 0 9 = true :=
  c123k7p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c123k8p0 : chartBlock (check123 8) 0 3 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev123k8 : chartBlock (check123 8) 0 3 = true :=
  c123k8p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c123k9p0 : chartBlock (check123 9) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev123k9 : chartBlock (check123 9) 0 1 = true :=
  c123k9p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded123 : Impossible true (graphGoal 123) 9 (vars 123).toFinset := by
  apply compactRoot (g := grid123) (t := tab123) (dom := compactDomains123) (perms := compactPerms123) pairs123 domains123 autos123
  · intro k hk
    change k ≤ 9 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev123k5
    · exact lev123k6
    · exact lev123k7
    · exact lev123k8
    · exact lev123k9
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound123 : Lower true (vars 123) (graphGoal 123) 10 :=
  plain_low (hints := 67) (by decide +kernel) excluded123

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound125 : Lower true (vars 125) (graphGoal 125) 10 :=
  carry_of (old := 125) (rep := 123) (swaps := [33, 84]) (by decide +kernel) bound123

def grid95 : CompactGrid := (95, 8, samplesP95, samplesQ95)
def tab95 : CompactTable := (compactCount95, compactPath95, compactLive95, compactPoolIDs95, compactBucket95)
def check95 (k : Nat) := compactNode grid95 tab95 compactDomains95 compactPerms95 k
def sliceSpecs95 : List SliceSpec := [(2, 0, 93, 0, 0, 8, 8)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains95 : ∀ d ∈ compactDomains95, Slice true (vars 95) (graphGoal 95) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(93, 8)]) (specs := sliceSpecs95)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound93
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs95 : properPairs (graphGoal 95) (asRow samplesP95) (asRow samplesQ95) :=
  compactPairs (g := grid95) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos95 : ∀ p ∈ compactPerms95, autoOK (graphGoal 95) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c95k8p0 : chartBlock (check95 8) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev95k8 : chartBlock (check95 8) 0 1 = true :=
  c95k8p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded95 : Impossible true (graphGoal 95) 8 (vars 95).toFinset := by
  apply compactRoot (g := grid95) (t := tab95) (dom := compactDomains95) (perms := compactPerms95) pairs95 domains95 autos95
  · intro k hk
    change k ≤ 8 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev95k8
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound95 : Lower true (vars 95) (graphGoal 95) 9 :=
  plain_low (hints := 1603) (by decide +kernel) excluded95

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound111 : Lower true (vars 111) (graphGoal 111) 9 :=
  carry_of (old := 111) (rep := 95) (swaps := [33, 84]) (by decide +kernel) bound95

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound61 : Lower true (vars 61) (graphGoal 61) 7 :=
  carry_of (old := 61) (rep := 59) (swaps := [33, 84]) (by decide +kernel) bound59

def grid63 : CompactGrid := (63, 7, samplesP63, samplesQ63)
def tab63 : CompactTable := (compactCount63, compactPath63, compactLive63, compactPoolIDs63, compactBucket63)
def check63 (k : Nat) := compactNode grid63 tab63 compactDomains63 compactPerms63 k
def sliceSpecs63 : List SliceSpec := [(2, 0, 61, 0, 0, 7, 7)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains63 : ∀ d ∈ compactDomains63, Slice true (vars 63) (graphGoal 63) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(61, 7)]) (specs := sliceSpecs63)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound61
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs63 : properPairs (graphGoal 63) (asRow samplesP63) (asRow samplesQ63) :=
  compactPairs (g := grid63) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos63 : ∀ p ∈ compactPerms63, autoOK (graphGoal 63) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c63k7p0 : chartBlock (check63 7) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev63k7 : chartBlock (check63 7) 0 1 = true :=
  c63k7p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded63 : Impossible true (graphGoal 63) 7 (vars 63).toFinset := by
  apply compactRoot (g := grid63) (t := tab63) (dom := compactDomains63) (perms := compactPerms63) pairs63 domains63 autos63
  · intro k hk
    change k ≤ 7 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev63k7
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound63 : Lower true (vars 63) (graphGoal 63) 8 :=
  plain_low (hints := 1347) (by decide +kernel) excluded63

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound45 : Lower true (vars 45) (graphGoal 45) 5 :=
  carry_of (old := 45) (rep := 27) (swaps := [33, 84]) (by decide +kernel) bound27

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound77 : Lower true (vars 77) (graphGoal 77) 5 :=
  carry_of (old := 77) (rep := 27) (swaps := [33, 100]) (by decide +kernel) bound27

def grid79 : CompactGrid := (79, 5, samplesP79, samplesQ79)
def tab79 : CompactTable := (compactCount79, compactPath79, compactLive79, compactPoolIDs79, compactBucket79)
def check79 (k : Nat) := compactNode grid79 tab79 compactDomains79 compactPerms79 k
def sliceSpecs79 : List SliceSpec := [(2, 0, 77, 0, 0, 5, 5)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains79 : ∀ d ∈ compactDomains79, Slice true (vars 79) (graphGoal 79) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(77, 5)]) (specs := sliceSpecs79)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound77
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs79 : properPairs (graphGoal 79) (asRow samplesP79) (asRow samplesQ79) :=
  compactPairs (g := grid79) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos79 : ∀ p ∈ compactPerms79, autoOK (graphGoal 79) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c79k5p0 : chartBlock (check79 5) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev79k5 : chartBlock (check79 5) 0 1 = true :=
  c79k5p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded79 : Impossible true (graphGoal 79) 5 (vars 79).toFinset := by
  apply compactRoot (g := grid79) (t := tab79) (dom := compactDomains79) (perms := compactPerms79) pairs79 domains79 autos79
  · intro k hk
    change k ≤ 5 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev79k5
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound79 : Lower true (vars 79) (graphGoal 79) 6 :=
  plain_low (hints := 1635) (by decide +kernel) excluded79

def grid127 : CompactGrid := (127, 11, samplesP127, samplesQ127)
def tab127 : CompactTable := (compactCount127, compactPath127, compactLive127, compactPoolIDs127, compactBucket127)
def check127 (k : Nat) := compactNode grid127 tab127 compactDomains127 compactPerms127 k
def sliceSpecs127 : List SliceSpec := [(1, 0, 126, 0, 0, 10, 10), (2, 0, 125, 0, 0, 10, 10), (4, 0, 123, 0, 0, 10, 10), (8, 0, 119, 0, 0, 10, 10), (16, 0, 111, 0, 0, 9, 9), (32, 0, 95, 0, 0, 9, 9), (64, 0, 63, 0, 0, 8, 8), (34, 0, 93, 0, 0, 8, 8), (0, 2, 45, 80, 252641280, 7, 5), (0, 4, 27, 96, 267386880, 7, 5), (48, 0, 79, 0, 0, 6, 6), (16, 2, 45, 64, 251658240, 6, 5), (80, 2, 45, 0, 0, 5, 5), (96, 4, 27, 0, 0, 5, 5)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains127 : ∀ d ∈ compactDomains127, Slice true (vars 127) (graphGoal 127) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(126, 10), (125, 10), (123, 10), (119, 10), (111, 9), (95, 9), (63, 8), (93, 8), (45, 5), (27, 5), (79, 6)]) (specs := sliceSpecs127)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact bound126
    · exact bound125
    · exact bound123
    · exact bound119
    · exact bound111
    · exact bound95
    · exact bound63
    · exact bound93
    · exact bound45
    · exact bound27
    · exact bound79
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs127 : properPairs (graphGoal 127) (asRow samplesP127) (asRow samplesQ127) :=
  compactPairs (g := grid127) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos127 : ∀ p ∈ compactPerms127, autoOK (graphGoal 127) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k7p0 : chartBlock (check127 7) 0 8 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev127k7 : chartBlock (check127 7) 0 8 = true :=
  c127k7p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k8p0 : chartBlock (check127 8) 0 14 = true := by
  iterate 2 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev127k8 : chartBlock (check127 8) 0 14 = true :=
  c127k8p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k9p0 : chartBlock (check127 9) 0 11 = true := by
  iterate 2 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev127k9 : chartBlock (check127 9) 0 11 = true :=
  c127k9p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k10p0 : chartBlock (check127 10) 0 3 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev127k10 : chartBlock (check127 10) 0 3 = true :=
  c127k10p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k11p0 : chartBlock (check127 11) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev127k11 : chartBlock (check127 11) 0 1 = true :=
  c127k11p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded127 : Impossible true (graphGoal 127) 11 (vars 127).toFinset := by
  apply compactRoot (g := grid127) (t := tab127) (dom := compactDomains127) (perms := compactPerms127) pairs127 domains127 autos127
  · intro k hk
    change k ≤ 11 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev127k7
    · exact lev127k8
    · exact lev127k9
    · exact lev127k10
    · exact lev127k11
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound127 : Lower true (vars 127) (graphGoal 127) 12 :=
  plain_low (hints := 1347) (by decide +kernel) excluded127

abbrev flatValue := target
theorem usedBound : Impossible true graph 11 sevenInputs.toFinset := by simpa only [sevenInputs, show graph = graphGoal 127 by decide +kernel] using excluded127
end PEqualNP.Outside.L_meta_35826.Core7

namespace PEqualNP.Outside.L_meta_35826
namespace Paid

def zeroGate (k : Fin 4) (a b : Bool) : Bool :=
  match k.val with
  | 0 => a && b
  | 1 => a || b
  | 2 => a && !b
  | _ => !a && b

theorem zeroGate_canalizes :
    ∀ k : Fin 4,
      (∃ b c : Bool, ∀ a : Bool, zeroGate k a b = c) ∧
      (∃ a c : Bool, ∀ b : Bool, zeroGate k a b = c) := by
  decide

def singleInput {n : Nat} (i : Fin n) : Fin n → Bool :=
  fun j => decide (j = i)

def pairInput {n : Nat} (i j : Fin n) : Fin n → Bool :=
  fun k => decide (k = i ∨ k = j)

section Generic
variable {α : Type} {β : Type}

def UC (G : Fin 4 → α → α → α) (A : Fin 4 → Prop) : ℕ → (α → Prop) → α → Prop
  | 0, S, f => S f
  | t + 1, S, f => UC G A t S f ∨
      ∃ k a b, A k ∧ S a ∧ S b ∧ UC G A t (fun w => w = G k a b ∨ S w) f

theorem UC_monoS (G : Fin 4 → α → α → α) (A : Fin 4 → Prop) :
    ∀ (t : ℕ) (S S' : α → Prop) (f : α), (∀ w, S w → S' w) → UC G A t S f → UC G A t S' f
  | 0, _, _, f, h, hu => h f hu
  | t + 1, S, S', f, h, hu => by
    rcases hu with hu | ⟨k, a, b, hk, ha, hb, hu⟩
    · exact Or.inl (UC_monoS G A t S S' f h hu)
    · exact Or.inr ⟨k, a, b, hk, h a ha, h b hb,
        UC_monoS G A t _ _ f (fun w hw => hw.imp id (h w)) hu⟩

theorem UC_le {G : Fin 4 → α → α → α} {A : Fin 4 → Prop} {t t' : ℕ} {S : α → Prop} {f : α}
    (h : t ≤ t') (hu : UC G A t S f) : UC G A t' S f := by
  induction h with
  | refl => exact hu
  | step _ ih => exact Or.inl ih

theorem UC_gate {G : Fin 4 → α → α → α} {A : Fin 4 → Prop} {t : ℕ} {S : α → Prop} {f : α}
    (k : Fin 4) (a b : α) (hk : A k) (ha : S a) (hb : S b)
    (hu : UC G A t (fun w => w = G k a b ∨ S w) f) : UC G A (t + 1) S f :=
  Or.inr ⟨k, a, b, hk, ha, hb, hu⟩

theorem UC_map {G : Fin 4 → α → α → α} {G' : Fin 4 → β → β → β} {A : Fin 4 → Prop} (e : α → β)
    (he : ∀ k a b, e (G k a b) = G' k (e a) (e b)) :
    ∀ (t : ℕ) (S : α → Prop) (S' : β → Prop) (f : α), (∀ w, S w → S' (e w)) →
      UC G A t S f → UC G' A t S' (e f)
  | 0, _, _, f, h, hu => h f hu
  | t + 1, S, S', f, h, hu => by
    rcases hu with hu | ⟨k, a, b, hk, ha, hb, hu⟩
    · exact Or.inl (UC_map e he t S S' f h hu)
    · refine Or.inr ⟨k, e a, e b, hk, h a ha, h b hb, UC_map e he t _ _ f ?_ hu⟩
      intro w hw
      rcases hw with rfl | hw
      · exact Or.inl (he k a b)
      · exact Or.inr (h w hw)

def TR (G : Fin 4 → α → α → α) (C : Fin 4 → α → α → Prop) (ys : List α) (t : ℕ)
    (ws : List α) : Prop :=
  ∀ P : ℕ → List α → Prop, P 0 ys →
    (∀ s xs zs, List.Perm xs zs → P s xs → P s zs) →
    (∀ s a b r (k : Fin 4) (u : ℕ), C k a b →
      P s (List.replicate (u + 1) (G k a b) ++ r) → P (s + 1) (a :: b :: r)) →
    P t ws

section Run
variable {G : Fin 4 → α → α → α} {C : Fin 4 → α → α → Prop} {ys : List α}

theorem TR.done : TR G C ys 0 ys := fun _ d _ _ => d

theorem TR.perm {s : ℕ} {xs zs : List α} (p : List.Perm xs zs) (h : TR G C ys s xs) :
    TR G C ys s zs := fun P d q st => q s xs zs p (h P d q st)

theorem TR.step {s : ℕ} {a b : α} {r : List α} (k : Fin 4) (u : ℕ) (hc : C k a b)
    (h : TR G C ys s (List.replicate (u + 1) (G k a b) ++ r)) :
    TR G C ys (s + 1) (a :: b :: r) := fun P d q st => st s a b r k u hc (h P d q st)

theorem TR.ind {P : ℕ → List α → Prop} {t : ℕ} {ws : List α} (h : TR G C ys t ws)
    (d : P 0 ys)
    (p : ∀ s xs zs, List.Perm xs zs → TR G C ys s xs → P s xs → P s zs)
    (st : ∀ s a b r (k : Fin 4) (u : ℕ), C k a b →
      TR G C ys s (List.replicate (u + 1) (G k a b) ++ r) →
      P s (List.replicate (u + 1) (G k a b) ++ r) → P (s + 1) (a :: b :: r)) : P t ws :=
  (h (fun s xs => TR G C ys s xs ∧ P s xs) ⟨TR.done, d⟩
    (fun s xs zs hp hx => ⟨TR.perm hp hx.1, p s xs zs hp hx.1 hx.2⟩)
    (fun s a b r k u hc hx => ⟨TR.step k u hc hx.1, st s a b r k u hc hx.1 hx.2⟩)).2

theorem TR.inv {t : ℕ} {ws : List α} (h : TR G C ys t ws) :
    (t = 0 → List.Perm ws ys) ∧
    (∀ s, t = s + 1 → ∃ (k : Fin 4) (u : ℕ) (a b : α) (r : List α), C k a b ∧
      List.Perm ws (a :: b :: r) ∧ TR G C ys s (List.replicate (u + 1) (G k a b) ++ r)) := by
  refine TR.ind (P := fun t ws => (t = 0 → List.Perm ws ys) ∧
    (∀ s, t = s + 1 → ∃ (k : Fin 4) (u : ℕ) (a b : α) (r : List α), C k a b ∧
      List.Perm ws (a :: b :: r) ∧ TR G C ys s (List.replicate (u + 1) (G k a b) ++ r))) h
    ⟨fun _ => List.Perm.refl _, fun s hs => by omega⟩ ?_ ?_
  · intro s xs zs hp _ ih
    refine ⟨fun h0 => hp.symm.trans (ih.1 h0), fun s' hs => ?_⟩
    obtain ⟨k, u, a, b, r, hc, hq, hr⟩ := ih.2 s' hs
    exact ⟨k, u, a, b, r, hc, hp.symm.trans hq, hr⟩
  · intro s a b r k u hc hr _
    refine ⟨fun h0 => by omega, fun s' hs => ?_⟩
    have : s = s' := by omega
    subst this
    exact ⟨k, u, a, b, r, hc, List.Perm.refl _, hr⟩

theorem TR.len {t : ℕ} {ws : List α} (h : TR G C ys t ws) : ws.length ≤ t + ys.length := by
  refine TR.ind (P := fun t ws => ws.length ≤ t + ys.length) h (by simp) ?_ ?_
  · intro s xs zs hp _ ih
    rw [← hp.length_eq]; exact ih
  · intro s a b r k u _ _ ih
    simp only [List.length_append, List.length_replicate, List.length_cons] at ih ⊢
    omega

theorem TR.monoC {C' : Fin 4 → α → α → Prop} (hC : ∀ k a b, C k a b → C' k a b) {t : ℕ}
    {ws : List α} (h : TR G C ys t ws) : TR G C' ys t ws :=
  TR.ind (P := fun t ws => TR G C' ys t ws) h TR.done (fun _ _ _ hp _ ih => TR.perm hp ih)
    (fun _ _ _ _ k u hc _ ih => TR.step k u (hC _ _ _ hc) ih)

end Run

def strictC (G : Fin 4 → α → α → α) (z : α) (A : Fin 4 → Prop) (I : α → Prop) :
    Fin 4 → α → α → Prop :=
  fun k a b => A k ∧ I a ∧ I b ∧ a ≠ b ∧ G k a b ≠ a ∧ G k a b ≠ b ∧ G k a b ≠ z

theorem normalize [DecidableEq α] (G : Fin 4 → α → α → α) (z : α) (A : Fin 4 → Prop)
    (I : α → Prop) (hI : ∀ k a b, I a → I b → I (G k a b))
    (hz1 : ∀ k b, G k z b = z ∨ G k z b = b) (hz2 : ∀ k a, G k a z = z ∨ G k a z = a)
    (hd : ∀ k a, G k a a = z ∨ G k a a = a) :
    ∀ (t : ℕ) (S : α → Prop) (f : α), (∀ w, S w → I w) → f ≠ z → UC G A t S f →
      ∃ t', t' ≤ t ∧ ∃ ws : List α, (∀ w ∈ ws, S w ∧ w ≠ z) ∧
        TR G (strictC G z A I) [f] t' ws
  | 0, S, f, _, hf, hu => ⟨0, le_rfl, [f], by simpa using ⟨hu, hf⟩, TR.done⟩
  | t + 1, S, f, hS, hf, hu => by
    rcases hu with hu | ⟨k, a, b, hk, ha, hb, hu⟩
    · obtain ⟨t', ht, ws, hws, hr⟩ := normalize G z A I hI hz1 hz2 hd t S f hS hf hu
      exact ⟨t', by omega, ws, hws, hr⟩
    · obtain ⟨t', ht, ws, hws, hr⟩ := normalize G z A I hI hz1 hz2 hd t _ f (by
        rintro w (rfl | hw)
        · exact hI k a b (hS a ha) (hS b hb)
        · exact hS w hw) hf hu
      by_cases hg : S (G k a b)
      · refine ⟨t', by omega, ws, fun w hw => ⟨?_, (hws w hw).2⟩, hr⟩
        rcases (hws w hw).1 with rfl | h
        · exact hg
        · exact h
      by_cases hc : G k a b ∈ ws
      · have hgz : G k a b ≠ z := (hws _ hc).2
        have hga : G k a b ≠ a := fun h => hg (by rw [h]; exact ha)
        have hgb : G k a b ≠ b := fun h => hg (by rw [h]; exact hb)
        have hab : a ≠ b := by
          rintro rfl
          rcases hd k a with h | h
          · exact hgz h
          · exact hga h
        have haz : a ≠ z := by
          rintro rfl
          rcases hz1 k b with h | h
          · exact hgz h
          · exact hgb h
        have hbz : b ≠ z := by
          rintro rfl
          rcases hz2 k a with h | h
          · exact hgz h
          · exact hga h
        obtain ⟨u, hu1⟩ : ∃ u, List.count (G k a b) ws = u + 1 :=
          ⟨List.count (G k a b) ws - 1, by have := List.count_pos_iff.2 hc; omega⟩
        have hperm : ws.Perm (List.replicate (u + 1) (G k a b) ++ ws.filter (· ≠ G k a b)) := by
          rw [← hu1, ← List.filter_eq]
          have := List.filter_append_perm (fun x => decide (x = G k a b)) ws
          refine this.symm.trans ?_
          simp
        refine ⟨t' + 1, by omega, a :: b :: ws.filter (· ≠ G k a b), ?_,
          TR.step k u ⟨hk, hS a ha, hS b hb, hab, hga, hgb, hgz⟩ (TR.perm hperm hr)⟩
        intro w hw
        simp only [List.mem_cons, List.mem_filter, decide_eq_true_eq] at hw
        rcases hw with rfl | rfl | ⟨hw, hne⟩
        · exact ⟨ha, haz⟩
        · exact ⟨hb, hbz⟩
        · rcases (hws w hw).1 with h | h
          · exact absurd h hne
          · exact ⟨h, (hws w hw).2⟩
      · refine ⟨t', by omega, ws, fun w hw => ⟨?_, (hws w hw).2⟩, hr⟩
        rcases (hws w hw).1 with rfl | h
        · exact absurd hw hc
        · exact h

theorem TR.map {G : Fin 4 → α → α → α} {G' : Fin 4 → β → β → β} {C : Fin 4 → α → α → Prop}
    {C' : Fin 4 → β → β → Prop} (e : α → β) (he : ∀ k a b, e (G k a b) = G' k (e a) (e b))
    (hC : ∀ k a b, C k a b → C' k (e a) (e b)) {ys : List α} {t : ℕ} {ws : List α}
    (h : TR G C ys t ws) : TR G' C' (ys.map e) t (ws.map e) := by
  refine TR.ind (P := fun t ws => TR G' C' (ys.map e) t (ws.map e)) h TR.done
    (fun _ _ _ hp _ ih => TR.perm (hp.map e) ih) ?_
  intro s a b r k u hc _ ih
  rw [List.map_append, List.map_replicate, he] at ih
  exact TR.step k u (hC _ _ _ hc) ih

theorem TR.rel {G : Fin 4 → α → α → α} {A : Fin 4 → Prop} (R : α → α → Prop)
    (hR : ∀ k a a' b b', R a a' → R b b' → R (G k a b) (G k a' b')) {ys : List α} {t : ℕ}
    {ws : List α} (h : TR G (fun k _ _ => A k) ys t ws) :
    ∀ ws', List.Forall₂ R ws ws' →
      ∃ ys', List.Forall₂ R ys ys' ∧ TR G (fun k _ _ => A k) ys' t ws' := by
  refine TR.ind (P := fun t ws => ∀ ws', List.Forall₂ R ws ws' →
      ∃ ys', List.Forall₂ R ys ys' ∧ TR G (fun k _ _ => A k) ys' t ws') h
    (fun ws' hw => ⟨ws', hw, TR.done⟩) ?_ ?_
  · intro s xs zs hp _ ih zs' hz
    obtain ⟨xs', hx, hp'⟩ := List.perm_comp_forall₂ hp hz
    obtain ⟨ys', hy, hr⟩ := ih xs' hx
    exact ⟨ys', hy, TR.perm hp' hr⟩
  · intro s a b r k u hc _ ih ws' hw
    obtain ⟨a', t1, ha, ht1, rfl⟩ := List.forall₂_cons_left_iff.1 hw
    obtain ⟨b', r', hb, hr', rfl⟩ := List.forall₂_cons_left_iff.1 ht1
    have h1 : List.Forall₂ R (List.replicate (u + 1) (G k a b) ++ r)
        (List.replicate (u + 1) (G k a' b') ++ r') := by
      refine List.rel_append ?_ hr'
      generalize u + 1 = n
      induction n with
      | zero => exact List.Forall₂.nil
      | succ n ih => exact List.Forall₂.cons (hR k a a' b b' ha hb) ih
    obtain ⟨ys', hy, hrun⟩ := ih _ h1
    exact ⟨ys', hy, TR.step k u hc hrun⟩

end Generic

abbrev BF := (Fin 8 → Bool) → Bool

def gF (k : Fin 4) (a b : BF) : BF := fun x => zeroGate k (a x) (b x)

def var (i : Fin 8) : BF := fun x => x i

def zF : BF := fun _ => false

def rst (p : Fin 8) (a : BF) : BF := fun x => a (Function.update x p false)

def ThrL (V : Fin 8 → Prop) (F : BF) : Prop :=
  (∀ i, V i → F (singleInput i) = false) ∧
    ∀ i j, V i → V j → i ≠ j → F (pairInput i j) = true

theorem gF_zero_left (k : Fin 4) (b : BF) : gF k zF b = zF ∨ gF k zF b = b := by
  fin_cases k
  · exact Or.inl (funext fun x => by simp [gF, zF, zeroGate])
  · exact Or.inr (funext fun x => by simp [gF, zF, zeroGate])
  · exact Or.inl (funext fun x => by simp [gF, zF, zeroGate])
  · exact Or.inr (funext fun x => by simp [gF, zF, zeroGate])

theorem gF_zero_right (k : Fin 4) (a : BF) : gF k a zF = zF ∨ gF k a zF = a := by
  fin_cases k
  · exact Or.inl (funext fun x => by simp [gF, zF, zeroGate])
  · exact Or.inr (funext fun x => by simp [gF, zF, zeroGate])
  · exact Or.inr (funext fun x => by simp [gF, zF, zeroGate])
  · exact Or.inl (funext fun x => by simp [gF, zF, zeroGate])

theorem gF_self (k : Fin 4) (a : BF) : gF k a a = zF ∨ gF k a a = a := by
  fin_cases k
  · exact Or.inr (funext fun x => by simp [gF, zeroGate])
  · exact Or.inr (funext fun x => by simp [gF, zeroGate])
  · exact Or.inl (funext fun x => by simp [gF, zF, zeroGate])
  · exact Or.inl (funext fun x => by simp [gF, zF, zeroGate])

theorem gF_zero_zero (k : Fin 4) : gF k zF zF = zF := by
  fin_cases k <;> exact funext fun x => by simp [gF, zF, zeroGate]

theorem upd_single {i p : Fin 8} (h : i ≠ p) :
    Function.update (singleInput i) p false = singleInput i := by
  funext m
  by_cases hm : m = p
  · subst hm; simp [singleInput, Ne.symm h]
  · simp [Function.update_of_ne hm]

theorem upd_pair {i j p : Fin 8} (hi : i ≠ p) (hj : j ≠ p) :
    Function.update (pairInput i j) p false = pairInput i j := by
  funext m
  by_cases hm : m = p
  · subst hm; simp [pairInput, Ne.symm hi, Ne.symm hj]
  · simp [Function.update_of_ne hm]

theorem rst_var_self (p : Fin 8) : rst p (var p) = zF :=
  funext fun x => by simp [rst, var, zF]

theorem rst_var_ne {i p : Fin 8} (h : i ≠ p) : rst p (var i) = var i :=
  funext fun x => by simp [rst, var, Function.update_of_ne h]

theorem var_inj {i j : Fin 8} (h : var i = var j) : i = j := by
  have := congrFun h (singleInput i)
  exact (by simpa [var, singleInput] using this : j = i).symm

theorem TRF_det {C : Fin 4 → BF → BF → Prop} {ys : List BF} {s : ℕ} {ws : List BF}
    (h : TR gF C ys s ws) (x x' : Fin 8 → Bool) :
    (∀ w ∈ ws, w x = w x') → ∀ y ∈ ys, y x = y x' := by
  refine TR.ind (P := fun _ ws => (∀ w ∈ ws, w x = w x') → ∀ y ∈ ys, y x = y x') h
    (fun h => h) ?_ ?_
  · intro s xs zs hp _ ih hz
    exact ih fun t ht => hz t (hp.mem_iff.1 ht)
  · intro s a b r k u _ _ ih hz
    apply ih
    intro t ht
    rcases List.mem_append.1 ht with ht | ht
    · rw [List.eq_of_mem_replicate ht]
      show zeroGate k (a x) (b x) = zeroGate k (a x') (b x')
      rw [hz a (by simp), hz b (by simp)]
    · exact hz t (by simp [ht])

def dcount (p : Fin 8) (ws : List BF) : ℕ := ws.countP fun w => decide (rst p w = zF)

theorem dcount_cons (p : Fin 8) (a : BF) (l : List BF) :
    dcount p (a :: l) = dcount p l + if rst p a = zF then 1 else 0 := by
  simp [dcount, List.countP_cons]

theorem dcount_rep (p : Fin 8) (n : ℕ) (g : BF) (r : List BF) :
    dcount p (List.replicate n g ++ r) = (if rst p g = zF then n else 0) + dcount p r := by
  simp only [dcount, List.countP_append, List.countP_replicate]
  split_ifs <;> simp_all

theorem pot_dead {A : Fin 4 → Prop} (p : Fin 8) {F : BF} (hF : rst p F ≠ zF) {s : ℕ}
    {ws : List BF} (h : TR gF (fun k _ _ => A k) [F] s ws) :
    dcount p ws ≤ s ∧ ∀ S : BF → Prop, (∀ w ∈ ws, rst p w ≠ zF → S (rst p w)) →
      UC gF A (s - dcount p ws) S (rst p F) := by
  refine TR.ind (P := fun s ws => dcount p ws ≤ s ∧ ∀ S : BF → Prop,
    (∀ w ∈ ws, rst p w ≠ zF → S (rst p w)) → UC gF A (s - dcount p ws) S (rst p F)) h ?_ ?_ ?_
  · refine ⟨by simp [dcount, hF], fun S hS => ?_⟩
    have : dcount p [F] = 0 := by simp [dcount, hF]
    rw [this]
    exact hS F (by simp) hF
  · intro s xs zs hp _ ih
    have hc : dcount p zs = dcount p xs := (hp.countP_eq _).symm
    rw [hc]
    exact ⟨ih.1, fun S hS => ih.2 S fun w hw => hS w (hp.mem_iff.1 hw)⟩
  · intro s a b r k u hk _ ih
    obtain ⟨ih1, ih2⟩ := ih
    have hg : rst p (gF k a b) = gF k (rst p a) (rst p b) := rfl
    rw [dcount_rep] at ih1 ih2
    rw [dcount_cons, dcount_cons]
    have hmem : ∀ (S : BF → Prop), (∀ w ∈ a :: b :: r, rst p w ≠ zF → S (rst p w)) →
        ∀ w ∈ r, rst p w ≠ zF → S (rst p w) := fun S hS w hw => hS w (by simp [hw])
    by_cases ha : rst p a = zF <;> by_cases hb : rst p b = zF
    · have hgz : rst p (gF k a b) = zF := by rw [hg, ha, hb, gF_zero_zero]
      simp only [hgz, ha, hb, ite_true] at ih1 ih2 ⊢
      refine ⟨by omega, fun S hS => UC_le (by omega) (ih2 S ?_)⟩
      intro w hw hwz
      rcases List.mem_append.1 hw with hw | hw
      · exact absurd (List.eq_of_mem_replicate hw ▸ hgz) hwz
      · exact hmem S hS w hw hwz
    · by_cases hgz : rst p (gF k a b) = zF
      · simp only [hgz, ha, hb, ite_true, ite_false] at ih1 ih2 ⊢
        refine ⟨by omega, fun S hS => UC_le (by omega) (ih2 S ?_)⟩
        intro w hw hwz
        rcases List.mem_append.1 hw with hw | hw
        · exact absurd (List.eq_of_mem_replicate hw ▸ hgz) hwz
        · exact hmem S hS w hw hwz
      · have hgb : rst p (gF k a b) = rst p b := by
          rcases gF_zero_left k (rst p b) with h | h
          · exact absurd (by rw [hg, ha, h]) hgz
          · rw [hg, ha, h]
        simp only [hgz, ha, hb, ite_true, ite_false] at ih1 ih2 ⊢
        refine ⟨by omega, fun S hS => UC_le (by omega) (ih2 S ?_)⟩
        intro w hw hwz
        rcases List.mem_append.1 hw with hw | hw
        · rw [List.eq_of_mem_replicate hw, hgb]
          exact hS b (by simp) hb
        · exact hmem S hS w hw hwz
    · by_cases hgz : rst p (gF k a b) = zF
      · simp only [hgz, ha, hb, ite_true, ite_false] at ih1 ih2 ⊢
        refine ⟨by omega, fun S hS => UC_le (by omega) (ih2 S ?_)⟩
        intro w hw hwz
        rcases List.mem_append.1 hw with hw | hw
        · exact absurd (List.eq_of_mem_replicate hw ▸ hgz) hwz
        · exact hmem S hS w hw hwz
      · have hga : rst p (gF k a b) = rst p a := by
          rcases gF_zero_right k (rst p a) with h | h
          · exact absurd (by rw [hg, hb, h]) hgz
          · rw [hg, hb, h]
        simp only [hgz, ha, hb, ite_true, ite_false] at ih1 ih2 ⊢
        refine ⟨by omega, fun S hS => UC_le (by omega) (ih2 S ?_)⟩
        intro w hw hwz
        rcases List.mem_append.1 hw with hw | hw
        · rw [List.eq_of_mem_replicate hw, hga]
          exact hS a (by simp) ha
        · exact hmem S hS w hw hwz
    · by_cases hgz : rst p (gF k a b) = zF
      · simp only [hgz, ha, hb, ite_true, ite_false] at ih1 ih2 ⊢
        refine ⟨by omega, fun S hS => UC_le (by omega) (ih2 S ?_)⟩
        intro w hw hwz
        rcases List.mem_append.1 hw with hw | hw
        · exact absurd (List.eq_of_mem_replicate hw ▸ hgz) hwz
        · exact hmem S hS w hw hwz
      · simp only [hgz, ha, hb, ite_false] at ih1 ih2 ⊢
        refine ⟨by omega, fun S hS => ?_⟩
        have h1 := ih2 (fun w => w = gF k (rst p a) (rst p b) ∨ S w) (by
          intro w hw hwz
          rcases List.mem_append.1 hw with hw | hw
          · exact Or.inl (by rw [List.eq_of_mem_replicate hw, hg])
          · exact Or.inr (hmem S hS w hw hwz))
        have h2 := UC_gate k (rst p a) (rst p b) hk (hS a (by simp) ha) (hS b (by simp) hb) h1
        exact UC_le (by omega) h2

def MonoA : Fin 4 → Prop := fun k => k.val < 2

abbrev MR (ys : List BF) (s : ℕ) (ws : List BF) : Prop := TR gF (fun k _ _ => MonoA k) ys s ws

def outF (ys : List BF) : BF := fun x => ys.any fun y => y x

def otop (x : Fin 8) : BF := fun p => decide (∃ i, i ≠ x ∧ p i = true)

theorem mono_cases (k : Fin 4) (hk : MonoA k) : k = 0 ∨ k = 1 := by
  fin_cases k <;> simp_all [MonoA]

theorem gF_and (a b : BF) : gF 0 a b = fun p => a p && b p := rfl

theorem gF_or (a b : BF) : gF 1 a b = fun p => a p || b p := rfl

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def gv (g : Gate) (W : List BF) : BF :=
  fun x => g.op.eval (g.inputs.map fun i => (W.getD i zF) x)

def wiresF : List Gate → List BF → List BF
  | [], W => W
  | g :: gs, W => wiresF gs (W ++ [gv g W])

theorem getD_map_x (W : List BF) (i : ℕ) (x : Fin 8 → Bool) :
    (W.map fun w => w x).getD i false = (W.getD i zF) x := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases W[i]? <;> rfl

theorem wires_eq (x : Fin 8 → Bool) : ∀ (gs : List Gate) (W : List BF),
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (W.map fun w => w x) = (wiresF gs W).map fun w => w x
  | [], W => rfl
  | g :: gs, W => by
    simp only [List.foldl_cons, wiresF]
    rw [← wires_eq x gs (W ++ [gv g W])]
    congr 1
    simp only [List.map_append, List.map_cons, List.map_nil, gv, getD_map_x]

theorem getD_mem (W : List BF) (i : ℕ) : W.getD i zF ∈ W ∨ W.getD i zF = zF := by
  rw [List.getD_eq_getElem?_getD]
  rcases h : W[i]? with _ | a
  · exact Or.inr rfl
  · exact Or.inl (List.mem_of_getElem? h)

theorem gate_form (g : Gate) (W : List BF)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hl : g.inputs.length ≤ 2) :
    gv g W = zF ∨ gv g W = (fun _ => true) ∨
    (∃ a, (a ∈ W ∨ a = zF) ∧ gv g W = a) ∨
    (∃ a, (a ∈ W ∨ a = zF) ∧ gv g W = fun x => !a x) ∨
    (∃ k a b, MonoA k ∧ (a ∈ W ∨ a = zF) ∧ (b ∈ W ∨ b = zF) ∧ gv g W = gF k a b) := by
  rcases g with ⟨op, ins⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases ins with _ | ⟨i, _ | ⟨j, _ | ⟨l, rest⟩⟩⟩
  · rcases hop with rfl | rfl | rfl
    · exact Or.inr (Or.inl (funext fun x => by simp [gv, GateOp.eval]))
    · exact Or.inl (funext fun x => by simp [gv, GateOp.eval, zF])
    · exact Or.inr (Or.inl (funext fun x => by simp [gv, GateOp.eval]))
  · rcases hop with rfl | rfl | rfl
    · exact Or.inr (Or.inr (Or.inl ⟨W.getD i zF, getD_mem W i,
        funext fun x => by simp [gv, GateOp.eval]⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨W.getD i zF, getD_mem W i,
        funext fun x => by simp [gv, GateOp.eval]⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨W.getD i zF, getD_mem W i,
        funext fun x => by simp [gv, GateOp.eval]⟩)))
  · rcases hop with rfl | rfl | rfl
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨0, W.getD i zF, W.getD j zF, by simp [MonoA],
        getD_mem W i, getD_mem W j, funext fun x => by simp [gv, GateOp.eval, gF_and]⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨1, W.getD i zF, W.getD j zF, by simp [MonoA],
        getD_mem W i, getD_mem W j, funext fun x => by simp [gv, GateOp.eval, gF_or]⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨W.getD i zF, getD_mem W i,
        funext fun x => by simp [gv, GateOp.eval]⟩)))
  · simp at hl

def ori (w : BF) : BF := fun x => xor (w x) (w fun _ => false)

theorem ori_zero : ori zF = zF := funext fun x => by simp [ori, zF]

theorem ori_true : ori (fun _ => true) = zF := funext fun x => by simp [ori, zF]

theorem ori_not (a : BF) : ori (fun x => !a x) = ori a :=
  funext fun x => by
    simp only [ori]
    cases a x <;> cases a (fun _ => false) <;> rfl

theorem ori_zp {w : BF} (h : w (fun _ => false) = false) : ori w = w :=
  funext fun x => by simp [ori, h]

theorem ori_gate (k : Fin 4) (hk : MonoA k) (a b : BF) :
    ∃ k', ori (gF k a b) = gF k' (ori a) (ori b) := by
  rcases mono_cases k hk with rfl | rfl
  · cases hu : a (fun _ => false) <;> cases hv : b (fun _ => false)
    · exact ⟨0, funext fun x => by
        cases hax : a x <;> cases hbx : b x <;> simp [ori, gF, zeroGate, hu, hv, hax, hbx]⟩
    · exact ⟨2, funext fun x => by
        cases hax : a x <;> cases hbx : b x <;> simp [ori, gF, zeroGate, hu, hv, hax, hbx]⟩
    · exact ⟨3, funext fun x => by
        cases hax : a x <;> cases hbx : b x <;> simp [ori, gF, zeroGate, hu, hv, hax, hbx]⟩
    · exact ⟨1, funext fun x => by
        cases hax : a x <;> cases hbx : b x <;> simp [ori, gF, zeroGate, hu, hv, hax, hbx]⟩
  · cases hu : a (fun _ => false) <;> cases hv : b (fun _ => false)
    · exact ⟨1, funext fun x => by
        cases hax : a x <;> cases hbx : b x <;> simp [ori, gF, zeroGate, hu, hv, hax, hbx]⟩
    · exact ⟨3, funext fun x => by
        cases hax : a x <;> cases hbx : b x <;> simp [ori, gF, zeroGate, hu, hv, hax, hbx]⟩
    · exact ⟨2, funext fun x => by
        cases hax : a x <;> cases hbx : b x <;> simp [ori, gF, zeroGate, hu, hv, hax, hbx]⟩
    · exact ⟨0, funext fun x => by
        cases hax : a x <;> cases hbx : b x <;> simp [ori, gF, zeroGate, hu, hv, hax, hbx]⟩

abbrev GOK (gs : List Gate) : Prop :=
  ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem ori_key (g : Gate) (W : List BF) (S : BF → Prop)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hl : g.inputs.length ≤ 2) (hW : ∀ w ∈ W, ori w = zF ∨ S (ori w)) :
    (ori (gv g W) = zF ∨ S (ori (gv g W))) ∨
      ∃ k a b, S a ∧ S b ∧ ori (gv g W) = gF k a b := by
  have hWz : ∀ a, (a ∈ W ∨ a = zF) → ori a = zF ∨ S (ori a) := by
    rintro a (h | rfl)
    · exact hW a h
    · exact Or.inl ori_zero
  rcases gate_form g W hop hl with h | h | ⟨a, ha, h⟩ | ⟨a, ha, h⟩ | ⟨k, a, b, hk, ha, hb, h⟩
  · rw [h]; exact Or.inl (Or.inl ori_zero)
  · rw [h]; exact Or.inl (Or.inl ori_true)
  · rw [h]; exact Or.inl (hWz a ha)
  · rw [h, ori_not]; exact Or.inl (hWz a ha)
  · obtain ⟨k', hk'⟩ := ori_gate k hk a b
    rw [h, hk']
    rcases hWz a ha with ha1 | ha1
    · rw [ha1]
      rcases gF_zero_left k' (ori b) with e | e
      · rw [e]; exact Or.inl (Or.inl rfl)
      · rw [e]; exact Or.inl (hWz b hb)
    rcases hWz b hb with hb1 | hb1
    · rw [hb1]
      rcases gF_zero_right k' (ori a) with e | e
      · rw [e]; exact Or.inl (Or.inl rfl)
      · rw [e]; exact Or.inl (Or.inr ha1)
    exact Or.inr ⟨k', ori a, ori b, ha1, hb1, rfl⟩

def graphTable (a : ℕ) (x : Fin 8 → Bool) : Bool := a.testBit (tableIndex x)

def assignment (a : ℕ) (i : Fin 8) : Bool := a.testBit i.val

def isNot : GateOp → Bool
  | .not => true
  | _ => false

theorem isNot_true (op : GateOp) : isNot op = true ↔ op = GateOp.not := by
  cases op <;> simp [isNot]

def countBinary : List Gate → ℕ
  | [] => 0
  | g :: gs => countBinary gs + if isNot g.op then 0 else 1

theorem countBinary_le (gs : List Gate) : countBinary gs ≤ gs.length := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp only [countBinary, List.length_cons]
    split <;> omega

theorem countBinary_lt (gs : List Gate) (h : ∃ g ∈ gs, g.op = GateOp.not) :
    countBinary gs < gs.length := by
  induction gs with
  | nil => simp at h
  | cons g gs ih =>
    obtain ⟨a, ha, he⟩ := h
    rcases List.mem_cons.1 ha with rfl | ha
    · have hb := countBinary_le gs
      simp [countBinary, he, isNot, Nat.lt_succ_of_le hb]
    · have hb := ih ⟨a, ha, he⟩
      simp only [countBinary, List.length_cons]
      split <;> omega

theorem not_key (g : Gate) (W : List BF) (S : BF → Prop) (hop : g.op = GateOp.not)
    (hW : ∀ w ∈ W, ori w = zF ∨ S (ori w)) :
    ori (gv g W) = zF ∨ S (ori (gv g W)) := by
  obtain ⟨op, ins⟩ := g
  change op = GateOp.not at hop
  subst op
  cases ins with
  | nil => exact Or.inl ori_true
  | cons i rest =>
    have he : gv ⟨GateOp.not, i :: rest⟩ W = fun x => !(W.getD i zF) x := rfl
    rw [he, ori_not]
    rcases getD_mem W i with h | h
    · exact hW _ h
    · rw [h]; exact Or.inl ori_zero

theorem trans_binary : ∀ (gs : List Gate) (W : List BF) (S : BF → Prop), GOK gs →
    (∀ w ∈ W, ori w = zF ∨ S (ori w)) → ∀ o : ℕ,
    ori ((wiresF gs W).getD o zF) = zF ∨
      UC gF (fun _ => True) (countBinary gs) S (ori ((wiresF gs W).getD o zF))
  | [], W, S, _, hw, o => by
    rcases getD_mem W o with h | h
    · exact hw _ h
    · rw [wiresF, h]; exact Or.inl ori_zero
  | g :: gs, W, S, hg, hw, o => by
    have hg1 := hg g (by simp)
    have hg2 : GOK gs := fun g' h => hg g' (by simp [h])
    have free (h : ori (gv g W) = zF ∨ S (ori (gv g W))) :=
      trans_binary gs (W ++ [gv g W]) S hg2 (by
        intro w hm
        rcases List.mem_append.1 hm with hm | hm
        · exact hw w hm
        · rw [List.mem_singleton.1 hm]; exact h) o
    simp only [wiresF, countBinary]
    by_cases hn : g.op = GateOp.not
    · simpa [hn, isNot] using free (not_key g W S hn hw)
    · rw [if_neg (fun ht => hn ((isNot_true g.op).1 ht))]
      rcases ori_key g W S hg1.1 hg1.2 hw with h | ⟨k, a, b, ha, hb, h⟩
      · exact (free h).imp id (UC_le (Nat.le_succ _))
      · have next := trans_binary gs (W ++ [gv g W]) (fun w => w = gF k a b ∨ S w) hg2 (by
          intro w hm
          rcases List.mem_append.1 hm with hm | hm
          · exact (hw w hm).imp id Or.inr
          · rw [List.mem_singleton.1 hm]; exact Or.inr (Or.inl h)) o
        exact next.imp id (UC_gate k a b trivial ha hb)

def sourceVars (xs : Finset (Fin 8)) (f : BF) : Prop := ∃ i ∈ xs, f = var i

theorem remove_var (F : BF) (p : Fin 8) (xs : Finset (Fin 8)) (s : ℕ)
    (hd : ∃ x, rst p F x ≠ F x) (hn : rst p F ≠ zF)
    (h : UC gF (fun _ => True) s (sourceVars xs) F) :
    ∃ t, t + 1 ≤ s ∧ UC gF (fun _ => True) t (sourceVars (xs.erase p)) (rst p F) := by
  have hf : F ≠ zF := fun e => hn (by rw [e]; rfl)
  obtain ⟨k, hk, ws, hws, run⟩ := normalize gF zF (fun _ => True) (fun _ => True)
    (fun _ _ _ _ _ => trivial) gF_zero_left gF_zero_right gF_self
    s (sourceVars xs) F (fun _ _ => trivial) hf h
  have hp : var p ∈ ws := by
    by_contra hmiss
    obtain ⟨x, hx⟩ := hd
    apply hx
    exact TRF_det run (Function.update x p false) x (by
      intro w hw
      obtain ⟨i, _, rfl⟩ := (hws w hw).1
      have hi : i ≠ p := fun e => hmiss (e ▸ hw)
      exact Function.update_of_ne hi false x) F (by simp)
  have hc : 1 ≤ dcount p ws := by
    apply Nat.succ_le_of_lt
    unfold dcount
    exact List.countP_pos_iff.2 ⟨var p, hp, by simp [rst_var_self]⟩
  have dr := pot_dead p hn (TR.monoC (fun _ _ _ _ => trivial) run)
  refine ⟨k - dcount p ws, by omega, dr.2 (sourceVars (xs.erase p)) ?_⟩
  intro w hw hz
  obtain ⟨i, hi, rfl⟩ := (hws w hw).1
  have hne : i ≠ p := fun e => hz (e ▸ rst_var_self p)
  exact ⟨i, Finset.mem_erase.2 ⟨hne, hi⟩, rst_var_ne hne⟩

end Paid

namespace SignedLift

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev zeroGate := Paid.zeroGate
abbrev UC {α : Type} := @Paid.UC α
abbrev BF (n : Nat) := (Fin n → Bool) → Bool

def signed {n : Nat} (k : Fin 4) (a b : BF n) : BF n := fun x => zeroGate k (a x) (b x)

def binary (g : Gate) : Bool := match g.op with | .not => false | _ => true

def ready {n : Nat} (gs : List Gate) (j : Nat) (f : BF n) : Prop :=
  j < n + gs.length ∧ ∀ x : Fin n → Bool, Circuit.eval ⟨gs,j⟩ (List.ofFn x) = f x

def legal (g : Gate) : Prop :=
  (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def addWire (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]

theorem wireLength {n : Nat} (gs : List Gate) (x : Fin n → Bool) :
    (Circuit.wires ⟨gs,0⟩ (List.ofFn x)).length = n + gs.length := by
  have aux (v : List Bool) (ls : List Gate) : (ls.foldl addWire v).length = v.length + ls.length := by
    induction ls generalizing v with
    | nil => simp
    | cons g ls ih => simp [List.foldl_cons,ih,addWire]; omega
  exact (aux _ _).trans (by simp)

theorem stepW (gs : List Gate) (g : Gate) (x : List Bool) :
    Circuit.wires ⟨gs ++ [g],0⟩ x = addWire (Circuit.wires ⟨gs,0⟩ x) g := by
  simp [Circuit.wires, addWire, List.foldl_append]

theorem keep {n j} {gs : List Gate} {f : BF n} (h : ready gs j f) (g : Gate) :
    ready (gs ++ [g]) j f := by
  refine ⟨by have := h.1; simp; omega, ?_⟩
  intro x
  change (Circuit.wires ⟨gs ++ [g],0⟩ _).getD j false = _
  rw [stepW]
  exact (List.getD_append _ _ _ _ (by rw [wireLength];exact h.1)).trans (h.2 x)

theorem nextWire {n} (gs : List Gate) (g : Gate) (f : BF n)
    (eval : ∀ x : Fin n → Bool, g.op.eval (g.inputs.map (fun j =>
      (Circuit.wires ⟨gs,0⟩ (List.ofFn x)).getD j false)) = f x) :
    ready (gs ++ [g]) (n + gs.length) f := by
  refine ⟨by simp, ?_⟩
  intro x
  change (Circuit.wires ⟨gs ++ [g],0⟩ _).getD (n + gs.length) false = _
  rw [stepW,← wireLength gs x]
  simpa [addWire] using eval x

theorem negative {n j} {gs : List Gate} {f : BF n} (h : ready gs j f) :
    ready (gs ++ [⟨.not,[j]⟩]) (n+gs.length) (fun x => !f x) := by
  apply nextWire
  intro x
  have hx : (Circuit.wires ⟨gs,0⟩ (List.ofFn x)).getD j false = f x := h.2 x
  simp only [GateOp.eval,List.map_cons,List.map_nil,List.headD_cons,hx]

theorem conjWire {n i j} {gs : List Gate} {a b : BF n} (ha : ready gs i a) (hb : ready gs j b) :
    ready (gs ++ [⟨.and,[i,j]⟩]) (n+gs.length) (fun x => a x && b x) := by
  apply nextWire
  intro x
  have h1 : (Circuit.wires ⟨gs,0⟩ (List.ofFn x)).getD i false = a x := ha.2 x
  have h2 : (Circuit.wires ⟨gs,0⟩ (List.ofFn x)).getD j false = b x := hb.2 x
  simp only [GateOp.eval,List.map_cons,List.map_nil,List.all_cons,List.all_nil,id_eq,h1,h2,Bool.and_true]

theorem disjWire {n i j} {gs : List Gate} {a b : BF n} (ha : ready gs i a) (hb : ready gs j b) :
    ready (gs ++ [⟨.or,[i,j]⟩]) (n+gs.length) (fun x => a x || b x) := by
  apply nextWire
  intro x
  have h1 : (Circuit.wires ⟨gs,0⟩ (List.ofFn x)).getD i false = a x := ha.2 x
  have h2 : (Circuit.wires ⟨gs,0⟩ (List.ofFn x)).getD j false = b x := hb.2 x
  simp only [GateOp.eval,List.map_cons,List.map_nil,List.any_cons,List.any_nil,id_eq,h1,h2,Bool.or_false]

theorem shift {n j} {gs : List Gate} {f : BF n} (h : ready gs j f) (tail : List Gate) :
    ready (gs ++ tail) j f := by
  induction tail using List.reverseRecOn with
  | nil => simpa using h
  | append_singleton _ g ih => simpa [List.append_assoc] using keep ih g

theorem produce {n i j} {gs : List Gate} {a b : BF n} (k : Fin 4)
    (ha : ready gs i a) (hb : ready gs j b) :
    ∃ (tail : List Gate) (r : Nat), (∀ g ∈ tail, legal g) ∧ tail.countP binary = 1 ∧
      ready (gs ++ tail) r (signed k a b) := by
  fin_cases k
  · exact ⟨[⟨.and,[i,j]⟩],_,by simp [legal],rfl,conjWire ha hb⟩
  · exact ⟨[⟨.or,[i,j]⟩],_,by simp [legal],rfl,disjWire ha hb⟩
  · let v : Gate := ⟨.not,[j]⟩
    refine ⟨[v,⟨.and,[i,n+gs.length]⟩],n+(gs++[v]).length,by simp [legal,v],rfl,?_⟩
    change ready _ _ (fun x => a x && !(b x))
    simpa only [List.append_assoc,List.singleton_append] using conjWire (keep ha v) (negative hb)
  · let v : Gate := ⟨.not,[i]⟩
    refine ⟨[v,⟨.and,[n+gs.length,j]⟩],n+(gs++[v]).length,by simp [legal,v],rfl,?_⟩
    change ready _ _ (fun x => !(a x) && b x)
    simpa only [List.append_assoc,List.singleton_append] using conjWire (negative ha) (keep hb v)

theorem realizeAux {n t} (S : BF n → Prop) (f : BF n)
    (h : UC signed (fun _ => True) t S f) (gs : List Gate)
    (fan : ∀ g ∈ gs, legal g) (pool : ∀ w, S w → ∃ i, ready gs i w) :
    ∃ C : Circuit, FanInTwo C ∧ C.gates.countP binary ≤ gs.countP binary + t ∧ circuitFun n C = f := by
  induction t generalizing gs S with
  | zero =>
    obtain ⟨i,e⟩ := pool f h
    exact ⟨⟨gs,i⟩,fan,by simp,funext e.2⟩
  | succ t ih =>
    rcases h with skip | ⟨k,a,b,_,ha,hb,more⟩
    · obtain ⟨C,fanC,lo,eq⟩ := ih S skip gs fan pool
      exact ⟨C,fanC,by omega,eq⟩
    obtain ⟨i,hi⟩ := pool a ha
    obtain ⟨j,hj⟩ := pool b hb
    obtain ⟨tail,r,ok,cost,new⟩ := produce k hi hj
    obtain ⟨C,fanC,lo,eq⟩ := ih _ more (gs++tail)
      (fun g hg => (List.mem_append.mp hg).elim (fan g) (ok g)) (by
        rintro w (rfl | hw)
        · exact ⟨r,new⟩
        · obtain ⟨v,ev⟩ := pool w hw
          exact ⟨v,shift ev tail⟩)
    rw [List.countP_append,cost] at lo
    exact ⟨C,fanC,by omega,eq⟩

theorem realize {n t} (f : BF n)
    (h : UC signed (fun _ => True) t (fun w => ∃ i : Fin n, w = fun x => x i) f) :
    ∃ C : Circuit, FanInTwo C ∧ C.gates.countP binary ≤ t ∧ circuitFun n C = f := by
  have p : ∀ w : BF n, (∃ i : Fin n, w = fun x => x i) → ∃ j, ready [] j w := by
    rintro w ⟨i,rfl⟩
    exact ⟨i.val,by simp [ready,i.isLt,Circuit.eval,Circuit.wires]⟩
  simpa using realizeAux _ f h [] (by simp) p

end SignedLift
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def target8 (x : Fin 8 → Bool) : Bool := (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 0 && x 7) || (x 1 && x 4) || (x 1 && x 7) || (x 2 && x 5) || (x 2 && x 7) || (x 3 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 4 && x 7) || (x 5 && x 6) || (x 5 && x 7) || (x 6 && x 7)
def witness : List Gate := [⟨.or, [0,1]⟩, ⟨.or, [4,7]⟩, ⟨.and, [8,9]⟩, ⟨.or, [0,2]⟩, ⟨.or, [11,6]⟩, ⟨.or, [5,7]⟩, ⟨.and, [12,13]⟩, ⟨.or, [0,3]⟩, ⟨.or, [15,4]⟩, ⟨.or, [16,5]⟩, ⟨.or, [6,7]⟩, ⟨.and, [17,18]⟩, ⟨.or, [10,14]⟩, ⟨.or, [20,19]⟩]
theorem witnessBasis : ∀ g ∈ witness, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem witnessCorrect : ∀ x : Fin 8 → Bool, Circuit.eval ⟨witness, 21⟩ (List.ofFn x) = target8 x := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem graph_correct : ∀ x : Fin 8 → Bool, target8 x = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
open Paid in
theorem lower_using_binary
    (coreLow : ∀ C : Circuit, FanInTwo C → circuitFun 7 C = Core7.flatValue →
        12 ≤ C.gates.countP SignedLift.binary)
    (gates : List Gate) (o : ℕ) (legal : GOK gates)
    (comp : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates,o⟩ (List.ofFn x) = target8 x)
    (hasNot : ∃ g ∈ gates, g.op = GateOp.not) : 14 ≤ gates.length := by
  have hg : (wiresF gates (List.ofFn var)).getD o zF = target8 := by
    funext x
    rw [← comp x, ← getD_map_x, ← wires_eq]
    simp only [Circuit.eval, Circuit.wires, List.map_ofFn]
    rfl
  have start := trans_binary gates (List.ofFn var) (sourceVars Finset.univ) legal (by
    intro w hw
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hw
    exact Or.inr ⟨i, Finset.mem_univ i, ori_zp rfl⟩) o
  rw [hg, ori_zp (show target8 (fun _ => false) = false by decide)] at start
  rcases start with e | run
  · exact False.elim ((by decide : target8 (fun i : Fin 8 => (129 : ℕ).testBit i.val) ≠ zF (fun i : Fin 8 => (129 : ℕ).testBit i.val)) (congrFun e _))
  have inf : ∃ x, rst 3 target8 x ≠ target8 x := ⟨(fun i : Fin 8 => (136 : ℕ).testBit i.val), by decide⟩
  have nz : rst 3 target8 ≠ zF := fun e => (by decide : rst 3 target8 (fun i : Fin 8 => (129 : ℕ).testBit i.val) ≠ zF (fun i : Fin 8 => (129 : ℕ).testBit i.val)) (congrFun e _)
  obtain ⟨k, paid, small⟩ := remove_var target8 3 Finset.univ _ inf nz run
  let π : Fin 8 → Fin 7 := ![0, 1, 2, 0, 4, 5, 3, 6]
  let lift (w : BF) : SignedLift.BF 7 := fun y => w (y ∘ π)
  have sources : ∀ w, sourceVars (Finset.univ.erase 3) w →
      ∃ i : Fin 7, lift w = fun y => y i := by
    rintro w ⟨i,_hi,rfl⟩
    exact ⟨π i,rfl⟩
  have hom : ∀ op a b, lift (gF op a b) = SignedLift.signed op (lift a) (lift b) := by intros; rfl
  have mapped := UC_map (G := gF) (G' := SignedLift.signed) (A := fun _ => True) lift hom k
    (sourceVars (Finset.univ.erase 3)) (fun w => ∃ i : Fin 7, w = fun y => y i) (rst 3 target8) sources small
  obtain ⟨C,fan,ct,hc⟩ := SignedLift.realize _ mapped
  have eqn : lift (rst 3 target8) = Core7.flatValue := by
    funext y
    exact (by decide +kernel : ∀ z : Fin 7 → Bool, lift (rst 3 target8) z = Core7.flatValue z) y
  have bound := coreLow C fan (hc.trans eqn)
  have hneg := countBinary_lt gates hasNot
  omega
theorem coreLower (C : Circuit) (fan : FanInTwo C) (hc : circuitFun 7 C = Core7.flatValue) : 12 ≤ C.gates.countP SignedLift.binary := by
  obtain ⟨k,hk,run⟩ := Core7.physicalSigned C fan (congrFun hc)
  have bound := Core7.usedBound k
  have lower : ¬ k ≤ 11 := fun h => bound h run
  have e : (fun g : Gate => !Core7.isNot g) = SignedLift.binary := by
    funext g
    cases g with
    | mk op ins => cases op <;> rfl
  rw [e] at hk
  omega
end PEqualNP.Outside.L_meta_35826
open PEqualNP.Outside.L_meta_35826 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_35826 : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) := by
  intro gates o legal _oneNot computes
  by_cases hnot : ∃ g ∈ gates, g.op = GateOp.not
  · have comp : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = target8 x := fun x => (computes x).trans (graph_correct x).symm
    have large := lower_using_binary coreLower gates o legal comp hnot
    have hw : witness.length ≤ 14 := by decide
    exact ⟨witness, 21, witnessBasis, by omega, fun x => (witnessCorrect x).trans (graph_correct x)⟩
  · refine ⟨gates, o, ?_, le_rfl, computes⟩
    intro g hg
    obtain ⟨ops, hlen⟩ := legal g hg
    refine ⟨?_, hlen⟩
    rcases ops with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact False.elim (hnot ⟨g,hg,h⟩)

import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_37159.LiveCircuits
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 64
def zero : Sig := 0
def one : Sig := BitVec.allOnes 64
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

def bit (i : Fin 64) (a : Sig) : Bool := a.getLsbD i.val
lemma bit_zero (i) : bit i zero = false := by simp [bit,zero]
lemma bit_one (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
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
lemma get_rep {u} (w : List Sig) (i : Nat) : Repr u (w.map (nrm u)) (w.getD i zero) := by
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

lemma extract {u target} (gs : List Gate) (w : List Sig)
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

lemma b_read (i) (w : List Sig) (j : Nat) :
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

lemma execute_bits (gs : List Gate) (i) (w : List Sig)
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

abbrev Row := Fin 64
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

def inputs : List Sig := [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0,0,0]
def graph : Sig := (((((((0xffffffffffffffff * 18446744073709551616 + 0xffffffffffeaeae8) * 18446744073709551616 + 0xfffefefcfffafaf8) * 18446744073709551616 + 0xffeeeeecffeaeae8) * 18446744073709551616 + 0xffffffffffffffff) * 18446744073709551616 + 0xffffffffffeaeae8) * 18446744073709551616 + 0xfffefefcfffafaf8) * 18446744073709551616 + 0xffeeeeecffeaeae8)
def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 4) || (x 5 && x 7) || (x 6 && x 7)
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
  if h : r.val < 64-d.val then ⟨d.val+r.val,by omega⟩ else ⟨r.val-(64-d.val),by omega⟩
def backwards (d : Row) : Row := Fin.ofNat 64 (64-d.val)
def rowMove (m : Move) (r : Row) : Row :=
  if bit r m.1 then shifted m.2.2 r else if bit r m.2.1 then shifted (backwards m.2.2) r else r
def mux (m a b : Sig) := (m &&& a) ||| (~~~m &&& b)
def wordMove (m : Move) (a : Sig) :=
  mux m.1 (a.rotateRight m.2.2.val) (mux m.2.1 (a.rotateRight (backwards m.2.2).val) a)

theorem bit_shift (d r : Row) (a : Sig) : bit r (a.rotateRight d.val) = bit (shifted d r) a := by
  unfold bit
  rw [BitVec.getLsbD_rotateRight_of_lt d.isLt]
  by_cases h : r.val < 64-d.val <;> simp [shifted,h,r.isLt]

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

end PEqualNP.Outside.L_meta_37159.LiveCircuits
namespace PEqualNP.Outside.L_meta_37159.Certificate
open PEqualNP.Outside.L_meta_37159.LiveCircuits
structure Spec where
 roots : List Sig
 target : Sig
 negativeRows : List Row
 slices : List (Sig × Nat)
 plans : List (List Nat)
 codes : Array Nat
 width : Nat
def swapRows (v : Nat) : Move :=
 let i := v % 16
 let j := v / 16
 let a := inputs.getD i zero
 let b := inputs.getD j zero
 (a &&& ~~~b,b &&& ~~~a,Fin.ofNat 64 ((1 <<< j)-(1 <<< i)))
def permWord (g : Spec) (p : Nat) (w : Sig) := movedWord ((g.plans.getD p []).map swapRows) w
variable (g : Spec)
abbrev Entry := Nat × List Nat × Nat × Nat × List Nat
def Entry.cap (x : Entry) : Nat := x.1
def Entry.program (x : Entry) : List Nat := x.2.1
def Entry.livingMask (x : Entry) : Nat := x.2.2.1
def Entry.badMask (x : Entry) : Nat := x.2.2.2.1
def Entry.codes (x : Entry) : List Nat := x.2.2.2.2
def unpackGates (ws : List Sig) : List Nat → List Choice
 | [] => []
 | g::gs => let c : Choice := (g/1024,ws.getD (g%32) 0,ws.getD ((g/32)%32) 0)
            c :: unpackGates (ws++[choiceVal c]) gs
def selectMask {α : Type} (m : Nat) : List α → List α
 | [] => []
 | w::ws => if m.testBit 0 then w::selectMask (m/2) ws else selectMask (m/2) ws
def choicesOf (e : Entry) := unpackGates g.roots e.program
def stateOf (e : Entry) := selectMask e.livingMask (g.roots++(choicesOf g e).map choiceVal)
def candidates (r : Row) : List Sig → Sig
 | [] => g.target
 | w::ws => (if bit r w then w else ~~~w) &&& candidates r ws
def indist (e : Entry) (ws : List Sig) := (selectMask e.badMask g.negativeRows).any fun r => candidates g r ws != 0
def pop (x : Nat) := (BitVec.ofNat 16 x).cpop.toNat
def readCode (e : Entry) (ws : List Sig) (a b : Sig) (d : Nat) (ka kb : Bool) : Nat :=
 let ia := ws.idxOf a
 let ib := ws.idxOf b
 let lo := min ia ib
 let hi := max ia ib
 let block := e.codes.getD (hi*(hi-1)/2+lo) 0
 let dir := ia < ib
 let slot := 4*(if dir then d else flipOp d)+(if dir then ka.toNat+2*kb.toNat else kb.toNat+2*ka.toNat)
 if block.testBit slot then (g.codes[(block >>> (16+g.width*pop (block % (2^slot)))) % (2^g.width)]?).getD 0 else 0
def verifyCut (cap : Nat) (cs : List Choice) (ch : List Sig) (code : Nat) : Bool :=
 match g.slices[code % 64-1]? with
 | none => false
 | some (dom,lb) =>
  let witness := selectMask (code/64) cs
  match makePool true dom g.roots witness with
  | none => false
  | some pool => poolCut true dom lb cap witness.length pool ch
def verifyIso (db : Array Entry) (cap : Nat) (ch : List Sig) (code : Nat) : Bool :=
 let key := code-16384
 let j := key/g.plans.length
 let dest := (db[j]?).getD default
 decide (j < db.size) && (dest.cap==cap) && decide ((ch.map (permWord g (key % g.plans.length))).toFinset = (stateOf g dest).toFinset)
def verifyChild (db : Array Entry) (e : Entry) (steps : List Choice) (ws : List Sig) (a b : Sig) (d : Nat) (ka kb : Bool) : Bool :=
 let y := bin d a b
 let ch := childTwo ws a b d ka kb
 if b.toNat ≤ a.toNat then true else
 if a==b || ws.contains y || y==zero || y==one || decide (e.cap<ch.length) then true
 else
 let code := readCode g e ws a b d ka kb
 if code==0 then indist g e ch else if 16384≤code then verifyIso g db (e.cap-1) ch code
 else verifyCut g (e.cap-1) (steps++[(d,a,b)]) ch code
def verify (db : Array Entry) (e : Entry) : Bool :=
 let ws := stateOf g e
 let cs := choicesOf g e
 decide (0 < e.cap) && decide ws.Nodup && !ws.contains g.target &&
 ws.all fun a => ws.all fun b => [0,1,2,3].all fun d => [false,true].all fun ka => [false,true].all fun kb => verifyChild g db e cs ws a b d ka kb

variable {g : Spec}
structure Good (g : Spec) : Prop where
 negatives : ∀ r ∈ g.negativeRows, bit r g.target = false
 slices : ∀ s ∈ g.slices, Slice true g.roots g.target s.1 s.2
 perms : ∀ p : Nat, permWord g p g.target = g.target ∧
  ∀ r : Row, movedRow ((g.plans.getD p []).map swapRows)
    (movedRow ((g.plans.getD p []).reverse.map swapRows) r) = r

theorem selectMask_sub {α : Type} (m : Nat) (xs : List α) : (selectMask m xs).Sublist xs := by
 induction xs generalizing m with
 | nil => exact List.Sublist.slnil
 | cons a xs ih =>
  unfold selectMask
  split
  · exact List.Sublist.cons₂ _ (ih _)
  · exact List.Sublist.cons _ (ih _)

theorem candBit (r s : Row) (ws : List Sig) :
 bit s (candidates g r ws) = true ↔ bit s g.target = true ∧ ∀ w ∈ ws, bit r w = bit s w := by
 induction ws with
 | nil => simp [candidates]
 | cons a ws ih =>
  have ba (x y : Sig) : bit s (x &&& y) = (bit s x && bit s y) := BitVec.getLsbD_and
  have bn (x : Sig) : bit s (~~~x) = !bit s x := by
   simp only [bit,BitVec.getLsbD_not,s.isLt,decide_true,Bool.true_and]
  cases hr : bit r a <;> cases hs : bit s a <;>
   simp only [candidates,hr,Bool.false_eq_true,ite_false,ite_true,ba,bn,hs,Bool.and_eq_true,
    ih,List.forall_mem_cons] <;> simp_all

theorem indistSound (good : Good g) {e ws} (bad : indist g e ws = true) (k : Nat) :
 Impossible true g.target k ws.toFinset := by
 obtain ⟨s,hs,hbad⟩ := List.any_eq_true.mp bad
 have hn := good.negatives s ((selectMask_sub e.badMask g.negativeRows).subset hs)
 intro l _ run
 have z : candidates g s ws = 0 := by
  apply bit_ext
  intro r
  cases e : bit r (candidates g s ws)
  · exact (bit_zero _).symm
  · obtain ⟨yes,all⟩ := (candBit _ _ _).mp e
    obtain ⟨w,hw,sep⟩ := live_row_difference run (show bit r g.target ≠ bit s g.target by simp [yes,hn])
    exact False.elim (sep (all w (List.mem_toFinset.mp hw)).symm)
 simp [z] at hbad

theorem isoTransfer (good : Good g) (p : Nat) (ws : List Sig) (k : Nat)
 (h : Impossible true g.target k (ws.map (permWord g p)).toFinset) :
 Impossible true g.target k ws.toFinset := by
 intro n hn run
 let ms := (g.plans.getD p []).map swapRows
 have onto : Function.Surjective (movedRow ms) := fun r =>
  ⟨movedRow ((g.plans.getD p []).reverse.map swapRows) r,(good.perms p).2 r⟩
 have hr := live_rename run (movedRow ms) onto
 have eq : rename (movedRow ms) = permWord g p := funext fun w => (moved_eq_rename ms w).symm
 rw [eq,(good.perms p).1] at hr
 have seteq : ws.toFinset.image (permWord g p) = (ws.map (permWord g p)).toFinset := by ext w; simp
 exact h n hn (seteq ▸ hr)

theorem verifiedCut (good : Good g) {cap cs ch code}
 (nd : ch.Nodup) (ok : verifyCut g cap cs ch code = true) :
 Impossible true g.target cap ch.toFinset := by
 unfold verifyCut at ok
 cases hs : g.slices[code % 64-1]? with
 | none => rw [hs] at ok; contradiction
 | some s =>
  obtain ⟨dom,lb⟩ := s
  rw [hs] at ok
  let witness := selectMask (code/64) cs
  change (match makePool true dom g.roots witness with
   | none => false
   | some pool => poolCut true dom lb cap witness.length pool ch) = true at ok
  cases hp : makePool true dom g.roots witness with
  | none => rw [hp] at ok; contradiction
  | some pool =>
   apply poolCut_sound (good.slices (dom,lb) (List.mem_of_getElem? hs)) witness hp nd
   rw [hp] at ok
   exact ok

theorem verifiedIso (good : Good g) {db cap ch code} (ok : verifyIso g db cap ch code = true)
 (prev : ∀ j, j < db.size → (db[j]?.getD default).cap = cap →
  Impossible true g.target (db[j]?.getD default).cap (stateOf g (db[j]?.getD default)).toFinset) :
 Impossible true g.target cap ch.toFinset := by
 let j := (code-16384)/g.plans.length
 let p := (code-16384)%g.plans.length
 let dest := db[j]?.getD default
 simp only [verifyIso,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at ok
 obtain ⟨⟨hj,hcap⟩,eq⟩ := ok
 apply isoTransfer good p ch cap
 rw [eq]
 exact hcap ▸ prev j hj hcap

theorem childSwap {u : Bool} {d : Nat} (hd : allowed u d) (ws : List Sig)
    (a b : Sig) (ka kb : Bool) :
    (childTwo ws a b d ka kb).Perm (childTwo ws b a (flipOp d) kb ka) := by
  unfold childTwo
  rw [bin_flip hd a b, List.erase_comm a b]
  apply List.Perm.cons
  cases ka <;> cases kb <;> simp only [kept, Bool.false_eq_true, ↓reduceIte]
  all_goals first | exact List.Perm.refl _ | exact List.Perm.swap _ _ _

theorem enumStepOrdered {u} {T : Sig} {cap : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (twoStep : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d, allowed u d → ∀ ka kb, a.toNat < b.toNat → bin d a b ∉ ws →
      proper (bin d a b) → (childTwo ws a b d ka kb).length ≤ cap →
      Impossible u T (cap-1) (childTwo ws a b d ka kb).toFinset) :
    Impossible u T cap ws.toFinset := by
  apply enum_step hn out
  intro a ha b hb d hd ka kb ne fresh pr sz
  rcases lt_or_gt_of_ne (fun eq => ne (BitVec.toNat_inj.mp eq)) with lt | gt
  · exact twoStep a ha b hb d hd ka kb lt fresh pr sz
  · have eq := bin_flip hd a b
    have perm := childSwap hd ws a b ka kb
    have hs := twoStep b hb a ha (flipOp d) (flip_flip hd).1 kb ka gt
      (eq ▸ fresh) (eq ▸ pr) (perm.length_eq ▸ sz)
    have eqSet : (childTwo ws a b d ka kb).toFinset = (childTwo ws b a (flipOp d) kb ka).toFinset := by
      ext x
      simpa only [List.mem_toFinset] using (perm.mem_iff : x ∈ _ ↔ x ∈ _)
    exact eqSet.symm ▸ hs

theorem nodeSound (good : Good g) {db e} (ok : verify g db e = true)
 (prev : ∀ j, j < db.size → (db[j]?.getD default).cap < e.cap →
  Impossible true g.target (db[j]?.getD default).cap (stateOf g (db[j]?.getD default)).toFinset) :
 Impossible true g.target e.cap (stateOf g e).toFinset := by
 let ws := stateOf g e
 let cs := choicesOf g e
 simp only [verify,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.all_eq_true] at ok
 obtain ⟨⟨⟨pos,nd⟩,notout⟩,all⟩ := ok
 apply enumStepOrdered nd (by simpa using notout)
 intro a ha b hb d hd ka kb lt fresh prop len
 have reverse : ¬b.toNat ≤ a.toNat := Nat.not_le.mpr lt
 have ne : a ≠ b := fun eq => (Nat.lt_irrefl _) (eq ▸ lt)
 have op : d ∈ [0,1,2,3] := by rcases allowed_four hd with h|h|h|h <;> simp_all
 have ka' : ka ∈ [false,true] := by cases ka <;> simp
 have kb' : kb ∈ [false,true] := by cases kb <;> simp
 have chk := all a ha b hb d op ka ka' kb kb'
 have nz := prop.1
 have no := prop.2
 simp only [verifyChild,beq_iff_eq,List.contains_iff_mem,Bool.or_eq_true,decide_eq_true_eq,
  reverse,ne,fresh,nz,no,Nat.not_lt.mpr len,or_self,ite_false] at chk
 split at chk
 · exact indistSound good chk _
 · split at chk
   · have dec : e.cap-1 < e.cap := by omega
     exact verifiedIso good chk (fun j hj heq => prev j hj (heq.trans_lt dec))
   · apply verifiedCut good _ chk
     unfold childTwo kept
     have nodup := nd
     have rn : ((ws.erase a).erase b).Nodup := (nodup.erase a).erase b
     have notA : a ∉ (ws.erase a).erase b := fun h => ((nodup.mem_erase_iff).mp (List.mem_of_mem_erase h)).1 rfl
     have notB : b ∉ (ws.erase a).erase b := fun h => (((nodup.erase a).mem_erase_iff).mp h).1 rfl
     have old : ∀ x ∈ (ws.erase a).erase b, x ∈ ws := fun _ h => List.mem_of_mem_erase (List.mem_of_mem_erase h)
     have ya : bin d a b ≠ a := by intro eq; apply fresh; rw [eq]; exact ha
     have yb : bin d a b ≠ b := by intro eq; apply fresh; rw [eq]; exact hb
     have yr : bin d a b ∉ (ws.erase a).erase b := fun h => fresh (old _ h)
     change (bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))).Nodup
     cases ka <;> cases kb <;> simp [kept,ya,yb,yr,notA,notB,rn,ne]

theorem forestSound (good : Good g) (db : Array Entry)
 (checked : ∀ j, j < db.size → verify g db (db[j]?.getD default) = true)
 (j : Nat) (hj : j < db.size) :
 Impossible true g.target (db[j]?.getD default).cap (stateOf g (db[j]?.getD default)).toFinset := by
 suffices ∀ k i, i < db.size → (db[i]?.getD default).cap = k →
  Impossible true g.target (db[i]?.getD default).cap (stateOf g (db[i]?.getD default)).toFinset from this _ j hj rfl
 intro k
 induction k using Nat.strong_induction_on with
 | ind k ih =>
  intro i hi hc
  apply nodeSound good (checked i hi)
  intro j hj lt
  exact ih _ (hc ▸ lt) j hj rfl

def pack (xs : List Nat) : Nat := xs.foldr (fun x a => x+18446744073709551616*a) 0
def rootsOf (m : Nat) : List Sig := (List.range 6).filterMap fun i => if m.testBit i then some (inputs.getD i zero) else none
def targetOf (t : Nat) : Sig := BitVec.ofNat 64 t
def domainOf (m z o : Nat) : Sig := (List.range 8).foldl (fun d i =>
 if !m.testBit i || z.testBit i then d &&& ~~~(inputs.getD i zero)
 else if o.testBit i then d &&& inputs.getD i zero else d) one
def fixRows (z o : Nat) : List Move := (List.range 8).filterMap fun j =>
 let x := inputs.getD j zero
 let step := Fin.ofNat 64 (1 <<< j)
 if z.testBit j then some (zero,x,step)
 else if o.testBit j then some (~~~x,zero,step) else none

def checkPerm (g : Spec) (xs : List Nat) : Bool :=
 (movedWord (xs.map swapRows) g.target == g.target) &&
 decide (∀ r : Row, movedRow (xs.map swapRows) (movedRow (xs.reverse.map swapRows) r) = r)
theorem checkedPerms {g : Spec} (ok : g.plans.all (checkPerm g) = true) (p : Nat) :
 permWord g p g.target = g.target ∧ ∀ r : Row,
 movedRow ((g.plans.getD p []).map swapRows) (movedRow ((g.plans.getD p []).reverse.map swapRows) r)=r := by
 cases h : g.plans[p]? with
 | none => simp [permWord,List.getD_eq_getElem?_getD,h,movedWord,movedRow]
 | some xs =>
  have chk := List.all_eq_true.mp ok xs (List.mem_of_getElem? h)
  simpa only [checkPerm,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq,permWord,
   List.getD_eq_getElem?_getD,h,Option.getD_some] using chk

theorem lowerFrom {raw T cap} (xs : List (Sig × Row × Row)) (hp : proper T)
 (ok : checkEssential T raw xs = true) (eq : xs.map Prod.fst = raw)
 (impossible : Impossible true T cap raw.toFinset) : Lower true raw T (cap+1) := by
 apply lower_impossible hp (essential_plain ok).1 (essential_plain ok).2 _ impossible
 intro v hv
 apply essential_ok ok v
 rw [eq]
 exact List.mem_toFinset.mpr hv

theorem checkedList {g : Spec} (xs : List Entry)
 (good : xs.all (verify g xs.toArray) = true) (j : Nat) (hj : j < xs.toArray.size) :
 verify g xs.toArray (xs.toArray[j]?.getD default) = true := by
 have hlen : j < xs.length := by simpa using hj
 have hm : xs[j]?.getD default ∈ xs := by
  simp only [List.getElem?_eq_getElem hlen,Option.getD_some]
  exact List.getElem_mem hlen
 simpa using List.all_eq_true.mp good _ hm
def g0 : Spec := ⟨rootsOf 7,targetOf 16782920098433788136,[0,1,2,4,8,9,10,12,16,17,18,20,24,25,26,28,32,33,34,36,40,41,42,44,48,49,50,52,56,57,58,60],[],[[]],#[],1⟩
def e0_0 : Entry := ⟨3,[],7,15,[0,0,0]⟩
def entries0 : List Entry := [e0_0]
def db0 : Array Entry := entries0.toArray
def g1 : Spec := ⟨rootsOf 11,targetOf 17188250249744412296,[0,1,2,4,5,6,8,12,16,17,18,20,21,22,24,28,32,33,34,36,37,38,40,44,48,49,50,52,53,54,56,60],[],[[]],#[],1⟩
def e1_0 : Entry := ⟨3,[],7,71,[0,0,0]⟩
def entries1 : List Entry := [e1_0]
def db1 : Array Entry := entries1.toArray
def g2 : Spec := ⟨rootsOf 13,targetOf 18059710075062254240,[0,1,2,3,4,6,8,10,16,17,18,19,20,22,24,26,32,33,34,35,36,38,40,42,48,49,50,51,52,54,56,58],[],[[]],#[],1⟩
def e2_0 : Entry := ⟨3,[],7,83,[0,0,0]⟩
def entries2 : List Entry := [e2_0]
def db2 : Array Entry := entries2.toArray
def g3 : Spec := ⟨rootsOf 21,targetOf 18084943866925588640,[0,1,2,3,4,6,8,9,10,11,12,14,16,18,24,26,32,33,34,35,36,38,40,41,42,43,44,46,48,50,56,58],[],[[]],#[],1⟩
def e3_0 : Entry := ⟨3,[],7,4115,[0,0,0]⟩
def entries3 : List Entry := [e3_0]
def db3 : Array Entry := entries3.toArray
def g4 : Spec := ⟨rootsOf 14,targetOf 18212834798890712256,[0,1,2,3,4,5,8,9,16,17,18,19,20,21,24,25,32,33,34,35,36,37,40,41,48,49,50,51,52,53,56,57],[],[[]],#[],1⟩
def e4_0 : Entry := ⟨3,[],7,85,[0,0,0]⟩
def entries4 : List Entry := [e4_0]
def db4 : Array Entry := entries4.toArray
def g5 : Spec := ⟨rootsOf 23,targetOf 16927598236496750824,[0,1,2,4,8,9,10,12,16,18,20,24,26,28,32,33,34,36,40,41,42,44,48,50,52,56,58,60],[(domainOf 23 16 0,4)],[[]],#[],1⟩
def entries5 : List Entry := []
def db5 : Array Entry := entries5.toArray
def g6 : Spec := ⟨rootsOf 39,targetOf 16927600444076255464,[0,1,2,4,8,9,10,12,16,17,18,20,24,25,26,28,32,34,36,40,42,44,48,50,52,56,58,60],[(domainOf 39 32 0,4)],[[]],#[],1⟩
def entries6 : List Entry := []
def db6 : Array Entry := entries6.toArray
def g7 : Spec := ⟨rootsOf 15,targetOf 17071154872699120872,[0,1,2,4,8,9,12,16,17,18,20,24,25,28,32,33,34,36,40,41,44,48,49,50,52,56,57,60],[(domainOf 15 8 0,4)],[[]],#[],1⟩
def entries7 : List Entry := []
def db7 : Array Entry := entries7.toArray
def g8 : Spec := ⟨rootsOf 27,targetOf 17197783015559449736,[0,1,2,4,5,6,8,9,12,13,16,18,20,22,24,28,32,33,34,36,37,38,40,41,44,45,48,50,52,54,56,60],[],[[]],#[],1⟩
def e8_0 : Entry := ⟨3,[],15,16583,[0,0,0,0,0,0]⟩
def entries8 : List Entry := [e8_0]
def db8 : Array Entry := entries8.toArray
def g9 : Spec := ⟨rootsOf 43,targetOf 17197820544981462664,[0,1,2,4,5,6,8,12,16,17,18,20,21,22,24,28,32,34,36,38,40,44,48,50,52,54,56,60],[(domainOf 43 32 0,4)],[[]],#[],1⟩
def entries9 : List Entry := []
def db9 : Array Entry := entries9.toArray
def g10 : Spec := ⟨rootsOf 29,targetOf 18059611119015731360,[0,1,2,3,4,6,8,9,10,11,12,14,16,17,18,19,20,22,24,26,32,33,34,35,36,38,40,41,42,43,44,46,48,49,50,51,52,54,56,58],[(domainOf 29 0 8,4)],[[]],#[],1⟩
def entries10 : List Entry := []
def db10 : Array Entry := entries10.toArray
def g11 : Spec := ⟨rootsOf 29,targetOf 18062513829713735840,[0,1,2,3,4,6,8,9,10,11,16,18,20,22,24,26,32,33,34,35,36,38,40,41,42,43,48,50,52,54,56,58],[],[[]],#[],1⟩
def e11_0 : Entry := ⟨3,[],15,16595,[0,0,0,0,0,0]⟩
def entries11 : List Entry := [e11_0]
def db11 : Array Entry := entries11.toArray
def g12 : Spec := ⟨rootsOf 45,targetOf 18062524867779033760,[0,1,2,3,4,6,8,10,16,17,18,19,20,22,24,26,32,34,36,38,40,42,48,50,52,54,56,58],[(domainOf 45 32 0,4)],[[]],#[],1⟩
def entries12 : List Entry := []
def db12 : Array Entry := entries12.toArray
def g13 : Spec := ⟨rootsOf 53,targetOf 18085032171453194400,[0,1,2,3,4,6,8,9,10,11,12,14,16,18,24,26,32,33,34,35,40,41,42,43,48,50,56,58],[(domainOf 53 32 0,4)],[[]],#[],1⟩
def entries13 : List Entry := []
def db13 : Array Entry := entries13.toArray
def g14 : Spec := ⟨rootsOf 46,targetOf 18212834798085393600,[0,1,2,3,4,5,8,9,12,13,16,17,18,19,20,21,24,25,28,29,32,33,34,35,36,37,40,41,48,49,50,51,52,53,56,57],[(domainOf 46 0 32,4)],[[]],#[],1⟩
def entries14 : List Entry := []
def db14 : Array Entry := entries14.toArray
def g15 : Spec := ⟨rootsOf 15,targetOf 18224093969760451816,[0,1,2,4,8,9,16,17,18,20,24,25,32,33,34,36,40,41,48,49,50,52,56,57],[(domainOf 15 1 0,4)],[[]],#[],1⟩
def entries15 : List Entry := []
def db15 : Array Entry := entries15.toArray
def g16 : Spec := ⟨rootsOf 15,targetOf 18368211356893118184,[0,1,2,4,8,16,17,18,20,24,32,33,34,36,40,48,49,50,52,56],[(domainOf 15 4 0,4),(domainOf 15 8 0,4),(domainOf 15 1 0,4),(domainOf 15 2 0,4)],[[]],#[1,2,3,4,16384,16385,16386,16387,16388,16389,16390,16391,16392,16393,16394,16395,16396,16397,16398,16399,16400,16401,16402,16403,16404,16405,16406,16407,16408,16409,16410,16411,16412,16413,16414,16415,16416,16417,16418,16419,16420,16421,16422,16423,16424,16425],6⟩
def e16_0 : Entry := ⟨3,[1056,1092,2149],71,7,[0,0,0,0,0,0]⟩
def e16_1 : Entry := ⟨4,[1056,1092],47,30,[0,0,0,0,0,0,0,0,0,0x1011001]⟩
def e16_2 : Entry := ⟨4,[1056,2116],47,15,[0,0,0,0,0,0,0,0,0,0]⟩
def e16_3 : Entry := ⟨3,[1056,1124,2117],75,7,[0,0,0,0,0,0]⟩
def e16_4 : Entry := ⟨4,[1056,1124],47,30,[0,0,0,0,0,0,0,0,0x1c01001,0]⟩
def e16_5 : Entry := ⟨4,[1056,2148],47,31,[0,0,0,0,0,0,0,0,0,0]⟩
def e16_6 : Entry := ⟨3,[1056,1088,1089],120,14,[0,0,0x1,0,0x1,0x20001]⟩
def e16_7 : Entry := ⟨4,[1056,1088],62,14,[0xa0010,0,0,0,0x1,0,0x30001,0,0,0x1]⟩
def e16_8 : Entry := ⟨3,[1056,1120,1121],116,30,[0,0,0x10001,0,0x10001,0x20001]⟩
def e16_9 : Entry := ⟨4,[1056,1120],62,30,[0,0xc0010,0,0,0,0x10001,0x30001,0,0,0x10001]⟩
def e16_10 : Entry := ⟨4,[1056,1089],61,14,[0xa0010,0,0,0,0x1,0,0x20001,0,0,0x1]⟩
def e16_11 : Entry := ⟨4,[1056,1121],61,30,[0,0xc0010,0,0,0,0x10001,0x20001,0,0,0x10001]⟩
def e16_12 : Entry := ⟨5,[1056],31,31,[0x30820824207,0x8b0440,0xce0440,0x8d0440,0xcf0440,0,0xc26000,0x826000,0x1801402222,0x2412012222]⟩
def e16_13 : Entry := ⟨4,[1088,2084],47,15,[0,0,0,0,0,0,0,0,0,0]⟩
def e16_14 : Entry := ⟨3,[1088,1124,2085],77,11,[0,0,0,0,0,0]⟩
def e16_15 : Entry := ⟨4,[1088,1124],47,30,[0,0,0,0,0,0,0,0x4831001,0,0]⟩
def e16_16 : Entry := ⟨4,[1088,2148],47,31,[0,0,0,0,0,0,0,0,0,0]⟩
def e16_17 : Entry := ⟨3,[1088,1120,1122],114,30,[0,0,0x1,0,0x10001,0x1]⟩
def e16_18 : Entry := ⟨4,[1088,1120],62,30,[0,0,0x150010,0,0,0x10001,0,0x1,0,0x1]⟩
def e16_19 : Entry := ⟨4,[1088,1089],59,14,[0xa0010,0,0,0,0x30001,0,0x20001,0,0,0x20001]⟩
def e16_20 : Entry := ⟨4,[1088,1122],59,30,[0,0x150010,0,0,0,0x10001,0x20001,0,0,0x10001]⟩
def e16_21 : Entry := ⟨5,[1088],31,31,[0x8b0440,0x800004207,0x172020,0x960440,0,0x180440,0x6000,0x4431432222,0x806000,0x5014c12222]⟩
def e16_22 : Entry := ⟨4,[1120,2084],47,31,[0,0,0,0,0,0,0,0,0,0]⟩
def e16_23 : Entry := ⟨4,[1120,2116],47,31,[0,0,0,0,0,0,0,0,0,0]⟩
def e16_24 : Entry := ⟨4,[1120,1121],55,22,[0xc0010,0,0,0,0x30001,0,0x20001,0,0,0x20001]⟩
def e16_25 : Entry := ⟨4,[1120,1122],55,30,[0,0x150010,0,0,0,0x1,0x20001,0,0,0x1]⟩
def e16_26 : Entry := ⟨5,[1120],31,31,[0x8d0440,0x960440,0,0x10810414207,0x5c2020,0x5d2020,0x416000,0x6832032222,0x6c04c02222,0x816000]⟩
def e16_27 : Entry := ⟨4,[1089,2052],47,15,[0,0,0,0,0,0,0,0,0,0]⟩
def e16_28 : Entry := ⟨3,[1089,1124,2053],78,13,[0,0,0,0,0,0]⟩
def e16_29 : Entry := ⟨4,[1089,1124],47,30,[0,0,0,0,0,0,0x8021001,0,0,0]⟩
def e16_30 : Entry := ⟨4,[1089,2148],47,31,[0,0,0,0,0,0,0,0,0,0]⟩
def e16_31 : Entry := ⟨3,[1089,1121,1122],113,30,[0,0,0x1,0,0x10001,0x1]⟩
def e16_32 : Entry := ⟨4,[1089,1121],61,30,[0,0,0x230010,0,0,0x10001,0,0x1,0,0x1]⟩
def e16_33 : Entry := ⟨4,[1089,1122],59,30,[0,0,0x230010,0,0,0x10001,0,0x30001,0,0x10001]⟩
def e16_34 : Entry := ⟨5,[1089],31,31,[0xce2020,0x172020,0xc00004207,0,0xe40440,0x250440,0x7c21422222,0x6000,0xc06000,0x8818412222]⟩
def e16_35 : Entry := ⟨4,[1121,2052],47,31,[0,0,0,0,0,0,0,0,0,0]⟩
def e16_36 : Entry := ⟨4,[1121,2116],47,31,[0,0,0,0,0,0,0,0,0,0]⟩
def e16_37 : Entry := ⟨4,[1121,1122],55,30,[0,0,0x230010,0,0,0x1,0,0x30001,0,0x1]⟩
def e16_38 : Entry := ⟨5,[1121],31,31,[0xcf2020,0,0xe40440,0x5c2020,0x10c10414207,0x692020,0x9c22022222,0x416000,0xa008402222,0xc16000]⟩
def e16_39 : Entry := ⟨4,[1122,2052],47,31,[0,0,0,0,0,0,0,0,0,0]⟩
def e16_40 : Entry := ⟨4,[1122,2084],47,31,[0,0,0,0,0,0,0,0,0,0]⟩
def e16_41 : Entry := ⟨5,[1122],31,31,[0,0x182020,0x252020,0x5d2020,0x692020,0x10000004207,0xac24c22222,0xb038432222,0x406000,0x6000]⟩
def e16_42 : Entry := ⟨6,[],15,31,[0xc24028888,0x26408888,0x39808888,0x427818888,0x43a818888,0x40b408888]⟩
def entries16 : List Entry := [e16_0,e16_1,e16_2,e16_3,e16_4,e16_5,e16_6,e16_7,e16_8,e16_9,e16_10,e16_11,e16_12,e16_13,e16_14,e16_15,e16_16,e16_17,e16_18,e16_19,e16_20,e16_21,e16_22,e16_23,e16_24,e16_25,e16_26,e16_27,e16_28,e16_29,e16_30,e16_31,e16_32,e16_33,e16_34,e16_35,e16_36,e16_37,e16_38,e16_39,e16_40,e16_41,e16_42]
def db16 : Array Entry := entries16.toArray
def g17 : Spec := ⟨rootsOf 15,targetOf 18368774315436605162,[0,2,4,8,16,18,20,24,32,34,36,40,48,50,52,56],[(domainOf 15 1 0,4)],[[]],#[],1⟩
def entries17 : List Entry := []
def db17 : Array Entry := entries17.toArray
def g18 : Spec := ⟨rootsOf 55,targetOf 16927598236463065320,[0,1,2,4,8,9,10,12,16,17,18,20,24,25,26,28,32,33,34,36,40,41,42,44,48,50,52,56,58,60],[(domainOf 55 0 16,5)],[[]],#[],1⟩
def entries18 : List Entry := []
def db18 : Array Entry := entries18.toArray
def g19 : Spec := ⟨rootsOf 59,targetOf 17197783015557221512,[0,1,2,4,5,6,8,9,12,13,16,17,18,20,21,22,24,28,32,33,34,36,37,38,40,41,44,45,48,50,52,54,56,60],[(domainOf 59 0 16,5)],[[]],#[],1⟩
def entries19 : List Entry := []
def db19 : Array Entry := entries19.toArray
def g20 : Spec := ⟨rootsOf 61,targetOf 18062513829713060000,[0,1,2,3,4,6,8,9,10,11,12,14,16,17,18,19,20,22,24,26,32,33,34,35,36,38,40,41,42,43,48,50,52,54,56,58],[(domainOf 61 0 16,5),(domainOf 61 0 8,5),(domainOf 61 32 0,5),(domainOf 61 0 32,4),(domainOf 61 32 16,4),(domainOf 61 32 8,4)],[[]],#[1,2,3,4,5,6,65,66,67,129,130,16384,16385,16386,16387,16388,16389,16390,16391,16392,16393,16394,16395,16396,16397,16398,16399,16400,16401,16402,16403,16404,16405,16406,16407,16408,16409,16410,16411,16412,16413,16414,16415,16416,16417,16418,16419,16420,16421,16422,16423,16424,16425,16426,16427,16428,16429,16430,16431,16432,16433,16434,16435,16436,16437,16438,16439,16440,16441,16442,16443,16444,16445,16446,16447,16448,16449,16450,16451,16452,16453,16454,16455,16456,16457,16458,16459,16460,16461,16462,16463,16464,16465,16466,16467,16468,16469,16470,16471,16472,16473,16474,16475,16476,16477,16478,16479,16480,16481,16482,16483,16484,16485,16486,16487,16488,16489,16490,16491,16492,16493,16494,16495,16496,16497,16498,16499,16500,16501,16502,16503,16504,16505,16506,16507,16508,16509,16510,16511,16512,16513,16514,16515,16516,16517,16518,16519,16520,16521,16522,16523,16524,16525,16526,16527,16528,16529,16530,16531,16532,16533,16534,16535,16536,16537,16538,16539,16540,16541,16542,16543,16544,16545,16546,16547,16548,16549,16550,16551,16552,16553,16554,16555,16556,16557,16558,16559,16560,16561,16562,16563,16564,16565,16566,16567,16568,16569,16570,16571,16572,16573,16574,16575,16576],8⟩
def e20_0 : Entry := ⟨5,[32,3077],126,153171155,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0x10]⟩
def e20_1 : Entry := ⟨5,[32,3077],95,2438355,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]⟩
def e20_2 : Entry := ⟨5,[32,3109],125,136393939,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0x10]⟩
def e20_3 : Entry := ⟨5,[32,3109],95,2438355,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]⟩
def e20_4 : Entry := ⟨4,[32,69,3142],155,2372755,[0,0,0,0,0,0,0,0,0,0]⟩
def e20_5 : Entry := ⟨4,[32,69,3174],151,2368659,[0,0,0,0,0,0,0,0,0,0]⟩
def e20_6 : Entry := ⟨5,[32,69],95,2372755,[0,0,0,0,0,0,0,0,0,0,0,0,0xf0100,0x10000110,0x2030110]⟩
def e20_7 : Entry := ⟨4,[32,1093,1125],211,136656082,[0,0,0,0,0,0,0,0,0,0]⟩
def e20_8 : Entry := ⟨4,[32,1093,3173],211,2434258,[0,0,0,0,0,0,0,0,0,0]⟩
def e20_9 : Entry := ⟨4,[32,1093,1157],203,136656082,[0,0,0,0,0,0,0,0,0,0]⟩
def e20_10 : Entry := ⟨5,[32,1093],123,136656082,[0,0,0,0,0,0,0,0,0x13120110,0x5140110,0,0,0,0,0xf1000]⟩
def e20_11 : Entry := ⟨5,[32,3141],91,19215507,[0,0,0,0,0,0,0,0,0,0]⟩
def e20_12 : Entry := ⟨4,[32,3141,1125],211,2438354,[0,0,0,0,0,0,0,0,0,0]⟩
def e20_13 : Entry := ⟨4,[32,3141,3173],211,2372819,[0,0,0,0,0,0,0,0,0,0]⟩
def e20_14 : Entry := ⟨4,[32,3141,1157],203,2438354,[0,0,0,0,0,0,0,0,0,0]⟩
def e20_15 : Entry := ⟨4,[32,3141,3205],203,2372819,[0,0,0,0,0,0,0,0,0,0]⟩
def e20_16 : Entry := ⟨5,[32,3141],123,136656082,[0,0,0,0,0,0,0,0,0x18170110,0x1a190110,0,0,0,0,0x10010]⟩
def e20_17 : Entry := ⟨5,[32,3141],95,2368659,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]⟩
def e20_18 : Entry := ⟨4,[32,101,3142],155,2368659,[0,0,0,0,0,0,0,0,0,0]⟩
def e20_19 : Entry := ⟨4,[32,101,3174],151,2368723,[0,0,0,0,0,0,0,0,0,0]⟩
def e20_20 : Entry := ⟨5,[32,101],95,2434259,[0,0,0,0,0,0,0,0,0,0,0,0,0x1d010110,0x1e0100,0x2030110]⟩
def e20_21 : Entry := ⟨4,[32,1125,1157],199,136656082,[0,0,0,0,0,0,0,0,0,0]⟩
def e20_22 : Entry := ⟨5,[32,1125],119,136656082,[0,0,0,0,0,0,0,0,0x17120110,0x4200110,0,0,0,0,0x1e1000]⟩
def e20_23 : Entry := ⟨5,[32,3173],87,19211475,[0,0,0,0,0,0,0,0,0,0]⟩
def e20_24 : Entry := ⟨4,[32,3173,1157],199,2438354,[0,0,0,0,0,0,0,0,0,0]⟩
def e20_25 : Entry := ⟨4,[32,3173,3205],199,2368723,[0,0,0,0,0,0,0,0,0,0]⟩
def e20_26 : Entry := ⟨5,[32,3173],119,136656082,[0,0,0,0,0,0,0,0,0x18130110,0x24230110,0,0,0,0,0x10]⟩
def e20_27 : Entry := ⟨5,[32,3173],95,17114259,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]⟩
def e20_28 : Entry := ⟨5,[32,1157],79,19215570,[0,0,0,0,0,0,0,0,0,0]⟩
def e20_29 : Entry := ⟨5,[32,1157],111,153433298,[0,0,0,0,0,0,0,0,0x19140110,0x23200110,0,0,0,0,0x21000]⟩
def e20_30 : Entry := ⟨5,[32,3205],111,136656082,[0,0,0,0,0,0,0,0,0x1a050110,0x24040110,0,0,0,0,0x30010]⟩
def e20_31 : Entry := ⟨4,[32,1056,2214],157,2368723,[0,0,0,0,0,0,0,0,0,0]⟩
def e20_32 : Entry := ⟨4,[32,1056,70],185,3159171,[0,0,0,0,0,0,0,0,0,0]⟩
def e20_33 : Entry := ⟨5,[32,1056],125,69547218,[0,0,0,0,0,0,0,0,0,0,0,0x2b0001,0,0,0x2a1000]⟩
def e20_34 : Entry := ⟨4,[32,1056,2214],158,2372819,[0,0,0,0,0,0,0,0,0,0]⟩
def e20_35 : Entry := ⟨4,[32,1056,102],182,17900625,[0,0,0,0,0,0,0,0,0,0]⟩
def e20_36 : Entry := ⟨5,[32,1056],126,1092957394,[0,0,0,0,0,0,0,0,0,0,0,0,0x2e0001,0,0x2d1000]⟩
def e20_37 : Entry := ⟨5,[32,96],126,4379194449,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0x10]⟩
def e20_38 : Entry := ⟨5,[32,3168],126,85275729,[0,0,0,0,0,0,0,0,0x10,0,0,0,0,0,0]⟩
def e20_39 : Entry := ⟨5,[32,65],125,1210332355,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0x10010]⟩
def e20_40 : Entry := ⟨5,[32,3137],125,1211380931,[0,0,0,0,0,0,0,0x10010,0,0,0,0,0,0,0]⟩
def e20_41 : Entry := ⟨6,[32],63,1294283986,[0xd0b2f2c2460,0,0x33324004,0x31304004,0,0,0,0,0,0,0xb0c0600,0xd0e0600,(pack [0x1c16150101112772,0x11b]),(pack [0x26222100001f2772,0x25]),(pack [0x202280327022772,0x329])]⟩
def e20_42 : Entry := ⟨4,[1056,2053,101],214,68166737,[0,0,0,0,0,0,0,0,0,0]⟩
def e20_43 : Entry := ⟨5,[1056,2053],126,1210332371,[0,0,0,0,0,0,0,0,0x350001,0,0,0,0,0,0x100]⟩
def e20_44 : Entry := ⟨4,[1056,2085,69],217,135279747,[0,0,0,0,0,0,0,0,0,0]⟩
def e20_45 : Entry := ⟨5,[1056,2085],125,203699411,[0,0,0,0,0,0,0,0x370001,0,0,0,0,0,0,0x100]⟩
def e20_46 : Entry := ⟨5,[1056,69],91,1226908819,[0x372b0202,0,0,0,0,0,0,0,0,0]⟩
def e20_47 : Entry := ⟨4,[1056,69,101],211,136324243,[0,0,0,0,0,0,0,0,0,0]⟩
def e20_48 : Entry := ⟨4,[1056,69,2149],211,3155091,[0,0,0,0,0,0,0,0,0,0]⟩
def e20_49 : Entry := ⟨4,[1056,69,133],203,136324243,[0,0,0,0,0,0,0,0,0,0]⟩
def e20_50 : Entry := ⟨4,[1056,69,2181],203,2110611,[0,0,0,0,0,0,0,0,0,0]⟩
def e20_51 : Entry := ⟨5,[1056,69],123,1210066066,[0,0,0,0,0,0,0,0x371000,0x3b3a1001,0x3d3c1001,0,0,0,0,0x10100]⟩
def e20_52 : Entry := ⟨5,[1056,69],95,136324243,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]⟩
def e20_53 : Entry := ⟨4,[1056,2117,3238],155,136324243,[0,0,0,0,0,0,0,0,0,0]⟩
def e20_54 : Entry := ⟨4,[1056,2117,101],211,3155091,[0,0,0,0,0,0,0,0,0,0]⟩
def e20_55 : Entry := ⟨4,[1056,2117,2149],211,2106515,[0,0,0,0,0,0,0,0,0,0]⟩
def e20_56 : Entry := ⟨4,[1056,2117,2181],203,2110611,[0,0,0,0,0,0,0,0,0,0]⟩
def e20_57 : Entry := ⟨5,[1056,2117],123,136328338,[0,0,0,0,0,0,0,0,0x42411001,0x43051001,0,0,0,0,0x400100]⟩
def e20_58 : Entry := ⟨4,[1056,3141,3174],151,69215379,[0,0,0,0,0,0,0,0,0,0]⟩
def e20_59 : Entry := ⟨5,[1056,3141],95,136586387,[0,0,0,0,0,0,0,0,0,0,0,0,0x400100,0x45000110,0x2030110]⟩
def e20_60 : Entry := ⟨5,[1056,101],87,86058131,[0x352e4004,0,0,0,0,0,0,0,0,0]⟩
def e20_61 : Entry := ⟨4,[1056,101,133],199,136324243,[0,0,0,0,0,0,0,0,0,0]⟩
def e20_62 : Entry := ⟨4,[1056,101,2181],199,2106579,[0,0,0,0,0,0,0,0,0,0]⟩
def e20_63 : Entry := ⟨5,[1056,101],119,203433106,[0,0,0,0,0,0,0x351000,0,0x413a1001,0x49481001,0,0,0,0,0x100]⟩
def e20_64 : Entry := ⟨5,[1056,101],95,83960979,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]⟩
def e20_65 : Entry := ⟨4,[1056,2149,3238],151,69215379,[0,0,0,0,0,0,0,0,0,0]⟩
def e20_66 : Entry := ⟨4,[1056,2149,2181],199,2106579,[0,0,0,0,0,0,0,0,0,0]⟩
def e20_67 : Entry := ⟨5,[1056,2149],119,136324306,[0,0,0,0,0,0,0,0,0x423b1001,0x4d041001,0,0,0,0,0x4c0100]⟩
def e20_68 : Entry := ⟨4,[1056,3173,3142],155,69215379,[0,0,0,0,0,0,0,0,0,0]⟩
def e20_69 : Entry := ⟨5,[1056,3173],95,69477523,[0,0,0,0,0,0,0,0,0,0,0,0,0x4f010110,0x4c0100,0x2030110]⟩
def e20_70 : Entry := ⟨5,[1056,133],111,136586386,[0,0,0,0,0,0,0,0,0x53c1001,0x4481001,0,0,0,0,0x30100]⟩
def e20_71 : Entry := ⟨5,[1056,2181],79,18953427,[0,0,0,0,0,0,0,0,0,0]⟩
def e20_72 : Entry := ⟨5,[1056,2181],111,136328402,[0,0,0,0,0,0,0,0,0x433d1001,0x4d491001,0,0,0,0,0x20100]⟩
def e20_73 : Entry := ⟨6,[1056],63,153429138,[0x36382f2c4206,0,0,0,0,0,0,0,0,0,0x360e6000,0x380c6000,(pack [0x146013e3f397227,0x4401]),(pack [0x50004a4b477227,0x4e00]),(pack [0x5202035102027227,0x5303])]⟩
def e20_74 : Entry := ⟨5,[2080,3077],95,136656082,[0,0,0,0,0,0,0,0,0,0,0,0,0xf010110,0x1e000110,0x2030110]⟩
def e20_75 : Entry := ⟨5,[2080,1061],95,136586386,[0,0,0,0,0,0,0,0,0,0,0,0,0x1401001,0x4c1001,0x3021001]⟩
def e20_76 : Entry := ⟨5,[2080,69],95,2434195,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0x2030110]⟩
def e20_77 : Entry := ⟨5,[2080,3141],95,2434195,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]⟩
def e20_78 : Entry := ⟨5,[2080,101],95,17114259,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]⟩
def e20_79 : Entry := ⟨5,[2080,3173],95,2434259,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0x2030110]⟩
def e20_80 : Entry := ⟨5,[2080,3104],125,2438355,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0x2a0010]⟩
def e20_81 : Entry := ⟨5,[2080,3104],126,2438355,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0x2d0010]⟩
def e20_82 : Entry := ⟨5,[2080,65],125,2372803,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]⟩
def e20_83 : Entry := ⟨5,[2080,3137],125,1324227,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0x10010]⟩
def e20_84 : Entry := ⟨6,[2080],63,86324435,[0x5c5b380b6024,0,0x5e5d4004,0,0,0,0,0,0,0,0xb550600,0x38560060,0x15801572222,0x5a00592222,0x30203022222]⟩
def e20_85 : Entry := ⟨5,[3104,69],95,2434195,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]⟩
def e20_86 : Entry := ⟨5,[3104,3141],95,2434195,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0x2030110]⟩
def e20_87 : Entry := ⟨5,[3104,101],95,2434195,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0x2030110]⟩
def e20_88 : Entry := ⟨5,[3104,3173],95,17114323,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]⟩
def e20_89 : Entry := ⟨5,[3104,96],126,17118289,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]⟩
def e20_90 : Entry := ⟨5,[3104,3168],126,1389649,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0x10]⟩
def e20_91 : Entry := ⟨6,[3104],63,1092957395,[0x5c5b360d0642,0,0,0x65644004,0,0,0,0,0,0,0x36560060,0xd550600,0x16101602222,0x6300622222,0x30203022222]⟩
def e20_92 : Entry := ⟨5,[64,1061],95,1210393746,[0,0,0,0,0,0,0,0,0,0,0,0,0x400001,0,0]⟩
def e20_93 : Entry := ⟨5,[64,3109],95,2438354,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]⟩
def e20_94 : Entry := ⟨4,[64,3141,1157],203,341139,[0,0,0,0,0,0,0,0,0,0]⟩
def e20_95 : Entry := ⟨5,[64,3141],123,341139,[0,0,0,0,0,0,0,0,0,0x690010,0,0,0,0,0x10]⟩
def e20_96 : Entry := ⟨4,[64,101,1062],157,2434195,[0,0,0,0,0,0,0,0,0,0]⟩
def e20_97 : Entry := ⟨4,[64,101,3110],157,2368659,[0,0,0,0,0,0,0,0,0,0]⟩
def e20_98 : Entry := ⟨5,[64,101],95,2434195,[0,0,0,0,0,0,0,0,0,0,0,0x6c6b0110,0,0,0x2030110]⟩
def e20_99 : Entry := ⟨5,[64,3173],95,17114323,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]⟩
def e20_100 : Entry := ⟨4,[64,1157,65],203,1073816723,[0,0,0,0,0,0,0,0,0,0]⟩
def e20_101 : Entry := ⟨5,[64,1157],79,18272822419,[0,0x690a2020,0xa6f0202,0,0,0,0,0,0,0]⟩
def e20_102 : Entry := ⟨5,[64,1157],111,17182303379,[0,0,0,0,0,0,0,0,0x690100,0,0,0,0,0,0x21000]⟩
def e20_103 : Entry := ⟨5,[64,65],123,1073816723,[0,0,0,0,0,0,0,0,0,0x6f0010,0,0,0,0,0x400010]⟩
def e20_104 : Entry := ⟨6,[64],63,1092953235,[0,0x6a0101012460,0x1720202,0,0,0,0,0,0,0,0x1010600,0x576867112222,0x6a010600,0x6e006d2222,(pack [0x202710370022772,0x305])]⟩
def e20_105 : Entry := ⟨5,[3136,1061],95,1076176082,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]⟩
def e20_106 : Entry := ⟨4,[3136,3109,3174],151,2368723,[0,0,0,0,0,0,0,0,0,0]⟩
def e20_107 : Entry := ⟨5,[3136,3109],95,2438354,[0,0,0,0,0,0,0,0,0,0,0,0,0xf0100,0x75000110,0x2030110]⟩
def e20_108 : Entry := ⟨5,[3136,101],95,2434195,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0x2030110]⟩
def e20_109 : Entry := ⟨5,[3136,3173],95,17114323,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]⟩
def e20_110 : Entry := ⟨4,[3136,3137,1158],171,9427,[0,0,0,0,0,0,0,0,0,0]⟩
def e20_111 : Entry := ⟨5,[3136,3137],123,1073820819,[0,0,0,0,0,0,0,0,0,0,0,0,0,0x790010,0xf0010]⟩
def e20_112 : Entry := ⟨4,[3136,98,1158],171,4314178579,[0,0,0,0,0,0,0,0,0,0]⟩
def e20_113 : Entry := ⟨5,[3136,98],123,4314182675,[0,0,0,0,0,0,0,0,0,0,0,0,0,0x7b0010,0x10]⟩
def e20_114 : Entry := ⟨6,[3136],63,1092953235,[0,0x101016a0642,0x7a012020,0,0,0x17c4004,0,0,0x5010440,0,0x1010060,0x467674602222,0x6a010600,0x7800772222,0x30203022222]⟩
def e20_115 : Entry := ⟨4,[96,1061,70],155,1075913747,[0,0,0,0,0,0,0,0,0,0]⟩
def e20_116 : Entry := ⟨5,[96,1061],95,4312081554,[0,0,0,0,0,0,0,0,0,0,0x1,0,0x17e1001,0x4c0001,0x3021001]⟩
def e20_117 : Entry := ⟨5,[96,3109],95,2438354,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]⟩
def e20_118 : Entry := ⟨5,[96,3141],95,2434195,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]⟩
def e20_119 : Entry := ⟨4,[96,3173,1158],167,337043,[0,0,0,0,0,0,0,0,0,0]⟩
def e20_120 : Entry := ⟨5,[96,3173],119,337107,[0,0,0,0,0,0,0,0,0,0,0,0,0,0x820010,0x10]⟩
def e20_121 : Entry := ⟨4,[96,97,1158],167,67183827,[0,0,0,0,0,0,0,0,0,0]⟩
def e20_122 : Entry := ⟨5,[96,97],119,67183827,[0,0,0,0,0,0,0,0,0,0,0,0,0,0x840010,0x4c0010]⟩
def e20_123 : Entry := ⟨4,[96,98,1030],182,69215379,[0,0,0,0,0,0,0,0,0,0]⟩
def e20_124 : Entry := ⟨4,[96,98,1158],167,136586387,[0,0,0,0,0,0,0,0,0,0]⟩
def e20_125 : Entry := ⟨5,[96,98],119,153363667,[0,0,0,0,0,0,0,0,0,0,0x860010,0,0,0x870010,0x10010]⟩
def e20_126 : Entry := ⟨6,[96],63,19211475,[0x64304004,0,0,0x830000002460,0x850202,0x880202,0,0,0,0x4000440,0x600,0x59807f1f2222,0x181016d2222,0x83000600,0x30203022222]⟩
def e20_127 : Entry := ⟨5,[3168,1061],95,2438290,[0,0,0,0,0,0,0,0,0,0,0x1000,0,0,0,0]⟩
def e20_128 : Entry := ⟨5,[3168,3109],95,19215570,[0,0,0,0,0,0,0,0,0,0,0,0,0,0x1e0100,0]⟩
def e20_129 : Entry := ⟨5,[3168,3141],95,2368659,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]⟩
def e20_130 : Entry := ⟨4,[3168,1157,3169],199,79059,[0,0,0,0,0,0,0,0,0,0]⟩
def e20_131 : Entry := ⟨5,[3168,1157],79,19215507,[0,0,0,0x9820202,0x8d092020,0,0,0,0,0]⟩
def e20_132 : Entry := ⟨5,[3168,1157],111,2438291,[0,0,0,0,0,0,0,0,0,0x820100,0,0,0,0,0x21000]⟩
def e20_133 : Entry := ⟨5,[3168,3169],119,67183827,[0,0,0,0,0,0,0,0,0,0x8d0010,0,0,0,0,0x1e0010]⟩
def e20_134 : Entry := ⟨6,[3168],63,19211411,[0x65314004,0,0,0x830642,0x90002020,0,0,0,0,0,0x60,0x508b8a622222,0x18c01772222,0x83000600,(pack [0x2028f038e022772,0x304])]⟩
def e20_135 : Entry := ⟨4,[1152,37,3174],151,2368723,[0,0,0,0,0,0,0,0,0,0]⟩
def e20_136 : Entry := ⟨5,[1152,37],95,17199084754,[0,0,0,0,0,0,0,0,0,0,0,0,0,0x92000110,0x30010]⟩
def e20_137 : Entry := ⟨5,[1152,2085],95,1076180179,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]⟩
def e20_138 : Entry := ⟨6,[1152],63,18272822418,[0,0,0,0,0,0,0x20302024206,0x2032020,0x7072020,0x3020202,0x2026000,0x940303932222,0x10301052222,0x300042222,0x3026000]⟩
def e20_139 : Entry := ⟨4,[2176,1061,70],155,1075848339,[0,0,0,0,0,0,0,0,0,0]⟩
def e20_140 : Entry := ⟨5,[2176,1061],95,1092887698,[0,0,0,0,0,0,0,0,0,0,0,0,0x1961001,0,0x31000]⟩
def e20_141 : Entry := ⟨5,[2176,3109],95,19215571,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]⟩
def e20_142 : Entry := ⟨6,[2176],63,18272822482,[0,0,0,0,0,0,0x20203026024,0x3020202,0x3020202,0x6062020,0x2020600,0x39897032222,0x10501032222,0x400032222,0x3020060]⟩
def e20_143 : Entry := ⟨4,[65,1029,102],151,69215379,[0,0,0,0,0,0,0,0,0,0]⟩
def e20_144 : Entry := ⟨5,[65,1029],95,136651922,[0,0,0,0,0,0,0,0,0,0,0,0x10001,0x400001,0x9a1001,0x3021001]⟩
def e20_145 : Entry := ⟨5,[65,3077],95,2438354,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]⟩
def e20_146 : Entry := ⟨4,[65,3141,1158],171,271507,[0,0,0,0,0,0,0,0,0,0]⟩
def e20_147 : Entry := ⟨5,[65,3141],123,275603,[0,0,0,0,0,0,0,0,0,0,0,0,0,0x9d0010,0x10]⟩
def e20_148 : Entry := ⟨4,[65,101,1030],158,2368659,[0,0,0,0,0,0,0,0,0,0]⟩
def e20_149 : Entry := ⟨4,[65,101,3078],158,2368659,[0,0,0,0,0,0,0,0,0,0]⟩
def e20_150 : Entry := ⟨5,[65,101],95,2434195,[0,0,0,0,0,0,0,0,0,0,0xa09f0110,0,0,0,0x2030110]⟩
def e20_151 : Entry := ⟨5,[65,3173],95,17114323,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]⟩
def e20_152 : Entry := ⟨4,[65,98,1062],185,1075913747,[0,0,0,0,0,0,0,0,0,0]⟩
def e20_153 : Entry := ⟨4,[65,98,1158],171,4314178579,[0,0,0,0,0,0,0,0,0,0]⟩
def e20_154 : Entry := ⟨5,[65,98],123,4314182675,[0,0,0,0,0,0,0,0,0,0,0,0xa30010,0,0xa40010,0x10]⟩
def e20_155 : Entry := ⟨6,[65],63,19211411,[0x5d320202,0x1720202,0x9e0101012460,0,0,0x1a54004,0,0,0x5010440,0,0x609c9b112222,0x1010600,0x9e010600,0xa200a12222,0x30203022222]⟩
def e20_156 : Entry := ⟨5,[3137,1029],95,2434258,[0,0,0,0,0,0,0,0,0,0,0,0x11000,0,0,0]⟩
def e20_157 : Entry := ⟨5,[3137,3077],95,2438354,[0,0,0,0,0,0,0,0,0,0,0,0,0xf0100,0,0]⟩
def e20_158 : Entry := ⟨5,[3137,101],95,2434195,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0x2030110]⟩
def e20_159 : Entry := ⟨5,[3137,3173],95,17114323,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]⟩
def e20_160 : Entry := ⟨5,[3137,1157],79,19211475,[0,0x790a2020,0xa9d0202,0,0,0,0,0,0,0]⟩
def e20_161 : Entry := ⟨5,[3137,1157],111,2434259,[0,0,0,0,0,0,0,0,0x9d0100,0,0,0,0,0,0x21000]⟩
def e20_162 : Entry := ⟨6,[3137],63,19211411,[0x5e330202,0x7a012020,0x101019e0642,0,0,0,0,0,0,0,0x46a8a7572222,0x1010060,0x9e010600,0xaa00a92222,(pack [0x202ac03ab022772,0x305])]⟩
def e20_163 : Entry := ⟨5,[97,1029],95,86320274,[0,0,0,0,0,0,0,0,0,0,0,0,0,0x4c0001,0]⟩
def e20_164 : Entry := ⟨5,[97,3077],95,2438354,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]⟩
def e20_165 : Entry := ⟨5,[97,3141],95,2368659,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]⟩
def e20_166 : Entry := ⟨4,[97,3173,1157],199,337107,[0,0,0,0,0,0,0,0,0,0]⟩
def e20_167 : Entry := ⟨5,[97,3173],119,337107,[0,0,0,0,0,0,0,0,0,0xb10010,0,0,0,0,0x10]⟩
def e20_168 : Entry := ⟨5,[97,1157],79,17266189523,[0,0,0,0x9840202,0xb1092020,0,0,0,0,0]⟩
def e20_169 : Entry := ⟨5,[97,1157],111,17182303443,[0,0,0,0,0,0,0,0,0,0xb10100,0,0,0,0,0x21000]⟩
def e20_170 : Entry := ⟨6,[97],63,86320339,[0,0,0,0x850202,0xb20000002460,0,0,0,0,0,0x62afae1f2222,0x600,0x1b001a12222,0xb2000600,(pack [0x202b403b3022772,0x304])]⟩
def e20_171 : Entry := ⟨5,[3169,1029],95,69547154,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]⟩
def e20_172 : Entry := ⟨4,[3169,3077,3142],155,2438163,[0,0,0,0,0,0,0,0,0,0]⟩
def e20_173 : Entry := ⟨5,[3169,3077],95,17118418,[0,0,0,0,0,0,0,0,0,0,0,0,0xb7010110,0x1e0100,0x2030110]⟩
def e20_174 : Entry := ⟨5,[3169,3141],95,2434195,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]⟩
def e20_175 : Entry := ⟨4,[3169,98,1158],167,136586387,[0,0,0,0,0,0,0,0,0,0]⟩
def e20_176 : Entry := ⟨5,[3169,98],119,153363667,[0,0,0,0,0,0,0,0,0,0,0,0,0,0xba0010,0x10010]⟩
def e20_177 : Entry := ⟨6,[3169],63,86320275,[0,0,0,0x90002020,0xb20642,0xbb0202,0,0,0,0x4000440,0x50b8b6592222,0x60,0x1b901a92222,0xb2000600,0x30203022222]⟩
def e20_178 : Entry := ⟨4,[1153,5,3142],155,2372755,[0,0,0,0,0,0,0,0,0,0]⟩
def e20_179 : Entry := ⟨5,[1153,5],95,17182307538,[0,0,0,0,0,0,0,0,0,0,0,0,0xbd010110,0,0x30010]⟩
def e20_180 : Entry := ⟨5,[1153,2053],95,69547219,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]⟩
def e20_181 : Entry := ⟨6,[1153],63,17266189458,[0,0,0,0,0,0,0x2032020,0x20302024206,0x3020202,0x6062020,0xbf0303be2222,0x2026000,0x10301052222,0x300042222,0x3026000]⟩
def e20_182 : Entry := ⟨4,[2177,1029,102],151,69215379,[0,0,0,0,0,0,0,0,0,0]⟩
def e20_183 : Entry := ⟨5,[2177,1029],95,86254738,[0,0,0,0,0,0,0,0,0,0,0,0,0,0xc11001,0x31000]⟩
def e20_184 : Entry := ⟨5,[2177,3077],95,2438355,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]⟩
def e20_185 : Entry := ⟨6,[2177],63,17266193554,[0,0,0,0,0,0,0x3020202,0x20203026024,0x7072020,0x3020202,0x3c3c2032222,0x2020600,0x10501032222,0x400032222,0x3020060]⟩
def e20_186 : Entry := ⟨5,[98,1029],95,86320274,[0,0,0,0x860001,0,0,0,0,0,0,0,0,0,0x10001,0]⟩
def e20_187 : Entry := ⟨5,[98,3077],95,2438354,[0,0,0,0,0,0,0,0,0,0,0,0,0x100,0,0]⟩
def e20_188 : Entry := ⟨5,[98,1061],95,1076176018,[0,0,0xa30001,0,0,0,0,0,0,0,0,0,0x1,0,0]⟩
def e20_189 : Entry := ⟨5,[98,3109],95,19215570,[0,0,0,0,0,0,0,0,0,0,0,0,0,0x10100,0]⟩
def e20_190 : Entry := ⟨5,[98,1157],79,4448396435,[0,0x7b0a2020,0xaa40202,0x9870202,0xba092020,0,0,0,0xa094004,0x90a4004]⟩
def e20_191 : Entry := ⟨5,[98,1157],111,4448396435,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0x21000]⟩
def e20_192 : Entry := ⟨6,[98],63,153429139,[0,0x7c012020,0x1a50202,0x880202,0xbb002020,0x10000002460,0,0,0x1084004,0x84004,0x77c6c56d2222,0xa9c8c7a12222,0x600,0x1000600,(pack [0x202ca03c9022772,0x304])]⟩
def e20_193 : Entry := ⟨7,[],31,19211411,[0x665f54348888,0x7d0101738888,0xad0101a68888,0x910000898888,0xbc0000b58888,0x10000cb8888,0x29995028888,0x2c4c0028888,0x10501028888,0x400028888]⟩
def entries20 : List Entry := [e20_0,e20_1,e20_2,e20_3,e20_4,e20_5,e20_6,e20_7,e20_8,e20_9,e20_10,e20_11,e20_12,e20_13,e20_14,e20_15,e20_16,e20_17,e20_18,e20_19,e20_20,e20_21,e20_22,e20_23,e20_24,e20_25,e20_26,e20_27,e20_28,e20_29,e20_30,e20_31,e20_32,e20_33,e20_34,e20_35,e20_36,e20_37,e20_38,e20_39,e20_40,e20_41,e20_42,e20_43,e20_44,e20_45,e20_46,e20_47,e20_48,e20_49,e20_50,e20_51,e20_52,e20_53,e20_54,e20_55,e20_56,e20_57,e20_58,e20_59,e20_60,e20_61,e20_62,e20_63,e20_64,e20_65,e20_66,e20_67,e20_68,e20_69,e20_70,e20_71,e20_72,e20_73,e20_74,e20_75,e20_76,e20_77,e20_78,e20_79,e20_80,e20_81,e20_82,e20_83,e20_84,e20_85,e20_86,e20_87,e20_88,e20_89,e20_90,e20_91,e20_92,e20_93,e20_94,e20_95,e20_96,e20_97,e20_98,e20_99,e20_100,e20_101,e20_102,e20_103,e20_104,e20_105,e20_106,e20_107,e20_108,e20_109,e20_110,e20_111,e20_112,e20_113,e20_114,e20_115,e20_116,e20_117,e20_118,e20_119,e20_120,e20_121,e20_122,e20_123,e20_124,e20_125,e20_126,e20_127,e20_128,e20_129,e20_130,e20_131,e20_132,e20_133,e20_134,e20_135,e20_136,e20_137,e20_138,e20_139,e20_140,e20_141,e20_142,e20_143,e20_144,e20_145,e20_146,e20_147,e20_148,e20_149,e20_150,e20_151,e20_152,e20_153,e20_154,e20_155,e20_156,e20_157,e20_158,e20_159,e20_160,e20_161,e20_162,e20_163,e20_164,e20_165,e20_166,e20_167,e20_168,e20_169,e20_170,e20_171,e20_172,e20_173,e20_174,e20_175,e20_176,e20_177,e20_178,e20_179,e20_180,e20_181,e20_182,e20_183,e20_184,e20_185,e20_186,e20_187,e20_188,e20_189,e20_190,e20_191,e20_192,e20_193]
def db20 : Array Entry := entries20.toArray
def g21 : Spec := ⟨rootsOf 62,targetOf 18212834798890699968,[0,1,2,3,4,5,8,9,12,13,16,17,18,19,20,21,24,25,32,33,34,35,36,37,40,41,48,49,50,51,52,53,56,57],[(domainOf 62 16 0,5)],[[]],#[],1⟩
def entries21 : List Entry := []
def db21 : Array Entry := entries21.toArray
def g22 : Spec := ⟨rootsOf 47,targetOf 18224093969492012264,[0,1,2,4,8,9,12,16,17,18,20,24,25,28,32,33,34,36,40,41,48,49,50,52,56,57],[(domainOf 47 0 32,5),(domainOf 47 1 0,5),(domainOf 47 32 0,5),(domainOf 47 8 0,4),(domainOf 47 40 0,4)],[[]],#[1,2,3,4,5,16384,16385,16386,16387,16388,16389,16390,16391],4⟩
def e22_0 : Entry := ⟨4,[65,1029],94,98415,[0,0,0,0,0,0,0,0,0,0]⟩
def e22_1 : Entry := ⟨4,[65,1125],87,98415,[0,0,0,0,0,0,0,0,0,0]⟩
def e22_2 : Entry := ⟨5,[65],63,98415,[0,0,0,0,0,0,0,0,0,0,0x150110,0,0,0x360110,0x200110]⟩
def e22_3 : Entry := ⟨4,[1089,2053],94,82013,[0,0,0,0,0,0,0,0,0,0]⟩
def e22_4 : Entry := ⟨4,[1089,2149],87,81991,[0,0,0,0,0,0,0,0,0,0]⟩
def e22_5 : Entry := ⟨5,[1089],63,196686,[0,0,0,0,0,0,0,0,0,0,0x811001,0,0,0x931001,0x21001]⟩
def e22_6 : Entry := ⟨5,[2113],63,196719,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0x200110]⟩
def e22_7 : Entry := ⟨5,[3137],63,229455,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0x21001]⟩
def e22_8 : Entry := ⟨6,[],31,229503,[0x11118888,0x11118888,0xcba78888,0x111111a8a8,0x34438888,0x34438888,0x10000a8a8,0x20000a8a8,0x28a8a,0x28a8a]⟩
def entries22 : List Entry := [e22_0,e22_1,e22_2,e22_3,e22_4,e22_5,e22_6,e22_7,e22_8]
def db22 : Array Entry := entries22.toArray
def g23 : Spec := ⟨rootsOf 31,targetOf 18368191565683813608,[0,1,2,4,8,9,12,16,17,18,20,24,32,33,34,36,40,41,44,48,49,50,52,56],[(domainOf 31 0 16,7)],[[]],#[],1⟩
def entries23 : List Entry := []
def db23 : Array Entry := entries23.toArray
def g24 : Spec := ⟨rootsOf 31,targetOf 18368772107823414504,[0,1,2,4,8,9,16,18,20,24,32,33,34,36,40,41,48,50,52,56],[(domainOf 31 0 16,5),(domainOf 31 8 0,5),(domainOf 31 16 0,5),(domainOf 31 4 0,4),(domainOf 31 2 0,4),(domainOf 31 1 0,4),(domainOf 31 17 0,4)],[[]],#[1,2,3,4,5,6,7,16384,16385],4⟩
def e24_0 : Entry := ⟨4,[1089,2149],87,71,[0,0,0,0,0,0,0,0,0,0]⟩
def e24_1 : Entry := ⟨5,[1089],63,1007,[0,0,0x30001,0,0,0,0,0,0,0,0,0,0,0x711001,0x200110]⟩
def e24_2 : Entry := ⟨6,[],31,1023,[0x45648888,0x35638888,0x34838888,0x111161a8a8,0x11118888,0x11118888,0x28a8a,0x20000a8a8,0x20000a8a8,0x8888]⟩
def entries24 : List Entry := [e24_0,e24_1,e24_2]
def db24 : Array Entry := entries24.toArray
def g25 : Spec := ⟨rootsOf 47,targetOf 18368774315436474088,[0,1,2,4,8,16,17,18,20,24,32,34,36,40,48,50,52,56],[(domainOf 47 32 0,7)],[[]],#[],1⟩
def entries25 : List Entry := []
def db25 : Array Entry := entries25.toArray
def g26 : Spec := ⟨rootsOf 55,targetOf 18374401693258280172,[0,1,4,8,9,12,16,24,32,33,40,41,48,56],[(domainOf 55 2 0,5)],[[]],#[],1⟩
def entries26 : List Entry := []
def db26 : Array Entry := entries26.toArray
def g27 : Spec := ⟨rootsOf 63,targetOf 18368772107823279336,[0,1,2,4,8,9,12,16,17,18,20,24,32,33,34,36,40,41,48,50,52,56],[(domainOf 63 0 16,8),(domainOf 63 2 0,8),(domainOf 63 32 0,8),(domainOf 63 0 32,7),(domainOf 63 16 0,7),(domainOf 63 4 0,6),(domainOf 63 1 0,6),(domainOf 63 0 8,6),(domainOf 63 8 0,6),(domainOf 63 17 0,5),(domainOf 63 8 16,5),(domainOf 63 8 32,5),(domainOf 63 16 32,5),(domainOf 63 24 0,4),(domainOf 63 1 48,4),(domainOf 63 17 32,4),(domainOf 63 40 0,4),(domainOf 63 56 0,4)],[[]],#[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,65,66,67,68,69,129,131,132,133,134,135,193,194,195,196,197,321,322,323,324,325,449,451,16384,16385,16386,16387,16388,16389,16390,16391,16392,16393,16394,16395,16396,16397,16398,16399,16400,16401,16402,16403,16404,16405,16406,16407,16408,16409,16410,16411,16412,16413,16414,16415,16416,16417,16418,16419,16420,16421,16422,16423,16424,16425,16426,16427,16428,16429,16430,16431,16432,16433,16434,16435,16436,16437,16438,16439,16440,16441,16442,16443,16444,16445,16446],7⟩
def e27_0 : Entry := ⟨6,[64,1062,103],445,140799,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0x3130110,0x2930110,0,0x109d0110,0xfa00110,0]⟩
def e27_1 : Entry := ⟨5,[64,1062,1127,2120],697,135655,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]⟩
def e27_2 : Entry := ⟨6,[64,1062,1127],445,469366,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0x15051001,0,0,0,0]⟩
def e27_3 : Entry := ⟨6,[64,1062,2151],445,208383,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0x109d0110,0xfa00110,0]⟩
def e27_4 : Entry := ⟨6,[64,1062,3175],445,141695,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]⟩
def e27_5 : Entry := ⟨7,[64,1062],189,159615,[(pack [0x142850a1431dace8,0xa]),0xc183068888,0xa142858888,0x3a74e9d8888,0x3a74e9d8888,0x3a74e9d8888,0x3e7cf9f8888,0x3e7cf9f8888,0x3e7cf9f8888,0x3a74e9d8888,0x26189938888,0x26149938888,0x58b55a98888,0xe9d1274e9d8cc8,0xf9f3e7c71f8cc8]⟩
def e27_6 : Entry := ⟨7,[64,1126],183,26495,[0x3c78f1e8888,0xa1429d8888,0x3c78f1e8888,0x3a74e9d8888,0xe9e3a74e9da8a8,0x3a74e9d8888,0x3e7cf9f8888,0xf1e3c78f1ea8a8,0x3e7cf9f8888,0x3a74e9d8888,0xc183068888,0x3c78f1e8888,0xa142858888,0x3a74e9d8888,0x3e7cf9f8888]⟩
def e27_7 : Entry := ⟨7,[64,3174],183,28543,[0x3c78f1e8888,0xa1429d8888,0x3c78f1e8888,0x3a74e9d8888,0xe9e3a74e9da8a8,0x3a74e9d8888,0x3e7cf9f8888,0xf1e3c78f1ea8a8,0x3e7cf9f8888,0x3a74e9d8888,0xc183068888,0x3c78f1e8888,0xa142858888,0x3a74e9d8888,0x3e7cf9f8888]⟩
def e27_8 : Entry := ⟨8,[64],127,159615,[0x264c9938888,0x142850a14286ace0,0x264c9938888,0xc183068888,0x264c9938888,0xa142858888,0x24489128888,0x9132448912a8a8,0x24489128888,0x24489128888,0x2850a148888,0x993264c993a8a8,0x2850a148888,0x2850a148888,0x24489128888,0x142860e00,(pack [0x498526b8981affa,0x264c99302]),0x142850e00,(pack [0xc02850ebc285affa,0xa1428510]),(pack [0x109120000912affa,0x240090524]),(pack [0x8a05280ca02affa,0x2850a1404])]⟩
def e27_9 : Entry := ⟨5,[1088,102,1126,2280],567,8559,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]⟩
def e27_10 : Entry := ⟨6,[1088,102,1126],439,139631,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0x1e0001,0,0,0,0x321000]⟩
def e27_11 : Entry := ⟨7,[1088,102],255,139647,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0x4330110,0xe8d1001,0x59f1001,0,0,0,0,0,0,0x70100]⟩
def e27_12 : Entry := ⟨6,[1088,1126,2055],382,139647,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0x100]⟩
def e27_13 : Entry := ⟨5,[1088,1126,2087,134],813,8555,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]⟩
def e27_14 : Entry := ⟨5,[1088,1126,2087,2214],797,379,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]⟩
def e27_15 : Entry := ⟨6,[1088,1126,2087],381,139643,[0,0,0,0,0,0,0,0,0,0,0,0,0,0x13b61001,0x1ba81001,0,0,0,0,0,0]⟩
def e27_16 : Entry := ⟨6,[1088,1126,2119],379,139647,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0x100]⟩
def e27_17 : Entry := ⟨6,[1088,1126,134],431,74110,[0,0,0,0,0,0,0,0,0,0,0,0x1b231001,0,0,0x12a41001,0,0,0,0,0,0xa0100]⟩
def e27_18 : Entry := ⟨6,[1088,1126,2214],415,8574,[0,0,0,0,0,0,0,0,0,0,0,0x1ba31001,0,0,0x11261001,0,0,0,0,0,0x100100]⟩
def e27_19 : Entry := ⟨7,[1088,1126],255,141694,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0x3b31001,0xeba1001,0x1d9f1001,0x351000,0x1c131001,0x391000,0,0x9161001,0xa941001,0x81000]⟩
def e27_20 : Entry := ⟨6,[1088,2150,3174],439,27519,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0x320010]⟩
def e27_21 : Entry := ⟨6,[1088,2150,134],431,74111,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]⟩
def e27_22 : Entry := ⟨6,[1088,2150,2214],415,8575,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]⟩
def e27_23 : Entry := ⟨7,[1088,2150],255,141695,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0x1e870110,0xebe1001,0x1f9f1001,0,0,0,0,0,0,0x80100]⟩
def e27_24 : Entry := ⟨6,[1088,3174,1031],382,2238846,[0,0,0,0,0,0,0,0,0,0,0,0,0,0xd0001,0,0,0,0,0,0,0x1]⟩
def e27_25 : Entry := ⟨6,[1088,3174,1095],379,207230,[0,0,0,0,0,0,0,0,0,0,0,0,0x80001,0,0,0,0,0,0,0,0x1]⟩
def e27_26 : Entry := ⟨7,[1088,3174],255,139646,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0x1e881001,0xe8d1001,0x59f1001,0x410010,0,0x420010,0,0xb120110,0xa150110,0x70010]⟩
def e27_27 : Entry := ⟨7,[1088,134],239,189823,[0xf1e0440,0x3670d9c4206,0xf1e2020,0,0,0,0,0xf1e2020,0,0,0xd9b6000,0x3c78f1e2222,0xe1c6000,0x7c35d0d2222,(pack [0x7c61f3e7cf9f7227,0x1e]),0,0xf1e2020,0,0,0,0x489000700]⟩
def e27_28 : Entry := ⟨7,[1088,2214],223,173439,[0xf1e0440,0x3670d9c4206,0xf1e2020,0,0,0,0,0xf1d2020,0,0,0xd9b6000,0x3c78f1e2222,0xe1c6000,0x7e2dd8b2222,(pack [0x74e9d3a3ce8c7227,0x3a]),0,0xf1e2020,0,0,0,0x50a020700]⟩
def e27_29 : Entry := ⟨7,[1088,1120],255,141694,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0x3881001,0xb9a1001,0xc981001,0,0,0x1c851001,0,0x9161001,0xa941001,0x10143851111]⟩
def e27_30 : Entry := ⟨7,[1088,3168],255,1057150,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0x3881001,0xb9a1001,0xc981001,0,0,0x2c20110,0,0,0,0x10143851111]⟩
def e27_31 : Entry := ⟨7,[1088,1122],255,142718,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0x3881001,0xb9a1001,0xc981001,0x1a861001,0,0,0,0,0,0x10183861111]⟩
def e27_32 : Entry := ⟨7,[1088,3170],255,1058174,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0x3881001,0xb9a1001,0xc981001,0x3410110,0,0,0,0,0xa150110,0x10183861111]⟩
def e27_33 : Entry := ⟨8,[1088],127,189823,[0x993264c9938cc8,0x142860c14286ca0e,0x993264c993a8a8,0x8e1a3068888,0x264c9938888,0x92164058888,0x24489128888,0x9132448912a8a8,0x24489128888,0x24489128888,0x2850a148888,0x993264c993a8a8,0x2850a148888,0x2850a148888,0x24489128888,0x14285e000,(pack [0x4c981264c981aaaa,0x26]),0x18306e000,(pack [0x1e188781da08aaaa,0x80]),(pack [0x489002510904faaf,0x244800024]),(pack [0x8a142850102faaf,0x2914a0328])]⟩
def e27_34 : Entry := ⟨7,[2112,1094],191,189823,[0xf1e0440,0xa742854206,0xf1e2020,0,0,0,0,0xf1d2020,0,0,0,0xf1e2020,0,0,0,0x2856000,0x3c04f012222,0xe926000,0xe203882222,(pack [0x1d0024e847227,0x3a]),(pack [0x7c1823e7c1027227,0x1c])]⟩
def e27_35 : Entry := ⟨6,[2112,1122,2055],382,11647,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]⟩
def e27_36 : Entry := ⟨7,[2112,1122],255,11646,[0,0,0,0,0,0x50001,0,0,0,0,0,0,0,0,0,0,0,0,0x4070110,0,0,0x26061001,0,0,0,0,0,0x10183861111]⟩
def e27_37 : Entry := ⟨6,[2112,3170,1031],382,9599,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]⟩
def e27_38 : Entry := ⟨7,[2112,3170],255,11647,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0x4070110,0,0,0x34e0110,0,0,0,0,0xa150110,0x10183861111]⟩
def e27_39 : Entry := ⟨8,[2112],127,61311,[0x993264c9938cc8,0x142860c18285e0ac,0x264c9938888,0xc183068888,0x264c9938888,0x9e166858888,0x24489128888,0x9132448912a8a8,0x24489128888,0x24489128888,0x2850a148888,0x993264c993a8a8,0x2850a148888,0x2850a148888,0x24489128888,0x142850e00,(pack [0x4c981264c981aaaa,0x26]),0x1834b00e0,(pack [0x183080c1c306aaaa,0xc]),(pack [0x9122400912aaaa,0x24]),(pack [0x50a022850a02aaaa,0x28])]⟩
def e27_40 : Entry := ⟨6,[3136,1120,2119],379,11647,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]⟩
def e27_41 : Entry := ⟨7,[3136,1120],255,2107774,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0x4070110,0,0,0,0,0x28851001,0,0x9161001,0xa941001,0x10143851111]⟩
def e27_42 : Entry := ⟨6,[3136,3168,1095],379,9599,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]⟩
def e27_43 : Entry := ⟨7,[3136,3168],255,10623,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0x4070110,0,0,0,0,0x2d30110,0,0,0,0x10143851111]⟩
def e27_44 : Entry := ⟨8,[3136],127,28543,[0x264c9938888,0x142860a142850eca,0x993264c993a8a8,0xa81a9068888,0x264c9938888,0xa142858888,0x24489128888,0x9132448912a8a8,0x24489128888,0x24489128888,0x2850a148888,0x993264c993a8a8,0x2850a148888,0x2850a148888,0x24489128888,0x142cb00e0,(pack [0x4c981264c981aaaa,0x26]),0x142850e00,(pack [0x142880a1c285aaaa,0xa]),(pack [0x9122400912aaaa,0x24]),(pack [0x50a022850a02aaaa,0x28])]⟩
def e27_45 : Entry := ⟨7,[96,1094],191,157567,[0,0x3060202,0xf1e2020,0x3062020,0,0x4084004,0,0xf1d2020,0xe9d0440,0,0,0xf1e2020,0,0,0,0xa182862222,0x3c04f012222,0x3066000,0xa202882222,0x7401d2222,0x3e08f822222]⟩
def e27_46 : Entry := ⟨8,[96],127,26495,[0x264c9938888,0xc183068888,0x264c9938888,0x183060c18386ace0,0x264c9938888,0x101c3888888,0x24489128888,0x9132448912a8a8,0x24489128888,0x24489128888,0x2850a148888,0x993264c993a8a8,0x2850a148888,0x2850a148888,0x24489128888,0x183060e00,(pack [0x4c981264c981aaaa,0x26]),(pack [0x183050d58305aaaa,0xc]),0x183080e00,(pack [0x9122400912aaaa,0x24]),(pack [0x8a06280ca02affa,0x2850a1404])]⟩
def e27_47 : Entry := ⟨7,[1120,2118],191,61311,[0xf1e0440,0x28b92020,0xf1e0202,0,0xf1e2020,0x3870440,0,0xf1d2020,0,0,0,0xf1e2020,0,0,0,0x10144052222,0x3c04f012222,0x3870060,0xc143052222,0x7401d2222,0x3e08f822222]⟩
def e27_48 : Entry := ⟨7,[1120,3170],247,2141567,[0xf1e0440,0,0,0,0xf1d2020,0,0,0xf1e2020,0,0,0x3886000,0xf1e2020,0x2850202,0xe874004,0x39f4004,0x3060202,0xf1e2020,0x3870060,0xe9d0202,0x1f3e20f952470,0x4070600]⟩
def e27_49 : Entry := ⟨8,[1120],127,2107775,[0x993264c9938cc8,0xa41a3068888,0x264c9938888,0x1c3860c18386ca0e,0x993264c993a8a8,0x3d90e1c387a8a8,0x24489128888,0x9132448912a8a8,0x24489128888,0x9122448912c88c,0x2850a148888,0x993264c993a8a8,0x2850a148888,0xa142850a148cc8,0x24489128888,0x1c388e000,(pack [0x4c981264c981aaaa,0x26]),(pack [0x603850e1c385aaaa,0xf]),0x18306e000,(pack [0x48900241c904faaf,0x244800024]),(pack [0x8a142850102faaf,0x281ca0328])]⟩
def e27_50 : Entry := ⟨7,[2144,1094],191,61311,[0xf1e0440,0x3060202,0xf1e2020,0x3062020,0,0x3870440,0,0xf1d2020,0,0,0,0xf1e2020,0,0,0,0xa182862222,0x3c04f012222,0x3066000,0xe143852222,0x7401d2222,(pack [0x7c1823e7c1027227,0x1c])]⟩
def e27_51 : Entry := ⟨8,[2144],127,2125695,[0x993264c9938cc8,0xc183068888,0x264c9938888,0x183860c18306e0ac,0x264c9938888,0xe1c3878888,0x24489128888,0x9132448912a8a8,0x24489128888,0x24489128888,0x2850a148888,0x993264c993a8a8,0x2850a148888,0x2850a148888,0x24489128888,0x183060e00,(pack [0x4c981264c981aaaa,0x26]),(pack [0x183050d6c305aaaa,0xc]),0x1830700e0,(pack [0x9122400912aaaa,0x24]),(pack [0x50a022850a02aaaa,0x28])]⟩
def e27_52 : Entry := ⟨7,[3168,1094],191,126847,[0,0x29c22020,0xf1e2020,0,0xf1e2020,0x4084004,0,0xf1d2020,0,0,0,0xf1e2020,0,0,0,0xe143852222,0x3c04f012222,0x4086000,0xa182862222,0x7401d2222,0x3e08f822222]⟩
def e27_53 : Entry := ⟨7,[3168,1122],247,126847,[0,0,0xf1e2020,0,0xf1d2020,0,0,0xf1e2020,0,0,0x3870060,0xf1e2020,0x2850202,0,0,0x3060202,0xf1e2020,0x3886000,0xe9d0202,0xf9f2020,0x3886000]⟩
def e27_54 : Entry := ⟨8,[3168],127,27519,[0x264c9938888,0xa81a3868888,0x264c9938888,0x183860e1c3060eca,0x993264c993a8a8,0x4080e1ef08a8a8,0x24489128888,0x9132448912a8a8,0x24489128888,0x9122448912c88c,0x2850a148888,0x993264c993a8a8,0x2850a148888,0xa142850a148cc8,0x24489128888,0x1c38700e0,(pack [0x4c981264c981aaaa,0x26]),(pack [0x204051174405aaaa,0x10]),0x183060e00,(pack [0x9122400912aaaa,0x24]),(pack [0x50a022850a02aaaa,0x28])]⟩
def e27_55 : Entry := ⟨7,[98,1030],191,24959,[0xf1e0440,0x2854004,0,0x4084004,0,0x2852020,0xe9d0440,0xf1d2020,0,0,0xf9f0440,0xf1e2020,0,0,0,0x2856000,0x3c04f012222,0xa142852222,0xc203082222,(pack [0x1d0044e847227,0x3a]),(pack [0x7c1823e7c1027227,0x16])]⟩
def e27_56 : Entry := ⟨8,[98],127,26495,[0x264c9938888,0xa142858888,0x264c9938888,0x101c3888888,0x264c9938888,0x142850a14385ace0,0x24489128888,0x9132448912a8a8,0x24489128888,0x24489128888,0x2850a148888,0x993264c993a8a8,0x2850a148888,0x2850a148888,0x24489128888,(pack [0x142860b80285aaaa,0xa]),(pack [0x4c981264c981aaaa,0x26]),0x142850e00,0x142880e00,(pack [0x9122400912aaaa,0x24]),(pack [0x50a022850a02aaaa,0x28])]⟩
def e27_57 : Entry := ⟨7,[1122,2054],191,323455,[0,0x26350440,0xf1e2020,0x3870440,0xf1e2020,0,0,0xf1d2020,0,0,0,0xf1e2020,0,0,0,0x3870060,0x3c04f012222,0x10144052222,0xa182862222,0x7401d2222,0x3e08f822222]⟩
def e27_58 : Entry := ⟨8,[1122],127,126847,[0x264c9938888,0xb364058888,0x993264c993a8a8,0x3de0e1c387a8a8,0x993264c993a8a8,0x1c3850a14385ca0e,0x24489128888,0x9132448912a8a8,0x24489128888,0x24489128888,0x2850a148888,0x993264c993a8a8,0x2850a148888,0x2850a148888,0x24489128888,(pack [0x883860e1c386aaaa,0xf]),(pack [0x4c981264c981aaaa,0x26]),0x1c388e000,0x14285e000,(pack [0x9122400912aaaa,0x24]),(pack [0x50a022850a02aaaa,0x28])]⟩
def e27_59 : Entry := ⟨7,[2146,1030],191,60799,[0xf1e0440,0x2854004,0xf1e2020,0x3870440,0,0x2852020,0,0xf1d2020,0,0,0,0xf1e2020,0,0,0,0x2856000,0x3c04f012222,0xa142852222,0xe183862222,0x7401d2222,0x3e08f822222]⟩
def e27_60 : Entry := ⟨8,[2146],127,94079,[0x264c9938888,0xa142858888,0x993264c993a8a8,0xe1c3878888,0x264c9938888,0x143850a14285e0ac,0x24489128888,0x9132448912a8a8,0x24489128888,0x24489128888,0x2850a148888,0x993264c993a8a8,0x2850a148888,0x2850a148888,0x24489128888,(pack [0x142860b90285aaaa,0xa]),(pack [0x4c981264c981aaaa,0x26]),0x142850e00,0x1428700e0,(pack [0x109120000912affa,0x240090524]),(pack [0x8a05280ca02affa,0x2850a1404])]⟩
def e27_61 : Entry := ⟨7,[3170,1030],191,2141567,[0xf1e0440,0x27410440,0,0x4084004,0xf1e2020,0,0xe9d4004,0xf1d2020,0,0,0,0xf1e2020,0,0,0,0x4086000,0x3c04f012222,0xe143852222,0xc143052222,0x7401d2222,0x3e08f822222]⟩
def e27_62 : Entry := ⟨8,[3170],127,61311,[0x264c9938888,0xb3e4858888,0x264c9938888,0x4080e1ec88a8a8,0x993264c993a8a8,0x143850e1c2850eca,0x24489128888,0x9132448912a8a8,0x24489128888,0x24489128888,0x2850a148888,0x993264c993a8a8,0x2850a148888,0x2850a148888,0x24489128888,(pack [0x204061198406aaaa,0x10]),(pack [0x4c981264c981aaaa,0x26]),0x1c38700e0,0x142850e00,(pack [0x9122400912aaaa,0x24]),(pack [0x8a08280ca02affa,0x2850a1404])]⟩
def e27_63 : Entry := ⟨9,[],63,26495,[0x2040818888,0xab425318888,0x2040818888,0xbf72d578888,0x2040818888,0xcf971e18888,0x8888,0x10000000a8a8,0x8888,0x8888,0x4081028888,0x810204081a8a8,0x4081028888,0x4081028888,0x8888]⟩
def entries27 : List Entry := [e27_0,e27_1,e27_2,e27_3,e27_4,e27_5,e27_6,e27_7,e27_8,e27_9,e27_10,e27_11,e27_12,e27_13,e27_14,e27_15,e27_16,e27_17,e27_18,e27_19,e27_20,e27_21,e27_22,e27_23,e27_24,e27_25,e27_26,e27_27,e27_28,e27_29,e27_30,e27_31,e27_32,e27_33,e27_34,e27_35,e27_36,e27_37,e27_38,e27_39,e27_40,e27_41,e27_42,e27_43,e27_44,e27_45,e27_46,e27_47,e27_48,e27_49,e27_50,e27_51,e27_52,e27_53,e27_54,e27_55,e27_56,e27_57,e27_58,e27_59,e27_60,e27_61,e27_62,e27_63]
def db27 : Array Entry := entries27.toArray
def specBy : Nat → Spec
 | 0 => g0
 | 1 => g1
 | 2 => g2
 | 3 => g3
 | 4 => g4
 | 5 => g5
 | 6 => g6
 | 7 => g7
 | 8 => g8
 | 9 => g9
 | 10 => g10
 | 11 => g11
 | 12 => g12
 | 13 => g13
 | 14 => g14
 | 15 => g15
 | 16 => g16
 | 17 => g17
 | 18 => g18
 | 19 => g19
 | 20 => g20
 | 21 => g21
 | 22 => g22
 | 23 => g23
 | 24 => g24
 | 25 => g25
 | 26 => g26
 | 27 => g27
 | _ => g0
def dbBy : Nat → Array Entry
 | 0 => db0
 | 1 => db1
 | 2 => db2
 | 3 => db3
 | 4 => db4
 | 5 => db5
 | 6 => db6
 | 7 => db7
 | 8 => db8
 | 9 => db9
 | 10 => db10
 | 11 => db11
 | 12 => db12
 | 13 => db13
 | 14 => db14
 | 15 => db15
 | 16 => db16
 | 17 => db17
 | 18 => db18
 | 19 => db19
 | 20 => db20
 | 21 => db21
 | 22 => db22
 | 23 => db23
 | 24 => db24
 | 25 => db25
 | 26 => db26
 | 27 => db27
 | _ => #[]
def AllChecks : Prop := ∀ i ∈ List.range 28, ∀ j, j < (dbBy i).size → verify (specBy i) (dbBy i) ((dbBy i)[j]?.getD default) = true
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e0_0 : verify g0 db0 e0_0 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem all0 : entries0.all (verify g0 db0) = true := by
 simp only [entries0,List.all_cons,List.all_nil,ok_e0_0,Bool.and_self]
theorem checked0 : ∀ j, j < db0.size → verify g0 db0 (db0[j]?.getD default) = true := checkedList entries0 all0
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e1_0 : verify g1 db1 e1_0 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem all1 : entries1.all (verify g1 db1) = true := by
 simp only [entries1,List.all_cons,List.all_nil,ok_e1_0,Bool.and_self]
theorem checked1 : ∀ j, j < db1.size → verify g1 db1 (db1[j]?.getD default) = true := checkedList entries1 all1
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e2_0 : verify g2 db2 e2_0 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem all2 : entries2.all (verify g2 db2) = true := by
 simp only [entries2,List.all_cons,List.all_nil,ok_e2_0,Bool.and_self]
theorem checked2 : ∀ j, j < db2.size → verify g2 db2 (db2[j]?.getD default) = true := checkedList entries2 all2
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e3_0 : verify g3 db3 e3_0 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem all3 : entries3.all (verify g3 db3) = true := by
 simp only [entries3,List.all_cons,List.all_nil,ok_e3_0,Bool.and_self]
theorem checked3 : ∀ j, j < db3.size → verify g3 db3 (db3[j]?.getD default) = true := checkedList entries3 all3
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e4_0 : verify g4 db4 e4_0 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem all4 : entries4.all (verify g4 db4) = true := by
 simp only [entries4,List.all_cons,List.all_nil,ok_e4_0,Bool.and_self]
theorem checked4 : ∀ j, j < db4.size → verify g4 db4 (db4[j]?.getD default) = true := checkedList entries4 all4
theorem checked5 (j) (h : j < db5.size) : verify g5 db5 (db5[j]?.getD default) = true := by change j < 0 at h; omega
theorem checked6 (j) (h : j < db6.size) : verify g6 db6 (db6[j]?.getD default) = true := by change j < 0 at h; omega
theorem checked7 (j) (h : j < db7.size) : verify g7 db7 (db7[j]?.getD default) = true := by change j < 0 at h; omega
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e8_0 : verify g8 db8 e8_0 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem all8 : entries8.all (verify g8 db8) = true := by
 simp only [entries8,List.all_cons,List.all_nil,ok_e8_0,Bool.and_self]
theorem checked8 : ∀ j, j < db8.size → verify g8 db8 (db8[j]?.getD default) = true := checkedList entries8 all8
theorem checked9 (j) (h : j < db9.size) : verify g9 db9 (db9[j]?.getD default) = true := by change j < 0 at h; omega
theorem checked10 (j) (h : j < db10.size) : verify g10 db10 (db10[j]?.getD default) = true := by change j < 0 at h; omega
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e11_0 : verify g11 db11 e11_0 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem all11 : entries11.all (verify g11 db11) = true := by
 simp only [entries11,List.all_cons,List.all_nil,ok_e11_0,Bool.and_self]
theorem checked11 : ∀ j, j < db11.size → verify g11 db11 (db11[j]?.getD default) = true := checkedList entries11 all11
theorem checked12 (j) (h : j < db12.size) : verify g12 db12 (db12[j]?.getD default) = true := by change j < 0 at h; omega
theorem checked13 (j) (h : j < db13.size) : verify g13 db13 (db13[j]?.getD default) = true := by change j < 0 at h; omega
theorem checked14 (j) (h : j < db14.size) : verify g14 db14 (db14[j]?.getD default) = true := by change j < 0 at h; omega
theorem checked15 (j) (h : j < db15.size) : verify g15 db15 (db15[j]?.getD default) = true := by change j < 0 at h; omega
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e16_0 : verify g16 db16 e16_0 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e16_1 : verify g16 db16 e16_1 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e16_2 : verify g16 db16 e16_2 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e16_3 : verify g16 db16 e16_3 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e16_4 : verify g16 db16 e16_4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e16_5 : verify g16 db16 e16_5 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e16_6 : verify g16 db16 e16_6 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e16_7 : verify g16 db16 e16_7 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e16_8 : verify g16 db16 e16_8 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e16_9 : verify g16 db16 e16_9 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e16_10 : verify g16 db16 e16_10 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e16_11 : verify g16 db16 e16_11 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e16_12 : verify g16 db16 e16_12 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e16_13 : verify g16 db16 e16_13 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e16_14 : verify g16 db16 e16_14 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e16_15 : verify g16 db16 e16_15 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e16_16 : verify g16 db16 e16_16 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e16_17 : verify g16 db16 e16_17 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e16_18 : verify g16 db16 e16_18 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e16_19 : verify g16 db16 e16_19 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e16_20 : verify g16 db16 e16_20 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e16_21 : verify g16 db16 e16_21 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e16_22 : verify g16 db16 e16_22 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e16_23 : verify g16 db16 e16_23 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e16_24 : verify g16 db16 e16_24 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e16_25 : verify g16 db16 e16_25 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e16_26 : verify g16 db16 e16_26 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e16_27 : verify g16 db16 e16_27 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e16_28 : verify g16 db16 e16_28 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e16_29 : verify g16 db16 e16_29 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e16_30 : verify g16 db16 e16_30 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e16_31 : verify g16 db16 e16_31 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e16_32 : verify g16 db16 e16_32 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e16_33 : verify g16 db16 e16_33 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e16_34 : verify g16 db16 e16_34 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e16_35 : verify g16 db16 e16_35 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e16_36 : verify g16 db16 e16_36 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e16_37 : verify g16 db16 e16_37 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e16_38 : verify g16 db16 e16_38 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e16_39 : verify g16 db16 e16_39 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e16_40 : verify g16 db16 e16_40 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e16_41 : verify g16 db16 e16_41 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e16_42 : verify g16 db16 e16_42 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem all16 : entries16.all (verify g16 db16) = true := by
 simp only [entries16,List.all_cons,List.all_nil,ok_e16_0,ok_e16_1,ok_e16_2,ok_e16_3,ok_e16_4,ok_e16_5,ok_e16_6,ok_e16_7,ok_e16_8,ok_e16_9,ok_e16_10,ok_e16_11,ok_e16_12,ok_e16_13,ok_e16_14,ok_e16_15,ok_e16_16,ok_e16_17,ok_e16_18,ok_e16_19,ok_e16_20,ok_e16_21,ok_e16_22,ok_e16_23,ok_e16_24,ok_e16_25,ok_e16_26,ok_e16_27,ok_e16_28,ok_e16_29,ok_e16_30,ok_e16_31,ok_e16_32,ok_e16_33,ok_e16_34,ok_e16_35,ok_e16_36,ok_e16_37,ok_e16_38,ok_e16_39,ok_e16_40,ok_e16_41,ok_e16_42,Bool.and_self]
theorem checked16 : ∀ j, j < db16.size → verify g16 db16 (db16[j]?.getD default) = true := checkedList entries16 all16
theorem checked17 (j) (h : j < db17.size) : verify g17 db17 (db17[j]?.getD default) = true := by change j < 0 at h; omega
theorem checked18 (j) (h : j < db18.size) : verify g18 db18 (db18[j]?.getD default) = true := by change j < 0 at h; omega
theorem checked19 (j) (h : j < db19.size) : verify g19 db19 (db19[j]?.getD default) = true := by change j < 0 at h; omega
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_0 : verify g20 db20 e20_0 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_1 : verify g20 db20 e20_1 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_2 : verify g20 db20 e20_2 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_3 : verify g20 db20 e20_3 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_4 : verify g20 db20 e20_4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_5 : verify g20 db20 e20_5 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_6 : verify g20 db20 e20_6 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_7 : verify g20 db20 e20_7 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_8 : verify g20 db20 e20_8 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_9 : verify g20 db20 e20_9 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_10 : verify g20 db20 e20_10 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_11 : verify g20 db20 e20_11 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_12 : verify g20 db20 e20_12 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_13 : verify g20 db20 e20_13 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_14 : verify g20 db20 e20_14 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_15 : verify g20 db20 e20_15 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_16 : verify g20 db20 e20_16 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_17 : verify g20 db20 e20_17 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_18 : verify g20 db20 e20_18 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_19 : verify g20 db20 e20_19 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_20 : verify g20 db20 e20_20 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_21 : verify g20 db20 e20_21 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_22 : verify g20 db20 e20_22 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_23 : verify g20 db20 e20_23 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_24 : verify g20 db20 e20_24 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_25 : verify g20 db20 e20_25 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_26 : verify g20 db20 e20_26 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_27 : verify g20 db20 e20_27 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_28 : verify g20 db20 e20_28 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_29 : verify g20 db20 e20_29 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_30 : verify g20 db20 e20_30 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_31 : verify g20 db20 e20_31 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_32 : verify g20 db20 e20_32 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_33 : verify g20 db20 e20_33 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_34 : verify g20 db20 e20_34 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_35 : verify g20 db20 e20_35 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_36 : verify g20 db20 e20_36 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_37 : verify g20 db20 e20_37 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_38 : verify g20 db20 e20_38 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_39 : verify g20 db20 e20_39 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_40 : verify g20 db20 e20_40 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_41 : verify g20 db20 e20_41 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_42 : verify g20 db20 e20_42 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_43 : verify g20 db20 e20_43 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_44 : verify g20 db20 e20_44 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_45 : verify g20 db20 e20_45 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_46 : verify g20 db20 e20_46 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_47 : verify g20 db20 e20_47 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_48 : verify g20 db20 e20_48 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_49 : verify g20 db20 e20_49 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_50 : verify g20 db20 e20_50 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_51 : verify g20 db20 e20_51 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_52 : verify g20 db20 e20_52 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_53 : verify g20 db20 e20_53 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_54 : verify g20 db20 e20_54 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_55 : verify g20 db20 e20_55 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_56 : verify g20 db20 e20_56 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_57 : verify g20 db20 e20_57 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_58 : verify g20 db20 e20_58 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_59 : verify g20 db20 e20_59 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_60 : verify g20 db20 e20_60 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_61 : verify g20 db20 e20_61 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_62 : verify g20 db20 e20_62 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_63 : verify g20 db20 e20_63 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_64 : verify g20 db20 e20_64 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_65 : verify g20 db20 e20_65 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_66 : verify g20 db20 e20_66 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_67 : verify g20 db20 e20_67 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_68 : verify g20 db20 e20_68 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_69 : verify g20 db20 e20_69 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_70 : verify g20 db20 e20_70 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_71 : verify g20 db20 e20_71 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_72 : verify g20 db20 e20_72 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_73 : verify g20 db20 e20_73 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_74 : verify g20 db20 e20_74 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_75 : verify g20 db20 e20_75 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_76 : verify g20 db20 e20_76 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_77 : verify g20 db20 e20_77 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_78 : verify g20 db20 e20_78 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_79 : verify g20 db20 e20_79 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_80 : verify g20 db20 e20_80 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_81 : verify g20 db20 e20_81 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_82 : verify g20 db20 e20_82 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_83 : verify g20 db20 e20_83 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_84 : verify g20 db20 e20_84 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_85 : verify g20 db20 e20_85 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_86 : verify g20 db20 e20_86 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_87 : verify g20 db20 e20_87 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_88 : verify g20 db20 e20_88 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_89 : verify g20 db20 e20_89 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_90 : verify g20 db20 e20_90 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_91 : verify g20 db20 e20_91 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_92 : verify g20 db20 e20_92 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_93 : verify g20 db20 e20_93 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_94 : verify g20 db20 e20_94 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_95 : verify g20 db20 e20_95 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_96 : verify g20 db20 e20_96 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_97 : verify g20 db20 e20_97 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_98 : verify g20 db20 e20_98 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_99 : verify g20 db20 e20_99 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_100 : verify g20 db20 e20_100 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_101 : verify g20 db20 e20_101 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_102 : verify g20 db20 e20_102 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_103 : verify g20 db20 e20_103 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_104 : verify g20 db20 e20_104 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_105 : verify g20 db20 e20_105 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_106 : verify g20 db20 e20_106 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_107 : verify g20 db20 e20_107 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_108 : verify g20 db20 e20_108 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_109 : verify g20 db20 e20_109 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_110 : verify g20 db20 e20_110 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_111 : verify g20 db20 e20_111 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_112 : verify g20 db20 e20_112 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_113 : verify g20 db20 e20_113 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_114 : verify g20 db20 e20_114 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_115 : verify g20 db20 e20_115 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_116 : verify g20 db20 e20_116 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_117 : verify g20 db20 e20_117 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_118 : verify g20 db20 e20_118 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_119 : verify g20 db20 e20_119 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_120 : verify g20 db20 e20_120 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_121 : verify g20 db20 e20_121 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_122 : verify g20 db20 e20_122 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_123 : verify g20 db20 e20_123 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_124 : verify g20 db20 e20_124 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_125 : verify g20 db20 e20_125 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_126 : verify g20 db20 e20_126 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_127 : verify g20 db20 e20_127 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_128 : verify g20 db20 e20_128 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_129 : verify g20 db20 e20_129 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_130 : verify g20 db20 e20_130 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_131 : verify g20 db20 e20_131 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_132 : verify g20 db20 e20_132 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_133 : verify g20 db20 e20_133 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_134 : verify g20 db20 e20_134 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_135 : verify g20 db20 e20_135 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_136 : verify g20 db20 e20_136 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_137 : verify g20 db20 e20_137 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_138 : verify g20 db20 e20_138 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_139 : verify g20 db20 e20_139 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_140 : verify g20 db20 e20_140 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_141 : verify g20 db20 e20_141 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_142 : verify g20 db20 e20_142 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_143 : verify g20 db20 e20_143 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_144 : verify g20 db20 e20_144 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_145 : verify g20 db20 e20_145 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_146 : verify g20 db20 e20_146 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_147 : verify g20 db20 e20_147 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_148 : verify g20 db20 e20_148 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_149 : verify g20 db20 e20_149 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_150 : verify g20 db20 e20_150 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_151 : verify g20 db20 e20_151 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_152 : verify g20 db20 e20_152 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_153 : verify g20 db20 e20_153 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_154 : verify g20 db20 e20_154 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_155 : verify g20 db20 e20_155 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_156 : verify g20 db20 e20_156 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_157 : verify g20 db20 e20_157 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_158 : verify g20 db20 e20_158 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_159 : verify g20 db20 e20_159 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_160 : verify g20 db20 e20_160 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_161 : verify g20 db20 e20_161 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_162 : verify g20 db20 e20_162 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_163 : verify g20 db20 e20_163 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_164 : verify g20 db20 e20_164 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_165 : verify g20 db20 e20_165 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_166 : verify g20 db20 e20_166 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_167 : verify g20 db20 e20_167 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_168 : verify g20 db20 e20_168 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_169 : verify g20 db20 e20_169 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_170 : verify g20 db20 e20_170 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_171 : verify g20 db20 e20_171 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_172 : verify g20 db20 e20_172 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_173 : verify g20 db20 e20_173 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_174 : verify g20 db20 e20_174 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_175 : verify g20 db20 e20_175 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_176 : verify g20 db20 e20_176 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_177 : verify g20 db20 e20_177 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_178 : verify g20 db20 e20_178 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_179 : verify g20 db20 e20_179 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_180 : verify g20 db20 e20_180 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_181 : verify g20 db20 e20_181 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_182 : verify g20 db20 e20_182 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_183 : verify g20 db20 e20_183 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_184 : verify g20 db20 e20_184 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_185 : verify g20 db20 e20_185 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_186 : verify g20 db20 e20_186 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_187 : verify g20 db20 e20_187 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_188 : verify g20 db20 e20_188 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_189 : verify g20 db20 e20_189 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_190 : verify g20 db20 e20_190 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_191 : verify g20 db20 e20_191 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_192 : verify g20 db20 e20_192 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e20_193 : verify g20 db20 e20_193 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem all20 : entries20.all (verify g20 db20) = true := by
 simp only [entries20,List.all_cons,List.all_nil,ok_e20_0,ok_e20_1,ok_e20_2,ok_e20_3,ok_e20_4,ok_e20_5,ok_e20_6,ok_e20_7,ok_e20_8,ok_e20_9,ok_e20_10,ok_e20_11,ok_e20_12,ok_e20_13,ok_e20_14,ok_e20_15,ok_e20_16,ok_e20_17,ok_e20_18,ok_e20_19,ok_e20_20,ok_e20_21,ok_e20_22,ok_e20_23,ok_e20_24,ok_e20_25,ok_e20_26,ok_e20_27,ok_e20_28,ok_e20_29,ok_e20_30,ok_e20_31,ok_e20_32,ok_e20_33,ok_e20_34,ok_e20_35,ok_e20_36,ok_e20_37,ok_e20_38,ok_e20_39,ok_e20_40,ok_e20_41,ok_e20_42,ok_e20_43,ok_e20_44,ok_e20_45,ok_e20_46,ok_e20_47,ok_e20_48,ok_e20_49,ok_e20_50,ok_e20_51,ok_e20_52,ok_e20_53,ok_e20_54,ok_e20_55,ok_e20_56,ok_e20_57,ok_e20_58,ok_e20_59,ok_e20_60,ok_e20_61,ok_e20_62,ok_e20_63,ok_e20_64,ok_e20_65,ok_e20_66,ok_e20_67,ok_e20_68,ok_e20_69,ok_e20_70,ok_e20_71,ok_e20_72,ok_e20_73,ok_e20_74,ok_e20_75,ok_e20_76,ok_e20_77,ok_e20_78,ok_e20_79,ok_e20_80,ok_e20_81,ok_e20_82,ok_e20_83,ok_e20_84,ok_e20_85,ok_e20_86,ok_e20_87,ok_e20_88,ok_e20_89,ok_e20_90,ok_e20_91,ok_e20_92,ok_e20_93,ok_e20_94,ok_e20_95,ok_e20_96,ok_e20_97,ok_e20_98,ok_e20_99,ok_e20_100,ok_e20_101,ok_e20_102,ok_e20_103,ok_e20_104,ok_e20_105,ok_e20_106,ok_e20_107,ok_e20_108,ok_e20_109,ok_e20_110,ok_e20_111,ok_e20_112,ok_e20_113,ok_e20_114,ok_e20_115,ok_e20_116,ok_e20_117,ok_e20_118,ok_e20_119,ok_e20_120,ok_e20_121,ok_e20_122,ok_e20_123,ok_e20_124,ok_e20_125,ok_e20_126,ok_e20_127,ok_e20_128,ok_e20_129,ok_e20_130,ok_e20_131,ok_e20_132,ok_e20_133,ok_e20_134,ok_e20_135,ok_e20_136,ok_e20_137,ok_e20_138,ok_e20_139,ok_e20_140,ok_e20_141,ok_e20_142,ok_e20_143,ok_e20_144,ok_e20_145,ok_e20_146,ok_e20_147,ok_e20_148,ok_e20_149,ok_e20_150,ok_e20_151,ok_e20_152,ok_e20_153,ok_e20_154,ok_e20_155,ok_e20_156,ok_e20_157,ok_e20_158,ok_e20_159,ok_e20_160,ok_e20_161,ok_e20_162,ok_e20_163,ok_e20_164,ok_e20_165,ok_e20_166,ok_e20_167,ok_e20_168,ok_e20_169,ok_e20_170,ok_e20_171,ok_e20_172,ok_e20_173,ok_e20_174,ok_e20_175,ok_e20_176,ok_e20_177,ok_e20_178,ok_e20_179,ok_e20_180,ok_e20_181,ok_e20_182,ok_e20_183,ok_e20_184,ok_e20_185,ok_e20_186,ok_e20_187,ok_e20_188,ok_e20_189,ok_e20_190,ok_e20_191,ok_e20_192,ok_e20_193,Bool.and_self]
theorem checked20 : ∀ j, j < db20.size → verify g20 db20 (db20[j]?.getD default) = true := checkedList entries20 all20
theorem checked21 (j) (h : j < db21.size) : verify g21 db21 (db21[j]?.getD default) = true := by change j < 0 at h; omega
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e22_0 : verify g22 db22 e22_0 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e22_1 : verify g22 db22 e22_1 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e22_2 : verify g22 db22 e22_2 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e22_3 : verify g22 db22 e22_3 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e22_4 : verify g22 db22 e22_4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e22_5 : verify g22 db22 e22_5 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e22_6 : verify g22 db22 e22_6 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e22_7 : verify g22 db22 e22_7 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e22_8 : verify g22 db22 e22_8 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem all22 : entries22.all (verify g22 db22) = true := by
 simp only [entries22,List.all_cons,List.all_nil,ok_e22_0,ok_e22_1,ok_e22_2,ok_e22_3,ok_e22_4,ok_e22_5,ok_e22_6,ok_e22_7,ok_e22_8,Bool.and_self]
theorem checked22 : ∀ j, j < db22.size → verify g22 db22 (db22[j]?.getD default) = true := checkedList entries22 all22
theorem checked23 (j) (h : j < db23.size) : verify g23 db23 (db23[j]?.getD default) = true := by change j < 0 at h; omega
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e24_0 : verify g24 db24 e24_0 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e24_1 : verify g24 db24 e24_1 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e24_2 : verify g24 db24 e24_2 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem all24 : entries24.all (verify g24 db24) = true := by
 simp only [entries24,List.all_cons,List.all_nil,ok_e24_0,ok_e24_1,ok_e24_2,Bool.and_self]
theorem checked24 : ∀ j, j < db24.size → verify g24 db24 (db24[j]?.getD default) = true := checkedList entries24 all24
theorem checked25 (j) (h : j < db25.size) : verify g25 db25 (db25[j]?.getD default) = true := by change j < 0 at h; omega
theorem checked26 (j) (h : j < db26.size) : verify g26 db26 (db26[j]?.getD default) = true := by change j < 0 at h; omega
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e27_0 : verify g27 db27 e27_0 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e27_1 : verify g27 db27 e27_1 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e27_2 : verify g27 db27 e27_2 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e27_3 : verify g27 db27 e27_3 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e27_4 : verify g27 db27 e27_4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e27_5 : verify g27 db27 e27_5 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e27_6 : verify g27 db27 e27_6 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e27_7 : verify g27 db27 e27_7 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e27_8 : verify g27 db27 e27_8 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e27_9 : verify g27 db27 e27_9 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e27_10 : verify g27 db27 e27_10 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e27_11 : verify g27 db27 e27_11 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e27_12 : verify g27 db27 e27_12 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e27_13 : verify g27 db27 e27_13 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e27_14 : verify g27 db27 e27_14 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e27_15 : verify g27 db27 e27_15 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e27_16 : verify g27 db27 e27_16 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e27_17 : verify g27 db27 e27_17 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e27_18 : verify g27 db27 e27_18 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e27_19 : verify g27 db27 e27_19 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e27_20 : verify g27 db27 e27_20 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e27_21 : verify g27 db27 e27_21 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e27_22 : verify g27 db27 e27_22 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e27_23 : verify g27 db27 e27_23 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e27_24 : verify g27 db27 e27_24 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e27_25 : verify g27 db27 e27_25 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e27_26 : verify g27 db27 e27_26 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e27_27 : verify g27 db27 e27_27 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e27_28 : verify g27 db27 e27_28 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e27_29 : verify g27 db27 e27_29 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e27_30 : verify g27 db27 e27_30 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e27_31 : verify g27 db27 e27_31 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e27_32 : verify g27 db27 e27_32 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e27_33 : verify g27 db27 e27_33 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e27_34 : verify g27 db27 e27_34 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e27_35 : verify g27 db27 e27_35 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e27_36 : verify g27 db27 e27_36 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e27_37 : verify g27 db27 e27_37 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e27_38 : verify g27 db27 e27_38 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e27_39 : verify g27 db27 e27_39 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e27_40 : verify g27 db27 e27_40 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e27_41 : verify g27 db27 e27_41 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e27_42 : verify g27 db27 e27_42 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e27_43 : verify g27 db27 e27_43 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e27_44 : verify g27 db27 e27_44 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e27_45 : verify g27 db27 e27_45 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e27_46 : verify g27 db27 e27_46 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e27_47 : verify g27 db27 e27_47 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e27_48 : verify g27 db27 e27_48 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e27_49 : verify g27 db27 e27_49 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e27_50 : verify g27 db27 e27_50 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e27_51 : verify g27 db27 e27_51 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e27_52 : verify g27 db27 e27_52 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e27_53 : verify g27 db27 e27_53 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e27_54 : verify g27 db27 e27_54 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e27_55 : verify g27 db27 e27_55 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e27_56 : verify g27 db27 e27_56 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e27_57 : verify g27 db27 e27_57 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e27_58 : verify g27 db27 e27_58 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e27_59 : verify g27 db27 e27_59 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e27_60 : verify g27 db27 e27_60 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e27_61 : verify g27 db27 e27_61 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e27_62 : verify g27 db27 e27_62 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok_e27_63 : verify g27 db27 e27_63 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem all27 : entries27.all (verify g27 db27) = true := by
 simp only [entries27,List.all_cons,List.all_nil,ok_e27_0,ok_e27_1,ok_e27_2,ok_e27_3,ok_e27_4,ok_e27_5,ok_e27_6,ok_e27_7,ok_e27_8,ok_e27_9,ok_e27_10,ok_e27_11,ok_e27_12,ok_e27_13,ok_e27_14,ok_e27_15,ok_e27_16,ok_e27_17,ok_e27_18,ok_e27_19,ok_e27_20,ok_e27_21,ok_e27_22,ok_e27_23,ok_e27_24,ok_e27_25,ok_e27_26,ok_e27_27,ok_e27_28,ok_e27_29,ok_e27_30,ok_e27_31,ok_e27_32,ok_e27_33,ok_e27_34,ok_e27_35,ok_e27_36,ok_e27_37,ok_e27_38,ok_e27_39,ok_e27_40,ok_e27_41,ok_e27_42,ok_e27_43,ok_e27_44,ok_e27_45,ok_e27_46,ok_e27_47,ok_e27_48,ok_e27_49,ok_e27_50,ok_e27_51,ok_e27_52,ok_e27_53,ok_e27_54,ok_e27_55,ok_e27_56,ok_e27_57,ok_e27_58,ok_e27_59,ok_e27_60,ok_e27_61,ok_e27_62,ok_e27_63,Bool.and_self]
theorem checked27 : ∀ j, j < db27.size → verify g27 db27 (db27[j]?.getD default) = true := checkedList entries27 all27
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem allChecked : AllChecks := by
 intro i hi
 have bound : i < 28 := List.mem_range.mp hi
 interval_cases i
 · exact checked0
 · exact checked1
 · exact checked2
 · exact checked3
 · exact checked4
 · exact checked5
 · exact checked6
 · exact checked7
 · exact checked8
 · exact checked9
 · exact checked10
 · exact checked11
 · exact checked12
 · exact checked13
 · exact checked14
 · exact checked15
 · exact checked16
 · exact checked17
 · exact checked18
 · exact checked19
 · exact checked20
 · exact checked21
 · exact checked22
 · exact checked23
 · exact checked24
 · exact checked25
 · exact checked26
 · exact checked27

set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem assembledLower (all : AllChecks) : Lower true (rootsOf 63) (targetOf 18368772107823279336) 10 := by
 have good0 : Good g0 := by
  refine ⟨?_,?_,checkedPerms (by decide +kernel)⟩
  · decide +kernel
  · intro s hs
    change s ∈ ([] : List (Sig × Nat)) at hs
    simp at hs
 have imp0 : Impossible true (targetOf 16782920098433788136) 3 (rootsOf 7).toFinset := by
  have h := forestSound good0 db0 (all 0 (by decide +kernel)) 0 (by decide +kernel)
  change Impossible true (targetOf 16782920098433788136) 3 (stateOf g0 (db0[0]?.getD default)).toFinset at h
  have home : stateOf g0 (db0[0]?.getD default) = rootsOf 7 := by decide +kernel
  simpa only [home] using h
 have low0 : Lower true (rootsOf 7) (targetOf 16782920098433788136) 4 :=
  lowerFrom [(inputs.getD 0 zero,2,3),(inputs.getD 1 zero,1,3),(inputs.getD 2 zero,1,5)] (by unfold proper; decide +kernel) (by decide +kernel) (by decide +kernel) imp0
 have good1 : Good g1 := by
  refine ⟨?_,?_,checkedPerms (by decide +kernel)⟩
  · decide +kernel
  · intro s hs
    change s ∈ ([] : List (Sig × Nat)) at hs
    simp at hs
 have imp1 : Impossible true (targetOf 17188250249744412296) 3 (rootsOf 11).toFinset := by
  have h := forestSound good1 db1 (all 1 (by decide +kernel)) 0 (by decide +kernel)
  change Impossible true (targetOf 17188250249744412296) 3 (stateOf g1 (db1[0]?.getD default)).toFinset at h
  have home : stateOf g1 (db1[0]?.getD default) = rootsOf 11 := by decide +kernel
  simpa only [home] using h
 have low1 : Lower true (rootsOf 11) (targetOf 17188250249744412296) 4 :=
  lowerFrom [(inputs.getD 0 zero,2,3),(inputs.getD 1 zero,1,3),(inputs.getD 3 zero,1,9)] (by unfold proper; decide +kernel) (by decide +kernel) (by decide +kernel) imp1
 have good2 : Good g2 := by
  refine ⟨?_,?_,checkedPerms (by decide +kernel)⟩
  · decide +kernel
  · intro s hs
    change s ∈ ([] : List (Sig × Nat)) at hs
    simp at hs
 have imp2 : Impossible true (targetOf 18059710075062254240) 3 (rootsOf 13).toFinset := by
  have h := forestSound good2 db2 (all 2 (by decide +kernel)) 0 (by decide +kernel)
  change Impossible true (targetOf 18059710075062254240) 3 (stateOf g2 (db2[0]?.getD default)).toFinset at h
  have home : stateOf g2 (db2[0]?.getD default) = rootsOf 13 := by decide +kernel
  simpa only [home] using h
 have low2 : Lower true (rootsOf 13) (targetOf 18059710075062254240) 4 :=
  lowerFrom [(inputs.getD 0 zero,4,5),(inputs.getD 2 zero,1,5),(inputs.getD 3 zero,1,9)] (by unfold proper; decide +kernel) (by decide +kernel) (by decide +kernel) imp2
 have good3 : Good g3 := by
  refine ⟨?_,?_,checkedPerms (by decide +kernel)⟩
  · decide +kernel
  · intro s hs
    change s ∈ ([] : List (Sig × Nat)) at hs
    simp at hs
 have imp3 : Impossible true (targetOf 18084943866925588640) 3 (rootsOf 21).toFinset := by
  have h := forestSound good3 db3 (all 3 (by decide +kernel)) 0 (by decide +kernel)
  change Impossible true (targetOf 18084943866925588640) 3 (stateOf g3 (db3[0]?.getD default)).toFinset at h
  have home : stateOf g3 (db3[0]?.getD default) = rootsOf 21 := by decide +kernel
  simpa only [home] using h
 have low3 : Lower true (rootsOf 21) (targetOf 18084943866925588640) 4 :=
  lowerFrom [(inputs.getD 0 zero,4,5),(inputs.getD 2 zero,1,5),(inputs.getD 4 zero,1,17)] (by unfold proper; decide +kernel) (by decide +kernel) (by decide +kernel) imp3
 have good4 : Good g4 := by
  refine ⟨?_,?_,checkedPerms (by decide +kernel)⟩
  · decide +kernel
  · intro s hs
    change s ∈ ([] : List (Sig × Nat)) at hs
    simp at hs
 have imp4 : Impossible true (targetOf 18212834798890712256) 3 (rootsOf 14).toFinset := by
  have h := forestSound good4 db4 (all 4 (by decide +kernel)) 0 (by decide +kernel)
  change Impossible true (targetOf 18212834798890712256) 3 (stateOf g4 (db4[0]?.getD default)).toFinset at h
  have home : stateOf g4 (db4[0]?.getD default) = rootsOf 14 := by decide +kernel
  simpa only [home] using h
 have low4 : Lower true (rootsOf 14) (targetOf 18212834798890712256) 4 :=
  lowerFrom [(inputs.getD 1 zero,4,6),(inputs.getD 2 zero,2,6),(inputs.getD 3 zero,2,10)] (by unfold proper; decide +kernel) (by decide +kernel) (by decide +kernel) imp4
 have good5 : Good g5 := by
  refine ⟨?_,?_,checkedPerms (by decide +kernel)⟩
  · decide +kernel
  · intro s hs
    change s ∈ [(domainOf 23 16 0,4)] at hs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
    rcases hs with rfl
    · exact slice_correct (ms:=fixRows 248 0) (base:=rootsOf 7) (G:=targetOf 16782920098433788136)
       (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) low0
 have imp5 : Impossible true (targetOf 16927598236496750824) 4 (rootsOf 23).toFinset :=
  verifiedCut good5 (cap:=4) (cs:=[]) (ch:=rootsOf 23) (code:=1) (by decide +kernel) (by decide +kernel)
 have low5 : Lower true (rootsOf 23) (targetOf 16927598236496750824) 5 :=
  lowerFrom [(inputs.getD 0 zero,2,3),(inputs.getD 1 zero,1,3),(inputs.getD 2 zero,1,5),(inputs.getD 4 zero,1,17)] (by unfold proper; decide +kernel) (by decide +kernel) (by decide +kernel) imp5
 have good6 : Good g6 := by
  refine ⟨?_,?_,checkedPerms (by decide +kernel)⟩
  · decide +kernel
  · intro s hs
    change s ∈ [(domainOf 39 32 0,4)] at hs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
    rcases hs with rfl
    · exact slice_correct (ms:=fixRows 248 0) (base:=rootsOf 7) (G:=targetOf 16782920098433788136)
       (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) low0
 have imp6 : Impossible true (targetOf 16927600444076255464) 4 (rootsOf 39).toFinset :=
  verifiedCut good6 (cap:=4) (cs:=[]) (ch:=rootsOf 39) (code:=1) (by decide +kernel) (by decide +kernel)
 have low6 : Lower true (rootsOf 39) (targetOf 16927600444076255464) 5 :=
  lowerFrom [(inputs.getD 0 zero,2,3),(inputs.getD 1 zero,1,3),(inputs.getD 2 zero,1,5),(inputs.getD 5 zero,1,33)] (by unfold proper; decide +kernel) (by decide +kernel) (by decide +kernel) imp6
 have good7 : Good g7 := by
  refine ⟨?_,?_,checkedPerms (by decide +kernel)⟩
  · decide +kernel
  · intro s hs
    change s ∈ [(domainOf 15 8 0,4)] at hs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
    rcases hs with rfl
    · exact slice_correct (ms:=fixRows 248 0) (base:=rootsOf 7) (G:=targetOf 16782920098433788136)
       (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) low0
 have imp7 : Impossible true (targetOf 17071154872699120872) 4 (rootsOf 15).toFinset :=
  verifiedCut good7 (cap:=4) (cs:=[]) (ch:=rootsOf 15) (code:=1) (by decide +kernel) (by decide +kernel)
 have low7 : Lower true (rootsOf 15) (targetOf 17071154872699120872) 5 :=
  lowerFrom [(inputs.getD 0 zero,2,3),(inputs.getD 1 zero,1,3),(inputs.getD 2 zero,1,5),(inputs.getD 3 zero,2,10)] (by unfold proper; decide +kernel) (by decide +kernel) (by decide +kernel) imp7
 have good8 : Good g8 := by
  refine ⟨?_,?_,checkedPerms (by decide +kernel)⟩
  · decide +kernel
  · intro s hs
    change s ∈ ([] : List (Sig × Nat)) at hs
    simp at hs
 have imp8 : Impossible true (targetOf 17197783015559449736) 3 (rootsOf 27).toFinset := by
  have h := forestSound good8 db8 (all 8 (by decide +kernel)) 0 (by decide +kernel)
  change Impossible true (targetOf 17197783015559449736) 3 (stateOf g8 (db8[0]?.getD default)).toFinset at h
  have home : stateOf g8 (db8[0]?.getD default) = rootsOf 27 := by decide +kernel
  simpa only [home] using h
 have low8 : Lower true (rootsOf 27) (targetOf 17197783015559449736) 4 :=
  lowerFrom [(inputs.getD 0 zero,2,3),(inputs.getD 1 zero,1,3),(inputs.getD 3 zero,2,10),(inputs.getD 4 zero,1,17)] (by unfold proper; decide +kernel) (by decide +kernel) (by decide +kernel) imp8
 have good9 : Good g9 := by
  refine ⟨?_,?_,checkedPerms (by decide +kernel)⟩
  · decide +kernel
  · intro s hs
    change s ∈ [(domainOf 43 32 0,4)] at hs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
    rcases hs with rfl
    · exact slice_correct (ms:=fixRows 244 0) (base:=rootsOf 11) (G:=targetOf 17188250249744412296)
       (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) low1
 have imp9 : Impossible true (targetOf 17197820544981462664) 4 (rootsOf 43).toFinset :=
  verifiedCut good9 (cap:=4) (cs:=[]) (ch:=rootsOf 43) (code:=1) (by decide +kernel) (by decide +kernel)
 have low9 : Lower true (rootsOf 43) (targetOf 17197820544981462664) 5 :=
  lowerFrom [(inputs.getD 0 zero,2,3),(inputs.getD 1 zero,1,3),(inputs.getD 3 zero,1,9),(inputs.getD 5 zero,1,33)] (by unfold proper; decide +kernel) (by decide +kernel) (by decide +kernel) imp9
 have good10 : Good g10 := by
  refine ⟨?_,?_,checkedPerms (by decide +kernel)⟩
  · decide +kernel
  · intro s hs
    change s ∈ [(domainOf 29 0 8,4)] at hs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
    rcases hs with rfl
    · exact slice_correct (ms:=fixRows 226 8) (base:=rootsOf 21) (G:=targetOf 18084943866925588640)
       (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) low3
 have imp10 : Impossible true (targetOf 18059611119015731360) 4 (rootsOf 29).toFinset :=
  verifiedCut good10 (cap:=4) (cs:=[]) (ch:=rootsOf 29) (code:=1) (by decide +kernel) (by decide +kernel)
 have low10 : Lower true (rootsOf 29) (targetOf 18059611119015731360) 5 :=
  lowerFrom [(inputs.getD 0 zero,4,5),(inputs.getD 2 zero,1,5),(inputs.getD 3 zero,17,25),(inputs.getD 4 zero,9,25)] (by unfold proper; decide +kernel) (by decide +kernel) (by decide +kernel) imp10
 have good11 : Good g11 := by
  refine ⟨?_,?_,checkedPerms (by decide +kernel)⟩
  · decide +kernel
  · intro s hs
    change s ∈ ([] : List (Sig × Nat)) at hs
    simp at hs
 have imp11 : Impossible true (targetOf 18062513829713735840) 3 (rootsOf 29).toFinset := by
  have h := forestSound good11 db11 (all 11 (by decide +kernel)) 0 (by decide +kernel)
  change Impossible true (targetOf 18062513829713735840) 3 (stateOf g11 (db11[0]?.getD default)).toFinset at h
  have home : stateOf g11 (db11[0]?.getD default) = rootsOf 29 := by decide +kernel
  simpa only [home] using h
 have low11 : Lower true (rootsOf 29) (targetOf 18062513829713735840) 4 :=
  lowerFrom [(inputs.getD 0 zero,4,5),(inputs.getD 2 zero,1,5),(inputs.getD 3 zero,4,12),(inputs.getD 4 zero,1,17)] (by unfold proper; decide +kernel) (by decide +kernel) (by decide +kernel) imp11
 have good12 : Good g12 := by
  refine ⟨?_,?_,checkedPerms (by decide +kernel)⟩
  · decide +kernel
  · intro s hs
    change s ∈ [(domainOf 45 32 0,4)] at hs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
    rcases hs with rfl
    · exact slice_correct (ms:=fixRows 242 0) (base:=rootsOf 13) (G:=targetOf 18059710075062254240)
       (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) low2
 have imp12 : Impossible true (targetOf 18062524867779033760) 4 (rootsOf 45).toFinset :=
  verifiedCut good12 (cap:=4) (cs:=[]) (ch:=rootsOf 45) (code:=1) (by decide +kernel) (by decide +kernel)
 have low12 : Lower true (rootsOf 45) (targetOf 18062524867779033760) 5 :=
  lowerFrom [(inputs.getD 0 zero,4,5),(inputs.getD 2 zero,1,5),(inputs.getD 3 zero,1,9),(inputs.getD 5 zero,1,33)] (by unfold proper; decide +kernel) (by decide +kernel) (by decide +kernel) imp12
 have good13 : Good g13 := by
  refine ⟨?_,?_,checkedPerms (by decide +kernel)⟩
  · decide +kernel
  · intro s hs
    change s ∈ [(domainOf 53 32 0,4)] at hs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
    rcases hs with rfl
    · exact slice_correct (ms:=fixRows 234 0) (base:=rootsOf 21) (G:=targetOf 18084943866925588640)
       (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) low3
 have imp13 : Impossible true (targetOf 18085032171453194400) 4 (rootsOf 53).toFinset :=
  verifiedCut good13 (cap:=4) (cs:=[]) (ch:=rootsOf 53) (code:=1) (by decide +kernel) (by decide +kernel)
 have low13 : Lower true (rootsOf 53) (targetOf 18085032171453194400) 5 :=
  lowerFrom [(inputs.getD 0 zero,4,5),(inputs.getD 2 zero,1,5),(inputs.getD 4 zero,1,17),(inputs.getD 5 zero,4,36)] (by unfold proper; decide +kernel) (by decide +kernel) (by decide +kernel) imp13
 have good14 : Good g14 := by
  refine ⟨?_,?_,checkedPerms (by decide +kernel)⟩
  · decide +kernel
  · intro s hs
    change s ∈ [(domainOf 46 0 32,4)] at hs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
    rcases hs with rfl
    · exact slice_correct (ms:=fixRows 209 32) (base:=rootsOf 14) (G:=targetOf 18212834798890712256)
       (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) low4
 have imp14 : Impossible true (targetOf 18212834798085393600) 4 (rootsOf 46).toFinset :=
  verifiedCut good14 (cap:=4) (cs:=[]) (ch:=rootsOf 46) (code:=1) (by decide +kernel) (by decide +kernel)
 have low14 : Lower true (rootsOf 46) (targetOf 18212834798085393600) 5 :=
  lowerFrom [(inputs.getD 1 zero,4,6),(inputs.getD 2 zero,2,6),(inputs.getD 3 zero,2,10),(inputs.getD 5 zero,12,44)] (by unfold proper; decide +kernel) (by decide +kernel) (by decide +kernel) imp14
 have good15 : Good g15 := by
  refine ⟨?_,?_,checkedPerms (by decide +kernel)⟩
  · decide +kernel
  · intro s hs
    change s ∈ [(domainOf 15 1 0,4)] at hs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
    rcases hs with rfl
    · exact slice_correct (ms:=fixRows 241 0) (base:=rootsOf 14) (G:=targetOf 18212834798890712256)
       (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) low4
 have imp15 : Impossible true (targetOf 18224093969760451816) 4 (rootsOf 15).toFinset :=
  verifiedCut good15 (cap:=4) (cs:=[]) (ch:=rootsOf 15) (code:=1) (by decide +kernel) (by decide +kernel)
 have low15 : Lower true (rootsOf 15) (targetOf 18224093969760451816) 5 :=
  lowerFrom [(inputs.getD 0 zero,2,3),(inputs.getD 1 zero,1,3),(inputs.getD 2 zero,1,5),(inputs.getD 3 zero,2,10)] (by unfold proper; decide +kernel) (by decide +kernel) (by decide +kernel) imp15
 have good16 : Good g16 := by
  refine ⟨?_,?_,checkedPerms (by decide +kernel)⟩
  · decide +kernel
  · intro s hs
    change s ∈ [(domainOf 15 4 0,4),(domainOf 15 8 0,4),(domainOf 15 1 0,4),(domainOf 15 2 0,4)] at hs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl
    · exact slice_correct (ms:=fixRows 244 0) (base:=rootsOf 11) (G:=targetOf 17188250249744412296)
       (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) low1
    · exact slice_correct (ms:=fixRows 248 0) (base:=rootsOf 7) (G:=targetOf 16782920098433788136)
       (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) low0
    · exact slice_correct (ms:=fixRows 241 0) (base:=rootsOf 14) (G:=targetOf 18212834798890712256)
       (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) low4
    · exact slice_correct (ms:=fixRows 242 0) (base:=rootsOf 13) (G:=targetOf 18059710075062254240)
       (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) low2
 have imp16 : Impossible true (targetOf 18368211356893118184) 6 (rootsOf 15).toFinset := by
  have h := forestSound good16 db16 (all 16 (by decide +kernel)) 42 (by decide +kernel)
  change Impossible true (targetOf 18368211356893118184) 6 (stateOf g16 (db16[42]?.getD default)).toFinset at h
  have home : stateOf g16 (db16[42]?.getD default) = rootsOf 15 := by decide +kernel
  simpa only [home] using h
 have low16 : Lower true (rootsOf 15) (targetOf 18368211356893118184) 7 :=
  lowerFrom [(inputs.getD 0 zero,2,3),(inputs.getD 1 zero,1,3),(inputs.getD 2 zero,1,5),(inputs.getD 3 zero,1,9)] (by unfold proper; decide +kernel) (by decide +kernel) (by decide +kernel) imp16
 have good17 : Good g17 := by
  refine ⟨?_,?_,checkedPerms (by decide +kernel)⟩
  · decide +kernel
  · intro s hs
    change s ∈ [(domainOf 15 1 0,4)] at hs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
    rcases hs with rfl
    · exact slice_correct (ms:=fixRows 241 0) (base:=rootsOf 14) (G:=targetOf 18212834798890712256)
       (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) low4
 have imp17 : Impossible true (targetOf 18368774315436605162) 4 (rootsOf 15).toFinset :=
  verifiedCut good17 (cap:=4) (cs:=[]) (ch:=rootsOf 15) (code:=1) (by decide +kernel) (by decide +kernel)
 have low17 : Lower true (rootsOf 15) (targetOf 18368774315436605162) 5 :=
  lowerFrom [(inputs.getD 0 zero,0,1),(inputs.getD 1 zero,4,6),(inputs.getD 2 zero,2,6),(inputs.getD 3 zero,2,10)] (by unfold proper; decide +kernel) (by decide +kernel) (by decide +kernel) imp17
 have good18 : Good g18 := by
  refine ⟨?_,?_,checkedPerms (by decide +kernel)⟩
  · decide +kernel
  · intro s hs
    change s ∈ [(domainOf 55 0 16,5)] at hs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
    rcases hs with rfl
    · exact slice_correct (ms:=fixRows 200 16) (base:=rootsOf 39) (G:=targetOf 16927600444076255464)
       (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) low6
 have imp18 : Impossible true (targetOf 16927598236463065320) 5 (rootsOf 55).toFinset :=
  verifiedCut good18 (cap:=5) (cs:=[]) (ch:=rootsOf 55) (code:=1) (by decide +kernel) (by decide +kernel)
 have low18 : Lower true (rootsOf 55) (targetOf 16927598236463065320) 6 :=
  lowerFrom [(inputs.getD 0 zero,2,3),(inputs.getD 1 zero,1,3),(inputs.getD 2 zero,1,5),(inputs.getD 4 zero,33,49),(inputs.getD 5 zero,17,49)] (by unfold proper; decide +kernel) (by decide +kernel) (by decide +kernel) imp18
 have good19 : Good g19 := by
  refine ⟨?_,?_,checkedPerms (by decide +kernel)⟩
  · decide +kernel
  · intro s hs
    change s ∈ [(domainOf 59 0 16,5)] at hs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
    rcases hs with rfl
    · exact slice_correct (ms:=fixRows 196 16) (base:=rootsOf 43) (G:=targetOf 17197820544981462664)
       (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) low9
 have imp19 : Impossible true (targetOf 17197783015557221512) 5 (rootsOf 59).toFinset :=
  verifiedCut good19 (cap:=5) (cs:=[]) (ch:=rootsOf 59) (code:=1) (by decide +kernel) (by decide +kernel)
 have low19 : Lower true (rootsOf 59) (targetOf 17197783015557221512) 6 :=
  lowerFrom [(inputs.getD 0 zero,2,3),(inputs.getD 1 zero,1,3),(inputs.getD 3 zero,2,10),(inputs.getD 4 zero,9,25),(inputs.getD 5 zero,17,49)] (by unfold proper; decide +kernel) (by decide +kernel) (by decide +kernel) imp19
 have good20 : Good g20 := by
  refine ⟨?_,?_,checkedPerms (by decide +kernel)⟩
  · decide +kernel
  · intro s hs
    change s ∈ [(domainOf 61 0 16,5),(domainOf 61 0 8,5),(domainOf 61 32 0,5),(domainOf 61 0 32,4),(domainOf 61 32 16,4),(domainOf 61 32 8,4)] at hs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
    · exact slice_correct (ms:=fixRows 194 16) (base:=rootsOf 45) (G:=targetOf 18062524867779033760)
       (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) low12
    · exact slice_correct (ms:=fixRows 194 8) (base:=rootsOf 53) (G:=targetOf 18085032171453194400)
       (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) low13
    · exact slice_correct (ms:=fixRows 226 0) (base:=rootsOf 29) (G:=targetOf 18059611119015731360)
       (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) low10
    · exact slice_correct (ms:=fixRows 194 32) (base:=rootsOf 29) (G:=targetOf 18062513829713735840)
       (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) low11
    · exact slice_correct (ms:=fixRows 226 16) (base:=rootsOf 13) (G:=targetOf 18059710075062254240)
       (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) low2
    · exact slice_correct (ms:=fixRows 226 8) (base:=rootsOf 21) (G:=targetOf 18084943866925588640)
       (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) low3
 have imp20 : Impossible true (targetOf 18062513829713060000) 7 (rootsOf 61).toFinset := by
  have h := forestSound good20 db20 (all 20 (by decide +kernel)) 193 (by decide +kernel)
  change Impossible true (targetOf 18062513829713060000) 7 (stateOf g20 (db20[193]?.getD default)).toFinset at h
  have home : stateOf g20 (db20[193]?.getD default) = rootsOf 61 := by decide +kernel
  simpa only [home] using h
 have low20 : Lower true (rootsOf 61) (targetOf 18062513829713060000) 8 :=
  lowerFrom [(inputs.getD 0 zero,4,5),(inputs.getD 2 zero,1,5),(inputs.getD 3 zero,17,25),(inputs.getD 4 zero,9,25),(inputs.getD 5 zero,12,44)] (by unfold proper; decide +kernel) (by decide +kernel) (by decide +kernel) imp20
 have good21 : Good g21 := by
  refine ⟨?_,?_,checkedPerms (by decide +kernel)⟩
  · decide +kernel
  · intro s hs
    change s ∈ [(domainOf 62 16 0,5)] at hs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
    rcases hs with rfl
    · exact slice_correct (ms:=fixRows 209 0) (base:=rootsOf 46) (G:=targetOf 18212834798085393600)
       (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) low14
 have imp21 : Impossible true (targetOf 18212834798890699968) 5 (rootsOf 62).toFinset :=
  verifiedCut good21 (cap:=5) (cs:=[]) (ch:=rootsOf 62) (code:=1) (by decide +kernel) (by decide +kernel)
 have low21 : Lower true (rootsOf 62) (targetOf 18212834798890699968) 6 :=
  lowerFrom [(inputs.getD 1 zero,4,6),(inputs.getD 2 zero,2,6),(inputs.getD 3 zero,2,10),(inputs.getD 4 zero,12,28),(inputs.getD 5 zero,12,44)] (by unfold proper; decide +kernel) (by decide +kernel) (by decide +kernel) imp21
 have good22 : Good g22 := by
  refine ⟨?_,?_,checkedPerms (by decide +kernel)⟩
  · decide +kernel
  · intro s hs
    change s ∈ [(domainOf 47 0 32,5),(domainOf 47 1 0,5),(domainOf 47 32 0,5),(domainOf 47 8 0,4),(domainOf 47 40 0,4)] at hs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl
    · exact slice_correct (ms:=fixRows 208 32) (base:=rootsOf 15) (G:=targetOf 18224093969760451816)
       (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) low15
    · exact slice_correct (ms:=fixRows 209 0) (base:=rootsOf 46) (G:=targetOf 18212834798085393600)
       (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) low14
    · exact slice_correct (ms:=fixRows 240 0) (base:=rootsOf 15) (G:=targetOf 17071154872699120872)
       (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) low7
    · exact slice_correct (ms:=fixRows 248 0) (base:=rootsOf 7) (G:=targetOf 16782920098433788136)
       (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) low0
    · exact slice_correct (ms:=fixRows 248 0) (base:=rootsOf 7) (G:=targetOf 16782920098433788136)
       (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) low0
 have imp22 : Impossible true (targetOf 18224093969492012264) 6 (rootsOf 47).toFinset := by
  have h := forestSound good22 db22 (all 22 (by decide +kernel)) 8 (by decide +kernel)
  change Impossible true (targetOf 18224093969492012264) 6 (stateOf g22 (db22[8]?.getD default)).toFinset at h
  have home : stateOf g22 (db22[8]?.getD default) = rootsOf 47 := by decide +kernel
  simpa only [home] using h
 have low22 : Lower true (rootsOf 47) (targetOf 18224093969492012264) 7 :=
  lowerFrom [(inputs.getD 0 zero,2,3),(inputs.getD 1 zero,1,3),(inputs.getD 2 zero,1,5),(inputs.getD 3 zero,2,10),(inputs.getD 5 zero,12,44)] (by unfold proper; decide +kernel) (by decide +kernel) (by decide +kernel) imp22
 have good23 : Good g23 := by
  refine ⟨?_,?_,checkedPerms (by decide +kernel)⟩
  · decide +kernel
  · intro s hs
    change s ∈ [(domainOf 31 0 16,7)] at hs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
    rcases hs with rfl
    · exact slice_correct (ms:=fixRows 224 16) (base:=rootsOf 15) (G:=targetOf 18368211356893118184)
       (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) low16
 have imp23 : Impossible true (targetOf 18368191565683813608) 7 (rootsOf 31).toFinset :=
  verifiedCut good23 (cap:=7) (cs:=[]) (ch:=rootsOf 31) (code:=1) (by decide +kernel) (by decide +kernel)
 have low23 : Lower true (rootsOf 31) (targetOf 18368191565683813608) 8 :=
  lowerFrom [(inputs.getD 0 zero,2,3),(inputs.getD 1 zero,1,3),(inputs.getD 2 zero,1,5),(inputs.getD 3 zero,2,10),(inputs.getD 4 zero,9,25)] (by unfold proper; decide +kernel) (by decide +kernel) (by decide +kernel) imp23
 have good24 : Good g24 := by
  refine ⟨?_,?_,checkedPerms (by decide +kernel)⟩
  · decide +kernel
  · intro s hs
    change s ∈ [(domainOf 31 0 16,5),(domainOf 31 8 0,5),(domainOf 31 16 0,5),(domainOf 31 4 0,4),(domainOf 31 2 0,4),(domainOf 31 1 0,4),(domainOf 31 17 0,4)] at hs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact slice_correct (ms:=fixRows 224 16) (base:=rootsOf 15) (G:=targetOf 18368774315436605162)
       (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) low17
    · exact slice_correct (ms:=fixRows 232 0) (base:=rootsOf 23) (G:=targetOf 16927598236496750824)
       (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) low5
    · exact slice_correct (ms:=fixRows 240 0) (base:=rootsOf 15) (G:=targetOf 18224093969760451816)
       (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) low15
    · exact slice_correct (ms:=fixRows 228 0) (base:=rootsOf 27) (G:=targetOf 17197783015559449736)
       (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) low8
    · exact slice_correct (ms:=fixRows 226 0) (base:=rootsOf 29) (G:=targetOf 18062513829713735840)
       (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) low11
    · exact slice_correct (ms:=fixRows 241 0) (base:=rootsOf 14) (G:=targetOf 18212834798890712256)
       (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) low4
    · exact slice_correct (ms:=fixRows 241 0) (base:=rootsOf 14) (G:=targetOf 18212834798890712256)
       (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) low4
 have imp24 : Impossible true (targetOf 18368772107823414504) 6 (rootsOf 31).toFinset := by
  have h := forestSound good24 db24 (all 24 (by decide +kernel)) 2 (by decide +kernel)
  change Impossible true (targetOf 18368772107823414504) 6 (stateOf g24 (db24[2]?.getD default)).toFinset at h
  have home : stateOf g24 (db24[2]?.getD default) = rootsOf 31 := by decide +kernel
  simpa only [home] using h
 have low24 : Lower true (rootsOf 31) (targetOf 18368772107823414504) 7 :=
  lowerFrom [(inputs.getD 0 zero,2,3),(inputs.getD 1 zero,1,3),(inputs.getD 2 zero,1,5),(inputs.getD 3 zero,2,10),(inputs.getD 4 zero,1,17)] (by unfold proper; decide +kernel) (by decide +kernel) (by decide +kernel) imp24
 have good25 : Good g25 := by
  refine ⟨?_,?_,checkedPerms (by decide +kernel)⟩
  · decide +kernel
  · intro s hs
    change s ∈ [(domainOf 47 32 0,7)] at hs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
    rcases hs with rfl
    · exact slice_correct (ms:=fixRows 240 0) (base:=rootsOf 15) (G:=targetOf 18368211356893118184)
       (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) low16
 have imp25 : Impossible true (targetOf 18368774315436474088) 7 (rootsOf 47).toFinset :=
  verifiedCut good25 (cap:=7) (cs:=[]) (ch:=rootsOf 47) (code:=1) (by decide +kernel) (by decide +kernel)
 have low25 : Lower true (rootsOf 47) (targetOf 18368774315436474088) 8 :=
  lowerFrom [(inputs.getD 0 zero,2,3),(inputs.getD 1 zero,1,3),(inputs.getD 2 zero,1,5),(inputs.getD 3 zero,1,9),(inputs.getD 5 zero,1,33)] (by unfold proper; decide +kernel) (by decide +kernel) (by decide +kernel) imp25
 have good26 : Good g26 := by
  refine ⟨?_,?_,checkedPerms (by decide +kernel)⟩
  · decide +kernel
  · intro s hs
    change s ∈ [(domainOf 55 2 0,5)] at hs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
    rcases hs with rfl
    · exact slice_correct (ms:=fixRows 202 0) (base:=rootsOf 53) (G:=targetOf 18085032171453194400)
       (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) low13
 have imp26 : Impossible true (targetOf 18374401693258280172) 5 (rootsOf 55).toFinset :=
  verifiedCut good26 (cap:=5) (cs:=[]) (ch:=rootsOf 55) (code:=1) (by decide +kernel) (by decide +kernel)
 have low26 : Lower true (rootsOf 55) (targetOf 18374401693258280172) 6 :=
  lowerFrom [(inputs.getD 0 zero,4,5),(inputs.getD 1 zero,0,2),(inputs.getD 2 zero,1,5),(inputs.getD 4 zero,1,17),(inputs.getD 5 zero,4,36)] (by unfold proper; decide +kernel) (by decide +kernel) (by decide +kernel) imp26
 have good27 : Good g27 := by
  refine ⟨?_,?_,checkedPerms (by decide +kernel)⟩
  · decide +kernel
  · intro s hs
    change s ∈ [(domainOf 63 0 16,8),(domainOf 63 2 0,8),(domainOf 63 32 0,8),(domainOf 63 0 32,7),(domainOf 63 16 0,7),(domainOf 63 4 0,6),(domainOf 63 1 0,6),(domainOf 63 0 8,6),(domainOf 63 8 0,6),(domainOf 63 17 0,5),(domainOf 63 8 16,5),(domainOf 63 8 32,5),(domainOf 63 16 32,5),(domainOf 63 24 0,4),(domainOf 63 1 48,4),(domainOf 63 17 32,4),(domainOf 63 40 0,4),(domainOf 63 56 0,4)] at hs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact slice_correct (ms:=fixRows 192 16) (base:=rootsOf 47) (G:=targetOf 18368774315436474088)
       (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) low25
    · exact slice_correct (ms:=fixRows 194 0) (base:=rootsOf 61) (G:=targetOf 18062513829713060000)
       (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) low20
    · exact slice_correct (ms:=fixRows 224 0) (base:=rootsOf 31) (G:=targetOf 18368191565683813608)
       (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) low23
    · exact slice_correct (ms:=fixRows 192 32) (base:=rootsOf 31) (G:=targetOf 18368772107823414504)
       (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) low24
    · exact slice_correct (ms:=fixRows 208 0) (base:=rootsOf 47) (G:=targetOf 18224093969492012264)
       (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) low22
    · exact slice_correct (ms:=fixRows 196 0) (base:=rootsOf 59) (G:=targetOf 17197783015557221512)
       (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) low19
    · exact slice_correct (ms:=fixRows 193 0) (base:=rootsOf 62) (G:=targetOf 18212834798890699968)
       (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) low21
    · exact slice_correct (ms:=fixRows 192 8) (base:=rootsOf 55) (G:=targetOf 18374401693258280172)
       (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) low26
    · exact slice_correct (ms:=fixRows 200 0) (base:=rootsOf 55) (G:=targetOf 16927598236463065320)
       (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) low18
    · exact slice_correct (ms:=fixRows 209 0) (base:=rootsOf 46) (G:=targetOf 18212834798085393600)
       (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) low14
    · exact slice_correct (ms:=fixRows 200 16) (base:=rootsOf 39) (G:=targetOf 16927600444076255464)
       (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) low6
    · exact slice_correct (ms:=fixRows 200 32) (base:=rootsOf 23) (G:=targetOf 16927598236496750824)
       (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) low5
    · exact slice_correct (ms:=fixRows 208 32) (base:=rootsOf 15) (G:=targetOf 18224093969760451816)
       (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) low15
    · exact slice_correct (ms:=fixRows 248 0) (base:=rootsOf 7) (G:=targetOf 16782920098433788136)
       (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) low0
    · exact slice_correct (ms:=fixRows 193 48) (base:=rootsOf 14) (G:=targetOf 18212834798890712256)
       (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) low4
    · exact slice_correct (ms:=fixRows 209 32) (base:=rootsOf 14) (G:=targetOf 18212834798890712256)
       (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) low4
    · exact slice_correct (ms:=fixRows 248 0) (base:=rootsOf 7) (G:=targetOf 16782920098433788136)
       (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) low0
    · exact slice_correct (ms:=fixRows 248 0) (base:=rootsOf 7) (G:=targetOf 16782920098433788136)
       (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) low0
 have imp27 : Impossible true (targetOf 18368772107823279336) 9 (rootsOf 63).toFinset := by
  have h := forestSound good27 db27 (all 27 (by decide +kernel)) 63 (by decide +kernel)
  change Impossible true (targetOf 18368772107823279336) 9 (stateOf g27 (db27[63]?.getD default)).toFinset at h
  have home : stateOf g27 (db27[63]?.getD default) = rootsOf 63 := by decide +kernel
  simpa only [home] using h
 have low27 : Lower true (rootsOf 63) (targetOf 18368772107823279336) 10 :=
  lowerFrom [(inputs.getD 0 zero,2,3),(inputs.getD 1 zero,1,3),(inputs.getD 2 zero,1,5),(inputs.getD 3 zero,2,10),(inputs.getD 4 zero,9,25),(inputs.getD 5 zero,12,44)] (by unfold proper; decide +kernel) (by decide +kernel) (by decide +kernel) imp27
 exact low27

end PEqualNP.Outside.L_meta_37159.Certificate

namespace PEqualNP.Outside.L_meta_37159.ExplicitCircuit
open PEqualNP.CircuitLowerBounds
def upper : Circuit :=
 ⟨[⟨.or,[0,1]⟩,⟨.and,[6,2]⟩,⟨.or,[0,3]⟩,⟨.and,[0,4]⟩,⟨.or,[9,2]⟩,⟨.and,[3,4]⟩,⟨.or,[11,5]⟩,⟨.and,[12,10]⟩,⟨.or,[13,1]⟩,⟨.and,[14,8]⟩,⟨.or,[15,7]⟩],16⟩
def target (x : Fin 6 → Bool) : Bool := Nat.testBit (4276813032 * 2 ^ 32 + 4276677864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem upperComputes : ∀ x : Fin 6 → Bool, upper.eval (List.ofFn x) = target x := by decide +kernel
theorem upperLegal : PEqualNP.MetaComplexity.Monotone2 upper := by
 intro g hg
 simp only [upper,List.mem_cons,List.not_mem_nil,or_false] at hg
 rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
end PEqualNP.Outside.L_meta_37159.ExplicitCircuit
namespace PEqualNP.Outside.L_meta_37159.GraphTarget
open PEqualNP.Outside.L_meta_37159.LiveCircuits
def cols7 : List Sig := inputs.take 6
def full : Sig := PEqualNP.Outside.L_meta_37159.Certificate.targetOf 18368772107823279336
end PEqualNP.Outside.L_meta_37159.GraphTarget
namespace PEqualNP.Outside.L_meta_37159.GraphTarget
open PEqualNP.Outside.L_meta_37159.LiveCircuits PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def sample7 (r : Row) (j : Fin 6) := bit r (cols7.getD j.val zero)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem sevenTable : ∀ r : Row, bit r full = PEqualNP.Outside.L_meta_37159.ExplicitCircuit.target (sample7 r) := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem sevenList : List.ofFn (fun i : Fin 6 => cols7.getD i.val zero) = cols7 := rfl
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem sevenSampled (r : Row) : List.ofFn (sample7 r) = cols7.map (bit r) := by
  rw [←sevenList,List.map_ofFn]; rfl
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem eval7 (C : Circuit) (h : FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates cols7).getD i zero) =
      (C.wires (List.ofFn (sample7 r))).getD i false := by
  rw [← b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),sevenSampled]
  rfl

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem binaryLower (low : Lower true cols7 full 10) (C : Circuit) (legal : FanInTwo C)
    (computes : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = PEqualNP.Outside.L_meta_37159.ExplicitCircuit.target x) :
    10 ≤ C.gates.countP (fun g => !isNot g) := by
  classical
  have goalEq : (execute C.gates cols7).getD C.output zero = full := by
    apply bit_ext
    intro r
    exact (eval7 C legal C.output r).trans ((computes (sample7 r)).trans (sevenTable r).symm)
  have rep := get_rep (u:=true) (execute C.gates cols7) C.output
  rw [goalEq] at rep
  unfold PEqualNP.Outside.L_meta_37159.LiveCircuits.Repr at rep
  have pg : bit 0 full = false := by decide +kernel
  have pfull : proper full := by unfold proper; decide +kernel
  rw [nrm_id pg] at rep
  obtain ⟨k,S,hk,run,sub⟩ := extract C.gates cols7 legal (by simp) pfull (rep.resolve_right (fun h => h pfull))
  have plain : cols7.all plainWord = true := by decide +kernel
  rw [nrm_map plain] at sub
  have rs := list_run run S.toList (Finset.nodup_toList _) (Finset.toList_toFinset _)
  have hs : supply true (cols7.map observe) ((S.toList.map observe).map (restrictRows (id : Row → Row))) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
    exact Or.inl (List.mem_map_of_mem (sub _ (Finset.mem_toList.mp ha)))
  have b := projected_bound (id : Row → Row) rs (observe_proper pfull) Reach.start hs (L:=10) low
  omega
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem gateLower (low : Lower true cols7 full 10) (C : Circuit) (legal : FanInTwo C)
    (negUsed : ∃ g ∈ C.gates, g.op = GateOp.not)
    (computes : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = PEqualNP.Outside.L_meta_37159.ExplicitCircuit.target x) :
    11 ≤ C.gates.length := by
  obtain ⟨g,hg,ng⟩ := negUsed
  have hc := binaryLower low C legal computes
  by_contra! h
  have all := (List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length (by omega : C.gates.length ≤ C.gates.countP (fun g => !isNot g)))) g hg
  simp [isNot,ng] at all

theorem solve (low : Lower true cols7 full 10) : ∀ s : ℕ,
 HasCircuitSize 6 PEqualNP.Outside.L_meta_37159.ExplicitCircuit.target s →
 ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool,
 C.eval (List.ofFn x) = PEqualNP.Outside.L_meta_37159.ExplicitCircuit.target x := by
 intro s hs
 obtain ⟨C,legal,size,computes⟩ := hs
 by_cases hn : ∃ g ∈ C.gates, g.op = GateOp.not
 · have bound := gateLower low C legal hn computes
   refine ⟨PEqualNP.Outside.L_meta_37159.ExplicitCircuit.upper,
    PEqualNP.Outside.L_meta_37159.ExplicitCircuit.upperLegal,?_,
    PEqualNP.Outside.L_meta_37159.ExplicitCircuit.upperComputes⟩
   change 11 ≤ s
   exact bound.trans size
 · refine ⟨C,?_,size,computes⟩
   intro g hg
   obtain ⟨ht,hw⟩ := legal g hg
   change g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not at ht
   rcases ht with ha | ho | hnot
   · exact ⟨Or.inl ha,hw⟩
   · exact ⟨Or.inr ho,hw⟩
   · exact (hn ⟨g,hg,hnot⟩).elim
end PEqualNP.Outside.L_meta_37159.GraphTarget

theorem PEqualNP.Outside.L_meta_37159 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276813032 * 2 ^ 32 + 4276677864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276813032 * 2 ^ 32 + 4276677864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
 have low := PEqualNP.Outside.L_meta_37159.Certificate.assembledLower PEqualNP.Outside.L_meta_37159.Certificate.allChecked
 have same : PEqualNP.Outside.L_meta_37159.Certificate.rootsOf 63 = PEqualNP.Outside.L_meta_37159.GraphTarget.cols7 := by decide +kernel
 rw [same] at low
 exact PEqualNP.Outside.L_meta_37159.GraphTarget.solve low

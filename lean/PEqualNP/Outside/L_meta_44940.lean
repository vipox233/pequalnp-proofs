import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_44940
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 128
def zero : Sig := 0
def one : Sig := BitVec.allOnes 128
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

def bit (i : Fin 128) (a : Sig) : Bool := a.getLsbD i.val
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


abbrev Row := Fin 128
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


def W (a : Nat) : Sig := BitVec.ofNat 128 a
def full : Nat := 0xffffffffffffffffffffffffffffffff
def xN : Nat → Nat
  | 0 => 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
  | 1 => 0xcccccccccccccccccccccccccccccccc
  | 2 => 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
  | 3 => 0xff00ff00ff00ff00ff00ff00ff00ff00
  | 4 => 0xffff0000ffff0000ffff0000ffff0000
  | 5 => 0xffffffff00000000ffffffff00000000
  | _ => 0xffffffffffffffff0000000000000000
def nb (o a b : Nat) : Nat :=
  bif Nat.beq o 0 then Nat.land a b else bif Nat.beq o 1 then Nat.lor a b else
    bif Nat.beq o 2 then Nat.xor a (Nat.land a b) else Nat.xor b (Nat.land a b)
theorem bit_W (r : Row) (a : Nat) : bit r (W a) = a.testBit r.val := by
  unfold bit W
  rw [BitVec.getLsbD_ofNat]
  simp [r.isLt]
theorem tb_land (a b i : Nat) : (Nat.land a b).testBit i = (a.testBit i && b.testBit i) := Nat.testBit_and ..
theorem tb_lor (a b i : Nat) : (Nat.lor a b).testBit i = (a.testBit i || b.testBit i) := Nat.testBit_or ..
theorem tb_xor (a b i : Nat) : (Nat.xor a b).testBit i = (a.testBit i ^^ b.testBit i) := Nat.testBit_xor ..
theorem nbeq {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases e : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true e) h
theorem W_nb (o a b : Nat) : W (nb o a b) = bin o (W a) (W b) := by
  apply bit_ext
  intro r
  rw [bit_bin,bit_W,bit_W,bit_W]
  by_cases h0 : o = 0
  · subst h0
    exact tb_land a b _
  by_cases h1 : o = 1
  · subst h1
    exact tb_lor a b _
  by_cases h2 : o = 2
  · subst h2
    change (Nat.xor a (Nat.land a b)).testBit r.val = _
    rw [tb_xor,tb_land]
    cases a.testBit r.val <;> cases b.testBit r.val <;> rfl
  · unfold nb
    rw [nbeq h0,nbeq h1,nbeq h2,if_neg h0,if_neg h1,if_neg h2]
    change (Nat.xor b (Nat.land a b)).testBit r.val = _
    rw [tb_xor,tb_land]
    cases a.testBit r.val <;> cases b.testBit r.val <;> rfl
theorem bin_four (u : Bool) (o : Nat) (h : (u || Nat.blt o 2) = true) : ∃ e, allowed u e ∧ ∀ a b, bin o a b = bin e a b := by
  cases u
  · refine ⟨o,Or.inl ?_,fun _ _ => rfl⟩
    simpa only [Bool.false_or,Nat.blt_eq] using h
  · by_cases h : o < 4
    · exact ⟨o,Or.inr ⟨rfl,h⟩,fun _ _ => rfl⟩
    · refine ⟨3,Or.inr ⟨rfl,by omega⟩,fun a b => ?_⟩
      have h0 : o ≠ 0 := by omega
      have h1 : o ≠ 1 := by omega
      have h2 : o ≠ 2 := by omega
      simp [bin,h0,h1,h2]
theorem W_zero : W 0 = zero := rfl
theorem W_full : W full = one := by
  apply bit_ext
  intro r
  rw [bit_W,bit_one]
  revert r
  decide +kernel
theorem W_inj {a b : Nat} (ha : a < 2^128) (hb : b < 2^128) (h : W a = W b) : a = b := by
  have := congrArg BitVec.toNat h
  simpa only [W,BitVec.toNat_ofNat,Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hb] using this

def rootsW (R : List Nat) : List Sig := R.map fun i => W (xN i)
def LowN (u : Bool) (R : List Nat) (T L : Nat) : Prop := Lower u (rootsW R) (W T) L
abbrev SliceD := Nat × Nat × List Nat
def SliceN (u : Bool) (R : List Nat) (T : Nat) (s : SliceD) : Prop :=
  Slice u (rootsW R) (W T) (W s.1) s.2.1 ∧ ∀ v ∈ s.2.2, v ∈ R

def baseOK (T : Nat) (R : List Nat) (E : List (Nat × Nat × Nat)) : Bool :=
  decide (T < 2^128) && !(T.testBit 0) && (E.map Prod.fst == R) && !R.isEmpty && decide (rootsW R).Nodup &&
  R.all (fun i => !((xN i).testBit 0)) &&
  E.all (fun e => decide (e.2.1 < 128) && decide (e.2.2 < 128) && (T.testBit e.2.1 != T.testBit e.2.2) &&
    R.all (fun i => i == e.1 || (xN i).testBit e.2.1 == (xN i).testBit e.2.2))

abbrev BaseP (T : Nat) (R : List Nat) : Prop :=
  T < 2^128 ∧ plainWord (W T) = true ∧ (rootsW R).Nodup ∧ (rootsW R).all plainWord = true ∧
  (∀ a ∈ rootsW R, Essential (W T) (rootsW R) a) ∧ proper (W T)
theorem BaseP.lt {T R} (h : BaseP T R) : T < 2^128 := h.1
theorem BaseP.plain {T R} (h : BaseP T R) : plainWord (W T) = true := h.2.1
theorem BaseP.nodup {T R} (h : BaseP T R) : (rootsW R).Nodup := h.2.2.1
theorem BaseP.plainR {T R} (h : BaseP T R) : (rootsW R).all plainWord = true := h.2.2.2.1
theorem BaseP.ess {T R} (h : BaseP T R) : ∀ a ∈ rootsW R, Essential (W T) (rootsW R) a := h.2.2.2.2.1
theorem BaseP.prop {T R} (h : BaseP T R) : proper (W T) := h.2.2.2.2.2

theorem baseOK_ok {T R E} (h : baseOK T R E = true) : BaseP T R := by
  simp only [baseOK,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq,Bool.not_eq_true',List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hT,h0⟩,hE⟩,hne⟩,nd⟩,pr⟩,he⟩ := h
  have ess : ∀ a ∈ rootsW R, Essential (W T) (rootsW R) a := by
    intro a ha
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
    rw [←hE] at hi
    obtain ⟨e,hem,rfl⟩ := List.mem_map.mp hi
    obtain ⟨⟨⟨h1,h2⟩,h3⟩,h4⟩ := he e hem
    refine ⟨⟨e.2.1,h1⟩,⟨e.2.2,h2⟩,?_,?_⟩
    · rw [bit_W,bit_W]
      simpa using h3
    · intro v hv hne
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hv
      rw [bit_W,bit_W]
      have := h4 j hj
      simp only [Bool.or_eq_true,beq_iff_eq] at this
      rcases this with rfl | this
      · exact absurd rfl hne
      · exact this
  refine ⟨hT,?_,nd,?_,ess,?_⟩
  · have : bit 0 (W T) = false := (bit_W 0 T).trans h0
    simp [plainWord,this]
  · rw [List.all_eq_true]
    intro a ha
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
    have : bit 0 (W (xN i)) = false := (bit_W 0 _).trans (by simpa using pr i hi)
    simp [plainWord,this]
  · cases R with
    | nil => simp at hne
    | cons i R =>
      obtain ⟨r,s,hd,_⟩ := ess (W (xN i)) (by simp [rootsW])
      constructor
      · intro hh
        rw [hh,bit_zero,bit_zero] at hd
        exact hd rfl
      · intro hh
        rw [hh,bit_one,bit_one] at hd
        exact hd rfl

theorem lowOf {u T R E K} (hB : baseOK T R E = true) (h : Impossible u (W T) K (rootsW R).toFinset) :
    LowN u R T (K+1) := by
  have b := baseOK_ok hB
  exact lower_impossible b.prop b.plain b.plainR b.ess h
theorem lowCount {u T R E K} (hB : baseOK T R E = true) (h : K + 2 ≤ R.length) : LowN u R T (K+1) := by
  apply lowOf hB
  intro k hk run
  have b := baseOK_ok hB
  have := live_size run
  rw [List.toFinset_card_of_nodup b.nodup,rootsW,List.length_map] at this
  omega

def rowOf : List Nat → Nat → Nat → Nat
  | [],w,_ => w
  | v::vs,w,r => rowOf vs (w + ((r % 2) <<< v)) (r / 2)
def sliceChk (R : List Nat) (T : Nat) (R' : List Nat) (G d : Nat) (vs : List Nat) (w : Nat) : Bool :=
  vs.all (fun v => R.contains v) &&
  (List.range 128).all (fun r => let q := rowOf vs w r
    Nat.blt q 128 && d.testBit q && (T.testBit q == G.testBit r)) &&
  R.all (fun i => (List.range 128).all (fun r => !((xN i).testBit (rowOf vs w r))) ||
    (List.range 128).all (fun r => (xN i).testBit (rowOf vs w r)) ||
    R'.any (fun j => (List.range 128).all (fun r => (xN i).testBit (rowOf vs w r) == (xN j).testBit r)))

theorem mkSlice {u R T E R' G E' d L vs w} (_hB : baseOK T R E = true) (hB' : baseOK G R' E' = true)
    (hL : LowN u R' G L) (h : sliceChk R T R' G d vs w = true) : SliceN u R T (d,L,vs) := by
  have b' := baseOK_ok hB'
  simp only [sliceChk,Bool.and_eq_true,List.all_eq_true,List.mem_range,Bool.or_eq_true,beq_iff_eq,
    Bool.not_eq_true',List.any_eq_true,Nat.blt_eq,List.contains_eq_mem,decide_eq_true_eq] at h
  obtain ⟨⟨hv,hr⟩,hR⟩ := h
  let f : Row → Row := fun r => ⟨rowOf vs w r.val,(hr r.val r.isLt).1.1⟩
  have fe (r : Row) (a : Nat) : bit (f r) (W a) = a.testBit (rowOf vs w r.val) := bit_W _ _
  have obs : restrictRows f (observe (W T)) = observe (W G) := by
    funext r
    change bit (f r) (W T) = bit r (W G)
    rw [fe,bit_W]
    exact (hr r.val r.isLt).2
  refine ⟨⟨f,rootsW R',?_,?_,?_,?_⟩,hv⟩
  · intro r
    rw [fe]
    exact (hr r.val r.isLt).1.2
  · intro a ha
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
    rcases hR i hi with (h | h) | ⟨j,hj,h⟩
    · refine Or.inr (Or.inl ⟨false,funext fun r => ?_⟩)
      exact (fe r _).trans (h r.val r.isLt)
    · refine Or.inr (Or.inl ⟨true,funext fun r => ?_⟩)
      exact (fe r _).trans (h r.val r.isLt)
    · have e : restrictRows f (observe (W (xN i))) = observe (W (xN j)) := by
        funext r
        exact (fe r _).trans ((h r.val r.isLt).trans (bit_W r _).symm)
      rw [e]
      exact Or.inl (List.mem_map_of_mem (List.mem_map_of_mem hj))
  · rw [obs]
    exact observe_proper b'.prop
  · rw [obs]
    exact hL

def opOK (u : Bool) (o : Nat) : Bool := u || Nat.blt o 2
def av (u : Bool) (d : Nat) (P : List Nat) (v : Nat) : Bool :=
  let m := Nat.land v d
  Nat.beq m 0 || Nat.beq m d || P.any (fun x => Nat.beq x m || (u && Nat.beq x (Nat.xor d m)))
def cn (d v : Nat) : Nat :=
  let m := Nat.land v d
  bif Nat.beq m 0 || Nat.beq m d then 1 else 0
def sumc (d : Nat) : List Nat → Nat
  | [] => 0
  | v::l => Nat.add (cn d v) (sumc d l)
def mkPool (u : Bool) (P : List Nat) : List Nat → List Nat
  | [] => P
  | c::cs => mkPool u (bif opOK u (Nat.mod c 4) then P ++ [nb (Nat.mod c 4) (P.getD (Nat.mod (Nat.div c 4) 32) 0) (P.getD (Nat.div c 128) 0)] else P) cs
def initPool (d : Nat) (vs : List Nat) : List Nat := vs.map fun v => Nat.land (xN v) d

abbrev RF (f : Row → Row) (v : Nat) : Wire Row := restrictRows f (observe (W v))
def PS (u : Bool) (f : Row → Row) (bank : List (Wire Row)) (P : List Nat) : Prop :=
  ∀ v ∈ P, Available u bank (RF f v)
theorem rf_apply (f : Row → Row) (v : Nat) (r : Row) : RF f v r = v.testBit (f r).val := bit_W _ _
theorem rf_land {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) (v : Nat) :
    RF f (Nat.land v d) = RF f v := by
  funext r
  have h := dom r
  rw [bit_W] at h
  rw [rf_apply,rf_apply]
  have : (Nat.land v d).testBit (f r).val = (v.testBit (f r).val && d.testBit (f r).val) := Nat.testBit_and ..
  rw [this,h,Bool.and_true]
theorem rf_zero {f : Row → Row} : RF f 0 = fun _ => false := by
  funext r
  rw [rf_apply]
  exact Nat.zero_testBit _
theorem rf_dom {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) : RF f d = fun _ => true := by
  funext r
  exact dom r
theorem rf_xor {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) (m : Nat) :
    RF f (Nat.xor d m) = inv (RF f m) := by
  funext r
  have h := dom r
  rw [bit_W] at h
  change RF f (Nat.xor d m) r = !(RF f m r)
  rw [rf_apply,rf_apply]
  have : (Nat.xor d m).testBit (f r).val = ((d.testBit (f r).val) ^^ (m.testBit (f r).val)) := Nat.testBit_xor ..
  rw [this,h,Bool.true_xor]
theorem cn_ok {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) (v : Nat) : cn d v ≤ cost (RF f v) := by
  change (bif (Nat.beq (Nat.land v d) 0 || Nat.beq (Nat.land v d) d) then 1 else 0) ≤ _
  cases h : (Nat.beq (Nat.land v d) 0 || Nat.beq (Nat.land v d) d)
  · exact Nat.zero_le _
  · have c : Constant (RF f v) := by
      rw [←rf_land dom v]
      rw [Bool.or_eq_true] at h
      rcases h with h | h
      · rw [Nat.eq_of_beq_eq_true h,rf_zero]
        exact ⟨false,rfl⟩
      · rw [Nat.eq_of_beq_eq_true h,rf_dom dom]
        exact ⟨true,rfl⟩
    rw [cost,if_pos c]
    exact Nat.le_refl 1
theorem av_ok {u} {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) {bank P v} (hP : PS u f bank P)
    (h : av u d P v = true) : Available u bank (RF f v) := by
  simp only [av,Bool.or_eq_true,List.any_eq_true,Bool.and_eq_true] at h
  rw [←rf_land dom v]
  rcases h with (h | h) | ⟨x,hx,h | ⟨hu,h⟩⟩
  · rw [Nat.eq_of_beq_eq_true h,rf_zero]
    exact Or.inr (Or.inl ⟨false,rfl⟩)
  · rw [Nat.eq_of_beq_eq_true h,rf_dom dom]
    exact Or.inr (Or.inl ⟨true,rfl⟩)
  · rw [←Nat.eq_of_beq_eq_true h]
    exact hP x hx
  · have e := hP x hx
    rw [Nat.eq_of_beq_eq_true h,rf_xor dom] at e
    have e' := avail_inv hu e
    rwa [inv_inv'] at e'
theorem rf_nb (f : Row → Row) (o a b : Nat) : RF f (nb o a b) = comb o (RF f a) (RF f b) := by
  unfold RF
  rw [W_nb,obs_bin,restrict_comb]
theorem pay_nb {u} {f : Row → Row} {roots bank p P} (o a b : Nat) (ho : opOK u o = true) (hr : Reach u roots p bank) (hP : PS u f bank P)
    (ha : Available u bank (RF f a)) (hb : Available u bank (RF f b)) :
    ∃ next, Reach u roots (p+1) next ∧ PS u f next P ∧ Available u next (RF f (nb o a b)) ∧
      ∀ v, Available u bank v → Available u next v := by
  obtain ⟨e,he,heq⟩ := bin_four u o ho
  have hn : RF f (nb o a b) = comb e (RF f a) (RF f b) := by
    unfold RF
    rw [W_nb,heq,obs_bin,restrict_comb]
  obtain ⟨op,x,y,e1,hx,hy,_,_⟩ := comb_prime (d:=e) he ha hb
  refine ⟨_,Reach.two op hr hx hy,fun v hv => available_cons _ (hP v hv),?_,fun v hv => available_cons _ hv⟩
  rw [hn,e1]
  exact Or.inl (by simp)
theorem getD_ps {u} {f : Row → Row} {bank P} (hP : PS u f bank P) (i : Nat) : Available u bank (RF f (P.getD i 0)) := by
  rw [List.getD_eq_getElem?_getD]
  cases h : P[i]? with
  | none => exact Or.inr (Or.inl ⟨false,rf_zero⟩)
  | some a => exact hP a (List.mem_of_getElem? h)
theorem mkPool_ok {u} {f : Row → Row} {roots} (cs : List Nat) {bank p P} (hr : Reach u roots p bank)
    (hP : PS u f bank P) : ∃ next, Reach u roots (p+cs.length) next ∧ PS u f next (mkPool u P cs) := by
  induction cs generalizing bank p P with
  | nil => exact ⟨bank,hr,hP⟩
  | cons c cs ih =>
    have big : ∃ next, Reach u roots (p+1) next ∧ PS u f next (bif opOK u (Nat.mod c 4) then P ++ [nb (Nat.mod c 4) (P.getD (Nat.mod (Nat.div c 4) 32) 0) (P.getD (Nat.div c 128) 0)] else P) := by
      cases ho : opOK u (Nat.mod c 4)
      · refine ⟨_,Reach.two false hr (Or.inr (Or.inl ⟨false,rfl⟩)) (Or.inr (Or.inl ⟨false,rfl⟩)),fun v hv => available_cons _ (hP v hv)⟩
      · obtain ⟨next,h1,h2,h3,_⟩ := pay_nb (Nat.mod c 4) _ _ ho hr hP (getD_ps hP (Nat.mod (Nat.div c 4) 32)) (getD_ps hP (Nat.div c 128))
        refine ⟨next,h1,?_⟩
        intro v hv
        rw [cond_true] at hv
        rcases List.mem_append.mp hv with hv | hv
        · exact h2 v hv
        · rw [List.mem_singleton.mp hv]
          exact h3
    obtain ⟨next,h1,this⟩ := big
    obtain ⟨out,o1,o2⟩ := ih h1 this
    exact ⟨out,by rw [List.length_cons,show p+(cs.length+1) = p+1+cs.length by omega]; exact o1,o2⟩

abbrev CutV := Nat × Nat × Nat × List Nat
def keepB (u : Bool) (d : Nat) (P : List Nat) (ka : Bool) (a : Nat) : Bool := bif ka then av u d P a else true
def keepC (d : Nat) (ka : Bool) (a : Nat) : Nat := bif ka then cn d a else 0
def cutEval (u : Bool) (k : Nat) (rest : List Nat) (a b z : Nat) (ka kb : Bool) (c : CutV) : Bool :=
  rest.all (av u c.1 c.2.2.2) && keepB u c.1 c.2.2.2 ka a && keepB u c.1 c.2.2.2 kb b &&
  (bif av u c.1 c.2.2.2 z then
    Nat.blt (Nat.add k c.2.2.1) (Nat.add c.2.1 (Nat.add (Nat.add (sumc c.1 rest) (cn c.1 z)) (Nat.add (keepC c.1 ka a) (keepC c.1 kb b))))
  else av u c.1 c.2.2.2 a && av u c.1 c.2.2.2 b &&
    Nat.blt (Nat.add (Nat.add k c.2.2.1) 1) (Nat.add c.2.1 (Nat.add (Nat.add (sumc c.1 rest) (cn c.1 z)) (Nat.add (keepC c.1 ka a) (keepC c.1 kb b)))))
def same (u : Bool) (p : Nat × Nat) (v : Nat) : Bool :=
  bif u then Nat.testBit v p.1 == Nat.testBit v p.2 else !(Nat.testBit v p.1) || Nat.testBit v p.2
def sepEval (u : Bool) (rest : List Nat) (a b z : Nat) (ka kb : Bool) (p : Nat × Nat) : Bool :=
  same u p z && (!ka || same u p a) && (!kb || same u p b) && rest.all (same u p)
def sepOK (T : Nat) (p : Nat × Nat) : Bool := Nat.blt p.1 128 && Nat.blt p.2 128 && T.testBit p.1 && !(T.testBit p.2)

def kidW (rest : List Nat) (a b z : Nat) (ka kb : Bool) : List Sig :=
  W z :: kept ka (W a) (kept kb (W b) (rest.map W))
theorem sumc_ok {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) (l : List Nat) :
    sumc d l ≤ mass (l.map (RF f)) := by
  induction l with
  | nil => simp [sumc]
  | cons v l ih =>
    rw [List.map_cons,mass_cons]
    exact Nat.add_le_add (cn_ok dom v) ih
theorem mass_keep {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) (ka : Bool) (a : Nat) (l : List (Wire Row)) :
    keepC d ka a + mass l ≤ mass (kept ka (RF f a) l) := by
  cases ka
  · simp [keepC,kept]
  · rw [kept,if_pos rfl,mass_cons]
    exact Nat.add_le_add_right (cn_ok dom a) _
theorem kid_map (f : Row → Row) (rest : List Nat) (a b z : Nat) (ka kb : Bool) :
    ((kidW rest a b z ka kb).map observe).map (restrictRows f) =
      RF f z :: kept ka (RF f a) (kept kb (RF f b) (rest.map (RF f))) := by
  cases ka <;> cases kb <;> simp [kidW,kept,List.map_map,Function.comp_def,RF]

def CutP (u : Bool) (_R : List Nat) (T : Nat) (c : CutV) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig) (bank : List (Wire Row)), (∀ r, bit (f r) (W c.1) = true) ∧
    ¬Constant (restrictRows f (observe (W T))) ∧ Reach u (roots.map observe) c.2.2.1 bank ∧ PS u f bank c.2.2.2 ∧
    ∀ p bank, Reach u (roots.map observe) p bank → Available u bank (restrictRows f (observe (W T))) → c.2.1 ≤ p

theorem cut_sound {u R T c k rest a b o ka kb} (hc : CutP u R T c) (ho : opOK u o = true)
    (nd : (kidW rest a b (nb o a b) ka kb).Nodup)
    (h : cutEval u k rest a b (nb o a b) ka kb c = true) :
    Impossible u (W T) k (kidW rest a b (nb o a b) ka kb).toFinset := by
  obtain ⟨f,roots,bank,dom,nc,hr,hP,lo⟩ := hc
  simp only [cutEval,Bool.and_eq_true,List.all_eq_true] at h
  obtain ⟨⟨⟨h1,h2⟩,h3⟩,h4⟩ := h
  have key : ∃ q bank', Reach u (roots.map observe) q bank' ∧ PS u f bank' c.2.2.2 ∧ Available u bank' (RF f (nb o a b)) ∧
      k + q < c.2.1 + ((sumc c.1 rest + cn c.1 (nb o a b)) + (keepC c.1 ka a + keepC c.1 kb b)) := by
    cases hz : av u c.1 c.2.2.2 (nb o a b)
    · rw [hz,cond_false,Bool.and_eq_true,Bool.and_eq_true,Nat.blt_eq] at h4
      obtain ⟨next,n1,n2,n3,_⟩ := pay_nb o a b ho hr hP (av_ok dom hP h4.1.1) (av_ok dom hP h4.1.2)
      refine ⟨_,next,n1,n2,n3,?_⟩
      have := h4.2
      exact this
    · rw [hz,cond_true,Nat.blt_eq] at h4
      exact ⟨_,bank,hr,hP,av_ok dom hP hz,h4⟩
  obtain ⟨q,bank',r1,r2,r3,r4⟩ := key
  intro k' hk run
  have supp : supply u bank' (((kidW rest a b (nb o a b) ka kb).map observe).map (restrictRows f)) := by
    rw [kid_map]
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact r3
    have kb' : ∀ v ∈ kept kb (RF f b) (rest.map (RF f)), Available u bank' v := by
      intro v hv
      cases kb
      · obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hv
        exact av_ok dom r2 (h1 x hx)
      · rcases List.mem_cons.mp hv with rfl | hv
        · exact av_ok dom r2 h3
        · obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hv
          exact av_ok dom r2 (h1 x hx)
    cases ka
    · exact kb' v hv
    · rcases List.mem_cons.mp hv with rfl | hv
      · exact av_ok dom r2 h2
      · exact kb' v hv
  have bound := projected_bound f (list_run run _ nd rfl) nc r1 supp lo
  rw [kid_map,mass_cons] at bound
  have m1 := mass_keep dom ka a (kept kb (RF f b) (rest.map (RF f)))
  have m2 := mass_keep dom kb b (rest.map (RF f))
  have m3 := sumc_ok dom rest
  have m4 := cn_ok dom (nb o a b)
  omega

theorem kid_mem {rest : List Nat} {a b z : Nat} {ka kb : Bool} {v : Sig} (hv : v ∈ kidW rest a b z ka kb) :
    ∃ x, v = W x ∧ (x = z ∨ (ka = true ∧ x = a) ∨ (kb = true ∧ x = b) ∨ x ∈ rest) := by
  rcases List.mem_cons.mp hv with rfl | hv
  · exact ⟨z,rfl,Or.inl rfl⟩
  have low : ∀ v ∈ kept kb (W b) (rest.map W), ∃ x, v = W x ∧ ((kb = true ∧ x = b) ∨ x ∈ rest) := by
    intro v hv
    cases kb
    · obtain ⟨x,hx,e⟩ := List.mem_map.mp hv
      exact ⟨x,e.symm,Or.inr hx⟩
    · rcases List.mem_cons.mp hv with e | hv
      · exact ⟨b,e,Or.inl ⟨rfl,rfl⟩⟩
      · obtain ⟨x,hx,e⟩ := List.mem_map.mp hv
        exact ⟨x,e.symm,Or.inr hx⟩
  cases ka
  · obtain ⟨x,h1,h2⟩ := low v hv
    exact ⟨x,h1,Or.inr (Or.inr h2)⟩
  · rcases List.mem_cons.mp hv with e | hv
    · exact ⟨a,e,Or.inr (Or.inl ⟨rfl,rfl⟩)⟩
    · obtain ⟨x,h1,h2⟩ := low v hv
      exact ⟨x,h1,Or.inr (Or.inr h2)⟩
theorem sep_sound {u T k rest a b o ka kb p} (hT : sepOK T p = true)
    (h : sepEval u rest a b (nb o a b) ka kb p = true) :
    Impossible u (W T) k (kidW rest a b (nb o a b) ka kb).toFinset := by
  simp only [sepOK,Bool.and_eq_true,Nat.blt_eq,Bool.not_eq_true'] at hT
  obtain ⟨⟨⟨p1,p2⟩,t1⟩,t2⟩ := hT
  simp only [sepEval,Bool.and_eq_true,Bool.or_eq_true,Bool.not_eq_true',List.all_eq_true] at h
  obtain ⟨⟨⟨h1,h2⟩,h3⟩,h4⟩ := h
  have all : ∀ v ∈ kidW rest a b (nb o a b) ka kb, ∃ x, v = W x ∧ same u p x = true := by
    intro v hv
    obtain ⟨x,rfl,hx⟩ := kid_mem hv
    refine ⟨x,rfl,?_⟩
    rcases hx with rfl | ⟨q,rfl⟩ | ⟨q,rfl⟩ | hx
    · exact h1
    · subst q; exact h2.resolve_left (by simp)
    · subst q; exact h3.resolve_left (by simp)
    · exact h4 x hx
  intro k' _ run
  cases u
  · obtain ⟨v,hv,hp,hn⟩ := mono_row_difference run rfl (r:=⟨p.1,p1⟩) (s:=⟨p.2,p2⟩) (by rw [bit_W]; exact t1) (by rw [bit_W]; exact t2)
    obtain ⟨x,rfl,hx⟩ := all v (List.mem_toFinset.mp hv)
    rw [bit_W] at hp hn
    simp only [same,cond_false,Bool.or_eq_true,Bool.not_eq_true'] at hx
    rcases hx with hx | hx
    · rw [hx] at hp; exact Bool.noConfusion hp
    · rw [hx] at hn; exact Bool.noConfusion hn
  · obtain ⟨v,hv,hne⟩ := live_row_difference run (r:=⟨p.1,p1⟩) (s:=⟨p.2,p2⟩) (by rw [bit_W,bit_W,t1,t2]; simp)
    obtain ⟨x,rfl,hx⟩ := all v (List.mem_toFinset.mp hv)
    apply hne
    rw [bit_W,bit_W]
    simpa only [same,cond_true,beq_iff_eq] using hx

def KWOwn (S : Finset Sig) (T : Sig) (owns : Sig → Row → Row → Prop) : Prop :=
  (∀ p n, bit p T = true → bit n T = false → ∃ v, owns v p n) ∧
  (∀ v p n, owns v p n → v ∈ S ∧ bit p v = true ∧ bit n v = false) ∧
  (∀ v w p n, owns v p n → owns w p n → v = w) ∧
  (∀ v p n p' n', owns v p n → owns v p' n' → owns v p n')
abbrev KWRooms (S : Finset Sig) (T : Sig) := {o : Sig → Row → Row → Prop // KWOwn S T o}
def KWRooms.owns {S T} (H : KWRooms S T) : Sig → Row → Row → Prop := H.1
theorem KWRooms.total {S T} (H : KWRooms S T) : ∀ p n, bit p T = true → bit n T = false → ∃ v, H.owns v p n := H.2.1
theorem KWRooms.valid {S T} (H : KWRooms S T) {v p n} : H.owns v p n → v ∈ S ∧ bit p v = true ∧ bit n v = false := H.2.2.1 v p n
theorem KWRooms.unique {S T} (H : KWRooms S T) {v w p n} : H.owns v p n → H.owns w p n → v = w := H.2.2.2.1 v w p n
theorem KWRooms.rect {S T} (H : KWRooms S T) {v p n p' n'} : H.owns v p n → H.owns v p' n' → H.owns v p n' := H.2.2.2.2 v p n p' n'
theorem kwLeaf (T : Sig) : Nonempty (KWRooms {T} T) := by
  refine ⟨⟨fun v p n => v = T ∧ bit p T = true ∧ bit n T = false,?_,?_,?_,?_⟩⟩
  · intro p n hp hn
    exact ⟨T,rfl,hp,hn⟩
  · rintro v p n ⟨rfl,hp,hn⟩
    exact ⟨by simp,hp,hn⟩
  · rintro v w p n ⟨rfl,_⟩ ⟨rfl,_⟩
    rfl
  · rintro v p n p' n' ⟨rfl,hp,_⟩ ⟨_,_,hn⟩
    exact ⟨rfl,hp,hn⟩
theorem kwFork {T : Sig} {U : Finset Sig} {a b : Sig} {d : Nat} (d01 : d=0 ∨ d=1) (hab : a ≠ b) (ha : a ∉ U) (hb : b ∉ U)
    (hz : bin d a b ∉ U) (H : KWRooms (insert (bin d a b) U) T) : Nonempty (KWRooms (insert a (insert b U)) T) := by
  classical
  let z := bin d a b
  let own : Sig → Row → Row → Prop := fun v p n => (v ∈ U ∧ H.owns v p n) ∨
    (H.owns z p n ∧ v = (if d=0 then (if bit n a = false then a else b) else (if bit p a = true then a else b)))
  have pickU : ∀ (p n : Row), (if d=0 then (if bit n a = false then a else b) else (if bit p a = true then a else b)) ∉ U := by
    intro p n
    split <;> split <;> assumption
  refine ⟨⟨own,?_,?_,?_,?_⟩⟩
  · intro p n hp hn
    obtain ⟨v,hv⟩ := H.total p n hp hn
    rcases Finset.mem_insert.mp (H.valid hv).1 with e | hm
    · refine ⟨_,Or.inr ⟨?_,rfl⟩⟩
      rw [show v = z from e] at hv
      exact hv
    · exact ⟨v,Or.inl ⟨hm,hv⟩⟩
  · intro v p n h
    rcases h with ⟨hm,hv⟩ | ⟨hv,rfl⟩
    · exact ⟨Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm),(H.valid hv).2⟩
    · obtain ⟨_,hp,hn⟩ := H.valid hv
      change bit p (bin d a b) = true at hp
      change bit n (bin d a b) = false at hn
      rw [bit_bin] at hp hn
      rcases d01 with rfl | rfl
      · cases pa : bit p a <;> cases na : bit n a <;> cases pb : bit p b <;> cases nb' : bit n b <;> simp_all
      · cases pa : bit p a <;> cases na : bit n a <;> cases pb : bit p b <;> cases nb' : bit n b <;> simp_all
  · intro v w p n h1 h2
    rcases h1 with ⟨vU,hv⟩ | ⟨hv,rfl⟩ <;> rcases h2 with ⟨wU,hw⟩ | ⟨hw,rfl⟩
    · exact H.unique hv hw
    · exact absurd (show z ∈ U by rw [←H.unique hv hw]; exact vU) hz
    · exact absurd (show z ∈ U by rw [←H.unique hw hv]; exact wU) hz
    · rfl
  · intro v p n p' n' h1 h2
    rcases h1 with ⟨vU,hv⟩ | ⟨hv,e1⟩ <;> rcases h2 with ⟨wU,hw⟩ | ⟨hw,e2⟩
    · exact Or.inl ⟨vU,H.rect hv hw⟩
    · exact absurd (e2 ▸ vU) (pickU p' n')
    · exact absurd (e1 ▸ wU) (pickU p n)
    · refine Or.inr ⟨H.rect hv hw,?_⟩
      by_cases h : d=0
      · rw [if_pos h] at e2 ⊢
        exact e2
      · rw [if_neg h] at e1 ⊢
        exact e1
theorem kwTight {T : Sig} {k : Nat} {S : Finset Sig} (run : Live false T k S) (tight : S.card=k+1) :
    Nonempty (KWRooms S T) := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,_⟩ := run
    exact kwLeaf T
  | succ k ih =>
    obtain ⟨U,a,b,d,hd,rfl,_,_,hab,hfresh,tail⟩ := run
    have fresh : bin d a b ∉ U := fun h => hfresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    have li := live_size tail
    rw [Finset.card_insert_of_notMem fresh] at li
    have le1 := Finset.card_insert_le a (insert b U)
    have le2 := Finset.card_insert_le b U
    have ha : a ∉ U := by
      intro h
      rw [Finset.insert_eq_of_mem (Finset.mem_insert_of_mem h : a ∈ insert b U)] at tight
      omega
    have hb : b ∉ U := by
      intro h
      rw [Finset.insert_eq_of_mem h] at tight le1
      omega
    have eq : (insert (bin d a b) U).card=k+1 := by
      rw [Finset.card_insert_of_notMem fresh]
      omega
    obtain ⟨H⟩ := ih tail eq
    have d01 : d=0 ∨ d=1 := by
      rcases hd with h | ⟨h,_⟩
      · omega
      · exact Bool.noConfusion h
    exact kwFork d01 hab ha hb fresh H
def only (l : List Nat) (p n a : Nat) : Bool :=
  Nat.blt p 128 && Nat.blt n 128 && l.all (fun x => !(Nat.testBit x p) || Nat.testBit x n || Nat.beq x a)
abbrev KwD := Nat × Nat × Nat × Nat × Nat × Nat
def findW (l : List Nat) (p n : Nat) : Nat := (l.find? (fun x => Nat.testBit x p && !(Nat.testBit x n))).getD 0
def kwOK (T : Nat) (q : KwD) : Bool :=
  T.testBit q.1 && T.testBit q.2.2.2.1 && T.testBit q.2.2.2.2.2 && !(T.testBit q.2.1) && !(T.testBit q.2.2.1) && !(T.testBit q.2.2.2.2.1)
def kwList (l : List Nat) (q : KwD) : Bool :=
  let a := findW l q.1 q.2.2.1
  let b := findW l q.1 q.2.2.2.2.1
  only l q.1 q.2.2.1 a && only l q.2.2.2.1 q.2.1 a &&
  (bif Nat.beq q.1 q.2.2.2.2.2 && Nat.beq q.2.1 q.2.2.2.2.1 then !(Nat.testBit a q.1 && !(Nat.testBit a q.2.1))
   else only l q.1 q.2.2.2.2.1 b && only l q.2.2.2.2.2 q.2.1 b && !(Nat.beq a b))
theorem only_own {l : List Nat} {T p n a : Nat} (H : KWRooms ((l.map W).toFinset) (W T))
    (h : only l p n a = true) (tp : T.testBit p = true) (tn : T.testBit n = false) :
    ∃ (hp : p < 128) (hn : n < 128), H.owns (W a) ⟨p,hp⟩ ⟨n,hn⟩ := by
  simp only [only,Bool.and_eq_true,Nat.blt_eq,List.all_eq_true,Bool.or_eq_true,Bool.not_eq_true'] at h
  obtain ⟨⟨hp,hn⟩,hl⟩ := h
  refine ⟨hp,hn,?_⟩
  obtain ⟨v,hv⟩ := H.total ⟨p,hp⟩ ⟨n,hn⟩ (by rw [bit_W]; exact tp) (by rw [bit_W]; exact tn)
  obtain ⟨hm,h1,h2⟩ := H.valid hv
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hm)
  rw [bit_W] at h1 h2
  rcases hl x hx with (h | h) | h
  · rw [h] at h1; exact Bool.noConfusion h1
  · rw [h] at h2; exact Bool.noConfusion h2
  · rw [Nat.eq_of_beq_eq_true h] at hv
    exact hv
theorem kw_sound {T k : Nat} {l : List Nat} (nd : (l.map W).Nodup) (size : l.length = k+1) (lt : ∀ x ∈ l, x < 2^128) (q : KwD)
    (hT : kwOK T q = true) (h : kwList l q = true) : Impossible false (W T) k (l.map W).toFinset := by
  intro k' hk run
  have lb := live_size run
  rw [List.toFinset_card_of_nodup nd,List.length_map] at lb
  obtain ⟨H⟩ := kwTight run (by rw [List.toFinset_card_of_nodup nd,List.length_map]; omega)
  simp only [kwOK,Bool.and_eq_true,Bool.not_eq_true'] at hT
  obtain ⟨⟨⟨⟨⟨t1,t2⟩,t3⟩,t4⟩,t5⟩,t6⟩ := hT
  simp only [kwList,Bool.and_eq_true] at h
  obtain ⟨⟨h1,h2⟩,h3⟩ := h
  obtain ⟨hp,hna,o1⟩ := only_own H h1 t1 t5
  obtain ⟨hpa,hn,o2⟩ := only_own H h2 t2 t4
  have own := H.rect o1 o2
  cases hc : (Nat.beq q.1 q.2.2.2.2.2 && Nat.beq q.2.1 q.2.2.2.2.1)
  · rw [hc,cond_false] at h3
    simp only [Bool.and_eq_true,Bool.not_eq_true'] at h3
    obtain ⟨⟨h4,h5⟩,h6⟩ := h3
    obtain ⟨_,hnb,o3⟩ := only_own H h4 t1 t6
    obtain ⟨hpb,_,o4⟩ := only_own H h5 t3 t4
    have own' := H.rect o3 o4
    have ee := H.unique own own'
    have mem : ∀ {a : Nat}, W a ∈ (l.map W).toFinset → ∃ x ∈ l, W x = W a := by
      intro a ha
      obtain ⟨x,hx,e⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
      exact ⟨x,hx,e⟩
    have fw : ∀ p n, findW l p n < 2^128 := by
      intro p n
      unfold findW
      cases hf : l.find? (fun x => Nat.testBit x p && !(Nat.testBit x n)) with
      | none => exact Nat.two_pow_pos 128
      | some x => exact lt x (List.mem_of_find?_eq_some hf)
    have := W_inj (fw _ _) (fw _ _) ee
    rw [this,Nat.beq_refl] at h6
    exact Bool.noConfusion h6
  · rw [hc,cond_true] at h3
    have v := (H.valid own).2
    rw [bit_W,bit_W] at v
    rw [v.1,v.2] at h3
    exact Bool.noConfusion h3

def hiM : Nat → Nat
  | 0 => 0x22222222222222222222222222222222
  | 1 => 0x0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c
  | 2 => 0x00f000f000f000f000f000f000f000f0
  | 3 => 0x0000ff000000ff000000ff000000ff00
  | _ => 0x00000000ffff000000000000ffff0000
def loM : Nat → Nat
  | 0 => 0x44444444444444444444444444444444
  | 1 => 0x30303030303030303030303030303030
  | 2 => 0x0f000f000f000f000f000f000f000f00
  | 3 => 0x00ff000000ff000000ff000000ff0000
  | _ => 0x0000ffff000000000000ffff00000000
def keM : Nat → Nat
  | 0 => 0x99999999999999999999999999999999
  | 1 => 0xc3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3
  | 2 => 0xf00ff00ff00ff00ff00ff00ff00ff00f
  | 3 => 0xff0000ffff0000ffff0000ffff0000ff
  | _ => 0xffff00000000ffffffff00000000ffff
def shM : Nat → Nat
  | 0 => 1
  | 1 => 2
  | 2 => 4
  | 3 => 8
  | _ => 16
def swapN (i v : Nat) : Nat :=
  Nat.lor (Nat.lor (Nat.land v (keM i)) (Nat.shiftLeft (Nat.land v (hiM i)) (shM i))) (Nat.shiftRight (Nat.land v (loM i)) (shM i))
def sig (i : Nat) (r : Row) : Row :=
  if (hiM i).testBit r.val then Fin.ofNat 128 (r.val + shM i) else
    if (loM i).testBit r.val then Fin.ofNat 128 (r.val - shM i) else r
def swapFacts (i : Nat) (r : Row) : Prop :=
  ((keM i).testBit r.val = true ∧ (sig i r).val = r.val ∧ (decide (shM i ≤ r.val) && (hiM i).testBit (r.val - shM i)) = false ∧ (loM i).testBit (shM i + r.val) = false) ∨
  ((keM i).testBit r.val = false ∧ shM i ≤ r.val ∧ (sig i r).val = r.val - shM i ∧ (hiM i).testBit (r.val - shM i) = true ∧ (loM i).testBit (shM i + r.val) = false) ∨
  ((keM i).testBit r.val = false ∧ (sig i r).val = shM i + r.val ∧ (decide (shM i ≤ r.val) && (hiM i).testBit (r.val - shM i)) = false ∧ (loM i).testBit (shM i + r.val) = true)
theorem swap_facts : ∀ (i : Fin 5) (r : Row), swapFacts i.val r ∧ sig i.val (sig i.val r) = r := by
  unfold swapFacts
  decide +kernel
theorem swap_ok (i : Nat) (hi : i < 5) (v : Nat) : W (swapN i v) = rename (sig i) (W v) := by
  apply bit_ext
  intro r
  rw [bit_W,bit_rename,bit_W]
  have e : (swapN i v).testBit r.val = (((v.testBit r.val && (keM i).testBit r.val) ||
      (decide (shM i ≤ r.val) && (v.testBit (r.val - shM i) && (hiM i).testBit (r.val - shM i)))) ||
      (v.testBit (shM i + r.val) && (loM i).testBit (shM i + r.val))) := by
    have s1 : (Nat.shiftLeft (Nat.land v (hiM i)) (shM i)).testBit r.val = (decide (shM i ≤ r.val) && (Nat.land v (hiM i)).testBit (r.val - shM i)) := by
      exact Nat.testBit_shiftLeft ..
    have s2 : (Nat.shiftRight (Nat.land v (loM i)) (shM i)).testBit r.val = (Nat.land v (loM i)).testBit (shM i + r.val) := by
      exact Nat.testBit_shiftRight ..
    unfold swapN
    rw [tb_lor,tb_lor,s1,s2,tb_land,tb_land,tb_land]
  rw [e]
  rcases (swap_facts ⟨i,hi⟩ r).1 with ⟨h1,h2,h3,h4⟩ | ⟨h1,h2,h3,h4,h5⟩ | ⟨h1,h2,h3,h4⟩
  · change (sig i r).val = r.val at h2
    rw [h2]
    simp only [] at h1 h3 h4
    rw [h1,h4]
    cases hd : decide (shM i ≤ r.val)
    · simp
    · rw [hd,Bool.true_and] at h3
      rw [h3]; simp
  · change (sig i r).val = r.val - shM i at h3
    rw [h3]
    simp only [] at h1 h2 h4 h5
    rw [h1,h4,h5,decide_eq_true h2]
    simp
  · change (sig i r).val = shM i + r.val at h2
    rw [h2]
    simp only [] at h1 h3 h4
    rw [h1,h4]
    cases hd : decide (shM i ≤ r.val)
    · simp
    · rw [hd,Bool.true_and] at h3
      rw [h3]; simp
def permN (l : List Nat) (v : Nat) : Nat := l.foldl (fun v i => swapN i v) v
def symOK (T : Nat) (l : List Nat) : Bool := l.all fun i => Nat.blt i 5 && Nat.beq (swapN i T) T
theorem perm_sound {u T k} (l : List Nat) (hT : symOK T l = true) (s : List Nat)
    (h : Impossible u (W T) k ((s.map (permN l)).map W).toFinset) : Impossible u (W T) k (s.map W).toFinset := by
  induction l generalizing s with
  | nil =>
    simpa [show (permN [] : Nat → Nat) = id from rfl] using h
  | cons i l ih =>
    simp only [symOK,List.all_cons,Bool.and_eq_true,Nat.blt_eq] at hT
    obtain ⟨⟨hi,hs⟩,hl⟩ := hT
    have h' : Impossible u (W T) k ((s.map (swapN i)).map W).toFinset := by
      apply ih hl
      have : (s.map (swapN i)).map (permN l) = s.map (permN (i::l)) := by
        rw [List.map_map]
        rfl
      rw [this]
      exact h
    intro k' hk run
    have onto : Function.Surjective (sig i) := fun r => ⟨sig i r,(swap_facts ⟨i,hi⟩ r).2⟩
    have r2 := live_rename run (sig i) onto
    rw [←swap_ok i hi T,Nat.eq_of_beq_eq_true hs] at r2
    apply h' k' hk
    have : ((s.map (swapN i)).map W).toFinset = (s.map W).toFinset.image (rename (sig i)) := by
      ext v
      simp only [List.mem_toFinset,List.mem_map,Finset.mem_image,exists_exists_and_eq_and,swap_ok i hi]
    rw [this]
    exact r2

abbrev StD := List Nat × List Nat × List Nat
def pick : List Nat → Nat → List Nat
  | [],_ => []
  | x::xs,m => bif Nat.beq (Nat.mod m 2) 1 then x :: pick xs (Nat.div m 2) else pick xs (Nat.div m 2)
def picks : List Nat → List (Nat × List Nat)
  | [] => []
  | x::xs => (x,xs) :: (picks xs).map fun p => (p.1,x::p.2)
def pairs : List Nat → List (Nat × Nat × List Nat)
  | [] => []
  | x::xs => ((picks xs).map fun p => (x,p.1,p.2)) ++ (pairs xs).map fun p => (p.1,p.2.1,x::p.2.2)
theorem picks_ok {l : List Nat} {a : Nat} (h : a ∈ l) : ∃ p ∈ picks l, p.1 = a ∧ (a::p.2).Perm l := by
  induction l with
  | nil => cases h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨(a,xs),by simp [picks],rfl,List.Perm.refl _⟩
    · obtain ⟨p,hp,rfl,q⟩ := ih h
      refine ⟨(p.1,x::p.2),?_,rfl,?_⟩
      · simp only [picks,List.mem_cons,List.mem_map]
        exact Or.inr ⟨p,hp,rfl⟩
      · exact (List.Perm.swap x p.1 p.2).trans (q.cons x)
theorem pairs_ok {l : List Nat} {a b : Nat} (ha : a ∈ l) (hb : b ∈ l) (hab : a ≠ b) :
    ∃ p ∈ pairs l, (p.1::p.2.1::p.2.2).Perm l ∧ ((p.1 = a ∧ p.2.1 = b) ∨ (p.1 = b ∧ p.2.1 = a)) := by
  induction l with
  | nil => cases ha
  | cons x xs ih =>
    have first (c : Nat) (hc : c ∈ xs) : ∃ p ∈ pairs (x::xs), (p.1::p.2.1::p.2.2).Perm (x::xs) ∧ p.1 = x ∧ p.2.1 = c := by
      obtain ⟨p,hp,rfl,q⟩ := picks_ok hc
      refine ⟨(x,p.1,p.2),?_,q.cons x,rfl,rfl⟩
      simp only [pairs,List.mem_append,List.mem_map]
      exact Or.inl ⟨p,hp,rfl⟩
    rcases List.mem_cons.mp ha with rfl | ha2
    · rcases List.mem_cons.mp hb with rfl | hb
      · exact absurd rfl hab
      · obtain ⟨p,h1,h2,h3,h4⟩ := first b hb
        exact ⟨p,h1,h2,Or.inl ⟨h3,h4⟩⟩
    · rcases List.mem_cons.mp hb with e | hb
      · subst e
        obtain ⟨p,h1,h2,h3,h4⟩ := first a ha2
        exact ⟨p,h1,h2,Or.inr ⟨h3,h4⟩⟩
      · obtain ⟨p,hp,q,e⟩ := ih ha2 hb
        refine ⟨(p.1,p.2.1,x::p.2.2),?_,?_,e⟩
        · simp only [pairs,List.mem_append,List.mem_map]
          exact Or.inr ⟨p,hp,rfl⟩
        · exact ((List.Perm.swap x p.2.1 p.2.2).cons p.1).trans ((List.Perm.swap x p.1 _).trans (q.cons x))

def mem1 (z : Nat) (l : List Nat) : Bool := l.any fun x => Nat.beq x z
def beqL : List Nat → List Nat → Bool
  | [],[] => true
  | x::xs,y::ys => Nat.beq x y && beqL xs ys
  | _,_ => false
theorem beqL_ok {a b : List Nat} (h : beqL a b = true) : a = b := by
  induction a generalizing b with
  | nil => cases b with
    | nil => rfl
    | cons => simp [beqL] at h
  | cons x xs ih => cases b with
    | nil => simp [beqL] at h
    | cons y ys =>
      simp only [beqL,Bool.and_eq_true] at h
      rw [Nat.eq_of_beq_eq_true h.1,ih h.2]
def ins (z : Nat) : List Nat → List Nat
  | [] => [z]
  | x::xs => bif Nat.ble z x then z::x::xs else x :: ins z xs
theorem mem_ins {z v : Nat} {l : List Nat} : v ∈ ins z l ↔ v = z ∨ v ∈ l := by
  induction l with
  | nil => simp [ins]
  | cons x xs ih =>
    unfold ins
    cases Nat.ble z x
    · simp only [cond_false,List.mem_cons,ih]
      tauto
    · simp
def kidN (rest : List Nat) (a b z : Nat) (ka kb : Bool) : List Nat :=
  ins z (bif ka then ins a (bif kb then ins b rest else rest) else bif kb then ins b rest else rest)
theorem kid_fin (rest : List Nat) (a b z : Nat) (ka kb : Bool) :
    ((kidN rest a b z ka kb).map W).toFinset = (kidW rest a b z ka kb).toFinset := by
  ext v
  cases ka <;> cases kb <;> simp [kidN,kidW,kept,mem_ins] <;> aesop

def keeps : List (Bool × Bool) := [(true,true),(true,false),(false,true),(false,false)]
def bl (b : Bool) : Nat := bif b then 1 else 0
def mkCut (u : Bool) (Z : List SliceD) (c : Nat × List Nat) : CutV :=
  let s := Z.getD c.1 (0,0,[])
  (s.1,s.2.1,c.2.length,mkPool u (initPool s.1 s.2.2) c.2)
abbrev Tabs := List CutV × List (Nat × Nat) × List KwD × List (List Nat)
def Tabs.cuts (t : Tabs) : List CutV := t.1
def Tabs.seps (t : Tabs) : List (Nat × Nat) := t.2.1
def Tabs.kws (t : Tabs) : List KwD := t.2.2.1
def Tabs.perms (t : Tabs) : List (List Nat) := t.2.2.2
def sortN (l : List Nat) : List Nat := l.foldr ins []
theorem mem_sortN {v : Nat} {l : List Nat} : v ∈ sortN l ↔ v ∈ l := by
  induction l with
  | nil => simp [sortN]
  | cons x xs ih =>
    change v ∈ ins x (sortN xs) ↔ _
    rw [mem_ins,ih]
    simp
def ty (i n : Nat) : Bool := Nat.beq (Nat.mod i 4) n
def hintOK (u : Bool) (k : Nat) (next : List (List Nat)) (t : Tabs) (rest : List Nat) (a b z : Nat) (ka kb : Bool) (i : Nat) : Bool :=
  bif ty i 0 then (match t.cuts[Nat.div i 4]? with
    | some c => cutEval u k rest a b z ka kb c
    | none => false)
  else bif ty i 1 then (match t.seps[Nat.div i 4]? with
    | some q => sepEval u rest a b z ka kb q
    | none => false)
  else bif ty i 2 then (match t.kws[Nat.div i 4]? with
    | some q => !u && Nat.beq (kidN rest a b z ka kb).length (k+1) && kwList (kidN rest a b z ka kb) q
    | none => false)
  else (match t.perms[Nat.div i 4]? with
    | some l => next.any (beqL (sortN ((kidN rest a b z ka kb).map (permN l))))
    | none => false)
def kidOK (u : Bool) (k : Nat) (next : List (List Nat)) (t : Tabs) (rest : List Nat) (hints : List Nat)
    (a b z : Nat) (kk : Bool × Bool) : Bool :=
  Nat.blt k (Nat.add (Nat.add rest.length (Nat.add (bl kk.1) (bl kk.2))) 0) ||
  hints.any (hintOK u k next t rest a b z kk.1 kk.2)
def opsOf (u : Bool) : List Nat := bif u then [0,1,2,3] else [0,1]
def pairOK (u : Bool) (k : Nat) (next : List (List Nat)) (t : Tabs) (s : List Nat)
    (p : Nat × Nat × List Nat) (hints : List Nat) : Bool :=
  (opsOf u).all fun o =>
    let z := nb o p.1 p.2.1
    mem1 z s || Nat.beq z 0 || Nat.beq z full ||
      keeps.all (kidOK u k next t p.2.2 hints p.1 p.2.1 z)
def allZip (f : Nat × Nat × List Nat → List Nat → Bool) : List (Nat × Nat × List Nat) → List (List Nat) → Bool
  | [],_ => true
  | p::ps,[] => f p [] && allZip f ps []
  | p::ps,h::hs => f p h && allZip f ps hs
theorem allZip_ok {f ps hs} (h : allZip f ps hs = true) : ∀ p ∈ ps, ∃ x, f p x = true := by
  induction ps generalizing hs with
  | nil => intro p hp; cases hp
  | cons q ps ih =>
    intro p hp
    cases hs with
    | nil =>
      simp only [allZip,Bool.and_eq_true] at h
      rcases List.mem_cons.mp hp with rfl | hp
      · exact ⟨_,h.1⟩
      · exact ih h.2 p hp
    | cons x hs =>
      simp only [allZip,Bool.and_eq_true] at h
      rcases List.mem_cons.mp hp with rfl | hp
      · exact ⟨_,h.1⟩
      · exact ih h.2 p hp
def asc : List Nat → Bool
  | [] => true
  | [x] => Nat.blt x (2^128)
  | x::y::l => Nat.blt x y && asc (y::l)
theorem asc_ok {l : List Nat} (h : asc l = true) : l.Pairwise (· < ·) ∧ ∀ x ∈ l, x < 2^128 := by
  induction l with
  | nil => simp
  | cons x l ih =>
    cases l with
    | nil =>
      simp only [asc,Nat.blt_eq] at h
      simpa using h
    | cons y l =>
      simp only [asc,Bool.and_eq_true,Nat.blt_eq] at h
      obtain ⟨i1,i2⟩ := ih h.2
      have hy := List.pairwise_cons.mp i1
      refine ⟨List.pairwise_cons.mpr ⟨?_,i1⟩,?_⟩
      · intro v hv
        rcases List.mem_cons.mp hv with rfl | hv
        · exact h.1
        · exact h.1.trans (hy.1 v hv)
      · intro v hv
        rcases List.mem_cons.mp hv with rfl | hv
        · exact h.1.trans (i2 y (by simp))
        · exact i2 v hv
theorem asc_nodup {l : List Nat} (h : asc l = true) : l.Nodup ∧ (l.map W).Nodup := by
  obtain ⟨h1,h2⟩ := asc_ok h
  have nd : l.Nodup := h1.imp (fun h => Nat.ne_of_lt h)
  refine ⟨nd,?_⟩
  refine nd.map_on ?_
  intro x hx y hy e
  exact W_inj (h2 x hx) (h2 y hy) e
def stOK (u : Bool) (T : Nat) (t : Tabs) (k : Nat) (next : List (List Nat)) (st : StD) : Bool :=
  asc st.1 && !(mem1 T st.1) &&
  allZip (pairOK u k next t st.1) (pairs st.1) (st.2.2.map (pick st.2.1))
def levelOK (u : Bool) (T : Nat) (t : Tabs) (k : Nat) (next : List (List Nat)) (D : List StD) : Bool :=
  D.all (stOK u T t k next)
abbrev TabsP (u : Bool) (R : List Nat) (T : Nat) (t : Tabs) : Prop :=
  (∀ c ∈ t.cuts, CutP u R T c) ∧ t.seps.all (sepOK T) = true ∧ t.kws.all (kwOK T) = true ∧ t.perms.all (symOK T) = true
theorem TabsP.c {u R T t} (h : TabsP u R T t) : ∀ c ∈ t.cuts, CutP u R T c := h.1
theorem TabsP.s {u R T t} (h : TabsP u R T t) : t.seps.all (sepOK T) = true := h.2.1
theorem TabsP.k {u R T t} (h : TabsP u R T t) : t.kws.all (kwOK T) = true := h.2.2.1
theorem TabsP.p {u R T t} (h : TabsP u R T t) : t.perms.all (symOK T) = true := h.2.2.2
def LevelN (u : Bool) (T k : Nat) (D : List StD) : Prop :=
  ∀ st ∈ D, Impossible u (W T) k (st.1.map W).toFinset
theorem cutsGood {u R T} {Z : List SliceD} {C : List (Nat × List Nat)} (hZ : ∀ s ∈ Z, SliceN u R T s)
    (hC : C.all (fun c => Nat.blt c.1 Z.length) = true) : ∀ c ∈ C.map (mkCut u Z), CutP u R T c := by
  intro c hc
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hc
  have hi : q.1 < Z.length := by simpa only [Nat.blt_eq] using List.all_eq_true.mp hC q hq
  have hm : Z.getD q.1 (0,0,[]) ∈ Z := by
    rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi]
    exact List.getElem_mem hi
  obtain ⟨⟨f,roots,dom,base,nc,lo⟩,hv⟩ := hZ _ hm
  have ps : PS u f (roots.map observe) (initPool (Z.getD q.1 (0,0,[])).1 (Z.getD q.1 (0,0,[])).2.2) := by
    intro v hv'
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hv'
    rw [rf_land dom]
    exact base _ (List.mem_map_of_mem (hv j hj))
  obtain ⟨bank,b1,b2⟩ := mkPool_ok q.2 (Reach.start (u:=u) (roots:=roots.map observe)) ps
  refine ⟨f,roots,bank,dom,nc,?_,b2,lo⟩
  simpa [mkCut] using b1

theorem stStep {u R T E t k next st} (hB : baseOK T R E = true) (ht : TabsP u R T t)
    (hn : ∀ s ∈ next, Impossible u (W T) k (s.map W).toFinset)
    (h : stOK u T t k next st = true) : Impossible u (W T) (k+1) (st.1.map W).toFinset := by
  have b := baseOK_ok hB
  simp only [stOK,Bool.and_eq_true,Bool.not_eq_true'] at h
  obtain ⟨⟨ha,hT⟩,hz⟩ := h
  obtain ⟨nd,ndW⟩ := asc_nodup ha
  have lt := (asc_ok ha).2
  have hTm : W T ∉ st.1.map W := by
    intro hm
    obtain ⟨x,hx,e⟩ := List.mem_map.mp hm
    have := W_inj (lt x hx) b.lt e
    subst this
    have : mem1 x st.1 = true := List.any_eq_true.mpr ⟨x,hx,Nat.beq_refl x⟩
    rw [hT] at this
    exact Bool.noConfusion this
  apply enum_step ndW hTm
  intro a' ha' b' hb' d hd ka kb hab fresh hprop hlen
  obtain ⟨a,ham,rfl⟩ := List.mem_map.mp ha'
  obtain ⟨c,hcm,rfl⟩ := List.mem_map.mp hb'
  have hac : a ≠ c := fun h => hab (by rw [h])
  have inOps : ∀ {o : Nat}, allowed u o → o ∈ opsOf u := by
    intro o h
    cases u
    · rcases h with h | ⟨h,_⟩
      · have : o = 0 ∨ o = 1 := by omega
        simpa [opsOf] using this
      · exact Bool.noConfusion h
    · have : o = 0 ∨ o = 1 ∨ o = 2 ∨ o = 3 := by rcases h with h | ⟨_,h⟩ <;> omega
      simpa [opsOf] using this
  have opk : ∀ {o : Nat}, allowed u o → opOK u o = true := by
    intro o h
    cases u
    · rcases h with h | ⟨h,_⟩
      · simpa only [opOK,Bool.false_or,Nat.blt_eq] using h
      · exact Bool.noConfusion h
    · rfl
  obtain ⟨p,hp,perm,ho⟩ := pairs_ok ham hcm hac
  obtain ⟨x,hx⟩ := allZip_ok hz p hp
  have core : ∀ (o : Nat) (ja jb : Bool), allowed u o → W (nb o p.1 p.2.1) = bin d (W a) (W c) →
      (p.2.2.length + (bl ja + bl jb) ≤ k) →
      Impossible u (W T) k (kidW p.2.2 p.1 p.2.1 (nb o p.1 p.2.1) ja jb).toFinset := by
    intro o ja jb ho4 hW hl
    have hf := List.all_eq_true.mp hx o (inOps ho4)
    simp only [Bool.or_eq_true] at hf
    have pm (v : Nat) : v ∈ st.1 ↔ v = p.1 ∨ v = p.2.1 ∨ v ∈ p.2.2 := by
      rw [←perm.mem_iff]
      simp
    rcases hf with ((hf | hf) | hf) | hf
    · exfalso
      obtain ⟨y,hy,e⟩ := List.any_eq_true.mp hf
      apply fresh
      rw [←hW,←Nat.eq_of_beq_eq_true e]
      exact List.mem_map_of_mem hy
    · exfalso
      apply hprop.1
      rw [←hW,Nat.eq_of_beq_eq_true hf]
      rfl
    · exfalso
      apply hprop.2
      rw [←hW,Nat.eq_of_beq_eq_true hf]
      exact W_full
    have hk := List.all_eq_true.mp hf (ja,jb) (by cases ja <;> cases jb <;> simp [keeps])
    simp only [kidOK,Bool.or_eq_true] at hk
    have ndp : ((p.1::p.2.1::p.2.2).map W).Nodup := (perm.map W).nodup_iff.mpr ndW
    simp only [List.map_cons,List.nodup_cons,List.mem_cons,not_or] at ndp
    have nk : (kidW p.2.2 p.1 p.2.1 (nb o p.1 p.2.1) ja jb).Nodup := by
      have n1 := kept_nd jb (W p.2.1) _ ndp.2.2 ndp.2.1
      have n2 : W p.1 ∉ kept jb (W p.2.1) (p.2.2.map W) := by
        cases jb
        · exact ndp.1.2
        · simp only [kept,if_true,List.mem_cons,not_or]
          exact ndp.1
      refine List.nodup_cons.mpr ⟨?_,kept_nd ja _ _ n1 n2⟩
      intro hm
      apply fresh
      rw [←hW]
      have sub : W (nb o p.1 p.2.1) ∈ (p.1::p.2.1::p.2.2).map W := by
        rcases mem_kept hm with h | h
        · rw [h]; simp
        · rcases mem_kept h with h | h
          · rw [h]; simp
          · simp [h]
      exact (perm.map W).mem_iff.mp sub
    rcases hk with hk | hk
    · exfalso
      rw [Nat.blt_eq] at hk
      have : k < p.2.2.length + (bl ja + bl jb) + 0 := hk
      omega
    · obtain ⟨i,_,hi⟩ := List.any_eq_true.mp hk
      unfold hintOK at hi
      have sub : ∀ x ∈ kidN p.2.2 p.1 p.2.1 (nb o p.1 p.2.1) ja jb, x < 2^128 := by
        intro x hx
        have hx' : x = nb o p.1 p.2.1 ∨ x ∈ st.1 := by
          unfold kidN at hx
          rw [mem_ins] at hx
          rcases hx with hx | hx
          · exact Or.inl hx
          · right
            rw [pm]
            cases ja <;> cases jb <;> simp only [cond_true,cond_false,mem_ins] at hx <;> tauto
        rcases hx' with rfl | hx'
        · have l1 : p.1 < 2^128 := lt _ ((pm _).mpr (Or.inl rfl))
          have l2 : p.2.1 < 2^128 := lt _ ((pm _).mpr (Or.inr (Or.inl rfl)))
          have la : Nat.land p.1 p.2.1 < 2^128 := Nat.lt_of_le_of_lt (Nat.and_le_left) l1
          unfold nb
          cases Nat.beq o 0 <;> cases Nat.beq o 1 <;> cases Nat.beq o 2 <;>
            first | exact la | exact Nat.or_lt_two_pow l1 l2 | exact Nat.xor_lt_two_pow l1 la | exact Nat.xor_lt_two_pow l2 la
        · exact lt x hx'
      cases h1 : ty i 0
      · rw [h1,cond_false] at hi
        cases h2 : ty i 1
        · rw [h2,cond_false] at hi
          cases h3 : ty i 2
          · rw [h3,cond_false] at hi
            cases hg : t.perms[Nat.div i 4]? with
            | none => rw [hg] at hi; exact Bool.noConfusion hi
            | some l =>
              rw [hg] at hi
              obtain ⟨s,hs',e⟩ := List.any_eq_true.mp hi
              rw [←kid_fin]
              apply perm_sound l (List.all_eq_true.mp ht.p l (List.mem_of_getElem? hg))
              have : (((kidN p.2.2 p.1 p.2.1 (nb o p.1 p.2.1) ja jb).map (permN l)).map W).toFinset = (s.map W).toFinset := by
                rw [←beqL_ok e]
                ext v
                simp only [List.mem_toFinset,List.mem_map,mem_sortN]
              rw [this]
              exact hn s hs'
          · rw [h3,cond_true] at hi
            cases hg : t.kws[Nat.div i 4]? with
            | none => rw [hg] at hi; exact Bool.noConfusion hi
            | some q =>
              rw [hg] at hi
              simp only [Bool.and_eq_true,Bool.not_eq_true'] at hi
              obtain ⟨⟨hu,hlen⟩,hkw⟩ := hi
              rw [←kid_fin]
              have sz := Nat.eq_of_beq_eq_true hlen
              have nd' : ((kidN p.2.2 p.1 p.2.1 (nb o p.1 p.2.1) ja jb).map W).Nodup := by
                apply List.dedup_eq_self.mp
                apply (List.dedup_sublist _).eq_of_length
                have c1 : ((kidN p.2.2 p.1 p.2.1 (nb o p.1 p.2.1) ja jb).map W).toFinset.card = (kidW p.2.2 p.1 p.2.1 (nb o p.1 p.2.1) ja jb).length := by
                  rw [kid_fin,List.toFinset_card_of_nodup nk]
                rw [List.card_toFinset] at c1
                rw [c1,List.length_map]
                have il : ∀ (z : Nat) (l : List Nat), (ins z l).length = l.length + 1 := by
                  intro z l
                  induction l with
                  | nil => rfl
                  | cons x xs ih =>
                    unfold ins
                    cases Nat.ble z x
                    · rw [cond_false,List.length_cons,ih,List.length_cons]
                    · rfl
                unfold kidN kidW
                cases ja <;> cases jb <;> simp [kept,il]
              subst hu
              exact kw_sound nd' sz sub q (List.all_eq_true.mp ht.k q (List.mem_of_getElem? hg)) hkw
        · rw [h2,cond_true] at hi
          cases hg : t.seps[Nat.div i 4]? with
          | none => rw [hg] at hi; exact Bool.noConfusion hi
          | some q =>
            rw [hg] at hi
            exact sep_sound (List.all_eq_true.mp ht.s q (List.mem_of_getElem? hg)) hi
      · rw [h1,cond_true] at hi
        cases hg : t.cuts[Nat.div i 4]? with
        | none => rw [hg] at hi; exact Bool.noConfusion hi
        | some q =>
          rw [hg] at hi
          exact cut_sound (ht.c q (List.mem_of_getElem? hg)) (opk ho4) nk hi
  have rp : (((st.1.map W).erase (W a)).erase (W c)).Perm (p.2.2.map W) := by
    have e : (W a :: W c :: p.2.2.map W).Perm (st.1.map W) := by
      rcases ho with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact perm.map W
      · exact (List.Perm.swap _ _ _).trans (perm.map W)
    have e1 := e.erase (W a)
    rw [List.erase_cons_head] at e1
    have e2 := e1.erase (W c)
    rw [List.erase_cons_head] at e2
    exact e2.symm
  have lenr : (((st.1.map W).erase (W a)).erase (W c)).length = p.2.2.length := by
    rw [rp.length_eq,List.length_map]
  have fits : p.2.2.length + (bl ka + bl kb) ≤ k := by
    have h := hlen
    unfold childTwo at h
    cases ka <;> cases kb <;> simp [kept,lenr] at h <;> simp [bl] <;> omega
  rw [Nat.add_sub_cancel]
  rcases ho with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · have r := core d ka kb hd (W_nb _ _ _) fits
    have e : (childTwo (st.1.map W) (W p.1) (W p.2.1) d ka kb).toFinset = (kidW p.2.2 p.1 p.2.1 (nb d p.1 p.2.1) ka kb).toFinset := by
      unfold childTwo kidW
      rw [W_nb]
      ext v
      cases ka <;> cases kb <;> simp [kept,rp.mem_iff]
    rw [e]
    exact r
  · have hfl := flip_flip hd
    have r := core (flipOp d) kb ka hfl.1 (by rw [W_nb]; exact (bin_flip hd _ _).symm) (by omega)
    have e : (childTwo (st.1.map W) (W p.2.1) (W p.1) d ka kb).toFinset = (kidW p.2.2 p.1 p.2.1 (nb (flipOp d) p.1 p.2.1) kb ka).toFinset := by
      unfold childTwo kidW
      rw [W_nb,bin_flip hd]
      ext v
      cases ka <;> cases kb <;> simp [kept,rp.mem_iff] <;> tauto
    rw [e]
    exact r

theorem levelStep {u R T E t k D' D} (hB : baseOK T R E = true) (ht : TabsP u R T t)
    (hI : LevelN u T k D') (h : levelOK u T t k (D'.map Prod.fst) D = true) : LevelN u T (k+1) D := by
  intro st hst
  refine stStep hB ht ?_ (List.all_eq_true.mp h st hst)
  intro s hs
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hs
  exact hI q hq
theorem chunks {u : Bool} {T : Nat} {t : Tabs} {k : Nat} {next : List (List Nat)} (c : Nat) (D : List StD) (n : Nat) (hc : 0 < c)
    (hl : Nat.ble D.length (n*c) = true)
    (h : ∀ i, i < n → levelOK u T t k next ((D.drop (i*c)).take c) = true) : levelOK u T t k next D = true := by
  rw [levelOK,List.all_eq_true]
  intro x hx
  obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem hx
  have hl' := Nat.le_of_ble_eq_true hl
  have hi : j / c < n := by
    rw [Nat.div_lt_iff_lt_mul hc]
    omega
  refine List.all_eq_true.mp (h _ hi) _ ?_
  have hm : j / c * c + j % c = j := by rw [Nat.mul_comm]; exact Nat.div_add_mod j c
  have hmod := Nat.mod_lt j hc
  refine List.mem_of_getElem? (i := j % c) ?_
  rw [List.getElem?_take_of_lt hmod,List.getElem?_drop,hm]
  exact List.getElem?_eq_getElem hj
theorem lowSearch {u R T E K D} (hB : baseOK T R E = true) (hI : LevelN u T K D)
    (h : (D.map Prod.fst).contains (R.map xN) = true) : LowN u R T (K+1) := by
  apply lowOf hB
  simp only [List.contains_eq_mem,decide_eq_true_eq] at h
  obtain ⟨q,hq,e⟩ := List.mem_map.mp h
  have := hI q hq
  rw [e] at this
  simpa only [rootsW,List.map_map,Function.comp_def] using this

def target (x : Fin 6 → Bool) : Bool := Nat.testBit (4277075688 * 2 ^ 32 + 4276807904) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def smallCircuit : Circuit := ⟨[
    ⟨.and, [0, 1]⟩,
    ⟨.or, [0, 1]⟩,
    ⟨.and, [2, 3]⟩,
    ⟨.and, [3, 5]⟩,
    ⟨.or, [3, 5]⟩,
    ⟨.or, [4, 9]⟩,
    ⟨.or, [6, 11]⟩,
    ⟨.or, [0, 8]⟩,
    ⟨.and, [10, 12]⟩,
    ⟨.or, [2, 14]⟩,
    ⟨.and, [7, 15]⟩,
    ⟨.and, [11, 13]⟩,
    ⟨.or, [16, 17]⟩], 18⟩
theorem witnessMonotone : PEqualNP.MetaComplexity.Monotone2 smallCircuit := by
  intro g hg
  simp only [smallCircuit,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ⟨Or.inl rfl,by decide⟩ | exact ⟨Or.inr rfl,by decide⟩
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem witnessCorrect : ∀ x : Fin 6 → Bool, smallCircuit.eval (List.ofFn x) = target x := by
  decide +kernel
theorem witnessSize : smallCircuit.size = 13 := rfl
def pw0 : Nat := 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
def pw1 : Nat := 0xcccccccccccccccccccccccccccccccc
def pw2 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
def pw3 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff00
def pw4 : Nat := 0xffff0000ffff0000ffff0000ffff0000
def pw5 : Nat := 0xffffffff00000000ffffffff00000000
def pw6 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff
def pw7 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def pw8 : Nat := 0x33333333333333333333333333333333
def pw9 : Nat := 0x55555555555555555555555555555555
def pw10 : Nat := 0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc
def pw11 : Nat := 0xffccffccffccffccffccffccffccffcc
def pw12 : Nat := 0xfff0fff0fff0fff0fff0fff0fff0fff0
def pw13 : Nat := 0xfe00fe00fe00fe00fe00fe00fe00fe
def pw14 : Nat := 0xffaaffaaffaaffaaffaaffaaffaaffaa
def pw15 : Nat := 0xfefefefefefefefefefefefefefefefe
def pw16 : Nat := 0xee00ee00ee00ee00ee00ee00ee00ee
def pw17 : Nat := 0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee
def pw18 : Nat := 0x2aaa2aaa2aaa2aaa2aaa2aaa2aaa2aaa
def pw19 : Nat := 0x88888888888888888888888888888888
def pw20 : Nat := 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0
def pw21 : Nat := 0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0
def pw22 : Nat := 0x80808080808080808080808080808080
def pw23 : Nat := 0xaaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa
def pw24 : Nat := 0xffff0000ffff0000ffff0000ffff
def pw25 : Nat := 0xff000000ff000000ff000000ff00
def pw26 : Nat := 0xff000000ff000000ff000000ff0000
def pw27 : Nat := 0xf0f00000f0f00000f0f00000f0f0000
def pw28 : Nat := 0x33330000333300003333000033330000
def pw29 : Nat := 0x55550000555500005555000055550000
def pw30 : Nat := 0xf000f000f000f000f000f000f000f00
def pw31 : Nat := 0x33003300330033003300330033003300
def pw32 : Nat := 0x55005500550055005500550055005500
def pw33 : Nat := 0x50505050505050505050505050505050
def pw34 : Nat := 0x44444444444444444444444444444444
def pw35 : Nat := 0xfce8e8e8fce8e8e8fce8e8e8fce8e8e8
def pw36 : Nat := 0xfafafafafafafafafafafafafafafafa
def pw37 : Nat := 0xfca8a8a8fca8a8a8fca8a8a8fca8a8a8
def pw38 : Nat := 0xfe0e0e0efe0e0e0efe0e0e0efe0e0e0e
def pw39 : Nat := 0xfefefe00fefefe00fefefe00fefefe
def pw40 : Nat := 0xffffff00ffffff00ffffff00ffffff00
def pw41 : Nat := 0xe0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e
def pw42 : Nat := 0xfaaaaaaafaaaaaaafaaaaaaafaaaaaaa
def pw43 : Nat := 0xee00ee00ee00ee00ee00ee00ee00ee00
def pw44 : Nat := 0xeeee0000eeee0000eeee0000eeee0000
def pw45 : Nat := 0xffaaaaaaffaaaaaaffaaaaaaffaaaaaa
def pw46 : Nat := 0xeeeeee00eeeeee00eeeeee00eeeeee
def pw47 : Nat := 0xfaaafaaafaaafaaafaaafaaafaaafaaa
def pw48 : Nat := 0xfcf8f8f8fcf8f8f8fcf8f8f8fcf8f8f8
def pw49 : Nat := 0xf0e0e0e0f0e0e0e0f0e0e0e0f0e0e0e
def pw50 : Nat := 0xff000000ff000000ff000000ff000000
def pw51 : Nat := 0xd5c0c0c0d5c0c0c0d5c0c0c0d5c0c0c0
def pw52 : Nat := 0xffc0c0c0ffc0c0c0ffc0c0c0ffc0c0c0
def pw53 : Nat := 0xeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaea
def pw54 : Nat := 0xffeaeaeaffeaeaeaffeaeaeaffeaeaea
def pw55 : Nat := 0xeaeaea00eaeaea00eaeaea00eaeaea
def pw56 : Nat := 0xff3c3c3cff3c3c3cff3c3c3cff3c3c3c
def pw57 : Nat := 0x3c3c3c003c3c3c003c3c3c003c3c3c
def pw58 : Nat := 0xfeaaaaaafeaaaaaafeaaaaaafeaaaaaa
def pw59 : Nat := 0xfcc0c0c0fcc0c0c0fcc0c0c0fcc0c0c0
def pw60 : Nat := 0xfc00fc00fc00fc00fc00fc00fc00fc00
def pw61 : Nat := 0x55404040554040405540404055404040
def pw62 : Nat := 0x55545454555454545554545455545454
def pw63 : Nat := 0x1e1e5a5a1e1e5a5a1e1e5a5a1e1e5a5a
def pw64 : Nat := 0xc888c888c888c888c888c888c888c888
def pw65 : Nat := 0xfeee0000feee0000feee0000feee0000
def pw66 : Nat := 0xeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaa
def pw67 : Nat := 0xfafaaaaafafaaaaafafaaaaafafaaaaa
def pw68 : Nat := 0xfeeefaaafeeefaaafeeefaaafeeefaaa
def pw69 : Nat := 0x54445000544450005444500054445000
def pw70 : Nat := 0xfcecececfcecececfcecececfcececec
def pw71 : Nat := 0xfffafafafffafafafffafafafffafafa
def pw72 : Nat := 0xf5a5a5a0f5a5a5a0f5a5a5a0f5a5a5a
def pw73 : Nat := 0xcc888888cc888888cc888888cc888888
def pw74 : Nat := 0xf0e0e0e0f0e0e0e0f0e0e0e0f0e0e0e0
def pw75 : Nat := 0xcccccc00cccccc00cccccc00cccccc
def pw76 : Nat := 0xfcfcfc00fcfcfc00fcfcfc00fcfcfc
def pw77 : Nat := 0xff303030ff303030ff303030ff303030
def pw78 : Nat := 0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c
def pw79 : Nat := 0xc0ccccc0c0ccccc0c0ccccc0c0ccccc
def pw80 : Nat := 0x32323232323232323232323232323232
def pw81 : Nat := 0x1f00ff001f00ff001f00ff001f00ff00
def pw82 : Nat := 0xc8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8
def pw83 : Nat := 0xcc00cc00cc00cc00cc00cc00cc00cc00
def pw84 : Nat := 0xfa00fa00fa00fa00fa00fa00fa00fa00
def pw85 : Nat := 0x404cccc0404cccc0404cccc0404cccc
def pw86 : Nat := 0xf000f000f000f000f000f000f000f000
def pw87 : Nat := 0xf0000000f0000000f0000000f0000000
def pw88 : Nat := 0xf00ff000f00ff000f00ff000f00ff00
def pw89 : Nat := 0xff0e0e0eff0e0e0eff0e0e0eff0e0e0e
def pw90 : Nat := 0x4cccccc04cccccc04cccccc04cccccc
def pw91 : Nat := 0xfcf0fcf0fcf0fcf0fcf0fcf0fcf0fcf0
def pw92 : Nat := 0xe0a0e0a0e0a0e0a0e0a0e0a0e0a0e0a
def pw93 : Nat := 0xe0eeeee0e0eeeee0e0eeeee0e0eeeee
def pw94 : Nat := 0xeeaaaaaaeeaaaaaaeeaaaaaaeeaaaaaa
def pw95 : Nat := 0xeeeeeee0eeeeeee0eeeeeee0eeeeeee
def pw96 : Nat := 0xfff0f0f0fff0f0f0fff0f0f0fff0f0f0
def pw97 : Nat := 0xf0a0a0a0f0a0a0a0f0a0a0a0f0a0a0a
def pw98 : Nat := 0xee0e0e0eee0e0e0eee0e0e0eee0e0e0e
def pw99 : Nat := 0xdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdc
def pw100 : Nat := 0xdcdcdc00dcdcdc00dcdcdc00dcdcdc
def pw101 : Nat := 0xd0cddcc0d0cddcc0d0cddcc0d0cddcc
def pw102 : Nat := 0x55000000550000005500000055000000
def pw103 : Nat := 0xa8fcfcfca8fcfcfca8fcfcfca8fcfcfc
def pw104 : Nat := 0x54545454545454545454545454545454
def pw105 : Nat := 0x5d0c0c0c5d0c0c0c5d0c0c0c5d0c0c0c
def pw106 : Nat := 0xaa00ff00aa00ff00aa00ff00aa00ff00
def pw107 : Nat := 0xff0c0c0cff0c0c0cff0c0c0cff0c0c0c
def pw108 : Nat := 0xea00ea00ea00ea00ea00ea00ea00ea00
def pw109 : Nat := 0x15001500150015001500150015001500
def pw110 : Nat := 0x3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c
def pw111 : Nat := 0xbebebebebebebebebebebebebebebebe
def pw112 : Nat := 0x14141414141414141414141414141414
def pw113 : Nat := 0x3c003c003c003c003c003c003c003c00
def pw114 : Nat := 0xc300c300c300c300c300c300c300c300
def pw115 : Nat := 0xfc000000fc000000fc000000fc000000
def pw116 : Nat := 0x300ff000300ff000300ff000300ff00
def pw117 : Nat := 0x3f2a2a2a3f2a2a2a3f2a2a2a3f2a2a2a
def pw118 : Nat := 0x545454005454540054545400545454
def pw119 : Nat := 0xfcfc0000fcfc0000fcfc0000fcfc0000
def pw120 : Nat := 0xffccccccffccccccffccccccffcccccc
def pw121 : Nat := 0xf0f0f000f0f0f000f0f0f000f0f0f0
def pw122 : Nat := 0xaaeeeeeeaaeeeeeeaaeeeeeeaaeeeeee
def pw123 : Nat := 0xfc0c0c0cfc0c0c0cfc0c0c0cfc0c0c0c
def pw124 : Nat := 0xaafefefeaafefefeaafefefeaafefefe
def pw125 : Nat := 0xaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeae
def pw126 : Nat := 0xffaeaeaeffaeaeaeffaeaeaeffaeaeae
def pw127 : Nat := 0x55040404550404045504040455040404
def pw128 : Nat := 0xcf8a8a8acf8a8a8acf8a8a8acf8a8a8a
def pw129 : Nat := 0x54445444544454445444544454445444
def pw130 : Nat := 0xaeaeeeeeaeaeeeeeaeaeeeeeaeaeeeee
def pw131 : Nat := 0x32322222323222223232222232322222
def pw132 : Nat := 0x1f005f001f005f001f005f001f005f00
def pw133 : Nat := 0xeeeeaaaaeeeeaaaaeeeeaaaaeeeeaaaa
def pw134 : Nat := 0xfeeefeeefeeefeeefeeefeeefeeefeee
def pw135 : Nat := 0xfefa0000fefa0000fefa0000fefa0000
def pw136 : Nat := 0x4044444040444440404444404044444
def pw137 : Nat := 0x5005500050055000500550005005500
def pw138 : Nat := 0xe0aeeaa0e0aeeaa0e0aeeaa0e0aeeaa
def pw139 : Nat := 0xafaaafaaafaaafaaafaaafaaafaaafaa
def pw140 : Nat := 0xc8888888c8888888c8888888c8888888
def pw141 : Nat := 0xfefafafafefafafafefafafafefafafa
def pw142 : Nat := 0xe0a0a0a0e0a0a0a0e0a0a0a0e0a0a0a
def pw143 : Nat := 0x4444444044444440444444404444444
def pw144 : Nat := 0xfcccf000fcccf000fcccf000fcccf000
def pw145 : Nat := 0x55444444554444445544444455444444
def pw146 : Nat := 0x33222222332222223322222233222222
def pw147 : Nat := 0xc4c4c4c0c4c4c4c0c4c4c4c0c4c4c4c
def pw148 : Nat := 0xffeeeeeeffeeeeeeffeeeeeeffeeeeee
def pw149 : Nat := 0xccc8c8c8ccc8c8c8ccc8c8c8ccc8c8c8
def pw150 : Nat := 0x444444004444440044444400444444
def pw151 : Nat := 0x33303030333030303330303033303030
def pw152 : Nat := 0xccfcfcfcccfcfcfcccfcfcfcccfcfcfc
def pw153 : Nat := 0xc800c800c800c800c800c800c800c800
def pw154 : Nat := 0x1f001f001f001f001f001f001f001f00
def pw155 : Nat := 0xe0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0
def pw156 : Nat := 0xfe00fe00fe00fe00fe00fe00fe00fe00
def pw157 : Nat := 0xcd00cd00cd00cd00cd00cd00cd00cd00
def pw158 : Nat := 0xee000000ee000000ee000000ee000000
def pw159 : Nat := 0x500ff000500ff000500ff000500ff00
def pw160 : Nat := 0xf0f00000f0f00000f0f00000f0f00000
def pw161 : Nat := 0xfefafefafefafefafefafefafefafefa
def pw162 : Nat := 0xcc000000cc000000cc000000cc000000
def pw163 : Nat := 0xc8c8fafac8c8fafac8c8fafac8c8fafa
def pw164 : Nat := 0xcc00ff00cc00ff00cc00ff00cc00ff00
def pw165 : Nat := 0x40404040404040404040404040404040
def pw166 : Nat := 0xdc50dc50dc50dc50dc50dc50dc50dc50
def pw167 : Nat := 0xfcccfcccfcccfcccfcccfcccfcccfccc
def pw168 : Nat := 0xf000ff00f000ff00f000ff00f000ff00
def pw169 : Nat := 0xff444444ff444444ff444444ff444444
def pw170 : Nat := 0xf5f5f0f0f5f5f0f0f5f5f0f0f5f5f0f0
def pw171 : Nat := 0xddddccccddddccccddddccccddddcccc
def pw172 : Nat := 0xcccc0000cccc0000cccc0000cccc0000
def pw173 : Nat := 0xeaaaeaaaeaaaeaaaeaaaeaaaeaaaeaaa
def pw174 : Nat := 0x3f00ff003f00ff003f00ff003f00ff00
def pw175 : Nat := 0xfeaafeaafeaafeaafeaafeaafeaafeaa
def pw176 : Nat := 0xfffcfcfcfffcfcfcfffcfcfcfffcfcfc
def pw177 : Nat := 0xee00aa00ee00aa00ee00aa00ee00aa00
def pw178 : Nat := 0xfcf0f0f0fcf0f0f0fcf0f0f0fcf0f0f0
def pw179 : Nat := 0xccccccc0ccccccc0ccccccc0ccccccc
def pw180 : Nat := 0xbbbbaaaabbbbaaaabbbbaaaabbbbaaaa
def pw181 : Nat := 0xeaeaeeeeeaeaeeeeeaeaeeeeeaeaeeee
def pw182 : Nat := 0xf0c0c0c0f0c0c0c0f0c0c0c0f0c0c0c
def pw183 : Nat := 0x4040404040404040404040404040404
def pw184 : Nat := 0x5000500050005000500050005000500
def pw185 : Nat := 0x8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c
def pw186 : Nat := 0x44004400440044004400440044004400
def pw187 : Nat := 0xaf00af00af00af00af00af00af00af00
def pw188 : Nat := 0xddccddccddccddccddccddccddccddcc
def pw189 : Nat := 0x8888cccc8888cccc8888cccc8888cccc
def pw190 : Nat := 0xc000c000c000c000c000c000c000c000
def pw191 : Nat := 0x3f003f003f003f003f003f003f003f00
def pw192 : Nat := 0x3000300030003000300030003000300
def pw193 : Nat := 0xc000c000c000c000c000c000c000c00
def pw194 : Nat := 0xcf00cf00cf00cf00cf00cf00cf00cf00
def pw195 : Nat := 0x30303030303030303030303030303030
def pw196 : Nat := 0xcfcccfcccfcccfcccfcccfcccfcccfcc
def pw197 : Nat := 0xc0c0ccccc0c0ccccc0c0ccccc0c0cccc
def pw198 : Nat := 0xf0000000f0000000f0000000f000000
def pw199 : Nat := 0xeecceecceecceecceecceecceecceecc
def pw200 : Nat := 0x3f3f00003f3f00003f3f00003f3f0000
def pw201 : Nat := 0x1f3f00001f3f00001f3f00001f3f0000
def pw202 : Nat := 0xfefc0000fefc0000fefc0000fefc0000
def pw203 : Nat := 0x55ff000055ff000055ff000055ff0000
def pw204 : Nat := 0xfefcaa00fefcaa00fefcaa00fefcaa00
def pw205 : Nat := 0x33223322332233223322332233223322
def pw206 : Nat := 0xffaa0000ffaa0000ffaa0000ffaa0000
def pw207 : Nat := 0xffeac0c0ffeac0c0ffeac0c0ffeac0c0
def pw208 : Nat := 0x302ffaa0302ffaa0302ffaa0302ffaa
def pw209 : Nat := 0x54fcfc0054fcfc0054fcfc0054fcfc
def pw210 : Nat := 0xf0e0c0c0f0e0c0c0f0e0c0c0f0e0c0c0
def pw211 : Nat := 0xf0e0c0c0f0e0c0c0f0e0c0c0f0e0c0c
def pw212 : Nat := 0x15ff000015ff000015ff000015ff0000
def pw213 : Nat := 0xffea0000ffea0000ffea0000ffea0000
def pw214 : Nat := 0xfe00aa00fe00aa00fe00aa00fe00aa00
def pw215 : Nat := 0xfe00aa00fe00aa00fe00aa00fe00aa
def pw216 : Nat := 0xbbaabbaabbaabbaabbaabbaabbaabbaa
def pw217 : Nat := 0xeee0eee0eee0eee0eee0eee0eee0eee
def pw218 : Nat := 0x73507350735073507350735073507350
def pw219 : Nat := 0xe0c0e0c0e0c0e0c0e0c0e0c0e0c0e0c0
def pw220 : Nat := 0xfefcfefcfefcfefcfefcfefcfefcfefc
def pw221 : Nat := 0xe0c0e0c0e0c0e0c0e0c0e0c0e0c0e0c
def pw222 : Nat := 0x10301030103010301030103010301030
def pw223 : Nat := 0xeac0eac0eac0eac0eac0eac0eac0eac0
def pw224 : Nat := 0xaa00aa00aa00aa00aa00aa00aa00aa00
def pw225 : Nat := 0x54fc54fc54fc54fc54fc54fc54fc54fc
def pw226 : Nat := 0xae0cae0cae0cae0cae0cae0cae0cae0c
def pw227 : Nat := 0x3f2a3f2a3f2a3f2a3f2a3f2a3f2a3f2a
def pw228 : Nat := 0xfca8fca8fca8fca8fca8fca8fca8fca8
def pw229 : Nat := 0xf3a2f3a2f3a2f3a2f3a2f3a2f3a2f3a2
def pw230 : Nat := 0xffeeccccffeeccccffeeccccffeecccc
def pw231 : Nat := 0x44cccc0044cccc0044cccc0044cccc
def pw232 : Nat := 0xfffaf0f0fffaf0f0fffaf0f0fffaf0f0
def pw233 : Nat := 0x50f0f00050f0f00050f0f00050f0f0
def pw234 : Nat := 0xc0eac0eac0eac0eac0eac0eac0eac0ea
def pw235 : Nat := 0xaa00aa00aa00aa00aa00aa00aa00aa
def pw236 : Nat := 0xfc54fc54fc54fc54fc54fc54fc54fc54
def pw237 : Nat := 0xcae0cae0cae0cae0cae0cae0cae0cae
def pw238 : Nat := 0xffeaffeaffeaffeaffeaffeaffeaffea
def pw239 : Nat := 0xea00ea00ea00ea00ea00ea00ea00ea
def pw240 : Nat := 0xfefeaaaafefeaaaafefeaaaafefeaaaa
def pw241 : Nat := 0x202aaaa0202aaaa0202aaaa0202aaaa
def pw242 : Nat := 0xfffcff00fffcff00fffcff00fffcff00
def pw243 : Nat := 0x32223222322232223222322232223222
def pw244 : Nat := 0xf8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8
def pw245 : Nat := 0x70707070707070707070707070707070
def pw246 : Nat := 0xff88ff88ff88ff88ff88ff88ff88ff88
def pw247 : Nat := 0x77007700770077007700770077007700
def pw248 : Nat := 0x77770000777700007777000077770000
def pw249 : Nat := 0x10101010101010101010101010101010
def pw250 : Nat := 0x11001100110011001100110011001100
def pw251 : Nat := 0xecececececececececececececececec
def pw252 : Nat := 0xf5f50000f5f50000f5f50000f5f50000
def pw253 : Nat := 0x44cc44cc44cc44cc44cc44cc44cc44cc
def pw254 : Nat := 0xfaf0faf0faf0faf0faf0faf0faf0faf0
def pw255 : Nat := 0x50f050f050f050f050f050f050f050f0
def pw256 : Nat := 0xcceecceecceecceecceecceecceeccee
def pw257 : Nat := 0x2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a
def pw258 : Nat := 0xffc0ffc0ffc0ffc0ffc0ffc0ffc0ffc0
def pw259 : Nat := 0xff330000ff330000ff330000ff330000
def pw260 : Nat := 0xfff00000fff00000fff00000fff00000
def pw261 : Nat := 0xccfcccfcccfcccfcccfcccfcccfcccfc
def pw262 : Nat := 0x22222222222222222222222222222222
def pw263 : Nat := 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a
def pw264 : Nat := 0xcc00cc00cc00cc00cc00cc00cc00cc
def pw265 : Nat := 0xf000f000f000f000f000f000f000f0
def pw266 : Nat := 0xffffffff00000000ffffffff
def pw267 : Nat := 0xffff000000000000ffff00000000
def pw268 : Nat := 0xff00ff0000000000ff00ff00
def pw269 : Nat := 0xf0f00000f0f00000f0f00000f0f
def pw270 : Nat := 0xffff000000000000ffff0000
def pw271 : Nat := 0xff00ff0000000000ff00ff00000000
def pw272 : Nat := 0xf0f0f0f000000000f0f0f0f
def pw273 : Nat := 0xf0f0f0f000000000f0f0f0f00000000
def pw274 : Nat := 0x333333330000000033333333
def pw275 : Nat := 0xcccccccc00000000cccccccc
def pw276 : Nat := 0x33333333000000003333333300000000
def pw277 : Nat := 0x555555550000000055555555
def pw278 : Nat := 0x55555555000000005555555500000000
def pw279 : Nat := 0xff000000ff000000ff000000ff
def pw280 : Nat := 0x3333000033330000333300003333
def pw281 : Nat := 0x5555000055550000555500005555
def pw282 : Nat := 0xaaaa0000aaaa0000aaaa0000aaaa
def pw283 : Nat := 0xf000f000f000f000f000f000f000f
def pw284 : Nat := 0x5050505050505050505050505050505
def pw285 : Nat := 0xff00ff0000000000ff00ff
def pw286 : Nat := 0xff00000000000000ff00000000
def pw287 : Nat := 0xf0f0000000000000f0f00000000
def pw288 : Nat := 0x3333000000000000333300000000
def pw289 : Nat := 0x555500000000000055550000
def pw290 : Nat := 0x5555000000000000555500000000
def pw291 : Nat := 0xf000f00000000000f000f00
def pw292 : Nat := 0xf000f00000000000f000f00000000
def pw293 : Nat := 0x330033000000000033003300
def pw294 : Nat := 0x550055000000000055005500
def pw295 : Nat := 0xc0c0c0c000000000c0c0c0c
def pw296 : Nat := 0xf0000000f0000000f0000000f00
def pw297 : Nat := 0x3300000033000000330000003300
def pw298 : Nat := 0x5500000055000000550000005500
def pw299 : Nat := 0xa0a00000a0a00000a0a00000a0a
def pw300 : Nat := 0xc000c000c000c000c000c000c000c
def pw301 : Nat := 0x56565656565a565a56565656565a565a
def pw302 : Nat := 0xfffffafafffffafafffffafafffffafa
def pw303 : Nat := 0xfafa0000fafa0000fafa0000fafa
def pw304 : Nat := 0xfffffcf0fffffcf0fffffcf0fffffcf0
def pw305 : Nat := 0xffffcc00ffffcc00ffffcc00ffffcc00
def pw306 : Nat := 0xfffff0f0fffff0f0fffff0f0fffff0f0
def pw307 : Nat := 0x22aa22aa22aa22aa22aa22aa22aa22aa
def pw308 : Nat := 0x32fa32fa32fa32fa32fa32fa32fa32fa
def pw309 : Nat := 0xa8a8a8a8a8a0a8a0a8a8a8a8a8a0a8a0
def pw310 : Nat := 0xfcfcfcfcfcf0fcf0fcfcfcfcfcf0fcf0
def pw311 : Nat := 0x54545454545054505454545454505450
def pw312 : Nat := 0xffff0a0affff0a0affff0a0affff0a0a
def pw313 : Nat := 0xfefe0000feaa0000fefe0000feaa
def pw314 : Nat := 0xfcfcfcfcfc00fc00fcfcfcfcfc00fc00
def pw315 : Nat := 0xffffaaaaffffaaaaffffaaaaffffaaaa
def pw316 : Nat := 0xf0f0fafaf0f0fafaf0f0fafaf0f0fafa
def pw317 : Nat := 0xffff0e0affff0e0affff0e0affff0e0a
def pw318 : Nat := 0xe0a00000e0a00000e0a00000e0a
def pw319 : Nat := 0xffffeeaaffffeeaaffffeeaaffffeeaa
def pw320 : Nat := 0xf0f0e0a0f0f0e0a0f0f0e0a0f0f0e0a
def pw321 : Nat := 0xfffff2fafffff2fafffff2fafffff2fa
def pw322 : Nat := 0xffff22aaffff22aaffff22aaffff22aa
def pw323 : Nat := 0xfefa0000fefa0000fefa0000fefa
def pw324 : Nat := 0xffff020affff020affff020affff020a
def pw325 : Nat := 0xffffa8a8ffffa8a0ffffa8a8ffffa8a0
def pw326 : Nat := 0xfefefefefefafefafefefefefefafefa
def pw327 : Nat := 0xfefe0000fefa0000fefe0000fefa
def pw328 : Nat := 0x2020202020a020a02020202020a020a
def pw329 : Nat := 0x7000700070007000700070007000700
def pw330 : Nat := 0xfffffffff0f0f0f0fffffffff0f0f0f0
def pw331 : Nat := 0xfffff8f8fffff8f8fffff8f8fffff8f8
def pw332 : Nat := 0x7070707070007000707070707000700
def pw333 : Nat := 0xff88ff88f888f888ff88ff88f888f888
def pw334 : Nat := 0xf4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4
def pw335 : Nat := 0xffffffffff00ff00ffffffffff00ff00
def pw336 : Nat := 0x37003700370037003700370037003700
def pw337 : Nat := 0x37373737370037003737373737003700
def pw338 : Nat := 0xfffffefafffffefafffffefafffffefa
def pw339 : Nat := 0xffff32faffff32faffff32faffff32fa
def pw340 : Nat := 0x5fa05fa05fa05fa05fa05fa05fa05fa
def pw341 : Nat := 0xce0ace0ace0ace0ace0ace0ace0ace0a
def pw342 : Nat := 0xffffce0affffce0affffce0affffce0a
def pw343 : Nat := 0xce0a0000ce0a0000ce0a0000ce0a
def pw344 : Nat := 0xeecceecceac0eac0eecceecceac0eac0
def pw345 : Nat := 0xf0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a
def pw346 : Nat := 0xfefefefefeaafeaafefefefefeaafeaa
def pw347 : Nat := 0x202020202aa02aa0202020202aa02aa
def pw348 : Nat := 0xbabababababababababababababababa
def pw349 : Nat := 0xcccccccccc00cc00cccccccccc00cc00
def pw350 : Nat := 0xeeaa0000eeaa0000eeaa0000eeaa
def pw351 : Nat := 0xf2faf2faf2faf2faf2faf2faf2faf2fa
def pw352 : Nat := 0x20a020a020a020a020a020a020a020a
def pw353 : Nat := 0x55555555505050505555555550505050
def pw354 : Nat := 0xf0f0f0f0f000f000f0f0f0f0f000f00
def pw355 : Nat := 0xaeaeaeaeaeaaaeaaaeaeaeaeaeaaaeaa
def pw356 : Nat := 0xfff8fff8fff8fff8fff8fff8fff8fff8
def pw357 : Nat := 0xfffffffff8f8f8f8fffffffff8f8f8f8
def pw358 : Nat := 0xf7f0f7f0f7f0f7f0f7f0f7f0f7f0f7f0
def pw359 : Nat := 0x77707770777077707770777077707770
def pw360 : Nat := 0x8f888f888f888f888f888f888f888f88
def pw361 : Nat := 0xffffffff0f000f00ffffffff0f000f00
def pw362 : Nat := 0x77777777707070707777777770707070
def pw363 : Nat := 0xff00ff00f000f000ff00ff00f000f000
def pw364 : Nat := 0x77777777770077007777777777007700
def pw365 : Nat := 0xcc88cc88cc88cc88cc88cc88cc88cc88
def pw366 : Nat := 0x88cc88cc88cc88cc88cc88cc88cc88cc
def pw367 : Nat := 0xcccccccc88888888cccccccc88888888
def pw368 : Nat := 0xeeeeeeeeee00ee00eeeeeeeeee00ee00
def pw369 : Nat := 0xdddddddddd00dd00dddddddddd00dd00
def pw370 : Nat := 0xf4f0f4f0f4f0f4f0f4f0f4f0f4f0f4f0
def pw371 : Nat := 0xbb00bb00bb00bb00bb00bb00bb00bb00
def pw372 : Nat := 0xfbf0fbf0fbf0fbf0fbf0fbf0fbf0fbf0
def pw373 : Nat := 0xff00ff00aa00aa00ff00ff00aa00aa00
def pw374 : Nat := 0xb8b8b8b8b8b8b8b8b8b8b8b8b8b8b8b8
def pw375 : Nat := 0xbbb0bbb0bbb0bbb0bbb0bbb0bbb0bbb0
def pw376 : Nat := 0x4f444f444f444f444f444f444f444f44
def pw377 : Nat := 0xbbbbbbbbb0b0b0b0bbbbbbbbb0b0b0b0
def pw378 : Nat := 0xbbbbbbbbbb00bb00bbbbbbbbbb00bb00
def pw379 : Nat := 0x4c4c4c4c4c4c4c4c4c4c4c4c4c4c4c4c
def pw380 : Nat := 0x5f005f005f005f005f005f005f005f00
def pw381 : Nat := 0xffffffff5f005f00ffffffff5f005f00
def pw382 : Nat := 0xffffa0a0ffffa0a0ffffa0a0ffffa0a0
def pw383 : Nat := 0x5f5f5f5f5f005f005f5f5f5f5f005f00
def pw384 : Nat := 0xf5f0f5f0f5f0f5f0f5f0f5f0f5f0f5f0
def pw385 : Nat := 0xf0f0f0f0a0a0a0a0f0f0f0f0a0a0a0a
def pw386 : Nat := 0xaaeeaaeeaaeeaaeeaaeeaaeeaaeeaaee
def pw387 : Nat := 0xfafefafefafefafefafefafefafefafe
def pw388 : Nat := 0xfa32fa32fa32fa32fa32fa32fa32fa32
def pw389 : Nat := 0xaaaaaaaaeeeeeeeeaaaaaaaaeeeeeeee
def pw390 : Nat := 0xfafafafafefefefefafafafafefefefe
def pw391 : Nat := 0xfafafafa32323232fafafafa32323232
def pw392 : Nat := 0xff00ff0033003300ff00ff0033003300
def pw393 : Nat := 0x55505550555055505550555055505550
def pw394 : Nat := 0xfffafffafffafffafffafffafffafffa
def pw395 : Nat := 0xccc8ccc8ccc8ccc8ccc8ccc8ccc8ccc8
def pw396 : Nat := 0xfa00fa00fa00fa00fa00fa00fa00fa
def pw397 : Nat := 0xc8ccc8ccc8ccc8ccc8ccc8ccc8ccc8cc
def pw398 : Nat := 0xccccccccc8c8c8c8ccccccccc8c8c8c8
def pw399 : Nat := 0xff00ff00fa00fa00ff00ff00fa00fa00
def pw400 : Nat := 0xff00ff0005000500ff00ff0005000500
def pw401 : Nat := 0xfafafafafa00fa00fafafafafa00fa00
def pw402 : Nat := 0x5050505050005000505050505000500
def pw403 : Nat := 0xf500f500f500f500f500f500f500f500
def pw404 : Nat := 0xace0ace0ace0ace0ace0ace0ace0ace
def pw405 : Nat := 0xa0a0a0acececece0a0a0a0acececece
def pw406 : Nat := 0xf5f5f5f5f500f500f5f5f5f5f500f500
def pw407 : Nat := 0xafafafafaf00af00afafafafaf00af00
def pw408 : Nat := 0xf4fcf4fcf4fcf4fcf4fcf4fcf4fcf4fc
def pw409 : Nat := 0xffffffffccccccccffffffffcccccccc
def pw410 : Nat := 0xf0f0f0f000000000f0f0f0f0
def pw411 : Nat := 0xffffc0c0ffffc0c0ffffc0c0ffffc0c0
def pw412 : Nat := 0xffffffffc0c0c0c0ffffffffc0c0c0c0
def pw413 : Nat := 0xba30ba30ba30ba30ba30ba30ba30ba30
def pw414 : Nat := 0x55ff55ff44cc44cc55ff55ff44cc44cc
def pw415 : Nat := 0xaa00aa00eecceeccaa00aa00eecceecc
def pw416 : Nat := 0x55ff55ff50f050f055ff55ff50f050f0
def pw417 : Nat := 0xccccccccc0c0c0c0ccccccccc0c0c0c0
def pw418 : Nat := 0xaa00aa00faf0faf0aa00aa00faf0faf0
def pw419 : Nat := 0xcf8acf8acf8acf8acf8acf8acf8acf8a
def pw420 : Nat := 0xfcf8fcf8fcf8fcf8fcf8fcf8fcf8fcf8
def pw421 : Nat := 0xf0aaf0aaf0aaf0aaf0aaf0aaf0aaf0aa
def pw422 : Nat := 0xc080c080c080c080c080c080c080c08
def pw423 : Nat := 0xfcf4fcf4fcf4fcf4fcf4fcf4fcf4fcf4
def pw424 : Nat := 0xcc44cc44cc44cc44cc44cc44cc44cc44
def pw425 : Nat := 0x30ba30ba30ba30ba30ba30ba30ba30ba
def pw426 : Nat := 0xf8fcf8fcf8fcf8fcf8fcf8fcf8fcf8fc
def pw427 : Nat := 0xffffa0f0ffffa0f0ffffa0f0ffffa0f0
def pw428 : Nat := 0xffffffffa0f0a0f0ffffffffa0f0a0f0
def pw429 : Nat := 0xcccccccc44004400cccccccc44004400
def pw430 : Nat := 0xd5c0d5c0d5c0d5c0d5c0d5c0d5c0d5c0
def pw431 : Nat := 0xa8fca8fca8fca8fca8fca8fca8fca8fc
def pw432 : Nat := 0x75307530753075307530753075307530
def pw433 : Nat := 0xaaffaaff88cc88ccaaffaaff88cc88cc
def pw434 : Nat := 0x55005500ddccddcc55005500ddccddcc
def pw435 : Nat := 0xaaf0aaf0aaf0aaf0aaf0aaf0aaf0aaf0
def pw436 : Nat := 0xaaffaaffa0f0a0f0aaffaaffa0f0a0f0
def pw437 : Nat := 0x55005500f5f0f5f055005500f5f0f5f0
def pw438 : Nat := 0xffffffffaaaaaaaaffffffffaaaaaaaa
def pw439 : Nat := 0x3f3f3f3f2a2a2a2a3f3f3f3f2a2a2a2a
def pw440 : Nat := 0xfcfcfcfca8a8a8a8fcfcfcfca8a8a8a8
def pw441 : Nat := 0xcfcfcfcf8a8a8a8acfcfcfcf8a8a8a8a
def pw442 : Nat := 0x33ff33ff22aa22aa33ff33ff22aa22aa
def pw443 : Nat := 0xccffccff88aa88aaccffccff88aa88aa
def pw444 : Nat := 0xfcfcfcfcf8f8f8f8fcfcfcfcf8f8f8f8
def pw445 : Nat := 0xfff0fff0aaa0aaa0fff0fff0aaa0aaa
def pw446 : Nat := 0xf0fff0ffa0aaa0aaf0fff0ffa0aaa0aa
def pw447 : Nat := 0xfff0fff0faf0faf0fff0fff0faf0faf0
def pw448 : Nat := 0xfcfcfcfcf4f4f4f4fcfcfcfcf4f4f4f4
def pw449 : Nat := 0xcccccccc44444444cccccccc44444444
def pw450 : Nat := 0xfff0fff0f5f0f5f0fff0fff0f5f0f5f0
def pw451 : Nat := 0xc0c0c0c0eaeaeaeac0c0c0c0eaeaeaea
def pw452 : Nat := 0xaaaaaaaa00000000aaaaaaaa
def pw453 : Nat := 0xfcfcfcfc54545454fcfcfcfc54545454
def pw454 : Nat := 0x30303030babababa30303030babababa
def pw455 : Nat := 0xcc00cc00eeaaeeaacc00cc00eeaaeeaa
def pw456 : Nat := 0x33003300bbaabbaa33003300bbaabbaa
def pw457 : Nat := 0xf000f000faaafaaaf000f000faaafaaa
def pw458 : Nat := 0xf000f00afaaafaa0f000f00afaaafaa
def pw459 : Nat := 0xffffffffeaeaeaeaffffffffeaeaeaea
def pw460 : Nat := 0xeaeaeaea00000000eaeaeaea
def pw461 : Nat := 0xbfaabfaabfaabfaabfaabfaabfaabfaa
def pw462 : Nat := 0x80aa80aa80aa80aa80aa80aa80aa80aa
def pw463 : Nat := 0xffffffff3f003f00ffffffff3f003f00
def pw464 : Nat := 0x3f3f3f3f3f003f003f3f3f3f3f003f00
def pw465 : Nat := 0x55555555550055005555555555005500
def pw466 : Nat := 0xaeaaaeaaaeaaaeaaaeaaaeaaaeaaaeaa
def pw467 : Nat := 0xefaaefaaefaaefaaefaaefaaefaaefaa
def pw468 : Nat := 0xcfcfcfcfcf00cf00cfcfcfcfcf00cf00
def pw469 : Nat := 0xffffffffcc00cc00ffffffffcc00cc00
def pw470 : Nat := 0xeeaaeeaa00000000eeaaeeaa
def pw471 : Nat := 0x54505450545054505450545054505450
def pw472 : Nat := 0x33ff33ff30f030f033ff33ff30f030f0
def pw473 : Nat := 0xa0e0a0e0a0e0a0e0a0e0a0e0a0e0a0e
def pw474 : Nat := 0x50545054505450545054505450545054
def pw475 : Nat := 0xffaaffaaeeaaeeaaffaaffaaeeaaeeaa
def pw476 : Nat := 0xa0a0a0a0e0e0e0e0a0a0a0a0e0e0e0e
def pw477 : Nat := 0x50505050545454545050505054545454
def pw478 : Nat := 0xffaaffaabbaabbaaffaaffaabbaabbaa
def pw479 : Nat := 0xfff0fff0f3f0f3f0fff0fff0f3f0f3f0
def pw480 : Nat := 0xf000f00cfcccfcc0f000f00cfcccfcc
def pw481 : Nat := 0xeeeaeeeaeeeaeeeaeeeaeeeaeeeaeeea
def pw482 : Nat := 0x8c888c888c888c888c888c888c888c88
def pw483 : Nat := 0x4c444c444c444c444c444c444c444c44
def pw484 : Nat := 0xeaeeeaeeeaeeeaeeeaeeeaeeeaeeeaee
def pw485 : Nat := 0x55555555050005005555555505000500
def pw486 : Nat := 0xcccccccc0c000c00cccccccc0c000c00
def pw487 : Nat := 0xeeeeeeeeeaeaeaeaeeeeeeeeeaeaeaea
def pw488 : Nat := 0xffaaffaafaaafaaaffaaffaafaaafaaa
def pw489 : Nat := 0xffaaffaaafaaafaaffaaffaaafaaafaa
def pw490 : Nat := 0xf5f5f5f5f5f0f5f0f5f5f5f5f5f0f5f0
def pw491 : Nat := 0xeeeeeeeeeeaaeeaaeeeeeeeeeeaaeeaa
def pw492 : Nat := 0xa0a0a0a0a000a000a0a0a0a0a000a00
def pw493 : Nat := 0xafafafafafaaafaaafafafafafaaafaa
def pw494 : Nat := 0xc0c0c0c0c000c000c0c0c0c0c000c00
def pw495 : Nat := 0xdd00dd00dd00dd00dd00dd00dd00dd00
def pw496 : Nat := 0xff44ff44ff44ff44ff44ff44ff44ff44
def pw497 : Nat := 0xffffffff44444444ffffffff44444444
def pw498 : Nat := 0xffa0ffa0ffa0ffa0ffa0ffa0ffa0ffa0
def pw499 : Nat := 0xffffffffa0a0a0a0ffffffffa0a0a0a0
def pw500 : Nat := 0xfffffffffafafafafffffffffafafafa
def pw501 : Nat := 0xfafafafa00000000fafafafa
def pw502 : Nat := 0xc4c4c4c4c4c4c4c4c4c4c4c4c4c4c4c4
def pw503 : Nat := 0xf0faf0faf0faf0faf0faf0faf0faf0fa
def pw504 : Nat := 0xa0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0
def pw505 : Nat := 0xffffffff55005500ffffffff55005500
def pw506 : Nat := 0xf0f0f0f0fafafafaf0f0f0f0fafafafa
def pw507 : Nat := 0xff00ff0055005500ff00ff0055005500
def pw508 : Nat := 0x55445544554455445544554455445544
def pw509 : Nat := 0xffccffcc00000000ffccffcc
def pw510 : Nat := 0xf0fcf0fcf0fcf0fcf0fcf0fcf0fcf0fc
def pw511 : Nat := 0x55555555444444445555555544444444
def pw512 : Nat := 0xff00ff00cc00cc00ff00ff00cc00cc00
def pw513 : Nat := 0xf0f0f0f0fcfcfcfcf0f0f0f0fcfcfcfc
def pw514 : Nat := 0xccc0ccc0ccc0ccc0ccc0ccc0ccc0ccc0
def pw515 : Nat := 0xaafaaafaaafaaafaaafaaafaaafaaafa
def pw516 : Nat := 0xffff00f0ffff00f0ffff00f0ffff00f0
def pw517 : Nat := 0xffffffff00f000f0ffffffff00f000f0
def pw518 : Nat := 0xa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0aa
def pw519 : Nat := 0xc0ccc0ccc0ccc0ccc0ccc0ccc0ccc0cc
def pw520 : Nat := 0xaaaaaaaafafafafaaaaaaaaafafafafa
def pw521 : Nat := 0xff00ff000f000f00ff00ff000f000f00
def p1_T : Nat := 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8
def p1_R : List Nat := [0, 1, 2]
def p1_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5)]
theorem p1_B : baseOK p1_T p1_R p1_E = true := by decide +kernel
def p1_Z : List SliceD := []
theorem p1_Y : ∀ s ∈ p1_Z, SliceN true p1_R p1_T s := by
  unfold p1_Z
  intro s h; cases h
def p1_C : List (Nat × List Nat) := []
def p1_t : Tabs := (p1_C.map (mkCut true p1_Z),[(3,1),(3,2),(5,1),(5,4),(6,2),(6,4)],[],[])
theorem p1_W : TabsP true p1_R p1_T p1_t := ⟨cutsGood p1_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p1_D3 : List StD := [
([pw0,pw1,pw2],[21,13,1,5,17,9],[15,58,53])]
def p1_D2 : List StD := []
theorem p1_I2 : LevelN true p1_T 2 p1_D2 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p1_C3x0 : levelOK true p1_T p1_t 2 (p1_D2.map Prod.fst) ((p1_D3.drop (0*32)).take 32) = true := by decide +kernel
theorem p1_I3 : LevelN true p1_T 3 p1_D3 := levelStep p1_B p1_W p1_I2 (chunks 32 p1_D3 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p1_C3x0
  ))
theorem p1_L : LowN true p1_R p1_T 4 := lowSearch p1_B p1_I3 (by decide +kernel)
def p2_T : Nat := 0xfee8fee8fee8fee8fee8fee8fee8fee8
def p2_R : List Nat := [0, 1, 2, 3]
def p2_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,1,9)]
theorem p2_B : baseOK p2_T p2_R p2_E = true := by decide +kernel
def p2_Z : List SliceD := [(pw6,4,[0, 1, 2]),(pw7,4,[0, 1, 3]),(pw8,4,[0, 2, 3]),(pw9,4,[1, 2, 3])]
theorem p2_Y : ∀ s ∈ p2_Z, SliceN true p2_R p2_T s := by
  unfold p2_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p2_B p1_B p1_L (by decide +kernel),mkSlice (w:=0) p2_B p1_B p1_L (by decide +kernel),mkSlice (w:=0) p2_B p1_B p1_L (by decide +kernel),mkSlice (w:=0) p2_B p1_B p1_L (by decide +kernel),by simp⟩
def p2_C : List (Nat × List Nat) := [(0,[]),(1,[]),(2,[]),(3,[])]
def p2_t : Tabs := (p2_C.map (mkCut true p2_Z),[(3,1),(3,2),(3,8),(5,1),(5,4),(6,2),(6,4),(6,8),(7,8),(9,0),(9,1),(9,8),(10,0),(10,2),(10,8),(12,0),(12,4),(12,8)],[],[[],[1],[2],[0,1],[1,0],[1,2],[2,1],[0,1,2],[0,2,1],[1,2,1],[0,1,2,1],[1,0,2,1]])
theorem p2_W : TabsP true p2_R p2_T p2_t := ⟨cutsGood p2_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p2_D6 : List StD := [
([pw0,pw1,pw2,pw3],[8,25,3,1,5,12,7,13,17,4,27,41,45,0,15,21,35,53,57,47,65,69],[63,1008,15408,49675,468995,3680896])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p2_D5 : List StD := [
([pw0,pw1,pw17,pw2,pw3],[8,12,31,13,5,43,41,23,21,1,39,53,69,4,3,11,65,0],[3,1,30,114,3,897,3585,61448,245824,69704])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p2_D4 : List StD := [
([pw0,pw1,pw2,pw14,pw11],[45,19,9,13,21,5,12,41,8,53,1],[7,25,32,193,24,768,1024,24,24,192]),
([pw0,pw1,pw2,pw15,pw3],[17,1,5,45,41,53,21,13,57,69,65,0,3],[7,5,8,49,194,256,50,512,1104,6160]),
([pw16,pw0,pw1,pw2,pw3],[45,5,57,1,69,13,41,21],[3,12,48,64,3,49,3,148,12,48])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p2_D3 : List StD := [
([pw0,pw10,pw11,pw12],[29,5,33,17,0,4,21,25],[7,10,10,17,17,224]),
([pw13,pw0,pw1,pw2],[37,5,41,1,49,13,61,21],[3,28,100,3,97,168])]
def p2_D2 : List StD := []
theorem p2_I2 : LevelN true p2_T 2 p2_D2 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p2_C3x0 : levelOK true p2_T p2_t 2 (p2_D2.map Prod.fst) ((p2_D3.drop (0*32)).take 32) = true := by decide +kernel
theorem p2_I3 : LevelN true p2_T 3 p2_D3 := levelStep p2_B p2_W p2_I2 (chunks 32 p2_D3 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p2_C3x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p2_C4x0 : levelOK true p2_T p2_t 3 (p2_D3.map Prod.fst) ((p2_D4.drop (0*32)).take 32) = true := by decide +kernel
theorem p2_I4 : LevelN true p2_T 4 p2_D4 := levelStep p2_B p2_W p2_I3 (chunks 32 p2_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p2_C4x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p2_C5x0 : levelOK true p2_T p2_t 4 (p2_D4.map Prod.fst) ((p2_D5.drop (0*32)).take 32) = true := by decide +kernel
theorem p2_I5 : LevelN true p2_T 5 p2_D5 := levelStep p2_B p2_W p2_I4 (chunks 32 p2_D5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p2_C5x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p2_C6x0 : levelOK true p2_T p2_t 5 (p2_D5.map Prod.fst) ((p2_D6.drop (0*32)).take 32) = true := by decide +kernel
theorem p2_I6 : LevelN true p2_T 6 p2_D6 := levelStep p2_B p2_W p2_I5 (chunks 32 p2_D6 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p2_C6x0
  ))
theorem p2_L : LowN true p2_R p2_T 7 := lowSearch p2_B p2_I6 (by decide +kernel)
def p3_T : Nat := 0xe880e880e880e880e880e880e880e880
def p3_R : List Nat := [0, 1, 2, 3]
def p3_E : List (Nat × Nat × Nat) := [(0,6,7),(1,5,7),(2,3,7),(3,3,11)]
theorem p3_B : baseOK p3_T p3_R p3_E = true := by decide +kernel
def p3_Z : List SliceD := [(pw3,4,[0, 1, 2]),(pw2,4,[0, 1, 3]),(pw1,4,[0, 2, 3]),(pw0,4,[1, 2, 3])]
theorem p3_Y : ∀ s ∈ p3_Z, SliceN true p3_R p3_T s := by
  unfold p3_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=8) p3_B p1_B p1_L (by decide +kernel),mkSlice (w:=4) p3_B p1_B p1_L (by decide +kernel),mkSlice (w:=2) p3_B p1_B p1_L (by decide +kernel),mkSlice (w:=1) p3_B p1_B p1_L (by decide +kernel),by simp⟩
def p3_C : List (Nat × List Nat) := [(0,[]),(1,[]),(2,[]),(3,[])]
def p3_t : Tabs := (p3_C.map (mkCut true p3_Z),[(7,3),(7,4),(7,5),(7,6),(11,0),(11,2),(11,3),(11,8),(11,9),(11,10),(13,5),(13,8),(13,9),(13,12),(14,6),(14,8),(14,10),(14,12)],[],[[],[0],[1],[2],[0,1],[0,2],[2,1],[0,2,1],[2,1,0],[1,0,2,1],[1,0,2,1,0]])
theorem p3_W : TabsP true p3_R p3_T p3_t := ⟨cutsGood p3_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p3_D6 : List StD := [
([pw0,pw1,pw2,pw3],[3,69,53,8,9,12,11,65,37,4,27,57,13,0,19,49,33,31,41,39,25,1],[63,996,15396,115338,401434,3680896])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p3_D5 : List StD := [
([pw19,pw0,pw1,pw2,pw3],[8,12,49,3,1,4,39,41,15,25,0,43,65,53,57,7,69,23],[1,3,124,3968,3,12298,24834,98309,196737,660])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p3_D4 : List StD := [
([pw22,pw0,pw1,pw2,pw3],[13,9,1,25,0,35,53,33,29,37,57,65,49,41],[1,2,4,56,448,576,1096,6272,8328,1032]),
([pw23,pw0,pw1,pw2,pw3],[13,69,9,49,65,1,41,57,25,33],[1,6,56,448,6,48,384,530,6,48]),
([pw19,pw20,pw1,pw2,pw3],[37,4,9,41,21,53,8,1,25,3,65,61],[3,4,3,25,96,128,296,3584,264,264])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p3_D3 : List StD := [
([pw18,pw1,pw2,pw3],[53,9,5,37,13,33,1,41,25],[7,9,17,34,34,448]),
([pw19,pw20,pw21,pw3],[29,4,41,17,45,8,25,57],[3,3,13,48,84,132])]
def p3_D2 : List StD := []
theorem p3_I2 : LevelN true p3_T 2 p3_D2 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p3_C3x0 : levelOK true p3_T p3_t 2 (p3_D2.map Prod.fst) ((p3_D3.drop (0*32)).take 32) = true := by decide +kernel
theorem p3_I3 : LevelN true p3_T 3 p3_D3 := levelStep p3_B p3_W p3_I2 (chunks 32 p3_D3 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p3_C3x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p3_C4x0 : levelOK true p3_T p3_t 3 (p3_D3.map Prod.fst) ((p3_D4.drop (0*32)).take 32) = true := by decide +kernel
theorem p3_I4 : LevelN true p3_T 4 p3_D4 := levelStep p3_B p3_W p3_I3 (chunks 32 p3_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p3_C4x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p3_C5x0 : levelOK true p3_T p3_t 4 (p3_D4.map Prod.fst) ((p3_D5.drop (0*32)).take 32) = true := by decide +kernel
theorem p3_I5 : LevelN true p3_T 5 p3_D5 := levelStep p3_B p3_W p3_I4 (chunks 32 p3_D5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p3_C5x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p3_C6x0 : levelOK true p3_T p3_t 5 (p3_D5.map Prod.fst) ((p3_D6.drop (0*32)).take 32) = true := by decide +kernel
theorem p3_I6 : LevelN true p3_T 6 p3_D6 := levelStep p3_B p3_W p3_I5 (chunks 32 p3_D6 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p3_C6x0
  ))
theorem p3_L : LowN true p3_R p3_T 7 := lowSearch p3_B p3_I6 (by decide +kernel)
def p4_T : Nat := 0xe8a8e8a8e8a8e8a8e8a8e8a8e8a8e8a8
def p4_R : List Nat := [0, 1, 2, 3]
def p4_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,6,14)]
theorem p4_B : baseOK p4_T p4_R p4_E = true := by decide +kernel
def p4_Z : List SliceD := [(pw3,4,[0, 1, 2])]
theorem p4_Y : ∀ s ∈ p4_Z, SliceN true p4_R p4_T s := by
  unfold p4_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=8) p4_B p1_B p1_L (by decide +kernel),by simp⟩
def p4_C : List (Nat × List Nat) := [(0,[])]
def p4_t : Tabs := (p4_C.map (mkCut true p4_Z),[(3,1),(3,2),(5,1),(5,4),(14,6),(14,10),(14,12)],[],[])
theorem p4_W : TabsP true p4_R p4_T p4_t := ⟨cutsGood p4_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p4_D4 : List StD := [
([pw0,pw1,pw2,pw3],[25,13,1,5,21,9,17,0],[15,58,194,53,197,240])]
def p4_D3 : List StD := []
theorem p4_I3 : LevelN true p4_T 3 p4_D3 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p4_C4x0 : levelOK true p4_T p4_t 3 (p4_D3.map Prod.fst) ((p4_D4.drop (0*32)).take 32) = true := by decide +kernel
theorem p4_I4 : LevelN true p4_T 4 p4_D4 := levelStep p4_B p4_W p4_I3 (chunks 32 p4_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p4_C4x0
  ))
theorem p4_L : LowN true p4_R p4_T 5 := lowSearch p4_B p4_I4 (by decide +kernel)
def p5_T : Nat := 0xe888e888e888e888e888e888e888e888
def p5_R : List Nat := [0, 1, 2, 3]
def p5_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,9,13),(3,5,13)]
theorem p5_B : baseOK p5_T p5_R p5_E = true := by decide +kernel
def p5_Z : List SliceD := [(pw3,4,[0, 1, 2])]
theorem p5_Y : ∀ s ∈ p5_Z, SliceN true p5_R p5_T s := by
  unfold p5_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=8) p5_B p1_B p1_L (by decide +kernel),by simp⟩
def p5_C : List (Nat × List Nat) := [(0,[])]
def p5_t : Tabs := (p5_C.map (mkCut true p5_Z),[(3,1),(3,2),(13,5),(13,9),(13,12),(14,6),(14,10),(14,12)],[],[])
theorem p5_W : TabsP true p5_R p5_T p5_t := ⟨cutsGood p5_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p5_D4 : List StD := [
([pw0,pw1,pw2,pw3],[29,17,1,5,25,13,21,9,0],[15,58,202,53,197,336])]
def p5_D3 : List StD := []
theorem p5_I3 : LevelN true p5_T 3 p5_D3 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p5_C4x0 : levelOK true p5_T p5_t 3 (p5_D3.map Prod.fst) ((p5_D4.drop (0*32)).take 32) = true := by decide +kernel
theorem p5_I4 : LevelN true p5_T 4 p5_D4 := levelStep p5_B p5_W p5_I3 (chunks 32 p5_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p5_C4x0
  ))
theorem p5_L : LowN true p5_R p5_T 5 := lowSearch p5_B p5_I4 (by decide +kernel)
def p6_T : Nat := 0xfeeafeeafeeafeeafeeafeeafeeafeea
def p6_R : List Nat := [0, 1, 2, 3]
def p6_E : List (Nat × Nat × Nat) := [(0,0,1),(1,4,6),(2,2,6),(3,2,10)]
theorem p6_B : baseOK p6_T p6_R p6_E = true := by decide +kernel
def p6_Z : List SliceD := [(pw9,4,[1, 2, 3])]
theorem p6_Y : ∀ s ∈ p6_Z, SliceN true p6_R p6_T s := by
  unfold p6_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p6_B p1_B p1_L (by decide +kernel),by simp⟩
def p6_C : List (Nat × List Nat) := [(0,[])]
def p6_t : Tabs := (p6_C.map (mkCut true p6_Z),[(1,0),(6,4)],[],[])
theorem p6_W : TabsP true p6_R p6_T p6_t := ⟨cutsGood p6_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p6_D4 : List StD := [
([pw0,pw1,pw2,pw3],[5,1,0],[7,6,6,5,5,4])]
def p6_D3 : List StD := []
theorem p6_I3 : LevelN true p6_T 3 p6_D3 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p6_C4x0 : levelOK true p6_T p6_t 3 (p6_D3.map Prod.fst) ((p6_D4.drop (0*32)).take 32) = true := by decide +kernel
theorem p6_I4 : LevelN true p6_T 4 p6_D4 := levelStep p6_B p6_W p6_I3 (chunks 32 p6_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p6_C4x0
  ))
theorem p6_L : LowN true p6_R p6_T 5 := lowSearch p6_B p6_I4 (by decide +kernel)
def p7_T : Nat := 0xfee8e8a8fee8e8a8fee8e8a8fee8e8a8
def p7_R : List Nat := [0, 1, 2, 3, 4]
def p7_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,6,14),(4,6,22)]
theorem p7_B : baseOK p7_T p7_R p7_E = true := by decide +kernel
def p7_Z : List SliceD := [(pw4,7,[0, 1, 2, 3]),(pw3,7,[0, 1, 2, 4]),(pw9,7,[1, 2, 3, 4]),(pw24,5,[0, 1, 2, 3]),(pw6,5,[0, 1, 2, 4]),(pw7,5,[0, 1, 3, 4]),(pw2,5,[0, 1, 3, 4]),(pw8,5,[0, 2, 3, 4]),(pw1,5,[0, 2, 3, 4]),(pw25,4,[0, 1, 2]),(pw26,4,[0, 1, 2]),(pw27,4,[0, 1, 3]),(pw28,4,[0, 2, 3]),(pw29,4,[1, 2, 3]),(pw30,4,[0, 1, 4]),(pw31,4,[0, 2, 4]),(pw32,4,[1, 2, 4]),(pw33,4,[1, 3, 4]),(pw34,4,[2, 3, 4])]
theorem p7_Y : ∀ s ∈ p7_Z, SliceN true p7_R p7_T s := by
  unfold p7_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=16) p7_B p2_B p2_L (by decide +kernel),mkSlice (w:=8) p7_B p2_B p2_L (by decide +kernel),mkSlice (w:=0) p7_B p3_B p3_L (by decide +kernel),mkSlice (w:=0) p7_B p4_B p4_L (by decide +kernel),mkSlice (w:=0) p7_B p4_B p4_L (by decide +kernel),mkSlice (w:=0) p7_B p5_B p5_L (by decide +kernel),mkSlice (w:=4) p7_B p6_B p6_L (by decide +kernel),mkSlice (w:=0) p7_B p5_B p5_L (by decide +kernel),mkSlice (w:=2) p7_B p6_B p6_L (by decide +kernel),mkSlice (w:=8) p7_B p1_B p1_L (by decide +kernel),mkSlice (w:=16) p7_B p1_B p1_L (by decide +kernel),mkSlice (w:=16) p7_B p1_B p1_L (by decide +kernel),mkSlice (w:=16) p7_B p1_B p1_L (by decide +kernel),mkSlice (w:=16) p7_B p1_B p1_L (by decide +kernel),mkSlice (w:=8) p7_B p1_B p1_L (by decide +kernel),mkSlice (w:=8) p7_B p1_B p1_L (by decide +kernel),mkSlice (w:=8) p7_B p1_B p1_L (by decide +kernel),mkSlice (w:=4) p7_B p1_B p1_L (by decide +kernel),mkSlice (w:=2) p7_B p1_B p1_L (by decide +kernel),by simp⟩
def p7_C : List (Nat × List Nat) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(6,[]),(7,[]),(8,[]),(9,[]),(10,[]),(11,[]),(12,[]),(13,[]),(14,[]),(15,[]),(16,[]),(17,[]),(18,[]),(1,[129]),(0,[129]),(2,[128]),(1,[261]),(0,[261]),(2,[256]),(2,[392]),(0,[257,261]),(1,[257,261]),(0,[261,513]),(1,[261,513]),(1,[129,523]),(0,[129,523]),(1,[257]),(2,[260]),(2,[384]),(0,[261,515]),(1,[261,515]),(2,[388,514]),(2,[384,520]),(2,[388,522]),(2,[256,392]),(0,[385]),(0,[389]),(2,[392,514]),(2,[256,128]),(1,[257,519]),(1,[129,257]),(2,[384,516]),(0,[129,385]),(1,[385,129]),(0,[257,393]),(0,[385,517]),(0,[129,527]),(1,[129,527]),(2,[392,384]),(0,[261,527]),(0,[261,393]),(0,[261,525]),(0,[385,389]),(0,[385,523]),(0,[389,515]),(0,[389,393]),(0,[389,523]),(0,[257,385,393]),(0,[261,389,393]),(2,[392,516])]
def p7_t : Tabs := (p7_C.map (mkCut true p7_Z),[(3,0),(3,1),(3,2),(3,4),(3,6),(3,8),(3,9),(3,10),(3,16),(3,17),(3,18),(5,0),(5,1),(5,2),(5,4),(5,6),(5,8),(5,9),(5,12),(5,16),(5,17),(5,20),(7,0),(7,1),(7,2),(7,4),(7,6),(7,10),(7,12),(7,17),(7,20),(11,0),(11,1),(11,2),(11,6),(11,8),(11,9),(11,10),(13,0),(13,1),(13,4),(13,6),(13,8),(13,9),(13,10),(13,12),(14,2),(14,4),(14,6),(14,8),(14,9),(14,10),(14,12),(14,18),(19,0),(19,1),(19,2),(19,6),(19,16),(19,17),(19,18),(19,24),(21,0),(21,1),(21,4),(21,6),(21,12),(21,16),(21,17),(21,20),(21,24),(22,0),(22,2),(22,4),(22,6),(22,16),(22,17),(22,18),(22,20),(22,24),(25,0),(25,1),(25,8),(25,9),(25,10),(25,16),(25,17),(25,24),(26,0),(26,2),(26,8),(26,9),(26,10),(26,12),(26,16),(26,17),(26,18),(26,24),(27,18),(27,24),(28,0),(28,4),(28,6),(28,8),(28,12),(28,16),(28,17),(28,20),(28,24),(30,24)],[],[[],[1],[3],[1,3]])
theorem p7_W : TabsP true p7_R p7_T p7_t := ⟨cutsGood p7_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p7_D9 : List StD := [
([pw0,pw1,pw2,pw3,pw4],[8,57,3,5,9,7,49,4,345,133,0,333,225,11,205,209,193,297,15],[31,115,903,15363,49260,98732,404488,82404,404544,200068])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p7_D8 : List StD := [
([pw0,pw1,pw17,pw2,pw3,pw4],[8,3,5,57,105,9,149,241,49,32,7,205,345,145,76,11,333,237,80,433,429,417,15,297,193],[7,11,49,81,145,1,3846,29190,492036,526082,1070594,6652416,1072386,7176448,25513986]),
([pw34,pw0,pw1,pw2,pw3,pw4],[8,3,9,28,49,72,7,205,345,4,193,11,333,0,15,297,5,57,349,145,237,60,48],[7,1,250,1898,63528,65539,393233,393473,397313,65722,591144,1151016,2098578,4233232,6329602]),
([pw32,pw0,pw1,pw2,pw3,pw4],[4,16,3,5,64,209,7,11,49,205,15,8,297,0,369,9,57,241,345,333,40],[1,254,1878,2049,28822,100408,101136,2049,165904,876,262217,1577996,262405,1069504,266245]),
([pw0,pw21,pw1,pw2,pw3,pw4],[20,8,3,105,84,9,57,5,28,7,49,56,345,133,44,333,225,11,209,205,193,4,297,0,60,48],[63,476,1593,14364,245784,262404,524801,3151877,12763137,1925,17832320,37798272,17832961,37798913,5298180]),
([pw0,pw1,pw2,pw10,pw3,pw4],[68,57,32,7,9,72,3,8,349,88,345,92,333,11,209,205,5,313,49,309,15,193,297],[127,123,395,1803,14595,49229,65548,149060,161796,262209,558601,1611777,2098697,4208641,6299144]),
([pw78,pw0,pw1,pw2,pw3,pw4],[24,8,68,9,3,57,28,5,205,193,60,385,4,7,11,297,48,369,0,15,433,49,345,333,209,93,313],[63,208,273,15889,1032193,124,3145773,4195868,8503308,51388497,88081984,92373056,2100753,2342913,101904]),
([pw0,pw83,pw1,pw2,pw3,pw4],[16,8,3,149,96,9,57,5,28,49,7,4,345,40,333,225,11,205,15,193,369,0,313,48,429,297],[63,476,1628,6201,122904,2304,394757,527361,3432453,4327300,3457,9462144,16783873,33645060,33560581]),
([pw30,pw0,pw1,pw2,pw3,pw4],[16,8,56,3,149,9,5,145,11,4,345,297,0,15,333,68,57,309,49,40,429,193],[63,461,516,1545,30733,98392,491540,33341,575512,426052,3146437,542792,131597,444420,3148293]),
([pw0,pw1,pw2,pw50,pw3,pw4],[100,57,3,5,9,7,49,349,12,4,0,11,205,209,389,193,297,433,15],[31,115,391,647,3459,12396,16684,33292,68872,131428,33376,329024,1536,768,1792])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p7_D7 : List StD := [
([pw34,pw1,pw17,pw2,pw3,pw4],[8,28,105,9,149,241,32,349,57,60,345,193,48,333,297],[1,1,14,22,38,1,66,66,66,448,448,448,3584,28672,3584]),
([pw0,pw21,pw1,pw17,pw2,pw3,pw4],[8,9,72,105,28,149,241,68,60,193,48,297,20,433,429,417,345,333],[15,22,20,14,38,70,148,148,4,784,3088,132,20,20,20,12420,16644,33796,66432,134272,1792]),
([pw0,pw1,pw36,pw10,pw3,pw4],[68,17,57,9,8,49,181,277,28,3,205,72,5,313,209,309,173,273,297,193,104,333,108],[7,9,51,67,131,1793,6145,26624,26624,49,33793,33793,65569,131105,8126976]),
([pw78,pw0,pw1,pw17,pw2,pw3,pw4],[105,8,9,68,28,5,32,84,60,385,48,369,433,429,417,193],[15,56,200,72,776,3080,25,24,13,265,1033,8,88,80,80,4168,8512,17472,776,3080,34560]),
([pw78,pw0,pw17,pw2,pw3,pw4],[28,8,68,5,84,205,145,237,9,49,61,149,241,433,3,429,313,32,209,60,11,417,48,297,193],[15,20,36,77,141,1,1796,2308,4356,8708,1032192,7798784,8708,8708,32030720]),
([pw0,pw83,pw1,pw17,pw2,pw3,pw4],[8,9,72,149,61,5,57,105,241,28,145,64,68,205,15,48,369,56,433,3,16,429,417,345,49,297],[15,54,68,134,14,262,1540,2564,29184,4,98816,2052,548,516,548,917508,3147780,4227076,27273216,4300800,33654784]),
([pw0,pw82,pw1,pw2,pw36,pw3,pw4],[8,57,68,105,17,49,349,181,277,72,345,3,193,56,7,333,11,297,44,15,389,173,273,385,60,369,48],[15,14,54,68,134,262,4,549,516,31744,1015808,1049124,1049092,1072640,1802752,516,2098212,4227108,25167876,100728836,168960]),
([pw0,pw82,pw1,pw2,pw3,pw4],[28,84,105,349,5,20,205,4,16,193,0,12,297,24,3,389,60,48,345,333],[7,7,14,14,14,17,99,897,7169,57345,98817,167937,336384,667648,201216]),
([pw0,pw1,pw2,pw15,pw3,pw4],[32,209,5,24,205,49,68,349,149,9,241,389,237,433,273,16,3,4,12,11,0,297,193,112,333,116],[7,56,193,832,1344,7,2049,7,4099,8201,56,16408,229377,1835009,65077248]),
([pw41,pw0,pw1,pw17,pw2,pw3,pw4],[105,8,9,68,28,5,32,20,60,345,7,48,333,15,57,149,241,145,237,433,3,429,120,11,417,124,297,193],[15,58,200,72,1800,14344,105,16456,13,33289,69641,8,104,131680,266336,524360,7340096,58720320,1573384,8917000,201331200]),
([pw41,pw0,pw1,pw2,pw3,pw4],[24,68,9,8,20,49,4,16,345,0,12,333,57,149,241,433,32,5,3,145,120,11,237,124,297,193],[7,25,33,449,3585,4102,7,8454,18438,229377,2031872,14878720,295169,2131969,60033280]),
([pw183,pw0,pw1,pw2,pw3,pw4],[24,68,9,28,389,205,4,16,385,0,12,369,5,17,45,181,57,277,145,237,49,173,273,48,297],[7,25,33,449,3585,4106,24579,98306,163842,4105,266504,530440,3145985,5244929,25168128]),
([pw0,pw1,pw43,pw17,pw2,pw3,pw4],[64,32,61,5,9,72,149,57,105,241,3,49,145,237,7,173,68,15,297,333,48,433,429,417,40,76],[15,113,162,305,112,561,11,1,3082,4107,8202,1,247808,2,1967104,2114562,4194307,25166850,37799937,2885632,38536193]),
([pw0,pw1,pw43,pw2,pw3,pw4],[60,313,32,5,16,76,64,9,96,57,241,24,173,20,0,12,333,40,297],[15,49,960,49,1472,55,15,55,15,14352,4,114704,49,462848,49]),
([pw184,pw0,pw1,pw2,pw3,pw4],[16,56,32,389,28,24,205,385,0,12,369,64,57,68,9,73,241,49,309,193,345,40,333],[3,29,97,129,1793,30728,26658,40961,80896,393258,1572873,6292488,1048609,394274,1573889]),
([pw0,pw83,pw1,pw2,pw36,pw3,pw4],[8,57,96,3,105,56,49,73,277,24,15,16,72,297,369,44,313,5,28,7,25,345,333,429,173,273,128,36,40],[15,22,102,36,166,262,32,1640,3592,4096,58376,200800,856072,3215392,4403200,4,27263040,33579104,69208104,402677760,69230632]),
([pw30,pw0,pw1,pw17,pw2,pw3,pw4],[9,8,149,68,32,28,145,15,56,173,76,345,48,333,60,17,97,241,309,429,193,297,237,3,417,36,40,49],[15,120,408,520,3080,12424,16457,16392,98313,13,139273,8,278600,1573952,6299712,8651016,1574144,117448704,263176,134488072,1573888]),
([pw0,pw1,pw17,pw2,pw50,pw3,pw4],[52,48,61,9,5,49,105,100,3,149,41,205,7,32,193,145,60,297,221,433,44,12,16,76,11,80,68,15],[31,2,105,393,649,1162,1,6450,12562,49170,458769,1573152,2105600,12665088,52559873,67637280,8411168,168427553,1,65536,8601601]),
([pw165,pw0,pw1,pw2,pw3,pw4],[20,84,105,28,209,205,4,16,193,0,12,297,5,49,149,9,241,3,145,237,173,273,44,333],[7,25,33,449,3585,4106,8195,49154,81922,131081,266504,530440,1057025,2107393,12585216]),
([pw0,pw1,pw99,pw2,pw3,pw4],[32,209,68,101,57,349,17,45,9,5,49,313,16,345,4,12,333,0,173,273,3,297,193,44,56],[15,53,228,292,292,513,1031,2051,2051,1029,28673,229377,271364,590852,32579584]),
([pw185,pw0,pw1,pw2,pw3,pw4],[28,68,9,5,205,8,4,16,385,0,12,369,49,45,149,241,197,209,313,173,273,48,297],[7,9,51,449,3585,7,12294,16390,32774,65539,393473,395265,528642,1054722,6293760]),
([pw186,pw0,pw1,pw2,pw3,pw4],[16,76,28,209,24,205,20,193,0,12,369,5,313,64,9,96,57,73,241,25,429,345,40,297],[3,13,113,129,1793,6148,122912,163841,320512,6180,524293,7172,3145761,12583968,5243905]),
([pw0,pw187,pw1,pw2,pw3,pw4],[16,56,64,57,68,9,241,173,345,40,333,297],[3,60,30,3,92,3,135,257,3,18,3,3584,147,18,3]),
([pw34,pw0,pw2,pw10,pw3,pw4],[32,28,20,3,68,205,72,389,313,209,13,349,5,1,57,309,145,237,297,193,48,333,60],[1,62,208,834,834,3120,14353,18448,18448,2,32816,32816,69649,135185,8126472]),
([pw78,pw34,pw0,pw2,pw3,pw4],[28,5,8,68,205,145,237,9,197,209,313,349,49,45,57,173,273,48,297,333],[7,7,25,35,67,137,265,1537,1537,14344,18440,18440,36872,69640,917504]),
([pw34,pw0,pw1,pw86,pw2,pw3,pw4],[60,76,209,7,72,16,24,309,20,40,36,297,5,64,1,57,132,181,349,3,68,25,129,237,417,48,11,333,49,345],[3,5,57,449,35,3585,28673,229392,360576,98305,362496,528401,1052801,6295553,8394753,1,1048577,117966848,1048705,402655360,537397249]),
([pw30,pw34,pw0,pw1,pw2,pw3,pw4],[16,28,56,60,57,8,349,68,145,345,48,11,333,9,40,36,297,5,237,49,273,193,429],[15,240,394,8,648,7296,8328,136,140,13,114696,392,208,152,208,392,131336,327944,524424,1577088,6357000]),
([pw34,pw0,pw1,pw2,pw50,pw3,pw4],[48,76,209,7,205,44,3,72,12,16,297,0,5,52,1,349,49,57,100,145,221,68,433,193,60,11],[3,5,57,449,515,3329,28673,229392,426112,434176,394241,4177,4289,528385,1053697,6291544,25231440,33555473,1,16777217,25165825]),
([pw0,pw1,pw188,pw2,pw3,pw4],[32,209,64,57,9,29,133,241,5,389,345,20,49,24,12,333,0,193,15,40,297,11],[15,13,28,108,140,257,515,1031,515,14337,1029,114689,136196,3969024,132100]),
([pw189,pw0,pw1,pw2,pw3,pw4],[28,0,8,5,24,205,20,4,16,193,52,9,57,149,85,225,313,389,293,60,345,333,417],[7,9,113,897,7,3073,7200,11776,52224,196641,197121,263169,1573408,6292512,525824]),
([pw102,pw0,pw1,pw2,pw3,pw4],[12,100,349,32,389,28,24,433,20,16,385,369,9,57,29,41,3,205,209,7,193,345,297,333],[7,57,449,1537,2049,12290,12290,16898,32771,983184,3146256,12582929,3146368,12583041,2097665]),
([pw106,pw0,pw1,pw2,pw3,pw4],[16,0,4,32,145,28,24,173,20,193,8,52,9,57,149,41,225,3,205,209,7,385,429,333,297],[7,57,449,513,1027,14352,14464,18433,104448,1966224,6291473,25167888,6291585,25168000,8390657]),
([pw32,pw0,pw21,pw1,pw2,pw3,pw4],[56,64,16,5,28,389,32,433,49,68,297,3,369,44,11,84,105,57,241,205,40,36,60,345],[1,7,120,385,513,31744,98307,229416,385,33281,361984,513,524289,7,3146753,4196481,4194313,4195368,385,385,8391681]),
([pw32,pw0,pw1,pw2,pw10,pw3,pw4],[56,313,28,209,32,309,205,24,16,68,64,297,3,369,44,11,9,57,345,241,60,72,36,333,40,88],[1,30,225,1808,512,63488,197122,197153,71168,262657,590336,1053219,1,2359307,1050634,1049088,608,609,1793,29360640,33830913]),
([pw78,pw32,pw0,pw1,pw2,pw3,pw4],[24,16,60,64,68,9,5,205,40,36,369,209,313,49,433,297,3,44,11,241,93,345],[15,60,68,148,14,1796,4,6148,24593,20,492544,52,24624,20,524336,1048596,6148,7172,8212,25616,2195460]),
([pw30,pw32,pw0,pw1,pw2,pw4],[16,193,8,345,72,25,4,40,325,429,20,185,64,57,68,9,49,309,333,297],[15,13,57,65,393,65,515,3075,643,61440,61440,28800,212992,786560,82048]),
([pw32,pw0,pw172,pw1,pw2,pw3,pw4],[36,40,64,32,209,28,11,205,44,193,417,333,136,241,57,68,309,56,297,49,5,3,325],[1,7,58,450,515,3075,12293,28688,28800,3,3,3,229377,7,262145,1573008,3,3,3,3,6292481]),
([pw30,pw29,pw0,pw1,pw2,pw3,pw4],[16,12,40,36,52,68,149,72,145,48,345,3,313,60,309,429,193,57,49],[31,116,900,12,1028,22,4,14344,16424,98317,44,131424,147552,12,12,278816,12,12,12,12,98308]),
([pw32,pw0,pw1,pw2,pw50,pw4],[4,16,193,48,189,44,185,0,52,57,100,9,345,241,3,49,5,205,209,7,72,389,36,297,40,68,433],[1,30,102,142,142,3840,3840,5378,9984,1032192,3149826,31539456,100667394,29917440,1]),
([pw0,pw21,pw1,pw53,pw2,pw3,pw4],[20,68,105,28,5,49,433,345,56,333,44,72,193,297,3,385,369],[7,30,1,101,390,1542,3,3,2049,4353,9217,26,16393,280,1048,97,33152,67072,97,97,5504]),
([pw0,pw1,pw53,pw2,pw3,pw4],[28,389,72,5,105,20,17,68,49,56,345,193,84,44,333,3,385,16,11,369,12,173,273,297],[31,1,500,7700,28692,15,33159,15,15,4516,230912,1859584,2100640,4211104,8433152]),
([pw78,pw0,pw21,pw2,pw3,pw4],[24,5,389,20,0,3,68,61,149,9,241,93,209,313,44,297,333],[7,25,33,7,7,200,9,832,1344,2057,12296,12296,9,9,114688]),
([pw78,pw0,pw1,pw2,pw3,pw4],[24,68,9,20,205,4,16,385,0,12,369,57,149,241,49,28,93,209,313,173,273,48,297],[7,9,17,225,1793,2054,7,4102,8198,114689,426112,427008,540801,1065985,6292608]),
([pw0,pw190,pw1,pw2,pw3,pw4],[16,3,8,28,5,313,20,49,309,345,385,40,297,333,209,205,193,0,11,69],[7,56,448,1537,14336,16393,32833,65537,395265,56,1033,56,524353,448,10753]),
([pw191,pw0,pw1,pw2,pw3,pw4],[16,56,173,345,28,313,60,5,309,40,297,333],[3,3,7,9,3,240,262,3,3584,102,3,240,7,262,3]),
([pw0,pw21,pw1,pw2,pw10,pw3,pw4],[20,68,105,57,349,205,3,56,193,44,297,345,333,49],[7,14,7,22,22,22,3,33,67,385,1537,3,1,2432,5632,8195,3,3,2178,4610,896]),
([pw0,pw21,pw1,pw10,pw3,pw4],[20,205,28,72,17,9,349,209,3,309,49,173,273,48,297,333],[31,44,104,104,104,132,268,519,519,1,12,12,3080,5128,57344]),
([pw0,pw21,pw10,pw3,pw4],[20,205,3,105,68,9,389,349,5,56,345,44,333,11,93,309,193,297],[63,472,1692,14488,16388,99843,169987,1876,14672,204292]),
([pw0,pw21,pw1,pw2,pw50,pw3,pw4],[44,3,105,52,389,57,5,49,433,68,349,193,56,297,11,48,209,205,12],[15,116,389,1542,7174,24581,98305,131073,262147,6145,12289,32899,32848,38992,41025,385,385,385,1,4097,6145]),
([pw104,pw0,pw1,pw2,pw3,pw4],[24,68,8,20,205,49,16,345,4,12,333,0,32,5,349,3,11,72,145,237,273,297,193,140,144],[1,14,55,450,3586,28674,51,49282,82946,51,405632,668672,51,1049619,31491200]),
([pw78,pw0,pw1,pw10,pw3,pw4],[24,68,9,28,3,0,205,309,349,93,209,313,49,173,273,48,297,333],[7,25,33,193,193,14,259,262,262,521,3080,3080,12289,20481,229376]),
([pw0,pw83,pw1,pw2,pw10,pw3,pw4],[28,72,149,57,349,209,24,20,205,56,44,369,48,345,309,429,297,16,333],[7,7,14,22,14,22,33,449,515,3,7169,3,515,3,3,1,57600,72448,139778,266242,72192]),
([pw0,pw1,pw2,pw60,pw10,pw3,pw4],[209,57,32,68,9,149,349,3,313,5,309,205,49,56,297,369,44,11,345,333,40,88],[15,26,42,78,42,74,141,261,516,261,261,3080,4108,3080,3080,8196,4,245888,270340,1572996,2416768]),
([pw0,pw1,pw2,pw60,pw3,pw4],[60,209,32,5,56,205,24,49,16,3,149,8,345,68,40,333,369],[15,240,3840,13569,58368,15,15,4367,16391,241,4593,16496,4,82176,53505]),
([pw192,pw0,pw1,pw2,pw3,pw4],[16,68,349,32,145,173,345,0,12,333,17,45,9,5,129,237,157,49,273,385,193],[7,25,35,65,897,14,3078,7,4614,8202,16393,41480,65539,393730,1573377]),
([pw0,pw1,pw2,pw10,pw50,pw3,pw4],[209,57,7,9,3,205,52,349,68,193,88,297,92,11,48,44,32,313,60,309,56,12,16],[31,62,198,390,1670,14466,49189,32768,81941,148993,268289,16384,33076,558624,1054752,2097412,4195844,2111552,5120,1024,7680]),
([pw0,pw125,pw1,pw2,pw3,pw4],[24,28,209,68,9,5,49,97,149,241,8,433,4,16,345,0,12,333,72,237,3,297,193,48,60],[1,62,217,280,536,1070,3145,28680,229384,262191,262182,917510,2121,2121,32653312]),
([pw0,pw21,pw1,pw2,pw3,pw4],[20,84,105,57,149,241,24,205,4,16,193,0,12,297,28,3,145,5,237,173,49,273,44,333],[7,14,7,22,38,65,129,1793,14337,49153,214016,352256,1573889,2629633,12592128]),
([pw0,pw1,pw2,pw10,pw3,pw4],[28,209,32,68,57,9,349,3,5,313,309,205,16,345,4,12,333,0,88,193],[31,56,76,88,88,143,260,519,519,1,3080,3080,28676,229380,860160]),
([pw193,pw0,pw1,pw2,pw3,pw4],[16,68,149,28,145,205,385,0,12,369,17,45,241,5,25,237,157,49,273,345,193],[7,25,35,65,897,14,3078,7,4102,8202,16393,41480,65539,393730,1573377]),
([pw0,pw1,pw194,pw2,pw3,pw4],[60,313,32,5,16,56,49,205,40,297,333],[15,48,224,49,1792,55,15,55,15,177,4,48,177,352,49]),
([pw78,pw195,pw0,pw1,pw2,pw3,pw4],[24,20,3,68,9,205,56,385,44,369,57,49,429,417,193],[7,25,3,33,193,769,1034,1,2051,4162,8450,1048,3,88,280,3,4288,8960,3,3,16832]),
([pw78,pw195,pw0,pw1,pw3,pw4],[28,32,3,72,9,5,205,309,49,45,209,173,273,149,241,48,297,333],[7,25,33,193,193,778,1027,2306,4354,3,8216,16408,3,3,229376]),
([pw78,pw0,pw1,pw86,pw2,pw3,pw4],[57,24,68,9,20,88,16,40,36,369,181,241,32,209,28,345,313,385,333,173,44,417,297],[15,18,50,34,98,898,13,1045,15,1029,2053,28688,18,237568,336384,524306,2,3145744,18,18,5276160]),
([pw78,pw0,pw1,pw2,pw50,pw3,pw4],[57,48,3,9,52,5,88,12,16,0,209,433,49,68,349,193,60,297,11,44,93,56],[31,34,66,134,322,642,1039,6153,24581,114693,393219,1573890,1030,99330,197634,538624,628736,2232322,2,65538,98306]),
([pw0,pw83,pw1,pw66,pw2,pw3,pw4],[16,64,149,28,5,49,3,96,40,205,15,72,369,313,25,309,56,297,429,345],[7,30,1,230,133,390,3,3,1601,2049,4353,26,8728,16393,280,98400,129,135424,786945,135456,4353]),
([pw0,pw1,pw66,pw2,pw3,pw4],[28,313,72,5,149,96,3,49,16,345,40,333,145,7,309,20,24,15,11,297,12,60,429,76],[31,1,244,820,3124,15,15,4615,15,254144,36,1969152,6292352,937088,8916800]),
([pw0,pw83,pw1,pw2,pw91,pw3,pw4],[16,3,149,68,313,57,5,205,7,64,9,345,429,297,333,241,28,209,56,193,40,369,25],[15,116,422,1798,6149,57348,196609,262273,262145,524289,3145729,65744,66128,4261889,24656,1,6273,1073280,6145,1073152,1067009]),
([pw0,pw1,pw2,pw167,pw3,pw4],[32,209,72,57,9,149,241,20,49,16,345,40,333,24,56,193,205,297,44,12],[15,28,13,44,76,387,129,1539,6147,8577,116608,399744,17921,530433,40448]),
([pw79,pw0,pw1,pw160,pw2,pw3,pw4],[57,48,3,9,52,5,12,32,20,205,36,193,369,333,313,277,148,49,345,429,417],[31,34,194,770,3074,12354,16399,98373,131849,265217,67,16450,770,3074,12354,2,525376,1048642,3840,66,66]),
([pw79,pw0,pw1,pw2,pw3,pw4],[28,3,9,8,5,24,205,0,4,16,193,12,369,313,20,49,57,148,36,345,60,44,333,417,273],[15,17,225,1793,6273,8199,245830,1967108,6428676,24641,271361,14337,1360960,27285568,1842176]),
([pw30,pw0,pw1,pw86,pw2,pw4],[16,345,385,0,4,40,325,68,9,57,73,193,429,49,309,333,297],[7,7,9,17,99,896,1153,896,416,6145,24704,98336,17,6177,8352]),
([pw0,pw162,pw1,pw2,pw3,pw4],[12,3,8,28,5,209,152,9,49,57,7,16,345,133,333,225,389,24,20,385,369,37,193,297],[7,56,1986,14528,49217,65545,394243,526337,1048577,56,56,2097161,4200704,8404993,6145]),
([pw88,pw0,pw1,pw2,pw3,pw4],[16,36,193,333,156,57,3,5,9,56,49,225,205,297],[3,3,3,5,11,496,1840,3,2074,5760,3,8202,3,8714,11]),
([pw0,pw83,pw1,pw160,pw2,pw3,pw4],[40,15,149,52,313,57,5,36,3,277,64,205,49,7,24,20,193,369,333,32,28,429,345,297],[15,116,1924,6180,133,133,129,8321,51201,65537,393345,1573072,6224,129,193,1,6291585,8388737,129,129,2228227]),
([pw30,pw0,pw172,pw1,pw2,pw3,pw4],[9,40,3,149,52,36,56,32,145,28,345,333,417,241,64,209,57,309,49,24,297,193,405],[31,98,898,34,1026,6178,24613,98561,458753,43,35,2,655456,98,1048610,426240,34,34,34,34,6293506]),
([pw0,pw83,pw1,pw2,pw50,pw4],[16,3,29,193,48,5,313,160,9,49,57,7,345,341,11,129,44,185,0,429,297,325],[15,112,3970,12417,16784,32785,196617,262169,262169,112,19,112,528385,1049106,2097169]),
([pw0,pw139,pw1,pw2,pw3,pw4],[16,64,349,68,149,49,169,345,32,5,28,309,0,12,333,193,3,40,297,15],[1,30,110,143,30,1800,2090,139,28680,2600,33411,999936,171,2088,49283]),
([pw0,pw1,pw196,pw2,pw3,pw4],[32,389,145,8,72,57,9,149,241,5,24,49,16,25,20,429,4,12,417,0,385,205,56,273,193],[7,57,112,176,304,513,3075,12291,7,19457,102401,917505,7379968,12848128,21270528]),
([pw0,pw197,pw1,pw2,pw3,pw4],[28,3,9,8,237,389,44,49,205,60,193,345,297,333,5],[15,53,452,3588,12356,16385,321,1537,4161,337,49,4177,448,12480,1600]),
([pw198,pw0,pw1,pw2,pw3,pw4],[12,68,349,32,389,28,433,16,345,333,9,17,45,49,205,193,429,297,417,253],[7,57,67,385,513,1030,6150,134,7,24594,98448,393233,16514,524291,65665]),
([pw0,pw164,pw1,pw2,pw3,pw4],[16,36,48,5,209,72,9,3,49,57,7,333,369,221],[3,28,2016,3,6,3,3,33,6147,28,3,12294,3,6,4103]),
([pw30,pw28,pw0,pw1,pw2,pw3,pw4],[16,12,40,36,48,15,149,52,32,345,3,277,64,24,20,273,429,193,333,209,5,309],[31,228,276,12,516,22,7176,4,57352,196621,262156,1574976,2132032,12,12,3702784,12,12,12,12,196612]),
([pw0,pw1,pw2,pw50,pw3,pw45,pw4],[209,349,5,3,100,7,49,12,16,205,389,193,36,48,297,40,433,44,345,333,164],[31,114,146,274,144,146,581,1161,6405,8237,50305,65760,6976,131688,49344,262528,16,524416,272,1048960,144]),
([pw0,pw1,pw2,pw3,pw45,pw4],[52,349,100,3,5,7,49,16,345,12,333,205,209,36,193,28,32,297,20,24],[31,103,391,132,1543,6264,29072,102456,132625,27072,788584,132673,5,1925,1541]),
([pw0,pw1,pw2,pw50,pw3,pw120,pw4],[389,57,7,9,3,205,49,12,349,72,193,36,16,52,40,48,433,44,369,168],[31,106,914,7426,8218,16770,117,32897,7169,128,16513,65700,7264,131188,16544,34944,32896,262272,7168,530560,16512]),
([pw0,pw1,pw2,pw3,pw120,pw4],[32,389,72,57,9,149,241,3,49,16,12,11,385,36,193,20,24,369,40,297,0,345,4],[15,28,44,13,76,387,643,513,3075,29440,98561,918784,3154433,161280,5506049]),
([pw75,pw0,pw1,pw2,pw50,pw3,pw4],[57,48,3,9,52,5,7,205,44,12,32,4,0,389,49,349,172,36,16,433,333],[31,34,450,1538,6146,4610,8207,16521,98821,491521,515,8326,8706,401410,8706,524932,409728,642,2,1049090,514]),
([pw75,pw0,pw1,pw2,pw3,pw4],[28,3,9,8,5,24,205,20,4,0,389,172,49,57,36,345,133,16,40,333,225,193,297],[15,17,225,769,769,1031,14406,247812,1853444,1091,2229249,4211713,2281536,4997184,2801664])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p7_D6 : List StD := [
([pw0,pw82,pw10,pw3,pw4],[28,68,17,349,5,205,309,49,173,273,48,297,333],[7,14,14,14,19,97,97,386,642,7168]),
([pw0,pw1,pw36,pw10,pw50,pw3,pw4],[57,17,9,52,49,3,68,73,137,85,229,48,205,5,209,72,313,7,309,69,157,345,333,104,193],[3,4,25,97,385,1537,6144,8192,49184,81920,81920,24,135232,266240,6144,112,1572880,24,2097152,4194304,25165824]),
([pw78,pw0,pw43,pw17,pw2,pw3,pw4],[61,5,9,145,176,205,37,221,149,57,41,225,209,49,173,193,297,333,433,32,429,417],[7,10,16,32,10,194,257,512,5,257,3073,4096,24576,32768,196608,270336,1572864,2162688,24576,204800,196608]),
([pw78,pw0,pw17,pw2,pw50,pw3,pw4],[61,5,9,389,205,7,28,25,129,37,221,57,3,68,29,133,41,225,433,49,209,32,313,345,333,48,193],[7,8,16,98,386,1538,2048,5,12289,49153,196609,786432,3149824,5242880,5242880,794624,786432,786432,8388608,16777216,100663296]),
([pw79,pw0,pw1,pw2,pw36,pw3,pw4],[57,105,5,49,24,20,28,52,345,193,85,257,313,3,333,293,205,81,385,369],[3,4,56,208,768,144,3,41,32,769,3073,4136,12352,768,53248,65536,552,131112,262400,540672,768]),
([pw41,pw0,pw83,pw1,pw2,pw3,pw4],[57,9,16,64,313,5,49,297,333,149,145,433,24,15,193,369,25,345,421],[3,12,56,64,12,384,513,3,3,513,385,1024,14336,16384,32896,48,196624,48,395264,384,384]),
([pw0,pw153,pw1,pw2,pw36,pw3,pw4],[57,20,8,5,101,17,49,9,73,161,85,257,145,180,193,297,44,15,313,389,309,69,157,253,385,345,369],[7,25,97,128,769,3073,4096,6,8192,16384,229376,262216,524296,524296,294920,1048576,6291520,8421440,50331648,67141632,83918848]),
([pw154,pw0,pw1,pw17,pw2,pw3,pw4],[9,149,5,145,16,4,56,49,173,433,345,297,333,61,57,313,309,417],[3,12,112,896,1024,6144,8197,16384,641,3,6145,32768,65668,12,6148,704,80,133120,640,640,6144]),
([pw0,pw82,pw83,pw2,pw36,pw3,pw4],[57,5,101,3,389,17,49,349,73,161,85,257,24,313,32,25,345,193,297,361,433,69,253,60,369],[7,25,97,128,769,3073,4114,8258,16384,98306,8194,4176,4112,131072,786448,1048576,2162752,4456512,8454152,17039360,17104896]),
([pw30,pw0,pw1,pw155,pw17,pw3,pw4],[9,149,5,145,173,433,32,345,297,333,61,17,97,349,309,49,389,24,193,157,421,417],[3,12,16,96,128,800,1029,6145,8192,3,769,49156,65536,12,772,131072,802816,768,1310720,2097408,768]),
([pw0,pw82,pw1,pw2,pw84,pw3,pw4],[57,105,17,45,181,85,257,5,49,24,309,16,56,333,297,389,72,28,3,377,173],[3,3,13,17,17,97,128,1792,6144,6144,24576,33536,229376,819200,24576,1049344,1049344,8960,512,24576,24576]),
([pw0,pw1,pw2,pw156,pw4],[32,209,5,24,205,49,16,345,193,40,297,333],[7,56,448,3584,7,7,515,56,536,448]),
([pw0,pw1,pw2,pw15,pw50,pw3,pw4],[57,5,9,349,3,68,29,133,41,225,205,49,389,32,25,129,37,221,433,7,81,253,12,16,193,4,297,0,345,333,112],[7,5,8,49,193,769,3074,4096,8210,49154,196610,262144,525344,3072,3146752,4194352,58720256,205520896,268435456,536870912,1157627904]),
([pw0,pw1,pw157,pw2,pw36,pw3,pw4],[57,5,101,56,8,17,49,9,73,161,85,257,389,313,24,16,180,193,297,369,205],[7,25,97,128,769,3073,4106,8258,4098,4098,4098,16456,98312,131072,786432,1048576,65600,786496,98304,786432,327680]),
([pw41,pw0,pw1,pw43,pw2,pw3,pw4],[57,9,313,5,16,60,49,297,333,149,145,433,24,15,193,3,421],[3,12,48,64,48,384,3,513,3,513,385,1028,12,1028,12,14336,16384,384,100352,384,384]),
([pw41,pw0,pw1,pw17,pw86,pw3,pw4],[97,17,49,5,309,20,173,345,69,61,9,45,3,433,133,41,225,209,32,25,37,221,120,417,297,193],[3,28,32,64,388,20,1544,2048,13312,17536,99328,131072,270344,524424,3145736,270336,4198528,25165824,33554432,25174016,20971648]),
([pw41,pw0,pw1,pw86,pw3,pw4],[45,309,9,49,209,5,24,116,433,68,181,241,32,345,385,333,297,237,3,417,11,120],[15,58,192,194,74,53,1793,1537,2561,4400,24624,229392,64,1868032,2465792]),
([pw41,pw0,pw1,pw2,pw50,pw3,pw4],[57,9,209,5,49,12,3,24,193,4,16,0,68,29,41,225,32,37,221,433,11,297,345,333,120],[3,12,16,224,1792,2080,3,3,4161,8449,49153,12,65604,12,393220,524480,524608,3670016,4194304,8388608,18874624]),
([pw85,pw0,pw1,pw2,pw36,pw3,pw4],[57,105,5,49,24,20,0,44,345,193,17,9,85,257,313,237,28,3,333,221,205,81,385,369],[3,4,56,208,768,144,3,1033,2048,769,12289,49160,212992,768,802816,1048576,776,2359304,4194560,8650752,768]),
([pw0,pw1,pw158,pw17,pw2,pw3,pw4],[61,9,5,28,8,57,17,97,29,133,41,225,209,205,49,25,129,37,221,172,68,7,345,333,433,429,193,417,297],[7,26,32,194,770,3074,28,4096,24580,98308,393220,524288,3153920,4194304,8388608,16785408,100663296,402653184,24576,16785408,100663296]),
([pw159,pw0,pw1,pw2,pw36,pw3,pw4],[57,181,5,145,49,173,0,4,16,36,193,297,333,369,101,17,9,85,209,389,205],[3,12,48,960,1024,14336,16389,32785,65536,3,133121,262164,524292,12,526340,1048576,48,10256,768,10752,10240]),
([pw0,pw1,pw43,pw44,pw2,pw3,pw4],[57,5,1,149,241,145,237,205,49,12,48,193,273,429,60,16,297,3,405],[7,9,17,9,9,17,34,66,386,34,66,1536,384,2048,1536,4224,57344,65536,384,4224,401408]),
([pw0,pw83,pw1,pw2,pw84,pw36,pw4],[57,7,385,5,101,17,49,73,161,9,85,257,145,24,297,357,313,25,345,3,69,309,253,4,325,369],[7,25,97,385,512,3073,4096,8260,8196,8196,49156,65608,393224,524298,81928,1310784,2097152,4210752,8388608,17055744,33570816]),
([pw0,pw1,pw43,pw17,pw2,pw50,pw4],[61,9,5,29,133,57,17,97,3,429,41,225,25,129,313,205,49,32,37,221,4,193,48,433,297,40,333],[7,26,32,194,770,3074,12292,16384,98308,131588,786436,1048576,98304,131584,6291456,8421376,131584,50331904,8421888,8421376,67108864]),
([pw83,pw1,pw66,pw2,pw36,pw3,pw4],[145,8,49,3,15,16,149,72,297,369,57,5,101,313,28,25,345,17,69],[1,2,28,96,128,768,7168,10244,18496,100352,10496,132100,96,66688,768,128,327684,772,96,832,768]),
([pw1,pw66,pw2,pw36,pw3,pw4],[57,313,105,5,49,72,28,3,7,149,345,145,333,20,429,181,297,277,173,273,16,184,369,40],[15,58,994,3106,4138,8593,8769,50209,200705,32,279568,593936,3147520,12587520,2167936]),
([pw0,pw83,pw1,pw36,pw91,pw3,pw4],[57,3,68,5,101,9,17,49,73,161,85,257,209,16,205,20,193,297,369,28,313,25,345,69,253],[7,25,32,193,769,3073,4096,24580,32768,65536,393216,540680,1048712,6291464,1179656,24704,24576,409600,12583040,16908416,393216]),
([pw79,pw0,pw17,pw160,pw2,pw3,pw4],[61,5,9,209,32,205,49,25,129,37,221,57,3,148,29,41,12,313,20,193,429,273,417,81,333],[7,8,16,98,386,1538,2048,12292,100,24580,40964,204800,393248,1703936,196608,2097152,1572864,4194304,96,25165856,1572864]),
([pw79,pw0,pw17,pw2,pw3,pw4],[28,5,8,188,32,145,205,9,49,105,193,345,149,369,333,241,433,20,313,429,36,417,60],[7,9,19,35,19,1,960,7296,57472,458816,1836032,3416064,3392,2170944,4205568]),
([pw0,pw83,pw1,pw2,pw161,pw3,pw4],[57,149,9,85,257,145,49,205,180,193,297,369,5,25,345,221,309,16,36,40],[3,3,3,4,3,25,32,192,256,512,3072,192,4352,28672,37888,65536,192,3136,147712,787456,3072]),
([pw93,pw0,pw1,pw160,pw2,pw3,pw4],[277,9,313,5,32,0,49,24,429,193,29,433,417,157,81,333],[3,12,16,224,768,160,3,3,3,1281,3,12,12,772,12,2048,768,4096,8512,49216,768]),
([pw93,pw0,pw1,pw17,pw2,pw3,pw4],[8,9,28,12,273,433,49,429,193,297,417,333,61,5,277,29,313,205,37],[7,5,8,112,384,3584,12290,16384,98,32898,3074,65536,139296,384,271360,96,384,3072,96,96,384]),
([pw93,pw0,pw1,pw2,pw3,pw4],[277,8,9,28,313,5,433,0,49,24,429,16,193,4,417,333,345,149,205,145,369,3,124],[15,58,960,15360,49792,53,325,197633,49157,262256,529424,1065008,66880,49472,6312960]),
([pw0,pw162,pw1,pw2,pw36,pw3,pw4],[57,3,8,5,101,17,49,9,73,161,85,257,389,24,20,12,7,385,369,209,28,37,221,205,69,157,81,253,16,193,36,297,40,333],[7,25,97,128,769,3073,4096,24640,106496,131072,262144,524360,1114120,524296,6291464,8388608,50331712,201326656,1879048192,6442483712,11274289152]),
([pw88,pw0,pw1,pw17,pw2,pw3,pw4],[9,149,5,145,16,32,36,49,173,193,297,333,61,57,97,209,205,20,3,40],[3,12,112,384,512,3072,4101,8192,16513,3,3073,32768,65668,12,3076,393344,80,525376,384,3200,3072]),
([pw0,pw83,pw1,pw2,pw36,pw50,pw4],[57,3,193,5,101,17,49,9,345,429,85,257,129,44,16,15,313,48,7,72,205,81,253,36,325],[7,25,97,128,769,3073,4096,8260,49156,8452,8196,65608,393224,524552,65544,1048576,832,6291520,278784,8519680,16777216]),
([pw0,pw163,pw1,pw2,pw36,pw3,pw4],[277,57,5,101,17,49,349,73,161,389,273,12,345,193,333,369,297,209,433,385],[3,13,49,64,385,3,516,1056,2048,12288,114688,131108,516,516,516,262144,12320,1056,528384,98304,12288]),
([pw0,pw164,pw1,pw2,pw36,pw3,pw4],[57,181,5,101,17,49,9,85,257,145,173,16,24,36,193,297,333,369,209,48,32,221,205],[3,13,49,64,3,385,516,1056,14336,16384,229376,262180,1572868,516,2129924,4194304,1056,163872,10240,172032,163840]),
([pw1,pw17,pw2,pw50,pw3,pw45,pw4],[209,5,205,49,7,3,25,129,61,9,37,221,349,433,12,16,345,8,333,29,133,192,193],[1,14,50,194,770,3074,12292,20480,36864,20992,20480,8196,12,12,8196,65536,131072,262144,1573376,6291456,2097664]),
([pw1,pw17,pw2,pw3,pw45,pw4],[52,49,5,205,7,3,345,193,145,28,9,333,297,433,349,16,196,11,12,192,105],[1,62,452,1588,6149,24626,114784,50688,935937,202,1049610,6147,66753,6337,7169]),
([pw0,pw1,pw36,pw50,pw3,pw96,pw4],[57,5,101,9,3,68,73,161,17,49,85,257,389,12,433,16,429,20,417,69,157,200,193],[7,8,49,193,769,3073,4098,4098,4098,4610,4098,24608,49152,25088,24576,65536,131072,262144,1573376,6291456,2097664]),
([pw75,pw0,pw17,pw2,pw50,pw3,pw4],[61,5,9,209,205,49,32,25,129,37,221,57,3,172,29,41,389,433,12,16,345,333,48,193],[7,8,50,64,386,1538,2048,52,12292,24580,40964,196624,335872,589824,327680,131088,48,131088,1048576,2097152,12582912]),
([pw75,pw0,pw17,pw2,pw3,pw4],[28,5,8,152,68,145,237,205,9,49,105,193,345,149,297,333,241,433,389,3,429,16,417,12],[7,9,19,35,67,1,1920,14592,114944,917632,3409920,12861440,6784,180352,55296]),
([pw0,pw1,pw2,pw50,pw3,pw148,pw4],[61,9,5,17,97,349,57,205,49,389,209,433,44,3,345,172,333,193,4,204],[7,26,34,34,64,34,388,516,516,1024,516,2176,384,12416,2176,16384,32768,65536,397312,655360,266240]),
([pw46,pw0,pw1,pw17,pw2,pw3,pw4],[8,9,28,12,433,49,345,429,193,333,417,297,61,5,349,29,41,389,205],[7,5,8,48,448,3584,12290,16384,50,32898,66562,131072,270352,384,3072,48,384,3072,48,48,384]),
([pw46,pw0,pw1,pw2,pw50,pw3,pw4],[349,9,389,5,433,49,32,0,193,4,205,429,417,208],[3,12,48,64,896,640,3,49,3,3,3,1044,12,12,12,48,48,48,2048,4096,8448]),
([pw46,pw0,pw1,pw2,pw3,pw4],[349,8,9,28,389,5,433,20,49,24,429,0,193,4,417,297,105,172,205,3,212,11,208],[15,58,960,15360,59392,53,65857,132101,147461,786512,5168,49200,1574208,6308160,54272]),
([pw75,pw0,pw1,pw2,pw36,pw3,pw4],[57,105,5,49,24,20,28,7,345,193,333,297,17,9,3,389,205,16,36,40],[3,4,56,208,768,3072,3,4105,8192,769,3073,49160,49216,768,3072,65536,776,3080,393472,787456,768]),
([pw165,pw0,pw10,pw3,pw4],[20,68,17,197,205,309,349,5,1,9,145,237,44,297,333],[7,11,49,49,450,578,578,1154,2178,28672]),
([pw0,pw1,pw99,pw2,pw50,pw3,pw4],[209,9,101,57,349,17,45,5,49,205,32,3,313,12,16,193,4,297,0,68,20,253,345,333,44],[7,26,98,18,18,18,128,769,3073,4097,4097,768,11264,114688,401408,1573120,768,2228480,4194304,8388608,16941056]),
([pw34,pw0,pw2,pw10,pw50,pw3,pw4],[9,44,205,209,389,72,28,313,13,349,5,1,57,49,68,7,309,3,25,129,37,221,345,333,48,193],[1,14,16,104,136,10,772,3584,4640,4608,4608,8192,49156,65540,65540,132128,787456,3146752,4194304,8388608,50331648]),
([pw0,pw83,pw1,pw166,pw2,pw3,pw4],[9,149,313,1,49,45,41,225,209,20,205,193,297,369,5,25,345,429,333],[3,13,3,49,3,193,256,512,1040,2048,12288,16388,1044,98308,20484,1040,196608,266240,1040,12304,12288]),
([pw34,pw0,pw86,pw2,pw167,pw3,pw4],[9,16,209,49,309,313,297,333,57,181,205,28,193,417,69,345,25,5],[1,6,28,32,6,196,768,24,768,768,192,1024,2048,4096,8256,24,49160,24,229376,192,192]),
([pw34,pw0,pw1,pw87,pw2,pw3,pw4],[9,209,12,72,28,49,205,345,193,297,333,57,5,1,3,433,429,417],[1,2,28,96,384,1540,14336,18440,96,384,1536,24,96,384,1536,32768,65536,131072,96,1568,384]),
([pw88,pw34,pw0,pw1,pw2,pw3,pw4],[16,36,57,181,5,145,49,173,193,297,333,9,209,205,1],[3,12,48,192,256,1536,2048,4096,8256,3,1538,16404,8260,12,1540,8272,48,1552,192,1600,1536]),
([pw34,pw0,pw1,pw86,pw2,pw50,pw4],[9,209,16,193,48,49,309,385,345,36,297,40,57,5,1,73,85,221,157,68,325],[1,2,28,96,388,3584,28672,36872,96,384,70656,24,96,384,140288,262144,24,24,524448,96,1048576]),
([pw34,pw0,pw1,pw168,pw2,pw3,pw4],[9,209,16,36,49,205,297,417,57,5,1,181,85,145,193,253],[1,2,12,48,12,200,1792,2304,48,2304,4416,8704,48,8704,192,48,16384,192,48,32848,192]),
([pw0,pw1,pw2,pw50,pw3,pw169,pw4],[57,5,1,205,45,349,49,389,433,385,28,369,0,193,4,48],[7,25,33,33,33,33,74,130,130,130,130,264,72,72,264,512,1024,2048,28672,40960,20480]),
([pw34,pw0,pw2,pw50,pw3,pw120,pw4],[9,49,205,12,389,16,209,57,349,433,385,28,369,5,25,129,48,193],[1,6,24,48,64,24,6,384,384,384,384,514,6,6,514,1024,2048,4096,57344,196608,73728]),
([pw75,pw33,pw0,pw1,pw2,pw3,pw4],[20,68,9,349,5,345,193,333,297,57,389,3,28,205,49,45],[3,14,16,3,96,384,512,7168,8192,96,384,12,49156,12,12,19456,96,384,96,384,96]),
([pw0,pw83,pw1,pw2,pw170,pw3,pw4],[9,149,57,85,225,145,309,24,44,16,15,193,297,12,5,301,313,25,345,49,429,333],[3,5,5,5,3,25,32,448,1664,2048,12544,49216,81920,409600,86016,524288,1310784,2101312,1311232,2101248,2363392]),
([pw30,pw0,pw1,pw171,pw2,pw3,pw4],[9,149,313,389,16,32,56,173,345,297,333,57,5,309,49,193,157],[3,12,112,128,256,1536,2053,2049,2049,3,1537,4096,12,12,1540,24640,80,1536,106496,1536,1536]),
([pw102,pw0,pw21,pw1,pw2,pw3,pw4],[349,12,3,20,5,389,433,49,385,369,9,105,29,133,41,225,209,205,345,193,297,333],[1,14,48,200,256,512,3072,48,192,13312,50176,65536,131072,786432,3145730,84,48,48,192,192,786432]),
([pw102,pw0,pw1,pw2,pw10,pw3,pw4],[349,209,32,28,205,24,20,12,3,385,369,9,57,52,29,133,41,225,5,313,49,309,345,193],[1,14,112,388,512,1024,6146,6160,10496,51200,198656,274,262144,524290,524290,1048576,2097168,2097168,12582912,8320,12582912]),
([pw78,pw102,pw0,pw1,pw2,pw3,pw4],[12,3,24,57,9,5,205,193,36,16,40,349,209,32,28,49,433,385,369,29,41,225,93,313,333,297],[7,24,32,64,896,1025,2048,28672,98308,131072,262144,24,24,524424,3145736,4231168,8392832,8392704,98432,98304,50331776]),
([pw106,pw0,pw21,pw1,pw2,pw3,pw4],[9,149,16,36,5,145,49,173,193,297,333,105,57,209,205,3],[3,12,48,192,256,1536,2049,4113,2113,3,1537,8192,16384,12,1544,32848,48,1552,192,1600,1536]),
([pw106,pw0,pw1,pw2,pw10,pw3,pw4],[9,149,313,209,309,205,16,24,36,193,297,333,57,52,3,5,49],[3,12,48,448,512,3072,4101,4113,24577,3,3073,16404,32768,12,12,65536,48,48,320,3328,3072]),
([pw78,pw106,pw0,pw1,pw2,pw3,pw4],[16,36,57,9,5,205,40,149,313,209,49,173,193,297,333,93],[3,12,16,32,3,66,132,768,3072,4096,24576,12,12,132,24580,34048,768,768,3072,25600,24576]),
([pw32,pw0,pw21,pw10,pw3,pw4],[56,205,309,5,68,389,297,3,369,44,11,17,241,9,93,345],[1,7,56,17,1984,2067,56,17,12304,16401,7,7,25,56,32961]),
([pw32,pw0,pw21,pw1,pw2,pw50,pw4],[29,16,193,44,5,389,9,105,345,341,41,225,209,205,3,36,297,40,49,433,325],[1,14,52,12,12,12,192,48,192,832,3136,4096,8192,16642,229376,278544,48,48,786688,851968,1048576]),
([pw104,pw32,pw1,pw2,pw3,pw4],[349,9,24,4,1,57,209,45,205,341,68,241,32,297,3,369,11,72,233,269,144],[15,114,418,1546,3074,4177,389,1024,122881,464,131664,401424,1920,558208,1106432]),
([pw32,pw0,pw1,pw2,pw10,pw50,pw4],[29,313,193,189,309,185,16,64,44,9,57,3,345,341,41,225,5,72,209,49,68,205,36,297,40,325],[1,14,52,196,260,260,1538,1552,2688,12800,49664,2066,65536,135170,262146,524288,1052688,2097168,135232,29360128,33554432]),
([pw78,pw32,pw0,pw1,pw2,pw50,pw4],[193,64,16,9,57,5,205,3,345,297,40,36,29,313,189,49,433,44,341,41,93,72,209,325],[7,26,32,64,388,3584,4096,24577,98305,131329,131585,24,24,262408,524808,1089536,2105600,4203008,98560,98816,8388608]),
([pw32,pw0,pw172,pw1,pw2,pw50],[36,40,64,193,48,44,185,216,41,9,57,325,297,56,289,49,5,205,209,60,72,417],[1,7,26,106,19,389,1664,1664,2177,3,28673,7,491520,1574913,2099201]),
([pw0,pw21,pw53,pw10,pw3,pw4],[20,68,389,5,56,105,44,93,193,297,385,369],[3,1,14,50,98,3,131,273,577,14,1296,2624,14,14,336]),
([pw0,pw53,pw10,pw3,pw4],[20,68,201,17,5,56,345,44,333,389,3,385,309,11,369,205,297,193],[1,30,106,394,530,7264,61824,114,402,198112]),
([pw0,pw1,pw108,pw53,pw2,pw3,pw4],[61,105,5,20,56,333,297,145,389,3,49,173,193,309,16,369],[7,26,16,18,18,98,132,260,1540,20,100,16,3080,4096,96,9232,16400,32800,3072,80,80]),
([pw109,pw0,pw1,pw53,pw2,pw3,pw4],[56,5,389,433,49,385,297,369,105,333,3,16],[1,6,1,25,32,192,6,1,25,257,832,6,1033,3,6,25,2049,192,24,25,65]),
([pw0,pw1,pw53,pw2,pw50,pw3,pw4],[61,105,5,9,17,49,3,68,56,44,389,205,12,16,69,81],[7,8,50,194,258,514,1028,100,1028,260,516,2336,4160,8448,4608,416,16928,33056,512,256,768]),
([pw0,pw21,pw10,pw3,pw4],[20,68,17,349,5,1,9,93,205,309,145,237,44,297,333],[7,58,74,74,131,769,769,1042,2066,28672]),
([pw0,pw1,pw173,pw2,pw3,pw4],[313,28,5,309,20,49,385,16,345,297,40,333,69],[7,2,56,448,3584,7,7,195,7,56,448,3584,4248,56,3264]),
([pw1,pw173,pw2,pw3,pw4],[28,5,313,145,20,49,309,16,345,385,40,297,333,69],[7,7,11,7,112,896,7168,8368,112,5504]),
([pw174,pw0,pw1,pw2,pw4],[16,345,193,28,5,209,20,49,205,12,333,297],[7,7,7,7,56,448,3584,56,2584,2752]),
([pw110,pw0,pw1,pw2,pw3,pw4],[105,8,9,68,20,193,16,385,4,297,12,369,0,57,149,241,345,28,32],[15,8,24,480,7680,8201,13,16393,32777,24,458784,393728,24,24,2720]),
([pw110,pw0,pw1,pw3,pw4],[68,105,72,9,20,60,193,385,48,297,369],[15,21,224,1792,39,39,263,292,36,224]),
([pw110,pw0,pw21,pw10,pw3,pw4],[105,68,9,193,56,385,297,44,369,349,345,333],[7,0,0,56,448,7,515,19,131,0,56,208,1042,2178,56]),
([pw110,pw0,pw21,pw3,pw4],[68,105,3,9,5,56,193,385,44,297,369,93,345,333],[31,1,240,1808,2091,4131,8451,224,800,224]),
([pw110,pw0,pw10,pw3,pw4],[68,9,105,20,3,193,309,56,385,11,297,205,44,369,197,89,29,41,93,285],[7,9,496,15936,49155,65667,135171,278657,544769,5552]),
([pw0,pw21,pw60,pw10,pw3,pw4],[205,9,68,105,149,349,20,309,56,93,297,3,369,44,11,5,237,345],[15,22,38,22,38,449,772,385,385,260,4,31744,260,98308,134400]),
([pw0,pw21,pw10,pw50,pw3,pw4],[205,9,3,105,44,389,349,5,68,193,56,297,11,93],[31,226,326,1606,6162,8212,21,1553,3089,420,1700,6288,16,1040,1552]),
([pw0,pw21,pw1,pw2,pw3,pw45,pw4],[349,3,52,5,389,49,433,193,345,9,297,333,209,205,20,28,32,24],[7,25,97,385,512,3073,4096,8192,384,16386,3076,42,24,98312,24,96,147488,96,384,384,3072]),
([pw0,pw1,pw2,pw50,pw3,pw52,pw4],[57,5,1,9,349,3,49,389,433,44,56],[7,9,17,17,17,17,98,130,130,130,130,320,320,320,320,512,512,1024,512,1536,1536]),
([pw0,pw1,pw2,pw3,pw52,pw4],[389,57,5,9,433,49,193,56,3,8,105,297,44,11,48],[15,58,450,1794,14338,16785,16581,16389,22533,240,176,176,4288,6336,128]),
([pw104,pw0,pw1,pw2,pw50,pw3,pw4],[9,5,209,49,205,12,68,3,16,193,4,297,0,349,11,32,221,7,253,345,333,140],[1,6,24,224,1792,6176,6,24,8384,8832,26624,6,32898,6,67586,131144,24,264200,524288,1048576,2099712]),
([pw0,pw1,pw2,pw115,pw10,pw3,pw4],[57,9,3,68,349,209,205,20,28,5,313,49,309,220,385,369,345,193,333,297],[3,3,13,17,17,17,100,416,512,1056,1056,200,2048,4160,4160,8192,16384,32768,196608,786432,196608]),
([pw116,pw0,pw1,pw2,pw10,pw3,pw4],[9,149,313,209,309,205,0,4,16,36,193,297,333,57,349,3,5,49],[3,12,48,960,1024,6144,8197,8209,16385,3,6145,32788,65536,12,12,131072,48,48,768,6656,6144]),
([pw0,pw1,pw2,pw60,pw119,pw3,pw4],[57,5,1,9,149,241,205,49,209,313,309,12,44,193,345,56,16,297,3,325],[7,9,17,33,17,33,194,258,514,258,514,192,1088,192,1088,6144,8192,6144,114688,131072,802816]),
([pw0,pw1,pw2,pw60,pw10,pw50,pw4],[57,9,29,133,349,3,209,205,313,5,32,345,309,49,24,4,193,44,297,40,325],[3,3,13,17,17,17,224,320,512,3136,320,4224,8192,18560,4224,32768,3072,196608,3072,786464,1048576]),
([pw0,pw1,pw2,pw175,pw3,pw4],[209,181,5,149,205,49,16,345,68,40,4,313,32,72,309,297,333],[15,58,64,450,770,53,7169,8389,8705,17680,496,784,448,98816,66240]),
([pw0,pw1,pw2,pw10,pw3,pw45,pw4],[209,7,349,3,205,52,193,345,9,297,333,5,32,28,49,24,20],[7,28,38,196,256,1540,19,2048,193,12289,1537,16384,208,98320,1552,192,4098,1568,192,192,1536]),
([pw0,pw1,pw10,pw50,pw3,pw96,pw4],[57,9,349,5,209,3,313,48,205,12,433,16,429,20,417,224,193],[3,5,5,5,3,5,8,48,80,400,80,1536,3072,384,1536,4096,8192,16384,384,98304,384]),
([pw75,pw0,pw2,pw10,pw50,pw3,pw4],[57,9,44,205,209,5,32,349,49,3,309,12,389,16,345,333,48,193],[3,28,32,64,20,20,3,129,129,129,129,256,520,1032,1032,6144,12288,6144,16384,32768,196608]),
([pw75,pw0,pw2,pw10,pw3,pw4],[57,209,9,3,28,20,7,5,313,205,389,349,193,345,297,333,309,16,12],[31,50,208,274,274,525,3081,14337,51201,16,78336,115200,144384,312320,61440]),
([pw0,pw1,pw2,pw50,pw3,pw176,pw4],[57,9,349,52,3,389,205,209,313,5,433,309,49,385,220,369,193,228,4],[3,3,5,5,25,5,224,160,288,512,160,1088,2112,4096,1088,8192,16384,32768,81928,196608,262152]),
([pw76,pw0,pw1,pw2,pw10,pw3,pw4],[349,9,28,209,20,12,345,193,333,297,17,57,3,205,389,433],[3,28,20,32,192,768,3,3073,3,3,3,12296,16384,200,776,32768,192,768,192,768,192]),
([pw76,pw0,pw1,pw2,pw50,pw3,pw4],[349,9,389,209,433,205,24,0,193,4,17,313,309,345,333,220],[3,12,48,64,896,640,3,1041,3,3,3,12,12,2308,12,48,4368,48,8192,16384,33024]),
([pw76,pw0,pw1,pw2,pw3,pw4],[349,8,9,3,389,12,209,20,433,205,24,345,0,193,333,297,7,57,313,309],[15,240,1824,15360,50208,65565,196873,10245,49157,848,272400,49232,534784,49920,59392]),
([pw0,pw125,pw1,pw2,pw50,pw3,pw4],[57,209,5,9,49,97,3,68,29,133,41,225,205,433,12,193,4,16,0,72,28,37,221,345,333,48],[1,6,56,200,776,3080,6,12304,16576,229376,278528,6,1572866,6,6291458,8336,8208,8208,8388608,16777216,33587200]),
([pw0,pw1,pw2,pw50,pw3,pw107,pw4],[57,9,349,49,209,93,389,313,433,385,24,369,193,4,0,48],[3,3,5,5,3,5,56,80,144,80,80,264,264,264,264,512,1024,2048,28672,36864,24576]),
([pw0,pw1,pw2,pw3,pw107,pw4],[209,57,7,9,48,433,49,193,60,3,8,297,11,389,385,12,24,369],[31,106,898,1546,6162,8209,401,8209,2321,16864,98400,133200,16,400,272]),
([pw78,pw0,pw1,pw2,pw3,pw45,pw4],[349,3,52,5,205,193,36,16,24,7,209,49,433,345,9,297,333,93,32,28,20],[7,8,16,224,770,68,1027,6145,8225,16384,98305,134144,9248,787456,99328,6176,1050880,6144,8224,8224,98304]),
([pw78,pw0,pw2,pw50,pw3,pw120,pw4],[57,9,205,12,389,193,16,5,349,49,433,385,28,369,313,189,48,209],[3,4,24,112,128,24,3,257,289,3,257,1536,1568,1536,1536,2048,4096,8192,49184,65568,147456]),
([pw78,pw0,pw2,pw3,pw120,pw4],[57,389,9,72,193,16,385,48,5,297,369,149,49,173,20,209],[15,8,114,392,1666,13,2057,13,137,12368,53256,1664,136,1744,32904]),
([pw0,pw1,pw66,pw2,pw91,pw3,pw4],[313,5,9,149,3,205,64,7,429,345,333,297,25,56,24,49],[3,4,56,200,776,3080,3,3,3,4353,3,24608,24640,768,3072,32768,800,3104,832,3072,3328]),
([pw79,pw0,pw1,pw2,pw67,pw3,pw4],[277,3,52,5,205,49,32,28,345,193,333,369,313,9,81],[7,8,52,196,768,3076,4099,49,8192,769,3073,48,4226,768,3072,48,48,17424,768,3072,768]),
([pw92,pw0,pw83,pw1,pw2,pw3,pw4],[57,149,16,64,313,5,49,297,333,145,309,24,15,193,369,25,345,429],[3,12,56,64,12,384,3,3,3,3,385,512,7168,8192,16512,48,98320,48,197632,384,384]),
([pw0,pw64,pw1,pw2,pw47,pw3,pw4],[181,16,64,3,313,309,49,57,73,345,333,297,5,20,32,40,15,28,385,69],[7,25,97,128,769,3073,4096,8228,16384,6,99328,112,131096,262672,3088,96,524832,96,262656,3072,3584]),
([pw0,pw1,pw66,pw2,pw161,pw3,pw4],[313,5,57,149,49,205,7,29,345,333,297,28,72,25,24,20,429,309,60,3,40],[3,4,56,64,392,1544,3,3,6145,8449,3,16464,32768,65792,1536,131072,48,1552,266496,1573376,1792]),
([pw92,pw0,pw1,pw66,pw2,pw3,pw4],[64,149,16,313,5,20,49,297,333,57,3,309,29,345,25,24,15,429],[7,25,32,64,5,384,26,512,3074,12290,386,24,24,24584,24,100352,139264,384,141312,384,384]),
([pw136,pw0,pw1,pw2,pw67,pw3,pw4],[3,209,49,205,32,345,193,333,369,277,5,313,57,28,81],[1,2,12,16,96,384,3584,12,4096,96,384,12,9217,96,384,12,12,16516,96,384,96]),
([pw0,pw1,pw177,pw133,pw2,pw3,pw4],[209,5,241,12,36,49,205,145,37,221,173,345,333,417,16,193,405],[3,28,16,100,20,20,129,3,3,3,769,16,1056,2048,12296,96,16400,12304,48,12304,102400]),
([pw137,pw0,pw1,pw2,pw67,pw3,pw4],[36,5,209,49,205,193,369,333,277,81,16,3,325],[1,6,24,1,32,193,6,24,1,257,193,6,6,3,193,24,9,577,1025,193,6208]),
([pw0,pw83,pw1,pw2,pw67,pw3,pw4],[277,3,52,5,313,205,49,9,345,429,85,333,145,16,7,15,193,369,28,32,25,81,4],[7,25,97,128,769,3073,4096,96,57344,65536,133124,24,786440,1048840,24,96,96,2099232,4202752,133120,2306]),
([pw30,pw0,pw1,pw133,pw2,pw3,pw4],[241,3,52,5,145,16,56,173,345,417,333,209,9,49,309,36,37,24,193,405],[7,24,96,128,256,1540,2057,4096,24577,32769,1537,2056,2056,24,66056,139328,96,1536,40960,1536,786944]),
([pw0,pw1,pw66,pw2,pw50,pw4],[313,48,5,205,29,49,3,160,16,345,72,309,44,193,429,297,15,325],[7,2,248,912,146,7,7,1283,7,14344,17152,106498,17160,98314,131330]),
([pw129,pw0,pw1,pw86,pw2,pw3,pw4],[9,5,209,16,60,49,309,333,297,57,3,72,345,341,173,193,417,69],[1,6,24,112,24,384,6,3584,96,12800,384,6,6,6,386,16384,32768,65664,135200,96,384]),
([pw0,pw130,pw1,pw160,pw2,pw3,pw4],[57,61,9,5,3,148,17,29,41,32,20,49,24,429,193,12,333,0,313,273,417,157,81],[1,14,52,100,164,292,40,544,7168,24576,229376,262184,264200,24584,327688,524288,24576,1048576,2107392,4261888,24576]),
([pw0,pw130,pw1,pw2,pw3,pw4],[28,5,313,205,9,49,105,193,345,149,369,333,241,433,20,24,429,16,4,417,12,0,145,60],[1,7,120,912,7184,7,57352,458880,3671040,7,4194435,7,424,533512,8390016]),
([pw0,pw1,pw94,pw2,pw3,pw4],[209,28,5,205,152,3,49,7,16,345,12,333,37,20,24,193,297],[7,2,248,784,3088,7,7,7,5123,24648,272,1040,33608,68616,1792]),
([pw1,pw94,pw2,pw3,pw4],[28,5,209,237,7,205,9,3,49,57,16,345,193,12,333,297],[7,7,7,11,1008,7232,57408,7456,57376,7168]),
([pw0,pw1,pw178,pw3,pw4],[28,5,209,24,205,49,16,345,193,12,333,297],[7,56,448,3584,7,7,2563,56,1560,448]),
([pw179,pw0,pw2,pw3,pw4],[28,5,209,237,20,49,205,16,345,193,12,333,297],[7,7,7,11,112,896,7168,112,5168,896]),
([pw0,pw1,pw2,pw144,pw3,pw4],[209,57,5,9,309,49,8,3,181,385,345,417,333,241,0,16,40,36],[15,58,450,1794,14338,53,49157,1541,198657,131120,197136,6192,99840,88064,68224]),
([pw0,pw83,pw1,pw160,pw2,pw50],[193,9,15,149,40,313,57,5,297,3,277,36,205,49,325,369,7,44,48,429],[31,226,3842,12354,49170,2064,67601,135185,49169,264608,12448,49168,16,542736,540688]),
([pw0,pw139,pw172,pw1,pw2,pw3,pw4],[9,149,3,64,209,5,49,169,29,345,333,329,12,56,68,205,309,193,417,237,16,297,37],[1,14,50,194,770,3074,28672,48,98368,131584,267264,524288,24640,1049096,2097152,48,48,4195344,131648,66624,132608]),
([pw0,pw83,pw2,pw120,pw4],[16,72,29,57,9,241,193,385,129,5,313,36,369,40,297],[7,26,26,42,193,259,193,1538,30720,1538]),
([pw30,pw0,pw180,pw1,pw2,pw3,pw4],[277,349,16,48,56,145,5,173,345,297,333,9,209,49,309,193,157],[3,28,104,128,256,1544,2048,4129,3,3,1537,4128,24592,20,1536,4128,96,1568,106496,1536,1536]),
([pw0,pw1,pw181,pw2,pw3,pw4],[389,28,5,205,9,49,105,193,345,149,297,333,44,433,385,16,4,417],[7,2,120,912,7184,7,4107,7,7,12296,114816,136192,424,7176,3456]),
([pw0,pw1,pw2,pw3,pw45,pw120,pw4],[349,7,389,49,205,193,16,52,3,297,12,48,32,253,36,232],[7,25,97,64,385,1537,28,100,6148,64,1540,24,24,24,8712,16480,16480,32864,6272,3584,1664]),
([pw75,pw0,pw1,pw2,pw3,pw45,pw4],[349,3,52,5,49,205,193,345,32,28,333,297,389,9],[7,8,48,196,772,3076,4099,49,193,8192,3073,48,192,4610,3072,48,48,3088,192,192,3072]),
([pw97,pw0,pw1,pw2,pw50,pw3,pw4],[57,349,209,5,49,12,52,193,16,389,205,24,7,309,345,333,236],[3,12,16,96,448,96,13,3,3,3,3,12,516,12,516,7168,9344,9216,16384,32768,65664]),
([pw0,pw73,pw1,pw2,pw3,pw45,pw4],[349,12,52,3,209,49,205,193,345,57,297,333,5,7,16,32,28],[7,25,97,385,512,3073,4096,8232,16516,32768,6,112,400,65560,3088,96,96,3104,384,384,3072]),
([pw0,pw1,pw2,pw3,pw45,pw148,pw4],[349,5,389,49,205,193,345,9,3,297,333,32,209,7,16,36,28,40],[7,25,97,128,256,1537,26,6,2306,4096,6,24,24,8456,1544,96,49184,96,65536,1536,164352]),
([pw150,pw0,pw1,pw2,pw3,pw45,pw4],[3,209,49,205,345,193,32,333,297,349,5,389,57,28],[1,2,12,48,64,384,3584,12,48,4096,384,12,48,9217,384,12,12,388,48,48,384]),
([pw97,pw0,pw1,pw2,pw3,pw45,pw4],[52,349,12,209,5,49,193,345,20,3,205,57,297,333,24,7],[7,24,32,193,256,5,26,1538,194,2048,12290,24,24,24,12296,192,50176,13312,192,192,12288]),
([pw145,pw0,pw1,pw2,pw50,pw3,pw4],[9,5,389,49,205,12,48,16,57,3,72,73,161,85,257,433,345,333,240,193],[1,6,24,96,192,96,6,24,1792,6400,24832,26,6,6,6,32776,24,32776,65536,131072,786432]),
([pw0,pw1,pw2,pw3,pw120,pw96,pw4],[57,9,29,133,41,225,389,3,433,16,48,32,12,44,24,193,429,385,244],[3,3,13,3,3,49,448,576,512,3136,4160,768,24832,512,4352,98816,164352,266752,3072,12288,5120]),
([pw75,pw0,pw1,pw2,pw3,pw96,pw4],[57,9,5,433,24,44,193,429,417,297,29,41,3,389,28,16,12,345,333],[3,4,56,224,48,800,3,3,1089,3,2305,12296,192,28672,768,32840,32768,65800,163904,192,327936]),
([pw182,pw0,pw1,pw2,pw50,pw3,pw4],[57,9,209,389,205,12,48,193,16,349,313,49,24,7,157,81,253,385,369,248],[3,12,16,96,448,96,3,3,513,641,513,12,12,1156,12,14336,18560,100352,131072,262144,524416]),
([pw0,pw122,pw1,pw2,pw50,pw3,pw4],[57,61,9,5,17,97,3,172,29,41,433,49,32,16,193,4,12,297,0,205,389,345,333,48],[1,14,52,196,388,644,136,3072,4224,57344,458752,525320,1048712,1064968,1179656,3072,3072,3072,2097152,4194304,8536064]),
([pw0,pw1,pw152,pw2,pw50,pw3,pw4],[57,9,349,5,433,205,209,32,3,313,12,220,16,193,309,345,333,44],[3,5,3,5,5,5,8,48,448,576,576,48,3200,14336,3072,48,24592,48,32768,65536,139264]),
([pw75,pw121,pw0,pw1,pw2,pw3,pw4],[20,220,24,57,9,5,7,433,345,193,333,297,389,3,28,49],[7,24,32,193,768,3072,24,28672,32768,768,3072,24,24,776,3080,4288,768,3072,896,3200,768]),
([pw0,pw122,pw1,pw2,pw3,pw4],[28,5,389,205,9,49,105,193,345,149,297,333,241,433,20,24,429,16,4,417,12,0,3],[1,7,120,912,7184,7,57352,458880,3671040,4194315,7,7,424,11272,3456])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p7_D5 : List StD := [
([pw1,pw36,pw10,pw3,pw45,pw4],[349,205,5,313,193,189,17,13,209,309,49,157,3,81,253,73,333,297],[3,4,56,200,264,3,529,3,3,3088,5184,25600,32848,196624,196672]),
([pw75,pw0,pw36,pw10,pw3,pw4],[57,17,28,205,5,313,193,189,209,9,389,49,73,85,229,309,333,297],[3,12,16,224,288,512,3073,4161,24577,12,32840,32776,3136,3072,196672]),
([pw46,pw0,pw2,pw10,pw3,pw4],[209,9,57,20,389,5,313,17,53,29,133,41,225,49,309,193,185,205,417,297],[7,9,49,65,65,386,50,1538,6146,8192,114688,147456,48,48,819200]),
([pw76,pw0,pw1,pw36,pw3,pw4],[8,17,49,209,5,433,205,69,157,81,253,13,9,73,137,85,229,313,309,193,333,297],[7,28,100,388,1540,2058,4096,24578,98306,104,131080,131080,262176,96,3670016]),
([pw0,pw1,pw36,pw3,pw77,pw4],[57,5,17,9,73,137,85,229,389,309,193,185,49,433,205,69,417,297],[7,8,49,5,193,258,258,258,258,3584,12800,16896,37888,197632,200704]),
([pw78,pw17,pw2,pw3,pw45,pw4],[389,205,5,25,129,61,9,37,221,349,49,197,313,209,69,157,81,253,29,133,193,333,297],[1,2,28,100,388,3584,4608,4640,8704,50176,96,197632,786464,7340032,6291488]),
([pw46,pw78,pw0,pw2,pw3,pw4],[209,5,389,9,57,433,49,313,205,29,133,41,225,193,417,297],[7,25,97,129,129,6,256,6,6,104,1544,6152,96,96,57344]),
([pw79,pw80,pw0,pw2,pw3,pw4],[5,57,9,49,205,345,193,297,333,361,293,313,225,81],[1,6,24,96,896,6,24,96,3328,6,98,4354,24,8456,96]),
([pw81,pw0,pw1,pw17,pw2,pw4],[9,29,133,5,25,129,429,193,49,157,61,57,97,41,225,209,205,37,221,433,417,297],[7,56,192,832,192,1033,2048,4353,24577,32768,65800,393224,524544,3145728,524544]),
([pw82,pw66,pw2,pw36,pw3,pw4],[57,5,101,313,149,25,129,17,49,389,177,69,157,81,253,381,60,345,365,337,297,325],[7,10,16,98,10,385,513,513,513,1024,6400,24832,229376,786432,3276800]),
([pw0,pw82,pw83,pw2,pw84,pw4],[57,5,1,381,377,17,45,73,161,85,257,24,313,25,345,297,353,69,49,253,325],[7,25,97,385,1537,2066,4098,24578,4098,2064,2064,98320,409600,819200,1097728]),
([pw1,pw2,pw15,pw3,pw45,pw4],[5,205,49,389,25,129,57,9,37,221,433,81,253,16,193,349,12,29,333,297],[7,8,49,193,769,1024,6,6,6146,57344,41024,98304,147520,802816,786496]),
([pw75,pw0,pw2,pw15,pw3,pw4],[57,5,9,205,49,7,25,129,37,221,349,29,133,41,225,433,81,253,16,193,377,12,297,361,333],[7,26,32,194,770,5,1024,6145,24577,32768,24,196616,1835008,14680064,21495808]),
([pw39,pw0,pw1,pw2,pw3,pw4],[349,9,389,5,433,49,345,4,193,297,0,205,3],[3,12,48,448,1664,3,49,3,3,2068,12,12,48,48,4864]),
([pw85,pw80,pw0,pw2,pw3,pw4],[5,57,9,49,205,345,193,297,333,361,221,237,217,81],[1,6,24,96,896,6,24,96,3328,6,98,4354,24,8456,96]),
([pw41,pw0,pw1,pw43,pw86,pw4],[45,9,49,5,301,345,69,173,253,81,133,73,421,41,225,25,32,297,325,401],[3,28,100,128,772,3,1057,6145,24577,32808,69640,24,69664,393248,659456]),
([pw41,pw1,pw17,pw47,pw3,pw4],[49,5,309,20,157,69,209,61,9,25,129,37,221,433,73,181,345,297,417],[7,8,5,49,5,64,386,1538,6146,8448,114688,425984,8448,8448,458752]),
([pw41,pw0,pw1,pw87,pw3,pw4],[45,9,49,5,197,3,157,69,253,81,433,29,133,41,225,32,37,221,421,413,193,333,297],[3,28,32,196,772,3,1057,6145,24577,33800,24,196616,262144,524288,7340032]),
([pw41,pw88,pw0,pw1,pw3,pw4],[49,173,45,9,5,197,253,81,149,193,297,333],[3,13,49,3,193,260,48,512,3072,12,260,3076,48,3088,3072]),
([pw41,pw0,pw1,pw86,pw50,pw4],[45,9,49,5,209,157,345,24,253,81,73,153,385,41,225,37,221,193,433,325],[3,28,32,196,772,3,3073,4161,24577,24,4168,98312,192,393216,524288]),
([pw0,pw1,pw2,pw3,pw89,pw4],[57,5,9,29,133,41,225,209,37,221,345,193,49,433,24,333,297],[7,5,25,5,97,130,130,130,770,3072,28672,106496,3072,3072,114688]),
([pw41,pw1,pw2,pw3,pw45,pw4],[209,5,49,193,345,57,9,297,333],[3,4,24,96,384,3,3,3,385,24,96,384,24,24,416]),
([pw75,pw41,pw0,pw2,pw3,pw4],[209,5,37,221,57,9,49,193,345,297,333],[3,3,3,3,13,48,64,384,1536,48,400,1552,384,1536,384]),
([pw90,pw0,pw2,pw36,pw3,pw4],[57,5,101,209,389,17,49,9,73,161,85,257,205,69,157,81,253,385,193,369,297],[7,10,18,10,18,97,128,769,3073,4096,24640,98368,393216,1572864,393216]),
([pw0,pw1,pw43,pw44,pw2,pw50],[57,5,1,29,133,41,225,9,3,405,25,129,37,221,205,49,409,193,48,81,253,32,401],[7,25,97,129,769,3074,12290,49154,66050,393216,49152,393728,1589248,2097664,4211200]),
([pw1,pw43,pw17,pw2,pw47,pw4],[5,25,129,113,309,49,61,9,37,221,181,69,157,29,133,297,333,425,73,429,265],[7,8,49,193,769,1024,6160,24704,98304,393232,786560,1343488,48,48,98432]),
([pw1,pw43,pw17,pw2,pw45,pw4],[5,25,129,245,205,49,61,9,37,221,349,29,133,193,333,297,425,281,429,3,40],[7,8,49,193,769,1024,48,6272,57344,196624,262272,1589248,48,49168,49280]),
([pw1,pw66,pw36,pw91,pw3,pw4],[57,5,101,177,149,313,25,345,16,17,49,137,85,257,297,369,69,253],[7,26,34,194,34,273,1537,2177,12289,272,400,49168,66688,148480,49280]),
([pw79,pw17,pw2,pw67,pw3,pw4],[209,5,205,49,61,9,25,129,37,221,20,277,193,429,85,333,81,225],[1,14,50,194,770,3076,3104,14336,51200,12,12,98308,12320,163872,12288]),
([pw64,pw17,pw2,pw47,pw3,pw4],[209,5,64,9,37,221,389,49,181,73,313,305,53,69,157,81,253,61,345,165,333,261,297],[1,6,8,6,50,448,320,1600,320,6272,24704,98432,917504,3276800,5505024]),
([pw92,pw1,pw66,pw36,pw3,pw4],[49,5,313,17,205,149,157,69,253,81,433,25,129,57,73,161,85,257,29,309,297,333],[7,8,49,193,769,6,1058,6146,6,1056,57344,204800,786464,1056,3145728]),
([pw1,pw66,pw2,pw36,pw50,pw4],[57,5,101,313,48,29,72,345,17,49,385,85,257,109,429,81,253,7,325],[7,10,50,194,10,769,49,1089,6145,8192,17024,98816,131232,48,262144]),
([pw93,pw0,pw1,pw2,pw50,pw3],[257,9,293,5,253,297,49,333,417,193,4,29,369,129,157,325],[3,12,112,416,1568,3,3,385,2561,12,4228,8708,448,16960,32768]),
([pw1,pw94,pw2,pw36,pw3,pw4],[57,5,101,209,28,7,37,221,17,49,9,73,161,85,257,205,69,157,81,253,16,193,36,297,40,333],[7,10,50,10,194,769,1041,6145,24577,32768,197120,786944,7340032,29360128,44040192]),
([pw95,pw0,pw1,pw2,pw3,pw4],[8,9,57,12,433,49,429,193,297,417,61,5,29,41,205],[7,9,48,192,776,3074,50,4162,8450,18448,192,768,48,48,192]),
([pw46,pw0,pw1,pw86,pw2,pw4],[341,9,345,5,209,193,429,49,24,325,297,3,97,309,221,157],[3,28,100,388,1540,3,2081,4225,3,104,8328,17416,32768,96,9344]),
([pw1,pw36,pw3,pw45,pw96,pw4],[349,5,389,57,101,281,193,12,73,49,157,252,17],[7,6,26,6,6,97,137,129,129,328,1600,2112,4616,2056,2560]),
([pw75,pw17,pw2,pw3,pw45,pw4],[209,5,205,49,25,129,61,9,37,221,349,433,16,12,29,133,193,333,297],[1,14,50,194,770,3076,5120,5248,9216,12,12,2052,49280,458752,393344]),
([pw73,pw17,pw2,pw3,pw45,pw4],[389,5,3,49,25,129,9,37,221,349,197,313,209,69,157,201,53,81,253,61,345,165,193,333,261],[1,14,50,64,386,1544,2560,2560,4608,24584,98312,393224,3670016,5242880,25690112]),
([pw97,pw1,pw36,pw3,pw45,pw4],[49,5,209,205,349,157,69,17,253,81,37,221,309,57,73,161,193,333,297],[7,25,97,128,769,26,6,6,3074,4104,24,24,57344,458752,401408]),
([pw49,pw0,pw1,pw50,pw3,pw4],[45,9,49,5,197,433,349,389,345,333,3,297,193],[3,28,36,36,36,3,65,65,65,136,24,136,256,512,7168]),
([pw0,pw1,pw98,pw2,pw3,pw4],[57,5,9,29,133,41,225,209,37,221,49,433,12,193,345,333,297],[7,5,5,25,97,130,130,130,770,7168,24576,102400,26624,100352,24576]),
([pw75,pw0,pw99,pw2,pw3,pw4],[209,9,101,5,49,205,313,57,349,345,193,333,297],[7,8,49,65,65,386,50,258,258,48,1536,6144,48,6160,1536]),
([pw100,pw0,pw1,pw2,pw3,pw4],[57,349,9,389,209,49,205,345,193,333,297],[7,24,96,384,1536,6,98,6,6,24,392,24,96,1568,384]),
([pw75,pw33,pw0,pw10,pw3,pw4],[20,205,209,9,349,5,313,17,433,309,49,69,157,81,253,193,333,297],[7,28,32,68,68,128,256,514,514,24,24,24,7168,25600,229376]),
([pw76,pw34,pw0,pw2,pw3,pw4],[5,209,389,349,1,205,49,25,129,37,221,9,313,13,57,309,193,333,297],[7,25,97,385,1537,2048,6,4098,6,8232,16392,16392,32800,32800,458752]),
([pw34,pw1,pw2,pw42,pw3,pw4],[209,49,205,9,57,12,345,193,297,333,5,1],[1,6,56,192,800,6,3088,192,768,6,6,770,208,784,192]),
([pw101,pw0,pw1,pw2,pw3,pw4],[57,9,313,209,49,205,345,193,297,333,369,81],[3,12,48,192,1792,3,3,193,1537,52,12,12,48,2576,192]),
([pw0,pw1,pw51,pw2,pw3,pw4],[57,5,1,105,9,29,133,41,225,389,3,49,433,345,193,333,297],[7,9,17,97,385,514,3074,514,514,6144,24576,98304,6144,6144,24576]),
([pw102,pw0,pw21,pw10,pw3,pw4],[349,205,3,20,5,389,385,369,17,9,29,133,41,225,93,309,193,333,297],[1,14,48,64,128,770,48,3584,12800,16384,32770,32770,48,48,458752]),
([pw103,pw0,pw1,pw2,pw3,pw4],[349,9,389,209,433,205,345,193,333,297,17],[3,12,48,192,768,3,1041,3,3,12,196,12,208,48,192]),
([pw104,pw102,pw1,pw2,pw3,pw4],[9,24,349,1,57,133,29,225,41,397,385,369,205,45,21,125,33,217,77,249,193,329,297],[7,25,17,97,385,524,6,1024,2048,12296,49160,196616,12288,790528,7340032]),
([pw105,pw0,pw1,pw2,pw3,pw4],[57,9,209,389,49,205,433,193,385,297,369,29,41,313],[3,12,112,384,1536,3,3,2177,4609,12,8324,12,80,80,384]),
([pw106,pw0,pw21,pw10,pw3,pw4],[9,149,309,205,5,145,193,297,333,17,389,93],[3,12,48,64,384,517,1041,3,385,2048,12,12,48,400,384]),
([pw104,pw106,pw1,pw2,pw3,pw4],[9,149,1,57,225,41,141,45,169,193,297,329,205],[3,13,9,3,49,68,384,512,3072,4228,68,3076,384,3200,3072]),
([pw32,pw0,pw21,pw10,pw50,pw4],[29,309,193,185,5,389,44,17,9,345,341,41,225,93,3,205,325],[1,14,52,68,68,386,48,1792,6400,8192,16898,32770,48,48,65536]),
([pw32,pw0,pw1,pw2,pw52,pw4],[29,5,193,389,49,433,345,385,44,9,105,41,225,3,4],[1,14,52,196,260,10,48,1600,6656,8210,10,10,48,48,16448]),
([pw104,pw32,pw1,pw2,pw50,pw4],[9,193,29,1,57,393,341,225,41,189,45,185,349,205,72,33,217,68,77,249,321],[7,25,17,97,385,522,3074,4162,4098,9224,16456,98312,132160,787456,1048576]),
([pw32,pw0,pw1,pw2,pw107,pw4],[29,313,193,189,49,385,9,57,41,225,93,389,209,205,345,81,253,297,325],[1,14,52,36,36,194,208,192,832,1042,2050,4098,24592,98320,409600]),
([pw0,pw108,pw53,pw10,pw3,pw4],[17,20,56,201,5,333,229,145,193,297,389,309,369],[7,4,25,5,97,4,144,256,544,1040,2052,6176,20,560,516]),
([pw109,pw0,pw53,pw10,pw3,pw4],[56,5,389,385,297,369,17,333,309],[1,1,6,8,48,1,6,65,208,6,257,48,3,6,17]),
([pw0,pw53,pw10,pw50,pw3,pw4],[9,201,17,5,3,68,56,44,389,205,309],[1,14,52,68,132,264,528,1088,640,296,72,136,128,64,192]),
([pw1,pw53,pw2,pw3,pw45,pw4],[349,5,209,3,49,25,129,61,105,37,221,205,16,12,69,157,17,81,253,345,193,333,297],[7,26,98,386,1538,2065,4097,4353,8193,49168,65808,393232,1573120,1572864,6291712]),
([pw0,pw1,pw2,pw3,pw54,pw4],[61,105,5,17,49,345,193,9,333,297,3,24,209,20,0,385,4],[7,26,98,128,770,1044,100,6148,772,112,10256,784,49184,96,82176]),
([pw55,pw0,pw1,pw2,pw3,pw4],[349,105,389,5,433,49,345,385,193,333,369,297,3],[3,12,48,448,3584,3,3,3,3,4116,12,12,48,48,384]),
([pw110,pw0,pw111,pw21,pw3,pw4],[68,5,25,129,37,221,105,93,29,9,41,193,345,297,333],[3,1,1,14,50,64,129,769,1537,1,6144,24576,6272,24704,6144]),
([pw112,pw110,pw0,pw21,pw3,pw4],[389,9,68,193,385,297,369,5,93,345,333],[1,2,4,24,96,132,4,24,96,260,516,1028,24,96,24]),
([pw113,pw110,pw0,pw10,pw3,pw4],[205,9,149,56,385,297,369,97,17,309,197,89,41,93,285],[1,6,8,16,96,386,8,520,96,3074,6,4130,8200,17440,40]),
([pw110,pw0,pw114,pw10,pw3,pw4],[97,17,205,5,309,385,56,289,369,9,349,193,333,93,297],[3,4,8,112,400,1536,1536,608,1792,64,2048,4352,8288,4352,16480]),
([pw110,pw0,pw10,pw50,pw3,pw4],[97,17,5,205,3,185,309,197,9,89,349,437,93,345,333,44,193],[3,4,24,104,72,896,1280,1280,1280,2176,4224,2176,8192,16384,98304]),
([pw0,pw21,pw115,pw10,pw3,pw4],[9,17,97,3,68,349,205,20,93,309,389,385,369,5,25,129,37,221,193,333,297],[7,25,33,33,33,200,256,576,576,1024,2048,4096,57344,204800,1835008]),
([pw116,pw0,pw21,pw10,pw3,pw4],[9,149,309,205,5,145,193,297,333,17,349,93],[3,12,48,64,384,517,1041,3,385,2048,12,12,48,400,384]),
([pw0,pw21,pw60,pw10,pw50,pw4],[9,17,97,29,133,349,309,193,185,93,3,345,205,129,24,44,5,37,221,325],[7,25,33,33,33,448,512,3136,4160,8192,18560,32896,18432,458752,524288]),
([pw0,pw21,pw10,pw3,pw45,pw4],[205,3,349,5,389,193,345,9,297,333,93,20,24],[7,28,100,128,772,1024,97,2051,769,24,4106,24,96,96,768]),
([pw0,pw10,pw50,pw3,pw52,pw4],[349,5,1,9,389,44,56],[7,9,9,9,9,18,18,18,18,32,32,64,32,96,96]),
([pw0,pw10,pw3,pw52,pw4],[389,349,5,9,193,56,3,205,297,44,11],[15,122,202,1802,117,197,1797,560,816,32]),
([pw76,pw0,pw21,pw10,pw3,pw4],[349,9,20,205,3,5,345,193,333,297,17,437],[3,28,32,192,768,1033,3,3,3,2048,200,776,192,768,192]),
([pw117,pw0,pw1,pw2,pw3,pw4],[105,349,209,5,205,49,193,345,297,333],[3,12,48,192,768,3,3,3,3,12,12,772,48,784,192]),
([pw61,pw0,pw1,pw2,pw3,pw4],[105,5,389,49,433,345,193,333,297,3],[1,6,24,96,384,6,24,96,384,522,6,6,24,24,96]),
([pw118,pw0,pw1,pw2,pw3,pw4],[9,5,209,49,205,345,193,333,297],[1,6,24,96,384,6,24,96,384,6,6,386,24,392,96]),
([pw75,pw104,pw0,pw2,pw3,pw4],[5,209,37,221,9,49,205,345,193,333,297],[3,3,3,3,13,16,96,384,1536,96,384,1536,96,1568,384]),
([pw1,pw2,pw10,pw58,pw3,pw4],[3,209,205,5,9,57,313,49,309,349,345,193,333,297],[7,8,50,66,66,128,52,260,260,528,3072,12288,528,528,3072]),
([pw0,pw1,pw2,pw60,pw119,pw50],[57,5,1,9,29,133,41,225,325,321,205,49,193,129,297,221,32,253,24,44],[7,9,49,193,769,3074,12290,49154,65794,3072,148480,263424,544768,69888,82176]),
([pw0,pw1,pw2,pw37,pw3,pw4],[209,7,349,3,205,12,9,193,341,297,329,20,5,313,24,309,4,385,0,333],[7,28,100,388,1540,19,6145,8321,8705,18448,32912,33296,196736,262688,524928]),
([pw0,pw10,pw3,pw120,pw96,pw4],[349,9,57,317,389,193,12,313,189,309,185,256,44,209,205],[3,3,5,3,3,56,80,80,80,416,1568,2080,4736,8320,16896]),
([pw75,pw0,pw10,pw3,pw96,pw4],[57,9,5,313,193,189,20,205,209,349,16,389,12,309,373,297],[3,4,56,200,264,513,529,3,513,3088,3200,6144,8336,49168,8320]),
([pw75,pw121,pw0,pw10,pw3,pw4],[20,205,209,9,57,5,313,49,309,349,345,193,333,297],[7,28,32,68,68,26,128,258,258,520,520,520,3072,12288,3072]),
([pw0,pw122,pw2,pw10,pw3,pw4],[57,9,17,53,389,5,29,133,41,225,20,205,209,313,49,309,193,333,297],[1,14,50,194,770,7168,48,12288,12288,16384,34816,34816,48,48,458752]),
([pw0,pw1,pw123,pw10,pw3,pw4],[57,9,349,209,205,20,313,185,309,49,69,157,81,253,193,333,297],[3,3,5,5,5,56,32,72,72,32,400,272,3584,12800,114688]),
([pw62,pw1,pw2,pw50,pw3,pw4],[1,9,57,349,205,45,389,433,341,329,3,297,193],[7,6,10,10,10,49,65,65,65,144,48,144,256,512,7168]),
([pw0,pw124,pw1,pw2,pw3,pw4],[349,57,5,9,29,133,41,225,389,433,49,385,4,193,369,0,297,205,333],[1,14,10,50,194,260,1536,14336,114688,131588,260,260,1536,1536,335872]),
([pw125,pw1,pw2,pw3,pw45,pw4],[209,5,205,433,49,193,345,12,9,57,333,297,97],[3,28,96,896,3200,3,3,3,3073,24,4360,24,96,96,3328]),
([pw0,pw1,pw2,pw3,pw126,pw4],[209,5,9,49,97,29,133,57,41,225,37,221,69,157,205,24,81,253,193,345,297,333],[3,28,100,128,772,3,3,3,3073,12296,49160,196616,786432,786432,3145728]),
([pw127,pw0,pw1,pw2,pw3,pw4],[9,5,389,49,205,433,193,385,297,369,73,57,85,209],[1,6,56,192,768,6,40,3136,6400,8202,6,6,40,40,192]),
([pw0,pw1,pw128,pw2,pw3,pw4],[57,5,209,349,37,221,49,205,20,193,345,297,333],[7,9,9,9,9,6,6,6,50,448,1536,6144,1664,6272,1536]),
([pw129,pw1,pw2,pw47,pw3,pw4],[5,209,49,181,309,9,0,345,73,297,333,57,1,69,161],[3,28,104,392,1544,3,6145,3,1537,20,8324,20,18560,1536,1664]),
([pw130,pw1,pw2,pw67,pw3,pw4],[277,5,209,20,193,429,85,333,205,49,61,9,37,81,225],[7,9,9,49,193,770,3074,50,4226,768,784,8576,48,18560,48]),
([pw79,pw131,pw0,pw2,pw3,pw4],[5,209,9,1,49,197,345,189,297,293,277,205,193,313,333],[1,14,50,194,770,1028,2064,4160,25088,1044,4164,1540,2128,16912,4672]),
([pw132,pw0,pw1,pw133,pw2,pw4],[193,345,209,5,9,205,49,41,241,333,37,417],[3,3,3,3,3,12,16,96,896,12,12,1540,96,2560,2592]),
([pw0,pw64,pw2,pw134,pw3,pw4],[61,5,9,305,49,57,73,165,333,261,209,15,37,389,301,69,157,81,313,3,297],[7,25,32,193,769,1042,2048,1026,4354,24592,98320,131344,270336,532736,1048832]),
([pw0,pw1,pw66,pw2,pw135,pw3],[313,5,9,149,49,205,333,297,29,345,25,7,24,429],[3,4,56,200,776,3,3,3,1537,6160,192,8704,208,48,192]),
([pw136,pw131,pw0,pw2,pw3,pw4],[7,9,49,205,345,193,209,297,293,1,5,57,221,33,253],[1,2,12,48,448,3584,12,48,5376,12,48,8960,12,16644,48]),
([pw137,pw0,pw1,pw2,pw67,pw50],[36,5,193,189,49,185,369,325,85,121,205,209,429],[1,14,52,1,193,770,1296,1,193,1042,2050,193,1040,4161,193]),
([pw1,pw66,pw2,pw67,pw3,pw4],[277,5,209,205,49,28,149,25,129,37,221,20,345,193,85,333,81,29,297,3],[7,26,98,386,1538,2057,97,12289,49153,24,24,98312,135232,294976,561152]),
([pw0,pw1,pw2,pw68,pw3,pw4],[181,5,209,241,9,0,313,37,221,4,49,205,69,157,81,253,16,12,3,333,325],[7,9,16,9,9,6,98,6,386,3584,13312,50176,66048,131104,1835008]),
([pw138,pw0,pw1,pw2,pw3,pw4],[277,149,313,5,273,309,49,429,345,297,333,25],[3,12,112,384,1536,3,3,3,3,12,2180,12,416,96,1664]),
([pw0,pw83,pw1,pw2,pw67,pw50],[85,3,193,5,121,205,49,9,325,369,129,7,297,48,429],[7,25,97,128,769,1024,100,6148,772,104,12296,776,96,16672,768]),
([pw139,pw1,pw133,pw2,pw3,pw4],[209,5,12,149,9,205,309,49,193,345,41,241,37,221,169,333,297],[3,28,224,768,3076,3,3,3,12289,16456,776,98312,832,192,768]),
([pw140,pw1,pw2,pw42,pw3,pw4],[5,49,260,20,9,193,16,297,12,205,61,57,209,313,253,73,85,333],[1,14,16,100,388,514,7168,12320,12416,514,546,16514,34848,67712,131232]),
([pw1,pw94,pw2,pw141,pw3,pw4],[57,5,101,209,28,7,37,221,17,49,9,73,161,85,257,205,69,157,81,253,16,193,36,297,40,333],[7,10,50,10,194,769,1024,6145,24577,32768,197120,786944,7340032,29360128,44040192]),
([pw142,pw1,pw94,pw2,pw3,pw4],[209,5,9,49,193,345,297,333,205,57,45],[3,4,8,48,192,3,3,3,193,1792,48,192,48,192,48]),
([pw143,pw1,pw2,pw42,pw3,pw4],[209,49,205,9,345,193,333,297,57,5,1],[1,6,8,48,192,6,1792,48,192,6,6,194,48,192,48]),
([pw69,pw0,pw1,pw2,pw3,pw4],[181,5,209,49,309,345,385,333,417,37,69,3],[1,6,24,96,384,6,24,96,384,6,6,642,1064,24,2208]),
([pw0,pw1,pw2,pw144,pw50],[209,57,5,9,213,49,193,3,181,385,325,349,0,36,417],[15,58,450,3586,53,4165,9729,8304,25104,9792]),
([pw145,pw1,pw2,pw3,pw45,pw4],[5,389,49,205,345,193,9,57,0,333,297,1],[3,12,48,448,1536,13,3,2177,3,12,12,1540,48,48,1664]),
([pw122,pw1,pw2,pw3,pw45,pw4],[349,5,209,49,433,16,12,205,25,129,61,9,37,221,29,133,193,333,297],[7,25,33,33,65,138,770,3074,12290,24,136,24,51200,458752,395264]),
([pw75,pw146,pw0,pw2,pw3,pw4],[5,209,9,1,49,197,313,349,205,193,345,297,333],[1,14,50,66,66,132,272,1536,6144,276,132,132,272,6160,1536]),
([pw0,pw1,pw48,pw3,pw45,pw4],[209,3,349,49,205,193,345,17,297,333,7,28],[7,28,100,128,772,25,97,3073,769,24,24,776,96,96,768]),
([pw147,pw0,pw2,pw3,pw45,pw4],[209,5,37,221,205,49,193,345,9,297,333],[3,3,3,3,13,48,192,256,1536,48,48,1552,192,192,1536]),
([pw0,pw73,pw2,pw3,pw148,pw4],[61,5,9,201,49,345,165,57,333,261,7,25,37,69,3,197,81,313,189,193,209],[7,25,97,128,769,1042,2082,1024,4354,8240,49168,65808,393248,524576,1179904]),
([pw0,pw149,pw2,pw3,pw45,pw4],[209,5,349,49,433,193,345,57,297,333,7,24],[3,28,100,128,772,3,3,3,769,24,3080,24,96,96,768]),
([pw49,pw0,pw1,pw3,pw45,pw4],[205,49,253,81,197,5,193,345,9,297,333],[3,3,3,3,13,48,192,256,1536,48,48,1552,192,192,1536]),
([pw150,pw146,pw0,pw2,pw3,pw4],[7,9,49,205,313,193,189,209,1,5,57,129,221,37,21,33,217,81,253,333,297],[1,2,12,112,144,1792,12,2592,12800,12,16672,98560,12,393220,1572896]),
([pw75,pw151,pw0,pw2,pw3,pw4],[209,57,5,1,205,93,25,129,37,221,9,433,193,389,345,297,333,29,41,309,361],[1,14,52,196,772,1026,2064,28672,106496,1042,135170,294914,528400,2064,1085440]),
([pw75,pw0,pw152,pw2,pw3,pw4],[57,9,5,433,205,313,193,189,209,349,345,333,297],[3,4,24,224,288,513,3,577,513,24,1088,6144,1096,24,1088])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p7_D4 : List StD := [
([pw1,pw36,pw37,pw3,pw4],[349,201,197,17,5,305,9,309,205,69,137,81,229,193,333,297],[7,26,34,34,73,129,257,1544,6152,57344]),
([pw0,pw1,pw38,pw3,pw4],[45,5,9,29,133,41,225,49,197,37,221,157,69,253,81,193,333,297],[7,5,25,97,386,258,1538,6272,24704,229376]),
([pw39,pw0,pw1,pw2,pw40],[329,9,333,5,361,49,413,325,193,205],[3,28,100,388,3,97,3,552,24,96]),
([pw41,pw1,pw42,pw3,pw4],[49,5,197,45,9,157,69,253,81,37,221,29,133,41,225,193,333,297],[7,25,97,385,6,6,1538,6152,24584,229376]),
([pw1,pw43,pw44,pw2,pw45],[5,25,129,37,221,205,49,57,1,193,333,297,29],[7,25,97,385,3584,96,4736,3104,3200,96]),
([pw46,pw1,pw2,pw47,pw4],[73,5,113,345,341,9,309,49,37,221],[7,9,49,9,194,50,770,208,192,48]),
([pw17,pw48,pw3,pw45,pw4],[349,5,197,313,209,25,129,201,9,37,221,17,345,137,193,333,229],[7,9,9,17,98,386,1538,14336,20480,100352]),
([pw49,pw0,pw1,pw50,pw40],[45,9,49,5,197,333,413,157,69,29,133,369,325],[3,28,100,388,3,97,1537,2088,24,4096]),
([pw0,pw51,pw10,pw3,pw4],[9,17,97,389,1,29,133,41,225,5,309,193,185,205,333,297],[7,25,97,385,520,7168,9216,520,520,51200]),
([pw32,pw0,pw10,pw52,pw4],[29,5,193,389,309,185,44,17,9,41,225,205],[1,14,52,68,10,400,1792,10,10,2064]),
([pw53,pw10,pw3,pw45,pw4],[349,5,197,309,205,25,129,201,17,37,221,345,137,193,333,229],[7,9,9,17,98,386,1538,6400,10240,49408]),
([pw0,pw10,pw3,pw54,pw4],[201,17,5,345,137,9,333,229,25,3,197,37,309,185,193,205],[7,26,32,194,268,1540,2116,12296,16456,36928]),
([pw55,pw0,pw10,pw3,pw4],[205,17,9,389,5,309,349,193,369,297],[7,25,33,33,26,66,66,24,24,896]),
([pw0,pw10,pw3,pw56,pw4],[197,9,89,29,133,97,17,41,225,93,205,5,117,285,185,309,193,369,297],[7,26,98,386,513,3073,12289,50176,458752,33792]),
([pw57,pw0,pw10,pw3,pw4],[97,17,5,185,193,309,205,197,9,89,29,41,225,93,117,285,333,297],[3,4,56,96,896,1296,6400,8336,49280,196624]),
([pw21,pw10,pw58,pw3,pw4],[93,9,17,97,309,193,185,205,349,5,129,37,221,333,297],[1,14,112,144,258,1568,6656,290,258,24608]),
([pw0,pw59,pw10,pw3,pw4],[9,17,97,349,93,309,193,185,205,5,129,37,221,333,297],[7,9,9,9,16,224,288,1600,6656,24640]),
([pw0,pw60,pw10,pw52,pw4],[9,29,133,317,1,17,97,41,225,129,309,193,185,44,5,205],[7,25,97,385,512,7168,10240,17416,16392,33792]),
([pw0,pw21,pw37,pw3,pw4],[197,201,349,5,1,193,341,297,329,3,301,25,37,333],[7,28,100,388,521,1057,1153,2088,4232,8352]),
([pw61,pw0,pw10,pw3,pw4],[17,5,205,197,309,389,9,29,133,41,225,193,333,297],[1,14,20,20,34,448,1600,34,34,14336]),
([pw62,pw1,pw2,pw50,pw40],[1,9,57,349,205,45,369,329,21,125,417,321],[7,6,10,10,49,193,769,1104,48,2048]),
([pw63,pw0,pw1,pw3,pw4],[45,17,49,5,197,157,69,253,81,65,137,41,229,25,129,37,221,193,213,289],[3,28,100,388,3,1537,6145,24584,98312,917504]),
([pw0,pw64,pw2,pw65,pw3],[57,5,1,305,45,333,257,73,161,209,37,81,49,69,157,293],[7,25,97,385,514,1058,514,6176,28672,32800]),
([pw1,pw66,pw2,pw67,pw50],[85,5,121,205,49,48,29,369,325,44,357,429],[7,26,98,386,521,97,1153,24,2184,448]),
([pw0,pw1,pw2,pw68,pw50],[73,5,41,9,325,385,209,0,189,4,49,185,417,193,357],[7,5,8,49,66,386,50,3584,5136,24592]),
([pw69,pw0,pw1,pw2,pw50],[41,5,193,189,49,185,385,325,57,1,9,209,417],[1,14,52,196,770,1296,192,2066,194,4176]),
([pw0,pw70,pw3,pw71,pw4],[201,13,17,345,137,9,333,229,25,5,3,197,37,309,185,193,205],[3,28,32,196,776,3584,4672,24584,32840,73792]),
([pw72,pw0,pw1,pw3,pw4],[45,17,49,5,197,157,69,253,81,65,137,77,229,25,129,37,221,193,333,297],[3,28,100,388,3,1537,6145,24584,98312,917504]),
([pw0,pw73,pw74,pw3,pw4],[61,5,1,197,45,345,165,333,261,3,25,37,49,81,193],[7,25,97,385,522,1058,2178,4136,8328,16544])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p7_D3 : List StD := [
([pw0,pw35,pw3,pw4],[197,5,17,345,137,333,229,37,193],[3,28,100,3,161,296])]
def p7_D2 : List StD := []
theorem p7_I2 : LevelN true p7_T 2 p7_D2 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p7_C3x0 : levelOK true p7_T p7_t 2 (p7_D2.map Prod.fst) ((p7_D3.drop (0*32)).take 32) = true := by decide +kernel
theorem p7_I3 : LevelN true p7_T 3 p7_D3 := levelStep p7_B p7_W p7_I2 (chunks 32 p7_D3 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p7_C3x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p7_C4x0 : levelOK true p7_T p7_t 3 (p7_D3.map Prod.fst) ((p7_D4.drop (0*32)).take 32) = true := by decide +kernel
theorem p7_I4 : LevelN true p7_T 4 p7_D4 := levelStep p7_B p7_W p7_I3 (chunks 32 p7_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p7_C4x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p7_C5x0 : levelOK true p7_T p7_t 4 (p7_D4.map Prod.fst) ((p7_D5.drop (0*32)).take 32) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p7_C5x1 : levelOK true p7_T p7_t 4 (p7_D4.map Prod.fst) ((p7_D5.drop (1*32)).take 32) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p7_C5x2 : levelOK true p7_T p7_t 4 (p7_D4.map Prod.fst) ((p7_D5.drop (2*32)).take 32) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p7_C5x3 : levelOK true p7_T p7_t 4 (p7_D4.map Prod.fst) ((p7_D5.drop (3*32)).take 32) = true := by decide +kernel
theorem p7_I5 : LevelN true p7_T 5 p7_D5 := levelStep p7_B p7_W p7_I4 (chunks 32 p7_D5 4 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p7_C5x0
  · exact p7_C5x1
  · exact p7_C5x2
  · exact p7_C5x3
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p7_C6x0 : levelOK true p7_T p7_t 5 (p7_D5.map Prod.fst) ((p7_D6.drop (0*32)).take 32) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p7_C6x1 : levelOK true p7_T p7_t 5 (p7_D5.map Prod.fst) ((p7_D6.drop (1*32)).take 32) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p7_C6x2 : levelOK true p7_T p7_t 5 (p7_D5.map Prod.fst) ((p7_D6.drop (2*32)).take 32) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p7_C6x3 : levelOK true p7_T p7_t 5 (p7_D5.map Prod.fst) ((p7_D6.drop (3*32)).take 32) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p7_C6x4 : levelOK true p7_T p7_t 5 (p7_D5.map Prod.fst) ((p7_D6.drop (4*32)).take 32) = true := by decide +kernel
theorem p7_I6 : LevelN true p7_T 6 p7_D6 := levelStep p7_B p7_W p7_I5 (chunks 32 p7_D6 5 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p7_C6x0
  · exact p7_C6x1
  · exact p7_C6x2
  · exact p7_C6x3
  · exact p7_C6x4
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p7_C7x0 : levelOK true p7_T p7_t 6 (p7_D6.map Prod.fst) ((p7_D7.drop (0*32)).take 32) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p7_C7x1 : levelOK true p7_T p7_t 6 (p7_D6.map Prod.fst) ((p7_D7.drop (1*32)).take 32) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p7_C7x2 : levelOK true p7_T p7_t 6 (p7_D6.map Prod.fst) ((p7_D7.drop (2*32)).take 32) = true := by decide +kernel
theorem p7_I7 : LevelN true p7_T 7 p7_D7 := levelStep p7_B p7_W p7_I6 (chunks 32 p7_D7 3 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p7_C7x0
  · exact p7_C7x1
  · exact p7_C7x2
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p7_C8x0 : levelOK true p7_T p7_t 7 (p7_D7.map Prod.fst) ((p7_D8.drop (0*32)).take 32) = true := by decide +kernel
theorem p7_I8 : LevelN true p7_T 8 p7_D8 := levelStep p7_B p7_W p7_I7 (chunks 32 p7_D8 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p7_C8x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p7_C9x0 : levelOK true p7_T p7_t 8 (p7_D8.map Prod.fst) ((p7_D9.drop (0*32)).take 32) = true := by decide +kernel
theorem p7_I9 : LevelN true p7_T 9 p7_D9 := levelStep p7_B p7_W p7_I8 (chunks 32 p7_D9 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p7_C9x0
  ))
theorem p7_L : LowN true p7_R p7_T 10 := lowSearch p7_B p7_I9 (by decide +kernel)
def p8_T : Nat := 0xeac8eac8eac8eac8eac8eac8eac8eac8
def p8_R : List Nat := [0, 1, 2, 3]
def p8_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,2,6),(3,1,9)]
theorem p8_B : baseOK p8_T p8_R p8_E = true := by decide +kernel
def p8_Z : List SliceD := []
theorem p8_Y : ∀ s ∈ p8_Z, SliceN true p8_R p8_T s := by
  unfold p8_Z
  intro s h; cases h
def p8_C : List (Nat × List Nat) := []
def p8_t : Tabs := (p8_C.map (mkCut true p8_Z),[(3,1),(3,2),(3,10),(6,2),(6,4),(6,10),(6,12),(9,0),(9,1),(9,12)],[],[])
theorem p8_W : TabsP true p8_R p8_T p8_t := ⟨cutsGood p8_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p8_D3 : List StD := [
([pw0,pw1,pw2,pw3],[17,1,5,37,13,9,29,25,33,21],[3,28,100,3,385,784])]
def p8_D2 : List StD := []
theorem p8_I2 : LevelN true p8_T 2 p8_D2 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p8_C3x0 : levelOK true p8_T p8_t 2 (p8_D2.map Prod.fst) ((p8_D3.drop (0*32)).take 32) = true := by decide +kernel
theorem p8_I3 : LevelN true p8_T 3 p8_D3 := levelStep p8_B p8_W p8_I2 (chunks 32 p8_D3 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p8_C3x0
  ))
theorem p8_L : LowN true p8_R p8_T 4 := lowSearch p8_B p8_I3 (by decide +kernel)
def p9_T : Nat := 0xfee8eac8fee8eac8fee8eac8fee8eac8
def p9_R : List Nat := [0, 1, 2, 3, 4]
def p9_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,2,6),(3,1,9),(4,5,21)]
theorem p9_B : baseOK p9_T p9_R p9_E = true := by decide +kernel
def p9_Z : List SliceD := [(pw4,7,[0, 1, 2, 3]),(pw6,5,[1, 0, 2, 4]),(pw3,5,[0, 1, 2, 4]),(pw7,5,[0, 1, 3, 4]),(pw2,5,[1, 0, 3, 4]),(pw8,5,[0, 3, 2, 4]),(pw9,5,[1, 2, 3, 4]),(pw24,4,[0, 1, 2, 3]),(pw26,4,[0, 1, 2]),(pw27,4,[0, 1, 3]),(pw28,4,[0, 2, 3]),(pw29,4,[1, 2, 3]),(pw32,4,[1, 2, 4]),(pw195,4,[0, 3, 4])]
theorem p9_Y : ∀ s ∈ p9_Z, SliceN true p9_R p9_T s := by
  unfold p9_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=16) p9_B p2_B p2_L (by decide +kernel),mkSlice (w:=0) p9_B p4_B p4_L (by decide +kernel),mkSlice (w:=8) p9_B p6_B p6_L (by decide +kernel),mkSlice (w:=0) p9_B p4_B p4_L (by decide +kernel),mkSlice (w:=4) p9_B p6_B p6_L (by decide +kernel),mkSlice (w:=0) p9_B p5_B p5_L (by decide +kernel),mkSlice (w:=0) p9_B p5_B p5_L (by decide +kernel),mkSlice (w:=0) p9_B p8_B p8_L (by decide +kernel),mkSlice (w:=16) p9_B p1_B p1_L (by decide +kernel),mkSlice (w:=16) p9_B p1_B p1_L (by decide +kernel),mkSlice (w:=16) p9_B p1_B p1_L (by decide +kernel),mkSlice (w:=16) p9_B p1_B p1_L (by decide +kernel),mkSlice (w:=8) p9_B p1_B p1_L (by decide +kernel),mkSlice (w:=4) p9_B p1_B p1_L (by decide +kernel),by simp⟩
def p9_C : List (Nat × List Nat) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(6,[]),(7,[]),(8,[]),(9,[]),(10,[]),(11,[]),(12,[]),(13,[]),(0,[129]),(0,[257]),(0,[385]),(0,[261]),(0,[389]),(0,[393])]
def p9_t : Tabs := (p9_C.map (mkCut true p9_Z),[(3,0),(3,1),(3,2),(3,4),(3,5),(3,8),(3,10),(3,16),(3,17),(3,18),(6,0),(6,1),(6,2),(6,4),(6,5),(6,8),(6,10),(6,12),(6,18),(6,20),(7,1),(7,2),(7,4),(7,5),(7,17),(9,0),(9,1),(9,2),(9,4),(9,5),(9,8),(9,10),(9,12),(9,16),(9,17),(9,24),(11,1),(11,2),(11,8),(11,10),(11,18),(13,1),(13,5),(13,8),(13,12),(14,2),(14,4),(14,5),(14,10),(14,12),(19,0),(19,1),(19,2),(19,17),(19,18),(21,1),(21,4),(21,5),(21,16),(21,17),(21,20),(22,0),(22,2),(22,4),(22,18),(22,20),(25,1),(25,8),(25,17),(25,24),(26,2),(26,10),(26,16),(26,18),(26,24),(28,12),(28,20),(28,24)],[],[[]])
theorem p9_W : TabsP true p9_R p9_T p9_t := ⟨cutsGood p9_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p9_D8 : List StD := [
([pw0,pw1,pw2,pw3,pw4],[3,53,121,5,9,49,237,177,293,105,0,285,229,197,169,193],[31,229,789,7172,107,8963,7170,49441,7264,7936])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p9_D7 : List StD := [
([pw19,pw0,pw1,pw2,pw3,pw4],[20,24,9,5,16,3,12,8,4,0,40,57,177,121,241,53,297,48,105,169,285,229],[7,9,113,417,1569,2051,12290,20482,5122,98305,98305,99329,917504,3146752,394240]),
([pw0,pw1,pw17,pw2,pw3,pw4],[20,24,57,9,5,52,237,49,3,48,105,157,40,229,209,44,93,293,285,309,12,305,4,56,301],[31,1,490,3594,61450,2,65777,132881,307217,1573216,6293248,25178112,526176,8655072,8533504]),
([pw262,pw0,pw1,pw2,pw3,pw4],[20,24,56,16,237,12,8,105,4,44,229,9,1,52,157,297,49,53,48,293,285],[1,6,58,450,1542,6147,10258,18562,1538,237585,950401,1181185,270480,1115664,263808]),
([pw34,pw0,pw1,pw2,pw3,pw4],[20,56,53,16,49,12,8,293,4,40,285,5,24,1,121,52,237,241,48,105,229],[3,5,57,449,1539,14337,118800,938112,1066496,34833,264321,1537,295056,34320,1574528]),
([pw20,pw0,pw1,pw2,pw3,pw4],[12,16,3,93,20,237,8,169,4,0,36,229,24,9,121,129,49,309,48,293,285],[3,29,33,449,3585,28680,36865,28800,7168,196617,786568,1051656,196737,3073,265344]),
([pw0,pw1,pw2,pw36,pw3,pw4],[24,177,52,5,53,129,237,12,241,48,105,36,229,44,297,60,285,4,293],[31,103,132,1795,14595,28,16396,16908,18444,1,1604,98372,393732,100356,40448]),
([pw263,pw0,pw1,pw2,pw3,pw4],[12,16,52,5,237,8,105,4,0,44,3,85,177,241,197,49,193,229,285],[1,14,18,226,1794,524,2563,12864,12800,15,16396,524,98371,33283,393792]),
([pw33,pw0,pw1,pw2,pw3,pw4],[12,16,3,53,20,49,8,305,4,0,36,301,24,121,5,9,52,237,85,48,105,229,293,285],[3,29,33,449,3585,126988,397313,1618048,2108416,131085,4784268,8391688,655489,3073,3148928]),
([pw224,pw0,pw1,pw2,pw3,pw4],[4,8,3,20,16,12,105,0,32,24,9,241,25,237,5,49,53,293,305,229,285],[3,13,53,65,389,3584,3584,4609,1792,122884,393217,1589504,393217,1605888,1179905]),
([pw0,pw1,pw2,pw3,pw14,pw4],[24,121,48,157,177,25,105,9,277,3,237,5,49,53,20,64,229,285,169,12,16],[15,23,103,132,263,15872,2628,25092,231424,263236,1576964,234496,1,32836,33284]),
([pw235,pw0,pw1,pw2,pw3,pw4],[4,8,3,5,20,16,237,12,105,0,44,229,157,121,177,101,269,49,53,305,293,285],[1,30,226,258,3586,13320,21568,33795,72704,393292,1572875,2100232,1572931,2231360,3075]),
([pw32,pw0,pw1,pw2,pw3,pw4],[4,8,48,293,9,241,105,101,3,237,5,49,53,32,229,285],[3,5,5,9,5,52,52,197,52,7936,5,58368,5,59904,5]),
([pw0,pw21,pw1,pw2,pw3,pw4],[12,3,24,20,5,297,237,309,293,9,105,121,36,285,229,53,49,8,4,0,17],[7,56,193,3842,29184,32777,65537,393219,528387,1048585,56,56,193,20545,29952]),
([pw0,pw1,pw2,pw10,pw3,pw4],[20,53,52,93,49,3,9,24,121,293,105,68,285,229,17,5,197,193,4,8],[15,116,420,1888,14400,16407,32772,66055,2055,1,131604,2068,787460,2084,15872]),
([pw78,pw0,pw1,pw2,pw3,pw4],[16,3,9,24,12,49,8,293,4,0,40,285,93,53,309,237,105,121,229,41,197],[15,17,33,449,3585,13316,49157,196742,265220,525313,1053824,269312,49281,3073,330880]),
([pw195,pw0,pw1,pw2,pw3,pw4],[12,52,53,237,5,297,3,293,9,105,121,36,285,229,49,41],[3,7,9,3,3,50,3,1984,14592,49155,50,50,3,3,14976]),
([pw0,pw83,pw1,pw2,pw3,pw4],[4,3,157,24,20,5,53,48,52,237,105,305,32,229,193,293,285,69],[15,116,900,3077,12420,145,16641,32769,69633,112,131089,4144,1281,21248,3073]),
([pw0,pw1,pw2,pw3,pw11,pw4],[20,197,48,9,121,177,241,297,52,49,69,293,4,32,285,40,12,237,72,229],[31,44,28,76,76,899,3079,4100,57475,2820,196868,418560,1,788484,794628]),
([pw264,pw0,pw1,pw2,pw3,pw4],[8,48,9,4,16,49,12,293,0,40,3,177,197,297,145,105,169,285,229],[7,9,113,129,1793,518,2054,7,518,12832,16897,12800,98337,393760,33281]),
([pw31,pw0,pw1,pw2,pw3,pw4],[4,3,121,24,8,16,309,12,105,0,32,301,20,53,5,9,48,52,237,293,229,49,145,285],[15,17,225,257,3585,126982,458822,524295,1051652,2256960,4722689,8399872,655425,10488896,3073]),
([pw0,pw1,pw86,pw2,pw3,pw4],[48,121,3,5,9,52,4,177,237,12,105,293,32,229,197,49,285,301,65],[63,199,931,3155,12291,16492,49960,3177,69672,1,32,135232,262753,13088,3137]),
([pw0,pw1,pw2,pw3,pw12,pw4],[48,9,121,177,217,12,309,16,193,169,52,5,213,65,49,305,76,3],[7,11,7,7,19,480,3585,3073,7168,8353,16513,480,33,33281,196609]),
([pw265,pw0,pw1,pw2,pw3,pw4],[8,48,241,3,53,20,4,169,0,36,229,9,193,309,105,293,285,165],[7,57,65,129,1793,2054,518,7,1542,12816,49169,67088,131585,13824,1537]),
([pw30,pw0,pw1,pw2,pw3,pw4],[4,3,121,24,52,297,193,105,0,32,285,5,49,237,169,305,229,165],[15,49,81,129,1793,2100,12308,49157,67076,12336,49,1584,131089,1552,1537])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p9_D6 : List StD := [
([pw0,pw1,pw244,pw3,pw4],[20,17,53,16,49,237,24,121,241,197,261,193,40,229,285],[7,56,448,448,27,515,1027,2072,56,28672]),
([pw245,pw0,pw1,pw3,pw4],[12,237,49,193,20,5,53,24,121,9,217,197,213,36,229,285],[7,7,11,7,112,896,1408,2096,4144,57344]),
([pw0,pw1,pw2,pw246,pw4],[20,24,25,177,241,53,297,8,105,169,40,285,229],[7,14,22,22,97,97,97,896,7168,1408]),
([pw247,pw0,pw1,pw2,pw4],[4,105,293,169,20,5,53,24,177,9,217,213,32,285,229],[7,7,11,7,112,896,1408,112,2096,28672]),
([pw248,pw0,pw1,pw2,pw3],[24,241,9,20,261,5,28,285,40,229,121,197,48,105,169],[7,56,960,960,7,7,1027,56,2072,28672]),
([pw33,pw0,pw1,pw17,pw2,pw3,pw4],[52,3,5,49,105,305,229,301,9,53,17,81,293,33,12,285],[1,7,1,8,48,192,257,1,257,48,192,512,3076,4101,8197,16385,48,192,17,32769,48]),
([pw31,pw0,pw1,pw17,pw2,pw3,pw4],[9,3,24,48,49,309,105,229,301,5,121,237,25,149,33,4],[7,8,12,48,64,384,521,1024,2057,12289,137,8,48,520,17024,48,32776,384,24,48,136]),
([pw0,pw1,pw155,pw17,pw2,pw3,pw4],[57,9,5,20,24,121,52,25,149,37,209,297,93,293,33,49,169,285,229,12,305,301],[7,26,32,66,386,1538,28,2048,4100,8260,16452,64,32768,73728,393216,524352,1056768,2228224,8256,131136,73728]),
([pw249,pw0,pw1,pw17,pw2,pw3,pw4],[52,3,309,105,305,229,301,9,297,5,17,81,293,33,12,49,221],[1,2,1,4,24,96,129,1,129,24,96,256,3584,4609,8705,16385,24,96,9,98305,24]),
([pw0,pw1,pw43,pw17,pw2,pw3,pw4],[57,9,5,157,241,237,49,37,209,24,20,53,48,33,205,193,105,229,285,309,4,301],[7,10,16,98,10,386,1540,2048,100,4100,24580,4096,32800,65536,393216,524320,1052672,2228224,4128,96,135168]),
([pw250,pw0,pw1,pw17,pw2,pw3,pw4],[3,48,49,309,305,229,301,5,241,237,9,25,149,33,4],[1,2,2,12,16,96,130,256,514,7168,34,2,12,130,8352,12,16386,96,6,12,34]),
([pw0,pw1,pw17,pw86,pw2,pw3,pw4],[57,9,5,121,3,24,237,49,25,149,37,209,53,20,293,105,33,205,4,12,16,8,301,229,193,169,65],[7,8,50,194,770,3074,4096,8212,196,49156,196612,262160,1572928,2375680,12582912,16777216,33554432,12582912,67125312,192,49152]),
([pw0,pw1,pw251,pw2,pw3,pw4],[24,9,121,12,129,217,49,309,105,93,293,48,229,285,36,301],[7,7,27,7,35,1,200,3840,29184,200,3328,53248,200,200,3328]),
([pw0,pw1,pw2,pw252,pw3],[24,9,121,177,241,16,309,49,28,229,44,285,48,105,293],[7,11,19,7,224,3840,28672,224,224,3840]),
([pw0,pw1,pw99,pw2,pw3,pw4],[53,121,3,9,52,49,237,293,105,285,229,217,12,197,261,4,8,28,0],[31,26,114,394,3586,4112,113,8337,16913,112,98688,394752,4272,112,1920]),
([pw33,pw0,pw1,pw10,pw3,pw4],[12,16,49,20,309,193,257,53,121,17,9,24,237,293,105,285,229,217,197,261,48,36,3],[3,13,19,37,69,1920,6402,25856,229632,1,286848,622720,1069058,6295554,122880]),
([pw31,pw33,pw0,pw1,pw2,pw3,pw4],[4,3,12,9,121,197,16,105,229,301,177,5,53,49,8,237,85,293,145,33,48,285],[7,24,32,68,128,768,1024,6144,8192,16385,768,24,98312,24,776,6144,395264,526592,1212416,2130176,768]),
([pw0,pw1,pw199,pw2,pw3,pw4],[24,9,241,157,237,3,49,305,4,293,229,32,285,12,16],[7,7,7,11,7,1,112,896,7168,24656,896,7168,912,7248,6528]),
([pw0,pw199,pw2,pw3,pw4],[24,9,241,125,3,237,5,49,53,4,293,305,32,229,285],[7,7,11,7,496,3648,28736,3616,28832,22016]),
([pw253,pw0,pw2,pw3,pw4],[20,5,53,197,213,24,177,9,217,4,169,105,32,285,229],[7,7,11,19,224,224,352,3584,28672,13824]),
([pw0,pw1,pw254,pw3,pw4],[24,9,129,217,16,237,49,4,293,117,32,229,285],[7,7,7,11,112,896,7168,432,112,896]),
([pw255,pw0,pw1,pw3,pw4],[12,237,49,193,24,9,121,217,4,293,105,32,229,285],[7,7,11,7,112,112,176,1792,14336,1792]),
([pw203,pw0,pw1,pw2,pw3],[24,217,9,28,229,32,285,121,177,3,237,5,49,53,293,105,169],[7,120,120,120,131,259,163,15872,49184,81952]),
([pw224,pw0,pw21,pw1,pw2,pw3,pw4],[121,4,3,12,5,20,16,105,229,36,9,24,241,25,293,53,49,8,32,17,237,289,33,305,285],[1,14,52,72,128,772,3076,5136,5120,25600,5376,32768,65536,147458,262404,1572880,2113552,4194576,9453568,17826048,16793856]),
([pw224,pw0,pw1,pw2,pw10,pw3,pw4],[121,53,3,20,49,16,12,4,105,229,36,9,89,241,24,25,293,17,5,185,77,237,65,249,8,32,281],[1,14,112,164,256,1540,6146,10256,18436,100352,10752,131090,262144,589826,1049090,2097152,4259856,8389136,16842880,33554948,67174912]),
([pw78,pw224,pw0,pw1,pw2,pw3,pw4],[4,3,16,241,9,5,49,293,305,229,285,121,53,20,237,12,105,36,25,41],[7,24,32,64,385,1536,2048,12290,49156,65536,131586,24,24,262280,24,544768,384,1536,384,1536,1664]),
([pw195,pw224,pw0,pw1,pw2,pw3,pw4],[4,52,12,9,241,53,237,305,293,285,229,121,3,5,105,36,25,49,41],[7,24,32,64,385,1536,2048,12290,6,16384,37376,24,24,65672,24,401408,384,1536,384,1536,1664]),
([pw0,pw21,pw1,pw2,pw3,pw14,pw4],[121,3,24,5,153,129,173,25,105,9,141,269,53,49,8,4,12,229,32,17,237,297,20,117,16,285,293,36],[7,25,97,385,512,3073,4096,8192,49408,81922,393218,1572872,2097416,4194314,2228232,9437440,17891328,34734080,67108864,33685760,134348802]),
([pw0,pw1,pw2,pw10,pw3,pw14,pw4],[53,93,49,177,121,25,105,9,141,269,17,5,197,77,229,237,169,193,249,3,8,16,32,293,137,36],[3,28,24,104,128,776,1029,2048,4161,3,24577,32768,65604,131076,278532,65600,3670016,4734976,8388608,16793664,34095104]),
([pw78,pw0,pw1,pw2,pw3,pw14,pw4],[121,157,5,49,105,8,4,16,3,229,285,129,173,25,9,237,53,41,197,117,12,293,36],[3,4,8,112,416,1536,3,6145,8209,16384,1537,229376,327696,327680,1536,557072,1081472,1536,2097152,1552,4195072]),
([pw195,pw0,pw1,pw2,pw3,pw14,pw4],[121,177,53,237,105,169,12,8,52,285,229,5,153,25,9,49,41,297,3,293,36],[3,4,8,48,448,1536,6145,3,8209,16384,1537,100352,133136,264448,1536,48,320,1536,524288,1552,1311232]),
([pw31,pw0,pw1,pw2,pw14,pw4],[25,4,105,24,8,169,305,273,53,121,5,49,237,177,285,229,277,20,293,213,52,32,3],[15,18,38,82,134,1793,14337,2,114689,7424,393488,573696,1312784,55296,6553616]),
([pw205,pw0,pw1,pw2,pw3,pw4],[9,20,121,4,8,49,12,237,16,293,105,285,28,229,0,53,48,177,217,3,261,169],[15,16,480,1554,30720,98309,196769,1557,337921,557216,1552,1091584,2097712,10400,1552]),
([pw0,pw1,pw2,pw3,pw206],[44,121,48,9,177,277,3,237,5,49,53,105,28,229,285,213,169],[15,23,15,39,1984,2372,61760,67716,29376,2053]),
([pw0,pw1,pw256,pw2,pw3,pw4],[24,9,121,177,217,237,5,49,93,305,293,8,229,285,213,309,12,16,301,28,0,44],[7,7,11,7,19,1,480,3648,28736,229408,3584,1839104,3616,12448,2103808]),
([pw235,pw0,pw21,pw1,pw2,pw3,pw4],[9,8,3,12,297,5,237,309,105,285,229,121,24,293,101,53,49,4,32,17],[1,14,48,200,256,1536,6148,48,192,26624,1536,32768,65536,139266,262660,524368,48,48,192,1600,1536]),
([pw235,pw0,pw1,pw2,pw10,pw3,pw4],[9,53,93,49,16,12,8,3,105,285,229,177,121,293,101,17,5,185,237,65,4,32],[1,6,56,208,256,1536,6,6152,6144,26624,1536,32778,65536,139266,1538,262144,532488,1544,1056832,2097792,1536]),
([pw235,pw78,pw0,pw1,pw2,pw3,pw4],[8,3,16,9,53,93,309,237,105,285,229,121,157,5,49,305,293,101,41],[7,8,48,196,256,1536,6144,8192,16384,98305,1536,48,192,165888,1536,262224,98320,1552,192,1600,1536]),
([pw235,pw195,pw0,pw1,pw2,pw3,pw4],[8,52,12,9,5,297,105,285,229,121,177,53,237,293,305,101,49,41],[7,8,50,6,64,384,1536,2048,4096,24577,384,48,1536,41472,384,196624,48,48,24576,384,384]),
([pw32,pw0,pw21,pw1,pw2,pw3,pw4],[121,4,48,5,297,237,309,293,229,285,3,9,105,101,53,49,32,17],[1,6,24,96,128,768,3076,24,96,14336,768,16384,32768,6,66816,131112,24,24,96,800,768]),
([pw32,pw0,pw1,pw2,pw10,pw3,pw4],[121,53,197,49,193,4,16,48,293,229,285,9,89,241,3,105,101,17,5,237,32],[1,6,24,224,256,1536,6146,10248,18560,100352,1536,131082,262144,6,1538,524288,24,1544,160,1065472,1536]),
([pw78,pw32,pw0,pw1,pw2,pw3,pw4],[4,48,9,241,5,49,229,285,121,53,197,237,309,293,105,101,41],[3,14,16,32,3,192,256,1536,6144,8192,192,12,12,49156,12,68096,1536,192,6144,192,192]),
([pw195,pw32,pw0,pw1,pw2,pw3,pw4],[4,48,241,9,53,237,285,229,121,5,297,49,193,293,105,101,41],[3,14,16,32,3,192,256,1536,6144,8192,192,12,12,49156,12,68096,1536,192,6144,192,192]),
([pw0,pw1,pw53,pw2,pw3,pw4],[297,20,5,309,12,237,293,3,105,285,36,229,17,4,8],[7,2,56,448,3584,7,4115,7,7,56,24896,3584,56,3096,3904]),
([pw1,pw53,pw2,pw3,pw4],[20,5,297,57,12,237,309,3,293,9,105,121,36,285,229],[7,11,7,7,112,3968,29184,112,20528,29952]),
([pw257,pw1,pw2,pw3,pw4],[20,5,53,12,237,49,24,121,9,217,197,213,193,36,229,285],[7,56,448,704,7,1027,2051,4120,56,57344]),
([pw0,pw1,pw2,pw258,pw4],[20,5,69,12,237,65,8,293,105,36,285,229],[7,56,448,3584,7,7,515,56,56,448]),
([pw191,pw0,pw1,pw2,pw4],[4,105,293,169,20,5,53,12,237,49,32,285,229],[7,7,11,7,112,896,7168,112,1072,896]),
([pw200,pw0,pw1,pw2,pw3],[28,285,36,229,20,5,53,237,49,3,293,9,105,121,197,193],[15,15,15,15,112,388,15872,84,17456,32900]),
([pw104,pw0,pw1,pw2,pw3,pw4],[16,5,20,53,12,237,49,105,4,293,8,229,28,285,0,121,52,3,277,197,213,193],[1,30,113,1920,30720,98314,97,164480,305152,99,590466,1124354,2097313,97,10880]),
([pw0,pw1,pw2,pw119,pw3],[40,53,52,5,49,3,9,28,285,229,217,293,105,121,261,197,193],[15,116,2016,14432,15,16647,34823,21,67604,2976]),
([pw0,pw125,pw1,pw2,pw3,pw4],[16,53,20,5,309,237,293,9,105,157,285,229,217,305,4,8,301,28,0,197,213,40],[1,14,49,960,7296,14,49,57408,459776,13,524358,1049606,49,2098193,3392]),
([pw0,pw1,pw66,pw2,pw3,pw4],[53,20,5,49,157,237,52,305,4,105,285,229,32,69,301],[7,2,120,912,7184,7,7,8451,5123,104,896,21504,840,104,896]),
([pw0,pw1,pw2,pw3,pw259],[20,5,53,48,177,9,241,297,105,169,28,285,40,229],[7,56,56,88,7,11,131,776,15360,4360]),
([pw0,pw216,pw1,pw2,pw3,pw4],[4,53,121,5,3,48,177,277,49,12,237,16,285,28,229,0,213],[1,62,100,37,164,42,3840,33,61440,1290,33,86018,33,21760,33]),
([pw0,pw1,pw2,pw47,pw3,pw4],[53,177,5,3,48,12,293,105,32,49,237,20,229,285],[31,50,48,210,274,1573,2061,209,12545,16,304,800,208,12544,208]),
([pw0,pw1,pw2,pw167,pw3,pw4],[197,121,3,9,52,49,237,24,293,105,285,229,217,4,32],[31,114,142,778,7170,113,8208,8465,17425,112,8496,112,16,19456,3840]),
([pw0,pw1,pw2,pw3,pw260],[48,9,121,177,241,16,309,49,105,52,5,261,305],[7,11,7,19,224,1793,3584,161,224,4353]),
([pw0,pw1,pw261,pw2,pw3,pw4],[53,121,93,9,24,48,177,217,309,12,49,105,293,229,285,261,301,28,0],[15,58,98,42,162,32,1793,6177,57345,1792,6176,466944,1568,1792,6176]),
([pw0,pw139,pw1,pw2,pw3,pw4],[4,53,121,5,157,49,237,16,105,305,285,229,277,20,52,301,28,0,69,213],[1,30,228,773,7172,24586,224,769,230400,106,278785,543746,385,224,769])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p9_D5 : List StD := [
([pw0,pw99,pw17,pw2,pw3,pw4],[57,9,5,89,237,49,25,149,37,209,0,53,293,105,33,205,12,185,77,253,65],[7,8,50,194,770,3076,52,12292,49156,67600,137216,788480,1052688,48,12288]),
([pw216,pw1,pw17,pw2,pw3,pw4],[57,9,5,0,121,237,49,25,149,37,209,53,293,105,33,205,173,4,141,269,65],[7,26,98,386,1538,2048,100,12292,49156,65584,135184,786448,1052704,96,12288]),
([pw1,pw17,pw2,pw47,pw3,pw4],[53,5,17,81,57,9,293,105,33,205,129,177,49,4,229,301,237,65,209],[1,14,50,194,770,7168,10272,10304,51200,69664,135232,86016,224,278560,192]),
([pw0,pw17,pw2,pw167,pw3,pw4],[121,9,237,49,57,5,25,149,37,209,12,197,69,105,229,301,65,293],[1,14,50,194,770,3076,3104,14336,51200,12,73732,12,139296,49184,57344]),
([pw0,pw1,pw2,pw134,pw3,pw4],[57,9,5,129,49,121,25,149,37,209,81,53,69,105,33,205,8,309,65,73,221,4,28,229,0,137],[7,26,32,194,770,1044,2048,12292,49156,196624,270352,1572880,2170880,29360128,41951232]),
([pw217,pw0,pw1,pw2,pw3,pw4],[177,9,197,5,193,309,49,169,305,105,301,229,33],[3,12,112,896,3072,3,3,3,3073,12,12,5124,96,96,768]),
([pw33,pw0,pw1,pw119,pw3],[16,5,36,49,40,193,53,121,9,285,221,217,293,105,197],[1,30,28,44,450,3712,12672,6,28674,13824]),
([pw218,pw0,pw1,pw2,pw3,pw4],[9,121,5,53,237,309,293,305,229,301,33,285],[3,12,48,192,768,3,49,3,769,12,196,1284,48,2320,832]),
([pw0,pw21,pw199,pw2,pw3,pw4],[9,3,24,241,25,109,53,49,293,48,4,229,32,5,17,237,105,33,305,285],[7,9,9,49,9,64,128,1792,6146,57344,73984,141312,295168,559104,526592]),
([pw0,pw199,pw2,pw10,pw3,pw4],[53,9,89,241,125,3,25,149,17,49,4,5,69,105,77,229,237,65,181,249,293,48,32,281],[7,10,50,194,10,769,3073,12289,49153,65536,393728,557568,3146752,4227104,9469952]),
([pw78,pw0,pw199,pw2,pw3,pw4],[125,241,9,5,49,305,293,229,285,25,237,53,41],[7,8,16,96,384,6,6,546,6,7168,96,384,96,384,416]),
([pw195,pw0,pw199,pw2,pw3,pw4],[9,241,5,53,4,237,305,293,285,229,25,49,41],[3,28,32,208,768,3,3,1089,3,6148,196,772,192,768,832]),
([pw0,pw219,pw199,pw2,pw3,pw4],[9,3,24,241,25,109,53,49,293,48,4,229,32,17,237,5,105,33,305,285],[7,9,9,49,9,64,128,1792,6146,57344,98560,165888,278784,542720,526592]),
([pw0,pw199,pw2,pw220,pw3,pw4],[53,9,89,241,24,3,25,109,17,49,5,69,169,77,229,237,65,181,249,4,293,48,32,281],[7,10,50,194,10,769,1024,6145,24577,32768,197120,279040,3670016,4210720,9453568]),
([pw221,pw0,pw199,pw2,pw3,pw4],[241,9,5,49,305,293,229,285,25,237,53,41],[3,4,8,48,192,3,3,273,3,3584,48,192,48,192,208]),
([pw222,pw0,pw199,pw2,pw3,pw4],[9,241,53,237,293,305,285,229,25,5,49,41],[3,4,8,48,192,3,3,273,3,3584,48,192,48,192,208]),
([pw203,pw0,pw21,pw1,pw2,pw3],[9,37,209,229,32,28,33,5,285,3,24,121,129,173,53,49,48,17,237,293,105,117],[7,56,200,264,264,1537,2177,12289,2049,16384,32768,65552,393344,1572992,2883584]),
([pw203,pw0,pw1,pw2,pw10,pw3],[9,37,209,53,77,229,49,249,28,32,137,105,89,177,121,17,5,69,237,65,169],[7,56,224,800,3104,4105,8257,16385,10241,32840,65536,133128,262144,526400,1051136]),
([pw78,pw203,pw0,pw1,pw2,pw3],[229,285,121,9,5,49,105,293,129,173,237,53,41,117],[3,12,16,32,192,3,3,3,3,12,772,12,7168,192,9280]),
([pw195,pw203,pw0,pw1,pw2,pw3],[285,229,9,177,53,237,105,169,5,49,41,293],[3,12,16,32,192,3,3,3,3,12,12,12,1792,2368,192]),
([pw0,pw1,pw223,pw2,pw3,pw4],[241,5,1,12,121,9,25,293,4,53,17,237,289,33,205,229,0,28,305,285],[7,25,33,193,33,770,3074,4226,24578,264,392,229376,264320,559104,557184]),
([pw224,pw1,pw53,pw2,pw3,pw4],[5,3,20,121,237,52,12,105,229,36,241,1,17,293,189,33,9,25,305,285],[7,8,112,128,770,3073,4113,24577,33025,66576,140288,66816,270352,524560,532736]),
([pw200,pw224,pw0,pw1,pw2,pw3],[229,36,28,9,209,33,5,49,221,285,121,3,20,52,105,53,237,25,293,185,65],[7,25,97,385,513,1024,6208,8322,16384,32840,65672,393224,32960,786496,1310848]),
([pw225,pw0,pw1,pw2,pw3,pw4],[121,9,4,53,5,49,237,169,105,28,229,0,241,17,69,77,65,249,137],[3,28,100,388,3584,3,4129,3,5121,8232,16648,33800,65824,132128,263424]),
([pw104,pw224,pw1,pw2,pw3,pw4],[157,1,9,53,49,233,293,25,209,37,3,121,16,101,141,229,185,29,65,281],[1,14,52,196,772,3074,6160,8192,51200,10,65602,163842,262224,48,557120]),
([pw224,pw0,pw1,pw2,pw119,pw3],[121,5,3,40,49,16,36,229,28,105,53,241,9,25,293,77,185,221,65,281],[1,14,112,388,512,1026,6160,6272,26624,1042,32898,81922,131216,278544,540800]),
([pw0,pw226,pw1,pw2,pw3,pw4],[241,9,25,149,53,4,5,49,237,293,105,229,285,41,185,305],[3,3,3,13,3,112,416,1568,6144,8464,16912,6160,33536,6400,6656]),
([pw1,pw53,pw2,pw3,pw14,pw4],[121,5,53,17,81,297,57,3,129,49,25,105,4,141,269,117,165,12,237,52,285,221,293,229,36],[7,26,34,194,34,769,3073,4097,24577,100352,917504,3407872,4194304,9439232,17825920]),
([pw227,pw0,pw1,pw2,pw3,pw4],[12,121,9,53,5,193,49,105,293,28,229,0,129,25,269,297,117,221,137],[7,24,97,385,3584,26,4162,8322,17410,24,32904,33800,65728,132160,263296]),
([pw200,pw0,pw1,pw2,pw3,pw14],[121,141,269,5,33,205,49,73,221,105,137,229,28,36,53,129,25,9,197,117,193,293],[7,56,448,3584,14336,16393,32833,66049,131072,16456,262664,16392,524864,1056832,2097152]),
([pw205,pw0,pw21,pw2,pw3,pw4],[1,5,121,93,237,17,105,289,205,33,3,53,173,29,201,41,8,77,229,117,285],[7,8,50,194,770,3073,4113,5,24577,32768,67648,395264,524368,1310736,192]),
([pw0,pw21,pw1,pw2,pw3,pw206],[9,3,44,121,129,173,141,209,53,49,105,8,32,229,28,17,237,5,297,117,285],[7,9,49,9,193,256,512,7168,24578,229376,394240,401408,590848,1122304,1057792]),
([pw0,pw1,pw2,pw228,pw3,pw4],[53,93,49,177,121,25,101,141,269,17,197,77,229,193,249,105,169,28,0,137],[3,28,24,104,392,517,3,1025,6145,8196,8196,20484,98304,397312,561152]),
([pw0,pw1,pw2,pw119,pw3,pw14],[53,5,49,129,121,229,285,25,105,9,197,117,193,28,3,293],[3,28,112,400,512,3,97,1281,3,100,2308,4100,96,24608,32768]),
([pw0,pw1,pw2,pw10,pw3,pw206],[53,9,89,177,121,141,209,17,49,5,69,105,285,229,237,65,169,28,3],[7,10,18,10,98,385,512,3073,12289,16384,35072,12544,67584,397312,14336]),
([pw0,pw1,pw2,pw229,pw3,pw4],[53,9,1,129,49,121,37,209,237,5,93,197,77,229,65,105,293,285],[7,26,34,34,194,273,1537,2049,12289,272,49168,272,98304,139264,106496]),
([pw78,pw0,pw1,pw2,pw3,pw206],[121,9,5,49,105,8,32,229,285,129,173,237,53,41,69,117],[3,4,8,112,384,3,1537,3,385,14336,20496,384,34832,384,400]),
([pw195,pw205,pw0,pw2,pw3,pw4],[5,8,53,89,1,237,229,77,121,81,41,105,289,33,177,201,65,245],[7,28,32,6,196,273,1537,6145,8257,17424,272,32848,68608,132160,6208]),
([pw195,pw0,pw1,pw2,pw3,pw206],[9,177,53,237,105,169,285,229,5,49,41,297],[3,4,8,48,192,3,3,3,193,1792,2320,192,48,192,208]),
([pw31,pw0,pw1,pw2,pw206],[9,32,105,44,8,169,53,121,5,49,237,177,229,281,213],[15,18,38,14,449,3585,3,1856,28736,13824]),
([pw0,pw1,pw2,pw3,pw206,pw230],[121,9,129,49,277,213,237,297,33,285,5,65,105,3,273,229],[3,13,3,17,3,104,160,800,1024,6152,72,8200,20992,20480,32768]),
([pw231,pw0,pw1,pw2,pw3,pw206],[121,9,5,237,49,105,8,32,285,141,225,297,213,229,205,65,137],[3,4,24,224,256,3,25,3,1537,24,6176,26624,32808,24,73760]),
([pw0,pw1,pw2,pw3,pw206,pw232],[53,5,9,177,229,225,69,105,213,169,28,237,273,285],[3,12,12,52,12,3,193,273,3,640,3088,1024,4240,640,8192]),
([pw233,pw0,pw1,pw2,pw3,pw206],[9,177,5,53,49,105,169,229,141,209,69,33,205,285,237,221,265],[3,12,16,96,128,3,3,3,769,12,1060,6148,96,57344,73760]),
([pw0,pw234,pw1,pw2,pw3,pw4],[121,12,9,5,153,129,173,293,101,141,269,297,237,49,105,285,229,17,305],[7,25,97,385,1537,2056,12290,16514,98304,135176,2184,2056,266368,102400,98432]),
([pw235,pw1,pw53,pw2,pw3,pw4],[57,297,5,9,309,237,105,285,229,17,293,121,101],[7,8,48,64,384,6,530,6,6,48,7168,384,48,400,384]),
([pw235,pw200,pw0,pw1,pw2,pw3],[285,229,9,53,5,49,237,105,293,121,101,185,65],[3,4,24,96,128,3,3,3,3,24,96,1792,24,2312,4384]),
([pw0,pw1,pw2,pw236,pw3,pw4],[53,5,49,177,121,293,101,141,269,105,33,205,237,65,229,285],[3,28,24,104,392,3,3,545,3073,4100,8228,4100,544,49152,544]),
([pw235,pw0,pw1,pw2,pw119,pw3],[9,53,5,49,16,36,285,229,105,129,121,293,101,185,65],[1,6,56,192,256,6,1544,192,7168,6,194,10242,200,18440,192]),
([pw237,pw0,pw1,pw2,pw3,pw4],[121,9,53,5,49,309,237,105,305,293,301,229,33,285],[3,12,112,896,3072,3,97,3,3073,12,772,5124,96,9248,3328]),
([pw32,pw1,pw53,pw2,pw3,pw4],[5,297,9,121,8,237,309,293,229,285,17],[3,28,96,128,768,3,1057,3,3,100,20,772,96,800,768]),
([pw200,pw32,pw0,pw1,pw2,pw3],[229,285,121,5,197,49,193,293,237,9,105,101],[3,3,3,3,3,4,24,96,128,24,288,3584,24,24,96]),
([pw104,pw32,pw1,pw2,pw3,pw4],[9,8,1,53,49,233,209,37,153,121,173,293,269,141,197,29,201,117,101,133,229],[3,13,49,3,193,772,1552,2048,12800,12,16388,98308,393232,48,1835008]),
([pw32,pw0,pw1,pw2,pw119,pw3],[121,5,197,49,193,229,285,293,241,9,105,101],[1,6,24,96,128,6,776,96,3328,6,98,6,104,24,96]),
([pw1,pw108,pw53,pw2,pw3,pw4],[5,3,20,241,1,17,45,293,289,33,205,121,237,52,12,105,229,36,9,25,305,285],[7,25,97,385,1537,2048,28672,32768,196610,266248,524424,327688,1052800,2166784,2162816]),
([pw1,pw53,pw2,pw3,pw238,pw4],[121,5,153,17,45,297,20,3,129,173,25,105,9,141,269,117,165,12,237,52,285,221,293,229,36],[7,26,34,194,34,769,3073,4096,24577,100352,917504,3407872,4194304,9439232,17825920]),
([pw239,pw1,pw53,pw2,pw3,pw4],[297,5,9,309,237,105,285,229,17,293,121,101],[3,4,24,32,192,3,265,3,3,24,3584,192,24,200,192]),
([pw109,pw1,pw53,pw2,pw3,pw4],[5,297,121,237,309,293,229,285,17,9,105,101],[3,4,24,32,192,3,265,3,3,24,3584,192,24,200,192]),
([pw0,pw1,pw2,pw119,pw240,pw3],[53,5,49,241,217,37,229,9,105,293,261,221,257,65,285,3],[3,28,104,128,776,3,1089,3,769,2116,4100,8452,16384,832,33024]),
([pw241,pw0,pw1,pw2,pw119,pw3],[9,53,5,49,16,36,229,293,105,241,217,285,209,253,73,65],[1,6,56,64,384,6,1544,6656,384,6,10242,386,18440,32904,384]),
([pw0,pw1,pw2,pw119,pw3,pw242],[53,5,9,129,49,217,121,261,197,257,193,28,293,229],[3,28,36,68,36,3,129,257,129,528,1040,528,6144,8192,2048]),
([pw116,pw0,pw1,pw2,pw119,pw3],[9,121,5,197,49,193,285,105,129,37,209,77,205,73,221,229,293,281],[3,12,48,64,128,3,273,1537,3,12,6148,12,24592,48,229376]),
([pw243,pw0,pw1,pw2,pw3,pw4],[9,177,5,49,237,293,105,285,229,65],[3,4,24,96,384,3,3,3,385,24,96,384,552,24,96]),
([pw129,pw0,pw1,pw2,pw3,pw4],[9,5,197,237,49,105,293,229,285,65],[1,6,24,96,384,6,24,96,384,6,6,386,552,24,96])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p9_D4 : List StD := [
([pw53,pw199,pw2,pw3,pw4],[241,5,1,9,25,109,17,45,293,105,33,205,305,285,229],[7,9,49,9,194,770,3074,4352,24576,24832]),
([pw200,pw0,pw199,pw2,pw3],[9,37,209,5,33,205,49,73,221,229,285,53,237,25,109,69,105,65,181],[7,56,448,1536,2057,4161,24577,2120,98312,393280]),
([pw104,pw199,pw2,pw3,pw4],[1,9,53,49,233,109,25,209,37,21,101,29,201,65,181,229,285],[7,26,98,386,5,1537,6145,24584,24,98304]),
([pw0,pw199,pw2,pw119,pw3],[53,5,9,241,25,109,77,205,69,105,49,73,221,65,181,229,285],[3,12,12,52,3,193,769,7168,25600,98304]),
([pw201,pw0,pw199,pw2,pw3],[9,37,209,5,33,205,49,73,221,229,285,53,237,25,109,69,105,65,181],[7,56,448,1536,2057,4161,24577,2120,98312,393280]),
([pw0,pw199,pw2,pw202,pw3],[53,5,9,241,25,109,77,205,69,105,49,73,221,65,181,229,285],[3,12,12,52,3,193,769,7168,25600,98304]),
([pw203,pw1,pw53,pw2,pw3],[5,33,205,9,37,209,285,229,121,17,45,293,105,129,49,117,165],[7,56,192,192,265,1537,6145,24584,264,100352]),
([pw0,pw1,pw2,pw204,pw3],[53,5,9,241,25,161,77,205,69,185,49,73,221,65,181,229,285],[3,12,12,52,3,193,769,7168,25600,98304]),
([pw205,pw53,pw2,pw3,pw4],[1,5,121,45,17,105,289,205,33,13,41,29,201,117,165,285,229],[7,26,98,386,1537,5,6145,24608,98304,96]),
([pw1,pw53,pw2,pw3,pw206],[121,5,1,17,45,297,129,49,9,141,209,105,117,165,285,229],[7,26,34,34,193,257,1537,14336,49152,51200]),
([pw0,pw1,pw2,pw3,pw207],[121,5,1,129,173,9,141,209,17,97,297,105,117,165,285,229],[7,25,33,193,770,1026,1026,14336,49152,51200]),
([pw208,pw0,pw1,pw2,pw3],[209,121,53,5,49,193,229,105,281,129],[3,12,48,448,3,529,3,12,388,48]),
([pw209,pw0,pw1,pw2,pw3],[121,9,205,53,221,49,105,169,69],[3,12,48,192,3,49,3,12,324,208]),
([pw0,pw1,pw210,pw3,pw206],[121,5,1,237,49,9,141,209,297,65,105,137,265],[7,25,33,193,26,258,258,1544,24,7168]),
([pw211,pw0,pw1,pw3,pw206],[49,9,121,41,5,181,65,237,221,209,61,105,33,273],[7,25,97,129,6,6,770,3080,4360,10496]),
([pw212,pw1,pw53,pw2,pw3],[5,33,205,9,37,209,285,229,121,17,45,293,105,129,49,117,165],[7,56,192,192,265,1537,6145,24584,264,100352]),
([pw1,pw53,pw2,pw3,pw213],[121,5,1,17,45,297,129,49,9,141,209,105,117,165,285,229],[7,26,34,34,193,257,1537,14336,49152,51200]),
([pw0,pw1,pw2,pw119,pw214],[53,5,9,241,105,101,77,205,293,49,73,221,117],[3,12,12,52,3,193,273,3584,4624,272]),
([pw215,pw0,pw1,pw2,pw119],[101,105,9,5,53,165,49,229,281,113],[7,26,98,386,25,577,385,24,392,448])]
def p9_D3 : List StD := []
theorem p9_I3 : LevelN true p9_T 3 p9_D3 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p9_C4x0 : levelOK true p9_T p9_t 3 (p9_D3.map Prod.fst) ((p9_D4.drop (0*32)).take 32) = true := by decide +kernel
theorem p9_I4 : LevelN true p9_T 4 p9_D4 := levelStep p9_B p9_W p9_I3 (chunks 32 p9_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p9_C4x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p9_C5x0 : levelOK true p9_T p9_t 4 (p9_D4.map Prod.fst) ((p9_D5.drop (0*32)).take 32) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p9_C5x1 : levelOK true p9_T p9_t 4 (p9_D4.map Prod.fst) ((p9_D5.drop (1*32)).take 32) = true := by decide +kernel
theorem p9_I5 : LevelN true p9_T 5 p9_D5 := levelStep p9_B p9_W p9_I4 (chunks 32 p9_D5 2 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p9_C5x0
  · exact p9_C5x1
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p9_C6x0 : levelOK true p9_T p9_t 5 (p9_D5.map Prod.fst) ((p9_D6.drop (0*32)).take 32) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p9_C6x1 : levelOK true p9_T p9_t 5 (p9_D5.map Prod.fst) ((p9_D6.drop (1*32)).take 32) = true := by decide +kernel
theorem p9_I6 : LevelN true p9_T 6 p9_D6 := levelStep p9_B p9_W p9_I5 (chunks 32 p9_D6 2 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p9_C6x0
  · exact p9_C6x1
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p9_C7x0 : levelOK true p9_T p9_t 6 (p9_D6.map Prod.fst) ((p9_D7.drop (0*32)).take 32) = true := by decide +kernel
theorem p9_I7 : LevelN true p9_T 7 p9_D7 := levelStep p9_B p9_W p9_I6 (chunks 32 p9_D7 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p9_C7x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p9_C8x0 : levelOK true p9_T p9_t 7 (p9_D7.map Prod.fst) ((p9_D8.drop (0*32)).take 32) = true := by decide +kernel
theorem p9_I8 : LevelN true p9_T 8 p9_D8 := levelStep p9_B p9_W p9_I7 (chunks 32 p9_D8 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p9_C8x0
  ))
theorem p9_L : LowN true p9_R p9_T 9 := lowSearch p9_B p9_I8 (by decide +kernel)
def p10_T : Nat := 0xfeeefee8feeefee8feeefee8feeefee8
def p10_R : List Nat := [0, 1, 2, 3, 4]
def p10_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,1,9),(4,1,17)]
theorem p10_B : baseOK p10_T p10_R p10_E = true := by decide +kernel
def p10_Z : List SliceD := [(pw24,7,[0, 1, 2, 3])]
theorem p10_Y : ∀ s ∈ p10_Z, SliceN true p10_R p10_T s := by
  unfold p10_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p10_B p2_B p2_L (by decide +kernel),by simp⟩
def p10_C : List (Nat × List Nat) := [(0,[])]
def p10_t : Tabs := (p10_C.map (mkCut true p10_Z),[],[],[])
theorem p10_W : TabsP true p10_R p10_T p10_t := ⟨cutsGood p10_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p10_D7 : List StD := [
([pw0,pw1,pw2,pw3,pw4],[0],[1,1,1,1,1,1,1,1,1,1])]
def p10_D6 : List StD := []
theorem p10_I6 : LevelN true p10_T 6 p10_D6 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p10_C7x0 : levelOK true p10_T p10_t 6 (p10_D6.map Prod.fst) ((p10_D7.drop (0*32)).take 32) = true := by decide +kernel
theorem p10_I7 : LevelN true p10_T 7 p10_D7 := levelStep p10_B p10_W p10_I6 (chunks 32 p10_D7 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p10_C7x0
  ))
theorem p10_L : LowN true p10_R p10_T 8 := lowSearch p10_B p10_I7 (by decide +kernel)
def p11_T : Nat := 0xfefefee8fefefee8fefefee8fefefee8
def p11_R : List Nat := [0, 1, 2, 3, 4]
def p11_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,1,9),(4,1,17)]
theorem p11_B : baseOK p11_T p11_R p11_E = true := by decide +kernel
def p11_Z : List SliceD := [(pw24,7,[0, 1, 2, 3])]
theorem p11_Y : ∀ s ∈ p11_Z, SliceN true p11_R p11_T s := by
  unfold p11_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p11_B p2_B p2_L (by decide +kernel),by simp⟩
def p11_C : List (Nat × List Nat) := [(0,[])]
def p11_t : Tabs := (p11_C.map (mkCut true p11_Z),[],[],[])
theorem p11_W : TabsP true p11_R p11_T p11_t := ⟨cutsGood p11_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p11_D7 : List StD := [
([pw0,pw1,pw2,pw3,pw4],[0],[1,1,1,1,1,1,1,1,1,1])]
def p11_D6 : List StD := []
theorem p11_I6 : LevelN true p11_T 6 p11_D6 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p11_C7x0 : levelOK true p11_T p11_t 6 (p11_D6.map Prod.fst) ((p11_D7.drop (0*32)).take 32) = true := by decide +kernel
theorem p11_I7 : LevelN true p11_T 7 p11_D7 := levelStep p11_B p11_W p11_I6 (chunks 32 p11_D7 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p11_C7x0
  ))
theorem p11_L : LowN true p11_R p11_T 8 := lowSearch p11_B p11_I7 (by decide +kernel)
def p12_T : Nat := 0xeee8e8a0eee8e8a0eee8e8a0eee8e8a0
def p12_R : List Nat := [0, 1, 2, 3, 4]
def p12_E : List (Nat × Nat × Nat) := [(0,4,5),(1,9,11),(2,1,5),(3,3,11),(4,3,19)]
theorem p12_B : baseOK p12_T p12_R p12_E = true := by decide +kernel
def p12_Z : List SliceD := [(pw7,7,[0, 1, 3, 4])]
theorem p12_Y : ∀ s ∈ p12_Z, SliceN true p12_R p12_T s := by
  unfold p12_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p12_B p3_B p3_L (by decide +kernel),by simp⟩
def p12_C : List (Nat × List Nat) := [(0,[])]
def p12_t : Tabs := (p12_C.map (mkCut true p12_Z),[],[],[])
theorem p12_W : TabsP true p12_R p12_T p12_t := ⟨cutsGood p12_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p12_D7 : List StD := [
([pw0,pw1,pw2,pw3,pw4],[0],[1,1,1,1,1,1,1,1,1,1])]
def p12_D6 : List StD := []
theorem p12_I6 : LevelN true p12_T 6 p12_D6 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p12_C7x0 : levelOK true p12_T p12_t 6 (p12_D6.map Prod.fst) ((p12_D7.drop (0*32)).take 32) = true := by decide +kernel
theorem p12_I7 : LevelN true p12_T 7 p12_D7 := levelStep p12_B p12_W p12_I6 (chunks 32 p12_D7 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p12_C7x0
  ))
theorem p12_L : LowN true p12_R p12_T 8 := lowSearch p12_B p12_I7 (by decide +kernel)
def p13_T : Nat := 0xfffefeeafffefeeafffefeeafffefeea
def p13_R : List Nat := [0, 1, 2, 3, 4]
def p13_E : List (Nat × Nat × Nat) := [(0,0,1),(1,4,6),(2,2,6),(3,2,10),(4,2,18)]
theorem p13_B : baseOK p13_T p13_R p13_E = true := by decide +kernel
def p13_Z : List SliceD := [(pw9,7,[1, 2, 3, 4])]
theorem p13_Y : ∀ s ∈ p13_Z, SliceN true p13_R p13_T s := by
  unfold p13_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p13_B p2_B p2_L (by decide +kernel),by simp⟩
def p13_C : List (Nat × List Nat) := [(0,[])]
def p13_t : Tabs := (p13_C.map (mkCut true p13_Z),[],[],[])
theorem p13_W : TabsP true p13_R p13_T p13_t := ⟨cutsGood p13_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p13_D7 : List StD := [
([pw0,pw1,pw2,pw3,pw4],[0],[1,1,1,1,1,1,1,1,1,1])]
def p13_D6 : List StD := []
theorem p13_I6 : LevelN true p13_T 6 p13_D6 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C7x0 : levelOK true p13_T p13_t 6 (p13_D6.map Prod.fst) ((p13_D7.drop (0*32)).take 32) = true := by decide +kernel
theorem p13_I7 : LevelN true p13_T 7 p13_D7 := levelStep p13_B p13_W p13_I6 (chunks 32 p13_D7 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p13_C7x0
  ))
theorem p13_L : LowN true p13_R p13_T 8 := lowSearch p13_B p13_I7 (by decide +kernel)
def p14_T : Nat := 0xeae8eae8eae8eae8eae8eae8eae8eae8
def p14_R : List Nat := [0, 1, 2, 3]
def p14_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,1,9)]
theorem p14_B : baseOK p14_T p14_R p14_E = true := by decide +kernel
def p14_Z : List SliceD := [(pw6,4,[0, 1, 2])]
theorem p14_Y : ∀ s ∈ p14_Z, SliceN true p14_R p14_T s := by
  unfold p14_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p14_B p1_B p1_L (by decide +kernel),by simp⟩
def p14_C : List (Nat × List Nat) := [(0,[])]
def p14_t : Tabs := (p14_C.map (mkCut true p14_Z),[(3,1),(3,2),(5,1),(5,4),(6,2),(6,4)],[],[])
theorem p14_W : TabsP true p14_R p14_T p14_t := ⟨cutsGood p14_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p14_D4 : List StD := [
([pw0,pw1,pw2,pw3],[21,13,1,5,17,9,0],[15,58,66,53,65,80])]
def p14_D3 : List StD := []
theorem p14_I3 : LevelN true p14_T 3 p14_D3 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p14_C4x0 : levelOK true p14_T p14_t 3 (p14_D3.map Prod.fst) ((p14_D4.drop (0*32)).take 32) = true := by decide +kernel
theorem p14_I4 : LevelN true p14_T 4 p14_D4 := levelStep p14_B p14_W p14_I3 (chunks 32 p14_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p14_C4x0
  ))
theorem p14_L : LowN true p14_R p14_T 5 := lowSearch p14_B p14_I4 (by decide +kernel)
def p15_T : Nat := 0xeee8eee8eee8eee8eee8eee8eee8eee8
def p15_R : List Nat := [0, 1, 2, 3]
def p15_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,1,9)]
theorem p15_B : baseOK p15_T p15_R p15_E = true := by decide +kernel
def p15_Z : List SliceD := [(pw6,4,[0, 1, 2])]
theorem p15_Y : ∀ s ∈ p15_Z, SliceN true p15_R p15_T s := by
  unfold p15_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p15_B p1_B p1_L (by decide +kernel),by simp⟩
def p15_C : List (Nat × List Nat) := [(0,[])]
def p15_t : Tabs := (p15_C.map (mkCut true p15_Z),[(3,1),(3,2),(5,1),(5,4),(6,2),(6,4),(9,1),(9,8),(10,2),(10,8)],[],[])
theorem p15_W : TabsP true p15_R p15_T p15_t := ⟨cutsGood p15_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p15_D4 : List StD := [
([pw0,pw1,pw2,pw3],[21,13,1,5,17,9,33,25,29,37,0],[15,58,450,53,705,1104])]
def p15_D3 : List StD := []
theorem p15_I3 : LevelN true p15_T 3 p15_D3 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p15_C4x0 : levelOK true p15_T p15_t 3 (p15_D3.map Prod.fst) ((p15_D4.drop (0*32)).take 32) = true := by decide +kernel
theorem p15_I4 : LevelN true p15_T 4 p15_D4 := levelStep p15_B p15_W p15_I3 (chunks 32 p15_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p15_C4x0
  ))
theorem p15_L : LowN true p15_R p15_T 5 := lowSearch p15_B p15_I4 (by decide +kernel)
def p16_T : Nat := 0xa880a880a880a880a880a880a880a880
def p16_R : List Nat := [0, 1, 2, 3]
def p16_E : List (Nat × Nat × Nat) := [(0,6,7),(1,5,7),(2,3,7),(3,3,11)]
theorem p16_B : baseOK p16_T p16_R p16_E = true := by decide +kernel
def p16_Z : List SliceD := [(pw0,4,[1, 2, 3])]
theorem p16_Y : ∀ s ∈ p16_Z, SliceN true p16_R p16_T s := by
  unfold p16_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=1) p16_B p1_B p1_L (by decide +kernel),by simp⟩
def p16_C : List (Nat × List Nat) := [(0,[])]
def p16_t : Tabs := (p16_C.map (mkCut true p16_Z),[],[],[])
theorem p16_W : TabsP true p16_R p16_T p16_t := ⟨cutsGood p16_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p16_D4 : List StD := [
([pw0,pw1,pw2,pw3],[0],[1,1,1,1,1,1])]
def p16_D3 : List StD := []
theorem p16_I3 : LevelN true p16_T 3 p16_D3 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p16_C4x0 : levelOK true p16_T p16_t 3 (p16_D3.map Prod.fst) ((p16_D4.drop (0*32)).take 32) = true := by decide +kernel
theorem p16_I4 : LevelN true p16_T 4 p16_D4 := levelStep p16_B p16_W p16_I3 (chunks 32 p16_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p16_C4x0
  ))
theorem p16_L : LowN true p16_R p16_T 5 := lowSearch p16_B p16_I4 (by decide +kernel)
def p17_T : Nat := 0xeae8e888eae8e888eae8e888eae8e888
def p17_R : List Nat := [0, 1, 2, 3, 4]
def p17_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,9,13),(3,5,13),(4,5,21)]
theorem p17_B : baseOK p17_T p17_R p17_E = true := by decide +kernel
def p17_Z : List SliceD := [(pw24,5,[0, 1, 2, 3]),(pw4,5,[0, 1, 2, 3]),(pw6,5,[0, 1, 2, 4]),(pw3,5,[0, 1, 2, 4]),(pw2,5,[0, 1, 3, 4]),(pw8,5,[0, 2, 3, 4]),(pw0,5,[1, 2, 3, 4]),(pw262,4,[2, 3, 4])]
theorem p17_Y : ∀ s ∈ p17_Z, SliceN true p17_R p17_T s := by
  unfold p17_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p17_B p5_B p5_L (by decide +kernel),mkSlice (w:=16) p17_B p14_B p14_L (by decide +kernel),mkSlice (w:=0) p17_B p5_B p5_L (by decide +kernel),mkSlice (w:=8) p17_B p14_B p14_L (by decide +kernel),mkSlice (w:=4) p17_B p15_B p15_L (by decide +kernel),mkSlice (w:=0) p17_B p16_B p16_L (by decide +kernel),mkSlice (w:=1) p17_B p6_B p6_L (by decide +kernel),mkSlice (w:=1) p17_B p1_B p1_L (by decide +kernel),by simp⟩
def p17_C : List (Nat × List Nat) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(6,[]),(7,[])]
def p17_t : Tabs := (p17_C.map (mkCut true p17_Z),[(3,0),(3,1),(3,2),(7,5),(7,6),(11,9),(11,10),(13,5),(13,12),(14,6),(14,10),(14,12),(19,1),(19,17),(19,18),(21,5),(22,6),(22,18),(25,9),(25,17)],[],[[]])
theorem p17_W : TabsP true p17_R p17_T p17_t := ⟨cutsGood p17_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p17_D7 : List StD := [
([pw0,pw1,pw2,pw3,pw4],[20,45,24,9,28,1,3,41,17,16,8,37,25,12,0,65,57,4,5,49,77,73],[63,972,15372,245772,262851,273411,704515,1060480,2278016,1223680])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p17_D6 : List StD := [
([pw20,pw0,pw1,pw2,pw3,pw4],[16,5,20,13,28,37,8,29,12,65,0,61,4,45,9,25,57,53,69,41,73,77],[1,30,17,480,7680,8210,17,49200,82448,19,8242,131602,786433,786433,3146272]),
([pw195,pw0,pw1,pw2,pw3,pw4],[9,28,33,16,37,8,29,12,65,0,61,4,57,21,5,53,69,41,73,77],[7,10,2,240,3840,7,7,7,4355,10,24594,41218,196616,196616,786704])]
def p17_D5 : List StD := []
theorem p17_I5 : LevelN true p17_T 5 p17_D5 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p17_C6x0 : levelOK true p17_T p17_t 5 (p17_D5.map Prod.fst) ((p17_D6.drop (0*32)).take 32) = true := by decide +kernel
theorem p17_I6 : LevelN true p17_T 6 p17_D6 := levelStep p17_B p17_W p17_I5 (chunks 32 p17_D6 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p17_C6x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p17_C7x0 : levelOK true p17_T p17_t 6 (p17_D6.map Prod.fst) ((p17_D7.drop (0*32)).take 32) = true := by decide +kernel
theorem p17_I7 : LevelN true p17_T 7 p17_D7 := levelStep p17_B p17_W p17_I6 (chunks 32 p17_D7 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p17_C7x0
  ))
theorem p17_L : LowN true p17_R p17_T 8 := lowSearch p17_B p17_I7 (by decide +kernel)
def p18_T : Nat := 0xeee8eae0eee8eae0eee8eae0eee8eae0
def p18_R : List Nat := [0, 1, 2, 3, 4]
def p18_E : List (Nat × Nat × Nat) := [(0,4,5),(1,4,6),(2,1,5),(3,1,9),(4,3,19)]
theorem p18_B : baseOK p18_T p18_R p18_E = true := by decide +kernel
def p18_Z : List SliceD := [(pw4,5,[0, 1, 2, 3]),(pw6,5,[2, 0, 1, 4]),(pw7,5,[0, 3, 1, 4]),(pw1,5,[2, 0, 3, 4])]
theorem p18_Y : ∀ s ∈ p18_Z, SliceN true p18_R p18_T s := by
  unfold p18_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=16) p18_B p15_B p15_L (by decide +kernel),mkSlice (w:=0) p18_B p4_B p4_L (by decide +kernel),mkSlice (w:=0) p18_B p5_B p5_L (by decide +kernel),mkSlice (w:=2) p18_B p6_B p6_L (by decide +kernel),by simp⟩
def p18_C : List (Nat × List Nat) := [(0,[]),(1,[]),(2,[]),(3,[])]
def p18_t : Tabs := (p18_C.map (mkCut true p18_Z),[(5,1),(6,2),(6,4),(6,10),(9,1),(19,3),(19,17),(26,10),(26,18)],[],[])
theorem p18_W : TabsP true p18_R p18_T p18_t := ⟨cutsGood p18_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p18_D6 : List StD := [
([pw0,pw1,pw2,pw3,pw4],[12,9,25,8,1,5,4,17,33,0,29,21,13],[7,56,448,3584,7,195,7,4184,536,448])]
def p18_D5 : List StD := []
theorem p18_I5 : LevelN true p18_T 5 p18_D5 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p18_C6x0 : levelOK true p18_T p18_t 5 (p18_D5.map Prod.fst) ((p18_D6.drop (0*32)).take 32) = true := by decide +kernel
theorem p18_I6 : LevelN true p18_T 6 p18_D6 := levelStep p18_B p18_W p18_I5 (chunks 32 p18_D6 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p18_C6x0
  ))
theorem p18_L : LowN true p18_R p18_T 7 := lowSearch p18_B p18_I6 (by decide +kernel)
def p19_T : Nat := 0xeae8ea88eae8ea88eae8ea88eae8ea88
def p19_R : List Nat := [0, 1, 2, 3, 4]
def p19_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,10,14),(3,1,9),(4,5,21)]
theorem p19_B : baseOK p19_T p19_R p19_E = true := by decide +kernel
def p19_Z : List SliceD := [(pw24,5,[0, 1, 3, 2]),(pw4,5,[0, 1, 2, 3]),(pw6,5,[0, 1, 2, 4]),(pw2,5,[0, 1, 3, 4])]
theorem p19_Y : ∀ s ∈ p19_Z, SliceN true p19_R p19_T s := by
  unfold p19_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p19_B p4_B p4_L (by decide +kernel),mkSlice (w:=16) p19_B p14_B p14_L (by decide +kernel),mkSlice (w:=0) p19_B p5_B p5_L (by decide +kernel),mkSlice (w:=4) p19_B p15_B p15_L (by decide +kernel),by simp⟩
def p19_C : List (Nat × List Nat) := [(0,[]),(1,[]),(2,[]),(3,[])]
def p19_t : Tabs := (p19_C.map (mkCut true p19_Z),[(3,0),(3,1),(3,2),(3,5),(3,6),(3,10),(3,17),(3,18),(3,26),(7,1),(7,2),(7,10),(9,0),(9,1),(9,5),(9,8),(9,10),(9,12),(9,17),(11,2),(13,1),(13,8),(14,4),(14,6),(14,8),(14,10),(14,12),(14,26),(14,28),(19,1),(19,2),(19,10),(21,1),(21,4),(21,5),(21,17),(22,6)],[],[[]])
theorem p19_W : TabsP true p19_R p19_T p19_t := ⟨cutsGood p19_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p19_D6 : List StD := [
([pw0,pw1,pw2,pw3,pw4],[3,105,61,5,9,12,101,141,8,53,93,0,137,145,73],[31,228,1812,14340,234,1802,14338,224,224,19200])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p19_D5 : List StD := [
([pw19,pw0,pw1,pw2,pw3,pw4],[9,5,101,12,3,53,8,137,4,0,65,105,61,69,93,133,141,113,73],[1,2,28,112,896,7168,12292,20512,36992,67588,18464,133248,16420,65668,262304]),
([pw0,pw1,pw17,pw2,pw3,pw4],[65,9,5,61,17,41,21,77,29,121,105,13,37,93,53,25,117,3,101,12,8,0,137,4,129,73],[7,8,50,194,770,1024,6148,24580,98308,917504,1187840,14680064,24576,21233664,37756928]),
([pw262,pw0,pw1,pw2,pw3,pw4],[61,5,101,141,93,53,145,137,105,9,1,73],[1,2,12,48,192,1792,12,48,192,12,48,192,12,12,2128]),
([pw34,pw0,pw1,pw2,pw3,pw4],[9,105,141,101,53,93,137,145,61,5,1,73],[1,2,12,48,192,1792,12,48,192,12,48,192,12,12,2128])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p19_D4 : List StD := [
([pw245,pw0,pw1,pw3,pw4],[9,17,85,5,13,97,53,57,81,101,109,129,61,29,121,93,25,117,73,137],[7,56,448,3584,4105,4161,24577,32840,196616,786496]),
([pw0,pw1,pw2,pw246,pw4],[61,21,69,45,93,9,33,125,141,101,53,105,113,137,73],[3,13,49,193,768,1040,14336,784,768,24592]),
([pw0,pw1,pw155,pw3,pw4],[61,5,1,17,41,9,29,121,13,37,93,53,25,117,101,109,129,73,137],[7,25,33,193,770,3074,12290,3072,114688,394240]),
([pw16,pw0,pw1,pw2,pw4],[49,9,53,5,89,81,57,137,73,17,41,121,25,101,129],[3,28,100,388,3,1537,2177,24,4232,24704])]
def p19_D3 : List StD := []
theorem p19_I3 : LevelN true p19_T 3 p19_D3 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p19_C4x0 : levelOK true p19_T p19_t 3 (p19_D3.map Prod.fst) ((p19_D4.drop (0*32)).take 32) = true := by decide +kernel
theorem p19_I4 : LevelN true p19_T 4 p19_D4 := levelStep p19_B p19_W p19_I3 (chunks 32 p19_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p19_C4x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p19_C5x0 : levelOK true p19_T p19_t 4 (p19_D4.map Prod.fst) ((p19_D5.drop (0*32)).take 32) = true := by decide +kernel
theorem p19_I5 : LevelN true p19_T 5 p19_D5 := levelStep p19_B p19_W p19_I4 (chunks 32 p19_D5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p19_C5x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p19_C6x0 : levelOK true p19_T p19_t 5 (p19_D5.map Prod.fst) ((p19_D6.drop (0*32)).take 32) = true := by decide +kernel
theorem p19_I6 : LevelN true p19_T 6 p19_D6 := levelStep p19_B p19_W p19_I5 (chunks 32 p19_D6 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p19_C6x0
  ))
theorem p19_L : LowN true p19_R p19_T 7 := lowSearch p19_B p19_I6 (by decide +kernel)
def p20_T : Nat := 0xfeeefeeafeeefeeafeeefeeafeeefeea
def p20_R : List Nat := [0, 1, 2, 3, 4]
def p20_E : List (Nat × Nat × Nat) := [(0,0,1),(1,4,6),(2,2,6),(3,2,10),(4,2,18)]
theorem p20_B : baseOK p20_T p20_R p20_E = true := by decide +kernel
def p20_Z : List SliceD := [(pw24,5,[0, 1, 2, 3])]
theorem p20_Y : ∀ s ∈ p20_Z, SliceN true p20_R p20_T s := by
  unfold p20_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p20_B p6_B p6_L (by decide +kernel),by simp⟩
def p20_C : List (Nat × List Nat) := [(0,[])]
def p20_t : Tabs := (p20_C.map (mkCut true p20_Z),[(1,0),(6,4)],[],[])
theorem p20_W : TabsP true p20_R p20_T p20_t := ⟨cutsGood p20_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p20_D5 : List StD := [
([pw0,pw1,pw2,pw3,pw4],[5,1,0],[7,6,6,6,5,5,5,4,4,4])]
def p20_D4 : List StD := []
theorem p20_I4 : LevelN true p20_T 4 p20_D4 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p20_C5x0 : levelOK true p20_T p20_t 4 (p20_D4.map Prod.fst) ((p20_D5.drop (0*32)).take 32) = true := by decide +kernel
theorem p20_I5 : LevelN true p20_T 5 p20_D5 := levelStep p20_B p20_W p20_I4 (chunks 32 p20_D5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p20_C5x0
  ))
theorem p20_L : LowN true p20_R p20_T 6 := lowSearch p20_B p20_I5 (by decide +kernel)
def p21_T : Nat := 0xfffefeeefffefeeefffefeeefffefeee
def p21_R : List Nat := [0, 1, 2, 3, 4]
def p21_E : List (Nat × Nat × Nat) := [(0,0,1),(1,0,2),(2,8,12),(3,4,12),(4,4,20)]
theorem p21_B : baseOK p21_T p21_R p21_E = true := by decide +kernel
def p21_Z : List SliceD := [(pw8,5,[0, 2, 3, 4])]
theorem p21_Y : ∀ s ∈ p21_Z, SliceN true p21_R p21_T s := by
  unfold p21_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p21_B p6_B p6_L (by decide +kernel),by simp⟩
def p21_C : List (Nat × List Nat) := [(0,[])]
def p21_t : Tabs := (p21_C.map (mkCut true p21_Z),[(1,0),(2,0)],[],[])
theorem p21_W : TabsP true p21_R p21_T p21_t := ⟨cutsGood p21_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p21_D5 : List StD := [
([pw0,pw1,pw2,pw3,pw4],[5,1,0],[7,6,6,6,5,5,5,4,4,4])]
def p21_D4 : List StD := []
theorem p21_I4 : LevelN true p21_T 4 p21_D4 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p21_C5x0 : levelOK true p21_T p21_t 4 (p21_D4.map Prod.fst) ((p21_D5.drop (0*32)).take 32) = true := by decide +kernel
theorem p21_I5 : LevelN true p21_T 5 p21_D5 := levelStep p21_B p21_W p21_I4 (chunks 32 p21_D5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p21_C5x0
  ))
theorem p21_L : LowN true p21_R p21_T 6 := lowSearch p21_B p21_I5 (by decide +kernel)
def ptopT : Nat := 0xfeeefee8feeae8e0feeefee8feeae8e0
def ptopR : List Nat := [0, 1, 2, 3, 4, 5]
def ptopE : List (Nat × Nat × Nat) := [(0,4,5),(1,4,6),(2,1,5),(3,3,11),(4,1,17),(5,3,35)]
theorem ptopB : baseOK ptopT ptopR ptopE = true := by decide +kernel
def ptopZ : List SliceD := [(pw24,10,[2, 0, 1, 3, 5]),(pw266,9,[0, 2, 1, 4, 3]),(pw5,8,[0, 1, 2, 3, 4]),(pw3,8,[0, 1, 2, 4, 5]),(pw7,8,[0, 1, 4, 3, 5]),(pw1,8,[2, 0, 3, 4, 5]),(pw9,8,[1, 2, 3, 4, 5]),(pw6,7,[0, 1, 2, 4, 5]),(pw8,7,[0, 2, 3, 4, 5]),(pw267,7,[0, 1, 2, 3]),(pw268,7,[0, 1, 2, 4]),(pw25,7,[0, 1, 2, 5]),(pw269,7,[0, 1, 3, 5]),(pw78,7,[0, 3, 4, 5]),(pw4,6,[0, 1, 2, 3, 5]),(pw0,6,[2, 4, 1, 3, 5]),(pw270,5,[0, 1, 2, 3]),(pw271,5,[0, 1, 2, 4]),(pw272,5,[0, 4, 1, 3]),(pw273,5,[0, 1, 3, 4]),(pw274,5,[0, 2, 4, 3]),(pw275,5,[2, 0, 3, 4]),(pw276,5,[0, 2, 3, 4]),(pw277,5,[1, 2, 3, 4]),(pw278,5,[1, 2, 3, 4]),(pw279,5,[2, 0, 1, 5]),(pw280,5,[0, 2, 3, 5]),(pw281,5,[1, 2, 3, 5]),(pw282,5,[2, 1, 3, 5]),(pw29,5,[1, 2, 3, 5]),(pw283,5,[0, 4, 1, 5]),(pw30,5,[0, 1, 4, 5]),(pw264,5,[2, 0, 4, 5]),(pw31,5,[0, 2, 4, 5]),(pw32,5,[1, 2, 4, 5]),(pw284,5,[1, 3, 4, 5]),(pw263,5,[4, 1, 3, 5]),(pw34,5,[2, 3, 4, 5]),(pw285,4,[0, 2, 1, 4]),(pw286,4,[0, 1, 2]),(pw287,4,[0, 1, 3]),(pw288,4,[0, 2, 3]),(pw289,4,[1, 2, 3]),(pw290,4,[1, 2, 3]),(pw291,4,[0, 1, 4]),(pw292,4,[0, 1, 4]),(pw293,4,[0, 2, 4]),(pw294,4,[1, 2, 4]),(pw295,4,[0, 3, 4]),(pw296,4,[0, 1, 5]),(pw297,4,[0, 2, 5]),(pw298,4,[1, 2, 5]),(pw299,4,[1, 3, 5]),(pw300,4,[0, 4, 5]),(pw183,4,[3, 4, 5])]
theorem ptopY : ∀ s ∈ ptopZ, SliceN true ptopR ptopT s := by
  unfold ptopZ
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) ptopB p7_B p7_L (by decide +kernel),mkSlice (w:=0) ptopB p9_B p9_L (by decide +kernel),mkSlice (w:=32) ptopB p10_B p10_L (by decide +kernel),mkSlice (w:=8) ptopB p11_B p11_L (by decide +kernel),mkSlice (w:=0) ptopB p12_B p12_L (by decide +kernel),mkSlice (w:=2) ptopB p13_B p13_L (by decide +kernel),mkSlice (w:=0) ptopB p17_B p17_L (by decide +kernel),mkSlice (w:=0) ptopB p18_B p18_L (by decide +kernel),mkSlice (w:=0) ptopB p19_B p19_L (by decide +kernel),mkSlice (w:=32) ptopB p2_B p2_L (by decide +kernel),mkSlice (w:=8) ptopB p2_B p2_L (by decide +kernel),mkSlice (w:=8) ptopB p2_B p2_L (by decide +kernel),mkSlice (w:=0) ptopB p3_B p3_L (by decide +kernel),mkSlice (w:=2) ptopB p2_B p2_L (by decide +kernel),mkSlice (w:=16) ptopB p20_B p20_L (by decide +kernel),mkSlice (w:=1) ptopB p21_B p21_L (by decide +kernel),mkSlice (w:=16) ptopB p6_B p6_L (by decide +kernel),mkSlice (w:=32) ptopB p15_B p15_L (by decide +kernel),mkSlice (w:=0) ptopB p5_B p5_L (by decide +kernel),mkSlice (w:=32) ptopB p15_B p15_L (by decide +kernel),mkSlice (w:=0) ptopB p4_B p4_L (by decide +kernel),mkSlice (w:=2) ptopB p6_B p6_L (by decide +kernel),mkSlice (w:=32) ptopB p14_B p14_L (by decide +kernel),mkSlice (w:=0) ptopB p5_B p5_L (by decide +kernel),mkSlice (w:=32) ptopB p14_B p14_L (by decide +kernel),mkSlice (w:=0) ptopB p4_B p4_L (by decide +kernel),mkSlice (w:=0) ptopB p5_B p5_L (by decide +kernel),mkSlice (w:=0) ptopB p5_B p5_L (by decide +kernel),mkSlice (w:=1) ptopB p6_B p6_L (by decide +kernel),mkSlice (w:=16) ptopB p14_B p14_L (by decide +kernel),mkSlice (w:=0) ptopB p5_B p5_L (by decide +kernel),mkSlice (w:=8) ptopB p15_B p15_L (by decide +kernel),mkSlice (w:=2) ptopB p6_B p6_L (by decide +kernel),mkSlice (w:=8) ptopB p15_B p15_L (by decide +kernel),mkSlice (w:=8) ptopB p15_B p15_L (by decide +kernel),mkSlice (w:=0) ptopB p16_B p16_L (by decide +kernel),mkSlice (w:=1) ptopB p6_B p6_L (by decide +kernel),mkSlice (w:=2) ptopB p6_B p6_L (by decide +kernel),mkSlice (w:=0) ptopB p8_B p8_L (by decide +kernel),mkSlice (w:=32) ptopB p1_B p1_L (by decide +kernel),mkSlice (w:=32) ptopB p1_B p1_L (by decide +kernel),mkSlice (w:=32) ptopB p1_B p1_L (by decide +kernel),mkSlice (w:=16) ptopB p1_B p1_L (by decide +kernel),mkSlice (w:=32) ptopB p1_B p1_L (by decide +kernel),mkSlice (w:=8) ptopB p1_B p1_L (by decide +kernel),mkSlice (w:=32) ptopB p1_B p1_L (by decide +kernel),mkSlice (w:=8) ptopB p1_B p1_L (by decide +kernel),mkSlice (w:=8) ptopB p1_B p1_L (by decide +kernel),mkSlice (w:=2) ptopB p1_B p1_L (by decide +kernel),mkSlice (w:=8) ptopB p1_B p1_L (by decide +kernel),mkSlice (w:=8) ptopB p1_B p1_L (by decide +kernel),mkSlice (w:=8) ptopB p1_B p1_L (by decide +kernel),mkSlice (w:=1) ptopB p1_B p1_L (by decide +kernel),mkSlice (w:=2) ptopB p1_B p1_L (by decide +kernel),mkSlice (w:=2) ptopB p1_B p1_L (by decide +kernel),by simp⟩
def ptopC : List (Nat × List Nat) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(6,[]),(7,[]),(8,[]),(9,[]),(10,[]),(11,[]),(12,[]),(13,[]),(14,[]),(15,[]),(16,[]),(17,[]),(18,[]),(19,[]),(20,[]),(21,[]),(22,[]),(23,[]),(24,[]),(25,[]),(26,[]),(27,[]),(28,[]),(29,[]),(30,[]),(31,[]),(32,[]),(33,[]),(34,[]),(35,[]),(36,[]),(37,[]),(38,[]),(39,[]),(40,[]),(41,[]),(42,[]),(43,[]),(44,[]),(45,[]),(46,[]),(47,[]),(48,[]),(49,[]),(50,[]),(51,[]),(52,[]),(53,[]),(54,[]),(0,[263]),(0,[260]),(1,[256]),(0,[261]),(1,[257]),(0,[262]),(1,[258]),(1,[259]),(1,[128]),(0,[129]),(1,[129]),(0,[131]),(1,[130]),(1,[131]),(0,[391]),(0,[388]),(1,[260]),(0,[257]),(1,[261]),(0,[259]),(1,[263]),(1,[262]),(0,[392]),(0,[395]),(0,[387]),(0,[260,641]),(1,[256,645]),(0,[260,654]),(6,[263]),(0,[260,387]),(0,[392,645]),(2,[385]),(2,[129]),(3,[129]),(0,[261,652]),(1,[257,656]),(13,[389]),(0,[261,525]),(0,[261,526]),(0,[262,654]),(1,[258,658]),(0,[263,641]),(1,[259,645]),(0,[259,647]),(0,[392,647]),(0,[263,654]),(1,[259,129]),(0,[263,257]),(1,[259,261]),(0,[263,387]),(1,[128,649]),(1,[128,650]),(1,[128,658]),(1,[128,653]),(5,[261]),(3,[257]),(10,[257]),(2,[257]),(5,[517]),(0,[129,648]),(1,[129,648]),(1,[129,650]),(6,[256]),(0,[392,129]),(0,[129,394]),(0,[129,522]),(0,[129,652]),(13,[129]),(0,[129,655]),(0,[387,645]),(0,[391,641]),(0,[129,654]),(13,[385]),(0,[129,659]),(0,[129,525]),(0,[526,129]),(0,[131,650]),(0,[131,654]),(0,[392,131]),(0,[388,650]),(0,[388,641]),(0,[256,388]),(0,[257,388]),(2,[261]),(0,[259,388]),(0,[258,388]),(3,[261]),(0,[389,257]),(0,[257,390]),(0,[391,650]),(0,[257,391]),(0,[391,259]),(0,[391,387]),(0,[257,517]),(0,[257,518]),(1,[260,641]),(1,[260,642]),(1,[260,658]),(1,[260,653]),(0,[257,647]),(1,[261,643]),(0,[257,652]),(1,[261,656]),(0,[257,525]),(10,[261]),(0,[526,257]),(0,[259,652]),(1,[262,641]),(1,[520,641]),(0,[392,646]),(0,[392,641]),(0,[395,645]),(10,[129]),(0,[387,650]),(9,[129]),(1,[259,645,129]),(8,[129]),(0,[129,392,769]),(3,[257,261]),(1,[129,520,773]),(11,[257,519]),(10,[257,519]),(0,[129,522,782]),(0,[129,652,385]),(0,[129,513,780]),(9,[257]),(8,[130]),(0,[388,641,257]),(0,[256,645,388]),(10,[261,515]),(11,[261]),(12,[256]),(0,[257,647,525]),(5,[521,647]),(13,[389,515]),(12,[260,514]),(9,[261,257]),(8,[129,655])]
def ptopt : Tabs := (ptopC.map (mkCut true ptopZ),[(5,0),(5,1),(5,2),(5,3),(5,4),(5,8),(5,9),(5,12),(5,16),(5,20),(5,32),(5,33),(5,36),(5,52),(6,0),(6,1),(6,2),(6,3),(6,4),(6,10),(6,12),(6,16),(6,18),(6,20),(6,32),(6,34),(6,36),(7,1),(7,2),(7,3),(7,4),(7,10),(11,1),(11,2),(11,3),(11,4),(11,8),(11,9),(11,10),(11,18),(13,1),(13,4),(13,8),(13,9),(13,10),(13,12),(13,20),(14,2),(14,3),(14,4),(14,8),(14,10),(14,12),(14,18),(14,20),(14,24),(15,10),(15,12),(15,24),(17,0),(17,1),(17,3),(17,4),(17,9),(17,16),(17,18),(17,20),(17,24),(17,33),(17,48),(17,52),(19,3),(19,10),(19,16),(19,18),(21,0),(21,1),(21,4),(21,12),(21,16),(21,20),(22,2),(22,4),(22,16),(22,18),(22,20),(22,52),(23,10),(25,1),(25,8),(25,9),(25,10),(25,16),(25,20),(25,24),(25,56),(26,2),(26,10),(26,16),(26,18),(26,24),(26,56),(28,4),(28,12),(28,16),(28,20),(28,24),(28,52),(28,56),(35,0),(35,1),(35,2),(35,3),(35,33),(35,34),(37,1),(37,4),(37,20),(37,32),(37,33),(37,36),(38,2),(38,4),(38,34),(38,36),(41,1),(41,8),(41,9),(41,12),(41,32),(41,33),(41,40),(41,56),(42,2),(42,10),(42,32),(42,34),(42,40),(44,4),(44,12),(44,32),(44,36),(44,40),(49,33),(49,48),(49,56),(50,18),(50,34),(50,48),(50,52),(57,56),(60,52),(60,56)],[],[[]])
theorem ptopW : TabsP true ptopR ptopT ptopt := ⟨cutsGood ptopY (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def ptopD11 : List StD := [
([pw0,pw1,pw2,pw3,pw4,pw5],[3,73,17,149,153,65,5,397,137,0,241,389,4,537,449,457,421,509,453,173,413,557,477,521,573],[31,117,405,3588,61445,107,65675,3586,405507,589985,1050144,6303777,3968,8417409,16778752])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def ptopD10 : List StD := [
([pw19,pw0,pw1,pw2,pw3,pw4,pw5],[20,24,220,3,117,16,12,137,224,285,8,449,4,261,17,257,181,481,32,401,73,497,52,421,173,413,557,477,228,521,573],[1,6,58,202,774,7170,24579,49170,82050,770,149506,1835025,1835137,787201,2885633,29360280,33555216,473958424,41943936,872417416,1073742592]),
([pw0,pw1,pw17,pw2,pw3,pw4,pw5],[20,24,261,149,220,153,52,5,65,297,3,137,232,241,449,457,236,453,425,421,12,413,557,8,477,521,573],[15,17,482,3618,12834,115746,3,201,131081,12297,131081,262209,1573889,2101265,12648449,262336,266432,20971712,2635776,37833728,67121152]),
([pw262,pw0,pw1,pw2,pw3,pw4,pw5],[20,24,17,149,52,5,12,521,3,240,241,8,509,4,121,153,297,457,73,209,497,173,89,477,361,244,449,573],[7,9,49,449,1537,14337,16387,50,98434,1538,167938,49,786561,1537,1314817,2097200,4194864,8388656,16778880,100667776,134219264]),
([pw34,pw0,pw1,pw2,pw3,pw4,pw5],[20,24,32,16,5,3,65,52,137,397,12,0,220,389,241,4,537,8,449,248,17,149,121,181,481,453,421,173,413,557,477,521,573],[1,2,252,1828,30724,1015844,7340039,1048818,9437986,28674,17629218,2097269,35651845,28677,36241413,201327024,268447888,1611202736,29440,2148335904,4294979584]),
([pw20,pw0,pw1,pw2,pw3,pw4,pw5],[16,24,17,20,3,52,5,12,48,0,8,4,145,69,153,257,457,65,57,73,149,241,453,205,89,493,361,252,449,509,521,573],[7,57,65,145,785,3089,4130,8195,49154,33026,81922,393249,1572896,2097440,4718624,8519681,16908545,33685505,69206272,2013265936,2149581056]),
([pw0,pw1,pw2,pw36,pw3,pw4,pw5],[24,17,52,149,73,3,69,5,137,181,256,241,309,449,481,260,117,401,421,509,453,173,413,557,477,397,12,389,537,8,521,573],[63,199,4,803,7171,57379,65692,131116,262204,134156,1613868,1,2359716,4197508,25206948,100663584,134220800,805347360,4459776,1074307360,2147486720]),
([pw263,pw0,pw1,pw2,pw3,pw4,pw5],[16,24,20,149,3,256,12,137,264,241,8,449,4,52,17,1,181,481,425,65,73,421,93,268,509,453,413,557,493,521,573],[1,30,34,210,802,7170,24586,49155,82050,770,149506,1843209,3154072,4203272,58730520,2883729,67371777,411306001,69206912,562038928,1073742592]),
([pw33,pw0,pw1,pw2,pw3,pw4,pw5],[16,256,20,73,52,65,12,421,3,48,413,8,557,4,149,5,24,1,257,137,153,241,449,457,272,453,173,477,521,573],[3,29,33,449,1539,14337,16408,229377,1900928,2360832,29692160,25,16536,1560,33558552,67141761,1537,134254593,2098816,289411456,536872448]),
([pw224,pw0,pw1,pw2,pw3,pw4,pw5],[12,24,20,149,3,173,16,276,280,361,8,509,4,297,17,29,457,65,73,28,421,397,285,40,449,453,413,557,477,545,573],[1,30,114,130,898,7170,24586,24610,40963,770,75778,393272,3932169,4195080,58722328,3801121,67109664,411043888,1573633,555223041,1073742592]),
([pw0,pw1,pw2,pw3,pw14,pw4,pw5],[24,181,3,149,153,5,12,29,137,276,44,241,357,40,449,505,65,73,521,20,285,509,16,413,557,589,585],[31,55,451,576,7171,57347,196652,393544,655436,1051656,2121736,356,4259940,8391712,16801824,1,3392,24896,33556032,67117120,33565696]),
([pw235,pw0,pw1,pw2,pw3,pw4,pw5],[12,24,17,20,453,3,5,16,137,44,241,8,449,4,153,181,133,525,65,73,421,397,285,40,509,413,557,273],[7,57,225,257,1537,14337,49170,49218,65539,1538,151554,786544,3145745,4195856,25694224,3145793,33556032,75501632,1537,9441281,142607872]),
([pw32,pw0,pw1,pw2,pw3,pw4,pw5],[12,28,3,73,209,20,16,5,205,24,0,276,389,241,4,537,8,449,40,17,149,297,137,133,457,521,509,453,413,557,477,573],[1,62,454,514,15362,507910,3670540,2622340,13107715,14848,17203716,1048972,37748763,14344,201621516,4194695,268441728,1610907780,14339,37912579,2147489792]),
([pw0,pw1,pw2,pw3,pw4,pw5,pw438],[24,481,3,149,457,5,40,137,397,36,241,389,49,449,65,73,421,509,20,413,4,16,273],[31,55,455,3587,12355,64,49196,98508,3592,139848,295436,65764,525856,1057376,2114084,1984,139968,964,4204096,3584,1]),
([pw452,pw0,pw1,pw2,pw3,pw4,pw5],[4,8,20,149,3,5,16,12,137,36,241,449,24,457,481,525,65,73,421,40,285,413],[1,30,114,402,1538,2051,28680,28704,45312,5632,3,196664,917784,1050120,3,786736,2098720,3,788224,3,3]),
([pw0,pw21,pw1,pw2,pw3,pw4,pw5],[16,3,24,32,401,20,149,5,425,397,17,137,153,48,241,389,284,537,449,457,52,73,12,0,8,4,13,453,477,521,573],[7,120,385,7682,58368,984066,3145729,33,4194307,8396803,50397187,67109033,135266872,120,135397432,385,385,268435585,59904,537330178,1073766400]),
([pw0,pw1,pw2,pw10,pw3,pw4,pw5],[20,73,3,17,16,65,52,117,24,257,397,137,153,48,389,288,241,292,537,449,457,13,209,497,5,205,89,493,521,12,509,8,573],[15,248,773,7180,123400,1966092,2097171,17,4194307,98307,8388611,16777281,33554544,67141744,134217840,805306373,106497,3221356545,125952,269353988,4295024640]),
([pw78,pw0,pw1,pw2,pw3,pw4,pw5],[32,24,17,52,3,149,65,421,12,0,296,241,4,8,509,73,5,425,137,153,389,300,537,457,57,209,497,477,449,521,573],[31,41,72,409,3593,28681,32797,196620,786580,1051652,14696468,16875529,33587337,3081,67158025,196744,132104,134283272,1051776,807420048,1073744896]),
([pw195,pw0,pw1,pw2,pw3,pw4,pw5],[16,3,17,24,20,73,5,12,421,48,413,8,557,4,401,149,117,65,137,153,241,304,449,457,57,453,205,493,521,573],[15,49,65,387,1537,14337,49172,196613,786694,1050116,14684166,16777233,33571088,1552,33574928,67174657,1537,134287361,1050368,274731266,536872448]),
([pw0,pw83,pw1,pw2,pw3,pw4,pw5],[28,24,17,3,153,32,73,20,453,52,65,5,421,12,521,44,389,308,241,40,537,449,457,205,8,81,413,557,477,573],[31,500,3612,28693,491524,7864332,8224,8390153,129,491521,20447241,480,33566945,458976,480,30209,67339776,404227592,28673,28673,537100288]),
([pw0,pw1,pw2,pw3,pw11,pw4,pw5],[20,209,149,52,5,65,12,397,137,24,17,3,44,241,389,40,449,537,81,73,509,89,45,421,4,273],[7,56,448,3585,29696,230400,7,262211,524289,12291,1081347,88,25,2101272,4227096,8388673,448,98496,12289,16812033,33599488]),
([pw264,pw0,pw1,pw2,pw3,pw4,pw5],[12,3,297,24,308,65,16,137,44,285,8,449,4,32,209,20,149,52,5,17,421,521,389,40,537,129,241,509,413,557,273],[15,17,99,129,785,7169,122884,917542,3145733,4195076,25167876,122912,34643969,67117824,142665728,1179681,268436256,545392672,769,3147777,1082131200]),
([pw31,pw0,pw1,pw2,pw3,pw4,pw5],[20,3,181,24,149,52,173,308,312,361,8,509,4,73,453,65,28,397,12,137,389,40,537,457,129,89,477,545,573],[15,17,97,129,897,7169,24581,32868,983044,1049348,14682118,97,17047553,769,26625,32864,33554784,67108960,197376,134678528,268436224]),
([pw0,pw1,pw2,pw3,pw4,pw5,pw409],[20,497,453,52,5,65,3,397,17,40,137,36,241,389,537,449,24,421,105,89,573,509],[7,56,1984,14592,51968,65857,7,131587,6147,262659,513,131608,526360,2072,25,7808,51840,131649,1071616,6145,2099201]),
([pw275,pw0,pw1,pw2,pw3,pw4,pw5],[8,3,153,24,4,65,16,12,137,36,285,449,32,497,20,453,52,5,17,397,40,389,421,241,413],[15,17,99,387,1537,2049,61444,458790,1835270,2098692,21,61472,5271808,8394240,17,5308706,16778784,17,1574656,17,17]),
([pw0,pw1,pw86,pw2,pw3,pw4,pw5],[52,73,149,3,181,24,5,65,28,397,12,137,44,389,48,241,40,537,449,457,209,453,316,413,8,557,25,477,521,573],[7,57,209,3856,61456,983064,1048579,7,7,49155,2097155,1025,4194305,12603393,50397185,67109953,8405057,167772225,3840,268830464,536899584]),
([pw0,pw1,pw2,pw3,pw12,pw4,pw5],[3,73,17,52,149,205,173,12,421,24,257,44,241,389,40,449,537,453,509,25,316,413,557,273],[31,109,389,1669,15364,114692,122,410,131211,14346,442378,524712,1048704,2103336,4243496,8,6528,49536,6272,49280,8411136]),
([pw265,pw0,pw1,pw2,pw3,pw4,pw5],[12,3,17,24,20,73,52,5,421,44,0,8,4,149,173,205,397,137,241,389,40,449,537,441,161,413,433,273],[15,113,193,257,1539,6147,8292,49220,196613,786948,7340036,8288,97,262752,9437280,16777281,33555008,68173888,197121,3211265,135528960]),
([pw30,pw0,pw1,pw2,pw3,pw4,pw5],[28,24,17,3,153,73,52,149,12,0,316,361,241,4,509,8,449,40,65,5,421,389,537,457,453,161,413,557,477,565,573],[31,233,256,65,7681,253961,252,786524,1048861,2100228,12730380,786656,1049057,2100320,16990312,34865473,67112000,403062856,7425,538001665,1073744896]),
([pw0,pw1,pw2,pw3,pw4,pw5,pw330],[3,73,17,52,149,493,477,397,40,137,36,241,389,557,4,24,153,421,413,573],[31,109,901,7172,25860,99333,122,131355,7178,9482,1051,131497,265256,24872,256,3968,25984,1409,535808,265216,8]),
([pw410,pw0,pw1,pw2,pw3,pw4,pw5],[8,3,17,24,20,73,52,5,12,421,36,413,557,149,477,493,40,137,241,537,449,461],[15,113,193,771,3073,4097,8292,49220,197126,265220,1572869,8288,8800,3168,97,82496,3136,2097217,265728,1573377,3073]),
([pw0,pw1,pw2,pw3,pw4,pw5,pw335],[3,73,17,149,153,65,5,12,545,521,36,241,389,537,509,24,20,565,413,557,16,429,137,573,449],[31,117,916,7172,25604,32917,107,906,7170,25602,65675,131488,265248,533536,1048737,3456,2098560,4194432,8399872,3200,16778368]),
([pw268,pw0,pw1,pw2,pw3,pw4,pw5],[8,40,137,509,3,73,17,149,153,65,5,545,521,36,241,389,565,413,449,501],[3,3,3,7,3,9,496,1872,6210,57408,3,1712,6178,57376,3,68098,156160,3,26626,786435,3])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def ptopD9 : List StD := [
([pw0,pw1,pw2,pw244,pw3,pw4,pw5],[24,52,17,181,257,481,13,73,117,401,497,3,421,320,413,557,140,28,397,12,241,4,8,324,449,521,573],[7,7,3,13,21,37,450,642,642,642,1154,1,6402,24834,35074,989184,1138688,14780416,1077248,58759168,67133440]),
([pw247,pw0,pw1,pw2,pw3,pw4,pw5],[24,181,17,28,12,32,209,3,173,16,328,361,8,4,297,457,401,128,137,453,413,120,68,557,449,180,273],[7,120,904,1,3080,12296,16387,16643,7,3075,32771,196960,262248,199776,655456,262536,1051904,65011968,3080,8650888,71306240]),
([pw19,pw0,pw1,pw2,pw3,pw12,pw4,pw5],[52,132,149,3,421,12,24,200,285,180,449,40,173,205,136,17,257,481,593,5,413,569,565,80,88,573],[1,7,11,58,106,386,3586,3,12289,49170,81986,16768,181248,8195,19,278531,3,3,19,524291,1048705,2101249,1,402,4195346,386,25166850,33554816]),
([pw30,pw19,pw0,pw1,pw2,pw3,pw4,pw5],[128,24,332,124,3,28,377,17,73,32,401,20,52,132,104,241,336,361,80,449,509,88,184,149,117,12,285,68,40,481,497,421,89,477,565,573],[63,199,3841,12288,4097,245761,8126481,1,8392708,16781324,33554477,67174404,403177476,4165,196,197,196,537395268,5377,5377,5377,1074794753,2147495937,4295036928,8610910208,237569,19328933889,34359836672]),
([pw19,pw0,pw1,pw2,pw3,pw4,pw5,pw330],[52,88,149,3,40,68,137,164,285,8,24,477,493,92,17,96,181,257,73,401,569,413,557,228,132],[1,7,11,114,386,530,1546,3,6145,122944,41344,49154,164866,4099,3,3,294915,557059,1050625,2097281,4194307,8195,2097600,12582978,16777290,386,386,1]),
([pw19,pw0,pw1,pw2,pw3,pw4,pw5,pw335],[88,96,153,149,3,117,76,12,28,164,285,509,8,4,24,261,17,257,181,73,401,132,521,565,413,557,52,429,137,449],[7,9,113,401,1537,14337,16529,32771,196642,327682,1538,67587,81923,1572897,1572865,1537,526339,524291,14680096,16778784,33556513,67108913,2098688,136316929,270532609,1537,1537,536870913]),
([pw268,pw19,pw0,pw1,pw2,pw3,pw4,pw5],[80,8,88,40,96,181,209,184,509,153,149,3,117,76,28,164,285,261,257,401,73,521,565,413,449,501],[15,52,85,132,1,132,260,532,1029,14341,16525,98309,15,131093,266288,262320,98352,53,528453,1048773,98373,85,6295680,8491008,133,98432,50331781,133]),
([pw0,pw1,pw17,pw2,pw3,pw14,pw4,pw5],[24,60,181,297,132,149,128,144,13,5,521,453,137,32,3,20,112,245,241,425,28,12,340,413,40,344,557,65,477,589,84,585,348],[3,7,3,3,11,3,3,1,1008,7216,57410,458864,2160,524418,3162130,4235266,8454146,117440514,525008,134217858,590464,335544960,1,8717392,5200,536936450,7516192770,537198592]),
([pw32,pw0,pw1,pw17,pw2,pw3,pw4,pw5],[24,60,153,20,32,3,12,144,205,112,389,348,537,84,17,5,128,453,137,129,241,149,425,28,413,40,68,557,477,521,573],[7,58,90,386,1,1538,14338,3,16387,3,3,3,3,1,33152,983040,1115648,2297856,4194434,8454210,16777730,234881026,33152,4195200,402653568,67072,537202688,1073743360]),
([pw0,pw1,pw17,pw2,pw3,pw4,pw5,pw438],[24,60,481,153,88,149,84,144,13,5,453,112,245,241,509,449,32,3,20,425,68,421,40,413,8,45,128,352,273],[3,7,3,3,3,3,11,1,1008,1136,14448,50224,458818,524418,7340034,8390658,20971538,4521986,524928,526976,33555152,524418,10496000,49232,203423746,268445776,8390658,1]),
([pw0,pw1,pw43,pw2,pw3,pw4,pw5],[20,73,149,28,340,12,52,5,65,3,29,421,100,389,356,241,360,537,68,449,441,173,8,89,45,565,273],[7,56,448,3592,61440,983040,7,7,7,49155,1310723,2097224,1,24600,4390920,2120,8405184,17039552,26632,33687560,67399680]),
([pw0,pw1,pw17,pw2,pw3,pw4,pw5,pw335],[88,96,261,153,149,364,5,65,297,132,521,128,172,241,537,509,24,60,453,368,348,3,425,28,565,413,557,429,84],[31,1,234,3850,12554,49163,196875,2,241,263217,532529,32819,3145779,4194400,25166368,34082848,68157473,3145761,4194912,4718688,1048673,1048673,34090496,135286273,269484544,1601537,1585153,2049]),
([pw268,pw0,pw1,pw17,pw2,pw3,pw4,pw5],[88,24,96,153,60,297,32,453,149,20,128,8,40,212,173,137,372,361,236,509,261,65,521,449,585,425,565,413,45],[63,965,7697,25601,33792,197633,787457,1048717,1,2121740,4195372,196652,25427981,4,25729,1409,197761,1413,33563648,71308288,134284288,7169,25600,33644544,268460033,197632,4457473,16973825]),
([pw0,pw1,pw495,pw2,pw3,pw4,pw5],[20,73,453,24,153,17,257,457,209,341,28,52,205,376,389,8,4,89,477,521,380,501,573],[7,56,56,56,88,152,259,7,259,515,7,7168,1,25600,99328,7168,145408,268288,25600,3671040,4218880]),
([pw262,pw0,pw1,pw2,pw3,pw4,pw5,pw335],[88,84,96,236,364,5,12,28,521,172,241,509,3,121,153,297,457,65,73,209,173,89,361,128,429],[1,14,54,454,1542,2079,4183,8215,52,49412,1540,83975,49157,131123,786707,1555,2069,262167,1048624,2097712,55,53,4196096,25167879,2,1543,1541,8388613]),
([pw268,pw262,pw0,pw1,pw2,pw3,pw4,pw5],[84,8,96,40,297,153,209,32,188,509,17,128,149,212,5,521,172,241,121,449,445,73,89,501],[15,52,197,260,1,260,516,1028,6149,24581,33037,196613,15,264213,24596,52,52,1572885,26689,2132289,198721,325,2304,4284416,261,2304,8390917,261]),
([pw34,pw0,pw1,pw2,pw334,pw3,pw4,pw5],[32,52,73,148,17,181,257,481,205,65,337,493,144,104,241,132,397,200,137,80,449,521,88,585],[3,5,3,3,9,9,9,3,26,2,56,88,152,11,3,3,3,3,1,770,1282,2306,4104,4104,4104,516096,7962624,14180352]),
([pw0,pw1,pw2,pw334,pw3,pw4,pw5],[32,73,52,149,3,17,65,148,144,181,257,481,341,453,205,337,493,28,137,12,397,0,384,389,241,4,8,388,449,509,521,573],[15,116,4,928,1440,2464,15,15,15,4103,8199,1,16452,32836,65604,1966464,31457664,100663680,30670848,2013528080,2160066560]),
([pw183,pw0,pw1,pw2,pw3,pw4,pw5],[32,52,401,65,12,28,397,392,389,8,4,5,425,216,17,60,181,37,481,13,57,477,241,80,449,88,509,273],[3,5,11,113,385,1537,3,6146,122944,164224,319488,1572867,3,3,3,6146,4226,2099202,4194752,125829184,167772544]),
([pw186,pw0,pw1,pw2,pw3,pw4,pw5],[28,340,32,209,3,205,16,397,396,389,8,4,149,73,120,60,17,144,1,29,421,37,80,537,457,68,413,557,521,273],[3,13,113,129,771,3073,12292,507936,1605633,2130688,63012864,12324,4101,772,41947140,1179681,67109664,180371488,769,277872641,570426112]),
([pw34,pw0,pw1,pw2,pw3,pw496,pw4,pw5],[32,148,153,209,28,149,121,17,257,181,481,453,132,397,216,5,337,477,545,104,241,200,80,449,88,273],[7,9,3,3,19,3,3,99,386,642,642,386,1154,3,3,2083,3,3,61440,49154,114688,180224,1,274432,274432,3670018,29360130,54001664]),
([pw34,pw0,pw371,pw1,pw2,pw3,pw4,pw5],[32,128,132,12,73,148,17,149,121,257,481,453,397,216,5,337,477,545,80,449,88,585],[3,13,17,33,37,33,33,102,417,608,102,608,1120,2181,38,1,38,38,33,37,33,33,28678,57344,90112,135174,135174,3932160]),
([pw0,pw371,pw1,pw2,pw3,pw4,pw5],[28,20,12,32,73,128,149,120,65,216,5,17,3,181,400,241,237,68,449,445,184,173,16,361,8,4,93,441,413,557,545,397,273],[7,120,3968,12801,117248,1968640,75,6295553,9,8404993,50331649,120,585,67158072,134611000,2101761,268484992,538313088,8404993,3758096385,4295147520]),
([pw34,pw0,pw1,pw2,pw3,pw4,pw5,pw497],[32,148,457,497,4,149,121,17,257,181,481,453,144,5,132,421,137,184,164,413,241,573],[7,9,3,3,3,3,19,99,386,642,386,1154,1154,3,3,3,3,2083,258048,1847296,405504,143362,245760,442368,180226,2490368,131074,1]),
([pw34,pw0,pw1,pw2,pw36,pw3,pw4,pw5],[24,52,60,3,216,5,13,109,32,453,149,112,241,173,413,477,404,449,509,521,573],[3,1,14,2,20,20,20,3,3,3,5,5,5,226,262,1538,6658,1538,1,8226,18466,32802,20,20,20,22528,983048,1054720]),
([pw34,pw0,pw1,pw2,pw3,pw14,pw4,pw5],[24,60,153,144,65,12,28,3,20,112,389,184,537,17,453,137,129,32,149,89,45,241,449,589,585],[7,1,26,226,354,1538,6146,3,3,3,8195,3,3,2072,116736,133378,3584,284672,2072,26,524824,1050648,1,2100736,4233216,8389122,16779266,8392192]),
([pw34,pw32,pw0,pw1,pw2,pw3,pw4,pw5],[60,28,12,297,24,144,65,112,389,68,537,40,181,20,32,205,88,80,5,128,521,453,137,149,241,132,89,477,573],[7,9,17,97,7,385,3585,4097,24577,32801,17,385,197633,17,17,17,17,17,262240,16252928,16777600,44565504,32864,67109088,134217824,17301888,39322624,268435840]),
([pw34,pw0,pw1,pw2,pw3,pw4,pw5,pw438],[24,60,457,144,65,40,68,397,112,389,8,17,5,80,453,88,149,32,20,173,89,241,449,509,3,132],[7,1,26,226,770,1122,1058,3,3,3,3,3,2051,4120,123008,41728,122880,434178,524312,1048856,32792,26,2098048,12624000,50331778,33536,770,1]),
([pw34,pw0,pw2,pw10,pw3,pw4,pw5],[20,32,16,52,65,13,3,401,73,148,209,341,497,24,149,17,144,181,257,481,205,337,493,453,408,241,361,412,449,509,521,573],[1,62,193,1794,2818,4866,56,24577,229888,360960,623104,3,1048600,2097176,4194328,8404993,50348033,8404993,117440512,2013265984,2197815296]),
([pw78,pw34,pw0,pw2,pw3,pw4,pw5],[32,73,16,149,24,20,453,52,209,341,497,5,425,216,17,132,137,165,144,257,481,477,104,241,397,200,80,449,521,88,585],[7,25,33,73,137,73,33,7,259,515,1027,6272,516096,811008,1335296,6272,6272,2099328,63012864,1006731264,1824522240]),
([pw34,pw0,pw1,pw2,pw3,pw12,pw4,pw5],[52,132,73,205,421,12,3,32,200,389,180,537,40,173,144,17,24,257,136,481,5,413,569,241,565,80,449,88,573],[1,7,11,114,226,770,7170,3,8201,49170,212994,148224,837632,11,19,131,3,3,19,1048579,2097417,4194313,1,8388882,16777234,8388866,234881026,268436224]),
([pw30,pw34,pw0,pw1,pw2,pw3,pw4,pw5],[128,32,216,124,3,28,132,17,144,377,453,149,104,241,416,361,80,449,509,88,184,332,5,65,52,12,389,40,68,537,481,421,89,477,565,573],[127,901,3079,64,5,61441,2031633,1,2097156,29360204,33554797,67133508,939655236,18875845,6292100,965,900,1610744196,29361477,16780293,16802881,3137,2168455237,4311769092,8612085764,57409,19327746113,34359762944]),
([pw34,pw0,pw1,pw2,pw3,pw4,pw5,pw330],[52,88,73,493,40,68,397,164,389,8,32,3,477,96,17,144,181,37,557,24,257,569,413,5,241,248,132],[1,7,11,114,386,530,3586,3,4105,122944,164224,311298,1605634,11,3,3,262147,1027,2097161,4194441,262147,8388611,16777664,33816642,67110978,386,386,1]),
([pw34,pw0,pw1,pw2,pw3,pw4,pw5,pw335],[88,236,73,3,65,76,12,28,545,164,389,537,509,32,149,96,121,257,5,17,364,132,521,241,24,60,20,565,413,557,429,137,449],[3,5,57,449,1537,6147,8265,114689,1998872,6455552,8521216,6145,50462721,16409,2113793,1537,6145,67133441,137363728,268437008,536872977,1048601,10487552,1075841025,2149580801,1537,8389121,4294967297]),
([pw268,pw34,pw0,pw1,pw2,pw3,pw4,pw5],[80,8,88,40,60,181,24,453,149,184,509,128,73,3,65,76,545,164,389,96,121,257,5,212,521,241,565,413,449,501],[15,116,389,516,1,516,1028,2052,4101,57349,66061,393221,15,1572997,15228960,18940448,36044832,549,24709,389,393349,389,67191296,134627328,517,33751552,805306885,517]),
([pw0,pw251,pw2,pw3,pw4,pw5],[20,73,149,16,13,65,24,153,257,457,341,453,205,337,493,48,361,241,420,449,3,509,521,573],[7,56,448,448,704,7,7,1027,2051,4120,8216,16408,229376,8126464,8486912]),
([pw379,pw0,pw2,pw3,pw4,pw5],[24,153,17,16,65,5,32,73,52,149,341,453,257,457,173,337,477,48,361,241,424,449,3,509,521,573],[7,56,960,1472,2496,7,7,4099,8195,16408,32792,65560,917504,32505856,33947648]),
([pw0,pw1,pw2,pw498,pw4,pw5],[24,153,29,257,457,16,65,25,12,421,137,44,285,241,40,449,509,89,101,273],[7,7,11,11,19,224,1792,14336,114688,224,133216,278624,1792,49920,546816]),
([pw380,pw0,pw1,pw2,pw3,pw4,pw5],[24,153,17,28,20,32,149,12,16,48,361,8,4,457,65,5,52,453,205,89,477,3,509,428,573],[7,120,392,1,1544,6152,7,7,7,1539,8195,49472,65608,67136,196672,262408,541440,1065216,1544,14680072,16778752]),
([pw380,pw0,pw1,pw2,pw4,pw5],[24,153,17,28,421,52,149,205,137,48,361,3,509,521,428,457,5,453,89,477,573],[7,120,184,1816,30744,7,7,1539,36867,65760,1632,135264,262816,524448,1050112]),
([pw0,pw1,pw2,pw3,pw382,pw5],[24,153,37,457,16,65,425,52,73,149,341,453,493,48,361,241,432,449,3,509,521,573],[7,7,7,7,11,112,896,1408,2432,112,112,4144,57344,2031616,2121728]),
([pw0,pw1,pw2,pw3,pw4,pw499],[24,153,49,257,16,65,45,52,73,149,341,453,205,337,36,361,241,449,509,273],[7,7,7,11,7,112,896,1408,2432,4144,8240,112,114688,409600,704512]),
([pw20,pw0,pw1,pw2,pw3,pw4,pw5,pw335],[76,96,17,364,3,5,12,28,160,36,4,145,69,153,257,65,57,73,149,241,205,89,361,120,429,509,72],[7,25,33,209,785,1545,89,2058,4099,24578,16642,8195,16387,98313,393224,524552,131081,131081,1081345,2130177,32779,32779,4718848,58720257,67108865,524545,524545,8388609]),
([pw268,pw20,pw0,pw1,pw2,pw3,pw4,pw5],[72,8,76,40,96,153,52,176,205,509,17,128,3,88,5,28,160,36,257,69,425,521,545,285,241,65,449,501],[15,52,196,341,1,132,516,1044,14341,16389,32909,200709,15,262192,524309,262320,327728,53,1048837,6291584,25231360,133,33554821,1114373,277,8454272,201326725,133]),
([pw0,pw1,pw2,pw36,pw3,pw14,pw4,pw5],[24,60,153,17,124,5,144,117,132,401,436,440,521,137,3,73,52,112,285,241,176,509,216,453,444,413,45,28,389,537,589,585],[3,3,7,3,11,3,3,240,1794,14864,114690,950784,32506368,1,2160,81986,33685616,83886192,18450,134285314,268566530,554696706,1,399376,14352,1073872898,2164260866,1090912256]),
([pw32,pw0,pw1,pw2,pw36,pw3,pw4,pw5],[24,60,181,52,3,209,144,12,28,112,389,448,537,260,257,117,5,401,128,120,521,136,137,241,188,509,180,25,413,477,273],[7,58,90,394,1,1538,14338,3,3,16387,3,3,3,98400,393234,7864352,8521248,117444640,1,136347712,268436032,536903744,386,1538,83890178,8914432,7868416,1140852224]),
([pw0,pw1,pw2,pw36,pw3,pw4,pw5,pw438],[24,60,457,17,76,5,144,117,88,401,452,180,421,188,137,112,285,241,509,449,3,52,413,477,397,389,4,8,440,273],[3,3,7,3,3,3,11,240,1794,31232,229888,795152,3146242,1,12400,4227184,8388720,3145794,16787458,33587202,201334802,203423746,30720,792592,269488130,536977424,4227074,1]),
([pw0,pw82,pw1,pw2,pw36,pw3,pw4,pw5],[52,401,60,17,140,181,321,481,117,5,440,137,3,456,285,448,449,260,32,593,425,173,413,477,132,88,80,460,509,521,573],[1,15,25,1,60,92,156,5,785,1,7184,24592,229392,771,262149,524291,8195,524291,1048593,2097409,4202753,8388865,16783380,24596,100728852,4220928,939595776,1073766400]),
([pw0,pw82,pw1,pw2,pw3,pw4,pw5],[32,16,20,52,5,425,140,17,132,137,165,3,456,241,237,88,449,465,80,73,117,12,28,285,8,4,45,253,429,273],[7,9,56,4032,28864,491712,524289,1048587,6291969,8392705,50397185,1048585,9,9,9,56,56,67141656,134230784,268796672,536915968]),
([pw183,pw0,pw1,pw2,pw36,pw3,pw4,pw5],[52,60,401,3,216,17,5,13,109,32,73,149,341,453,425,173,112,413,477,241,464,449,509,521,573],[1,7,11,1,18,18,18,35,35,1,18,18,18,449,515,3073,5121,9217,16387,32833,196673,262209,18,18,18,720896,15728648,16973824]),
([pw0,pw83,pw1,pw2,pw36,pw3,pw4,pw5],[120,24,3,60,216,17,73,453,52,468,440,521,165,472,241,309,180,449,465,444,5,28,389,537,448,593,25,413,477,12,421,273],[63,496,817,1,7217,57392,983088,1280,1048853,2097181,17,4218881,25886721,465,33554768,3409,24912,464,784,68158737,134226177,270008577,538971153,4218896,9109520,4221953,1082264577,2147573760]),
([pw264,pw0,pw1,pw2,pw36,pw3,pw4,pw5],[124,24,136,212,60,3,17,440,52,73,117,140,476,285,444,449,149,421,521,309,465,5,401,509,413,45,216,389,537,273],[127,904,1413,2233,385,12425,49289,65868,325,1,393421,536644,1097796,2163977,4260104,131465,4198664,8405256,4,1413,16782593,33572097,67240105,201338880,335593472,12425,49289,536899584]),
([pw275,pw0,pw1,pw2,pw36,pw3,pw4,pw5],[76,24,96,192,60,3,17,260,16,117,52,5,140,8,448,440,137,480,285,453,444,165,180,309,549,241,25,413,397,389],[127,136,3845,12345,114729,409609,1153,525388,1605,1,7405636,8781892,16589,3593,17302536,18351112,33686536,1161,4,68158977,134350337,17541,273743872,537264128,24713,135725056,16521,16521]),
([pw0,pw1,pw2,pw36,pw3,pw12,pw4,pw5],[52,73,149,136,17,421,144,181,24,120,3,321,481,401,453,440,5,48,413,444,557,140,28,389,537,449,241,273],[7,25,1,248,1880,2136,4184,7,8195,7,16899,8195,16387,9,32801,98305,393217,1572865,2131560,4227912,10879040,20447296,1,164392,34112040,67273224,34112008,135135232]),
([pw30,pw0,pw1,pw2,pw36,pw3,pw4,pw5],[120,24,124,60,3,17,52,73,149,440,28,48,361,241,260,448,509,449,332,144,29,165,309,481,401,453,421,413,477,5,140,12,389,40,68,537,565,573],[63,453,577,1551,65,14341,245765,480,262241,1,3932197,4462624,9240608,449,16777408,453,6336,33620160,262208,67109441,134219841,805306433,3288859653,5368715264,61203873792,14341,68786782213,137438959616]),
([pw0,pw1,pw2,pw36,pw3,pw4,pw5,pw330],[52,73,149,96,17,144,181,321,557,481,24,72,3,401,444,421,477,48,413,140,68,397,389,4,8,241,260,448],[7,25,1,120,184,824,7224,7,8195,7,8195,267,7,9,114689,458753,16641,16385,3719200,5111840,25692456,16796712,33734656,201361672,136370184,134613256,4589576,1]),
([pw0,pw1,pw2,pw84,pw36,pw3,pw4,pw5],[140,212,149,17,69,5,181,321,481,117,52,216,73,341,453,173,65,484,413,477,12,60,448,509,260,440,3,28,68,444,241,397,545,573],[15,57,73,3,75,137,265,545,3077,2055,6150,10246,18438,33825,65537,32801,393249,524321,1048577,2097153,393217,29360129,234881027,393217,813694977,1074135042,6484393986,8590327808]),
([pw0,pw1,pw2,pw84,pw3,pw4,pw5],[140,17,128,149,73,216,65,257,5,12,16,181,28,3,484,241,68,449,445,444,20,32,93,509,24,77,173,413,557,137,8,545,397,273],[63,451,3587,14343,49283,983043,317,3149853,12348,4243468,9109516,16781893,100675653,134266945,269156417,536875012,134238209,1082658817,134238212,6450843652,8590049280]),
([pw0,pw1,pw2,pw36,pw3,pw394,pw4,pw5],[60,17,488,73,69,181,3,321,481,5,149,117,132,401,440,421,593,112,241,176,509,444,136,144,413,45,28,389,537,397,449,589,585],[15,23,5,35,65,131,259,3596,12293,50188,65605,401420,3735564,4194305,49668,8388673,25559556,45613572,20545,67108865,134348801,271056897,536887297,180224,1075888128,2147614721,4297064449,2149974016]),
([pw396,pw0,pw1,pw2,pw36,pw3,pw4,pw5],[124,24,60,17,181,136,140,52,216,73,28,492,241,444,449,149,69,5,441,413,45,3,509,273],[63,961,227,1088,5,6209,24641,33132,196653,1,125,6252,24684,833,836,8961,6912,271104,32,139361,526401,1056833,2105413,6212,24644,14337,4218881,8402944]),
([pw184,pw0,pw1,pw2,pw36,pw3,pw4,pw5],[60,3,52,401,144,12,140,112,389,448,537,260,17,212,69,181,481,117,5,421,73,137,241,444,509,453,180,65,413,477,28,521,273],[3,15,19,33,65,385,3585,12297,20497,8193,36865,385,70657,393240,8203,3678216,4194696,125838344,134217745,9043984,268435600,537002000,1082138627,385,75498497,532864,2156405760,4362076544]),
([pw184,pw0,pw1,pw2,pw3,pw4,pw5],[28,496,20,32,401,500,397,504,389,8,4,332,17,60,297,29,133,457,120,5,128,73,212,137,421,241,444,509,453,68,413,557,521,273],[3,29,33,65,387,1537,30736,30848,108545,24960,145408,8126480,25165841,33554832,1007681552,25165825,1073742208,2886467584,385,4437573633,9126805888]),
([pw0,pw1,pw2,pw36,pw3,pw4,pw5,pw500],[60,17,508,73,69,181,321,481,3,5,149,117,88,401,180,421,444,112,241,509,105,96,137,413,557,144,397,389,260,8,449,273,537],[15,23,5,35,67,131,257,3596,12293,115724,401420,1654796,8453,2097153,4309508,8782340,19415556,33554689,67190785,134348801,805376001,65537,245760,1344847872,67174657,2147958784,134348801,4563402753]),
([pw501,pw0,pw1,pw2,pw36,pw3,pw4,pw5],[76,24,60,17,481,96,140,52,216,73,4,440,137,3,512,241,149,69,5,181,453,173,413,477,444,68,8,260,537,585],[63,961,227,1088,14401,49217,5,65900,393261,1,528492,49260,125,833,836,66304,49920,1049345,32,2359361,4210753,8650849,50335812,49220,218103877,4247552,956305409,536920065]),
([pw0,pw1,pw2,pw36,pw3,pw4,pw5,pw335],[96,17,364,149,73,3,69,5,124,521,181,136,172,241,321,509,481,24,60,117,88,401,180,516,176,405,440,565,413,557,545,389,537,140,260,573,449],[63,199,4,3843,28675,100355,394499,524444,3145772,4195100,10498060,50364429,67108925,1,201329540,276836484,541098117,67109285,1145045760,2155884544,4311777281,8657305633,79704832,17251205889,17246978304,34368172033,75509761,85966454785]),
([pw268,pw0,pw1,pw2,pw36,pw3,pw4,pw5],[76,24,96,181,60,17,448,52,444,137,509,212,149,73,3,69,5,521,172,241,321,117,88,401,545,520,565,413,389,449,501],[63,449,453,337,832,321,1089,30732,98317,1,131372,1835020,333,2177025,12605440,16916736,42735616,321,4,67174657,168624129,325,16908544,302776320,321,34210048,1610613057,321]),
([pw0,pw502,pw1,pw2,pw3,pw4,pw5],[24,32,153,149,17,257,181,481,52,65,12,28,397,524,389,8,4,173,89,477,241,80,449,88,509,273],[7,11,49,81,49,145,1,770,7170,24578,98306,778,266,266,266,131840,271104,525056,1077248,31461376,41967616]),
([pw0,pw1,pw2,pw403,pw3,pw4,pw5],[24,297,17,181,457,120,5,128,73,212,57,28,20,32,209,137,521,100,241,341,528,188,509,453,68,500,12,3,25,413,557,8,4,273],[7,7,11,11,7,19,2016,31136,117152,1966464,31457664,100665440,402688096,538312800,1096810592,1,537921568,7516194848,537954336,100384,8608153600]),
([pw263,pw0,pw83,pw1,pw2,pw3,pw4,pw5],[52,120,24,468,3,28,453,5,12,532,241,68,449,40,17,181,481,136,205,65,389,92,180,537,96,57,421,73,89,493,521,273],[1,62,73,137,298,1544,14344,16414,73,16393,49162,1544,86024,131073,786433,1,1050114,31461378,33816641,67239937,1601,134217793,917505,268435969,537133057,1181186,1149374466,2151679488]),
([pw264,pw263,pw0,pw1,pw2,pw3,pw4,pw5],[124,24,136,3,12,17,52,73,65,116,285,48,96,449,92,149,5,421,521,204,88,40,481,201,241,549,89,493,573],[31,47,196,325,69,3589,28677,1,32836,65604,393237,525316,3153924,100,101,393253,525348,4202532,8421697,131141,17334336,33587264,325,67633473,134218049,394245,401413,268968960]),
([pw275,pw263,pw0,pw1,pw2,pw3,pw4,pw5],[76,24,96,3,8,17,52,73,65,136,137,116,285,48,453,5,40,68,172,181,49,465,425,549,241,509,361,268],[31,47,196,325,1549,14341,69,1,16452,32836,197636,266244,65557,100,101,525348,266276,3145765,4211009,8405056,17055808,33554501,4194625,4456769,325,67376128,167773189,266245]),
([pw263,pw0,pw1,pw2,pw3,pw12,pw4,pw5],[16,52,73,149,136,173,421,12,3,24,500,48,241,180,449,40,17,29,453,65,413,569,205,565,92,96,273],[1,14,49,464,1680,6160,57360,14,65553,196688,66320,6160,90128,7,14,262166,6150,270342,81,524305,1050625,6291457,1,2128,8405072,6160,50348048,67123200]),
([pw263,pw30,pw0,pw1,pw2,pw3,pw4,pw5],[120,24,124,144,12,28,52,73,149,332,5,48,241,68,449,40,3,17,136,361,92,96,509,29,481,453,421,89,65,493,565,573],[63,1,456,1608,573,6664,57864,196623,453,262209,9,530437,7356421,456,131657,8520205,6664,16925192,449,453,6336,37748928,67371081,402655297,805306433,530437,1145061381,2147489792]),
([pw263,pw0,pw1,pw2,pw3,pw4,pw5,pw330],[16,52,73,149,96,477,40,68,137,48,241,8,17,181,49,465,24,3,569,493,413,557,65,268,136],[1,14,49,464,1552,2128,2128,14,4113,12560,1552,53264,200720,7,14,1542,22,14,786433,1311233,2097169,4194321,1050368,10486032,16908560,1552,1552,1]),
([pw263,pw0,pw1,pw2,pw3,pw4,pw5,pw335],[76,92,88,73,96,364,149,260,12,28,521,172,241,509,537,24,3,17,1,181,425,65,136,93,565,413,557,429,449],[1,126,144,1810,6162,24723,98579,131194,393235,656402,6162,24595,688147,3145833,4195432,8394792,8251,65593,24118273,34609153,68165683,2162737,4201472,138420243,2,6163,6161,268435473]),
([pw268,pw263,pw0,pw1,pw2,pw3,pw4,pw5],[76,24,96,40,8,181,17,52,188,137,509,128,149,88,260,521,172,241,212,1,49,465,425,65,73,545,93,565,413,449,501],[31,103,389,389,772,261,1029,1,14340,16388,33036,196612,29,266276,524325,100,196644,3145765,29626369,50364672,67571712,261,142639361,272826369,261,229632,1610612997,261]),
([pw0,pw187,pw1,pw2,pw3,pw4,pw5],[28,496,12,52,73,149,5,65,3,29,421,48,241,389,176,537,68,449,8,4,441,89,45,565,273],[7,56,200,1793,14336,245760,41,13,9,10243,819201,56,41,6168,1114136,1033,2099272,4259912,3073,8422401,16848896]),
([pw33,pw0,pw1,pw2,pw3,pw14,pw4,pw5],[24,60,181,436,73,132,12,28,3,496,112,413,176,557,257,117,5,521,137,488,25,241,589,585],[7,58,1,482,706,3074,12290,3,3,3,16387,3,3,102416,397328,524306,527376,536592,1216512,528642,7168,569344,1,2104320,405504,4195330,8392706,4201472]),
([pw33,pw32,pw0,pw1,pw2,pw3,pw4,pw5],[60,16,12,28,17,128,73,212,65,112,413,68,557,40,153,209,3,397,76,72,1,133,257,457,5,109,453,25,137,477,521,573],[15,17,225,385,13,1537,14337,16385,32897,65667,131201,1537,790529,193,1048705,2097281,1537,12587009,50331840,32960,1728,67113152,419430528,1664,553652352,1664,1342181504,2147485184]),
([pw33,pw0,pw1,pw2,pw3,pw4,pw5,pw438],[24,60,481,452,73,88,40,68,421,112,413,8,153,72,5,76,117,180,137,285,509,449,508,45,3],[7,58,1,450,1538,2146,2114,3,3,3,3,3,4099,122896,393488,525840,3186704,4194322,188672,42496,9494528,21012482,132864,172288,131330,34304,1538,1]),
([pw33,pw0,pw1,pw2,pw3,pw4,pw5,pw335],[76,260,364,73,65,12,28,565,160,413,557,3,149,5,96,1,257,124,521,241,509,24,60,173,429,137,449],[3,13,17,225,769,1031,2085,4108,57345,475264,590592,1115137,6356993,13,4236,780,13,13,139393,769,1029,8396805,656256,16909313,33685505,769,524545,67108865]),
([pw268,pw33,pw0,pw1,pw2,pw3,pw4,pw5],[72,8,76,40,60,153,24,52,176,173,5,509,260,128,73,88,65,565,160,413,96,257,192,149,212,1,241,45,501],[15,116,388,1669,1,260,2052,4100,57349,65541,131341,786437,15,32522272,34603525,19005728,69992480,293,16794117,4342016,21774336,261,1797,786949,150995461,17170688,285212933,261]),
([pw253,pw0,pw1,pw2,pw3,pw4,pw5],[24,297,17,32,3,65,16,12,28,397,536,285,8,4,181,457,149,449,132,421,413,80,88,557,273],[7,1,120,904,3080,12296,7,7,16387,7,32771,65592,66312,3080,196632,787232,1051680,14811168,263936,12976896,20974592]),
([pw0,pw1,pw2,pw254,pw3,pw4,pw5],[24,297,17,181,457,120,173,212,3,73,149,32,401,20,421,397,540,241,444,509,453,180,28,413,557,449,8,545,273],[7,7,7,11,7,19,2016,15008,50848,201344,3932800,1,4243552,8585312,19661152,4505632,8585248,103546912,344096,168575008,270729216]),
([pw224,pw0,pw21,pw1,pw2,pw3,pw4,pw5],[120,124,16,3,24,20,32,173,5,137,544,361,76,509,72,140,297,17,29,457,212,73,65,12,28,68,40,13,149,453,413,477,545,397,573],[3,29,97,389,513,3073,28673,32793,229376,163969,294913,35840,630784,3145729,4194305,25198593,1033,100663305,135266433,269484033,1051648,806363136,385,1073742977,2147483777,3073,12884910081,17179872256]),
([pw224,pw0,pw1,pw2,pw10,pw3,pw4,pw5],[128,148,153,73,20,3,212,16,24,137,548,361,552,509,84,17,257,29,457,13,149,197,497,5,77,189,89,493,65,28,12,40,68,545,397,573],[7,57,225,305,513,3073,28673,32779,32834,65795,131075,3074,303106,524361,1048577,2097163,3081,4202505,8388673,50331713,67109952,402653248,1610612739,3073,6442459137,3073,25769811969,34359741440]),
([pw78,pw224,pw0,pw1,pw2,pw3,pw4,pw5],[120,32,212,52,24,216,17,65,421,44,116,241,40,68,509,153,173,5,137,556,361,88,80,29,457,73,57,497,413,477,545,573],[15,116,1,132,293,3588,28676,32804,15,196621,262149,1572869,6307845,100,101,8388645,526432,16793696,100728837,293,526340,167788548,293,269025285,536936453,524549,1073758469,2148026368]),
([pw195,pw224,pw0,pw1,pw2,pw3,pw4,pw5],[120,16,3,24,140,17,128,73,5,421,116,413,44,68,557,40,153,149,137,560,361,76,509,72,29,457,57,453,493,65,545,573],[15,57,193,257,529,7169,57345,65553,131137,71,262145,1572865,14680065,112,49,16777233,1572912,37748784,67108929,131649,657472,134365248,593,526337,805322753,526849,1073758721,2148026368]),
([pw224,pw0,pw1,pw2,pw3,pw4,pw5,pw409],[40,68,20,32,3,180,173,137,156,361,8,24,92,17,96,297,65,285,89,397,421,509],[1,30,98,131,770,1027,2070,61440,12384,3,21248,3,26626,65632,3,131840,3,1,3,262496,3,98,3,540673,1064963,3,770,2097155]),
([pw275,pw224,pw0,pw1,pw2,pw3,pw4,pw5],[68,8,3,24,96,297,40,180,65,397,116,285,44,449,20,32,173,137,156,361,17,89],[15,57,65,385,593,7169,8193,81,49153,65665,131073,786433,67,1048624,65712,81,264240,49,65920,65,788480,65,65,2359680,65,65,529,65]),
([pw224,pw0,pw1,pw2,pw3,pw4,pw5,pw330],[40,68,52,88,149,180,3,137,156,361,8,24,92,17,96,297,493,477,285,128,413,397,449],[1,30,102,131,770,1027,3138,61456,28704,3,21248,3,51202,196656,3,262928,3,524370,3,1048864,3,1,3,2113537,2113539,3,770,4194307]),
([pw410,pw224,pw0,pw1,pw2,pw3,pw4,pw5],[68,8,3,24,96,17,128,73,212,5,421,116,413,44,557,153,149,16,137,156,361,509,29,397,461],[15,57,449,769,1041,14337,16385,32785,65793,131333,262145,1572865,2097411,304,304,4194321,1572912,49,65920,66817,528768,385,8389889,528640,16777473,529409,1297,528385]),
([pw0,pw21,pw1,pw2,pw3,pw14,pw4,pw5],[120,24,124,60,3,132,149,401,5,425,140,29,137,153,144,377,525,73,65,12,16,196,44,176,40,13,453,593,45,241,449,589,585],[31,224,773,7173,1,58368,91136,131108,262149,528405,1572885,6291477,25165845,33554469,67112997,134217764,224,75497568,293,1048629,773,276824325,1028,538972165,1082134533,2149580804,4303355908,2157969408]),
([pw0,pw1,pw2,pw10,pw3,pw14,pw4,pw5],[132,73,128,144,153,181,65,117,148,24,377,29,137,525,13,521,209,32,341,497,488,205,337,493,28,564,3,44,568,241,40,344,509,589,84,585,552],[63,248,1820,6429,4,1304,8472,16463,12,102659,196623,262151,524295,1,3149901,1048777,5242952,9437256,17862917,101711877,940572676,7517241348,257,838864901,36869,8891924481,120292638721,9395240960]),
([pw78,pw0,pw1,pw2,pw3,pw14,pw4,pw5],[132,60,153,24,149,436,521,137,32,12,52,200,285,184,449,144,73,425,5,181,216,29,212,357,505,57,488,3,45,589,585],[15,17,33,193,1793,6145,24577,98309,950276,3145793,4194305,9443332,17850372,33652737,193,1281,6145,24577,67371073,201327617,67246080,335568896,1048577,6209,193,536872961,1073750017,536885248]),
([pw195,pw0,pw1,pw2,pw3,pw14,pw4,pw5],[120,24,124,60,181,436,73,5,12,3,196,413,176,557,401,149,117,65,140,29,137,241,449,57,453,593,205,589,585],[31,100,133,805,805,3077,12293,49200,196629,1835013,1,2100240,4206608,8388645,16777253,33554468,3104,12320,68222981,196613,3077,12293,262148,3146757,5246981,134218756,268439556,134224896]),
([pw0,pw365,pw1,pw2,pw3,pw4,pw5],[32,340,20,3,153,73,468,5,17,488,12,137,44,241,237,40,449,465,117,285,593,421,413,557,273],[7,57,984,3408,28752,229456,1025,262665,1029,528387,98305,1310753,1057,528417,98337,2098816,4207232,8487552,15360,101376,16822272]),
([pw30,pw0,pw1,pw2,pw14,pw4,pw5],[28,24,124,137,521,12,3,397,44,253,241,332,29,144,153,5,313,525,488,65,73,421,93,40,105,509,413,557,565,273],[15,29,36,228,1805,29,30720,63492,1,68864,145408,1867780,3407908,4457728,60030976,2883620,67110148,176193540,270532900,278921252,545260800]),
([pw345,pw0,pw1,pw2,pw3,pw4,pw5],[144,17,16,153,496,28,3,73,32,20,488,149,12,421,44,241,413,40,449,557,332,65,93,273],[63,4033,4097,12293,114705,917505,1049739,1048651,12299,114691,917507,2100417,15488,4244608,918656,2109441,114689,917505,61440,405504,8568832]),
([pw0,pw424,pw1,pw2,pw3,pw4,pw5],[24,153,17,257,481,32,3,65,16,12,137,44,389,8,4,453,40,397,421,413,557,449,241,273],[7,7,7,7,11,19,1,480,1568,6176,24608,32992,33312,6176,98336,393856,530560,3211392,4327936,2294272,8460288]),
([pw0,pw1,pw2,pw503,pw3,pw4,pw5],[24,153,17,321,481,124,5,216,117,73,32,149,20,12,421,44,93,241,40,105,509,413,557,137,361,449,273],[7,7,7,7,11,19,992,7840,27296,230016,1835648,1,24800,2261088,5505120,8413344,16941088,5505056,188448,33841184,67534848]),
([pw235,pw0,pw21,pw1,pw2,pw3,pw4,pw5],[120,12,124,3,16,20,32,5,173,137,196,241,76,449,72,140,24,153,181,133,525,132,73,65,44,96,40,13,421,393,245,453,149,413,477,545,573],[1,31,100,405,516,3076,28676,98317,425984,295045,557061,35840,1220608,6291460,8388613,32783,16778253,100663309,136315013,807403525,1075842048,6444556288,389,8589935749,17179869317,3077,34628182021,68719479808]),
([pw235,pw0,pw1,pw2,pw10,pw3,pw4,pw5],[128,124,32,73,148,20,3,216,117,12,436,572,241,552,449,84,153,181,377,133,525,13,197,497,5,205,89,493,28,40,96,509,361,397,545,573],[1,127,402,627,1042,6162,57362,196633,402,327697,589843,6160,1130512,2097179,3,4194331,6169,8388633,16777360,33554819,67111298,134218114,268436051,6161,3758096401,4294973443,27917303811,34359744512]),
([pw235,pw78,pw0,pw1,pw2,pw3,pw4,pw5],[124,32,132,52,212,216,5,137,200,241,88,449,80,153,65,421,169,133,525,73,57,413,477,545,573],[15,20,15,109,133,773,7173,8228,1,16420,32805,36,36,8228,73825,131109,800,272416,1572901,32805,36,36,101,2097505,4194401,773,8423429,16777984]),
([pw235,pw195,pw0,pw1,pw2,pw3,pw4,pw5],[120,12,124,3,16,20,32,453,117,65,137,196,241,76,449,72,140,181,148,73,5,421,413,96,557,40,133,525,57,149,493,545,573],[31,1,228,789,1028,6148,57348,196613,786436,1048581,2162695,4196357,58720261,458880,773,67174405,71680,134430720,268697861,262277,268416,553926784,2162949,4196613,1090519301,6149,2149597189,4294973440]),
([pw32,pw0,pw1,pw188,pw2,pw3,pw4,pw5],[28,136,153,32,397,297,17,137,133,457,120,5,128,209,401,549,212,521,44,204,241,40,68,509,89,45,273],[7,3,11,3,17,3,3,98,98,98,387,98,546,1,15360,3,28672,45056,68610,131203,1835010,14680066,3,17370112,37817344,3,3,72876032]),
([pw32,pw366,pw0,pw1,pw2,pw3,pw4,pw5],[28,128,20,132,209,136,421,17,137,521,257,133,457,401,549,100,241,204,413,120,5,68,557,449,180,273],[7,9,19,33,65,33,33,162,1,34,771,34,34,178,1184,2337,1184,4256,8210,19,8210,16402,33,491520,33030144,33,33,35880960]),
([pw366,pw0,pw1,pw2,pw3,pw4,pw5],[32,12,20,73,3,65,16,24,576,285,8,4,297,209,136,5,17,212,421,137,181,88,449,445,80,401,28,549,413,557,273],[7,9,113,131,769,3073,12305,249904,1855744,21248,31477760,33562657,67641345,769,138420225,933920,268436256,560070688,279296,543571968,1075839744]),
([pw32,pw0,pw1,pw2,pw384,pw3,pw4,pw5],[28,136,181,16,421,297,17,137,133,457,120,205,425,100,241,128,341,204,180,509,433,12],[7,3,3,11,17,3,3,98,98,98,387,98,546,7168,1026,3,253952,884736,1,3,7168,1313792,2097283,1026,1026,3,3,417792]),
([pw0,pw1,pw2,pw384,pw3,pw4,pw5],[136,17,144,297,3,16,12,421,181,457,425,212,205,73,32,149,20,137,204,241,341,500,188,509,453,180,28,413,557,569,4,8,521,273],[15,31,107,391,15,519,15364,122885,174209,3942400,62924800,67108868,67243141,136582148,851444740,67240101,136839173,3498049541,133249,4303358081,8626372608]),
([pw32,pw504,pw0,pw1,pw2,pw3,pw4,pw5],[28,120,500,124,52,136,397,17,128,73,212,12,204,3,68,40,137,133,37,49,241,441,413,433,205,273],[7,9,49,35,65,33,33,162,1794,1,2051,12294,57346,1440,162,196641,266400,540832,1794,33,1054464,2115328,35,4198402,25182210,33,33,34623488]),
([pw32,pw0,pw1,pw2,pw3,pw4,pw5,pw505],[28,40,136,545,297,17,457,120,5,128,73,180,100,241,341,156,3,89],[3,5,5,9,5,3,3,52,52,3,52,70,2,3968,3,62976,2562,67076,3,166272,34946,2436,3,7,3,2050,45060,1]),
([pw32,pw0,pw1,pw2,pw3,pw4,pw5,pw438],[24,40,60,188,8,144,65,5,521,137,112,285,241,449,509,89,45,28,273],[3,12,12,1,12,22,2,5,5,3,5,3,3,224,770,7168,24578,12,98,33888,65570,12,3330,770,131078,263170,12,1]),
([pw32,pw0,pw21,pw1,pw2,pw3,pw4,pw5],[120,124,16,3,28,20,32,425,5,397,208,389,76,537,72,24,17,297,133,457,212,73,65,12,44,68,40,13,137,129,241,149,453,477,521,573],[3,29,97,389,513,3073,28673,33801,197632,385,263169,199680,599040,3145729,4194305,8389649,16778249,100663305,135266433,806354945,1074793472,6443507712,385,385,8589934721,3073,17448312833,34359741440]),
([pw32,pw0,pw1,pw2,pw10,pw3,pw4,pw5],[128,436,73,209,212,205,28,3,397,580,389,552,537,84,144,17,117,24,257,137,148,133,457,13,241,497,5,89,493,521,40,68,509,573],[3,15,49,195,257,1537,14337,49157,98352,409601,3686401,280064,5296128,8388629,16385,13,16777733,33554437,67108881,49,134218288,268435504,537395265,16777729,7516192769,1537,537399297,8589936128]),
([pw78,pw32,pw0,pw1,pw2,pw3,pw4,pw5],[120,32,212,52,24,60,17,65,521,137,44,584,241,40,68,509,132,425,5,397,389,88,537,80,73,144,216,133,457,57,497,477,573],[15,116,1,132,773,7172,57348,65540,15,393229,524293,1050629,14680069,50331716,393285,201326853,1054784,373325888,553779205,773,6148,1090551812,393477,133125,2147614725,1050885,773,4294973440]),
([pw195,pw32,pw0,pw1,pw2,pw3,pw4,pw5],[120,16,3,28,60,17,24,128,73,5,12,208,413,68,557,40,153,401,205,397,76,72,133,37,457,57,453,493,521,137,573],[15,113,385,513,1033,6145,57345,67585,131201,262275,524289,6145,3162113,2208,2081,4196353,8394784,16795680,33554561,131201,6272,67256448,264321,6145,134496257,6145,805322753,1073747968]),
([pw32,pw0,pw1,pw2,pw3,pw4,pw5,pw409],[40,68,20,32,549,180,205,397,156,389,537,449,28,3,96,17,128,453,5,241,24,60,89,509],[1,30,98,131,770,3075,12294,245776,295008,3,525056,3,3178498,327792,3,590608,3,1,3,4194656,3,262178,3,3073,4099,3,524546,8388611]),
([pw275,pw32,pw0,pw1,pw2,pw3,pw4,pw5],[68,8,3,28,60,297,24,40,180,65,156,285,449,20,32,205,397,389,96,17,128,453,132,5,241,89,137,509,501],[15,113,129,769,137,3073,4097,129,24577,33025,65537,132097,131,8126496,8913696,129,134176,161,12583680,129,20974592,129,129,33556224,129,129,469762049,129]),
([pw32,pw0,pw1,pw2,pw12,pw4,pw5],[12,28,421,136,52,3,397,565,17,144,297,25,24,457,212,205,73,521,137,44,93,241,40,105,509,413,557,273],[1,30,30,97,142,142,1800,3848,5633,1800,8968,117248,393217,3751936,29442048,3,36178432,88082944,2752513,393217,141033472]),
([pw30,pw32,pw0,pw1,pw2,pw4,pw5],[28,137,16,397,24,521,12,588,253,52,421,565,332,17,128,149,73,144,257,5,457,212,93,241,40,509,453,68,413,557,273],[15,19,35,65,387,35,65,1537,1029,1153,3073,258048,929792,397440,1191936,2867200,12599424,251707392,276955264,722075648,1216348288]),
([pw32,pw0,pw1,pw2,pw3,pw4,pw5,pw330],[40,68,52,88,209,180,569,397,156,389,557,8,28,3,96,17,144,297,477,24,493,241,149,128,413,137,521],[1,30,102,131,770,3075,14338,245776,295008,3,197376,3,720898,1048688,3,2097936,3,12591106,3,16777568,3,1,3,100664321,4099,3,770,65539]),
([pw410,pw32,pw0,pw1,pw2,pw3,pw4,pw5],[68,8,3,28,60,17,24,128,73,212,5,12,156,413,557,40,209,569,397,149,477,241,509],[15,113,897,1537,2057,12289,16385,32769,66049,131585,262145,12289,33283,525088,1180192,32769,2109472,32801,656128,33281,13056,769,33281,12800,33281,12289,4194817,12289]),
([pw0,pw21,pw1,pw2,pw3,pw4,pw5,pw438],[72,24,76,60,3,80,401,88,149,5,425,140,457,144,525,577,49,73,65,40,68,160,36,16,13,453,361,241,449,509,120,397,124,389],[31,480,1541,30720,47104,75781,1,131204,262149,1572885,6291477,4726789,12582933,16777381,33554656,480,197,228,1541,1541,645,1157,203423744,805306373,7516192772,69206021,8592031748,2052]),
([pw0,pw1,pw2,pw10,pw3,pw4,pw5,pw438],[88,73,84,144,457,481,65,117,148,24,525,577,49,449,13,209,341,509,497,32,180,421,205,160,413,337,508,493,521,40,241,168,3,8,592,128,552,564],[63,248,1820,1304,2328,12573,4,16463,12,32775,65543,401667,786447,1,7340104,58720328,201334861,67109065,875560964,3313500164,604119301,15099494405,17476616192,139269,240789749761,85916131333,18278776833,257]),
([pw78,pw0,pw1,pw2,pw3,pw4,pw5,pw438],[80,24,88,60,457,149,292,40,68,137,164,285,449,509,32,8,52,144,73,425,5,481,180,397,525,184,389,216,49,57,209,421,413,300,508,212],[31,37,68,901,3077,12357,114693,393237,3801104,63046160,67111952,402657285,1,537264133,1074004485,3077,12293,81925,2153382400,4295494656,8590462981,17180459012,41946624,12805,34401681412,3077,67109892,134217732]),
([pw195,pw0,pw1,pw2,pw3,pw4,pw5,pw438],[72,24,76,60,481,292,5,40,68,421,160,413,8,16,3,88,401,84,149,117,65,140,144,525,49,57,453,509,449,32,205,493,241,120,124],[31,36,69,901,3077,4133,28677,491536,1572885,14680592,4197392,23068677,1,34242565,67338752,199680,402718725,537067524,1074266629,3077,2152202245,1581061,4294970880,402653701,25769804292,3077,3076,2097156]),
([pw0,pw83,pw1,pw2,pw3,pw4,pw5,pw438],[68,60,3,24,80,73,88,453,180,5,65,521,421,156,241,389,40,205,137,8,28,89,537],[15,240,1792,6145,57344,65537,17,65601,131329,262145,40961,589825,1572869,240,65617,41072,97,113,6401,2106112,769,1281,6145,4161,4161,24577,40961,4194305]),
([pw31,pw0,pw1,pw2,pw3,pw4,pw5,pw438],[68,60,525,24,40,180,173,421,156,361,509,449,20,8,3,88,73,84,453,65,389,32,89,397,137,537],[15,17,97,129,769,3089,28673,491524,524388,21,1049348,17,17,196704,17,1180416,17,2166785,17,4194656,17,524321,17,3073,25165841,17,1048833,33554433]),
([pw0,pw367,pw1,pw2,pw3,pw4,pw5],[32,4,20,3,261,73,92,257,5,17,508,132,137,165,188,36,241,557,449,117,12,28,285,401,421,413,273],[7,57,1992,30912,99008,426176,32769,525321,3149825,4227073,32771,8912929,20513,4227105,32801,16784648,33654016,165184,16881664,317504,67338304]),
([pw0,pw1,pw86,pw2,pw3,pw4,pw5,pw438],[140,481,144,457,3,24,525,577,40,452,209,88,65,5,521,137,156,285,241,508,421,413,8,397,273,449],[15,55,15,71,135,263,260,3589,13317,49408,459776,65792,525316,261,1048836,2162693,4194565,4718613,4357,2166789,65797,12293,213248,49408,8388868,50397440,2162692,1]),
([pw30,pw0,pw1,pw2,pw3,pw4,pw5,pw438],[68,60,525,24,452,149,88,40,137,156,361,509,449,28,8,3,188,144,457,5,481,389,180,65,73,52,89,537],[15,113,129,257,1537,6273,57345,458788,1769476,133,2164228,129,129,13238304,161,2098720,161,50364417,129,71304704,129,12582913,129,6145,8321,129,2097665,134217729]),
([pw385,pw0,pw1,pw2,pw3,pw4,pw5],[92,17,16,457,4,32,73,76,20,149,8,28,397,12,137,0,36,241,389,557,449,144,3,181,425,508,65,180,421,188,413],[31,993,1152,30849,491649,1573893,2097675,6291595,10506243,458755,1573899,117441216,973083200,458816,1574081,486543488,1090715776,1574017,479232,1578113,197761]),
([pw0,pw1,pw2,pw373,pw3,pw4,pw5],[92,17,128,149,73,3,257,5,120,12,4,525,28,40,36,241,212,20,32,93,173,16,413,361,397,273,449],[63,483,3587,14343,49219,26627,65948,397341,12316,573452,24589,3150241,12676,4243840,24961,20484,8409089,29189,12292,16805893,100687873]),
([pw0,pw449,pw1,pw2,pw3,pw4,pw5],[24,457,17,181,257,32,3,65,16,12,28,397,36,389,449,149,216,132,421,413,557,241,585],[7,7,7,11,19,7,1,480,3616,12320,20512,32992,34912,12320,36896,460992,536704,1118336,2111488,4331520,5255168]),
([pw0,pw1,pw2,pw506,pw3,pw4,pw5],[24,457,17,181,321,76,5,216,117,73,32,401,20,180,421,444,36,241,557,137,413,28,397,389,449,585],[7,7,7,11,19,7,992,7840,60032,199296,361120,1,581728,1245280,327904,6348832,8585248,17137824,122880,33906720,34045984]),
([pw0,pw1,pw2,pw507,pw3,pw4,pw5],[24,297,17,525,120,5,128,73,212,57,28,20,32,209,137,40,36,93,241,3,205,16,413,273,449],[7,7,11,11,7,11,1008,15568,58576,458944,98496,3671088,50224,4522032,98352,1,4260880,99344,50192,115728,25264128]),
([pw452,pw0,pw21,pw1,pw2,pw3,pw4,pw5],[72,8,76,3,16,20,32,5,425,124,137,120,160,241,449,140,24,457,481,525,445,88,73,65,40,68,36,13,149,453,245,361,585,537],[1,31,100,405,3588,12292,16388,98317,425984,389,689152,45056,1081349,6291460,8388613,50331661,67112973,16809991,136315013,807404544,1075851264,270532613,389,389,2130053,2147496960,12884902917,12293]),
([pw452,pw0,pw1,pw2,pw10,pw3,pw4,pw5],[84,76,32,73,148,20,3,216,117,8,564,137,128,596,241,292,449,457,481,525,13,209,489,5,205,89,101,68,521,40,361,537,585],[1,127,402,627,7186,24594,98322,393241,402,655377,657424,24592,163859,1048603,3,2097177,24601,4194331,8388752,16777602,33563010,67142019,939524113,24593,33299,1073768448,6710921219,4294991875]),
([pw452,pw78,pw0,pw1,pw2,pw3,pw4,pw5],[76,32,88,52,80,216,5,132,137,212,164,241,449,457,65,557,425,525,445,73,57,361,585],[15,20,15,109,901,3077,4101,8228,1,16420,36,36,32805,8228,73825,139552,3104,262181,1572901,36,36,32805,65633,66657,101,2100480,4227333,3077]),
([pw452,pw195,pw0,pw1,pw2,pw3,pw4,pw5],[72,8,76,3,16,20,32,149,117,65,124,137,120,160,241,449,140,481,148,73,5,40,68,421,413,525,445,57,453,205,101,585,537],[31,1,228,789,7172,24580,32772,196613,786436,1048581,14680069,16785413,2162695,458880,773,33753088,90112,67174405,134480133,277088384,286848,262277,545259781,16785669,1073807621,25192448,6442452997,24581]),
([pw452,pw0,pw83,pw1,pw2,pw3,pw4,pw5],[40,68,8,3,28,20,32,180,5,156,241,449,468,457,481,205,137,389,89,421,429,521],[1,30,98,386,19,1538,2051,4106,28672,4480,3,5632,3,1,32898,65539,131586,7,33152,3,132608,3,3,263040,3,3,3670017,3]),
([pw452,pw31,pw0,pw1,pw2,pw3,pw4,pw5],[68,8,3,20,40,32,180,5,397,137,156,241,449,148,525,173,421,361,453,73,89,537,533],[15,17,45,193,785,3073,4097,24577,17,32833,65537,132097,19,811008,8384,17,11264,17,8384,17,11264,17,17,1049792,17,17,6291713,17]),
([pw452,pw0,pw1,pw86,pw2,pw3,pw4,pw5],[40,68,52,216,149,3,8,5,137,156,241,449,73,24,65,209,421,413,521],[1,30,102,142,267,1538,2051,4120,8234,16520,3,1544,3,32778,4248,3,1560,3,1,65539,131586,75,3,131720,3,3,262401,3]),
([pw452,pw30,pw0,pw1,pw2,pw3,pw4,pw5],[68,8,3,28,40,52,149,180,5,156,241,449,332,525,148,88,137,361,457,65,285,89,421,429,553],[15,17,101,417,25,1537,2049,12289,49217,17,65537,131585,19,274496,4480,17,5632,17,524736,17,1050176,17,17,2098048,17,17,29360129,17]),
([pw0,pw1,pw53,pw2,pw3,pw4,pw5],[32,401,52,149,5,425,140,3,397,60,137,48,241,389,600,537,449,13,453,28,12,8,477,521,573],[15,1,52,1984,14912,115392,15,131095,262151,15,262151,52,1574720,14912,2212416,52,52,4194324,15616,8503680,16783360]),
([pw1,pw53,pw2,pw3,pw4,pw5],[32,401,52,149,13,5,453,425,3,397,17,137,153,48,241,389,600,537,449,457,477,521,573],[15,55,71,15,71,164,7936,58368,984320,164,164,1048612,59904,2556672,4218880]),
([pw257,pw1,pw2,pw3,pw4,pw5],[24,153,17,257,457,16,65,5,32,73,52,149,341,453,173,337,477,48,361,241,604,449,3,509,521,573],[7,7,7,11,19,224,3840,5888,9984,16480,32864,65632,917504,32505856,33947648]),
([pw0,pw1,pw2,pw258,pw4,pw5],[32,81,52,149,5,77,12,397,137,44,241,389,40,449,537,421,441,413,45,273],[15,52,448,3584,28672,15,32839,1543,69639,52,131604,266260,448,12480,529920]),
([pw191,pw0,pw1,pw2,pw3,pw4,pw5],[28,3,153,24,12,32,149,16,48,361,8,4,73,52,5,65,389,176,537,68,449,441,173,89,45,608,273],[15,113,145,33,769,3073,12388,49284,7,66308,1966084,12512,8289,9056,2629728,4194433,8405376,17318016,769,33816579,67633920]),
([pw191,pw0,pw1,pw2,pw4,pw5],[28,397,3,153,137,421,52,149,173,48,361,509,521,608,73,65,389,537,457,453,89,477,573],[31,227,355,1555,14343,16584,33096,67080,403468,16832,1728,526528,1049408,2097472,4195840]),
([pw0,pw1,pw2,pw3,pw411,pw5],[32,93,52,149,5,89,3,397,17,137,153,48,241,389,612,537,449,457,453,173,477,521,573],[15,52,1984,14592,246080,15,15,15,262151,524308,52,1048596,14976,2212032,4200448]),
([pw0,pw1,pw2,pw3,pw4,pw412],[32,105,52,149,5,101,3,397,17,137,153,36,241,389,537,449,173,413,273],[15,52,1984,14592,51456,15,15,6151,15,65556,133140,52,14976,51328,284672]),
([pw0,pw21,pw1,pw2,pw3,pw4,pw5,pw335],[72,76,3,96,80,401,88,149,5,425,120,545,124,521,160,241,389,537,509,140,17,144,73,65,12,36,4,16,13,32,20,429],[15,240,771,15360,114688,393219,3670018,4194370,8388611,16781319,33570823,100667395,150994951,268435539,3184,240,99,1610612818,771,771,323,323,56320,2147488771,1,49155,49154,1026]),
([pw268,pw0,pw21,pw1,pw2,pw3,pw4,pw5],[76,144,153,140,8,40,20,32,5,173,72,160,361,509,3,96,80,401,88,149,425,120,521,545,389,585,449,73,65,28,36,13,501],[15,49,193,769,1025,6145,8193,49153,983044,1048833,14680068,16783364,100663301,134479873,268435457,538968097,1073760257,49,2147746049,2555904,399360,393217,769,1050881,262401,2103296,4297064449,6145]),
([pw104,pw0,pw1,pw2,pw3,pw4,pw5],[20,149,73,52,65,5,60,28,137,148,12,397,0,616,389,241,4,8,257,377,525,453,173,89,477,620,449,3,509,521,573],[1,7,56,4032,62016,197184,7,56,789312,57920,1311296,7,7,40963,2097155,4194328,8396824,16777240,59648,1040187648,1073766400]),
([pw0,pw1,pw2,pw60,pw3,pw4,pw5],[20,73,453,52,5,65,28,3,153,24,521,100,389,624,241,628,537,68,449,149,205,89,45,8,273],[7,56,960,1472,30976,491776,7,524355,1091,24579,7,1048664,1048664,2105368,4325400,1,12352,8486976,13376,99392,16922624]),
([pw0,pw1,pw2,pw10,pw3,pw4,pw5,pw335],[88,73,84,364,3,17,117,65,96,257,128,545,124,521,160,389,632,241,537,509,552,148,13,205,89,28,429],[63,232,796,15392,246304,786469,3145777,4194383,4108,12303,196623,540683,1052687,1,8388680,16842824,1048653,1048649,33566732,213004,1572877,1048605,236544,67378181,4,1146885,245761,1025]),
([pw268,pw0,pw1,pw2,pw10,pw3,pw4,pw5],[76,128,636,73,8,137,509,3,17,65,212,117,96,257,160,389,640,241,449,585,13,489,5,89,101,521,545,501],[7,15,7,23,34,7,71,394,3841,12418,6,254208,786437,1048587,1,14,196618,2097159,4195330,7,8455681,16778245,100663302,212994,23,6,167772167,589829]),
([pw193,pw0,pw1,pw2,pw3,pw4,pw5],[28,3,153,24,32,149,52,205,644,389,8,4,5,65,521,421,241,80,537,68,449,89,45,273],[15,49,193,65,769,3073,84,12356,49157,66308,1966084,8272,81,80,80,32833,2097472,4722752,769,49153,8913664]),
([pw78,pw0,pw1,pw2,pw3,pw4,pw5,pw335],[80,88,364,149,65,509,32,5,425,132,545,521,160,389,164,241,537,216,17,3,73,57,429,449],[7,11,22,7,7,39,71,7,388,3584,61440,65571,917506,3145735,7,7,39,71,388,388,135,134,50688,4194851,1,24611,49154,8388610]),
([pw268,pw78,pw0,pw1,pw2,pw3,pw4,pw5],[76,32,88,40,8,184,209,73,137,509,212,65,545,5,425,160,389,164,241,57,489,501],[31,37,199,37,292,37,517,1028,1,3076,4140,1028,29,1092,25601,1056,491520,37,524357,228,1092,1049669,13345,25601,37,1056,2098213,37]),
([pw0,pw348,pw1,pw2,pw3,pw4,pw5],[16,20,401,149,5,65,140,17,60,181,321,481,28,397,12,137,0,48,241,389,4,8,453,173,89,477,648,449,3,509,521,573],[1,14,49,960,1472,2496,14,49,61760,983360,3146048,19,4194310,14,4194310,8388625,16908305,33554449,958464,2080382976,2147876864]),
([pw0,pw1,pw194,pw2,pw3,pw4,pw5],[20,73,149,28,3,153,24,16,5,65,421,48,241,389,176,537,68,449,441,173,8,4,89,45,565,273],[7,120,928,1080,14368,245792,7,7,7,6147,327683,524424,1,10248,3178504,1160,4196736,8454528,3080,16811016,33626112]),
([pw195,pw0,pw1,pw2,pw3,pw4,pw5,pw335],[72,76,3,17,96,292,5,12,28,565,160,413,557,509,16,88,401,84,149,117,65,120,124,521,241,140,144,57,453,537,32,20,205,429],[31,34,67,899,3075,12323,16519,491528,1572875,14680584,16780296,12299,100663306,134905859,270762496,199680,536940547,3221356550,4719107,3075,12291,4295507971,18877952,8592035843,1,3075,16778242,2097154]),
([pw268,pw195,pw0,pw1,pw2,pw3,pw4,pw5],[72,8,76,40,144,153,140,20,32,149,65,205,160,361,509,3,17,96,128,73,5,565,413,401,117,521,585,449,57,453,101,501],[15,116,900,3077,1,12292,16388,229381,786436,1048581,2359309,4198405,15,8716832,16843781,35979296,4206624,201326629,268698629,539230720,274944,262661,3077,4199429,1140851717,274432,2147745797,12293]),
([pw0,pw83,pw1,pw66,pw2,pw3,pw4,pw5],[28,468,153,32,453,3,5,65,120,521,340,241,389,68,449,537,80,149,205,144,137,652,73,81,413,557,421,273],[7,30,1,486,519,7174,122886,131081,3,786465,1048577,5121,2129953,26,4194456,8388617,5144,2113560,480,515,16780288,33644544,67371521,16780608,33644864,5633,98817,134228992]),
([pw0,pw1,pw66,pw2,pw3,pw4,pw5],[32,73,60,153,436,149,144,65,3,5,28,421,352,137,112,389,340,241,468,449,537,453,16,413,652,557,8,477,521,573],[63,1,972,15372,245772,1835276,55,51,51,229395,2621459,4195268,15380,8503300,117965060,15552,8503488,185074112,15360,270015488,536985600]),
([pw307,pw0,pw83,pw1,pw2,pw3,pw4,pw5],[28,468,340,20,12,3,5,52,656,241,68,449,40,153,32,209,205,140,397,389,96,537,92,73,453,81,421,521,413,80,557,273],[1,7,26,226,19,774,7170,8195,24578,8290,8195,770,11266,49153,196641,262145,524545,7340033,25247808,33570817,541440,8408064,201392129,268436288,1610615872,524545,203423745,2147485440]),
([pw0,pw83,pw1,pw2,pw91,pw3,pw4,pw5],[28,3,153,32,453,73,52,17,205,120,468,521,421,100,389,660,241,80,537,68,449,209,180,413,557],[7,60,454,1542,6149,122884,1966084,2097161,65,65,65,49153,4456449,56,56,73,88,56,1,321,8421696,17301824,65,57856,918016,6145,6145,4775936]),
([pw0,pw1,pw2,pw91,pw3,pw4,pw5],[32,73,52,453,3,17,205,120,24,257,421,564,521,660,241,389,636,537,180,449,28,413,557,8,273],[15,116,944,7328,57888,983072,15,15,3079,24583,15,1,1049668,2105412,4194388,4,57472,9371776,7296,7296,17063936]),
([pw0,pw83,pw1,pw2,pw3,pw4,pw5,pw469],[28,3,153,96,32,453,73,120,65,180,5,521,421,100,389,156,241,537,40,80,205,545,89],[15,116,1924,6149,122884,393732,524804,262161,1049089,2097153,49153,131585,262657,112,262161,49200,112,112,6657,4227968,33664,33664,6145,6657,6657,57856,107008,1]),
([pw0,pw83,pw1,pw2,pw3,pw4,pw5,pw330],[68,3,153,96,52,73,453,477,493,521,421,156,241,389,557,40,468,8,28,32,413],[15,116,404,1541,14340,49157,65543,32785,19,17,10241,180225,393219,112,529,6192,49,524305,1041,1050768,16401,32785,1537,1537,295425,6145,6145,17]),
([pw508,pw0,pw1,pw2,pw3,pw4,pw5],[12,20,149,209,52,65,5,137,397,44,389,241,40,537,449,81,441,89,45,273],[1,14,112,385,3584,28672,14,112,385,3584,28672,14,32771,2566,69638,49,131632,266288,385,20609,529920]),
([pw509,pw0,pw1,pw2,pw3,pw4],[8,449,537,509,557,585,20,209,149,52,5,65,12,397,137,36,241,389,81,89],[7,11,19,7,35,448,3584,28672,229376,448,266432,98496,5632,558592,28672]),
([pw0,pw386,pw1,pw2,pw3,pw4,pw5],[12,32,209,60,297,128,149,136,3,5,65,421,457,20,16,205,137,0,44,241,389,4,8,453,413,40,557,449,273],[1,126,1944,2073,4248,4248,8302,50056,67593,1966216,6291592,102,67587,1835046,8388646,68097,17564160,234881536,67585,167774209,302776320]),
([pw0,pw1,pw2,pw510,pw3,pw4,pw5],[32,73,52,149,117,65,124,24,128,3,17,153,421,521,44,241,389,40,449,537,489,89,101,285,273],[15,52,4032,15680,115712,918528,15,15,15,49159,1179655,1,20500,2113556,4325396,4,8438080,917824,12608,12608,16957440]),
([pw0,pw216,pw1,pw2,pw3,pw4,pw5],[20,73,149,52,5,65,28,397,60,181,132,137,112,389,377,148,525,12,0,664,241,4,8,453,25,89,477,521,573],[1,7,56,4032,29440,99072,7,56,134592,1847552,6324480,7,7,1572867,8388611,16778264,34078744,67108888,3264,134218944,268972032]),
([pw511,pw0,pw1,pw2,pw3,pw4,pw5],[8,20,149,497,52,65,5,60,28,137,96,12,397,0,36,389,241,449,537,17,181,173,89],[1,14,112,8064,124032,393345,14,112,1578624,115840,393345,14,14,81926,7,2097200,4210736,49,119296,393729,49153]),
([pw0,pw1,pw2,pw512,pw3,pw4,pw5],[20,73,453,52,5,65,28,3,153,24,40,36,241,389,205,89,421,273,449],[7,56,960,1344,14592,3328,7,1091,1091,6147,7,16472,1112,34840,3096,1,10304,3136,1088,68672,396288]),
([pw0,pw389,pw1,pw2,pw3,pw4,pw5],[8,32,497,60,153,84,149,96,3,5,65,297,557,20,16,425,28,421,12,137,0,36,241,413,449,245,144,668],[1,126,1944,2200,2200,4121,8302,50056,983176,15728776,16781321,102,102,39845926,16777283,202015488,14713344,16781825,15335424,16912385,6295553]),
([pw0,pw1,pw2,pw513,pw3,pw4,pw5],[32,73,52,453,117,65,76,24,84,3,17,257,180,397,636,137,36,241,389,557,509,197,77,89,28,521,292,273],[15,52,4032,62464,461824,1639744,15,15,2113543,196615,15,1,4210708,8454164,65556,50356544,459072,4,61440,67707200,134938944]),
([pw0,pw1,pw2,pw392,pw3,pw4,pw5],[32,73,84,453,120,65,3,5,17,24,28,181,137,397,36,241,389,557,449,12,549,173,16,40,413,273],[15,496,3908,15632,114944,409860,15,1573895,1053703,114695,278543,6292596,10490928,16826416,147508,1,16794628,148500,13328,21524,33734660]),
([pw275,pw30,pw0,pw1,pw2,pw3,pw4,pw5],[68,8,3,28,153,332,40,52,65,156,285,96,549,361,453,5,389,89,421,429,553],[15,53,65,385,73,1537,129,2069,4225,65,129,8705,67,20624,33168,81,67088,81,37248,65,8832,65,65,131968,65,65,1835009,65]),
([pw0,pw1,pw2,pw47,pw3,pw4,pw5],[52,73,149,5,65,28,397,60,181,140,137,48,241,389,3,449,537,453,173,89,477,12,4,8,440,521,573],[7,25,1,2016,15232,115584,7,7,7,6147,131075,25,262153,526345,1048585,2098912,14976,12681856,11360,50430048,67115008]),
([pw393,pw0,pw1,pw2,pw3,pw4,pw5],[12,60,32,149,136,20,73,16,500,28,421,44,389,241,4,8,257,297,3,5,1,457,120,212,117,137,40,105,509,413,557,449,273],[1,126,914,1283,14610,49170,196698,1900562,66563,14354,2162706,29884488,33555521,14344,478150664,34079745,536877056,1414004736,11265,2214593537,4362082304]),
([pw0,pw514,pw1,pw2,pw3,pw4,pw5],[32,3,153,24,453,593,52,5,205,12,421,521,44,241,389,40,449,537,413,45,273],[15,53,452,3588,28676,229380,513,321,65,20481,163841,337,81,49,81,448,266432,557248,3584,3584,1093632]),
([pw0,pw515,pw1,pw2,pw3,pw4,pw5],[12,52,73,149,5,205,397,137,44,241,389,40,449,537,209,441,413,45,273],[1,14,50,193,1792,14336,16390,50,193,1792,14336,14,7,774,34822,19,65810,133138,193,6209,264960]),
([pw0,pw1,pw2,pw3,pw516,pw5],[52,73,149,173,89,12,397,137,44,241,389,40,449,537,441,433,273],[7,25,224,1792,14336,7,7,7,18435,25,25,34825,224,6240,68352]),
([pw0,pw1,pw2,pw3,pw4,pw517],[52,73,149,45,101,12,397,137,36,241,389,537,449,413,5,273],[7,25,224,1792,6400,7,7,771,7,41,8457,16649,224,352,35584]),
([pw30,pw0,pw139,pw1,pw2,pw3,pw4,pw5],[28,124,24,173,137,332,377,128,149,73,144,5,65,153,525,3,12,44,196,413,40,68,557,93,176,105,421,161,273],[3,7,3,11,17,3,3,1,2016,6178,3,9312,17504,33410,6178,65571,917506,7340034,2690,3,9175424,56623488,201326595,788482,6293506,3,3,271319040]),
([pw0,pw139,pw1,pw2,pw3,pw4,pw5],[28,332,377,60,153,3,5,65,269,137,525,73,32,20,488,149,12,124,421,112,413,0,496,241,176,557,4,8,93,453,173,477,521,573],[1,30,238,783,30,1038,63528,213194,328203,16252936,251658248,51392,444929,274221056,587221024,1074152001,14172224,2197831744,393729,4328653313,8595701760]),
([pw30,pw518,pw0,pw1,pw2,pw3,pw4,pw5],[28,124,496,205,397,52,3,453,5,65,12,196,241,68,449,40,136,377,128,73,216,505,176,93,509,421,161,89,45,273],[7,3,3,11,17,3,3,1,226,802,1027,6150,57346,2031744,770,3,202752,6512640,770,3,8657024,21782656,100663299,134220034,268443906,3,3,536885248]),
([pw30,pw0,pw519,pw1,pw2,pw3,pw4,pw5],[28,124,20,173,521,128,401,149,5,65,100,389,196,241,176,449,537,12,509,421,161,89,45,273],[3,7,3,11,17,3,3,34,224,770,3,15360,114688,1,290,131075,34,34,290,3,224,278624,1572867,2101506,4210946,3,3,8412160]),
([pw0,pw519,pw1,pw2,pw3,pw4,pw5],[32,3,297,24,149,401,52,5,65,28,421,124,521,104,389,672,241,80,537,88,449,285,8,4,173,89,45,273],[15,53,452,7684,122884,1966084,513,321,65,2129921,13631489,337,81,49,81,16778432,33587392,67633344,7680,7680,134799360]),
([pw30,pw0,pw1,pw2,pw3,pw4,pw5,pw361],[28,124,569,521,4,3,73,17,128,149,5,65,100,389,156,241,537,509,332,421,161,89,565,573],[3,3,7,9,3,3,19,992,3202,3,61568,213120,262306,1346,3,61760,147776,354,1572867,2114562,17410,17410,3,3,4718595,8482816,53250,1]),
([pw30,pw0,pw1,pw2,pw3,pw4,pw5,pw330],[68,176,569,137,557,8,4,52,73,149,477,493,48,241,389,421,413,5,553,28,12],[3,3,7,9,3,113,97,896,3074,3,28672,3,3,386,3,12672,3,3,32899,70658,147,131075,3,294929,1605633,3,3,129]),
([pw353,pw0,pw1,pw2,pw3,pw4,pw5],[8,60,32,149,96,20,73,16,4,28,137,12,421,0,36,413,241,557,257,153,3,5,1,72,192,117,176,93,449,173],[1,126,402,7698,122898,131331,786522,7602194,791570,114706,393219,60817480,84939848,151044104,268566537,614470656,114688,270663681,119808,268567553,49153]),
([pw0,pw417,pw1,pw2,pw3,pw4,pw5],[32,3,457,24,149,401,52,5,425,397,132,137,36,241,389,557,509,493,12,28,545,589,284],[15,53,452,3590,28676,102404,4097,131137,1835009,2101249,65,131153,81,49,81,448,448,4288,15872,4199936,2142208]),
([pw0,pw1,pw2,pw363,pw3,pw4,pw5],[3,73,17,128,149,72,65,5,24,28,181,137,397,36,241,389,557,449,192,20,32,209,40,413,273],[31,229,1805,7692,57348,204836,262330,3670538,4196890,57354,73770,4194920,4196968,8413280,204896,8712,8397320,74280,6664,10792,16867360]),
([pw0,pw520,pw1,pw2,pw3,pw4,pw5],[8,52,73,149,5,493,96,17,60,181,321,537,401,28,397,12,137,0,36,241,389,449,173,413],[1,14,50,960,1472,2433,4166,50,123200,1966400,2099457,14,14,4102,7,4194322,8650770,19,1916928,2115585,788481]),
([pw0,pw1,pw2,pw521,pw3,pw4,pw5],[52,73,149,5,65,28,3,153,24,40,36,241,389,89,421,273,449],[7,25,480,672,7296,1664,7,7,7,3075,1539,553,553,9225,1545,1,5152,1568,544,17952,99840]),
([pw465,pw0,pw1,pw2,pw3,pw4,pw5],[8,60,32,73,96,20,209,16,3,205,5,12,137,397,0,36,389,241,449,537,17,297,144,521,509,565,413,557],[1,126,1938,14354,245778,786435,3145754,3147282,1054738,229394,786435,4196104,8394824,229384,17039369,33562112,67207680,134480385,169984,6145,98305]),
([pw0,pw349,pw1,pw2,pw3,pw4,pw5],[32,3,153,24,73,364,65,5,17,12,421,521,36,241,389,537,509,205,413,557,273],[15,23,486,3844,28676,102404,513,131107,545,20481,4129,83,529,20497,4113,1632,274528,528480,3584,3584,1093632]),
([pw354,pw0,pw1,pw2,pw3,pw4,pw5],[3,17,24,76,153,73,32,20,364,149,8,12,421,36,361,241,557,65,5,521,389,509,413],[31,1001,1032,6408,57352,66824,819,393243,530450,1073154,2163722,394024,6944,1073440,66856,137224,4218888,197896,14336,7176,25608])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def ptopD8 : List StD := [
([pw0,pw1,pw244,pw3,pw12,pw4,pw5],[52,73,132,421,136,17,69,117,257,481,13,140,25,24,173,200,285,241,184,449,509,273],[7,1,60,212,304,560,7,15,1031,7,7,6156,10372,247808,1853440,1,98316,786444,98436,786564,2457600]),
([pw0,pw1,pw244,pw3,pw4,pw5,pw330],[52,73,88,92,17,96,181,257,13,140,477,184,137,397,3,164,285,241,45,557,4,324,117],[7,1,120,184,52,172,7,7,7,39,263,32256,230912,786948,1049100,112640,2625540,4200452,98308,98308,1]),
([pw0,pw1,pw2,pw244,pw3,pw356,pw4,pw5],[73,17,136,132,261,257,481,401,593,137,421,140,332,200,413,184,557,449,241,585],[31,38,38,14,38,38,70,137,137,13,269,137,265,4,1540,6148,26624,100352,2564,6148,26624,100352,2052,1540,164356,270340,557060,581632]),
([pw329,pw0,pw1,pw2,pw244,pw3,pw4,pw5],[17,24,377,140,73,32,401,52,132,241,104,361,116,449,80,509,88,212,481,497,421,3,413,117,557,100,68,152,137,565,585,573],[15,240,264,264,8,7680,122880,131081,13,13,13,13,270345,131352,131352,131152,131408,696592,264,1179912,14680072,27262984,1048840,39845896,201334792,269617920,538091776,3221234176]),
([pw0,pw1,pw2,pw244,pw3,pw4,pw5,pw357],[73,17,96,88,261,257,181,401,137,117,421,184,241,413,164,449,557,397,68,140,212],[31,38,38,70,38,14,38,137,137,137,137,13,141,4,3840,29184,98820,2052,395520,28672,557060,2052,7424,98564,1181700,20484,20484,524292]),
([pw0,pw1,pw2,pw244,pw3,pw4,pw5,pw335],[73,17,96,88,261,257,181,401,521,117,565,132,241,413,164,509,557,52,364,140,3,429,137,449],[31,38,38,70,38,14,14,137,137,137,137,13,13,4,3840,29184,98820,393732,3328,28672,98308,1572868,22784,2099204,4196356,20484,20484,8388612]),
([pw268,pw0,pw1,pw2,pw244,pw3,pw4,pw5],[17,24,181,96,52,32,184,137,509,261,257,49,465,73,401,521,565,241,117,413,164,449,501],[15,56,88,72,200,72,264,585,1033,1033,13,1033,6153,24640,24640,24640,24640,8264,8,98368,1966080,72,98368,1703936,72,1212480,6291528,72]),
([pw0,pw1,pw2,pw358,pw3,pw4,pw5],[132,453,73,120,173,205,100,389,136,257,17,457,341,25,421,425,569,137,68,585,449,156],[7,56,9,9,1984,2816,7,7,259,4227,7,73,24585,32792,65560,147457,9,9,9,9,3932352]),
([pw247,pw0,pw1,pw2,pw12,pw4,pw5],[28,12,421,16,120,397,565,132,453,73,173,205,100,389,136,257,17,457,341,425,569,68,585,449,156],[7,7,13,49,69,69,896,3088,144,126976,180224,656,656,270720,896,1,525328,1049616,144,144,31469568]),
([pw247,pw0,pw1,pw2,pw4,pw5,pw335],[28,521,545,565,605,4,68,397,80,73,88,453,92,257,96,17,341,100,241,156,413,509,557,137,180,5],[7,7,11,19,35,193,3840,61440,61440,24640,28736,3840,67328,1600,1856,1966080,6291520,58720320,917568,917568,1]),
([pw359,pw0,pw1,pw2,pw3,pw4,pw5],[120,12,20,32,173,5,56,361,0,8,4,132,453,73,205,136,257,17,457,341,25,117,425,569,180,449,585],[7,11,57,11,449,1537,14336,16401,2049,229504,360448,10257,34817,530560,14336,3145745,4194321,8388625,2177,2049,117440640]),
([pw360,pw0,pw1,pw2,pw3,pw4,pw5],[124,20,28,32,117,5,0,56,241,4,8,132,73,128,149,65,421,137,136,17,196,237,176,449,465,93,489,89,45,273],[7,11,57,13,449,1537,30720,32785,196609,3932416,30146560,49,200705,34617600,79706112,196625,135266321,272629777,196865,12648449,542114048]),
([pw30,pw19,pw0,pw1,pw2,pw3,pw4,pw5,pw361],[28,124,17,377,73,401,569,521,241,361,128,509,80,149,117,5,285,68,40,132,152,481,421,161,89,477,573],[3,12,48,64,128,768,3072,4096,1024,8192,49154,3,65792,395264,1572866,1044,12,12,12,2099204,12,48,48,48,3088,48,12583936,16793856,33572864,34095104,768,3072,525312,67111168,768,1024]),
([pw362,pw0,pw1,pw2,pw3,pw4,pw5],[72,8,20,32,477,5,12,28,56,413,0,80,73,88,149,493,92,17,96,153,257,341,569,609,45,117,164,241],[7,11,57,193,1793,11,30720,32785,983040,1507840,8193,12305,30720,2112000,270337,4194321,8389137,50331665,201327104,8193,8193]),
([pw19,pw0,pw1,pw2,pw363,pw3,pw4,pw5],[88,96,153,149,192,117,3,40,28,164,285,449,557,181,17,209,73,569,89,413],[7,9,49,81,385,1537,6161,19,50,8210,24578,1538,19,49,98321,17,17,6147,131120,131120,262704,49,1,524816,6161,525824,17,17]),
([pw364,pw0,pw1,pw2,pw3,pw4,pw5],[88,20,8,73,209,16,3,5,24,4,0,56,241,96,261,17,257,181,401,132,137,565,164,413,449,557],[7,27,225,769,7169,261,24585,106624,172032,110592,40961,262153,25,262153,8201,3670144,12587136,50331777,5771264,1572865,4198401]),
([pw354,pw19,pw0,pw1,pw2,pw3,pw4,pw5],[88,76,152,3,17,24,377,60,401,73,421,52,521,80,241,104,361,116,557,509,96,153,149,364,117,12,180,164,285,40,132,89],[15,240,769,1,15360,245760,788481,3145729,4194305,25165827,100663301,402653185,537133059,9437441,1048656,5200,1065040,786449,769,769,769,1310977,1098912768,2306883584,786433,87040,1074004993,134496257]),
([pw0,pw365,pw17,pw2,pw3,pw4,pw5],[32,149,20,60,153,144,9,261,88,537,209,13,112,245,453,425,73,12,329,489,5,45,361,241,80,449,273],[7,1,120,152,152,792,1033,2083,7,12291,16899,32808,196616,331784,590088,1081376,36896,2130208,12587008,50332416,71308032]),
([pw0,pw1,pw43,pw2,pw14,pw4,pw5],[60,29,153,17,269,581,28,137,521,120,5,128,73,132,57,421,341,453,144,25,397,112,253,65,89,477,565,573,241],[7,7,7,9,19,35,448,32256,38913,79872,145408,786624,1048641,6291648,448,8421889,19138048,33818112,69238785,67141633,404750336]),
([pw366,pw0,pw17,pw2,pw3,pw4,pw5],[32,149,20,60,73,128,129,297,136,133,401,209,421,549,104,241,112,413,80,449,88,557,273],[7,25,35,99,35,35,1,392,552,392,392,3080,4392,3080,9224,288,245760,3932160,288,288,5357568]),
([pw0,pw367,pw17,pw2,pw3,pw4,pw5],[32,149,20,60,261,92,457,497,144,13,453,112,245,401,57,73,557,173,5,89,361,241,449,273],[7,1,56,56,56,120,137,771,1027,6147,1059,24840,40968,43016,65576,393472,526592,65824,3147776,4259872,8390688]),
([pw0,pw349,pw17,pw2,pw3,pw4,pw5],[32,149,24,96,153,364,5,9,261,132,521,128,172,241,537,509,457,205,116,389,425,73,421,341,557,348,668],[7,1,248,3864,12568,114712,9,131107,35,786435,43,1048672,6292000,10489888,18874408,131680,1048672,16777320,4730368,4214312,100691976]),
([pw0,pw1,pw368,pw2,pw3,pw4,pw5],[88,73,84,149,96,17,348,153,364,5,132,521,128,172,241,257,537,509,341,173,676,361,89,421],[15,113,944,7344,57392,196709,15,15,15,278791,339,525056,260,3170304,325,526080,5243648,837,3169280,8459333,1130565]),
([pw0,pw1,pw369,pw2,pw3,pw4,pw5],[88,73,84,96,153,17,257,457,401,509,537,16,364,5,0,56,241,173,337,128,521,132,605,429,172],[63,57,56,56,88,157,15,263,263,263,1547,14344,4108,114696,1549,143360,274432,12813,7929856,8913421,16843277]),
([pw0,pw1,pw334,pw36,pw3,pw4,pw5],[52,73,149,60,17,181,321,481,597,341,453,144,173,5,112,389,477,65,205,493,241,680,449,3,509,521,573],[7,1,1,56,88,152,7,267,7,515,1027,1,14336,55296,71680,393224,49160,655368,1097728,65011712,67158016]),
([pw0,pw1,pw2,pw334,pw3,pw4,pw5,pw335],[73,17,149,88,65,257,3,364,545,521,181,389,241,537,509,140,60,205,337,28,12,36,64,144,148,605,132,429,137,164,449],[15,242,162,1794,6178,24586,98314,13,13,13,137,16521,13,8,131216,262288,152,152,1573632,6297600,24584,25165832,33560832,201334792,335544328,536881160,536875016,1073741832]),
([pw268,pw0,pw1,pw2,pw334,pw3,pw4,pw5],[17,88,60,181,140,73,149,184,137,509,65,257,3,212,389,241,441,337,36,64,501],[31,98,146,130,386,130,514,99,15361,10241,8329,51201,131,98,98,98,8226,73762,2,9344,140288,130,8320,835584,130,8320,1056898,130]),
([pw0,pw1,pw2,pw370,pw3,pw4,pw5],[32,149,73,120,60,17,205,16,29,421,100,389,257,112,80,537,457,68,341,77,208,413,557,521,273],[7,120,184,792,15408,245808,7,7,7,264195,163843,1,524872,3145800,4325448,1049224,1051656,180232,10760,8421896,18009088]),
([pw0,pw371,pw1,pw2,pw14,pw4,pw5],[28,137,12,60,181,128,73,377,525,521,132,421,149,341,453,397,144,65,337,477,545,100,241,68,585,449,112],[7,120,152,1,152,280,515,1027,2057,1027,515,5216,1128,9312,17504,229384,458752,720896,1081352,1081352,132120576]),
([pw0,pw1,pw2,pw372,pw3,pw4,pw5],[132,149,73,120,173,425,100,389,144,257,148,17,457,341,453,25,421,569,397,68,585,449,156],[7,56,9,9,4032,5888,7,11,7,8323,16387,73,98313,56,131096,327937,9,9,9,9,7864512]),
([pw0,pw371,pw1,pw2,pw12,pw4,pw5],[28,52,421,132,149,73,120,173,77,100,389,144,257,136,17,457,341,453,425,569,68,585,449,156],[7,56,448,72,32256,47104,7,7,2057,13,13,56,88,66584,131096,1,262336,524480,72,72,15730176]),
([pw34,pw0,pw1,pw2,pw36,pw3,pw4,pw5,pw335],[192,73,5,3,76,80,521,545,241,389,509,537,60,148,17,149,121,265,13,364,684,65,173,413,477,140,429,573,449],[1,2,28,49,192,768,3088,12304,114688,147460,1,192,768,3072,12288,294916,557088,192,768,3072,1089536,2097152,4194372,8388868,16778244,4718596,192,768,3104,33558528,832,67109952,1,134219008,768,268435456]),
([pw268,pw34,pw0,pw1,pw2,pw36,pw3,pw4,pw5],[60,148,453,149,5,173,88,140,137,241,361,509,192,73,3,76,521,545,389,449,585,17,121,265,13,128,65,413,45,501],[3,3,14,48,193,256,1536,2048,4096,8192,49168,36928,196608,262656,1605632,6291460,10485776,4096,196608,262656,1572864,16777236,33554500,12,262660,12,67108864,48,134218256,268959760,196608,262656,1572928,1536,537460736,1573376]),
([pw34,pw0,pw1,pw2,pw373,pw3,pw4,pw5],[60,297,88,73,144,65,92,148,40,28,112,389,585,149,453,173,89,361,509,241],[3,13,49,193,769,3073,4165,69,49,193,65,65,4101,52,196,24580,3076,20548,32880,32816,66608,52,1,132160,266308,527360,68,68]),
([pw34,pw0,pw374,pw2,pw3,pw4,pw5],[20,32,52,65,401,593,549,13,140,181,17,257,481,149,453,116,245,205,337,493,104,241,132,397,200,137,80,449,521,88,585],[1,1,14,50,82,50,1,140,1792,2816,4864,2,24832,106752,24832,131084,262156,524300,66060288,1019215872,1815085056]),
([pw34,pw0,pw2,pw10,pw3,pw4,pw5,pw335],[84,13,72,65,73,88,364,401,209,341,497,92,257,149,545,521,181,389,241,537,509,140,144,205,337,453,164,3,128,429],[1,30,224,304,560,1073,304,74,14401,118784,462848,1576993,6295584,32,8388674,16777282,99,98,33595457,67379265,8288,134217825,67518464,805830689,1,67764257,67371040,268435488]),
([pw268,pw34,pw0,pw2,pw10,pw3,pw4,pw5],[73,32,209,88,144,140,181,184,137,509,84,72,65,128,401,341,105,449,257,13,92,149,389,241,413,337,453,164,501],[15,120,152,136,392,136,520,1032,6153,24584,13,32777,196617,790592,3416128,8384,12845120,200,8,12416,54530048,136,67118208,144712704,136,8320,268443784,136]),
([pw0,pw375,pw1,pw2,pw3,pw4,pw5],[120,20,12,132,149,593,173,65,136,17,144,257,457,397,337,493,180,449,585],[7,56,193,9,3840,5888,27,137,9221,9,9,137,25,56,56,137,16449,32833,9,9,458752]),
([pw376,pw0,pw1,pw2,pw3,pw4,pw5],[124,24,20,5,65,421,397,0,56,241,4,8,132,401,128,149,144,17,148,257,481,453,337,477,545,176,585,449],[7,7,25,97,897,3073,61440,25,196641,983552,1507328,25,97,61952,2387968,105,4194313,8388617,16777761,16777249,234881536]),
([pw30,pw34,pw0,pw1,pw2,pw3,pw4,pw5,pw361],[28,124,17,377,453,149,569,521,241,361,128,509,80,73,65,5,389,537,132,152,421,161,89,477,573],[3,12,48,64,128,768,3072,4096,1024,8192,49154,3,65792,133120,786434,1044,12,12,12,133124,12,33808,48,1296,48,263184,3146752,4210944,8407040,8667136,768,3072,263168,16779520,768,1024]),
([pw0,pw377,pw1,pw2,pw3,pw4,pw5],[72,20,8,80,401,88,149,477,65,96,17,144,153,257,453,537,205,337,164,361,241],[7,120,385,7680,11776,33,16395,297,33,33,34821,297,16440,120,16417,65665,131201,289,1835008,33,33]),
([pw34,pw0,pw1,pw2,pw363,pw3,pw4,pw5],[88,128,73,192,65,148,397,164,389,585,449,5,60,137,241,149,441,569,89,413,509],[3,5,25,35,67,385,1545,3,2072,4130,8258,16768,9,3,35,11,3,98307,131082,131082,262296,25,1,524418,1048579,194,11,9]),
([pw0,pw378,pw1,pw2,pw3,pw4,pw5],[88,8,20,149,73,96,257,148,17,181,449,453,132,397,565,164,413,241,509,557],[7,25,480,736,480,193,27,129,129,129,1155,25,25,137,2185,28672,229376,786433,28672,12289,98305]),
([pw354,pw34,pw0,pw1,pw2,pw3,pw4,pw5],[88,76,152,148,17,377,60,149,364,421,80,241,104,361,116,73,65,12,545,164,389,509,537,5,521,132,89],[15,120,393,1,1792,30720,257,257,32769,65795,393221,1572865,6291459,385,8454448,16777776,1574960,6291473,65921,385,385,2097537,33620736,67698944,65793,272896,35652097,526337]),
([pw0,pw251,pw2,pw3,pw4,pw5,pw335],[92,257,84,149,17,96,76,13,153,425,120,521,124,73,160,93,241,509,537,364,429],[63,227,291,291,99,99,716,15372,114700,393261,532524,704,704,225,224,89088,1053729,1,81953,81952,1056]),
([pw268,pw0,pw251,pw2,pw3,pw4,pw5],[76,96,153,20,128,149,205,137,116,361,48,509,13,257,5,73,341,337,605,521,501,449,585],[7,57,67,145,1793,2049,54,4099,22,8710,7,16401,32816,66096,49,81,131137,67,786960,1048593,6291969]),
([pw379,pw0,pw2,pw3,pw4,pw5,pw335],[80,73,88,149,341,405,453,72,65,76,5,92,17,96,153,257,173,337,120,521,124,605,429,509,160,241],[15,15,15,23,103,15,1920,30720,47104,12293,14340,66432,131968,773,900,3932160,5505029,1,58720261,50331652,262148]),
([pw268,pw379,pw0,pw2,pw3,pw4,pw5],[76,52,32,96,153,173,72,116,361,48,509,17,65,80,73,88,149,341,257,337,120,605,521,501,449,585],[7,25,43,65,897,1025,2072,4129,122880,188672,49153,41,2072,262424,25,4129,524321,41,7340288,9437185,50331905]),
([pw380,pw0,pw1,pw2,pw4,pw5,pw335],[28,521,545,565,605,4,68,137,92,17,96,153,257,72,5,76,65,100,241,128,341,156,509,364,89],[7,7,11,19,35,193,3840,3840,5888,1600,1856,122880,4063232,5767232,9961536,18931712,49216,57408,2490432,2490432,1]),
([pw380,pw0,pw1,pw2,pw4,pw5,pw381],[28,521,545,565,605,68,509,137,92,17,96,153,257,72,5,76,65,100,241,128,341,156,364,89],[7,7,11,19,97,161,3840,3840,5888,1632,1824,122880,4063232,1572960,5767200,10543104,49248,57376,2359392,2490400,1]),
([pw0,pw1,pw2,pw3,pw382,pw5,pw335],[92,37,96,153,381,457,72,425,76,65,120,521,124,545,160,285,241,509,537,364,73,429],[15,15,15,15,55,15,960,15360,114688,393221,1572868,960,960,389,836,56320,2102277,1,49157,49156,1028]),
([pw268,pw0,pw1,pw2,pw3,pw382,pw5],[76,96,153,52,176,205,137,509,37,425,521,545,160,285,241,65,449,501],[7,25,43,81,17,129,262,259,278,262,7,545,3088,28672,17,32817,545,35,13328,196625,17]),
([pw383,pw0,pw1,pw2,pw3,pw4,pw5],[76,24,8,32,20,5,205,4,0,56,241,92,17,96,153,257,120,521,124,545,160,285,509,537,89,429],[7,25,101,131,1793,7,30720,97,30720,48128,12289,97,983040,3146752,12582913,97,17825825,8225,1508352,33882113,1049601]),
([pw0,pw365,pw1,pw2,pw36,pw3,pw4,pw5],[24,17,60,212,73,265,181,321,481,5,117,144,32,421,137,241,48,285,112,509,72,449,76,593,124,65,173,413,477,216,521,573],[15,30,46,12,70,134,262,4,3592,4108,24585,491520,7864320,3600,8392716,16801808,426008,11010072,33556484,67119616,134482440,268438024,553648140,537133060,536870916,17063944,1076371464,2147778560]),
([pw345,pw0,pw1,pw36,pw3,pw4,pw5],[60,17,124,69,144,5,117,65,0,173,112,413,477,332,132,401,440,421,137,285,176,509,216,453,444,325,485,449,273],[15,116,405,564,3124,4148,8195,5,8199,3075,8195,49281,491524,560128,32538624,65669,33555585,83886209,199684,151191556,285215744]),
([pw0,pw1,pw2,pw84,pw14,pw4,pw5],[60,181,128,73,269,581,120,5,140,137,521,216,341,453,25,65,337,477,421,112,253,545,385,397,573,241],[15,19,23,5,19,35,460,1804,2061,6156,10252,17348,33089,65984,131520,262401,1573636,1796,6815745,10485761,50855936]),
([pw366,pw0,pw1,pw2,pw36,pw3,pw4,pw5],[17,24,60,136,144,117,52,112,285,76,449,72,257,165,5,32,128,421,137,241,509,209,549,413,477,389,80,68,537,521,573],[15,4,56,76,74,392,3592,13,13,4100,8205,13,13,16432,98308,393224,524672,7341056,12,56,8388784,16777264,65548,33554564,469762052,392,537003016,1073742208]),
([pw0,pw1,pw384,pw36,pw3,pw4,pw5],[60,17,136,69,169,165,5,117,425,205,421,137,112,285,241,188,449,509,0,77,537,273],[7,15,17,39,7,7,196,769,3076,28672,229376,262149,3140,12356,98372,524293,769,1081601,3076,99332,2142208]),
([pw32,pw0,pw82,pw1,pw2,pw3,pw4,pw5],[60,181,132,136,401,140,425,112,389,88,80,65,137,285,68,40,117,521,549,477,573],[3,13,21,97,37,385,1537,13,21,97,37,33,33,1,2092,4140,8324,49156,65588,135188,148,262164,65572,224,524384,8324,135172,1048960]),
([pw0,pw367,pw1,pw2,pw36,pw3,pw4,pw5],[24,17,60,92,257,465,144,117,52,124,137,120,112,285,5,32,84,401,421,73,241,449,509,173,413,45,68,397,132,389,8,273],[15,14,14,20,14,14,46,4,200,268,3592,12296,265,16576,229380,918528,1191936,6291464,12,8650944,16781504,33554504,469762052,536875012,1073741836,17052672,6291464,2147487752]),
([pw385,pw0,pw1,pw36,pw3,pw4,pw5],[60,17,76,69,92,117,5,0,173,112,241,449,45,465,425,65,180,421,188,137,285,509,485,273],[15,116,149,308,1588,6196,19,5,19,19,8199,49153,983040,1050112,2099220,49153,49665,4194325,394752,2361364,8389140]),
([pw0,pw1,pw2,pw36,pw373,pw3,pw4,pw5],[73,17,149,60,92,257,181,465,5,117,88,401,128,52,212,441,173,112,413,45,124,397,389,585,361,509],[31,26,40,90,26,26,154,773,7177,24597,16389,18433,49169,24,90128,82176,409856,540688,1048600,2117640,4325384,8388632,8,16908304,34619408,409600,33570832,8519696]),
([pw336,pw0,pw1,pw2,pw36,pw3,pw4,pw5],[17,24,181,60,73,401,52,5,173,120,397,116,361,48,76,509,72,453,212,140,321,481,65,3,413,477,137,100,68,80,180,585],[15,120,960,584,1536,14848,115200,393233,524929,512,524805,1576961,2654209,262832,262192,262704,266288,426000,4719104,896,25166464,33555072,67633664,143134720,805863424,75502080,1140883968,3221262336]),
([pw184,pw0,pw82,pw1,pw2,pw3,pw4,pw5],[60,377,140,488,32,425,112,389,88,80,17,297,69,5,117,124,137,28,285,68,152,449,421,593,401,241,509,173,413,477,521,573],[3,13,25,37,5,193,769,3077,5,5125,5,5,5,1,24580,229380,262212,3670020,24580,29425664,41943232,94371840,138420228,268435524,536879108,262336,1143013376,2147483840]),
([pw0,pw82,pw1,pw2,pw36,pw3,pw4,pw5,pw335],[17,76,96,364,181,37,309,481,73,521,124,180,241,285,509,176,140,3,5,117,80,684,425,173,413,477,545,389,537,60,429,137,573,449],[7,9,9,8,17,97,129,17,256,6,8,3584,12288,49154,196610,786432,1048584,520,4104,16392,2097160,4194304,8650760,17039368,33816584,8650760,67109376,134221824,269500416,536936448,16781824,1073758720,2147483648,4294987776,16781312,8589934592]),
([pw268,pw0,pw82,pw1,pw2,pw36,pw3,pw4,pw5],[17,181,76,176,549,401,5,173,88,60,140,137,241,361,509,96,212,309,49,465,73,285,117,521,541,425,413,45,545,389,585,449,501],[3,12,48,192,1792,2048,12288,16384,32773,65553,65601,65536,3,135169,786433,1048576,32836,65536,65544,2101248,12,4194384,65808,25165840,48,48,33554432,192,67113024,134283328,276889600,536875008,3221225728,12288,4303421440,3221229568]),
([pw183,pw0,pw1,pw2,pw36,pw3,pw4,pw5,pw335],[192,401,3,521,545,241,389,509,537,60,76,216,17,149,73,69,5,80,364,425,173,413,477,429,573,449],[1,2,4,1,24,96,384,3584,28672,102400,1,24,96,384,2560,24576,401408,24,96,384,26624,524288,1114120,2162720,4259968,1116160,24,96,384,2560,104,8388744,1,16777376,96,33554432]),
([pw268,pw183,pw0,pw1,pw2,pw36,pw3,pw4,pw5],[60,176,76,17,181,73,149,5,173,88,140,137,241,361,509,192,401,3,521,545,389,69,49,465,212,441,425,413,45,585,449,501],[7,25,96,384,1537,2048,12288,16384,32768,65536,131072,32768,786434,1052672,6,104,2097288,32768,24,1052680,12582920,96,16777760,96,1052704,50331680,67108864,384,134221952,285212800,786432,1052672,1610613248,12288,2164523008,1610616832]),
([pw0,pw83,pw1,pw66,pw2,pw36,pw3,pw4,pw5],[120,216,73,453,468,521,241,449,149,3,5,60,389,537,593,413,557,25,273],[3,12,1,17,1,35,66,130,256,2,1538,2051,2,4097,8193,14,5,16388,35,70,14,1537,1,3,32832,65664,16,132098,33793,66561,35,66,130,4129,8225,262336]),
([pw83,pw1,pw66,pw2,pw36,pw3,pw4,pw5],[120,212,149,216,5,3,144,153,389,112,180,537,73,453,593,81,421,17,521,413,321,557,468,585],[7,9,113,201,9,801,3073,12290,4115,20482,98307,20482,5122,131121,1,262153,1704192,2231296,4194305,327697,524337,2098193,65673,524712,2098312,327937,3073,8391936]),
([pw1,pw66,pw2,pw36,pw3,pw4,pw5],[60,17,24,120,5,144,117,32,153,421,212,137,149,112,93,241,488,453,309,481,65,173,413,477,28,389,68,537,180,521,273],[7,120,385,7688,62464,201728,65547,139,7,270339,524291,1048609,2097720,4202552,8388664,16777481,33562881,201326849,4205064,939524616,1342218240]),
([pw307,pw83,pw1,pw2,pw36,pw3,pw4,pw5],[216,120,60,17,453,73,29,321,481,209,3,5,153,116,389,108,96,537,92,593,421,65,413,477,68,521,585,573],[7,57,11,3,67,137,265,515,3075,4099,1,57346,458754,35,528401,1048579,524305,49,2097153,1050627,4197377,8390657,4099,4199425,16781313,34619394,34734082,201474048]),
([pw0,pw83,pw1,pw36,pw91,pw3,pw4,pw5],[120,3,216,73,17,453,52,5,521,165,241,321,449,481,209,205,389,688,180,537,593],[7,120,1,149,773,3092,12308,16449,32775,5,5,196611,786433,1048648,77,325,132172,108,32901,33029,230404,299012,69,196737,786561,196865,786689,398336]),
([pw0,pw1,pw36,pw91,pw3,pw4,pw5],[52,73,453,120,24,3,5,17,216,692,521,165,688,241,309,180,449,465,696,593,205,77,389,537,477,273],[7,1,504,3976,29056,491904,524291,7,1539,12291,7,1048952,3147528,4206848,9797888,1,4206664,25264200,4208136,8717832,33599488]),
([pw0,pw83,pw1,pw2,pw36,pw161,pw3,pw4,pw5],[17,60,216,453,73,69,5,153,120,29,37,49,149,3,389,537,593,421,205,413,45,449,589,585],[7,25,97,128,256,517,1029,2053,4096,8260,6,4,4,16640,33024,24,65544,65548,131076,65548,28,262144,8192,131140,524356,1048644,256,131332,524292,2097156,4,4210688,8421376,16640,33024,4243456]),
([pw0,pw83,pw1,pw2,pw161,pw3,pw4,pw5],[120,60,216,153,73,17,453,5,205,521,241,321,449,481,212,149,3,389,112,180,537,593,81,65,413,45,589,44,585,421],[15,120,417,1,525,3084,12300,49153,385,5,5,458753,1572865,401,2113556,4194821,2114580,16468,8454145,385,16842881,34078849,517,201393152,268963840,537002497,1573377,268964864]),
([pw0,pw1,pw2,pw161,pw3,pw4,pw5],[60,17,153,257,321,481,120,5,144,117,12,20,421,212,137,149,112,93,241,488,453,65,173,413,477,589,4,8,180,509,521],[7,7,9,7,19,35,960,3073,61504,499712,1613824,2097409,4198848,8454592,16777664,3137,33619969,201326593,8474688,1879052352,33882112]),
([pw308,pw0,pw83,pw1,pw2,pw3,pw4,pw5],[153,28,17,52,216,120,60,593,73,5,65,421,3,241,44,68,40,321,481,401,205,389,700,180,537,413,45,521,585],[15,112,408,1554,2098,28688,98320,21,21,21,21,139281,262161,524336,1049136,16,6295584,25165856,304,2096,400,400,2608,33559056,75498000,136316960,25167904,281026560]),
([pw308,pw0,pw1,pw2,pw3,pw4,pw5],[140,153,17,20,12,205,5,56,241,0,8,4,321,481,120,421,212,397,401,216,73,453,3,413,477,521,700,180,585,449,704],[7,25,97,25,897,3073,7,7,7,4355,8195,97,507904,1900800,2949120,97,12582945,16777249,109101312,100712448,2080375040]),
([pw386,pw1,pw2,pw36,pw3,pw4,pw5],[60,17,24,16,181,321,481,124,5,144,69,32,297,212,421,137,149,401,453,65,112,413,477,133,389,457,521,573],[7,11,11,19,35,67,1920,6145,57472,204800,335872,524801,25472,3146624,4195200,8392833,17829889,33558529,57472,67133568,137363456]),
([pw0,pw1,pw2,pw387,pw3,pw4,pw5],[60,17,297,153,181,457,124,5,128,73,401,453,136,421,137,112,413,241,144,477,397,12,389,4,8,521,573],[7,7,9,19,7,35,960,1281,1856,1792,2816,4097,25024,229568,786624,3146049,4227073,25165825,24896,33562944,67207168]),
([pw0,pw1,pw2,pw388,pw3,pw4,pw5],[128,209,149,124,65,140,5,17,29,297,457,421,129,401,549,337,477,56,241,0,8,4,521,176,449,444,585],[7,120,169,289,672,1184,7,35,6147,8195,16387,105,2081,32824,65592,2081,917505,3145729,4196353,4196353,126091264]),
([pw264,pw0,pw1,pw2,pw84,pw4,pw5],[124,397,128,60,17,73,212,5,137,545,209,149,65,521,100,389,204,241,257,68,449,445,176,129,393,509,25,337,45,421,585],[31,36,199,260,519,519,3092,4305,8197,507920,7929872,197,8397828,16909316,34079748,67117125,134217921,268959937,536879108,37756932,1079558144]),
([pw389,pw1,pw2,pw36,pw3,pw4,pw5],[60,17,24,16,181,321,481,76,5,144,69,32,153,180,421,192,149,593,65,173,112,413,45,297,445,509,449,273],[7,11,11,19,35,67,1920,6145,122880,229376,229504,262657,541568,3146624,4227968,8400897,9441281,16781441,3170304,100720768,135299200]),
([pw0,pw1,pw2,pw390,pw3,pw4,pw5],[60,17,153,257,297,481,76,5,84,73,549,341,96,144,173,337,45,28,12,0,56,589,537,8,112,361,509,449],[7,7,9,7,19,35,960,1281,1792,2816,1856,4097,24768,41152,74176,393217,3670017,12583233,52428800,201326912,18874688]),
([pw0,pw1,pw2,pw391,pw3,pw4,pw5],[84,401,453,76,65,140,5,17,153,297,49,173,337,45,12,28,56,241,0,509,160,704,397,180,137,585],[7,120,169,416,672,1057,99,7,7,7,7,105,2104,4152,8225,49153,458753,524321,32636928,34078721,34078721]),
([pw0,pw1,pw2,pw36,pw392,pw3,pw4,pw5],[73,17,453,192,96,60,181,137,241,321,449,557,549,341,5,173,708,413,140,397,28,40,389,585],[15,26,8,122,210,786,3082,13,4105,4105,4105,8457,13,24,49160,49160,213000,3080,262184,3670144,4260096,8389640,24,196616,3080,196992,3080,8455176]),
([pw393,pw1,pw2,pw36,pw3,pw4,pw5],[60,52,17,321,481,120,117,5,257,297,137,421,112,285,241,176,509,180,449,1,413,45,133,389],[7,7,7,7,13,21,224,769,3104,28672,491520,524321,3168,1052768,2228320,4194337,8392961,131329,3104,197664,143360]),
([pw0,pw1,pw2,pw84,pw12,pw4,pw5],[136,17,128,149,73,140,77,21,29,153,257,457,173,52,421,120,212,341,453,712,413,68,557,137,565,397,273],[63,227,807,1059,1059,2083,4156,24636,98317,196620,327692,4197,4,1572960,6291552,8421408,540708,20987940,1605633,39878657,70778880]),
([pw139,pw1,pw2,pw36,pw3,pw4,pw5],[60,17,52,181,321,481,120,5,124,117,377,153,421,137,112,285,241,176,449,509,65,413,45,269,505,273],[7,7,7,11,19,35,960,3073,12608,114688,917504,1048833,12736,2113984,4325824,8388929,3073,16909313,12608,397632,33734656]),
([pw353,pw1,pw2,pw36,pw3,pw4,pw5],[60,52,17,181,321,72,117,5,257,153,176,421,137,112,285,241,449,509,1,413,45,445,273],[7,7,7,13,21,7,224,769,7168,57344,196640,262177,3168,532576,1114208,769,769,2097185,7168,197664,4202528]),
([pw0,pw1,pw2,pw36,pw363,pw3,pw4,pw5],[73,17,149,192,96,60,181,137,241,321,449,557,401,209,5,260,173,120,25,716,413,136,397,389,585],[15,26,8,122,210,786,3082,13,4105,8201,13,4361,3081,24,114696,409608,1589256,3080,2097192,4325504,8913152,16778248,24,1572872,3080,1704320,3080,17302536]),
([pw0,pw1,pw2,pw84,pw394,pw4,pw5],[60,17,140,69,153,257,77,5,137,421,216,593,73,65,112,413,477,3,521,545,385,397,573],[7,15,23,33,7,7,196,772,3073,7168,7168,836,8197,49220,65604,131077,772,262404,1589249,2621441,4243456]),
([pw0,pw395,pw1,pw2,pw36,pw3,pw4,pw5],[24,17,60,212,593,69,181,321,481,5,117,144,32,421,137,124,241,48,285,112,509,72,449,76,176,205,173,413,477,216,521,573],[15,30,46,12,70,134,262,4,3592,4108,57352,983040,15728640,3600,4124,57360,851992,22020120,33556484,67119616,134744584,268438024,536903692,537395204,553648132,57352,1079025672,2148073472]),
([pw396,pw184,pw0,pw1,pw2,pw4,pw5],[60,140,3,133,17,137,421,521,153,397,132,393,205,545,117,5,112,285,241,176,509,180,449,213,477,273],[7,27,98,98,98,162,257,3585,4099,8705,8705,3,27,3,3,49154,458752,7864320,8470530,16793602,35848192]),
([pw0,pw397,pw1,pw2,pw36,pw3,pw4,pw5],[24,17,60,212,165,321,481,5,117,32,397,421,137,48,112,241,72,509,76,401,549,65,413,477,132,389,80,68,537,521,573],[15,14,14,12,30,38,70,4,392,524,7176,57352,458760,392,524,6152,49160,1703944,2097164,6280,4210824,8388744,16777228,33570820,469762052,6152,537004040,1073790976]),
([pw0,pw398,pw1,pw2,pw36,pw3,pw4,pw5],[24,17,60,192,401,69,181,321,481,5,117,144,32,397,120,137,124,241,48,285,112,509,449,76,421,180,425,173,413,477,132,389,80,8,273],[15,30,46,12,70,134,262,4,3592,4108,122880,1966080,14680072,3600,4124,50339864,1703960,14680080,67110916,150997512,269486600,536873472,1107304452,2148532228,12893290508,269656064,14688264,17189437448]),
([pw0,pw1,pw2,pw36,pw399,pw3,pw4,pw5],[73,17,149,60,212,181,321,481,401,453,65,5,173,112,413,477,12,397,389,152,585,8,76,509,72],[31,26,24,58,58,74,138,21,281,21,21,273,529,1048,6160,6160,26640,34832,65560,131096,270344,3670024,8,24592,29360144,24592,12714000,5267456]),
([pw0,pw1,pw2,pw36,pw400,pw3,pw4,pw5],[73,17,149,212,96,60,24,137,165,241,321,537,449,481,401,441,5,136,16,25,720,413,140,389,273],[15,26,8,122,410,1554,14338,13,16393,16393,13,16905,32793,24,458760,589960,3211272,1114136,4194344,4194440,5243392,1054736,24,9437192,133176,3145864,2200,17828368]),
([pw0,pw349,pw1,pw2,pw36,pw3,pw4,pw5],[24,17,60,684,364,96,521,181,241,321,537,509,481,3,140,116,389,48,13,109,173,5,720,413,545,68,12,212,421,273],[15,26,50,16,226,802,7170,40,8216,16396,24,229384,24,786456,24,24,24,24,48,3145744,13631504,5242928,117440576,4260096,4197408,4260160,406848624,541066528]),
([pw354,pw0,pw1,pw2,pw36,pw3,pw4,pw5],[17,24,76,60,364,73,173,72,48,116,241,449,149,96,521,181,321,537,509,401,124,421,160,413,557,545,389],[15,52,68,14,148,1796,2068,4145,8197,4,57345,74753,393221,52,524336,4144,525360,52,8196,3145732,12582916,16777236,34619392,71304192,393220,3163136,3276804,4326404]),
([pw0,pw1,pw2,pw401,pw3,pw4,pw5],[96,17,140,297,181,481,65,5,20,32,152,521,124,397,160,241,216,341,453,173,337,101,28,56,361,4,585,509],[15,15,23,23,15,39,196,772,15360,245760,459777,524357,524356,1048644,2097221,4200452,25182212,37748741,15360,67124225,201360385]),
([pw402,pw0,pw1,pw2,pw3,pw4,pw5],[60,153,20,32,96,4,28,56,389,0,17,297,181,481,76,5,144,65,152,421,124,137,112,241,509,449,173,89,45,273],[3,13,17,97,897,113,3073,3073,5121,3329,9217,245760,3932160,12583168,50593808,67747840,138526976,268550160,3932416,52166672,541327632]),
([pw0,pw1,pw2,pw403,pw12,pw4,pw5],[136,297,17,29,165,457,120,205,25,100,241,128,341,204,176,509,453,68,413,433,397,273],[7,7,27,7,7,35,448,65,65,15872,251904,321,577,270528,655552,1048577,65,65,65,65,2237952]),
([pw0,pw83,pw1,pw341,pw2,pw3,pw4,pw5],[120,144,136,153,17,453,468,321,481,205,65,137,3,389,204,180,537,425,148,81,421,241,341,509,413,557,521,585],[15,60,1,85,73,204,332,5,5,1539,2049,28673,98305,100,131585,1835009,6299680,12681248,1537,65,16805888,33652736,1537,131585,33587713,68165633,98305,134275072]),
([pw0,pw1,pw341,pw2,pw3,pw4,pw5],[136,17,144,153,321,481,12,65,425,120,421,137,204,241,148,341,208,188,509,453,180,5,205,413,557,493,521,273],[15,15,15,15,23,39,69,388,3585,126976,2015232,6291588,1605,8458244,17956868,389,388,50331780,3585,67372545,135344128]),
([pw263,pw83,pw1,pw66,pw2,pw3,pw4,pw5],[120,144,136,153,32,453,468,5,3,241,68,205,65,137,389,112,180,537,425,148,81,421,341,509,413,17,321,557,521,585],[15,60,1,193,73,844,1100,5,5,6147,8193,49409,196609,100,264193,3670017,4211232,12779552,6145,65,117441024,167968768,6145,264193,134285313,270548993,196609,537068032]),
([pw263,pw1,pw66,pw2,pw3,pw4,pw5],[136,32,144,153,257,5,28,208,389,68,537,17,65,425,120,421,137,241,188,509,148,453,180,1,309,465,493,521,273],[15,20,36,77,397,1549,2053,12292,114689,131456,8127488,8394756,34821,16779396,37750788,12293,12420,67112964,49537,134267905,272630144]),
([pw404,pw0,pw1,pw2,pw3,pw4,pw5],[128,16,12,209,149,136,397,137,17,297,133,457,421,401,453,124,65,144,337,493,176,449,188,585],[7,25,35,197,33,33,25,800,1185,800,2336,25,4233,8201,16393,33,491520,753664,33,33,15728640]),
([pw263,pw386,pw1,pw2,pw3,pw4,pw5],[124,136,297,32,60,137,133,457,24,17,1,165,321,481,425,144,65,421,112,241,148,401,204,176,509,453,188,101,449,273],[1,14,18,103,134,134,770,1539,2339,4610,8706,114689,131107,8126464,128974848,98339,114689,201375745,131107,335544355,608960512]),
([pw405,pw0,pw1,pw2,pw3,pw4,pw5],[84,16,8,497,149,96,537,449,17,153,297,445,593,76,65,144,205,337,160,241,168,361],[7,25,35,33,33,197,25,800,800,1312,2209,25,25,4105,25,122880,188416,33,3932160,33,33]),
([pw263,pw389,pw1,pw2,pw3,pw4,pw5],[76,92,32,96,153,60,297,449,445,24,17,1,181,321,465,425,144,65,180,421,148,149,188,129,112,241,593,168,509,137,172],[1,30,40,90,90,411,522,3081,5128,9224,17035,229377,16515072,254803968,270532747,229377,229377,98443,592183296,268959883,1107296395]),
([pw263,pw0,pw1,pw2,pw392,pw3,pw4,pw5],[76,73,32,453,84,96,120,5,132,172,241,449,557,192,17,181,149,549,65,425,361],[1,30,224,368,352,1568,6193,8234,16481,32864,32864,1568,6177,8267,204866,139330,9730,6187,786497,794689,524865,4192,1,1049152,4193,1049152,4193,1569]),
([pw263,pw393,pw1,pw2,pw3,pw4,pw5],[120,124,136,297,257,5,137,133,457,1,165,17,113,112,241,204,285,176,509,180,449,33,41],[3,28,37,197,268,268,5,517,3137,5,5,4609,5,122880,1966080,581,2130433,4719105,5,5,581632]),
([pw263,pw139,pw1,pw2,pw3,pw4,pw5],[120,136,377,144,153,5,269,525,17,52,165,321,481,65,169,421,137,112,241,196,285,176,449,509,89,101,273],[1,30,40,79,30,142,776,779,1291,2312,4360,24585,98307,1966080,14680064,24587,17309705,35659785,98307,6848515,70123520]),
([pw263,pw353,pw1,pw2,pw3,pw4,pw5],[72,76,92,257,96,153,5,449,445,1,465,17,113,176,421,137,112,241,168,285,33],[3,60,81,60,60,401,17,533,17,17,3201,4609,57344,983040,17,25089,1311233,657,57344,17,17]),
([pw263,pw0,pw1,pw2,pw363,pw3,pw4,pw5],[72,73,88,149,128,96,5,144,40,172,241,449,557,192,17,181,209,569,65,89,413],[1,30,97,161,304,1568,6177,8234,16417,161,49184,1568,6177,8195,73729,8202,9730,33,393345,393217,524801,6177,33,1049089,6177,1050112,33,33]),
([pw0,pw1,pw2,pw406,pw3,pw4,pw5],[92,17,96,297,153,181,449,445,76,5,144,65,136,521,137,160,241,168,285,509,89,172],[15,15,55,39,15,199,3840,1028,28672,491520,524357,1796,5888,1181440,1605,1029,1028,4165,208896,4165,2162757]),
([pw263,pw0,pw349,pw1,pw2,pw3,pw4,pw5],[76,24,32,96,724,144,364,5,12,68,521,172,241,537,509,17,181,205,389,65,89,136,421],[1,62,92,200,1800,6152,24585,58,88,32841,99336,6152,24585,1,131185,80,264208,89,131153,80,80,89,655425,1050689,131144,269312,6299657,6153]),
([pw263,pw354,pw0,pw1,pw2,pw3,pw4,pw5],[24,76,60,73,88,149,192,96,5,12,68,521,160,241,537,509,17,364,181,124,421,89,65],[7,2,120,386,3712,12416,49282,65543,131146,130,131138,12290,147586,65768,65666,329856,12416,49282,131082,2152,143432,49162,1572866,6295554,4210818,538624,1589250,12290]),
([pw0,pw187,pw1,pw2,pw14,pw4,pw5],[28,137,12,60,29,153,377,525,521,397,112,253,120,5,124,65,421,52,285,241,176,449,509,89,45,565,273],[7,56,56,1,88,152,259,7,521,3075,259,61440,196616,787456,7340032,53256,8410112,17854464,33621000,34668552,68420608]),
([pw345,pw33,pw0,pw1,pw3,pw4,pw5],[60,124,205,1,5,117,137,25,112,413,477,17,65,132,57,421,493,113,473,285,176,449,509,273],[7,11,50,210,786,1042,2049,28673,36867,769,69633,131081,11,777,262153,32834,525056,7340032,33090,3145794,9437952]),
([pw33,pw0,pw1,pw384,pw3,pw4,pw5],[60,17,205,425,120,65,421,569,169,225,257,457,117,5,137,112,285,241,176,509,180,449,389,45],[3,13,49,85,13,133,769,273,81,1281,2305,12304,16464,229376,3932160,20560,4231184,9441296,16464,1572944,1146880]),
([pw385,pw33,pw0,pw1,pw3,pw4,pw5],[60,76,493,1,5,117,173,92,449,45,17,65,425,557,180,137,421,112,285,241],[7,11,50,82,146,786,1025,6145,6145,6145,8323,137,137,137,11,114688,917504,130,114688,130,130]),
([pw0,pw407,pw1,pw2,pw3,pw4,pw5],[76,8,60,17,96,192,149,73,364,5,124,521,160,241,237,537,509,173,89,477,421],[15,504,537,3096,28696,98313,417,275,289,12289,263,385,480,12640,321,132609,266753,525057,15360,1049601,12289]),
([pw0,pw1,pw2,pw408,pw3,pw4,pw5],[32,149,73,120,65,140,117,17,257,128,20,521,165,148,457,421,212,337,493,0,56,241,4,8,80,449,88,585],[7,248,1952,6824,8608,24736,7,7,7,515,515,1,35384,196632,327704,11784,3670528,12583424,35336,35336,253755392]),
([pw253,pw0,pw2,pw10,pw3,pw4,pw5],[32,20,73,16,120,341,497,65,140,117,17,257,128,149,521,165,148,457,421,212,337,493,116,241,68,509,80,88,585],[7,13,17,7,37,69,1936,15616,54544,68864,197888,1,283024,1573008,2621584,94224,12595200,50343936,282640,282640,511705088]),
([pw253,pw0,pw2,pw3,pw4,pw5,pw409],[32,453,497,549,593,4,68,73,92,257,96,17,29,421,397,104,241,156,413,449,80],[7,7,11,19,35,193,3840,5440,3840,1600,1856,24640,491520,1572928,1048640,303168,9280,9280,229440,229440,1]),
([pw0,pw1,pw254,pw10,pw3,pw4,pw5],[128,73,148,17,257,29,457,120,13,197,341,497,24,173,421,397,65,212,337,493,25,116,241,68,509,545,728,573],[15,28,21,37,28,76,387,129,519,1027,2051,12417,49153,458880,721024,1056773,6299649,25174017,33570817,50348033,222298112]),
([pw195,pw0,pw1,pw254,pw3,pw4,pw5],[120,173,24,128,73,5,25,421,116,413,68,557,401,149,117,65,140,29,257,17,457,453,337,493,545,176,180,585],[7,25,33,195,771,3075,12296,49153,196737,852480,1378304,8201,4233,12808,2103304,65673,4211201,8407041,16777857,16779393,234883584]),
([pw0,pw1,pw254,pw3,pw4,pw5,pw330],[92,17,96,297,181,49,457,120,477,180,493,397,421,156,285,241,557,212,73,173,149,361,45,4],[15,15,23,15,103,15,1920,6784,57344,458757,1703940,7040,2106240,4260485,8388741,2108032,2693,2692,24581,24580,132]),
([pw410,pw0,pw1,pw254,pw3,pw4,pw5],[68,173,24,128,73,92,25,421,116,413,557,17,96,297,29,120,493,477,397,156,285,509,449],[7,27,33,195,771,1025,14384,14368,20641,14880,6145,229392,262273,1573392,6291473,295041,623104,2129921,524929,4225,524801]),
([pw0,pw1,pw223,pw2,pw3,pw4,pw5],[132,401,128,149,120,16,5,425,140,29,257,17,457,13,397,421,453,173,137,56,361,0,8,4,477,545,176,449,180,585],[15,49,208,789,3328,5376,15,8279,49171,15,65543,131124,262453,3670032,12582928,213,208,16777296,34619413,33570837,1007681536]),
([pw224,pw1,pw53,pw2,pw3,pw4,pw5],[120,52,32,124,173,5,137,732,361,76,509,72,132,401,60,297,17,140,69,397,421,285,148,453,29,457,413,477,545,573],[7,9,51,65,385,3585,258048,262161,1581057,2105728,12596224,196625,16924673,164224,33735680,49,67109009,134217745,385,268960769,536871296]),
([pw224,pw0,pw1,pw2,pw3,pw411,pw5],[116,153,52,32,120,173,137,361,76,509,64,297,17,29,457,89,397,421,285,132,93,168,449,45],[3,13,53,81,145,1793,6145,49,8209,6273,18945,32816,196624,262273,7864832,32816,49,10485808,145,2163216,2097793]),
([pw224,pw0,pw1,pw2,pw3,pw4,pw412],[68,96,153,52,32,120,173,137,156,361,509,297,17,29,101,397,421,285,449,413],[7,25,105,129,769,1057,6146,98,8195,770,3075,16480,98305,131840,263169,97,524640,97,769,1059,769]),
([pw225,pw0,pw1,pw2,pw3,pw4,pw5],[128,12,20,149,73,16,32,137,397,0,56,241,4,8,120,65,140,117,17,521,148,257,457,341,497,421,212,337,493,736,449,180,585],[7,29,97,387,3585,12289,25,507904,524545,3475456,5570560,25,25,8390665,16777225,33554689,201377792,335593472,524545,524545,8053065728]),
([pw0,pw413,pw1,pw2,pw3,pw4,pw5],[120,16,12,128,401,149,117,65,140,29,257,17,457,173,137,56,361,0,8,4,453,337,493,397,545,176,449,180,585],[7,56,193,769,3328,5376,41,8203,16643,229377,786433,8201,25,56,1048600,8457,2097217,4194369,25231361,25165825,503382016]),
([pw414,pw0,pw1,pw2,pw3,pw4,pw5],[68,12,8,24,4,16,80,397,149,497,92,257,96,17,29,593,421,156,413,241],[7,25,97,195,65,13,832,15360,20609,15360,65,832,193,33088,321,65665,917504,65,393345,4161,65]),
([pw415,pw0,pw1,pw2,pw3,pw4,pw5],[68,8,12,20,4,84,421,497,149,92,153,96,17,257,593,137,156,413,241],[7,25,33,99,33,19,416,7680,3137,11776,33,416,97,16544,289,32833,458752,33,32833,2081,33]),
([pw416,pw0,pw1,pw2,pw3,pw4,pw5],[68,12,8,32,20,16,4,137,421,0,56,241,92,17,96,153,257,72,493,173,156,285,413],[7,25,97,387,3585,69,61440,61440,385,96256,24577,917504,385,3147776,131073,385,5638144,655361,385,16513,133121]),
([pw224,pw0,pw417,pw1,pw2,pw3,pw4,pw5],[68,96,153,132,3,149,176,173,137,156,361,509,557,457,493,545,397,589,449,413],[7,25,41,193,257,1537,6209,8202,42,194,11,1538,67,1,16456,98313,131592,262153,16488,41,131624,41,9,524992,193,9,65547,65]),
([pw418,pw0,pw1,pw2,pw3,pw4,pw5],[68,8,12,20,32,24,4,397,137,56,361,0,92,17,96,297,29,120,493,173,421,156,285,509,449,413],[7,25,97,387,3585,35,61440,61440,82049,62464,24577,917504,1048705,6292480,25165825,655489,36045824,655361,2098305,16513,2098177]),
([pw1,pw53,pw2,pw3,pw14,pw4,pw5],[60,181,153,120,5,124,117,521,137,32,52,112,285,241,132,453,149,29,357,525,3,413,477,397,589,72,585,76],[7,120,424,1537,14336,114688,7,131083,523,264195,524291,16568,1049641,2099256,4194360,8388641,6312,424,16779265,234881025,16783360]),
([pw191,pw0,pw1,pw2,pw14,pw4,pw5],[28,137,24,521,12,124,397,132,149,73,5,65,100,389,144,377,525,341,453,337,477,589,196,72,585,68],[7,11,19,97,35,11,896,3104,1,61440,114688,672,672,139648,262528,2208,525344,1049632,6295584,58720288,6303744]),
([pw227,pw0,pw1,pw2,pw3,pw4,pw5],[124,16,28,32,12,0,56,589,4,8,132,149,73,5,65,140,29,137,153,144,377,525,341,453,337,477,196,521,241],[7,25,19,19,225,769,7168,24577,229377,1867904,2916352,5121,5121,4197504,8391680,9217,16785409,33562625,67240065,134348801,335544448]),
([pw0,pw1,pw2,pw3,pw14,pw411,pw5],[116,181,132,149,93,153,124,5,29,137,120,389,241,377,144,525,453,89,477,521,48,589,64,585,76,168,449],[31,227,775,1028,14339,49155,28,28,28,29,65548,196,131140,131265,262336,1,4613,524804,3145733,29360132,102762497]),
([pw0,pw1,pw2,pw3,pw14,pw4,pw412],[96,181,132,149,105,153,124,5,29,137,68,144,377,505,345,101,425,196,241,449,589,72,585],[31,227,775,1028,6147,11267,28,28,28,16396,29,196,32836,65728,32961,1,393732,524805,1179652,6291461,1441793]),
([pw345,pw0,pw21,pw1,pw3,pw4,pw5],[124,425,5,117,20,477,60,3,65,132,149,401,417,137,140,1,144,317,473,57,12,337,493,453,521,176,585,449],[7,9,19,7,7,35,449,3584,12289,245760,376832,524801,1052929,2097409,4194561,12801,3584,8390144,12289,16781313,234881024]),
([pw0,pw1,pw2,pw228,pw3,pw4,pw5],[132,73,128,144,153,181,65,117,148,257,525,13,209,521,341,497,488,205,337,493,196,241,740,285,176,509,636,449,273],[63,248,796,797,792,1304,2127,4111,12547,16391,32775,65737,204877,327752,589896,73989,15728640,251658240,73408517,205529093,342884352]),
([pw78,pw345,pw0,pw1,pw3,pw4,pw5],[132,12,65,60,113,149,337,493,144,1,425,153,5,109,57,417,196,413,176,557,477,317,200,473,184,81,85,97,137,449,273],[7,29,33,7,69,133,7936,24833,37121,201984,1836288,18689,33537,6488832,25953024,33603585,71319553,151011329,272662529,553680897,1095696384]),
([pw0,pw1,pw194,pw2,pw14,pw4,pw5],[132,73,128,149,24,28,137,120,65,124,5,100,389,144,377,525,421,341,453,397,337,477,565,68,585,449,156],[15,116,1920,4,30720,57344,111,15,66063,135175,262151,101,524832,612,612,1921,1049472,2098048,4262401,4260353,125835264]),
([pw0,pw1,pw419,pw2,pw3,pw4,pw5],[132,73,128,149,124,16,117,65,421,137,140,17,144,321,481,341,453,0,56,413,4,8,337,493,521,176,585,449],[15,52,208,789,15360,23552,15,15,795,32775,65543,177,821,917520,3145744,853,4718672,8388688,789,16777493,235405312]),
([pw0,pw1,pw2,pw420,pw3,pw4,pw5],[32,144,153,73,205,117,17,216,257,481,209,341,497,124,421,196,413,740,241,88,557,449,80,521,509,273],[15,118,390,198,390,646,27,11,1033,2057,4105,1,24626,491538,7864338,8544384,491520,22544384,516096,2777088,34308096]),
([pw30,pw0,pw1,pw421,pw2,pw4,pw5],[28,124,137,77,140,153,29,377,525,52,421,65,5,44,285,241,40,449,509,89,45,273],[3,3,7,11,3,3,112,1,82,176,304,1538,6146,57344,458752,1538,9218,197634,534530,1116162,2187264]),
([pw422,pw345,pw0,pw1,pw2,pw3,pw4,pw5],[132,124,20,60,153,136,564,421,137,196,285,176,449,144,17,73,413,557,273],[7,57,3,67,387,1537,6145,24578,32771,1,387,66050,133122,8209,24578,385,75280,145424,32771,387,1537,6145,387,66050,133122,385,6273,265728]),
([pw0,pw1,pw2,pw423,pw3,pw4,pw5],[32,453,73,124,65,140,148,17,113,257,29,481,421,205,196,413,337,88,557,449,80,20,137,241,56,521,585],[7,504,736,1256,736,2272,7,7,75,67,7,1,12344,114712,1966104,6291528,25182272,1704000,41996296,1970184,68599808]),
([pw0,pw424,pw2,pw10,pw3,pw4,pw5],[32,20,73,124,65,140,13,17,257,128,453,148,29,481,421,205,196,413,337,88,557,449,80,521,116,241,509,585],[7,248,4000,6824,2464,10400,29,9,2059,2053,2053,1,49208,458776,7864344,8392200,50335232,71306752,8536584,3686920,140181504]),
([pw0,pw234,pw1,pw2,pw3,pw4,pw5],[124,16,24,132,149,401,5,425,397,140,133,377,153,525,73,137,56,241,0,8,4,13,421,453,477,545,176,585,449],[7,56,193,1793,6656,10752,16397,7,33027,458753,1572865,2097161,4194569,56,8388632,73,193,16777281,33685761,33554689,469893120]),
([pw235,pw1,pw53,pw2,pw3,pw4,pw5],[124,52,32,120,5,173,137,196,241,76,449,72,132,149,401,13,421,393,453,425,60,133,389,140,525,153,477,545,573],[7,9,51,65,385,3585,28672,36881,200705,20864,275456,524305,3211265,4194688,59769856,49,524433,67108881,385,134284289,268435840]),
([pw235,pw191,pw0,pw1,pw2,pw4,pw5],[28,124,137,52,32,5,65,196,241,68,449,72,77,173,132,149,73,389,140,153,89,45,273],[7,1,26,106,386,3586,3,3,12291,3,3,114688,98,131456,787968,98,147840,50688,1048738,2097698,4195200]),
([pw235,pw0,pw1,pw2,pw3,pw411,pw5],[116,17,52,32,124,5,137,241,76,449,64,153,181,133,357,525,89,421,397,285,132,453,93,477,545,573],[3,13,53,81,145,1793,6145,49,8209,18561,35329,65584,393232,524417,7340544,393264,49,8388656,145,16908816,33555073]),
([pw235,pw0,pw1,pw2,pw3,pw4,pw412],[68,96,52,32,124,5,137,172,241,449,153,181,133,505,101,421,397,285,509,413],[1,14,54,82,386,531,3074,50,4115,386,9731,16432,98321,131456,262659,98353,524464,51,401,531,387]),
([pw0,pw1,pw2,pw236,pw3,pw4,pw5],[132,73,128,453,124,65,140,5,181,148,257,525,197,341,421,189,196,413,337,176,557,477,521,241,56,449,8,636,585],[15,496,1860,1861,1856,2880,15,15,4627,8711,15,689,49253,458800,3670064,4194821,25231872,101188096,4341765,5259269,404422656]),
([pw235,pw0,pw1,pw2,pw60,pw4,pw5],[28,124,521,128,453,73,132,5,216,25,137,740,241,84,449,65,153,517,89,477,389,545,397,573],[1,126,966,1281,6406,24838,120,33154,65793,6400,213248,122,259,6488,120,2371,264578,524674,1050625,6291457,8394752]),
([pw425,pw0,pw1,pw2,pw3,pw4,pw5],[124,16,24,20,137,397,56,241,0,8,4,132,401,128,149,5,65,140,17,321,481,421,453,337,477,545,176,585,449],[7,13,7,51,449,1537,30720,98305,393249,917632,1441792,108545,2097185,30848,4208640,2129953,8421377,16809985,33554593,33554465,469762176]),
([pw0,pw1,pw2,pw426,pw3,pw4,pw5],[32,128,120,65,144,117,17,20,153,29,421,104,389,257,136,457,81,73,137,208,413,337,88,557,449,80,397,56,509,585],[3,124,402,1554,30800,49232,3,135,196611,3,3,1,263186,3676172,62914572,67110018,134223874,306184194,7170,12583938,583014400]),
([pw32,pw0,pw1,pw2,pw3,pw427,pw5],[112,120,124,52,136,89,397,297,17,137,133,457,425,196,241,116,285,168,509,156,449,433,273],[7,27,59,66,19,19,401,275,1555,2193,2193,4130,18,122880,1966080,50,35,2621474,18,18,5038080]),
([pw32,pw0,pw1,pw2,pw3,pw4,pw428],[68,124,52,88,209,120,205,397,136,297,17,137,133,45,156,285,241,509,449,413],[3,29,103,129,257,289,1808,1378,6401,1792,769,8306,273,114704,393233,97,540770,99,257,289,49153]),
([pw32,pw0,pw429,pw1,pw2,pw3,pw4,pw5],[68,132,40,136,421,509,457,17,257,180,205,116,389,44,341,73,337,137,501,152],[3,7,11,9,17,9,41,78,74,200,3,328,41,1,1538,7,14338,7,1538,11,53250,16387,3,67072,1569,3,393219,528417]),
([pw0,pw1,pw430,pw2,pw3,pw4,pw5],[132,209,128,149,120,16,5,205,137,136,133,257,17,457,401,453,397,425,477,176,449,180,585],[15,49,208,1813,6656,10752,15,15,787,16391,32775,180,65845,528,528,213,131152,262224,789,789,7864320]),
([pw32,pw1,pw53,pw2,pw3,pw4,pw5],[60,52,32,153,17,120,425,397,112,389,76,537,72,297,69,137,521,241,132,149,180,133,45],[7,27,99,161,769,7169,8209,16480,98336,131840,1837056,49,2097201,785,1050641,16480,352,5242976,800,100384,1049344]),
([pw32,pw0,pw1,pw2,pw3,pw411,pw5],[120,124,52,32,425,5,397,56,389,48,76,537,64,116,17,144,297,133,457,89,137,521,132,149,73,196,180,45],[3,13,53,65,897,7169,122880,49,172033,123136,321536,524305,3145729,62923008,79693824,49,49,201326609,1057025,3147777,100673792]),
([pw32,pw0,pw1,pw2,pw3,pw4,pw412],[68,124,52,32,120,425,397,156,389,537,96,17,144,297,133,101,137,521,241,509],[3,13,55,65,385,529,15360,6194,21505,4480,6657,32818,196609,262528,524801,49,178,51,385,529,385]),
([pw431,pw0,pw1,pw2,pw3,pw4,pw5],[128,20,12,209,73,16,32,397,137,0,56,241,4,8,136,17,257,133,457,401,497,120,65,204,413,180,557,493,273],[7,27,97,387,3585,12289,49161,114688,147713,116736,311296,524297,25,526345,1048585,16641,31459328,241172480,16641,16641,310380544]),
([pw432,pw0,pw1,pw2,pw3,pw4,pw5],[120,12,16,20,28,56,389,0,8,4,128,209,149,117,65,137,421,136,257,17,457,401,453,337,493,176,449,180,585],[7,25,21,19,225,769,7168,24577,98305,917568,1441792,3073,3073,2100288,4197376,99329,8396801,16785409,98369,163841,503316544]),
([pw0,pw433,pw1,pw2,pw3,pw4,pw5],[68,8,12,80,453,209,96,257,136,17,29,133,137,449,401,156,413,241],[7,56,960,3393,960,9,41,9,4107,9,8451,56,41,16408,41,257,229376,9,257,8457,9]),
([pw434,pw0,pw1,pw2,pw3,pw4,pw5],[68,12,8,20,4,84,521,209,453,96,153,136,17,257,401,156,413,241],[7,25,33,99,33,21,416,7680,1601,11776,33,416,97,16544,161,2113,229376,33,2113,97,33]),
([pw32,pw0,pw435,pw1,pw2,pw4,pw5],[12,28,397,136,297,17,457,137,521,44,253,120,205,25,285,241,40,449,509,413,433,273],[1,1,14,14,14,14,1,56,56,56,88,392,2,1672,392,14336,49664,458752,526848,1120256,2179584]),
([pw0,pw436,pw1,pw2,pw3,pw4,pw5],[68,8,12,96,17,136,153,257,521,449,72,205,425,156,285,241],[7,120,120,105,184,49,33,33,267,33,547,7168,33,57344,1025,33,7168,3073,33,1313,1025]),
([pw32,pw0,pw417,pw1,pw2,pw3,pw4,pw5],[68,132,136,401,176,425,397,156,389,557,509,60,149,5,241,493,589,449,137,501],[3,7,11,49,65,385,1553,2054,4106,8240,3,16768,17,1,32786,7,65666,131075,32794,11,138,11,3,176,49,3,786435,17]),
([pw437,pw0,pw1,pw2,pw3,pw4,pw5],[68,12,8,20,32,28,4,56,389,0,96,17,136,297,29,133,120,205,425,156,241,509,449],[7,25,97,35,897,37,15360,15360,54273,15616,6145,458752,4097,1573120,6291457,4097,459008,196609,4353,69633,524545]),
([pw1,pw53,pw2,pw3,pw4,pw5,pw438],[60,481,457,72,5,76,117,80,453,88,149,401,525,577,49,4,173,425,112,361,241,449,509,120,397,124,389,537],[7,120,1920,2944,1576,2689,7,4099,8195,16395,32779,65592,131128,568,131113,1835008,6291496,58720257,786472,67371009,134217761]),
([pw191,pw0,pw1,pw2,pw4,pw5,pw438],[68,137,397,421,509,449,80,73,88,149,72,65,76,5,140,457,144,577,49,341,337,156,241,389],[7,11,11,7,51,7,960,15360,245760,278545,65,960,524736,49,449,1055744,6161,7169,6291473,10485761,16385]),
([pw0,pw1,pw2,pw3,pw411,pw5,pw438],[80,93,88,149,72,89,76,5,116,457,144,525,577,49,173,160,361,241,449,509,120,397,124,389],[15,240,3840,5888,9477,1,15,15,15,71,15,16496,240,101,116,229632,786437,7340036,98565,8421636,260]),
([pw439,pw0,pw1,pw2,pw3,pw4,pw5],[76,16,4,32,8,28,12,0,56,389,80,73,88,149,5,65,92,525,457,577,49,449,341,173,337,160,241],[7,25,19,97,897,19,15360,49153,458752,721408,3211265,7169,15360,4201984,6145,8404993,16793601,20481,100663808,65537,66049]),
([pw0,pw1,pw2,pw440,pw3,pw4,pw5],[88,73,84,92,261,257,481,377,401,497,449,509,32,76,65,180,421,205,160,413,337,508,433,12,137,56,285,168,273],[63,104,108,168,104,109,263,527,263,263,3595,4105,253952,1859584,6292493,25198600,100925448,3085,151879680,3085,402654221]),
([pw0,pw1,pw441,pw2,pw3,pw4,pw5],[88,73,84,149,76,16,117,65,92,181,17,321,341,449,537,205,337,493,160,361,241],[15,52,208,1792,2816,789,15,15,15,4103,275,177,272,272,24629,32848,65616,139349,1835008,277,277]),
([pw1,pw66,pw2,pw3,pw4,pw5,pw438],[60,481,457,80,149,88,73,341,449,441,525,577,49,4,68,421,137,112,413,241,144,5,65,537],[7,120,120,184,824,105,7,1027,2051,4107,8203,114688,917504,3146024,5242881,114688,49448,49153,393512,393217,8388641]),
([pw442,pw0,pw1,pw2,pw3,pw4,pw5],[68,24,4,12,8,16,92,521,153,481,577,80,401,88,73,421,156,413,241],[7,25,97,201,65,7,832,832,193,1344,321,30720,12417,30720,65,32897,458752,65,32897,193,65]),
([pw0,pw1,pw443,pw2,pw3,pw4,pw5],[88,73,84,453,68,20,92,181,377,81,129,341,137,449,509,421,156,413,241],[15,52,448,208,448,213,15,15,1559,2055,91,80,4177,80,24629,36880,458752,85,36880,24661,85]),
([pw0,pw1,pw2,pw444,pw3,pw4,pw5],[32,144,261,73,493,257,117,17,92,181,557,457,209,341,497,132,421,137,180,160,413,168,241,397,509,449,552,324],[15,242,418,802,418,3362,27,11,4105,8201,16393,1,491538,7864338,263506,8749056,7864320,17040640,491520,34440448,202638592]),
([pw30,pw0,pw367,pw1,pw2,pw3,pw4,pw5],[17,68,60,377,92,132,124,401,137,156,361,509,449,40,52,144,261,65,5,389,557,180,117,285,89],[31,114,162,34,258,1538,6162,24609,98465,393225,43,525833,1050627,2,6291552,98,8389152,4130,2228384,162,672,162,34,18875904,1181698,34,4130,1538]),
([pw1,pw2,pw47,pw3,pw4,pw5,pw438],[72,5,76,65,60,481,457,68,137,521,112,285,241,509,449,181,52,25,89,397,389,49,537],[15,112,896,7168,24581,98308,15,131207,263175,135,15,524464,1049648,2097173,65557,525696,389,557188,3077,1082372,4194308]),
([pw445,pw0,pw1,pw2,pw3,pw4,pw5],[68,16,4,32,20,8,397,137,0,56,389,92,457,181,577,72,5,76,65,421,156,241,89],[7,25,35,225,1793,35,14336,14336,193,23552,10241,491520,524353,3146752,2049,655425,5473280,2049,193,131137,3073]),
([pw0,pw1,pw2,pw446,pw3,pw4,pw5],[92,153,377,481,76,5,124,65,20,32,421,397,156,285,241,89,565,449,273],[7,11,11,11,7,11,240,769,3136,28672,4097,113,3184,36976,4161,65617,12289,131137,13376,65601,397313]),
([pw0,pw1,pw2,pw3,pw447,pw4,pw5],[92,17,128,149,73,144,257,173,181,557,457,120,397,421,32,100,241,341,168,453,68,413,565,585],[63,227,295,99,99,1571,2236,14364,18444,491532,1573389,14500,1,2361504,1051297,14372,6297604,4196869,2394112,1051137,9798145]),
([pw0,pw1,pw2,pw448,pw3,pw4,pw5],[32,149,73,76,65,140,148,17,113,153,257,181,49,132,421,137,180,160,413,337,557,493,241,56,4,449,585],[7,504,1760,2272,1248,4328,7,7,7,67,75,1,122904,917528,3145784,106560,12714048,50331720,122880,68247560,68550664]),
([pw0,pw449,pw2,pw10,pw3,pw4,pw5],[32,20,73,76,65,140,13,17,257,84,149,148,181,49,132,421,137,180,160,413,337,557,493,521,116,241,509,585],[7,248,4000,6304,2464,10920,29,9,2053,2053,2059,1,245784,1835032,6291512,8523264,50335232,67112456,245760,144753160,136839688]),
([pw31,pw0,pw449,pw2,pw3,pw4,pw5],[68,149,24,32,209,132,537,453,73,136,257,148,17,104,241,156,413,557,129,533],[7,25,35,9,35,99,392,7680,33,7680,3137,392,2057,2184,73,33,122880,131137,33,786465,49217]),
([pw30,pw0,pw449,pw1,pw2,pw3,pw4,pw5],[17,24,377,216,28,68,32,173,116,361,36,557,509,153,457,5,65,421,44,132,337,553,585],[15,120,104,168,8,1824,7200,24585,16393,13,13,13,41,40,98312,131128,786952,2088,98312,131112,524808,2088,131112,1081352,2088,655904,2230304,4196896]),
([pw0,pw1,pw2,pw3,pw450,pw4,pw5],[136,297,17,29,133,457,76,425,120,205,100,241,128,341,204,176,557,105,77,421,569,137,273],[7,7,27,7,7,35,960,257,257,31744,241728,786753,1281,960,1114560,2621505,257,321,257,321,4213824]),
([pw0,pw451,pw1,pw2,pw3,pw4,pw5],[76,16,4,80,401,88,149,5,425,140,525,457,577,445,12,28,56,241,0,449,13,453,160,361,585,537],[7,120,385,3584,5632,8705,105,163,49153,458753,524803,1048617,2097208,120,49,385,385,161,12713984,50331649,4325377]),
([pw452,pw1,pw53,pw2,pw3,pw4,pw5],[76,52,32,72,5,425,124,137,120,160,241,449,80,401,60,457,73,88,13,453,140,525,445,361,585,537],[7,9,51,449,1537,2049,258048,393233,667776,140800,139265,49,3195008,1050112,5259265,49,49,131089,8390272,50331777,1537]),
([pw452,pw191,pw0,pw1,pw2,pw4,pw5],[68,397,137,72,52,32,76,5,156,241,449,421,80,73,88,149,65,389,537,140,445,89],[7,9,49,217,769,1025,7,2051,2115,7,67,61440,65736,131840,1835009,24776,148224,24577,2097608,193,769]),
([pw452,pw0,pw1,pw2,pw3,pw411,pw5],[64,76,52,32,5,89,124,137,120,241,48,449,80,93,88,149,116,525,457,389,445,173,585,537],[1,14,54,450,1539,2050,61440,50,458880,721409,1114115,50,61568,61953,24579,2097170,51,16403,590465,12583043,66051]),
([pw0,pw1,pw2,pw453,pw3,pw4,pw5],[88,73,84,149,76,65,140,5,481,148,257,377,341,489,180,421,173,160,413,337,557,485,137,12,241,56,509,736,585],[15,496,1860,2880,1856,1861,15,15,15,4615,8723,689,114736,917552,3145829,12599808,50463232,67109381,138854400,269516805,269746181]),
([pw454,pw0,pw1,pw2,pw3,pw4,pw5],[76,16,4,20,8,12,28,56,241,0,88,401,84,149,5,65,140,181,17,321,453,557,537,173,337,160,361,585],[7,25,19,97,897,19,15360,49153,458752,721152,196609,54273,1055744,15616,6293505,8404993,16793601,2179073,100663552,136314881,35651841]),
([pw0,pw455,pw1,pw2,pw3,pw4,pw5],[68,28,4,80,73,88,149,136,153,180,5,65,137,421,156,241,389,468,449,557,89],[7,120,3968,12545,115072,131457,105,1537,4131,49153,786435,120,105,81976,49,12801,1066496,1537,12289,4129,49153]),
([pw452,pw1,pw66,pw2,pw3,pw4,pw5],[68,153,32,80,180,5,421,137,156,241,449,73,60,457,149,88,93,65,413,557,445],[7,9,51,195,771,1025,63496,34872,201,99080,34817,131120,193,262912,1576961,209,262448,49,193,32833,769]),
([pw456,pw0,pw1,pw2,pw3,pw4,pw5],[68,20,4,8,132,397,137,149,73,136,377,148,181,156,413,241,509,557,501],[7,11,17,105,17,11,400,7680,17,7680,3585,400,177,2192,145,17,57344,196609,17,262193,24577]),
([pw0,pw1,pw457,pw2,pw3,pw4,pw5],[136,181,140,457,577,20,32,65,5,68,137,521,156,285,241,557,537,25,89,253],[15,15,15,15,23,15,100,388,3585,28672,98816,389,1541,12292,33284,131205,266372,644,529921,3585,12800]),
([pw452,pw1,pw2,pw47,pw3,pw4,pw5],[68,52,181,72,29,137,156,241,449,5,76,65,140,457,481,521,285,557,537,25,89,253],[7,7,9,53,197,257,3592,28672,32801,65728,393217,3592,525353,1049800,1537,4129,4288,135169,2097249,1057,193]),
([pw458,pw0,pw1,pw2,pw3,pw4,pw5],[68,28,4,20,32,12,8,56,241,0,136,377,216,149,153,5,481,137,156,509,65,73,421,93,413,557,501],[7,25,97,35,897,67,31744,105472,137217,281856,527361,3190784,4206593,8663296,536577,4329473,17076480,33591297,4587521,67764225,262401]),
([pw0,pw1,pw53,pw2,pw3,pw4,pw5,pw335],[401,80,149,88,425,72,5,76,545,120,521,124,389,160,241,537,509,140,60,13,32,52,429],[15,2,240,3840,28672,98314,393224,15,524427,779,15,137,3145739,240,3840,28672,98314,393224,240,240,154,232,27392,4196874,2,12298,24584,520]),
([pw268,pw0,pw1,pw53,pw2,pw3,pw4,pw5],[76,60,140,52,32,173,5,72,160,361,509,401,80,149,88,425,545,120,521,389,585,449,13,501],[7,25,7,101,129,769,1025,30720,1,32801,458752,525056,3145729,30720,4210721,219136,19200,18433,32801,458752,525056,3145729,97,33057,16417,131840,8519681,769]),
([pw1,pw108,pw53,pw2,pw3,pw4,pw5],[120,52,32,132,401,60,297,17,140,69,5,397,421,149,200,285,180,449,173,744,361,509,29,413,45],[7,504,1545,6161,57368,196632,9,262659,33,1589249,2162689,417,4194593,480,65888,4865,8913409,16843265,526337,2164737,638976]),
([pw1,pw53,pw2,pw3,pw238,pw4,pw5],[60,181,153,120,5,124,69,521,137,32,52,112,285,241,132,453,149,29,357,525,3,413,477,397,589,72,585,76],[7,120,424,1537,14336,114688,7,131083,9,264195,524291,16568,1049641,2099256,4194360,8388641,6312,424,16779265,234881025,16783360]),
([pw239,pw1,pw53,pw2,pw3,pw4,pw5],[124,52,32,120,5,173,137,196,241,76,449,72,132,149,401,13,421,393,453,425,60,133,389,140,525,153,477,545,573],[7,9,51,65,385,3585,28672,36881,200705,20864,275456,524305,3211265,4194688,59769856,49,524433,67108881,385,134284289,268435840]),
([pw109,pw1,pw53,pw2,pw3,pw4,pw5],[60,52,32,153,120,425,397,112,389,76,537,72,17,297,69,137,521,241,132,149,180,133,45],[7,9,51,81,385,3585,12289,16432,98320,131456,1836032,49,2097169,385,1053697,16432,176,5242928,400,99344,1048960]),
([pw1,pw53,pw2,pw3,pw4,pw5,pw459],[60,481,457,72,5,76,69,80,453,88,149,401,525,577,49,173,425,112,361,241,449,509,120,397,124,389,537],[7,120,1920,2944,1576,2689,7,4099,8195,16395,9,32824,65592,568,65577,917504,3145768,29360129,393256,33685505,67108897]),
([pw460,pw1,pw53,pw2,pw3,pw4,pw5],[76,52,32,72,5,425,124,137,120,160,241,449,80,401,60,457,149,88,13,453,140,525,445,361,585,537],[7,9,51,449,1537,2049,258048,393233,667776,140800,139265,49,3195008,1050112,5259265,49,49,131089,8390272,50331777,1537]),
([pw1,pw53,pw2,pw3,pw4,pw5,pw335],[80,401,88,149,76,13,453,32,52,5,425,120,545,124,521,160,241,389,537,509,140,17,60,429],[15,55,71,15,23,391,1552,30720,229376,786437,7340036,1552,1552,533,788,112640,8398853,1,98309,98308,2052]),
([pw268,pw1,pw53,pw2,pw3,pw4,pw5],[76,52,32,60,153,140,173,5,72,160,361,509,80,401,88,149,13,453,425,120,521,545,389,585,449,501],[7,57,195,257,1537,2049,61456,81985,159744,26112,24577,262209,3670032,4195856,25165841,193,262721,16449,525824,34078721,1537]),
([pw257,pw1,pw2,pw3,pw4,pw5,pw335],[80,73,88,149,72,65,76,5,92,17,96,153,257,341,173,337,120,521,124,605,429,509,160,241],[15,240,3840,5888,1541,1796,15,15,8199,71,15,16496,32880,101,116,983040,1376261,1,14680069,12582916,65540]),
([pw268,pw257,pw1,pw2,pw3,pw4,pw5],[76,96,153,52,32,173,72,116,361,48,509,17,257,65,80,73,88,149,341,337,120,605,521,501,449,585],[7,25,43,65,897,1025,2054,35,2054,4358,7,8225,245760,377088,98305,8225,524321,35,7340288,9437185,50331905]),
([pw0,pw461,pw1,pw2,pw3,pw4,pw5],[28,60,181,153,377,525,32,12,16,0,56,589,4,8,120,5,124,65,100,241,112,132,453,73,89,477],[1,14,14,7,22,38,194,386,131,3586,12290,245760,65537,1837056,14680064,2162689,17942528,33669120,65537,65537,1837056]),
([pw191,pw0,pw1,pw2,pw4,pw5,pw335],[28,521,545,565,605,4,68,137,80,73,88,149,72,65,76,5,100,389,156,241,537,509,140,17,144,89],[7,7,11,19,35,193,3840,61440,983040,3145792,29360192,3840,395008,1600,1856,33845248,24640,28736,458816,852032,1]),
([pw191,pw0,pw461,pw1,pw2,pw4,pw5],[28,124,397,25,137,132,149,73,5,65,100,389,144,377,525,589,196,72,585,68,89,45],[3,7,3,27,3,3,1,224,770,15360,28672,162,546,99330,917506,162,67680,786528,1114370,2621698,101376]),
([pw191,pw462,pw0,pw1,pw2,pw4,pw5],[28,124,137,77,173,52,32,5,196,241,68,449,72,132,149,73,65,389,140,153,89,45,273],[7,3,3,27,3,3,1,98,178,770,7170,57344,65554,131840,789504,40978,140032,27648,1048850,2098194,4196096]),
([pw191,pw0,pw1,pw2,pw4,pw5,pw463],[28,521,545,565,605,68,509,137,80,73,88,149,72,65,76,5,100,389,156,241,537,140,17,144,89],[7,7,11,19,97,161,3840,61440,983040,1048672,14680096,3840,395008,1632,1824,17068032,24672,28704,393312,852000,1]),
([pw0,pw1,pw2,pw3,pw411,pw5,pw335],[80,93,88,149,72,89,76,5,120,545,124,521,160,241,389,537,509,116,17,144,173,429],[15,240,3840,28672,98309,917508,15,15,15,71,15,1049712,240,101,116,14080,2098437,1,12293,12292,260]),
([pw268,pw0,pw1,pw2,pw3,pw411,pw5],[76,144,153,116,52,32,173,5,64,361,48,509,80,93,88,149,89,120,521,545,160,389,585,449,501],[15,49,209,257,1545,2049,61444,65601,917508,3146500,12582917,24641,61440,62208,24577,193,65857,16449,393984,16908289,1049089]),
([pw464,pw0,pw1,pw2,pw3,pw4,pw5],[76,24,60,17,32,8,5,173,4,0,56,241,80,73,88,149,65,120,545,124,521,160,389,537,509,89,429],[15,49,225,273,3585,49,61448,65609,1966088,6293512,25165833,24641,61440,6322176,24577,193,35651649,16449,3016704,67764225,2099201]),
([pw104,pw0,pw1,pw2,pw3,pw4,pw5,pw335],[84,149,80,73,5,72,65,88,521,28,545,12,241,36,389,64,509,537,60,152,148,257,364,377,525,341,453,173,337,477,605,128,429,748,573],[1,15,244,3840,61440,196737,1835136,2097163,6291536,10487040,18894848,16973825,11796480,27,267,37769219,71499778,4194315,138412304,272633872,541130769,138412048,1073762560,6442516737,1,25769873409,8589955072,2147483648]),
([pw268,pw104,pw0,pw1,pw2,pw3,pw4,pw5],[8,60,40,148,257,377,73,128,149,212,173,137,736,509,65,241,36,389,64,585,449,525,341,441,337,45,521,501],[15,58,456,1664,2176,4224,12416,128,448,17920,4228,491520,1576965,464,17936,4272,2261008,1576976,448,448,4227264,8392896,1664,16778752,33560064,4224,201330816,1576960]),
([pw0,pw1,pw2,pw175,pw3,pw4,pw5],[60,181,153,17,28,112,389,68,537,120,5,128,73,144,12,137,521,241,436,441,65,25,89,45,589,4,585],[7,7,9,19,99,387,15872,22529,98320,131168,792960,1073665,2105360,4202592,8398720,16401,16777249,100663425,112,98576,16777440]),
([pw465,pw0,pw1,pw2,pw10,pw3,pw4,pw5],[76,73,32,209,20,65,205,144,752,96,84,120,397,208,389,537,17,113,124,133,241,497,5,89,493,68,521,40,449,137,273],[1,30,225,912,7296,24704,33921,386,196769,896,852096,24704,98433,419,1,266,1057026,2097411,4194688,225,8396961,16777376,100925696,1057024,134218497,1073152,872448257,1073766401]),
([pw0,pw1,pw2,pw314,pw3,pw4,pw5],[88,73,84,364,3,17,5,65,152,24,60,153,545,124,521,160,389,740,241,537,509,89,45,429,273],[63,232,3888,31008,491552,1572901,207,8207,24591,393231,1081355,131081,131144,2228296,4194381,12,491776,1048589,471296,8531981,16973829]),
([pw0,pw466,pw1,pw2,pw3,pw4,pw5],[28,32,149,73,60,153,144,65,112,389,68,537,397,413,4,557,25,521,137,273],[1,14,240,49,816,3120,14,208,4113,8464,50192,14,7,774,3078,65601,8640,33984,769,395265,526080]),
([pw78,pw465,pw0,pw1,pw2,pw3,pw4,pw5],[32,60,52,96,17,297,76,88,144,65,12,68,137,164,285,509,449,425,5,80,120,397,389,124,133,73],[15,58,64,896,7296,24704,98440,64,389,393476,3670272,4202752,524736,432,304,25166096,304,464,33554880,41947264,24704,98496,393536,139584,131456,4222976,102592,24768]),
([pw0,pw348,pw1,pw2,pw3,pw4,pw5,pw335],[72,401,17,149,84,65,5,545,521,181,389,241,321,537,509,481,140,60,80,76,28,12,36,64,453,364,3,173,337,477,605,120,429,160],[1,30,101,900,7172,57349,197124,262170,524385,3146112,12585984,548865,720896,524403,16777618,2074,548867,101187602,134742177,268960801,537403440,134807585,1073745024,6442983553,1,8590468097,8590461952,2148007936]),
([pw268,pw0,pw348,pw1,pw2,pw3,pw4,pw5],[17,76,60,140,20,128,149,173,137,160,361,509,401,65,521,545,389,585,449,89,45,501],[15,14,114,170,290,1538,2050,2,4193,8323,49185,67073,393219,4192,8322,49184,67072,393218,162,49248,1632,98,162,524930,1179778,1568,2097186,1538]),
([pw0,pw1,pw467,pw2,pw3,pw4,pw5],[60,377,153,17,124,65,269,525,12,20,5,421,137,100,241,112,285,176,449,509,413,557,273],[7,9,51,83,7,131,769,1072,6160,122880,917504,49,785,1089537,2228225,6192,1081392,2228272,6160,395280,4382720]),
([pw0,pw1,pw468,pw2,pw3,pw4,pw5],[88,73,84,149,76,24,60,17,5,65,120,421,124,521,160,241,389,537,509,205,557,89],[15,240,912,15488,114816,393365,15,15,15,114695,393235,524561,3092,49168,1053717,6416,2113808,1052949,15360,7189,49173]),
([pw195,pw0,pw349,pw2,pw3,pw4,pw5],[76,3,17,73,32,209,12,341,557,105,149,401,109,57,124,421,521,104,389,160,241,509,205,129,85],[15,49,17,73,137,777,3092,12293,114692,1966084,2097413,4194321,8406032,3088,1041,53249,17305601,20737,114688,49409,786689]),
([pw0,pw1,pw66,pw2,pw91,pw3,pw4,pw5],[73,32,453,205,153,3,120,60,136,521,421,389,241,537,449,68,81,341,413,100,557,80,585],[7,2,120,464,1616,6192,57360,7,7,7,65603,133123,7,104,448,1600,788512,3186688,2,1608,262248,1081416,1600,526432,2138176,1600,1600,4237312]),
([pw0,pw1,pw66,pw2,pw3,pw4,pw5,pw469],[73,32,453,65,153,5,180,521,421,389,241,156,537,80,81,413],[7,2,120,464,3600,12368,8272,7,7,16451,2563,7,7,104,448,35328,12352,8256,456,34888,2120,2120,448,448,448,2624,3136,2]),
([pw0,pw83,pw1,pw66,pw2,pw161,pw3,pw4,pw5],[120,153,73,453,5,205,241,389,449,537,149,216,593,81,421,3,521,413,557,65,589,585],[3,14,1,49,1,3,194,770,1024,2048,48,2048,2048,129,513,12,5,4100,24577,196,12,32769,1,67585,131136,262400,524288,48,131089,262161,18433,1048640,2097408,129,513,1048896]),
([pw92,pw0,pw83,pw1,pw66,pw2,pw3,pw4,pw5],[120,144,136,73,453,5,521,421,413,241,557,449,153,3,65,149,216,389,537,81,273],[1,7,28,1,32,193,768,3072,4097,24,1,24577,193,768,3072,32768,65536,24578,65536,131073,262145,24,9,524353,131336,24,8193,193,768,3072,192,257,1025,193,193,1049856]),
([pw92,pw0,pw83,pw1,pw2,pw3,pw4,pw5],[17,52,153,28,120,144,216,73,32,453,3,5,521,413,44,241,557,40,449,68,65,321,481,212,149,389,112,180,537,81,341,421,337,585],[15,114,898,3088,4178,58368,983040,117,645,1049621,4181,2138177,4522049,25165840,1049648,80,100664336,402653200,9437328,536875088,1082138816,66240,2148536336,4296024080,135331856,2147495952,134287376,8724226048]),
([pw92,pw0,pw1,pw2,pw3,pw4,pw5],[144,17,153,32,20,5,28,12,0,56,413,4,8,321,481,65,425,120,421,212,137,149,112,341,208,488,453,493,180,509,521,273],[7,25,33,193,1793,6145,7,7,7,9219,16387,98305,4063232,31982592,103284736,98305,99329,134250497,22414336,1879441408,2436891648]),
([pw470,pw0,pw1,pw66,pw2,pw3,pw4,pw5],[68,28,60,153,88,149,4,144,5,137,112,241,65,389,73,421,413,557],[15,49,69,385,531,3073,5,28,1,4236,13,9228,13,16404,4272,49,9264,49,4228,32773,66564,131077,32897,66944,385,9729,529,3073]),
([pw0,pw1,pw66,pw2,pw3,pw4,pw5,pw330],[73,80,149,153,493,477,144,68,156,389,52,137,241,557,88,397,413,72,421],[15,2,120,200,840,202,200,1095,23,2183,4867,24705,16519,112,32960,65856,8386,131264,262352,65872,8274,2,896,26754,18560,898,896,64]),
([pw0,pw83,pw1,pw2,pw351,pw3,pw4,pw5],[24,17,216,153,321,481,120,209,3,5,60,116,389,108,96,537,92,13,593,73,421,65,413,477,44,68,40,521,585,573],[15,14,14,14,14,22,38,196,836,1092,4,14400,114752,131652,786436,1048644,786436,786436,2097156,1049156,4195076,8389124,1048644,20971780,100663300,135270464,135299136,805343232]),
([pw307,pw0,pw1,pw2,pw91,pw3,pw4,pw5],[28,73,32,453,205,52,216,3,120,60,521,241,100,68,449,80,153,413,557,116,421,585],[1,14,240,864,1089,6336,57408,14,464,65856,1089,6336,57408,14,14,69,70,14,1,81,131280,270416,65,659712,303360,1180673,295937,2127872]),
([pw0,pw1,pw2,pw91,pw161,pw3,pw4,pw5],[73,17,453,153,205,3,120,216,521,241,321,449,481,212,593,81,5,421,413,180,557,112,589,100,585],[15,122,194,64,458,1666,6274,8277,8389,24705,33217,25217,8325,65600,96,131408,262256,1572944,192,131520,2359392,1572928,448,12583456,17303552,131392,131392,17304064]),
([pw352,pw0,pw1,pw2,pw91,pw3,pw4,pw5],[120,73,32,453,52,216,3,60,521,241,100,68,449,80,17,321,481,341,65,77,421,413,205,180,557,116,108,585],[1,30,97,161,289,1632,14368,42,16417,16417,289,49696,86048,35,35,289,131618,42,262145,1572897,6291521,29360129,33,102760449,25165825,1048833,1048833,142610944]),
([pw471,pw0,pw1,pw2,pw3,pw4,pw5],[60,17,16,32,28,56,389,0,8,4,257,297,120,1,133,457,117,5,137,421,112,241,180,509,449,413,45],[3,13,13,21,225,769,3073,13313,21505,33857,33793,200704,790528,3145792,29360128,856064,34672704,71372800,790592,12849152,5242944]),
([pw0,pw1,pw91,pw3,pw4,pw5,pw330],[52,73,453,120,493,180,477,521,421,156,241,389,557,636,205,3,153,32,77],[7,120,424,3584,12320,114720,7,163,1539,7,131107,1,2616,12344,8248,424,424,270504,1568,1568,1]),
([pw353,pw0,pw83,pw1,pw2,pw3,pw4,pw5],[68,96,60,453,32,73,20,5,52,493,40,421,521,241,44,413,156,449,557,257,153,176,3,137,389],[1,7,120,1920,7169,122880,394241,7,1572904,2622080,6145,106496,393217,2097153,6291457,8388609,16842753,2228227,680,2099201,16850952,393249,6145,106624,393345,6145,6145,73729]),
([pw472,pw0,pw1,pw2,pw3,pw4,pw5],[68,24,60,153,12,8,16,4,137,421,0,56,241,80,73,88,149,72,477,205,156,389,413],[15,49,193,785,7169,161,122888,917512,777,3149832,131081,122880,769,3207168,49153,769,5640192,655361,769,33025,135169]),
([pw473,pw0,pw1,pw2,pw3,pw4,pw5],[136,17,297,20,32,60,397,421,137,56,241,0,8,4,457,124,425,128,73,144,112,341,204,176,509,453,188,433,449,273],[7,25,33,449,3585,12289,7,7,387,7,16387,1015808,385,7734272,126222336,385,5866496,201949184,385,335544449,609223680]),
([pw474,pw0,pw1,pw2,pw3,pw4,pw5],[60,17,16,32,12,56,413,0,8,4,257,153,124,1,525,65,5,421,137,112,285,176,449,509,45,273],[3,13,13,21,225,769,3073,13313,3073,3137,17409,102400,397312,1572928,14680064,430080,561216,18911232,397376,6426624,36175936]),
([pw0,pw1,pw2,pw3,pw475,pw4,pw5],[60,525,153,144,65,28,601,5,137,421,12,20,80,73,112,285,241,509,449,453,89,477,521,413,8,573],[7,27,35,33,67,7,152,800,3073,126976,929792,568,25,1064984,2097176,545,800,4325664,8404993,16778241,33607680]),
([pw476,pw0,pw1,pw2,pw3,pw4,pw5],[96,17,153,20,32,60,12,28,56,241,0,537,557,449,297,76,425,84,73,144,180,421,149,192,341,493,137,172,361],[7,25,33,193,1793,14337,7,7,7,16899,12291,1015808,16121856,25559552,12289,36274176,34177536,12289,472908288,12289,8393217]),
([pw30,pw0,pw389,pw1,pw2,pw3,pw4,pw5],[297,68,60,92,153,96,84,32,132,137,156,361,497,149,65,5,144,52,493,421,413,537,192,429,449],[31,38,194,258,514,3074,98,2,12545,114689,65555,68625,65539,209152,475136,589826,1117184,2162690,28928,4726786,4197632,4202754,589826,1117184,81922,3074,25690114,3074]),
([pw477,pw0,pw1,pw2,pw3,pw4,pw5],[60,17,16,32,12,28,56,389,0,8,257,457,76,1,377,65,5,180,137,421,112,241,509,449,89,45],[3,13,13,49,449,517,3073,13313,17409,3201,3073,102400,917504,3145856,12587008,692224,17862784,37785600,917632,397312,1052800]),
([pw0,pw1,pw2,pw3,pw478,pw4,pw5],[60,181,84,73,377,28,525,120,5,132,57,137,129,341,453,65,144,337,477,397,0,56,389,585,8,449,68],[15,19,35,5,19,67,1932,6700,525,8716,16908,544,98433,196992,328068,524321,544,548,7340033,25165829,113246212]),
([pw0,pw1,pw2,pw3,pw479,pw4,pw5],[132,453,73,76,425,120,173,100,389,200,241,84,557,449,81,129,25,421,569,137,273],[7,120,33,33,1920,14344,7,49155,7,771,7,196649,161,120,266296,655369,33,41,33,41,1049480]),
([pw480,pw0,pw1,pw2,pw3,pw4,pw5],[68,60,153,24,20,4,12,8,421,137,56,285,0,84,401,149,76,65,124,5,156,389,89,533],[15,49,193,833,7169,49,57348,983044,773,3147780,8197,811008,769,59392,24577,769,5703680,8193,769,8651009,10241]),
([pw275,pw0,pw139,pw1,pw2,pw3,pw4,pw5],[377,68,60,136,153,176,84,65,421,137,156,285,449,497,453,5,389,32,413,429,501],[31,102,34,162,802,3074,4098,2,24593,32929,35,68625,35,139360,32928,802,263200,98,41120,34,265216,34,802,263328,162,34,1573122,34]),
([pw0,pw1,pw481,pw2,pw3,pw4,pw5],[32,149,593,60,153,144,205,120,421,112,389,88,537,425,12,413,4,557,5,449,80,273],[7,1,120,408,1560,6168,7,99,7,7,7,8232,16776,33288,198664,262496,8800,133216,1920,1579392,2100736]),
([pw30,pw482,pw0,pw1,pw2,pw3,pw4,pw5],[28,32,124,128,73,173,137,117,5,241,44,285,196,509,40,449,68,132,65,389,537,17,481,89,477,573],[15,12,30,36,68,12,12,9,4,388,13,7680,122880,131096,262276,12,528896,7348224,28,28,4632,139288,131084,8392836,16777348,12,12,33559040]),
([pw482,pw0,pw139,pw1,pw2,pw3,pw4,pw5],[377,60,153,128,5,120,117,124,421,137,241,100,285,112,509,176,449,65,505,73,413,557,273],[7,10,2,240,904,15360,114688,10,7,131203,267,7,294915,524298,131202,394,1056770,2129922,216,896,13320,114696,920,1056912,2130064,904,98696,4236288]),
([pw30,pw483,pw0,pw1,pw2,pw3,pw4,pw5],[28,32,124,128,453,173,397,65,5,241,44,389,196,449,40,537,68,132,17,481,89,477,573],[15,12,30,36,68,12,12,9,4,388,13,7680,122880,131096,388,12,6656,827392,268,28,4632,131096,131084,1052804,2097284,12,12,4198912]),
([pw0,pw1,pw484,pw2,pw3,pw4,pw5],[32,149,401,60,297,144,65,124,133,457,453,425,28,421,0,56,389,4,8,477,104,241,112,80,449,521,88,273],[7,1,120,408,536,536,7,99,1027,7,1027,2088,12424,114696,393224,2144,2144,524384,7413888,125837440,206635008]),
([pw30,pw485,pw0,pw1,pw2,pw3,pw4,pw5],[28,60,40,96,17,68,124,173,137,449,73,132,401,52,493,5,241,44,389,156,537,149,297,509,421,161,89],[15,58,96,224,288,96,616,32,15360,49220,101,983040,1049125,6292496,49232,112,851984,1049136,50240,96,332800,8390176,50331744,67649600,32864,96,608,590368]),
([pw30,pw0,pw486,pw1,pw2,pw3,pw4,pw5],[17,68,124,173,521,557,132,144,153,136,128,5,65,389,241,257,509,493,156,89],[7,6,6,14,18,6,38,961,1345,6149,7,57345,65571,2,131140,6,270400,1122,1092,6,1088,1122,70,788484,38,6,1030,270370]),
([pw0,pw1,pw487,pw2,pw3,pw4,pw5],[32,149,401,60,457,144,425,132,397,112,389,72,557,13,453,28,8,5,477,241,449,521,88,273],[7,1,120,408,1560,6168,7,8227,16643,7,16387,104,33160,1544,71688,131168,608,266336,525184,7346560,12584448]),
([pw0,pw1,pw2,pw3,pw488,pw4,pw5],[60,181,128,73,525,29,601,72,5,144,521,137,149,32,100,241,341,112,509,453,68,173,65,89,45,397,12,361,389,537,273],[15,19,39,5,67,19,908,7180,8205,245772,1835148,2098052,4194945,8520576,17826688,100663301,167953412,1313924,268582913,605028481,1074970752]),
([pw0,pw1,pw2,pw3,pw489,pw4,pw5],[60,377,153,124,65,269,17,525,5,421,137,32,20,100,241,112,285,176,449,509,89,45,413,585],[7,27,43,65,7,131,280,1544,6145,122880,917504,1560,25,1081368,2228248,521,1544,393736,4235265,8519681,8577024]),
([pw0,pw1,pw2,pw490,pw3,pw4,pw5],[96,297,17,181,49,445,76,425,144,205,136,421,137,112,241,172,285,509,449],[7,7,7,11,7,51,960,257,7168,122880,393217,8449,3520,960,385,257,257,1281,7168,3073,57345]),
([pw0,pw1,pw491,pw2,pw3,pw4,pw5],[32,149,73,60,153,144,65,457,112,389,453,20,12,413,8,173,477,241,80,449,88,509,273],[7,1,120,152,792,152,7,7,7,771,1027,104,6152,8456,18440,32864,8544,65632,131840,3932160,5243648]),
([pw0,pw1,pw2,pw310,pw3,pw4,pw5],[32,364,3,17,205,24,257,60,180,421,124,521,104,389,740,241,80,537,509,413,493,273],[3,30,236,3848,61512,459016,19,3,3,3,3,1,16914,540690,1048594,3074,61440,262402,3840,20226,2126080]),
([pw492,pw354,pw0,pw1,pw2,pw3,pw4,pw5],[96,76,60,192,149,88,440,68,521,160,361,537,509,17,152,421,557,297,65,5,545,285,89],[7,3,57,67,449,1537,6147,8195,16386,1,49154,16898,67587,139281,8195,24833,1537,6147,786434,1065232,2098704,6161,49154,4456962,18435,18176,51201,1537]),
([pw0,pw493,pw1,pw2,pw3,pw4,pw5],[60,17,377,153,76,65,457,32,20,16,12,0,56,413,557,5,124,421,137,112,285,449],[3,13,53,69,13,21,385,49,1537,14337,16913,32816,458752,1581056,2113552,196656,532528,81968,466944,213008,548880]),
([pw402,pw354,pw0,pw1,pw2,pw3,pw4,pw5],[96,76,73,88,401,192,421,68,545,12,241,36,389,160,509,537,17,152,557,149,297,5,521,65,89],[1,2,60,1,992,15360,49155,65539,131078,1,131138,9218,278531,1638405,2162691,4390977,13313,49154,10485766,340,5140,49159,131138,18882562,409603,5440,147523,9219]),
([pw494,pw354,pw0,pw1,pw2,pw3,pw4,pw5],[88,76,20,3,153,96,552,12,68,545,160,389,509,537,152,421,557,364,5,65,521,241,89],[7,57,3,67,897,3073,12291,16386,16387,1,49154,17410,69635,131089,786434,1065488,2100240,12305,524291,16897,3073,12291,49154,4457474,20483,19968,53249,3073])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def ptopD7 : List StD := [
([pw329,pw0,pw1,pw244,pw3,pw4,pw5,pw330],[17,377,73,401,569,397,241,361,557,88,80,261,49,105,477,137,561,285,45,132,5,553,117,573,449],[3,12,16,32,192,1792,1536,2053,3,3,3,4353,3,12,12,12,8452,12,114688,147520,278784,1589248,192,2130176,4751360,8388928,12582976,16777216]),
([pw329,pw0,pw1,pw244,pw3,pw4,pw306,pw5],[17,377,73,401,425,397,413,116,104,449,509,261,69,117,465,13,337,137,417,89,100,409,421,241,585],[3,12,16,32,448,384,1536,2053,3,3,3,12289,16897,12,12,12,40964,1540,458752,589888,1122304,1536,2228288,4333568,1536,8388608,16777792,16785920]),
([pw329,pw0,pw1,pw2,pw3,pw4,pw331,pw5],[17,377,73,401,425,397,285,56,104,449,509,261,525,549,117,421,137,89,5,557,28,132,241,585],[3,12,16,32,448,384,1536,2053,3,3,3,4097,4609,12,12,12,8196,1540,114688,147520,262144,541184,98368,3178496,1536,4194304,8389184,1536]),
([pw332,pw0,pw1,pw2,pw244,pw3,pw4,pw5],[17,377,73,401,88,137,521,241,361,449,509,261,421,413,117],[3,12,16,16,96,384,1552,2053,3,3,3,3,17,12,12,12,12,1540,16,4128,8320,16912,96,8320,1552,416,48,144]),
([pw332,pw0,pw1,pw2,pw3,pw4,pw5],[17,20,377,60,73,401,88,137,28,521,4,241,0,361,56,449,509,96,261,5,421,132,413,337,557,152],[15,58,64,1920,30720,99392,393297,131077,131205,133125,163905,112,112,112,98384,3670144,13109248,17334336,1058944,98496,33589312]),
([pw0,pw1,pw2,pw3,pw333,pw4,pw5],[73,17,96,88,261,257,181,401,209,137,5,184,128,241,413,337,0,56],[31,38,70,70,38,14,137,137,265,137,13,7680,3072,58368,3076,4,6656,2564,221184,2052,2052]),
([pw0,pw1,pw334,pw36,pw3,pw4,pw5,pw335],[17,149,73,69,5,113,181,37,309,481,597,65,93,241,453,4,173,389,477,205,493,429,521,509,137,573,449],[7,25,32,65,385,513,65,6,3074,6,12290,16386,6,34832,65552,139280,262160,65552,526336,141312,1050624,526336,139264,14680064,16777216,41951232,139264,67108864]),
([pw268,pw0,pw1,pw334,pw36,pw3,pw4,pw5],[17,181,73,149,5,173,65,205,137,241,361,509,69,113,309,49,465,597,93,105,441,4,389,45,449,485,521,501,273],[3,12,48,192,256,1536,2048,13,4113,8192,3,16897,98305,12,131140,12,262660,1572868,2097232,48,4194832,25165840,192,4194880,50331712,1536,218103808,285213184]),
([pw34,pw0,pw2,pw314,pw3,pw4,pw5],[84,5,76,65,73,149,88,209,341,257,17,24,181,545,521,389,241,537,509,565,205,413,337,557,453,116,605,128,429,164],[1,30,116,208,336,85,1546,6688,29184,99840,393793,98,1581058,6324226,8519747,16801825,33652768,393313,67215360,402784321,537034817]),
([pw336,pw0,pw1,pw36,pw3,pw4,pw306,pw5],[17,181,73,149,401,337,425,397,48,413,116,449,509,453,257,37,69,5,465,89,100,537,137,120,173,585],[3,28,96,128,1792,1280,6144,8197,16384,3,33281,196609,264193,20,20,20,8196,6148,96,524832,1179680,2099232,12583424,21102592,6144,8388608,33556992,33687552]),
([pw336,pw0,pw1,pw2,pw3,pw4,pw302,pw5],[17,181,73,149,401,5,173,397,241,361,28,12,132,449,509,261,69,257,457,465,549,89,65,45,389,273,537],[3,28,96,128,768,7168,24576,32773,65569,3,131329,262144,532481,20,20,20,1052676,24580,96,2097440,4194304,8396832,768,5120,24576,16777216,33562880,67117056]),
([pw336,pw0,pw1,pw2,pw36,pw4,pw40,pw5],[17,181,73,149,393,5,173,397,421,253,361,521,429,449,453,69,257,321,465,401,65,413,45,389,100,137,132,537,241,585],[3,28,96,384,1664,2048,12416,16389,32801,65536,132097,3,270337,16420,524292,525316,524292,24580,1048576,2098208,96,4202528,8389632,117440512,134225920,268435456,536880128,167780352]),
([pw337,pw0,pw1,pw2,pw36,pw3,pw4,pw5],[17,181,73,149,401,5,173,20,8,60,52,137,521,241,361,449,509,756,309,481,65,413,477,545,389,537,573],[3,28,96,1920,6144,24576,98304,131077,131105,131072,3,270337,557057,20,20,20,20,98308,1048576,96,2105376,4227104,8390656,16785408,33587200,26624,6144,67149824]),
([pw0,pw1,pw66,pw36,pw91,pw3,pw4,pw5],[73,453,17,153,120,5,136,521,421,389,241,537,449,593,81,413,557,205,273],[3,4,8,112,400,1536,6144,3,8193,3,16513,1537,3,16,112,400,33280,67584,112,131216,1536,6144,96,560,2096,400,400,264704]),
([pw92,pw0,pw83,pw1,pw36,pw3,pw4,pw5],[17,5,69,136,241,413,449,45,60,216,453,73,1,29,149,389,537,425,57,421,273],[7,10,10,10,10,50,194,769,3073,4096,8705,49,577,16384,768,512,32784,65600,394240,524800,528,3136,655872,528,576,48,65600,1048656]),
([pw1,pw66,pw36,pw91,pw3,pw4,pw5],[17,73,52,453,32,593,153,5,117,421,212,81,136,521,413,241,321,557,449,481,216,3,389,68,477,585,573],[15,114,394,3586,1058,1034,85,5253,9729,114689,917505,5328,1050176,7356480,9568320,9856,2114688,16909440,9728,9728,100810752]),
([pw1,pw66,pw2,pw36,pw3,pw4,pw305,pw5],[17,453,73,593,81,421,69,5,28,153,29,321,49,465,65,161,3,389,120,45,100,449,537,137,585],[7,6,10,50,10,10,6,193,769,1057,2049,2049,12289,16384,32928,196736,327808,786560,800,197120,1049088,6291968,393248,8650784,4456480,262144,19005440,6291456]),
([pw92,pw83,pw1,pw66,pw36,pw3,pw4,pw5],[5,144,136,109,69,153,161,25,241,413,449,45,149,216,65,389,537,17,453,73,425,81,421,29,465,273],[7,13,16,37,193,769,3073,4096,8192,16418,8192,33024,66560,917504,1310752,6553600,33024,787456,16416,8527872,768,16909312,16416,33056,66592,768,66560,33555712]),
([pw83,pw1,pw66,pw36,pw3,pw4,pw306,pw5],[149,108,337,153,137,413,3,112,5,208,449,537,17,453,73,425,81,421,93,29,37,69,465,521,241,585],[1,2,12,16,224,832,3072,28672,40964,204800,270368,24832,25600,12,659456,1052704,2101504,4199424,12,12,12,3076,8519712,8519936,3072,16777216,33555488,33555712]),
([pw83,pw1,pw66,pw2,pw3,pw4,pw302,pw5],[149,108,5,3,144,137,241,112,28,153,449,537,17,261,73,109,81,421,93,32,441,69,29,257,465,161,89,65,45,353,389,273],[1,2,28,32,200,784,3072,28672,49156,212992,278592,541184,1065984,2101252,4329472,8392768,768,16782336,33685508,67108932,134217728,268436484,537002048,768,3072,1073741824,2147484736,3584]),
([pw303,pw83,pw1,pw66,pw2,pw3,pw4,pw5],[28,153,341,73,257,17,5,65,241,449,537,149,108,3,144,137,589,389,261,109,81,421,441,29,465,161,337,45],[3,14,50,194,3,256,1538,2048,4096,24640,32768,196608,1536,262164,524356,3145732,12,4194820,48,10485776,48,16777744,35651648,67174464,134218304,196608,1536,197120]),
([pw307,pw1,pw36,pw91,pw3,pw4,pw5],[73,17,453,52,120,5,24,521,421,389,241,321,537,449,481,32,593,153,117,212,81,216,3,68,116,477,585,573],[15,16,122,402,3586,28674,229377,262197,1573009,67073,528389,112,2228368,6424064,10629120,432,16777776,33558576,400,400,201331200]),
([pw307,pw83,pw1,pw36,pw3,pw4,pw306,pw5],[112,17,453,73,257,29,165,37,249,69,5,49,465,209,337,153,397,413,116,108,760,449,537,425,81,421,93,241,585],[1,14,16,98,386,1538,6146,8192,49152,65536,917504,1311744,6291456,8404996,50331652,67239940,12,12,49152,49152,50176,6307840,34734080,34604032,6291456,134217728,269615104,269485056]),
([pw307,pw83,pw1,pw2,pw3,pw4,pw302,pw5],[60,17,261,73,69,5,29,165,37,257,457,49,465,209,3,140,397,241,116,108,28,153,449,537,109,81,421,93,32,441,161,89,65,45,353,389,273],[1,14,50,194,770,1024,6146,8192,49184,65536,917504,3407872,12582912,16777256,100663304,134348808,270532616,541065224,1140850720,2147614752,4294967296,8594128928,17247109120,3145728,12582912,34359738368,68723802112,14680064]),
([pw0,pw1,pw36,pw91,pw161,pw3,pw4,pw5],[17,453,73,153,69,5,120,29,165,37,309,49,465,593,81,197,205,241,389,449,537,24,25,137,421,216,589,585],[7,8,49,64,385,1537,6145,8194,6,8194,49154,8194,6,65632,64,65600,458752,1638400,2097152,12582944,262240,1048672,50331712,67239936,134742016,262208,1048640,67764224]),
([pw0,pw1,pw36,pw91,pw3,pw4,pw305,pw5],[17,453,73,153,69,5,29,165,321,49,465,593,81,421,28,65,205,688],[7,8,49,193,257,257,1537,2050,6,12290,2050,2050,6,49184,90112,196608,196608,196608,139296,131104,131104,131104,139264,139264,139264,131072,131072,131072]),
([pw0,pw1,pw2,pw161,pw3,pw4,pw305,pw5],[17,153,257,321,49,465,5,13,109,593,73,81,421,65,161,3,389,205,45,449,28,397,44,56,585,521,241],[3,3,4,3,9,3,49,448,1536,6656,1536,1536,1536,8192,20544,98368,131136,786496,3149824,12648448,12582912,17301504,33624064,33558528,34082816,67108864,17367040,17301504]),
([pw92,pw0,pw83,pw1,pw161,pw3,pw4,pw5],[17,5,69,205,12,241,413,449,45,153,1,465,149,216,389,537,425,65,81,421,73,441,485,273],[7,10,10,16,10,98,386,513,513,1024,513,97,2177,4096,8192,8192,16416,32896,196608,1835008,16416,3145856,204800,196640,4259968,96,32896,8388768]),
([pw0,pw83,pw1,pw161,pw3,pw4,pw306,pw5],[17,153,257,37,249,49,465,149,140,137,413,3,112,5,205,449,537,425,73,333,81,421,93,441,337,89,44,585,521,241],[3,3,4,3,25,3,97,128,256,512,7168,24576,98304,917504,3407872,4457472,24576,8683520,19005440,33686528,67248128,134381568,270533632,24576,98304,536870912,134251520,134258688]),
([pw0,pw83,pw1,pw2,pw3,pw4,pw338,pw5],[17,153,37,257,457,49,465,149,5,205,137,241,389,700,449,537,81,421,73,441,89,65,45,20,589,273,40,68],[3,3,3,3,13,16,97,128,768,1024,6144,8192,49152,768,458752,6144,270336,802816,768,1050880,2097152,4210944,6144,8527872,49152,16777216,33572864,201342976]),
([pw323,pw0,pw83,pw1,pw2,pw3,pw4,pw5],[257,17,28,112,56,341,73,337,5,521,421,241,585,449,153,149,205,137,537,81,441,45],[3,28,96,384,1540,2048,12288,16393,16417,3,1537,3,12289,32768,65664,131072,24,266240,416,524832,96,1052704,1664,384,2101376,1536,1536,12288]),
([pw0,pw83,pw1,pw2,pw3,pw4,pw339,pw5],[17,153,37,257,49,465,401,5,205,397,241,56,700,449,537,73,93,441,89,45,253,353,28,389,273],[3,3,3,3,13,3,49,64,384,512,7168,6144,24576,384,36864,70656,36864,172032,384,263296,384,532608,3146752,4198400,12288,8388608,16782336,24576]),
([pw308,pw0,pw1,pw2,pw3,pw4,pw305,pw5],[153,17,401,73,205,5,397,421,389,56,44,537,449,321,441,3,45,521,241,585],[3,12,48,192,1792,1536,6144,3,3,3,8449,3,6145,12,12,12,12,18436,48,33040,48,67600,131392,131136,6208,262144,526592,6144]),
([pw308,pw0,pw83,pw1,pw3,pw4,pw306,pw5],[153,17,112,425,73,333,337,89,413,205,5,433,537,37,49,401,397,3,700,449,93,441,521,409,241,585],[3,4,56,72,392,1544,6152,3,3,3,8449,3,20481,32768,65536,393472,1536,528384,262160,1048848,1552,2101264,12583168,1536,528384,16777216,33558784,33559040]),
([pw308,pw0,pw1,pw3,pw4,pw306,pw5],[153,337,17,16,401,425,73,397,421,140,0,48,609,265,481,413,212,5,453,509,521,173,585,180],[15,114,418,1538,2562,4610,533,645,8705,517,16897,464,98384,458768,851984,1147008,3342464,1638528,512,13139968,13238272]),
([pw340,pw0,pw1,pw2,pw4,pw5],[60,133,17,216,149,73,5,173,112,241,361,176,509,180,449,213,477,273],[7,56,200,1792,30720,7,7,11,11,56,792,12312,33096,65608,140032]),
([pw0,pw1,pw36,pw310,pw3,pw4,pw5],[73,17,364,684,24,3,5,421,521,181,389,241,321,537,509,481,205,545,493,764,173,212,273],[15,4,122,898,7170,57346,13,13,13,13,13,65560,458880,592896,352256,1048836,527424,540676,3456,2630020,4727808]),
([pw0,pw1,pw341,pw2,pw3,pw4,pw305,pw5],[17,153,321,49,465,73,453,81,421,341,5,65,205,521,44,389,56,557,449,337,241,585],[3,3,3,3,5,3,25,96,96,416,544,544,96,7168,8448,114688,81920,393216,6400,559104,6144,395264,8448,8448,8448,1048576,2260992,2228224]),
([pw0,pw83,pw1,pw2,pw3,pw4,pw342,pw5],[17,153,241,257,49,465,149,65,205,137,389,108,449,537,425,81,421,73,341,441,101,565,413,273,557],[3,3,3,3,13,3,49,64,384,512,1028,2048,12288,16512,229376,1028,393216,659456,384,16516,384,1052800,1028,2162688,12288,4194304,8392708,16781312]),
([pw343,pw0,pw83,pw1,pw2,pw3,pw4,pw5],[17,153,28,136,73,453,5,65,241,557,449,37,237,149,205,137,413,56,204,537,93,325,521,409,585],[3,12,56,196,12,256,1536,3,3,3,3,6145,1537,8192,16512,32768,458752,524800,48,262160,1114128,48,16512,2162816,1664,12648448,1536,16843264]),
([pw83,pw1,pw66,pw2,pw3,pw4,pw312,pw5],[149,24,65,205,137,241,3,112,28,153,449,537,17,261,73,425,81,421,245,341,441,29,257,465,101,353,389,273],[1,2,12,16,224,768,3072,28672,49156,212992,278560,541184,1065984,12,2232320,4198432,4198912,8393728,12,32804,33284,16778244,33685536,768,3072,67108864,134218784,3584]),
([pw263,pw1,pw66,pw2,pw3,pw4,pw305,pw5],[73,153,453,257,5,421,521,3,389,100,449,537,81,341,65,17,1,321,465,337,101,241,585],[7,8,16,98,386,514,3074,5,5,4129,8449,8193,5,114688,96,164096,163840,295936,96,540928,540672,1065984,96,96,96,2097152,4195584,3072]),
([pw0,pw1,pw344,pw2,pw3,pw4,pw5],[401,17,149,297,12,32,457,425,5,397,96,68,29,493,176,241,285,0,361,56],[15,114,394,7682,1034,1090,1061,24705,18945,98309,17409,24704,18960,950272,17408,19328,16768,17536,18944,3584,17408]),
([pw345,pw1,pw53,pw3,pw4,pw5],[124,5,69,425,477,60,1,65,417,137,112,285,241,132,453,149,301,473,521,573],[7,11,11,11,19,224,769,7168,57344,97,66656,131168,769,262401,527360]),
([pw0,pw1,pw2,pw314,pw346,pw3,pw4,pw5],[73,153,181,152,241,389,457,5,57,209,497,205,65,89,45,493,24,521,545,509,537,124,160,3,429,273],[7,6,10,8,10,50,66,385,513,513,513,49,1025,2056,4224,2056,8336,49160,65536,393216,40,1572864,2228232,12582928,4718600,40,17432576,34078728]),
([pw347,pw0,pw1,pw2,pw314,pw3,pw4,pw5],[17,73,84,76,5,65,60,521,545,389,241,153,181,24,152,457,209,497,205,89,45,493,509,537,429,273],[1,14,56,64,388,1536,12,6146,48,26624,384,1536,34816,50,65538,386,1538,131074,262160,262288,524816,3145744,384,1536,12582912,1664,20971648,37749248]),
([pw0,pw348,pw349,pw2,pw3,pw4,pw5],[76,401,17,149,684,57,421,521,181,389,241,321,537,509,545,73,12,341,205,453,333,45,124,160],[1,30,53,452,3588,12293,26,49,114752,165376,12289,262161,540690,26,19,262241,1048609,2101281,1728,4198465,8393217]),
([pw1,pw66,pw2,pw91,pw3,pw4,pw315,pw5],[73,261,209,453,81,421,245,241,257,205,321,269,37,28,17,277,557,5,521,3,153,449,100,120,389,273],[7,9,9,49,193,9,9,1792,1280,2336,4480,24832,98560,131072,262688,524928,1573376,2163200,262176,4718720,9437184,2162688,262304,1056800,327712,16777216,33620096,3211264]),
([pw282,pw1,pw66,pw2,pw91,pw3,pw4,pw5],[73,153,453,17,3,205,120,241,449,537,81,421,93,329,257,321,269,413,237,557,5,521,389,589],[7,8,50,66,66,128,770,5,5,5,3073,12289,5,49184,49152,83968,409600,540928,1048576,2099232,4325408,524576,2099200,8519680,768,2230272,768,8519936]),
([pw92,pw0,pw1,pw66,pw91,pw3,pw4,pw5],[205,153,28,73,453,52,241,413,449,557,17,65,60,421,521,81,93,273],[7,25,32,5,5,193,769,26,1024,6146,24578,194,770,24,24,40968,65608,24,6144,24576,192,768,26624,192,768,192,768,131392]),
([pw92,pw0,pw1,pw91,pw3,pw4,pw5],[17,205,153,28,73,32,453,65,60,421,521,413,241,3,557,449,68,120,321,481,425,212,81,341,493,585,573],[15,114,394,1546,14338,114690,85,131457,1541,268289,573441,1179856,6423056,10487824,49232,132736,1185920,16957568,7680,50688,100681728]),
([pw0,pw1,pw2,pw91,pw3,pw4,pw319,pw5],[73,153,257,321,17,277,537,453,81,421,245,241,5,521,3,205,52,557,389,56,108,449,565,413,273],[7,10,6,6,6,16,98,129,129,769,3073,129,193,4096,8704,51200,114688,163904,8704,264192,1638400,2097216,10752,4260352,8768,8388608,16779328,131136]),
([pw350,pw0,pw1,pw2,pw91,pw3,pw4,pw5],[257,153,73,453,52,205,3,56,112,421,521,241,557,449,321,81,93,329,5,413,589],[3,12,112,384,1536,2048,12288,3,16417,3,3,3,12289,12,12,33284,196612,12,262144,1568,1572896,12320,1536,384,12288,1536,1536,1576960]),
([pw0,pw1,pw66,pw91,pw3,pw4,pw306,pw5],[73,153,453,17,337,112,421,521,3,413,205,449,537,81,93,100,196,557,241,585],[7,8,50,194,770,1282,6146,5,5,8257,16897,5,5,48,192,33536,66816,133120,208,48,48,6160,192,192,192,262144,526848,134144]),
([pw0,pw1,pw66,pw2,pw3,pw4,pw304,pw5],[73,153,453,17,3,205,421,521,389,136,60,449,537,81,329,337,413,557,5,241,585],[7,8,50,194,274,1538,6146,5,5,8257,16641,5,5,32800,192,65792,1536,133120,224,33056,262144,133152,192,192,192,524288,1050880,6144]),
([pw0,pw83,pw1,pw2,pw3,pw4,pw317,pw5],[17,153,241,257,49,465,149,65,3,144,137,389,28,108,449,537,425,81,421,73,341,441,101,565,413,273,557],[3,3,3,3,13,3,49,64,896,1024,2052,12800,49152,65664,917504,2052,1572864,2637824,65664,65668,65664,4210816,2052,8654848,49152,16777216,33570820,67125248]),
([pw318,pw0,pw83,pw1,pw2,pw3,pw4,pw5],[17,153,28,136,73,453,5,241,557,449,37,237,149,65,3,144,137,413,56,112,537,81,421,93,417,325,521,585],[3,12,56,64,12,128,768,3,3,3,3,3073,769,4096,57344,65536,917504,1048832,48,6291472,8519696,48,20979712,33693696,768,71434240,768,134349056]),
([pw92,pw0,pw1,pw2,pw3,pw4,pw305,pw5],[17,153,73,453,5,421,521,44,389,56,100,557,449,321,81,341,337,65,241,585],[3,12,16,96,896,1536,6144,3,3,3,8449,3,6145,12,16420,33028,32772,12,96,196864,196608,6144,96,96,96,262144,526592,526336]),
([pw0,pw1,pw351,pw91,pw3,pw4,pw5],[73,17,453,153,205,52,24,120,5,521,421,389,241,321,537,449,481,32,593,117,212,81,216,3,68,116,477,585,573],[15,58,450,1674,14338,114690,393233,524677,3146369,268289,1064965,496,4194992,12589072,21020688,1920,33556864,67125632,1664,1664,402671616]),
([pw0,pw83,pw1,pw351,pw3,pw4,pw306,pw5],[17,153,37,249,49,465,209,337,112,140,397,413,116,108,5,760,449,537,425,81,421,73,93,441,241,585],[3,3,3,3,13,3,49,64,896,1024,14336,53248,196608,262272,3670016,4229120,2146304,10551296,262272,34944,49280,196736,1083392,1097728,196608,16777216,33589248,33603584]),
([pw0,pw83,pw1,pw2,pw3,pw4,pw321,pw5],[17,153,37,257,49,465,209,5,3,140,397,241,56,108,28,700,449,537,13,109,81,421,73,93,32,441,161,89,65,45,353,389,273],[3,3,3,3,13,3,49,64,896,1024,14336,53248,196608,786560,7340032,12584960,21004288,37814272,69206144,134219904,268435456,536936576,1075841024,49152,196608,2147483648,4295034880,196608]),
([pw0,pw1,pw2,pw91,pw3,pw4,pw322,pw5],[73,153,229,321,257,277,537,453,81,197,245,241,5,77,205,421,3,52,557,521,56,100,48,108,449,565,389,273],[7,10,18,10,10,10,98,129,129,769,3073,129,193,4096,57344,83968,212992,278592,557056,3147776,13631488,16777280,559104,35684352,557120,67108864,134219840,16777280]),
([pw307,pw1,pw2,pw91,pw3,pw4,pw315,pw5],[73,261,257,321,269,369,37,241,17,277,537,453,81,197,245,5,77,205,421,3,153,557,521,116,100,108,449,389,273],[7,12,12,52,196,256,1540,2049,2049,12289,16513,2049,3073,32768,458752,655488,1703936,2229248,4456448,25165952,42991616,67109888,4456576,18087936,4457472,134217728,268436608,68158464]),
([pw307,pw0,pw1,pw91,pw3,pw4,pw306,pw5],[17,73,453,337,112,52,521,421,413,3,100,205,196,537,449,153,120,81,93,585],[1,6,56,224,1792,6656,24576,6,98312,192,1792,35328,24576,6,131138,262402,6,6,200,1288,1032,24584,192,192,192,65536,525568,534528]),
([pw92,pw0,pw1,pw91,pw161,pw3,pw4,pw5],[17,153,73,205,453,5,60,28,421,77,241,413,449,557,120,593,81,65,521,216,589,585],[3,28,104,128,776,3080,12296,3,16449,16384,3,3073,12289,20,32772,65796,33796,20,131072,262400,3072,12288,540928,1049600,2101248,3328,12544,1053696]),
([pw0,pw1,pw91,pw161,pw3,pw4,pw306,pw5],[17,153,265,112,257,37,309,49,465,453,73,593,81,197,337,521,421,413,120,205,537,196,3,585],[3,13,16,3,97,3,385,1536,2560,12800,2560,1536,1536,16384,98304,393224,786440,1310720,2392064,6422528,6815744,9437184,98304,98304,98304,262144,9568256,9961472]),
([pw0,pw1,pw2,pw161,pw3,pw4,pw304,pw5],[17,153,257,37,309,216,60,49,465,453,73,593,81,197,337,77,205,421,413,389,5,557,449,100,397,56,585,521,241],[3,3,4,3,25,97,385,1536,2560,12800,2560,1568,1536,16384,229376,851968,1048576,6356992,25296896,42205184,96,69206016,134610944,134348832,6422528,268435456,69468160,6291456]),
([pw0,pw1,pw2,pw91,pw3,pw4,pw338,pw5],[17,153,257,457,49,465,453,73,81,197,93,241,32,52,5,77,205,421,413,3,557,449,521,108,124,589,273,80,68],[3,3,5,3,5,8,49,192,192,832,3136,12352,192,16384,229376,329728,524288,3211264,4325376,264192,8388608,3145728,395264,16916480,3276800,33554432,68159488,403701760]),
([pw323,pw0,pw1,pw2,pw91,pw3,pw4,pw5],[257,17,341,73,52,205,3,56,112,421,521,241,585,449,153,453,81,5,589,557],[3,12,112,384,1536,2048,12288,16389,3,3,1537,3,12289,32804,32772,66052,12,36868,131072,1568,262240,528416,1536,384,528384,1536,1536,12288]),
([pw0,pw1,pw2,pw91,pw3,pw4,pw324,pw5],[17,153,257,49,465,453,73,81,197,245,241,65,77,205,421,3,52,557,449,521,56,108,565,389,273],[3,3,5,3,5,5,25,96,96,416,1568,96,96,2048,28672,41984,106496,401408,540672,3146752,3145728,393216,541696,4210688,409600,8388608,16909312,393216]),
([pw352,pw0,pw1,pw91,pw3,pw4,pw306,pw5],[257,73,453,112,421,521,413,3,100,205,537,449,337,17,317,37,153,81,93,89,108,241,585],[1,6,8,48,448,896,3072,6,28672,48,41024,74240,3072,6,131090,262210,6,6,48,528448,1053184,3072,48,48,48,2097152,4195392,4195840]),
([pw353,pw0,pw1,pw91,pw3,pw4,pw5],[68,453,32,73,205,5,120,493,421,521,241,413,156,449,557,257,153,88,81,93],[1,30,240,785,7184,24593,98314,98464,769,7168,24577,170,393473,660482,24585,769,7200,24609,769,769,5121]),
([pw309,pw0,pw1,pw2,pw310,pw3,pw4,pw5],[17,73,76,32,60,421,124,180,241,3,104,509,80,261,257,205,24,269,389,505,597,96,401,81,105,65,77,413,101,521,537,273],[1,14,12,16,224,1792,6148,24578,49664,82432,147488,278784,542720,1081346,6291458,8388642,262402,16779266,33554432,67141664,134250752,268470272,536870944,262400,1075841024,262432,536872992,2147485952]),
([pw0,pw1,pw2,pw310,pw326,pw3,pw4,pw5],[17,153,3,60,257,37,309,49,457,597,73,205,684,149,192,81,93,105,724,77,421,413,241,101,493,521,509,537,124,104,76,273],[3,3,13,16,3,97,385,3584,13312,21504,37888,70656,136192,4096,262144,1574912,6293504,25167872,262144,34603008,6291456,201326592,269500416,538968068,1140867072,7340032,34603008,2216689664]),
([pw328,pw0,pw1,pw2,pw310,pw3,pw4,pw5],[257,73,192,32,684,521,421,389,241,509,537,153,17,24,3,597,205,96,401,81,65,413,101,273],[1,14,16,16,100,384,1540,6146,6144,26624,96,384,1536,98306,393218,524322,386,1538,1048576,96,2162816,4260352,96,384,1536,96,96,8389248]),
([pw311,pw0,pw1,pw2,pw310,pw3,pw4,pw5],[17,32,73,76,24,521,421,241,389,509,537,261,257,3,205,60,597,736,149,5,413,101,273],[1,14,10,16,96,384,1544,6148,28672,45056,96,384,1536,81924,393220,131108,388,1540,524288,96,1065088,2114048,96,384,1536,96,96,4194944]),
([pw354,pw0,pw355,pw1,pw2,pw3,pw4,pw5],[152,153,60,24,149,173,421,521,361,557,509,73,5,65,389,413,105,573],[3,13,17,32,192,257,1536,1,2066,12290,3,16642,1537,2064,12288,193,33024,1537,2064,17,16656,66049,193,37120,1537,193,192,131585])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def ptopD6 : List StD := [
([pw1,pw66,pw91,pw3,pw4,pw302,pw5],[17,261,73,5,109,81,421,93,241,177,153,105,441,69,29,257,28,49,465,137,89,45,449,353,429,389,273,537],[7,28,100,388,1540,6148,8201,16449,33025,66561,393217,524360,1048840,66568,6291464,8388928,66624,20971584,33554432,71303424,138413056]),
([pw303,pw1,pw66,pw91,pw3,pw4,pw5],[177,153,73,257,17,337,5,125,521,241,449,537,261,81,341,441,165,465,25,349,421,585],[7,26,98,386,512,3074,4108,100,8452,16388,33796,24,65800,24,132104,262432,96,3104,1573120,3328,2098176]),
([pw1,pw66,pw36,pw3,pw4,pw304,pw5],[17,453,73,177,153,81,421,93,329,337,29,37,249,69,5,49,465,100,433,537,521,241,585,449],[7,26,98,386,6,6,529,1089,6145,24577,98305,592,528,147472,786448,1048640,1065024,1572928,2097152,4718592,8929280]),
([pw1,pw66,pw36,pw3,pw305,pw306,pw5],[17,453,73,425,153,81,421,93,149,29,37,249,69,5,49,465,337,89,413,433,537,521,241,449,45],[7,26,98,386,6,6,25,577,3073,12289,49153,65608,393224,24,1572872,2359360,2105408,3145792,4464640,9699328,17833984]),
([pw1,pw66,pw2,pw3,pw305,pw302,pw5],[17,261,73,5,109,81,421,93,149,365,153,105,441,69,29,37,257,28,49,465,161,89,241,65,45,449,137,429,273,537],[7,28,100,388,1540,6148,8201,16449,98305,132097,786433,1048648,6291464,8388608,50331656,71303232,132160,167772224,132096,306184192,570426368]),
([pw307,pw1,pw91,pw3,pw4,pw302,pw5],[17,261,73,69,5,29,165,37,257,457,49,465,109,81,141,93,241,32,153,105,441,25,161,89,45,449,253,353,77,421,429,389,273,537],[7,25,97,385,512,3073,4116,24580,98308,393220,1572868,6291472,8454160,393232,50331664,201392128,805568512,1644167168,2147483648,4328587264,8623751168]),
([pw0,pw1,pw161,pw3,pw305,pw306,pw5],[17,153,257,49,465,425,73,221,81,217,93,149,5,109,105,441,337,89,413,44,433,585,521,137,25,421,205,449],[3,4,3,3,3,25,224,832,3136,12352,49216,65568,393248,528416,3145760,12845056,20975616,39845888,67375104,136577024,136318976]),
([pw308,pw0,pw1,pw3,pw305,pw306,pw5],[153,17,221,73,213,421,89,337,413,205,5,433,537,49,441,521,449,45],[3,12,48,448,1664,6272,3,3,3,3,12289,12,12,1540,20484,33040,1552,36880,1792,69888,135680]),
([pw309,pw1,pw36,pw310,pw3,pw4,pw5],[17,76,153,5,29,165,37,241,257,73,205,265,61,81,197,93,105,489,101,493,373,193,69,513,281,253,353,421,429,501,273,509],[3,4,8,49,193,3,1792,6656,25088,33408,197120,1280,1280,1408,786688,3147776,4196480,25167872,100663424,939524096,3221225600]),
([pw311,pw1,pw36,pw310,pw3,pw4,pw5],[17,73,76,69,165,29,309,37,257,205,5,109,81,197,93,241,105,489,101,493,25,137,389,45,449,421,429,501,273,509],[7,5,8,49,193,5,770,3074,12290,49154,196610,768,768,768,786688,3146752,4228096,25166848,4227072,234881024,805339136]),
([pw1,pw66,pw2,pw3,pw312,pw305,pw5],[17,261,73,425,57,81,421,153,341,105,441,1,29,257,49,465,65,101,449,289,241,137,429,28,537],[7,28,100,388,260,1540,2057,4161,8321,8193,49153,65608,65672,65544,393224,524480,3145792,4456512,9437312,17039488,18087936]),
([pw313,pw0,pw1,pw2,pw314,pw3,pw5],[237,153,73,209,65,5,241,389,509,273,457,497,205,45,521,545,537,429],[3,12,48,192,192,832,3,49,3,3,1281,52,12,12,2308,4112,4112,8464,49152,65792,147712]),
([pw1,pw66,pw91,pw3,pw315,pw306,pw5],[37,261,73,425,149,81,421,93,329,241,205,105,441,33,269,413,17,529,53,469,337,89,433,449,565,537,273],[7,28,100,388,1540,6148,8201,16449,98305,131585,786433,1048648,2129928,1544,12582920,16810048,1600,25165888,1536,41975808,75497984]),
([pw1,pw66,pw2,pw3,pw315,pw304,pw5],[37,261,73,425,205,81,421,93,329,241,149,105,441,269,413,17,529,53,469,337,5,433,449,289,137,429,120,537],[7,28,100,388,1540,6148,25,8257,49153,66049,393217,524360,24,1048576,6291464,8405056,16777792,37748800,67125760,138428416,138412544]),
([pw1,pw66,pw316,pw91,pw3,pw4,pw5],[17,261,73,177,153,5,109,81,421,93,329,105,441,257,29,49,465,28,241,389,449,537,137,305,521,585],[7,28,100,388,1540,6148,8209,8225,16641,8193,98305,131120,131344,786448,3145744,4194592,8912928,3145760,17301760,3145984,35127296]),
([pw0,pw1,pw91,pw3,pw4,pw317,pw5],[17,153,65,1,241,257,49,465,425,73,81,197,245,205,341,105,441,101,449,253,353,565,77,421,413,273,557],[3,13,3,49,3,193,260,3584,4624,25088,98816,260,276,260,393220,1572880,6299648,10747904,16777216,33816592,67379200]),
([pw318,pw0,pw1,pw91,pw3,pw4,pw5],[17,153,73,205,453,5,0,421,77,241,449,557,65,1,37,237,81,93,329,137,89,325,521,585],[3,28,104,392,512,3080,3,12289,3,49153,3073,20,65668,393220,20,528512,3149824,3072,4194432,3200,8389632]),
([pw0,pw1,pw91,pw3,pw319,pw306,pw5],[37,153,257,17,53,469,425,73,149,81,217,93,209,241,205,105,441,337,89,413,433,449,565,409,421,52,557],[3,5,3,8,3,49,448,1664,6272,24704,98432,131136,786496,24640,3145792,13107200,24576,23068672,34086912,69730304,69214208]),
([pw320,pw0,pw1,pw91,pw3,pw4,pw5],[17,153,73,205,453,5,0,421,77,241,413,449,557,65,1,81,93,137,273],[3,28,104,392,1544,6152,3,24577,3,1537,6145,20,32900,66052,20,139392,1536,6144,1664,6272,264704]),
([pw0,pw1,pw91,pw3,pw4,pw321,pw5],[17,153,69,5,37,257,49,465,13,109,73,81,197,93,241,32,205,105,441,25,161,89,45,449,253,353,77,421,429,389,273,537],[3,13,3,49,3,193,776,7168,25600,99328,394240,1572872,2113544,98312,12582920,50348032,201392128,411041792,536870912,1082146816,2155937792]),
([pw0,pw1,pw91,pw3,pw322,pw306,pw5],[37,153,257,53,469,425,73,333,81,197,93,329,241,205,105,441,337,89,413,433,449,565,409,421,537,273],[3,5,3,3,3,25,224,832,3136,12352,49216,65568,393248,12320,1572896,6553600,12288,11534336,12288,18087936,34607104]),
([pw307,pw1,pw91,pw3,pw315,pw306,pw5],[37,261,73,257,269,185,17,205,241,53,469,425,233,81,197,93,229,105,441,337,89,153,433,449,565,409,421,537,273],[7,9,49,64,385,1537,6148,24580,98308,388,393220,526336,3147776,384,12584960,52428800,384,92274688,384,144703488,276824192]),
([pw323,pw0,pw1,pw91,pw3,pw306,pw5],[257,17,329,93,337,413,89,409,521,241,205,449,585,153,425,81,73,453,589,433,421],[3,12,112,416,1568,6176,8193,3,8449,9217,6145,16400,98560,197632,198656,16656,263184,526352,263424,1050880,7168]),
([pw0,pw1,pw91,pw3,pw324,pw306,pw5],[17,153,257,49,465,425,73,333,81,197,93,329,241,205,105,441,337,89,413,433,449,565,409,421,537,273],[3,5,3,5,3,25,224,832,3136,12352,49216,65568,393248,12320,1572896,6553600,12288,11534336,12288,18087936,34607104]),
([pw0,pw1,pw2,pw310,pw3,pw325,pw5],[37,261,73,205,257,269,185,389,17,53,469,597,96,401,81,197,241,105,489,65,77,421,413,101,493,521,509,537,273],[7,25,17,97,385,1537,2060,12292,49156,65668,393220,524288,3145736,4194440,25165832,35651584,65664,201330688,65664,35651584,335544448]),
([pw309,pw1,pw2,pw326,pw3,pw4,pw5],[17,153,3,37,241,49,449,265,69,257,73,293,81,197,93,105,489,65,77,193,101,281,269,369,525,253,353,421,429,501,273,509],[3,3,4,3,25,97,384,3584,13312,17424,99328,131072,786560,400,3145856,12583424,16777744,16777728,100663312,939524096,3221225488]),
([pw327,pw0,pw1,pw2,pw310,pw3,pw5],[237,17,241,73,93,205,413,509,273,153,457,597,768,149,81,105,77,421,101,521,537],[3,28,100,68,68,388,521,3,3,513,1153,2088,12296,20488,32904,4096,196640,262304,655360,1048704,655488]),
([pw328,pw311,pw1,pw2,pw3,pw4,pw5],[3,73,149,257,5,137,133,389,237,277,445,17,145,1,65,153,37,457,241,437,21,33,41,429,273],[1,14,16,104,392,1544,6146,26624,34880,67712,134144,4098,4162,262274,525314,1056832,2105472,4203520,262336,8389696,16778368])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def ptopD5 : List StD := [
([pw301,pw1,pw2,pw3,pw4,pw5],[17,73,145,1,65,137,29,241,37,277,49,93,105,437,21,133,33,41,281,157,429,445,273],[7,25,97,385,1537,6,6,2178,12290,49160,65672,393224,557184,3178496,6291584])]
def ptopD4 : List StD := []
theorem ptopI4 : LevelN true ptopT 4 ptopD4 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ptopC5x0 : levelOK true ptopT ptopt 4 (ptopD4.map Prod.fst) ((ptopD5.drop (0*32)).take 32) = true := by decide +kernel
theorem ptopI5 : LevelN true ptopT 5 ptopD5 := levelStep ptopB ptopW ptopI4 (chunks 32 ptopD5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact ptopC5x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ptopC6x0 : levelOK true ptopT ptopt 5 (ptopD5.map Prod.fst) ((ptopD6.drop (0*32)).take 32) = true := by decide +kernel
theorem ptopI6 : LevelN true ptopT 6 ptopD6 := levelStep ptopB ptopW ptopI5 (chunks 32 ptopD6 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact ptopC6x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ptopC7x0 : levelOK true ptopT ptopt 6 (ptopD6.map Prod.fst) ((ptopD7.drop (0*32)).take 32) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ptopC7x1 : levelOK true ptopT ptopt 6 (ptopD6.map Prod.fst) ((ptopD7.drop (1*32)).take 32) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ptopC7x2 : levelOK true ptopT ptopt 6 (ptopD6.map Prod.fst) ((ptopD7.drop (2*32)).take 32) = true := by decide +kernel
theorem ptopI7 : LevelN true ptopT 7 ptopD7 := levelStep ptopB ptopW ptopI6 (chunks 32 ptopD7 3 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact ptopC7x0
  · exact ptopC7x1
  · exact ptopC7x2
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ptopC8x0 : levelOK true ptopT ptopt 7 (ptopD7.map Prod.fst) ((ptopD8.drop (0*32)).take 32) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ptopC8x1 : levelOK true ptopT ptopt 7 (ptopD7.map Prod.fst) ((ptopD8.drop (1*32)).take 32) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ptopC8x2 : levelOK true ptopT ptopt 7 (ptopD7.map Prod.fst) ((ptopD8.drop (2*32)).take 32) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ptopC8x3 : levelOK true ptopT ptopt 7 (ptopD7.map Prod.fst) ((ptopD8.drop (3*32)).take 32) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ptopC8x4 : levelOK true ptopT ptopt 7 (ptopD7.map Prod.fst) ((ptopD8.drop (4*32)).take 32) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ptopC8x5 : levelOK true ptopT ptopt 7 (ptopD7.map Prod.fst) ((ptopD8.drop (5*32)).take 32) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ptopC8x6 : levelOK true ptopT ptopt 7 (ptopD7.map Prod.fst) ((ptopD8.drop (6*32)).take 32) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ptopC8x7 : levelOK true ptopT ptopt 7 (ptopD7.map Prod.fst) ((ptopD8.drop (7*32)).take 32) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ptopC8x8 : levelOK true ptopT ptopt 7 (ptopD7.map Prod.fst) ((ptopD8.drop (8*32)).take 32) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ptopC8x9 : levelOK true ptopT ptopt 7 (ptopD7.map Prod.fst) ((ptopD8.drop (9*32)).take 32) = true := by decide +kernel
theorem ptopI8 : LevelN true ptopT 8 ptopD8 := levelStep ptopB ptopW ptopI7 (chunks 32 ptopD8 10 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact ptopC8x0
  · exact ptopC8x1
  · exact ptopC8x2
  · exact ptopC8x3
  · exact ptopC8x4
  · exact ptopC8x5
  · exact ptopC8x6
  · exact ptopC8x7
  · exact ptopC8x8
  · exact ptopC8x9
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ptopC9x0 : levelOK true ptopT ptopt 8 (ptopD8.map Prod.fst) ((ptopD9.drop (0*32)).take 32) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ptopC9x1 : levelOK true ptopT ptopt 8 (ptopD8.map Prod.fst) ((ptopD9.drop (1*32)).take 32) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ptopC9x2 : levelOK true ptopT ptopt 8 (ptopD8.map Prod.fst) ((ptopD9.drop (2*32)).take 32) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ptopC9x3 : levelOK true ptopT ptopt 8 (ptopD8.map Prod.fst) ((ptopD9.drop (3*32)).take 32) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ptopC9x4 : levelOK true ptopT ptopt 8 (ptopD8.map Prod.fst) ((ptopD9.drop (4*32)).take 32) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ptopC9x5 : levelOK true ptopT ptopt 8 (ptopD8.map Prod.fst) ((ptopD9.drop (5*32)).take 32) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ptopC9x6 : levelOK true ptopT ptopt 8 (ptopD8.map Prod.fst) ((ptopD9.drop (6*32)).take 32) = true := by decide +kernel
theorem ptopI9 : LevelN true ptopT 9 ptopD9 := levelStep ptopB ptopW ptopI8 (chunks 32 ptopD9 7 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact ptopC9x0
  · exact ptopC9x1
  · exact ptopC9x2
  · exact ptopC9x3
  · exact ptopC9x4
  · exact ptopC9x5
  · exact ptopC9x6
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ptopC10x0 : levelOK true ptopT ptopt 9 (ptopD9.map Prod.fst) ((ptopD10.drop (0*32)).take 32) = true := by decide +kernel
theorem ptopI10 : LevelN true ptopT 10 ptopD10 := levelStep ptopB ptopW ptopI9 (chunks 32 ptopD10 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact ptopC10x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ptopC11x0 : levelOK true ptopT ptopt 10 (ptopD10.map Prod.fst) ((ptopD11.drop (0*32)).take 32) = true := by decide +kernel
theorem ptopI11 : LevelN true ptopT 11 ptopD11 := levelStep ptopB ptopW ptopI10 (chunks 32 ptopD11 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact ptopC11x0
  ))
theorem ptopL : LowN true ptopR ptopT 12 := lowSearch ptopB ptopI11 (by decide +kernel)
def sixInputs : List Sig := rootsW [0,1,2,3,4,5]
def graph : Sig := W ptopT
theorem graph_proper : proper graph := (baseOK_ok ptopB).prop
def sample (r : Row) (i : Fin 6) : Bool := bit r (sixInputs.getD i.val zero)
theorem sixList : List.ofFn (fun i : Fin 6 => sixInputs.getD i.val zero) = sixInputs := rfl
theorem sampled (r : Row) : List.ofFn (sample r) = sixInputs.map (bit r) := by
  rw [←sixList,List.map_ofFn]
  rfl
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem sixTable : ∀ r : Row, bit r graph = target (sample r) := by decide +kernel
theorem sixEval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates sixInputs).getD i zero) =
      (C.wires (List.ofFn (sample r))).getD i false := by
  rw [←b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),sampled]
  rfl
theorem physicalSigned (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x)=target x) :
    ∃ k, k ≤ C.gates.countP (fun g => !isNot g) ∧ Live true graph k sixInputs.toFinset := by
  have b := baseOK_ok ptopB
  have goalEq : (execute C.gates sixInputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (sixEval C legal C.output r).trans ((computes (sample r)).trans (sixTable r).symm)
  have out := get_rep (u:=true) (execute C.gates sixInputs) C.output
  rw [goalEq] at out
  unfold Repr at out
  have pg : bit 0 graph = false := by
    change bit 0 (W ptopT) = false
    have := b.plain
    unfold plainWord at this
    simpa using this
  rw [nrm_id pg] at out
  obtain ⟨k,S,hk,run,sub⟩ := extract (u:=true) C.gates sixInputs legal (by simp) graph_proper
    (out.resolve_right (fun h => h graph_proper))
  have ns : sixInputs.all plainWord = true := b.plainR
  rw [nrm_map ns] at sub
  have eq : S = sixInputs.toFinset := by
    ext a
    constructor
    · exact fun h => List.mem_toFinset.mpr (sub a h)
    · intro ha
      obtain ⟨r,s,hd,iso⟩ := b.ess a (List.mem_toFinset.mp ha)
      exact raw_required run sixInputs a sub r s hd iso
  exact ⟨k,hk,eq ▸ run⟩
theorem excludes : Impossible true graph 11 sixInputs.toFinset := by
  intro k small run
  have steps := list_run run sixInputs (by decide +kernel) rfl
  obtain ⟨q, bank, built, hit, limit⟩ := contraction (observe_proper graph_proper)
    steps (sixInputs.map observe) Reach.start (fun _ h => Or.inl h)
  have bound := ptopL q bank built hit
  omega
theorem replaceShort (s : Nat) (h : PEqualNP.MetaComplexity.HasCircuitSize 6 target s) :
    ∃ C : Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = target x := by
  classical
  by_cases big : 13 ≤ s
  · exact ⟨smallCircuit,witnessMonotone,(by rw [witnessSize]; exact big),witnessCorrect⟩
  obtain ⟨C,legal,hs,correct⟩ := h
  by_cases mono : ∀ g ∈ C.gates, g.op ≠ GateOp.not
  · refine ⟨C,?_,hs,correct⟩
    intro g hg
    obtain ⟨ho,hl⟩ := legal g hg
    refine ⟨?_,hl⟩
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ho ⊢
    rcases ho with a | a | a
    · exact Or.inl a
    · exact Or.inr a
    · exact (mono g hg a).elim
  push Not at mono
  obtain ⟨g,hg,hop⟩ := mono
  have lt : C.gates.countP (fun q => !isNot q) < C.gates.length := by
    rcases Nat.lt_or_ge (C.gates.countP (fun q => !isNot q)) C.gates.length with h | h
    · exact h
    · have eq := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length h) g hg
      simp [isNot,hop] at eq
  obtain ⟨k,hk,run⟩ := physicalSigned C legal correct
  have hs' : C.gates.length ≤ s := hs
  exact (excludes k (by omega) run).elim

end PEqualNP.Outside.L_meta_44940

theorem PEqualNP.Outside.L_meta_44940 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075688 * 2 ^ 32 + 4276807904) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075688 * 2 ^ 32 + 4276807904) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s h
  exact PEqualNP.Outside.L_meta_44940.replaceShort s h

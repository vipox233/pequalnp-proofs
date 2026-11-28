import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_32888.Certificate11481
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
def graph : Sig := 0xfffffffffffffffefffefffaeeeeee00fffffffffffffffefffefffaeeeeee00fffffffffffffffefffefffaeeeeee00fffffffffffffffefffefffaeeeeee00
theorem graph_proper : proper graph := by unfold proper; decide +kernel
theorem input_list : List.ofFn (fun j : Fin 9 => inputs.getD j.val zero) = inputs := rfl
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
  (x 0 &&& x 3) ||| (x 1 &&& x 3) ||| (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 2 &&& x 5) ||| (x 3 &&& x 5) ||| (x 0 &&& x 6) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 5 &&& x 6)
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

abbrev Bits := BitVec 700
abbrev Signals := Bits × Bits
abbrev Decor := Sig × Signals

def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def pairSig (r s : Fin 700 → Row) (a : Sig) : Signals := (ofRows r a,ofRows s a)
def properPairs (T : Sig) (r s : Fin 700 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 700 r s (pairSig r s) := by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩
def faithful (r s : Fin 700 → Row) (x : Decor) := x.2 = pairSig r s x.1
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

def asRow (cols : Nat → Bits) (i : Fin 700) : Row :=
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
theorem asRow_bit (cols : Nat → Bits) (i : Fin 700) (j : Fin 9) :
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
  (x 0 &&& x 3) ||| (x 1 &&& x 3) ||| (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 2 &&& x 5) ||| (x 3 &&& x 5) ||| (x 0 &&& x 6) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 5 &&& x 6)
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 700) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then v j.val else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · simpa [vertex,hh] using asRow_bit v i j
  · simp [vertex,hh,bit_zero]
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 700) :
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
    if (rs ||| column d z.2) != BitVec.allOnes 700 then true else
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
  have be : ((restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 700) = false := by
    simpa using sep
  change (if (restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 700 then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
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
theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 700) :
    bit (asRow v i) (chartGoal m) = (chartSamples m v).getLsbD i.val := by
  exact bit_liftGoal m v i
theorem chart_pairs {m : Nat} {p q : Nat → Bits}
    (hp : chartSamples m p = BitVec.allOnes 700) (hq : chartSamples m q = 0) :
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
  (chartSamples g.mask (fun j => (g.samples j).1) == BitVec.allOnes 700) &&
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
def target (x : Fin 7 → Bool) : Bool := decide (∃ i < ([0, 3, 1, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)
def smallCircuit : Circuit := ⟨[
    ⟨.or, [4, 5]⟩,
    ⟨.or, [3, 4]⟩,
    ⟨.or, [6, 8]⟩,
    ⟨.or, [5, 6]⟩,
    ⟨.or, [0, 1]⟩,
    ⟨.or, [2, 3]⟩,
    ⟨.or, [0, 6]⟩,
    ⟨.and, [13, 7]⟩,
    ⟨.and, [10, 12]⟩,
    ⟨.and, [9, 11]⟩,
    ⟨.or, [14, 16]⟩,
    ⟨.or, [15, 17]⟩], 18⟩

theorem witnessMonotone : ∀ g ∈ smallCircuit.gates,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [smallCircuit,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ⟨Or.inl rfl,by decide⟩ | exact ⟨Or.inr rfl,by decide⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem witnessCorrect : ∀ x : Fin 7 → Bool, smallCircuit.eval (List.ofFn x) = target x := by
  decide +kernel

theorem witnessSize : smallCircuit.gates.length = 12 := rfl

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

def lowRow (i : Fin 7) : Row := Fin.ofNat 512 (1 <<< ([3, 3, 5, 0, 0, 0, 0] : List Nat).getD i.val 0)
def highRow (i : Fin 7) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< ([3, 3, 5, 0, 0, 0, 0] : List Nat).getD i.val 0))

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
    (lower : Impossible true graph 10 sevenInputs.toFinset) (gates : List Gate) (o : Nat)
    (fit : ∀ g ∈ gates, (g.op=GateOp.and ∨ g.op=GateOp.or ∨ g.op=GateOp.not) ∧ g.inputs.length≤2)
    (correct : ∀ x : Fin 7 → Bool, (Circuit.mk gates o).eval (List.ofFn x)=target x) :
    ∃ (gs : List Gate) (out : Nat), (∀ g ∈ gs, (g.op=GateOp.and ∨ g.op=GateOp.or) ∧ g.inputs.length≤2) ∧
       gs.length≤gates.length ∧ ∀ x : Fin 7 → Bool, (Circuit.mk gs out).eval (List.ofFn x)=target x := by
  classical
  by_cases big : 12 ≤ gates.length
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

def g74Y : Array (Bits × Bits) := #[(0x0, 0x0),
    (0xbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb, 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0),
    (0x0, 0x0),
    (0xddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd, 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00),
    (0x0, 0x0),
    (0x0, 0x0),
    (0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee, 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000)]
def g74C : List ColumnInfo := []
def g74D3 (j : Nat) : Nat := if j = 0 then 0x7 else 0
def g74L : Nat → Packing
  | 3 => (1, 0, 1, 0, 0, 1, 0, g74D3)
  | _ => emptyPacking
def g74I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g74 : Forest := ⟨74, 3, fun i => (g74Y[i]?).getD (0,0), g74C, [[], [99], [49], [49, 99], [97, 99], [97]], g74L, g74I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g74P3n0 : block g74 3 0 1 = true := by decide +kernel
theorem g74B3 : block g74 3 0 1 = true := g74P3n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g74T : checkedTables g74 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g74 0 0 0 = true)
  · exact (rfl : block g74 1 0 0 = true)
  · exact (rfl : block g74 2 0 0 = true)
  · exact g74B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g74G : graphValid g74 (boundsBefore []) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low74 : Lower true (varsX 74) (graphGoal 74) 4 := lower_forest (g:=g74) (i:=0) (hints:=16781360) (before_sound [] baseKnown) g74G g74T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K74 := extendKnown [] 4 [(74,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V74 : Known true K74 := extend_ok (m:=74) baseKnown low74 (by decide +kernel)

def g82Y : Array (Bits × Bits) := #[(0x0, 0x0),
    (0xbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb, 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0),
    (0x0, 0x0),
    (0x0, 0x0),
    (0xddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd, 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00),
    (0x0, 0x0),
    (0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee, 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000)]
def g82C : List ColumnInfo := []
def g82D3 (j : Nat) : Nat := if j = 0 then 0x7 else 0
def g82L : Nat → Packing
  | 3 => (1, 0, 1, 0, 0, 1, 0, g82D3)
  | _ => emptyPacking
def g82I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g82 : Forest := ⟨82, 3, fun i => (g82Y[i]?).getD (0,0), g82C, [[], [100], [65], [65, 100], [97, 100], [97]], g82L, g82I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g82P3n0 : block g82 3 0 1 = true := by decide +kernel
theorem g82B3 : block g82 3 0 1 = true := g82P3n0
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
theorem g82G : graphValid g82 (boundsBefore K74) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low82 : Lower true (varsX 82) (graphGoal 82) 4 := lower_forest (g:=g82) (i:=0) (hints:=16842816) (before_sound K74 V74) g82G g82T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K82 := extendKnown K74 4 [(82,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V82 : Known true K82 := extend_ok (m:=82) V74 low82 (by decide +kernel)

def g100Y : Array (Bits × Bits) := #[(0x0, 0x0),
    (0x0, 0x0),
    (0xbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb, 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0),
    (0x0, 0x0),
    (0x0, 0x0),
    (0xddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd, 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00),
    (0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee, 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000)]
def g100C : List ColumnInfo := []
def g100D3 (j : Nat) : Nat := if j = 0 then 0x7 else 0
def g100L : Nat → Packing
  | 3 => (1, 0, 1, 0, 0, 1, 0, g100D3)
  | _ => emptyPacking
def g100I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g100 : Forest := ⟨100, 3, fun i => (g100Y[i]?).getD (0,0), g100C, [[], [101], [82], [82, 101], [98, 101], [98]], g100L, g100I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g100P3n0 : block g100 3 0 1 = true := by decide +kernel
theorem g100B3 : block g100 3 0 1 = true := g100P3n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g100T : checkedTables g100 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g100 0 0 0 = true)
  · exact (rfl : block g100 1 0 0 = true)
  · exact (rfl : block g100 2 0 0 = true)
  · exact g100B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g100G : graphValid g100 (boundsBefore K82) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low100 : Lower true (varsX 100) (graphGoal 100) 4 := lower_forest (g:=g100) (i:=0) (hints:=35652864) (before_sound K82 V82) g100G g100T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K100 := extendKnown K82 4 [(100,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V100 : Known true K100 := extend_ok (m:=100) V82 low100 (by decide +kernel)

def g104Y : Array (Bits × Bits) := #[(0x0, 0x0),
    (0x0, 0x0),
    (0x0, 0x0),
    (0xbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb, 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0),
    (0x0, 0x0),
    (0xddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd, 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00),
    (0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee, 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000)]
def g104C : List ColumnInfo := []
def g104D3 (j : Nat) : Nat := if j = 0 then 0x7 else 0
def g104L : Nat → Packing
  | 3 => (1, 0, 1, 0, 0, 1, 0, g104D3)
  | _ => emptyPacking
def g104I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g104 : Forest := ⟨104, 3, fun i => (g104Y[i]?).getD (0,0), g104C, [[], [101], [83], [83, 101], [99, 101], [99]], g104L, g104I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g104P3n0 : block g104 3 0 1 = true := by decide +kernel
theorem g104B3 : block g104 3 0 1 = true := g104P3n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g104T : checkedTables g104 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g104 0 0 0 = true)
  · exact (rfl : block g104 1 0 0 = true)
  · exact (rfl : block g104 2 0 0 = true)
  · exact g104B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g104G : graphValid g104 (boundsBefore K100) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low104 : Lower true (varsX 104) (graphGoal 104) 4 := lower_forest (g:=g104) (i:=0) (hints:=53497856) (before_sound K100 V100) g104G g104T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K104 := extendKnown K100 4 [(104,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V104 : Known true K104 := extend_ok (m:=104) V100 low104 (by decide +kernel)

def g46Y : Array (Bits × Bits) := #[(0x0, 0x0),
    (0xbababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababab, 0xf000000ff00ff00ff000000ff00ff00ff000000ff00ff00ff000000ff00ff00ff000000ff00ff00ff000000ff00ff00ff000000ff00ff00ff000000ff00ff00ff000000ff00ff00ff000000ff00ff00ff000000ff00ff00),
    (0xececececececececececececececececececececececececececececececececececececececececececececececececececececececececececececececececececececececececececececececececececececececece, 0xff00ffff00000000ff00ffff00000000ff00ffff00000000ff00ffff00000000ff00ffff00000000ff00ffff00000000ff00ffff00000000ff00ffff00000000ff00ffff00000000ff00ffff00000000ff00ffff0000),
    (0x3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3, 0xffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff00000000),
    (0x0, 0x0),
    (0xcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc, 0xfff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000),
    (0x0, 0x0)]
def g46C : List ColumnInfo := []
def g46D3 (j : Nat) : Nat := if j = 0 then 0xf else 0
def g46L : Nat → Packing
  | 3 => (1, 0, 1, 0, 0, 1, 0, g46D3)
  | _ => emptyPacking
def g46I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g46 : Forest := ⟨46, 3, fun i => (g46Y[i]?).getD (0,0), g46C, [[], [33, 83]], g46L, g46I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g46P3n0 : block g46 3 0 1 = true := by decide +kernel
theorem g46B3 : block g46 3 0 1 = true := g46P3n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g46T : checkedTables g46 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g46 0 0 0 = true)
  · exact (rfl : block g46 1 0 0 = true)
  · exact (rfl : block g46 2 0 0 = true)
  · exact g46B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g46G : graphValid g46 (boundsBefore K104) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low46 : Lower true (varsX 46) (graphGoal 46) 4 := lower_forest (g:=g46) (i:=0) (hints:=2102576) (before_sound K104 V104) g46G g46T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K46 := extendKnown K104 4 [(46,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V46 : Known true K46 := extend_ok (m:=46) V104 low46 (by decide +kernel)

def g58Y : Array (Bits × Bits) := #[(0x0, 0x0),
    (0x7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7, 0xff00000000ff0000ff00000000ff0000ff00000000ff0000ff00000000ff0000ff00000000ff0000ff00000000ff0000ff00000000ff0000ff00000000ff0000ff00000000ff0000ff00000000ff0000ff00000000ff00),
    (0x0, 0x0),
    (0xddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd, 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000),
    (0x6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6, 0xf0000ffff000000ff0000ffff000000ff0000ffff000000ff0000ffff000000ff0000ffff000000ff0000ffff000000ff0000ffff000000ff0000ffff000000ff0000ffff000000ff0000ffff000000ff0000ffff000000),
    (0x8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8, 0xfffff0000000000ffffff0000000000ffffff0000000000ffffff0000000000ffffff0000000000ffffff0000000000ffffff0000000000ffffff0000000000ffffff0000000000ffffff0000000000ffffff0000000000),
    (0x0, 0x0)]
def g58C : List ColumnInfo := []
def g58D3 (j : Nat) : Nat := if j = 0 then 0xf else 0
def g58L : Nat → Packing
  | 3 => (1, 0, 1, 0, 0, 1, 0, g58D3)
  | _ => emptyPacking
def g58I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g58 : Forest := ⟨58, 3, fun i => (g58Y[i]?).getD (0,0), g58C, [[], [49, 84]], g58L, g58I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g58P3n0 : block g58 3 0 1 = true := by decide +kernel
theorem g58B3 : block g58 3 0 1 = true := g58P3n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g58T : checkedTables g58 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g58 0 0 0 = true)
  · exact (rfl : block g58 1 0 0 = true)
  · exact (rfl : block g58 2 0 0 = true)
  · exact g58B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g58G : graphValid g58 (boundsBefore K46) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low58 : Lower true (varsX 58) (graphGoal 58) 4 := lower_forest (g:=g58) (i:=0) (hints:=3215408) (before_sound K46 V46) g58G g58T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K58 := extendKnown K46 4 [(58,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V58 : Known true K58 := extend_ok (m:=58) V46 low58 (by decide +kernel)

def g78Y : Array (Bits × Bits) := #[(0x0, 0x0),
    (0xaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57, 0x3fe00ff8000000007fc01ff000000000ff803fe000000001ff007fc000000003fe00ff8000000007fc01ff000000000ff803fe000000001ff007fc000000003fe00ff8000000007fc01ff000000000ff803fe00),
    (0x359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359a, 0xff803ffff0000001ff007fffe0000003fe00ffffc0000007fc01ffff8000000ff803ffff0000001ff007fffe0000003fe00ffffc0000007fc01ffff8000000ff803ffff0000001ff007fffe0000003fe00ffffc0000),
    (0xc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3, 0xffffc00000000001ffff800000000003ffff000000000007fffe00000000000ffffc00000000001ffff800000000003ffff000000000007fffe00000000000ffffc00000000001ffff800000000003ffff000000000),
    (0x0, 0x0),
    (0x0, 0x0),
    (0xf9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fc, 0x1ff00000000000003fe00000000000007fc0000000000000ff80000000000001ff00000000000003fe00000000000007fc0000000000000ff80000000000001ff00000000000003fe00000000000007fc0000000000000)]
def g78C : List ColumnInfo := [(4,0,74,0,4)]
def g78D4 (j : Nat) : Nat := if j = 0 then 0x2f else 0
def g78L : Nat → Packing
  | 4 => (1, 0, 1, 0, 0, 1, 0, g78D4)
  | _ => emptyPacking
def g78I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g78 : Forest := ⟨78, 4, fun i => (g78Y[i]?).getD (0,0), g78C, [[], [49]], g78L, g78I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g78P4n0 : block g78 4 0 1 = true := by decide +kernel
theorem g78B4 : block g78 4 0 1 = true := g78P4n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g78T : checkedTables g78 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g78 0 0 0 = true)
  · exact (rfl : block g78 1 0 0 = true)
  · exact (rfl : block g78 2 0 0 = true)
  · exact (rfl : block g78 3 0 0 = true)
  · exact g78B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g78G : graphValid g78 (boundsBefore K58) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low78 : Lower true (varsX 78) (graphGoal 78) 5 := lower_forest (g:=g78) (i:=0) (hints:=16782896) (before_sound K58 V58) g78G g78T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K78 := extendKnown K58 5 [(78,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V78 : Known true K78 := extend_ok (m:=78) V58 low78 (by decide +kernel)

def g86Y : Array (Bits × Bits) := #[(0x0, 0x0),
    (0xaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57, 0x3fe00ff8000000007fc01ff000000000ff803fe000000001ff007fc000000003fe00ff8000000007fc01ff000000000ff803fe000000001ff007fc000000003fe00ff8000000007fc01ff000000000ff803fe00),
    (0x359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359a, 0xff803ffff0000001ff007fffe0000003fe00ffffc0000007fc01ffff8000000ff803ffff0000001ff007fffe0000003fe00ffffc0000007fc01ffff8000000ff803ffff0000001ff007fffe0000003fe00ffffc0000),
    (0x0, 0x0),
    (0xc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3, 0xffffc00000000001ffff800000000003ffff000000000007fffe00000000000ffffc00000000001ffff800000000003ffff000000000007fffe00000000000ffffc00000000001ffff800000000003ffff000000000),
    (0x0, 0x0),
    (0xf9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fc, 0x1ff00000000000003fe00000000000007fc0000000000000ff80000000000001ff00000000000003fe00000000000007fc0000000000000ff80000000000001ff00000000000003fe00000000000007fc0000000000000)]
def g86C : List ColumnInfo := [(4,0,82,0,4)]
def g86D4 (j : Nat) : Nat := if j = 0 then 0x2f else 0
def g86L : Nat → Packing
  | 4 => (1, 0, 1, 0, 0, 1, 0, g86D4)
  | _ => emptyPacking
def g86I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g86 : Forest := ⟨86, 4, fun i => (g86Y[i]?).getD (0,0), g86C, [[], [65]], g86L, g86I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g86P4n0 : block g86 4 0 1 = true := by decide +kernel
theorem g86B4 : block g86 4 0 1 = true := g86P4n0
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
theorem g86G : graphValid g86 (boundsBefore K78) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low86 : Lower true (varsX 86) (graphGoal 86) 5 := lower_forest (g:=g86) (i:=0) (hints:=16844352) (before_sound K78 V78) g86G g86T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K86 := extendKnown K78 5 [(86,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V86 : Known true K86 := extend_ok (m:=86) V78 low86 (by decide +kernel)

def g90Y : Array (Bits × Bits) := #[(0x0, 0x0),
    (0xabeafabeafabeafabeafabeafabeafabeafabeafabeafabeafabeafabeafabeafabeafabeafabeafabeafabeafabeafabeafabeafabeafabeafabeafabeafabeafabeafabeafabeafabeafabeafabeafabeafabeafabeaf, 0xffc000000000000ffc000000000000ffc000000000000ffc000000000000ffc000000000000ffc000000000000ffc000000000000ffc000000000000ffc000000000000ffc000000000000ffc000000000000ffc00),
    (0x0, 0x0),
    (0xcd735cd735cd735cd735cd735cd735cd735cd735cd735cd735cd735cd735cd735cd735cd735cd735cd735cd735cd735cd735cd735cd735cd735cd735cd735cd735cd735cd735cd735cd735cd735cd735cd735cd735cd735, 0x3ff00000003ff003ff00000003ff003ff00000003ff003ff00000003ff003ff00000003ff003ff00000003ff003ff00000003ff003ff00000003ff003ff00000003ff003ff00000003ff003ff00000003ff003ff00000),
    (0xf1bc6f1bc6f1bc6f1bc6f1bc6f1bc6f1bc6f1bc6f1bc6f1bc6f1bc6f1bc6f1bc6f1bc6f1bc6f1bc6f1bc6f1bc6f1bc6f1bc6f1bc6f1bc6f1bc6f1bc6f1bc6f1bc6f1bc6f1bc6f1bc6f1bc6f1bc6f1bc6f1bc6f1bc6f1bc6, 0xffc0000000003ffffc0000000003ffffc0000000003ffffc0000000003ffffc0000000003ffffc0000000003ffffc0000000003ffffc0000000003ffffc0000000003ffffc0000000003ffffc0000000003ffffc0000000),
    (0x0, 0x0),
    (0xfe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8, 0xffc000000000000ffc000000000000ffc000000000000ffc000000000000ffc000000000000ffc000000000000ffc000000000000ffc000000000000ffc000000000000ffc000000000000ffc000000000000)]
def g90C : List ColumnInfo := [(8,0,82,0,4)]
def g90D4 (j : Nat) : Nat := if j = 0 then 0x2f else 0
def g90L : Nat → Packing
  | 4 => (1, 0, 1, 0, 0, 1, 0, g90D4)
  | _ => emptyPacking
def g90I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g90 : Forest := ⟨90, 4, fun i => (g90Y[i]?).getD (0,0), g90C, [[], [67], [97], [97, 67]], g90L, g90I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g90P4n0 : block g90 4 0 1 = true := by decide +kernel
theorem g90B4 : block g90 4 0 1 = true := g90P4n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g90T : checkedTables g90 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g90 0 0 0 = true)
  · exact (rfl : block g90 1 0 0 = true)
  · exact (rfl : block g90 2 0 0 = true)
  · exact (rfl : block g90 3 0 0 = true)
  · exact g90B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g90G : graphValid g90 (boundsBefore K86) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low90 : Lower true (varsX 90) (graphGoal 90) 5 := lower_forest (g:=g90) (i:=0) (hints:=16846896) (before_sound K86 V86) g90G g90T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K90 := extendKnown K86 5 [(90,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V90 : Known true K90 := extend_ok (m:=90) V86 low90 (by decide +kernel)

def g102Y : Array (Bits × Bits) := #[(0x0, 0x0),
    (0xad56ab55aad56ab55aad56ab55aad56ab55aad56ab55aad56ab55aad56ab55aad56ab55aad56ab55aad56ab55aad56ab55aad56ab55aad56ab55aad56ab55aad56ab55aad56ab55aad56ab55aad56ab55aad56ab55aad56, 0xff803fe00ff80001ff007fc01ff00003fe00ff803fe00007fc01ff007fc0000ff803fe00ff80001ff007fc01ff00003fe00ff803fe00007fc01ff007fc0000ff803fe00ff80001ff007fc01ff00003fe00ff803fe00),
    (0x379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379b, 0x3ffff000000000007fffe00000000000ffffc00000000001ffff800000000003ffff000000000007fffe00000000000ffffc00000000001ffff800000000003ffff000000000007fffe00000000000ffffc0000),
    (0x0, 0x0),
    (0x0, 0x0),
    (0xc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3, 0xffffc00000000001ffff800000000003ffff000000000007fffe00000000000ffffc00000000001ffff800000000003ffff000000000007fffe00000000000ffffc00000000001ffff800000000003ffff000000000),
    (0xf9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fc, 0x1ff00000000000003fe00000000000007fc0000000000000ff80000000000001ff00000000000003fe00000000000007fc0000000000000ff80000000000001ff00000000000003fe00000000000007fc0000000000000)]
def g102C : List ColumnInfo := [(2,0,100,0,4)]
def g102D4 (j : Nat) : Nat := if j = 0 then 0x2f else 0
def g102L : Nat → Packing
  | 4 => (1, 0, 1, 0, 0, 1, 0, g102D4)
  | _ => emptyPacking
def g102I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g102 : Forest := ⟨102, 4, fun i => (g102Y[i]?).getD (0,0), g102C, [[], [82]], g102L, g102I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g102P4n0 : block g102 4 0 1 = true := by decide +kernel
theorem g102B4 : block g102 4 0 1 = true := g102P4n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g102T : checkedTables g102 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g102 0 0 0 = true)
  · exact (rfl : block g102 1 0 0 = true)
  · exact (rfl : block g102 2 0 0 = true)
  · exact (rfl : block g102 3 0 0 = true)
  · exact g102B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g102G : graphValid g102 (boundsBefore K90) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low102 : Lower true (varsX 102) (graphGoal 102) 5 := lower_forest (g:=g102) (i:=0) (hints:=18875744) (before_sound K90 V90) g102G g102T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K102 := extendKnown K90 5 [(102,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V102 : Known true K102 := extend_ok (m:=102) V90 low102 (by decide +kernel)

def g106Y : Array (Bits × Bits) := #[(0x0, 0x0),
    (0xab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6ad, 0xffc00003ff00000ffc00003ff00000ffc00003ff00000ffc00003ff00000ffc00003ff00000ffc00003ff00000ffc00003ff00000ffc00003ff00000ffc00003ff00000ffc00003ff00000ffc00003ff00000ffc00),
    (0x0, 0x0),
    (0xcdf37cdf37cdf37cdf37cdf37cdf37cdf37cdf37cdf37cdf37cdf37cdf37cdf37cdf37cdf37cdf37cdf37cdf37cdf37cdf37cdf37cdf37cdf37cdf37cdf37cdf37cdf37cdf37cdf37cdf37cdf37cdf37cdf37cdf37cdf37, 0x3ff0000000000003ff0000000000003ff0000000000003ff0000000000003ff0000000000003ff0000000000003ff0000000000003ff0000000000003ff0000000000003ff0000000000003ff0000000000003ff00000),
    (0x0, 0x0),
    (0xf1bc6f1bc6f1bc6f1bc6f1bc6f1bc6f1bc6f1bc6f1bc6f1bc6f1bc6f1bc6f1bc6f1bc6f1bc6f1bc6f1bc6f1bc6f1bc6f1bc6f1bc6f1bc6f1bc6f1bc6f1bc6f1bc6f1bc6f1bc6f1bc6f1bc6f1bc6f1bc6f1bc6f1bc6f1bc6, 0xffc0000000003ffffc0000000003ffffc0000000003ffffc0000000003ffffc0000000003ffffc0000000003ffffc0000000003ffffc0000000003ffffc0000000003ffffc0000000003ffffc0000000003ffffc0000000),
    (0xfe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8, 0xffc000000000000ffc000000000000ffc000000000000ffc000000000000ffc000000000000ffc000000000000ffc000000000000ffc000000000000ffc000000000000ffc000000000000ffc000000000000)]
def g106C : List ColumnInfo := [(2,0,104,0,4)]
def g106D4 (j : Nat) : Nat := if j = 0 then 0x2f else 0
def g106L : Nat → Packing
  | 4 => (1, 0, 1, 0, 0, 1, 0, g106D4)
  | _ => emptyPacking
def g106I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g106 : Forest := ⟨106, 4, fun i => (g106Y[i]?).getD (0,0), g106C, [[], [99], [81], [81, 99]], g106L, g106I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g106P4n0 : block g106 4 0 1 = true := by decide +kernel
theorem g106B4 : block g106 4 0 1 = true := g106P4n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g106T : checkedTables g106 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g106 0 0 0 = true)
  · exact (rfl : block g106 1 0 0 = true)
  · exact (rfl : block g106 2 0 0 = true)
  · exact (rfl : block g106 3 0 0 = true)
  · exact g106B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g106G : graphValid g106 (boundsBefore K102) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low106 : Lower true (varsX 106) (graphGoal 106) 5 := lower_forest (g:=g106) (i:=0) (hints:=19927088) (before_sound K102 V102) g106G g106T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K106 := extendKnown K102 5 [(106,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V106 : Known true K106 := extend_ok (m:=106) V102 low106 (by decide +kernel)

def g108Y : Array (Bits × Bits) := #[(0x0, 0x0),
    (0x0, 0x0),
    (0xab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6ad, 0xffc00ffc0000000ffc00ffc0000000ffc00ffc0000000ffc00ffc0000000ffc00ffc0000000ffc00ffc0000000ffc00ffc0000000ffc00ffc0000000ffc00ffc0000000ffc00ffc0000000ffc00ffc0000000ffc00ffc00),
    (0xcdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36, 0xfffff0000000000fffff0000000000fffff0000000000fffff0000000000fffff0000000000fffff0000000000fffff0000000000fffff0000000000fffff0000000000fffff0000000000fffff0000000000fffff00000),
    (0x0, 0x0),
    (0xf1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7, 0x3ff0000000000003ff0000000000003ff0000000000003ff0000000000003ff0000000000003ff0000000000003ff0000000000003ff0000000000003ff0000000000003ff0000000000003ff0000000000),
    (0xfe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8, 0xffc000000000000ffc000000000000ffc000000000000ffc000000000000ffc000000000000ffc000000000000ffc000000000000ffc000000000000ffc000000000000ffc000000000000ffc000000000000)]
def g108C : List ColumnInfo := [(4,0,104,0,4)]
def g108D4 (j : Nat) : Nat := if j = 0 then 0x2f else 0
def g108L : Nat → Packing
  | 4 => (1, 0, 1, 0, 0, 1, 0, g108D4)
  | _ => emptyPacking
def g108I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g108 : Forest := ⟨108, 4, fun i => (g108Y[i]?).getD (0,0), g108C, [[], [101], [50], [50, 101]], g108L, g108I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g108P4n0 : block g108 4 0 1 = true := by decide +kernel
theorem g108B4 : block g108 4 0 1 = true := g108P4n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g108T : checkedTables g108 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g108 0 0 0 = true)
  · exact (rfl : block g108 1 0 0 = true)
  · exact (rfl : block g108 2 0 0 = true)
  · exact (rfl : block g108 3 0 0 = true)
  · exact g108B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g108G : graphValid g108 (boundsBefore K106) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low108 : Lower true (varsX 108) (graphGoal 108) 5 := lower_forest (g:=g108) (i:=0) (hints:=35673344) (before_sound K106 V106) g108G g108T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K108 := extendKnown K106 5 [(108,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V108 : Known true K108 := extend_ok (m:=108) V106 low108 (by decide +kernel)

def g114Y : Array (Bits × Bits) := #[(0x0, 0x0),
    (0xaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57, 0x7fc0000ff8000000ff80001ff0000001ff00003fe0000003fe00007fc0000007fc0000ff8000000ff80001ff0000001ff00003fe0000003fe00007fc0000007fc0000ff8000000ff80001ff0000001ff00003fe00),
    (0x0, 0x0),
    (0x0, 0x0),
    (0x379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379b, 0xff80001ff0000001ff00003fe0000003fe00007fc0000007fc0000ff8000000ff80001ff0000001ff00003fe0000003fe00007fc0000007fc0000ff8000000ff80001ff0000001ff00003fe0000003fe00007fc0000),
    (0xc5e2f178bc5e2f178bc5e2f178bc5e2f178bc5e2f178bc5e2f178bc5e2f178bc5e2f178bc5e2f178bc5e2f178bc5e2f178bc5e2f178bc5e2f178bc5e2f178bc5e2f178bc5e2f178bc5e2f178bc5e2f178bc5e2f178bc5e2, 0xffffffe000000001ffffffc000000003ffffff8000000007ffffff000000000ffffffe000000001ffffffc000000003ffffff8000000007ffffff000000000ffffffe000000001ffffffc000000003ffffff8000000),
    (0xf9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fc, 0x1ff00000000000003fe00000000000007fc0000000000000ff80000000000001ff00000000000003fe00000000000007fc0000000000000ff80000000000001ff00000000000003fe00000000000007fc0000000000000)]
def g114C : List ColumnInfo := [(32,0,82,0,4)]
def g114D4 (j : Nat) : Nat := if j = 0 then 0x2f else 0
def g114L : Nat → Packing
  | 4 => (1, 0, 1, 0, 0, 1, 0, g114D4)
  | _ => emptyPacking
def g114I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g114 : Forest := ⟨114, 4, fun i => (g114Y[i]?).getD (0,0), g114C, [[], [65]], g114L, g114I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g114P4n0 : block g114 4 0 1 = true := by decide +kernel
theorem g114B4 : block g114 4 0 1 = true := g114P4n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g114T : checkedTables g114 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g114 0 0 0 = true)
  · exact (rfl : block g114 1 0 0 = true)
  · exact (rfl : block g114 2 0 0 = true)
  · exact (rfl : block g114 3 0 0 = true)
  · exact g114B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g114G : graphValid g114 (boundsBefore K108) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low114 : Lower true (varsX 114) (graphGoal 114) 5 := lower_forest (g:=g114) (i:=0) (hints:=23134272) (before_sound K108 V108) g114G g114T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K114 := extendKnown K108 5 [(114,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V114 : Known true K114 := extend_ok (m:=114) V108 low114 (by decide +kernel)

def g116Y : Array (Bits × Bits) := #[(0x0, 0x0),
    (0x0, 0x0),
    (0xaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57, 0x3fe00ff8000000007fc01ff000000000ff803fe000000001ff007fc000000003fe00ff8000000007fc01ff000000000ff803fe000000001ff007fc000000003fe00ff8000000007fc01ff000000000ff803fe00),
    (0x0, 0x0),
    (0x359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359a, 0xff803ffff0000001ff007fffe0000003fe00ffffc0000007fc01ffff8000000ff803ffff0000001ff007fffe0000003fe00ffffc0000007fc01ffff8000000ff803ffff0000001ff007fffe0000003fe00ffffc0000),
    (0xc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3, 0xffffc00000000001ffff800000000003ffff000000000007fffe00000000000ffffc00000000001ffff800000000003ffff000000000007fffe00000000000ffffc00000000001ffff800000000003ffff000000000),
    (0xf9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fc, 0x1ff00000000000003fe00000000000007fc0000000000000ff80000000000001ff00000000000003fe00000000000007fc0000000000000ff80000000000001ff00000000000003fe00000000000007fc0000000000000)]
def g116C : List ColumnInfo := [(16,0,100,0,4)]
def g116D4 (j : Nat) : Nat := if j = 0 then 0x2f else 0
def g116L : Nat → Packing
  | 4 => (1, 0, 1, 0, 0, 1, 0, g116D4)
  | _ => emptyPacking
def g116I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g116 : Forest := ⟨116, 4, fun i => (g116Y[i]?).getD (0,0), g116C, [[], [82]], g116L, g116I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g116P4n0 : block g116 4 0 1 = true := by decide +kernel
theorem g116B4 : block g116 4 0 1 = true := g116P4n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g116T : checkedTables g116 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g116 0 0 0 = true)
  · exact (rfl : block g116 1 0 0 = true)
  · exact (rfl : block g116 2 0 0 = true)
  · exact (rfl : block g116 3 0 0 = true)
  · exact g116B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g116G : graphValid g116 (boundsBefore K114) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low116 : Lower true (varsX 116) (graphGoal 116) 5 := lower_forest (g:=g116) (i:=0) (hints:=36046080) (before_sound K114 V114) g116G g116T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K116 := extendKnown K114 5 [(116,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V116 : Known true K116 := extend_ok (m:=116) V114 low116 (by decide +kernel)

def g120Y : Array (Bits × Bits) := #[(0x0, 0x0),
    (0x0, 0x0),
    (0x0, 0x0),
    (0xaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57, 0x3fe00ff8000000007fc01ff000000000ff803fe000000001ff007fc000000003fe00ff8000000007fc01ff000000000ff803fe000000001ff007fc000000003fe00ff8000000007fc01ff000000000ff803fe00),
    (0x359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359a, 0xff803ffff0000001ff007fffe0000003fe00ffffc0000007fc01ffff8000000ff803ffff0000001ff007fffe0000003fe00ffffc0000007fc01ffff8000000ff803ffff0000001ff007fffe0000003fe00ffffc0000),
    (0xc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3, 0xffffc00000000001ffff800000000003ffff000000000007fffe00000000000ffffc00000000001ffff800000000003ffff000000000007fffe00000000000ffffc00000000001ffff800000000003ffff000000000),
    (0xf9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fc, 0x1ff00000000000003fe00000000000007fc0000000000000ff80000000000001ff00000000000003fe00000000000007fc0000000000000ff80000000000001ff00000000000003fe00000000000007fc0000000000000)]
def g120C : List ColumnInfo := [(16,0,104,0,4)]
def g120D4 (j : Nat) : Nat := if j = 0 then 0x2f else 0
def g120L : Nat → Packing
  | 4 => (1, 0, 1, 0, 0, 1, 0, g120D4)
  | _ => emptyPacking
def g120I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g120 : Forest := ⟨120, 4, fun i => (g120Y[i]?).getD (0,0), g120C, [[], [83]], g120L, g120I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g120P4n0 : block g120 4 0 1 = true := by decide +kernel
theorem g120B4 : block g120 4 0 1 = true := g120P4n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g120T : checkedTables g120 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g120 0 0 0 = true)
  · exact (rfl : block g120 1 0 0 = true)
  · exact (rfl : block g120 2 0 0 = true)
  · exact (rfl : block g120 3 0 0 = true)
  · exact g120B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g120G : graphValid g120 (boundsBefore K116) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low120 : Lower true (varsX 120) (graphGoal 120) 5 := lower_forest (g:=g120) (i:=0) (hints:=53891072) (before_sound K116 V116) g120G g120T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K120 := extendKnown K116 5 [(120,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V120 : Known true K120 := extend_ok (m:=120) V116 low120 (by decide +kernel)

def g62Y : Array (Bits × Bits) := #[(0x0, 0x0),
    (0x5abfab57f56afead5fd5abfab57f56afead5fd5abfab57f56afead5fd5abfab57f56afead5fd5abfab57f56afead5fd5abfab57f56afead5fd5abfab57f56afead5fd5abfab57f56afead5fd5abfab57f56afead5fd5abf, 0x3ffff80000ffffe0000000007ffff0000000000000000000000000000000007ffff00001ffffc000000000ffffe000000000000000000000000000000000ffffe00003ffff80000),
    (0x6ceacd9d59b3ab367566ceacd9d59b3ab367566ceacd9d59b3ab367566ceacd9d59b3ab367566ceacd9d59b3ab367566ceacd9d59b3ab367566ceacd9d59b3ab367566ceacd9d59b3ab367566ceacd9d59b3ab367566cea, 0xffffe00003ffff80000ffffe00003fffffffff000000000000000000000001ffffc00007ffff00001ffffc00007ffffffffe000000000000000000000003ffff80000ffffe00003ffff80000fffffffffc000000000),
    (0x8f33f1e67e3ccfc799f8f33f1e67e3ccfc799f8f33f1e67e3ccfc799f8f33f1e67e3ccfc799f8f33f1e67e3ccfc799f8f33f1e67e3ccfc799f8f33f1e67e3ccfc799f8f33f1e67e3ccfc799f8f33f1e67e3ccfc799f8f33, 0xfffffffffc000000000fffffffffc000000000000000000000000000000001fffffffff8000000001fffffffff8000000000000000000000000000000003fffffffff0000000003fffffffff0000000000000000000),
    (0xf03cfe079fc0f3f81e7f03cfe079fc0f3f81e7f03cfe079fc0f3f81e7f03cfe079fc0f3f81e7f03cfe079fc0f3f81e7f03cfe079fc0f3f81e7f03cfe079fc0f3f81e7f03cfe079fc0f3f81e7f03cfe079fc0f3f81e7f03c, 0xfffffffffffffffffff00000000000000000000000000003ffff8000000001ffffffffffffffffffe00000000000000000000000000007ffff0000000003ffffffffffffffffffc0000000000000000000000000000),
    (0xffc0fff81fff03ffe07ffc0fff81fff03ffe07ffc0fff81fff03ffe07ffc0fff81fff03ffe07ffc0fff81fff03ffe07ffc0fff81fff03ffe07ffc0fff81fff03ffe07ffc0fff81fff03ffe07ffc0fff81fff03ffe07ffc0, 0xffff000000000000000000000000000000000000000000000003fffffffffffffe000000000000000000000000000000000000000000000007fffffffffffffc00000000000000000000000000000000000000000000000),
    (0x0, 0x0)]
def g62C : List ColumnInfo := []
def g62D4 (j : Nat) : Nat := if j = 0 then 0x1f else 0
def g62L : Nat → Packing
  | 4 => (1, 0, 1, 0, 0, 1, 0, g62D4)
  | _ => emptyPacking
def g62I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g62 : Forest := ⟨62, 4, fun i => (g62Y[i]?).getD (0,0), g62C, [[], [81, 66]], g62L, g62I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g62P4n0 : block g62 4 0 1 = true := by decide +kernel
theorem g62B4 : block g62 4 0 1 = true := g62P4n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g62T : checkedTables g62 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g62 0 0 0 = true)
  · exact (rfl : block g62 1 0 0 = true)
  · exact (rfl : block g62 2 0 0 = true)
  · exact (rfl : block g62 3 0 0 = true)
  · exact g62B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g62G : graphValid g62 (boundsBefore K120) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low62 : Lower true (varsX 62) (graphGoal 62) 5 := lower_forest (g:=g62) (i:=0) (hints:=2168112) (before_sound K120 V120) g62G g62T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K62 := extendKnown K120 5 [(62,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V62 : Known true K62 := extend_ok (m:=62) V120 low62 (by decide +kernel)

def g94Y : Array (Bits × Bits) := #[(0x0, 0x0),
    (0xff5557faaabfd555feaaaff5557faaabfd555feaaaff5557faaabfd555feaaaff5557faaabfd555feaaaff5557faaabfd555feaaaff5557faaabfd555feaaaff5557faaabfd555feaaaff5557faaabfd555feaaaff5557f, 0x3ffffe00000fffff8000000000000000000000000000000000000000007ffffc00001fffff000000000000000000000000000000000000000000fffff800003ffffe00000),
    (0x55999aacccd56666ab33355999aacccd56666ab33355999aacccd56666ab33355999aacccd56666ab33355999aacccd56666ab33355999aacccd56666ab33355999aacccd56666ab33355999aacccd56666ab33355999aa, 0xfffff800003ffffe00000fffff800003ffffffffff0000000000000001fffff000007ffffc00001fffff000007fffffffffe0000000000000003ffffe00000fffff800003ffffe00000ffffffffffc0000000000),
    (0x67e1e33f0f19f878cfc3c67e1e33f0f19f878cfc3c67e1e33f0f19f878cfc3c67e1e33f0f19f878cfc3c67e1e33f0f19f878cfc3c67e1e33f0f19f878cfc3c67e1e33f0f19f878cfc3c67e1e33f0f19f878cfc3c67e1e33, 0xffffffffffc0000000000ffffffffffc00000000000000000000000001ffffffffff80000000001ffffffffff800000000000000000000000003ffffffffff00000000003ffffffffff000000000000000000000),
    (0x79fe03cff01e7f80f3fc079fe03cff01e7f80f3fc079fe03cff01e7f80f3fc079fe03cff01e7f80f3fc079fe03cff01e7f80f3fc079fe03cff01e7f80f3fc079fe03cff01e7f80f3fc079fe03cff01e7f80f3fc079fe03c, 0xfffffffffffffffffffff0000000000000000000000000000000000001ffffffffffffffffffffe0000000000000000000000000000000000003ffffffffffffffffffffc0000000000000000000000000000000),
    (0x0, 0x0),
    (0x81fffc0fffe07fff03fff81fffc0fffe07fff03fff81fffc0fffe07fff03fff81fffc0fffe07fff03fff81fffc0fffe07fff03fff81fffc0fffe07fff03fff81fffc0fffe07fff03fff81fffc0fffe07fff03fff81fffc0, 0x1fffff00000000000000000000000000000000000000000000000000003ffffe00000000000000000000000000000000000000000000000000007ffffc0000000000000000000000000000000000000000000000000000)]
def g94C : List ColumnInfo := [(4,0,90,0,5)]
def g94D5 (j : Nat) : Nat := if j = 0 then 0x5f else 0
def g94L : Nat → Packing
  | 5 => (1, 0, 1, 0, 0, 1, 0, g94D5)
  | _ => emptyPacking
def g94I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g94 : Forest := ⟨94, 5, fun i => (g94Y[i]?).getD (0,0), g94C, [[], [67]], g94L, g94I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g94P5n0 : block g94 5 0 1 = true := by decide +kernel
theorem g94B5 : block g94 5 0 1 = true := g94P5n0
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
theorem g94G : graphValid g94 (boundsBefore K62) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low94 : Lower true (varsX 94) (graphGoal 94) 6 := lower_forest (g:=g94) (i:=0) (hints:=16848432) (before_sound K62 V62) g94G g94T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K94 := extendKnown K62 6 [(94,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V94 : Known true K94 := extend_ok (m:=94) V62 low94 (by decide +kernel)

def g110Y : Array (Bits × Bits) := #[(0x0, 0x0),
    (0x6aeaaad5d555abaaab575556aeaaad5d555abaaab575556aeaaad5d555abaaab575556aeaaad5d555abaaab575556aeaaad5d555abaaab575556aeaaad5d555abaaab575556aeaaad5d555abaaab575556aeaaad5d555ab, 0xffc000007fffff000000000003fffff800000000000000003fffff800000fffffe000000000007fffff000000000000000007fffff000001fffffc00000000000fffffe00000000000000000fffffe000003fffff800000),
    (0xb3b333676666cecccd9d999b3b333676666cecccd9d999b3b333676666cecccd9d999b3b333676666cecccd9d999b3b333676666cecccd9d999b3b333676666cecccd9d999b3b333676666cecccd9d999b3b333676666ce, 0xffffffff80000000000000000000000000000fffffe000003fffffffffff00000000000000000000000000001fffffc000007ffffffffffe00000000000000000000000000003fffff800000fffffffffffc00000000000),
    (0x3cfc3c79f878f3f0f1e7e1e3cfc3c79f878f3f0f1e7e1e3cfc3c79f878f3f0f1e7e1e3cfc3c79f878f3f0f1e7e1e3cfc3c79f878f3f0f1e7e1e3cfc3c79f878f3f0f1e7e1e3cfc3c79f878f3f0f1e7e1e3cfc3c79f878f3, 0xfffffffffffc0000000000000000000000000000000000000001fffffffffff80000000000000000000000000000000000000003fffffffffff00000000000000000000000),
    (0x0, 0x0),
    (0x3f3fc07e7f80fcff01f9fe03f3fc07e7f80fcff01f9fe03f3fc07e7f80fcff01f9fe03f3fc07e7f80fcff01f9fe03f3fc07e7f80fcff01f9fe03f3fc07e7f80fcff01f9fe03f3fc07e7f80fcff01f9fe03f3fc07e7f80fc, 0x3fffffffffff00000000000000000000000000000000000000007ffffffffffe0000000000000000000000000000000000000000fffffffffffc0000000000000000000000000000000000),
    (0xc03fff807fff00fffe01fffc03fff807fff00fffe01fffc03fff807fff00fffe01fffc03fff807fff00fffe01fffc03fff807fff00fffe01fffc03fff807fff00fffe01fffc03fff807fff00fffe01fffc03fff807fff00, 0x1fffffc0000000000000000000000000000000000000000000003fffff80000000000000000000000000000000000000000000007fffff0000000000000000000000000000000000000000000000)]
def g110C : List ColumnInfo := [(2,0,108,0,5), (4,0,106,0,5), (8,0,102,0,5), (32,0,78,0,5)]
def g110D6 (j : Nat) : Nat := if j = 0 then 0xe411f else 0
def g110L : Nat → Packing
  | 6 => (1, 0, 2, 0, 0, 1, 0, g110D6)
  | _ => emptyPacking
def g110I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g110 : Forest := ⟨110, 6, fun i => (g110Y[i]?).getD (0,0), g110C, [[], [33, 83]], g110L, g110I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g110P6n0 : block g110 6 0 1 = true := by decide +kernel
theorem g110B6 : block g110 6 0 1 = true := g110P6n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g110T : checkedTables g110 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g110 0 0 0 = true)
  · exact (rfl : block g110 1 0 0 = true)
  · exact (rfl : block g110 2 0 0 = true)
  · exact (rfl : block g110 3 0 0 = true)
  · exact (rfl : block g110 4 0 0 = true)
  · exact (rfl : block g110 5 0 0 = true)
  · exact g110B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g110G : graphValid g110 (boundsBefore K94) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low110 : Lower true (varsX 110) (graphGoal 110) 7 := lower_forest (g:=g110) (i:=0) (hints:=18879792) (before_sound K94 V94) g110G g110T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K110 := extendKnown K94 7 [(110,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V110 : Known true K110 := extend_ok (m:=110) V94 low110 (by decide +kernel)

def g118Y : Array (Bits × Bits) := #[(0x0, 0x0),
    (0xaab6eaaadbaaab6eaaadbaaab6eaaadbaaab6eaaadbaaab6eaaadbaaab6eaaadbaaab6eaaadbaaab6eaaadbaaab6eaaadbaaab6eaaadbaaab6eaaadbaaab6eaaadbaaab6eaaadbaaab6eaaadbaaab6eaaadbaaab6eaaadb, 0xffffc0000000000000000fffffc0000000000000000fffffc00000fffffc0000000000000000fffffc0000000000000000fffffc00000fffffc0000000000000000fffffc0000000000000000fffffc00000fffffc00000),
    (0xccdbb3336ecccdbb3336ecccdbb3336ecccdbb3336ecccdbb3336ecccdbb3336ecccdbb3336ecccdbb3336ecccdbb3336ecccdbb3336ecccdbb3336ecccdbb3336ecccdbb3336ecccdbb3336ecccdbb3336ecccdbb3336e, 0xfffffc00000fffffffffff000000000000000000000000000000000fffffc00000fffffffffff000000000000000000000000000000000fffffc00000fffffffffff00000000000),
    (0x0, 0x0),
    (0xf1cfc3c73f0f1cfc3c73f0f1cfc3c73f0f1cfc3c73f0f1cfc3c73f0f1cfc3c73f0f1cfc3c73f0f1cfc3c73f0f1cfc3c73f0f1cfc3c73f0f1cfc3c73f0f1cfc3c73f0f1cfc3c73f0f1cfc3c73f0f1cfc3c73f0f1cfc3c73, 0x3fffff00000000000fffffffffff0000000000000000000000000003fffff00000000000fffffffffff0000000000000000000000000003fffff00000000000fffffffffff0000000000000000000000),
    (0xf01f3fc07cff01f3fc07cff01f3fc07cff01f3fc07cff01f3fc07cff01f3fc07cff01f3fc07cff01f3fc07cff01f3fc07cff01f3fc07cff01f3fc07cff01f3fc07cff01f3fc07cff01f3fc07cff01f3fc07cff01f3fc07c, 0x3ffffffffffffffff000000000000000000000000000000000000003ffffffffffffffff000000000000000000000000000000000000003ffffffffffffffff000000000000000000000000000000000),
    (0xffe03fff80fffe03fff80fffe03fff80fffe03fff80fffe03fff80fffe03fff80fffe03fff80fffe03fff80fffe03fff80fffe03fff80fffe03fff80fffe03fff80fffe03fff80fffe03fff80fffe03fff80fffe03fff80, 0xfffffc0000000000000000000000000000000000000000000000000fffffc0000000000000000000000000000000000000000000000000fffffc0000000000000000000000000000000000000000000000000)]
def g118C : List ColumnInfo := [(2,0,116,0,5), (4,0,114,0,5), (16,0,102,0,5), (18,0,100,0,4), (32,0,86,0,5), (36,0,82,0,4)]
def g118D4 (j : Nat) : Nat := if j = 0 then 0x31825f63546049b899544066d6215101 else 0
def g118D5 (j : Nat) : Nat := if j = 0 then 0x202204002400800082088208045042db8ae568d01d2a2002faa3027b89504b712a097e15413f408825fd5101bf2a2037d54406f8a880fe41101 else 0
def g118D6 (j : Nat) : Nat := if j = 0 then 0x21d1080c864202ae21d1081101300fe04fd04fd01 else 0
def g118D7 (j : Nat) : Nat := if j = 0 then 0x2c68819f else 0
def g118L : Nat → Packing
  | 4 => (3, 3, 3, 0, 0, 4, 0, g118D4)
  | 5 => (10, 2, 3, 0, 0, 7, 0, g118D5)
  | 6 => (3, 1, 3, 0, 0, 7, 0, g118D6)
  | 7 => (1, 0, 3, 0, 0, 1, 0, g118D7)
  | _ => emptyPacking
def g118I : Nat → Nat → Option (Nat × Nat)
  | 5, tag => lookupShort 3 8 2 6 2 2 (fun j => if j=0 then 0x850000278082 else 0) tag
  | 6, tag => lookupShort 8 24 3 8 4 2 (fun j => if j=0 then 0x60c58300060000000800d2004299c100100056004489c713640800 else 0) tag
  | 7, tag => lookupShort 6 18 1 7 2 3 (fun j => if j=0 then 0xa1340000800000822604e84c553401c93 else 0) tag
  | _, _ => none
def g118 : Forest := ⟨118, 7, fun i => (g118Y[i]?).getD (0,0), g118C, [[], [82], [33, 84], [33, 66, 84], [65], [65, 82], [81, 82, 84], [81, 66]], g118L, g118I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g118P4n0 : block g118 4 0 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g118P4n2 : block g118 4 2 1 = true := by decide +kernel
theorem g118B4 : block g118 4 0 3 = true := (@block_merge g118 4 0 2 1 g118P4n0 g118P4n2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g118P5n0 : block g118 5 0 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g118P5n2 : block g118 5 2 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g118P5n4 : block g118 5 4 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g118P5n6 : block g118 5 6 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g118P5n8 : block g118 5 8 2 = true := by decide +kernel
theorem g118B5 : block g118 5 0 10 = true := (@block_merge g118 5 0 4 6 (@block_merge g118 5 0 2 2 g118P5n0 g118P5n2) (@block_merge g118 5 4 2 4 g118P5n4 (@block_merge g118 5 6 2 2 g118P5n6 g118P5n8)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g118P6n0 : block g118 6 0 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g118P6n2 : block g118 6 2 1 = true := by decide +kernel
theorem g118B6 : block g118 6 0 3 = true := (@block_merge g118 6 0 2 1 g118P6n0 g118P6n2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g118P7n0 : block g118 7 0 1 = true := by decide +kernel
theorem g118B7 : block g118 7 0 1 = true := g118P7n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g118T : checkedTables g118 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g118 0 0 0 = true)
  · exact (rfl : block g118 1 0 0 = true)
  · exact (rfl : block g118 2 0 0 = true)
  · exact (rfl : block g118 3 0 0 = true)
  · exact g118B4
  · exact g118B5
  · exact g118B6
  · exact g118B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g118G : graphValid g118 (boundsBefore K110) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low118 : Lower true (varsX 118) (graphGoal 118) 8 := lower_forest (g:=g118) (i:=0) (hints:=18941248) (before_sound K110 V110) g118G g118T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K118 := extendKnown K110 8 [(118,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V118 : Known true K118 := extend_ok (m:=118) V110 low118 (by decide +kernel)

def g122Y : Array (Bits × Bits) := #[(0x0, 0x0),
    (0x6deaaadbd555b7aaab6f5556deaaadbd555b7aaab6f5556deaaadbd555b7aaab6f5556deaaadbd555b7aaab6f5556deaaadbd555b7aaab6f5556deaaadbd555b7aaab6f5556deaaadbd555b7aaab6f5556deaaadbd555b7, 0x7fffff000000000000000007fffff00000000000000000000000fffffe00000000000000000fffffe00000000000000000000001fffffc00000000000000001fffffc00000000000000000000003fffff800000),
    (0x0, 0x0),
    (0xb773336ee666ddcccdbb999b773336ee666ddcccdbb999b773336ee666ddcccdbb999b773336ee666ddcccdbb999b773336ee666ddcccdbb999b773336ee666ddcccdbb999b773336ee666ddcccdbb999b773336ee666dd, 0x3fffff80000000000000000000000000000000001fffffc000007fffff00000000000000000000000000000000003fffff800000fffffe00000000000000000000000000000000007fffff000001fffffc00000000000),
    (0x39bc3c737878e6f0f1cde1e39bc3c737878e6f0f1cde1e39bc3c737878e6f0f1cde1e39bc3c737878e6f0f1cde1e39bc3c737878e6f0f1cde1e39bc3c737878e6f0f1cde1e39bc3c737878e6f0f1cde1e39bc3c737878e6, 0xffc00000000000000000000003fffff800000000001fffffffffff800000000000000000000007fffff000000000003fffffffffff00000000000000000000000fffffe000000000007ffffffffffe00000000000000000),
    (0x3e3fc07c7f80f8ff01f1fe03e3fc07c7f80f8ff01f1fe03e3fc07c7f80f8ff01f1fe03e3fc07c7f80f8ff01f1fe03e3fc07c7f80f8ff01f1fe03e3fc07c7f80f8ff01f1fe03e3fc07c7f80f8ff01f1fe03e3fc07c7f80f8, 0x3ffffffffffffffffe00000000000000000000000000000000007ffffffffffffffffc0000000000000000000000000000000000fffffffffffffffff80000000000000000000000000000),
    (0xc03fff807fff00fffe01fffc03fff807fff00fffe01fffc03fff807fff00fffe01fffc03fff807fff00fffe01fffc03fff807fff00fffe01fffc03fff807fff00fffe01fffc03fff807fff00fffe01fffc03fff807fff00, 0x1fffffc0000000000000000000000000000000000000000000003fffff80000000000000000000000000000000000000000000007fffff0000000000000000000000000000000000000000000000)]
def g122C : List ColumnInfo := [(2,0,120,0,5), (8,0,114,0,5), (16,0,106,0,5), (32,0,90,0,5)]
def g122D6 (j : Nat) : Nat := if j = 0 then 0xe411f else 0
def g122L : Nat → Packing
  | 6 => (1, 0, 2, 0, 0, 1, 0, g122D6)
  | _ => emptyPacking
def g122I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g122 : Forest := ⟨122, 6, fun i => (g122Y[i]?).getD (0,0), g122C, [[], [49, 84]], g122L, g122I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g122P6n0 : block g122 6 0 1 = true := by decide +kernel
theorem g122B6 : block g122 6 0 1 = true := g122P6n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g122T : checkedTables g122 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g122 0 0 0 = true)
  · exact (rfl : block g122 1 0 0 = true)
  · exact (rfl : block g122 2 0 0 = true)
  · exact (rfl : block g122 3 0 0 = true)
  · exact (rfl : block g122 4 0 0 = true)
  · exact (rfl : block g122 5 0 0 = true)
  · exact g122B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g122G : graphValid g122 (boundsBefore K118) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low122 : Lower true (varsX 122) (graphGoal 122) 7 := lower_forest (g:=g122) (i:=0) (hints:=19992624) (before_sound K118 V118) g122G g122T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K122 := extendKnown K118 7 [(122,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V122 : Known true K122 := extend_ok (m:=122) V118 low122 (by decide +kernel)

def g124Y : Array (Bits × Bits) := #[(0x0, 0x0),
    (0x0, 0x0),
    (0xdb5556daaab6d555b6aaadb5556daaab6d555b6aaadb5556daaab6d555b6aaadb5556daaab6d555b6aaadb5556daaab6d555b6aaadb5556daaab6d555b6aaadb5556daaab6d555b6aaadb5556daaab6d555b6aaadb5556d, 0x3ffffe00000fffff800003ffffe00000fffff8000000000000000000007ffffc00001fffff000007ffffc00001fffff000000000000000000000fffff800003ffffe00000fffff800003ffffe00000),
    (0x6d999b6cccdb6666db3336d999b6cccdb6666db3336d999b6cccdb6666db3336d999b6cccdb6666db3336d999b6cccdb6666db3336d999b6cccdb6666db3336d999b6cccdb6666db3336d999b6cccdb6666db3336d999b6, 0x3ffffffffff00000000003ffffffffff000000000000000000000000007fffffffffe00000000007fffffffffe00000000000000000000000000ffffffffffc0000000000ffffffffffc0000000000),
    (0x71e1e38f0f1c7878e3c3c71e1e38f0f1c7878e3c3c71e1e38f0f1c7878e3c3c71e1e38f0f1c7878e3c3c71e1e38f0f1c7878e3c3c71e1e38f0f1c7878e3c3c71e1e38f0f1c7878e3c3c71e1e38f0f1c7878e3c3c71e1e38, 0xfffff800003ffffffffffffffffffffc00000000000000000000000001fffff000007ffffffffffffffffffff800000000000000000000000003ffffe00000fffffffffffffffffffff000000000000000000000),
    (0x7ffe03fff01fff80fffc07ffe03fff01fff80fffc07ffe03fff01fff80fffc07ffe03fff01fff80fffc07ffe03fff01fff80fffc07ffe03fff01fff80fffc07ffe03fff01fff80fffc07ffe03fff01fff80fffc07ffe03f, 0xffffffffffc00000000000000000000000000000000000000000000001ffffffffff800000000000000000000000000000000000000000000003ffffffffff000000000000000000000000000000000000000000),
    (0x81fffc0fffe07fff03fff81fffc0fffe07fff03fff81fffc0fffe07fff03fff81fffc0fffe07fff03fff81fffc0fffe07fff03fff81fffc0fffe07fff03fff81fffc0fffe07fff03fff81fffc0fffe07fff03fff81fffc0, 0x1fffff00000000000000000000000000000000000000000000000000003ffffe00000000000000000000000000000000000000000000000000007ffffc0000000000000000000000000000000000000000000000000000)]
def g124C : List ColumnInfo := [(4,0,120,0,5)]
def g124D5 (j : Nat) : Nat := if j = 0 then 0x5f else 0
def g124L : Nat → Packing
  | 5 => (1, 0, 1, 0, 0, 1, 0, g124D5)
  | _ => emptyPacking
def g124I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g124 : Forest := ⟨124, 5, fun i => (g124Y[i]?).getD (0,0), g124C, [[], [50]], g124L, g124I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g124P5n0 : block g124 5 0 1 = true := by decide +kernel
theorem g124B5 : block g124 5 0 1 = true := g124P5n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g124T : checkedTables g124 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g124 0 0 0 = true)
  · exact (rfl : block g124 1 0 0 = true)
  · exact (rfl : block g124 2 0 0 = true)
  · exact (rfl : block g124 3 0 0 = true)
  · exact (rfl : block g124 4 0 0 = true)
  · exact g124B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g124G : graphValid g124 (boundsBefore K122) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low124 : Lower true (varsX 124) (graphGoal 124) 6 := lower_forest (g:=g124) (i:=0) (hints:=36066560) (before_sound K122 V122) g124G g124T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K124 := extendKnown K122 6 [(124,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V124 : Known true K124 := extend_ok (m:=124) V122 low124 (by decide +kernel)

def g126Y : Array (Bits × Bits) := #[(0x0, 0x0),
    (0xaaaaaaab56afeaaaaaaad5abfaaaaaaab56afeaaaaaaad5abfaaaaaaab56afeaaaaaaad5abfaaaaaaab56afeaaaaaaad5abfaaaaaaab56afeaaaaaaad5abfaaaaaaab56afeaaaaaaad5abfaaaaaaab56afeaaaaaaad5abf, 0xffffffffffffc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffc000000000000ffffffffffffc000000000000),
    (0xcccccccd9b3ab333333366ceacccccccd9b3ab333333366ceacccccccd9b3ab333333366ceacccccccd9b3ab333333366ceacccccccd9b3ab333333366ceacccccccd9b3ab333333366ceacccccccd9b3ab333333366cea, 0xffffffffffffc000000000000ffffffffffffc000000000000ffffffffffffc000000000000fffffffffffffffffffffffff0000000000000000000000000),
    (0xf0f0f0f1e3ccfc3c3c3c78f33f0f0f0f1e3ccfc3c3c3c78f33f0f0f0f1e3ccfc3c3c3c78f33f0f0f0f1e3ccfc3c3c3c78f33f0f0f0f1e3ccfc3c3c3c78f33f0f0f0f1e3ccfc3c3c3c78f33f0f0f0f1e3ccfc3c3c3c78f33, 0xfffffffffffffffffffffffff0000000000000000000000000fffffffffffffffffffffffff00000000000000000000000000000000000000000000000000),
    (0xff00ff01fc0f3fc03fc07f03cff00ff01fc0f3fc03fc07f03cff00ff01fc0f3fc03fc07f03cff00ff01fc0f3fc03fc07f03cff00ff01fc0f3fc03fc07f03cff00ff01fc0f3fc03fc07f03cff00ff01fc0f3fc03fc07f03c, 0x3ffffffffffff0000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000),
    (0xffff0001fff03fffc0007ffc0ffff0001fff03fffc0007ffc0ffff0001fff03fffc0007ffc0ffff0001fff03fffc0007ffc0ffff0001fff03fffc0007ffc0ffff0001fff03fffc0007ffc0ffff0001fff03fffc0007ffc0, 0x3fffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    (0xfffffffe00003fffffff80000fffffffe00003fffffff80000fffffffe00003fffffff80000fffffffe00003fffffff80000fffffffe00003fffffff80000fffffffe00003fffffff80000fffffffe00003fffffff80000, 0xffffffffffffc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)]
def g126C : List ColumnInfo := [(2,0,124,0,6), (4,0,122,0,7), (6,0,120,0,5), (8,0,118,0,8), (10,0,116,0,5), (16,0,110,0,7), (18,0,108,0,5), (20,0,106,0,5), (22,0,104,0,4), (26,0,100,0,4), (32,0,94,0,6), (36,0,90,0,5), (48,0,78,0,5), (52,0,74,0,4), (64,0,62,0,5), (68,0,58,0,4), (80,0,46,0,4)]
def g126D4 (j : Nat) : Nat := if j = 0 then 0xf624c30219d12a324e1b20b4c619519270d905867c930d1ba0b02631e0f8189d6541318a708c24e32a0998a474a03741504 else 0
def g126D5 (j : Nat) : Nat := if j = 0 then 0xc004c6e10800000000000000000000000000000000000000000000018080000000000000000000000000000000410797c5dfee767add3e873795c7e27077dbbda2a14aa24fa71329649a411a8a43a11027e3d9e0ea72379b0d26631980ba5a2b950a24e2350e813d9d4de6931974ae51259147e39198b44e210d8541e008df835c24645675e0d7085515cf30585d64816b960817592058be78518464163b8a1748d9058f6185d236416b38a1468d905ad61851a36416b38a1748d905ad6185d236416b6600748d9058de7851836416b38a1460d905ad6185183641733919270d905ccd4649c364173585e36515059f2185d205417368de6741405cdb8399d05017a68e10559005ad61851563017369e10558c05ae61851562017b28e105588058f67851561017b48e105584058dd868dd05813a58614558e04a9d848156381339e062759504ce48189d65413358de1759504ce62785d65413358dc1759504ce62705d654121f9e16519504c6d6549c654133946127195048de385da154123b8a176855048ee2859d05412974e06541504a6d28195054133619e3741504d9a470dd05412f24a03741504b593819505412da4a06541504e35458561641275861748d7038f6185d265c0e3b8a175593038f6185d564c0e3d8617499503aba6851504c06ae6027559301ab6185d564c06a74e07559301aad281d564c06ad4607559301e9a3841564c0637e0d76915018de385d5644063b8a175591018f6185d5644078d51515591018f58799614407cc5151541101 else 0
def g126D6 : Nat → Nat
  | 0 => 0x67eb8c8c82dde3751905bdc4ea320b7d85d464175ea308c82cfd748d905dbe8d1b20bb791a364176ea346c82edc468d905fb6e11b20bb7dd2364176f3a46c82edd748d905db8e91b20bb7dc6364176eb8c6c82edf708d905dbae11b20bb7918364176ea306c82dde760d905b9a4e1b20bb78da164167eba42c82dde3745905dbc6c8b20baf91b454176f1b68a82df970d1505dbc6d22a0baf919454176f1b28a82f5e368d505dbc6c9aa0bd78dd35417af1b26a82ede3685505dbc6c8aa0bbd859154176f1b40a82fda3681505bf2e902a0b3f5db45016fb0ba8a02cfe6751405fb46e8280bbe99d050167d33a0a02ef90559005d7eeab200bae415640176fa2ac602edd4558c05db20ab180bbbd156201776a2ac402ee90558805dee8ab080bbd515610177882ac202fb61751604d7ccea2c096f5d205812df23a0b025de3741604cfa0b32c099f815658133e82acb0269d4558e04dbc0ab1c09b7415638127eb8eca8267f65995049fae132a097b89d65412fb0baca8267e5759504ddc4eb2a093b89d654127f0baca826f617595049ec2eb2a09bd05d654127f03aca826fa0759504cfaca32a093f9d865412f6938ca825f517195049da4e32a093d45c654127f3b42a824fd7685504b7ae90aa097e5c215412df23a2a827bb45c1504bf4ed82a099fd9605412deba40a825f970815049face82a096f91d05412ef1ba0a8267f6541504cf8ca82a09be19d05413dd23a0a827b84741504fb46e82a09f60dd05412fd0ba0a8277b6541504ef0ca82a09eed1505413dca2a0a8277a3541504ef26a82a09af516164137b0ac2c826f905859049feeb0b2093f5d616413ea9aa2a89df970917039faed22e07778dd45c0efb0ba8b81cfe6751703bbae91ae07f65c235c0f6eb3c6b81fda3741703fb46a82e07d68d505c0e7eba4cb81cfe4759703dbc6eb2e07b78d565c0e7fbaac981cfd7559303d7a8ab2607be41564c0e7ebb48a81ddd7391503bf2e122a073f99d4540efb0ba8a81cfd74995039fc8eb2a07b78dd6540e6f1baca81fda3741503fb26a82a07d64d50540efcb848b80cfd7691701bec2ea2e033f99d45c06fd23a0b80fda37417019fae932e033f91d65c06fdbaa0980df97541301f728a82603be59504c067fbaac980cfd7559301d7c8ab2603af51564c077c82ac980ebf7559301d7ceab2603af5d564c075e3aac980eb905593019faed22a037d5c645406fcb848a80cfe6751501bec2ea2a033f5d2654067f23aca80ede37595019bc6eb2a03bd85d65407bb22a2a80f754545501bf48e82a03f68dd05407f90ba0a80ff115415019feeab22033f5d5644075ea2ac880ef51559101df20ab2203bd85d64407daa2c2880ef66585101fe20b0a2037d5d614406fdbaa0880df97541101f728a82203be59504407f88aa0880ff21741101
  | 1 => 0x820a0f1e0840a0808200725008600000000080020f1820128284000020128284000001808400018c6c21804a80100031b084800800030202002c6c213182201812100cc7c380400002d0840e08006281840018342083128286070010702841c4a100001820518200003158b86822008004003020dc6100003718006030820dc600180c2083025181000a010820dc60019082010820000000608585718614086020000a08000182060800718085c6083f184001820001c080201e1c187718400281840008512d086000804a080064210512840a06021818200182006020004a086021408000552841c154ac200292824a0908205082000800a0210282000000042820082282860c0880371c00802080003020018084c20012282000020a0800008200183c60a280041c0a0018704032282f1800e000031408080040000208000082005020008082000a08004000820a08216cac682002837180060a08002020800008000283c60818200082020e082001008006002818404087021c161018204080020010000082820852284540a0839098fd8e18c589987d86185581980d8017f57e97cd7c17a578977d75174572971d6f16e56d96cd6a169568964d6416156095fd5d15b55a959d58157555952d51148547946d44142541940d3e13d53b939d3613353092dd2d12c52a929d28127525920d1e11d51b918d18117513912d1110d50c90ad051045028fecfd0fc4fa8f9cf90f84f78f5cf20f04ee8edced0eb4ea8e9ce80e64e58e4ce20e04dd8dccdb0da4d98d7cd70d34d08cfccd0cb4c78c5cc50c34c28bfcbd0b94b78b6cb50b44b28b1cb10af4ad8abcab0aa4a78a1ca009e49c89bc9a098497894c93092491890c9008f48d88cc89087482880c8007f47d87cc7a077475874c7307147086fc6e06d46b869c6706345b85ac59057454853c5305145084fc4e04d44b849c48046443842c4204043e838c3503343182fc2f02d42c82bc2a028426825c2402242081fc1c01b418816c1501241080ec0e00b40a809c08006403801c0013f81d64856efb9ac10acff7458215dbee6b042b37dcd608567eb848c8acfd7481915bbc6e8322b7d5d215456fab842a8aebf4559305bec2eb240bbec15648167f1bac902cfe1759205dec2eb240b3d85d648177a0bac902ddd73d1905d7e8d2320b3f5ce4641
  | _ => 0
def g126D7 : Nat → Nat
  | 0 => 0xb8c1610038e0d94223058401038365c6090801c70c162b1a10038e1514315152863860b141718302009182c505c60c0802060b14971c2c30081c283650b8d18305840803070a0018a0b8c1810030e0480f1c171830238e4a8d088171830220e14951a1003101e38505c60c0802470a420400a3c521020051c28325c60b0802070a0870a4a0041c292e3c200614840863858a101718304840802c5824204414182e30608080205060b8c182020081c3660a101e2e3070a0803080f1a284078b8c1c10058f1c355080f142e30404b1c14006282a100205c70a008407450b8c1001c70a8a1718304040122a285c60c1010040e19142e3060b0810050e0c14008283210c70a101a2e30606012405080d17183024101c20305c60071c203450b8c00e385000c5010018f1c1b1c1020071c28305c60e0810048a0c1718382040102c5068b8e0810040a0d971c10030e161b285c60e08100506cb8e080147020200414080801070a1017183050481e28405c60c1412078e5423182020081c23182820400e385aa10171830504958ab1820200616a85088b8c1410200abdadd8ae036dfb49d91ec595d2ad4d576a77512a6a53028f7467a184fca7933b59cd4d8e6212bd93c497648520b8f4c73a359159898441e1cb0a7842c102020ff57ed3ee1f2cf58797bbe1dacead74cb96dc72e106f3b66dac8d1166d328d8cac2e5fbaf71782b7c59f2c0154ca8b52da93942e9f54e9a68d2bc93548623391748984342134ff47d83cd1d70e046af32e1904c3e5fd2e31604a864f726a92e88ea4372000f2475c3931ae0c5c5b229b135887c3ec1d40d905d026c0f806081f0098000ff59215bf59215bf58e15ff58215bf58215bf91915ff51915bf8d915ff4d915bf81915ff41915ff4d515fd85515ffd1705bf59305ffd1605df8d605df4d605fec1605ff99205ff59205bf59205bf58e05bf58605bf58205ffd1905ff91905bf91905ff51905ff11905ff8d905bf8d905f78d905b78d905ff4d905f70d905ff85905bf85905ff45905ffd1505ff91505ff51505ff8d505df8d505ff4d505df4d505ff85505ff45505ff81505fe81505ffd1405ff51405fe41405bf99405af99005bf59005af59005b758c05bb58805bd58405ef51604ff81604ff41604bf99604bf59604b758e04bf58204ffd9504bfd9504ff99504bf99504ff59504bf59504ff19504bf19504ff85504ff45504fec1504ff81504ff41504fe41504ff85904bf85904ff45904bf99404bf59404bf99513bf59513fd45513ff91703ff51703f78d703fe41703bf99703bf59703bf59303ff91503ff51503bf99503bf59503f74d503fe41503ff91701ff51701fe41701bf99701bf59701fe41301af99301bf59301af59301ff91501ff51501bf99501bf59501fd45501fe41501bf59101fd85101fe41101
  | 1 => 0x70b150408a3868b54282e307040802c80e1ab05084a17183820401a392820020e14202e3060a0810050f1a2c505c60e0810050f162831e345084a1718385040803080f0e9428a3c5080b8c18282040143d282002101e160811480e958e1a3060481400214182e3060b0810048e1410e0c942e38000720384064a1718020706c60800a38504385210c70a0b8c181003901c284064a171830200b1e385080b8c182420401628305c68c182020091829286385000c70a0b8c1810038a4a8d088305000c7250a00414203250b8c1e10300016942e3c30054b8e161802900c94288406080c971e18040e108408828405c60c121020091e212824204615140063a2800c545420041c18280107080c942e3800082019285002901019285c60071d14100107c5420400b140044078ec70d1830040a8b0e0882a2c3828451c1b1820028e14182e3460c1010050a0d97182c20071c283650b8c182c20401638365c60b0801c7064
  | _ => 0
def g126D8 (j : Nat) : Nat := if j = 0 then 0x40e34b2889458c308100d3cd2ca2251630c204030a1a51630c284100a40f38a2069458c30a104038a2069458c30a10402ce2869458c30a10402cc2ca1a51630c284100c30b2881a51630c284100d2869458c30a104028d30b2881c58c308100c30a1630c284100930a2061630c284100b2ca1a51630c10092ca2251630c20402baed831eb127c8d1e664950408c61f842003fc2bfd15ff82ff817fa0bfc05ff027f413f809fd13ff81ff40ffe03fd01 else 0
def g126D9 (j : Nat) : Nat := if j = 0 then 0x28c21bf else 0
def g126L : Nat → Packing
  | 4 => (6, 5, 5, 0, 0, 5, 0, g126D4)
  | 5 => (70, 4, 5, 0, 0, 9, 0, g126D5)
  | 6 => (231, 3, 5, 0, 0, 12, 0, g126D6)
  | 7 => (120, 2, 5, 0, 0, 13, 0, g126D7)
  | 8 => (14, 1, 5, 0, 0, 10, 0, g126D8)
  | 9 => (1, 0, 5, 0, 0, 1, 0, g126D9)
  | _ => emptyPacking
def g126I : Nat → Nat → Option (Nat × Nat)
  | 5, tag => lookupShort 3 9 1 5 3 0 (fun j => if j=0 then 0xab8829810 else 0) tag
  | 6, tag => lookupShort 44 131 4 10 7 1 (fun j => if j=0 then 0x32206c00e0c0b000000000006000825a3e50000001700119e4a41a9a1e000000069310800002400000046b03cfc00051388d8000003148e100910a001020010d459120540004f2a00182cac05cfa44003a5000000000000000410a10dd320000000000000008813cc332c8a781c38250471fa6b3a0023d0c23b0020749800001340d400e881c10d27818000b8000cc9540139003804b400a64080742f11528a7921a600f91c40111200301101100000011110200010001000300 else 0) tag
  | 7, tag => lookupShort 151 452 5 11 8 1 (fun j => if j=0 then 0x357468000006e5db0e501241f000138018000018680028800510c5162695200000000d7c36e712ab57e35d8a071dba0e34e8000011882f85002a00000000001364006df00024862207000d4932c9e8531da6ac9488b6c563e4c08d8af83cd4b009ec006bdefc0000000023a1f40028eed9c2000000a1a0000057c51e9800066682c0011d000914003da0000000000053d00000010484b024d511551d409e34014fd1932a2b80014898c000000db61c006700018ff3b8000003040000000000000000000a0f1b789122b8d69e1322a109bf8ccd6e83a64eae8c306d12c540f80000054012c0010c03b2b502a06628e068794c8000009f8730000000023c800c080032f0c616c9540042a8fe6bc000005175b81e60f6830c65625b2088714e18559638184890e56001198114e45b6bec6f0002093606a14b0c80a0002b79291ce2100030202800001b588dcb38b90b28742e2580014aa47c2e27c722850002d782c6b0000024c000c6e0009f0008475d80062f000000686670000000040dd0c4cc0022d00000034a1204e003202ba239cb52d452936002b503e000001af000977124545dcb4c9e80000012600167000a3e00000000000001578000d1910000006f0000002d174a00000000000003258ad0002241847318486767ec51b4d9d3aea3ebe974324a18b22f000201dc32ca1eb4db6493c04c4d0000006f4b469ca9a5c20063c000860009b80000001d560000002cd000000006c3001efd28939617cff83608ad0d72208002c0000000004e815853f54001a040068d0000016956659002d080000000000000055400000000963eba5c800cb000000000c6a0000066e0000034be48ca681800000001a6b4394000810e0004014c0338c41190041b4046080300020318070086008121180006000108000000850012803460004001044000022004810800008c2100000009260180008444000201800000400280c0000020044000c0e180481002008400 else 0) tag
  | 8, tag => lookupShort 79 237 4 10 7 1 (fun j => if j=0 then 0x2ca002239162044c008974b844004a301f332f55f047400099624420544e81dc391f6ac0033c0000000e94000000086114000cb000000000025a6a4085a0005ff1000545cd00322d763b1bd34c4000002a4002565a0668d64c1651581d80250009870b00000000001cc0065519a1f530000089f3f91d3e0020d00033a75828144d923768879fe30001904358029588bb53f491726ca0469242320ae40dd671562ac4485e00000f17a90031a4b0004f4728f02e14b97d081c00000d0709dd000001a700363ce000000934c7391b4000031b9396785c000000000346002770db2d4de2adc20a00188b98a80000000000002aa000000035b003e707a0f679e80024492b5000026001300180000000000000010355791c58000000c000000000000000e736b1b9a6003002052018000112b0201a000100405240102100051300150110200000001200000001024000000001 else 0) tag
  | 9, tag => lookupShort 13 39 2 7 4 1 (fun j => if j=0 then 0x53389007bc4e4031000007dae4a58a016806c000240002021a9f1980000140685009c517040 else 0) tag
  | _, _ => none
def g126 : Forest := ⟨126, 9, fun i => (g126Y[i]?).getD (0,0), g126C, [[], [81, 66]], g126L, g126I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P4n0 : block g126 4 0 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P4n2 : block g126 4 2 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P4n4 : block g126 4 4 2 = true := by decide +kernel
theorem g126B4 : block g126 4 0 6 = true := (@block_merge g126 4 0 2 4 g126P4n0 (@block_merge g126 4 2 2 2 g126P4n2 g126P4n4))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P5n0 : block g126 5 0 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P5n2 : block g126 5 2 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P5n4 : block g126 5 4 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P5n6 : block g126 5 6 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P5n8 : block g126 5 8 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P5n10 : block g126 5 10 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P5n12 : block g126 5 12 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P5n14 : block g126 5 14 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P5n16 : block g126 5 16 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P5n18 : block g126 5 18 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P5n20 : block g126 5 20 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P5n22 : block g126 5 22 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P5n24 : block g126 5 24 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P5n26 : block g126 5 26 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P5n28 : block g126 5 28 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P5n30 : block g126 5 30 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P5n32 : block g126 5 32 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P5n34 : block g126 5 34 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P5n36 : block g126 5 36 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P5n38 : block g126 5 38 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P5n40 : block g126 5 40 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P5n42 : block g126 5 42 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P5n44 : block g126 5 44 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P5n46 : block g126 5 46 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P5n48 : block g126 5 48 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P5n50 : block g126 5 50 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P5n52 : block g126 5 52 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P5n54 : block g126 5 54 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P5n56 : block g126 5 56 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P5n58 : block g126 5 58 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P5n60 : block g126 5 60 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P5n62 : block g126 5 62 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P5n64 : block g126 5 64 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P5n66 : block g126 5 66 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P5n68 : block g126 5 68 2 = true := by decide +kernel
theorem g126B5 : block g126 5 0 70 = true := (@block_merge g126 5 0 34 36 (@block_merge g126 5 0 16 18 (@block_merge g126 5 0 8 8 (@block_merge g126 5 0 4 4 (@block_merge g126 5 0 2 2 g126P5n0 g126P5n2) (@block_merge g126 5 4 2 2 g126P5n4 g126P5n6)) (@block_merge g126 5 8 4 4 (@block_merge g126 5 8 2 2 g126P5n8 g126P5n10) (@block_merge g126 5 12 2 2 g126P5n12 g126P5n14))) (@block_merge g126 5 16 8 10 (@block_merge g126 5 16 4 4 (@block_merge g126 5 16 2 2 g126P5n16 g126P5n18) (@block_merge g126 5 20 2 2 g126P5n20 g126P5n22)) (@block_merge g126 5 24 4 6 (@block_merge g126 5 24 2 2 g126P5n24 g126P5n26) (@block_merge g126 5 28 2 4 g126P5n28 (@block_merge g126 5 30 2 2 g126P5n30 g126P5n32))))) (@block_merge g126 5 34 18 18 (@block_merge g126 5 34 8 10 (@block_merge g126 5 34 4 4 (@block_merge g126 5 34 2 2 g126P5n34 g126P5n36) (@block_merge g126 5 38 2 2 g126P5n38 g126P5n40)) (@block_merge g126 5 42 4 6 (@block_merge g126 5 42 2 2 g126P5n42 g126P5n44) (@block_merge g126 5 46 2 4 g126P5n46 (@block_merge g126 5 48 2 2 g126P5n48 g126P5n50)))) (@block_merge g126 5 52 8 10 (@block_merge g126 5 52 4 4 (@block_merge g126 5 52 2 2 g126P5n52 g126P5n54) (@block_merge g126 5 56 2 2 g126P5n56 g126P5n58)) (@block_merge g126 5 60 4 6 (@block_merge g126 5 60 2 2 g126P5n60 g126P5n62) (@block_merge g126 5 64 2 4 g126P5n64 (@block_merge g126 5 66 2 2 g126P5n66 g126P5n68))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n0 : block g126 6 0 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n2 : block g126 6 2 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n4 : block g126 6 4 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n6 : block g126 6 6 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n8 : block g126 6 8 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n10 : block g126 6 10 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n12 : block g126 6 12 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n14 : block g126 6 14 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n16 : block g126 6 16 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n18 : block g126 6 18 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n20 : block g126 6 20 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n22 : block g126 6 22 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n24 : block g126 6 24 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n26 : block g126 6 26 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n28 : block g126 6 28 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n30 : block g126 6 30 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n32 : block g126 6 32 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n34 : block g126 6 34 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n36 : block g126 6 36 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n38 : block g126 6 38 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n40 : block g126 6 40 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n42 : block g126 6 42 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n44 : block g126 6 44 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n46 : block g126 6 46 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n48 : block g126 6 48 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n50 : block g126 6 50 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n52 : block g126 6 52 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n54 : block g126 6 54 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n56 : block g126 6 56 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n58 : block g126 6 58 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n60 : block g126 6 60 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n62 : block g126 6 62 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n64 : block g126 6 64 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n66 : block g126 6 66 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n68 : block g126 6 68 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n70 : block g126 6 70 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n72 : block g126 6 72 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n74 : block g126 6 74 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n76 : block g126 6 76 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n78 : block g126 6 78 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n80 : block g126 6 80 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n82 : block g126 6 82 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n84 : block g126 6 84 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n86 : block g126 6 86 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n88 : block g126 6 88 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n90 : block g126 6 90 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n92 : block g126 6 92 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n94 : block g126 6 94 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n96 : block g126 6 96 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n98 : block g126 6 98 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n100 : block g126 6 100 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n102 : block g126 6 102 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n104 : block g126 6 104 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n106 : block g126 6 106 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n108 : block g126 6 108 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n110 : block g126 6 110 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n112 : block g126 6 112 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n114 : block g126 6 114 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n116 : block g126 6 116 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n118 : block g126 6 118 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n120 : block g126 6 120 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n122 : block g126 6 122 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n124 : block g126 6 124 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n126 : block g126 6 126 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n128 : block g126 6 128 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n130 : block g126 6 130 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n132 : block g126 6 132 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n134 : block g126 6 134 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n136 : block g126 6 136 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n138 : block g126 6 138 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n140 : block g126 6 140 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n142 : block g126 6 142 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n144 : block g126 6 144 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n146 : block g126 6 146 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n148 : block g126 6 148 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n150 : block g126 6 150 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n152 : block g126 6 152 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n154 : block g126 6 154 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n156 : block g126 6 156 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n158 : block g126 6 158 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n160 : block g126 6 160 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n162 : block g126 6 162 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n164 : block g126 6 164 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n166 : block g126 6 166 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n168 : block g126 6 168 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n170 : block g126 6 170 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n172 : block g126 6 172 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n174 : block g126 6 174 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n176 : block g126 6 176 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n178 : block g126 6 178 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n180 : block g126 6 180 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n182 : block g126 6 182 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n184 : block g126 6 184 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n186 : block g126 6 186 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n188 : block g126 6 188 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n190 : block g126 6 190 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n192 : block g126 6 192 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n194 : block g126 6 194 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n196 : block g126 6 196 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n198 : block g126 6 198 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n200 : block g126 6 200 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n202 : block g126 6 202 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n204 : block g126 6 204 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n206 : block g126 6 206 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n208 : block g126 6 208 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n210 : block g126 6 210 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n212 : block g126 6 212 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n214 : block g126 6 214 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n216 : block g126 6 216 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n218 : block g126 6 218 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n220 : block g126 6 220 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n222 : block g126 6 222 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n224 : block g126 6 224 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n226 : block g126 6 226 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n228 : block g126 6 228 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n230 : block g126 6 230 1 = true := by decide +kernel
theorem g126B6 : block g126 6 0 231 = true := (@block_merge g126 6 0 116 115 (@block_merge g126 6 0 58 58 (@block_merge g126 6 0 28 30 (@block_merge g126 6 0 14 14 (@block_merge g126 6 0 6 8 (@block_merge g126 6 0 2 4 g126P6n0 (@block_merge g126 6 2 2 2 g126P6n2 g126P6n4)) (@block_merge g126 6 6 4 4 (@block_merge g126 6 6 2 2 g126P6n6 g126P6n8) (@block_merge g126 6 10 2 2 g126P6n10 g126P6n12))) (@block_merge g126 6 14 6 8 (@block_merge g126 6 14 2 4 g126P6n14 (@block_merge g126 6 16 2 2 g126P6n16 g126P6n18)) (@block_merge g126 6 20 4 4 (@block_merge g126 6 20 2 2 g126P6n20 g126P6n22) (@block_merge g126 6 24 2 2 g126P6n24 g126P6n26)))) (@block_merge g126 6 28 14 16 (@block_merge g126 6 28 6 8 (@block_merge g126 6 28 2 4 g126P6n28 (@block_merge g126 6 30 2 2 g126P6n30 g126P6n32)) (@block_merge g126 6 34 4 4 (@block_merge g126 6 34 2 2 g126P6n34 g126P6n36) (@block_merge g126 6 38 2 2 g126P6n38 g126P6n40))) (@block_merge g126 6 42 8 8 (@block_merge g126 6 42 4 4 (@block_merge g126 6 42 2 2 g126P6n42 g126P6n44) (@block_merge g126 6 46 2 2 g126P6n46 g126P6n48)) (@block_merge g126 6 50 4 4 (@block_merge g126 6 50 2 2 g126P6n50 g126P6n52) (@block_merge g126 6 54 2 2 g126P6n54 g126P6n56))))) (@block_merge g126 6 58 28 30 (@block_merge g126 6 58 14 14 (@block_merge g126 6 58 6 8 (@block_merge g126 6 58 2 4 g126P6n58 (@block_merge g126 6 60 2 2 g126P6n60 g126P6n62)) (@block_merge g126 6 64 4 4 (@block_merge g126 6 64 2 2 g126P6n64 g126P6n66) (@block_merge g126 6 68 2 2 g126P6n68 g126P6n70))) (@block_merge g126 6 72 6 8 (@block_merge g126 6 72 2 4 g126P6n72 (@block_merge g126 6 74 2 2 g126P6n74 g126P6n76)) (@block_merge g126 6 78 4 4 (@block_merge g126 6 78 2 2 g126P6n78 g126P6n80) (@block_merge g126 6 82 2 2 g126P6n82 g126P6n84)))) (@block_merge g126 6 86 14 16 (@block_merge g126 6 86 6 8 (@block_merge g126 6 86 2 4 g126P6n86 (@block_merge g126 6 88 2 2 g126P6n88 g126P6n90)) (@block_merge g126 6 92 4 4 (@block_merge g126 6 92 2 2 g126P6n92 g126P6n94) (@block_merge g126 6 96 2 2 g126P6n96 g126P6n98))) (@block_merge g126 6 100 8 8 (@block_merge g126 6 100 4 4 (@block_merge g126 6 100 2 2 g126P6n100 g126P6n102) (@block_merge g126 6 104 2 2 g126P6n104 g126P6n106)) (@block_merge g126 6 108 4 4 (@block_merge g126 6 108 2 2 g126P6n108 g126P6n110) (@block_merge g126 6 112 2 2 g126P6n112 g126P6n114)))))) (@block_merge g126 6 116 58 57 (@block_merge g126 6 116 28 30 (@block_merge g126 6 116 14 14 (@block_merge g126 6 116 6 8 (@block_merge g126 6 116 2 4 g126P6n116 (@block_merge g126 6 118 2 2 g126P6n118 g126P6n120)) (@block_merge g126 6 122 4 4 (@block_merge g126 6 122 2 2 g126P6n122 g126P6n124) (@block_merge g126 6 126 2 2 g126P6n126 g126P6n128))) (@block_merge g126 6 130 6 8 (@block_merge g126 6 130 2 4 g126P6n130 (@block_merge g126 6 132 2 2 g126P6n132 g126P6n134)) (@block_merge g126 6 136 4 4 (@block_merge g126 6 136 2 2 g126P6n136 g126P6n138) (@block_merge g126 6 140 2 2 g126P6n140 g126P6n142)))) (@block_merge g126 6 144 14 16 (@block_merge g126 6 144 6 8 (@block_merge g126 6 144 2 4 g126P6n144 (@block_merge g126 6 146 2 2 g126P6n146 g126P6n148)) (@block_merge g126 6 150 4 4 (@block_merge g126 6 150 2 2 g126P6n150 g126P6n152) (@block_merge g126 6 154 2 2 g126P6n154 g126P6n156))) (@block_merge g126 6 158 8 8 (@block_merge g126 6 158 4 4 (@block_merge g126 6 158 2 2 g126P6n158 g126P6n160) (@block_merge g126 6 162 2 2 g126P6n162 g126P6n164)) (@block_merge g126 6 166 4 4 (@block_merge g126 6 166 2 2 g126P6n166 g126P6n168) (@block_merge g126 6 170 2 2 g126P6n170 g126P6n172))))) (@block_merge g126 6 174 28 29 (@block_merge g126 6 174 14 14 (@block_merge g126 6 174 6 8 (@block_merge g126 6 174 2 4 g126P6n174 (@block_merge g126 6 176 2 2 g126P6n176 g126P6n178)) (@block_merge g126 6 180 4 4 (@block_merge g126 6 180 2 2 g126P6n180 g126P6n182) (@block_merge g126 6 184 2 2 g126P6n184 g126P6n186))) (@block_merge g126 6 188 6 8 (@block_merge g126 6 188 2 4 g126P6n188 (@block_merge g126 6 190 2 2 g126P6n190 g126P6n192)) (@block_merge g126 6 194 4 4 (@block_merge g126 6 194 2 2 g126P6n194 g126P6n196) (@block_merge g126 6 198 2 2 g126P6n198 g126P6n200)))) (@block_merge g126 6 202 14 15 (@block_merge g126 6 202 6 8 (@block_merge g126 6 202 2 4 g126P6n202 (@block_merge g126 6 204 2 2 g126P6n204 g126P6n206)) (@block_merge g126 6 208 4 4 (@block_merge g126 6 208 2 2 g126P6n208 g126P6n210) (@block_merge g126 6 212 2 2 g126P6n212 g126P6n214))) (@block_merge g126 6 216 8 7 (@block_merge g126 6 216 4 4 (@block_merge g126 6 216 2 2 g126P6n216 g126P6n218) (@block_merge g126 6 220 2 2 g126P6n220 g126P6n222)) (@block_merge g126 6 224 4 3 (@block_merge g126 6 224 2 2 g126P6n224 g126P6n226) (@block_merge g126 6 228 2 1 g126P6n228 g126P6n230)))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7n0 : block g126 7 0 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7n2 : block g126 7 2 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7n4 : block g126 7 4 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7n6 : block g126 7 6 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7n8 : block g126 7 8 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7n10 : block g126 7 10 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7n12 : block g126 7 12 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7n14 : block g126 7 14 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7n16 : block g126 7 16 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7n18 : block g126 7 18 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7n20 : block g126 7 20 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7n22 : block g126 7 22 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7n24 : block g126 7 24 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7n26 : block g126 7 26 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7n28 : block g126 7 28 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7n30 : block g126 7 30 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7n32 : block g126 7 32 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7n34 : block g126 7 34 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7n36 : block g126 7 36 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7n38 : block g126 7 38 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7n40 : block g126 7 40 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7n42 : block g126 7 42 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7n44 : block g126 7 44 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7n46 : block g126 7 46 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7n48 : block g126 7 48 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7n50 : block g126 7 50 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7n52 : block g126 7 52 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7n54 : block g126 7 54 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7n56 : block g126 7 56 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7n58 : block g126 7 58 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7n60 : block g126 7 60 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7n62 : block g126 7 62 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7n64 : block g126 7 64 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7n66 : block g126 7 66 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7n68 : block g126 7 68 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7n70 : block g126 7 70 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7n72 : block g126 7 72 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7n74 : block g126 7 74 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7n76 : block g126 7 76 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7n78 : block g126 7 78 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7n80 : block g126 7 80 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7n82 : block g126 7 82 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7n84 : block g126 7 84 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7n86 : block g126 7 86 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7n88 : block g126 7 88 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7n90 : block g126 7 90 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7n92 : block g126 7 92 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7n94 : block g126 7 94 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7n96 : block g126 7 96 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7n98 : block g126 7 98 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7n100 : block g126 7 100 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7n102 : block g126 7 102 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7n104 : block g126 7 104 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7n106 : block g126 7 106 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7n108 : block g126 7 108 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7n110 : block g126 7 110 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7n112 : block g126 7 112 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7n114 : block g126 7 114 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7n116 : block g126 7 116 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7n118 : block g126 7 118 2 = true := by decide +kernel
theorem g126B7 : block g126 7 0 120 = true := (@block_merge g126 7 0 60 60 (@block_merge g126 7 0 30 30 (@block_merge g126 7 0 14 16 (@block_merge g126 7 0 6 8 (@block_merge g126 7 0 2 4 g126P7n0 (@block_merge g126 7 2 2 2 g126P7n2 g126P7n4)) (@block_merge g126 7 6 4 4 (@block_merge g126 7 6 2 2 g126P7n6 g126P7n8) (@block_merge g126 7 10 2 2 g126P7n10 g126P7n12))) (@block_merge g126 7 14 8 8 (@block_merge g126 7 14 4 4 (@block_merge g126 7 14 2 2 g126P7n14 g126P7n16) (@block_merge g126 7 18 2 2 g126P7n18 g126P7n20)) (@block_merge g126 7 22 4 4 (@block_merge g126 7 22 2 2 g126P7n22 g126P7n24) (@block_merge g126 7 26 2 2 g126P7n26 g126P7n28)))) (@block_merge g126 7 30 14 16 (@block_merge g126 7 30 6 8 (@block_merge g126 7 30 2 4 g126P7n30 (@block_merge g126 7 32 2 2 g126P7n32 g126P7n34)) (@block_merge g126 7 36 4 4 (@block_merge g126 7 36 2 2 g126P7n36 g126P7n38) (@block_merge g126 7 40 2 2 g126P7n40 g126P7n42))) (@block_merge g126 7 44 8 8 (@block_merge g126 7 44 4 4 (@block_merge g126 7 44 2 2 g126P7n44 g126P7n46) (@block_merge g126 7 48 2 2 g126P7n48 g126P7n50)) (@block_merge g126 7 52 4 4 (@block_merge g126 7 52 2 2 g126P7n52 g126P7n54) (@block_merge g126 7 56 2 2 g126P7n56 g126P7n58))))) (@block_merge g126 7 60 30 30 (@block_merge g126 7 60 14 16 (@block_merge g126 7 60 6 8 (@block_merge g126 7 60 2 4 g126P7n60 (@block_merge g126 7 62 2 2 g126P7n62 g126P7n64)) (@block_merge g126 7 66 4 4 (@block_merge g126 7 66 2 2 g126P7n66 g126P7n68) (@block_merge g126 7 70 2 2 g126P7n70 g126P7n72))) (@block_merge g126 7 74 8 8 (@block_merge g126 7 74 4 4 (@block_merge g126 7 74 2 2 g126P7n74 g126P7n76) (@block_merge g126 7 78 2 2 g126P7n78 g126P7n80)) (@block_merge g126 7 82 4 4 (@block_merge g126 7 82 2 2 g126P7n82 g126P7n84) (@block_merge g126 7 86 2 2 g126P7n86 g126P7n88)))) (@block_merge g126 7 90 14 16 (@block_merge g126 7 90 6 8 (@block_merge g126 7 90 2 4 g126P7n90 (@block_merge g126 7 92 2 2 g126P7n92 g126P7n94)) (@block_merge g126 7 96 4 4 (@block_merge g126 7 96 2 2 g126P7n96 g126P7n98) (@block_merge g126 7 100 2 2 g126P7n100 g126P7n102))) (@block_merge g126 7 104 8 8 (@block_merge g126 7 104 4 4 (@block_merge g126 7 104 2 2 g126P7n104 g126P7n106) (@block_merge g126 7 108 2 2 g126P7n108 g126P7n110)) (@block_merge g126 7 112 4 4 (@block_merge g126 7 112 2 2 g126P7n112 g126P7n114) (@block_merge g126 7 116 2 2 g126P7n116 g126P7n118))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P8n0 : block g126 8 0 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P8n2 : block g126 8 2 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P8n4 : block g126 8 4 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P8n6 : block g126 8 6 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P8n8 : block g126 8 8 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P8n10 : block g126 8 10 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P8n12 : block g126 8 12 2 = true := by decide +kernel
theorem g126B8 : block g126 8 0 14 = true := (@block_merge g126 8 0 6 8 (@block_merge g126 8 0 2 4 g126P8n0 (@block_merge g126 8 2 2 2 g126P8n2 g126P8n4)) (@block_merge g126 8 6 4 4 (@block_merge g126 8 6 2 2 g126P8n6 g126P8n8) (@block_merge g126 8 10 2 2 g126P8n10 g126P8n12)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P9n0 : block g126 9 0 1 = true := by decide +kernel
theorem g126B9 : block g126 9 0 1 = true := g126P9n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126T : checkedTables g126 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g126 0 0 0 = true)
  · exact (rfl : block g126 1 0 0 = true)
  · exact (rfl : block g126 2 0 0 = true)
  · exact (rfl : block g126 3 0 0 = true)
  · exact g126B4
  · exact g126B5
  · exact g126B6
  · exact g126B7
  · exact g126B8
  · exact g126B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126G : graphValid g126 (boundsBefore K124) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low126 : Lower true (varsX 126) (graphGoal 126) 10 := lower_forest (g:=g126) (i:=0) (hints:=18945328) (before_sound K124 V124) g126G g126T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end PEqualNP.Outside.L_meta_32888.Certificate11481

namespace PEqualNP.Outside.L_meta_32888

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev X := Fin 8 → Bool
abbrev F := X → Bool

def Cst (f : F) : Prop := ∃ b, f = fun _ => b

def Av (s : Set F) (f : F) : Prop := Cst f ∨ ∃ u ∈ s, f = u ∨ f = fun x => !u x

def comb (t : Bool) (a b : F) : F := fun x => if t then a x && b x else a x || b x

def rs (i : Fin 8) (c : Bool) (f : F) : F := fun x => f (Function.update x i c)

def Ind (i : Fin 8) (f : F) : Prop := ∀ x b, f (Function.update x i b) = f x

def Smp (i : Fin 8) (c : Bool) (f : F) : Prop := Ind i f ∨ Cst (rs i c f)

def LI (i : Fin 8) (f : F) : Prop := Ind i f ∨ ∃ e, f = fun x => xor (x i) e

inductive Prog : Set F → F → ℕ → Prop where
  | done {s f} (h : Av s f) : Prog s f 0
  | gate {s f a b k} (t : Bool) (ha : Av s a) (hb : Av s b)
      (tail : Prog (insert (comb t a b) s) f k) : Prog s f (k + 1)

theorem av_mem {s : Set F} {f} (h : f ∈ s) : Av s f := Or.inr ⟨f, h, Or.inl rfl⟩

theorem av_ins {s : Set F} {f} (g) (h : Av s f) : Av (insert g s) f := by
  rcases h with h | ⟨u, hu, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨u, Set.mem_insert_of_mem _ hu, h⟩

theorem av_not {s : Set F} {f} (h : Av s f) : Av s (fun x => !f x) := by
  rcases h with ⟨b, rfl⟩ | ⟨u, hu, rfl | rfl⟩
  · exact Or.inl ⟨!b, rfl⟩
  · exact Or.inr ⟨_, hu, Or.inr rfl⟩
  · exact Or.inr ⟨u, hu, Or.inl (by funext x; simp)⟩

theorem av_rs {s t : Set F} {i c} (hs : ∀ u ∈ s, Av t (rs i c u)) {f} (h : Av s f) :
    Av t (rs i c f) := by
  rcases h with ⟨b, rfl⟩ | ⟨u, hu, rfl | rfl⟩
  · exact Or.inl ⟨b, rfl⟩
  · exact hs _ hu
  · exact av_not (hs _ hu)

theorem av_cheap {s : Set F} (t) {a b : F} (ha : Av s a) (hb : Av s b) (h : Cst a ∨ Cst b) :
    Av s (comb t a b) := by
  rcases h with ⟨e, rfl⟩ | ⟨e, rfl⟩
  · by_cases h : e = t
    · subst h
      rw [show comb e (fun _ => e) b = b by funext x; cases e <;> simp [comb]]
      exact hb
    · exact Or.inl ⟨e, by funext x; cases t <;> cases e <;> simp_all [comb]⟩
  · by_cases h : e = t
    · subst h
      rw [show comb e a (fun _ => e) = a by funext x; cases e <;> simp [comb]]
      exact ha
    · exact Or.inl ⟨e, by funext x; cases t <;> cases e <;> simp_all [comb]⟩

theorem smp_av {s : Set F} {i c} (hs : ∀ u ∈ s, Smp i c u) {f} (h : Av s f) : Smp i c f := by
  rcases h with ⟨b, rfl⟩ | ⟨u, hu, rfl | rfl⟩
  · exact Or.inl fun _ _ => rfl
  · exact hs _ hu
  · rcases hs _ hu with h | ⟨b, h⟩
    · exact Or.inl fun x b => congrArg not (h x b)
    · exact Or.inr ⟨!b, by funext x; exact congrArg not (congrFun h x)⟩

theorem li_av {s : Set F} {i} (hs : ∀ u ∈ s, LI i u) {f} (h : Av s f) : LI i f := by
  rcases h with ⟨b, rfl⟩ | ⟨u, hu, rfl | rfl⟩
  · exact Or.inl fun _ _ => rfl
  · exact hs _ hu
  · rcases hs _ hu with h | ⟨e, rfl⟩
    · exact Or.inl fun x b => congrArg not (h x b)
    · exact Or.inr ⟨!e, by funext x; cases e <;> simp⟩

theorem restrict {i : Fin 8} {c : Bool} {s : Set F} {f k} (p : Prog s f k) :
    ∀ t : Set F, (∀ u ∈ s, Av t (rs i c u)) →
    ∃ j ≤ k, Prog t (rs i c f) j ∧ (j = k → (∀ u ∈ s, Smp i c u) → Smp i c f) := by
  induction p with
  | done h => exact fun t hs => ⟨0, le_rfl, .done (av_rs hs h), fun _ h' => smp_av h' h⟩
  | @gate s f a b k tag ha hb tail ih =>
    intro t hs
    have pa := av_rs hs ha
    have pb := av_rs hs hb
    by_cases hc : Cst (rs i c a) ∨ Cst (rs i c b)
    · obtain ⟨j, hj, q, _⟩ := ih t (by
        intro v hv
        rcases Set.mem_insert_iff.mp hv with rfl | hu
        · exact av_cheap tag pa pb hc
        · exact hs _ hu)
      exact ⟨j, by omega, q, fun he => by omega⟩
    · obtain ⟨j, hj, q, act⟩ := ih (insert (comb tag (rs i c a) (rs i c b)) t) (by
        intro v hv
        rcases Set.mem_insert_iff.mp hv with rfl | hu
        · exact av_mem (Set.mem_insert _ _)
        · exact av_ins _ (hs _ hu))
      refine ⟨j + 1, by omega, .gate tag pa pb q, fun he ss => act (by omega) ?_⟩
      intro u hu
      rcases Set.mem_insert_iff.mp hu with rfl | hu
      · have sa := (smp_av ss ha).resolve_right (fun h => hc (.inl h))
        have sb := (smp_av ss hb).resolve_right (fun h => hc (.inr h))
        exact Or.inl fun x e => by simp only [comb, sa x e, sb x e]
      · exact ss _ hu

theorem strict {i : Fin 8} {c : Bool} {s : Set F} {f k} (p : Prog s f k) (t : Set F)
    (hs : ∀ u ∈ s, Av t (rs i c u)) (hi : ∀ u ∈ s, Smp i c u) (hf : ¬ Smp i c f) :
    ∃ j, j + 1 ≤ k ∧ Prog t (rs i c f) j := by
  obtain ⟨j, hj, q, h⟩ := restrict p t hs
  exact ⟨j, lt_of_le_of_ne hj (fun he => hf (h he hi)), q⟩

theorem li_smp {i c f} (h : LI i f) : Smp i c f := by
  rcases h with h | ⟨e, rfl⟩
  · exact Or.inl h
  · exact Or.inr ⟨xor c e, by funext x; simp [rs]⟩

theorem kill {i : Fin 8} {t : Bool} {a b : F} (h : (∃ e, a = fun x => xor (x i) e) ∨
    ∃ e, b = fun x => xor (x i) e) : ∃ c, Cst (rs i c (comb t a b)) := by
  rcases h with ⟨e, rfl⟩ | ⟨e, rfl⟩
  · refine ⟨xor e (!t), !t, ?_⟩
    funext x
    cases t <;> cases e <;> simp [rs, comb]
  · refine ⟨xor e (!t), !t, ?_⟩
    funext x
    cases t <;> cases e <;> simp [rs, comb]

theorem double {i : Fin 8} {s : Set F} {f k} (p : Prog s f k) (hs : ∀ u ∈ s, LI i u)
    (hf : ∀ c, ¬ Smp i c f) :
    ∃ c, ∀ t : Set F, (∀ u ∈ s, Av t (rs i c u)) → ∃ j, j + 2 ≤ k ∧ Prog t (rs i c f) j := by
  induction p with
  | done h => exact absurd (li_smp (li_av hs h)) (hf true)
  | @gate s f a b k tag ha hb tail ih =>
    by_cases hl : (∃ e, a = fun x => xor (x i) e) ∨ ∃ e, b = fun x => xor (x i) e
    · obtain ⟨c, hc⟩ := kill (t := tag) hl
      refine ⟨c, fun t ht => ?_⟩
      obtain ⟨j, hj, q⟩ := strict tail t (by
        intro u hu
        rcases Set.mem_insert_iff.mp hu with rfl | hu
        · exact Or.inl hc
        · exact ht _ hu) (by
        intro u hu
        rcases Set.mem_insert_iff.mp hu with rfl | hu
        · exact Or.inr hc
        · exact li_smp (hs _ hu)) (hf c)
      exact ⟨j, by omega, q⟩
    · have ia := (li_av hs ha).resolve_right (fun h => hl (.inl h))
      have ib := (li_av hs hb).resolve_right (fun h => hl (.inr h))
      obtain ⟨c, hc⟩ := ih (by
        intro u hu
        rcases Set.mem_insert_iff.mp hu with rfl | hu
        · exact Or.inl fun x e => by simp only [comb, ia x e, ib x e]
        · exact hs _ hu) hf
      refine ⟨c, fun t ht => ?_⟩
      obtain ⟨j, hj, q⟩ := hc (insert (comb tag (rs i c a) (rs i c b)) t) (by
        intro u hu
        rcases Set.mem_insert_iff.mp hu with rfl | hu
        · exact av_mem (Set.mem_insert _ _)
        · exact av_ins _ (ht _ hu))
      exact ⟨j + 1, by omega, .gate tag (av_rs ht ha) (av_rs ht hb) q⟩

def stock : Set F := Set.range fun (i : Fin 8) (x : X) => x i

theorem stock_li (i) : ∀ u ∈ stock, LI i u := by
  rintro _ ⟨j, rfl⟩
  by_cases h : j = i
  · subst h
    exact Or.inr ⟨false, by simp⟩
  · exact Or.inl fun x b => by simp [Function.update_of_ne h]

theorem stock_rs (i c) : ∀ u ∈ stock, Av stock (rs i c u) := by
  rintro _ ⟨j, rfl⟩
  by_cases h : j = i
  · subst h
    exact Or.inl ⟨c, by funext x; simp [rs]⟩
  · exact Or.inr ⟨_, ⟨j, rfl⟩, Or.inl (by funext x; simp [rs, Function.update_of_ne h])⟩

def pt (n : ℕ) : X := fun i => n.testBit i

theorem good_at {i c f} (a b d : ℕ)
    (h : (f (Function.update (pt a) i true) != f (pt a)) &&
        (rs i c f (pt b) != rs i c f (pt d)) = true) : ¬ Smp i c f := by
  simp only [Bool.and_eq_true, bne_iff_ne] at h
  obtain ⟨ha, hb⟩ := h
  rintro (hi | ⟨v, e⟩)
  · exact ha (hi _ _)
  · rw [e] at hb
    simp at hb

def Low (n : ℕ) (f : F) : Prop := ∀ k, Prog stock f k → n ≤ k

theorem zero (f : F) : Low 0 f := fun _ _ => Nat.zero_le _

theorem one {n f} (i c) (h : ¬ Smp i c f) (t : Low n (rs i c f)) : Low (n + 1) f := by
  intro k p
  obtain ⟨j, hj, q⟩ := strict p stock (stock_rs i c) (fun u hu => li_smp (stock_li i u hu))
    h
  have := t j q
  omega

theorem two {n f} (i) (h0 : ¬ Smp i false f) (h1 : ¬ Smp i true f)
    (t0 : Low n (rs i false f)) (t1 : Low n (rs i true f)) : Low (n + 2) f := by
  intro k p
  obtain ⟨c, hc⟩ := double p (stock_li i) (by
    intro c
    cases c
    · exact h0
    · exact h1)
  obtain ⟨j, hj, q⟩ := hc stock (stock_rs i c)
  cases c
  · have := t0 j q
    omega
  · have := t1 j q
    omega

def rd (w : List F) (i : ℕ) : F := fun x => (w.map fun f => f x).getD i false

def gv (w : List F) (g : Gate) : F := fun x => g.op.eval (g.inputs.map fun i => rd w i x)

theorem rd_av {s : Set F} {w : List F} (hw : ∀ u ∈ w, Av s u) (i : ℕ) : Av s (rd w i) := by
  by_cases h : i < w.length
  · have e : rd w i = w[i] := by funext x; simp [rd, h]
    rw [e]
    exact hw _ (List.getElem_mem h)
  · exact Or.inl ⟨false, by funext x; simp [rd, Nat.le_of_not_lt h]⟩

theorem gv_av {s : Set F} {w : List F} (hw : ∀ u ∈ w, Av s u) (g : Gate)
    (hop : g.op = .and ∨ g.op = .or ∨ g.op = .not) (hl : g.inputs.length ≤ 2) :
    Av s (gv w g) ∨ (g.op ≠ .not ∧ ∃ t a b, Av s a ∧ Av s b ∧ gv w g = comb t a b) := by
  obtain ⟨op, args⟩ := g
  simp only at hop hl
  rcases args with _ | ⟨i, _ | ⟨j, _ | ⟨k, r⟩⟩⟩
  · left
    exact Or.inl ⟨op.eval [], by funext x; simp [gv]⟩
  · left
    rcases hop with rfl | rfl | rfl
    · rw [show gv w ⟨.and, [i]⟩ = rd w i by funext x; simp [gv, GateOp.eval]]
      exact rd_av hw i
    · rw [show gv w ⟨.or, [i]⟩ = rd w i by funext x; simp [gv, GateOp.eval]]
      exact rd_av hw i
    · rw [show gv w ⟨.not, [i]⟩ = fun x => !rd w i x by funext x; simp [gv, GateOp.eval]]
      exact av_not (rd_av hw i)
  · rcases hop with rfl | rfl | rfl
    · exact Or.inr ⟨by simp, true, _, _, rd_av hw i, rd_av hw j,
        by funext x; simp [gv, GateOp.eval, comb]⟩
    · exact Or.inr ⟨by simp, false, _, _, rd_av hw i, rd_av hw j,
        by funext x; simp [gv, GateOp.eval, comb]⟩
    · left
      rw [show gv w ⟨.not, [i, j]⟩ = fun x => !rd w i x by funext x; simp [gv, GateOp.eval]]
      exact av_not (rd_av hw i)
  · simp at hl

def isNot (g : Gate) : Bool := match g.op with
  | .not => true
  | _ => false

theorem toProg (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2) (o : ℕ) :
    ∀ (w : List F) (s : Set F), (∀ u ∈ w, Av s u) →
    ∃ k ≤ (gs.filter fun g => !isNot g).length,
      Prog s (rd (gs.foldl (fun w g => w ++ [gv w g]) w) o) k := by
  induction gs with
  | nil => exact fun w s hw => ⟨0, le_rfl, .done (rd_av hw o)⟩
  | cons g gs ih =>
    intro w s hw
    have hg' := hg g (by simp)
    have ih := ih fun v hv => hg v (by simp [hv])
    have hlen : (gs.filter fun g => !isNot g).length ≤
        ((g :: gs).filter fun g => !isNot g).length := by
      rw [List.filter_cons]
      split <;> simp
    rcases gv_av hw g hg'.1 hg'.2 with h | ⟨hn, t, a, b, ha, hb, e⟩
    · obtain ⟨k, hk, p⟩ := ih (w ++ [gv w g]) s (by
        intro u hu
        rcases List.mem_append.mp hu with h' | h'
        · exact hw _ h'
        · rw [List.mem_singleton.mp h']
          exact h)
      exact ⟨k, hk.trans hlen, p⟩
    · obtain ⟨k, hk, p⟩ := ih (w ++ [gv w g]) (insert (comb t a b) s) (by
        intro u hu
        rcases List.mem_append.mp hu with h' | h'
        · exact av_ins _ (hw _ h')
        · rw [List.mem_singleton.mp h', e]
          exact av_mem (Set.mem_insert _ _))
      refine ⟨k + 1, ?_, .gate t ha hb p⟩
      have : isNot g = false := by
        rcases hg'.1 with h | h | h
        · simp [isNot, h]
        · simp [isNot, h]
        · exact absurd h hn
      simp [this]
      simpa using hk

theorem fold_eval (gs : List Gate) (x : X) : ∀ w : List F,
    (gs.foldl (fun w g => w ++ [gv w g]) w).map (fun f => f x) =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (w.map fun f => f x) := by
  induction gs with
  | nil => exact fun _ => rfl
  | cons g gs ih =>
    intro w
    simp only [List.foldl_cons, ih, List.map_append, List.map_cons, List.map_nil]
    rfl

theorem all_not_not_of_guillabert_pr42591 {n : ℕ} {f : F} (hl : Low n f) (gs : List Gate) (o : ℕ)
    (hg : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hn : gs.length ≤ n)
    (he : ∀ x : X, Circuit.eval ⟨gs, o⟩ (List.ofFn x) = f x) :
    ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  obtain ⟨k, hk, p⟩ := toProg gs hg o
    (List.ofFn fun (i : Fin 8) (x : X) => x i) stock (by
      intro u hu
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hu
      exact av_mem ⟨i, rfl⟩)
  have e : rd (gs.foldl (fun w g => w ++ [gv w g])
      (List.ofFn fun (i : Fin 8) (x : X) => x i)) o = f := by
    funext x
    rw [← he x, rd, fold_eval, List.map_ofFn]
    rfl
  rw [e] at p
  have h := hl k p
  have hle := List.length_filter_le (fun g => !isNot g) gs
  have hall : ∀ g ∈ gs, (!isNot g) = true := by
    rw [← List.length_filter_eq_length_iff]
    omega
  intro g hm
  have h2 := hall g hm
  refine ⟨?_, (hg g hm).2⟩
  rcases (hg g hm).1 with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · simp [isNot, h] at h2

private theorem signed_av {s : Set F} (point : Certificate11481.Row → X)
    {bank : List (Certificate11481.Wire Certificate11481.Row)}
    (hs : ∀ v ∈ s, Certificate11481.Available true bank (fun r => v (point r)))
    {f : F} (h : Av s f) :
    Certificate11481.Available true bank (fun r => f (point r)) := by
  rcases h with ⟨b,rfl⟩ | ⟨a,ha,rfl | rfl⟩
  · exact Or.inr (Or.inl ⟨b,rfl⟩)
  · exact hs _ ha
  · exact Certificate11481.avail_inv rfl (hs _ ha)

private theorem signed_prog {s : Set F} {f : F} {k : Nat} (p : Prog s f k)
    (point : Certificate11481.Row → X) (roots : List (Certificate11481.Wire Certificate11481.Row)) :
    ∀ m bank, Certificate11481.Reach true roots m bank →
      (∀ v ∈ s, Certificate11481.Available true bank (fun r => v (point r))) →
      ∃ pool, Certificate11481.Reach true roots (m+k) pool ∧
        Certificate11481.Available true pool (fun r => f (point r)) := by
  induction p with
  | done h => intro m bank hm hs; exact ⟨bank,hm,signed_av point hs h⟩
  | @gate s f a b k tag ha hb tail ih =>
    intro m bank hm hs
    let a' := fun r => a (point r)
    let b' := fun r => b (point r)
    let w := Certificate11481.combine (!tag) a' b'
    have hl : (fun r => comb tag a b (point r)) = w := by
      cases tag <;> rfl
    have hr : Certificate11481.Reach true roots (m+1) (w :: bank) :=
      Certificate11481.Reach.two (!tag) hm (signed_av point hs ha) (signed_av point hs hb)
    obtain ⟨pool,hp,hv⟩ := ih (m+1) (w :: bank) hr (by
      intro v h
      rcases Set.mem_insert_iff.mp h with rfl | h
      · rw [hl]
        exact Or.inl (List.mem_cons_self)
      · exact Certificate11481.available_cons w (hs _ h))
    exact ⟨pool,by simpa only [Nat.add_assoc, Nat.add_comm 1 k] using hp,hv⟩

private theorem from_signed_simonsickle_pr15587 {f : F} {L : Nat}
    {roots : List Certificate11481.Sig} {targetWord : Certificate11481.Sig}
    (cols : Fin 8 → Certificate11481.Sig)
    (hcols : ∀ i, cols i ∈ roots ∨ cols i = Certificate11481.zero)
    (he : ∀ r : Certificate11481.Row, Certificate11481.bit r targetWord =
      f (fun i => Certificate11481.bit r (cols i)))
    (h : Certificate11481.Lower true roots targetWord L) : Low L f := by
  intro k p
  let point := fun r i => Certificate11481.bit r (cols i)
  obtain ⟨pool,hp,hv⟩ := signed_prog p point (roots.map Certificate11481.observe) 0
    (roots.map Certificate11481.observe) Certificate11481.Reach.start (by
      rintro _ ⟨i,rfl⟩
      rcases hcols i with hmem | hz
      · exact Or.inl (List.mem_map.mpr ⟨cols i,hmem,rfl⟩)
      · apply Or.inr; apply Or.inl
        exact ⟨false,by funext r; change Certificate11481.bit r (cols i) = false
                        rw [hz]; simp [Certificate11481.bit,Certificate11481.zero]⟩)
  have eq : Certificate11481.observe targetWord = fun r => f (point r) := funext he
  rw [← eq] at hv
  exact h k pool (by simpa using hp) hv

def target : F := fun x => (x 0 && x 4) || (x 1 && x 4) || (x 0 && x 5) || (x 2 && x 5) || (x 0 && x 6) || (x 3 && x 6) || (x 4 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 2 && x 7) || (x 4 && x 7) || (x 5 && x 7) || (x 6 && x 7)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem lower : Low 13 target := (two 3 (good_at 64 17 0 (by decide +kernel)) (good_at 64 17 0 (by decide +kernel)) (one 6 false (good_at 1 17 0 (by decide +kernel)) (from_signed_simonsickle_pr15587 (f := (rs 6 false (rs 3 false target))) ![(Certificate11481.inputs.getD 3 Certificate11481.zero), (Certificate11481.inputs.getD 4 Certificate11481.zero), (Certificate11481.inputs.getD 2 Certificate11481.zero), Certificate11481.zero, (Certificate11481.inputs.getD 1 Certificate11481.zero), (Certificate11481.inputs.getD 5 Certificate11481.zero), Certificate11481.zero, (Certificate11481.inputs.getD 6 Certificate11481.zero)] (by decide +kernel) (by decide +kernel) Certificate11481.low126)) (one 6 false (good_at 0 17 0 (by decide +kernel)) (from_signed_simonsickle_pr15587 (f := (rs 6 false (rs 3 true target))) ![(Certificate11481.inputs.getD 3 Certificate11481.zero), (Certificate11481.inputs.getD 4 Certificate11481.zero), (Certificate11481.inputs.getD 2 Certificate11481.zero), Certificate11481.zero, (Certificate11481.inputs.getD 1 Certificate11481.zero), (Certificate11481.inputs.getD 5 Certificate11481.zero), Certificate11481.zero, (Certificate11481.inputs.getD 6 Certificate11481.zero)] (by decide +kernel) (by decide +kernel) Certificate11481.low126)))

def witness : List Gate := [⟨.or, [0, 1]⟩, ⟨.or, [4, 7]⟩, ⟨.and, [8, 9]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [11, 6]⟩, ⟨.or, [0, 7]⟩, ⟨.and, [12, 13]⟩, ⟨.or, [5, 7]⟩, ⟨.and, [2, 15]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [17, 6]⟩, ⟨.or, [10, 14]⟩, ⟨.or, [19, 16]⟩, ⟨.or, [20, 18]⟩]

theorem witness_ok : ∀ g ∈ witness, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  simp [witness]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem witness_eval : ∀ x : X, Circuit.eval ⟨witness, 21⟩ (List.ofFn x) = target x := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem target_eq : ∀ x : X, target x = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  decide +kernel

end PEqualNP.Outside.L_meta_32888

open PEqualNP.Outside.L_meta_32888 in
theorem PEqualNP.Outside.L_meta_32888 : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) := by
  intro gates o hg _ he
  by_cases hs : 14 ≤ gates.length
  · exact ⟨witness, 21, witness_ok, hs, fun x => (witness_eval x).trans (target_eq x)⟩
  · exact ⟨gates, o, all_not_not_of_guillabert_pr42591 lower gates o hg (by omega)
      (fun x => (he x).trans (target_eq x).symm), le_rfl, he⟩

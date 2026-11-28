import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_31153_aux


open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 256
def zero : Sig := 0
def one : Sig := BitVec.allOnes 256
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

def bit (i : Fin 256) (a : Sig) : Bool := a.getLsbD i.val
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


abbrev Row := Fin 256
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

def Lower (u : Bool) (roots : List Sig) (T : Sig) (L : Nat) : Prop :=
  ∀ p bank, Reach u (roots.map observe) p bank → Available u bank (observe T) → L ≤ p

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
  if h : r.val < 256-d.val then ⟨d.val+r.val,by omega⟩ else ⟨r.val-(256-d.val),by omega⟩
def backwards (d : Row) : Row := Fin.ofNat 256 (256-d.val)
def rowMove (m : Move) (r : Row) : Row :=
  if bit r m.1 then shifted m.2.2 r else if bit r m.2.1 then shifted (backwards m.2.2) r else r
def mux (m a b : Sig) := (m &&& a) ||| (~~~m &&& b)
def wordMove (m : Move) (a : Sig) :=
  mux m.1 (a.rotateRight m.2.2.val) (mux m.2.1 (a.rotateRight (backwards m.2.2).val) a)

theorem bit_shift (d r : Row) (a : Sig) : bit r (a.rotateRight d.val) = bit (shifted d r) a := by
  unfold bit
  rw [BitVec.getLsbD_rotateRight_of_lt d.isLt]
  by_cases h : r.val < 256-d.val <;> simp [shifted,h,r.isLt]

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

abbrev Cut := Sig × Nat × List Sig

def cutTest (c : Cut) (k : Nat) (ws : List Sig) : Bool :=
  decide (k < c.2.1 + ws.countP (isMaskedConstant c.1)) &&
    ws.all fun w => masked c.1 w == zero || c.2.2.contains (masked c.1 w)

def CutGood (T : Sig) (c : Cut) : Prop :=
  ∀ k ws, ws.Nodup → cutTest c k ws = true → Impossible true T k ws.toFinset

theorem cut_good {T d raw L} (s : Slice true raw T d L) (cs : List Choice)
    {pool} (hp : makePool true d raw cs = some pool) (afford : cs.length ≤ L) :
    CutGood T (d,L-cs.length,pool.map (masked d)) := by
  intro k ws nd checked
  simp only [cutTest,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at checked
  apply poolCut_sound s cs hp nd
  apply Bool.and_eq_true_iff.mpr
  refine ⟨decide_eq_true (by omega),List.all_eq_true.mpr ?_⟩
  intro w hw
  rcases Bool.or_eq_true_iff.mp (checked.2 w hw) with hz | hm
  · simp [availableB,hz]
  · have mem := List.contains_iff_mem.mp hm
    obtain ⟨v,hv,eq⟩ := List.mem_map.mp mem
    have yes : ((pool.map (masked d)).any fun z => z == masked d w) = true :=
      List.any_eq_true.mpr ⟨masked d v,List.mem_map_of_mem hv,beq_iff_eq.mpr eq⟩
    simp [availableB,yes]

def properB (w : Sig) := w != zero && w != one
theorem proper_of (w : Sig) (h : properB w = true) : proper w := by
  simpa only [properB,proper,Bool.and_eq_true,bne_iff_ne] using h

def bothFlags : List Bool := [false,true]
theorem has_flag (b : Bool) : b ∈ bothFlags := by cases b <;> decide

def moves (ws : List Sig) (k : Nat) (a b : Sig) : List (List Sig) :=
  ([0,1,2,3] : List Nat).flatMap fun d =>
    let z := bin d a b
    if properB z && !ws.contains z then
      bothFlags.flatMap fun ka =>
        (bothFlags.map fun kb => childTwo ws a b d ka kb).filter fun v => decide (v.length ≤ k)
    else []

def children (ws : List Sig) (k : Nat) : List (List Sig) :=
  ws.flatMap fun a => ws.flatMap fun b => if a < b then moves ws k a b else []

theorem listed {ws : List Sig} {k a b d ka kb} (ha : a ∈ ws) (hb : b ∈ ws)
    (ab : a < b) (legal : allowed true d) (fresh : bin d a b ∉ ws) (pr : proper (bin d a b))
    (short : (childTwo ws a b d ka kb).length ≤ k) : childTwo ws a b d ka kb ∈ children ws k := by
  apply List.mem_flatMap.mpr
  refine ⟨a,ha,List.mem_flatMap.mpr ⟨b,hb,?_⟩⟩
  rw [if_pos ab]
  have dm : d ∈ ([0,1,2,3] : List Nat) := by
    rcases allowed_four legal with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> decide
  apply List.mem_flatMap.mpr
  refine ⟨d,dm,?_⟩
  have ready : (properB (bin d a b) && !ws.contains (bin d a b)) = true := by
    simp [properB,pr.1,pr.2,fresh]
  dsimp only
  rw [if_pos ready]
  exact List.mem_flatMap.mpr ⟨ka,has_flag ka,List.mem_filter.mpr
    ⟨List.mem_map_of_mem (f:=fun kb => childTwo ws a b d ka kb) (has_flag kb),decide_eq_true short⟩⟩

theorem swapped {ws : List Sig} {a b d} (h : allowed true d) (ka kb : Bool) :
    (childTwo ws a b d ka kb).Perm (childTwo ws b a (flipOp d) kb ka) := by
  unfold childTwo
  rw [bin_flip h a b,List.erase_comm a b]
  apply List.Perm.cons
  cases ka <;> cases kb <;> simp [kept,List.Perm.swap]

theorem by_children {T k ws} (nd : ws.Nodup) (absent : T ∉ ws)
    (h : ∀ w ∈ children ws k, Impossible true T (k-1) w.toFinset) : Impossible true T k ws.toFinset := by
  apply enum_step nd absent
  intro a ha b hb d leg ka kb ne fresh pr short
  rcases lt_or_gt_of_ne (show a.toNat ≠ b.toNat from fun e => ne (BitVec.eq_of_toNat_eq e)) with ab | ba
  · exact h _ (listed ha hb ab leg fresh pr short)
  · have p := swapped leg (ws:=ws) (a:=a) (b:=b) ka kb
    have e := bin_flip leg a b
    have other := listed hb ha ba (flip_flip leg).1 (e ▸ fresh) (e ▸ pr)
      (ka:=kb) (kb:=ka) (p.length_eq ▸ short)
    have eq : (childTwo ws a b d ka kb).toFinset = (childTwo ws b a (flipOp d) kb ka).toFinset := by
      ext w
      simpa only [List.mem_toFinset] using (p.mem_iff (a:=w))
    rw [eq]
    exact h _ other

def sameWires (ws vs : List Sig) := ws.all vs.contains && vs.all ws.contains
theorem same_wires {ws vs} (ok : sameWires ws vs = true) : ws.toFinset = vs.toFinset := by
  obtain ⟨l,r⟩ := Bool.and_eq_true_iff.mp ok
  ext a
  simp only [List.mem_toFinset]
  exact ⟨fun ha => List.contains_iff_mem.mp (List.all_eq_true.mp l _ ha),
    fun ha => List.contains_iff_mem.mp (List.all_eq_true.mp r _ ha)⟩

abbrev Cuts (T : Sig) := List {c : Cut // CutGood T c}
abbrev Links (T : Sig) (k : Nat) := List {ws : List Sig // Impossible true T k ws.toFinset}

def closeCase (T : Sig) (k : Nat) (cuts : Cuts T) (links : Links T k) (ws : List Sig) (code : Nat) :=
  if code < 65536 then
    let r := Fin.ofNat 256 (code % 256)
    let s := Fin.ofNat 256 (code / 256)
    (bit r T != bit s T) && ws.all (fun w => bit r w == bit s w)
  else if code < 131072 then
    match cuts[code-65536]? with
    | none => false
    | some c => decide ws.Nodup && cutTest c.val k ws
  else
    match links[code-131072]? with
    | none => false
    | some v => sameWires ws v.val

theorem close_ok {T k cuts links ws code} (ok : closeCase T k cuts links ws code = true) :
    Impossible true T k ws.toFinset := by
  unfold closeCase at ok
  split at ok
  · simp only [Bool.and_eq_true,bne_iff_ne,List.all_eq_true,beq_iff_eq] at ok
    intro n _ run
    obtain ⟨w,hw,ne⟩ := live_row_difference run ok.1
    exact ne (ok.2 w (List.mem_toFinset.mp hw))
  · split at ok
    · split at ok
      · contradiction
      · rename_i c _
        obtain ⟨nd,good⟩ := Bool.and_eq_true_iff.mp ok
        exact c.property k ws (of_decide_eq_true nd) good
    · split at ok
      · contradiction
      · rename_i v _
        rw [same_wires ok]
        exact v.property

def checkMoves (T : Sig) (k : Nat) (cuts : Cuts T) (links : Links T k) :
    List (List Sig) → Nat → Bool
  | [],_ => true
  | ws::rest,data => closeCase T k cuts links ws (data % 262144) &&
      checkMoves T k cuts links rest (data / 262144)

theorem moves_ok {T k cuts links vs data} (ok : checkMoves T k cuts links vs data = true) :
    ∀ w ∈ vs, Impossible true T k w.toFinset := by
  induction vs generalizing data with
  | nil => simp
  | cons v vs ih =>
    obtain ⟨closed,tail⟩ := Bool.and_eq_true_iff.mp ok
    intro w hw
    rcases List.mem_cons.mp hw with rfl | hm
    · exact close_ok closed
    · exact ih tail _ hm

def checkNode (T : Sig) (k : Nat) (ws : List Sig) (cuts : Cuts T) (links : Links T (k-1)) (data : Nat) :=
  (decide ws.Nodup && !ws.contains T) && checkMoves T (k-1) cuts links (children ws k) data

theorem node_ok {T k ws} (cuts : Cuts T) (links : Links T (k-1)) (data : Nat)
    (ok : checkNode T k ws cuts links data = true) : Impossible true T k ws.toFinset := by
  obtain ⟨head,tail⟩ := Bool.and_eq_true_iff.mp ok
  obtain ⟨hn,hm⟩ := Bool.and_eq_true_iff.mp head
  exact by_children (of_decide_eq_true hn) (by simpa using hm) (moves_ok tail)

def inputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00, 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000, 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000, 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000, 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000]
def input (i : Nat) := inputs.getD i zero
def selected (m : Nat) := (List.range 8).filter (fun i => m.testBit i)
def roots (m : Nat) := (selected m).map input


def goalAt (m : Nat) : Sig :=
  let x := fun i => if m.testBit i then input i else zero
  (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 2 &&& x 5) ||| (x 3 &&& x 5) ||| (x 0 &&& x 6) ||| (x 2 &&& x 6) ||| (x 4 &&& x 6) ||| (x 5 &&& x 6) ||| (x 2 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)


def fixes (q : Nat) : List Move :=
  ((List.range 8).filter fun i => !(q.testBit i)).map fun i =>
    (zero,input i,Fin.ofNat 256 (1 <<< i))

def domain (q : Nat) : Sig :=
  ((List.range 8).filter fun i => !(q.testBit i)).foldl (fun d i => d &&& neg (input i)) one

def tests (m hints : Nat) : List (Sig × Row × Row) :=
  (selected m).map fun i =>
    let r := 1 <<< ((hints >>> (4*i)) % 16)
    (input i,Fin.ofNat 256 r,Fin.ofNat 256 (r ||| (1 <<< i)))

def Claim (m L : Nat) : Prop := Lower true (roots m) (goalAt m) L

def essTest (m hints : Nat) :=
  (properB (goalAt m) && checkEssential (goalAt m) (roots m) (tests m hints)) &&
    ((tests m hints).map Prod.fst == roots m)

theorem fromSearch {m k} (hints : Nat) (checked : essTest m hints = true)
    (no : Impossible true (goalAt m) k (roots m).toFinset) : Claim m (k+1) := by
  simp only [essTest,Bool.and_eq_true,beq_iff_eq] at checked
  have ok := checked.1.2
  apply lower_impossible (proper_of _ checked.1.1) (essential_plain ok).1 (essential_plain ok).2 _ no
  intro w hw
  apply essential_ok ok w
  rw [checked.2]
  exact List.mem_toFinset.mpr hw

def liftTest (m q a b e hints : Nat) :=
  ((checkLift (fixes q) (goalAt m) (roots m) (roots q) (goalAt q) (tests e hints) &&
    properB (goalAt m)) && properB (goalAt q)) &&
      decide (b ≤ a+((tests e hints).map Prod.fst).toFinset.card)

theorem fromLift {m q a} (b e hints : Nat) (lower : Claim q a)
    (ok : liftTest m q a b e hints = true) : Claim m b := by
  simp only [liftTest,Bool.and_eq_true,decide_eq_true_eq] at ok
  have lb := lift_ok ok.1.1.1 (proper_of _ ok.1.1.2) (proper_of _ ok.1.2) lower
  exact fun p bank hr ha => ok.2.trans (lb p bank hr ha)

def poolFor (q : Nat) (extra : Option Choice) : List Sig :=
  match extra with
  | none => roots q
  | some c => choiceVal c :: roots q

def ruleTest (m q L : Nat) (e : Option Choice) : Bool :=
  (((checkMap (fixes q) (roots q) (goalAt m) (roots q) (goalAt q) &&
    (movedWord (fixes q) (domain q) == one)) && properB (goalAt q)) &&
    (makePool true (domain q) (roots q) e.toList == some (poolFor q e))) &&
    decide (e.toList.length ≤ L)

def ruleFor (m : Nat) {q L} (lo : Claim q L) (e : Option Choice)
    (ok : ruleTest m q L e = true) : {c : Cut // CutGood (goalAt m) c} := by
  refine ⟨(domain q,L-e.toList.length,(poolFor q e).map (masked (domain q))),?_⟩
  simp only [ruleTest,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at ok
  exact cut_good (slice_correct ok.1.1.1.1 ok.1.1.1.2 (proper_of _ ok.1.1.2) lo)
    e.toList ok.1.2 ok.2




def cuts224 : Cuts (goalAt 224) := []

def state224_0 : List Sig := roots 224
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude224_0 : Impossible true (goalAt 224) 3 state224_0.toFinset :=
  node_ok cuts224 [] 0x30100602030100a02030200c08030100c08030200a02018080602028080604018100c04028200a08028080a08028200c04018100604018080a08028200c08018100c08018080604018100c08028200a080 (by decide +kernel)

theorem lower224 : Claim 224 4 :=
  fromSearch 1432354816 (by decide +kernel) exclude224_0

def cuts196 : Cuts (goalAt 196) := []

def state196_0 : List Sig := roots 196
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude196_0 : Impossible true (goalAt 196) 3 state196_0.toFinset :=
  node_ok cuts196 [] 0x30100440430100840430200c08030100c08030200840411010440421010444011100c04021200848021010848021200c04011100444011010848021200c08011100c08011010444011100c080212008480 (by decide +kernel)

theorem lower196 : Claim 196 4 :=
  fromSearch 570426880 (by decide +kernel) exclude196_0

def cuts164 : Cuts (goalAt 164) := []

def state164_0 : List Sig := roots 164
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude164_0 : Impossible true (goalAt 164) 3 state164_0.toFinset :=
  node_ok cuts164 [] 0x28080240428080840428200a08028080a08028200840409010240421010242009080a02021200848021010848021200a02009080242009010848021200a08009080a08009010242009080a080212008480 (by decide +kernel)

theorem lower164 : Claim 164 4 :=
  fromSearch 538969344 (by decide +kernel) exclude164_0

def rule228_0 : {c : Cut // CutGood (goalAt 228) c} :=
  ruleFor 228 lower224 none (by decide +kernel)

def rule228_1 : {c : Cut // CutGood (goalAt 228) c} :=
  ruleFor 228 lower196 none (by decide +kernel)

def rule228_2 : {c : Cut // CutGood (goalAt 228) c} :=
  ruleFor 228 lower164 none (by decide +kernel)

def cuts228 : Cuts (goalAt 228) := [rule228_0,rule228_1,rule228_2]

def state228_0 : List Sig := roots 228
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude228_0 : Impossible true (goalAt 228) 5 state228_0.toFinset :=
  node_ok cuts228 [] 0x40008c04018080c04040008a02030200c08040008c04030200c08040008a02018080602040004a02018100604040004c04028200a08040004a02028200a08040004c04018100604040004602028200a08040004c08018100c08040004602018100604040004c08028200a08040000840411100444040000c04021200848040000840421200848040000c04011100444040000440421200848040000c08011100c08040000440411100444040000c08021200848040000240421200848040000a08009080a08040000240409080242040000a080212008480 (by decide +kernel)

theorem lower228 : Claim 228 6 :=
  fromSearch 572523776 (by decide +kernel) exclude228_0

def cuts208 : Cuts (goalAt 208) := []

def state208_0 : List Sig := roots 208
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude208_0 : Impossible true (goalAt 208) 3 state208_0.toFinset :=
  node_ok cuts208 [] 0x30100501030100901030200c08030100c08030200901014040501024040504014100c04024200908024040908024200c04014100504014040908024200c08014100c08014040504014100c080242009080 (by decide +kernel)

theorem lower208 : Claim 208 4 :=
  fromSearch 1141243904 (by decide +kernel) exclude208_0

theorem lower212 : Claim 212 5 :=
  fromLift 5 4 570820096 lower208 (by decide +kernel)

theorem lower240 : Claim 240 5 :=
  fromLift 5 16 1147535360 lower224 (by decide +kernel)

theorem lower180 : Claim 180 5 :=
  fromLift 5 16 539428096 lower164 (by decide +kernel)

def cuts100 : Cuts (goalAt 100) := []

def state100_0 : List Sig := roots 100
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude100_0 : Impossible true (goalAt 100) 3 state100_0.toFinset :=
  node_ok cuts100 [] 0x180802404180804404181006040180806040181004404090102404110102420090806020111004440110104440111006020090802420090104440111006040090806040090102420090806040111004440 (by decide +kernel)

theorem lower100 : Claim 100 4 :=
  fromSearch 35652864 (by decide +kernel) exclude100_0

theorem lower116 : Claim 116 5 :=
  fromLift 5 16 36046080 lower100 (by decide +kernel)

def rule244_0 : {c : Cut // CutGood (goalAt 244) c} :=
  ruleFor 244 lower228 none (by decide +kernel)

def rule244_1 : {c : Cut // CutGood (goalAt 244) c} :=
  ruleFor 244 lower212 none (by decide +kernel)

def rule244_2 : {c : Cut // CutGood (goalAt 244) c} :=
  ruleFor 244 lower208 none (by decide +kernel)

def rule244_3 : {c : Cut // CutGood (goalAt 244) c} :=
  ruleFor 244 lower240 none (by decide +kernel)

def rule244_4 : {c : Cut // CutGood (goalAt 244) c} :=
  ruleFor 244 lower180 none (by decide +kernel)

def rule244_5 : {c : Cut // CutGood (goalAt 244) c} :=
  ruleFor 244 lower116 none (by decide +kernel)

def rule244_6 : {c : Cut // CutGood (goalAt 244) c} :=
  ruleFor 244 lower224 none (by decide +kernel)

def rule244_7 : {c : Cut // CutGood (goalAt 244) c} :=
  ruleFor 244 lower100 none (by decide +kernel)

def rule244_8 : {c : Cut // CutGood (goalAt 244) c} :=
  ruleFor 244 lower164 none (by decide +kernel)

def rule244_9 : {c : Cut // CutGood (goalAt 244) c} :=
  ruleFor 244 lower196 none (by decide +kernel)

def cuts244 : Cuts (goalAt 244) := [rule244_0,rule244_1,rule244_2,rule244_3,rule244_4,rule244_5,rule244_6,rule244_7,rule244_8,rule244_9]

def state244_0 : List Sig := [0xfffffffffffffffffffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0,input 7,input 6,0xfffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_0 : Impossible true (goalAt 244) 4 state244_0.toFinset :=
  node_ok cuts244 [] 0x28200c08018100a08018100a0802820060400d0c0a08028201000221200a08009050848021200c0801110084801110084802120044400d0c0848021201000030100c080302004414190c0a430 (by decide +kernel)

def state244_1 : List Sig := [0xfffffffffffffffff0f0f0f0f0f0f0f0,input 7,input 6,0xfffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_1 : Impossible true (goalAt 244) 4 state244_1.toFinset :=
  node_ok cuts244 [] 0xa08030200604028200604028200a08018100848028200241421200848030200444021200444021200848011100e43030200c080290c0604028200604028200444021200444021200343030200441430200c040 (by decide +kernel)

def state244_2 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0,0xfffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_2 : Impossible true (goalAt 244) 4 state244_2.toFinset :=
  node_ok cuts244 [] 0xa08030200604028200604028200a08018100241428200a08009050908028200241424200848021200444024200444024200908011100441424200908040018c04030200c0800d0c0343030200c0800d0c0b030 (by decide +kernel)

def state244_3 : List Sig := [0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0,input 6,0xfffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_3 : Impossible true (goalAt 244) 5 state244_3.toFinset :=
  node_ok cuts244 [⟨state244_0,exclude244_0⟩,⟨state244_1,exclude244_1⟩,⟨state244_2,exclude244_2⟩] 0xb03018100604030100a08028200b03028200a08030100604018101000228200a08011050604018101000218100604011050a08028200343028200a08040008604018100343018100604040008a08028200b03011100444030100908024200b03024200908030100444011100241424200908028201000628200241440008241428200908024200441424200908040018444011100441411100444040018908024200343024200848040000444021200343011100444040000908024200c04011050c0402c0c100082c0c0c04080008c0402c0c044142c0c100034000cc08030100343030100b03080004a43030102000030100b0300d0c03430 (by decide +kernel)

def state244_4 : List Sig := [0xffffffffffffffff0000000000000000f0f0f0f0f0f0f0f0,input 6,input 7,0xfffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_4 : Impossible true (goalAt 244) 4 state244_4.toFinset :=
  node_ok cuts244 [] 0x604028200a08018100a08018100604028200848028200241421200444021200848011100848011100444021200c040390c0c040190c0a08018100a08018100848011100848011100343030100841430100c080 (by decide +kernel)

def state244_5 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_5 : Impossible true (goalAt 244) 4 state244_5.toFinset :=
  node_ok cuts244 [] 0x604028200a08018100a08030200604028200241428200a08009050848028200241421200444021200848014100848030200504021200841421200848040018343030100c0400d0c0c04030200c0800d0c07030 (by decide +kernel)

def state244_6 : List Sig := [0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 7,0xfffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_6 : Impossible true (goalAt 244) 5 state244_6.toFinset :=
  node_ok cuts244 [⟨state244_0,exclude244_0⟩,⟨state244_4,exclude244_4⟩,⟨state244_5,exclude244_5⟩] 0x100071c0c0703021050c08030202000230200c0802105070301c0c200011c0c064300d0c0c08030202000030200c0800d0c070300d0c0703028200a08030200604030200703018100604030200a08028201000218100604021050a08028201000228200a08021050604018100343018100604040008a08028200343028200a0804000860401810070302120084803020050403020070301410050403020084802120024142120084802820100062820024144000824142820084802120084141410050404001884802120084142120084804001850401410034301410044404000084802120034302120084804000050401410100034000cc040 (by decide +kernel)

def state244_7 : List Sig := [0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f0000000000000000,input 6,input 7,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_7 : Impossible true (goalAt 244) 4 state244_7.toFinset :=
  node_ok cuts244 [] 0x604028200a08018100a08030200604028200241428200343028200343030100841430100343030200441430200c04030200c0801c0c0908009050a080242008480141009080242005040242005040302009080 (by decide +kernel)

def state244_8 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,input 7,0xfffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_8 : Impossible true (goalAt 244) 5 state244_8.toFinset :=
  node_ok cuts244 [⟨state244_0,exclude244_0⟩,⟨state244_2,exclude244_2⟩,⟨state244_5,exclude244_5⟩,⟨state244_7,exclude244_7⟩] 0x18100a08028200604028200c08018100a08009050a08028200241409050a0800d0c0a0802120034303010200023010034303020200013020034304000e00000d0c0908028200241424200504024200908014100908030200504024202000324200908040018b03030100c0804001c7030 (by decide +kernel)

def state244_9 : List Sig := [0xfffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0,input 2,input 5,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_9 : Impossible true (goalAt 244) 6 state244_9.toFinset :=
  node_ok cuts244 [⟨state244_3,exclude244_3⟩,⟨state244_6,exclude244_6⟩,⟨state244_8,exclude244_8⟩] 0x4001cc0401c0c0c04040020b03030200c08080008c04030200c0804001cb0301c0c0703040008b03018100604040008c04028200a08040008b03028200a08040008c04018100604040008703028200a08040008c08018100c08040008703018100604040008c08028200a0804000c84140d0c034304000cc0404000cc0404000c84148000484144000cc0400d0c0c0404000c44140d0c034304000cc0804000cc0804000c44148000044144000cc0800d0c0c0804000c24144000824144000ca0800d0c0a0804000c24140d0c034304000ca0804000ca08040001000040000848040018b03014100504040018c04024200908040018b03024200908040018c04014100504040018703024200908040018c08014100c08040018703014100504040018c08024200908040018241424200908040018a08040018a08040018241440008241440018a080242009080 (by decide +kernel)

def state244_10 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000,input 7,input 6,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_10 : Impossible true (goalAt 244) 4 state244_10.toFinset :=
  node_ok cuts244 [] 0x2120090800d0c0848021200c08011100848011100848021200444009050848021201000624200c08014100908014100908024200504009050908024201000030100c080302005030150509414 (by decide +kernel)

def state244_11 : List Sig := [0xffffffffffffffffffffffff00000000,input 7,input 6,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_11 : Impossible true (goalAt 244) 4 state244_11.toFinset :=
  node_ok cuts244 [] 0x848024200343021200848030200444021200444021200848011100908030200504024200504024200908014100503030200c080140c0444021200444021200504024200504024200503030200503030200c040 (by decide +kernel)

def state244_12 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_12 : Impossible true (goalAt 244) 4 state244_12.toFinset :=
  node_ok cuts244 [] 0x84802420034302120084803020044402120044402120084801110034302120084800d0c0908028200504024200504024200908014100503024200908040024c04030200c08009050503030200c08009050a030 (by decide +kernel)

def state244_13 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 6,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 2,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_13 : Impossible true (goalAt 244) 5 state244_13.toFinset :=
  node_ok cuts244 [⟨state244_10,exclude244_10⟩,⟨state244_11,exclude244_11⟩,⟨state244_12,exclude244_12⟩] 0x94141110044403010084802120094142120084803010044401110100022120084802420034302420100020d0c03430242008480212010002212008480140c04440111010002111004440140c0848021200241421200848040018444011100241411100444040018848021200a03014100504030100908024200a03024200908030100504014100503024200908040024504014100503014100504040024908024200241424200908040000504028200241414100504040000908024200c040140c0c040280c10008280c0c04080008c040280c05030140c1000140004c080301002414301009414800049414301020000301009414090509030 (by decide +kernel)

def state244_14 : List Sig := [0xffffffffffffffff0000000000000000ffffffff00000000,input 6,input 7,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_14 : Impossible true (goalAt 244) 4 state244_14.toFinset :=
  node_ok cuts244 [] 0x848024200343021200444021200848011100848011100444021200504024200908014100908014100504024200c040240c0c040240c0848011100848011100908014100908014100903030100903030100c080 (by decide +kernel)

def state244_15 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_15 : Impossible true (goalAt 244) 4 state244_15.toFinset :=
  node_ok cuts244 [] 0x84802420034302120044402120084801110084803020044402120034302120084800d0c0504024200908014100908030200504024200903024200908040024903030100c04009050c04030200c080090506030 (by decide +kernel)

def state244_16 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 7,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_16 : Impossible true (goalAt 244) 5 state244_16.toFinset :=
  node_ok cuts244 [⟨state244_10,exclude244_10⟩,⟨state244_14,exclude244_14⟩,⟨state244_15,exclude244_15⟩] 0x10007180c06030240c0c08030202000230200c080240c06030180c2000115050541409050c08030202000030200c080090505414140c054142120084803020044403020054141110044403020084802120100022120084802420034302420100020d0c03430242008480212010002111004440240c08480212010002212008480240c0444011100241411100444040018848021200241421200848040018444011100603024200908030200504030200603014100504030200908024200903014100504040024908024200903024200908040024504014100241414100504040000908024200241424200908040000504014101000140004c040 (by decide +kernel)

def state244_17 : List Sig := [0xffff000000000000ffff000000000000ffff0000000000000000,input 6,input 7,input 5,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_17 : Impossible true (goalAt 244) 4 state244_17.toFinset :=
  node_ok cuts244 [] 0x84800d0c0343021200444021200848011100848030200444021200a03030100903030100603030200503030200c04030200c080180c084800d0c0848024200a080141009080242005040242005040302009080 (by decide +kernel)

def state244_18 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,input 7,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 5,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_18 : Impossible true (goalAt 244) 5 state244_18.toFinset :=
  node_ok cuts244 [⟨state244_10,exclude244_10⟩,⟨state244_12,exclude244_12⟩,⟨state244_15,exclude244_15⟩,⟨state244_17,exclude244_17⟩] 0x2120034300d0c084802120090800d0c0848011100848021200444021200c0801110084800d0c0848021200343028200241430102000230100241430202000130200241440006000009050504024200908014100908030200504024202000324200908040024a03030100c0804001c6030 (by decide +kernel)

def state244_19 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 5,input 2,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_19 : Impossible true (goalAt 244) 6 state244_19.toFinset :=
  node_ok cuts244 [⟨state244_13,exclude244_13⟩,⟨state244_16,exclude244_16⟩,⟨state244_18,exclude244_18⟩] 0x4001cc040180c0c04040020a03030200c08080008c04030200c0804001ca030180c0603040008941411100444040018c04021200848040008941421200848040018c04011100444040008541421200848040018c08011100c08040008541411100444040018c0802120084804000424142120084804000500060d0c034304000424140d0c034304000500012120084804000900022120084804001890800d0c090804000900020d0c0343040018908021200848040004a03009050a03040004c04040004c04040004a03080004903040004c04009050c04040004603009050603040004c08040004c08040004603080000503040004c08009050c08040001000040000a08040024a03014100504040024c04024200908040024a03024200908040024c04014100504040024603024200908040024c08014100c08040024603014100504040024c080242009080 (by decide +kernel)

def state244_20 : List Sig := [0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000f0f00000f0f0,input 7,input 2,input 6,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_20 : Impossible true (goalAt 244) 4 state244_20.toFinset :=
  node_ok cuts244 [] 0x28200c08018100a08018100a08028200604030100c08030200703021200a0800d0c0848021200c080111008480111008480212004440242002414282009080242005040302009080212003430212009080141009080242005040 (by decide +kernel)

def state244_21 : List Sig := [0xffffffff00000000ffffffff00000000ffffffff00000000f0f0f0f0,input 7,input 2,input 6,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_21 : Impossible true (goalAt 244) 4 state244_21.toFinset :=
  node_ok cuts244 [] 0x24200c08014100908014100908024200504030100c0803020070302120090800d0c0848021200c08011100848011100848021200444024200241424200a08028200604030200a08021200343021200a08018100a080282006040 (by decide +kernel)

def state244_22 : List Sig := [0xfffffffffffffffffffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0,input 7,input 2,input 6,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_22 : Impossible true (goalAt 244) 5 state244_22.toFinset :=
  node_ok cuts244 [⟨state244_0,exclude244_0⟩,⟨state244_20,exclude244_20⟩,⟨state244_21,exclude244_21⟩] 0xa08030200604028200604028200a08018102000228200a08040004908028200241424200908030200504024200504024200908014102000124200908040000c04030200c08015050703021200a0800d050848021200908080000848021200c0801110084801110084802120044400d0c0b030 (by decide +kernel)

def state244_23 : List Sig := [0xfffffffffffffffff0f0f0f0f0f0f0f0,input 7,input 2,input 6,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_23 : Impossible true (goalAt 244) 5 state244_23.toFinset :=
  node_ok cuts244 [⟨state244_1,exclude244_1⟩] 0xa08030200604028200604028200a08018100908028200241424200908030200504024200504024200908014100f03030200c0802c0c0848028200341421200848024202000021200848030200444021200444021200848011100604028200604028200504024200504024200703030200541430200444021200444021200c040 (by decide +kernel)

def state244_24 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_24 : Impossible true (goalAt 244) 4 state244_24.toFinset :=
  node_ok cuts244 [] 0x28200848018100848018100a0802820044400d050a08028200341424200a0800905090802420084801410084801410090802420044401505090802420044141110084802120100041c0c084802120090142c0c04440111005014 (by decide +kernel)

def state244_25 : List Sig := [0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 7,0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0,input 6,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_25 : Impossible true (goalAt 244) 5 state244_25.toFinset :=
  node_ok cuts244 [⟨state244_24,exclude244_24⟩] 0x28200604018100a08028200848018100848018100a08028200604018100a08028200444024200a08009050908024200504014100908024200848014100848014100908024200504014100908024200444030200541425052000015050444015050444014050941421200848024050444021200848040010c040 (by decide +kernel)

def state244_26 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0,input 2,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_26 : Impossible true (goalAt 244) 5 state244_26.toFinset :=
  node_ok cuts244 [⟨state244_24,exclude244_24⟩,⟨state244_2,exclude244_2⟩] 0x28200c08018100a08018100a0802820060400d050a08028200341424200a08009050908024200c08014100908014100908024200504015050908024200441411100a0800d050a08011100908080004908021200444021102000011100541411100444014050c04030200c08040014703030200c0804000cb030 (by decide +kernel)

def state244_27 : List Sig := [0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0,input 2,input 6,input 4,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_27 : Impossible true (goalAt 244) 6 state244_27.toFinset :=
  node_ok cuts244 [⟨state244_3,exclude244_3⟩,⟨state244_22,exclude244_22⟩,⟨state244_23,exclude244_23⟩,⟨state244_25,exclude244_25⟩,⟨state244_26,exclude244_26⟩] 0xb03018100604030100a08028200b03028200a08030100604018101000428200a08015050604018101000218100604015050a08028201000228200a08040004604018101000218100604040004a08028200b03014100504030100908024200b03024200908030100504014100341424200908028201000628200341440008241428200908024200541424200908011010504014100541414100504011010908024201000624200908040000504014101000614100504040000908024200c04015050c0402c0c100042c0c0c04080010c0402c0c054142c0c100044000cc08025050444011100c0404000cc04025052000325050c0401110044400d050444011100a0804000ca0800d05100020d050a08011100a0804000c44401110090804000c90804000d000680000908011100908015051000415051000311100444040011000414051000440010848030101000530100b03080008b03030102000130100b03040014b030 (by decide +kernel)

def state244_28 : List Sig := [0xffffffffffffffff0000000000000000f0f0f0f0f0f0f0f0,input 6,input 2,input 7,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_28 : Impossible true (goalAt 244) 5 state244_28.toFinset :=
  node_ok cuts244 [⟨state244_4,exclude244_4⟩] 0x604028200a08018100a08018100604028200908028200241424200504024200908014100908014100504024200848028200341421200848024202000021200444021200848011100848011100444021200c0403c0c0c0401c0c0a08018100a08018100908014100908014100b03030100941430100848011100848011100c080 (by decide +kernel)

def state244_29 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 2,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_29 : Impossible true (goalAt 244) 5 state244_29.toFinset :=
  node_ok cuts244 [⟨state244_24,exclude244_24⟩,⟨state244_5,exclude244_5⟩] 0x18100a08028200604028200c08018100a0800d050a08028200341424200a08009050908014100908024200504024200c08014100908025050908024200841421200a0800d050848021200908080004848011100848030202000021200941421200848024050b03030100c04040010c04030200c080400107030 (by decide +kernel)

def state244_30 : List Sig := [0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 2,input 7,input 4,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_30 : Impossible true (goalAt 244) 6 state244_30.toFinset :=
  node_ok cuts244 [⟨state244_6,exclude244_6⟩,⟨state244_25,exclude244_25⟩,⟨state244_22,exclude244_22⟩,⟨state244_28,exclude244_28⟩,⟨state244_29,exclude244_29⟩] 0x100051c0c0703025050c08030202000430200c0802505070301c0c200031c0c0703040010c08030202000230200c0804001070301c0c0703028200a08030200604030200703018100604030200a08028201000518100604025050a08028201000228200a08025050604018101000218100604040004a08028201000228200a0804000460401810070302420090803020050403020070301410050403020090802420034142420090802820100062820034144000824142820090802420094141410050402101090802420094142420090802101050401410100061410050404000090802420100062420090804000050401410100034000cc04015050848021200c0804000cc08015052000115050c0802120084800d050848021200a0804000ca0800d05100020d050a0802120084804000c84802120090804000c90804000d00068000090802120084802505100052505100032120084804000d0003240510003400144440 (by decide +kernel)

def state244_31 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000,input 7,input 5,input 6,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_31 : Impossible true (goalAt 244) 4 state244_31.toFinset :=
  node_ok cuts244 [] 0x24200c08014100908024200a08009050908014100908024200504030100c08030200703028200c08018100a08018100a080282006040212003430242008480212004440302008480212003430282008480111008480212004440 (by decide +kernel)

def state244_32 : List Sig := [0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff00000000,input 7,input 5,input 6,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_32 : Impossible true (goalAt 244) 4 state244_32.toFinset :=
  node_ok cuts244 [] 0x21200c08011100848021200a0800d0c0848011100848021200444030100c08030200703028200c08018100a08018100a080282006040212003430212009080242005040302009080242002414282009080141009080242005040 (by decide +kernel)

def state244_33 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000,input 7,input 5,input 6,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_33 : Impossible true (goalAt 244) 5 state244_33.toFinset :=
  node_ok cuts244 [⟨state244_10,exclude244_10⟩,⟨state244_31,exclude244_31⟩,⟨state244_32,exclude244_32⟩] 0x90803020050402420090802820200002420050402420090801410200022420090804000084802420034302120084803020044402120084802820034302120044402120084801110200012120084804000cc04030200c0801c0c0541428200c08018100a08018100a0802820060400d0509414 (by decide +kernel)

def state244_34 : List Sig := [0xffffffffffffffffffffffff00000000,input 7,input 5,input 6,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_34 : Impossible true (goalAt 244) 5 state244_34.toFinset :=
  node_ok cuts244 [⟨state244_11,exclude244_11⟩] 0x908030200504024200908028202000024200504024200908014100848024200343021200848030200444021200848028200343021200444021200848011100703030200c0801c0c0a08030200604028200604028200a08018100504024200504024200444021200444021200703030200703030200604028200604028200c040 (by decide +kernel)

def state244_35 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_35 : Impossible true (goalAt 244) 4 state244_35.toFinset :=
  node_ok cuts244 [] 0x24200a0801410090801410090802420050401c0c090802420060302120090800d0c0848021200a0801110084801110084802120044400d0c0848021200343018100a0802820100041c0c0a0802820090301c0c06040181005030 (by decide +kernel)

def state244_36 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 7,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 6,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_36 : Impossible true (goalAt 244) 5 state244_36.toFinset :=
  node_ok cuts244 [⟨state244_35,exclude244_35⟩] 0x24200504014100908024200a0801410090801410090802420050401410090802420050402120090800d0c0848021200444011100848021200a0801110084801110084802120044401110084802120044403020070302c0c200001c0c060401c0c06040140c0b03028200a080240c0604028200a08040010c040 (by decide +kernel)

def state244_37 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 5,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_37 : Impossible true (goalAt 244) 5 state244_37.toFinset :=
  node_ok cuts244 [⟨state244_35,exclude244_35⟩,⟨state244_12,exclude244_12⟩] 0x24200604080004908024200c0801410090801410090802420050401c0c090802420060302120090800d0c084802120060400d0c0848021200c0801110084801110084802120044400d0c08480212003430282006040281020000181007030181006040140c0c04030200c08040014703030200c08040004b030 (by decide +kernel)

def state244_38 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 5,input 6,input 2,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_38 : Impossible true (goalAt 244) 6 state244_38.toFinset :=
  node_ok cuts244 [⟨state244_13,exclude244_13⟩,⟨state244_33,exclude244_33⟩,⟨state244_34,exclude244_34⟩,⟨state244_36,exclude244_36⟩,⟨state244_37,exclude244_37⟩] 0xb03014100504030100908024200b0302420090803010050401410070302420090801808050401410070301410050401808090802420100012420090801810100011810100094000600001810090802420100092420090804000050401410100091410050404000090802420094141110044403010084802120094142120084803010044401110100022120084802420034302420100020d0c034302420084802120100042120084801c0c044401110100021110044401c0c084802120100012120084801810034301810100020d0c034301810084802120100022120084804000c44401110100021110044404000c848021200c0401c0c0c0402c0c100042c0c0c04080010c0402c0c070301c0c1000140004c0802c0c0604018100c04040004c0402c0c200032c0c0c0401810060401c0c100041c0c10001181006040400050001140c1000140010a080301010005301009414800089414301020001301009414400149414 (by decide +kernel)

def state244_39 : List Sig := [0xffffffffffffffff0000000000000000ffffffff00000000,input 6,input 5,input 7,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_39 : Impossible true (goalAt 244) 5 state244_39.toFinset :=
  node_ok cuts244 [⟨state244_14,exclude244_14⟩] 0x504024200908014100908028202000024200908014100504024200848024200343021200444021200848011100848028200343021200848011100444021200604028200a08018100a08018100604028200c0402c0c0c0402c0c0908014100908014100848011100848011100b03030100b03030100a08018100a08018100c080 (by decide +kernel)

def state244_40 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_40 : Impossible true (goalAt 244) 5 state244_40.toFinset :=
  node_ok cuts244 [⟨state244_35,exclude244_35⟩,⟨state244_15,exclude244_15⟩] 0x24200a08080004908014100908024200504024200c0801410090802c0c0908024200a0302120090800d0c0848021200a0800d0c0848011100848021200444021200c0801110084800d0c0848021200343018100a08030202000028200b03028200a080240c0b03030100c04040004c04030200c080400107030 (by decide +kernel)

def state244_41 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,input 7,input 2,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_41 : Impossible true (goalAt 244) 6 state244_41.toFinset :=
  node_ok cuts244 [⟨state244_36,exclude244_36⟩,⟨state244_16,exclude244_16⟩,⟨state244_33,exclude244_33⟩,⟨state244_39,exclude244_39⟩,⟨state244_40,exclude244_40⟩] 0x100051c0c070302c0c0c08030202000430200c0802c0c070301c0c2000315050541440010c08030202000230200c08040010541415050703024200908030200504030200703014100504030200908024200b03014100504028080908024200b0302420090802808050401410100012420090802820100012820100094000600012820090802420100091410050404000090802420100092420090804000050401410054142120084803020044403020054141110044403020084802120100022120084802420034302420100020d0c034302420084802120100051110044402c0c084802120100022120084802c0c044401110100012120084802820034302820100020d0c034302820084802120100021110044404000c84802120100022120084804000c444011101000140004c0401c0c0a08028200c08040004c0801c0c200001c0c0c08028200a0802c0c100052c0c1000128200a080400050001240c10001400146040 (by decide +kernel)

def state244_42 : List Sig := [0xf0f0ffff00000000f0f0ffff00000000f0f0ffff00000000f0f0f0f0,input 2,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_42 : Impossible true (goalAt 244) 3 state244_42.toFinset :=
  node_ok cuts244 [] 0x30100c08030200503011100848021200444021200c080111008480141009080242005040242005040302009080212003430212009080 (by decide +kernel)

def state244_43 : List Sig := [0xf0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0f0f0f0f0f0f0,input 2,input 6,input 7,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_43 : Impossible true (goalAt 244) 4 state244_43.toFinset :=
  node_ok cuts244 [⟨state244_42,exclude244_42⟩] 0x604028200a08018100a08030200604028200c04030200c0801c0c08480282002414212004440212008480111008480302004440212003430242020000282009080141009080242005040242005040302009080 (by decide +kernel)

def state244_44 : List Sig := [0xf0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f00000000,input 5,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_44 : Impossible true (goalAt 244) 3 state244_44.toFinset :=
  node_ok cuts244 [] 0x30100c08030200603018100a08028200604028200c08018100a080111008480212004440212004440302008480212003430282008480 (by decide +kernel)

def state244_45 : List Sig := [0xffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff00000000,input 5,input 6,input 7,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_45 : Impossible true (goalAt 244) 4 state244_45.toFinset :=
  node_ok cuts244 [⟨state244_44,exclude244_44⟩] 0x444021200848011100848030200444021200848028200343021202000021200848024200c04030200c080180c0604028200a08018100a080302006040282002414141009080242005040242005040302009080 (by decide +kernel)

def state244_46 : List Sig := [0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000,input 6,input 7,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_46 : Impossible true (goalAt 244) 5 state244_46.toFinset :=
  node_ok cuts244 [⟨state244_7,exclude244_7⟩,⟨state244_17,exclude244_17⟩,⟨state244_43,exclude244_43⟩,⟨state244_45,exclude244_45⟩] 0x2c0c0604018100c04028200a0802c0c0a08028200c0401810060401c0c0a08028200c08018100c0801c0c0604018100c08028200a08009050848021200a0800d0c0a0800905034300d0c0a08021200848025050444011100c04021200848025050848021200c04011100444015050848021200c08011100c08015050444011100c08021200848030100703030100b03030200c08030100c08030200b0301c0c0703028200908024200241480004241428202000328200241424200908021200908021200343080000343021202000221200343024200908030100504014100b03024200908030100908024200b030141005040302009080242007030141005040302005040302007030242009080 (by decide +kernel)

def state244_47 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0000000000000000,input 2,input 6,input 7,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_47 : Impossible true (goalAt 244) 5 state244_47.toFinset :=
  node_ok cuts244 [⟨state244_7,exclude244_7⟩] 0x604028200a08018100a08030200604028200908028200241424200504024200908014100908030200504024200c04030200c08015050341428200343028200242024200343024200343030100941430100343030200541430200a0800d050a0800d050908080000908040000c0402c0c0c04025050c0801c0c0c080150508480 (by decide +kernel)

def state244_48 : List Sig := [0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,input 7,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_48 : Impossible true (goalAt 244) 5 state244_48.toFinset :=
  node_ok cuts244 [] 0x18100a08028200604028200c08018100a08009050a08028200241421200a0800d0c0848011100848021200444021200c0801110084800d0c084802120034302c0c0c0403020100071c0c0908009050a0802420084800d0c0848024200504024200908014100908014100c080242010000 (by decide +kernel)

def state244_49 : List Sig := [0xffffffff00000000ffffffff00000000ffffffff0000000000000000,input 5,input 6,input 7,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_49 : Impossible true (goalAt 244) 5 state244_49.toFinset :=
  node_ok cuts244 [⟨state244_17,exclude244_17⟩] 0x50402420090801410090803020050402420090800901024142420084802420034302120044402120084801110084803020044402120084800d0c0343021200c04030200c0801c0c0b03030100b0303010070303020070303020090808000090804000084800d0c084800d0c0c0402c0c0c0402c0c0c0801c0c0c0801c0c0a080 (by decide +kernel)

def state244_50 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,input 7,input 2,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_50 : Impossible true (goalAt 244) 6 state244_50.toFinset :=
  node_ok cuts244 [⟨state244_22,exclude244_22⟩,⟨state244_26,exclude244_26⟩,⟨state244_29,exclude244_29⟩,⟨state244_8,exclude244_8⟩,⟨state244_18,exclude244_18⟩,⟨state244_33,exclude244_33⟩,⟨state244_37,exclude244_37⟩,⟨state244_40,exclude244_40⟩,⟨state244_46,exclude244_46⟩,⟨state244_47,exclude244_47⟩,⟨state244_48,exclude244_48⟩,⟨state244_49,exclude244_49⟩] 0x1000518100604030100a08028202000728200a08030100604018101000428200a08030200604030202000618100604030200a08028202000b0d050341440004a08028202000528200a0804000434140d05034142420090802820100072820034148001024142820090802420100051410050403010090802420100072420090803010050401410100042420090803020050403020100071410050403020090802420100078002a00084000090802420100072420090804000100074000034142120084802820034302820034140d0c034302820084802120100072120084802420034302420200030d0c034302420084802120100051110044403010084802120200022120084803010044401110100042120084803020044403020200011110044403020084802120200090d0c034304000c84802120200002120084804000c34300d0c1000440010b03030101000530101000430200c080400110004400110004400147030 (by decide +kernel)

def state244_51 : List Sig := roots 244
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_51 : Impossible true (goalAt 244) 7 state244_51.toFinset :=
  node_ok cuts244 [⟨state244_9,exclude244_9⟩,⟨state244_19,exclude244_19⟩,⟨state244_27,exclude244_27⟩,⟨state244_30,exclude244_30⟩,⟨state244_38,exclude244_38⟩,⟨state244_41,exclude244_41⟩,⟨state244_50,exclude244_50⟩] 0x40014c0401c0c0c04040010b03030200c08080018c04030200c08040010b0301c0c0703040014b03018100604040004c04028200a08080014b03028200a08040004c04018100604040010703028200a08040004c08018100c08080010703018100604040004c08028200a08040000b03014100504040000c04024200908040000b03024200908040000c04014100504040000703024200908040000c08014100c08040000703014100504040000c08024200908040000341424200908040000a08040000a08040000341480004241440000a0802420090804001494141110044404000cc0402120084808000c94142120084804000cc0401110044404001054142120084804000cc08011100c08080008541411100444040010c0802120084804000434142120084804000ca0800d0c0a0804000834140d0c0343040004a0802120084804000100002120084804000090800d0c090804000200000d0c03430400009080212008480 (by decide +kernel)

theorem lower244 : Claim 244 8 :=
  fromSearch 572916992 (by decide +kernel) exclude244_51

theorem lower245 : Claim 245 9 :=
  fromLift 9 1 536872196 lower244 (by decide +kernel)

theorem lower246 : Claim 246 9 :=
  fromLift 9 2 572589376 lower244 (by decide +kernel)

def cuts97 : Cuts (goalAt 97) := []

def state97_0 : List Sig := roots 97
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude97_0 : Impossible true (goalAt 97) 3 state97_0.toFinset :=
  node_ok cuts97 [] 0x180802101180804101181006040180806040181004101084042101104042120084806020105004140104044140105006020084802120084044140105006040084806040084042120084806040105004140 (by decide +kernel)

theorem lower97 : Claim 97 4 :=
  fromSearch 5 (by decide +kernel) exclude97_0

theorem lower113 : Claim 113 5 :=
  fromLift 5 16 4 lower97 (by decide +kernel)

theorem lower101 : Claim 101 5 :=
  fromLift 5 1 1285 lower100 (by decide +kernel)

def cuts81 : Cuts (goalAt 81) := []

def state81_0 : List Sig := roots 81
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude81_0 : Impossible true (goalAt 81) 3 state81_0.toFinset :=
  node_ok cuts81 [] 0x140401101140404101141005040140405040141004101044041101104041110044405010105004140104044140105005010044401110044044140105005040044405040044041110044405040105004140 (by decide +kernel)

theorem lower81 : Claim 81 4 :=
  fromSearch 4 (by decide +kernel) exclude81_0

theorem lower85 : Claim 85 5 :=
  fromLift 5 4 1540 lower81 (by decide +kernel)

def rule117_0 : {c : Cut // CutGood (goalAt 117) c} :=
  ruleFor 117 lower113 none (by decide +kernel)

def rule117_1 : {c : Cut // CutGood (goalAt 117) c} :=
  ruleFor 117 lower116 none (by decide +kernel)

def rule117_2 : {c : Cut // CutGood (goalAt 117) c} :=
  ruleFor 117 lower101 none (by decide +kernel)

def rule117_3 : {c : Cut // CutGood (goalAt 117) c} :=
  ruleFor 117 lower85 none (by decide +kernel)

def cuts117 : Cuts (goalAt 117) := [rule117_0,rule117_1,rule117_2,rule117_3]

def state117_0 : List Sig := roots 117
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude117_0 : Impossible true (goalAt 117) 6 state117_0.toFinset :=
  node_ok cuts117 [] 0x4000c70300d05070304000c54141810060404000c70301810060404000c54140d05050304000870300541470304000860201410050404000870301410050404000860200541460304000834141410050404000860404000860404000834144000c24144000860401410050404000054140d0c034304000070301110044404000054141110044404000070300d0c034304000034141110044404000060400d0c060404000034140d0c034304000060401110044404000015051110044404000050400d0c050404000015050d0c034304000050401110044404000445050c4c031304000470301050041404000445051050041404000470300c4c031304000425051050041404000460400c4c060404000425050c4c031304000460401050041404000815051050041404000850400c4c050404000815050c4c03130400085040105004140400010000105004140400004440054504440400010001054501514400004440105004140 (by decide +kernel)

theorem lower117 : Claim 117 7 :=
  fromSearch 1284 (by decide +kernel) exclude117_0

def cuts114 : Cuts (goalAt 114) := []

def state114_0 : List Sig := roots 114
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude114_0 : Impossible true (goalAt 114) 3 state114_0.toFinset :=
  node_ok cuts114 [] 0x1c0c062421890850301c0c052421490860301490862420c88852420c8c07030180883230189086040181086042149085040141085042 (by decide +kernel)

theorem lower114 : Claim 114 4 :=
  fromSearch 73465920 (by decide +kernel) exclude114_0

def cuts86 : Cuts (goalAt 86) := []

def state86_0 : List Sig := roots 86
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude86_0 : Impossible true (goalAt 86) 3 state86_0.toFinset :=
  node_ok cuts86 [] 0x150505242149084414150504642119085014119085242048184642058505414110181614149085040141085042119084440111084442 (by decide +kernel)

theorem lower86 : Claim 86 4 :=
  fromSearch 33621568 (by decide +kernel) exclude86_0

def rule118_0 : {c : Cut // CutGood (goalAt 118) c} :=
  ruleFor 118 lower116 none (by decide +kernel)

def rule118_1 : {c : Cut // CutGood (goalAt 118) c} :=
  ruleFor 118 lower100 none (by decide +kernel)

def rule118_2 : {c : Cut // CutGood (goalAt 118) c} :=
  ruleFor 118 lower114 none (by decide +kernel)

def rule118_3 : {c : Cut // CutGood (goalAt 118) c} :=
  ruleFor 118 lower86 none (by decide +kernel)

def cuts118 : Cuts (goalAt 118) := [rule118_0,rule118_1,rule118_2,rule118_3]

def state118_0 : List Sig := [0xffff0000ffff0000cccc0000cccc0000ffff0000ffff0000cccc0000cccc,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,input 6,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude118_0 : Impossible true (goalAt 118) 4 state118_0.toFinset :=
  node_ok cuts118 [] 0x1808860421810824140c8c060421810816141110860420d0c044420d0c044421110834300d0c044421110832301c0c050420c88860421410844420d0c044421410832221410850420c8890001 (by decide +kernel)

def state118_1 : List Sig := [0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,input 6,input 2,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude118_1 : Impossible true (goalAt 118) 5 state118_1.toFinset :=
  node_ok cuts118 [⟨state118_0,exclude118_0⟩] 0x60220d05060221101860421810860221810860421101834140d05032300d05032300585060421810832301810860420585034140585034141410850421810832221810834140c88832221810850421410900010c88832221808850421410900011410850421808832220c88832308000032304000450421410832301410850424000500014000434141110844421810834301810834140d0c034301810844421110816061110844421410834301410816060d0c034301410844421110844060d0c034301808844421110844061110844421808834300d0c016140d0c034300c8c044421110816141110844420c8c034300c8c10000400007030 (by decide +kernel)

def state118_2 : List Sig := [0xfffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0,input 2,input 5,input 1,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude118_2 : Impossible true (goalAt 118) 5 state118_2.toFinset :=
  node_ok cuts118 [] 0x7030149085242180c052420c88832221490852420c88832221490832301c0c060220c8c052421410050421410816140c8c032300585032300d0c024220c8c012100c8c032300484070301505070300d05062420d0c070301505034300988852420d0c052420d05034304000846421c0c050101c0c05010 (by decide +kernel)

def state118_3 : List Sig := [0xffffffff00000000f0f0f0f000000000ffffffff00000000f0f0f0f0,input 2,input 6,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude118_3 : Impossible true (goalAt 118) 4 state118_3.toFinset :=
  node_ok cuts118 [] 0x1c0c052421490860301490850401410850420c8c070301808832301190844401110844421190852420d0c046420d0c04642119083430149083222149086242181086042189086040140c06242189087030119083430119086242 (by decide +kernel)

def state118_4 : List Sig := [0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0,input 2,input 6,input 1,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude118_4 : Impossible true (goalAt 118) 5 state118_4.toFinset :=
  node_ok cuts118 [⟨state118_3,exclude118_3⟩] 0x34141890862420d05200001890862424000c52421890832221490832221490852420c88832221490852420c88862421810060421810852421410050421410832301505044060c8c046421110044421110832300585016140c8c070301190862420d0504642119085242058184642150504642140503430 (by decide +kernel)

def state118_5 : List Sig := [0xcfcfcfcfcfcfcfcfcccccccccccccccccfcfcfcfcfcfcfcfcccccccccccccccc,input 2,input 6,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude118_5 : Impossible true (goalAt 118) 4 state118_5.toFinset :=
  node_ok cuts118 [] 0x1808860421810834141410860420c88850420c88850421410832221190860420d0c046421190850420d0c046420d0c046421190834301810832301810816141410832301410900010c8c07030180883230119083430111084442 (by decide +kernel)

def state118_6 : List Sig := [0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0000000000000000,input 2,input 6,input 1,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude118_6 : Impossible true (goalAt 118) 5 state118_6.toFinset :=
  node_ok cuts118 [⟨state118_5,exclude118_5⟩] 0x34141890862420d05052421890832221490832221490852420c88862421810060421810852421410050421410832301505044060c8c032300d0c024220c8c034141890834301890826221490834301490874301505034301890834141890834141490832221490832224000032308000032301c0c04642 (by decide +kernel)

def state118_7 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f0f0f0f0f0f0f0f0f00000000,input 5,input 6,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude118_7 : Impossible true (goalAt 118) 4 state118_7.toFinset :=
  node_ok cuts118 [] 0x1c0c052421490860301490862420c88852421490850401410850420c8c070301808832301890860401810860421c0c062421890850301190834301490846421110844421190844400d0c04642119083430119083430189084642 (by decide +kernel)

def state118_8 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 5,input 6,input 1,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude118_8 : Impossible true (goalAt 118) 5 state118_8.toFinset :=
  node_ok cuts118 [⟨state118_7,exclude118_7⟩] 0x7030149085242180c052421890832221490816061490852420581846421490834301190834301190846420d0c046421890834301190a00001190846424000852421410050421410846421110044421110832301c0c060220c8c062421810060421810816140c8c032300585054141c0c06242140c03414 (by decide +kernel)

def state118_9 : List Sig := [0xccccccccffffffffccccccccccccccccccccccccffffffffcccccccccccccccc,input 5,input 6,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude118_9 : Impossible true (goalAt 118) 4 state118_9.toFinset :=
  node_ok cuts118 [] 0x1c0c050421410860301410862420c88850421110850420d0c044420d0c044421110834301110862420d0c044421c0c062421890834141410832301410900011110834301110832300c8c07030180883230189083230181086042 (by decide +kernel)

def state118_10 : List Sig := [0xffffffff000000000000000000000000ffffffff0000000000000000,input 5,input 6,input 1,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude118_10 : Impossible true (goalAt 118) 5 state118_10.toFinset :=
  node_ok cuts118 [⟨state118_9,exclude118_9⟩] 0x7030149085242180c052420c88832221490846421490834301190834301190846420d0c046420d0c034301190852421410050421410846421110044421110832301c0c060220c8c016140c8c032300585074141c0c03414149083222149083222119083430119083430400003230800003230150506242 (by decide +kernel)

def state118_11 : List Sig := roots 118
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude118_11 : Impossible true (goalAt 118) 6 state118_11.toFinset :=
  node_ok cuts118 [⟨state118_1,exclude118_1⟩,⟨state118_2,exclude118_2⟩,⟨state118_4,exclude118_4⟩,⟨state118_6,exclude118_6⟩,⟨state118_8,exclude118_8⟩,⟨state118_10,exclude118_10⟩] 0x8001470300d05070304000c54141890862428001070301890862424000c54140d05050304000470300c88870304000462221490852424000470301490852424000462220c88860304000434141490852424000462420c88862424000434140c88832224000462421490852428000c54140d0c034304000870301190846428000854141190846424000870300d0c034304000c34141190846424000862420d0c062428000434140d0c034304000862421190846424000416061190846424000852420d0c052424000416060d0c034304000852421190846424000062220c8c032304000070304000070304000062228000060224000070300c8c032304000062420585062424000060400c8c060404000062420c8c060424000060400585060424000052424000452424000050400c8c050404000052420c8c050424000050404000050424000046420c8c046424000044400585044404000046420585044424000044400c8c04442 (by decide +kernel)

theorem lower118 : Claim 118 7 :=
  fromSearch 35718464 (by decide +kernel) exclude118_11

theorem lower83 : Claim 83 5 :=
  fromLift 5 2 68 lower81 (by decide +kernel)

def cuts51 : Cuts (goalAt 51) := []

def state51_0 : List Sig := roots 51
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude51_0 : Impossible true (goalAt 51) 3 state51_0.toFinset :=
  node_ok cuts51 [] 0x4c0c32220c88812220484032300c8c012300c88832300c8c011030444031300c4c0113008c8831300c4c023220c4c0323008c883130 (by decide +kernel)

theorem lower51 : Claim 51 4 :=
  fromSearch 68 (by decide +kernel) exclude51_0

def rule115_0 : {c : Cut // CutGood (goalAt 115) c} :=
  ruleFor 115 lower113 none (by decide +kernel)

def rule115_1 : {c : Cut // CutGood (goalAt 115) c} :=
  ruleFor 115 lower114 none (by decide +kernel)

def rule115_2 : {c : Cut // CutGood (goalAt 115) c} :=
  ruleFor 115 lower97 none (by decide +kernel)

def rule115_3 : {c : Cut // CutGood (goalAt 115) c} :=
  ruleFor 115 lower83 none (by decide +kernel)

def rule115_4 : {c : Cut // CutGood (goalAt 115) c} :=
  ruleFor 115 lower51 none (by decide +kernel)

def cuts115 : Cuts (goalAt 115) := [rule115_0,rule115_1,rule115_2,rule115_3,rule115_4]

def state115_0 : List Sig := [0xffffffffffffffffeeeeeeeeeeeeeeeeffffffffffffffffeeeeeeeeeeeeeeee,input 6,input 0,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude115_0 : Impossible true (goalAt 115) 4 state115_0.toFinset :=
  node_ok cuts115 [] 0x1808860421810821030c8c060421810812301410860420c88850420c88850421410832220c8c0504214109000210d08604208c88434210d0850420440c434208c88434210d0823220c4c07030 (by decide +kernel)

def state115_1 : List Sig := [0xeeeeeeeeeeeeeeee0000000000000000eeeeeeeeeeeeeeee,input 6,input 0,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude115_1 : Impossible true (goalAt 115) 4 state115_1.toFinset :=
  node_ok cuts115 [] 0x7030181086042140c05042181083222141087030141085042180c0434218108232210d08434214108110310d08713010d0843421c0c0121018108323018108322214108323014108313010d08232210d086022 (by decide +kernel)

def state115_2 : List Sig := [0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 0,input 4,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude115_2 : Impossible true (goalAt 115) 5 state115_2.toFinset :=
  node_ok cuts115 [⟨state115_0,exclude115_0⟩,⟨state115_1,exclude115_1⟩] 0x70300840c7030140406242189087030189086242140402103140c070300c8887030188885242149087030149085242188883222180c100021490852421890832221890900020c888322218908524214908410308c8823221c0c0434210d08410310d0843421c0c023221c0c0210310d08434218908232218508210308c88232218908434210d08110310d08434214909000114508110340008110314908434210d0900004000041401888832300c8c070308000470301888a00001808870300c8c032301890812101890860400c8c060401890832301810860400484060421490900021490850400c8c05040149083230141085040400085042 (by decide +kernel)

def state115_3 : List Sig := [0x5555555555555555444444444444444455555555555555554444444444444444,input 0,input 6,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude115_3 : Impossible true (goalAt 115) 4 state115_3.toFinset :=
  node_ok cuts115 [] 0x60221810860420840c50421810832221410832221410850420c88811101810831301810821201410831301410831301c4c041030c4c060420c8c06042048c050420c8c050420440c32301c0c060220c8c04342 (by decide +kernel)

def state115_4 : List Sig := [0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,input 6,input 0,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude115_4 : Impossible true (goalAt 115) 5 state115_4.toFinset :=
  node_ok cuts115 [⟨state115_0,exclude115_0⟩,⟨state115_3,exclude115_3⟩] 0x602208c0c60221040c60421810860221810860421040c230308c0c3230084043230048406042181083230181086042048402101048c100021410850421810832221810900020c88832221810850421410900020c88832221808850421410900021410850421808832220c88832300440432304000850421410832301410850424000811010440c230310d0843421810831301810823030c4c0313018108434210d08130310d0843421410831301410813030c4c0313014108434210d0841030c4c0313018088434210d08410310d0843421808831300c4c200010c4c031300c8c0434210d0a000010d0843420c8c031300c4c10000400007030 (by decide +kernel)

def state115_5 : List Sig := [0xffffffff00000000aaaaaaaa00000000ffffffff00000000aaaaaaaa,input 0,input 6,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude115_5 : Impossible true (goalAt 115) 4 state115_5.toFinset :=
  node_ok cuts115 [] 0x1c0c052421490860301490850401410850420c8c0703018088323010d0852420c4c0434210500434210d0841420c4c0434210d083130149083222149086242181086042189086040140c0624218908703010d08313010d086242 (by decide +kernel)

def state115_6 : List Sig := [0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa,input 0,input 6,input 1,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude115_6 : Impossible true (goalAt 115) 5 state115_6.toFinset :=
  node_ok cuts115 [⟨state115_0,exclude115_0⟩,⟨state115_5,exclude115_5⟩] 0x230318908624208c0e00011890862424000c52421890832221490832221490852420c88832221490852420c88862421810060421810852421410050421410832301040441030c8c032304000200000c8c0703010d08624208c0c434210d08524204c0c434210500434210d08414210c0c4342400043130 (by decide +kernel)

def state115_7 : List Sig := roots 115
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude115_7 : Impossible true (goalAt 115) 6 state115_7.toFinset :=
  node_ok cuts115 [⟨state115_2,exclude115_2⟩,⟨state115_4,exclude115_4⟩,⟨state115_6,exclude115_6⟩] 0x4000c703008c0c70304000c50101890862424000c70301890862424000c501008c0c50304000870300c88870304000862221490852424000870301490852424000862220c88860304000d00031490852424000c62420c88862424000d00020c88832224000c62421490852424000062220c8c032304000070304000070304000062228000460224000070300c8c032304000062420484062424000060400c8c060404000062420c8c060424000060400484060424000052424000852424000050400c8c050404000052420c8c050424000050404000050424001043030c4c0313040004703010d08434280008430310d0843424000470300c4c031304000c230310d0843424000c62420c4c062424000c23030c4c031304000c624210d08434240008130310d0843424000452420c4c052424000813030c4c0313040004524210d08434240001000010500414040000323010d08434240002000010d084342400003230105004142 (by decide +kernel)

theorem lower115 : Claim 115 7 :=
  fromSearch 68 (by decide +kernel) exclude115_7

theorem lower87 : Claim 87 6 :=
  fromLift 6 2 1604 lower85 (by decide +kernel)

def cuts53 : Cuts (goalAt 53) := []

def state53_0 : List Sig := roots 53
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude53_0 : Impossible true (goalAt 53) 3 state53_0.toFinset :=
  node_ok cuts53 [] 0xd05025050905024140d05034300d0c021050908034300d0c024300545031300c4c015140848031300c4c021300c4c03430054503130 (by decide +kernel)

theorem lower53 : Claim 53 4 :=
  fromSearch 1284 (by decide +kernel) exclude53_0

theorem lower55 : Claim 55 5 :=
  fromLift 5 2 1348 lower53 (by decide +kernel)

def rule119_0 : {c : Cut // CutGood (goalAt 119) c} :=
  ruleFor 119 lower117 none (by decide +kernel)

def rule119_1 : {c : Cut // CutGood (goalAt 119) c} :=
  ruleFor 119 lower118 none (by decide +kernel)

def rule119_2 : {c : Cut // CutGood (goalAt 119) c} :=
  ruleFor 119 lower115 none (by decide +kernel)

def rule119_3 : {c : Cut // CutGood (goalAt 119) c} :=
  ruleFor 119 lower87 none (by decide +kernel)

def rule119_4 : {c : Cut // CutGood (goalAt 119) c} :=
  ruleFor 119 lower101 none (by decide +kernel)

def rule119_5 : {c : Cut // CutGood (goalAt 119) c} :=
  ruleFor 119 lower116 none (by decide +kernel)

def rule119_6 : {c : Cut // CutGood (goalAt 119) c} :=
  ruleFor 119 lower100 none (by decide +kernel)

def rule119_7 : {c : Cut // CutGood (goalAt 119) c} :=
  ruleFor 119 lower85 none (by decide +kernel)

def rule119_8 : {c : Cut // CutGood (goalAt 119) c} :=
  ruleFor 119 lower113 none (by decide +kernel)

def rule119_9 : {c : Cut // CutGood (goalAt 119) c} :=
  ruleFor 119 lower97 none (by decide +kernel)

def rule119_10 : {c : Cut // CutGood (goalAt 119) c} :=
  ruleFor 119 lower118 (some (1,input 1,input 6)) (by decide +kernel)

def rule119_11 : {c : Cut // CutGood (goalAt 119) c} :=
  ruleFor 119 lower53 none (by decide +kernel)

def rule119_12 : {c : Cut // CutGood (goalAt 119) c} :=
  ruleFor 119 lower55 none (by decide +kernel)

def rule119_13 : {c : Cut // CutGood (goalAt 119) c} :=
  ruleFor 119 lower115 (some (1,input 1,input 6)) (by decide +kernel)

def rule119_14 : {c : Cut // CutGood (goalAt 119) c} :=
  ruleFor 119 lower51 none (by decide +kernel)

def rule119_15 : {c : Cut // CutGood (goalAt 119) c} :=
  ruleFor 119 lower81 none (by decide +kernel)

def rule119_16 : {c : Cut // CutGood (goalAt 119) c} :=
  ruleFor 119 lower83 none (by decide +kernel)

def rule119_17 : {c : Cut // CutGood (goalAt 119) c} :=
  ruleFor 119 lower118 (some (1,input 5,input 6)) (by decide +kernel)

def rule119_18 : {c : Cut // CutGood (goalAt 119) c} :=
  ruleFor 119 lower118 (some (3,input 5,input 6)) (by decide +kernel)

def cuts119 : Cuts (goalAt 119) := [rule119_0,rule119_1,rule119_2,rule119_3,rule119_4,rule119_5,rule119_6,rule119_7,rule119_8,rule119_9,rule119_10,rule119_11,rule119_12,rule119_13,rule119_14,rule119_15,rule119_16,rule119_17,rule119_18]

def state119_0 : List Sig := [0xffffffffffffffff3333000033330000ffffffffffffffff3333000033330000,input 6,input 4,input 0,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_0 : Impossible true (goalAt 119) 6 state119_0.toFinset :=
  node_ok cuts119 [] 0x70300d0507030150506042181087030181086042150503414140c032300941c32300585060421810832301810860420585025070585034141110844421810834301810834140d0c034301810844421110817071110844421410834301410817070d0c034301410844421110854140d0c034301c0c044421110854141110844421c0c034300d0c016140908824220c8c044421110816141110844420c8c024220c8c0250710d0843421810831301810825070c4c0313018108434210d09000610d08434211108151411109000605450151411108434210d08170710d0843421410831301410817070c4c0313014108434210d0900060c4c031301c0c0434210d09000610d0843421c0c031300c4c1000608c8823220c8c0434210d09000610d0843420c8c023220c8c034141410850421810832221810834140c88832221810850421410870300c8887030400105042141087030141085042400103222180c032300c88832304000050421410832301410850424000032220c8890004400106022 (by decide +kernel)

def state119_1 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f0f0f0f0f0f0f0f0f00000000,input 5,input 6,0x3333000033330000333300003333000033330000333300003333000033330000,input 4,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_1 : Impossible true (goalAt 119) 5 state119_1.toFinset :=
  node_ok cuts119 [] 0x434214908313010d08313010d0843420c4c0434218108313010d0870301490852420c888524218108322214908313010d08313010d0850420c8c060221c0c032300585060420c8c060421c0c0604218108503010d08151410d0844421110834301490844421110834300c8c044420d0c04442111083430111083430181084442 (by decide +kernel)

def state119_2 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 5,input 6,0x3333000033330000333300003333000033330000333300003333000033330000,input 4,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_2 : Impossible true (goalAt 119) 6 state119_2.toFinset :=
  node_ok cuts119 [⟨state119_1,exclude119_1⟩] 0x1110852420d0c044420d0c044421110834301110860420d0c0444280000444211109000810d08444205450434210d0852420c4c043420c4c0434210d08313010d0860420c4c0434205450434210d0815141c0c052421490832221490860420c888524205c1c52421490817070c8c044420d0c044420c4c043420c4c043421410832301808870300c8c016141810832301810816140c8c032300585054141c0c06042140c03414 (by decide +kernel)

def state119_3 : List Sig := [0x33330000ffffffff333300003333000033330000ffffffff3333000033330000,input 5,input 6,input 4,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_3 : Impossible true (goalAt 119) 5 state119_3.toFinset :=
  node_ok cuts119 [] 0x1110850420d0c044420d0c044421110834301110834300d0c0444210d08444205450434210d0850420c4c043420c4c0434210d08313010d0831300c4c043421c0c050421410832221410870420c88850421c0c05414140c0503011108242211108323010d08232210d0832301410832301410832220c8c060221c0c03230058503230181086042 (by decide +kernel)

def state119_4 : List Sig := [0xffffffff000000000000000000000000ffffffff0000000000000000,input 5,input 6,0x3333000033330000333300003333000033330000333300003333000033330000,input 4,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_4 : Impossible true (goalAt 119) 6 state119_4.toFinset :=
  node_ok cuts119 [⟨state119_3,exclude119_3⟩] 0x1110852420d0c044420d0c044421110834301110834300d0c0444210d08444205450434210d0852420c4c043420c4c0434210d08313010d0831300c4c043421c0c052421490832221490832220c88852420c8c044420d0c044420c4c043420c4c043421410832301808870300c8c016140c8c032300585074141c0c0341411108343011108343010d08313010d083130149083222149083222400103230800003230150506042 (by decide +kernel)

def state119_5 : List Sig := [0x3333000033330000333300003333000033330000333300003333000033330000,input 4,input 0,input 2,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_5 : Impossible true (goalAt 119) 7 state119_5.toFinset :=
  node_ok cuts119 [⟨state119_0,exclude119_0⟩,⟨state119_2,exclude119_2⟩,⟨state119_4,exclude119_4⟩] 0x8000870300d05070304001c54141810860428000470301810860424001c54140d05050304002454140d0c034304002070301110844424002454141110844424002070300d0c034304001c34141110844424002060420d0c060424002434140d0c034304001c60421110844424001017071110844424001052420d0c052424001017070d0c034304001052421110844424001845070c4c0313040014703010d08434240018450710d0843424001470300c4c031304001c250710d0843424001460420c4c060424001825070c4c031304001c604210d08434240021000610d08434240014444205450444240019000605450151440014444210d08434240010170710d0843424001452420c4c052424001017070c4c0313040014524210d0843424001070300c88870304001060221490852424001070301490852424001060220c88832224001c34141490852424001060420c88860424001034140c88832224001c60421490852424001070300c8c032304001060224001060224001070308000070304001060220c8c032304001c34140585016144001060420c8c060424001034140c8c032304001c60420585060424001034300c8c032304001044420585044424001034300585034304001044420c8c044424001431300c8c031304001043424001043424001031304001831304001443420c8c04342400010000400005042 (by decide +kernel)

def state119_6 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 5,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_6 : Impossible true (goalAt 119) 5 state119_6.toFinset :=
  node_ok cuts119 [] 0x34301110844420c8c02622111084442090c044420d0c0343011108444214108343011108434211108151410d08313010d0843420c4c0232210d08434208c8843420c4c0313010d08434214108313010d0832220c8c032304001c3230058503230140c032220d05032221408860420c8c050421410844140c8885042141084507 (by decide +kernel)

def state119_7 : List Sig := [0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 4,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,input 0,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_7 : Impossible true (goalAt 119) 6 state119_7.toFinset :=
  node_ok cuts119 [⟨state119_6,exclude119_6⟩] 0x32300d0503230058506042181083230181086042058503414140c0602209c1c60221141c60421810860221810860421141c270709c1c34141110844421810834301810834140d0c034301810844421110816140d0c034300c8c044421110816141110844420c8c034300c8c100041110844421410834301410900090d0c0343014108444211108450709888262218088444211108450711108444218088262209888270710d0843421810831301810827070c4c0313018108434210d09000610d08434211108151411109000605450151411108434210d0900060c4c031300c8c0434210d09000610d0843420c8c031300c4c1000410d0843421410831301410900060c4c0313014108434210d08450708c88232218088434210d08450710d08434218088232208c8860224001060224000032300c8c060220c8c032304000100044000034141410850421810900041810834148000034141810850421410832304002c3230400105042141083230141085042400110004180c1000c400303222 (by decide +kernel)

def state119_8 : List Sig := [0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000,input 4,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,input 0,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_8 : Impossible true (goalAt 119) 6 state119_8.toFinset :=
  node_ok cuts119 [] 0xc8c034140c8c016141810860420c8c060421810816140d05050300d05044421110860420d0c060420d05034300d0c060421110844420585034300d0c032301110844420585044421110832300d0c0323005c1c44421110832220d0c0343005c1c34300d0c0322211108444209c1c434210d0860420c4c0604209c1c31300c4c0604210d08434240018434210d08444205450444240018151405450444210d0843424001831300c4c0323010d08434240018434210d0832300c4c0313005c1c434210d0832220c4c0313005c1c31300c4c0322210d0843420d05017070d05060420c88860420d05032220c888604205c1c60420c8c015050c8c100040c88832220c8c032220c8c100040541415071810845071810834141808860221810860221810834141141c34141110860221110834301141c343011108450711108343018088343010d08602210d0831301141c313010d08450710d08313018088313040031000418081000c400105042 (by decide +kernel)

def state119_9 : List Sig := [0xffffffffffffffffffffccccffffccccffffffffffffffffffffccccffffcccc,input 4,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,input 6,input 0,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_9 : Impossible true (goalAt 119) 6 state119_9.toFinset :=
  node_ok cuts119 [] 0x60221810860420d05032301810860420585025051810860420941444421810834301110834301110844420d0c034301110844420c8c0444214108343011108242011108444209080434218108313010d08434211108151410d08313010d0843420c4c0313010d0843420c4c0434214108313010d08212010d0843420848070304001100041410860420c88850420c88850421410832220c8c050420541c1505 (by decide +kernel)

def state119_10 : List Sig := [0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 4,input 6,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,input 0,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_10 : Impossible true (goalAt 119) 6 state119_10.toFinset :=
  node_ok cuts119 [] 0xc8c060421810816140d050604218108341409c1c60421810827071110860420d0c044420d0c044421110832300d0c044421110834301110850420d0c0444209888444211108262210d0860420c4c0434210d0844420545043420c4c0434210d0831300c4c0434210d08313010d0850420c4c0434208c88434210d0823224001032300c8c100001c0c060221410860420d05050420c8c05042141090004400305042049003222 (by decide +kernel)

def state119_11 : List Sig := [0x333333333333000000000000000000003333333333330000,input 4,input 5,input 6,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_11 : Impossible true (goalAt 119) 5 state119_11.toFinset :=
  node_ok cuts119 [] 0x34301110844420d0c0444218108343011108444214108343011108434211108151410d08313010d0843420c4c0434218108313010d08434214108313010d0860221810860420d05032221410850420c888504218108322214108323011108343011108313010d08313010d0870300585060420c8c060420541c50420c8c05042 (by decide +kernel)

def state119_12 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,input 5,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,input 6,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_12 : Impossible true (goalAt 119) 6 state119_12.toFinset :=
  node_ok cuts119 [⟨state119_6,exclude119_6⟩,⟨state119_11,exclude119_11⟩] 0xd0c044421110834300d0c044421110832301110834300d0c044421110834300d0c044421110834300d0c0444210d0844420545043420c4c0434210d0831300c4c0434210d08313010d0831300c4c0434210d0831300c4c0434210d0831300c4c043421c0c060221141c60220d05032300585032300585060420c88860228000032220c8c032220c8c100040d05032220905050421808845071808845070c8c200010c8c1000b (by decide +kernel)

def state119_13 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0c0c0c0c0f0f0f0f0f0f0f0f0f0f0f0f0c0c0c0c,input 5,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,input 6,input 0,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_13 : Impossible true (goalAt 119) 5 state119_13.toFinset :=
  node_ok cuts119 [] 0x32221410850420c88832301410850420441c504218108322214108434214108313010d08313010d0843420c4c0313010d0843420c4c0434218108313010d0870301808860421810834140c8c0604218108161411108343014108444210d08151410d0844420d0c044421110834300c8c04442111083430111083430181084442 (by decide +kernel)

def state119_14 : List Sig := [0xffffffffffffffffffffffffccccccccffffffffffffffffffffffffcccccccc,input 5,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,input 6,input 0,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_14 : Impossible true (goalAt 119) 6 state119_14.toFinset :=
  node_ok cuts119 [⟨state119_13,exclude119_13⟩] 0x32221410850420c88832301410850420541450421810832221410815051410850420541444421410834301110834301110844420d0c034301110844420c8c044421810834301110a000011108444240020434214108313010d08434211108151410d08313010d0843420c4c0313010d0843420c4c0434218108313010d08151410d0843420545070304001c16141808860421810827070c8c06042048c03414 (by decide +kernel)

def state119_15 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f0f0f0f0f0f0f0f0f00000000,input 5,input 6,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,input 0,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_15 : Impossible true (goalAt 119) 5 state119_15.toFinset :=
  node_ok cuts119 [] 0x32301410850420441c32221410850420c888504218108322214108434214108313010d08313010d0843420c4c0313010d0843420c4c0434218108313010d0870300c8c0604218108161418088604218108341411108343014108444210d08151410d0844420c8c044421110834300d0c04442111083430111083430181084442 (by decide +kernel)

def state119_16 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 5,input 6,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,input 0,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_16 : Impossible true (goalAt 119) 6 state119_16.toFinset :=
  node_ok cuts119 [⟨state119_15,exclude119_15⟩] 0xc8c050421410815070c88850421410832221410860420c888504205c1c50421410817071110850420d0c044420d0c044421110832300d0c044421110834301110860420d0c0444280000444211109000810d0850420c4c0434210d0844420545043420c4c0434210d0831300c4c0434210d08313010d0860420c4c0434205450434210d0815140585032300c8c016141c0c045070c8c060421810816141808860424001c3414 (by decide +kernel)

def state119_17 : List Sig := [0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,input 6,input 0,input 2,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_17 : Impossible true (goalAt 119) 7 state119_17.toFinset :=
  node_ok cuts119 [⟨state119_7,exclude119_7⟩,⟨state119_8,exclude119_8⟩,⟨state119_9,exclude119_9⟩,⟨state119_10,exclude119_10⟩,⟨state119_12,exclude119_12⟩,⟨state119_14,exclude119_14⟩,⟨state119_16,exclude119_16⟩] 0x4003060220d05060224001c45071810860428001860221810860424001c45070d05034144002c32300d05032304001c16141810860428001432301810860424001c16140d05016144001c34141410850424001060420c88860428001034140c88832224001c60421410850424003200010c88832224001060221410850428000e00001410850424003060220c88832224002c32300541432304001100041410850428000832301410850424001100040541415074001c34141110844424002060420d0c060424003c34140d0c034304001c60421110844424001017071110844424002050420d0c050424002417070d0c034304001050421110844424003045070d0c034304002060221110844424003845071110844424003060220d0c034304002c16140d0c034304002032301110844424003416141110844424002032300d0c032304001c270710d0843424001460420c4c060424002827070c4c031304001c604210d08434240010170710d0843424001450420c4c050424001817070c4c0313040014504210d08434240021000a10d08434240014444205450444240029000a05450151440014444210d0843424003045070c4c0313040014602210d08434240028450710d0843424003060220c4c031304002d000a0c4c0313040014323010d08434240029000a10d0843424001432300c4c03130400010000400007030 (by decide +kernel)

def state119_18 : List Sig := [0xffffffffffffffff3333333333330000ffffffffffffffff3333333333330000,input 6,input 4,input 5,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_18 : Impossible true (goalAt 119) 5 state119_18.toFinset :=
  node_ok cuts119 [] 0x44421810834301110844421410834301110834301110844420d0c024221110844420c8c0434211108151410d08434218108313010d08434214108313010d08313010d0843420c4c0232210d0843420c8c07030181086042140c03230181086042058505042181083222141087030141085042180c032301410850420c8886022 (by decide +kernel)

def state119_19 : List Sig := [0x3333333333330000333333333333000033333333333300003333333333330000,input 4,input 5,input 0,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_19 : Impossible true (goalAt 119) 6 state119_19.toFinset :=
  node_ok cuts119 [⟨state119_11,exclude119_11⟩,⟨state119_18,exclude119_18⟩] 0x1505034300d0c070301110844421505044421110870300d0c034300d05044421110862420d0c062420d05034300d0c0624211108444205c1c44421110852420d0c0524205c1c34300d0c052421110844421141c31300c4c0703010d0843421141c434210d0870300c4c0313040018434210d08444205450444240018151405450444210d08434209c1c434210d0862420c4c0624209c1c31300c4c0624210d08434205c1c434210d0852420c4c0524205c1c31300c4c0524210d0843421c0c034141c0c054141890862421c0c062421890854140d05050301c0c032221c0c062221490852421c0c052421490862220c88860300d05052421490862420c88862420d05032220c88862421490852421c0c032300c8c062228000060221c0c200011c0c062220c8c032300d0c032300c8c044420585044420d0c016140d0c044420c8c044420c4c032300c4c043424001843420c4c100060c4c043420c8c043420d05016141810862420c8c060420d05032300c8c062420585062424001d00001410852420c8c050424001c32300c8c05242400005242 (by decide +kernel)

def state119_20 : List Sig := [0x5555555555555555555555555555000055555555555555555555555555550000,input 6,input 4,input 5,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_20 : Impossible true (goalAt 119) 5 state119_20.toFinset :=
  node_ok cuts119 [] 0x1190862420d0c046421190852420d0c046420d0c046421190834301190844401110844421890860401810860421490850401410850420c8c070301808832301c0c062421890850301490862420c88852421c0c0524214908603010d08151411908434210508434210d08414010d08313018908434210d0831301490843420c4c0434210d083130 (by decide +kernel)

def state119_21 : List Sig := [0x3333333333333333333333333333000033333333333333333333333333330000,input 6,input 4,input 5,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_21 : Impossible true (goalAt 119) 5 state119_21.toFinset :=
  node_ok cuts119 [] 0x1190862420d0c046421190852420d0c046420d0c0464211908343010d08464205450434210d0862420c4c0434210d0852420c4c043420c4c0434210d0831301c0c062421890850301490862420c88852421c0c052421490860301110844421110046421050843421050043421810860421810062421410850421410052420c8c060221c0c03230 (by decide +kernel)

def state119_22 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0f0f0f0f0f0f0f0f0f0f0f0f0000,input 6,input 4,input 5,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_22 : Impossible true (goalAt 119) 5 state119_22.toFinset :=
  node_ok cuts119 [] 0x1890860401810860421490850401410850420c8c0703018088323010500434210d08414210d0862420c4c0434210d0852420c4c043420c4c0434210d0831301c0c062421890850301490862420c88852421c0c0524214908603011108444211908444010d08151410d0846421190834301890846421190834301490846420d0c04642119083430 (by decide +kernel)

def state119_23 : List Sig := [0xffffffffffffffffffffffffffff0000ffffffffffffffffffffffffffff0000,input 6,input 4,input 5,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_23 : Impossible true (goalAt 119) 6 state119_23.toFinset :=
  node_ok cuts119 [⟨state119_20,exclude119_20⟩,⟨state119_21,exclude119_21⟩,⟨state119_22,exclude119_22⟩] 0x46421890834301190846421490834301190834301190846420d0c200021190846424000846421110044421110862421810060421810852421410050421410832301c0c060220c8c200010c8c0323040000434211908151410d08414010d08434210508434218908313010d08434214908313010d08313010d0843420c4c2000010d084342400047030189086242140c027071490862420c88852421c0c0524214908603005c1c4707 (by decide +kernel)

def state119_24 : List Sig := [0xffffffffffff00000000000000000000ffffffffffff0000,input 6,input 4,input 5,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_24 : Impossible true (goalAt 119) 6 state119_24.toFinset :=
  node_ok cuts119 [⟨state119_11,exclude119_11⟩] 0x46421890834301190846421490834301190834301190846420d0c046421110044421110862421810060421810852421410050421410832301141445070c8c0434211908151410d08414010d08434210508434218908313010d08434214908313010d08313010d0843420c4c034141890862420d05052421890832221490832221490852420c888343011908343011908323080000323040000313010d08313010d083414189083414189083222149083222149087030 (by decide +kernel)

def state119_25 : List Sig := [0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 6,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 5,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_25 : Impossible true (goalAt 119) 6 state119_25.toFinset :=
  node_ok cuts119 [⟨state119_6,exclude119_6⟩] 0x1190834300d0c046421190852420d0c046420d0c046421190834300988846421190824301190844401110844420585032300c8c016141490850401410850420c8c060308000032300c88832300c8c1000710d08464205450434210500434210d08414210d0831300c4c0434210d0852420c4c043420c4c0434210d08313008c88434210d082322189086030150505030140c032220d05032220905060301490852421105032221490852424000c6222 (by decide +kernel)

def state119_26 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 6,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_26 : Impossible true (goalAt 119) 6 state119_26.toFinset :=
  node_ok cuts119 [] 0x1190834300d0c046421190862420d0c046420d0c046421190834300d05046421190900101190844401110844420c88832300c8c100071890860401810860420c8c050301808832300585032300c8c0161410d08464205450434210500434210d08414210d0831300c4c0434210d0862420c4c043420c4c0434210d08313005450434210d081514149085030148885030180c034140c8883222090505030189086242400303414189086242400305414 (by decide +kernel)

def state119_27 : List Sig := [0x3333333333330000333333333333000033333333333300003333333333330000,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,input 5,input 0,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_27 : Impossible true (goalAt 119) 6 state119_27.toFinset :=
  node_ok cuts119 [] 0xd0c044421110834301110834300d0c044421110834300d0c044421110834300d0c044420c4c0434210d08313010d08444205450434210d0831300c4c0434210d0831300c4c0434210d0831300c4c043421c0c05414140c05030189087030188886030180c034140c88824141490870301141c70301141c32301808870300c8c0323011108343011108313010d08313010d0816140c8c032300585100070c8c032300c8890000 (by decide +kernel)

def state119_28 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,input 5,input 0,input 1,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_28 : Impossible true (goalAt 119) 7 state119_28.toFinset :=
  node_ok cuts119 [⟨state119_12,exclude119_12⟩,⟨state119_19,exclude119_19⟩,⟨state119_23,exclude119_23⟩,⟨state119_24,exclude119_24⟩,⟨state119_25,exclude119_25⟩,⟨state119_26,exclude119_26⟩,⟨state119_27,exclude119_27⟩] 0x54140d0c034301c0c046421190854141190846421c0c034300d0c034141190846424004034300d0c034140d0c034304000c46421190900101190846420c88834300d0c100100d0c034300c88846421190900101190846424000834300d0c100100d0c034304000846421190862220c8c032301c0c100071c0c062228000060221c0c032300c8c046420c8c046421110016141110046420585044421110032301110900030585016140d05032300c8c100070c8c032300d05016140585032224001032224001c32300c8c032220c8c032304001d00074001d00078001a00014000032300c8c100070c8c032304000100074000047070c4c031301c0c0434210d08470710d0843421c0c031300c4c1001010d08434211908151411909000605450151411908434210d0900071050041400c8c0434210d09000610d0843420c8c0414010509000310d0843420d05031300c4c100060c4c031300d050434210d09000410d0843420c88831300c4c100060c4c031300c888434210d09000610d0843424000431300c4c100060c4c0313040004434210d0870300d0507030150510003150507030800145030150503414140c100034001062421c0c032221c0c062224001062221c0c20004180c062220c88860300d05100030d05100040c88832224000d00030905100034000c52421c0c1000c1c0c047078000c47071c0c200021c0c04707400304707 (by decide +kernel)

def state119_29 : List Sig := [0x3333333333333333333300003333000033333333333333333333000033330000,input 4,input 6,input 0,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_29 : Impossible true (goalAt 119) 6 state119_29.toFinset :=
  node_ok cuts119 [] 0x1c0c034141c0c054141890862421c0c062421890854140d05050300d05046421190862420d0c062420d05034300d0c062421190846421505034300d0c070301190846421505046421190870300d0c0343005c1c46421190852420d0c0524205c1c34300d0c052421190846420941c434210d0862420c4c062420941c31300c4c0624210d08434240018434210d08464205450464240018151405450464210d08434211c1c31300c4c0703010d08434211c1c434210d0870300c4c0313005c1c434210d0852420c4c0524205c1c31300c4c0524210d0843420d05052421490862420c88862420d05032220c88862421490852421c0c032221c0c062221490852421c0c052421490862220c88860301810016141810862420c8c060421810032301810062420585062421110032301110846420585044421110016141110046420c8c046421050032301050843424001843421050100061050043420c8c043421c0c032300c8c062224001060221c0c100041c0c062220c8c032301410100001410852420c8c05042141003230141005242400005242 (by decide +kernel)

def state119_30 : List Sig := [0x3333333333333333333300003333000033333333333333333333000033330000,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 4,input 6,input 0,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_30 : Impossible true (goalAt 119) 6 state119_30.toFinset :=
  node_ok cuts119 [] 0x1c0c062421890850300941c62421890825071190862420d0c046420d0c046421190834301190852420d0c0464209088464211908242210d0862420c4c0434210d0846420545043420c4c0434210d08313010d0852420c4c0434208c88434210d0823221888852421890834141490870301490860300c888604218108604018908444211108444011908414210d08414010d0832304001070300c8c05042141085040149090000 (by decide +kernel)

def state119_31 : List Sig := [0xffffffff00000000ffff000000000000ffffffff00000000ffff0000,input 5,input 4,input 6,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_31 : Impossible true (goalAt 119) 6 state119_31.toFinset :=
  node_ok cuts119 [] 0x34301190846420d0c046421490834301190846420d0c034301190846421110044421110832301c0c060220c8c052421410050421410816140c8c0323005850434211908151410d08414010d08434210508313010d0843420c4c0434214908313010d0843420c4c0313010d087030149085242180c052420c88832221490870301505070301505046420d0c046420d0c016140c8c016140c8c043420c4c043420c4c054141c0c054141c0c052420c88852420c8886242 (by decide +kernel)

def state119_32 : List Sig := [0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 4,input 6,input 0,input 1,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_32 : Impossible true (goalAt 119) 7 state119_32.toFinset :=
  node_ok cuts119 [⟨state119_25,exclude119_25⟩,⟨state119_7,exclude119_7⟩,⟨state119_10,exclude119_10⟩,⟨state119_23,exclude119_23⟩,⟨state119_29,exclude119_29⟩,⟨state119_30,exclude119_30⟩,⟨state119_31,exclude119_31⟩] 0x70300d0507030150506242189087030189086242150503414140c2000609c1c27074000c62421890a00031890862424000c270709c1c34141190846421890834301890834140d0c034301890846421190854140d0c034301c0c046421190854141190846421c0c034300d0c100041190846421490834301490900090d0c034301490846421190900090988826224000846421190900091190846424000826220988862420585062421810032301810062420c8c060421810016141810846420c8c046421110016141110046420585044421110032301110900040c8c032301c0c100041c0c100048000a00011c0c032300c8c052424001052421410032301410052420c8c050421410100041410900048001600044000032300c8c100040c8c0323040001000440000270710d0843421890831301890827070c4c0313018908434210d09000610d08434211908151411909000605450151411908434210d0900041050041400c8c0434210d09000610d0843420c8c041401050900060c4c031301c0c0434210d09000610d0843421c0c031300c4c1000410d0843421490831301490900060c4c0313014908434210d09000608c88232240004434210d09000610d08434240004232208c8900044001062220d05052421490862424001062420d05200000d05062421490852421c0c1000c1c0c1000414908524240011000c180c1000c400303222 (by decide +kernel)

def state119_33 : List Sig := [0xccccffffccccffffccccccccccccccccccccffffccccffffcccccccccccccccc,input 4,input 6,input 0,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_33 : Impossible true (goalAt 119) 6 state119_33.toFinset :=
  node_ok cuts119 [] 0x1c0c034141c0c054141810860421c0c060421810854140d05050300d05044421110860420d0c060420d05034300d0c060421110844421505034300d0c070301110844421505044421110870300d0c0343005c1c44421110852420d0c0524205c1c34300d0c0524211108444209c1c434210d0860420c4c0604209c1c31300c4c0604210d08434240018434210d08444205450444240018151405450444210d0843421141c31300c4c0703010d0843421141c434210d0870300c4c0313005c1c434210d0852420c4c0524205c1c31300c4c0524210d0843424001831300c4c0323010d08434240018434210d0832300c4c031300d05052421490860420c88860420d05032220c88860421490852421c0c032221c0c060221490852421c0c052421490860220c88832221810816141810834140c8c032301810832301810834140585016141110832301110834300585034301110816141110834300c8c032301808832300c8c070304000070301808900001808870300c8c032301490900001490815050c8c03230149083230141081505400005042 (by decide +kernel)

def state119_34 : List Sig := [0xf0f0f0f00000f0f0f0f0f0f000000000f0f0f0f00000f0f0f0f0f0f00000000,input 5,input 4,input 6,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_34 : Impossible true (goalAt 119) 5 state119_34.toFinset :=
  node_ok cuts119 [] 0xc8c070301808832300c88832300c8c0110718908604018108604210500434210d0841420c4c0434210d08313010d0831300c4c0434210d0862420c4c043421c0c06222180c060301c90862420c88862421c0c0624218908341411108444211908444010d08151410d0846420d0c04642119083430119083430149084642119083430189084642 (by decide +kernel)

def state119_35 : List Sig := [0xffffffff0000ffffffffffff00000000ffffffff0000ffffffffffff00000000,input 5,input 4,input 6,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_35 : Impossible true (goalAt 119) 6 state119_35.toFinset :=
  node_ok cuts119 [⟨state119_34,exclude119_34⟩] 0x34301190846420d0c046420d0c034301190846421890834301190a00001190846424000846421110044421110832301c0c060220c8c032220c8c032300541c62421810060421810816140c8c0323005850434211908151410d08414010d08434210508313010d0843420c4c043420c4c0313010d08434218908313010d08151410d084342054507030188886030180c072421890832221890817070c88852421490870301890862421505034141c0c054141c0c05414 (by decide +kernel)

def state119_36 : List Sig := [0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000,input 4,input 6,input 0,input 1,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_36 : Impossible true (goalAt 119) 7 state119_36.toFinset :=
  node_ok cuts119 [⟨state119_8,exclude119_8⟩,⟨state119_33,exclude119_33⟩,⟨state119_35,exclude119_35⟩] 0x70300d0507030150506242189087030189086242150503414140c034141190846421890834301890834140d0c034301890846421190854140d0c034301c0c046421190854141190846421c0c034300d0c017071190846420c88834300d0c017070d0c034300c88846421190862420585062421810032301810062420c8c060421810016141810846420c8c0464211100161411100464205850444211100323011109000c0c8c032301c0c1000c1c0c100044003200001c0c032300c8c032224001032220541432300c8c032220c8c032300541500040541c270710d0843421890831301890827070c4c0313018908434210d09000610d08434211908151411909000605450151411908434210d0900041050041400c8c0434210d09000610d0843420c8c0414010509000c0c4c031301c0c0434210d09000610d0843421c0c031300c4c0170710d0843420c88831300c4c017070c4c031300c888434210d08341405c1c34141890832221890834140c88832221890817071890900044003072221c0c1000c1c0c1000c0c88832221890900031890834144003034141890a00021890834144000c341411909000211908343040030343011909000911908343040008343040031000040000323040030323040031000480004323040000323010d09000110d08313040030313010d09000610d08313040004313040031000c18889000c400105242 (by decide +kernel)

def state119_37 : List Sig := [0xafafafafafafafafafafafafaaaaaaaaafafafafafafafafafafafafaaaaaaaa,input 0,input 5,input 6,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_37 : Impossible true (goalAt 119) 5 state119_37.toFinset :=
  node_ok cuts119 [] 0x7030149085242180c052421890832221490852421410050421410832301c0c060220c8c06242181006042181087030189086242140c0434214908313010d08414010d08434211508313010d0843420c4c0434218908313010d0815141190834301490846421110844421190844400d0c04642119083430119083430189084642 (by decide +kernel)

def state119_38 : List Sig := [0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,0x505050505050505050505050000000005050505050505050505050500000000,input 5,input 6,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_38 : Impossible true (goalAt 119) 4 state119_38.toFinset :=
  node_ok cuts119 [] 0x1c0c052421490860301490862420c88852421c0c0624218908503010d0834301450843420d0c0434210d08343010d08343018508434211108434210d0841401490850401410850420c8c07030180883230189086040181086042 (by decide +kernel)

def state119_39 : List Sig := [0x505050505050505050505050000000005050505050505050505050500000000,input 0,input 5,input 6,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_39 : Impossible true (goalAt 119) 5 state119_39.toFinset :=
  node_ok cuts119 [⟨state119_38,exclude119_38⟩] 0x7030149085242180c052421890832221490852421410050421410832301c0c060220c8c06242181006042181087030189086242140c013071490815141490815140c8c200000c8c015141c0c043071c0c015141890823071890846420d0c052421190844421110846421110034301190846420d0c046420d0c06242119084342 (by decide +kernel)

def state119_40 : List Sig := [0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 0,0xf0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f0f0f0f0f0f0f0f0f00000000,input 5,input 6,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_40 : Impossible true (goalAt 119) 5 state119_40.toFinset :=
  node_ok cuts119 [⟨state119_38,exclude119_38⟩] 0x7030149085242180c05242189083222149087030189086242140c046420d0c052421190834301190846420d0c046420d0c0624211908434280000434211508444211108464211100434214508110710d08232210d0843421c0c0434218508232210d0841401490850401410850420c8c07030180883230189086040181086042 (by decide +kernel)

def state119_41 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f0f0f0f0f0f0f0f0f00000000,input 5,input 6,input 0,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_41 : Impossible true (goalAt 119) 6 state119_41.toFinset :=
  node_ok cuts119 [⟨state119_15,exclude119_15⟩,⟨state119_1,exclude119_1⟩,⟨state119_37,exclude119_37⟩,⟨state119_39,exclude119_39⟩,⟨state119_40,exclude119_40⟩] 0x1c0c032221c0c062221490852421c0c052421490862220c88860300d05052421490862420c88862420d05032220c88862421490852421490a00011490850400c8c050401490832301410850404003c50421888832300c8c070304003c70301888a00001808870300c8c032301890816141890860400c8c0604018908323018108604005850604204c1c434210d0852420c4c0524204c1c31300c4c0524210d0843424003c414010500323010d08434280010434210d08323010500414211c1c31300c4c0703010d08434211c1c434210d0870300c4c0313009c1c434210d0862420c4c0624209c1c31300c4c0624210d0843421c0c034141c0c054141890862421c0c062421890854140d05050301490846421190813070d0c034301490834301490813071190846420c8c044401110816141190844420c8c0464211908161411100444010d08464210d0815148000c151410d0a000210d0815141190846421c0c034300d0c054141190846421c0c046421190854140d0c034301890846421190834140d0c03430189083430189083414119084642 (by decide +kernel)

def state119_42 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f0f0f0f0f0f0f0f0f00000000,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 5,input 6,input 0,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_42 : Impossible true (goalAt 119) 6 state119_42.toFinset :=
  node_ok cuts119 [] 0x1c0c052421490860301490862420c888524204c1c52421490813071490850401410850420c8c070301808832301890860401810860420585032300c8c0161410d0852420c4c0434210500434210d0841420c4c0434210d08313010d0862420c4c0434205450434210d0815141505070301890850300d05046420d0c052421190844421110846421110043420545043421190834301190846420d0c046420d0c06242119090002 (by decide +kernel)

def state119_43 : List Sig := [0xccccffffccccffffccccffffccccccccccccffffccccffffccccffffcccccccc,input 4,input 5,input 6,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_43 : Impossible true (goalAt 119) 5 state119_43.toFinset :=
  node_ok cuts119 [] 0xd0c044421110834301110860420d0c044421110852420d0c0444210d0844420545043420c4c0434210d08313010d0860420c4c0434210d0852420c4c043420c4c0434210d0831301c0c060421810850301c0c052421490832221490860420c88852421110834301110832300c8c07030180883230181083230181081614149083230141085042 (by decide +kernel)

def state119_44 : List Sig := [0xffff0000ffff0000ffff000000000000ffff0000ffff0000ffff00000000,input 4,input 5,input 6,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_44 : Impossible true (goalAt 119) 6 state119_44.toFinset :=
  node_ok cuts119 [⟨state119_43,exclude119_43⟩] 0x34301190846420d0c046421890834301190846420d0c034301190846421110044421110832301c0c060220c8c062421810060421810817070c8c032300541c434211908151410d08414010d08434210508313010d0843420c4c0434218908313010d0843420c4c0313010d087030189086242140c070301888870301888834141890834141890846420d0c046420d0c100000c8c200000c8c043420c4c043420c4c062221c0c062221c0c062420d05062420d0505242 (by decide +kernel)

def state119_45 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 5,input 6,input 0,input 1,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_45 : Impossible true (goalAt 119) 7 state119_45.toFinset :=
  node_ok cuts119 [⟨state119_16,exclude119_16⟩,⟨state119_2,exclude119_2⟩,⟨state119_23,exclude119_23⟩,⟨state119_26,exclude119_26⟩,⟨state119_41,exclude119_41⟩,⟨state119_42,exclude119_42⟩,⟨state119_44,exclude119_44⟩] 0x70300c8887030188885242149087030149085242188883222180c100031490852421890832221890a00030c88832221890852421490a000605c1c17074001052421490a000214908524240010170705c1c17071190846421490834301490817070d0c034301490846421190900100d0c034301c0c046421190900101190846421c0c034300d0c100031190846421890834301890900100d0c034301890846421190900108001600044000846421190900101190846424000900104000852428000452421410032301410052420c8c050421410100071410846420c8c046421110016141110046420585044421110032301110862220c8c032301c0c100071c0c062228000060221c0c032300c8c062420585062421810032301810062420c8c060421810016141810900070585016144000032300c8c100070c8c0323040000161405850170710d0843421490831301490817070c4c0313014908434210d09001010d08434211908151411909001105450151411908434210d0900071050041400c8c0434210d09001110d0843420c8c041401050900110c4c031301c0c0434210d09001110d0843421c0c031300c4c1000310d0843421890831301890900110c4c0313018908434210d09001105450151440004434210d09001110d0843424000415140545100034000c54141c0c1000c1c0c100031890862424000d0003140c10003400303414 (by decide +kernel)

def state119_46 : List Sig := [0xfafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafa,0xeeeeeeeeffffffffeeeeeeeeeeeeeeeeeeeeeeeeffffffffeeeeeeeeeeeeeeee,input 5,input 6,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_46 : Impossible true (goalAt 119) 4 state119_46.toFinset :=
  node_ok cuts119 [] 0x1c0c050421410860301410862420c88850421c0c062421890834141410832301410900060c8c0703018088323018908323018108604210d08313010d08323010d0850420d0c043420d0c0434210d08343010d0861420d0c04342 (by decide +kernel)

def state119_47 : List Sig := [0xeeeeeeeeffffffffeeeeeeeeeeeeeeeeeeeeeeeeffffffffeeeeeeeeeeeeeeee,input 0,input 5,input 6,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_47 : Impossible true (goalAt 119) 5 state119_47.toFinset :=
  node_ok cuts119 [⟨state119_46,exclude119_46⟩] 0x7030141085042180c050421890832221410844421410834301110834301110844420d0c044421890834301110870301890862420d050434214108150710d0843421110a000010d08232210d0843421c0c0434218508232210d0831301410832301410900041110834301110832300c8c07030180883230189083230181086042 (by decide +kernel)

def state119_48 : List Sig := [0xfafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafa,input 0,0xccccccccffffffffccccccccccccccccccccccccffffffffcccccccccccccccc,input 5,input 6,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_48 : Impossible true (goalAt 119) 5 state119_48.toFinset :=
  node_ok cuts119 [⟨state119_46,exclude119_46⟩] 0x7030141085042180c050421890832221410870301890862420d05050420c8c050420441c32301c0c060220c8c062420c8c060421810844420d0c044420c8c013071410815141410815141c0c041071c0c015141890823071890815140c8c200000c8c043421110850420d0c044420d0c044421110834301110862420d0c04442 (by decide +kernel)

def state119_49 : List Sig := [0xccccccccffffffffccccccccccccccccccccccccffffffffcccccccccccccccc,input 5,input 6,input 0,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_49 : Impossible true (goalAt 119) 6 state119_49.toFinset :=
  node_ok cuts119 [⟨state119_47,exclude119_47⟩,⟨state119_48,exclude119_48⟩] 0x1c0c032221c0c062221410850421c0c050421410862220c88860300d05050421410862420c88862420d05032220c888624214108504205c1c44421110850420d0c0504205c1c34300d0c050421110844421141c34300d0c070301110844421141c44421110870300d0c034300d05044421110862420d0c062420d05034300d0c0624211108444205c1c434210d0850420c4c0504205c1c31300c4c0504210d0843424003c434210d08444205450444280004151405450444210d0843421141c31300c4c0703010d0843421141c434210d0870300c4c0313009c1c434210d0862420c4c0624209c1c31300c4c0624210d0843424002c31300c4c0323010d08434280000434210d0832300c4c031301c0c034141c0c045071890862421c0c062421890845070d05034141410900041410815050c8c032301410832301410815054001015071110832301110834300585034301110816141110834300c8c032301888832300c8c070304000070301888900001808870300c8c032301890816141890834140c8c03230189083230181083414058506042 (by decide +kernel)

def state119_50 : List Sig := [0x3333000033333333333300003333000033330000333333333333000033330000,input 4,input 5,input 6,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_50 : Impossible true (goalAt 119) 5 state119_50.toFinset :=
  node_ok cuts119 [] 0xd0c046421190834301190860420d0c046421190852420d0c0464210d0846420545043420c4c0434210d08313010d0860420c4c0434210d0852420c4c043421c0c060421810850301c0c052421490832221490860420c88852421110844421110046421050843421050043420c8c060221c0c03230058506042181006042141085042141005242 (by decide +kernel)

def state119_51 : List Sig := [0xffff0000ffffffffffff0000ffff0000ffff0000ffffffffffff0000ffff0000,input 4,input 5,input 6,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_51 : Impossible true (goalAt 119) 6 state119_51.toFinset :=
  node_ok cuts119 [⟨state119_50,exclude119_50⟩] 0x34301190846420d0c046420d0c034301190846421490834301190826221190846420988846421110044421110832301c0c060220c8c016140c8c032300585052421410050421410a00000c8c0323040000434211908151410d08414010d08434210508313010d0843420c4c043420c4c0313010d08434214908313010d08232210d08434208c887030150505030140c070301490852421888852421c90834141490832221c0c062221c0c062220d0502707189086242 (by decide +kernel)

def state119_52 : List Sig := [0xffffffff000000000000000000000000ffffffff0000000000000000,input 5,input 6,input 0,input 1,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_52 : Impossible true (goalAt 119) 7 state119_52.toFinset :=
  node_ok cuts119 [⟨state119_4,exclude119_4⟩,⟨state119_49,exclude119_49⟩,⟨state119_51,exclude119_51⟩] 0x70300c8887030188885242149087030149085242188883222180c0341414908524209c1c32220c88834140c888322209c1c52421490817071190846421490834301490817070d0c0343014908464211909000c0d0c034301c0c046421190900101190846421c0c034300d0c0341411908464208c0c34300d0c034140d0c0343008c0c46421190852428000052421410032301410052420c8c050421410100071410846420c8c046421110016141110046420585044421110032301110862220c8c032301c0c100071c0c062224003060221c0c032300c8c027070585016140d05032300c8c027070c8c032300d050161405850170710d0843421490831301490817070c4c0313014908434210d09001010d08434211908151411909001205450151411908434210d0900071050041400c8c0434210d09001210d0843420c8c0414010509000c0c4c031301c0c0434210d09001210d0843421c0c031300c4c0270710d0843420d05031300c4c027070c4c031300d050434210d0900034000c74141c0c1000c1c0c100030d05034141490900041490832224003032221490a00021490832224003032221190900021190834304003034301190900101190834304000834304001d00004000032304001c323040031000780004323040000323010d09000110d08313040030313010d09001210d0831304000431304000d000315051000c4000c6242 (by decide +kernel)

def state119_53 : List Sig := roots 119
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_53 : Impossible true (goalAt 119) 8 state119_53.toFinset :=
  node_ok cuts119 [⟨state119_5,exclude119_5⟩,⟨state119_17,exclude119_17⟩,⟨state119_28,exclude119_28⟩,⟨state119_32,exclude119_32⟩,⟨state119_36,exclude119_36⟩,⟨state119_45,exclude119_45⟩,⟨state119_52,exclude119_52⟩] 0x8001870300d05070304000c54141890862428001470301890862424000c54140d05050308001070300c88870304001062221490852428000c70301490852424001062220c88860304000c34141490852424001062420c88862428000834140c88832224000c62421490852424000854140d0c034304000870301190846424000854141190846424000870300d0c034304000834141190846424000862420d0c062424000834140d0c034304000862421190846424000817071190846424000852420d0c052424000817070d0c034304000852421190846424000062220c8c032304000070304000070304000062228000460224000070300c8c032304000062420585062424000060400c8c060404000062420c8c060424000060400585060424000052428000052424000050400c8c050404000052420c8c050424000050404000050424000046420c8c046424000044400585044404000046420585044424000044400c8c044424000447070c4c0313040004703010d08434240004470710d0843424000470300c4c0313040004270710d0843424000462420c4c062424000427070c4c0313040004624210d08434240004170710d0843424000452420c4c052424000417070c4c0313040004524210d08434240005000110d08434240004464205450464240005000105450151440004464210d08434240001000010500414040000323010d08434240001000110d084342400003230105004142 (by decide +kernel)

theorem lower119 : Claim 119 9 :=
  fromSearch 1348 (by decide +kernel) exclude119_53

theorem lower225 : Claim 225 5 :=
  fromLift 5 1 1342177285 lower224 (by decide +kernel)

theorem lower197 : Claim 197 5 :=
  fromLift 5 1 536872454 lower196 (by decide +kernel)

theorem lower165 : Claim 165 5 :=
  fromLift 5 1 536872197 lower164 (by decide +kernel)

def rule229_0 : {c : Cut // CutGood (goalAt 229) c} :=
  ruleFor 229 lower228 none (by decide +kernel)

def rule229_1 : {c : Cut // CutGood (goalAt 229) c} :=
  ruleFor 229 lower225 none (by decide +kernel)

def rule229_2 : {c : Cut // CutGood (goalAt 229) c} :=
  ruleFor 229 lower197 none (by decide +kernel)

def rule229_3 : {c : Cut // CutGood (goalAt 229) c} :=
  ruleFor 229 lower165 none (by decide +kernel)

def rule229_4 : {c : Cut // CutGood (goalAt 229) c} :=
  ruleFor 229 lower97 none (by decide +kernel)

def rule229_5 : {c : Cut // CutGood (goalAt 229) c} :=
  ruleFor 229 lower101 none (by decide +kernel)

def rule229_6 : {c : Cut // CutGood (goalAt 229) c} :=
  ruleFor 229 lower196 none (by decide +kernel)

def rule229_7 : {c : Cut // CutGood (goalAt 229) c} :=
  ruleFor 229 lower224 none (by decide +kernel)

def rule229_8 : {c : Cut // CutGood (goalAt 229) c} :=
  ruleFor 229 lower164 none (by decide +kernel)

def rule229_9 : {c : Cut // CutGood (goalAt 229) c} :=
  ruleFor 229 lower100 none (by decide +kernel)

def cuts229 : Cuts (goalAt 229) := [rule229_0,rule229_1,rule229_2,rule229_3,rule229_4,rule229_5,rule229_6,rule229_7,rule229_8,rule229_9]

def state229_0 : List Sig := [0xfffffffffffffffffffffffff0f0f0f0fffffffffffffffffffffffff0f0f0f0,input 6,input 5,0xfafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafa,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_0 : Impossible true (goalAt 229) 4 state229_0.toFinset :=
  node_ok cuts229 [] 0x10500c04021014414010500604008480414008480414010500212021204848021205000018100c04028080604018080604018100210528604c04028080c04018080c181301008481212050004 (by decide +kernel)

def state229_1 : List Sig := [0xfffffffff0f0f0f00000000000000000fffffffff0f0f0f0,input 6,input 5,0xfafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafa,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_1 : Impossible true (goalAt 229) 4 state229_1.toFinset :=
  node_ok cuts229 [] 0x414030100840510500414018100212010500c18130200c08130204604030100a02018100e18130604604030604c04030604c18111604a020212048481301008480212048481105008481286042105212046020 (by decide +kernel)

def state229_2 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 6,0xfffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0,0xfafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafa,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_2 : Impossible true (goalAt 229) 4 state229_2.toFinset :=
  node_ok cuts229 [] 0x41403010084051050084812120084811050021201050041400848021051050041404001c604021204848118100848118100604021204848128604604021204c04028080c04018080c181301008405301002105 (by decide +kernel)

def state229_3 : List Sig := [0xfffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0,input 5,0xfafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafa,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_3 : Impossible true (goalAt 229) 5 state229_3.toFinset :=
  node_ok cuts229 [⟨state229_0,exclude229_0⟩,⟨state229_1,exclude229_1⟩,⟨state229_2,exclude229_2⟩] 0xc04018080c04028080c18130604c04030604c18128080602010604840510500414030101000430100840540010840530100414010500c18108480c18130200414030200c18110500c0813020021203020421051050041404001c212008480210508480212040018414010500848110500848140000212021200848108480848140000414010500a02008414a02030101000430100a02040010a02030100210530100602008414602030605000630604602080008602030604210530605000140004a18128081000428080c04021204848128080848121204c04040010c04018080848121204c18180004c18118082000018080c181212048481 (by decide +kernel)

def state229_4 : List Sig := [0xffffffff00000000f0f0f0f000000000ffffffff00000000f0f0f0f0,input 5,input 6,0xfafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafa,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_4 : Impossible true (goalAt 229) 4 state229_4.toFinset :=
  node_ok cuts229 [] 0x414030100840510500212010500414008480a18128200a08128204c04028080c04018080a02028604a18130100a18138604602028604c040212048481280808480212048481084808481306044105212046040 (by decide +kernel)

def state229_5 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 5,0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0,0xfafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafa,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_5 : Impossible true (goalAt 229) 4 state229_5.toFinset :=
  node_ok cuts229 [] 0x41403010084051050084812120084810848041401810021201050041051050041404001cc04021204848118080848130604602021204604030100a02018100602021204604021204a181301008405301004105 (by decide +kernel)

def state229_6 : List Sig := [0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0,input 6,0xfafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafa,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_6 : Impossible true (goalAt 229) 5 state229_6.toFinset :=
  node_ok cuts229 [⟨state229_0,exclude229_0⟩,⟨state229_4,exclude229_4⟩,⟨state229_5,exclude229_5⟩] 0xa02018100604030100a18128604a02028604a18130100604018101000828604a18110414604018102000218100604010414a18128606000128604a18121204604021206000018100604021204a18121204840510500414030101000430100840540010840530100414010500a18110500a18128200212028200a18108480a0812820041402820441050848021204001c414010500410510500414040020212008480848108480848140000414021200848110500848140000212008480c04010414c04028081000828080c04040010c04028080410528081000140004c18130101000430100a02021204848130100848121204a02040010a020 (by decide +kernel)

def state229_7 : List Sig := [0x505050505050505050505050000000005050505050505050505050500000000,input 5,input 6,input 2,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_7 : Impossible true (goalAt 229) 4 state229_7.toFinset :=
  node_ok cuts229 [] 0x840521204848130100848130604410521204848128604210521204c04030604c18110600604028604a18118100a18130604604028604414021014c04010500444030204c08110500c18128204a08118100a181 (by decide +kernel)

def state229_8 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 5,input 6,0xfafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafa,input 2,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_8 : Impossible true (goalAt 229) 5 state229_8.toFinset :=
  node_ok cuts229 [⟨state229_0,exclude229_0⟩,⟨state229_2,exclude229_2⟩,⟨state229_5,exclude229_5⟩,⟨state229_7,exclude229_7⟩] 0x21014848121204c0402120084811808200022120484811810200012120484814000600002120441403010084051050021201050041400848041401810021201050200031050041404001cc04028080c04018080c18118100c04028080604018080604040020a181301008405301008405 (by decide +kernel)

def state229_9 : List Sig := [0xfafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafa,input 2,input 5,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_9 : Impossible true (goalAt 229) 6 state229_9.toFinset :=
  node_ok cuts229 [⟨state229_3,exclude229_3⟩,⟨state229_6,exclude229_6⟩,⟨state229_8,exclude229_8⟩] 0x40010c04018080c04040020a02030604c18140010c04030604c18140020a02018080418140010a02018100604040010c04028604a18140010a02028604a18140010c04018100604040020602028604a18140018c18118100c18180008602018100604040020c18128604a18140004840540010840540004c04021204848140004840521204848140004c04040004c04040004440521204848140004c18140004c18140004440580004410540004c18121204848140004240521204848140004a18140004a18140004240580000210540004a18121204848140001000040000848040010840510500414040010c04040010c04040010840540010840540010c04010500414040020c18108480c1814001cc08010500c0804001cc18110500c08140020c08008480c08140018a18110500a1814001ca08008480a0804001ca18108480a08140018a08010500a081 (by decide +kernel)

def state229_10 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 6,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_10 : Impossible true (goalAt 229) 4 state229_10.toFinset :=
  node_ok cuts229 [] 0x444021204848110500444021204848111100848111100444021204848128204444021204414018100212010500414008480414008480604018080604021014c08110500a08128205000918100a081282048405 (by decide +kernel)

def state229_11 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000,input 6,input 5,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_11 : Impossible true (goalAt 229) 4 state229_11.toFinset :=
  node_ok cuts229 [] 0x11100848121204414021204a08109080848121204c08111100848121014848121205000421014414010501000018100a08128204414028204c08118100a08109414414030204c081084804505 (by decide +kernel)

def state229_12 : List Sig := [0xffffffffffffffff0000000000000000ffffffff00000000,input 6,input 5,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_12 : Impossible true (goalAt 229) 4 state229_12.toFinset :=
  node_ok cuts229 [] 0x444021204848110500848128204242021204848111100444021204604028204a08110500a08118100604028204414008480414008480848111100848111100212010500212010500a08118100a08118100c081 (by decide +kernel)

def state229_13 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_13 : Impossible true (goalAt 229) 5 state229_13.toFinset :=
  node_ok cuts229 [⟨state229_10,exclude229_10⟩,⟨state229_11,exclude229_11⟩,⟨state229_12,exclude229_12⟩] 0x414018080414008480c08130204414030204c08108480602008482000211414450521014c08130206000130204c08121014450510600450521204848130204444030204450511100444030204848121205000411100444010500848121205000421204848110500444010501000421204848128204242028205000409080242028204848121204840511100444040010848121204840521204848140010444011100840510500414040000212030100840508480212040000414010500602028204a08130205000630204602080000602030204a08128204212040024212010500a08128204212028204a081105010009105010005400146040 (by decide +kernel)

def state229_14 : List Sig := [0xffffffff00000000ffffffff00000000ffffffff0000000000000000,input 5,input 6,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_14 : Impossible true (goalAt 229) 4 state229_14.toFinset :=
  node_ok cuts229 [] 0x444021204848110500848130204444021204848109080242021204414030204c08108480212010500212010500602030204602030204848109080848109080414008480414008480c08118080c08118080a081 (by decide +kernel)

def state229_15 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 5,0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_15 : Impossible true (goalAt 229) 4 state229_15.toFinset :=
  node_ok cuts229 [] 0x444021204848110500242021204848109080848118100242021204848130204444021204212010500414008480604010500212010500602018100604021014a08110500c08130205000918080c081302048405 (by decide +kernel)

def state229_16 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_16 : Impossible true (goalAt 229) 5 state229_16.toFinset :=
  node_ok cuts229 [⟨state229_11,exclude229_11⟩,⟨state229_14,exclude229_14⟩,⟨state229_15,exclude229_15⟩] 0x212018100604010500a08128204212028204a08110500604010501000828204a08130204604030206000218100604030204a08128206000109414250521014a08128206000028204a08121014250508600250521204848128204242028204250509080242028204848121205000411100444010500848121205000421204848110500444010501000821204848130204444030205000411100444030204848121204840509080242040010848121204840521204848140010242009080840508480212040000414010500840510500414040000212008480414040024414008480c08130204414030204c081084810008084810005400146020 (by decide +kernel)

def state229_17 : List Sig := [0x55555555555555555555555500000000,input 5,input 6,input 7,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_17 : Impossible true (goalAt 229) 4 state229_17.toFinset :=
  node_ok cuts229 [] 0x444021204848111100848130204444021204848128204242021204602030204c08110600604028204a08118100a08130204604028204414021204444021204c04008480c08110500c08110500a08118100a081 (by decide +kernel)

def state229_18 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 5,input 6,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 7,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_18 : Impossible true (goalAt 229) 5 state229_18.toFinset :=
  node_ok cuts229 [⟨state229_11,exclude229_11⟩,⟨state229_10,exclude229_10⟩,⟨state229_15,exclude229_15⟩,⟨state229_17,exclude229_17⟩] 0x11100848121204444011100848121204414021204444011100848121204604009080848121204444011100848130100602021016000218080414008480414008480c08118100840580004604018100414008480414018080604040020a081400148405800008405105020003105010009 (by decide +kernel)

def state229_19 : List Sig := [0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 7,input 2,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_19 : Impossible true (goalAt 229) 6 state229_19.toFinset :=
  node_ok cuts229 [⟨state229_13,exclude229_13⟩,⟨state229_16,exclude229_16⟩,⟨state229_18,exclude229_18⟩] 0x40015000518080602040014840530204c08140016000130204c08140014840518080418040024414018080414040020212030204c08140024414030204c08140020212018080212040020602028204a08140018c08118100c08180008602018100604040020c08128204a08140015000518100604040014840528204a08140016000028204a08140014840518100604040024212018100604040024414028204a08140024212028204a08140024414018100414040020450521204848140010c08111100c08140010450511100444040020c08121204848140010250521204848140010a08109080a08140010250509080242040010a08121204848140014840511100444040015000421204848140014840521204848140015000511100444040011000411100444040010414021204848140011000421204848140010414011100414040001000040000c040 (by decide +kernel)

def state229_20 : List Sig := [0xfffffffffffffffffffffffff0f0f0f0,input 6,input 2,input 5,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_20 : Impossible true (goalAt 229) 4 state229_20.toFinset :=
  node_ok cuts229 [] 0x28604a08028204a08121604848021204848130604c08030204c08128604c18118100a18121604a18109080858121604c18111100858110500840510500c04018100a18118100a18111100858111100858110604c18130100c181 (by decide +kernel)

def state229_21 : List Sig := [0x5555555555555555555555555050505055555555555555555555555550505050,input 6,input 2,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_21 : Impossible true (goalAt 229) 4 state229_21.toFinset :=
  node_ok cuts229 [] 0x18100a18128604604028604c18118100a18111100858121604444021604a18109080858121604c18111100858130100c18130604418010500840530100414028204a08118100a18121204848111100858130204c08110500c181 (by decide +kernel)

def state229_22 : List Sig := [0xfffffffffffffffffffffffff0f0f0f0fffffffffffffffffffffffff0f0f0f0,input 6,input 2,input 5,input 0,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_22 : Impossible true (goalAt 229) 5 state229_22.toFinset :=
  node_ok cuts229 [⟨state229_0,exclude229_0⟩,⟨state229_20,exclude229_20⟩,⟨state229_21,exclude229_21⟩] 0x414030100840510500414018100212010500414011102000010500212010500414008482000210500414040000604030100a02018100602018100604009414a18111100c04021414444011100604009080444009080444011100242021604c04028080c04018080c181301020001301010005 (by decide +kernel)

def state229_23 : List Sig := [0xfffffffff0f0f0f00000000000000000fffffffff0f0f0f0,input 6,input 2,input 5,input 0,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_23 : Impossible true (goalAt 229) 5 state229_23.toFinset :=
  node_ok cuts229 [⟨state229_1,exclude229_1⟩] 0x414030100840510500414018100212010500414011102000010500c18130200c08130204604030100a02018100e18130604604030604444030100850511100444018100242011100c58130604444030604c04030604c18110604a02030100a02030100212010500212010500a181286042505181008581216042420111006020 (by decide +kernel)

def state229_24 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0,0xfffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0,input 0,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_24 : Impossible true (goalAt 229) 4 state229_24.toFinset :=
  node_ok cuts229 [] 0x10500c04021014414010500444008480414008480414010500212009414414010500240511100a44028080444021604858111101000228604a18111100410530100a02030100242030604c181090802105301008505301002505 (by decide +kernel)

def state229_25 : List Sig := [0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0,input 6,0xfffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0,input 5,input 0,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_25 : Impossible true (goalAt 229) 5 state229_25.toFinset :=
  node_ok cuts229 [⟨state229_24,exclude229_24⟩] 0x10500c04021014414010500212008480414010500444008480414008480414010500212008480414010500212028080c04028080c04028604250511416000009414242009414242008414444030100a02011100450511100444010414858121604444040008c04028080c04028080c18130100a020301002420 (by decide +kernel)

def state229_26 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 6,0xfffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0,input 2,input 0,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_26 : Impossible true (goalAt 229) 5 state229_26.toFinset :=
  node_ok cuts229 [⟨state229_24,exclude229_24⟩,⟨state229_2,exclude229_2⟩] 0x10500c04021014414010500242080004414010500604008480414008480414010500212009414414010500240509080c04021414c04021604242011082000009080250509080242008414604030100a0201810060201810060404000ca18128604604040004c04028080c04018080c181301008505301002505 (by decide +kernel)

def state229_27 : List Sig := [0xfffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0,input 2,input 5,input 0,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_27 : Impossible true (goalAt 229) 6 state229_27.toFinset :=
  node_ok cuts229 [⟨state229_3,exclude229_3⟩,⟨state229_22,exclude229_22⟩,⟨state229_23,exclude229_23⟩,⟨state229_25,exclude229_25⟩,⟨state229_26,exclude229_26⟩] 0xc04018080c04028080c18130604c04030604c18128080602010604850510500414030101000430100850540010840530100414010500c18108480c18130200414030200c18110500c08130200212030204250510500414009010212008480250508480212009010414010501000110500414009081000109081000640006000009080414010501000610500414040000212008481000608480212040000414010500a02009414a02030101000230100a02040010a02030100250530100602009414602030605000230604602080010602030604250530605000140004a18121414242009080c04040004c04021415000421414c04009080c04011414242009080c18140004c18111416000311414c18109080c18109415000209415000109080242040005000108415000140008858128081000528080c04040010c04028081000428080c04040014c04018081000318080c18180008c18118082000118080c1814000cc181 (by decide +kernel)

def state229_28 : List Sig := [0xffffffff00000000f0f0f0f000000000ffffffff00000000f0f0f0f0,input 5,input 2,input 6,input 0,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_28 : Impossible true (goalAt 229) 5 state229_28.toFinset :=
  node_ok cuts229 [⟨state229_4,exclude229_4⟩] 0x414030100840510500212010500414008480414011102000010500a18128200a08128204c04028080c04018080444030100850511100242011100444009080a58128604242028604a02028604a18130100a18138604602028604c04028080c04028080414008480414008480c181306044505180808581216044440090806040 (by decide +kernel)

def state229_29 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 5,0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0,input 2,input 0,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_29 : Impossible true (goalAt 229) 5 state229_29.toFinset :=
  node_ok cuts229 [⟨state229_24,exclude229_24⟩,⟨state229_5,exclude229_5⟩] 0x10500c04021014414010500444080004414008480414010500212010500604008480414011414414010500440511100c04021414444021604444018102000011100450511100444010414c04028080c04018080c18130604602040004604030100a02018100602018100604040008a181301008505301004505 (by decide +kernel)

def state229_30 : List Sig := [0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0,input 2,input 6,input 0,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_30 : Impossible true (goalAt 229) 6 state229_30.toFinset :=
  node_ok cuts229 [⟨state229_25,exclude229_25⟩,⟨state229_6,exclude229_6⟩,⟨state229_22,exclude229_22⟩,⟨state229_28,exclude229_28⟩,⟨state229_29,exclude229_29⟩] 0xa02018100604030100a18128604a02028604a18130100604018101000328604a18111414604018102000418100604011414a18128606000328604a18140008604018102000218100604040008a18128604850510500414030101000830100850540010840530100414010500a18110500a18128200212028200a18108480a08128200414028204450508480212011010414010500450510500414011010212008481000110500414011101000111101000840006000111100414010501000808480212040000414010501000810500414040000212008480c04011414c04028081000328080c04040010c04028080450528081000140004c18121414444011100c04040004c04021415000421414c04011100444009414444011100a18140004a18109416000009414a18111100a1811141500031141500011110044404000500011041500014000c858130101000530100a02040010a02030101000430100a02040014a020 (by decide +kernel)

def state229_31 : List Sig := [0xf5f5f5f5f5f5f5f5f5f5f5f5f0f0f0f0,input 2,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_31 : Impossible true (goalAt 229) 3 state229_31.toFinset :=
  node_ok cuts229 [] 0x28204c08118100a08121204c08111100848121204a08109080848108480c08110500c08110500a08118100a081105008481111008481 (by decide +kernel)

def state229_32 : List Sig := [0xf5f5f5f5f5f5f5f5f5f5f5f5f0f0f0f0f5f5f5f5f5f5f5f5f5f5f5f5f0f0f0f0,input 2,input 5,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_32 : Impossible true (goalAt 229) 4 state229_32.toFinset :=
  node_ok cuts229 [⟨state229_31,exclude229_31⟩] 0xc04030604c18110600604028604a18118100a18130604604028604444030100840511100242030604444030604444028604242028604848110502000030100414030204c08110500c18128204a08118100a181 (by decide +kernel)

def state229_33 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f05050505050505050505050500000000,input 7,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_33 : Impossible true (goalAt 229) 3 state229_33.toFinset :=
  node_ok cuts229 [] 0x30100c08130204602028204c08118100a08118100a081282046040212044140302048481212042120282048481105008481212044140 (by decide +kernel)

def state229_34 : List Sig := [0xffffffffffffffffffffffffffffffff55555555555555555555555500000000,input 7,input 5,input 6,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_34 : Impossible true (goalAt 229) 4 state229_34.toFinset :=
  node_ok cuts229 [⟨state229_33,exclude229_33⟩] 0x848130204444021204848128204242021204444021204848111102000021204848110500c04030204c08118080414030204c08108480a08130204604028204604028204a08118100212028204a081105008405 (by decide +kernel)

def state229_35 : List Sig := [0x5555555555555555555555550000000055555555555555555555555500000000,input 5,input 6,input 2,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_35 : Impossible true (goalAt 229) 5 state229_35.toFinset :=
  node_ok cuts229 [⟨state229_7,exclude229_7⟩,⟨state229_17,exclude229_17⟩,⟨state229_32,exclude229_32⟩,⟨state229_34,exclude229_34⟩] 0x21014444011100c04021204848121014848121204c04011100444011414848121204c18111100c18111414444011100c18121204848109414848121204a18109080a18109414242009080a18121204848130100602030100a02030604c18130100c18130604a02018080418028080604018100c04028604a18128080a18128604c04018100604018080a18128604c18118100c18118080604018100c18128604a18130100414010500840580004840530102000330100840510500414011100414010500848180000848111102000211100848110500848118080212030204c18110500c08118080414010500c18108480c18118100414028204a18108480a08118100212018100a18110500a181 (by decide +kernel)

def state229_36 : List Sig := [0x5555555555555555555555555555555555555555555555555555555500000000,input 7,input 5,input 6,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_36 : Impossible true (goalAt 229) 4 state229_36.toFinset :=
  node_ok cuts229 [] 0x21604c18111100858121604a18109080858111100858121604444030100c18130604418128604c18118100a18118100a18128604604021204848121200858130204c08130200c18128204a08128200a181105008405301004140 (by decide +kernel)

def state229_37 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000,input 7,input 5,input 6,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_37 : Impossible true (goalAt 229) 4 state229_37.toFinset :=
  node_ok cuts229 [] 0x30604c08030204c08128604a08028204a08110500c04021014414030100c18130604418128604c18118100a18118100a181286046040212048481216048480216044440306048581216042420286048581111008581216044440 (by decide +kernel)

def state229_38 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000,input 7,input 5,input 6,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_38 : Impossible true (goalAt 229) 5 state229_38.toFinset :=
  node_ok cuts229 [⟨state229_11,exclude229_11⟩,⟨state229_36,exclude229_36⟩,⟨state229_37,exclude229_37⟩] 0x858130604444021604858128604242021604444021604858111102000221604858140004858121200848121204c18130200c08130204a18128200a08128204414030102000010502000110500414040000c04030604c18110604450528604c18118100a18118100a181286046040094148505 (by decide +kernel)

def state229_39 : List Sig := [0xffffffffffffffffffffffff00000000,input 7,input 5,input 6,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_39 : Impossible true (goalAt 229) 5 state229_39.toFinset :=
  node_ok cuts229 [⟨state229_17,exclude229_17⟩] 0x858130604444021604858128604242021604444021604858111100858121200848121204c18130200c08130204a18128200a08128204414021010840510500602030604c18118080a18130604604028604604028604a18118100444021604444021604414080000414040000602030604602030604604028604604028604c040 (by decide +kernel)

def state229_40 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_40 : Impossible true (goalAt 229) 4 state229_40.toFinset :=
  node_ok cuts229 [] 0x21604a18111100858111100858121604444009080858121604242021604848021204848128604a08028204a08110500604008480414008480414010500212018100a18128604418118080a181286042181180806040181010002 (by decide +kernel)

def state229_41 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 7,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 6,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_41 : Impossible true (goalAt 229) 5 state229_41.toFinset :=
  node_ok cuts229 [⟨state229_10,exclude229_10⟩,⟨state229_40,exclude229_40⟩] 0x21604444011100858121604a18111100858111100858121604444011100858121604444021604848021204848108480414010500212028604a08028204a08110500a0208000041401050060400848041403060460202808200011808060401808060404000ca02028604a18108604604028604a18140014c040 (by decide +kernel)

def state229_42 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 5,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_42 : Impossible true (goalAt 229) 5 state229_42.toFinset :=
  node_ok cuts229 [⟨state229_40,exclude229_40⟩,⟨state229_15,exclude229_15⟩] 0x21604604009080858121604c18111100858111100858121604444009080858121604242021604848021204848110500604008480414030604c08030204c08110500c04080004414008480414010500212028604604028102000018100602018100604040008c04030604c18110604602030604c18140008a020 (by decide +kernel)

def state229_43 : List Sig := [0x5555555555555555555555550000000055555555555555555555555500000000,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 5,input 6,input 2,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_43 : Impossible true (goalAt 229) 5 state229_43.toFinset :=
  node_ok cuts229 [] 0x11100848121204444021204444011100848121204604009080848121204444011100848130100a02030100602030604604030100a02018100602018101000828604c04021014c04021014414021014c040105004140212044440212042120105004140084804140084806040105010000 (by decide +kernel)

def state229_44 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f0f0f0f0f0f0f0f0f00000000,input 2,input 5,input 6,input 0,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_44 : Impossible true (goalAt 229) 5 state229_44.toFinset :=
  node_ok cuts229 [⟨state229_7,exclude229_7⟩] 0x414030100840510500212010500414008480414018100212010500858121200848121204c04028080c04018080604030100a02018100602018100604009414850521604858130100858131604450521604858129604250521604c04021414c04021414414080000414040000c18130604602011414a181286046040094144440 (by decide +kernel)

def state229_45 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 5,input 6,input 0,input 2,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_45 : Impossible true (goalAt 229) 6 state229_45.toFinset :=
  node_ok cuts229 [⟨state229_8,exclude229_8⟩,⟨state229_18,exclude229_18⟩,⟨state229_22,exclude229_22⟩,⟨state229_26,exclude229_26⟩,⟨state229_29,exclude229_29⟩,⟨state229_35,exclude229_35⟩,⟨state229_38,exclude229_38⟩,⟨state229_39,exclude229_39⟩,⟨state229_41,exclude229_41⟩,⟨state229_42,exclude229_42⟩,⟨state229_43,exclude229_43⟩,⟨state229_44,exclude229_44⟩] 0x850511100444030100858121604850521604858130100444011101000321604858118080444011102000411100444018080858121605000221604858118100242018102000309080242018100858121606000b2160485814000444401110200021110044404000485812160485051050041403010100083010085058000484053010041401050085811050085812120100082120085818000084812120041402120500030848021201808041401050100081050041401808021200848100021050041401810021201810100080848021201810041401050100088002a000540000414010501000810500414040001000840000c04018080c04028081000328080c04080024c04028080602018081000240008c18128080604018100c04040008c04028082000828080c0401810060401808100031808100021810060404000900024000900024000ca1813010100053010085058001c8505301020006301008505400148505 (by decide +kernel)

def state229_46 : List Sig := [0xffffffffffffffff0000000000000000ffffffff00000000,input 6,input 5,input 7,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_46 : Impossible true (goalAt 229) 5 state229_46.toFinset :=
  node_ok cuts229 [⟨state229_12,exclude229_12⟩] 0x444021604858111100858128604242021604858111100444021604858121200848121204414030102000010500a18128200a08128204212010500414008480604028604a18118100a18118100604028604c04028080c04028080858111100858111100212010500212010500a02030100a02030100a18118100a18118100c181 (by decide +kernel)

def state229_47 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_47 : Impossible true (goalAt 229) 5 state229_47.toFinset :=
  node_ok cuts229 [⟨state229_40,exclude229_40⟩] 0x21604a18109080858111100858121604444021604c18111100858109080858121604242021604848021204848128604a08028204a08110500c04008480414030604c08030204c08108480414010500212018100a18130606000028604a02028604a18108604a02030100c04040008c04030604c181106046020 (by decide +kernel)

def state229_48 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,input 7,input 0,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_48 : Impossible true (goalAt 229) 6 state229_48.toFinset :=
  node_ok cuts229 [⟨state229_41,exclude229_41⟩,⟨state229_13,exclude229_13⟩,⟨state229_38,exclude229_38⟩,⟨state229_46,exclude229_46⟩,⟨state229_47,exclude229_47⟩] 0x1000518080602028080c18130606000430604c1812808060201808200031141445054000cc18130606000230604c1814000c450511414450521604858130604444030604450511100444030604858121605000511100444028080858121605000421604858128080444011101000221604858128604242028605000409080242028604858121605000411100444040004858121605000421604858140004444011100c18108480c18130200414030200c18110500c08130200212030204858110500858121201000421200858140010848121200414021205000510500414028081000528081000940016000128080414010500a18110500a18128200212028200a18108480a08128200414028205000910500414040000212008481000908480212040000414010501000240008c04018080a18128604c18140008c18118082000018080c18128604a18128081000528081000228604a181400090002086050002400146040 (by decide +kernel)

def state229_49 : List Sig := [0xffffffff00000000ffffffff00000000ffffffff0000000000000000,input 5,input 6,input 7,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_49 : Impossible true (goalAt 229) 5 state229_49.toFinset :=
  node_ok cuts229 [⟨state229_14,exclude229_14⟩] 0x444021604858111100858130604444021604858109080242021604858121200848121204414030102000010500c18130200c08130204414008480212010500c04030604c18110604a02030100a02030100602030604602030604858109080858109080414008480414008480c04028080c04028080c18118080c18118080a181 (by decide +kernel)

def state229_50 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,input 7,input 0,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_50 : Impossible true (goalAt 229) 6 state229_50.toFinset :=
  node_ok cuts229 [⟨state229_16,exclude229_16⟩,⟨state229_38,exclude229_38⟩,⟨state229_42,exclude229_42⟩,⟨state229_47,exclude229_47⟩,⟨state229_49,exclude229_49⟩] 0x1000518100604030100a18128606000328604a18130100604018101000328604a18130604604030606000218100604030604a18128606000409414250540008a18128606000128604a18140008250509414250521604858128604242028604250509080242028604858121605000511100444030100858121605000421604858130100444011101000321604858130604444030605000411100444030604858121605000409080242040004858121605000421604858140004242009080a18110500a18128200212028200a18108480a08128200414028204858110500858121201000821200858140010848121200414021205000510500414030101000530101000840016000030100414010500c18108480c18130200414030200c18110500c0813020021203020500080848021204000041401050100081050041404000021200848100054000ca02030101000530101000330604c181400150005106050005400146020 (by decide +kernel)

def state229_51 : List Sig := roots 229
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_51 : Impossible true (goalAt 229) 7 state229_51.toFinset :=
  node_ok cuts229 [⟨state229_9,exclude229_9⟩,⟨state229_19,exclude229_19⟩,⟨state229_27,exclude229_27⟩,⟨state229_30,exclude229_30⟩,⟨state229_45,exclude229_45⟩,⟨state229_48,exclude229_48⟩,⟨state229_50,exclude229_50⟩] 0x40014c04018080c0404000ca02030604c18180018c04030604c18140014a02018080418140014a02018100604040008c04028604a18180014a02028604a18140008c0401810060404000c602028604a18140008c18118100c18180010602018100604040008c18128604a18140014850511100444040004c04021604858140010850521604858140004c0401110044404000c450521604858140004c18111100c1818000c450511100444040004c18121604858140008250521604858140004a18109080a18180008250509080242040004a18121604858140000850510500414040000c04040000c04040000850580004840540000c04010500414040000c18108480c18140000c08010500c08040000c18110500c08140000c08008480c08140000a18110500a18140000a08008480a08040000a18108480a08140000a08010500a081400008581105008581400008480400008480400008581800008481400008480105008481 (by decide +kernel)

theorem lower229 : Claim 229 8 :=
  fromSearch 536872197 (by decide +kernel) exclude229_51

theorem lower210 : Claim 210 5 :=
  fromLift 5 2 1140916288 lower208 (by decide +kernel)

def cuts178 : Cuts (goalAt 178) := []

def state178_0 : List Sig := roots 178
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude178_0 : Impossible true (goalAt 178) 3 state178_0.toFinset :=
  node_ok cuts178 [] 0x2c0c0a28228a0890302c0c0928224a08a03024a08a2820c88892820c8c0b03028088323028a08a08028208a08224a089080242089082 (by decide +kernel)

theorem lower178 : Claim 178 4 :=
  fromSearch 1081147456 (by decide +kernel) exclude178_0

def rule242_0 : {c : Cut // CutGood (goalAt 242) c} :=
  ruleFor 242 lower240 none (by decide +kernel)

def rule242_1 : {c : Cut // CutGood (goalAt 242) c} :=
  ruleFor 242 lower224 none (by decide +kernel)

def rule242_2 : {c : Cut // CutGood (goalAt 242) c} :=
  ruleFor 242 lower210 none (by decide +kernel)

def rule242_3 : {c : Cut // CutGood (goalAt 242) c} :=
  ruleFor 242 lower178 none (by decide +kernel)

def rule242_4 : {c : Cut // CutGood (goalAt 242) c} :=
  ruleFor 242 lower114 none (by decide +kernel)

def cuts242 : Cuts (goalAt 242) := [rule242_0,rule242_1,rule242_2,rule242_3,rule242_4]

def state242_0 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffffcccccccccccccccc,input 7,input 6,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_0 : Impossible true (goalAt 242) 4 state242_0.toFinset :=
  node_ok cuts242 [] 0x28208c08218108a08218108a0822820860420c8c0a08228208123024208a0820c888908224208c0821410890821410890822420850420c8c0908224209000130108c0823020860221c0c0b030 (by decide +kernel)

def state242_1 : List Sig := [0xffffffffffffffffcccccccccccccccc,input 7,input 6,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_1 : Impossible true (goalAt 242) 4 state242_1.toFinset :=
  node_ok cuts242 [] 0xa08230208604228208604228208a08218108908228208322224208908230208504224208504224208908214108f03030208c0822c0c0604228208604228208504224208504224208323030208602230208c042 (by decide +kernel)

def state242_2 : List Sig := [0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,input 6,input 4,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_2 : Impossible true (goalAt 242) 5 state242_2.toFinset :=
  node_ok cuts242 [⟨state242_0,exclude242_0⟩,⟨state242_1,exclude242_1⟩] 0xb03018108604230108a28228a08b03028a08a28230108604218108602228a08a28230208604230208602218108604230208a28228a08323028200a08004840a28228a08323028a08a08204840a08028208b03014108504230108928224a08b03024a08928230108504214109000124a08928228a08322228a0900010c888322228a08928224a09000124a08928230208504230209000114108504230208928224a08323024200908040004928224a08323024a08908240004908024208c04218088c0422c0c0c08230208c04230208c0822c0c060222c0c1000040000c08030108323030108b03080004b0303010a000030108b0300c8c03230 (by decide +kernel)

def state242_3 : List Sig := [0xffffffffffffffff0000000000000000cccccccccccccccc,input 6,input 7,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_3 : Impossible true (goalAt 242) 4 state242_3.toFinset :=
  node_ok cuts242 [] 0x604228208a08218108a08218108604228208908228208322224208504224208908214108908214108504224208c0423c0c0c0421c0c0a08218108a08218108908214108908214108323030108a02230108c082 (by decide +kernel)

def state242_4 : List Sig := [0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 7,input 4,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_4 : Impossible true (goalAt 242) 5 state242_4.toFinset :=
  node_ok cuts242 [⟨state242_0,exclude242_0⟩,⟨state242_3,exclude242_3⟩] 0xc0421c0c0c04228088c08230208c04230208c0822808870301c0c200011c0c070300c8c0c0823020a000030208c0820c8c070300c8c0703028208a08230208624230208703018908624230208a08228208a02218908624230108a08228208a02228208a08230108624218908323018100604004840a08228208323028208a0820484060401810870302420890823020852423020870301490852423020890822420900012420890822820832222820900010c888322228208908224209000114908524230108908224209000124208908230108524214908323014100504040004908224208323024208908240004504014109000040000c040 (by decide +kernel)

def state242_5 : List Sig := [0xffffffff00000000ffffffff00000000ffffffff0000000000000000,input 6,input 7,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_5 : Impossible true (goalAt 242) 4 state242_5.toFinset :=
  node_ok cuts242 [] 0x14908928224a08524224a08c28214908928224a08908024208908230908c04030108c04230a08c08030208c08230908c28230a08703024a08322224a08a28228208a08228a08a08018908a28228a08624228a08624230a08a282 (by decide +kernel)

def state242_6 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,input 7,input 1,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_6 : Impossible true (goalAt 242) 5 state242_6.toFinset :=
  node_ok cuts242 [⟨state242_0,exclude242_0⟩,⟨state242_5,exclude242_5⟩] 0x624228a08a28218908a28230a08624228a0a000128a08a28240008928228a08322224a08524224a08928214908928230a08524224a08322224a0892820c888a28228200a08228208928224200908224208c24230100c04230108c28230200c0823020832304000200000c8c0b03030908c2824000c7030 (by decide +kernel)

def state242_7 : List Sig := roots 242
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_7 : Impossible true (goalAt 242) 6 state242_7.toFinset :=
  node_ok cuts242 [⟨state242_2,exclude242_2⟩,⟨state242_4,exclude242_4⟩,⟨state242_6,exclude242_6⟩] 0x40010c2421c0c0c2424000cb03030a08c28280008c24230a08c2824000cb0301c0c0703040008b03018908624240008c24228a08a28240008b03028a08a28240008c24218908624240008703028a08a28240008c28218908c28240008703018908624240008c28228a08a28240004b03014908524240004c24224a08928240004b03024a08928240004c24214908524240004703024a08928240004c28214908c28240004703014908524240004c28224a08928240009000224a08928240008a2820c888a2824000900010c888322240008a28224a08928240000c2420c8c0c24240000c04040000c04040000c24280004c04240000c0400c8c0c04240000c2820c8c0c28240000c08040000c08040000c28280000c08240000c0800c8c0c08240000a28204840a28240000a0800c8c0a08040000a2820c8c0a08240000a08004840a0824000092824000492824000090800c8c090804000092820c8c09082400009080400009082 (by decide +kernel)

theorem lower242 : Claim 242 7 :=
  fromSearch 1147207744 (by decide +kernel) exclude242_7

theorem lower243 : Claim 243 8 :=
  fromLift 8 1 1073741892 lower242 (by decide +kernel)

def cuts150 : Cuts (goalAt 150) := []

def state150_0 : List Sig := roots 150
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude150_0 : Impossible true (goalAt 150) 3 state150_0.toFinset :=
  node_ok cuts150 [] 0x25050928224a08841425050868221a08901421a08928204818868205850941421018161424a08908024208908221a088480212088482 (by decide +kernel)

theorem lower150 : Claim 150 4 :=
  fromSearch 536938304 (by decide +kernel) exclude150_0

def rule214_0 : {c : Cut // CutGood (goalAt 214) c} :=
  ruleFor 214 lower212 none (by decide +kernel)

def rule214_1 : {c : Cut // CutGood (goalAt 214) c} :=
  ruleFor 214 lower196 none (by decide +kernel)

def rule214_2 : {c : Cut // CutGood (goalAt 214) c} :=
  ruleFor 214 lower210 none (by decide +kernel)

def rule214_3 : {c : Cut // CutGood (goalAt 214) c} :=
  ruleFor 214 lower150 none (by decide +kernel)

def rule214_4 : {c : Cut // CutGood (goalAt 214) c} :=
  ruleFor 214 lower86 none (by decide +kernel)

def rule214_5 : {c : Cut // CutGood (goalAt 214) c} :=
  ruleFor 214 lower208 none (by decide +kernel)

def cuts214 : Cuts (goalAt 214) := [rule214_0,rule214_1,rule214_2,rule214_3,rule214_4,rule214_5]

def state214_0 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffffcccccccccccccccc,input 7,input 6,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude214_0 : Impossible true (goalAt 214) 4 state214_0.toFinset :=
  node_ok cuts214 [] 0x24208c08214108908214108908224208504205850908224209000121208908204818848221208c08211108848211108848221208444205850848221208121430108c082302084406150509414 (by decide +kernel)

def state214_1 : List Sig := [0xffffffffffffffffcccccccccccccccc,input 7,input 6,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude214_1 : Impossible true (goalAt 214) 4 state214_1.toFinset :=
  node_ok cuts214 [] 0x908230208504224208504224208908214108848224208120621208848230208444221208444221208848211108d41430208c08225050504224208504224208444221208444221208161430208440630208c042 (by decide +kernel)

def state214_2 : List Sig := [0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,input 6,input 2,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude214_2 : Impossible true (goalAt 214) 5 state214_2.toFinset :=
  node_ok cuts214 [⟨state214_0,exclude214_0⟩,⟨state214_1,exclude214_1⟩] 0x941414108504230108928224a08941424a08928230108504214109000124a08928230208504230209000114108504230208928224a08161424200908040004928224a08161424a08908240004908024208941411108444230108868221a08941421a08868230108444211108160621a08868224a09000524a08160640004120624a08868221a08440621a08868230208444230208440611108444230208868221a08161421200848004840868221a08161421a08848204840848021208c04211018c04225050c08230208c04230208c08225050440625051000040000c0803010816143010894148000494143010a0000301089414058501614 (by decide +kernel)

def state214_3 : List Sig := [0xffffffffffffffff0000000000000000cccccccccccccccc,input 6,input 7,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude214_3 : Impossible true (goalAt 214) 4 state214_3.toFinset :=
  node_ok cuts214 [] 0x504224208908214108908214108504224208848224208120621208444221208848211108848211108444221208c04235050c04215050908214108908214108848211108848211108161430108840630108c082 (by decide +kernel)

def state214_4 : List Sig := [0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 7,input 2,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude214_4 : Impossible true (goalAt 214) 5 state214_4.toFinset :=
  node_ok cuts214 [⟨state214_0,exclude214_0⟩,⟨state214_3,exclude214_3⟩] 0xc04215050c04221018c08230208c04230208c08221018541415052000115050541405850c0823020a000030208c08205850541405850541424208908230208524230208541414908524230208908224209000114908524230108908224209000124208908230108524214908161414100504040004908224208161424208908240004504014108541421208848230208464230208541411908464230208848221208160621208848224209000524208160640004120624208848221208840611908464230108848221208840621208848230108464211908161411100444004840848221208161421208848204840444011109000040000c040 (by decide +kernel)

def state214_5 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0000000000000000,input 6,input 7,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude214_5 : Impossible true (goalAt 214) 4 state214_5.toFinset :=
  node_ok cuts214 [] 0x14908928224a08524224a08c28214908928224a08908024208908230908c04030108c04230a08c08030208c08230908c28230a08541421a08120624a08868221208848221a08848011908868221a08464221a08464230a088682 (by decide +kernel)

def state214_6 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,input 7,input 1,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude214_6 : Impossible true (goalAt 214) 5 state214_6.toFinset :=
  node_ok cuts214 [⟨state214_0,exclude214_0⟩,⟨state214_5,exclude214_5⟩] 0x524224a08928214908928230a08524224a08160624a08928205818868224a08120621a08464221a08868211908868230a08464221a0a000121a08868240008928224200908224208868221200848221208c24230100c04230108c28230200c08230208161440002000005850941430908c2824000c5414 (by decide +kernel)

def state214_7 : List Sig := roots 214
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude214_7 : Impossible true (goalAt 214) 6 state214_7.toFinset :=
  node_ok cuts214 [⟨state214_2,exclude214_2⟩,⟨state214_4,exclude214_4⟩,⟨state214_6,exclude214_6⟩] 0x40010c24215050c2424000c941430a08c28280008c24230a08c2824000c941415050541440004941414908524240004c24224a08928240004941424a08928240004c24214908524240004541424a08928240004c28214908c28240004541414908524240004c28224a08928240008941411908464240008c24221a08868240008941421a08868240008c24211908464240008541421a08868240008c28211908c28240008541411908464240008c28221a08868240008160621a08868240008928240008928240008160640004120640008928221a08868240000c24205850c24240000c04040000c04040000c24280004c04240000c04005850c04240000c28205850c28240000c08040000c08040000c28280000c08240000c08005850c082400009282400049282400009080058509080400009282058509082400009080400009082400008682048408682400008480058508480400008682058508482400008480048408482 (by decide +kernel)

theorem lower214 : Claim 214 7 :=
  fromSearch 570492480 (by decide +kernel) exclude214_7

theorem lower215 : Claim 215 8 :=
  fromLift 8 1 536872516 lower214 (by decide +kernel)

def rule182_0 : {c : Cut // CutGood (goalAt 182) c} :=
  ruleFor 182 lower180 none (by decide +kernel)

def rule182_1 : {c : Cut // CutGood (goalAt 182) c} :=
  ruleFor 182 lower164 none (by decide +kernel)

def rule182_2 : {c : Cut // CutGood (goalAt 182) c} :=
  ruleFor 182 lower178 none (by decide +kernel)

def rule182_3 : {c : Cut // CutGood (goalAt 182) c} :=
  ruleFor 182 lower150 none (by decide +kernel)

def cuts182 : Cuts (goalAt 182) := [rule182_0,rule182_1,rule182_2,rule182_3]

def state182_0 : List Sig := [0xffff0000ffff0000ffff0000ffff0000cccc0000cccc0000cccc0000cccc,0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 7,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude182_0 : Impossible true (goalAt 182) 4 state182_0.toFinset :=
  node_ok cuts182 [] 0x28088a0822820824140c8c0a08228208161421208a0820d0c084820d0c084822120834300d0c084822120832302c0c090820c888a0822420884820d0c084822420832222420890820c8890001 (by decide +kernel)

def state182_1 : List Sig := [0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 7,input 2,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude182_1 : Impossible true (goalAt 182) 5 state182_1.toFinset :=
  node_ok cuts182 [⟨state182_0,exclude182_0⟩] 0xa0220d050a02221018a08228208a02228208a0822101834140d05032300d050323005850a08228208323028208a0820585034140585034142420890822820832222820834140c88832222820890822420900010c88832222808890822420900012420890822808832220c88832308000032304000490822420832302420890824000500014000434142120884822820834302820834140d0c034302820884822120816062120884822420834302420816060d0c034302420884822120884060d0c034302808884822120884062120884822808834300d0c016140d0c034300c8c084822120816142120884820c8c034300c8c1000040000b030 (by decide +kernel)

def state182_2 : List Sig := [0xfffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0,input 2,input 5,input 1,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude182_2 : Impossible true (goalAt 182) 5 state182_2.toFinset :=
  node_ok cuts182 [] 0xb03024a089282280c092820c888322224a0892820c888322224a0832302c0c0a0220c8c092822420090822420816140c8c032300585032300d0c024220c8c012100c8c0323004840b03025050b0300d050a2820d0c0b0302505034300988892820d0c092820d05034304000886822c0c090102c0c09010 (by decide +kernel)

def state182_3 : List Sig := [0xffffffff00000000ffffffff00000000f0f0f0f000000000f0f0f0f0,input 2,input 7,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude182_3 : Impossible true (goalAt 182) 4 state182_3.toFinset :=
  node_ok cuts182 [] 0x2c0c0928224a08a03024a0890802420890820c8c0b03028088323021a08848021208848221a0892820d0c086820d0c0868221a08343024a08322224a08a28228208a08228a08a080240c0a28228a08b03021a08343021a08a282 (by decide +kernel)

def state182_4 : List Sig := [0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 2,input 7,input 1,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude182_4 : Impossible true (goalAt 182) 5 state182_4.toFinset :=
  node_ok cuts182 [⟨state182_3,exclude182_3⟩] 0x341428a08a2820d052000028a08a2824000c928228a08322224a08322224a0892820c888322224a0892820c888a28228200a0822820892822420090822420832302505084060c8c086822120084822120832300585016140c8c0b03021a08a2820d050868221a089282058188682250508682240503430 (by decide +kernel)

def state182_5 : List Sig := [0xcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcccccccccccccccccccccccccccccccc,input 2,input 7,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude182_5 : Impossible true (goalAt 182) 4 state182_5.toFinset :=
  node_ok cuts182 [] 0x28088a08228208341424208a0820c88890820c888908224208322221a08a0820d0c0868221a0890820d0c086820d0c0868221a0834302820832302820816142420832302420900010c8c0b03028088323021a083430212088482 (by decide +kernel)

def state182_6 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000000000000000000,input 2,input 7,input 1,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude182_6 : Impossible true (goalAt 182) 5 state182_6.toFinset :=
  node_ok cuts182 [⟨state182_5,exclude182_5⟩] 0x341428a08a2820d050928228a08322224a08322224a0892820c888a28228200a0822820892822420090822420832302505084060c8c032300d0c024220c8c0341428a08343028a08262224a08343024a08b43025050343028a08341428a08341424a08322224a0832224000032308000032302c0c08682 (by decide +kernel)

def state182_7 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f00000000,input 5,input 7,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude182_7 : Impossible true (goalAt 182) 4 state182_7.toFinset :=
  node_ok cuts182 [] 0x2c0c0928224a08a03024a08a2820c888928224a0890802420890820c8c0b03028088323028a08a08028208a0822c0c0a28228a08903021a08343024a08868221208848221a0884800d0c0868221a08343021a08343028a088682 (by decide +kernel)

def state182_8 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,input 7,input 1,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude182_8 : Impossible true (goalAt 182) 5 state182_8.toFinset :=
  node_ok cuts182 [⟨state182_7,exclude182_7⟩] 0xb03024a089282280c0928228a08322224a08160624a08928205818868224a08343021a08343021a0886820d0c0868228a08343021a0a000021a0886824000892822420090822420886822120084822120832302c0c0a0220c8c0a28228200a0822820816140c8c032300585094142c0c0a282240c03414 (by decide +kernel)

def state182_9 : List Sig := [0xccccccccffffffffccccccccffffffffcccccccccccccccccccccccccccccccc,input 5,input 7,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude182_9 : Impossible true (goalAt 182) 4 state182_9.toFinset :=
  node_ok cuts182 [] 0x2c0c0908224208a03024208a2820c88890822120890820d0c084820d0c0848221208343021208a2820d0c084822c0c0a28228a0834142420832302420900012120834302120832300c8c0b03028088323028a08323028208a082 (by decide +kernel)

def state182_10 : List Sig := [0xffffffff00000000ffffffff00000000000000000000000000000000,input 5,input 7,input 1,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude182_10 : Impossible true (goalAt 182) 5 state182_10.toFinset :=
  node_ok cuts182 [⟨state182_9,exclude182_9⟩] 0xb03024a089282280c092820c888322224a08868224a08343021a08343021a0886820d0c086820d0c0343021a0892822420090822420886822120084822120832302c0c0a0220c8c016140c8c0323005850b4142c0c0341424a08322224a08322221a08343021a08343040000323080000323025050a282 (by decide +kernel)

def state182_11 : List Sig := roots 182
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude182_11 : Impossible true (goalAt 182) 6 state182_11.toFinset :=
  node_ok cuts182 [⟨state182_1,exclude182_1⟩,⟨state182_2,exclude182_2⟩,⟨state182_4,exclude182_4⟩,⟨state182_6,exclude182_6⟩,⟨state182_8,exclude182_8⟩,⟨state182_10,exclude182_10⟩] 0x80014b0300d050b0304000c941428a08a28280010b03028a08a2824000c94140d050903040004b0300c888b03040004a22224a08928240004b03024a08928240004a2220c888a03040004341424a08928240004a2820c888a2824000434140c888322240004a28224a0892828000c94140d0c0343040008b03021a08868280008941421a08868240008b0300d0c034304000c341421a08868240008a2820d0c0a2828000434140d0c0343040008a28221a08868240004160621a0886824000892820d0c092824000416060d0c0343040008928221a08868240000a2220c8c0323040000b03040000b03040000a22280000a02240000b0300c8c0323040000a28205850a28240000a0800c8c0a08040000a2820c8c0a08240000a08005850a0824000092824000492824000090800c8c090804000092820c8c090824000090804000090824000086820c8c086824000084800585084804000086820585084824000084800c8c08482 (by decide +kernel)

theorem lower182 : Claim 182 7 :=
  fromSearch 539034944 (by decide +kernel) exclude182_11

theorem lower183 : Claim 183 8 :=
  fromLift 8 1 536872260 lower182 (by decide +kernel)

theorem lower181 : Claim 181 6 :=
  fromLift 6 1 536872196 lower180 (by decide +kernel)

theorem lower209 : Claim 209 5 :=
  fromLift 5 1 1073741828 lower208 (by decide +kernel)

def rule213_0 : {c : Cut // CutGood (goalAt 213) c} :=
  ruleFor 213 lower209 none (by decide +kernel)

def rule213_1 : {c : Cut // CutGood (goalAt 213) c} :=
  ruleFor 213 lower197 none (by decide +kernel)

def rule213_2 : {c : Cut // CutGood (goalAt 213) c} :=
  ruleFor 213 lower212 none (by decide +kernel)

def rule213_3 : {c : Cut // CutGood (goalAt 213) c} :=
  ruleFor 213 lower85 none (by decide +kernel)

def cuts213 : Cuts (goalAt 213) := [rule213_0,rule213_1,rule213_2,rule213_3]

def state213_0 : List Sig := roots 213
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude213_0 : Impossible true (goalAt 213) 6 state213_0.toFinset :=
  node_ok cuts213 [] 0x4000cc04015050c0404000c941430604c1814000cc04030604c1814000c941415050418140004941414100504040004c04024604918140004941424604918140004c04014100504040004541424604918140004c18114100c18140004541414100504040004c18124604918140000941411100444040000c04021604858140000941421604858140000c04011100444040000541421604858140000c18111100c18140000541411100444040000c18121604858140000150521604858140000918140000918140000150540004110540000918121604858140008850510500414040008c04040008c0404000885054000c840540008c04010500414040008c18105450c18140008c08010500c08040008c18110500c08140008c08005450c081400049181105009181400049080054509080400049181054509081400049080105009081400008581105008581400008480054508480400008581054508481400008480105008481 (by decide +kernel)

theorem lower213 : Claim 213 7 :=
  fromSearch 536872452 (by decide +kernel) exclude213_0

theorem lower241 : Claim 241 6 :=
  fromLift 6 1 1073741828 lower240 (by decide +kernel)

def cuts149 : Cuts (goalAt 149) := []

def state149_0 : List Sig := roots 149
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude149_0 : Impossible true (goalAt 149) 3 state149_0.toFinset :=
  node_ok cuts149 [] 0x250509181246048414250508581216049014216049181044148581054509414210141514246049080242049081216048480212048481 (by decide +kernel)

theorem lower149 : Claim 149 4 :=
  fromSearch 536872708 (by decide +kernel) exclude149_0

theorem lower211 : Claim 211 6 :=
  fromLift 6 1 1073741892 lower210 (by decide +kernel)

theorem lower151 : Claim 151 5 :=
  fromLift 5 1 536872772 lower150 (by decide +kernel)

theorem lower179 : Claim 179 5 :=
  fromLift 5 1 1073741892 lower178 (by decide +kernel)

def rule247_0 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower245 none (by decide +kernel)

def rule247_1 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower246 none (by decide +kernel)

def rule247_2 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower119 none (by decide +kernel)

def rule247_3 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower229 none (by decide +kernel)

def rule247_4 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower243 none (by decide +kernel)

def rule247_5 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower215 none (by decide +kernel)

def rule247_6 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower183 none (by decide +kernel)

def rule247_7 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower117 none (by decide +kernel)

def rule247_8 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower119 (some (1,input 1,input 6)) (by decide +kernel)

def rule247_9 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower181 none (by decide +kernel)

def rule247_10 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower244 none (by decide +kernel)

def rule247_11 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower243 (some (1,input 1,input 6)) (by decide +kernel)

def rule247_12 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower213 none (by decide +kernel)

def rule247_13 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower115 (some (1,input 1,input 6)) (by decide +kernel)

def rule247_14 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower241 none (by decide +kernel)

def rule247_15 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower165 none (by decide +kernel)

def rule247_16 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower180 none (by decide +kernel)

def rule247_17 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower209 none (by decide +kernel)

def rule247_18 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower183 (some (1,input 2,input 5)) (by decide +kernel)

def rule247_19 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower81 none (by decide +kernel)

def rule247_20 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower208 none (by decide +kernel)

def rule247_21 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower229 (some (1,input 2,input 5)) (by decide +kernel)

def rule247_22 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower197 none (by decide +kernel)

def rule247_23 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower149 none (by decide +kernel)

def rule247_24 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower85 none (by decide +kernel)

def rule247_25 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower211 none (by decide +kernel)

def rule247_26 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower115 none (by decide +kernel)

def rule247_27 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower214 none (by decide +kernel)

def rule247_28 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower83 none (by decide +kernel)

def rule247_29 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower151 none (by decide +kernel)

def rule247_30 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower179 none (by decide +kernel)

def rule247_31 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower210 none (by decide +kernel)

def rule247_32 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower242 none (by decide +kernel)

def rule247_33 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower229 (some (1,input 2,input 6)) (by decide +kernel)

def rule247_34 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower182 none (by decide +kernel)

def rule247_35 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower245 (some (1,input 2,input 6)) (by decide +kernel)

def rule247_36 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower87 none (by decide +kernel)

def rule247_37 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower119 (some (1,input 5,input 6)) (by decide +kernel)

def rule247_38 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower229 (some (1,input 5,input 6)) (by decide +kernel)

def cuts247 : Cuts (goalAt 247) := [rule247_0,rule247_1,rule247_2,rule247_3,rule247_4,rule247_5,rule247_6,rule247_7,rule247_8,rule247_9,rule247_10,rule247_11,rule247_12,rule247_13,rule247_14,rule247_15,rule247_16,rule247_17,rule247_18,rule247_19,rule247_20,rule247_21,rule247_22,rule247_23,rule247_24,rule247_25,rule247_26,rule247_27,rule247_28,rule247_29,rule247_30,rule247_31,rule247_32,rule247_33,rule247_34,rule247_35,rule247_36,rule247_37,rule247_38]

def state247_0 : List Sig := [0xfffffffffffffffffffffffffcfcfcfcfffffffffffffffffffffffffcfcfcfc,input 5,input 2,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,input 6,input 0,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_0 : Impossible true (goalAt 247) 7 state247_0.toFinset :=
  node_ok cuts247 [] 0x504224e0c93831410893833060c504224e0c918124e0c938324604938328e0c322224e0c918124e0c938324604434230108860710d08938324a08928324a0cc18330208c0833020c313010d0843420c4c0878321a08868321a0ca38328a08a28328a0c111010d08434204440c0423060cc18310e0c703040044c0422c0c0c0420c8c0121011108878321e0c444221e0c93830d0c0878321e0cc1831110887830d0c087832160c858321e0ca3830d0c0878321604604228e0ca38318108a3833060c604228e0c323028e0ca1832860ca181301089010301089010 (by decide +kernel)

def state247_1 : List Sig := [0xffffffff00000000fcfcfcfc00000000ffffffff00000000fcfcfcfc,input 5,input 2,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,input 6,input 0,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_1 : Impossible true (goalAt 247) 7 state247_1.toFinset :=
  node_ok cuts247 [] 0x14108938324e0c504224e0cc18314108938324604938324e0c918124e0ca1810c888938310d08c0422181c434224e0c928224a0c92833060cc0823020cc0830c4c0434210d08313021e0c868221a0c868328604a08028204a08130108c1833060c43831c0c0c0422c0c0c0420c8c0444221e0c878311108878324e0c343021e0c87833060c444221e0c343021e0c85832160c878328604343021e0cb03028604a18130108a1813060c60223060ca18128e04323028604c0422c0c0c0422c0c093832460493832460443420c4c043420c4c0c18318088c1831808816140c8c016140c8c087832160487830d0c0a383 (by decide +kernel)

def state247_2 : List Sig := [0xffffffffffffffffffffffffccccccccffffffffffffffffffffffffcccccccc,input 5,0xfffffffffffffffffcfcfcfcfcfcfcfcfffffffffffffffffcfcfcfcfcfcfcfc,input 2,input 6,input 0,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_2 : Impossible true (goalAt 247) 7 state247_2.toFinset :=
  node_ok cuts247 [] 0x14108938324e0c504224e0cc18314108938324604938324e0c918124e0ca3830c888938324604938324e0c918110d08c0422181c434224e0c928224a0c92833060cc0823020cc08321e0c868221a0c86830c4c0434210d08313028e0ca28228a0ca28305450434210d08151430108c1833060c43831c0c0541411108878321e0c444221e0c938304c1c878321e0cc18311108878321604878328e0c242221e0c161421e0c85832160cc0422c0c0c0420c8c016140c8c0323040030604228e0ca38318108a3833060c604228e0c323028e0ca1832860ca181301089414301081614 (by decide +kernel)

def state247_3 : List Sig := [0xfffffffffffffffffcfcfcfcfcfcfcfcfffffffffffffffffcfcfcfcfcfcfcfc,input 2,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,input 6,input 0,input 4,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_3 : Impossible true (goalAt 247) 8 state247_3.toFinset :=
  node_ok cuts247 [⟨state247_0,exclude247_0⟩,⟨state247_1,exclude247_1⟩,⟨state247_2,exclude247_2⟩] 0xb03018108604230108a38328e0cb03028e0ca38330108604218108602228e0ca3833060c60423060c60221810860423060ca38328e0d000928604a18105850a38328e0e000228e0ca38305850a18128606000128604a18140030a38328e0e000028e0ca38340030a18128604b03014108504230108938324e0cb03024e0c938330108504214108341424e0c938328e0c322228e0c34140c888322228e0c938324e0d000924e0c93833060c50423060d000f1410850423060c938324e0c16142460491814003c938324e0c161424e0c938340024918124605000f2460491814000c938324e0d000f24e0c93834000c918124604870710d08434230109001030108870740034860730108434210d08a38310d08a38328a08313028a08a3830c4c0a28328a08434228a0c938310d08938324a08313024a0893830c4c0928324a08434224a0cc1830c4c0c18330208434230208c18310d08c0833020831303020d00090c4c0313005850434210d09001010d0843420585031300c4c0878310d08878321a08151421a08878305450868321a08434221a0d00100c4c0313040028434210d09001010d0843424002831300c4c0c04218088c0422c0c0c1833060cc0423060cc1832c0c0602210e0d000e40038541440039000e40038c04205850c0422c0c100092c0c0c04240034c0422c0c016142c0c1000e40038323025050444211108c04221e0c878325050878321e0cc0421110844420d050878321e0ca38309888a3830d050262209888a38321e0c878305c1c878321e0c93834003c938305c1d000f04c1c938321e0c87831141c878321e0cc18311108c1831141c444211108c18321e0c878305851000905851000e21e0c87834003900092160d000940024858130109000730108b03040034b03030109000d30108b0304001cb030 (by decide +kernel)

def state247_4 : List Sig := [0xfffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0,input 2,input 5,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,input 6,input 0,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_4 : Impossible true (goalAt 247) 8 state247_4.toFinset :=
  node_ok cuts247 [⟨state247_0,exclude247_0⟩] 0x2c0c0504214108c04224e0c93832c0c0938324e0cc04214108504240048938324e0cc18314108c18340054504214108c18324e0c93830c8c0918124605001624e0c93830c8c093832460d00162460491830d050938324e0c27070c88832220d05032220c888270724e0c938340044938324e0d00030c88832224005432220c889000324e0c938321c1c434210d08c0424004cc04221c1d00132181cc04210d08434224e0c434224e0c92820c4c0928224e0c313024a0c928210d0892833060c31303060cc08210d08c0823060c43423020cc0820c4c0c0834005031300c4c0323010d08434240050434210d0832300c4c0313009c1c434210d0834140c4c0313009c1c31300c4c0341410d08434240044434210d08343005450343040050151405450343010d08434240044434210d09000a0c4c031304005031300c4c1000a10d08434230108602230108b0303060cc18330108c1833060cb03018088438340031000c30604c0420c8c0c0422c0c100132c0c0c0424004cc0422c0c032300c8c0b0300d050b03030109000c30108b0304004cb0303010834143010860220d05060223060d000c3060c60224004860223060c34143060c32300d050323005850270705850323009c1c323005850341405851000c40038a3832505034300d0c0c04240044c04225051001325050c0420d0c0c04205c1c26220988893830d0c0938305c1c34300d0c093830988893831141c34300d0c0c18340044c1831141d00121141cc1830d0c0c1830585034300d0c032300988832300585026220908832300d0c032300d051000c0d051000e0d0c0343040031000c08c1d000c4003087832c0c100072c0c0c04240044c0422c0c100132c0c0c0424001cc04218089000618088c18340044c18318089001218088c18340018c1830c8c100090c8c012104004412100c8c200000c8c01210400241210 (by decide +kernel)

def state247_5 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0c0c0c0c,input 7,input 5,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,input 6,input 0,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_5 : Impossible true (goalAt 247) 6 state247_5.toFinset :=
  node_ok cuts247 [] 0x93833060c504224e0c918124e0c91832460c938328e0c322224e0c504224e0c938314108938324a08928324a0cc18330208c0833020c313010d0843420c4c0a38328a08a28328a0c434230108860710d08c18130108c1833060c438330108b03030108323028e0cc18318108a38328604a3832860ca18318108a38328e0c604221e0c343024e0c878321a0c868321e0c868221e0c44423060c87832160c858321e0c858121e0c343028e0c878311108878321e0c4442 (by decide +kernel)

def state247_6 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffcccccccc,input 7,input 5,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,input 6,input 0,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_6 : Impossible true (goalAt 247) 7 state247_6.toFinset :=
  node_ok cuts247 [⟨state247_5,exclude247_5⟩] 0x93833060c504224e0c918124e0c91832460c938328e0c322224e0c504224e0c938314108150524e0c938305414878324e0c343021e0c87833060c444221e0c858121e0c85832160c878328e0c343021e0c444221e0c87831110a000021e0c878340038938324a08928324a0c878321a08868321a0cc18330208c0833020c313010d0843420c4c0a38328a08a28328a0c434230108860710d08151410d08434205450c18130108c1833060c438340060c0422c0c0c0420c8c0161428e0cc18318108a38328604a3832860ca18318108a38328e0c60420d0509414 (by decide +kernel)

def state247_7 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffffcccccccccccccccc,input 7,0xffffffffffffffffffffffffccccccccffffffffffffffffffffffffcccccccc,input 5,input 6,input 0,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_7 : Impossible true (goalAt 247) 7 state247_7.toFinset :=
  node_ok cuts247 [] 0x24e0cc18314108938324e0ca1830c88893832460493832460c918314108938324e0c50420c8c0938324e0c150521e0c93830d0c0878321e0cc18311108878321e0ca1830d0c087832160487832160c858311108878321e0c44420d0c0878321e0c323024e0c928224a0c928321e0c868221a0c86833060cc0823020cc0832860ca0822820ca08305450434210d08151410d08c0422181c43420c4c0434210d08313030604c0423060cc18310e0c70302860cc18318108a1832860460422860ca1831810832302860ca183048c0c0424005cc0422141c32300585032304001cb030 (by decide +kernel)

def state247_8 : List Sig := [0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 7,0xffffffffffffffffffffffffccccccccffffffffffffffffffffffffcccccccc,input 5,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,input 6,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_8 : Impossible true (goalAt 247) 7 state247_8.toFinset :=
  node_ok cuts247 [] 0x24a0cc08314108928324204928324a0c908124a0ca2830c888928324204928324a0c908114108928324a0c504214108928324a0c434221a0c92830d0c0868321a0cc08311108868321204868321a0c848121a0ca2830d0c0868321204868321a0c848111108868321a0c444211108868321a0c43421c0c1001818088c0833020c438210d08c0833020c31300585032302101486070c8c043420c4c043420c4c0a2833020c604228a0c323028a0ca08328204604228a0ca28318108604228a0ca28310d08860721014860721014434205450434205450c042 (by decide +kernel)

def state247_9 : List Sig := [0xffffffffffffffffffffffffccccccccffffffffffffffffffffffffcccccccc,input 5,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,input 6,input 0,input 2,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_9 : Impossible true (goalAt 247) 8 state247_9.toFinset :=
  node_ok cuts247 [⟨state247_0,exclude247_0⟩,⟨state247_2,exclude247_2⟩,⟨state247_6,exclude247_6⟩,⟨state247_7,exclude247_7⟩,⟨state247_8,exclude247_8⟩] 0xb03014108504230108938324e0cb03024e0c938330108504214109000924e0c93833060c50423060d000f1410850423060c938324e0c32302460491814003c938324e0c323024e0c938340024918124605000c24e0c938328e0c322228e0d000f0c888322228e0c938324e0d000f2460491814000c938324e0d000f24e0c93834000c918124604941411108444230108878321e0c941421e0c878330108444211108170721e0c878324e0c343024e0c17070d0c0343024e0c878321e0c450721e0c87833060c44423060c45071110844423060c878321e0d00092160485810c8c0878321e0e000121e0c87830c8c0858121604270721e0c878328e0c343028e0c27070d0c0343028e0c878321e0d001721604858140038878321e0e000021e0c878340038858121604870710d08434230109001030108870780010860730108434210d08938310d08938324a08313024a0893830c4c0928324a08434224a0c878310d08878321a08151421a08878305450868321a08434221a0cc1830c4c0c18330208434230208c18310d08c0833020831303020d00090c4c031300c8c0434210d09001010d0843420c8c031300c4c0a38310d08a38328a08313028a08a3830c4c0a28328a08434228a0d001005450151440028434210d09001010d08434240028151405450c04218088c0422c0c0c1833060cc0423060cc1832c0c0602210e0d000c40030703040031000c40030c0420c8c0c0422c0c100092c0c0c0428000cc0422c0c032300c8c1000c4003016142c0c0604218108c04228e0ca3832c0c0a38328e0cc04218108604218088a38328e0cc18318108c18318088604218108c18328e0ca3830c8c100090c8c1000c28e0ca38340031000c2860d000c40024a1813010900073010894144005c94143010a00023010894144001c9414 (by decide +kernel)

def state247_10 : List Sig := [0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,input 6,input 0,input 2,input 4,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_10 : Impossible true (goalAt 247) 9 state247_10.toFinset :=
  node_ok cuts247 [⟨state247_3,exclude247_3⟩,⟨state247_4,exclude247_4⟩,⟨state247_9,exclude247_9⟩] 0x4001cb03018108604240030c04228e0ca38340020b03028e0ca3834001cc04218108604240018602228e0ca38340018c18318108c18340018602218108604240018c18328e0ca38340024323028604a18140030161428e0ca38380008323028e0ca18340030161428604a1834000cb0301410850424000cc04224e0c93834000cb03024e0c93834000cc0421410850424000c341424e0c93834000ca3830c888a3834000c34140c88832224000ca38324e0c938340019000624e0c938340018c18314108c18340019000314108504240018c18324e0c93834000c32302460491814000d000324e0c93834000c323024e0c91834000d00032460491834001c941411108444240020c04221e0c878340020941421e0c87834001cc04211108444240030341421e0c87834002ca3830d0c0a3838000434140d0c0343040030a38321e0c87834000c170721e0c87834000c93830d0c093834000c17070d0c034304000c938321e0c878340018450721e0c878340018c18311108c18340018450711108444240018c18321e0c87834002416142160485814002c323021e0c878380000161421e0c858340024323021604858340028870710d08434240028c04240028c04240028870740020860740028c04210d08434240028a38310d08a38340028a2820c4c0a28240028a3830c4c0a28340028a28210d08a28340028938310d0893834002892820c4c092824002893830c4c0928340028928210d08928340028878310d08878340028868205450868240028878305450868340028868210d08868340028c1830c4c0c18340028c08210d08c08240028c18310d08c08340028c0820c4c0c08340029000a0c4c0313040028323010d08434240029000a10d0843424002832300c4c0313040018c04218088c04240018b0303060cc18340018c0423060cc18340018b03018088438340001000040000c1814001cc0420c8c0c04240024b03040020b03040020c04240020c0424001cb0300c8c03230 (by decide +kernel)

def state247_11 : List Sig := [0x3333000033330000333300003333000033330000333300003333000033330000,input 4,0xfffffffffffffffffffffffff0f0f0f0fffffffffffffffffffffffff0f0f0f0,input 6,input 2,input 5,input 0,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_11 : Impossible true (goalAt 247) 7 state247_11.toFinset :=
  node_ok cuts247 [] 0x10d08c0422101c434210d0860420c4c0434210d0844420545043420c4c0434210d08313004440434210d08111024e0c928224a0c928318108c0422c0c060421c0c060421810850302860c44423010894141110844421810834301110834301110844420d0c085831110893830d0c0938330108b0303010870303060cc04224040c04224040524224e0c938314908938318108322224e0c938314908524224e0c938314908524224e0c323030108b03030108313010d08313010d0816141810832301810832301110834301110832301808870300c8c012100c8c03230048409183 (by decide +kernel)

def state247_12 : List Sig := [0xfffffffffffffffffffffffffffff0f0,input 4,input 6,input 2,input 5,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_12 : Impossible true (goalAt 247) 6 state247_12.toFinset :=
  node_ok cuts247 [] 0x28e0ca1812860ca18321e0c85812160c858330e0cc1813060cc18324e0c91812460c918310500434210d08414228e0ca28228a0ca28321e0c868221a0c868330e0cc28230a0cc28324e0c928224a0c928328e0cc38318908a38321e0ca3830d0c0878321e0cc38311908878321e0c93830d0c0878324e0ca3830c888938324e0cc38314908938330108c04230908c04010d08860710d08c24218908a38318908a38311908878311908878310e0cc38330908c383149089383149089383 (by decide +kernel)

def state247_13 : List Sig := [0x5555555555555555555555555555505055555555555555555555555555555050,input 4,input 6,input 2,input 5,input 1,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_13 : Impossible true (goalAt 247) 6 state247_13.toFinset :=
  node_ok cuts247 [] 0x30908c04030108c04228e0ca1812860ca18321e0c85812160c858330e0cc1813060cc18324e0c91812460c918318908a38328e0c624228e0cc38318908a38311908878321e0c464221e0ca3830d0c0878321e0cc38311908878321e0c93830d0c0878330908c38330e0c438214908938324e0c524224e0ca3830c888938324e0cc38314908938310d08860730908434210508434210d08414028a0ca28318908a38321a0c868311908878330a0cc28310d08c38324a0c9283149089383 (by decide +kernel)

def state247_14 : List Sig := [0x3333333333333333333333333333303033333333333333333333333333333030,input 4,input 6,input 2,input 5,input 0,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_14 : Impossible true (goalAt 247) 6 state247_14.toFinset :=
  node_ok cuts247 [] 0x10d08c2422181c434228e0ca28228a0ca28321e0c868221a0c868330e0cc28230a0cc28324e0c928224a0c928318908a38328e0c624228e0cc38318908a38311908878321e0c464221e0ca3830d0c0878321e0cc38311908878321e0c93830d0c0878330908c38330e0c438114908938324e0c524224e0ca3830c888938324e0cc38314908938330108c04230100c2421050843421050043422860ca18318100a3832160c85831110087833060cc1831c0c0c3832460c9183141009383 (by decide +kernel)

def state247_15 : List Sig := [0xfffffffffffffffffffffffffffff0f0fffffffffffffffffffffffffffff0f0,input 4,input 6,input 2,input 5,input 0,input 1,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_15 : Impossible true (goalAt 247) 7 state247_15.toFinset :=
  node_ok cuts247 [⟨state247_12,exclude247_12⟩,⟨state247_13,exclude247_13⟩,⟨state247_14,exclude247_14⟩] 0x30908c04030108c0421890860401810860421190844401110844420c8c070301808832301490850401410850428000832300c8c1000010d08c2422181c434210500434210d08414210d0862420c4c0434210d0846420545043420c4c0434210d08313010d0852420c4c0434280004434210d09000118908c242240c062421c0c0624218908503028e0c46423090890141190846421890834301190834301190846420d0c0464214908343011908878330908b03030908703030e0c524230908a030149085242189083222149087030149085242180c093833090a0000309090002 (by decide +kernel)

def state247_16 : List Sig := [0xccccffffccccffffccccffffccccfcfcccccffffccccffffccccffffccccfcfc,input 4,input 6,input 2,input 5,input 0,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_16 : Impossible true (goalAt 247) 6 state247_16.toFinset :=
  node_ok cuts247 [] 0x10d08c0422101c43422860ca0822820ca0832160c84822120c84833060cc0823020cc08324e0c928224a0c92830c4c0434210d08313018108a1832860c60422860cc18318108a1831110885832160c44422160ca1830d0c085832160cc1831110885832160c93830d0c0858330108c1833060c438314908938324e0c524224e0ca1830c888938324e0cc18314908938330108b0303010832302860ca1812860c16142160c85812160c32303060cc1813060c323024e0c91812460c9183 (by decide +kernel)

def state247_17 : List Sig := [0xffff0000ffff0000ffff0000f0f00000ffff0000ffff0000ffff0000f0f0,input 4,input 6,input 2,input 5,input 0,input 1,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_17 : Impossible true (goalAt 247) 7 state247_17.toFinset :=
  node_ok cuts247 [⟨state247_16,exclude247_16⟩] 0xc24230100c0423010862421810060421810846421110044421110832301c0c060220c8c093832460491832460c434230908860710d08414010d08434210508434218908313010d08434211908151410d08313010d0843420c4c0938324a08928324a0c6242309089030189087030189086242140c046423090890141190846421890834301190834301190846420d0c0978324e0c343024e0cc2422c0c0c2421c0c0b03024e0c93833090893832ce0c341424e0c938334e0c703024e0cc2422c0c0c2422c0c100000c8c200000c8c043420c4c043420c4c0a38328e0c62420d050878321e0c46420d0c0c38330e0c62221c0c05242 (by decide +kernel)

def state247_18 : List Sig := [0xfffffffffffffffffffffffff0f0f0f0fffffffffffffffffffffffff0f0f0f0,input 6,input 2,input 5,input 0,input 1,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_18 : Impossible true (goalAt 247) 8 state247_18.toFinset :=
  node_ok cuts247 [⟨state247_11,exclude247_11⟩,⟨state247_15,exclude247_15⟩,⟨state247_17,exclude247_17⟩] 0xb03014908524230908938324e0cb03024e0c938330908524214908341424e0c93831890832221890834140c888322218908938324e0c703024e0c938318888524214908703014908524218888938324e0e000224e0c93834000c52421490a00011490852424000c938324e0cc2420c8c0c24230101001c30100c24240070c0423010032303010893838000093832460432302460493830c8c091832460500112460c62420585062421810032301810062420c8c060421810016141810846420c8c046421110016141110046420585044421110032301110862220c8c032301c0c100111c0c062224004860221c0c032300c8c100110484012104000032300c8c100110c8c0323040000121004840870710d08434230909001c30908870740070860730908434210d08938310d08938324a08313024a0893830c4c0928324a08434224a0d001f1050041400c8c0434210d09001f10d0843420c8c0414010508270710d0843421890831301890827070c4c0313018908434210d09001910d08434211908151411909001f05450151411908434210d0847070c4c031301c0c0434210d08470710d0843421c0c031300c4c1001f04440111040004434210d09001f10d08434240004111004440b03018908624230909001930908b03040070b0303090862421890870300d0507030150506242189087030189086242150503414140c1001940078a38325050464211908c24240064c24225051001c25050c24211908464205c1c46421190893830d0c0938305c1c34300d0c093831190893830d05046421190862420d0c062420d05034300d0c062421190846421505034300d0c070301190846421505046421190870300d0c0343040065001d21e0cc2421c0c0c2422c0c1001c2c0c0c24240070c2422c0c070301c0c1001940064c38330909000230908901040070901030909001c309089010400089010 (by decide +kernel)

def state247_19 : List Sig := [0x3333000033330000333300003333000033330000333300003333000033330000,input 4,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0,0xfffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0,input 0,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_19 : Impossible true (goalAt 247) 6 state247_19.toFinset :=
  node_ok cuts247 [] 0x434230108840710d08434211108313010d08313010d0843420c4c0151410d08434205450938324a08928324a0c444229108b0301110885832160c4442140c0a1832860c444214050c0422c0c0c0420d0c0c1833060c34300841cc04225050c0420d050524224e0c938314908938311108322224e0c938314908524224e0c938314908524224e0c323030108b03030108313010d08313010d0812101110832301110832300908834300c8c016140c8c03230058509183 (by decide +kernel)

def state247_20 : List Sig := [0xfffffffffffff0f0fffffffffffff0f0fffffffffffff0f0fffffffffffff0f0,input 4,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0,input 0,input 1,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_20 : Impossible true (goalAt 247) 6 state247_20.toFinset :=
  node_ok cuts247 [] 0xc24230100c0423010832300d0c024220c8c016140c8c032300585032220c8c032300541c464211100444211108434230908860710d08414010d08434210508313010d0843420c4c0151410d0843420545043420c4c0313010d08434211908313010d08c2422c0c0c2420d0c0c38330e0c343008c1cc24225050c242240c0b03030908a030309083430098883430110c034140c888322209050938311908a6422c0c0464221e0c878311909000628e0ca383119084307 (by decide +kernel)

def state247_21 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0,0xfffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0,input 0,input 1,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_21 : Impossible true (goalAt 247) 7 state247_21.toFinset :=
  node_ok cuts247 [⟨state247_19,exclude247_19⟩,⟨state247_20,exclude247_20⟩] 0x2c0c0524214908c24224e0c93832c0c0938324e0cc24214908524240064938324e0c46420c88846428000432220c888464224e0c93830d0c0938324e0c26221490852420d0c0524214908262224e0c93830d050938324e0c27071490852420d050524214908270724e0c938330908323030908c04040070c04030909001c30108c0400c8c0c04224e0e000024e0c91810c8c0918124e0c32302460c91814004491831190812101190844400c8c044401190832301110844400484044420988832300c8c034300585034300988816140908834300c8c0323009c1c16140585034140c8c0323009c1c32300c8c0341405850161421c1c434210d08c24240070c24221c1d001c2181cc24210d08434224e0c434224e0c92820c4c0928224e0c313024a0c928210d0892834007c414010500323010d0843424007c434210d08323010500414240064434210d0846420c4c046424007c31300c4c0464210d0843424007c31300c4c0343010d0843424007c434210d0834300c4c0313009c1c151405450341410d08434209c1c434210d0834140545015142c0c0464211908c24240064a6422c0c1001c2c0c0c2421190846420d0c1000621e0d00051190887830d0c046421190900054001850300d051000628e0d000411908a3830d050464211909000440018501430908343030908b03040070b03030909001c30908b0300d0c034300d051000530e0d00040d0c0c3830d05034300d0c1000440014230730908341430908941440070941430909001c3090894140d0503414 (by decide +kernel)

def state247_22 : List Sig := [0x3333000033330000333300003333000033330000333300003333000033330000,input 4,0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0,input 6,0xfffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0,input 5,input 0,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_22 : Impossible true (goalAt 247) 7 state247_22.toFinset :=
  node_ok cuts247 [⟨state247_19,exclude247_19⟩] 0x434230108840710d0843420c4c0313010d08434211108313010d08313010d0843420c4c0313010d0843420c4c0938324a08928324a0cb03030108b03030108a1830d05054148000034140d0c034140d0c0210711108c0422c0c044421505044421110850142160c858311109000c30108b03030108b0303060cc0422c0c0c0420d0c0524224e0c93831490893830c888322224e0c938311108322224e0c938314908524224e0c938314908524224e0c323030108b03030108313010d08313010d0816140c8c032300585012101110832301110832301141c54140c8c032300908834300c8c09183 (by decide +kernel)

def state247_23 : List Sig := [0xfffffffffffff0f0fffffffffffff0f0fffffffffffff0f0fffffffffffff0f0,input 4,0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0,input 6,input 5,input 0,input 1,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_23 : Impossible true (goalAt 247) 7 state247_23.toFinset :=
  node_ok cuts247 [⟨state247_20,exclude247_20⟩] 0xc24230100c0423010816140c8c032300585032301405045070c8c032300d0c024220c8c032220c8c032300541c464211100444211108434230908860710d08414010d0843421050843420c4c0313010d08313010d0843420c4c0313010d0843420c4c043420c4c0313010d08434211908313010d08b0303090890303090834141405200000d05034300d050343008c1ca38330908b03030908b03030e0cc2422c0c0c2420d0c0b03030908a0303090834140c888322209050322211c1c44140c8883430098883430090c0938311908c2422c0c0464214050464211908430721e0c8783119090006 (by decide +kernel)

def state247_24 : List Sig := [0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0,input 6,0xfffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0,input 5,input 0,input 1,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_24 : Impossible true (goalAt 247) 8 state247_24.toFinset :=
  node_ok cuts247 [⟨state247_21,exclude247_21⟩,⟨state247_22,exclude247_22⟩,⟨state247_23,exclude247_23⟩] 0x2c0c0524214908c24224e0c93832c0c0938324e0cc2421490852420d050938324e0c27070c88832220d05032220c888270724e0c938340064938324e0c46420c88846428000832220c888464224e0c938315050938324e0c470714908524215050524214908470724e0c93830d0c0938324e0c26221490852420d0c0524214908262224e0c938330908323030908c04040068c04030909001a30108c0400c8c0c04224e0e000124e0c91810c8c0918124e0c32302460c918140044918309c1c16140585034140c8c0323009c1c32300c8c034140585016141190812101190844400c8c0444011908323011108444004840444211c1c32300c8c0541440044541411c1d00121141c54140c8c032300988832300c8c034300585034300988816140908834300c8c0323021c1c434210d08c24240068c24221c1d001a2181cc24210d08434224e0c434224e0c92820c4c0928224e0c313024a0c928210d08928340080414010500323010d08434240080434210d08323010500414209c1c434210d0834140c4c0313009c1c31300c4c0341410d08434240080434210d0846420c4c046424008031300c4c0464210d08434211c1c31300c4c0541410d08434211c1c434210d0854140c4c031304008031300c4c0343010d08434240080434210d0834300c4c031302c0c034142c0c0c24240068c2422c0c1001a2c0c0c2420d050c24240011000428e0d00190d05034141505100191505100194004a00001505034140d05034304007834304001434140d05034300d050343040015001908c1cb03011908464230909001a30908b03040068b03030908464211908541440018541440064464211908541411908464240065000614050343040018878340014464221e0c343011908464240015000640018c24215050c2422c0c1001a2c0c0c24240068c2422c0c054142c0c1000440010c38330908343030908b03040068b03030909001a30908b0300d0c03430 (by decide +kernel)

def state247_25 : List Sig := [0x3333000033330000333300003333000033330000333300003333000033330000,input 4,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 6,0xfffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0,input 2,input 0,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_25 : Impossible true (goalAt 247) 7 state247_25.toFinset :=
  node_ok cuts247 [⟨state247_19,exclude247_19⟩] 0x434230108840710d0843420d0c0151410d08434218108313010d08313010d0843420c4c0151410d08434205450938324a08928324a0c34303010894143010885830d0c054308000034300d05034300d0c021070908893830d0c0938318108c0422c0c060421c0c060421810850302860ca18318109000e30108b0303010870303060cc04225050c0420d050524224e0c938314908938318108322224e0c938314908524224e0c938314908524224e0c323030108b03030108313010d08313010d0832300908834300c8c012101810832301810832301808870300c8c016140c8c03230058509183 (by decide +kernel)

def state247_26 : List Sig := [0xfffffffffffff0f0fffffffffffff0f0fffffffffffff0f0fffffffffffff0f0,input 4,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 6,input 2,input 0,input 1,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_26 : Impossible true (goalAt 247) 7 state247_26.toFinset :=
  node_ok cuts247 [⟨state247_20,exclude247_20⟩] 0xc24230100c0423010832300d0c024220c8c03230140c060220c8c016140c8c032300585032220c8c032300541c624218100604218108434230908860710d08414010d0843421050843420d0c0151410d08313010d0843420c4c0151410d0843420545043420c4c0313010d08434218908313010d083430309089014309083430140c200000d0c034140d0c0343008c1c26220d0c03430090c0878330908b03030908503030e0cc24225050c242240c0b03030908a030309085030148885030180c034140c888322209050938318908c2422c0c06242140c0624218909000628e0ca383189090006 (by decide +kernel)

def state247_27 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 6,0xfffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0,input 2,input 0,input 1,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_27 : Impossible true (goalAt 247) 8 state247_27.toFinset :=
  node_ok cuts247 [⟨state247_21,exclude247_21⟩,⟨state247_25,exclude247_25⟩,⟨state247_26,exclude247_26⟩] 0x2c0c0524214908c24224e0c93832c0c0938324e0cc24214908524240064938324e0c62420c88862428000832220c888624224e0c93831c0c0938324e0c62221490852421c0c0524214908622224e0c93830d050938324e0c27071490852420d050524214908270724e0c938330908323030908c04040030c04030909001c30108c0400c8c0c04224e0e000124e0c91810c8c0918124e0c32302460c91814003091830988832300c8c034300585034300988816140908834300c8c032301890812101890860400c8c060401890832301810860400484060421888832300c8c070304003070301888900121808870300c8c0323009c1c16140585034140c8c0323009c1c32300c8c0341405850161421c1c434210d08c2424006cc24221c1d001c2181cc24210d08434224e0c434224e0c92820c4c0928224e0c313024a0c928210d08928340030414010500323010d0843424006c434210d0832301050041424006c434210d0834300545034304006c151405450343010d0843424006c434210d0862420c4c062424006c31300c4c0624210d0843424006c31300c4c0703010d0843424006c434210d0870300c4c0313009c1c151405450341410d08434209c1c434210d0834140545015142505034300d0c0c24240064c24225051001c25050c2420d0c0c24205c1c26220988893830d0c0938305c1c34300d0c0938309888938340015000521e0d00190d0c034301c0c10019150c100194004a00001c0c034300d0c034144007434144001034300d0c034140d0c0343040011001908c1cb03018908624230909001930908b03040070b030309086242189087030400187030400646242189087030189086242400650006140c0341440018a38340010624228e0c341418908624240011000640010c2421c0c0c2422c0c1001c2c0c0c24240070c2422c0c070301c0c1000540014c38330908341430908941440070941430909001c3090894140d0503414 (by decide +kernel)

def state247_28 : List Sig := [0xfffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0,input 2,input 5,input 0,input 1,input 4,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_28 : Impossible true (goalAt 247) 9 state247_28.toFinset :=
  node_ok cuts247 [⟨state247_4,exclude247_4⟩,⟨state247_18,exclude247_18⟩,⟨state247_24,exclude247_24⟩,⟨state247_27,exclude247_27⟩] 0x40068c2421c0c0c24240068b03030e0cc38340068c24230e0cc38340068b0301c0c0438340068b03014908524240068c24224e0c938340068b03024e0c938340068c24214908524240048703024e0c938340058c38314908c38340054703014908524240058c38324e0c938340014341424e0c93834001427070c88832224001434140c888322240014270724e0c938340065001924e0c93834006500030c88832224006500150c888322240065000324e0c938340030c2420c8c0c24240030c04040030c04040030c24240068c04240030c0400c8c0c04240030c3830c8c0c38340030c18140030c18140030c38380000c18340030c1810c8c0c1834003093834005493834003091810c8c091814003093830c8c091834003091814003091834001427070585016144001434140c8c032304001427070c8c032304001434140585016144001026220c8c032304001034300585034304001026220585024224001034300c8c0323040031000c0484012104003100000c8c0323040031000c0c8c032304003100000484012104006c870710d0843424006cc2424006cc2424006c87074006886074006cc24210d0843424006cc3830c4c0c3834006cc28210d08c2824006cc38310d08c2834006cc2820c4c0c2834006c938310d0893834006c92820c4c092824006c93830c4c092834006c928210d08928340031000c10500414040030323010d08434240031001b10d08434240030323010500414240014270710d0843424001434140c4c031304001427070c4c0313040014341410d08434240011000410d08434240010343005450343040011001b05450151440010343010d0843424006d001b10d0843424006d00010c4c031304006d001b0c4c031304006d000110d08434240014b0300d050b03040014c24240014c24240014b03040068b03040014c2420d050c2424001470300d050703040014c38340014c3834001470308000c703040014c3830d050c38340011000440010a3834001094140d0c0343040010c24240010c24240010941440068941440010c2420d0c0c2424001054140d0c0343040010c38340010c38340010541480008541440010c3830d0c0c3834001017070988826224001093830d0c093834001017070d0c034304001093830988893834001034144001434144001100040d0c0343040011000440010230740011000440014878340068b03040008b03040068c24240068c24240068b03040068b03040068c24240008c24240064703040018703040064c38340064c38340064703080004703040064c38340018c383 (by decide +kernel)

def state247_29 : List Sig := [0x3333000033333333333300003333303033330000333333333333000033333030,input 4,input 5,input 2,input 6,input 0,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_29 : Impossible true (goalAt 247) 6 state247_29.toFinset :=
  node_ok cuts247 [] 0x10d08c2422181c434230e0cc28230a0cc28321e0c868221a0c86832860ca0822820ca08324e0c928224a0c928330908c38330e0c438111908878321e0c464221e0cc38311908878321e0ca1830d0c0878321e0c93830d0c0878318108a1832860c60422860cc38318108a18314908938324e0c524224e0cc38314908938324e0ca1830c888938330108c04230100c2421050843421050043423060cc1831c0c0c3832160c858311100878305850a18318100a1832460c9183141009383 (by decide +kernel)

def state247_30 : List Sig := [0xffff0000ffffffffffff0000fffff0f0ffff0000ffffffffffff0000fffff0f0,input 4,input 5,input 2,input 6,input 0,input 1,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_30 : Impossible true (goalAt 247) 7 state247_30.toFinset :=
  node_ok cuts247 [⟨state247_29,exclude247_29⟩] 0xc24230100c0423010832301c0c060220c8c0464211100444211108a38328604a1832860c52421410050421410a00000c8c0323040000434230908860710d08414010d08434210508313010d0843420c4c0434211908151410d08a38328a08a28328a0c434214908313010d08232210d08434208c88c2422c0c0c2421c0c046423090890141190834301190846420d0c0a78328e0c343028e0c464214908343011908878321e0c464209888b03028e0ca38330908a38338e0c503028e0c524230908b03014908703014908524218888524228e0c341428e0c938330908a22230908a22230e0cc3831c0c062220d050a38318908a383 (by decide +kernel)

def state247_31 : List Sig := [0x3333000033330000333300003333000033330000333300003333000033330000,input 4,0xffffffff00000000f0f0f0f000000000ffffffff00000000f0f0f0f0,input 5,input 2,input 6,input 0,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_31 : Impossible true (goalAt 247) 7 state247_31.toFinset :=
  node_ok cuts247 [] 0x10d08c0422101c43420c4c0434210d08313010d0844420545043422860ca0822820ca08324e0c928224a0c928330108b03030108703011108c0422505044420d0c044421110834302960ca1830d0c0a1831110893830d0c093832c0c0a1832860cc0422860ce1831c0c0a18330108b03030108b03010d08313010d0831303060cc1831505070302160c858311108343018108524224e0c524224e0c16140c8c016140c8c0524224e0c938314908938314908524224e0c93832860c322224e0c323030108b03030108313010d08313010d0832301808870300c8c032301110834301110816142860c32302860c9183 (by decide +kernel)

def state247_32 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,0xffffffff00000000f0f0f0f000000000ffffffff00000000f0f0f0f0,input 2,input 6,input 0,input 1,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_32 : Impossible true (goalAt 247) 7 state247_32.toFinset :=
  node_ok cuts247 [] 0xc24230100c0423010832301c0c060220c8c046421110044421110832220c8c0323040044a38328604a1832860c434230908860710d08414010d08434210508313010d0843420c4c0434211908151410d0843420c4c0313010d08a38328a08a28328a0cc242240c0c2421c0c046423090894141190834301190846420d0c046420d0c0343011908a78328e0c343028e0cc242240c0c242240c016140c8c016140c8c043420c4c043420c4c0c38330e0c54141c0c0878321e0c46420d0c024140c88834140c889000328e0c624228e0c9030309089030309087030188886030180c09383240c0a38328e0cc24228e0ce3831c0c0a383 (by decide +kernel)

def state247_33 : List Sig := [0xffffffff00000000f0f0f0f000000000ffffffff00000000f0f0f0f0,input 5,input 2,input 6,input 0,input 1,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_33 : Impossible true (goalAt 247) 8 state247_33.toFinset :=
  node_ok cuts247 [⟨state247_30,exclude247_30⟩,⟨state247_31,exclude247_31⟩,⟨state247_32,exclude247_32⟩] 0xb03014908524230908938324e0cb03024e0c938330908524214908703024e0c938318888524214908703014908524218888938324e0d001924e0c938328e0c322228e0e00020c888322228e0c938324e0cc2420c8c0c24230101001c30100c24240070c0423010032303010893838000493832460432302460493830c8c091832460500112460c62220c8c032301c0c100111c0c062224007860221c0c032300c8c046420c8c0464211100161411100464205850444211100323011108a38305850a38328604323028604a3830c8c0a1832860416142860c870710d08434230909001c30908870740070860730908434210d08938310d08938324a08313024a0893830c4c0928324a08434224a0d001f1050041400c8c0434210d09001f10d0843420c8c041401050847070c4c031301c0c0434210d08470710d0843421c0c031300c4c1001910d08434211908151411909001f05450151411908434210d08a38310d08a38328a08313028a08a3830c4c0a28328a08434228a0cc2421c0c0c2422c0c1001c2c0c0c24240070c2422c0c070301c0c0941411908464230909001930908941440070941430908464211908170711908464224e0c343024e0c17070d0c0343024e0c464224e0c54140d0c034301c0c046421190854141190846421c0c034300d0c1001911908a78328e0c343028e0d00190d0c0343028e0c464228e0cb03008c0cb03030908a38328e0cb03028e0ca38330908230330908703028e0ca38315051001938e0c703040078703015050a38328e0cc24240008c2422c0c1001c2c0c0c24240070c2422c0c100022c0c052424000c524224e0d001e24e0c524280000524224e0d000324e0c16144000016140c8c100110c8c016144004416140c8c100000c8c043424000443420c4c1001f0c4c043424007c43420c4c100010c4c0541440018c3831c0c1000430e0c54144001054141c0c100061c0c046424001087830d0c1000621e0c46424001846420d0c100040d0c1001e400646242 (by decide +kernel)

def state247_34 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,0xfffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0,input 0,input 1,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_34 : Impossible true (goalAt 247) 6 state247_34.toFinset :=
  node_ok cuts247 [] 0x30908c04030108c0420c8c034301808832300585032300c8c0161411908444011108444218908604018108604210d08c2422181c434210500434210d0841420c4c0434210d08313005450434210d08151410d0846420c4c0434210d0862420c4c0434230908a43030908343030e0cc3830d0c1001930908941430908903011908c242280c0464221e0c878311908603009050464211908601424e0c93830c888464218908c2422c0c062420d0c0624218908443028e0ca383189084414 (by decide +kernel)

def state247_35 : List Sig := [0xfffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0,input 4,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 5,0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0,input 0,input 1,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_35 : Impossible true (goalAt 247) 7 state247_35.toFinset :=
  node_ok cuts247 [⟨state247_20,exclude247_20⟩,⟨state247_34,exclude247_34⟩] 0x30908c04030108c0420c8c034301808832301890860401810860420585032300c8c0161405c1c32300c8c0150711908444011108444210d08c2422181c434210500434210d0841420c4c0434210d08313010d0862420c4c0434205450434210d08151410d0831300c4c0434210d0846420c4c0434230908b03030908343030e0cc3830d0c1000418908c2422c0c062420d0c0624218908503028e0cc24225050c24214050b03030908b030309083430188883430190c017071890a000118908501411c1c441411050938311908c2422c0c0464221e0c8783119086222119086242800004642140504642119084307 (by decide +kernel)

def state247_36 : List Sig := [0x3333000033330000333300003333000033330000333300003333000033330000,input 4,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 5,0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0,input 2,input 0,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_36 : Impossible true (goalAt 247) 7 state247_36.toFinset :=
  node_ok cuts247 [⟨state247_19,exclude247_19⟩] 0x434230108840710d08434211108151410d08313010d0843420c4c0434218108313010d08151410d08434205450938324a08928324a0c444230108941411108858311108604280000444215050444211108501411108938305c1c938330108b0303010870303060cc1831c0c1000c18108c0422c0c060421c0c060421810850302860cc04225050c04215050524224e0c938314908938314908524224e0c938318108322224e0c938314908524224e0c323030108b03030108313010d08313010d0832301110816141110832301808870300c8c016141810832301810816140c8c03230058509183 (by decide +kernel)

def state247_37 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0,input 2,input 0,input 1,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_37 : Impossible true (goalAt 247) 7 state247_37.toFinset :=
  node_ok cuts247 [⟨state247_20,exclude247_20⟩,⟨state247_34,exclude247_34⟩] 0x30908c04030108c0421190844401110844420c8c050301808832300585032300c8c016140c88832300c8c1001118908604018108604210d08c2422181c434210500434210d08414210d0846420545043420c4c0434210d08313005450434210d08151410d0831300c4c0434210d0862420c4c0434211908c24225050464221e0c34141190846421405046420c88a00011190846421890a000011908c2422c0c0c242140c0c38330e0c503040014c24225050c242240c0b03030908a030309085030148885030180c034140c888322209050938318908c2422c0c06242140c0624218909001628e0ca383189084707 (by decide +kernel)

def state247_38 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 5,0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0,input 2,input 0,input 1,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_38 : Impossible true (goalAt 247) 8 state247_38.toFinset :=
  node_ok cuts247 [⟨state247_21,exclude247_21⟩,⟨state247_35,exclude247_35⟩,⟨state247_36,exclude247_36⟩,⟨state247_37,exclude247_37⟩] 0x2c0c0524214908c24224e0c93832c0c0938324e0cc2421490852421c0c0938324e0c62221490852421c0c0524214908622224e0c938340064938324e0c62420c88862428000c32220c888624224e0c938315050938324e0c470714908524215050524214908470724e0c938330908323030908c04040070c04030909001c30108c0400c8c0c04224e0e000224e0c91810c8c0918124e0c32302460c91814004491831190832301190844400585044401190816141110844400c8c044421888832300c8c070300585070301888816141808870300c8c032301890816141890860400c8c0604018908323018108604005850604211c1c16140585054140c8c0323011c1c32300c8c0541405850161421c1c434210d08c24240088c24221c1d001c2181cc24210d08434224e0c434224e0c92820c4c0928224e0c313024a0c928210d08928340088414010500323010d08434240088434210d08323010500414240088434210d08464205450464240088151405450464210d0843424008831300c4c0703010d08434240088434210d0870300c4c0313040088434210d0862420c4c062424008831300c4c0624210d08434211c1c151405450541410d08434211c1c434210d08541405450151425050464211908c24240064c24225051001c25050c24211908464205c1c464211908938340064938305c1e000105c1c938311908938340019000621e0d001911908464218909001918909001940066000018908464211908541440074541440010464211908541411908464240011001914050c2421c0c0c2422c0c1001c2c0c0c24240070c2422c0c070301c0c0541440014c38340010703030e0c54141c0c0703040011000540010b03018908624230909001930908b03040070b030309086242189087030400787030400146242189087030189086242400150019140c1000640018a38330908541430908941440070941430909001c309089414150505414 (by decide +kernel)

def state247_39 : List Sig := [0xfffffffffffffffffffffffff0f0f0f0fffffffffffffffffffffffff0f0f0f0,input 5,0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0,input 2,input 6,input 0,input 1,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_39 : Impossible true (goalAt 247) 8 state247_39.toFinset :=
  node_ok cuts247 [] 0x14908938324e0c524224e0c524214908938324e0c524214908938324e0c62420c888938324e0c524214908938330908c04030108c04224e0c91812460c91830c8c054141141c32301190844401110844420c8c016140585032301890860401810860420484032300c8c0121010d08c2422181c434224e0c928224a0c928310500434210d0841420c4c0434210d08313010d0846420545043420c4c0434210d08313010d0862420c4c0434204440434210d08111030908b03030908b0301c0c1001911908c24225050464211908938305c1c93831505046421405034301190862420d050464240074c2422c0c0c2422c0c1000518908c2422c0c062420d050624218908341440078624240064a383309089010309089010 (by decide +kernel)

def state247_40 : List Sig := [0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0,input 2,input 6,input 0,input 1,input 4,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_40 : Impossible true (goalAt 247) 9 state247_40.toFinset :=
  node_ok cuts247 [⟨state247_24,exclude247_24⟩,⟨state247_18,exclude247_18⟩,⟨state247_33,exclude247_33⟩,⟨state247_38,exclude247_38⟩,⟨state247_39,exclude247_39⟩] 0x40068b03018908624240068c24228e0ca38340068b03028e0ca38340068c24218908624240019000628e0ca3834001854141890862424001a000318908624240018541428e0ca3834007a000228e0ca38340065000518908624280012000118908624240065000528e0ca38340068b03014908524240068c24224e0c938340068b03024e0c938340068c24214908524240064341424e0c93834003ca3830c888a3834008434140c888322240064a38324e0c938340018541424e0c938340018470714908524240018541414908524240018470724e0c938340079002124e0c93834003d00031490852424008500211490852424003d000324e0c938340068c2420c8c0c24240068c04040068c04040068c24240068c04240068c0400c8c0c04240064a38305850a38340038a1810c8c0a18140044a3830c8c0a18340064a18105850a1834003c93834008493834003891810c8c091814003c93830c8c091834003891814008c91834001847070c8c032304001854144001854144001847074001845074001854140c8c032304001046420c8c046424001044400585044404001046420585044424001044400c8c044424007900230c8c032304003900000585016144008d00230585016144003900000c8c0323040088870710d08434240088c24240088c24240088870740068860740088c24210d08434240088a38310d08a38340088a2820c4c0a28240088a3830c4c0a28340088a28210d08a28340088938310d0893834008892820c4c092824008893830c4c0928340088928210d08928340089002210500414040088323010d08434240089002210d0843424008832301050041424001847070c4c0313040018541410d08434240018470710d0843424001854140c4c0313040011000410d08434240010464205450464240011002205450151440010464210d0843424008900220c4c0313040089000110d08434240089002210d0843424008900010c4c0313040018c24215050c24240018b03040018b03040018c24240068c24240018b03015050b03040011000440010c38340010941411908464240010c24240010c24240010941440068941440010c24211908464240010341411908464240010a38340010a38340010341480000341440010a38311908a38340010170711908464240010938340010938340010170740084170740010938311908938340010541440018541440011000411908464240011000440010501440011000440018878340068c24240008c24240068b03040068b03040068c24240068c24240068b03040008b030 (by decide +kernel)

def state247_41 : List Sig := [0x5555050555550505555505055555000055550505555505055555050555550000,input 4,input 2,input 5,input 6,input 1,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_41 : Impossible true (goalAt 247) 6 state247_41.toFinset :=
  node_ok cuts247 [] 0x30908c04030108c04230e0cc1813060cc18328e0ca1812860ca18321a0c84812120c848324e0c91812460c918330908c38330e0c438218908a38328e0c624228e0cc38318908a3830d0c0868321a0cc24221a0cc38314050868321a0ca3830d0c0868321a0c93830d0c0868314908938324e0c524224e0cc38314908938324e0ca3830c888938310d08860730908434210508434210d08414030a0cc28310d08c38328a0ca28318908a38310d08868311908868324a0c9283149089383 (by decide +kernel)

def state247_42 : List Sig := [0x3333030333330303333303033333000033330303333303033333030333330000,input 4,input 2,input 5,input 6,input 0,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_42 : Impossible true (goalAt 247) 6 state247_42.toFinset :=
  node_ok cuts247 [] 0x10d08c2422101c434230e0cc28230a0cc28328e0ca28228a0ca2832160c84822120c848324e0c928224a0c928330908c38330e0c438118908a38328e0c624228e0cc38318908a3831110885832160c44422160cc3831110885832160ca3830d0c085832160c93830d0c0858314908938324e0c524224e0cc38314908938324e0ca3830c888938330108c04230100c2421050843421050043423060cc1831c0c0c3832860ca18318100a3830c8c085831110085832460c9183141009383 (by decide +kernel)

def state247_43 : List Sig := [0xffff0f0fffff0f0fffff0f0fffff0000ffff0f0fffff0f0fffff0f0fffff0000,input 4,input 2,input 5,input 6,input 0,input 1,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_43 : Impossible true (goalAt 247) 7 state247_43.toFinset :=
  node_ok cuts247 [⟨state247_41,exclude247_41⟩,⟨state247_42,exclude247_42⟩] 0xc24230100c0423010832301c0c060220c8c062421810060421810887832160485832160c52421410050421410a00010c8c0323040000434230908860710d08414010d08434210508313010d0843420c4c0434218908313010d08878321a08868321a0c434214908313010d0a000010d08434240004c2422c0c0c2421c0c06242309089030189087030189086242140c0343021e0c878330908878331e0c501421e0c878329e0c343021e0c878314908343021e0c87830d0c0464221e0c524230908a030149087030149085242180c0524218908322214908938330908870730908870730e0cc3831c0c0470728e0ca383189082707 (by decide +kernel)

def state247_44 : List Sig := [0xfffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0,input 4,0xf0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f0f0f0f0f0f0f0f0f00000000,input 5,input 6,input 0,input 1,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_44 : Impossible true (goalAt 247) 7 state247_44.toFinset :=
  node_ok cuts247 [] 0xc24230100c0423010832301c0c060220c8c062421810060421810813070c8c032300441c87832160485832160c434230908860710d08414010d08434210508313010d0843420c4c0434218908313010d0843420c4c0313010d08878321a08868321a0cc2422c0c0c2421c0c0624230908b030189087030189086242140c0c24224050c2420d0c032300585032300d0c043420545043420d0c0c38330e0c70300d0c0a38328e0c62420d05024300d0c0343004c1d000321e0c464221e0cb03030908b0303090870301888870301888834141890824141890893832c0c0878321e0cc24221e0cc7831c0c0878321e0ca7830d0508783 (by decide +kernel)

def state247_45 : List Sig := [0x3333000033330000333300003333000033330000333300003333000033330000,input 4,0xf0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f0f0f0f0f0f0f0f0f00000000,input 2,input 5,input 6,input 0,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_45 : Impossible true (goalAt 247) 7 state247_45.toFinset :=
  node_ok cuts247 [] 0x10d08c0422101c43420c4c0434210d08313010d0860420c4c043422160c84822120c848324e0c928224a0c928330108b03030108703018108c0422c0c060421c0c060421810850302505085832160cc0422160cc5831505085832160ca5830d05085832160c938304c1c858330108941430108941410d08151410d0815143060cc1831c0c054142860ca18318108341411108524224e0c524224e0c323005850323005850524224e0c938314908938314908524224e0c938318108322224e0c323030108b03030108313010d08313010d0832301808870300c8c016141810832301810832302160c16142160c9183 (by decide +kernel)

def state247_46 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f0f0f0f0f0f0f0f0f00000000,input 2,input 5,input 6,input 0,input 1,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_46 : Impossible true (goalAt 247) 8 state247_46.toFinset :=
  node_ok cuts247 [⟨state247_43,exclude247_43⟩,⟨state247_44,exclude247_44⟩,⟨state247_45,exclude247_45⟩] 0xb03014908524230908938324e0cb03024e0c938330908524214908703024e0c938318888524214908703014908524218888938324e0c341424e0c93831890832221890834140c888322218908938324e0cc2420c8c0c24230101001c30100c24240070c0423010032303010893838000893832460432302460493830c8c091832460500112460c62220c8c032301c0c1001d1c0c062224007460221c0c032300c8c062420585062421810032301810062420c8c060421810016141810887830c8c087832160416142160487830585085832160432302160c870710d08434230909001c30908870740070860730908434210d08938310d08938324a08313024a0893830c4c0928324a08434224a0d001f1050041400c8c0434210d09001f10d0843420c8c041401050847070c4c031301c0c0434210d08470710d0843421c0c031300c4c0270710d0843421890831301890827070c4c0313018908434210d08878310d08878321a08151421a08878305450868321a08434221a0cc2421c0c0c2422c0c1001d2c0c0c24240070c2422c0c070301c0c0b03018908624230909001930908b03040070b0303090862421890870300d0507030150506242189087030189086242150503414140c0941440070941430908878321e0c941421e0c878330909001930908170721e0c878324e0d001924e0c170780004130724e0c878321e0c541421e0c87831c0c1001931e0c54144007454141c0c0878321e0c341421e0c878318909001929e0c341440064341418908878321e0cc24240008c24225051001d25050c24240070c2422505100022505052424000c524224e0d001d24e0c524280000524224e0d000324e0c323040000323005851001d05850323040044323005851000005850434240004434205451001d0545043424007c434205451000105450703040010c38315051000530e0c703040014703015051000415050624240010a3830d051000628e0c62424001862420d05100040d051001d400644642 (by decide +kernel)

def state247_47 : List Sig := [0xfffffffffffffffffffffffff0f0f0f0fffffffffffffffffffffffff0f0f0f0,input 2,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 5,input 6,input 0,input 1,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_47 : Impossible true (goalAt 247) 8 state247_47.toFinset :=
  node_ok cuts247 [] 0x14908938324e0c524224e0c524214908938324e0c62420c888938324e0c524214908938324e0c524214908938330908c04030108c04224e0c91812460c91830c8c070301808832301890860401810860420585032300c8c016141190844401110844420484032300c8c0121010d08c2422181c434224e0c928224a0c928310500434210d0841420c4c0434210d08313010d0862420c4c0434205450434210d08151410d08464205450434204440434210d08111030908b03030908703015051001918908c2422c0c062421c0c06242140c0341440078c24225050c24225051000411908c2422505046421190893830d0c093830d0c046421190834301190862420d0c04642400744642400648783309089010309089010 (by decide +kernel)

def state247_48 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 5,input 6,input 0,input 1,input 2,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_48 : Impossible true (goalAt 247) 9 state247_48.toFinset :=
  node_ok cuts247 [⟨state247_18,exclude247_18⟩,⟨state247_27,exclude247_27⟩,⟨state247_38,exclude247_38⟩,⟨state247_46,exclude247_46⟩,⟨state247_47,exclude247_47⟩] 0x40090b0301490852424003cc24224e0c938340094b03024e0c938340090c24214908524240018703024e0c938340018622214908524240018703014908524240018622224e0c938340015000524e0c93834001462420c88862424001500260c888322240014624224e0c938340075002624e0c93834003d000314908524240099002614908524240075000324e0c938340090941411908464240064c24221e0c878340070941421e0c878340064c2421190846424003c170721e0c87834006493830d0c093834009817070d0c0343040064938321e0c878340019000621e0c87834001870301190846424001a000211908464240018703021e0c878340015000521e0c87834001462420d0c062424001600010d0c0343040014624221e0c878340076000321e0c878340065000411908464280012000011908464240065000421e0c878340030c2420c8c0c24240030c04040030c04040030c24240094c04240030c0400c8c0c0424003093834009893834003091810c8c091814003093830c8c091834003091814003091834003087830c8c087834003085810585085814003087830585085834003085810c8c085834001862220c8c032304001870304001870304001862224001860224001870300c8c032304001462420585062424001460400c8c060404001462420c8c0604240014604005850604240031000c0585016144003100000c8c0323040031000c0c8c0323040031000005850161440088870710d08434240088c24240088c24240088870740094860740088c24210d08434240088938310d0893834008892820c4c092824008893830c4c0928340088928210d08928340088878310d08878340088868205450868240088878305450868340088868210d08868340089002210500414040088323010d08434240089002210d0843424008832301050041424001900060c4c0313040018703010d08434240019002210d0843424001870300c4c0313040015000510d0843424001462420c4c062424001500220c4c0313040014624210d08434240089002205450151440089000110d08434240089002210d08434240089000105450151440018c2421c0c0c24240018b03040018b03040018c24240094c24240018b0301c0c0703040019000640014c38340014b03018908624240014c24240014c24240014b03040094b03040014c24218908624240018703040018703040019000518908624240019000640018503040019000640018a38340090c24240008c24240074941440094941440094c24240094c242400909414400089414 (by decide +kernel)

def state247_49 : List Sig := roots 247
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_49 : Impossible true (goalAt 247) 10 state247_49.toFinset :=
  node_ok cuts247 [⟨state247_10,exclude247_10⟩,⟨state247_28,exclude247_28⟩,⟨state247_40,exclude247_40⟩,⟨state247_48,exclude247_48⟩] 0x40008c2421c0c0c24240008b03030e0cc38340008c24230e0cc38340008b0301c0c0438340008b03018908624240008c24228e0ca38340008b03028e0ca38340008c24218908624240018703028e0ca38340014c38318908c3838000c703018908624240018c38328e0ca38340008b03014908524240008c24224e0c938340008b03024e0c938340008c24214908524240018703024e0c93834000cc38314908c3834000c703014908524240018c38324e0c93834000c341424e0c93834000ca3830c888a3834000c34140c88832224000ca38324e0c938340008941411908464240008c24221e0c878340008941421e0c878340008c24211908464240018541421e0c878340010c38311908c38380008541411908464240010c38321e0c878340014341421e0c878340010a3830d0c0a3838000434140d0c0343040010a38321e0c87834000c170721e0c87834001093830d0c093834000c17070d0c0343040010938321e0c878340000c2420c8c0c24240000c04040000c04040000c24240008c04240000c0400c8c0c04240000c3830c8c0c38340000c18140000c18140000c38380000c18340000c1810c8c0c18340000a38305850a38340000a1810c8c0a18140000a3830c8c0a18340000a18105850a1834000093834000c93834000091810c8c091814000093830c8c091834000091814000091834000087830c8c087834000085810585085814000087830585085834000085810c8c0858340004870710d08434240004c24240004c24240004870740008860740004c24210d08434240004c3830c4c0c38340004c28210d08c28240004c38310d08c28340004c2820c4c0c28340004a38310d08a38340004a2820c4c0a28240004a3830c4c0a28340004a28210d08a28340004938310d0893834000492820c4c092824000493830c4c0928340004928210d08928340004878310d08878340004868205450868240004878305450868340004868210d08868340001000010500414040000323010d08434240001000110d084342400003230105004142 (by decide +kernel)

theorem lower247 : Claim 247 11 :=
  fromSearch 536872260 (by decide +kernel) exclude247_49


open PEqualNP.CircuitLowerBounds

def graph : Sig := goalAt 255
theorem graph_proper : proper graph := by unfold proper; decide +kernel

def edgeList : List Nat := [0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 2, 6, 4, 6, 5, 6, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7]
def target (x : Fin 8 → Bool) : Bool :=
  decide (∃ i < edgeList.length / 2,
    (List.ofFn x).getD (edgeList.getD (2*i) 0) false = true ∧
    (List.ofFn x).getD (edgeList.getD (2*i+1) 0) false = true)

def smallCircuit : Circuit := ⟨[⟨.or, [0, 7]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [6, 8]⟩, ⟨.or, [2, 3]⟩, ⟨.or, [5, 7]⟩, ⟨.or, [2, 8]⟩, ⟨.and, [9, 10]⟩, ⟨.and, [11, 12]⟩, ⟨.and, [6, 13]⟩, ⟨.and, [4, 1]⟩, ⟨.or, [14, 15]⟩, ⟨.or, [18, 16]⟩, ⟨.or, [19, 17]⟩], 20⟩

theorem witnessMonotone : ∀ g ∈ smallCircuit.gates,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [smallCircuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ⟨Or.inl rfl, by decide⟩ | exact ⟨Or.inr rfl, by decide⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem witnessCorrect : ∀ x : Fin 8 → Bool, smallCircuit.eval (List.ofFn x) = target x := by
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


def eightInputs : List Sig := roots 255
def sampleEight (r : Row) (i : Fin 8) : Bool := bit r (eightInputs.getD i.val zero)
theorem eightList : List.ofFn (fun i : Fin 8 => eightInputs.getD i.val zero) = eightInputs := rfl
theorem eightSampled (r : Row) : List.ofFn (sampleEight r) = eightInputs.map (bit r) := by
  rw [←eightList,List.map_ofFn]
  rfl

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem eightTable : ∀ r : Row, bit r graph = target (sampleEight r) := by decide +kernel

theorem eightEval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates eightInputs).getD i zero) =
      (C.wires (List.ofFn (sampleEight r))).getD i false := by
  rw [←b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),eightSampled]
  rfl


def lowRow (i : Fin 8) : Row := Fin.ofNat 256 (1 <<< ([4, 4, 5, 5, 0, 0, 0, 2] : List Nat).getD i.val 0)
def highRow (i : Fin 8) : Row := Fin.ofNat 256 ((1 <<< i.val) ||| (1 <<< ([4, 4, 5, 5, 0, 0, 0, 2] : List Nat).getD i.val 0))

set_option maxHeartbeats 1000000 in
theorem allEightRequired :
    (∀ i : Fin 8, bit (lowRow i) graph ≠ bit (highRow i) graph) ∧
    (∀ i j : Fin 8, i ≠ j →
      bit (lowRow i) (eightInputs.getD j.val zero) =
      bit (highRow i) (eightInputs.getD j.val zero)) := by decide +kernel

theorem physicalSigned (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x : Fin 8 → Bool, C.eval (List.ofFn x)=target x) :
    ∃ k, k ≤ C.gates.countP (fun g => !isNot g) ∧ Live true graph k eightInputs.toFinset := by
  have goalEq : (execute C.gates eightInputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (eightEval C legal C.output r).trans ((computes (sampleEight r)).trans (eightTable r).symm)
  have out := get_rep (u:=true) (execute C.gates eightInputs) C.output
  rw [goalEq] at out
  unfold Repr at out
  have pg : bit 0 graph = false := by decide +kernel
  rw [nrm_id pg] at out
  obtain ⟨k,S,hk,run,sub⟩ := extract (u:=true) C.gates eightInputs legal (by simp) graph_proper
    (out.resolve_right (fun h => h graph_proper))
  have ns : eightInputs.all plainWord = true := by decide +kernel
  rw [nrm_map ns] at sub
  have idx (a : Sig) (ha : a ∈ eightInputs) : ∃ i : Fin 8, eightInputs.getD i.val zero = a := by
    rw [←eightList] at ha
    exact List.mem_ofFn.mp ha
  have eq : S = eightInputs.toFinset := by
    ext a
    constructor
    · exact fun h => List.mem_toFinset.mpr (sub a h)
    · intro ha
      obtain ⟨i,rfl⟩ := idx a (List.mem_toFinset.mp ha)
      apply raw_required run eightInputs (eightInputs.getD i.val zero) sub (lowRow i) (highRow i)
        (allEightRequired.1 i)
      intro v hv hn
      obtain ⟨j,rfl⟩ := idx v hv
      apply allEightRequired.2 i j
      rintro rfl
      exact hn rfl
  exact ⟨k,hk,eq ▸ run⟩


theorem replaceShort
    (lower : Impossible true graph 11 eightInputs.toFinset) (gates : List Gate) (o : Nat)
    (fit : ∀ g ∈ gates, (g.op=GateOp.and ∨ g.op=GateOp.or ∨ g.op=GateOp.not) ∧ g.inputs.length≤2)
    (correct : ∀ x : Fin 8 → Bool, (Circuit.mk gates o).eval (List.ofFn x)=target x) :
    ∃ (gs : List Gate) (out : Nat), (∀ g ∈ gs, (g.op=GateOp.and ∨ g.op=GateOp.or) ∧ g.inputs.length≤2) ∧
       gs.length≤gates.length ∧ ∀ x : Fin 8 → Bool, (Circuit.mk gs out).eval (List.ofFn x)=target x := by
  classical
  by_cases big : 13 ≤ gates.length
  · exact ⟨smallCircuit.gates, smallCircuit.output, witnessMonotone, (by simpa only [witnessSize] using big), witnessCorrect⟩
  by_cases mono : ∀ g ∈ gates, g.op ≠ GateOp.not
  · exact ⟨gates, o, noNotReuse fit mono, Nat.le_refl _, correct⟩
  push Not at mono
  obtain ⟨g, hg, hop⟩ := mono
  have lt : gates.countP (fun q => !isNot q) < gates.length := by
    rcases Nat.lt_or_ge (gates.countP (fun q => !isNot q)) gates.length with h | h
    · exact h
    · have eq := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length h) g hg
      simp [isNot, hop] at eq
  have legal : PEqualNP.MetaComplexity.FanInTwo (Circuit.mk gates o) := by
    intro g hg
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using fit g hg
  obtain ⟨k, hk, run⟩ := physicalSigned (Circuit.mk gates o) legal correct
  change k ≤ gates.countP (fun q => !isNot q) at hk
  exact (lower k (by omega) run).elim

theorem lowerGraph : Impossible true graph 11 eightInputs.toFinset :=
  (ruleFor 255 lower247 none (by decide +kernel)).property 11 eightInputs
    (by decide +kernel) (by decide +kernel)

end PEqualNP.Outside.L_meta_31153_aux

open PEqualNP.Outside.L_meta_31153_aux in
theorem PEqualNP.Outside.L_meta_31153 : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 2, 6, 4, 6, 5, 6, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 2, 6, 4, 6, 5, 6, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 2, 6, 4, 6, 5, 6, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 2, 6, 4, 6, 5, 6, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 2, 6, 4, 6, 5, 6, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 2, 6, 4, 6, 5, 6, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true))  := by
  intro gates o fit _ correct
  exact replaceShort lowerGraph gates o fit correct

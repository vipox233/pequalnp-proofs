import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_31163_aux


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
  (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 2 &&& x 5) ||| (x 3 &&& x 5) ||| (x 0 &&& x 6) ||| (x 2 &&& x 6) ||| (x 4 &&& x 6) ||| (x 5 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 2 &&& x 7) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)


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

theorem lower225 : Claim 225 5 :=
  fromLift 5 1 6291462 lower224 (by decide +kernel)

theorem lower240 : Claim 240 5 :=
  fromLift 5 16 1147535360 lower224 (by decide +kernel)

def cuts208 : Cuts (goalAt 208) := []

def state208_0 : List Sig := roots 208
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude208_0 : Impossible true (goalAt 208) 3 state208_0.toFinset :=
  node_ok cuts208 [] 0x30100501030100901030200c08030100c08030200901014040501024040504014100c04024200908024040908024200c04014100504014040908024200c08014100c08014040504014100c080242009080 (by decide +kernel)

theorem lower208 : Claim 208 4 :=
  fromSearch 1141243904 (by decide +kernel) exclude208_0

def cuts193 : Cuts (goalAt 193) := []

def state193_0 : List Sig := roots 193
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude193_0 : Impossible true (goalAt 193) 3 state193_0.toFinset :=
  node_ok cuts193 [] 0x30100410130100810130200c08030100c08030200810110404410120404414010500c04020600818020404818020600c04010500414010404818020600c08010500c08010404414010500c080206008180 (by decide +kernel)

theorem lower193 : Claim 193 4 :=
  fromSearch 6 (by decide +kernel) exclude193_0

def cuts145 : Cuts (goalAt 145) := []

def state145_0 : List Sig := roots 145
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude145_0 : Impossible true (goalAt 145) 3 state145_0.toFinset :=
  node_ok cuts145 [] 0x240401101240408101242009080240409080242008101044041101204041110044409010206008180204048180206009010044401110044048180206009080044409080044041110044409080206008180 (by decide +kernel)

theorem lower145 : Claim 145 4 :=
  fromSearch 4 (by decide +kernel) exclude145_0

def rule209_0 : {c : Cut // CutGood (goalAt 209) c} :=
  ruleFor 209 lower208 none (by decide +kernel)

def rule209_1 : {c : Cut // CutGood (goalAt 209) c} :=
  ruleFor 209 lower193 none (by decide +kernel)

def rule209_2 : {c : Cut // CutGood (goalAt 209) c} :=
  ruleFor 209 lower145 none (by decide +kernel)

def cuts209 : Cuts (goalAt 209) := [rule209_0,rule209_1,rule209_2]

def state209_0 : List Sig := roots 209
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude209_0 : Impossible true (goalAt 209) 5 state209_0.toFinset :=
  node_ok cuts209 [] 0x40008c04014040c04040008901030200c08040008c04030200c08040008901014040501040004901014100504040004c04024200908040004901024200908040004c04014100504040004501024200908040004c08014100c08040004501014100504040004c08024200908040000810110500414040000c04020600818040000810120600818040000c04010500414040000410120600818040000c08010500c08040000410110500414040000c080206008180400001101206008180400009080044409080400001101044401110400009080206008180 (by decide +kernel)

theorem lower209 : Claim 209 6 :=
  fromSearch 4 (by decide +kernel) exclude209_0

theorem lower177 : Claim 177 5 :=
  fromLift 5 32 7340036 lower145 (by decide +kernel)

def cuts81 : Cuts (goalAt 81) := []

def state81_0 : List Sig := roots 81
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude81_0 : Impossible true (goalAt 81) 3 state81_0.toFinset :=
  node_ok cuts81 [] 0x140401101140404101141005040140405040141004101044041101104041110044405010105004140104044140105005010044401110044044140105005040044405040044041110044405040105004140 (by decide +kernel)

theorem lower81 : Claim 81 4 :=
  fromSearch 4 (by decide +kernel) exclude81_0

theorem lower113 : Claim 113 5 :=
  fromLift 5 32 6291460 lower81 (by decide +kernel)

def rule241_0 : {c : Cut // CutGood (goalAt 241) c} :=
  ruleFor 241 lower225 none (by decide +kernel)

def rule241_1 : {c : Cut // CutGood (goalAt 241) c} :=
  ruleFor 241 lower224 none (by decide +kernel)

def rule241_2 : {c : Cut // CutGood (goalAt 241) c} :=
  ruleFor 241 lower240 none (by decide +kernel)

def rule241_3 : {c : Cut // CutGood (goalAt 241) c} :=
  ruleFor 241 lower209 none (by decide +kernel)

def rule241_4 : {c : Cut // CutGood (goalAt 241) c} :=
  ruleFor 241 lower177 none (by decide +kernel)

def rule241_5 : {c : Cut // CutGood (goalAt 241) c} :=
  ruleFor 241 lower113 none (by decide +kernel)

def rule241_6 : {c : Cut // CutGood (goalAt 241) c} :=
  ruleFor 241 lower145 none (by decide +kernel)

def rule241_7 : {c : Cut // CutGood (goalAt 241) c} :=
  ruleFor 241 lower208 none (by decide +kernel)

def rule241_8 : {c : Cut // CutGood (goalAt 241) c} :=
  ruleFor 241 lower81 none (by decide +kernel)

def rule241_9 : {c : Cut // CutGood (goalAt 241) c} :=
  ruleFor 241 lower193 none (by decide +kernel)

def cuts241 : Cuts (goalAt 241) := [rule241_0,rule241_1,rule241_2,rule241_3,rule241_4,rule241_5,rule241_6,rule241_7,rule241_8,rule241_9]

def state241_0 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaa,input 7,input 6,0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_0 : Impossible true (goalAt 241) 4 state241_0.toFinset :=
  node_ok cuts241 [] 0x2420081800c484818024200c0801410090801410090802420050400c4c0908024201000920600c0801050081801050081802060041400c4c0818020601000330100c080302004121144c09130 (by decide +kernel)

def state241_1 : List Sig := [0xffffffffffffffffaaaaaaaaaaaaaaaa,input 7,input 6,0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_1 : Impossible true (goalAt 241) 4 state241_1.toFinset :=
  node_ok cuts241 [] 0x908020600312120600908030200504024200504024200908014100818030200414020600414020600818010500d13030200c080244c0504024200504024200414020600414020600313030200412130200c040 (by decide +kernel)

def state241_2 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa,0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_2 : Impossible true (goalAt 241) 4 state241_2.toFinset :=
  node_ok cuts241 [] 0x90802820031212420090803020050402420050402420090801410031212420090800c484818020600414028200414028200a08010500412128200a0804001cc04030200c0800c4c0313030200c0800c4c0b030 (by decide +kernel)

def state241_3 : List Sig := [0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa,input 6,0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_3 : Impossible true (goalAt 241) 5 state241_3.toFinset :=
  node_ok cuts241 [⟨state241_0,exclude241_0⟩,⟨state241_1,exclude241_1⟩,⟨state241_2,exclude241_2⟩] 0xb03014100504030100908024200b0302420090803010050401410100072420090802820031212820100010c484312128200908024201000624200908010484504014101000114100504010484908024200313024200908040024504014100313014100504040024908024200b03010500414030100a08028200b03028200a08030100414010500412128200a0804001c414010500412110500414040018a0802820031302820081804000c41402060031301050041404000ca08028200c04010484c0402c0c100062c0c0c04080008c0402c0c041212c0c1000240008c08030100313030100b03080004913030102000030100b0300c4c03130 (by decide +kernel)

def state241_4 : List Sig := [0xffffffffffffffff0000000000000000aaaaaaaaaaaaaaaa,input 6,input 7,0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_4 : Impossible true (goalAt 241) 4 state241_4.toFinset :=
  node_ok cuts241 [] 0x908020600312120600504024200908014100908014100504024200414020600818010500818010500414020600c040344c0c040144c0908014100908014100818010500818010500313030100812130100c080 (by decide +kernel)

def state241_5 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_5 : Impossible true (goalAt 241) 4 state241_5.toFinset :=
  node_ok cuts241 [] 0x90802060031212060050402420090801410090803020050402420031212420090800c48441402060081801810081803020060402060081212060081804001c313030100c0400c4c0c04030200c0800c4c07030 (by decide +kernel)

def state241_6 : List Sig := [0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 7,0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_6 : Impossible true (goalAt 241) 5 state241_6.toFinset :=
  node_ok cuts241 [⟨state241_0,exclude241_0⟩,⟨state241_4,exclude241_4⟩,⟨state241_5,exclude241_5⟩] 0x100081c0c0703020484c08030202000230200c0802048470301c0c200011c0c051300c4c0c08030202000030200c0800c4c070300c4c070302420090803020050403020070301410050403020090802420100072420090802060031212060100010c48431212060090802060100081410050402048490802420100012420090802048450401410031301410050404002490802420031302420090804002450401410070302060081803020060403020070301810060403020081802060081211810060404001c81802060081212060081804002060401810031301810041404000c81802060031302060081804000c604018101000240008c040 (by decide +kernel)

def state241_7 : List Sig := [0x55555555000000005555555500000000555555550000000000000000,input 6,input 7,input 0,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_7 : Impossible true (goalAt 241) 4 state241_7.toFinset :=
  node_ok cuts241 [] 0x504024200908014100908030200504024200312124200313024200313030100812130100313030200412130200c04030200c0801c0c090800c484908028200818018100a08028200604028200604030200a080 (by decide +kernel)

def state241_8 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,input 7,0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,input 0,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_8 : Impossible true (goalAt 241) 5 state241_8.toFinset :=
  node_ok cuts241 [⟨state241_0,exclude241_0⟩,⟨state241_2,exclude241_2⟩,⟨state241_5,exclude241_5⟩,⟨state241_7,exclude241_7⟩] 0x24200a0800c484908014100908024200504024200c0801410090800c48490802420031210c48490800c4c090802060031303010200023010031303020200013020031304000a00000c4c0604028200a08018100a08030200604028202000328200a0804001cb03030100c080400187030 (by decide +kernel)

def state241_9 : List Sig := [0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,input 0,input 4,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_9 : Impossible true (goalAt 241) 6 state241_9.toFinset :=
  node_ok cuts241 [⟨state241_3,exclude241_3⟩,⟨state241_6,exclude241_6⟩,⟨state241_8,exclude241_8⟩] 0x40020c0401c0c0c04040018b03030200c08080008c04030200c08040018b0301c0c0703040020b03014100504040024c04024200908040004b03024200908040020c04014100504040018703024200908040024c08014100c08040004703014100504040018c0802420090804001d000724200908040024a0800c484a0804001d00010c484312140024a0802420090804000881210c4c0313040008c04040008c04040008812180004812140008c0400c4c0c0404000841210c4c0313040008c08040008c08040008412180000412140008c0800c4c0c0804000831214002431214000890800c4c090804000831210c4c031304000890804000890804000d00034000c818040020b0301810060404001cc04028200a0804001cb03028200a08040020c04018100604040018703028200a0804001cc08018100c0804001c703018100604040018c08028200a080 (by decide +kernel)

def state241_10 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffffffff0000ffff0000,input 7,input 6,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_10 : Impossible true (goalAt 241) 4 state241_10.toFinset :=
  node_ok cuts241 [] 0x2060090800c4c0818020600c0801050081801050081802060041400c484818020601000724200c0801410090801410090802420050400c484908024201000330100c080302005030144849121 (by decide +kernel)

def state241_11 : List Sig := [0xffffffffffffffffffff0000ffff0000,input 7,input 6,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_11 : Impossible true (goalAt 241) 4 state241_11.toFinset :=
  node_ok cuts241 [] 0x818024200313020600818030200414020600414020600818010500908030200504024200504024200908014100503030200c080140c0414020600414020600504024200504024200503030200503030200c040 (by decide +kernel)

def state241_12 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_12 : Impossible true (goalAt 241) 4 state241_12.toFinset :=
  node_ok cuts241 [] 0x81802820031302060081803020041402060041402060081801050031302060081800c4c0908024200504028200504028200a08014100503028200a08040024c04030200c0800c484503030200c0800c4849030 (by decide +kernel)

def state241_13 : List Sig := [0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 6,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 0,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_13 : Impossible true (goalAt 241) 5 state241_13.toFinset :=
  node_ok cuts241 [⟨state241_10,exclude241_10⟩,⟨state241_11,exclude241_11⟩,⟨state241_12,exclude241_12⟩] 0xa12110500414030100818020600a1212060081803010041401050100092060081802820031302820100010c4c03130282008180206010006206008180140c04140105010001105004140140c081802060031212060081804001c41401050031211050041404001c818020600903014100504030100a08028200903028200a08030100504014100503028200a08040024504014100503014100504040018a0802820031212820090804000c50402420031211410050404000ca08028200c040140c0c040240c10006240c0c04080008c040240c05030140c1000040000c08030100312130100a12180004912130102000030100a1210c484a030 (by decide +kernel)

def state241_14 : List Sig := [0xffffffffffffffff0000000000000000ffff0000ffff0000,input 6,input 7,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_14 : Impossible true (goalAt 241) 4 state241_14.toFinset :=
  node_ok cuts241 [] 0x818024200313020600414020600818010500818010500414020600504024200908014100908014100504024200c040240c0c040240c0818010500818010500908014100908014100903030100903030100c080 (by decide +kernel)

def state241_15 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_15 : Impossible true (goalAt 241) 4 state241_15.toFinset :=
  node_ok cuts241 [] 0x81802420031302060041402060081801050081803020041402060031302060081800c4c0504024200908018100908030200604024200903024200908040024903030100c0400c484c04030200c0800c4845030 (by decide +kernel)

def state241_16 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 7,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 0,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_16 : Impossible true (goalAt 241) 5 state241_16.toFinset :=
  node_ok cuts241 [⟨state241_10,exclude241_10⟩,⟨state241_14,exclude241_14⟩,⟨state241_15,exclude241_15⟩] 0x10008140c05030240c0c08030202000230200c080240c05030140c200011848451210c484c08030202000030200c0800c4846121180c061212060081803020041403020061211050041403020081802060100092060081802420031302420100010c4c03130242008180206010008105004140240c08180206010001206008180240c041401050031211050041404001c81802060031212060081804001c41401050050302420090803020060403020050301810060403020090802420090301810060404002490802420090302420090804002060401810031211810050404000c90802420031212420090804000c604018101000040000c040 (by decide +kernel)

def state241_17 : List Sig := [0xffff000000000000ffff000000000000ffff0000000000000000,input 6,input 7,input 4,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_17 : Impossible true (goalAt 241) 4 state241_17.toFinset :=
  node_ok cuts241 [] 0x81800c4c0313020600414020600818010500818030200414020600903030100903030100503030200503030200c04030200c080140c081800c4c0818028200908018100a08028200604028200604030200a080 (by decide +kernel)

def state241_18 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,input 7,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_18 : Impossible true (goalAt 241) 5 state241_18.toFinset :=
  node_ok cuts241 [⟨state241_10,exclude241_10⟩,⟨state241_12,exclude241_12⟩,⟨state241_15,exclude241_15⟩,⟨state241_17,exclude241_17⟩] 0x2060031300c4c0818020600a0800c4c0818010500818020600414020600c0801050081800c4c081802060031302420031213010200023010031213020200013020031214000200000c484604028200a08018100a08030200604028202000328200a08040024903030100c080400185030 (by decide +kernel)

def state241_19 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,input 0,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_19 : Impossible true (goalAt 241) 6 state241_19.toFinset :=
  node_ok cuts241 [⟨state241_13,exclude241_13⟩,⟨state241_16,exclude241_16⟩,⟨state241_18,exclude241_18⟩] 0x40020c040140c0c04040018903030200c08080008c04030200c080400189030140c0503040020a1211050041404001cc04020600818040004a12120600818040020c0401050041404001861212060081804001cc08010500c08040004612110500414040018c0802060081804000031212060081804000100070c4c031304000031210c4c0313040001000020600818040025000920600818040024a0800c4c0a0804002500010c4c0313040024a0802060081804000090300c484903040000c04040000c04040000903080004903040000c0400c484c0404000050300c484503040000c08040000c08040000503080000503040000c0800c484c0804000d00034000c908040020903018100604040024c04028200a08040024903028200a08040020c04018100604040018503028200a08040024c08018100c08040024503018100604040018c08028200a080 (by decide +kernel)

def state241_20 : List Sig := [0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000aaaa0000aaaa,input 7,input 0,input 6,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_20 : Impossible true (goalAt 241) 4 state241_20.toFinset :=
  node_ok cuts241 [] 0x28200c08018100a08018100a08028200604030100c08030200703020600a0800c4c0818020600c080105008180105008180206004140242003121282009080242005040302009080206003130206009080141009080242005040 (by decide +kernel)

def state241_21 : List Sig := [0xffffffff00000000ffffffff00000000ffffffff00000000aaaaaaaa,input 7,input 0,input 6,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_21 : Impossible true (goalAt 241) 4 state241_21.toFinset :=
  node_ok cuts241 [] 0x24200c08014100908014100908024200504030100c0803020070302060090800c4c0818020600c08010500818010500818020600414024200312124200a08028200604030200a08020600313020600a08018100a080282006040 (by decide +kernel)

def state241_22 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaa,input 7,input 0,input 6,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_22 : Impossible true (goalAt 241) 5 state241_22.toFinset :=
  node_ok cuts241 [⟨state241_0,exclude241_0⟩,⟨state241_20,exclude241_20⟩,⟨state241_21,exclude241_21⟩] 0xa08030200604028200604028200a08018102000228200a0804000c908028200312124200908030200504024200504024200908014102000124200908040000c04030200c08018484703020600a0808000081802060090800c484818020600c0801050081801050081802060041400c4c0b030 (by decide +kernel)

def state241_23 : List Sig := [0xffffffffffffffffaaaaaaaaaaaaaaaa,input 7,input 0,input 6,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_23 : Impossible true (goalAt 241) 5 state241_23.toFinset :=
  node_ok cuts241 [⟨state241_1,exclude241_1⟩] 0xa08030200604028200604028200a08018100908028200312124200908030200504024200504024200908014100f03030200c0802c0c0818028202000020600818024200312120600818030200414020600414020600818010500604028200604028200504024200504024200703030200612130200414020600414020600c040 (by decide +kernel)

def state241_24 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_24 : Impossible true (goalAt 241) 4 state241_24.toFinset :=
  node_ok cuts241 [] 0x28200818018100818018100a08028200414018484a08028200412124200a0800c48490802420081801410081801410090802420041400c48490802420031211050081802060100051c0c0818020600a0212c0c04140105006021 (by decide +kernel)

def state241_25 : List Sig := [0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 7,0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa,input 6,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_25 : Impossible true (goalAt 241) 5 state241_25.toFinset :=
  node_ok cuts241 [⟨state241_24,exclude241_24⟩] 0x28200604018100a08028200818018100818018100a08028200604018100a08028200414024200a0800c484908024200504014100908024200818014100818014100908024200504014100908024200414030200612128486000018484414018484414018084a12120600818028084414020600818040014c040 (by decide +kernel)

def state241_26 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa,input 0,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_26 : Impossible true (goalAt 241) 5 state241_26.toFinset :=
  node_ok cuts241 [⟨state241_24,exclude241_24⟩,⟨state241_2,exclude241_2⟩] 0x28200c08018100a08018100a08028200604018484a08028200412124200a0800c484908024200c0801410090801410090802420050400c484908024200312110500a08080004a0801050090800c484908020600414020502000010500612110500414018084c04030200c08040014703030200c08040014b030 (by decide +kernel)

def state241_27 : List Sig := [0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa,input 0,input 6,input 4,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_27 : Impossible true (goalAt 241) 6 state241_27.toFinset :=
  node_ok cuts241 [⟨state241_3,exclude241_3⟩,⟨state241_22,exclude241_22⟩,⟨state241_23,exclude241_23⟩,⟨state241_25,exclude241_25⟩,⟨state241_26,exclude241_26⟩] 0xb03018100604030100a08028200b03028200a08030100604018100612128200a08010404604018100612118100604010404a08028201000628200a0804000c60401810100061810060404000ca08028200b03014100504030100908024200b0302420090803010050401410100062420090802820031212820100010c484312128200908024201000424200908018484504014101000114100504018484908024201000124200908040000504014101000114100504040000908024200c04018484c0402c0c100042c0c0c04080010c0402c0c061212c0c1000240008c08028484414010500c04040008c04028486000328484c04010500414040008414010500a08040008a08040009000680000a08010500a0800c48441401050090804000890800c48500010c484908010500908018485000418485000210500414040009000218085000240010818030101000530100b03080008b03030102000130100b03040014b030 (by decide +kernel)

def state241_28 : List Sig := [0xffffffffffffffff0000000000000000aaaaaaaaaaaaaaaa,input 6,input 0,input 7,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_28 : Impossible true (goalAt 241) 5 state241_28.toFinset :=
  node_ok cuts241 [⟨state241_4,exclude241_4⟩] 0x604028200a08018100a08018100604028200908028200312124200504024200908014100908014100504024200818028202000020600818024200312120600414020600818010500818010500414020600c0403c0c0c0401c0c0a08018100a08018100908014100908014100b03030100a12130100818010500818010500c080 (by decide +kernel)

def state241_29 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 0,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_29 : Impossible true (goalAt 241) 5 state241_29.toFinset :=
  node_ok cuts241 [⟨state241_24,exclude241_24⟩,⟨state241_5,exclude241_5⟩] 0x18100a08028200604028200c08018100a08028484a08028200812124200a0800c484908014100908024200504024200c0801410090800c484908024200312120600a0808000481802060090800c484818010500818030202000020600a12120600818028084b03030100c04040008c04030200c080400107030 (by decide +kernel)

def state241_30 : List Sig := [0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 0,input 7,input 4,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_30 : Impossible true (goalAt 241) 6 state241_30.toFinset :=
  node_ok cuts241 [⟨state241_6,exclude241_6⟩,⟨state241_25,exclude241_25⟩,⟨state241_22,exclude241_22⟩,⟨state241_28,exclude241_28⟩,⟨state241_29,exclude241_29⟩] 0x100051c0c0703028484c08030202000430200c0802848470301c0c200031c0c0703040010c08030202000230200c0804001070301c0c0703028200a08030200604030200703018100604030200a08028200a12118100604020404a08028200a12128200a0802040460401810100081810060404000ca08028201000828200a0804000c60401810070302420090803020050403020070301410050403020090802420100082420090802820031212820100010c484312128200908024201000514100504028484908024201000124200908028484504014101000114100504040000908024201000124200908040000504014101000540008c04018484818020600c08040008c08018486000118484c08020600818040008818020600a08040008a08040009000880000a0802060081800c48481802060090804000890800c48500010c4849080206008180284850005284850002206008180400150005280850005400144140 (by decide +kernel)

def state241_31 : List Sig := [0x5555555555555555555555555555555555555555555555555555000055550000,input 7,input 4,input 6,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_31 : Impossible true (goalAt 241) 4 state241_31.toFinset :=
  node_ok cuts241 [] 0x28200c08018100a08018100a08028200604030100c08030200703024200a0800c484908024200c080141009080141009080242005040206003130282008180206004140302008180206003130242008180105008180206004140 (by decide +kernel)

def state241_32 : List Sig := [0xffffffff00000000ffffffff00000000ffffffff00000000ffff0000,input 7,input 4,input 6,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_32 : Impossible true (goalAt 241) 4 state241_32.toFinset :=
  node_ok cuts241 [] 0x20600c0801050081802060090800c4c0818010500818020600414030100c08030200703024200c08014100908014100908024200504020600313020600a08028200604030200a08024200312124200a08018100a080282006040 (by decide +kernel)

def state241_33 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffffffff0000ffff0000,input 7,input 4,input 6,input 0,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_33 : Impossible true (goalAt 241) 5 state241_33.toFinset :=
  node_ok cuts241 [⟨state241_10,exclude241_10⟩,⟨state241_31,exclude241_31⟩,⟨state241_32,exclude241_32⟩] 0xa08030200604028200604028200a08018102000228200a0804000c818028200313020600818030200414020600818024200313020600414020600818010502000120600818040008c04030200c0801c0c0612124200a08080000908024200c0801410090801410090802420050400c484a121 (by decide +kernel)

def state241_34 : List Sig := [0xffffffffffffffffffff0000ffff0000,input 7,input 4,input 6,input 0,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_34 : Impossible true (goalAt 241) 5 state241_34.toFinset :=
  node_ok cuts241 [⟨state241_11,exclude241_11⟩] 0xa08030200604028200604028200a08018100818028200313020600818030200414020600818024200313020600414020600818010500703030200c0801c0c0908028202000024200908030200504024200504024200908014100604028200604028200414020600414020600703030200703030200504024200504024200c040 (by decide +kernel)

def state241_35 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 0,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_35 : Impossible true (goalAt 241) 4 state241_35.toFinset :=
  node_ok cuts241 [] 0x28200908018100908018100a0802820050401c0c0a08028200503020600a0800c4c081802060090801050081801050081802060041400c4c081802060031301410090802420100051c0c0908024200a0301c0c05040141006030 (by decide +kernel)

def state241_36 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 7,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 6,input 0,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_36 : Impossible true (goalAt 241) 5 state241_36.toFinset :=
  node_ok cuts241 [⟨state241_35,exclude241_35⟩] 0x28200604018100a08028200908018100908018100a08028200604018100a08028200504020600a0800c4c081802060041401050081802060090801050081801050081802060041401050081802060041403020070302c0c200001c0c050401c0c05040180c0b030242009080280c0504024200908040014c040 (by decide +kernel)

def state241_37 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 4,input 0,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_37 : Impossible true (goalAt 241) 5 state241_37.toFinset :=
  node_ok cuts241 [⟨state241_35,exclude241_35⟩,⟨state241_12,exclude241_12⟩] 0x28200c08018100a08018100a0802820060401c0c0a08028200503020600a0800c4c081802060050400c4c0818020600c0801050081801050081802060041400c4c0818020600313014100a08080004a080242005040241020000141007030141005040180c0c04030200c08040014703030200c08040000b030 (by decide +kernel)

def state241_38 : List Sig := [0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 4,input 6,input 0,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_38 : Impossible true (goalAt 241) 6 state241_38.toFinset :=
  node_ok cuts241 [⟨state241_13,exclude241_13⟩,⟨state241_33,exclude241_33⟩,⟨state241_34,exclude241_34⟩,⟨state241_36,exclude241_36⟩,⟨state241_37,exclude241_37⟩] 0xb03018100604030100a08028200b03028200a08030100604018100703028200a08014040604018100703018100604014040a08028201000628200a0804000c60401810100061810060404000ca08028200a12110500414030100818020600a1212060081803010041401050100062060081802820031302820100010c4c031302820081802060100042060081801c0c041401050100011050041401c0c081802060100002060081801410031301410100010c4c0313014100818020601000120600818040008414010501000110500414040008818020600c0401c0c0c0402c0c100042c0c0c04080010c0402c0c070301c0c1000040000c0802c0c0504014100c04040000c0402c0c200032c0c0c04014100504040000504014100a08040000a08040001000680000a08014100a0801c0c100041c0c10000141005040400010000180c1000040010908030101000530100a12180008a12130102000130100a12140014a121 (by decide +kernel)

def state241_39 : List Sig := [0xffffffffffffffff0000000000000000ffff0000ffff0000,input 6,input 4,input 7,input 0,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_39 : Impossible true (goalAt 241) 5 state241_39.toFinset :=
  node_ok cuts241 [⟨state241_14,exclude241_14⟩] 0x604028200a08018100a08018100604028200818028200313020600414020600818010500818024200313020600818010500414020600908028202000024200504024200908014100908014100504024200c0402c0c0c0402c0c0a08018100a08018100818010500818010500b03030100b03030100908014100908014100c080 (by decide +kernel)

def state241_40 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 4,input 0,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_40 : Impossible true (goalAt 241) 5 state241_40.toFinset :=
  node_ok cuts241 [⟨state241_35,exclude241_35⟩,⟨state241_15,exclude241_15⟩] 0x18100a08028200604028200c08018100a0802c0c0a08028200903020600a0800c4c081802060090800c4c0818010500818020600414020600c0801050081800c4c0818020600313024200a08080004908014100908030202000024200b030242009080280c0b03030100c04040000c04030200c080400107030 (by decide +kernel)

def state241_41 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 4,input 7,input 0,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_41 : Impossible true (goalAt 241) 6 state241_41.toFinset :=
  node_ok cuts241 [⟨state241_16,exclude241_16⟩,⟨state241_36,exclude241_36⟩,⟨state241_33,exclude241_33⟩,⟨state241_39,exclude241_39⟩,⟨state241_40,exclude241_40⟩] 0x100051c0c070302c0c0c08030202000430200c0802c0c070301c0c2000318484612140010c08030202000230200c08040010612118484703028200a08030200604030200703018100604030200a08028200b03018100604024040a08028200b03028200a0802404060401810100081810060404000ca08028201000828200a0804000c60401810061212060081803020041403020061211050041403020081802060100082060081802820031302820100010c4c031302820081802060100051050041402c0c081802060100012060081802c0c041401050100002060081802420031302420100010c4c0313024200818020601000110500414040008818020601000120600818040008414010501000040000c0401c0c0908024200c08040000c0801c0c200011c0c0c08024200908040000908024200a08040000a08040001000880000a0802420090802c0c100052c0c10000242009080400010000280c10000400145040 (by decide +kernel)

def state241_42 : List Sig := [0xaaaa0000ffff0000aaaa0000ffff0000aaaa0000ffff0000aaaa0000aaaa,input 0,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_42 : Impossible true (goalAt 241) 3 state241_42.toFinset :=
  node_ok cuts241 [] 0x30100c08030200503010500818020600414020600c080105008180141009080242005040242005040302009080206003130206009080 (by decide +kernel)

def state241_43 : List Sig := [0xaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaaaaaaaaa,input 0,input 6,input 7,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_43 : Impossible true (goalAt 241) 4 state241_43.toFinset :=
  node_ok cuts241 [⟨state241_42,exclude241_42⟩] 0x504024200908014100908030200504024200c04030200c0801c0c0818024200312120600414020600818010500818030200414020600313024202000024200a08018100a08028200604028200604030200a080 (by decide +kernel)

def state241_44 : List Sig := [0x5555000055555555555500005555555555550000555555555555000055550000,input 4,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_44 : Impossible true (goalAt 241) 3 state241_44.toFinset :=
  node_ok cuts241 [] 0x30100c08030200503014100908024200504024200c080141009080105008180206004140206004140302008180206003130242008180 (by decide +kernel)

def state241_45 : List Sig := [0xffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffff0000,input 4,input 6,input 7,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_45 : Impossible true (goalAt 241) 4 state241_45.toFinset :=
  node_ok cuts241 [⟨state241_44,exclude241_44⟩] 0x414020600818010500818030200414020600818024200313020602000020600818028200c04030200c080140c0504024200908014100908030200504024200312118100a08028200604028200604030200a080 (by decide +kernel)

def state241_46 : List Sig := [0xffffffff00000000ffffffff00000000ffffffff0000000000000000,input 6,input 7,input 0,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_46 : Impossible true (goalAt 241) 5 state241_46.toFinset :=
  node_ok cuts241 [⟨state241_7,exclude241_7⟩,⟨state241_17,exclude241_17⟩,⟨state241_43,exclude241_43⟩,⟨state241_45,exclude241_45⟩] 0x2c0c0504014100c0402420090802c0c0908024200c0401410050401c0c0908024200c08014100c0801c0c0504014100c0802420090800c48481802060090800c4c090800c48431300c4c0908020600818028484414010500c04020600818028484818020600c04010500414018484818020600c08010500c08018484414010500c08020600818030100703030100b03030200c08030100c08030200b0301c0c0703024200a08024200312180004312124202000324200312128200a08020600a08020600313080000313020602000220600313028200a08030100604018100b03028200a08030100a08028200b03018100604030200a08028200703018100604030200604030200703028200a080 (by decide +kernel)

def state241_47 : List Sig := [0x5555555555555555555555555555555555555555555555550000000000000000,input 0,input 6,input 7,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_47 : Impossible true (goalAt 241) 5 state241_47.toFinset :=
  node_ok cuts241 [⟨state241_7,exclude241_7⟩] 0x604028200a08018100a08030200604028200908028200312124200504024200908014100908030200504024200c04030200c08018484111028200313028200312124200313024200313030100a12130100313030200612130200a08080000a0804000c90800c48490800c484c0402c0c0c04028484c0801c0c0c080184848180 (by decide +kernel)

def state241_48 : List Sig := [0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000,input 4,input 6,input 7,input 0,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_48 : Impossible true (goalAt 241) 5 state241_48.toFinset :=
  node_ok cuts241 [⟨state241_17,exclude241_17⟩] 0x604028200a08018100a0803020060402820081802820031302060041402060081801050081803020041402060081800c4c0313020600c04030200c0801c0c0110128200312128200b03030100b03030100703030200703030200a08080000a0804000c81800c4c081800c4c0c0402c0c0c0402c0c0c0801c0c0c0801c0c09080 (by decide +kernel)

def state241_49 : List Sig := [0xffffffff00000000ffffffff00000000ffffffff0000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,input 7,input 0,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_49 : Impossible true (goalAt 241) 5 state241_49.toFinset :=
  node_ok cuts241 [] 0x14100908024200504024200c0801410090800c48490802420031212060090800c4c0818010500818020600414020600c0801050081800c4c081802060031302c0c0c0403020100061c0c090800c48490802820081800c4c0818028200604028200a08018100a08018100c080282010003 (by decide +kernel)

def state241_50 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,input 7,input 0,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_50 : Impossible true (goalAt 241) 6 state241_50.toFinset :=
  node_ok cuts241 [⟨state241_22,exclude241_22⟩,⟨state241_26,exclude241_26⟩,⟨state241_29,exclude241_29⟩,⟨state241_8,exclude241_8⟩,⟨state241_33,exclude241_33⟩,⟨state241_37,exclude241_37⟩,⟨state241_40,exclude241_40⟩,⟨state241_18,exclude241_18⟩,⟨state241_46,exclude241_46⟩,⟨state241_47,exclude241_47⟩,⟨state241_48,exclude241_48⟩,⟨state241_49,exclude241_49⟩] 0x1000518100604030100a08028201000628200a08030100604018101000428200a08030200604030201000618100604030200a0802820100068002e00084000ca08028201000628200a0804000d00064000d00062420090802820031212820200070c484312128200908024201000514100504030100908024202000624200908030100504014101000424200908030200504030202000514100504030200908024202000a0c48431214000090802420200042420090804000031210c48500062060081802820031302820200030c4c031302820081802060031212060081802420031302420031210c4c031302420081802060100051050041403010081802060200022060081803010041401050100042060081803020041403020200011050041403020081802060200090c4c031304000881802060200002060081804000831300c4c1000540010b03030101000530101000430200c080400150005400150005400147030 (by decide +kernel)

def state241_51 : List Sig := roots 241
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_51 : Impossible true (goalAt 241) 7 state241_51.toFinset :=
  node_ok cuts241 [⟨state241_9,exclude241_9⟩,⟨state241_19,exclude241_19⟩,⟨state241_27,exclude241_27⟩,⟨state241_30,exclude241_30⟩,⟨state241_38,exclude241_38⟩,⟨state241_41,exclude241_41⟩,⟨state241_50,exclude241_50⟩] 0x40014c0401c0c0c04040010b03030200c08080018c04030200c08040014b0301c0c070304000cb0301810060404000cc04028200a0804000cb03028200a0804000cc0401810060404000c703028200a0804000cc08018100c0804000c70301810060404000cc08028200a08040014b03014100504040000c04024200908080014b03024200908040000c04014100504040010703024200908040000c08014100c08080010703014100504040000c0802420090804000d00032420090804000ca0800c484a0804000e00010c48431214000ca08024200908040014a12110500414040008c0402060081808000ca12120600818040014c04010500414040010612120600818040008c08010500c08080008612110500414040008c0802060081804000d00032060081804000ca0800c4c0a0804000e00000c4c031304000ca0802060081804000031212060081804000890800c4c090804000431210c4c03130400009080206008180 (by decide +kernel)

theorem lower241 : Claim 241 8 :=
  fromSearch 6291460 (by decide +kernel) exclude241_51

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

theorem lower197 : Claim 197 5 :=
  fromLift 5 1 1542 lower196 (by decide +kernel)

theorem lower165 : Claim 165 5 :=
  fromLift 5 1 2098439 lower164 (by decide +kernel)

def cuts100 : Cuts (goalAt 100) := []

def state100_0 : List Sig := roots 100
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude100_0 : Impossible true (goalAt 100) 3 state100_0.toFinset :=
  node_ok cuts100 [] 0x180802404180804404181006040180806040181004404090102404110102420090806020111004440110104440111006020090802420090104440111006040090806040090102420090806040111004440 (by decide +kernel)

theorem lower100 : Claim 100 4 :=
  fromSearch 35652864 (by decide +kernel) exclude100_0

theorem lower101 : Claim 101 5 :=
  fromLift 5 1 2098438 lower100 (by decide +kernel)

def rule229_0 : {c : Cut // CutGood (goalAt 229) c} :=
  ruleFor 229 lower228 none (by decide +kernel)

def rule229_1 : {c : Cut // CutGood (goalAt 229) c} :=
  ruleFor 229 lower225 none (by decide +kernel)

def rule229_2 : {c : Cut // CutGood (goalAt 229) c} :=
  ruleFor 229 lower193 none (by decide +kernel)

def rule229_3 : {c : Cut // CutGood (goalAt 229) c} :=
  ruleFor 229 lower197 none (by decide +kernel)

def rule229_4 : {c : Cut // CutGood (goalAt 229) c} :=
  ruleFor 229 lower165 none (by decide +kernel)

def rule229_5 : {c : Cut // CutGood (goalAt 229) c} :=
  ruleFor 229 lower101 none (by decide +kernel)

def rule229_6 : {c : Cut // CutGood (goalAt 229) c} :=
  ruleFor 229 lower224 none (by decide +kernel)

def rule229_7 : {c : Cut // CutGood (goalAt 229) c} :=
  ruleFor 229 lower196 none (by decide +kernel)

def rule229_8 : {c : Cut // CutGood (goalAt 229) c} :=
  ruleFor 229 lower164 none (by decide +kernel)

def rule229_9 : {c : Cut // CutGood (goalAt 229) c} :=
  ruleFor 229 lower100 none (by decide +kernel)

def cuts229 : Cuts (goalAt 229) := [rule229_0,rule229_1,rule229_2,rule229_3,rule229_4,rule229_5,rule229_6,rule229_7,rule229_8,rule229_9]

def state229_0 : List Sig := [0xfffffffffffffffffffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0,input 7,input 6,0xfafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafa,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_0 : Impossible true (goalAt 229) 4 state229_0.toFinset :=
  node_ok cuts229 [] 0x28200c08018100a08018100a08028200604009084a08028201000720600a08009014818020600c08010500818010500818020600414009084818020601000030100c08030200410518484a121 (by decide +kernel)

def state229_1 : List Sig := [0xfffffffffffffffff0f0f0f0f0f0f0f0,input 7,input 6,0xfafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafa,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_1 : Impossible true (goalAt 229) 4 state229_1.toFinset :=
  node_ok cuts229 [] 0xa08030200604028200604028200a08018100818028200240520600818030200414020600414020600818010500e12130200c08028484604028200604028200414020600414020600242130200410530200c040 (by decide +kernel)

def state229_2 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0,0xfafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafa,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_2 : Impossible true (goalAt 229) 4 state229_2.toFinset :=
  node_ok cuts229 [] 0xa08030200604028200604028200a08018100240528200a08009014818028200240520600818021200414020600414020600818010500410520600818040018c04030200c08009084242130200c08009084a121 (by decide +kernel)

def state229_3 : List Sig := [0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0,input 6,0xfafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafa,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_3 : Impossible true (goalAt 229) 5 state229_3.toFinset :=
  node_ok cuts229 [⟨state229_0,exclude229_0⟩,⟨state229_1,exclude229_1⟩,⟨state229_2,exclude229_2⟩] 0xa12118100604030100a08028200a12128200a08030100604018101000228200a08010414604018101000218100604010414a08028200242128200a0804001c60401810024211810060404001ca08028200a12110500414030100818020600a12120600818030100414010500240520600818028201000628200240540008240528200818020600410520600818040018414010500410510500414040018818020600242120600818040000414021200242110500414040000818020600c04010414c04028485000828484c04080008c04028484410528485000140004c08030100242130100a12180004a12130102000030100a121090842421 (by decide +kernel)

def state229_4 : List Sig := [0xffffffffffffffff0000000000000000f0f0f0f0f0f0f0f0,input 6,input 7,0xfafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafa,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_4 : Impossible true (goalAt 229) 4 state229_4.toFinset :=
  node_ok cuts229 [] 0x604028200a08018100a08018100604028200818028200240520600414020600818010500818010500414020600c04038484c04018484a08018100a08018100818010500818010500242130100810530100c080 (by decide +kernel)

def state229_5 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafa,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_5 : Impossible true (goalAt 229) 4 state229_5.toFinset :=
  node_ok cuts229 [] 0x604028200a08018100a08030200604028200240528200a08009014818028200240520600414020600818010500818030200414020600810520600818040018242130100c04009084c04030200c080090846121 (by decide +kernel)

def state229_6 : List Sig := [0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 7,0xfafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafa,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_6 : Impossible true (goalAt 229) 5 state229_6.toFinset :=
  node_ok cuts229 [⟨state229_0,exclude229_0⟩,⟨state229_4,exclude229_4⟩,⟨state229_5,exclude229_5⟩] 0x1000918484612120414c08030202000230200c08020414612118486000118484612109084c08030202000030200c08009084612109084612128200a08030200604030200612118100604030200a08028201000218100604020414a08028201000228200a0802041460401810024211810060404001ca08028200242128200a0804001c604018100612120600818030200414030200612110500414030200818020600240520600818028201000628200240540008240528200818020600810510500414040018818020600810520600818040018414010500242110500414040000818020600242120600818040000414010501000140004c040 (by decide +kernel)

def state229_7 : List Sig := [0x505050505050505050505050505050505050505050505050000000000000000,input 6,input 7,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_7 : Impossible true (goalAt 229) 4 state229_7.toFinset :=
  node_ok cuts229 [] 0x604028200a08018100a08030200604028200240528200242128200242130100810530100242130200410530200c04030200c08018484818009014a080206008480105008180206004140206004140302008180 (by decide +kernel)

def state229_8 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,input 7,0xfafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafa,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_8 : Impossible true (goalAt 229) 5 state229_8.toFinset :=
  node_ok cuts229 [⟨state229_0,exclude229_0⟩,⟨state229_2,exclude229_2⟩,⟨state229_5,exclude229_5⟩,⟨state229_7,exclude229_7⟩] 0x18100a08028200604028200c08018100a08009014a08028200240509014a08009084a08021200242130102000230100242130202000130200242140006000009084818028200240520600414020600818010500818030200414020602000320600818040018a12130100c080400206121 (by decide +kernel)

def state229_9 : List Sig := [0xfafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafa,input 2,input 5,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_9 : Impossible true (goalAt 229) 6 state229_9.toFinset :=
  node_ok cuts229 [⟨state229_3,exclude229_3⟩,⟨state229_6,exclude229_6⟩,⟨state229_8,exclude229_8⟩] 0x40024c04018484c04040020a12130200c08080008c04030200c08040020a12118484612140008a1211810060404001cc04028200a08040008a12128200a0804001cc04018100604040008612128200a0804001cc08018100c0804000861211810060404001cc08028200a08040004840509084242140004c04040004c04040004840580004810540004c04009084c04040004440509084242140004c08040004c08040004440580000410540004c08009084c0804000424054001c240540004a08009084a08040004240509084242140004a08040004a08040001000040000848040018a12110500414040018c04020600818040018a12120600818040018c04010500414040018612120600818040018c08010500c08040018612110500414040018c08020600818040018240520600818040018a08040018a08040018240540008240540018a080206008180 (by decide +kernel)

def state229_10 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000,input 7,input 6,0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_10 : Impossible true (goalAt 229) 4 state229_10.toFinset :=
  node_ok cuts229 [] 0x21200818009084818021200c08011100848011100848021200444009014848021201000620600c08010500818010500818020600414009014818020601000030100c080302004121114148505 (by decide +kernel)

def state229_11 : List Sig := [0xffffffffffffffffffffffff00000000,input 7,input 6,0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_11 : Impossible true (goalAt 229) 4 state229_11.toFinset :=
  node_ok cuts229 [] 0x848020600242120600848030200444021200444021200848011100818030200414020600414020600818010500412130200c08010484444021200444021200414020600414020600412130200412130200c040 (by decide +kernel)

def state229_12 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_12 : Impossible true (goalAt 229) 4 state229_12.toFinset :=
  node_ok cuts229 [] 0x84802060024212060084803020044402120044402120084801110024212120084800908481802820041402060041402060081801050041212060081804001cc04030200c08009014412130200c08009014a021 (by decide +kernel)

def state229_13 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 6,0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,input 2,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_13 : Impossible true (goalAt 229) 5 state229_13.toFinset :=
  node_ok cuts229 [⟨state229_10,exclude229_10⟩,⟨state229_11,exclude229_11⟩,⟨state229_12,exclude229_12⟩] 0x850511100444030100848021200850521200848030100444011101000721200848020600242120601000209084242120600848020601000221200848010484444011101000211100444010484848021200240521200848040018444011100240511100444040018848021200a02110500414030100818020600a0212060081803010041401050041212060081804001c41401050041211050041404001c818020600240520600818040000414028200240510500414040000818020600c04010484c04028085000828084c04080008c0402808441211048500034000cc080301002405301008505800048505301020000301008505090148121 (by decide +kernel)

def state229_14 : List Sig := [0xffffffffffffffff0000000000000000ffffffff00000000,input 6,input 7,0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_14 : Impossible true (goalAt 229) 4 state229_14.toFinset :=
  node_ok cuts229 [] 0x848020600242120600444021200848011100848011100444021200414020600818010500818010500414020600c04020484c04020484848011100848011100818010500818010500812130100812130100c080 (by decide +kernel)

def state229_15 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_15 : Impossible true (goalAt 229) 4 state229_15.toFinset :=
  node_ok cuts229 [] 0x84802060024212060044402120084801110084803020044402120024212120084800908441402060081801050081803020041402060081212060081804001c812130100c04009014c04030200c080090146021 (by decide +kernel)

def state229_16 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 7,0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_16 : Impossible true (goalAt 229) 5 state229_16.toFinset :=
  node_ok cuts229 [⟨state229_10,exclude229_10⟩,⟨state229_14,exclude229_14⟩,⟨state229_15,exclude229_15⟩] 0x1000918084602120484c08030202000230200c08020484602118086000111414450509014c08030202000030200c0800901445051048445052120084803020044403020045051110044403020084802120100072120084802060024212060100020908424212060084802060100021110044402048484802120100022120084802048444401110024051110044404001884802120024052120084804001844401110060212060081803020041403020060211050041403020081802060081211050041404001c81802060081212060081804001c41401050024051050041404000081802060024052060081804000041401050100034000cc040 (by decide +kernel)

def state229_17 : List Sig := [0x55555555000000005555555500000000555555550000000000000000,input 6,input 7,input 5,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_17 : Impossible true (goalAt 229) 4 state229_17.toFinset :=
  node_ok cuts229 [] 0x848009084242121200444021200848011100848030200444021200a02130100812130100602130200412130200c04030200c08018084818009084848020600a080105008180206004140206004140302008180 (by decide +kernel)

def state229_18 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,input 7,0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,input 5,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_18 : Impossible true (goalAt 229) 5 state229_18.toFinset :=
  node_ok cuts229 [⟨state229_10,exclude229_10⟩,⟨state229_12,exclude229_12⟩,⟨state229_15,exclude229_15⟩,⟨state229_17,exclude229_17⟩] 0x21200242109084848021200818009084818011100848021200444021200c0801110084800908484802120024212820024053010200023010024053020200013020024054000e00000901441402060081801050081803020041402060200032060081804001ca02130100c080400206021 (by decide +kernel)

def state229_19 : List Sig := [0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,input 5,input 2,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_19 : Impossible true (goalAt 229) 6 state229_19.toFinset :=
  node_ok cuts229 [⟨state229_13,exclude229_13⟩,⟨state229_16,exclude229_16⟩,⟨state229_18,exclude229_18⟩] 0x40024c04018084c04040020a02130200c08080008c04030200c08040020a02118084602140008850511100444040018c04021200848040008850521200848040018c04011100444040008450521200848040018c08011100c08040008450511100444040018c0802120084804000c24052120084804000d00060908424214000c24050908424214000d00032120084804001d00072120084804001881800908481804001d00020908424214001881802120081804000ca02109014a0214000cc0404000cc0404000ca0218000481214000cc04009014c0404000c60210901460214000cc0804000cc0804000c60218000041214000cc08009014c08040001000040000a0804001ca0211050041404001cc0402060081804001ca0212060081804001cc0401050041404001c60212060081804001cc08010500c0804001c60211050041404001cc080206008180 (by decide +kernel)

def state229_20 : List Sig := [0x5555555555555555555555555555555555555555555555555050505050505050,input 7,input 2,input 6,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_20 : Impossible true (goalAt 229) 4 state229_20.toFinset :=
  node_ok cuts229 [] 0x28200c08018100a08018100a08028200604030100c08030200612121200a08009484848021200c080111008480111008480212004440206002405282008180206004140302008180206002421212008180105008180206004140 (by decide +kernel)

def state229_21 : List Sig := [0xffffffff00000000ffffffff00000000ffffffff00000000f0f0f0f0,input 7,input 2,input 6,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_21 : Impossible true (goalAt 229) 4 state229_21.toFinset :=
  node_ok cuts229 [] 0x20600c08010500818020600848009084818010500818020600414030100c08030200612121200c08011100848011100848021200444020600240520600a08028200604030200a08021200252121200a08018100a080282006040 (by decide +kernel)

def state229_22 : List Sig := [0xfffffffffffffffffffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0,input 7,input 2,input 6,input 0,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_22 : Impossible true (goalAt 229) 5 state229_22.toFinset :=
  node_ok cuts229 [⟨state229_0,exclude229_0⟩,⟨state229_20,exclude229_20⟩,⟨state229_21,exclude229_21⟩] 0xa08030200604028200604028200a08018102000228200a0804000c818028200240520600818030200414020600818021202000020600414020600818010502000120600818040000c04030200c08011414612121200a08009414848021200c08011100848011100848021200444009484a121 (by decide +kernel)

def state229_23 : List Sig := [0xfffffffffffffffff0f0f0f0f0f0f0f0,input 7,input 2,input 6,input 0,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_23 : Impossible true (goalAt 229) 5 state229_23.toFinset :=
  node_ok cuts229 [⟨state229_1,exclude229_1⟩] 0xa08030200604028200604028200a08018100818028200240520600818030200414020600818021202000020600414020600818010500e12130200c08028484848028200250521200848030200444021200444021200848011100604028200604028200414020600414020600612130200450530200444021200444021200c040 (by decide +kernel)

def state229_24 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0,input 0,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_24 : Impossible true (goalAt 229) 4 state229_24.toFinset :=
  node_ok cuts229 [] 0x28200848018100848018100a08028200444009414a08028200250520600a080090148180206008480105008180105008180206004140114148180206004405111008480212010004184848480212008105284844440111004105 (by decide +kernel)

def state229_25 : List Sig := [0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 7,0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0,input 6,input 0,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_25 : Impossible true (goalAt 229) 5 state229_25.toFinset :=
  node_ok cuts229 [⟨state229_24,exclude229_24⟩] 0x28200604018100a08028200848018100848018100a08028200604018100a08028200444020600a08009014818020600414010500818020600848010500818010500818020600414010500818020600414030200450521416000011414444011414444010414850521200848020414444021200848040010c040 (by decide +kernel)

def state229_26 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0,input 2,input 0,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_26 : Impossible true (goalAt 229) 5 state229_26.toFinset :=
  node_ok cuts229 [⟨state229_24,exclude229_24⟩,⟨state229_2,exclude229_2⟩] 0x28200c08018100a08018100a08028200604009414a08028200250520600a08009014818020600444080004818020600c08010500818010500818020600414011414818020600440511100a08009414a08021200444021102000011100450511100444010414c04030200c08040014612130200c08040004a121 (by decide +kernel)

def state229_27 : List Sig := [0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0,input 2,input 6,input 0,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_27 : Impossible true (goalAt 229) 6 state229_27.toFinset :=
  node_ok cuts229 [⟨state229_3,exclude229_3⟩,⟨state229_22,exclude229_22⟩,⟨state229_23,exclude229_23⟩,⟨state229_25,exclude229_25⟩,⟨state229_26,exclude229_26⟩] 0xa12118100604030100a08028200a12128200a08030100604018101000428200a08011414604018101000218100604011414a08028201000228200a0804000c60401810100021810060404000ca08028200a12110500414030100818020600a12120600818030100414010500250520600818028201000628200250540008240528200818020600450520600818011010414010500450510500414011010818020601000120600818011101000111101000640006000011100818020601000620600818040000414010501000610500414040000818020600c04011414c04028485000428484c04080010c04028484450528485000140004c08021414444011100c04040004c04021416000321414c04011100444009414444011100a08040004a08009415000209414a08011100a08011415000411415000111100444040005000110415000140010848030101000530100a12180008a12130102000130100a12140014a121 (by decide +kernel)

def state229_28 : List Sig := [0xffffffffffffffff0000000000000000f0f0f0f0f0f0f0f0,input 6,input 2,input 7,input 0,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_28 : Impossible true (goalAt 229) 5 state229_28.toFinset :=
  node_ok cuts229 [⟨state229_4,exclude229_4⟩] 0x604028200a08018100a08018100604028200818028200240520600414020600818010500818021202000020600818010500414020600848028200250521200444021200848011100848011100444021200c04038484c04018484a08018100a08018100818010500818010500a12130100850530100848011100848011100c080 (by decide +kernel)

def state229_29 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 2,input 0,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_29 : Impossible true (goalAt 229) 5 state229_29.toFinset :=
  node_ok cuts229 [⟨state229_24,exclude229_24⟩,⟨state229_5,exclude229_5⟩] 0x18100a08028200604028200c08018100a08009414a08028200250520600a08009014818020600848080004818010500818020600414020600c08010500818021414818020600840521200a08009414848011100848030202000021200850521200848020414a12130100c04040004c04030200c080400106121 (by decide +kernel)

def state229_30 : List Sig := [0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 2,input 7,input 0,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_30 : Impossible true (goalAt 229) 6 state229_30.toFinset :=
  node_ok cuts229 [⟨state229_25,exclude229_25⟩,⟨state229_6,exclude229_6⟩,⟨state229_22,exclude229_22⟩,⟨state229_28,exclude229_28⟩,⟨state229_29,exclude229_29⟩] 0x1000518484612121414c08030202000430200c08021414612118486000318484612140010c08030202000230200c08040010612118484612128200a08030200604030200612118100604030200a08028201000518100604021414a08028201000228200a0802141460401810100021810060404000ca08028201000228200a0804000c604018100612120600818030200414030200612110500414030200818020600250520600818028201000628200250540008240528200818020600850510500414021010818020600850520600818021010414010501000120600818021201000121201000640006000121200818020601000610500414040000818020601000620600818040000414010501000140004c04011414848021200c08040004c08011416000011414c08021200848009414848021200a08040004a08009415000209414a080212008480214150005214150001212008480400050001204150001400144440 (by decide +kernel)

def state229_31 : List Sig := [0x5555555555555555555555555555555555555555555555555555555500000000,input 7,input 5,input 6,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_31 : Impossible true (goalAt 229) 4 state229_31.toFinset :=
  node_ok cuts229 [] 0x21200c08011100848021200a08009484848011100848021200444030100c08030200612128200c08018100a08018100a080282006040206002421212008180206004140302008180206002405282008180105008180206004140 (by decide +kernel)

def state229_32 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000,input 7,input 5,input 6,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_32 : Impossible true (goalAt 229) 4 state229_32.toFinset :=
  node_ok cuts229 [] 0x20600c08010500818020600a08009014818010500818020600414030100c08030200612128200c08018100a08018100a080282006040206002421206008480212004440302008480212002521282008480111008480212004440 (by decide +kernel)

def state229_33 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000,input 7,input 5,input 6,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_33 : Impossible true (goalAt 229) 5 state229_33.toFinset :=
  node_ok cuts229 [⟨state229_10,exclude229_10⟩,⟨state229_31,exclude229_31⟩,⟨state229_32,exclude229_32⟩] 0x848030200444021200848028200252121200444021200848011102000221200848040004818021200242120600818030200414020600818028202000020600414020600818010502000120600818040000c04030200c08018484450528200c08018100a08018100a080282006040094148505 (by decide +kernel)

def state229_34 : List Sig := [0xffffffffffffffffffffffff00000000,input 7,input 5,input 6,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_34 : Impossible true (goalAt 229) 5 state229_34.toFinset :=
  node_ok cuts229 [⟨state229_11,exclude229_11⟩] 0x848030200444021200848028200252121200444021200848011100818021200242120600818030200414020600818028202000020600414020600818010500612130200c08018484a08030200604028200604028200a08018100444021200444021200414020600414020600612130200612130200604028200604028200c040 (by decide +kernel)

def state229_35 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_35 : Impossible true (goalAt 229) 4 state229_35.toFinset :=
  node_ok cuts229 [] 0x21200a08011100848011100848021200444009484848021200252120600848009084818020600a08010500818010500818020600414018484818020600602118100a08028201000418484a080282008121184846040181004121 (by decide +kernel)

def state229_36 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 7,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 6,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_36 : Impossible true (goalAt 229) 5 state229_36.toFinset :=
  node_ok cuts229 [⟨state229_35,exclude229_35⟩] 0x21200444011100848021200a08011100848011100848021200444011100848021200444020600848009084818020600414010500818020600a08010500818010500818020600414010500818020600414030200612128486000018484604018484604010484a12128200a08020484604028200a08040010c040 (by decide +kernel)

def state229_37 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 5,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_37 : Impossible true (goalAt 229) 5 state229_37.toFinset :=
  node_ok cuts229 [⟨state229_35,exclude229_35⟩,⟨state229_12,exclude229_12⟩] 0x21200604009484848021200c08011100848011100848021200444009484848021200252120600848009084818020600604080004818020600c08010500818010500818020600414018484818020600602128200604028102000018100612118100604010484c04030200c08040014612130200c0804000ca121 (by decide +kernel)

def state229_38 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 5,input 6,input 0,input 2,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_38 : Impossible true (goalAt 229) 6 state229_38.toFinset :=
  node_ok cuts229 [⟨state229_13,exclude229_13⟩,⟨state229_33,exclude229_33⟩,⟨state229_34,exclude229_34⟩,⟨state229_36,exclude229_36⟩,⟨state229_37,exclude229_37⟩] 0x850511100444030100848021200850521200848030100444011101000421200848018484444011101000211100444018484848021201000321200848018100252118101000209484252118100848021201000221200848040004444011101000211100444040004848021200a12110500414030100818020600a1212060081803010041401050025212060081802120100072120025214000824212120081802060061212060081801808041401050061211050041401808081802060100032060081801810100031810100074000e000018100818020601000720600818040000414010501000710500414040000818020600c04018484c04028485000428484c04080010c0402848461211848500034000cc08028484604018100c0404000cc04028486000328484c0401810060401848500041848500031810060404000d000310485000340010a080301010005301008505800088505301020001301008505400148505 (by decide +kernel)

def state229_39 : List Sig := [0xffffffffffffffff0000000000000000ffffffff00000000,input 6,input 5,input 7,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_39 : Impossible true (goalAt 229) 5 state229_39.toFinset :=
  node_ok cuts229 [⟨state229_14,exclude229_14⟩] 0x444021200848011100848028200252121200848011100444021200818021200242120600414020600818010500818028202000020600818010500414020600604028200a08018100a08018100604028200c04028484c04028484848011100848011100818010500818010500a12130100a12130100a08018100a08018100c080 (by decide +kernel)

def state229_40 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_40 : Impossible true (goalAt 229) 5 state229_40.toFinset :=
  node_ok cuts229 [⟨state229_35,exclude229_35⟩,⟨state229_15,exclude229_15⟩] 0x21200a08009484848011100848021200444021200c08011100848009484848021200252120600848009084818020600a08080004818010500818020600414020600c08010500818028484818020600a02118100a08030202000028200a12128200a08020484a12130100c0404000cc04030200c080400106121 (by decide +kernel)

def state229_41 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,input 7,input 0,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_41 : Impossible true (goalAt 229) 6 state229_41.toFinset :=
  node_ok cuts229 [⟨state229_36,exclude229_36⟩,⟨state229_16,exclude229_16⟩,⟨state229_33,exclude229_33⟩,⟨state229_39,exclude229_39⟩,⟨state229_40,exclude229_40⟩] 0x1000518484612128484c08030202000430200c08028484612118486000311414450540010c08030202000230200c08040010450511414450521200848030200444030200450511100444030200848021201000511100444028484848021201000221200848028484444011101000321200848028200252128201000209484252128200848021201000211100444040004848021201000221200848040004444011100612120600818030200414030200612110500414030200818020600252120600818021201000721200252140008242121200818020600a12110500414028080818020600a1212060081802808041401050100032060081802820100032820100074000e00012820081802060100071050041404000081802060100072060081804000041401050100034000cc04018484a08028200c0804000cc08018486000018484c08028200a08028485000528485000328200a0804000d0003204850003400146040 (by decide +kernel)

def state229_42 : List Sig := [0xf5f5f5f500000000f5f5f5f500000000f5f5f5f500000000f0f0f0f0,input 2,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_42 : Impossible true (goalAt 229) 3 state229_42.toFinset :=
  node_ok cuts229 [] 0x30100c08030200412111100848021200444021200c080111008480105008180206004140206004140302008180206002421212008180 (by decide +kernel)

def state229_43 : List Sig := [0xf5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f0f0f0f0f0f0f0f0,input 2,input 6,input 7,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_43 : Impossible true (goalAt 229) 4 state229_43.toFinset :=
  node_ok cuts229 [⟨state229_42,exclude229_42⟩] 0x604028200a08018100a08030200604028200c04030200c080184848480282002405212004440212008480111008480302004440212002421206020000282008180105008180206004140206004140302008180 (by decide +kernel)

def state229_44 : List Sig := [0xf0f0f0f050505050f0f0f0f050505050f0f0f0f050505050f0f0f0f00000000,input 5,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_44 : Impossible true (goalAt 229) 3 state229_44.toFinset :=
  node_ok cuts229 [] 0x30100c08030200602118100a08028200604028200c08018100a080105008180206004140206004140302008180206002421282008180 (by decide +kernel)

def state229_45 : List Sig := [0xffffffff55555555ffffffff55555555ffffffff55555555ffffffff00000000,input 5,input 6,input 7,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_45 : Impossible true (goalAt 229) 4 state229_45.toFinset :=
  node_ok cuts229 [⟨state229_44,exclude229_44⟩] 0x444021200848011100848030200444021200848028200242121202000020600848020600c04030200c08018084604028200a08018100a080302006040282002405105008180206004140206004140302008180 (by decide +kernel)

def state229_46 : List Sig := [0x5555555555555555555555555555555555555555555555550000000000000000,input 6,input 7,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_46 : Impossible true (goalAt 229) 5 state229_46.toFinset :=
  node_ok cuts229 [⟨state229_7,exclude229_7⟩,⟨state229_17,exclude229_17⟩,⟨state229_43,exclude229_43⟩,⟨state229_45,exclude229_45⟩] 0x28484604018100c04028200a08028484a08028200c04018100604018484a08028200c08018100c08018484604018100c08028200a08009014848021200a08009084a08009014242109084a08021200848021414444011100c04021200848021414848021200c04011100444011414848021200c08011100c08011414444011100c08021200848030100612130100a12130200c08030100c08030200a12118484612128200818020600240580004240528202000328200240520600818021200818020600242180000242121202000221200242120600818030100414010500a12120600818030100818020600a121105004140302008180206006121105004140302004140302006121206008180 (by decide +kernel)

def state229_47 : List Sig := [0x5555555555555555555555555555555555555555555555550000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,input 7,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_47 : Impossible true (goalAt 229) 5 state229_47.toFinset :=
  node_ok cuts229 [] 0x18100a08028200604028200c08018100a08009014a08028200240521200a08009084848011100848021200444021200c08011100848009084848021200242128484c04030201000818484818009014a08020600818009084848020600414020600818010500818010500c080206010000 (by decide +kernel)

def state229_48 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0000000000000000,input 2,input 6,input 7,input 0,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_48 : Impossible true (goalAt 229) 5 state229_48.toFinset :=
  node_ok cuts229 [⟨state229_7,exclude229_7⟩] 0x604028200a08018100a08030200604028200818028200240520600414020600818010500818030200414020600818009080242120600c04030200c08011414250528200252128200252130100850530100252130200450530200a08009414a08009414818080000818040000c04028484c04021414c08018484c080114148480 (by decide +kernel)

def state229_49 : List Sig := [0xffffffff00000000ffffffff00000000ffffffff0000000000000000,input 5,input 6,input 7,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_49 : Impossible true (goalAt 229) 5 state229_49.toFinset :=
  node_ok cuts229 [⟨state229_17,exclude229_17⟩] 0x444021200848011100848030200444021200848009484252121200818021200242120600414020600818010500818030200414020600818009010240520600c04030200c08018484a12130100a12130100612130200612130200848009484848009484818080000818040000c04028484c04028484c08018484c08018484a080 (by decide +kernel)

def state229_50 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,input 7,input 0,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_50 : Impossible true (goalAt 229) 6 state229_50.toFinset :=
  node_ok cuts229 [⟨state229_8,exclude229_8⟩,⟨state229_18,exclude229_18⟩,⟨state229_22,exclude229_22⟩,⟨state229_26,exclude229_26⟩,⟨state229_29,exclude229_29⟩,⟨state229_33,exclude229_33⟩,⟨state229_37,exclude229_37⟩,⟨state229_40,exclude229_40⟩,⟨state229_46,exclude229_46⟩,⟨state229_47,exclude229_47⟩,⟨state229_48,exclude229_48⟩,⟨state229_49,exclude229_49⟩] 0x1000518100604030100a08028202000728200a08030100604018101000428200a08030200604030202000618100604030200a08028202000b0941425054000ca08028202000528200a0804000c250509414250521200848028200252128200250509484252128200848021201000511100444030100848021202000421200848030100444011101000421200848030200444030202000311100444030200848021202000a09484252140004848021202000221200848040004252109484250520600818028201000828200250580004240528200818020600252120600818021201000821200252180000242121200818020601000510500414030100818020601000820600818030100414010501000420600818030200414030201000810500414030200818020601000880026000840000818020601000820600818040001000840001000440010a12130101000530101000430200c080400110004400110004400146121 (by decide +kernel)

def state229_51 : List Sig := roots 229
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude229_51 : Impossible true (goalAt 229) 7 state229_51.toFinset :=
  node_ok cuts229 [⟨state229_9,exclude229_9⟩,⟨state229_19,exclude229_19⟩,⟨state229_27,exclude229_27⟩,⟨state229_30,exclude229_30⟩,⟨state229_38,exclude229_38⟩,⟨state229_41,exclude229_41⟩,⟨state229_50,exclude229_50⟩] 0x40014c04018484c04040010a12130200c08080018c04030200c08040010a12118484612140014a1211810060404000cc04028200a08080014a12128200a0804000cc04018100604040010612128200a0804000cc08018100c0808001061211810060404000cc08028200a08040014850511100444040004c0402120084808000c850521200848040004c04011100444040010450521200848040004c08011100c08080008450511100444040004c0802120084804000c250521200848040004a08009484a08040008250509484252140004a08021200848040000a12110500414040000c04020600818040000a12120600818040000c04010500414040000612120600818040000c08010500c08040000612110500414040000c08020600818040000250520600818040000a08040000a08040000250580004240540000a080206008180400002521206008180400008480400008480400002521800002421400008480206008180 (by decide +kernel)

theorem lower229 : Claim 229 8 :=
  fromSearch 2098438 (by decide +kernel) exclude229_51

theorem lower212 : Claim 212 5 :=
  fromLift 5 4 570820096 lower208 (by decide +kernel)

theorem lower149 : Claim 149 5 :=
  fromLift 5 4 1796 lower145 (by decide +kernel)

theorem lower85 : Claim 85 5 :=
  fromLift 5 4 1540 lower81 (by decide +kernel)

def rule213_0 : {c : Cut // CutGood (goalAt 213) c} :=
  ruleFor 213 lower209 none (by decide +kernel)

def rule213_1 : {c : Cut // CutGood (goalAt 213) c} :=
  ruleFor 213 lower197 none (by decide +kernel)

def rule213_2 : {c : Cut // CutGood (goalAt 213) c} :=
  ruleFor 213 lower196 none (by decide +kernel)

def rule213_3 : {c : Cut // CutGood (goalAt 213) c} :=
  ruleFor 213 lower212 none (by decide +kernel)

def rule213_4 : {c : Cut // CutGood (goalAt 213) c} :=
  ruleFor 213 lower149 none (by decide +kernel)

def rule213_5 : {c : Cut // CutGood (goalAt 213) c} :=
  ruleFor 213 lower85 none (by decide +kernel)

def rule213_6 : {c : Cut // CutGood (goalAt 213) c} :=
  ruleFor 213 lower208 none (by decide +kernel)

def rule213_7 : {c : Cut // CutGood (goalAt 213) c} :=
  ruleFor 213 lower81 none (by decide +kernel)

def rule213_8 : {c : Cut // CutGood (goalAt 213) c} :=
  ruleFor 213 lower145 none (by decide +kernel)

def rule213_9 : {c : Cut // CutGood (goalAt 213) c} :=
  ruleFor 213 lower193 none (by decide +kernel)

def cuts213 : Cuts (goalAt 213) := [rule213_0,rule213_1,rule213_2,rule213_3,rule213_4,rule213_5,rule213_6,rule213_7,rule213_8,rule213_9]

def state213_0 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaa,input 7,input 6,0xfafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafa,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude213_0 : Impossible true (goalAt 213) 4 state213_0.toFinset :=
  node_ok cuts213 [] 0x24200c08014100908014100908024200504005450908024201000220600908004414818020600c08010500818010500818020600414005450818020601000030100c080302004105144509114 (by decide +kernel)

def state213_1 : List Sig := [0xffffffffffffffffaaaaaaaaaaaaaaaa,input 7,input 6,0xfafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafa,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude213_1 : Impossible true (goalAt 213) 4 state213_1.toFinset :=
  node_ok cuts213 [] 0x908030200504024200504024200908014100818024200110520600818030200414020600414020600818010500d11430200c08024450504024200504024200414020600414020600151430200410530200c040 (by decide +kernel)

def state213_2 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa,0xfafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafa,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude213_2 : Impossible true (goalAt 213) 4 state213_2.toFinset :=
  node_ok cuts213 [] 0x908030200504024200504024200908014100110524200908004414848024200110521200818020600414021200414021200848010500410521200848040018c04030200c08005450151430200c080054509414 (by decide +kernel)

def state213_3 : List Sig := [0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa,input 6,0xfafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafa,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude213_3 : Impossible true (goalAt 213) 5 state213_3.toFinset :=
  node_ok cuts213 [⟨state213_0,exclude213_0⟩,⟨state213_1,exclude213_1⟩,⟨state213_2,exclude213_2⟩] 0x941414100504030100908024200941424200908030100504014101000224200908010414504014101000214100504010414908024200151424200908040008504014100151414100504040008908024200941410500414030100848021200941421200848030100414010500110521200848024201000624200110540008110524200848021200410521200848040018414010500410510500414040018848021200151421200818040000414020600151410500414040000848021200c04010414c04025051000825050c04080008c0402505041052505100034000cc080301001514301009414800049114301020000301009414054501514 (by decide +kernel)

def state213_4 : List Sig := [0xffffffffffffffff0000000000000000aaaaaaaaaaaaaaaa,input 6,input 7,0xfafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafa,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude213_4 : Impossible true (goalAt 213) 4 state213_4.toFinset :=
  node_ok cuts213 [] 0x504024200908014100908014100504024200818024200110520600414020600818010500818010500414020600c04034450c04014450908014100908014100818010500818010500151430100810530100c080 (by decide +kernel)

def state213_5 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xfafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafa,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude213_5 : Impossible true (goalAt 213) 4 state213_5.toFinset :=
  node_ok cuts213 [] 0x504024200908014100908030200504024200110524200908004414818024200110520600414020600818011100818030200444020600810520600818040018151430100c04005450c04030200c080054505414 (by decide +kernel)

def state213_6 : List Sig := [0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 7,0xfafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafa,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude213_6 : Impossible true (goalAt 213) 5 state213_6.toFinset :=
  node_ok cuts213 [⟨state213_0,exclude213_0⟩,⟨state213_4,exclude213_4⟩,⟨state213_5,exclude213_5⟩] 0x1000715050541420414c08030202000230200c08020414541415052000115050511405450c08030202000030200c0800545054140545054142420090803020050403020054141410050403020090802420100021410050402041490802420100022420090802041450401410015141410050404000890802420015142420090804000850401410054142060081803020044403020054141110044403020081802060011052060081802420100062420011054000811052420081802060081051110044404001881802060081052060081804001844401110015141110041404000081802060015142060081804000044401110100034000cc040 (by decide +kernel)

def state213_7 : List Sig := [0x505050505050505050505050505050505050505050505050000000000000000,input 6,input 7,input 0,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude213_7 : Impossible true (goalAt 213) 4 state213_7.toFinset :=
  node_ok cuts213 [] 0x504024200908014100908030200504024200110524200151424200151430100810530100151430200410530200c04030200c080150508480044149080212008180111008480212004440212004440302008480 (by decide +kernel)

def state213_8 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,input 7,0xfafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafa,input 0,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude213_8 : Impossible true (goalAt 213) 5 state213_8.toFinset :=
  node_ok cuts213 [⟨state213_0,exclude213_0⟩,⟨state213_2,exclude213_2⟩,⟨state213_5,exclude213_5⟩,⟨state213_7,exclude213_7⟩] 0x14100908024200504024200c0801410090800441490802420011050441490800545090802060015143010200023010015143020200013020015144000e000005450848024200110521200444021200848011100848030200444021202000321200848040018941430100c0804001c5414 (by decide +kernel)

def state213_9 : List Sig := [0xfafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafa,input 0,input 4,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude213_9 : Impossible true (goalAt 213) 6 state213_9.toFinset :=
  node_ok cuts213 [⟨state213_3,exclude213_3⟩,⟨state213_6,exclude213_6⟩,⟨state213_8,exclude213_8⟩] 0x4001cc04015050c04040020941430200c08080008c04030200c0804001c941415050541440008941414100504040008c04024200908040008941424200908040008c04014100504040008541424200908040008c08014100c08040008541414100504040008c0802420090804000c81050545015144000cc0404000cc0404000c81058000481054000cc04005450c0404000c41050545015144000cc0804000cc0804000c41058000041054000cc08005450c0804000c11054000811054000c90800545090804000c11050545015144000c90804000c908040001000040000818040018941411100444040018c04021200848040018941421200848040018c04011100444040018541421200848040018c08011100c08040018541411100444040018c080212008480400181105212008480400189080400189080400181105400081105400189080212008480 (by decide +kernel)

def state213_10 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffffffff0000ffff0000,input 7,input 6,0xfffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude213_10 : Impossible true (goalAt 213) 4 state213_10.toFinset :=
  node_ok cuts213 [] 0x20600848005450818020600c08010500818010500818020600414004414818020601000621200c08011100848011100848021200444004414848021201000030100c080302004414114148505 (by decide +kernel)

def state213_11 : List Sig := [0xffffffffffffffffffff0000ffff0000,input 7,input 6,0xfffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude213_11 : Impossible true (goalAt 213) 4 state213_11.toFinset :=
  node_ok cuts213 [] 0x818021200151420600818030200414020600414020600818010500848030200444021200444021200848011100441430200c08011050414020600414020600444021200444021200441430200441430200c040 (by decide +kernel)

def state213_12 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,0xfffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude213_12 : Impossible true (goalAt 213) 4 state213_12.toFinset :=
  node_ok cuts213 [] 0x818021200151420600818030200414020600414020600818010500151420600818005450848024200444021200444021200848011100441421200848040024c04030200c08004414441430200c080044149014 (by decide +kernel)

def state213_13 : List Sig := [0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 6,0xfffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0,input 0,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude213_13 : Impossible true (goalAt 213) 5 state213_13.toFinset :=
  node_ok cuts213 [⟨state213_10,exclude213_10⟩,⟨state213_11,exclude213_11⟩,⟨state213_12,exclude213_12⟩] 0x850510500414030100818020600850520600818030100414010501000220600818021200151421201000205450151421200818020601000220600818011050414010501000210500414011050818020600110520600818040018414010500110510500414040018818020600901411100444030100848021200901421200848030100444011100441421200848040024444011100441411100444040024848021200110521200848040000444024200110511100444040000848021200c04011050c04024051000824050c04080008c04024050441411051000140004c080301001105301008505800048505301020000301008505044148414 (by decide +kernel)

def state213_14 : List Sig := [0xffffffffffffffff0000000000000000ffff0000ffff0000,input 6,input 7,0xfffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude213_14 : Impossible true (goalAt 213) 4 state213_14.toFinset :=
  node_ok cuts213 [] 0x818021200151420600414020600818010500818010500414020600444021200848011100848011100444021200c04021050c04021050818010500818010500848011100848011100841430100841430100c080 (by decide +kernel)

def state213_15 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,0xfffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude213_15 : Impossible true (goalAt 213) 4 state213_15.toFinset :=
  node_ok cuts213 [] 0x818021200151420600414020600818010500818030200414020600151420600818005450444021200848011100848030200444021200841421200848040024841430100c04004414c04030200c080044145014 (by decide +kernel)

def state213_16 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 7,0xfffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0,input 0,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude213_16 : Impossible true (goalAt 213) 5 state213_16.toFinset :=
  node_ok cuts213 [⟨state213_10,exclude213_10⟩,⟨state213_14,exclude213_14⟩,⟨state213_15,exclude213_15⟩] 0x1000714050501421050c08030202000230200c08021050501414052000111414450504414c08030202000030200c08004414450511050450520600818030200414030200450510500414030200818020601000220600818021200151421201000205450151421200818020601000210500414021050818020601000220600818021050414010500110510500414040018818020600110520600818040018414010500501421200848030200444030200501411100444030200848021200841411100444040024848021200841421200848040024444011100110511100444040000848021200110521200848040000444011101000140004c040 (by decide +kernel)

def state213_17 : List Sig := [0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f0000000000000000,input 6,input 7,input 4,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude213_17 : Impossible true (goalAt 213) 4 state213_17.toFinset :=
  node_ok cuts213 [] 0x818005450151420600414020600818010500818030200414020600901430100841430100501430200441430200c04030200c080140508180054508180212009080111008480212004440212004440302008480 (by decide +kernel)

def state213_18 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,input 7,0xfffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0,input 4,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude213_18 : Impossible true (goalAt 213) 5 state213_18.toFinset :=
  node_ok cuts213 [⟨state213_10,exclude213_10⟩,⟨state213_12,exclude213_12⟩,⟨state213_15,exclude213_15⟩,⟨state213_17,exclude213_17⟩] 0x20600151405450818020600848005450818010500818020600414020600c08010500818005450818020600151424200110530102000230100110530202000130200110540006000004414444021200848011100848030200444021202000321200848040024901430100c0804001c5014 (by decide +kernel)

def state213_19 : List Sig := [0xfffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0,input 4,input 0,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude213_19 : Impossible true (goalAt 213) 6 state213_19.toFinset :=
  node_ok cuts213 [⟨state213_13,exclude213_13⟩,⟨state213_16,exclude213_16⟩,⟨state213_18,exclude213_18⟩] 0x4001cc04014050c04040020901430200c08080008c04030200c0804001c901414050501440008850510500414040018c04020600818040008850520600818040018c04010500414040008450520600818040018c08010500c08040008450510500414040018c08020600818040004110520600818040005000605450151440004110505450151440005000120600818040009000220600818040018848005450848040009000205450151440018848020600818040004901404414901440004c04040004c04040004901480004841440004c04004414c04040004501404414501440004c08040004c08040004501480000441440004c08004414c08040001000040000908040024901411100444040024c04021200848040024901421200848040024c04011100444040024501421200848040024c08011100c08040024501411100444040024c080212008480 (by decide +kernel)

def state213_20 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0a0a0a0a0a0a0a0a,input 7,input 0,input 6,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude213_20 : Impossible true (goalAt 213) 4 state213_20.toFinset :=
  node_ok cuts213 [] 0x24200c08014100908014100908024200504030100c08030200541420600908005450818020600c080105008180105008180206004140212001105242008480212004440302008480206001514206008480111008480212004440 (by decide +kernel)

def state213_21 : List Sig := [0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000aaaa0000aaaa,input 7,input 0,input 6,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude213_21 : Impossible true (goalAt 213) 4 state213_21.toFinset :=
  node_ok cuts213 [] 0x21200c08011100848011100848021200444030100c08030200541420600848005450818020600c080105008180105008180206004140212001105212009080242005040302009080206001514206009080141009080242005040 (by decide +kernel)

def state213_22 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaa,input 7,input 0,input 6,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude213_22 : Impossible true (goalAt 213) 5 state213_22.toFinset :=
  node_ok cuts213 [⟨state213_0,exclude213_0⟩,⟨state213_20,exclude213_20⟩,⟨state213_21,exclude213_21⟩] 0x908030200504024200504024200908014102000224200908040004848024200110521200848030200444021200444021200848011102000121200848040000c04030200c08011414541420600908005414818020600848080000818020600c080105008180105008180206004140054509414 (by decide +kernel)

def state213_23 : List Sig := [0xffffffffffffffffaaaaaaaaaaaaaaaa,input 7,input 0,input 6,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude213_23 : Impossible true (goalAt 213) 5 state213_23.toFinset :=
  node_ok cuts213 [⟨state213_1,exclude213_1⟩] 0x908030200504024200504024200908014100848024200110521200848030200444021200444021200848011100d41430200c08025050818024200150520600818021202000020600818030200414020600414020600818010500504024200504024200444021200444021200541430200450530200414020600414020600c040 (by decide +kernel)

def state213_24 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude213_24 : Impossible true (goalAt 213) 4 state213_24.toFinset :=
  node_ok cuts213 [] 0x242008180141008180141009080242004140054149080242001505212009080044148480212008180111008180111008480212004140114148480212004105105008180206010004150508180206008405250504140105004405 (by decide +kernel)

def state213_25 : List Sig := [0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 7,0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa,input 6,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude213_25 : Impossible true (goalAt 213) 5 state213_25.toFinset :=
  node_ok cuts213 [⟨state213_24,exclude213_24⟩] 0x24200504014100908024200818014100818014100908024200504014100908024200414021200908004414848021200444011100848021200818011100818011100848021200444011100848021200414030200450521416000011414414011414414011014850520600818021014414020600818040010c040 (by decide +kernel)

def state213_26 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa,input 0,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude213_26 : Impossible true (goalAt 213) 5 state213_26.toFinset :=
  node_ok cuts213 [⟨state213_24,exclude213_24⟩,⟨state213_2,exclude213_2⟩] 0x24200c08014100908014100908024200504005414908024200150521200908004414848021200c08011100848011100848021200444011414848021200410510500908005414908010500848080004848020600414020502000010500450510500414011014c04030200c08040014541430200c0804000c9414 (by decide +kernel)

def state213_27 : List Sig := [0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa,input 0,input 6,input 2,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude213_27 : Impossible true (goalAt 213) 6 state213_27.toFinset :=
  node_ok cuts213 [⟨state213_3,exclude213_3⟩,⟨state213_22,exclude213_22⟩,⟨state213_23,exclude213_23⟩,⟨state213_25,exclude213_25⟩,⟨state213_26,exclude213_26⟩] 0x941414100504030100908024200941424200908030100504014101000424200908011414504014101000214100504011414908024201000224200908040004504014101000214100504040004908024200941411100444030100848021200941421200848030100444011100150521200848024201000624200150540008110524200848021200450521200848010404444011100450511100444010404848021201000621200848040000444011101000611100444040000848021200c04011414c04025051000425050c04080010c0402505045052505100044000cc08021414414010500c0404000cc04021416000321414c0401050041400541441401050090804000c90800541500020541490801050090804000c41401050084804000c84804000d0006800008480105008480114150004114150003105004140400110004110150004400108180301010005301009414800089414301020001301009414400149414 (by decide +kernel)

def state213_28 : List Sig := [0xffffffffffffffff0000000000000000aaaaaaaaaaaaaaaa,input 6,input 0,input 7,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude213_28 : Impossible true (goalAt 213) 5 state213_28.toFinset :=
  node_ok cuts213 [⟨state213_4,exclude213_4⟩] 0x504024200908014100908014100504024200848024200110521200444021200848011100848011100444021200818024200150520600818021202000020600414020600818010500818010500414020600c04035050c04015050908014100908014100848011100848011100941430100850530100818010500818010500c080 (by decide +kernel)

def state213_29 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 0,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude213_29 : Impossible true (goalAt 213) 5 state213_29.toFinset :=
  node_ok cuts213 [⟨state213_24,exclude213_24⟩,⟨state213_5,exclude213_5⟩] 0x14100908024200504024200c08014100908005414908024200150521200908004414848011100848021200444021200c08011100848021414848021200810520600908005414818020600848080004818010500818030202000020600850520600818021014941430100c04040010c04030200c080400105414 (by decide +kernel)

def state213_30 : List Sig := [0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 0,input 7,input 2,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude213_30 : Impossible true (goalAt 213) 6 state213_30.toFinset :=
  node_ok cuts213 [⟨state213_6,exclude213_6⟩,⟨state213_25,exclude213_25⟩,⟨state213_22,exclude213_22⟩,⟨state213_28,exclude213_28⟩,⟨state213_29,exclude213_29⟩] 0x1000515050541421414c08030202000430200c08021414541415052000315050541440010c08030202000230200c0804001054141505054142420090803020050403020054141410050403020090802420100051410050402141490802420100022420090802141450401410100021410050404000490802420100022420090804000450401410054142120084803020044403020054141110044403020084802120015052120084802420100062420015054000811052420084802120085051110044402040484802120085052120084802040444401110100061110044404000084802120100062120084804000044401110100034000cc04011414818020600c0804000cc08011416000111414c0802060081800541481802060090804000c90800541500020541490802060081804000c81802060084804000c84804000d00068000084802060081802141500052141500032060081804000d0003210150003400144140 (by decide +kernel)

def state213_31 : List Sig := [0x5555555555555555555555555555555555555555555555555555000055550000,input 7,input 4,input 6,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude213_31 : Impossible true (goalAt 213) 4 state213_31.toFinset :=
  node_ok cuts213 [] 0x21200c08011100848021200908004414848011100848021200444030100c08030200541424200c080141009080141009080242005040206001514212008180206004140302008180206001514242008180105008180206004140 (by decide +kernel)

def state213_32 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0000,input 7,input 4,input 6,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude213_32 : Impossible true (goalAt 213) 4 state213_32.toFinset :=
  node_ok cuts213 [] 0x20600c08010500818020600908005450818010500818020600414030100c08030200541424200c080141009080141009080242005040206001514206008480212004440302008480212001105242008480111008480212004440 (by decide +kernel)

def state213_33 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffffffff0000ffff0000,input 7,input 4,input 6,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude213_33 : Impossible true (goalAt 213) 5 state213_33.toFinset :=
  node_ok cuts213 [⟨state213_10,exclude213_10⟩,⟨state213_31,exclude213_31⟩,⟨state213_32,exclude213_32⟩] 0x84803020044402120084802420200002120044402120084801110200022120084804000081802120015142060081803020041402060081802420015142060041402060081801050200012060081804000cc04030200c08015050450524200c080141009080141009080242005040054148505 (by decide +kernel)

def state213_34 : List Sig := [0xffffffffffffffffffff0000ffff0000,input 7,input 4,input 6,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude213_34 : Impossible true (goalAt 213) 5 state213_34.toFinset :=
  node_ok cuts213 [⟨state213_11,exclude213_11⟩] 0x848030200444021200848024202000021200444021200848011100818021200151420600818030200414020600818024200151420600414020600818010500541430200c08015050908030200504024200504024200908014100444021200444021200414020600414020600541430200541430200504024200504024200c040 (by decide +kernel)

def state213_35 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude213_35 : Impossible true (goalAt 213) 4 state213_35.toFinset :=
  node_ok cuts213 [] 0x212009080111008480111008480212004440150508480212005014206008480054508180206009080105008180105008180206004140054508180206001514141009080242010004150509080242008414150505040141004414 (by decide +kernel)

def state213_36 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 7,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 6,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude213_36 : Impossible true (goalAt 213) 5 state213_36.toFinset :=
  node_ok cuts213 [⟨state213_35,exclude213_35⟩] 0x21200444011100848021200908011100848011100848021200444011100848021200444020600848005450818020600414010500818020600908010500818010500818020600414010500818020600414030200541425052000015050504015050504011050941424200908021050504024200908040010c040 (by decide +kernel)

def state213_37 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 4,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude213_37 : Impossible true (goalAt 213) 5 state213_37.toFinset :=
  node_ok cuts213 [⟨state213_35,exclude213_35⟩,⟨state213_12,exclude213_12⟩] 0x21200504080004848021200c08011100848011100848021200444015050848021200501420600848005450818020600504005450818020600c08010500818010500818020600414005450818020600151424200504024102000014100541414100504011050c04030200c08040014541430200c080400049414 (by decide +kernel)

def state213_38 : List Sig := [0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 4,input 6,input 0,input 2,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude213_38 : Impossible true (goalAt 213) 6 state213_38.toFinset :=
  node_ok cuts213 [⟨state213_13,exclude213_13⟩,⟨state213_33,exclude213_33⟩,⟨state213_34,exclude213_34⟩,⟨state213_36,exclude213_36⟩,⟨state213_37,exclude213_37⟩] 0x94141110044403010084802120094142120084803010044401110054142120084801404044401110054141110044401404084802120100012120084801410100011410100094000600001410084802120100092120084804000044401110100091110044404000084802120085051050041403010081802060085052060081803010041401050100022060081802120015142120100020545015142120081802060100042060081801505041401050100021050041401505081802060100012060081801410015141410100020545015141410081802060100022060081804000c41401050100021050041404000c818020600c04015050c04025051000425050c04080010c04025050541415051000140004c08025050504014100c04040004c04025052000325050c040141005040150510004150510001141005040400050001110510001400109080301010005301008505800088505301020001301008505400148505 (by decide +kernel)

def state213_39 : List Sig := [0xffffffffffffffff0000000000000000ffff0000ffff0000,input 6,input 4,input 7,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude213_39 : Impossible true (goalAt 213) 5 state213_39.toFinset :=
  node_ok cuts213 [⟨state213_14,exclude213_14⟩] 0x444021200848011100848024202000021200848011100444021200818021200151420600414020600818010500818024200151420600818010500414020600504024200908014100908014100504024200c04025050c04025050848011100848011100818010500818010500941430100941430100908014100908014100c080 (by decide +kernel)

def state213_40 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 4,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude213_40 : Impossible true (goalAt 213) 5 state213_40.toFinset :=
  node_ok cuts213 [⟨state213_35,exclude213_35⟩,⟨state213_15,exclude213_15⟩] 0x21200908080004848011100848021200444021200c08011100848025050848021200901420600848005450818020600908005450818010500818020600414020600c08010500818005450818020600151414100908030202000024200941424200908021050941430100c04040004c04030200c080400105414 (by decide +kernel)

def state213_41 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 4,input 7,input 0,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude213_41 : Impossible true (goalAt 213) 6 state213_41.toFinset :=
  node_ok cuts213 [⟨state213_36,exclude213_36⟩,⟨state213_16,exclude213_16⟩,⟨state213_33,exclude213_33⟩,⟨state213_39,exclude213_39⟩,⟨state213_40,exclude213_40⟩] 0x1000515050541425050c08030202000430200c08025050541415052000311414450540010c08030202000230200c0804001045051141454142120084803020044403020054141110044403020084802120094141110044402404084802120094142120084802404044401110100012120084802420100012420100094000600012420084802120100091110044404000084802120100092120084804000044401110045052060081803020041403020045051050041403020081802060100022060081802120015142120100020545015142120081802060100051050041402505081802060100022060081802505041401050100012060081802420015142420100020545015142420081802060100021050041404000c81802060100022060081804000c414010501000140004c04015050908024200c08040004c08015052000015050c080242009080250510005250510001242009080400050001210510001400145040 (by decide +kernel)

def state213_42 : List Sig := [0xafaf0000afaf0000afaf0000afaf0000afaf0000afaf0000aaaa0000aaaa,input 0,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude213_42 : Impossible true (goalAt 213) 3 state213_42.toFinset :=
  node_ok cuts213 [] 0x30100c08030200441410500818020600414020600c080105008180111008480212004440212004440302008480206001514206008480 (by decide +kernel)

def state213_43 : List Sig := [0xafafafafafafafafafafafafafafafafafafafafafafafafaaaaaaaaaaaaaaaa,input 0,input 6,input 7,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude213_43 : Impossible true (goalAt 213) 4 state213_43.toFinset :=
  node_ok cuts213 [⟨state213_42,exclude213_42⟩] 0x504024200908014100908030200504024200c04030200c080150508180242001105206004140206008180105008180302004140206001514212020000242008480111008480212004440212004440302008480 (by decide +kernel)

def state213_44 : List Sig := [0x5555050555550505555505055555050555550505555505055555000055550000,input 4,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude213_44 : Impossible true (goalAt 213) 3 state213_44.toFinset :=
  node_ok cuts213 [] 0x30100c08030200501414100908024200504024200c080141009080105008180206004140206004140302008180206001514242008180 (by decide +kernel)

def state213_45 : List Sig := [0xffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0000ffff0000,input 4,input 6,input 7,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude213_45 : Impossible true (goalAt 213) 4 state213_45.toFinset :=
  node_ok cuts213 [⟨state213_44,exclude213_44⟩] 0x414020600818010500818030200414020600818024200151420602000020600818021200c04030200c080140505040242009080141009080302005040242001105111008480212004440212004440302008480 (by decide +kernel)

def state213_46 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0000000000000000,input 6,input 7,input 0,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude213_46 : Impossible true (goalAt 213) 5 state213_46.toFinset :=
  node_ok cuts213 [⟨state213_7,exclude213_7⟩,⟨state213_17,exclude213_17⟩,⟨state213_43,exclude213_43⟩,⟨state213_45,exclude213_45⟩] 0x25050504014100c04024200908025050908024200c04014100504015050908024200c08014100c08015050504014100c08024200908004414818020600908005450908004414151405450908020600818021414414010500c04020600818021414818020600c04010500414011414818020600c08010500c08011414414010500c08020600818030100541430100941430200c08030100c080302009414150505414242008480212001105800041105242020003242001105212008480206008480206001514800001514206020002206001514212008480301004440111009414212008480301008480212009414111004440302008480212005414111004440302004440302005414212008480 (by decide +kernel)

def state213_47 : List Sig := [0x5555555555555555555555555555555555555555555555550000000000000000,input 0,input 6,input 7,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude213_47 : Impossible true (goalAt 213) 5 state213_47.toFinset :=
  node_ok cuts213 [⟨state213_7,exclude213_7⟩] 0x504024200908014100908030200504024200848024200110521200444021200848011100848030200444021200c04030200c08011414150524200151424200111021200151421200151430100850530100151430200450530200908005414908005414848080000848040000c04025050c04021414c08015050c080114148180 (by decide +kernel)

def state213_48 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,input 7,input 0,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude213_48 : Impossible true (goalAt 213) 5 state213_48.toFinset :=
  node_ok cuts213 [] 0x14100908024200504024200c08014100908004414908024200110520600908005450818010500818020600414020600c08010500818005450818020600151425050c04030201000715050848004414908021200818005450818021200444021200848011100848011100c080212010000 (by decide +kernel)

def state213_49 : List Sig := [0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000,input 4,input 6,input 7,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude213_49 : Impossible true (goalAt 213) 5 state213_49.toFinset :=
  node_ok cuts213 [⟨state213_17,exclude213_17⟩] 0x444021200848011100848030200444021200848004404110521200818021200151420600414020600818010500818030200414020600818005450151420600c04030200c08015050941430100941430100541430200541430200848080000848040000818005450818005450c04025050c04025050c08015050c080150509080 (by decide +kernel)

def state213_50 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,input 7,input 0,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude213_50 : Impossible true (goalAt 213) 6 state213_50.toFinset :=
  node_ok cuts213 [⟨state213_22,exclude213_22⟩,⟨state213_26,exclude213_26⟩,⟨state213_29,exclude213_29⟩,⟨state213_8,exclude213_8⟩,⟨state213_18,exclude213_18⟩,⟨state213_33,exclude213_33⟩,⟨state213_37,exclude213_37⟩,⟨state213_40,exclude213_40⟩,⟨state213_46,exclude213_46⟩,⟨state213_47,exclude213_47⟩,⟨state213_48,exclude213_48⟩,⟨state213_49,exclude213_49⟩] 0x1000514100504030100908024202000724200908030100504014101000424200908030200504030202000614100504030200908024202000b0541415054000490802420200052420090804000415050541415052120084802420100072420015058001011052420084802120100051110044403010084802120100072120084803010044401110100042120084803020044403020100071110044403020084802120100078002a00084000084802120100072120084804000100074000015052060081802420015142420015050545015142420081802060100072060081802120015142120200030545015142120081802060100051050041403010081802060200022060081803010041401050100042060081803020041403020200011050041403020081802060200090545015144000c81802060200002060081804000c151405451000440010941430101000530101000430200c080400110004400110004400145414 (by decide +kernel)

def state213_51 : List Sig := roots 213
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude213_51 : Impossible true (goalAt 213) 7 state213_51.toFinset :=
  node_ok cuts213 [⟨state213_9,exclude213_9⟩,⟨state213_19,exclude213_19⟩,⟨state213_27,exclude213_27⟩,⟨state213_30,exclude213_30⟩,⟨state213_38,exclude213_38⟩,⟨state213_41,exclude213_41⟩,⟨state213_50,exclude213_50⟩] 0x40014c04015050c04040010941430200c08080018c04030200c08040010941415050541440014941414100504040004c04024200908080014941424200908040004c04014100504040010541424200908040004c08014100c08080010541414100504040004c08024200908040000941411100444040000c04021200848040000941421200848040000c04011100444040000541421200848040000c08011100c08040000541411100444040000c0802120084804000015052120084804000090804000090804000015058000411054000090802120084804001485051050041404000cc0402060081808000c85052060081804000cc0401050041404001045052060081804000cc08010500c08080008450510500414040010c0802060081804000415052060081804000c9080054509080400081505054501514400049080206008180400010000206008180400008480054508480400020000054501514400008480206008180 (by decide +kernel)

theorem lower213 : Claim 213 8 :=
  fromSearch 1540 (by decide +kernel) exclude213_51

theorem lower180 : Claim 180 5 :=
  fromLift 5 16 539428096 lower164 (by decide +kernel)

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

def rule117_0 : {c : Cut // CutGood (goalAt 117) c} :=
  ruleFor 117 lower113 none (by decide +kernel)

def rule117_1 : {c : Cut // CutGood (goalAt 117) c} :=
  ruleFor 117 lower101 none (by decide +kernel)

def rule117_2 : {c : Cut // CutGood (goalAt 117) c} :=
  ruleFor 117 lower85 none (by decide +kernel)

def rule117_3 : {c : Cut // CutGood (goalAt 117) c} :=
  ruleFor 117 lower116 none (by decide +kernel)

def cuts117 : Cuts (goalAt 117) := [rule117_0,rule117_1,rule117_2,rule117_3]

def state117_0 : List Sig := roots 117
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude117_0 : Impossible true (goalAt 117) 6 state117_0.toFinset :=
  node_ok cuts117 [] 0x4000870300d05070304000854141810060404000870301810060404000854140d05050304000470300c48470304000461211410050404000470301410050404000461210c48460304000434141410050404000460400c48460404000434140c48431214000460401410050404000054140d0c034304000070301110044404000054141110044404000070300d0c034304000034141110044404000060400d0c060404000034140d0c034304000060401110044404000015051110044404000050400d0c050404000015050d0c034304000050401110044404000c61210c4c031304000c70301050041404000c61211050041404000c70300c4c031304000825051050041404000860400c4c060404000825050c4c031304000860401050041404000431211050041404000450400c4c050404000431210c4c03130400045040105004140400002521105004140400004440054504440400002521054502421400004440105004140 (by decide +kernel)

theorem lower117 : Claim 117 7 :=
  fromSearch 2098436 (by decide +kernel) exclude117_0

def rule181_0 : {c : Cut // CutGood (goalAt 181) c} :=
  ruleFor 181 lower177 none (by decide +kernel)

def rule181_1 : {c : Cut // CutGood (goalAt 181) c} :=
  ruleFor 181 lower165 none (by decide +kernel)

def rule181_2 : {c : Cut // CutGood (goalAt 181) c} :=
  ruleFor 181 lower149 none (by decide +kernel)

def rule181_3 : {c : Cut // CutGood (goalAt 181) c} :=
  ruleFor 181 lower180 none (by decide +kernel)

def cuts181 : Cuts (goalAt 181) := [rule181_0,rule181_1,rule181_2,rule181_3]

def state181_0 : List Sig := roots 181
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude181_0 : Impossible true (goalAt 181) 6 state181_0.toFinset :=
  node_ok cuts181 [] 0x40008b0300d050b03040008941428200a08040008b03028200a0804000894140d050903040004b0300c484b03040004a12124200908040004b03024200908040004a1210c484a03040004341424200908040004a0800c484a0804000434140c484312140004a0802420090804000094140d0c0343040000b03021200848040000941421200848040000b0300d0c0343040000341421200848040000a0800d0c0a0804000034140d0c0343040000a0802120084804000015052120084804000090800d0c090804000015050d0c034304000090802120084804000ca1210c4c031304000cb0302060081804000ca1212060081804000cb0300c4c0313040008250520600818040008a0800c4c0a0804000825050c4c0313040008a0802060081804000431212060081804000490800c4c090804000431210c4c03130400049080206008180400002521206008180400008480054508480400002521054502421400008480206008180 (by decide +kernel)

theorem lower181 : Claim 181 7 :=
  fromSearch 2098436 (by decide +kernel) exclude181_0

def rule245_0 : {c : Cut // CutGood (goalAt 245) c} :=
  ruleFor 245 lower241 none (by decide +kernel)

def rule245_1 : {c : Cut // CutGood (goalAt 245) c} :=
  ruleFor 245 lower229 none (by decide +kernel)

def rule245_2 : {c : Cut // CutGood (goalAt 245) c} :=
  ruleFor 245 lower213 none (by decide +kernel)

def rule245_3 : {c : Cut // CutGood (goalAt 245) c} :=
  ruleFor 245 lower244 none (by decide +kernel)

def rule245_4 : {c : Cut // CutGood (goalAt 245) c} :=
  ruleFor 245 lower117 none (by decide +kernel)

def rule245_5 : {c : Cut // CutGood (goalAt 245) c} :=
  ruleFor 245 lower181 none (by decide +kernel)

def rule245_6 : {c : Cut // CutGood (goalAt 245) c} :=
  ruleFor 245 lower116 none (by decide +kernel)

def rule245_7 : {c : Cut // CutGood (goalAt 245) c} :=
  ruleFor 245 lower244 (some (1,input 6,input 7)) (by decide +kernel)

def rule245_8 : {c : Cut // CutGood (goalAt 245) c} :=
  ruleFor 245 lower113 none (by decide +kernel)

def rule245_9 : {c : Cut // CutGood (goalAt 245) c} :=
  ruleFor 245 lower241 (some (1,input 6,input 7)) (by decide +kernel)

def rule245_10 : {c : Cut // CutGood (goalAt 245) c} :=
  ruleFor 245 lower100 none (by decide +kernel)

def rule245_11 : {c : Cut // CutGood (goalAt 245) c} :=
  ruleFor 245 lower101 none (by decide +kernel)

def rule245_12 : {c : Cut // CutGood (goalAt 245) c} :=
  ruleFor 245 lower213 (some (1,input 6,input 7)) (by decide +kernel)

def rule245_13 : {c : Cut // CutGood (goalAt 245) c} :=
  ruleFor 245 lower85 none (by decide +kernel)

def rule245_14 : {c : Cut // CutGood (goalAt 245) c} :=
  ruleFor 245 lower145 none (by decide +kernel)

def rule245_15 : {c : Cut // CutGood (goalAt 245) c} :=
  ruleFor 245 lower229 (some (1,input 6,input 7)) (by decide +kernel)

def cuts245 : Cuts (goalAt 245) := [rule245_0,rule245_1,rule245_2,rule245_3,rule245_4,rule245_5,rule245_6,rule245_7,rule245_8,rule245_9,rule245_10,rule245_11,rule245_12,rule245_13,rule245_14,rule245_15]

def state245_0 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,input 7,input 0,input 2,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude245_0 : Impossible true (goalAt 245) 8 state245_0.toFinset :=
  node_ok cuts245 [] 0x40011000418100604040010c04028200a08040011000c28200a08040010c04018100604040015000528200a08040014c08018100c08040015000c18100604040014c08028200a08040031000c0d050341440035000228200a08040031000c28200a0804003500020d05034144003434142420090804002ca0800c484a0804003c34140c48431214002ca08024200908040011000414100504040010c04024200908040011000f24200908040010c04014100504040015000524200908040014c08014100c08040015000f14100504040014c0802420090804003d000f0c48431214002d00012420090804003d000f2420090804002d00010c484312140034341421200848040020a0800d0c0a0804003834140d0c0343040020a0802120084804002c15052120084804002090800d0c090804002415050d0c0343040020908021200848040011000411100444040010c04021200848040011000921200848040010c04011100444040015000521200848040014c08011100c08040015000911100444040014c0802120084804002500090d0c034304002100002120084804002500092120084804002100000d0c0343040034250520600818040018a0800c4c0a0804003025050c4c0313040018a0802060081804002c31212060081804001890800c4c090804002831210c4c0313040018908020600818040020252120600818040018848005450848040024252105450242140020848020600818040011000410500414040010c04020600818040011000720600818040010c04010500414040015000520600818040014c08010500c08040015000710500414040014c0802060081804001d00070c4c031304001900032060081804001d00072060081804001900030c4c0313040011000440014b03040010c04040010c04040011000530200c080400110004400110004400110004400107030 (by decide +kernel)

def state245_1 : List Sig := roots 245
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude245_1 : Impossible true (goalAt 245) 9 state245_1.toFinset :=
  node_ok cuts245 [⟨state245_0,exclude245_0⟩] 0x40010c0401c0c0c04040014b03030200c08080000c04030200c08040010b0301c0c0703040008b03018100604040008c04028200a08040008b03028200a08040008c04018100604040008703028200a08040008c08018100c08040008703018100604040008c08028200a08040004b03014100504040004c04024200908040004b03024200908040004c04014100504040004703024200908040004c08014100c08040004703014100504040004c08024200908040004341424200908040004a0800c484a0804000434140c484312140004a08024200908040000941411100444040000c04021200848040000941421200848040000c04011100444040000541421200848040000c08011100c08040000541411100444040000c08021200848040000341421200848040000a0800d0c0a0804000034140d0c0343040000a0802120084804000015052120084804000090800d0c090804000015050d0c034304000090802120084804000ca1211050041404000cc0402060081804000ca1212060081804000cc0401050041404000c61212060081804000cc08010500c0804000c61211050041404000cc08020600818040008250520600818040008a0800c4c0a0804000825050c4c0313040008a0802060081804000431212060081804000490800c4c090804000431210c4c03130400049080206008180400002521206008180400008480054508480400002521054502421400008480206008180 (by decide +kernel)

theorem lower245 : Claim 245 10 :=
  fromSearch 2098436 (by decide +kernel) exclude245_1


open PEqualNP.CircuitLowerBounds

def graph : Sig := goalAt 255
theorem graph_proper : proper graph := by unfold proper; decide +kernel

def edgeList : List Nat := [0, 4, 1, 4, 2, 5, 3, 5, 0, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7]
def target (x : Fin 8 → Bool) : Bool :=
  decide (∃ i < edgeList.length / 2,
    (List.ofFn x).getD (edgeList.getD (2*i) 0) false = true ∧
    (List.ofFn x).getD (edgeList.getD (2*i+1) 0) false = true)

def smallCircuit : Circuit := ⟨[⟨.or, [0, 2]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [6, 12]⟩, ⟨.or, [4, 7]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [10, 11]⟩, ⟨.and, [13, 14]⟩, ⟨.and, [5, 15]⟩, ⟨.or, [16, 17]⟩, ⟨.or, [19, 18]⟩], 20⟩

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


def lowRow (i : Fin 8) : Row := Fin.ofNat 256 (1 <<< ([4, 4, 5, 5, 0, 2, 0, 0] : List Nat).getD i.val 0)
def highRow (i : Fin 8) : Row := Fin.ofNat 256 ((1 <<< i.val) ||| (1 <<< ([4, 4, 5, 5, 0, 2, 0, 0] : List Nat).getD i.val 0))

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
  (ruleFor 255 lower245 none (by decide +kernel)).property 11 eightInputs
    (by decide +kernel) (by decide +kernel)

end PEqualNP.Outside.L_meta_31163_aux

open PEqualNP.Outside.L_meta_31163_aux in
theorem PEqualNP.Outside.L_meta_31163 : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 2, 5, 3, 5, 0, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 2, 5, 3, 5, 0, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 2, 5, 3, 5, 0, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 2, 5, 3, 5, 0, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 2, 5, 3, 5, 0, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 2, 5, 3, 5, 0, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true))  := by
  intro gates o fit _ correct
  exact replaceShort lowerGraph gates o fit correct

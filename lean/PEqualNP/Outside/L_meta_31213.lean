import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_31213_aux


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
  (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 3 &&& x 5) ||| (x 0 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 2 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7)


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




def cuts146 : Cuts (goalAt 146) := []

def state146_0 : List Sig := roots 146
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude146_0 : Impossible true (goalAt 146) 3 state146_0.toFinset :=
  node_ok cuts146 [] 0x24040120224040820224200908024040908024200820204808120220808121004840901020a00828020808828020a00901004840121004808828020a00908004840908004808121004840908020a008280 (by decide +kernel)

theorem lower146 : Claim 146 4 :=
  fromSearch 268501056 (by decide +kernel) exclude146_0

theorem lower210 : Claim 210 5 :=
  fromLift 5 64 335609920 lower146 (by decide +kernel)

theorem lower242 : Claim 242 6 :=
  fromLift 6 32 336658496 lower210 (by decide +kernel)

theorem lower218 : Claim 218 6 :=
  fromLift 6 8 318857280 lower210 (by decide +kernel)

theorem lower178 : Claim 178 5 :=
  fromLift 5 32 269549632 lower146 (by decide +kernel)

theorem lower186 : Claim 186 6 :=
  fromLift 6 8 269570112 lower178 (by decide +kernel)

def cuts120 : Cuts (goalAt 120) := []

def state120_0 : List Sig := roots 120
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude120_0 : Impossible true (goalAt 120) 3 state120_0.toFinset :=
  node_ok cuts120 [] 0x1c0c05818140c050301c0c070601c18048181410070601c18050600e0c068601a18038301210068601a18048601a18070600e0c06860 (by decide +kernel)

theorem lower120 : Claim 120 4 :=
  fromSearch 53891072 (by decide +kernel) exclude120_0

def cuts114 : Cuts (goalAt 114) := []

def state114_0 : List Sig := roots 114
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude114_0 : Impossible true (goalAt 114) 3 state114_0.toFinset :=
  node_ok cuts114 [] 0x1c0c062421890850301c0c070601c18012421490870601c18050600c8c06260189803230189086260189801230189807060141086260 (by decide +kernel)

theorem lower114 : Claim 114 4 :=
  fromSearch 68223040 (by decide +kernel) exclude114_0

def cuts106 : Cuts (goalAt 106) := []

def state106_0 : List Sig := roots 106
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude106_0 : Impossible true (goalAt 106) 3 state106_0.toFinset :=
  node_ok cuts106 [] 0xa82862421890822420a08068601a18028601290868601a180486008880626018980226018908626018980280a189806860121086260 (by decide +kernel)

theorem lower106 : Claim 106 4 :=
  fromSearch 51400784 (by decide +kernel) exclude106_0

def cuts90 : Cuts (goalAt 90) := []

def state90_0 : List Sig := roots 90
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude90_0 : Impossible true (goalAt 90) 3 state90_0.toFinset :=
  node_ok cuts90 [] 0x160605242149084818160604a42129085018129085242048284a42068605818120281a18149085040141085042129084840121084842 (by decide +kernel)

theorem lower90 : Claim 90 4 :=
  fromSearch 50421824 (by decide +kernel) exclude90_0

def cuts58 : Cuts (goalAt 58) := []

def state58_0 : List Sig := roots 58
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude58_0 : Impossible true (goalAt 58) 3 state58_0.toFinset :=
  node_ok cuts58 [] 0xe0602a0a0a06028180e06038300e0c0220a0a08038300e0c028300686032300c8c01a180888032300c8c022300c8c03830068603230 (by decide +kernel)

theorem lower58 : Claim 58 4 :=
  fromSearch 1134656 (by decide +kernel) exclude58_0

def rule122_0 : {c : Cut // CutGood (goalAt 122) c} :=
  ruleFor 122 lower120 none (by decide +kernel)

def rule122_1 : {c : Cut // CutGood (goalAt 122) c} :=
  ruleFor 122 lower114 none (by decide +kernel)

def rule122_2 : {c : Cut // CutGood (goalAt 122) c} :=
  ruleFor 122 lower106 none (by decide +kernel)

def rule122_3 : {c : Cut // CutGood (goalAt 122) c} :=
  ruleFor 122 lower90 none (by decide +kernel)

def rule122_4 : {c : Cut // CutGood (goalAt 122) c} :=
  ruleFor 122 lower58 none (by decide +kernel)

def cuts122 : Cuts (goalAt 122) := [rule122_0,rule122_1,rule122_2,rule122_3,rule122_4]

def state122_0 : List Sig := [0xffccffcc00000000ffccffcc00000000ffccffcc00000000ffccffcc,input 1,input 3,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude122_0 : Impossible true (goalAt 122) 4 state122_0.toFinset :=
  node_ok cuts122 [] 0x140c070601c18048180e0c068601a18038301a18070600e0c068600c8c06260189803230189807060149086260189806860121086260089086242189085030149087060149087060121806860129086860068606260189086260 (by decide +kernel)

def state122_1 : List Sig := [0xffccffccffccffccffccffccffccffccffccffccffccffccffccffccffccffcc,input 1,input 3,input 4,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude122_1 : Impossible true (goalAt 122) 5 state122_1.toFinset :=
  node_ok cuts122 [⟨state122_0,exclude122_0⟩] 0x7030189086242140c070301c18070601206052421c1807060141805818129084a421c0c04a42189083818129084a421c180120a1c1806860068607030120287030189083818189081a18149087060149087060129081a181210862601606070301606070301890a0000189090003149087060149087060 (by decide +kernel)

def state122_2 : List Sig := [0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc,input 1,input 4,input 3,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude122_2 : Impossible true (goalAt 122) 5 state122_2.toFinset :=
  node_ok cuts122 [] 0x7030189086242140c038301a18068600e0c04a421a18068601218068601490838301a1806860129084a421a18070301490852420490852421890838181490870600c8c07030128283230189083230189081a181290868601290868601490832301410862601c0c048081c0c04808189082808189082808 (by decide +kernel)

def state122_3 : List Sig := [0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 1,input 5,input 3,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude122_3 : Impossible true (goalAt 122) 5 state122_3.toFinset :=
  node_ok cuts122 [] 0x70301c18070601206052421c18070601490850401c18070601410038301a18068600e0c068601c18038301a1804a421a18068601290848401a18068601210070301890862420890838180c8c06260189803230189807060149086260189806860129086260189086260048c01a181c0c058181c0c05818 (by decide +kernel)

def state122_4 : List Sig := [0xffff0000ffff0000cccc0000cccc0000ffff0000ffff0000cccc0000cccc,input 1,input 6,input 3,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude122_4 : Impossible true (goalAt 122) 4 state122_4.toFinset :=
  node_ok cuts122 [] 0x1c0c062421890850301290868601a18048600e0c068601a1803830189086260189801a181898068601210862600c8c062601898032301418070601c18052421a18038301a18070601206070601c1807030189805042189807060 (by decide +kernel)

def state122_5 : List Sig := [0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,input 1,input 6,input 3,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude122_5 : Impossible true (goalAt 122) 5 state122_5.toFinset :=
  node_ok cuts122 [⟨state122_4,exclude122_4⟩] 0x38181890862420890838181890862420e06052421c1807060141801a0a1c18070600490a00001c1807060400084a421a18068601218068601c18038301a18038301a18068600e0c038301a18068600e0c07030189086260189803818189807060141086260189806860121086260128286260089803230 (by decide +kernel)

def state122_6 : List Sig := [0xffffff00ffffff000000000000000000ffffff00ffffff00,input 3,input 4,input 1,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude122_6 : Impossible true (goalAt 122) 4 state122_6.toFinset :=
  node_ok cuts122 [] 0x189086260189801a181898070601410862601898068601210862601490870601c18050601290868601a18048601a18070600e0c06860140c062421c0c062420c8c062600c8c062601206070601c0c070600e0c068600e0c06860 (by decide +kernel)

def state122_7 : List Sig := [0xffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00,input 3,input 4,input 1,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude122_7 : Impossible true (goalAt 122) 5 state122_7.toFinset :=
  node_ok cuts122 [⟨state122_6,exclude122_6⟩] 0x7030189086242140c032301898062600c8c062421898062600686062600c8c032301898062600e0c01a181898062600c8c032301898070301282870301206038181890828181890870600e0c070301406038300e06062420e0c062420682838300a0c068601c0c200001c0c100040e06062420e0606242 (by decide +kernel)

def state122_8 : List Sig := [0xffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00,input 3,input 5,input 1,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude122_8 : Impossible true (goalAt 122) 5 state122_8.toFinset :=
  node_ok cuts122 [] 0x70301c18070601206052421c18070601490852421c18070601490832301898062600c8c062601c1805042189801a181898062600686062601a1801a181898012101898062600484070301606070300e06062420e0c068601a18038301a18070600e0c068600e0606860121804a421c0c050101c0c05010 (by decide +kernel)

def state122_9 : List Sig := [0xffffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00,input 3,input 6,input 1,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude122_9 : Impossible true (goalAt 122) 5 state122_9.toFinset :=
  node_ok cuts122 [] 0x38181890862420e06022021890862420880852421c18070601418058181c18070601206012021c18070600480862421898062600686062601c18050421898032301898062600c8c062601a18048421898032301898062600c8c070301290868601a18048601a18070600682868601606068600a1803830 (by decide +kernel)

def state122_10 : List Sig := [0x3333333333330000333333333333000033333333333300003333333333330000,input 4,input 5,input 3,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude122_10 : Impossible true (goalAt 122) 4 state122_10.toFinset :=
  node_ok cuts122 [] 0xe0c068601a18038301210868601a18048421a18070600e0c068601c0c062421890850301c0c070601c18012401490870601c18050600c8c062601898032301898048421a18062600686062601898062421898050421c1806260 (by decide +kernel)

def state122_11 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,input 5,input 1,input 3,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude122_11 : Impossible true (goalAt 122) 5 state122_11.toFinset :=
  node_ok cuts122 [⟨state122_10,exclude122_10⟩] 0x38301a18068600e0c04a421a18068601290868601c18038301a1804a421a18068601290832301898062600c8c062601a1804842189801a181898062600686062601c1803230189820000189806260400007030160605030140c062421c0c070601c1804a0a0e06070601418052421c0c04a0a1c0c04a0a (by decide +kernel)

def state122_12 : List Sig := [0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 4,input 6,input 1,input 3,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude122_12 : Impossible true (goalAt 122) 5 state122_12.toFinset :=
  node_ok cuts122 [] 0x7030189086242140c02a0a1890862420a8284a421a18068601218038301a18068600e0c068601c18038301a18028201a18068600a08062421898062600686062601a18048421898032301898062600c8c062601c1805042189802220189806260088804a0a1490870601c18050601c0c07060120601a0a (by decide +kernel)

def state122_13 : List Sig := [0xff00ff00ff00ff00ff00ff0000000000ff00ff00ff00ff00ff00ff00000000,input 5,input 6,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude122_13 : Impossible true (goalAt 122) 4 state122_13.toFinset :=
  node_ok cuts122 [] 0x1c0c070601c18048181490870601c18050601898070601410862600c8c06260189803230189086260189801a181c0c062421890850301a18038301c18068601898048421898068600e0c068601a18038301218068601a1804a42 (by decide +kernel)

def state122_14 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 5,input 6,input 1,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude122_14 : Impossible true (goalAt 122) 5 state122_14.toFinset :=
  node_ok cuts122 [⟨state122_13,exclude122_13⟩] 0x70301c18070600682852421c1807060141801a0a1c18070600682868601c18038301a18038301a18068600e0c04a421a18068601218200001a18068604000462601c18050421898062601a18048421898032301898062600c8c06242189806260068601a181898062600686058181c0c06242140c03818 (by decide +kernel)

def state122_15 : List Sig := roots 122
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude122_15 : Impossible true (goalAt 122) 6 state122_15.toFinset :=
  node_ok cuts122 [⟨state122_1,exclude122_1⟩,⟨state122_2,exclude122_2⟩,⟨state122_3,exclude122_3⟩,⟨state122_5,exclude122_5⟩,⟨state122_7,exclude122_7⟩,⟨state122_8,exclude122_8⟩,⟨state122_9,exclude122_9⟩,⟨state122_11,exclude122_11⟩,⟨state122_12,exclude122_12⟩,⟨state122_14,exclude122_14⟩] 0x4001070300e06070304000c58181890862428002470301890862424000c58180e0605030400107030068287030400084a0a1c18070608002070301c1807060400084a0a0682848184000c38181490852424000862421c18070608001c38181c18070604000862421490850604001058180e0c038304000470301a18068608001858181a18068604000470300e0c038304000c3818129084a424000462421a18068608001438181a1806860400046242129084860400081a0a1a18068604000470600e0c07060800101a0a0e0c038304000470601a1806860400104a0a0c8c032304000070301898062608000c4a0a1898062604000070300c8c032304000c6242068606242400003818189806260800086242189806260400003818068601a184000852421898062604000070600c8c070608000452420c8c05042400007060189806260400044a42189806260400006860068606860800004a42068604842400006860189806260 (by decide +kernel)

theorem lower122 : Claim 122 7 :=
  fromSearch 51466304 (by decide +kernel) exclude122_15

theorem lower154 : Claim 154 5 :=
  fromLift 5 8 268529728 lower146 (by decide +kernel)

def cuts202 : Cuts (goalAt 202) := []

def state202_0 : List Sig := roots 202
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude202_0 : Impossible true (goalAt 202) 3 state202_0.toFinset :=
  node_ok cuts202 [] 0x309088a0a20908824212908c8c03230048c022200c8c03230088c030908c2c030b00880a20a00c2c030b0082c030b00c8c012108c2c0 (by decide +kernel)

theorem lower202 : Claim 202 4 :=
  fromSearch 318791792 (by decide +kernel) exclude202_0

theorem lower234 : Claim 234 5 :=
  fromLift 5 32 319836240 lower202 (by decide +kernel)

def cuts184 : Cuts (goalAt 184) := []

def state184_0 : List Sig := roots 184
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude184_0 : Impossible true (goalAt 184) 3 state184_0.toFinset :=
  node_ok cuts184 [] 0x2c0c09818240c090302c0c0b0a02c280881824200b0a02c28090a00e0c0a8a02a280383022200a8a02a28088a02a280b0a00e0c0a8a0 (by decide +kernel)

theorem lower184 : Claim 184 4 :=
  fromSearch 808931328 (by decide +kernel) exclude184_0

theorem lower248 : Claim 248 5 :=
  fromLift 5 64 859197440 lower184 (by decide +kernel)

def rule250_0 : {c : Cut // CutGood (goalAt 250) c} :=
  ruleFor 250 lower242 none (by decide +kernel)

def rule250_1 : {c : Cut // CutGood (goalAt 250) c} :=
  ruleFor 250 lower218 none (by decide +kernel)

def rule250_2 : {c : Cut // CutGood (goalAt 250) c} :=
  ruleFor 250 lower186 none (by decide +kernel)

def rule250_3 : {c : Cut // CutGood (goalAt 250) c} :=
  ruleFor 250 lower122 none (by decide +kernel)

def rule250_4 : {c : Cut // CutGood (goalAt 250) c} :=
  ruleFor 250 lower210 none (by decide +kernel)

def rule250_5 : {c : Cut // CutGood (goalAt 250) c} :=
  ruleFor 250 lower178 none (by decide +kernel)

def rule250_6 : {c : Cut // CutGood (goalAt 250) c} :=
  ruleFor 250 lower154 none (by decide +kernel)

def rule250_7 : {c : Cut // CutGood (goalAt 250) c} :=
  ruleFor 250 lower234 none (by decide +kernel)

def rule250_8 : {c : Cut // CutGood (goalAt 250) c} :=
  ruleFor 250 lower122 (some (1,input 1,input 3)) (by decide +kernel)

def rule250_9 : {c : Cut // CutGood (goalAt 250) c} :=
  ruleFor 250 lower248 none (by decide +kernel)

def rule250_10 : {c : Cut // CutGood (goalAt 250) c} :=
  ruleFor 250 lower146 none (by decide +kernel)

def rule250_11 : {c : Cut // CutGood (goalAt 250) c} :=
  ruleFor 250 lower120 none (by decide +kernel)

def rule250_12 : {c : Cut // CutGood (goalAt 250) c} :=
  ruleFor 250 lower202 none (by decide +kernel)

def rule250_13 : {c : Cut // CutGood (goalAt 250) c} :=
  ruleFor 250 lower184 none (by decide +kernel)

def rule250_14 : {c : Cut // CutGood (goalAt 250) c} :=
  ruleFor 250 lower106 none (by decide +kernel)

def rule250_15 : {c : Cut // CutGood (goalAt 250) c} :=
  ruleFor 250 lower122 (some (1,input 1,input 4)) (by decide +kernel)

def rule250_16 : {c : Cut // CutGood (goalAt 250) c} :=
  ruleFor 250 lower122 (some (1,input 1,input 5)) (by decide +kernel)

def rule250_17 : {c : Cut // CutGood (goalAt 250) c} :=
  ruleFor 250 lower122 (some (1,input 1,input 6)) (by decide +kernel)

def rule250_18 : {c : Cut // CutGood (goalAt 250) c} :=
  ruleFor 250 lower122 (some (1,input 3,input 4)) (by decide +kernel)

def rule250_19 : {c : Cut // CutGood (goalAt 250) c} :=
  ruleFor 250 lower122 (some (1,input 4,input 5)) (by decide +kernel)

def rule250_20 : {c : Cut // CutGood (goalAt 250) c} :=
  ruleFor 250 lower122 (some (1,input 4,input 6)) (by decide +kernel)

def cuts250 : Cuts (goalAt 250) := [rule250_0,rule250_1,rule250_2,rule250_3,rule250_4,rule250_5,rule250_6,rule250_7,rule250_8,rule250_9,rule250_10,rule250_11,rule250_12,rule250_13,rule250_14,rule250_15,rule250_16,rule250_17,rule250_18,rule250_19,rule250_20]

def state250_0 : List Sig := [0xffffffffffffffffffffffffffffffff00000000ffccffcc00000000ffccffcc,input 7,input 1,input 3,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_0 : Impossible true (goalAt 250) 5 state250_0.toFinset :=
  node_ok cuts250 [] 0xc242260608242209086242089086242140c0b0a03c380f0e02c30070603c380f0e01c18070603c380f0e01c180a8a03a380e8e02a300e8e03c38038303a38068603a380e8e01a18068603a380e8e01a180a2a038b80e2e028b00e2e03c380524238b80e2e03a380484238b80626038b80e2e018980626038b80e2e0189809030 (by decide +kernel)

def state250_1 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,0xffccffcc00000000ffccffcc,input 1,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_1 : Impossible true (goalAt 250) 4 state250_1.toFinset :=
  node_ok cuts250 [] 0x140c0f0e03c38048183a380f0e00e0c0e8e00e0c0e8e03a380383038b80f0e014908e2e038b80e8e012108e2e00c8c0e2e038b80323014908f0e014908f0e012180e8e012908e8e006860e2e018908e2e0089086242189085030 (by decide +kernel)

def state250_2 : List Sig := [0xffccffcc00000000ffccffcc,input 7,input 1,input 3,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_2 : Impossible true (goalAt 250) 5 state250_2.toFinset :=
  node_ok cuts250 [⟨state250_1,exclude250_1⟩] 0x5030240c20000140c0b0a03c380f0e02c30070603c380f0e01c300a8a03a380e8e02a300e8e03c38038303a38068603a380e8e01a300a2a038b80e2e028b00e2e03c380524238b80e2e03a380484238b80626038b80e2e018b002242189086242140c052423c38052423c38048603a3804a423a3801a1838b80624238b80c242 (by decide +kernel)

def state250_3 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,0xffccffcc00000000ffccffcc00000000ffccffcc00000000ffccffcc,input 1,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_3 : Impossible true (goalAt 250) 5 state250_3.toFinset :=
  node_ok cuts250 [⟨state250_1,exclude250_1⟩] 0x70603c380f0e01c20050303c380f0e012060e8e03c38038303a38068603a380e8e01a20038303a380e8e00e0c0e2e03c380524238b80e2e03a380484238b80626038b80e2e018a00323038b80e2e00c8c052423c38052423c380c8e03a3804a423a380c2e038b80624238b806242800008242189082242189086242140c09030 (by decide +kernel)

def state250_4 : List Sig := [0xffccffcc00000000ffccffcc00000000ffccffcc00000000ffccffcc,input 1,input 3,input 4,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_4 : Impossible true (goalAt 250) 6 state250_4.toFinset :=
  node_ok cuts250 [⟨state250_0,exclude250_0⟩,⟨state250_2,exclude250_2⟩,⟨state250_3,exclude250_3⟩] 0x3090850303090890304002890303090a0002209089030140c08242240c070601c180c2423c380f0e0240c0f0e03c380c2421c18070c0140c0b0a02c2804a0a3c380f0e0140c0f0e03c3804a0a2c280b0c02606068601a180c2423a380e8e026060e8e03a380c2421a18068c016060a8a02a28050303a380e8e016060e8e03a38050302a280a8c006828e8e03a380f0e00e0c0f0e00682838300e0c0f0e03a380e8e030908626018980903038b80e2e030908e2e038b8090301898062c012828a2a028a80503038b80e2e012828e2e038b80503028a80a2c014908e2e038b80f0e00c8c0f0e014908323014908f0e038b80e2e012908e2e038b80e8e006860e8e0129081a1812108e8e038b80e2e03090862421890890308000490303090a00003090890301890862421606038180890850301890862421606062421890850300e060503014908624214908f0e00e060f0e014908381814908f0e018908f0e012908624232380e8e00e060e8e012908381812908e8e018908e8e006860381830b80e2e018908e2e006860624218908e2e00e060e2e0 (by decide +kernel)

def state250_5 : List Sig := [0xffffffcc00000000ffffffcc00000000ffffffcc00000000ffffffcc,input 4,input 1,input 3,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_5 : Impossible true (goalAt 250) 5 state250_5.toFinset :=
  node_ok cuts250 [] 0x30908b0302090882421a180e8e03a38068c02a280e8e03a380a8c03a380f0e00e0c0e8e018980e2e038b8062c028a80e2e038b80a2c038b80e8e012108e2e038b80f0e014108e2e01c180f0e03c38070c02c280f0e03c380b0c0189089030309086242140c0624218908703032380e8e012908e8e030b80e2e018908e2e034380f0e014908f0e0 (by decide +kernel)

def state250_6 : List Sig := [0xffffffccffffffcc0000000000000000ffffffccffffffcc,input 4,input 1,input 3,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_6 : Impossible true (goalAt 250) 5 state250_6.toFinset :=
  node_ok cuts250 [] 0x18908c242240c062421a180e8e03a38068a032300e8e03a380c8e03a380f0e00e0c0e8e018980e2e038b8062a030b00e2e038b80c2e038b80e8e012108e2e038b80f0e014108e2e01c180f0e03c38070a034300f0e03c380d0e02090882422c0c0c242140c062421c0c062422a380e8e00e0c0e8e028b80e2e00c8c0e2e02c380f0e01c0c0f0e0 (by decide +kernel)

def state250_7 : List Sig := [0xffffffccffffffccffffffccffffffcc,input 4,input 1,input 3,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_7 : Impossible true (goalAt 250) 5 state250_7.toFinset :=
  node_ok cuts250 [] 0x1c0c062421890850302a280e8e03a380a8e032300e8e03a380c8e03a380f0e00e0c0e8e028a80e2e038b80a2e030b00e2e038b80c2e038b80e8e012108e2e038b80f0e014108e2e02c280f0e03c380b0e034300f0e03c380d0e020908824230908b03018908903018908c2421a380e8e012908e8e018b80e2e030908e2e01c380f0e014908f0e0 (by decide +kernel)

def state250_8 : List Sig := [0xffffffccffffffccffffffccffffffccffffffccffffffccffffffccffffffcc,input 4,input 1,input 3,input 5,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_8 : Impossible true (goalAt 250) 6 state250_8.toFinset :=
  node_ok cuts250 [⟨state250_5,exclude250_5⟩,⟨state250_6,exclude250_6⟩,⟨state250_7,exclude250_7⟩] 0xc2422c0c08242209086242309089030189087030189086242140c04a42309089018129083830129084a420e0c04a42189083830129084a4214908383012908e8e030908b0303090832300c8c07030120283230189083230189081a1812908383012108484214908323014108504238b80524230908b03014908703014908524212060524218908281814908f0e03090a00023090900031c0c200011c0c100021890a0000189090001 (by decide +kernel)

def state250_9 : List Sig := [0xffcc0000ffcc0000ffcc0000ffcc0000ffcc0000ffcc0000ffcc0000ffcc,input 4,input 1,input 3,input 5,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_9 : Impossible true (goalAt 250) 6 state250_9.toFinset :=
  node_ok cuts250 [] 0xc2422c0c08242209086242309089030189087030189086242140c04a42309089018129083830129084a420e0c04a4218908383012908f8e03c38038303c380c2422c0c0c2420c8c032301c0c0480a0c8c062420c8c06242068604a420e0c0484212108f2e03c38032303c38070603c380f0e01c380b0a03c380f0e02c380d0c03c380f0e034380c2422c0c0c2422c0c04a0a1c0c04a0a1c0c062420e06062420e060e8e03a3804a420e0c0e2e038b8100000c8c05242 (by decide +kernel)

def state250_10 : List Sig := [0xffccffcc00000000ffccffcc00000000ffccffcc00000000ffccffcc,0xffccffccffccffccffccffccffccffccffccffccffccffccffccffccffccffcc,input 1,input 3,input 4,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_10 : Impossible true (goalAt 250) 6 state250_10.toFinset :=
  node_ok cuts250 [] 0x3090890302090882421c180f0e03c38070c02c280f0e03c380b0c012908c242260604a42160604a4212908503012908f0e004828f0e03a380c242240c0c242240c01a18140c0480a140c052423c38052423c3804a4206860484238b80c242240c0c242240c05818140c05818140c052423c38052423c3806242240c0c242189082242189086242140c052423c38052423c3804a420e0604a42189081a181890862420e0610001 (by decide +kernel)

def state250_11 : List Sig := [0xffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00,0xffffffffcccc0000ffffffffcccc0000ffffffffcccc0000ffffffffcccc0000,0xffccffccffccffccffccffccffccffccffccffccffccffccffccffccffccffcc,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_11 : Impossible true (goalAt 250) 4 state250_11.toFinset :=
  node_ok cuts250 [] 0x30908b03020908824218980e2e038b8062e028a80e2e038b80a2e030b00e2e038b80c2e038b80e8e012108e2e018908c242240c062421c0c062421890850301c180f0e03c38070e02c280f0e03c380b0e034300f0e03c380d0e0 (by decide +kernel)

def state250_12 : List Sig := [0xffffffffcccc0000ffffffffcccc0000ffffffffcccc0000ffffffffcccc0000,input 4,0xffccffccffccffccffccffccffccffccffccffccffccffccffccffccffccffcc,input 3,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_12 : Impossible true (goalAt 250) 5 state250_12.toFinset :=
  node_ok cuts250 [⟨state250_11,exclude250_11⟩] 0xc2422c0c082422090848423090898181210858181210848421c0c0e8e012108f0e080000f0e012108624206860484218980e2e038b8062e028a80e2e038b80a2e038b80f0e014108e2e030b00e2e038b80c2e01c180f0e03c38070e02c280f0e03c380b0e034300f0e03c380d0e018908c242240c062421c0c06242189085030 (by decide +kernel)

def state250_13 : List Sig := [0xffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00,0xffffffffffffffffcccc0000cccc0000ffffffffffffffffcccc0000cccc0000,0xffccffccffccffccffccffccffccffccffccffccffccffccffccffccffccffcc,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_13 : Impossible true (goalAt 250) 4 state250_13.toFinset :=
  node_ok cuts250 [] 0x18908c242240c062421c0c0624218908503018980e2e038b8062e030b00e2e038b80c2e028a80e2e038b80a2e038b80e8e012108e2e030908b0302090882421c180f0e03c38070e034300f0e03c380d0e02c280f0e03c380b0e0 (by decide +kernel)

def state250_14 : List Sig := [0xffffffffffffffffcccc0000cccc0000ffffffffffffffffcccc0000cccc0000,input 4,0xffccffccffccffccffccffccffccffccffccffccffccffccffccffccffccffcc,input 3,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_14 : Impossible true (goalAt 250) 5 state250_14.toFinset :=
  node_ok cuts250 [⟨state250_13,exclude250_13⟩] 0x6242309089030189087030189086242140c0484230908981812108484218908381812108e8e012108f0e080000f0e006860484212108703018980e2e038b8062e030b00e2e038b80c2e038b80f0e014108e2e028a80e2e038b80a2e01c180f0e03c38070e034300f0e03c380d0e02c280f0e03c380b0e030908b030209088242 (by decide +kernel)

def state250_15 : List Sig := [0xffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00,0xffffffffffffffffffffffffffffffffcccc0000cccc0000cccc0000cccc0000,0xffccffccffccffccffccffccffccffccffccffccffccffccffccffccffccffcc,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_15 : Impossible true (goalAt 250) 4 state250_15.toFinset :=
  node_ok cuts250 [] 0x30908b0302090882421c0c0624218908503018908c242240c0624228a80e2e038b80a2e030b00e2e038b80c2e018980e2e038b8062e038b80e8e012108e2e02c280f0e03c380b0e034300f0e03c380d0e01c180f0e03c38070e0 (by decide +kernel)

def state250_16 : List Sig := [0xffffffffffffffffffffffffffffffffcccc0000cccc0000cccc0000cccc0000,input 4,0xffccffccffccffccffccffccffccffccffccffccffccffccffccffccffccffcc,input 3,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_16 : Impossible true (goalAt 250) 5 state250_16.toFinset :=
  node_ok cuts250 [⟨state250_15,exclude250_15⟩] 0xc2422c0c08242209087030189086242140c062423090890301890858181210848421c0c0484218908381812108e8e012108f0e080000f0e012108c24206860484228a80e2e038b80a2e030b00e2e038b80c2e038b80f0e014108e2e018980e2e038b8062e02c280f0e03c380b0e034300f0e03c380d0e01c180f0e03c38070e0 (by decide +kernel)

def state250_17 : List Sig := [0xffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00,0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000,0xffccffccffccffccffccffccffccffccffccffccffccffccffccffccffccffcc,input 5,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_17 : Impossible true (goalAt 250) 5 state250_17.toFinset :=
  node_ok cuts250 [⟨state250_11,exclude250_11⟩,⟨state250_13,exclude250_13⟩,⟨state250_15,exclude250_15⟩] 0x30908b03020908824218908c242240c062421c0c0624218908503018980e2e038b8062e028a80e2e038b80a2e030b00e2e038b80c2e038b80e8e012108e2e006860c24280008c2420686070308000470300686062428000062420c8c052421c180f0e03c38070e02c280f0e03c380b0e034300f0e03c380d0e0 (by decide +kernel)

def state250_18 : List Sig := [0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000,input 4,0xffccffccffccffccffccffccffccffccffccffccffccffccffccffccffccffcc,input 3,input 5,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_18 : Impossible true (goalAt 250) 6 state250_18.toFinset :=
  node_ok cuts250 [⟨state250_12,exclude250_12⟩,⟨state250_14,exclude250_14⟩,⟨state250_16,exclude250_16⟩,⟨state250_17,exclude250_17⟩] 0xc2422c0c08242209086242309089030189087030189086242140c048423090898181210858181210848421c0c0484218908381812108e8e012108f0e08000cf0e018980e2e038b8062e028a80e2e038b80a2e030b00e2e038b80c2e038b80f0e014108e2e01c180f0e03c38070e02c280f0e03c380b0e034300f0e03c380d0e006860c24280008c2420686070308000470300686062428000062424000048420686048420c8c05242 (by decide +kernel)

def state250_19 : List Sig := [0x3333000033330000333300003333000033330000333300003333000033330000,input 4,0xffccffccffccffccffccffccffccffccffccffccffccffccffccffccffccffcc,input 3,input 5,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_19 : Impossible true (goalAt 250) 6 state250_19.toFinset :=
  node_ok cuts250 [] 0x30908b03020908824218908c242240c062421c0c0624218908503012108c2422606048421606048421210870301210862420e06048423a380484214908120a12108626038b80e2e018b80a2a038b80e2e028b80c2c038b80e2e030b80e2e03cb80524238b80524230908b03014908703014908524204908524218908381814908b03030908b030309087030120287030068601a18189083818189081218121081a1812109000038b80323038b80f0e0 (by decide +kernel)

def state250_20 : List Sig := [0xffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00,input 4,0xffccffccffccffccffccffccffccffccffccffccffccffccffccffccffccffcc,input 1,input 5,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_20 : Impossible true (goalAt 250) 6 state250_20.toFinset :=
  node_ok cuts250 [⟨state250_17,exclude250_17⟩] 0x30908b03020908824218908c242240c062421c0c0624218908503030908b03030908b030068607030120287030189083218189081a1838b80120a068601a18800004a4206860484212108c2422c0c0c2420e0c038301c0c050180e0c062420e0c0624240010120a0e0c038300a0c0e8e03a3804a424001cb03030908b03030908703012828703012060381818908281818908f0e012908c2422c0c04a421c0c04a421290900051290862420e0604a42 (by decide +kernel)

def state250_21 : List Sig := [0xffccffccffccffccffccffccffccffccffccffccffccffccffccffccffccffcc,input 1,input 3,input 4,input 5,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_21 : Impossible true (goalAt 250) 7 state250_21.toFinset :=
  node_ok cuts250 [⟨state250_4,exclude250_4⟩,⟨state250_8,exclude250_8⟩,⟨state250_9,exclude250_9⟩,⟨state250_10,exclude250_10⟩,⟨state250_18,exclude250_18⟩,⟨state250_19,exclude250_19⟩,⟨state250_20,exclude250_20⟩] 0xc2421c0c0c2422c0c100052c0c0c2424002082422c0c0703020908b03018908624230909000430908b0304002090303090862421890870300e0607030160606242189087030189086242160603818140c0b0301c180706030908f0e03c380b0303c380f0e03090870601c38070302c280b0a012828f0e03c38070303c380f0e012828b0a02c380381834300d0c018908f0e03c38038183c380f0e018908d0c0343809818129084a42309090000309089818400209818309084a421290858184001458181c0c04a42129085818129084a421c0c100001c0c03818129084a42189090000189083818400103818189084a42129081a0a129084a423c38100003c3801a0a80018120a3c3804a423c381000040024e8e0309081a1830908b03040020b03030909000830908b03006860b030128281a18068607030400147030128290005120287030068607030189081a18189083818400103818189090004189083818068601a181490a000514908f0e006860f0e0149081a1814908f0e080010f0e0129090000129090009068601a1840001000012109000040000e2e030909000330908b03040020b03030909000830908b0304000cb0301606100021606070304001470301606100051606070304000870301890900011890a000340012000018909000418909000440005000114909000714908f0e080008f0e01490a000114908f0e04001cf0e0 (by decide +kernel)

def state250_22 : List Sig := [0xffffffffffffffff00cc00cc00cc00ccffffffffffffffff00cc00cc00cc00cc,input 1,input 3,input 4,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_22 : Impossible true (goalAt 250) 6 state250_22.toFinset :=
  node_ok cuts250 [] 0x2c0c062421890882424002c82422c0c1000b240c082421890862421c0c038181c0c058181890862421c0c062421890858180e06050302c0c070601c18082423c380f0e02c0c0f0e03c38082421c18070e00e060d0c03430062423c380f0e00e060f0e03c380624234300d0e01c0c0b0a02c2804a0a3c380f0e01c0c0f0e03c3804a0a2c280b0e02606068601a18082423a380e8e026060e8e03a38082421a18068e00e060c8c03230062423a380e8e00e060e8e03a380624232300c8e006828e8e03a380f0e00e0c0f0e00682838300e0c0f0e03a380e8e016060a8a02a28070303a380e8e016060e8e03a38070302a280a8e020908626018980b03038b80e2e020908e2e038b80b0301898062e018908c2c030b00381838b80e2e018908e2e038b80381830b00c2e014908e2e038b80f0e006860f0e0149081a1814108f0e038b80e2e012908e2e038b80e8e006860e8e0129081a1812108e8e038b80e2e0128281a1828a80703038b80e2e012828e2e038b80703006860703020908703020908b0304002cb03020909000b20908b0301c0c07030 (by decide +kernel)

def state250_23 : List Sig := [0xffff00ccffff00ccffff00ccffff00ccffff00ccffff00ccffff00ccffff00cc,input 4,input 1,input 3,input 5,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_23 : Impossible true (goalAt 250) 6 state250_23.toFinset :=
  node_ok cuts250 [] 0xc2422c0c08242209086242309089030189087030189086242140c068603a380e8e01a380a8a03a380e8e02a380c8c03a380e8e032380e8e01490838303a380e8e00e0c04a423a380c2422c0c0c2420c8c032301c0c0480a0c8c062420c8c0624206860eae03a3801a183a38052420c8c0504214108e2e038b80323040000524230908b03014908703014908524204908524218908381814908f0e0309088a0a309088a0a1c0c04a0a1c0c04a0a189082a0a189082a0a (by decide +kernel)

def state250_24 : List Sig := [0x3333000033330000333300003333000033330000333300003333000033330000,input 4,0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,input 3,input 5,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_24 : Impossible true (goalAt 250) 6 state250_24.toFinset :=
  node_ok cuts250 [] 0xc2422c0c08242209086242309089030189087030189086242140c068603a380e8e01ab80a8a03a380e8e02ab80c8c03a380e8e032b80e8e03eb8038303a380626038b80e2e018b80a2a038b80e2e028b80c2c038b80e2e030b80484238b80f2e014908e2e00c8c0524230908b03014908703014908524204908524218908381814908b03030908b030309087030120287030068601a181890838181890838303a38038303a380f0e0 (by decide +kernel)

def state250_25 : List Sig := [0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,input 1,input 3,input 4,input 5,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_25 : Impossible true (goalAt 250) 7 state250_25.toFinset :=
  node_ok cuts250 [⟨state250_22,exclude250_22⟩,⟨state250_23,exclude250_23⟩,⟨state250_24,exclude250_24⟩] 0xc2421c0c0c2422c0c100052c0c0c2424002c82422c0c0703020908b03018908624230909000430908b0304002c90303090862421890870300e0607030160606242189087030189086242160603818140c0b0301c180706030908f0e03c380b0303c380f0e03090870601c38070302c280b0a012828f0e03c38070303c380f0e012828b0a02c380381834300d0c018908f0e03c38038183c380f0e018908d0c03438098181a180686030908e8e03a38098183a380e8e03090868601a38058182a280a8a01c0c0e8e03a38058183a380e8e01c0c0a8a02a380381832300c8c018908e8e03a38038183a380e8e018908c8c0323801a0a3a380e8e03c38038303c3801a0a0e0c038303c380e8e03a380c24206860c2422c0c100092c0c0c2424002cc2422c0c01a182c0c04a0a068601a181c0c100091c0c04a0a40014480a1c0c01a181c0c062420686062420e06100040e06062424001062420e0601a180686052428000852423c3801a183c38052420686052423c38100093c381000040000eae0400241a1806860e8e040000e8e030909000330908b03040024b03030909000b30908b0304000cb03040025000240008703040024703040025000580000703040008703018909000118908381840010381818909000418908381840004381814909000714908f0e040024f0e01490a000114908f0e04001cf0e040025000012909000040000e2e0 (by decide +kernel)

def state250_26 : List Sig := [0xffccff00ffccff00ffccff00ffccff00ffccff00ffccff00ffccff00ffccff00,input 1,input 4,input 5,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_26 : Impossible true (goalAt 250) 6 state250_26.toFinset :=
  node_ok cuts250 [] 0x30908703030908b03040038b03030909000e20908b0301c0c082422c0c0624218908c24240038c2422c0c1000e240c0c2421890862421c0c038181c0c058181890862421c0c062421890858180e06050302c0c070601c180c2423c380f0e02c0c0f0e03c380c2421c18070e01c0c0b0a02c2804a0a3c380f0e01c0c0f0e03c3804a0a2c280b0e00e060d0c03430062423c380f0e00e060f0e03c380624234300d0e030908626018980b03038b80e2e030908e2e038b80b0301898062e012828a2a028a80703038b80e2e012828e2e038b80703028a80a2e018908c2c030b00381838b80e2e018908e2e038b80381830b00c2e004828e2e038b80f0e006860f0e0048281a1814108f0e038b80e2e012908e2e038b80e8e006860e8e0129081a1812108e8e038b80e2e02606068601a180c2423a380e8e026060e8e03a380c2421a18068e016060a8a02a28070303a380e8e016060e8e03a38070302a280a8e00e060c8c03230062423a380e8e00e060e8e03a380624232300c8e004828e8e03a380f0e00e0c0f0e00482838300e0c0f0e03a380e8e0 (by decide +kernel)

def state250_27 : List Sig := [0xffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00,input 3,0xffffffffcccc0000ffffffffcccc0000ffffffffcccc0000ffffffffcccc0000,input 1,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_27 : Impossible true (goalAt 250) 5 state250_27.toFinset :=
  node_ok cuts250 [⟨state250_11,exclude250_11⟩] 0xc2422c0c0824220908626038b80e2e018b80a2a038b80e2e028b80c2c038b80e2e030b80e2e00e0c2000038b80e2e03c380504238b806242309089030189087030189086242140c038303090888183090838301a0c048180e0c0281818908383018908e8e01c180f0e03c38070e02c280f0e03c380b0e034300f0e03c380d0e0 (by decide +kernel)

def state250_28 : List Sig := [0xffffffffcccc0000ffffffffcccc0000ffffffffcccc0000ffffffffcccc0000,input 1,input 4,input 3,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_28 : Impossible true (goalAt 250) 6 state250_28.toFinset :=
  node_ok cuts250 [⟨state250_12,exclude250_12⟩,⟨state250_27,exclude250_27⟩] 0x30908703030908b03040038b03030909000e20908b0301c0c082422606068601a180c2423a380e8e026060e8e03a380c2421a18068e016060a8a02a28070303a380e8e016060e8e03a38070302a280a8e04001ce8e03a380f0e00e0c0f0e08000438300e0c0f0e03a380e8e00e060c8c03230062423a380e8e00e060e8e03a380624232300c8e02c0c070601c180c2423c380f0e02c0c0f0e03c380c2421c18070e01c0c0b0a02c2804a0a3c380f0e01c0c0f0e03c3804a0a2c280b0e00e060d0c03430062423c380f0e00e060f0e03c380624234300d0e030908626018980b03038b80e2e030908e2e038b80b0301898062e012828a2a028a80703038b80e2e012828e2e038b80703028a80a2e012908e2e038b80e8e040024e8e01290a000012108e8e038b80e2e04001ce2e038b80f0e00c8c0f0e040024323014108f0e038b80e2e018908c2c030b00381838b80e2e018908e2e038b80381830b00c2e02c0c0624218908c24240038c2422c0c1000e240c0c2421890862421c0c038181c0c058181890862421c0c062421890858180e0605030 (by decide +kernel)

def state250_29 : List Sig := [0xffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00,input 3,0xffffffffffffffffcccc0000cccc0000ffffffffffffffffcccc0000cccc0000,input 1,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_29 : Impossible true (goalAt 250) 5 state250_29.toFinset :=
  node_ok cuts250 [⟨state250_13,exclude250_13⟩] 0x6242309089030189087030189086242140c0626038b80e2e018b80c2c038b80e2e030b80a2a038b80e2e028b80e2e00e0c2000038b80e2e03c380504238b80c2422c0c082422090838303090888183090828181890838301890838301a0c048180e0c0e8e01c180f0e03c38070e034300f0e03c380d0e02c280f0e03c380b0e0 (by decide +kernel)

def state250_30 : List Sig := [0xffffffffffffffffcccc0000cccc0000ffffffffffffffffcccc0000cccc0000,input 1,input 4,input 3,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_30 : Impossible true (goalAt 250) 6 state250_30.toFinset :=
  node_ok cuts250 [⟨state250_14,exclude250_14⟩,⟨state250_29,exclude250_29⟩] 0x2c0c0624218908c24240038c2422c0c1000e240c0c2421890862421c0c038181c0c058181890862421c0c062421890858180e06050302606068601a180c2423a380e8e026060e8e03a380c2421a18068e00e060c8c03230062423a380e8e00e060e8e03a380624232300c8e04001ce8e03a380f0e00e0c0f0e08000438300e0c0f0e03a380e8e016060a8a02a28070303a380e8e016060e8e03a38070302a280a8e02c0c070601c180c2423c380f0e02c0c0f0e03c380c2421c18070e00e060d0c03430062423c380f0e00e060f0e03c380624234300d0e01c0c0b0a02c2804a0a3c380f0e01c0c0f0e03c3804a0a2c280b0e030908626018980b03038b80e2e030908e2e038b80b0301898062e018908c2c030b00381838b80e2e018908e2e038b80381830b00c2e012908e2e038b80e8e040024e8e01290a000012108e8e038b80e2e014908e2e038b80f0e04001cf0e014909000714108f0e038b80e2e012828a2a028a80703038b80e2e012828e2e038b80703028a80a2e030908703030908b03040038b03030909000e20908b0301c0c08242 (by decide +kernel)

def state250_31 : List Sig := [0xffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00,input 3,0xffffffffffffffffffffffffffffffffcccc0000cccc0000cccc0000cccc0000,input 1,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_31 : Impossible true (goalAt 250) 5 state250_31.toFinset :=
  node_ok cuts250 [⟨state250_15,exclude250_15⟩] 0xc2422c0c08242209087030189086242140c0624230908903018908a2a038b80e2e028b80c2c038b80e2e030b80626038b80e2e018b80e2e00e0c2000038b80e2e03c380504238b8038301a0c048180e0c0281818908383018908383030908881830908e8e02c280f0e03c380b0e034300f0e03c380d0e01c180f0e03c38070e0 (by decide +kernel)

def state250_32 : List Sig := [0xffffffffffffffffffffffffffffffffcccc0000cccc0000cccc0000cccc0000,input 1,input 4,input 3,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_32 : Impossible true (goalAt 250) 6 state250_32.toFinset :=
  node_ok cuts250 [⟨state250_16,exclude250_16⟩,⟨state250_31,exclude250_31⟩] 0x30908703030908b03040038b03030909000e20908b0301c0c082421c0c038181c0c058181890862421c0c062421890858180e06050302c0c0624218908c24240038c2422c0c1000e240c0c24218908624216060a8a02a28070303a380e8e016060e8e03a38070302a280a8e00e060c8c03230062423a380e8e00e060e8e03a380624232300c8e04001ce8e03a380f0e00e0c0f0e08000438300e0c0f0e03a380e8e02606068601a180c2423a380e8e026060e8e03a380c2421a18068e01c0c0b0a02c2804a0a3c380f0e01c0c0f0e03c3804a0a2c280b0e00e060d0c03430062423c380f0e00e060f0e03c380624234300d0e02c0c070601c180c2423c380f0e02c0c0f0e03c380c2421c18070e012828a2a028a80703038b80e2e012828e2e038b80703028a80a2e018908c2c030b00381838b80e2e018908e2e038b80381830b00c2e012908e2e038b80e8e040024e8e01290a000012108e8e038b80e2e04001ce2e038b80f0e04001cf0e040025000714108f0e038b80e2e030908626018980b03038b80e2e030908e2e038b80b0301898062e0 (by decide +kernel)

def state250_33 : List Sig := [0xffccff00ffccff00ffccff00ffccff00ffccff00ffccff00ffccff00ffccff00,input 3,input 1,input 4,input 5,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_33 : Impossible true (goalAt 250) 6 state250_33.toFinset :=
  node_ok cuts250 [] 0xc2422c0c08242209086242309089030189087030189086242140c070603c380f0e01c380b0a03c380f0e02c380d0c03c380f0e034380626038b80e2e018b80a2a038b80e2e028b80c2c038b80e2e030b80e2e03c380504238b80e2e0068601a1838b80e2e00c8c01a1838b8098183090898183090858181c0c058181c0c03818189083818189081a0a3c380120a3c380e8e026060c24226060c2421606070301606070300e06062420e060624214908f0e006828f0e0 (by decide +kernel)

def state250_34 : List Sig := [0xffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00,input 3,0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000,input 1,input 5,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_34 : Impossible true (goalAt 250) 6 state250_34.toFinset :=
  node_ok cuts250 [⟨state250_27,exclude250_27⟩,⟨state250_29,exclude250_29⟩,⟨state250_31,exclude250_31⟩,⟨state250_17,exclude250_17⟩] 0xc2422c0c08242209086242309089030189087030189086242140c0626038b80e2e018b80a2a038b80e2e028b80c2c038b80e2e030b80e2e00e0c2000338b80e2e03c380504238b801a0a3090a0002309081a0a1c0c200011c0c01a0a1890a00001890832304000038300482838301490838303090888183090838301a0c048180e0c0281818908383018908e8e01c180f0e03c38070e02c280f0e03c380b0e034300f0e03c380d0e0 (by decide +kernel)

def state250_35 : List Sig := [0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000,input 1,input 4,input 3,input 5,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_35 : Impossible true (goalAt 250) 7 state250_35.toFinset :=
  node_ok cuts250 [⟨state250_18,exclude250_18⟩,⟨state250_26,exclude250_26⟩,⟨state250_28,exclude250_28⟩,⟨state250_30,exclude250_30⟩,⟨state250_32,exclude250_32⟩,⟨state250_33,exclude250_33⟩,⟨state250_34,exclude250_34⟩] 0xc2421c0c0c2422c0c1000e2c0c0c2424003882422c0c0703020908b03018908624230909000e30908b0304003890303090862421890870300e0607030160606242189087030189086242160603818140c098181a180686030908e8e03a38098183a380e8e03090868601a38058182a280a8a01c0c0e8e03a38058183a380e8e01c0c0a8a02a380381832300c8c018908e8e03a38038183a380e8e018908c8c03238100073a380e8e03c38038303c38200060e0c038303c380e8e03a380b0301c180706030908f0e03c380b0303c380f0e03090870601c38070302c280b0a012828f0e03c38070303c380f0e012828b0a02c380381834300d0c018908f0e03c38038183c380f0e018908d0c034380c2421898062602c0c0e2e038b80c24238b80e2e02c0c0626018b804a0a28a80a2a01c0c0e2e038b804a0a38b80e2e01c0c0a2a028b80624230b00c2c00e060e2e038b80624238b80e2e00e060c2c030b804a4238b80e2e03a38100093a3804a428000048423a380e2e038b81000738b80e2e03c38100073c38100094001c50424001d00034000cc2424001cc2424001d000e80010c2424000cc2424001d00024000870304001c70304001d000d8000c70304000870304001d00014000462424001c62424001d000c8000862424000462424001d000040000e8e04001ce8e04001e000580004e8e040000e8e04001d0007149090007400243230 (by decide +kernel)

def state250_36 : List Sig := [0xffffffffffffccccffffffffffffccccffffffffffffccccffffffffffffcccc,input 5,input 1,input 4,input 3,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_36 : Impossible true (goalAt 250) 6 state250_36.toFinset :=
  node_ok cuts250 [] 0xc2422c0c082422090868603a380e8e01a380a8a03a380e8e02a380e8e03c38038303a380c8c03a380e8e032300c8c03a380e8e03230070603c380f0e01c380b0a03c380f0e02c38052423c380f0e034380d0c018980e2e038b8062e028a80e2e038b80a2e038b80e8e012908e2e038b80f0e014108e2e018908e2e038b80c2e030b006242309089030189087030189086242140c028083090888083090888081c0c048081c0c04808 (by decide +kernel)

def state250_37 : List Sig := [0xffffcccc00000000ffffcccc00000000ffffcccc00000000ffffcccc,input 5,input 1,input 4,input 3,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_37 : Impossible true (goalAt 250) 6 state250_37.toFinset :=
  node_ok cuts250 [] 0xc2422c0c082422090868603a380e8e01a380a8a03a380e8e02a380e8e03c38038303a380c8c03a380e8e03238070603c380f0e01c380b0a03c380f0e02c380f0c03c380f0e014908626038b80e2e018b80a2a038b80e2e028b80e2e03a3804a4238b80e2e03c380504238b80e2c038b80e2e006860b03030908b03030908703016060703016060c2422c0c0c2422c0c058181c0c058181c0c04a423a3804a423a380d0c03c38052423c380c2c038b801a1838b806242 (by decide +kernel)

def state250_38 : List Sig := [0xffffffffffffffffffffccccffffccccffffffffffffffffffffccccffffcccc,input 6,input 1,input 4,input 3,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_38 : Impossible true (goalAt 250) 6 state250_38.toFinset :=
  node_ok cuts250 [] 0x6242309089030189087030189086242140c028081890862420a02068603a380e8e01a380c8c03a380e8e032380e8e03c38038303a380a8a03a380e8e02a280a8a03a380e8e02a28070603c380f0e01c380d0c03c380f0e03438070303c380f0e02c380b0a018980e2e038b8062e030b00e2e038b80c2e038b80e8e012108e2e038b80f0e014108e2e00c8c0e2e038b80a2e028a80c2422c0c08242209084808309088808309088808 (by decide +kernel)

def state250_39 : List Sig := [0xffffccccffffcccc0000000000000000ffffccccffffcccc,input 6,input 1,input 4,input 3,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_39 : Impossible true (goalAt 250) 6 state250_39.toFinset :=
  node_ok cuts250 [] 0x62423090890301890838181890862420e06068603a380e8e01a380c8c03a380e8e032380e8e03c38038303a380a8a03a380e8e02a38070603c380f0e01c380d0c03c380f0e034380f0a03c380f0e006828626038b80e2e018b80c2c038b80e2e030b80e2e03a380484238b80e2e03c380504238b80e2a038b80e2e00c8c0c2422c0c0c2422c0c0b03030908b0303090838181890838181890838303a38038303a380b0a03c3801a0a3c380a2a038b80323038b807030 (by decide +kernel)

def state250_40 : List Sig := [0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,input 6,0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc,input 4,input 3,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_40 : Impossible true (goalAt 250) 6 state250_40.toFinset :=
  node_ok cuts250 [] 0x18908c242240c062420e06062421890822420c8c06242189081a181a180e8e03a38068e032300e8e03a380c8e03a38050420e0c0e8e03a380e2e012108e2e02a280e8e03a380a8a02a280e8e03a380a8a014108c2422c0c050421410862420e06050423c3801a0a141085042049083230141085042088c0626038b80e2e018b80c2c038b80e2e030b804a0a38b80e2e028b80a2a038b80e2e040008c2422c0c0824220908703030908b030309083230 (by decide +kernel)

def state250_41 : List Sig := [0xcccccccccccccccc0000000000000000cccccccccccccccc,input 6,0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc,input 4,input 3,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_41 : Impossible true (goalAt 250) 6 state250_41.toFinset :=
  node_ok cuts250 [] 0x6242309089030189087030189086242140c068603a380e8e01a380c8c03a380e8e032380e8e01410838303a380e8e038b80484238b80a8a03a380e8e02a380504230908b03014108504218908381814108f0e01c0c0504214108623018980e2e038b8062e030b00e2e038b80c2e038a80e2e038b80480830908b0303090870300c8c0c24222828c2420686062420c8c062420c8c0e8e006860e8e00682850420c8c0504228a804a0a (by decide +kernel)

def state250_42 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 5,0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc,input 1,input 3,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_42 : Impossible true (goalAt 250) 6 state250_42.toFinset :=
  node_ok cuts250 [] 0x30908b0302090882421a180e8e03a38068e02a280e8e03a380a8e03a380f0e012908e8e032300e8e03a380c8c032300e8e03a380c8c030908a2303090832300c8c0623012828323012908e8e012908e8e038b801a180c8c032300686052420c8c050421410870603c380f0e01c380b0a03c380f0e02c38038183c380f0e034380d0c03c380f0e040004b030309089030309087030160605030140c0624214908c2422c0c052421c0c05242149081242 (by decide +kernel)

def state250_43 : List Sig := [0xffff000000000000ffff000000000000ffff000000000000ffff0000,input 5,0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc,input 1,input 3,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_43 : Impossible true (goalAt 250) 6 state250_43.toFinset :=
  node_ok cuts250 [] 0xc2422c0c082422090868603a380e8e01a380a8a03a380e8e02a380e8e03c3804a423a380c8c03a380e8e032380c242288c0c2420c8c03230188c04a0a0c8c04a423a3804a423a380e2e01890832301890870421c180f0e03c38070e02c280f0e03c380b0e03c300f0e03c380280818908c2422c0c062421c0c0624218908324214908c24226060524216060524214908703014908e8e004828e8e0068605242141085042343003818 (by decide +kernel)

def state250_44 : List Sig := [0xff00cc00ff00cc00ff00cc00ff00cc00ff00cc00ff00cc00ff00cc00ff00cc,input 3,input 1,input 4,input 5,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_44 : Impossible true (goalAt 250) 6 state250_44.toFinset :=
  node_ok cuts250 [] 0xc2422c0c08242209086242309089030189087030189086242140c0524230908b03014908703014908524212060524218908281814908c2422c0c0c2420c8c032301c0c0480a0c8c062420c8c062420686052420c8c0504214108eae03a3801a183a38068603a380e8e01a380a8a03a380e8e02a380c8c03a380e8e032380e8e03e3801a0a3a380c24226060c2422606070301606070301606062420e06062420e060f0e03c380524206828e2e038b803230068604a42 (by decide +kernel)

def state250_45 : List Sig := [0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc,input 1,input 4,input 3,input 5,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_45 : Impossible true (goalAt 250) 7 state250_45.toFinset :=
  node_ok cuts250 [⟨state250_8,exclude250_8⟩,⟨state250_36,exclude250_36⟩,⟨state250_37,exclude250_37⟩,⟨state250_38,exclude250_38⟩,⟨state250_39,exclude250_39⟩,⟨state250_40,exclude250_40⟩,⟨state250_41,exclude250_41⟩,⟨state250_42,exclude250_42⟩,⟨state250_43,exclude250_43⟩,⟨state250_44,exclude250_44⟩] 0xc2421c0c0c2422c0c1000f2c0c0c2424003c82422c0c0703020908b03018908624230909000f30908b0304003c90303090862421890870300e0607030160606242189087030189086242160603818140c098181a180686030908e8e03a38098183a380e8e03090868601a38058182a280a8a01c0c0e8e03a38058183a380e8e01c0c0a8a02a380381832300c8c018908e8e03a38038183a380e8e018908c8c0323801a0a3a380e8e0149083830149081a0a0e0c0383014908e8e03a38200093a380e8e0400004a421290a0000129084a4240000e8e03a380b03014908524230909000f30908b0304003cb030309085242149087030068287030128285242149087030149085242128281a0a0490838181490852421890a00081890838188001c381818908524214909000940024f0e030908323030908b0304003cb03030909000f30908b0300c8c032301282832300c8c070308001870301282a00051282870300c8c03230189081a181890838180c8c03230189083230189083818068601a1812908323012908e8e006860e8e0129081a1812908e8e00c8c0e8e01490900071490900090c8c032304002500071410900074001ce2e03090900033090888084003c880830909000f3090888084000c88081c0c100021c0c048088001048081c0c200031c0c048084000848081890900011890828088000828081890a0001189082808400042808 (by decide +kernel)

def state250_46 : List Sig := [0xff00ffcc00000000ff00ffcc00000000ff00ffcc00000000ff00ffcc,input 3,input 1,input 4,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_46 : Impossible true (goalAt 250) 5 state250_46.toFinset :=
  node_ok cuts250 [] 0x3090890302090882421c180f0e03c38070c02c280f0e03c380b0c018980e2e038b8062c028a80e2e038b80a2c038b80f0e00c8c0e2e038b80e8e012108e2e01a180e8e03a38068c02a280e8e03a380a8c03a380f0e00e0c0e8e018908903030908624208908624218908503018908f0e014908f0e030b80e2e018908e2e032380e8e012908e8e0 (by decide +kernel)

def state250_47 : List Sig := [0xff00ffccff00ffccff00ffccff00ffccff00ffccff00ffccff00ffccff00ffcc,input 3,input 1,input 4,input 5,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_47 : Impossible true (goalAt 250) 6 state250_47.toFinset :=
  node_ok cuts250 [⟨state250_46,exclude250_46⟩] 0xc2422c0c08242209086242309089030189087030189086242140c070603c380f0e01c380b0a03c380f0e02c380d0c03c380f0e034380c2422c0c0c2420c8c032301c0c0480a0c8c062420c8c0624206860f2e03c38032303c3804a4206860484212108e2e038b801a180c8c04a42309089818129085818129084a421c0c04a42189083818129084a423c3801a0a3c380e8e030908b03030908b0301606070301606070301890a000018909000106828f0e014908f0e0 (by decide +kernel)

def state250_48 : List Sig := [0xffffffff0000ccccffffffff0000ccccffffffff0000ccccffffffff0000cccc,input 5,input 1,input 4,input 3,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_48 : Impossible true (goalAt 250) 6 state250_48.toFinset :=
  node_ok cuts250 [] 0xc2422c0c082422090868603a380e8e01a380a8a03a380e8e02a380e8e03c38038303a380c8c03a380e8e032300c8c03a380e8e03230070603c380f0e01c380b0a03c380f0e02c380d0c03c380f0e034300d0c03c380f0e034300626038b80e2e018b80a2a038b80e2e028b80e2e03a3804a4238b80e2e03c380323038b80624238b80e2e030b80c2c038b80e2e006860624230908b0301890870301890862420890838183090898183090898181c0c058181c0c05818 (by decide +kernel)

def state250_49 : List Sig := [0xffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00,input 3,0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,input 1,input 5,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_49 : Impossible true (goalAt 250) 6 state250_49.toFinset :=
  node_ok cuts250 [] 0x30908b03020908824218908c242240c062421c0c0624218908503030908b0303090832300c8c07030128283230189083230189081a180c8c038300686032303cb80f0e00c8c0f0e030908b03030908b03006828703012828703018908281818908281838b80120a0e0c01a0a0e0c100003c38052423c38038303090888183090838301a0c048180e0c0281818908383018908e8e01c180f0e03c38070e02c280f0e03c380b0e034300f0e03c380d0e0 (by decide +kernel)

def state250_50 : List Sig := [0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000,input 3,0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,input 1,input 5,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_50 : Impossible true (goalAt 250) 6 state250_50.toFinset :=
  node_ok cuts250 [] 0xc2422c0c08242209086242309089030189087030189086242140c0c2422c0c0c2420c8c032301c0c04a0a0c8c062420c8c0624206860fae03a3804a423a380c2422c0c0c2422c0c01a0a1c0c04a0a1c0c062420a06062420a060e2e012908e8e012908e8e01490868603a380e8e01e380a8a03a380e8e02e380c8c03a380e8e03638070603c380f0e01c380b0a03c380f0e02c380d0c03c380f0e034380f0e03cb8032303c3803830 (by decide +kernel)

def state250_51 : List Sig := [0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,input 1,input 4,input 3,input 5,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_51 : Impossible true (goalAt 250) 7 state250_51.toFinset :=
  node_ok cuts250 [⟨state250_47,exclude250_47⟩,⟨state250_48,exclude250_48⟩,⟨state250_49,exclude250_49⟩,⟨state250_50,exclude250_50⟩] 0xc2421c0c0c2422c0c1000b2c0c0c2424002c82422c0c0703020908b03018908624230909000b30908b0304002c90303090862421890870300e0607030160606242189087030189086242160603818140c098181a180686030908e8e03a38098183a380e8e03090868601a38058182a280a8a01c0c0e8e03a38058183a380e8e01c0c0a8a02a380381832300c8c018908e8e03a38038183a380e8e018908c8c03238200033a380e8e03c38038303c38200020e0c038303c380e8e03a380b0301c180706030908f0e03c380b0303c380f0e03090870601c38070302c280b0a012828f0e03c38070303c380f0e012828b0a02c380381834300d0c018908f0e03c38038183c380f0e018908d0c034380c2420c8c0c2422c0c100092c0c0c2424002cc2422c0c032300c8c04a0a0c8c032301c0c100091c0c04a0a400344a0a1c0c032300c8c062420686062420e06032300c8c062420c8c062420e0601a18068604a420c8c04a423a3801a183a3804a42068604a423a38032303a38100094001cf2e04002432300c8c0f0e04001cf0e030909000330908b03040024b03030909000b30908b0304000cb03012829000212828703040024703012829000d1282870304000870301890900011890838184002438181890a000118908381840004381812909000012908e8e040024e8e01290a000012908e8e040000e8e040025000f1490900074001ce2e0 (by decide +kernel)

def state250_52 : List Sig := [0xff33ff00ff33ff000000000000000000ff33ff00ff33ff00,input 3,input 1,input 4,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_52 : Impossible true (goalAt 250) 5 state250_52.toFinset :=
  node_ok cuts250 [] 0x189088242240c062421c180f0e03c38070a034300f0e03c380d0e018980e2e038b8062a030b00e2e038b80c2e038b80f0e014108e2e038b80e8e012108e2e01a180e8e03a38068a032300e8e03a380c8e03a380f0e00e0c0e8e01c0c082422c0c08242140c062421c0c062422c380f0e01c0c0f0e01c0c0e2e00c8c0e2e02a380e8e00e0c0e8e0 (by decide +kernel)

def state250_53 : List Sig := [0xff33ff00ff33ff00ff33ff00ff33ff00ff33ff00ff33ff00ff33ff00ff33ff00,input 3,input 1,input 4,input 5,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_53 : Impossible true (goalAt 250) 6 state250_53.toFinset :=
  node_ok cuts250 [⟨state250_52,exclude250_52⟩] 0xc2422c0c08242209086242309089030189087030189086242140c0524230908b03014908703014908524212060524218908281814908626038b80e2e018b80a2a038b80e2e028b80c2c038b80e2e030b80e2e03cb80524238b80e2e00e0c01a1838b80e2e006860323038b8038303090890183090838301c0c050180e0c03818189083830189081a0a14908383014908e8e02c0c0c2422c0c0c2421c0c200001c0c100020e06062420e06062423c380f0e0068285242 (by decide +kernel)

def state250_54 : List Sig := [0xffffffffffffffff3333000033330000ffffffffffffffff3333000033330000,input 6,input 1,input 4,input 3,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_54 : Impossible true (goalAt 250) 6 state250_54.toFinset :=
  node_ok cuts250 [] 0x6242309089030189087030189086242140c02a0a1890862420a82868603a380e8e01a380c8c03a380e8e032380e8e03c38038303a380a8a03a380e8e02a280a8a03a380e8e02a28070603c380f0e01c380d0c03c380f0e03438070303c380f0e02c380b0a03c380f0e006828626038b80e2e018b80c2c038b80e2e030b80e2e03a380484238b80e2e03c380504238b80a2a038b80e2e028a80a2a038b80e2e028a80c2422c0c0c2421c0c04a0a309088a0a309088a0a (by decide +kernel)

def state250_55 : List Sig := [0x3333000033330000333300003333000033330000333300003333000033330000,input 1,input 4,input 3,input 5,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_55 : Impossible true (goalAt 250) 7 state250_55.toFinset :=
  node_ok cuts250 [⟨state250_19,exclude250_19⟩,⟨state250_24,exclude250_24⟩,⟨state250_53,exclude250_53⟩,⟨state250_54,exclude250_54⟩] 0xc2421c0c0c2422c0c1000e2c0c0c2424003882422c0c0703020908b03018908624230909000e30908b0304003890303090862421890870300e0607030160606242189087030189086242160603818140c098181a180686030908e8e03a38098183a380e8e03090868601a38058182a280a8a01c0c0e8e03a38058183a380e8e01c0c0a8a02a380381832300c8c018908e8e03a38038183a380e8e018908c8c0323801a0a3a380e8e0149083830149081a0a0e0c0383014908e8e03a380b03014908524230909000730908b03040038b030309085242149087030068287030128285242149087030149085242128281a0a04908381814908524218909000718908381840030381818908524214908c2421898062602c0c0e2e038b80c24238b80e2e02c0c0626018b804a0a28a80a2a01c0c0e2e038b804a0a38b80e2e01c0c0a2a028b80624230b00c2c00e060e2e038b80624238b80e2e00e060c2c030b804a4238b80e2e03a38200013a3804a428000048423a380e2e038b8100094001cf2e014909000714909000738b80e2e02c0c100032c0c0c2424001cc2422c0c1000e2c0c0c2424000cc2421c0c100021c0c04a0a4001c4a0a1c0c200031c0c04a0a400084a0a0e06100010e06062424001c62420e061000c0e06062424000462420e0c100000e0c0e8e04001ce8e00e0c200020e0c0e8e040000e8e04001d00073c38100074003c3230 (by decide +kernel)

def state250_56 : List Sig := [0xffff0000cccc0000ffff0000cccc0000ffff0000cccc0000ffff0000cccc,input 4,input 1,input 5,input 3,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_56 : Impossible true (goalAt 250) 6 state250_56.toFinset :=
  node_ok cuts250 [] 0xc2422c0c082422090868603a380e8e01a380a8a03a380e8e02a380c8c03a380e8e032300e8e03430038303a3806242309089030189087030189086242140c0626038b80e2e018b80a2a038b80e2e028b80e2e03a3804a4238b80624238b80e2e030b80e2e034300323038b80504034300d0c014300908034300d0c024300d0c03c300381834300c2422c0c0c2422c0c04a0a1c0c04a0a1c0c0e8e032300e8e03230062420e06062420e060e2e030b00e2e00c8c0f0e0 (by decide +kernel)

def state250_57 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 1,input 3,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_57 : Impossible true (goalAt 250) 6 state250_57.toFinset :=
  node_ok cuts250 [] 0x30908b0302090882421a180e8e03a38068e02a280e8e03a380a8e032300e8e03a380c8c03a380f0e00e0c0e8e032300e8e03a380c8c018980e2e038b8062e028a80e2e038b80a2e038b80e8e012908e2e030b00e2e03c380323038b80624238b80e2e030b80c24226060c242240c07030160605030140c062420e06062424001c70603c380f0e01c380b0a03c380f0e02c38038183c380f0e034380d0c018908c2422c0c062421c0c06242189082242 (by decide +kernel)

def state250_58 : List Sig := [0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 1,input 5,input 3,input 4,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_58 : Impossible true (goalAt 250) 7 state250_58.toFinset :=
  node_ok cuts250 [⟨state250_36,exclude250_36⟩,⟨state250_56,exclude250_56⟩,⟨state250_57,exclude250_57⟩] 0xc2421c0c0c2422c0c100062c0c0c2424004082422c0c0703020908b0301c180706030908f0e03c380b0303c380f0e03090870601c38070302c280b0a012828f0e03c38070303c380f0e012828b0a02c381000134300d0c018908f0e03c38200023c380f0e018908d0c034302000134300d0c04001cf0e03c38200003c380f0e04001cd0c03430098181a180686030908e8e03a38098183a380e8e03090868601a38058182a280a8a01c0c0e8e03a38058183a380e8e01c0c0a8a02a3801a0a3a380e8e03c38038303c3801a0a0e0c038303c380e8e03a3802a0a32300c8c018908e8e03a3802a0a3a380e8e018908c8c032301000432300c8c040000e8e03a38100043a380e8e040000c8c032300b03018908624230909000130908b03040040b0303090862421890870300a8287030160606242189087030189086242160602a0a08909000140024381830908626018980b03038b80e2e030908e2e038b80b0301898062e012828a2a028a80703038b80e2e012828e2e038b80703028a80a2e014908e2e038b80f0e00c8c0f0e014908323014908f0e038b80e2e012908e2e038b80e8e040010e8e012909000412908e8e038b80e2e018909000118909000938b80e2e040005000130b81000140004c2c03090900033090898184004098183090900103090898184000c98181c0c100021c0c058184001858181c0c100061c0c05818400085818 (by decide +kernel)

def state250_59 : List Sig := [0xffff0000ffffccccffff0000ffffccccffff0000ffffccccffff0000ffffcccc,input 4,input 1,input 5,input 3,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_59 : Impossible true (goalAt 250) 6 state250_59.toFinset :=
  node_ok cuts250 [] 0xc2422c0c082422090868603a380e8e01a380a8a03a380e8e02a380c8c03a380e8e032380e8e01490838303a380e8e0129084a423a380b030309089030309087030160605030140c0626038b80e2e018b80a2a038b80e2e028b80e2e03a3804a4238b80e2c038b80e2e006860e2e00c8c0504238b80e2e030b00323038b80524230908b0301490870301490852420490852421c908381814908f0e03090888083090888081c0c048081c0c048080e0602808189086242 (by decide +kernel)

def state250_60 : List Sig := [0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,input 1,input 5,input 3,input 4,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_60 : Impossible true (goalAt 250) 7 state250_60.toFinset :=
  node_ok cuts250 [⟨state250_59,exclude250_59⟩] 0xc2421c0c0c2422c0c100062c0c0c2424002c82422c0c0703020908b0301c180706030908f0e03c380b0303c380f0e03090870601c38070302c280b0a012828f0e03c38070303c380f0e012828b0a02c380381834300d0c00a020f0e03c38038183c380f0e00a020d0c03438098181a180686030908e8e03a38098183a380e8e03090868601a38058182a280a8a01c0c0e8e03a38058183a380e8e01c0c0a8a02a3801a0a3a380e8e03c38038303c3801a0a0e0c038303c380e8e03a380381832300c8c040010e8e03a38038183a380e8e040004c8c032380b0300e060b03030909000130908b0304002c90303090838183090870300e0607030160610001160607030400185030160603818140c0c2421898062602c0c0e2e038b80c24238b80e2e02c0c0626018b804a0a28a80a2a01c0c0e2e038b804a0a38b80e2e01c0c0a2a028b80524238b80e2e03c38032303c38052420c8c052423c380e2e038b804a4238b80e2e03a38100043a3804a42400104a423a380e2e038b81000140004e2c040024e2e038b80381840004381830909000330908b03040024b03030909000b30908b0304000cb03012829000212828703040024703012829000612828703040008703014909000714908f0e040024f0e01490a000014908f0e04001cf0e012909000012908e8e040010e8e012909000412908e8e040000e8e040025000118909000140004c2c0 (by decide +kernel)

def state250_61 : List Sig := [0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 4,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,input 1,input 3,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_61 : Impossible true (goalAt 250) 6 state250_61.toFinset :=
  node_ok cuts250 [] 0x18908c242240c062421c0c062421890850300a82862421890822421a180e8e03a38068e032300e8e03a380c8e02a280e8e03a380a8a03a380f0e00e0c0e8e02a280e8e03a380a8a018980e2e038b8062e030b00e2e038b80c2e038b80e8e012108e2e028a80e2e03c380504238b804a0a38b80e2e028b80c2422c0c0c2421c0c04a0a1c0c070304001c70603c380f0e01c380d0c03c380f0e03438070303c380f0e02c380b0a0309088a0a209088242 (by decide +kernel)

def state250_62 : List Sig := [0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,input 1,input 6,input 3,input 4,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_62 : Impossible true (goalAt 250) 7 state250_62.toFinset :=
  node_ok cuts250 [⟨state250_40,exclude250_40⟩,⟨state250_38,exclude250_38⟩,⟨state250_61,exclude250_61⟩] 0xb03018908624230909000630908b0304004490303090862421890900020e06038181282862421890900061890862421282838180890900060e06038184000462421890900061890862424000438180e060b0301c180706030908f0e03c380b0303c380f0e03090870601c380381834300d0c018908f0e03c38038183c380f0e018908d0c03438100022c280b0a012828f0e03c38200023c380f0e012828b0a02c281000d2c280b0a04001cf0e03c38200013c380f0e04001cb0a02c28098181a180686030908e8e03a38098183a380e8e03090868601a380381832300c8c018908e8e03a38038183a380e8e018908c8c0323801a0a3a380e8e03c38038303c3801a0a0e0c038303c380e8e03a3804a0a2a280a8a040014e8e03a3804a0a3a380e8e040008a8a02a28100052a280a8a040000e8e03a38100053a380e8e040000a8a02a280c24212828c2422c0c100022c0c0c2424004482422c0c04a0a20909000240024703030908626018980b03038b80e2e030908e2e038b80b0301898062e018908c2c030b00381838b80e2e018908e2e038b80381830b00c2e014908e2e038b80f0e040034f0e01490a000014108f0e038b80e2e012908e2e038b80e8e040014e8e012909000512108e8e038b80e2e012829000212829000938b80e2e040009000228b81000240008a2a030909000330908b03040034b03030909001130908b0304000cb030 (by decide +kernel)

def state250_63 : List Sig := [0xff00ff00ff00ff00ffccffccffccffccff00ff00ff00ff00ffccffccffccffcc,input 1,input 6,input 4,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_63 : Impossible true (goalAt 250) 6 state250_63.toFinset :=
  node_ok cuts250 [] 0x2c0c0624218908c2424002cc2422c0c1000b240c0c2421890862421c0c038181c0c058181890862421c0c062421890858180e06050302c0c070601c180c2423c380f0e02c0c0f0e03c380c2421c18070e00e060d0c03430062423c380f0e00e060f0e03c380624234300d0e01c0c0b0a02c2804a0a3c380f0e01c0c0f0e03c3804a0a2c280b0e030908703030908b03040014b03030909000b30908b0301c0c0703030908626018980b03038b80e2e030908e2e038b80b0301898062e018908c2c030b00381838b80e2e018908e2e038b80381830b00c2e014908e2e038b80f0e006860f0e0149081a1814108f0e038b80e2e0128281a1838a80703038b80e2e012828e2e038b80703006860703012908e2e038b80e8e006860e8e0129081a1812108e8e038b80e2e02606068601a180c2423a380e8e026060e8e03a380c2421a18068e00e060c8c03230062423a380e8e00e060e8e03a380624232300c8e004828e8e03a380f0e00e0c0f0e00482838300e0c0f0e03a380e8e016060a8a02a28070303a380e8e016060e8e03a38070302a280a8e0 (by decide +kernel)

def state250_64 : List Sig := [0xffff0000ffff0000ffffccccffffccccffff0000ffff0000ffffccccffffcccc,input 4,input 1,input 6,input 3,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_64 : Impossible true (goalAt 250) 6 state250_64.toFinset :=
  node_ok cuts250 [] 0x6242309089030189087030189086242140c068603a380e8e01a380c8c03a380e8e032380a8a03a380e8e02a380e8e00e0c038303a380e8e00e0c038303a380c2422c0c0c2421c0c0626038b80e2e018b80c2c038b80e2e030b80e2e03a380484238b80e2a038b80e2e00c8c0e2e00c8c0323038b80e2e028a80323038b80b03030908b03030908381818908381818908703016828703006828f0e02c0c0c2422c0c0c2420e06062420e06062421c0c048081c0c04a0a (by decide +kernel)

def state250_65 : List Sig := [0xcccccccccccccccc0000000000000000cccccccccccccccc,input 1,input 6,input 3,input 4,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_65 : Impossible true (goalAt 250) 7 state250_65.toFinset :=
  node_ok cuts250 [⟨state250_41,exclude250_41⟩,⟨state250_63,exclude250_63⟩,⟨state250_64,exclude250_64⟩] 0xb03018908624230909000630908b0304002c90303090862421890870300e0607030160606242189087030189086242160603818140c0b0301c180706030908f0e03c380b0303c380f0e03090870601c380381834300d0c018908f0e03c38038183c380f0e018908d0c03438070302c280b0a012020f0e03c38070303c380f0e012020b0a02c38098181a180686030908e8e03a38098183a380e8e03090868601a380381832300c8c018908e8e03a38038183a380e8e018908c8c0323801a0a3a380e8e03c38038303c3801a0a0e0c038303c380e8e03a38058182a280a8a01c0c0e8e03a38058183a380e8e01c0c0a8a02a380c2421c0c0c2422c0c100022c0c0c2424002cc2422c0c070301c0c0c2421898062602c0c0e2e038b80c24238b80e2e02c0c0626018b80624230b00c2c00e060e2e038b80624238b80e2e00e060c2c030b80524238b80e2e03c38100093c38052428000050423c380e2e038b804a4238b80e2e03a38100093a3804a424001448423a380e2e038b81000240008e2a040024e2e038b80703040008703022829000322828c24240024c24222829000b22828c2424000cc2420a82900010a82862424002462420a82900060a828624240004624206829000706828f0e040024f0e00682a000206828f0e04001cf0e040025000040000e8e040024e8e040025000580004e8e040000e8e040025000212829000240008a2a0 (by decide +kernel)

def state250_66 : List Sig := [0xffffffffffffffffffffffffffffffff0000000000000000ffffff00ffffff00,input 7,input 3,input 4,input 1,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_66 : Impossible true (goalAt 250) 5 state250_66.toFinset :=
  node_ok cuts250 [] 0x6242260609030189086242140c0703018908c2c038b80e2e030b80e2e03c380504238b80e2e03a380484238b80626038b80e2e018980626038b80e2e018980d0c03c380f0e03438070603c380f0e01c18070603c380f0e01c180c8c03a380e8e032380e8e03c38038303a38068603a380e8e01a18068603a380e8e01a1808242 (by decide +kernel)

def state250_67 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,0xffffff00ffffff00,input 3,input 4,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_67 : Impossible true (goalAt 250) 4 state250_67.toFinset :=
  node_ok cuts250 [] 0x38b80f0e014108e2e038b80e8e012108e2e018908e2e038b801a1814908f0e03c38050603a380f0e00e0c0e8e012908e8e03a38048600c8c0e2e00c8c0e2e012060f0e01c0c0f0e00e0c0e8e00e0c0e8e0140c062421c0c06242 (by decide +kernel)

def state250_68 : List Sig := [0xffffff00ffffff00,input 7,input 3,input 4,input 1,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_68 : Impossible true (goalAt 250) 5 state250_68.toFinset :=
  node_ok cuts250 [⟨state250_67,exclude250_67⟩] 0x62422090a000018908c2c038b80e2e030b80e2e03c380504238b80e2e03a380484238b80626038b80e2e018a80d0c03c380f0e03438070603c380f0e01c280c8c03a380e8e032380e8e03c38038303a38068603a380e8e01a280503018908703018908323038b80323038b8048183c38070303c38038303a38038303a380b030 (by decide +kernel)

def state250_69 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 7,0xffffff00ffffff000000000000000000ffffff00ffffff00,input 3,input 4,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_69 : Impossible true (goalAt 250) 5 state250_69.toFinset :=
  node_ok cuts250 [⟨state250_67,exclude250_67⟩] 0xe2e03c380504238b80e2e03a380484238b80626038b80e2e018a00624238b80e2e00686070603c380f0e01c20052423c380f0e014180e8e03c38038303a38068603a380e8e01a2004a423a380e8e012180323038b80323038b80b0c03c38070303c380a8c03a38038303a38070308000090301c0c05030189087030189088242 (by decide +kernel)

def state250_70 : List Sig := [0xffffff00ffffff000000000000000000ffffff00ffffff00,input 3,input 4,input 1,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_70 : Impossible true (goalAt 250) 6 state250_70.toFinset :=
  node_ok cuts250 [⟨state250_66,exclude250_66⟩,⟨state250_68,exclude250_68⟩,⟨state250_69,exclude250_69⟩] 0x2c0c062421890882424002882422c0c20002240c0824218908624220908626018980b03038b80e2e020908e2e038b80b0301898062a018908c2c030b00381838b80e2e018908e2e038b80381830b00c2e014908e2e038b80f0e00c8c0f0e014908323014108f0e038b80e2e012908e2e038b80e8e006860e8e0129081a1812108e8e038b80e2e02c0c070601c18082423c380f0e02c0c0f0e03c38082421c18070a00e060d0c03430062423c380f0e00e060f0e03c380624234300d0e02606068601a18082423a380e8e026060e8e03a38082421a18068a00e060c8c03230062423a380e8e00e060e8e03a380624232300c8e006828e8e03a380f0e00e0c0f0e00682838300e0c0f0e03a380e8e02c0c070301c0c082428000482422c0c200002c0c082421c0c082420e0605818140c062421c0c062420e06070301c0c062421606062420c8c070300c8c0e2e012828e2e00c8c04a0a0c8c0e2e01c0c0e2e0068284a0a2c380f0e01c0c0f0e00682870301c0c0f0e012828f0e00e0c070302a380e8e016060e8e00e0c058180e0c0e8e01c0c0e8e0 (by decide +kernel)

def state250_71 : List Sig := [0xffffff00ffffff000000000000000000ffffff00ffffff00,0xffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00,input 3,input 4,input 1,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_71 : Impossible true (goalAt 250) 6 state250_71.toFinset :=
  node_ok cuts250 [] 0x189088242240c0624218980e2e038b8062a030b00e2e038b80c2e038b8032300c8c0e2e038b80383006860e2e038b8032300c8c0e2e02c0c082422c0c082420e06062420a06062423c3803830209089018209083818189083830189081a0a0e0c028303a380b03020908b03020908381818908381818908703020908b03020908503018908703018908323038b80323038b8048181c0c070301282838301406038301c0c10002 (by decide +kernel)

def state250_72 : List Sig := [0x3333330033333300333333003333330033333300333333003333330033333300,input 1,input 3,input 4,input 5,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_72 : Impossible true (goalAt 250) 6 state250_72.toFinset :=
  node_ok cuts250 [] 0xc2422c0c08242209086242309089030189087030189086242140c0524230908b030149087030149085242120605242189082818149084a42309089018129083830129084a420e0c04a42189083830129084a4214908383012908626038b80e2e018b80a2a038b80e2e028b80c2c038b80e2e030b80e2e03cb80524238b80e2e03ab804a4238b80b03030908b03030908703012828703012828381818908381818908f0e03c381000014908e8e03a3803830129083230 (by decide +kernel)

def state250_73 : List Sig := [0xffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00,input 3,input 4,input 1,input 5,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_73 : Impossible true (goalAt 250) 7 state250_73.toFinset :=
  node_ok cuts250 [⟨state250_8,exclude250_8⟩,⟨state250_20,exclude250_20⟩,⟨state250_34,exclude250_34⟩,⟨state250_49,exclude250_49⟩,⟨state250_70,exclude250_70⟩,⟨state250_71,exclude250_71⟩,⟨state250_72,exclude250_72⟩] 0xc2421c0c0c2422c0c100052c0c0c2424004882422c0c0703020908b03018908624230909000430908b0304004890303090862421890870300e0607030160606242189087030189086242160603818140c0c2421898062602c0c0e2e038b80c24238b80e2e02c0c0626018b804a0a28a80a2a01c0c0e2e038b804a0a38b80e2e01c0c0a2a028b80624230b00c2c00e060e2e038b80624238b80e2e00e060c2c030b801a0a38b80e2e08000c32300c8c01a0a0c8c0323080008e2e038b81000038b80e2e00e0c01a180e0c20001068601a180e0c0e2e038b82000638b80e2e04002432300c8c200000c8c0323040024e2e038b80b03006828b03030909001230908b03040048b030309081a0a309087030068287030128290005128287030400147030128281a0a120603818068283818189090004189083818400102818189081a0a18909000040000f0e02606038300e0c0c24240000c24226061001224060c2420e0c0c2421606038300e0c070304000070301606100051406070300e0c038300e06100040e06062420e0c062420e06038300e0c062424000062420682900070682900000e0c038304000100000a0c100004001ce8e02c0c100032c0c0c24240048c2422c0c100122c0c0c2424000cc2421c0c100021c0c200054001600041c0c100051c0c100054000900020e06100010e06062424001062420e06100040e0606242400046242 (by decide +kernel)

def state250_74 : List Sig := [0xffffffff00ff0000ffffffff00ff0000ffffffff00ff0000ffffffff00ff0000,input 3,input 4,input 1,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_74 : Impossible true (goalAt 250) 6 state250_74.toFinset :=
  node_ok cuts250 [] 0x30908503030908903040038903030909000e209089030140c0824230908626018980903038b80e2e030908e2e038b8090301898062e012828a2a028a80503038b80e2e012828e2e038b80503028a80a2e006828e2e038b80f0e00c8c0f0e00682832300c8c0f0e038b80e2e012908e2e038b80e8e006860e8e0129081a1812108e8e038b80e2e018908c2c030b00381838b80e2e018908e2e038b80381830b00c2e0240c070601c180c2423c380f0e0240c0f0e03c380c2421c18070e0140c0b0a02c2804a0a3c380f0e0140c0f0e03c3804a0a2c280b0e00e0601a0a3430062423c380f0e00e060f0e03c38062420682862422606068601a180c2423a380e8e026060e8e03a380c2421a18068e016060a8a02a28050303a380e8e016060e8e03a38050302a280a8e006828e8e03a380f0e00e0c0f0e00682838300e0c0f0e03a380e8e00e060c8c03230062423a380e8e00e060e8e03a380624232300c8e0240c0624218908c24240038c242240c1000e240c0c242189086242140c03818140c05818189086242140c062421890858180e0602242 (by decide +kernel)

def state250_75 : List Sig := [0xccffccccccffccccccffccccccffccccccffccccccffccccccffccccccffcccc,input 1,input 3,input 4,input 5,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_75 : Impossible true (goalAt 250) 6 state250_75.toFinset :=
  node_ok cuts250 [] 0xc2422c0c08242209086242309089030189087030189086242140c0524230908b0301490870301490852421206052421890828181490868603a380e8e01a380a8a03a380e8e02a380c8c03a380e8e032380e8e03e380120a3a380c2422c0c0c2420c8c032301c0c04a0a0c8c062420c8c062420e06052420c8c05042141084a423a3804a423a380e2e03090898183090898181c0c058181c0c058181890838181890838183c380f0e014909000012908e8e012908e8e0 (by decide +kernel)

def state250_76 : List Sig := [0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000,input 3,input 4,input 1,input 5,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_76 : Impossible true (goalAt 250) 7 state250_76.toFinset :=
  node_ok cuts250 [⟨state250_50,exclude250_50⟩,⟨state250_74,exclude250_74⟩,⟨state250_75,exclude250_75⟩] 0xc2421c0c0c2422c0c100052c0c0c2424003882422c0c0703020908b03018908624230909000430908b0304003890303090862421890870300e0607030160606242189087030189086242160603818140c0c2421898062602c0c0e2e038b80c24238b80e2e02c0c0626018b804a0a28a80a2a01c0c0e2e038b804a0a38b80e2e01c0c0a2a028b80624230b00c2c00e060e2e038b80624238b80e2e00e060c2c030b801a0a38b80e2e08000032300c8c01a0a0c8c032304001ce2e038b804a4238b80e2e03a3801a183a3804a420686048423a380e2e038b80b03006828b03030909000730908b03040038b030309081a0a309087030068287030128290007128287030400147030128281a0a120603818068283818189090007189083818400102818189081a0a1890898181a180686030908e8e03a38098183a380e8e03090868601a38058182a280a8a01c0c0e8e03a38058183a380e8e01c0c0a8a02a380381832300c8c018908e8e03a38038183a380e8e018908c8c032381000040000f8e00682900070682900003a380e8e02c0c100032c0c0c2424001cc2422c0c1000e2c0c0c2424000cc2421c0c100021c0c058184001c58181c0c100051c0c058184000858184001d00014000462424001c62424001d00048000462424000462420c8c100090c8c0e2e04001ce2e00c8c200020c8c0e2e04001ce2e04000100003c3810007400003830 (by decide +kernel)

def state250_77 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,input 5,input 1,input 3,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_77 : Impossible true (goalAt 250) 7 state250_77.toFinset :=
  node_ok cuts250 [⟨state250_36,exclude250_36⟩,⟨state250_42,exclude250_42⟩,⟨state250_57,exclude250_57⟩] 0xc2421c0c0c2422c0c100062c0c0c2424004c82422c0c070302090898181a180686030908e8e03a38098183a380e8e03090868601a38058182a280a8a01c0c0e8e03a38058183a380e8e01c0c0a8a02a380381832300c8c040010e8e03a38038183a380e8e040004c8c03230100043a380e8e03c38038303c38100040e0c038303c380e8e03a381000432300c8c040000e8e03a38100043a380e8e040000c8c032300c2421898062602c0c0e2e038b80c24238b80e2e02c0c0626018b804a0a28a80a2a01c0c0e2e038b804a0a38b80e2e01c0c0a2a028b804a4238b80e2e03a3801a183a3804a420686048423a380e2e038b81000130b00c2c00e060e2e038b82000238b80e2e00e060c2c030b01000c38b80e2e03c38032303c38200010c8c032303c380e2e038b81000c30b00c2c040024e2e038b82000038b80e2e040024c2c030b00b0300e060b03030909000130908b0304004c90303090838183090870300e0607030160610001160607030400185030160603818140c100014001c62422c0c070601c180c2423c380f0e02c0c0f0e03c380c2421c18070e01c0c0b0a02c2804a0a3c380f0e01c0c0f0e03c3804a0a2c280b0e00e06100010e06100073c380f0e040005000134381000140004d0c02c0c100032c0c0c24240030c2422c0c100132c0c0c2424000cc2421c0c100021c0c04a0a400184a0a1c0c100061c0c04a0a400084a0a (by decide +kernel)

def state250_78 : List Sig := [0xff00ff00ffffff00ff00ff00ffffff00ff00ff00ffffff00ff00ff00ffffff00,input 4,input 5,input 1,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_78 : Impossible true (goalAt 250) 6 state250_78.toFinset :=
  node_ok cuts250 [] 0x30908703030908b03040038b03030909000e20908b0301c0c0824230908626018980b03038b80e2e030908e2e038b80b0301898062e012828a2a028a80703038b80e2e012828e2e038b80703028a80a2e018908c2c030b00381838b80e2e018908e2e038b80381830b00c2e004828e2e038b80f0e00c8c0f0e00482832300c8c0f0e038b80e2e012908e2e038b80e8e006860e8e0129081a1812108e8e038b80e2e02c0c0624218908c24240010c2422c0c1000e2c0c0c2421890862421c0c038181c0c050181890862421c0c062421890850180e06022422c0c070601c180c2423c380f0e02c0c0f0e03c380c2421c18070e01c0c0b0a02c2804a0a3c380f0e01c0c0f0e03c3804a0a2c280b0e00e060120a3c30062423c380f0e00e060f0e03c38062420482862422406068601a180c2423a380e8e024060e8e03a380c2421a18068e014060a8a02a28070303a380e8e014060e8e03a38070302a280a8e00e060c8c03230062423a380e8e00e060e8e03a380624232300c8e004828e8e03a380f0e00e0c0f0e00482838300e0c0f0e03a380e8e0 (by decide +kernel)

def state250_79 : List Sig := [0xccccccccffffccccccccccccffffccccccccccccffffccccccccccccffffcccc,input 1,input 4,input 5,input 3,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_79 : Impossible true (goalAt 250) 6 state250_79.toFinset :=
  node_ok cuts250 [] 0xc2422c0c082422090868603a380e8e01a380a8a03a380e8e02a380c8c03a380e8e032380e8e03c38038303a380624230908b0301890870301890862420890870603c380f0e01c380b0a03c380f0e02c380f0c03c380f0e014908c2422c0c0c2422c0c01a181c0c04a0a1c0c04a423a3804a423a38062420e86062420686052423c38050423c380e2e030908b03030908b03016060703016060703012908e8e012908e8e018908280818908381834300f0e014908f0e0 (by decide +kernel)

def state250_80 : List Sig := [0xffff000000000000ffff000000000000ffff000000000000ffff0000,input 4,input 5,input 1,input 3,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_80 : Impossible true (goalAt 250) 7 state250_80.toFinset :=
  node_ok cuts250 [⟨state250_43,exclude250_43⟩,⟨state250_78,exclude250_78⟩,⟨state250_79,exclude250_79⟩] 0xc2421c0c0c2422c0c100062c0c0c2424003882422c0c070302090898181a180686030908e8e03a38098183a380e8e03090868601a38058182a280a8a01c0c0e8e03a38058183a380e8e01c0c0a8a02a3802a0a32300c8c018908e8e03a3802a0a3a380e8e018908c8c03238100073a380e8e03c38038303c38100040e0c038303c380e8e03a380c2421898062602c0c0e2e038b80c24238b80e2e02c0c0626018b804a0a28a80a2a01c0c0e2e038b804a0a38b80e2e01c0c0a2a028b804a4238b80e2e03a3801a183a3804a420686048423a380e2e038b80624230b00c2c00a020e2e038b80624238b80e2e00a020c2c030b81000738b80e2e03c38032303c38200000c8c032303c380e2e038b80b03018908624230909000130908b03040038b0303090862421890870300a8287030160606242189087030189086242160602a0a08908b0301c180706030908f0e03c380b0303c380f0e03090870601c38070302c280b0a012828f0e03c38070303c380f0e012828b0a02c381000140004f0c04001cf0e03c380624240004624226061000326060c2424001cc24226061000e26060c2424000cc2421606100021606070304001c70301606100061606070304000870304001d000040000e8e04001ce8e04001d000480004e8e040000e8e006861000906860e2e04001ce2e006862000206860e2e04001ce2e04001d00010e061000140004d0c0 (by decide +kernel)

def state250_81 : List Sig := [0x3333333333333333333300003333000033333333333333333333000033330000,input 1,input 4,input 6,input 3,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_81 : Impossible true (goalAt 250) 6 state250_81.toFinset :=
  node_ok cuts250 [] 0x6242309089030189087030189086242140c068603a380e8e01a380c8c03a380e8e032380a8a03a380e8e02a280e8e03c38038303a380c2422c0c082422090870603c380f0e01c380d0c03c380f0e03438070303c380f0e02c380c24228a80a2a02c0c0828028a80a2a020a80a2a03a3804a423a380a2a038a804a0a28a80a2a03c38052423c380b03030908b03030908381818908381818908e8e02a280e8e02a280703012828703012828f0e02c280f0e014908e2e0 (by decide +kernel)

def state250_82 : List Sig := [0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 4,input 6,input 1,input 3,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_82 : Impossible true (goalAt 250) 7 state250_82.toFinset :=
  node_ok cuts250 [⟨state250_38,exclude250_38⟩,⟨state250_61,exclude250_61⟩,⟨state250_81,exclude250_81⟩] 0xb03018908624230909000630908b0304005090303090862421890870300e0607030160606242189087030189086242160603818140c100060a8282a0a400046242189090006189086242400042a0a0a82898181a180686030908e8e03a38098183a380e8e03090868601a380381832300c8c018908e8e03a38038183a380e8e018908c8c03238058182a280a8a01c0c0e8e03a38058183a380e8e01c0c0a8a02a28100053a380e8e03c38038303c38100050e0c038303c380e8e03a38100052a280a8a040000e8e03a38100053a380e8e040000a8a02a280c2421898062602c0c0e2e038b80c24238b80e2e02c0c0626018b80624230b00c2c00e060e2e038b80624238b80e2e00e060c2c030b804a4238b80e2e03a3801a183a3804a420686048423a380e2e038b81000228a80a2a01c0c0e2e038b82000138b80e2e01c0c0a2a028a80524238b80e2e03c38032303c38052420c8c050423c380e2e038b82000228a80a2a040024e2e038b82000038b80e2e040024a2a028a80c2421c0c0c2422c0c100022c0c0c24240050c2422c0c070301c0c100024001c4a0a2c0c070601c180c2423c380f0e02c0c0f0e03c380c2421c18070e00e060d0c03430062423c380f0e00e060f0e03c380624234300d0e01c0c100021c0c100073c380f0e04000900022c381000240008b0a0309090003309088a0a400508a0a309090014309088a0a4000c8a0a (by decide +kernel)

def state250_83 : List Sig := [0xccccccccccccccccffffccccffffccccccccccccccccccccffffccccffffcccc,input 1,input 4,input 6,input 3,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_83 : Impossible true (goalAt 250) 6 state250_83.toFinset :=
  node_ok cuts250 [] 0x62423090890301890838181890862420890868603a380e8e01a380c8c03a380e8e032380a8a03a380e8e02a380e8e03c38038303a380c2422c0c082422090870603c380f0e01c380d0c03c380f0e034380f0a03c380f0e004908c2422c0c0c2420c8c062420c8c06242068604a423a3804a423a38032301c8c04a0a0c8c052423c38052423c380e2e030908880830908880818908280818908280812908e8e012908e8e01282848081c0c070302c280f0e014908f0e0 (by decide +kernel)

def state250_84 : List Sig := [0xffff0000ffff00000000000000000000ffff0000ffff0000,input 4,input 6,input 1,input 3,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_84 : Impossible true (goalAt 250) 7 state250_84.toFinset :=
  node_ok cuts250 [⟨state250_83,exclude250_83⟩] 0xb03018908624230909000630908b0304003890303090862421890900020e06038181282862421890900061890862421282838180890898181a180686030908e8e03a38098183a380e8e03090868601a380381832300c8c018908e8e03a38038183a380e8e018908c8c0323804a0a2a280a8a040014e8e03a3804a0a3a380e8e040008a8a02a38100073a380e8e03c38038303c38100050e0c038303c380e8e03a380c2421898062602c0c0e2e038b80c24238b80e2e02c0c0626018b80624230b00c2c00e060e2e038b80624238b80e2e00e060c2c030b804a4238b80e2e03a3801a183a3804a420686048423a380e2e038b804a0a28a80a2a012020e2e038b804a0a38b80e2e012020a2a028b80524238b80e2e03c38032303c38052420c8c050423c380e2e038b80c24212828c2422c0c100022c0c0c2424003882422c0c04a0a20908b0301c180706030908f0e03c380b0303c380f0e03090870601c380381834300d0c018908f0e03c38038183c380f0e018908d0c034381000240008f0a04001cf0e03c3804a0a400084a0a2c0c100032c0c0c2424001cc2422c0c1000e2c0c0c2424000cc2420e06100010e06062424001c62420e06100060e06062424000462420e0c100000e0c0e8e04001ce8e00e0c100050e0c0e8e040000e8e00c8c100090c8c0e2e04001ce2e00c8c200000c8c0e2e04001ce2e04001d00021c0c1000240008b0a0 (by decide +kernel)

def state250_85 : List Sig := roots 250
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_85 : Impossible true (goalAt 250) 8 state250_85.toFinset :=
  node_ok cuts250 [⟨state250_21,exclude250_21⟩,⟨state250_25,exclude250_25⟩,⟨state250_35,exclude250_35⟩,⟨state250_45,exclude250_45⟩,⟨state250_51,exclude250_51⟩,⟨state250_55,exclude250_55⟩,⟨state250_58,exclude250_58⟩,⟨state250_60,exclude250_60⟩,⟨state250_62,exclude250_62⟩,⟨state250_65,exclude250_65⟩,⟨state250_73,exclude250_73⟩,⟨state250_76,exclude250_76⟩,⟨state250_77,exclude250_77⟩,⟨state250_80,exclude250_80⟩,⟨state250_82,exclude250_82⟩,⟨state250_84,exclude250_84⟩] 0x4000cc2421c0c0c2424000cb0304000cb0304000cc2424000c82424000cb0301c0c082424000cb0301890862424000cc2424000cc2424000cb0304000c90304000cc2421890862424000870300e06070304000458181890862424001870301890862424000458180e06050304000cb0301c18070604000cc2423c380f0e04000cb0303c380f0e04000cc2421c18070e04000870302c280b0a08003c4a0a3c380f0e08003870303c380f0e0400084a0a2c280b0e040004381834300d0c08003462423c380f0e08003038183c380f0e040004624234300d0e04000c98181a18068604000cc2423a380e8e04000c98183a380e8e04000cc2421a18068e04000858182a280a8a04000070303a380e8e04001458183a380e8e04000070302a280a8e040004381832300c8c04000062423a380e8e04001038183a380e8e040000624232300c8e08002c1a0a3a380e8e040000f0e00e0c0f0e0800281a0a0e0c0383040000f0e03a380e8e04000cc2421898062604000cb03038b80e2e04000cc24238b80e2e04000cb0301898062e0400084a0a28a80a2a080024703038b80e2e0800204a0a38b80e2e040008703028a80a2e040004624230b00c2c08001c381838b80e2e080018624238b80e2e040004381830b00c2e080014524238b80e2e080010f0e00c8c0f0e08000c52420c8c0504280008f0e038b80e2e0400004a4238b80e2e080004e8e006860e8e0800004a4206860484240000e8e038b80e2e0 (by decide +kernel)

theorem lower250 : Claim 250 9 :=
  fromSearch 319901760 (by decide +kernel) exclude250_85

def cuts145 : Cuts (goalAt 145) := []

def state145_0 : List Sig := roots 145
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude145_0 : Impossible true (goalAt 145) 3 state145_0.toFinset :=
  node_ok cuts145 [] 0x240401101240408101242009080240409080242008101044041101204041110044409010206008180204048180206009010044401110044048180206009080044409080044041110044409080206008180 (by decide +kernel)

theorem lower145 : Claim 145 4 :=
  fromSearch 4 (by decide +kernel) exclude145_0

theorem lower177 : Claim 177 5 :=
  fromLift 5 32 4 lower145 (by decide +kernel)

def cuts137 : Cuts (goalAt 137) := []

def state137_0 : List Sig := roots 137
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude137_0 : Impossible true (goalAt 137) 3 state137_0.toFinset :=
  node_ok cuts137 [] 0x220200901220208101222008880220208880222008101024040901204040908024208808206008180204048180206008808024200908024048180206008880024208880024040908024208880206008180 (by decide +kernel)

theorem lower137 : Claim 137 4 :=
  fromSearch 3 (by decide +kernel) exclude137_0

theorem lower169 : Claim 169 5 :=
  fromLift 5 32 3 lower137 (by decide +kernel)

theorem lower153 : Claim 153 5 :=
  fromLift 5 8 3 lower145 (by decide +kernel)

def cuts41 : Cuts (goalAt 41) := []

def state41_0 : List Sig := roots 41
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude41_0 : Impossible true (goalAt 41) 3 state41_0.toFinset :=
  node_ok cuts41 [] 0xa02009010a02021010a08028200a02028200a0802101024040901084040908024202808084802120084042120084802808024200908024042120084802820024202820024040908024202820084802120 (by decide +kernel)

theorem lower41 : Claim 41 4 :=
  fromSearch 3 (by decide +kernel) exclude41_0

theorem lower57 : Claim 57 5 :=
  fromLift 5 16 3 lower41 (by decide +kernel)

def rule185_0 : {c : Cut // CutGood (goalAt 185) c} :=
  ruleFor 185 lower177 none (by decide +kernel)

def rule185_1 : {c : Cut // CutGood (goalAt 185) c} :=
  ruleFor 185 lower169 none (by decide +kernel)

def rule185_2 : {c : Cut // CutGood (goalAt 185) c} :=
  ruleFor 185 lower153 none (by decide +kernel)

def rule185_3 : {c : Cut // CutGood (goalAt 185) c} :=
  ruleFor 185 lower57 none (by decide +kernel)

def cuts185 : Cuts (goalAt 185) := [rule185_0,rule185_1,rule185_2,rule185_3]

def state185_0 : List Sig := roots 185
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude185_0 : Impossible true (goalAt 185) 6 state185_0.toFinset :=
  node_ok cuts185 [] 0x40008b0300e060b03040008981840008981840008b0304000c90304000898180e060903040004b03004404b0304000488082c280b0a040004b0302c280b0a04000488080440488184000438182420090804000428082c280b0a04000438182c280b0a04000428082420090a04000098180e0c0383040000b0302a280a8a04000098182a280a8a040000b0300e0c038304000038182220088804000021012a280a8a04000038182a280a8a04000021012220088a04000100002a280a8a040000b0a00e0c0b0a04000100000e0c0383040000b0a02a280a8a04000c81010c4c031304000cb03028680a1a04000c810128680a1a04000cb0300c4c0313040008210120600818040008381828680a1a040008210128680a1a04000838182060081a040004110128680a1a040004b0a00c4c0b0a04000411010c4c0313040004b0a028680a1a040000090128680a1a040000a8a006460a8a040000090106460191840000a8a028680a1a0 (by decide +kernel)

theorem lower185 : Claim 185 7 :=
  fromSearch 3 (by decide +kernel) exclude185_0

theorem lower179 : Claim 179 6 :=
  fromLift 6 1 68 lower178 (by decide +kernel)

theorem lower171 : Claim 171 6 :=
  fromLift 6 2 83 lower169 (by decide +kernel)

theorem lower147 : Claim 147 5 :=
  fromLift 5 1 68 lower146 (by decide +kernel)

theorem lower139 : Claim 139 5 :=
  fromLift 5 2 115 lower137 (by decide +kernel)

def rule155_0 : {c : Cut // CutGood (goalAt 155) c} :=
  ruleFor 155 lower153 none (by decide +kernel)

def rule155_1 : {c : Cut // CutGood (goalAt 155) c} :=
  ruleFor 155 lower154 none (by decide +kernel)

def rule155_2 : {c : Cut // CutGood (goalAt 155) c} :=
  ruleFor 155 lower147 none (by decide +kernel)

def rule155_3 : {c : Cut // CutGood (goalAt 155) c} :=
  ruleFor 155 lower139 none (by decide +kernel)

def cuts155 : Cuts (goalAt 155) := [rule155_0,rule155_1,rule155_2,rule155_3]

def state155_0 : List Sig := roots 155
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude155_0 : Impossible true (goalAt 155) 6 state155_0.toFinset :=
  node_ok cuts155 [] 0x4000c98180682898184000c8a0a2420090804000c98182420090804000c8a0a06828881840008981802c0c981840008901022200888040008981822200888040008901002c0c9018400081a0a222008880400089080400089080400081a0a4000c120a400089080222008880400008a0a068601a1840000981820a008280400008a0a20a008280400009818068601a18400001a0a20a008280400009080068609080400001a0a068601a1840000908020a008280400000b0320a008280400008880068608880400000b03068601a1840000888020a008280400048303064601918400049818206008180400048303206008180400049818064601918400041303206008180400049080064609080400041303064601918400049080206008180400080b03206008180400088880064608880400080b0306460191840008888020600818040001000020600818040000828002c28828040001000102c280b0a400008280206008180 (by decide +kernel)

theorem lower155 : Claim 155 7 :=
  fromSearch 67 (by decide +kernel) exclude155_0

theorem lower59 : Claim 59 6 :=
  fromLift 6 2 67 lower57 (by decide +kernel)

theorem lower43 : Claim 43 5 :=
  fromLift 5 2 83 lower41 (by decide +kernel)

def cuts27 : Cuts (goalAt 27) := []

def state27_0 : List Sig := roots 27
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude27_0 : Impossible true (goalAt 27) 3 state27_0.toFinset :=
  node_ok cuts27 [] 0x6828130304828120a068281a18068601103048401a1806860121802c281918064600b0a044401918064601118064601a1802c281918 (by decide +kernel)

theorem lower27 : Claim 27 4 :=
  fromSearch 67 (by decide +kernel) exclude27_0

def rule187_0 : {c : Cut // CutGood (goalAt 187) c} :=
  ruleFor 187 lower185 none (by decide +kernel)

def rule187_1 : {c : Cut // CutGood (goalAt 187) c} :=
  ruleFor 187 lower179 none (by decide +kernel)

def rule187_2 : {c : Cut // CutGood (goalAt 187) c} :=
  ruleFor 187 lower178 none (by decide +kernel)

def rule187_3 : {c : Cut // CutGood (goalAt 187) c} :=
  ruleFor 187 lower186 none (by decide +kernel)

def rule187_4 : {c : Cut // CutGood (goalAt 187) c} :=
  ruleFor 187 lower171 none (by decide +kernel)

def rule187_5 : {c : Cut // CutGood (goalAt 187) c} :=
  ruleFor 187 lower155 none (by decide +kernel)

def rule187_6 : {c : Cut // CutGood (goalAt 187) c} :=
  ruleFor 187 lower59 none (by decide +kernel)

def rule187_7 : {c : Cut // CutGood (goalAt 187) c} :=
  ruleFor 187 lower43 none (by decide +kernel)

def rule187_8 : {c : Cut // CutGood (goalAt 187) c} :=
  ruleFor 187 lower177 none (by decide +kernel)

def rule187_9 : {c : Cut // CutGood (goalAt 187) c} :=
  ruleFor 187 lower169 none (by decide +kernel)

def rule187_10 : {c : Cut // CutGood (goalAt 187) c} :=
  ruleFor 187 lower184 none (by decide +kernel)

def rule187_11 : {c : Cut // CutGood (goalAt 187) c} :=
  ruleFor 187 lower153 none (by decide +kernel)

def rule187_12 : {c : Cut // CutGood (goalAt 187) c} :=
  ruleFor 187 lower154 none (by decide +kernel)

def rule187_13 : {c : Cut // CutGood (goalAt 187) c} :=
  ruleFor 187 lower57 none (by decide +kernel)

def rule187_14 : {c : Cut // CutGood (goalAt 187) c} :=
  ruleFor 187 lower41 none (by decide +kernel)

def rule187_15 : {c : Cut // CutGood (goalAt 187) c} :=
  ruleFor 187 lower58 none (by decide +kernel)

def rule187_16 : {c : Cut // CutGood (goalAt 187) c} :=
  ruleFor 187 lower145 none (by decide +kernel)

def rule187_17 : {c : Cut // CutGood (goalAt 187) c} :=
  ruleFor 187 lower146 none (by decide +kernel)

def rule187_18 : {c : Cut // CutGood (goalAt 187) c} :=
  ruleFor 187 lower27 none (by decide +kernel)

def rule187_19 : {c : Cut // CutGood (goalAt 187) c} :=
  ruleFor 187 lower147 none (by decide +kernel)

def rule187_20 : {c : Cut // CutGood (goalAt 187) c} :=
  ruleFor 187 lower139 none (by decide +kernel)

def cuts187 : Cuts (goalAt 187) := [rule187_0,rule187_1,rule187_2,rule187_3,rule187_4,rule187_5,rule187_6,rule187_7,rule187_8,rule187_9,rule187_10,rule187_11,rule187_12,rule187_13,rule187_14,rule187_15,rule187_16,rule187_17,rule187_18,rule187_19,rule187_20]

def state187_0 : List Sig := [0xffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaa,input 4,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 3,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude187_0 : Impossible true (goalAt 187) 6 state187_0.toFinset :=
  node_ok cuts187 [] 0xb0300e060b03026061000c26060b030400389030260603818240c098180e0c038302c0c0a8a02a28098182a280a8a02c0c038300e0c038182220088800840ca8a02a28038182a280a8a00840c88802228100092a280a8a00440c38300e0c100020e0c038300440ca8a02a2800b0a2a280a8a04002038300e0c00b0a0e0c0383040020a8a02a2808a0a0c4c031302c0c0a2a028a808a0a28a80a2a02c0c031300c4c02a0a20a0082800e060a2a028a802a0a28a80a2a00e060828020a80090328a80a2a02a28019182a28009030646019182a280a2a028a80110328a80a2a04002831300c4c011030c4c0313040024a2a028a800b0a28a80a1a0400003130286800b0a0c4c0313040000a2a028a80b0300440cb03022829000922828b03040038b0302282811032282838180440c38180a829000c0a82838184003038180a82811030a82900034000cb0a02c0c00b0a2c0c08a0a40038890a2c0c1000e2c0c08a0a02c280b0a0e0600b0a0e0602a0a40030290a0e061000c0e0602a0a02c280b0a (by decide +kernel)

def state187_1 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude187_1 : Impossible true (goalAt 187) 5 state187_1.toFinset :=
  node_ok cuts187 [] 0x240c01a0a240c00b0a2c280b0a0240c0b0a02c2800b0a068280b0a0e0601a0a0e0602a0a2c280b0a00e060b0a02c2802a0a06828281806828a8a02a280b0a00e0c0b0a00682838300e0c0b0a02a280a8a002c2838300e0c090302a280a8a002c28a8a02a28090300e0c038300e06009030e06021032a280a8a00e060a8a02a28021030240c220a06828a1a028680b0a00c8c0b0a00682832300c8c0b0a028680a1a00240ca1a028680a8a006860a8a00240c1a1806860a8a028680a1a002c2832300c4c0903028680a1a002c28a1a02868090300c8c032300a8281a1806860381828680a1a00a828a1a0286803818068601a180840c0b0a260603818240c090300840c9030240c0381802c283818 (by decide +kernel)

def state187_2 : List Sig := [0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 7,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 3,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude187_2 : Impossible true (goalAt 187) 6 state187_2.toFinset :=
  node_ok cuts187 [⟨state187_1,exclude187_1⟩] 0x1000c0e06038182040d000c2040d000c4003600002040c38180e061000c0e060381802c28210302c29000c0840c210302c2838180e06038182420090800a828b0a02c28038182c280b0a00a828908024281000d068281a0a2040cb0a02c281000e2c280b0a02040c1a0a06829000f06828190a02c28b0a02c281000e2c280b0a002c281a0a02c2838182220088800840ca8a02a28038182a280a8a00840c8880222801a0a2a280a8a02c28038302c2801a0a0e0c038302c280a8a02a281000d0e0c038302040ca8a02a28100022a280a8a02040c38300e0c00b0a0e0c0383040020a8a02a2800b0a2a280a8a04002038300e0c02a0a2060081800e060a1a0286802a0a28680a1a00e060818020e801a0a28680a1a02c28032302c2801a0a0c8c032302c280a1a028680090328680a1a02a2801a182a2800903068601a182a280a1a02868081030c8c0323040028a1a028680810328680a1a04003432300c8c00b0a0c8c0313040000a1a0286800b0a28680a1a04000032300c8c100034000cb030 (by decide +kernel)

def state187_3 : List Sig := [0xffffffffffffffffffffffffffffffffeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 0,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude187_3 : Impossible true (goalAt 187) 5 state187_3.toFinset :=
  node_ok cuts187 [] 0x38182c280b0a00a06090302c280b0a040038a8a02c28038302a28038182a280a8a00882838302a280a8a00e0c00b0a2c28011032c28009032a2800b0a2a2800b0a0e06021030e060a1a040034a2a02c2801a0a28a80a2a02a280090328a802a0a28a80a2a00e0603230260609030240c03818 (by decide +kernel)

def state187_4 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffaaaaaaaaffffffffaaaaaaaa,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 7,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude187_4 : Impossible true (goalAt 187) 5 state187_4.toFinset :=
  node_ok cuts187 [] 0x90302c280b0a0068281a0a2c280b0a006828190a2c280b0a002c28a8a02c28038302a28038302a280a8a00e0c009032a280a8a00240c0b0a2a280a8a040040a1a02c280313028680a1a02a2801a1828680313028680a1a00c4c01a1828680a1a006860191828680a1a0068608103400303818 (by decide +kernel)

def state187_5 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 7,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 0,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude187_5 : Impossible true (goalAt 187) 6 state187_5.toFinset :=
  node_ok cuts187 [⟨state187_1,exclude187_1⟩,⟨state187_3,exclude187_3⟩,⟨state187_4,exclude187_4⟩] 0x240c01a0a240c1000e2c280b0a0240c0b0a02c281000d068281a0a0e0601a0a0e0602a0a2c280b0a00e060b0a02c2802a0a06828281806828a8a02a280b0a00e0c0b0a00682838300e0c0b0a02a280a8a04003438300e0c090302a280a8a040044a8a02a28090300e0c038300e06009030e06021032a280a8a00e060a8a02a28021030240c220a0440c0b0a02c28b0a040030b0a00440d000e0440cb0a002c28b0a00240d00100240ca8a002c28a8a00240c0b0a02c28a8a040030a8a04002d000b28681000c02c280b0a240c1000c240c1000c400360000240c00b0a240c0210302c280b0a0e061000c0e06021038000821030e0600b0a0e0601a0a28a80a2a02c28032302c2801a0a0c8c032302c280a2a028a80090328a80a2a02a2801a182a2800903068601a182a280a2a028a81000d0c8c03230240c0a2a028a82000128a80a2a0240c032300c8c02a0a068601a180e060a2a028a802a0a28a80a2a00e0601a1806861000b4002c9818 (by decide +kernel)

def state187_6 : List Sig := [0xffffeeeeffffeeeeffffeeeeffffeeeeffffeeeeffffeeeeffffeeeeffffeeee,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 4,input 0,input 3,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude187_6 : Impossible true (goalAt 187) 6 state187_6.toFinset :=
  node_ok cuts187 [] 0xb030260609030240c038302a280a8a00e0c088802a280a8a022280a8a00e0c038302a280a8a00e0c038302a2800b0a2c0c081032c0c00b0a0e06021030e06009032a2800b0a2a2800b0a06428110302c28313040024b03022828b0300682838180a828381806828b0a00c8c0b0302282832300686032300c8c01a180c8c0a8a006860a8a0068283230088c0a2a02c0c088082c0c088080e06028080e0602808 (by decide +kernel)

def state187_7 : List Sig := [0xffff0000ffff0000ffff0000ffff0000eeee0000eeee0000eeee0000eeee,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 7,input 0,input 3,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude187_7 : Impossible true (goalAt 187) 5 state187_7.toFinset :=
  node_ok cuts187 [] 0xb030260609030240c088802a280a8a02228038302a280a8a00e0c00b0a0a06021030a06009032a2800b0a2a2800b0a2c0c081032c0c0a1a020a00a2a028a8082a028a80a8a006860a2a00c8c0a2a028a80323024280b0a02c28090802a28038302a280b0a02c280110302c28b0a022060b0a02c280b03028a80323028a80b0a0 (by decide +kernel)

def state187_8 : List Sig := [0xffffffffffffffffffffffffffffffffeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 7,input 0,input 3,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude187_8 : Impossible true (goalAt 187) 6 state187_8.toFinset :=
  node_ok cuts187 [⟨state187_3,exclude187_3⟩,⟨state187_7,exclude187_7⟩] 0x38182282a00000e06038180a8282a0a0e06090802c280b0a0242801a0a2c280b0a00682a00012c280b0a04002488802a280a8a022280a8a02c28038302a28038302a280a8a00e0c038302a280a8a00e0c00b0a0e06021030e0600b0a2c28011032c28009032a2800b0a2a2800b0a22428810302c28a1a040034b03020a00a2a028a8082a028a80b0a006828a2a028a80a8a00240ca2a022828a2a008a803230 (by decide +kernel)

def state187_9 : List Sig := [0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 0,input 3,input 4,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude187_9 : Impossible true (goalAt 187) 7 state187_9.toFinset :=
  node_ok cuts187 [⟨state187_0,exclude187_0⟩,⟨state187_2,exclude187_2⟩,⟨state187_5,exclude187_5⟩,⟨state187_6,exclude187_6⟩,⟨state187_8,exclude187_8⟩] 0x40030b0300e060b0304002c981840030981840030b0308000890304002c98180e060903040034b03006828b030400248a0a2c280b0a040038b0302c280b0a0400348a0a0682888184002c3818242009080400302a0a2c280b0a04003038182c280b0a04002c2a0a2420090a04003498180e0c0383040020b0302a280a8a04000898182a280a8a040034b0300e0c038304002c38182220088804003021032a280a8a04003038182a280a8a04002c21032220088a0400241a0a2a280a8a040020b0a00e0c0b0a0400081a0a0e0c0383040024b0a02a280a8a04000c810302c280b0a4000cb0304000cb0304000c81038000481034000cb03002c28b0304000c210302c280b0a4000c38184000c38184000c21034003021034000c381802c2838184000c110302c280b0a4000cb0a04000cb0a04000c11038000011034000cb0a002c28b0a04000c09034002009034000ca8a002c28a8a04000c090302c280b0a4000ca8a04000ca8a040001000040000a1a0400348a0a0c8c0323040028b03028a80a2a0800108a0a28a80a2a040034b0300c8c032304002c2a0a20a00828040030381828a80a2a0400302a0a28a80a2a04002c381820a0082a0400241a0a28a80a2a040028b0a00c8c0b0a08000c1a0a0c8c0323040024b0a028a80a2a040020090328a80a2a040008a8a006860a8a0400080903068601a1840020a8a028a80a2a0 (by decide +kernel)

def state187_10 : List Sig := [0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 0,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 1,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude187_10 : Impossible true (goalAt 187) 6 state187_10.toFinset :=
  node_ok cuts187 [⟨state187_1,exclude187_1⟩] 0x38180682838180a828b0a02c28038182c280b0a00a8281a0a0a060903006828903040050b0a02c28090302c280b0a0400501a0a068281a0a2a280a8a02c28038302c2801a0a0e0c038302c280a8a02a280381802c0c381808c0ca8a02a28038182a280a8a008c0c0b0308829000f0e0c03830240c0a8a02a28100112a280a8a0240c038300e0c01a0a28a80a2a02c28032302c2801a0a0c8c032302c280a2a028a800b0328a80a2a02a2801a182a2800b03068601a182a280a2a028a802a0a068601a180e060a2a028a802a0a28a80a2a00e0601a1806861000d0c8c03230240c0a2a028a81000d28a80a2a0240c032300c8c0130328680a1a02c281000c2c28013034001c13032c280a1a0286800b0328680a1a02a281000c2a2800b03400440b032a280a1a028681000c28680a1a028a81000c28a81000c40036000028a80a1a02868023034004823030e060a1a028680230328680a1a00e061000c0e061000640018313008c0d0005260603818240c0903008c0c9030240c03818400143818 (by decide +kernel)

def state187_11 : List Sig := [0xffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00,input 3,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 0,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude187_11 : Impossible true (goalAt 187) 6 state187_11.toFinset :=
  node_ok cuts187 [] 0x38180682838180a828b0a02c28038182c280b0a00a8281a0a0a060903004c0c903040050b0a02c28090302c280b0a040050130304c0c1a0a28a80a2a02c28032302c2801a0a0c8c032302c280a2a028a802a0a068601a180e060a2a028a802a0a28a80a2a00e0601a1806861001328a80a2a02a2801a182a281000d068601a182a280a2a028a81000d0c8c03230240c0a2a028a81000d28a80a2a0240c032300c8c0130328680a1a02c28031302c28013030c4c031302c280a1a028681000d28680a1a028a800b0a28a81001102c280b0a28a80a1a02868023030646019180e060a1a028680230328680a1a00e060191806461001328680a1a02a28019182a28100110646019182a280a1a02868100110c4c03130240c0a1a028681001128680a1a0240c031300c4c01a0a2a280a8a02c28100132c2801a0a4001c1a0a2c280a8a02a280381840048381808c0ca8a02a28038182a280a8a008c0d00132406100064001838300e06100050e0602303240c090300e0609030240c02303400142303 (by decide +kernel)

def state187_12 : List Sig := [0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00aa00aa00ff00ff00aa00aa,input 0,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 7,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude187_12 : Impossible true (goalAt 187) 5 state187_12.toFinset :=
  node_ok cuts187 [] 0x90302c280b0a00482838182c280b0a00a060a2a02c280323028a80323028a80a2a00c8c01a1828a80a2a006860981828680b0a00c4c0a1a028680a2a002c28a1a00c4c0a1a028680313006460a1a02868019182a28038302c280a8a028a801a1828a80a8a00e0c0a8a02a280383008828a8a02a280381828680191828680a8a0 (by decide +kernel)

def state187_13 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffaaaaaaaaffffffffaaaaaaaa,input 0,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 7,input 1,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude187_13 : Impossible true (goalAt 187) 6 state187_13.toFinset :=
  node_ok cuts187 [⟨state187_4,exclude187_4⟩,⟨state187_12,exclude187_12⟩] 0x90302c280b0a0068281a0a2c280b0a0068281a0a2c280b0a006828a8a02c28038302a28038302a280a8a00e0c00b032a280a8a002c0e00012a280a8a04004ca2a02c280323028a80a2a02a2801a1828a80323028a80a2a00c8c01a1828a80a2a0068601a1828a80a2a006860830340030381828680b0a00c4c0a1a028680a8a002c0ca1a028680a2a080000a1a00c4c0a1a028680313008c0ca1a0044c01918 (by decide +kernel)

def state187_14 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffff00ff00ffffffffff00ff00,input 3,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 7,input 0,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude187_14 : Impossible true (goalAt 187) 6 state187_14.toFinset :=
  node_ok cuts187 [] 0x90302c280b0a00682838182c280b0a00a06013032c280b0a004c0ca2a02c280323028a80323028a80a2a00c8c01a1828a80a2a006860a2a02a2801a1828a80121028a80a2a004840a1a02c280313028680a1a028a800b0a28680313028680a1a00c4c0191828680a1a006460a1a02a280191828680111028680a1a00444098184004c23032a280b0a00e0c0a8a00e0c0a8a02a28038300e060a8a0088280b03 (by decide +kernel)

def state187_15 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 7,input 0,input 1,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude187_15 : Impossible true (goalAt 187) 7 state187_15.toFinset :=
  node_ok cuts187 [⟨state187_5,exclude187_5⟩,⟨state187_10,exclude187_10⟩,⟨state187_11,exclude187_11⟩,⟨state187_13,exclude187_13⟩,⟨state187_14,exclude187_14⟩] 0x4001890300682890304001900142c280b0a04001890302c280b0a0400190006068281a0a4001c3818068283818400502a0a2c280b0a04001c38182c280b0a0400502a0a068282818400501a0a2a280a8a04004cb0a00e0c0b0a04001c1a0a0e0c0383040050b0a02a280a8a04001900060e0c038304001890302a280a8a04001a00022a280a8a04001890300e0c0383040048381802c0c38184004c23032a280a8a08001038182a280a8a04004c230302c0c220a400501a0a28a80a2a04002cb0a00c8c0b0a0400341a0a0c8c0323040050b0a028a80a2a04004c0b0328a80a2a04002ca8a006860a8a0400340b03068601a184004ca8a028a80a2a04001900060c8c0323040018903028a80a2a040019000d28a80a2a04001890300c8c03230400342a0a068601a184002c381828a80a2a0400342a0a28a80a2a04002c3818068601a1840050130328680a1a040030b0a00c4c0b0a04001c13030c4c0313040050b0a028680a1a04004c0b0328680a1a040030a8a006460a8a0400440b030646019184004ca8a028680a1a04002d000d28680a1a040030a2a002c28a2a040036000002c280b0a4002ca2a028680a1a04001900060c4c0313040018903028680a1a04001a000128680a1a04001890300c4c0313040048230306460191840030381828680a1a08000c230328680a1a0400303818064601918400150005400149818 (by decide +kernel)

def state187_16 : List Sig := [0xffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaa,input 0,input 4,input 1,input 3,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude187_16 : Impossible true (goalAt 187) 7 state187_16.toFinset :=
  node_ok cuts187 [⟨state187_0,exclude187_0⟩] 0xb0300e060b03026061001426060b0304001c9030260603818240c098180e0c038302c0c0a8a02a28098182a280a8a02c0c038300e0c0381822200888008c0ca8a02a28038182a280a8a008c0c88802228100042a280a8a004c0c38300e0c100020e0c0383004c0ca8a02a28100022a280a8a04000438300e0c100020e0c0383040004a8a02a2808a0a0c8c032302c0c0a2a028a808a0a28a80a2a02c0c032300c8c02a0a20a0082800e060a2a028a802a0a28a80a2a00e060828020a800b0328a80a2a02a2801a182a2800b03068601a182a280a2a028a80130328a80a2a00440432300c8c013030c8c0323004404a2a028a81000928a80a2a04000032300c8c100090c8c0323040000a2a028a80b03004c0cb03022829000422828b0304001cb03022828130322828381804c0c38180a82900040a82838184005038180a82813030a82900034000cb0a020c0c31300c4c0b0304000cb03020c0d000720c0cb0300c4c0313008c0c19180646038180c4c0313008c0c31300c4c0381806460191802c0c31300c4c0a8a006460a8a002c0c191806460a8a00c4c0a8a04000c31300c4c0a2a04000ca2a04000d000980000a2a00c4c0a2a004c0d000404c0d00030c4c031304000d0003084c1000340010a1a02c0c100062c0c08a0a4001c8a0a2c0c100072c0c08a0a400188a0a0e06100050e0602a0a400502a0a0e06100140e0602a0a400142a0a (by decide +kernel)

def state187_17 : List Sig := [0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 0,input 7,input 1,input 3,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude187_17 : Impossible true (goalAt 187) 7 state187_17.toFinset :=
  node_ok cuts187 [⟨state187_2,exclude187_2⟩,⟨state187_10,exclude187_10⟩] 0x100060e060381820c0d000620c0d000c4001a000120c0c38180e061000c0e060381840014230308c0d000c08c0c23034001438180e06038182420090800a828b0a02c28038182c280b0a00a8289080242810006068281a0a20c0cb0a02c28100072c280b0a020c0c1a0a068290007068281a0a40010b0a02c28100072c280b0a0400101a0a06828381822200888008c0ca8a02a28038182a280a8a008c0c8880222801a0a2a280a8a02c28038302c2801a0a0e0c038302c280a8a02a28100060e0c0383020c0ca8a02a28100022a280a8a020c0c38300e0c100020e0c0383040004a8a02a28100022a280a8a04000438300e0c02a0a20a0082800e060a2a028a802a0a28a80a2a00e060828020a801a0a28a80a2a02c28032302c2801a0a0c8c032302c280a2a028a800b0328a80a2a02a2801a182a2800b03068601a182a280a2a028a8083030c8c0323020404a2a028a80830328a80a2a02040432300c8c1000d0c8c0323040000a2a028a81000d28a80a2a04000032300c8c100034000cb03008c0c818020600381828680a1a008c0ca1a02868038182060081a004c0ca1a028680b0a04000cb0a004c0d000704c0cb0a028680a1a002c0ca1a028680a8a04000ca8a002c0d000202c0ca8a028680a1a04000ca1a028680a2a04000ca2a04000d000d80000a2a028680a1a020c0d000620c0d000328680a1a04000d0003086810003400183130 (by decide +kernel)

def state187_18 : List Sig := [0xffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00,input 3,input 4,input 0,input 1,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude187_18 : Impossible true (goalAt 187) 7 state187_18.toFinset :=
  node_ok cuts187 [] 0xb0300e060b03026061001426060b0304001c9030260603818240c08a0a0c8c032302c0c0a2a028a808a0a28a80a2a02c0c032300c8c02a0a20a0082800e060a2a028a802a0a28a80a2a00e060828020a801a0a28a80a2a04002432300c8c01a0a0c8c0323040010a2a028a81000128a80a2a00e0c01a180e0c10009068601a180e0c0a2a028a81000928a80a2a04000032300c8c100090c8c0323040000a2a028a8083030c4c031302c0c0a1a028680830328680a1a02c0c031300c4c023032060081800e060a1a028680230328680a1a00e060818020681000928680a1a028a800b0a28a81000202c280b0a28a80a1a028681000428680a1a00682831300c4c100020c4c0313006828a1a028681000128680a1a00e0c019180e0c100020646019180e0c0a1a028681000228680a1a04000c31300c4c100020c4c031304000ca1a028680b03006828b03022829000422828b0304001cb030228281a0a2206038180682838180a82900040a82838184005028180a8281a0a0a061000140004b0a02606038300e0c0b03040004b03026061000724060b0300e0c038300e06100140e06023030e0c038300e06038300e0c023034000423030682900040682900010e0c038304000500010a0c1000140010a8a02c0c100062c0c083034001c83032c0c100072c0c083034001883030e06100050e06023034005023030e06100140e0602303400142303 (by decide +kernel)

def state187_19 : List Sig := [0xffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00,input 3,input 7,input 0,input 1,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude187_19 : Impossible true (goalAt 187) 7 state187_19.toFinset :=
  node_ok cuts187 [⟨state187_11,exclude187_11⟩] 0x100060e06038182606100062606100134001a00002606038180e061001308c0c23034001438180e06100130e060381840014230308c0c38182420090800a828b0a02c28038182c280b0a00a828908024280981806828981822828b0a02c28098182c280b0a0228281a0a22061000704c0c130340010b0a02c28100072c280b0a040010130304c0c2a0a20a0082800e060a2a028a802a0a28a80a2a00e060828020a801a0a28a80a2a02c28032302c2801a0a0c8c032302c280a2a028a808a0a0c8c0323026060a2a028a808a0a28a80a2a02606032300c8c1000128a80a2a02a2801a182a281000d068601a182a280a2a028a81000d0c8c0323040000a2a028a81000d28a80a2a04000032300c8c023032060081800e060a1a028680230328680a1a00e060818020680130328680a1a02c28031302c28013030c4c031302c280a1a028681000d28680a1a028a800b0a28a81000202c280b0a28a80a1a02868100060c4c0313026060a1a028681000228680a1a02606031300c4c1000128680a1a02a28019182a28100020646019182a280a1a02868100020c4c031304000ca1a028681000228680a1a04000c31300c4c1000140004b0300e06088802220023032a280a8a00e060a8a02a28023032220088a006828a8a02a280b0a040004b0a006829000706828b0a02a280a8a02606100062606100012a280a8a04000500010a2810001400183830 (by decide +kernel)

def state187_20 : List Sig := roots 187
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude187_20 : Impossible true (goalAt 187) 8 state187_20.toFinset :=
  node_ok cuts187 [⟨state187_9,exclude187_9⟩,⟨state187_15,exclude187_15⟩,⟨state187_16,exclude187_16⟩,⟨state187_17,exclude187_17⟩,⟨state187_18,exclude187_18⟩,⟨state187_19,exclude187_19⟩] 0x40014b0300e060b03040014981840014981840014b0308000490304001498180e060903040018b03006828b030400108a0a2c280b0a04001cb0302c280b0a0400108a0a068288818400143818242009080400142a0a2c280b0a04001438182c280b0a0400142a0a2420090a04001898180e0c0383040004b0302a280a8a08001498182a280a8a040004b0300e0c038304001438182220088804001423032a280a8a04001438182a280a8a04001423032220088a0400101a0a2a280a8a040004b0a00e0c0b0a0800101a0a0e0c0383040004b0a02a280a8a0400008a0a0c8c0323040000b03028a80a2a0400008a0a28a80a2a040000b0300c8c03230400002a0a20a00828040000381828a80a2a0400002a0a28a80a2a040000381820a0082a0400001a0a28a80a2a040000b0a00c8c0b0a0400001a0a0c8c0323040000b0a028a80a2a0400000b0328a80a2a040000a8a006860a8a0400000b03068601a1840000a8a028a80a2a04001883030c4c031304000cb03028680a1a08000c830328680a1a04000cb0300c4c0313040014230320600818040014381828680a1a040014230328680a1a04001438182060081a040010130328680a1a04000cb0a00c4c0b0a08000813030c4c031304000cb0a028680a1a0400040b0328680a1a04000ca8a006460a8a0400080b0306460191840004a8a028680a1a040001000028680a1a040000a2a002c28a2a040002000002c280b0a40000a2a028680a1a0 (by decide +kernel)

theorem lower187 : Claim 187 9 :=
  fromSearch 67 (by decide +kernel) exclude187_20

theorem lower249 : Claim 249 8 :=
  fromLift 8 64 3 lower185 (by decide +kernel)

theorem lower209 : Claim 209 5 :=
  fromLift 5 64 4 lower145 (by decide +kernel)

def cuts81 : Cuts (goalAt 81) := []

def state81_0 : List Sig := roots 81
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude81_0 : Impossible true (goalAt 81) 3 state81_0.toFinset :=
  node_ok cuts81 [] 0x140401101140404101141005040140405040141004101044041101104041110044405010105004140104044140105005010044401110044044140105005040044405040044041110044405040105004140 (by decide +kernel)

theorem lower81 : Claim 81 4 :=
  fromSearch 4 (by decide +kernel) exclude81_0

theorem lower83 : Claim 83 5 :=
  fromLift 5 2 68 lower81 (by decide +kernel)

def rule211_0 : {c : Cut // CutGood (goalAt 211) c} :=
  ruleFor 211 lower209 none (by decide +kernel)

def rule211_1 : {c : Cut // CutGood (goalAt 211) c} :=
  ruleFor 211 lower210 none (by decide +kernel)

def rule211_2 : {c : Cut // CutGood (goalAt 211) c} :=
  ruleFor 211 lower147 none (by decide +kernel)

def rule211_3 : {c : Cut // CutGood (goalAt 211) c} :=
  ruleFor 211 lower83 none (by decide +kernel)

def cuts211 : Cuts (goalAt 211) := [rule211_0,rule211_1,rule211_2,rule211_3]

def state211_0 : List Sig := roots 211
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude211_0 : Impossible true (goalAt 211) 6 state211_0.toFinset :=
  node_ok cuts211 [] 0x40008c24214040c24240008901040008901040008c2424000c82424000890101404082424000c90101490852424000cc24234300d0c04000c901034300d0c04000cc2421490850c040008501024200908040008430334300d0c040008501034300d0c04000843032420090c040000c24204840c24240000901030b00c2c040000c24230b00c2c040000901004840121040000430320a00828040000501030b00c2c040000430330b00c2c040000501020a0082c040000524230b00c2c040000d0c004840d0c040000524204840504240000d0c030b00c2c040004830310d08434240004c24230700c1c040004830330700c1c040004c24210d08434240008430320600818040008501030700c1c040008430330700c1c04000850102060081c040004130330700c1c040004d0c004440d0c040004130304440111040004d0c030700c1c040001000030700c1c040000c2c010d08c2c040001000110d08434240000c2c030700c1c0 (by decide +kernel)

theorem lower211 : Claim 211 7 :=
  fromSearch 68 (by decide +kernel) exclude211_0

theorem lower243 : Claim 243 8 :=
  fromLift 8 32 68 lower211 (by decide +kernel)

theorem lower201 : Claim 201 5 :=
  fromLift 5 64 3 lower137 (by decide +kernel)

def cuts195 : Cuts (goalAt 195) := []

def state195_0 : List Sig := roots 195
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude195_0 : Impossible true (goalAt 195) 3 state195_0.toFinset :=
  node_ok cuts195 [] 0x30908830320908824230908c2c030b00810320a00c2c030b0082c010d08c1c030700434220600c1c03070081c030700c2c010d08c1c0 (by decide +kernel)

theorem lower195 : Claim 195 4 :=
  fromSearch 118 (by decide +kernel) exclude195_0

def cuts73 : Cuts (goalAt 73) := []

def state73_0 : List Sig := roots 73
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude73_0 : Impossible true (goalAt 73) 3 state73_0.toFinset :=
  node_ok cuts73 [] 0x120200901120204101121004840120204840121004101024040901104040908024204808105004140104044140105004808024200908024044140105004840024204840024040908024204840105004140 (by decide +kernel)

theorem lower73 : Claim 73 4 :=
  fromSearch 3 (by decide +kernel) exclude73_0

def rule203_0 : {c : Cut // CutGood (goalAt 203) c} :=
  ruleFor 203 lower201 none (by decide +kernel)

def rule203_1 : {c : Cut // CutGood (goalAt 203) c} :=
  ruleFor 203 lower202 none (by decide +kernel)

def rule203_2 : {c : Cut // CutGood (goalAt 203) c} :=
  ruleFor 203 lower195 none (by decide +kernel)

def rule203_3 : {c : Cut // CutGood (goalAt 203) c} :=
  ruleFor 203 lower139 none (by decide +kernel)

def rule203_4 : {c : Cut // CutGood (goalAt 203) c} :=
  ruleFor 203 lower73 none (by decide +kernel)

def rule203_5 : {c : Cut // CutGood (goalAt 203) c} :=
  ruleFor 203 lower137 none (by decide +kernel)

def cuts203 : Cuts (goalAt 203) := [rule203_0,rule203_1,rule203_2,rule203_3,rule203_4,rule203_5]

def state203_0 : List Sig := [0xffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffee,input 3,input 0,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude203_0 : Impossible true (goalAt 203) 4 state203_0.toFinset :=
  node_ok cuts203 [] 0x30908880a20908824210d08c1422040c434202c28434210d080b0a10d08484202c28434230700484230908820a12108480a1210848420240cc8c030908c2c030b01000420a00c2c030b0082c0 (by decide +kernel)

def state203_1 : List Sig := [0xee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee,input 3,input 0,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude203_1 : Impossible true (goalAt 203) 4 state203_1.toFinset :=
  node_ok cuts203 [] 0xc24222028824220908434230508810310d080b0a10d08434202c28c9c0323000b0a32300484032300c8c012b00888032300c8c022b00c24230b00c2c022028828030b00c2c020b00c1c030700434230b004842 (by decide +kernel)

def state203_2 : List Sig := [0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 0,input 3,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude203_2 : Impossible true (goalAt 203) 5 state203_2.toFinset :=
  node_ok cuts203 [⟨state203_0,exclude203_0⟩,⟨state203_1,exclude203_1⟩] 0xc24212828c24222829000522828c242400108242228284a0a209088a0a129084a4230908c8c0323008a0a32300c8c0309084a42123004a0a2220088801040cc8c0323004a0a32300c8c01040c888022300810310d08434230909000130508810340010810330908434210d08410302c280b0a12828434210d08410310d084342128280b0a02c28090310d084342323000b0a32300090302c280b0a32300434232301000040000c1c030909000430908880830b00c2c030908c2c030b00880840010880a12828828020a00480830b00c2c012828c2c030b00480820a0082c012908c2c030b00c8c080004c8c01290a000012108c8c030b00c2c0 (by decide +kernel)

def state203_3 : List Sig := [0x5544554455445544554455445544554455445544554455445544554455445544,input 0,input 3,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude203_3 : Impossible true (goalAt 203) 4 state203_3.toFinset :=
  node_ok cuts203 [] 0xc24222028824220908484230908820a12108480a1210848420240c414030700c1c010f00818030700c1c020f00c1c032700090330700c24230b00c2c02040c828030b00c2c020b00c2c032300484230b004342 (by decide +kernel)

def state203_4 : List Sig := [0xffccffccffccffccffccffccffccffccffccffccffccffccffccffccffccffcc,input 3,input 0,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude203_4 : Impossible true (goalAt 203) 5 state203_4.toFinset :=
  node_ok cuts203 [⟨state203_0,exclude203_0⟩,⟨state203_3,exclude203_3⟩] 0xc24212028c24222029000522028c24240010824222028480a20908830310d08434230908c1c030700830330700c1c030908434210d08430320600818012028c1c030700430330700c1c012028818020700090330700c1c0121080b0a12108090302c280b0a12108c1c030702000130700c1c030b00434230b02000010d08434230b00c1c030700880a12108484230909000230908880a40010820a30908484212108480a0240c480a10c0c484212108480a12108484210c0c09030240d000040000c8c030909000430908810130b00c2c030908c2c030b00810140010810312028828020a00410130b00c2c012028c2c030b00410120a0082c0 (by decide +kernel)

def state203_5 : List Sig := [0xffaaffaaffaaffaa0000000000000000ffaaffaaffaaffaa,input 0,input 3,input 1,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude203_5 : Impossible true (goalAt 203) 4 state203_5.toFinset :=
  node_ok cuts203 [] 0x20908c2c030b00880a30b00c8c012108c2c012908c8c032300488010d08c1c030700434230700c2c010d08c1c030700c8c002c28c1c012828824222828824212028c2c012828c2c022300c8c012828c8c020700c1c002c28c1c0 (by decide +kernel)

def state203_6 : List Sig := [0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 0,input 3,input 1,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude203_6 : Impossible true (goalAt 203) 5 state203_6.toFinset :=
  node_ok cuts203 [⟨state203_0,exclude203_0⟩,⟨state203_5,exclude203_5⟩] 0xc24222828824220908c24230b00c2c022028828030b00c2c020b00c2c002404090330b00c2c040002000030b008a0a309088a0a309084a0a10c0c4a0a02c0cc8c002c28c24220c0cc24202c284a0a10c0c0b0a02420c2c002c28c2c002c0c0b0a40004c1c022828c24222828c2421282a0001128290003 (by decide +kernel)

def state203_7 : List Sig := roots 203
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude203_7 : Impossible true (goalAt 203) 6 state203_7.toFinset :=
  node_ok cuts203 [⟨state203_2,exclude203_2⟩,⟨state203_4,exclude203_4⟩,⟨state203_6,exclude203_6⟩] 0x4000cc24212828c2424000c8a0a4000c8a0a4000cc2424001082424000c8a0a128288242400108a0a129084a4240008c24232300c8c0400108a0a32300c8c040008c2421290848c04000c4a0a2220088804000c430332300c8c04000c4a0a32300c8c04000c43032220088c040000c24240010c24240000880830b00c2c040000c24230b00c2c040000880840000880a400004a0a20a00828040000480830b00c2c0400004a0a30b00c2c040000480820a0082c0400004a4230b00c2c040000c8c040000c8c0400004a4280004484240000c8c030b00c2c040010830310d08434240004c24230700c1c040010830330700c1c040004c24210d0843424000c43032060081804000c4a0a30700c1c04000c430330700c1c04000c4a0a2060081c0400080b0330700c1c040004c8c002c28c8c0800080b0302c280b0a40004c8c030700c1c040001000030700c1c040000c2c010d08c2c040002000010d08434240000c2c030700c1c0 (by decide +kernel)

theorem lower203 : Claim 203 7 :=
  fromSearch 115 (by decide +kernel) exclude203_7

theorem lower235 : Claim 235 8 :=
  fromLift 8 32 83 lower203 (by decide +kernel)

theorem lower217 : Claim 217 6 :=
  fromLift 6 8 3 lower209 (by decide +kernel)

theorem lower89 : Claim 89 5 :=
  fromLift 5 8 3 lower81 (by decide +kernel)

def rule91_0 : {c : Cut // CutGood (goalAt 91) c} :=
  ruleFor 91 lower89 none (by decide +kernel)

def rule91_1 : {c : Cut // CutGood (goalAt 91) c} :=
  ruleFor 91 lower83 none (by decide +kernel)

def rule91_2 : {c : Cut // CutGood (goalAt 91) c} :=
  ruleFor 91 lower90 none (by decide +kernel)

def rule91_3 : {c : Cut // CutGood (goalAt 91) c} :=
  ruleFor 91 lower73 none (by decide +kernel)

def rule91_4 : {c : Cut // CutGood (goalAt 91) c} :=
  ruleFor 91 lower27 none (by decide +kernel)

def rule91_5 : {c : Cut // CutGood (goalAt 91) c} :=
  ruleFor 91 lower81 none (by decide +kernel)

def cuts91 : Cuts (goalAt 91) := [rule91_0,rule91_1,rule91_2,rule91_3,rule91_4,rule91_5]

def state91_0 : List Sig := [0xffffffffffffffffeeeeeeeeeeeeeeeeffffffffffffffffeeeeeeeeeeeeeeee,input 6,input 0,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude91_0 : Impossible true (goalAt 91) 4 state91_0.toFinset :=
  node_ok cuts91 [] 0x6828504214108124006860504214109000312108504204828484212028484212108090306860484212108121810d0850420440c434210d08484202c28434202c28434210d080b0a064605818 (by decide +kernel)

def state91_1 : List Sig := [0xeeeeeeeeeeeeeeee0000000000000000eeeeeeeeeeeeeeee,input 6,input 0,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude91_1 : Impossible true (goalAt 91) 4 state91_1.toFinset :=
  node_ok cuts91 [] 0x581814108504212060484214108120a12108581812108484214060434214108110310d084342121080b0a10d08591810d084342160601a0a141081a18141081210121081a1812108191810d080b0a10d08480a (by decide +kernel)

def state91_2 : List Sig := [0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 0,input 3,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude91_2 : Impossible true (goalAt 91) 5 state91_2.toFinset :=
  node_ok cuts91 [⟨state91_0,exclude91_0⟩,⟨state91_1,exclude91_1⟩] 0x5818068285818128285242149085818149085242128281a0a1206058180240c5818140404a42129085818129084a42140400903140601a0a129084a42149090005149081a0a4000c120a149084a4212908410302c280b0a16060434210d08410310d084342160600b0a16060110310d0843421490900021450811034000c110314908434210d08090310d084342129080b0a12508090302c280b0a12908434210d090000400004140128281a180686058188000458181282a0000120285818068601a18149090003149085040068605040149081a181410850404000c5042129081210129084840068604840129081a18121084840048404842 (by decide +kernel)

def state91_3 : List Sig := [0x5555555555555555444444444444444455555555555555554444444444444444,input 0,input 6,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude91_3 : Impossible true (goalAt 91) 4 state91_3.toFinset :=
  node_ok cuts91 [] 0x1a0a14108504204900484214108120a12108480a1210848420240c09081410819181410811101210819181210819181646041030646050420686050420440c4842068604842048601a1816060480a068604342 (by decide +kernel)

def state91_4 : List Sig := [0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,input 6,input 0,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude91_4 : Impossible true (goalAt 91) 5 state91_4.toFinset :=
  node_ok cuts91 [⟨state91_0,exclude91_0⟩,⟨state91_3,exclude91_3⟩] 0x10003068281a0a120285042141090003141085042120281a0a049001a18044041a184000c5042141081a181410850424000c11010440c1a0a121084842141090005141081a0a4000c120a14108484212108480a02c0c480a1040c484212108480a1210848421040c0b0302c0c1a18024041a18048404842121081a1812108484204840090104860130310d08434214108191814108130306460191814108434210d080b0310d084342121081918121080b0306460191812108434210d08410306460191812028434210d08410310d08434212028191806462000106460191806860434210d0a000010d084342068601918064610000400005818 (by decide +kernel)

def state91_5 : List Sig := [0xff00ff00ff00ff00aa00aa00aa00aa00ff00ff00ff00ff00aa00aa00aa00aa,input 0,input 6,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude91_5 : Impossible true (goalAt 91) 4 state91_5.toFinset :=
  node_ok cuts91 [] 0x160605242149084818149085040141085042068605818120281a1810d08524206460434210500434210d08414206460434210d08191812908120a149084a42121084842129084840140604a4212908581810d08191810d084a42 (by decide +kernel)

def state91_6 : List Sig := [0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa,input 0,input 6,input 1,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude91_6 : Impossible true (goalAt 91) 5 state91_6.toFinset :=
  node_ok cuts91 [⟨state91_0,exclude91_0⟩,⟨state91_5,exclude91_5⟩] 0x1a0a149085242068281a0a149085242068284a4214908120a129080b03129084a4202c0e0001129084a42400045242141005042141084a42121004842121081a18104044103068601a1840002000006860581810d08524204c0c434210d084a4202c0c434210500434210d08414210c0c4342400081918 (by decide +kernel)

def state91_7 : List Sig := roots 91
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude91_7 : Impossible true (goalAt 91) 6 state91_7.toFinset :=
  node_ok cuts91 [⟨state91_2,exclude91_2⟩,⟨state91_4,exclude91_4⟩,⟨state91_6,exclude91_6⟩] 0x4000c58180682858184000c4a0a1490852424000c58181490852424000c4a0a06828481840004581802c0c5818400045010129084a42400045818129084a4240004501002c0c5018400041a0a129084a42400045242400045242400041a0a4000c120a400045242129084a42400004a0a068601a18400005818400005818400004a0a80004480a400005818068601a184000052424000c5242400005040068605040400005242068605042400005040400005042400004a42048404a42400004840068604840400004a4206860484240000484004840484240010430306460191840008581810d08434280008430310d0843424000858180646019184000c130310d0843424000852420646052424000c130306460191840008524210d084342400040b0310d084342400044a42064604a42400040b03064601918400044a4210d084342400010000105004140400001a1810d08434240002000010d084342400001a18105004142 (by decide +kernel)

theorem lower91 : Claim 91 7 :=
  fromSearch 67 (by decide +kernel) exclude91_7

def rule219_0 : {c : Cut // CutGood (goalAt 219) c} :=
  ruleFor 219 lower217 none (by decide +kernel)

def rule219_1 : {c : Cut // CutGood (goalAt 219) c} :=
  ruleFor 219 lower218 none (by decide +kernel)

def rule219_2 : {c : Cut // CutGood (goalAt 219) c} :=
  ruleFor 219 lower211 none (by decide +kernel)

def rule219_3 : {c : Cut // CutGood (goalAt 219) c} :=
  ruleFor 219 lower203 none (by decide +kernel)

def rule219_4 : {c : Cut // CutGood (goalAt 219) c} :=
  ruleFor 219 lower155 none (by decide +kernel)

def rule219_5 : {c : Cut // CutGood (goalAt 219) c} :=
  ruleFor 219 lower91 none (by decide +kernel)

def rule219_6 : {c : Cut // CutGood (goalAt 219) c} :=
  ruleFor 219 lower210 none (by decide +kernel)

def rule219_7 : {c : Cut // CutGood (goalAt 219) c} :=
  ruleFor 219 lower201 none (by decide +kernel)

def rule219_8 : {c : Cut // CutGood (goalAt 219) c} :=
  ruleFor 219 lower203 (some (1,input 0,input 1)) (by decide +kernel)

def rule219_9 : {c : Cut // CutGood (goalAt 219) c} :=
  ruleFor 219 lower153 none (by decide +kernel)

def rule219_10 : {c : Cut // CutGood (goalAt 219) c} :=
  ruleFor 219 lower154 none (by decide +kernel)

def rule219_11 : {c : Cut // CutGood (goalAt 219) c} :=
  ruleFor 219 lower89 none (by decide +kernel)

def rule219_12 : {c : Cut // CutGood (goalAt 219) c} :=
  ruleFor 219 lower91 (some (1,input 0,input 1)) (by decide +kernel)

def rule219_13 : {c : Cut // CutGood (goalAt 219) c} :=
  ruleFor 219 lower73 none (by decide +kernel)

def cuts219 : Cuts (goalAt 219) := [rule219_0,rule219_1,rule219_2,rule219_3,rule219_4,rule219_5,rule219_6,rule219_7,rule219_8,rule219_9,rule219_10,rule219_11,rule219_12,rule219_13]

def state219_0 : List Sig := [0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 0,input 3,input 4,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude219_0 : Impossible true (goalAt 219) 7 state219_0.toFinset :=
  node_ok cuts219 [] 0x4002cc24216060c24240024981840028981840028c2424003082424002498181606082424002c98181490852424001cc24234300d0c040034981834300d0c04002cc2421490850c0400245818242009080400284a0a34300d0c040028581834300d0c0400244a0a2420090c04002c9818129084a4240018c24232300c8c040018981832300c8c04002cc2421290848c040024581822200888040028501032300c8c040028581832300c8c04002450102220088c0400181a0a32300c8c040018d0c040018d0c0400181a0a40020120a40018d0c032300c8c040004810310d08434240004c24240004c14240004810340030810340004c24210d08434240004410302c280b0a40004581810d08434240004410310d08434240004581802c28581840004110310d08434240004d0c040004d0c040004110340020110340004d0c010d08d0c040004090310d08434240004c8c002c28c8c040004090302c280b0a40004c8c010d08c8c040001000040000c1c04002cc24206860c24240030981830b00c2c040030c24230b00c2c04002c9818068601a18400244a0a20a00828040028581830b00c2c0400284a0a30b00c2c040024581820a0082c04001c524230b00c2c040020d0c006860d0c04002052420686050424001cd0c030b00c2c0400184a4230b00c2c040018c8c006860c8c0400184a4206860484240018c8c030b00c2c0 (by decide +kernel)

def state219_1 : List Sig := [0x4444444444444444444444444444444444444444444444444444444444444444,input 0,input 3,input 4,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude219_1 : Impossible true (goalAt 219) 7 state219_1.toFinset :=
  node_ok cuts219 [] 0x40024c24216060c24240024981840024981840024c2424002c82424002498181606082424002c98181490852424002cc24234300d0c04002c981834300d0c04002cc2421490850c0400245818242009080400244a0a34300d0c040024581834300d0c0400244a0a2420090c04002c9818129084a424002cc24232300c8c04002c981832300c8c04002cc2421290848c040024581822200888040024501032300c8c040024581832300c8c04002450102220088c0400181a0a32300c8c040018d0c040018d0c0400181a0a4001c120a40018d0c032300c8c040004810310500414040004c24230700c1c040004810330700c1c040004c2421050043c040004410320600818040004581830700c1c040004410330700c1c04000458182060083c040004110330700c1c040004d0c006460d0c040004110306460191840004d0c030700c1c040004090330700c1c040004c8c006460c8c040004090306460191840004c8c030700c1c040000c24206860c24240000981830b00c2c040000c24230b00c2c0400009818068601a18400004a0a20a00828040000581830b00c2c0400004a0a30b00c2c040000581820a0082c040000524230b00c2c040000d0c006860d0c040000524206860504240000d0c030b00c2c0400004a4230b00c2c040000c8c006860c8c0400004a4206860484240000c8c030b00c2c0400010000400044342 (by decide +kernel)

def state219_2 : List Sig := [0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 0,input 1,input 3,input 4,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude219_2 : Impossible true (goalAt 219) 7 state219_2.toFinset :=
  node_ok cuts219 [] 0xc24216060c24226061000926060c2424002c824226060581820908981814908524230908d0c034300981834300d0c030908524214300581824200908012828d0c034300581834300d0c0128289080243009818129084a4230908c8c032300981832300c8c0309084a4212300581822200888014040c8c032300581832300c8c0140408880223001a0a32300c8c0343010006343001a0a4001c120a34300c8c032300c2424002cc24226061000026060c2424002cc242260610000260604a0a400244a0a160610000160604a0a400244a0a1606100001606052424001c52423430100003430052424001c5242343010000343004a42400184a42323010000323004a42400184a4232301000032301000040004c2c020c0c434210d08c24240004c24220c0d000b2080cc24210d08434210c0c0b0a02c28581810d08434210c0c434210d08581802c28581804c0c434210d08d0c040004d0c004c0d00070480cd0c010d08d0c002c0c434210d08c8c002c28c8c002c0c0b0a02c28c8c010d08c8c040001000040001000110d08434240001000010509000040000c1c03090900053090898184002c981830909000b30908981840014981812829000412828581840024581812829000912828581840010581814909000314908d0c04001cd0c014909000714908d0c04000cd0c012909000212908c8c040018c8c012909000612908c8c040008c8c0 (by decide +kernel)

def state219_3 : List Sig := roots 219
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude219_3 : Impossible true (goalAt 219) 8 state219_3.toFinset :=
  node_ok cuts219 [⟨state219_0,exclude219_0⟩,⟨state219_1,exclude219_1⟩,⟨state219_2,exclude219_2⟩] 0x40014c24216060c24240014981840014981840014c24240014824240014981816060824240014981814908524240014c24234300d0c040014981834300d0c040014c2421490850c04000c58182420090804000c4a0a34300d0c04000c581834300d0c04000c4a0a2420090c0400149818129084a4240014c24232300c8c040014981832300c8c040014c2421290848c040008581822200888040008501032300c8c040008581832300c8c04000850102220088c0400081a0a32300c8c040008d0c040008d0c0400081a0a4000c120a40008d0c032300c8c040014c24206860c24240014981830b00c2c040014c24230b00c2c0400149818068601a18400104a0a20a00828040010581830b00c2c0400104a0a30b00c2c040010581820a0082c04000c524230b00c2c04000cd0c006860d0c04000c52420686050424000cd0c030b00c2c0400084a4230b00c2c040008c8c006860c8c0400084a4206860484240008c8c030b00c2c040014830310d08434240014c24230700c1c040014830330700c1c040014c24210d08434240010430320600818040010581830700c1c040010430330700c1c04001058182060081c04000c130330700c1c04000cd0c006460d0c04000c13030646019184000cd0c030700c1c0400080b0330700c1c040008c8c006460c8c0400080b0306460191840008c8c030700c1c040002000130700c1c040004c2c010d08c2c08000a000010d08434240000c2c030700c1c0 (by decide +kernel)

theorem lower219 : Claim 219 9 :=
  fromSearch 67 (by decide +kernel) exclude219_3

theorem lower113 : Claim 113 5 :=
  fromLift 5 32 4 lower81 (by decide +kernel)

theorem lower105 : Claim 105 5 :=
  fromLift 5 32 3 lower73 (by decide +kernel)

def rule121_0 : {c : Cut // CutGood (goalAt 121) c} :=
  ruleFor 121 lower113 none (by decide +kernel)

def rule121_1 : {c : Cut // CutGood (goalAt 121) c} :=
  ruleFor 121 lower105 none (by decide +kernel)

def rule121_2 : {c : Cut // CutGood (goalAt 121) c} :=
  ruleFor 121 lower89 none (by decide +kernel)

def rule121_3 : {c : Cut // CutGood (goalAt 121) c} :=
  ruleFor 121 lower57 none (by decide +kernel)

def cuts121 : Cuts (goalAt 121) := [rule121_0,rule121_1,rule121_2,rule121_3]

def state121_0 : List Sig := roots 121
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude121_0 : Impossible true (goalAt 121) 6 state121_0.toFinset :=
  node_ok cuts121 [] 0x4000870300e06070304000858184000858184000870304000c50304000858180e06050304000470300440470304000448081c18070604000470301c18070604000448080440448184000438181410050404000428081c18070604000438181c18070604000428081410050604000058180e0c038304000070301a18068604000058181a18068604000070300e0c038304000038181210048404000021011a18068604000038181a18068604000021011210048604000100001a18068604000070600e0c070604000100000e0c038304000070601a18068604000c41010c4c031304000c70301858061604000c41011858061604000c70300c4c031304000821011050041404000838181858061604000821011858061604000838181050041604000411011858061604000470600c4c070604000411010c4c03130400047060185806160400000901185806160400006860064606860400000901064601918400006860185806160 (by decide +kernel)

theorem lower121 : Claim 121 7 :=
  fromSearch 3 (by decide +kernel) exclude121_0

def cuts99 : Cuts (goalAt 99) := []

def state99_0 : List Sig := roots 99
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude99_0 : Impossible true (goalAt 99) 3 state99_0.toFinset :=
  node_ok cuts99 [] 0x8c0c624218908224208880626018980226018908626018980210308480616018580216010d08616018580434218580626010d086160 (by decide +kernel)

theorem lower99 : Claim 99 4 :=
  fromSearch 85 (by decide +kernel) exclude99_0

def rule107_0 : {c : Cut // CutGood (goalAt 107) c} :=
  ruleFor 107 lower105 none (by decide +kernel)

def rule107_1 : {c : Cut // CutGood (goalAt 107) c} :=
  ruleFor 107 lower106 none (by decide +kernel)

def rule107_2 : {c : Cut // CutGood (goalAt 107) c} :=
  ruleFor 107 lower99 none (by decide +kernel)

def rule107_3 : {c : Cut // CutGood (goalAt 107) c} :=
  ruleFor 107 lower73 none (by decide +kernel)

def rule107_4 : {c : Cut // CutGood (goalAt 107) c} :=
  ruleFor 107 lower43 none (by decide +kernel)

def cuts107 : Cuts (goalAt 107) := [rule107_0,rule107_1,rule107_2,rule107_3,rule107_4]

def state107_0 : List Sig := [0xffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffee,input 3,input 0,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude107_0 : Impossible true (goalAt 107) 4 state107_0.toFinset :=
  node_ok cuts107 [] 0xa028624218908224202c28434210d080b0a10d0861420840c434210d08484202c28434218580480a1210848420240c484218908220a121086860088806260189802260189086260189810003 (by decide +kernel)

def state107_1 : List Sig := [0xee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee,input 3,input 0,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude107_1 : Impossible true (goalAt 107) 4 state107_1.toFinset :=
  node_ok cuts107 [] 0x280a189086242089080b0a10d08434202c28434218508210310d0869601a1800b0a1a18028201a18068600a98048401a18068601298022201898062600898062421898062600a0286160185804342189804842 (by decide +kernel)

def state107_2 : List Sig := [0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 0,input 3,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude107_2 : Impossible true (goalAt 107) 5 state107_2.toFinset :=
  node_ok cuts107 [⟨state107_0,exclude107_0⟩,⟨state107_1,exclude107_1⟩] 0x100030a8282a0a128286242189090003189086242128282a0a089084a0a0a08028201040c68601a1804a0a1a18068601040c28200a1802a0a129084a421890868601a1802a0a1a1806860189084a4212180410302c280b0a12828434210d08410310d084342128280b0a02c28210310d0843421890900011850821034000c210318908434210d08090310d0843421a1800b0a1a180090302c280b0a1a18043421a18100004000061601282822200888048081898062601282862601898048080888022601890900031890828081898062601890862601898028084000c280a1290862601898068608000468601290a0000121086860189806260 (by decide +kernel)

def state107_3 : List Sig := [0x5544554455445544554455445544554455445544554455445544554455445544,input 0,input 3,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude107_3 : Impossible true (goalAt 107) 4 state107_3.toFinset :=
  node_ok cuts107 [] 0x280a18908624208908480a1210848420240c484218908220a12108212018580616008d80414018580616010d8061601a58009031858022201898062600898062421898062600840c62601a1804842189804342 (by decide +kernel)

def state107_4 : List Sig := [0xffccffccffccffccffccffccffccffccffccffccffccffccffccffccffccffcc,input 3,input 0,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude107_4 : Impossible true (goalAt 107) 5 state107_4.toFinset :=
  node_ok cuts107 [⟨state107_0,exclude107_0⟩,⟨state107_3,exclude107_3⟩] 0x100030a028280a12028624218909000318908624212028280a08908430308480212012028616018580430318580616012028212008580230310d08434218908616018580230318580616018908434210d080903185806160121080b0a12108090302c280b0a12108616018582000118580616018980434218982000010d08434218980616018580480a0240c480a10c0c484212108480a12108484210c0c09030240c280a12108484218909000218908280a4000c220a1890848421210900004000068601202822200888041011898062601202862601898041010888022601890900031890821011898062601890862601898021014000c2103 (by decide +kernel)

def state107_5 : List Sig := [0xffaaffaaffaaffaa0000000000000000ffaaffaaffaaffaa,input 0,input 3,input 1,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude107_5 : Impossible true (goalAt 107) 4 state107_5.toFinset :=
  node_ok cuts107 [] 0x18908626018980280a1898068601210862601290868601a180486010d08616018580434218580626010d08616018580686002c2861600a82862420a82862421202862601282862600a180686012828686008580616002c286160 (by decide +kernel)

def state107_6 : List Sig := [0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 0,input 3,input 1,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude107_6 : Impossible true (goalAt 107) 5 state107_6.toFinset :=
  node_ok cuts107 [⟨state107_0,exclude107_0⟩,⟨state107_5,exclude107_5⟩] 0x2a0a1890862420890822201898062600898062421898062600a0286260024040903189806260400020000189804a0a10c0c4a0a02c0c2a0a189082a0a18908686002c284a0a10c0c0b0a02c28624208c0c624202420626002c28626002c0c0b0a4000461601282a00011282900040a82862420a8286242 (by decide +kernel)

def state107_7 : List Sig := roots 107
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude107_7 : Impossible true (goalAt 107) 6 state107_7.toFinset :=
  node_ok cuts107 [⟨state107_2,exclude107_2⟩,⟨state107_4,exclude107_4⟩,⟨state107_6,exclude107_6⟩] 0x4001100040a8282a0a400104a0a189086242400110003189086242400104a0a0a8282242400104a0a0a08028204001043031a1806860400104a0a1a18068604001043030a08028604000c2a0a129084a424000862421a18068604000c2a0a1a1806860400086242129084860400004a0a088802220400004808189806260400004a0a1898062604000048080888022604000062424000c624240000280818980626040000624218980626040000280840000280a400004a42189806260400006860400006860400004a42800044842400006860189806260400104303084802120400104a0a185806160400104303185806160400104a0a0848021604000c230310d0843424000462421858061604000c230318580616040004624210d084342400080b0318580616040004686002c286860800080b0302c280b0a40004686018580616040001000018580616040000626010d08626040002000010d084342400006260185806160 (by decide +kernel)

theorem lower107 : Claim 107 7 :=
  fromSearch 83 (by decide +kernel) exclude107_7

theorem lower115 : Claim 115 6 :=
  fromLift 6 2 68 lower113 (by decide +kernel)

def rule123_0 : {c : Cut // CutGood (goalAt 123) c} :=
  ruleFor 123 lower121 none (by decide +kernel)

def rule123_1 : {c : Cut // CutGood (goalAt 123) c} :=
  ruleFor 123 lower122 none (by decide +kernel)

def rule123_2 : {c : Cut // CutGood (goalAt 123) c} :=
  ruleFor 123 lower107 none (by decide +kernel)

def rule123_3 : {c : Cut // CutGood (goalAt 123) c} :=
  ruleFor 123 lower91 none (by decide +kernel)

def rule123_4 : {c : Cut // CutGood (goalAt 123) c} :=
  ruleFor 123 lower115 none (by decide +kernel)

def rule123_5 : {c : Cut // CutGood (goalAt 123) c} :=
  ruleFor 123 lower59 none (by decide +kernel)

def rule123_6 : {c : Cut // CutGood (goalAt 123) c} :=
  ruleFor 123 lower43 none (by decide +kernel)

def rule123_7 : {c : Cut // CutGood (goalAt 123) c} :=
  ruleFor 123 lower122 (some (1,input 3,input 6)) (by decide +kernel)

def rule123_8 : {c : Cut // CutGood (goalAt 123) c} :=
  ruleFor 123 lower57 none (by decide +kernel)

def rule123_9 : {c : Cut // CutGood (goalAt 123) c} :=
  ruleFor 123 lower83 none (by decide +kernel)

def cuts123 : Cuts (goalAt 123) := [rule123_0,rule123_1,rule123_2,rule123_3,rule123_4,rule123_5,rule123_6,rule123_7,rule123_8,rule123_9]

def state123_0 : List Sig := [0xffffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00,input 3,input 6,input 0,input 1,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude123_0 : Impossible true (goalAt 123) 7 state123_0.toFinset :=
  node_ok cuts123 [] 0x100050e06038181606062421890900091890862421606038180e061000908c0c23034000c62421890900091890862424000c230308c0c38181490852421890870601c18038181c18070601890852421418058180682858181282870601c18058181c1807060128281a0a12061000604c0c13034000870601c18100061c180706040008130304c0c62420686062420e06062601898062421898062600e0601a180686052421898062601c18032301c18052420c8c050421c1806260189804a0a0c8c03230160606260189804a0a1898062601606032300c8c04a421898062601a1801a181a1804a420686048421a18062601898100080c8c032304000062601898100081898062604000032300c8c0230310d08434218908616018580230318580616018908434210d0813031858061601c18031301c18013030c4c031301c180616018581000818580616018980434218981000710d0843421898061601858100050c4c031301606061601858100071858061601606031300c4c100041858061601a18019181a18100070646019181a18061601858100070c4c031304000461601858100071858061604000431300c4c100044001070300e0604a421290862421a18068600e06068601a18062421290848600682868601a18070604001070600682900060682870601a18068601606100051606100041a18068604001100040a1810004400143830 (by decide +kernel)

def state123_1 : List Sig := roots 123
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude123_1 : Impossible true (goalAt 123) 8 state123_1.toFinset :=
  node_ok cuts123 [⟨state123_0,exclude123_0⟩] 0x4000c70300e06070304000c58181890862424000c70301890862424000c58180e0605030400087030068287030400084a0a1c18070604000870301c1807060400084a0a0682848184000c38181490852424000c62421c18070604000c38181c18070604000c62421490850604001458180e0c038304001070301a18068608000058181a18068604001070300e0c038304000c3818129084a424000c62421a18068604000c38181a18068604000c6242129084860400081a0a1a18068604000870600e0c07060400081a0a0e0c038304000870601a1806860400004a0a0c8c03230400007030189806260400004a0a1898062604000070300c8c03230400006242068606242400003818189806260400006242189806260400003818068601a184000052421898062604000070600c8c070604000052420c8c05042400007060189806260400004a42189806260400006860068606860400004a420686048424000068601898062604000443030c4c031304000470301858061604000443031858061604000470300c4c0313040004230310d08434240004624218580616040004230318580616040004624210d0843424000413031858061604000470600c4c070604000413030c4c03130400047060185806160400040b03185806160400046860064606860400040b0306460191840004686018580616040001000018580616040000626010d08626040001000110d084342400006260185806160 (by decide +kernel)

theorem lower123 : Claim 123 9 :=
  fromSearch 67 (by decide +kernel) exclude123_1

theorem lower233 : Claim 233 6 :=
  fromLift 6 32 3 lower201 (by decide +kernel)

theorem lower241 : Claim 241 6 :=
  fromLift 6 32 4 lower209 (by decide +kernel)

theorem lower227 : Claim 227 5 :=
  fromLift 5 32 85 lower195 (by decide +kernel)

def rule251_0 : {c : Cut // CutGood (goalAt 251) c} :=
  ruleFor 251 lower250 none (by decide +kernel)

def rule251_1 : {c : Cut // CutGood (goalAt 251) c} :=
  ruleFor 251 lower187 none (by decide +kernel)

def rule251_2 : {c : Cut // CutGood (goalAt 251) c} :=
  ruleFor 251 lower249 none (by decide +kernel)

def rule251_3 : {c : Cut // CutGood (goalAt 251) c} :=
  ruleFor 251 lower243 none (by decide +kernel)

def rule251_4 : {c : Cut // CutGood (goalAt 251) c} :=
  ruleFor 251 lower235 none (by decide +kernel)

def rule251_5 : {c : Cut // CutGood (goalAt 251) c} :=
  ruleFor 251 lower219 none (by decide +kernel)

def rule251_6 : {c : Cut // CutGood (goalAt 251) c} :=
  ruleFor 251 lower123 none (by decide +kernel)

def rule251_7 : {c : Cut // CutGood (goalAt 251) c} :=
  ruleFor 251 lower233 none (by decide +kernel)

def rule251_8 : {c : Cut // CutGood (goalAt 251) c} :=
  ruleFor 251 lower241 none (by decide +kernel)

def rule251_9 : {c : Cut // CutGood (goalAt 251) c} :=
  ruleFor 251 lower211 none (by decide +kernel)

def rule251_10 : {c : Cut // CutGood (goalAt 251) c} :=
  ruleFor 251 lower185 none (by decide +kernel)

def rule251_11 : {c : Cut // CutGood (goalAt 251) c} :=
  ruleFor 251 lower121 none (by decide +kernel)

def rule251_12 : {c : Cut // CutGood (goalAt 251) c} :=
  ruleFor 251 lower235 (some (1,input 1,input 3)) (by decide +kernel)

def rule251_13 : {c : Cut // CutGood (goalAt 251) c} :=
  ruleFor 251 lower250 (some (1,input 1,input 3)) (by decide +kernel)

def rule251_14 : {c : Cut // CutGood (goalAt 251) c} :=
  ruleFor 251 lower242 none (by decide +kernel)

def rule251_15 : {c : Cut // CutGood (goalAt 251) c} :=
  ruleFor 251 lower209 none (by decide +kernel)

def rule251_16 : {c : Cut // CutGood (goalAt 251) c} :=
  ruleFor 251 lower169 none (by decide +kernel)

def rule251_17 : {c : Cut // CutGood (goalAt 251) c} :=
  ruleFor 251 lower105 none (by decide +kernel)

def rule251_18 : {c : Cut // CutGood (goalAt 251) c} :=
  ruleFor 251 lower227 none (by decide +kernel)

def rule251_19 : {c : Cut // CutGood (goalAt 251) c} :=
  ruleFor 251 lower203 none (by decide +kernel)

def rule251_20 : {c : Cut // CutGood (goalAt 251) c} :=
  ruleFor 251 lower250 (some (1,input 1,input 4)) (by decide +kernel)

def rule251_21 : {c : Cut // CutGood (goalAt 251) c} :=
  ruleFor 251 lower171 none (by decide +kernel)

def rule251_22 : {c : Cut // CutGood (goalAt 251) c} :=
  ruleFor 251 lower187 (some (1,input 3,input 4)) (by decide +kernel)

def rule251_23 : {c : Cut // CutGood (goalAt 251) c} :=
  ruleFor 251 lower107 none (by decide +kernel)

def rule251_24 : {c : Cut // CutGood (goalAt 251) c} :=
  ruleFor 251 lower250 (some (1,input 3,input 4)) (by decide +kernel)

def rule251_25 : {c : Cut // CutGood (goalAt 251) c} :=
  ruleFor 251 lower178 none (by decide +kernel)

def cuts251 : Cuts (goalAt 251) := [rule251_0,rule251_1,rule251_2,rule251_3,rule251_4,rule251_5,rule251_6,rule251_7,rule251_8,rule251_9,rule251_10,rule251_11,rule251_12,rule251_13,rule251_14,rule251_15,rule251_16,rule251_17,rule251_18,rule251_19,rule251_20,rule251_21,rule251_22,rule251_23,rule251_24,rule251_25]

def state251_0 : List Sig := [0xffffffee00000000ffffffee00000000ffffffee00000000ffffffee,input 0,input 4,input 1,input 3,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude251_0 : Impossible true (goalAt 251) 6 state251_0.toFinset :=
  node_ok cuts251 [] 0x30908b0302090882421a180e8e03a38068c02a280e8e03a380a8c03a380f0e00e0c0e8e018980e2e038b8062c028a80e2e038b80a2c038b80e8e012108e2e038b80f0e014108e2e01c180f0e03c38070c02c280f0e03c380b0c018580e1e03878061c028680e1e038780a1c038780e8e006460e1e038780e2e010d08e1e038780f0e00c4c0e1e0189089030309086242140c0624218908703032380e8e012908e8e030b80e2e018908e2e034380f0e014908f0e030780e1e010d08e1e0 (by decide +kernel)

def state251_1 : List Sig := [0xffffffeeffffffee0000000000000000ffffffeeffffffee,input 0,input 4,input 1,input 3,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude251_1 : Impossible true (goalAt 251) 6 state251_1.toFinset :=
  node_ok cuts251 [] 0x18908c242240c062421a180e8e03a38068a032300e8e03a380c8e03a380f0e00e0c0e8e018980e2e038b8062a030b00e2e038b80c2e038b80e8e012108e2e038b80f0e014108e2e01c180f0e03c38070a034300f0e03c380d0e018580e1e03878061a030700e1e038780c1e038780e8e006460e1e038780e2e010d08e1e038780f0e00c4c0e1e02090882422c0c0c242140c062421c0c062422a380e8e00e0c0e8e028b80e2e00c8c0e2e02c380f0e01c0c0f0e028780e1e00c4c0e1e0 (by decide +kernel)

def state251_2 : List Sig := [0xffffffeeffffffeeffffffeeffffffee,input 0,input 4,input 1,input 3,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude251_2 : Impossible true (goalAt 251) 6 state251_2.toFinset :=
  node_ok cuts251 [] 0x1c0c062421890850302a280e8e03a380a8e032300e8e03a380c8e03a380f0e00e0c0e8e028a80e2e038b80a2e030b00e2e038b80c2e038b80e8e012108e2e038b80f0e014108e2e02c280f0e03c380b0e034300f0e03c380d0e028680e1e038780a1e030700e1e038780c1e038780e8e006460e1e038780e2e010d08e1e038780f0e00c4c0e1e020908824230908b03018908903018908c2421a380e8e012908e8e018b80e2e030908e2e01c380f0e014908f0e018780e1e010d08e1e0 (by decide +kernel)

def state251_3 : List Sig := [0xffffffeeffffffeeffffffeeffffffeeffffffeeffffffeeffffffeeffffffee,input 0,input 4,input 1,input 3,input 5,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude251_3 : Impossible true (goalAt 251) 7 state251_3.toFinset :=
  node_ok cuts251 [⟨state251_0,exclude251_0⟩,⟨state251_1,exclude251_1⟩,⟨state251_2,exclude251_2⟩] 0x30908b03020908824218908c242240c062421c0c0624218908503012908c242240604a420e0c04a421290838301290862420e0c04a421290852420e0c04a423a380c2422c0c0c2420c8c032301c0c0480a0c8c062420c8c06242068604a420e0c048421210852420c8c0504214108e2e014908c2422c0c052421c0c052421490848181490862420a06052423c380434230908820310d08313010d0843420c4c0434218908313010d08434212908191810d08313010d08434210508434214908313010d08e1e03090a00023090900061c0c200011c0c100011890a0000189090005 (by decide +kernel)

def state251_4 : List Sig := [0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,0x5555554455555544555555445555554455555544555555445555554455555544,input 4,input 3,input 5,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude251_4 : Impossible true (goalAt 251) 6 state251_4.toFinset :=
  node_ok cuts251 [] 0x30908b03020908824218908c242240c062421c0c0624218908503012908c242240604a420e0c04a421290838301290862420e0c04a421290852420e0c04a4214908c2422c0c052421c0c052421490848181490862420a060524210d0881033050843421c0c0434210d080b0a10d0821031850843423a380e8e01250843423c380f0e014508434238b80e1e010d08e1e018580e1e03878063e028680e1e038780a3e030700e1e038780c3e038780e9e012108e1e038780f1e014108e1e0 (by decide +kernel)

def state251_5 : List Sig := [0x5555554455555544555555445555554455555544555555445555554455555544,input 0,input 4,input 1,input 3,input 5,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude251_5 : Impossible true (goalAt 251) 7 state251_5.toFinset :=
  node_ok cuts251 [⟨state251_4,exclude251_4⟩] 0xc2422c0c08242209086242309089030189087030189086242140c04a42309089018129083830129084a420e0c04a42189083830129084a4214908383012908c2422c0c0c2420c8c032301c0c0480a0c8c062420c8c06242068604a420e0c048421210852420c8c0504214108524230908b03014908703014908524212060524218908281814908616038780e1e018780a1a038780e1e028780c1c038780e1e030780e1e03a7800b0338780e1e038f82000038780e1e03c780130338780c24220c0cc24220c0c703010c0c703010c0c624208c0c624208c0ce8e03a3804a4202c0ce2e038b80323040000f0e03c380524204c0c4342 (by decide +kernel)

def state251_6 : List Sig := [0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 0,0xffffffccffffffccffffffccffffffccffffffccffffffccffffffccffffffcc,input 4,input 3,input 5,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude251_6 : Impossible true (goalAt 251) 7 state251_6.toFinset :=
  node_ok cuts251 [⟨state251_4,exclude251_4⟩] 0xc2422c0c08242209086242309089030189087030189086242140c04a42309089018129083830129084a420e0c04a42189083830129084a4214908383012908e8e014908c2422c0c052421c0c052421490848181490862420a06052423c380c24220404c2422040c70301040470301040c62420840462420840c434230908820310d080b0a10d0843421c0c0434218908220310d084342125080b0a10d08434214508110310d0a000010d08434210508e1e030908b0303090832300c8c07030120283230189083230189081a1812908383012108484214908323014108504238b80e2e00c8c10000 (by decide +kernel)

def state251_7 : List Sig := [0xffffffccffffffccffffffccffffffccffffffccffffffccffffffccffffffcc,input 4,input 1,input 3,input 0,input 5,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude251_7 : Impossible true (goalAt 251) 8 state251_7.toFinset :=
  node_ok cuts251 [⟨state251_3,exclude251_3⟩,⟨state251_5,exclude251_5⟩,⟨state251_6,exclude251_6⟩] 0xc2421c0c0c2422c0c100112c0c0c2424004482422c0c0703020908b03018908624230909001130908b0304004490303090862421890870300e0607030160606242189087030189086242160603818140c0830318580616030908e1e038780830338780e1e030908616018780430328680a1a01c0c0e1e038780430338780e1e01c0c0a1a028780230330700c1c018908e1e038780230338780e1e018908c1c0307800b0338780e1e0129081918129080b0306460191812908e1e038781000738780e1e00c8c0434210d0a000210d0843420c8c0e1e038780130338780e1e01490831301490813030c4c0313014908e1e038782000138780e1e040000434210d0a000010d08434240000e1e0387809818129084a42309090008309089818400449018309084a421290858180e0c038301c0c04a42129085818129084a421c0c038300e0c03818129084a421890838301890838180e0c03830189084a42129081a0a129084a42149083830149081a0a0e0c03830149084a421290900074001ce8e030908323030908b0304001cb03030909001130908b0300c8c032301282832300c8c070304001c70301282900101202870300c8c03230189081a181890838180c8c03230189083230189083818068601a18129083230129083830068603830129081a181210838300c8c048421490900071490900070c8c032301490832301410900074001c50424001d001238b80b03014908524230909000730908b03040044b030309085242149087030068287030128285242149087030149085242128281a0a1206038181490852421890900071890838184003c281818908524214909000740020f0e03090900063090881014004481013090900113090881014001881011c0c100011c0c041014004041011c0c100101c0c041014000441011890900051890821014003c210118909000f189082101400142101 (by decide +kernel)

def state251_8 : List Sig := [0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,0xffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaa,0xffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00,0xffccffccffccffccffccffccffccffccffccffccffccffccffccffccffccffcc,input 5,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude251_8 : Impossible true (goalAt 251) 6 state251_8.toFinset :=
  node_ok cuts251 [] 0x30908b03020908824218908c242240c062421c0c0624218908503030908b0303090838300e0c070301406038301890838301890821033a380e8e012908110310d08383010d08414212908c2422c0c04a421c0c04a421290809031290862420e0604a4210d08c2422c0c043421c0c0434210d08481810d0862420a06043423c380f0e002c28434230908b0303090831300c4c0703012028313018908313018908191838b80e2e006460313012908313012108484238780e1e010d090007 (by decide +kernel)

def state251_9 : List Sig := [0xffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaa,input 0,0xffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00,0xffccffccffccffccffccffccffccffccffccffccffccffccffccffccffccffcc,input 1,input 5,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude251_9 : Impossible true (goalAt 251) 7 state251_9.toFinset :=
  node_ok cuts251 [⟨state251_8,exclude251_8⟩] 0x30908b03020908824218908c242240c062421c0c0624218908503030908b03030908b030068607030120287030189083218189081a1838b804a4206860484212108120a068601a184001cc2422c0c0c2420e0c038301c0c050180e0c062420e0c0624208404e8e03a3804a4204404120a0e0c038300a0c04a4230908b030129087030129084a4202c0c4a421890838181290831303090883033090831301c0c043030c4c019181890831301890831300686200000c4c031300e0c019180c4c00b0312908313012908e1e02c0c0c2422c0c0c2421c0c04a0a1c0c048180e06062420a06062423c380f0e0048284a42 (by decide +kernel)

def state251_10 : List Sig := [0xffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffee,input 0,0xffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00,input 4,input 1,input 5,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude251_10 : Impossible true (goalAt 251) 7 state251_10.toFinset :=
  node_ok cuts251 [] 0xc2422c0c08242209086242309089030189087030189086242140c0c2422c0c0c2422c0c01a181c0c0480a1c0c062420c860624206860120a068601a18400204a4206860484212108e2e02c0c0c2422c0c0c2421c0c04a0a1c0c048180e06062420a06062423c3804a4230908b030129087030129084a4202c0c4a4218908381812908434230908820310d08191810d0843421c0c0434218908220310d08191810d08434210508434206460191810d08434212908191810d08e1e030908b0303090838300e0c070301406038301890838301890900130482838300e0c028303a380e8e0129090004 (by decide +kernel)

def state251_11 : List Sig := [0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 0,0xffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00,input 4,0xffccffccffccffccffccffccffccffccffccffccffccffccffccffccffccffcc,input 5,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude251_11 : Impossible true (goalAt 251) 7 state251_11.toFinset :=
  node_ok cuts251 [⟨state251_8,exclude251_8⟩] 0x30908b03020908824218908c242240c062421c0c0624218908503030908b0303090838300e0c070301406038301890838301890821030482838300e0c028303a380e8e01290900022c0c0c2422c0c0c2421c0c04a0a1c0c048180e06062420a06062423c3804a4230908b030129087030129084a420240c4a4218908381812908434230908820310d080b0a10d0843421c0c0434218908220310d09000810d0843421050843420482a000010d084342125080b0a10d08e1e030908b03030908b030068607030120287030189083218189081a1838b80e2e0068603830048281a18068610007129081a18121084842 (by decide +kernel)

def state251_12 : List Sig := [0xffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00,input 4,0xffccffccffccffccffccffccffccffccffccffccffccffccffccffccffccffcc,input 1,input 0,input 5,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude251_12 : Impossible true (goalAt 251) 8 state251_12.toFinset :=
  node_ok cuts251 [⟨state251_9,exclude251_9⟩,⟨state251_10,exclude251_10⟩,⟨state251_11,exclude251_11⟩] 0x30908703030908b03040044b03030909001120908b0301c0c082422c0c0624218908c24240024c2422c0c10011240c0c2421890862421c0c038181c0c058181890862421c0c062421890858180e060503020c0c616018580c24238780e1e020c0ce1e038780c2421858061e010c0ca1a028680703038780e1e010c0ce1e038780703028680a1e008c0cc1c030700624238780e1e008c0ce1e038780624230700c1e04001ce1e0387801a1810d08434280008434210d081a1838780e1e040020e1e038780383010d08434280004434210d08383038780e1e04001ce1e038780120a0c4c031308000031300c4c0120a38780e1e002c0ce1e0387804a420c4c04a4202c0c31300c4c04a4238780e1e0309081a1830908b0304001cb03030909001130908b03006860b030128281a180686070304001c7030128290010120287030068607030189081a18189083818400243218189090009189083818068601a184000d000338b80120a4001c120a4001c1a1806860120a068601a184001d0007400204a42400484a42400081a18068604a4206860484240009000712108c2420e0c0c2422c0c100082c0c0c24240044c2422c0c038300e0c058180e0c038301c0c100081c0c058184004050181c0c038300e0c062424004c62420840438300e0c062420e0c0624208405001308404120a40010120a4002038300e0c0120a0e0c038304001d00040a0c04a4240010e8e04000838303a3804a420e0c04a4240009000440008b03004828b03030909000730908b03040044b03030908120a30908703004828703012829000712828703040040703012828120a12060381804828381818909000918908381840024281818908120a1890900034000cf0e02c0c04a4212908c24240044c2422c0c100112c0c0c242129084a421c0c00b031c0c04303129084a421c0c04a4212908430302c0c0b030e0604a421290862424002462420e06100090e0606242129084a42 (by decide +kernel)

def state251_13 : List Sig := [0xffccffccffccffccffccffccffccffccffccffccffccffccffccffccffccffcc,input 1,input 3,input 0,input 4,input 5,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude251_13 : Impossible true (goalAt 251) 9 state251_13.toFinset :=
  node_ok cuts251 [⟨state251_7,exclude251_7⟩,⟨state251_12,exclude251_12⟩] 0x40028c2421c0c0c24240028b03040028b03040028c2424002c824240028b0301c0c082424002cb0301890862424002cc2424002cc2424002cb0304002c90304002cc2421890862424002870300e06070304002858181890862424002870301890862424002858180e06050304002cb0301c18070604002cc2423c380f0e04002cb0303c380f0e04002cc2421c18070e04002870302c280b0a0400284a0a3c380f0e04002870303c380f0e0400284a0a2c280b0e040024381834300d0c04002462423c380f0e04002438183c380f0e040024624234300d0e04002c83031858061604002cc24238780e1e04002c830338780e1e04002cc2421858061e040028430328680a1a040028703038780e1e040028430338780e1e040028703028680a1e040024230330700c1c040024624238780e1e040024230338780e1e040024624230700c1e04001c130338780e1e040038f0e00c4c0f0e04003413030c4c031304001cf0e038780e1e04000c0b0338780e1e04000c4a42064604a424000c0b030646019184000c4a4238780e1e040009000238780e1e0400081a1810d08434240009000d10d084342400081a1838780e1e040021000838780e1e040021000010d08434240021000d10d08434240021000038780e1e04000c9818129084a424000cc2424000cc2424000c98184002c98184000cc242129084a424000c581802c0c58184000c7030129084a424000c5818129084a424000c703002c0c70304000c3818129084a424000c62424000c62424000c38184002438184000c6242129084a424000c1a0a129084a424000cf0e04000cf0e04000c1a0a80004120a4000cf0e012908f0e040009000240008e8e040008c24206860c24240008b03040008b03040008c2424002cc24240008b03006860b030400084a0a068601a18400087030400087030400084a0a40028480a400087030068607030400086242068606242400083818400083818400086242400246242400083818068601a1840008524240030524240008f0e006860f0e040008524206860524240008f0e040008f0e0400084a424000c4a42400090002068601a184000900024000848424000900024000ce2e04002cc24240018c2424002cb0304002cb0304002cc2424002cc2424002cb03040018b0304002858184000458184002870304002870304002858184002858184002870304000470304002462424001462424002421014002421014002462424002462424002421014001421014001c524240010524240020f0e040020f0e04002052428000052424001cf0e040010f0e0 (by decide +kernel)

def state251_14 : List Sig := [0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc,input 1,input 4,input 0,input 3,input 5,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude251_14 : Impossible true (goalAt 251) 9 state251_14.toFinset :=
  node_ok cuts251 [⟨state251_7,exclude251_7⟩] 0x40028c2421c0c0c24240028b03040028b03040028c2424002c824240028b0301c0c082424004cb0301890862424004cc2424004cc2424004cb0304002c90304004cc2421890862424002870300e06070304002858181890862424002870301890862424002858180e06050304002c98181a18068604002cc2423a380e8e04002c98183a380e8e04002cc2421a18068e04002858182a280a8a04002870303a380e8e04002858183a380e8e04002870302a280a8e04004c381832300c8c04004c62423a380e8e04004c38183a380e8e04004c624232300c8e0400101a0a3a380e8e04001052420e0c05242400101a0a0e0c038304001052423a380e8e04001d00073a380e8e04001d0003129084a424001e0000129084a424001d00033a380e8e04002c83031858061604002cc24238780e1e04002c830338780e1e04002cc2421858061e040028430328680a1a040028703038780e1e040028430338780e1e040028703028680a1e04004c230330700c1c04004c624238780e1e04004c230338780e1e04004c624230700c1e0400200b0338780e1e040050e8e006460e8e0400500b0306460191840020e8e038780e1e040010130338780e1e04001052420c4c052424001013030c4c0313040010524238780e1e040009000238780e1e040008323010d08434240009001410d08434240008323038780e1e04001d000738780e1e04001d000010d0843424001d001410d0843424001d000038780e1e040010b03014908524240010c24240010c24240010b0304002cb03040010c242149085242400107030068287030400104a0a149085242400107030149085242400104a0a0682812424001038181490852424001062424001062424001038184004c381840010624214908524240009000240008f0e040008c2420c8c0c24240008b03040008b03040008c2424002cc24240008b0300c8c03230400084a0a0c8c03230400087030400087030400084a0a400284a0a4000870300c8c032304000862420686062424000838180c8c032304000862420c8c06242400083818068601a18400084a420c8c04a4240008e8e006860e8e0400084a42068604a4240008e8e00c8c0e8e04000852424001052424000900020c8c0323040009000240008504240009000240010e2e04002cc24240018c2424002c88084002c88084002cc2424002cc2424002c88084001888084002870304000470304002848084002848084002870304002870304002848084000448084004c62424001462424004c28084004c28084004c62424004c62424004c2808400142808 (by decide +kernel)

def state251_15 : List Sig := [0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,0xbbbbbbaabbbbbbaabbbbbbaabbbbbbaabbbbbbaabbbbbbaabbbbbbaabbbbbbaa,input 3,input 4,input 5,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude251_15 : Impossible true (goalAt 251) 6 state251_15.toFinset :=
  node_ok cuts251 [] 0x30908b03020908824218908c242240c062421c0c0624218908503014908c2422c0c052421c0c052421490848181490862420a060524212908c242240604a420e0c04a421290838301290862420e0c04a421290852420e0c04a4210d08c1422c0c043421c0c0434210d080b0a10d0861420e06043423c380f0e00440c43423a380e8e00e0c0434238780e1e010d08e2e018980e2e038b8062e028a80e2e038b80a2e030b00e2e038b80c2e038b80f2e014908e2e038b80eae012908e2e0 (by decide +kernel)

def state251_16 : List Sig := [0xbbbbbbaabbbbbbaabbbbbbaabbbbbbaabbbbbbaabbbbbbaabbbbbbaabbbbbbaa,input 0,input 1,input 3,input 4,input 5,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude251_16 : Impossible true (goalAt 251) 7 state251_16.toFinset :=
  node_ok cuts251 [⟨state251_15,exclude251_15⟩] 0xc2422c0c08242209086242309089030189087030189086242140c0524230908b030149087030149085242120605242189082818149084a42309089018129083830129084a420e0c04a42189083830129084a4214908383012908626038b80e2e018b80a2a038b80e2e028b80c2c038b80e2e030b80e2e03cb80524238b80e2e03ab804a4238b8031303090883033090831301c0c043030c4c0191818908313018908090814908313014908313012908191812908313038b82000038b80e1e02c0c0c2422c0c0c2421c0c04a0a1c0c04a0a0e06062420e06062423c380f0e004c0c52423a380e8e00e0c04a4240000e2e00c8c0e2e0 (by decide +kernel)

def state251_17 : List Sig := [0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 0,0x3333330033333300333333003333330033333300333333003333330033333300,input 3,input 4,input 5,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude251_17 : Impossible true (goalAt 251) 7 state251_17.toFinset :=
  node_ok cuts251 [⟨state251_15,exclude251_15⟩] 0xc2422c0c08242209086242309089030189087030189086242140c0524230908b030149087030149085242120605242189082818149084a42309089018129083830129084a420e0c04a42189083830129084a4214908383012908b03030908b03030908703012828703012828381818908381818908f0e03c381000814908e8e03a380383012908090a10d0a000010d09000038b80323038b80434230508810310d080b0a10d0843421c0c0434218508210310d08434214908120310d084342129080b0a10d08e1e018980e2e038b8062e028a80e2e038b80a2e030b00e2e038b80c2e038b80f2e014908e2e038b80eae012908e2e0 (by decide +kernel)

def state251_18 : List Sig := [0x3333330033333300333333003333330033333300333333003333330033333300,input 1,input 3,input 4,input 0,input 5,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude251_18 : Impossible true (goalAt 251) 8 state251_18.toFinset :=
  node_ok cuts251 [⟨state251_16,exclude251_16⟩,⟨state251_17,exclude251_17⟩] 0xc2421c0c0c2422c0c100112c0c0c2424004482422c0c0703020908b03018908624230909001130908b0304004490303090862421890870300e0607030160606242189087030189086242160603818140c0830318580616030908e1e038780830338780e1e030908616018780430328680a1a01c0c0e1e038780430338780e1e01c0c0a1a028780230330700c1c018908e1e038780230338780e1e018908c1c030780130338780e1e01490831301490813030c4c0313014908e1e0387800b0338780e1e0129081918129080b0306460191812908e1e038781000738780e1e038b80434238b82000110d08434238b80e1e038780b03014908524230909000730908b03040044b030309085242149087030068287030128285242149087030149085242128281a0a1206038181490852421890900071890838184003c2818189085242149089818129084a42309090008309089818400449018309084a421290858180e0c038301c0c04a42129085818129084a421c0c038300e0c03818129084a421890838301890838180e0c03830189084a42129081a0a129084a42149083830149081a0a0e0c03830149084a4212908c2421898062602c0c0e2e038b80c24238b80e2e02c0c0626018b804a0a28a80a2a01c0c0e2e038b804a0a38b80e2e01c0c0a2a028b80624230b00c2c00e060e2e038b80624238b80e2e00e060c2c030b80524238b80e2e04001d00073cb8052424001c52424001ce2e038b804a4238b80e2e00e0c100073ab804a42400204a420e0c0e2e038b80b03040018b03030909001130908b03040044b0303090900063090870304000470301282900101282870304004070301282900011282838184001438181890900121890838184003c381818909000518908313040000313038781001238780313080000313038781000038781000740008f0e01490900033c38100084000d000314909000214908383040008e8e01290900043a38038304001038301290900021290900124001c3230 (by decide +kernel)

def state251_19 : List Sig := [0xffffffccffffffccffffffccffffffccffffffccffffffccffffffccffffffcc,input 1,0xffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00,input 3,input 4,input 0,input 5,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude251_19 : Impossible true (goalAt 251) 8 state251_19.toFinset :=
  node_ok cuts251 [] 0x30908b03020908824218908c242240c062421c0c0624218908503018580e1e03878061e028680e1e038780a1e030700e1e038780c1e03878031300c4c0e1e038780383006460e1e03878031300c4c0e1e038780434210d08e1e038780434210d08e1e02c0c0c2422c0c0c2421c0c04a0a1c0c048180e06062420a06062421490900080e0c0c24224060c2420e0c070301406038300e06062420e0c062420682838300a0c04a424001cb03030908b03030908703010c0c703010c0c381818908381818909000230908b0303090832300c8c07030120283230189083230189081a180682832300c8c100080c8c038300686032304004832304001ce2e03090881013090881011c0c041011c0c04101189082101189082101 (by decide +kernel)

def state251_20 : List Sig := [0xffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00,input 3,input 4,input 0,input 1,input 5,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude251_20 : Impossible true (goalAt 251) 9 state251_20.toFinset :=
  node_ok cuts251 [⟨state251_7,exclude251_7⟩,⟨state251_12,exclude251_12⟩,⟨state251_18,exclude251_18⟩,⟨state251_19,exclude251_19⟩] 0x4005cc2421c0c0c2424005cb0304005cb0304005cc2424005c82424005cb0301c0c082424004cb0301890862424004cc2424004cc2424004cb0304005c90304004cc2421890862424004c70300e06070304004c58181890862424004c70301890862424004c58180e06050304005cc2421898062604005cb03038b80e2e04005cc24238b80e2e04005cb0301898062e0400544a0a28a80a2a04001c703038b80e2e0400404a0a38b80e2e040054703028a80a2e04004c624230b00c2c04004c381838b80e2e04004c624238b80e2e04004c381830b00c2e0400101a0a38b80e2e04001100080c8c03230400101a0a0c8c0323040011000438b80e2e04000d000338b80e2e04000c38300686038304000e0001068601a184000c383038b80e2e04004a000238b80e2e04001d00020c8c032308000e00000c8c032304001d000238b80e2e04005c83031858061604005cc24238780e1e04005c830338780e1e04005cc2421858061e040054430328680a1a040038703038780e1e040064430338780e1e040054703028680a1e04004c230330700c1c04004c624238780e1e04004c230338780e1e04004c624230700c1e04001d001838780e1e040038e2e010d08e2e040061001810d0843424001ce2e038780e1e040011000438780e1e0400101a0a0c4c031304001100180c4c03130400101a0a38780e1e04000d000338780e1e04000c38300646038304000d00180646019184000c383038780e1e040049001838780e1e04003900000c4c031304006100180c4c0313040039000038780e1e040010b03006828b03040010c24240010c24240010b0304005cb03040010c24206828c242400107030068287030400104a0a400104a0a400107030400587030400104a0a0682848184001038180682838184001062424001062424001038184004c28184001062420682862424000d00034000cf0e04000c98180e0c038304000cc2424000cc2424000c98184005c90184000cc2420e0c0c2424000c58180e0c038304000c70304000c70304000c58184005850184000c70300e0c038304000c38184004c38184000c62420e0c062424000c38180e0c038304000c62424000c62424000c1a0a400101a0a4000d00030e0c038304000d00034000c28304000d000340010e8e04005cb03040018b0304005cc2424005cc2424005cb0304005cb0304005cc24240018c2424005470304000470304004843034005843034005870304005870304005443034000443034004c38184001438184004c62424004c62424004c38184004c38184004c6242400146242 (by decide +kernel)

def state251_21 : List Sig := roots 251
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude251_21 : Impossible true (goalAt 251) 10 state251_21.toFinset :=
  node_ok cuts251 [⟨state251_13,exclude251_13⟩,⟨state251_14,exclude251_14⟩,⟨state251_20,exclude251_20⟩] 0x40004c2421c0c0c24240004b03040004b03040004c24240018824240004b0301c0c0824240018b03018908624240018c24240018c24240018b03040018903040018c2421890862424000470300e06070304000458181890862424000470301890862424000458180e060503040018b0301c180706040018c2423c380f0e040018b0303c380f0e040018c2421c18070e04000470302c280b0a0400044a0a3c380f0e04000470303c380f0e0400044a0a2c280b0e040014381834300d0c04001462423c380f0e04001438183c380f0e040014624234300d0e04001898181a180686040018c2423a380e8e04001898183a380e8e040018c2421a18068e04000458182a280a8a04000470303a380e8e04000458183a380e8e04000470302a280a8e040014381832300c8c04001462423a380e8e04001438183a380e8e040014624232300c8e0400101a0a3a380e8e04000cf0e00e0c0f0e0800081a0a0e0c038304000cf0e03a380e8e040018c24218980626040018b03038b80e2e040018c24238b80e2e040018b0301898062e0400044a0a28a80a2a040004703038b80e2e0400044a0a38b80e2e040004703028a80a2e040014624230b00c2c040014381838b80e2e040014624238b80e2e040014381830b00c2e040010524238b80e2e040008f0e00c8c0f0e08000452420c8c0504240008f0e038b80e2e04000c4a4238b80e2e040008e8e006860e8e0800004a4206860484240008e8e038b80e2e040000830318580616040000c24238780e1e040000830338780e1e040000c2421858061e040004430328680a1a040004703038780e1e040004430338780e1e040004703028680a1e040000230330700c1c040000624238780e1e040000230338780e1e040000624230700c1e040000130338780e1e040000f0e00c4c0f0e04000013030c4c0313040000f0e038780e1e0400000b0338780e1e040000e8e006460e8e0400000b0306460191840000e8e038780e1e040001000038780e1e040000e2e010d08e2e040001000010d08434240000e2e038780e1e0 (by decide +kernel)

theorem lower251 : Claim 251 11 :=
  fromSearch 67 (by decide +kernel) exclude251_21


open PEqualNP.CircuitLowerBounds

def graph : Sig := goalAt 255
theorem graph_proper : proper graph := by unfold proper; decide +kernel

def edgeList : List Nat := [0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7]
def target (x : Fin 8 → Bool) : Bool :=
  decide (∃ i < edgeList.length / 2,
    (List.ofFn x).getD (edgeList.getD (2*i) 0) false = true ∧
    (List.ofFn x).getD (edgeList.getD (2*i+1) 0) false = true)

def smallCircuit : Circuit := ⟨[⟨.or, [0, 1]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [7, 9]⟩, ⟨.or, [0, 2]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [11, 12]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [0, 5]⟩, ⟨.and, [8, 10]⟩, ⟨.and, [13, 14]⟩, ⟨.and, [3, 15]⟩, ⟨.or, [16, 17]⟩, ⟨.or, [19, 18]⟩], 20⟩

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


def lowRow (i : Fin 8) : Row := Fin.ofNat 256 (1 <<< ([3, 4, 6, 0, 0, 0, 0, 0] : List Nat).getD i.val 0)
def highRow (i : Fin 8) : Row := Fin.ofNat 256 ((1 <<< i.val) ||| (1 <<< ([3, 4, 6, 0, 0, 0, 0, 0] : List Nat).getD i.val 0))

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
  (ruleFor 255 lower251 none (by decide +kernel)).property 11 eightInputs
    (by decide +kernel) (by decide +kernel)

end PEqualNP.Outside.L_meta_31213_aux

open PEqualNP.Outside.L_meta_31213_aux in
theorem PEqualNP.Outside.L_meta_31213 : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true))  := by
  intro gates o fit _ correct
  exact replaceShort lowerGraph gates o fit correct

import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_31389_aux


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
  (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 2 &&& x 5) ||| (x 0 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 5 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 2 &&& x 7) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)


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

def cuts193 : Cuts (goalAt 193) := []

def state193_0 : List Sig := roots 193
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude193_0 : Impossible true (goalAt 193) 3 state193_0.toFinset :=
  node_ok cuts193 [] 0x30100410130100810130200c08030100c08030200810110404410120404414010500c04020600818020404818020600c04010500414010404818020600c08010500c08010404414010500c080206008180 (by decide +kernel)

theorem lower193 : Claim 193 4 :=
  fromSearch 6 (by decide +kernel) exclude193_0

def cuts161 : Cuts (goalAt 161) := []

def state161_0 : List Sig := roots 161
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude161_0 : Impossible true (goalAt 161) 3 state161_0.toFinset :=
  node_ok cuts161 [] 0x28080210128080810128200a08028080a08028200810108404210120404212008480a02020600818020404818020600a02008480212008404818020600a08008480a08008404212008480a080206008180 (by decide +kernel)

theorem lower161 : Claim 161 4 :=
  fromSearch 5 (by decide +kernel) exclude161_0

def rule225_0 : {c : Cut // CutGood (goalAt 225) c} :=
  ruleFor 225 lower224 none (by decide +kernel)

def rule225_1 : {c : Cut // CutGood (goalAt 225) c} :=
  ruleFor 225 lower193 none (by decide +kernel)

def rule225_2 : {c : Cut // CutGood (goalAt 225) c} :=
  ruleFor 225 lower161 none (by decide +kernel)

def cuts225 : Cuts (goalAt 225) := [rule225_0,rule225_1,rule225_2]

def state225_0 : List Sig := roots 225
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude225_0 : Impossible true (goalAt 225) 5 state225_0.toFinset :=
  node_ok cuts225 [] 0x40008c04018080c04040008a02030200c08040008c04030200c08040008a02018080602040004a02018100604040004c04028200a08040004a02028200a08040004c04018100604040004602028200a08040004c08018100c08040004602018100604040004c08028200a08040000810110500414040000c04020600818040000810120600818040000c04010500414040000410120600818040000c08010500c08040000410110500414040000c08020600818040000210120600818040000a08008480a08040000210108480212040000a080206008180 (by decide +kernel)

theorem lower225 : Claim 225 6 :=
  fromSearch 5 (by decide +kernel) exclude225_0

theorem lower209 : Claim 209 5 :=
  fromLift 5 16 4 lower193 (by decide +kernel)

theorem lower240 : Claim 240 5 :=
  fromLift 5 16 1164378112 lower224 (by decide +kernel)

theorem lower177 : Claim 177 5 :=
  fromLift 5 16 4 lower161 (by decide +kernel)

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

def cuts145 : Cuts (goalAt 145) := []

def state145_0 : List Sig := roots 145
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude145_0 : Impossible true (goalAt 145) 3 state145_0.toFinset :=
  node_ok cuts145 [] 0x240401101240408101242009080240409080242008101044041101204041110044409010206008180204048180206009010044401110044048180206009080044409080044041110044409080206008180 (by decide +kernel)

theorem lower145 : Claim 145 4 :=
  fromSearch 4 (by decide +kernel) exclude145_0

def rule241_0 : {c : Cut // CutGood (goalAt 241) c} :=
  ruleFor 241 lower225 none (by decide +kernel)

def rule241_1 : {c : Cut // CutGood (goalAt 241) c} :=
  ruleFor 241 lower209 none (by decide +kernel)

def rule241_2 : {c : Cut // CutGood (goalAt 241) c} :=
  ruleFor 241 lower240 none (by decide +kernel)

def rule241_3 : {c : Cut // CutGood (goalAt 241) c} :=
  ruleFor 241 lower177 none (by decide +kernel)

def rule241_4 : {c : Cut // CutGood (goalAt 241) c} :=
  ruleFor 241 lower113 none (by decide +kernel)

def rule241_5 : {c : Cut // CutGood (goalAt 241) c} :=
  ruleFor 241 lower145 none (by decide +kernel)

def rule241_6 : {c : Cut // CutGood (goalAt 241) c} :=
  ruleFor 241 lower97 none (by decide +kernel)

def rule241_7 : {c : Cut // CutGood (goalAt 241) c} :=
  ruleFor 241 lower193 none (by decide +kernel)

def rule241_8 : {c : Cut // CutGood (goalAt 241) c} :=
  ruleFor 241 lower224 none (by decide +kernel)

def rule241_9 : {c : Cut // CutGood (goalAt 241) c} :=
  ruleFor 241 lower161 none (by decide +kernel)

def cuts241 : Cuts (goalAt 241) := [rule241_0,rule241_1,rule241_2,rule241_3,rule241_4,rule241_5,rule241_6,rule241_7,rule241_8,rule241_9]

def state241_0 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffaaaaaaaaffffffffaaaaaaaa,input 0,input 7,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_0 : Impossible true (goalAt 241) 4 state241_0.toFinset :=
  node_ok cuts241 [] 0x180c0c08030200603018140c08030201000524200c080180c09080240c090802420011011814090802420100003414081803020041012060081802420031302060031302060081800c4c05150 (by decide +kernel)

def state241_1 : List Sig := [0x5555555555555555555555555555555555555555000000005555555500000000,input 0,input 7,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_1 : Impossible true (goalAt 241) 4 state241_1.toFinset :=
  node_ok cuts241 [] 0x603030200c080180c0908030200603024200903024200908004404111030200515030200414024200515024200515034540810114540c08018140c080104049080181409080044046050341409030181408180 (by decide +kernel)

def state241_2 : List Sig := [0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 0,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_2 : Impossible true (goalAt 241) 4 state241_2.toFinset :=
  node_ok cuts241 [] 0x605030200c08010404603030200c080180c090803020060302420060502420090800440490302420090804001c8180302004101206008180242001101206008101206008180181405150341406050240c06050 (by decide +kernel)

def state241_3 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 7,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 0,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_3 : Impossible true (goalAt 241) 5 state241_3.toFinset :=
  node_ok cuts241 [⟨state241_0,exclude241_0⟩,⟨state241_1,exclude241_1⟩,⟨state241_2,exclude241_2⟩] 0x10005180c06030240c0c08030201000530200c080240c06030180c0605010404605040014c08030200605030200c080400144101104044101206008180302005150302004101145405150302008180206001101206008180242005150242001101145405150242008180206010006145405150240c08180206020002206008180240c051501454200011454051501814081802060200002060081801814051501454060302420090803020100053020060304001460303020090802420090300440490304001c908024200903024200908040018110104404605004404605040000908024200605024200908040000110104405000140004d050 (by decide +kernel)

def state241_4 : List Sig := [0xffffffffaaaaaaaaffffffffaaaaaaaa,input 7,input 0,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_4 : Impossible true (goalAt 241) 4 state241_4.toFinset :=
  node_ok cuts241 [] 0xd05030200c08024140908030200603024200d05024200908030140818030200410120600818024200313020600d150206008180341406030302006050302006040242006050242005150206003130206009030 (by decide +kernel)

def state241_5 : List Sig := [0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 7,0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_5 : Impossible true (goalAt 241) 4 state241_5.toFinset :=
  node_ok cuts241 [] 0x603030200c080180c0513030200c0800c4c090803020060302420011012420090800440431302420090804001c818030200605020600818024200605020600605020600818018140515020600818018140d050 (by decide +kernel)

def state241_6 : List Sig := [0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,input 0,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_6 : Impossible true (goalAt 241) 5 state241_6.toFinset :=
  node_ok cuts241 [⟨state241_0,exclude241_0⟩,⟨state241_4,exclude241_4⟩,⟨state241_5,exclude241_5⟩] 0xd050180c0d050280c0c08030200d05030200c080280c0603024140d05004404d05030100908024200d0502420090803010011013014060302420090803020100053020060304001460303020090802420081010c4c031303414100083414081018000881013414031303414041010c4c031303020100053020041014001441013020031303020011014001c11012420031302420011010c4c03130242010007242010001400048180280c0605018140d05080004d050280c20000240c0d050181406050180c10005180c0c08018140c080180c0605018140c08040014c080044050000282009080181409080044046050181409080400009080 (by decide +kernel)

def state241_7 : List Sig := [0xffff000000000000ffff000000000000aaaa000000000000aaaa,input 0,input 7,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_7 : Impossible true (goalAt 241) 4 state241_7.toFinset :=
  node_ok cuts241 [] 0xd05030200c080241406030302006050302006050341409030181408180302005150206008180181403130206005150206008180145409080180c0c08024200a08030140908024200d050206005150206009080 (by decide +kernel)

def state241_8 : List Sig := [0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 0,input 7,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_8 : Impossible true (goalAt 241) 5 state241_8.toFinset :=
  node_ok cuts241 [⟨state241_5,exclude241_5⟩,⟨state241_0,exclude241_0⟩,⟨state241_2,exclude241_2⟩,⟨state241_7,exclude241_7⟩] 0x180c0c080302006030180c0c080302006030180c0c08018140c0802820060502040600021814060504000600011814090803020060302420011012420090800440600032420090804001cd05020600c080104048180206006050800008180206009080044048180204048180400185150 (by decide +kernel)

def state241_9 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 5,input 0,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_9 : Impossible true (goalAt 241) 6 state241_9.toFinset :=
  node_ok cuts241 [⟨state241_3,exclude241_3⟩,⟨state241_6,exclude241_6⟩,⟨state241_8,exclude241_8⟩] 0x40014d050180c0d05040014a03030200c08040014d05030200c08040014a030180c0905040018810114540515040020d05020600818080008810120600818040018d05014540515040014410120600818040014c08014540c08040014410114540515040014c0802060081804000500012060081804000460500c4c060504000600010c4c031304000460502060081804001c11012060081804001c90801454090804001c11011454051504001c908020600818040004a03018140605040004d05040004d05040004a03080000903040004d05018140605040004603040014603040004c08018140c08040004603018140605040004c08040004c08040001000040000a08040018d05004404d0504001cc0402420090804001cd05024200908040018c04004404c05040014603024200908040014c08040014c08040014603040014603040014c080242009080 (by decide +kernel)

def state241_10 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaa,input 0,input 7,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_10 : Impossible true (goalAt 241) 4 state241_10.toFinset :=
  node_ok cuts241 [] 0x28200908018140908018140a080282006050180c0a080282010005241409080242001101180c090802420100002c0c08180282002101206008180242005150206005150206008180145403130 (by decide +kernel)

def state241_11 : List Sig := [0x5555555555555555555555555555555555555555555555550000000000000000,input 0,input 7,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_11 : Impossible true (goalAt 241) 4 state241_11.toFinset :=
  node_ok cuts241 [] 0xa08024200605024200605028200a08018140905024200908004404111028200313028200212024200313024200313024140810124140a080180c0a080084049080180c090800440490502c0c09050180c08180 (by decide +kernel)

def state241_12 : List Sig := [0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 0,0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_12 : Impossible true (goalAt 241) 4 state241_12.toFinset :=
  node_ok cuts241 [] 0xa08024200605024200603028200a08008404605028200a080181406030242009080044049050242009080400248180282002101206008180242001101206008101206008180180c051502c0c09050241406030 (by decide +kernel)

def state241_13 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 0,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_13 : Impossible true (goalAt 241) 5 state241_13.toFinset :=
  node_ok cuts241 [⟨state241_10,exclude241_10⟩,⟨state241_11,exclude241_11⟩,⟨state241_12,exclude241_12⟩] 0x1000528200a08024200605024201000518140605024200a08024201000518140605024140a08028201000528200a08024140605018140603008404603040014a08028200603028200a0804001421010840421012060081802820031302820021010c4c031302820081802060011012060081802420051502420011011454051502420081802060100061454051502414081802060200022060081802414051501454200010c4c03130180c08180206020000206008180180c031300c4c090500440490504002490802420090502420090804001811010440460300440460304000090802420060302420090804000011010440500034000cb030 (by decide +kernel)

def state241_14 : List Sig := [0xffffffffffffffffaaaaaaaaaaaaaaaa,input 7,input 0,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_14 : Impossible true (goalAt 241) 4 state241_14.toFinset :=
  node_ok cuts241 [] 0xa08024200605024200605028200a08018140b030242009080280c08180282002101206008180242005150206005150206008180145406050282006050282006020242006030242005150206005150206009050 (by decide +kernel)

def state241_15 : List Sig := [0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 7,0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_15 : Impossible true (goalAt 241) 4 state241_15.toFinset :=
  node_ok cuts241 [] 0xa08024200605024200a08020600605020600605028200a08018140605028200a080145401101242009080044045150242009080400248180242006030206006030206008180180c05150206008180180c09150 (by decide +kernel)

def state241_16 : List Sig := [0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa,input 0,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_16 : Impossible true (goalAt 241) 5 state241_16.toFinset :=
  node_ok cuts241 [⟨state241_10,exclude241_10⟩,⟨state241_14,exclude241_14⟩,⟨state241_15,exclude241_15⟩] 0xb03018140605030140a08028200b03028200a08030140605018141000528200a08024200605024201000518140605024200a08024200603028200a08040014605018140603018140605040014a08028200c05004404c05028080908024200c050242009080280801101280c081011454051503014100082454081018000881013014051501454021011454051502820100052820021014001421012820051502820011014002411012420051502420011011454051502420100092420100034000c818030140603030140b03080004b03030142000024140b030180c09050044050000302009080180c09080044046030180c09080400009080 (by decide +kernel)

def state241_17 : List Sig := [0xffff0000ffff00000000000000000000aaaa0000aaaa,input 0,input 7,input 6,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_17 : Impossible true (goalAt 241) 4 state241_17.toFinset :=
  node_ok cuts241 [] 0xa08018140605028200605028200a08018140c0502c0c0905024140818028200313020600818014540515020600515020600818014540908018140a08024200c080280c0908024200c050206005150206009080 (by decide +kernel)

def state241_18 : List Sig := [0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 0,input 7,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 6,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_18 : Impossible true (goalAt 241) 5 state241_18.toFinset :=
  node_ok cuts241 [⟨state241_15,exclude241_15⟩,⟨state241_10,exclude241_10⟩,⟨state241_12,exclude241_12⟩,⟨state241_17,exclude241_17⟩] 0x28200605018140a08028200908018140908018140a08028200605018140a080282006050302006030204060002180c060304000e0001180c0110124200908004406000324200908040024c05020600a080084048180206006030800008180206009080044048180204048180400185150 (by decide +kernel)

def state241_19 : List Sig := [0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 6,input 0,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_19 : Impossible true (goalAt 241) 6 state241_19.toFinset :=
  node_ok cuts241 [⟨state241_13,exclude241_13⟩,⟨state241_16,exclude241_16⟩,⟨state241_18,exclude241_18⟩] 0x40014b03018140605040014c05028200a08040014b03028200a08040014c0501814060504000c603028200a0804000d00051814060504000c60301814060504000d000328200a08040015000528200a08040014908018140908040015000518140605040014908028200908040018810114540515040020c05020600818080008810120600818040018c05014540515040014210120600818040014a0800c4c0a0804001421010c4c0313040014a0802060081804000d00032060081804000c60301454051504000e00011454051504000c60302060081804002411012060081804002490801454090804002411011454051504002490802060081804000cc050180c0c0504000cb0304000cb0304000cc0508000090504000cb030180c0905040001000040000c08040018c05004404c05040024a02024200908040024c05024200908040018a02004404a030 (by decide +kernel)

def state241_20 : List Sig := [0xffff0000ffff0000ffff0000ffff0000ffff0000aaaa0000ffff0000aaaa,input 7,input 0,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_20 : Impossible true (goalAt 241) 4 state241_20.toFinset :=
  node_ok cuts241 [] 0x34140c08030200905028200c0801c140a0801c140a08028200705020600c08014540818020600a0800c4c0818014540818020600515024200603030200908024200605028200908020600515020600908030140908024200d050 (by decide +kernel)

def state241_21 : List Sig := [0xffffffffffffffff0000000000000000ffffffffaaaaaaaa,input 7,input 0,input 5,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_21 : Impossible true (goalAt 241) 4 state241_21.toFinset :=
  node_ok cuts241 [] 0x24200a08018140908034140908024200c0501c140a08028200705020600908014540818020600a0800c4c0818014540818020600515024200603024200c08028200705028200c08020600515020600c08024140c08030200d050 (by decide +kernel)

def state241_22 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffaaaaaaaaffffffffaaaaaaaa,input 7,input 0,input 5,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_22 : Impossible true (goalAt 241) 5 state241_22.toFinset :=
  node_ok cuts241 [⟨state241_0,exclude241_0⟩,⟨state241_20,exclude241_20⟩,⟨state241_21,exclude241_21⟩] 0x703030200c0801c0c2000230200c0804000c908030200603024200908028202000024200b030242009080280c2000124200908040000a08030200703028200b03028200a080240c0705020600c0801040481802060090800c4c0818020600a0800c4c081800c4c0818020600313014540d050 (by decide +kernel)

def state241_23 : List Sig := [0xffffffffaaaaaaaaffffffffaaaaaaaa,input 7,input 0,input 5,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_23 : Impossible true (goalAt 241) 5 state241_23.toFinset :=
  node_ok cuts241 [⟨state241_4,exclude241_4⟩] 0xd05030200c08024140908030200603024200908028202000024200d05024200908030140a08030200703028200f05028200a08034140818030200410120600818024200313020600818028200313020600d15020600818034140703030200703030200110124200110124200705028200210128200515020600313020600b030 (by decide +kernel)

def state241_24 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_24 : Impossible true (goalAt 241) 4 state241_24.toFinset :=
  node_ok cuts241 [] 0x1c0c0c08030200313010404c08030200210124200c080180c090802420081800440481800c4c0908024200813004404908024200110120600c0801c0c081801454081802060090301c140818020601000434140d0500c4c01130 (by decide +kernel)

def state241_25 : List Sig := [0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 7,0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,input 5,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_25 : Impossible true (goalAt 241) 5 state241_25.toFinset :=
  node_ok cuts241 [⟨state241_5,exclude241_5⟩,⟨state241_24,exclude241_24⟩] 0x1c0c0c0803020070301c0c0c08030200313024200c080180c090802420021018000090802420081800440481800440490802420011010c4c090802420021301c0c0c0801c0c0c080282002101204060001084043130084043130044c0818030200703020600810120600818040010515020600818040004d050 (by decide +kernel)

def state241_26 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 7,0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,input 0,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_26 : Impossible true (goalAt 241) 5 state241_26.toFinset :=
  node_ok cuts241 [⟨state241_24,exclude241_24⟩] 0x1c0c0c08030200703010404c08030200210124200c080180c0908024200a0800440490802c0c0908024200a0300440490802420011010c4c0c08010404c0800848090800c4c09080206003130244c200000c4c021010c4c03130044c0a08030200703028200b03028200a080240c0705028200a08040010d050 (by decide +kernel)

def state241_27 : List Sig := [0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,input 0,input 5,input 4,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_27 : Impossible true (goalAt 241) 6 state241_27.toFinset :=
  node_ok cuts241 [⟨state241_6,exclude241_6⟩,⟨state241_22,exclude241_22⟩,⟨state241_23,exclude241_23⟩,⟨state241_25,exclude241_25⟩,⟨state241_26,exclude241_26⟩] 0xd0501c0c0d0502c0c0c08030200d05030200c0802c0c0703024140d05004404d05030100908024200d05024200908030100110130140703024200908030201000530200703040014603030200908024201000124200908008405000108405000740006000008404908024201000724200908040000110104405000704404110140000908024200b03008404b03034141000134140b03080010b03034140210134140703008404703030201000130200703040014703030200210130201000140008a0802040431300c4c0d05040008d05020406000320404d0500c4c0d0501040431300c4c0c08040008c08010405000510404c0800c4c0c0800440421200848090800c4c090800440431300c4c090800848090800840500010840500020c4c03130400050001044c100014000481802c0c100042c0c0d05080008d0502c0c200012c0c0d05040010d0501c0c100031c0c0c08040014c0801c0c100051c0c0c0804000cc080 (by decide +kernel)

def state241_28 : List Sig := [0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000aaaa0000aaaa,input 7,input 0,input 6,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_28 : Impossible true (goalAt 241) 4 state241_28.toFinset :=
  node_ok cuts241 [] 0x28200c0801c140a0801c140a08028200705034140c08030200905020600a0800c4c0818020600c08014540818014540818020600515024200605028200908024200603030200908020600515020600908030140908024200d050 (by decide +kernel)

def state241_29 : List Sig := [0xffffffff00000000ffffffff00000000ffffffff00000000aaaaaaaa,input 7,input 0,input 6,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_29 : Impossible true (goalAt 241) 4 state241_29.toFinset :=
  node_ok cuts241 [] 0x24200c080180c0908034140908024200c05034140c08030200905020600908014540818020600c08014540818014540818020600515024200605024200a08028200705030200a08020600313020600a0801c140a080282007050 (by decide +kernel)

def state241_30 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaa,input 7,input 0,input 6,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_30 : Impossible true (goalAt 241) 5 state241_30.toFinset :=
  node_ok cuts241 [⟨state241_10,exclude241_10⟩,⟨state241_28,exclude241_28⟩,⟨state241_29,exclude241_29⟩] 0xa08030200705028200705028200a0801c142000228200a08040004908028200605024200908030202000024200d05024200908030142000124200908040000d05030200c08024140703020600a08008404818020600908014540818020600c0801454081801454081802060051500c4c0b030 (by decide +kernel)

def state241_31 : List Sig := [0xffffffffffffffffaaaaaaaaaaaaaaaa,input 7,input 0,input 6,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_31 : Impossible true (goalAt 241) 5 state241_31.toFinset :=
  node_ok cuts241 [⟨state241_14,exclude241_14⟩] 0xa08030200705028200705028200a0801c140908028200605024200908030202000024200b030242009080280c0f03030200c0802c0c0818028200210120600818024200515020600818030200515020600515020600818014540705028200705028200110124200110124200703030200410130200515020600515020600d050 (by decide +kernel)

def state241_32 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_32 : Impossible true (goalAt 241) 4 state241_32.toFinset :=
  node_ok cuts241 [] 0x2820081801c14081801c140a08028200515008404a08028200210124200a0801814090802420081800440481801454090802420081500440490802420011011454081802060090501c0c081802060100042c0c05150145401150 (by decide +kernel)

def state241_33 : List Sig := [0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 7,0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa,input 6,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_33 : Impossible true (goalAt 241) 5 state241_33.toFinset :=
  node_ok cuts241 [⟨state241_15,exclude241_15⟩,⟨state241_32,exclude241_32⟩] 0x2820070501c140a0802820081801c14081801c140a0802820070501c140a08028200515024200a08018140908024200410180000908024200818004404818004404908024200110114540908024200415030200410120406000110404515010404515004540810120600818040010515020600818040010d050 (by decide +kernel)

def state241_34 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa,input 0,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_34 : Impossible true (goalAt 241) 5 state241_34.toFinset :=
  node_ok cuts241 [⟨state241_32,exclude241_32⟩] 0x28200c0801c140a0801c140a08028200705008404a08028200210124200a08018140908024200c08004404908034140908024200c05004404908024200110114540a08008404a08010500908014540908020600515024542000014540410114540515004540d05030200c08024140703030200c08040010b030 (by decide +kernel)

def state241_35 : List Sig := [0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa,input 0,input 6,input 4,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_35 : Impossible true (goalAt 241) 6 state241_35.toFinset :=
  node_ok cuts241 [⟨state241_16,exclude241_16⟩,⟨state241_30,exclude241_30⟩,⟨state241_31,exclude241_31⟩,⟨state241_33,exclude241_33⟩,⟨state241_34,exclude241_34⟩] 0xb0301c140705034140a08028200b03028200a0803414070501c141000328200a0801040470501c14100051c140705010404a08028201000528200a0804000470501c14100051c140705040004a08028200d05004404d05030100908024200d0502420090803010011013014070502420090802820100052820070504001460502820090802420100032420090801040500031040500094000e000010404908024201000924200908040000110104405000904404110140000908024200d05010404d0502c0c100032c0c0d05080010d0502c0c041012c0c1000240008c08020404515014540d05040008d05020406000320404d05014540515008404515014540a08040008a08008405000508404a08014540a0800440441401050090801454090800440451501454090801050090801040500031040500021454051504000900020454100024000c818034141000434140b03080008b03034142000134140b03040010b030 (by decide +kernel)

def state241_36 : List Sig := [0xffffffff0000ffff0000000000000000ffffffff0000aaaa,input 5,input 0,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_36 : Impossible true (goalAt 241) 3 state241_36.toFinset :=
  node_ok cuts241 [] 0x14540818020600515020600a0800c4c0818018140a080282006050180c09080242009050206005150206009080242006050282009080 (by decide +kernel)

def state241_37 : List Sig := [0xffffffff0000ffffffffffff0000ffffffffffff0000aaaaffffffff0000aaaa,input 5,input 0,input 7,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_37 : Impossible true (goalAt 241) 4 state241_37.toFinset :=
  node_ok cuts241 [⟨state241_36,exclude241_36⟩] 0xd05030200c08024140818030200515020600515020600818014540818028200313020600515020600818024200a08030200603028200a03028200a08034140605024202000030200908030140908024200d050 (by decide +kernel)

def state241_38 : List Sig := [0xffffffff000000000000ffff00000000ffffffff000000000000aaaa,input 6,input 0,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_38 : Impossible true (goalAt 241) 3 state241_38.toFinset :=
  node_ok cuts241 [] 0x14540818020600515020600c08014540818030140c080302006030181409080242006050206003130206009080242006050302009080 (by decide +kernel)

def state241_39 : List Sig := [0xffffffffffffffff0000ffff0000ffffffffffffffffffff0000aaaa0000aaaa,input 6,input 0,input 7,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_39 : Impossible true (goalAt 241) 4 state241_39.toFinset :=
  node_ok cuts241 [⟨state241_38,exclude241_38⟩] 0x605028200a08018140a08030200605028202000024200a08024200818028200313020600515020600818014540818030200515020600313020600818024200c05030200c0802c0c0603030140908024200b030 (by decide +kernel)

def state241_40 : List Sig := [0xffff0000ffff0000ffff0000ffff0000aaaa0000aaaa0000aaaa0000aaaa,input 0,input 7,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_40 : Impossible true (goalAt 241) 5 state241_40.toFinset :=
  node_ok cuts241 [⟨state241_7,exclude241_7⟩,⟨state241_17,exclude241_17⟩,⟨state241_37,exclude241_37⟩,⟨state241_39,exclude241_39⟩] 0x34140603034140b03030200c08034140c08030200b030180c09050180c0a08028200c08018140c080180c0605018140c08028200a0802c0c0605018140d05028200a0802c0c0a08028200d05018140605010404818020600c08014540c08010404515014540c08020600818008404818020600a0800c4c0a0800840431300c4c0a08020600818020404515014540d05020600818020404818020600d05014540515030200908024200603080004603030202000330200603024200908028200908024200605080000605028202000228200605024200908020404110130140d05024200908020404908024200d05004404d050206009080206005150044045150206001101206005150242009080 (by decide +kernel)

def state241_41 : List Sig := [0xffff0000ffff0000ffff0000ffff0000aaaa0000aaaa0000aaaa0000aaaa,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 0,input 7,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_41 : Impossible true (goalAt 241) 5 state241_41.toFinset :=
  node_ok cuts241 [] 0x180c0c080302006030180c0c08030200603028200c08018140a08018140a08028200605018140a080282006050341408180302004101206008180282002101206008101206010006145409080180c0c08024200908018140a080242001101242009080044048180044048180242010000 (by decide +kernel)

def state241_42 : List Sig := [0xffffffff00000000ffffffff00000000aaaaaaaa00000000aaaaaaaa,input 5,input 0,input 7,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_42 : Impossible true (goalAt 241) 5 state241_42.toFinset :=
  node_ok cuts241 [⟨state241_7,exclude241_7⟩] 0x703030200c0801c0c0908030200603024200b030242009080280c090801810060502420081803020041012060081802420031302060031302060081800c4c081801c14031302060070303020070503020070503c140b0301c140c0801c0c0c0801c0c0908080000908040000d0503414081012c0c081801454081800c4c0a080 (by decide +kernel)

def state241_43 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 0,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_43 : Impossible true (goalAt 241) 5 state241_43.toFinset :=
  node_ok cuts241 [⟨state241_24,exclude241_24⟩,⟨state241_2,exclude241_2⟩] 0x1c0c0c08030200703010404c08030200410124200c080180c090802c0c0908024200a03024200a08080004908004404908024200110120600c08010404818020600908004404818014540818028202000020600810120600818040008d05034140b03040004a08030200703028200b03028200a080240c07050 (by decide +kernel)

def state241_44 : List Sig := [0xffffffffffffffff0000000000000000aaaaaaaaaaaaaaaa,input 6,input 0,input 7,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_44 : Impossible true (goalAt 241) 5 state241_44.toFinset :=
  node_ok cuts241 [⟨state241_17,exclude241_17⟩] 0x705028200a0801c140a0801c140705028200908028200605024200d05024200908030140908018080603024200818028200210120600818024200515020600515020600818014540818014540515020600d0503c0c0d0501c0c0a0801c140a0801c140908080000908040000b03034140810134140818014540818014540c080 (by decide +kernel)

def state241_45 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 0,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_45 : Impossible true (goalAt 241) 5 state241_45.toFinset :=
  node_ok cuts241 [⟨state241_32,exclude241_32⟩,⟨state241_12,exclude241_12⟩] 0x1c140a08028200705028200c0801c140a08008404a08028200210124200a08018140908034140908024200c05024200c08080004908004404908024200110120600a08008404818020600908004404818014540818030202000020600810120600818040008b03034140d05040008d05030200c080241407030 (by decide +kernel)

def state241_46 : List Sig := [0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 0,input 7,input 4,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_46 : Impossible true (goalAt 241) 6 state241_46.toFinset :=
  node_ok cuts241 [⟨state241_25,exclude241_25⟩,⟨state241_33,exclude241_33⟩,⟨state241_8,exclude241_8⟩,⟨state241_18,exclude241_18⟩,⟨state241_22,exclude241_22⟩,⟨state241_30,exclude241_30⟩,⟨state241_40,exclude241_40⟩,⟨state241_41,exclude241_41⟩,⟨state241_42,exclude241_42⟩,⟨state241_43,exclude241_43⟩,⟨state241_44,exclude241_44⟩,⟨state241_45,exclude241_45⟩] 0x100041c0c0703020404c08030202000b30200c0802040470301c0c2000a1c0c070304000cc08030202000530200c0804000c70301c0c0703028200a0803020070503020070301c140705030200a0802820100041c140705020404a08028202000928200a0802040470501c14200081c140705040004a08028202000428200a0804000470501c14070302420090803020100063020070308000c60303020090802420070502420090802820100062820070508000860502820090802420100040440411012040490802420100062420090802040411010440500068001e000640000908024201000624200908040001000640001000440008d05010404818020600c08040008c08010406000110404c08020600818008404818020600a08040008a08008406000008404a080206008180044048180206009080400089080044050006044049080206008180204050004204050002206008180400110004400110004400105150 (by decide +kernel)

def state241_47 : List Sig := [0x5555555555555555555555555555555555555555000000005555555500000000,input 0,input 5,input 7,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_47 : Impossible true (goalAt 241) 5 state241_47.toFinset :=
  node_ok cuts241 [⟨state241_1,exclude241_1⟩] 0x703030200c0801c0c0908030200603024200b030242009080280c0908028202000024200a08030200703028200b03028200a080240c0111030200515030200414024200515024200515034540810114540515028200210128200c08010404c08010404908004404908004404d05034140b03020404a0801c140a080084048180 (by decide +kernel)

def state241_48 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,input 7,input 0,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_48 : Impossible true (goalAt 241) 6 state241_48.toFinset :=
  node_ok cuts241 [⟨state241_22,exclude241_22⟩,⟨state241_26,exclude241_26⟩,⟨state241_43,exclude241_43⟩,⟨state241_3,exclude241_3⟩,⟨state241_47,exclude241_47⟩] 0x100041c0c070302c0c0c08030201000530200c0802c0c070301c0c100051040441014000cc08030201000530200c0804000c410110404703024200908030201000530200703040014603030200908024200b03004404b03028080908024200b030242009080280801101280c100012420090802820100012820100064000600032820090802420100060440411014000090802420100062420090804000011010440441012060081803020051503020041011454051503020081802060011012060081802420051502420011011454051502420081802060100041454051502c0c081802060200022060081802c0c051501454100012060081802820031302820200010c4c0313028200818020602000414540515040008818020602000020600818040008515014541000140004d0501c0c0a08028200c08040004c0801c0c100051c0c0c08028200a0802c0c100042c0c1000128200a080400050001240c10001400107050 (by decide +kernel)

def state241_49 : List Sig := [0x5555555555555555555555555555555555555555555555550000000000000000,input 0,input 6,input 7,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_49 : Impossible true (goalAt 241) 5 state241_49.toFinset :=
  node_ok cuts241 [⟨state241_11,exclude241_11⟩] 0x705028200a0801c140a08030200705028200908028200605024200d05024200908030140908030202000024200d05030200c08024140111028200313028200212024200313024200313034140810134140313030200410130200a08008404a08008404908004404908004404d0502c0c0d05020404c0801c0c0c080104048180 (by decide +kernel)

def state241_50 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,input 7,input 0,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_50 : Impossible true (goalAt 241) 6 state241_50.toFinset :=
  node_ok cuts241 [⟨state241_30,exclude241_30⟩,⟨state241_34,exclude241_34⟩,⟨state241_45,exclude241_45⟩,⟨state241_13,exclude241_13⟩,⟨state241_49,exclude241_49⟩] 0x100041c140705034140a08028201000528200a0803414070501c141000328200a0803020070503020100051c140705030200a08028201000508404210140004a08028201000528200a08040004210108404705024200908028201000528200705040014605028200908024200d05004404d05030100908024200d0502420090803010011013014100032420090803020100033020100064000e00033020090802420100060440411014000090802420100062420090804000011010440421012060081802820031302820021010c4c031302820081802060011012060081802420051502420011011454051502420081802060100041454051503414081802060200022060081803414051501454100032060081803020051503020200011454051503020081802060200040c4c031304000881802060200002060081804000831300c4c100044000cb03034141000434141000330200c080400110004241410004400107030 (by decide +kernel)

def state241_51 : List Sig := roots 241
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_51 : Impossible true (goalAt 241) 7 state241_51.toFinset :=
  node_ok cuts241 [⟨state241_9,exclude241_9⟩,⟨state241_19,exclude241_19⟩,⟨state241_27,exclude241_27⟩,⟨state241_35,exclude241_35⟩,⟨state241_46,exclude241_46⟩,⟨state241_48,exclude241_48⟩,⟨state241_50,exclude241_50⟩] 0x40010d0501c0c0d0504000cb03030200c08080018d05030200c08040010b0301c0c0905040010b0301c140705040004d05028200a08080014b03028200a08040004d0501c14070504000c703028200a08040004c0801c140c0804001470301c140705040004c08028200a08040000d05004404d05040000c04024200908040000d05024200908040000c04004404c05040000703024200908040000c08040000c08040000703080004603040000c08024200908040000705024200908040000a08040000a08040000705080000605040000a08024200908040010810114540515040008d05020600818080010810120600818040010d0501454051504000c410120600818040008c08014540c0808000c410114540515040008c08020600818040004210120600818040008a0800c4c0a0808000821010c4c0313040004a080206008180400001101206008180400009080145409080400001101145405150400009080206008180 (by decide +kernel)

theorem lower241 : Claim 241 8 :=
  fromSearch 4 (by decide +kernel) exclude241_51

theorem lower245 : Claim 245 9 :=
  fromLift 9 4 1284 lower241 (by decide +kernel)

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

theorem lower226 : Claim 226 5 :=
  fromLift 5 2 353370192 lower224 (by decide +kernel)

theorem lower198 : Claim 198 5 :=
  fromLift 5 2 301991536 lower196 (by decide +kernel)

def cuts162 : Cuts (goalAt 162) := []

def state162_0 : List Sig := roots 162
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude162_0 : Impossible true (goalAt 162) 3 state162_0.toFinset :=
  node_ok cuts162 [] 0x28080220228080820228200a08028080a08028200820208808220220808222008880a02020a00828020808828020a00a02008880222008808828020a00a08008880a08008808222008880a08020a008280 (by decide +kernel)

theorem lower162 : Claim 162 4 :=
  fromSearch 269484112 (by decide +kernel) exclude162_0

theorem lower166 : Claim 166 5 :=
  fromLift 5 2 269485392 lower164 (by decide +kernel)

def cuts100 : Cuts (goalAt 100) := []

def state100_0 : List Sig := roots 100
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude100_0 : Impossible true (goalAt 100) 3 state100_0.toFinset :=
  node_ok cuts100 [] 0x180802404180804404181006040180806040181004404090102404110102420090806020111004440110104440111006020090802420090104440111006040090806040090102420090806040111004440 (by decide +kernel)

theorem lower100 : Claim 100 4 :=
  fromSearch 35652864 (by decide +kernel) exclude100_0

theorem lower102 : Claim 102 5 :=
  fromLift 5 2 34604368 lower100 (by decide +kernel)

def rule230_0 : {c : Cut // CutGood (goalAt 230) c} :=
  ruleFor 230 lower228 none (by decide +kernel)

def rule230_1 : {c : Cut // CutGood (goalAt 230) c} :=
  ruleFor 230 lower226 none (by decide +kernel)

def rule230_2 : {c : Cut // CutGood (goalAt 230) c} :=
  ruleFor 230 lower198 none (by decide +kernel)

def rule230_3 : {c : Cut // CutGood (goalAt 230) c} :=
  ruleFor 230 lower162 none (by decide +kernel)

def rule230_4 : {c : Cut // CutGood (goalAt 230) c} :=
  ruleFor 230 lower166 none (by decide +kernel)

def rule230_5 : {c : Cut // CutGood (goalAt 230) c} :=
  ruleFor 230 lower102 none (by decide +kernel)

def rule230_6 : {c : Cut // CutGood (goalAt 230) c} :=
  ruleFor 230 lower224 none (by decide +kernel)

def rule230_7 : {c : Cut // CutGood (goalAt 230) c} :=
  ruleFor 230 lower164 none (by decide +kernel)

def rule230_8 : {c : Cut // CutGood (goalAt 230) c} :=
  ruleFor 230 lower196 none (by decide +kernel)

def rule230_9 : {c : Cut // CutGood (goalAt 230) c} :=
  ruleFor 230 lower100 none (by decide +kernel)

def cuts230 : Cuts (goalAt 230) := [rule230_0,rule230_1,rule230_2,rule230_3,rule230_4,rule230_5,rule230_6,rule230_7,rule230_8,rule230_9]

def state230_0 : List Sig := [0xfffffffffffffffffffffffffffffffffffffffff0f0f0f0fffffffff0f0f0f0,input 7,input 5,0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude230_0 : Impossible true (goalAt 230) 4 state230_0.toFinset :=
  node_ok cuts230 [] 0x18080c08030200602011108c08030201000720a00c08011018828020a00a08008880828008880828020a00222011108828020a01000028200c08018080a08028080a08028200220618908c242 (by decide +kernel)

def state230_1 : List Sig := [0xfffffffff0f0f0f0fffffffff0f0f0f0,input 7,input 5,0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude230_1 : Impossible true (goalAt 230) 4 state230_1.toFinset :=
  node_ok cuts230 [] 0xc24230200c08020908828030200440620a00828028200222020a00c24220a00828030108a08030200602028200e24228200a08030908602030200444230200444020a00444220a00444228200220628200a020 (by decide +kernel)

def state230_2 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 7,0xfffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0,0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude230_2 : Impossible true (goalAt 230) 4 state230_2.toFinset :=
  node_ok cuts230 [] 0x602030200c08018080440630200c08008818828030200440620a00828021200444220a00222020a00828008880220620a00828040018a08030200444228200444228200a08011108444228200a08011108c242 (by decide +kernel)

def state230_3 : List Sig := [0xfffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0,input 5,0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude230_3 : Impossible true (goalAt 230) 5 state230_3.toFinset :=
  node_ok cuts230 [⟨state230_0,exclude230_0⟩,⟨state230_1,exclude230_1⟩,⟨state230_2,exclude230_2⟩] 0xc24218080c24228080c08030200c24230200c08028080602020908c24208880c24230100828020a00c24220a00828030100222030108440620a0082803020100063020044064000c440630200828020a00220620a00828040018222008880220608880222040018828020a00444220a00828040000222021200444208880444240000828020a00a02008818a02030909000830908a02080008a0203090822063090860200881860203020100083020060204000c602030200220630201000140004a08028080444211108c24280004c24228082000028080c24211108444218081000718080c08011108c08018080444211108c0804001cc080 (by decide +kernel)

def state230_4 : List Sig := [0xffffffff00000000ffffffff00000000f0f0f0f000000000f0f0f0f0,input 5,input 7,0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude230_4 : Impossible true (goalAt 230) 4 state230_4.toFinset :=
  node_ok cuts230 [] 0x602030200c08018080828030200440620a00222020a00828008880828018100604220a00602030200624230200624238908a02018908c08011108c08018080828011108828008880444230908820611108a080 (by decide +kernel)

def state230_5 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude230_5 : Impossible true (goalAt 230) 4 state230_5.toFinset :=
  node_ok cuts230 [] 0x444230200c08018080440630200c08011018828030200440620a00444220a00828008880828028200222020a00820620a00828040018444230908a02011108a08030200602028200a02028200a080111086242 (by decide +kernel)

def state230_6 : List Sig := [0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 7,0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude230_6 : Impossible true (goalAt 230) 5 state230_6.toFinset :=
  node_ok cuts230 [⟨state230_0,exclude230_0⟩,⟨state230_4,exclude230_4⟩,⟨state230_5,exclude230_5⟩] 0x1000318080602020818c08030201000330200c0802081860201808044421808044424001cc08030200444230200c0804001c602018080602028200a08030200624230200602018908624230200a08028201000918908624220818a08028202000228200a0802081862421890a000118908624211108a08028202000028200a08011108624211108440620a0082803020100063020044064000c440630200828020a00624220a00828028200222028200624208880604228200828020a00820608880222040018828020a00820620a00828040018222008880444208880444240000828020a00444220a00828040000222008881000140004c242 (by decide +kernel)

def state230_7 : List Sig := [0x303030303030303030303030303030303030303000000000303030300000000,input 5,input 7,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude230_7 : Impossible true (goalAt 230) 4 state230_7.toFinset :=
  node_ok cuts230 [] 0xc24230200c08020908440630200444230200444230908820611108444228200220628200a08030200624228200624228200a08018908828011018c08020a00848030108828020a00c24220a006042282008280 (by decide +kernel)

def state230_8 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,input 7,0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude230_8 : Impossible true (goalAt 230) 5 state230_8.toFinset :=
  node_ok cuts230 [⟨state230_0,exclude230_0⟩,⟨state230_2,exclude230_2⟩,⟨state230_5,exclude230_5⟩,⟨state230_7,exclude230_7⟩] 0x18080c08030200602011018c08030200440611018c08011108c08021200444228082000211108444228202000128200444240006000011108828030200440620a00222020a00828008880828028200222020a02000320a00828040018c24228200c08018080a08028080a080400206242 (by decide +kernel)

def state230_9 : List Sig := [0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc,input 2,input 5,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude230_9 : Impossible true (goalAt 230) 6 state230_9.toFinset :=
  node_ok cuts230 [⟨state230_3,exclude230_3⟩,⟨state230_6,exclude230_6⟩,⟨state230_8,exclude230_8⟩] 0x4000cc24218080c2424001ca02030200c0804000cc24230200c0804001ca02018080824240024a02018908624240020c24228200a08080008a02028200a08040020c2421890862424001c602028200a08040020c08018908c0804000c602018908624240020c08028200a08040004840611108444240004c24240004c24240004840680004820640004c2421110844424000444064001c440640004c08011108c08040004440611108444240004c08040004c08040004240611108444240004a08040004a08040004240680000220640004a08011108a08040001000040000848040018c24208880c24240018c04020a00828040018c24220a00828040018c04008880c04240018440620a00828040018c08040018c0804001844064000c440640018c08020a00828040018624220a00828040018a08008880a08040018624208880604240018a08020a008280 (by decide +kernel)

def state230_10 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000,input 5,input 7,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude230_10 : Impossible true (goalAt 230) 4 state230_10.toFinset :=
  node_ok cuts230 [] 0x21200828011108828011108848021200444221200a08009080848011018848021201000620908828020a00222011018828020a01000021818a08020a00604220a00604228200a080181082606 (by decide +kernel)

def state230_11 : List Sig := [0xffffffff00000000ffffffff00000000ffffffff0000000000000000,input 5,input 7,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude230_11 : Impossible true (goalAt 230) 4 state230_11.toFinset :=
  node_ok cuts230 [] 0x848020a00444220a00444221200848011108848009080242021200824220a00828008880222020a00222020a00a02020908a02020908848009080848009080828008880828008880824228080824228080a080 (by decide +kernel)

def state230_12 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude230_12 : Impossible true (goalAt 230) 4 state230_12.toFinset :=
  node_ok cuts230 [] 0x848020a00444220a00242021200848009080848028200242021200444221200848011108222020a00828008880824220a0082804001ca08020a00222020a00a02028200a080110186042280808242209084406 (by decide +kernel)

def state230_13 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude230_13 : Impossible true (goalAt 230) 5 state230_13.toFinset :=
  node_ok cuts230 [⟨state230_10,exclude230_10⟩,⟨state230_11,exclude230_11⟩,⟨state230_12,exclude230_12⟩] 0x222028200a08020a00604220a00222018108604220a00a08020a01000918108604220908a08028202000228200a0802090860421810a000109818260611018a08028202000028200a08011018260608900260621200848028200242028200260609080242028200848021201000721200848020a00444220a01000311108444220a00848020a0100031110844422090884802120100032120084802090844421110844060908024204001884802120044062120084804001824200908082420888082424001c828020a00824220a0082804001c222008880440608880222040000828020a00440620a00828040000222008881000440010a020 (by decide +kernel)

def state230_14 : List Sig := [0xffffffffffffffffffffffff00000000,input 7,input 5,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude230_14 : Impossible true (goalAt 230) 4 state230_14.toFinset :=
  node_ok cuts230 [] 0x848020a00444220a00848028200242021200444221200848011108222020a00828008880a08020a00604220a00604228200a08018108444221200444221200222020a00222020a006042282006042282008242 (by decide +kernel)

def state230_15 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 7,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude230_15 : Impossible true (goalAt 230) 4 state230_15.toFinset :=
  node_ok cuts230 [] 0x848020a00444220a00848028200444221200444221200848011108444221200848011108828028200222020a00222020a00828008880604220a0082804001ca02028200a08011018604228200a08011018a242 (by decide +kernel)

def state230_16 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 5,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,input 2,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude230_16 : Impossible true (goalAt 230) 5 state230_16.toFinset :=
  node_ok cuts230 [⟨state230_10,exclude230_10⟩,⟨state230_14,exclude230_14⟩,⟨state230_15,exclude230_15⟩] 0x860611108444230108848021200860621200848030108444211109000721200848020a00444220a01000311108444220a00848020a01000821200848018108242018109000309080242018108848021200440621200848040018444211108440611108444240018848021200c04208880c04228080828020a00c04220a00828028080222008880440620a00828040000222030200440608880222040000828020a00a02018108604230109000828908a02080008a0203010860421810822204001c222020a00604220a00222018108604220a01000820a01000440010a0803010844063010886068000486063010a0000209088606110188242 (by decide +kernel)

def state230_17 : List Sig := [0x333333333333333300000000000000003333333300000000,input 5,input 7,input 6,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude230_17 : Impossible true (goalAt 230) 4 state230_17.toFinset :=
  node_ok cuts230 [] 0x848011108444221200444221200848011108848028200242021200c04228080824220908a08018108604228200604228200a08018108828011108848020a00c08008880828020a00c04220a006042282008280 (by decide +kernel)

def state230_18 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,input 7,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,input 6,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude230_18 : Impossible true (goalAt 230) 5 state230_18.toFinset :=
  node_ok cuts230 [⟨state230_15,exclude230_15⟩,⟨state230_10,exclude230_10⟩,⟨state230_12,exclude230_12⟩,⟨state230_17,exclude230_17⟩] 0x21200444211108848021200828011108828011108848021200444221200a08009080848011108848021200444230200440628082000228080440640012000111018222020a00828008882000320a0082804001cc04228200440680000a08028200828008880828028080a080400206042 (by decide +kernel)

def state230_19 : List Sig := [0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,input 6,input 2,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude230_19 : Impossible true (goalAt 230) 6 state230_19.toFinset :=
  node_ok cuts230 [⟨state230_13,exclude230_13⟩,⟨state230_16,exclude230_16⟩,⟨state230_18,exclude230_18⟩] 0x40024a02018108604240020c04228200a08080008a02028200a08040020c04218108604240011000428200a08040010440618108604240012000118108604240010440628200a0804001c222028200a0804002082801810882804001c22201810860424002082802820082804000c860611108444240018c0422120084804000c860621200848040018c04211108444240020260621200848040018a08009080a0804000c260609080242040018a0802120084804001044062120084804001100061110844424001044061110844424001100042120084804001d00072120084804001882801110882804001d000311108444240018828021200828040010c04211018c04240010a02040010a02040010c04280000824240010a02011018824240001000040000c0804001cc04208880c0424001ca02020a0082804001cc04220a0082804001ca020088802220 (by decide +kernel)

def state230_20 : List Sig := [0x3333333333333333333333333333333333333333303030303333333330303030,input 7,input 2,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude230_20 : Impossible true (goalAt 230) 4 state230_20.toFinset :=
  node_ok cuts230 [] 0x30908c08030200824228200c08018908a08018908a08028200624221200c08011908848021200a08009080848011908848021200464220a00440630200828020a00604228200828020a00444221200828030108828020a00c242 (by decide +kernel)

def state230_21 : List Sig := [0xffffffffffffffff0000000000000000fffffffff0f0f0f0,input 7,input 2,input 5,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude230_21 : Impossible true (goalAt 230) 4 state230_21.toFinset :=
  node_ok cuts230 [] 0x20a00a08018108828020a00848011108828030908828020a00c04218908a08028200624221200a08009080848011908848021200464220a00440620a00c08028200624228200c08021200464221200c08020908c08030200c242 (by decide +kernel)

def state230_22 : List Sig := [0xfffffffffffffffffffffffffffffffffffffffff0f0f0f0fffffffff0f0f0f0,input 7,input 2,input 5,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude230_22 : Impossible true (goalAt 230) 5 state230_22.toFinset :=
  node_ok cuts230 [⟨state230_0,exclude230_0⟩,⟨state230_20,exclude230_20⟩,⟨state230_21,exclude230_21⟩] 0x602030200c08018082000230200c08040010828030200440620a00828028200222020a00828021202000020a00222020a00828008882000120a00828040000a08030200602028200a02028200a08009818624221200c08011818848021200a08009080848009080848021200242011908c242 (by decide +kernel)

def state230_23 : List Sig := [0xfffffffff0f0f0f0fffffffff0f0f0f0,input 7,input 2,input 5,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude230_23 : Impossible true (goalAt 230) 5 state230_23.toFinset :=
  node_ok cuts230 [⟨state230_1,exclude230_1⟩] 0xc24230200c08020908828030200440620a00828028200222020a00828021202000020a00c24220a00828030108a08030200602028200e24228200a08030908848030200460621200848028200242021200c64221200848030908602030200602030200222020a00222020a00624228200260628200464221200242021200a020 (by decide +kernel)

def state230_24 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude230_24 : Impossible true (goalAt 230) 4 state230_24.toFinset :=
  node_ok cuts230 [] 0x18080c08030200242011818c08030200260620a00c08011018828020a00848008880828008880828020a00222009818828020a00240621200c08018080848011908848021201000218908848021200820630908c242090802206 (by decide +kernel)

def state230_25 : List Sig := [0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 7,0xfffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0,input 5,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude230_25 : Impossible true (goalAt 230) 5 state230_25.toFinset :=
  node_ok cuts230 [⟨state230_24,exclude230_24⟩] 0x18080c08030200602018080c08030200242020a00c08011018828020a00222008880828020a00848008880828008880828020a00222008880828020a00222018080c08018080c0802820026062181a000009818242009818242008818848030200602021200860621200848020818464221200848040008c242 (by decide +kernel)

def state230_26 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 7,0xfffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0,input 2,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude230_26 : Impossible true (goalAt 230) 5 state230_26.toFinset :=
  node_ok cuts230 [⟨state230_24,exclude230_24⟩,⟨state230_2,exclude230_2⟩] 0x18080c08030200602011818c08030200260620a00c08011018828020a00242080004828020a00a08008880828008880828020a00222009818828020a00240609080c08011818c08021200242021082000009080260609080242008818a08030200602028200a02028200a08040014624228200a08040004c242 (by decide +kernel)

def state230_27 : List Sig := [0xfffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0,input 2,input 5,input 1,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude230_27 : Impossible true (goalAt 230) 6 state230_27.toFinset :=
  node_ok cuts230 [⟨state230_3,exclude230_3⟩,⟨state230_22,exclude230_22⟩,⟨state230_23,exclude230_23⟩,⟨state230_25,exclude230_25⟩,⟨state230_26,exclude230_26⟩] 0xc24218080c24228080c08030200c24230200c08028080602020908c24208880c24230100828020a00c24220a00828030100222030108460620a0082803020100063020046064000c440630200828020a00260620a00828009010222008880260608880222009010828020a01000120a00828009081000109081000640006000009080828020a01000620a00828040000222008881000608880222040000828020a00a02009818a02030909000230908a02080010a0203090826063090860200981860203020100023020060204000c602030200260630201000140004a08021818242009080c24240004c2422181a000321818c24209080c24211818242009080c08040004c08011819000311818c08009080c08009819000209819000109080242040005000108819000140008848028081000528080c24280008c24228082000128080c24240014c24218081000418080c0804000cc08018081000318080c08040010c080 (by decide +kernel)

def state230_28 : List Sig := [0xffffffff00000000ffffffff00000000f0f0f0f000000000f0f0f0f0,input 5,input 2,input 7,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude230_28 : Impossible true (goalAt 230) 5 state230_28.toFinset :=
  node_ok cuts230 [⟨state230_4,exclude230_4⟩] 0x602030200c08018080828030200440620a00222020a00828008880828021202000020a00828018100604220a00848030200460621200242021200848009080848018908242021200602030200624230200624238908a02018908c08018080c08018080828008880828008880c24230908860628080848011908848009080a080 (by decide +kernel)

def state230_29 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 2,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude230_29 : Impossible true (goalAt 230) 5 state230_29.toFinset :=
  node_ok cuts230 [⟨state230_24,exclude230_24⟩,⟨state230_5,exclude230_5⟩] 0x18080c08030200602011818c08030200460620a00c08011018828020a00848080004828008880828020a00222020a00a08008880828021818828020a00840621200c08011818848011908848028202000021200860621200848020818c24230908a02040004a08030200602028200a02028200a080400086242 (by decide +kernel)

def state230_30 : List Sig := [0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 2,input 7,input 1,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude230_30 : Impossible true (goalAt 230) 6 state230_30.toFinset :=
  node_ok cuts230 [⟨state230_25,exclude230_25⟩,⟨state230_6,exclude230_6⟩,⟨state230_22,exclude230_22⟩,⟨state230_28,exclude230_28⟩,⟨state230_29,exclude230_29⟩] 0x1000518080602021818c08030201000330200c08021818602018081000318080602040010c08030201000330200c08040010602018080602028200a08030200624230200602018908624230200a08028201000518908624221818a08028202000428200a0802181862421890a000318908624240008a08028202000228200a08040008624218908460620a0082803020100063020046064000c440630200828020a00624220a00828028200222028200624208880604228200828020a00860608880222021010828020a00860620a00828021010222008881000120a00828021201000121201000640006000121200828020a01000608880222040000828020a01000620a00828040000222008881000140004c24211818848021200c08040004c08011819000311818c08021200848009818848021200a08040004a0800981a000009818a080212008480218190005218190001212008480400050001208190001400144642 (by decide +kernel)

def state230_31 : List Sig := [0x3333333333333333333333333333333333333333333333333333333300000000,input 7,input 5,input 6,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude230_31 : Impossible true (goalAt 230) 4 state230_31.toFinset :=
  node_ok cuts230 [] 0x21200c08011908848021200a08009080848011908848021200464230908c08030200824228200c08018908a08018908a08028200624220a00444221200828020a00440630200828020a00604228200828030108828020a00c242 (by decide +kernel)

def state230_32 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000,input 7,input 5,input 6,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude230_32 : Impossible true (goalAt 230) 4 state230_32.toFinset :=
  node_ok cuts230 [] 0x20a00c08011018828020a00a08018108828030908828020a00c04230908c08030200824228200c08018908a08018908a08028200624220a00444220a008480212004642302008480212002420282008480119088480212004642 (by decide +kernel)

def state230_33 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000,input 7,input 5,input 6,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude230_33 : Impossible true (goalAt 230) 5 state230_33.toFinset :=
  node_ok cuts230 [⟨state230_10,exclude230_10⟩,⟨state230_31,exclude230_31⟩,⟨state230_32,exclude230_32⟩] 0x84803020046422120084802820024202120046422120084801190a000221200848040004828021200444220a00828030202000020a00828028200604220a00c24220a0082803010a000120a00828040000c24230200c08020908460628200c08018908a08018908a080282006242098188606 (by decide +kernel)

def state230_34 : List Sig := [0xffffffffffffffffffffffff00000000,input 7,input 5,input 6,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude230_34 : Impossible true (goalAt 230) 5 state230_34.toFinset :=
  node_ok cuts230 [⟨state230_14,exclude230_14⟩] 0x848030200464221200848028200242021200464221200848011908828021200444220a00828030202000020a00828028200604220a00222020a00828008880602030200c08018080a08030200624228200624228200a08018908464221200464221200222020a00222020a00602030200602030200624228200624228200c242 (by decide +kernel)

def state230_35 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude230_35 : Impossible true (goalAt 230) 4 state230_35.toFinset :=
  node_ok cuts230 [] 0x21200a08011908848011908848021200464209080848021200242020a00848011108828020a00a08008880828018908828020a00604208880828020a00222018908a08028200824218080a080282010002180806242189082242 (by decide +kernel)

def state230_36 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 7,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 6,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude230_36 : Impossible true (goalAt 230) 5 state230_36.toFinset :=
  node_ok cuts230 [⟨state230_15,exclude230_15⟩,⟨state230_35,exclude230_35⟩] 0x21200464211908848021200a08011908848011908848021200464211908848021200464220a00848011108828020a00602080000828020a00a08008880828008880828020a00222018908828020a00604230200602028082000118080624218080624208908a02028200a08040014624228200a08040010c242 (by decide +kernel)

def state230_37 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 5,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude230_37 : Impossible true (goalAt 230) 5 state230_37.toFinset :=
  node_ok cuts230 [⟨state230_35,exclude230_35⟩] 0x21200624209080848021200c08011908848011908848021200464209080848021200242020a00848011108828020a00604018108828020a00c08008880828030908828020a00c04208880828020a0022202820062422890a000018908602018908624208908c24230200c08020908602030200c08040008a020 (by decide +kernel)

def state230_38 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 5,input 6,input 1,input 2,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude230_38 : Impossible true (goalAt 230) 6 state230_38.toFinset :=
  node_ok cuts230 [⟨state230_16,exclude230_16⟩,⟨state230_33,exclude230_33⟩,⟨state230_34,exclude230_34⟩,⟨state230_36,exclude230_36⟩,⟨state230_37,exclude230_37⟩] 0x860611908464230908848021200860621200848030908464211909000421200848018080464211909000311908464218080848021201000221200848018908242018909000309080242018908848021201000321200848040004464211909000311908464240004848021200c24208880c24230100828020a00c24220a00828030100222030108464220a0082802120100082120046424000c444221200828020a01000420a00828018081000418081000840012000018080828020a00624220a00828018100222018100624208880604218100828020a01000820a00828040000222008881000808880222040000828020a00c24218080c24228081000428080c24280010c24228080602018081000240008c08028080624218908c24240008c24228082000328080c24218908624218081000418081000218908624240009000208909000240010a0803090900053090886068000886063090a0001309088606400148606 (by decide +kernel)

def state230_39 : List Sig := [0xf3f3f3f3f3f3f3f30000000000000000f3f3f3f3f0f0f0f0,input 2,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude230_39 : Impossible true (goalAt 230) 3 state230_39.toFinset :=
  node_ok cuts230 [] 0x18108a08028200604211108848021200444221200a08009080848008880828020a00824220a00604228200828020a004442212008280 (by decide +kernel)

def state230_40 : List Sig := [0xf3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f0f0f0f0f3f3f3f3f0f0f0f0,input 2,input 5,input 7,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude230_40 : Impossible true (goalAt 230) 4 state230_40.toFinset :=
  node_ok cuts230 [⟨state230_39,exclude230_39⟩] 0xc24230200c08020908a08030200624228200624228200a08018908848030200440621200242021200848030908848028200242021200444220a02000030200828030108828020a00c24220a006042282008280 (by decide +kernel)

def state230_41 : List Sig := [0xf0f0f0f0f0f0f0f03030303030303030f0f0f0f0f0f0f0f0303030300000000,input 6,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude230_41 : Impossible true (goalAt 230) 3 state230_41.toFinset :=
  node_ok cuts230 [] 0x18108a08028200604228200c08018108a08030108c08030200602011108828020a00444220a00222028200828020a004442302008280 (by decide +kernel)

def state230_42 : List Sig := [0xffffffffffffffff3333333333333333ffffffffffffffff3333333300000000,input 6,input 5,input 7,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude230_42 : Impossible true (goalAt 230) 4 state230_42.toFinset :=
  node_ok cuts230 [⟨state230_41,exclude230_41⟩] 0x444221200848011108848028200242021200848030200444221202000020a00848020a00604228200a08018108a08030200604228200222020a00a08020a00c04230200c08018080440630108828020a002220 (by decide +kernel)

def state230_43 : List Sig := [0x3333333333333333333333333333333333333333000000003333333300000000,input 5,input 7,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude230_43 : Impossible true (goalAt 230) 5 state230_43.toFinset :=
  node_ok cuts230 [⟨state230_7,exclude230_7⟩,⟨state230_17,exclude230_17⟩,⟨state230_40,exclude230_40⟩,⟨state230_42,exclude230_42⟩] 0x30908602030908a02030200c08030908c08030200a02018080824211018848021200c08011108c08011018444211108c08021200848021818444211108c24221200848021818848021200c24211108444209818848021200a08009080a08009818242009080a08021200848018080a08028200c08018908c08018080624218908c08028200a08028080624218908c24228200a08028080a08028200c24218908624230200828020a00440680004440630202000330200440620a00828021200828020a00444280000444221202000221200444220a00828028080222030108c24220a00828028080828020a00c24208880c24228200828020a00624208880604228200222028200624220a008280 (by decide +kernel)

def state230_44 : List Sig := [0x3333333333333333333333333333333333333333000000003333333300000000,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,input 7,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude230_44 : Impossible true (goalAt 230) 5 state230_44.toFinset :=
  node_ok cuts230 [] 0x18080c08030200602011018c08030200440621200c08011108848011108848021200444221200a08009080848011108848021200444230908a08030200602028200a02028201000818908828011018c08020a00828011108848020a00222020a00828008880828008880a08020a010000 (by decide +kernel)

def state230_45 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f00000000,input 2,input 5,input 7,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude230_45 : Impossible true (goalAt 230) 5 state230_45.toFinset :=
  node_ok cuts230 [⟨state230_7,exclude230_7⟩] 0x602030200c08018080828030200440620a00222020a00828008880828028200222020a00828011100444220a00a08030200602028200a02028200a08009818460630200464230200464231908860611908464228200260628200c08011818c08011818828080000828040000c24230908a02021818a08018908a080098188480 (by decide +kernel)

def state230_46 : List Sig := [0xffffffffffffffff0000000000000000ffffffff00000000,input 6,input 5,input 7,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude230_46 : Impossible true (goalAt 230) 5 state230_46.toFinset :=
  node_ok cuts230 [⟨state230_17,exclude230_17⟩] 0x464221200848011908848028200242021200848011908464221200828021200444220a00c24220a00828030108828028200604220a00828011010440620a00624228200a08018908a08018908624228200c24228080c24228080848011908848011908828080000828040000a02030908a02030908a08018908a08018908c080 (by decide +kernel)

def state230_47 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude230_47 : Impossible true (goalAt 230) 5 state230_47.toFinset :=
  node_ok cuts230 [⟨state230_35,exclude230_35⟩,⟨state230_12,exclude230_12⟩] 0x21200a08009080848011908848021200464221200c08011908848009080848021200242020a00848011108828020a00a08008880828030908828020a00c04220a00c08080004828008880828020a00222018908a08030202000028200a02028200a08040008a02030908c24240008c24230200c080209086020 (by decide +kernel)

def state230_48 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,input 7,input 1,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude230_48 : Impossible true (goalAt 230) 6 state230_48.toFinset :=
  node_ok cuts230 [⟨state230_36,exclude230_36⟩,⟨state230_8,exclude230_8⟩,⟨state230_18,exclude230_18⟩,⟨state230_22,exclude230_22⟩,⟨state230_26,exclude230_26⟩,⟨state230_29,exclude230_29⟩,⟨state230_33,exclude230_33⟩,⟨state230_43,exclude230_43⟩,⟨state230_44,exclude230_44⟩,⟨state230_45,exclude230_45⟩,⟨state230_46,exclude230_46⟩,⟨state230_47,exclude230_47⟩] 0x1000518080602028080c08030202000b30200c08028080602018082000a11818460640010c08030202000630200c08040010460611818460621200848030200464230200460611908464230200848021201000511908464228080848021202000521200848028080464211909000221200848028200242028202000409080242028200848021202000911908464240004848021202000321200848040004464211908460620a00828030201000830200460680008440630200828020a00464220a00828021201000821200464280004444221200828020a01000508880222028080828020a01000820a00828028080222008881000220a00828028200222028201000808880222028200828020a01000880022000740000828020a01000820a00828040001000840001000240008c24218080a08028200c08040008c08018082000018080c08028200a08028081000528081000228200a080400090002400090002400146242 (by decide +kernel)

def state230_49 : List Sig := [0xffffffff00000000ffffffff00000000ffffffff0000000000000000,input 5,input 6,input 7,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude230_49 : Impossible true (goalAt 230) 5 state230_49.toFinset :=
  node_ok cuts230 [⟨state230_11,exclude230_11⟩] 0x464221200848011908848030200464221200848009080242021200828021200444220a00c24220a00828030108828030202000020a00828008880222020a00c24230200c08020908a02030908a02030908602030200602030200848009080848009080828008880828008880c24228080c24228080c08018080c08018080a080 (by decide +kernel)

def state230_50 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,input 7,input 1,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude230_50 : Impossible true (goalAt 230) 6 state230_50.toFinset :=
  node_ok cuts230 [⟨state230_13,exclude230_13⟩,⟨state230_33,exclude230_33⟩,⟨state230_37,exclude230_37⟩,⟨state230_47,exclude230_47⟩,⟨state230_49,exclude230_49⟩] 0x1000518908624230908a08028202000328200a08030908624218909000428200a08030200624230202000218908624230200a08028202000409818260640008a08028202000128200a08040008260609818260621200848028200242028200260609080242028200848021201000511908464230908848021201000321200848030908464211909000421200848030200464230201000311908464230200848021201000309080242040004848021201000321200848040004242009080624220a00828028200222028200624208880604228200828020a00464220a0082802120100072120046424000c444221200828020a00c24208880c24230100828020a00c24220a00828030100222030109000420a00828030201000430201000740012000030200828020a01000708880222040000828020a01000720a00828040000222008881000440010a02030909000530909000430200c080400110004209090004400146020 (by decide +kernel)

def state230_51 : List Sig := roots 230
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude230_51 : Impossible true (goalAt 230) 7 state230_51.toFinset :=
  node_ok cuts230 [⟨state230_9,exclude230_9⟩,⟨state230_19,exclude230_19⟩,⟨state230_27,exclude230_27⟩,⟨state230_30,exclude230_30⟩,⟨state230_38,exclude230_38⟩,⟨state230_48,exclude230_48⟩,⟨state230_50,exclude230_50⟩] 0x40014c24218080c24240010a02030200c08080018c24230200c08040010a02018080824240014a02018908624240008c24228200a08080014a02028200a08040008c24218908624240010602028200a08040008c08018908c08080010602018908624240008c08028200a08040014860611908464240004c2422120084808000c860621200848040004c24211908464240010460621200848040004c08011908c0804000c460611908464240004c08021200848040008260621200848040004a08009080a08080008260609080242040004a08021200848040000c24208880c24240000c04020a00828040000c24220a00828040000c04008880c04240000460620a00828040000c08040000c08040000460680004440640000c08020a00828040000624220a00828040000a08008880a08040000624208880604240000a08020a00828040000464220a00828040000848040000848040000464280000444240000848020a008280 (by decide +kernel)

theorem lower230 : Claim 230 8 :=
  fromSearch 303039824 (by decide +kernel) exclude230_51

theorem lower246 : Claim 246 9 :=
  fromLift 9 16 303105344 lower230 (by decide +kernel)

theorem lower243 : Claim 243 9 :=
  fromLift 9 2 68 lower241 (by decide +kernel)

theorem lower212 : Claim 212 5 :=
  fromLift 5 16 570885632 lower196 (by decide +kernel)

theorem lower197 : Claim 197 5 :=
  fromLift 5 1 1542 lower196 (by decide +kernel)

theorem lower149 : Claim 149 5 :=
  fromLift 5 4 1796 lower145 (by decide +kernel)

def rule213_0 : {c : Cut // CutGood (goalAt 213) c} :=
  ruleFor 213 lower209 none (by decide +kernel)

def rule213_1 : {c : Cut // CutGood (goalAt 213) c} :=
  ruleFor 213 lower212 none (by decide +kernel)

def rule213_2 : {c : Cut // CutGood (goalAt 213) c} :=
  ruleFor 213 lower197 none (by decide +kernel)

def rule213_3 : {c : Cut // CutGood (goalAt 213) c} :=
  ruleFor 213 lower149 none (by decide +kernel)

def cuts213 : Cuts (goalAt 213) := [rule213_0,rule213_1,rule213_2,rule213_3]

def state213_0 : List Sig := roots 213
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude213_0 : Impossible true (goalAt 213) 6 state213_0.toFinset :=
  node_ok cuts213 [] 0x4000cd05015050d0504000c941430200c0804000cd05030200c0804000c941415050905040008d05005414d05040008c04024200908040008d05024200908040008c04005414c05040008541424200908040008c08040008c0804000854144000c441440008c08024200908040000941415140545040000d05021200848040000941421200848040000d05015140545040000541421200848040000c08015140c08040000541415140545040000c08021200848040000150521200848040000908015140908040000150515140545040000908021200848040004850514540515040004d05020600818040004850520600818040004d05014540515040004450520600818040004c08014540c08040004450514540515040004c080206008180400081505206008180400089080145409080400081505145405150400089080206008180400010000206008180400008480054508480400010001054501514400008480206008180 (by decide +kernel)

theorem lower213 : Claim 213 7 :=
  fromSearch 1540 (by decide +kernel) exclude213_0

def cuts146 : Cuts (goalAt 146) := []

def state146_0 : List Sig := roots 146
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude146_0 : Impossible true (goalAt 146) 3 state146_0.toFinset :=
  node_ok cuts146 [] 0x24040120224040820224200908024040908024200820204808120220808121004840901020a00828020808828020a00901004840121004808828020a00908004840908004808121004840908020a008280 (by decide +kernel)

theorem lower146 : Claim 146 4 :=
  fromSearch 268501056 (by decide +kernel) exclude146_0

theorem lower210 : Claim 210 5 :=
  fromLift 5 64 385941568 lower146 (by decide +kernel)

theorem lower150 : Claim 150 5 :=
  fromLift 5 4 268502848 lower146 (by decide +kernel)

def rule214_0 : {c : Cut // CutGood (goalAt 214) c} :=
  ruleFor 214 lower210 none (by decide +kernel)

def rule214_1 : {c : Cut // CutGood (goalAt 214) c} :=
  ruleFor 214 lower198 none (by decide +kernel)

def rule214_2 : {c : Cut // CutGood (goalAt 214) c} :=
  ruleFor 214 lower150 none (by decide +kernel)

def rule214_3 : {c : Cut // CutGood (goalAt 214) c} :=
  ruleFor 214 lower212 none (by decide +kernel)

def cuts214 : Cuts (goalAt 214) := [rule214_0,rule214_1,rule214_2,rule214_3]

def state214_0 : List Sig := roots 214
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude214_0 : Impossible true (goalAt 214) 6 state214_0.toFinset :=
  node_ok cuts214 [] 0x40008d05015050d05040008941430200c08040008d05030200c08040008941415050905040004d05014908d05040004c24224200908040004d05024200908040004c24214908c05040004541424200908040004c08014908c08040004541414908524240004c08024200908040000941415140545040000d05021200848040000941421200848040000d05015140545040000541421200848040000c08015140c08040000541415140545040000c0802120084804000016062120084804000090801514090804000016061514054504000090802120084804000cc2421494052504000cd05020a0082804000cc24220a0082804000cd05014940525040008460620a00828040008c08014940c08040008460614940525040008c08020a00828040004524220a00828040004908014940908040004524214940525040004908020a00828040000464220a00828040000848005850848040000464205850444240000848020a008280 (by decide +kernel)

theorem lower214 : Claim 214 7 :=
  fromSearch 302057024 (by decide +kernel) exclude214_0

theorem lower195 : Claim 195 5 :=
  fromLift 5 2 118 lower193 (by decide +kernel)

theorem lower147 : Claim 147 5 :=
  fromLift 5 1 68 lower146 (by decide +kernel)

def rule211_0 : {c : Cut // CutGood (goalAt 211) c} :=
  ruleFor 211 lower209 none (by decide +kernel)

def rule211_1 : {c : Cut // CutGood (goalAt 211) c} :=
  ruleFor 211 lower210 none (by decide +kernel)

def rule211_2 : {c : Cut // CutGood (goalAt 211) c} :=
  ruleFor 211 lower195 none (by decide +kernel)

def rule211_3 : {c : Cut // CutGood (goalAt 211) c} :=
  ruleFor 211 lower147 none (by decide +kernel)

def cuts211 : Cuts (goalAt 211) := [rule211_0,rule211_1,rule211_2,rule211_3]

def state211_0 : List Sig := roots 211
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude211_0 : Impossible true (goalAt 211) 6 state211_0.toFinset :=
  node_ok cuts211 [] 0x4000cd05010c0cd0504000c901030200c0804000cd05030200c0804000c901010c0c905040008d05014908d05040008c24224200908040008d05024200908040008c24214908c05040009000224200908040008c08014908c08040009000214908524240008c08024200908040000c24214940525040000d05020a00828040000c24220a00828040000d05014940525040000430320a00828040000c08014940c08040000430314940525040000c08020a00828040000524220a00828040000908014940908040000524214940525040000908020a00828040004830314540515040004d05020600818040004830320600818040004d05014540515040004430320600818040004c08014540c08040004430314540515040004c08020600818040008130320600818040008908014540908040008130314540515040008908020600818040001000020600818040000828010d08828040001000110d084342400008280206008180 (by decide +kernel)

theorem lower211 : Claim 211 7 :=
  fromSearch 68 (by decide +kernel) exclude211_0

theorem lower151 : Claim 151 6 :=
  fromLift 6 1 1860 lower150 (by decide +kernel)

theorem lower199 : Claim 199 6 :=
  fromLift 6 1 1654 lower198 (by decide +kernel)

def cuts85 : Cuts (goalAt 85) := []

def state85_0 : List Sig := roots 85
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude85_0 : Impossible true (goalAt 85) 3 state85_0.toFinset :=
  node_ok cuts85 [] 0x150504505110504414150505450151404105111005450151404450054505150145401514105005150145404150145405450054505150 (by decide +kernel)

theorem lower85 : Claim 85 4 :=
  fromSearch 1540 (by decide +kernel) exclude85_0

theorem lower87 : Claim 87 5 :=
  fromLift 5 2 1604 lower85 (by decide +kernel)

def rule215_0 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower213 none (by decide +kernel)

def rule215_1 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower214 none (by decide +kernel)

def rule215_2 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower211 none (by decide +kernel)

def rule215_3 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower151 none (by decide +kernel)

def rule215_4 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower199 none (by decide +kernel)

def rule215_5 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower87 none (by decide +kernel)

def rule215_6 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower150 none (by decide +kernel)

def rule215_7 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower149 none (by decide +kernel)

def rule215_8 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower147 none (by decide +kernel)

def rule215_9 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower198 none (by decide +kernel)

def rule215_10 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower197 none (by decide +kernel)

def rule215_11 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower195 none (by decide +kernel)

def rule215_12 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower196 none (by decide +kernel)

def rule215_13 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower193 none (by decide +kernel)

def rule215_14 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower146 none (by decide +kernel)

def rule215_15 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower145 none (by decide +kernel)

def cuts215 : Cuts (goalAt 215) := [rule215_0,rule215_1,rule215_2,rule215_3,rule215_4,rule215_5,rule215_6,rule215_7,rule215_8,rule215_9,rule215_10,rule215_11,rule215_12,rule215_13,rule215_14,rule215_15]

def state215_0 : List Sig := [0x5555555555555555555555555555555555555555555555555555000055550000,input 7,input 4,input 6,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_0 : Impossible true (goalAt 215) 5 state215_0.toFinset :=
  node_ok cuts215 [] 0x21200c08015140848021200908015140848015140848021200545020a00848011108828020a00c08014940828020a00908014940828014940828020a00525034140c08030200905024200c08014908908034140908024200c05020600151421200818020600434220a008180206005150302008180206005150242008180145408180206005150 (by decide +kernel)

def state215_1 : List Sig := [0x3333333333333333333333333333333333333333333333333333000033330000,input 7,input 4,input 6,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_1 : Impossible true (goalAt 215) 5 state215_1.toFinset :=
  node_ok cuts215 [] 0x21200c08015140848021200908015140848015140848021200545020600848005450818020600c08014540818020600908014540818014540818020600515034140c08030200905024200c08014908908034140908024200c05020a00444221200828020600434220600828020a00525030200828020a00525024200828014940828020a005250 (by decide +kernel)

def state215_2 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0000,input 7,input 4,input 6,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_2 : Impossible true (goalAt 215) 5 state215_2.toFinset :=
  node_ok cuts215 [] 0x20a00c08014940828020a00908014940828014940828020a00525020600828010d08818020600c08014540818020600908014540818014540818020600515034140c08030200905024200c08014908908034140908024200c05020a00444220a008480206001514206008480212005450302008480212005450242008480151408480212005450 (by decide +kernel)

def state215_3 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffffffff0000ffff0000,input 7,input 4,input 6,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_3 : Impossible true (goalAt 215) 6 state215_3.toFinset :=
  node_ok cuts215 [⟨state215_0,exclude215_0⟩,⟨state215_1,exclude215_1⟩,⟨state215_2,exclude215_2⟩] 0x848030200545021200848024200545021200545021200848015142000221200848040008828021200444220a00828030200525020a00828024200525020a00525020a00828014942000120a00828040000818021200151420600818020a00434220600818030200515020600818024200515020600515020600818014542000020600818040004d05030200c08024140470724200c08014908908034140908024200c05005c1c8707 (by decide +kernel)

def state215_4 : List Sig := [0xffffffffffffffffffff0000ffff0000,input 7,input 4,input 6,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_4 : Impossible true (goalAt 215) 6 state215_4.toFinset :=
  node_ok cuts215 [] 0x848030200545021200848024200545021200545021200848015140828021200444220a00828030200525020a00828024200525020a00525020a00828014940818021200151420600818020a00434220600818030200515020600818024200515020600515020600818014540541430200c08015050908030200524224200524224200908014908545021200545021200525020a00525020a00515020600515020600541430200541430200524224200524224200d050 (by decide +kernel)

def state215_5 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 7,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 6,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_5 : Impossible true (goalAt 215) 6 state215_5.toFinset :=
  node_ok cuts215 [] 0x21200545015140848021200908015140848015140848021200545011908848021200445020a00848011108828020a00525014940828020a00908014940828014940828020a00525014908828020a01000720600848005450818020600828010d08818020600515014540818020600908014540818014540818020600515010d08818020600434230200c05025050905024140524215050524211050c0502420090802105052422420090804000cc242 (by decide +kernel)

def state215_6 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 4,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_6 : Impossible true (goalAt 215) 6 state215_6.toFinset :=
  node_ok cuts215 [] 0x21200545015140848021200c08015140848015140848021200545015050848021201000820a00848011108828020a00525014940828020a00c08014940828014940828020a00525005850828020a00161420600848005450818020600828010d08818020600515014540818020600c08014540818014540818020600515005450818020600151424200905024908905030140541414908524211050905030200c08020908541430200c080400109414 (by decide +kernel)

def state215_7 : List Sig := [0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 4,input 6,input 0,input 1,input 2,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_7 : Impossible true (goalAt 215) 7 state215_7.toFinset :=
  node_ok cuts215 [⟨state215_3,exclude215_3⟩,⟨state215_4,exclude215_4⟩,⟨state215_5,exclude215_5⟩,⟨state215_6,exclude215_6⟩] 0x94141514054503414084802120094142120084803414054501514054142120084804002054501514054141514054504000c848021201000421200848014908545015141000815140545014908848021201000821200848040008545015141000815140545040008848021200c24214940525034140828020a00c24220a00828034140525014940464220a00828021200161421200464205850444221200828020a01000320a00828015050525014941000714940525015050828020a00524220a0082804001c525014940524214940525040010828020a01000720a00828040000525014941000714940525040000828020a00870714540515034140818020600870720600818034140515014541000820600818021200151421201000605450151421200818020601000720600818020a00434220a01000610d08434220a00818020601000320600818015050515014541000614540515015050818020601000420600818014908515014541000614540515014908818020601000620600818040004515014541000614540515040004818020600d05015050d05025051000325050d0508000c905025050541424141000340010c08034140524234140c24240010c24234142000230140c24214908c0501505100031505100041490852424000d00031105100034000c9080341410005341408707800048707341420000341408707400148707 (by decide +kernel)

def state215_8 : List Sig := [0x3333333333333333333333333333333333330000333300003333000033330000,input 4,input 7,input 0,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_8 : Impossible true (goalAt 215) 6 state215_8.toFinset :=
  node_ok cuts215 [] 0x34140541434140941430200c08034140c08030200941415050905015050848021200c08015140c08015050545015140c08021200848025050545015140d05021200848025050848021200d05015140545005c1c848021200908015140908005c1c54501514090802120084801141c818020600c08014540c0801141c515014540c08020600818040034818020600848005450848040030151405450848020600818021c1c515014540d05020600818021c1c818020600d05014540515005c1c818020600908014540908005c1c515014540908020600818015050908024200c08014908c08015050524214908c08024200908034140524234140c24224200908034140908024200c24214908c05030200828020a00450714940525030200525030200450720a00828021200828020a00444205850444221200161421200444220a00828020600828020600434240030434220601000c20600434220a00828034140525014940c24220a00828034140828020a00c24214940525024200828020a00524214940525024200525024200524220a008280 (by decide +kernel)

def state215_9 : List Sig := [0x3333333333333333333333333333333333330000333300003333000033330000,0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 4,input 7,input 0,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_9 : Impossible true (goalAt 215) 6 state215_9.toFinset :=
  node_ok cuts215 [] 0x34140c0803020090501141cc08030200450721200c08015140848015140848021200545021200908015140848011108848021200444220600c08014540818020600848005450818014540818020600515020600908014540818010d08818020600434230908908030200541424200d05024200c05014908828014940c08020a00828011108848020a00818010d08818020a00525020a00828014940828014940908020a010000 (by decide +kernel)

def state215_10 : List Sig := [0xffffffffffffffff0000000000000000ffff0000ffff0000,input 6,input 4,input 7,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_10 : Impossible true (goalAt 215) 6 state215_10.toFinset :=
  node_ok cuts215 [] 0x545021200848015140848024200545021200848015140545021200828021200444220a00525020a00828014940828024200525020a00828014940525020a00818021200151420600818020a00434220600515020600818014540818024200515020600818014540515020600d05024200908030140908014908524224200d05025050d05025050848015140848015140828014940828014940818014540818014540941434140941434140908014908908014908c080 (by decide +kernel)

def state215_11 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 4,input 7,input 0,input 1,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_11 : Impossible true (goalAt 215) 7 state215_11.toFinset :=
  node_ok cuts215 [⟨state215_5,exclude215_5⟩,⟨state215_3,exclude215_3⟩,⟨state215_8,exclude215_8⟩,⟨state215_9,exclude215_9⟩,⟨state215_10,exclude215_10⟩] 0xd05015050d05025050c08030200d05030200c08025050541424142000411c1c47074000cc08030202000130200c0804000c470711c1c541421200848030200545030200541415140545030200848021200941415140545034140848021200941421200848034140545015141000421200848024200545024201000b15140545024200848021201000b11908464240008848021201000b21200848040008464211908470720a00828030200525030200470714940525030200828020a00464220a00828021200161421200464205850444221200828020a01000a14940525034140828020a01000a20a00828034140525014941000420a00828024200525024201000a14940525024200828020a01000a8000e000240000828020a01000a20a00828040001000a40000470720600818030200515030200470714540515030200818020601000b20600818021200151421201000905450151421200818020601000a20600818020a00434220a01000910d08434220a00818020601000914540515034140818020601000920600818034140515014541000420600818024200515024201000914540515024200818020601000910d08434240004818020601000920600818040004434210d09000440010c24215050908024200c08040010c08015052000015050c080242009080341410005341410004242009080400110004301410004400145242 (by decide +kernel)

def state215_12 : List Sig := [0xf0f0f0f0f0f0f0f00000f0f00000f0f0f0f0f0f0f0f0f0f0000000000000000,input 6,input 4,input 7,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_12 : Impossible true (goalAt 215) 5 state215_12.toFinset :=
  node_ok cuts215 [] 0x14940828020a00525020a00525014940828020a00c08014940828020600828010d08818014540818020600515020600515014540818020600c08014540818034140c24230140c05034200c08014908c08034140c08030200824220a00444220a008480206001514206008480151408480212005450212005450242008480212005450302008480 (by decide +kernel)

def state215_13 : List Sig := [0xffffffffffffffff0000ffff0000ffffffffffffffffffff0000000000000000,input 6,input 4,input 7,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_13 : Impossible true (goalAt 215) 6 state215_13.toFinset :=
  node_ok cuts215 [⟨state215_12,exclude215_12⟩] 0x545021200848015140848015140545021200848030200545021202000021200848040008828021200444220a00525020a00828014940828014940525020a00828030200525020a00161420a00828005850818021200151420600818020a00434220600515020600818014540818014540515020600818030200515020600151420600818005450d05030908c05030140d08030200524230200170714908908024200d05030200c080209085414341409414341409414 (by decide +kernel)

def state215_14 : List Sig := [0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000,input 4,input 7,input 0,input 1,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_14 : Impossible true (goalAt 215) 7 state215_14.toFinset :=
  node_ok cuts215 [⟨state215_13,exclude215_13⟩] 0xd05015050d05025050c08030200d05030200c08025050541424140541421200848030200545030200541415140545030200848021200941415140545034140848021200941421200848034140545015140170721200848014908545015140170715140545014908848021200470720a00828030200525030200470714940525030200828020a00464220a00828021200161421200464205850444221200828020a01000514940525034140828020a01000a20a00828034140525014940524220a00828005414525014940524214940525005414828020a00470720600818030200515030200470714540515030200818020601000b20600818021200151421201000905450151421200818020601000a20600818020a00434220a01000910d08434220a00818020601000514540515034140818020601000920600818034140515014540170720600818014908515014540170714540515014908818020600541405c1c541430200524230200541414908524230200170730201000440010d2423414100053414100041490852423020100033020054144001454143020200003020054144000c541421201000221200545040014545021201000b21200545040008545020a01000020a00525040014525020a01000a20a005250400005250206010001206005150400145150206010009206005150400045150400110004309090005400109080 (by decide +kernel)

def state215_15 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0000000000000000,input 6,input 7,input 0,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_15 : Impossible true (goalAt 215) 6 state215_15.toFinset :=
  node_ok cuts215 [] 0x34140524234140c24224200908034140908024200c24214908c05015050908024200c08014908c08015050524214908c08024200908014908828020a00908014940908014908525014940908020a00828030908525014940d05020a00828030908828020a00d05014940525011c1c828020a00c08014940c08011c1c525014940c08020a00828004c1c818020600908014540908004c1c51501454090802060081804003c818020600828010d08828040038434210d08828020600818021c1c515014540d05020600818021c1c818020600d05014540515011c1c818020600c08014540c08011c1c515014540c08020600818034140541434140941430200c08034140c08030200941415050905024200848021200130715140545024200545024200130721200848020a00848020a00161411908444220a00464220a00161421200848020600848020600151440038151420601000e206001514212008480341405450151409414212008480341408480212009414151405450302008480212005414151405450302005450302005414212008480 (by decide +kernel)

def state215_16 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,input 7,input 0,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_16 : Impossible true (goalAt 215) 6 state215_16.toFinset :=
  node_ok cuts215 [] 0x34140908024200c05024200c08014908908004c1c908024200130720a00908014940828014940828020a00525020a00c08014940828005850828020a00161420600908014540818020600828010d08818014540818020600515020600c08014540818005450818020600151425050d05030200905015050848015140908021200828011108828021200818005450818021200545021200848015140848015140c080212010002 (by decide +kernel)

def state215_17 : List Sig := [0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000,input 4,input 6,input 7,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_17 : Impossible true (goalAt 215) 6 state215_17.toFinset :=
  node_ok cuts215 [] 0x545021200848015140848030200545021200848015140545021200828021200444220a00525020a00828014940828030200525020a00828014940525020a00818021200151420600818020a00434220600515020600818014540818030200515020600818014540515020600d05030200c08024140d05030908d05030908541430200541430200848015140848015140828014940828014940818014540818014540c24234140c24234140c08015050c080150509080 (by decide +kernel)

def state215_18 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,input 7,input 0,input 1,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_18 : Impossible true (goalAt 215) 7 state215_18.toFinset :=
  node_ok cuts215 [⟨state215_3,exclude215_3⟩,⟨state215_6,exclude215_6⟩,⟨state215_15,exclude215_15⟩,⟨state215_16,exclude215_16⟩,⟨state215_17,exclude215_17⟩] 0xd05014908d05030908908024200d05024200908030908524230141000324200908030200524230202000114908524230200908024202000405c1c170740010908024202000024200908040010170705c1c17072120084802420054502420017071514054502420084802120100081514054503414084802120100082120084803414054501514100032120084803020054503020100081514054503020084802120100088000e000240008848021201000821200848040009000840008524220a00828024200525024200524214940525024200828020a00464220a00828021200161421200464205850444221200828020a00c24214940525034140828020a00c24220a00828034140525014941000320a00828030200525030201000714940525030200828020a01000705850161440000828020a01000720a00828040000161405850170720600818024200515024200170714540515024200818020601000820600818021200151421201000605450151421200818020601000720600818020a00434220a01000610d08434220a0081802060100061454051503414081802060100062060081803414051501454100032060081803020051503020100061454051503020081802060100060545015144000481802060100062060081804000415140545100034000c941434141000534141000330200c0804000d0003241410003400145414 (by decide +kernel)

def state215_19 : List Sig := [0x3333000033330000333333333333333333330000333300003333000033330000,input 4,input 6,input 7,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_19 : Impossible true (goalAt 215) 5 state215_19.toFinset :=
  node_ok cuts215 [] 0x15140848021200545021200545015140848021200908015140848020600848005450818014540818020600515020600515014540818020600908014540818034140941424140905034140908024200524224200d08014908908020a00444221200828020600434220600828014940828020a00525020a00525030200828020a005250242008280 (by decide +kernel)

def state215_20 : List Sig := [0xffff0000ffff0000ffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 4,input 6,input 7,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_20 : Impossible true (goalAt 215) 6 state215_20.toFinset :=
  node_ok cuts215 [⟨state215_19,exclude215_19⟩] 0x545021200848015140848015140545021200848024200545021200464221200848011908828021200444220a00525020a00828014940828014940525020a00828024200525020a02000020a00828040000818021200151420600818020a00434220600515020600818014540818014540515020600818024200515020600434220600818010d08d05025050905024140d05024200908030908908034200541424200524234140c24234140c24215050470730200c080 (by decide +kernel)

def state215_21 : List Sig := [0xffffffffffffffff00000000000000000000000000000000,input 6,input 7,input 0,input 1,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_21 : Impossible true (goalAt 215) 7 state215_21.toFinset :=
  node_ok cuts215 [⟨state215_20,exclude215_20⟩] 0xd05014908d05030908908024200d05024200908030908524230140541424200908011c1c524214908541414908524211c1c908024200170721200848024200545024200170715140545024200848021201000815140545034140848021201000821200848034140545015140541421200848010c0c545015140541415140545010c0c848021200524220a00828024200525024200524214940525024200828020a00464220a00828021200161421200464205850444221200828020a00c24214940525034140828020a00c24220a00828034140525014940470720a00828015050525014940470714940525015050828020a00170720600818024200515024200170714540515024200818020601000820600818021200151421201000605450151421200818020601000720600818020a00434220a01000610d08434220a0081802060100061454051503414081802060100062060081803414051501454047072060081801505051501454047071454051501505081802060100034000cd41434141000534141000315050541424201000424200524240014524224202000024200524240010524221201000221200545040020545021201000821200545040008545020a01000020a0052504001c525020a01000720a0052504000052502060100012060051504001851502060100062060051504000451504000d00032505100054000cc080 (by decide +kernel)

def state215_22 : List Sig := roots 215
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_22 : Impossible true (goalAt 215) 8 state215_22.toFinset :=
  node_ok cuts215 [⟨state215_7,exclude215_7⟩,⟨state215_11,exclude215_11⟩,⟨state215_14,exclude215_14⟩,⟨state215_18,exclude215_18⟩,⟨state215_21,exclude215_21⟩] 0x80010d05015050d0504000c941430200c0808000cd05030200c0804000c941415050905080008d05014908d05040010c24224200908080004d05024200908040010c24214908c0504000c541424200908040010c08014908c0808000054141490852424000cc08024200908040008941415140545040008d05021200848040008941421200848040008d05015140545040008541421200848040008c08015140c08040008541415140545040008c08021200848040008170721200848040008908015140908040008170715140545040008908021200848040000c24214940525040000d05020a00828040000c24220a00828040000d05014940525040000470720a00828040000c08014940c08040000470714940525040000c08020a00828040000524220a00828040000908014940908040000524214940525040000908020a00828040000464220a00828040000848005850848040000464205850444240000848020a00828040004870714540515040004d05020600818040004870720600818040004d05014540515040004470720600818040004c08014540c08040004470714540515040004c08020600818040004170720600818040004908014540908040004170714540515040004908020600818040009000220600818040008848005450848040009000105450151440008848020600818040001000020600818040000828010d08828040001000110d084342400008280206008180 (by decide +kernel)

theorem lower215 : Claim 215 9 :=
  fromSearch 1604 (by decide +kernel) exclude215_22

theorem lower231 : Claim 231 9 :=
  fromLift 9 1 1365 lower230 (by decide +kernel)

theorem lower101 : Claim 101 5 :=
  fromLift 5 1 1285 lower100 (by decide +kernel)

def cuts53 : Cuts (goalAt 53) := []

def state53_0 : List Sig := roots 53
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude53_0 : Impossible true (goalAt 53) 3 state53_0.toFinset :=
  node_ok cuts53 [] 0xd05025050905024140d05034300d0c021050908034300d0c024300545031300c4c015140848031300c4c021300c4c03430054503130 (by decide +kernel)

theorem lower53 : Claim 53 4 :=
  fromSearch 1284 (by decide +kernel) exclude53_0

def rule117_0 : {c : Cut // CutGood (goalAt 117) c} :=
  ruleFor 117 lower113 none (by decide +kernel)

def rule117_1 : {c : Cut // CutGood (goalAt 117) c} :=
  ruleFor 117 lower100 none (by decide +kernel)

def rule117_2 : {c : Cut // CutGood (goalAt 117) c} :=
  ruleFor 117 lower101 none (by decide +kernel)

def rule117_3 : {c : Cut // CutGood (goalAt 117) c} :=
  ruleFor 117 lower85 none (by decide +kernel)

def rule117_4 : {c : Cut // CutGood (goalAt 117) c} :=
  ruleFor 117 lower53 none (by decide +kernel)

def cuts117 : Cuts (goalAt 117) := [rule117_0,rule117_1,rule117_2,rule117_3,rule117_4]

def state117_0 : List Sig := [0xffffffffffffffffffffffffffff0000ffffffffffffffffffffffffffff0000,input 6,input 5,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude117_0 : Impossible true (goalAt 117) 4 state117_0.toFinset :=
  node_ok cuts117 [] 0x1514060500d0c054500d0c054501514034300541454501514011051454054500545051501454060500c4c051500c4c05150145403130054145150145410001180c06050181402414094144505 (by decide +kernel)

def state117_1 : List Sig := [0xffffffffffff00000000000000000000ffffffffffff0000,input 6,input 5,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude117_1 : Impossible true (goalAt 117) 4 state117_1.toFinset :=
  node_ok cuts117 [] 0x54501814034301514034301514054500d0c051501514015141454051501814031301454031301454051500c4c02414181406050090503430151403430151403130145403130145402414181402414181406030 (by decide +kernel)

def state117_2 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 5,input 0,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude117_2 : Impossible true (goalAt 117) 5 state117_2.toFinset :=
  node_ok cuts117 [⟨state117_0,exclude117_0⟩,⟨state117_1,exclude117_1⟩] 0x54140d0c03430180c05450151405414151405450180c034300d0c024141514054501814034301814024140d0c034301814054501514015051110044400440454501514015051514054500440444401114045050c4c03130180c05150145404505145405150180c031300c4c100011454051501514015141514100010545015141514051501454100011454051501814031301814100010c4c03130181405150145401505105004140400045150145401505145405150400044140105406030090506030150506050181406030181406050150502414090510002400086040180c01505180c04505800044505180c20000180c04505054144414 (by decide +kernel)

def state117_3 : List Sig := [0xffffffff00000000ffff000000000000ffffffff00000000ffff0000,input 5,input 6,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude117_3 : Impossible true (goalAt 117) 4 state117_3.toFinset :=
  node_ok cuts117 [] 0x34301514054500d0c054500d0c034301514051501514015141454031301454051500c4c051500c4c031301454060301105060301105054500d0c054500d0c051500c4c051500c4c04414180c04414180c06050 (by decide +kernel)

def state117_4 : List Sig := [0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 6,input 0,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude117_4 : Impossible true (goalAt 117) 5 state117_4.toFinset :=
  node_ok cuts117 [⟨state117_0,exclude117_0⟩,⟨state117_3,exclude117_3⟩] 0x60300d05060301105060501814060301814060501105034140d05200010941425050541460501814200001814060500541425050905034141514054501814034301814034140d0c034301814054501514044140d0c03430180c05450151404414151405450180c034300d0c01505090802420044045450151401505151405450044042420090c025051454051501814031301814025050c4c031301814051501454100011454051501514015141514100010545015141514051501454100010c4c03130180c05150145410001145405150180c031300c4c01505084802120400045150145401505145405150400042120084c10002400086020 (by decide +kernel)

def state117_5 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f0f0f0f0f0f0f0f0f00000000,input 5,input 6,input 0,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude117_5 : Impossible true (goalAt 117) 4 state117_5.toFinset :=
  node_ok cuts117 [] 0x1c0c06020180c060301c14060401814060501050051501454041500c4c051501454031301454070500c4c051501c0c070501c14034141114054501514044401454015141454054500d0c054501514034301514034301c1405450 (by decide +kernel)

def state117_6 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 5,input 6,input 0,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude117_6 : Impossible true (goalAt 117) 5 state117_6.toFinset :=
  node_ok cuts117 [⟨state117_0,exclude117_0⟩,⟨state117_5,exclude117_5⟩] 0x7030180806030180c070501810060501814015054000a00000541444401514054501114034301514054500d0c054501c14034301514200011514054504000041401454051501054051501514015141454031301454051500c4c051501c14031301454015141454051500545054141c0c070504000c3414 (by decide +kernel)

def state117_7 : List Sig := roots 117
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude117_7 : Impossible true (goalAt 117) 6 state117_7.toFinset :=
  node_ok cuts117 [⟨state117_2,exclude117_2⟩,⟨state117_4,exclude117_4⟩,⟨state117_6,exclude117_6⟩] 0x4001070300d05070304000c54141c14070508000870301c14070504000c54140d05034144000870300541470304000860204000860204000870308000460304000860200541460304000870500541470504000860404000860404000870508000060504000860400541460504000054140d0c034304000070301514054504000054141514054504000070300d0c034304000034141514054504000070500d0c070504000034140d0c034304000070501514054504000015051110044404000011011514054504000015051514054504000011011110044504000445050c4c031304000470301454051504000445051454051504000470300c4c031304000425051454051504000470500c4c070504000425050c4c03130400047050145405150400081505105004140400090001145405150400081505145405150400090002105004150400010000145405150400005450054505450400010001054501514400005450145405150 (by decide +kernel)

theorem lower117 : Claim 117 7 :=
  fromSearch 1284 (by decide +kernel) exclude117_7

def cuts114 : Cuts (goalAt 114) := []

def state114_0 : List Sig := roots 114
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude114_0 : Impossible true (goalAt 114) 3 state114_0.toFinset :=
  node_ok cuts114 [] 0x1c0c070501c14022421c0c052421490860301c14062421814060500c8c05250149403230149407050181085250149085250149402230 (by decide +kernel)

theorem lower114 : Claim 114 4 :=
  fromSearch 85000256 (by decide +kernel) exclude114_0

def cuts54 : Cuts (goalAt 54) := []

def state54_0 : List Sig := roots 54
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude54_0 : Impossible true (goalAt 54) 3 state54_0.toFinset :=
  node_ok cuts54 [] 0xd05026060905024140d05034300d0c022060908034300d0c024300585032300c8c016140888032300c8c022300c8c03430058503230 (by decide +kernel)

theorem lower54 : Claim 54 4 :=
  fromSearch 1115456 (by decide +kernel) exclude54_0

def rule118_0 : {c : Cut // CutGood (goalAt 118) c} :=
  ruleFor 118 lower114 none (by decide +kernel)

def rule118_1 : {c : Cut // CutGood (goalAt 118) c} :=
  ruleFor 118 lower100 none (by decide +kernel)

def rule118_2 : {c : Cut // CutGood (goalAt 118) c} :=
  ruleFor 118 lower102 none (by decide +kernel)

def rule118_3 : {c : Cut // CutGood (goalAt 118) c} :=
  ruleFor 118 lower54 none (by decide +kernel)

def cuts118 : Cuts (goalAt 118) := [rule118_0,rule118_1,rule118_2,rule118_3]

def state118_0 : List Sig := [0x3333333333330000333333333333000033333333333300003333333333330000,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 5,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude118_0 : Impossible true (goalAt 118) 4 state118_0.toFinset :=
  node_ok cuts118 [] 0xd0c054501514034301514060500d0c05450111085450151404442180c060501814024141890860301490852420490032301494052500c8c052501110854501494052500c8c06050149410001 (by decide +kernel)

def state118_1 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 5,input 1,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude118_1 : Impossible true (goalAt 118) 5 state118_1.toFinset :=
  node_ok cuts118 [⟨state118_0,exclude118_0⟩] 0x54140d0c03430180c05450151405414151405450180c034300d0c024141514054501814034301814024140d0c034301814054501514016061190846421490854501514016061514054501490846421114046060c8c03230180c05250149404606149405250180c032300c8c046421494052501514016141514046420585044421514052501494100011494052501814032301814100010c8c03230181405250149405242800005242400045250149405242149405250400050001400046030090506030150506050181406030181406050150502414090510002400086242180c01606180c04606149085242180c05242149084606058184414 (by decide +kernel)

def state118_2 : List Sig := [0xfffffffff0f0f0f00000000000000000fffffffff0f0f0f0,input 2,input 5,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude118_2 : Impossible true (goalAt 118) 4 state118_2.toFinset :=
  node_ok cuts118 [] 0x1c14062421814060501490852501494022301494070501810852501494054501110852501190854501514044501514070500d0c05450180c052421c0c052420c8c052500c8c052500890870501c0c070500d0c054500d0c05450 (by decide +kernel)

def state118_3 : List Sig := [0xfffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0,input 2,input 5,input 1,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude118_3 : Impossible true (goalAt 118) 5 state118_3.toFinset :=
  node_ok cuts118 [⟨state118_2,exclude118_2⟩] 0x7030149085242180c052420981824141490852420581816061490832301494052500c8c05242149405250088c052500c8c032301494052500d0c016141494052500c8c032301494070301505070300d05070500d0c070301505034300908052420d0c052420d05034300881854501c0c200001c0c10003 (by decide +kernel)

def state118_4 : List Sig := [0xffff0f0fffff0000ffff0f0fffff0000ffff0f0fffff0000ffff0f0fffff0000,input 2,input 5,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude118_4 : Impossible true (goalAt 118) 4 state118_4.toFinset :=
  node_ok cuts118 [] 0xc8c052501494032301494060500c8c05250149405450111085250149085250149410001180c060501814034140d0c054501514034301514060500d0c05450119085450151404450180c05242149084414181406242181405242 (by decide +kernel)

def state118_5 : List Sig := [0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000,input 2,input 5,input 1,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude118_5 : Impossible true (goalAt 118) 5 state118_5.toFinset :=
  node_ok cuts118 [⟨state118_4,exclude118_4⟩] 0x7030149085242180c052420981824141490832301494052500c8c05242149405250088c052500c8c032301494052501514044421494070301505070300d05054141514054501c0c046421514054501114074500d05054501c0c054141c0c054144000852428000052420c8c052500c8c052501c1403430 (by decide +kernel)

def state118_6 : List Sig := [0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0,input 2,input 6,input 1,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude118_6 : Impossible true (goalAt 118) 5 state118_6.toFinset :=
  node_ok cuts118 [] 0x34141c14070500d05022021c14070500880870501890860501814054141490852421105012021490852420480852501c1406042149405242149405250088c032301494052500c8c052501514044421494032301494052500c8c070301514070500d0505450119085450151404450150505450400003430 (by decide +kernel)

def state118_7 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f0f0f0f0f0f0f0f0f00000000,input 5,input 6,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude118_7 : Impossible true (goalAt 118) 4 state118_7.toFinset :=
  node_ok cuts118 [] 0x1c0c052421490860301c14062421814060501490852501494022300c8c052501494032301494070501810852501c0c070501c14022421114054501514046421494044421494054500d0c054501514034301514034301c1405450 (by decide +kernel)

def state118_8 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 5,input 6,input 1,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude118_8 : Impossible true (goalAt 118) 5 state118_8.toFinset :=
  node_ok cuts118 [⟨state118_7,exclude118_7⟩] 0x7030149085242180c070501890860501814016061490852420581846421514054501114034301514054500d0c054501c1403430151420000151405450400005242149405250088c052501514044421494032301494052500c8c052501c14060421494016141494052500585054141c0c07050089083414 (by decide +kernel)

def state118_9 : List Sig := [0xffff0000ffff0000ffffffffffff0000ffff0000ffff0000ffffffffffff0000,input 5,input 6,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude118_9 : Impossible true (goalAt 118) 4 state118_9.toFinset :=
  node_ok cuts118 [] 0xd0c054501514034301514070500d0c054501190854501514044501494054501110852500c8c052501494032301494070501810852501490852501494100011c0c070501c14024141c0c052421490860301c1406242181406050 (by decide +kernel)

def state118_10 : List Sig := [0xffffffff000000000000000000000000ffffffff00000000,input 5,input 6,input 1,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude118_10 : Impossible true (goalAt 118) 5 state118_10.toFinset :=
  node_ok cuts118 [⟨state118_9,exclude118_9⟩] 0x54141490852421105070501890860501814046421514054501114034301514054500d0c054501c1403430151405242149405250088c052501514044421494032301494052500c8c052501c14060421494074141c14054144000852428000052420d0c054500d0c054500c8c052500c8c052501c0c03414 (by decide +kernel)

def state118_11 : List Sig := roots 118
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude118_11 : Impossible true (goalAt 118) 6 state118_11.toFinset :=
  node_ok cuts118 [⟨state118_1,exclude118_1⟩,⟨state118_3,exclude118_3⟩,⟨state118_5,exclude118_5⟩,⟨state118_6,exclude118_6⟩,⟨state118_8,exclude118_8⟩,⟨state118_10,exclude118_10⟩] 0x4000c70300d05070308001454141c14070508001070301c14070504000c54140d05022424000870300581870304000860201490852424000870301490852424000860200581860304000870501490870504000862424000862424000870508000060504000862421490860504000c54140d0c034304000070301514054508000c54141514054504000070300d0c034308000834141514054504000070500d0c070508000434140d0c034304000070501514054504000816061190846424000852421514054504000816061514054504000852421190844504000446060c8c032304000470301494052504000446061494052504000470300c8c032304000462421494052504000470500c8c070504000462420c8c06042400047050149405250400085242088805242400090001149405250400085242149405250400090002088802230400004642149405250400045450058505450400044642058504442400005450149405250 (by decide +kernel)

theorem lower118 : Claim 118 7 :=
  fromSearch 34669888 (by decide +kernel) exclude118_11

theorem lower115 : Claim 115 6 :=
  fromLift 6 2 68 lower113 (by decide +kernel)

theorem lower99 : Claim 99 5 :=
  fromLift 5 2 85 lower97 (by decide +kernel)

theorem lower103 : Claim 103 6 :=
  fromLift 6 1 1365 lower102 (by decide +kernel)

def cuts83 : Cuts (goalAt 83) := []

def state83_0 : List Sig := roots 83
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude83_0 : Impossible true (goalAt 83) 3 state83_0.toFinset :=
  node_ok cuts83 [] 0x4c0c524214908124204840525014940125014908525014940110304440515014540115010d08515014540434214540525010d085150 (by decide +kernel)

theorem lower83 : Claim 83 4 :=
  fromSearch 68 (by decide +kernel) exclude83_0

theorem lower55 : Claim 55 5 :=
  fromLift 5 1 1348 lower54 (by decide +kernel)

def rule119_0 : {c : Cut // CutGood (goalAt 119) c} :=
  ruleFor 119 lower117 none (by decide +kernel)

def rule119_1 : {c : Cut // CutGood (goalAt 119) c} :=
  ruleFor 119 lower118 none (by decide +kernel)

def rule119_2 : {c : Cut // CutGood (goalAt 119) c} :=
  ruleFor 119 lower115 none (by decide +kernel)

def rule119_3 : {c : Cut // CutGood (goalAt 119) c} :=
  ruleFor 119 lower99 none (by decide +kernel)

def rule119_4 : {c : Cut // CutGood (goalAt 119) c} :=
  ruleFor 119 lower103 none (by decide +kernel)

def rule119_5 : {c : Cut // CutGood (goalAt 119) c} :=
  ruleFor 119 lower87 none (by decide +kernel)

def rule119_6 : {c : Cut // CutGood (goalAt 119) c} :=
  ruleFor 119 lower102 none (by decide +kernel)

def rule119_7 : {c : Cut // CutGood (goalAt 119) c} :=
  ruleFor 119 lower118 (some (1,input 4,input 5)) (by decide +kernel)

def rule119_8 : {c : Cut // CutGood (goalAt 119) c} :=
  ruleFor 119 lower101 none (by decide +kernel)

def rule119_9 : {c : Cut // CutGood (goalAt 119) c} :=
  ruleFor 119 lower100 none (by decide +kernel)

def rule119_10 : {c : Cut // CutGood (goalAt 119) c} :=
  ruleFor 119 lower117 (some (1,input 4,input 5)) (by decide +kernel)

def rule119_11 : {c : Cut // CutGood (goalAt 119) c} :=
  ruleFor 119 lower85 none (by decide +kernel)

def rule119_12 : {c : Cut // CutGood (goalAt 119) c} :=
  ruleFor 119 lower97 none (by decide +kernel)

def rule119_13 : {c : Cut // CutGood (goalAt 119) c} :=
  ruleFor 119 lower83 none (by decide +kernel)

def rule119_14 : {c : Cut // CutGood (goalAt 119) c} :=
  ruleFor 119 lower55 none (by decide +kernel)

def rule119_15 : {c : Cut // CutGood (goalAt 119) c} :=
  ruleFor 119 lower118 (some (1,input 2,input 5)) (by decide +kernel)

def rule119_16 : {c : Cut // CutGood (goalAt 119) c} :=
  ruleFor 119 lower113 none (by decide +kernel)

def rule119_17 : {c : Cut // CutGood (goalAt 119) c} :=
  ruleFor 119 lower118 (some (3,input 2,input 5)) (by decide +kernel)

def rule119_18 : {c : Cut // CutGood (goalAt 119) c} :=
  ruleFor 119 lower118 (some (1,input 2,input 6)) (by decide +kernel)

def rule119_19 : {c : Cut // CutGood (goalAt 119) c} :=
  ruleFor 119 lower54 none (by decide +kernel)

def rule119_20 : {c : Cut // CutGood (goalAt 119) c} :=
  ruleFor 119 lower53 none (by decide +kernel)

def rule119_21 : {c : Cut // CutGood (goalAt 119) c} :=
  ruleFor 119 lower118 (some (1,input 5,input 6)) (by decide +kernel)

def rule119_22 : {c : Cut // CutGood (goalAt 119) c} :=
  ruleFor 119 lower117 (some (1,input 5,input 6)) (by decide +kernel)

def rule119_23 : {c : Cut // CutGood (goalAt 119) c} :=
  ruleFor 119 lower118 (some (2,input 5,input 6)) (by decide +kernel)

def cuts119 : Cuts (goalAt 119) := [rule119_0,rule119_1,rule119_2,rule119_3,rule119_4,rule119_5,rule119_6,rule119_7,rule119_8,rule119_9,rule119_10,rule119_11,rule119_12,rule119_13,rule119_14,rule119_15,rule119_16,rule119_17,rule119_18,rule119_19,rule119_20,rule119_21,rule119_22,rule119_23]

def state119_0 : List Sig := [0xbbbbbbbbbbbbaaaabbbbbbbbbbbbaaaabbbbbbbbbbbbaaaabbbbbbbbbbbbaaaa,input 0,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 5,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_0 : Impossible true (goalAt 119) 5 state119_0.toFinset :=
  node_ok cuts119 [] 0xd0c054501514034301514060500d0c05450111085450151404442180c060501814024141890860301490852420490031301454051500c4c0515015140151414540515018140313014540150714540515010d4043420c8c052501494032301494044421514052501494032301814052500541c5250149405242 (by decide +kernel)

def state119_1 : List Sig := [0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,0x1111111111110000111111111111000011111111111100001111111111110000,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_1 : Impossible true (goalAt 119) 4 state119_1.toFinset :=
  node_ok cuts119 [] 0x34301514054500d0c044421514054501110854501814034301514060301490852420490031301494052500c4c05250111085450149402407149404342145405150180c0605018140241410d086050181404342 (by decide +kernel)

def state119_2 : List Sig := [0xfafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafa,0x1111111111110000111111111111000011111111111100001111111111110000,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_2 : Impossible true (goalAt 119) 4 state119_2.toFinset :=
  node_ok cuts119 [] 0x180c060501814024141890860301490852420490032301494052500c8c052500c8c060501494100091494043421454051500d0c054501514034301514060500d0c0545010d085450151404342 (by decide +kernel)

def state119_3 : List Sig := [0x1111111111110000111111111111000011111111111100001111111111110000,input 0,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 5,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_3 : Impossible true (goalAt 119) 5 state119_3.toFinset :=
  node_ok cuts119 [⟨state119_1,exclude119_1⟩,⟨state119_2,exclude119_2⟩] 0x34301514054500d0c05450181403430151404442151405450111086030181406050090506242180c052421490812401141c434210d08603010d08545080004545010d08605080000605010d0851420541c43420c8c05250149403230149404442151405250149403230181405250400245150 (by decide +kernel)

def state119_4 : List Sig := [0xfafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafa,0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,0x3333333333330000333333333333000033333333333300003333333333330000,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_4 : Impossible true (goalAt 119) 4 state119_4.toFinset :=
  node_ok cuts119 [] 0x60301490852420490032301494052500c8c01107149403230181405250149404442151405250180c060501814015141890860501814052420c4c054501514031301110854501514044421454051500c4c05450 (by decide +kernel)

def state119_5 : List Sig := [0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,input 0,0x3333333333330000333333333333000033333333333300003333333333330000,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_5 : Impossible true (goalAt 119) 5 state119_5.toFinset :=
  node_ok cuts119 [⟨state119_1,exclude119_1⟩,⟨state119_4,exclude119_4⟩] 0xd0c054501514034301110854501514044421514060500d0c05450180c052421490812400c8c052501494032301494044421514052500541c52508000031301494052500c8c06050149403130144c045070c4c03130151420001151401707149083130149085150180c06050181402414189086050181405242 (by decide +kernel)

def state119_6 : List Sig := [0x5555555500000000555555550000000055555555000000005555555500000000,input 0,0x3333333333330000333333333333000033333333333300003333333333330000,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_6 : Impossible true (goalAt 119) 5 state119_6.toFinset :=
  node_ok cuts119 [] 0x34301514054500d0c044421514054501110860301490852420490032301494052500c8c0525011108545014940150714540434214540525014940323018140525005450515014540315014540545005450515010d085150145404342180c060501814024141814054500d0c05450189083130 (by decide +kernel)

def state119_7 : List Sig := [0xfafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafa,input 0,0x3333333333330000333333333333000033333333333300003333333333330000,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_7 : Impossible true (goalAt 119) 5 state119_7.toFinset :=
  node_ok cuts119 [⟨state119_4,exclude119_4⟩,⟨state119_2,exclude119_2⟩] 0x6030181406050090506242180c052421490812400c8c052501494032301494032301814052500441c5250800041514149405250111085450149401514180c04107180c015141814200001814013071490815141490851500d0c054501514034301514060500d0c05450111085450151404442 (by decide +kernel)

def state119_8 : List Sig := [0x5050505050505050505050505050505050505050505050505050505050505050,input 0,0x3333333333330000333333333333000033333333333300003333333333330000,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_8 : Impossible true (goalAt 119) 5 state119_8.toFinset :=
  node_ok cuts119 [] 0x6030181406050090506242180c052421490812400c8c052501494032301494032301814052500441c515010d0851501494052501110854501494031301454051500c4c0515018140313014540434214540515010d0834301514054500d0c05450181403430151404442151405450111081514 (by decide +kernel)

def state119_9 : List Sig := [0x3333333333330000333333333333000033333333333300003333333333330000,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 5,input 0,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_9 : Impossible true (goalAt 119) 6 state119_9.toFinset :=
  node_ok cuts119 [⟨state119_0,exclude119_0⟩,⟨state119_3,exclude119_3⟩,⟨state119_5,exclude119_5⟩,⟨state119_6,exclude119_6⟩,⟨state119_7,exclude119_7⟩,⟨state119_8,exclude119_8⟩] 0x1505034300d0c060301514054501505054501514060300d0c034300905054501514060500d0c060500905034300d0c0605015140545005c1c444211108524215140545005c1c54501514052421110844421141c31300c4c060301454051501141c51501454060300c4c031308001451501454054500545054508001015140545054501454051508000c51501454060500c4c060508000831300c4c0605014540515005c1c434210d08524214540515005c1c515014540524210d084342180c02414180c05414181406050180c0605018140541409050241440021000818908603005c1c60301141c52421490860301490852421141c17070490060300c8c032301141c52501494060301494052501141c32300c8c0545014940525011108161411108545005850545011108525014940515014940515010d0a000110d08515080000515010d0852501494060501494052504002032300c8c060500c8c06050400285250149410008400201507 (by decide +kernel)

def state119_10 : List Sig := [0xffffffffffff00000000000000000000ffffffffffff00000000000000000000,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 6,input 5,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_10 : Impossible true (goalAt 119) 6 state119_10.toFinset :=
  node_ok cuts119 [] 0x1514060500d0c054500d0c054501514034301190854501514046421190854501514046421494054501110852501494060500c8c052500c8c0525014940323005c1c52501494015070c8c0525014940323014540545005450515014540525010d0851501454060500c4c051500c4c0515014540313010d08515014540434210d08515014540434209050605018140241409c1c241418140605009050170711c1c4414180c05242 (by decide +kernel)

def state119_11 : List Sig := [0xffffffff00000000ffff000000000000ffffffff00000000ffff0000,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 6,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_11 : Impossible true (goalAt 119) 5 state119_11.toFinset :=
  node_ok cuts119 [] 0xd0c054501514034301190854501514044501494054501110852500c8c0525014940323014908525014940250714540545005450515014540525010d0851500c4c0515014540313010d085150145404342180c05242149084414151403430151406050149403230149406050145403130145406050090506050181406030149086050181406242 (by decide +kernel)

def state119_12 : List Sig := [0x5555555555555555555555555555000055555555555555555555555555550000,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 6,input 5,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_12 : Impossible true (goalAt 119) 5 state119_12.toFinset :=
  node_ok cuts119 [] 0x54501814034301514034301514054500d0c046421514054501114052501514044421494052501814032301494032301494052500c8c052421494052500541c6030181406050090506242180c052421490844141454015141514051501454043421494051501454031301814051500c4c0515014540313010d085150145404342 (by decide +kernel)

def state119_13 : List Sig := [0x3333333333333333333333333333000033333333333333333333333333330000,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 6,input 5,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_13 : Impossible true (goalAt 119) 5 state119_13.toFinset :=
  node_ok cuts119 [] 0x54501814034301514034301514054500d0c046421514054501114051501514015141454051501814031301454031301454051500c4c0434214540515010d086030181406050090506242180c052421490844141494044421514052501454043421454052501494032301814052500c8c052501494032300541c5250149405242 (by decide +kernel)

def state119_14 : List Sig := [0xeeeeeeeeeeeeaaaaeeeeeeeeeeeeaaaaeeeeeeeeeeeeaaaaeeeeeeeeeeeeaaaa,0xffffffffffffffffffffffffffff0000ffffffffffffffffffffffffffff0000,input 6,input 5,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_14 : Impossible true (goalAt 119) 4 state119_14.toFinset :=
  node_ok cuts119 [] 0x1514060500d0c054500d0c054501514034300541c5450151401107180c060501814024140941c45071454054500545051501454060500c4c051500c4c051501454031300541c5150145410009 (by decide +kernel)

def state119_15 : List Sig := [0xcccccccccccc0000cccccccccccc0000cccccccccccc0000cccccccccccc0000,0xffffffffffffffffffffffffffff0000ffffffffffffffffffffffffffff0000,input 6,input 5,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_15 : Impossible true (goalAt 119) 5 state119_15.toFinset :=
  node_ok cuts119 [⟨state119_14,exclude119_14⟩] 0x54501814034301514034301514054500d0c015071514054500441c51501514015141454051501814031301454031301454051500c4c015071454051504002451501494200001454060301814060500905025071141c52501514016141494052501814032301494032301494052500c8c01707 (by decide +kernel)

def state119_16 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0f0f0f0f0f0f0f0f0f0f0f0f0000,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 6,input 5,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_16 : Impossible true (goalAt 119) 5 state119_16.toFinset :=
  node_ok cuts119 [] 0x52501814032301494032301494052500c8c052421494052500541c51501494043421454051501814031301454031301454051500c4c0434214540515010d086030181406050090506242180c052421490844141494044421494054501454015141454054501514034301814054500d0c05450151403430111405450151404642 (by decide +kernel)

def state119_17 : List Sig := [0xffffffffffffffffffffffffffff0000ffffffffffffffffffffffffffff0000,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 6,input 5,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_17 : Impossible true (goalAt 119) 6 state119_17.toFinset :=
  node_ok cuts119 [⟨state119_11,exclude119_11⟩,⟨state119_12,exclude119_12⟩,⟨state119_13,exclude119_13⟩,⟨state119_15,exclude119_15⟩,⟨state119_16,exclude119_16⟩] 0x54501814034301514034301514054500d0c046421514054501114200041514054504000c52501514044421494052501814032301494032301494052500c8c052421494052508000e00021494052504002051501514015141454051501494043421454051501814031301454031301454051500c4c0434214540515010d0a0001145405150400186030181406050090506242800004707180c05242110501707 (by decide +kernel)

def state119_18 : List Sig := [0xeeeeeeeeeeeeaaaaeeeeeeeeeeeeaaaaeeeeeeeeeeeeaaaaeeeeeeeeeeeeaaaa,0xffffffffffff00000000000000000000ffffffffffff0000,input 6,input 5,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_18 : Impossible true (goalAt 119) 4 state119_18.toFinset :=
  node_ok cuts119 [] 0x54501814034301514034301514054500d0c024141814060500905034301514034301514024141814024141814060300c4c051500c4c051501454054500545051501454060500c4c051500c4c05150145403130 (by decide +kernel)

def state119_19 : List Sig := [0xcccccccccccc0000cccccccccccc0000cccccccccccc0000cccccccccccc0000,0xffffffffffff00000000000000000000ffffffffffff0000,input 6,input 5,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_19 : Impossible true (goalAt 119) 5 state119_19.toFinset :=
  node_ok cuts119 [⟨state119_18,exclude119_18⟩] 0x54501814034301514034301514054500d0c051501514015141454051501814031301454031301454051500c4c051501494200001454024141814060500905034301514034301514031301454031301454024141814024141814060300c8c052500c8c052501494054500585052501494060500c8c052500c8c05250149403230 (by decide +kernel)

def state119_20 : List Sig := [0xffffffffffff00000000000000000000ffffffffffff0000,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 6,input 5,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_20 : Impossible true (goalAt 119) 6 state119_20.toFinset :=
  node_ok cuts119 [⟨state119_19,exclude119_19⟩] 0x1514060500d0c054500d0c054501514034301190854501514044501494054501110852501494060500c8c052500c8c0525014940323014908525014942000014540545005450515014540525010d0851501454060500c4c051500c4c0515014540313010d0851501454043420905060501814024141890857071490847070d0c054500d0c054500c8c052500c8c052500c4c051500c4c05150090506050090506050180c01707 (by decide +kernel)

def state119_21 : List Sig := [0xffffffff0000ffffffffffff00000000ffffffff0000ffffffffffff00000000,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 6,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_21 : Impossible true (goalAt 119) 5 state119_21.toFinset :=
  node_ok cuts119 [] 0xd0c054501514034301190854501514046421514060501190854501494054501110852500c8c052501494032301890852501494060421494060500c8c0525014540545005450515014540525010d0851500c4c0515014540313010d08515014540434214540605010d085150180c06242189083242180c06050181402414189086050181405242 (by decide +kernel)

def state119_22 : List Sig := [0xccccccccccccffffccccccccccccccccccccccccccccffffcccccccccccccccc,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 6,input 5,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_22 : Impossible true (goalAt 119) 5 state119_22.toFinset :=
  node_ok cuts119 [] 0x54501814034301514034301514054500d0c044421514054501110851501514015141454051501814031301454031301454051500c4c0434214540515010d085150149404342145406030181406050090506242180c052421490812401494054501110852501494060500c8c052500c8c05250149403230149085250149401507 (by decide +kernel)

def state119_23 : List Sig := [0xffff0000000000000000000000000000ffff0000000000000000,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 6,input 5,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_23 : Impossible true (goalAt 119) 6 state119_23.toFinset :=
  node_ok cuts119 [⟨state119_21,exclude119_21⟩,⟨state119_22,exclude119_22⟩] 0x54501814034301514034301514054500d0c046421514054501190852501514044421494052501814032301494032301494052500c8c017071494052500541c51501514015141454051501494043421454051501814031301454031301454051500c4c0434214540515010d08603018140605009050270715c1c603005c1c464215140464215141000814942000114940434214540434214542000011c1c5242 (by decide +kernel)

def state119_24 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f0f0f0f0f0f0f0f0f00000000,input 5,input 6,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_24 : Impossible true (goalAt 119) 5 state119_24.toFinset :=
  node_ok cuts119 [] 0x52421494052500441c32301494052500c8c0525018140323014940515014940434214540434214540515010d0831301454051500c4c05150181403130145406030149085242110506242180c060501814024141494044421494054501454015141454054501114054501514046420d0c05450151403430151403430181405450 (by decide +kernel)

def state119_25 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 5,input 6,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_25 : Impossible true (goalAt 119) 6 state119_25.toFinset :=
  node_ok cuts119 [⟨state119_24,exclude119_24⟩] 0x1190854501514044500d0c054501514034301514060500d0c054508000054501514100031494054501110852501490852501494015070c8c052501494032301494060500c8c0525005850525014940161414540545005450515014540525010d08515010d0851501454043420c4c051501454031301454060500c4c05150054505150145401514180c0524214908170705c1c5242149081707150506242180c06050400142414 (by decide +kernel)

def state119_26 : List Sig := [0xffffffff000000000000000000000000ffffffff0000000000000000,input 5,input 6,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_26 : Impossible true (goalAt 119) 6 state119_26.toFinset :=
  node_ok cuts119 [] 0x1190854501514044500d0c054501514034301514034300d0c054501494054501110852501490852501494015070c8c052501494032301494032300c8c0525014540545005450515014540525010d08515010d0851501454043420c4c051501454031301454031300c4c05150180c0524214908170709c1c6414180c02414151403430151403430149403230149403230145403130145403130149081707149081707150506050 (by decide +kernel)

def state119_27 : List Sig := [0x3333333333333030333333333333303033333333333330303333333333333030,input 2,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 5,input 0,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_27 : Impossible true (goalAt 119) 5 state119_27.toFinset :=
  node_ok cuts119 [] 0x31301454051500c4c0515018140313014540434214540515010d085150151401514145406030181406050090506242180c052421490844140d0c054501514034301514060500d0c054501190854501514044500c8c052501494032301454043421454052501494032301814052500541c5250149405242149404442151405250 (by decide +kernel)

def state119_28 : List Sig := [0xfffffffffffff0f0fffffffffffff0f0fffffffffffff0f0fffffffffffff0f0,input 2,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 5,input 0,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_28 : Impossible true (goalAt 119) 6 state119_28.toFinset :=
  node_ok cuts119 [⟨state119_27,exclude119_27⟩] 0x32301494052500c8c052501814032301494017071494052500541c52501514016141494200001494052504002031301454051500c4c0515014940434214540515018140313014540434214540515010d08515015140151414540434214540515010d0860301814060500905027074000c603011c1c60301105052420d0c054501514034301514060500d0c0545005c1c5450111404642180c04303180c04303 (by decide +kernel)

def state119_29 : List Sig := [0xf0f0f0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f0000,input 2,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 5,input 0,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_29 : Impossible true (goalAt 119) 6 state119_29.toFinset :=
  node_ok cuts119 [] 0xc8c052501494032301494060500c8c0525005c1c52501494015071494044401110852500c4c0515014540313014540525010d0851501454060500c4c0515010d085150145404342145404642054505150180c0605018140241409c1c603011c1c6030110505414119084642180c0464218140241418140564205c1c4642180c05414180c05414149401614149401614145404342145404342181402414181402414149085450 (by decide +kernel)

def state119_30 : List Sig := [0xffffffff00000000f0f0f0f000000000ffffffff00000000f0f0f0f0,input 2,input 6,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_30 : Impossible true (goalAt 119) 5 state119_30.toFinset :=
  node_ok cuts119 [] 0x1490852501494015070c8c0525014940323014940545011108525014540525010d08515010d0851501454043420c4c05150145403130145405450054505150180c052421490844141190854501514044500d0c05450151403430149403230149406050145403130145406050149086050181406242090506050181406030151403430151406050 (by decide +kernel)

def state119_31 : List Sig := [0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0,input 2,input 6,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 5,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_31 : Impossible true (goalAt 119) 6 state119_31.toFinset :=
  node_ok cuts119 [⟨state119_30,exclude119_30⟩] 0x1494060500c8c052501490852501494015070c8c052501494032301494054501110852500c8c0525014940323014540525010d0851501454060500c4c0515010d0851501454043420c4c051501454031301454054500545051500c4c0515014540313018908241418140605009052000018140605040014541414908524211050130314908524204c0c603015140605009050545011908545015140445015050545010c1c3430 (by decide +kernel)

def state119_32 : List Sig := [0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0000000000000000,input 2,input 6,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 5,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_32 : Impossible true (goalAt 119) 6 state119_32.toFinset :=
  node_ok cuts119 [] 0x1494060500c8c052501490852501494015070c8c0525014940323014940343005850525014540525010d0851501454060500c4c0515010d0851501454043420c4c05150145403130145403430054505150189082414181406050090505414149085242110502414181403430181401707149083430149086430150503430149403230149403230145403130145403130181402414181402414149081707149081707180c05450 (by decide +kernel)

def state119_33 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 5,input 0,input 1,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_33 : Impossible true (goalAt 119) 7 state119_33.toFinset :=
  node_ok cuts119 [⟨state119_9,exclude119_9⟩,⟨state119_10,exclude119_10⟩,⟨state119_17,exclude119_17⟩,⟨state119_20,exclude119_20⟩,⟨state119_23,exclude119_23⟩,⟨state119_25,exclude119_25⟩,⟨state119_26,exclude119_26⟩,⟨state119_28,exclude119_28⟩,⟨state119_29,exclude119_29⟩,⟨state119_31,exclude119_31⟩,⟨state119_32,exclude119_32⟩] 0x8002854140d0c034304000c60301514054508002454141514054504000c60300d0c034304001424141514054504000c60500d0c060504003424140d0c034304001460501514054508002017071190846424000c52421514054508001c17071514054504000c52421190844504002847070c8c032304002060301494052504002847071494052504002060300c8c032304000c46421494052504002054500585054504003046420585044424000c545014940525040015000a1494052504002060500c8c060504002d000a0c8c032304001460501494052504002852428000052424002015051494052504002852421494052504002015054002815074001c47070c4c031304001860301454051504001c47071454051504001860300c4c031304000d00071454051504001854500545054504001d00070545015144000c545014540515040021000a14540515040018525010d08525040025000710d0843424002052501454051504001500071454051504001860500c4c060504001d00070c4c031304001460501454051504001c170710d0843424001852421454051504001c170714540515040018524210d08434280018603009050603040014541418140605080014603018140605040014541409050241440011000440010624280010603005c1c60308000c470714908524280008603014908524280004470705c1c4414 (by decide +kernel)

def state119_34 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f0f0f0f0f0f0f0f0f00000000,input 5,input 6,0xffff000000000000ffff000000000000ffff000000000000ffff0000,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_34 : Impossible true (goalAt 119) 5 state119_34.toFinset :=
  node_ok cuts119 [] 0x32301494052500c8c052501810060421494051501494043421454031301454051500c4c051501890831301454052501490852500c8c0515010d08515010d085414149085242180c06050151404450151404642180c062421890832421494044421494054501454015141454054500d0c05450151403430151403430189085450 (by decide +kernel)

def state119_35 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 5,input 6,0xffff000000000000ffff000000000000ffff000000000000ffff0000,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_35 : Impossible true (goalAt 119) 6 state119_35.toFinset :=
  node_ok cuts119 [⟨state119_34,exclude119_34⟩] 0xd0c054501514034301514062420d0c054508000054501514100031494054501110852500c8c0525014940323014940604018108525005850525014940161414540545005450515014540525010d0851500c4c051501454031301454062420c4c0515005450515014540151415140464215140445014940524214940323014540434214540434205c1c524214908603018140170714908524205c1c5414180c062420c9082707 (by decide +kernel)

def state119_36 : List Sig := [0xffffffff000000000000000000000000ffffffff0000000000000000,input 5,input 6,0xffff000000000000ffff000000000000ffff000000000000ffff0000,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_36 : Impossible true (goalAt 119) 6 state119_36.toFinset :=
  node_ok cuts119 [] 0xd0c054501514034301514034300d0c054501494054501110852500c8c052501494032301494032300c8c0525014540545005450515014540525010d0851500c4c051501454031301454031300c4c0515015140464215140445014940524214940323014540434214540434205c1c524214908603009050170714908524205c1c6707180c02707151403430151403430149403230149403230145403130145403130150506242 (by decide +kernel)

def state119_37 : List Sig := [0xffff000000000000ffff000000000000ffff000000000000ffff0000,input 5,input 0,input 1,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_37 : Impossible true (goalAt 119) 7 state119_37.toFinset :=
  node_ok cuts119 [⟨state119_35,exclude119_35⟩,⟨state119_36,exclude119_36⟩] 0x4000c54140d0c034304000c60301514054504000c54141514054504000c60300d0c034304001427071514054504000c62420d0c062424000c27070d0c034304001462421514054504002047070c8c032304002060301494052504002047071494052504002060300c8c032304000c46421494052504000c54500585054504000c46420585044424000c54501494052504001462421494052504002060400c8c060404002062420c8c060424001460401494052504001847070c4c031304001860301454051504001847071454051504001860300c4c031304000d00031454051504000c54500545054504000d00060545015144000c545014540515040021000814540515040020525010d08525040021000610d0843424002052501454051504001427071454051504001862420c4c062424001827070c4c0313040014624214540515080004603009c1c603040014541418908624280000603018908624240014541409c1c324240010541405c1c541440010603014908524240010541414908524240010603005c1c603040010545014908545040010464205c1c464240010545005c1c545040010464214908445040010525005414525040010323014908524240010525014908525040010323005414323040010515014908515040010434205c1c434240010515005c1c5150400104342149084342400110004400286050 (by decide +kernel)

def state119_38 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f0f0f0f0f0f0f0f0f00000000,input 6,input 5,input 0,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_38 : Impossible true (goalAt 119) 5 state119_38.toFinset :=
  node_ok cuts119 [] 0x1c14062421814060501c0c052421490860301490852501494022301494070501810852500c8c0525014940323010d08515014540434214540525010d0851501454070500c4c051500c4c051501454031301c0c070501c14022421114054501514046421494044421494054501454015141454054501514034301c14054500d0c05450151403430 (by decide +kernel)

def state119_39 : List Sig := [0xfffffffffffffffffffffffff0f0f0f0fffffffffffffffffffffffff0f0f0f0,input 6,input 2,input 5,input 0,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_39 : Impossible true (goalAt 119) 6 state119_39.toFinset :=
  node_ok cuts119 [⟨state119_38,exclude119_38⟩] 0x7050189086050181407030149085242180c0130314908524204c0c5242149405250088c052501c14060421494052501514044421494032301494052500c8c0121014940525004840434214540515010d0851501494043421454051501c14031301454051501514015141454031301454051500c4c011101454051500444070301c14070500890823031190854501514044501514070500d0c054500d0c05450151403430800004303 (by decide +kernel)

def state119_40 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0,0xfffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0,input 0,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_40 : Impossible true (goalAt 119) 5 state119_40.toFinset :=
  node_ok cuts119 [] 0x1514046421514060500d0c052421490844300d05052421490824141490852501494022301494054501110852500c8c0525014940323005850525014940161410d08515014540434214540525010d0851501454054500c4c051500c4c051501454031300545051501454015140d0c054501514022420d05054501514043070d05034300d0c02307 (by decide +kernel)

def state119_41 : List Sig := [0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0,input 6,0xfffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0,input 5,input 0,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_41 : Impossible true (goalAt 119) 6 state119_41.toFinset :=
  node_ok cuts119 [⟨state119_40,exclude119_40⟩] 0x1490827070905052421514046421514044501505052421490844140d0c052421490824301490852501494022301494032300c8c052501494054501110852500c8c052501494032300c8c0525014940323010d08515014540434214540525010d0851501454031300c4c051501454054500c4c051500c4c051501454031300c4c051501454031301c14034141505200000d05034300d050343008c1c541415140545010c1c3430151405450400147030 (by decide +kernel)

def state119_42 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 6,0xfffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0,input 2,input 0,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_42 : Impossible true (goalAt 119) 6 state119_42.toFinset :=
  node_ok cuts119 [⟨state119_40,exclude119_40⟩] 0x1c14062421814060501c0c052421490860300d05052421490824141490852501494022301494034300585052501494070501810852500c8c0525014940323005850525014940161410d08515014540434214540525010d0851501454034300545051501454070500c4c051500c4c051501454031300545051501454015140908052420d0c05242151403430150c200000d0c034140d0c0343008c1c70301c14070500890834141c1407050400085414 (by decide +kernel)

def state119_43 : List Sig := [0xfffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0,input 2,input 5,input 0,input 1,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_43 : Impossible true (goalAt 119) 7 state119_43.toFinset :=
  node_ok cuts119 [⟨state119_39,exclude119_39⟩,⟨state119_41,exclude119_41⟩,⟨state119_42,exclude119_42⟩] 0x703005c1c7030180805242149087030149085242180801707180c0341414908524209c1d000309c1c341440034241409c1c524214909000314908524240010170705c1d000305c1c17074001052421490847070c8c032301c0c052501494047071494052501c0c032300c8c05242088805242054145250149405242149405250054142220088c027071494052500d05032300c8c027070c8c032300d05052501494100021494052500d0c016140d0c100100585016140d0c052501494100101494052504000032300c8c100100c8c032304000052501494047070c4c031301c0c051501454047071454051501c0c031300c4c0170710d08434214908515014540170714540515014908434210d09001014540515014940434214941000f10d0843421494051501454027071454051500d05031300c4c027070c4c031300d05051501454100021454051500d0c015140d0c1000f0545015140d0c0515014541000d1454051504000431300c4c1000f0c4c031304000451501454070300d050703015051000d1505070308000870301505034140d05100024000870501505034300d0c070304000870301505200011505070300d0c0343005c1c24200908052420d0c0524205c1c34300d0c052420908052420d05100050d05100020d0c0343040009000208c1d00024001454501c0c1000e1c0c043034003443031c0c200001c0c04303400384303 (by decide +kernel)

def state119_44 : List Sig := [0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,0xfafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafa,0xffff0f0fffff0000ffff0f0fffff0000ffff0f0fffff0000ffff0f0fffff0000,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_44 : Impossible true (goalAt 119) 4 state119_44.toFinset :=
  node_ok cuts119 [] 0x180c06050181403414180c052421490844141814062421814052420d0c054501514034301514060500d0c0545010d0854501514044500c8c052501494032301494060500c8c0525014908525014941000914540515010d085250 (by decide +kernel)

def state119_45 : List Sig := [0xfafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafa,input 0,0xffff0f0fffff0000ffff0f0fffff0000ffff0f0fffff0000ffff0f0fffff0000,input 5,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_45 : Impossible true (goalAt 119) 5 state119_45.toFinset :=
  node_ok cuts119 [⟨state119_44,exclude119_44⟩] 0x32301494052500c8c052501814032301494052421494052500441c52501514044421494060301814060500d0506030149085242110506050189086050149081514180c04307180c015141494200001494015141814026071814013071490815141490851500d0c054501514034301514060500d0c05450119085450151404450 (by decide +kernel)

def state119_46 : List Sig := [0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 0,0xffff0f0fffff0000ffff0f0fffff0000ffff0f0fffff0000ffff0f0fffff0000,input 2,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_46 : Impossible true (goalAt 119) 5 state119_46.toFinset :=
  node_ok cuts119 [⟨state119_44,exclude119_44⟩] 0x60301814060500d05034301514054500d0c0545018140343015140464215140545011140603014908524211050605018908605014908450710d084342180c0434218140250718140434215142000015140434214508150710d0851500c8c052501494032301494060500c8c05250149405450111085250149085250149410009 (by decide +kernel)

def state119_47 : List Sig := [0x3333030333330000333303033333000033330303333300003333030333330000,0xffff0f0fffff0000ffff0f0fffff0000ffff0f0fffff0000ffff0f0fffff0000,input 2,input 5,input 0,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_47 : Impossible true (goalAt 119) 5 state119_47.toFinset :=
  node_ok cuts119 [] 0x31301454051500c4c0515018140313014540515015140151414540434214540515010d0860301814060500d05034301514054500d0c054501814034301514044421514054501110860301490852420490060501890860501490832301494052500c8c0515010d0851501494052500c8c06050149405250111085450149401507 (by decide +kernel)

def state119_48 : List Sig := [0xffff0f0fffff0000ffff0f0fffff0000ffff0f0fffff0000ffff0f0fffff0000,input 2,input 5,input 0,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_48 : Impossible true (goalAt 119) 6 state119_48.toFinset :=
  node_ok cuts119 [⟨state119_45,exclude119_45⟩,⟨state119_46,exclude119_46⟩,⟨state119_47,exclude119_47⟩] 0x11c1c32300c8c0603014940525011c1c52501494060300c8c0323009c1c52501494060500c8c0605009c1c32300c8c060501494052501190852501494054500585054501190816141110854501494052501490a00021490815051494052501490852501494015054002c150711c1c31300c4c0603014540515011c1c51501454060300c4c031304002c515014540525010d08525080004434210d08525014540515009c1c51501454060500c4c0605009c1c31300c4c060501454051504000c515014540545005450545080000151405450545014540515005c1c434210d08524214540515005c1c515014540524210d084342180c03414180c05414181406050180c060501814054140d05034141505034300d0c060301514054501505054501514060300d0c034300d05054501514060500d0c060500d05034300d0c0605015140545005c1c464211908524215140545005c1c5450151405242119084450180c01707180c04707149085242180c0524214908470705c1c4414181405242181402707400106242181410004181402707149085242 (by decide +kernel)

def state119_49 : List Sig := [0xffffffffffffffff0f0f0f0f00000000ffffffffffffffff0f0f0f0f00000000,input 6,input 2,input 5,input 0,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_49 : Impossible true (goalAt 119) 6 state119_49.toFinset :=
  node_ok cuts119 [⟨state119_38,exclude119_38⟩] 0x7050189086050181407030149085242180c0170714908524205c1c5242149405250088c052501c14060421494052501514044421494032301494052500c8c0161414940525005850434214540515010d0851501494043421454051501c14031301454051501514015141454031301454051500c4c015141454051500545070301c14070500890834141c14070500d05046421514054501114054501c14034141514074301514054501c0c200001514054500d0c05414 (by decide +kernel)

def state119_50 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0000000000000000,0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000,input 0,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_50 : Impossible true (goalAt 119) 5 state119_50.toFinset :=
  node_ok cuts119 [] 0xd050524214908241414908525014940223005850525014940161410d08515014540434214540525010d0851500545051501454015141890870501814060501c14052501810852501c14051500c4c051500d0c054501c140545008c1c64501514054501190852501110852501514051500c4c05150151404307 (by decide +kernel)

def state119_51 : List Sig := [0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0000000000000000,input 6,0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000,input 5,input 0,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_51 : Impossible true (goalAt 119) 6 state119_51.toFinset :=
  node_ok cuts119 [⟨state119_38,exclude119_38⟩,⟨state119_50,exclude119_50⟩] 0x1490827070905052421505052421490844141490852501494022301494032300c8c052500c8c0525014940323010d08515014540434214540525010d0851501454031300c4c051500c4c051501454031300d0505414800043414090c052420d0c052420c8c052500c8c052500c4c051500c4c051501c14034301505074300d0c034301514200001514044501514054501190852501110852501514051500c4c051501514054500d0507450151407030 (by decide +kernel)

def state119_52 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 6,0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000,input 2,input 0,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_52 : Impossible true (goalAt 119) 6 state119_52.toFinset :=
  node_ok cuts119 [⟨state119_50,exclude119_50⟩] 0x7030149085242180c03414149085242090505242149405250088c052501514044421494032301494052500c8c0161414940525005850434214540515010d0851501494043421454051501514015141454031301454051500c4c015141454051500545046421514054501914200001514054500d14034141514054504000862421c14060501814070501494060421494070501454031301454034301c0c070501c140224208c0c5414 (by decide +kernel)

def state119_53 : List Sig := [0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000,input 2,input 5,input 0,input 1,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_53 : Impossible true (goalAt 119) 7 state119_53.toFinset :=
  node_ok cuts119 [⟨state119_48,exclude119_48⟩,⟨state119_49,exclude119_49⟩,⟨state119_51,exclude119_51⟩,⟨state119_52,exclude119_52⟩] 0x703005c1c7030180805242149087030149085242180801707180c0341414908524209c1d000509c1c341440014241409c1c52421490847070c8c032301c0c052501494047071494052501c0c032300c8c05242088805242054145250149405242149405250054142220088c027071494052500d05032300c8c027070c8c032300d05052501494046421494052501514016141514046420585044421514052501494047070c4c031301c0c051501454047071454051501c0c031300c4c0170710d08434214908515014540170714540515014908434210d09001014540515014940434214941001110d0843421494051501454027071454051500d05031300c4c027070c4c031300d05051501454100021454051501514015141514100110545015141514051501454070300d05070301505100051505070308000c70301505034140d05054148000854141c0c054501514054141514054501c0c100021c0c017071190846421490854501514017071514054501490846421114100024000874500d05100050d05100021514054501c0c1000e1c0c054144001454141c0c200011c0c054144001454144001500044001052424001452424001500038000052424001052420c8c100000c8c052504001452500c8c100100c8c052504000052500c4c100010c4c051504001451500c4c100110c4c051504000451504000900021c1410005400083430 (by decide +kernel)

def state119_54 : List Sig := [0xffffffff00000000f0f0f0f000000000ffffffff00000000f0f0f0f0,input 5,input 2,input 6,input 0,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_54 : Impossible true (goalAt 119) 6 state119_54.toFinset :=
  node_ok cuts119 [⟨state119_30,exclude119_30⟩] 0x7030149085242180c0524208c0e0000149085242149405250088c032301494052500c8c052501514044421494052500c8c0323014940434214540515010d0851501494043421454031301454051500c4c051501514015141454051500c4c031301454046421514054501114034301514054500d0c054500d0c0343015140703015050703015050524204c0c524204c0c52500c8c052500c8c051500c4c051500c4c054141c0c054141c0c054500d0c054500d0c07050 (by decide +kernel)

def state119_55 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 5,0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0,input 2,input 0,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_55 : Impossible true (goalAt 119) 6 state119_55.toFinset :=
  node_ok cuts119 [⟨state119_40,exclude119_40⟩] 0x1c0c052421490860301c14062421814060501505052421490844141490852501494022301494054501110852500c8c0525014940323014940705018108525005850525014940161410d08515014540434214540525010d0851501454054500545051500c4c051501454031301454070500c4c051500545051501454015141190854501514044500d0c054501c142000015140541415140545010c1c54141c0c070304000870301c1407050089083414 (by decide +kernel)

def state119_56 : List Sig := [0xffffffff000000000000000000000000ffffffff0000000000000000,input 5,0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0,input 2,input 0,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_56 : Impossible true (goalAt 119) 6 state119_56.toFinset :=
  node_ok cuts119 [] 0x7030149085242180c0524209c1c2414149085242149405250088c052501514044421494032301494052500c8c052500c8c0323014940434214540515010d0851501494043421454051501514015141454031301454051500c4c051500c4c031301454046421514054501114034301514023030d05054501c0c034141c0c0230314908541414908441414940323014940323014540313014540313015140541415140430710c0c7050 (by decide +kernel)

def state119_57 : List Sig := [0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0,input 2,input 6,input 0,input 1,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_57 : Impossible true (goalAt 119) 7 state119_57.toFinset :=
  node_ok cuts119 [⟨state119_41,exclude119_41⟩,⟨state119_31,exclude119_31⟩,⟨state119_39,exclude119_39⟩,⟨state119_54,exclude119_54⟩,⟨state119_55,exclude119_55⟩,⟨state119_56,exclude119_56⟩] 0x200050d05034141505070501c14200041c14070501505034140d052000308c0c23034001470501c14200021c140705040014230308c0c705014908705018909000318908705080004605018908524218140541405c1c541411c1c524214908541414908524211c1c170711051000304c0c130340010524214909000314908524240010130304c0c62421494052501c14032301c14062420c8c060421c1405250149405242088805242054145250149405242149405250054142220088c047070c8c032301505052501494047071494052501505032300c8c046421494052501514016141514046420585044421514052501494100100c8c032304000052501494100101494052504000032300c8c027071454051501c14031301c14027070c4c031301c140515014540170710d08434214908515014540170714540515014908434210d09001014540515014940434214941001210d0843421494051501454047070c4c031301505051501454047071454051501505031300c4c100021454051501514015141514100120545015141514051501454100120c4c031304000451501454100121454051504000431300c4c100024000870300d05054501514070504000870500d05200000d050705015140545005c1c464211908524215140545005c1c545015140524211908445015051000e15051000215140545040009000210c1d0002400383430 (by decide +kernel)

def state119_58 : List Sig := [0xffffffff0f0f0f0fffffffff00000000ffffffff0f0f0f0fffffffff00000000,input 5,input 2,input 6,input 0,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_58 : Impossible true (goalAt 119) 6 state119_58.toFinset :=
  node_ok cuts119 [⟨state119_38,exclude119_38⟩] 0x7030149085242180c0705018908605018140170714908524205c1c5242149405250088c032301494052500c8c052500d0c016141494052501c140604214940161414940525005850434214540515010d0851501494043421454031301454051500c4c051500d0c015141454051501c14031301454015141454051500545024201490834301490834301c0c054140d0c074501c14034301c14200000d0c054501514070301c14070500890834141c0c054141c0c05414 (by decide +kernel)

def state119_59 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 5,0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0000000000000000,input 2,input 0,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_59 : Impossible true (goalAt 119) 6 state119_59.toFinset :=
  node_ok cuts119 [⟨state119_50,exclude119_50⟩] 0x7050189086050181405414149085242110505242149405250088c052500d0c016141494052501c140604214940161414940525005850434214540515010d0851501494043421454051500d0c015141454051501c14031301454015141454051500545024201490834301490a00001c14034301c14054140d0c034304000852421c0c05242180c052500c8c052500c8c051500c4c051500c4c054501c14070301c140224210c0c3414 (by decide +kernel)

def state119_60 : List Sig := [0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0000000000000000,input 2,input 6,input 0,input 1,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_60 : Impossible true (goalAt 119) 7 state119_60.toFinset :=
  node_ok cuts119 [⟨state119_51,exclude119_51⟩,⟨state119_32,exclude119_32⟩,⟨state119_58,exclude119_58⟩,⟨state119_59,exclude119_59⟩] 0x1000e0d05034141505070501c14200031c14070501505034140d050705014908705018909000318908705080004605018908524218140541405c1c541411c1c524214908541414908524211c1c17071105062421494052501c14032301c14062420c8c060421c1405250149405242088805242054145250149405242149405250054142220088c047070c8c032301505052501494047071494052501505032300c8c100021494052500d0c016140d0c100100585016140d0c052501494027071454051501c14031301c14027070c4c031301c140515014540170710d08434214908515014540170714540515014908434210d09001014540515014940434214941001310d0843421494051501454047070c4c031301505051501454047071454051501505031300c4c100021454051500d0c015140d0c100130545015140d0c051501454034148000034141c14034301c14034140d0c034301c14100021c14017070908024201490834301490817070d0c0343014908242014909000240008743015051000e1505100020d0c034301c14100051c14034144003834141c14200021c14034144001434141490900041490817074003817071490900031490817074001017071494100001494032304003832301494100101494032304000032301454100011454031304003831301454100131454031304000431304000900021c0c1000e400085450 (by decide +kernel)

def state119_61 : List Sig := [0x3333333333330000333333333333000033333333333300003333333333330000,input 4,input 5,input 0,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_61 : Impossible true (goalAt 119) 6 state119_61.toFinset :=
  node_ok cuts119 [] 0x1505034300d0c070301514054501505054501514070300d0c034300d05054501514070500d0c070500d05034300d0c0705015140545005c1c444211108524215140545005c1c54501514052421110844421141c31300c4c070301454051501141c51501454070300c4c0313040024515014540545005450545040024151405450545014540515009c1c51501454070500c4c0705009c1c31300c4c0705014540515005c1c434210d08524214540515005c1c515014540524210d0843421c0c034141c0c054141c14070501c0c070501c14054140d05022401c0c017071c0c060201490852421c0c0524214908602005c1c60301c14052421c14062424002062421c141000a1814062421490860501c0c032300c8c045071494052501c0c052501494045070c8c032301514052501494044420585044421514016141514044421494052501454052501454043424002443421454100091454043421494052501c14052501494062420c8c060421c14032301c1406242149405250400202220088c05242149405250400285250149405242088805242 (by decide +kernel)

def state119_62 : List Sig := [0x5555555555555555555555555555000055555555555555555555555555550000,input 6,input 4,input 5,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_62 : Impossible true (goalAt 119) 5 state119_62.toFinset :=
  node_ok cuts119 [] 0x1514070500d0c054501190854501514044500d0c054501514034301494054501110852501494070501810852501490852501494022300c8c052501494032301c0c070501c14022421c14062421814060501c0c052421490860301454015141514051501454043421494051501454031301c140515010d0851501454043420c4c05150145403130 (by decide +kernel)

def state119_63 : List Sig := [0x3333333333333333333333333333000033333333333333333333333333330000,input 6,input 4,input 5,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_63 : Impossible true (goalAt 119) 5 state119_63.toFinset :=
  node_ok cuts119 [] 0x1514070500d0c054501190854501514044500d0c054501514034301454054500545051501454070500c4c0515010d0851501454043420c4c051501454031301c0c070501c14022421c14062421814060501c0c052421490860301494044421514052501454043421454052501494060421c1405250088c052501494052420c8c05250149403230 (by decide +kernel)

def state119_64 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0f0f0f0f0f0f0f0f0f0f0f0f0000,input 6,input 4,input 5,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_64 : Impossible true (goalAt 119) 5 state119_64.toFinset :=
  node_ok cuts119 [] 0x1494070501810852501490852501494022300c8c0525014940323014540525010d0851501454070500c4c0515010d0851501454043420c4c051501454031301c0c070501c14022421c14062421814060501c0c052421490860301494044421494054501454015141454054501514034301c14054501114054501514046420d0c05450151403430 (by decide +kernel)

def state119_65 : List Sig := [0xffffffffffffffffffffffffffff0000ffffffffffffffffffffffffffff0000,input 6,input 4,input 5,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_65 : Impossible true (goalAt 119) 6 state119_65.toFinset :=
  node_ok cuts119 [⟨state119_62,exclude119_62⟩,⟨state119_63,exclude119_63⟩,⟨state119_64,exclude119_64⟩] 0x54501c14034301514046421514054501114034301514054500d0c200021514054504000852501514044421494052501c1406042149405242149405250088c032301494052500c8c200011494052504000051501514015141454051501494043421454051501c140313014540434214540515010d0831301454051500c4c200001454051504000470301c14070500890827071c14062421814060501c0c0524214908603005c1c4707 (by decide +kernel)

def state119_66 : List Sig := [0xffffffffffff00000000000000000000ffffffffffff0000,input 6,input 4,input 5,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_66 : Impossible true (goalAt 119) 6 state119_66.toFinset :=
  node_ok cuts119 [] 0x54501c14034301514046421514054501114034301514054500d0c052501514044421494052501c1406042149405242149405250088c032301494052500c8c051501514015141454051501494043421454051501c140313014540434214540515010d0831301454051500c4c034141c14070500d050705018908605018140570714908524211c1c34301514034301514032301494032301494031301454031301454034141c14034141c1401707149090005149087030 (by decide +kernel)

def state119_67 : List Sig := [0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 6,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 5,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_67 : Impossible true (goalAt 119) 6 state119_67.toFinset :=
  node_ok cuts119 [⟨state119_11,exclude119_11⟩] 0x1514060500d0c054501190854501514044500d0c054501514034300908054501514024301494054501110852501494060500c8c052501490852501494100080c8c0525014940323008880525014940223014540545005450515014540525010d0851501454060500c4c0515010d0851501454043420c4c051501454031300848051501454021301890860301814060500d0520000181406050090506030149085242110501707149085242400146020 (by decide +kernel)

def state119_68 : List Sig := [0xccccffffccccffffccccccccccccccccccccffffccccffffcccccccccccccccc,input 6,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 5,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_68 : Impossible true (goalAt 119) 5 state119_68.toFinset :=
  node_ok cuts119 [] 0x54501c14034301514044421514054501110834301514054500d0c051501514015141454051501c140313014540434214540515010d0831301454051500c4c051501494043421454060421c0c070501c14024141c0c052421490812401494054501110852501494060500c8c052501490852501494015070c8c05250149403230 (by decide +kernel)

def state119_69 : List Sig := [0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000,input 6,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 5,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_69 : Impossible true (goalAt 119) 6 state119_69.toFinset :=
  node_ok cuts119 [⟨state119_21,exclude119_21⟩,⟨state119_68,exclude119_68⟩] 0x1514070500d0c054501190854501514046420d0c054501514034301494054501110852501494070500c8c0525005c1c52501494015070c8c0525014940323014540545005450515014540525010d0851501454070500c4c0515010d0851501454043420c4c051501454031301890870301c140705009050703015c1c703005c1c46421514046421514100081494200011494043421454043421454060501814200001c141000505c1c5242149086030 (by decide +kernel)

def state119_70 : List Sig := [0x3333333333330000333333333333000033333333333300003333333333330000,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,input 5,input 0,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_70 : Impossible true (goalAt 119) 6 state119_70.toFinset :=
  node_ok cuts119 [] 0xd0c054501514034301514070500d0c054501110854501514044421110854501514044420c4c051501454031301454054500545051501454070500c4c0515010d08515014540434210d0851501454043421c0c070501c1403414189087030180806030180c070504002060501490870301141c70301141c32301494052500c8c0525011108545014940515010d0851501494052500c8c07050149402230149405250088810000 (by decide +kernel)

def state119_71 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,input 5,input 0,input 1,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_71 : Impossible true (goalAt 119) 7 state119_71.toFinset :=
  node_ok cuts119 [⟨state119_61,exclude119_61⟩,⟨state119_65,exclude119_65⟩,⟨state119_66,exclude119_66⟩,⟨state119_67,exclude119_67⟩,⟨state119_69,exclude119_69⟩,⟨state119_70,exclude119_70⟩] 0x54140d0c034301c0c054501514054141514054501c0c034300d0c034141514054501c14034301c14034140d0c034301c14054501514100041190846424000c54501514100031514054504001046421190900031190846424000854501514100031514054504000846421190847070c8c032301c0c052501494047071494052501c0c032300c8c046421494052501514016141514046420585044421514052501494100081494052501c14032301c14100080c8c032301c1405250149410004088802220400205250149410008149405250400102220088c100088001600004000052501494100081494052504000100084000047070c4c031301c0c051501454047071454051501c0c031300c4c1000314540515015140151415141000605450151415140515014541000814540515014940434214941000610d0843421494051501454100061454051501c14031301c14100060c4c031301c140515014541000410d08434240018515014541000614540515040010434210d09000610d08434240004515014541000614540515040004434210d0870300d05070301505070501c14070301c14070501505034140d05100044001062421c0c200041c0c060204001060201c0c20003180c060204001060301c14100051c14100044001100044001100041814100044001452421c0c1000e1c0c047078000847071c0c200011c0c04707400384707 (by decide +kernel)

def state119_72 : List Sig := [0xffffffffffffffff0000ffff00000000ffffffffffffffff0000ffff00000000,input 6,input 4,input 5,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_72 : Impossible true (goalAt 119) 6 state119_72.toFinset :=
  node_ok cuts119 [] 0x54501c14034301514046421514054501114034301514054500d0c034301514054500d0c052501514044421494052501c14060421494052421494052500888032301494052500c8c032301494052500c8c051501514015141454051501494043421454051501c140313014540434214540515010d0831301454051500c4c031301454051500c4c060201c14070500890834141c14070500d050705018908605018140702014908524218080170714908524205c1c7030 (by decide +kernel)

def state119_73 : List Sig := [0xffff000000000000ffff000000000000ffff000000000000ffff00000000,input 4,input 5,input 0,input 1,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_73 : Impossible true (goalAt 119) 7 state119_73.toFinset :=
  node_ok cuts119 [⟨state119_72,exclude119_72⟩] 0x54140d0c034301c0c054501514054141514054501c0c034300d0c034141514054501c14034301c14034140d0c034301c14054501514017071190846421490854501514017071514054501490846421114047070c8c032301c0c052501494047071494052501c0c032300c8c046421494052501514016141514046420585044421514052501494100051494052501c14032301c14100080c8c032301c14052501494052420888052420541452501494052421494052500541422200888047070c4c031301c0c051501454047071454051501c0c031300c4c1000314540515015140151415141000605450151415140515014541000814540515014940434214941000610d0843421494051501454100051454051501c14031301c14100060c4c031301c140515014540170710d08434214908515014540170714540515014908434210d0870300d05070301505070501c14070301c14070501505034140d050703005c1c70301808052421490870301490852421808017071808100044001072421c14100051c141000414908524218081000e18080703040014703018082000018080703040014703009081000209080545040014545009081000309080545040008545008881000008880525040014525008881000808880525040000525008481000108480515040014515008481000608480515040004515040011000418909000540011000a (by decide +kernel)

def state119_74 : List Sig := [0xffffffff00000000ffff000000000000ffffffff00000000ffff0000,input 5,input 4,input 6,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_74 : Impossible true (goalAt 119) 6 state119_74.toFinset :=
  node_ok cuts119 [⟨state119_11,exclude119_11⟩] 0x34301514054500d0c046421514054501114054500d0c034301514052501514044421494032301494052500c8c05242149405250088c052500c8c032301494051501514015141454051501494043421454031301454051500c4c0434214540515010d0851500c4c03130145407030149085242180c0524209c1e00001490870301505070301505054500d0c054500d0c052500c8c052500c8c051500c4c051500c4c054141c0c054141c0c0524205c1c5242400107050 (by decide +kernel)

def state119_75 : List Sig := [0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 4,input 6,input 0,input 1,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_75 : Impossible true (goalAt 119) 7 state119_75.toFinset :=
  node_ok cuts119 [⟨state119_67,exclude119_67⟩,⟨state119_65,exclude119_65⟩,⟨state119_74,exclude119_74⟩] 0x70300d05070301505070501c14070301c14070501505034140d052000209c1c27074001470501c14200011c140705040014270709c1c34141514054501c14034301c14034140d0c034301c14054501514054140d0c034301c0c054501514054141514054501c0c034300d0c100041190846421490854501514100031514054501490846421114100030908024204000854501514100031514054504000824200908062421494052501c14032301c14062420c8c060421c14052501494046421494052501514016141514046420585044421514052501494100080c8c032301c0c052501494100081494052501c0c032300c8c052420888052424002052501494052421494052504001022200888100080888022204000052501494100081494052504000022200888027071454051501c14031301c14027070c4c031301c140515014541000314540515015140151415141000605450151415140515014541000814540515014940434214941000610d0843421494051501454100060c4c031301c0c051501454100061454051501c0c031300c4c1000410d08434214908515014541000614540515014908434210d0900060848021204000451501454100061454051504000421200848100044001060201c14052421c14062424001062421c14200001814062421490860501c0c1000e1c0c10004149085242400110004180c10004400381707 (by decide +kernel)

def state119_76 : List Sig := [0xccccffffccccffffccccccccccccccccccccffffccccffffcccccccccccccccc,input 4,input 6,input 0,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_76 : Impossible true (goalAt 119) 6 state119_76.toFinset :=
  node_ok cuts119 [⟨state119_68,exclude119_68⟩] 0x1c0c034141c0c054141c14070501c0c070501c14054140d05022400d05054501514070500d0c070500d05034300d0c070501514054501505034300d0c070301514054501505054501514070300d0c0343005c1c444211108524215140545005c1c545015140524211108444209c1c51501454070500c4c0705009c1c31300c4c070501454051504002451501454054500545054504002415140545054501454051501141c31300c4c070301454051501141c51501454070300c4c0313005c1c434210d08524214540515005c1c515014540524210d08434240024515014540525010d08525040024434210d0852501454051501c14052421c14060424002060421c14200001c14060421490852421c0c017071c0c045071490852421c0c0524214908450705c1c12401810852501494070500c8c070501810832301810870501494052501110852501494054500585054501110816141110854501494052501141c32300c8c070301494052501141c52501494070300c8c03230149082220149081505149405250149085250149401505088802230 (by decide +kernel)

def state119_77 : List Sig := [0xffffffff0000ffffffffffff00000000ffffffff0000ffffffffffff00000000,input 5,input 4,input 6,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_77 : Impossible true (goalAt 119) 6 state119_77.toFinset :=
  node_ok cuts119 [⟨state119_21,exclude119_21⟩] 0x34301514054500d0c046421514054501190854501890834301514054501190846421514052501514044421494032301494052500c8c02220149405250088c052501810060421494052500c8c032301494051501514015141454051501494043421454031301454051500c4c0434214540515010d08515018908313014540515010d084342145407030180806030180c072421890a00001890817074001052421490870301890862420890870501c0c054141c0c05414 (by decide +kernel)

def state119_78 : List Sig := [0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000,input 4,input 6,input 0,input 1,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_78 : Impossible true (goalAt 119) 7 state119_78.toFinset :=
  node_ok cuts119 [⟨state119_69,exclude119_69⟩,⟨state119_76,exclude119_76⟩,⟨state119_77,exclude119_77⟩] 0x70300d05070301505070501c14070301c14070501505034140d05034141514054501c14034301c14034140d0c034301c14054501514054140d0c034301c0c054501514054141514054501c0c034300d0c0170711908464204c0c545015140170715140545004c0c46421190862421494052501c14032301c14062420c8c060421c140525014940464214940525015140161415140464205850444215140525014941000e0c8c032301c0c052501494100081494052501c0c032300c8c01707088802220054145250149401707149405250054142220088c027071454051501c14031301c14027070c4c031301c140515014541000314540515015140151415141000605450151415140515014541000814540515014940434214941000610d08434214940515014541000e0c4c031301c0c051501454100061454051501c0c031300c4c0170710d08434205818515014540170714540515005818434210d08705005c1c70501890900041890870508000070501890817071890900044001070201c0c1000e1c0c1000405c1c17071890900051890870504003870501890a000218908705040014705011909000211908545040038545011909000311908545040008545040039000040000525040038525040039000880004525040000525010d09000110d08515040038515010d09000610d08515040004515040011000418081000e400105242 (by decide +kernel)

def state119_79 : List Sig := [0xffffffffaaaaaaaaaaaaaaaaaaaaaaaaffffffffaaaaaaaaaaaaaaaaaaaaaaaa,input 5,input 6,input 1,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_79 : Impossible true (goalAt 119) 6 state119_79.toFinset :=
  node_ok cuts119 [] 0x15050170715050470714908524215050524214908470705c1c44140d05052421490827074001427070d051000509050270714908524214540524214540434205c1c434214540170714540434214908434205c1c464211908524215140545005c1c54501514052421190844501505034300d0c043031514054501505054501514043030d0c034300d05054501514023030d0c034300d05034300d0c023031514054500545054501514051504004c515005451001305450515015140515014908222014908150514940525014908525014940150508880223011908525014940545005850545011908161411108545014940525011c1c32300c8c0541414940525011c1c52501494054140c8c0323009c1c52501494034140c8c0323009c1c32300c8c0341414940525010d08525014940515040050515010d09001310d0851501494051504001434140d050541440014541440015000e0890854140d05022420c4c034141c140515009c1c51500c4c027070c4c051500d050515011c1c31300c4c0541414540515011c1c51501454054140c4c03130 (by decide +kernel)

def state119_80 : List Sig := [0xffffffffccccccccccccccccccccccccffffffffcccccccccccccccccccccccc,input 5,input 6,input 0,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_80 : Impossible true (goalAt 119) 6 state119_80.toFinset :=
  node_ok cuts119 [] 0x15050170715050470714908524215050524214908470705c1c44140d05052421490860424001460420d051000509050604214908524214940150514940222014908524214940524214940222005414223005c1c464211908524215140545005c1c54501514052421190844501505034300d0c043031514054501505054501514043030d0c034300d05054501514060420d0c060420d05034300d0c0604215140545005850545015140525011908525005850464211108525015140525005c1c434210d08524214540515005c1c515014540524210d0843424004c51501454054500545054504004c151405450545014540515011c1c31300c4c0541414540515011c1c51501454054140c4c0313009c1c51501454060420c4c0604209c1c31300c4c0604214540515040050515014540525010d0852504004c434210d0852501454051504001434140d05054141810860424001460421810854140d05022420c8c034141c14052501810852500c8c060421810852500d050525011c1c32300c8c0541414940525011c1c52501494054140c8c03230 (by decide +kernel)

def state119_81 : List Sig := [0xfffffffff0f0f0f0f0f0f0f0f0f0f0f0fffffffff0f0f0f0f0f0f0f0f0f0f0f0,input 5,input 6,input 0,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_81 : Impossible true (goalAt 119) 6 state119_81.toFinset :=
  node_ok cuts119 [] 0x15050170715050470714908524215050524214908470705c1c44140d05052421490827074001427070d051000509050270714908524215140524215140464205c1c464215140170715140464214908445014908222014908150514940525014908525014940150508880223011c1c32300c8c0541414940525011c1c52501494054140c8c0323009c1c52501494034140c8c0323009c1c32300c8c0341414940525011908525014940545005850545011908161411108545014940525005c1c434210d08524214540515005c1c515014540524210d08434240050515014540525010d0852504004c434210d08525014540515011c1c31300c4c0541414540515011c1c51501454054140c4c0313009c1c51501454034140c4c0313009c1c31300c4c034141454051504004c51501454054500545054504004c15140545054501454051504001434140d050541440014541440015000e0890854140d05022420d0c023031c14054500d05054500d0c034140d0c0545008c0c54501505034300d0c043031514054501505054501514043030d0c03430 (by decide +kernel)

def state119_82 : List Sig := [0xffffffffffff0000ffff0000ffff0000ffffffffffff0000ffff0000ffff0000,input 5,input 6,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_82 : Impossible true (goalAt 119) 6 state119_82.toFinset :=
  node_ok cuts119 [] 0x1505034300d0c060301514054501505054501514060300d0c034300d05054501514060500d0c060500d05034300d0c0605015140545005c1c464211908524215140545005c1c545015140524211908445011908525014940545005850545011908161411108545014940525011c1c32300c8c0603014940525011c1c52501494060300c8c0323009c1c52501494060500c8c0605009c1c32300c8c060501494052501490822201490815051494052501490852501494015050888022304004c51501454054500545054504004c151405450545014540515040050515014540525010d0852504004c434210d08525014540515011c1c31300c4c0603014540515011c1c51501454060300c4c0313009c1c51501454060500c4c0605009c1c31300c4c0605014540515005c1c434210d08524214540515005c1c515014540524210d084342180c03414180c05414181406050180c060501814054140d050224240010270718908524218140605040010605018140524209c1c5242180c01707180c04707149085242180c0524214908470705c1c4414 (by decide +kernel)

def state119_83 : List Sig := [0xffffffffffff0000ffff0000ffff0000ffffffffffff0000ffff0000ffff0000,input 4,input 5,input 6,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_83 : Impossible true (goalAt 119) 6 state119_83.toFinset :=
  node_ok cuts119 [] 0x34301514054500d0c054501c14034301514046421514054501190846421514054501190852501514044421494032301494052500c8c052501c14032301494022201494052500888022201494052500888051501514015141454051501494043421454031301454051500c4c051501c140313014540434214540515010d08434214540515010d0870301c14070500890862421c140705009c1c703011c1c6030180c0705009c1c60501814052421c0c060201c0c04707 (by decide +kernel)

def state119_84 : List Sig := [0xffffffff000000000000000000000000ffffffff000000000000000000000000,input 5,input 6,input 0,input 1,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_84 : Impossible true (goalAt 119) 7 state119_84.toFinset :=
  node_ok cuts119 [⟨state119_79,exclude119_79⟩,⟨state119_80,exclude119_80⟩,⟨state119_81,exclude119_81⟩,⟨state119_82,exclude119_82⟩,⟨state119_83,exclude119_83⟩] 0x541405c1c541411c1c524214908541414908524211c1c170711050341414908524209c1d000509c1c341440014241409c1c52421490900051490852424001100054001200044001600034001052421490817071190846421490854501514017071514054501490846421114054140d0c0343010c0c545015140541415140545010c0c34300d0c0341415140545008c0c34300d0c034140d0c0343008c0c545015141000515140545040009000540009000d400160002400085450151405242088805242054145250149405242149405250054142220088c046421494052501514016141514046420585044421514052501494047070c8c032301505052501494047071494052501505032300c8c027071494052500d05032300c8c027070c8c032300d050525014941000514940525040001000540001001440016000140000525014940170710d08434214908515014540170714540515014908434210d09001314540515015140151415141001305450151415140515014541001414540515014940434214941001310d0843421494051501454047070c4c031301505051501454047071454051501505031300c4c027071454051500d05031300c4c027070c4c031300d05051501454100051454051504000500054000500134001600004000451501454100050d050341415051000515051000540038224240015000e1c0c10005400147050 (by decide +kernel)

def state119_85 : List Sig := [0xafafafafafafafafafafafafaaaaaaaaafafafafafafafafafafafafaaaaaaaa,input 0,input 5,input 6,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_85 : Impossible true (goalAt 119) 5 state119_85.toFinset :=
  node_ok cuts119 [] 0x7030149085242180c07050189086050181405242149405250088c032301494052500c8c052501c14060421494070301c14070500890843421454051501154051501494043421454031301454051500c4c051501c14031301454015141114054501514046421494044421494054500d0c054501514034301514034301c1405450 (by decide +kernel)

def state119_86 : List Sig := [0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,0x505050505050505050505050000000005050505050505050505050500000000,input 5,input 6,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_86 : Impossible true (goalAt 119) 4 state119_86.toFinset :=
  node_ok cuts119 [] 0x1c0c052421490860301c14062421814060501c0c070501c14022421114054501514043420d0c054501514034301514034301c14054501494043421454051501490852501494022300c8c05250149403230149407050181085250 (by decide +kernel)

def state119_87 : List Sig := [0x505050505050505050505050000000005050505050505050505050500000000,input 0,input 5,input 6,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_87 : Impossible true (goalAt 119) 5 state119_87.toFinset :=
  node_ok cuts119 [⟨state119_86,exclude119_86⟩] 0x7030149085242180c07050189086050181405242149405250088c032301494052500c8c052501c14060421494070301c14070500890813071490815141490815141494200001494015141c0c043071c0c015141c14023071c14044501514054501190852501110852501514034301514054500d0c054500d0c07050151405150 (by decide +kernel)

def state119_88 : List Sig := [0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 0,0xf0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f0f0f0f0f0f0f0f0f00000000,input 5,input 6,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_88 : Impossible true (goalAt 119) 5 state119_88.toFinset :=
  node_ok cuts119 [⟨state119_86,exclude119_86⟩] 0x7030149085242180c070501890860501814070301c14070500890844501514054501190834301514054500d0c054500d0c0705015140545080000434215140525011108525015140434214508110710d08450710d0843421c0c043421c14025071c14051501490852501494022300c8c05250149403230149407050181085250 (by decide +kernel)

def state119_89 : List Sig := [0x4444444444444444444444444444444444444444444444444444444444444444,input 0,0xf0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f0f0f0f0f0f0f0f0f00000000,input 5,input 6,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_89 : Impossible true (goalAt 119) 5 state119_89.toFinset :=
  node_ok cuts119 [] 0x7030149085242180c070501890860501814070301c14070500890844501514054501190834301514054500d0c054500d0c0705015140515005450515015140525011108525015140414014540515010d4031301454051500c4c051501c1403130145405242149405250088c032301494052500c8c052501c1406042149404342 (by decide +kernel)

def state119_90 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f0f0f0f0f0f0f0f0f00000000,input 5,input 6,input 0,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_90 : Impossible true (goalAt 119) 6 state119_90.toFinset :=
  node_ok cuts119 [⟨state119_24,exclude119_24⟩,⟨state119_34,exclude119_34⟩,⟨state119_85,exclude119_85⟩,⟨state119_87,exclude119_87⟩,⟨state119_88,exclude119_88⟩,⟨state119_89,exclude119_89⟩] 0x1c0c013071c0c060201490852421c0c0524214908602004c1c60301c14052421c14062428000462421c142000018140624214908605014908222014908110514940525014908525014940110508880223011c1c32300c8c0703014940525011c1c52501494070300c8c032301890852501494070500c8c0705018908323018108705014940525004c1c434210d08524214540515004c1c515014540524210d08434280014515014540525010d08525080010434210d08525014540515011c1c31300c4c0703014540515011c1c51501454070300c4c0313009c1c51501454070500c4c0705009c1c31300c4c070501454051501c0c034141c0c054141c14070501c0c070501c14054140d05022421490846421114013071514054501490854501514013071190846421494054501494016141190844421494046421494016141514054501454054501454015148000c15141454200021454015141514054501c0c034300d0c054141514054501c0c054501514054140d0c034301c14054501514034140d0c034301c14034301c1403414151405450 (by decide +kernel)

def state119_91 : List Sig := [0xfafafafafafafafafafafafaaaaaaaaafafafafafafafafafafafafaaaaaaaaa,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 5,input 6,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_91 : Impossible true (goalAt 119) 5 state119_91.toFinset :=
  node_ok cuts119 [] 0x7030149085242180c0705018908605018140130714908524204c1c5242149405250088c032301494052500c8c052501c14060421494016141494052500585052501454043421454043071c0c0705008908230710d0851501454045500c4c051501454031301454070500c4c05150054505150145401514 (by decide +kernel)

def state119_92 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f0f0f0f0f0f0f0f0f000000000,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 5,input 6,input 0,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_92 : Impossible true (goalAt 119) 6 state119_92.toFinset :=
  node_ok cuts119 [⟨state119_38,exclude119_38⟩,⟨state119_91,exclude119_91⟩] 0x1c0c052421490860301c140624218140605004c1c52421490813071490852501494022300c8c0525014940323014940705018108525005850525014940161414940545011108525010d08515014540434214540525010d0851500c4c051501454031301454070500c4c0515005450515014540151414540545080004515010c1c70301c140224208c1c46421514054501114034301514054500d0c054501c1403430151420000 (by decide +kernel)

def state119_93 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f0f0f0f0f0f0f0f0f00000000,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 5,input 6,input 0,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_93 : Impossible true (goalAt 119) 6 state119_93.toFinset :=
  node_ok cuts119 [] 0x1c0c052421490860301c140624218140605004c1c52421490813071490852501494022300c8c0525014940323014940705018108525005850525014940161410d08515014540434214540525010d0851500c4c051501454031301454070500c4c051500545051501454015141505070301c14022420d05044501514054501190852501110852501514051500545051501514034301514054500d0c054500d0c07050151410002 (by decide +kernel)

def state119_94 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f0f0f0f0f0f0f0f0f00000000,input 2,input 5,input 6,input 0,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_94 : Impossible true (goalAt 119) 6 state119_94.toFinset :=
  node_ok cuts119 [] 0x7030149085242180c07050189086050181405242149405250088c032301494052500c8c052501c140604214940525005850161414940434214540515010d0851501494043421454031301454051500c4c051501c14031301454051500545015141454070301c14070500890817071490813071490854141c0c054141c0c034141c14034141c140524205c1c524205c1c52500585052500585051500545051500545070301505070301505070500d05070500d0505450 (by decide +kernel)

def state119_95 : List Sig := [0xffff0000ffff0000ffff000000000000ffff0000ffff0000ffff00000000,input 4,input 5,input 6,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_95 : Impossible true (goalAt 119) 6 state119_95.toFinset :=
  node_ok cuts119 [] 0x34301514054500d0c054501c14034301514046421514054501190852501514044421494032301494052500c8c052501c14060421494022201494052500888051501514015141454051501494043421454031301454051500c4c051501c140313014540434214540515010d0870301c14070500890870301808070301808070501890870501890846421514046421514022201494022201494043421454043421454060201c0c060201c0c062421c14062421c1405242 (by decide +kernel)

def state119_96 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 5,input 6,input 0,input 1,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_96 : Impossible true (goalAt 119) 7 state119_96.toFinset :=
  node_ok cuts119 [⟨state119_39,exclude119_39⟩,⟨state119_42,exclude119_42⟩,⟨state119_52,exclude119_52⟩,⟨state119_55,exclude119_55⟩,⟨state119_59,exclude119_59⟩,⟨state119_65,exclude119_65⟩,⟨state119_25,exclude119_25⟩,⟨state119_35,exclude119_35⟩,⟨state119_90,exclude119_90⟩,⟨state119_92,exclude119_92⟩,⟨state119_93,exclude119_93⟩,⟨state119_94,exclude119_94⟩,⟨state119_95,exclude119_95⟩] 0x703005c1c7030180805242149087030149085242180801707180c070501490870501890a000718908705080018605018908524218142000c05c1c17074001052421490a000514908524240010170705c1c17071190846421490854501514017071514054501490846421114200040d0c034301c0c054501514200031514054501c0c034300d0c200021514054501c14034301c14200010d0c034301c140545015142000b8002a00084000854501514200001514054504000a0009400085242088805242054145250149405242149405250054142220088c046421494052501514016141514046420585044421514052501494100160c8c032301c0c052501494100161494052501c0c032300c8c062421494052501c14032301c14062420c8c060421c140525014941001605850161440000525014941001614940525040000161405850170710d08434214908515014540170714540515014908434210d09001514540515015140151415141001505450151415140515014541001614540515014940434214941001510d0843421494051501454100150c4c031301c0c051501454100151454051501c0c031300c4c100151454051501c14031301c14100150c4c031301c14051501454100150545015144000451501454100151454051504000415140545100054001454141c0c1000e1c0c100051c140705040015000e08909000e400383414 (by decide +kernel)

def state119_97 : List Sig := [0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,0xffff0000ffff0000ffffffffffff0000ffff0000ffff0000ffffffffffff0000,input 6,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_97 : Impossible true (goalAt 119) 4 state119_97.toFinset :=
  node_ok cuts119 [] 0xd0c054501514034301190854501514044501514070500d0c054501c0c052421490860301c14043421814060501c0c070501c14024141494054501110852500c4c0525014940313014908525014940240714540515010d085250 (by decide +kernel)

def state119_98 : List Sig := [0xfafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafa,0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,0xffff0000ffff0000ffffffffffff0000ffff0000ffff0000ffffffffffff0000,input 6,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_98 : Impossible true (goalAt 119) 4 state119_98.toFinset :=
  node_ok cuts119 [] 0xc8c052501494032301490852501494011071494070501810852501494054501110852501c0c052421490860301c14062421814060501c0c070501c14015140c4c054501514031301190854501514044501454051500c4c05450 (by decide +kernel)

def state119_99 : List Sig := [0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,input 0,0xffff0000ffff0000ffffffffffff0000ffff0000ffff0000ffffffffffff0000,input 6,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_99 : Impossible true (goalAt 119) 5 state119_99.toFinset :=
  node_ok cuts119 [⟨state119_97,exclude119_97⟩,⟨state119_98,exclude119_98⟩] 0x34301514054500d0c046421514054501114054501c14034301514052501514044421494032301494052500c8c052421494052500541c52501c1406042149407030149085242180c07050189086050181403130151420001151403130149420000149403130144c047070c4c017071490831301490851501c0c070501c1402414 (by decide +kernel)

def state119_100 : List Sig := [0xfafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafa,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,0xffff0000ffff0000ffffffffffff0000ffff0000ffff0000ffffffffffff0000,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_100 : Impossible true (goalAt 119) 4 state119_100.toFinset :=
  node_ok cuts119 [] 0x1c0c070501c14024141c0c052421490860301c14062421814060500c8c0525014940323014940705018108525014908525014941000914540515010d0852500d0c054501514034301514070500d0c0545010d085450151404450 (by decide +kernel)

def state119_101 : List Sig := [0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 0,0xffff0000ffff0000ffffffffffff0000ffff0000ffff0000ffffffffffff0000,input 5,input 6,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_101 : Impossible true (goalAt 119) 5 state119_101.toFinset :=
  node_ok cuts119 [⟨state119_97,exclude119_97⟩,⟨state119_100,exclude119_100⟩] 0x34301514054500d0c054501c14034301514046421514054501114070301c1407050090507030149085242180c0705018908605018140434215142000115140450710d0843421c0c043421c14200001c140434214508150710d0851501494054501110852500c8c05250149403230149407050181085250149085250149410009 (by decide +kernel)

def state119_102 : List Sig := [0xfafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafa,input 0,0xffff0000ffff0000ffffffffffff0000ffff0000ffff0000ffffffffffff0000,input 5,input 6,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_102 : Impossible true (goalAt 119) 5 state119_102.toFinset :=
  node_ok cuts119 [⟨state119_98,exclude119_98⟩,⟨state119_100,exclude119_100⟩] 0x32301494052500c8c052501c14060421494052421494052500441c52501514044421494070301c1407050090507030149085242180c070501890860501814015141494200011494015141c0c043071c0c015141c14200001c14013071490815141490851500d0c054501514034301514070500d0c05450119085450151404450 (by decide +kernel)

def state119_103 : List Sig := [0x3333000033330000333333333333000033330000333300003333333333330000,0xffff0000ffff0000ffffffffffff0000ffff0000ffff0000ffffffffffff0000,input 5,input 6,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_103 : Impossible true (goalAt 119) 5 state119_103.toFinset :=
  node_ok cuts119 [] 0x34301514054500d0c054501c14034301514044421514054501110851501514015141454031301454051500c4c051501c140313014540434214540515010d0870301c140705009050703014908524204900705018108705014908525011108545014940515010d0851501494032301494052500c8c05250181087050149401507 (by decide +kernel)

def state119_104 : List Sig := [0xffff0000ffff0000ffffffffffff0000ffff0000ffff0000ffffffffffff0000,input 5,input 6,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_104 : Impossible true (goalAt 119) 6 state119_104.toFinset :=
  node_ok cuts119 [⟨state119_99,exclude119_99⟩,⟨state119_101,exclude119_101⟩,⟨state119_102,exclude119_102⟩,⟨state119_103,exclude119_103⟩] 0x1505034300d0c070301514054501505054501514070300d0c034300905054501514070500d0c070500905034300d0c0705015140545005c1c464211908524215140545005c1c545015140524211908445011908525014940545005850545011908161411108545014940525011c1c32300c8c0703014940525011c1c52501494070300c8c032301890852501494070500c8c070501890832301810870501494052501490a00031490815051494052501490852501494015054002c15074003451501454054500545054508000815140545054501454051504002c515014540525010d08525080004434210d08525014540515011c1c31300c4c0703014540515011c1c51501454070300c4c031304001451501454070500c4c070508000031300c4c0705014540515005c1c434210d08524214540515005c1c515014540524210d0843421c0c024141c0c054141c14070501c0c070501c14054140905024141c0c017071c0c047071490852421c0c0524214908470705c1c60301c14052421c14062424001062421c1410004181406242149086050 (by decide +kernel)

def state119_105 : List Sig := [0x3333000033330000333333333333000033330000333300003333333333330000,input 4,input 5,input 6,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_105 : Impossible true (goalAt 119) 5 state119_105.toFinset :=
  node_ok cuts119 [] 0xd0c054501514034301514070500d0c054501110854501514044421454054500545051500c4c051501454031301454070500c4c0515010d0851501454043421c0c070501c14022401c0c052421490812401c14060421c14052421494044421514052501454043421454052500c8c052501494032301494060421c1405250088c05250149405242 (by decide +kernel)

def state119_106 : List Sig := [0xffff0000ffff0000ffffffffffff0000ffff0000ffff0000ffffffffffff0000,input 4,input 5,input 6,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_106 : Impossible true (goalAt 119) 6 state119_106.toFinset :=
  node_ok cuts119 [⟨state119_105,exclude119_105⟩] 0x34301514054500d0c054501c14034301514046421514054501190846421514054501190852501514044421494032301494052500c8c052501c1406042149402220149405250088c200001494052504000051501514015141454051501494043421454031301454051500c4c051501c140313014540434214540515010d08434214540515010d0870301c14070500d05070301c080703011c1c70501890870501890852421c0c047071c0c060201c14062421c1406242 (by decide +kernel)

def state119_107 : List Sig := [0xffffffff000000000000000000000000ffffffff00000000,input 5,input 6,input 0,input 1,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_107 : Impossible true (goalAt 119) 7 state119_107.toFinset :=
  node_ok cuts119 [⟨state119_104,exclude119_104⟩,⟨state119_106,exclude119_106⟩] 0x541405c1c541411c1c524214908541414908524211c1c17071105070501490870501890900051890870504001460501890852421814017071190846421490854501514017071514054501490846421114054140d0c0343010c0c545015140541415140545010c0c34300d0c100051514054501c14034301c141000d0d0c034301c1405450151405242088805242054145250149405242149405250054142220088c046421494052501514016141514046420585044421514052501494047070c8c032301505052501494047071494052501505032300c8c062421494052501c14032301c14062420c8c060421c140525014940170710d08434214908515014540170714540515014908434210d09000d14540515015140151415141001705450151415140515014541000b14540515014940434214941001710d0843421494051501454047070c4c031301505051501454047071454051501505031300c4c100051454051501c14031301c14100170c4c031301c14051501454100054003874144001470501c14054144001454144001500044001052424001452424001600018000052424001052420d0c100020d0c054504001454500d0c1000d0d0c054504000854500c8c100000c8c052504001452500c8c1000b0c8c052504000052500c4c100010c4c051504001451500c4c100170c4c051504000451504001500161c0c10005400143414 (by decide +kernel)

def state119_108 : List Sig := [0xf0f0f0f0fffffffff0f0f0f0f0f0f0f0f0f0f0f0fffffffff0f0f0f0f0f0f0f0,input 2,input 5,input 6,input 0,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_108 : Impossible true (goalAt 119) 6 state119_108.toFinset :=
  node_ok cuts119 [] 0x7030149085242180c0524209c1c2414149085242149405250088c032301494052500c8c052500c8c032301494052501514044421494032301494052500c8c0434214540515010d0851501494043421454031301454051500c4c051500c4c031301454051501514015141454031301454051500c4c070301505070300d05046421514054501114054141514054501c0c054501d14034141514034301490813031490813031505070301505070300d05023031c1407050 (by decide +kernel)

def state119_109 : List Sig := [0xffff0000ffffffffffff0000ffff0000ffff0000ffffffffffff0000ffff0000,input 4,input 5,input 6,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_109 : Impossible true (goalAt 119) 6 state119_109.toFinset :=
  node_ok cuts119 [] 0x34301514054500d0c054501c14034301514046421514054501114024201514054500908052501514044421494032301494052500c8c052501c14032301494052421494052500888022201494052500888051501514015141454051501494043421454031301454051500c4c051501c140313014540434214540515010d0821201454051500848070301c14070500d05070301490852421808070501c90870501490817071c0c060201c0c060201c14027071c1406242 (by decide +kernel)

def state119_110 : List Sig := [0xffffffff000000000000000000000000ffffffff0000000000000000,input 5,input 6,input 0,input 1,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_110 : Impossible true (goalAt 119) 7 state119_110.toFinset :=
  node_ok cuts119 [⟨state119_56,exclude119_56⟩,⟨state119_26,exclude119_26⟩,⟨state119_36,exclude119_36⟩,⟨state119_108,exclude119_108⟩,⟨state119_109,exclude119_109⟩] 0x703005c1c7030180805242149087030149085242180801707180c0341414908524209c1e000209c1c341480004241409c1c524214908170711908464214908545015140170715140545014908464211141000e0d0c034301c0c054501514200001514054501c0c034300d0c0341415140545008c0c34300d0c034140d0c0343008c0c5450151405242088805242054145250149405242149405250054142220088c0464214940525015140161415140464205850444215140525014941000e0c8c032301c0c052501494100141494052501c0c032300c8c027071494052500d05032300c8c027070c8c032300d050525014940170710d08434214908515014540170714540515014908434210d09001314540515015140151415141001305450151415140515014541001414540515014940434214941001310d08434214940515014541000e0c4c031301c0c051501454100131454051501c0c031300c4c027071454051500d05031300c4c027070c4c031300d05051501454100054003874141c0c1000e1c0c100050d05034141490900041490817074003817071490a000414908170740010170715141000215140343040038343015142000315140343040008343014941000014940323040038323014941001414940323040000323014541000114540313040038313014541001314540313040004313040015000515051000e400587050 (by decide +kernel)

def state119_111 : List Sig := roots 119
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_111 : Impossible true (goalAt 119) 8 state119_111.toFinset :=
  node_ok cuts119 [⟨state119_33,exclude119_33⟩,⟨state119_37,exclude119_37⟩,⟨state119_43,exclude119_43⟩,⟨state119_53,exclude119_53⟩,⟨state119_57,exclude119_57⟩,⟨state119_60,exclude119_60⟩,⟨state119_71,exclude119_71⟩,⟨state119_73,exclude119_73⟩,⟨state119_75,exclude119_75⟩,⟨state119_78,exclude119_78⟩,⟨state119_84,exclude119_84⟩,⟨state119_96,exclude119_96⟩,⟨state119_107,exclude119_107⟩,⟨state119_110,exclude119_110⟩] 0x8003470300d05070308003054141c14070508002c70301c14070508002854140d050224280024703005c1c703040010602014908524280020703014908524240010602005c1c60308001c70501490870504001062428000462428001870508000060504001062421490860508001454140d0c034304000870301514054508001054141514054504000870300d0c034308000c34141514054504000870500d0c070508000834140d0c034304000870501514054504001017071190846424000852421514054504000c17071514054504000852421190844504000047070c8c032304000070301494052504000047071494052504000070300c8c032304000062421494052504000070500c8c070504000062420c8c060424000070501494052504000052420888052424000015051494052504000052421494052504000015050888022304000046421494052504000054500585054504000046420585044424000054501494052504000447070c4c031304000470301454051504000447071454051504000470300c4c031304000427071454051504000470500c4c070504000427070c4c0313040004705014540515040004170710d08434240004524214540515040004170714540515040004524210d08434240005000114540515040004545005450545040005000105450151440004545014540515040001000014540515040000525010d08525040001000110d084342400005250145405150 (by decide +kernel)

theorem lower119 : Claim 119 9 :=
  fromSearch 1348 (by decide +kernel) exclude119_111

def rule247_0 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower245 none (by decide +kernel)

def rule247_1 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower246 none (by decide +kernel)

def rule247_2 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower243 none (by decide +kernel)

def rule247_3 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower215 none (by decide +kernel)

def rule247_4 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower231 none (by decide +kernel)

def rule247_5 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower119 none (by decide +kernel)

def cuts247 : Cuts (goalAt 247) := [rule247_0,rule247_1,rule247_2,rule247_3,rule247_4,rule247_5]

def state247_0 : List Sig := roots 247
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_0 : Impossible true (goalAt 247) 10 state247_0.toFinset :=
  node_ok cuts247 [] 0x40014d0501c0c0d05040014b03030200c08040014d05030200c08040014b0301c0c090504000cb0301c14070504000cd05028200a0804000cb03028200a0804000cd0501c14070504000c703028200a0804000cc0801c140c0804000c70301c14070504000cc08028200a08040014d05014908d05040014c24224200908040014d05024200908040014c24214908c05040010703024200908040010c08014908c08040010703014908524240010c0802420090804000c70502420090804000ca0804000ca0804000c70504000c60504000ca08024200908040008941415140545040008d05021200848040008941421200848040008d05015140545040008541421200848040008c08015140c08040008541415140545040008c08021200848040008341421200848040008a0800d0c0a0804000834140d0c0343040008a08021200848040008170721200848040008908015140908040008170715140545040008908021200848040000c24214940525040000d05020a00828040000c24220a00828040000d05014940525040000470720a00828040000c08014940c08040000470714940525040000c08020a00828040000624220a00828040000a0800c8c0a0804000062420c8c0604240000a08020a00828040000524220a00828040000908014940908040000524214940525040000908020a00828040000464220a00828040000848005850848040000464205850444240000848020a00828040004870714540515040004d05020600818040004870720600818040004d05014540515040004470720600818040004c08014540c08040004470714540515040004c08020600818040004270720600818040004a0800c4c0a0804000427070c4c0313040004a08020600818040004170720600818040004908014540908040004170714540515040004908020600818040005000120600818040004848005450848040005000105450151440004848020600818040001000020600818040000828010d08828040001000110d084342400008280206008180 (by decide +kernel)

theorem lower247 : Claim 247 11 :=
  fromSearch 1348 (by decide +kernel) exclude247_0


open PEqualNP.CircuitLowerBounds

def graph : Sig := goalAt 255
theorem graph_proper : proper graph := by unfold proper; decide +kernel

def edgeList : List Nat := [0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7]
def target (x : Fin 8 → Bool) : Bool :=
  decide (∃ i < edgeList.length / 2,
    (List.ofFn x).getD (edgeList.getD (2*i) 0) false = true ∧
    (List.ofFn x).getD (edgeList.getD (2*i+1) 0) false = true)

def smallCircuit : Circuit := ⟨[⟨.or, [0, 1]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [7, 8]⟩, ⟨.or, [2, 6]⟩, ⟨.or, [8, 11]⟩, ⟨.or, [5, 7]⟩, ⟨.or, [0, 2]⟩, ⟨.or, [3, 14]⟩, ⟨.and, [9, 10]⟩, ⟨.and, [12, 13]⟩, ⟨.and, [6, 15]⟩, ⟨.or, [16, 17]⟩, ⟨.or, [19, 18]⟩], 20⟩

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


def lowRow (i : Fin 8) : Row := Fin.ofNat 256 (1 <<< ([4, 4, 5, 6, 0, 0, 0, 0] : List Nat).getD i.val 0)
def highRow (i : Fin 8) : Row := Fin.ofNat 256 ((1 <<< i.val) ||| (1 <<< ([4, 4, 5, 6, 0, 0, 0, 0] : List Nat).getD i.val 0))

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

end PEqualNP.Outside.L_meta_31389_aux

open PEqualNP.Outside.L_meta_31389_aux in
theorem PEqualNP.Outside.L_meta_31389 : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true))  := by
  intro gates o fit _ correct
  exact replaceShort lowerGraph gates o fit correct

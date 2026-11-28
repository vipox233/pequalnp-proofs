import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_31403_aux


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
  (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 2 &&& x 5) ||| (x 0 &&& x 6) ||| (x 1 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 5 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 2 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7)


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
  fromLift 5 4 1285 lower97 (by decide +kernel)

def cuts116 : Cuts (goalAt 116) := []

def state116_0 : List Sig := roots 116
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude116_0 : Impossible true (goalAt 116) 3 state116_0.toFinset :=
  node_ok cuts116 [] 0x1c0c064441911050301c0c054441511060301511064440905054440d0c07030140503430191106040181106044151105040141105044 (by decide +kernel)

theorem lower116 : Claim 116 4 :=
  fromSearch 69600512 (by decide +kernel) exclude116_0

def cuts81 : Cuts (goalAt 81) := []

def state81_0 : List Sig := roots 81
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude81_0 : Impossible true (goalAt 81) 3 state81_0.toFinset :=
  node_ok cuts81 [] 0x140401101140404101141005040140405040141004101044041101104041110044405010105004140104044140105005010044401110044044140105005040044405040044041110044405040105004140 (by decide +kernel)

theorem lower81 : Claim 81 4 :=
  fromSearch 4 (by decide +kernel) exclude81_0

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
  ruleFor 117 lower101 none (by decide +kernel)

def rule117_2 : {c : Cut // CutGood (goalAt 117) c} :=
  ruleFor 117 lower116 none (by decide +kernel)

def rule117_3 : {c : Cut // CutGood (goalAt 117) c} :=
  ruleFor 117 lower81 none (by decide +kernel)

def rule117_4 : {c : Cut // CutGood (goalAt 117) c} :=
  ruleFor 117 lower53 none (by decide +kernel)

def rule117_5 : {c : Cut // CutGood (goalAt 117) c} :=
  ruleFor 117 lower97 none (by decide +kernel)

def cuts117 : Cuts (goalAt 117) := [rule117_0,rule117_1,rule117_2,rule117_3,rule117_4,rule117_5]

def state117_0 : List Sig := [0xfffffffffffffffffafafafafafafafafffffffffffffffffafafafafafafafa,input 6,input 0,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude117_0 : Impossible true (goalAt 117) 4 state117_0.toFinset :=
  node_ok cuts117 [] 0xd05060441811024400d0c060441811100031411060440905050441405050441411011050d0c050441411024301151060440841445441151050440545045440545045441151015140c4c07030 (by decide +kernel)

def state117_1 : List Sig := [0xfafafafafafafafa0000000000000000fafafafafafafafa,input 6,input 0,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude117_1 : Impossible true (goalAt 117) 4 state117_1.toFinset :=
  node_ok cuts117 [] 0x7030181106044140c05044181102414141107030141105044180c045441811021051151045441411015141151071301151045441c0c03414181103430181102420141103430141103130115101514115105014 (by decide +kernel)

def state117_2 : List Sig := [0xfafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafa,input 0,input 4,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude117_2 : Impossible true (goalAt 117) 5 state117_2.toFinset :=
  node_ok cuts117 [⟨state117_0,exclude117_0⟩,⟨state117_1,exclude117_1⟩] 0x70300d0507030150506444191107030191106444150503414140c07030044147030180805444151107030151105444180801105180c034141511054441911100051911034144000c24141911054441511041050545015141c0c045441151041051151045441c0c015141c0c021051151045441911100021851021054000c21051911045441151011051151045441511015141451011050545015141511045441151100004000041401505034300d0c070308000470301505200001405070300d0c034301911100031911060400d0c060401911034301811060404000c60441511024201511050400d0c05040151103430141105040090805044 (by decide +kernel)

def state117_3 : List Sig := [0x5555555555555555505050505050505055555555555555555050505050505050,input 0,input 6,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude117_3 : Impossible true (goalAt 117) 4 state117_3.toFinset :=
  node_ok cuts117 [] 0x34141811060440910050441811024141411050141411050440441411101811031301811021201411031301411031301c4c041050c4c060440d0c060440841450440d0c05044090c034301c0c050140d0c04544 (by decide +kernel)

def state117_4 : List Sig := [0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0,input 6,input 0,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude117_4 : Impossible true (goalAt 117) 5 state117_4.toFinset :=
  node_ok cuts117 [⟨state117_0,exclude117_0⟩,⟨state117_3,exclude117_3⟩] 0x100030d05034141405060441811100031811060441405034140910034300840434304000c60441811034301811060444000c21010841434141411050441811100051811034144000c2414181105044141105014054145014104145044141105014141105044104141505054143430044043430090805044141103430141105044090801101090c025051151045441811031301811025050c4c031301811045441151015051151045441411031301411015050c4c031301411045441151041050c4c031301405045441151041051151045441405031300c4c200010c4c031300d0c045441151200001151045440d0c031300c4c10000400007030 (by decide +kernel)

def state117_5 : List Sig := [0xffff0000ffff0000aaaa0000aaaa0000ffff0000ffff0000aaaa0000aaaa,input 0,input 6,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude117_5 : Impossible true (goalAt 117) 4 state117_5.toFinset :=
  node_ok cuts117 [] 0x1c0c064441911050301911060401811060440d0c070301405034301151064440c4c045441050045441151041440c4c04544115103130151102414191105444141105044151105040180c05444151107030115103130115105444 (by decide +kernel)

def state117_6 : List Sig := [0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa,input 0,input 6,input 2,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude117_6 : Impossible true (goalAt 117) 5 state117_6.toFinset :=
  node_ok cuts117 [⟨state117_0,exclude117_0⟩,⟨state117_5,exclude117_5⟩] 0x34141911064440d05034141911064440d05054441911024141511015051511054440541600011511054444000464441810060441811054441410050441411034301040441050d0c034304000200000d0c07030115106444094144544115105444054144544105004544115104144114144544400083130 (by decide +kernel)

def state117_7 : List Sig := roots 117
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude117_7 : Impossible true (goalAt 117) 6 state117_7.toFinset :=
  node_ok cuts117 [⟨state117_2,exclude117_2⟩,⟨state117_4,exclude117_4⟩,⟨state117_6,exclude117_6⟩] 0x4000c70300d05070304000c54141911064444000c70301911064444000c54140d05050304000470300541470304000460201511054444000470301511054444000460200541460304000434141511054444000464444000464444000434144000c24144000464441511054444000054140d0c034304000070304000070304000054148000450144000070300d0c034304000064444000c64444000060400d0c060404000064440d0c060444000060404000060444000054440908054444000050400d0c050404000054440d0c050444000050400908050444001045050c4c031304000870301151045448000845051151045444000870300c4c031304000c25051151045444000864440c4c064444000c25050c4c031304000864441151045444000415051151045444000454440c4c054444000415050c4c03130400045444115104544400010000105004140400003430115104544400020000115104544400003430105004144 (by decide +kernel)

theorem lower117 : Claim 117 7 :=
  fromSearch 1284 (by decide +kernel) exclude117_7

def cuts82 : Cuts (goalAt 82) := []

def state82_0 : List Sig := roots 82
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude82_0 : Impossible true (goalAt 82) 3 state82_0.toFinset :=
  node_ok cuts82 [] 0x140401202140404202141005040140405040141004202048081202108081210048405010109004240108084240109005010048401210048084240109005040048405040048081210048405040109004240 (by decide +kernel)

theorem lower82 : Claim 82 4 :=
  fromSearch 16842816 (by decide +kernel) exclude82_0

theorem lower114 : Claim 114 5 :=
  fromLift 5 32 23134272 lower82 (by decide +kernel)

def cuts102 : Cuts (goalAt 102) := []

def state102_0 : List Sig := roots 102
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude102_0 : Impossible true (goalAt 102) 3 state102_0.toFinset :=
  node_ok cuts102 [] 0x188886444191102444098886222108182622191106040181106044188884644119106022119106444090184644109004644119104244 (by decide +kernel)

theorem lower102 : Claim 102 4 :=
  fromSearch 18875744 (by decide +kernel) exclude102_0

def rule118_0 : {c : Cut // CutGood (goalAt 118) c} :=
  ruleFor 118 lower114 none (by decide +kernel)

def rule118_1 : {c : Cut // CutGood (goalAt 118) c} :=
  ruleFor 118 lower116 none (by decide +kernel)

def rule118_2 : {c : Cut // CutGood (goalAt 118) c} :=
  ruleFor 118 lower102 none (by decide +kernel)

def rule118_3 : {c : Cut // CutGood (goalAt 118) c} :=
  ruleFor 118 lower82 none (by decide +kernel)

def cuts118 : Cuts (goalAt 118) := [rule118_0,rule118_1,rule118_2,rule118_3]

def state118_0 : List Sig := [0xffffffff00000000f0f0f0f000000000ffffffff00000000f0f0f0f0,0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0,input 6,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude118_0 : Impossible true (goalAt 118) 4 state118_0.toFinset :=
  node_ok cuts118 [] 0xc88850441411032220d0c050441411024301191050440c8c046440c8c046441191032300c8c046441191032301c0c050440c88850441811046440c8c046441811024401811060440d0510003 (by decide +kernel)

def state118_1 : List Sig := [0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0,input 6,input 1,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude118_1 : Impossible true (goalAt 118) 5 state118_1.toFinset :=
  node_ok cuts118 [⟨state118_0,exclude118_0⟩] 0x100030d05034141405060441811100031811060441405034140910034308000034304000c60441811034301811060444000d00034000c34141411050441811032221811034140c88832221811050441411050140c88832221081850441411050141411050441081832220c88834300c8883430098885044141103430141105044098883222090c026061191046441811032301811026060c8c032301811046441191032221191046441411032301411032220c8c032301411046441191042060c8c032301405046441191042061191046441405032300c8c026220c8c032300d0c046441191026221191046440d0c032300c8c10000400007030 (by decide +kernel)

def state118_2 : List Sig := [0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc,input 1,input 4,input 2,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude118_2 : Impossible true (goalAt 118) 5 state118_2.toFinset :=
  node_ok cuts118 [] 0x7030191106444140c034301c0c050140d0c064441810060441811026220d0c034300988824200d0c034300908070301888870300c88834141911032221911054440c8c070301888832300585064440c8c064440c8c034300988832300c88832304000446441c0c060201c0c060200d05064440d0506444 (by decide +kernel)

def state118_3 : List Sig := [0xffff0000ffff0000cccc0000cccc0000ffff0000ffff0000cccc0000cccc,input 1,input 6,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude118_3 : Impossible true (goalAt 118) 4 state118_3.toFinset :=
  node_ok cuts118 [] 0x1c0c064441911050301911060401811060440d0c070301405034301191064440c8c046441090046441191042440c8c04644119103230151103222191105444141105044151105040180c05444151107030119103230119105444 (by decide +kernel)

def state118_4 : List Sig := [0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,input 1,input 6,input 2,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude118_4 : Impossible true (goalAt 118) 5 state118_4.toFinset :=
  node_ok cuts118 [⟨state118_3,exclude118_3⟩] 0x62221911064441088834141911064440d05054441911032221511032221511054440c88a00001511054444000864441810060441811054441410050441411034301888842060d0c034300988826220d0c070301191064440981846441191054440c8884644109004644119104244188884644180883230 (by decide +kernel)

def state118_5 : List Sig := [0xf3f3f3f3f3f3f3f3f0f0f0f0f0f0f0f0f3f3f3f3f3f3f3f3f0f0f0f0f0f0f0f0,input 1,input 6,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude118_5 : Impossible true (goalAt 118) 4 state118_5.toFinset :=
  node_ok cuts118 [] 0x1888860441811024401411060440c88850440c88850441411032221191060440c8c046441191050440c8c046440c8c046441191032300c8c046441191042441811034301811100031411034301411024300d0c07030140503430 (by decide +kernel)

def state118_6 : List Sig := [0x3333333333333333000000000000000033333333333333330000000000000000,input 1,input 6,input 2,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude118_6 : Impossible true (goalAt 118) 5 state118_6.toFinset :=
  node_ok cuts118 [⟨state118_5,exclude118_5⟩] 0x62221911064441088854441911032221511032221511054440c88864441810060441811054441410050441411034301888842060d0c016141911032301911032221511032301511032300d0c024220c8c072301888832301911034141911034141511032221511032224000034308000034301c0c04644 (by decide +kernel)

def state118_7 : List Sig := [0x3333333333333333333300003333000033333333333333333333000033330000,input 4,input 6,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude118_7 : Impossible true (goalAt 118) 4 state118_7.toFinset :=
  node_ok cuts118 [] 0x1c0c064441911050301911060401811060440d0c070301405034301511050401411050441511064440c88854441c0c054441511060301191032301911046441091046441191042400c8c04644119103230119103230151104644 (by decide +kernel)

def state118_8 : List Sig := [0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 4,input 6,input 1,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude118_8 : Impossible true (goalAt 118) 5 state118_8.toFinset :=
  node_ok cuts118 [⟨state118_7,exclude118_7⟩] 0x7030191106444140c026061911064440981864441810060441811034301c0c050140d0c054441410050441411026220d0c034300988846441911032301191042401191046441091032301191046440c8c046441511032301191200001191046444000462221511064440d05054441c0c05444180c03222 (by decide +kernel)

def state118_9 : List Sig := [0xf0f0fffff0f0fffff0f0f0f0f0f0f0f0f0f0fffff0f0fffff0f0f0f0f0f0f0f0,input 4,input 6,input 1,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude118_9 : Impossible true (goalAt 118) 4 state118_9.toFinset :=
  node_ok cuts118 [] 0x1c0c060441811050301191060440c8c046440c8c046441191032301191054440c8c046440c8c046441191032301511060440c88854441c0c054441511032221811034301811100030d0c07030140503430151103430141105044 (by decide +kernel)

def state118_10 : List Sig := [0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000,input 4,input 6,input 1,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude118_10 : Impossible true (goalAt 118) 5 state118_10.toFinset :=
  node_ok cuts118 [⟨state118_9,exclude118_9⟩] 0x7030191106444140c064441810060441811034301c0c050140d0c026220d0c03430090c046441911032301191042401191046441091032301191046440c8c046440c8c032301191034141911032221911072221c0c03222191103414191103414400003430800003430119103230119103230188885444 (by decide +kernel)

def state118_11 : List Sig := roots 118
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude118_11 : Impossible true (goalAt 118) 6 state118_11.toFinset :=
  node_ok cuts118 [⟨state118_1,exclude118_1⟩,⟨state118_2,exclude118_2⟩,⟨state118_4,exclude118_4⟩,⟨state118_6,exclude118_6⟩,⟨state118_8,exclude118_8⟩,⟨state118_10,exclude118_10⟩] 0x4000c70300d05070304000c54141911064444000c70301911064444000c54140d05050308001470300c88870304000862221511054448001070301511054444000862220c88860304000c34141511054444000864440c88864444000c34140c88832224000864441511054444000054140d0c034304000070304000070304000054148000050144000070300d0c034304000064444000c64444000060400d0c060404000064440d0c060444000060404000060444000054440988854444000050400d0c050404000054440d0c050444000050400988850448000c62220c8c032304000470301191046448000862221191046444000470300c8c032304000c26061191046444000464440c8c064444000c26060c8c032304000464441191046444000832221191046444000454440c8c054448000432220c8c03230400045444119104644400002622109004240400003430119104644400002622119104644400003430109004244 (by decide +kernel)

theorem lower118 : Claim 118 7 :=
  fromSearch 18941248 (by decide +kernel) exclude118_11

theorem lower99 : Claim 99 5 :=
  fromLift 5 2 101 lower97 (by decide +kernel)

theorem lower83 : Claim 83 5 :=
  fromLift 5 1 68 lower82 (by decide +kernel)

def rule115_0 : {c : Cut // CutGood (goalAt 115) c} :=
  ruleFor 115 lower113 none (by decide +kernel)

def rule115_1 : {c : Cut // CutGood (goalAt 115) c} :=
  ruleFor 115 lower114 none (by decide +kernel)

def rule115_2 : {c : Cut // CutGood (goalAt 115) c} :=
  ruleFor 115 lower99 none (by decide +kernel)

def rule115_3 : {c : Cut // CutGood (goalAt 115) c} :=
  ruleFor 115 lower83 none (by decide +kernel)

def cuts115 : Cuts (goalAt 115) := [rule115_0,rule115_1,rule115_2,rule115_3]

def state115_0 : List Sig := roots 115
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude115_0 : Impossible true (goalAt 115) 6 state115_0.toFinset :=
  node_ok cuts115 [] 0x4000c703008c0c70304000c50101810060404000c70301810060404000c501008c0c50304000870300c88870304000862221410050404000870301410050404000862220c88860304000900021410050404000860400c88860404000900020c88832224000860401410050404000062220c8c032304000070301090042404000062221090042404000070300c8c032304000023031090042404000060400c8c060404000023030c8c032304000060401090042404000032221090042404000050400c8c050404000032220c8c032304000050401090042404000443030c4c031304000470301050041404000443031050041404000470300c4c031304000423031050041404000460400c4c060404000423030c4c031304000460401050041404000813031050041404000850400c4c050404000813030c4c0313040008504010500414040001000010500414040000424008c88424040001000108c882322400004240105004140 (by decide +kernel)

theorem lower115 : Claim 115 7 :=
  fromSearch 68 (by decide +kernel) exclude115_0

theorem lower103 : Claim 103 6 :=
  fromLift 6 2 1381 lower101 (by decide +kernel)

def cuts51 : Cuts (goalAt 51) := []

def state51_0 : List Sig := roots 51
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude51_0 : Impossible true (goalAt 51) 3 state51_0.toFinset :=
  node_ok cuts51 [] 0x4c0c32220c88812220484032300c8c012300c88832300c8c011030444031300c4c0113008c8831300c4c023220c4c0323008c883130 (by decide +kernel)

theorem lower51 : Claim 51 4 :=
  fromSearch 68 (by decide +kernel) exclude51_0

theorem lower55 : Claim 55 5 :=
  fromLift 5 2 1348 lower53 (by decide +kernel)

def rule119_0 : {c : Cut // CutGood (goalAt 119) c} :=
  ruleFor 119 lower117 none (by decide +kernel)

def rule119_1 : {c : Cut // CutGood (goalAt 119) c} :=
  ruleFor 119 lower118 none (by decide +kernel)

def rule119_2 : {c : Cut // CutGood (goalAt 119) c} :=
  ruleFor 119 lower115 none (by decide +kernel)

def rule119_3 : {c : Cut // CutGood (goalAt 119) c} :=
  ruleFor 119 lower103 none (by decide +kernel)

def rule119_4 : {c : Cut // CutGood (goalAt 119) c} :=
  ruleFor 119 lower83 none (by decide +kernel)

def rule119_5 : {c : Cut // CutGood (goalAt 119) c} :=
  ruleFor 119 lower114 none (by decide +kernel)

def rule119_6 : {c : Cut // CutGood (goalAt 119) c} :=
  ruleFor 119 lower82 none (by decide +kernel)

def rule119_7 : {c : Cut // CutGood (goalAt 119) c} :=
  ruleFor 119 lower113 none (by decide +kernel)

def rule119_8 : {c : Cut // CutGood (goalAt 119) c} :=
  ruleFor 119 lower99 none (by decide +kernel)

def rule119_9 : {c : Cut // CutGood (goalAt 119) c} :=
  ruleFor 119 lower81 none (by decide +kernel)

def rule119_10 : {c : Cut // CutGood (goalAt 119) c} :=
  ruleFor 119 lower118 (some (1,input 2,input 6)) (by decide +kernel)

def rule119_11 : {c : Cut // CutGood (goalAt 119) c} :=
  ruleFor 119 lower51 none (by decide +kernel)

def rule119_12 : {c : Cut // CutGood (goalAt 119) c} :=
  ruleFor 119 lower55 none (by decide +kernel)

def rule119_13 : {c : Cut // CutGood (goalAt 119) c} :=
  ruleFor 119 lower117 (some (1,input 2,input 6)) (by decide +kernel)

def rule119_14 : {c : Cut // CutGood (goalAt 119) c} :=
  ruleFor 119 lower53 none (by decide +kernel)

def rule119_15 : {c : Cut // CutGood (goalAt 119) c} :=
  ruleFor 119 lower97 none (by decide +kernel)

def rule119_16 : {c : Cut // CutGood (goalAt 119) c} :=
  ruleFor 119 lower101 none (by decide +kernel)

def rule119_17 : {c : Cut // CutGood (goalAt 119) c} :=
  ruleFor 119 lower118 (some (1,input 4,input 6)) (by decide +kernel)

def rule119_18 : {c : Cut // CutGood (goalAt 119) c} :=
  ruleFor 119 lower118 (some (3,input 4,input 6)) (by decide +kernel)

def cuts119 : Cuts (goalAt 119) := [rule119_0,rule119_1,rule119_2,rule119_3,rule119_4,rule119_5,rule119_6,rule119_7,rule119_8,rule119_9,rule119_10,rule119_11,rule119_12,rule119_13,rule119_14,rule119_15,rule119_16,rule119_17,rule119_18]

def state119_0 : List Sig := [0xffffffffffffffff0f0f0f0f00000000ffffffffffffffff0f0f0f0f00000000,input 6,input 5,input 0,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_0 : Impossible true (goalAt 119) 6 state119_0.toFinset :=
  node_ok cuts119 [] 0x34141411050441811032221811034140c88832221811050441411070300c8887030188885044141107030141105044188883222180c0343004c1c34300988850441411034301411050440988813070988832221191046441411032301411032220c8c032301411046441191027071191046441811032301811027070c8c032301811046441191062220c8c032301c0c046441191062221191046441c0c032300c8c026220585024220d0c046441191026221191046440d0c016140d0c013071151045441411031301411013070c4c0313014110454411511000611510454411910232211911000608c8823221191045441151027071151045441811031301811027070c4c031301811045441151100060c4c031301c0c045441151100061151045441c0c031300c4c100060545015140d0c045441151100061151045440d0c015140d0c070300d0507030400106044181107030181106044400103414140c034300d05034304000860441811034301811060444000834140d0510004400105014 (by decide +kernel)

def state119_1 : List Sig := [0x3333333333333333333300003333000033333333333333333333000033330000,input 4,input 6,0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000,input 5,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_1 : Impossible true (goalAt 119) 5 state119_1.toFinset :=
  node_ok cuts119 [] 0x45441911031301151031301151045440c4c045441411031301151070301911064440d05031301151031301151060440d0c050141c0c034300908850440d0c050440c8c046440c8c046441411064440c88850441c0c050441411060301151023221151046441191032301911046440c8c04644119103230119103230141104644 (by decide +kernel)

def state119_2 : List Sig := [0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 4,input 6,0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000,input 5,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_2 : Impossible true (goalAt 119) 6 state119_2.toFinset :=
  node_ok cuts119 [⟨state119_1,exclude119_1⟩] 0x1191064440c8c046440c8c046441191032301191050440c8c0464480000464411911000711510464408c8845441151064440c4c045440c4c045441151031301151050440c4c0454408c8845441151023221c0c0644419110341409c1c64441911027070c8c046440c8c046440c4c045440c4c045441811034301405070300d0c026221411034301411026220d0c034300988862221411064440d05050441c0c05044180c03222 (by decide +kernel)

def state119_3 : List Sig := [0xf0fffff0000ffff0f0f0f0f000000000f0fffff0000ffff0f0f0f0f00000000,input 4,input 6,input 5,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_3 : Impossible true (goalAt 119) 5 state119_3.toFinset :=
  node_ok cuts119 [] 0x1191060440c8c046440c8c046441191032301191032300c8c0464411510464408c8845441151060440c4c045440c4c045441151031301151031300c4c045441c0c060441811042221c11060440c88860441c0c06222180c060301191024221191034301151015141151034301811034301811034140d0c050141c0c03430090c03430141105044 (by decide +kernel)

def state119_4 : List Sig := [0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000,input 4,input 6,0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000,input 5,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_4 : Impossible true (goalAt 119) 6 state119_4.toFinset :=
  node_ok cuts119 [⟨state119_3,exclude119_3⟩] 0x1191064440c8c046440c8c046441191032301191032300c8c0464411510464408c8845441151064440c4c045440c4c045441151031301151031300c4c045441c0c064441911034140c8c046440c8c046440c4c045440c4c045441811034301405070300d0c024300d0c034300988834141911032221911072221c0c03222119103230119103230115103130115103130191103414191103414400103430800003430188885044 (by decide +kernel)

def state119_5 : List Sig := [0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000,input 5,input 0,input 1,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_5 : Impossible true (goalAt 119) 7 state119_5.toFinset :=
  node_ok cuts119 [⟨state119_0,exclude119_0⟩,⟨state119_2,exclude119_2⟩,⟨state119_4,exclude119_4⟩] 0x8000870300c88870304002062221411050448000470301411050444002062220c88860304001034141411050444002064440c88864444001034140c88832224002064441411050444002462220c8c032304001c70301191046444002462221191046444001c70300c8c032304002032221191046444001c50440c8c050444002432220c8c032304001c50441191046444001027071191046444001c64440c8c064444001027070c8c032304001c64441191046444001843070c4c031304001470301151045444001843071151045444001470300c4c031304002013071151045444001450440c4c050444001813070c4c031304001450441151045444001d000611510454440014464408c88464440019000608c8823224001446441151045444001027071151045444001464440c4c064444001027070c4c031304001464441151045444001070300d05070304001050141911064444001070301911064444001050140d05024404001070300d0c034304001050144001050144001070308000070304001050140d0c034304002032220988824304001050440d0c050444001032220d0c034304002050440988850444001c32300d0c032304001046440988846444001032300988832304001c46440d0c046444001431300d0c031304001045444001045444001031304001831304001445440d0c04544400090002400086044 (by decide +kernel)

def state119_6 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_6 : Impossible true (goalAt 119) 5 state119_6.toFinset :=
  node_ok cuts119 [] 0x32301191046440c8c016141191046440585046440c8c032301191046441811032301191045441191023221151031301151045440c4c015141151045440545045440c4c031301151045441811031301151034140d0c03430400203430098883430180c034140c88832220905050440d0c060441811042220d0506044181104307 (by decide +kernel)

def state119_7 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 5,0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0,input 0,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_7 : Impossible true (goalAt 119) 6 state119_7.toFinset :=
  node_ok cuts119 [⟨state119_6,exclude119_6⟩] 0x34300c8883430098885044141103430141105044098883222180c100041411050441811032221811200000c888322218110504414110501405c1c501410c1c504414110501414110504410c1c170705c1c32221191046441411032301411032220c8c032301411046441191026220c8c032300d0c046441191026221191046440d0c032300c8c100041191046441811032301811100090c8c032301811046441191043070585016141405046441191043071191046441405016140585017071151045441411031301411017070c4c0313014110454411511000611510454411910232211911000608c8823221191045441151100060c4c031300d0c045441151100061151045440d0c031300c4c100041151045441811031301811100060c4c031301811045441151043070545015141405045441151043071151045441405015140545050144001050144000834300d0c050140d0c034304000900044000834304002c3430400106044181103430181106044400110004140c1000c400303414 (by decide +kernel)

def state119_8 : List Sig := [0xffffffff000000000000000000000000ffffffff0000000000000000,input 5,0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0,input 0,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_8 : Impossible true (goalAt 119) 6 state119_8.toFinset :=
  node_ok cuts119 [] 0xd0c032220d0c026221411050440d0c050441411026220c88860300d05050441411027070c88832220d05032220c88827071411050440c88846441191050440c8c050440c88832300c8c050441191046440988832300c8c034301191046440988846441191034300c8c0323009c1c46441191034140c8c0323009c1c32300c8c0341411910464405c1c45441151050440c4c0504405c1c31300c4c0504411510454440018454411510464408c88464440018232208c8846441151045444001831300c4c034301151045444001845441151034300c4c0313009c1c45441151034140c4c0313009c1c31300c4c034141151045440d0c023030d0c100040d05034140d0c034140d0c1000408c0c230714110430714110322214050322214110501414110322210c1c322211910501411910323010c1c323011910430711910323014050323011510501411510313010c1c313011510430711510313014050313040031000414041000c400106044 (by decide +kernel)

def state119_9 : List Sig := [0x3333333333333333333330303333303033333333333333333333303033333030,input 4,0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0,input 6,input 0,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_9 : Impossible true (goalAt 119) 5 state119_9.toFinset :=
  node_ok cuts119 [] 0x34141811060440910034301811060440841c45441811031301151031301151045440c4c031301151045440c4c045441411031301151070301411060440c88850440c88850441411032220d0c050441411024301191032301811046441151023221151046440c8c046441191032300c8c04644119103230119103230141104644 (by decide +kernel)

def state119_10 : List Sig := [0xfffffffffffffffffffff0f0fffff0f0fffffffffffffffffffff0f0fffff0f0,input 4,0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0,input 6,input 0,input 1,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_10 : Impossible true (goalAt 119) 6 state119_10.toFinset :=
  node_ok cuts119 [⟨state119_9,exclude119_9⟩] 0x341418110604409100343018110604408c0c230318110604408c0c46441811032301191032301191046440c8c032301191046440c8c046441411032301191200001191046444001c45441811031301151045441191023221151031301151045440c4c031301151045440c4c0454414110313011510232211510454408c8870304002026221411060440905050441405050441411017070d0c05044090c03222 (by decide +kernel)

def state119_11 : List Sig := [0x3333333333333333333300003333000033333333333333333333000033330000,input 4,input 6,0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0,input 0,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_11 : Impossible true (goalAt 119) 5 state119_11.toFinset :=
  node_ok cuts119 [] 0x34301811060440841c34141811060440d05045441811031301151031301151045440c4c031301151045440c4c045441411031301151070301411060440c88850440d0c050441411024220c88850441411032221191032301811046441151023221151046440c8c046441191032300c8c04644119103230119103230141104644 (by decide +kernel)

def state119_12 : List Sig := [0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 4,input 6,0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0,input 0,input 1,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_12 : Impossible true (goalAt 119) 6 state119_12.toFinset :=
  node_ok cuts119 [⟨state119_11,exclude119_11⟩] 0xd0c060441811023070d050604418110341409c1c60441811027071191060440c8c046440c8c046441191032300c8c046441191032301191050440c8c046448000046441191100071151060440c4c0454411510464408c8845440c4c045441151031300c4c045441151031301151050440c4c0454408c8845441151023220988834300d0c026221c0c043071411060440d05050440d0c05044141102622140505044400303222 (by decide +kernel)

def state119_13 : List Sig := [0xf0f0f0f0f0f000000000000000000000f0f0f0f0f0f0000,input 4,input 5,input 6,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_13 : Impossible true (goalAt 119) 5 state119_13.toFinset :=
  node_ok cuts119 [] 0x32301191046440c8c046441811032301191046441411032301191045441191023221151031301151045440c4c045441811031301151045441411031301151034141811060440910032221411050440c888504418110322214110323011910323011910313011510313011510703008c1c60440d0c06044090c050440d0c05044 (by decide +kernel)

def state119_14 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,input 5,0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0,input 6,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_14 : Impossible true (goalAt 119) 6 state119_14.toFinset :=
  node_ok cuts119 [⟨state119_6,exclude119_6⟩,⟨state119_13,exclude119_13⟩] 0xc8c046441191032300c8c046441191032301191032300c8c046441191032300c8c046441191032300c8c0464411510464408c8845440c4c045441151031300c4c045441151031301151031300c4c045441151031300c4c045441151031300c4c045441c0c034141405200000d05034300d05034304001060440c88843071405032220d0c026220d0c024300d05032220905050441405043071405043070d0c200010d0c1000b (by decide +kernel)

def state119_15 : List Sig := [0xfffffffffffffffffffffffff0f0f0f0fffffffffffffffffffffffff0f0f0f0,input 5,0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0,input 6,input 0,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_15 : Impossible true (goalAt 119) 6 state119_15.toFinset :=
  node_ok cuts119 [] 0x32221411050440c8883430141105044090c0504418110322214110130314110504404c0c46441411032301191032301191046440c8c032301191046440c8c046441811032301191012101191046440484045441411031301151045441191023221151031301151045440c4c031301151045440c4c045441811031301151011101151045440444070304001100040d05060441811024400d0c0604408c1c2303 (by decide +kernel)

def state119_16 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 5,input 6,0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0,input 0,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_16 : Impossible true (goalAt 119) 6 state119_16.toFinset :=
  node_ok cuts119 [] 0xd0c050441411024300c88850441411032221411060440c888504405c1c50441411017071191050440c8c046440c8c046441191032300c8c046441191032301191060440c8c046440585046441191016141151050440c4c0454411510464408c8845440c4c045441151031300c4c045441151031301151060440c4c045440545045441151015144001034300d0c100021c0c050140d0c06044181110004400306044091003414 (by decide +kernel)

def state119_17 : List Sig := [0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0,input 6,input 0,input 1,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_17 : Impossible true (goalAt 119) 7 state119_17.toFinset :=
  node_ok cuts119 [⟨state119_7,exclude119_7⟩,⟨state119_8,exclude119_8⟩,⟨state119_10,exclude119_10⟩,⟨state119_12,exclude119_12⟩,⟨state119_14,exclude119_14⟩,⟨state119_15,exclude119_15⟩,⟨state119_16,exclude119_16⟩] 0x4003200010d05034144001050141811060448001a00001811060444003050140d05024404002c343008c0c343040011000418110604480014343018110604440011000408c0c23074001034141411050444002060440c88860448001034140c88832224002060441411050444003050140c88832224002043071411050448000c50141411050444003043070c88832224002c34300c88834304002026221411050448000834301411050444002026220c88824304001027071191046444001c60440c8c060444002427070c8c032304001c60441191046444002032221191046444001c50440c8c050444003c32220c8c032304001c50441191046444003043070c8c032304001c50141191046444003843071191046444001c50140c8c032304002c26220c8c032304001c34301191046444003426221191046444001c34300c8c032304001027071151045444001460440c4c060444001827070c4c031304001460441151045444002017071151045444001450440c4c050444002817070c4c031304001450441151045444001d000d11510454440014464408c88464440035000a08c8823224001446441151045444003043070c4c031304001450141151045444002843071151045444001450140c4c031304002d000a0c4c0313040014343011510454440029000a1151045444001434300c4c03130400090002400087030 (by decide +kernel)

def state119_18 : List Sig := [0xffffffffffffffff0f0f0f0f0f0f0000ffffffffffffffff0f0f0f0f0f0f0000,input 6,input 4,input 5,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_18 : Impossible true (goalAt 119) 5 state119_18.toFinset :=
  node_ok cuts119 [] 0x46441811032301191046441411032301191032301191046440c8c024221191046440d0c045441191023221151045441811031301151045441411031301151031301151045440c4c015141151045440d0c07030181106044140c034301811060440d0505044181103222141107030141105044180c03430141105044098885014 (by decide +kernel)

def state119_19 : List Sig := [0xf0f0f0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f0000,input 4,input 5,input 0,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_19 : Impossible true (goalAt 119) 6 state119_19.toFinset :=
  node_ok cuts119 [⟨state119_13,exclude119_13⟩,⟨state119_18,exclude119_18⟩] 0x1888832300c8c070301191046441888846441191070300c8c0323009c1c46441191064440c8c0644409c1c32300c8c064441191046440c88846441191054440c8c054440c88832300c8c0544411910464410c1c31300c4c0703011510454410c1c45441151070300c4c0313040018454411510464408c88464440018232208c88464411510454409c1c45441151064440c4c0644409c1c31300c4c0644411510454405c1c45441151054440c4c0544405c1c31300c4c054441151045441c0c034141c0c054141911064441c0c064441911054140d05050301c0c032221c0c062221511054441c0c054441511062220c88860300d05054441511064440c88864440d05032220c88864441511054441c0c034300d0c054148000050141c0c200011c0c054140d0c034300c8c034300c8c046440988846440c8c026220c8c046440d0c046440c4c034300c4c045444001845440c4c100060c4c045440d0c045444002100021811064440d0c060444002034300d0c064444000864440c88826221411054440d0c050440c88834300d0c05444098885444 (by decide +kernel)

def state119_20 : List Sig := [0x5555555555555555555555555555000055555555555555555555555555550000,input 6,input 4,input 5,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_20 : Impossible true (goalAt 119) 5 state119_20.toFinset :=
  node_ok cuts119 [] 0x1911060401811060441511050401411050440d0c070301405034301090046441191042441191064440c8c046441191054440c8c046440c8c046441191032301c0c064441911050301511064440c88854441c0c054441511060301051045441151041401151023221191045441151031301911045441151031301511045440c4c04544115103130 (by decide +kernel)

def state119_21 : List Sig := [0x3333333333333333333333333333000033333333333333333333333333330000,input 6,input 4,input 5,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_21 : Impossible true (goalAt 119) 5 state119_21.toFinset :=
  node_ok cuts119 [] 0x1911060401811060441511050401411050440d0c070301405034301050045441151041441151064440c4c045441151054440c4c045440c4c045441151031301c0c064441911050301511064440c88854441c0c054441511060301091046441191042401151023221151046441191032301911046441191032301511046440c8c04644119103230 (by decide +kernel)

def state119_22 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0f0f0f0f0f0f0f0f0f0f0f0f0000,input 6,input 4,input 5,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_22 : Impossible true (goalAt 119) 5 state119_22.toFinset :=
  node_ok cuts119 [] 0x1191064440c8c046441191054440c8c046440c8c0464411910323011510464408c8845441151064440c4c045441151054440c4c045440c4c045441151031301c0c064441911050301511064440c88854441c0c054441511060301091046441090046441051045441050045441811060441810064441411050441410054440d0c050141c0c03430 (by decide +kernel)

def state119_23 : List Sig := [0xffffffffffffffffffffffffffff0000ffffffffffffffffffffffffffff0000,input 6,input 4,input 5,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_23 : Impossible true (goalAt 119) 6 state119_23.toFinset :=
  node_ok cuts119 [⟨state119_20,exclude119_20⟩,⟨state119_21,exclude119_21⟩,⟨state119_22,exclude119_22⟩] 0x64441810060441811054441410050441411034301c0c050140d0c200020d0c034304000842401191046441091046441911032301191046441511032301191032301191046440c8c200011191046444000041401151045441051045441191023221151045441911031301151045441511031301151031301151045440c4c20000115104544400047030191106444140c027071511064440c88854441c0c0544415110603005c1c4707 (by decide +kernel)

def state119_24 : List Sig := [0xffffffffffff00000000000000000000ffffffffffff0000,input 6,input 4,input 5,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_24 : Impossible true (goalAt 119) 6 state119_24.toFinset :=
  node_ok cuts119 [⟨state119_13,exclude119_13⟩] 0x644418100604418110544414100504414110343010c0c43070d0c042401191046441091046441911032301191046441511032301191032301191046440c8c041401151045441051045441191023221151045441911031301151045441511031301151031301151045440c4c034141911064440d05054441911032221511032221511054440c8883430800003430400083230119103230119103130115103130115103414191103414191103222151103222151107030 (by decide +kernel)

def state119_25 : List Sig := [0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 6,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 5,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_25 : Impossible true (goalAt 119) 6 state119_25.toFinset :=
  node_ok cuts119 [] 0xd05034300d0c100081511050401411050440d0c060301405034300988834300d0c024301090046441191042441191032300c8c046441191054440c8c046440c8c046441191032300c888464411911001010500454411510414411510464408c8845441151031300c4c045441151054440c4c045440c4c0454411510313008c884544115102322191106030150505030140c032220d0503222090506030151105444400303222151105444400306222 (by decide +kernel)

def state119_26 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 6,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_26 : Impossible true (goalAt 119) 6 state119_26.toFinset :=
  node_ok cuts119 [⟨state119_6,exclude119_6⟩] 0x988834300d0c024301911060401811060440d0c050308000034300d05034300d0c100081090046441191042441191032300c8c046441191064440c8c046440c8c0464411910323005850464411910161410500454411510414411510464408c8845441151031300c4c045441151064440c4c045440c4c04544115103130054504544115101514151105030148885030180c034140c88832220905050301911064440911034141911064444000c5414 (by decide +kernel)

def state119_27 : List Sig := [0xf0f0f0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f0000,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,input 5,input 0,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_27 : Impossible true (goalAt 119) 6 state119_27.toFinset :=
  node_ok cuts119 [] 0xc8c046441191032301191032300c8c046441191032300c8c046441191032300c8c046440c4c0454411510313011510464408c8845441151031300c4c045441151031300c4c045441151031300c4c045441c0c05414140c05030191107030188886030180c034140c888241415110703010c1c703010c1c34301405070300d0c032301191032301191031301151031301151100080d0c034300d05024300d0c03430098890002 (by decide +kernel)

def state119_28 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,input 5,input 0,input 1,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_28 : Impossible true (goalAt 119) 7 state119_28.toFinset :=
  node_ok cuts119 [⟨state119_14,exclude119_14⟩,⟨state119_19,exclude119_19⟩,⟨state119_23,exclude119_23⟩,⟨state119_24,exclude119_24⟩,⟨state119_25,exclude119_25⟩,⟨state119_26,exclude119_26⟩,⟨state119_27,exclude119_27⟩] 0x54140d0c034301c0c100081c0c054148000050141c0c034300d0c034144001034144002034300d0c034140d0c034304002100084002100030988826220c88834300d0c100080d0c034300c8882622090c100088001a00014000834300d0c100080d0c034304000900084000862220c8c032301c0c046441191062221191046441c0c032300c8c026221090042400d0c046441191026221191046440d0c042401091100101191046440d05032300c8c100100c8c032300d05046441191032221191046444004032300c8c032220c8c032304000c46441191100101191046444000032300c8c100100c8c032304000046441191047070c4c031301c0c045441151047071151045441c0c031300c4c100081050041400d0c045441151100061151045440d0c0414010511001011510454411910232211911000608c8823221191045441151100041151045440d05031300c4c100060c4c031300d05045441151100031151045440c88831300c4c100060c4c031300c88845441151100061151045444000431300c4c100060c4c031304000445441151070300d0507030150510004150507030800145030150503414140c100034000c64441c0c032221c0c062224000c62221c0c20004180c062220c88860300d05100040d05100030c88832224000d00030905100034001054441c0c1000c1c0c047078000c47071c0c200021c0c04707400304707 (by decide +kernel)

def state119_29 : List Sig := [0xbbbbbbbbbbbbbbbbbbbbaaaabbbbaaaabbbbbbbbbbbbbbbbbbbbaaaabbbbaaaa,input 0,input 4,input 6,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_29 : Impossible true (goalAt 119) 5 state119_29.toFinset :=
  node_ok cuts119 [] 0x7030191106444140c064441810060441811034301c0c050140d0c05444141005044141105444191103222151107030151105444180c0454419110313011510414011510454410d1031301151045440c4c045441511031301151023221191032301911046441091046441191042400c8c04644119103230119103230151104644 (by decide +kernel)

def state119_30 : List Sig := [0xfafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafa,0x1111111111111111111100001111000011111111111111111111000011110000,input 4,input 6,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_30 : Impossible true (goalAt 119) 4 state119_30.toFinset :=
  node_ok cuts119 [] 0x1c0c064441911050301511064440c88854441c0c054441511060301151032301851045440c8c045441151032301151032301451045441091045441151041401911060401811060440d0c07030140503430151105040141105044 (by decide +kernel)

def state119_31 : List Sig := [0x1111111111111111111100001111000011111111111111111111000011110000,input 0,input 4,input 6,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_31 : Impossible true (goalAt 119) 5 state119_31.toFinset :=
  node_ok cuts119 [⟨state119_30,exclude119_30⟩] 0x7030191106444140c064441810060441811034301c0c050140d0c05444141005044141105444191103222151107030151105444180c025071911023221911023220d0c200000d0c023221c0c045071c0c023221511015071511046440c8c064441191042441191046441090032301191046440c8c046440c8c05444119104544 (by decide +kernel)

def state119_32 : List Sig := [0xfafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafa,input 0,0x3333333333333333333300003333000033333333333333333333000033330000,input 4,input 6,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_32 : Impossible true (goalAt 119) 5 state119_32.toFinset :=
  node_ok cuts119 [⟨state119_30,exclude119_30⟩] 0x7030191106444140c05444191103222151107030151105444180c046440c8c064441191032301191046440c8c046440c8c054441191045448000045441191042441191046441090045441851021071151015141151045441c0c045441451015141151041401911060401811060440d0c07030140503430151105040141105044 (by decide +kernel)

def state119_33 : List Sig := [0x3333333333333333333300003333000033333333333333333333000033330000,input 4,input 6,input 0,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_33 : Impossible true (goalAt 119) 6 state119_33.toFinset :=
  node_ok cuts119 [⟨state119_11,exclude119_11⟩,⟨state119_1,exclude119_1⟩,⟨state119_29,exclude119_29⟩,⟨state119_31,exclude119_31⟩,⟨state119_32,exclude119_32⟩] 0x1c0c034141c0c054141911064441c0c064441911054140d05050301911200011911060400d0c060401911034301811060404003c60441505034300d0c070304003c70301505200001405070300d0c034301511024221511050400d0c050401511034301411050400908850440941c45441151064440c4c064440941c31300c4c064441151045444003c414010500343011510454480010454411510343010500414411c1c31300c4c0703011510454411c1c45441151070300c4c0313005c1c45441151054440c4c0544405c1c31300c4c054441151045440d05054441511064440c88864440d05032220c88864441511054441c0c032221c0c062221511054441c0c054441511062220c88860301911046441191025070c8c032301911032301911025071191046440d0c042401091024221191046440d0c046441191024221090042401151046441151023228000c23221151200021151023221191046441c0c032300c8c062221191046441c0c046441191062220c8c032301511046441191032220c8c03230151103230151103222119104644 (by decide +kernel)

def state119_34 : List Sig := [0x3333333333333333333300003333000033333333333333333333000033330000,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 4,input 6,input 0,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_34 : Impossible true (goalAt 119) 6 state119_34.toFinset :=
  node_ok cuts119 [] 0x1c0c064441911050300941c64441911025071911060401811060440d0c070301405034301511050401411050440908834300d0c024221151064440c4c045441050045441151041440c4c045441151031301151054440c4c0454408c8845441151023221888854441911034141511070301511060300c88846440c8c0644411910424411910464410900454408c8845441191032301191046440c8c046440c8c05444119110000 (by decide +kernel)

def state119_35 : List Sig := [0xf0f0f0f0fffffffff0f0f0f0fffff0f0f0f0f0f0fffffffff0f0f0f0fffff0f0,input 5,input 4,input 6,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_35 : Impossible true (goalAt 119) 5 state119_35.toFinset :=
  node_ok cuts119 [] 0xc8c046441191032301191050440c8c046441191064440c8c046440c8c0464411910323011510464408c8845440c4c045441151031301151050440c4c045441151064440c4c045440c4c045441151031301c0c050441411060301411064440c88850441c0c064441911024400d0c07030140503430141103430141102430191103430181106044 (by decide +kernel)

def state119_36 : List Sig := [0xffffffff00000000ffff000000000000ffffffff00000000ffff0000,input 5,input 4,input 6,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_36 : Impossible true (goalAt 119) 6 state119_36.toFinset :=
  node_ok cuts119 [⟨state119_35,exclude119_35⟩] 0x34301c0c050140d0c054441410050441411027070d0c0343008c1c42401191046441091032301191046440c8c046441511032301191046440c8c032301191041401151045441051045441191023221151031301151045440c4c045441511031301151045440c4c03130115107030151105444180c054440c88832221511070301505070301505100020d0c200000d0c046440c8c046440c8c045440c4c045440c4c054141c0c054141c0c054440c88854440c8886444 (by decide +kernel)

def state119_37 : List Sig := [0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 4,input 6,input 0,input 1,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_37 : Impossible true (goalAt 119) 7 state119_37.toFinset :=
  node_ok cuts119 [⟨state119_25,exclude119_25⟩,⟨state119_12,exclude119_12⟩,⟨state119_2,exclude119_2⟩,⟨state119_23,exclude119_23⟩,⟨state119_33,exclude119_33⟩,⟨state119_34,exclude119_34⟩,⟨state119_36,exclude119_36⟩] 0x70300d0507030150506444191107030191106444150503414140c2000609c1c270740010644419112000319110644440010270709c1c64448000864441810034301810064440d0c060441810100081811054140d0c034301c0c100081c0c054148000450141c0c034300d0c054440988854441410034301410054440d0c050441410026221411100080988826224000834300d0c100080d0c034304000826220988827071191046441911032301911027070c8c032301911046441191026221090042400d0c046441191026221191046440d0c042401091100100c8c032301c0c046441191100101191046441c0c032300c8c100031191046441511032301511100100c8c032301511046441191100108001600044000046441191100101191046444000100104000027071151045441911031301911027070c4c031301911045441151100081050041400d0c045441151100111151045440d0c0414010511001011510454411910232211911001108c8823221191045441151100110c4c031301c0c045441151100111151045441c0c031300c4c100031151045441511031301511100110c4c0313015110454411511001108c88232240004454411511001111510454440004232208c8900034000c62220d05054441511064444000c64440d05200000d05064441511054441c0c1000c1c0c100031511054444000d0003180c10003400303222 (by decide +kernel)

def state119_38 : List Sig := [0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,0xfafafffffafafffffafafafafafafafafafafffffafafffffafafafafafafafa,input 4,input 6,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_38 : Impossible true (goalAt 119) 4 state119_38.toFinset :=
  node_ok cuts119 [] 0x1c0c060441811050301511060440c88854441c0c054441511032221811034301811100060d0c070301405034301511034301411050441151060440c8c045440c8c045441151032301151051440c8c045440c4c04544115103230 (by decide +kernel)

def state119_39 : List Sig := [0xfafafffffafafffffafafafafafafafafafafffffafafffffafafafafafafafa,input 0,input 4,input 6,input 1,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_39 : Impossible true (goalAt 119) 5 state119_39.toFinset :=
  node_ok cuts119 [⟨state119_38,exclude119_38⟩] 0x7030181106044140c046441811032301191032301191046440c8c046441511032301191032301191046440c8c054441811032221511070301511054440c88845441811023071151045441191200001151015141151045441c0c045441451015141151031301811034301811100040d0c07030140503430151103430141105044 (by decide +kernel)

def state119_40 : List Sig := [0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 0,0xf0f0fffff0f0fffff0f0f0f0f0f0f0f0f0f0fffff0f0fffff0f0f0f0f0f0f0f0,input 4,input 6,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_40 : Impossible true (goalAt 119) 5 state119_40.toFinset :=
  node_ok cuts119 [⟨state119_38,exclude119_38⟩] 0x7030181106044140c054441811032221511070301511054440c88860440d0c060440841c34301c0c050140d0c054440d0c050441411025071811023221811023221c0c041071c0c023221511015071511023220d0c200000d0c045441191060440c8c046440c8c046441191032301191054440c8c046440c8c04644119103230 (by decide +kernel)

def state119_41 : List Sig := [0xf0f0fffff0f0fffff0f0f0f0f0f0f0f0f0f0fffff0f0fffff0f0f0f0f0f0f0f0,input 4,input 6,input 0,input 1,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_41 : Impossible true (goalAt 119) 6 state119_41.toFinset :=
  node_ok cuts119 [⟨state119_39,exclude119_39⟩,⟨state119_40,exclude119_40⟩] 0x1c0c034141c0c054141811060441c0c060441811054140d050503009c1c46441191060440c8c0604409c1c32300c8c0604411910464410c1c32300c8c0703011910464410c1c46441191070300c8c032300c88846441191054440c8c054440c88832300c8c054441191046440988832300c8c034301191046440988846441191034300c8c0323009c1c45441151060440c4c0604409c1c31300c4c0604411510454440038454411510464408c88464480004232208c88464411510454410c1c31300c4c0703011510454410c1c45441151070300c4c0313005c1c45441151054440c4c0544405c1c31300c4c054441151045444002c31300c4c034301151045448000045441151034300c4c031300d05054441511060440c88860440d05032220c88860441511054441c0c032221c0c043071511054441c0c054441511043070c88832221811100041811023030d0c034301811034301811023034001023071505034300d0c070304000870301505100021405070300d0c034301511026221511032220d0c03430151103430141103222098885044 (by decide +kernel)

def state119_42 : List Sig := [0xf0f0f0f00000f0f0f0f0f0f000000000f0f0f0f00000f0f0f0f0f0f00000000,input 5,input 4,input 6,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_42 : Impossible true (goalAt 119) 5 state119_42.toFinset :=
  node_ok cuts119 [] 0xc8c046441191032301191050440c8c046441191064440c8c0464411510464408c8845440c4c045441151031301151050440c4c045441151064440c4c045441c0c050441411060301411064440c88850441c0c064441911024441091046441090046441051045441050045440d0c050141c0c03430090c05044141005044181106044181006444 (by decide +kernel)

def state119_43 : List Sig := [0xffffffff0000ffffffffffff00000000ffffffff0000ffffffffffff00000000,input 5,input 4,input 6,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_43 : Impossible true (goalAt 119) 6 state119_43.toFinset :=
  node_ok cuts119 [⟨state119_42,exclude119_42⟩] 0x34301c0c050140d0c026220d0c03430090c064441810060441811200000d0c034304000842401191046441091032301191046440c8c046440c8c032301191046441911032301191016141191046440585041401151045441051045441191023221151031301151045440c4c045440c4c03130115104544191103130115101514115104544054507030188886030180c074441911032221911017070c88854441511070301911064440911034141c0c054141c0c05414 (by decide +kernel)

def state119_44 : List Sig := [0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000,input 4,input 6,input 0,input 1,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_44 : Impossible true (goalAt 119) 7 state119_44.toFinset :=
  node_ok cuts119 [⟨state119_4,exclude119_4⟩,⟨state119_41,exclude119_41⟩,⟨state119_43,exclude119_43⟩] 0x70300d0507030150506444191107030191106444150503414140c064448000064441810034301810064440d0c060441810100081811054140d0c034301c0c1000c1c0c054144003050141c0c034300d0c017070988826220c88834300d0c017070d0c034300c8882622090c027071191046441911032301911027070c8c032301911046441191026221090042400d0c046441191026221191046440d0c0424010911000c0c8c032301c0c046441191100101191046441c0c032300c8c032221191046440541432300c8c032220c8c032300541446441191027071151045441911031301911027070c4c031301911045441151100081050041400d0c045441151100121151045440d0c0414010511001011510454411910232211911001208c88232211910454411511000c0c4c031301c0c045441151100121151045441c0c031300c4c017071151045440c88831300c4c017070c4c031300c888454411510341405c1c34141911032221911034140c88832221911017071911100034000c72221c0c1000c1c0c100030c88832221911100041911034144003034141911200021911034144003034144003100024000834304003034304003100088000434304000834301191100001191032304003032301191100101191032304000032301151100011151031304003031301151100121151031304000431304000d000318889000c4000c5444 (by decide +kernel)

def state119_45 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f0f0f0f0f0f0f0f0f00000000,input 5,input 6,input 0,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_45 : Impossible true (goalAt 119) 6 state119_45.toFinset :=
  node_ok cuts119 [] 0x1c0c032221c0c062221511054441c0c054441511062220c88860300d05054441511064440c88864440d05032220c88864441511054440c88846441191054440c8c054440c88832300c8c054441191046441888832300c8c070301191046441888846441191070300c8c0323009c1c46441191064440c8c0644409c1c32300c8c0644411910464404c1c45441151054440c4c0544404c1c31300c4c0544411510454440018454411510464408c88464440018232208c88464411510454411c1c31300c4c0703011510454411c1c45441151070300c4c0313009c1c45441151064440c4c0644409c1c31300c4c064441151045441c0c034141c0c054141911064441c0c064441911054140d05050301410026221411054440d0c050441410034301410054440988854441090034301091046440988846441090026221090046440d0c046441050034301051045444001845441050100061050045440d0c045441c0c034300d0c054144001050141c0c100041c0c054140d0c034301810100021811064440d0c06044181003430181006444400086444 (by decide +kernel)

def state119_46 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f0f0f0f0f0f0f0f0f00000000,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 5,input 6,input 0,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_46 : Impossible true (goalAt 119) 6 state119_46.toFinset :=
  node_ok cuts119 [] 0x1c0c054441511060301511064440c888544404c1c54441511013071191054440c8c046440c8c046441191032301191064440c8c046440585046441191016141151054440c4c0454411510464408c8845440c4c045441151031301151064440c4c045440545045441151015141505070301911050300d05050441411050401511042441191042401191041441151041401151034304001070300d0c06044181106040191110002 (by decide +kernel)

def state119_47 : List Sig := [0xffff0000ffff0000ffff000000000000ffff0000ffff0000ffff00000000,input 4,input 5,input 6,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_47 : Impossible true (goalAt 119) 6 state119_47.toFinset :=
  node_ok cuts119 [] 0x34301c0c050140d0c064441810060441811026220d0c034300988842401191046441091032301191046440c8c046441911032301191046440c8c032301191041401151045441051045441191023221151031301151045440c4c045441911031301151045440c4c03130115107030191106444140c070301888870301888834141911034141911026220d0c026220d0c046440c8c046440c8c045440c4c045440c4c062221c0c062221c0c064440d05064440d0505444 (by decide +kernel)

def state119_48 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 5,input 6,input 0,input 1,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_48 : Impossible true (goalAt 119) 7 state119_48.toFinset :=
  node_ok cuts119 [⟨state119_7,exclude119_7⟩,⟨state119_16,exclude119_16⟩,⟨state119_23,exclude119_23⟩,⟨state119_26,exclude119_26⟩,⟨state119_45,exclude119_45⟩,⟨state119_46,exclude119_46⟩,⟨state119_47,exclude119_47⟩] 0x70300c8887030188885444151107030151105444188883222180c100041511054441911032221911200030c888322219110544415112000605c1c17074000c54441511200021511054444000c170705c1c54440988854441410034301410054440d0c050441410026221411100040d0c034301c0c100041c0c100048000600001c0c034300d0c064444001064441810034301810064440d0c060441810100041811100048001600044000834300d0c100040d0c034304000900044000832221191046441511032301511032220c8c032301511046441191026221090042400d0c046441191026221191046440d0c042401091062220c8c032301c0c046441191062221191046441c0c032300c8c100041191046441911032301911100090c8c032301911046441191100090585016144000046441191100091191046444000016140585017071151045441511031301511017070c4c031301511045441151100041050041400d0c045441151100061151045440d0c0414010511000611510454411910232211911000608c8823221191045441151100060c4c031301c0c045441151100061151045441c0c031300c4c100041151045441911031301911100060c4c031301911045441151100060545015144000445441151100061151045444000415140545100044001054141c0c1000c1c0c1000419110644440011000c140c1000c400303414 (by decide +kernel)

def state119_49 : List Sig := [0xf0f0f0f0fffffffff0f0f0f0f0f0f0f0f0f0f0f0fffffffff0f0f0f0f0f0f0f0,input 5,input 6,input 0,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_49 : Impossible true (goalAt 119) 6 state119_49.toFinset :=
  node_ok cuts119 [] 0x1c0c032221c0c062221411050441c0c050441411062220c88860300d05050441411064440c88864440d05032220c88864441411050440c88846441191050440c8c050440c88832300c8c050441191046441888832300c8c070301191046441888846441191070300c8c0323009c1c46441191064440c8c0644409c1c32300c8c064441191046440988832300c8c034301191046440988846441191034300c8c0323005c1c45441151050440c4c0504405c1c31300c4c0504411510454440018454411510464408c88464440018232208c88464411510454410c1c31300c4c0703011510454410c1c45441151070300c4c0313009c1c45441151064440c4c0644409c1c31300c4c064441151045444001831300c4c034301151045444001845441151034300c4c031301c0c034141c0c050141911064441c0c064441911050140d05024401411026221411032220d0c034301411034301411032220988824301405034300d0c070304000870301405100021405070300d0c034301911100021911023030d0c03430191103430181102303400086044 (by decide +kernel)

def state119_50 : List Sig := [0x3333000033333333333300003333000033330000333333333333000033330000,input 4,input 5,input 6,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_50 : Impossible true (goalAt 119) 5 state119_50.toFinset :=
  node_ok cuts119 [] 0xd0c070301405034300d05034300d0c021071511050401411050441050045441151041440c4c045441151031301151031300c4c045441151054440c4c045441c0c05414140c050301c0c054441511032221511074440c88854441091046441191042401151023221151046440c8c04644119103230119103230191104644119103230151104644 (by decide +kernel)

def state119_51 : List Sig := [0xffff0000ffffffffffff0000ffff0000ffff0000ffffffffffff0000ffff0000,input 4,input 5,input 6,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_51 : Impossible true (goalAt 119) 6 state119_51.toFinset :=
  node_ok cuts119 [⟨state119_50,exclude119_50⟩] 0x34301c0c050140d0c034140d0c0343008c1c54441410050441411026220d0c034300988842401191046441091032301191046440c8c046440c8c032301191046441511032301191200001191046444000041401151045441051045441191023221151031301151045440c4c045440c4c0313011510454415110313011510232211510454408c887030150505030140c070301511054441888854441d11034141511032221c0c062221c0c062220d0502707191106444 (by decide +kernel)

def state119_52 : List Sig := [0xffffffff000000000000000000000000ffffffff0000000000000000,input 5,input 6,input 0,input 1,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_52 : Impossible true (goalAt 119) 7 state119_52.toFinset :=
  node_ok cuts119 [⟨state119_8,exclude119_8⟩,⟨state119_49,exclude119_49⟩,⟨state119_51,exclude119_51⟩] 0x70300c8887030188885444151107030151105444188883222180c0341415110544409c1c32220c88834140c888322209c1c54441511054440988854441410034301410054440d0c0504414100262214111000c0d0c034301c0c1000c1c0c100044003200001c0c034300d0c0341440010341408c0c34300d0c034140d0c0343008c0d000408c1c32221191046441511032301511032220c8c032301511046441191026221090042400d0c046441191026221191046440d0c042401091062220c8c032301c0c046441191062221191046441c0c032300c8c027071191046440d05032300c8c027070c8c032300d05046441191017071151045441511031301511017070c4c031301511045441151100041050041400d0c045441151100061151045440d0c0414010511000611510454411910232211911000608c88232211910454411511000c0c4c031301c0c045441151100061151045441c0c031300c4c027071151045440d05031300c4c027070c4c031300d05045441151100044003074141c0c1000c1c0c1000c0d05034141511100031511032224003032221511200021511032224000c322240031000240008343040030343040031000480004343040008343011911000011910323040030323011911000e11910323040000323011511000111510313040030313011511000611510313040004313040031000c15051000c400106444 (by decide +kernel)

def state119_53 : List Sig := roots 119
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude119_53 : Impossible true (goalAt 119) 8 state119_53.toFinset :=
  node_ok cuts119 [⟨state119_5,exclude119_5⟩,⟨state119_17,exclude119_17⟩,⟨state119_28,exclude119_28⟩,⟨state119_37,exclude119_37⟩,⟨state119_44,exclude119_44⟩,⟨state119_48,exclude119_48⟩,⟨state119_52,exclude119_52⟩] 0x8001870300d05070304001054141911064448001470301911064444001054140d05050308001070300c88870304000c62221511054448000c70301511054444000c62220c88860304001034141511054444000c64440c88864448000834140c88832224000c64441511054444000854140d0c034304000870304000870304000854148000450144000870300d0c034304000864448000064444000860400d0c060404000864440d0c060444000860404000860444000854440988854444000850400d0c050404000854440d0c050444000850400988850444000062220c8c032304000070301191046444000062221191046444000070300c8c032304000027071191046444000064440c8c064444000027070c8c032304000064441191046444000032221191046444000054440c8c054444000032220c8c032304000054441191046444000026221090042404000034301191046444000026221191046444000034301090042444000447070c4c031304000470301151045444000447071151045444000470300c4c031304000427071151045444000464440c4c064444000427070c4c031304000464441151045444000417071151045444000454440c4c054444000417070c4c0313040004544411510454440009000210500414040008343011510454440009000111510454440008343010500414440001000011510454440000464408c88464440001000108c882322400004644115104544 (by decide +kernel)

theorem lower119 : Claim 119 9 :=
  fromSearch 1348 (by decide +kernel) exclude119_53


open PEqualNP.CircuitLowerBounds

def graph : Sig := goalAt 255
theorem graph_proper : proper graph := by unfold proper; decide +kernel

def edgeList : List Nat := [0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7]
def target (x : Fin 8 → Bool) : Bool :=
  decide (∃ i < edgeList.length / 2,
    (List.ofFn x).getD (edgeList.getD (2*i) 0) false = true ∧
    (List.ofFn x).getD (edgeList.getD (2*i+1) 0) false = true)

def smallCircuit : Circuit := ⟨[⟨.or, [0, 1]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [5, 8]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [0, 2]⟩, ⟨.or, [5, 7]⟩, ⟨.and, [11, 12]⟩, ⟨.and, [13, 14]⟩, ⟨.and, [8, 4]⟩, ⟨.or, [15, 16]⟩, ⟨.or, [18, 17]⟩], 19⟩

theorem witnessMonotone : ∀ g ∈ smallCircuit.gates,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [smallCircuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ⟨Or.inl rfl, by decide⟩ | exact ⟨Or.inr rfl, by decide⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem witnessCorrect : ∀ x : Fin 8 → Bool, smallCircuit.eval (List.ofFn x) = target x := by
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
    (lower : Impossible true graph 10 eightInputs.toFinset) (gates : List Gate) (o : Nat)
    (fit : ∀ g ∈ gates, (g.op=GateOp.and ∨ g.op=GateOp.or ∨ g.op=GateOp.not) ∧ g.inputs.length≤2)
    (correct : ∀ x : Fin 8 → Bool, (Circuit.mk gates o).eval (List.ofFn x)=target x) :
    ∃ (gs : List Gate) (out : Nat), (∀ g ∈ gs, (g.op=GateOp.and ∨ g.op=GateOp.or) ∧ g.inputs.length≤2) ∧
       gs.length≤gates.length ∧ ∀ x : Fin 8 → Bool, (Circuit.mk gs out).eval (List.ofFn x)=target x := by
  classical
  by_cases big : 12 ≤ gates.length
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

theorem lowerGraph : Impossible true graph 10 eightInputs.toFinset :=
  (ruleFor 255 lower119 none (by decide +kernel)).property 10 eightInputs
    (by decide +kernel) (by decide +kernel)

end PEqualNP.Outside.L_meta_31403_aux

open PEqualNP.Outside.L_meta_31403_aux in
theorem PEqualNP.Outside.L_meta_31403 : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true))  := by
  intro gates o fit _ correct
  exact replaceShort lowerGraph gates o fit correct

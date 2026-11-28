import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_31463_aux


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
  (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 2 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 3 &&& x 5) ||| (x 0 &&& x 6) ||| (x 1 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 3 &&& x 7) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)


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




def cuts193 : Cuts (goalAt 193) := []

def state193_0 : List Sig := roots 193
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude193_0 : Impossible true (goalAt 193) 3 state193_0.toFinset :=
  node_ok cuts193 [] 0x30100410130100810130200c08030100c08030200810110404410120404414010500c04020600818020404818020600c04010500414010404818020600c08010500c08010404414010500c080206008180 (by decide +kernel)

theorem lower193 : Claim 193 4 :=
  fromSearch 6 (by decide +kernel) exclude193_0

theorem lower225 : Claim 225 5 :=
  fromLift 5 32 5 lower193 (by decide +kernel)

def cuts200 : Cuts (goalAt 200) := []

def state200_0 : List Sig := roots 200
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude200_0 : Impossible true (goalAt 200) 3 state200_0.toFinset :=
  node_ok cuts200 [] 0x30100480830100880830200c08030100c08030200880812020480822020484012100c04022200888022020888022200c04012100484012020888022200c08012100c08012020484012100c080222008880 (by decide +kernel)

theorem lower200 : Claim 200 4 :=
  fromSearch 855662592 (by decide +kernel) exclude200_0

theorem lower232 : Claim 232 5 :=
  fromLift 5 32 858804224 lower200 (by decide +kernel)

def cuts137 : Cuts (goalAt 137) := []

def state137_0 : List Sig := roots 137
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude137_0 : Impossible true (goalAt 137) 3 state137_0.toFinset :=
  node_ok cuts137 [] 0x220200901220208101222008880220208880222008101024040901204040908024208808206008180204048180206008808024200908024048180206008880024208880024040908024208880206008180 (by decide +kernel)

theorem lower137 : Claim 137 4 :=
  fromSearch 3 (by decide +kernel) exclude137_0

def rule201_0 : {c : Cut // CutGood (goalAt 201) c} :=
  ruleFor 201 lower200 none (by decide +kernel)

def rule201_1 : {c : Cut // CutGood (goalAt 201) c} :=
  ruleFor 201 lower193 none (by decide +kernel)

def rule201_2 : {c : Cut // CutGood (goalAt 201) c} :=
  ruleFor 201 lower137 none (by decide +kernel)

def cuts201 : Cuts (goalAt 201) := [rule201_0,rule201_1,rule201_2]

def state201_0 : List Sig := roots 201
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude201_0 : Impossible true (goalAt 201) 5 state201_0.toFinset :=
  node_ok cuts201 [] 0x40008c04012020c04040008880830200c08040008c04030200c08040008880812020480840004880812100484040004c04022200888040004880822200888040004c04012100484040004480822200888040004c08012100c08040004480812100484040004c08022200888040000810110500414040000c04020600818040000810120600818040000c04010500414040000410120600818040000c08010500c08040000410110500414040000c080206008180400000901206008180400008880024208880400000901024200908400008880206008180 (by decide +kernel)

theorem lower201 : Claim 201 6 :=
  fromSearch 3 (by decide +kernel) exclude201_0

def cuts168 : Cuts (goalAt 168) := []

def state168_0 : List Sig := roots 168
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude168_0 : Impossible true (goalAt 168) 3 state168_0.toFinset :=
  node_ok cuts168 [] 0x28080280828080880828200a08028080a0802820088080a02028082202028200a080a02022200888022020888022200a0200a08028200a020888022200a0800a080a0800a02028200a080a080222008880 (by decide +kernel)

theorem lower168 : Claim 168 4 :=
  fromSearch 808472576 (by decide +kernel) exclude168_0

def cuts161 : Cuts (goalAt 161) := []

def state161_0 : List Sig := roots 161
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude161_0 : Impossible true (goalAt 161) 3 state161_0.toFinset :=
  node_ok cuts161 [] 0x28080210128080810128200a08028080a08028200810108404210120404212008480a02020600818020404818020600a02008480212008404818020600a08008480a08008404212008480a080206008180 (by decide +kernel)

theorem lower161 : Claim 161 4 :=
  fromSearch 5 (by decide +kernel) exclude161_0

def rule169_0 : {c : Cut // CutGood (goalAt 169) c} :=
  ruleFor 169 lower168 none (by decide +kernel)

def rule169_1 : {c : Cut // CutGood (goalAt 169) c} :=
  ruleFor 169 lower161 none (by decide +kernel)

def rule169_2 : {c : Cut // CutGood (goalAt 169) c} :=
  ruleFor 169 lower137 none (by decide +kernel)

def cuts169 : Cuts (goalAt 169) := [rule169_0,rule169_1,rule169_2]

def state169_0 : List Sig := roots 169
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude169_0 : Impossible true (goalAt 169) 5 state169_0.toFinset :=
  node_ok cuts169 [] 0x40008a0200a020a02040008880828200a08040008a02028200a0804000888080a02028084000488080a080282040004a02022200888040004880822200888040004a0200a080282040004280822200888040004a0800a080a0804000428080a080282040004a08022200888040000810108480212040000a02020600818040000810120600818040000a02008480212040000210120600818040000a08008480a08040000210108480212040000a080206008180400000901206008180400008880024208880400000901024200908400008880206008180 (by decide +kernel)

theorem lower169 : Claim 169 6 :=
  fromSearch 3 (by decide +kernel) exclude169_0

def cuts73 : Cuts (goalAt 73) := []

def state73_0 : List Sig := roots 73
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude73_0 : Impossible true (goalAt 73) 3 state73_0.toFinset :=
  node_ok cuts73 [] 0x120200901120204101121004840120204840121004101024040901104040908024204808105004140104044140105004808024200908024044140105004840024204840024040908024204840105004140 (by decide +kernel)

theorem lower73 : Claim 73 4 :=
  fromSearch 3 (by decide +kernel) exclude73_0

theorem lower105 : Claim 105 5 :=
  fromLift 5 32 3 lower73 (by decide +kernel)

def cuts41 : Cuts (goalAt 41) := []

def state41_0 : List Sig := roots 41
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude41_0 : Impossible true (goalAt 41) 3 state41_0.toFinset :=
  node_ok cuts41 [] 0xa02009010a02021010a08028200a02028200a0802101024040901084040908024202808084802120084042120084802808024200908024042120084802820024202820024040908024202820084802120 (by decide +kernel)

theorem lower41 : Claim 41 4 :=
  fromSearch 3 (by decide +kernel) exclude41_0

def rule233_0 : {c : Cut // CutGood (goalAt 233) c} :=
  ruleFor 233 lower225 none (by decide +kernel)

def rule233_1 : {c : Cut // CutGood (goalAt 233) c} :=
  ruleFor 233 lower232 none (by decide +kernel)

def rule233_2 : {c : Cut // CutGood (goalAt 233) c} :=
  ruleFor 233 lower201 none (by decide +kernel)

def rule233_3 : {c : Cut // CutGood (goalAt 233) c} :=
  ruleFor 233 lower169 none (by decide +kernel)

def rule233_4 : {c : Cut // CutGood (goalAt 233) c} :=
  ruleFor 233 lower105 none (by decide +kernel)

def rule233_5 : {c : Cut // CutGood (goalAt 233) c} :=
  ruleFor 233 lower73 none (by decide +kernel)

def rule233_6 : {c : Cut // CutGood (goalAt 233) c} :=
  ruleFor 233 lower137 none (by decide +kernel)

def rule233_7 : {c : Cut // CutGood (goalAt 233) c} :=
  ruleFor 233 lower168 none (by decide +kernel)

def rule233_8 : {c : Cut // CutGood (goalAt 233) c} :=
  ruleFor 233 lower161 none (by decide +kernel)

def rule233_9 : {c : Cut // CutGood (goalAt 233) c} :=
  ruleFor 233 lower193 none (by decide +kernel)

def rule233_10 : {c : Cut // CutGood (goalAt 233) c} :=
  ruleFor 233 lower41 none (by decide +kernel)

def cuts233 : Cuts (goalAt 233) := [rule233_0,rule233_1,rule233_2,rule233_3,rule233_4,rule233_5,rule233_6,rule233_7,rule233_8,rule233_9,rule233_10]

def state233_0 : List Sig := [0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00aa00aa,input 0,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_0 : Impossible true (goalAt 233) 3 state233_0.toFinset :=
  node_ok cuts233 [] 0x28180a08028200280818580818020600616020600a0801858081801a1808880222006860222006860282008880206000908206008880 (by decide +kernel)

def state233_1 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffaaaaaaaa,input 0,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 7,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_1 : Impossible true (goalAt 233) 4 state233_1.toFinset :=
  node_ok cuts233 [⟨state233_0,exclude233_0⟩] 0x68602220088801a180888028200686022202000022200888040020880828180a0802820021010a0208180222000901206006160206008180185808180282006160206000908 (by decide +kernel)

def state233_2 : List Sig := [0x5555555555555555555555555555555555555555555555555555555500000000,input 0,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 7,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_2 : Impossible true (goalAt 233) 4 state233_2.toFinset :=
  node_ok cuts233 [] 0x68602220088801a180888028200686022200a06028200a08008404090122200090822200090828180810128180090828200210128200888002404888002404a06022020a06020404a0800a020a080084048180 (by decide +kernel)

def state233_3 : List Sig := [0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffffffffffffaaaaaaaaffffffffffffffffffffffffaaaaaaaa,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_3 : Impossible true (goalAt 233) 3 state233_3.toFinset :=
  node_ok cuts233 [] 0x240488802220009012220081801a18081801a18088802220061600a0208180206010005185808180206010005220206160185810006 (by decide +kernel)

def state233_4 : List Sig := [0xffffffffffffffffffffffffaaaaaaaaffffffffffffffffffffffffaaaaaaaa,input 0,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000,input 7,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_4 : Impossible true (goalAt 233) 4 state233_4.toFinset :=
  node_ok cuts233 [⟨state233_3,exclude233_3⟩] 0x1a180888022200686002404888022200090122200a0801a18088802202061602220009012220061602058200001858021011858061604001c818028180a0802820100050a020a080282010005 (by decide +kernel)

def state233_5 : List Sig := [0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 0,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_5 : Impossible true (goalAt 233) 4 state233_5.toFinset :=
  node_ok cuts233 [⟨state233_3,exclude233_3⟩] 0x22200a0801a18088800240488802220009011a18088802220068600a020a06028200a0804001881802220009012060081802820200002060081012060081804001c616022020a060281810006 (by decide +kernel)

def state233_6 : List Sig := [0x5555555555555555555555555555555555555555555555555555555555005500,input 3,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_6 : Impossible true (goalAt 233) 3 state233_6.toFinset :=
  node_ok cuts233 [] 0x28180a0802820028081a180888022200686022200a0801a1808880185808180206006160206006160282008180206000908222008180 (by decide +kernel)

def state233_7 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00ff00,input 3,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 7,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_7 : Impossible true (goalAt 233) 4 state233_7.toFinset :=
  node_ok cuts233 [⟨state233_6,exclude233_6⟩] 0x61602060081801858081802820061602060081802220009082060200002060081804001c810128180a0802820028080840468602220088801a1808880282006860222000901 (by decide +kernel)

def state233_8 : List Sig := [0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00000000,input 3,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 7,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_8 : Impossible true (goalAt 233) 4 state233_8.toFinset :=
  node_ok cuts233 [] 0x616020600818018580818028200616020600818002420090820600a06028200a0800a020880828180880828180280828200280828200818002420818002420a06022020a06022020a0800a020a0800a0208880 (by decide +kernel)

def state233_9 : List Sig := [0xffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffffffffffffff00ff00ffffffffffffffffffffffffff00ff00,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_9 : Impossible true (goalAt 233) 3 state233_9.toFinset :=
  node_ok cuts233 [] 0x242081802060009082060088801858081801858081802060061600a02088802220100081a18088802220100050a02068601a1810008 (by decide +kernel)

def state233_10 : List Sig := [0xffffffffffffffffffffffffff00ff00ffffffffffffffffffffffffff00ff00,input 3,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000,input 7,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_10 : Impossible true (goalAt 233) 4 state233_10.toFinset :=
  node_ok cuts233 [⟨state233_9,exclude233_9⟩] 0x18580818020600616002420818020600090820600686002420818020600a0801858081802202068602218200001a18028081a180686040020888028180a0802820100050a020a080282010008 (by decide +kernel)

def state233_11 : List Sig := [0xffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00,input 3,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_11 : Impossible true (goalAt 233) 4 state233_11.toFinset :=
  node_ok cuts233 [⟨state233_9,exclude233_9⟩] 0x20600a0801858081800242081802060009082060088800242081801858081802060061600a020a06028200a08040018888028202000022200880822200888040020686022020a060281810008 (by decide +kernel)

def state233_12 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 7,input 0,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_12 : Impossible true (goalAt 233) 5 state233_12.toFinset :=
  node_ok cuts233 [⟨state233_1,exclude233_1⟩,⟨state233_2,exclude233_2⟩,⟨state233_4,exclude233_4⟩,⟨state233_5,exclude233_5⟩,⟨state233_7,exclude233_7⟩,⟨state233_8,exclude233_8⟩,⟨state233_10,exclude233_10⟩,⟨state233_11,exclude233_11⟩] 0x100051a18068602818088802220200072220088802818068601a18100062220088802820068602820200061a18068602820088802220200050240409014002088802220200042220088804002009010240409012060081802220009082220009010242009082220081802060100051858061602818081802060200032060081802818061601858100062060081802820061602820200021858061602820081802060200010242009084001c81802060200002060081804001c090802421000540018880828181000528181000628200a080400150005400150005400142808 (by decide +kernel)

def state233_13 : List Sig := [0xffffffffffffffffffffffffaaaaaaaa,input 7,input 0,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_13 : Impossible true (goalAt 233) 4 state233_13.toFinset :=
  node_ok cuts233 [] 0x88802820068602220068602220088801a180a80828200a08022020818022200090120600818028200616020600616020600818018580686022200686022200280828200210128200616020600616020600a060 (by decide +kernel)

def state233_14 : List Sig := [0xffffffffffffffffffffffffff00ff00ffffffffffffffffffffffffff00ff00,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,0xffffffffffffffffffffffffaaaaaaaaffffffffffffffffffffffffaaaaaaaa,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_14 : Impossible true (goalAt 233) 3 state233_14.toFinset :=
  node_ok cuts233 [] 0x28180880828180090828200a080024210008185808960220206160206008180185810008222008880185810006281808101281800901 (by decide +kernel)

def state233_15 : List Sig := [0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 3,0xffffffffffffffffffffffffaaaaaaaaffffffffffffffffffffffffaaaaaaaa,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_15 : Impossible true (goalAt 233) 4 state233_15.toFinset :=
  node_ok cuts233 [⟨state233_14,exclude233_14⟩] 0x28180880828180880828200a06022020a06002420880828180880828180090108406000002404090802404090840020888018580a060220206160084046160185810006206008180185810008 (by decide +kernel)

def state233_16 : List Sig := [0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 7,0xffffffffffffffffffffffffaaaaaaaaffffffffffffffffffffffffaaaaaaaa,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_16 : Impossible true (goalAt 233) 4 state233_16.toFinset :=
  node_ok cuts233 [⟨state233_3,exclude233_3⟩] 0x2220068601a18088802220081801a18081801a18088802220068601a180888022200616028200210120406000008404616008404616040018810120600818040014616020600818040014a060 (by decide +kernel)

def state233_17 : List Sig := [0xffffffffffffffffffffffffffaaffaa,input 3,input 0,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_17 : Impossible true (goalAt 233) 3 state233_17.toFinset :=
  node_ok cuts233 [] 0x20600a08018580818020600888002420818022200a0801a18088800a020a08028180a0801858081801858081801a18088801a1808880 (by decide +kernel)

def state233_18 : List Sig := [0xffffffffffffffffffffffffffaaffaaffffffffffffffffffffffffffaaffaa,input 3,input 0,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_18 : Impossible true (goalAt 233) 4 state233_18.toFinset :=
  node_ok cuts233 [⟨state233_17,exclude233_17⟩] 0xa06022020a0600a020a08018580a0602040461600242061601858009081858068600242061602060068602818088081a18028081a1806860024048880281820000281810005 (by decide +kernel)

def state233_19 : List Sig := [0xff00ff00ff00ff00ff00ff00aa00aa00ff00ff00ff00ff00ff00ff00aa00aa,input 3,input 0,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_19 : Impossible true (goalAt 233) 4 state233_19.toFinset :=
  node_ok cuts233 [] 0xa06022020a0600a02061602818081011858009081858061600242089802220009082220088082220088802818088802a200280822200a06022020a06022020a0802820021010a0208180206006160024206860 (by decide +kernel)

def state233_20 : List Sig := [0xffffffffffffffffffffffffff00ff00ffffffffffffffffffffffffff00ff00,input 3,0xffffffffffffffffffffffffaaaaaaaaffffffffffffffffffffffffaaaaaaaa,input 0,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_20 : Impossible true (goalAt 233) 4 state233_20.toFinset :=
  node_ok cuts233 [⟨state233_14,exclude233_14⟩] 0x18580a0602040461602060061601a18200001858021011858061604001ca06022020a0600a020a0802820028084002068602818088081a18028081a1806860400208880281808101281802101 (by decide +kernel)

def state233_21 : List Sig := [0xffffffffffffffffffffffffaaaaaaaaffffffffffffffffffffffffaaaaaaaa,input 0,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 3,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_21 : Impossible true (goalAt 233) 5 state233_21.toFinset :=
  node_ok cuts233 [⟨state233_1,exclude233_1⟩,⟨state233_4,exclude233_4⟩,⟨state233_13,exclude233_13⟩,⟨state233_15,exclude233_15⟩,⟨state233_16,exclude233_16⟩,⟨state233_18,exclude233_18⟩,⟨state233_19,exclude233_19⟩,⟨state233_20,exclude233_20⟩] 0x88081a18068602818088802220088082220088802818068601a18100062220088800840468601a18200071a18068600840488802220200062220088804002068601a18200051a180686040020888022200a06008404a06022021000622020a06080004a0602202021012202100064001ca08020404616018580a0604001ca06020406000420404a0601858061600240461601858088804001c8880024060003024048880185808880084050006084050007185806160400190006400190006400188180281810005281808808800088808281820000281808808400148808 (by decide +kernel)

def state233_22 : List Sig := [0xffaaffaa000000000000000000000000ffaaffaa,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 0,input 3,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_22 : Impossible true (goalAt 233) 4 state233_22.toFinset :=
  node_ok cuts233 [] 0x68602818088081a180a8802820068602820061602818081011858061601a180090818580a18028200616028200a06028200a0802202088082818088082818088802220009011a1808180206000908185802808 (by decide +kernel)

def state233_23 : List Sig := [0xffffffff000000000000000000000000ffaaffaa,input 7,input 0,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_23 : Impossible true (goalAt 233) 3 state233_23.toFinset :=
  node_ok cuts233 [] 0x1a180888022200686020600888002420818018580818020600616022200686022200a08020600616020600a0800a020a08028200a060 (by decide +kernel)

def state233_24 : List Sig := [0xffffffffffffffffffffffffffffffffffaaffaaffaaffaaffaaffaaffaaffaa,input 7,input 0,input 3,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_24 : Impossible true (goalAt 233) 4 state233_24.toFinset :=
  node_ok cuts233 [⟨state233_23,exclude233_23⟩] 0x280828200a0800a022000028200a08040018888028200280822200880822200888002404686020600a08008404818020600888002420818002420818020600090818580a060 (by decide +kernel)

def state233_25 : List Sig := [0xffaaffaaffaaffaaffaaffaaffaaffaa,input 7,input 0,input 3,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_25 : Impossible true (goalAt 233) 4 state233_25.toFinset :=
  node_ok cuts233 [] 0xa06028200a0800a020888028200280822200a86022200888028180818028200210120600818022200090820600a160206008180281802808282002808282006860222000901222006160206000908206008808 (by decide +kernel)

def state233_26 : List Sig := [0xffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_26 : Impossible true (goalAt 233) 3 state233_26.toFinset :=
  node_ok cuts233 [] 0xa020a08028200090808404a08028200090120600a0800a02081801858081802060100081a180818020601000528180a060024210008 (by decide +kernel)

def state233_27 : List Sig := [0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 7,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 3,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_27 : Impossible true (goalAt 233) 4 state233_27.toFinset :=
  node_ok cuts233 [⟨state233_26,exclude233_26⟩] 0xa020a0802820028080a020a0802820009080a020a0800a020a08022200090120406000002404090802404090840020818028200280820600810120600818040014616020600818040020a060 (by decide +kernel)

def state233_28 : List Sig := [0xffffffffffffffffffffffffff00ff00ffffffffffffffffffffffffff00ff00,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 0,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_28 : Impossible true (goalAt 233) 4 state233_28.toFinset :=
  node_ok cuts233 [⟨state233_14,exclude233_14⟩] 0x2420a06020404a0602060009080842200000242009010242009084001c68602818088081a18028081a180686040018888022200686040018a06022020a0600a020a080281808101281800901 (by decide +kernel)

def state233_29 : List Sig := [0xffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00,input 7,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 0,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_29 : Impossible true (goalAt 233) 4 state233_29.toFinset :=
  node_ok cuts233 [⟨state233_26,exclude233_26⟩] 0xa020a08028200280808404a08028200090102420a08008404a0802060009082042200000242009010242009084001c888028200280822200880822200888040014686022200888040014a060 (by decide +kernel)

def state233_30 : List Sig := [0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 0,input 3,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_30 : Impossible true (goalAt 233) 5 state233_30.toFinset :=
  node_ok cuts233 [⟨state233_18,exclude233_18⟩,⟨state233_15,exclude233_15⟩,⟨state233_22,exclude233_22⟩,⟨state233_24,exclude233_24⟩,⟨state233_25,exclude233_25⟩,⟨state233_27,exclude233_27⟩,⟨state233_28,exclude233_28⟩,⟨state233_29,exclude233_29⟩] 0xa0600a020a06022020a08028200a06028200a0802202028080a02088080240488082818100082818088088001c88082818009012818028080240428082820100082820028088001828082820009012820100084001c888020404090802420a0604001ca06020406000520404a06002420a06008404090802420a0804001ca08008406000108404a08002420a08002405000802405000702420090840021000840021000840020818022021000522020a06080010a06022022000322020a06040014a0600a02100060a020a08080008a0800a02200000a020a08040018a080 (by decide +kernel)

def state233_31 : List Sig := [0xffffffff000000000000000000000000aaaaaaaa,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 0,input 7,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_31 : Impossible true (goalAt 233) 4 state233_31.toFinset :=
  node_ok cuts233 [] 0x68602220088801a18088801a180686022200818022200090120600616020600818018580818018580616020600a0602a020a0600a02088801a18088801a180880828180810128180818018580818018580a080 (by decide +kernel)

def state233_32 : List Sig := [0xff00ff00ff00ff00ff00ff00ff00ff00aa00aa00aa00aa00aa00aa00aa00aa,input 3,input 0,input 7,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_32 : Impossible true (goalAt 233) 4 state233_32.toFinset :=
  node_ok cuts233 [] 0x280828200a0800a02081802820021012060009082060081800242081801a18009082060028082820068602820068602a18088081a180a0800a020a0800a020a060281808101220208180185808180024208880 (by decide +kernel)

def state233_33 : List Sig := [0xffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00,input 3,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 0,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_33 : Impossible true (goalAt 233) 4 state233_33.toFinset :=
  node_ok cuts233 [⟨state233_26,exclude233_26⟩] 0xa020a08028200280808404a08028200210120600a0800840481801858081802220200002060081012060081804001ca060281808808400208880282002808222008808222008880400206860 (by decide +kernel)

def state233_34 : List Sig := [0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 0,input 7,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_34 : Impossible true (goalAt 233) 5 state233_34.toFinset :=
  node_ok cuts233 [⟨state233_16,exclude233_16⟩,⟨state233_27,exclude233_27⟩,⟨state233_1,exclude233_1⟩,⟨state233_5,exclude233_5⟩,⟨state233_24,exclude233_24⟩,⟨state233_31,exclude233_31⟩,⟨state233_32,exclude233_32⟩,⟨state233_33,exclude233_33⟩] 0x28082220088802820068602820028081a18068602820088802220100051a18068602040488802220200072220088802040468601a18200061a18068604002088802220200042220088804002068601a18100050a020280820404a08028202000328200a0802040428080a02200050a020280840018a08028202000228200a0804001828080a02100054001ca0600240481802060088804001c888002406000102404888020600818008404818020600a0804001ca08008406000008404a080206008180204050005204050007206008180400150005400150005400146160 (by decide +kernel)

def state233_35 : List Sig := [0xffffffffffffffffffffffffff00ff00,input 7,input 3,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_35 : Impossible true (goalAt 233) 4 state233_35.toFinset :=
  node_ok cuts233 [] 0x818028200616020600818022200090820600616020600818018580280828200a0800a02088802820068602220068602220088801a180616020600616020600280828200280828200686022200686022200a060 (by decide +kernel)

def state233_36 : List Sig := [0xffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00,input 7,0xffffffffffffffffffffffffff00ff00ffffffffffffffffffffffffff00ff00,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_36 : Impossible true (goalAt 233) 4 state233_36.toFinset :=
  node_ok cuts233 [⟨state233_9,exclude233_9⟩] 0x2060061601858081802060088801858081801858081802060061601858081802060061602820028082202200000a02068600a020686040018880822200888040014686022200888040014a060 (by decide +kernel)

def state233_37 : List Sig := [0x5555555555555555555555555500550055555555555555555555555555005500,input 0,input 3,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_37 : Impossible true (goalAt 233) 4 state233_37.toFinset :=
  node_ok cuts233 [] 0xa06022020a0600a02068602818088081a18028081a180686002404810120600818028180818028600210120600818022600090120600a06020404a06020404a080282002808084048880222006860024046160 (by decide +kernel)

def state233_38 : List Sig := [0xffffffffffffffffffffffffff00ff00ffffffffffffffffffffffffff00ff00,input 3,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 0,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_38 : Impossible true (goalAt 233) 5 state233_38.toFinset :=
  node_ok cuts233 [⟨state233_7,exclude233_7⟩,⟨state233_10,exclude233_10⟩,⟨state233_18,exclude233_18⟩,⟨state233_28,exclude233_28⟩,⟨state233_20,exclude233_20⟩,⟨state233_35,exclude233_35⟩,⟨state233_36,exclude233_36⟩,⟨state233_37,exclude233_37⟩] 0x81011858061602818081802060081012060081802818061601858100062060081800a02061601858200041858061600a02081802060100082060081801a18009081a18200030242009081a18081802060200072060081804001c61601858200021858061604001c818020600a0600a020a06022021000622020a06080004a0602202028080a021000840020a0802202068601a180a06040020a06022022000622020a0601a18068600a02100060a02100081a1806860400210008400210008400188880281810005281808101800148101281820000281808101400148101 (by decide +kernel)

def state233_39 : List Sig := [0xffffffff000000000000000000000000ff00ff00,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 3,input 7,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_39 : Impossible true (goalAt 233) 4 state233_39.toFinset :=
  node_ok cuts233 [] 0x61602060081801858081802220009082060081801858061602060068602220088801a18088801a180686022200a06022020a0602202081801858081801858088082818088082818088801a18088801a180a080 (by decide +kernel)

def state233_40 : List Sig := [0x5555555555555555555555555555555555005500550055005500550055005500,input 0,input 3,input 7,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_40 : Impossible true (goalAt 233) 4 state233_40.toFinset :=
  node_ok cuts233 [] 0x280828200a0800a020888028200280822200880822200888002404210128200616028200616028580810118580616022200090122200a08008404a08008404a0602818088082040488801a1808880024048180 (by decide +kernel)

def state233_41 : List Sig := [0xffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00,input 3,input 7,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_41 : Impossible true (goalAt 233) 5 state233_41.toFinset :=
  node_ok cuts233 [⟨state233_36,exclude233_36⟩,⟨state233_7,exclude233_7⟩,⟨state233_11,exclude233_11⟩,⟨state233_24,exclude233_24⟩,⟨state233_29,exclude233_29⟩,⟨state233_33,exclude233_33⟩,⟨state233_39,exclude233_39⟩,⟨state233_40,exclude233_40⟩] 0x21012060081802820061602820021011858061602820081802060100051858061602202081802060200052060081802202061601858100082060081802220009082220200040242009082220081802060200071858061604001c81802060200032060081804001c61601858100050a020280822020a08028202000228200a0802202028080a022000608404210140018a08028202000128200a08040018210108405000840020a0600a020888022200a08040020a0800a02200000a020a080222008880220210005220210008222008880400210008400210008400146860 (by decide +kernel)

def state233_42 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 0,input 3,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_42 : Impossible true (goalAt 233) 6 state233_42.toFinset :=
  node_ok cuts233 [⟨state233_12,exclude233_12⟩,⟨state233_21,exclude233_21⟩,⟨state233_30,exclude233_30⟩,⟨state233_34,exclude233_34⟩,⟨state233_38,exclude233_38⟩,⟨state233_41,exclude233_41⟩] 0x4001488081a180686040020a06022200888080014880822200888040020a0601a180686040018280822200888040020a0801a180a0808001028081a180686040020a0802220088804001481011858061604001ca0602060081808000c810120600818040014a0601858061604002009012060081804001c88800242088808000809010242009084002088802060081804001821012060081804001ca08018580a08080004210118580616040018a08020600818040014a0600a020a06040018880828200a08080000a06028200a0804001488080a0202808 (by decide +kernel)

def state233_43 : List Sig := [0xffffffff00000000ffffffff00000000ffaaffaa00000000ffaaffaa,input 7,input 0,input 3,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_43 : Impossible true (goalAt 233) 4 state233_43.toFinset :=
  node_ok cuts233 [⟨state233_23,exclude233_23⟩] 0x38180c08030200a06022200c0801a18088801a180888022200686020600c08018580818020600888002420818018580818020600616028202000030200a08022200686022200a08020600616020600a08030180a08028200e060 (by decide +kernel)

def state233_44 : List Sig := [0xffffffffffffffff0000000000000000ffaaffaaffaaffaa,input 7,input 0,input 3,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_44 : Impossible true (goalAt 233) 4 state233_44.toFinset :=
  node_ok cuts233 [⟨state233_23,exclude233_23⟩] 0x38180a08028200c06022200a0801a18088801a180888022200686020600a08018580818020600888002420818018580818020600616028202000028200c08022200686022200c08020600616020600c08028180c08030200e060 (by decide +kernel)

def state233_45 : List Sig := [0xffffffffffffffffffffffffffffffffffaaffaaffaaffaaffaaffaaffaaffaa,input 7,input 0,input 3,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_45 : Impossible true (goalAt 233) 5 state233_45.toFinset :=
  node_ok cuts233 [⟨state233_24,exclude233_24⟩,⟨state233_43,exclude233_43⟩,⟨state233_44,exclude233_44⟩] 0x480830200c08012022000230200c0804000ca08030202000028200280828200a0800a022000128200a08040008888030200480822200888028200280822200880822200888002404686020600c08010404818020600a08008404818020600888002420818002420818020600090818580e060 (by decide +kernel)

def state233_46 : List Sig := [0xffaaffaaffaaffaaffaaffaaffaaffaa,input 7,input 0,input 3,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_46 : Impossible true (goalAt 233) 5 state233_46.toFinset :=
  node_ok cuts233 [⟨state233_25,exclude233_25⟩] 0xe06030200c08028180a08030202000028200e06028200a08030180888030200480822200888028200280822200e86022200888038180818030200410120600818028200210120600818022200090820600e160206008180381804808302004808302002808282002808282006860222000901222006160206000908206008808 (by decide +kernel)

def state233_47 : List Sig := [0xffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_47 : Impossible true (goalAt 233) 4 state233_47.toFinset :=
  node_ok cuts233 [⟨state233_26,exclude233_26⟩] 0x12020c08030200090810404c08030200090128200c08080000a0800a020a08028200090808404a08028200090120600c08012020818020600a0800a02081801858081802060100001a180818020601000438180e060024210000 (by decide +kernel)

def state233_48 : List Sig := [0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 7,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 3,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_48 : Impossible true (goalAt 233) 5 state233_48.toFinset :=
  node_ok cuts233 [⟨state233_27,exclude233_27⟩,⟨state233_47,exclude233_47⟩] 0x12020c08030200480812020c08030200090828200c08080000a0800a020a0802820028080a020a08028200090812020c08012020c0800a020a0800a020a08022200090120406000102404090802404090840000818030200480820600818028200280820600810120600818040010616020600818040000e060 (by decide +kernel)

def state233_49 : List Sig := [0xffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00,input 7,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 0,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_49 : Impossible true (goalAt 233) 5 state233_49.toFinset :=
  node_ok cuts233 [⟨state233_47,exclude233_47⟩,⟨state233_29,exclude233_29⟩] 0x12020c08030200480810404c08030200090128200c08080004a0800a020a08028200280808404a08028200090102420c08010404c08002420a08008404a08020600090820422000002420090102420090840004888030200480822200888028200280822200880822200888040010686022200888040010e060 (by decide +kernel)

def state233_50 : List Sig := [0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 0,input 3,input 5,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_50 : Impossible true (goalAt 233) 6 state233_50.toFinset :=
  node_ok cuts233 [⟨state233_30,exclude233_30⟩,⟨state233_45,exclude233_45⟩,⟨state233_46,exclude233_46⟩,⟨state233_48,exclude233_48⟩,⟨state233_49,exclude233_49⟩] 0xe06012020e06028080c08030200e06030200c08028080480828180e0600a020e06030100a08028200e06028200a08030100280830181000828200a08030201000830201000940022000030200a08028200880802404880838181000038180880880010880838180090138180480802404480830201000030200480840020480830200090130200280802404280828201000028200280840024280828200090128201000040004888020404090802420e06040004e06020406000320404e06002420e06010404090802420c08040004c08010405000810404c08002420c08008404090802420a08040004a08008405000908404a08002420a08002405000002405000102420090840001000040001000040000818022021000422020e06080008e06022022000122020e06040010e06012021000312020c08040020c08012021000812020c0804000cc0800a02100020a020a08040024a0800a02100090a020a08040008a080 (by decide +kernel)

def state233_51 : List Sig := [0xff00ff00ff00ff00ff00ff00ff00ff00aa00aa00aa00aa00aa00aa00aa00aa,input 3,input 0,input 7,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_51 : Impossible true (goalAt 233) 5 state233_51.toFinset :=
  node_ok cuts233 [⟨state233_32,exclude233_32⟩] 0x480830200c08012020a08030202000028200280828200a0800a02081803020041012060081802820021012060009082060081800242081801a18009082060028203020068603020048402820068602820068603a18088081a180c08012020c08012020a0800a020a0800a020e060381808101220208180185808180024208880 (by decide +kernel)

def state233_52 : List Sig := [0xffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00,input 3,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 0,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_52 : Impossible true (goalAt 233) 5 state233_52.toFinset :=
  node_ok cuts233 [⟨state233_47,exclude233_47⟩,⟨state233_33,exclude233_33⟩] 0x12020c08030200480810404c08030200410128200c08080004a0800a020a08028200280808404a08028200210120600c08010404818020600a08008404818018580818022202000020600810120600818040004e060381808808400008880302004808222008880282002808222008808222008880400006860 (by decide +kernel)

def state233_53 : List Sig := [0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 0,input 7,input 3,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_53 : Impossible true (goalAt 233) 6 state233_53.toFinset :=
  node_ok cuts233 [⟨state233_48,exclude233_48⟩,⟨state233_45,exclude233_45⟩,⟨state233_34,exclude233_34⟩,⟨state233_51,exclude233_51⟩,⟨state233_52,exclude233_52⟩] 0x1000412020480820404c08030201000a30200c08020404480812021000a1202048084000cc08030201000a30200c0804000c480812021000528200a0803020100053020100054002a000230200a0802820100040a020280820404a08028201000528200a0802040428080a02100050a020280840008a08028201000528200a0804000828080a02048082220088803020068603020048081a18068603020088802220028082220088802820068602820028081a18068602820088802220100041a18068602040488802220200042220088802040468601a18200031a18068604000088802220200012220088804000068601a181000440004e06010404818020600c08040004c08010405000a10404c08020600818008404818020600a08040004a08008405000508404a080206008180024048180206008880400048880024060000024048880206008180204050004204050001206008180400110004400110004400106160 (by decide +kernel)

def state233_54 : List Sig := [0x5555555555555555555555555555555555005500550055005500550055005500,input 0,input 3,input 7,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_54 : Impossible true (goalAt 233) 5 state233_54.toFinset :=
  node_ok cuts233 [⟨state233_40,exclude233_40⟩] 0x480830200c08012020a08030202000028200280828200a0800a020888030200480822200888028200280822200880822200888002404212030200616030200414028200616028200616038580810118580616022200090122200c08010404c08010404a08008404a08008404e0603818088082040488801a1808880024048180 (by decide +kernel)

def state233_55 : List Sig := [0xffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00,input 3,input 7,input 0,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_55 : Impossible true (goalAt 233) 6 state233_55.toFinset :=
  node_ok cuts233 [⟨state233_45,exclude233_45⟩,⟨state233_49,exclude233_49⟩,⟨state233_52,exclude233_52⟩,⟨state233_41,exclude233_41⟩,⟨state233_54,exclude233_54⟩] 0x1000412020480822020c08030201000830200c0802202048081202100081040441014000cc08030201000830200c0804000c410110405000828200a08030201000830201000540022000330200a0802820100040a020280822020a08028201000528200a0802202028080a021000508404210140008a08028201000528200a08040008210108404410120600818030200616030200410118580616030200818020600210120600818028200616028200210118580616028200818020601000418580616022020818020602000220600818022020616018581000020600818022200090822202000102420090822200818020602000418580616040004818020602000020600818040004616018581000040000e06012020888022200c08040000c08012021000812020c0802220088800a020888022200a08040000a0800a02100050a020a080222008880220210004220210000222008880400010000400010000400106860 (by decide +kernel)

def state233_56 : List Sig := roots 233
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_56 : Impossible true (goalAt 233) 7 state233_56.toFinset :=
  node_ok cuts233 [⟨state233_42,exclude233_42⟩,⟨state233_50,exclude233_50⟩,⟨state233_53,exclude233_53⟩,⟨state233_55,exclude233_55⟩] 0x4000ce06012020e0604000ca02030200c0804000ce06030200c0804000ca02012020a06040008e0600a020e06040008c04028200a08040008e06028200a08040008c0400a020c06040009000228200a08040008c08040008c0804000900024000e000040008c08028200a0804001088081a180686040000e0602220088808000c880822200888040000e0601a18068604000c48082220088804000cc0801a180c0804000c48081a18068604000cc08022200888040008280822200888040008a0801a180a0804000828081a180686040008a08022200888040010810118580616040004e06020600818080008810120600818040010e0601858061604000c41012060081804000cc08018580c0804000c41011858061604000cc08020600818040008210120600818040008a08018580a08040008210118580616040008a080206008180400000901206008180400048880024208880800040901024200908400008880206008180 (by decide +kernel)

theorem lower233 : Claim 233 8 :=
  fromSearch 3 (by decide +kernel) exclude233_56

theorem lower249 : Claim 249 9 :=
  fromLift 9 16 3 lower233 (by decide +kernel)

def cuts194 : Cuts (goalAt 194) := []

def state194_0 : List Sig := roots 194
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude194_0 : Impossible true (goalAt 194) 3 state194_0.toFinset :=
  node_ok cuts194 [] 0x30100420230100820230200c08030100c08030200820210808420220808424010900c04020a00828020808828020a00c04010900424010808828020a00c08010900c08010808424010900c08020a008280 (by decide +kernel)

theorem lower194 : Claim 194 4 :=
  fromSearch 285212768 (by decide +kernel) exclude194_0

theorem lower226 : Claim 226 5 :=
  fromLift 5 32 286261328 lower194 (by decide +kernel)

theorem lower210 : Claim 210 5 :=
  fromLift 5 16 285278272 lower194 (by decide +kernel)

def cuts162 : Cuts (goalAt 162) := []

def state162_0 : List Sig := roots 162
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude162_0 : Impossible true (goalAt 162) 3 state162_0.toFinset :=
  node_ok cuts162 [] 0x28080220228080820228200a08028080a08028200820208808220220808222008880a02020a00828020808828020a00a02008880222008808828020a00a08008880a08008808222008880a08020a008280 (by decide +kernel)

theorem lower162 : Claim 162 4 :=
  fromSearch 269484112 (by decide +kernel) exclude162_0

theorem lower178 : Claim 178 5 :=
  fromLift 5 16 269549632 lower162 (by decide +kernel)

def cuts82 : Cuts (goalAt 82) := []

def state82_0 : List Sig := roots 82
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude82_0 : Impossible true (goalAt 82) 3 state82_0.toFinset :=
  node_ok cuts82 [] 0x140401202140404202141005040140405040141004202048081202108081210048405010109004240108084240109005010048401210048084240109005040048405040048081210048405040109004240 (by decide +kernel)

theorem lower82 : Claim 82 4 :=
  fromSearch 16842816 (by decide +kernel) exclude82_0

theorem lower114 : Claim 114 5 :=
  fromLift 5 32 17891392 lower82 (by decide +kernel)

def rule242_0 : {c : Cut // CutGood (goalAt 242) c} :=
  ruleFor 242 lower226 none (by decide +kernel)

def rule242_1 : {c : Cut // CutGood (goalAt 242) c} :=
  ruleFor 242 lower210 none (by decide +kernel)

def rule242_2 : {c : Cut // CutGood (goalAt 242) c} :=
  ruleFor 242 lower178 none (by decide +kernel)

def rule242_3 : {c : Cut // CutGood (goalAt 242) c} :=
  ruleFor 242 lower114 none (by decide +kernel)

def cuts242 : Cuts (goalAt 242) := [rule242_0,rule242_1,rule242_2,rule242_3]

def state242_0 : List Sig := roots 242
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_0 : Impossible true (goalAt 242) 6 state242_0.toFinset :=
  node_ok cuts242 [] 0x40008e0601c0c0e06040008b03034240d09040008e06034240d09040008b0301c0c0a06040004e06008808e06040004c0402c240b09040004e0602c240b09040004c04008808c0604000470302c240b09040004d09040004d09040004703040008503040004d0902c240b09040000b0301c180706040000e06040000e06040000b0304000ca03040000e0601c180706040000d09004808d09040000c0801c180c08040000d0901c180c09040000c08004808c09040000b09014100b09040000a0801c180a08040000b0901c180a09040000a08014100a0904000c82021898062604000ce06024a4092904000c820224a4092904000ce06018980626040008420224a40929040008d09018980d09040008420218980626040008d09024a40929040004220224a40929040004b09018980b09040004220218980626040004b09024a40929040000120220a00828040000706024a40929040000120224a40929040000706020a008290 (by decide +kernel)

theorem lower242 : Claim 242 7 :=
  fromSearch 286326848 (by decide +kernel) exclude242_0

theorem lower216 : Claim 216 5 :=
  fromLift 5 16 856055808 lower200 (by decide +kernel)

def cuts240 : Cuts (goalAt 240) := []

def state240_0 : List Sig := roots 240
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude240_0 : Impossible true (goalAt 240) 3 state240_0.toFinset :=
  node_ok cuts240 [] 0x38180d09034240a06038180b0902c240c0602c240d090140c0b0901c180e060280c0706034240c08030240c0902c240a08028240a090 (by decide +kernel)

theorem lower240 : Claim 240 4 :=
  fromSearch 1417019392 (by decide +kernel) exclude240_0

def cuts120 : Cuts (goalAt 120) := []

def state120_0 : List Sig := roots 120
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude120_0 : Impossible true (goalAt 120) 3 state120_0.toFinset :=
  node_ok cuts120 [] 0x1c0c05818140c050301c0c070601c18048181410070601c18050600e0c068601a18038301210068601a18048601a18070600e0c06860 (by decide +kernel)

theorem lower120 : Claim 120 4 :=
  fromSearch 53891072 (by decide +kernel) exclude120_0

def rule248_0 : {c : Cut // CutGood (goalAt 248) c} :=
  ruleFor 248 lower232 none (by decide +kernel)

def rule248_1 : {c : Cut // CutGood (goalAt 248) c} :=
  ruleFor 248 lower216 none (by decide +kernel)

def rule248_2 : {c : Cut // CutGood (goalAt 248) c} :=
  ruleFor 248 lower240 none (by decide +kernel)

def rule248_3 : {c : Cut // CutGood (goalAt 248) c} :=
  ruleFor 248 lower168 none (by decide +kernel)

def rule248_4 : {c : Cut // CutGood (goalAt 248) c} :=
  ruleFor 248 lower120 none (by decide +kernel)

def rule248_5 : {c : Cut // CutGood (goalAt 248) c} :=
  ruleFor 248 lower200 none (by decide +kernel)

def cuts248 : Cuts (goalAt 248) := [rule248_0,rule248_1,rule248_2,rule248_3,rule248_4,rule248_5]

def state248_0 : List Sig := [0xffffffffffffffffffffffffffffffffffffff00ffffff00ffffff00ffffff00,input 7,input 3,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude248_0 : Impossible true (goalAt 248) 4 state248_0.toFinset :=
  node_ok cuts248 [] 0x1c0c0c0903024050801c180c09030241000328240c090140c0a090280c0a0902824028181c180a09028240506026240c09012060989026240a0900e0c098900e0c098902624038301a180e060 (by decide +kernel)

def state248_1 : List Sig := [0xffffff00ffffff00ffffff00ffffff00,input 7,input 3,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude248_1 : Impossible true (goalAt 248) 4 state248_1.toFinset :=
  node_ok cuts248 [] 0xe06030240c09028180a09030240503028240e06028240a09030180989030240481826240989028240383026240e86026240989038180703030240706030240504028240706028240686026240383026240a030 (by decide +kernel)

def state248_2 : List Sig := [0xffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00,input 3,input 5,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude248_2 : Impossible true (goalAt 248) 5 state248_2.toFinset :=
  node_ok cuts248 [⟨state248_0,exclude248_0⟩,⟨state248_1,exclude248_1⟩] 0xe0601c0c0e0602c0c0d09034240e06034240d0902c0c0703028180e0600a060e06030100b0902c240e0602c240b0903010028183018070302c240b0903424100053424070304000c503034240b0902c24088180e0c038303818098902624088182624098903818038303818048182624098903424100023224048184000c48183424098902624028182624098902c24038302a24028180e0c038302c24098902624100004000088802c0c070601c180e06080004e0602c0c20000280c0e0601c180706034241000334240c0801c180c08034240706030240c0804000cc0902c24050402c240a0801c180a0802c240706028240a08014100a090 (by decide +kernel)

def state248_3 : List Sig := [0xff00ff00ff00ff00ff00ff00ff00ff00ff000000ff000000ff000000ff0000,input 3,input 7,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude248_3 : Impossible true (goalAt 248) 4 state248_3.toFinset :=
  node_ok cuts248 [] 0x703030240c09014200a09030240503028240a03028240a0900a06028203024068603024048402824068602824068603a18088181a180c0901c180c09012060a0901c180a09014180706038180a0301c1809890 (by decide +kernel)

def state248_4 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 7,input 3,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude248_4 : Impossible true (goalAt 248) 5 state248_4.toFinset :=
  node_ok cuts248 [⟨state248_0,exclude248_0⟩,⟨state248_3,exclude248_3⟩] 0x100031c0c07030280c0c09030241000330240c090280c070301420070601202070604000cc09030240706030240c0904000c480812060703028240a0903024100053024070304000c503030240a09028240a0300e060a03022060a09028240a03028240a0902206038180e06070600a020706014100a09028240706028240a0901410028081418058182624098903024068603024058181a18068603024098902624038182624098902824068602824038181a18068602824098902624088181a1806860280c09890262408818262409890280c068601a18200011a18068601c18098902624200002624098901c18068601a181000040000e060 (by decide +kernel)

def state248_5 : List Sig := [0xffffffff00000000ffffffff00000000ff00ff0000000000ff00ff00,input 3,input 7,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude248_5 : Impossible true (goalAt 248) 4 state248_5.toFinset :=
  node_ok cuts248 [] 0x38180d09034240a06034240c08030240c0901c180e060280c0706026240d0901a18098902220098902624088901a18098902624068602c240503034240b09028240a0902c240a08030180b0902c240e06026240686026240b090 (by decide +kernel)

def state248_6 : List Sig := [0xffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00,input 3,input 7,input 4,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude248_6 : Impossible true (goalAt 248) 5 state248_6.toFinset :=
  node_ok cuts248 [⟨state248_0,exclude248_0⟩,⟨state248_5,exclude248_5⟩] 0x703034240d0901c0c0703034240d0901c0c0b0903424050302c24038182c240b0900e06200012c240b09040004d09030200c09030240b09028200a0902824070602202088181c18070604000200001c180e06026240d09016060989026240b0900e0609890222009890262408890260609890400086860 (by decide +kernel)

def state248_7 : List Sig := roots 248
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude248_7 : Impossible true (goalAt 248) 6 state248_7.toFinset :=
  node_ok cuts248 [⟨state248_2,exclude248_2⟩,⟨state248_4,exclude248_4⟩,⟨state248_6,exclude248_6⟩] 0x4000ce0601c0c0e0604000cb03034240d0904000ce06034240d0904000cb0301c0c0a06040004e0600e060e06040004c0402c240b09040004e0602c240b09040004c0400e060c0604000470302c240b09040004d09040004d0904000470304000c503040004d0902c240b09040000b0301c180706040000e06040000e06040000b03080004a03040000e0601c180706040000d0904000cd09040000c0801c180c08040000d0901c180c09040000c08040000c09040000b09014100b09040000a0801c180a08040000b0901c180a09040000a08014100a0904001098181a180686040008e06026240989080008981826240989040008e0601a18068604000c581826240989040008d0901a180d0904000c58181a180686040008d09026240989040004381826240989040004b0901a180b0904000438181a180686040004b090262409890400010000222008880400007060262409890400020000262409890400007060222008890 (by decide +kernel)

theorem lower248 : Claim 248 7 :=
  fromSearch 859197440 (by decide +kernel) exclude248_7

theorem lower202 : Claim 202 5 :=
  fromLift 5 2 285237344 lower200 (by decide +kernel)

theorem lower90 : Claim 90 5 :=
  fromLift 5 8 16867392 lower82 (by decide +kernel)

def rule218_0 : {c : Cut // CutGood (goalAt 218) c} :=
  ruleFor 218 lower210 none (by decide +kernel)

def rule218_1 : {c : Cut // CutGood (goalAt 218) c} :=
  ruleFor 218 lower216 none (by decide +kernel)

def rule218_2 : {c : Cut // CutGood (goalAt 218) c} :=
  ruleFor 218 lower202 none (by decide +kernel)

def rule218_3 : {c : Cut // CutGood (goalAt 218) c} :=
  ruleFor 218 lower90 none (by decide +kernel)

def cuts218 : Cuts (goalAt 218) := [rule218_0,rule218_1,rule218_2,rule218_3]

def state218_0 : List Sig := roots 218
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude218_0 : Impossible true (goalAt 218) 6 state218_0.toFinset :=
  node_ok cuts218 [] 0x4000cc04016060c0404000c981834240d0904000cc04034240d0904000c981816060509040008981814100504040008c04040008c0404000898184000c881840008c04014100504040008d09006828d09040008c08014100c08040008d09014100c09040008c08006828c09040000981812100484040000c04026240989040000981826240989040000c04012100484040000581826240989040000d09012100d09040000581812100484040000d090262409890400001a0a222008880400005040262409890400001a0a262409890400005040222008890400048a0a10900424040004c04024a409290400048a0a24a40929040004c040109004240400044a0a24a40929040004d09010900d090400044a0a10900424040004d09024a409290400081a0a20a00828040008504024a409290400081a0a24a40929040008504020a00829040001000024a409290400009890068609890400010001068601a1840000989024a409290 (by decide +kernel)

theorem lower218 : Claim 218 7 :=
  fromSearch 285302848 (by decide +kernel) exclude218_0

theorem lower170 : Claim 170 5 :=
  fromLift 5 2 269504592 lower168 (by decide +kernel)

def cuts154 : Cuts (goalAt 154) := []

def state154_0 : List Sig := roots 154
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude154_0 : Impossible true (goalAt 154) 3 state154_0.toFinset :=
  node_ok cuts154 [] 0x260608a0a22060881826060989026240820a22200989026240889006860929024a401a1820a00929024a40829024a409890068609290 (by decide +kernel)

theorem lower154 : Claim 154 4 :=
  fromSearch 268529728 (by decide +kernel) exclude154_0

def cuts58 : Cuts (goalAt 58) := []

def state58_0 : List Sig := roots 58
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude58_0 : Impossible true (goalAt 58) 3 state58_0.toFinset :=
  node_ok cuts58 [] 0xe0602a0a0a06028180e06038300e0c0220a0a08038300e0c028300686032300c8c01a180888032300c8c022300c8c03830068603230 (by decide +kernel)

theorem lower58 : Claim 58 4 :=
  fromSearch 1134656 (by decide +kernel) exclude58_0

def rule186_0 : {c : Cut // CutGood (goalAt 186) c} :=
  ruleFor 186 lower178 none (by decide +kernel)

def rule186_1 : {c : Cut // CutGood (goalAt 186) c} :=
  ruleFor 186 lower168 none (by decide +kernel)

def rule186_2 : {c : Cut // CutGood (goalAt 186) c} :=
  ruleFor 186 lower170 none (by decide +kernel)

def rule186_3 : {c : Cut // CutGood (goalAt 186) c} :=
  ruleFor 186 lower154 none (by decide +kernel)

def rule186_4 : {c : Cut // CutGood (goalAt 186) c} :=
  ruleFor 186 lower58 none (by decide +kernel)

def cuts186 : Cuts (goalAt 186) := [rule186_0,rule186_1,rule186_2,rule186_3,rule186_4]

def state186_0 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffff0000ffffffffffff0000,input 7,input 5,input 1,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude186_0 : Impossible true (goalAt 186) 4 state186_0.toFinset :=
  node_ok cuts186 [] 0x26240a0900e0c098900e0c0989026240383006828989026240120a24a40989006860929024a40a0900c8c092900c8c0929024a40323006828929024a410001280c0a0902824028180a8288a0a (by decide +kernel)

def state186_1 : List Sig := [0xffffffffffff0000ffffffffffff0000,input 7,input 5,input 1,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude186_1 : Impossible true (goalAt 186) 4 state186_1.toFinset :=
  node_ok cuts186 [] 0x98902824038302624038302624098900e0c09290262401a1824a40929028240323024a40323024a4092900c8c0281828240a0900a060383026240383026240323024a40323024a40281828240281828240a030 (by decide +kernel)

def state186_2 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 5,input 1,input 3,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude186_2 : Impossible true (goalAt 186) 5 state186_2.toFinset :=
  node_ok cuts186 [⟨state186_0,exclude186_0⟩,⟨state186_1,exclude186_1⟩] 0x98180e0c03830280c09890262409818262409890280c038300e0c028182624098902824038302824028180e0c03830282409890262401a0a222008880048089890262401a0a262409890048088880222408a0a0c8c03230280c0929024a408a0a24a409290280c032300c8c1000124a409290262401a18262410001068601a1826240929024a41000124a4092902824032302824100010c8c0323028240929024a401a0a20a00828040004929024a401a0a24a40929040004828020a40a0300a060a03026060a09028240a03028240a0902606028180a061000240008a080280c01a0a280c08a0a800048a0a280c20000280c08a0a068288818 (by decide +kernel)

def state186_3 : List Sig := [0xffffffff00000000ffffffff00000000ffff000000000000ffff0000,input 5,input 7,input 1,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude186_3 : Impossible true (goalAt 186) 4 state186_3.toFinset :=
  node_ok cuts186 [] 0x38302624098900e0c098900e0c03830262409290262401a1824a40323024a4092900c8c092900c8c0323024a40a03022060a0302206098900e0c098900e0c092900c8c092900c8c08818280c08818280c0a090 (by decide +kernel)

def state186_4 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 7,input 1,input 3,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude186_4 : Impossible true (goalAt 186) 5 state186_4.toFinset :=
  node_ok cuts186 [⟨state186_0,exclude186_0⟩,⟨state186_3,exclude186_3⟩] 0xa0300e060a03022060a09028240a03028240a0902206038180e06200010a8282a0a06828a09028242000028240a090068282a0a0a06038182624098902824038302824038180e0c038302824098902624088180e0c03830280c09890262408818262409890280c038300e0c01a0a0a0802820048089890262401a0a2624098900480828200a0c02a0a24a409290282403230282402a0a0c8c0323028240929024a41000124a409290262401a18262410001068601a1826240929024a4100010c8c03230280c0929024a41000124a409290280c032300c8c01a0a08880222040004929024a401a0a24a409290400042220088c1000240008a020 (by decide +kernel)

def state186_5 : List Sig := [0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000ff00ff00000000,input 5,input 7,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude186_5 : Impossible true (goalAt 186) 4 state186_5.toFinset :=
  node_ok cuts186 [] 0x2c0c0a020280c0a0302c240a08028240a09020a00929024a4082900c8c0929024a40323024a40b0900c8c092902c0c0b0902c240381822240989026240888024a401a1824a4098900e0c098902624038302624038302c2409890 (by decide +kernel)

def state186_6 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,input 7,input 1,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude186_6 : Impossible true (goalAt 186) 5 state186_6.toFinset :=
  node_ok cuts186 [⟨state186_0,exclude186_0⟩,⟨state186_5,exclude186_5⟩] 0xb03028080a030280c0b09028200a090282401a0a4000a00000682888802624098902224038302624098900e0c098902c240383026242000126240989040000828024a40929020a409290262401a1824a40323024a4092900c8c092902c240323024a401a1824a4092900686098182c0c0b0904000c3818 (by decide +kernel)

def state186_7 : List Sig := roots 186
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude186_7 : Impossible true (goalAt 186) 6 state186_7.toFinset :=
  node_ok cuts186 [⟨state186_2,exclude186_2⟩,⟨state186_4,exclude186_4⟩,⟨state186_6,exclude186_6⟩] 0x40010b0300e060b0304000c98182c240b09080008b0302c240b0904000c98180e060381840008b03006828b03040008a02040008a02040008b03080004a03040008a02006828a03040008b09006828b09040008a08040008a08040008b09080000a09040008a08006828a0904000098180e0c0383040000b03026240989040000981826240989040000b0300e0c0383040000381826240989040000b0900e0c0b0904000038180e0c0383040000b090262409890400001a0a222008880400001202262409890400001a0a262409890400001202222008890400048a0a0c8c0323040004b03024a409290400048a0a24a40929040004b0300c8c03230400042a0a24a40929040004b0900c8c0b090400042a0a0c8c0323040004b09024a409290400081a0a20a00828040009000124a409290400081a0a24a40929040009000220a00829040001000024a409290400009890068609890400010001068601a1840000989024a409290 (by decide +kernel)

theorem lower186 : Claim 186 7 :=
  fromSearch 269570112 (by decide +kernel) exclude186_7

theorem lower122 : Claim 122 6 :=
  fromLift 6 8 17911872 lower114 (by decide +kernel)

theorem lower234 : Claim 234 6 :=
  fromLift 6 2 286281808 lower232 (by decide +kernel)

def rule250_0 : {c : Cut // CutGood (goalAt 250) c} :=
  ruleFor 250 lower242 none (by decide +kernel)

def rule250_1 : {c : Cut // CutGood (goalAt 250) c} :=
  ruleFor 250 lower248 none (by decide +kernel)

def rule250_2 : {c : Cut // CutGood (goalAt 250) c} :=
  ruleFor 250 lower218 none (by decide +kernel)

def rule250_3 : {c : Cut // CutGood (goalAt 250) c} :=
  ruleFor 250 lower186 none (by decide +kernel)

def rule250_4 : {c : Cut // CutGood (goalAt 250) c} :=
  ruleFor 250 lower122 none (by decide +kernel)

def rule250_5 : {c : Cut // CutGood (goalAt 250) c} :=
  ruleFor 250 lower234 none (by decide +kernel)

def rule250_6 : {c : Cut // CutGood (goalAt 250) c} :=
  ruleFor 250 lower232 none (by decide +kernel)

def rule250_7 : {c : Cut // CutGood (goalAt 250) c} :=
  ruleFor 250 lower248 (some (1,input 4,input 7)) (by decide +kernel)

def rule250_8 : {c : Cut // CutGood (goalAt 250) c} :=
  ruleFor 250 lower226 none (by decide +kernel)

def rule250_9 : {c : Cut // CutGood (goalAt 250) c} :=
  ruleFor 250 lower114 none (by decide +kernel)

def rule250_10 : {c : Cut // CutGood (goalAt 250) c} :=
  ruleFor 250 lower90 none (by decide +kernel)

def rule250_11 : {c : Cut // CutGood (goalAt 250) c} :=
  ruleFor 250 lower170 none (by decide +kernel)

def rule250_12 : {c : Cut // CutGood (goalAt 250) c} :=
  ruleFor 250 lower168 none (by decide +kernel)

def rule250_13 : {c : Cut // CutGood (goalAt 250) c} :=
  ruleFor 250 lower186 (some (1,input 4,input 7)) (by decide +kernel)

def cuts250 : Cuts (goalAt 250) := [rule250_0,rule250_1,rule250_2,rule250_3,rule250_4,rule250_5,rule250_6,rule250_7,rule250_8,rule250_9,rule250_10,rule250_11,rule250_12,rule250_13]

def state250_0 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 7,input 1,input 3,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_0 : Impossible true (goalAt 250) 7 state250_0.toFinset :=
  node_ok cuts250 [] 0x4001100041c0c0703040010a03030240c09040011000d30240c09040010a0301c0c050804003470601282870604002c1a0a30240c09040034706030240c0904002c1a0a12828481840028703028240a09040028c09040028c09040028703040034503040028c09028240a09040010a0300e060a03040010881828240a09040010a03028240a0904001088180e06038184002870600a828706040028504028240a09040028706028240a0904002850400a828506040024581826240989040020c0901a180c0904002458181a180686040020c09026240989040024381826240989040020a0901a180a0904002438181a180686040020a0902624098904001088181a180686040010a03026240989040010881826240989040010a0301a1806860400241a0a1a1806860400207060262409890400241a0a2624098904002070601a18068604002c4a0a24a40929040018c09018980c090400304a0a1898062604002cc09024a409290400282a0a24a40929040028a09018980a090400282a0a18980626040028a09024a40929040021000924a409290400249890068609890400250007068601a1840020989024a40929040011000418980626040010a03024a40929040011000724a40929040010a0301898062604001c1a0a18980626040018706024a4092904001c1a0a24a40929040018706018980626040011000440014e060 (by decide +kernel)

def state250_1 : List Sig := [0xffff0000ffff0000ffff0000ffff0000,input 7,input 1,input 3,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_1 : Impossible true (goalAt 250) 7 state250_1.toFinset :=
  node_ok cuts250 [] 0x40010e0601c0c0e06040010a02030240c09040010e06030240c09040010a0201c0c0a06040028703028240a09040028c09040028c0904002870304002c503040028c09028240a09040010e0600e060e06040010c04028240a09040010e06028240a09040010c0400e060c06040020581826240989040020c0901a180c0904002058181a180686040020c09026240989040020381826240989040020a0901a180a0904002038181a180686040020a090262409890400108a0a1a180686040010e060262409890400108a0a26240989040010e0601a18068604002c4a0a24a4092904002cc09018980c0904002c4a0a1898062604002cc09024a409290400282a0a24a40929040028a09018980a090400282a0a18980626040028a09024a40929040021000824a409290400209890068609890400210006068601a1840020989024a409290400108a0a18980626040010e06024a409290400108a0a24a40929040010e06018980626040014703006828703040014c0901c180c0904001470301c180706040014c09006828c09040014381814100504040014a0901c180a0904001438181c180706040014a09014100a0904001438301c18070604001498900682898904001438300682838304001498901c18098904001432301c18070604001492900682892904001432300682832304001492901c180929040011000540010a030 (by decide +kernel)

def state250_2 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 4,input 7,input 1,input 3,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_2 : Impossible true (goalAt 250) 7 state250_2.toFinset :=
  node_ok cuts250 [] 0x100041c0c070302c0c0d09034241000b34240d0902c0c0703014241000b128284a0a4000cd09034241000b34240d0904000c4a0a1282870302c240b09034241000a3424070304002c503034240b0902c240b0300e060b03026060b0902c240b0302c240b0902606038180e061000a0a8282a0a40008b0902c241000a2c240b090400082a0a0a82858182624098903424068603424058181a18068603424098902624038182624098902c24068602c24038181a18068602c24098902624098181a18068602c0c098902624098182624098902c0c068601a18100052220088804002098902624100082624098904001488802224100081a18068604000098902624100082624098904000068601a1804a0a24a409290342406260342404a0a18980626034240929024a402a0a24a4092902c24062602c2402a0a1898062602c240929024a41000824a409290262401a18262410006068601a1826240929024a4100041898062602c0c0929024a41000624a4092902c0c0626018981000520a00828040018929024a41000624a40929040014828020a41000618980626040004929024a41000624a40929040004626018981000440014e06034241000b34240c08040014c08034241000b30240c08040014c0902c241000a2c240a08040014a0802c241000a28240a08040014a0902c0c100042c0c10005400110005400110004280c10004400107060 (by decide +kernel)

def state250_3 : List Sig := roots 250
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude250_3 : Impossible true (goalAt 250) 8 state250_3.toFinset :=
  node_ok cuts250 [⟨state250_0,exclude250_0⟩,⟨state250_1,exclude250_1⟩,⟨state250_2,exclude250_2⟩] 0x4000ce0601c0c0e0604000cb03034240d0904000ce06034240d0904000cb0301c0c0a06040008e0600e060e06040008c0402c240b09040008e0602c240b09040008c0400e060c0604000c70302c240b0904000cd0904000cd0904000c70304000c50304000cd0902c240b09040010b0301c180706040014e06080004e06080008b03080000a03040010e0601c18070604000cd09006828d0904000cc0801c180c0804000cd0901c180c0904000cc08006828c09040008b09014100b09040008a0801c180a08040008b0901c180a09040008a08014100a0904000098181a180686040000e06026240989040000981826240989040000e0601a180686040000581826240989040000d0901a180d0904000058181a180686040000d09026240989040000381826240989040000b0901a180b0904000038181a180686040000b090262409890400001a0a222008880400007060262409890400001a0a262409890400007060222008890400048a0a18980626040004e06024a409290400048a0a24a40929040004e060189806260400044a0a24a40929040004d09018980d090400044a0a18980626040004d09024a409290400042a0a24a40929040004b09018980b090400042a0a18980626040004b09024a409290400041a0a20a00828040004706024a409290400041a0a24a40929040004706020a00829040001000024a409290400009890068609890400010001068601a1840000989024a409290 (by decide +kernel)

theorem lower250 : Claim 250 9 :=
  fromSearch 286347328 (by decide +kernel) exclude250_3

def cuts81 : Cuts (goalAt 81) := []

def state81_0 : List Sig := roots 81
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude81_0 : Impossible true (goalAt 81) 3 state81_0.toFinset :=
  node_ok cuts81 [] 0x140401101140404101141005040140405040141004101044041101104041110044405010105004140104044140105005010044401110044044140105005040044405040044041110044405040105004140 (by decide +kernel)

theorem lower81 : Claim 81 4 :=
  fromSearch 4 (by decide +kernel) exclude81_0

theorem lower113 : Claim 113 5 :=
  fromLift 5 32 4 lower81 (by decide +kernel)

theorem lower89 : Claim 89 5 :=
  fromLift 5 8 3 lower81 (by decide +kernel)

theorem lower57 : Claim 57 5 :=
  fromLift 5 16 3 lower41 (by decide +kernel)

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

theorem lower115 : Claim 115 6 :=
  fromLift 6 1 68 lower114 (by decide +kernel)

theorem lower107 : Claim 107 6 :=
  fromLift 6 2 83 lower105 (by decide +kernel)

theorem lower83 : Claim 83 5 :=
  fromLift 5 1 68 lower82 (by decide +kernel)

theorem lower75 : Claim 75 5 :=
  fromLift 5 2 99 lower73 (by decide +kernel)

def rule91_0 : {c : Cut // CutGood (goalAt 91) c} :=
  ruleFor 91 lower89 none (by decide +kernel)

def rule91_1 : {c : Cut // CutGood (goalAt 91) c} :=
  ruleFor 91 lower90 none (by decide +kernel)

def rule91_2 : {c : Cut // CutGood (goalAt 91) c} :=
  ruleFor 91 lower83 none (by decide +kernel)

def rule91_3 : {c : Cut // CutGood (goalAt 91) c} :=
  ruleFor 91 lower75 none (by decide +kernel)

def cuts91 : Cuts (goalAt 91) := [rule91_0,rule91_1,rule91_2,rule91_3]

def state91_0 : List Sig := roots 91
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude91_0 : Impossible true (goalAt 91) 6 state91_0.toFinset :=
  node_ok cuts91 [] 0x4000c58180682858184000c4a0a1410050404000c58181410050404000c4a0a06828481840008581802c0c581840008501012100484040008581812100484040008501002c0c5018400081a0a121004840400085040400085040400081a0a4000c120a400085040121004840400004a0a068601a18400005818109004240400004a0a109004240400005818068601a18400001a0a109004240400005040068605040400001a0a068601a18400005040109004240400000b03109004240400004840068604840400000b03068601a18400004840109004240400044303064601918400045818105004140400044303105004140400045818064601918400041303105004140400045040064605040400041303064601918400045040105004140400080b03105004140400084840064604840400080b0306460191840008484010500414040001000010500414040000424002c28424040001000102c280b0a400004240105004140 (by decide +kernel)

theorem lower91 : Claim 91 7 :=
  fromSearch 67 (by decide +kernel) exclude91_0

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

def rule123_0 : {c : Cut // CutGood (goalAt 123) c} :=
  ruleFor 123 lower121 none (by decide +kernel)

def rule123_1 : {c : Cut // CutGood (goalAt 123) c} :=
  ruleFor 123 lower115 none (by decide +kernel)

def rule123_2 : {c : Cut // CutGood (goalAt 123) c} :=
  ruleFor 123 lower114 none (by decide +kernel)

def rule123_3 : {c : Cut // CutGood (goalAt 123) c} :=
  ruleFor 123 lower122 none (by decide +kernel)

def rule123_4 : {c : Cut // CutGood (goalAt 123) c} :=
  ruleFor 123 lower107 none (by decide +kernel)

def rule123_5 : {c : Cut // CutGood (goalAt 123) c} :=
  ruleFor 123 lower91 none (by decide +kernel)

def rule123_6 : {c : Cut // CutGood (goalAt 123) c} :=
  ruleFor 123 lower59 none (by decide +kernel)

def rule123_7 : {c : Cut // CutGood (goalAt 123) c} :=
  ruleFor 123 lower43 none (by decide +kernel)

def rule123_8 : {c : Cut // CutGood (goalAt 123) c} :=
  ruleFor 123 lower113 none (by decide +kernel)

def rule123_9 : {c : Cut // CutGood (goalAt 123) c} :=
  ruleFor 123 lower105 none (by decide +kernel)

def rule123_10 : {c : Cut // CutGood (goalAt 123) c} :=
  ruleFor 123 lower120 none (by decide +kernel)

def rule123_11 : {c : Cut // CutGood (goalAt 123) c} :=
  ruleFor 123 lower89 none (by decide +kernel)

def rule123_12 : {c : Cut // CutGood (goalAt 123) c} :=
  ruleFor 123 lower90 none (by decide +kernel)

def rule123_13 : {c : Cut // CutGood (goalAt 123) c} :=
  ruleFor 123 lower57 none (by decide +kernel)

def rule123_14 : {c : Cut // CutGood (goalAt 123) c} :=
  ruleFor 123 lower41 none (by decide +kernel)

def rule123_15 : {c : Cut // CutGood (goalAt 123) c} :=
  ruleFor 123 lower58 none (by decide +kernel)

def rule123_16 : {c : Cut // CutGood (goalAt 123) c} :=
  ruleFor 123 lower81 none (by decide +kernel)

def rule123_17 : {c : Cut // CutGood (goalAt 123) c} :=
  ruleFor 123 lower82 none (by decide +kernel)

def rule123_18 : {c : Cut // CutGood (goalAt 123) c} :=
  ruleFor 123 lower27 none (by decide +kernel)

def rule123_19 : {c : Cut // CutGood (goalAt 123) c} :=
  ruleFor 123 lower83 none (by decide +kernel)

def rule123_20 : {c : Cut // CutGood (goalAt 123) c} :=
  ruleFor 123 lower75 none (by decide +kernel)

def cuts123 : Cuts (goalAt 123) := [rule123_0,rule123_1,rule123_2,rule123_3,rule123_4,rule123_5,rule123_6,rule123_7,rule123_8,rule123_9,rule123_10,rule123_11,rule123_12,rule123_13,rule123_14,rule123_15,rule123_16,rule123_17,rule123_18,rule123_19,rule123_20]

def state123_0 : List Sig := [0xffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaa,input 4,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 3,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude123_0 : Impossible true (goalAt 123) 6 state123_0.toFinset :=
  node_ok cuts123 [] 0x70300e060703016061000c160607030400385030160603818140c058180e0c038301c0c068601a18058181a18068601c0c038300e0c038181210048400840c68601a18038181a18068600840c48401218100091a18068600440c38300e0c100020e0c038300440c68601a1800b0a1a18068604002038300e0c00b0a0e0c038304002068601a1804a0a0c4c031301c0c06260189804a0a1898062601c0c031300c4c02a0a1090042400e0606260189802a0a1898062600e06042401098009031898062601a18019181a18009030646019181a18062601898011031898062604002831300c4c011030c4c03130400246260189800b0a189806160400003130185800b0a0c4c031304000062601898070300440c70301282900091282870304003870301282811031282838180440c38180a829000c0a82838184003038180a82811030a82900034000c70601c0c00b0a1c0c04a0a40038490a1c0c1000e1c0c04a0a02c280b0a0e0600b0a0e0602a0a40030290a0e061000c0e0602a0a02c280b0a (by decide +kernel)

def state123_1 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude123_1 : Impossible true (goalAt 123) 5 state123_1.toFinset :=
  node_ok cuts123 [] 0x140c01a0a140c00b0a1c1807060140c070601c1800b0a068280b0a0e0601a0a0e0602a0a1c18070600e06070601c1802a0a0682828180682868601a18070600e0c070600682838300e0c070601a180686002c2838300e0c050301a180686002c2868601a18050300e0c038300e06009030e06021031a18068600e06068601a18021030240c220a0682861601858070600c8c070600682832300c8c070601858061600240c61601858068600686068600240c1a1806860686018580616002c2832300c4c0503018580616002c2861601858050300c8c032300a8281a180686038181858061600a8286160185803818068601a180840c0b0a160603818140c050300840c5030140c0381802c283818 (by decide +kernel)

def state123_2 : List Sig := [0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa,input 6,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 3,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude123_2 : Impossible true (goalAt 123) 6 state123_2.toFinset :=
  node_ok cuts123 [⟨state123_1,exclude123_1⟩] 0x1000c0e06038181040d000c1040d000c4003600001040c38180e061000c0e060381802c28210302c29000c0840c210302c2838180e06038181410050400a82870601c18038181c18070600a828504014181000d068281a0a1040c70601c181000e1c18070601040c1a0a06829000f06828190a02c2870601c181000e1c180706002c281a0a02c2838181210048400840c68601a18038181a18068600840c4840121801a0a1a18068601c18038301c1801a0a0e0c038301c18068601a181000d0e0c038301040c68601a18100021a18068601040c38300e0c00b0a0e0c038304002068601a1800b0a1a18068604002038300e0c02a0a1050041400e0606160185802a0a1858061600e060414010d801a0a1858061601c18032301c1801a0a0c8c032301c18061601858009031858061601a1801a181a1800903068601a181a18061601858041030c8c032304002861601858041031858061604003432300c8c00b0a0c8c03130400006160185800b0a1858061604000032300c8c100034000c7030 (by decide +kernel)

def state123_3 : List Sig := [0xffffffffffffffffeeeeeeeeeeeeeeeeffffffffffffffffeeeeeeeeeeeeeeee,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 0,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude123_3 : Impossible true (goalAt 123) 5 state123_3.toFinset :=
  node_ok cuts123 [] 0x38181c18070600a06050301c18070604003868601c18038301a18038181a18068600882838301a18068600e0c00b0a1c18011031c18009031a1800b0a1a1800b0a0e06021030e06061604003462601c1801a0a1898062601a1800903189802a0a1898062600e0603230160605030140c03818 (by decide +kernel)

def state123_4 : List Sig := [0xffffffffffffffffffffffffaaaaaaaaffffffffffffffffffffffffaaaaaaaa,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 6,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude123_4 : Impossible true (goalAt 123) 5 state123_4.toFinset :=
  node_ok cuts123 [] 0x50301c1807060068281a0a1c180706006828190a1c180706002c2868601c18038301a18038301a18068600e0c009031a18068600240c0b0a1a18068604004061601c18031301858061601a1801a181858031301858061600c4c01a18185806160068601918185806160068604103400303818 (by decide +kernel)

def state123_5 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 6,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 0,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude123_5 : Impossible true (goalAt 123) 6 state123_5.toFinset :=
  node_ok cuts123 [⟨state123_1,exclude123_1⟩,⟨state123_3,exclude123_3⟩,⟨state123_4,exclude123_4⟩] 0x140c01a0a140c1000e1c1807060140c070601c181000d068281a0a0e0601a0a0e0602a0a1c18070600e06070601c1802a0a0682828180682868601a18070600e0c070600682838300e0c070601a18068604003438300e0c050301a18068604004468601a18050300e0c038300e06009030e06021031a18068600e06068601a18021030240c220a0440c0b0a02c2870604003070600440d000e0440c706002c2870600240d00100240c686002c2868600240c0b0a02c2868604003068604002d000b18581000c02c280b0a140c1000c140c1000c400360000140c00b0a140c0210302c280b0a0e061000c0e06021038000821030e0600b0a0e0601a0a1898062601c18032301c1801a0a0c8c032301c18062601898009031898062601a1801a181a1800903068601a181a180626018981000d0c8c03230140c06260189820001189806260140c032300c8c02a0a068601a180e0606260189802a0a1898062600e0601a1806861000b4002c5818 (by decide +kernel)

def state123_6 : List Sig := [0xffffeeeeffffeeeeffffeeeeffffeeeeffffeeeeffffeeeeffffeeeeffffeeee,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 4,input 0,input 3,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude123_6 : Impossible true (goalAt 123) 6 state123_6.toFinset :=
  node_ok cuts123 [] 0x7030160605030140c038301a18068600e0c048401a18068601218068600e0c038301a18068600e0c038301a1800b0a1c0c041031c0c00b0a0e06021030e06009031a1800b0a1a1800b0a06428110302c2831304002470301282870300682838180a82838180682870600c8c070301282832300686032300c8c01a180c8c06860068606860068283230088c062601c0c048081c0c048080e06028080e0602808 (by decide +kernel)

def state123_7 : List Sig := [0xffff0000ffff0000eeee0000eeee0000ffff0000ffff0000eeee0000eeee,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 6,input 0,input 3,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude123_7 : Impossible true (goalAt 123) 5 state123_7.toFinset :=
  node_ok cuts123 [] 0x7030160605030140c048401a18068601218038301a18068600e0c00b0a0a06021030a06009031a1800b0a1a1800b0a1c0c041031c0c061601090062601898042601898068600686062600c8c062601898032301418070601c18050401a18038301a18070601c180110302c2870601206070601c1807030189803230189807060 (by decide +kernel)

def state123_8 : List Sig := [0xffffffffffffffffeeeeeeeeeeeeeeeeffffffffffffffffeeeeeeeeeeeeeeee,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 6,input 0,input 3,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude123_8 : Impossible true (goalAt 123) 6 state123_8.toFinset :=
  node_ok cuts123 [⟨state123_3,exclude123_3⟩,⟨state123_7,exclude123_7⟩] 0x38181282a00000e06038180a8282a0a0e06050401c1807060141801a0a1c18070600682a00011c18070604002448401a18068601218068601c18038301a18038301a18068600e0c038301a18068600e0c00b0a0e06021030e0600b0a1c18011031c18009031a1800b0a1a1800b0a12428410302c2861604003470301090062601898042601898070600682862601898068600240c6260128286260089803230 (by decide +kernel)

def state123_9 : List Sig := [0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 0,input 3,input 4,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude123_9 : Impossible true (goalAt 123) 7 state123_9.toFinset :=
  node_ok cuts123 [⟨state123_0,exclude123_0⟩,⟨state123_2,exclude123_2⟩,⟨state123_5,exclude123_5⟩,⟨state123_6,exclude123_6⟩,⟨state123_8,exclude123_8⟩] 0x4003070300e06070304002c58184003058184003070308000850304002c58180e0605030400347030068287030400244a0a1c18070604003870301c1807060400344a0a0682848184002c3818141005040400302a0a1c18070604003038181c18070604002c2a0a1410050604003458180e0c038304002070301a18068604000858181a18068604003470300e0c038304002c38181210048404003021031a18068604003038181a18068604002c2103121004860400241a0a1a18068604002070600e0c07060400081a0a0e0c038304002470601a18068604000c410302c280b0a4000c70304000c70304000c41038000441034000c703002c2870304000c210302c280b0a4000c38184000c38184000c21034003021034000c381802c2838184000c110302c280b0a4000c70604000c70604000c11038000011034000c706002c2870604000c09034002009034000c686002c2868604000c090302c280b0a4000c68604000c6860400010000400006160400344a0a0c8c03230400287030189806260800104a0a1898062604003470300c8c032304002c2a0a109004240400303818189806260400302a0a1898062604002c3818109004260400241a0a1898062604002870600c8c070608000c1a0a0c8c03230400247060189806260400200903189806260400086860068606860400080903068601a18400206860189806260 (by decide +kernel)

def state123_10 : List Sig := [0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa,input 0,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 1,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude123_10 : Impossible true (goalAt 123) 6 state123_10.toFinset :=
  node_ok cuts123 [⟨state123_1,exclude123_1⟩] 0x38180682838180a82870601c18038181c18070600a8281a0a0a06050300682850304005070601c18050301c1807060400501a0a068281a0a1a18068601c18038301c1801a0a0e0c038301c18068601a180381802c0c381808c0c68601a18038181a180686008c0c0b0308829000f0e0c03830140c068601a18100111a1806860140c038300e0c01a0a1898062601c18032301c1801a0a0c8c032301c1806260189800b031898062601a1801a181a1800b03068601a181a1806260189802a0a068601a180e0606260189802a0a1898062600e0601a1806861000d0c8c03230140c0626018981000d189806260140c032300c8c013031858061601c181000c1c18013034001c13031c1806160185800b031858061601a181000c1a1800b03400440b031a180616018581000c18580616018981000c18981000c4003600001898061601858023034004823030e06061601858023031858061600e061000c0e061000640018313008c0d0005160603818140c0503008c0c5030140c03818400143818 (by decide +kernel)

def state123_11 : List Sig := [0xffffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00,input 3,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 0,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude123_11 : Impossible true (goalAt 123) 6 state123_11.toFinset :=
  node_ok cuts123 [] 0x38180682838180a82870601c18038181c18070600a8281a0a0a060503004c0c50304005070601c18050301c180706040050130304c0c1a0a1898062601c18032301c1801a0a0c8c032301c1806260189802a0a068601a180e0606260189802a0a1898062600e0601a180686100131898062601a1801a181a181000d068601a181a180626018981000d0c8c03230140c0626018981000d189806260140c032300c8c013031858061601c18031301c18013030c4c031301c180616018581000d185806160189800b0a18981001102c280b0a1898061601858023030646019180e06061601858023031858061600e06019180646100131858061601a18019181a18100110646019181a18061601858100110c4c03130140c06160185810011185806160140c031300c4c01a0a1a18068601c18100131c1801a0a4001c1a0a1c18068601a180381840048381808c0c68601a18038181a180686008c0d00131406100064001838300e06100050e0602303140c050300e0605030140c02303400142303 (by decide +kernel)

def state123_12 : List Sig := [0xff00ff00ff00ff00ff00ff00aa00aa00ff00ff00ff00ff00ff00ff00aa00aa,input 0,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 6,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude123_12 : Impossible true (goalAt 123) 5 state123_12.toFinset :=
  node_ok cuts123 [] 0x50301c18070600482838181c18070600a06062601c18032301898032301898062600c8c01a181898062600686058181858070600c4c0616018580626002c2861600c4c061601858031300646061601858019181a18038301c1806860189801a181898068600e0c068601a18038300882868601a1803818185801918185806860 (by decide +kernel)

def state123_13 : List Sig := [0xffffffffffffffffffffffffaaaaaaaaffffffffffffffffffffffffaaaaaaaa,input 0,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 6,input 1,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude123_13 : Impossible true (goalAt 123) 6 state123_13.toFinset :=
  node_ok cuts123 [⟨state123_4,exclude123_4⟩,⟨state123_12,exclude123_12⟩] 0x50301c1807060068281a0a1c1807060068281a0a1c18070600682868601c18038301a18038301a18068600e0c00b031a180686002c0e00011a18068604004c62601c18032301898062601a1801a181898032301898062600c8c01a18189806260068601a181898062600686043034003038181858070600c4c0616018580686002c0c61601858062608000061600c4c0616018580313008c0c6160044c01918 (by decide +kernel)

def state123_14 : List Sig := [0xffffffffffffffffffffffffff00ff00ffffffffffffffffffffffffff00ff00,input 3,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 6,input 0,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude123_14 : Impossible true (goalAt 123) 6 state123_14.toFinset :=
  node_ok cuts123 [] 0x50301c18070600682838181c18070600a06013031c180706004c0c62601c18032301898032301898062600c8c01a181898062600686062601a1801a181898012101898062600484061601c1803130185806160189800b0a1858031301858061600c4c019181858061600646061601a18019181858011101858061600444058184004c23031a18070600e0c068600e0c068601a18038300e0606860088280b03 (by decide +kernel)

def state123_15 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 6,input 0,input 1,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude123_15 : Impossible true (goalAt 123) 7 state123_15.toFinset :=
  node_ok cuts123 [⟨state123_5,exclude123_5⟩,⟨state123_10,exclude123_10⟩,⟨state123_11,exclude123_11⟩,⟨state123_13,exclude123_13⟩,⟨state123_14,exclude123_14⟩] 0x4001850300682850304001900141c18070604001850301c1807060400190006068281a0a4001c3818068283818400502a0a1c18070604001c38181c1807060400502a0a068282818400501a0a1a18068604004c70600e0c070604001c1a0a0e0c038304005070601a18068604001900060e0c038304001850301a18068604001a00021a18068604001850300e0c0383040048381802c0c38184004c23031a18068608001038181a18068604004c230302c0c220a400501a0a1898062604002c70600c8c07060400341a0a0c8c032304005070601898062604004c0b031898062604002c6860068606860400340b03068601a184004c68601898062604001900060c8c0323040018503018980626040019000d1898062604001850300c8c03230400342a0a068601a184002c3818189806260400342a0a1898062604002c3818068601a184005013031858061604003070600c4c070604001c13030c4c031304005070601858061604004c0b03185806160400306860064606860400440b030646019184004c68601858061604002d000d18580616040030626002c28626040036000002c280b0a4002c62601858061604001900060c4c031304001850301858061604001a00011858061604001850300c4c031304004823030646019184003038181858061608000c2303185806160400303818064601918400150005400145818 (by decide +kernel)

def state123_16 : List Sig := [0xffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaa,input 0,input 4,input 1,input 3,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude123_16 : Impossible true (goalAt 123) 7 state123_16.toFinset :=
  node_ok cuts123 [⟨state123_0,exclude123_0⟩] 0x70300e06070301606100141606070304001c5030160603818140c058180e0c038301c0c068601a18058181a18068601c0c038300e0c0381812100484008c0c68601a18038181a180686008c0c48401218100041a180686004c0c38300e0c100020e0c0383004c0c68601a18100021a18068604000438300e0c100020e0c038304000468601a1804a0a0c8c032301c0c06260189804a0a1898062601c0c032300c8c02a0a1090042400e0606260189802a0a1898062600e0604240109800b031898062601a1801a181a1800b03068601a181a18062601898013031898062600440432300c8c013030c8c032300440462601898100091898062604000032300c8c100090c8c0323040000626018980703004c0c70301282900041282870304001c703012828130312828381804c0c38180a82900040a82838184005038180a82813030a82900034000c706010c0c31300c4c070304000c703010c0d000710c0c70300c4c0313008c0c19180646038180c4c0313008c0c31300c4c0381806460191802c0c31300c4c0686006460686002c0c19180646068600c4c068604000c31300c4c062604000c62604000d00098000062600c4c0626004c0d000404c0d00030c4c031304000d0003084c100034001061601c0c100061c0c04a0a4001c4a0a1c0c100071c0c04a0a400184a0a0e06100050e0602a0a400502a0a0e06100140e0602a0a400142a0a (by decide +kernel)

def state123_17 : List Sig := [0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa,input 0,input 6,input 1,input 3,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude123_17 : Impossible true (goalAt 123) 7 state123_17.toFinset :=
  node_ok cuts123 [⟨state123_2,exclude123_2⟩,⟨state123_10,exclude123_10⟩] 0x100060e060381810c0d000610c0d000c4001a000110c0c38180e061000c0e060381840014230308c0d000c08c0c23034001438180e06038181410050400a82870601c18038181c18070600a8285040141810006068281a0a10c0c70601c18100071c180706010c0c1a0a068290007068281a0a4001070601c18100071c1807060400101a0a06828381812100484008c0c68601a18038181a180686008c0c4840121801a0a1a18068601c18038301c1801a0a0e0c038301c18068601a18100060e0c0383010c0c68601a18100021a180686010c0c38300e0c100020e0c038304000468601a18100021a18068604000438300e0c02a0a1090042400e0606260189802a0a1898062600e0604240109801a0a1898062601c18032301c1801a0a0c8c032301c1806260189800b031898062601a1801a181a1800b03068601a181a18062601898043030c8c032301040462601898043031898062601040432300c8c1000d0c8c0323040000626018981000d1898062604000032300c8c100034000c703008c0c414010500381818580616008c0c616018580381810500416004c0c61601858070604000c706004c0d000704c0c706018580616002c0c61601858068604000c686002c0d000202c0c68601858061604000c61601858062604000c62604000d000d80000626018580616010c0d000610c0d00031858061604000d0003085810003400183130 (by decide +kernel)

def state123_18 : List Sig := [0xffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00,input 3,input 4,input 0,input 1,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude123_18 : Impossible true (goalAt 123) 7 state123_18.toFinset :=
  node_ok cuts123 [] 0x70300e06070301606100141606070304001c5030160603818140c04a0a0c8c032301c0c06260189804a0a1898062601c0c032300c8c02a0a1090042400e0606260189802a0a1898062600e0604240109801a0a1898062604002432300c8c01a0a0c8c032304001062601898100011898062600e0c01a180e0c10009068601a180e0c062601898100091898062604000032300c8c100090c8c032304000062601898043030c4c031301c0c061601858043031858061601c0c031300c4c023031050041400e06061601858023031858061600e0604140105810009185806160189800b0a18981000202c280b0a1898061601858100041858061600682831300c4c100020c4c031300682861601858100011858061600e0c019180e0c100020646019180e0c061601858100021858061604000c31300c4c100020c4c031304000c61601858070300682870301282900041282870304001c7030128281a0a1206038180682838180a82900040a82838184005028180a8281a0a0a06100014000470601606038300e0c070304000470301606100071406070300e0c038300e06100140e06023030e0c038300e06038300e0c023034000423030682900040682900010e0c038304000500010a0c100014001068601c0c100061c0c043034001c43031c0c100071c0c043034001843030e06100050e06023034005023030e06100140e0602303400142303 (by decide +kernel)

def state123_19 : List Sig := [0xffffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00,input 3,input 6,input 0,input 1,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude123_19 : Impossible true (goalAt 123) 7 state123_19.toFinset :=
  node_ok cuts123 [⟨state123_11,exclude123_11⟩] 0x100060e06038181606100061606100134001a00001606038180e061001308c0c23034001438180e06100130e060381840014230308c0c38181410050400a82870601c18038181c18070600a82850401418058180682858181282870601c18058181c1807060128281a0a12061000704c0c13034001070601c18100071c180706040010130304c0c2a0a1090042400e0606260189802a0a1898062600e0604240109801a0a1898062601c18032301c1801a0a0c8c032301c1806260189804a0a0c8c03230160606260189804a0a1898062601606032300c8c100011898062601a1801a181a181000d068601a181a180626018981000d0c8c0323040000626018981000d1898062604000032300c8c023031050041400e06061601858023031858061600e06041401058013031858061601c18031301c18013030c4c031301c180616018581000d185806160189800b0a18981000202c280b0a1898061601858100060c4c031301606061601858100021858061601606031300c4c100011858061601a18019181a18100020646019181a18061601858100020c4c031304000c61601858100021858061604000c31300c4c100014000470300e06048401210023031a18068600e06068601a18023031210048600682868601a18070604000470600682900070682870601a18068601606100061606100011a18068604000500010a1810001400183830 (by decide +kernel)

def state123_20 : List Sig := roots 123
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude123_20 : Impossible true (goalAt 123) 8 state123_20.toFinset :=
  node_ok cuts123 [⟨state123_9,exclude123_9⟩,⟨state123_15,exclude123_15⟩,⟨state123_16,exclude123_16⟩,⟨state123_17,exclude123_17⟩,⟨state123_18,exclude123_18⟩,⟨state123_19,exclude123_19⟩] 0x4001470300e06070304001458184001458184001470308000450304001458180e0605030400187030068287030400104a0a1c18070604001c70301c1807060400104a0a068284818400143818141005040400142a0a1c18070604001438181c1807060400142a0a1410050604001858180e0c038304000470301a18068608001458181a18068604000470300e0c038304001438181210048404001423031a18068604001438181a1806860400142303121004860400101a0a1a18068604000470600e0c07060800101a0a0e0c038304000470601a1806860400004a0a0c8c03230400007030189806260400004a0a1898062604000070300c8c03230400002a0a109004240400003818189806260400002a0a189806260400003818109004260400001a0a1898062604000070600c8c07060400001a0a0c8c03230400007060189806260400000b03189806260400006860068606860400000b03068601a184000068601898062604001843030c4c031304000c70301858061608000c43031858061604000c70300c4c031304001423031050041404001438181858061604001423031858061604001438181050041604001013031858061604000c70600c4c070608000813030c4c031304000c7060185806160400040b031858061604000c6860064606860400080b0306460191840004686018580616040001000018580616040000626002c28626040002000002c280b0a400006260185806160 (by decide +kernel)

theorem lower123 : Claim 123 9 :=
  fromSearch 67 (by decide +kernel) exclude123_20

theorem lower235 : Claim 235 9 :=
  fromLift 9 2 83 lower233 (by decide +kernel)

theorem lower209 : Claim 209 5 :=
  fromLift 5 16 4 lower193 (by decide +kernel)

theorem lower153 : Claim 153 5 :=
  fromLift 5 16 3 lower137 (by decide +kernel)

def rule217_0 : {c : Cut // CutGood (goalAt 217) c} :=
  ruleFor 217 lower209 none (by decide +kernel)

def rule217_1 : {c : Cut // CutGood (goalAt 217) c} :=
  ruleFor 217 lower216 none (by decide +kernel)

def rule217_2 : {c : Cut // CutGood (goalAt 217) c} :=
  ruleFor 217 lower201 none (by decide +kernel)

def rule217_3 : {c : Cut // CutGood (goalAt 217) c} :=
  ruleFor 217 lower153 none (by decide +kernel)

def rule217_4 : {c : Cut // CutGood (goalAt 217) c} :=
  ruleFor 217 lower89 none (by decide +kernel)

def rule217_5 : {c : Cut // CutGood (goalAt 217) c} :=
  ruleFor 217 lower81 none (by decide +kernel)

def rule217_6 : {c : Cut // CutGood (goalAt 217) c} :=
  ruleFor 217 lower137 none (by decide +kernel)

def rule217_7 : {c : Cut // CutGood (goalAt 217) c} :=
  ruleFor 217 lower193 none (by decide +kernel)

def rule217_8 : {c : Cut // CutGood (goalAt 217) c} :=
  ruleFor 217 lower73 none (by decide +kernel)

def rule217_9 : {c : Cut // CutGood (goalAt 217) c} :=
  ruleFor 217 lower200 none (by decide +kernel)

def cuts217 : Cuts (goalAt 217) := [rule217_0,rule217_1,rule217_2,rule217_3,rule217_4,rule217_5,rule217_6,rule217_7,rule217_8,rule217_9]

def state217_0 : List Sig := [0xffffffffffffffffffaaffaaffaaffaaffffffffffffffffffaaffaaffaaffaa,input 0,input 6,0xffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude217_0 : Impossible true (goalAt 217) 4 state217_0.toFinset :=
  node_ok cuts217 [] 0x12100c040220604840120604840121000901262408880262410002301008818301004818322404140301008101105004140121001918105001918105004140064609190301009890262410008 (by decide +kernel)

def state217_1 : List Sig := [0x5555555555555555550055005500550055555555555555555500550055005500,input 0,input 6,0xffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude217_1 : Impossible true (goalAt 217) 4 state217_1.toFinset :=
  node_ok cuts217 [] 0x484030100881812100481812100484002404c04022060c04012060111024640919030100818024640919020640919032640410124640c040262409890204048880262409890024049890322404818262404140 (by decide +kernel)

def state217_2 : List Sig := [0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa,input 0,0xffffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00,0xffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude217_2 : Impossible true (goalAt 217) 4 state217_2.toFinset :=
  node_ok cuts217 [] 0x48403010088181210098902220098900440448181210048404001cc040262409890104044140301008101105004140121001101105004101262404140262409190301008818301004818322409890120609890 (by decide +kernel)

def state217_3 : List Sig := [0xffffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00,input 6,0xffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00,input 0,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude217_3 : Impossible true (goalAt 217) 5 state217_3.toFinset :=
  node_ok cuts217 [⟨state217_0,exclude217_0⟩,⟨state217_1,exclude217_1⟩,⟨state217_2,exclude217_2⟩] 0x81011050041403010091902464081012464091903010041401050011012060081801210091902464011012464091901210081802064100062464091901206041401050200021050041401206091902464200012464091902624041402624200001050041402624091902464088181210048403010100053010088184001488183010048401210048180440448184001c484012100481812100484040018110104404989004404989040008484022200989012100989040008110104404c04012060c04022061000522060c04040014c04022060481812061000040000c890301010008301008101262409890301009890262408101400208101 (by decide +kernel)

def state217_4 : List Sig := [0xffaaffaaffaaffaa0000000000000000ffaaffaaffaaffaa,input 6,input 0,0xffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude217_4 : Impossible true (goalAt 217) 4 state217_4.toFinset :=
  node_ok cuts217 [] 0x484030100881812100c89030200c09030240414030100810110500414012100191810500c99032240414032240c04032240c890162408818262409890301008880262409890121009190246401918262404818 (by decide +kernel)

def state217_5 : List Sig := [0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa,input 6,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,0xffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude217_5 : Impossible true (goalAt 217) 4 state217_5.toFinset :=
  node_ok cuts217 [] 0x50403010088181410009011410050400240419181410050404001c414026240989010500888026240989010500989010500414026240919024640414026240c04022060c04022060d090301008818301001918 (by decide +kernel)

def state217_6 : List Sig := [0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 0,0xffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude217_6 : Impossible true (goalAt 217) 5 state217_6.toFinset :=
  node_ok cuts217 [⟨state217_0,exclude217_0⟩,⟨state217_4,exclude217_4⟩,⟨state217_5,exclude217_5⟩] 0xc04012060c04022060d09034240c04034240d09022060481814240881814100504030101000530100881840014881830100504014100d09002404d09030200504030200d09014100c0903020009013024081010646019183010100053010081014001481013010019183010041010646019183424100093424041018000841013424019183424009014001c090114100191814100090106460191814101000714101000040000919022061000822060c04026240989022060989026240c04040020c04012060989026240d09080004c89012062000012060d090262409890024050002222005040262409890024049890262405040400085040 (by decide +kernel)

def state217_7 : List Sig := [0xff000000ff000000aa000000aa000000ff000000ff000000aa000000aa,input 0,input 6,input 3,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude217_7 : Impossible true (goalAt 217) 4 state217_7.toFinset :=
  node_ok cuts217 [] 0x881826240989030100989032240481826240c04034240d09014200414024640919010500919026240191824640919034240414024640504022060c04014100484030240c09014100d090206409190105009190 (by decide +kernel)

def state217_8 : List Sig := [0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa,input 0,input 6,0xffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00,input 3,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude217_8 : Impossible true (goalAt 217) 5 state217_8.toFinset :=
  node_ok cuts217 [⟨state217_5,exclude217_5⟩,⟨state217_0,exclude217_0⟩,⟨state217_2,exclude217_2⟩,⟨state217_7,exclude217_7⟩] 0x22060989026240c0402220098901040600022624098904000200012624050403010088181410011011410050400440600031410050404001cc04022060c04022060d09010500c040204044140105009890800009890105005040044044140104044140400189190301008818301008818 (by decide +kernel)

def state217_9 : List Sig := [0xffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00,input 3,input 0,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude217_9 : Impossible true (goalAt 217) 6 state217_9.toFinset :=
  node_ok cuts217 [⟨state217_3,exclude217_3⟩,⟨state217_6,exclude217_6⟩,⟨state217_8,exclude217_8⟩] 0x40020c04012060c04040014881834240d09040014c04034240d09040020881812060509040020810110500414040014c04024640919040014810124640919040020c04010500414040018410124640919040024d09010500d09080008410110500414040018d0902464091904000100002464091904000098900646098904000200010646019184000098902464091904001c11012060081804001c50402464091904001c11012464091904001c504020600819040000881840020881840000c04026240989040000881826240989040000c04040000c04040000481826240989040000d09040000c89040000481880000481840000d09026240989040009000240008888040020881814100504040014c04040014c04040014881840014881840020c04014100504040018d09004404d0904001cc08014100c0804001cd09014100c09040018c08004404c090 (by decide +kernel)

def state217_10 : List Sig := [0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa,input 6,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude217_10 : Impossible true (goalAt 217) 4 state217_10.toFinset :=
  node_ok cuts217 [] 0x484026240989012100484026240989010500989012100484026240989024640484024640414014100881810500504004404504004404414022060414022060c090141009190246410008105009190246408818 (by decide +kernel)

def state217_11 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaa,input 6,input 0,0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude217_11 : Impossible true (goalAt 217) 4 state217_11.toFinset :=
  node_ok cuts217 [] 0x12100989026240484026240c09012100989022060989026241000522060504014101000224640989002404919010500919024640414024640c09010500919006460504030240c090044045818 (by decide +kernel)

def state217_12 : List Sig := [0xffffffffffffffff0000000000000000aaaaaaaaaaaaaaaa,input 6,input 0,0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude217_12 : Impossible true (goalAt 217) 4 state217_12.toFinset :=
  node_ok cuts217 [] 0x484026240989012100989012100484026240919026240090124640414024640919010500919010500414024640504016060504012060989012100989012100880814100881814100919010500919010500c090 (by decide +kernel)

def state217_13 : List Sig := [0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 0,0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 3,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude217_13 : Impossible true (goalAt 217) 5 state217_13.toFinset :=
  node_ok cuts217 [⟨state217_10,exclude217_10⟩,⟨state217_11,exclude217_11⟩,⟨state217_12,exclude217_12⟩] 0x504012020504004404c09030240504030240c09004404480812062000216060581822060c09030242000130240c090220605818142005818262409890302404840302405818121004840302409890262410008121004840141009890262410005262409890141004840121008818121004840400149890262408818262409890400144840121004101246409190302410009302404101800004101302409190246400901246409190262410005262400901400140901262409190246401101400201101141009190246401101246409190141010008141010004400104140044050002301005040220605040044048818220605040400085040 (by decide +kernel)

def state217_14 : List Sig := [0x5555555555555555555555555555555555555555555555550000000000000000,input 0,input 6,0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude217_14 : Impossible true (goalAt 217) 4 state217_14.toFinset :=
  node_ok cuts217 [] 0x484026240989012100989030240484026240504030240c09004404111026240191826240090814100191814100191830240410130240989022060989002404504022060504004404c09016060c090220609190 (by decide +kernel)

def state217_15 : List Sig := [0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa,input 0,0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude217_15 : Impossible true (goalAt 217) 4 state217_15.toFinset :=
  node_ok cuts217 [] 0x484026240989012100881826240989002404989030240484026240881814100504004404414026240090126240414014100110110500410110500414022060919014100c09030241000816060c090302408818 (by decide +kernel)

def state217_16 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 0,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude217_16 : Impossible true (goalAt 217) 5 state217_16.toFinset :=
  node_ok cuts217 [⟨state217_11,exclude217_11⟩,⟨state217_14,exclude217_14⟩,⟨state217_15,exclude217_15⟩] 0x1000812100484014100989026241000526240989014100484012101000526240989030240484030241000512100484030240989026240881802404881840014989026240881826240989040014090102404090124640919026240191826240090106460191826240919024640110110500414014100919024640110124640919014100414010501000624640919030240414030242000210500414030240919024642000106460191822060919024642000024640919022060191806460881804404881840008504014100881814100504040008110104404504040020504004404c09030240504030240c090044050008044050004400105818 (by decide +kernel)

def state217_17 : List Sig := [0xffff0000ffff0000aaaa0000aaaa,input 0,input 6,input 7,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude217_17 : Impossible true (goalAt 217) 4 state217_17.toFinset :=
  node_ok cuts217 [] 0x484026240989012100989030240484026240581830240c09014200919026240191824640414024640919010500919030240414024640484026240484026240c04012060c09014100c090105009190105009190 (by decide +kernel)

def state217_18 : List Sig := [0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa,input 0,input 6,0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 7,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude217_18 : Impossible true (goalAt 217) 5 state217_18.toFinset :=
  node_ok cuts217 [⟨state217_11,exclude217_11⟩,⟨state217_10,exclude217_10⟩,⟨state217_15,exclude217_15⟩,⟨state217_17,exclude217_17⟩] 0x12100989026240484012100989026240484026240484012100989026240484012100989030100410122062000222060504004404504004404c090105009890024049890105008818800044140105005040044044140104044140400189190400108818800008818141020003141010008 (by decide +kernel)

def state217_19 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 7,input 0,input 3,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude217_19 : Impossible true (goalAt 217) 6 state217_19.toFinset :=
  node_ok cuts217 [⟨state217_13,exclude217_13⟩,⟨state217_16,exclude217_16⟩,⟨state217_18,exclude217_18⟩] 0x40011000416060581840010881830240c09040012000130240c09040010881816060508040020504012020504040020110130240c09040020504030240c09040020110112020481840014581826240989040014c09012100c09040014581812100484040014c09026240989040010881812100484040011000526240989040010881826240989040011000412100484040021000812100484040020504026240989040021000526240989040020504012100484040018410124640919040024c09010500c09080008410110500414040018c09024640919040014090124640919040014989006460989040014090106460191840014989024640919040011000410500414040010881824640919040012000024640919040010881810500414040020110110500414040020504024640919040020110124640919040020504010500414040009000240008c040 (by decide +kernel)

def state217_20 : List Sig := [0xffffffffffffffffffaaffaaffaaffaa,input 6,input 0,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude217_20 : Impossible true (goalAt 217) 4 state217_20.toFinset :=
  node_ok cuts217 [] 0x34240c08030240c09022200989026240889026240d09012100989020600919024640819024640989006460919024640d09010500919014100881814100c04012100989012100989010500919010500919014240d09030100d090 (by decide +kernel)

def state217_21 : List Sig := [0xffff0000ffff0000ffaa0000ffaa0000ffff0000ffff0000ffaa0000ffaa,input 6,input 0,input 3,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude217_21 : Impossible true (goalAt 217) 4 state217_21.toFinset :=
  node_ok cuts217 [] 0x12100989026240484026240d09012100989010500919024640414024640989006460919024640d09010500919030100d09034240508014100881830100504022240989012100989020640919010500919030240c09014100d090 (by decide +kernel)

def state217_22 : List Sig := [0xffffffffffffffffffaaffaaffaaffaaffffffffffffffffffaaffaaffaaffaa,input 6,input 0,input 3,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude217_22 : Impossible true (goalAt 217) 5 state217_22.toFinset :=
  node_ok cuts217 [⟨state217_0,exclude217_0⟩,⟨state217_20,exclude217_20⟩,⟨state217_21,exclude217_21⟩] 0x504030100881814100581814100504012062000214100504040008484030100981812100484014102000012100581812100484014060989010500c04020404414010500504006460414010500484006460414006460414010500191824640c04026060c04016060d090301020001301010004 (by decide +kernel)

def state217_23 : List Sig := [0xffaaffaaffaaffaa0000000000000000ffaaffaaffaaffaa,input 6,input 0,input 3,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude217_23 : Impossible true (goalAt 217) 5 state217_23.toFinset :=
  node_ok cuts217 [⟨state217_4,exclude217_4⟩] 0x504030100881814100d09030200c09030240484030100981812100484014102000012100d89034240484034240414030100810110500414014100191810500414012100191810500d19034240414034240c04034240d090142409818301009818301001101141001101141009890262400901121009190246401918105005818 (by decide +kernel)

def state217_24 : List Sig := [0xffffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00,0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude217_24 : Impossible true (goalAt 217) 4 state217_24.toFinset :=
  node_ok cuts217 [] 0x14100c04022060504006460504014100411804404504014100090110500894026060414010500504004404414024640919010500501826240989010501000130100981830100191834240d090064601118301008101301000901 (by decide +kernel)

def state217_25 : List Sig := [0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa,input 6,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 3,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude217_25 : Impossible true (goalAt 217) 5 state217_25.toFinset :=
  node_ok cuts217 [⟨state217_5,exclude217_5⟩,⟨state217_24,exclude217_24⟩] 0x14100c04022060504004404504014100110106460504014100091826060c04026060c0400240450408000050402624009011040600010240419180240419180446041403010098181050041401410011011050041011050041404000c919024640414040000c04026060c04026060d090301009818301001918 (by decide +kernel)

def state217_26 : List Sig := [0xffffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00,input 6,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 0,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude217_26 : Impossible true (goalAt 217) 5 state217_26.toFinset :=
  node_ok cuts217 [⟨state217_24,exclude217_24⟩] 0x14100c04022060504016060504014100481804404504014100090106460c04020404c04002420504006460504024640191814462000006460090106460191804460484030100981812100484014100110112100581812100484014060989026240484040004c04026060c04016060d090301008101301000901 (by decide +kernel)

def state217_27 : List Sig := [0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 0,input 3,input 4,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude217_27 : Impossible true (goalAt 217) 6 state217_27.toFinset :=
  node_ok cuts217 [⟨state217_6,exclude217_6⟩,⟨state217_22,exclude217_22⟩,⟨state217_23,exclude217_23⟩,⟨state217_25,exclude217_25⟩,⟨state217_26,exclude217_26⟩] 0xc04016060c04026060d09034240c04034240d09026060581814240981814100504030101000530100981840014881830100504014100d09004404d09030200504030200d09014100c0903020011013024098180240498183010100003010098184001498183010009013010058180240458183424100003424058188001058183424009013424100000240409011410100001410100004001e000014100090114101000040004989020404191806460c04040004c04020405000520404c04006460c04010404191806460d09040004d09010406000310404d09006460d09004404090802420504006460504004404191806460504002420504002405000002405000106460191840001000004461000040000919026061000426060c04040014c04026061000526060c04040010c04016061000316060d09080008d09016062000116060d0904000cd0900440500020440450404001c5040044050007044045040400085040 (by decide +kernel)

def state217_28 : List Sig := [0xff00ffffff00ffffff00ffaaff00ffaa,input 3,input 0,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude217_28 : Impossible true (goalAt 217) 3 state217_28.toFinset :=
  node_ok cuts217 [] 0x24640c09010500919024640989006460919026240c09012100989012060c09014100c090105009190105009190121009890121009890 (by decide +kernel)

def state217_29 : List Sig := [0xff00ffffff00ffffff00ffaaff00ffaaff00ffffff00ffffff00ffaaff00ffaa,input 3,input 0,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude217_29 : Impossible true (goalAt 217) 4 state217_29.toFinset :=
  node_ok cuts217 [⟨state217_28,exclude217_28⟩] 0xc04034240d09014200414024640919010500919034240414024640919012100191824640919020640414024640484030100881812100481834240484034240989014102000030100504030240c09014100d090 (by decide +kernel)

def state217_30 : List Sig := [0xff00ff00ff00ff00ff00ff00ff00ff000000ff000000ff000000aa000000aa,input 7,input 0,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude217_30 : Impossible true (goalAt 217) 3 state217_30.toFinset :=
  node_ok cuts217 [] 0x30100c09030240481824640c090105009190105009190246404140262404840302409890246401918246409890121009890262404840 (by decide +kernel)

def state217_31 : List Sig := [0xffffffffffffffffffffffffffffffff0000ffff0000ffff0000aaaa0000aaaa,input 7,input 0,input 6,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude217_31 : Impossible true (goalAt 217) 4 state217_31.toFinset :=
  node_ok cuts217 [⟨state217_30,exclude217_30⟩] 0x989030240484026240484026240989012102000026240989014100c04030240c09016060504030240c090160609190262401918246409190302404140246404140246409190105001918246409190141008818 (by decide +kernel)

def state217_32 : List Sig := [0xffff0000ffff0000aaaa0000aaaa0000ffff0000ffff0000aaaa0000aaaa,input 0,input 6,input 3,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude217_32 : Impossible true (goalAt 217) 5 state217_32.toFinset :=
  node_ok cuts217 [⟨state217_7,exclude217_7⟩,⟨state217_17,exclude217_17⟩,⟨state217_29,exclude217_29⟩,⟨state217_31,exclude217_31⟩] 0x22060484012100c04026240989022060989026240c04012100484016060989026240d09012100d09016060484012100d09026240989030100581830100881834240d09030100d09034240881816060508020404414010500c04024640919020404919024640c04010500414002404919024640989006460989002404191806460989024640919010404919024640d09010500d09010404414010500d09024640919030100504014100881880004881830102000330100881814100504012100504012100989080000989012102000212100989014100989010404110130240d09014100c09010404504014100d09004404d090105005040206409190044049190105001101105009190141009190 (by decide +kernel)

def state217_33 : List Sig := [0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00aa00aa00aa00aa,input 7,input 0,input 6,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude217_33 : Impossible true (goalAt 217) 4 state217_33.toFinset :=
  node_ok cuts217 [] 0x34240c08030240c09014100c04022060504030100d09034240509020600919024640819024640d090105009190105009190246404140222409890262408880262404840342409890246401918246409890121009890262404840 (by decide +kernel)

def state217_34 : List Sig := [0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000aaaa0000aaaa,input 7,input 0,input 6,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude217_34 : Impossible true (goalAt 217) 4 state217_34.toFinset :=
  node_ok cuts217 [] 0x26240d09012100989012100989026240484030100d09034240509024640989006460919024640d09010500919010500919024640414022240989022200989030240c09030200d090206409190206009190141008818301005040 (by decide +kernel)

def state217_35 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaa,input 7,input 0,input 6,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude217_35 : Impossible true (goalAt 217) 5 state217_35.toFinset :=
  node_ok cuts217 [⟨state217_11,exclude217_11⟩,⟨state217_33,exclude217_33⟩,⟨state217_34,exclude217_34⟩] 0xd09030200c09030240504030102000014102000214100504040008888026240989022240989034240484026240484026240989012102000126240989040000c04034240d09014240581820600919024640819024640989002404919024640d090105009190105009190246404140064609818 (by decide +kernel)

def state217_36 : List Sig := [0xffffffffffffffffaaaaaaaaaaaaaaaa,input 7,input 0,input 6,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude217_36 : Impossible true (goalAt 217) 5 state217_36.toFinset :=
  node_ok cuts217 [⟨state217_17,exclude217_17⟩] 0xd09030200c09030240504022020881814100888026240989022240989034240484026240484026240989012100d81834240d09026060818024640919020640919026240090124640919034240414024640414024640919010500504080000504040008484026240484026240581834240410134240414024640414024640c040 (by decide +kernel)

def state217_37 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude217_37 : Impossible true (goalAt 217) 4 state217_37.toFinset :=
  node_ok cuts217 [] 0x24640818024640c090141004140044044140044045040141001101222009890262408890262409190121009190121009890262404140024049890262400901105009190246405090160609190246401190260604140105010001 (by decide +kernel)

def state217_38 : List Sig := [0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 7,0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa,input 6,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude217_38 : Impossible true (goalAt 217) 5 state217_38.toFinset :=
  node_ok cuts217 [⟨state217_10,exclude217_10⟩,⟨state217_37,exclude217_37⟩] 0x440450401410011012464081802464081901410081018000050401410041400440441402220098902624088902624048401210098902624091901210091901210098902624048401210098902624041403424041012040600011040441401040441404000c810124640919004640414024640919040010c040 (by decide +kernel)

def state217_39 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa,input 0,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude217_39 : Impossible true (goalAt 217) 5 state217_39.toFinset :=
  node_ok cuts217 [⟨state217_37,exclude217_37⟩,⟨state217_15,exclude217_15⟩] 0x34240c08030240c09014100c04080004504004404504014100110122200989026240889026240d09012100989012100989026240484002404989026240090110500504004404414010500989002404989024640414020502000010500410110500414040004c04034240d09014240581834240d090400109818 (by decide +kernel)

def state217_40 : List Sig := [0xff00ff00ff00ff00aa00aa00aa00aa00ff00ff00ff00ff00aa00aa00aa00aa,input 3,input 0,input 6,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude217_40 : Impossible true (goalAt 217) 5 state217_40.toFinset :=
  node_ok cuts217 [⟨state217_7,exclude217_7⟩] 0x504030100881814100581814100504012060c04026060c04016060414030100810110500414014100191810500191810500414006460999026240191826240981826240989030100888026240989022240989036240581826240c04026060c04026060504080000504040008d090342404101160609190246404140064604840 (by decide +kernel)

def state217_41 : List Sig := [0xffffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00,input 3,0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa,input 0,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude217_41 : Impossible true (goalAt 217) 5 state217_41.toFinset :=
  node_ok cuts217 [⟨state217_2,exclude217_2⟩,⟨state217_24,exclude217_24⟩] 0x14100c04022060504016060504014100481804404504014100110110500c04020404414010500504004404414024640414012102000110500410110500414040004c04026060c04016060d090342405818400004840301009818121004840141020000121005818121004840140609890301008101301004101 (by decide +kernel)

def state217_42 : List Sig := [0xffff0000ffff0000aaaa0000aaaa0000ffff0000ffff0000aaaa0000aaaa,0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa,input 0,input 6,input 3,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude217_42 : Impossible true (goalAt 217) 5 state217_42.toFinset :=
  node_ok cuts217 [] 0x12100989026240484026240484012100989026240484012100989030100881830100881834240414030100810110500414026240090126240410110501000624640c04022060c04022060504022060c040141004840262404840262401101141005040044044140044044140141010002 (by decide +kernel)

def state217_43 : List Sig := [0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa,input 0,input 6,input 3,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude217_43 : Impossible true (goalAt 217) 6 state217_43.toFinset :=
  node_ok cuts217 [⟨state217_25,exclude217_25⟩,⟨state217_22,exclude217_22⟩,⟨state217_8,exclude217_8⟩,⟨state217_18,exclude217_18⟩,⟨state217_32,exclude217_32⟩,⟨state217_35,exclude217_35⟩,⟨state217_36,exclude217_36⟩,⟨state217_38,exclude217_38⟩,⟨state217_39,exclude217_39⟩,⟨state217_40,exclude217_40⟩,⟨state217_41,exclude217_41⟩,⟨state217_42,exclude217_42⟩] 0x98181410050403010100063010098188000c88183010050401410100030440411011040450401410100061410050401040411010440500068002e000440008504014101000614100504040009000640008981812100484030100989026240981826240989030100484012101000622200888014100989026242000226240989014100888022241000326240989010404484012102000a12100484010404989026242000926240989040000484012102000112100484040000989026240c04010404c04026061000326060c04080020c04026060410126061000140004d09020404414010500c04040004c04020406000720404c0401050041400440441401050050404000450400440500060440450401050041400240441401050098904000498900240600000240498901050098901040500031040500011050041404000500014000500014000c9190301010004301009818800189818301020005301009818400109818 (by decide +kernel)

def state217_44 : List Sig := [0xffffffffffffffff0000000000000000aaaaaaaaaaaaaaaa,input 6,input 0,input 7,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude217_44 : Impossible true (goalAt 217) 5 state217_44.toFinset :=
  node_ok cuts217 [⟨state217_12,exclude217_12⟩] 0x504030102000014100581814100504012060888026240989022240484026240989012100989012100484026240818024640919020640919026240090124640414024640919010500919010500414024640c04036060c04016060110114100110114100989012100989012100981830100810130100919010500919010500d090 (by decide +kernel)

def state217_45 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 0,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude217_45 : Impossible true (goalAt 217) 5 state217_45.toFinset :=
  node_ok cuts217 [⟨state217_37,exclude217_37⟩] 0x14100c04004404504034240c08030240c09004404504014100110122200989026240889012100989026240484026240d09012100989002404989026240090120600919024640819024640989002404919010500919034242000024640810124640919004640981830100c04040004c04034240d090142405818 (by decide +kernel)

def state217_46 : List Sig := [0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 0,input 7,input 3,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude217_46 : Impossible true (goalAt 217) 6 state217_46.toFinset :=
  node_ok cuts217 [⟨state217_38,exclude217_38⟩,⟨state217_13,exclude217_13⟩,⟨state217_35,exclude217_35⟩,⟨state217_44,exclude217_44⟩,⟨state217_45,exclude217_45⟩] 0x1000416060581820404d09034242000434240d0902040458181606200031606058184000cd09034242000234240d0904000c581816060d09004404d09030200504030200d09014100c09030200110130241000414100504020405000420405000840012000120404504014101000814100504040008110104405000804404110140008504014100581826240989034240484034240581812100484034240989026241000822200888014100989026241000526240989014100888022241000412100484020404989026241000526240989020404484012101000512100484040000989026241000526240989040000484012101000440004c04010404919024640d09040004d09010406000010404d090246409190044048180206005040246409190044049190246405040206008190024049190246409890400049890024050005024049890246409190204050004204050001246409190400110004046410004400104140 (by decide +kernel)

def state217_47 : List Sig := [0x5555555555555555550055005500550055555555555555555500550055005500,input 0,input 3,input 6,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude217_47 : Impossible true (goalAt 217) 5 state217_47.toFinset :=
  node_ok cuts217 [⟨state217_1,exclude217_1⟩] 0x504030100881814100581814100504012060c04026060c04016060484030100981812100484014102000012100581812100484014060111024640919030100818024640919020640919034640410124640919026640090124640c04020404c04020404504004404504004404d090342405818104049890262404840024044140 (by decide +kernel)

def state217_48 : List Sig := [0xffffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00,input 3,input 6,input 0,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude217_48 : Impossible true (goalAt 217) 6 state217_48.toFinset :=
  node_ok cuts217 [⟨state217_3,exclude217_3⟩,⟨state217_22,exclude217_22⟩,⟨state217_26,exclude217_26⟩,⟨state217_41,exclude217_41⟩,⟨state217_47,exclude217_47⟩] 0x981814100504030101000530100981840014881830100504014100581804404581812020504014100581814100504012020110112061000604404110140008504014101000614100504040008110104404810110500414030100919024640810124640919030100414010500110120600818014100919024640110124640919014100818020641000324640919016060414010502000310500414016060919024641000024640919012100191812102000206460191812100919024642000424640919040004414010502000110500414040004919024640c04016060c04026061000326060c04040014c04026060581816061000040000d09026060484012100c04040000c04026061000526060c0401210048404000048401210050404000050404000100068000050401210048401606100031606100001210048404000100001406100004000c9890301010004301008101400148101301010005301008101400108101 (by decide +kernel)

def state217_49 : List Sig := [0x5555555555555555555555555555555555555555555555550000000000000000,input 0,input 6,input 7,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude217_49 : Impossible true (goalAt 217) 5 state217_49.toFinset :=
  node_ok cuts217 [⟨state217_14,exclude217_14⟩] 0x504030102000014100d09030200c09030240888026240989022240484026240989012100989034240484026240c04034240d09014240090814100191814100111026240191826240191830100810130100191834240410134240504004404504004404989002404989002404c04026060c04020404d09016060d090104049190 (by decide +kernel)

def state217_50 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,input 7,input 0,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude217_50 : Impossible true (goalAt 217) 6 state217_50.toFinset :=
  node_ok cuts217 [⟨state217_35,exclude217_35⟩,⟨state217_39,exclude217_39⟩,⟨state217_45,exclude217_45⟩,⟨state217_16,exclude217_16⟩,⟨state217_49,exclude217_49⟩] 0x1000414100504030101000430101000840012000330100504014100d09004404d09030200504030200d09014100c0903020011013024100080440411014000850401410100081410050404000811010440500082220088801410098902624100052624098901410088802224100041210048403010098902624100052624098903010048401210100032624098903424048403424100051210048403424098902624100050240409014000098902624100052624098904000009010240411012060081801410091902464011012464091901410081802064009012464091902624019182624009010646019182624091902464100041050041403010091902464200022464091903010041401050100032464091903424041403424200011050041403424091902464200040646019184000491902464200002464091904000419180646100044000c981830101000430101000334240d090400110004142410004400105818 (by decide +kernel)

def state217_51 : List Sig := roots 217
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude217_51 : Impossible true (goalAt 217) 7 state217_51.toFinset :=
  node_ok cuts217 [⟨state217_9,exclude217_9⟩,⟨state217_19,exclude217_19⟩,⟨state217_27,exclude217_27⟩,⟨state217_43,exclude217_43⟩,⟨state217_46,exclude217_46⟩,⟨state217_48,exclude217_48⟩,⟨state217_50,exclude217_50⟩] 0x40010c04016060c0404000c981834240d09080018c04034240d09040010981816060509040008981814100504040008c04040008c04040008981880004881840008c04014100504040008d09004404d09040008c08014100c08040008d09014100c09040008c08004404c09040010981812100484040000c04026240989040014981826240989040000c0401210048404000c581826240989040000d09012100d09080014581812100484040000d0902624098904000900022220088804000850402624098904000a000026240989040008504022200889040010810110500414040004c04024640919080010810124640919040010c0401050041404000c410124640919040004d09010500d0908000c410110500414040004d090246409190400081101206008180400085040246409190400081101246409190400085040206008190400000901246409190400049890064609890800080901064601918400009890246409190 (by decide +kernel)

theorem lower217 : Claim 217 8 :=
  fromSearch 3 (by decide +kernel) exclude217_51

theorem lower219 : Claim 219 9 :=
  fromLift 9 2 67 lower217 (by decide +kernel)

theorem lower163 : Claim 163 5 :=
  fromLift 5 1 85 lower162 (by decide +kernel)

theorem lower139 : Claim 139 5 :=
  fromLift 5 2 115 lower137 (by decide +kernel)

def rule171_0 : {c : Cut // CutGood (goalAt 171) c} :=
  ruleFor 171 lower169 none (by decide +kernel)

def rule171_1 : {c : Cut // CutGood (goalAt 171) c} :=
  ruleFor 171 lower163 none (by decide +kernel)

def rule171_2 : {c : Cut // CutGood (goalAt 171) c} :=
  ruleFor 171 lower162 none (by decide +kernel)

def rule171_3 : {c : Cut // CutGood (goalAt 171) c} :=
  ruleFor 171 lower170 none (by decide +kernel)

def rule171_4 : {c : Cut // CutGood (goalAt 171) c} :=
  ruleFor 171 lower139 none (by decide +kernel)

def rule171_5 : {c : Cut // CutGood (goalAt 171) c} :=
  ruleFor 171 lower43 none (by decide +kernel)

def rule171_6 : {c : Cut // CutGood (goalAt 171) c} :=
  ruleFor 171 lower168 none (by decide +kernel)

def rule171_7 : {c : Cut // CutGood (goalAt 171) c} :=
  ruleFor 171 lower41 none (by decide +kernel)

def rule171_8 : {c : Cut // CutGood (goalAt 171) c} :=
  ruleFor 171 lower137 none (by decide +kernel)

def rule171_9 : {c : Cut // CutGood (goalAt 171) c} :=
  ruleFor 171 lower161 none (by decide +kernel)

def cuts171 : Cuts (goalAt 171) := [rule171_0,rule171_1,rule171_2,rule171_3,rule171_4,rule171_5,rule171_6,rule171_7,rule171_8,rule171_9]

def state171_0 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffaaaaaaaaffffffffaaaaaaaa,input 7,input 5,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude171_0 : Impossible true (goalAt 171) 4 state171_0.toFinset :=
  node_ok cuts171 [] 0x22200a0800a08088800a080888022200282002c2888802220100022060088800240c818020600a08008480818008480818020600212002c28818020601000028080a0802820021030a428890a (by decide +kernel)

def state171_1 : List Sig := [0xffffffffaaaaaaaaffffffffaaaaaaaa,input 7,input 5,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude171_1 : Impossible true (goalAt 171) 4 state171_1.toFinset :=
  node_ok cuts171 [] 0x88802820028202220028202220088800a080818022200090320600818028200212020600212020600818008480a90a28200a080224282820222002820222002120206002120206000b0a28200210328200a020 (by decide +kernel)

def state171_2 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 7,0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude171_2 : Impossible true (goalAt 171) 4 state171_2.toFinset :=
  node_ok cuts171 [] 0x88802820028202220028202220088800a08009032220088800240c828022200090320a00818020600212020a00212020a00828008480210320a00828040018a02028200a08002c280b0a28200a08002c288a0a (by decide +kernel)

def state171_3 : List Sig := [0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,input 5,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 3,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude171_3 : Impossible true (goalAt 171) 5 state171_3.toFinset :=
  node_ok cuts171 [⟨state171_0,exclude171_0⟩,⟨state171_1,exclude171_1⟩,⟨state171_2,exclude171_2⟩] 0x8a0a0a0802820280808880222008a0a2220088802808028200a08100022220088800840c28200a08100020a08028200840c8880222000b0a2220088804000828200a0800b0a0a0802820400088880222008a0a08480212028080828020a008a0a20a00828028080212008480090320a00828022201000622200090340008090322200828020a00210320a00828040018212008480210308480212040018828020a000b0a20a008180400002120206000b0a08480212040000828020a00a0200840ca02022829000822828a02080008a0202282821032282900034000ca080280800b0a280808a0a80004890a280820000280808a0a02c280b0a (by decide +kernel)

def state171_4 : List Sig := [0xffffffff00000000ffffffff00000000aaaaaaaa00000000aaaaaaaa,input 5,input 7,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude171_4 : Impossible true (goalAt 171) 4 state171_4.toFinset :=
  node_ok cuts171 [] 0x28202220088800a08088800a080282022200818022200090320600212020600818008480818008480212020600a0202a428a0200a42888800a08088800a0808180084808180084800b0a28080810328080a080 (by decide +kernel)

def state171_5 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude171_5 : Impossible true (goalAt 171) 4 state171_5.toFinset :=
  node_ok cuts171 [] 0x28202220088800a08088802820028202220009032220088800240c8180222000903206002120206008180088808180282002220206008103206008180400180b0a28080a02002c28a02028200a08002c282a0a (by decide +kernel)

def state171_6 : List Sig := [0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 7,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 3,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude171_6 : Impossible true (goalAt 171) 5 state171_6.toFinset :=
  node_ok cuts171 [⟨state171_0,exclude171_0⟩,⟨state171_4,exclude171_4⟩,⟨state171_5,exclude171_5⟩] 0x100070a8282a0a2040ca08028202000228200a0802040c2a0a0a82a00010a828290a02c28a08028202000028200a08002c282a0a02c282a0a222008880282002820282002a0a0a08028202820088802220100020a08028202040c88802220100022220088802040c28200a0800b0a0a0802820400088880222000b0a2220088804000828200a0802a0a206008180282002220282002a0a088802220282008180206000903206008180222010006222000903400080903222008180206008103088802220400188180206008103206008180400182220088800b0a088802120400008180206000b0a2060081804000022200888100034000ca020 (by decide +kernel)

def state171_7 : List Sig := [0x1111111111111111111111111111111111111111000000001111111100000000,input 5,input 7,input 0,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude171_7 : Impossible true (goalAt 171) 4 state171_7.toFinset :=
  node_ok cuts171 [] 0x28202220088800a0808880282002820222000903222000b0a222000b0a280808103280800b0a28200210328200a02028200a0800a82882800240c888020a00818008880828020a00222020a002220282008280 (by decide +kernel)

def state171_8 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,input 7,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 0,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude171_8 : Impossible true (goalAt 171) 5 state171_8.toFinset :=
  node_ok cuts171 [⟨state171_0,exclude171_0⟩,⟨state171_2,exclude171_2⟩,⟨state171_5,exclude171_5⟩,⟨state171_7,exclude171_7⟩] 0xa080888022200282022200a0800a08088800240c88802220009030240c888002c288880206000b0a280820002280800b0a282020001282000b0a4000e000002c28828022200090320a00222020a00828008880828028200222020a02000320a008280400188a0a28080a0804001c2a0a (by decide +kernel)

def state171_9 : List Sig := [0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 0,input 3,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude171_9 : Impossible true (goalAt 171) 6 state171_9.toFinset :=
  node_ok cuts171 [⟨state171_3,exclude171_3⟩,⟨state171_6,exclude171_6⟩,⟨state171_8,exclude171_8⟩] 0x4001ca0200a828a020400208a0a28200a08080008a02028200a0804001c8a0a0a8282a0a400088a0a0a080282040008a020222008880400088a0a22200888040008a0200a0802820400082a0a22200888040008a0800a080a080400082a0a0a080282040008a0802220088804000c810302c280b0a4000ca0204000ca0204000c81038000481034000ca02002c28a0204000c210302c280b0a4000ca0804000ca0804000c21038000021034000ca08002c28a0804000c09034000809034000c888002c2888804000c090302c280b0a4000c88804000c8880400010000400008180400188a0a08880222040018a02020a008280400188a0a20a00828040018a020088802220400182a0a20a00828040018a08008880a080400182a0a08880222040018a08020a00828040018090320a00828040018888040018888040018090340008090340018888020a008280 (by decide +kernel)

def state171_10 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffff00ff00ffffffffff00ff00,input 7,input 5,0xffccffccffccffccffccffccffccffccffccffccffccffccffccffccffccffcc,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude171_10 : Impossible true (goalAt 171) 4 state171_10.toFinset :=
  node_ok cuts171 [] 0x20600828002c28818020600a0800848081800848081802060021200240c818020601000620a00a08008880828008880828020a0022200240c828020a01000028080a08028200220a08c0c8303 (by decide +kernel)

def state171_11 : List Sig := [0xffffffffff00ff00ffffffffff00ff00,input 7,input 5,0xffccffccffccffccffccffccffccffccffccffccffccffccffccffccffccffcc,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude171_11 : Impossible true (goalAt 171) 4 state171_11.toFinset :=
  node_ok cuts171 [] 0x818020a000b0a20600818028200212020600212020600818008480828028200222020a00222020a00828008880220a28200a08008828212020600212020600222020a00222020a00220a28200220a28200a020 (by decide +kernel)

def state171_12 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 7,0xffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00,0xffccffccffccffccffccffccffccffccffccffccffccffccffccffccffccffcc,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude171_12 : Impossible true (goalAt 171) 4 state171_12.toFinset :=
  node_ok cuts171 [] 0x818020a000b0a206008180282002120206002120206008180084800b0a20600818002c28828022200222020a00222020a00828008880220a20a00828040024a02028200a0800240c220a28200a0800240c880a (by decide +kernel)

def state171_13 : List Sig := [0xffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00,input 5,0xffccffccffccffccffccffccffccffccffccffccffccffccffccffccffccffcc,input 0,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude171_13 : Impossible true (goalAt 171) 5 state171_13.toFinset :=
  node_ok cuts171 [⟨state171_10,exclude171_10⟩,⟨state171_11,exclude171_11⟩,⟨state171_12,exclude171_12⟩] 0x830308480212028080818020600830320600818028080212008481000220600818020a000b0a20a01000202c280b0a20a00818020601000220600818008828212008481000208480212008828818020600090320600818040018212008480090308480212040018818020600880a08880222028080828020a00880a20a00828028080222008880220a20a00828040024222008880220a08880222040024828020a00090320a00828040000222022200090308880222040000828020a00a02008828a02022029000822028a02080008a02022028220a08829000140004a0802808009032808083038000483032808200002808083030240c820a (by decide +kernel)

def state171_14 : List Sig := [0xffffffff00000000ffffffff00000000ff00ff0000000000ff00ff00,input 5,input 7,0xffccffccffccffccffccffccffccffccffccffccffccffccffccffccffccffcc,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude171_14 : Impossible true (goalAt 171) 4 state171_14.toFinset :=
  node_ok cuts171 [] 0x818020a000b0a20600212020600818008480818008480212020600222020a00828008880828008880222020a00a02020828a02020828818008480818008480828008880828008880820a28080820a28080a080 (by decide +kernel)

def state171_15 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,0xffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00,0xffccffccffccffccffccffccffccffccffccffccffccffccffccffccffccffcc,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude171_15 : Impossible true (goalAt 171) 4 state171_15.toFinset :=
  node_ok cuts171 [] 0x818020a000b0a206002120206008180084808180282002120206000b0a20600818002c28222020a00828008880828028200222020a00820a20a00828040024820a28080a0200240ca02028200a0800240c280a (by decide +kernel)

def state171_16 : List Sig := [0xffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00,input 7,0xffccffccffccffccffccffccffccffccffccffccffccffccffccffccffccffcc,input 0,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude171_16 : Impossible true (goalAt 171) 5 state171_16.toFinset :=
  node_ok cuts171 [⟨state171_10,exclude171_10⟩,⟨state171_14,exclude171_14⟩,⟨state171_15,exclude171_15⟩] 0x100070a028280a20828a08028202000228200a08020828280a0a02a000108c0c23030240ca08028202000028200a0800240c230308828230320600818028200212028200230308480212028200818020601000220600818020a000b0a20a01000202c280b0a20a00818020601000208480212020828818020601000220600818020828212008480090308480212040018818020600090320600818040018212008480280a20a00828028200222028200280a08880222028200828020a00820a08880222040024828020a00820a20a00828040024222008880090308880222040000828020a00090320a00828040000222008881000140004a020 (by decide +kernel)

def state171_17 : List Sig := [0x33003300330033003300330033003300330033000000000033003300000000,input 5,input 7,input 3,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude171_17 : Impossible true (goalAt 171) 4 state171_17.toFinset :=
  node_ok cuts171 [] 0x818002c280b0a20600212020600818008480818028200212020600880a28080820a28080280a28200220a28200a02028200a0800a028818002c28818020a00888008880828020a00222020a002220282008280 (by decide +kernel)

def state171_18 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,input 7,0xffccffccffccffccffccffccffccffccffccffccffccffccffccffccffccffcc,input 3,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude171_18 : Impossible true (goalAt 171) 5 state171_18.toFinset :=
  node_ok cuts171 [⟨state171_10,exclude171_10⟩,⟨state171_12,exclude171_12⟩,⟨state171_15,exclude171_15⟩,⟨state171_17,exclude171_17⟩] 0x206000b0a02c28818020600828002c28818008480818020600212020600a08008480818002c288180206000b0a2220009032808200022808009032820200012820009034000600000240c222020a00828008880828028200222020a02000320a00828040024880a28080a0804001c280a (by decide +kernel)

def state171_19 : List Sig := [0xffccffccffccffccffccffccffccffccffccffccffccffccffccffccffccffcc,input 3,input 0,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude171_19 : Impossible true (goalAt 171) 6 state171_19.toFinset :=
  node_ok cuts171 [⟨state171_13,exclude171_13⟩,⟨state171_16,exclude171_16⟩,⟨state171_18,exclude171_18⟩] 0x4001ca0200a028a02040020880a28200a08080008a02028200a0804001c880a0a028280a40008830308480212040018a02020600818040008830320600818040018a02008480212040008230320600818040018a08008480a08040008230308480212040018a08020600818040004090320600818040005000602c280b0a40004090302c280b0a40005000120600818040009000220600818040018828002c28828040009000202c280b0a40018828020600818040004880a0240c880a40004a02040004a02040004880a80004820a40004a0200240ca02040004280a0240c280a40004a08040004a08040004280a80000220a40004a0800240ca08040001000040000888040024880a08880222040024a02020a00828040024880a20a00828040024a02008880222040024280a20a00828040024a08008880a08040024280a08880222040024a08020a008280 (by decide +kernel)

def state171_20 : List Sig := [0x3333333333333333333333333333333333333333222222223333333322222222,input 7,input 0,input 5,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude171_20 : Impossible true (goalAt 171) 4 state171_20.toFinset :=
  node_ok cuts171 [] 0x22200a0800a08088800a080888022200282028080a080282002a0a20600888002c28818020600a08008480818008480818020600212020a00090322200828020a002220282008280206000b0a20600828008880828020a002220 (by decide +kernel)

def state171_21 : List Sig := [0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00aa00aa00ff00ff00aa00aa,input 7,input 0,input 5,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude171_21 : Impossible true (goalAt 171) 4 state171_21.toFinset :=
  node_ok cuts171 [] 0x20a00a08008880828008880828020a00222028080a080282002a0a20600828002c28818020600a08008480818008480818020600212020a00090320a008880222002820282008880206000b0a2060088800a0808880222002820 (by decide +kernel)

def state171_22 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffaaaaaaaaffffffffaaaaaaaa,input 7,input 0,input 5,input 1,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude171_22 : Impossible true (goalAt 171) 5 state171_22.toFinset :=
  node_ok cuts171 [⟨state171_0,exclude171_0⟩,⟨state171_20,exclude171_20⟩,⟨state171_21,exclude171_21⟩] 0x88802820028202220028202220088800a082000222200888040004828022200090320a00828028200222020a00222020a00828008882000120a00828040000a02028200a08008c0c2a0a20600888002c0c818020600828080000818020600a08008480818008480818020600212002c288a0a (by decide +kernel)

def state171_23 : List Sig := [0xffffffffaaaaaaaaffffffffaaaaaaaa,input 7,input 0,input 5,input 1,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude171_23 : Impossible true (goalAt 171) 5 state171_23.toFinset :=
  node_ok cuts171 [⟨state171_1,exclude171_1⟩] 0x88802820028202220028202220088800a080828022200090320a00828028200222020a00222020a00828008880aa0a28200a080228288180222000b0320600818020a02000020600818028200212020600212020600818008480282022200282022200222020a00222020a002a0a28200230328200212020600212020600a020 (by decide +kernel)

def state171_24 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,input 1,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude171_24 : Impossible true (goalAt 171) 4 state171_24.toFinset :=
  node_ok cuts171 [] 0x2220081800a08081800a080888022200212002c0c8880222000b0320a0088800240c828020a00818008880818008880828020a00212008c0c828020a0021030848081802060100040a8288180206008203228282120084802203 (by decide +kernel)

def state171_25 : List Sig := [0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 7,0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,input 5,input 1,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude171_25 : Impossible true (goalAt 171) 5 state171_25.toFinset :=
  node_ok cuts171 [⟨state171_24,exclude171_24⟩] 0x2220028200a08088802220081800a08081800a08088802220028200a080888022200212020a0088800240c828020a00222008880828020a00818008880818008880828020a00222008880828020a00212028200230320c0e000008c0c212008c0c21200880c83032060081802080c212020600818040010a020 (by decide +kernel)

def state171_26 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 7,0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,input 0,input 1,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude171_26 : Impossible true (goalAt 171) 5 state171_26.toFinset :=
  node_ok cuts171 [⟨state171_24,exclude171_24⟩,⟨state171_2,exclude171_2⟩] 0x22200a0800a08088800a080888022200282002c0c8880222000b0320a0088800240c828020a00a08008880828008880828020a00222008c0c828020a00210308480888002c0c88800848082808000482802060021202048200000848023030848021200880ca02028200a080400142a0a28200a0804000c8a0a (by decide +kernel)

def state171_27 : List Sig := [0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,input 0,input 5,input 1,input 3,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude171_27 : Impossible true (goalAt 171) 6 state171_27.toFinset :=
  node_ok cuts171 [⟨state171_3,exclude171_3⟩,⟨state171_22,exclude171_22⟩,⟨state171_23,exclude171_23⟩,⟨state171_25,exclude171_25⟩,⟨state171_26,exclude171_26⟩] 0x8a0a0a0802820280808880222008a0a2220088802808028200a081000422200888008c0c28200a08100020a080282008c0c88802220100022220088804000428200a08100020a0802820400048880222008a0a08880222028080828020a008a0a20a008280280802220088800b0320a008280222010006222000b0340008090322200828020a00230320a00828008404222008880230308880222008404828020a01000620a00828040000222008881000608880222040000828020a00a02008c0ca02022829000422828a02080010a0202282823032282900044000ca08020c0c212008480a0204000ca02020c0e000320c0ca02008480212002c0c21200848088804000c888002c0d000202c0c88800848088804000c21200848082804000c82804000d000680000828008480828008c0d000408c0d00030848021204001100040880d0004400108180280810005280808a0a800088a0a280820001280808a0a400148a0a (by decide +kernel)

def state171_28 : List Sig := [0xffffffff00000000ffffffff00000000aaaaaaaa00000000aaaaaaaa,input 5,input 0,input 7,input 1,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude171_28 : Impossible true (goalAt 171) 5 state171_28.toFinset :=
  node_ok cuts171 [⟨state171_4,exclude171_4⟩] 0x28202220088800a08088800a080282022200828022200090320a00222020a00828008880828008880222020a008180222000b0320600818020a02000020600212020600818008480818008480212020600a0202a828a0200a82888800a08088800a0808280088808280088808a0a28080830328080818008480818008480a080 (by decide +kernel)

def state171_29 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 0,input 1,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude171_29 : Impossible true (goalAt 171) 5 state171_29.toFinset :=
  node_ok cuts171 [⟨state171_24,exclude171_24⟩,⟨state171_5,exclude171_5⟩] 0xa080888022200282022200a0800a080888002c0c8880222000b0320a0088800240c828008880828020a00222020a00a08008880828020c0c828020a00810320600888002c0c81802060082808000481800848081802820200002060083032060081802080c8a0a28080a02040010a02028200a080400102a0a (by decide +kernel)

def state171_30 : List Sig := [0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 0,input 7,input 1,input 3,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude171_30 : Impossible true (goalAt 171) 6 state171_30.toFinset :=
  node_ok cuts171 [⟨state171_6,exclude171_6⟩,⟨state171_25,exclude171_25⟩,⟨state171_22,exclude171_22⟩,⟨state171_28,exclude171_28⟩,⟨state171_29,exclude171_29⟩] 0x100050a8282a0a20c0ca08028202000428200a08020c0c2a0a0a82a00030a8282a0a40010a08028202000228200a080400102a0a0a8282a0a222008880282002820282002a0a0a08028202820088802220100050a080282020c0c888022201000222200888020c0c28200a08100020a08028204000488802220100022220088804000428200a0802a0a20a008280282002220282002a0a08880222028200828020a000b0320a008280222010006222000b0340008090322200828020a00830308880222020404828020a00830320a00828020404222008881000608880222040000828020a01000620a0082804000022200888100034000ca02008c0c818020600a0804000ca08008c0e000108c0ca08020600818002c0c81802060088804000c888002c0d000202c0c88802060081804000c81802060082804000c82804000d000680000828020600818020c0d000520c0d00032060081804000d00032080d0003400142120 (by decide +kernel)

def state171_31 : List Sig := [0x5555555555555555555555555555555555555555550055005555555555005500,input 7,input 3,input 5,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude171_31 : Impossible true (goalAt 171) 4 state171_31.toFinset :=
  node_ok cuts171 [] 0x20a00a08008880828020a0088800240c828008880828020a00222028080a080282002a0a22200a0800a08088800a0808880222002820206000b0a20a008180206002120282008180206000b0a222008180084808180206002120 (by decide +kernel)

def state171_32 : List Sig := [0x3333333333333333333333333333333333333333330033003333333333003300,input 7,input 3,input 5,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude171_32 : Impossible true (goalAt 171) 4 state171_32.toFinset :=
  node_ok cuts171 [] 0x20600a08008480818020600888002c28818008480818020600212028080a080282002a0a22200a0800a08088800a0808880222002820206000b0a20600828020a00222028200828020a00090322200828008880828020a002220 (by decide +kernel)

def state171_33 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffff00ff00ffffffffff00ff00,input 7,input 3,input 5,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude171_33 : Impossible true (goalAt 171) 5 state171_33.toFinset :=
  node_ok cuts171 [⟨state171_10,exclude171_10⟩,⟨state171_31,exclude171_31⟩,⟨state171_32,exclude171_32⟩] 0x828028200222020a00828022202000020a00222020a00828008882000220a00828040000818020a000b0a206008180282002120206008180222000b0a2060021202060081800848200012060081804000ca02028200a0800a828230322200a0800a08088800a080888022200282002c0c8303 (by decide +kernel)

def state171_34 : List Sig := [0xffffffffff00ff00ffffffffff00ff00,input 7,input 3,input 5,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude171_34 : Impossible true (goalAt 171) 5 state171_34.toFinset :=
  node_ok cuts171 [⟨state171_11,exclude171_11⟩] 0x828028200222020a00828022202000020a00222020a00828008880818020a000b0a206008180282002120206008180222000b0a206002120206008180084802a0a28200a0800a82888802820028202220028202220088800a080222020a00222020a002120206002120206002a0a282002a0a28200282022200282022200a020 (by decide +kernel)

def state171_35 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,0xffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude171_35 : Impossible true (goalAt 171) 4 state171_35.toFinset :=
  node_ok cuts171 [] 0x20a00888008880828008880828020a0022200a828828020a00280a20600828002c28818020600888008480818008480818020600212002c288180206000b0a0a08088802220100040a828888022200820a0a82828200a080220a (by decide +kernel)

def state171_36 : List Sig := [0xffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00,input 7,0xffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00,input 5,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude171_36 : Impossible true (goalAt 171) 5 state171_36.toFinset :=
  node_ok cuts171 [⟨state171_35,exclude171_35⟩] 0x20a00222008880828020a00888008880828008880828020a00222008880828020a00222020600828002c288180206002120084808180206008880084808180084808180206002120084808180206002120282002a0a2282a00000a82828200a8282820088288a0a22200888020828282022200888040010a020 (by decide +kernel)

def state171_37 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 7,0xffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00,input 3,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude171_37 : Impossible true (goalAt 171) 5 state171_37.toFinset :=
  node_ok cuts171 [⟨state171_35,exclude171_35⟩,⟨state171_12,exclude171_12⟩] 0x20a00282080004828020a00a08008880828008880828020a0022200a828828020a00280a20600828002c28818020600282002c28818020600a08008480818008480818020600212002c288180206000b0a2220028202208200000a0802a0a0a080282008828a02028200a080400142a0a28200a080400048a0a (by decide +kernel)

def state171_38 : List Sig := [0xffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00,input 3,input 5,input 0,input 1,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude171_38 : Impossible true (goalAt 171) 6 state171_38.toFinset :=
  node_ok cuts171 [⟨state171_13,exclude171_13⟩,⟨state171_33,exclude171_33⟩,⟨state171_34,exclude171_34⟩,⟨state171_36,exclude171_36⟩,⟨state171_37,exclude171_37⟩] 0x8a0a08880222028080828020a008a0a20a008280280802220088802a0a20a0082800a0202220088802a0a0888022200a020828020a01000120a0082800a08100010a08100094000600000a080828020a01000920a00828040000222008881000908880222040000828020a00830308480212028080818020600830320600818028080212008481000220600818020a000b0a20a01000202c280b0a20a0081802060100042060081800a82821200848100020848021200a82881802060100012060081800a0800b0a0a081000202c280b0a0a08081802060100022060081804000c21200848100020848021204000c818020600a0200a828a02022829000422828a02080010a020228282a0a0a829000140004a0802282828200a080a02040004a0202282a000322828a0200a08028200a82900040a82900010a0802820400050001088290001400108880280810005280808303800088303280820001280808303400148303 (by decide +kernel)

def state171_39 : List Sig := [0xffffffff00000000ffffffff00000000ff00ff0000000000ff00ff00,input 5,input 3,input 7,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude171_39 : Impossible true (goalAt 171) 5 state171_39.toFinset :=
  node_ok cuts171 [⟨state171_14,exclude171_14⟩] 0x222020a00828008880828022202000020a00828008880222020a00818020a000b0a206002120206008180084808180222000b0a2060081800848021202060028202220088800a08088800a080282022200a02022828a020228288280088808280088808180084808180084808a0a280808a0a2808088800a08088800a080a080 (by decide +kernel)

def state171_40 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,0xffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00,input 3,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude171_40 : Impossible true (goalAt 171) 5 state171_40.toFinset :=
  node_ok cuts171 [⟨state171_35,exclude171_35⟩,⟨state171_15,exclude171_15⟩] 0x20a00888080004828008880828020a00222020a00a08008880828022828828020a00880a20600828002c28818020600888002c28818008480818020600212020600a08008480818002c288180206000b0a0a0808880282020000222008a0a222008880208288a0a28080a02040004a02028200a080400102a0a (by decide +kernel)

def state171_41 : List Sig := [0xffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00,input 3,input 7,input 0,input 1,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude171_41 : Impossible true (goalAt 171) 6 state171_41.toFinset :=
  node_ok cuts171 [⟨state171_36,exclude171_36⟩,⟨state171_16,exclude171_16⟩,⟨state171_33,exclude171_33⟩,⟨state171_39,exclude171_39⟩,⟨state171_40,exclude171_40⟩] 0x100050a8282a0a22828a08028202000428200a080228282a0a0a82a000308c0c230340010a08028202000228200a08040010230308c0c2a0a20a008280282002220282002a0a08880222028200828020a008a0a08880222022020828020a008a0a20a00828022020222008881000120a00828022201000122201000940006000122200828020a01000908880222040000828020a01000920a00828040000222008880230320600818028200212028200230308480212028200818020601000220600818020a000b0a20a01000202c280b0a20a008180206010005084802120228288180206010002206008180228282120084810001206008180222000b0a22201000202c280b0a2220081802060100020848021204000c81802060100022060081804000c212008481000140004a0200a828888022200a08040004a0800a82a00000a828a080222008880228290005228290001222008880400050001208290001400142820 (by decide +kernel)

def state171_42 : List Sig := [0xbb00bb00bb00bb00bb00bb00bb00bb00bb00bb00aa00aa00bb00bb00aa00aa,input 0,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude171_42 : Impossible true (goalAt 171) 3 state171_42.toFinset :=
  node_ok cuts171 [] 0x28080a08028200220a08480818020600212020600a08008480818008880828020a00222020a002220282008280206000b0a206008280 (by decide +kernel)

def state171_43 : List Sig := [0xbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbaaaaaaaabbbbbbbbaaaaaaaa,input 0,input 5,input 7,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude171_43 : Impossible true (goalAt 171) 4 state171_43.toFinset :=
  node_ok cuts171 [⟨state171_42,exclude171_42⟩] 0x28202220088800a080888028200282022200a02028200a0800a8288180222000903206002120206008180084808180282002120206000b0a20a02000022200828008880828020a00222020a002220282008280 (by decide +kernel)

def state171_44 : List Sig := [0x5511551155115511551155115511551155115511550055005511551155005500,input 3,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude171_44 : Impossible true (goalAt 171) 3 state171_44.toFinset :=
  node_ok cuts171 [] 0x28080a08028200280a0a080888022200282022200a0800a0808880084808180206002120206002120282008180206000b0a222008180 (by decide +kernel)

def state171_45 : List Sig := [0xff33ff33ff33ff33ff33ff33ff33ff33ff33ff33ff00ff00ff33ff33ff00ff00,input 3,input 5,input 7,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude171_45 : Impossible true (goalAt 171) 4 state171_45.toFinset :=
  node_ok cuts171 [⟨state171_44,exclude171_44⟩] 0x2120206008180084808180282002120206008180222000b0a20602000020600818020a00a02028200a0800a02828202220088800a080888028200282022200090308880828020a00222020a002220282008280 (by decide +kernel)

def state171_46 : List Sig := [0x3333333333333333333333333333333333333333000000003333333300000000,input 5,input 7,input 0,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude171_46 : Impossible true (goalAt 171) 5 state171_46.toFinset :=
  node_ok cuts171 [⟨state171_7,exclude171_7⟩,⟨state171_17,exclude171_17⟩,⟨state171_43,exclude171_43⟩,⟨state171_45,exclude171_45⟩] 0x2282828200a080a02022200888022828888022200a0200a08028200a828888022200a0800a080a0800a82828200a080a0802220088800240c818020600888002c2888800240c0b0a02c28888020600818020c0c212008480a02020600818020c0c818020600a02008480212008c0c818020600a08008480a08008c0c212008480a080206008180280802a0a280808a0a28200a08028080a080282008a0a0a8282a0a22200828020a00090380004090322202000322200090320a008280206008280206000b0a800000b0a206020002206000b0a20a008280280802220088808a0a20a00828028080828020a008a0a08880222028200828020a002a0a088802220282002220282002a0a20a008280 (by decide +kernel)

def state171_47 : List Sig := [0x5555555555555555555555555555555555555555000000005555555500000000,input 0,input 5,input 7,input 1,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude171_47 : Impossible true (goalAt 171) 5 state171_47.toFinset :=
  node_ok cuts171 [⟨state171_7,exclude171_7⟩] 0x28202220088800a080888028200282022200828022200090320a00222020a00828008880828028200222020a00a02028200a08008c0c0b03222000b0a22200090820a000b0a20a000b0a280808303280800b0a28200230328200888002c0c888002c0c828080000828040000a02022828a02020c0ca0800a828a08008c0c8180 (by decide +kernel)

def state171_48 : List Sig := [0x3333333333333333333333333333333333333333000000003333333300000000,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,input 7,input 0,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude171_48 : Impossible true (goalAt 171) 5 state171_48.toFinset :=
  node_ok cuts171 [] 0xa080888022200282022200a0800a08088800240c888022200090320600888002c28818008480818020600212020600a08008480818002c288180206000b0a22828a0202820100070a82882800240c888020a00818002c28818020a00222020a00828008880828008880a08020a010000 (by decide +kernel)

def state171_49 : List Sig := [0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000ff00ff00000000,input 3,input 5,input 7,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude171_49 : Impossible true (goalAt 171) 5 state171_49.toFinset :=
  node_ok cuts171 [⟨state171_17,exclude171_17⟩] 0x222020a00828008880828028200222020a00828002404090320a00818020a000b0a20600212020600818008480818028200212020600818002c280b0a20600a02028200a0800a8288a0a280808a0a280802a0a282002a0a28200828080000828040000818002c28818002c28a02022828a02022828a0800a828a0800a8288880 (by decide +kernel)

def state171_50 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,input 7,input 0,input 1,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude171_50 : Impossible true (goalAt 171) 6 state171_50.toFinset :=
  node_ok cuts171 [⟨state171_22,exclude171_22⟩,⟨state171_26,exclude171_26⟩,⟨state171_29,exclude171_29⟩,⟨state171_8,exclude171_8⟩,⟨state171_18,exclude171_18⟩,⟨state171_33,exclude171_33⟩,⟨state171_37,exclude171_37⟩,⟨state171_40,exclude171_40⟩,⟨state171_46,exclude171_46⟩,⟨state171_47,exclude171_47⟩,⟨state171_48,exclude171_48⟩,⟨state171_49,exclude171_49⟩] 0x100050a08028202808088802220200072220088802808028200a08100042220088802820028202820200060a080282028200888022202000b02c0c0b03400048880222020005222008880400040b0302c0c0b0320a008280222010007222000b0380010090322200828020a01000508880222028080828020a01000720a00828028080222008881000420a00828028200222028201000708880222028200828020a0100078002a000840000828020a01000720a008280400010007400000b03206008180222000b0a222000b0302c280b0a22200818020601000720600818020a000b0a20a02000302c280b0a20a00818020601000508480212028080818020602000220600818028080212008481000420600818028200212028202000108480212028200818020602000902c280b0a4000c81802060200002060081804000c0b0a02c290004400108a0a28081000528081000428200a080400110004400110004400142a0a (by decide +kernel)

def state171_51 : List Sig := roots 171
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude171_51 : Impossible true (goalAt 171) 7 state171_51.toFinset :=
  node_ok cuts171 [⟨state171_9,exclude171_9⟩,⟨state171_19,exclude171_19⟩,⟨state171_27,exclude171_27⟩,⟨state171_30,exclude171_30⟩,⟨state171_38,exclude171_38⟩,⟨state171_41,exclude171_41⟩,⟨state171_50,exclude171_50⟩] 0x40014a0200a828a020400108a0a28200a08080018a02028200a080400108a0a0a8282a0a400148a0a0a080282040004a020222008880800148a0a22200888040004a0200a0802820400102a0a22200888040004a0800a080a080800102a0a0a080282040004a080222008880400008a0a08880222040000a02020a008280400008a0a20a00828040000a020088802220400002a0a20a00828040000a08008880a080400002a0a08880222040000a08020a008280400000b0320a008280400008880400008880400000b0380004090340000888020a0082804001483030848021204000ca0202060081808000c83032060081804000ca0200848021204001023032060081804000ca08008480a08080008230308480212040010a080206008180400040b032060081804000c888002c288880400080b0302c280b0a40004888020600818040001000020600818040000828002c28828040002000002c280b0a400008280206008180 (by decide +kernel)

theorem lower171 : Claim 171 8 :=
  fromSearch 83 (by decide +kernel) exclude171_51

theorem lower187 : Claim 187 9 :=
  fromLift 9 16 67 lower171 (by decide +kernel)

def rule251_0 : {c : Cut // CutGood (goalAt 251) c} :=
  ruleFor 251 lower249 none (by decide +kernel)

def rule251_1 : {c : Cut // CutGood (goalAt 251) c} :=
  ruleFor 251 lower250 none (by decide +kernel)

def rule251_2 : {c : Cut // CutGood (goalAt 251) c} :=
  ruleFor 251 lower123 none (by decide +kernel)

def rule251_3 : {c : Cut // CutGood (goalAt 251) c} :=
  ruleFor 251 lower235 none (by decide +kernel)

def rule251_4 : {c : Cut // CutGood (goalAt 251) c} :=
  ruleFor 251 lower219 none (by decide +kernel)

def rule251_5 : {c : Cut // CutGood (goalAt 251) c} :=
  ruleFor 251 lower187 none (by decide +kernel)

def cuts251 : Cuts (goalAt 251) := [rule251_0,rule251_1,rule251_2,rule251_3,rule251_4,rule251_5]

def state251_0 : List Sig := roots 251
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude251_0 : Impossible true (goalAt 251) 10 state251_0.toFinset :=
  node_ok cuts251 [] 0x40008e0601c0c0e06040008b03034240d09040008e06034240d09040008b0301c0c0a06040008e0600e060e06040008c0402c240b09040008e0602c240b09040008c0400e060c0604001470302c240b09040014d09040014d09040014703040014503040014d0902c240b09040008b0301c180706040008e06040008e06040008b03040008a03040008e0601c18070604000cd09006828d0904000cc0801c180c0804000cd0901c180c0904000cc08006828c0904000cb09014100b0904000ca0801c180a0804000cb0901c180a0904000ca08014100a0904000898181a180686040008e06026240989040008981826240989040008e0601a180686040014581826240989040014d0901a180d0904001458181a180686040014d09026240989040010381826240989040010b0901a180b0904001038181a180686040010b0902624098904000c1a0a2220088804000c70602624098904000c1a0a2624098904000c7060222008890400008a0a18980626040000e06024a409290400008a0a24a40929040000e060189806260400004a0a24a40929040000d09018980d090400004a0a18980626040000d09024a409290400002a0a24a40929040000b09018980b090400002a0a18980626040000b09024a409290400001a0a20a00828040000706024a409290400001a0a24a40929040000706020a008290400000b0324a409290400009890068609890400000b03068601a1840000989024a40929040008830318580616040008e06024640919040008830324640919040008e06018580616040004430324640919040004d09018580d09040004430318580616040004d09024640919040004230324640919040004b09018580b09040004230318580616040004b090246409190400041303206008180400047060246409190400041303246409190400047060206008190400040b03246409190400049890064609890400040b0306460191840004989024640919040001000024640919040000929002c28929040001000102c280b0a400009290246409190 (by decide +kernel)

theorem lower251 : Claim 251 11 :=
  fromSearch 67 (by decide +kernel) exclude251_0


open PEqualNP.CircuitLowerBounds

def graph : Sig := goalAt 255
theorem graph_proper : proper graph := by unfold proper; decide +kernel

def edgeList : List Nat := [0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 5, 7, 6, 7]
def target (x : Fin 8 → Bool) : Bool :=
  decide (∃ i < edgeList.length / 2,
    (List.ofFn x).getD (edgeList.getD (2*i) 0) false = true ∧
    (List.ofFn x).getD (edgeList.getD (2*i+1) 0) false = true)

def smallCircuit : Circuit := ⟨[⟨.or, [0, 1]⟩, ⟨.or, [5, 6]⟩, ⟨.or, [3, 8]⟩, ⟨.or, [7, 9]⟩, ⟨.or, [2, 6]⟩, ⟨.or, [8, 12]⟩, ⟨.and, [10, 11]⟩, ⟨.and, [4, 13]⟩, ⟨.and, [9, 7]⟩, ⟨.and, [3, 0]⟩, ⟨.or, [14, 15]⟩, ⟨.or, [18, 16]⟩, ⟨.or, [19, 17]⟩], 20⟩

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


def lowRow (i : Fin 8) : Row := Fin.ofNat 256 (1 <<< ([3, 4, 4, 0, 0, 0, 0, 0] : List Nat).getD i.val 0)
def highRow (i : Fin 8) : Row := Fin.ofNat 256 ((1 <<< i.val) ||| (1 <<< ([3, 4, 4, 0, 0, 0, 0, 0] : List Nat).getD i.val 0))

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

end PEqualNP.Outside.L_meta_31463_aux

open PEqualNP.Outside.L_meta_31463_aux in
theorem PEqualNP.Outside.L_meta_31463 : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true))  := by
  intro gates o fit _ correct
  exact replaceShort lowerGraph gates o fit correct

import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_28972_aux


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
  (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 2 &&& x 5) ||| (x 1 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 5 &&& x 6) ||| (x 0 &&& x 7) ||| (x 2 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7)


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




def cuts82 : Cuts (goalAt 82) := []

def state82_0 : List Sig := roots 82
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude82_0 : Impossible true (goalAt 82) 3 state82_0.toFinset :=
  node_ok cuts82 [] 0x140401202140404202141005040140405040141004202048081202108081210048405010109004240108084240109005010048401210048084240109005040048405040048081210048405040109004240 (by decide +kernel)

theorem lower82 : Claim 82 4 :=
  fromSearch 16842816 (by decide +kernel) exclude82_0

theorem lower210 : Claim 210 5 :=
  fromLift 5 128 1090584640 lower82 (by decide +kernel)

theorem lower242 : Claim 242 6 :=
  fromLift 6 32 1096876096 lower210 (by decide +kernel)

def cuts164 : Cuts (goalAt 164) := []

def state164_0 : List Sig := roots 164
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude164_0 : Impossible true (goalAt 164) 3 state164_0.toFinset :=
  node_ok cuts164 [] 0x28080240428080840428200a08028080a08028200840409010240421010242009080a02021200848021010848021200a02009080242009010848021200a08009080a08009010242009080a080212008480 (by decide +kernel)

theorem lower164 : Claim 164 4 :=
  fromSearch 538969344 (by decide +kernel) exclude164_0

theorem lower228 : Claim 228 5 :=
  fromLift 5 64 622855424 lower164 (by decide +kernel)

theorem lower244 : Claim 244 6 :=
  fromLift 6 16 606471424 lower228 (by decide +kernel)

def cuts226 : Cuts (goalAt 226) := []

def state226_0 : List Sig := roots 226
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude226_0 : Impossible true (goalAt 226) 3 state226_0.toFinset :=
  node_ok cuts226 [] 0x18888c28230a08428218100e0c03830060c028a08e0c038300a0c010900c2c030b0042c030a08c2c030b00602230b00e0c028208c2c0 (by decide +kernel)

theorem lower226 : Claim 226 4 :=
  fromSearch 1365246048 (by decide +kernel) exclude226_0

def cuts102 : Cuts (goalAt 102) := []

def state102_0 : List Sig := roots 102
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude102_0 : Impossible true (goalAt 102) 3 state102_0.toFinset :=
  node_ok cuts102 [] 0x188886444191102444098886222108182622191106040181106044188884644119106022119106444090184644109004644119104244 (by decide +kernel)

theorem lower102 : Claim 102 4 :=
  fromSearch 18875744 (by decide +kernel) exclude102_0

def rule230_0 : {c : Cut // CutGood (goalAt 230) c} :=
  ruleFor 230 lower228 none (by decide +kernel)

def rule230_1 : {c : Cut // CutGood (goalAt 230) c} :=
  ruleFor 230 lower164 none (by decide +kernel)

def rule230_2 : {c : Cut // CutGood (goalAt 230) c} :=
  ruleFor 230 lower226 none (by decide +kernel)

def rule230_3 : {c : Cut // CutGood (goalAt 230) c} :=
  ruleFor 230 lower102 none (by decide +kernel)

def cuts230 : Cuts (goalAt 230) := [rule230_0,rule230_1,rule230_2,rule230_3]

def state230_0 : List Sig := [0xffffffffcccccccc0000000000000000ffffffffcccccccc,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 5,input 2,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude230_0 : Impossible true (goalAt 230) 4 state230_0.toFinset :=
  node_ok cuts230 [] 0x21110c4c031300242231300a08209088c4c031300c2c021a08c2c028088a08228208844438300464430b00c2c011910428230a08c28221110868231300868231300a08210888a08230a090001 (by decide +kernel)

def state230_1 : List Sig := [0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 5,input 2,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude230_1 : Impossible true (goalAt 230) 5 state230_1.toFinset :=
  node_ok cuts230 [⟨state230_0,exclude230_0⟩] 0xc44418088c44428088c28230a08c44430a08c28228088602221110c44409088c44428088c4c031300c44431300c4c028088242209088460621a08868230a08c4c031300460631300c4c030a08868221300240631300c4c028208242228208240609088242228208c4c031300464431300c4c030b00868230b00464421a08848230b00c4c030b00a02209018a02231110a08228208a02228208a08231110240631110602228208a08230a09000130a08602240004422230a08a08228209000040000e0c028088464411910c44430b00c2c028088c2c030b00c44411910464430a09000130a0a000030b00c2c030a08c2c030b010001400050001 (by decide +kernel)

def state230_2 : List Sig := [0xfffffffff0f0f0f0fffffffff0f0f0f0,input 2,input 5,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude230_2 : Impossible true (goalAt 230) 4 state230_2.toFinset :=
  node_ok cuts230 [] 0x30a08c2c030b00602230b00e0c028208c2c030b00c4c021208c2c028a08e0c038300a0c021a08c4c03130084c031300e0c018110c4c021110c28231110c28211910c2c011910c2c018300e0c019110e0c009888c4c031110c4c0 (by decide +kernel)

def state230_3 : List Sig := [0xfffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0,input 2,input 5,input 1,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude230_3 : Impossible true (goalAt 230) 5 state230_3.toFinset :=
  node_ok cuts230 [⟨state230_2,exclude230_2⟩] 0xc44430a08c28221110464430b00c2c011910c28230b00c2c018088c2c019110240630b00c2c011910464430b00c2c011910464430b00644431110a22219110622230a08644430a08e0c031110a22231110262209888c28211818c28219110262218110c4c031112000031111000318888c28218888c282 (by decide +kernel)

def state230_4 : List Sig := [0xcfcfcfcfcccccccccfcfcfcfcccccccccfcfcfcfcccccccccfcfcfcfcccccccc,input 2,input 5,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude230_4 : Impossible true (goalAt 230) 4 state230_4.toFinset :=
  node_ok cuts230 [] 0x31110c28230a08844419110a08228208644428208c28219110a08231110c4c031300262221a08c4c03130084c031300e4c019110c4c011910c2c030b00464430a08c2c030b01000130b00e0c028208c2c030b00c4c021208c2c0 (by decide +kernel)

def state230_5 : List Sig := [0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000,input 2,input 5,input 1,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude230_5 : Impossible true (goalAt 230) 5 state230_5.toFinset :=
  node_ok cuts230 [⟨state230_4,exclude230_4⟩] 0xc44430a08c28221110464430b00c2c011910c28230b00c2c018088c2c019110240630b00c2c031300848230b00644431110a22219110622230a08644430a08c44431300c4c028888868231300c4c021300e4c019110c4c028888c44428888c44418888c28218888c28240000c2c080000c2c0383002622 (by decide +kernel)

def state230_6 : List Sig := [0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 2,input 7,input 1,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude230_6 : Impossible true (goalAt 230) 5 state230_6.toFinset :=
  node_ok cuts230 [] 0xc44430a08c28221110622230a08c28218888a28238300e0c028300644438300e0c019110604038300e0c018100c28230b00c2c018088c2c038300a08230b00464430b00c2c011910c2c031300848230b00424030b00c2c010900a22221a08c4c03130084c031300e0c019110c4c031110c4c0400082622 (by decide +kernel)

def state230_7 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f00000000,input 5,input 7,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude230_7 : Impossible true (goalAt 230) 4 state230_7.toFinset :=
  node_ok cuts230 [] 0x31110c28230a08844430a08c2c030b00602211910c2c030b00464430b00e0c028208c2c028a08e0c038300a0c019110e0c03830060c021300c4c031300868230b00848230b00c4c009888c4c031300c44431300604438300c4c0 (by decide +kernel)

def state230_8 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,input 7,input 1,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude230_8 : Impossible true (goalAt 230) 5 state230_8.toFinset :=
  node_ok cuts230 [⟨state230_7,exclude230_7⟩] 0x622230a08c28218888460630a08c28211818868231300c4c021300262231300c4c009888c4c038300262231302000031300c4c040008c28230b00c2c018088c2c031300848230b00464430b00c2c011910c2c038300a08230b00464430b00c2c011910c44428a08e0c038300a0c028888e0c0183006444 (by decide +kernel)

def state230_9 : List Sig := [0xccccccccccccccccccccccccccccccccffffffffccccccccffffffffcccccccc,input 5,input 7,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude230_9 : Impossible true (goalAt 230) 4 state230_9.toFinset :=
  node_ok cuts230 [] 0x31110c28230a08844421a08c4c03130084c031110c4c031300242231300e0c009088c4c028a08e0c038300a0c039110e0c038300c44430a08c2c030b01000130b00c4c021208c2c011910c2c030b00464430b00e0c028208c2c0 (by decide +kernel)

def state230_10 : List Sig := [0xffffffff00000000ffffffff00000000,input 5,input 7,input 1,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude230_10 : Impossible true (goalAt 230) 5 state230_10.toFinset :=
  node_ok cuts230 [⟨state230_9,exclude230_9⟩] 0xc44430a08c28221110868231300c4c021300c44431300c4c009888c4c038300262231300c28230b00c2c018088c2c031300848230b00464430b00c2c011910c2c038300a08230b00a28238300e0c028300e44438300c44418888c28218888c28209888c4c009888c4c040000c2c080000c2c0288886444 (by decide +kernel)

def state230_11 : List Sig := roots 230
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude230_11 : Impossible true (goalAt 230) 6 state230_11.toFinset :=
  node_ok cuts230 [⟨state230_1,exclude230_1⟩,⟨state230_3,exclude230_3⟩,⟨state230_5,exclude230_5⟩,⟨state230_6,exclude230_6⟩,⟨state230_8,exclude230_8⟩,⟨state230_10,exclude230_10⟩] 0x40004c44418888c44440004a22230a08c28240004c44430a08c28240004a2221888884444000ca22219110644480014c44438300e0c080010a22238300e0c04000cc4441911060c040004622228a08a28240004c28238300e0c040004622238300e0c040004c28228a08a0c04000cc44409888c44440008a22231300c4c08000cc44431300c4c040008a22209888262240004460621a08868240008c28231300c4c040004460631300c4c040008c28221a0884c080008644431300c4c040008e0c009888e0c080004644409888604440008e0c031300c4c040000a22211910464440000c44430b00c2c040000a22230b00c2c040000c44411910464440000c28240004c28240000602030b00c2c040000c28230b00c2c040000602040000602240000a28230b00c2c040000e0c040000e0c040000a28280000a08240000e0c030b00c2c040000868230b00c2c040000c4c011910c4c040000868211910848240000c4c030b00c2c0 (by decide +kernel)

theorem lower230 : Claim 230 7 :=
  fromSearch 555746656 (by decide +kernel) exclude230_11

def cuts212 : Cuts (goalAt 212) := []

def state212_0 : List Sig := roots 212
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude212_0 : Impossible true (goalAt 212) 3 state212_0.toFinset :=
  node_ok cuts212 [] 0x31110941421110844415110d0c03430050c024200d0c03430090c031110c4c031300901421200c4c03130084c031300d0c014110c4c0 (by decide +kernel)

theorem lower212 : Claim 212 4 :=
  fromSearch 604374784 (by decide +kernel) exclude212_0

def cuts150 : Cuts (goalAt 150) := []

def state150_0 : List Sig := roots 150
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude150_0 : Impossible true (goalAt 150) 3 state150_0.toFinset :=
  node_ok cuts150 [] 0x25050928224a08841425050868221a08901421a08928204818868205850941421018161424a08908024208908221a088480212088482 (by decide +kernel)

theorem lower150 : Claim 150 4 :=
  fromSearch 536938304 (by decide +kernel) exclude150_0

def rule214_0 : {c : Cut // CutGood (goalAt 214) c} :=
  ruleFor 214 lower210 none (by decide +kernel)

def rule214_1 : {c : Cut // CutGood (goalAt 214) c} :=
  ruleFor 214 lower212 none (by decide +kernel)

def rule214_2 : {c : Cut // CutGood (goalAt 214) c} :=
  ruleFor 214 lower150 none (by decide +kernel)

def rule214_3 : {c : Cut // CutGood (goalAt 214) c} :=
  ruleFor 214 lower82 none (by decide +kernel)

def cuts214 : Cuts (goalAt 214) := [rule214_0,rule214_1,rule214_2,rule214_3]

def state214_0 : List Sig := [0xfffff0f0fffff0f0fffff0f0fffff0f0,0xfffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0,input 4,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude214_0 : Impossible true (goalAt 214) 4 state214_0.toFinset :=
  node_ok cuts214 [] 0x30a08c2c030b00161430b00504405850c2c030b00c4c021208c2c014050c28214110c28234300868231300c4c021300844430a08c44430a08464430b00464430b005044210505044311110003 (by decide +kernel)

def state214_1 : List Sig := [0xfffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0,input 4,input 1,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude214_1 : Impossible true (goalAt 214) 5 state214_1.toFinset :=
  node_ok cuts214 [⟨state214_0,exclude214_0⟩] 0xc44414050c44424050c28230a08c44430a08c28224050501421110860611910464431110c2c030b00860630b00c2c031110464411910c28205850c28214050c2c030b00c28230b00c2c014050161405850120630b00c2c014110161414110120605850161414110c2c030b00868230b00c2c031300464431300868211910848231300c2c030b0090141411050443111100033111090144000c841431110504414110501404818501430a08504430a08501414110504430a08120630a09000040000d0c031111000331112000031300c4c031110c4c03130100034000d000314050868221a08c28231300c4c014050c4c031300c28221a0884c0 (by decide +kernel)

def state214_2 : List Sig := [0xffffccccffffcccc0000000000000000ffffccccffffcccc,input 1,input 4,input 2,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude214_2 : Impossible true (goalAt 214) 4 state214_2.toFinset :=
  node_ok cuts214 [] 0x21110c4c031300901431300d0c014110c4c015110d0c034300508011910c2c030b00464430b00c4c021a08c2c030b00d0c024208c2c010a08c28230a08844421a08c4c021a08c4c024300d0c024a08d0c005850c2c030a08c2c0 (by decide +kernel)

def state214_3 : List Sig := [0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc,input 1,input 4,input 2,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude214_3 : Impossible true (goalAt 214) 5 state214_3.toFinset :=
  node_ok cuts214 [⟨state214_2,exclude214_2⟩] 0xc44430a08c28221110c44431300c4c024050868231300c4c021300c4c024a08120631300c4c021a08868231300941424a08928231110928230a08541424a08d0c005850c44421818c44430a08541430a08161421a08c4c021a08c4c024a08161424208c2c025050c44425050c44430a0a000030a090002 (by decide +kernel)

def state214_4 : List Sig := [0xf3f3f0f0f3f3f0f0f3f3f0f0f3f3f0f0f3f3f0f0f3f3f0f0f3f3f0f0f3f3f0f0,input 1,input 4,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude214_4 : Impossible true (goalAt 214) 4 state214_4.toFinset :=
  node_ok cuts214 [] 0x31110c28230a08844414110928224a08504424a08c28214110928211910c2c030b00464430a08c2c030b00161430b00d2c024a08c2c030b00c4c021208c2c031110c4c031301000321a08c4c03130084c031300d0c014110c4c0 (by decide +kernel)

def state214_5 : List Sig := [0x3333000033330000333300003333000033330000333300003333000033330000,input 1,input 4,input 2,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude214_5 : Impossible true (goalAt 214) 5 state214_5.toFinset :=
  node_ok cuts214 [⟨state214_4,exclude214_4⟩] 0xc44430a08c28221110c44431300c4c024050868231300c4c021300c4c024a08120631300941424a08928231110928230a08541424a08464430b00c2c011910c28230b00c2c015050c2c031300848230b00d2c024a08c2c025050c44425050c44415050c28215050c28240000c4c080000c4c0343001614 (by decide +kernel)

def state214_6 : List Sig := [0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,input 1,input 6,input 2,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude214_6 : Impossible true (goalAt 214) 5 state214_6.toFinset :=
  node_ok cuts214 [] 0x544434300d0c014300928234300d0c024a08908034300d0c024200c44431300c4c024050c4c034300504431300868231300c4c021a08848031300c4c021200c44430a08c28210a08541411910c2c030b00464430b00d0c024a08c2c030b00c4c021a08c2c030a08c2c0400041614311109414311109414 (by decide +kernel)

def state214_7 : List Sig := [0x3333333333333333333300003333000033333333333333333333000033330000,input 4,input 6,input 2,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude214_7 : Impossible true (goalAt 214) 4 state214_7.toFinset :=
  node_ok cuts214 [] 0x31110c4c031300901421208c4c031300848231300d0c014110c4c031110c28230a08428015110d0c03430050c024a08d0c03430090c011910c2c030b00464430b00848231300c2c005850c2c030b00c28230b00908234300c2c0 (by decide +kernel)

def state214_8 : List Sig := [0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 4,input 6,input 1,input 2,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude214_8 : Impossible true (goalAt 214) 5 state214_8.toFinset :=
  node_ok cuts214 [⟨state214_7,exclude214_7⟩] 0xc44431300c4c024050868231300c4c021a08c4c034300504431300868231300c4c021a08464430b00c2c011910c2c031300848230b00161430b00c2c005850c2c034300161430b02000030b00c2c040004c44425050c44415050c28215110d0c03430050c015050d0c0243009282311108606311108606 (by decide +kernel)

def state214_9 : List Sig := [0xf0f0f0f0f0f0f0f0fffff0f0fffff0f0f0f0f0f0f0f0f0f0fffff0f0fffff0f0,input 4,input 6,input 1,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude214_9 : Impossible true (goalAt 214) 4 state214_9.toFinset :=
  node_ok cuts214 [] 0x11910c2c030b00464430a08c2c030b00161430b00d0c005850c2c030b00c4c021208c2c031110c28230a08844415110d0c03430050c034a08d0c034300c28231110c4c031301000321a08c4c03130084c031300d0c014110c4c0 (by decide +kernel)

def state214_10 : List Sig := [0xffff0000ffff00000000000000000000ffff0000ffff0000,input 4,input 6,input 1,input 2,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude214_10 : Impossible true (goalAt 214) 5 state214_10.toFinset :=
  node_ok cuts214 [⟨state214_9,exclude214_9⟩] 0xc44431300c4c024050868231300c4c021300c4c034300504431300464430b00c2c011910c2c031300848230b00c28230b00c2c005850c2c034300161430b00c44430a08c28221110544434300d0c014300d28234300c28225050c44425050c44440000c4c080000c4c005850c2c005850c2c0150509282 (by decide +kernel)

def state214_11 : List Sig := roots 214
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude214_11 : Impossible true (goalAt 214) 6 state214_11.toFinset :=
  node_ok cuts214 [⟨state214_1,exclude214_1⟩,⟨state214_3,exclude214_3⟩,⟨state214_5,exclude214_5⟩,⟨state214_6,exclude214_6⟩,⟨state214_8,exclude214_8⟩,⟨state214_10,exclude214_10⟩] 0x4000cc44415050c44440008941430a08c2824000cc44430a08c2824000894141505084444000c94141511054444000cc44434300d0c04000c941434300d0c04000cc4441511050c040008541424a08928280014c28234300d0c080010541434300d0c040008c28224a0890c040000c4444000cc44440000901031300c4c040000c44431300c4c040000901040000901440000541421a08868240000c28231300c4c040000541431300c4c040000c28221a0884c040000544431300c4c040000d0c040000d0c040000544480000504440000d0c031300c4c04000c860611910464440004c44430b00c2c04000c860630b00c2c040004c44411910464440008c28205850c28240004541430b00c2c08000cc28230b00c2c040004541405850161480008928230b00c2c040004d0c005850d0c080004928205850908240004d0c030b00c2c040000868230b00c2c040000c4c011910c4c040000868211910848240000c4c030b00c2c0 (by decide +kernel)

theorem lower214 : Claim 214 7 :=
  fromSearch 553715520 (by decide +kernel) exclude214_11

theorem lower180 : Claim 180 5 :=
  fromLift 5 16 539428096 lower164 (by decide +kernel)

def cuts178 : Cuts (goalAt 178) := []

def state178_0 : List Sig := roots 178
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude178_0 : Impossible true (goalAt 178) 3 state178_0.toFinset :=
  node_ok cuts178 [] 0x2c0c0a28228a0890302c0c0928224a08a03024a08a2820c88892820c8c0b03028088323028a08a08028208a08224a089080242089082 (by decide +kernel)

theorem lower178 : Claim 178 4 :=
  fromSearch 1081147456 (by decide +kernel) exclude178_0

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

theorem lower114 : Claim 114 5 :=
  fromLift 5 32 23134272 lower82 (by decide +kernel)

def cuts116 : Cuts (goalAt 116) := []

def state116_0 : List Sig := roots 116
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude116_0 : Impossible true (goalAt 116) 3 state116_0.toFinset :=
  node_ok cuts116 [] 0x1c0c064441911050301c0c054441511060301511064440905054440d0c07030140503430191106040181106044151105040141105044 (by decide +kernel)

theorem lower116 : Claim 116 4 :=
  fromSearch 69600512 (by decide +kernel) exclude116_0

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

def rule246_0 : {c : Cut // CutGood (goalAt 246) c} :=
  ruleFor 246 lower242 none (by decide +kernel)

def rule246_1 : {c : Cut // CutGood (goalAt 246) c} :=
  ruleFor 246 lower244 none (by decide +kernel)

def rule246_2 : {c : Cut // CutGood (goalAt 246) c} :=
  ruleFor 246 lower230 none (by decide +kernel)

def rule246_3 : {c : Cut // CutGood (goalAt 246) c} :=
  ruleFor 246 lower214 none (by decide +kernel)

def rule246_4 : {c : Cut // CutGood (goalAt 246) c} :=
  ruleFor 246 lower182 none (by decide +kernel)

def rule246_5 : {c : Cut // CutGood (goalAt 246) c} :=
  ruleFor 246 lower118 none (by decide +kernel)

def rule246_6 : {c : Cut // CutGood (goalAt 246) c} :=
  ruleFor 246 lower228 none (by decide +kernel)

def rule246_7 : {c : Cut // CutGood (goalAt 246) c} :=
  ruleFor 246 lower210 none (by decide +kernel)

def rule246_8 : {c : Cut // CutGood (goalAt 246) c} :=
  ruleFor 246 lower180 none (by decide +kernel)

def rule246_9 : {c : Cut // CutGood (goalAt 246) c} :=
  ruleFor 246 lower114 none (by decide +kernel)

def cuts246 : Cuts (goalAt 246) := [rule246_0,rule246_1,rule246_2,rule246_3,rule246_4,rule246_5,rule246_6,rule246_7,rule246_8,rule246_9]

def state246_0 : List Sig := [0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc,input 1,input 2,input 4,input 5,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude246_0 : Impossible true (goalAt 246) 7 state246_0.toFinset :=
  node_ok cuts246 [] 0xc4441c0c0c4442c0c0c28230a08c44430a08c2822c0c0703021110b03019110644431110e0c038300b03038300e0c031110644418300703028a08a28230a08e0c038300703038300e0c030a08a28228300b03015110544431110d0c034300b03034300d0c031110544414300703024a08928230a08d0c034300703034300d0c030a08928224300341434300d0c03830032223830034140c888322238300d0c034300c44409888c4442c0c0868221a08c44421a0886822c0c026222c0c0541421a08868230a09000030a08541440020541430a08868221a08644421a08868238300262238300644409888644438300868238300544421a08868234301000034300544440018544434300868234301000040004c4c028888464411910c44440004c44428889000928888c44411910464430a08161430a08703011910464430a08464430a08703005850703028a08464428a08e0c040004e0c028a09000728a08e0c011910e0c024a08464424a08d0c005850d0c024a08161424a08d0c011910d0c021a09000021a09000111910464440001000021209000040000c2c031111000531110b03040024b03031111000931110b03040014b03030a09000430a08703040020703030a09000830a08703040010703028a09000328a08e0c04001ce0c028a09000728a08e0c04000ce0c024a09000224a08d0c040018d0c024a09000624a08d0c040008d0c0 (by decide +kernel)

def state246_1 : List Sig := roots 246
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude246_1 : Impossible true (goalAt 246) 8 state246_1.toFinset :=
  node_ok cuts246 [⟨state246_0,exclude246_0⟩] 0x40014c4441c0c0c44440014b03030a08c28240014c44430a08c28240014b0301c0c084444000cb0301911064444000cc44438300e0c04000cb03038300e0c04000cc4441911060c04000c703028a08a2824000cc28238300e0c04000c703038300e0c04000cc28228a08a0c040008b03015110544440008c44434300d0c040008b03034300d0c040008c4441511050c040008703024a08928240008c28234300d0c040008703034300d0c040008c28224a0890c040008341434300d0c040008e0c00c888e0c04000834140c888322240008e0c034300d0c040014c4440d0c0c44440014b03031300c4c040014c44431300c4c040014b0300d0c0343040010541421a08868240010c28231300c4c040010541431300c4c040010c28221a0884c04000c644431300c4c04000ce0c00d0c0e0c04000c64440d0c060444000ce0c031300c4c040008544431300c4c040008d0c00d0c0d0c04000854440d0c0504440008d0c031300c4c040014a22211910464440014c44430b00c2c040014a22230b00c2c040014c44411910464440010c2820c8c0c28240010703030b00c2c040010c28230b00c2c04001070300c8c032304000ca28230b00c2c04000ce0c00c8c0e0c04000ca2820c8c0a0824000ce0c030b00c2c040008928230b00c2c040008d0c00c8c0d0c04000892820c8c0908240008d0c030b00c2c040000868230b00c2c040004c4c011910c4c080000868211910848240000c4c030b00c2c0 (by decide +kernel)

theorem lower246 : Claim 246 9 :=
  fromSearch 555812160 (by decide +kernel) exclude246_1

def cuts161 : Cuts (goalAt 161) := []

def state161_0 : List Sig := roots 161
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude161_0 : Impossible true (goalAt 161) 3 state161_0.toFinset :=
  node_ok cuts161 [] 0x28080210128080810128200a08028080a08028200810108404210120404212008480a02020600818020404818020600a02008480212008404818020600a08008480a08008404212008480a080206008180 (by decide +kernel)

theorem lower161 : Claim 161 4 :=
  fromSearch 5 (by decide +kernel) exclude161_0

theorem lower177 : Claim 177 5 :=
  fromLift 5 16 4 lower161 (by decide +kernel)

theorem lower165 : Claim 165 5 :=
  fromLift 5 1 1285 lower164 (by decide +kernel)

def cuts145 : Cuts (goalAt 145) := []

def state145_0 : List Sig := roots 145
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude145_0 : Impossible true (goalAt 145) 3 state145_0.toFinset :=
  node_ok cuts145 [] 0x240401101240408101242009080240409080242008101044041101204041110044409010206008180204048180206009010044401110044048180206009080044409080044041110044409080206008180 (by decide +kernel)

theorem lower145 : Claim 145 4 :=
  fromSearch 4 (by decide +kernel) exclude145_0

theorem lower149 : Claim 149 5 :=
  fromLift 5 4 1796 lower145 (by decide +kernel)

def rule181_0 : {c : Cut // CutGood (goalAt 181) c} :=
  ruleFor 181 lower177 none (by decide +kernel)

def rule181_1 : {c : Cut // CutGood (goalAt 181) c} :=
  ruleFor 181 lower180 none (by decide +kernel)

def rule181_2 : {c : Cut // CutGood (goalAt 181) c} :=
  ruleFor 181 lower165 none (by decide +kernel)

def rule181_3 : {c : Cut // CutGood (goalAt 181) c} :=
  ruleFor 181 lower149 none (by decide +kernel)

def cuts181 : Cuts (goalAt 181) := [rule181_0,rule181_1,rule181_2,rule181_3]

def state181_0 : List Sig := roots 181
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude181_0 : Impossible true (goalAt 181) 6 state181_0.toFinset :=
  node_ok cuts181 [] 0x4000cb0300d050b0304000c941428200a0804000cb03028200a0804000c94140d050903040008b03005414b03040008a02024200908040008b03024200908040008a02005414a03040008341424200908040008a08040008a0804000834144000c241440008a0802420090804000094140d0c0343040000b03021200848040000941421200848040000b0300d0c0343040000341421200848040000a0800d0c0a0804000034140d0c0343040000a0802120084804000015052120084804000090800d0c090804000015050d0c034304000090802120084804000485050c4c0313040004b03020600818040004850520600818040004b0300c4c0313040004250520600818040004a0800c4c0a0804000425050c4c0313040004a0802060081804000815052060081804000890800c4c090804000815050c4c03130400089080206008180400010000206008180400008480054508480400010001054501514400008480206008180 (by decide +kernel)

theorem lower181 : Claim 181 7 :=
  fromSearch 1284 (by decide +kernel) exclude181_0

theorem lower147 : Claim 147 5 :=
  fromLift 5 2 68 lower145 (by decide +kernel)

def cuts51 : Cuts (goalAt 51) := []

def state51_0 : List Sig := roots 51
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude51_0 : Impossible true (goalAt 51) 3 state51_0.toFinset :=
  node_ok cuts51 [] 0x4c0c32220c88812220484032300c8c012300c88832300c8c011030444031300c4c0113008c8831300c4c023220c4c0323008c883130 (by decide +kernel)

theorem lower51 : Claim 51 4 :=
  fromSearch 68 (by decide +kernel) exclude51_0

def rule179_0 : {c : Cut // CutGood (goalAt 179) c} :=
  ruleFor 179 lower177 none (by decide +kernel)

def rule179_1 : {c : Cut // CutGood (goalAt 179) c} :=
  ruleFor 179 lower178 none (by decide +kernel)

def rule179_2 : {c : Cut // CutGood (goalAt 179) c} :=
  ruleFor 179 lower161 none (by decide +kernel)

def rule179_3 : {c : Cut // CutGood (goalAt 179) c} :=
  ruleFor 179 lower147 none (by decide +kernel)

def rule179_4 : {c : Cut // CutGood (goalAt 179) c} :=
  ruleFor 179 lower51 none (by decide +kernel)

def cuts179 : Cuts (goalAt 179) := [rule179_0,rule179_1,rule179_2,rule179_3,rule179_4]

def state179_0 : List Sig := [0xffffffffffffffffffffffffffffffffeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 7,input 0,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_0 : Impossible true (goalAt 179) 4 state179_0.toFinset :=
  node_ok cuts179 [] 0x28088a0822820821030c8c0a08228208123024208a0820c88890820c88890822420832220c8c0908224209000220e08a08208c88838220e0890820440c838208c88838220e0823220c4c0b030 (by decide +kernel)

def state179_1 : List Sig := [0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 7,input 0,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_1 : Impossible true (goalAt 179) 4 state179_1.toFinset :=
  node_ok cuts179 [] 0xb03028208a082240c0908228208322224208b030242089082280c0838228208232220e08838224208110320e08b13020e0883822c0c0121028208323028208322224208323024208313020e08232220e08a022 (by decide +kernel)

def state179_2 : List Sig := [0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 0,input 4,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_2 : Impossible true (goalAt 179) 5 state179_2.toFinset :=
  node_ok cuts179 [⟨state179_0,exclude179_0⟩,⟨state179_1,exclude179_1⟩] 0xb0300840cb03024040a28228a08b03028a08a282240402103240c0b0300c888b03028888928224a08b03024a089282288883222280c1000224a08928228a08322228a0900020c888322228a08928224a08810308c8823222c0c0838220e08810320e0883822c0c023222c0c0210320e08838228a08232228608210308c88232228a08838220e08110320e08838224a09000124608110340008110324a08838220e0900004000081802888832300c8c0b03080004b0302888a000028088b0300c8c0323028a08121028a08a0800c8c0a08028a08323028208a08004840a08224a09000224a0890800c8c0908024a083230242089080400089082 (by decide +kernel)

def state179_3 : List Sig := [0x5555555555555555555555555555555544444444444444444444444444444444,input 0,input 7,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_3 : Impossible true (goalAt 179) 4 state179_3.toFinset :=
  node_ok cuts179 [] 0xa02228208a0820840c90822820832222420832222420890820c88811102820831302820821202420831302420831302c4c081030c4c0a0820c8c0a082048c090820c8c090820440c32302c0c0a0220c8c08382 (by decide +kernel)

def state179_4 : List Sig := [0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 7,input 0,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_4 : Impossible true (goalAt 179) 5 state179_4.toFinset :=
  node_ok cuts179 [⟨state179_0,exclude179_0⟩,⟨state179_3,exclude179_3⟩] 0xa02208c0ca0222040ca08228208a02228208a0822040c230308c0c323008404323004840a08228208323028208a082048402101048c100022420890822820832222820900020c88832222820890822420900020c88832222808890822420900022420890822808832220c88832300440432304000890822420832302420890824000811010440c230320e0883822820831302820823030c4c0313028208838220e08130320e0883822420831302420813030c4c0313024208838220e0881030c4c0313028088838220e08810320e0883822808831300c4c200010c4c031300c8c0838220e0a000020e0883820c8c031300c4c1000040000b030 (by decide +kernel)

def state179_5 : List Sig := [0xffffffff00000000ffffffff00000000aaaaaaaa00000000aaaaaaaa,input 0,input 7,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_5 : Impossible true (goalAt 179) 4 state179_5.toFinset :=
  node_ok cuts179 [] 0x2c0c0928224a08a03024a0890802420890820c8c0b03028088323020e0892820c4c0838220600838220e0881820c4c0838220e08313024a08322224a08a28228208a08228a08a080240c0a28228a08b03020e08313020e08a282 (by decide +kernel)

def state179_6 : List Sig := [0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 0,input 7,input 1,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_6 : Impossible true (goalAt 179) 5 state179_6.toFinset :=
  node_ok cuts179 [⟨state179_0,exclude179_0⟩,⟨state179_5,exclude179_5⟩] 0x230328a08a28208c0e000128a08a2824000c928228a08322224a08322224a0892820c888322224a0892820c888a28228200a0822820892822420090822420832302040481030c8c032304000200000c8c0b03020e08a28208c0c838220e08928204c0c838220600838220e08818220c0c8382400043130 (by decide +kernel)

def state179_7 : List Sig := roots 179
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_7 : Impossible true (goalAt 179) 6 state179_7.toFinset :=
  node_ok cuts179 [⟨state179_2,exclude179_2⟩,⟨state179_4,exclude179_4⟩,⟨state179_6,exclude179_6⟩] 0x4000cb03008c0cb0304000c901028a08a2824000cb03028a08a2824000c901008c0c903040008b0300c888b03040008a22224a08928240008b03024a08928240008a2220c888a0304000d000324a0892824000ca2820c888a2824000d00020c88832224000ca28224a08928240000a2220c8c0323040000b03040000b03040000a22280004a02240000b0300c8c0323040000a28204840a28240000a0800c8c0a08040000a2820c8c0a08240000a08004840a0824000092824000892824000090800c8c090804000092820c8c090824000090804000090824001083030c4c0313040004b03020e08838280008830320e08838240004b0300c4c031304000c230320e0883824000ca2820c4c0a2824000c23030c4c031304000ca28220e08838240008130320e0883824000492820c4c092824000813030c4c0313040004928220e08838240001000020600818040000323020e08838240002000020e088382400003230206008182 (by decide +kernel)

theorem lower179 : Claim 179 7 :=
  fromSearch 68 (by decide +kernel) exclude179_7

theorem lower151 : Claim 151 6 :=
  fromLift 6 2 1860 lower149 (by decide +kernel)

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

def rule183_0 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower181 none (by decide +kernel)

def rule183_1 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower182 none (by decide +kernel)

def rule183_2 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower179 none (by decide +kernel)

def rule183_3 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower151 none (by decide +kernel)

def rule183_4 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower165 none (by decide +kernel)

def rule183_5 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower180 none (by decide +kernel)

def rule183_6 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower164 none (by decide +kernel)

def rule183_7 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower149 none (by decide +kernel)

def rule183_8 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower177 none (by decide +kernel)

def rule183_9 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower161 none (by decide +kernel)

def rule183_10 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower182 (some (1,input 1,input 7)) (by decide +kernel)

def rule183_11 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower53 none (by decide +kernel)

def rule183_12 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower55 none (by decide +kernel)

def rule183_13 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower179 (some (1,input 1,input 7)) (by decide +kernel)

def rule183_14 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower51 none (by decide +kernel)

def rule183_15 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower145 none (by decide +kernel)

def rule183_16 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower147 none (by decide +kernel)

def rule183_17 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower182 (some (1,input 5,input 7)) (by decide +kernel)

def rule183_18 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower182 (some (3,input 5,input 7)) (by decide +kernel)

def cuts183 : Cuts (goalAt 183) := [rule183_0,rule183_1,rule183_2,rule183_3,rule183_4,rule183_5,rule183_6,rule183_7,rule183_8,rule183_9,rule183_10,rule183_11,rule183_12,rule183_13,rule183_14,rule183_15,rule183_16,rule183_17,rule183_18]

def state183_0 : List Sig := [0xffffffffffffffffffffffffffffffff33330000333300003333000033330000,input 7,input 4,input 0,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_0 : Impossible true (goalAt 183) 6 state183_0.toFinset :=
  node_ok cuts183 [] 0xb0300d050b03025050a08228208b03028208a082250503414240c032300941c323005850a08228208323028208a0820585025070585034142120884822820834302820834140d0c034302820884822120817072120884822420834302420817070d0c034302420884822120894140d0c034302c0c084822120894142120884822c0c034300d0c016140908824220c8c084822120816142120884820c8c024220c8c0250720e0883822820831302820825070c4c0313028208838220e09000620e08838221208151421209000605450151421208838220e08170720e0883822420831302420817070c4c0313024208838220e0900060c4c031302c0c0838220e09000620e0883822c0c031300c4c1000608c8823220c8c0838220e09000620e0883820c8c023220c8c034142420890822820832222820834140c888322228208908224208b0300c888b03040010908224208b030242089082400103222280c032300c88832304000090822420832302420890824000032220c889000440010a022 (by decide +kernel)

def state183_1 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f00000000,input 5,input 7,0x3333000033330000333300003333000033330000333300003333000033330000,input 4,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_1 : Impossible true (goalAt 183) 5 state183_1.toFinset :=
  node_ok cuts183 [] 0x838224a08313020e08313020e0883820c4c0838228208313020e08b03024a0892820c888928228208322224a08313020e08313020e0890820c8c0a0222c0c0323005850a0820c8c0a0822c0c0a08228208903020e08151420e08848221208343024a0884822120834300c8c084820d0c08482212083430212083430282088482 (by decide +kernel)

def state183_2 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,input 7,0x3333000033330000333300003333000033330000333300003333000033330000,input 4,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_2 : Impossible true (goalAt 183) 6 state183_2.toFinset :=
  node_ok cuts183 [⟨state183_1,exclude183_1⟩] 0x2120892820d0c084820d0c0848221208343021208a0820d0c0848280000848221209000820e08848205450838220e0892820c4c083820c4c0838220e08313020e08a0820c4c0838205450838220e0815142c0c0928224a08322224a08a0820c888928205c1c928224a0817070c8c084820d0c084820c4c083820c4c0838224208323028088b0300c8c016142820832302820816140c8c032300585094142c0c0a082240c03414 (by decide +kernel)

def state183_3 : List Sig := [0x33330000ffffffff33330000ffffffff33330000333300003333000033330000,input 5,input 7,input 4,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_3 : Impossible true (goalAt 183) 5 state183_3.toFinset :=
  node_ok cuts183 [] 0x2120890820d0c084820d0c084822120834302120834300d0c0848220e08848205450838220e0890820c4c083820c4c0838220e08313020e0831300c4c083822c0c0908224208322224208b0820c88890822c0c09414240c0903021208242221208323020e08232220e0832302420832302420832220c8c0a0222c0c0323005850323028208a082 (by decide +kernel)

def state183_4 : List Sig := [0xffffffff00000000ffffffff00000000000000000000000000000000,input 5,input 7,0x3333000033330000333300003333000033330000333300003333000033330000,input 4,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_4 : Impossible true (goalAt 183) 6 state183_4.toFinset :=
  node_ok cuts183 [⟨state183_3,exclude183_3⟩] 0x2120892820d0c084820d0c084822120834302120834300d0c0848220e08848205450838220e0892820c4c083820c4c0838220e08313020e0831300c4c083822c0c0928224a08322224a0832220c88892820c8c084820d0c084820c4c083820c4c0838224208323028088b0300c8c016140c8c0323005850b4142c0c0341421208343021208343020e08313020e08313024a08322224a08322240010323080000323025050a082 (by decide +kernel)

def state183_5 : List Sig := [0x3333000033330000333300003333000033330000333300003333000033330000,input 4,input 0,input 2,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_5 : Impossible true (goalAt 183) 7 state183_5.toFinset :=
  node_ok cuts183 [⟨state183_0,exclude183_0⟩,⟨state183_2,exclude183_2⟩,⟨state183_4,exclude183_4⟩] 0x80008b0300d050b0304001c941428208a08280004b03028208a0824001c94140d05090304002494140d0c0343040020b03021208848240024941421208848240020b0300d0c034304001c341421208848240020a0820d0c0a0824002434140d0c034304001ca0822120884824001017072120884824001092820d0c092824001017070d0c034304001092822120884824001885070c4c0313040014b03020e08838240018850720e08838240014b0300c4c031304001c250720e08838240014a0820c4c0a0824001825070c4c031304001ca08220e08838240021000620e08838240014848205450848240019000605450151440014848220e08838240010170720e0883824001492820c4c092824001017070c4c0313040014928220e08838240010b0300c888b03040010a02224a08928240010b03024a08928240010a0220c88832224001c341424a08928240010a0820c888a0824001034140c88832224001ca08224a08928240010b0300c8c0323040010a02240010a02240010b03080000b03040010a0220c8c032304001c341405850161440010a0820c8c0a0824001034140c8c032304001ca08205850a0824001034300c8c032304001084820585084824001034300585034304001084820c8c084824001431300c8c031304001083824001083824001031304001831304001483820c8c08382400010000400009082 (by decide +kernel)

def state183_6 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 5,0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_6 : Impossible true (goalAt 183) 5 state183_6.toFinset :=
  node_ok cuts183 [] 0x34302120884820c8c02622212088482090c084820d0c0343021208848224208343021208838221208151420e08313020e0883820c4c0232220e08838208c8883820c4c0313020e08838224208313020e0832220c8c032304001c3230058503230240c032220d050322224088a0820c8c090822420884140c8889082242088507 (by decide +kernel)

def state183_7 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 4,0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 0,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_7 : Impossible true (goalAt 183) 6 state183_7.toFinset :=
  node_ok cuts183 [⟨state183_6,exclude183_6⟩] 0x32300d050323005850a08228208323028208a082058503414240c0a02209c1ca0222141ca08228208a02228208a0822141c270709c1c34142120884822820834302820834140d0c034302820884822120816140d0c034300c8c084822120816142120884820c8c034300c8c100042120884822420834302420900090d0c0343024208848221208850709888262228088848221208850721208848228088262209888270720e0883822820831302820827070c4c0313028208838220e09000620e08838221208151421209000605450151421208838220e0900060c4c031300c8c0838220e09000620e0883820c8c031300c4c1000420e0883822420831302420900060c4c0313024208838220e08850708c88232228088838220e08850720e08838228088232208c88a02240010a0224000032300c8c0a0220c8c032304000100044000034142420890822820900042820834148000034142820890822420832304002c3230400109082242083230242089082400110004280c1000c400303222 (by decide +kernel)

def state183_8 : List Sig := [0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000,input 4,0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 0,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_8 : Impossible true (goalAt 183) 6 state183_8.toFinset :=
  node_ok cuts183 [] 0xc8c034140c8c0161428208a0820c8c0a0822820816140d05090300d050848221208a0820d0c0a0820d05034300d0c0a0822120884820585034300d0c032302120884820585084822120832300d0c0323005c1c84822120832220d0c0343005c1c34300d0c0322221208848209c1c838220e08a0820c4c0a08209c1c31300c4c0a08220e08838240018838220e08848205450848240018151405450848220e0883824001831300c4c0323020e08838240018838220e0832300c4c0313005c1c838220e0832220c4c0313005c1c31300c4c0322220e0883820d05017070d050a0820c888a0820d05032220c888a08205c1ca0820c8c015050c8c100040c88832220c8c032220c8c1000405414150728208850728208341428088a02228208a0222820834142141c341421208a0222120834302141c343021208850721208343028088343020e08a02220e0831302141c313020e08850720e08313028088313040031000428081000c400109082 (by decide +kernel)

def state183_9 : List Sig := [0xffffffffffffffffffffffffffffffffffffccccffffccccffffccccffffcccc,input 4,0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 7,input 0,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_9 : Impossible true (goalAt 183) 6 state183_9.toFinset :=
  node_ok cuts183 [] 0xa02228208a0820d050323028208a08205850250528208a0820941484822820834302120834302120884820d0c034302120884820c8c0848224208343021208242021208848209080838228208313020e08838221208151420e08313020e0883820c4c0313020e0883820c4c0838224208313020e08212020e08838208480b03040011000424208a0820c88890820c88890822420832220c8c090820541c1505 (by decide +kernel)

def state183_10 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 4,input 7,0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 0,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_10 : Impossible true (goalAt 183) 6 state183_10.toFinset :=
  node_ok cuts183 [] 0xc8c0a0822820816140d050a08228208341409c1ca08228208270721208a0820d0c084820d0c084822120832300d0c084822120834302120890820d0c0848209888848221208262220e08a0820c4c0838220e0884820545083820c4c0838220e0831300c4c0838220e08313020e0890820c4c0838208c88838220e0823224001032300c8c100002c0c0a02224208a0820d05090820c8c0908224209000440030908204a003222 (by decide +kernel)

def state183_11 : List Sig := [0x33333333333300003333333333330000,input 4,input 5,input 7,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_11 : Impossible true (goalAt 183) 5 state183_11.toFinset :=
  node_ok cuts183 [] 0x34302120884820d0c0848228208343021208848224208343021208838221208151420e08313020e0883820c4c0838228208313020e08838224208313020e08a02228208a0820d05032222420890820c888908228208322224208323021208343021208313020e08313020e08b03005850a0820c8c0a0820541c90820c8c09082 (by decide +kernel)

def state183_12 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,input 5,0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 7,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_12 : Impossible true (goalAt 183) 6 state183_12.toFinset :=
  node_ok cuts183 [⟨state183_6,exclude183_6⟩,⟨state183_11,exclude183_11⟩] 0xd0c084822120834300d0c084822120832302120834300d0c084822120834300d0c084822120834300d0c0848220e0884820545083820c4c0838220e0831300c4c0838220e08313020e0831300c4c0838220e0831300c4c0838220e0831300c4c083822c0c0a0222141ca0220d050323005850323005850a0820c888a0228000032220c8c032220c8c100040d05032220905090822808885072808885070c8c200010c8c1000b (by decide +kernel)

def state183_13 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0c0c0c0c0f0f0f0f0c0c0c0c,input 5,0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 7,input 0,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_13 : Impossible true (goalAt 183) 5 state183_13.toFinset :=
  node_ok cuts183 [] 0x32222420890820c88832302420890820441c908228208322224208838224208313020e08313020e0883820c4c0313020e0883820c4c0838228208313020e08b03028088a0822820834140c8c0a08228208161421208343024208848220e08151420e0884820d0c084822120834300c8c08482212083430212083430282088482 (by decide +kernel)

def state183_14 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffccccccccffffffffcccccccc,input 5,0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 7,input 0,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_14 : Impossible true (goalAt 183) 6 state183_14.toFinset :=
  node_ok cuts183 [⟨state183_13,exclude183_13⟩] 0x32222420890820c88832302420890820541490822820832222420815052420890820541484822420834302120834302120884820d0c034302120884820c8c084822820834302120a000021208848240020838224208313020e08838221208151420e08313020e0883820c4c0313020e0883820c4c0838228208313020e08151420e08838205450b0304001c161428088a0822820827070c8c0a082048c03414 (by decide +kernel)

def state183_15 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f00000000,input 5,input 7,0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 0,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_15 : Impossible true (goalAt 183) 5 state183_15.toFinset :=
  node_ok cuts183 [] 0x32302420890820441c32222420890820c888908228208322224208838224208313020e08313020e0883820c4c0313020e0883820c4c0838228208313020e08b0300c8c0a08228208161428088a08228208341421208343024208848220e08151420e0884820c8c084822120834300d0c08482212083430212083430282088482 (by decide +kernel)

def state183_16 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,input 7,0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 0,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_16 : Impossible true (goalAt 183) 6 state183_16.toFinset :=
  node_ok cuts183 [⟨state183_15,exclude183_15⟩] 0xc8c090822420815070c888908224208322224208a0820c888908205c1c90822420817072120890820d0c084820d0c084822120832300d0c0848221208343021208a0820d0c0848280000848221209000820e0890820c4c0838220e0884820545083820c4c0838220e0831300c4c0838220e08313020e08a0820c4c0838205450838220e0815140585032300c8c016142c0c085070c8c0a08228208161428088a0824001c3414 (by decide +kernel)

def state183_17 : List Sig := [0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 7,input 0,input 2,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_17 : Impossible true (goalAt 183) 7 state183_17.toFinset :=
  node_ok cuts183 [⟨state183_7,exclude183_7⟩,⟨state183_8,exclude183_8⟩,⟨state183_9,exclude183_9⟩,⟨state183_10,exclude183_10⟩,⟨state183_12,exclude183_12⟩,⟨state183_14,exclude183_14⟩,⟨state183_16,exclude183_16⟩] 0x40030a0220d050a0224001c850728208a08280018a02228208a0824001c85070d05034144002c32300d05032304001c161428208a08280014323028208a0824001c16140d05016144001c341424208908240010a0820c888a0828001034140c88832224001ca0822420890824003200010c888322240010a0222420890828000e000024208908240030a0220c88832224002c32300541432304001100042420890828000832302420890824001100040541415074001c341421208848240020a0820d0c0a0824003c34140d0c034304001ca0822120884824001017072120884824002090820d0c090824002417070d0c034304001090822120884824003085070d0c0343040020a02221208848240038850721208848240030a0220d0c034304002c16140d0c034304002032302120884824003416142120884824002032300d0c032304001c270720e08838240014a0820c4c0a0824002827070c4c031304001ca08220e08838240010170720e0883824001490820c4c090824001817070c4c0313040014908220e08838240021000a20e08838240014848205450848240029000a05450151440014848220e0883824003085070c4c0313040014a02220e08838240028850720e08838240030a0220c4c031304002d000a0c4c0313040014323020e08838240029000a20e0883824001432300c4c0313040001000040000b030 (by decide +kernel)

def state183_18 : List Sig := [0xffffffffffffffffffffffffffffffff33333333333300003333333333330000,input 7,input 4,input 5,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_18 : Impossible true (goalAt 183) 5 state183_18.toFinset :=
  node_ok cuts183 [] 0x84822820834302120884822420834302120834302120884820d0c024222120884820c8c0838221208151420e08838228208313020e08838224208313020e08313020e0883820c4c0232220e0883820c8c0b03028208a082240c0323028208a08205850908228208322224208b030242089082280c032302420890820c888a022 (by decide +kernel)

def state183_19 : List Sig := [0x3333333333330000333333333333000033333333333300003333333333330000,input 4,input 5,input 0,input 2,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_19 : Impossible true (goalAt 183) 6 state183_19.toFinset :=
  node_ok cuts183 [⟨state183_11,exclude183_11⟩,⟨state183_18,exclude183_18⟩] 0x2505034300d0c0b03021208848225050848221208b0300d0c034300d050848221208a2820d0c0a2820d05034300d0c0a28221208848205c1c84822120892820d0c0928205c1c34300d0c092822120884822141c31300c4c0b03020e0883822141c838220e08b0300c4c0313040018838220e08848205450848240018151405450848220e08838209c1c838220e08a2820c4c0a28209c1c31300c4c0a28220e08838205c1c838220e0892820c4c0928205c1c31300c4c0928220e0883822c0c034142c0c0941428a08a2822c0c0a28228a0894140d05090302c0c032222c0c0a22224a0892822c0c0928224a08a2220c888a0300d050928224a08a2820c888a2820d05032220c888a28224a0892822c0c032300c8c0a22280000a0222c0c200012c0c0a2220c8c032300d0c032300c8c084820585084820d0c016140d0c084820c8c084820c4c032300c4c083824001883820c4c100060c4c083820c8c083820d050161428208a2820c8c0a0820d05032300c8c0a28205850a2824001d00002420892820c8c090824001c32300c8c09282400009282 (by decide +kernel)

def state183_20 : List Sig := [0x5555555555555555555555555555555555555555555500005555555555550000,input 7,input 4,input 5,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_20 : Impossible true (goalAt 183) 5 state183_20.toFinset :=
  node_ok cuts183 [] 0x21a08a2820d0c0868221a0892820d0c086820d0c0868221a08343021a08848021208848228a08a08028208a08224a0890802420890820c8c0b0302808832302c0c0a28228a08903024a08a2820c88892822c0c0928224a08a03020e08151421a08838220608838220e08818020e08313028a08838220e08313024a0883820c4c0838220e083130 (by decide +kernel)

def state183_21 : List Sig := [0x3333333333333333333333333333333333333333333300003333333333330000,input 7,input 4,input 5,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_21 : Impossible true (goalAt 183) 5 state183_21.toFinset :=
  node_ok cuts183 [] 0x21a08a2820d0c0868221a0892820d0c086820d0c0868221a08343020e08868205450838220e08a2820c4c0838220e0892820c4c083820c4c0838220e0831302c0c0a28228a08903024a08a2820c88892822c0c0928224a08a03021208848221200868220608838220600838228208a08228200a2822420890822420092820c8c0a0222c0c03230 (by decide +kernel)

def state183_22 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0f0f0f0f0000,input 7,input 4,input 5,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_22 : Impossible true (goalAt 183) 5 state183_22.toFinset :=
  node_ok cuts183 [] 0x28a08a08028208a08224a0890802420890820c8c0b03028088323020600838220e08818220e08a2820c4c0838220e0892820c4c083820c4c0838220e0831302c0c0a28228a08903024a08a2820c88892822c0c0928224a08a03021208848221a08848020e08151420e08868221a08343028a08868221a08343024a0886820d0c0868221a083430 (by decide +kernel)

def state183_23 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffff0000ffffffffffff0000,input 7,input 4,input 5,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_23 : Impossible true (goalAt 183) 6 state183_23.toFinset :=
  node_ok cuts183 [⟨state183_20,exclude183_20⟩,⟨state183_21,exclude183_21⟩,⟨state183_22,exclude183_22⟩] 0x868228a08343021a08868224a08343021a08343021a0886820d0c2000221a08868240008868221200848221208a28228200a0822820892822420090822420832302c0c0a0220c8c200010c8c0323040000838221a08151420e08818020e08838220608838228a08313020e08838224a08313020e08313020e0883820c4c2000020e08838240004b03028a08a282240c0270724a08a2820c88892822c0c0928224a08a03005c1c8707 (by decide +kernel)

def state183_24 : List Sig := [0xffffffffffff0000ffffffffffff0000,input 7,input 4,input 5,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_24 : Impossible true (goalAt 183) 6 state183_24.toFinset :=
  node_ok cuts183 [⟨state183_11,exclude183_11⟩] 0x868228a08343021a08868224a08343021a08343021a0886820d0c0868221200848221208a28228200a0822820892822420090822420832302141485070c8c0838221a08151420e08818020e08838220608838228a08313020e08838224a08313020e08313020e0883820c4c0341428a08a2820d050928228a08322224a08322224a0892820c888343021a08343021a08323080000323040000313020e08313020e08341428a08341428a08322224a08322224a08b030 (by decide +kernel)

def state183_25 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 7,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 5,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_25 : Impossible true (goalAt 183) 6 state183_25.toFinset :=
  node_ok cuts183 [⟨state183_6,exclude183_6⟩] 0x21a0834300d0c0868221a0892820d0c086820d0c0868221a08343009888868221a08243021a0884802120884820585032300c8c0161424a0890802420890820c8c0a0308000032300c88832300c8c1000720e08868205450838220600838220e08818220e0831300c4c0838220e0892820c4c083820c4c0838220e08313008c88838220e08232228a08a030250509030240c032220d050322209050a03024a08928221050322224a0892824000ca222 (by decide +kernel)

def state183_26 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 7,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_26 : Impossible true (goalAt 183) 6 state183_26.toFinset :=
  node_ok cuts183 [] 0x21a0834300d0c0868221a08a2820d0c086820d0c0868221a0834300d050868221a09001021a0884802120884820c88832300c8c1000728a08a08028208a0820c8c090302808832300585032300c8c0161420e08868205450838220600838220e08818220e0831300c4c0838220e08a2820c4c083820c4c0838220e08313005450838220e08151424a089030248889030280c034140c888322209050903028a08a28240030341428a08a282400309414 (by decide +kernel)

def state183_27 : List Sig := [0x3333333333330000333333333333000033333333333300003333333333330000,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,input 5,input 0,input 2,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_27 : Impossible true (goalAt 183) 6 state183_27.toFinset :=
  node_ok cuts183 [] 0xd0c084822120834302120834300d0c084822120834300d0c084822120834300d0c084820c4c0838220e08313020e08848205450838220e0831300c4c0838220e0831300c4c0838220e0831300c4c083822c0c09414240c0903028a08b03028888a030280c034140c888241424a08b0302141cb0302141c323028088b0300c8c0323021208343021208313020e08313020e0816140c8c032300585100070c8c032300c8890000 (by decide +kernel)

def state183_28 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,input 5,input 0,input 1,input 2,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_28 : Impossible true (goalAt 183) 7 state183_28.toFinset :=
  node_ok cuts183 [⟨state183_12,exclude183_12⟩,⟨state183_19,exclude183_19⟩,⟨state183_23,exclude183_23⟩,⟨state183_24,exclude183_24⟩,⟨state183_25,exclude183_25⟩,⟨state183_26,exclude183_26⟩,⟨state183_27,exclude183_27⟩] 0x94140d0c034302c0c0868221a08941421a0886822c0c034300d0c0341421a0886824004034300d0c034140d0c034304000c868221a09001021a0886820c88834300d0c100100d0c034300c888868221a09001021a0886824000834300d0c100100d0c0343040008868221a08a2220c8c032302c0c100072c0c0a22280000a0222c0c032300c8c086820c8c086822120016142120086820585084822120032302120900030585016140d05032300c8c100070c8c032300d05016140585032224001032224001c32300c8c032220c8c032304001d00074001d00078001a00014000032300c8c100070c8c032304000100074000087070c4c031302c0c0838220e08870720e0883822c0c031300c4c1001020e08838221a08151421a09000605450151421a08838220e0900072060081800c8c0838220e09000620e0883820c8c0818020609000320e0883820d05031300c4c100060c4c031300d050838220e09000420e0883820c88831300c4c100060c4c031300c888838220e09000620e0883824000431300c4c100060c4c0313040004838220e08b0300d050b03025051000325050b030800149030250503414240c1000340010a2822c0c032222c0c0a22240010a2222c0c20004280c0a2220c888a0300d05100030d05100040c88832224000d00030905100034000c92822c0c1000c2c0c087078000c87072c0c200022c0c08707400308707 (by decide +kernel)

def state183_29 : List Sig := [0x3333333333333333333333333333333333330000333300003333000033330000,input 4,input 7,input 0,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_29 : Impossible true (goalAt 183) 6 state183_29.toFinset :=
  node_ok cuts183 [] 0x2c0c034142c0c0941428a08a2822c0c0a28228a0894140d05090300d050868221a08a2820d0c0a2820d05034300d0c0a28221a0886822505034300d0c0b03021a08868225050868221a08b0300d0c0343005c1c868221a0892820d0c0928205c1c34300d0c0928221a0886820941c838220e08a2820c4c0a2820941c31300c4c0a28220e08838240018838220e08868205450868240018151405450868220e08838221c1c31300c4c0b03020e08838221c1c838220e08b0300c4c0313005c1c838220e0892820c4c0928205c1c31300c4c0928220e0883820d050928224a08a2820c888a2820d05032220c888a28224a0892822c0c032222c0c0a22224a0892822c0c0928224a08a2220c888a03028200161428208a2820c8c0a08228200323028200a28205850a2822120032302120886820585084822120016142120086820c8c086822060032302060883824001883822060100062060083820c8c083822c0c032300c8c0a22240010a0222c0c100042c0c0a2220c8c032302420100002420892820c8c09082242003230242009282400009282 (by decide +kernel)

def state183_30 : List Sig := [0x3333333333333333333333333333333333330000333300003333000033330000,0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 4,input 7,input 0,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_30 : Impossible true (goalAt 183) 6 state183_30.toFinset :=
  node_ok cuts183 [] 0x2c0c0a28228a0890300941ca28228a08250721a08a2820d0c086820d0c0868221a08343021a0892820d0c0868209088868221a08242220e08a2820c4c0838220e0886820545083820c4c0838220e08313020e0892820c4c0838208c88838220e08232228888928228a08341424a08b03024a08a0300c888a08228208a08028a08848221208848021a08818220e08818020e08323040010b0300c8c0908224208908024a090000 (by decide +kernel)

def state183_31 : List Sig := [0xffffffff00000000ffffffff00000000ffff000000000000ffff0000,input 5,input 4,input 7,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_31 : Impossible true (goalAt 183) 6 state183_31.toFinset :=
  node_ok cuts183 [] 0x343021a0886820d0c0868224a08343021a0886820d0c0343021a0886822120084822120832302c0c0a0220c8c092822420090822420816140c8c0323005850838221a08151420e08818020e08838220608313020e0883820c4c0838224a08313020e0883820c4c0313020e08b03024a089282280c092820c888322224a08b03025050b0302505086820d0c086820d0c016140c8c016140c8c083820c4c083820c4c094142c0c094142c0c092820c88892820c888a282 (by decide +kernel)

def state183_32 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 4,input 7,input 0,input 1,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_32 : Impossible true (goalAt 183) 7 state183_32.toFinset :=
  node_ok cuts183 [⟨state183_25,exclude183_25⟩,⟨state183_7,exclude183_7⟩,⟨state183_10,exclude183_10⟩,⟨state183_23,exclude183_23⟩,⟨state183_29,exclude183_29⟩,⟨state183_30,exclude183_30⟩,⟨state183_31,exclude183_31⟩] 0xb0300d050b03025050a28228a08b03028a08a282250503414240c2000609c1c27074000ca28228a0a000328a08a2824000c270709c1c341421a08868228a08343028a0834140d0c0343028a08868221a0894140d0c034302c0c0868221a08941421a0886822c0c034300d0c1000421a08868224a08343024a0900090d0c0343024a08868221a09000909888262240008868221a09000921a08868240008262209888a28205850a28228200323028200a2820c8c0a0822820016142820886820c8c086822120016142120086820585084822120032302120900040c8c032302c0c100042c0c100048000a00012c0c032300c8c092824001092822420032302420092820c8c090822420100042420900048001600044000032300c8c100040c8c0323040001000440000270720e08838228a08313028a0827070c4c0313028a08838220e09000620e08838221a08151421a09000605450151421a08838220e0900042060081800c8c0838220e09000620e0883820c8c081802060900060c4c031302c0c0838220e09000620e0883822c0c031300c4c1000420e08838224a08313024a0900060c4c0313024a08838220e09000608c88232240004838220e09000620e08838240004232208c89000440010a2220d050928224a08a28240010a2820d05200000d050a28224a0892822c0c1000c2c0c1000424a08928240011000c280c1000c400303222 (by decide +kernel)

def state183_33 : List Sig := [0xccccffffccccffffccccffffccccffffcccccccccccccccccccccccccccccccc,input 4,input 7,input 0,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_33 : Impossible true (goalAt 183) 6 state183_33.toFinset :=
  node_ok cuts183 [] 0x2c0c034142c0c0941428208a0822c0c0a0822820894140d05090300d050848221208a0820d0c0a0820d05034300d0c0a0822120884822505034300d0c0b03021208848225050848221208b0300d0c0343005c1c84822120892820d0c0928205c1c34300d0c0928221208848209c1c838220e08a0820c4c0a08209c1c31300c4c0a08220e08838240018838220e08848205450848240018151405450848220e0883822141c31300c4c0b03020e0883822141c838220e08b0300c4c0313005c1c838220e0892820c4c0928205c1c31300c4c0928220e0883824001831300c4c0323020e08838240018838220e0832300c4c031300d050928224a08a0820c888a0820d05032220c888a08224a0892822c0c032222c0c0a02224a0892822c0c0928224a08a0220c88832222820816142820834140c8c032302820832302820834140585016142120832302120834300585034302120816142120834300c8c032302808832300c8c0b03040000b03028089000028088b0300c8c0323024a09000024a0815050c8c0323024a083230242081505400009082 (by decide +kernel)

def state183_34 : List Sig := [0xf0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f000000000f0f0f0f00000000,input 5,input 4,input 7,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_34 : Impossible true (goalAt 183) 5 state183_34.toFinset :=
  node_ok cuts183 [] 0xc8c0b0302808832300c88832300c8c0110728a08a08028208a08220600838220e0881820c4c0838220e08313020e0831300c4c0838220e08a2820c4c083822c0c0a222280c0a0302ca08a2820c888a2822c0c0a28228a08341421208848221a08848020e08151420e0886820d0c0868221a08343021a08343024a08868221a08343028a088682 (by decide +kernel)

def state183_35 : List Sig := [0xffffffff0000ffffffffffff0000ffffffffffff00000000ffffffff00000000,input 5,input 4,input 7,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_35 : Impossible true (goalAt 183) 6 state183_35.toFinset :=
  node_ok cuts183 [⟨state183_34,exclude183_34⟩] 0x343021a0886820d0c086820d0c0343021a08868228a08343021a0a000021a0886824000886822120084822120832302c0c0a0220c8c032220c8c032300541ca28228200a0822820816140c8c0323005850838221a08151420e08818020e08838220608313020e0883820c4c083820c4c0313020e08838228a08313020e08151420e08838205450b03028888a030280c0b28228a08322228a0817070c888928224a08b03028a08a2822505034142c0c094142c0c09414 (by decide +kernel)

def state183_36 : List Sig := [0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000,input 4,input 7,input 0,input 1,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_36 : Impossible true (goalAt 183) 7 state183_36.toFinset :=
  node_ok cuts183 [⟨state183_8,exclude183_8⟩,⟨state183_33,exclude183_33⟩,⟨state183_35,exclude183_35⟩] 0xb0300d050b03025050a28228a08b03028a08a282250503414240c0341421a08868228a08343028a0834140d0c0343028a08868221a0894140d0c034302c0c0868221a08941421a0886822c0c034300d0c0170721a0886820c88834300d0c017070d0c034300c888868221a08a28205850a28228200323028200a2820c8c0a0822820016142820886820c8c0868221200161421200868205850848221200323021209000c0c8c032302c0c1000c2c0c100044003200002c0c032300c8c032224001032220541432300c8c032220c8c032300541500040541c270720e08838228a08313028a0827070c4c0313028a08838220e09000620e08838221a08151421a09000605450151421a08838220e0900042060081800c8c0838220e09000620e0883820c8c0818020609000c0c4c031302c0c0838220e09000620e0883822c0c031300c4c0170720e0883820c88831300c4c017070c4c031300c888838220e08341405c1c341428a08322228a0834140c888322228a08170728a09000440030b2222c0c1000c2c0c1000c0c888322228a09000328a08341440030341428a0a000228a0834144000c341421a09000221a08343040030343021a09000921a08343040008343040031000040000323040030323040031000480004323040000323020e09000120e08313040030313020e09000620e08313040004313040031000c28889000c400109282 (by decide +kernel)

def state183_37 : List Sig := [0xafafafafafafafafafafafafafafafafafafafafaaaaaaaaafafafafaaaaaaaa,input 0,input 5,input 7,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_37 : Impossible true (goalAt 183) 5 state183_37.toFinset :=
  node_ok cuts183 [] 0xb03024a089282280c0928228a08322224a0892822420090822420832302c0c0a0220c8c0a28228200a08228208b03028a08a282240c0838224a08313020e08818020e08838221608313020e0883820c4c0838228a08313020e08151421a08343024a08868221208848221a0884800d0c0868221a08343021a08343028a088682 (by decide +kernel)

def state183_38 : List Sig := [0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,0x505050505050505050505050505050505050505000000000505050500000000,input 5,input 7,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_38 : Impossible true (goalAt 183) 4 state183_38.toFinset :=
  node_ok cuts183 [] 0x2c0c0928224a08a03024a08a2820c88892822c0c0a28228a08903020e0834302460883820d0c0838220e08343020e08343028608838221208838220e08818024a0890802420890820c8c0b03028088323028a08a08028208a082 (by decide +kernel)

def state183_39 : List Sig := [0x505050505050505050505050505050505050505000000000505050500000000,input 0,input 5,input 7,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_39 : Impossible true (goalAt 183) 5 state183_39.toFinset :=
  node_ok cuts183 [⟨state183_38,exclude183_38⟩] 0xb03024a089282280c0928228a08322224a0892822420090822420832302c0c0a0220c8c0a28228200a08228208b03028a08a282240c0130724a08151424a0815140c8c200000c8c015142c0c083072c0c0151428a08230728a0886820d0c0928221a08848221208868221200343021a0886820d0c086820d0c0a28221a088382 (by decide +kernel)

def state183_40 : List Sig := [0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f00000000,input 5,input 7,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_40 : Impossible true (goalAt 183) 5 state183_40.toFinset :=
  node_ok cuts183 [⟨state183_38,exclude183_38⟩] 0xb03024a089282280c0928228a08322224a08b03028a08a282240c086820d0c0928221a08343021a0886820d0c086820d0c0a28221a08838280000838221608848221208868221200838224608110720e08232220e0883822c0c0838228608232220e08818024a0890802420890820c8c0b03028088323028a08a08028208a082 (by decide +kernel)

def state183_41 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f00000000,input 5,input 7,input 0,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_41 : Impossible true (goalAt 183) 6 state183_41.toFinset :=
  node_ok cuts183 [⟨state183_15,exclude183_15⟩,⟨state183_1,exclude183_1⟩,⟨state183_37,exclude183_37⟩,⟨state183_39,exclude183_39⟩,⟨state183_40,exclude183_40⟩] 0x2c0c032222c0c0a22224a0892822c0c0928224a08a2220c888a0300d050928224a08a2820c888a2820d05032220c888a28224a08928224a0a000124a0890800c8c0908024a0832302420890804003c90822888832300c8c0b0304003cb0302888a000028088b0300c8c0323028a08161428a08a0800c8c0a08028a08323028208a08005850a08204c1c838220e0892820c4c0928204c1c31300c4c0928220e0883824003c818020600323020e08838280010838220e08323020600818221c1c31300c4c0b03020e08838221c1c838220e08b0300c4c0313009c1c838220e08a2820c4c0a28209c1c31300c4c0a28220e0883822c0c034142c0c0941428a08a2822c0c0a28228a0894140d050903024a08868221a0813070d0c0343024a08343024a08130721a0886820c8c0848021208161421a0884820c8c0868221a08161421200848020e08868220e0815148000c151420e0a000220e08151421a0886822c0c034300d0c0941421a0886822c0c0868221a0894140d0c0343028a08868221a0834140d0c0343028a08343028a08341421a088682 (by decide +kernel)

def state183_42 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f00000000,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,input 7,input 0,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_42 : Impossible true (goalAt 183) 6 state183_42.toFinset :=
  node_ok cuts183 [] 0x2c0c0928224a08a03024a08a2820c888928204c1c928224a08130724a0890802420890820c8c0b03028088323028a08a08028208a0820585032300c8c0161420e0892820c4c0838220600838220e0881820c4c0838220e08313020e08a2820c4c0838205450838220e08151425050b03028a0890300d05086820d0c0928221a08848221208868221200838205450838221a08343021a0886820d0c086820d0c0a28221a090002 (by decide +kernel)

def state183_43 : List Sig := [0xccccffffccccffffccccffffccccffffccccffffccccccccccccffffcccccccc,input 4,input 5,input 7,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_43 : Impossible true (goalAt 183) 5 state183_43.toFinset :=
  node_ok cuts183 [] 0xd0c0848221208343021208a0820d0c084822120892820d0c0848220e0884820545083820c4c0838220e08313020e08a0820c4c0838220e0892820c4c083820c4c0838220e0831302c0c0a0822820890302c0c0928224a08322224a08a0820c88892822120834302120832300c8c0b03028088323028208323028208161424a083230242089082 (by decide +kernel)

def state183_44 : List Sig := [0xffff0000ffff0000ffff0000ffff0000ffff000000000000ffff00000000,input 4,input 5,input 7,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_44 : Impossible true (goalAt 183) 6 state183_44.toFinset :=
  node_ok cuts183 [⟨state183_43,exclude183_43⟩] 0x343021a0886820d0c0868228a08343021a0886820d0c0343021a0886822120084822120832302c0c0a0220c8c0a28228200a0822820817070c8c032300541c838221a08151420e08818020e08838220608313020e0883820c4c0838228a08313020e0883820c4c0313020e08b03028a08a282240c0b03028888b03028888341428a08341428a0886820d0c086820d0c100000c8c200000c8c083820c4c083820c4c0a2222c0c0a2222c0c0a2820d050a2820d0509282 (by decide +kernel)

def state183_45 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,input 7,input 0,input 1,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_45 : Impossible true (goalAt 183) 7 state183_45.toFinset :=
  node_ok cuts183 [⟨state183_16,exclude183_16⟩,⟨state183_2,exclude183_2⟩,⟨state183_23,exclude183_23⟩,⟨state183_26,exclude183_26⟩,⟨state183_41,exclude183_41⟩,⟨state183_42,exclude183_42⟩,⟨state183_44,exclude183_44⟩] 0xb0300c888b03028888928224a08b03024a089282288883222280c1000324a08928228a08322228a0a00030c888322228a08928224a0a000605c1c170740010928224a0a000224a08928240010170705c1c170721a08868224a08343024a0817070d0c0343024a08868221a0900100d0c034302c0c0868221a09001021a0886822c0c034300d0c1000321a08868228a08343028a0900100d0c0343028a08868221a09001080016000440008868221a09001021a0886824000900104000892828000492822420032302420092820c8c090822420100072420886820c8c0868221200161421200868205850848221200323021208a2220c8c032302c0c100072c0c0a22280000a0222c0c032300c8c0a28205850a28228200323028200a2820c8c0a0822820016142820900070585016144000032300c8c100070c8c0323040000161405850170720e08838224a08313024a0817070c4c0313024a08838220e09001020e08838221a08151421a09001105450151421a08838220e0900072060081800c8c0838220e09001120e0883820c8c081802060900110c4c031302c0c0838220e09001120e0883822c0c031300c4c1000320e08838228a08313028a0900110c4c0313028a08838220e09001105450151440004838220e09001120e0883824000415140545100034000c94142c0c1000c2c0c1000328a08a2824000d0003240c10003400303414 (by decide +kernel)

def state183_46 : List Sig := [0xfafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafa,0xeeeeeeeeffffffffeeeeeeeeffffffffeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 5,input 7,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_46 : Impossible true (goalAt 183) 4 state183_46.toFinset :=
  node_ok cuts183 [] 0x2c0c0908224208a03024208a2820c88890822c0c0a28228a0834142420832302420900060c8c0b03028088323028a08323028208a08220e08313020e08323020e0890820d0c083820d0c0838220e08343020e08a1820d0c08382 (by decide +kernel)

def state183_47 : List Sig := [0xeeeeeeeeffffffffeeeeeeeeffffffffeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 0,input 5,input 7,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_47 : Impossible true (goalAt 183) 5 state183_47.toFinset :=
  node_ok cuts183 [⟨state183_46,exclude183_46⟩] 0xb030242089082280c0908228a0832222420884822420834302120834302120884820d0c0848228a08343021208b03028a08a2820d050838224208150720e0883822120a000020e08232220e0883822c0c0838228608232220e0831302420832302420900042120834302120832300c8c0b03028088323028a08323028208a082 (by decide +kernel)

def state183_48 : List Sig := [0xfafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafa,input 0,0xccccccccffffffffccccccccffffffffcccccccccccccccccccccccccccccccc,input 5,input 7,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_48 : Impossible true (goalAt 183) 5 state183_48.toFinset :=
  node_ok cuts183 [⟨state183_46,exclude183_46⟩] 0xb030242089082280c0908228a08322224208b03028a08a2820d05090820c8c090820441c32302c0c0a0220c8c0a2820c8c0a0822820884820d0c084820c8c013072420815142420815142c0c081072c0c0151428a08230728a0815140c8c200000c8c083822120890820d0c084820d0c0848221208343021208a2820d0c08482 (by decide +kernel)

def state183_49 : List Sig := [0xccccccccffffffffccccccccffffffffcccccccccccccccccccccccccccccccc,input 5,input 7,input 0,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_49 : Impossible true (goalAt 183) 6 state183_49.toFinset :=
  node_ok cuts183 [⟨state183_47,exclude183_47⟩,⟨state183_48,exclude183_48⟩] 0x2c0c032222c0c0a2222420890822c0c0908224208a2220c888a0300d050908224208a2820c888a2820d05032220c888a28224208908205c1c84822120890820d0c0908205c1c34300d0c090822120884822141c34300d0c0b0302120884822141c848221208b0300d0c034300d050848221208a2820d0c0a2820d05034300d0c0a28221208848205c1c838220e0890820c4c0908205c1c31300c4c0908220e0883824003c838220e08848205450848280004151405450848220e0883822141c31300c4c0b03020e0883822141c838220e08b0300c4c0313009c1c838220e08a2820c4c0a28209c1c31300c4c0a28220e0883824002c31300c4c0323020e08838280000838220e0832300c4c031302c0c034142c0c0850728a08a2822c0c0a28228a0885070d05034142420900042420815050c8c032302420832302420815054001015072120832302120834300585034302120816142120834300c8c032302888832300c8c0b03040000b03028889000028088b0300c8c0323028a08161428a0834140c8c0323028a08323028208341405850a082 (by decide +kernel)

def state183_50 : List Sig := [0x3333000033333333333300003333333333330000333300003333000033330000,input 4,input 5,input 7,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_50 : Impossible true (goalAt 183) 5 state183_50.toFinset :=
  node_ok cuts183 [] 0xd0c0868221a08343021a08a0820d0c0868221a0892820d0c0868220e0886820545083820c4c0838220e08313020e08a0820c4c0838220e0892820c4c083822c0c0a0822820890302c0c0928224a08322224a08a0820c88892822120884822120086822060883822060083820c8c0a0222c0c0323005850a08228200a082242089082242009282 (by decide +kernel)

def state183_51 : List Sig := [0xffff0000ffffffffffff0000ffffffffffff0000ffff0000ffff0000ffff0000,input 4,input 5,input 7,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_51 : Impossible true (goalAt 183) 6 state183_51.toFinset :=
  node_ok cuts183 [⟨state183_50,exclude183_50⟩] 0x343021a0886820d0c086820d0c0343021a08868224a08343021a08262221a0886820988886822120084822120832302c0c0a0220c8c016140c8c032300585092822420090822420a00000c8c0323040000838221a08151420e08818020e08838220608313020e0883820c4c083820c4c0313020e08838224a08313020e08232220e08838208c88b030250509030240c0b03024a0892822888892822ca08341424a0832222c0c0a2222c0c0a2220d050270728a08a282 (by decide +kernel)

def state183_52 : List Sig := [0xffffffff00000000ffffffff00000000000000000000000000000000,input 5,input 7,input 0,input 1,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_52 : Impossible true (goalAt 183) 7 state183_52.toFinset :=
  node_ok cuts183 [⟨state183_4,exclude183_4⟩,⟨state183_49,exclude183_49⟩,⟨state183_51,exclude183_51⟩] 0xb0300c888b03028888928224a08b03024a089282288883222280c0341424a08928209c1c32220c88834140c888322209c1c928224a08170721a08868224a08343024a0817070d0c0343024a08868221a09000c0d0c034302c0c0868221a09001021a0886822c0c034300d0c0341421a08868208c0c34300d0c034140d0c0343008c0c868221a0892828000092822420032302420092820c8c090822420100072420886820c8c0868221200161421200868205850848221200323021208a2220c8c032302c0c100072c0c0a22240030a0222c0c032300c8c027070585016140d05032300c8c027070c8c032300d050161405850170720e08838224a08313024a0817070c4c0313024a08838220e09001020e08838221a08151421a09001205450151421a08838220e0900072060081800c8c0838220e09001220e0883820c8c0818020609000c0c4c031302c0c0838220e09001220e0883822c0c031300c4c0270720e0883820d05031300c4c027070c4c031300d050838220e0900034000cb4142c0c1000c2c0c100030d050341424a09000424a08322240030322224a0a000224a08322240030322221a09000221a08343040030343021a09001021a0834304000834304001d00004000032304001c323040031000780004323040000323020e09000120e08313040030313020e09001220e0831304000431304000d000325051000c4000ca282 (by decide +kernel)

def state183_53 : List Sig := roots 183
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_53 : Impossible true (goalAt 183) 8 state183_53.toFinset :=
  node_ok cuts183 [⟨state183_5,exclude183_5⟩,⟨state183_17,exclude183_17⟩,⟨state183_28,exclude183_28⟩,⟨state183_32,exclude183_32⟩,⟨state183_36,exclude183_36⟩,⟨state183_45,exclude183_45⟩,⟨state183_52,exclude183_52⟩] 0x80018b0300d050b0304000c941428a08a28280014b03028a08a2824000c94140d050903080010b0300c888b03040010a22224a0892828000cb03024a08928240010a2220c888a0304000c341424a08928240010a2820c888a2828000834140c88832224000ca28224a0892824000894140d0c0343040008b03021a08868240008941421a08868240008b0300d0c0343040008341421a08868240008a2820d0c0a2824000834140d0c0343040008a28221a08868240008170721a0886824000892820d0c092824000817070d0c0343040008928221a08868240000a2220c8c0323040000b03040000b03040000a22280004a02240000b0300c8c0323040000a28205850a28240000a0800c8c0a08040000a2820c8c0a08240000a08005850a0824000092828000092824000090800c8c090804000092820c8c090824000090804000090824000086820c8c086824000084800585084804000086820585084824000084800c8c084824000487070c4c0313040004b03020e08838240004870720e08838240004b0300c4c0313040004270720e08838240004a2820c4c0a2824000427070c4c0313040004a28220e08838240004170720e0883824000492820c4c092824000417070c4c0313040004928220e08838240005000120e08838240004868205450868240005000105450151440004868220e08838240001000020600818040000323020e08838240001000120e088382400003230206008182 (by decide +kernel)

theorem lower183 : Claim 183 9 :=
  fromSearch 1348 (by decide +kernel) exclude183_53

theorem lower225 : Claim 225 5 :=
  fromLift 5 64 83886085 lower161 (by decide +kernel)

theorem lower241 : Claim 241 6 :=
  fromLift 6 16 67108868 lower225 (by decide +kernel)

def cuts99 : Cuts (goalAt 99) := []

def state99_0 : List Sig := roots 99
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude99_0 : Impossible true (goalAt 99) 3 state99_0.toFinset :=
  node_ok cuts99 [] 0x18888614118504422218888434110d04602210d0461410840c434108c8862221080c232218504604018104604110d044240109044241 (by decide +kernel)

theorem lower99 : Claim 99 4 :=
  fromSearch 16777317 (by decide +kernel) exclude99_0

def rule227_0 : {c : Cut // CutGood (goalAt 227) c} :=
  ruleFor 227 lower225 none (by decide +kernel)

def rule227_1 : {c : Cut // CutGood (goalAt 227) c} :=
  ruleFor 227 lower226 none (by decide +kernel)

def rule227_2 : {c : Cut // CutGood (goalAt 227) c} :=
  ruleFor 227 lower161 none (by decide +kernel)

def rule227_3 : {c : Cut // CutGood (goalAt 227) c} :=
  ruleFor 227 lower99 none (by decide +kernel)

def cuts227 : Cuts (goalAt 227) := [rule227_0,rule227_1,rule227_2,rule227_3]

def state227_0 : List Sig := [0xffffffffcccccccc0000000000000000ffffffffcccccccc,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 5,input 0,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_0 : Impossible true (goalAt 227) 4 state227_0.toFinset :=
  node_ok cuts227 [] 0x20504c1c030700232230700a08208c88c1c030700c2c020e08c1c028088a08228208814138300434130b00c2c010a00428230a08c28220504838230700838230700a08210888a08230a090002 (by decide +kernel)

def state227_1 : List Sig := [0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 5,input 0,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_1 : Impossible true (goalAt 227) 5 state227_1.toFinset :=
  node_ok cuts227 [⟨state227_0,exclude227_0⟩] 0xc14118088c14128088c28230a08c14130a08c28228088602210a08c14108c88c14128088c1c030700c14130700c1c028088232208c88430320e08838230a08c1c030700430330700c1c030a08838220e08210330700c1c028208232228208210308c88232228208c1c030700434130700c1c030b00838230b00434120e08838230b00c1c030700a0220840ca02230504a08228208a02228208a08230504210330504602228208a08230a09000230a08602240008422230a08a08228209000040000e0c028088434110d04c14130b00c2c028088c2c030b00c14110d0442c030a09000230a0a000030b00c2c030a08c2c030b010002400090002 (by decide +kernel)

def state227_2 : List Sig := [0xffffffffaaaaaaaaffffffffaaaaaaaa,input 0,input 5,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_2 : Impossible true (goalAt 227) 4 state227_2.toFinset :=
  node_ok cuts227 [] 0x30a08c2c030b00602230b00e0c028208c2c028a08e0c038300a0c020e08c1c030700838230700c2c020e08c1c030700e0c018104c1c020504c28230504c28210d04c2c010d04c2c018300e0c018504e0c008c88c1c030504c1c0 (by decide +kernel)

def state227_3 : List Sig := [0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,input 0,input 5,input 1,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_3 : Impossible true (goalAt 227) 5 state227_3.toFinset :=
  node_ok cuts227 [⟨state227_2,exclude227_2⟩] 0xc14130a08c28210a08434130b00c2c010b00c28230b00c2c018088c2c018504210330b00c2c010d04434130b00614130504a22218504622230a08614130a08e0c030504a22230504232208c88c28210c0cc28210d04c2c010d04c2c018504232218104c1c030506000030505000318888c28218888c282 (by decide +kernel)

def state227_4 : List Sig := [0xddddddddccccccccddddddddccccccccddddddddccccccccddddddddcccccccc,input 0,input 5,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_4 : Impossible true (goalAt 227) 4 state227_4.toFinset :=
  node_ok cuts227 [] 0x30504c28230a08428218504a08228208614128208c28218504a08230504c1c030700232220e08c1c030700838230700e1c018504c1c030700c2c020e08c1c010d04c2c030b0042c030a08c2c030b01000230b00e0c028208c2c0 (by decide +kernel)

def state227_5 : List Sig := [0x5555555500000000555555550000000055555555000000005555555500000000,input 0,input 5,input 1,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_5 : Impossible true (goalAt 227) 5 state227_5.toFinset :=
  node_ok cuts227 [⟨state227_4,exclude227_4⟩] 0xc14130a08c28210a08434130b00c2c010b00c28230b00c2c018088c2c018504210330b00614130504a22218504622230a08614130a08c14130700c1c028888838230700c1c020e08c1c030b00838230700e1c018504c1c028888c14128888c14118888c28218888c28240000c2c080000c2c0383002322 (by decide +kernel)

def state227_6 : List Sig := [0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 0,input 7,input 1,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_6 : Impossible true (goalAt 227) 5 state227_6.toFinset :=
  node_ok cuts227 [] 0xc14130a08c28220504622230a08c28218888a28238300e0c028300614138300e0c018504604038300e0c018100c28230b00c2c018088c2c038300a08230b00434130b00c2c010d04424030b00c2c010900a22220e08c1c030700838230700e0c018504c1c030700c2c020e08c1c030504c1c0400042322 (by decide +kernel)

def state227_7 : List Sig := [0x5555555555555555555555555555555555555555000000005555555500000000,input 5,input 7,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_7 : Impossible true (goalAt 227) 4 state227_7.toFinset :=
  node_ok cuts227 [] 0x30504c28230a08814130a08c2c030b00602210904c2c030b00424130b00e0c028208c2c028a08e0c038300a0c018504e0c03830060c020e08c1c030700838230700838230b00c1c008c88c1c030700c14130700604138300c1c0 (by decide +kernel)

def state227_8 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,input 7,input 0,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_8 : Impossible true (goalAt 227) 5 state227_8.toFinset :=
  node_ok cuts227 [⟨state227_7,exclude227_7⟩] 0x622230a08c28218888430330a08c28210c0cc28230b00c2c018088434130b00c2c010d04c2c038300a08230b00434130b00c2c010d04838230700c1c020e08c1c030b00838230700232230700c1c008c88c1c038300232230702000030700c1c040004c14128a08e0c038300a0c028888e0c0183006141 (by decide +kernel)

def state227_9 : List Sig := [0xccccccccccccccccccccccccccccccccffffffffccccccccffffffffcccccccc,input 5,input 7,input 0,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_9 : Impossible true (goalAt 227) 4 state227_9.toFinset :=
  node_ok cuts227 [] 0x30504c28230a08428220e08c1c030700838230504c1c030700232230700e0c008c88c1c030700c2c020e08c1c028a08e0c038300a0c038504e0c038300c14130a08c2c030b01000210d04c2c030b0042c030b00e0c028208c2c0 (by decide +kernel)

def state227_10 : List Sig := [0xffffffff00000000ffffffff00000000,input 5,input 7,input 0,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_10 : Impossible true (goalAt 227) 5 state227_10.toFinset :=
  node_ok cuts227 [⟨state227_9,exclude227_9⟩] 0xc14130a08c28210a08c28230b00c2c018088434130b00c2c010b00c2c038300a08230b00838230700c1c020e08c1c030b00838230700c14130700c1c008c88c1c038300232230700a28238300e0c028300e14138300c14118888c28218888c28240000c2c080000c2c008c88c1c008c88c1c0288886141 (by decide +kernel)

def state227_11 : List Sig := roots 227
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude227_11 : Impossible true (goalAt 227) 6 state227_11.toFinset :=
  node_ok cuts227 [⟨state227_1,exclude227_1⟩,⟨state227_3,exclude227_3⟩,⟨state227_5,exclude227_5⟩,⟨state227_6,exclude227_6⟩,⟨state227_8,exclude227_8⟩,⟨state227_10,exclude227_10⟩] 0x40008c14118888c14140008a22230a08c28240008c14130a08c28240008a2221888842824000ca22218504614180014c14138300e0c080010a22238300e0c04000cc1411850460c040008622228a08a28240008c28238300e0c040008622238300e0c040008c28228a08a0c040000a22210d04434140000c14130b00c2c040000a22230b00c2c040000c14110d0442c040000c28240008c28240000602030b00c2c040000c28230b00c2c040000602040000602240000a28230b00c2c040000e0c040000e0c040000a28280000a08240000e0c030b00c2c04000cc14108c88c14140004a22230700c1c08000cc14130700c1c040004a22208c88232240008430320e08838240004c28230700c1c040008430330700c1c040004c28220e08838280008614130700c1c040004e0c008c88e0c080004614108c88604140004e0c030700c1c040000434130700c1c040000c2c020e08c2c040000434120e08838240000c2c030700c1c0 (by decide +kernel)

theorem lower227 : Claim 227 7 :=
  fromSearch 16777317 (by decide +kernel) exclude227_11

theorem lower209 : Claim 209 5 :=
  fromLift 5 64 67108868 lower145 (by decide +kernel)

theorem lower83 : Claim 83 5 :=
  fromLift 5 1 16777284 lower82 (by decide +kernel)

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
  node_ok cuts211 [] 0x40008c14114040c14140008901030a08c28240008c14130a08c2824000890101404042824000c90101450451414000cc14134300d0c04000c901034300d0c04000cc1411450450c040008501024a08928240008c28234300d0c040008501034300d0c040008c28224a0890c040000830310d04434140000c14130b00c2c040000830330b00c2c040000c14110d0442c040000c28204840c28240000501030b00c2c040000c28230b00c2c040000501004840121040000928230b00c2c040000d0c004840d0c040000928204840908240000d0c030b00c2c040004c14104440c14140004901030700c1c040004c14130700c1c040004901004440111040008430320e08838240008c28230700c1c040008430330700c1c040008c28220e08838240004514130700c1c040004d0c004440d0c040004514104440504140004d0c030700c1c040000434130700c1c040000c2c020e08c2c040000434120e08838240000c2c030700c1c0 (by decide +kernel)

theorem lower211 : Claim 211 7 :=
  fromSearch 16777284 (by decide +kernel) exclude211_0

theorem lower115 : Claim 115 6 :=
  fromLift 6 1 16777284 lower114 (by decide +kernel)

def rule243_0 : {c : Cut // CutGood (goalAt 243) c} :=
  ruleFor 243 lower241 none (by decide +kernel)

def rule243_1 : {c : Cut // CutGood (goalAt 243) c} :=
  ruleFor 243 lower242 none (by decide +kernel)

def rule243_2 : {c : Cut // CutGood (goalAt 243) c} :=
  ruleFor 243 lower227 none (by decide +kernel)

def rule243_3 : {c : Cut // CutGood (goalAt 243) c} :=
  ruleFor 243 lower211 none (by decide +kernel)

def rule243_4 : {c : Cut // CutGood (goalAt 243) c} :=
  ruleFor 243 lower179 none (by decide +kernel)

def rule243_5 : {c : Cut // CutGood (goalAt 243) c} :=
  ruleFor 243 lower115 none (by decide +kernel)

def rule243_6 : {c : Cut // CutGood (goalAt 243) c} :=
  ruleFor 243 lower114 none (by decide +kernel)

def rule243_7 : {c : Cut // CutGood (goalAt 243) c} :=
  ruleFor 243 lower225 none (by decide +kernel)

def rule243_8 : {c : Cut // CutGood (goalAt 243) c} :=
  ruleFor 243 lower209 none (by decide +kernel)

def rule243_9 : {c : Cut // CutGood (goalAt 243) c} :=
  ruleFor 243 lower177 none (by decide +kernel)

def rule243_10 : {c : Cut // CutGood (goalAt 243) c} :=
  ruleFor 243 lower83 none (by decide +kernel)

def cuts243 : Cuts (goalAt 243) := [rule243_0,rule243_1,rule243_2,rule243_3,rule243_4,rule243_5,rule243_6,rule243_7,rule243_8,rule243_9,rule243_10]

def state243_0 : List Sig := [0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 0,input 1,input 4,input 5,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude243_0 : Impossible true (goalAt 243) 7 state243_0.toFinset :=
  node_ok cuts243 [] 0xc1411c0c0c1412c0c0c28230a08c14130a08c2822c0c0703010a08b03018504614130504e0c038300b03038300e0c030504614118300703028a08a28230a08e0c038300703038300e0c030a08a28228300b03014504514130504d0c034300b03034300d0c030504514114300703024a08928230a08d0c034300703034300d0c030a08928224301000834300d0c03830032223830100070c888322238300d0c034300a22210d04434130505000030504a22240018a22230504434110d04c28240024c2821c0c0434110d04c28210d04c2821c0c100001c0c0a28210d04a28238301000038300a28240020a28238300434138300928210d0492823430100003430092824001c928234300434134301000040004c2c030504232230504b03020e08838230504838220e08b03008c88b03010c0c838220e08c28240004c28210c0d00091080cc28220e08838218504838220e08e0c008c88e0c018504232218504e0c020e08e0c014504838220e08d0c040004d0c014505000714504d0c020e08d0c010d05000010d05000120e08838240001000020609000040000c1c030505000530504b03040018b03030505000630504b03040014b03030a09000430a08703040024703030a09000930a08703040010703028a09000328a08e0c040020e0c028a09000828a08e0c04000ce0c024a09000224a08d0c04001cd0c024a09000724a08d0c040008d0c0 (by decide +kernel)

def state243_1 : List Sig := [0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 1,input 7,input 0,input 4,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude243_1 : Impossible true (goalAt 243) 7 state243_1.toFinset :=
  node_ok cuts243 [] 0x100051c0c0703028888c28230a09000930a08c28228888703010a0900091c0c0703040010c28230a09000930a08c2824001070301c0c0703028a08a28230a08e0c038300703038300e0c030a08a28228300a22218504614120c0ce0c038300a22238300e0c020c0c614118505000a1850461414000ce0c038301000a38300e0c04000c614118504703024a08928230a08d0c034300703034300d0c030a08928224301000a34300d0c03830032223830100070c888322238300d0c034301000514504514128888d0c034301000734300d0c028888514114505000714504514140008d0c034301000734300d0c040008514114504430320e08838230a08c1c030700430330700c1c030a08838220e08614130700c1c03830031303830061410c4c0604138300c1c030700514130700c1c03430031303430051410c4c0504134300c1c03070083030c4c0313028888c1c030700830330700c1c02888831300c4c1000030700c1c030b00838230b01000620e08838230b00c1c03070100060c4c0313040004c1c030701000630700c1c04000431300c4c1000040000c14130a09000930a08703030b00c2c030a08c2c030b00703040000703028a08c2c030b00e0c040000e0c028a09000a28208e0c030b00c2c024a08c2c030b00d0c040000d0c024a09000724208d0c030b00c2c028889000528889000030b00c2c040001000010b010000400144341 (by decide +kernel)

def state243_2 : List Sig := roots 243
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude243_2 : Impossible true (goalAt 243) 8 state243_2.toFinset :=
  node_ok cuts243 [⟨state243_0,exclude243_0⟩,⟨state243_1,exclude243_1⟩] 0x40010c1411c0c0c14140010b03030a08c28240010c14130a08c28240010b0301c0c042824000cb0301850461414000cc14138300e0c04000cb03038300e0c04000cc1411850460c04000c703028a08a2824000cc28238300e0c04000c703038300e0c04000cc28228a08a0c040008b03014504514140008c14134300d0c040008b03034300d0c040008c1411450450c040008703024a08928240008c28234300d0c040008703034300d0c040008c28224a0890c040009000234300d0c040008e0c00c888e0c04000900020c888322240008e0c034300d0c040014a22210d04434140000c14130b00c2c080004a22230b00c2c040000c14110d0442c040010c2820c8c0c28240010703030b00c2c040010c28230b00c2c04001070300c8c032304000ca28230b00c2c04000ce0c00c8c0e0c04000ca2820c8c0a0824000ce0c030b00c2c040008928230b00c2c040008d0c00c8c0d0c04000892820c8c0908240008d0c030b00c2c040014c1410c4c0c14140004b03030700c1c040018c14130700c1c040014b0300c4c0313040010430320e08838240010c28230700c1c040010430330700c1c040010c28220e0883824000c614130700c1c04000ce0c00c4c0e0c04000c61410c4c060414000ce0c030700c1c040008514130700c1c040008d0c00c4c0d0c04000851410c4c0504140008d0c030700c1c040000434130700c1c040004c2c020e08c2c080000434120e08838240000c2c030700c1c0 (by decide +kernel)

theorem lower243 : Claim 243 9 :=
  fromSearch 16777284 (by decide +kernel) exclude243_2

theorem lower245 : Claim 245 8 :=
  fromLift 8 64 67110148 lower181 (by decide +kernel)

theorem lower231 : Claim 231 8 :=
  fromLift 8 1 16778597 lower230 (by decide +kernel)

theorem lower215 : Claim 215 8 :=
  fromLift 8 1 16779076 lower214 (by decide +kernel)

theorem lower119 : Claim 119 8 :=
  fromLift 8 1 16778564 lower118 (by decide +kernel)

theorem lower229 : Claim 229 6 :=
  fromLift 6 1 83887365 lower228 (by decide +kernel)

theorem lower213 : Claim 213 6 :=
  fromLift 6 4 67110660 lower209 (by decide +kernel)

theorem lower103 : Claim 103 5 :=
  fromLift 5 1 16778597 lower102 (by decide +kernel)

theorem lower117 : Claim 117 5 :=
  fromLift 5 1 67110148 lower116 (by decide +kernel)

def rule247_0 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower246 none (by decide +kernel)

def rule247_1 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower183 none (by decide +kernel)

def rule247_2 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower243 none (by decide +kernel)

def rule247_3 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower245 none (by decide +kernel)

def rule247_4 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower231 none (by decide +kernel)

def rule247_5 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower215 none (by decide +kernel)

def rule247_6 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower119 none (by decide +kernel)

def rule247_7 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower229 none (by decide +kernel)

def rule247_8 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower181 none (by decide +kernel)

def rule247_9 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower230 none (by decide +kernel)

def rule247_10 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower227 none (by decide +kernel)

def rule247_11 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower213 none (by decide +kernel)

def rule247_12 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower119 (some (1,input 1,input 4)) (by decide +kernel)

def rule247_13 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower165 none (by decide +kernel)

def rule247_14 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower228 none (by decide +kernel)

def rule247_15 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower225 none (by decide +kernel)

def rule247_16 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower164 none (by decide +kernel)

def rule247_17 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower145 none (by decide +kernel)

def rule247_18 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower103 none (by decide +kernel)

def rule247_19 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower117 none (by decide +kernel)

def rule247_20 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower83 none (by decide +kernel)

def rule247_21 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower211 none (by decide +kernel)

def rule247_22 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower231 (some (1,input 1,input 5)) (by decide +kernel)

def rule247_23 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower214 none (by decide +kernel)

def rule247_24 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower82 none (by decide +kernel)

def rule247_25 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower149 none (by decide +kernel)

def rule247_26 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower243 (some (1,input 1,input 7)) (by decide +kernel)

def rule247_27 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower118 none (by decide +kernel)

def rule247_28 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower115 none (by decide +kernel)

def rule247_29 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower116 none (by decide +kernel)

def rule247_30 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower151 none (by decide +kernel)

def rule247_31 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower183 (some (1,input 4,input 5)) (by decide +kernel)

def rule247_32 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower231 (some (2,input 5,input 7)) (by decide +kernel)

def rule247_33 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower231 (some (1,input 5,input 7)) (by decide +kernel)

def rule247_34 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower55 none (by decide +kernel)

def rule247_35 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower183 (some (1,input 4,input 7)) (by decide +kernel)

def rule247_36 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower102 none (by decide +kernel)

def rule247_37 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower183 (some (1,input 5,input 7)) (by decide +kernel)

def rule247_38 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower147 none (by decide +kernel)

def rule247_39 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower114 none (by decide +kernel)

def rule247_40 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower209 none (by decide +kernel)

def rule247_41 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower227 (some (1,input 5,input 7)) (by decide +kernel)

def cuts247 : Cuts (goalAt 247) := [rule247_0,rule247_1,rule247_2,rule247_3,rule247_4,rule247_5,rule247_6,rule247_7,rule247_8,rule247_9,rule247_10,rule247_11,rule247_12,rule247_13,rule247_14,rule247_15,rule247_16,rule247_17,rule247_18,rule247_19,rule247_20,rule247_21,rule247_22,rule247_23,rule247_24,rule247_25,rule247_26,rule247_27,rule247_28,rule247_29,rule247_30,rule247_31,rule247_32,rule247_33,rule247_34,rule247_35,rule247_36,rule247_37,rule247_38,rule247_39,rule247_40,rule247_41]

def state247_0 : List Sig := [0xffffffffffffcccc0000000000000000ffffffffffffcccc,input 5,input 1,input 4,input 0,input 2,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_0 : Impossible true (goalAt 247) 7 state247_0.toFinset :=
  node_ok cuts247 [] 0x21514343021514814131300c4c021514c4c03130081410d0c0814515514c4c031300d0c00d0c0d0c015514343014514d0c031300c4c019514c4c031300e0c00d0c0e0c019514343018514e0c031300c4c021514313021514844430700c1c021514c1c03070084440c4c0844540044c1c030700c4c005450c4c040040151405450c4c030700c1c015514c1c030700d0c00c4c0d0c015514313015114d0c030700c1c011d14c1c030700c2c020e08c2c011d14838220e08c2c030700c1c019514c1c030700e0c00c4c0e0c019514313019114e0c030700c1c02c0c0554515514854534300d0c02c0c0d0c03430085451551450800d050d0c034300e0c00c888e0c00d05032220c888e0c034300d0c028888474511d14854530b00c2c028888c2c030b00854511d14474521a08c2c030b00c4c011d14c4c021a08474521a08c4c030b00c2c024a08c2c030b00d0c00c8c0d0c024a08323024208d0c030b00c2c028a08c2c030b00e0c00c8c0e0c028a08323028208e0c030b00c2c02c0c0654519514854538300e0c02c0c0e0c03830085451951460802c0c0703010a08854530a08c2822c0c0c28230a0885451c0c0854521a08c28221a08c4c015050c4c021a08541421a08c4c030a08c4c020e08c28220e08c1c011c1cc1c020e08470720e08c1c030a08c1c024a08c28224300d0c01c0c0d0c024a08703024a08d0c030a08d0c00c8c070300c8c0c2c030a08c2c00c8c0c28230a08c2c01c0c0c2c028a08c28228300e0c01c0c0e0c028a08703028a08e0c030a08e0c0 (by decide +kernel)

def state247_1 : List Sig := [0xffffffffffffcccc0000000000000000ffffffffffffcccc,0xffffffffffffccccffffffffffffccccffffffffffffccccffffffffffffcccc,input 5,input 1,input 4,input 0,input 2,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_1 : Impossible true (goalAt 247) 7 state247_1.toFinset :=
  node_ok cuts247 [] 0x21514c4c03130081453130092820d0c0c4c031300a2820d0c0c4c031300868221a08c4c021514c1c030700844530700c4c005450c1c03070092820c4c0c1c030700838220e08c1c030700a2820c4c0c1c030700838220e08c1c02c0c0928224a08854524a08a2820c888928234300323021514a0222151486823130086823130092820c8c0908224208a2820c8c0a08228208c2c02c0c0a28228a08854538300b03021514b03021514428230a08c282215148682313008682313008382307008382307009282180c0928230a08323030a08c2821c0c0a282140c0a28230a090001 (by decide +kernel)

def state247_2 : List Sig := [0x5555555555555555555555555555555555555555555544445555555555554444,input 7,input 5,input 1,input 4,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_2 : Impossible true (goalAt 247) 6 state247_2.toFinset :=
  node_ok cuts247 [] 0x31514c28230a08854521a08c4c03130084c031300d0c014514c4c031300e0c018514c4c031514c4c031300c14524a08d0c03430090c034300e0c00c888d0c015514d0c03430050c030a08c2c030b00323030b00c4c021208c2c030b00d0c024208c2c030b00e0c028208c2c011d14c2c030b00474528a08e0c038300a0c019514e0c03830060c020e08c1c030700838230700151431300c1c030700544534300c1c030700838230b00c1c030700644538300c1c031114c1c030700c545 (by decide +kernel)

def state247_3 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0c0c0f0f0f0f0f0f0c0c,input 7,input 5,input 1,input 4,input 0,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_3 : Impossible true (goalAt 247) 6 state247_3.toFinset :=
  node_ok cuts247 [] 0x31514c28230a08854520e08c1c030700838230700d0c015114c1c030700c2c020e08c1c030700e0c019114c1c031514c1c030700c44524a08d0c03430090c034300e0c00c888d0c015514d0c03430050c030a08c2c030b00323030b00d0c024208c2c030b00e0c028208c2c011d14c2c030b00474528a08e0c038300a0c019514e0c03830060c021300c4c031300868230700151430700c4c031300514534300c4c030b00848230b00c4c031300614538300c4c030514c4c031300c545 (by decide +kernel)

def state247_4 : List Sig := [0xffffffffffffffff0000000000000000ffffffffffffcccc,input 7,input 5,input 1,input 4,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_4 : Impossible true (goalAt 247) 6 state247_4.toFinset :=
  node_ok cuts247 [] 0x31300d0c014514c4c031300e0c018514c4c031514c4c031300c14530700c4c005450c1c030700d0c015114c1c030700c2c020e08c1c030700e0c019114c1c031514c1c030700c44534300e0c00c888d0c015514d0c03430050c030b00c4c021208c2c030b00d0c024208c2c030b00e0c028208c2c011d14c2c030b00474519514e0c03830060c021300c4c021a08c4c020e08c1c020e08c1c024300d0c024a08d0c00c8c0c2c030a08c2c028300e0c028a08e0c021514c28230a08c545 (by decide +kernel)

def state247_5 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffccccffffffffffffcccc,input 7,input 5,input 1,input 4,input 0,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_5 : Impossible true (goalAt 247) 7 state247_5.toFinset :=
  node_ok cuts247 [⟨state247_2,exclude247_2⟩,⟨state247_3,exclude247_3⟩,⟨state247_4,exclude247_4⟩] 0x1c0c0c28230a08428280008c28230a09000121a08c4c03130084c031300d0c00d0c0c4c031300e0c00d0c0c4c00d0c0c4c031300343080004c4c031301000220e08c1c030700838230700c4c005450c1c030700d0c00c4c0c1c030700c2c020e08c1c030700e0c00c4c0c1c00c4c0c1c030700313080000c1c030701000024a08d0c03430090c034300e0c00c888d0c02c0c0d0c03430050c015514c28230b00c2c00c8c0c2c031300848230b00c2c034300908230b00c2c038300a08230b00323030b00c2c010b00474528a08e0c038300a0c02c0c0e0c03830060c019514c545 (by decide +kernel)

def state247_6 : List Sig := [0xffffffffffffccccffffffffffffcccc,input 7,input 5,input 1,input 4,input 0,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_6 : Impossible true (goalAt 247) 7 state247_6.toFinset :=
  node_ok cuts247 [] 0xc54530a08c28221514868231300c4c021300c4c034300343031300c4c038300343031300c54531300c4c030514838230700c1c020e08c1c031300151430700c1c034300313030700c1c030b00838230700c1c038300313030700c54530700c1c031114928234300d0c024300d0c038300322234300d54534300d0c031514c28230b00c2c00c8c0c2c031300848230b00c2c034300908230b00c2c038300a08230b00c74530b00c2c031514a28238300e0c028300e54538300e0c031514703030a08703030a08343031300343031300313030700313030700554534300322234300474530b00323030b00654538300341438300b030 (by decide +kernel)

def state247_7 : List Sig := [0x3333333333330000333333333333000033333333333300003333333333330000,0xffffffffffffccccffffffffffffccccffffffffffffccccffffffffffffcccc,input 5,input 4,input 0,input 2,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_7 : Impossible true (goalAt 247) 7 state247_7.toFinset :=
  node_ok cuts247 [] 0xc54530a08c28221514c54531300c4c030514868231300c4c021300c4c024a08343031300c4c028a08343031300c4c030b00848230b00c54530700c1c031114838230700c1c020e08c1c031300151430700c1c024a08313030700c1c028a08313030700c1c030b00838230700b03024a08928231514928230a08603024a08928228a08322224a08d2c02c0c0a28228a08c54528a08c282140c0a28238b00474530b00c2c011d14c28230b00c2c040034323031514b03031514323030a08703030a08323031300343031300313030700313030700908224208323024a08a08228208323028a090001 (by decide +kernel)

def state247_8 : List Sig := [0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 7,0xffffffffffffccccffffffffffffccccffffffffffffccccffffffffffffcccc,input 5,input 4,input 0,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_8 : Impossible true (goalAt 247) 7 state247_8.toFinset :=
  node_ok cuts247 [] 0x703030a08c28210a08703030a08c2820c8c0868231300c4c021300c4c024208343031300c4c028208343031300c4c030b00848230b00343031300c4c00d0c0343031300c4c00c8c0838230700c1c020e08c1c031300151430700c1c024208313030700c1c028208313030700c1c030b00838230700313030700c1c00c4c0313030700c1c00c4c0908230a08603024208908228208322224208d0c00c88890822420832220c8c0908224208150728208c282140c0a08238300a02228208a0820d050323028208a08205850c28230b00c2c040020a02230b00c2c010b00474530b00c2c040018c545 (by decide +kernel)

def state247_9 : List Sig := [0xffffffffffffccccffffffffffffccccffffffffffffccccffffffffffffcccc,input 5,input 1,input 4,input 0,input 2,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_9 : Impossible true (goalAt 247) 8 state247_9.toFinset :=
  node_ok cuts247 [⟨state247_0,exclude247_0⟩,⟨state247_1,exclude247_1⟩,⟨state247_5,exclude247_5⟩,⟨state247_6,exclude247_6⟩,⟨state247_7,exclude247_7⟩,⟨state247_8,exclude247_8⟩] 0xc5451c0c0c5452c0c0c28230a08c54530a08c2822c0c0703021514c5450d0c0c54530504c4c031300c54531300c4c030504343030514541421a08868230a08c4c031300541431300c4c030a08868221300170731300c4c024a08343024a0817070d0c0343024a08c4c031300341431300c4c028a08343028a0834140d0c0343028a08c4c031301000f31300c4c040008868221a09000f21a08868240008c4c031300c5450c4c0c54531110c1c030700c54530700c1c031110313031114470720e08838230a08c1c030700470730700c1c030a08838220e09000f30700c1c031300151431301000e05450151431300c1c030700170730700c1c024a08313024a0817070c4c0313024a08c1c030701000730700c1c00c8c0838220e09000e20e0883820c8c0c1c030700270730700c1c028a08313028a0827070c4c0313028a08c1c030701000e30700c1c040000838220e09000e20e08838240000c1c030700b0300c888b03031514928224a08b03024a08928231514322231514703024a08928230a09000730a08703040034603030a08928224a08341424a08928228a08322228a0834140c888322228a08928224a0900074002cd0c02888832300c8c0c5454001cc5452888a000528088c5450c8c0c54530a08323030a0870304001c703030a09000d30a0870300c8c0323021a08323021a08c4c005850c4c021a08161421a08c4c00c8c0c4c024a09000724a0900070c8c0323024a0832302420900074001c908228a08161428a0834140c8c0323028a08323028208341405850a0824001e000430b00b0300d050b03031514a28228a08b03028a08a28231514341431514703028a08a28230a09000b30a08703040034503030a08a28228a0900074001ce0c02c0c100062c0c0c5458000cc5452c0c200022c0c0c54540018c54530a09000130a0a000140036000030a09000d30a09000d400050001 (by decide +kernel)

def state247_10 : List Sig := [0xffffffff00000000ffffffff00000000ffffcccc00000000ffffcccc,input 5,input 7,input 1,input 4,input 0,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_10 : Impossible true (goalAt 247) 7 state247_10.toFinset :=
  node_ok cuts247 [] 0x703030a08c28210a08868231300c4c021300c4c034300343031300343031300c4c00d0c0c4c018504614531300838230700c1c020e08c1c031300151430700c1c034300313030700c1c030b00838230700313030700c1c00c4c0c1c019110644530700928234300d0c024300b03034300d0c014300d0c019514322234300c28230b00c2c00c8c0c2c031300848230b00c2c034300908230b00323030b00c2c010b00c2c019514323030b00703030a08654530a08654539514b03019514c2821c0c0c2821c0c0c4c00d0c0c4c00d0c0c1c00c4c0c1c00c4c0d0c015514d0c00c888c2c011d14c2c00c8c0c5453151494142c0c0e0c0 (by decide +kernel)

def state247_11 : List Sig := [0xffffffffffffffffffffffffffffffffffffccccffffccccffffccccffffcccc,input 7,input 1,input 4,input 0,input 2,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_11 : Impossible true (goalAt 247) 8 state247_11.toFinset :=
  node_ok cuts247 [⟨state247_5,exclude247_5⟩,⟨state247_10,exclude247_10⟩] 0x1000d1c0c070302c0c0c28230a09000d30a08c2822c0c0703010a09000d18080602040004c28230a09000d30a08c28240004602018080703028a08a28230a08e0c038300703038300e0c030a08a28228300b03019514654525050e0c038300b03038300e0c025050654519516000119514654540014e0c038302000038300e0c040014654519514541421a08868230a08c4c031300541431300c4c030a08868221300654531300c4c03830034303830065450d0c0614538300c4c031300170731300c4c03430034303430017070d0c0343034300c4c03130094140d0c034302c0c0c4c031300941431300c4c02c0c034300d0c1000f09080242040008c4c031301000f31300c4c040008242009080470720e08838230a08c1c030700470730700c1c030a08838220e08654530700c1c03830031303830065450c4c0644538300c1c030701000f30700c1c031300151431301000e05450151431300c1c030700170730700c1c03430031303430017070c4c0313034300c1c030701000730700c1c030b00838230b01000e20e08838230b00c1c03070087070c4c031302c0c0c1c030700870730700c1c02c0c031300c4c1000e08480212040000c1c030701000e30700c1c040000212008480703024a08928230a08d0c034300703034300d0c030a08928224300341434300d0c03830032223830034140c888322238300d0c034300b0300c888b03028888d0c034300b03034300d0c02888832221430100074004c554530a08323030a08703030b00c2c030a08c2c030b0070300c8c0323028a08c2c030b00e0c00c8c0e0c028a08323028208e0c030b00c2c021a08c2c030b00c4c005850c4c021a08161421208c4c030b00c2c024a08c2c030b00d0c00c8c0d0c024a08323024208d0c030b00c2c02888832300c8c0b03030b00c2c028888c2c030b00b0300c8c042c04001d001211d1500074001cc545 (by decide +kernel)

def state247_12 : List Sig := [0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 7,0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc,input 4,input 0,input 2,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_12 : Impossible true (goalAt 247) 8 state247_12.toFinset :=
  node_ok cuts247 [⟨state247_8,exclude247_8⟩] 0x4002070301c0c0a22230a08c28240020c28230a08a2221c0c042824002070301c0c0323030a08c28240020c28230a0832301c0c032301c0c0a28228a08c28238300e0c01c0c0e0c038300c28228a08a0c028888654519514870738300e0c028888e0c03830087071951465450c8c0654519514161438300e0c00c8c0e0c038300161419514654515050868221a08c28231300c4c015050c4c031300c28221a0884c019514c4c031300e0c00d0c0e0c019514343018514e0c031300c4c005c1cc4c03130090820d0c0908205c1c34300d0c0908231300c4c04001cc4c031300c2c021a08c2c04003c868221208c2c031300c2c021c1c34300d0c0a22231300c4c021c1cc4c031300a2220d0c034300585034300d0c0323031300c4c005850c4c03130032300d0c0323011c1c838220e08c28230700c1c011c1cc1c030700c28220e08838219514c1c030700e0c00c4c0e0c019514313019114e0c030700c1c04003cc1c030700c4c005450c4c040038151405450c4c030700c1c005c1cc1c03070090820c4c0908205c1c31300c4c0908230700c1c04001cc1c030700c2c020e08c2c040038838220e08c2c030700c1c021c1c31300c4c0a22230700c1c021c1cc1c030700a2220c4c031304003831300c4c0323030700c1c040038c1c03070032300c4c031301c0c0908224208c28240020c2821c0c100081c0c0c2822420890820d050908224208e0c00c888e0c00d05032220c888e0c024208e0c04000d00033430100070c88832222888890822420900072420890822888832220c88832304004c32304001090822420832302420890824001100070541cc28240020c28218080c2c030b00c28230b00c2c018081000818080a28230b00c2c038301000738300a28280000a08238300c2c030b00a22240018a2224001cc2c030b00a22230b00c2c04001d000610b00323040018474540010c2c030b00323030b00c2c04001100064001900034000cc545 (by decide +kernel)

def state247_13 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f00000000,input 5,input 7,0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc,input 1,input 4,input 0,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_13 : Impossible true (goalAt 247) 7 state247_13.toFinset :=
  node_ok cuts247 [] 0xc54530a08c28221514838230700c1c020e08c1c024a08313030700c1c020e08838230700c1c020e08838230700c54530700c1c031114c1c038300644530700928230a08703024a08d0c02c0c0928224a08c54524a08e0c00c888e0c030a08703030a08323024a08323024208c2c00c8c0c54528888c54528a08e0c028a08e0c030a08602030a0860202c0c0c5452c0c0c54528a08e0c028a08e0c028a08e0c038300a0c019514e0c03830060c021300c4c031300868230700151430700c4c031300343024a08c4c031300868221a08c4c031300868221a08c4c030514c4c031300c54531300614538300c4c0 (by decide +kernel)

def state247_14 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,input 7,0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc,input 1,input 4,input 0,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_14 : Impossible true (goalAt 247) 8 state247_14.toFinset :=
  node_ok cuts247 [⟨state247_5,exclude247_5⟩,⟨state247_13,exclude247_13⟩] 0x1c0c0c28230a08703015050c28230a08541421a08c4c03130084c03130092820d0c0c4c031300868221a08c4c00d0c0c4c031300343031300e0c00d0c0c4c080004c4c031301000a20e08c1c030700838230700c4c005450c1c03070092820c4c0c1c030700838220e08c1c030700838220e08c1c00c4c0c1c030700313030700e0c00c4c0c1c005450c1c030700151424a08c2821c0c0928234300b03024a0892820c888928238300322238300170724a08928205c1cc2821c0c0c2820c8c086823130086823130092820c8c0908230b0032302c0c0a2220c8c0a28238300a2823830016140c8c0323005850c28218080c28218080b03028080b03028080a28238300a2823830100144001e00004001cc54528a08e0c038300a0c02c0c0e0c0183006545 (by decide +kernel)

def state247_15 : List Sig := [0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc,input 1,input 4,input 0,input 2,input 5,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_15 : Impossible true (goalAt 247) 9 state247_15.toFinset :=
  node_ok cuts247 [⟨state247_9,exclude247_9⟩,⟨state247_11,exclude247_11⟩,⟨state247_12,exclude247_12⟩,⟨state247_14,exclude247_14⟩] 0x40020c5451c0c0c54540020b03030a08c28240020c54530a08c28240020b0301c0c0854540030b0301951465454002cc54538300e0c08000cb03038300e0c04002cc5451951460c040020703028a08a28240020c28238300e0c040020703038300e0c040020c28228a08a0c040028c5450d0c0c54540028c14131300c4c040028c54531300c4c040028c1410d0c0c14540020541421a08868240020c28231300c4c040020541431300c4c040020c28221a0884c040028654531300c4c040028e0c00d0c0e0c04002865450d0c0614540028e0c031300c4c040010170731300c4c04001092820d0c092824001017070d0c0343040010928231300c4c040029000a31300c4c040029000221a08868240029000a21a08868240029000231300c4c040024c5450c4c0c54540024c44430700c1c040024c54530700c1c040024c4440c4c0c44540020470720e08838240020c28230700c1c040020470730700c1c040020c28220e08838240024654530700c1c040024e0c00c4c0e0c04002465450c4c0644540024e0c030700c1c040025000930700c1c040024c4c005450c4c040025000905450151440024c4c030700c1c040010170730700c1c04001092820c4c092824001017070c4c0313040010928230700c1c04000d000330700c1c04000c323020e0883824000d000920e0883824000c323030700c1c040025000930700c1c040025000020e08838240025000920e08838240025000030700c1c040010b0300c888b03040010c54524a08928240010b03024a08928240010c5450c888c54540010703024a08928240010c28240010c28240010703040020703040010c28224a08928240010341424a08928240010e0c00c888e0c04001034140c888322240010e0c024a08e0c04000d00034000cd0c04000ca2220c8c032304000cc5454000cc5454000ca22280008a2224000cc5450c8c0c5454000cc2820c8c0c2824000c70304000c70304000cc28240020c2824000c70300c8c032304000ca28205850a2824000ce0c00c8c0e0c04000ca2820c8c0a2824000ce0c005850e0c04000c86820c8c086824000cc4c005850c4c04000c86820585086824000cc4c00c8c0c4c04000c92824001092824000d00030c8c032304000d00034000c90824000d000340010c2c04001cb03040018b0304001cc5454001cc5454001cb03080004b0304001cc54540018c54540020c28240004c28240020602040020602040020c28240020c2824002060204000460204001ca28240014a2824001ce0c04001ce0c04001ca28280000a2824001ce0c040014e0c0 (by decide +kernel)

def state247_16 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0c0c0c0c0f0f0f0f0c0c0c0c,input 7,input 1,input 5,input 0,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_16 : Impossible true (goalAt 247) 7 state247_16.toFinset :=
  node_ok cuts247 [] 0x31514703031514b03030a08c28231514c28230a08b0301c0c085451c0c0928224a08c28234300d0c01c0c0d0c034300c28224a0890c00d050d0c034300e0c00c888e0c00d05032220c888e0c034300d0c02c0c0514514514c54534300d0c02c0c0d0c034300c54514514514511c1c838220e08c28230700c1c011c1cc1c030700c28220e08838214514c1c030700d0c00c4c0d0c014514313014114d0c030700c1c019514c1c030700e0c00c4c0e0c019514313019114e0c030700c1c011d14c1c030700c2c020e08c2c011d14838220e08c2c030700c1c031514313031514c44430700c1c031514c1c030700c4440c4c0c4451c0c0a28228a08c28238300e0c01c0c0e0c038300c28228a08a0c02c0c0654519514c54538300e0c02c0c0e0c038300c5451951460c030a08323030a08703030b00c2c030a08c2c030b0070300c8c0323024a08c2c030b00d0c00c8c0d0c024a08323024208d0c030b00c2c028a08c2c030b00e0c00c8c0e0c028a08323028208e0c030b00c2c028888474511d14c54530b00c2c028888c2c030b00c54511d14474530a08868221300501431300c4c030a08c4c031300501421a08868234300c4c03130051450d0c0514534300343034300514531300c4c030700c4c030700151440060151430701001830700151431300c4c038300c4c03130065450d0c0614538300343038300654531300c4c030b00c4c030b00474521a08848230b00868230b00474531300c4c02c0c0343030514c54531300c4c02c0c0c4c031300c5450d0c0c545 (by decide +kernel)

def state247_17 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0c0c0c0c0f0f0f0f0c0c0c0c,0xffffffffffffffffffffffffffffffffffffffffccccccccffffffffcccccccc,input 7,input 1,input 5,input 0,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_17 : Impossible true (goalAt 247) 7 state247_17.toFinset :=
  node_ok cuts247 [] 0x1c0c0c28230a08428214050c28230a08501424a08d0c03430090c034300e0c00c888d0c014514d0c034300514514514d0c034300514520e08c1c030700838230700d0c014114c1c030700e0c00c4c0c1c030700c2c020e08c1c00c4c0c1c030700313005450c1c030700151428a08e0c038300a0c02c0c0e0c03830060c019514c28230b00c2c00c8c0c2c034300908230b00c2c038300a08230b00323030b00c2c010b0047453151484c031300c4c021a08c4c014514d0c031300c1c005450c1c031300c4c00d0c0e0c031300c2c021208c2c031300343031300c4c00d0c10002 (by decide +kernel)

def state247_18 : List Sig := [0xffff0000ffff0000ffff0000ffff0000ffff0000cccc0000ffff0000cccc,input 4,input 7,input 1,input 5,input 0,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_18 : Impossible true (goalAt 247) 7 state247_18.toFinset :=
  node_ok cuts247 [] 0x703030a08c28210a08868231300c4c021300c4c038300343031300343031300c4c00d0c0c4c014504514531300838230700c1c020e08c1c031300151430700c1c038300313030700c1c030b00838230700313030700c1c00c4c0c1c015110544530700a28238300e0c028300b03038300e0c018300c28230b00c2c00c8c0c2c031300848230b00c2c038300a08230b00323030b00c2c010b00c2c015514323030b00703030a08554530a08554538300341438300554535514b03015514c2821c0c0c2821c0c0c4c00d0c0c4c00d0c0c1c00c4c0c1c00c4c0e0c019514e0c00d050c2c011d14c2c00c8c0c54531514a2222c0c0d0c0 (by decide +kernel)

def state247_19 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,0xffffffffffffffffffffffffffffffffffffffffccccccccffffffffcccccccc,input 7,input 1,input 0,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_19 : Impossible true (goalAt 247) 7 state247_19.toFinset :=
  node_ok cuts247 [] 0x703030a08c28210a08541430a08c282140c0868231300c4c021300343031300c4c00d0c0341431300c4c040054c4c00d0c0343031300c4c038300343031300838230700c1c020e08c1c031300151430700c1c030b00838230700313030700c1c00c4c0151430700c1c005450c1c00c4c0313030700c1c038300313030700c28230b00c2c00c8c0c2c031300848230b00323030b00c2c010b00474530b0032300c8c0c2c030b00e0c028208c2c031514703030a08603030a089030248889030280c034140c888322209050d0c028a08e0c038300a0c0240c0e0c03830060c019514e0c0383010004 (by decide +kernel)

def state247_20 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffccccccccffffffffcccccccc,input 7,input 1,input 5,input 0,input 2,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_20 : Impossible true (goalAt 247) 8 state247_20.toFinset :=
  node_ok cuts247 [⟨state247_5,exclude247_5⟩,⟨state247_16,exclude247_16⟩,⟨state247_17,exclude247_17⟩,⟨state247_18,exclude247_18⟩,⟨state247_19,exclude247_19⟩] 0x100191c0c070302c0c0c28230a09001930a08c2822c0c0703010a09001915050541440004c28230a09001930a08c28240004541415050703024a08928230a08d0c034300703034300d0c030a08928224301000b34300d0c03830032223830200040c888322238300d0c034300b03015514554528888d0c034300b03034300d0c028888554515516000315514554540010d0c034302000034300d0c040010554515514541421a08868230a08c4c031300541431300c4c030a08868221300554531300c4c03430034303430055450d0c0514534300c4c031300270731300c4c03830034303830027070d0c0343038300c4c03130087070d0c034302c0c0c4c031300870731300c4c02c0c034300d0c100148000a000140008c4c031301001431300c4c040009001440008470720e08838230a08c1c030700470730700c1c030a08838220e08554530700c1c03430031303430055450c4c0544534300c1c030701001430700c1c031300151431301001805450151431300c1c030700270730700c1c03830031303830027070c4c0313038300c1c030701000b30700c1c030b00838230b01001820e08838230b00c1c03070087070c4c031302c0c0c1c030700870730700c1c02c0c031300c4c1001805450151440000c1c030701001830700c1c040000151405450703028a08a28230a08e0c038300703038300e0c030a08a28228300b03009c1cb03021c1ce0c038300b03038300e0c021c1c270718301000b4004c654530a08323030a08703030b00c2c030a08c2c030b0070300c8c0323024a08c2c030b00d0c00c8c0d0c024a08323024208d0c030b00c2c021a08c2c030b00c4c04002cc4c021a09001421208c4c030b00c2c028a08c2c030b00e0c00c8c0e0c028a08323028208e0c030b00c2c02888832300c8c0b03030b00c2c028888c2c030b00b0300c8c042c04002d001411d15000b4002cc545 (by decide +kernel)

def state247_21 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 0,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_21 : Impossible true (goalAt 247) 6 state247_21.toFinset :=
  node_ok cuts247 [] 0x148c0c28230a08323014888c28230a08428221a08c4c03130084c031300c2c021208c2c00d0c0c4c031300323009888c4c031300243031300d0c00d0c0c4c020e08c1c030700838230700c4c005450c1c030700c2c020e08c1c00c4c0c1c030700313008c88c1c030700232230700d0c00c4c0c1c030a08c2c030b00503011d14c2c030b0090300c888c2c030b0042c030b00d0c024208c2c031514c5450c8c1000724a08d0c03430090c00c8c0d0c03430050c015514d0c0343002707 (by decide +kernel)

def state247_22 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 4,0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 5,input 0,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_22 : Impossible true (goalAt 247) 7 state247_22.toFinset :=
  node_ok cuts247 [⟨state247_21,exclude247_21⟩] 0x1c0c0c28230a08323018888c28230a08428221a08c4c03130084c031300a0820d0c0c4c031300c2c021208c2c00d0c0c4c031300323031300d0c00d0c0c4c009888c4c031300262220e08c1c030700838230700c4c005450c1c030700a0820c4c0c1c030700c2c020e08c1c00c4c0c1c030700313030700d0c00c4c0c1c008c88c1c030700232228208c2821c0c0a08238300323028208a082248c0a02228208a08209c1cc28230b00c2c015050474530b00c2c025050a02230b00c2c010b00c5453151432304000c928234300d0c024300d0c02820a000034300d0c030b00908230b00323034300d0c0143005545 (by decide +kernel)

def state247_23 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 7,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 0,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_23 : Impossible true (goalAt 247) 7 state247_23.toFinset :=
  node_ok cuts247 [⟨state247_21,exclude247_21⟩] 0x1c0c0c28230a084282148c0c28230a08323021a08c4c03130084c031300c2c021208c2c00d0c0c4c03130034300d0c0c4c03130032303130034300d0c0c4c031300a0820d0c0c4c020e08c1c030700838230700c4c005450c1c030700c2c020e08c1c00c4c0c1c03070031300c4c0c1c03070031303070031300c4c0c1c030700a0820c4c0c1c030a08c2c030b00503028088c2c030b0042c011d14c2c030b00341430b00e0c028208c2c031514703030a08603030a08341430b00322230b0032222488a00000c88832300c88832304001cd0c028208c2821c0c0a08228088a0822820827070c8c0a082282082507 (by decide +kernel)

def state247_24 : List Sig := [0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 7,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 5,input 0,input 2,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_24 : Impossible true (goalAt 247) 8 state247_24.toFinset :=
  node_ok cuts247 [⟨state247_8,exclude247_8⟩,⟨state247_22,exclude247_22⟩,⟨state247_23,exclude247_23⟩] 0x4002070301c0c0a02230a08c28240020c28230a08a0221c0c042824002070301c0c0323030a08c28240020c28230a0832301c0c032301c0c0928224a08c28234300d0c01c0c0d0c034300c28224a0890c04002cd0c034300a0820c888a0828000832220c888a08234300d0c04002cd0c034300c2c024a08c2c080000928224208c2c034300c2c040050554515514a02234300d0c080004d0c034300a0221551455450c8c0554515515000734300d0c00c8c0d0c034301000715514554515050868221a08c28231300c4c015050c4c031300c28221a0884c015514c4c031300d0c00d0c0d0c015514343014514d0c031300c4c009c1cc4c031300a0820d0c0a08209c1c34300d0c0a08231300c4c04002cc4c031300c2c021a08c2c040050868221208c2c031300c2c021c1c34300d0c0a02231300c4c021c1cc4c031300a0220d0c034304005034300d0c0323031300c4c040050c4c03130032300d0c0323011c1c838220e08c28230700c1c011c1cc1c030700c28220e08838215514c1c030700d0c00c4c0d0c015514313015114d0c030700c1c040050c1c030700c4c005450c4c040060151405450c4c030700c1c009c1cc1c030700a0820c4c0a08209c1c31300c4c0a08230700c1c04002cc1c030700c2c020e08c2c040060838220e08c2c030700c1c021c1c31300c4c0a02230700c1c021c1cc1c030700a0220c4c031304006031300c4c0323030700c1c040060c1c03070032300c4c031301c0c0a08228208c28240020c2821c0c100081c0c0c28228208a0824000d000338300a02209c1ca02221c1ca08228208a02228208a08221c1c270709c1c32304004c323040014a08228208323028208a08240015000b048c0c28240020c28215050c2c030b00c28230b00c2c015051000815050a02240018a0224002cc2c030b00a02230b00c2c04002d000610b00323040018474540014c2c030b00323030b00c2c04001500064001900034000cc545 (by decide +kernel)

def state247_25 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 7,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 1,input 0,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_25 : Impossible true (goalAt 247) 7 state247_25.toFinset :=
  node_ok cuts247 [⟨state247_21,exclude247_21⟩] 0x1c0c0c28230a08703014888c28230a08603021a08c4c03130084c031300868221a08c4c031300d0c00d0c0c4c00d0c0c4c031300343009888c4c031300243020e08c1c030700838230700c4c005450c1c030700838220e08c1c030700838220e08c1c030700d0c00c4c0c1c00c4c0c1c030700313008c88c1c030700232230a08523030a08323021a08c4c021a08c4c030b009282343009282343003230248c200000c8c032220c8c032304001cc28215050c282140c0e0c034300928234300a030250509030240c032220d050322209050928234300d0c024300a03034300d0c014300554534300d0c009c1cc545 (by decide +kernel)

def state247_26 : List Sig := [0x3333333333330000333333333333000033333333333300003333333333330000,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 0,input 2,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_26 : Impossible true (goalAt 247) 7 state247_26.toFinset :=
  node_ok cuts247 [] 0x31514c28230a08854531514c4c031300c14521a08c4c03130084c031300c2c021208c2c03130034300d0c0c4c031300a2820d0c0c4c031514c1c030700c44520e08c1c030700838230700c4c005450c1c030700c2c020e08c1c03070031300c4c0c1c030700a2820c4c0c1c011d14c2c030b00474530a08c2c030b00503030b00e2c028a08c2c02c0c0c545280c0c5451c0c0c282180c0c2820d050c2c00c888c2c024a08b03028a08a28231514a28230a08703028a08323031514923031514323030a08523030a08323031300343031300313030700313030700341430b00323030b0100070c8c032300c888a082 (by decide +kernel)

def state247_27 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 1,input 0,input 2,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_27 : Impossible true (goalAt 247) 8 state247_27.toFinset :=
  node_ok cuts247 [⟨state247_19,exclude247_19⟩,⟨state247_23,exclude247_23⟩,⟨state247_25,exclude247_25⟩,⟨state247_26,exclude247_26⟩] 0x31514703031514b03030a08c28231514c28230a08b0301c0c0854531514343031514c14131300c4c031514c4c031300c1410d0c0c14515050868221a08c28231300c4c015050c4c031300c28221a0884c00d050c4c031301001521a0886820d050868221a09001531300c4c040054c4c03130032220d0c034304005434300d0c0322231300c4c009c1cc4c031300a2820d0c0a28209c1c34300d0c0a28231300c4c031514313031514c44430700c1c031514c1c030700c4440c4c0c44511c1c838220e08c28230700c1c011c1cc1c030700c28220e08838240054c1c030700c4c005450c4c04005c151405450c4c030700c1c04005cc1c030700323020e0883824005c838220e08323030700c1c04005cc1c030700341420e0883824005c838220e08341430700c1c04005cc1c03070032220c4c031304005c31300c4c0322230700c1c009c1cc1c030700a2820c4c0a28209c1c31300c4c0a28230700c1c02888832300c8c0c5454001cc5452888a000128088c5450c8c0c54530a08323030a0870304001c523030a09000d30a0870300c8c0323021a08323021a08c4c040054c4c021a09001521a08c4c00c8c0c4c040015000530b0032224001c32224001c32300c8c032220c8c032304001d00074002ca2828000ca2824000c32300c8c0a2820c8c0a0824000d000728208b0300d050b03031515000b31514b03080000903031514341431514c2820d050c28215051000b15050c28240034c282150503414140c0a28240010e0c04000c341438300a2820d050a2824000d00044000cb0300c888b03031515000731514b03080008a0303151432223151470300c888703030a09000730a08703040034603030a08322230a0834144002c34144001032220c88834140c888322240011000709051000540014d0c02c0c027072c0c0c54528a08a2822c0c0a28228a08c54509c1cc5451c0c0a28228a08c28240034c2821c0c1000d1c0c0c28228a08a282 (by decide +kernel)

def state247_28 : List Sig := [0x3333333333333333333333333333333333330000333300003333000033330000,input 4,input 7,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 5,input 0,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_28 : Impossible true (goalAt 247) 7 state247_28.toFinset :=
  node_ok cuts247 [] 0x703030a08c28210a08868231300c4c021300c4c028a08343031300c4c021a08868231300343031300c4c00d0c0c4c034300343031300838230700c1c020e08c1c031300151430700c1c028a08313030700c1c020e08838230700313030700c1c00c4c0c1c034300313030700a28230a08703028a08e0c02c0c0a28228a08941430a08474530a08541411d14c7452c0c0474524a08d0c03430090c034300a2820c888d0c034300928224a08d0c02c0c0d0c03430050c00c8c0c2821c0c0c28231300868231300868230700838230700838228208a0820c8c0a28240014474530b00c2c031514c5452c0c03230343009282343009282 (by decide +kernel)

def state247_29 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 4,input 7,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 1,input 5,input 0,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_29 : Impossible true (goalAt 247) 8 state247_29.toFinset :=
  node_ok cuts247 [⟨state247_25,exclude247_25⟩,⟨state247_5,exclude247_5⟩,⟨state247_22,exclude247_22⟩,⟨state247_28,exclude247_28⟩] 0x1c0c0c28230a08703018888c28230a08622221a08c4c03130084c031300a2820d0c0c4c031300868221a08c4c00d0c0c4c031300343031300d0c00d0c0c4c009888c4c031300262220e08c1c030700838230700c4c005450c1c030700a2820c4c0c1c030700838220e08c1c030700838220e08c1c00c4c0c1c030700313030700d0c00c4c0c1c008c88c1c030700232228a08c2821c0c0a28238300b03028a08a28225050270728a08a28209c1cc2821c0c0c2820c8c0868231300868231300a2820c8c0a08230b0032302c0c200020c8c092823430092823430200030c8c032304000cc28215050c28215050b03025050b0302505100124002e00014002cc54524a08d0c03430090c034300a28280000d0c034300928224a08d0c02c0c0d0c0143005545 (by decide +kernel)

def state247_30 : List Sig := [0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 1,input 5,input 0,input 2,input 4,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_30 : Impossible true (goalAt 247) 9 state247_30.toFinset :=
  node_ok cuts247 [⟨state247_9,exclude247_9⟩,⟨state247_20,exclude247_20⟩,⟨state247_24,exclude247_24⟩,⟨state247_27,exclude247_27⟩,⟨state247_29,exclude247_29⟩] 0x40020c5451c0c0c54540020b03030a08c28240020c54530a08c28240020b0301c0c0854540050b0301551455454001cc54534300d0c080010b03034300d0c04001cc5451551450c040020703024a08928240020c28234300d0c040020703034300d0c040020c28224a0890c040015000534300d0c040014a2820c888a2824001600030c888322240014a28234300d0c04002d000b34300d0c04001d000424a0892824002e000024a0892824001d000434300d0c040054c5450d0c0c54540054c14131300c4c040054c54531300c4c040054c1410d0c0c14540054541421a08868240054c28231300c4c040054541431300c4c040054c28221a0884c040054554531300c4c040054d0c00d0c0d0c04005455450d0c0514540054d0c031300c4c040014270731300c4c040014a2820d0c0a2824001427070d0c0343040014a28231300c4c040055001531300c4c040055000221a08868240055001521a08868240055000231300c4c04005cc5450c4c0c5454005cc44430700c1c04005cc54530700c1c04005cc4440c4c0c44540020470720e08838240020c28230700c1c040020470730700c1c040020c28220e0883824005c554530700c1c04005cd0c00c4c0d0c04005c55450c4c054454005cd0c030700c1c040055001530700c1c040054c4c005450c4c040055001705450151440054c4c030700c1c040014270730700c1c040014a2820c4c0a2824001427070c4c0313040014a28230700c1c04000d000330700c1c04000c323020e0883824000d001720e0883824000c323030700c1c04005d001730700c1c04005d000020e0883824005d001720e0883824005d000030700c1c040014b03009c1cb03040014c54528a08a28240014b03028a08a28240014c54509c1cc54540014703028a08a28240014c28240014c28240014703040020703040014c28228a08a2824000d00034000ce0c04000ca2220c8c032304000cc5454000cc5454000ca22280008a0224000cc5450c8c0c5454000cc2820c8c0c2824000c70304000c70304000cc28240020c2824000c70300c8c032304000c92824005892824000cd0c00c8c0d0c04000c92820c8c092824000cd0c04000cd0c04000c86820c8c086824000cc4c04000cc4c04000c86824005486824000cc4c00c8c0c4c04000ca28240014a2824000d00030c8c032304000d00034000ca0824000d000340014c2c04002cb03040018b0304002cc5454002cc5454002cb03080004b0304002cc54540018c54540020c28240004c28240020541440020541440020c28240020c282400205414400045414 (by decide +kernel)

def state247_31 : List Sig := [0xf0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f00000c0c0f0f0f0f00000c0c,input 5,input 4,input 1,input 7,input 0,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_31 : Impossible true (goalAt 247) 6 state247_31.toFinset :=
  node_ok cuts247 [] 0x31514c28230a08854520e08c1c030700838231514c1c030700c44530700c2c020e08c1c030700504414114c1c030700e0c019114c1c030a08c2c030b00323011d14c2c030b00474530b0051450c8c0c2c030b00e0c028208c2c01c0c0c28214514c28214514c545280c051453c300e0c00c888e0c028a08e0c038300a0c019514e0c03830060c021300c4c031300868230700151430700c4c030514c4c031300c54530b00848230b00c4c031300514534300c4c031300614538300c4c0 (by decide +kernel)

def state247_32 : List Sig := [0xffffffff0000ffffffffffff0000ffffffffffff0000ccccffffffff0000cccc,input 5,input 4,input 1,input 7,input 0,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_32 : Impossible true (goalAt 247) 7 state247_32.toFinset :=
  node_ok cuts247 [⟨state247_31,exclude247_31⟩] 0x703030a08c28210a08868231300c4c021300343031300c4c00d0c0c4c014504514531300c4c038300343031302000031300c4c040008838230700c1c020e08c1c031300151430700313030700c1c00c4c0c1c030b00838230700c1c015110544530700c1c038300313030700151430700c1c005450c28230b00c2c00c8c0c2c031300848230b00323030b00c2c010b00c2c015514323030b00c2c038300a08230b00474530b00c2c005850703030a08554530a08554535514a03015514f0c03830032223830055450c888d0c034300a28238300e0c028300b03038300e0c018300654530a08541430a08541431514c5452c0c09414 (by decide +kernel)

def state247_33 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 5,0xffff0000ffff0000ffff0000ffff0000cccc0000cccc0000cccc0000cccc,input 1,input 7,input 0,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_33 : Impossible true (goalAt 247) 7 state247_33.toFinset :=
  node_ok cuts247 [] 0x603030a08c28210a08868231300c4c021300343031300c4c00d0c0c4c00d0c0343031300c4c014504514531300838230700c1c020e08c1c031300151430700313030700c1c00c4c0c1c030b00838230700c1c00c4c0313030700c1c015110544530700c28230b00c2c00c8c0c2c031300848230b00323030b00c2c010b00c2c00c8c0323030b00c2c015514323030b00c282180c0c282180c0c4c00d0c0c4c00d0c0c1c00c4c0c1c00c4c0c54531514a2222c0c0c2c011d14c2c00c8c012220c888322209051000515514d0c034300603030a08503030a08b030250509030240c0e0c0180c0c28215514c28215514d5452c0c05545 (by decide +kernel)

def state247_34 : List Sig := [0xffff0000ffff0000ffff0000ffff0000cccc0000cccc0000cccc0000cccc,input 4,input 1,input 7,input 0,input 2,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_34 : Impossible true (goalAt 247) 8 state247_34.toFinset :=
  node_ok cuts247 [⟨state247_32,exclude247_32⟩,⟨state247_33,exclude247_33⟩] 0x100131c0c070302c0c0c28230a09000d30a08c2822c0c0703010a08703028a08a28230a08e0c038300703038300e0c030a08a28228300b03019514654525050e0c038300b03038300e0c025050654519514541421a08868230a08c4c031300541431300c4c030a08868221300654531300c4c03830034303830065450d0c0614538300c4c03130094140d0c034302c0c0c4c031300941431300c4c02c0c034300d0c0554531300c4c01450434301450455450d0c0514514504c4c031300470720e08838230a08c1c030700470730700c1c030a08838220e08654530700c1c03830031303830065450c4c0644538300c1c030701000f30700c1c031300151431301000e05450151431300c1c03070087070c4c031302c0c0c1c030700870730700c1c02c0c031300c4c1000730700c1c030b00838230b01000e20e08838230b00c1c030700554530700c1c01511031301511055450c4c0544515110c1c030700c2820c8c0c2821c0c0c2c030b00c28230b00c2c01c0c032300c8c0a28230b00c2c038300323038300a2820c8c0a08238300c2c030b00868230b00c2c031300161431300868205850848231300c2c030b00a2220c8c032302c0c0c2c030b00a22230b00c2c02c0c0323010b01000730b00c2c01551432301551500070c8c0323015514c2c030b00703005414703030a08554530a08703015514554530a08150530a08341415514554538301000738300341480004241438300554538300b03015514554528889000735514b0304004cb03028888554515514c28240004c2821c0c100131c0c0c28240034c2821c0c100011c0c0e0c040014e0c019515001319514e0c080000e0c019515000519514c4c040008c4c00d0c100130d0c0c4c04003cc4c00d0c100020d0c0c1c040000c1c00c4c100130c4c0c1c040038c1c00c4c100000c4c0a22240018c5452c0c1000331514a2224000ca2222c0c100062c0c0c2c04000cc2c00c8c1000611d14c2c040018c2c00c8c100030c8c100134001cd0c0 (by decide +kernel)

def state247_35 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 5,0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 1,input 0,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_35 : Impossible true (goalAt 247) 7 state247_35.toFinset :=
  node_ok cuts247 [⟨state247_21,exclude247_21⟩] 0x1c0c0c28230a08703018888c28230a08428221a08c4c03130084c00d0c0c4c031300343009888c4c03130024303130034300d0c0c4c031300d0c00d0c0c4c020e08c1c030700838230700c4c005450c1c030700c2c020e08c1c00c4c0c1c030700313008c88c1c03070023223070031300c4c0c1c030700d0c00c4c0c1c030a08c2c030b00703030b00c4c021208c2c011d14322230b00c2c010b00c2c00d052000030b00c2c034300908230b00c54531514a03040010703030a08503030a08a030250509030240c032220d050322224888e0c024a08d0c03430090c0280c0d0c03430050c015514d0c0343008707 (by decide +kernel)

def state247_36 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 4,0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 1,input 0,input 2,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_36 : Impossible true (goalAt 247) 8 state247_36.toFinset :=
  node_ok cuts247 [⟨state247_22,exclude247_22⟩,⟨state247_35,exclude247_35⟩] 0x4003470301c0c0b03030a08c28240034c28230a08b0301c0c0703040034622218888a22230a08c28240034c28230a08a2221888842821c0c0a28228a08c28238300e0c01c0c0e0c038300c28228a08a0c02c0c0654519514941438300e0c02c0c0e0c038300941419514654528888654519514870738300e0c028888e0c038300870719514654515050868221a08c28231300c4c015050c4c031300c28221a0884c019514c4c031300e0c00d0c0e0c019514343018514e0c031300c4c02505034300d0c0b03031300c4c025050c4c031300b0300d0c034304001cc4c031300d0c00d0c0d0c04003c34300d0c0d0c031300c4c021c1c262209888a22231300c4c021c1cc4c031300a22209888262211c1c838220e08c28230700c1c011c1cc1c030700c28220e08838219514c1c030700e0c00c4c0e0c019514313019114e0c030700c1c04006cc1c030700c4c005450c4c04006c151405450c4c030700c1c04006cc1c030700c2c020e08c2c04006c838220e08c2c030700c1c04006c31300c4c0b03030700c1c04006cc1c030700b0300c4c031304006cc1c030700d0c00c4c0d0c04006c31300c4c0d0c030700c1c021c1c232208c88a22230700c1c021c1cc1c030700a22208c88232230a09000d30a08703030b00c2c030a08c2c030b0070304001c703028a08c2c030b00e0c04001ce0c028a0a000028208e0c030b00c2c021a08c2c030b00c4c04001cc4c021a09000f21208c4c030b00c2c040019000611d14928230b00c2c03430100073430092824001c908234300c2c030b00a22240048a2224000cc2c030b00a22230b00c2c04000d000710b00a22240010c5454000cb03031514a2222c0c0b0304000d00044000c703024a08928230a08d0c034300703034300d0c030a08928224300341434300d0c038301000738300341480004341438300d0c034300b0304004cb03040010d0c034300b03034300d0c0400110007143010006400185545 (by decide +kernel)

def state247_37 : List Sig := [0xffff0000ffffffffffff0000ffffffffffff0000ffffccccffff0000ffffcccc,input 4,input 5,input 1,input 7,input 0,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_37 : Impossible true (goalAt 247) 7 state247_37.toFinset :=
  node_ok cuts247 [] 0x703030a08c28210a08868231300c4c021300343031300c4c00d0c0c4c018504614531300c4c034300343031300262231300c4c009888838230700c1c020e08c1c031300151430700313030700c1c00c4c0c1c030b00838230700c1c019110644530700c1c034300313030700232230700c1c008c88c28230b00c2c00c8c0c2c031300848230b00323030b00c2c010b00c2c019514323030b00c2c034300908230b00474530b00c2c04000c703030a08654530a08654539514903019514928234300d0c024300b03034300d0c014300d0c03c300341434300554530a08622230a08622231514c5452c0c0a2220d050654538300e0c0 (by decide +kernel)

def state247_38 : List Sig := [0xffffffff00000000ffffffff00000000cccccccc00000000cccccccc,input 5,input 1,input 7,input 0,input 2,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_38 : Impossible true (goalAt 247) 8 state247_38.toFinset :=
  node_ok cuts247 [⟨state247_37,exclude247_37⟩] 0x100131c0c070302c0c0c28230a09001930a08c2822c0c0703010a08703024a08928230a08d0c034300703034300d0c030a08928224300b03015514554528888d0c034300b03034300d0c028888554515514341434300d0c01951432221951434140c888322219514d0c034300541421a08868230a08c4c031300541431300c4c030a08868221300554531300c4c03430034303430055450d0c0514534300c4c03130087070d0c034302c0c0c4c031300870731300c4c02c0c034300d0c0654531300c4c01850434301850465450d0c0614518504c4c031300470720e08838230a08c1c030700470730700c1c030a08838220e08554530700c1c03430031303430055450c4c0544534300c1c030701001430700c1c031300151431301001d05450151431300c1c03070087070c4c031302c0c0c1c030700870730700c1c02c0c031300c4c1000b30700c1c030b00838230b01001d20e08838230b00c1c030700654530700c1c01911031301911065450c4c0644519110c1c030700c2820c8c0c2821c0c0c2c030b00c28230b00c2c01c0c032300c8c0928230b00c2c03430032303430092820c8c0908234300c2c030b00868230b00c2c031301000b31300868240050848231300c2c030b00a2220c8c032302c0c0c2c030b00a22230b00c2c02c0c0323010b01000b30b00c2c019514323019515000b0c8c0323019514c2c030b0070300d050703030a08654530a08703019514654530a08341430a08b03019514654521c1d000b39514b0304004cb03021c1c654519514c28240004c2821c0c100131c0c0c28240064c2821c0c100011c0c0d0c040010d0c015515001315514d0c080000d0c015515000415514c4c040008c4c00d0c100130d0c0c4c040050c4c00d0c100020d0c0c1c040000c1c00c4c100130c4c0c1c040074c1c00c4c100000c4c0870740018c5452c0c100033151487074000c87072c0c100062c0c0c2c04000cc2c00c8c1000611d14c2c040018c2c00c8c100030c8c100134002ce0c0 (by decide +kernel)

def state247_39 : List Sig := [0xffffffffffffffffffffffffffffffffffffccccffffccccffffccccffffcccc,input 4,0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 1,input 7,input 0,input 2,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_39 : Impossible true (goalAt 247) 8 state247_39.toFinset :=
  node_ok cuts247 [] 0x1c0c0c28230a0842821c0c0c28230a08703018080c28230a08602028a08e0c038300a0c019514e0c038300654519514e0c038300654519514e0c038300654521a08c4c03130084c031300e0c018514c4c00d0c0c4c03130034300d0c0c4c031300343031300d0c00d0c0c4c009080c4c031300242020e08c1c030700838230700e0c019114c1c030700c4c005450c1c00c4c0c1c030700313030700c2c020e08c1c00c4c0c1c030700313030700d0c00c4c0c1c008480c1c03070021202c0c1000730a08c2c030b00703030b00e0c028208c2c030b00c4c021208c2c028888c2c010b00323030b00d0c024208c2c040049000424a08d0c03430090c034300e0c00c888d0c00c888d0c03430032224004cd0c04001c5545 (by decide +kernel)

def state247_40 : List Sig := [0x33333333333300003333333333330000,input 4,input 5,input 1,input 7,input 0,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_40 : Impossible true (goalAt 247) 7 state247_40.toFinset :=
  node_ok cuts247 [] 0x31514c28230a08854521a08c4c03130084c031514c4c031300c14531300e0c00d0c0c4c031300d0c00d0c0c4c020e08c1c030700838230700c4c005450c1c031514c1c030700c44530700c2c020e08c1c030700e0c00c4c0c1c030700d0c00c4c0c1c030a08c2c030b00703030b00c4c021208c2c011d14c2c030b00474530b00e0c028208c2c030b00d0c024208c2c028a08e0c038300a0c039514e0c038300c54524a08d0c03430090c035514d0c034300c54534300e0c00c888d0c01c0c0c2821c0c0c2820d0c0c4c00d0c0c4c00c4c0c1c00c4c0c1c02c0c0323019514e0c00d050e0c015514d0c040014d0c0 (by decide +kernel)

def state247_41 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,input 5,0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 1,input 7,input 0,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_41 : Impossible true (goalAt 247) 8 state247_41.toFinset :=
  node_ok cuts247 [⟨state247_5,exclude247_5⟩,⟨state247_33,exclude247_33⟩,⟨state247_35,exclude247_35⟩,⟨state247_19,exclude247_19⟩,⟨state247_8,exclude247_8⟩,⟨state247_23,exclude247_23⟩,⟨state247_40,exclude247_40⟩] 0x1c0c0c28230a0842821c0c0c28230a08703021a08c4c03130084c00d0c0c4c03130034300d0c0c4c03130034303130034300d0c0c4c03130034300d0c0c4c03130034300d0c0c4c020e08c1c030700838230700c4c005450c1c00c4c0c1c030700313030700c2c020e08c1c00c4c0c1c03070031303070031300c4c0c1c03070031300c4c0c1c03070031300c4c0c1c031514c28230b00c2c01c0c0c2c031300848230b00a22230b0042c011d14c2c00d052000530b00c2c04002c322230b00c2c04000e000430b00703030a08503030a08a22221c1ca2220d05034144001600030d050e0c01c0c0c282180c0c2820c888a2228000832228000432220c88900040d050322209050d0c01c0c0c2821c0c0c2822888887072888887074004e0006800010013 (by decide +kernel)

def state247_42 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0c0c0c0c0f0f0f0f0c0c0c0c,input 5,0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 1,input 7,input 0,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_42 : Impossible true (goalAt 247) 7 state247_42.toFinset :=
  node_ok cuts247 [] 0x703030a08c28210a08703030a08c2821c0c0928234300d0c024300514534300d0c014514514534300d0c014514d0c038300322234300838230700c1c020e08c1c034300504530700313030700c1c00c4c0c1c030b00838230700313030700c1c00c4c0c1c038300644530700c54530a08c2c030b00703030b00d0c024208c2c028888c2c010b00474530b00e0c028208c2c028a08e0c038300a0c019514e0c038300654519514e0c038300654521300c4c031300868231300514534300c4c030700151430700c4c00d0c0c4c031300343030b00848230b00c4c00d0c0c4c031300343031300614538300c4c0 (by decide +kernel)

def state247_43 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffccccccccffffffffcccccccc,input 5,0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 1,input 7,input 0,input 2,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_43 : Impossible true (goalAt 247) 8 state247_43.toFinset :=
  node_ok cuts247 [⟨state247_42,exclude247_42⟩] 0x1c0c0c28230a0842821c0c0c28230a08703015050c28230a08541424a08d0c03430090c015514d0c034300554515514d0c034300554534300e0c00c888d0c015514d0c034300554521a08c4c03130084c031300d0c014514c4c00d0c0c4c03130034300d0c0c4c031300343031300e0c00d0c0c4c080000c4c031301001c20e08c1c030700838230700d0c015114c1c030700c4c005450c1c00c4c0c1c030700313030700c2c020e08c1c00c4c0c1c030700313030700e0c00c4c0c1c005450c1c03070015142c0c1000b30a08c2c030b00703030b00d0c024208c2c030b00c4c021208c2c028888c2c010b00323030b00e0c028208c2c040051000528a08e0c038300a0c028888e0c03830027074004ce0c04002c6545 (by decide +kernel)

def state247_44 : List Sig := [0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 1,input 7,input 0,input 2,input 4,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_44 : Impossible true (goalAt 247) 9 state247_44.toFinset :=
  node_ok cuts247 [⟨state247_12,exclude247_12⟩,⟨state247_24,exclude247_24⟩,⟨state247_11,exclude247_11⟩,⟨state247_20,exclude247_20⟩,⟨state247_34,exclude247_34⟩,⟨state247_36,exclude247_36⟩,⟨state247_38,exclude247_38⟩,⟨state247_39,exclude247_39⟩,⟨state247_41,exclude247_41⟩,⟨state247_43,exclude247_43⟩] 0x4001900061c0c0703040018a22230a08c28240019000830a08c28240018a2221c0c042824002100081c0c0703040021000130a08c28240021000830a08c2824002100011c0c0703040020703028a08a28240020c28238300e0c040020703038300e0c040020c28228a08a0c040018a22219514654540018870738300e0c040018a22238300e0c04001887071951465454004e00061951465454002d000538300e0c080026000338300e0c04002d000519514654540020703024a08928240020c28234300d0c040020703034300d0c040020c28224a0890c04002c341434300d0c04001ce0c00c888e0c08002034140c88832224001ce0c034300d0c040019000615514554540018a22234300d0c04001a000534300d0c040018a2221551455454004e00041551455454001d000434300d0c08001e000234300d0c04001d000415514554540020541421a08868240020c28231300c4c040020541431300c4c040020c28221a0884c04002c654531300c4c040070e0c00d0c0e0c04005065450d0c0614540070e0c031300c4c04001c554531300c4c040070d0c00d0c0d0c04003c55450d0c0514540070d0c031300c4c04001887070d0c0343040018a22231300c4c040018870731300c4c040018a2220d0c034304004d001a0d0c0343040071000231300c4c040069001a31300c4c04007100020d0c0343040020470720e08838240020c28230700c1c040020470730700c1c040020c28220e0883824006c654530700c1c04006ce0c00c4c0e0c04006c65450c4c064454006ce0c030700c1c04006c554530700c1c04006cd0c00c4c0d0c04006c55450c4c054454006cd0c030700c1c04006d001b30700c1c04006cc4c005450c4c04006d001b0545015144006cc4c030700c1c04001887070c4c0313040018a22230700c1c040018870730700c1c040018a2220c4c031304000d000330700c1c04000cc2c020e08c2c04000d001b20e0883824000cc2c030700c1c04006d001b0c4c031304006d000030700c1c04006d001b30700c1c04006d00000c4c031304000d00034000cc5454000cc28240020c2824000c703030b00c2c04000cc28230b00c2c04000c70304000c70304000ca28230b00c2c04000ce0c04000ce0c04000ca28280004a0824000ce0c030b00c2c04000c928230b00c2c04000cd0c04000cd0c04000c92828000090824000cd0c030b00c2c04000c868230b00c2c04000cc4c04000cc4c04000c86824006884824000cc4c030b00c2c04000ca22240018a2224000d000330b00c2c04000d00034000c42c04000d0003400184745 (by decide +kernel)

def state247_45 : List Sig := [0x505050505050505050505050505050505050505050500000505050505050000,0x5555555555555555555555555555555555555555555500005555555555550000,input 7,input 4,input 5,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_45 : Impossible true (goalAt 247) 6 state247_45.toFinset :=
  node_ok cuts247 [] 0xc14530a08c28220514c28230b00c2c00c8c0c2c038300a08230b00c2c034300908230b00464530b00c2c011914a28238300e0c028300614538300e0c018300928234300d0c024300d0c038300322234300514534300d0c014300c2821081cc28205450c2c011914c2c011914e0c018514e0c018514d0c014514d0c014514c44530514b0303051484c031300c4c021a08c2c021208c2c031300c4c018514e0c031300c4c014514d0c031300343031300c4c030514c1c0 (by decide +kernel)

def state247_46 : List Sig := [0x5555555555555555555555555555555555555555555500005555555555550000,input 7,input 4,input 5,input 1,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_46 : Impossible true (goalAt 247) 7 state247_46.toFinset :=
  node_ok cuts247 [⟨state247_45,exclude247_45⟩] 0x31514703031514b03030a08c28231514c28230a08b0301c0c0854515050868221a08c28231300c4c015050c4c031300c28221a0884c019514c4c031300e0c00d0c0e0c019514343018514e0c031300c4c015514c4c031300d0c00d0c0d0c015514343014514d0c031300c4c031514343031514c14131300c4c031514c4c031300c1410d0c0c14530a08323030a08703030b00c2c030a08c2c030b0070300c8c0323021a08c2c030b00c4c011914c4c021a08464521208c4c030b00c2c028a08c2c030b00e0c00c8c0e0c028a08323028208e0c030b00c2c024a08c2c030b00d0c00c8c0d0c024a08323024208d0c030b00c2c028888464511914c54530b00c2c028888c2c030b00c5451191446451c0c0a28228a08c28238300e0c01c0c0e0c038300c28228a08a0c02c0c0654519514c54538300e0c02c0c0e0c038300c5451951460c01c0c0928224a08c28234300d0c01c0c0d0c034300c28224a0890c00d050d0c034300e0c00c888e0c00d05032220c888e0c034300d0c02c0c0554515514c54534300d0c02c0c0d0c034300c5451551450c030a08838220e08460730700c1c030a08c1c030700460720e08838231300c1c030702000005450151431300151431301001830700c1c030b00c1c030700464520e08838230b00838230b00464530700c1c038300c1c03070065450c4c0644538300313038300654530700c1c034300c1c03070055450c4c0544534300313034300554530700c1c02c0c0313031114c54530700c1c02c0c0c1c030700c5450c4c0c545 (by decide +kernel)

def state247_47 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0f0f0f0f0000,input 7,input 4,input 5,input 0,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_47 : Impossible true (goalAt 247) 7 state247_47.toFinset :=
  node_ok cuts247 [] 0x31514703031514b03030a08c28231514c28230a08b0301c0c0854530a08323030a08703030b00c2c030a08c2c030b0070300c8c0323028a08c2c030b00e0c00c8c0e0c028a08323028208e0c030b00c2c024a08c2c030b00d0c00c8c0d0c024a08323024208d0c030b00c2c028888474511d14c54530b00c2c028888c2c030b00c54511d14474510c1c838220e08c28230700c1c010c1cc1c030700c28220e08838211d14c1c030700c2c020e08c2c011d14838220e08c2c030700c1c019514c1c030700e0c00c4c0e0c019514313019114e0c030700c1c015514c1c030700d0c00c4c0d0c015514313015114d0c030700c1c031514313031514c44430700c1c031514c1c030700c4440c4c0c4451c0c0a28228a08c28238300e0c01c0c0e0c038300c28228a08a0c02c0c0654519514c54538300e0c02c0c0e0c038300c5451951460c01c0c0928224a08c28234300d0c01c0c0d0c034300c28224a0890c00d050d0c034300e0c00c888e0c00d05032220c888e0c034300d0c02c0c0554515514c54534300d0c02c0c0d0c034300c5451551450c030a08868221300541431300c4c030a08c4c031300541421a08868230b00c4c030b00474521a08848230b00868230b00474531300c4c030700c4c030700151440060151430701001830700151431300c4c038300c4c03130065450d0c0614538300343038300654531300c4c034300c4c03130055450d0c0514534300343034300554531300c4c02c0c0343030514c54531300c4c02c0c0c4c031300c5450d0c0c545 (by decide +kernel)

def state247_48 : List Sig := [0xffffffffffff0000ffffffffffff0000,0xffffffffffffffffffffffffffffffffffffffffffff0000ffffffffffff0000,input 4,input 5,input 0,input 1,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_48 : Impossible true (goalAt 247) 7 state247_48.toFinset :=
  node_ok cuts247 [] 0xc54530a08c28221514868231300c4c021300c4c038300343031300c4c034300343031300c54531300c4c030514c28230b00c2c00c8c0c2c031300848230b00c2c038300a08230b00c2c034300908230b00474530b00c2c011d14838230700c1c020e08c1c031300151430700c1c030b00838230700c1c038300313030700c1c034300313030700c54530700c1c031114a28238300e0c028300e54524a08d0c03430090c034300e0c00c888d0c035514703030a08703030a08343031300343031300323030b00323030b0031303070031303070060c038300b0303830050c034300b030343010001 (by decide +kernel)

def state247_49 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0f0f0f0f0000,0x5555555555555555555555555555555555555555555500005555555555550000,input 7,input 4,input 5,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_49 : Impossible true (goalAt 247) 6 state247_49.toFinset :=
  node_ok cuts247 [] 0x31514c28230a08854530a08c2c030b00323030b00e0c028208c2c030b00d0c024208c2c011914c2c030b00464528a08e0c038300a0c019514e0c03830060c024a08d0c03430090c034300e0c00c888d0c015514d0c03430050c020e08c1c030700838230700838230b00c1c030700644538300c1c030700544534300c1c031114c1c030700c54521300c4c031300868230b00848230b00c4c031300614538300c4c031300514534300c4c030514c4c031300c54530700c4c0307001514 (by decide +kernel)

def state247_50 : List Sig := [0x5555555555555555555555555555555555555555555500005555555555550000,0xffffffffffffffffffffffffffffffffffffffffffff0000ffffffffffff0000,input 7,input 4,input 5,input 1,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_50 : Impossible true (goalAt 247) 7 state247_50.toFinset :=
  node_ok cuts247 [⟨state247_49,exclude247_49⟩] 0x1c0c0c28230a0870301181cc28230a08460721a08c4c03130084c031300e0c00d0c0c4c031300d0c00d0c0c4c00d0c0c4c031300343080000c4c031301001830a08c2c030b00323030b00c4c021208c2c030b00e0c028208c2c030b00d0c024208c2c011914c2c030b00464511914c2c030b00464528a08e0c038300a0c02c0c0e0c03830060c019514928234300d0c024300d0c038300322234300b03034300d0c014300554531514838230700c1c020e08c1c005450c4c030700c1c020e08c2c030700c1c00c4c0e0c030700c1c00c4c0d0c030700313030700c1c00c4c10000 (by decide +kernel)

def state247_51 : List Sig := [0x3333333333333333333333333333333333333333333300003333333333330000,input 1,input 7,input 4,input 5,input 0,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_51 : Impossible true (goalAt 247) 7 state247_51.toFinset :=
  node_ok cuts247 [] 0x703030a08c28210a08868231300c4c021300c4c038300343031300c4c034300343031300343031300c4c00d0c0838230700c1c020e08c1c031300151430700c1c038300313030700c1c034300313030700313030700c1c00c4c0c1c020e08838230700a28238300e0c028300b03038300e0c018300928234300d0c024300d0c038300322234300b03034300d0c014300c28211d14c2821c0c0868231300868231300a28238300a28238300928234300928234300474531d14a22211d14703030a08703030a08c4c021a08c4c021a08c1c020e08c1c020e08e0c028a08e0c028a08d0c024a08d0c024a08c54531514b03028888c2c0 (by decide +kernel)

def state247_52 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0f0f0f0f0000,0xffffffffffffffffffffffffffffffffffffffffffff0000ffffffffffff0000,input 7,input 4,input 5,input 0,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_52 : Impossible true (goalAt 247) 7 state247_52.toFinset :=
  node_ok cuts247 [⟨state247_49,exclude247_49⟩] 0x1c0c0c28230a08703010c1cc28230a08430730a08c2c030b00323030b00e0c028208c2c030b00d0c024208c2c011d14c2c030b00474511d14c2c030b00474520e08c1c030700838230700c2c020e08c1c030700e0c00c4c0c1c030700d0c00c4c0c1c00c4c0c1c030700313080000c1c030701001828a08e0c038300a0c02c0c0e0c03830060c019514928234300d0c024300d0c038300322234300b03034300d0c01430055453151484c031300c4c021a08c2c021208c2c031300c1c005450c1c031300c4c00d0c0e0c031300c4c00d0c0d0c031300343031300c4c00d0c10002 (by decide +kernel)

def state247_53 : List Sig := [0x5555555555555555555555555555555555555555555555555555555555550000,input 6,input 7,input 4,input 5,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_53 : Impossible true (goalAt 247) 6 state247_53.toFinset :=
  node_ok cuts247 [] 0x31300e0c018514c4c031300d0c014514c4c031514c4c031300c14521a08c4c03130084c030b00c4c021208c2c030b00e0c028208c2c030b00d0c024208c2c011d14c2c030b00474530a08c2c030b00323019514e0c03830060c028a08e0c038300a0c034300e0c00c888d0c015514d0c03430050c024a08d0c03430090c031514c28230a08854530700151431300c1c030700838230b00c1c030700644538300c1c030700544534300c1c031114c1c030700c54520e08c1c0307008382 (by decide +kernel)

def state247_54 : List Sig := [0x3333333333333333333333333333333333333333333333333333333333330000,input 6,input 7,input 4,input 5,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_54 : Impossible true (goalAt 247) 6 state247_54.toFinset :=
  node_ok cuts247 [] 0x31300e0c018514c4c031300d0c014514c4c031514c4c031300c14521a08c4c03130084c030700c4c005450c1c030700e0c019114c1c030700d0c015114c1c031514c1c030700c44520e08c1c030700838219514e0c03830060c028a08e0c038300a0c034300e0c00c888d0c015514d0c03430050c024a08d0c03430090c031514c28230a08854530b00848231300c2c030700838230700c2c030b00a08238300c2c030b00908234300c2c011d14c2c030b0047450c8c0c2c030b00c282 (by decide +kernel)

def state247_55 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0000,input 6,input 7,input 4,input 5,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_55 : Impossible true (goalAt 247) 6 state247_55.toFinset :=
  node_ok cuts247 [] 0x30b00e0c028208c2c030b00d0c024208c2c011d14c2c030b00474530a08c2c030b00323030700c2c020e08c1c030700e0c019114c1c030700d0c015114c1c031514c1c030700c44520e08c1c030700838219514e0c03830060c028a08e0c038300a0c034300e0c00c888d0c015514d0c03430050c024a08d0c03430090c031514c28230a08854530b00848230b00c4c030700151430700c4c031300614538300c4c031300514534300c4c030514c4c031300c54521300c4c0313008682 (by decide +kernel)

def state247_56 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000,input 6,input 7,input 4,input 5,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_56 : Impossible true (goalAt 247) 7 state247_56.toFinset :=
  node_ok cuts247 [⟨state247_53,exclude247_53⟩,⟨state247_54,exclude247_54⟩,⟨state247_55,exclude247_55⟩] 0x31300e0c018514c4c031300d0c014514c4c031514c4c031300c14521a08c4c03130084c080008c4c031301000230b00c4c021208c2c030b00e0c028208c2c030b00d0c024208c2c011d14c2c030b00474530a08c2c030b00323080004c2c030b01000330700c4c005450c1c030700c2c020e08c1c030700e0c019114c1c030700d0c015114c1c031514c1c030700c44520e08c1c030700838280000c1c030701000019514e0c03830060c028a08e0c038300a0c009c1cd0c038300322234300554534300d0c014300928234300d0c024300170721c1cc54530a08c282215144707 (by decide +kernel)

def state247_57 : List Sig := [0xffffffffffffffff0000000000000000ffffffffffff0000,input 6,input 7,input 4,input 5,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_57 : Impossible true (goalAt 247) 7 state247_57.toFinset :=
  node_ok cuts247 [] 0xc4c038300614531300c4c034300514531300c54531300c4c030514868231300c4c021a08c2c031300848230b00c2c038300a08230b00c2c034300908230b00474530b00c2c011d14323030b00c2c00c8c0c1c031300151430700c1c030b00838230700c1c038300644530700c1c034300544530700c54530700c1c031114838230700c1c020e08654538300e0c018300a28238300e0c028a08d0c038300322234300554534300d0c014300928234300d0c024a08c5452c0c0c5452c0c0868231300868231300323030b00323030b00838230700838230700a28238300a28238300928234300928234300b03031514b03031514c282 (by decide +kernel)

def state247_58 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,0xffffffffffffffffffffffffffffffffffffffffffff0000ffffffffffff0000,input 4,input 5,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_58 : Impossible true (goalAt 247) 7 state247_58.toFinset :=
  node_ok cuts247 [] 0xc4c038300343031300c4c034300343031300c54531300c4c030514868231300c4c021300343031300c4c00d0c0c2c031300848230b00c2c038300a08230b00c2c034300908230b00474530b00c2c011d14c28230b00c2c00c8c0323030b00c2c00c8c0c1c031300151430700c1c030b00838230700c1c038300313030700c1c034300313030700c54530700c1c031114838230700c1c020e08313030700c1c00c4c0654528a08e0c038300a0c02c0c0e0c038300903034300e0c00c888d0c015514928234300d0c024300b03034300d0c0280c0b03031514c54540004c54530a08c282215147030 (by decide +kernel)

def state247_59 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffff0000ffffffffffff0000,input 7,input 4,input 5,input 0,input 1,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_59 : Impossible true (goalAt 247) 8 state247_59.toFinset :=
  node_ok cuts247 [⟨state247_5,exclude247_5⟩,⟨state247_46,exclude247_46⟩,⟨state247_47,exclude247_47⟩,⟨state247_48,exclude247_48⟩,⟨state247_50,exclude247_50⟩,⟨state247_51,exclude247_51⟩,⟨state247_52,exclude247_52⟩,⟨state247_56,exclude247_56⟩,⟨state247_57,exclude247_57⟩,⟨state247_58,exclude247_58⟩] 0x100141c0c070302c0c0c28230a0a000930a08c2822c0c070301c0c2000811c1c470740004c28230a0a000730a08c28240004470711c1c541421a08868230a08c4c031300541431300c4c030a08868221300341431300c4c03830034303830034140d0c0343038300c4c031301001431300c4c03430034303430100140d0c0343034300c4c03130094140d0c034302c0c0c4c031300941431300c4c02c0c034300d0c100148001a000240008c4c031301001431300c4c040009001440008c2820c8c0c2821c0c0c2c030b00c28230b00c2c01c0c032300c8c0868230b00c2c031300474531300868211d14848231300c2c030b00a28230b00c2c038300323038300a2820c8c0a08238300c2c030b00928230b00c2c03430032303430092820c8c0908234300c2c030b00a22211d1447452c0c0c2c030b00a22230b00c2c02c0c0474511d16000511d1447454000cc2c030b02000030b00c2c04000c474511d14470720e08838230a08c1c030700470730700c1c030a08838220e09001430700c1c031300151431301001805450151431300c1c030700474530700c1c030b00838230b00474520e08838230b00c1c030701001430700c1c03830031303830100180c4c0313038300c1c030701001830700c1c03430031303430100180c4c0313034300c1c03070100140c4c031302c0c0c1c030701001830700c1c02c0c031300c4c1001880012000140000c1c030701001830700c1c040001001840000703028a08a28230a08e0c038300703038300e0c030a08a28228300b0300d050b03025050e0c038300b03038300e0c02505034141830100124004865451c0c0928224a08c28234300d0c01c0c0d0c034300c28224a0890c00d050d0c034300e0c00c888e0c00d05032220c888e0c034300d0c02c0c032222c0c0a22234300d0c02c0c0d0c034300a2220c88850c04005100141551500148000cc545 (by decide +kernel)

def state247_60 : List Sig := [0xcccccccccccccccc0000000000000000ffffffffffffcccc,input 1,input 7,input 4,input 5,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_60 : Impossible true (goalAt 247) 6 state247_60.toFinset :=
  node_ok cuts247 [] 0x31300e0c018514c4c031300d0c014514c4c021514c4c031300814530700c4c005450c1c030700e0c019114c1c030700d0c015114c1c021514c1c030700844530700c2c020e08c1c019514e0c038300608034300e0c00c888d0c015514d0c034300508030b00c4c021a08c2c030b00e0c028a08c2c030b00d0c024a08c2c011d14c2c030b00474521a08c4c021a08c4c020e08c1c020e08c1c028a08e0c028a08e0c024a08d0c024a08d0c010a08c28230a0885450c8c0c2c030a08c2c0 (by decide +kernel)

def state247_61 : List Sig := [0xccccccccccccccccccccccccccccccccffffffffffffccccffffffffffffcccc,input 1,input 7,input 4,input 5,input 0,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_61 : Impossible true (goalAt 247) 7 state247_61.toFinset :=
  node_ok cuts247 [⟨state247_60,exclude247_60⟩] 0xc54530a08c28221514868231300c4c021300c4c038300343031300c4c034300343031300c54531300c4c030514838230700c1c020e08c1c031300151430700c1c038300313030700c1c034300313030700c54530700c1c031114c1c020e08838230700c1c020e08838230700a28238300e0c028300e54538300e0c031514928234300d0c024300d0c038300322234300d54534300d0c031514c2821c0c0c2820c8c0868231300868231300a28238300a28238300928234300928234300323031514a22231514c2c030a0a000030a09000121a08c4c021a08c4c028a08e0c028a08e0c024a08d0c024a08d0c028888c5452c0c0c545 (by decide +kernel)

def state247_62 : List Sig := [0x3333333333333333000000000000000033333333333333333333333333330000,input 6,input 7,input 4,input 5,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_62 : Impossible true (goalAt 247) 6 state247_62.toFinset :=
  node_ok cuts247 [] 0x31300e0c018514c4c031300d0c014514c4c031514c4c031300c14521208c4c031300848230700c4c005450c1c030700e0c019114c1c030700d0c015114c1c031514c1c030700c44520e08c1c030700838219514e0c03830060c028208e0c038300a08234300e0c00c888d0c015514d0c03430050c024208d0c034300908231514c28230a08428030b00848231300c2c030700838230700c2c030b00a08238300c2c030b00908234300c2c011d14c2c030b0047450c8c0c2c030b00c282 (by decide +kernel)

def state247_63 : List Sig := [0xffffffffffffffff0000000000000000ffffffffffffffffffffffffffff0000,input 6,input 7,input 4,input 5,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_63 : Impossible true (goalAt 247) 7 state247_63.toFinset :=
  node_ok cuts247 [⟨state247_62,exclude247_62⟩] 0xc4c038300614531300c4c034300514531300c54531300c4c030514868231300c4c021a08868231300c4c021a08c2c031300848230b00c2c038300a08230b00c2c034300908230b00474530b00c2c011d14323030b00c2c00c8c2000030b00c2c04000cc1c031300151430700c1c030b00838230700c1c038300644530700c1c034300544530700c54530700c1c031114838230700c1c020e08838230700c1c020e08654538300e0c018300a28238300e0c028a08a28238300e0c028a08d0c038300322234300554534300d0c014300928234300d0c024a08928234300d0c024a08c5453c0c0c5451c0c0c28231514870731514b030 (by decide +kernel)

def state247_64 : List Sig := [0xffffffffffff0000,input 6,input 7,input 4,input 5,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_64 : Impossible true (goalAt 247) 7 state247_64.toFinset :=
  node_ok cuts247 [] 0x31300e0c018514c4c031300d0c014514c4c031514c4c031300c14521a08c4c03130084c030b00c4c021208c2c030b00e0c028208c2c030b00d0c024208c2c011d14c2c030b00474530a08c2c030b00323030700c4c005450c1c030700c2c020e08c1c030700e0c019114c1c030700d0c015114c1c031514c1c030700c44520e08c1c030700838219514e0c03830060c028a08e0c038300a0c034300e0c00c888d0c015514d0c03430050c024a08d0c03430090c031514c28230a0885450d0c0c4c00d0c0c4c00c8c0c2c00c8c0c2c00c4c0c1c00c4c0c1c00d050e0c00d050e0c00c888d0c00c888d0c02c0c07030 (by decide +kernel)

def state247_65 : List Sig := [0xffffffffffff0000ffffffffffff0000,input 7,input 4,input 5,input 0,input 1,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_65 : Impossible true (goalAt 247) 8 state247_65.toFinset :=
  node_ok cuts247 [⟨state247_48,exclude247_48⟩,⟨state247_40,exclude247_40⟩,⟨state247_61,exclude247_61⟩,⟨state247_63,exclude247_63⟩,⟨state247_64,exclude247_64⟩] 0xc5451c0c0c54521c1cc28230a08c54530a08c28221c1c703021514541421a08868230a08c4c031300541431300c4c030a08868221300341431300c4c03830034303830034140d0c0343038300c4c031301001431300c4c03430034303430100140d0c0343034300c4c031300c5450d0c0c54530504c4c031300c54531300c4c030504343030514c2820c8c0c2821c0c0c2c030b00c28230b00c2c01c0c032300c8c0868230b00c2c031300474531300868211d14848231300c2c030b00a28230b00c2c038300323038300a2820c8c0a08238300c2c030b00928230b00c2c03430032303430092820c8c0908234300c2c030b00870711d14474531514c2c030b00870730b00c2c031514474511d14470720e08838230a08c1c030700470730700c1c030a08838220e09001430700c1c031300151431301001805450151431300c1c030700474530700c1c030b00838230b00474520e08838230b00c1c030701001430700c1c03830031303830100180c4c0313038300c1c030701001830700c1c03430031303430100180c4c0313034300c1c030700c5450c4c0c54531110c1c030700c54530700c1c031110313031114703028a08a28230a08e0c038300703038300e0c030a08a2822830100140d050e54531514e0c038301001438300e0c031514341431514703024a08928230a08d0c034300703034300d0c030a08928224300341434300d0c03830032223830034140c888322238300d0c03430100140c888d54531514d0c034301002034300d0c031514322231514703040004703030a0a000430a0870308000c703030a09000130a0834304000834303130100143130034304005034303130100023130032304000c323030b02000130b00323080008323030b01000330b00313040000313030701001830700313040060313030701000030700341440018654538301000438300341440010341438301000638300322240018554534301000534300322240014322234301000634302000040050b030 (by decide +kernel)

def state247_66 : List Sig := [0xffffffffffff0000ffffffffffff0000,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 5,input 0,input 1,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_66 : Impossible true (goalAt 247) 7 state247_66.toFinset :=
  node_ok cuts247 [] 0x31514c28230a08854521a08c4c03130084c03130034300d0c0c4c031514c4c031300c14531300d0c00d0c0c4c030a08c2c030b00323030b00c4c021208c2c030b0032300c8c0c2c011d14c2c030b00474530b00d0c024208c2c020e08c1c030700838230700c4c005450c1c030700c2c020e08c1c03070031300c4c0c1c031514c1c030700c44530700d0c00c4c0c1c01c0c0c282140c0c2820c888c5450c888c54538300928234300d0c024300d54534300d0c031514703030a08703030a08343031300343031300323030b00323030b003130307003130307009030240c0a03025050322231514a0303151450c0 (by decide +kernel)

def state247_67 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_67 : Impossible true (goalAt 247) 6 state247_67.toFinset :=
  node_ok cuts247 [] 0x31300d0c018514c4c031514c4c031300c14521a08c4c03130084c00d0c0c4c031300343030b00c4c021208c2c030b00d0c024208c2c011d14c2c030b00474530a08c2c030b0016140c8c0c2c030b00323030700c4c005450c1c030700c2c020e08c1c030700d0c019114c1c031514c1c030700c44520e08c1c03070083820c4c0c1c030700313015514d0c03430060c024a08d0c03430090c0140c0d0c0343002545140c0c54531514603031514c28230a088545140c0c28230a089030 (by decide +kernel)

def state247_68 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 6,0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 7,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_68 : Impossible true (goalAt 247) 7 state247_68.toFinset :=
  node_ok cuts247 [⟨state247_67,exclude247_67⟩] 0x31300d0c018514c4c00d0c0c4c031300343009888c4c031300243021a08c4c031300868221a08c4c031300868230b00c4c021208c2c030b00d0c024208c2c011d14c2c030b00474511d14c2c030b0047450c8c0c2c030b00323005850c2c030b00161430700c4c005450c1c030700c2c020e08c1c030700d0c019114c1c00c4c0c1c030700313008c88c1c030700232220e08c1c030700838220e08c1c030700838219514d0c03430070c015514d0c034300654524a08d0c034300b0c024a08d0c0343009282315145030280c20000140c05222140c05030180c0c282280c09414240c090300c88834140c8882414 (by decide +kernel)

def state247_69 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffffffff0000ffff0000,input 6,input 7,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 5,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_69 : Impossible true (goalAt 247) 7 state247_69.toFinset :=
  node_ok cuts247 [] 0xc4c00d0c0343031300c4c034300514531300c54531300c4c030514868231300c4c021300262231300c4c0090c0c2c031300848230b00c2c00c8c0323030b00c2c034300908230b00474530b00c2c011d14c28230b00c2c00c8c0322230b00c2c04001cc1c031300151430700c1c030b00838230700c1c00c4c0313030700c1c034300544530700c54530700c1c031114838230700c1c020e08232230700c1c008c88e0c0280c0c545240c0c545180c0c282140c0c2820c88834140c888241415514d0c03430050c024a08d0c03430090c00c888d0c034301000528888c54530a08c282215146222 (by decide +kernel)

def state247_70 : List Sig := [0xffffffffffffffff0000000000000000ffff0000ffff0000,input 6,input 7,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 5,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_70 : Impossible true (goalAt 247) 7 state247_70.toFinset :=
  node_ok cuts247 [] 0x3130034300d0c0c4c031300d0c014514c4c031514c4c031300c14521a08c4c031300868230b00c4c021208c2c030b0032300c8c0c2c030b00d0c024208c2c011d14c2c030b0047450c8c0c2c030b00323030700c4c005450c1c030700c2c020e08c1c03070031300c4c0c1c030700d0c015114c1c031514c1c030700c44520e08c1c030700838238300a03031514903031514622211c1c522214888554534300d0c014300928234300d0c024a08c545280c0c545280c0868231300868231300323030b00323030b0083823070083823070034140c888322209050928234300928234300a03031514a03031514c282 (by decide +kernel)

def state247_71 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 5,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_71 : Impossible true (goalAt 247) 7 state247_71.toFinset :=
  node_ok cuts247 [⟨state247_67,exclude247_67⟩] 0x3130034300d0c0c4c031300d0c00d0c0c4c031514c4c031300c14521a08c4c03130084c00d0c0c4c031300343030b00c4c021208c2c030b0032300c8c0c2c030b00d0c024208c2c011d14c2c030b00474530a08c2c030b0032300c8c0c2c030b00323030700c4c005450c1c030700c2c020e08c1c03070031300c4c0c1c030700d0c00c4c0c1c031514c1c030700c44520e08c1c03070083820c4c0c1c030700313038300322231514322231514341430a0a000030a08a030250509030240c0554534300d0c031514928234300d0c024300a03034300d0c021050a03031514c5450c888c54530a08c282215147030 (by decide +kernel)

def state247_72 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 7,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 5,input 0,input 1,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_72 : Impossible true (goalAt 247) 8 state247_72.toFinset :=
  node_ok cuts247 [⟨state247_35,exclude247_35⟩,⟨state247_25,exclude247_25⟩,⟨state247_66,exclude247_66⟩,⟨state247_68,exclude247_68⟩,⟨state247_69,exclude247_69⟩,⟨state247_70,exclude247_70⟩,⟨state247_71,exclude247_71⟩] 0x4005070301c0c0a03030a08c28280018c28230a08a0301c0c0703080014622218888322230a08c28280010c28230a08322218888603015050868221a08c28231300c4c015050c4c031300c28221a0884c00d050c4c031301000a0d0c034300d05034300d0c1000a31300c4c040028c4c031300d0c00d0c0d0c04002834300d0c0d0c031300c4c02505034300d0c0a03031300c4c025050c4c031300a0300d0c0343040028262209888322231300c4c040028c4c031300322209888243030a08323030a08703030b00c2c030a08c2c030b0070300c8c0323021a08c2c030b00c4c011d14c4c021a08474521208c4c030b00c2c040050c2c030b0034140c8c032308000432300c8c0341430b00c2c024a08c2c030b00d0c00c8c0d0c024a08323024208d0c030b00c2c040050474511d14a03030b00c2c080000c2c030b00a03011d1447450c888474511d15000730b00c2c00c888c2c030b01000711d14474511c1c838220e08c28230700c1c011c1cc1c030700c28220e08838240024c1c030700c4c005450c4c040024151405450c4c030700c1c011d14c1c030700c2c020e08c2c011d14838220e08c2c030700c1c040024c1c03070034140c4c031304002431300c4c0341430700c1c040024c1c030700d0c00c4c0d0c04002431300c4c0d0c030700c1c04002431300c4c0a03030700c1c040024c1c030700a0300c4c0313040024232208c88322230700c1c040024c1c030700322208c8823221c0c034141c0c0c28240050c2821c0c20003140c0c2820d050c28240011000438300a0300d050a03025051001425050a030400509030250503414240c032224004832224001434140d05032220d050322240015001209050703024a08928230a08d0c034300703034300d0c030a08928224300a03040018a03080008d0c034300a03034300d0c040051000614300322240018554540014d0c034300322234300d0c040015000640019000440010c545 (by decide +kernel)

def state247_73 : List Sig := [0xffffffffffff0000ffffffffffff0000,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 4,input 0,input 1,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_73 : Impossible true (goalAt 247) 7 state247_73.toFinset :=
  node_ok cuts247 [] 0x31514c28230a08854521a08c4c03130084c03130034300d0c0c4c031514c4c031300c14531300e0c00d0c0c4c030a08c2c030b00323030b00c4c021208c2c030b0032300c8c0c2c011d14c2c030b00474530b00e0c028208c2c020e08c1c030700838230700c4c005450c1c030700c2c020e08c1c03070031300c4c0c1c031514c1c030700c44530700e0c00c4c0c1c01c0c0c282180c0c2820d050c5450c888c54534300a28238300e0c028300e54538300e0c031514703030a08703030a08343031300343031300323030b00323030b00313030700313030700a030240c090302488834143151490303151460c0 (by decide +kernel)

def state247_74 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_74 : Impossible true (goalAt 247) 6 state247_74.toFinset :=
  node_ok cuts247 [] 0x31300d0c014514c4c031514c4c031300c14521a08c4c03130084c00d0c0c4c031300343030b00c4c021208c2c030b00d0c028208c2c011d14c2c030b00474530a08c2c030b0100190c8c0c2c030b00323030700c4c005450c1c030700c2c020e08c1c030700d0c015114c1c031514c1c030700c44520e08c1c03070083820c4c0c1c030700313015514d0c03430050c024a08d0c034300a0c0180c0d0c0343001545180c0c54531514503031514c28230a088545180c0c28230a08a030 (by decide +kernel)

def state247_75 : List Sig := [0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 6,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 7,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_75 : Impossible true (goalAt 247) 7 state247_75.toFinset :=
  node_ok cuts247 [⟨state247_74,exclude247_74⟩] 0x31300d0c014514c4c00d0c0c4c03130034300d050c4c031301000a21a08c4c031300868221a08c4c031300868230b00c4c021208c2c030b00d0c028208c2c011d14c2c030b00474511d14c2c030b0047450c8c0c2c030b0032300c888c2c030b01000b30700c4c005450c1c030700c2c020e08c1c030700d0c015114c1c00c4c0c1c030700313005450c1c030700151420e08c1c030700838220e08c1c030700838215514d0c03430070c015514d0c034300554528a08d0c034300b0c024a08d0c034300a282315146030240c20000180c05414180c05030140c0c282240c09222240c0a0300d05032220c8882414 (by decide +kernel)

def state247_76 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000,input 6,input 7,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_76 : Impossible true (goalAt 247) 7 state247_76.toFinset :=
  node_ok cuts247 [] 0xc4c00d0c0343031300c4c038300614531300c54531300c4c030514868231300c4c021300341431300c4c040054c2c031300848230b00c2c00c8c0323030b00c2c038300a08230b00474530b00c2c011d14c28230b00c2c00c8c0161430b00c2c005850c1c031300151430700c1c030b00838230700c1c00c4c0313030700c1c038300644530700c54530700c1c031114838230700c1c020e08151430700c1c005450d0c0240c0c545240c0c545140c0c282140c0c2820d05032220c888241419514e0c03830060c028a08e0c038300a0c00d050e0c038301000425050c54530a08c282215145414 (by decide +kernel)

def state247_77 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_77 : Impossible true (goalAt 247) 7 state247_77.toFinset :=
  node_ok cuts247 [⟨state247_74,exclude247_74⟩] 0x3130034300d0c0c4c031300e0c00d0c0c4c031514c4c031300c14521a08c4c03130084c00d0c0c4c031300343030b00c4c021208c2c030b0032300c8c0c2c030b00e0c028208c2c011d14c2c030b00474530a08c2c030b0032300c8c0c2c030b00323030700c4c005450c1c030700c2c020e08c1c03070031300c4c0c1c030700e0c00c4c0c1c031514c1c030700c44520e08c1c03070083820c4c0c1c030700313034300341431514322231514322230a0a000030a089030248889030280c0654538300e0c031514a28238300e0c028300903038300e0c040088903031514c5450d050c54530a08c282215147030 (by decide +kernel)

def state247_78 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 7,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,input 0,input 1,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_78 : Impossible true (goalAt 247) 8 state247_78.toFinset :=
  node_ok cuts247 [⟨state247_19,exclude247_19⟩,⟨state247_73,exclude247_73⟩,⟨state247_75,exclude247_75⟩,⟨state247_76,exclude247_76⟩,⟨state247_77,exclude247_77⟩] 0x4005070301c0c0903030a08c28280010c28230a0890301c0c0703040050541415050341430a08c2828000cc28230a08341415050503015050868221a08c28231300c4c015050c4c031300c28221a0884c040054c4c03130032220d0c034304005434300d0c0322231300c4c040054c4c031300e0c00d0c0e0c04005434300d0c0e0c031300c4c04005434300d0c0903031300c4c040054c4c03130090300d0c034300d05100140d051001531300c4c00d050c4c031301001540055001530a08323030a08703030b00c2c030a08c2c030b0070300c8c0323021a08c2c030b00c4c011d14c4c021a08474521208c4c030b00c2c00c888c2c030b01000b0c8c032300c88832300c8c1000b30b00c2c028a08c2c030b00e0c00c8c0e0c028a08323028208e0c030b00c2c028888474511d14903030b00c2c028888c2c030b00903011d14474540050474511d14341430b00c2c080000c2c030b00341411d14474511c1c838220e08c28230700c1c011c1cc1c030700c28220e08838240054c1c030700c4c005450c4c04005c151405450c4c030700c1c011d14c1c030700c2c020e08c2c011d14838220e08c2c030700c1c04005cc1c03070032220c4c031304005c31300c4c0322230700c1c04005cc1c030700e0c00c4c0e0c04005c31300c4c0e0c030700c1c04005c31300c4c0903030700c1c04005cc1c03070090300c4c031304005c151405450341430700c1c04005cc1c03070034140545015141c0c032221c0c0c28240084c2821c0c20002180c0c2820c888c2824001500053430090300c8889030288890014248889030400509030288883222280c034144005034144001032220c88834140c888322240011001409050703028a08a28230a08e0c038300703038300e0c030a08a28228300903040018903080004e0c038300903038300e0c040051000618300341440018654540010e0c038300341438300e0c040011000640019000540014c545 (by decide +kernel)

def state247_79 : List Sig := [0xffffffffffffffffffffffffffffffff33333333333300003333333333330000,input 7,input 1,input 4,input 5,input 0,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_79 : Impossible true (goalAt 247) 7 state247_79.toFinset :=
  node_ok cuts247 [] 0x703030a08c2821c0c0622230a08c28218888868231300c4c021300c4c038300343031300c4c034300343031300343031300c4c00d0c0262231300c4c009888838230700c1c020e08c1c031300151430700c1c038300313030700c1c034300313030700c1c030b00838230700313030700c1c00c4c0232230700c1c008c88a28238300e0c028300b03038300e0c018300654538300e0c009c1c928234300d0c024300d0c038300322234300b03034300d0c014300554534300d0c00c888c28230b00c2c01c0c0c2c031300848230b00c2c038300a08230b00c2c034300908230b00474530b00c2c011d14474530b00c2c011d14c545 (by decide +kernel)

def state247_80 : List Sig := [0x3333333333330000333333333333000033333333333300003333333333330000,input 1,input 4,input 5,input 0,input 2,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_80 : Impossible true (goalAt 247) 8 state247_80.toFinset :=
  node_ok cuts247 [⟨state247_7,exclude247_7⟩,⟨state247_40,exclude247_40⟩,⟨state247_79,exclude247_79⟩] 0xc5451c0c0c5452c0c0c28230a08c54530a08c2822c0c0703021514c5450d0c0c54530504c4c031300c54531300c4c030504343030514541421a08868230a08c4c031300541431300c4c030a08868221300341431300c4c028a08343028a0834140d0c0343028a08c4c031300170731300c4c024a08343024a0817070d0c0343024a08c4c031300c5450c4c0c54531110c1c030700c54530700c1c031110313031114470720e08838230a08c1c030700470730700c1c030a08838220e09000f30700c1c031300151431301000e05450151431300c1c030700270730700c1c028a08313028a0827070c4c0313028a08c1c030700170730700c1c024a08313024a0817070c4c0313024a08c1c030700474530700c1c030b00838230b00474520e08838230b00c1c030700b0300d050b03031514a28228a08b03028a08a28231514341431514703028a08a28230a09000b30a08703040034503030a08a28228a08b0300c888b03031514928224a08b03024a08928231514322231514703024a08928230a09000730a08703040034603030a08928224a08341424a08928228a08322228a0834140c888322228a08928224a08a22211d14474531514c2c030b00a22230b00c2c031514474511d14c28240034c2821c0c0c2c030b00c28230b00c2c01c0c100071c0c0868230b00c2c031300474531300868211d14848231300c2c030b00a28230b00c2c00d051000738b00a2824002ca2820d050c2c030b00928230b00c2c04001d000734b0092824001c92824001cc2c030b00b03040018b03031516000131514b03080008b03031515000631514703040004703030a09000d30a08703040034703030a09000130a08343040008343031301000f3130034304003c343031301000231300313040000313030701000e3070031304003831303070100003070034144000ce0c028a09000438300341440010341428a09000328a0900074000cd0c024a09000534301000b40015000524a09000324a0a00004001c3230 (by decide +kernel)

def state247_81 : List Sig := [0x5555555555555555555555555555555555555555555500005555555555550000,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 7,input 4,input 5,input 1,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_81 : Impossible true (goalAt 247) 7 state247_81.toFinset :=
  node_ok cuts247 [] 0xc54530a08c28221514868231300c4c021300c4c00d0c0343031300c4c00d0c0343031300c54531300c4c030514c4c00d0c0343031300c28230b00c2c00c8c0c2c031300848230b00c2c00c8c0323030b00c2c00c8c0323030b00464530b00c2c011914c2c00c8c0323030b00703030a08503030a08b03031514903031514e0c01c0c0c282180c0c2820d050322209050b03031514a03031514d0c01c0c0c2821c0c0c2822c0c0c5452c0c0c54520e08c1c030700838230700151431300c1c030700838230b00c1c03070031300c4c0c1c03070031300c4c0c1c031114c1c030700c5453070031300c4c0c1c0 (by decide +kernel)

def state247_82 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0f0f0f0f0000,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 7,input 4,input 5,input 0,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_82 : Impossible true (goalAt 247) 7 state247_82.toFinset :=
  node_ok cuts247 [] 0xc54530a08c28221514c28230b00c2c00c8c0c2c00c8c0323030b00c2c00c8c0323030b00474530b00c2c011d14c2c00c8c0323030b00838230700c1c020e08c1c030b00838230700c1c00c4c0313030700c1c00c4c0313030700c54530700c1c031114c1c00c4c0313030700703030a08503030a08b03031514903031514e0c01c0c0c282180c0c2820d050322209050b03031514a03031514d0c01c0c0c2821c0c0c2822c0c0c5452c0c0c54521300c4c031300868230b00848230b00c4c030700151430700c4c03130034300d0c0c4c03130034300d0c0c4c030514c4c031300c5453130034300d0c0c4c0 (by decide +kernel)

def state247_83 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffff0000ffffffffffff0000,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 7,input 4,input 5,input 0,input 1,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_83 : Impossible true (goalAt 247) 8 state247_83.toFinset :=
  node_ok cuts247 [⟨state247_48,exclude247_48⟩,⟨state247_81,exclude247_81⟩,⟨state247_82,exclude247_82⟩] 0x1c0c0c28230a08703011c1cc28230a08470721a08c4c03130084c03130034300d0c0c4c03130034300d0c0c4c00d0c0c4c03130034303130034300d0c0c4c080008c4c031301001530a08c2c030b00323030b00c4c021208c2c030b0032300c8c0c2c030b0032300c8c0c2c011d14c2c030b00474530b0032300c8c0c2c011d14c2c030b00474520e08c1c030700838230700c4c005450c1c030700c2c020e08c1c03070031300c4c0c1c03070031300c4c0c1c00c4c0c1c03070031303070031300c4c0c1c080004c1c03070100171c0c0c282140c0c2822c0c09414240c090303830100121c0c0c282180c0c2820d050322209050b03028888a030280c0d0c040050c5451c0c0c2821c0c0c2822c0c20000400510006 (by decide +kernel)

def state247_84 : List Sig := [0xffffffffffff0000ffffffffffff0000,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 7,input 4,input 5,input 0,input 1,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_84 : Impossible true (goalAt 247) 8 state247_84.toFinset :=
  node_ok cuts247 [⟨state247_48,exclude247_48⟩,⟨state247_66,exclude247_66⟩,⟨state247_73,exclude247_73⟩] 0x31514c28230a08854521a08c4c03130084c03130034300d0c0c4c03130034300d0c0c4c031514c4c031300c1453130034300d0c0c4c030a08c2c030b00323030b00c4c021208c2c030b0032300c8c0c2c030b0032300c8c0c2c011d14c2c030b00474530b0032300c8c0c2c020e08c1c030700838230700c4c005450c1c030700c2c020e08c1c03070031300c4c0c1c03070031300c4c0c1c031514c1c030700c4453070031300c4c0c1c01c0c0c282140c0c2820d050c54580008c54538300703030a08603030a0834140c88824140c888c54580004c54534300703030a08703030a09001480000c5451c0c0c2821c0c0c2820d0c0c4c00d0c0c4c00c8c0c2c00c8c0c2c00c4c0c1c00c4c0c1c00d05100040d05100050c88900050c88900042c0c10006 (by decide +kernel)

def state247_85 : List Sig := [0xffffffffffffcccc0000000000000000ffffffffffffcccc,input 1,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,input 5,input 0,input 2,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_85 : Impossible true (goalAt 247) 7 state247_85.toFinset :=
  node_ok cuts247 [] 0x854531300c4c020514c4c00d0c0343031300c4c00d0c0343031300c4c00d0c0343031300854530700c1c021114c1c031300151430700c1c00c4c0313030700c1c00c4c0313030700c1c00c4c0313030700c1c030b00838230700b03021514903021514e0c02c0c08545280c085450d050322209050d0c02c0c085452c0c0854511d14c2c030b00474530b00c4c021a08c2c030b0032300c8c0c2c030b0032300c8c0c2c030b0032300c8c0c2c010a08c28230a08854521a08c4c021a08c4c020e08c1c020e08c1c030a0850301c0c0c28230a0860301c0c0c28230a0870301c0c0c2820c8c0c2c030a08c2c0 (by decide +kernel)

def state247_86 : List Sig := [0xffffffffffffccccffffffffffffccccffffffffffffccccffffffffffffcccc,input 1,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,input 5,input 0,input 2,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_86 : Impossible true (goalAt 247) 8 state247_86.toFinset :=
  node_ok cuts247 [⟨state247_7,exclude247_7⟩,⟨state247_85,exclude247_85⟩] 0x31514c28230a08854531514c4c031300c14521a08c4c03130084c03130034300d0c0c4c03130034300d0c0c4c03130034300d0c0c4c031300868221a08c4c031514c1c030700c44520e08c1c030700838230700c4c005450c1c03070031300c4c0c1c03070031300c4c0c1c03070031300c4c0c1c030700838220e08c1c030700838220e08c1c02c0c0c545240c0c5451c0c0c282140c0c28228a0900072c0c0c545280c0c5451c0c0c282180c0c2820d05032220905092824002cb03031514b03031514703030a08703030a0900030c8c0c54528088c54530a08703030a08323021a08c4c021a08c4c00585032300c8c016140c88832300c8c1000b8000032304001cc2c02c0c0c5452c0c0c54530a0a000130a09001e (by decide +kernel)

def state247_87 : List Sig := [0x3333333333330000333333333333000033333333333300003333333333330000,input 1,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,input 5,input 0,input 2,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_87 : Impossible true (goalAt 247) 8 state247_87.toFinset :=
  node_ok cuts247 [⟨state247_7,exclude247_7⟩,⟨state247_26,exclude247_26⟩] 0x31514c28230a08854531514c4c031300c14521a08c4c03130084c03130034300d0c0c4c03130034300d0c0c4c03130034300d0c0c4c031514c1c030700c44520e08c1c030700838230700c4c005450c1c03070031300c4c0c1c03070031300c4c0c1c03070031300c4c0c1c030700c2c020e08c1c02c0c0c545240c0c5451c0c0c282140c0c28228a08b03031514a03031514703030a08603030a0834140c888241424a08b03031514b03031514703030a08703030a08474530b00c2c011d14c28230b00c2c01c0c0c2c031300848230b00c2c00d052000130b00c2c04002c322230b01000780000c2c02c0c0c5452c0c0c5451c0c0c2821c0c0c2820d0c0c4c00d0c0c4c00c4c0c1c00c4c0c1c00d05100040d05100054001032224001432224000c3230 (by decide +kernel)

def state247_88 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,input 5,input 0,input 1,input 2,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_88 : Impossible true (goalAt 247) 9 state247_88.toFinset :=
  node_ok cuts247 [⟨state247_9,exclude247_9⟩,⟨state247_27,exclude247_27⟩,⟨state247_41,exclude247_41⟩,⟨state247_59,exclude247_59⟩,⟨state247_65,exclude247_65⟩,⟨state247_72,exclude247_72⟩,⟨state247_78,exclude247_78⟩,⟨state247_80,exclude247_80⟩,⟨state247_83,exclude247_83⟩,⟨state247_84,exclude247_84⟩,⟨state247_86,exclude247_86⟩,⟨state247_87,exclude247_87⟩] 0x40050c5451c0c0c54540078b03030a08c2824007cc54530a08c28240078b0301c0c0854540054c5450d0c0c54540054c14131300c4c040054c54531300c4c040054c1410d0c0c14540054541421a08868240054c28231300c4c040054541431300c4c040054c28221a0884c040014341431300c4c04001500150d0c034304001434140d0c0343040015000531300c4c040011000431300c4c04001032220d0c034304001100150d0c0343040010322231300c4c040055001531300c4c04005500020d0c034304005500150d0c0343040055000231300c4c040050a22211d1447454001cc54530b00c2c080008a22230b00c2c04001cc54511d14474540078c2820c8c0c2824001c703030b00c2c040034c28230b00c2c04001c70300c8c0323040054868230b00c2c040054c4c011d14c4c040054868211d14848240054c4c030b00c2c040015000530b00c2c04001434140c8c032304001600010c8c0323040014341430b00c2c040010322230b00c2c040011000b0c8c032304001032220c8c0323040011000430b00c2c08002e000730b00c2c04001d00030c8c032308002a00000c8c032304001d000330b00c2c04005cc5450c4c0c5454005cc44430700c1c04005cc54530700c1c04005cc4440c4c0c4454005c470720e0883824005cc28230700c1c04005c470730700c1c04005cc28220e08838240055001530700c1c040054c4c005450c4c040055001705450151440054c4c030700c1c04005c474530700c1c04005cc2c020e08c2c04005c474520e0883824005cc2c030700c1c040015000530700c1c04001434140c4c031304001500170c4c0313040014341430700c1c040011000430700c1c04001032220c4c031304001100170c4c0313040010322230700c1c04005d001730700c1c04005d00000c4c031304005d00170c4c031304005d000030700c1c040014b0300d050b03040014c54540014c54540014b03080018903040014c5450d050c5454001470300d050703040014c28240014c2824001470304007c503040014c2820d050c28240015000540010e0c040010b0300c888b03040010c54540010c54540010b03080014a03040010c5450c888c5454001070300c888703040010c28240010c2824001070304007c603040010c2820c888c2824001434144001434144001500040c888322240015000540014241440015000540014d0c040050b03040018b03080024c54580010c54580020b0308000cb03040050c54540018c5454007870304000470304007cc2824007cc2824007c70304007c703040078c28240004c282 (by decide +kernel)

def state247_89 : List Sig := [0xffffffff33333333ffffffff33333333ffffffff33330000ffffffff33330000,input 5,input 1,input 4,input 7,input 0,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_89 : Impossible true (goalAt 247) 7 state247_89.toFinset :=
  node_ok cuts247 [] 0x703030a08c28210a08868231300c4c021300343031300c4c00d0c0c4c034300343031300c4c038300343031300868231300c4c021a08838230700c1c020e08c1c031300151430700313030700c1c00c4c0c1c034300313030700c1c020e08838230700c1c038300313030700838230700c1c020e08928234300d0c024300b03034300d0c014300d0c038300322234300928234300d0c024a08c28211d14c2820c8c0868231300868231300474531d14a02211d14928234300928234300e2c03830032303830047450c8c0c2c030b00a08038300e0c028300b03038300e0c018300a2821c0c0c2821c0c0c28231514c5452c0c08707 (by decide +kernel)

def state247_90 : List Sig := [0x3333333333333333333333333333333333330000333300003333000033330000,input 1,input 4,input 7,input 0,input 2,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_90 : Impossible true (goalAt 247) 8 state247_90.toFinset :=
  node_ok cuts247 [⟨state247_28,exclude247_28⟩,⟨state247_89,exclude247_89⟩] 0x100121c0c070302c0c0c28230a09000d30a08c2822c0c0703010a08703028a08a28230a08e0c038300703038300e0c030a08a28228300b03019514654525050e0c038300b03038300e0c025050654519514541421a08868230a08c4c031300541431300c4c030a08868221300654531300c4c03830034303830065450d0c0614538300c4c03130094140d0c034302c0c0c4c031300941431300c4c02c0c034300d0c0170731300c4c03430034303430017070d0c0343034300c4c031300470720e08838230a08c1c030700470730700c1c030a08838220e08654530700c1c03830031303830065450c4c0644538300c1c030701000f30700c1c031300151431301000e05450151431300c1c03070087070c4c031302c0c0c1c030700870730700c1c02c0c031300c4c0170730700c1c03430031303430017070c4c0313034300c1c030700474530700c1c011910838220e08474520e08838211910c1c030700703024a08928230a08d0c034300703034300d0c030a08928224300341434300d0c03830032223830034140c888322238300d0c034300b0300c888b03028888d0c034300b03034300d0c028888322214300c28240034c2821c0c0474511d14c28211d14c2821c0c100071c0c0a28211d14a28238301000738300a28280000a28238300474538300868210d04868231300474531300868211d14868231300434131300a22211d1447452c0c1000731d14a22240048a2222c0c0474511d14928211d1492823430100073430092824001c928234300474534300703040004703030a09001230a08703040034703030a09000130a08e0c040014e0c028a09001228a08e0c080004e0c028a09000528a08c4c040008c4c021a09001221a08c4c04003cc4c021a09000221a08c1c040000c1c020e09001220e08c1c040038c1c020e09000020e08b0304000cc54528889000431514b03040010b03028889000328888d0c04000cd0c024a09000624a08d0c040018d0c024a09000324a0900124001cc2c0 (by decide +kernel)

def state247_91 : List Sig := [0xccccccccffffffffccccccccffffffffccccccccffffccccccccccccffffcccc,input 1,input 5,input 4,input 7,input 0,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_91 : Impossible true (goalAt 247) 7 state247_91.toFinset :=
  node_ok cuts247 [] 0x703030a08c28210a08868231300c4c021300343031300c4c00d0c0c4c034300343031300c4c028a08614531300838230700c1c020e08c1c031300151430700313030700c1c00c4c0c1c034300313030700c1c028a08644530700c1c030b00838230700313030700c1c00c4c0928234300d0c024300b03034300d0c014300d0c028a08322234300a28230a08654528a08654528a08a28219514c28230b00c2c01c0c0c2c031300848230b00a22230b00c2c010b00c2c034300908230b00c2c038b00a28230b00474530a08703030a08703031300343031300343031514c54528888b03034300554534301000528a08654538300e0c0 (by decide +kernel)

def state247_92 : List Sig := [0xffffffffffffffff00000000ffffffffffffffffffffffff00000000ffff0000,input 6,input 5,input 4,input 7,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_92 : Impossible true (goalAt 247) 7 state247_92.toFinset :=
  node_ok cuts247 [] 0xc54531300c4c030514c4c034300514531300c4c038300614531300868231300c4c021300343031300c4c00d0c0c2c031300848230b00474530b00c2c011d14c2c034300908230b00c2c038300323030b00c28230b00c2c00c8c0323030b00c2c00c8c0c1c031300151430700c1c030b00838230700c54530700c1c031114c1c034300544530700c1c038300644530700838230700c1c020e08313030700c1c00c4c0554534300d0c014300d0c038300322234300928234300d0c024300322234300d0c00c888654538300e0c018300e28238300e0c030a08270738300e0c028a08c54530a08c28221514703031514b03031514b030 (by decide +kernel)

def state247_93 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,0xffffffff00000000ffffffff00000000ffff000000000000ffff0000,input 5,input 4,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_93 : Impossible true (goalAt 247) 7 state247_93.toFinset :=
  node_ok cuts247 [] 0x31300d0c00d0c0c4c031300614118514c4c021a08c4c03130084c00d0c0c4c031300343030b00c4c021208c2c030b00d0c024208c2c030b0065450c8c0c2c030a08c2c030b0032300c8c0c2c030b00323030700c4c005450c1c030700c2c020e08c1c030700d0c00c4c0c1c030700644419114c1c020e08c1c03070083820c4c0c1c03070031303430065450c888d0c024a08d0c03430090c02c0c0d0c034300a03009c1cc28219514c2822c0c0654519514941431300c54531300c14530b00474530b00474530700c54530700c44534300554534300c54538300c28231514c28221514941431514c5452c0c07030 (by decide +kernel)

def state247_94 : List Sig := [0xffffffff00000000ffffffff00000000ffff000000000000ffff0000,input 5,input 4,input 7,input 0,input 1,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_94 : Impossible true (goalAt 247) 8 state247_94.toFinset :=
  node_ok cuts247 [⟨state247_91,exclude247_91⟩,⟨state247_92,exclude247_92⟩,⟨state247_93,exclude247_93⟩] 0x100121c0c070302c0c0c28230a0a000230a08c2822c0c070301c0c0541421a08868230a08c4c031300541431300c4c030a0886822130094140d0c034302c0c0c4c031300941431300c4c02c0c034300d0c1001231300c4c03430034303430100140d0c0343034300c4c031300654531300c4c01850434301850465450d0c0614518504c4c031300c2820c8c0c2821c0c0c2c030b00c28230b00c2c01c0c032300c8c0868230b00c2c031300474531300868211d14848231300c2c030b00a22211d1447452c0c0c2c030b00a22230b00c2c02c0c0474511d14928230b00c2c03430032303430092820c8c0908234300c2c030b00270730b00c2c01951432301951427070c8c0323019514c2c030b00470720e08838230a08c1c030700470730700c1c030a08838220e09001430700c1c031300151431301002405450151431300c1c030700474530700c1c030b00838230b00474520e08838230b00c1c03070100120c4c031302c0c0c1c030701002430700c1c02c0c031300c4c1001230700c1c03430031303430100240c4c0313034300c1c030700654530700c1c01911031301911065450c4c0644519110c1c030700703024a08928230a08d0c034300703034300d0c030a08928224300b0300c888b03028888d0c034300b03034300d0c028888322214301001234300d0c01951432221951500120c888322219514d0c034300703009c1c703030a08654530a08703019514654530a08270730a08b03019514654525051001239514b03040048b03025050654519514c28240004c2821c0c100121c0c0c28280004c2821c0c100011c0c0c4c040008c4c00d0c100120d0c0c4c040050c4c00d0c100020d0c0c2c04000cc2c011d15001211d14c2c080000c2c011d15000311d14c1c040000c1c00c4c100120c4c0c1c040090c1c00c4c100000c4c0941440018c5452c0c100043151494144001094142c0c100062c0c0d0c040014d0c00c889000615514d0c040018d0c00c88900050c889001240050e0c0 (by decide +kernel)

def state247_95 : List Sig := [0xffffffffffffffffffffffffffffffffffffccccffffccccffffccccffffcccc,input 1,0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 4,input 7,input 0,input 2,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_95 : Impossible true (goalAt 247) 8 state247_95.toFinset :=
  node_ok cuts247 [] 0x1c0c0c28230a08703018888c28230a08622218080c28230a08602028a08e0c038300a0c019514e0c038300654519514e0c038300654519514e0c038300654521a08c4c03130084c031300e0c018514c4c00d0c0c4c031300343031300d0c00d0c0c4c009888c4c031300262209080c4c031300242020e08c1c030700838230700e0c019114c1c030700c4c005450c1c00c4c0c1c030700313030700d0c00c4c0c1c008c88c1c030700232230700c2c020e08c1c008480c1c030700212028889000724a08d0c03430090c034300e0c00d050d0c02c0c0d0c01430032224004d000330a08c2c030b00323030b00e0c028208c2c030b00c4c021208c2c00c8c0c2c030b00323030b00d0c024208c2c040048c2c04001c4745 (by decide +kernel)

def state247_96 : List Sig := [0x5555555555555555555555555555555555555555555500005555555555550000,input 5,0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 4,input 7,input 1,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_96 : Impossible true (goalAt 247) 7 state247_96.toFinset :=
  node_ok cuts247 [] 0x703030a08c2821c0c0622230a08c28218888868231300c4c021300343031300c4c00d0c0c4c034300343031300262231300c4c009888c4c038300614531300c28230b00c2c00c8c0c2c031300848230b00464530b00c2c011914c2c034300908230b00464530b00c2c011914c2c038300a08230b00c54524a08d0c03430090c02c0c0d0c014300554534300e0c00d050d0c028a08e0c038300a0c019514e0c038300654519514e0c038300654520e08c1c030700838230700151431300c1c030700838230b00c1c00c4c0c1c030700313030700313034300c1c008c88c1c030700232230700644538300c1c0 (by decide +kernel)

def state247_97 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0f0f0f0f0000,input 5,0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 4,input 7,input 0,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_97 : Impossible true (goalAt 247) 7 state247_97.toFinset :=
  node_ok cuts247 [] 0x703030a08c2821c0c0622230a08c28218888c28230b00c2c00c8c0474530b00c2c011d14c2c034300908230b00474530b00c2c011d14c2c038300a08230b00838230700c1c020e08c1c030b00838230700313030700c1c00c4c0c1c034300313030700232230700c1c008c88c1c038300644530700c54524a08d0c03430090c02c0c0d0c014300554534300e0c00d050d0c028a08e0c038300a0c019514e0c038300654519514e0c038300654521300c4c031300868230b00848230b00c4c030700151430700c4c00d0c0c4c031300343031300343034300c4c009888c4c031300262231300614538300c4c0 (by decide +kernel)

def state247_98 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffff0000ffffffffffff0000,input 5,0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 4,input 7,input 0,input 1,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_98 : Impossible true (goalAt 247) 8 state247_98.toFinset :=
  node_ok cuts247 [⟨state247_96,exclude247_96⟩,⟨state247_97,exclude247_97⟩] 0x1c0c0c28230a08703018888c28230a08622211c1cc28230a08470721a08c4c03130084c00d0c0c4c031300343031300d0c00d0c0c4c009888c4c031300262231300e0c00d0c0c4c080004c4c031301000a30a08c2c030b00323030b00c4c021208c2c011d14c2c030b00474530b00d0c024208c2c011d14c2c030b00474530b00e0c028208c2c011d14c2c030b00474520e08c1c030700838230700c4c005450c1c030700c2c020e08c1c00c4c0c1c030700313030700d0c00c4c0c1c008c88c1c030700232230700e0c00c4c0c1c080000c1c030701001b28889002024a08d0c03430090c02c0c0d0c014300322234300e0c00d050d0c040051000528a08e0c038300a0c02c0c0e0c038300903040048e0c0400486545 (by decide +kernel)

def state247_99 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 4,input 7,input 0,input 1,input 2,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_99 : Impossible true (goalAt 247) 9 state247_99.toFinset :=
  node_ok cuts247 [⟨state247_72,exclude247_72⟩,⟨state247_11,exclude247_11⟩,⟨state247_36,exclude247_36⟩,⟨state247_29,exclude247_29⟩,⟨state247_59,exclude247_59⟩,⟨state247_90,exclude247_90⟩,⟨state247_94,exclude247_94⟩,⟨state247_95,exclude247_95⟩,⟨state247_98,exclude247_98⟩] 0x4001900061c0c0703040018b03030a08c28240019002330a08c28240018b0301c0c0703040049002318888622240035000130a08c2824008d002330a08c28240049000118888622240034703028a08a28240050c28238300e0c04008c703038300e0c040034c28228a08a0c040018b03019514654540018941438300e0c040018b03038300e0c04001894141951465454004a000619514654540051000538300e0c080022000438300e0c040049000519514654540028541421a08868240028c28231300c4c040028541431300c4c040028c28221a0884c040028654531300c4c040028e0c00d0c0e0c04002865450d0c0614540028e0c031300c4c04001894140d0c0343040018b03031300c4c040018941431300c4c040018b0300d0c0343040011000431300c4c040010d0c00d0c0d0c040011000a0d0c0343040010d0c031300c4c040029000a09888262240029000231300c4c040029000a31300c4c040029000209888262240034c2820c8c0c2824001c703030b00c2c040034c28230b00c2c04001c70300c8c0323040050a28230b00c2c04001ce0c00c8c0e0c08000ca2820c8c0a0824001ce0c030b00c2c040028868230b00c2c040028c4c011d14c4c040028868211d14848240028c4c030b00c2c040019000611d14474540018b03030b00c2c04001a000230b00c2c040018b03011d14474540010928230b00c2c040010d0c00c8c0d0c04001092820c8c0908240010d0c030b00c2c04004a000511d1447454001d000330b00c2c08001e000130b00c2c04001d000311d1447454006c470720e0883824006cc28230700c1c04006c470730700c1c04006cc28220e0883824006c654530700c1c04006ce0c00c4c0e0c04006c65450c4c064454006ce0c030700c1c04006d001b30700c1c04006cc4c005450c4c04006d001b0545015144006cc4c030700c1c04006c474530700c1c04006cc2c020e08c2c04006c474520e0883824006cc2c030700c1c04001900060c4c0313040018b03030700c1c040019001b30700c1c040018b0300c4c0313040011000430700c1c040010d0c00c4c0d0c040011001b0c4c0313040010d0c030700c1c04006d001b08c8823224006d000030700c1c04006d001b30700c1c04006d000008c88232240019000640010c54540010703024a08928240010c28234300d0c040010703034300d0c040010c28224a0890c040010341434300d0c040010e0c040010e0c040010341480000341440010e0c034300d0c040018b03040018b03040019000434300d0c04001900064001850c0400190006400185545 (by decide +kernel)

def state247_100 : List Sig := [0x3333333333333333333300003333000033333333333333333333000033330000,input 4,input 6,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f00000000,input 5,input 7,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_100 : Impossible true (goalAt 247) 6 state247_100.toFinset :=
  node_ok cuts247 [] 0x31514c1c030700c44530700e0c019114c1c020e08c1c030700838230700d0c014114c1c019514e0c03830060c028208e0c038300a08230700151430700c4c030514c4c031300c54531300614538300c4c021208c4c031300848231300514534300c4c030b00c4c030b00848231514c28230a08703014514d0c034300514534300e0c00c888d0c024a08d0c03430090c030700838230700c2c011d14c2c030b00474530b00a08238300c2c00c8c0c2c030b00c28230b00908234300c2c0 (by decide +kernel)

def state247_101 : List Sig := [0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 4,input 6,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f00000000,input 5,input 7,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_101 : Impossible true (goalAt 247) 7 state247_101.toFinset :=
  node_ok cuts247 [⟨state247_100,exclude247_100⟩] 0x474530b00c2c011d14c2c038300a08230b00323030b00c2c00c8c0c2c034300323030b02000030b00c2c0400a0c1c030b00838230700c54530700c1c031114c1c038300644530700838230700c1c020e08c1c034300504530700838230700c1c020e08654538300e0c018300a28238300e0c028a08a28238300e0c028a08c2c021208c2c031300c1c005450c1c031300c14531300c4c031514c4c018514e0c031300868231300c4c021a08c4c014514d0c031300868231300c4c021a08c5452c0c0c5451c0c0c28214514d0c034300514534300e0c00d050d0c01c0c0d0c024300928231514a22231514a222 (by decide +kernel)

def state247_102 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f00000000,input 5,input 7,input 0,input 1,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_102 : Impossible true (goalAt 247) 8 state247_102.toFinset :=
  node_ok cuts247 [⟨state247_13,exclude247_13⟩,⟨state247_101,exclude247_101⟩] 0x40070c5451c0c0c54540098b03030a08c28240050c54530a08c28240070b0301c0c0854540098703024a089282400a4c28234300d0c080004703034300d0c040098c28224a0890c040070b03014514514540050c54534300d0c040050b03034300d0c040070c54514514514540054341434300d0c040054e0c00c888e0c04005434140c888322240054e0c034300d0c040098c2820c8c0c282400a0703030b00c2c040044c28230b00c2c04009870300c8c03230400a4928230b00c2c0400a0d0c00c8c0d0c08000092820c8c09082400a0d0c030b00c2c040070a22211d14474540050c54530b00c2c040050a22230b00c2c040070c54511d14474540054a28230b00c2c040054e0c00c8c0e0c040054a2820c8c0a08240054e0c030b00c2c040098430720e0883824009cc28230700c1c040060430730700c1c040098c28220e08838240060514530700c1c04009cd0c00c4c0d0c04006051450c4c050454009cd0c030700c1c0400a0474530700c1c04009cc2c020e08c2c040060474520e0883824009cc2c030700c1c040070c5450c4c0c54540050c44430700c1c040050c54530700c1c040070c4440c4c0c44540054654530700c1c040054e0c00c4c0e0c04005465450c4c0644540054e0c030700c1c040054703028a08a28240054c28238300e0c040054703038300e0c040054c28228a08a0c040054b03019514654540054c54538300e0c040054b03038300e0c040054c5451951460c040098c28221a0884c040050501431300c4c040050c28231300c4c040098501421a08868240050d0c031300c4c04005051450d0c0514540050d0c00d0c0d0c040050514531300c4c040050c2c031300c2c040050474521a08848240050c2c021a08c2c040050474531300c4c040050c1c031300c1c040050151440050151440050c1c040060c1c040050151431300c4c040054b0300d0c0c14540054c54531300c4c040054b03031300c4c040054c5450d0c0c54540054e0c031300c4c04005465450d0c0614540054e0c00d0c0e0c040054654531300c4c0 (by decide +kernel)

def state247_103 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,input 7,input 0,input 1,input 2,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_103 : Impossible true (goalAt 247) 9 state247_103.toFinset :=
  node_ok cuts247 [⟨state247_20,exclude247_20⟩,⟨state247_14,exclude247_14⟩,⟨state247_59,exclude247_59⟩,⟨state247_78,exclude247_78⟩,⟨state247_102,exclude247_102⟩] 0x4001900061c0c0703040018b03030a08c28240019002530a08c28240018b0301c0c0703040051001415050541440079000130a08c28240051002530a08c28240079000115050541440078703024a08928240094c28234300d0c040094703034300d0c040078c28224a0890c040018b03015514554540018a22234300d0c040018b03034300d0c040018a22215514554540015000534300d0c040014e0c00c888e0c04001600030c888322240014e0c034300d0c040051001415514554540051000434300d0c040052000234300d0c040051000415514554540054541421a08868240054c28231300c4c040054541431300c4c040054c28221a0884c040054554531300c4c040054d0c00d0c0d0c04005455450d0c0514540054d0c031300c4c04001900060d0c0343040018b03031300c4c040019001531300c4c040018b0300d0c0343040015000531300c4c040014e0c00d0c0e0c04001500150d0c0343040014e0c031300c4c040055001540052000440055000231300c4c040055001531300c4c040055000240055000240078c2820c8c0c2824002c703030b00c2c040064c28230b00c2c04007870300c8c0323040084928230b00c2c04002cd0c00c8c0d0c08000492820c8c090824002cd0c030b00c2c040054868230b00c2c040054c4c011d14c4c040054868211d14848240054c4c030b00c2c040018a22211d14474540018b03030b00c2c040018a22230b00c2c040018b03011d14474540014a28230b00c2c040014e0c00c8c0e0c040014a2820c8c0a08240014e0c030b00c2c040051001411d1447454002d000330b00c2c040052000030b00c2c04002d000311d1447454006c470720e0883824006cc28230700c1c04006c470730700c1c04006cc28220e0883824006c554530700c1c04006cd0c00c4c0d0c04006c55450c4c054454006cd0c030700c1c040055001530700c1c040054c4c005450c4c040055001b05450151440054c4c030700c1c04006c474530700c1c04006cc2c020e08c2c04006c474520e0883824006cc2c030700c1c04001900060c4c0313040018b03030700c1c040019001b30700c1c040018b0300c4c0313040015000530700c1c040014e0c00c4c0e0c040015001b0c4c0313040014e0c030700c1c04006d001b0545015144006d000030700c1c04006d001b30700c1c04006d000005450151440019000640014c54540014703028a08a28240014c28238300e0c040014703038300e0c040014c28228a08a0c040018b03040018b03040019000538300e0c04001900064001860c0400190006400186545 (by decide +kernel)

def state247_104 : List Sig := roots 247
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_104 : Impossible true (goalAt 247) 10 state247_104.toFinset :=
  node_ok cuts247 [⟨state247_15,exclude247_15⟩,⟨state247_30,exclude247_30⟩,⟨state247_44,exclude247_44⟩,⟨state247_88,exclude247_88⟩,⟨state247_99,exclude247_99⟩,⟨state247_103,exclude247_103⟩] 0x40004c5451c0c0c54540004b03030a08c28240004c54530a08c28240004b0301c0c0854540018b03019514654540014c54538300e0c080014b03038300e0c040018c5451951460c040004703028a08a28240004c28238300e0c040004703038300e0c040004c28228a08a0c040018b03015514554540010c54534300d0c080010b03034300d0c040018c5451551450c040004703024a08928240004c28234300d0c040004703034300d0c040004c28224a0890c040014341434300d0c040010e0c00c888e0c08000c34140c888322240014e0c034300d0c040008c5450d0c0c54540008c14131300c4c040008c54531300c4c040008c1410d0c0c14540004541421a08868240004c28231300c4c040004541431300c4c040004c28221a0884c040008654531300c4c040008e0c00d0c0e0c04000865450d0c0614540008e0c031300c4c040008554531300c4c040008d0c00d0c0d0c04000855450d0c0514540008d0c031300c4c040018a22211d1447454000cc54530b00c2c080008a22230b00c2c04000cc54511d14474540004c2820c8c0c28240004703030b00c2c040004c28230b00c2c04000470300c8c0323040014a28230b00c2c04000ce0c00c8c0e0c080004a2820c8c0a0824000ce0c030b00c2c040010928230b00c2c04000cd0c00c8c0d0c08000092820c8c090824000cd0c030b00c2c040008868230b00c2c040008c4c011d14c4c040008868211d14848240008c4c030b00c2c040000c5450c4c0c54540000c44430700c1c040000c54530700c1c040000c4440c4c0c44540004470720e08838240004c28230700c1c040004470730700c1c040004c28220e08838240000654530700c1c040000e0c00c4c0e0c04000065450c4c0644540000e0c030700c1c040000554530700c1c040000d0c00c4c0d0c04000055450c4c0544540000d0c030700c1c040001000030700c1c040000c4c005450c4c040001000005450151440000c4c030700c1c040000474530700c1c040000c2c020e08c2c040000474520e08838240000c2c030700c1c0 (by decide +kernel)

theorem lower247 : Claim 247 11 :=
  fromSearch 16778564 (by decide +kernel) exclude247_104


open PEqualNP.CircuitLowerBounds

def graph : Sig := goalAt 255
theorem graph_proper : proper graph := by unfold proper; decide +kernel

def edgeList : List Nat := [0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7]
def target (x : Fin 8 → Bool) : Bool :=
  decide (∃ i < edgeList.length / 2,
    (List.ofFn x).getD (edgeList.getD (2*i) 0) false = true ∧
    (List.ofFn x).getD (edgeList.getD (2*i+1) 0) false = true)

def smallCircuit : Circuit := ⟨[⟨.or, [0, 2]⟩, ⟨.or, [5, 7]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [5, 10]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [0, 1]⟩, ⟨.and, [8, 9]⟩, ⟨.and, [11, 12]⟩, ⟨.and, [4, 13]⟩, ⟨.and, [1, 6]⟩, ⟨.or, [14, 15]⟩, ⟨.or, [18, 16]⟩, ⟨.or, [19, 17]⟩], 20⟩

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


def lowRow (i : Fin 8) : Row := Fin.ofNat 256 (1 <<< ([4, 4, 5, 6, 0, 0, 1, 0] : List Nat).getD i.val 0)
def highRow (i : Fin 8) : Row := Fin.ofNat 256 ((1 <<< i.val) ||| (1 <<< ([4, 4, 5, 6, 0, 0, 1, 0] : List Nat).getD i.val 0))

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

end PEqualNP.Outside.L_meta_28972_aux

open PEqualNP.Outside.L_meta_28972_aux in
theorem PEqualNP.Outside.L_meta_28972 : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true))  := by
  intro gates o fit _ correct
  exact replaceShort lowerGraph gates o fit correct

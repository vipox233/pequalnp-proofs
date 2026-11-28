import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_51578.Six
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

abbrev Cuts := List (Sig × Nat)

def budget (T : Sig) (total lower room : Nat) (cs : Cuts) (ws : List Sig) : Prop :=
  ∀ c ∈ cs, ∃ (f : Row → Row) (roots : List Sig) (p : Nat) (bank : List (Wire Row)),
    (∀ r, bit (f r) c.1 = true) ∧ p + c.2 + room ≤ total ∧
    Reach true (roots.map observe) p bank ∧ poolSupply true f bank ws ∧
    ¬Constant (restrictRows f (observe T)) ∧
    ∀ k next, Reach true (roots.map observe) k next →
      Available true next (restrictRows f (observe T)) → lower ≤ k

def advanceCuts (cs : Cuts) (a b z : Sig) : Cuts :=
  cs.map fun c => (c.1, c.2 + (if availableB true c.1 [a, b] z then 1 else 0))

def cutsOK (total lower : Nat) (cs : Cuts) (ws : List Sig) : Bool :=
  cs.all fun c => decide (lower + c.2 + ws.countP (isMaskedConstant c.1) ≤ total)

lemma child_mem {ws : List Sig} {a b w : Sig} {d : Nat} {ka kb : Bool}
    (ha : a ∈ ws) (hb : b ∈ ws) (hm : w ∈ childTwo ws a b d ka kb) :
    w = bin d a b ∨ w ∈ ws := by
  rcases List.mem_cons.mp hm with eq | tail
  · exact Or.inl eq
  · right
    rcases mem_kept tail with rfl | tail
    · exact ha
    · rcases mem_kept tail with rfl | tail
      · exact hb
      · exact List.mem_of_mem_erase (List.mem_of_mem_erase tail)

lemma child_nodup {ws : List Sig} (hn : ws.Nodup) {a b : Sig} {d : Nat} {ka kb : Bool}
    (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) (fresh : bin d a b ∉ ws) :
    (childTwo ws a b d ka kb).Nodup := by
  let rest := (ws.erase a).erase b
  have hrest : rest.Nodup := (hn.erase _).erase _
  have har : a ∉ rest := fun h => hn.not_mem_erase (List.mem_of_mem_erase h)
  have hbr : b ∉ rest := (hn.erase a).not_mem_erase
  have hark : a ∉ kept kb b rest := by cases kb <;> simp [kept, har, hne]
  apply List.nodup_cons.mpr
  refine ⟨?_, kept_nd ka a _ (kept_nd kb b _ hrest hbr) hark⟩
  intro hm
  rcases mem_kept hm with e | tail
  · exact fresh (e.symm ▸ ha)
  rcases mem_kept tail with e | hl
  · exact fresh (e.symm ▸ hb)
  · exact fresh (List.mem_of_mem_erase (List.mem_of_mem_erase hl))

lemma keep_membership {α : Type} {a x : α} {l : List α} {k : Bool} :
    x ∈ kept k a l ↔ (k = true ∧ x = a) ∨ x ∈ l := by
  cases k <;> simp [kept,eq_comm]

lemma child_swap (ws : List Sig) (hn : ws.Nodup) (a b : Sig)
    (d : Nat) (hd : allowed true d) (ka kb : Bool) :
    (childTwo ws a b d ka kb).toFinset =
      (childTwo ws b a (flipOp d) kb ka).toFinset := by
  ext x
  simp only [childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    keep_membership,(hn.erase _).mem_erase_iff,hn.mem_erase_iff,bin_flip hd a b]
  tauto

lemma budget_next {T total lower room cs ws} (h : budget T total lower (room+1) cs ws)
    {a b : Sig} {d : Nat} {ka kb : Bool}
    (ha : a ∈ ws) (hb : b ∈ ws) (hd : allowed true d) :
    budget T total lower room (advanceCuts cs a b (bin d a b)) (childTwo ws a b d ka kb) := by
  intro c hc
  obtain ⟨c₀, ch, rfl⟩ := List.mem_map.mp hc
  obtain ⟨f, roots, p, bank, dom, size, reach, avail, nonconst, bound⟩ := h c₀ ch
  let z := bin d a b
  by_cases old : availableB true c₀.1 [a, b] z = true
  · refine ⟨f, roots, p, bank, dom, ?_, reach, ?_, nonconst, bound⟩
    · change p + (c₀.2 + (if availableB true c₀.1 [a, b] z then 1 else 0)) + room ≤ total
      rw [if_pos old]
      omega
    · intro v hv
      rcases child_mem ha hb hv with rfl | raw
      · exact availableB_sound dom (fun u hu => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
          exact avail _ (hu.elim (· ▸ ha) (· ▸ hb))) old
      · exact avail _ raw
  · obtain ⟨op,x,y,e,hx,hy,_,_⟩ := comb_prime hd (avail _ ha) (avail _ hb)
    refine ⟨f, roots, p+1, _, dom, ?_, Reach.two op reach hx hy, ?_, nonconst, bound⟩
    · change p + 1 + (c₀.2 + (if availableB true c₀.1 [a, b] z then 1 else 0)) + room ≤ total
      rw [if_neg old]
      omega
    · intro v hv
      rcases child_mem ha hb hv with rfl | raw
      · rw [obs_bin,restrict_comb,e]
        exact Or.inl (by simp)
      · exact available_cons _ (avail _ raw)

lemma cutsOK_run {T total lower room cs ws k}
    (h : budget T total lower room cs ws) (hk : k ≤ room)
    (hn : ws.Nodup) (run : Live true T k ws.toFinset) :
    cutsOK total lower cs ws = true := by
  apply List.all_eq_true.mpr
  intro c hc
  obtain ⟨f, roots, p, bank, dom, size, reach, avail, nonconst, bound⟩ := h c hc
  have supplyP : supply true bank ((ws.map observe).map (restrictRows f)) := by
    intro v hv
    obtain ⟨_, hm, rfl⟩ := List.mem_map.mp hv
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm
    exact avail a ha
  have limit := projected_bound f (list_run run ws hn rfl) nonconst reach supplyP bound
  have count := count_constants dom ws
  exact decide_eq_true (by omega)

abbrev PairIndex := Fin 156

def leftRow (j : PairIndex) : Row := ⟨128+j.val, by have := j.isLt; omega⟩
def rightRow (j : PairIndex) : Row := ⟨284+j.val, by have := j.isLt; omega⟩

def separation (a : Sig) : BitVec 156 := ((a >>> 128) ^^^ (a >>> 284)).setWidth 156

lemma separation_bit (a : Sig) (j : PairIndex) :
    (separation a).getLsbD j.val = true ↔ bit (leftRow j) a ≠ bit (rightRow j) a := by
  have lo : j.val + 128 < 512 := by have := j.isLt; omega
  have hi : j.val + 284 < 512 := by have := j.isLt; omega
  simp only [separation,BitVec.getLsbD_setWidth,j.isLt,decide_true,Bool.true_and,
    BitVec.getLsbD_xor,BitVec.getLsbD_ushiftRight]
  change ((a.getLsbD (128+j.val)) ^^ (a.getLsbD (284+j.val))) = true ↔ _
  simp [leftRow,rightRow,bit]

def cover (ws : List Sig) : BitVec 156 :=
  ws.foldr (fun a z => separation a ||| z) 0

lemma cover_bit (j : PairIndex) (ws : List Sig) :
    (cover ws).getLsbD j.val = true ↔ ∃ a ∈ ws, bit (leftRow j) a ≠ bit (rightRow j) a := by
  induction ws with
  | nil => simp [cover]
  | cons a ws ih =>
    change (separation a ||| cover ws).getLsbD j.val = true ↔ _
    simp only [BitVec.getLsbD_or,Bool.or_eq_true,separation_bit,ih,List.mem_cons,exists_eq_or_imp]

def coverOK (T : Sig) (ws : List Sig) : Bool :=
  ((separation T) &&& cover ws) == separation T

lemma coverOK_run {T ws k} (run : Live true T k ws.toFinset) : coverOK T ws = true := by
  apply beq_iff_eq.mpr
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  let i : PairIndex := ⟨j,hj⟩
  change ((separation T) &&& cover ws).getLsbD i.val = (separation T).getLsbD i.val
  rw [BitVec.getLsbD_and]
  cases h : (separation T).getLsbD i.val
  · rfl
  · obtain ⟨a,ha,hd⟩ := live_row_difference run ((separation_bit T i).mp h)
    have hc := (cover_bit i ws).mpr ⟨a,List.mem_toFinset.mp ha,hd⟩
    simp [hc]

def flags : List (Bool × Bool) := [(false,false),(false,true),(true,false),(true,true)]

lemma mem_flags (a b : Bool) : (a,b) ∈ flags := by
  cases a <;> cases b <;> simp [flags]

def checkChildren (room : Nat) (ws : List Sig) (a b : Sig) (d : Nat)
    (check : List Sig → Bool) : Bool :=
  let z := bin d a b
  if z == zero || z == one || ws.contains z then true
  else flags.all fun (ka,kb) =>
    let child := childTwo ws a b d ka kb
    if child.length ≤ room+1 then check child else true

lemma checkChildren_at {room ws a b d check} (h : checkChildren room ws a b d check = true)
    {ka kb : Bool} (fresh : bin d a b ∉ ws) (properB : proper (bin d a b))
    (size : (childTwo ws a b d ka kb).length ≤ room+1) :
    check (childTwo ws a b d ka kb) = true := by
  have invalid : (bin d a b == zero || bin d a b == one || ws.contains (bin d a b)) = false := by
    simp [properB.1, properB.2, fresh]
  simp only [checkChildren, invalid, Bool.false_eq_true, ite_false] at h
  have each := List.all_eq_true.mp h (ka,kb) (mem_flags ka kb)
  simpa only [if_pos size] using each

def checkNode (T : Sig) (total lower room : Nat) (cs : Cuts) (ws : List Sig)
    (next : Cuts → List Sig → Bool) : Bool :=
  if !coverOK T ws || !cutsOK total lower cs ws then true
  else !ws.contains T && ws.all fun a => ws.all fun b =>
    if a.toNat < b.toNat then (List.range 4).all fun d =>
      checkChildren room ws a b d (next (advanceCuts cs a b (bin d a b)))
    else true

lemma rejectZero {T : Sig} {ws : List Sig} (h : !ws.contains T = true) :
    Impossible true T 0 ws.toFinset := by
  intro k hk run
  have eq : k = 0 := by omega
  subst k
  have ht : T ∈ ws := by
    apply List.mem_toFinset.mp
    rw [run.1]
    simp
  have con : ws.contains T = true := List.contains_iff_mem.mpr ht
  rw [con] at h
  exact Bool.noConfusion h

set_option maxHeartbeats 1000000 in
lemma checkNode_sound {T total lower room cs ws} {next : Cuts → List Sig → Bool}
    (hn : ws.Nodup) (hb : budget T total lower (room+1) cs ws)
    (next_sound : ∀ c w, w.Nodup → budget T total lower room c w →
      next c w = true → Impossible true T room w.toFinset)
    (hc : checkNode T total lower room cs ws next = true) :
    Impossible true T (room+1) ws.toFinset := by
  unfold checkNode at hc
  split at hc
  next h =>
    intro k hk run
    simp [cutsOK_run hb hk hn run, coverOK_run run] at h
  next h =>
    simp only [Bool.and_eq_true] at hc
    obtain ⟨noTarget, allMoves⟩ := hc
    have noGoal : T ∉ ws := by
      intro hm
      have con : ws.contains T = true := List.contains_iff_mem.mpr hm
      rw [con] at noTarget
      exact Bool.noConfusion noTarget
    apply enum_step hn noGoal
    intro a ha b hm d hd ka kb hab fresh pr size
    have oneSide (a b : Sig) (ha : a ∈ ws) (hm : b ∈ ws)
        (ordered : a.toNat < b.toNat) (d : Nat) (hd : allowed true d)
        (ka kb : Bool) (hab : a ≠ b) (fresh : bin d a b ∉ ws)
        (pr : proper (bin d a b)) (size : (childTwo ws a b d ka kb).length ≤ room+1) :
        Impossible true T room (childTwo ws a b d ka kb).toFinset := by
      have all := List.all_eq_true.mp (List.all_eq_true.mp allMoves a ha) b hm
      rw [if_pos ordered] at all
      have hlt : d < 4 := by rcases hd with h | ⟨_,h⟩ <;> omega
      have ok := List.all_eq_true.mp all d (List.mem_range.mpr hlt)
      have childCheck := checkChildren_at ok fresh pr size
      exact next_sound _ _ (child_nodup hn ha hm hab fresh) (budget_next hb ha hm hd) childCheck
    rcases lt_or_gt_of_ne (fun e => hab (BitVec.eq_of_toNat_eq e)) with ordered | ordered
    · exact oneSide a b ha hm ordered d hd ka kb hab fresh pr size
    · have e := bin_flip hd a b
      rw [child_swap ws hn a b d hd ka kb]
      have len : (childTwo ws b a (flipOp d) kb ka).length ≤ room+1 := by
        have nc1 := child_nodup hn ha hm hab fresh (ka:=ka) (kb:=kb)
        have nc2 := child_nodup hn hm ha hab.symm (e ▸ fresh) (ka:=kb) (kb:=ka)
        rw [←List.toFinset_card_of_nodup nc2, ←child_swap ws hn a b d hd ka kb,
          List.toFinset_card_of_nodup nc1]
        exact size
      exact oneSide b a hm ha ordered (flipOp d) (flip_flip hd).1 kb ka hab.symm
        (e ▸ fresh) (e ▸ pr) len

def reject (T : Sig) (total lower : Nat) : Nat → Cuts → List Sig → Bool
  | 0, _, ws => !ws.contains T
  | room+1, cs, ws => checkNode T total lower room cs ws (reject T total lower room)

lemma reject_sound {T total lower} :
    ∀ {room cs ws}, ws.Nodup → budget T total lower room cs ws →
      reject T total lower room cs ws = true → Impossible true T room ws.toFinset := by
  intro room
  induction room with
  | zero =>
    intro cs ws hn hb hc
    exact rejectZero hc
  | succ room ih =>
    intro cs ws hn hb hc
    exact checkNode_sound hn hb (fun _ _ => ih) hc

def rejectPrefix (T : Sig) (total lower : Nat) (finish : Cuts → List Sig → Bool) :
    Nat → Nat → Cuts → List Sig → Bool
  | 0, _, cs, ws => finish cs ws
  | _+1, 0, _, ws => !ws.contains T
  | depth+1, room+1, cs, ws =>
      checkNode T total lower room cs ws (rejectPrefix T total lower finish depth room)

lemma rejectPrefix_sound {T total lower} {finish : Cuts → List Sig → Bool} :
    ∀ {depth room : Nat}, (∀ c ws, ws.Nodup → budget T total lower room c ws →
       finish c ws = true → Impossible true T room ws.toFinset) →
    ∀ cs ws, ws.Nodup → budget T total lower (depth+room) cs ws →
       rejectPrefix T total lower finish depth (depth+room) cs ws = true →
        Impossible true T (depth+room) ws.toFinset := by
  intro depth
  induction depth with
  | zero =>
    intro room close cs ws nd hb ok
    simp only [Nat.zero_add, rejectPrefix] at hb ok ⊢
    exact close cs ws nd hb ok
  | succ depth ih =>
    intro room close cs ws nd hb ok
    have eq : depth+1+room=depth+room+1 := by omega
    rw [eq] at hb ok ⊢
    exact checkNode_sound nd hb (ih close) ok

def inputWords : List Sig :=
  [((((((0x8208208208208 * 0x10000000000000000 + 0x2082082082082082) * 0x10000000000000000 + 0x082082082fc0fc0f) * 0x10000000000000000 + 0xc0fc0fc0fc0fc0ff) * 0x10000000000000000 + 0xf03f03f03ffc0fff) * 0x10000000000000000 + 0xaaaaaaaaaaaaaaaa) * 0x10000000000000000 + 0xaaaaaaaaaaaaaaaa),
   ((((((0x10410410410410 * 0x10000000000000000 + 0x4104104104104104) * 0x10000000000000000 + 0x104104104fff000f) * 0x10000000000000000 + 0xff000fff000fff03) * 0x10000000000000000 + 0xffc003ffc0fff03f) * 0x10000000000000000 + 0xcccccccccccccccc) * 0x10000000000000000 + 0xcccccccccccccccc),
   ((((((0x20820820820820 * 0x10000000000000000 + 0x8208208208208208) * 0x10000000000000000 + 0x208208208ffffff0) * 0x10000000000000000 + 0x00000ffffff00003) * 0x10000000000000000 + 0xfffffc0000ffffc0) * 0x10000000000000000 + 0xf0f0f0f0f0f0f0f0) * 0x10000000000000000 + 0xf0f0f0f0f0f0f0f0),
   ((((((0x41041041041041 * 0x10000000000000000 + 0x0410410410410410) * 0x10000000000000000 + 0x410410410fffffff) * 0x10000000000000000 + 0xfffff00000000003) * 0x10000000000000000 + 0xffffffffff000000) * 0x10000000000000000 + 0xff00ff00ff00ff00) * 0x10000000000000000 + 0xff00ff00ff00ff00),
   ((((((0x82082082082082 * 0x10000000000000000 + 0x0820820820820820) * 0x10000000000000000 + 0x820820820fffffff) * 0x10000000000000000 + 0xfffffffffffffffc) * 0x10000000000000000 + 0x0000000000000000) * 0x10000000000000000 + 0xffff0000ffff0000) * 0x10000000000000000 + 0xffff0000ffff0000),
   (0xffffffff00000000 * 0x10000000000000000 + 0xffffffff00000000),
   (0xffffffffffffffff * 0x10000000000000000 + 0x0000000000000000)]

def threshold3 : Sig := ((((0xffffc0f * 0x10000000000000000 + 0xc0000ffffc0fc003) * 0x10000000000000000 + 0xffff03f000ffffff) * 0x10000000000000000 + 0xe8e8e8e8e8e8e8e8) * 0x10000000000000000 + 0xe8e8e8e8e8e8e8e8)
def threshold4 : Sig := ((((0xfffffff * 0x10000000000000000 + 0xfffc0ffffc0fc003) * 0x10000000000000000 + 0xffffffffffffffff) * 0x10000000000000000 + 0xfee8fee8fee8fee8) * 0x10000000000000000 + 0xfee8fee8fee8fee8)
def threshold5 : Sig := ((((0xfffffff * 0x10000000000000000 + 0xffffffffffffffff) * 0x10000000000000000 + 0xffffffffffffffff) * 0x10000000000000000 + 0xfffefee8fffefee8) * 0x10000000000000000 + 0xfffefee8fffefee8)
def threshold6 : Sig := ((((0xfffffff * 0x10000000000000000 + 0xffffffffffffffff) * 0x10000000000000000 + 0xffffffffffffffff) * 0x10000000000000000 + 0xfffffffefffefee8) * 0x10000000000000000 + 0xfffffffefffefee8)

def input (i : Nat) : Sig := inputWords.getD i zero

def roots (n : Nat) : List Sig := (List.range n).map input

lemma input_mem {n : Nat} (i : Fin n) : input i.val ∈ roots n :=
  List.mem_map.mpr ⟨i.val, List.mem_range.mpr i.isLt, rfl⟩

lemma input_index {n : Nat} {a : Sig} (ha : a ∈ roots n) :
    ∃ i : Fin n, input i.val = a := by
  obtain ⟨i, hi, he⟩ := List.mem_map.mp ha
  exact ⟨⟨i, List.mem_range.mp hi⟩, he⟩

def checkEssential (T : Sig) (xs : List Sig) (a : Sig) (r s : Row) : Bool :=
  (bit r T != bit s T) && xs.all (fun w => w == a || bit r w == bit s w)

lemma checkEssential_sound {T xs a r s}
    (h : checkEssential T xs a r s = true) : Essential T xs a := by
  simp only [checkEssential,Bool.and_eq_true,bne_iff_ne,List.all_eq_true,Bool.or_eq_true,beq_iff_eq] at h
  exact ⟨r,s,h.1,fun w hw hne => (h.2 w hw).resolve_left hne⟩

def lowSingle (i : Nat) : Row := if i = 0 then 2 else 1

def highSingle (i : Nat) : Row :=
  Fin.ofNat 512 ((lowSingle i).val + (1 <<< i))

lemma threshold4EssentialTest : ∀ i : Fin 4,
    checkEssential threshold4 (roots 4) (input i.val) (lowSingle i.val) (highSingle i.val) = true := by
  decide +kernel

lemma threshold5EssentialTest : ∀ i : Fin 5,
    checkEssential threshold5 (roots 5) (input i.val) (lowSingle i.val) (highSingle i.val) = true := by
  decide +kernel

lemma threshold6EssentialTest : ∀ i : Fin 6,
    checkEssential threshold6 (roots 6) (input i.val) (lowSingle i.val) (highSingle i.val) = true := by
  decide +kernel

def positiveRows : List Nat := [3,5,6,7,9,10,11,12,13,14,15,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31]
def negativeRows : List Nat := [0,1,2,4,8,16]

def assignment (r : Row) : Nat :=
  if r.val < 128 then r.val
  else if r.val < 284 then positiveRows.getD ((r.val-128)/6) 0
  else if r.val < 440 then negativeRows.getD ((r.val-284)%6) 0
  else 0

def selectRows (i : Nat) (r : Row) : Row :=
  let base := 1 <<< i
  let a := assignment r
  Fin.ofNat 512 ((a % base + 2 * (a - a % base)) % 128)

def inBase (base : List Sig) (a : Sig) : Bool := a == zero || base.contains a

lemma inBase_sound {base : List Sig} {f : Row → Row} {a : Sig}
    (h : inBase base (rename f a) = true) :
    Available true (base.map observe) (restrictRows f (observe a)) := by
  simp only [inBase, Bool.or_eq_true, beq_iff_eq, List.contains_eq_mem, decide_eq_true_eq] at h
  rw [←observe_rename]
  rcases h with hz | hm
  · rw [hz]
    exact Or.inr (Or.inl ⟨false, funext bit_zero⟩)
  · exact Or.inl (List.mem_map_of_mem hm)

lemma threshold3EssentialTest : ∀ i : Fin 3,
    checkEssential threshold3 (roots 3) (input i.val) (lowSingle i.val) (highSingle i.val) = true := by
  decide +kernel

lemma reject3 : reject threshold3 3 0 3 [] (roots 3) = true := by decide +kernel

lemma lower3 : Lower true (roots 3) threshold3 4 := by
  apply lower_impossible (by unfold proper; decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro a ha
    obtain ⟨i,rfl⟩ := input_index ha
    exact checkEssential_sound (threshold3EssentialTest i)
  · exact reject_sound (by decide +kernel) (by simp [budget]) reject3

def initial4 : Cuts := (List.finRange 4).map fun i => (neg (input i.val), 0)

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
lemma cutTo3 : ∀ i : Fin 4,
    rename (selectRows i.val) threshold4 = threshold3 ∧
    (∀ r : Row, bit (selectRows i.val r) (neg (input i.val)) = true) ∧
    (roots 4).all (fun w => inBase (roots 3) (rename (selectRows i.val) w)) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
lemma initialBudget4 : budget threshold4 6 4 6 initial4 (roots 4) := by
  intro c hc
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hc
  obtain ⟨eq, dom, check⟩ := cutTo3 i
  have heq : restrictRows (selectRows i.val) (observe threshold4) = observe threshold3 :=
    (observe_rename _ _).symm.trans (congrArg observe eq)
  refine ⟨selectRows i.val, roots 3, 0, _, dom, Nat.le_refl _, Reach.start,
    (fun _ hm => inBase_sound (List.all_eq_true.mp check _ hm)), ?_, ?_⟩
  · rw [heq]
    exact observe_proper (by unfold proper; decide +kernel)
  · rw [heq]
    exact lower3

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
lemma reject4 : reject threshold4 6 4 6 initial4 (roots 4) = true := by decide +kernel

lemma lower4 : Lower true (roots 4) threshold4 7 := by
  apply lower_impossible (by unfold proper; decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro a ha
    obtain ⟨i,rfl⟩ := input_index ha
    exact checkEssential_sound (threshold4EssentialTest i)
  · exact reject_sound (by decide +kernel) initialBudget4 reject4

def initial5 : Cuts := (List.finRange 5).map fun i => (neg (input i.val), 0)

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
lemma cutTo4 : ∀ i : Fin 5,
    rename (selectRows i.val) threshold5 = threshold4 ∧
    (∀ r : Row, bit (selectRows i.val r) (neg (input i.val)) = true) ∧
    (roots 5).all (fun w => inBase (roots 4) (rename (selectRows i.val) w)) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
lemma initialBudget5 : budget threshold5 9 7 9 initial5 (roots 5) := by
  intro c hc
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hc
  obtain ⟨eq, dom, check⟩ := cutTo4 i
  have heq : restrictRows (selectRows i.val) (observe threshold5) = observe threshold4 :=
    (observe_rename _ _).symm.trans (congrArg observe eq)
  refine ⟨selectRows i.val, roots 4, 0, _, dom, Nat.le_refl _, Reach.start,
    (fun _ hm => inBase_sound (List.all_eq_true.mp check _ hm)), ?_, ?_⟩
  · rw [heq]
    exact observe_proper (by unfold proper; decide +kernel)
  · rw [heq]
    exact lower4

def swapAssignment (i j : Fin 5) (m : Nat) : Nat :=
  if m.testBit i.val == m.testBit j.val then m
  else m ^^^ ((1 <<< i.val) ||| (1 <<< j.val))

def swappedPair (i j : Fin 5) (k : Nat) : Nat :=
  positiveRows.idxOf (swapAssignment i j (positiveRows.getD (k/6) 0)) * 6 +
    negativeRows.idxOf (swapAssignment i j (negativeRows.getD (k%6) 0))

def swapRow (i j : Fin 5) (r : Row) : Row :=
  if r.val < 128 then Fin.ofNat 512 (swapAssignment i j r.val)
  else if r.val < 284 then Fin.ofNat 512 (128 + swappedPair i j (r.val-128))
  else if r.val < 440 then Fin.ofNat 512 (284 + swappedPair i j (r.val-284))
  else r

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
lemma swapRow_involutive : ∀ (i j : Fin 5) (r : Row), swapRow i j (swapRow i j r) = r := by
  decide +kernel

def firstPairRows (i j : Fin 5) (r : Row) : Row :=
  swapRow i 0 (swapRow (if j = 0 then i else j) 1 r)

lemma pairRows_onto (i j : Fin 5) : Function.Surjective (firstPairRows i j) :=
  (Function.Involutive.surjective (swapRow_involutive i 0)).comp
    (Function.Involutive.surjective (swapRow_involutive (if j = 0 then i else j) 1))

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
lemma pairRows_valid : ∀ (i j : Fin 5), i ≠ j →
    rename (firstPairRows i j) threshold5 = threshold5 ∧
    (roots 5).toFinset.image (rename (firstPairRows i j)) = (roots 5).toFinset ∧
    rename (firstPairRows i j) (input i.val) = input 0 ∧
    rename (firstPairRows i j) (input j.val) = input 1 := by
  decide +kernel

lemma child_rename {ws : List Sig} {a b : Sig} {d : Nat} {ka kb : Bool}
    (hn : ws.Nodup) {f : Row → Row} (onto : Function.Surjective f)
    (invariantB : ws.toFinset.image (rename f) = ws.toFinset) :
    (childTwo ws a b d ka kb).toFinset.image (rename f) =
      (childTwo ws (rename f a) (rename f b) d ka kb).toFinset := by
  have hi := rename_inj f onto
  unfold childTwo
  simp only [List.toFinset_cons,Finset.image_insert,rename_bin,kept_fin]
  cases ka <;> cases kb <;>
    simp [erase_fin (hn.erase _), erase_fin hn, Finset.image_erase hi, invariantB]

abbrev FrontierNode := Cuts × List Sig

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
def frontierSig : Nat → Sig
  | 0 => (((0x3 * 0x10000000000000000 + 0xffff03ffffffffc0) * 0x10000000000000000 + 0x0000eee00000eee0) * 0x10000000000000000 + 0x0000eee00000eee0)
  | 1 => (((0x3 * 0x10000000000000000 + 0xfffffff03ffff03f) * 0x10000000000000000 + 0x0000fac80000fac8) * 0x10000000000000000 + 0x0000fac80000fac8)
  | 2 => (((0x3 * 0x10000000000000000 + 0xffffffffc0fc0fff) * 0x10000000000000000 + 0x0000fca80000fca8) * 0x10000000000000000 + 0x0000fca80000fca8)
  | 3 => (((0xffffc0ffffc * 0x10000000000000000 + 0x0000000000ffffc0) * 0x10000000000000000 + 0x00ee00e000ee00e0) * 0x10000000000000000 + 0x00ee00e000ee00e0)
  | 4 => (((0xfffffffc0fc * 0x10000000000000000 + 0x0000000000fff03f) * 0x10000000000000000 + 0x00fa00c800fa00c8) * 0x10000000000000000 + 0x00fa00c800fa00c8)
  | 5 => (((0xfffffffff00 * 0x10000000000000000 + 0x0000000000fc0fff) * 0x10000000000000000 + 0x00fc00a800fc00a8) * 0x10000000000000000 + 0x00fc00a800fc00a8)
  | 6 => ((((0xf * 0x10000000000000000 + 0xfffc0000000ffffc) * 0x10000000000000000 + 0x000003ffff000000) * 0x10000000000000000 + 0x0e0e0e000e0e0e00) * 0x10000000000000000 + 0x0e0e0e000e0e0e00)
  | 7 => ((((0xf * 0x10000000000000000 + 0xfffff000000fc0fc) * 0x10000000000000000 + 0x000003ffc000003f) * 0x10000000000000000 + 0x0f0a0c080f0a0c08) * 0x10000000000000000 + 0x0f0a0c080f0a0c08)
  | 8 => ((((0xf * 0x10000000000000000 + 0xfffff000000fff00) * 0x10000000000000000 + 0x000003f03f00003f) * 0x10000000000000000 + 0x0f0c0a080f0c0a08) * 0x10000000000000000 + 0x0f0c0a080f0c0a08)
  | 9 => ((((0xffffc0f * 0x10000000000000000 + 0xfffc0ffffc000003) * 0x10000000000000000 + 0xffff03ffffffffc0) * 0x10000000000000000 + 0xeee0eee0eee0eee0) * 0x10000000000000000 + 0xeee0eee0eee0eee0)
  | 10 => ((((0xffffc0f * 0x10000000000000000 + 0xfffc0ffffc0fffff) * 0x10000000000000000 + 0xffff000000ffffc0) * 0x10000000000000000 + 0xeeeee0e0eeeee0e0) * 0x10000000000000000 + 0xeeeee0e0eeeee0e0)
  | 11 => ((((0xffffc0f * 0x10000000000000000 + 0xfffc0ffffc0fffff) * 0x10000000000000000 + 0xffff03ffff000000) * 0x10000000000000000 + 0xeeeeee00eeeeee00) * 0x10000000000000000 + 0xeeeeee00eeeeee00)
  | 12 => ((((0xffffc0f * 0x10000000000000000 + 0xfffc0ffffc0fffff) * 0x10000000000000000 + 0xffff03ffffffffc0) * 0x10000000000000000 + 0xeeeeeee0eeeeeee0) * 0x10000000000000000 + 0xeeeeeee0eeeeeee0)
  | 13 => ((((0xffffff0 * 0x10000000000000000 + 0x00000ffffff00003) * 0x10000000000000000 + 0xfffffc0000ffffc0) * 0x10000000000000000 + 0xf0f0f0e0f0f0f0e0) * 0x10000000000000000 + 0xf0f0f0e0f0f0f0e0)
  | 14 => ((((0xfffffff * 0x10000000000000000 + 0xc0fc0fff000fc003) * 0x10000000000000000 + 0xfffffff03ffff03f) * 0x10000000000000000 + 0xfac8fac8fac8fac8) * 0x10000000000000000 + 0xfac8fac8fac8fac8)
  | 15 => ((((0xfffffff * 0x10000000000000000 + 0xc0fc0fffffffc0ff) * 0x10000000000000000 + 0xffc003f000fff03f) * 0x10000000000000000 + 0xfafac8c8fafac8c8) * 0x10000000000000000 + 0xfafac8c8fafac8c8)
  | 16 => ((((0xfffffff * 0x10000000000000000 + 0xc0fc0fffffffc0ff) * 0x10000000000000000 + 0xfffffff03ffff03f) * 0x10000000000000000 + 0xfafafac8fafafac8) * 0x10000000000000000 + 0xfafafac8fafafac8)
  | 17 => ((((0xfffffff * 0x10000000000000000 + 0xff000fc0fc0fc003) * 0x10000000000000000 + 0xffffffffc0fc0fff) * 0x10000000000000000 + 0xfca8fca8fca8fca8) * 0x10000000000000000 + 0xfca8fca8fca8fca8)
  | 18 => ((((0xfffffff * 0x10000000000000000 + 0xff000fffffffff03) * 0x10000000000000000 + 0xf03f03f000fc0fff) * 0x10000000000000000 + 0xfcfca8a8fcfca8a8) * 0x10000000000000000 + 0xfcfca8a8fcfca8a8)
  | 19 => ((((0xfffffff * 0x10000000000000000 + 0xff000fffffffff03) * 0x10000000000000000 + 0xffffffffc0fc0fff) * 0x10000000000000000 + 0xfcfcfca8fcfcfca8) * 0x10000000000000000 + 0xfcfcfca8fcfcfca8)
  | 20 => ((((0xfffffff * 0x10000000000000000 + 0xfffc0fffffffffff) * 0x10000000000000000 + 0xffffffffff000000) * 0x10000000000000000 + 0xfefefe00fefefe00) * 0x10000000000000000 + 0xfefefe00fefefe00)
  | 21 => ((((0xfffffff * 0x10000000000000000 + 0xfffff00000000003) * 0x10000000000000000 + 0xffffffffff000000) * 0x10000000000000000 + 0xff00fe00ff00fe00) * 0x10000000000000000 + 0xff00fe00ff00fe00)
  | 22 => ((((0xfffffff * 0x10000000000000000 + 0xffffffc0fc0fc0ff) * 0x10000000000000000 + 0xffc003ffc0fc003f) * 0x10000000000000000 + 0xffaacc88ffaacc88) * 0x10000000000000000 + 0xffaacc88ffaacc88)
  | 23 => ((((0xfffffff * 0x10000000000000000 + 0xffffffc0fc0fc0ff) * 0x10000000000000000 + 0xffffffffc0fc0fff) * 0x10000000000000000 + 0xffaafca8ffaafca8) * 0x10000000000000000 + 0xffaafca8ffaafca8)
  | 24 => ((((0xfffffff * 0x10000000000000000 + 0xffffffff000fff03) * 0x10000000000000000 + 0xf03f03f03ffc003f) * 0x10000000000000000 + 0xffccaa88ffccaa88) * 0x10000000000000000 + 0xffccaa88ffccaa88)
  | 25 => ((((0xfffffff * 0x10000000000000000 + 0xffffffff000fff03) * 0x10000000000000000 + 0xfffffff03ffff03f) * 0x10000000000000000 + 0xffccfac8ffccfac8) * 0x10000000000000000 + 0xffccfac8ffccfac8)
  | 26 => ((((0xfffffff * 0x10000000000000000 + 0xfffffffffc0fffff) * 0x10000000000000000 + 0xfffffc0000ffffc0) * 0x10000000000000000 + 0xffeef0e0ffeef0e0) * 0x10000000000000000 + 0xffeef0e0ffeef0e0)
  | 27 => ((((0xfffffff * 0x10000000000000000 + 0xfffffffffff00003) * 0x10000000000000000 + 0xffff03ffffffffc0) * 0x10000000000000000 + 0xfff0eee0fff0eee0) * 0x10000000000000000 + 0xfff0eee0fff0eee0)
  | 28 => ((((0xfffffff * 0x10000000000000000 + 0xffffffffffffc0ff) * 0x10000000000000000 + 0xffc003ffc0fff03f) * 0x10000000000000000 + 0xfffaccc8fffaccc8) * 0x10000000000000000 + 0xfffaccc8fffaccc8)
  | 29 => ((((0xfffffff * 0x10000000000000000 + 0xffffffffffffff03) * 0x10000000000000000 + 0xf03f03f03ffc0fff) * 0x10000000000000000 + 0xfffcaaa8fffcaaa8) * 0x10000000000000000 + 0xfffcaaa8fffcaaa8)
  | 30 => ((((0xfffffff * 0x10000000000000000 + 0xfffffffffffffffc) * 0x10000000000000000 + 0x0000000000000000) * 0x10000000000000000 + 0xfffe0000fffe0000) * 0x10000000000000000 + 0xfffe0000fffe0000)
  | 31 => ((((((0x8208208208208 * 0x10000000000000000 + 0x2082082082082082) * 0x10000000000000000 + 0x0820820820000000) * 0x10000000000000000 + 0x00000000fc0000ff) * 0x10000000000000000 + 0xffff03fffffc0fff) * 0x10000000000000000 + 0x0022eeaa0022eeaa) * 0x10000000000000000 + 0x0022eeaa0022eeaa)
  | 32 => ((((((0x8208208208208 * 0x10000000000000000 + 0x2082082082082082) * 0x10000000000000000 + 0x0820820820000000) * 0x10000000000000000 + 0x00000ffffc0ffffc) * 0x10000000000000000 + 0x003f00003ffc0fff) * 0x10000000000000000 + 0x00ee22aa00ee22aa) * 0x10000000000000000 + 0x00ee22aa00ee22aa)
  | 33 => ((((((0x8208208208208 * 0x10000000000000000 + 0x2082082082082082) * 0x10000000000000000 + 0x0820820820000000) * 0x10000000000000000 + 0x00fc0000000000ff) * 0x10000000000000000 + 0xffff03f03fffffff) * 0x10000000000000000 + 0x0202eaea0202eaea) * 0x10000000000000000 + 0x0202eaea0202eaea)
  | 34 => ((((((0x8208208208208 * 0x10000000000000000 + 0x2082082082082082) * 0x10000000000000000 + 0x0820820820000000) * 0x10000000000000000 + 0x00fc0ffffc0fc0fc) * 0x10000000000000000 + 0x000000003fffffff) * 0x10000000000000000 + 0x02ea02ea02ea02ea) * 0x10000000000000000 + 0x02ea02ea02ea02ea)
  | 35 => ((((((0x8208208208208 * 0x10000000000000000 + 0x2082082082082082) * 0x10000000000000000 + 0x082082082000000f) * 0x10000000000000000 + 0xfffc0000000ffffc) * 0x10000000000000000 + 0x003f03f03f000fff) * 0x10000000000000000 + 0x0e0e2a2a0e0e2a2a) * 0x10000000000000000 + 0x0e0e2a2a0e0e2a2a)
  | 36 => ((((((0x8208208208208 * 0x10000000000000000 + 0x2082082082082082) * 0x10000000000000000 + 0x082082082000000f) * 0x10000000000000000 + 0xfffc0000fc0fc0fc) * 0x10000000000000000 + 0x000003ffff000fff) * 0x10000000000000000 + 0x0e2a0e2a0e2a0e2a) * 0x10000000000000000 + 0x0e2a0e2a0e2a0e2a)
  | 37 => ((((((0x8208208208208 * 0x10000000000000000 + 0x2082082082082082) * 0x10000000000000000 + 0x082082082fc0fc0f) * 0x10000000000000000 + 0xc0fc0fc0fc0fc0ff) * 0x10000000000000000 + 0xf03f03f03ffc0fff) * 0x10000000000000000 + 0xaaaaaaaaaaaaaaaa) * 0x10000000000000000 + 0xaaaaaaaaaaaaaaaa)
  | 38 => ((((((0x8208208208208 * 0x10000000000000000 + 0x2082082082082082) * 0x10000000000000000 + 0x082082082ffffc00) * 0x10000000000000000 + 0x00000ffffc000003) * 0x10000000000000000 + 0xffff00003fffffc0) * 0x10000000000000000 + 0xe0e0e2e2e0e0e2e2) * 0x10000000000000000 + 0xe0e0e2e2e0e0e2e2)
  | 39 => ((((((0x8208208208208 * 0x10000000000000000 + 0x2082082082082082) * 0x10000000000000000 + 0x082082082ffffc00) * 0x10000000000000000 + 0x00000ffffc0000ff) * 0x10000000000000000 + 0xffff000000ffffc0) * 0x10000000000000000 + 0xe0e2e0e2e0e2e0e2) * 0x10000000000000000 + 0xe0e2e0e2e0e2e0e2)
  | 40 => ((((((0x8208208208208 * 0x10000000000000000 + 0x2082082082082082) * 0x10000000000000000 + 0x082082082ffffc0f) * 0x10000000000000000 + 0xfffc000000000003) * 0x10000000000000000 + 0xffff03ffff000fc0) * 0x10000000000000000 + 0xee00ee22ee00ee22) * 0x10000000000000000 + 0xee00ee22ee00ee22)
  | 41 => ((((((0x8208208208208 * 0x10000000000000000 + 0x2082082082082082) * 0x10000000000000000 + 0x082082082ffffc0f) * 0x10000000000000000 + 0xfffc0000000000ff) * 0x10000000000000000 + 0xffff03ffff000000) * 0x10000000000000000 + 0xee02ee02ee02ee02) * 0x10000000000000000 + 0xee02ee02ee02ee02)
  | 42 => ((((((0x8208208208208 * 0x10000000000000000 + 0x2082082082082082) * 0x10000000000000000 + 0x082082082ffffc0f) * 0x10000000000000000 + 0xfffc0ffffc0fc0ff) * 0x10000000000000000 + 0xffff03ffffffffff) * 0x10000000000000000 + 0xeeeaeeeaeeeaeeea) * 0x10000000000000000 + 0xeeeaeeeaeeeaeeea)
  | 43 => ((((((0x8208208208208 * 0x10000000000000000 + 0x2082082082082082) * 0x10000000000000000 + 0x082082082ffffc0f) * 0x10000000000000000 + 0xfffc0ffffc0ffffc) * 0x10000000000000000 + 0x0000000000000fc0) * 0x10000000000000000 + 0xeeee0022eeee0022) * 0x10000000000000000 + 0xeeee0022eeee0022)
  | 44 => ((((((0x8208208208208 * 0x10000000000000000 + 0x2082082082082082) * 0x10000000000000000 + 0x082082082ffffc0f) * 0x10000000000000000 + 0xfffc0ffffc0ffffc) * 0x10000000000000000 + 0x000000003f000000) * 0x10000000000000000 + 0xeeee0202eeee0202) * 0x10000000000000000 + 0xeeee0202eeee0202)
  | 45 => ((((((0x8208208208208 * 0x10000000000000000 + 0x2082082082082082) * 0x10000000000000000 + 0x082082082ffffc0f) * 0x10000000000000000 + 0xfffc0ffffc0fffff) * 0x10000000000000000 + 0xffff03f03fffffff) * 0x10000000000000000 + 0xeeeeeaeaeeeeeaea) * 0x10000000000000000 + 0xeeeeeaeaeeeeeaea)
  | 46 => ((((((0x8208208208208 * 0x10000000000000000 + 0x2082082082082082) * 0x10000000000000000 + 0x082082082ffffc0f) * 0x10000000000000000 + 0xfffc0ffffc0fffff) * 0x10000000000000000 + 0xffff03fffffc0fff) * 0x10000000000000000 + 0xeeeeeeaaeeeeeeaa) * 0x10000000000000000 + 0xeeeeeeaaeeeeeeaa)
  | 47 => ((((((0x8208208208208 * 0x10000000000000000 + 0x2082082082082082) * 0x10000000000000000 + 0x082082082ffffff0) * 0x10000000000000000 + 0x00000fc0fc0000ff) * 0x10000000000000000 + 0xfffffc0000fc0fc0) * 0x10000000000000000 + 0xf0a2f0a2f0a2f0a2) * 0x10000000000000000 + 0xf0a2f0a2f0a2f0a2)
  | 48 => ((((((0x8208208208208 * 0x10000000000000000 + 0x2082082082082082) * 0x10000000000000000 + 0x082082082ffffff0) * 0x10000000000000000 + 0x00000ffffff00003) * 0x10000000000000000 + 0xf03f00003ffc0fc0) * 0x10000000000000000 + 0xf0f0a2a2f0f0a2a2) * 0x10000000000000000 + 0xf0f0a2a2f0f0a2a2)
  | 49 => ((((((0x8208208208208 * 0x10000000000000000 + 0x2082082082082082) * 0x10000000000000000 + 0x082082082fffffff) * 0x10000000000000000 + 0xc0fc0000000000ff) * 0x10000000000000000 + 0xfffffff03f000000) * 0x10000000000000000 + 0xfa02fa02fa02fa02) * 0x10000000000000000 + 0xfa02fa02fa02fa02)
  | 50 => ((((((0x8208208208208 * 0x10000000000000000 + 0x2082082082082082) * 0x10000000000000000 + 0x082082082fffffff) * 0x10000000000000000 + 0xc0fc0ffffc0fc0ff) * 0x10000000000000000 + 0xfffffff03fffffff) * 0x10000000000000000 + 0xfaeafaeafaeafaea) * 0x10000000000000000 + 0xfaeafaeafaeafaea)
  | 51 => ((((((0x8208208208208 * 0x10000000000000000 + 0x2082082082082082) * 0x10000000000000000 + 0x082082082fffffff) * 0x10000000000000000 + 0xc0fc0fffffffc0fc) * 0x10000000000000000 + 0x000000003f000000) * 0x10000000000000000 + 0xfafa0202fafa0202) * 0x10000000000000000 + 0xfafa0202fafa0202)
  | 52 => ((((((0x8208208208208 * 0x10000000000000000 + 0x2082082082082082) * 0x10000000000000000 + 0x082082082fffffff) * 0x10000000000000000 + 0xc0fc0fffffffc0ff) * 0x10000000000000000 + 0xffff03f03fffffff) * 0x10000000000000000 + 0xfafaeaeafafaeaea) * 0x10000000000000000 + 0xfafaeaeafafaeaea)
  | 53 => ((((((0x8208208208208 * 0x10000000000000000 + 0x2082082082082082) * 0x10000000000000000 + 0x082082082fffffff) * 0x10000000000000000 + 0xfffc0fc0fc0fc0ff) * 0x10000000000000000 + 0xfffffffffffc0fff) * 0x10000000000000000 + 0xfeaafeaafeaafeaa) * 0x10000000000000000 + 0xfeaafeaafeaafeaa)
  | 54 => ((((((0x8208208208208 * 0x10000000000000000 + 0x2082082082082082) * 0x10000000000000000 + 0x082082082fffffff) * 0x10000000000000000 + 0xfffc0fffffffffff) * 0x10000000000000000 + 0xf03f03f03ffc0fff) * 0x10000000000000000 + 0xfefeaaaafefeaaaa) * 0x10000000000000000 + 0xfefeaaaafefeaaaa)
  | 55 => ((((((0x8208208208208 * 0x10000000000000000 + 0x2082082082082082) * 0x10000000000000000 + 0x082082082fffffff) * 0x10000000000000000 + 0xfffc0fffffffffff) * 0x10000000000000000 + 0xfffffffffffc0fff) * 0x10000000000000000 + 0xfefefeaafefefeaa) * 0x10000000000000000 + 0xfefefeaafefefeaa)
  | 56 => ((((((0x8208208208208 * 0x10000000000000000 + 0x2082082082082082) * 0x10000000000000000 + 0x082082082fffffff) * 0x10000000000000000 + 0xfffff00000000003) * 0x10000000000000000 + 0xf03f03f03f000fc0) * 0x10000000000000000 + 0xff00aa22ff00aa22) * 0x10000000000000000 + 0xff00aa22ff00aa22)
  | 57 => ((((((0x8208208208208 * 0x10000000000000000 + 0x2082082082082082) * 0x10000000000000000 + 0x082082082fffffff) * 0x10000000000000000 + 0xffffffc0fc0fc0fc) * 0x10000000000000000 + 0x0000000000000fc0) * 0x10000000000000000 + 0xffaa0022ffaa0022) * 0x10000000000000000 + 0xffaa0022ffaa0022)
  | 58 => ((((((0x8208208208208 * 0x10000000000000000 + 0x2082082082082082) * 0x10000000000000000 + 0x082082082fffffff) * 0x10000000000000000 + 0xffffffc0fc0fc0ff) * 0x10000000000000000 + 0xffff03fffffc0fff) * 0x10000000000000000 + 0xffaaeeaaffaaeeaa) * 0x10000000000000000 + 0xffaaeeaaffaaeeaa)
  | 59 => ((((((0x8208208208208 * 0x10000000000000000 + 0x2082082082082082) * 0x10000000000000000 + 0x082082082fffffff) * 0x10000000000000000 + 0xfffffffffc0fffff) * 0x10000000000000000 + 0xf03f03f03ffc0fff) * 0x10000000000000000 + 0xffeeaaaaffeeaaaa) * 0x10000000000000000 + 0xffeeaaaaffeeaaaa)
  | 60 => ((((((0x8208208208208 * 0x10000000000000000 + 0x2082082082082082) * 0x10000000000000000 + 0x082082082fffffff) * 0x10000000000000000 + 0xfffffffffc0fffff) * 0x10000000000000000 + 0xfffffff03fffffff) * 0x10000000000000000 + 0xffeefaeaffeefaea) * 0x10000000000000000 + 0xffeefaeaffeefaea)
  | 61 => ((((((0x8208208208208 * 0x10000000000000000 + 0x2082082082082082) * 0x10000000000000000 + 0x082082082fffffff) * 0x10000000000000000 + 0xffffffffffffc0ff) * 0x10000000000000000 + 0xffff03ffffffffff) * 0x10000000000000000 + 0xfffaeeeafffaeeea) * 0x10000000000000000 + 0xfffaeeeafffaeeea)
  | 62 => ((((((0x10410410410410 * 0x10000000000000000 + 0x4104104104104104) * 0x10000000000000000 + 0x1041041040000000) * 0x10000000000000000 + 0x0000003f00003f03) * 0x10000000000000000 + 0xffff03fffffff03f) * 0x10000000000000000 + 0x0044eecc0044eecc) * 0x10000000000000000 + 0x0044eecc0044eecc)
  | 63 => ((((((0x10410410410410 * 0x10000000000000000 + 0x4104104104104104) * 0x10000000000000000 + 0x1041041040000000) * 0x10000000000000000 + 0x00000ffffc0ffffc) * 0x10000000000000000 + 0x0fc0000fc0fff03f) * 0x10000000000000000 + 0x00ee44cc00ee44cc) * 0x10000000000000000 + 0x00ee44cc00ee44cc)
  | 64 => ((((((0x10410410410410 * 0x10000000000000000 + 0x4104104104104104) * 0x10000000000000000 + 0x1041041040000000) * 0x10000000000000000 + 0x3f00000000003f03) * 0x10000000000000000 + 0xffff03ffc0ffffff) * 0x10000000000000000 + 0x0404ecec0404ecec) * 0x10000000000000000 + 0x0404ecec0404ecec)
  | 65 => ((((((0x10410410410410 * 0x10000000000000000 + 0x4104104104104104) * 0x10000000000000000 + 0x1041041040000000) * 0x10000000000000000 + 0x3f000ffffc0fff00) * 0x10000000000000000 + 0x0000000fc0ffffff) * 0x10000000000000000 + 0x04ec04ec04ec04ec) * 0x10000000000000000 + 0x04ec04ec04ec04ec)
  | 66 => ((((((0x10410410410410 * 0x10000000000000000 + 0x4104104104104104) * 0x10000000000000000 + 0x104104104000000f) * 0x10000000000000000 + 0xfffc0000000ffffc) * 0x10000000000000000 + 0x0fc003ffc003f03f) * 0x10000000000000000 + 0x0e0e4c4c0e0e4c4c) * 0x10000000000000000 + 0x0e0e4c4c0e0e4c4c)
  | 67 => ((((((0x10410410410410 * 0x10000000000000000 + 0x4104104104104104) * 0x10000000000000000 + 0x104104104000000f) * 0x10000000000000000 + 0xfffc003f000fff00) * 0x10000000000000000 + 0x000003ffff03f03f) * 0x10000000000000000 + 0x0e4c0e4c0e4c0e4c) * 0x10000000000000000 + 0x0e4c0e4c0e4c0e4c)
  | 68 => ((((((0x10410410410410 * 0x10000000000000000 + 0x4104104104104104) * 0x10000000000000000 + 0x104104104fff000f) * 0x10000000000000000 + 0xff000fff000fff03) * 0x10000000000000000 + 0xffc003ffc0fff03f) * 0x10000000000000000 + 0xcccccccccccccccc) * 0x10000000000000000 + 0xcccccccccccccccc)
  | 69 => ((((((0x10410410410410 * 0x10000000000000000 + 0x4104104104104104) * 0x10000000000000000 + 0x104104104ffffc00) * 0x10000000000000000 + 0x00000ffffc000003) * 0x10000000000000000 + 0xffff000fc0ffffc0) * 0x10000000000000000 + 0xe0e0e4e4e0e0e4e4) * 0x10000000000000000 + 0xe0e0e4e4e0e0e4e4)
  | 70 => ((((((0x10410410410410 * 0x10000000000000000 + 0x4104104104104104) * 0x10000000000000000 + 0x104104104ffffc00) * 0x10000000000000000 + 0x00000ffffc003f03) * 0x10000000000000000 + 0xffff000000ffffc0) * 0x10000000000000000 + 0xe0e4e0e4e0e4e0e4) * 0x10000000000000000 + 0xe0e4e0e4e0e4e0e4)
  | 71 => ((((((0x10410410410410 * 0x10000000000000000 + 0x4104104104104104) * 0x10000000000000000 + 0x104104104ffffc0f) * 0x10000000000000000 + 0xfffc000000000003) * 0x10000000000000000 + 0xffff03ffff03f000) * 0x10000000000000000 + 0xee00ee44ee00ee44) * 0x10000000000000000 + 0xee00ee44ee00ee44)
  | 72 => ((((((0x10410410410410 * 0x10000000000000000 + 0x4104104104104104) * 0x10000000000000000 + 0x104104104ffffc0f) * 0x10000000000000000 + 0xfffc000000003f03) * 0x10000000000000000 + 0xffff03ffff000000) * 0x10000000000000000 + 0xee04ee04ee04ee04) * 0x10000000000000000 + 0xee04ee04ee04ee04)
  | 73 => ((((((0x10410410410410 * 0x10000000000000000 + 0x4104104104104104) * 0x10000000000000000 + 0x104104104ffffc0f) * 0x10000000000000000 + 0xfffc0ffffc0fff03) * 0x10000000000000000 + 0xffff03ffffffffff) * 0x10000000000000000 + 0xeeeceeeceeeceeec) * 0x10000000000000000 + 0xeeeceeeceeeceeec)
  | 74 => ((((((0x10410410410410 * 0x10000000000000000 + 0x4104104104104104) * 0x10000000000000000 + 0x104104104ffffc0f) * 0x10000000000000000 + 0xfffc0ffffc0ffffc) * 0x10000000000000000 + 0x000000000003f000) * 0x10000000000000000 + 0xeeee0044eeee0044) * 0x10000000000000000 + 0xeeee0044eeee0044)
  | 75 => ((((((0x10410410410410 * 0x10000000000000000 + 0x4104104104104104) * 0x10000000000000000 + 0x104104104ffffc0f) * 0x10000000000000000 + 0xfffc0ffffc0ffffc) * 0x10000000000000000 + 0x0000000fc0000000) * 0x10000000000000000 + 0xeeee0404eeee0404) * 0x10000000000000000 + 0xeeee0404eeee0404)
  | 76 => ((((((0x10410410410410 * 0x10000000000000000 + 0x4104104104104104) * 0x10000000000000000 + 0x104104104ffffc0f) * 0x10000000000000000 + 0xfffc0ffffc0fffff) * 0x10000000000000000 + 0xffff03ffc0ffffff) * 0x10000000000000000 + 0xeeeeececeeeeecec) * 0x10000000000000000 + 0xeeeeececeeeeecec)
  | 77 => ((((((0x10410410410410 * 0x10000000000000000 + 0x4104104104104104) * 0x10000000000000000 + 0x104104104ffffc0f) * 0x10000000000000000 + 0xfffc0ffffc0fffff) * 0x10000000000000000 + 0xffff03fffffff03f) * 0x10000000000000000 + 0xeeeeeecceeeeeecc) * 0x10000000000000000 + 0xeeeeeecceeeeeecc)
  | 78 => ((((((0x10410410410410 * 0x10000000000000000 + 0x4104104104104104) * 0x10000000000000000 + 0x104104104ffffff0) * 0x10000000000000000 + 0x00000fff00003f03) * 0x10000000000000000 + 0xfffffc0000fff000) * 0x10000000000000000 + 0xf0c4f0c4f0c4f0c4) * 0x10000000000000000 + 0xf0c4f0c4f0c4f0c4)
  | 79 => ((((((0x10410410410410 * 0x10000000000000000 + 0x4104104104104104) * 0x10000000000000000 + 0x104104104ffffff0) * 0x10000000000000000 + 0x00000ffffff00003) * 0x10000000000000000 + 0xffc0000fc0fff000) * 0x10000000000000000 + 0xf0f0c4c4f0f0c4c4) * 0x10000000000000000 + 0xf0f0c4c4f0f0c4c4)
  | 80 => ((((((0x10410410410410 * 0x10000000000000000 + 0x4104104104104104) * 0x10000000000000000 + 0x104104104fffffff) * 0x10000000000000000 + 0xff00000000003f03) * 0x10000000000000000 + 0xffffffffc0000000) * 0x10000000000000000 + 0xfc04fc04fc04fc04) * 0x10000000000000000 + 0xfc04fc04fc04fc04)
  | 81 => ((((((0x10410410410410 * 0x10000000000000000 + 0x4104104104104104) * 0x10000000000000000 + 0x104104104fffffff) * 0x10000000000000000 + 0xff000ffffc0fff03) * 0x10000000000000000 + 0xffffffffc0ffffff) * 0x10000000000000000 + 0xfcecfcecfcecfcec) * 0x10000000000000000 + 0xfcecfcecfcecfcec)
  | 82 => ((((((0x10410410410410 * 0x10000000000000000 + 0x4104104104104104) * 0x10000000000000000 + 0x104104104fffffff) * 0x10000000000000000 + 0xff000fffffffff00) * 0x10000000000000000 + 0x0000000fc0000000) * 0x10000000000000000 + 0xfcfc0404fcfc0404) * 0x10000000000000000 + 0xfcfc0404fcfc0404)
  | 83 => ((((((0x10410410410410 * 0x10000000000000000 + 0x4104104104104104) * 0x10000000000000000 + 0x104104104fffffff) * 0x10000000000000000 + 0xff000fffffffff03) * 0x10000000000000000 + 0xffff03ffc0ffffff) * 0x10000000000000000 + 0xfcfcececfcfcecec) * 0x10000000000000000 + 0xfcfcececfcfcecec)
  | 84 => ((((((0x10410410410410 * 0x10000000000000000 + 0x4104104104104104) * 0x10000000000000000 + 0x104104104fffffff) * 0x10000000000000000 + 0xfffc0fff000fff03) * 0x10000000000000000 + 0xfffffffffffff03f) * 0x10000000000000000 + 0xfeccfeccfeccfecc) * 0x10000000000000000 + 0xfeccfeccfeccfecc)
  | 85 => ((((((0x10410410410410 * 0x10000000000000000 + 0x4104104104104104) * 0x10000000000000000 + 0x104104104fffffff) * 0x10000000000000000 + 0xfffc0fffffffffff) * 0x10000000000000000 + 0xffc003ffc0fff03f) * 0x10000000000000000 + 0xfefeccccfefecccc) * 0x10000000000000000 + 0xfefeccccfefecccc)
  | 86 => ((((((0x10410410410410 * 0x10000000000000000 + 0x4104104104104104) * 0x10000000000000000 + 0x104104104fffffff) * 0x10000000000000000 + 0xfffc0fffffffffff) * 0x10000000000000000 + 0xfffffffffffff03f) * 0x10000000000000000 + 0xfefefeccfefefecc) * 0x10000000000000000 + 0xfefefeccfefefecc)
  | 87 => ((((((0x10410410410410 * 0x10000000000000000 + 0x4104104104104104) * 0x10000000000000000 + 0x104104104fffffff) * 0x10000000000000000 + 0xfffff00000000003) * 0x10000000000000000 + 0xffc003ffc003f000) * 0x10000000000000000 + 0xff00cc44ff00cc44) * 0x10000000000000000 + 0xff00cc44ff00cc44)
  | 88 => ((((((0x10410410410410 * 0x10000000000000000 + 0x4104104104104104) * 0x10000000000000000 + 0x104104104fffffff) * 0x10000000000000000 + 0xffffffff000fff00) * 0x10000000000000000 + 0x000000000003f000) * 0x10000000000000000 + 0xffcc0044ffcc0044) * 0x10000000000000000 + 0xffcc0044ffcc0044)
  | 89 => ((((((0x10410410410410 * 0x10000000000000000 + 0x4104104104104104) * 0x10000000000000000 + 0x104104104fffffff) * 0x10000000000000000 + 0xffffffff000fff03) * 0x10000000000000000 + 0xffff03fffffff03f) * 0x10000000000000000 + 0xffcceeccffcceecc) * 0x10000000000000000 + 0xffcceeccffcceecc)
  | 90 => ((((((0x10410410410410 * 0x10000000000000000 + 0x4104104104104104) * 0x10000000000000000 + 0x104104104fffffff) * 0x10000000000000000 + 0xfffffffffc0fffff) * 0x10000000000000000 + 0xffc003ffc0fff03f) * 0x10000000000000000 + 0xffeeccccffeecccc) * 0x10000000000000000 + 0xffeeccccffeecccc)
  | 91 => ((((((0x10410410410410 * 0x10000000000000000 + 0x4104104104104104) * 0x10000000000000000 + 0x104104104fffffff) * 0x10000000000000000 + 0xfffffffffc0fffff) * 0x10000000000000000 + 0xffffffffc0ffffff) * 0x10000000000000000 + 0xffeefcecffeefcec) * 0x10000000000000000 + 0xffeefcecffeefcec)
  | 92 => ((((((0x10410410410410 * 0x10000000000000000 + 0x4104104104104104) * 0x10000000000000000 + 0x104104104fffffff) * 0x10000000000000000 + 0xffffffffffffff03) * 0x10000000000000000 + 0xffff03ffffffffff) * 0x10000000000000000 + 0xfffceeecfffceeec) * 0x10000000000000000 + 0xfffceeecfffceeec)
  | 93 => ((((((0x18618618618618 * 0x10000000000000000 + 0x6186186186186186) * 0x10000000000000000 + 0x1861861860000000) * 0x10000000000000000 + 0x0000000000000000) * 0x10000000000000000 + 0x000000000000003f) * 0x10000000000000000 + 0x0000000e0000000e) * 0x10000000000000000 + 0x0000000e0000000e)
  | 94 => ((((((0x18618618618618 * 0x10000000000000000 + 0x6186186186186186) * 0x10000000000000000 + 0x1861861860000000) * 0x10000000000000000 + 0x0000000000000000) * 0x10000000000000000 + 0x0000000000ffffff) * 0x10000000000000000 + 0x000000ee000000ee) * 0x10000000000000000 + 0x000000ee000000ee)
  | 95 => ((((((0x18618618618618 * 0x10000000000000000 + 0x6186186186186186) * 0x10000000000000000 + 0x1861861860000000) * 0x10000000000000000 + 0x0000000000000000) * 0x10000000000000000 + 0x000003ffff00003f) * 0x10000000000000000 + 0x00000e0e00000e0e) * 0x10000000000000000 + 0x00000e0e00000e0e)
  | 96 => ((((((0x18618618618618 * 0x10000000000000000 + 0x6186186186186186) * 0x10000000000000000 + 0x1861861860000000) * 0x10000000000000000 + 0x0000000000000003) * 0x10000000000000000 + 0xffff03ffffffffff) * 0x10000000000000000 + 0x0000eeee0000eeee) * 0x10000000000000000 + 0x0000eeee0000eeee)
  | 97 => ((((((0x18618618618618 * 0x10000000000000000 + 0x6186186186186186) * 0x10000000000000000 + 0x1861861860000000) * 0x10000000000000000 + 0x00000000000ffffc) * 0x10000000000000000 + 0x000000000000003f) * 0x10000000000000000 + 0x000e000e000e000e) * 0x10000000000000000 + 0x000e000e000e000e)
  | 98 => ((((((0x18618618618618 * 0x10000000000000000 + 0x6186186186186186) * 0x10000000000000000 + 0x1861861860000000) * 0x10000000000000000 + 0x00000000fc0000fc) * 0x10000000000000000 + 0x0fc0000fc003ffc0) * 0x10000000000000000 + 0x0022446600224466) * 0x10000000000000000 + 0x0022446600224466)
  | 99 => ((((((0x18618618618618 * 0x10000000000000000 + 0x6186186186186186) * 0x10000000000000000 + 0x1861861860000000) * 0x10000000000000000 + 0x0000003f00003f00) * 0x10000000000000000 + 0x003f00003f03ffc0) * 0x10000000000000000 + 0x0044226600442266) * 0x10000000000000000 + 0x0044226600442266)
  | 100 => ((((((0x18618618618618 * 0x10000000000000000 + 0x6186186186186186) * 0x10000000000000000 + 0x1861861860000000) * 0x10000000000000000 + 0x00000ffffc0ffffc) * 0x10000000000000000 + 0x0000000000ffffff) * 0x10000000000000000 + 0x00ee00ee00ee00ee) * 0x10000000000000000 + 0x00ee00ee00ee00ee)
  | 101 => ((((((0x18618618618618 * 0x10000000000000000 + 0x6186186186186186) * 0x10000000000000000 + 0x1861861860000000) * 0x10000000000000000 + 0x00fc0000000000fc) * 0x10000000000000000 + 0x0fc0000fff03f000) * 0x10000000000000000 + 0x0202464602024646) * 0x10000000000000000 + 0x0202464602024646)
  | 102 => ((((((0x18618618618618 * 0x10000000000000000 + 0x6186186186186186) * 0x10000000000000000 + 0x1861861860000000) * 0x10000000000000000 + 0x00fc003f00003ffc) * 0x10000000000000000 + 0x000000003f03f000) * 0x10000000000000000 + 0x0246024602460246) * 0x10000000000000000 + 0x0246024602460246)
  | 103 => ((((((0x18618618618618 * 0x10000000000000000 + 0x6186186186186186) * 0x10000000000000000 + 0x1861861860000000) * 0x10000000000000000 + 0x3f00000000003f00) * 0x10000000000000000 + 0x003f000fff000fc0) * 0x10000000000000000 + 0x0404262604042626) * 0x10000000000000000 + 0x0404262604042626)
  | 104 => ((((((0x18618618618618 * 0x10000000000000000 + 0x6186186186186186) * 0x10000000000000000 + 0x1861861860000000) * 0x10000000000000000 + 0x3f000000fc003ffc) * 0x10000000000000000 + 0x0000000fc0000fc0) * 0x10000000000000000 + 0x0426042604260426) * 0x10000000000000000 + 0x0426042604260426)
  | 105 => ((((((0x18618618618618 * 0x10000000000000000 + 0x6186186186186186) * 0x10000000000000000 + 0x186186186000000f) * 0x10000000000000000 + 0xfffc0000000ffffc) * 0x10000000000000000 + 0x000003ffff00003f) * 0x10000000000000000 + 0x0e0e0e0e0e0e0e0e) * 0x10000000000000000 + 0x0e0e0e0e0e0e0e0e)
  | 106 => ((((((0x18618618618618 * 0x10000000000000000 + 0x6186186186186186) * 0x10000000000000000 + 0x186186186ffffc00) * 0x10000000000000000 + 0x00000ffffc000003) * 0x10000000000000000 + 0xffff000000ffffff) * 0x10000000000000000 + 0xe0e0e0eee0e0e0ee) * 0x10000000000000000 + 0xe0e0e0eee0e0e0ee)
  | 107 => ((((((0x18618618618618 * 0x10000000000000000 + 0x6186186186186186) * 0x10000000000000000 + 0x186186186ffffc0f) * 0x10000000000000000 + 0xfffc000000000003) * 0x10000000000000000 + 0xffff03ffff00003f) * 0x10000000000000000 + 0xee00ee0eee00ee0e) * 0x10000000000000000 + 0xee00ee0eee00ee0e)
  | 108 => ((((((0x18618618618618 * 0x10000000000000000 + 0x6186186186186186) * 0x10000000000000000 + 0x186186186ffffc0f) * 0x10000000000000000 + 0xfffc0ffffc0ffffc) * 0x10000000000000000 + 0x000000000000003f) * 0x10000000000000000 + 0xeeee000eeeee000e) * 0x10000000000000000 + 0xeeee000eeeee000e)
  | 109 => ((((((0x18618618618618 * 0x10000000000000000 + 0x6186186186186186) * 0x10000000000000000 + 0x186186186ffffc0f) * 0x10000000000000000 + 0xfffc0ffffc0fffff) * 0x10000000000000000 + 0xffff03ffffffffff) * 0x10000000000000000 + 0xeeeeeeeeeeeeeeee) * 0x10000000000000000 + 0xeeeeeeeeeeeeeeee)
  | 110 => ((((((0x20820820820820 * 0x10000000000000000 + 0x8208208208208208) * 0x10000000000000000 + 0x2082082080000000) * 0x10000000000000000 + 0x00000000fff00000) * 0x10000000000000000 + 0x0fc0fc000003ffc0) * 0x10000000000000000 + 0x0030507000305070) * 0x10000000000000000 + 0x0030507000305070)
  | 111 => ((((((0x20820820820820 * 0x10000000000000000 + 0x8208208208208208) * 0x10000000000000000 + 0x2082082080000000) * 0x10000000000000000 + 0x0000003f03f00000) * 0x10000000000000000 + 0x003ffc000003ffc0) * 0x10000000000000000 + 0x0050307000503070) * 0x10000000000000000 + 0x0050307000503070)
  | 112 => ((((((0x20820820820820 * 0x10000000000000000 + 0x8208208208208208) * 0x10000000000000000 + 0x20820820800003f0) * 0x10000000000000000 + 0x0000000003f00000) * 0x10000000000000000 + 0x0000fc0000ffffc0) * 0x10000000000000000 + 0x101010f0101010f0) * 0x10000000000000000 + 0x101010f0101010f0)
  | 113 => ((((((0x20820820820820 * 0x10000000000000000 + 0x8208208208208208) * 0x10000000000000000 + 0x20820820800003f0) * 0x10000000000000000 + 0x0000000003f00003) * 0x10000000000000000 + 0xfffffff000ffffff) * 0x10000000000000000 + 0x1010f8f81010f8f8) * 0x10000000000000000 + 0x1010f8f81010f8f8)
  | 114 => ((((((0x20820820820820 * 0x10000000000000000 + 0x8208208208208208) * 0x10000000000000000 + 0x20820820800003f0) * 0x10000000000000000 + 0x00000fffffffc000) * 0x10000000000000000 + 0x0000fc0000ffffff) * 0x10000000000000000 + 0x10f810f810f810f8) * 0x10000000000000000 + 0x10f810f810f810f8)
  | 115 => ((((((0x20820820820820 * 0x10000000000000000 + 0x8208208208208208) * 0x10000000000000000 + 0x208208208fc0fc0f) * 0x10000000000000000 + 0xc0000fc0fc0fc003) * 0x10000000000000000 + 0xf03ffff000fc0fff) * 0x10000000000000000 + 0xa8a8b8b8a8a8b8b8) * 0x10000000000000000 + 0xa8a8b8b8a8a8b8b8)
  | 116 => ((((((0x20820820820820 * 0x10000000000000000 + 0x8208208208208208) * 0x10000000000000000 + 0x208208208fc0fc0f) * 0x10000000000000000 + 0xc0000fc0ffffc003) * 0x10000000000000000 + 0xf03f03f000fc0fff) * 0x10000000000000000 + 0xa8b8a8b8a8b8a8b8) * 0x10000000000000000 + 0xa8b8a8b8a8b8a8b8)
  | 117 => ((((((0x20820820820820 * 0x10000000000000000 + 0x8208208208208208) * 0x10000000000000000 + 0x208208208fc0fc0f) * 0x10000000000000000 + 0xc0fc0fc0fc0fc0ff) * 0x10000000000000000 + 0xf03ffff000fc0fff) * 0x10000000000000000 + 0xaaaab8b8aaaab8b8) * 0x10000000000000000 + 0xaaaab8b8aaaab8b8)
  | 118 => ((((((0x20820820820820 * 0x10000000000000000 + 0x8208208208208208) * 0x10000000000000000 + 0x208208208fc0fc0f) * 0x10000000000000000 + 0xc0fc0fc0ffffc003) * 0x10000000000000000 + 0xf03f03f03ffc0fff) * 0x10000000000000000 + 0xaab8aab8aab8aab8) * 0x10000000000000000 + 0xaab8aab8aab8aab8)
  | 119 => ((((((0x20820820820820 * 0x10000000000000000 + 0x8208208208208208) * 0x10000000000000000 + 0x208208208fff000f) * 0x10000000000000000 + 0xc0000fff000fc003) * 0x10000000000000000 + 0xffc0fff000fff03f) * 0x10000000000000000 + 0xc8c8d8d8c8c8d8d8) * 0x10000000000000000 + 0xc8c8d8d8c8c8d8d8)
  | 120 => ((((((0x20820820820820 * 0x10000000000000000 + 0x8208208208208208) * 0x10000000000000000 + 0x208208208fff000f) * 0x10000000000000000 + 0xc0000fff03ffc003) * 0x10000000000000000 + 0xffc003f000fff03f) * 0x10000000000000000 + 0xc8d8c8d8c8d8c8d8) * 0x10000000000000000 + 0xc8d8c8d8c8d8c8d8)
  | 121 => ((((((0x20820820820820 * 0x10000000000000000 + 0x8208208208208208) * 0x10000000000000000 + 0x208208208fff000f) * 0x10000000000000000 + 0xff000fff000fff03) * 0x10000000000000000 + 0xffc0fff000fff03f) * 0x10000000000000000 + 0xccccd8d8ccccd8d8) * 0x10000000000000000 + 0xccccd8d8ccccd8d8)
  | 122 => ((((((0x20820820820820 * 0x10000000000000000 + 0x8208208208208208) * 0x10000000000000000 + 0x208208208fff000f) * 0x10000000000000000 + 0xff000fff03ffc003) * 0x10000000000000000 + 0xffc003ffc0fff03f) * 0x10000000000000000 + 0xccd8ccd8ccd8ccd8) * 0x10000000000000000 + 0xccd8ccd8ccd8ccd8)
  | 123 => ((((((0x20820820820820 * 0x10000000000000000 + 0x8208208208208208) * 0x10000000000000000 + 0x208208208ffffff0) * 0x10000000000000000 + 0x00000ffffff00003) * 0x10000000000000000 + 0xfffffc0000ffffc0) * 0x10000000000000000 + 0xf0f0f0f0f0f0f0f0) * 0x10000000000000000 + 0xf0f0f0f0f0f0f0f0)
  | 124 => ((((((0x20820820820820 * 0x10000000000000000 + 0x8208208208208208) * 0x10000000000000000 + 0x208208208fffffff) * 0x10000000000000000 + 0xc0fc000003f00003) * 0x10000000000000000 + 0xfffffff03f000000) * 0x10000000000000000 + 0xfa10fa10fa10fa10) * 0x10000000000000000 + 0xfa10fa10fa10fa10)
  | 125 => ((((((0x20820820820820 * 0x10000000000000000 + 0x8208208208208208) * 0x10000000000000000 + 0x208208208fffffff) * 0x10000000000000000 + 0xc0fc0fffffffc003) * 0x10000000000000000 + 0xfffffff03fffffff) * 0x10000000000000000 + 0xfaf8faf8faf8faf8) * 0x10000000000000000 + 0xfaf8faf8faf8faf8)
  | 126 => ((((((0x20820820820820 * 0x10000000000000000 + 0x8208208208208208) * 0x10000000000000000 + 0x208208208fffffff) * 0x10000000000000000 + 0xc0fc0fffffffc0fc) * 0x10000000000000000 + 0x0000fc0000000000) * 0x10000000000000000 + 0xfafa1010fafa1010) * 0x10000000000000000 + 0xfafa1010fafa1010)
  | 127 => ((((((0x20820820820820 * 0x10000000000000000 + 0x8208208208208208) * 0x10000000000000000 + 0x208208208fffffff) * 0x10000000000000000 + 0xc0fc0fffffffc0ff) * 0x10000000000000000 + 0xfffffff000ffffff) * 0x10000000000000000 + 0xfafaf8f8fafaf8f8) * 0x10000000000000000 + 0xfafaf8f8fafaf8f8)
  | 128 => ((((((0x20820820820820 * 0x10000000000000000 + 0x8208208208208208) * 0x10000000000000000 + 0x208208208fffffff) * 0x10000000000000000 + 0xff00000003f00003) * 0x10000000000000000 + 0xffffffffc0000000) * 0x10000000000000000 + 0xfc10fc10fc10fc10) * 0x10000000000000000 + 0xfc10fc10fc10fc10)
  | 129 => ((((((0x20820820820820 * 0x10000000000000000 + 0x8208208208208208) * 0x10000000000000000 + 0x208208208fffffff) * 0x10000000000000000 + 0xff000fffffffc003) * 0x10000000000000000 + 0xffffffffc0ffffff) * 0x10000000000000000 + 0xfcf8fcf8fcf8fcf8) * 0x10000000000000000 + 0xfcf8fcf8fcf8fcf8)
  | 130 => ((((((0x20820820820820 * 0x10000000000000000 + 0x8208208208208208) * 0x10000000000000000 + 0x208208208fffffff) * 0x10000000000000000 + 0xff000fffffffff00) * 0x10000000000000000 + 0x0000fc0000000000) * 0x10000000000000000 + 0xfcfc1010fcfc1010) * 0x10000000000000000 + 0xfcfc1010fcfc1010)
  | 131 => ((((((0x20820820820820 * 0x10000000000000000 + 0x8208208208208208) * 0x10000000000000000 + 0x208208208fffffff) * 0x10000000000000000 + 0xff000fffffffff03) * 0x10000000000000000 + 0xfffffff000ffffff) * 0x10000000000000000 + 0xfcfcf8f8fcfcf8f8) * 0x10000000000000000 + 0xfcfcf8f8fcfcf8f8)
  | 132 => ((((((0x20820820820820 * 0x10000000000000000 + 0x8208208208208208) * 0x10000000000000000 + 0x208208208fffffff) * 0x10000000000000000 + 0xfffc000003f00003) * 0x10000000000000000 + 0xffffffffff000000) * 0x10000000000000000 + 0xfe10fe10fe10fe10) * 0x10000000000000000 + 0xfe10fe10fe10fe10)
  | 133 => ((((((0x20820820820820 * 0x10000000000000000 + 0x8208208208208208) * 0x10000000000000000 + 0x208208208fffffff) * 0x10000000000000000 + 0xfffc0ffffff00003) * 0x10000000000000000 + 0xffffffffffffffc0) * 0x10000000000000000 + 0xfef0fef0fef0fef0) * 0x10000000000000000 + 0xfef0fef0fef0fef0)
  | 134 => ((((((0x20820820820820 * 0x10000000000000000 + 0x8208208208208208) * 0x10000000000000000 + 0x208208208fffffff) * 0x10000000000000000 + 0xfffc0ffffffffffc) * 0x10000000000000000 + 0x0000fc0000000000) * 0x10000000000000000 + 0xfefe1010fefe1010) * 0x10000000000000000 + 0xfefe1010fefe1010)
  | 135 => ((((((0x20820820820820 * 0x10000000000000000 + 0x8208208208208208) * 0x10000000000000000 + 0x208208208fffffff) * 0x10000000000000000 + 0xfffc0fffffffffff) * 0x10000000000000000 + 0xfffffc0000ffffc0) * 0x10000000000000000 + 0xfefef0f0fefef0f0) * 0x10000000000000000 + 0xfefef0f0fefef0f0)
  | 136 => ((((((0x20820820820820 * 0x10000000000000000 + 0x8208208208208208) * 0x10000000000000000 + 0x208208208fffffff) * 0x10000000000000000 + 0xfffc0fffffffffff) * 0x10000000000000000 + 0xffffffffffffffc0) * 0x10000000000000000 + 0xfefefef0fefefef0) * 0x10000000000000000 + 0xfefefef0fefefef0)
  | 137 => ((((((0x20820820820820 * 0x10000000000000000 + 0x8208208208208208) * 0x10000000000000000 + 0x208208208fffffff) * 0x10000000000000000 + 0xffffffffffffc0ff) * 0x10000000000000000 + 0xffffffffc0ffffff) * 0x10000000000000000 + 0xfffafcf8fffafcf8) * 0x10000000000000000 + 0xfffafcf8fffafcf8)
  | 138 => ((((((0x20820820820820 * 0x10000000000000000 + 0x8208208208208208) * 0x10000000000000000 + 0x208208208fffffff) * 0x10000000000000000 + 0xffffffffffffff03) * 0x10000000000000000 + 0xfffffff03fffffff) * 0x10000000000000000 + 0xfffcfaf8fffcfaf8) * 0x10000000000000000 + 0xfffcfaf8fffcfaf8)
  | 139 => ((((((0x28a28a28a28a28 * 0x10000000000000000 + 0xa28a28a28a28a28a) * 0x10000000000000000 + 0x28a28a28a0000000) * 0x10000000000000000 + 0x0000000000000000) * 0x10000000000000000 + 0x0000000000ffffff) * 0x10000000000000000 + 0x000000fa000000fa) * 0x10000000000000000 + 0x000000fa000000fa)
  | 140 => ((((((0x28a28a28a28a28 * 0x10000000000000000 + 0xa28a28a28a28a28a) * 0x10000000000000000 + 0x28a28a28a0000000) * 0x10000000000000000 + 0x0000000000000000) * 0x10000000000000000 + 0x003ffc003f000fc0) * 0x10000000000000000 + 0x0000323200003232) * 0x10000000000000000 + 0x0000323200003232)
  | 141 => ((((((0x28a28a28a28a28 * 0x10000000000000000 + 0xa28a28a28a28a28a) * 0x10000000000000000 + 0x28a28a28a0000000) * 0x10000000000000000 + 0x0000000000000003) * 0x10000000000000000 + 0xfffffc003fffffc0) * 0x10000000000000000 + 0x0000f2f20000f2f2) * 0x10000000000000000 + 0x0000f2f20000f2f2)
  | 142 => ((((((0x28a28a28a28a28 * 0x10000000000000000 + 0xa28a28a28a28a28a) * 0x10000000000000000 + 0x28a28a28a0000000) * 0x10000000000000000 + 0x0000000000000003) * 0x10000000000000000 + 0xfffffff03fffffff) * 0x10000000000000000 + 0x0000fafa0000fafa) * 0x10000000000000000 + 0x0000fafa0000fafa)
  | 143 => ((((((0x28a28a28a28a28 * 0x10000000000000000 + 0xa28a28a28a28a28a) * 0x10000000000000000 + 0x28a28a28a0000000) * 0x10000000000000000 + 0x00000000fff000fc) * 0x10000000000000000 + 0x0000000000000fc0) * 0x10000000000000000 + 0x0032003200320032) * 0x10000000000000000 + 0x0032003200320032)
  | 144 => ((((((0x28a28a28a28a28 * 0x10000000000000000 + 0xa28a28a28a28a28a) * 0x10000000000000000 + 0x28a28a28a0000000) * 0x10000000000000000 + 0x00000ffffff000fc) * 0x10000000000000000 + 0x0000000000ffffc0) * 0x10000000000000000 + 0x00f200f200f200f2) * 0x10000000000000000 + 0x00f200f200f200f2)
  | 145 => ((((((0x28a28a28a28a28 * 0x10000000000000000 + 0xa28a28a28a28a28a) * 0x10000000000000000 + 0x28a28a28a0000000) * 0x10000000000000000 + 0x00000fffffffc0fc) * 0x10000000000000000 + 0x0000000000ffffff) * 0x10000000000000000 + 0x00fa00fa00fa00fa) * 0x10000000000000000 + 0x00fa00fa00fa00fa)
  | 146 => ((((((0x28a28a28a28a28 * 0x10000000000000000 + 0xa28a28a28a28a28a) * 0x10000000000000000 + 0x28a28a28a00003f0) * 0x10000000000000000 + 0x0000000003f00000) * 0x10000000000000000 + 0x0000fff03f00003f) * 0x10000000000000000 + 0x10101a1a10101a1a) * 0x10000000000000000 + 0x10101a1a10101a1a)
  | 147 => ((((((0x28a28a28a28a28 * 0x10000000000000000 + 0xa28a28a28a28a28a) * 0x10000000000000000 + 0x28a28a28a00003f0) * 0x10000000000000000 + 0x0000000003ffc0fc) * 0x10000000000000000 + 0x0000fc000000003f) * 0x10000000000000000 + 0x101a101a101a101a) * 0x10000000000000000 + 0x101a101a101a101a)
  | 148 => ((((((0x28a28a28a28a28 * 0x10000000000000000 + 0xa28a28a28a28a28a) * 0x10000000000000000 + 0x28a28a28a000fff0) * 0x10000000000000000 + 0x00000000fff00000) * 0x10000000000000000 + 0x003ffc003f000fc0) * 0x10000000000000000 + 0x3030323230303232) * 0x10000000000000000 + 0x3030323230303232)
  | 149 => ((((((0x28a28a28a28a28 * 0x10000000000000000 + 0xa28a28a28a28a28a) * 0x10000000000000000 + 0x28a28a28a000fff0) * 0x10000000000000000 + 0x00000000fff000fc) * 0x10000000000000000 + 0x003ffc0000000fc0) * 0x10000000000000000 + 0x3032303230323032) * 0x10000000000000000 + 0x3032303230323032)
  | 150 => ((((((0x28a28a28a28a28 * 0x10000000000000000 + 0xa28a28a28a28a28a) * 0x10000000000000000 + 0x28a28a28a000fff0) * 0x10000000000000000 + 0x00fc0000fff000fc) * 0x10000000000000000 + 0x003ffc003f000fc0) * 0x10000000000000000 + 0x3232323232323232) * 0x10000000000000000 + 0x3232323232323232)
  | 151 => ((((((0x28a28a28a28a28 * 0x10000000000000000 + 0xa28a28a28a28a28a) * 0x10000000000000000 + 0x28a28a28afffffff) * 0x10000000000000000 + 0xc0fc0fffffffc0ff) * 0x10000000000000000 + 0xfffffff03fffffff) * 0x10000000000000000 + 0xfafafafafafafafa) * 0x10000000000000000 + 0xfafafafafafafafa)
  | 152 => ((((((0x30c30c30c30c30 * 0x10000000000000000 + 0xc30c30c30c30c30c) * 0x10000000000000000 + 0x30c30c30c0000000) * 0x10000000000000000 + 0x0000000000000000) * 0x10000000000000000 + 0x0000000000ffffff) * 0x10000000000000000 + 0x000000fc000000fc) * 0x10000000000000000 + 0x000000fc000000fc)
  | 153 => ((((((0x30c30c30c30c30 * 0x10000000000000000 + 0xc30c30c30c30c30c) * 0x10000000000000000 + 0x30c30c30c0000000) * 0x10000000000000000 + 0x0000000000000000) * 0x10000000000000000 + 0x0fc0fc0fc003f000) * 0x10000000000000000 + 0x0000545400005454) * 0x10000000000000000 + 0x0000545400005454)
  | 154 => ((((((0x30c30c30c30c30 * 0x10000000000000000 + 0xc30c30c30c30c30c) * 0x10000000000000000 + 0x30c30c30c0000000) * 0x10000000000000000 + 0x0000000000000003) * 0x10000000000000000 + 0xfffffc0fc0ffffc0) * 0x10000000000000000 + 0x0000f4f40000f4f4) * 0x10000000000000000 + 0x0000f4f40000f4f4)
  | 155 => ((((((0x30c30c30c30c30 * 0x10000000000000000 + 0xc30c30c30c30c30c) * 0x10000000000000000 + 0x30c30c30c0000000) * 0x10000000000000000 + 0x0000000000000003) * 0x10000000000000000 + 0xffffffffc0ffffff) * 0x10000000000000000 + 0x0000fcfc0000fcfc) * 0x10000000000000000 + 0x0000fcfc0000fcfc)
  | 156 => ((((((0x30c30c30c30c30 * 0x10000000000000000 + 0xc30c30c30c30c30c) * 0x10000000000000000 + 0x30c30c30c0000000) * 0x10000000000000000 + 0x0000003f03f03f00) * 0x10000000000000000 + 0x000000000003f000) * 0x10000000000000000 + 0x0054005400540054) * 0x10000000000000000 + 0x0054005400540054)
  | 157 => ((((((0x30c30c30c30c30 * 0x10000000000000000 + 0xc30c30c30c30c30c) * 0x10000000000000000 + 0x30c30c30c0000000) * 0x10000000000000000 + 0x00000ffffff03f00) * 0x10000000000000000 + 0x0000000000ffffc0) * 0x10000000000000000 + 0x00f400f400f400f4) * 0x10000000000000000 + 0x00f400f400f400f4)
  | 158 => ((((((0x30c30c30c30c30 * 0x10000000000000000 + 0xc30c30c30c30c30c) * 0x10000000000000000 + 0x30c30c30c0000000) * 0x10000000000000000 + 0x00000fffffffff00) * 0x10000000000000000 + 0x0000000000ffffff) * 0x10000000000000000 + 0x00fc00fc00fc00fc) * 0x10000000000000000 + 0x00fc00fc00fc00fc)
  | 159 => ((((((0x30c30c30c30c30 * 0x10000000000000000 + 0xc30c30c30c30c30c) * 0x10000000000000000 + 0x30c30c30c00003f0) * 0x10000000000000000 + 0x0000000003f00000) * 0x10000000000000000 + 0x0000ffffc000003f) * 0x10000000000000000 + 0x10101c1c10101c1c) * 0x10000000000000000 + 0x10101c1c10101c1c)
  | 160 => ((((((0x30c30c30c30c30 * 0x10000000000000000 + 0xc30c30c30c30c30c) * 0x10000000000000000 + 0x30c30c30c00003f0) * 0x10000000000000000 + 0x0000000003ffff00) * 0x10000000000000000 + 0x0000fc000000003f) * 0x10000000000000000 + 0x101c101c101c101c) * 0x10000000000000000 + 0x101c101c101c101c)
  | 161 => ((((((0x30c30c30c30c30 * 0x10000000000000000 + 0xc30c30c30c30c30c) * 0x10000000000000000 + 0x30c30c30c03f03f0) * 0x10000000000000000 + 0x0000003f03f00000) * 0x10000000000000000 + 0x0fc0fc0fc003f000) * 0x10000000000000000 + 0x5050545450505454) * 0x10000000000000000 + 0x5050545450505454)
  | 162 => ((((((0x30c30c30c30c30 * 0x10000000000000000 + 0xc30c30c30c30c30c) * 0x10000000000000000 + 0x30c30c30c03f03f0) * 0x10000000000000000 + 0x0000003f03f03f00) * 0x10000000000000000 + 0x0fc0fc000003f000) * 0x10000000000000000 + 0x5054505450545054) * 0x10000000000000000 + 0x5054505450545054)
  | 163 => ((((((0x30c30c30c30c30 * 0x10000000000000000 + 0xc30c30c30c30c30c) * 0x10000000000000000 + 0x30c30c30c03f03f0) * 0x10000000000000000 + 0x3f00003f03f03f00) * 0x10000000000000000 + 0x0fc0fc0fc003f000) * 0x10000000000000000 + 0x5454545454545454) * 0x10000000000000000 + 0x5454545454545454)
  | 164 => ((((((0x30c30c30c30c30 * 0x10000000000000000 + 0xc30c30c30c30c30c) * 0x10000000000000000 + 0x30c30c30cfffffff) * 0x10000000000000000 + 0xff000fffffffff03) * 0x10000000000000000 + 0xffffffffc0ffffff) * 0x10000000000000000 + 0xfcfcfcfcfcfcfcfc) * 0x10000000000000000 + 0xfcfcfcfcfcfcfcfc)
  | 165 => ((((((0x38e38e38e38e38 * 0x10000000000000000 + 0xe38e38e38e38e38e) * 0x10000000000000000 + 0x38e38e38e0000000) * 0x10000000000000000 + 0x0000000000000000) * 0x10000000000000000 + 0x0000000000ffffff) * 0x10000000000000000 + 0x000000fe000000fe) * 0x10000000000000000 + 0x000000fe000000fe)
  | 166 => ((((((0x38e38e38e38e38 * 0x10000000000000000 + 0xe38e38e38e38e38e) * 0x10000000000000000 + 0x38e38e38e0000000) * 0x10000000000000000 + 0x0000000000000003) * 0x10000000000000000 + 0xfffffc0000ffffff) * 0x10000000000000000 + 0x0000f0fe0000f0fe) * 0x10000000000000000 + 0x0000f0fe0000f0fe)
  | 167 => ((((((0x38e38e38e38e38 * 0x10000000000000000 + 0xe38e38e38e38e38e) * 0x10000000000000000 + 0x38e38e38e0000000) * 0x10000000000000000 + 0x0000000000000003) * 0x10000000000000000 + 0xffffffffffffffff) * 0x10000000000000000 + 0x0000fefe0000fefe) * 0x10000000000000000 + 0x0000fefe0000fefe)
  | 168 => ((((((0x38e38e38e38e38 * 0x10000000000000000 + 0xe38e38e38e38e38e) * 0x10000000000000000 + 0x38e38e38e0000000) * 0x10000000000000000 + 0x00000ffffff00000) * 0x10000000000000000 + 0x0000000000ffffff) * 0x10000000000000000 + 0x00f000fe00f000fe) * 0x10000000000000000 + 0x00f000fe00f000fe)
  | 169 => ((((((0x38e38e38e38e38 * 0x10000000000000000 + 0xe38e38e38e38e38e) * 0x10000000000000000 + 0x38e38e38e0000000) * 0x10000000000000000 + 0x00000ffffffffffc) * 0x10000000000000000 + 0x0000000000ffffff) * 0x10000000000000000 + 0x00fe00fe00fe00fe) * 0x10000000000000000 + 0x00fe00fe00fe00fe)
  | 170 => ((((((0x38e38e38e38e38 * 0x10000000000000000 + 0xe38e38e38e38e38e) * 0x10000000000000000 + 0x38e38e38e00003f0) * 0x10000000000000000 + 0x0000000003f00000) * 0x10000000000000000 + 0x0000ffffff00003f) * 0x10000000000000000 + 0x10101e1e10101e1e) * 0x10000000000000000 + 0x10101e1e10101e1e)
  | 171 => ((((((0x38e38e38e38e38 * 0x10000000000000000 + 0xe38e38e38e38e38e) * 0x10000000000000000 + 0x38e38e38e00003f0) * 0x10000000000000000 + 0x0000000003fffffc) * 0x10000000000000000 + 0x0000fc000000003f) * 0x10000000000000000 + 0x101e101e101e101e) * 0x10000000000000000 + 0x101e101e101e101e)
  | 172 => ((((((0x38e38e38e38e38 * 0x10000000000000000 + 0xe38e38e38e38e38e) * 0x10000000000000000 + 0x38e38e38effffff0) * 0x10000000000000000 + 0x00000ffffff00003) * 0x10000000000000000 + 0xfffffc0000ffffff) * 0x10000000000000000 + 0xf0f0f0fef0f0f0fe) * 0x10000000000000000 + 0xf0f0f0fef0f0f0fe)
  | 173 => ((((((0x38e38e38e38e38 * 0x10000000000000000 + 0xe38e38e38e38e38e) * 0x10000000000000000 + 0x38e38e38effffff0) * 0x10000000000000000 + 0x00000ffffff00003) * 0x10000000000000000 + 0xffffffffffffffff) * 0x10000000000000000 + 0xf0f0fefef0f0fefe) * 0x10000000000000000 + 0xf0f0fefef0f0fefe)
  | 174 => ((((((0x38e38e38e38e38 * 0x10000000000000000 + 0xe38e38e38e38e38e) * 0x10000000000000000 + 0x38e38e38effffff0) * 0x10000000000000000 + 0x00000fffffffffff) * 0x10000000000000000 + 0xfffffc0000ffffff) * 0x10000000000000000 + 0xf0fef0fef0fef0fe) * 0x10000000000000000 + 0xf0fef0fef0fef0fe)
  | 175 => ((((((0x38e38e38e38e38 * 0x10000000000000000 + 0xe38e38e38e38e38e) * 0x10000000000000000 + 0x38e38e38efffffff) * 0x10000000000000000 + 0xfffc0fffffffffff) * 0x10000000000000000 + 0xffffffffffffffff) * 0x10000000000000000 + 0xfefefefefefefefe) * 0x10000000000000000 + 0xfefefefefefefefe)
  | 176 => ((((((0x41041041041041 * 0x10000000000000000 + 0x0410410410410410) * 0x10000000000000000 + 0x4104104100000000) * 0x10000000000000000 + 0x00fff00000000000) * 0x10000000000000000 + 0x0fc0fc0fff000000) * 0x10000000000000000 + 0x0300570003005700) * 0x10000000000000000 + 0x0300570003005700)
  | 177 => ((((((0x41041041041041 * 0x10000000000000000 + 0x0410410410410410) * 0x10000000000000000 + 0x4104104100000000) * 0x10000000000000000 + 0x3f03f00000000000) * 0x10000000000000000 + 0x003ffc0fff000000) * 0x10000000000000000 + 0x0500370005003700) * 0x10000000000000000 + 0x0500370005003700)
  | 178 => ((((((0x41041041041041 * 0x10000000000000000 + 0x0410410410410410) * 0x10000000000000000 + 0x41041041000003f0) * 0x10000000000000000 + 0x0003f00000000000) * 0x10000000000000000 + 0x0000ffffff000000) * 0x10000000000000000 + 0x11001f0011001f00) * 0x10000000000000000 + 0x11001f0011001f00)
  | 179 => ((((((0x41041041041041 * 0x10000000000000000 + 0x0410410410410410) * 0x10000000000000000 + 0x41041041000003f0) * 0x10000000000000000 + 0x0003f00000000003) * 0x10000000000000000 + 0xfffffffffffc003f) * 0x10000000000000000 + 0x1100ff881100ff88) * 0x10000000000000000 + 0x1100ff881100ff88)
  | 180 => ((((((0x41041041041041 * 0x10000000000000000 + 0x0410410410410410) * 0x10000000000000000 + 0x41041041000003ff) * 0x10000000000000000 + 0xfffff000000fc000) * 0x10000000000000000 + 0x0000ffffff00003f) * 0x10000000000000000 + 0x1f081f081f081f08) * 0x10000000000000000 + 0x1f081f081f081f08)
  | 181 => ((((((0x41041041041041 * 0x10000000000000000 + 0x0410410410410410) * 0x10000000000000000 + 0x410410410fc0fc0f) * 0x10000000000000000 + 0xc0fc0fc0000fc003) * 0x10000000000000000 + 0xf03ffff03ffc003f) * 0x10000000000000000 + 0xaa88bb88aa88bb88) * 0x10000000000000000 + 0xaa88bb88aa88bb88)
  | 182 => ((((((0x41041041041041 * 0x10000000000000000 + 0x0410410410410410) * 0x10000000000000000 + 0x410410410fc0fc0f) * 0x10000000000000000 + 0xc0fc0fc0fc0fc0ff) * 0x10000000000000000 + 0xf03ffff03ffc003f) * 0x10000000000000000 + 0xaaaabb88aaaabb88) * 0x10000000000000000 + 0xaaaabb88aaaabb88)
  | 183 => ((((((0x41041041041041 * 0x10000000000000000 + 0x0410410410410410) * 0x10000000000000000 + 0x410410410fc0fc0f) * 0x10000000000000000 + 0xc0ffffc0000fc003) * 0x10000000000000000 + 0xf03f03f03ffc003f) * 0x10000000000000000 + 0xab88ab88ab88ab88) * 0x10000000000000000 + 0xab88ab88ab88ab88)
  | 184 => ((((((0x41041041041041 * 0x10000000000000000 + 0x0410410410410410) * 0x10000000000000000 + 0x410410410fc0fc0f) * 0x10000000000000000 + 0xc0ffffc0fc0fc003) * 0x10000000000000000 + 0xf03f03f03ffc0fff) * 0x10000000000000000 + 0xaba8aba8aba8aba8) * 0x10000000000000000 + 0xaba8aba8aba8aba8)
  | 185 => ((((((0x41041041041041 * 0x10000000000000000 + 0x0410410410410410) * 0x10000000000000000 + 0x410410410fff000f) * 0x10000000000000000 + 0xff000fc0000fc003) * 0x10000000000000000 + 0xffc0ffffc0fc003f) * 0x10000000000000000 + 0xcc88dd88cc88dd88) * 0x10000000000000000 + 0xcc88dd88cc88dd88)
  | 186 => ((((((0x41041041041041 * 0x10000000000000000 + 0x0410410410410410) * 0x10000000000000000 + 0x410410410fff000f) * 0x10000000000000000 + 0xff000fff000fff03) * 0x10000000000000000 + 0xffc0ffffc0fc003f) * 0x10000000000000000 + 0xccccdd88ccccdd88) * 0x10000000000000000 + 0xccccdd88ccccdd88)
  | 187 => ((((((0x41041041041041 * 0x10000000000000000 + 0x0410410410410410) * 0x10000000000000000 + 0x410410410fff000f) * 0x10000000000000000 + 0xff03ffc0000fc003) * 0x10000000000000000 + 0xffc003ffc0fc003f) * 0x10000000000000000 + 0xcd88cd88cd88cd88) * 0x10000000000000000 + 0xcd88cd88cd88cd88)
  | 188 => ((((((0x41041041041041 * 0x10000000000000000 + 0x0410410410410410) * 0x10000000000000000 + 0x410410410fff000f) * 0x10000000000000000 + 0xff03ffff000fc003) * 0x10000000000000000 + 0xffc003ffc0fff03f) * 0x10000000000000000 + 0xcdc8cdc8cdc8cdc8) * 0x10000000000000000 + 0xcdc8cdc8cdc8cdc8)
  | 189 => ((((((0x41041041041041 * 0x10000000000000000 + 0x0410410410410410) * 0x10000000000000000 + 0x410410410ffffff0) * 0x10000000000000000 + 0x0003ffc0fc000003) * 0x10000000000000000 + 0xfffffc0000fc0fc0) * 0x10000000000000000 + 0xf1a0f1a0f1a0f1a0) * 0x10000000000000000 + 0xf1a0f1a0f1a0f1a0)
  | 190 => ((((((0x41041041041041 * 0x10000000000000000 + 0x0410410410410410) * 0x10000000000000000 + 0x410410410ffffff0) * 0x10000000000000000 + 0x0003ffff00000003) * 0x10000000000000000 + 0xfffffc0000fff000) * 0x10000000000000000 + 0xf1c0f1c0f1c0f1c0) * 0x10000000000000000 + 0xf1c0f1c0f1c0f1c0)
  | 191 => ((((((0x41041041041041 * 0x10000000000000000 + 0x0410410410410410) * 0x10000000000000000 + 0x410410410ffffff0) * 0x10000000000000000 + 0x0003fffffc000003) * 0x10000000000000000 + 0xfffffc0000ffffc0) * 0x10000000000000000 + 0xf1e0f1e0f1e0f1e0) * 0x10000000000000000 + 0xf1e0f1e0f1e0f1e0)
  | 192 => ((((((0x41041041041041 * 0x10000000000000000 + 0x0410410410410410) * 0x10000000000000000 + 0x410410410fffffff) * 0x10000000000000000 + 0xfffff00000000003) * 0x10000000000000000 + 0xffffffffff000000) * 0x10000000000000000 + 0xff00ff00ff00ff00) * 0x10000000000000000 + 0xff00ff00ff00ff00)
  | 193 => ((((((0x41041041041041 * 0x10000000000000000 + 0x0410410410410410) * 0x10000000000000000 + 0x410410410fffffff) * 0x10000000000000000 + 0xffffffc0fc0fc003) * 0x10000000000000000 + 0xfffffffffffc0fff) * 0x10000000000000000 + 0xffa8ffa8ffa8ffa8) * 0x10000000000000000 + 0xffa8ffa8ffa8ffa8)
  | 194 => ((((((0x41041041041041 * 0x10000000000000000 + 0x0410410410410410) * 0x10000000000000000 + 0x410410410fffffff) * 0x10000000000000000 + 0xffffffc0fc0fc0fc) * 0x10000000000000000 + 0x0000fc0000000000) * 0x10000000000000000 + 0xffaa1100ffaa1100) * 0x10000000000000000 + 0xffaa1100ffaa1100)
  | 195 => ((((((0x41041041041041 * 0x10000000000000000 + 0x0410410410410410) * 0x10000000000000000 + 0x410410410fffffff) * 0x10000000000000000 + 0xffffffc0fc0fc0ff) * 0x10000000000000000 + 0xfffffffffffc003f) * 0x10000000000000000 + 0xffaaff88ffaaff88) * 0x10000000000000000 + 0xffaaff88ffaaff88)
  | 196 => ((((((0x41041041041041 * 0x10000000000000000 + 0x0410410410410410) * 0x10000000000000000 + 0x410410410fffffff) * 0x10000000000000000 + 0xffffffff000fc003) * 0x10000000000000000 + 0xfffffffffffff03f) * 0x10000000000000000 + 0xffc8ffc8ffc8ffc8) * 0x10000000000000000 + 0xffc8ffc8ffc8ffc8)
  | 197 => ((((((0x41041041041041 * 0x10000000000000000 + 0x0410410410410410) * 0x10000000000000000 + 0x410410410fffffff) * 0x10000000000000000 + 0xffffffff000fff00) * 0x10000000000000000 + 0x0000fc0000000000) * 0x10000000000000000 + 0xffcc1100ffcc1100) * 0x10000000000000000 + 0xffcc1100ffcc1100)
  | 198 => ((((((0x41041041041041 * 0x10000000000000000 + 0x0410410410410410) * 0x10000000000000000 + 0x410410410fffffff) * 0x10000000000000000 + 0xffffffff000fff03) * 0x10000000000000000 + 0xfffffffffffc003f) * 0x10000000000000000 + 0xffccff88ffccff88) * 0x10000000000000000 + 0xffccff88ffccff88)
  | 199 => ((((((0x41041041041041 * 0x10000000000000000 + 0x0410410410410410) * 0x10000000000000000 + 0x410410410fffffff) * 0x10000000000000000 + 0xfffffffffc000003) * 0x10000000000000000 + 0xffffffffffffffc0) * 0x10000000000000000 + 0xffe0ffe0ffe0ffe0) * 0x10000000000000000 + 0xffe0ffe0ffe0ffe0)
  | 200 => ((((((0x41041041041041 * 0x10000000000000000 + 0x0410410410410410) * 0x10000000000000000 + 0x410410410fffffff) * 0x10000000000000000 + 0xfffffffffc0ffffc) * 0x10000000000000000 + 0x0000fc0000000000) * 0x10000000000000000 + 0xffee1100ffee1100) * 0x10000000000000000 + 0xffee1100ffee1100)
  | 201 => ((((((0x41041041041041 * 0x10000000000000000 + 0x0410410410410410) * 0x10000000000000000 + 0x410410410fffffff) * 0x10000000000000000 + 0xfffffffffc0fffff) * 0x10000000000000000 + 0xffffffffff000000) * 0x10000000000000000 + 0xffeeff00ffeeff00) * 0x10000000000000000 + 0xffeeff00ffeeff00)
  | 202 => ((((((0x41041041041041 * 0x10000000000000000 + 0x0410410410410410) * 0x10000000000000000 + 0x410410410fffffff) * 0x10000000000000000 + 0xfffffffffc0fffff) * 0x10000000000000000 + 0xffffffffffffffc0) * 0x10000000000000000 + 0xffeeffe0ffeeffe0) * 0x10000000000000000 + 0xffeeffe0ffeeffe0)
  | 203 => ((((((0x41041041041041 * 0x10000000000000000 + 0x0410410410410410) * 0x10000000000000000 + 0x410410410fffffff) * 0x10000000000000000 + 0xffffffffffffc0ff) * 0x10000000000000000 + 0xfffffffffffff03f) * 0x10000000000000000 + 0xfffaffc8fffaffc8) * 0x10000000000000000 + 0xfffaffc8fffaffc8)
  | 204 => ((((((0x41041041041041 * 0x10000000000000000 + 0x0410410410410410) * 0x10000000000000000 + 0x410410410fffffff) * 0x10000000000000000 + 0xffffffffffffff03) * 0x10000000000000000 + 0xfffffffffffc0fff) * 0x10000000000000000 + 0xfffcffa8fffcffa8) * 0x10000000000000000 + 0xfffcffa8fffcffa8)
  | 205 => ((((((0x49249249249249 * 0x10000000000000000 + 0x2492492492492492) * 0x10000000000000000 + 0x4924924920000000) * 0x10000000000000000 + 0x0000000000000000) * 0x10000000000000000 + 0x000003ffff00003f) * 0x10000000000000000 + 0x00000f0a00000f0a) * 0x10000000000000000 + 0x00000f0a00000f0a)
  | 206 => ((((((0x49249249249249 * 0x10000000000000000 + 0x2492492492492492) * 0x10000000000000000 + 0x4924924920000000) * 0x10000000000000000 + 0x0000000000000000) * 0x10000000000000000 + 0x003ffc003f000fc0) * 0x10000000000000000 + 0x0000332200003322) * 0x10000000000000000 + 0x0000332200003322)
  | 207 => ((((((0x49249249249249 * 0x10000000000000000 + 0x2492492492492492) * 0x10000000000000000 + 0x4924924920000000) * 0x10000000000000000 + 0x0000000000000003) * 0x10000000000000000 + 0xffffffffff000fc0) * 0x10000000000000000 + 0x0000ff220000ff22) * 0x10000000000000000 + 0x0000ff220000ff22)
  | 208 => ((((((0x49249249249249 * 0x10000000000000000 + 0x2492492492492492) * 0x10000000000000000 + 0x4924924920000000) * 0x10000000000000000 + 0x0000000000000003) * 0x10000000000000000 + 0xfffffffffffc0fff) * 0x10000000000000000 + 0x0000ffaa0000ffaa) * 0x10000000000000000 + 0x0000ffaa0000ffaa)
  | 209 => ((((((0x49249249249249 * 0x10000000000000000 + 0x2492492492492492) * 0x10000000000000000 + 0x4924924920000000) * 0x10000000000000000 + 0x00fff000000000fc) * 0x10000000000000000 + 0x000000003f000000) * 0x10000000000000000 + 0x0302030203020302) * 0x10000000000000000 + 0x0302030203020302)
  | 210 => ((((((0x49249249249249 * 0x10000000000000000 + 0x2492492492492492) * 0x10000000000000000 + 0x492492492000000f) * 0x10000000000000000 + 0xfffff000000000fc) * 0x10000000000000000 + 0x000003ffff000000) * 0x10000000000000000 + 0x0f020f020f020f02) * 0x10000000000000000 + 0x0f020f020f020f02)
  | 211 => ((((((0x49249249249249 * 0x10000000000000000 + 0x2492492492492492) * 0x10000000000000000 + 0x492492492000000f) * 0x10000000000000000 + 0xfffff000000fc0fc) * 0x10000000000000000 + 0x000003ffff00003f) * 0x10000000000000000 + 0x0f0a0f0a0f0a0f0a) * 0x10000000000000000 + 0x0f0a0f0a0f0a0f0a)
  | 212 => ((((((0x49249249249249 * 0x10000000000000000 + 0x2492492492492492) * 0x10000000000000000 + 0x49249249200003f0) * 0x10000000000000000 + 0x0003f00000000000) * 0x10000000000000000 + 0x0000fc0000fc0fff) * 0x10000000000000000 + 0x110011aa110011aa) * 0x10000000000000000 + 0x110011aa110011aa)
  | 213 => ((((((0x49249249249249 * 0x10000000000000000 + 0x2492492492492492) * 0x10000000000000000 + 0x49249249200003f0) * 0x10000000000000000 + 0x0003f000000fc0fc) * 0x10000000000000000 + 0x0000fc000000003f) * 0x10000000000000000 + 0x110a110a110a110a) * 0x10000000000000000 + 0x110a110a110a110a)
  | 214 => ((((((0x49249249249249 * 0x10000000000000000 + 0x2492492492492492) * 0x10000000000000000 + 0x492492492000fff0) * 0x10000000000000000 + 0x00fff00000000000) * 0x10000000000000000 + 0x003ffc003f000fc0) * 0x10000000000000000 + 0x3300332233003322) * 0x10000000000000000 + 0x3300332233003322)
  | 215 => ((((((0x49249249249249 * 0x10000000000000000 + 0x2492492492492492) * 0x10000000000000000 + 0x492492492000fff0) * 0x10000000000000000 + 0x00fff000000000fc) * 0x10000000000000000 + 0x003ffc003f000000) * 0x10000000000000000 + 0x3302330233023302) * 0x10000000000000000 + 0x3302330233023302)
  | 216 => ((((((0x49249249249249 * 0x10000000000000000 + 0x2492492492492492) * 0x10000000000000000 + 0x492492492000fff0) * 0x10000000000000000 + 0x00fff000fc0000fc) * 0x10000000000000000 + 0x003ffc003f000fc0) * 0x10000000000000000 + 0x3322332233223322) * 0x10000000000000000 + 0x3322332233223322)
  | 217 => ((((((0x49249249249249 * 0x10000000000000000 + 0x2492492492492492) * 0x10000000000000000 + 0x492492492fffffff) * 0x10000000000000000 + 0xffffffc0fc0fc0ff) * 0x10000000000000000 + 0xfffffffffffc0fff) * 0x10000000000000000 + 0xffaaffaaffaaffaa) * 0x10000000000000000 + 0xffaaffaaffaaffaa)
  | 218 => ((((((0x51451451451451 * 0x10000000000000000 + 0x4514514514514514) * 0x10000000000000000 + 0x5145145140000000) * 0x10000000000000000 + 0x0000000000000000) * 0x10000000000000000 + 0x000003ffff00003f) * 0x10000000000000000 + 0x00000f0c00000f0c) * 0x10000000000000000 + 0x00000f0c00000f0c)
  | 219 => ((((((0x51451451451451 * 0x10000000000000000 + 0x4514514514514514) * 0x10000000000000000 + 0x5145145140000000) * 0x10000000000000000 + 0x0000000000000000) * 0x10000000000000000 + 0x0fc0fc0fc003f000) * 0x10000000000000000 + 0x0000554400005544) * 0x10000000000000000 + 0x0000554400005544)
  | 220 => ((((((0x51451451451451 * 0x10000000000000000 + 0x4514514514514514) * 0x10000000000000000 + 0x5145145140000000) * 0x10000000000000000 + 0x0000000000000003) * 0x10000000000000000 + 0xffffffffff03f000) * 0x10000000000000000 + 0x0000ff440000ff44) * 0x10000000000000000 + 0x0000ff440000ff44)
  | 221 => ((((((0x51451451451451 * 0x10000000000000000 + 0x4514514514514514) * 0x10000000000000000 + 0x5145145140000000) * 0x10000000000000000 + 0x0000000000000003) * 0x10000000000000000 + 0xfffffffffffff03f) * 0x10000000000000000 + 0x0000ffcc0000ffcc) * 0x10000000000000000 + 0x0000ffcc0000ffcc)
  | 222 => ((((((0x51451451451451 * 0x10000000000000000 + 0x4514514514514514) * 0x10000000000000000 + 0x5145145140000000) * 0x10000000000000000 + 0x3f03f00000003f00) * 0x10000000000000000 + 0x0000000fc0000000) * 0x10000000000000000 + 0x0504050405040504) * 0x10000000000000000 + 0x0504050405040504)
  | 223 => ((((((0x51451451451451 * 0x10000000000000000 + 0x4514514514514514) * 0x10000000000000000 + 0x514514514000000f) * 0x10000000000000000 + 0xfffff00000003f00) * 0x10000000000000000 + 0x000003ffff000000) * 0x10000000000000000 + 0x0f040f040f040f04) * 0x10000000000000000 + 0x0f040f040f040f04)
  | 224 => ((((((0x51451451451451 * 0x10000000000000000 + 0x4514514514514514) * 0x10000000000000000 + 0x514514514000000f) * 0x10000000000000000 + 0xfffff000000fff00) * 0x10000000000000000 + 0x000003ffff00003f) * 0x10000000000000000 + 0x0f0c0f0c0f0c0f0c) * 0x10000000000000000 + 0x0f0c0f0c0f0c0f0c)
  | 225 => ((((((0x51451451451451 * 0x10000000000000000 + 0x4514514514514514) * 0x10000000000000000 + 0x51451451400003f0) * 0x10000000000000000 + 0x0003f00000000000) * 0x10000000000000000 + 0x0000fc0000fff03f) * 0x10000000000000000 + 0x110011cc110011cc) * 0x10000000000000000 + 0x110011cc110011cc)
  | 226 => ((((((0x51451451451451 * 0x10000000000000000 + 0x4514514514514514) * 0x10000000000000000 + 0x51451451400003f0) * 0x10000000000000000 + 0x0003f000000fff00) * 0x10000000000000000 + 0x0000fc000000003f) * 0x10000000000000000 + 0x110c110c110c110c) * 0x10000000000000000 + 0x110c110c110c110c)
  | 227 => ((((((0x51451451451451 * 0x10000000000000000 + 0x4514514514514514) * 0x10000000000000000 + 0x51451451403f03f0) * 0x10000000000000000 + 0x3f03f00000000000) * 0x10000000000000000 + 0x0fc0fc0fc003f000) * 0x10000000000000000 + 0x5500554455005544) * 0x10000000000000000 + 0x5500554455005544)
  | 228 => ((((((0x51451451451451 * 0x10000000000000000 + 0x4514514514514514) * 0x10000000000000000 + 0x51451451403f03f0) * 0x10000000000000000 + 0x3f03f00000003f00) * 0x10000000000000000 + 0x0fc0fc0fc0000000) * 0x10000000000000000 + 0x5504550455045504) * 0x10000000000000000 + 0x5504550455045504)
  | 229 => ((((((0x51451451451451 * 0x10000000000000000 + 0x4514514514514514) * 0x10000000000000000 + 0x51451451403f03f0) * 0x10000000000000000 + 0x3f03f03f00003f00) * 0x10000000000000000 + 0x0fc0fc0fc003f000) * 0x10000000000000000 + 0x5544554455445544) * 0x10000000000000000 + 0x5544554455445544)
  | 230 => ((((((0x51451451451451 * 0x10000000000000000 + 0x4514514514514514) * 0x10000000000000000 + 0x514514514fffffff) * 0x10000000000000000 + 0xffffffff000fff03) * 0x10000000000000000 + 0xfffffffffffff03f) * 0x10000000000000000 + 0xffccffccffccffcc) * 0x10000000000000000 + 0xffccffccffccffcc)
  | 231 => ((((((0x59659659659659 * 0x10000000000000000 + 0x6596596596596596) * 0x10000000000000000 + 0x5965965960000000) * 0x10000000000000000 + 0x0000000000000000) * 0x10000000000000000 + 0x000003ffff00003f) * 0x10000000000000000 + 0x00000f0e00000f0e) * 0x10000000000000000 + 0x00000f0e00000f0e)
  | 232 => ((((((0x59659659659659 * 0x10000000000000000 + 0x6596596596596596) * 0x10000000000000000 + 0x5965965960000000) * 0x10000000000000000 + 0x0000000000000003) * 0x10000000000000000 + 0xffffffffff00003f) * 0x10000000000000000 + 0x0000ff0e0000ff0e) * 0x10000000000000000 + 0x0000ff0e0000ff0e)
  | 233 => ((((((0x59659659659659 * 0x10000000000000000 + 0x6596596596596596) * 0x10000000000000000 + 0x5965965960000000) * 0x10000000000000000 + 0x0000000000000003) * 0x10000000000000000 + 0xffffffffffffffff) * 0x10000000000000000 + 0x0000ffee0000ffee) * 0x10000000000000000 + 0x0000ffee0000ffee)
  | 234 => ((((((0x59659659659659 * 0x10000000000000000 + 0x6596596596596596) * 0x10000000000000000 + 0x596596596000000f) * 0x10000000000000000 + 0xfffff00000000000) * 0x10000000000000000 + 0x000003ffff00003f) * 0x10000000000000000 + 0x0f000f0e0f000f0e) * 0x10000000000000000 + 0x0f000f0e0f000f0e)
  | 235 => ((((((0x59659659659659 * 0x10000000000000000 + 0x6596596596596596) * 0x10000000000000000 + 0x596596596000000f) * 0x10000000000000000 + 0xfffff000000ffffc) * 0x10000000000000000 + 0x000003ffff00003f) * 0x10000000000000000 + 0x0f0e0f0e0f0e0f0e) * 0x10000000000000000 + 0x0f0e0f0e0f0e0f0e)
  | 236 => ((((((0x59659659659659 * 0x10000000000000000 + 0x6596596596596596) * 0x10000000000000000 + 0x59659659600003f0) * 0x10000000000000000 + 0x0003f00000000000) * 0x10000000000000000 + 0x0000fc0000ffffff) * 0x10000000000000000 + 0x110011ee110011ee) * 0x10000000000000000 + 0x110011ee110011ee)
  | 237 => ((((((0x59659659659659 * 0x10000000000000000 + 0x6596596596596596) * 0x10000000000000000 + 0x59659659600003f0) * 0x10000000000000000 + 0x0003f000000ffffc) * 0x10000000000000000 + 0x0000fc000000003f) * 0x10000000000000000 + 0x110e110e110e110e) * 0x10000000000000000 + 0x110e110e110e110e)
  | 238 => ((((((0x59659659659659 * 0x10000000000000000 + 0x6596596596596596) * 0x10000000000000000 + 0x596596596fffffff) * 0x10000000000000000 + 0xfffff00000000003) * 0x10000000000000000 + 0xffffffffff00003f) * 0x10000000000000000 + 0xff00ff0eff00ff0e) * 0x10000000000000000 + 0xff00ff0eff00ff0e)
  | 239 => ((((((0x59659659659659 * 0x10000000000000000 + 0x6596596596596596) * 0x10000000000000000 + 0x596596596fffffff) * 0x10000000000000000 + 0xfffff00000000003) * 0x10000000000000000 + 0xffffffffffffffff) * 0x10000000000000000 + 0xff00ffeeff00ffee) * 0x10000000000000000 + 0xff00ffeeff00ffee)
  | 240 => ((((((0x59659659659659 * 0x10000000000000000 + 0x6596596596596596) * 0x10000000000000000 + 0x596596596fffffff) * 0x10000000000000000 + 0xfffff000000fffff) * 0x10000000000000000 + 0xffffffffff00003f) * 0x10000000000000000 + 0xff0eff0eff0eff0e) * 0x10000000000000000 + 0xff0eff0eff0eff0e)
  | 241 => ((((((0x59659659659659 * 0x10000000000000000 + 0x6596596596596596) * 0x10000000000000000 + 0x596596596fffffff) * 0x10000000000000000 + 0xfffffffffc0fffff) * 0x10000000000000000 + 0xffffffffffffffff) * 0x10000000000000000 + 0xffeeffeeffeeffee) * 0x10000000000000000 + 0xffeeffeeffeeffee)
  | 242 => ((((((0x61861861861861 * 0x10000000000000000 + 0x8618618618618618) * 0x10000000000000000 + 0x6186186180000000) * 0x10000000000000000 + 0x0000000000000000) * 0x10000000000000000 + 0x0000fc0000000000) * 0x10000000000000000 + 0x0000111000001110) * 0x10000000000000000 + 0x0000111000001110)
  | 243 => ((((((0x61861861861861 * 0x10000000000000000 + 0x8618618618618618) * 0x10000000000000000 + 0x6186186180000000) * 0x10000000000000000 + 0x0000000000000003) * 0x10000000000000000 + 0xffffffffffffffc0) * 0x10000000000000000 + 0x0000fff00000fff0) * 0x10000000000000000 + 0x0000fff00000fff0)
  | 244 => ((((((0x61861861861861 * 0x10000000000000000 + 0x8618618618618618) * 0x10000000000000000 + 0x6186186180000000) * 0x10000000000000000 + 0x00fff03f03f00000) * 0x10000000000000000 + 0x000000003f03f000) * 0x10000000000000000 + 0x0350035003500350) * 0x10000000000000000 + 0x0350035003500350)
  | 245 => ((((((0x61861861861861 * 0x10000000000000000 + 0x8618618618618618) * 0x10000000000000000 + 0x6186186180000000) * 0x10000000000000000 + 0x3f03f000fff00000) * 0x10000000000000000 + 0x0000000fc0000fc0) * 0x10000000000000000 + 0x0530053005300530) * 0x10000000000000000 + 0x0530053005300530)
  | 246 => ((((((0x61861861861861 * 0x10000000000000000 + 0x8618618618618618) * 0x10000000000000000 + 0x61861861800003f0) * 0x10000000000000000 + 0x0003f00003f00000) * 0x10000000000000000 + 0x0000fc0000000000) * 0x10000000000000000 + 0x1110111011101110) * 0x10000000000000000 + 0x1110111011101110)
  | 247 => ((((((0x61861861861861 * 0x10000000000000000 + 0x8618618618618618) * 0x10000000000000000 + 0x618618618fffffff) * 0x10000000000000000 + 0xfffffffffff00000) * 0x10000000000000000 + 0x0000fc0000000000) * 0x10000000000000000 + 0xfff01110fff01110) * 0x10000000000000000 + 0xfff01110fff01110)
  | 248 => ((((((0x61861861861861 * 0x10000000000000000 + 0x8618618618618618) * 0x10000000000000000 + 0x618618618fffffff) * 0x10000000000000000 + 0xfffffffffff00003) * 0x10000000000000000 + 0xffffffffffffffc0) * 0x10000000000000000 + 0xfff0fff0fff0fff0) * 0x10000000000000000 + 0xfff0fff0fff0fff0)
  | 249 => ((((((0x69a69a69a69a69 * 0x10000000000000000 + 0xa69a69a69a69a69a) * 0x10000000000000000 + 0x69a69a69a0000000) * 0x10000000000000000 + 0x0000000000000003) * 0x10000000000000000 + 0xffffffffffffffff) * 0x10000000000000000 + 0x0000fffa0000fffa) * 0x10000000000000000 + 0x0000fffa0000fffa)
  | 250 => ((((((0x69a69a69a69a69 * 0x10000000000000000 + 0xa69a69a69a69a69a) * 0x10000000000000000 + 0x69a69a69a00003f0) * 0x10000000000000000 + 0x0003f00003ffc0fc) * 0x10000000000000000 + 0x0000fc000000003f) * 0x10000000000000000 + 0x111a111a111a111a) * 0x10000000000000000 + 0x111a111a111a111a)
  | 251 => ((((((0x69a69a69a69a69 * 0x10000000000000000 + 0xa69a69a69a69a69a) * 0x10000000000000000 + 0x69a69a69a000fff0) * 0x10000000000000000 + 0x00fff000fff000fc) * 0x10000000000000000 + 0x003ffc003f000fc0) * 0x10000000000000000 + 0x3332333233323332) * 0x10000000000000000 + 0x3332333233323332)
  | 252 => ((((((0x69a69a69a69a69 * 0x10000000000000000 + 0xa69a69a69a69a69a) * 0x10000000000000000 + 0x69a69a69afc0fc0f) * 0x10000000000000000 + 0xc0fc0fc0fc0fc0ff) * 0x10000000000000000 + 0xffffffffffffffff) * 0x10000000000000000 + 0xaaaafffaaaaafffa) * 0x10000000000000000 + 0xaaaafffaaaaafffa)
  | 253 => ((((((0x69a69a69a69a69 * 0x10000000000000000 + 0xa69a69a69a69a69a) * 0x10000000000000000 + 0x69a69a69afc0ffff) * 0x10000000000000000 + 0xc0ffffc0ffffc0ff) * 0x10000000000000000 + 0xf03ffff03ffc0fff) * 0x10000000000000000 + 0xbbbabbbabbbabbba) * 0x10000000000000000 + 0xbbbabbbabbbabbba)
  | 254 => ((((((0x69a69a69a69a69 * 0x10000000000000000 + 0xa69a69a69a69a69a) * 0x10000000000000000 + 0x69a69a69affffff0) * 0x10000000000000000 + 0x00000ffffff00003) * 0x10000000000000000 + 0xffffffffffffffff) * 0x10000000000000000 + 0xf0f0fffaf0f0fffa) * 0x10000000000000000 + 0xf0f0fffaf0f0fffa)
  | 255 => ((((((0x69a69a69a69a69 * 0x10000000000000000 + 0xa69a69a69a69a69a) * 0x10000000000000000 + 0x69a69a69affffff0) * 0x10000000000000000 + 0x00fffffffff000ff) * 0x10000000000000000 + 0xfffffc003fffffc0) * 0x10000000000000000 + 0xf3f2f3f2f3f2f3f2) * 0x10000000000000000 + 0xf3f2f3f2f3f2f3f2)
  | 256 => ((((((0x69a69a69a69a69 * 0x10000000000000000 + 0xa69a69a69a69a69a) * 0x10000000000000000 + 0x69a69a69afffffff) * 0x10000000000000000 + 0xfffff00000000003) * 0x10000000000000000 + 0xffffffffffffffff) * 0x10000000000000000 + 0xff00fffaff00fffa) * 0x10000000000000000 + 0xff00fffaff00fffa)
  | 257 => ((((((0x69a69a69a69a69 * 0x10000000000000000 + 0xa69a69a69a69a69a) * 0x10000000000000000 + 0x69a69a69afffffff) * 0x10000000000000000 + 0xfffff000fff000ff) * 0x10000000000000000 + 0xffffffffff000fc0) * 0x10000000000000000 + 0xff32ff32ff32ff32) * 0x10000000000000000 + 0xff32ff32ff32ff32)
  | 258 => ((((((0x69a69a69a69a69 * 0x10000000000000000 + 0xa69a69a69a69a69a) * 0x10000000000000000 + 0x69a69a69afffffff) * 0x10000000000000000 + 0xffffffffffffc0ff) * 0x10000000000000000 + 0xffffffffffffffff) * 0x10000000000000000 + 0xfffafffafffafffa) * 0x10000000000000000 + 0xfffafffafffafffa)
  | 259 => ((((((0x71c71c71c71c71 * 0x10000000000000000 + 0xc71c71c71c71c71c) * 0x10000000000000000 + 0x71c71c71c0000000) * 0x10000000000000000 + 0x0000000000000003) * 0x10000000000000000 + 0xffffffffffffffff) * 0x10000000000000000 + 0x0000fffc0000fffc) * 0x10000000000000000 + 0x0000fffc0000fffc)
  | 260 => ((((((0x71c71c71c71c71 * 0x10000000000000000 + 0xc71c71c71c71c71c) * 0x10000000000000000 + 0x71c71c71c00003f0) * 0x10000000000000000 + 0x0003f00003ffff00) * 0x10000000000000000 + 0x0000fc000000003f) * 0x10000000000000000 + 0x111c111c111c111c) * 0x10000000000000000 + 0x111c111c111c111c)
  | 261 => ((((((0x71c71c71c71c71 * 0x10000000000000000 + 0xc71c71c71c71c71c) * 0x10000000000000000 + 0x71c71c71c03f03f0) * 0x10000000000000000 + 0x3f03f03f03f03f00) * 0x10000000000000000 + 0x0fc0fc0fc003f000) * 0x10000000000000000 + 0x5554555455545554) * 0x10000000000000000 + 0x5554555455545554)
  | 262 => ((((((0x71c71c71c71c71 * 0x10000000000000000 + 0xc71c71c71c71c71c) * 0x10000000000000000 + 0x71c71c71cfff000f) * 0x10000000000000000 + 0xff000fff000fff03) * 0x10000000000000000 + 0xffffffffffffffff) * 0x10000000000000000 + 0xccccfffcccccfffc) * 0x10000000000000000 + 0xccccfffcccccfffc)
  | 263 => ((((((0x71c71c71c71c71 * 0x10000000000000000 + 0xc71c71c71c71c71c) * 0x10000000000000000 + 0x71c71c71cfff03ff) * 0x10000000000000000 + 0xff03ffff03ffff03) * 0x10000000000000000 + 0xffc0ffffc0fff03f) * 0x10000000000000000 + 0xdddcdddcdddcdddc) * 0x10000000000000000 + 0xdddcdddcdddcdddc)
  | 264 => ((((((0x71c71c71c71c71 * 0x10000000000000000 + 0xc71c71c71c71c71c) * 0x10000000000000000 + 0x71c71c71cffffff0) * 0x10000000000000000 + 0x00000ffffff00003) * 0x10000000000000000 + 0xffffffffffffffff) * 0x10000000000000000 + 0xf0f0fffcf0f0fffc) * 0x10000000000000000 + 0xf0f0fffcf0f0fffc)
  | 265 => ((((((0x71c71c71c71c71 * 0x10000000000000000 + 0xc71c71c71c71c71c) * 0x10000000000000000 + 0x71c71c71cffffff0) * 0x10000000000000000 + 0x3f03fffffff03f03) * 0x10000000000000000 + 0xfffffc0fc0ffffc0) * 0x10000000000000000 + 0xf5f4f5f4f5f4f5f4) * 0x10000000000000000 + 0xf5f4f5f4f5f4f5f4)
  | 266 => ((((((0x71c71c71c71c71 * 0x10000000000000000 + 0xc71c71c71c71c71c) * 0x10000000000000000 + 0x71c71c71cfffffff) * 0x10000000000000000 + 0xfffff00000000003) * 0x10000000000000000 + 0xffffffffffffffff) * 0x10000000000000000 + 0xff00fffcff00fffc) * 0x10000000000000000 + 0xff00fffcff00fffc)
  | 267 => ((((((0x71c71c71c71c71 * 0x10000000000000000 + 0xc71c71c71c71c71c) * 0x10000000000000000 + 0x71c71c71cfffffff) * 0x10000000000000000 + 0xfffff03f03f03f03) * 0x10000000000000000 + 0xffffffffff03f000) * 0x10000000000000000 + 0xff54ff54ff54ff54) * 0x10000000000000000 + 0xff54ff54ff54ff54)
  | 268 => ((((((0x71c71c71c71c71 * 0x10000000000000000 + 0xc71c71c71c71c71c) * 0x10000000000000000 + 0x71c71c71cfffffff) * 0x10000000000000000 + 0xffffffffffffff03) * 0x10000000000000000 + 0xffffffffffffffff) * 0x10000000000000000 + 0xfffcfffcfffcfffc) * 0x10000000000000000 + 0xfffcfffcfffcfffc)
  | 269 => ((((((0x79e79e79e79e79 * 0x10000000000000000 + 0xe79e79e79e79e79e) * 0x10000000000000000 + 0x79e79e79e0000000) * 0x10000000000000000 + 0x0000000000000003) * 0x10000000000000000 + 0xffffffffffffffff) * 0x10000000000000000 + 0x0000fffe0000fffe) * 0x10000000000000000 + 0x0000fffe0000fffe)
  | 270 => ((((((0x79e79e79e79e79 * 0x10000000000000000 + 0xe79e79e79e79e79e) * 0x10000000000000000 + 0x79e79e79effffc0f) * 0x10000000000000000 + 0xfffc0ffffc0fffff) * 0x10000000000000000 + 0xffffffffffffffff) * 0x10000000000000000 + 0xeeeefffeeeeefffe) * 0x10000000000000000 + 0xeeeefffeeeeefffe)
  | 271 => ((((((0x79e79e79e79e79 * 0x10000000000000000 + 0xe79e79e79e79e79e) * 0x10000000000000000 + 0x79e79e79effffff0) * 0x10000000000000000 + 0x00000ffffff00003) * 0x10000000000000000 + 0xffffffffffffffff) * 0x10000000000000000 + 0xf0f0fffef0f0fffe) * 0x10000000000000000 + 0xf0f0fffef0f0fffe)
  | 272 => ((((((0x79e79e79e79e79 * 0x10000000000000000 + 0xe79e79e79e79e79e) * 0x10000000000000000 + 0x79e79e79efffffff) * 0x10000000000000000 + 0xfffff00000000003) * 0x10000000000000000 + 0xffffffffffffffff) * 0x10000000000000000 + 0xff00fffeff00fffe) * 0x10000000000000000 + 0xff00fffeff00fffe)
  | 273 => ((((((0x79e79e79e79e79 * 0x10000000000000000 + 0xe79e79e79e79e79e) * 0x10000000000000000 + 0x79e79e79efffffff) * 0x10000000000000000 + 0xfffffffffff00003) * 0x10000000000000000 + 0xffffffffffffffff) * 0x10000000000000000 + 0xfff0fffefff0fffe) * 0x10000000000000000 + 0xfff0fffefff0fffe)
  | 274 => ((((((0x79e79e79e79e79 * 0x10000000000000000 + 0xe79e79e79e79e79e) * 0x10000000000000000 + 0x79e79e79efffffff) * 0x10000000000000000 + 0xffffffffffffffff) * 0x10000000000000000 + 0xffffffffffffffff) * 0x10000000000000000 + 0xfffefffefffefffe) * 0x10000000000000000 + 0xfffefffefffefffe)
  | 275 => ((((((0x82082082082082 * 0x10000000000000000 + 0x0820820820820820) * 0x10000000000000000 + 0x8208208200000000) * 0x10000000000000000 + 0x00fff03f03f03ffc) * 0x10000000000000000 + 0x0000000000000000) * 0x10000000000000000 + 0x0357000003570000) * 0x10000000000000000 + 0x0357000003570000)
  | 276 => ((((((0x82082082082082 * 0x10000000000000000 + 0x0820820820820820) * 0x10000000000000000 + 0x8208208200000000) * 0x10000000000000000 + 0x3f03f000fff03ffc) * 0x10000000000000000 + 0x0000000000000000) * 0x10000000000000000 + 0x0537000005370000) * 0x10000000000000000 + 0x0537000005370000)
  | 277 => ((((((0x82082082082082 * 0x10000000000000000 + 0x0820820820820820) * 0x10000000000000000 + 0x82082082000003f0) * 0x10000000000000000 + 0x0003f00003fffffc) * 0x10000000000000000 + 0x0000000000000000) * 0x10000000000000000 + 0x111f0000111f0000) * 0x10000000000000000 + 0x111f0000111f0000)
  | 278 => ((((((0x82082082082082 * 0x10000000000000000 + 0x0820820820820820) * 0x10000000000000000 + 0x82082082000003f0) * 0x10000000000000000 + 0x0003fffffffffffc) * 0x10000000000000000 + 0x0000000000fc003f) * 0x10000000000000000 + 0x11ff008811ff0088) * 0x10000000000000000 + 0x11ff008811ff0088)
  | 279 => ((((((0x82082082082082 * 0x10000000000000000 + 0x0820820820820820) * 0x10000000000000000 + 0x82082082000003ff) * 0x10000000000000000 + 0xfffff00003fffffc) * 0x10000000000000000 + 0x000003f00000003f) * 0x10000000000000000 + 0x1f1f08081f1f0808) * 0x10000000000000000 + 0x1f1f08081f1f0808)
  | 280 => ((((((0x82082082082082 * 0x10000000000000000 + 0x0820820820820820) * 0x10000000000000000 + 0x820820820fc0fc0f) * 0x10000000000000000 + 0xc0fc0fc0ffffc0ff) * 0x10000000000000000 + 0xf00003f000fc003f) * 0x10000000000000000 + 0xaabb8888aabb8888) * 0x10000000000000000 + 0xaabb8888aabb8888)
  | 281 => ((((((0x82082082082082 * 0x10000000000000000 + 0x0820820820820820) * 0x10000000000000000 + 0x820820820fc0fc0f) * 0x10000000000000000 + 0xc0fc0fc0ffffc0ff) * 0x10000000000000000 + 0xf03f03f03ffc003f) * 0x10000000000000000 + 0xaabbaa88aabbaa88) * 0x10000000000000000 + 0xaabbaa88aabbaa88)
  | 282 => ((((((0x82082082082082 * 0x10000000000000000 + 0x0820820820820820) * 0x10000000000000000 + 0x820820820fc0fc0f) * 0x10000000000000000 + 0xc0ffffc0fc0fc0ff) * 0x10000000000000000 + 0xf00003f000fc003f) * 0x10000000000000000 + 0xabab8888abab8888) * 0x10000000000000000 + 0xabab8888abab8888)
  | 283 => ((((((0x82082082082082 * 0x10000000000000000 + 0x0820820820820820) * 0x10000000000000000 + 0x820820820fc0fc0f) * 0x10000000000000000 + 0xc0ffffc0fc0fc0ff) * 0x10000000000000000 + 0xf03f03f000fc0fff) * 0x10000000000000000 + 0xababa8a8ababa8a8) * 0x10000000000000000 + 0xababa8a8ababa8a8)
  | 284 => ((((((0x82082082082082 * 0x10000000000000000 + 0x0820820820820820) * 0x10000000000000000 + 0x820820820fff000f) * 0x10000000000000000 + 0xff000fff03ffff03) * 0x10000000000000000 + 0xf00003f000fc003f) * 0x10000000000000000 + 0xccdd8888ccdd8888) * 0x10000000000000000 + 0xccdd8888ccdd8888)
  | 285 => ((((((0x82082082082082 * 0x10000000000000000 + 0x0820820820820820) * 0x10000000000000000 + 0x820820820fff000f) * 0x10000000000000000 + 0xff000fff03ffff03) * 0x10000000000000000 + 0xffc003ffc0fc003f) * 0x10000000000000000 + 0xccddcc88ccddcc88) * 0x10000000000000000 + 0xccddcc88ccddcc88)
  | 286 => ((((((0x82082082082082 * 0x10000000000000000 + 0x0820820820820820) * 0x10000000000000000 + 0x820820820fff000f) * 0x10000000000000000 + 0xff03ffff000fff03) * 0x10000000000000000 + 0xf00003f000fc003f) * 0x10000000000000000 + 0xcdcd8888cdcd8888) * 0x10000000000000000 + 0xcdcd8888cdcd8888)
  | 287 => ((((((0x82082082082082 * 0x10000000000000000 + 0x0820820820820820) * 0x10000000000000000 + 0x820820820fff000f) * 0x10000000000000000 + 0xff03ffff000fff03) * 0x10000000000000000 + 0xffc003f000fff03f) * 0x10000000000000000 + 0xcdcdc8c8cdcdc8c8) * 0x10000000000000000 + 0xcdcdc8c8cdcdc8c8)
  | 288 => ((((((0x82082082082082 * 0x10000000000000000 + 0x0820820820820820) * 0x10000000000000000 + 0x820820820ffffff0) * 0x10000000000000000 + 0x0003fffffff00003) * 0x10000000000000000 + 0xf03f000000fc0fc0) * 0x10000000000000000 + 0xf1f1a0a0f1f1a0a0) * 0x10000000000000000 + 0xf1f1a0a0f1f1a0a0)
  | 289 => ((((((0x82082082082082 * 0x10000000000000000 + 0x0820820820820820) * 0x10000000000000000 + 0x820820820ffffff0) * 0x10000000000000000 + 0x0003fffffff00003) * 0x10000000000000000 + 0xffc0000000fff000) * 0x10000000000000000 + 0xf1f1c0c0f1f1c0c0) * 0x10000000000000000 + 0xf1f1c0c0f1f1c0c0)
  | 290 => ((((((0x82082082082082 * 0x10000000000000000 + 0x0820820820820820) * 0x10000000000000000 + 0x820820820ffffff0) * 0x10000000000000000 + 0x0003fffffff00003) * 0x10000000000000000 + 0xffff000000ffffc0) * 0x10000000000000000 + 0xf1f1e0e0f1f1e0e0) * 0x10000000000000000 + 0xf1f1e0e0f1f1e0e0)
  | 291 => ((((((0x82082082082082 * 0x10000000000000000 + 0x0820820820820820) * 0x10000000000000000 + 0x820820820fffffff) * 0x10000000000000000 + 0xfffff00003f00003) * 0x10000000000000000 + 0xf03f03f03f000000) * 0x10000000000000000 + 0xff11aa00ff11aa00) * 0x10000000000000000 + 0xff11aa00ff11aa00)
  | 292 => ((((((0x82082082082082 * 0x10000000000000000 + 0x0820820820820820) * 0x10000000000000000 + 0x820820820fffffff) * 0x10000000000000000 + 0xfffff00003f00003) * 0x10000000000000000 + 0xffc003ffc0000000) * 0x10000000000000000 + 0xff11cc00ff11cc00) * 0x10000000000000000 + 0xff11cc00ff11cc00)
  | 293 => ((((((0x82082082082082 * 0x10000000000000000 + 0x0820820820820820) * 0x10000000000000000 + 0x820820820fffffff) * 0x10000000000000000 + 0xfffff00003f00003) * 0x10000000000000000 + 0xffff03ffff000000) * 0x10000000000000000 + 0xff11ee00ff11ee00) * 0x10000000000000000 + 0xff11ee00ff11ee00)
  | 294 => ((((((0x82082082082082 * 0x10000000000000000 + 0x0820820820820820) * 0x10000000000000000 + 0x820820820fffffff) * 0x10000000000000000 + 0xfffffffffffffffc) * 0x10000000000000000 + 0x0000000000000000) * 0x10000000000000000 + 0xffff0000ffff0000) * 0x10000000000000000 + 0xffff0000ffff0000)
  | 295 => ((((((0x82082082082082 * 0x10000000000000000 + 0x0820820820820820) * 0x10000000000000000 + 0x820820820fffffff) * 0x10000000000000000 + 0xffffffffffffffff) * 0x10000000000000000 + 0xf03f03f000fc0fff) * 0x10000000000000000 + 0xffffa8a8ffffa8a8) * 0x10000000000000000 + 0xffffa8a8ffffa8a8)
  | 296 => ((((((0x82082082082082 * 0x10000000000000000 + 0x0820820820820820) * 0x10000000000000000 + 0x820820820fffffff) * 0x10000000000000000 + 0xffffffffffffffff) * 0x10000000000000000 + 0xf03f03f03ffc003f) * 0x10000000000000000 + 0xffffaa88ffffaa88) * 0x10000000000000000 + 0xffffaa88ffffaa88)
  | 297 => ((((((0x82082082082082 * 0x10000000000000000 + 0x0820820820820820) * 0x10000000000000000 + 0x820820820fffffff) * 0x10000000000000000 + 0xffffffffffffffff) * 0x10000000000000000 + 0xffc003f000fff03f) * 0x10000000000000000 + 0xffffc8c8ffffc8c8) * 0x10000000000000000 + 0xffffc8c8ffffc8c8)
  | 298 => ((((((0x82082082082082 * 0x10000000000000000 + 0x0820820820820820) * 0x10000000000000000 + 0x820820820fffffff) * 0x10000000000000000 + 0xffffffffffffffff) * 0x10000000000000000 + 0xffc003ffc0fc003f) * 0x10000000000000000 + 0xffffcc88ffffcc88) * 0x10000000000000000 + 0xffffcc88ffffcc88)
  | 299 => ((((((0x82082082082082 * 0x10000000000000000 + 0x0820820820820820) * 0x10000000000000000 + 0x820820820fffffff) * 0x10000000000000000 + 0xffffffffffffffff) * 0x10000000000000000 + 0xffff000000ffffc0) * 0x10000000000000000 + 0xffffe0e0ffffe0e0) * 0x10000000000000000 + 0xffffe0e0ffffe0e0)
  | 300 => ((((((0x82082082082082 * 0x10000000000000000 + 0x0820820820820820) * 0x10000000000000000 + 0x820820820fffffff) * 0x10000000000000000 + 0xffffffffffffffff) * 0x10000000000000000 + 0xffff03ffff000000) * 0x10000000000000000 + 0xffffee00ffffee00) * 0x10000000000000000 + 0xffffee00ffffee00)
  | 301 => ((((((0x82082082082082 * 0x10000000000000000 + 0x0820820820820820) * 0x10000000000000000 + 0x820820820fffffff) * 0x10000000000000000 + 0xffffffffffffffff) * 0x10000000000000000 + 0xffff03ffffffffc0) * 0x10000000000000000 + 0xffffeee0ffffeee0) * 0x10000000000000000 + 0xffffeee0ffffeee0)
  | 302 => ((((((0x82082082082082 * 0x10000000000000000 + 0x0820820820820820) * 0x10000000000000000 + 0x820820820fffffff) * 0x10000000000000000 + 0xffffffffffffffff) * 0x10000000000000000 + 0xfffffff03ffff03f) * 0x10000000000000000 + 0xfffffac8fffffac8) * 0x10000000000000000 + 0xfffffac8fffffac8)
  | 303 => ((((((0x82082082082082 * 0x10000000000000000 + 0x0820820820820820) * 0x10000000000000000 + 0x820820820fffffff) * 0x10000000000000000 + 0xffffffffffffffff) * 0x10000000000000000 + 0xffffffffc0fc0fff) * 0x10000000000000000 + 0xfffffca8fffffca8) * 0x10000000000000000 + 0xfffffca8fffffca8)
  | 304 => ((((((0x8a28a28a28a28a * 0x10000000000000000 + 0x28a28a28a28a28a2) * 0x10000000000000000 + 0x8a28a28a20000000) * 0x10000000000000000 + 0x00000000000ffffc) * 0x10000000000000000 + 0x000000000000003f) * 0x10000000000000000 + 0x000f000a000f000a) * 0x10000000000000000 + 0x000f000a000f000a)
  | 305 => ((((((0x8a28a28a28a28a * 0x10000000000000000 + 0x28a28a28a28a28a2) * 0x10000000000000000 + 0x8a28a28a20000000) * 0x10000000000000000 + 0x00000000fff000fc) * 0x10000000000000000 + 0x0000000000000fc0) * 0x10000000000000000 + 0x0033002200330022) * 0x10000000000000000 + 0x0033002200330022)
  | 306 => ((((((0x8a28a28a28a28a * 0x10000000000000000 + 0x28a28a28a28a28a2) * 0x10000000000000000 + 0x8a28a28a20000000) * 0x10000000000000000 + 0x00000ffffffffffc) * 0x10000000000000000 + 0x0000000000000fc0) * 0x10000000000000000 + 0x00ff002200ff0022) * 0x10000000000000000 + 0x00ff002200ff0022)
  | 307 => ((((((0x8a28a28a28a28a * 0x10000000000000000 + 0x28a28a28a28a28a2) * 0x10000000000000000 + 0x8a28a28a20000000) * 0x10000000000000000 + 0x00000ffffffffffc) * 0x10000000000000000 + 0x0000000000fc0fff) * 0x10000000000000000 + 0x00ff00aa00ff00aa) * 0x10000000000000000 + 0x00ff00aa00ff00aa)
  | 308 => ((((((0x8a28a28a28a28a * 0x10000000000000000 + 0x28a28a28a28a28a2) * 0x10000000000000000 + 0x8a28a28a20000000) * 0x10000000000000000 + 0x00fff000000000fc) * 0x10000000000000000 + 0x000000003f000000) * 0x10000000000000000 + 0x0303020203030202) * 0x10000000000000000 + 0x0303020203030202)
  | 309 => ((((((0x8a28a28a28a28a * 0x10000000000000000 + 0x28a28a28a28a28a2) * 0x10000000000000000 + 0x8a28a28a2000000f) * 0x10000000000000000 + 0xfffff000000ffffc) * 0x10000000000000000 + 0x000000003f000000) * 0x10000000000000000 + 0x0f0f02020f0f0202) * 0x10000000000000000 + 0x0f0f02020f0f0202)
  | 310 => ((((((0x8a28a28a28a28a * 0x10000000000000000 + 0x28a28a28a28a28a2) * 0x10000000000000000 + 0x8a28a28a2000000f) * 0x10000000000000000 + 0xfffff000000ffffc) * 0x10000000000000000 + 0x000003f03f00003f) * 0x10000000000000000 + 0x0f0f0a0a0f0f0a0a) * 0x10000000000000000 + 0x0f0f0a0a0f0f0a0a)
  | 311 => ((((((0x8a28a28a28a28a * 0x10000000000000000 + 0x28a28a28a28a28a2) * 0x10000000000000000 + 0x8a28a28a200003f0) * 0x10000000000000000 + 0x0003f00003f00000) * 0x10000000000000000 + 0x0000000000fc0fff) * 0x10000000000000000 + 0x111100aa111100aa) * 0x10000000000000000 + 0x111100aa111100aa)
  | 312 => ((((((0x8a28a28a28a28a * 0x10000000000000000 + 0x28a28a28a28a28a2) * 0x10000000000000000 + 0x8a28a28a200003f0) * 0x10000000000000000 + 0x0003f00003f00000) * 0x10000000000000000 + 0x000003f03f00003f) * 0x10000000000000000 + 0x11110a0a11110a0a) * 0x10000000000000000 + 0x11110a0a11110a0a)
  | 313 => ((((((0x8a28a28a28a28a * 0x10000000000000000 + 0x28a28a28a28a28a2) * 0x10000000000000000 + 0x8a28a28a2000fff0) * 0x10000000000000000 + 0x00fff000fff000fc) * 0x10000000000000000 + 0x0000000000000fc0) * 0x10000000000000000 + 0x3333002233330022) * 0x10000000000000000 + 0x3333002233330022)
  | 314 => ((((((0x8a28a28a28a28a * 0x10000000000000000 + 0x28a28a28a28a28a2) * 0x10000000000000000 + 0x8a28a28a2000fff0) * 0x10000000000000000 + 0x00fff000fff000fc) * 0x10000000000000000 + 0x000000003f000000) * 0x10000000000000000 + 0x3333020233330202) * 0x10000000000000000 + 0x3333020233330202)
  | 315 => ((((((0x8a28a28a28a28a * 0x10000000000000000 + 0x28a28a28a28a28a2) * 0x10000000000000000 + 0x8a28a28a2000fff0) * 0x10000000000000000 + 0x00fff000fff000fc) * 0x10000000000000000 + 0x003f00003f000fc0) * 0x10000000000000000 + 0x3333222233332222) * 0x10000000000000000 + 0x3333222233332222)
  | 316 => ((((((0x8a28a28a28a28a * 0x10000000000000000 + 0x28a28a28a28a28a2) * 0x10000000000000000 + 0x8a28a28a2fffffff) * 0x10000000000000000 + 0xffffffffffffffff) * 0x10000000000000000 + 0xf03f03f03ffc0fff) * 0x10000000000000000 + 0xffffaaaaffffaaaa) * 0x10000000000000000 + 0xffffaaaaffffaaaa)
  | 317 => ((((((0x92492492492492 * 0x10000000000000000 + 0x4924924924924924) * 0x10000000000000000 + 0x9249249240000000) * 0x10000000000000000 + 0x00000000000ffffc) * 0x10000000000000000 + 0x000000000000003f) * 0x10000000000000000 + 0x000f000c000f000c) * 0x10000000000000000 + 0x000f000c000f000c)
  | 318 => ((((((0x92492492492492 * 0x10000000000000000 + 0x4924924924924924) * 0x10000000000000000 + 0x9249249240000000) * 0x10000000000000000 + 0x0000003f03f03f00) * 0x10000000000000000 + 0x000000000003f000) * 0x10000000000000000 + 0x0055004400550044) * 0x10000000000000000 + 0x0055004400550044)
  | 319 => ((((((0x92492492492492 * 0x10000000000000000 + 0x4924924924924924) * 0x10000000000000000 + 0x9249249240000000) * 0x10000000000000000 + 0x00000ffffffffffc) * 0x10000000000000000 + 0x000000000003f000) * 0x10000000000000000 + 0x00ff004400ff0044) * 0x10000000000000000 + 0x00ff004400ff0044)
  | 320 => ((((((0x92492492492492 * 0x10000000000000000 + 0x4924924924924924) * 0x10000000000000000 + 0x9249249240000000) * 0x10000000000000000 + 0x00000ffffffffffc) * 0x10000000000000000 + 0x0000000000fff03f) * 0x10000000000000000 + 0x00ff00cc00ff00cc) * 0x10000000000000000 + 0x00ff00cc00ff00cc)
  | 321 => ((((((0x92492492492492 * 0x10000000000000000 + 0x4924924924924924) * 0x10000000000000000 + 0x9249249240000000) * 0x10000000000000000 + 0x3f03f00000003f00) * 0x10000000000000000 + 0x0000000fc0000000) * 0x10000000000000000 + 0x0505040405050404) * 0x10000000000000000 + 0x0505040405050404)
  | 322 => ((((((0x92492492492492 * 0x10000000000000000 + 0x4924924924924924) * 0x10000000000000000 + 0x924924924000000f) * 0x10000000000000000 + 0xfffff000000ffffc) * 0x10000000000000000 + 0x0000000fc0000000) * 0x10000000000000000 + 0x0f0f04040f0f0404) * 0x10000000000000000 + 0x0f0f04040f0f0404)
  | 323 => ((((((0x92492492492492 * 0x10000000000000000 + 0x4924924924924924) * 0x10000000000000000 + 0x924924924000000f) * 0x10000000000000000 + 0xfffff000000ffffc) * 0x10000000000000000 + 0x000003ffc000003f) * 0x10000000000000000 + 0x0f0f0c0c0f0f0c0c) * 0x10000000000000000 + 0x0f0f0c0c0f0f0c0c)
  | 324 => ((((((0x92492492492492 * 0x10000000000000000 + 0x4924924924924924) * 0x10000000000000000 + 0x92492492400003f0) * 0x10000000000000000 + 0x0003f00003f00000) * 0x10000000000000000 + 0x0000000000fff03f) * 0x10000000000000000 + 0x111100cc111100cc) * 0x10000000000000000 + 0x111100cc111100cc)
  | 325 => ((((((0x92492492492492 * 0x10000000000000000 + 0x4924924924924924) * 0x10000000000000000 + 0x92492492400003f0) * 0x10000000000000000 + 0x0003f00003f00000) * 0x10000000000000000 + 0x000003ffc000003f) * 0x10000000000000000 + 0x11110c0c11110c0c) * 0x10000000000000000 + 0x11110c0c11110c0c)
  | 326 => ((((((0x92492492492492 * 0x10000000000000000 + 0x4924924924924924) * 0x10000000000000000 + 0x92492492403f03f0) * 0x10000000000000000 + 0x3f03f03f03f03f00) * 0x10000000000000000 + 0x000000000003f000) * 0x10000000000000000 + 0x5555004455550044) * 0x10000000000000000 + 0x5555004455550044)
  | 327 => ((((((0x92492492492492 * 0x10000000000000000 + 0x4924924924924924) * 0x10000000000000000 + 0x92492492403f03f0) * 0x10000000000000000 + 0x3f03f03f03f03f00) * 0x10000000000000000 + 0x0000000fc0000000) * 0x10000000000000000 + 0x5555040455550404) * 0x10000000000000000 + 0x5555040455550404)
  | 328 => ((((((0x92492492492492 * 0x10000000000000000 + 0x4924924924924924) * 0x10000000000000000 + 0x92492492403f03f0) * 0x10000000000000000 + 0x3f03f03f03f03f00) * 0x10000000000000000 + 0x0fc0000fc003f000) * 0x10000000000000000 + 0x5555444455554444) * 0x10000000000000000 + 0x5555444455554444)
  | 329 => ((((((0x92492492492492 * 0x10000000000000000 + 0x4924924924924924) * 0x10000000000000000 + 0x924924924fffffff) * 0x10000000000000000 + 0xffffffffffffffff) * 0x10000000000000000 + 0xffc003ffc0fff03f) * 0x10000000000000000 + 0xffffccccffffcccc) * 0x10000000000000000 + 0xffffccccffffcccc)
  | 330 => ((((((0x9a69a69a69a69a * 0x10000000000000000 + 0x69a69a69a69a69a6) * 0x10000000000000000 + 0x9a69a69a60000000) * 0x10000000000000000 + 0x00000000000ffffc) * 0x10000000000000000 + 0x000000000000003f) * 0x10000000000000000 + 0x000f000e000f000e) * 0x10000000000000000 + 0x000f000e000f000e)
  | 331 => ((((((0x9a69a69a69a69a * 0x10000000000000000 + 0x69a69a69a69a69a6) * 0x10000000000000000 + 0x9a69a69a60000000) * 0x10000000000000000 + 0x00000ffffffffffc) * 0x10000000000000000 + 0x000000000000003f) * 0x10000000000000000 + 0x00ff000e00ff000e) * 0x10000000000000000 + 0x00ff000e00ff000e)
  | 332 => ((((((0x9a69a69a69a69a * 0x10000000000000000 + 0x69a69a69a69a69a6) * 0x10000000000000000 + 0x9a69a69a60000000) * 0x10000000000000000 + 0x00000ffffffffffc) * 0x10000000000000000 + 0x0000000000ffffff) * 0x10000000000000000 + 0x00ff00ee00ff00ee) * 0x10000000000000000 + 0x00ff00ee00ff00ee)
  | 333 => ((((((0x9a69a69a69a69a * 0x10000000000000000 + 0x69a69a69a69a69a6) * 0x10000000000000000 + 0x9a69a69a6000000f) * 0x10000000000000000 + 0xfffff000000ffffc) * 0x10000000000000000 + 0x000000000000003f) * 0x10000000000000000 + 0x0f0f000e0f0f000e) * 0x10000000000000000 + 0x0f0f000e0f0f000e)
  | 334 => ((((((0x9a69a69a69a69a * 0x10000000000000000 + 0x69a69a69a69a69a6) * 0x10000000000000000 + 0x9a69a69a6000000f) * 0x10000000000000000 + 0xfffff000000ffffc) * 0x10000000000000000 + 0x000003ffff00003f) * 0x10000000000000000 + 0x0f0f0e0e0f0f0e0e) * 0x10000000000000000 + 0x0f0f0e0e0f0f0e0e)
  | 335 => ((((((0x9a69a69a69a69a * 0x10000000000000000 + 0x69a69a69a69a69a6) * 0x10000000000000000 + 0x9a69a69a600003f0) * 0x10000000000000000 + 0x0003f00003f00000) * 0x10000000000000000 + 0x0000000000ffffff) * 0x10000000000000000 + 0x111100ee111100ee) * 0x10000000000000000 + 0x111100ee111100ee)
  | 336 => ((((((0x9a69a69a69a69a * 0x10000000000000000 + 0x69a69a69a69a69a6) * 0x10000000000000000 + 0x9a69a69a600003f0) * 0x10000000000000000 + 0x0003f00003f00000) * 0x10000000000000000 + 0x000003ffff00003f) * 0x10000000000000000 + 0x11110e0e11110e0e) * 0x10000000000000000 + 0x11110e0e11110e0e)
  | 337 => ((((((0x9a69a69a69a69a * 0x10000000000000000 + 0x69a69a69a69a69a6) * 0x10000000000000000 + 0x9a69a69a6fffffff) * 0x10000000000000000 + 0xfffffffffffffffc) * 0x10000000000000000 + 0x000000000000003f) * 0x10000000000000000 + 0xffff000effff000e) * 0x10000000000000000 + 0xffff000effff000e)
  | 338 => ((((((0x9a69a69a69a69a * 0x10000000000000000 + 0x69a69a69a69a69a6) * 0x10000000000000000 + 0x9a69a69a6fffffff) * 0x10000000000000000 + 0xfffffffffffffffc) * 0x10000000000000000 + 0x0000000000ffffff) * 0x10000000000000000 + 0xffff00eeffff00ee) * 0x10000000000000000 + 0xffff00eeffff00ee)
  | 339 => ((((((0x9a69a69a69a69a * 0x10000000000000000 + 0x69a69a69a69a69a6) * 0x10000000000000000 + 0x9a69a69a6fffffff) * 0x10000000000000000 + 0xfffffffffffffffc) * 0x10000000000000000 + 0x000003ffff00003f) * 0x10000000000000000 + 0xffff0e0effff0e0e) * 0x10000000000000000 + 0xffff0e0effff0e0e)
  | 340 => ((((((0x9a69a69a69a69a * 0x10000000000000000 + 0x69a69a69a69a69a6) * 0x10000000000000000 + 0x9a69a69a6fffffff) * 0x10000000000000000 + 0xffffffffffffffff) * 0x10000000000000000 + 0xffff03ffffffffff) * 0x10000000000000000 + 0xffffeeeeffffeeee) * 0x10000000000000000 + 0xffffeeeeffffeeee)
  | 341 => ((((((0xa28a28a28a28a2 * 0x10000000000000000 + 0x8a28a28a28a28a28) * 0x10000000000000000 + 0xa28a28a280000000) * 0x10000000000000000 + 0x0000000003f00000) * 0x10000000000000000 + 0x0000000000000000) * 0x10000000000000000 + 0x0011001000110010) * 0x10000000000000000 + 0x0011001000110010)
  | 342 => ((((((0xa28a28a28a28a2 * 0x10000000000000000 + 0x8a28a28a28a28a28) * 0x10000000000000000 + 0xa28a28a280000000) * 0x10000000000000000 + 0x00000ffffffffffc) * 0x10000000000000000 + 0x0000000000ffffc0) * 0x10000000000000000 + 0x00ff00f000ff00f0) * 0x10000000000000000 + 0x00ff00f000ff00f0)
  | 343 => ((((((0xa28a28a28a28a2 * 0x10000000000000000 + 0x8a28a28a28a28a28) * 0x10000000000000000 + 0xa28a28a280000000) * 0x10000000000000000 + 0x00fff000000000fc) * 0x10000000000000000 + 0x0fc0fc000003f000) * 0x10000000000000000 + 0x0303505003035050) * 0x10000000000000000 + 0x0303505003035050)
  | 344 => ((((((0xa28a28a28a28a2 * 0x10000000000000000 + 0x8a28a28a28a28a28) * 0x10000000000000000 + 0xa28a28a280000000) * 0x10000000000000000 + 0x3f03f00000003f00) * 0x10000000000000000 + 0x003ffc0000000fc0) * 0x10000000000000000 + 0x0505303005053030) * 0x10000000000000000 + 0x0505303005053030)
  | 345 => ((((((0xa28a28a28a28a2 * 0x10000000000000000 + 0x8a28a28a28a28a28) * 0x10000000000000000 + 0xa28a28a2800003f0) * 0x10000000000000000 + 0x0003f00003f00000) * 0x10000000000000000 + 0x0000fc0000000000) * 0x10000000000000000 + 0x1111101011111010) * 0x10000000000000000 + 0x1111101011111010)
  | 346 => ((((((0xa28a28a28a28a2 * 0x10000000000000000 + 0x8a28a28a28a28a28) * 0x10000000000000000 + 0xa28a28a28fffffff) * 0x10000000000000000 + 0xfffff00003f00003) * 0x10000000000000000 + 0xfffffc0000000000) * 0x10000000000000000 + 0xff11f010ff11f010) * 0x10000000000000000 + 0xff11f010ff11f010)
  | 347 => ((((((0xa28a28a28a28a2 * 0x10000000000000000 + 0x8a28a28a28a28a28) * 0x10000000000000000 + 0xa28a28a28fffffff) * 0x10000000000000000 + 0xffffffffffffffff) * 0x10000000000000000 + 0xfffffc0000ffffc0) * 0x10000000000000000 + 0xfffff0f0fffff0f0) * 0x10000000000000000 + 0xfffff0f0fffff0f0)
  | 348 => ((((((0xaaaaaaaaaaaaaa * 0x10000000000000000 + 0xaaaaaaaaaaaaaaaa) * 0x10000000000000000 + 0xaaaaaaaaa0000000) * 0x10000000000000000 + 0x00000ffffffffffc) * 0x10000000000000000 + 0x0000000000ffffff) * 0x10000000000000000 + 0x00ff00fa00ff00fa) * 0x10000000000000000 + 0x00ff00fa00ff00fa)
  | 349 => ((((((0xaaaaaaaaaaaaaa * 0x10000000000000000 + 0xaaaaaaaaaaaaaaaa) * 0x10000000000000000 + 0xaaaaaaaaa00003f0) * 0x10000000000000000 + 0x0003f00003f00000) * 0x10000000000000000 + 0x0000fff03f00003f) * 0x10000000000000000 + 0x11111a1a11111a1a) * 0x10000000000000000 + 0x11111a1a11111a1a)
  | 350 => ((((((0xaaaaaaaaaaaaaa * 0x10000000000000000 + 0xaaaaaaaaaaaaaaaa) * 0x10000000000000000 + 0xaaaaaaaaa000fff0) * 0x10000000000000000 + 0x00fff000fff000fc) * 0x10000000000000000 + 0x003ffc003f000fc0) * 0x10000000000000000 + 0x3333323233333232) * 0x10000000000000000 + 0x3333323233333232)
  | 351 => ((((((0xaaaaaaaaaaaaaa * 0x10000000000000000 + 0xaaaaaaaaaaaaaaaa) * 0x10000000000000000 + 0xaaaaaaaaafc0fc0f) * 0x10000000000000000 + 0xc0fc0fffffffffff) * 0x10000000000000000 + 0xf03f03f03fffffff) * 0x10000000000000000 + 0xaaffaafaaaffaafa) * 0x10000000000000000 + 0xaaffaafaaaffaafa)
  | 352 => ((((((0xaaaaaaaaaaaaaa * 0x10000000000000000 + 0xaaaaaaaaaaaaaaaa) * 0x10000000000000000 + 0xaaaaaaaaafc0ffff) * 0x10000000000000000 + 0xc0ffffc0ffffc0ff) * 0x10000000000000000 + 0xf03ffff03ffc0fff) * 0x10000000000000000 + 0xbbbbbababbbbbaba) * 0x10000000000000000 + 0xbbbbbababbbbbaba)
  | 353 => ((((((0xaaaaaaaaaaaaaa * 0x10000000000000000 + 0xaaaaaaaaaaaaaaaa) * 0x10000000000000000 + 0xaaaaaaaaaffffff0) * 0x10000000000000000 + 0x00000fffffffffff) * 0x10000000000000000 + 0xfffffc0000ffffff) * 0x10000000000000000 + 0xf0fff0faf0fff0fa) * 0x10000000000000000 + 0xf0fff0faf0fff0fa)
  | 354 => ((((((0xaaaaaaaaaaaaaa * 0x10000000000000000 + 0xaaaaaaaaaaaaaaaa) * 0x10000000000000000 + 0xaaaaaaaaaffffff0) * 0x10000000000000000 + 0x00fffffffff000ff) * 0x10000000000000000 + 0xfffffc003fffffc0) * 0x10000000000000000 + 0xf3f3f2f2f3f3f2f2) * 0x10000000000000000 + 0xf3f3f2f2f3f3f2f2)
  | 355 => ((((((0xaaaaaaaaaaaaaa * 0x10000000000000000 + 0xaaaaaaaaaaaaaaaa) * 0x10000000000000000 + 0xaaaaaaaaafffffff) * 0x10000000000000000 + 0xfffffffffffffffc) * 0x10000000000000000 + 0x0000000000ffffff) * 0x10000000000000000 + 0xffff00faffff00fa) * 0x10000000000000000 + 0xffff00faffff00fa)
  | 356 => ((((((0xaaaaaaaaaaaaaa * 0x10000000000000000 + 0xaaaaaaaaaaaaaaaa) * 0x10000000000000000 + 0xaaaaaaaaafffffff) * 0x10000000000000000 + 0xfffffffffffffffc) * 0x10000000000000000 + 0x003ffc003f000fc0) * 0x10000000000000000 + 0xffff3232ffff3232) * 0x10000000000000000 + 0xffff3232ffff3232)
  | 357 => ((((((0xaaaaaaaaaaaaaa * 0x10000000000000000 + 0xaaaaaaaaaaaaaaaa) * 0x10000000000000000 + 0xaaaaaaaaafffffff) * 0x10000000000000000 + 0xffffffffffffffff) * 0x10000000000000000 + 0xfffffff03fffffff) * 0x10000000000000000 + 0xfffffafafffffafa) * 0x10000000000000000 + 0xfffffafafffffafa)
  | 358 => ((((((0xb2cb2cb2cb2cb2 * 0x10000000000000000 + 0xcb2cb2cb2cb2cb2c) * 0x10000000000000000 + 0xb2cb2cb2c0000000) * 0x10000000000000000 + 0x00000ffffffffffc) * 0x10000000000000000 + 0x0000000000ffffff) * 0x10000000000000000 + 0x00ff00fc00ff00fc) * 0x10000000000000000 + 0x00ff00fc00ff00fc)
  | 359 => ((((((0xb2cb2cb2cb2cb2 * 0x10000000000000000 + 0xcb2cb2cb2cb2cb2c) * 0x10000000000000000 + 0xb2cb2cb2c00003f0) * 0x10000000000000000 + 0x0003f00003f00000) * 0x10000000000000000 + 0x0000ffffc000003f) * 0x10000000000000000 + 0x11111c1c11111c1c) * 0x10000000000000000 + 0x11111c1c11111c1c)
  | 360 => ((((((0xb2cb2cb2cb2cb2 * 0x10000000000000000 + 0xcb2cb2cb2cb2cb2c) * 0x10000000000000000 + 0xb2cb2cb2c03f03f0) * 0x10000000000000000 + 0x3f03f03f03f03f00) * 0x10000000000000000 + 0x0fc0fc0fc003f000) * 0x10000000000000000 + 0x5555545455555454) * 0x10000000000000000 + 0x5555545455555454)
  | 361 => ((((((0xb2cb2cb2cb2cb2 * 0x10000000000000000 + 0xcb2cb2cb2cb2cb2c) * 0x10000000000000000 + 0xb2cb2cb2cfff000f) * 0x10000000000000000 + 0xff000fffffffffff) * 0x10000000000000000 + 0xffc003ffc0ffffff) * 0x10000000000000000 + 0xccffccfcccffccfc) * 0x10000000000000000 + 0xccffccfcccffccfc)
  | 362 => ((((((0xb2cb2cb2cb2cb2 * 0x10000000000000000 + 0xcb2cb2cb2cb2cb2c) * 0x10000000000000000 + 0xb2cb2cb2cfff03ff) * 0x10000000000000000 + 0xff03ffff03ffff03) * 0x10000000000000000 + 0xffc0ffffc0fff03f) * 0x10000000000000000 + 0xdddddcdcdddddcdc) * 0x10000000000000000 + 0xdddddcdcdddddcdc)
  | 363 => ((((((0xb2cb2cb2cb2cb2 * 0x10000000000000000 + 0xcb2cb2cb2cb2cb2c) * 0x10000000000000000 + 0xb2cb2cb2cffffff0) * 0x10000000000000000 + 0x00000fffffffffff) * 0x10000000000000000 + 0xfffffc0000ffffff) * 0x10000000000000000 + 0xf0fff0fcf0fff0fc) * 0x10000000000000000 + 0xf0fff0fcf0fff0fc)
  | 364 => ((((((0xb2cb2cb2cb2cb2 * 0x10000000000000000 + 0xcb2cb2cb2cb2cb2c) * 0x10000000000000000 + 0xb2cb2cb2cffffff0) * 0x10000000000000000 + 0x3f03fffffff03f03) * 0x10000000000000000 + 0xfffffc0fc0ffffc0) * 0x10000000000000000 + 0xf5f5f4f4f5f5f4f4) * 0x10000000000000000 + 0xf5f5f4f4f5f5f4f4)
  | 365 => ((((((0xb2cb2cb2cb2cb2 * 0x10000000000000000 + 0xcb2cb2cb2cb2cb2c) * 0x10000000000000000 + 0xb2cb2cb2cfffffff) * 0x10000000000000000 + 0xfffffffffffffffc) * 0x10000000000000000 + 0x0000000000ffffff) * 0x10000000000000000 + 0xffff00fcffff00fc) * 0x10000000000000000 + 0xffff00fcffff00fc)
  | 366 => ((((((0xb2cb2cb2cb2cb2 * 0x10000000000000000 + 0xcb2cb2cb2cb2cb2c) * 0x10000000000000000 + 0xb2cb2cb2cfffffff) * 0x10000000000000000 + 0xfffffffffffffffc) * 0x10000000000000000 + 0x0fc0fc0fc003f000) * 0x10000000000000000 + 0xffff5454ffff5454) * 0x10000000000000000 + 0xffff5454ffff5454)
  | 367 => ((((((0xb2cb2cb2cb2cb2 * 0x10000000000000000 + 0xcb2cb2cb2cb2cb2c) * 0x10000000000000000 + 0xb2cb2cb2cfffffff) * 0x10000000000000000 + 0xffffffffffffffff) * 0x10000000000000000 + 0xffffffffc0ffffff) * 0x10000000000000000 + 0xfffffcfcfffffcfc) * 0x10000000000000000 + 0xfffffcfcfffffcfc)
  | 368 => ((((((0xbaebaebaebaeba * 0x10000000000000000 + 0xebaebaebaebaebae) * 0x10000000000000000 + 0xbaebaebae0000000) * 0x10000000000000000 + 0x00000ffffffffffc) * 0x10000000000000000 + 0x0000000000ffffff) * 0x10000000000000000 + 0x00ff00fe00ff00fe) * 0x10000000000000000 + 0x00ff00fe00ff00fe)
  | 369 => ((((((0xbaebaebaebaeba * 0x10000000000000000 + 0xebaebaebaebaebae) * 0x10000000000000000 + 0xbaebaebaeffffc0f) * 0x10000000000000000 + 0xfffc0fffffffffff) * 0x10000000000000000 + 0xffff03ffffffffff) * 0x10000000000000000 + 0xeeffeefeeeffeefe) * 0x10000000000000000 + 0xeeffeefeeeffeefe)
  | 370 => ((((((0xbaebaebaebaeba * 0x10000000000000000 + 0xebaebaebaebaebae) * 0x10000000000000000 + 0xbaebaebaeffffff0) * 0x10000000000000000 + 0x00000fffffffffff) * 0x10000000000000000 + 0xfffffc0000ffffff) * 0x10000000000000000 + 0xf0fff0fef0fff0fe) * 0x10000000000000000 + 0xf0fff0fef0fff0fe)
  | 371 => ((((((0xbaebaebaebaeba * 0x10000000000000000 + 0xebaebaebaebaebae) * 0x10000000000000000 + 0xbaebaebaefffffff) * 0x10000000000000000 + 0xfffffffffffffffc) * 0x10000000000000000 + 0x0000000000ffffff) * 0x10000000000000000 + 0xffff00feffff00fe) * 0x10000000000000000 + 0xffff00feffff00fe)
  | 372 => ((((((0xbaebaebaebaeba * 0x10000000000000000 + 0xebaebaebaebaebae) * 0x10000000000000000 + 0xbaebaebaefffffff) * 0x10000000000000000 + 0xffffffffffffffff) * 0x10000000000000000 + 0xfffffc0000ffffff) * 0x10000000000000000 + 0xfffff0fefffff0fe) * 0x10000000000000000 + 0xfffff0fefffff0fe)
  | 373 => ((((((0xbaebaebaebaeba * 0x10000000000000000 + 0xebaebaebaebaebae) * 0x10000000000000000 + 0xbaebaebaefffffff) * 0x10000000000000000 + 0xffffffffffffffff) * 0x10000000000000000 + 0xffffffffffffffff) * 0x10000000000000000 + 0xfffffefefffffefe) * 0x10000000000000000 + 0xfffffefefffffefe)
  | 374 => ((((((0xc30c30c30c30c3 * 0x10000000000000000 + 0x0c30c30c30c30c30) * 0x10000000000000000 + 0xc30c30c300000000) * 0x10000000000000000 + 0x00000000fff000fc) * 0x10000000000000000 + 0x0fc0fc0fc0000000) * 0x10000000000000000 + 0x0033550000335500) * 0x10000000000000000 + 0x0033550000335500)
  | 375 => ((((((0xc30c30c30c30c3 * 0x10000000000000000 + 0x0c30c30c30c30c30) * 0x10000000000000000 + 0xc30c30c300000000) * 0x10000000000000000 + 0x0000003f03f03f00) * 0x10000000000000000 + 0x003ffc003f000000) * 0x10000000000000000 + 0x0055330000553300) * 0x10000000000000000 + 0x0055330000553300)
  | 376 => ((((((0xc30c30c30c30c3 * 0x10000000000000000 + 0x0c30c30c30c30c30) * 0x10000000000000000 + 0xc30c30c300000000) * 0x10000000000000000 + 0x0003f00000000000) * 0x10000000000000000 + 0x0000000000000000) * 0x10000000000000000 + 0x0101010001010100) * 0x10000000000000000 + 0x0101010001010100)
  | 377 => ((((((0xc30c30c30c30c3 * 0x10000000000000000 + 0x0c30c30c30c30c30) * 0x10000000000000000 + 0xc30c30c30000000f) * 0x10000000000000000 + 0xfffff000000ffffc) * 0x10000000000000000 + 0x000003ffff000000) * 0x10000000000000000 + 0x0f0f0f000f0f0f00) * 0x10000000000000000 + 0x0f0f0f000f0f0f00)
  | 378 => ((((((0xc30c30c30c30c3 * 0x10000000000000000 + 0x0c30c30c30c30c30) * 0x10000000000000000 + 0xc30c30c3000003f0) * 0x10000000000000000 + 0x0003f00003f00000) * 0x10000000000000000 + 0x0000fc0000000000) * 0x10000000000000000 + 0x1111110011111100) * 0x10000000000000000 + 0x1111110011111100)
  | 379 => ((((((0xc30c30c30c30c3 * 0x10000000000000000 + 0x0c30c30c30c30c30) * 0x10000000000000000 + 0xc30c30c30ffffff0) * 0x10000000000000000 + 0x0003fffffff00003) * 0x10000000000000000 + 0xfffffc0000000000) * 0x10000000000000000 + 0xf1f1f100f1f1f100) * 0x10000000000000000 + 0xf1f1f100f1f1f100)
  | 380 => ((((((0xc30c30c30c30c3 * 0x10000000000000000 + 0x0c30c30c30c30c30) * 0x10000000000000000 + 0xc30c30c30fffffff) * 0x10000000000000000 + 0xffffffffffffffff) * 0x10000000000000000 + 0xffffffffff000000) * 0x10000000000000000 + 0xffffff00ffffff00) * 0x10000000000000000 + 0xffffff00ffffff00)
  | 381 => ((((((0xcb2cb2cb2cb2cb * 0x10000000000000000 + 0x2cb2cb2cb2cb2cb2) * 0x10000000000000000 + 0xcb2cb2cb2000000f) * 0x10000000000000000 + 0xfffff000000ffffc) * 0x10000000000000000 + 0x000003ffff00003f) * 0x10000000000000000 + 0x0f0f0f0a0f0f0f0a) * 0x10000000000000000 + 0x0f0f0f0a0f0f0f0a)
  | 382 => ((((((0xcb2cb2cb2cb2cb * 0x10000000000000000 + 0x2cb2cb2cb2cb2cb2) * 0x10000000000000000 + 0xcb2cb2cb200003f0) * 0x10000000000000000 + 0x0003f00003f00000) * 0x10000000000000000 + 0x0000fc0000fc0fff) * 0x10000000000000000 + 0x111111aa111111aa) * 0x10000000000000000 + 0x111111aa111111aa)
  | 383 => ((((((0xcb2cb2cb2cb2cb * 0x10000000000000000 + 0x2cb2cb2cb2cb2cb2) * 0x10000000000000000 + 0xcb2cb2cb2000fff0) * 0x10000000000000000 + 0x00fff000fff000fc) * 0x10000000000000000 + 0x003ffc003f000fc0) * 0x10000000000000000 + 0x3333332233333322) * 0x10000000000000000 + 0x3333332233333322)
  | 384 => ((((((0xcb2cb2cb2cb2cb * 0x10000000000000000 + 0x2cb2cb2cb2cb2cb2) * 0x10000000000000000 + 0xcb2cb2cb2fc0fc0f) * 0x10000000000000000 + 0xffffffc0fc0fffff) * 0x10000000000000000 + 0xf03f03fffffc0fff) * 0x10000000000000000 + 0xafafafaaafafafaa) * 0x10000000000000000 + 0xafafafaaafafafaa)
  | 385 => ((((((0xcb2cb2cb2cb2cb * 0x10000000000000000 + 0x2cb2cb2cb2cb2cb2) * 0x10000000000000000 + 0xcb2cb2cb2fc0ffff) * 0x10000000000000000 + 0xc0ffffc0ffffc0ff) * 0x10000000000000000 + 0xf03ffff03ffc0fff) * 0x10000000000000000 + 0xbbbbbbaabbbbbbaa) * 0x10000000000000000 + 0xbbbbbbaabbbbbbaa)
  | 386 => ((((((0xcb2cb2cb2cb2cb * 0x10000000000000000 + 0x2cb2cb2cb2cb2cb2) * 0x10000000000000000 + 0xcb2cb2cb2fffffff) * 0x10000000000000000 + 0xfffff000000fffff) * 0x10000000000000000 + 0xffffffffff00003f) * 0x10000000000000000 + 0xff0fff0aff0fff0a) * 0x10000000000000000 + 0xff0fff0aff0fff0a)
  | 387 => ((((((0xcb2cb2cb2cb2cb * 0x10000000000000000 + 0x2cb2cb2cb2cb2cb2) * 0x10000000000000000 + 0xcb2cb2cb2fffffff) * 0x10000000000000000 + 0xfffff000fff000ff) * 0x10000000000000000 + 0xffffffffff000fc0) * 0x10000000000000000 + 0xff33ff22ff33ff22) * 0x10000000000000000 + 0xff33ff22ff33ff22)
  | 388 => ((((((0xcb2cb2cb2cb2cb * 0x10000000000000000 + 0x2cb2cb2cb2cb2cb2) * 0x10000000000000000 + 0xcb2cb2cb2fffffff) * 0x10000000000000000 + 0xfffffffffffffffc) * 0x10000000000000000 + 0x000003ffff00003f) * 0x10000000000000000 + 0xffff0f0affff0f0a) * 0x10000000000000000 + 0xffff0f0affff0f0a)
  | 389 => ((((((0xcb2cb2cb2cb2cb * 0x10000000000000000 + 0x2cb2cb2cb2cb2cb2) * 0x10000000000000000 + 0xcb2cb2cb2fffffff) * 0x10000000000000000 + 0xfffffffffffffffc) * 0x10000000000000000 + 0x003ffc003f000fc0) * 0x10000000000000000 + 0xffff3322ffff3322) * 0x10000000000000000 + 0xffff3322ffff3322)
  | 390 => ((((((0xcb2cb2cb2cb2cb * 0x10000000000000000 + 0x2cb2cb2cb2cb2cb2) * 0x10000000000000000 + 0xcb2cb2cb2fffffff) * 0x10000000000000000 + 0xffffffffffffffff) * 0x10000000000000000 + 0xfffffffffffc0fff) * 0x10000000000000000 + 0xffffffaaffffffaa) * 0x10000000000000000 + 0xffffffaaffffffaa)
  | 391 => ((((((0xd34d34d34d34d3 * 0x10000000000000000 + 0x4d34d34d34d34d34) * 0x10000000000000000 + 0xd34d34d34000000f) * 0x10000000000000000 + 0xfffff000000ffffc) * 0x10000000000000000 + 0x000003ffff00003f) * 0x10000000000000000 + 0x0f0f0f0c0f0f0f0c) * 0x10000000000000000 + 0x0f0f0f0c0f0f0f0c)
  | 392 => ((((((0xd34d34d34d34d3 * 0x10000000000000000 + 0x4d34d34d34d34d34) * 0x10000000000000000 + 0xd34d34d3400003f0) * 0x10000000000000000 + 0x0003f00003f00000) * 0x10000000000000000 + 0x0000fc0000fff03f) * 0x10000000000000000 + 0x111111cc111111cc) * 0x10000000000000000 + 0x111111cc111111cc)
  | 393 => ((((((0xd34d34d34d34d3 * 0x10000000000000000 + 0x4d34d34d34d34d34) * 0x10000000000000000 + 0xd34d34d3403f03f0) * 0x10000000000000000 + 0x3f03f03f03f03f00) * 0x10000000000000000 + 0x0fc0fc0fc003f000) * 0x10000000000000000 + 0x5555554455555544) * 0x10000000000000000 + 0x5555554455555544)
  | 394 => ((((((0xd34d34d34d34d3 * 0x10000000000000000 + 0x4d34d34d34d34d34) * 0x10000000000000000 + 0xd34d34d34fff000f) * 0x10000000000000000 + 0xffffffff000fffff) * 0x10000000000000000 + 0xffc003fffffff03f) * 0x10000000000000000 + 0xcfcfcfcccfcfcfcc) * 0x10000000000000000 + 0xcfcfcfcccfcfcfcc)
  | 395 => ((((((0xd34d34d34d34d3 * 0x10000000000000000 + 0x4d34d34d34d34d34) * 0x10000000000000000 + 0xd34d34d34fff03ff) * 0x10000000000000000 + 0xff03ffff03ffff03) * 0x10000000000000000 + 0xffc0ffffc0fff03f) * 0x10000000000000000 + 0xddddddccddddddcc) * 0x10000000000000000 + 0xddddddccddddddcc)
  | 396 => ((((((0xd34d34d34d34d3 * 0x10000000000000000 + 0x4d34d34d34d34d34) * 0x10000000000000000 + 0xd34d34d34fffffff) * 0x10000000000000000 + 0xfffff000000fffff) * 0x10000000000000000 + 0xffffffffff00003f) * 0x10000000000000000 + 0xff0fff0cff0fff0c) * 0x10000000000000000 + 0xff0fff0cff0fff0c)
  | 397 => ((((((0xd34d34d34d34d3 * 0x10000000000000000 + 0x4d34d34d34d34d34) * 0x10000000000000000 + 0xd34d34d34fffffff) * 0x10000000000000000 + 0xfffff03f03f03f03) * 0x10000000000000000 + 0xffffffffff03f000) * 0x10000000000000000 + 0xff55ff44ff55ff44) * 0x10000000000000000 + 0xff55ff44ff55ff44)
  | 398 => ((((((0xd34d34d34d34d3 * 0x10000000000000000 + 0x4d34d34d34d34d34) * 0x10000000000000000 + 0xd34d34d34fffffff) * 0x10000000000000000 + 0xfffffffffffffffc) * 0x10000000000000000 + 0x000003ffff00003f) * 0x10000000000000000 + 0xffff0f0cffff0f0c) * 0x10000000000000000 + 0xffff0f0cffff0f0c)
  | 399 => ((((((0xd34d34d34d34d3 * 0x10000000000000000 + 0x4d34d34d34d34d34) * 0x10000000000000000 + 0xd34d34d34fffffff) * 0x10000000000000000 + 0xfffffffffffffffc) * 0x10000000000000000 + 0x0fc0fc0fc003f000) * 0x10000000000000000 + 0xffff5544ffff5544) * 0x10000000000000000 + 0xffff5544ffff5544)
  | 400 => ((((((0xd34d34d34d34d3 * 0x10000000000000000 + 0x4d34d34d34d34d34) * 0x10000000000000000 + 0xd34d34d34fffffff) * 0x10000000000000000 + 0xffffffffffffffff) * 0x10000000000000000 + 0xfffffffffffff03f) * 0x10000000000000000 + 0xffffffccffffffcc) * 0x10000000000000000 + 0xffffffccffffffcc)
  | 401 => ((((((0xdb6db6db6db6db * 0x10000000000000000 + 0x6db6db6db6db6db6) * 0x10000000000000000 + 0xdb6db6db6000000f) * 0x10000000000000000 + 0xfffff000000ffffc) * 0x10000000000000000 + 0x000003ffff00003f) * 0x10000000000000000 + 0x0f0f0f0e0f0f0f0e) * 0x10000000000000000 + 0x0f0f0f0e0f0f0f0e)
  | 402 => ((((((0xdb6db6db6db6db * 0x10000000000000000 + 0x6db6db6db6db6db6) * 0x10000000000000000 + 0xdb6db6db6ffffc0f) * 0x10000000000000000 + 0xfffffffffc0fffff) * 0x10000000000000000 + 0xffff03ffffffffff) * 0x10000000000000000 + 0xefefefeeefefefee) * 0x10000000000000000 + 0xefefefeeefefefee)
  | 403 => ((((((0xdb6db6db6db6db * 0x10000000000000000 + 0x6db6db6db6db6db6) * 0x10000000000000000 + 0xdb6db6db6fffffff) * 0x10000000000000000 + 0xfffff000000fffff) * 0x10000000000000000 + 0xffffffffff00003f) * 0x10000000000000000 + 0xff0fff0eff0fff0e) * 0x10000000000000000 + 0xff0fff0eff0fff0e)
  | 404 => ((((((0xdb6db6db6db6db * 0x10000000000000000 + 0x6db6db6db6db6db6) * 0x10000000000000000 + 0xdb6db6db6fffffff) * 0x10000000000000000 + 0xfffffffffffffffc) * 0x10000000000000000 + 0x000003ffff00003f) * 0x10000000000000000 + 0xffff0f0effff0f0e) * 0x10000000000000000 + 0xffff0f0effff0f0e)
  | 405 => ((((((0xdb6db6db6db6db * 0x10000000000000000 + 0x6db6db6db6db6db6) * 0x10000000000000000 + 0xdb6db6db6fffffff) * 0x10000000000000000 + 0xffffffffffffffff) * 0x10000000000000000 + 0xffffffffff00003f) * 0x10000000000000000 + 0xffffff0effffff0e) * 0x10000000000000000 + 0xffffff0effffff0e)
  | 406 => ((((((0xdb6db6db6db6db * 0x10000000000000000 + 0x6db6db6db6db6db6) * 0x10000000000000000 + 0xdb6db6db6fffffff) * 0x10000000000000000 + 0xffffffffffffffff) * 0x10000000000000000 + 0xffffffffffffffff) * 0x10000000000000000 + 0xffffffeeffffffee) * 0x10000000000000000 + 0xffffffeeffffffee)
  | 407 => ((((((0xe38e38e38e38e3 * 0x10000000000000000 + 0x8e38e38e38e38e38) * 0x10000000000000000 + 0xe38e38e3800003f0) * 0x10000000000000000 + 0x0003f00003f00000) * 0x10000000000000000 + 0x0000fc0000000000) * 0x10000000000000000 + 0x1111111011111110) * 0x10000000000000000 + 0x1111111011111110)
  | 408 => ((((((0xe38e38e38e38e3 * 0x10000000000000000 + 0x8e38e38e38e38e38) * 0x10000000000000000 + 0xe38e38e38ffffff0) * 0x10000000000000000 + 0x0003fffffff00003) * 0x10000000000000000 + 0xfffffc0000ffffc0) * 0x10000000000000000 + 0xf1f1f1f0f1f1f1f0) * 0x10000000000000000 + 0xf1f1f1f0f1f1f1f0)
  | 409 => ((((((0xe38e38e38e38e3 * 0x10000000000000000 + 0x8e38e38e38e38e38) * 0x10000000000000000 + 0xe38e38e38fffffff) * 0x10000000000000000 + 0xfffff00003f00003) * 0x10000000000000000 + 0xffffffffff000000) * 0x10000000000000000 + 0xff11ff10ff11ff10) * 0x10000000000000000 + 0xff11ff10ff11ff10)
  | 410 => ((((((0xe38e38e38e38e3 * 0x10000000000000000 + 0x8e38e38e38e38e38) * 0x10000000000000000 + 0xe38e38e38fffffff) * 0x10000000000000000 + 0xfffffffffffffffc) * 0x10000000000000000 + 0x0000fc0000000000) * 0x10000000000000000 + 0xffff1110ffff1110) * 0x10000000000000000 + 0xffff1110ffff1110)
  | 411 => ((((((0xe38e38e38e38e3 * 0x10000000000000000 + 0x8e38e38e38e38e38) * 0x10000000000000000 + 0xe38e38e38fffffff) * 0x10000000000000000 + 0xffffffffffffffff) * 0x10000000000000000 + 0xffffffffffffffc0) * 0x10000000000000000 + 0xfffffff0fffffff0) * 0x10000000000000000 + 0xfffffff0fffffff0)
  | 412 => ((((((0xebaebaebaebaeb * 0x10000000000000000 + 0xaebaebaebaebaeba) * 0x10000000000000000 + 0xebaebaeba000fff0) * 0x10000000000000000 + 0x00fff000fff000fc) * 0x10000000000000000 + 0x003ffc003f000fc0) * 0x10000000000000000 + 0x3333333233333332) * 0x10000000000000000 + 0x3333333233333332)
  | 413 => ((((((0xebaebaebaebaeb * 0x10000000000000000 + 0xaebaebaebaebaeba) * 0x10000000000000000 + 0xebaebaebafffffff) * 0x10000000000000000 + 0xffffffffffffffff) * 0x10000000000000000 + 0xffffffffffffffff) * 0x10000000000000000 + 0xfffffffafffffffa) * 0x10000000000000000 + 0xfffffffafffffffa)
  | 414 => ((((((0xf3cf3cf3cf3cf3 * 0x10000000000000000 + 0xcf3cf3cf3cf3cf3c) * 0x10000000000000000 + 0xf3cf3cf3c03f03f0) * 0x10000000000000000 + 0x3f03f03f03f03f00) * 0x10000000000000000 + 0x0fc0fc0fc003f000) * 0x10000000000000000 + 0x5555555455555554) * 0x10000000000000000 + 0x5555555455555554)
  | 415 => ((((((0xf3cf3cf3cf3cf3 * 0x10000000000000000 + 0xcf3cf3cf3cf3cf3c) * 0x10000000000000000 + 0xf3cf3cf3cfffffff) * 0x10000000000000000 + 0xffffffffffffffff) * 0x10000000000000000 + 0xffffffffffffffff) * 0x10000000000000000 + 0xfffffffcfffffffc) * 0x10000000000000000 + 0xfffffffcfffffffc)
  | 416 => ((((((0xfbefbefbefbefb * 0x10000000000000000 + 0xefbefbefbefbefbe) * 0x10000000000000000 + 0xfbefbefbefffffff) * 0x10000000000000000 + 0xffffffffffffffff) * 0x10000000000000000 + 0xffffffffffffffff) * 0x10000000000000000 + 0xfffffffefffffffe) * 0x10000000000000000 + 0xfffffffefffffffe)
  | _ => zero

def frontierNode (charges : Nat) (signals : List Nat) : FrontierNode :=
  ((List.finRange 5).map fun i => (neg (input i.val), (charges / 4^i.val) % 4),
    signals.map frontierSig)

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
def frontier2 : Nat → List FrontierNode
  | 7 =>
    [frontierNode 682 [86,248,316]]
  | 8 =>
    [frontierNode 618 [109,204,347],
     frontierNode 682 [109,204,347]]
  | 12 =>
    [frontierNode 682 [61,164,380]]
  | 14 =>
    [frontierNode 666 [136,217,329],
     frontierNode 682 [136,217,329]]
  | 15 =>
    [frontierNode 618 [151,202,329],
     frontierNode 682 [151,202,329]]
  | 20 =>
    [frontierNode 426 [164,217,301],
     frontierNode 682 [164,217,301]]
  | 25 =>
    [frontierNode 618 [109,203,347],
     frontierNode 682 [109,203,347]]
  | 26 =>
    [frontierNode 426 [151,230,301],
     frontierNode 682 [151,230,301]]
  | 31 =>
    [frontierNode 682 [61,230,347]]
  | 32 =>
    [frontierNode 666 [109,137,380],
     frontierNode 682 [109,137,380]]
  | 37 =>
    [frontierNode 426 [109,248,303],
     frontierNode 682 [109,248,303]]
  | 41 =>
    [frontierNode 682 [55,248,329],
     frontierNode 682 [92,217,347]]
  | 43 =>
    [frontierNode 682 [92,151,380]]
  | 52 =>
    [frontierNode 682 [91,151,380]]
  | 57 =>
    [frontierNode 682 [60,248,329]]
  | 59 =>
    [frontierNode 618 [164,202,316],
     frontierNode 682 [164,202,316]]
  | 62 =>
    [frontierNode 682 [91,248,316]]
  | 64 =>
    [frontierNode 666 [136,230,316],
     frontierNode 682 [136,230,316]]
  | 76 =>
    [frontierNode 682 [60,164,380]]
  | 78 =>
    [frontierNode 426 [109,248,302],
     frontierNode 682 [109,248,302]]
  | 79 =>
    [frontierNode 682 [55,230,347]]
  | 85 =>
    [frontierNode 666 [109,138,380],
     frontierNode 682 [109,138,380]]
  | 92 =>
    [frontierNode 682 [86,217,347]]
  | _ => []

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
def frontier3 : Nat → List FrontierNode
  | 0 =>
    [frontierNode 666 [109,123,137,380]]
  | 1 =>
    [frontierNode 649 [37,90,123,380],
     frontierNode 554 [10,164,192,316],
     frontierNode 618 [18,109,176,347],
     frontierNode 426 [9,151,230,277],
     frontierNode 426 [164,217,248,301]]
  | 2 =>
    [frontierNode 358 [68,151,192,301],
     frontierNode 614 [68,151,192,301],
     frontierNode 666 [109,136,230,316],
     frontierNode 426 [25,109,248,294]]
  | 3 =>
    [frontierNode 361 [37,164,202,294],
     frontierNode 425 [37,164,202,294],
     frontierNode 394 [109,123,179,294]]
  | 4 =>
    [frontierNode 646 [58,68,123,380],
     frontierNode 650 [11,123,212,329],
     frontierNode 426 [12,151,230,294]]
  | 6 =>
    [frontierNode 553 [37,135,192,329],
     frontierNode 169 [37,164,199,294],
     frontierNode 425 [37,91,248,294],
     frontierNode 166 [53,68,248,294],
     frontierNode 362 [61,164,192,294],
     frontierNode 618 [26,164,192,316],
     frontierNode 682 [109,145,320,347]]
  | 7 =>
    [frontierNode 538 [109,123,192,279],
     frontierNode 554 [18,109,192,343]]
  | 8 =>
    [frontierNode 409 [37,136,230,294],
     frontierNode 425 [37,136,230,294],
     frontierNode 538 [85,123,192,316],
     frontierNode 618 [109,204,347]]
  | 9 =>
    [frontierNode 538 [35,123,192,329]]
  | 10 =>
    [frontierNode 618 [10,164,202,316]]
  | 12 =>
    [frontierNode 406 [68,136,217,294],
     frontierNode 422 [68,136,217,294],
     frontierNode 394 [58,123,230,294],
     frontierNode 666 [109,137,217,380],
     frontierNode 618 [3,164,192,316]]
  | 13 =>
    [frontierNode 617 [37,92,192,347],
     frontierNode 358 [68,151,202,294],
     frontierNode 422 [68,151,202,294],
     frontierNode 650 [24,109,123,374],
     frontierNode 666 [123,136,230,316],
     frontierNode 426 [14,109,248,276],
     frontierNode 682 [109,142,221,248],
     frontierNode 682 [109,224,310,380]]
  | 14 =>
    [frontierNode 394 [89,123,217,294],
     frontierNode 666 [136,217,329],
     frontierNode 618 [16,109,192,347],
     frontierNode 426 [109,230,248,302],
     frontierNode 682 [109,258,367,380]]
  | 15 =>
    [frontierNode 614 [61,68,192,347],
     frontierNode 586 [63,123,192,316],
     frontierNode 586 [109,123,192,296],
     frontierNode 106 [42,164,192,294],
     frontierNode 618 [15,109,177,347],
     frontierNode 618 [151,202,329]]
  | 16 =>
    [frontierNode 166 [68,151,199,294],
     frontierNode 422 [60,68,248,294],
     frontierNode 666 [29,109,123,380],
     frontierNode 170 [17,109,248,294],
     frontierNode 426 [164,217,294,301]]
  | 17 =>
    [frontierNode 650 [22,109,123,380],
     frontierNode 682 [105,230,316,377]]
  | 18 =>
    [frontierNode 646 [68,123,201,316],
     frontierNode 298 [45,164,192,294],
     frontierNode 554 [10,146,192,329]]
  | 20 =>
    [frontierNode 666 [136,230,316,380],
     frontierNode 554 [15,103,192,347],
     frontierNode 106 [34,164,192,294],
     frontierNode 426 [164,217,301]]
  | 21 =>
    [frontierNode 682 [109,258,347,400]]
  | 22 =>
    [frontierNode 538 [76,123,192,316],
     frontierNode 426 [14,109,248,302]]
  | 23 =>
    [frontierNode 394 [109,123,198,294],
     frontierNode 602 [86,123,192,316],
     frontierNode 666 [7,109,123,380],
     frontierNode 554 [10,159,192,316],
     frontierNode 362 [60,164,192,294]]
  | 24 =>
    [frontierNode 666 [6,123,230,316],
     frontierNode 618 [4,109,192,347],
     frontierNode 170 [17,109,244,294],
     frontierNode 426 [23,109,248,294],
     frontierNode 426 [27,164,217,294],
     frontierNode 426 [109,248,294,303]]
  | 25 =>
    [frontierNode 666 [12,123,217,329],
     frontierNode 666 [20,123,230,316],
     frontierNode 618 [109,203,347]]
  | 26 =>
    [frontierNode 618 [12,164,192,316],
     frontierNode 426 [151,230,301]]
  | 27 =>
    [frontierNode 602 [91,123,192,316],
     frontierNode 666 [8,109,123,380],
     frontierNode 298 [33,164,192,294],
     frontierNode 426 [17,109,248,303]]
  | 28 =>
    [frontierNode 618 [28,109,192,347],
     frontierNode 426 [109,151,248,302],
     frontierNode 682 [109,248,367,390]]
  | 29 =>
    [frontierNode 586 [46,123,192,329],
     frontierNode 346 [109,123,192,302],
     frontierNode 602 [109,123,192,302],
     frontierNode 618 [164,202,316,347]]
  | 30 =>
    [frontierNode 601 [37,123,202,329],
     frontierNode 665 [37,123,202,329],
     frontierNode 618 [10,151,178,329],
     frontierNode 426 [1,109,248,294],
     frontierNode 426 [27,151,230,294],
     frontierNode 682 [241,248,329,357]]
  | 31 =>
    [frontierNode 650 [11,123,217,329],
     frontierNode 298 [83,151,192,294],
     frontierNode 618 [109,164,204,347],
     frontierNode 426 [9,164,217,301],
     frontierNode 682 [105,217,329,377]]
  | 32 =>
    [frontierNode 666 [109,137,380],
     frontierNode 666 [109,138,316,380]]
  | 33 =>
    [frontierNode 678 [27,68,217,347],
     frontierNode 170 [9,164,217,294]]
  | 34 =>
    [frontierNode 538 [66,123,192,316],
     frontierNode 666 [136,217,329,380],
     frontierNode 170 [9,147,230,294]]
  | 35 =>
    [frontierNode 678 [27,68,151,380],
     frontierNode 554 [18,101,192,347],
     frontierNode 682 [151,230,340,411]]
  | 36 =>
    [frontierNode 422 [55,68,248,294],
     frontierNode 346 [109,138,192,294],
     frontierNode 298 [109,113,192,294],
     frontierNode 362 [109,138,192,294]]
  | 37 =>
    [frontierNode 666 [24,109,110,380],
     frontierNode 426 [9,151,230,301],
     frontierNode 426 [109,248,303]]
  | 38 =>
    [frontierNode 618 [18,109,204,347]]
  | 39 =>
    [frontierNode 170 [9,151,230,294]]
  | 40 =>
    [frontierNode 598 [68,136,192,316],
     frontierNode 614 [68,136,192,316],
     frontierNode 346 [109,123,204,294],
     frontierNode 410 [109,123,204,294],
     frontierNode 362 [92,151,192,294],
     frontierNode 426 [17,109,248,275]]
  | 41 =>
    [frontierNode 409 [37,123,230,301],
     frontierNode 665 [37,123,230,301]]
  | 42 =>
    [frontierNode 649 [37,89,123,380],
     frontierNode 426 [151,230,248,301]]
  | 43 =>
    [frontierNode 681 [27,37,164,380],
     frontierNode 298 [109,127,192,294],
     frontierNode 682 [96,164,217,243],
     frontierNode 682 [109,155,208,248]]
  | 44 =>
    [frontierNode 586 [59,123,192,329],
     frontierNode 394 [31,123,230,294],
     frontierNode 650 [24,109,123,380],
     frontierNode 170 [9,160,217,294],
     frontierNode 682 [164,241,357,380]]
  | 45 =>
    [frontierNode 665 [37,92,123,380],
     frontierNode 681 [20,37,248,329],
     frontierNode 406 [68,123,217,301],
     frontierNode 662 [68,123,217,301],
     frontierNode 394 [109,123,195,294],
     frontierNode 538 [45,123,192,329],
     frontierNode 106 [81,151,192,294],
     frontierNode 682 [151,241,367,380]]
  | 46 =>
    [frontierNode 394 [62,123,217,294],
     frontierNode 650 [24,98,123,380],
     frontierNode 666 [11,136,230,316],
     frontierNode 426 [19,109,248,294]]
  | 47 =>
    [frontierNode 662 [61,68,123,380],
     frontierNode 170 [14,104,248,294]]
  | 48 =>
    [frontierNode 425 [37,86,248,294],
     frontierNode 666 [22,109,111,380],
     frontierNode 298 [76,151,192,294]]
  | 49 =>
    [frontierNode 650 [22,109,123,375],
     frontierNode 666 [11,112,230,316],
     frontierNode 666 [109,136,217,329],
     frontierNode 666 [109,138,230,380],
     frontierNode 106 [73,151,192,294],
     frontierNode 682 [96,151,230,243]]
  | 50 =>
    [frontierNode 602 [60,123,192,329],
     frontierNode 666 [25,109,123,380],
     frontierNode 618 [109,151,202,329]]
  | 51 =>
    [frontierNode 169 [37,84,248,294],
     frontierNode 394 [46,123,230,294],
     frontierNode 394 [77,123,217,294]]
  | 52 =>
    [frontierNode 614 [55,68,192,347],
     frontierNode 618 [5,109,192,347],
     frontierNode 682 [109,211,323,380],
     frontierNode 682 [109,248,357,400],
     frontierNode 682 [151,268,340,380]]
  | 53 =>
    [frontierNode 666 [109,123,138,380],
     frontierNode 362 [91,151,192,294]]
  | 54 =>
    [frontierNode 665 [37,91,123,380],
     frontierNode 678 [20,68,217,347],
     frontierNode 554 [10,151,192,329],
     frontierNode 618 [151,192,202,329],
     frontierNode 170 [14,109,245,294],
     frontierNode 426 [2,109,248,294],
     frontierNode 682 [151,241,329,411]]
  | 55 =>
    [frontierNode 649 [37,123,230,300],
     frontierNode 410 [61,123,230,294],
     frontierNode 666 [24,109,138,380],
     frontierNode 618 [164,192,202,316],
     frontierNode 426 [109,164,217,301],
     frontierNode 682 [100,164,316,342],
     frontierNode 682 [109,268,347,390]]
  | 56 =>
    [frontierNode 154 [36,123,230,294],
     frontierNode 682 [230,258,340,347],
     frontierNode 682 [241,248,316,367]]
  | 57 =>
    [frontierNode 346 [109,123,203,294],
     frontierNode 410 [109,123,203,294],
     frontierNode 426 [151,230,294,301]]
  | 58 =>
    [frontierNode 646 [59,68,123,380],
     frontierNode 154 [67,123,217,294],
     frontierNode 554 [10,164,192,312]]
  | 59 =>
    [frontierNode 553 [37,83,192,347],
     frontierNode 646 [68,123,217,300],
     frontierNode 618 [26,151,192,329],
     frontierNode 618 [164,202,316]]
  | 60 =>
    [frontierNode 550 [68,135,192,316],
     frontierNode 666 [28,109,123,380],
     frontierNode 666 [123,136,217,329],
     frontierNode 426 [109,164,248,303]]
  | 61 =>
    [frontierNode 649 [37,123,201,329],
     frontierNode 106 [109,114,192,294],
     frontierNode 426 [109,151,230,301]]
  | 62 =>
    [frontierNode 681 [27,37,230,347],
     frontierNode 550 [54,68,192,347],
     frontierNode 154 [53,123,230,294],
     frontierNode 666 [109,137,329,380],
     frontierNode 618 [19,109,192,347],
     frontierNode 682 [175,248,316,400]]
  | 63 =>
    [frontierNode 553 [37,164,192,299],
     frontierNode 618 [10,151,202,329]]
  | 64 =>
    [frontierNode 617 [37,86,192,347],
     frontierNode 662 [60,68,123,380],
     frontierNode 154 [42,123,230,294],
     frontierNode 154 [84,123,217,294],
     frontierNode 666 [136,230,316],
     frontierNode 682 [217,268,340,347]]
  | 65 =>
    [frontierNode 154 [109,123,180,294],
     frontierNode 106 [109,129,192,294],
     frontierNode 618 [3,151,192,329],
     frontierNode 426 [109,248,294,302],
     frontierNode 682 [175,230,316,411]]
  | 66 =>
    [frontierNode 678 [20,68,248,316]]
  | 67 =>
    [frontierNode 170 [14,109,248,294],
     frontierNode 682 [100,151,329,342]]
  | 69 =>
    [frontierNode 586 [90,123,192,316],
     frontierNode 650 [11,123,217,324]]
  | 70 =>
    [frontierNode 602 [55,123,192,329]]
  | 71 =>
    [frontierNode 666 [6,123,217,329]]
  | 72 =>
    [frontierNode 666 [20,123,217,329],
     frontierNode 666 [22,109,137,380],
     frontierNode 666 [23,109,123,380],
     frontierNode 554 [15,109,192,344],
     frontierNode 554 [18,109,192,347],
     frontierNode 618 [109,151,203,347],
     frontierNode 682 [109,268,357,380]]
  | 73 =>
    [frontierNode 550 [68,151,192,299]]
  | 74 =>
    [frontierNode 154 [109,123,196,294],
     frontierNode 298 [52,164,192,294],
     frontierNode 106 [65,151,192,294],
     frontierNode 618 [10,164,178,316],
     frontierNode 618 [109,192,204,347]]
  | 75 =>
    [frontierNode 681 [26,37,248,329],
     frontierNode 650 [22,99,123,380],
     frontierNode 666 [12,123,230,316]]
  | 76 =>
    [frontierNode 553 [37,85,192,347],
     frontierNode 650 [11,123,225,316],
     frontierNode 538 [109,123,192,295]]
  | 77 =>
    [frontierNode 169 [37,133,230,294],
     frontierNode 682 [175,217,347,400]]
  | 78 =>
    [frontierNode 346 [109,137,192,294],
     frontierNode 362 [109,137,192,294],
     frontierNode 426 [109,248,302]]
  | 79 =>
    [frontierNode 586 [77,123,192,316],
     frontierNode 154 [109,123,193,294],
     frontierNode 618 [12,151,192,329],
     frontierNode 618 [15,109,203,347],
     frontierNode 682 [175,217,329,411]]
  | 80 =>
    [frontierNode 538 [54,123,192,329]]
  | 81 =>
    [frontierNode 166 [50,68,248,294],
     frontierNode 166 [68,133,217,294],
     frontierNode 650 [11,123,230,316],
     frontierNode 298 [64,151,192,294],
     frontierNode 106 [109,125,192,294],
     frontierNode 618 [29,109,192,347]]
  | 82 =>
    [frontierNode 298 [109,131,192,294]]
  | 83 =>
    [frontierNode 601 [37,136,192,329],
     frontierNode 617 [37,136,192,329],
     frontierNode 681 [20,37,230,347],
     frontierNode 550 [52,68,192,347],
     frontierNode 410 [92,123,217,294],
     frontierNode 618 [109,203,329,347]]
  | 84 =>
    [frontierNode 598 [68,123,202,316],
     frontierNode 662 [68,123,202,316],
     frontierNode 618 [151,202,329,347]]
  | 85 =>
    [frontierNode 346 [109,123,192,303],
     frontierNode 602 [109,123,192,303],
     frontierNode 666 [109,138,380],
     frontierNode 170 [9,164,213,294]]
  | 86 =>
    [frontierNode 678 [26,68,151,380],
     frontierNode 586 [109,123,192,298],
     frontierNode 426 [0,164,217,294]]
  | 87 =>
    [frontierNode 586 [32,123,192,329]]
  | 88 =>
    [frontierNode 106 [50,164,192,294]]
  | 89 =>
    [frontierNode 361 [37,164,192,301],
     frontierNode 617 [37,164,192,301]]
  | 90 =>
    [frontierNode 169 [37,81,248,294],
     frontierNode 682 [164,258,340,380]]
  | 91 =>
    [frontierNode 538 [109,123,192,297],
     frontierNode 618 [109,192,203,347],
     frontierNode 170 [17,102,248,294],
     frontierNode 682 [109,158,307,347],
     frontierNode 682 [164,217,340,411]]
  | 92 =>
    [frontierNode 586 [109,123,192,278],
     frontierNode 154 [73,123,217,294],
     frontierNode 410 [55,123,230,294],
     frontierNode 410 [86,123,217,294],
     frontierNode 618 [109,204,316,347],
     frontierNode 426 [0,151,230,294],
     frontierNode 426 [9,164,217,277],
     frontierNode 682 [175,248,329,390]]
  | 93 =>
    [frontierNode 650 [11,123,230,311],
     frontierNode 666 [11,136,217,329],
     frontierNode 682 [175,230,347,390]]
  | 94 =>
    [frontierNode 681 [26,37,164,380],
     frontierNode 618 [109,164,202,316]]
  | 95 =>
    [frontierNode 426 [12,164,217,294],
     frontierNode 426 [16,109,248,294]]
  | 96 =>
    [frontierNode 678 [26,68,248,316],
     frontierNode 666 [11,112,217,329],
     frontierNode 554 [10,151,192,325],
     frontierNode 554 [15,109,192,347],
     frontierNode 170 [9,151,226,294],
     frontierNode 426 [109,217,248,303],
     frontierNode 682 [164,241,316,411]]
  | _ => []

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
def frontier4 : Nat → List FrontierNode
  | 0 =>
    [frontierNode 169 [37,105,174,230,294],
     frontierNode 330 [22,99,123,192,294],
     frontierNode 650 [109,123,208,230,380],
     frontierNode 282 [109,117,123,192,294],
     frontierNode 346 [109,123,204,294,316],
     frontierNode 410 [109,123,230,294,384],
     frontierNode 410 [123,167,217,230,294],
     frontierNode 170 [109,143,151,248,294],
     frontierNode 426 [109,151,268,294,380]]
  | 1 =>
    [frontierNode 649 [37,94,123,241,329],
     frontierNode 342 [68,123,202,294,357],
     frontierNode 330 [109,123,192,284,294],
     frontierNode 346 [29,109,123,192,294],
     frontierNode 346 [109,123,192,203,294],
     frontierNode 602 [109,123,192,329,386],
     frontierNode 602 [123,192,241,316,367],
     frontierNode 554 [10,164,192,316]]
  | 2 =>
    [frontierNode 345 [37,91,123,192,294],
     frontierNode 665 [37,123,241,367,380],
     frontierNode 361 [37,164,202,294,347],
     frontierNode 86 [53,68,123,192,294],
     frontierNode 358 [68,151,192,301],
     frontierNode 422 [68,175,208,248,294],
     frontierNode 330 [109,123,186,192,294],
     frontierNode 346 [14,109,123,192,302],
     frontierNode 154 [109,123,158,267,294],
     frontierNode 298 [109,164,192,294,322]]
  | 3 =>
    [frontierNode 537 [10,37,123,192,325],
     frontierNode 409 [9,37,123,230,301],
     frontierNode 361 [37,164,202,294],
     frontierNode 598 [68,123,136,192,316],
     frontierNode 358 [3,68,151,192,294],
     frontierNode 650 [109,123,216,316,380],
     frontierNode 650 [123,217,315,340,380],
     frontierNode 410 [105,123,230,294,390],
     frontierNode 554 [109,140,151,192,347],
     frontierNode 362 [96,151,192,268,294],
     frontierNode 618 [151,192,230,340,347]]
  | 4 =>
    [frontierNode 617 [37,164,192,347,406],
     frontierNode 650 [94,109,123,230,316],
     frontierNode 538 [109,123,142,192,356],
     frontierNode 410 [109,123,217,259,294],
     frontierNode 410 [123,175,230,294,390],
     frontierNode 410 [123,230,258,294,340],
     frontierNode 666 [123,164,241,316,380],
     frontierNode 618 [109,164,192,316,411],
     frontierNode 618 [175,192,230,316,347],
     frontierNode 170 [100,105,164,217,294],
     frontierNode 426 [109,230,258,294,347]]
  | 5 =>
    [frontierNode 153 [9,37,123,230,294],
     frontierNode 665 [37,123,224,340,380],
     frontierNode 617 [37,175,192,320,347],
     frontierNode 294 [10,68,146,192,294],
     frontierNode 678 [68,109,248,357,380],
     frontierNode 678 [68,151,241,347,380],
     frontierNode 678 [68,241,248,316,347],
     frontierNode 394 [123,230,294,318,340],
     frontierNode 346 [109,123,192,294,302],
     frontierNode 346 [109,138,192,294,316],
     frontierNode 602 [100,123,192,316,323],
     frontierNode 154 [70,109,123,230,294]]
  | 6 =>
    [frontierNode 550 [68,95,175,192,316],
     frontierNode 538 [109,123,148,192,316],
     frontierNode 554 [96,105,151,192,329],
     frontierNode 106 [109,192,211,255,294],
     frontierNode 106 [124,151,164,192,294],
     frontierNode 106 [164,192,246,258,294],
     frontierNode 170 [9,151,230,248,294]]
  | 7 =>
    [frontierNode 361 [10,37,164,178,294],
     frontierNode 406 [9,68,123,217,301],
     frontierNode 650 [109,123,217,221,380],
     frontierNode 346 [25,109,123,192,294],
     frontierNode 602 [105,123,192,316,320],
     frontierNode 602 [109,123,142,192,221],
     frontierNode 298 [109,164,192,294,327],
     frontierNode 298 [164,192,294,345,357],
     frontierNode 554 [96,151,164,192,340],
     frontierNode 362 [109,139,164,192,294]]
  | 8 =>
    [frontierNode 341 [37,68,123,294,368],
     frontierNode 405 [37,68,123,294,368],
     frontierNode 409 [37,136,230,294],
     frontierNode 598 [12,68,123,192,316],
     frontierNode 102 [68,151,191,192,294],
     frontierNode 422 [68,151,241,294,411],
     frontierNode 394 [123,217,230,294,378],
     frontierNode 650 [22,109,123,329,380],
     frontierNode 90 [102,109,123,192,294],
     frontierNode 90 [109,123,183,192,294],
     frontierNode 602 [123,175,192,316,320],
     frontierNode 410 [123,217,224,294,340],
     frontierNode 426 [109,142,230,248,294],
     frontierNode 426 [109,164,208,248,294]]
  | 9 =>
    [frontierNode 389 [37,68,123,236,294],
     frontierNode 665 [37,123,268,340,380],
     frontierNode 150 [9,68,123,217,294],
     frontierNode 406 [68,123,217,294,301],
     frontierNode 586 [109,123,192,220,329],
     frontierNode 282 [109,123,192,286,294],
     frontierNode 410 [96,123,230,258,294],
     frontierNode 554 [109,192,323,328,347],
     frontierNode 106 [151,192,209,241,294],
     frontierNode 170 [109,211,230,248,294]]
  | 10 =>
    [frontierNode 409 [37,109,123,230,301],
     frontierNode 614 [68,169,192,316,347],
     frontierNode 586 [40,109,123,192,316],
     frontierNode 586 [123,192,316,378,400],
     frontierNode 650 [109,123,316,320,380],
     frontierNode 282 [18,101,123,192,294],
     frontierNode 602 [109,123,192,320,357],
     frontierNode 602 [109,123,192,323,390],
     frontierNode 298 [151,192,294,345,367],
     frontierNode 362 [145,164,192,294,340],
     frontierNode 170 [100,105,151,230,294]]
  | 11 =>
    [frontierNode 601 [37,123,192,202,329],
     frontierNode 665 [37,123,241,329,411],
     frontierNode 361 [0,37,164,192,294],
     frontierNode 586 [123,192,292,316,329],
     frontierNode 650 [11,109,123,230,316],
     frontierNode 650 [109,123,318,329,380],
     frontierNode 538 [69,109,123,192,329],
     frontierNode 602 [109,123,192,316,396],
     frontierNode 410 [109,123,208,268,294],
     frontierNode 410 [109,123,224,294,390],
     frontierNode 666 [109,123,230,316,377],
     frontierNode 554 [10,151,192,329,347],
     frontierNode 362 [109,151,192,262,294]]
  | 12 =>
    [frontierNode 341 [37,68,123,192,277],
     frontierNode 393 [11,37,123,225,294],
     frontierNode 681 [37,230,248,340,347],
     frontierNode 646 [68,100,123,239,316],
     frontierNode 406 [68,136,217,294],
     frontierNode 330 [24,98,123,192,294],
     frontierNode 346 [16,109,123,192,294],
     frontierNode 602 [105,123,192,307,329],
     frontierNode 602 [109,123,192,329,353],
     frontierNode 602 [109,123,192,329,381],
     frontierNode 410 [123,217,268,294,340],
     frontierNode 666 [109,123,230,357,380],
     frontierNode 554 [18,109,192,316,347],
     frontierNode 362 [151,164,192,233,294],
     frontierNode 426 [109,217,268,294,347]]
  | 13 =>
    [frontierNode 345 [30,37,123,192,251],
     frontierNode 342 [55,68,123,192,294],
     frontierNode 358 [68,151,202,294],
     frontierNode 330 [109,123,192,281,294],
     frontierNode 586 [71,109,123,192,329],
     frontierNode 538 [123,192,288,316,329],
     frontierNode 346 [5,109,123,192,294],
     frontierNode 602 [123,175,192,307,329],
     frontierNode 410 [109,123,217,294,415],
     frontierNode 554 [163,175,192,329,347],
     frontierNode 362 [109,192,268,294,357],
     frontierNode 618 [109,145,192,329,347],
     frontierNode 170 [17,109,164,248,294],
     frontierNode 426 [151,230,248,294,340]]
  | 14 =>
    [frontierNode 345 [37,123,192,294,412],
     frontierNode 409 [37,123,230,294,301],
     frontierNode 582 [68,123,192,311,316],
     frontierNode 598 [11,68,136,192,316],
     frontierNode 586 [109,123,192,206,390],
     frontierNode 650 [109,123,217,307,329],
     frontierNode 650 [123,217,329,378,380],
     frontierNode 346 [18,109,123,176,294],
     frontierNode 602 [109,123,192,329,351],
     frontierNode 666 [109,123,217,323,380],
     frontierNode 554 [105,175,192,316,329],
     frontierNode 554 [109,142,164,192,347],
     frontierNode 554 [109,192,321,329,347],
     frontierNode 362 [109,158,192,294,357],
     frontierNode 618 [100,164,192,316,347]]
  | 15 =>
    [frontierNode 341 [37,68,136,192,294],
     frontierNode 357 [37,68,136,192,294],
     frontierNode 361 [9,37,164,192,277],
     frontierNode 617 [37,175,192,347,400],
     frontierNode 425 [37,164,239,248,294],
     frontierNode 534 [10,68,123,192,316],
     frontierNode 342 [68,123,192,294,414],
     frontierNode 294 [68,151,192,290,294],
     frontierNode 166 [68,97,175,217,294],
     frontierNode 422 [68,217,248,294,373],
     frontierNode 678 [68,175,248,316,380],
     frontierNode 586 [123,192,316,329,378],
     frontierNode 650 [109,123,221,229,380],
     frontierNode 410 [109,123,268,294,390],
     frontierNode 554 [109,192,310,315,347],
     frontierNode 362 [151,155,192,241,294]]
  | 16 =>
    [frontierNode 405 [13,37,68,294,332],
     frontierNode 665 [37,100,123,329,342],
     frontierNode 326 [58,68,123,192,294],
     frontierNode 422 [68,167,217,248,294],
     frontierNode 602 [123,192,235,316,329],
     frontierNode 154 [109,123,143,217,294],
     frontierNode 154 [109,123,144,217,294],
     frontierNode 298 [126,151,164,192,294],
     frontierNode 554 [109,163,192,329,347],
     frontierNode 106 [109,164,192,222,294],
     frontierNode 362 [109,164,192,256,294],
     frontierNode 170 [17,109,248,294]]
  | 17 =>
    [frontierNode 677 [37,68,274,347,380],
     frontierNode 329 [37,89,123,192,294],
     frontierNode 393 [11,37,123,230,294],
     frontierNode 617 [37,175,192,329,411],
     frontierNode 646 [68,123,318,340,380],
     frontierNode 598 [11,68,112,192,316],
     frontierNode 358 [10,68,151,178,294],
     frontierNode 394 [74,109,123,230,294],
     frontierNode 650 [22,109,123,380],
     frontierNode 650 [109,123,307,329,390],
     frontierNode 90 [17,102,123,192,294],
     frontierNode 602 [123,192,240,316,329],
     frontierNode 410 [123,217,230,294,334],
     frontierNode 618 [109,151,192,329,342]]
  | 18 =>
    [frontierNode 341 [37,68,112,192,294],
     frontierNode 362 [109,145,192,294,367],
     frontierNode 362 [109,164,192,252,294],
     frontierNode 618 [109,192,248,316,367],
     frontierNode 618 [175,192,217,329,347]]
  | 19 =>
    [frontierNode 550 [68,153,175,192,347],
     frontierNode 614 [68,145,192,340,347],
     frontierNode 422 [68,151,233,248,294],
     frontierNode 410 [109,123,221,258,294],
     frontierNode 170 [9,109,164,217,294],
     frontierNode 170 [109,158,163,248,294],
     frontierNode 170 [164,217,246,248,294],
     frontierNode 426 [96,164,217,248,294]]
  | 20 =>
    [frontierNode 601 [3,37,123,192,329],
     frontierNode 278 [45,68,123,192,294],
     frontierNode 662 [68,123,235,316,380],
     frontierNode 550 [68,192,321,340,347],
     frontierNode 102 [68,147,151,192,294],
     frontierNode 586 [109,123,192,221,399],
     frontierNode 602 [109,123,192,307,367],
     frontierNode 602 [123,192,274,316,329],
     frontierNode 362 [109,164,192,294,355]]
  | 21 =>
    [frontierNode 341 [37,68,123,192,269],
     frontierNode 597 [37,68,123,192,269],
     frontierNode 425 [37,167,230,248,294],
     frontierNode 390 [11,68,123,217,294],
     frontierNode 342 [68,123,192,258,301],
     frontierNode 662 [68,123,240,316,380],
     frontierNode 358 [0,68,151,192,294],
     frontierNode 422 [68,100,151,294,342],
     frontierNode 586 [123,192,206,241,316],
     frontierNode 90 [109,120,123,192,294],
     frontierNode 346 [109,123,137,192,294],
     frontierNode 410 [109,123,217,218,294],
     frontierNode 298 [109,192,294,308,357],
     frontierNode 682 [109,164,248,316,380]]
  | 22 =>
    [frontierNode 533 [37,68,123,192,299],
     frontierNode 598 [20,68,123,192,316],
     frontierNode 598 [68,123,202,316,347],
     frontierNode 394 [109,123,217,294,306],
     frontierNode 602 [109,123,192,316,363],
     frontierNode 602 [109,123,192,316,391],
     frontierNode 410 [96,123,217,268,294],
     frontierNode 410 [109,123,230,294,386],
     frontierNode 618 [151,192,241,329,347],
     frontierNode 426 [175,230,248,294,316]]
  | 23 =>
    [frontierNode 537 [37,44,123,192,329],
     frontierNode 614 [68,151,192,340,342],
     frontierNode 422 [68,175,217,243,294],
     frontierNode 650 [11,123,230,316,380],
     frontierNode 602 [109,123,192,329,348],
     frontierNode 154 [123,189,217,230,294],
     frontierNode 362 [151,164,192,294,332]]
  | 24 =>
    [frontierNode 357 [37,68,175,192,301],
     frontierNode 677 [37,68,248,373,380],
     frontierNode 361 [12,37,164,192,294],
     frontierNode 425 [37,164,248,294,406],
     frontierNode 681 [37,241,248,329,347],
     frontierNode 598 [10,68,123,202,316],
     frontierNode 662 [68,123,274,316,380],
     frontierNode 614 [68,151,192,338,347],
     frontierNode 330 [22,109,123,192,294],
     frontierNode 346 [109,138,192,230,294],
     frontierNode 410 [109,123,230,249,294],
     frontierNode 106 [109,192,222,268,294],
     frontierNode 362 [164,192,241,294,357]]
  | 25 =>
    [frontierNode 345 [13,37,192,294,383],
     frontierNode 358 [9,68,151,192,277],
     frontierNode 346 [24,109,138,192,294],
     frontierNode 666 [109,123,217,329,377],
     frontierNode 298 [109,192,294,310,354],
     frontierNode 554 [10,109,164,192,316],
     frontierNode 106 [109,151,192,209,294],
     frontierNode 170 [9,109,151,230,294]]
  | 26 =>
    [frontierNode 341 [37,68,123,178,294],
     frontierNode 614 [68,175,192,347,390],
     frontierNode 362 [109,164,192,294,413]]
  | 27 =>
    [frontierNode 553 [37,105,173,192,329],
     frontierNode 282 [101,109,123,192,294],
     frontierNode 154 [123,156,175,230,294],
     frontierNode 362 [151,192,241,294,367]]
  | 28 =>
    [frontierNode 597 [21,37,68,123,167],
     frontierNode 169 [37,97,175,230,294],
     frontierNode 425 [37,100,164,294,342],
     frontierNode 425 [37,175,221,248,294],
     frontierNode 425 [37,175,230,243,294],
     frontierNode 650 [109,123,307,329,380],
     frontierNode 346 [22,109,137,192,294],
     frontierNode 346 [23,109,123,192,294],
     frontierNode 154 [109,123,143,258,294],
     frontierNode 154 [109,123,145,257,294],
     frontierNode 154 [123,230,246,258,294],
     frontierNode 362 [100,151,155,192,294]]
  | 29 =>
    [frontierNode 597 [13,37,68,192,233],
     frontierNode 617 [37,164,192,340,411],
     frontierNode 617 [37,169,192,329,347],
     frontierNode 425 [37,241,248,294,367],
     frontierNode 330 [109,123,192,280,294],
     frontierNode 346 [109,123,192,302],
     frontierNode 298 [109,151,192,294,308],
     frontierNode 298 [109,192,294,323,364],
     frontierNode 170 [109,150,217,248,294],
     frontierNode 170 [109,211,230,258,294],
     frontierNode 426 [109,164,217,243,294]]
  | 30 =>
    [frontierNode 601 [37,123,202,329],
     frontierNode 361 [37,164,192,202,294],
     frontierNode 425 [37,230,248,294,373],
     frontierNode 550 [68,95,151,192,340],
     frontierNode 678 [68,175,217,347,380],
     frontierNode 538 [123,192,316,345,367],
     frontierNode 346 [109,137,192,294,329],
     frontierNode 410 [109,123,217,262,294],
     frontierNode 106 [151,164,192,246,294],
     frontierNode 618 [109,192,258,329,347],
     frontierNode 426 [151,164,241,294,380]]
  | 31 =>
    [frontierNode 533 [37,68,123,192,336],
     frontierNode 421 [20,37,68,248,294],
     frontierNode 297 [10,37,164,192,294],
     frontierNode 342 [30,68,123,192,261],
     frontierNode 662 [68,123,217,340,377],
     frontierNode 650 [11,123,217,329],
     frontierNode 538 [123,192,329,345,357],
     frontierNode 154 [123,217,246,268,294],
     frontierNode 410 [109,123,145,294,320],
     frontierNode 170 [109,211,216,248,294]]
  | 32 =>
    [frontierNode 346 [109,123,203,294,329],
     frontierNode 602 [100,123,192,329,357],
     frontierNode 602 [109,123,192,329,388],
     frontierNode 298 [109,164,192,294,321],
     frontierNode 618 [109,164,192,347,390],
     frontierNode 170 [14,109,230,248,294]]
  | 33 =>
    [frontierNode 597 [37,68,123,202,340],
     frontierNode 585 [11,37,123,192,324],
     frontierNode 617 [37,164,192,332,347],
     frontierNode 598 [26,68,123,192,316],
     frontierNode 614 [68,174,192,316,347],
     frontierNode 422 [68,142,241,248,294],
     frontierNode 422 [68,175,217,294,411],
     frontierNode 602 [109,123,192,316,358],
     frontierNode 410 [109,123,230,294,381],
     frontierNode 554 [109,153,164,192,347],
     frontierNode 170 [9,164,217,294]]
  | 34 =>
    [frontierNode 601 [10,37,123,178,329],
     frontierNode 681 [37,175,248,329,380],
     frontierNode 358 [12,68,151,192,294],
     frontierNode 602 [109,123,192,310,400],
     frontierNode 554 [109,142,164,192,316],
     frontierNode 618 [109,192,268,316,347]]
  | 35 =>
    [frontierNode 293 [37,68,135,192,294],
     frontierNode 357 [37,68,175,202,294],
     frontierNode 425 [37,175,248,294,400],
     frontierNode 681 [37,175,230,347,380],
     frontierNode 342 [61,68,123,192,294],
     frontierNode 166 [68,97,151,241,294],
     frontierNode 650 [123,229,241,329,380],
     frontierNode 282 [109,119,123,192,294],
     frontierNode 538 [109,123,140,192,316],
     frontierNode 602 [100,123,192,310,329],
     frontierNode 554 [109,192,316,323,347],
     frontierNode 362 [109,192,258,294,367],
     frontierNode 618 [109,158,192,316,347]]
  | 36 =>
    [frontierNode 665 [37,123,230,340,377],
     frontierNode 361 [37,164,192,248,301],
     frontierNode 598 [68,109,123,202,316],
     frontierNode 150 [68,123,213,217,294],
     frontierNode 662 [68,123,241,316,377],
     frontierNode 614 [68,192,258,340,347],
     frontierNode 330 [99,109,123,192,294],
     frontierNode 346 [109,138,192,294],
     frontierNode 362 [109,164,192,254,294],
     frontierNode 170 [97,109,164,217,294],
     frontierNode 682 [109,164,217,347,380]]
  | 37 =>
    [frontierNode 149 [37,68,123,237,294],
     frontierNode 677 [37,68,248,347,406],
     frontierNode 553 [37,95,164,192,340],
     frontierNode 105 [37,39,164,192,294],
     frontierNode 105 [37,160,164,192,294],
     frontierNode 662 [68,123,241,357,380],
     frontierNode 294 [68,69,151,192,294],
     frontierNode 394 [57,109,123,217,294],
     frontierNode 650 [11,123,217,329,380],
     frontierNode 650 [123,230,328,340,380],
     frontierNode 282 [109,123,192,282,294],
     frontierNode 154 [109,123,149,217,294],
     frontierNode 410 [123,217,230,294,339],
     frontierNode 362 [109,151,192,266,294]]
  | 38 =>
    [frontierNode 297 [37,38,164,192,294],
     frontierNode 425 [37,175,230,294,411],
     frontierNode 646 [68,94,123,241,316],
     frontierNode 342 [60,68,123,192,294],
     frontierNode 358 [68,151,202,294,347],
     frontierNode 538 [38,109,123,192,316],
     frontierNode 90 [17,109,123,192,294],
     frontierNode 346 [15,109,123,203,294],
     frontierNode 346 [109,123,164,204,294],
     frontierNode 346 [109,137,192,217,294],
     frontierNode 154 [47,109,123,217,294],
     frontierNode 362 [109,151,192,294,363],
     frontierNode 426 [109,164,258,294,380]]
  | 39 =>
    [frontierNode 345 [37,123,192,268,301],
     frontierNode 665 [37,123,235,329,380],
     frontierNode 614 [68,96,151,192,243],
     frontierNode 394 [88,109,123,230,294],
     frontierNode 394 [123,217,294,305,340],
     frontierNode 394 [123,217,294,378,400],
     frontierNode 650 [96,100,123,230,316],
     frontierNode 346 [2,109,123,192,294],
     frontierNode 170 [9,151,230,294],
     frontierNode 170 [105,175,217,230,294],
     frontierNode 426 [109,164,217,294,411]]
  | 40 =>
    [frontierNode 281 [37,123,192,294,359],
     frontierNode 665 [37,123,240,329,380],
     frontierNode 361 [10,37,164,202,294],
     frontierNode 361 [27,37,164,192,294],
     frontierNode 326 [46,68,123,192,294],
     frontierNode 598 [68,136,192,316],
     frontierNode 102 [68,70,151,192,294],
     frontierNode 614 [68,151,192,347,406],
     frontierNode 394 [109,123,217,294,313],
     frontierNode 346 [109,123,204,294],
     frontierNode 602 [97,123,192,316,329],
     frontierNode 154 [78,109,123,230,294],
     frontierNode 666 [123,151,230,340,380],
     frontierNode 298 [151,164,192,294,345],
     frontierNode 298 [164,192,294,321,340],
     frontierNode 554 [109,151,192,310,329],
     frontierNode 554 [109,164,192,316,323],
     frontierNode 618 [164,192,217,340,347],
     frontierNode 426 [109,155,217,248,294],
     frontierNode 426 [164,217,248,294,340]]
  | 41 =>
    [frontierNode 601 [37,123,202,329,347],
     frontierNode 153 [37,123,226,230,294],
     frontierNode 409 [37,123,230,301],
     frontierNode 294 [10,68,151,192,294],
     frontierNode 650 [109,123,229,329,380],
     frontierNode 362 [96,151,158,192,294]]
  | 42 =>
    [frontierNode 357 [21,37,68,294,334],
     frontierNode 421 [26,37,68,248,294],
     frontierNode 677 [37,68,248,345,380],
     frontierNode 677 [37,68,248,347,378],
     frontierNode 601 [6,37,123,192,329],
     frontierNode 169 [37,97,164,241,294],
     frontierNode 646 [68,94,123,217,340],
     frontierNode 394 [109,123,294,305,390],
     frontierNode 538 [109,123,154,192,329],
     frontierNode 602 [109,123,192,316,398],
     frontierNode 554 [95,109,151,192,329],
     frontierNode 554 [109,150,192,316,347],
     frontierNode 554 [164,192,328,340,347],
     frontierNode 106 [109,164,192,228,294],
     frontierNode 170 [97,109,151,230,294]]
  | 43 =>
    [frontierNode 293 [37,68,170,192,294],
     frontierNode 677 [37,68,246,347,380],
     frontierNode 665 [37,123,274,329,380],
     frontierNode 342 [13,68,192,294,393],
     frontierNode 166 [68,156,175,248,294],
     frontierNode 346 [28,109,123,192,294],
     frontierNode 554 [109,151,155,192,367],
     frontierNode 362 [96,145,164,192,294],
     frontierNode 170 [150,175,217,248,294]]
  | 44 =>
    [frontierNode 329 [37,90,123,192,294],
     frontierNode 665 [37,123,241,323,380],
     frontierNode 330 [109,123,182,192,294],
     frontierNode 330 [109,123,185,192,294],
     frontierNode 650 [24,109,123,380],
     frontierNode 554 [109,151,155,192,329]]
  | 45 =>
    [frontierNode 406 [68,123,217,301],
     frontierNode 602 [123,192,241,316,323],
     frontierNode 618 [164,192,241,316,347]]
  | 46 =>
    [frontierNode 345 [37,123,202,294,367],
     frontierNode 617 [37,96,164,192,243],
     frontierNode 681 [37,164,248,340,380],
     frontierNode 150 [68,72,123,217,294],
     frontierNode 662 [68,123,217,373,380],
     frontierNode 550 [68,96,151,192,339],
     frontierNode 422 [68,175,248,294,390],
     frontierNode 538 [109,123,161,192,329],
     frontierNode 410 [109,123,217,294,396],
     frontierNode 554 [109,192,310,329,347],
     frontierNode 362 [96,164,192,258,294],
     frontierNode 170 [14,109,151,248,294]]
  | 47 =>
    [frontierNode 613 [20,37,68,192,347],
     frontierNode 278 [52,68,123,192,294],
     frontierNode 614 [68,105,192,316,377],
     frontierNode 650 [109,123,208,230,316],
     frontierNode 90 [14,109,123,192,294],
     frontierNode 106 [109,151,192,215,294],
     frontierNode 362 [100,142,164,192,294],
     frontierNode 618 [109,151,192,320,347]]
  | 48 =>
    [frontierNode 341 [37,68,123,192,301],
     frontierNode 597 [37,68,123,192,301],
     frontierNode 86 [42,68,123,192,294],
     frontierNode 598 [68,123,192,202,316],
     frontierNode 346 [4,109,123,192,294],
     frontierNode 602 [109,123,192,316,394],
     frontierNode 666 [123,241,248,316,329],
     frontierNode 554 [109,142,164,192,357],
     frontierNode 362 [109,142,192,268,294],
     frontierNode 170 [109,209,217,248,294]]
  | 49 =>
    [frontierNode 613 [27,37,68,192,347],
     frontierNode 153 [37,41,123,230,294],
     frontierNode 361 [26,37,164,192,294],
     frontierNode 582 [11,68,123,192,316],
     frontierNode 646 [68,96,123,217,338],
     frontierNode 278 [54,68,123,192,294],
     frontierNode 650 [109,123,305,316,380],
     frontierNode 650 [109,123,320,328,380],
     frontierNode 538 [109,123,140,192,357],
     frontierNode 346 [17,109,123,192,303],
     frontierNode 346 [19,109,123,192,294],
     frontierNode 602 [105,123,192,316,400],
     frontierNode 362 [109,151,192,294,358],
     frontierNode 618 [109,164,192,357,380],
     frontierNode 170 [17,109,217,248,294]]
  | 50 =>
    [frontierNode 598 [68,136,192,316,380],
     frontierNode 358 [10,68,151,202,294],
     frontierNode 358 [27,68,151,192,294],
     frontierNode 602 [123,175,192,316,400],
     frontierNode 554 [96,105,164,192,316],
     frontierNode 554 [109,192,308,316,347],
     frontierNode 618 [109,151,192,367,380]]
  | 51 =>
    [frontierNode 601 [12,37,123,192,329],
     frontierNode 665 [37,123,230,373,380],
     frontierNode 361 [9,37,164,192,301],
     frontierNode 361 [37,164,192,294,301],
     frontierNode 358 [68,109,151,192,301],
     frontierNode 422 [68,151,239,248,294],
     frontierNode 394 [109,123,230,294,319],
     frontierNode 650 [94,109,123,217,329],
     frontierNode 650 [109,123,217,221,400],
     frontierNode 90 [109,123,188,192,294],
     frontierNode 346 [18,109,123,204,294],
     frontierNode 346 [109,123,151,192,302]]
  | 52 =>
    [frontierNode 601 [37,109,136,192,329],
     frontierNode 617 [37,174,192,329,347],
     frontierNode 410 [109,123,205,230,294],
     frontierNode 666 [123,217,230,340,347],
     frontierNode 362 [109,151,152,192,294],
     frontierNode 170 [109,222,230,248,294],
     frontierNode 426 [109,164,248,294,390]]
  | 53 =>
    [frontierNode 297 [10,37,159,192,294],
     frontierNode 553 [37,96,164,192,339],
     frontierNode 105 [9,37,164,192,294],
     frontierNode 390 [68,123,217,293,294],
     frontierNode 614 [68,175,192,316,342],
     frontierNode 282 [15,103,123,192,294],
     frontierNode 602 [123,169,192,316,329],
     frontierNode 410 [109,123,208,224,294],
     frontierNode 410 [109,123,230,294,388],
     frontierNode 554 [10,164,192,316,347],
     frontierNode 554 [109,155,163,192,347],
     frontierNode 362 [109,192,224,294,310]]
  | 54 =>
    [frontierNode 405 [37,68,136,241,294],
     frontierNode 329 [37,77,123,192,294],
     frontierNode 537 [37,123,134,192,329],
     frontierNode 650 [109,123,316,320,400],
     frontierNode 346 [109,123,192,217,303],
     frontierNode 666 [109,123,230,310,380],
     frontierNode 554 [10,151,192,329],
     frontierNode 170 [100,151,164,241,294]]
  | 55 =>
    [frontierNode 649 [37,94,123,230,340],
     frontierNode 665 [37,123,241,329,377],
     frontierNode 650 [22,109,123,217,380],
     frontierNode 282 [15,109,123,192,294],
     frontierNode 298 [109,151,192,294,309]]
  | 56 =>
    [frontierNode 410 [109,123,217,266,294],
     frontierNode 554 [150,175,192,316,347],
     frontierNode 106 [109,192,224,265,294],
     frontierNode 170 [109,145,150,248,294],
     frontierNode 426 [164,241,248,294,316]]
  | 57 =>
    [frontierNode 585 [37,123,192,200,329],
     frontierNode 601 [11,37,136,192,329],
     frontierNode 586 [109,123,192,219,400],
     frontierNode 282 [103,109,123,192,294],
     frontierNode 346 [109,123,203,294],
     frontierNode 602 [109,123,192,304,329],
     frontierNode 410 [109,123,217,294,391],
     frontierNode 410 [123,211,230,294,340],
     frontierNode 298 [109,151,192,294,314],
     frontierNode 362 [109,151,192,264,294],
     frontierNode 618 [109,151,192,347,400],
     frontierNode 170 [109,156,164,248,294],
     frontierNode 170 [109,217,224,248,294]]
  | 58 =>
    [frontierNode 341 [13,37,68,192,294],
     frontierNode 393 [37,123,230,293,294],
     frontierNode 537 [10,37,123,192,329],
     frontierNode 361 [37,109,164,192,301],
     frontierNode 102 [9,68,147,192,294],
     frontierNode 650 [11,109,123,217,329],
     frontierNode 346 [22,109,111,192,294],
     frontierNode 602 [100,123,192,316,367]]
  | 59 =>
    [frontierNode 341 [37,68,123,202,294],
     frontierNode 405 [37,68,123,202,294],
     frontierNode 617 [37,192,268,340,347],
     frontierNode 425 [37,164,241,243,294],
     frontierNode 390 [68,71,123,217,294],
     frontierNode 150 [68,123,132,217,294],
     frontierNode 358 [26,68,151,192,294],
     frontierNode 650 [24,109,123,316,380],
     frontierNode 602 [109,123,192,329,355],
     frontierNode 666 [123,151,241,329,380],
     frontierNode 554 [109,164,192,328,347],
     frontierNode 362 [151,164,192,294,338],
     frontierNode 618 [109,151,192,329,411],
     frontierNode 618 [109,164,192,316,342]]
  | 60 =>
    [frontierNode 601 [11,37,112,192,329],
     frontierNode 409 [0,37,123,230,294],
     frontierNode 617 [37,158,192,340,347],
     frontierNode 422 [68,151,248,294,406],
     frontierNode 394 [109,123,230,294,318],
     frontierNode 650 [109,123,208,216,380],
     frontierNode 90 [109,122,123,192,294],
     frontierNode 346 [8,109,123,192,294],
     frontierNode 362 [151,192,268,294,340],
     frontierNode 426 [96,151,230,248,294]]
  | 61 =>
    [frontierNode 345 [21,37,123,294,350],
     frontierNode 582 [11,68,123,192,311],
     frontierNode 150 [9,68,123,213,294],
     frontierNode 406 [68,109,136,217,294],
     frontierNode 358 [9,68,151,192,301],
     frontierNode 394 [43,109,123,217,294],
     frontierNode 650 [109,123,217,315,380],
     frontierNode 650 [123,216,241,316,380],
     frontierNode 346 [109,123,192,294,303],
     frontierNode 602 [109,123,192,316,361],
     frontierNode 154 [123,143,175,217,294],
     frontierNode 666 [109,123,248,316,400],
     frontierNode 106 [109,192,209,258,294],
     frontierNode 362 [109,164,192,249,294],
     frontierNode 362 [151,158,192,294,340],
     frontierNode 170 [109,151,158,230,294]]
  | 62 =>
    [frontierNode 581 [37,68,123,192,300],
     frontierNode 149 [37,68,123,199,294],
     frontierNode 649 [37,96,123,230,338],
     frontierNode 153 [9,37,123,226,294],
     frontierNode 390 [68,123,212,217,294],
     frontierNode 358 [68,109,151,202,294],
     frontierNode 538 [123,153,175,192,329],
     frontierNode 346 [17,109,123,192,275],
     frontierNode 170 [9,164,217,248,294]]
  | 63 =>
    [frontierNode 585 [37,43,123,192,329],
     frontierNode 601 [37,123,136,192,329],
     frontierNode 662 [68,123,217,339,380],
     frontierNode 102 [9,68,151,192,294],
     frontierNode 330 [24,109,123,192,294],
     frontierNode 586 [109,123,192,214,316],
     frontierNode 106 [41,109,151,192,294],
     frontierNode 170 [164,229,241,248,294],
     frontierNode 426 [109,230,248,294,357]]
  | 64 =>
    [frontierNode 405 [30,37,68,123,169],
     frontierNode 409 [6,37,123,230,294],
     frontierNode 409 [9,37,123,230,277],
     frontierNode 105 [9,37,160,192,294],
     frontierNode 406 [0,68,123,217,294],
     frontierNode 550 [68,105,173,192,316],
     frontierNode 586 [56,109,123,192,316],
     frontierNode 602 [109,123,192,307,323],
     frontierNode 410 [96,123,217,224,294],
     frontierNode 410 [123,173,217,230,294],
     frontierNode 666 [109,123,230,316,411],
     frontierNode 362 [142,164,192,241,294],
     frontierNode 362 [151,164,192,239,294],
     frontierNode 170 [109,217,224,268,294]]
  | 65 =>
    [frontierNode 601 [20,37,123,192,329],
     frontierNode 614 [68,151,192,340,411],
     frontierNode 330 [109,123,181,192,294],
     frontierNode 586 [123,192,219,241,329],
     frontierNode 394 [123,230,294,378,390],
     frontierNode 90 [109,116,123,192,294],
     frontierNode 346 [7,109,123,192,294],
     frontierNode 602 [109,123,192,329,413],
     frontierNode 602 [109,123,192,367,390],
     frontierNode 154 [123,217,230,246,294],
     frontierNode 410 [109,123,158,294,307],
     frontierNode 362 [151,164,192,294,406]]
  | 66 =>
    [frontierNode 329 [37,123,192,294,392],
     frontierNode 553 [37,95,175,192,329],
     frontierNode 617 [37,105,192,329,377],
     frontierNode 681 [37,164,241,347,380],
     frontierNode 534 [68,75,123,192,316],
     frontierNode 358 [68,151,192,202,294],
     frontierNode 166 [68,100,151,240,294],
     frontierNode 330 [109,123,192,285,294],
     frontierNode 282 [109,123,192,283,294],
     frontierNode 602 [109,123,192,316,317],
     frontierNode 170 [151,216,241,248,294]]
  | 67 =>
    [frontierNode 89 [37,84,123,192,294],
     frontierNode 601 [10,37,123,202,329],
     frontierNode 681 [37,109,248,367,380],
     frontierNode 614 [68,175,192,307,347],
     frontierNode 586 [123,192,329,378,390],
     frontierNode 538 [48,109,123,192,316],
     frontierNode 538 [109,123,155,192,366],
     frontierNode 554 [15,109,192,329,347],
     frontierNode 362 [109,155,192,258,294],
     frontierNode 170 [14,109,248,294],
     frontierNode 426 [175,217,248,294,329]]
  | 68 =>
    [frontierNode 665 [37,123,230,339,380],
     frontierNode 86 [68,123,192,250,294],
     frontierNode 406 [6,68,123,217,294],
     frontierNode 406 [9,68,123,217,277],
     frontierNode 298 [44,109,151,192,294],
     frontierNode 298 [151,192,294,308,340]]
  | 69 =>
    [frontierNode 601 [37,136,192,329,380],
     frontierNode 105 [37,164,191,192,294],
     frontierNode 361 [37,109,164,202,294],
     frontierNode 425 [37,164,241,294,411],
     frontierNode 646 [68,123,219,241,380],
     frontierNode 614 [68,151,192,332,347],
     frontierNode 650 [109,123,219,230,380],
     frontierNode 346 [1,109,123,192,294],
     frontierNode 602 [109,123,192,316,365],
     frontierNode 154 [109,123,156,230,294],
     frontierNode 666 [105,123,230,316,380],
     frontierNode 666 [109,123,217,367,380],
     frontierNode 554 [109,151,192,315,347],
     frontierNode 362 [109,145,155,192,294],
     frontierNode 618 [100,151,192,329,347]]
  | 70 =>
    [frontierNode 393 [37,123,225,230,294],
     frontierNode 345 [37,136,192,294,400],
     frontierNode 425 [37,155,241,248,294],
     frontierNode 410 [123,217,230,294,373],
     frontierNode 666 [123,175,230,316,380],
     frontierNode 554 [15,109,151,192,347],
     frontierNode 362 [109,164,192,294,353],
     frontierNode 170 [109,151,211,230,294],
     frontierNode 426 [109,151,221,248,294],
     frontierNode 426 [109,151,230,243,294]]
  | 71 =>
    [frontierNode 678 [68,109,258,347,380],
     frontierNode 346 [15,109,123,177,294],
     frontierNode 106 [109,151,192,210,294],
     frontierNode 170 [109,151,158,248,294]]
  | 72 =>
    [frontierNode 649 [37,100,123,239,329],
     frontierNode 153 [37,123,132,230,294],
     frontierNode 617 [37,175,192,329,342],
     frontierNode 534 [10,68,123,192,312],
     frontierNode 406 [68,123,136,217,294],
     frontierNode 358 [68,151,192,248,301],
     frontierNode 586 [109,123,192,206,316],
     frontierNode 394 [109,123,230,294,326],
     frontierNode 650 [109,123,206,217,380],
     frontierNode 90 [14,104,123,192,294],
     frontierNode 602 [123,192,241,329,357],
     frontierNode 554 [18,109,192,347],
     frontierNode 362 [109,164,192,294,351]]
  | 73 =>
    [frontierNode 537 [37,123,192,325,329],
     frontierNode 409 [12,37,123,230,294],
     frontierNode 169 [37,100,164,240,294],
     frontierNode 586 [109,123,192,207,316],
     frontierNode 666 [109,123,211,329,380],
     frontierNode 618 [109,164,192,307,347],
     frontierNode 170 [109,145,164,248,294]]
  | 74 =>
    [frontierNode 649 [37,123,305,340,380],
     frontierNode 409 [37,109,136,230,294],
     frontierNode 681 [37,109,248,347,400],
     frontierNode 598 [3,68,123,192,316],
     frontierNode 614 [68,192,274,316,347],
     frontierNode 586 [87,109,123,192,329],
     frontierNode 586 [109,123,192,227,329],
     frontierNode 410 [109,123,211,294,400],
     frontierNode 554 [164,192,316,345,347],
     frontierNode 362 [100,151,192,294,367],
     frontierNode 426 [151,241,248,294,329]]
  | 75 =>
    [frontierNode 553 [37,192,308,340,347],
     frontierNode 602 [109,123,192,316,415],
     frontierNode 602 [123,192,241,310,329],
     frontierNode 106 [72,109,164,192,294],
     frontierNode 362 [109,192,211,294,323]]
  | 76 =>
    [frontierNode 601 [26,37,123,192,329],
     frontierNode 297 [37,164,192,290,294],
     frontierNode 650 [24,109,123,230,380],
     frontierNode 650 [96,123,217,230,340],
     frontierNode 538 [109,123,141,192,316],
     frontierNode 538 [123,140,175,192,316],
     frontierNode 346 [109,123,138,192,294],
     frontierNode 602 [109,123,192,329,384],
     frontierNode 602 [123,174,192,316,329],
     frontierNode 410 [109,123,217,264,294],
     frontierNode 410 [109,123,230,256,294],
     frontierNode 666 [109,123,217,347,400],
     frontierNode 554 [18,109,164,192,347],
     frontierNode 682 [109,151,248,329,380]]
  | 77 =>
    [frontierNode 281 [37,83,123,192,294],
     frontierNode 326 [68,123,192,294,382],
     frontierNode 406 [12,68,123,217,294],
     frontierNode 166 [68,222,241,248,294],
     frontierNode 282 [109,121,123,192,294],
     frontierNode 538 [79,109,123,192,329],
     frontierNode 346 [109,123,192,230,302],
     frontierNode 410 [109,123,217,294,398],
     frontierNode 666 [109,123,224,316,380],
     frontierNode 666 [109,123,258,329,380],
     frontierNode 362 [109,151,192,294,361],
     frontierNode 426 [109,151,248,294,400],
     frontierNode 682 [109,151,230,347,380]]
  | 78 =>
    [frontierNode 585 [37,123,192,324,329],
     frontierNode 169 [37,209,241,248,294],
     frontierNode 86 [50,68,123,192,294],
     frontierNode 538 [109,123,153,192,367],
     frontierNode 346 [109,137,192,294],
     frontierNode 410 [109,123,230,252,294],
     frontierNode 410 [109,123,258,294,400],
     frontierNode 666 [109,123,217,329,411],
     frontierNode 554 [10,109,151,192,329],
     frontierNode 554 [151,192,315,340,347],
     frontierNode 554 [151,192,329,345,347],
     frontierNode 106 [128,151,164,192,294],
     frontierNode 170 [109,151,158,268,294],
     frontierNode 170 [109,164,229,248,294]]
  | 79 =>
    [frontierNode 409 [11,37,136,230,294],
     frontierNode 534 [68,123,192,312,316],
     frontierNode 342 [21,68,123,294,360],
     frontierNode 662 [68,123,211,340,380],
     frontierNode 662 [68,123,241,310,380],
     frontierNode 394 [109,123,294,318,400],
     frontierNode 282 [109,115,123,192,294],
     frontierNode 538 [109,123,153,192,329],
     frontierNode 346 [109,123,151,203,294],
     frontierNode 602 [105,123,192,329,390],
     frontierNode 410 [109,123,211,221,294],
     frontierNode 106 [151,192,246,268,294],
     frontierNode 362 [164,192,258,294,340],
     frontierNode 426 [175,217,230,294,347]]
  | 80 =>
    [frontierNode 281 [37,85,123,192,294],
     frontierNode 425 [37,164,233,248,294],
     frontierNode 422 [68,173,217,248,294],
     frontierNode 650 [109,123,230,316,320],
     frontierNode 650 [123,230,316,378,380],
     frontierNode 602 [123,175,192,329,390],
     frontierNode 554 [109,192,310,329,357],
     frontierNode 106 [80,109,164,192,294],
     frontierNode 426 [109,151,230,294,411]]
  | 81 =>
    [frontierNode 661 [27,37,68,123,380],
     frontierNode 342 [68,136,192,294,390],
     frontierNode 422 [68,241,248,294,357],
     frontierNode 650 [11,123,230,316],
     frontierNode 346 [109,123,192,204,294],
     frontierNode 666 [109,123,268,316,380],
     frontierNode 362 [94,151,164,192,294],
     frontierNode 362 [109,164,192,294,348],
     frontierNode 170 [109,145,164,217,294],
     frontierNode 170 [109,164,217,224,294]]
  | 82 =>
    [frontierNode 409 [11,37,112,230,294],
     frontierNode 582 [68,74,123,192,316],
     frontierNode 662 [68,96,123,217,243],
     frontierNode 422 [68,105,217,294,377],
     frontierNode 678 [68,151,248,340,380],
     frontierNode 538 [123,192,316,329,345],
     frontierNode 410 [105,123,208,230,294],
     frontierNode 298 [82,109,164,192,294],
     frontierNode 362 [109,151,192,259,294]]
  | 83 =>
    [frontierNode 341 [30,37,68,123,192],
     frontierNode 601 [37,136,192,329],
     frontierNode 406 [11,68,136,217,294],
     frontierNode 662 [68,123,258,340,380],
     frontierNode 294 [68,146,151,192,294],
     frontierNode 650 [100,123,241,316,329],
     frontierNode 650 [109,123,217,221,329],
     frontierNode 346 [109,123,164,192,303],
     frontierNode 602 [109,123,155,192,208],
     frontierNode 410 [96,123,211,230,294],
     frontierNode 410 [109,123,217,294,394],
     frontierNode 410 [123,175,208,230,294],
     frontierNode 666 [105,123,217,329,380],
     frontierNode 298 [130,151,164,192,294],
     frontierNode 554 [109,192,316,323,367],
     frontierNode 170 [163,175,230,248,294]]
  | 84 =>
    [frontierNode 101 [37,68,133,192,294],
     frontierNode 617 [37,164,192,340,342],
     frontierNode 598 [68,123,202,316],
     frontierNode 662 [68,123,217,340,411],
     frontierNode 166 [68,105,174,217,294],
     frontierNode 586 [109,123,192,208,389],
     frontierNode 90 [109,118,123,192,294],
     frontierNode 90 [109,123,187,192,294],
     frontierNode 154 [39,109,123,217,294],
     frontierNode 410 [105,123,217,294,400],
     frontierNode 666 [123,175,217,329,380],
     frontierNode 682 [109,230,248,316,347]]
  | 85 =>
    [frontierNode 649 [37,123,206,241,380],
     frontierNode 409 [37,123,136,230,294],
     frontierNode 617 [37,164,192,338,347],
     frontierNode 425 [37,173,230,248,294],
     frontierNode 406 [68,136,217,294,380],
     frontierNode 678 [68,109,248,347,390],
     frontierNode 394 [109,123,294,320,397],
     frontierNode 282 [18,109,123,192,294],
     frontierNode 346 [109,123,192,303],
     frontierNode 154 [109,123,162,230,294],
     frontierNode 410 [123,175,217,294,400],
     frontierNode 298 [75,109,164,192,294],
     frontierNode 362 [109,151,192,294,365]]
  | 86 =>
    [frontierNode 597 [37,68,136,192,340],
     frontierNode 89 [37,123,192,260,294],
     frontierNode 345 [37,92,123,192,294],
     frontierNode 406 [11,68,112,217,294],
     frontierNode 394 [109,123,294,307,387],
     frontierNode 650 [96,100,123,217,329],
     frontierNode 650 [109,123,208,230,390],
     frontierNode 154 [109,123,156,268,294],
     frontierNode 410 [109,123,230,294,413],
     frontierNode 554 [95,109,164,192,316],
     frontierNode 362 [109,142,158,192,294],
     frontierNode 170 [109,163,230,248,294]]
  | 87 =>
    [frontierNode 341 [21,37,68,123,294],
     frontierNode 405 [37,68,123,241,301],
     frontierNode 409 [20,37,123,230,294],
     frontierNode 425 [37,105,230,294,377],
     frontierNode 358 [68,151,192,294,301],
     frontierNode 154 [109,123,157,230,294],
     frontierNode 410 [95,123,217,230,294],
     frontierNode 618 [151,164,192,340,380]]
  | 88 =>
    [frontierNode 581 [37,68,123,192,335],
     frontierNode 598 [10,68,123,178,316],
     frontierNode 662 [68,123,217,334,380],
     frontierNode 586 [123,192,291,316,329],
     frontierNode 106 [109,164,192,223,294],
     frontierNode 682 [109,217,248,329,347]]
  | 89 =>
    [frontierNode 409 [27,37,123,230,294],
     frontierNode 665 [37,123,230,340,411],
     frontierNode 361 [37,164,192,301],
     frontierNode 598 [68,109,136,192,316],
     frontierNode 662 [68,123,241,316,411],
     frontierNode 586 [109,123,192,219,329],
     frontierNode 602 [109,123,192,310,320],
     frontierNode 602 [109,123,192,357,400],
     frontierNode 410 [105,123,217,221,294],
     frontierNode 618 [109,192,248,329,357],
     frontierNode 618 [175,192,248,316,329],
     frontierNode 170 [151,230,246,248,294]]
  | 90 =>
    [frontierNode 389 [37,68,123,201,294],
     frontierNode 661 [26,37,68,123,380],
     frontierNode 393 [37,40,123,230,294],
     frontierNode 409 [37,136,230,294,380],
     frontierNode 361 [3,37,164,192,294],
     frontierNode 169 [37,143,175,248,294],
     frontierNode 90 [109,123,184,192,294],
     frontierNode 346 [14,109,123,192,276],
     frontierNode 410 [123,175,217,221,294],
     frontierNode 362 [100,164,192,294,357]]
  | 91 =>
    [frontierNode 101 [37,68,171,192,294],
     frontierNode 357 [30,37,68,192,235],
     frontierNode 89 [37,81,123,192,294],
     frontierNode 390 [11,68,123,212,294],
     frontierNode 534 [68,123,134,192,316],
     frontierNode 406 [20,68,123,217,294],
     frontierNode 406 [68,123,217,248,301],
     frontierNode 394 [109,123,217,294,305],
     frontierNode 394 [123,194,217,230,294],
     frontierNode 538 [123,192,289,316,329],
     frontierNode 666 [109,123,248,329,390],
     frontierNode 362 [109,151,192,294,415],
     frontierNode 170 [109,224,229,248,294]]
  | 92 =>
    [frontierNode 585 [11,37,123,192,329],
     frontierNode 278 [68,123,192,294,349],
     frontierNode 650 [109,123,230,328,380],
     frontierNode 282 [109,123,192,287,294],
     frontierNode 666 [109,123,230,347,390],
     frontierNode 554 [109,151,155,192,347]]
  | 93 =>
    [frontierNode 665 [37,123,230,334,380],
     frontierNode 553 [37,140,175,192,347],
     frontierNode 617 [37,192,274,329,347],
     frontierNode 406 [27,68,123,217,294],
     frontierNode 394 [123,197,217,230,294],
     frontierNode 298 [109,192,294,321,367],
     frontierNode 106 [49,109,151,192,294],
     frontierNode 106 [164,192,222,241,294],
     frontierNode 170 [109,145,164,258,294],
     frontierNode 426 [109,217,248,294,367]]
  | 94 =>
    [frontierNode 281 [37,76,123,192,294],
     frontierNode 681 [37,109,268,347,380],
     frontierNode 326 [59,68,123,192,294],
     frontierNode 582 [68,123,192,200,316],
     frontierNode 406 [68,109,123,217,301],
     frontierNode 662 [68,100,123,316,342],
     frontierNode 678 [68,217,248,340,347],
     frontierNode 330 [98,109,123,192,294],
     frontierNode 650 [109,123,307,315,380],
     frontierNode 154 [123,190,217,230,294],
     frontierNode 554 [109,142,150,192,347]]
  | 95 =>
    [frontierNode 341 [37,68,192,294,401],
     frontierNode 357 [37,68,192,294,401],
     frontierNode 89 [37,73,123,192,294],
     frontierNode 345 [37,86,123,192,294],
     frontierNode 665 [37,96,123,230,243],
     frontierNode 614 [68,175,192,316,411],
     frontierNode 422 [68,151,241,243,294],
     frontierNode 298 [51,109,151,192,294],
     frontierNode 170 [109,151,216,248,294]]
  | 96 =>
    [frontierNode 601 [37,109,123,202,329],
     frontierNode 409 [37,123,230,248,301],
     frontierNode 297 [37,159,164,192,294],
     frontierNode 598 [6,68,123,192,316],
     frontierNode 90 [104,109,123,192,294],
     frontierNode 346 [24,109,110,192,294],
     frontierNode 410 [109,123,230,254,294],
     frontierNode 666 [123,164,217,340,380],
     frontierNode 554 [15,109,192,347]]
  | _ => []

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
def frontier5 : Nat → List FrontierNode
  | 0 =>
    [frontierNode 329 [37,123,192,197,230,294],
     frontierNode 153 [9,37,123,230,248,294],
     frontierNode 41 [37,105,109,150,192,294],
     frontierNode 297 [37,164,192,294,334,340],
     frontierNode 342 [68,109,123,139,192,294],
     frontierNode 598 [68,109,123,192,307,347],
     frontierNode 330 [109,123,192,206,208,294],
     frontierNode 538 [109,123,192,316,329,357],
     frontierNode 346 [109,123,192,217,294,367],
     frontierNode 106 [100,109,151,164,192,294],
     frontierNode 106 [109,151,158,164,192,294]]
  | 1 =>
    [frontierNode 581 [37,68,123,192,233,380],
     frontierNode 341 [37,68,109,136,192,294],
     frontierNode 329 [37,43,109,123,192,294],
     frontierNode 281 [37,123,192,289,294,329],
     frontierNode 89 [37,123,143,175,192,294],
     frontierNode 297 [37,109,164,192,294,334],
     frontierNode 105 [37,109,150,192,248,294],
     frontierNode 361 [37,109,164,192,243,294],
     frontierNode 582 [68,109,123,192,239,316],
     frontierNode 390 [11,68,123,217,294,380],
     frontierNode 646 [68,123,217,340,380],
     frontierNode 294 [68,109,163,192,294,347],
     frontierNode 166 [68,151,241,248,294],
     frontierNode 394 [109,123,217,221,294]]
  | 2 =>
    [frontierNode 533 [10,37,68,123,192,340],
     frontierNode 341 [11,37,68,112,192,294],
     frontierNode 613 [37,68,175,192,347,380],
     frontierNode 281 [37,123,192,294,340,354],
     frontierNode 345 [37,109,123,192,262,294],
     frontierNode 345 [37,123,192,230,294,373],
     frontierNode 326 [68,123,192,241,294,399],
     frontierNode 278 [68,123,126,151,192,294],
     frontierNode 550 [68,109,175,192,316,347],
     frontierNode 102 [68,109,151,192,211,294],
     frontierNode 358 [68,109,151,192,294,342],
     frontierNode 330 [109,123,192,230,294,399],
     frontierNode 330 [123,192,229,241,294,329],
     frontierNode 586 [123,192,241,316,329],
     frontierNode 90 [123,151,192,216,241,294],
     frontierNode 106 [109,151,192,248,268,294]]
  | 3 =>
    [frontierNode 277 [37,68,123,134,192,294],
     frontierNode 597 [37,68,123,192,340,377],
     frontierNode 293 [37,68,173,192,294,347],
     frontierNode 601 [37,123,192,241,329,347],
     frontierNode 294 [10,68,151,192,294,347],
     frontierNode 102 [68,151,192,246,248,294],
     frontierNode 358 [68,175,192,217,294,347],
     frontierNode 330 [109,123,192,294,316,383],
     frontierNode 410 [109,123,164,217,294,380],
     frontierNode 298 [109,164,192,294,316,357],
     frontierNode 554 [109,151,192,329,347]]
  | 4 =>
    [frontierNode 341 [10,37,68,123,178,294],
     frontierNode 341 [37,68,109,112,192,294],
     frontierNode 405 [37,68,100,123,294,342],
     frontierNode 293 [10,37,68,175,192,294],
     frontierNode 393 [37,94,96,123,230,294],
     frontierNode 345 [37,123,164,192,294,332],
     frontierNode 326 [68,123,192,294,340,393],
     frontierNode 342 [68,123,192,241,294,310],
     frontierNode 598 [68,123,151,192,340,380],
     frontierNode 90 [109,123,164,192,261,294],
     frontierNode 346 [109,123,192,230,294,310]]
  | 5 =>
    [frontierNode 533 [37,68,123,167,192,340],
     frontierNode 149 [37,68,123,169,248,294],
     frontierNode 357 [37,68,175,192,294,411],
     frontierNode 393 [37,109,123,230,294,332],
     frontierNode 153 [9,37,123,230,294],
     frontierNode 326 [68,123,192,194,217,294],
     frontierNode 534 [10,68,109,123,192,316],
     frontierNode 342 [68,109,123,192,205,294],
     frontierNode 150 [68,109,123,229,248,294],
     frontierNode 330 [109,123,192,294,328,400],
     frontierNode 394 [96,123,217,230,294],
     frontierNode 346 [109,123,155,192,217,294]]
  | 6 =>
    [frontierNode 325 [37,68,123,192,200,294],
     frontierNode 277 [37,68,123,192,290,294],
     frontierNode 341 [37,68,123,192,294,368],
     frontierNode 149 [37,68,97,123,240,294],
     frontierNode 329 [37,123,192,294,340,383],
     frontierNode 393 [11,37,123,230,294,380],
     frontierNode 649 [37,123,230,340,380],
     frontierNode 537 [10,37,123,192,329,347],
     frontierNode 646 [68,123,241,316,380],
     frontierNode 342 [68,96,123,145,192,294],
     frontierNode 282 [109,123,151,192,294,350],
     frontierNode 282 [123,163,175,192,294,329],
     frontierNode 90 [109,123,150,192,258,294]]
  | 7 =>
    [frontierNode 389 [37,68,94,123,239,294],
     frontierNode 341 [13,37,68,109,192,294],
     frontierNode 341 [37,68,109,123,192,269],
     frontierNode 149 [37,68,123,240,248,294],
     frontierNode 329 [37,123,192,241,294,389],
     frontierNode 137 [37,100,109,123,216,294],
     frontierNode 86 [68,123,192,241,265,294],
     frontierNode 358 [68,151,192,241,294,347],
     frontierNode 266 [123,192,294,315,328,340],
     frontierNode 74 [109,123,192,216,229,294],
     frontierNode 330 [109,123,192,216,294,390],
     frontierNode 282 [109,123,164,192,294,328],
     frontierNode 90 [109,123,192,230,265,294],
     frontierNode 106 [151,164,192,241,294],
     frontierNode 362 [109,151,192,230,294,347]]
  | 8 =>
    [frontierNode 325 [37,68,94,123,192,294],
     frontierNode 581 [11,37,68,123,192,340],
     frontierNode 341 [37,68,123,294,368],
     frontierNode 101 [37,68,175,192,240,294],
     frontierNode 329 [37,109,123,192,294,387],
     frontierNode 345 [37,123,192,241,294,367],
     frontierNode 601 [37,109,123,192,329,342],
     frontierNode 617 [37,109,164,192,347,380],
     frontierNode 278 [68,123,153,175,192,294],
     frontierNode 534 [68,95,105,123,192,316],
     frontierNode 342 [68,109,123,192,294,348],
     frontierNode 586 [96,109,123,192,217,329],
     frontierNode 282 [123,150,175,192,294,316],
     frontierNode 538 [96,109,123,164,192,316],
     frontierNode 298 [109,151,192,294,367]]
  | 9 =>
    [frontierNode 86 [68,109,123,162,192,294],
     frontierNode 150 [9,68,123,217,294],
     frontierNode 150 [68,97,109,123,217,294],
     frontierNode 150 [68,123,169,175,217,294],
     frontierNode 550 [68,151,192,340,347],
     frontierNode 102 [68,109,151,192,235,294],
     frontierNode 394 [123,217,230,294,340],
     frontierNode 90 [109,123,151,192,216,294],
     frontierNode 154 [105,123,217,230,294]]
  | 10 =>
    [frontierNode 405 [37,68,123,233,248,294],
     frontierNode 357 [37,68,192,246,294,347],
     frontierNode 393 [37,109,123,216,294,380],
     frontierNode 534 [68,123,192,316,345,347],
     frontierNode 86 [68,123,124,151,192,294],
     frontierNode 406 [68,109,123,217,294,377],
     frontierNode 330 [109,123,192,294,318,320],
     frontierNode 394 [109,123,217,294,380,400],
     frontierNode 282 [109,123,192,294,350,357],
     frontierNode 154 [123,175,217,230,294]]
  | 11 =>
    [frontierNode 341 [9,37,68,123,192,277],
     frontierNode 341 [37,68,123,192,242,294],
     frontierNode 281 [10,37,123,192,294,367],
     frontierNode 89 [37,123,164,192,246,294],
     frontierNode 153 [9,37,109,123,230,294],
     frontierNode 409 [37,123,164,241,294,380],
     frontierNode 105 [37,105,175,192,230,294],
     frontierNode 361 [37,109,164,192,294,411],
     frontierNode 361 [37,175,192,230,294,347],
     frontierNode 518 [68,96,123,192,328,340],
     frontierNode 326 [68,123,192,219,241,294],
     frontierNode 582 [11,68,109,123,192,316],
     frontierNode 582 [68,94,100,123,192,316],
     frontierNode 342 [68,123,192,211,294,340],
     frontierNode 150 [68,109,123,169,217,294],
     frontierNode 282 [109,123,142,150,192,294],
     frontierNode 346 [123,175,192,217,294,329]]
  | 12 =>
    [frontierNode 533 [37,68,123,173,192,340],
     frontierNode 341 [37,68,109,123,178,294],
     frontierNode 341 [37,68,123,136,192,294],
     frontierNode 341 [37,68,123,192,231,294],
     frontierNode 341 [37,68,123,192,277],
     frontierNode 421 [37,68,241,248,294,347],
     frontierNode 329 [37,109,123,192,294,313],
     frontierNode 585 [37,109,123,192,233,329],
     frontierNode 89 [37,123,175,192,257,294],
     frontierNode 345 [37,100,123,192,294,323],
     frontierNode 361 [37,109,155,192,248,294],
     frontierNode 278 [68,109,123,192,294,364],
     frontierNode 150 [68,109,123,174,217,294],
     frontierNode 394 [109,123,217,294,329,400],
     frontierNode 394 [109,123,230,294,390]]
  | 13 =>
    [frontierNode 533 [37,68,95,123,192,340],
     frontierNode 85 [37,68,123,192,246,294],
     frontierNode 393 [37,94,109,123,230,294]]
  | 14 =>
    [frontierNode 341 [37,68,93,123,192,294],
     frontierNode 341 [37,68,123,192,247,294],
     frontierNode 597 [37,68,123,192,340,342],
     frontierNode 345 [37,105,123,192,294,320],
     frontierNode 105 [37,109,164,192,240,294],
     frontierNode 390 [68,100,123,217,294,340],
     frontierNode 330 [109,123,192,294,329,397],
     frontierNode 538 [109,123,192,316,329,367],
     frontierNode 90 [109,123,151,192,251,294]]
  | 15 =>
    [frontierNode 341 [37,68,123,192,294,404],
     frontierNode 341 [37,68,136,192,294],
     frontierNode 597 [37,68,123,192,338,347],
     frontierNode 293 [37,68,95,175,192,294],
     frontierNode 293 [37,68,175,192,294,339],
     frontierNode 393 [37,109,123,294,320,400],
     frontierNode 281 [37,109,123,148,192,294],
     frontierNode 345 [37,123,175,192,294,320],
     frontierNode 105 [37,150,175,192,248,294],
     frontierNode 534 [10,68,123,192,316],
     frontierNode 534 [68,109,123,142,192,347],
     frontierNode 342 [68,96,123,192,211,294],
     frontierNode 342 [68,123,192,258,294,340],
     frontierNode 150 [68,100,123,175,217,294],
     frontierNode 358 [68,109,192,258,294,347],
     frontierNode 330 [109,123,192,229,294,400],
     frontierNode 330 [109,123,192,294,390,400],
     frontierNode 282 [109,123,192,294,308,310],
     frontierNode 346 [123,151,192,241,294,329],
     frontierNode 154 [109,123,217,230,268,294],
     frontierNode 106 [100,151,164,192,294]]
  | 16 =>
    [frontierNode 341 [37,68,192,294,401,406],
     frontierNode 165 [37,68,235,241,248,294],
     frontierNode 89 [37,109,123,192,209,294],
     frontierNode 326 [68,123,192,294,318,340],
     frontierNode 38 [68,105,109,163,192,294],
     frontierNode 586 [109,123,192,316,320],
     frontierNode 90 [109,123,192,222,224,294],
     frontierNode 106 [109,145,151,164,192,294],
     frontierNode 106 [109,151,192,268,294],
     frontierNode 106 [109,164,192,217,258,294]]
  | 17 =>
    [frontierNode 341 [37,68,123,192,294,402],
     frontierNode 357 [37,68,169,192,294,347],
     frontierNode 393 [11,37,123,230,294],
     frontierNode 89 [37,109,123,192,263,294],
     frontierNode 105 [37,105,164,192,241,294],
     frontierNode 342 [68,100,123,192,294,357],
     frontierNode 342 [68,109,123,192,294,388],
     frontierNode 294 [68,105,151,192,294,340],
     frontierNode 282 [109,123,140,151,192,294],
     frontierNode 90 [109,123,192,216,258,294]]
  | 18 =>
    [frontierNode 277 [37,68,123,192,294,373],
     frontierNode 341 [37,68,112,192,294],
     frontierNode 597 [37,68,123,192,373,380],
     frontierNode 149 [37,68,97,123,241,294],
     frontierNode 101 [37,68,97,174,192,294],
     frontierNode 329 [37,123,192,292,294,329],
     frontierNode 345 [37,109,123,192,294,396],
     frontierNode 409 [37,109,123,230,294,377],
     frontierNode 598 [68,109,123,192,310,380],
     frontierNode 138 [100,109,123,229,230,294],
     frontierNode 394 [109,123,217,230,294,390],
     frontierNode 298 [109,151,155,164,192,294]]
  | 19 =>
    [frontierNode 341 [37,68,192,294,380,401],
     frontierNode 329 [37,40,109,123,192,294],
     frontierNode 89 [37,123,192,251,274,294],
     frontierNode 345 [37,100,123,155,192,294],
     frontierNode 326 [68,123,192,294,393,406],
     frontierNode 390 [68,109,123,294,307,390],
     frontierNode 330 [109,123,192,219,221,294]]
  | 20 =>
    [frontierNode 341 [37,68,123,165,192,294],
     frontierNode 341 [37,68,123,192,294,331],
     frontierNode 281 [37,109,123,192,294,308],
     frontierNode 89 [37,109,123,192,257,294],
     frontierNode 617 [37,109,192,248,329,347],
     frontierNode 326 [68,109,123,192,227,294],
     frontierNode 390 [68,123,229,241,294,380],
     frontierNode 342 [68,123,173,192,217,294],
     frontierNode 342 [68,123,174,192,294,316],
     frontierNode 394 [109,123,229,230,294,380],
     frontierNode 282 [123,164,192,294,328,340],
     frontierNode 90 [17,109,123,164,192,294]]
  | 21 =>
    [frontierNode 581 [37,68,123,192,239,340],
     frontierNode 389 [37,68,100,123,239,294],
     frontierNode 341 [37,68,123,192,269],
     frontierNode 341 [37,68,123,192,294,409],
     frontierNode 281 [37,123,164,192,294,345],
     frontierNode 297 [37,105,175,192,294,329],
     frontierNode 297 [37,109,164,192,294,339],
     frontierNode 361 [37,100,164,192,294,347],
     frontierNode 390 [11,68,123,217,294],
     frontierNode 278 [68,123,192,294,316,345],
     frontierNode 586 [109,123,192,307,329]]
  | 22 =>
    [frontierNode 341 [37,68,123,192,294,376],
     frontierNode 341 [37,68,123,294,368,373],
     frontierNode 597 [37,68,96,123,192,243],
     frontierNode 165 [37,68,175,241,248,294],
     frontierNode 421 [37,68,175,248,294,380],
     frontierNode 393 [37,100,123,230,294,340],
     frontierNode 537 [37,123,167,175,192,329],
     frontierNode 326 [68,109,123,192,294,385],
     frontierNode 86 [9,68,123,192,258,294],
     frontierNode 342 [68,105,123,192,294,307],
     frontierNode 90 [109,123,143,145,192,294],
     frontierNode 346 [100,123,151,192,294,329],
     frontierNode 154 [109,123,230,258,294],
     frontierNode 106 [105,109,164,192,217,294]]
  | 23 =>
    [frontierNode 277 [37,68,123,192,294,345],
     frontierNode 341 [37,68,108,123,192,294],
     frontierNode 585 [37,109,123,192,221,400],
     frontierNode 345 [37,123,192,235,294,329],
     frontierNode 390 [68,123,217,294,378,380],
     frontierNode 534 [68,96,105,123,192,316],
     frontierNode 86 [68,109,123,192,253,294],
     frontierNode 342 [68,105,123,192,208,294],
     frontierNode 342 [68,123,175,192,294,307],
     frontierNode 330 [109,123,192,294,329,393],
     frontierNode 346 [100,123,164,192,294,316],
     frontierNode 602 [109,123,151,192,329,380]]
  | 24 =>
    [frontierNode 101 [37,68,105,174,192,294],
     frontierNode 89 [37,39,109,123,192,294],
     frontierNode 345 [37,123,192,240,294,329],
     frontierNode 553 [37,109,175,192,329,347],
     frontierNode 518 [68,96,109,123,192,328],
     frontierNode 326 [68,109,123,192,294,318],
     frontierNode 390 [68,109,123,217,294,307],
     frontierNode 342 [68,123,175,192,208,294],
     frontierNode 358 [68,96,151,192,248,294],
     frontierNode 358 [68,151,192,248,294,340],
     frontierNode 330 [22,109,123,192,294],
     frontierNode 394 [100,109,123,230,294,316],
     frontierNode 282 [109,123,151,192,294,356],
     frontierNode 346 [109,123,151,192,294,400],
     frontierNode 298 [109,164,192,294,357]]
  | 25 =>
    [frontierNode 325 [37,68,123,192,293,294],
     frontierNode 101 [9,37,68,175,192,294],
     frontierNode 649 [37,123,241,329,380],
     frontierNode 537 [37,95,109,123,192,329],
     frontierNode 153 [37,97,109,123,230,294],
     frontierNode 153 [37,123,169,175,230,294],
     frontierNode 361 [37,109,192,248,294,367],
     frontierNode 326 [68,123,192,294,378,385],
     frontierNode 582 [68,94,109,123,192,316],
     frontierNode 278 [68,109,123,153,192,294],
     frontierNode 586 [109,123,192,316,329,390]]
  | 26 =>
    [frontierNode 341 [37,68,123,178,294],
     frontierNode 341 [37,68,123,192,232,294],
     frontierNode 613 [37,68,192,248,340,347],
     frontierNode 521 [37,96,109,123,192,315],
     frontierNode 585 [37,96,100,123,192,329],
     frontierNode 390 [68,109,123,229,294,380],
     frontierNode 86 [68,70,109,123,192,294],
     frontierNode 342 [68,123,151,192,233,294],
     frontierNode 166 [68,175,217,248,294],
     frontierNode 298 [96,109,151,164,192,294],
     frontierNode 106 [109,164,192,248,258,294]]
  | 27 =>
    [frontierNode 341 [3,37,68,123,192,294],
     frontierNode 341 [37,68,123,192,248,277],
     frontierNode 149 [37,68,123,169,241,294],
     frontierNode 405 [37,68,123,235,294,380],
     frontierNode 537 [37,96,123,175,192,329],
     frontierNode 345 [37,123,192,274,294,329],
     frontierNode 153 [37,109,123,169,230,294],
     frontierNode 582 [68,109,123,192,208,390],
     frontierNode 390 [68,100,123,241,294,316],
     frontierNode 330 [109,123,192,208,216,294]]
  | 28 =>
    [frontierNode 277 [10,37,68,123,192,294],
     frontierNode 341 [37,68,107,123,192,294],
     frontierNode 149 [37,68,123,174,241,294],
     frontierNode 405 [37,68,123,240,294,380],
     frontierNode 345 [37,109,123,192,266,294],
     frontierNode 153 [37,109,123,174,230,294],
     frontierNode 169 [37,109,164,241,248,294],
     frontierNode 425 [37,109,164,248,294,380],
     frontierNode 582 [68,96,123,192,241,316],
     frontierNode 598 [68,109,123,192,316,411],
     frontierNode 294 [68,109,192,294,310,347],
     frontierNode 166 [68,109,145,151,248,294],
     frontierNode 154 [109,123,217,230,258,294],
     frontierNode 298 [109,164,192,294,347,357]]
  | 29 =>
    [frontierNode 533 [37,68,96,123,192,339],
     frontierNode 341 [37,68,112,192,294,380],
     frontierNode 341 [37,68,123,202,294,347],
     frontierNode 101 [37,68,192,235,248,294],
     frontierNode 345 [37,109,123,192,294,363],
     frontierNode 345 [37,109,123,192,294,391],
     frontierNode 326 [68,123,192,217,294,378],
     frontierNode 86 [68,123,192,222,241,294],
     frontierNode 586 [109,123,192,315,316,380],
     frontierNode 346 [109,123,151,192,221,294],
     frontierNode 298 [109,163,164,192,294,347]]
  | 30 =>
    [frontierNode 389 [37,68,123,241,294,332],
     frontierNode 293 [37,68,95,173,192,294],
     frontierNode 549 [37,68,175,192,340,347],
     frontierNode 329 [37,123,192,206,241,294],
     frontierNode 134 [68,100,109,123,229,294],
     frontierNode 390 [68,109,123,294,307,380],
     frontierNode 90 [109,123,143,151,192,294],
     frontierNode 346 [105,123,192,230,294,316],
     frontierNode 298 [109,150,151,192,294,347]]
  | 31 =>
    [frontierNode 341 [30,37,68,123,175,192],
     frontierNode 597 [37,68,123,192,347,406],
     frontierNode 405 [37,68,123,274,294,380],
     frontierNode 153 [37,100,123,175,230,294],
     frontierNode 297 [10,37,164,192,294],
     frontierNode 169 [37,175,230,248,294],
     frontierNode 278 [68,109,123,192,294,327],
     frontierNode 294 [10,68,109,151,192,294],
     frontierNode 102 [68,100,105,151,192,294],
     frontierNode 330 [109,123,192,294,316,387],
     frontierNode 298 [109,151,192,294,347,367]]
  | 32 =>
    [frontierNode 341 [21,37,68,123,294,340],
     frontierNode 149 [37,68,123,169,274,294],
     frontierNode 585 [37,123,192,315,340,380],
     frontierNode 345 [37,96,123,158,192,294],
     frontierNode 326 [68,123,192,291,294,316],
     frontierNode 582 [68,96,123,192,217,340],
     frontierNode 390 [68,96,100,123,217,294],
     frontierNode 406 [68,109,123,208,248,294],
     frontierNode 90 [109,123,192,211,216,294],
     frontierNode 170 [109,164,217,248,294]]
  | 33 =>
    [frontierNode 585 [37,109,123,192,315,380],
     frontierNode 390 [68,109,123,217,294,338],
     frontierNode 598 [68,105,123,192,316,380],
     frontierNode 358 [68,175,192,248,294,316],
     frontierNode 298 [96,151,164,192,294]]
  | 34 =>
    [frontierNode 325 [11,37,68,123,192,294],
     frontierNode 341 [30,37,68,123,192,274],
     frontierNode 341 [37,68,109,123,192,301],
     frontierNode 329 [37,123,192,294,340,387],
     frontierNode 585 [37,123,192,233,241,329],
     frontierNode 537 [37,109,123,155,192,367],
     frontierNode 598 [68,123,175,192,316,380],
     frontierNode 294 [68,109,151,192,294,334],
     frontierNode 358 [68,109,151,192,243,294],
     frontierNode 282 [18,109,123,164,192,294],
     frontierNode 538 [109,123,192,316,323,329],
     frontierNode 42 [105,109,163,164,192,294]]
  | 35 =>
    [frontierNode 597 [37,68,123,192,339,380],
     frontierNode 537 [37,109,123,155,192,329],
     frontierNode 297 [37,164,192,294,345,347],
     frontierNode 326 [68,109,123,192,219,294],
     frontierNode 534 [68,109,123,142,192,316],
     frontierNode 86 [68,123,192,261,274,294],
     frontierNode 150 [68,100,123,151,241,294],
     frontierNode 90 [109,123,192,251,258,294],
     frontierNode 154 [109,123,217,268,294]]
  | 36 =>
    [frontierNode 341 [37,68,123,192,248,269],
     frontierNode 341 [37,68,123,192,294,333],
     frontierNode 597 [37,68,123,192,345,380],
     frontierNode 597 [37,68,123,192,347,378],
     frontierNode 281 [37,123,130,164,192,294],
     frontierNode 345 [37,96,123,192,224,294],
     frontierNode 345 [37,123,173,192,230,294],
     frontierNode 553 [37,109,164,192,340,347],
     frontierNode 326 [68,109,123,192,294,326],
     frontierNode 150 [68,109,123,145,248,294],
     frontierNode 330 [109,123,192,219,230,294],
     frontierNode 394 [109,123,230,294,380,390],
     frontierNode 282 [109,123,192,294,328,367],
     frontierNode 538 [109,123,192,316,323]]
  | 37 =>
    [frontierNode 341 [10,37,68,123,202,294],
     frontierNode 329 [37,123,192,230,294,378],
     frontierNode 345 [37,123,192,224,294,340],
     frontierNode 105 [9,37,164,192,248,294],
     frontierNode 278 [68,123,175,192,294,360],
     frontierNode 342 [68,123,151,192,294,332],
     frontierNode 330 [109,123,192,294,307,315],
     frontierNode 298 [109,142,151,164,192,294]]
  | 38 =>
    [frontierNode 645 [37,68,123,233,241,380],
     frontierNode 341 [13,37,68,192,294,406],
     frontierNode 341 [30,37,68,123,192,241],
     frontierNode 89 [37,109,123,192,215,294],
     frontierNode 601 [37,109,123,192,320,347],
     frontierNode 297 [10,37,109,164,192,294],
     frontierNode 326 [68,74,109,123,192,294],
     frontierNode 582 [68,109,123,192,208,380],
     frontierNode 278 [68,123,192,294,340,364],
     frontierNode 342 [68,123,192,217,294,334],
     frontierNode 598 [68,100,123,192,316,347],
     frontierNode 586 [109,123,192,329,380,390],
     frontierNode 90 [17,109,123,192,294],
     frontierNode 346 [96,123,151,192,230,294]]
  | 39 =>
    [frontierNode 277 [37,68,95,123,192,294],
     frontierNode 341 [37,68,123,192,294,330],
     frontierNode 281 [37,123,175,192,294,350],
     frontierNode 86 [68,123,192,246,258,294],
     frontierNode 550 [68,175,192,316,347],
     frontierNode 330 [109,123,192,206,217,294],
     frontierNode 154 [109,123,216,217,248,294]]
  | 40 =>
    [frontierNode 341 [30,37,68,109,123,192],
     frontierNode 341 [37,68,123,192,234,294],
     frontierNode 357 [37,68,174,192,294,347],
     frontierNode 89 [9,37,123,192,268,294],
     frontierNode 89 [37,123,128,164,192,294],
     frontierNode 345 [37,109,123,192,294,358],
     frontierNode 345 [37,123,164,192,294,338],
     frontierNode 105 [37,164,192,235,241,294],
     frontierNode 278 [68,123,192,294,345,357],
     frontierNode 86 [68,109,123,192,222,294],
     frontierNode 342 [68,109,123,192,256,294]]
  | 41 =>
    [frontierNode 533 [37,68,95,123,192,339],
     frontierNode 341 [27,37,68,123,192,294],
     frontierNode 165 [37,68,169,175,248,294],
     frontierNode 393 [37,109,123,230,294,338],
     frontierNode 393 [37,123,230,294,378,380],
     frontierNode 345 [37,123,192,268,294,340],
     frontierNode 601 [37,109,123,192,367,380],
     frontierNode 105 [37,100,105,164,192,294],
     frontierNode 361 [37,109,192,268,294,347],
     frontierNode 342 [68,109,123,192,294,304],
     frontierNode 294 [10,68,151,192,294],
     frontierNode 614 [68,109,151,192,347,380]]
  | 42 =>
    [frontierNode 341 [37,68,123,192,294,371],
     frontierNode 341 [37,68,192,241,294,401],
     frontierNode 405 [37,68,123,239,248,294],
     frontierNode 345 [37,123,158,192,294,340],
     frontierNode 361 [37,109,158,192,294,347],
     frontierNode 342 [68,109,123,192,252,294],
     frontierNode 282 [109,123,151,192,294,315],
     frontierNode 346 [109,123,192,224,294,316]]
  | 43 =>
    [frontierNode 405 [37,68,123,241,294,377],
     frontierNode 585 [37,123,192,329,378,380],
     frontierNode 281 [37,123,192,294,329,345],
     frontierNode 345 [37,109,123,152,192,294],
     frontierNode 342 [68,95,123,192,217,294],
     frontierNode 406 [68,96,123,217,248,294],
     frontierNode 538 [109,123,164,192,316,367],
     frontierNode 154 [109,123,151,230,258,294]]
  | 44 =>
    [frontierNode 341 [13,37,68,192,294,340],
     frontierNode 357 [37,68,192,248,294,373],
     frontierNode 281 [37,109,123,140,192,294],
     frontierNode 297 [37,109,192,294,323,367],
     frontierNode 86 [68,123,151,192,246,294],
     frontierNode 342 [68,109,123,192,294,355],
     frontierNode 150 [68,109,123,145,217,294],
     frontierNode 406 [68,123,151,241,294,380],
     frontierNode 358 [68,109,151,192,294,411],
     frontierNode 330 [24,109,123,192,294,316],
     frontierNode 586 [100,109,123,192,316,329],
     frontierNode 282 [109,123,192,294,321,329],
     frontierNode 346 [109,123,192,217,294,323],
     frontierNode 346 [123,151,192,230,294,340],
     frontierNode 410 [109,123,151,230,294,380],
     frontierNode 410 [109,123,217,248,294,329],
     frontierNode 362 [109,164,192,217,294,347]]
  | 45 =>
    [frontierNode 341 [37,68,109,123,202,294],
     frontierNode 345 [37,123,164,192,239,294],
     frontierNode 153 [37,100,123,164,241,294],
     frontierNode 553 [37,109,192,323,329,347],
     frontierNode 278 [68,109,123,192,294,360],
     frontierNode 662 [68,109,123,248,316,380],
     frontierNode 330 [123,192,217,294,315,340],
     frontierNode 90 [123,150,175,192,217,294],
     frontierNode 554 [109,164,192,316,347]]
  | 46 =>
    [frontierNode 341 [21,37,68,123,175,294],
     frontierNode 341 [37,68,123,178,294,347],
     frontierNode 341 [37,68,123,294,347,368],
     frontierNode 89 [37,41,109,123,192,294],
     frontierNode 345 [37,123,164,192,294,406],
     frontierNode 345 [37,123,192,230,294,334],
     frontierNode 582 [68,109,123,192,233,316],
     frontierNode 646 [68,109,123,208,217,380],
     frontierNode 330 [109,123,192,294,383,390],
     frontierNode 346 [109,123,192,268,294,316]]
  | 47 =>
    [frontierNode 389 [37,68,94,123,241,294],
     frontierNode 341 [9,37,68,123,192,301],
     frontierNode 341 [37,68,123,192,272,294],
     frontierNode 341 [37,68,123,294,340,368],
     frontierNode 281 [37,38,109,123,192,294],
     frontierNode 281 [37,109,123,192,294,350],
     frontierNode 89 [37,123,175,192,251,294],
     frontierNode 345 [37,97,123,192,294,329],
     frontierNode 153 [37,123,216,241,248,294],
     frontierNode 41 [37,105,150,175,192,294],
     frontierNode 297 [37,109,164,192,294,323],
     frontierNode 102 [68,109,151,192,240,294],
     frontierNode 102 [68,163,175,192,248,294],
     frontierNode 330 [109,123,192,229,294,329],
     frontierNode 282 [15,109,123,151,192,294],
     frontierNode 282 [109,123,153,164,192,294],
     frontierNode 90 [14,109,123,192,294],
     frontierNode 346 [109,123,158,192,294,316]]
  | 48 =>
    [frontierNode 325 [37,68,123,192,294,406],
     frontierNode 341 [6,37,68,123,192,294],
     frontierNode 341 [37,68,123,192,294,416],
     frontierNode 341 [37,68,123,192,301],
     frontierNode 585 [37,96,123,192,230,340],
     frontierNode 393 [37,96,100,123,230,294],
     frontierNode 281 [37,109,123,192,294,314],
     frontierNode 537 [37,109,123,167,192,329],
     frontierNode 345 [37,109,123,192,264,294],
     frontierNode 601 [37,109,123,192,347,400],
     frontierNode 105 [37,164,192,246,248,294],
     frontierNode 169 [37,109,158,164,248,294],
     frontierNode 582 [68,123,192,328,340,380],
     frontierNode 86 [68,72,109,123,192,294],
     frontierNode 86 [68,123,156,175,192,294],
     frontierNode 342 [68,100,123,142,192,294],
     frontierNode 282 [109,123,192,294,323,328],
     frontierNode 154 [109,123,230,248,258,294]]
  | 49 =>
    [frontierNode 85 [9,37,68,123,192,294],
     frontierNode 149 [37,68,100,123,240,294],
     frontierNode 357 [37,68,192,248,294,345],
     frontierNode 281 [37,123,192,294,308,340],
     frontierNode 345 [37,109,123,192,294,398],
     frontierNode 297 [37,109,150,192,294,347],
     frontierNode 582 [11,68,123,192,316],
     frontierNode 534 [68,109,123,142,192,357],
     frontierNode 294 [68,96,105,151,192,294],
     frontierNode 102 [68,97,100,151,192,294],
     frontierNode 330 [22,109,123,192,294,329],
     frontierNode 26 [123,150,163,175,192,294],
     frontierNode 282 [123,151,192,294,315,340],
     frontierNode 90 [109,123,158,163,192,294]]
  | 50 =>
    [frontierNode 281 [37,123,192,294,345,362],
     frontierNode 601 [37,109,123,192,329,411],
     frontierNode 342 [68,109,123,192,294,413],
     frontierNode 102 [68,105,151,192,241,294],
     frontierNode 102 [68,109,163,192,248,294],
     frontierNode 394 [109,123,230,294,316,390]]
  | 51 =>
    [frontierNode 341 [37,68,123,166,192,294],
     frontierNode 405 [37,68,123,248,294,406],
     frontierNode 281 [37,44,109,123,192,294],
     frontierNode 409 [37,96,123,230,248,294],
     frontierNode 326 [68,123,192,294,316,378],
     frontierNode 538 [109,123,192,316,347,367],
     frontierNode 154 [100,109,123,164,217,294],
     frontierNode 154 [109,123,217,248,268,294]]
  | 52 =>
    [frontierNode 389 [37,68,123,294,332,406],
     frontierNode 101 [37,68,97,175,192,294],
     frontierNode 357 [37,68,173,192,248,294],
     frontierNode 281 [37,123,192,294,350,373],
     frontierNode 345 [37,123,192,241,294,323],
     frontierNode 153 [37,109,123,158,230,294],
     frontierNode 361 [37,164,192,241,294,347],
     frontierNode 278 [68,123,175,192,294,366],
     frontierNode 150 [68,123,217,246,248,294],
     frontierNode 294 [68,151,192,294,334,340],
     frontierNode 102 [9,68,109,151,192,294],
     frontierNode 538 [109,123,192,329,347,357]]
  | 53 =>
    [frontierNode 325 [37,68,123,192,294,378],
     frontierNode 341 [0,37,68,123,192,294],
     frontierNode 341 [37,68,123,192,294,407],
     frontierNode 89 [37,109,123,143,192,294],
     frontierNode 105 [9,37,164,192,294],
     frontierNode 105 [37,109,164,192,224,294],
     frontierNode 342 [68,123,142,192,241,294],
     frontierNode 342 [68,123,167,192,217,294],
     frontierNode 406 [68,109,123,217,243,294],
     frontierNode 74 [123,192,216,229,241,294],
     frontierNode 282 [109,123,192,294,357,367],
     frontierNode 90 [109,123,192,209,211,294],
     frontierNode 346 [123,175,192,230,294,316]]
  | 54 =>
    [frontierNode 341 [26,37,68,123,192,294],
     frontierNode 357 [37,68,105,192,294,377],
     frontierNode 278 [68,69,109,123,192,294],
     frontierNode 278 [68,123,151,192,294,345],
     frontierNode 278 [68,123,192,288,294,316],
     frontierNode 294 [68,109,151,192,294,339],
     frontierNode 358 [68,100,151,192,294,347],
     frontierNode 586 [109,123,192,217,329,390],
     frontierNode 394 [109,123,208,217,230,294],
     frontierNode 282 [109,123,150,192,294,316],
     frontierNode 282 [109,123,192,294,308,316],
     frontierNode 90 [109,123,192,222,230,294],
     frontierNode 90 [109,123,192,229,268,294],
     frontierNode 346 [109,123,164,192,294,307],
     frontierNode 106 [109,151,158,192,294]]
  | 55 =>
    [frontierNode 341 [21,37,68,109,123,294],
     frontierNode 585 [37,109,123,192,221,329],
     frontierNode 537 [37,109,123,173,192,329],
     frontierNode 89 [37,109,123,192,251,294],
     frontierNode 345 [37,109,123,192,294,394],
     frontierNode 601 [37,105,123,192,329,380],
     frontierNode 409 [37,123,241,248,294,329],
     frontierNode 150 [68,97,105,123,217,294],
     frontierNode 294 [68,105,175,192,294,316],
     frontierNode 282 [15,109,123,192,294],
     frontierNode 346 [109,123,164,192,208,294],
     frontierNode 298 [109,151,164,192,294,357]]
  | 56 =>
    [frontierNode 341 [37,68,123,192,294,337],
     frontierNode 597 [37,68,123,192,340,411],
     frontierNode 405 [37,68,123,248,294,378],
     frontierNode 101 [37,68,192,235,274,294],
     frontierNode 345 [37,105,123,192,294,400],
     frontierNode 601 [37,123,175,192,329,380],
     frontierNode 326 [68,71,109,123,192,294],
     frontierNode 582 [68,109,123,192,328,380],
     frontierNode 278 [68,109,123,192,294,321],
     frontierNode 534 [68,123,167,175,192,316],
     frontierNode 598 [68,109,123,192,347,390],
     frontierNode 150 [68,109,123,145,258,294],
     frontierNode 26 [109,123,150,163,192,294],
     frontierNode 538 [109,123,192,315,316,347],
     frontierNode 90 [109,123,192,217,251,294],
     frontierNode 410 [109,123,217,230,294,347],
     frontierNode 106 [109,145,164,192,294]]
  | 57 =>
    [frontierNode 341 [37,68,123,168,192,294],
     frontierNode 341 [37,68,123,192,202,294],
     frontierNode 341 [37,68,136,192,294,380],
     frontierNode 405 [37,68,123,246,294,380],
     frontierNode 649 [37,109,123,221,230,380],
     frontierNode 281 [37,123,175,192,294,356],
     frontierNode 345 [37,123,175,192,294,400],
     frontierNode 86 [68,123,175,192,267,294],
     frontierNode 342 [68,123,192,235,294,316],
     frontierNode 342 [68,123,192,241,294,357],
     frontierNode 330 [22,109,123,192,217,294],
     frontierNode 282 [109,123,192,294,329,364],
     frontierNode 538 [109,123,192,310,316,329],
     frontierNode 90 [14,109,123,151,192,294],
     frontierNode 346 [109,123,192,230,294,357],
     frontierNode 154 [100,109,123,151,230,294]]
  | 58 =>
    [frontierNode 341 [13,37,68,192,294],
     frontierNode 341 [37,68,123,172,192,294],
     frontierNode 341 [37,68,123,192,241,269],
     frontierNode 281 [37,109,123,192,294,362],
     frontierNode 537 [10,37,123,192,329],
     frontierNode 553 [37,175,192,329,347],
     frontierNode 278 [68,75,109,123,192,294],
     frontierNode 342 [68,123,192,217,294,339],
     frontierNode 342 [68,123,192,240,294,316],
     frontierNode 406 [68,109,123,211,294,380],
     frontierNode 586 [96,109,123,192,230,316],
     frontierNode 586 [109,123,192,316,400]]
  | 59 =>
    [frontierNode 341 [37,68,123,202,294],
     frontierNode 341 [37,68,192,294,340,401],
     frontierNode 537 [37,123,192,315,340,347],
     frontierNode 537 [37,123,192,329,345,347],
     frontierNode 345 [37,95,123,192,230,294],
     frontierNode 297 [37,96,105,164,192,294],
     frontierNode 105 [9,37,109,164,192,294],
     frontierNode 105 [37,97,100,164,192,294],
     frontierNode 534 [68,95,109,123,192,316],
     frontierNode 586 [100,123,192,316,329],
     frontierNode 586 [109,123,192,316,320,329],
     frontierNode 90 [109,123,163,192,230,294],
     frontierNode 298 [109,151,155,192,294],
     frontierNode 298 [109,151,164,192,294,340],
     frontierNode 106 [109,164,192,258,294]]
  | 60 =>
    [frontierNode 581 [37,68,123,192,233,406],
     frontierNode 597 [37,68,123,192,332,347],
     frontierNode 597 [37,68,123,192,334,380],
     frontierNode 357 [37,68,175,192,294,342],
     frontierNode 537 [37,109,123,192,315,347],
     frontierNode 89 [37,123,192,246,268,294],
     frontierNode 345 [37,123,169,192,294,329],
     frontierNode 601 [37,100,123,192,329,347],
     frontierNode 582 [68,96,100,123,192,316],
     frontierNode 278 [68,109,123,192,294,366],
     frontierNode 342 [68,109,123,192,254,294],
     frontierNode 662 [68,109,123,217,347,380],
     frontierNode 102 [68,109,192,211,248,294],
     frontierNode 394 [109,123,216,217,294,380],
     frontierNode 282 [109,123,153,155,192,294]]
  | 61 =>
    [frontierNode 341 [12,37,68,123,192,294],
     frontierNode 677 [37,68,109,248,347,380],
     frontierNode 345 [37,105,123,192,221,294],
     frontierNode 409 [37,109,123,221,248,294],
     frontierNode 409 [37,109,123,230,243,294],
     frontierNode 646 [68,109,123,217,340,380],
     frontierNode 534 [68,96,123,175,192,316],
     frontierNode 342 [68,100,123,192,294,310],
     frontierNode 342 [68,109,123,192,294,384],
     frontierNode 342 [68,123,192,274,294,316],
     frontierNode 166 [68,109,151,241,248,294],
     frontierNode 422 [68,109,151,248,294,380],
     frontierNode 330 [109,123,192,294,393,400],
     frontierNode 538 [96,109,123,151,192,329]]
  | 62 =>
    [frontierNode 533 [37,68,123,192,339,347],
     frontierNode 341 [37,68,123,192,294,346],
     frontierNode 341 [37,68,123,192,294,405],
     frontierNode 345 [37,123,175,192,221,294],
     frontierNode 153 [37,109,123,158,248,294],
     frontierNode 169 [37,164,241,248,294],
     frontierNode 342 [68,94,123,151,192,294],
     frontierNode 406 [68,109,123,258,294,380],
     frontierNode 294 [68,109,192,294,310,357],
     frontierNode 282 [109,123,192,294,315,357]]
  | 63 =>
    [frontierNode 389 [37,68,123,239,294,380],
     frontierNode 341 [37,68,123,192,248,301],
     frontierNode 341 [37,68,123,192,269,274],
     frontierNode 329 [37,109,123,192,294,305],
     frontierNode 297 [37,150,175,192,294,347],
     frontierNode 582 [11,68,123,192,316,380],
     frontierNode 278 [10,68,123,192,294,357],
     frontierNode 406 [68,109,123,217,294,411],
     frontierNode 102 [9,68,151,192,294],
     frontierNode 102 [68,97,109,151,192,294],
     frontierNode 166 [68,109,211,217,248,294],
     frontierNode 330 [24,109,123,192,230,294],
     frontierNode 330 [24,109,123,192,294],
     frontierNode 538 [109,123,192,329,357],
     frontierNode 90 [123,164,192,229,241,294],
     frontierNode 106 [109,151,192,230,268,294]]
  | 64 =>
    [frontierNode 533 [37,68,123,167,192,347],
     frontierNode 549 [37,68,192,334,340,347],
     frontierNode 585 [37,109,123,192,239,329],
     frontierNode 89 [37,123,192,241,251,294],
     frontierNode 297 [10,37,164,192,294,347],
     frontierNode 342 [68,105,123,192,294,390]]
  | 65 =>
    [frontierNode 341 [37,68,106,123,192,294],
     frontierNode 281 [37,109,123,192,294,356],
     frontierNode 537 [10,37,109,123,192,329],
     frontierNode 345 [37,100,123,192,294,367],
     frontierNode 86 [68,109,123,192,267,294],
     frontierNode 342 [68,123,175,192,294,390],
     frontierNode 330 [109,123,192,216,294,316],
     frontierNode 282 [18,109,123,192,294,316],
     frontierNode 538 [105,109,123,192,316,329],
     frontierNode 602 [109,123,164,192,316,380]]
  | 66 =>
    [frontierNode 581 [37,68,123,192,233,340],
     frontierNode 389 [37,68,123,241,294,338],
     frontierNode 533 [37,68,123,167,192,373],
     frontierNode 89 [37,123,190,192,230,294],
     frontierNode 345 [37,123,192,230,294,339],
     frontierNode 361 [37,109,164,192,294,342],
     frontierNode 326 [68,109,123,192,294,397],
     frontierNode 646 [68,109,123,241,316,380],
     frontierNode 86 [68,109,123,192,228,294],
     frontierNode 294 [68,109,151,192,294,310],
     frontierNode 550 [68,109,142,151,192,347],
     frontierNode 538 [109,123,192,310,329],
     frontierNode 346 [109,123,145,192,294,329],
     frontierNode 602 [109,123,192,248,316,329]]
  | 67 =>
    [frontierNode 581 [37,68,94,123,192,338],
     frontierNode 341 [37,68,123,192,271,294],
     frontierNode 101 [37,68,175,192,235,294],
     frontierNode 665 [37,109,123,248,329,380],
     frontierNode 586 [109,123,192,328,329,380],
     frontierNode 282 [109,123,155,163,192,294]]
  | 68 =>
    [frontierNode 329 [37,123,192,294,305,340],
     frontierNode 329 [37,123,192,294,378,400],
     frontierNode 393 [37,109,123,294,320,380],
     frontierNode 393 [37,123,216,241,294,380],
     frontierNode 345 [37,109,123,192,294,361],
     frontierNode 601 [37,123,164,192,340,380],
     frontierNode 409 [37,109,123,248,294,400],
     frontierNode 665 [37,109,123,230,347,380],
     frontierNode 582 [68,123,192,233,241,316],
     frontierNode 646 [68,109,123,307,316,380],
     frontierNode 406 [68,105,123,217,294,380],
     frontierNode 282 [109,123,150,192,294,357],
     frontierNode 282 [109,123,163,192,294,367],
     frontierNode 282 [109,123,164,192,294,360]]
  | 69 =>
    [frontierNode 649 [37,109,123,230,340,380],
     frontierNode 345 [37,123,167,192,230,294],
     frontierNode 153 [37,109,123,158,268,294],
     frontierNode 361 [37,164,192,248,294,340],
     frontierNode 406 [68,123,175,217,294,380],
     frontierNode 550 [68,109,151,192,340,347],
     frontierNode 358 [68,109,142,192,248,294],
     frontierNode 282 [109,123,140,142,192,294],
     frontierNode 282 [109,123,163,192,294,329],
     frontierNode 298 [109,151,164,192,294,367]]
  | 70 =>
    [frontierNode 293 [37,68,192,294,334,347],
     frontierNode 89 [37,123,192,246,263,294],
     frontierNode 153 [37,123,230,246,248,294],
     frontierNode 553 [37,164,192,340,347],
     frontierNode 86 [68,123,175,192,261,294],
     frontierNode 342 [68,96,123,192,258,294],
     frontierNode 330 [109,123,192,294,305,307],
     frontierNode 282 [109,123,192,294,316,350],
     frontierNode 538 [109,123,175,192,316,329]]
  | 71 =>
    [frontierNode 341 [37,68,123,192,294,369],
     frontierNode 585 [11,37,109,123,192,329],
     frontierNode 537 [37,95,105,123,192,329],
     frontierNode 89 [37,109,123,192,255,294],
     frontierNode 153 [37,97,105,123,230,294],
     frontierNode 409 [37,109,123,230,294,411],
     frontierNode 278 [68,123,192,294,340,360],
     frontierNode 298 [151,164,192,294,340],
     frontierNode 106 [105,109,151,192,230,294]]
  | 72 =>
    [frontierNode 645 [37,68,123,332,340,380],
     frontierNode 293 [37,68,192,294,334,373],
     frontierNode 329 [37,109,123,192,214,294],
     frontierNode 345 [37,94,123,164,192,294],
     frontierNode 598 [68,109,123,192,316,377],
     frontierNode 90 [109,123,192,217,255,294],
     frontierNode 90 [109,123,192,261,268,294],
     frontierNode 154 [109,123,211,217,230,294],
     frontierNode 42 [105,109,150,151,192,294]]
  | 73 =>
    [frontierNode 389 [11,37,68,123,241,294],
     frontierNode 661 [37,68,123,248,340,380],
     frontierNode 293 [37,68,105,173,192,294],
     frontierNode 329 [37,123,192,294,329,378],
     frontierNode 281 [37,109,123,192,294,354],
     frontierNode 281 [37,123,192,294,340,350],
     frontierNode 345 [37,109,123,192,259,294],
     frontierNode 345 [37,109,123,192,294,317],
     frontierNode 105 [37,97,109,164,192,294],
     frontierNode 105 [37,109,164,192,235,294],
     frontierNode 278 [68,123,192,294,321,340],
     frontierNode 342 [68,123,151,192,294,338],
     frontierNode 598 [68,109,123,192,357,380],
     frontierNode 598 [68,123,192,217,340,347],
     frontierNode 406 [68,123,217,248,294,340],
     frontierNode 102 [9,68,151,192,248,294],
     frontierNode 422 [68,109,217,248,294,347],
     frontierNode 330 [109,123,192,294,305,316],
     frontierNode 330 [109,123,192,294,320,328],
     frontierNode 394 [109,123,217,230,294,400],
     frontierNode 170 [109,151,230,248,294]]
  | 74 =>
    [frontierNode 341 [37,68,123,192,294,410],
     frontierNode 585 [37,94,100,123,192,329],
     frontierNode 89 [37,109,123,149,192,294],
     frontierNode 390 [68,123,217,294,332,340],
     frontierNode 150 [68,100,105,123,217,294],
     frontierNode 358 [68,109,192,248,294,357],
     frontierNode 362 [109,164,192,248,294,316]]
  | 75 =>
    [frontierNode 341 [30,37,68,123,192,248],
     frontierNode 341 [37,68,123,192,294,408],
     frontierNode 326 [68,109,123,192,294,393],
     frontierNode 278 [68,123,192,294,360,373],
     frontierNode 534 [68,123,192,328,340,347]]
  | 76 =>
    [frontierNode 85 [37,68,97,123,192,294],
     frontierNode 341 [13,37,68,192,294,380],
     frontierNode 341 [37,68,123,192,294,341],
     frontierNode 549 [37,68,167,175,192,347],
     frontierNode 585 [37,109,123,192,221,380],
     frontierNode 345 [37,109,123,192,294,365],
     frontierNode 409 [37,105,123,230,294,380],
     frontierNode 326 [68,123,192,294,378,390],
     frontierNode 86 [68,123,189,192,217,294],
     frontierNode 86 [68,123,192,246,253,294],
     frontierNode 406 [68,109,123,248,294,390],
     frontierNode 294 [68,95,96,151,192,294],
     frontierNode 90 [109,123,151,192,257,294],
     frontierNode 90 [109,123,163,192,268,294]]
  | 77 =>
    [frontierNode 341 [13,37,68,192,241,294],
     frontierNode 329 [37,109,123,192,294,383],
     frontierNode 137 [37,100,123,216,241,294],
     frontierNode 409 [37,123,175,230,294,380],
     frontierNode 154 [109,123,217,224,294],
     frontierNode 106 [109,151,164,192,268,294]]
  | 78 =>
    [frontierNode 341 [37,68,123,175,294,368],
     frontierNode 341 [37,68,123,192,238,294],
     frontierNode 341 [37,68,123,192,294,301],
     frontierNode 86 [68,109,123,192,261,294],
     frontierNode 342 [68,123,151,192,239,294],
     frontierNode 598 [68,123,192,241,316,347],
     frontierNode 330 [109,123,192,217,294,383],
     frontierNode 586 [109,123,192,316,380,400],
     frontierNode 650 [109,123,230,316,380],
     frontierNode 346 [109,123,142,192,230,294],
     frontierNode 602 [109,123,192,230,316,347],
     frontierNode 298 [109,142,164,192,294],
     frontierNode 106 [109,163,164,192,248,294]]
  | 79 =>
    [frontierNode 581 [37,68,94,123,192,340],
     frontierNode 342 [68,123,151,192,294,406],
     frontierNode 330 [109,123,192,221,229,294],
     frontierNode 394 [100,109,123,217,294,329],
     frontierNode 346 [109,123,151,192,294,320],
     frontierNode 346 [109,123,192,211,294,329],
     frontierNode 106 [109,150,151,192,248,294]]
  | 80 =>
    [frontierNode 89 [37,123,192,241,255,294],
     frontierNode 390 [11,68,109,123,217,294],
     frontierNode 102 [68,109,192,211,258,294],
     frontierNode 586 [109,123,192,316,329,400]]
  | 81 =>
    [frontierNode 341 [37,68,109,192,294,401],
     frontierNode 341 [37,68,123,192,294,403],
     frontierNode 357 [37,68,192,274,294,347],
     frontierNode 329 [37,109,123,192,206,294],
     frontierNode 601 [37,123,192,230,340,347],
     frontierNode 297 [37,105,164,192,294,340],
     frontierNode 169 [37,109,224,230,248,294],
     frontierNode 278 [68,123,192,294,345,352],
     frontierNode 342 [68,97,123,192,294,316],
     frontierNode 282 [109,123,192,294,360,367],
     frontierNode 538 [105,123,192,316,329],
     frontierNode 90 [109,123,192,224,229,294],
     frontierNode 346 [123,164,192,217,294,340],
     frontierNode 298 [105,109,151,192,294,329]]
  | 82 =>
    [frontierNode 585 [11,37,123,192,329,380],
     frontierNode 345 [37,109,123,192,294,415],
     frontierNode 553 [37,109,155,164,192,347],
     frontierNode 534 [68,109,123,167,192,316],
     frontierNode 282 [109,123,192,294,310,315],
     frontierNode 538 [123,175,192,316,329],
     frontierNode 298 [105,109,164,192,294,316]]
  | 83 =>
    [frontierNode 341 [30,37,68,123,192],
     frontierNode 329 [11,37,123,192,294,400],
     frontierNode 537 [37,109,123,155,192,347],
     frontierNode 345 [37,123,174,192,294,329],
     frontierNode 601 [37,109,123,192,323,380],
     frontierNode 534 [68,109,123,192,328,347],
     frontierNode 342 [68,109,123,192,294,386],
     frontierNode 598 [68,109,123,192,316,342],
     frontierNode 138 [100,109,123,216,217,294],
     frontierNode 282 [15,109,123,192,294,329],
     frontierNode 282 [109,123,164,192,294,366],
     frontierNode 90 [14,109,123,192,230,294],
     frontierNode 346 [109,123,192,258,294,329]]
  | 84 =>
    [frontierNode 409 [37,109,123,224,294,380],
     frontierNode 326 [68,123,192,241,294,393],
     frontierNode 534 [10,68,123,192,316,347],
     frontierNode 522 [96,109,123,192,328,329],
     frontierNode 330 [109,123,192,217,294,315],
     frontierNode 330 [109,123,192,230,294,393],
     frontierNode 330 [109,123,192,294,318,329],
     frontierNode 330 [123,192,216,241,294,316],
     frontierNode 538 [109,123,151,192,329,357]]
  | 85 =>
    [frontierNode 581 [37,68,123,192,338,380],
     frontierNode 357 [37,68,167,192,248,294],
     frontierNode 521 [37,96,123,192,315,340],
     frontierNode 649 [37,109,123,320,329,380],
     frontierNode 281 [37,123,140,175,192,294],
     frontierNode 582 [68,109,123,192,208,316],
     frontierNode 390 [68,94,96,123,217,294],
     frontierNode 534 [68,96,123,151,192,340],
     frontierNode 342 [68,109,123,192,249,294],
     frontierNode 294 [68,95,109,151,192,294],
     frontierNode 282 [18,109,123,192,294],
     frontierNode 346 [105,123,192,217,294,329]]
  | 86 =>
    [frontierNode 581 [37,68,96,123,192,338],
     frontierNode 405 [37,68,123,241,243,294],
     frontierNode 329 [37,123,192,241,294,383],
     frontierNode 537 [37,96,105,123,192,329],
     frontierNode 153 [37,109,123,216,248,294],
     frontierNode 297 [37,95,96,164,192,294],
     frontierNode 105 [37,109,192,224,248,294],
     frontierNode 86 [68,123,192,217,246,294],
     frontierNode 550 [68,109,192,310,316,347],
     frontierNode 166 [68,109,175,217,248,294],
     frontierNode 330 [123,192,230,294,328,340],
     frontierNode 90 [109,123,145,150,192,294],
     frontierNode 346 [96,123,164,192,217,294],
     frontierNode 154 [109,123,164,217,268,294]]
  | 87 =>
    [frontierNode 341 [21,37,68,123,294],
     frontierNode 393 [37,109,123,230,294,320],
     frontierNode 89 [37,123,192,209,241,294],
     frontierNode 86 [68,123,192,241,261,294],
     frontierNode 294 [68,151,192,294,345,347],
     frontierNode 330 [109,123,192,294,315,390],
     frontierNode 586 [109,123,192,241,316,329],
     frontierNode 282 [109,123,192,294,321,323],
     frontierNode 90 [109,123,156,164,192,294],
     frontierNode 90 [109,123,192,230,261,294]]
  | 88 =>
    [frontierNode 149 [9,37,68,123,241,294],
     frontierNode 329 [37,109,123,192,294,395],
     frontierNode 585 [37,94,109,123,192,329],
     frontierNode 649 [37,109,123,241,329,380],
     frontierNode 281 [37,123,192,294,345,367],
     frontierNode 409 [37,109,123,268,294,380],
     frontierNode 361 [37,96,164,192,248,294],
     frontierNode 586 [109,123,192,329,390],
     frontierNode 90 [17,109,123,192,217,294],
     frontierNode 90 [109,123,164,192,267,294]]
  | 89 =>
    [frontierNode 341 [37,68,123,192,294,372],
     frontierNode 341 [37,68,123,192,294,379],
     frontierNode 101 [37,68,174,192,248,294],
     frontierNode 278 [68,109,123,161,192,294],
     frontierNode 278 [68,109,123,192,294,352],
     frontierNode 534 [68,109,123,173,192,316],
     frontierNode 406 [68,123,241,248,294,316],
     frontierNode 586 [109,123,192,307,316,329],
     frontierNode 538 [109,123,192,316,367]]
  | 90 =>
    [frontierNode 389 [37,68,123,294,332,380],
     frontierNode 341 [37,68,123,192,270,294],
     frontierNode 393 [37,100,123,241,294,329],
     frontierNode 345 [37,109,123,192,218,294],
     frontierNode 345 [37,123,164,192,233,294],
     frontierNode 153 [37,100,105,123,230,294],
     frontierNode 326 [68,109,123,192,294,399],
     frontierNode 86 [68,109,123,156,192,294],
     frontierNode 330 [109,123,192,230,294,328],
     frontierNode 282 [109,123,192,294,329,360],
     frontierNode 90 [109,123,192,258,268,294],
     frontierNode 154 [105,109,123,217,230,294],
     frontierNode 106 [109,151,164,192,258,294]]
  | 91 =>
    [frontierNode 341 [21,37,68,123,294,347],
     frontierNode 341 [37,68,109,123,294,368],
     frontierNode 341 [37,68,123,175,192,269],
     frontierNode 329 [37,123,192,294,378,395],
     frontierNode 585 [37,96,123,192,241,329],
     frontierNode 345 [37,96,123,192,268,294],
     frontierNode 409 [37,123,230,248,294,340],
     frontierNode 425 [37,109,230,248,294,347],
     frontierNode 582 [68,123,192,316,378,380],
     frontierNode 342 [68,123,192,217,294,373],
     frontierNode 394 [109,123,208,230,294],
     frontierNode 90 [109,123,150,192,217,294],
     frontierNode 298 [109,151,192,294,329,367],
     frontierNode 362 [109,151,164,192,294,380]]
  | 92 =>
    [frontierNode 85 [37,68,123,192,274,294],
     frontierNode 341 [20,37,68,123,192,294],
     frontierNode 341 [37,68,123,192,269,294],
     frontierNode 341 [37,68,123,192,294,370],
     frontierNode 341 [37,68,123,192,294,401],
     frontierNode 293 [37,68,175,192,294,334],
     frontierNode 357 [37,68,175,192,243,294],
     frontierNode 585 [11,37,123,192,329],
     frontierNode 393 [37,123,230,294,332,340],
     frontierNode 326 [68,123,192,294,340,397],
     frontierNode 150 [9,68,123,217,248,294],
     frontierNode 102 [68,105,175,192,217,294],
     frontierNode 102 [68,151,192,235,241,294],
     frontierNode 394 [109,123,217,221,230,294],
     frontierNode 650 [109,123,217,329,380],
     frontierNode 602 [109,123,192,217,329,347],
     frontierNode 106 [109,151,164,192,241,294],
     frontierNode 362 [109,151,192,248,294,329]]
  | 93 =>
    [frontierNode 341 [21,37,68,123,294,373],
     frontierNode 661 [37,68,123,241,347,380],
     frontierNode 329 [37,123,192,294,383,406],
     frontierNode 393 [11,37,109,123,230,294],
     frontierNode 345 [37,123,155,192,241,294],
     frontierNode 297 [37,109,192,294,323,347],
     frontierNode 105 [37,109,192,224,268,294],
     frontierNode 134 [68,100,123,229,241,294],
     frontierNode 394 [109,123,217,294,400],
     frontierNode 90 [123,163,175,192,230,294]]
  | 94 =>
    [frontierNode 645 [37,68,123,241,340,380],
     frontierNode 89 [37,123,192,230,246,294],
     frontierNode 601 [37,109,123,192,329,377],
     frontierNode 169 [37,109,175,230,248,294],
     frontierNode 326 [11,68,123,192,294,390],
     frontierNode 390 [68,94,109,123,217,294],
     frontierNode 390 [68,109,123,217,294,332],
     frontierNode 342 [68,109,123,192,294,353],
     frontierNode 342 [68,109,123,192,294,381],
     frontierNode 342 [68,123,169,192,294,316],
     frontierNode 394 [109,123,217,230,294,340],
     frontierNode 538 [109,123,192,328,329,347],
     frontierNode 346 [123,164,192,241,294,316],
     frontierNode 154 [109,123,217,224,230,294]]
  | 95 =>
    [frontierNode 341 [37,68,109,123,192,277],
     frontierNode 341 [37,68,123,192,273,294],
     frontierNode 341 [37,68,192,294,401],
     frontierNode 329 [37,109,123,192,294,389],
     frontierNode 537 [37,96,123,164,192,340],
     frontierNode 297 [37,95,109,164,192,294],
     frontierNode 86 [68,109,123,192,265,294],
     frontierNode 342 [68,123,145,192,294,340],
     frontierNode 150 [9,68,109,123,217,294],
     frontierNode 294 [68,163,175,192,294,347],
     frontierNode 358 [68,109,145,192,294,347],
     frontierNode 614 [68,109,192,248,316,347],
     frontierNode 266 [109,123,192,294,315,328],
     frontierNode 522 [96,109,123,192,315,316],
     frontierNode 586 [109,123,192,230,316,400],
     frontierNode 394 [96,109,123,217,230,294],
     frontierNode 90 [109,123,156,158,192,294],
     frontierNode 154 [109,123,175,217,230,294]]
  | 96 =>
    [frontierNode 85 [37,68,123,132,192,294],
     frontierNode 85 [37,68,123,191,192,294],
     frontierNode 341 [11,37,68,136,192,294],
     frontierNode 405 [37,68,123,241,294,411],
     frontierNode 361 [37,175,192,248,294,329],
     frontierNode 342 [68,109,123,192,294,351],
     frontierNode 150 [68,123,229,241,248,294],
     frontierNode 38 [68,105,163,175,192,294],
     frontierNode 330 [109,123,192,217,294,389],
     frontierNode 282 [109,123,192,294,316,354],
     frontierNode 90 [109,123,164,192,229,294],
     frontierNode 90 [109,123,192,209,217,294],
     frontierNode 346 [109,123,164,192,294,390],
     frontierNode 154 [109,123,211,230,294],
     frontierNode 154 [109,123,229,230,248,294],
     frontierNode 410 [109,123,230,248,294,316]]
  | _ => []

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
def frontier6 : Nat → List FrontierNode
  | 0 =>
    [frontierNode 277 [37,68,109,123,167,192,294],
     frontierNode 533 [37,68,123,192,340,347]]
  | 1 =>
    [frontierNode 517 [37,68,96,123,192,340],
     frontierNode 85 [37,68,97,105,123,192,294],
     frontierNode 281 [37,109,123,192,294,323,329],
     frontierNode 330 [109,123,192,217,294,329]]
  | 3 =>
    [frontierNode 325 [37,68,96,123,192,239,294],
     frontierNode 325 [37,68,123,192,294,380,406],
     frontierNode 329 [37,109,123,192,241,294,329],
     frontierNode 326 [68,100,123,192,294,316]]
  | 4 =>
    [frontierNode 105 [37,109,164,192,248,294]]
  | 5 =>
    [frontierNode 281 [37,109,123,155,164,192,294],
     frontierNode 74 [109,123,192,216,217,294]]
  | 6 =>
    [frontierNode 325 [37,68,123,192,294,332],
     frontierNode 85 [37,68,109,123,192,235,294],
     frontierNode 89 [37,100,123,164,192,294],
     frontierNode 278 [68,109,123,151,192,294,357]]
  | 7 =>
    [frontierNode 277 [37,68,109,123,173,192,294],
     frontierNode 89 [37,109,123,192,268,294],
     frontierNode 38 [68,105,109,151,192,294]]
  | 8 =>
    [frontierNode 325 [37,68,94,123,192,294]]
  | 9 =>
    [frontierNode 325 [11,37,68,123,192,294,380],
     frontierNode 329 [37,123,192,241,294,329],
     frontierNode 26 [109,123,163,164,192,294]]
  | 10 =>
    [frontierNode 278 [68,109,123,151,192,294,340]]
  | 11 =>
    [frontierNode 325 [37,68,109,123,192,294,338],
     frontierNode 341 [37,68,123,192,248,294,340],
     frontierNode 357 [37,68,109,192,248,294,347],
     frontierNode 329 [37,109,123,192,230,294,400]]
  | 12 =>
    [frontierNode 325 [37,68,123,192,294,332,340],
     frontierNode 277 [37,68,123,192,294,347,373],
     frontierNode 25 [37,109,123,150,175,192,294],
     frontierNode 70 [68,123,192,229,241,294]]
  | 13 =>
    [frontierNode 133 [37,68,100,109,123,241,294],
     frontierNode 389 [37,68,123,241,294,380],
     frontierNode 277 [37,68,123,192,294,340,373],
     frontierNode 85 [9,37,68,109,123,192,294],
     frontierNode 85 [37,68,123,192,246,294]]
  | 14 =>
    [frontierNode 277 [37,68,105,123,192,294,340],
     frontierNode 278 [68,96,123,151,192,294],
     frontierNode 342 [68,109,123,192,217,294,347]]
  | 15 =>
    [frontierNode 277 [10,37,68,109,123,192,294],
     frontierNode 277 [37,68,123,175,192,294,340],
     frontierNode 293 [37,68,109,175,192,294,347],
     frontierNode 86 [68,100,109,123,151,192,294]]
  | 16 =>
    [frontierNode 325 [37,68,109,123,192,239,294]]
  | 17 =>
    [frontierNode 325 [37,68,109,123,192,294,406],
     frontierNode 41 [37,105,109,164,192,294],
     frontierNode 278 [68,109,123,142,151,192,294]]
  | 18 =>
    [frontierNode 277 [37,68,123,192,294,373],
     frontierNode 25 [37,123,150,175,192,294],
     frontierNode 281 [37,109,123,192,294,347,367],
     frontierNode 138 [109,123,217,230,294]]
  | 19 =>
    [frontierNode 86 [68,109,123,145,192,294]]
  | 20 =>
    [frontierNode 85 [37,68,100,105,123,192,294],
     frontierNode 25 [37,109,123,150,192,294]]
  | 21 =>
    [frontierNode 341 [37,68,96,123,192,248,294],
     frontierNode 86 [68,123,151,192,241,294]]
  | 22 =>
    [frontierNode 325 [37,68,109,123,192,294,378],
     frontierNode 326 [68,100,109,123,192,294,316]]
  | 23 =>
    [frontierNode 277 [37,68,95,105,123,192,294],
     frontierNode 277 [37,68,123,192,294,345],
     frontierNode 329 [37,109,123,192,294,320],
     frontierNode 281 [37,96,109,123,164,192,294]]
  | 24 =>
    [frontierNode 85 [37,68,100,123,174,192,294],
     frontierNode 281 [37,96,123,164,192,294]]
  | 25 =>
    [frontierNode 278 [68,105,123,192,294,316]]
  | 26 =>
    [frontierNode 325 [37,68,94,100,123,192,294],
     frontierNode 325 [37,68,123,192,241,294,406],
     frontierNode 329 [37,109,123,192,294,320,329],
     frontierNode 278 [68,123,175,192,294,316]]
  | 28 =>
    [frontierNode 277 [10,37,68,123,192,294],
     frontierNode 134 [68,100,109,123,217,294],
     frontierNode 86 [68,109,123,192,211,294]]
  | 30 =>
    [frontierNode 329 [37,109,123,192,221,230,294],
     frontierNode 326 [68,123,192,217,294,340]]
  | 31 =>
    [frontierNode 325 [37,68,94,96,123,192,294],
     frontierNode 277 [37,68,109,123,192,294,334],
     frontierNode 277 [37,68,123,167,192,294],
     frontierNode 341 [37,68,109,123,192,243,294],
     frontierNode 326 [68,109,123,192,294,307]]
  | 32 =>
    [frontierNode 325 [37,68,123,192,241,294,340],
     frontierNode 329 [37,109,123,192,230,294,340],
     frontierNode 89 [37,109,123,192,224,230,294],
     frontierNode 326 [68,109,123,192,208,294],
     frontierNode 278 [68,109,123,192,294,310,316]]
  | 34 =>
    [frontierNode 325 [11,37,68,123,192,294],
     frontierNode 70 [68,109,123,192,229,241,294]]
  | 35 =>
    [frontierNode 85 [37,68,105,123,192,240,294]]
  | 36 =>
    [frontierNode 22 [68,109,123,163,192,294]]
  | 37 =>
    [frontierNode 85 [37,68,123,192,235,294],
     frontierNode 265 [37,109,123,192,294,315,340],
     frontierNode 102 [68,109,151,192,248,294],
     frontierNode 266 [109,123,192,294,328,329],
     frontierNode 74 [109,123,192,229,230,294]]
  | 38 =>
    [frontierNode 277 [37,68,96,105,123,192,294],
     frontierNode 277 [37,68,123,173,192,294],
     frontierNode 85 [37,68,97,100,123,192,294],
     frontierNode 597 [37,68,109,123,192,347,380],
     frontierNode 329 [37,123,192,230,294,340]]
  | 39 =>
    [frontierNode 581 [37,68,109,123,192,340,380],
     frontierNode 277 [37,68,95,123,192,294],
     frontierNode 277 [37,68,123,192,294,334,340]]
  | 40 =>
    [frontierNode 325 [37,68,94,109,123,192,294],
     frontierNode 521 [37,96,109,123,192,329]]
  | 41 =>
    [frontierNode 341 [37,68,109,123,192,294,411],
     frontierNode 278 [68,96,109,123,151,192,294],
     frontierNode 86 [68,109,123,151,192,258,294]]
  | 42 =>
    [frontierNode 325 [37,68,123,192,294,338],
     frontierNode 277 [37,68,105,123,192,294,339],
     frontierNode 85 [9,37,68,123,192,248,294],
     frontierNode 582 [68,109,123,192,316,380],
     frontierNode 342 [68,109,123,151,192,294,380]]
  | 43 =>
    [frontierNode 325 [37,68,96,123,192,241,294],
     frontierNode 325 [37,68,123,192,294,340,406],
     frontierNode 265 [37,123,192,294,315,340],
     frontierNode 281 [37,109,123,192,294,323],
     frontierNode 326 [68,123,192,241,294,316],
     frontierNode 278 [68,105,109,123,192,294,316],
     frontierNode 86 [68,109,123,151,192,241,294],
     frontierNode 330 [109,123,192,230,294,316]]
  | 44 =>
    [frontierNode 85 [37,68,109,123,192,240,294],
     frontierNode 137 [37,100,109,123,230,294],
     frontierNode 342 [68,109,123,192,248,294,316]]
  | 45 =>
    [frontierNode 329 [37,109,123,192,294,380,400],
     frontierNode 89 [37,109,123,158,192,294]]
  | 46 =>
    [frontierNode 341 [37,68,105,123,192,294,380],
     frontierNode 293 [37,68,175,192,294,347],
     frontierNode 281 [37,109,123,164,192,294,340],
     frontierNode 90 [109,123,151,192,230,294],
     frontierNode 42 [109,151,164,192,294]]
  | 47 =>
    [frontierNode 325 [37,68,123,192,239,294],
     frontierNode 85 [37,68,105,123,192,241,294],
     frontierNode 341 [37,68,123,175,192,294,380],
     frontierNode 329 [37,109,123,192,294,329,400],
     frontierNode 326 [68,109,123,192,208,217,294],
     frontierNode 26 [109,123,150,151,192,294]]
  | 48 =>
    [frontierNode 325 [37,68,123,192,294,406],
     frontierNode 85 [37,68,123,175,192,241,294],
     frontierNode 278 [68,109,123,175,192,294,316],
     frontierNode 278 [68,109,123,192,294,357],
     frontierNode 266 [109,123,192,294,315,316]]
  | 49 =>
    [frontierNode 85 [9,37,68,123,192,294],
     frontierNode 85 [37,68,123,192,248,274,294],
     frontierNode 89 [37,109,123,192,224,294]]
  | 50 =>
    [frontierNode 73 [37,109,123,192,216,294],
     frontierNode 281 [37,109,123,155,192,294],
     frontierNode 89 [37,109,123,192,230,268,294]]
  | 51 =>
    [frontierNode 277 [37,68,109,123,192,294,339],
     frontierNode 341 [37,68,100,123,192,294,347]]
  | 52 =>
    [frontierNode 85 [37,68,97,109,123,192,294],
     frontierNode 85 [37,68,123,169,175,192,294],
     frontierNode 281 [37,123,164,192,294,340],
     frontierNode 297 [37,109,164,192,294,347],
     frontierNode 326 [68,109,123,192,217,294,340],
     frontierNode 86 [68,109,123,192,211,217,294]]
  | 53 =>
    [frontierNode 325 [37,68,123,192,294,378],
     frontierNode 85 [37,68,123,175,192,274,294]]
  | 54 =>
    [frontierNode 277 [37,68,95,123,192,294,347],
     frontierNode 85 [37,68,109,123,169,192,294]]
  | 55 =>
    [frontierNode 85 [37,68,109,123,174,192,294]]
  | 56 =>
    [frontierNode 325 [11,37,68,109,123,192,294],
     frontierNode 281 [37,109,123,164,192,294,367],
     frontierNode 150 [68,109,123,217,248,294],
     frontierNode 282 [109,123,151,192,294,329]]
  | 57 =>
    [frontierNode 329 [37,100,109,123,192,294,329],
     frontierNode 282 [109,123,164,192,294,316]]
  | 58 =>
    [frontierNode 325 [37,68,123,192,294,378,380],
     frontierNode 85 [37,68,100,123,175,192,294],
     frontierNode 149 [37,68,109,123,241,248,294],
     frontierNode 405 [37,68,109,123,248,294,380],
     frontierNode 37 [37,68,105,175,192,294],
     frontierNode 326 [68,96,123,192,217,294]]
  | 61 =>
    [frontierNode 325 [37,68,109,123,192,233,294],
     frontierNode 133 [37,68,100,123,241,294],
     frontierNode 85 [37,68,109,123,192,274,294]]
  | 62 =>
    [frontierNode 277 [37,68,123,192,294,334],
     frontierNode 86 [68,105,123,192,217,294]]
  | 63 =>
    [frontierNode 517 [37,68,96,109,123,192,340],
     frontierNode 86 [68,123,175,192,217,294]]
  | 64 =>
    [frontierNode 101 [37,68,109,175,192,248,294],
     frontierNode 585 [37,109,123,192,329,380],
     frontierNode 89 [37,109,123,164,192,268,294],
     frontierNode 153 [37,109,123,230,248,294]]
  | 65 =>
    [frontierNode 277 [37,68,95,96,123,192,294],
     frontierNode 329 [37,109,123,192,294,400],
     frontierNode 326 [68,109,123,192,241,294,316]]
  | 66 =>
    [frontierNode 533 [37,68,109,123,192,340,347],
     frontierNode 329 [37,100,123,192,294,329],
     frontierNode 262 [68,123,192,294,328,340]]
  | 67 =>
    [frontierNode 22 [68,123,163,175,192,294]]
  | 68 =>
    [frontierNode 89 [37,105,109,123,192,230,294]]
  | 69 =>
    [frontierNode 37 [37,68,105,109,175,192,294],
     frontierNode 534 [68,109,123,192,316,347]]
  | 70 =>
    [frontierNode 581 [37,68,123,192,340,380],
     frontierNode 85 [37,68,123,192,241,274,294],
     frontierNode 329 [37,109,123,192,221,294],
     frontierNode 278 [68,109,123,192,294,316,357]]
  | 71 =>
    [frontierNode 277 [37,68,123,167,175,192,294]]
  | 72 =>
    [frontierNode 325 [37,68,109,123,192,294,332]]
  | 73 =>
    [frontierNode 329 [37,96,109,123,192,230,294],
     frontierNode 89 [37,109,123,175,192,230,294],
     frontierNode 70 [68,109,123,192,229,294],
     frontierNode 326 [68,109,123,192,217,294,390],
     frontierNode 326 [68,109,123,192,294,390]]
  | 74 =>
    [frontierNode 277 [37,68,95,109,123,192,294],
     frontierNode 277 [37,68,123,192,294,345,347],
     frontierNode 329 [37,96,123,192,230,294],
     frontierNode 518 [68,96,109,123,192,316]]
  | 75 =>
    [frontierNode 325 [37,68,96,100,123,192,294],
     frontierNode 85 [37,68,123,192,240,294]]
  | 76 =>
    [frontierNode 277 [37,68,96,123,175,192,294],
     frontierNode 277 [37,68,123,175,192,294,373],
     frontierNode 85 [37,68,97,123,192,294]]
  | 77 =>
    [frontierNode 325 [37,68,100,123,192,294,338],
     frontierNode 390 [68,109,123,217,294,380]]
  | 78 =>
    [frontierNode 281 [37,105,109,123,192,294,329],
     frontierNode 281 [37,109,123,192,294,329,367],
     frontierNode 89 [37,105,123,192,230,294],
     frontierNode 345 [37,109,123,164,192,294,380]]
  | 79 =>
    [frontierNode 389 [37,68,109,123,241,294,380],
     frontierNode 85 [37,68,109,123,192,246,294],
     frontierNode 85 [37,68,123,192,235,241,294],
     frontierNode 89 [37,109,123,164,192,241,294],
     frontierNode 89 [37,123,175,192,230,294],
     frontierNode 345 [37,109,123,192,248,294,329],
     frontierNode 278 [68,109,123,142,192,294]]
  | 80 =>
    [frontierNode 86 [68,105,109,123,192,217,294]]
  | 81 =>
    [frontierNode 85 [37,68,97,123,192,248,294],
     frontierNode 262 [68,109,123,192,294,328],
     frontierNode 326 [68,109,123,192,294,380,390]]
  | 82 =>
    [frontierNode 277 [37,68,123,192,294,339]]
  | 83 =>
    [frontierNode 325 [37,68,123,192,233,241,294],
     frontierNode 265 [37,109,123,192,294,315],
     frontierNode 281 [37,109,123,175,192,294,329],
     frontierNode 86 [68,109,123,192,217,258,294],
     frontierNode 86 [68,109,123,192,258,294]]
  | 84 =>
    [frontierNode 277 [37,68,109,123,192,294,373],
     frontierNode 89 [37,109,123,158,164,192,294],
     frontierNode 326 [68,109,123,192,294,307,316]]
  | 85 =>
    [frontierNode 85 [37,68,123,169,192,294],
     frontierNode 341 [37,68,109,123,192,294,377],
     frontierNode 393 [37,109,123,230,294,380],
     frontierNode 89 [37,123,164,192,241,294],
     frontierNode 326 [68,96,109,123,192,217,294],
     frontierNode 278 [68,123,151,192,294,340],
     frontierNode 86 [68,109,123,175,192,217,294],
     frontierNode 294 [68,109,151,192,294,347]]
  | 86 =>
    [frontierNode 85 [37,68,123,174,192,294],
     frontierNode 89 [37,109,123,192,248,268,294]]
  | 87 =>
    [frontierNode 85 [37,68,123,192,246,248,294],
     frontierNode 73 [37,109,123,192,216,241,294]]
  | 88 =>
    [frontierNode 281 [37,105,123,192,294,329],
     frontierNode 262 [68,109,123,192,294,328,340]]
  | 89 =>
    [frontierNode 325 [37,68,100,123,192,294,340],
     frontierNode 277 [37,68,109,123,192,294,345],
     frontierNode 149 [37,68,123,241,248,294],
     frontierNode 281 [37,123,175,192,294,329],
     frontierNode 22 [68,109,123,163,175,192,294]]
  | 90 =>
    [frontierNode 325 [37,68,94,123,192,294,380],
     frontierNode 522 [109,123,192,316,329]]
  | 91 =>
    [frontierNode 277 [37,68,96,123,173,192,294],
     frontierNode 341 [37,68,123,192,241,294,347],
     frontierNode 537 [37,109,123,192,329,347],
     frontierNode 345 [37,109,123,192,230,294,347]]
  | 92 =>
    [frontierNode 325 [37,68,123,192,233,294],
     frontierNode 277 [10,37,68,123,192,294,347],
     frontierNode 85 [37,68,123,192,274,294],
     frontierNode 278 [68,109,123,192,294,310],
     frontierNode 86 [68,109,123,145,151,192,294]]
  | 93 =>
    [frontierNode 73 [37,123,192,216,241,294],
     frontierNode 86 [68,100,123,151,192,294],
     frontierNode 86 [68,109,123,192,248,258,294]]
  | 94 =>
    [frontierNode 89 [37,100,109,123,164,192,294],
     frontierNode 90 [109,123,164,192,217,294]]
  | 95 =>
    [frontierNode 101 [37,68,175,192,248,294],
     frontierNode 326 [68,109,123,192,294,316,390],
     frontierNode 278 [68,109,123,192,294,347,357]]
  | 96 =>
    [frontierNode 341 [37,68,109,123,192,294,342],
     frontierNode 281 [37,109,123,192,294,367]]
  | _ => []

def frontier : Nat → Nat → List FrontierNode
  | 2, tag => frontier2 tag
  | 3, tag => frontier3 tag
  | 4, tag => frontier4 tag
  | 5, tag => frontier5 tag
  | 6, tag => frontier6 tag
  | _, _ => []

def insertSignal (a : Sig) : List Sig → List Sig
  | [] => [a]
  | b :: ws => if a.toNat ≤ b.toNat then a :: b :: ws else b :: insertSignal a ws

def sortedSignals : List Sig → List Sig
  | [] => []
  | a :: ws => insertSignal a (sortedSignals ws)

lemma insertSignal_perm (a : Sig) (ws : List Sig) : (insertSignal a ws).Perm (a :: ws) := by
  induction ws with
  | nil => exact List.Perm.refl _
  | cons b ws ih =>
    unfold insertSignal
    split
    · exact List.Perm.refl _
    · exact (ih.cons b).trans (List.Perm.swap _ _ _)

lemma sortedSignals_perm (ws : List Sig) : (sortedSignals ws).Perm ws := by
  induction ws with
  | nil => exact List.Perm.refl _
  | cons a ws ih => exact (insertSignal_perm a (sortedSignals ws)).trans (ih.cons a)

def frontierIndex (ws : List Sig) : Fin 97 :=
  Fin.ofNat 97 (ws.foldl (fun hash v => hash * 23 + v.toNat) 1)

def finishAt (room : Nat) (cs : Cuts) (ws : List Sig) : Bool :=
  !coverOK threshold5 ws || !cutsOK 9 7 cs ws ||
    (let ss := sortedSignals ws
     (frontier room (frontierIndex ss).val).any (fun x => x == (cs, ss)))

def layerOK (room : Nat) (nodes : List FrontierNode) : Bool :=
  nodes.all fun (cs,ws) =>
    match room with
    | 0 => !ws.contains threshold5
    | r+1 => checkNode threshold5 9 7 r cs ws (finishAt r)

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
lemma certifyLayer2 (i : Fin 97) : layerOK 2 (frontier 2 i.val) = true := by
  fin_cases i <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
lemma certifyLayer3 (i : Fin 97) : layerOK 3 (frontier 3 i.val) = true := by
  fin_cases i <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
lemma certifyLayer4 (i : Fin 97) : layerOK 4 (frontier 4 i.val) = true := by
  fin_cases i <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
lemma certifyLayer5 (i : Fin 97) : layerOK 5 (frontier 5 i.val) = true := by
  fin_cases i <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
lemma certifyLayer6 (i : Fin 97) : layerOK 6 (frontier 6 i.val) = true := by
  fin_cases i <;> decide +kernel

lemma certifyLayer (r : Fin 7) (i : Fin 97) : layerOK r.val (frontier r.val i.val) = true := by
  fin_cases r
  · rfl
  · rfl
  · exact certifyLayer2 i
  · exact certifyLayer3 i
  · exact certifyLayer4 i
  · exact certifyLayer5 i
  · exact certifyLayer6 i

lemma budgetPerm {T total lower room cs ws other}
    (perm : other.Perm ws) (hs : budget T total lower room cs ws) :
    budget T total lower room cs other := by
  intro c hc
  obtain ⟨f,roots,p,bank,dom,sz,hp,avail,properR,lb⟩ := hs c hc
  exact ⟨f,roots,p,bank,dom,sz,hp,fun x hx => avail x (perm.mem_iff.mp hx),properR,lb⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
lemma finishAt_sound : ∀ (room : Nat), room ≤ 6 → ∀ (cs : Cuts) (ws : List Sig), ws.Nodup →
    budget threshold5 9 7 room cs ws → finishAt room cs ws = true →
    Impossible true threshold5 room ws.toFinset := by
  intro room
  induction room with
  | zero =>
    intro _ cs ws hn hb ok
    simp only [finishAt, frontier, List.any_nil, Bool.or_false, Bool.or_eq_true] at ok
    intro k hk run
    rcases ok with miss | cut
    · simp [coverOK_run run] at miss
    · simp [cutsOK_run hb hk hn run] at cut
  | succ room ih =>
    intro hr cs ws hn hb ok
    let ss := sortedSignals ws
    have ps : ss.Perm ws := sortedSignals_perm ws
    change ((!coverOK threshold5 ws || !cutsOK 9 7 cs ws) ||
      (frontier (room+1) (frontierIndex ss).val).any (fun x => x == (cs,ss))) = true at ok
    simp only [Bool.or_eq_true] at ok
    rcases ok with (miss | cut) | hit
    · intro k hk run
      simp [coverOK_run run] at miss
    · intro k hk run
      simp [cutsOK_run hb hk hn run] at cut
    · obtain ⟨x,hx,he⟩ := List.any_eq_true.mp hit
      have eq : x = (cs,ss) := beq_iff_eq.mp he
      subst x
      have checked := certifyLayer ⟨room+1, by omega⟩ (frontierIndex ss)
      have hstep : checkNode threshold5 9 7 room cs ss (finishAt room) = true :=
        List.all_eq_true.mp checked _ hx
      rw [←List.toFinset_eq_of_perm _ _ ps]
      exact checkNode_sound (ps.nodup_iff.mpr hn) (budgetPerm ps hb) (ih (by omega)) hstep

def check5move (d : Nat) (ka kb : Bool) : Bool :=
  rejectPrefix threshold5 9 7 (finishAt 6) 2 8
    (advanceCuts initial5 (input 0) (input 1) (bin d (input 0) (input 1)))
    (childTwo (roots 5) (input 0) (input 1) d ka kb)

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
lemma reject5_and : ∀ ka kb : Bool, check5move 0 ka kb = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
lemma reject5_or : ∀ ka kb : Bool, check5move 1 ka kb = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
lemma reject5_left : ∀ ka kb : Bool, check5move 2 ka kb = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
lemma reject5_right : ∀ ka kb : Bool, check5move 3 ka kb = true := by decide +kernel

lemma reject5_moves {d : Nat} (hd : allowed true d) (ka kb : Bool) :
    check5move d ka kb = true := by
  rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
  · exact reject5_and ka kb
  · exact reject5_or ka kb
  · exact reject5_left ka kb
  · exact reject5_right ka kb

lemma reject5 : Impossible true threshold5 9 (roots 5).toFinset := by
  have nd : (roots 5).Nodup := by decide +kernel
  apply enum_step nd (by decide +kernel)
  intro a ha b hb d hd ka kb hn _ _ _ k hk run
  obtain ⟨i,rfl⟩ := input_index ha
  obtain ⟨j,rfl⟩ := input_index hb
  have hij : i ≠ j := fun h => hn (congrArg (fun q : Fin 5 => input q.val) h)
  obtain ⟨goalEq, rootsEq, ea, eb⟩ := pairRows_valid i j hij
  have onto := pairRows_onto i j
  have moved := live_rename run (firstPairRows i j) onto
  rw [goalEq, child_rename nd onto rootsEq, ea, eb] at moved
  have h0 : input 0 ∈ roots 5 := by decide +kernel
  have h1 : input 1 ∈ roots 5 := by decide +kernel
  have dnew : ∀ d : Fin 4, bin d.val (input 0) (input 1) ∉ roots 5 := by decide +kernel
  have hlt : d < 4 := by rcases hd with h | ⟨_,h⟩ <;> omega
  exact rejectPrefix_sound (depth := 2) (room := 6) (finishAt_sound 6 (le_refl 6)) _ _
    (child_nodup nd h0 h1 (by decide +kernel) (dnew ⟨d,hlt⟩))
    (budget_next initialBudget5 h0 h1 hd) (reject5_moves hd ka kb) k hk moved

lemma lower5 : Lower true (roots 5) threshold5 10 := by
  apply lower_impossible (by unfold proper; decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro a ha
    obtain ⟨i,rfl⟩ := input_index ha
    exact checkEssential_sound (threshold5EssentialTest i)
  · exact reject5

end PEqualNP.Outside.L_meta_51578.Six

namespace PEqualNP.Outside.L_meta_51578

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

def Prog : Set F → F → ℕ → Prop
  | s, f, 0 => Av s f
  | s, f, k + 1 => ∃ (t : Bool) (a b : F), Av s a ∧ Av s b ∧ Prog (insert (comb t a b) s) f k

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
  induction k generalizing s f with
  | zero => exact fun t hs => ⟨0, le_rfl, av_rs hs p, fun _ h' => smp_av h' p⟩
  | succ k ih =>
    rcases p with ⟨tag, a, b, ha, hb, tail⟩
    intro t hs
    have pa := av_rs hs ha
    have pb := av_rs hs hb
    by_cases hc : Cst (rs i c a) ∨ Cst (rs i c b)
    · obtain ⟨j, hj, q, _⟩ := ih tail t (by
        intro v hv
        rcases Set.mem_insert_iff.mp hv with rfl | hu
        · exact av_cheap tag pa pb hc
        · exact hs _ hu)
      exact ⟨j, by omega, q, fun he => by omega⟩
    · obtain ⟨j, hj, q, act⟩ := ih tail (insert (comb tag (rs i c a) (rs i c b)) t) (by
        intro v hv
        rcases Set.mem_insert_iff.mp hv with rfl | hu
        · exact av_mem (Set.mem_insert _ _)
        · exact av_ins _ (hs _ hu))
      refine ⟨j + 1, by omega, ⟨tag, rs i c a, rs i c b, pa, pb, q⟩, fun he ss => act (by omega) ?_⟩
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
  induction k generalizing s f with
  | zero => exact absurd (li_smp (li_av hs p)) (hf true)
  | succ k ih =>
    rcases p with ⟨tag, a, b, ha, hb, tail⟩
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
      obtain ⟨c, hc⟩ := ih tail (by
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
      exact ⟨j + 1, by omega, ⟨tag, rs i c a, rs i c b, av_rs ht ha, av_rs ht hb, q⟩⟩

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
  | nil => exact fun w s hw => ⟨0, le_rfl, rd_av hw o⟩
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
      refine ⟨k + 1, ?_, ⟨t, a, b, ha, hb, p⟩⟩
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

theorem all_not_not {n : ℕ} {f : F} (hl : Low n f) (gs : List Gate) (o : ℕ)
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

open PEqualNP.Outside.L_meta_51578.Six (Row observe input roots Available Reach threshold5 threshold6)

def project {m : ℕ} (pins : Fin 8 → Option (Fin m)) (v : F) : Row → Bool :=
  fun r => v (fun i => match pins i with
    | none => false
    | some j => observe (input j.val) r)

lemma projectAv {m : ℕ} (pins : Fin 8 → Option (Fin m)) {s : Set F}
    {bank : List (Row → Bool)} {v : F}
    (sub : ∀ a ∈ s, Available true bank (project pins a)) (h : Av s v) :
    Available true bank (project pins v) := by
  rcases h with ⟨b, rfl⟩ | ⟨a, ha, rfl | rfl⟩
  · exact Or.inr (Or.inl ⟨b, rfl⟩)
  · exact sub _ ha
  · exact Six.avail_inv rfl (sub a ha)

lemma projectProg {m : ℕ} (pins : Fin 8 → Option (Fin m)) {s : Set F}
    {f : F} {k n : ℕ} {bank : List (Row → Bool)}
    (p : Prog s f k) (h : Reach true ((roots m).map observe) n bank)
    (sub : ∀ a ∈ s, Available true bank (project pins a)) :
    ∃ next, Reach true ((roots m).map observe) (n + k) next ∧ Available true next (project pins f) := by
  induction k generalizing n s bank with
  | zero => exact ⟨bank, h, projectAv pins sub p⟩
  | succ k ih =>
    obtain ⟨t, a, b, ha, hb, proceed⟩ := p
    have eq : project pins (comb t a b) = Six.combine (!t) (project pins a) (project pins b) := by
      cases t <;> rfl
    have grow := Six.Reach.two (!t) h (projectAv pins sub ha) (projectAv pins sub hb)
    obtain ⟨next, hnext, hit⟩ := ih proceed grow (by
      intro v hv
      rcases Set.mem_insert_iff.mp hv with rfl | hv
      · exact Or.inl (eq ▸ List.mem_cons_self)
      · exact Six.available_cons _ (sub v hv))
    have indexEq : n + 1 + k = n + (k + 1) := by omega
    rw [indexEq] at hnext
    exact ⟨next, hnext, hit⟩

lemma stockProjection {m : ℕ} (pins : Fin 8 → Option (Fin m)) :
    ∀ a ∈ stock, Available true ((roots m).map observe) (project pins a) := by
  rintro a ⟨i, rfl⟩
  cases h : pins i with
  | none =>
    apply Or.inr
    apply Or.inl
    exact ⟨false, by funext r; simp [project, h]⟩
  | some j =>
    have eq : project pins (fun x => x i) = observe (input j.val) := by funext r; simp [project,h]
    rw [eq]
    exact Or.inl (List.mem_map_of_mem (Six.input_mem j))

lemma useCore {m l : ℕ} (pins : Fin 8 → Option (Fin m)) {code : Six.Sig} {g : F}
    (known : Six.Lower true (roots m) code l) (hg : project pins g = observe code) : Low l g := by
  intro k p
  obtain ⟨bank, run, hit⟩ := projectProg pins p Six.Reach.start (stockProjection pins)
  rw [hg] at hit
  exact known k bank (by simpa using run) hit

lemma decrease {i j : ℕ} {g : F} (small : i ≤ j) (h : Low j g) : Low i g :=
  fun k p => small.trans (h k p)

def target : F := fun x => (x 0 && x 2) || (x 1 && x 3) || (x 0 && x 4) || (x 2 && x 4) || (x 0 && x 5) || (x 2 && x 5) || (x 4 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 4 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 2 && x 7) || (x 4 && x 7) || (x 5 && x 7)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem lower : Low 14 target :=
  (one 1 false (good_at 8 0 5 (by decide +kernel)) (two 3 (good_at 64 0 5 (by decide +kernel)) (good_at 64 0 5 (by decide +kernel)) (one 6 false (good_at 1 0 5 (by decide +kernel)) (useCore (g := (rs 6 false (rs 3 false (rs 1 false target)))) (fun i => ([some 0, none, some 1, none, some 2, some 3, none, some 4] : List (Option (Fin 5))).getD i.val none) Six.lower5 (by funext r; revert r; decide +kernel))) (one 6 false (good_at 0 0 5 (by decide +kernel)) (useCore (g := (rs 6 false (rs 3 true (rs 1 false target)))) (fun i => ([some 0, none, some 1, none, some 2, some 3, none, some 4] : List (Option (Fin 5))).getD i.val none) Six.lower5 (by funext r; revert r; decide +kernel)))))

def witness : List Gate := [
  ⟨.or, [1, 6]⟩,
  ⟨.or, [0, 2]⟩,
  ⟨.or, [6, 7]⟩,
  ⟨.or, [9, 4]⟩,
  ⟨.or, [1, 11]⟩,
  ⟨.or, [11, 7]⟩,
  ⟨.and, [3, 8]⟩,
  ⟨.and, [12, 10]⟩,
  ⟨.and, [5, 13]⟩,
  ⟨.and, [9, 4]⟩,
  ⟨.and, [0, 2]⟩,
  ⟨.or, [14, 15]⟩,
  ⟨.or, [19, 16]⟩,
  ⟨.or, [20, 17]⟩,
  ⟨.or, [21, 18]⟩
]

theorem witness_ok : ∀ g ∈ witness, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  simp [witness]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem witness_eval : ∀ x : X, Circuit.eval ⟨witness, 22⟩ (List.ofFn x) = target x := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem target_eq : ∀ x : X, target x = decide (∃ i < ([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  decide +kernel

end PEqualNP.Outside.L_meta_51578

open PEqualNP.Outside.L_meta_51578 in
theorem PEqualNP.Outside.L_meta_51578 : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) := by
  intro gates o hg _ he
  by_cases hs : 15 ≤ gates.length
  · exact ⟨witness, 22, witness_ok, hs, fun x => (witness_eval x).trans (target_eq x)⟩
  · exact ⟨gates, o, all_not_not lower gates o hg (by omega)
      (fun x => (he x).trans (target_eq x).symm), le_rfl, he⟩

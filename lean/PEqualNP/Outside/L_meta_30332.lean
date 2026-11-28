import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_30332.Packed
def limbs (xs : List Nat) : Nat := xs.foldl (fun a b => Nat.shiftLeft a 64 + b) 0
end PEqualNP.Outside.L_meta_30332.Packed
open PEqualNP.Outside.L_meta_30332.Packed
namespace PEqualNP.Outside.L_meta_30332.P11311
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
lemma live_proper {u target k S} (h : Live u target k S) : ∀ a ∈ S, proper a := by
  induction h using Live.ind with
  | stop hp => simpa using hp
  | binary hd ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩
lemma live_size {u target k S} (h : Live u target k S) : S.card ≤ k+1 := by
  induction h using Live.ind with
  | stop hp => simp
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    omega
def bit (i : Fin 512) (a : Sig) : Bool := a.getLsbD i.val
lemma bit_zero (i) : bit i zero = false := by simp [bit,zero]
lemma bit_one (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
lemma bit_neg (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
lemma bit_bin (i d) (a b : Sig) : bit i (bin d a b) =
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
lemma bin_laws (a : Sig) :
    bin 0 a one = a ∧ bin 1 a zero = a ∧
    bin 0 a zero = zero ∧ bin 1 a one = one ∧
    bin 0 a a = a ∧ bin 1 a a = a ∧ bin 2 a a = zero ∧ bin 3 a a = zero ∧ bin 2 a zero = a ∧
    bin 3 zero a = a ∧ bin 2 zero a = zero ∧ bin 3 a zero = zero ∧ bin 0 zero a = zero ∧ bin 1 zero a = a ∧
    bin 0 one a = a ∧ bin 1 one a = one := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> apply bit_ext <;> intro i <;>
    simp [bit_bin,bit_zero,bit_one]
lemma neg_laws : neg zero = one ∧ neg one = zero := by simp [neg,zero,one]
lemma operand_cases {w : List Sig} {a : Sig} (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)
def witness (u : Bool) (w : List Sig) (z : Sig) : Prop :=
  ∃ d a b, allowed u d ∧ a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b
lemma bin_rep {u w a b} (d : Nat) (hd : allowed u d) (ha : represented w a) (hb : represented w b)
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
lemma gate_rep (u : Bool) (w : List Sig) (g : Gate)
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
lemma pull_gate {u target} {w : List Sig} {z : Sig} {k S c} (h : Live u target k S)
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
lemma run_bit (i) (g : Gate) (w : List Sig)
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
def inputs : List Sig := [(OfNat.ofNat (limbs [0xaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaa])),(OfNat.ofNat (limbs [0xcccccccccccccccc,0xcccccccccccccccc,0xcccccccccccccccc,0xcccccccccccccccc,0xcccccccccccccccc,0xcccccccccccccccc,0xcccccccccccccccc,0xcccccccccccccccc])),(OfNat.ofNat (limbs [0xf0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0])),(OfNat.ofNat (limbs [0xff00ff00ff00ff00,0xff00ff00ff00ff00,0xff00ff00ff00ff00,0xff00ff00ff00ff00,0xff00ff00ff00ff00,0xff00ff00ff00ff00,0xff00ff00ff00ff00,0xff00ff00ff00ff00])),(OfNat.ofNat (limbs [0xffff0000ffff0000,0xffff0000ffff0000,0xffff0000ffff0000,0xffff0000ffff0000,0xffff0000ffff0000,0xffff0000ffff0000,0xffff0000ffff0000,0xffff0000ffff0000])),(OfNat.ofNat (limbs [0xffffffff00000000,0xffffffff00000000,0xffffffff00000000,0xffffffff00000000,0xffffffff00000000,0xffffffff00000000,0xffffffff00000000,0xffffffff00000000])),(OfNat.ofNat (limbs [0xffffffffffffffff,0x0,0xffffffffffffffff,0x0,0xffffffffffffffff,0x0,0xffffffffffffffff,0x0])),(OfNat.ofNat (limbs [0xffffffffffffffff,0xffffffffffffffff,0x0,0x0,0xffffffffffffffff,0xffffffffffffffff,0x0,0x0])),(OfNat.ofNat (limbs [0xffffffffffffffff,0xffffffffffffffff,0xffffffffffffffff,0xffffffffffffffff,0x0,0x0,0x0,0x0]))]
def graph : Sig := (OfNat.ofNat (limbs [0xfffffffffffefffe,0xfffefffceeeeaa00,0xfffffffffffefffe,0xfffefffceeeeaa00,0xfffffffffffefffe,0xfffefffceeeeaa00,0xfffffffffffefffe,0xfffefffceeeeaa00]))
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
 (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 1 &&& x 5) ||| (x 2 &&& x 5) ||| (x 3 &&& x 5) ||| (x 0 &&& x 6) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 5 &&& x 6)
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
  | 0 => (OfNat.ofNat (limbs [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]))
  | 1 => (OfNat.ofNat (limbs [0x1,0x0,0x1,0x0,0x1,0x0,0x1]))
  | 2 => (OfNat.ofNat (limbs [0x1,0x1,0x0,0x0,0x1,0x1]))
  | 3 => (OfNat.ofNat (limbs [0x1,0x0,0x0,0x0,0x1]))
  | 4 => (OfNat.ofNat (limbs [0x1,0x1,0x1,0x1]))
  | 5 => (OfNat.ofNat (limbs [0x1,0x0,0x1]))
  | 6 => (OfNat.ofNat (limbs [0x1,0x1]))
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
def graphPairs (m hints : Nat) : List (Sig × Row × Row) :=
  (selected m).map fun (i,a) =>
    let r := 1 <<< ((hints >>> (4*i)) &&& 15)
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))
def properB (T : Sig) := T != zero && T != one
theorem proper_of (T : Sig) (h : properB T = true) : proper T := by
  simpa only [properB,proper,Bool.and_eq_true,bne_iff_ne] using h
abbrev ColumnInfo := Nat × Nat × Nat × Nat × Nat
def colFree (m z o : Nat) := m ^^^ (m &&& (z ||| o))
def rawMask (m : Nat) (c : ColumnInfo) : Nat := m % 512+512*(c.1/512)
def carryOK (old rep : Nat) (swaps : List Nat) :=
  (properB (graphGoal old) && plainWord (graphGoal old) && (varsX old).all plainWord) && properB (graphGoal rep) &&
    checkMap (swaps.map swapRows) (varsX old) (graphGoal old) (varsX rep) (graphGoal rep)
theorem carry_of {u old rep L swaps} (ok : carryOK old rep swaps = true)
    (h : Lower u (varsX rep) (graphGoal rep) L) : Lower u (varsX old) (graphGoal old) L := by
  simp only [carryOK,Bool.and_eq_true] at ok
  exact lower_map ok.2 (proper_of _ ok.1.1.1.1) ok.1.1.1.2 ok.1.1.2 (proper_of _ ok.1.2) h
def boundsBefore (entries : List (Nat × Nat)) (q : Nat) :=
  ((entries.find? (fun a => a.1 == q)).map Prod.snd).getD 0
def essOK (m hints : Nat) : Bool :=
  let xs := graphPairs m hints
  properB (graphGoal m) && checkEssential (graphGoal m) (vars m) xs && (xs.map Prod.fst == vars m)
theorem plain_low {u} {m hints cap : Nat} (ok : essOK m hints = true)
    (a : Impossible u (graphGoal m) cap (vars m).toFinset) : Lower u (vars m) (graphGoal m) (cap+1) := by
  simp only [essOK,Bool.and_eq_true,beq_iff_eq] at ok
  apply lower_impossible (proper_of _ ok.1.1) (essential_plain ok.1.2).1 (essential_plain ok.1.2).2 _ a
  intro v hv
  apply essential_ok ok.1.2 v
  rw [ok.2]
  exact List.mem_toFinset.mpr hv
def target (x : Fin 7 → Bool) : Bool := decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)
def paidSliceChoices (d : Sig) (pool : List Sig) : List Choice → List Choice
  | [] => []
  | c :: hist =>
    if availableB true d pool (choiceVal c) then paidSliceChoices d pool hist
    else c :: paidSliceChoices d (choiceVal c :: pool) hist
def zeroSliceOK (m s : Nat) : Bool :=
  let fixed := m - s
  let moves := fixRows fixed 0
  properB (graphGoal s) && (movedWord moves (subcube fixed 0) == one &&
    checkMap moves (vars m) (graphGoal m) (vars s) (graphGoal s))
theorem zeroSlice_sound {m s l} (ok : zeroSliceOK m s = true)
    (prior : Lower true (vars s) (graphGoal s) l) :
    Slice true (vars m) (graphGoal m) (subcube (m - s) 0) l := by
  simp only [zeroSliceOK, Bool.and_eq_true, beq_iff_eq] at ok
  exact slice_correct ok.2.2 ok.2.1 (proper_of _ ok.1) prior
def mixedPairs (support hints : Nat) : List (Sig × Row × Row) :=
  (selected support).map fun (i, w) =>
    let j := (hints >>> (4 * i)) &&& 15
    let r : Nat := if j < 9 then 1 <<< j else 0
    (w, Fin.ofNat 512 r, Fin.ofNat 512 (r ||| (1 <<< i)))
def mixedColumnOK (m z o q support hints L base : Nat) : Bool :=
  let ms := fixRows z o
  let free := colFree m z o
  let G := movedWord ms (graphGoal m)
  let xs := mixedPairs support hints
  let count := (xs.map Prod.fst).toFinset.card
  properB G && checkMap ms (vars m) (graphGoal m) (vars free) G &&
    (movedWord ms (subcube z o) == one) &&
    (if q = 0 then checkEssential G (vars free) xs && decide (L ≤ count - 1)
     else properB (graphGoal q) &&
       checkLift (fixRows (colFree free q 0) 0) G (vars free) (vars q) (graphGoal q) xs &&
       decide (L ≤ base + count))
theorem mixedColumn_sound {m z o q support hints L base : Nat}
    (prior : Lower true (vars q) (graphGoal q) base)
    (ok : mixedColumnOK m z o q support hints L base = true) :
    Slice true (vars m) (graphGoal m) (subcube z o) L := by
  let ms := fixRows z o
  let free := colFree m z o
  let G := movedWord ms (graphGoal m)
  let xs := mixedPairs support hints
  change (((properB G && checkMap ms (vars m) (graphGoal m) (vars free) G) &&
    (movedWord ms (subcube z o) == one)) && _) = true at ok
  simp only [Bool.and_eq_true, beq_iff_eq] at ok
  apply slice_correct ok.1.1.2 ok.1.2 (proper_of _ ok.1.1.1)
  intro p bank hr ha
  have h := ok.2
  by_cases hq : q = 0
  · simp only [hq, if_true, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.2.trans (lower_count (proper_of _ ok.1.1.1) xs h.1 p bank hr ha)
  · simp only [hq, if_false, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.2.trans (lift_ok h.1.2 (proper_of _ ok.1.1.1) (proper_of _ h.1.1) prior p bank hr ha)
theorem mixedBaseZero : Lower true (vars 0) (graphGoal 0) 0 :=
  fun _ _ _ _ => Nat.zero_le _
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
abbrev Bits := BitVec 1024
abbrev Signals := Bits × Bits
abbrev Decor := Sig × Signals
def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def pairSig (r s : Fin 1024 → Row) (a : Sig) : Signals := (ofRows r a,ofRows s a)
def properPairs (T : Sig) (r s : Fin 1024 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 1024 r s (pairSig r s) := by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩
def faithful (r s : Fin 1024 → Row) (x : Decor) := x.2 = pairSig r s x.1
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
def asRow (cols : Nat → Bits) (i : Fin 1024) : Row :=
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
theorem asRow_bit (cols : Nat → Bits) (i : Fin 1024) (j : Fin 9) :
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
 (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 1 &&& x 5) ||| (x 2 &&& x 5) ||| (x 3 &&& x 5) ||| (x 0 &&& x 6) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 5 &&& x 6)
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 1024) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then v j.val else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · simpa [vertex,hh] using asRow_bit v i j
  · simp [vertex,hh,bit_zero]
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 1024) :
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
theorem cov_one (c : Cov) (a : Bits) : takeOne (addCov a c) a=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeOne,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases c.1.getLsbD i <;> cases c.2.1.getLsbD i <;> rfl
theorem cov_two (c : Cov) (a b : Bits) : takeTwo (addCov a (addCov b c)) a b=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeTwo,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
    cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl
theorem add_swap (c : Cov) (a b : Bits) : addCov a (addCov b c)=addCov b (addCov a c) := by
  apply Prod.ext
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [addCov,BitVec.getLsbD_or]
    cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
  · apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
      simp only [addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and] <;>
      cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
      cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl
theorem cov_perm (d : Bool) {l r : List Decor} (h : l.Perm r) : coverage d l=coverage d r := by
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
def opsOf (u : Bool) : List Nat := if u then [0,1,2,3] else [0,1]
theorem opsOf_mem {u d} (h : allowed u d) : d ∈ opsOf u := by
  rcases allowed_four h with rfl | rfl | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · cases u <;> simp [opsOf]
  · cases u <;> simp [opsOf]
  · simp [opsOf]
  · simp [opsOf]
theorem keep_mem {v : List Sig} {w : Sig} (a : Sig) (k : Bool) :
    w ∈ kept k a v ↔ (w=a ∧ k=true) ∨ w∈v := by cases k <;> simp [kept]
theorem childTwo_swap {u} (v : List Sig) (nd : v.Nodup) (a b : Sig) (d : Nat) (hd : allowed u d) (ka kb : Bool) :
    (childTwo v a b d ka kb).toFinset = (childTwo v b a (flipOp d) kb ka).toFinset := by
  ext x
  simp only [childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,bin_flip hd a b]
  tauto
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
def compactNext (path : Nat) (ws : List Decor) (hist : List Choice) :
    List Decor × List Choice :=
  let a := ws.getD (path &&& 31) defaultDecor
  let b := ws.getD ((path >>> 5) &&& 31) defaultDecor
  let d := (path >>> 10) &&& 3
  (ws ++ [dbin d a b], hist ++ [(d, a.1, b.1)])
def walkCompact : Nat → Nat → List Decor → List Choice → List Decor × List Choice
  | 0, _, ws, hist => (ws, hist)
  | depth + 1, path, ws, hist =>
    let next := compactNext path ws hist
    walkCompact depth (path >>> 12) next.1 next.2
theorem walkCompact_faithful (depth path : Nat) (ws : List Decor) (hist : List Choice)
    {r s} (base : ∀ v ∈ ws, faithful r s v) :
    ∀ v ∈ (walkCompact depth path ws hist).1, faithful r s v := by
  induction depth generalizing path ws hist with
  | zero => exact base
  | succ depth ih =>
    apply ih
    intro v hv
    rcases List.mem_append.mp hv with hb | hz
    · exact base _ hb
    · obtain rfl := List.mem_singleton.mp hz
      exact faithful_bin _ (faithful_get base _) (faithful_get base _)
def rowWires : List Decor → Nat → List Decor
  | [], _ => []
  | v :: bank, mask =>
    if mask.testBit 0 then v :: rowWires bank (mask >>> 1)
    else rowWires bank (mask >>> 1)
theorem rowWires_faithful (bank : List Decor) (mask : Nat) {r s}
    (base : ∀ v ∈ bank, faithful r s v) :
    ∀ v ∈ rowWires bank mask, faithful r s v := by
  induction bank generalizing mask with
  | nil => simp [rowWires]
  | cons v bank ih =>
    have hv := List.forall_mem_cons.mp base
    unfold rowWires
    split
    · exact List.forall_mem_cons.mpr ⟨hv.1, ih _ hv.2⟩
    · exact ih _ hv.2
def compactPool (m : Nat) (domain : Sig × Nat) (hist : List Choice) : Option BoundPool :=
  materialize true (vars m) (paidSliceChoices domain.1 (vars m) hist) domain.1 domain.2
theorem compactPool_sound {m : Nat} {domain : Sig × Nat} {hist : List Choice} {pool : BoundPool}
    (slice : Slice true (vars m) (graphGoal m) domain.1 domain.2)
    (ok : compactPool m domain hist = some pool) :
    ValidPool true (vars m) (graphGoal m) pool :=
  materialize_sound slice ok
abbrev CompactGrid := Nat × Nat × (Nat → Bits) × (Nat → Bits)
def CompactGrid.mask (g : CompactGrid) := g.1
def CompactGrid.top (g : CompactGrid) := g.2.1
def CompactGrid.pos (g : CompactGrid) := g.2.2.1
def CompactGrid.neg (g : CompactGrid) := g.2.2.2
abbrev CompactTable := (Nat → Nat) × (Nat → Nat → Nat) × (Nat → Nat → Nat) ×
  (Nat → Nat → List Nat) × (Nat → Nat → List Nat)
def CompactTable.count (t : CompactTable) := t.1
def CompactTable.path (t : CompactTable) := t.2.1
def CompactTable.live (t : CompactTable) := t.2.2.1
def CompactTable.picks (t : CompactTable) := t.2.2.2.1
def CompactTable.bucket (t : CompactTable) := t.2.2.2.2
def chartAt (g : CompactGrid) (t : CompactTable) (k i : Nat) :=
  let bank := walkCompact (g.top-k) (t.path k i) (rawDecor g.mask g.pos g.neg) []
  (rowWires bank.1 (t.live k i), bank.2)
def wordsAt (g : CompactGrid) (t : CompactTable) (k i : Nat) :=
  (chartAt g t k i).1.map Prod.fst
abbrev Domains := Array (Sig × Nat)
abbrev Perms := Array (List Nat)
def selectedHistory : List Choice → Nat → List Choice
  | [], _ => []
  | a :: rest, mask =>
    if mask.testBit 0 then a :: selectedHistory rest (mask >>> 1)
    else selectedHistory rest (mask >>> 1)
def poolList (m : Nat) (dom : Domains) (h : List Choice) (picks : List Nat) :=
  picks.filterMap (fun j => dom[j % dom.size]?.bind (fun d => compactPool m d (selectedHistory h (j / dom.size))))
theorem poolList_valid {m dom h picks} (valid : ∀ d ∈ dom, Slice true (vars m) (graphGoal m) d.1 d.2) :
    ∀ pool ∈ poolList m dom h picks, ValidPool true (vars m) (graphGoal m) pool := by
  intro pool hp
  obtain ⟨j,_,hj⟩ := List.mem_filterMap.mp hp
  cases e : dom[j % dom.size]? with
  | none => simp [e] at hj
  | some d =>
    simp only [e,Option.bind_some] at hj
    exact compactPool_sound (valid d (Array.mem_of_getElem? e)) hj
def applySwaps : List Nat → List Sig → List Sig
  | [], xs => xs
  | p::ps,xs => xs.map (movedWord ((p::ps).map swapRows))
theorem applySwaps_valid {T k xs} {p : List Nat}
    (ok : autoOK T (p.map swapRows).reverse = true)
    (ih : Impossible true T k (List.toFinset xs)) :
    Impossible true T k (applySwaps p xs).toFinset := by
  cases p with
  | nil => exact ih
  | cons a p =>
    have := rotate_excluded ih (((a::p).map swapRows).reverse) ok
    simpa only [List.reverse_reverse,applySwaps] using this
def linkedCandidates (g : CompactGrid) (t : CompactTable) (perms : Perms) (k tag : Nat) :=
  (t.bucket k tag).filterMap (fun code =>
    let name := code / perms.size
    if name < t.count k then
      perms[code % perms.size]?.map (fun swaps => applySwaps swaps (wordsAt g t k name))
    else none)
theorem linkedCandidates_valid {g t perms k}
    (autos : ∀ p ∈ perms, autoOK (graphGoal g.mask) (p.map swapRows).reverse = true)
    (prev : ∀ i < t.count k, Impossible true (graphGoal g.mask) k (wordsAt g t k i).toFinset) :
    ∀ tag xs, xs ∈ linkedCandidates g t perms k tag → Impossible true (graphGoal g.mask) k xs.toFinset := by
  intro tag xs hx
  obtain ⟨code,_,he⟩ := List.mem_filterMap.mp hx
  dsimp only at he
  split at he
  next small =>
    cases eq : perms[code % perms.size]? with
    | none => simp [eq] at he
    | some p =>
      simp only [eq,Option.map_some,Option.some.injEq] at he
      subst xs
      exact applySwaps_valid (autos p (Array.mem_of_getElem? eq)) (prev _ small)
  next => contradiction
theorem cachedLiveSize {u target k S} (h : Live u target k S) : S.card ≤ k+1 := by
  induction h using Live.ind with
  | stop hp => simp
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    omega
abbrev NodePool := BoundPool × List Sig × List Sig × Nat
def cacheOnePool (u : Bool) (front : List Sig) (p : BoundPool) : NodePool :=
  (p, front.filter (fun a => !(availableB u p.domain p.wires a)),
    p.wires.map (masked p.domain), front.countP (isMaskedConstant p.domain))
def maskedAvailable (u : Bool) (d : Sig) (pool : List Sig) (a : Sig) : Bool :=
  let m := masked d a
  m == zero || m == d || pool.any (fun v => v==m) ||
    (u && (let c := masked d (neg a); pool.any (fun v => v==c)))
def cachedPoolCut (u : Bool) (a : NodePool) (k : Nat) (rest : List Sig) (op : Choice) : Bool :=
  let (c,missing,bank,maxCon) := a
  if c.bound + maxCon + 1 ≤ k + c.paid then false else
  let z := choiceVal op
  let con := c.bound + (z::rest).countP (isMaskedConstant c.domain)
  if con ≤ k+c.paid then false else
  let extra := !(maskedAvailable u c.domain bank z)
  (decide (k+c.paid+extra.toNat < con) &&
   missing.all (fun w => !(rest.contains w))) &&
    (!extra || (allowedB u op.1 && (!missing.contains op.2.1 && !missing.contains op.2.2)))
theorem cachedCut_ok {u p k rest op front}
    (sub : ∀ w ∈ rest, w ∈ front) (ha : op.2.1 ∈ front) (hb : op.2.2 ∈ front)
    (ok : cachedPoolCut u (cacheOnePool u front p) k rest op = true) :
    scalarPoolCut u p k rest op = true := by
  let miss := front.filter (fun a => !(availableB u p.domain p.wires a))
  let extra := !(availableB u p.domain p.wires (choiceVal op))
  have know (w) (hm : w ∈ front) (hn : w ∉ miss) : availableB u p.domain p.wires w = true := by
    by_contra h
    apply hn
    apply List.mem_filter.mpr
    exact ⟨hm, by simpa using h⟩
  dsimp only [cachedPoolCut, cacheOnePool] at ok
  split at ok
  · contradiction
  split at ok
  · contradiction
  change ((_ && miss.all (fun w => !(rest.contains w))) &&
    (!extra || (allowedB u op.1 && (!miss.contains op.2.1 && !miss.contains op.2.2)))) = true at ok
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', List.all_eq_true] at ok
  change ((_ && rest.all (availableB u p.domain p.wires)) && (!extra || choiceOK u p.domain p.wires op)) = true
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', List.all_eq_true]
  refine ⟨⟨ok.1.1, ?_⟩, ?_⟩
  · intro w hw
    apply know w (sub w hw)
    intro no
    have contra := ok.1.2 w no
    simpa [hw] using contra
  · rcases ok.2 with h | ⟨allowed, ah, bh⟩
    · exact Or.inl h
    · right
      simp only [choiceOK, Bool.and_eq_true]
      exact ⟨allowed, know _ ha (by simpa using ah), know _ hb (by simpa using bh)⟩
def cachedClose (u : Bool) (pools : List NodePool) (links : Nat → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) : Bool :=
  pools.any (fun p => cachedPoolCut u p k rest op) ||
    (let ws := choiceVal op::rest; (links (keySet ws)).any (sameWords ws))
theorem cachedClose_sound {u raw T} {pools : List BoundPool} {links k rest op front}
    (pValid : ∀ p ∈ pools, ValidPool u raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → Impossible u T k (List.toFinset xs))
    (nd : (choiceVal op::rest).Nodup)
    (sub : ∀ w ∈ rest, w ∈ front) (ha : op.2.1 ∈ front) (hb : op.2.2 ∈ front)
    (ok : cachedClose u (pools.map (cacheOnePool u front)) links k rest op = true) :
    Impossible u T k (choiceVal op::rest).toFinset := by
  simp only [cachedClose,Bool.or_eq_true,List.any_eq_true] at ok
  rcases ok with ⟨c,hc,cut⟩ | ⟨w,hw,eq⟩
  · obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hc
    exact scalarPoolCut_sound (pValid p hp) nd (cachedCut_ok sub ha hb cut)
  · rw [sameWords_sound eq]
    exact lValid _ _ hw
abbrev cached_NodeContext := Nat × Nat × List Decor × CovPair × List NodePool × (Nat → List (List Sig))
def cached_evalMove (c : cached_NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
  let (cap,n,ws,cov,pools,links) := c
  let len := 1+(n - (if ka then 0 else 1) - (if kb then 0 else 1))
  if len>cap then true else
    let d := !cov.2
    let rs := restCov cov.1 (column d a.2) (column d b.2) ka kb
    if (rs ||| column d z.2) != BitVec.allOnes 1024 then true else
    if !properB z.1 || ws.any (fun v => v.1==z.1) then true else
      let rest := (delTwo ws a b ka kb).map Prod.fst
      cachedClose cov.2 pools links (cap-1) rest (movedChoice op a b)
def cached_moveFront (ws : List Decor) (op : Nat) (a b : Decor) (ka kb : Bool) :=
  (dbin op a b).1 :: (delTwo ws a b ka kb).map Prod.fst
theorem cached_evalMove_sound {u raw T r s ws} {pools : List BoundPool} {links cap a b op ka kb}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a≠b) (hcap : 0<cap)
    (pv : ∀ p ∈ pools, ValidPool u raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible u T (cap-1) (List.toFinset xs))
    (pro : proper (dbin op a b).1) (fresh : (dbin op a b).1 ∉ ws.map Prod.fst)
    (test : cached_evalMove (cap,ws.length,ws,preCov u ws,pools.map (cacheOnePool u (ws.map Prod.fst)),links) op a b (dbin op a b) ka kb = true) :
    Impossible u T (cap-1) (cached_moveFront ws op a b ka kb).toFinset := by
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
  have hsz := cachedLiveSize h
  change child.toFinset.card ≤ k+1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have len : child.length ≤ cap := by omega
  unfold cached_evalMove at test
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
  have be : ((restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 1024) = false := by
    simpa using sep
  change (if (restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 1024 then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
  rw [be,pp,fr] at test
  exact cachedClose_sound (op:=movedChoice op a b) (rest:=rest.map Prod.fst) pv lv ndc (sub.map _).subset (List.mem_map_of_mem ha) (List.mem_map_of_mem hb) test k hk h
def cached_testPair (ctx : cached_NodeContext) (a b : Decor) (op : Nat) :=
  let z := dbin op a b
  let attempt := cached_evalMove ctx op a b z
  attempt false false && attempt true false && attempt false true && attempt true true
def cached_opsOf (u : Bool) : List Nat := if u then [0,1,2,3] else [0,1]
theorem cached_opsOf_mem {u d} (h : allowed u d) : d ∈ cached_opsOf u := by
  rcases allowed_four h with rfl | rfl | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · cases u <;> simp [cached_opsOf]
  · cases u <;> simp [cached_opsOf]
  · simp [cached_opsOf]
  · simp [cached_opsOf]
def cached_testRow (ctx : cached_NodeContext) (a : Decor) (bs : List Decor) :=
    bs.all (fun b => (cached_opsOf ctx.2.2.2.1.2).all (cached_testPair ctx a b))
def cached_testAll (ctx : cached_NodeContext) : List Decor → Bool
  | [] => true
  | a::bs => cached_testRow ctx a bs && cached_testAll ctx bs
theorem cached_all_binary {ctx ws} (h : cached_testAll ctx ws=true) {a b : Decor} (ha : a∈ws) (hb : b∈ws)
    (ne : a≠b) : (∀ d, allowed ctx.2.2.2.1.2 d → cached_testPair ctx a b d=true) ∨
      (∀ d, allowed ctx.2.2.2.1.2 d → cached_testPair ctx b a d=true) := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [cached_testAll,Bool.and_eq_true,cached_testRow,List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | haTail
    · have bm := (List.mem_cons.mp hb).resolve_left (Ne.symm ne)
      exact Or.inl fun d hd => h.1 b bm d (cached_opsOf_mem hd)
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · exact Or.inr fun d hd => h.1 a haTail d (cached_opsOf_mem hd)
      · exact ih h.2 haTail hbTail
theorem cached_testPair_at {ctx a b d} (h : cached_testPair ctx a b d = true) (ka kb : Bool) :
    cached_evalMove ctx d a b (dbin d a b) ka kb = true := by
  simp only [cached_testPair,Bool.and_eq_true] at h
  cases ka <;> cases kb <;> first | exact h.1.1.1 | exact h.1.2 | exact h.1.1.2 | exact h.2
theorem cached_keep_mem {v : List Sig} {w : Sig} (a : Sig) (k : Bool) :
    w ∈ kept k a v ↔ (w=a ∧ k=true) ∨ w∈v := by cases k <;> simp [kept]
theorem cached_mem_delone {v : List Decor} (nd : v.Nodup) (a w : Decor) (k : Bool) :
    w ∈ delOne v a k ↔ w∈v ∧ (w≠a ∨ k=true) := by
  cases k <;> simp [delOne,nd.mem_erase_iff,and_comm]
theorem cached_unique_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
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
theorem cached_kept_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a ∈ ws) (hb : b ∈ ws) (ka kb : Bool) (v : Sig) :
    v ∈ (delTwo ws a b ka kb).map Prod.fst ↔
    v ∈ ws.map Prod.fst ∧ (v≠a.1 ∨ ka=true) ∧ (v≠b.1 ∨ kb=true) := by
  have wn := nd.of_map
  have dn := wn.sublist (delOne_sub ws a ka)
  simp only [delTwo,List.mem_map,cached_mem_delone wn,cached_mem_delone dn]
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact ⟨⟨_,hw.1.1,rfl⟩,hw.1.2.imp (fun ne eq => ne (cached_unique_value nd hw.1.1 ha eq)) id,
          hw.2.imp (fun ne eq => ne (cached_unique_value nd hw.1.1 hb eq)) id⟩
  · rintro ⟨⟨w,hm,rfl⟩,h1,h2⟩
    exact ⟨w,⟨⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,
        h2.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩
theorem cached_binary_front {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (ne : a.1≠b.1) (d : Nat) (ka kb : Bool) :
    (cached_moveFront ws d a b ka kb).toFinset =
      (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
  ext v
  have av := List.mem_map_of_mem (f:=Prod.fst) ha
  have bv' := List.mem_map_of_mem (f:=Prod.fst) hb
  simp only [cached_moveFront,childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    cached_kept_value nd ha hb,cached_keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,dbin]
  by_cases va : v=a.1 <;> by_cases vb : v=b.1 <;> cases ka <;> cases kb <;> simp_all
theorem cached_childTwo_swap {u} (v : List Sig) (nd : v.Nodup) (a b : Sig) (d : Nat) (hd : allowed u d) (ka kb : Bool) :
    (childTwo v a b d ka kb).toFinset = (childTwo v b a (flipOp d) kb ka).toFinset := by
  ext x
  simp only [childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    cached_keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,bin_flip hd a b]
  tauto
theorem cached_node_sound {u raw T r s ws} {pools : List BoundPool} {links cap}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools, ValidPool u raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible u T (cap-1) (List.toFinset xs))
    (checks : cached_testAll (cap,ws.length,ws,preCov u ws,pools.map (cacheOnePool u (ws.map Prod.fst)),links) ws = true) :
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
      (test : cached_testPair (cap,ws.length,ws,preCov u ws,pools.map (cacheOnePool u (ws.map Prod.fst)),links) a b d = true) :
      Impossible u T (cap-1) (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
    rw [←cached_binary_front nd aa bb ne']
    exact cached_evalMove_sound pairs faith nd aa bb (fun e => ne' (congrArg Prod.fst e)) hc' pv lv
      pr fr (cached_testPair_at test ka kb)
  rcases cached_all_binary checks haW hbW ab with hh | hh
  · exact one a b d haW hbW ne ka kb pro fresh (hh d hd)
  · rw [cached_childTwo_swap _ nd _ _ d hd]
    exact one b a (flipOp d) hbW haW (Ne.symm ne) kb ka (bin_flip hd a.1 b.1 ▸ pro)
      (bin_flip hd a.1 b.1 ▸ fresh) (hh _ (flip_flip hd).1)
def compactNode (g : CompactGrid) (t : CompactTable) (dom : Domains) (perms : Perms) (k i : Nat) : Bool :=
  let state := chartAt g t k i
  let ws := state.1
  let words := ws.map Prod.fst
  let pools := poolList g.mask dom state.2 (t.picks k i)
  let links := linkedCandidates g t perms (k-1)
  decide words.Nodup && (!(words.contains (graphGoal g.mask)) &&
    (if k=0 then true else cached_testAll (k,ws.length,ws,preCov true ws,pools.map (cacheOnePool true words),links) ws))
theorem compactNode_sound {g t dom perms k i}
    (pairs : properPairs (graphGoal g.mask) (asRow g.pos) (asRow g.neg))
    (valid : ∀ d ∈ dom, Slice true (vars g.mask) (graphGoal g.mask) d.1 d.2)
    (autos : ∀ p ∈ perms, autoOK (graphGoal g.mask) (p.map swapRows).reverse = true)
    (prev : 0 < k → ∀ j < t.count (k-1),
      Impossible true (graphGoal g.mask) (k-1) (wordsAt g t (k-1) j).toFinset)
    (check : compactNode g t dom perms k i = true) :
    Impossible true (graphGoal g.mask) k (wordsAt g t k i).toFinset := by
  simp only [compactNode,Bool.and_eq_true,decide_eq_true_eq] at check
  have out : graphGoal g.mask ∉ wordsAt g t k i := by simpa [wordsAt] using check.2.1
  by_cases hz : k=0
  · subst k
    intro n hn run
    obtain rfl : n = 0 := by omega
    exact out (List.mem_toFinset.mp (run.1.symm ▸ Finset.mem_singleton_self _))
  · have f : ∀ v ∈ (chartAt g t k i).1, faithful (asRow g.pos) (asRow g.neg) v :=
      rowWires_faithful _ (t.live k i) (walkCompact_faithful (g.top-k) (t.path k i)
        (rawDecor g.mask g.pos g.neg) [] (raw_faithful g.mask g.pos g.neg))
    apply cached_node_sound pairs f check.1 out (poolList_valid valid) (linkedCandidates_valid autos (prev (by omega)))
    simpa only [hz,ite_false] using check.2.2
def chartBlock (test : Nat → Bool) (start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => test (start+n) && chartBlock test start n
theorem chartBlock_at {test start n} (ok : chartBlock test start n = true) (i)
    (a : start ≤ i) (b : i < start+n) : test i = true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [chartBlock,Bool.and_eq_true] at ok
    by_cases h : i=start+n
    · simpa only [h] using ok.1
    · exact ih ok.2 (by omega)
theorem chartBlock_join {test start a b}
    (left : chartBlock test start a = true) (right : chartBlock test (start+a) b = true) :
    chartBlock test start (a+b) = true := by
  induction b with
  | zero => simpa using left
  | succ b ih =>
    simp only [chartBlock,Bool.and_eq_true] at right
    simp only [Nat.add_succ,chartBlock,Bool.and_eq_true]
    constructor
    · change test (start + (a+b)) = true
      rw [← Nat.add_assoc]
      exact right.1
    · exact ih right.2
theorem compactAll {g t dom perms}
    (pairs : properPairs (graphGoal g.mask) (asRow g.pos) (asRow g.neg))
    (valid : ∀ d ∈ dom, Slice true (vars g.mask) (graphGoal g.mask) d.1 d.2)
    (autos : ∀ p ∈ perms, autoOK (graphGoal g.mask) (p.map swapRows).reverse = true)
    (blocks : ∀ k ≤ g.top, chartBlock (compactNode g t dom perms k) 0 (t.count k) = true) :
    ∀ k ≤ g.top, ∀ i < t.count k, Impossible true (graphGoal g.mask) k (wordsAt g t k i).toFinset := by
  intro k
  induction k with
  | zero =>
    intro h i hi
    exact compactNode_sound pairs valid autos (by omega) (chartBlock_at (blocks 0 h) i (by omega) (by simpa using hi))
  | succ k ih =>
    intro h i hi
    exact compactNode_sound pairs valid autos (fun _ => ih (by omega)) (chartBlock_at (blocks _ h) i (by omega) (by simpa using hi))
theorem compactPairs {g : CompactGrid}
    (yes : liftGoal g.mask g.pos = BitVec.allOnes 1024) (no : liftGoal g.mask g.neg = 0) :
    properPairs (graphGoal g.mask) (asRow g.pos) (asRow g.neg) := by
  intro i
  constructor
  · rw [bit_liftGoal,yes,BitVec.getLsbD_allOnes]
    exact decide_eq_true i.isLt
  · rw [bit_liftGoal,no]
    simp
abbrev SliceSpec := Nat × Nat × Nat × Nat × Nat × Nat × Nat
def specDomain (s : SliceSpec) : Sig × Nat :=
  (subcube s.1 s.2.1, s.2.2.2.2.2.1)
def certifiesSlice (m : Nat) (earlier : List (Nat × Nat)) (s : SliceSpec) : Bool :=
  let (z,o,q,support,hints,L,base) := s
  ((q == 0 && base == 0) || earlier.contains (q,base)) &&
    ((z == m-q && o == 0 && L == base && zeroSliceOK m q) ||
      mixedColumnOK m z o q support hints L base)
theorem certifiesSlice_sound {m earlier s}
    (prior : ∀ e ∈ earlier, Lower true (vars e.1) (graphGoal e.1) e.2)
    (ok : certifiesSlice m earlier s = true) :
    Slice true (vars m) (graphGoal m) (specDomain s).1 (specDomain s).2 := by
  obtain ⟨z,o,q,support,hints,L,base⟩ := s
  simp only [certifiesSlice,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq,
    List.contains_eq_mem,decide_eq_true_eq] at ok
  have lower : Lower true (vars q) (graphGoal q) base := by
    rcases ok.1 with ⟨rfl,rfl⟩ | he
    · exact mixedBaseZero
    · exact prior (q,base) he
  rcases ok.2 with ⟨⟨⟨rfl,rfl⟩,rfl⟩,h⟩ | h
  · exact zeroSlice_sound h lower
  · exact mixedColumn_sound lower h
theorem compactDomains_valid {m earlier specs ds}
    (prior : ∀ e ∈ earlier, Lower true (vars e.1) (graphGoal e.1) e.2)
    (ok : List.all specs (certifiesSlice m earlier) = true)
    (matchDs : (specs.map specDomain).toArray = ds) :
    ∀ d ∈ ds, Slice true (vars m) (graphGoal m) d.1 d.2 := by
  subst ds
  intro d hd
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp (List.mem_toArray.mp hd)
  exact certifiesSlice_sound prior (List.all_eq_true.mp ok _ hs)
theorem compactAutos_valid {T : Sig} {ps : Perms}
    (ok : ps.toList.all (fun p => autoOK T (p.map swapRows).reverse) = true) :
    ∀ p ∈ ps, autoOK T (p.map swapRows).reverse = true := by
  intro p hp
  exact List.all_eq_true.mp ok _ (Array.mem_toList_iff.mpr hp)
theorem compactRoot {g t dom perms}
    (pairs : properPairs (graphGoal g.mask) (asRow g.pos) (asRow g.neg))
    (valid : ∀ d ∈ dom, Slice true (vars g.mask) (graphGoal g.mask) d.1 d.2)
    (autos : ∀ p ∈ perms, autoOK (graphGoal g.mask) (p.map swapRows).reverse = true)
    (blocks : ∀ k ≤ g.top, chartBlock (compactNode g t dom perms k) 0 (t.count k) = true)
    (existsRoot : 0 < t.count g.top)
    (root : wordsAt g t g.top 0 = vars g.mask) :
    Impossible true (graphGoal g.mask) g.top (vars g.mask).toFinset := by
  rw [←root]
  exact compactAll pairs valid autos blocks _ (Nat.le_refl _) 0 existsRoot
def readCompactBits (table : Nat → Nat) (start width : Nat) : Nat :=
  let i := start / 4096
  let j := start % 4096
  let low := table i >>> j
  let result := if j + width ≤ 4096 then low else low ||| (table (i+1) <<< (4096-j))
  result &&& ((1 <<< width)-1)
def compactIDsFromBits (bits width : Nat) : Nat → List Nat
  | 0 => []
  | n+1 => (bits &&& ((1 <<< width)-1)) :: compactIDsFromBits (bits >>> width) width n
def samplesP73 : Nat → Bits
  | 0 => ~~~(0x110a : Bits)
  | 3 => ~~~(0x2070 : Bits)
  | 6 => 0xbf7a
  | _ => 0
def samplesQ73 : Nat → Bits
  | 0 => ~~~(0xebde : Bits)
  | 3 => 0x280c
  | 6 => 0x4212
  | _ => 0
def compactPerms73 : Array (List Nat) := ([[], [99], [48], [48, 99], [96, 99], [96]] : List (List Nat)).toArray
def compactDomains73 : Array (Sig × Nat) := ([] : List (Sig × Nat)).toArray
def compactWords73 : Nat → Nat
  | 0 => 0x7
  | _ => 0
def compactCount73 (k : Nat) : Nat := match k with
  | 3 => 1
  | _ => 0
def compactPath73 (k : Nat) (i : Nat) : Nat := match k with
  | 3 => 0
  | _ => 0
def compactLive73 (k : Nat) (i : Nat) : Nat := match k with
  | 3 => readCompactBits compactWords73 (0 + 3*i) 3
  | _ => 0
def compactPoolIDs73 (k : Nat) (i : Nat) : List Nat := match k with
  | 3 => let v := readCompactBits compactWords73 (3 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords73 (3 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []
def compactBucket73 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []
def samplesP75 : Nat → Bits
  | 0 => ~~~(0xa0c017012bc889a : Bits)
  | 1 => 0x78fe303e3fcc8f90
  | 3 => ~~~(0x11003632280cb1f0 : Bits)
  | 6 => 0x5ffdf77ffabcb9fa
  | _ => 0
def samplesQ75 : Nat → Bits
  | 0 => ~~~(0x75bbbfab5fbf2cbe : Bits)
  | 1 => 0x714d58e1415df10
  | 3 => 0x1180922903150c0c
  | 6 => 0x20200800488000a2
  | _ => 0
def compactPerms75 : Array (List Nat) := ([[], [48]] : List (List Nat)).toArray
def compactDomains75 : Array (Sig × Nat) := ([(subcube 2 0, 4)] : List (Sig × Nat)).toArray
def compactWords75 : Nat → Nat
  | 0 => 0x4f
  | _ => 0
def compactCount75 (k : Nat) : Nat := match k with
  | 4 => 1
  | _ => 0
def compactPath75 (k : Nat) (i : Nat) : Nat := match k with
  | 4 => 0
  | _ => 0
def compactLive75 (k : Nat) (i : Nat) : Nat := match k with
  | 4 => readCompactBits compactWords75 (0 + 4*i) 4
  | _ => 0
def compactPoolIDs75 (k : Nat) (i : Nat) : List Nat := match k with
  | 4 => let v := readCompactBits compactWords75 (5 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords75 (4 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []
def compactBucket75 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []
def samplesP102 : Nat → Bits
  | 1 => 0xebeb84e7be9ae70
  | 2 => ~~~(0x440ac6c4189b374 : Bits)
  | 5 => 0xdfdf63ff79a99ec
  | 6 => ~~~(0x80121c321a88e8 : Bits)
  | _ => 0
def samplesQ102 : Nat → Bits
  | 1 => 0x14863222902ec50
  | 2 => 0x4606c0b0242ec0a
  | 5 => 0x20400c0148000a4
  | 6 => ~~~(0xf6fffeb3fdffcfe : Bits)
  | _ => 0
def compactPerms102 : Array (List Nat) := ([[], [101], [33], [33, 101]] : List (List Nat)).toArray
def compactDomains102 : Array (Sig × Nat) := ([(subcube 2 0, 4)] : List (Sig × Nat)).toArray
def compactWords102 : Nat → Nat
  | 0 => 0x4f
  | _ => 0
def compactCount102 (k : Nat) : Nat := match k with
  | 4 => 1
  | _ => 0
def compactPath102 (k : Nat) (i : Nat) : Nat := match k with
  | 4 => 0
  | _ => 0
def compactLive102 (k : Nat) (i : Nat) : Nat := match k with
  | 4 => readCompactBits compactWords102 (0 + 4*i) 4
  | _ => 0
def compactPoolIDs102 (k : Nat) (i : Nat) : List Nat := match k with
  | 4 => let v := readCompactBits compactWords102 (5 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords102 (4 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []
def compactBucket102 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []
def samplesP27 : Nat → Bits
  | 0 => ~~~(0x400c0c004482e492 : Bits)
  | 1 => 0xdbfe3c3b5f82ef92
  | 3 => ~~~(0xc023e830852f83a : Bits)
  | 4 => 0xefcffebfecd2fcfa
  | _ => 0
def samplesQ27 : Nat → Bits
  | 0 => ~~~(0xbf7bbbf7d6eed6f6 : Bits)
  | 1 => 0x2604d25914156b82
  | 3 => 0xd2298b082a656c4
  | 4 => 0x1062012640221470
  | _ => 0
def compactPerms27 : Array (List Nat) := ([[], [49, 64]] : List (List Nat)).toArray
def compactDomains27 : Array (Sig × Nat) := ([] : List (Sig × Nat)).toArray
def compactWords27 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def compactCount27 (k : Nat) : Nat := match k with
  | 3 => 1
  | _ => 0
def compactPath27 (k : Nat) (i : Nat) : Nat := match k with
  | 3 => 0
  | _ => 0
def compactLive27 (k : Nat) (i : Nat) : Nat := match k with
  | 3 => readCompactBits compactWords27 (0 + 4*i) 4
  | _ => 0
def compactPoolIDs27 (k : Nat) (i : Nat) : List Nat := match k with
  | 3 => let v := readCompactBits compactWords27 (4 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords27 (4 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []
def compactBucket27 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []
def samplesP118 : Nat → Bits
  | 1 => (OfNat.ofNat (limbs [0xddfeffb,0x1f3b671febf9fce1,0xf6739e7247df973b,0x26f3861d3b5e19e4]))
  | 2 => ~~~((OfNat.ofNat (limbs [0x700803,0xab317d009808701,0x927386f27708172c,0x42660e1dfb909dec])) : Bits)
  | 4 => (OfNat.ofNat (limbs [0xf63f8f7,0xe6f1300f3fe7ff02,0x71ffa03001bfff1c,0xde1e420039b7f024]))
  | 5 => (OfNat.ofNat (limbs [0xbf7ff6f,0x98f6decfdf9fb31d,0x8ff4ddc43ef97be7,0xc1ee3c24c6f18798]))
  | 6 => ~~~((OfNat.ofNat (limbs [0x1040060,0x94706e0002013800,0x65f499740f910b13,0x849a36243f7703b4])) : Bits)
  | _ => 0
def samplesQ118 : Nat → Bits
  | 1 => (OfNat.ofNat (limbs [0x2211800,0xc080804821102400,0xa04a0051041820a,0x20500027014a0144]))
  | 2 => (OfNat.ofNat (limbs [0x705a01,0x82115ca82440548,0xa25aaa00455c090,0x908110a7114f4012]))
  | 4 => (OfNat.ofNat (limbs [0x9e03a9,0x11060fb71801496e,0xb4b14d4a20be7404,0x40a5ac85eb5f020]))
  | 5 => (OfNat.ofNat (limbs [0x4088088,0x2208203404881802,0x14004400c1a80901,0x41200a0006308288]))
  | 6 => ~~~((OfNat.ofNat (limbs [0xefbdedf,0xfbafb5febfdd7fdb,0x5f6fffeff5fdcf9f,0xf5fb7fb7b77fc3fe])) : Bits)
  | _ => 0
def compactPerms118 : Array (List Nat) := ([[], [101]] : List (List Nat)).toArray
def compactDomains118 : Array (Sig × Nat) := ([(subcube 4 0, 5), (subcube 16 0, 5), (subcube 0 16, 5), (subcube 32 0, 4), (subcube 64 0, 4), (subcube 2 16, 4)] : List (Sig × Nat)).toArray
def compactWords118 : Nat → Nat
  | 0 => (OfNat.ofNat (limbs [0x13c5dca14641,0xea0d8fd19288c8bf]))
  | _ => 0
def compactCount118 (k : Nat) : Nat := match k with
  | 6 => 1
  | 5 => 1
  | 4 => 1
  | _ => 0
def compactPath118 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => 0
  | 5 => readCompactBits compactWords118 (26 + 12*i) 12
  | 4 => let v := readCompactBits compactWords118 (80 + 12*i) 12
    (readCompactBits compactWords118 (68 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | _ => 0
def compactLive118 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => readCompactBits compactWords118 (0 + 5*i) 5
  | 5 => readCompactBits compactWords118 (38 + 6*i) 6
  | 4 => readCompactBits compactWords118 (92 + 7*i) 7
  | _ => 0
def compactPoolIDs118 (k : Nat) (i : Nat) : List Nat := match k with
  | 6 => let v := readCompactBits compactWords118 (20 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords118 (5 + 3*(v &&& 7)) (3*n)
    compactIDsFromBits bits 3 n
  | 5 => let v := readCompactBits compactWords118 (52 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords118 (44 + 2*(v &&& 7)) (2*n)
    compactIDsFromBits bits 2 n
  | 4 => let v := readCompactBits compactWords118 (99 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords118 (99 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []
def compactBucket118 (k : Nat) (i : Nat) : List Nat := match k with
  | 5 => let d := readCompactBits compactWords118 (58 + 1*(i % 1)) 1
    let off := ((i/1 + d) % 1)
    let v := readCompactBits compactWords118 (59 + 9*off) 9
    if v >>> 1 == (i/104729)%251 then [v &&& 1] else []
  | 4 => let d := readCompactBits compactWords118 (101 + 1*(i % 1)) 1
    let off := ((i/1 + d) % 1)
    let v := readCompactBits compactWords118 (102 + 9*off) 9
    if v >>> 1 == (i/104729)%251 then [v &&& 1] else []
  | _ => []
def samplesP107 : Nat → Bits
  | 0 => ~~~((OfNat.ofNat (limbs [0x581,0xc0102ba7f0001896,0xdcc00ba5e7fc0113,0x18d98ff931a07bba])) : Bits)
  | 1 => (OfNat.ofNat (limbs [0x5f3f,0xf8fd6d8447dd3ff7,0x2cc67b0024dfec57,0x3e9cf1f9003be320]))
  | 3 => ~~~((OfNat.ofNat (limbs [0x840,0xddd004780c2408,0xcc674ba24f80c54,0xa53831f93e43b768])) : Bits)
  | 5 => (OfNat.ofNat (limbs [0x7cff,0xe7d6db6637aeffb8,0xdfe60fa446b79f97,0x897b39e031c75b88]))
  | 6 => (OfNat.ofNat (limbs [0x6fff,0xdfd9b2bdff7ffcde,0xdcd9f4bba16c7d78,0xf5f986193e60b47a]))
  | _ => 0
def samplesQ107 : Nat → Bits
  | 0 => ~~~((OfNat.ofNat (limbs [0x7a7b,0x36eff75c2c6f5ff5,0xcf1e6cdfbe764373,0xdeffb79e29b07bfe])) : Bits)
  | 1 => (OfNat.ofNat (limbs [0x20e0,0x834082533e08124a,0x45ab221510276842,0x121022cb84bac220]))
  | 3 => (OfNat.ofNat (limbs [0x848,0x24510042c4200a0,0x450a208204464220,0x885028a00b04094]))
  | 5 => (OfNat.ofNat (limbs [0x310,0x48082408c1240900,0x30409108a8009401,0x804a182052450908]))
  | 6 => (OfNat.ofNat (limbs [0x1002,0x22410000014410,0x4002100110,0x4420800000003042]))
  | _ => 0
def compactPerms107 : Array (List Nat) := ([[], [16, 83]] : List (List Nat)).toArray
def compactDomains107 : Array (Sig × Nat) := ([(subcube 1 0, 5), (subcube 2 0, 5), (subcube 8 0, 5), (subcube 32 0, 5)] : List (Sig × Nat)).toArray
def compactWords107 : Nat → Nat
  | 0 => 0x41c9f
  | _ => 0
def compactCount107 (k : Nat) : Nat := match k with
  | 6 => 1
  | _ => 0
def compactPath107 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => 0
  | _ => 0
def compactLive107 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => readCompactBits compactWords107 (0 + 5*i) 5
  | _ => 0
def compactPoolIDs107 (k : Nat) (i : Nat) : List Nat := match k with
  | 6 => let v := readCompactBits compactWords107 (13 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords107 (5 + 2*(v &&& 7)) (2*n)
    compactIDsFromBits bits 2 n
  | _ => []
def compactBucket107 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []
def samplesP59 : Nat → Bits
  | 0 => ~~~((OfNat.ofNat (limbs [0x206001c0d3,0x211a8100430028d8,0xfc663e23c48034c6,0x19327327b6d305f2])) : Bits)
  | 1 => (OfNat.ofNat (limbs [0x76dfbffce3,0xf582ffb75fed38c7,0x7e67ac03dfed33e6,0x756c7326a1b634d2]))
  | 3 => ~~~((OfNat.ofNat (limbs [0x380300823,0x98c68023040e4087,0x6e01ed9398083330,0xa18d7f26e9183ada])) : Bits)
  | 4 => (OfNat.ofNat (limbs [0x7b6ff3fb9f,0x99567dffe74a6999,0xefb9e990fcbf763b,0xb9b11c26c9db4a1a]))
  | 5 => (OfNat.ofNat (limbs [0x6faffdcf73,0x2af8ff6bff96c6fe,0xfc4656237fdabdd4,0x8b9e63013659bde0]))
  | _ => 0
def samplesQ59 : Nat → Bits
  | 0 => ~~~((OfNat.ofNat (limbs [0x5f9f3f2f6e,0xdff59dfbdbf7a7df,0x73e1f7dec6bef6fe,0xdf3df0e77ef34ff6])) : Bits)
  | 1 => (OfNat.ofNat (limbs [0x924508108,0x83c448212004a2a,0x28948308138520a0,0x50082a5283262482]))
  | 3 => (OfNat.ofNat (limbs [0x381180922,0x10448d1080a0828a,0x3280e01206a6840c,0x420a0621aa34424]))
  | 4 => (OfNat.ofNat (limbs [0x4980a0c40,0x42819860407481c1,0x12205440443a4212,0x900902178d14a10]))
  | 5 => (OfNat.ofNat (limbs [0x1052025404,0x85033009091c1141,0x842a0084e8581040,0x8216150960589940]))
  | _ => 0
def compactPerms59 : Array (List Nat) := ([[], [81, 67], [16, 83], [16, 49, 67, 84], [48, 84], [48, 65, 83, 84], [64, 49], [64, 81, 67, 84], [80, 81, 83, 84], [80, 65]] : List (List Nat)).toArray
def compactDomains59 : Array (Sig × Nat) := ([(subcube 1 0, 4), (subcube 2 0, 4), (subcube 8 0, 4), (subcube 16 0, 4), (subcube 32 0, 4)] : List (Sig × Nat)).toArray
def compactWords59 : Nat → Nat
  | 0 => (OfNat.ofNat (limbs [0x3e93b242,0xe118bfc1c1bfc3fc,0x3fc12be51a00cc26,0x821fe0ff07f83188,0x4422b37f807ddd11,0x204554b167fe00c6,0xfffd00900688d11f]))
  | _ => 0
def compactCount59 (k : Nat) : Nat := match k with
  | 6 => 1
  | 5 => 2
  | 4 => 1
  | _ => 0
def compactPath59 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => 0
  | 5 => readCompactBits compactWords59 (26 + 12*i) 12
  | 4 => let v := readCompactBits compactWords59 (283 + 12*i) 12
    (readCompactBits compactWords59 (271 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | _ => 0
def compactLive59 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => readCompactBits compactWords59 (0 + 5*i) 5
  | 5 => readCompactBits compactWords59 (50 + 6*i) 6
  | 4 => readCompactBits compactWords59 (295 + 7*i) 7
  | _ => 0
def compactPoolIDs59 (k : Nat) (i : Nat) : List Nat := match k with
  | 6 => let v := readCompactBits compactWords59 (20 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords59 (5 + 3*(v &&& 7)) (3*n)
    compactIDsFromBits bits 3 n
  | 5 => let v := readCompactBits compactWords59 (64 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords59 (62 + 2*(v &&& 1)) (2*n)
    compactIDsFromBits bits 2 n
  | 4 => let v := readCompactBits compactWords59 (302 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords59 (302 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []
def compactBucket59 (k : Nat) (i : Nat) : List Nat := match k with
  | 5 => let d := readCompactBits compactWords59 (68 + 2*(i % 4)) 2
    let off := ((i/4 + d) % 15)
    let v := readCompactBits compactWords59 (76 + 13*off) 13
    if v >>> 5 == (i/104729)%251 then [v &&& 31] else []
  | 4 => let d := readCompactBits compactWords59 (304 + 1*(i % 2)) 1
    let off := ((i/2 + d) % 9)
    let v := readCompactBits compactWords59 (306 + 12*off) 12
    if v >>> 4 == (i/104729)%251 then [v &&& 15] else []
  | _ => []
def samplesP91 : Nat → Bits
  | 0 => ~~~((OfNat.ofNat (limbs [0x404000c,0xb9640a0211080e64,0x2c3885d268462051,0x61ad1dcde1a558e6])) : Bits)
  | 1 => (OfNat.ofNat (limbs [0xdebf1ff,0xdaf4c83ffbeafee4,0x23f8b55029ffa4c7,0x33fb01cde0fc38a2]))
  | 3 => ~~~((OfNat.ofNat (limbs [0x581180,0x272ecc100606112,0x23f0b7793d802ec6,0x1540c3cdfe423fb2])) : Bits)
  | 4 => (OfNat.ofNat (limbs [0xf57ff8f,0xb57aa43f57fde176,0x2c77f54913d7fad4,0xed65c209e467d432]))
  | 6 => (OfNat.ofNat (limbs [0xedffffc,0x2b677affbd7f4f1b,0xffb882b26fee6f7b,0x558c1dc41b837bc4]))
  | _ => 0
def samplesQ91 : Nat → Bits
  | 0 => ~~~((OfNat.ofNat (limbs [0xbfbbdfb,0x7edbfdf7df7bbdf9,0xefff3effb77777dd,0xf7bdfdf9ddb7ddee])) : Bits)
  | 1 => (OfNat.ofNat (limbs [0x2150684,0x2402166a40220206,0x9512d20a80ad8445,0x2200a96a2dc2082]))
  | 3 => (OfNat.ofNat (limbs [0x5894c0,0x2502ce492101108,0xa55a142120754110,0x8091289885b58048]))
  | 4 => (OfNat.ofNat (limbs [0xaa1051,0x88149940448b528,0x60c9009407527080,0x240464484d23d420]))
  | 6 => (OfNat.ofNat (limbs [0x1202011,0x5008811109012420,0x4081084013020208,0x5108444048025904]))
  | _ => 0
def compactPerms91 : Array (List Nat) := ([[], [65, 96]] : List (List Nat)).toArray
def compactDomains91 : Array (Sig × Nat) := ([(subcube 2 0, 5)] : List (Sig × Nat)).toArray
def compactWords91 : Nat → Nat
  | 0 => 0x9f
  | _ => 0
def compactCount91 (k : Nat) : Nat := match k with
  | 5 => 1
  | _ => 0
def compactPath91 (k : Nat) (i : Nat) : Nat := match k with
  | 5 => 0
  | _ => 0
def compactLive91 (k : Nat) (i : Nat) : Nat := match k with
  | 5 => readCompactBits compactWords91 (0 + 5*i) 5
  | _ => 0
def compactPoolIDs91 (k : Nat) (i : Nat) : List Nat := match k with
  | 5 => let v := readCompactBits compactWords91 (6 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords91 (5 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []
def compactBucket91 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []
def samplesP123 : Nat → Bits
  | 0 => ~~~((OfNat.ofNat (limbs [0x100c00,0x722791420e891b,0x5001810802c03980,0x60d4298270be2ccc,0x7ea3780a3bd6d601,0x451a2180c606c07,0x3041ec0f59e47b80,0xdbc6d9706573e8f4,0xfdd123443842ad0e,0xb06e076cf994fcf9,0x9fec1db4d50eddd6])) : Bits)
  | 1 => (OfNat.ofNat (limbs [0x7bdbff,0x1fff3ba3fb52b368,0xdff7ffdf76d3f9eb,0xf5dc3c7df0cf4ca7,0xd6e868a42a1095ed,0x7ffb7b365e3be69f,0x75f8b52071e47807,0x43ffe8707c42c810,0x99d1feee6e2e8c9c,0x72a716ce2b601cf9,0x872800ed80de1942]))
  | 3 => ~~~((OfNat.ofNat (limbs [0x203002,0x18018021699cd664,0x3002400230d38070,0x982020756105c8b7,0x677216e52e5fb440,0x580012471c0b82c4,0x48331bc085c5d847,0x43bff01c9f5ede1c,0x9fe4d414840e9cde,0x4bc16c9c8c6e1ff9,0x9f7be34624fbbb72])) : Bits)
  | 4 => (OfNat.ofNat (limbs [0x7e2ffe,0xf8feaf5ded9c4513,0x1fcfdd7fffff8e71,0xe8f4758f6fb22bcd,0x6652b669040081ff,0xfd5fb3d93f7b1de5,0xfab11ac1d427c381,0xdb87d6b39a424608,0x29ef757bf72dd56,0x835ae4e09d8a0701,0x7308176f7290062]))
  | 5 => (OfNat.ofNat (limbs [0x7777f3,0xff7df6f34ebccab4,0x6fffefbebbe3f196,0x7ae3abf3ff0cf0d6,0x2db750da324607d3,0xfff6e6cf9dc7ff5e,0x794749de89d87fc6,0x83c6114c6730a024,0xd51de9f595cf2f0a,0x7944293dccf418c0,0x18cc0f164ce4dc10]))
  | 6 => (OfNat.ofNat (limbs [0x7dbfff,0xfff3c5bd73ef9c4f,0x3ffbf3ebffdc3ffc,0x9f3febf670358c38,0x7b231f07e9df707f,0xdefd9e7fececeae7,0x8e63ee0f0fc59878,0x7c38f91c851d18d4,0x2c67171cf8deb0ef,0x8ce94f1cf004e038,0x98437380351aa394]))
  | _ => 0
def samplesQ123 : Nat → Bits
  | 0 => ~~~((OfNat.ofNat (limbs [0x6ff3eb,0xdfcfdeefbdf9f6ec,0xee7dfdfbbe1ff87f,0x7f13fdf5ff7bdff3,0xfd7fe7fdee6d7e7b,0x675fbf9fff6f7eff,0x3fdde3ff57de63ff,0x5bf9dfec9fedffdf,0xcfb73b5f3f53edfe,0xbf7f777ff9effc3f,0x1f9f9dbcf72fdfde])) : Bits)
  | 1 => (OfNat.ofNat (limbs [0x42480,0x68204448008c4c12,0x2521084020a50520,0xa502a024200210,0x2011041895062124,0x12c3010408024090,0x2402040480a91512,0x2914421248082482,0x4018cc862280884,0x2220104800404a92,0xc22044c980941102]))
  | 3 => (OfNat.ofNat (limbs [0x203022,0x4c0080210908c644,0x2c00211108154038,0x20120a1340040a0,0x414200412c452430,0x74a281082401022,0x108421402884112,0x49515a000b401008,0x88012a4a33110120,0x8014020241014813,0x20494a8d2040488]))
  | 4 => (OfNat.ofNat (limbs [0x1d103,0x58500821021b2ec,0xca4410220210d81d,0x3300ec1592088400,0x882401840a695e5b,0x651c828030080441,0x9c6353124660c9,0x40c919a486218904,0x3633171d52c012,0x102402018072409,0x99d913477290040]))
  | 5 => (OfNat.ofNat (limbs [0x88845,0x92080420431109,0x90d0840090400a85,0x9048480e80110901,0x100822004098d8c1,0xa824040a05012008,0x180419012806a841,0x84022121a4040251,0x9c412584840400,0x1840210500b40540,0x20d822160c604810]))
  | 6 => (OfNat.ofNat (limbs [0x24200,0x1041200841020a0,0x4208408804009000,0x2100841003421042,0x400c0200220020a,0x4010100140240a04,0x250204210400088,0x88008400804000,0x4302101008422048,0x4090410a0022008,0x9010100210a8204]))
  | _ => 0
def compactPerms123 : Array (List Nat) := ([[], [16, 83]] : List (List Nat)).toArray
def compactDomains123 : Array (Sig × Nat) := ([(subcube 1 0, 7), (subcube 2 0, 7), (subcube 16 0, 7), (subcube 64 0, 7), (subcube 8 0, 6), (subcube 32 0, 6), (subcube 0 16, 6), (subcube 9 0, 5), (subcube 17 0, 5), (subcube 24 0, 5), (subcube 34 0, 5), (subcube 48 0, 5), (subcube 1 16, 5), (subcube 2 16, 5), (subcube 10 0, 4), (subcube 33 0, 4), (subcube 65 0, 4), (subcube 66 0, 4), (subcube 72 0, 4), (subcube 80 0, 4), (subcube 96 0, 4), (subcube 3 16, 4), (subcube 19 0, 4), (subcube 25 0, 4), (subcube 50 0, 4)] : List (Sig × Nat)).toArray
def compactWords123 : Nat → Nat
  | 0 => (OfNat.ofNat (limbs [0xdfebf9cc29cc290c,0x2e4c4e4c184858cc,0x488c484c484c38cc,0x184c18cc084c0446,0x544454cc448c444c,0x44cc244c24cc144c,0x1c485c465c445c40,0x5c4c5c4c2c4c07c6,0x5746574657c45744,0x5744574057cc57cc,0x574c574c57cc374c,0x37cc07cc074c0046,0x504c504c504c304c,0xd485d4c5d4c4d4c,0x164853485b485b46,0x5b445b4c5b444b4c,0x4b4c354855c65546,0x55c4554455445542,0x554055cc554c554c,0x55c4454445444540,0x45cc454c45cc054c,0xac85a485a465a44,0x5a425a4c5a824a4c,0x4a4c12c852485246,0x524452425240524c,0x528242424240424c,0x41445140514c5144,0x41cc31422180214c,0x2c45c43844822802,0x4654454444434224,0x54034024010440e,0x16b08ff03fc0033a,0xa51ff03fc06787fc,0xfa4c655ff0334df,0xf0180c715d542ff0,0x2818ff00006e2277,0xc3ff0229dd52ffc0,0x83e41a570488a55,0x1d004546ffc08c7e,0x654f35bfc0b767fc,0x40010b41027b6da,0x98a1b96c8ac7eb73,0xd66c5aa50848b3dc,0x31e23c17c0bb00c2,0xef6c8c452040b1a7,0x426b326ab58236b2,0x3288c106d3a1e4e5,0xb984101f7ac8e453,0x881db0fa0406311,0xb80dacf951477308,0x20c737ac9cbc3053,0xb1880ac9cab10ca1,0xe032d3af80637293,0x2c9c0dcfa6a0c250,0xca6e081b4872738c,0xa61038456db90b92,0x3288c1e6d9a012e3,0x288c1e6d9a21ec32,0x8b8451c01af7ffdf,0xffffffffffffffff,0xffffffffc6546546,0x5c45445405844444,0x44c434434038224,0x228024024018393f]))
  | 1 => (OfNat.ofNat (limbs [0x5240ce052010283,0x3810286040400338,0x7091406483022804,0x1c36181090c6c58,0x20800c970a0c3020,0x21c0190e3cc80067,0x19b2364c33c72dc4,0xcd992c0800c0890a,0xf344cc962838915,0x302cb0c1e7099828,0x3846618a12061408,0x383438b680c0801,0xa1dece1b2da070c2,0x430868502036e7c3,0x1c7235b1f6604c87,0x2415983001811238,0x1c4873e6420a1424,0x18604040330ef04c,0xe0e125b30c507036,0xf2d90230cce1b2e0,0xdbcb6cc8a9c1a0e6,0x9f321ce0e08cce0e,0x240418e0934f9232,0x59833838dcb0834,0x8833854c901c1410,0x6007070e38288920,0x63830222cc900381,0x448e9a7c39914107,0x40acc0981d34f99,0x81450166ccc8f1d,0x38c03041800a1c38,0x28a2e541854a0831,0x91c6c38e0054c840,0xa10a036e7c31c2a3,0x1b1f38c88042a442,0x50418001640c91c,0x814485061810100,0x119092a0df059a18,0x1001c119070a5038,0x36e7c30c3855c9f2,0x4003b20670a910e4,0x604061ce32381c2,0x8604400920e14507,0x2ed07cc18102872e,0xc3021e059076848,0xa9d2005983385433,0x30a108112a08b342,0xa6e73c72cc3322ed,0xe9e023820700c8a,0xa20004ab33a08185,0x2e38395bff7f7bfb,0xfdfbfffffffbfffb,0xfffd7dfbfffffbff,0xfbfffeff7ffffbfb,0xfbff7fff7fbfffbf,0xfffbfffbfffffffb,0xffff7bf9fb7beffb,0xfbfbdfffffff7fbb,0xffbbfb7fff7f7fbf,0xffbfdffbfffbffbf,0xffbffbfffbffffff,0xff7fbffbfffbfbff,0xffff7fbfffebffff,0xffebffffebfffb7f]))
  | 2 => (OfNat.ofNat (limbs [0x5017ca08ceefb560,0x50cffe0077957f0f,0x657eae674cc0d27d,0xe8f1fe01fe013c97,0x54a5e27e22ff9fb4,0xfd0dc437fe01fe01,0xfe01fe01fe00933b,0xfe01fe016c1cfebd,0xf54b73860daea0e0,0xac6a820a58618201,0xa214006d8002a300,0x53a3898a248008c9,0x37800b040400,0x1b400221c20c386,0x6820020060000180,0xcd4d14f3d2ef484d,0xeb4134f853d1cee,0xd38acd8b33bcc0b2,0xdcca51254c8291ea,0xc71517245570fbc3,0x70ac41a9049c0cd,0x4bef8f5c3c66f0,0x4bae8e9ab9cae493,0x8e8e1c3768dbbb60,0x6d6ab506d2cb388c,0xc531d6c1b2faebb2,0xae28b6c2caeaf32b,0x4ab12a86a8c292c,0xa1ca74c9a4a57091,0x924348bc21f083b2,0x347bc1de875b1ca,0xc6fc9ad067299345,0xfa1770599961253b,0x14244f913b04aa92,0x646c90844148f38,0x3690d6434c0c2e2d,0x18aec28c89042310,0x8901e4068618b855,0x210903ee0c581ac0,0x3b801301051a0401,0x3683261e346469d2,0x63019e6a186a03a0,0xc3020201a8706d42,0xcd0c0800e0e48194,0x814106033001224,0x14a05242431b2664,0x10504180121c4491,0xa02166820c04c920,0xe40919000cd8220e,0x661518c881f06482,0x700c810608000b2,0x641a900a6c60f0e,0x502900a0830002c8,0x38320d4812081c28,0x20c10d002ac81906,0xa30d903444095144,0x8a366418d9338f1b,0x920a701842014106,0x600514126418604,0x400a0e2c7cd0618,0x1070004c8a0a0d9b,0x2046ce182e6c3130,0x66d9b20cd9b93381,0xca1c081029c240c2]))
  | 3 => (OfNat.ofNat (limbs [0x4498688a98508898,0x480a984802983886,0x98300498288a9810,0x8898008890b88690,0xa8868cb0448ca088,0x88b08888b04488b0,0x488a88888a84488,0xa80488a802889044,0x88884488880284a8,0x4484480280b08880,0xa88880a84480a804,0x80a8028088448088,0x41848cb3c400b0a,0xfbadb2872ec91f57,0x805e2e5941917f08,0x442c5f2b41b70bb9,0xfe01fe0132adc3a6,0x956606a10a39fe01,0xfe00919763293eb3,0xe0e6adba268b855e,0x62de72db616fe6ea,0x47b2381912650a9e,0xe16cda6a5c4283a9,0x68c5719d9a1e1a56,0xb8faefbe9129e62,0xf20bfe003d4dfe00,0x4ed5fe00e05cbd30,0xe426e77310212423,0xc559e62b2d173f7b,0xb136812ee6752c3a,0x468cc8043f92f08e,0x94b1e702c9b0ba6e,0xd0486af750005376,0x7cbffe01649c124f,0x748968baeb32b4cc,0xa151be2f2ca68f05,0x925acd64629b82e2,0x66ae884686910b82,0x3234a1063ef21980,0x4a3ffe00f60ed6c7,0x3ae5e407731eb347,0xfe00cd8a62d3874e,0xbd9e34a3f51a4d42,0xb41b9645512c2a82,0xee2462e9458cc9a2,0xc55b3a7a7602bea9,0xb55d5727f155d922,0xe76baee0664b96aa,0x9353dc533b78bb74,0x8633aedcbf99fe01,0xfe01fe00f8b7fe01,0xfe00063c9e736c68,0xa66c16760695fe01,0x15aaa478457caa99,0xfe01c850f2ec9a4d,0xd231fe014169fe01,0xd14530d8953ffe00,0x1284d0713135ead0,0x2c13d261c189fe01,0xfe00eeb9fe01fe01,0xbac3fe01fe01fe00,0x8370b162ed9b1492,0x9b848cd64eb5fe01,0xfe01fe000fa1a0ca]))
  | 4 => (OfNat.ofNat (limbs [0x453e8ca7d114fe72,0x9f4e53290a65194c,0xa02994e5729c2412,0x14824290ce10c8ca,0x191164232c844590,0x8cb211964222c84e,0x5b9cab7381ee42b,0xd4857a8caf5115ee,0x72bd4e57a9c25339,0x94a32a94e3308ca5,0xf3898a42a74854f9,0xca9d394e24296ce2,0x2b9cc492157a428c,0x485188ca31314667,0x28c4e54c90a99195,0x3222a6ce54c9ca85,0x215c2720f4851f9c,0x8252144a3289ce41,0x39c0151142e71474,0xe48e9c0b33916242,0xacce4599c8b33916,0x722cce06e8cadd0,0x95ba62b74e51690a,0x2d1945a128bcc516,0x98a2f3945a728bce,0x104889151962a22c,0x54258a9cb150122a,0x7024ce17888af109,0x5e272bc4e4769cc4,0x52157242b44e64b9,0xa952152a32a5445,0x4b9ca953952e709b,0x4453684a6d395d27,0x3a4e61c90a11194,0x222284ce4579c8af,0x3859a70334e60390,0xa052140a32814450,0x298a073940a72a2c,0x854490a891951222,0xa2405459ca893951,0x670a2ce01b9c00d1,0x141e722ace2159c0,0x2b39a1a22c34e586,0x888211144202884c,0x5119ca2139442220,0x84046488ac909592,0x72b2824649c87511,0x4ea129d4053b9ca7,0x5394ea021dce43a9,0xc998a88998a84598,0x888b98884598880b,0x9868039848cb9848,0xb98288b98280b98,0x88b980889980845,0x90b00590a80588a8,0x8988a84588884518,0x888b18880b049005,0x4880500480298b8,0x8698b08898b04498,0xb00498a88898a844,0x98a80498a80298a0,0x8898988a98988698,0x9044989004988844,0x98880a9888049870]))
  | 5 => (OfNat.ofNat (limbs [0x44e4989282524888,0x81112104287d0eb1,0xa0348618ab120248,0x400801021e439062,0xa410c1501803600,0x160606020a363e0a,0x3e06060820d6280c,0x4d624000ac80606,0x606060a06080a20,0x608040406060600,0x7872ff009adc04d6,0xd29adcd6dcd69ad0,0xa060404723f006d,0x2e0a06061d2e2206,0x362a1a2a081c3202,0xc040a0b000aca0a,0x21c66329c069c00,0xc0406062afa000a,0x606062a060a0a20,0x2a0618d6a20ec806,0x8000ad20a080606,0x606073002000202,0x40c0d30642a3a2a,0x68083c013064023d,0x301c2a0202062a06,0x2a060c040a0c04cc,0xa060c053fbbdde7,0xf3f9fdeefd9f9fcf,0xedf6f9fcff3f3f9f,0xf5ebf7e9ff5ef73f,0x9ff5e7f3fe7f5ef7,0x9fdbeee7f3fd7edf,0x7d3fbdf6f977bebf,0x6fafdbcfe5f3f3fc,0xfcff5fafdbeee7f3,0xf9fcdf2f97db5ef3,0xfaf9fcff7b7b9bf6,0xf3febf9eeef77bd7,0xedf773f9fedef7db,0xbdf77ab7dbef6ef7,0x3f9fdbf3f3fd7cbf,0x5f3ff9fe7777bf5f,0xcff3bbdddeef7f9f,0x5edf77bd9febe7f7,0xdddef67f3f9ff6f3,0xf3fd7ebf6fbb9fcf,0xe7fbbdecfefd3fed,0xf5bb57e9fcfefd3f,0xf77bbedfadf5fafd,0xafd7edf77be9fcfe,0x7fbebf77afd3fbf4,0xff6f37dbfe7f9bdb,0xedf7f3fcfd7f2fdf,0xcbf6ef7bbe9fcff7,0xd3f9fc24e4849c80,0x13914670c64e18c9,0xc0d9389067040485,0x809c901380d6721a,0xe47c9c8f9386222,0x2c44e2889c2d5195,0xaa72b54e06a9cc8d,0x1951e71414e4829c,0x279195fa723f4e22,0x690a1d1943e71304]))
  | 6 => (OfNat.ofNat (limbs [0x84c8b74dc15b6afb,0xfe00323e7f802191,0x75f1b2857dfcb7fc,0x1fe001a1d7f803f,0xc002a020c0db8c19,0xbd74cc4aff000138,0xc5d386c44c938aa9,0x611263fe0031bc18,0x80634ddfe0025297,0xf800ec284505ff00,0x10d571f0dfe00c7b,0x6279a540e1fe0018,0xa609e13fc011efef,0xf0075b6926708c36,0x5977c538782da796,0x9f733ff802b83f9d,0x83ba13e81452d51f,0xe009369a9d36faff,0x785b0409da4d575f,0x6a5643d5b8a5d7fc,0x9096cd5947b36b,0x58e2c91a14282000,0xe080920248828c0,0x3050000b8000041,0x830604701060c403,0x100018006980532e,0x286004278b3200,0x3400080401000,0x60c032003400f1,0x801801604000020,0x4f800c04c8314000,0x100742860004180,0x888f021409b00,0x4d0002140000424,0x801404082000030,0xac158aa8550aa154,0x6a4548a91526a054,0xa815069c538a714,0xea95d11a1340e744,0xe89d536a644c9983,0x2e6584b19532864c,0x49893324248c8891,0x122641c688d31823,0xc598a312620c388,0x730c2184308630a2,0x1442885309202bdb,0x788e81d0b99720e4,0x5c438970ad61acb5,0x6a0d41a83506a2d,0x25a0340680d01a03,0x41672cc19ab08614,0xbe974ae05c4b4168,0xac8592b055c2b857,0xae15cab0560ac55,0x42a8552a8150a985,0x36a01412714d09a5,0x3125149290918231,0x4508a114a2044088,0x50ca104208410821,0x14147e4f89e83d07,0xb4e3190320640c89,0x88310620c4980302,0x5e0bc9702e25a4b0,0x9592a0540a815129]))
  | 7 => (OfNat.ofNat (limbs [0x983fe000693fab7a,0xac182739f3b5580c,0xbe9ebfe00ed0e4f4,0xfd6b3f510764742,0xbff4c8b5661f116b,0x63ad4c9de77cbda9,0xd1c027716565ce1b,0xd3b484caedc26fb3,0x29a730db0573637f,0xf002588d34844d0d,0xb4ab6b8440e74e6c,0x9ff00514fcda7dfe,0xff00750c416348,0x490c567f800ca4b,0xfe004fae154bab56,0xa4057ff000b97e62,0xe6ac74c06dda3170,0x869b4a5c802b8d9a,0xcea4ce16aec4481d,0xd1b013d1cbe2eb60,0xf3fc00dd16ff007f,0x803fc01fe00e6c4a,0x4decfd3ffe002b67,0x7f80175da07688ab,0x7f801d6b5fe0004,0x8f7f803fc01b0d07,0xc3cf8399495df2b3,0x7c07ff801929c1f7,0x88af930f87af320,0x88b20ade6078515c,0x4932f43591b61db9,0xc8302b73cc60861a,0x9bb724f8cce28ad5,0xd49349ea8083ca74,0x88c787d5ea7e5a9c,0x8aee5d40db464dbd,0x8ba3fa841ff007f8,0x13d7620d8b70bde,0x451a5849f624c48f,0xf8015443e685ff00,0x19e1de9993cad07a,0xff8016109825444,0x342b838dd3a68be8,0xc40da9360a167229,0x9f8ec9dd022a2fa2,0x5ff003a265956844,0x9093496f40a206b4,0x409e7747f80111ac,0x94b0e350c02f3fc0,0x1fe006a9bb626aad,0x304f7159045aaaff,0xc01fe00f52d3bb2a,0x9dd9ba83cb027f80,0x20006d6bdff00215,0x53806686d2985f9a,0x1ed1a2e86d9c73aa,0x51d51c8df5b2372,0xff80095fb40eeff0,0x21423fc0026e0ff,0x5abc64c4cb1225,0x37e7f803189f9248,0xcc3009063fc01514,0x69167d9a788cbdfe,0x857c9b30270ff5]))
  | 8 => (OfNat.ofNat (limbs [0x8579194246565215,0x14653521624653d2,0x15d4653121614651,0x91946d0415214546,0x539215c4651d194b,0x485811955d046d11,0x4848551114a48511,0x19444457d1957d02,0x511404446141c34,0x455b4113d05ce5cc,0x444ce54c4822ce5,0x4c4802ce54c4402c,0xe54c2844ce544482,0x2ce5444422ce4405,0x402ce24c4405ce14,0x454448248024014e,0x54c44024e54c2401,0x4e54c18024e54044,0x24e44c24014e1cc,0x4454e0cc54444e0,0x8c44054c54448224,0xc5444422445cc044,0x44454c48224454c4,0x8024454c44024454,0xc284444540440242,0x5cc4422425c44422,0x4254444224054c44,0x24054c24014054c,0x844405422401404,0x422401446b89aa77,0x1f0e16ed87a16078,0xe032bb582a3f1719,0xba66dd20664ae84a,0x9040ed513209a85b,0x4aea64606f01a79a,0x1d849254e03db987,0xb22525487b42c794,0x39dcbffc00896367,0xb7ff8030901586cf,0xf0070375f226000d,0x265b612e710d7fe0,0x91c08143fc0124,0x7aff0076517ea864,0x76b6b51db0897554,0x8478ee32ab8fcb9a,0xb593cce7d7f8000f,0xb0eb16d0501877f,0xc00d8b84c711f082,0xc52a9e39a499d7df,0xad9363d3bdb23b4c,0x27291f25657788de,0x1569d1310d148a50,0x6843d94c3724c598,0x4eb7e1eaffe00302,0x587460f6cf328dff,0x7f8018881dec6f,0x5797f803fc01c4cb,0xbf310552c40b2543,0xb55af1f02e38c9fe,0x4a39ff8030225e,0xc72aa12518bd9315,0x4a071531ca41cc4d,0x4b93d527b8032001,0x2ee70484626b4578]))
  | 9 => (OfNat.ofNat (limbs [0xc181,0xfe00b0cb63cd40f9,0x48ffc07f80574d52,0x4eeda5a3eda12ac7,0x98185dbbe81e9855,0xe9d0ebf422830aac,0xd4d79db48ac72284,0x8a8af341b5086790,0x7084e04a9414c4c7,0xf808145d4e7fc012,0x963a5dfe037813cc,0x717572f2e44f8b31,0x2703fe018894bb38,0x74f102ffc0303264,0x8dfe03fc02c49d60,0x7303345c7f80be7b,0x824084d982c055ae,0x4d4d8e03433834ee,0x3b00bb841ac6dfe0,0x335b87a4ff01fe03,0xfc0118a519440a01,0x4eea8650062099a6,0x88801164204408,0x1020408102040810,0x2040810204081020,0x4081020408105cb0,0x60c18ac102400000,0x180c656007194640,0x38bf56d4f8bc5f96,0xd2f17e2f17e2f53e,0x2f17f46e9f27d1e2,0xf53e578bc5e2fd6b,0xcad6b8be5b9ac5e3,0xbf63e89f39a8be1f,0x4b41104656919494]))
  | _ => 0
def compactCount123 (k : Nat) : Nat := match k with
  | 9 => 1
  | 8 => 17
  | 7 => 111
  | 6 => 198
  | 5 => 38
  | _ => 0
def compactPath123 (k : Nat) (i : Nat) : Nat := match k with
  | 9 => 0
  | 8 => readCompactBits compactWords123 (20 + 12*i) 12
  | 7 => let v := readCompactBits compactWords123 (2300 + 16*i) 16
    (readCompactBits compactWords123 (2120 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | 6 => let v := readCompactBits compactWords123 (17337 + 19*i) 19
    (readCompactBits compactWords123 (15585 + 24*(v >>> 12)) 24) ||| ((v &&& 4095) <<< 24)
  | 5 => let v := readCompactBits compactWords123 (36244 + 18*i) 18
    (readCompactBits compactWords123 (34984 + 36*(v >>> 12)) 36) ||| ((v &&& 4095) <<< 36)
  | _ => 0
def compactLive123 (k : Nat) (i : Nat) : Nat := match k with
  | 9 => readCompactBits compactWords123 (0 + 6*i) 6
  | 8 => readCompactBits compactWords123 (224 + 7*i) 7
  | 7 => readCompactBits compactWords123 (4076 + 8*i) 8
  | 6 => readCompactBits compactWords123 (21099 + 9*i) 9
  | 5 => readCompactBits compactWords123 (36928 + 10*i) 10
  | _ => 0
def compactPoolIDs123 (k : Nat) (i : Nat) : List Nat := match k with
  | 9 => let v := readCompactBits compactWords123 (14 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords123 (6 + 2*(v &&& 7)) (2*n)
    compactIDsFromBits bits 2 n
  | 8 => let v := readCompactBits compactWords123 (1288 + 12*i) 12
    let n := v >>> 8
    let bits := readCompactBits compactWords123 (343 + 5*(v &&& 255)) (5*n)
    compactIDsFromBits bits 5 n
  | 7 => let v := readCompactBits compactWords123 (9773 + 14*i) 14
    let n := v >>> 10
    let bits := readCompactBits compactWords123 (4964 + 7*(v &&& 1023)) (7*n)
    compactIDsFromBits bits 7 n
  | 6 => let v := readCompactBits compactWords123 (24257 + 11*i) 11
    let n := v >>> 8
    let bits := readCompactBits compactWords123 (22881 + 8*(v &&& 255)) (8*n)
    compactIDsFromBits bits 8 n
  | 5 => let v := readCompactBits compactWords123 (37380 + 7*i) 7
    let n := v >>> 4
    let bits := readCompactBits compactWords123 (37308 + 9*(v &&& 15)) (9*n)
    compactIDsFromBits bits 9 n
  | _ => []
def compactBucket123 (k : Nat) (i : Nat) : List Nat := match k with
  | 8 => let d := readCompactBits compactWords123 (1492 + 4*(i % 10)) 4
    let off := ((i/10 + d) % 42)
    let v := readCompactBits compactWords123 (1532 + 14*off) 14
    if v >>> 6 == (i/104729)%251 then [v &&& 63] else []
  | 7 => let d := readCompactBits compactWords123 (11327 + 6*(i % 67)) 6
    let off := ((i/67 + d) % 241)
    let v := readCompactBits compactWords123 (11729 + 16*off) 16
    if v >>> 8 == (i/104729)%251 then [v &&& 255] else []
  | 6 => let d := readCompactBits compactWords123 (26435 + 7*(i % 126)) 7
    let off := ((i/126 + d) % 451)
    let v := readCompactBits compactWords123 (27317 + 17*off) 17
    if v >>> 9 == (i/104729)%251 then [v &&& 511] else []
  | 5 => let d := readCompactBits compactWords123 (37646 + 5*(i % 24)) 5
    let off := ((i/24 + d) % 86)
    let v := readCompactBits compactWords123 (37766 + 15*off) 15
    if v >>> 7 == (i/104729)%251 then [v &&& 127] else []
  | _ => []
theorem compactHalves {test : Nat → Bool} {start n : Nat}
    (first : chartBlock test start (n / 2) = true)
    (last : chartBlock test (start + n / 2) (n - n / 2) = true) :
    chartBlock test start n = true := by
  have eq : n / 2 + (n - n / 2) = n := by omega
  simpa only [eq] using chartBlock_join first last
def grid73 : CompactGrid := (73, 3, samplesP73, samplesQ73)
def tab73 : CompactTable := (compactCount73, compactPath73, compactLive73, compactPoolIDs73, compactBucket73)
def check73 (k : Nat) := compactNode grid73 tab73 compactDomains73 compactPerms73 k
def sliceSpecs73 : List SliceSpec := []
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains73 : ∀ d ∈ compactDomains73, Slice true (vars 73) (graphGoal 73) d.1 d.2 := by
  apply compactDomains_valid (earlier := []) (specs := sliceSpecs73)
  · simp
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs73 : properPairs (graphGoal 73) (asRow samplesP73) (asRow samplesQ73) :=
  compactPairs (g := grid73) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos73 : ∀ p ∈ compactPerms73, autoOK (graphGoal 73) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c73k3p0 : chartBlock (check73 3) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev73k3 : chartBlock (check73 3) 0 1 = true :=
  c73k3p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded73 : Impossible true (graphGoal 73) 3 (vars 73).toFinset := by
  apply compactRoot (g := grid73) (t := tab73) (dom := compactDomains73) (perms := compactPerms73) pairs73 domains73 autos73
  · intro k hk
    change k ≤ 3 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · exact lev73k3
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound73 : Lower true (vars 73) (graphGoal 73) 4 :=
  plain_low (hints := 3) (by decide +kernel) excluded73
def grid75 : CompactGrid := (75, 4, samplesP75, samplesQ75)
def tab75 : CompactTable := (compactCount75, compactPath75, compactLive75, compactPoolIDs75, compactBucket75)
def check75 (k : Nat) := compactNode grid75 tab75 compactDomains75 compactPerms75 k
def sliceSpecs75 : List SliceSpec := [(2, 0, 73, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains75 : ∀ d ∈ compactDomains75, Slice true (vars 75) (graphGoal 75) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(73, 4)]) (specs := sliceSpecs75)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound73
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs75 : properPairs (graphGoal 75) (asRow samplesP75) (asRow samplesQ75) :=
  compactPairs (g := grid75) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos75 : ∀ p ∈ compactPerms75, autoOK (graphGoal 75) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c75k4p0 : chartBlock (check75 4) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev75k4 : chartBlock (check75 4) 0 1 = true :=
  c75k4p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded75 : Impossible true (graphGoal 75) 4 (vars 75).toFinset := by
  apply compactRoot (g := grid75) (t := tab75) (dom := compactDomains75) (perms := compactPerms75) pairs75 domains75 autos75
  · intro k hk
    change k ≤ 4 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev75k4
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound75 : Lower true (vars 75) (graphGoal 75) 5 :=
  plain_low (hints := 99) (by decide +kernel) excluded75
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound114 : Lower true (vars 114) (graphGoal 114) 5 :=
  carry_of (old := 114) (rep := 75) (swaps := [97, 100, 83, 96]) (by decide +kernel) bound75
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound100 : Lower true (vars 100) (graphGoal 100) 4 :=
  carry_of (old := 100) (rep := 73) (swaps := [32, 83]) (by decide +kernel) bound73
def grid102 : CompactGrid := (102, 4, samplesP102, samplesQ102)
def tab102 : CompactTable := (compactCount102, compactPath102, compactLive102, compactPoolIDs102, compactBucket102)
def check102 (k : Nat) := compactNode grid102 tab102 compactDomains102 compactPerms102 k
def sliceSpecs102 : List SliceSpec := [(2, 0, 100, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains102 : ∀ d ∈ compactDomains102, Slice true (vars 102) (graphGoal 102) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(100, 4)]) (specs := sliceSpecs102)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound100
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs102 : properPairs (graphGoal 102) (asRow samplesP102) (asRow samplesQ102) :=
  compactPairs (g := grid102) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos102 : ∀ p ∈ compactPerms102, autoOK (graphGoal 102) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c102k4p0 : chartBlock (check102 4) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev102k4 : chartBlock (check102 4) 0 1 = true :=
  c102k4p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded102 : Impossible true (graphGoal 102) 4 (vars 102).toFinset := by
  apply compactRoot (g := grid102) (t := tab102) (dom := compactDomains102) (perms := compactPerms102) pairs102 domains102 autos102
  · intro k hk
    change k ≤ 4 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev102k4
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound102 : Lower true (vars 102) (graphGoal 102) 5 :=
  plain_low (hints := 17827152) (by decide +kernel) excluded102
def grid27 : CompactGrid := (27, 3, samplesP27, samplesQ27)
def tab27 : CompactTable := (compactCount27, compactPath27, compactLive27, compactPoolIDs27, compactBucket27)
def check27 (k : Nat) := compactNode grid27 tab27 compactDomains27 compactPerms27 k
def sliceSpecs27 : List SliceSpec := []
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains27 : ∀ d ∈ compactDomains27, Slice true (vars 27) (graphGoal 27) d.1 d.2 := by
  apply compactDomains_valid (earlier := []) (specs := sliceSpecs27)
  · simp
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs27 : properPairs (graphGoal 27) (asRow samplesP27) (asRow samplesQ27) :=
  compactPairs (g := grid27) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos27 : ∀ p ∈ compactPerms27, autoOK (graphGoal 27) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c27k3p0 : chartBlock (check27 3) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev27k3 : chartBlock (check27 3) 0 1 = true :=
  c27k3p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded27 : Impossible true (graphGoal 27) 3 (vars 27).toFinset := by
  apply compactRoot (g := grid27) (t := tab27) (dom := compactDomains27) (perms := compactPerms27) pairs27 domains27 autos27
  · intro k hk
    change k ≤ 3 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · exact lev27k3
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound27 : Lower true (vars 27) (graphGoal 27) 4 :=
  plain_low (hints := 67) (by decide +kernel) excluded27
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound86 : Lower true (vars 86) (graphGoal 86) 4 :=
  carry_of (old := 86) (rep := 27) (swaps := [16, 32, 67, 99]) (by decide +kernel) bound27
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound54 : Lower true (vars 54) (graphGoal 54) 4 :=
  carry_of (old := 54) (rep := 27) (swaps := [16, 32, 67, 83]) (by decide +kernel) bound27
def grid118 : CompactGrid := (118, 6, samplesP118, samplesQ118)
def tab118 : CompactTable := (compactCount118, compactPath118, compactLive118, compactPoolIDs118, compactBucket118)
def check118 (k : Nat) := compactNode grid118 tab118 compactDomains118 compactPerms118 k
def sliceSpecs118 : List SliceSpec := [(4, 0, 114, 0, 0, 5, 5), (16, 0, 102, 0, 0, 5, 5), (0, 16, 100, 2, 240, 5, 4), (32, 0, 86, 0, 0, 4, 4), (64, 0, 54, 0, 0, 4, 4), (2, 16, 100, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains118 : ∀ d ∈ compactDomains118, Slice true (vars 118) (graphGoal 118) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(114, 5), (102, 5), (100, 4), (86, 4), (54, 4)]) (specs := sliceSpecs118)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl
    · exact bound114
    · exact bound102
    · exact bound100
    · exact bound86
    · exact bound54
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs118 : properPairs (graphGoal 118) (asRow samplesP118) (asRow samplesQ118) :=
  compactPairs (g := grid118) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos118 : ∀ p ∈ compactPerms118, autoOK (graphGoal 118) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c118k4p0 : chartBlock (check118 4) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev118k4 : chartBlock (check118 4) 0 1 = true :=
  c118k4p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c118k5p0 : chartBlock (check118 5) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev118k5 : chartBlock (check118 5) 0 1 = true :=
  c118k5p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c118k6p0 : chartBlock (check118 6) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev118k6 : chartBlock (check118 6) 0 1 = true :=
  c118k6p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded118 : Impossible true (graphGoal 118) 6 (vars 118).toFinset := by
  apply compactRoot (g := grid118) (t := tab118) (dom := compactDomains118) (perms := compactPerms118) pairs118 domains118 autos118
  · intro k hk
    change k ≤ 6 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev118k4
    · exact lev118k5
    · exact lev118k6
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound118 : Lower true (vars 118) (graphGoal 118) 7 :=
  plain_low (hints := 17892672) (by decide +kernel) excluded118
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound122 : Lower true (vars 122) (graphGoal 122) 7 :=
  carry_of (old := 122) (rep := 118) (swaps := [50]) (by decide +kernel) bound118
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound121 : Lower true (vars 121) (graphGoal 121) 7 :=
  carry_of (old := 121) (rep := 118) (swaps := [16, 83, 82]) (by decide +kernel) bound118
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound106 : Lower true (vars 106) (graphGoal 106) 5 :=
  carry_of (old := 106) (rep := 102) (swaps := [50]) (by decide +kernel) bound102
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound105 : Lower true (vars 105) (graphGoal 105) 5 :=
  carry_of (old := 105) (rep := 102) (swaps := [16, 83, 82]) (by decide +kernel) bound102
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound99 : Lower true (vars 99) (graphGoal 99) 5 :=
  carry_of (old := 99) (rep := 75) (swaps := [16, 83]) (by decide +kernel) bound75
def grid107 : CompactGrid := (107, 6, samplesP107, samplesQ107)
def tab107 : CompactTable := (compactCount107, compactPath107, compactLive107, compactPoolIDs107, compactBucket107)
def check107 (k : Nat) := compactNode grid107 tab107 compactDomains107 compactPerms107 k
def sliceSpecs107 : List SliceSpec := [(1, 0, 106, 0, 0, 5, 5), (2, 0, 105, 0, 0, 5, 5), (8, 0, 99, 0, 0, 5, 5), (32, 0, 75, 0, 0, 5, 5)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains107 : ∀ d ∈ compactDomains107, Slice true (vars 107) (graphGoal 107) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(106, 5), (105, 5), (99, 5), (75, 5)]) (specs := sliceSpecs107)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact bound106
    · exact bound105
    · exact bound99
    · exact bound75
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs107 : properPairs (graphGoal 107) (asRow samplesP107) (asRow samplesQ107) :=
  compactPairs (g := grid107) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos107 : ∀ p ∈ compactPerms107, autoOK (graphGoal 107) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c107k6p0 : chartBlock (check107 6) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev107k6 : chartBlock (check107 6) 0 1 = true :=
  c107k6p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded107 : Impossible true (graphGoal 107) 6 (vars 107).toFinset := by
  apply compactRoot (g := grid107) (t := tab107) (dom := compactDomains107) (perms := compactPerms107) pairs107 domains107 autos107
  · intro k hk
    change k ≤ 6 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev107k6
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound107 : Lower true (vars 107) (graphGoal 107) 7 :=
  plain_low (hints := 1048659) (by decide +kernel) excluded107
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound58 : Lower true (vars 58) (graphGoal 58) 4 :=
  carry_of (old := 58) (rep := 27) (swaps := [65, 80]) (by decide +kernel) bound27
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound57 : Lower true (vars 57) (graphGoal 57) 4 :=
  carry_of (old := 57) (rep := 27) (swaps := [67, 81]) (by decide +kernel) bound27
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound51 : Lower true (vars 51) (graphGoal 51) 4 :=
  carry_of (old := 51) (rep := 27) (swaps := [16, 83]) (by decide +kernel) bound27
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound43 : Lower true (vars 43) (graphGoal 43) 4 :=
  carry_of (old := 43) (rep := 27) (swaps := [48, 84]) (by decide +kernel) bound27
def grid59 : CompactGrid := (59, 6, samplesP59, samplesQ59)
def tab59 : CompactTable := (compactCount59, compactPath59, compactLive59, compactPoolIDs59, compactBucket59)
def check59 (k : Nat) := compactNode grid59 tab59 compactDomains59 compactPerms59 k
def sliceSpecs59 : List SliceSpec := [(1, 0, 58, 0, 0, 4, 4), (2, 0, 57, 0, 0, 4, 4), (8, 0, 51, 0, 0, 4, 4), (16, 0, 43, 0, 0, 4, 4), (32, 0, 27, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains59 : ∀ d ∈ compactDomains59, Slice true (vars 59) (graphGoal 59) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(58, 4), (57, 4), (51, 4), (43, 4), (27, 4)]) (specs := sliceSpecs59)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl
    · exact bound58
    · exact bound57
    · exact bound51
    · exact bound43
    · exact bound27
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs59 : properPairs (graphGoal 59) (asRow samplesP59) (asRow samplesQ59) :=
  compactPairs (g := grid59) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos59 : ∀ p ∈ compactPerms59, autoOK (graphGoal 59) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c59k4p0 : chartBlock (check59 4) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev59k4 : chartBlock (check59 4) 0 1 = true :=
  c59k4p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c59k5p0 : chartBlock (check59 5) 0 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev59k5 : chartBlock (check59 5) 0 2 = true :=
  c59k5p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c59k6p0 : chartBlock (check59 6) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev59k6 : chartBlock (check59 6) 0 1 = true :=
  c59k6p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded59 : Impossible true (graphGoal 59) 6 (vars 59).toFinset := by
  apply compactRoot (g := grid59) (t := tab59) (dom := compactDomains59) (perms := compactPerms59) pairs59 domains59 autos59
  · intro k hk
    change k ≤ 6 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev59k4
    · exact lev59k5
    · exact lev59k6
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound59 : Lower true (vars 59) (graphGoal 59) 7 :=
  plain_low (hints := 1048643) (by decide +kernel) excluded59
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound89 : Lower true (vars 89) (graphGoal 89) 5 :=
  carry_of (old := 89) (rep := 75) (swaps := [96, 65]) (by decide +kernel) bound75
def grid91 : CompactGrid := (91, 5, samplesP91, samplesQ91)
def tab91 : CompactTable := (compactCount91, compactPath91, compactLive91, compactPoolIDs91, compactBucket91)
def check91 (k : Nat) := compactNode grid91 tab91 compactDomains91 compactPerms91 k
def sliceSpecs91 : List SliceSpec := [(2, 0, 89, 0, 0, 5, 5)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains91 : ∀ d ∈ compactDomains91, Slice true (vars 91) (graphGoal 91) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(89, 5)]) (specs := sliceSpecs91)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound89
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs91 : properPairs (graphGoal 91) (asRow samplesP91) (asRow samplesQ91) :=
  compactPairs (g := grid91) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos91 : ∀ p ∈ compactPerms91, autoOK (graphGoal 91) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c91k5p0 : chartBlock (check91 5) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev91k5 : chartBlock (check91 5) 0 1 = true :=
  c91k5p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded91 : Impossible true (graphGoal 91) 5 (vars 91).toFinset := by
  apply compactRoot (g := grid91) (t := tab91) (dom := compactDomains91) (perms := compactPerms91) pairs91 domains91 autos91
  · intro k hk
    change k ≤ 5 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev91k5
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound91 : Lower true (vars 91) (graphGoal 91) 6 :=
  plain_low (hints := 67) (by decide +kernel) excluded91
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound115 : Lower true (vars 115) (graphGoal 115) 6 :=
  carry_of (old := 115) (rep := 91) (swaps := [16, 83]) (by decide +kernel) bound91
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound104 : Lower true (vars 104) (graphGoal 104) 4 :=
  carry_of (old := 104) (rep := 73) (swaps := [80]) (by decide +kernel) bound73
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound113 : Lower true (vars 113) (graphGoal 113) 4 :=
  carry_of (old := 113) (rep := 27) (swaps := [67, 81, 99]) (by decide +kernel) bound27
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound90 : Lower true (vars 90) (graphGoal 90) 4 :=
  carry_of (old := 90) (rep := 27) (swaps := [65, 96]) (by decide +kernel) bound27
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound98 : Lower true (vars 98) (graphGoal 98) 4 :=
  carry_of (old := 98) (rep := 73) (swaps := [16, 83]) (by decide +kernel) bound73
def grid123 : CompactGrid := (123, 9, samplesP123, samplesQ123)
def tab123 : CompactTable := (compactCount123, compactPath123, compactLive123, compactPoolIDs123, compactBucket123)
def check123 (k : Nat) := compactNode grid123 tab123 compactDomains123 compactPerms123 k
def sliceSpecs123 : List SliceSpec := [(1, 0, 122, 0, 0, 7, 7), (2, 0, 121, 0, 0, 7, 7), (16, 0, 107, 0, 0, 7, 7), (64, 0, 59, 0, 0, 7, 7), (8, 0, 115, 0, 0, 6, 6), (32, 0, 91, 0, 0, 6, 6), (0, 16, 104, 3, 255, 6, 4), (9, 0, 114, 0, 0, 5, 5), (17, 0, 106, 0, 0, 5, 5), (24, 0, 99, 0, 0, 5, 5), (34, 0, 89, 0, 0, 5, 5), (48, 0, 75, 0, 0, 5, 5), (1, 16, 104, 2, 240, 5, 4), (2, 16, 104, 1, 15, 5, 4), (10, 0, 113, 0, 0, 4, 4), (33, 0, 90, 0, 0, 4, 4), (65, 0, 58, 0, 0, 4, 4), (66, 0, 57, 0, 0, 4, 4), (72, 0, 51, 0, 0, 4, 4), (80, 0, 43, 0, 0, 4, 4), (96, 0, 27, 0, 0, 4, 4), (3, 16, 104, 0, 0, 4, 4), (19, 0, 104, 0, 0, 4, 4), (25, 0, 98, 0, 0, 4, 4), (50, 0, 73, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains123 : ∀ d ∈ compactDomains123, Slice true (vars 123) (graphGoal 123) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(122, 7), (121, 7), (107, 7), (59, 7), (115, 6), (91, 6), (104, 4), (114, 5), (106, 5), (99, 5), (89, 5), (75, 5), (113, 4), (90, 4), (58, 4), (57, 4), (51, 4), (43, 4), (27, 4), (98, 4), (73, 4)]) (specs := sliceSpecs123)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact bound122
    · exact bound121
    · exact bound107
    · exact bound59
    · exact bound115
    · exact bound91
    · exact bound104
    · exact bound114
    · exact bound106
    · exact bound99
    · exact bound89
    · exact bound75
    · exact bound113
    · exact bound90
    · exact bound58
    · exact bound57
    · exact bound51
    · exact bound43
    · exact bound27
    · exact bound98
    · exact bound73
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs123 : properPairs (graphGoal 123) (asRow samplesP123) (asRow samplesQ123) :=
  compactPairs (g := grid123) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos123 : ∀ p ∈ compactPerms123, autoOK (graphGoal 123) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c123k5p0 : chartBlock (check123 5) 0 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c123k5p1 : chartBlock (check123 5) 32 6 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev123k5 : chartBlock (check123 5) 0 38 = true :=
  (chartBlock_join (a := 32) (b := 6) c123k5p0 c123k5p1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c123k6p0 : chartBlock (check123 6) 0 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c123k6p1 : chartBlock (check123 6) 32 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c123k6p2 : chartBlock (check123 6) 64 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c123k6p3 : chartBlock (check123 6) 96 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c123k6p4 : chartBlock (check123 6) 128 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c123k6p5 : chartBlock (check123 6) 160 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c123k6p6 : chartBlock (check123 6) 192 6 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev123k6 : chartBlock (check123 6) 0 198 = true :=
  (chartBlock_join (a := 96) (b := 102) (chartBlock_join (a := 32) (b := 64) c123k6p0 (chartBlock_join (a := 32) (b := 32) c123k6p1 c123k6p2)) (chartBlock_join (a := 64) (b := 38) (chartBlock_join (a := 32) (b := 32) c123k6p3 c123k6p4) (chartBlock_join (a := 32) (b := 6) c123k6p5 c123k6p6)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c123k7p0 : chartBlock (check123 7) 0 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c123k7p1 : chartBlock (check123 7) 32 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c123k7p2 : chartBlock (check123 7) 64 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c123k7p3 : chartBlock (check123 7) 96 15 = true := by
  iterate 2 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev123k7 : chartBlock (check123 7) 0 111 = true :=
  (chartBlock_join (a := 64) (b := 47) (chartBlock_join (a := 32) (b := 32) c123k7p0 c123k7p1) (chartBlock_join (a := 32) (b := 15) c123k7p2 c123k7p3))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c123k8p0 : chartBlock (check123 8) 0 17 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev123k8 : chartBlock (check123 8) 0 17 = true :=
  c123k8p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c123k9p0 : chartBlock (check123 9) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev123k9 : chartBlock (check123 9) 0 1 = true :=
  c123k9p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded123 : Impossible true (graphGoal 123) 9 (vars 123).toFinset := by
  apply compactRoot (g := grid123) (t := tab123) (dom := compactDomains123) (perms := compactPerms123) pairs123 domains123 autos123
  · intro k hk
    change k ≤ 9 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev123k5
    · exact lev123k6
    · exact lev123k7
    · exact lev123k8
    · exact lev123k9
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound123 : Lower true (vars 123) (graphGoal 123) 10 :=
  plain_low (hints := 1048643) (by decide +kernel) excluded123
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded127 : Impossible true (graphGoal 127) 10 (vars 127).toFinset :=
  poolCut_sound (zeroSlice_sound (m:=127) (s:=123) (by decide +kernel) bound123) []
    (by rfl) (by decide +kernel) (by decide +kernel)
end PEqualNP.Outside.L_meta_30332.P11311

namespace PEqualNP.Outside.L_meta_30332.P10724
open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_30332.P11311
def graphGoal (m : Nat) : Sig :=
  let x := vertex m
 (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 3 &&& x 4) ||| (x 0 &&& x 5) ||| (x 2 &&& x 5) ||| (x 3 &&& x 5) ||| (x 0 &&& x 6) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 5 &&& x 6)
def carryOK (old rep : Nat) (swaps : List Nat) :=
  (properB (graphGoal old) && plainWord (graphGoal old) && (varsX old).all plainWord) && properB (graphGoal rep) &&
    checkMap (swaps.map swapRows) (varsX old) (graphGoal old) (varsX rep) (graphGoal rep)
theorem carry_of {u old rep L swaps} (ok : carryOK old rep swaps = true)
    (h : Lower u (varsX rep) (graphGoal rep) L) : Lower u (varsX old) (graphGoal old) L := by
  simp only [carryOK,Bool.and_eq_true] at ok
  exact lower_map ok.2 (proper_of _ ok.1.1.1.1) ok.1.1.1.2 ok.1.1.2 (proper_of _ ok.1.2) h
def essOK (m hints : Nat) : Bool :=
  let xs := graphPairs m hints
  properB (graphGoal m) && checkEssential (graphGoal m) (vars m) xs && (xs.map Prod.fst == vars m)
theorem plain_low {u} {m hints cap : Nat} (ok : essOK m hints = true)
    (a : Impossible u (graphGoal m) cap (vars m).toFinset) : Lower u (vars m) (graphGoal m) (cap+1) := by
  simp only [essOK,Bool.and_eq_true,beq_iff_eq] at ok
  apply lower_impossible (proper_of _ ok.1.1) (essential_plain ok.1.2).1 (essential_plain ok.1.2).2 _ a
  intro v hv
  apply essential_ok ok.1.2 v
  rw [ok.2]
  exact List.mem_toFinset.mpr hv
def target (x : Fin 7 → Bool) : Bool := decide (∃ i < ([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)
def zeroSliceOK (m s : Nat) : Bool :=
  let fixed := m - s
  let moves := fixRows fixed 0
  properB (graphGoal s) && (movedWord moves (subcube fixed 0) == one &&
    checkMap moves (vars m) (graphGoal m) (vars s) (graphGoal s))
theorem zeroSlice_sound {m s l} (ok : zeroSliceOK m s = true)
    (prior : Lower true (vars s) (graphGoal s) l) :
    Slice true (vars m) (graphGoal m) (subcube (m - s) 0) l := by
  simp only [zeroSliceOK, Bool.and_eq_true, beq_iff_eq] at ok
  exact slice_correct ok.2.2 ok.2.1 (proper_of _ ok.1) prior
def mixedColumnOK (m z o q support hints L base : Nat) : Bool :=
  let ms := fixRows z o
  let free := colFree m z o
  let G := movedWord ms (graphGoal m)
  let xs := mixedPairs support hints
  let count := (xs.map Prod.fst).toFinset.card
  properB G && checkMap ms (vars m) (graphGoal m) (vars free) G &&
    (movedWord ms (subcube z o) == one) &&
    (if q = 0 then checkEssential G (vars free) xs && decide (L ≤ count - 1)
     else properB (graphGoal q) &&
       checkLift (fixRows (colFree free q 0) 0) G (vars free) (vars q) (graphGoal q) xs &&
       decide (L ≤ base + count))
theorem mixedColumn_sound {m z o q support hints L base : Nat}
    (prior : Lower true (vars q) (graphGoal q) base)
    (ok : mixedColumnOK m z o q support hints L base = true) :
    Slice true (vars m) (graphGoal m) (subcube z o) L := by
  let ms := fixRows z o
  let free := colFree m z o
  let G := movedWord ms (graphGoal m)
  let xs := mixedPairs support hints
  change (((properB G && checkMap ms (vars m) (graphGoal m) (vars free) G) &&
    (movedWord ms (subcube z o) == one)) && _) = true at ok
  simp only [Bool.and_eq_true, beq_iff_eq] at ok
  apply slice_correct ok.1.1.2 ok.1.2 (proper_of _ ok.1.1.1)
  intro p bank hr ha
  have h := ok.2
  by_cases hq : q = 0
  · simp only [hq, if_true, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.2.trans (lower_count (proper_of _ ok.1.1.1) xs h.1 p bank hr ha)
  · simp only [hq, if_false, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.2.trans (lift_ok h.1.2 (proper_of _ ok.1.1.1) (proper_of _ h.1.1) prior p bank hr ha)
theorem mixedBaseZero : Lower true (vars 0) (graphGoal 0) 0 :=
  fun _ _ _ _ => Nat.zero_le _
def liftGoal (m : Nat) (v : Nat → Bits) : Bits :=
  let x := fun j => if m.testBit j then v j else 0
 (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 3 &&& x 4) ||| (x 0 &&& x 5) ||| (x 2 &&& x 5) ||| (x 3 &&& x 5) ||| (x 0 &&& x 6) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 5 &&& x 6)
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 1024) :
    bit (asRow v i) (graphGoal m) = (liftGoal m v).getLsbD i.val := by
  have pos (j : Nat) (hj : j<9) : (vertex m j).getLsbD (asRow v i).val = ((if m.testBit j then v j else 0) : Bits).getLsbD i.val := bit_vertex m v i ⟨j,hj⟩
  simp only [bit,graphGoal,liftGoal,BitVec.getLsbD_and,BitVec.getLsbD_or]
  simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide),pos 6 (by decide)]
theorem compactPool_sound {m : Nat} {domain : Sig × Nat} {hist : List Choice} {pool : BoundPool}
    (slice : Slice true (vars m) (graphGoal m) domain.1 domain.2)
    (ok : compactPool m domain hist = some pool) :
    ValidPool true (vars m) (graphGoal m) pool :=
  materialize_sound slice ok
theorem poolList_valid {m dom h picks} (valid : ∀ d ∈ dom, Slice true (vars m) (graphGoal m) d.1 d.2) :
    ∀ pool ∈ poolList m dom h picks, ValidPool true (vars m) (graphGoal m) pool := by
  intro pool hp
  obtain ⟨j,_,hj⟩ := List.mem_filterMap.mp hp
  cases e : dom[j % dom.size]? with
  | none => simp [e] at hj
  | some d =>
    simp only [e,Option.bind_some] at hj
    exact compactPool_sound (valid d (Array.mem_of_getElem? e)) hj
theorem linkedCandidates_valid {g t perms k}
    (autos : ∀ p ∈ perms, autoOK (graphGoal g.mask) (p.map swapRows).reverse = true)
    (prev : ∀ i < t.count k, Impossible true (graphGoal g.mask) k (wordsAt g t k i).toFinset) :
    ∀ tag xs, xs ∈ linkedCandidates g t perms k tag → Impossible true (graphGoal g.mask) k xs.toFinset := by
  intro tag xs hx
  obtain ⟨code,_,he⟩ := List.mem_filterMap.mp hx
  dsimp only at he
  split at he
  next small =>
    cases eq : perms[code % perms.size]? with
    | none => simp [eq] at he
    | some p =>
      simp only [eq,Option.map_some,Option.some.injEq] at he
      subst xs
      exact applySwaps_valid (autos p (Array.mem_of_getElem? eq)) (prev _ small)
  next => contradiction
theorem cachedLiveSize {u target k S} (h : Live u target k S) : S.card ≤ k+1 := by
  induction h using Live.ind with
  | stop hp => simp
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    omega
theorem cached_evalMove_sound {u raw T r s ws} {pools : List BoundPool} {links cap a b op ka kb}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a≠b) (hcap : 0<cap)
    (pv : ∀ p ∈ pools, ValidPool u raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible u T (cap-1) (List.toFinset xs))
    (pro : proper (dbin op a b).1) (fresh : (dbin op a b).1 ∉ ws.map Prod.fst)
    (test : cached_evalMove (cap,ws.length,ws,preCov u ws,pools.map (cacheOnePool u (ws.map Prod.fst)),links) op a b (dbin op a b) ka kb = true) :
    Impossible u T (cap-1) (cached_moveFront ws op a b ka kb).toFinset := by
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
  have hsz := cachedLiveSize h
  change child.toFinset.card ≤ k+1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have len : child.length ≤ cap := by omega
  unfold cached_evalMove at test
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
  have be : ((restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 1024) = false := by
    simpa using sep
  change (if (restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 1024 then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
  rw [be,pp,fr] at test
  exact cachedClose_sound (op:=movedChoice op a b) (rest:=rest.map Prod.fst) pv lv ndc (sub.map _).subset (List.mem_map_of_mem ha) (List.mem_map_of_mem hb) test k hk h
theorem cached_node_sound {u raw T r s ws} {pools : List BoundPool} {links cap}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools, ValidPool u raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible u T (cap-1) (List.toFinset xs))
    (checks : cached_testAll (cap,ws.length,ws,preCov u ws,pools.map (cacheOnePool u (ws.map Prod.fst)),links) ws = true) :
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
      (test : cached_testPair (cap,ws.length,ws,preCov u ws,pools.map (cacheOnePool u (ws.map Prod.fst)),links) a b d = true) :
      Impossible u T (cap-1) (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
    rw [←cached_binary_front nd aa bb ne']
    exact cached_evalMove_sound pairs faith nd aa bb (fun e => ne' (congrArg Prod.fst e)) hc' pv lv
      pr fr (cached_testPair_at test ka kb)
  rcases cached_all_binary checks haW hbW ab with hh | hh
  · exact one a b d haW hbW ne ka kb pro fresh (hh d hd)
  · rw [cached_childTwo_swap _ nd _ _ d hd]
    exact one b a (flipOp d) hbW haW (Ne.symm ne) kb ka (bin_flip hd a.1 b.1 ▸ pro)
      (bin_flip hd a.1 b.1 ▸ fresh) (hh _ (flip_flip hd).1)
def compactNode (g : CompactGrid) (t : CompactTable) (dom : Domains) (perms : Perms) (k i : Nat) : Bool :=
  let state := chartAt g t k i
  let ws := state.1
  let words := ws.map Prod.fst
  let pools := poolList g.mask dom state.2 (t.picks k i)
  let links := linkedCandidates g t perms (k-1)
  decide words.Nodup && (!(words.contains (graphGoal g.mask)) &&
    (if k=0 then true else cached_testAll (k,ws.length,ws,preCov true ws,pools.map (cacheOnePool true words),links) ws))
theorem compactNode_sound {g t dom perms k i}
    (pairs : properPairs (graphGoal g.mask) (asRow g.pos) (asRow g.neg))
    (valid : ∀ d ∈ dom, Slice true (vars g.mask) (graphGoal g.mask) d.1 d.2)
    (autos : ∀ p ∈ perms, autoOK (graphGoal g.mask) (p.map swapRows).reverse = true)
    (prev : 0 < k → ∀ j < t.count (k-1),
      Impossible true (graphGoal g.mask) (k-1) (wordsAt g t (k-1) j).toFinset)
    (check : compactNode g t dom perms k i = true) :
    Impossible true (graphGoal g.mask) k (wordsAt g t k i).toFinset := by
  simp only [compactNode,Bool.and_eq_true,decide_eq_true_eq] at check
  have out : graphGoal g.mask ∉ wordsAt g t k i := by simpa [wordsAt] using check.2.1
  by_cases hz : k=0
  · subst k
    intro n hn run
    obtain rfl : n = 0 := by omega
    exact out (List.mem_toFinset.mp (run.1.symm ▸ Finset.mem_singleton_self _))
  · have f : ∀ v ∈ (chartAt g t k i).1, faithful (asRow g.pos) (asRow g.neg) v :=
      rowWires_faithful _ (t.live k i) (walkCompact_faithful (g.top-k) (t.path k i)
        (rawDecor g.mask g.pos g.neg) [] (raw_faithful g.mask g.pos g.neg))
    apply cached_node_sound pairs f check.1 out (poolList_valid valid) (linkedCandidates_valid autos (prev (by omega)))
    simpa only [hz,ite_false] using check.2.2
theorem compactAll {g t dom perms}
    (pairs : properPairs (graphGoal g.mask) (asRow g.pos) (asRow g.neg))
    (valid : ∀ d ∈ dom, Slice true (vars g.mask) (graphGoal g.mask) d.1 d.2)
    (autos : ∀ p ∈ perms, autoOK (graphGoal g.mask) (p.map swapRows).reverse = true)
    (blocks : ∀ k ≤ g.top, chartBlock (compactNode g t dom perms k) 0 (t.count k) = true) :
    ∀ k ≤ g.top, ∀ i < t.count k, Impossible true (graphGoal g.mask) k (wordsAt g t k i).toFinset := by
  intro k
  induction k with
  | zero =>
    intro h i hi
    exact compactNode_sound pairs valid autos (by omega) (chartBlock_at (blocks 0 h) i (by omega) (by simpa using hi))
  | succ k ih =>
    intro h i hi
    exact compactNode_sound pairs valid autos (fun _ => ih (by omega)) (chartBlock_at (blocks _ h) i (by omega) (by simpa using hi))
theorem compactPairs {g : CompactGrid}
    (yes : liftGoal g.mask g.pos = BitVec.allOnes 1024) (no : liftGoal g.mask g.neg = 0) :
    properPairs (graphGoal g.mask) (asRow g.pos) (asRow g.neg) := by
  intro i
  constructor
  · rw [bit_liftGoal,yes,BitVec.getLsbD_allOnes]
    exact decide_eq_true i.isLt
  · rw [bit_liftGoal,no]
    simp
def certifiesSlice (m : Nat) (earlier : List (Nat × Nat)) (s : SliceSpec) : Bool :=
  let (z,o,q,support,hints,L,base) := s
  ((q == 0 && base == 0) || earlier.contains (q,base)) &&
    ((z == m-q && o == 0 && L == base && zeroSliceOK m q) ||
      mixedColumnOK m z o q support hints L base)
theorem certifiesSlice_sound {m earlier s}
    (prior : ∀ e ∈ earlier, Lower true (vars e.1) (graphGoal e.1) e.2)
    (ok : certifiesSlice m earlier s = true) :
    Slice true (vars m) (graphGoal m) (specDomain s).1 (specDomain s).2 := by
  obtain ⟨z,o,q,support,hints,L,base⟩ := s
  simp only [certifiesSlice,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq,
    List.contains_eq_mem,decide_eq_true_eq] at ok
  have lower : Lower true (vars q) (graphGoal q) base := by
    rcases ok.1 with ⟨rfl,rfl⟩ | he
    · exact mixedBaseZero
    · exact prior (q,base) he
  rcases ok.2 with ⟨⟨⟨rfl,rfl⟩,rfl⟩,h⟩ | h
  · exact zeroSlice_sound h lower
  · exact mixedColumn_sound lower h
theorem compactDomains_valid {m earlier specs ds}
    (prior : ∀ e ∈ earlier, Lower true (vars e.1) (graphGoal e.1) e.2)
    (ok : List.all specs (certifiesSlice m earlier) = true)
    (matchDs : (specs.map specDomain).toArray = ds) :
    ∀ d ∈ ds, Slice true (vars m) (graphGoal m) d.1 d.2 := by
  subst ds
  intro d hd
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp (List.mem_toArray.mp hd)
  exact certifiesSlice_sound prior (List.all_eq_true.mp ok _ hs)
theorem compactRoot {g t dom perms}
    (pairs : properPairs (graphGoal g.mask) (asRow g.pos) (asRow g.neg))
    (valid : ∀ d ∈ dom, Slice true (vars g.mask) (graphGoal g.mask) d.1 d.2)
    (autos : ∀ p ∈ perms, autoOK (graphGoal g.mask) (p.map swapRows).reverse = true)
    (blocks : ∀ k ≤ g.top, chartBlock (compactNode g t dom perms k) 0 (t.count k) = true)
    (existsRoot : 0 < t.count g.top)
    (root : wordsAt g t g.top 0 = vars g.mask) :
    Impossible true (graphGoal g.mask) g.top (vars g.mask).toFinset := by
  rw [←root]
  exact compactAll pairs valid autos blocks _ (Nat.le_refl _) 0 existsRoot
def samplesP25 : Nat → Bits
  | 0 => 0xbfae
  | 3 => ~~~(0x1128 : Bits)
  | 4 => ~~~(0x2086 : Bits)
  | _ => 0
def samplesQ25 : Nat → Bits
  | 0 => 0x420a
  | 3 => ~~~(0xebfa : Bits)
  | 4 => 0x2830
  | _ => 0
def compactPerms25 : Array (List Nat) := ([[], [67], [48], [48, 67], [64, 67], [64]] : List (List Nat)).toArray
def compactDomains25 : Array (Sig × Nat) := ([] : List (Sig × Nat)).toArray
def compactWords25 : Nat → Nat
  | 0 => 0x7
  | _ => 0
def compactCount25 (k : Nat) : Nat := match k with
  | 3 => 1
  | _ => 0
def compactPath25 (k : Nat) (i : Nat) : Nat := match k with
  | 3 => 0
  | _ => 0
def compactLive25 (k : Nat) (i : Nat) : Nat := match k with
  | 3 => readCompactBits compactWords25 (0 + 3*i) 3
  | _ => 0
def compactPoolIDs25 (k : Nat) (i : Nat) : List Nat := match k with
  | 3 => let v := readCompactBits compactWords25 (3 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords25 (3 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []
def compactBucket25 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []
def samplesP27 : Nat → Bits
  | 0 => 0x5ef9f1efddbe0e9a
  | 1 => 0x6cfe360dafc07f24
  | 3 => ~~~(0x6003741843078b4 : Bits)
  | 4 => ~~~(0x80800a0098e060a : Bits)
  | _ => 0
def samplesQ27 : Nat → Bits
  | 0 => 0x21224a0414921a12
  | 1 => 0x1382d13c8a16bf04
  | 3 => ~~~(0x79bf6bb7bebb5af6 : Bits)
  | 4 => 0x8100083200000e0
  | _ => 0
def compactPerms27 : Array (List Nat) := ([[], [48]] : List (List Nat)).toArray
def compactDomains27 : Array (Sig × Nat) := ([(subcube 2 0, 4)] : List (Sig × Nat)).toArray
def compactWords27 : Nat → Nat
  | 0 => 0x4f
  | _ => 0
def compactCount27 (k : Nat) : Nat := match k with
  | 4 => 1
  | _ => 0
def compactPath27 (k : Nat) (i : Nat) : Nat := match k with
  | 4 => 0
  | _ => 0
def compactLive27 (k : Nat) (i : Nat) : Nat := match k with
  | 4 => readCompactBits compactWords27 (0 + 4*i) 4
  | _ => 0
def compactPoolIDs27 (k : Nat) (i : Nat) : List Nat := match k with
  | 4 => let v := readCompactBits compactWords27 (5 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords27 (4 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []
def samplesP118 : Nat → Bits
  | 1 => (OfNat.ofNat (limbs [0xdd7efeb,0x1f3b642febf9fcd1,0xadcd9e1921f7e73b,0x26f38a2a68df18a4]))
  | 2 => ~~~((OfNat.ofNat (limbs [0x700803,0xab31fa009808701,0x25cf06f93d02472c,0x42660e3beb524eec])) : Bits)
  | 4 => (OfNat.ofNat (limbs [0xf6bf9f7,0xe6f1388f3fe7ff12,0xe3ff2078096fff1c,0xde1e4208eb37e464]))
  | 5 => (OfNat.ofNat (limbs [0xbf3fe5f,0x98f6d30fdf9fb32d,0x5ed35d8216fedbe7,0xc1ee345114f2d318]))
  | 6 => ~~~((OfNat.ofNat (limbs [0x1000040,0x9470600002013810,0xcad1191a03648b13,0x849a32487cb79134])) : Bits)
  | _ => 0
def samplesQ118 : Nat → Bits
  | 1 => (OfNat.ofNat (limbs [0x2291890,0xc080899a21102430,0x5513a04284b0e20a,0x2050085e0ccb1084]))
  | 2 => (OfNat.ofNat (limbs [0x705a01,0x8211f0982440544,0x14552a900815b090,0x908110c6298da012]))
  | 4 => (OfNat.ofNat (limbs [0x960309,0x1106066518014946,0x28444d05104f1404,0x40a5680b134e420]))
  | 5 => (OfNat.ofNat (limbs [0x40c8198,0x220820f604881832,0x6902c42061ea4901,0x41200e1894725108]))
  | 6 => ~~~((OfNat.ofNat (limbs [0xeffdfff,0xfbafbfffbfdd7fff,0xfffffff7fdffff9f,0xf5fb7ffffffff5be])) : Bits)
  | _ => 0
def compactPerms118 : Array (List Nat) := ([[], [82], [33, 84], [33, 66, 84], [65], [65, 82], [81, 82, 84], [81, 66]] : List (List Nat)).toArray
def compactDomains118 : Array (Sig × Nat) := ([(subcube 2 0, 5), (subcube 4 0, 5), (subcube 16 0, 5), (subcube 32 0, 5), (subcube 18 0, 4), (subcube 36 0, 4)] : List (Sig × Nat)).toArray
def compactWords118 : Nat → Nat
  | 0 => (OfNat.ofNat (limbs [0x3dda25a3a7f801,0x1efeb53807c9fd39,0x22c13b4a319a226e,0x853930267df79c04,0xa11186a95a10cec5,0xeadfe0ff07f83fc1,0xfe0ff0486000a181,0x2f3736e61d984261,0x252200a50c020522,0x89cfb96bea7955,0x97f807009fe03fc0,0x60a9c65e0882b56a,0xd2b779c683dda581,0x49c86c228f3924ec,0x7884430c4bca1e43,0xff01fe03fc00b8a3,0x13ec0e4e5a569ca1,0x91bf17fc00d0c884,0xd4ced290de4d5c95,0xa25a543ff8087345,0xece9474a3de204ea,0x9e70bf106b624fc9,0x68587f8091823333,0xfc013bfff01fe03d,0x9bf1cba040000002,0xa04000c06cd0a14,0xa13060c920192140,0x991900dff76effef,0xd7efdfbf250b944e,0x513942e500808652,0x1148252014900880,0x8802c958527737fc,0x10d7343ff80e977d,0x1ff07f8079ffe0ff,0x239b3a6022d34a0,0x4133551008321403,0x124098325401ffff,0xe0110110068ae11f]))
  | _ => 0
def compactCount118 (k : Nat) : Nat := match k with
  | 7 => 1
  | 6 => 3
  | 5 => 10
  | 4 => 3
  | _ => 0
def compactPath118 (k : Nat) (i : Nat) : Nat := match k with
  | 7 => 0
  | 6 => readCompactBits compactWords118 (26 + 12*i) 12
  | 5 => let v := readCompactBits compactWords118 (469 + 14*i) 14
    (readCompactBits compactWords118 (433 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | 4 => let v := readCompactBits compactWords118 (1919 + 14*i) 14
    (readCompactBits compactWords118 (1847 + 24*(v >>> 12)) 24) ||| ((v &&& 4095) <<< 24)
  | _ => 0
def compactLive118 (k : Nat) (i : Nat) : Nat := match k with
  | 7 => readCompactBits compactWords118 (0 + 5*i) 5
  | 6 => readCompactBits compactWords118 (62 + 6*i) 6
  | 5 => readCompactBits compactWords118 (609 + 7*i) 7
  | 4 => readCompactBits compactWords118 (1961 + 8*i) 8
  | _ => 0
def compactPoolIDs118 (k : Nat) (i : Nat) : List Nat := match k with
  | 7 => let v := readCompactBits compactWords118 (20 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords118 (5 + 3*(v &&& 7)) (3*n)
    compactIDsFromBits bits 3 n
  | 6 => let v := readCompactBits compactWords118 (156 + 9*i) 9
    let n := v >>> 5
    let bits := readCompactBits compactWords118 (80 + 4*(v &&& 31)) (4*n)
    compactIDsFromBits bits 4 n
  | 5 => let v := readCompactBits compactWords118 (727 + 7*i) 7
    let n := v >>> 4
    let bits := readCompactBits compactWords118 (679 + 4*(v &&& 15)) (4*n)
    compactIDsFromBits bits 4 n
  | 4 => let v := readCompactBits compactWords118 (1985 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords118 (1985 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []
def compactBucket118 (k : Nat) (i : Nat) : List Nat := match k with
  | 6 => let d := readCompactBits compactWords118 (183 + 4*(i % 4)) 4
    let off := ((i/4 + d) % 18)
    let v := readCompactBits compactWords118 (199 + 13*off) 13
    if v >>> 5 == (i/104729)%251 then [v &&& 31] else []
  | 5 => let d := readCompactBits compactWords118 (797 + 5*(i % 18)) 5
    let off := ((i/18 + d) % 64)
    let v := readCompactBits compactWords118 (887 + 15*off) 15
    if v >>> 7 == (i/104729)%251 then [v &&& 127] else []
  | 4 => let d := readCompactBits compactWords118 (1991 + 4*(i % 8)) 4
    let off := ((i/8 + d) % 31)
    let v := readCompactBits compactWords118 (2023 + 13*off) 13
    if v >>> 5 == (i/104729)%251 then [v &&& 31] else []
  | _ => []
def samplesP57 : Nat → Bits
  | 0 => 0xbffd3b7dedcc78e
  | 3 => ~~~(0x8103241258c788 : Bits)
  | 4 => ~~~(0x14286d5408da2e6 : Bits)
  | 5 => 0xdbfa64773e9aee0
  | _ => 0
def samplesQ57 : Nat → Bits
  | 0 => 0x40408404440008a
  | 3 => ~~~(0xf77fdded7ffffda : Bits)
  | 4 => 0x162448691095d10
  | 5 => 0x252411a02a95e40
  | _ => 0
def compactPerms57 : Array (List Nat) := ([[], [48], [84], [84, 48]] : List (List Nat)).toArray
def compactDomains57 : Array (Sig × Nat) := ([(subcube 16 0, 4)] : List (Sig × Nat)).toArray
def compactWords57 : Nat → Nat
  | 0 => 0x4f
  | _ => 0
def compactCount57 (k : Nat) : Nat := match k with
  | 4 => 1
  | _ => 0
def compactPath57 (k : Nat) (i : Nat) : Nat := match k with
  | 4 => 0
  | _ => 0
def compactLive57 (k : Nat) (i : Nat) : Nat := match k with
  | 4 => readCompactBits compactWords57 (0 + 4*i) 4
  | _ => 0
def compactPoolIDs57 (k : Nat) (i : Nat) : List Nat := match k with
  | 4 => let v := readCompactBits compactWords57 (5 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords57 (4 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []
def compactBucket57 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []
def samplesP115 : Nat → Bits
  | 0 => (OfNat.ofNat (limbs [0x6efe,0xffad617e97be7f7d,0xe5e68eb0b14f6d38,0xfbd878c21f49e5c4]))
  | 1 => ~~~((OfNat.ofNat (limbs [0x580,0x162511e3d824012e,0xe4822cf6bbcc0111,0x55c94ad39f82afd6])) : Bits)
  | 4 => ~~~((OfNat.ofNat (limbs [0x2040,0x91d4217a0180c05,0x13c609f0c7984424,0xca4e3677172973e2])) : Bits)
  | 5 => (OfNat.ofNat (limbs [0x773f,0x5f75db91077fbdef,0xd2cb29c08386fcc5,0xd4cff253143fa302]))
  | 6 => (OfNat.ofNat (limbs [0x7dff,0xbfdf16e7effdcfb6,0x3f967d764e9dd737,0x4f6f063583a25af2]))
  | _ => 0
def samplesQ115 : Nat → Bits
  | 0 => (OfNat.ofNat (limbs [0x1121,0x210848109200854,0x4601104808130500,0x8850408425414184]))
  | 1 => ~~~((OfNat.ofNat (limbs [0x7a7a,0x6dfeeebe24eeddf3,0xb8ec4f5bdf7ca35d,0xdffbdb61da92bfde])) : Bits)
  | 4 => (OfNat.ofNat (limbs [0x2048,0x884021624424101,0x8a00500430ca209,0x1100834088128c08]))
  | 5 => (OfNat.ofNat (limbs [0x8c2,0x988a2022f6089029,0x9b2a5121424f840,0x4482175a883ea002]))
  | 6 => (OfNat.ofNat (limbs [0x210,0x20480800840480,0x180400014,0x229000000001250]))
  | _ => 0
def compactPerms115 : Array (List Nat) := ([[], [81, 64]] : List (List Nat)).toArray
def compactDomains115 : Array (Sig × Nat) := ([(subcube 1 0, 5), (subcube 2 0, 5), (subcube 16 0, 5), (subcube 32 0, 5)] : List (Sig × Nat)).toArray
def compactWords115 : Nat → Nat
  | 0 => 0x41c9f
  | _ => 0
def compactCount115 (k : Nat) : Nat := match k with
  | 6 => 1
  | _ => 0
def compactPath115 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => 0
  | _ => 0
def compactLive115 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => readCompactBits compactWords115 (0 + 5*i) 5
  | _ => 0
def compactPoolIDs115 (k : Nat) (i : Nat) : List Nat := match k with
  | 6 => let v := readCompactBits compactWords115 (13 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords115 (5 + 2*(v &&& 7)) (2*n)
    compactIDsFromBits bits 2 n
  | _ => []
def compactBucket115 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []
def samplesP87 : Nat → Bits
  | 0 => (OfNat.ofNat (limbs [0x6ecfbfd695,0xf6237fdfe5b4e6c,0xf1ab101967fdd3e3,0xf62ec71046793388]))
  | 1 => (OfNat.ofNat (limbs [0x774fd9fd29,0xd3b447cefbfdb717,0x2673ab6009defd3d,0x9875702ba876a854]))
  | 2 => ~~~((OfNat.ofNat (limbs [0x21d0191091,0xdb3ef8048209866c,0x2733bf7dee080b69,0x9434473bef902ffc])) : Bits)
  | 4 => (OfNat.ofNat (limbs [0x7dbfff3df6,0xff1a8fbfc7ffccfe,0xf5f0f54e5bb7afd,0x5dfcf01e9b3d63c]))
  | 6 => ~~~((OfNat.ofNat (limbs [0x400000524,0x712000840504c16,0x4b0b50649050b5,0x4fc701e833921c])) : Bits)
  | _ => 0
def samplesQ87 : Nat → Bits
  | 0 => (OfNat.ofNat (limbs [0x1132441912,0xb091ca81a063438f,0x115068451d5d1606,0x822cc11872792108]))
  | 1 => (OfNat.ofNat (limbs [0x8b4070a54,0x380b1b43c028cd0a,0x10b47453058cb50d,0xa21c10e2a74a044]))
  | 2 => (OfNat.ofNat (limbs [0x21d14b5091,0x721ef5a191309ea5,0x43e5e249c5f3e414,0x4322e256d8efd002]))
  | 4 => (OfNat.ofNat (limbs [0x248084008,0x64240806041020,0x420100a0022248a0,0x4400a4080825610]))
  | 6 => ~~~((OfNat.ofNat (limbs [0x7bff7fffdf,0xfaffffebf77fffff,0xfffffeffdfffffbf,0xcf6feffffffff75e])) : Bits)
  | _ => 0
def compactPerms87 : Array (List Nat) := ([[], [16]] : List (List Nat)).toArray
def compactDomains87 : Array (Sig × Nat) := ([(subcube 1 0, 5)] : List (Sig × Nat)).toArray
def compactWords87 : Nat → Nat
  | 0 => 0x9f
  | _ => 0
def compactCount87 (k : Nat) : Nat := match k with
  | 5 => 1
  | _ => 0
def compactPath87 (k : Nat) (i : Nat) : Nat := match k with
  | 5 => 0
  | _ => 0
def compactLive87 (k : Nat) (i : Nat) : Nat := match k with
  | 5 => readCompactBits compactWords87 (0 + 5*i) 5
  | _ => 0
def compactPoolIDs87 (k : Nat) (i : Nat) : List Nat := match k with
  | 5 => let v := readCompactBits compactWords87 (6 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords87 (5 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []
def compactBucket87 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []
def samplesP55 : Nat → Bits
  | 0 => (OfNat.ofNat (limbs [0x5edfbff5d1d176,0x7fffcfbe6cfd8bd8,0xe89c2ecf6def1b4e,0xdc4f9d9155e28be4]))
  | 1 => ~~~((OfNat.ofNat (limbs [0x8b01300738546,0xf800882269cda38c,0xc4853fd901409247,0x54c67dd3764893f6])) : Bits)
  | 2 => (OfNat.ofNat (limbs [0x7c3ff37bef84cc,0x87efb9efdbc2f7ac,0x45e11117bfdb96f3,0x37d2604223d9b512]))
  | 4 => ~~~((OfNat.ofNat (limbs [0x44020600440e4,0xb006000c06a09368,0x6065339024820372,0x8213e4d267520cb2])) : Bits)
  | 5 => (OfNat.ofNat (limbs [0x6fefffee766fe6,0xb7f6fe7fe7adb36f,0xf6653395f7f6e377,0xc2b7e4d2675e5eb2]))
  | _ => 0
def samplesQ55 : Nat → Bits
  | 0 => (OfNat.ofNat (limbs [0x212142061a2681,0x829411304f011c08,0x9102431c4d030382,0x985c050385e08824]))
  | 1 => ~~~((OfNat.ofNat (limbs [0x774bfc7c8ef8fb,0x24ceebf695ac5bf7,0x81fba5e18b6abf55,0x7ea6fe8f704d93fe])) : Bits)
  | 2 => (OfNat.ofNat (limbs [0x3c0c5a4104e13,0x7592308245541901,0xe728e25f0b9a04c3,0x86582c4709d1b102]))
  | 4 => (OfNat.ofNat (limbs [0x4482430040060,0x2448c04010a401b1,0x29008182681804,0x20a02a84300d1348]))
  | 5 => (OfNat.ofNat (limbs [0x10122011409008,0x8600a04b0a2a0b0,0x8000420b064a010,0x400282b0320e4690]))
  | _ => 0
def compactPerms55 : Array (List Nat) := ([[], [33, 84]] : List (List Nat)).toArray
def compactDomains55 : Array (Sig × Nat) := ([] : List (Sig × Nat)).toArray
def compactWords55 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def compactCount55 (k : Nat) : Nat := match k with
  | 4 => 1
  | _ => 0
def compactPath55 (k : Nat) (i : Nat) : Nat := match k with
  | 4 => 0
  | _ => 0
def compactLive55 (k : Nat) (i : Nat) : Nat := match k with
  | 4 => readCompactBits compactWords55 (0 + 5*i) 5
  | _ => 0
def compactPoolIDs55 (k : Nat) (i : Nat) : List Nat := match k with
  | 4 => let v := readCompactBits compactWords55 (5 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords55 (5 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []
def compactBucket55 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []
def samplesP51 : Nat → Bits
  | 0 => 0xbfff3bb9fbda7afa
  | 1 => ~~~(0x142c0b80325a707a : Bits)
  | 4 => ~~~(0x8120880818a52a8 : Bits)
  | 5 => 0xdbfec8beb78a57e8
  | _ => 0
def samplesQ51 : Nat → Bits
  | 0 => 0x404444208a10988a
  | 1 => ~~~(0xeadb95d3bee9647e : Bits)
  | 4 => 0xa11009124282454
  | 5 => 0x24b1215a10ae2760
  | _ => 0
def compactPerms51 : Array (List Nat) := ([[], [81, 64]] : List (List Nat)).toArray
def compactDomains51 : Array (Sig × Nat) := ([] : List (Sig × Nat)).toArray
def compactWords51 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def compactCount51 (k : Nat) : Nat := match k with
  | 3 => 1
  | _ => 0
def compactPath51 (k : Nat) (i : Nat) : Nat := match k with
  | 3 => 0
  | _ => 0
def compactLive51 (k : Nat) (i : Nat) : Nat := match k with
  | 3 => readCompactBits compactWords51 (0 + 4*i) 4
  | _ => 0
def compactPoolIDs51 (k : Nat) (i : Nat) : List Nat := match k with
  | 3 => let v := readCompactBits compactWords51 (4 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords51 (4 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []
def compactBucket51 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []
def samplesP119 : Nat → Bits
  | 0 => (OfNat.ofNat (limbs [0xdedbfeffd7d725e,0xd3d4aaaa4fdfe7ff,0x2ff6da9eebfe7d17,0xdc66b809bb0208a7,0xd4f093154eff7bbf,0xa99ffa3b5eeb8bf4,0xe4c97a6614bd98cf,0xa832c8d0c019e095,0xfddec9f66789592,0xe75ecb7809c65522,0x2054d3f0509e5620]))
  | 1 => (OfNat.ofNat (limbs [0xf66bfdb3feee587,0xf4e2702c8fee7bfd,0xf7ef5d6d78f9b7b8,0xe98161e44f1bb540,0xf92900220ffeffd5,0x7cf3cbf5bf3e1dcb,0x58666700cbc8f332,0x3b0f23ea21a20200,0x53e6deedbf7b70eb,0x1c4b06a3c7362209,0x932103adeca90144]))
  | 2 => ~~~((OfNat.ofNat (limbs [0x403c003210c1203,0x66df79a8f0082201,0x3035c0e602e4410,0x89e1b8ad0f9b3c75,0xd63dbff7e2102001,0x85992c11c230d10,0x6f407a469d8cb23b,0x3bab88fbefbbf3dd,0x5c0884242852f1ce,0x466a8bb195867f2f,0xbf75dc25499bf7ec])) : Bits)
  | 4 => (OfNat.ofNat (limbs [0xfdb7ff7e7c6bf79,0xefcf49d31ff9ffc7,0xffe9ff9fc51fc7d9,0x5bf0ce6a35fd2e57,0x5a1ca0412ff7ef6b,0xaf5877cfbb0b773f,0xfb913cc76cc11638,0x5fad4cc027a19045,0x4adb9d72fbcee5ad,0x6a0bce87d885301,0x7650ca33f54c0e4]))
  | 5 => (OfNat.ofNat (limbs [0xef3ffbffb99dee7,0x2ffb1d30effffefb,0xff1fbe7276e6ce66,0xb7f991978edc79b8,0xa6520d848fb9fdf9,0x52efb7c65cf5fff3,0xa778d878b336ec3d,0x34c89331181c413a,0x21baf3fe38f46a56,0xdba80917b6c78c34,0x2898a24f4bb23818]))
  | 6 => ~~~((OfNat.ofNat (limbs [0x4000800000e444,0x81c20832000040c0,0x240c9a1040d08700,0x5030c142bf5c2982,0xf85a810504a04901,0x208263061a0813e3,0xb0f97c6062f1dc3c,0x3c0c43d031bdc037,0x68d2d8da326c64b3,0x9f880c6a6fc7d731,0x23fda2eb7eb65874])) : Bits)
  | _ => 0
def samplesQ119 : Nat → Bits
  | 0 => (OfNat.ofNat (limbs [0x212601081808321,0xc2a4511b2980620,0x30890300b4004638,0x449c01e04252350,0x50a6420a88c62a1,0x1b8080447008b04,0xc4f003c017c00908,0x90650007202050a0,0xbb84ac9140398013,0x214843600b800502,0x80e293f010881420]))
  | 1 => (OfNat.ofNat (limbs [0x994220e0c10a50,0xe1d0ed33b041684,0x12136612d9094b48,0x1414841d20842a4c,0x446c6c579b63595,0x531408411128882,0xaca1a560254a2a05,0xbc9b241684254888,0x2be0d68d1d595009,0x150942014b042115,0xf021b3accca80104]))
  | 2 => (OfNat.ofNat (limbs [0x403d01169041202,0x2c9359a8f5810610,0x945a2d34654a1432,0xc0889c08162660,0x461da9b4cd6b4273,0x413201248188c820,0x89532a8a1292215c,0x257e054e093060c4,0x2bd52a58d7a10821,0x8198620a0b209452,0x51c307d8b6440012]))
  | 4 => (OfNat.ofNat (limbs [0x2484090c180084,0x1000b02c44604103,0x4082502721003,0x2880110040005080,0x80a1191a06418848,0x2240220900011008,0x110a480b08155050,0x100196010420110,0x41b0162a2820484,0x200840024089a60,0x50c04032354c040]))
  | 5 => (OfNat.ofNat (limbs [0x10c012804622008,0x4004a24608420840,0x90440030a310941,0x3802222011008001,0x800124b12109d08,0x4844208040051,0x3008c421280d5201,0x880382042008600,0x402a512628442000,0x4820080480422a25,0x240c200749320808]))
  | 6 => ~~~((OfNat.ofNat (limbs [0xfbff7ffffffbbff,0x7ebfffffffff5ff7,0xbfdfffffffffffff,0xffdfffbf7db7fffd,0xcfffffffffffffff,0x67ffefefdf9fdbff,0xffffffffffffffff,0xffffffffff77fffc,0xfffffffffffffcbf,0xfff9ef6fefefffff,0xfffffffffffedd7e])) : Bits)
  | _ => 0
def compactPerms119 : Array (List Nat) := ([[], [33, 84]] : List (List Nat)).toArray
def compactDomains119 : Array (Sig × Nat) := ([(subcube 1 0, 8), (subcube 2 0, 7), (subcube 4 0, 7), (subcube 16 0, 6), (subcube 32 0, 6), (subcube 64 0, 5), (subcube 6 0, 5), (subcube 17 0, 5), (subcube 18 0, 5), (subcube 20 0, 5), (subcube 34 0, 5), (subcube 36 0, 5), (subcube 66 0, 4), (subcube 68 0, 4), (subcube 19 0, 4), (subcube 22 0, 4), (subcube 38 0, 4)] : List (Sig × Nat)).toArray
def compactWords119 : Nat → Nat
  | 0 => (OfNat.ofNat (limbs [0xffef7ffffdfdfdfd,0xefbfffffbffffffd,0xfffdfffdfffdfffd,0xfffdfdffffffbdfd,0xffbd7dfd7fffffbf,0xddfdffbfffffbfed,0xfdffedffffffbfed,0xfdfdffedfdfee42e,0xa626642e632e4626,0x26262626261e2616,0x260be42bc42ba42b,0xe623e623c623a623,0x8623e61be61be613,0xe613a613e60be60b,0xe60be60ba60b8608,0xe428a428a328c628,0xc620a620a620a610,0xa608a604a42cc32c,0xa32ca32ca624a624,0xa61ca61ca612242a,0x432a232a232a222a,0x66222622661a261a,0x66122612660da42d,0xc32da32dc62da62d,0xa61da60b632b432b,0x232b232b412b212b,0x662b662b462b462b,0x262b262b062b062b,0x660b660b26084628,0x262d442d242d232d,0x462d262d23254625,0x26252622c42aa42a,0xa32aa22ac62aa62a,0xa324442c242c232c,0x412c462c262c2124,0x2621c429a429a329,0xa129c629a629a621,0x21294629262e32c3,0x2c32421c12c11a32,0xa32221a12a11a110,0x328323b22a365e22,0x66d1d15b0f25c581,0xc9ffc1e75624deeb,0xfc12242c8ff82cd7,0xfe0957ff83fc1c16,0x773770575d612c09,0xff8042ffe0461bc6,0x400980030048fcab,0x44609af92f1fc37a,0x5ae9a0f397721022,0x10209262823441,0x4e4f64482006727,0xc482094094447079,0x620291368630790,0x6202913606201855,0x25c48b5082024e4f,0x884035ca2a22c201,0x4a2822c20945e450,0x12188c8a102638bc,0x6083cc1147ffffff,0xffffffffffffffff,0xffc6586546506582,0x5425864464064843,0x443823423422c93f]))
  | 1 => (OfNat.ofNat (limbs [0xe641a20a08199e6,0x81002e67c618828,0x71a718620a188286,0x1020099a45269222,0x651019a88199829,0xe12620206679a9a4,0x11e18a0a5a881000,0x9f9a40ea94b9a55c,0xbae6418902519a9f,0x9a42491c42489c71,0xa49198688848408,0x291993ae8409989,0xae810200a4e640a4,0xeba1198a4e846629,0x3ae640a4ea46838a,0x994a1018b9c608a4,0x1e2e642620a28600,0x40c79a11a818a20a,0x1000c799e6881808,0xa0e67c662718809,0x878b9901c6602606,0x9f9c661b1840861,0x60284799898850,0x810060319f998190,0x7a60200c79983189,0x9a12201199a28699,0x45e62462891a4206,0x10200a5e65061020,0x179942222eba0408,0x4919975ea566224,0x2904e618a2242862,0x6a90a18998890608,0xa224198288184080,0x20798a6820666269,0x2228408198a9a488,0x620409a60620198a,0x18290a50400399e9,0x1050290408048999,0x102012266408286,0x2041c86e64081020,0xb26640810204999,0x4461e65901e9209,0x9962e81020499912,0x684662922122859c,0x879aa8a7e6192202,0xb99e68800399e5,0xab1862047e720228,0x62260860926071e6,0xd79ca20400a0c64,0xe62040039931d656,0x624a50ba840031e6,0x48a40899018a7839,0xc661e2e619024601,0xf98a64620401f98a,0x50404799ea182a19,0x8521f2460207e628,0x81986808667ffdff,0xffbffffdfdfdfdff,0xfffffffdffffffff,0xffbffdfffffdffed,0xefffefffffbdfd7d,0xfd7dddedf7fefffe,0xfffdfffdfdfffeff,0xfefffdfffdfffdff]))
  | 2 => (OfNat.ofNat (limbs [0x1611eb25c87158a4,0x4a420b5320c21852,0x3459e764d7912c36,0xe48b3785480df770,0x90123bf408eff007,0x1a7021be0e0f5316,0x9eada1eff00df35a,0x33fff0005381c719,0x3906997ff00870f0,0x3c06763ff0064a91,0xe1ff00394c5842e,0x8d3b255ff003c2bc,0x32921283109a8721,0xea20c2669dfff003,0x9dbff00efecad32d,0x81aa803780ecbadf,0xf00ff00b6b447a8f,0xf00ff009025b2b85,0x18c3f92b85f6fe47,0x1640f980469ad41f,0xf00911156aec02c9,0xc65501778afff00a,0xeb223bbe1841603,0x9b197274d683b9d8,0xd361d748fbdbf3eb,0x81510a12bc4c782a,0xbd221a6151000500,0x282803648d000c14,0x58b100008f0c8410,0x401016061010b1,0x80c0822a08100000,0x8083060008b00040,0x404181882000100,0x30389081c30406,0x142860408214f913,0xa14e4b3694d67343,0x4c512d3ca6f261c9,0x2723248471fbc705,0x1b24645180c5ed14,0xa44ab102c3690bc4,0x1eb052c0a900b3f6,0x8fbabe4af6cbc8ce,0xf53a8ce72b92ae23,0x37c6ddbb684d9235,0xc6d5c3468cfc32f4,0xc6ab10ac1a2fecbc,0xaae90b622d10b01a,0xbb0aaaaa0aa5ba88,0x6a09a7d09b3a5f69,0x22a3ee8c122c8893,0x218a83a20668031f,0x427ca9e887821d8c,0x7349ba66d41a4867,0x398ee60197a65d21,0x6d057394ea513139,0x249a11e4469116a4,0x338fec3cb0e72351,0x8ce831b0ba82cc0a,0x2e25288b21e10746,0x1bb062c15b04ae0f,0x382f007b81100006,0x209a840804e640a2,0x1240798a28898828,0x200420b9a2204012]))
  | 3 => (OfNat.ofNat (limbs [0x8438c58238c54648,0xc54438c54238c446,0x5885843885823885,0x4438854238658648,0x6546482582382546,0x44c58644c58434c5,0x8234c54644c54434,0xc54234c4c654c486,0x54c48434c48254c4,0x8234c44654c44254,0xc44234c40654c382,0x54c34254c24654c2,0x654c18644c10654,0xc006548586448584,0x3485825485823485,0x4434854254854234,0x8506546586446584,0x3465825465823465,0x4644654434654254,0x6542346506546484,0x3464443445443425,0x4644254234254224,0x248230c54640c446,0x50c1465874f032a3,0x6c72c3c069bda14e,0x2b6d1ef253ae2349,0xfc8ff00e2e57caa9,0x49999c1ba1fcd81f,0xf0007130a844e912,0x35b43b3aee2e266d,0xe4b493d2343c6479,0xbe70967ff00ff00f,0xf0086ba0bde8e57b,0x8acf10471ce800af,0xf00ecb01173b3bec,0x421778fff003e936,0x4377f1c74edff001,0x8519ccf66abff000,0xc20565e977e31e66,0xba3ef9655dcff009,0xb7b0e076e9fbd19f,0xf00de33704dff00f,0xf00266d14d0b939a,0xf5d05e36708ff002,0x597a2d5bd7009cb,0x9c9a28b6d8919bba,0x510c69a9d8378750,0x71679ccff0063d5d,0xd062ba0ff00ff005,0x7c2c9dd7322bac5c,0xcb7ed2ec37fff00f,0xf00ff003a23477df,0xf00ff009a49ff00a,0x8b9706269953c9e6,0x670ff00d1bcff00a,0x1cac3d87a05f4da8,0x42f937cff00ff001,0x11256e9eb0b53d15,0xa94ad6f0624a4a58,0x7cdccd94c6ed48d7,0x6c6ff00eecb7de8f,0xf009e6a2653cd0d6,0xa6bdb88a84aec409,0xa1d5930f6d4397a5]))
  | 4 => (OfNat.ofNat (limbs [0x990b122162242c48,0x65899c9123922272,0x440e4899c71338a2,0x27100cc400988013,0x800473414e6279c4,0x4f39856708ace615,0x9cc891951232a2ce,0x53d90a79214f2329,0xcc853890a71194de,0x429b485368ca6338,0x88670a7ce24f9c69,0xf3893e7121ce4439,0xc2573886670c84e3,0x499c493386327220,0xce1848cb09392127,0x19ace2359ccd1390,0x967212ce17e8cac2,0x19582329d4853b0c,0xa751960642c08e66,0x69c63b38476428e4,0x851d9c8383907671,0xece11c1c2383998,0xa32b14e4629c6c63,0x998a73064650d9c7,0x291965432ca46594,0x9c2f3315e271bc4e,0x6789c6b738d6e70a,0xdce05b9cab738d6e,0x71adce15b9c2b738,0x56870adce05b9c00,0x91941262824e1049,0xc00a3981232824e1,0x49c10d2161a32c3,0x825879cb0d395c27,0x1b84e6339c467398,0x8e7211ce17c9c8bf,0x3904a42894c5139c,0xa253954442a84855,0x8caa33954272a84,0x65519caa23954272,0xa80e56c9c6d9389b,0x27316ce22d9cc373,0x906e710dce10f10a,0x1d2143a32bb4e459,0x9c8b33896670acce,0x11090a2111442628,0x8ce5109ca23389ba,0x71b74e62f9c45f38,0x4be730fce1648cac,0x91959272324e3649,0xccf53917412aece4,0x5d9c20d2141a3283,0x4c5071ca99215323,0x2a6ce54c9cad538d,0xaa70b54e6299c453,0x3985e70854650a8c,0xae93915e722bce15,0x79c28d2151a32a34,0x25479ca8d3951e70,0x84445cc5464cc446,0x5cc4425cc3465cc3,0x425cc2465cc1465c,0xc1464cc1425c8506,0x5c654648c58648c5]))
  | 5 => (OfNat.ofNat (limbs [0x2481006acc5334a4,0x83356acd2884ad59,0x8a19e47b31ccc1c8,0xcf992040420477ee,0x20988eed7b886a1c,0x4231004082cfdc2a,0x3020010800140851,0x4993002fb84144,0x8904ac102b5ac101,0x842428512ac4c184,0x400904004800202,0x800003b81ee1b,0xb800bdc28d195890,0x4092020204101034,0x80c182ee21224062,0xd2346608181060b4,0x20a0c10003dd215,0x4610124028c60110,0x304778a084040229,0xa834608001060d18,0x506047858a0c401e,0xe080770a14282000,0x101d7def6f3fddc,0xef773fd7cfe7fafb,0xbdf6ef7bbedfb5f7,0x79fdf67fbddeef77,0xbf5faef77bbddeef,0x77bbddeef77bbdde,0xef77bbdbe5f67f7b,0x9ffd76f37dbe9f5f,0xbbddecf7bbddaefb,0x7db6bdf76f73fddc,0xee7fbdbdf767f7bb,0xecfefbddbedf7d7a,0xfb7dbefb9fcfe7f5,0xbbddef9eef77bef9,0xfcfe7f3ddfebf5db,0xf5edf779fcffaf77,0xebe7f3f3fcfdde7f,0x3fbbdf6fd9f9fede,0x7fbd9eef77d3eebe,0x7efb7e9fe7e7b3ed,0x7edf7b3f9fdde7f7,0xb9fddfeb3f9ff9f6,0xf77bbebf5fb79fcf,0xf4fafd7ebf5f77bd,0xcfef73fbbfcfebdb,0xedfce7f3fddef67b,0xe7f9edeef77f9dde,0x7f7bbecffebf5ead,0xf7ebbd9fef67fbdf,0x6fd77b7dd7ede7f3,0xfbbdf67f7b9ffd7e,0xbd59fcff7b3dd7ed,0xf7b3f9fef7f2ab21,0x54e7129c65539c4a,0x73894e71290e2539,0xc3272164a71494e1,0x73988e538dca70a5,0xce34b9c4973852e7,0x14c48e9c915390,0xfe70c44e48998912,0x3122262440c48998,0x71338e2661444c28]))
  | 6 => (OfNat.ofNat (limbs [0x6011a11f7f8008d7,0xbfe00be211a5323d,0xc5fe00032c5737d9,0xc1fe00f915ff803,0xfc00402cff007f80,0x1478b98eb1cc97f8,0x3fc01fe0000256a,0x4120081426045230,0x30cc800005b20a0,0x1186328c0870e558,0x87000c6a20204020,0x36181834c040a400,0x800e005c7000600,0x1000000580060010,0x2020c3800045c850,0x604022020870000d,0x819000480800c08d,0x8f62381090a08403,0x48141842a2c58000,0x2c380120220b060c,0xb80044c00f0a34c8,0x1089c68020480020,0xe0040100043000c2,0xc6b8d71ae35ceb1d,0x51aa7506a0d43a63,0x4d68acf39c339660,0xcc198330662ca590,0x320643c518a71161,0xc2382304609c018,0x300602be37a6f05,0xe0bc376ae7599b23,0x632b5558ab354aa0,0x542a614c298d2aa3,0x146689500a033ea7,0x44eb9a134664cc29,0x612c2584b2943262,0x4cc919151ea3446b,0x8a312224c4088110,0x2204418750a610c1,0x883304a004027eaf,0x21e43c9782ee5d8b,0xa9746e25c03826e2,0xda5b03606c2d61ac,0x35a696cc594b2064,0xc858c319620c498,0xafa5d2b81702e05,0xc0b856c2d85b4b29,0x5cab1550aa5502a0,0x542a6549280500a0,0x53c2784f29c138a6,0x94c494128a494848,0xc118a2944a7e4f89,0xe93c2760ec9d03a2,0x720e49c33506a0d4,0x9a1332644c49822e,0x5c4b49612b0560a,0xc1582b65049d9202,0x424608c911210420,0x850f91e03c0790e1,0x1b0368648c11702e,0x5c0ba15625c2c85,0xa2124208390620,0xa015019024000bb8,0x4082801202000920]))
  | 7 => (OfNat.ofNat (limbs [0xdb132162e1e19954,0x8ae2682824655c13,0x3ec13048b3c478eb,0xdec8650933cf2591,0x9ebed92e1bc1c21c,0x33a73208cab335d7,0xd8f81bcc2696f8d5,0xe47f801b4ed0c0e9,0x21749050641ffe00,0x573441b6ec141b21,0x7ff004d0d6eddab5,0x69ff007f801438df,0xe00ff007f803fc01,0x24646474d7e8aea8,0xde8a62a12d3d96e5,0x2aacfaff007f800c,0xa6c460c043d7f803,0xfc0079977d00ee49,0xac69b3a2608d613b,0xfd1934dbaddf7774,0xc53fc00141bd8ba5,0x90875b01beaaafa0,0x13a861c535a27013,0x8426e4467264444,0x36286e3c55fa6c9f,0xf007f8012c2b932e,0xff0023e22aa9161a,0x589260ecf7ba37fe,0x13e3c865ab0748,0x16d965817213a568,0xac75ff004e67ade9,0x565358e2e554c4e5,0xd1a6d9139c80b451,0x7fc6078f32ff802,0x4125a97d89de4a8c,0x6671da98dff0070c,0x57fc01fe005ab07f,0x80144641ef2ff007,0xf801118274e6d094,0xd01f3fc007e1dff0,0x7f802ff65fe0030,0x107f8033b7561321,0x990ff800a4554110,0xff00038b4c27c2f0,0xc49b672d563a1685,0xaef74431469071e2,0xf9a2444b832c4159,0xfe00c97b5688c1da,0x6593895a841dd66f,0x9b795dc7c0e2cae7,0x9274b9b618035569,0xc8e7fe007233ff80,0x3a4a16da4e4b7ff8,0x253760725a8bcde,0xeaed605fe00d6317,0xf80389cb5b78c6b2,0x2841bfc00852a9bd,0x4c6d5148da9034c3,0x5c4a825e8f7fe000,0x76ea110f894922a9,0xccaca74286f066a3,0xa5b1d2c36adab71,0x858b3a7f801d8abf,0xe00c679fc69829c7]))
  | 8 => (OfNat.ofNat (limbs [0x34051b84e4fe01c5,0x5c6f6697afd708,0x74658499c3d9b1dc,0x82ff801356f1f990,0x62b1a5784b05fe00,0x8fb9ad84b0805fe0,0x58087f803a688c2,0xcaff002d476eb29f,0xe00deb3fb4ddc6fd,0xfe00ff003a700d6f,0x87d9357ac499772c,0x91fe00dee4e6f31a,0x77eeedcde61ff802,0x634327535d8fff80,0x3fc00284e27207b0,0xbc38829b1747143c,0x68e3a5fbf18cc9d3,0x7928b589a372761e,0x98a3a7f0cf2812a3,0xcb5bc15180bd1667,0x87d53a9f23d0ef5b,0x184b667ec4e0c98b,0x1c3ffb50d14a80dc,0xaf166ade77787660,0x4b8d2c8de472373b,0x6474342f2b4255ef,0xdf57e0041520fe8a,0x5ea78ecc3bd86010,0xc6bfc49352aa27d2,0x55cd44faf1b2e94e,0xfb696b9cc73ea397,0xae20e2d037d3595d,0x1e2944dd7f5706e5,0x516936cf299056f5,0xa4647f305c918fa1,0x3921e3cafad2724d,0xf7f800918bc07e02,0x4b6e22f76d443a04,0xc3924b69a4349a03,0xf2967f800a1210b4,0xb7dd9a4b3b4e385d,0xb7a622a3b1da29d9,0xbbf838f716ecab7,0xa2224e90623b364b,0xfd73b26b716ad658,0xb55a1e3d917f8001,0x49bacad0b7a14a36,0x5eb95c77ff007f80,0x1e9af1069411b9f1,0x24a5de8da740921a,0xed7c25aa63c324f6,0x272ebf2b2e247d28,0x9f8e4c6cc8c16d95,0xfdd5589a93fe00b3,0x5c82a50df61fe00f,0xf007f80308de9e0b,0x294542ea3a1a9335,0xf5588d6233fc01fe,0xaf7e7f803fc005,0x60a69c6145c2daa2,0x4a8f130cceaea98c,0xd8005f8c870ddcdc,0x3f88865353e7c12d,0xa60b680f2c279be7]))
  | 9 => (OfNat.ofNat (limbs [0x71dc7d5cd795cd73,0x5e56b5cd791ee799,0xe66b9af4b1df635c,0xe6b5d7691dcf31ef,0x5356ecb7a66b1dc7,0xd1f6739ce799e679,0x9e43faaead8f63b8,0xf679cad4fd2d4f55,0xd5756d5d1ef873cc,0x771dc7d1ec77cac7,0x71ec7d763284a00a,0x683c1a04f6813da0,0xae812ba0096813d,0xa04f68006a069e81,0x27a009e83af988ba,0x625f9c37e8097a02,0x8e8395a027e8113a,0xe768111a02fe813,0xba05628321a054a8,0x2019c802800b9c32,0x68149a013e805b9c,0x40e71579c35870d7,0xa035880ada0eca32,0xb08cac262b28cac2,0x32b0a0342329ba0c,0x6680d4a071e8108a,0x4228088a0136808,0xe90ad68139a05168,0x145a012e80b7a043,0x232c3a050e80c3a0,0x19cc8ca0cb9c4989,0xcb9c298a8c99c28,0xcb0c99c098a8c91c,0xa9890870ca9830c9,0x4b9828c89cd18a8,0xc89cd10a8869cd10,0xa8469cd04a8c89ca,0x9890869ca9890469,0xca9888469c99868c,0xa9c998684a9c9982,0x8ca9c998284a9c91,0x8b0469c918a8469c,0x904b0469c218a8c8,0x9c018a8c89c01828,0xca98a18a8c898998,0x28ca9881888ca988,0x1828ca90b9828ca9,0xa9840ca90a9830c,0x890a9820ca90a980,0xca90a8c90868ca9,0x890868ca9880ca8c,0xa9840ca8ca9820ca,0x8ca9800ca88a8c88,0x8684a9888461cc8c,0xa8c81ca9890861c9,0x9828ca1c49890ca1,0xc298a8c81c28ca8c,0x9fe00e773822c71a,0x829a6aff007f8024,0xb55586eb7b58d276,0xe43900a330027f80,0xa2edfe0077693e5,0xa0615029bde791d5,0xd3ee1997b3f5abd7]))
  | 10 => (OfNat.ofNat (limbs [0xff0ff00,0x61b552fb969307ff,0xe9aff0f84f385c3,0x67642000a710f21e,0x664c718e06910d28,0x7a4073926812502d,0x1ce04c5464506ce,0x14658645014e00c5,0x4645000e14654644,0xc44e00c14650b773,0x561d013d0389254e,0x531f42da42f3b7f0,0x27849705e12ff009,0xb28b375693c0f1ec,0x211955f931bb536c,0x718d788051f0a5c8,0xf84b30fe10a59585,0x280a55127854743f,0xf004a6fa715986b1,0x1dff005f6dff001,0xe6a460bff00823ac,0x201c589e2106a6e7,0x1392f598164ff001,0xb20c549226891535,0x766ff000e0483557,0x2093c245033c121f,0x1037873ff00ff00e,0x925ff00f406bf8be,0x40c4317f3727c1a8,0xd16ff005c5b1941f,0xf007362ff001182a,0x223ff00ff00073f3,0x13e8767ff00ff000,0xe52f645c57db2578,0x14eff00ff00c25e5,0xb60ee37ff008e2b5,0x10d0a7b9500ce05f,0xf006c8aff00387cd,0x34f9914a10743765,0x508625031357f5d2,0x30e5056b8029d5a8,0x78183830647e8222,0x8656269034dff00f,0xf00bd63ee30a36c0,0x771ff004e44632ab,0xc463d19077949860,0x74cd92c674a68329,0x3bda4b5e29b9875,0x548a33d2b74ff00a,0xa261027e37eff00c,0xb1c0c50052839875,0x8020e03c040b0c00,0x3800420117ce1c2,0x2810023800041402,0x4100538a5294a529,0x4a5294a52b242108,0x4210842108421092,0x1084210842108421,0x842108421084210,0xa0000000000000d3,0xe598a4999d7517ce]))
  | _ => 0
def compactCount119 (k : Nat) : Nat := match k with
  | 9 => 1
  | 8 => 14
  | 7 => 120
  | 6 => 231
  | 5 => 70
  | 4 => 6
  | _ => 0
def compactPath119 (k : Nat) (i : Nat) : Nat := match k with
  | 9 => 0
  | 8 => readCompactBits compactWords119 (16 + 12*i) 12
  | 7 => let v := readCompactBits compactWords119 (1683 + 16*i) 16
    (readCompactBits compactWords119 (1515 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | 6 => let v := readCompactBits compactWords119 (16684 + 19*i) 19
    (readCompactBits compactWords119 (14884 + 24*(v >>> 12)) 24) ||| ((v &&& 4095) <<< 24)
  | 5 => let v := readCompactBits compactWords119 (39037 + 18*i) 18
    (readCompactBits compactWords119 (37309 + 36*(v >>> 12)) 36) ||| ((v &&& 4095) <<< 36)
  | 4 => let v := readCompactBits compactWords119 (44484 + 15*i) 15
    (readCompactBits compactWords119 (44244 + 48*(v >>> 12)) 48) ||| ((v &&& 4095) <<< 48)
  | _ => 0
def compactLive119 (k : Nat) (i : Nat) : Nat := match k with
  | 9 => readCompactBits compactWords119 (0 + 6*i) 6
  | 8 => readCompactBits compactWords119 (184 + 7*i) 7
  | 7 => readCompactBits compactWords119 (3603 + 8*i) 8
  | 6 => readCompactBits compactWords119 (21073 + 9*i) 9
  | 5 => readCompactBits compactWords119 (40297 + 10*i) 10
  | 4 => readCompactBits compactWords119 (44574 + 11*i) 11
  | _ => 0
def compactPoolIDs119 (k : Nat) (i : Nat) : List Nat := match k with
  | 9 => let v := readCompactBits compactWords119 (12 + 4*i) 4
    let n := v >>> 2
    let bits := readCompactBits compactWords119 (6 + 2*(v &&& 3)) (2*n)
    compactIDsFromBits bits 2 n
  | 8 => let v := readCompactBits compactWords119 (887 + 11*i) 11
    let n := v >>> 7
    let bits := readCompactBits compactWords119 (282 + 5*(v &&& 127)) (5*n)
    compactIDsFromBits bits 5 n
  | 7 => let v := readCompactBits compactWords119 (8391 + 14*i) 14
    let n := v >>> 10
    let bits := readCompactBits compactWords119 (4563 + 6*(v &&& 1023)) (6*n)
    compactIDsFromBits bits 6 n
  | 6 => let v := readCompactBits compactWords119 (24657 + 11*i) 11
    let n := v >>> 8
    let bits := readCompactBits compactWords119 (23152 + 7*(v &&& 255)) (7*n)
    compactIDsFromBits bits 7 n
  | 5 => let v := readCompactBits compactWords119 (41032 + 5*i) 5
    let n := v >>> 3
    let bits := readCompactBits compactWords119 (40997 + 7*(v &&& 7)) (7*n)
    compactIDsFromBits bits 7 n
  | 4 => let v := readCompactBits compactWords119 (44640 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords119 (44640 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []
def compactBucket119 (k : Nat) (i : Nat) : List Nat := match k with
  | 8 => let d := readCompactBits compactWords119 (1041 + 5*(i % 9)) 5
    let off := ((i/9 + d) % 33)
    let v := readCompactBits compactWords119 (1086 + 13*off) 13
    if v >>> 5 == (i/104729)%251 then [v &&& 31] else []
  | 7 => let d := readCompactBits compactWords119 (10071 + 7*(i % 75)) 7
    let off := ((i/75 + d) % 268)
    let v := readCompactBits compactWords119 (10596 + 16*off) 16
    if v >>> 8 == (i/104729)%251 then [v &&& 255] else []
  | 6 => let d := readCompactBits compactWords119 (27198 + 7*(i % 150)) 7
    let off := ((i/150 + d) % 533)
    let v := readCompactBits compactWords119 (28248 + 17*off) 17
    if v >>> 9 == (i/104729)%251 then [v &&& 511] else []
  | 5 => let d := readCompactBits compactWords119 (41382 + 6*(i % 45)) 6
    let off := ((i/45 + d) % 162)
    let v := readCompactBits compactWords119 (41652 + 16*off) 16
    if v >>> 8 == (i/104729)%251 then [v &&& 255] else []
  | 4 => let d := readCompactBits compactWords119 (44652 + 2*(i % 4)) 2
    let off := ((i/4 + d) % 14)
    let v := readCompactBits compactWords119 (44660 + 12*off) 12
    if v >>> 4 == (i/104729)%251 then [v &&& 15] else []
  | _ => []
def samplesP79 : Nat → Bits
  | 0 => (OfNat.ofNat (limbs [0x76bbfaffbfbe03,0x847fffefd2d8d9c7,0x7fc39d601edfdbfd,0xd6898c1d0beb9d94]))
  | 1 => (OfNat.ofNat (limbs [0x7ac3ff2df20cf4,0x19fa8f7ffe71e69,0x9c8c20045fffad86,0x670ef062407dc640]))
  | 2 => ~~~((OfNat.ofNat (limbs [0x10dc1021b3aca6,0xd7e028c400741c67,0x5ccfbf77400a09f6,0x470e837f6b8587fc])) : Bits)
  | 3 => (OfNat.ofNat (limbs [0x5f57f7f3f1e3af,0x561f7fdc7ff4f5f7,0x507392531dfe7b72,0xdff8f192a5db83c]))
  | 6 => ~~~((OfNat.ofNat (limbs [0x2000200300201,0x40000005280d1c1,0x1003904004d40b00,0x4898c190a499814])) : Bits)
  | _ => 0
def samplesQ79 : Nat → Bits
  | 0 => (OfNat.ofNat (limbs [0x945151000219c,0x4a89182c03140b10,0xd2007030ca87172c,0x1201800706e28d04]))
  | 1 => (OfNat.ofNat (limbs [0x53c245708f60e,0x7c7c829d414567c2,0x47957ae13dcbaf82,0x3624252bc0fdc440]))
  | 2 => (OfNat.ofNat (limbs [0x10dc9903a1bc2c,0x97a7068f09982cf9,0x91cf71233b74df01,0x12646c04fe7a7802]))
  | 3 => (OfNat.ofNat (limbs [0x20aa0844869440,0xa15262813009402b,0x455040d34386840,0x9ac2528381d3030]))
  | 6 => ~~~((OfNat.ofNat (limbs [0x7dffbfffeffffe,0xfffffebf7bffffff,0xffff7fffffffffef,0x3fedeffffffffd76])) : Bits)
  | _ => 0
def compactPerms79 : Array (List Nat) := ([[], [48], [33], [33, 48]] : List (List Nat)).toArray
def compactDomains79 : Array (Sig × Nat) := ([(subcube 2 0, 5)] : List (Sig × Nat)).toArray
def compactWords79 : Nat → Nat
  | 0 => 0x9f
  | _ => 0
def compactCount79 (k : Nat) : Nat := match k with
  | 5 => 1
  | _ => 0
def compactPath79 (k : Nat) (i : Nat) : Nat := match k with
  | 5 => 0
  | _ => 0
def compactLive79 (k : Nat) (i : Nat) : Nat := match k with
  | 5 => readCompactBits compactWords79 (0 + 5*i) 5
  | _ => 0
def compactPoolIDs79 (k : Nat) (i : Nat) : List Nat := match k with
  | 5 => let v := readCompactBits compactWords79 (6 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords79 (5 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []
def compactBucket79 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []
def grid25 : CompactGrid := (25, 3, samplesP25, samplesQ25)
def tab25 : CompactTable := (compactCount25, compactPath25, compactLive25, compactPoolIDs25, compactBucket25)
def check25 (k : Nat) := compactNode grid25 tab25 compactDomains25 compactPerms25 k
def sliceSpecs25 : List SliceSpec := []
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains25 : ∀ d ∈ compactDomains25, Slice true (vars 25) (graphGoal 25) d.1 d.2 := by
  apply compactDomains_valid (earlier := []) (specs := sliceSpecs25)
  · simp
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs25 : properPairs (graphGoal 25) (asRow samplesP25) (asRow samplesQ25) :=
  compactPairs (g := grid25) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos25 : ∀ p ∈ compactPerms25, autoOK (graphGoal 25) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c25k3p0 : chartBlock (check25 3) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev25k3 : chartBlock (check25 3) 0 1 = true :=
  c25k3p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded25 : Impossible true (graphGoal 25) 3 (vars 25).toFinset := by
  apply compactRoot (g := grid25) (t := tab25) (dom := compactDomains25) (perms := compactPerms25) pairs25 domains25 autos25
  · intro k hk
    change k ≤ 3 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · exact lev25k3
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound25 : Lower true (vars 25) (graphGoal 25) 4 :=
  plain_low (hints := 3) (by decide +kernel) excluded25
def grid27 : CompactGrid := (27, 4, samplesP27, samplesQ27)
def tab27 : CompactTable := (compactCount27, compactPath27, compactLive27, compactPoolIDs27, compactBucket27)
def check27 (k : Nat) := compactNode grid27 tab27 compactDomains27 compactPerms27 k
def sliceSpecs27 : List SliceSpec := [(2, 0, 25, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains27 : ∀ d ∈ compactDomains27, Slice true (vars 27) (graphGoal 27) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(25, 4)]) (specs := sliceSpecs27)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound25
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs27 : properPairs (graphGoal 27) (asRow samplesP27) (asRow samplesQ27) :=
  compactPairs (g := grid27) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos27 : ∀ p ∈ compactPerms27, autoOK (graphGoal 27) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c27k4p0 : chartBlock (check27 4) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev27k4 : chartBlock (check27 4) 0 1 = true :=
  c27k4p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded27 : Impossible true (graphGoal 27) 4 (vars 27).toFinset := by
  apply compactRoot (g := grid27) (t := tab27) (dom := compactDomains27) (perms := compactPerms27) pairs27 domains27 autos27
  · intro k hk
    change k ≤ 4 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev27k4
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound27 : Lower true (vars 27) (graphGoal 27) 5 :=
  plain_low (hints := 67) (by decide +kernel) excluded27
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound116 : Lower true (vars 116) (graphGoal 116) 5 :=
  carry_of (old := 116) (rep := 27) (swaps := [32, 65, 83, 97, 49]) (by decide +kernel) bound27
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound114 : Lower true (vars 114) (graphGoal 114) 5 :=
  carry_of (old := 114) (rep := 27) (swaps := [16, 67, 80, 99]) (by decide +kernel) bound27
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound102 : Lower true (vars 102) (graphGoal 102) 5 :=
  carry_of (old := 102) (rep := 27) (swaps := [32, 83, 100]) (by decide +kernel) bound27
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound86 : Lower true (vars 86) (graphGoal 86) 5 :=
  carry_of (old := 86) (rep := 27) (swaps := [16, 32, 67, 99]) (by decide +kernel) bound27
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound100 : Lower true (vars 100) (graphGoal 100) 4 :=
  carry_of (old := 100) (rep := 25) (swaps := [32, 83, 100]) (by decide +kernel) bound25
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound82 : Lower true (vars 82) (graphGoal 82) 4 :=
  carry_of (old := 82) (rep := 25) (swaps := [16, 99]) (by decide +kernel) bound25
def grid118 : CompactGrid := (118, 7, samplesP118, samplesQ118)
def tab118 : CompactTable := (compactCount118, compactPath118, compactLive118, compactPoolIDs118, compactBucket118)
def check118 (k : Nat) := compactNode grid118 tab118 compactDomains118 compactPerms118 k
def sliceSpecs118 : List SliceSpec := [(2, 0, 116, 0, 0, 5, 5), (4, 0, 114, 0, 0, 5, 5), (16, 0, 102, 0, 0, 5, 5), (32, 0, 86, 0, 0, 5, 5), (18, 0, 100, 0, 0, 4, 4), (36, 0, 82, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains118 : ∀ d ∈ compactDomains118, Slice true (vars 118) (graphGoal 118) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(116, 5), (114, 5), (102, 5), (86, 5), (100, 4), (82, 4)]) (specs := sliceSpecs118)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl
    · exact bound116
    · exact bound114
    · exact bound102
    · exact bound86
    · exact bound100
    · exact bound82
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs118 : properPairs (graphGoal 118) (asRow samplesP118) (asRow samplesQ118) :=
  compactPairs (g := grid118) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos118 : ∀ p ∈ compactPerms118, autoOK (graphGoal 118) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c118k4p0 : chartBlock (check118 4) 0 3 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev118k4 : chartBlock (check118 4) 0 3 = true :=
  c118k4p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c118k5p0 : chartBlock (check118 5) 0 10 = true := by
  iterate 2 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev118k5 : chartBlock (check118 5) 0 10 = true :=
  c118k5p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c118k6p0 : chartBlock (check118 6) 0 3 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev118k6 : chartBlock (check118 6) 0 3 = true :=
  c118k6p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c118k7p0 : chartBlock (check118 7) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev118k7 : chartBlock (check118 7) 0 1 = true :=
  c118k7p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded118 : Impossible true (graphGoal 118) 7 (vars 118).toFinset := by
  apply compactRoot (g := grid118) (t := tab118) (dom := compactDomains118) (perms := compactPerms118) pairs118 domains118 autos118
  · intro k hk
    change k ≤ 7 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev118k4
    · exact lev118k5
    · exact lev118k6
    · exact lev118k7
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound118 : Lower true (vars 118) (graphGoal 118) 8 :=
  plain_low (hints := 18941248) (by decide +kernel) excluded118
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound41 : Lower true (vars 41) (graphGoal 41) 4 :=
  carry_of (old := 41) (rep := 25) (swaps := [84]) (by decide +kernel) bound25
def grid57 : CompactGrid := (57, 4, samplesP57, samplesQ57)
def tab57 : CompactTable := (compactCount57, compactPath57, compactLive57, compactPoolIDs57, compactBucket57)
def check57 (k : Nat) := compactNode grid57 tab57 compactDomains57 compactPerms57 k
def sliceSpecs57 : List SliceSpec := [(16, 0, 41, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains57 : ∀ d ∈ compactDomains57, Slice true (vars 57) (graphGoal 57) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(41, 4)]) (specs := sliceSpecs57)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound41
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs57 : properPairs (graphGoal 57) (asRow samplesP57) (asRow samplesQ57) :=
  compactPairs (g := grid57) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos57 : ∀ p ∈ compactPerms57, autoOK (graphGoal 57) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c57k4p0 : chartBlock (check57 4) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev57k4 : chartBlock (check57 4) 0 1 = true :=
  c57k4p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded57 : Impossible true (graphGoal 57) 4 (vars 57).toFinset := by
  apply compactRoot (g := grid57) (t := tab57) (dom := compactDomains57) (perms := compactPerms57) pairs57 domains57 autos57
  · intro k hk
    change k ≤ 4 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev57k4
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound57 : Lower true (vars 57) (graphGoal 57) 5 :=
  plain_low (hints := 3) (by decide +kernel) excluded57
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound113 : Lower true (vars 113) (graphGoal 113) 5 :=
  carry_of (old := 113) (rep := 57) (swaps := [99]) (by decide +kernel) bound57
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound99 : Lower true (vars 99) (graphGoal 99) 5 :=
  carry_of (old := 99) (rep := 27) (swaps := [83, 100]) (by decide +kernel) bound27
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound83 : Lower true (vars 83) (graphGoal 83) 5 :=
  carry_of (old := 83) (rep := 57) (swaps := [64, 81, 99, 83]) (by decide +kernel) bound57
def grid115 : CompactGrid := (115, 6, samplesP115, samplesQ115)
def tab115 : CompactTable := (compactCount115, compactPath115, compactLive115, compactPoolIDs115, compactBucket115)
def check115 (k : Nat) := compactNode grid115 tab115 compactDomains115 compactPerms115 k
def sliceSpecs115 : List SliceSpec := [(1, 0, 114, 0, 0, 5, 5), (2, 0, 113, 0, 0, 5, 5), (16, 0, 99, 0, 0, 5, 5), (32, 0, 83, 0, 0, 5, 5)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains115 : ∀ d ∈ compactDomains115, Slice true (vars 115) (graphGoal 115) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(114, 5), (113, 5), (99, 5), (83, 5)]) (specs := sliceSpecs115)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact bound114
    · exact bound113
    · exact bound99
    · exact bound83
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs115 : properPairs (graphGoal 115) (asRow samplesP115) (asRow samplesQ115) :=
  compactPairs (g := grid115) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos115 : ∀ p ∈ compactPerms115, autoOK (graphGoal 115) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c115k6p0 : chartBlock (check115 6) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev115k6 : chartBlock (check115 6) 0 1 = true :=
  c115k6p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded115 : Impossible true (graphGoal 115) 6 (vars 115).toFinset := by
  apply compactRoot (g := grid115) (t := tab115) (dom := compactDomains115) (perms := compactPerms115) pairs115 domains115 autos115
  · intro k hk
    change k ≤ 6 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev115k6
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound115 : Lower true (vars 115) (graphGoal 115) 7 :=
  plain_low (hints := 68) (by decide +kernel) excluded115
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound117 : Lower true (vars 117) (graphGoal 117) 7 :=
  carry_of (old := 117) (rep := 115) (swaps := [33, 84]) (by decide +kernel) bound115
def grid87 : CompactGrid := (87, 5, samplesP87, samplesQ87)
def tab87 : CompactTable := (compactCount87, compactPath87, compactLive87, compactPoolIDs87, compactBucket87)
def check87 (k : Nat) := compactNode grid87 tab87 compactDomains87 compactPerms87 k
def sliceSpecs87 : List SliceSpec := [(1, 0, 86, 0, 0, 5, 5)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains87 : ∀ d ∈ compactDomains87, Slice true (vars 87) (graphGoal 87) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(86, 5)]) (specs := sliceSpecs87)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound86
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs87 : properPairs (graphGoal 87) (asRow samplesP87) (asRow samplesQ87) :=
  compactPairs (g := grid87) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos87 : ∀ p ∈ compactPerms87, autoOK (graphGoal 87) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c87k5p0 : chartBlock (check87 5) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev87k5 : chartBlock (check87 5) 0 1 = true :=
  c87k5p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded87 : Impossible true (graphGoal 87) 5 (vars 87).toFinset := by
  apply compactRoot (g := grid87) (t := tab87) (dom := compactDomains87) (perms := compactPerms87) pairs87 domains87 autos87
  · intro k hk
    change k ≤ 5 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev87k5
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound87 : Lower true (vars 87) (graphGoal 87) 6 :=
  plain_low (hints := 1604) (by decide +kernel) excluded87
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound103 : Lower true (vars 103) (graphGoal 103) 6 :=
  carry_of (old := 103) (rep := 87) (swaps := [33, 84]) (by decide +kernel) bound87
def grid55 : CompactGrid := (55, 4, samplesP55, samplesQ55)
def tab55 : CompactTable := (compactCount55, compactPath55, compactLive55, compactPoolIDs55, compactBucket55)
def check55 (k : Nat) := compactNode grid55 tab55 compactDomains55 compactPerms55 k
def sliceSpecs55 : List SliceSpec := []
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains55 : ∀ d ∈ compactDomains55, Slice true (vars 55) (graphGoal 55) d.1 d.2 := by
  apply compactDomains_valid (earlier := []) (specs := sliceSpecs55)
  · simp
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs55 : properPairs (graphGoal 55) (asRow samplesP55) (asRow samplesQ55) :=
  compactPairs (g := grid55) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos55 : ∀ p ∈ compactPerms55, autoOK (graphGoal 55) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c55k4p0 : chartBlock (check55 4) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev55k4 : chartBlock (check55 4) 0 1 = true :=
  c55k4p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded55 : Impossible true (graphGoal 55) 4 (vars 55).toFinset := by
  apply compactRoot (g := grid55) (t := tab55) (dom := compactDomains55) (perms := compactPerms55) pairs55 domains55 autos55
  · intro k hk
    change k ≤ 4 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev55k4
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound55 : Lower true (vars 55) (graphGoal 55) 5 :=
  plain_low (hints := 1348) (by decide +kernel) excluded55
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound101 : Lower true (vars 101) (graphGoal 101) 5 :=
  carry_of (old := 101) (rep := 57) (swaps := [64, 82, 83, 100]) (by decide +kernel) bound57
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound85 : Lower true (vars 85) (graphGoal 85) 5 :=
  carry_of (old := 85) (rep := 27) (swaps := [33, 67, 99]) (by decide +kernel) bound27
def grid51 : CompactGrid := (51, 3, samplesP51, samplesQ51)
def tab51 : CompactTable := (compactCount51, compactPath51, compactLive51, compactPoolIDs51, compactBucket51)
def check51 (k : Nat) := compactNode grid51 tab51 compactDomains51 compactPerms51 k
def sliceSpecs51 : List SliceSpec := []
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains51 : ∀ d ∈ compactDomains51, Slice true (vars 51) (graphGoal 51) d.1 d.2 := by
  apply compactDomains_valid (earlier := []) (specs := sliceSpecs51)
  · simp
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs51 : properPairs (graphGoal 51) (asRow samplesP51) (asRow samplesQ51) :=
  compactPairs (g := grid51) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos51 : ∀ p ∈ compactPerms51, autoOK (graphGoal 51) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c51k3p0 : chartBlock (check51 3) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev51k3 : chartBlock (check51 3) 0 1 = true :=
  c51k3p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded51 : Impossible true (graphGoal 51) 3 (vars 51).toFinset := by
  apply compactRoot (g := grid51) (t := tab51) (dom := compactDomains51) (perms := compactPerms51) pairs51 domains51 autos51
  · intro k hk
    change k ≤ 3 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · exact lev51k3
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound51 : Lower true (vars 51) (graphGoal 51) 4 :=
  plain_low (hints := 68) (by decide +kernel) excluded51
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound53 : Lower true (vars 53) (graphGoal 53) 4 :=
  carry_of (old := 53) (rep := 51) (swaps := [33, 84]) (by decide +kernel) bound51
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound97 : Lower true (vars 97) (graphGoal 97) 4 :=
  carry_of (old := 97) (rep := 25) (swaps := [83, 100]) (by decide +kernel) bound25
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound81 : Lower true (vars 81) (graphGoal 81) 4 :=
  carry_of (old := 81) (rep := 25) (swaps := [99]) (by decide +kernel) bound25
def grid119 : CompactGrid := (119, 9, samplesP119, samplesQ119)
def tab119 : CompactTable := (compactCount119, compactPath119, compactLive119, compactPoolIDs119, compactBucket119)
def check119 (k : Nat) := compactNode grid119 tab119 compactDomains119 compactPerms119 k
def sliceSpecs119 : List SliceSpec := [(1, 0, 118, 0, 0, 8, 8), (2, 0, 117, 0, 0, 7, 7), (4, 0, 115, 0, 0, 7, 7), (16, 0, 103, 0, 0, 6, 6), (32, 0, 87, 0, 0, 6, 6), (64, 0, 55, 0, 0, 5, 5), (6, 0, 113, 0, 0, 5, 5), (17, 0, 102, 0, 0, 5, 5), (18, 0, 101, 0, 0, 5, 5), (20, 0, 99, 0, 0, 5, 5), (34, 0, 85, 0, 0, 5, 5), (36, 0, 83, 0, 0, 5, 5), (66, 0, 53, 0, 0, 4, 4), (68, 0, 51, 0, 0, 4, 4), (19, 0, 100, 0, 0, 4, 4), (22, 0, 97, 0, 0, 4, 4), (38, 0, 81, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains119 : ∀ d ∈ compactDomains119, Slice true (vars 119) (graphGoal 119) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(118, 8), (117, 7), (115, 7), (103, 6), (87, 6), (55, 5), (113, 5), (102, 5), (101, 5), (99, 5), (85, 5), (83, 5), (53, 4), (51, 4), (100, 4), (97, 4), (81, 4)]) (specs := sliceSpecs119)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact bound118
    · exact bound117
    · exact bound115
    · exact bound103
    · exact bound87
    · exact bound55
    · exact bound113
    · exact bound102
    · exact bound101
    · exact bound99
    · exact bound85
    · exact bound83
    · exact bound53
    · exact bound51
    · exact bound100
    · exact bound97
    · exact bound81
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs119 : properPairs (graphGoal 119) (asRow samplesP119) (asRow samplesQ119) :=
  compactPairs (g := grid119) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos119 : ∀ p ∈ compactPerms119, autoOK (graphGoal 119) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c119k4p0 : chartBlock (check119 4) 0 6 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev119k4 : chartBlock (check119 4) 0 6 = true :=
  c119k4p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c119k5p0 : chartBlock (check119 5) 0 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c119k5p1 : chartBlock (check119 5) 32 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c119k5p2 : chartBlock (check119 5) 64 6 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev119k5 : chartBlock (check119 5) 0 70 = true :=
  (chartBlock_join (a := 32) (b := 38) c119k5p0 (chartBlock_join (a := 32) (b := 6) c119k5p1 c119k5p2))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c119k6p0 : chartBlock (check119 6) 0 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c119k6p1 : chartBlock (check119 6) 32 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c119k6p2 : chartBlock (check119 6) 64 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c119k6p3 : chartBlock (check119 6) 96 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c119k6p4 : chartBlock (check119 6) 128 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c119k6p5 : chartBlock (check119 6) 160 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c119k6p6 : chartBlock (check119 6) 192 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c119k6p7 : chartBlock (check119 6) 224 7 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev119k6 : chartBlock (check119 6) 0 231 = true :=
  (chartBlock_join (a := 128) (b := 103) (chartBlock_join (a := 64) (b := 64) (chartBlock_join (a := 32) (b := 32) c119k6p0 c119k6p1) (chartBlock_join (a := 32) (b := 32) c119k6p2 c119k6p3)) (chartBlock_join (a := 64) (b := 39) (chartBlock_join (a := 32) (b := 32) c119k6p4 c119k6p5) (chartBlock_join (a := 32) (b := 7) c119k6p6 c119k6p7)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c119k7p0 : chartBlock (check119 7) 0 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c119k7p1 : chartBlock (check119 7) 32 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c119k7p2 : chartBlock (check119 7) 64 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c119k7p3 : chartBlock (check119 7) 96 24 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev119k7 : chartBlock (check119 7) 0 120 = true :=
  (chartBlock_join (a := 64) (b := 56) (chartBlock_join (a := 32) (b := 32) c119k7p0 c119k7p1) (chartBlock_join (a := 32) (b := 24) c119k7p2 c119k7p3))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c119k8p0 : chartBlock (check119 8) 0 14 = true := by
  iterate 2 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev119k8 : chartBlock (check119 8) 0 14 = true :=
  c119k8p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c119k9p0 : chartBlock (check119 9) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev119k9 : chartBlock (check119 9) 0 1 = true :=
  c119k9p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded119 : Impossible true (graphGoal 119) 9 (vars 119).toFinset := by
  apply compactRoot (g := grid119) (t := tab119) (dom := compactDomains119) (perms := compactPerms119) pairs119 domains119 autos119
  · intro k hk
    change k ≤ 9 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev119k4
    · exact lev119k5
    · exact lev119k6
    · exact lev119k7
    · exact lev119k8
    · exact lev119k9
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound119 : Lower true (vars 119) (graphGoal 119) 10 :=
  plain_low (hints := 1348) (by decide +kernel) excluded119
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound77 : Lower true (vars 77) (graphGoal 77) 5 :=
  carry_of (old := 77) (rep := 27) (swaps := [33, 100]) (by decide +kernel) bound27
def grid79 : CompactGrid := (79, 5, samplesP79, samplesQ79)
def tab79 : CompactTable := (compactCount79, compactPath79, compactLive79, compactPoolIDs79, compactBucket79)
def check79 (k : Nat) := compactNode grid79 tab79 compactDomains79 compactPerms79 k
def sliceSpecs79 : List SliceSpec := [(2, 0, 77, 0, 0, 5, 5)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains79 : ∀ d ∈ compactDomains79, Slice true (vars 79) (graphGoal 79) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(77, 5)]) (specs := sliceSpecs79)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound77
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs79 : properPairs (graphGoal 79) (asRow samplesP79) (asRow samplesQ79) :=
  compactPairs (g := grid79) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos79 : ∀ p ∈ compactPerms79, autoOK (graphGoal 79) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c79k5p0 : chartBlock (check79 5) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev79k5 : chartBlock (check79 5) 0 1 = true :=
  c79k5p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded79 : Impossible true (graphGoal 79) 5 (vars 79).toFinset := by
  apply compactRoot (g := grid79) (t := tab79) (dom := compactDomains79) (perms := compactPerms79) pairs79 domains79 autos79
  · intro k hk
    change k ≤ 5 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev79k5
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound79 : Lower true (vars 79) (graphGoal 79) 6 :=
  plain_low (hints := 1635) (by decide +kernel) excluded79
end PEqualNP.Outside.L_meta_30332.P10724

namespace PEqualNP.Outside.L_meta_30332.P10830
open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_30332.P11311
theorem flip_flip {u d} (h : allowed u d) : allowed u (flipOp d) ∧ flipOp (flipOp d)=d := by
  rcases allowed_four h with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩ 
  all_goals simp_all [flipOp,allowed]
def graphGoal (m : Nat) : Sig :=
  let x := vertex m
  (x 0 &&& x 4) ||| (x 1 &&& x 5) ||| (x 0 &&& x 6) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 0 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7) ||| (x 2 &&& x 8) ||| (x 3 &&& x 8) ||| (x 5 &&& x 8)
def supportPairs (t : Nat) (mask : Nat) : List (Sig × Row × Row) :=
  (selected mask).map fun (i,a) =>
    let hi := ((mask/512-1) >>> (4*i)) &&& 15
    let r := if mask >= 512 then (if hi = 0 then 0 else 1 <<< (hi-1)) else if t/81==2 && i==t/9 % 9 then 1 <<< (t % 9) else if t/81==2 && i==t % 9 then 1 <<< (t/9 % 9) else 0
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))
def assertSize (m hints L : Nat) :=
  let xs := graphPairs m hints
  properB (graphGoal m) && checkEssential (graphGoal m) (vars m) xs &&
    decide (L ≤ (xs.map Prod.fst).toFinset.card-1)
theorem size_of {u m hints L} (h : assertSize m hints L = true) :
    Lower u (vars m) (graphGoal m) L := by
  simp only [assertSize,Bool.and_eq_true,decide_eq_true_eq] at h
  intro p bank hr ha
  exact h.2.trans (lower_count (proper_of _ h.1.1) _ h.1.2 p bank hr ha)
def chartGoal (m : Nat) : Sig := graphGoal m
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
abbrev Bits := BitVec 416
abbrev Signals := Bits × Bits
abbrev Decor := Sig × Signals
def pairSig (r s : Fin 416 → Row) (a : Sig) : Signals := (ofRows r a,ofRows s a)
def properPairs (T : Sig) (r s : Fin 416 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 416 r s (pairSig r s) := by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩
def faithful (r s : Fin 416 → Row) (x : Decor) := x.2 = pairSig r s x.1
def dbin (d : Nat) (x y : Decor) : Decor := (bin d x.1 y.1,bv d x.2.1 y.2.1,bv d x.2.2 y.2.2)
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
def asRow (cols : Nat → Bits) (i : Fin 416) : Row :=
  (BitVec.ofBoolListLE (List.ofFn (fun j : Fin 9 => (cols j.val).getLsbD i.val))).toFin.cast
    (by simp [List.length_ofFn])
theorem asRow_bit (cols : Nat → Bits) (i : Fin 416) (j : Fin 9) :
    bit (asRow cols i) (inputs.getD j.val zero) = (cols j.val).getLsbD i.val := by
  rw [input_coords]
  change (BitVec.ofBoolListLE (List.ofFn (fun h : Fin 9 => (cols h.val).getLsbD i.val))).getLsbD j.val = _
  simp only [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [j.isLt]
def rawDecor (m : Nat) (p q : Nat → Bits) : List Decor :=
  (selected m).map (fun (j,a) => (a,p j,q j))
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
  (x 0 &&& x 4) ||| (x 1 &&& x 5) ||| (x 0 &&& x 6) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 0 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7) ||| (x 2 &&& x 8) ||| (x 3 &&& x 8) ||| (x 5 &&& x 8)
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 416) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then v j.val else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · simpa [vertex,hh] using asRow_bit v i j
  · simp [vertex,hh,bit_zero]
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 416) :
    bit (asRow v i) (graphGoal m) = (liftGoal m v).getLsbD i.val := by
  have pos (j : Nat) (hj : j<9) : (vertex m j).getLsbD (asRow v i).val = ((if m.testBit j then v j else 0) : Bits).getLsbD i.val := bit_vertex m v i ⟨j,hj⟩
  simp only [bit,graphGoal,liftGoal,BitVec.getLsbD_and,BitVec.getLsbD_or]
  simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide),pos 6 (by decide),pos 7 (by decide),pos 8 (by decide)]
abbrev Cov := Bits × Bits × Bits
def addCov (z : Bits) (c : Cov) : Cov :=
  (z ||| c.1, (z &&& ~~~c.1) ||| (c.2.1 &&& ~~~z),
   (z &&& c.2.1) ||| (c.2.2 &&& ~~~z))
def coverage (d : Bool) (v : List Decor) : Cov :=
  v.foldr (fun a c => addCov (column d a.2) c) (0,0,0)
def takeOne (c : Cov) (a : Bits) : Bits := c.1 &&& ~~~(c.2.1 &&& a)
def takeTwo (c : Cov) (a b : Bits) : Bits :=
  c.1 &&& ~~~((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b)))
theorem cov_one (c : Cov) (a : Bits) : takeOne (addCov a c) a=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeOne,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases c.1.getLsbD i <;> cases c.2.1.getLsbD i <;> rfl
theorem cov_two (c : Cov) (a b : Bits) : takeTwo (addCov a (addCov b c)) a b=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeTwo,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
    cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl
theorem add_swap (c : Cov) (a b : Bits) : addCov a (addCov b c)=addCov b (addCov a c) := by
  apply Prod.ext
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [addCov,BitVec.getLsbD_or]
    cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
  · apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
      simp only [addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and] <;>
      cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
      cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl
theorem cov_perm (d : Bool) {l r : List Decor} (h : l.Perm r) : coverage d l=coverage d r := by
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
def keyWord (v : Sig) :=
  let n := v.toNat % 18446744073709551557
  (n*(n+971)) % 18446744073709551557
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
    if (rs ||| column d z.2) != BitVec.allOnes 416 then true else
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
  have be : ((restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 416) = false := by
    simpa using sep
  change (if (restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 416 then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
  rw [be,pp,fr] at test
  exact closeChild_sound (op:=movedChoice op a b) (rest:=rest.map Prod.fst) pv lv ndc test k hk h
def testPair (ctx : NodeContext) (a b : Decor) (op : Nat) :=
  let z := dbin op a b
  let attempt := evalMove ctx op a b z
  attempt false false && attempt true false && attempt false true && attempt true true
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
theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 416) :
    bit (asRow v i) (chartGoal m) = (chartSamples m v).getLsbD i.val := by
  exact bit_liftGoal m v i
theorem chart_pairs {m : Nat} {p q : Nat → Bits}
    (hp : chartSamples m p = BitVec.allOnes 416) (hq : chartSamples m q = 0) :
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
def storedDepth (_g : Forest) (depth : Nat) := depth
def readNode (g : Forest) (k i : Nat) : Nat × List Decor × List Decor :=
  let raw := wiresOf g
  let (_,depth,_,_,_,_,_,data) := g.levels k
  let len := 10*storedDepth g depth
  let width := len+raw.length+depth
  let recp := packedAt data (i*width) width
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
  let start := num*(10*storedDepth g depth+raw.length+depth)
  let pos := start+num*offw+packedAt data (start+i*offw) offw
  let nr := packedAt data pos 5
  let nl := packedAt data (pos+5) lw
  let st := pos+5+lw
  let rules := (getPairs data cw depth nr st).filterMap (fun (a,b) => buildRule g ops depth bank a b)
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
  (chartSamples g.mask (fun j => (g.samples j).1) == BitVec.allOnes 416) &&
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
theorem extendKnown_ok {u old L m carries} (previous : Known u old)
    (main : Lower u (varsX m) (graphGoal m) L)
    (ok : carries.all (fun v => carryOK v.1 m v.2) = true) :
    Known u (extendKnown old L carries) := by
  intro e he
  rcases List.mem_append.mp he with hx | h
  · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hx
    exact carry_of (List.all_eq_true.mp ok _ hv) main
  · exact previous e h
theorem baseKnown : Known true [] := by simp [Known]
def lanePlace (v : Nat) (upper : Nat) := 2^417*upper+v
def combineLanes {α : Type} (f : α → Bits) : List α → Nat
  | [] => 0
  | x::xs => lanePlace (f x).toNat (combineLanes f xs)
def units : Nat → Nat
  | 0 => 0
  | n+1 => lanePlace 1 (units n)
theorem laneSmall (x : Bits) : x.toNat < 2^417 :=
  lt_trans x.isLt (by decide +kernel)
theorem place_and (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u &&& lanePlace b.toNat v = lanePlace (a &&& b).toNat (u &&& v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_and,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<417 <;> simp only [h,ite_true,ite_false,BitVec.toNat_and,Nat.testBit_and]
theorem place_or (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ||| lanePlace b.toNat v = lanePlace (a ||| b).toNat (u ||| v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_or,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<417 <;> simp only [h,ite_true,ite_false,BitVec.toNat_or,Nat.testBit_or]
theorem place_xor (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ^^^ lanePlace b.toNat v = lanePlace (a ^^^ b).toNat (u ^^^ v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_xor,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<417 <;> simp only [h,ite_true,ite_false,BitVec.toNat_xor,Nat.testBit_xor]
theorem lanes_and {α} (f g : α → Bits) (xs) :
    combineLanes f xs &&& combineLanes g xs = combineLanes (fun x => f x &&& g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_and,ih]
theorem lanes_or {α} (f g : α → Bits) (xs) :
    combineLanes f xs ||| combineLanes g xs = combineLanes (fun x => f x ||| g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_or,ih]
theorem lanes_xor {α} (f g : α → Bits) (xs) :
    combineLanes f xs ^^^ combineLanes g xs = combineLanes (fun x => f x ^^^ g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_xor,ih]
def fullMarks (r packed : Nat) := ((packed+r) >>> 416) &&& r
theorem unit_bit (n i : Nat) (hi : i<n) : (units n).testBit (417*i) = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [units,lanePlace,Nat.testBit_two_pow_mul_add _ (by decide +kernel : 1 < 2^417)]
    cases i with
    | zero => simp
    | succ i =>
      have di : 417*(i+1)-417=417*i := by omega
      have ge : ¬417*(i+1)<417 := by omega
      simp only [ge,ite_false,di]
      exact ih _ (by omega)
set_option maxRecDepth 8192 in
theorem guardBit (a : Bits) : (a.toNat+1).testBit 416 = (a==BitVec.allOnes 416) := by
  by_cases h : a=BitVec.allOnes 416
  · subst a
    decide +kernel
  · have lim := a.isLt
    have ne : a.toNat ≠ 2^416-1 := by
      intro eq
      apply h
      apply BitVec.eq_of_toNat_eq
      simpa only [BitVec.toNat_allOnes] using eq
    have lt : a.toNat+1<2^416 := by omega
    rw [Nat.testBit_eq_false_of_lt lt]
    exact (beq_eq_false_iff_ne.mpr h).symm
set_option maxRecDepth 8192 in
theorem mark_at {α} (f : α → Bits) (xs : List α) (i : Nat) (hi : i<xs.length) :
    (fullMarks (units xs.length) (combineLanes f xs)).testBit (417*i) =
      (f xs[i]==BitVec.allOnes 416) := by
  simp only [fullMarks,Nat.testBit_and,Nat.testBit_shiftRight,unit_bit _ _ hi,Bool.and_true]
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    simp only [combineLanes,List.length_cons,units,lanePlace]
    have sum (u v x : Nat) : 2^417*u+x+(2^417*v+1)=2^417*(u+v)+(x+1) := by omega
    rw [sum,Nat.testBit_two_pow_mul_add _ (show (f a).toNat+1<2^417 from by have := (f a).isLt; omega)]
    have hi' : i < xs.length+1 := hi
    cases i with
    | zero => simpa using guardBit (f a)
    | succ i =>
      have ge : ¬417*(i+1)+416<417 := by omega
      have di : 417*(i+1)+416-417=417*i+416 := by omega
      simp only [ge,ite_false,di,List.getElem_cons_succ]
      apply ih i (by omega)
abbrev PackedSig := Nat × Nat
abbrev PackedCov := Nat × Nat × Nat
def packedSig {α} (s : α → Signals) (xs : List α) : PackedSig :=
  (combineLanes (fun x => (s x).1) xs,combineLanes (fun x => (s x).2) xs)
def packedCov {α} (c : α → Cov) (xs : List α) : PackedCov :=
  (combineLanes (fun x => (c x).1) xs,combineLanes (fun x => (c x).2.1) xs,
   combineLanes (fun x => (c x).2.2) xs)
def packedColumn (d : Bool) (a : PackedSig) :=
  if d then a.1 ^^^ (a.1 &&& a.2) else a.1 ^^^ a.2
theorem xor_meet (a b : Bits) : a ^^^ (a &&& b) = a &&& ~~~b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
theorem packed_column {α} (s : α → Signals) (xs : List α) (d : Bool) :
    packedColumn d (packedSig s xs) = combineLanes (fun x => column d (s x)) xs := by
  cases d <;> simp only [packedColumn,packedSig,column,Bool.false_eq_true,ite_false,ite_true,lanes_and,lanes_xor,xor_meet]
def packedOp (op : Nat) (a b : PackedSig) : PackedSig :=
  if op=0 then (a.1 &&& b.1,a.2 &&& b.2) else if op=1 then (a.1 ||| b.1,a.2 ||| b.2)
  else if op=2 then (a.1 ^^^ (a.1 &&& b.1),a.2 ^^^ (a.2 &&& b.2))
  else (b.1 ^^^ (b.1 &&& a.1),b.2 ^^^ (b.2 &&& a.2))
theorem packed_op {α} (a b : α → Decor) (xs : List α) (op : Nat) :
    packedOp op (packedSig (fun x => (a x).2) xs) (packedSig (fun x => (b x).2) xs) =
    packedSig (fun x => (dbin op (a x) (b x)).2) xs := by
  by_cases h0 : op=0
  · simp only [packedOp,h0,ite_true,packedSig,lanes_and,dbin,bv]
  by_cases h1 : op=1
  · simp [packedOp,h1,packedSig,lanes_or,dbin,bv]
  by_cases h2 : op=2
  · simp [packedOp,h2,packedSig,lanes_and,lanes_xor,xor_meet,dbin,bv]
  · have e (x y : Bits) : ~~~x &&& y = y &&& ~~~x := BitVec.and_comm _ _
    simp only [packedOp,h0,h1,h2,ite_false,packedSig,lanes_and,lanes_xor,xor_meet,dbin,bv,e]
def takePacked (c : PackedCov) (a b : Nat) (ka kb : Bool) :=
  let without1 := fun w => c.1 ^^^ (c.1 &&& (c.2.1 &&& w))
  let without2 := c.1 ^^^ (c.1 &&& ((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b))))
  if ka then (if kb then c.1 else without1 b)
  else if kb then without1 a else without2
theorem takePacked_ok {α} (c : α → Cov) (a b : α → Bits) (xs : List α) (ka kb : Bool) :
    takePacked (packedCov c xs) (combineLanes a xs) (combineLanes b xs) ka kb =
    combineLanes (fun x => restCov (c x) (a x) (b x) ka kb) xs := by
  cases ka <;> cases kb <;>
    simp only [takePacked,packedCov,lanes_and,lanes_or,lanes_xor,xor_meet,restCov,takeOne,takeTwo,
      Bool.false_eq_true,ite_false,ite_true]
def contextWire (c : NodeContext) (i : Nat) := c.2.2.1.getD i defaultDecor
def checkAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let a := contextWire c i
  let b := contextWire c j
  evalMove c op a b (dbin op a b) ka kb
def combField (c : NodeContext) (d ka kb : Bool) (op i j : Nat) :=
  let a := contextWire c i
  let b := contextWire c j
  restCov c.2.2.2.1.1 (column d a.2) (column d b.2) ka kb |||
    column d (dbin op a b).2
def onMarks {α : Type} (f : α → Bool) (mask : Nat) : List α → Bool
  | [] => true
  | x::xs => if mask=0 then true else
    ((mask &&& 1 == 0) || f x) && onMarks f (mask >>> 417) xs
theorem marked_ok {α} (f : α → Bool) (mask : Nat) (xs : List α) (i : Nat) (hi : i<xs.length)
    (bitOn : mask.testBit (417*i)=true) (ok : onMarks f mask xs=true) : f xs[i]=true := by
  induction xs generalizing mask i with
  | nil => simp at hi
  | cons x xs ih =>
    have ne : mask≠0 := by intro e; simp [e] at bitOn
    simp only [onMarks,ne,ite_false,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
    cases i with
    | zero =>
      have nonzero : mask &&& 1 ≠ 0 := by
        intro he
        have at0 := congrArg (fun n : Nat => n.testBit 0) he
        simp only [Nat.testBit_and] at at0
        change mask.testBit 0=true at bitOn
        simp [bitOn] at at0
      exact ok.1.resolve_left nonzero
    | succ i =>
      apply ih (mask:=mask >>> 417) (i:=i) (by simpa using hi) _ ok.2
      simpa only [Nat.testBit_shiftRight,Nat.mul_succ,Nat.add_comm] using bitOn
abbrev Batch := Nat × Nat × Nat × List PackedSig × PackedCov
def makeBatch (k n : Nat) (xs : List NodeContext) : Batch :=
  (k,n,units xs.length,(List.range n).map (fun i => packedSig (fun c => (contextWire c i).2) xs),
    packedCov (fun c => c.2.2.2.1.1) xs)
def laneWire (b : Batch) (i : Nat) := b.2.2.2.1.getD i (0,0)
theorem laneWire_at (k n) (xs) {i : Nat} (h : i<n) :
    laneWire (makeBatch k n xs) i = packedSig (fun c => (contextWire c i).2) xs := by
  simp [laneWire,makeBatch,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range,h]
theorem masked_comp (d x : Sig) : masked d (neg x) = d ^^^ masked d x := by
  apply bit_ext
  intro r
  simp only [masked,neg,bit,BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_xor,r.isLt,decide_true,Bool.true_and]
  cases d.getLsbD r.val <;> cases x.getLsbD r.val <;> rfl
def constantLoss (p : Decor → Bool) (a : Decor) (keep : Bool) :=
  if keep then 0 else (p a).toNat
theorem lossBound (p : Decor → Bool) (ws : List Decor) (a : Decor) (keep : Bool) :
    ws.countP p ≤ (delOne ws a keep).countP p + constantLoss p a keep := by
  cases keep
  · simp only [delOne,Bool.false_eq_true,ite_false,constantLoss,List.countP_erase]
    split
    next h => simp [h.2]; omega
    next => omega
  · simp [delOne,constantLoss]
theorem keptCount (p : Decor → Bool) (ws : List Decor) (a b : Decor) (ka kb : Bool) :
    ws.countP p - constantLoss p a ka - constantLoss p b kb ≤
    (delTwo ws a b ka kb).countP p := by
  have h1 := lossBound p ws a ka
  have h2 := lossBound p (delOne ws a ka) b kb
  simp only [delTwo]
  omega
noncomputable def force {β : Type} (n : Nat) (f : Nat → β) : β := Nat.rec (f 0) (fun k _ => f (Nat.succ k)) n
theorem force_eq {β : Type} (n : Nat) (f : Nat → β) : force n f = f n := by cases n <;> rfl
noncomputable def forceMap {α β : Type} (f : α → Nat) (l : List α) : (List Nat → β) → β :=
  List.rec (fun k => k []) (fun a _ ih k => force (f a) fun x => ih fun xs => k (x::xs)) l
theorem forceMap_eq {α β : Type} (f : α → Nat) (l : List α) (k : List Nat → β) : forceMap f l k = k (l.map f) := by
  induction l generalizing k with
  | nil => rfl
  | cons a l ih =>
    change force (f a) (fun x => forceMap f l fun xs => k (x::xs)) = _
    rw [force_eq,ih]
    rfl
def nmask (d : Nat) (a : Sig) : Nat := Nat.land a.toNat d
noncomputable def anyEq (m : Nat) (l : List Nat) : Bool := List.rec false (fun v _ ih => or (Nat.beq m v) ih) l
def nconst (d m : Nat) : Bool := or (Nat.beq m 0) (Nat.beq m d)
noncomputable def navail (u : Bool) (d : Nat) (pm : List Nat) (m : Nat) : Bool :=
  or (or (nconst d m) (anyEq m pm)) (and u (anyEq (Nat.xor d m) pm))
theorem nmask_eq (d a : Sig) : nmask d.toNat a = (masked d a).toNat := (BitVec.toNat_and _ _).symm
theorem beq_toNat (a b : Sig) : Nat.beq a.toNat b.toNat = (a==b) := by
  rw [Bool.eq_iff_iff,Nat.beq_eq,beq_iff_eq]
  exact BitVec.toNat_inj
theorem nconst_eq (d a : Sig) : nconst d.toNat (nmask d.toNat a) = isMaskedConstant d a := by
  rw [nmask_eq]
  have e : Nat.beq (masked d a).toNat 0 = (masked d a == zero) := by
    have z0 : zero.toNat=0 := by simp [zero]
    rw [←beq_toNat,z0]
  rw [nconst,e,beq_toNat]
  rfl
theorem anyEq_eq (x d : Sig) (pool : List Sig) : anyEq x.toNat (pool.map (nmask d.toNat)) = (pool.map (masked d)).any (fun v => v==x) := by
  induction pool with
  | nil => rfl
  | cons a l ih =>
    change or (Nat.beq x.toNat (nmask d.toNat a)) (anyEq x.toNat (l.map (nmask d.toNat))) = _
    rw [ih,nmask_eq,beq_toNat,List.map_cons,List.any_cons,Bool.beq_comm]
theorem navail_eq (u : Bool) (d a : Sig) (pool : List Sig) :
    navail u d.toNat (pool.map (nmask d.toNat)) (nmask d.toNat a) = availableB u d pool a := by
  have x : Nat.xor d.toNat (masked d a).toNat = (masked d (neg a)).toNat := by
    rw [masked_comp]
    exact (BitVec.toNat_xor _ _).symm
  rw [navail,nconst_eq,nmask_eq,x,anyEq_eq,anyEq_eq]
  simp only [availableB,isMaskedConstant]
def unav (u : Bool) (p : BoundPool) (w : Decor) : Nat := cond (availableB u p.domain p.wires w.1) 0 1
def slowCost (u : Bool) (p : BoundPool) (ws : List Decor) (k : Nat) (a b : Decor) (op : Nat) (ka kb : Bool) : Bool :=
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let z := bin op a.1 b.1
  let cm := ws.countP const - constantLoss const a ka - constantLoss const b kb + (isMaskedConstant p.domain z).toNat
  (((ws.map (unav u p)).sum == cond ka 0 (unav u p a) + cond kb 0 (unav u p b)) &&
    decide (k+p.paid+(!availableB u p.domain p.wires z).toNat < p.bound+cm)) &&
    (availableB u p.domain p.wires z || (availableB u p.domain p.wires a.1 && availableB u p.domain p.wires b.1))
def zN (op x y : Nat) : Nat := cond (Nat.beq op 0) (Nat.land x y) (cond (Nat.beq op 1) (Nat.lor x y)
  (cond (Nat.beq op 2) (Nat.xor x (Nat.land x y)) (Nat.xor y (Nat.land x y))))
theorem zN_eq (op : Nat) (d a b : Sig) : zN op (nmask d.toNat a) (nmask d.toNat b) = nmask d.toNat (bin op a b) := by
  have tn (x y : Sig) : Nat.land x.toNat y.toNat = (x &&& y).toNat := (BitVec.toNat_and x y).symm
  have tx (x y : Sig) : Nat.xor x.toNat y.toNat = (x ^^^ y).toNat := (BitVec.toNat_xor x y).symm
  have tor (x y : Sig) : Nat.lor x.toNat y.toNat = (x ||| y).toNat := (BitVec.toNat_or x y).symm
  simp only [nmask_eq]
  unfold zN
  by_cases h0 : op=0
  · subst h0
    change Nat.land _ _ = _
    rw [tn]
    congr 1
    apply bit_ext
    intro r
    simp only [masked,bin,bit,ite_true,BitVec.getLsbD_and]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  by_cases h1 : op=1
  · subst h1
    change Nat.lor _ _ = _
    rw [tor]
    congr 1
    apply bit_ext
    intro r
    simp only [masked,bin,bit,Nat.one_ne_zero,ite_true,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_or]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  have e0 : Nat.beq op 0=false := Bool.eq_false_iff.mpr (fun h => h0 (Nat.eq_of_beq_eq_true h))
  have e1 : Nat.beq op 1=false := Bool.eq_false_iff.mpr (fun h => h1 (Nat.eq_of_beq_eq_true h))
  by_cases h2 : op=2
  · subst h2
    change Nat.xor _ (Nat.land _ _) = _
    rw [tn,tx]
    congr 1
    apply bit_ext
    intro r
    simp only [masked,bin,bit,OfNat.ofNat_ne_zero,OfNat.ofNat_ne_one,ite_true,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_xor,BitVec.getLsbD_not,r.isLt,decide_true,Bool.true_and]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  have e2 : Nat.beq op 2=false := Bool.eq_false_iff.mpr (fun h => h2 (Nat.eq_of_beq_eq_true h))
  rw [e0,e1,e2]
  change Nat.xor _ (Nat.land _ _) = _
  rw [tn,tx]
  congr 1
  apply bit_ext
  intro r
  simp only [masked,bin,bit,h0,h1,h2,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_xor,BitVec.getLsbD_not,r.isLt,decide_true,Bool.true_and]
  cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
def nloss (d x : Nat) (keep : Bool) : Nat := cond keep 0 (cond (nconst d x) 1 0)
theorem nloss_eq (d : Sig) (a : Decor) (keep : Bool) :
    nloss d.toNat (nmask d.toNat a.1) keep = constantLoss (fun w : Decor => isMaskedConstant d w.1) a keep := by
  rw [nloss,nconst_eq,constantLoss]
  cases keep
  · cases isMaskedConstant d a.1 <;> rfl
  · rfl
abbrev QS := Nat × Nat × Nat × Nat × Nat × List Nat × List Nat × Bool
noncomputable def quickSpec (u : Bool) (k : Nat) (ws : List Decor) (p : BoundPool) : QS :=
  let d := p.domain.toNat
  let ms := ws.map (fun w : Decor => nmask d w.1)
  (d,ms.countP (nconst d),p.bound,Nat.add k p.paid,(ms.map fun m => cond (navail u d (p.wires.map (nmask d)) m) 0 1).sum,ms,p.wires.map (nmask d),u)
noncomputable def forceBool {β : Type} (b : Bool) (f : Bool → β) : β := Bool.rec (f false) (f true) b
noncomputable def forcePool {β : Type} (u : Bool) (k : Nat) (ws : List Decor) (p : BoundPool) (f : QS → β) : β :=
  force p.domain.toNat fun d => forceMap (nmask d) p.wires fun pm => forceMap (fun w : Decor => nmask d w.1) ws fun ms =>
  force (ms.countP (nconst d)) fun c => force p.bound fun l => force (Nat.add k p.paid) fun t =>
  force (ms.map fun m => cond (navail u d pm m) 0 1).sum fun v => forceBool u fun u => f (d,c,l,t,v,ms,pm,u)
theorem forcePool_eq {β : Type} (u k ws p) (f : QS → β) : forcePool u k ws p f = f (quickSpec u k ws p) := by
  have e (b : Bool) (f : Bool → β) : forceBool b f = f b := by cases b <;> rfl
  simp only [forcePool,force_eq,forceMap_eq,e]
  rfl
noncomputable def forcePools {β : Type} (u : Bool) (k : Nat) (ws : List Decor) (ps : List BoundPool) : (List QS → β) → β :=
  List.rec (fun f => f []) (fun p _ ih f => forcePool u k ws p fun q => ih fun qs => f (q::qs)) ps
theorem forcePools_eq {β : Type} (u k ws ps) (f : List QS → β) : forcePools u k ws ps f = f (ps.map (quickSpec u k ws)) := by
  induction ps generalizing f with
  | nil => rfl
  | cons p ps ih =>
    change forcePool u k ws p (fun q => forcePools u k ws ps fun qs => f (q::qs)) = _
    rw [forcePool_eq,ih]
    rfl
def kwN (v : Nat) : Nat :=
  let n := v % 18446744073709551557
  (n*(n+971)) % 18446744073709551557
abbrev Lane := NodeContext × Nat × Nat × List QS × List Nat × Nat
noncomputable def laneOf (c : NodeContext) : Lane :=
  let ws := c.2.2.1.map (fun w : Decor => w.1.toNat)
  (c,c.2.2.1.length,cond c.2.2.2.1.2 4 2,c.2.2.2.2.1.map (quickSpec c.2.2.2.1.2 (c.1-1) c.2.2.1),ws,(ws.map kwN).sum)
noncomputable def forceLanes {β : Type} (cs : List NodeContext) : (List Lane → β) → β :=
  List.rec (fun f => f []) (fun c _ ih f => force c.2.2.1.length fun n => force (cond c.2.2.2.1.2 4 2) fun l =>
    forceMap (fun w : Decor => w.1.toNat) c.2.2.1 fun ws => force (ws.map kwN).sum fun t =>
    forcePools c.2.2.2.1.2 (c.1-1) c.2.2.1 c.2.2.2.2.1 fun qs => ih fun ys => f ((c,n,l,qs,ws,t)::ys)) cs
theorem forceLanes_eq {β : Type} (cs) (f : List Lane → β) : forceLanes cs f = f (cs.map laneOf) := by
  induction cs generalizing f with
  | nil => rfl
  | cons c cs ih =>
    change force c.2.2.1.length (fun n => force (cond c.2.2.2.1.2 4 2) fun l =>
      forceMap (fun w : Decor => w.1.toNat) c.2.2.1 fun ws => force (ws.map kwN).sum fun t =>
      forcePools c.2.2.2.1.2 (c.1-1) c.2.2.1 c.2.2.2.2.1 fun qs => forceLanes cs fun ys => f ((c,n,l,qs,ws,t)::ys)) = _
    rw [force_eq,force_eq,forceMap_eq,force_eq,forcePools_eq,ih]
    rfl
noncomputable def fastCost (s : QS) (i j op : Nat) (ka kb : Bool) : Bool :=
  force (s.2.2.2.2.2.1.getD i 0) fun x => force (s.2.2.2.2.2.1.getD j 0) fun y =>
  let av := navail s.2.2.2.2.2.2.2 s.1 s.2.2.2.2.2.2.1
  let hi := Nat.add s.2.2.1 (Nat.sub (Nat.sub s.2.1 (nloss s.1 x ka)) (nloss s.1 y kb))
  let lo := s.2.2.2.1
  and (Nat.beq s.2.2.2.2.1 (Nat.add (cond ka 0 (cond (av x) 0 1)) (cond kb 0 (cond (av y) 0 1))))
  (cond (Nat.ble (Nat.succ lo) hi)
    (force (zN op x y) fun z => or (av z) (and (Nat.ble (Nat.add lo 2) hi) (and (av x) (av y))))
    (cond (Nat.ble lo hi) (nconst s.1 (zN op x y)) false))
theorem spec_get {d : Nat} (ws : List Decor) (i : Nat) (hd : nmask d zero=0) :
    (ws.map (fun w : Decor => nmask d w.1)).getD i 0 = nmask d (ws.getD i defaultDecor).1 := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases ws[i]? with
  | none => exact hd.symm
  | some v => rfl
theorem fast_slow {u k p ws i j op ka kb} (h : fastCost (quickSpec u k ws p) i j op ka kb=true) :
    slowCost u p ws k (ws.getD i defaultDecor) (ws.getD j defaultDecor) op ka kb=true := by
  have z0 : nmask p.domain.toNat zero=0 := by
    have : zero.toNat=0 := by simp [zero]
    simp [nmask,this]
  have su : (((ws.map (fun w : Decor => nmask p.domain.toNat w.1)).map fun m => cond (navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat)) m) 0 1).sum) =
      (ws.map (unav u p)).sum := by
    rw [List.map_map]
    refine congrArg List.sum (List.map_congr_left ?_)
    intro w _
    change cond (navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat)) (nmask p.domain.toNat w.1)) 0 1 = _
    rw [navail_eq]
    rfl
  simp only [fastCost,quickSpec,force_eq,spec_get _ _ z0,su,List.countP_map,Function.comp_def,nconst_eq] at h
  generalize ws.getD i defaultDecor=a at h ⊢
  generalize ws.getD j defaultDecor=b at h ⊢
  replace h : and (Nat.beq (ws.map (unav u p)).sum (Nat.add (cond ka 0 (cond ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat a.1)) 0 1)) (cond kb 0 (cond ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat b.1)) 0 1))))
   (cond (Nat.ble (Nat.succ (Nat.add k p.paid)) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w : Decor => isMaskedConstant p.domain w.1)) (nloss p.domain.toNat (nmask p.domain.toNat a.1) ka)) (nloss p.domain.toNat (nmask p.domain.toNat b.1) kb))))
    (or ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (zN op (nmask p.domain.toNat a.1) (nmask p.domain.toNat b.1))) (and (Nat.ble (Nat.add (Nat.add k p.paid) 2) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w : Decor => isMaskedConstant p.domain w.1)) (nloss p.domain.toNat (nmask p.domain.toNat a.1) ka)) (nloss p.domain.toNat (nmask p.domain.toNat b.1) kb)))) (and ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat a.1)) ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat b.1)))))
    (cond (Nat.ble (Nat.add k p.paid) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w : Decor => isMaskedConstant p.domain w.1)) (nloss p.domain.toNat (nmask p.domain.toNat a.1) ka)) (nloss p.domain.toNat (nmask p.domain.toNat b.1) kb)))) (nconst p.domain.toNat (zN op (nmask p.domain.toNat a.1) (nmask p.domain.toNat b.1))) false)) = true := h
  rw [zN_eq,nconst_eq,navail_eq,navail_eq,navail_eq,nloss_eq,nloss_eq] at h
  have ca : isMaskedConstant p.domain (bin op a.1 b.1)=true → availableB u p.domain p.wires (bin op a.1 b.1)=true := by
    intro zc
    simp only [availableB,isMaskedConstant,Bool.or_eq_true] at zc ⊢
    exact Or.inl (Or.inl zc)
  simp only [Nat.add_eq,Nat.sub_eq,Nat.succ_eq_add_one,Bool.and_eq_true,Nat.beq_eq] at h
  obtain ⟨hu,h⟩ := h
  simp only [slowCost,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq]
  refine ⟨⟨hu,?_⟩,?_⟩
  all_goals
    generalize ws.countP (fun w => isMaskedConstant p.domain w.1) - constantLoss (fun w : Decor => isMaskedConstant p.domain w.1) a ka -
      constantLoss (fun w : Decor => isMaskedConstant p.domain w.1) b kb = c at h ⊢
    generalize isMaskedConstant p.domain (bin op a.1 b.1)=r at h ca ⊢
    generalize availableB u p.domain p.wires (bin op a.1 b.1)=q at h ca ⊢
    cases h1 : Nat.ble (k+p.paid+1) (p.bound+c)
    · rw [h1] at h
      cases h2 : Nat.ble (k+p.paid) (p.bound+c)
      · simp [h2] at h
      · have := Nat.ble_eq.mp h2
        simp only [h2,cond_true,cond_false] at h
        subst h
        rw [ca rfl]
        simp <;> omega
    · rw [h1] at h
      have l1 := Nat.ble_eq.mp h1
      simp only [cond_true,Bool.or_eq_true,Bool.and_eq_true,Nat.ble_eq] at h
      rcases h with rfl | ⟨l2,ha,hb⟩
      · simp <;> omega
      · first
        | (have : (!q).toNat ≤ 1 := Bool.toNat_le _
           omega)
        | simp [ha,hb]
theorem anyEq_iff (m : Nat) (l : List Nat) : anyEq m l=true ↔ m ∈ l := by
  induction l with
  | nil => simp [anyEq]
  | cons a l ih =>
    change or (Nat.beq m a) (anyEq m l)=true ↔ _
    rw [Bool.or_eq_true,ih,Nat.beq_eq,List.mem_cons]
noncomputable def linkAt (fl : Nat → Option (List Nat)) (l : Lane) (i j op : Nat) (ka kb : Bool) : Bool :=
  force (l.2.2.2.2.1.getD i 0) fun x => force (l.2.2.2.2.1.getD j 0) fun y => force (zN op x y) fun z =>
  Option.rec false (fun ys => forceMap (fun v => v) ys fun ys =>
    and (anyEq z ys) (and (l.2.2.2.2.1.all fun v => or (and (not ka) (Nat.beq v x)) (or (and (not kb) (Nat.beq v y)) (anyEq v ys)))
      (ys.all fun v => or (Nat.beq v z) (and (and (or ka (not (Nat.beq v x))) (or kb (not (Nat.beq v y)))) (anyEq v l.2.2.2.2.1)))))
    (fl (Nat.add (kwN z) (Nat.sub (Nat.sub l.2.2.2.2.2 (cond ka 0 (kwN x))) (cond kb 0 (kwN y)))))
theorem keySet_sum (xs : List Sig) : keySet xs = (xs.map keyWord).sum := by
  have go (a : Nat) : xs.foldl (fun v x => v+keyWord x) a = a+(xs.map keyWord).sum := by
    induction xs generalizing a with
    | nil => rfl
    | cons x xs ih => rw [List.foldl_cons,ih,List.map_cons,List.sum_cons,Nat.add_assoc]
  exact (go 0).trans (Nat.zero_add _)
theorem delTwo_sum (f : Decor → Nat) {ws : List Decor} {a b : Decor} (ha : a ∈ ws) (hb : b ∈ ws) (ne : a≠b) (ka kb : Bool) :
    ((delTwo ws a b ka kb).map f).sum = (ws.map f).sum - (cond ka 0 (f a)) - (cond kb 0 (f b)) := by
  have er {l : List Decor} {x : Decor} (hx : x ∈ l) : (l.map f).sum = f x + ((l.erase x).map f).sum := by
    have := ((List.perm_cons_erase hx).map f).sum_eq
    rwa [List.map_cons,List.sum_cons] at this
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm ne)).mpr hb
  have e1 := er ha
  have e2 := er hb
  have e3 := er hm
  cases ka <;> cases kb <;> simp only [delTwo,delOne,Bool.false_eq_true,ite_true,ite_false,cond_true,cond_false] <;> omega
theorem fastCost_good {u p k ws a b op ka kb} (ha : a∈ws) (hb : b∈ws) (ne : a≠b) (al : allowedB u op=true)
    (h : slowCost u p ws k a b op ka kb=true) :
    scalarPoolCut u p k ((delTwo ws a b ka kb).map Prod.fst) (movedChoice op a b)=true := by
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let z := bin op a.1 b.1
  let rest := delTwo ws a b ka kb
  have ck := keptCount const ws a b ka kb
  change ws.countP const - constantLoss const a ka - constantLoss const b kb ≤ rest.countP const at ck
  simp only [slowCost,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at h
  obtain ⟨⟨hu,hc⟩,hz⟩ := h
  have sum := delTwo_sum (unav u p) ha hb ne ka kb
  rw [hu] at sum
  have zs : ((delTwo ws a b ka kb).map (unav u p)).sum=0 := by omega
  have hs : (rest.map Prod.fst).all (availableB u p.domain p.wires)=true := by
    apply List.all_eq_true.mpr
    intro _ hm
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hm
    have v := List.sum_eq_zero_iff.mp zs _ (List.mem_map_of_mem hw)
    cases e : availableB u p.domain p.wires w.1
    · simp [unav,e] at v
    · rfl
  have opOK : (!(!availableB u p.domain p.wires z) || choiceOK u p.domain p.wires (movedChoice op a b))=true := by
    simp only [Bool.or_eq_true,Bool.and_eq_true] at hz
    rcases hz with hz | ⟨x,y⟩
    · simp [z,hz]
    · simp [choiceOK,movedChoice,x,y,al]
  change k+p.paid+(!availableB u p.domain p.wires z).toNat < p.bound+(ws.countP const - constantLoss const a ka -
        constantLoss const b kb+(isMaskedConstant p.domain z).toNat) at hc
  dsimp only [rest] at hs
  have ez : choiceVal (movedChoice op a b)=z := rfl
  simp only [scalarPoolCut,ez,hs,opOK,Bool.and_true,decide_eq_true_eq,List.countP_cons,
      List.countP_map,Function.comp_def]
  change k+p.paid+(!availableB u p.domain p.wires z).toNat <
      p.bound+(rest.countP const + if isMaskedConstant p.domain z then 1 else 0)
  cases hc' : isMaskedConstant p.domain z <;> simp [hc'] at hc ⊢ <;> omega
theorem zN_full (op : Nat) (a b : Sig) : zN op a.toNat b.toNat = (bin op a b).toNat := by
  have e (v : Sig) : nmask one.toNat v = v.toNat := by
    rw [nmask_eq]
    congr 1
    exact BitVec.and_allOnes
  have := zN_eq op one a b
  rwa [e,e,e] at this
theorem getW (ws : List Decor) (i : Nat) :
    (ws.map (fun w : Decor => w.1.toNat)).getD i 0 = (ws.getD i defaultDecor).1.toNat := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases ws[i]? with
  | none =>
    have z0 : zero.toNat=0 := by simp [zero]
    exact z0.symm
  | some v => rfl
theorem wire_ne {c : NodeContext} {i j} (nd : (c.2.2.1.map Prod.fst).Nodup)
    (hi : i<c.2.2.1.length) (hj : j<c.2.2.1.length) (hij : i≠j) : (contextWire c i).1 ≠ (contextWire c j).1 := by
  have gi : contextWire c i = c.2.2.1[i] := by simp [contextWire,List.getD_eq_getElem?_getD,hi]
  have gj : contextWire c j = c.2.2.1[j] := by simp [contextWire,List.getD_eq_getElem?_getD,hj]
  rw [gi,gj]
  intro e
  apply hij
  apply (List.Nodup.getElem_inj_iff nd (hi:=by simpa using hi) (hj:=by simpa using hj)).mp
  simpa using e
theorem link_sound {c : NodeContext} {fl i j op ka kb} (nd : (c.2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ xs ∈ c.2.2.2.2.2 tag, ys=xs.map BitVec.toNat)
    (hi : i<c.2.2.1.length) (hj : j<c.2.2.1.length) (hij : i≠j) (h : linkAt fl (laneOf c) i j op ka kb=true) :
    (c.2.2.2.2.2 (keySet (choiceVal (movedChoice op (contextWire c i) (contextWire c j)) ::
      (delTwo c.2.2.1 (contextWire c i) (contextWire c j) ka kb).map Prod.fst))).any (sameWords
      (choiceVal (movedChoice op (contextWire c i) (contextWire c j)) ::
      (delTwo c.2.2.1 (contextWire c i) (contextWire c j) ka kb).map Prod.fst))=true := by
  have mem (t) (ht : t<c.2.2.1.length) : contextWire c t ∈ c.2.2.1 := by
    simp [contextWire,List.getD_eq_getElem?_getD,ht]
  have hne := wire_ne nd hi hj hij
  have ha := mem i hi
  have hb := mem j hj
  have hab : contextWire c i ≠ contextWire c j := fun e => hne (congrArg Prod.fst e)
  have kv (v : Sig) := kept_value nd ha hb ka kb v
  have sum := delTwo_sum (fun w : Decor => keyWord w.1) ha hb hab ka kb
  have wi : contextWire c i = c.2.2.1.getD i defaultDecor := rfl
  have wj : contextWire c j = c.2.2.1.getD j defaultDecor := rfl
  simp only [linkAt,laneOf,force_eq,getW,←wi,←wj,zN_full] at h
  generalize contextWire c i=a at *
  generalize contextWire c j=b at *
  change Option.rec false _ (fl (keyWord (bin op a.1 b.1)+(((c.2.2.1.map (fun w : Decor => w.1.toNat)).map kwN).sum -
    (cond ka 0 (keyWord a.1)) - (cond kb 0 (keyWord b.1)))))=true at h
  have tot : ((c.2.2.1.map (fun w : Decor => w.1.toNat)).map kwN).sum = (c.2.2.1.map (fun w : Decor => keyWord w.1)).sum := by
    rw [List.map_map]
    rfl
  rw [tot,←sum] at h
  have tag : keySet (choiceVal (movedChoice op a b) :: (delTwo c.2.2.1 a b ka kb).map Prod.fst) =
      keyWord (bin op a.1 b.1)+((delTwo c.2.2.1 a b ka kb).map (fun w : Decor => keyWord w.1)).sum := by
    rw [keySet_sum,List.map_cons,List.sum_cons,List.map_map]
    rfl
  rw [←tag] at h
  generalize keySet (choiceVal (movedChoice op a b) :: (delTwo c.2.2.1 a b ka kb).map Prod.fst)=t at h ⊢
  cases hf : fl t with
  | none => simp [hf] at h
  | some ys =>
    obtain ⟨xs,hx,rfl⟩ := hfl t ys hf
    rw [hf] at h
    simp only [forceMap_eq,List.map_id',Bool.and_eq_true,List.all_eq_true,Bool.or_eq_true,anyEq_iff,Nat.beq_eq,Bool.not_eq_true'] at h
    obtain ⟨h1,h2,h3⟩ := h
    have back {v : Sig} (hv : v.toNat ∈ xs.map BitVec.toNat) : v ∈ xs := by
      obtain ⟨w,hw,e⟩ := List.mem_map.mp hv
      exact BitVec.toNat_inj.mp e ▸ hw
    apply List.any_eq_true.mpr
    refine ⟨xs,hx,?_⟩
    simp only [sameWords,Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq]
    constructor
    · intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact back h1
      · obtain ⟨hw,va,vb⟩ := (kv v).mp hv
        obtain ⟨w,hm,rfl⟩ := List.mem_map.mp hw
        rcases h2 _ (List.mem_map_of_mem hm) with ⟨x,y⟩ | ⟨x,y⟩ | x
        · rcases va with va | va
          · exact absurd (BitVec.toNat_inj.mp y) va
          · simp [va] at x
        · rcases vb with vb | vb
          · exact absurd (BitVec.toNat_inj.mp y) vb
          · simp [vb] at x
        · exact back x
    · intro v hv
      rcases h3 _ (List.mem_map_of_mem hv) with x | ⟨⟨x,y⟩,m⟩
      · exact List.mem_cons.mpr (Or.inl (BitVec.toNat_inj.mp x))
      · refine List.mem_cons_of_mem _ ((kv v).mpr ⟨?_,?_,?_⟩)
        · obtain ⟨w,hw,e⟩ := List.mem_map.mp m
          exact BitVec.toNat_inj.mp e ▸ List.mem_map_of_mem hw
        · rcases x with x | x
          · exact Or.inr x
          · refine Or.inl fun e => ?_
            subst e
            simp at x
        · rcases y with x | x
          · exact Or.inr x
          · refine Or.inl fun e => ?_
            subst e
            simp at x
noncomputable def fallbackAt (fl : Nat → Option (List Nat)) (l : Lane) (i j op : Nat) (ka kb : Bool) : Bool :=
  or (and (and (Nat.ble (Nat.succ i) l.2.1) (and (Nat.ble (Nat.succ j) l.2.1) (and (Nat.ble (Nat.succ op) l.2.2.1) (not (Nat.beq i j)))))
    (or (l.2.2.2.1.any fun s => fastCost s i j op ka kb) (linkAt fl l i j op ka kb))) (checkAt l.1 i j op ka kb)
theorem fallback_sound {c : NodeContext} {fl i j op ka kb} (nd : (c.2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ xs ∈ c.2.2.2.2.2 tag, ys=xs.map BitVec.toNat)
    (h : fallbackAt fl (laneOf c) i j op ka kb=true) :
    checkAt c i j op ka kb=true := by
  simp only [fallbackAt,Bool.or_eq_true,Bool.and_eq_true] at h
  rcases h with ⟨⟨hi,hj,ho,hn⟩,h | h⟩ | h
  · have hi := Nat.ble_eq.mp hi
    have hj := Nat.ble_eq.mp hj
    have ho := Nat.ble_eq.mp ho
    change Nat.succ i ≤ c.2.2.1.length at hi
    change Nat.succ j ≤ c.2.2.1.length at hj
    change Nat.succ op ≤ cond c.2.2.2.1.2 4 2 at ho
    have al : allowedB c.2.2.2.1.2 op=true := by
      cases hu : c.2.2.2.1.2 <;> simp [hu] at ho <;> simp [allowedB] <;> omega
    have mem (t) (ht : t<c.2.2.1.length) : contextWire c t ∈ c.2.2.1 := by
      simp [contextWire,List.getD_eq_getElem?_getD,ht]
    obtain ⟨_,hm,ok⟩ := List.any_eq_true.mp h
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm
    have hne := wire_ne nd hi hj (fun e => by simp [e] at hn)
    have closed := fastCost_good (mem i hi) (mem j hj) (fun e => hne (congrArg Prod.fst e)) al (fast_slow ok)
    have cut : c.2.2.2.2.1.any (fun p => scalarPoolCut c.2.2.2.1.2 p (c.1-1)
        ((delTwo c.2.2.1 (contextWire c i) (contextWire c j) ka kb).map Prod.fst)
        (movedChoice op (contextWire c i) (contextWire c j)))=true :=
      List.any_eq_true.mpr ⟨p,hp,closed⟩
    simp only [checkAt,evalMove,closeChild,cut,Bool.or_true]
    repeat' split
    all_goals rfl
  · have cut := link_sound nd hfl (Nat.ble_eq.mp hi) (Nat.ble_eq.mp hj) (fun e => by simp [e] at hn) h
    simp only [checkAt,evalMove,closeChild,cut,Bool.true_or]
    repeat' split
    all_goals rfl
  · exact h
def swapIdx (v t : Nat) : Nat := cond (Nat.beq t (v &&& 15)) (v >>> 4) (cond (Nat.beq t (v >>> 4)) (v &&& 15) t)
def validSwap (v : Nat) : Bool := and (Nat.ble ((v &&& 15)+1) (v >>> 4)) (Nat.ble ((v >>> 4)+1) 9)
set_option maxRecDepth 8192 in
theorem swap_table : ∀ v : Fin 144, validSwap v.val=true → ∀ t : Fin 9, swapIdx v.val t.val<9 ∧
    wordMove (swapRows v.val) (inputs.getD t.val zero) = inputs.getD (swapIdx v.val t.val) zero := by decide +kernel
theorem swap_input {v t : Nat} (hv : validSwap v=true) (ht : t<9) : swapIdx v t<9 ∧
    wordMove (swapRows v) (inputs.getD t zero) = inputs.getD (swapIdx v t) zero := by
  have lt : v<144 := by
    simp only [validSwap,Bool.and_eq_true,Nat.ble_eq,Nat.shiftRight_eq_div_pow] at hv
    omega
  exact swap_table ⟨v,lt⟩ hv ⟨t,ht⟩
def idxOf (perm : List Nat) (t : Nat) : Nat := perm.foldl (fun t v => swapIdx v t) t
theorem idx_move {perm : List Nat} (ok : perm.all validSwap=true) {t : Nat} (ht : t<9) :
    movedWord (perm.map swapRows).reverse (inputs.getD t zero) = inputs.getD (idxOf perm t) zero := by
  rw [movedWord,List.foldr_reverse,List.foldl_map]
  induction perm generalizing t with
  | nil => rfl
  | cons v perm ih =>
    simp only [List.all_cons,Bool.and_eq_true] at ok
    obtain ⟨lt,e⟩ := swap_input ok.1 ht
    rw [List.foldl_cons,e,ih ok.2 lt]
    rfl
noncomputable def decodeN : Nat → Nat → List Nat → List Nat
  | 0,_,ws => ws
  | n+1,bits,ws => force (zN ((bits >>> 8) &&& 3) (ws.getD (bits &&& 15) 0) (ws.getD ((bits >>> 4) &&& 15) 0))
      fun z => decodeN n (bits >>> 10) (ws++[z])
theorem decodeN_eq (F : Sig → Nat) (F0 : F zero=0) (Fb : ∀ op a b, F (bin op a b)=zN op (F a) (F b))
    (n bits : Nat) (ds : List Decor) :
    (decodeBank n bits ds).map (fun w => F w.1) = decodeN n bits (ds.map fun w => F w.1) := by
  have gd (ds : List Decor) (i : Nat) : (ds.map fun w => F w.1).getD i 0 = F (ds.getD i defaultDecor).1 := by
    simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
    cases ds[i]? with
    | none => exact F0.symm
    | some v => rfl
  induction n generalizing bits ds with
  | zero => rfl
  | succ n ih =>
    rw [decodeN,force_eq,decodeBank,ih,gd,gd,←Fb,List.map_append]
    rfl
theorem selectLive_map {α β : Type} (f : α → β) (bits : Nat) (ws : List α) :
    (selectLive bits ws).map f = selectLive bits (ws.map f) := by
  induction ws generalizing bits with
  | nil => rfl
  | cons w ws ih =>
    rw [List.map_cons,selectLive,selectLive]
    split
    · rw [List.map_cons,ih]
    · exact ih _
noncomputable def fastState (g : Forest) (k i : Nat) (perm : List Nat) : List Nat :=
  let raw := (selected g.mask).map fun e => (inputs.getD (idxOf perm e.1) zero).toNat
  let (_,depth,_,_,_,_,_,data) := g.levels k
  let len := 10*depth
  force (packedAt data (i*(len+(selected g.mask).length+depth)) (len+(selected g.mask).length+depth)) fun rec =>
  selectLive (rec >>> len) (decodeN depth (rec &&& ((1 <<< len)-1)) raw)
theorem fastState_eq (g : Forest) (k i : Nat) {perm : List Nat} (ok : perm.all validSwap=true) :
    fastState g k i perm = ((stateSet g k i).map (movedWord (perm.map swapRows).reverse)).map BitVec.toNat := by
  let ms := (perm.map swapRows).reverse
  let F (a : Sig) : Nat := (movedWord ms a).toNat
  have F0 : F zero=0 := by
    change (movedWord ms zero).toNat=0
    rw [moved_eq_rename,(rename_constants _).1]
    simp [zero]
  have Fb (op a b) : F (bin op a b)=zN op (F a) (F b) := by
    change (movedWord ms (bin op a b)).toNat = zN op (movedWord ms a).toNat (movedWord ms b).toNat
    rw [zN_full,moved_eq_rename,rename_bin,moved_eq_rename,moved_eq_rename]
  have raw : (wiresOf g).map (fun w => F w.1) = (selected g.mask).map fun e => (inputs.getD (idxOf perm e.1) zero).toNat := by
    simp only [wiresOf,rawDecor,List.map_map]
    apply List.map_congr_left
    rintro ⟨j,a⟩ hm
    obtain ⟨hj,rfl⟩ := selected_entry hm
    exact congrArg BitVec.toNat (idx_move ok hj)
  have len : (wiresOf g).length = (selected g.mask).length := by simp [wiresOf,rawDecor]
  unfold fastState stateSet readNode
  rcases g.levels k with ⟨a,depth,b,c,d,e,f,data⟩
  simp only [force_eq,storedDepth,len]
  rw [List.map_map,List.map_map,selectLive_map,←raw,←decodeN_eq F F0 Fb]
  rfl
noncomputable def linkedFast (g : Forest) (k : Nat) (pair : Nat × Nat) : Option (List Nat) :=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.autos[pair.2]?).bind fun perm => cond (perm.all validSwap) (some (fastState g k pair.1 perm)) none
noncomputable def flOf (g : Forest) (k : Nat) : Nat → Option (List Nat) := fun tag => (g.index k tag).bind (linkedFast g (k-1))
noncomputable def batchMove (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) (i j op : Nat) (ka kb : Bool) :=
  let (k,n,r,_,cov) := b
  let len := 1+(n-(if ka then 0 else 1)-(if kb then 0 else 1))
  if len>k then true else
    let a := laneWire b i
    let b' := laneWire b j
    let z := packedOp op a b'
    let mask := fullMarks r (takePacked cov (packedColumn (!u) a) (packedColumn (!u) b') ka kb ||| packedColumn (!u) z)
    onMarks (fun c => fallbackAt fl c i j op ka kb) mask xs
theorem batchMove_at {fl u} (k n) (xs : List NodeContext) {i j op : Nat} {ka kb}
    (hi : i<n) (hj : j<n) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (mode : xs[q].2.2.2.1.2=u) (nd : (xs[q].2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat)
    (pass : batchMove fl u (makeBatch k n xs) (xs.map laneOf) i j op ka kb=true) :
    checkAt xs[q] i j op ka kb=true := by
  let len := 1+(n-(if ka then 0 else 1)-(if kb then 0 else 1))
  have eval : checkAt xs[q] i j op ka kb =
      if len>k then true else if combField xs[q] (!u) ka kb op i j != BitVec.allOnes 416 then true
      else if !properB (dbin op (contextWire xs[q] i) (contextWire xs[q] j)).1 ||
        xs[q].2.2.1.any (fun v => v.1==(dbin op (contextWire xs[q] i) (contextWire xs[q] j)).1)
      then true else closeChild u xs[q].2.2.2.2.1 xs[q].2.2.2.2.2 (k-1)
        ((delTwo xs[q].2.2.1 (contextWire xs[q] i) (contextWire xs[q] j) ka kb).map Prod.fst)
        (movedChoice op (contextWire xs[q] i) (contextWire xs[q] j)) := by
    simp only [checkAt,evalMove,budget,arity,mode,len,combField] <;> rfl
  by_cases small : len>k
  · simp [eval,small]
  · let r := units xs.length
    let a := laneWire (makeBatch k n xs) i
    let b := laneWire (makeBatch k n xs) j
    let cov := packedCov (fun c : NodeContext => c.2.2.2.1.1) xs
    change (if len>k then true else onMarks _ (fullMarks r
       (takePacked cov (packedColumn (!u) a) (packedColumn (!u) b) ka kb |||
        packedColumn (!u) (packedOp op a b))) (xs.map laneOf)) = true at pass
    rw [if_neg small] at pass
    have ca : a = _ := laneWire_at k n xs hi
    have cb : b = _ := laneWire_at k n xs hj
    dsimp only [r,cov] at pass
    rw [ca,cb,packed_op,packed_column,packed_column,packed_column,takePacked_ok,lanes_or] at pass
    by_cases hit : combField xs[q] (!u) ka kb op i j = BitVec.allOnes 416
    · apply fallback_sound nd hfl
      have m := marked_ok _ _ _ q (by simpa using hq) (by
        rw [mark_at _ _ _ hq]
        exact beq_iff_eq.mpr hit) pass
      simpa only [List.getElem_map] using m
    · rw [eval,if_neg small,if_pos (bne_iff_ne.mpr hit)]
noncomputable def batchPair (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) (i j op : Nat) :=
  let f := batchMove fl u b xs i j op
  f false false && f true false && f false true && f true true
noncomputable def batchRow (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) (i : Nat) (js : List Nat) :=
    js.all (fun j => (opsOf u).all (batchPair fl u b xs i j))
noncomputable def batchRows (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) : List Nat → Bool
  | [] => true
  | i::js => batchRow fl u b xs i js && batchRows fl u b xs js
theorem batchRows_at {fl u} (k n) (xs : List NodeContext) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (mode : xs[q].2.2.2.1.2=u) (nd : (xs[q].2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat)
    (js : List Nat)
    (bounds : ∀ j ∈ js, j<n) (allRows : batchRows fl u (makeBatch k n xs) (xs.map laneOf) js=true) :
    testAll xs[q] (js.map (contextWire xs[q])) = true := by
  induction js with
  | nil => rfl
  | cons i js ih =>
    simp only [batchRows,Bool.and_eq_true,batchRow,List.all_eq_true] at allRows
    simp only [List.map_cons,testAll,testRow,Bool.and_eq_true,List.all_eq_true,List.mem_map]
    have hi := bounds i List.mem_cons_self
    refine ⟨?_,ih (fun j hj => bounds j (List.mem_cons_of_mem _ hj)) allRows.2⟩
    rintro _ ⟨j,hj,rfl⟩ op hop
    have hj' := bounds j (List.mem_cons_of_mem _ hj)
    rw [mode] at hop
    have pass := allRows.1 j hj op hop
    have check := @batchMove_at fl u k n xs i j op
    simp only [batchPair,Bool.and_eq_true] at pass
    simp only [testPair,Bool.and_eq_true]
    exact ⟨⟨⟨check hi hj' hq budget arity mode nd hfl pass.1.1.1,check hi hj' hq budget arity mode nd hfl pass.1.1.2⟩,
      check hi hj' hq budget arity mode nd hfl pass.1.2⟩,check hi hj' hq budget arity mode nd hfl pass.2⟩
noncomputable def runBatch (fl : Nat → Option (List Nat)) (u : Bool) (k n : Nat) (xs : List NodeContext) :=
    batchRows fl u (makeBatch k n xs) (xs.map laneOf) (List.range n)
theorem runBatch_at {fl u k n} {xs : List NodeContext} {q} (hq : q<xs.length)
    (hb : xs[q].1=k) (ha : xs[q].2.1=n) (hm : xs[q].2.2.2.1.2=u) (nd : (xs[q].2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat)
    (hn : xs[q].2.2.1.length=n)
    (pass : runBatch fl u k n xs=true) : testAll xs[q] xs[q].2.2.1=true := by
  have all := batchRows_at k n xs hq hb ha hm nd hfl (List.range n) (fun _ => List.mem_range.mp) pass
  have eq : (List.range n).map (contextWire xs[q]) = xs[q].2.2.1 := by
    apply List.ext_getElem
    · simp [hn]
    · intro i h1 h2
      simp [contextWire,List.getD_eq_getElem?_getD,h2]
  rwa [eq] at all
def contextOf (g : Forest) (k i : Nat) : NodeContext :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let start := num*(10*storedDepth g depth+raw.length+depth)
  let pos := start+num*offw+packedAt data (start+i*offw) offw
  let nr := packedAt data pos 5
  let nl := packedAt data (pos+5) lw
  let st := pos+5+lw
  let rules := (getPairs data cw depth nr st).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  (k,ws.length,ws,preCov g.mode ws,rules,ls)
theorem flOf_ok (g : Forest) (k i tag : Nat) (ys) (h : flOf g k tag=some ys) :
    ∃ xs ∈ (contextOf g k i).2.2.2.2.2 tag, ys=xs.map BitVec.toNat := by
  change ∃ xs ∈ ((g.index k tag).bind (linkedSet g (k-1))).toList, _
  unfold flOf at h
  cases hp : g.index k tag with
  | none => simp [hp] at h
  | some pair =>
    simp only [hp,Option.bind_some,linkedFast] at h
    simp only [Option.bind_some,linkedSet]
    split at h
    · contradiction
    next v =>
      cases ha : g.autos[pair.2]? with
      | none => simp [ha] at h
      | some perm =>
        simp only [ha,Option.bind_some] at h
        cases hv : perm.all validSwap with
        | false => simp [hv] at h
        | true =>
          simp only [hv,cond_true,Option.some.injEq] at h
          refine ⟨(stateSet g (k-1) pair.1).map (movedWord (perm.map swapRows).reverse),?_,?_⟩
          · simp [v]
          · exact h.symm.trans (fastState_eq g _ _ hv)
def prelim (T : Sig) (c : NodeContext) :=
  let ws := c.2.2.1.map Prod.fst
  decide ws.Nodup && !(ws.contains T)
theorem from_context (g : Forest) (k i : Nat) :
    nodeVerified g k i = (prelim (targetOf g) (contextOf g k i) &&
      (if k=0 then true else testAll (contextOf g k i) (contextOf g k i).2.2.1)) := rfl
theorem makeBlock {g k start n} (h : ∀ (i : Nat), start ≤ i → i < start + n → nodeVerified g k i = true) :
    block g k start n=true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [block,Bool.and_eq_true]
    exact ⟨h _ (by omega) (by omega),ih (fun i le lt => h i le (by omega))⟩
def contexts (g : Forest) (k start n : Nat) :=
  ((List.range n).map (start+·)).map (contextOf g k)
def header (g : Forest) (k start n ar : Nat) :=
  (contexts g k start n).all (fun c => c.2.1==ar && prelim (targetOf g) c)
noncomputable def forceSignals {β : Type} (sigs : List PackedSig)
    (cont : List PackedSig → β) : β :=
  match sigs with
  | [] => cont []
  | (pos, neg)::tail =>
    force pos fun pos => force neg fun neg =>
    forceSignals tail fun rest => cont ((pos, neg)::rest)
theorem forceSignals_eq {β : Type} (sigs : List PackedSig)
    (cont : List PackedSig → β) : forceSignals sigs cont = cont sigs := by
  induction sigs generalizing cont with
  | nil => rfl
  | cons sig sigs ih =>
    obtain ⟨pos, neg⟩ := sig
    simp only [forceSignals, force_eq, ih]
noncomputable def forceBatch {β : Type} (b : Batch) (cont : Batch → β) : β :=
  let (k,n,count,sigs,any,once,twice) := b
  force count fun count => forceSignals sigs fun sigs =>
    force any fun any => force once fun once => force twice fun twice =>
    cont (k,n,count,sigs,any,once,twice)
theorem forceBatch_eq {β : Type} (b : Batch)
    (cont : Batch → β) : forceBatch b cont = cont b := by
  obtain ⟨k,n,count,sigs,any,once,twice⟩ := b
  simp only [forceBatch, force_eq, forceSignals_eq]
noncomputable def rowCut (g : Forest) (k start n ar lo len : Nat) :=
  let xs := contexts g k start n
  forceBatch (makeBatch k ar xs) fun b =>
    forceLanes xs fun ys => (List.range len).all (fun d =>
      let i := lo+d
      batchRow (flOf g k) g.mode b ys i (List.range' (i+1) (ar-(i+1))))
theorem rowCut_at {g k start n ar lo len} (h : rowCut g k start n ar lo len=true)
    (i : Nat) (l : lo ≤ i) (r : i < lo+len) :
    batchRow (flOf g k) g.mode (makeBatch k ar (contexts g k start n)) ((contexts g k start n).map laneOf)
      i (List.range' (i+1) (ar-(i+1)))=true := by
  simp only [rowCut,forceBatch_eq,forceLanes_eq] at h
  have ha := List.all_eq_true.mp h (i-lo) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le l] using ha
theorem rowCut_merge {g k start n ar lo a b}
    (h : rowCut g k start n ar lo a=true) (t : rowCut g k start n ar (lo+a) b=true) :
    rowCut g k start n ar lo (a+b)=true := by
  simp only [rowCut,forceBatch_eq,forceLanes_eq]
  apply List.all_eq_true.mpr
  intro j hj
  have jlt := List.mem_range.mp hj
  by_cases first : j<a
  · exact rowCut_at h (lo+j) (by omega) (by omega)
  · exact rowCut_at t (lo+j) (by omega) (by omega)
theorem cutsRun {g k start n ar} (h : rowCut g k start n ar 0 ar=true) :
    runBatch (flOf g k) g.mode k ar (contexts g k start n)=true := by
  let xs := contexts g k start n
  have go (lo num : Nat) (eq : lo+num=ar) :
      batchRows (flOf g k) g.mode (makeBatch k ar xs) (xs.map laneOf) (List.range' lo num)=true := by
    induction num generalizing lo with
    | zero => rfl
    | succ num ih =>
      simp only [List.range'_succ,batchRows,Bool.and_eq_true]
      refine ⟨?_,ih (lo+1) (by omega)⟩
      have ok := rowCut_at h lo (by omega) (by omega)
      simpa only [show ar-(lo+1)=num by omega] using ok
  unfold runBatch
  rw [List.range_eq_range']
  exact go 0 ar (by omega)
theorem cutsBlock {g k start n ar} (hd : header g k start n ar=true)
    (h : rowCut g k start n ar 0 ar=true) : block g k start n=true := by
  apply makeBlock
  intro i lo hi
  let xs := contexts g k start n
  have hm : contextOf g k i ∈ xs := by
    apply List.mem_map.mpr
    exact ⟨i,List.mem_map.mpr ⟨i-start,List.mem_range.mpr (by omega),by omega⟩,rfl⟩
  obtain ⟨q,hq,e⟩ := List.getElem_of_mem hm
  have one := List.all_eq_true.mp hd _ hm
  simp only [Bool.and_eq_true,beq_iff_eq] at one
  have hb : xs[q].1=k := by rw [e]; rfl
  have ha : xs[q].2.1=ar := e ▸ one.1
  have nd : (xs[q].2.2.1.map Prod.fst).Nodup := by
    have p := one.2
    simp only [prelim,Bool.and_eq_true,decide_eq_true_eq] at p
    rw [e]
    exact p.1
  have hfl : ∀ tag ys, flOf g k tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat := by
    rw [e]
    exact fun tag ys h => flOf_ok g k i tag ys h
  have hm : xs[q].2.2.2.1.2=g.mode := by rw [e]; rfl
  have hn : xs[q].2.2.1.length=ar := by rw [e]; exact one.1
  rw [from_context,Bool.and_eq_true]
  refine ⟨one.2,?_⟩
  split
  · rfl
  · exact e ▸ runBatch_at hq hb ha hm nd hfl hn (cutsRun h)
def boxes (g : Forest) (k start n ar lo num : Nat) : Nat → Prop
  | 0 => rowCut g k start n ar lo num=true
  | d+1 => boxes g k start n ar lo (num/2) d ∧ boxes g k start n ar (lo+num/2) (num-num/2) d
theorem boxesCut {g k start n ar lo num d} (h : boxes g k start n ar lo num d) :
    rowCut g k start n ar lo num=true := by
  induction d generalizing lo num with
  | zero => exact h
  | succ d ih =>
    have v := rowCut_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self num 2)] using v
def cells (g : Forest) (k start n ar rows : Nat) : Nat → Prop
  | 0 => header g k start n ar=true ∧ boxes g k start n ar 0 ar rows
  | d+1 => cells g k start (n/2) ar rows d ∧ cells g k (start+n/2) (n-n/2) ar rows d
theorem cellsBlock {g k start n ar rows d} (h : cells g k start n ar rows d) :
    block g k start n=true := by
  induction d generalizing start n with
  | zero => exact cutsBlock h.1 (boxesCut h.2)
  | succ d ih =>
    have v := block_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self n 2)] using v
def padSamples (n a : Nat) : Bits :=
  BitVec.ofNat _ (if a.testBit 0 then a ||| (((1 <<< 416)-1) ^^^ ((1 <<< n)-1)) else a)
def sampleAt (n : Nat) (data : Array (Nat × Nat)) (i : Nat) : Bits × Bits :=
  let p := data[i]?.getD (0,0)
  (padSamples n p.1,padSamples n p.2)
def mixTag (h : Nat) : Nat := (h*(OfNat.ofNat (limbs [0x1a87977,0x4372ca15cbdcab1f])))%(OfNat.ofNat (limbs [0x1ffffff,0xffffffffffffffff]))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls17 : Lower true (vars 17) (graphGoal 17) 1 := size_of (hints:=4) (by decide +kernel)
def es17 := extendKnown [] 1 [(17,[]),(34,[84,16]),(65,[101,100]),(66,[101,100,16]),(68,[101,33,100,32]),(129,[118,117,116]),(136,[118,117,50,49,116,48]),(144,[118,117,115,114,113,116,64]),(260,[135,134,133,33,132,32]),(264,[135,134,133,50,49,132,48]),(288,[135,134,83,82,81,132,80])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs17 : Known true es17 := extendKnown_ok (m:=17) baseKnown ls17 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls67 : Lower true (vars 67) (graphGoal 67) 2 := size_of (hints:=102) (by decide +kernel)
def es67 := extendKnown es17 2 [(67,[]),(69,[33]),(70,[33,16]),(81,[67,66,100,97,64]),(98,[84,83,82,97,80]),(137,[50,118,49]),(152,[67,50,118,65,48]),(193,[117,116,115,114,113,96]),(268,[135,134,49,32]),(290,[135,133,132,131,130,101,129,16]),(292,[135,84,83,134,81,32]),(296,[135,84,83,50,134,81,48]),(324,[135,133,132,131,98,129,96]),(392,[117,116,131,114,99,129,112])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs67 : Known true es67 := extendKnown_ok (m:=67) vs17 ls67 (by decide +kernel)
def s145S := sampleAt 9 #[(0x3f,0x49),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x1c7,0x92),(0x0,0x0),(0x0,0x0),(0x1f8,0x124),(0x0,0x0)]
def s145C : List ColumnInfo := []
def s145D3 (_ : Nat) : Nat := 0x7
def s145L : Nat → Packing
  | 3 => (1,0,1,0,0,1,0,s145D3)
  | _ => emptyPacking
def s145I : Nat → Nat → Option (Nat × Nat)
  | _,_ => none
def s145 : Forest := ⟨145,3,s145S,s145C,[[],[116],[64],[64,112],[112,64],[112]],s145L,s145I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs145_3_0 : block s145 3 0 1 = true := by
  apply cellsBlock (ar:=3) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs145_3 : block s145 3 0 1 = true := bs145_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts145 : checkedTables s145 3 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · exact bs145_3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs145 : graphValid s145 (boundsBefore es67) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls145 : Lower true (vars 145) (graphGoal 145) 4 := lower_forest (g:=s145) (i:=0) (hints:=4) (before_sound es67 vs67) gs145 ts145 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es145 := extendKnown es67 4 [(145,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs145 : Known true es145 := extendKnown_ok (m:=145) vs67 ls145 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls51 : Lower true (vars 51) (graphGoal 51) 3 := size_of (hints:=1048660) (by decide +kernel)
def es51 := extendKnown es145 3 [(51,[]),(163,[118,116]),(170,[118,50,116,117,49,16]),(178,[118,115,114,116,117,65,16]),(202,[50,100,117,49,16]),(204,[100,117,49,32]),(210,[99,98,100,117,65,16]),(212,[99,100,117,65,32]),(277,[135,134,133,33]),(281,[135,134,50,133,49]),(305,[135,134,131,130,133,81]),(329,[135,50,100,133,49]),(330,[135,50,100,133,49,16]),(353,[135,134,131,130,100,133,81]),(389,[135,118,116,133,33]),(404,[134,131,132,117,65,32]),(417,[134,131,130,116,133,81]),(432,[135,118,131,114,116,133,81,64])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs51 : Known true es51 := extendKnown_ok (m:=51) vs145 ls51 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls71 : Lower true (vars 71) (graphGoal 71) 3 := size_of (hints:=1638) (by decide +kernel)
def es71 := extendKnown es51 3 [(71,[]),(300,[135,84,83,134,82,49,32])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs71 : Known true es71 := extendKnown_ok (m:=71) vs51 ls71 (by decide +kernel)
def s83S := sampleAt 21 #[(0x60fff,0x221a3),(0x1bf060,0xa736a),(0x0,0x0),(0x0,0x0),(0x1c007f,0x1d4a5c),(0x0,0x0),(0x1fff80,0x158c10),(0x0,0x0),(0x0,0x0)]
def s83C : List ColumnInfo := []
def s83D3 (_ : Nat) : Nat := 0xf
def s83L : Nat → Packing
  | 3 => (1,0,1,0,0,1,0,s83D3)
  | _ => emptyPacking
def s83I : Nat → Nat → Option (Nat × Nat)
  | _,_ => none
def s83 : Forest := ⟨83,3,s83S,s83C,[[],[96,65]],s83L,s83I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs83_3_0 : block s83 3 0 1 = true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs83_3 : block s83 3 0 1 = true := bs83_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts83 : checkedTables s83 3 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · exact bs83_3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs83 : graphValid s83 (boundsBefore es71) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls83 : Lower true (vars 83) (graphGoal 83) 4 := lower_forest (g:=s83) (i:=0) (hints:=100) (before_sound es71 vs71) gs83 ts83 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es83 := extendKnown es71 4 [(83,[]),(85,[33]),(99,[84,16]),(102,[32,84,33]),(195,[117,116]),(197,[117,116,33]),(201,[117,50,118,100,49]),(294,[135,133,130,101,128,66]),(298,[135,133,131,130,101,128,67]),(325,[135,133,32,132,16]),(326,[135,133,32,132]),(332,[135,133,134,32,100,49]),(354,[135,83,82,80,132,97]),(356,[135,83,134,32,100,81]),(393,[135,133,50,118,48,132,16]),(396,[117,50,134,48,116,33]),(408,[135,133,131,50,118,48,132,65]),(424,[83,50,134,48,116,81])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs83 : Known true es83 := extendKnown_ok (m:=83) vs71 ls83 (by decide +kernel)
def s153S := sampleAt 21 #[(0x87ff,0x191a3),(0x0,0x0),(0x0,0x0),(0x10f860,0x15bb6a),(0x1f007f,0x16224c),(0x0,0x0),(0x0,0x0),(0x1fff80,0x84410),(0x0,0x0)]
def s153C : List ColumnInfo := [(8,0,145,512,4)]
def s153D4 (_ : Nat) : Nat := 0x2f
def s153L : Nat → Packing
  | 4 => (1,0,1,0,0,1,0,s153D4)
  | _ => emptyPacking
def s153I : Nat → Nat → Option (Nat × Nat)
  | _,_ => none
def s153 : Forest := ⟨153,4,s153S,s153C,[[],[64]],s153L,s153I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs153_4_0 : block s153 4 0 1 = true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs153_4 : block s153 4 0 1 = true := bs153_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts153 : checkedTables s153 4 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs153_4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs153 : graphValid s153 (boundsBefore es83) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls153 : Lower true (vars 153) (graphGoal 153) 5 := lower_forest (g:=s153) (i:=0) (hints:=28676) (before_sound es83 vs83) gs153 ts153 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es153 := extendKnown es83 5 [(153,[]),(209,[101,116,64,99])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs153 : Known true es153 := extendKnown_ok (m:=153) vs83 ls153 (by decide +kernel)
def s87S := sampleAt 36 #[(0x6820ffff,0x28a21aa3),(0x9b03f0660,0x8b1a7366a),(0xe3fc00780,0xa39c6378a),(0x0,0x0),(0xfc00007ff,0xfc514a55c),(0x0,0x0),(0xffffff800,0x54618c010),(0x0,0x0),(0x0,0x0)]
def s87C : List ColumnInfo := [(4,0,83,512,4)]
def s87D4 (_ : Nat) : Nat := 0x5f
def s87L : Nat → Packing
  | 4 => (1,0,1,0,0,1,0,s87D4)
  | _ => emptyPacking
def s87I : Nat → Nat → Option (Nat × Nat)
  | _,_ => none
def s87 : Forest := ⟨87,4,s87S,s87C,[[],[33]],s87L,s87I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs87_4_0 : block s87 4 0 1 = true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs87_4 : block s87 4 0 1 = true := bs87_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts87 : checkedTables s87 4 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs87_4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs87 : graphValid s87 (boundsBefore es153) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls87 : Lower true (vars 87) (graphGoal 87) 5 := lower_forest (g:=s87) (i:=0) (hints:=1636) (before_sound es153 vs153) gs87 ts87 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es87 := extendKnown es153 5 [(87,[]),(103,[16,84]),(199,[117,116]),(302,[135,83,134,80,50,33,65]),(327,[135,133,32,16,132]),(364,[135,83,134,80,82,49,100]),(428,[134,48,82,33,116])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs87 : Known true es87 := extendKnown_ok (m:=87) vs153 ls87 (by decide +kernel)
def s115S := sampleAt 41 #[(0xb303f3c0ff,0x1128b1d253),(0x14dfc0cffc0,0x51c6447ca),(0x0,0x0),(0x0,0x0),(0x18e000f00ff,0x18e924e24ac),(0x1f0000fff00,0x1f0a28bb830),(0x1fffff00000,0x1eac3002020),(0x0,0x0),(0x0,0x0)]
def s115C : List ColumnInfo := []
def s115D4 (_ : Nat) : Nat := 0x1f
def s115L : Nat → Packing
  | 4 => (1,0,1,0,0,1,0,s115D4)
  | _ => emptyPacking
def s115I : Nat → Nat → Option (Nat × Nat)
  | _,_ => none
def s115 : Forest := ⟨115,4,s115S,s115C,[[],[16,84]],s115L,s115I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs115_4_0 : block s115 4 0 1 = true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs115_4 : block s115 4 0 1 = true := bs115_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts115 : checkedTables s115 4 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs115_4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs115 : graphValid s115 (boundsBefore es87) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls115 : Lower true (vars 115) (graphGoal 115) 5 := lower_forest (g:=s115) (i:=0) (hints:=1048660) (before_sound es87 vs87) gs115 ts115 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es115 := extendKnown es87 5 [(115,[]),(203,[115,96,113,83,65]),(205,[115,114,96,113,83,66]),(227,[16,117,84]),(333,[135,131,130,98,96,129,83,64]),(334,[135,131,98,96,129,83,65]),(341,[135,33,133]),(355,[135,134,96,129,133,64]),(357,[135,130,98,96,129,64]),(362,[135,131,130,128,101,67]),(397,[135,115,130,99,112,129,82,64]),(412,[135,115,130,99,128,113,82,66]),(425,[131,130,99,112,129,64]),(426,[115,114,134,112,49,117,65]),(440,[131,114,99,112,129]),(453,[33,133,116]),(457,[50,118,49,133,100]),(460,[135,134,32,49,117,100])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs115 : Known true es115 := extendKnown_ok (m:=115) vs87 ls115 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls171 : Lower true (vars 171) (graphGoal 171) 4 := size_of (hints:=1077335) (by decide +kernel)
def es171 := extendKnown es115 4 [(171,[]),(186,[66,67,48]),(206,[118,50,48,117,49]),(214,[66,118,50,64,117,65]),(218,[66,67,48,101]),(220,[66,67,48,101,33]),(234,[100,98,118,99,112,117,49]),(242,[66,116,99,112,117,65]),(285,[135,32,84,16]),(307,[132,116,131,84,16]),(309,[135,67,32,84,16]),(313,[66,135,67,48,84,16]),(331,[134,118,133,49]),(345,[134,100,98,116,99,64,133,49]),(361,[100,98,135,99,48,101,16]),(369,[132,130,116,99,64,133,81]),(419,[134,132,131,117,16]),(421,[134,132,135,115,32,117,16]),(434,[134,66,131,64,117,65]),(436,[134,135,115,32,117,65]),(458,[134,132,130,135,131,112,101]),(468,[134,98,114,131,96,117,65]),(481,[132,130,118,115,96,133,81])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs171 : Known true es171 := extendKnown_ok (m:=171) vs115 ls171 (by decide +kernel)
def s179S := sampleAt 50 #[(0x3003ff3c03ff,0x10250b1c4913),(0xcc0300cfff00,0x4d1746451f4a),(0x0,0x0),(0x0,0x0),(0x30ffc00f003ff,0x1045814e0922c),(0x3f00000fffc00,0x3b26098bae0b0),(0x0,0x0),(0x3ffffff000000,0x2eb82e00300c0),(0x0,0x0)]
def s179C : List ColumnInfo := [(0,32,145,514,5)]
def s179D5 (_ : Nat) : Nat := 0x5f
def s179L : Nat → Packing
  | 5 => (1,0,1,0,0,1,0,s179D5)
  | _ => emptyPacking
def s179I : Nat → Nat → Option (Nat × Nat)
  | _,_ => none
def s179 : Forest := ⟨179,5,s179S,s179C,[[],[116],[64],[64,112],[112,64],[112],[81],[81,116],[64,81],[64,81,112],[112,81,64],[112,81]],s179L,s179I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs179_5_0 : block s179 5 0 1 = true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs179_5 : block s179 5 0 1 = true := bs179_5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts179 : checkedTables s179 5 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs179_5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs179 : graphValid s179 (boundsBefore es171) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls179 : Lower true (vars 179) (graphGoal 179) 6 := lower_forest (g:=s179) (i:=0) (hints:=1048660) (before_sound es171 vs171) gs179 ts179 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es179 := extendKnown es171 6 [(179,[]),(405,[134,133,33]),(433,[134,131,130,133,81])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs179 : Known true es179 := extendKnown_ok (m:=179) vs171 ls179 (by decide +kernel)
def s211S := sampleAt 50 #[(0x200ff980ffff,0x1418820683),(0xd80c06ff0180,0x5a5d32a74daa),(0x0,0x0),(0x0,0x0),(0x31ff0070001ff,0x108e06714291c),(0x0,0x0),(0x3e00007fffe00,0x3a4824558b050),(0x3fffff8000000,0x2f70b8060c060),(0x0,0x0)]
def s211C : List ColumnInfo := [(0,2,145,576,5),(2,0,209,512,5),(16,0,195,512,4),(66,0,145,512,4),(128,0,83,512,4)]
def s211D6 (_ : Nat) : Nat := 0x5191f
def s211H5 (_ : Nat) : Nat := 0xaa7b009441
def s211D5 (_ : Nat) : Nat := (OfNat.ofNat (limbs [0x84068140,0xc920fe20fd20fd42]))
def s211H4 (_ : Nat) : Nat := 0xd40
def s211D4 (_ : Nat) : Nat := 0x4f91520
def s211L : Nat → Packing
  | 6 => (1,0,3,0,0,1,0,s211D6)
  | 5 => (3,1,3,0,0,5,0,s211D5)
  | 4 => (1,2,3,0,0,1,0,s211D4)
  | _ => emptyPacking
def s211I : Nat → Nat → Option (Nat × Nat)
  | 6,h => lookupWord 2 6 1 7 2 1 s211H5 (mixTag h)
  | 5,h => lookupWord 1 3 1 6 1 1 s211H4 (mixTag h)
  | _,_ => none
def s211 : Forest := ⟨211,6,s211S,s211C,[[],[116]],s211L,s211I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs211_6_0 : block s211 6 0 1 = true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs211_6 : block s211 6 0 1 = true := bs211_6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs211_5_0 : block s211 5 0 3 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs211_5 : block s211 5 0 3 = true := bs211_5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs211_4_0 : block s211 4 0 1 = true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs211_4 : block s211 4 0 1 = true := bs211_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts211 : checkedTables s211 6 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs211_4
  · exact bs211_5
  · exact bs211_6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs211 : graphValid s211 (boundsBefore es179) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls211 : Lower true (vars 211) (graphGoal 211) 7 := lower_forest (g:=s211) (i:=0) (hints:=100) (before_sound es179 vs179) gs211 ts211 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es211 := extendKnown es179 7 [(211,[]),(213,[33]),(409,[131,130,112,64,99,129])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs211 : Known true es211 := extendKnown_ok (m:=211) vs179 ls211 (by decide +kernel)
def s217S := sampleAt 39 #[(0x2041fffff,0xc4311a3),(0x0,0x0),(0x0,0x0),(0x4d07e0b060,0x452ce6b56a),(0x71f800c07f,0x513084c44c),(0x0,0x0),(0x7e0000ff80,0x7ea294ee18),(0x7fffff0000,0x2ac3180810),(0x0,0x0)]
def s217C : List ColumnInfo := [(64,0,153,512,5)]
def s217D5 (_ : Nat) : Nat := 0x5f
def s217L : Nat → Packing
  | 5 => (1,0,1,0,0,1,0,s217D5)
  | _ => emptyPacking
def s217I : Nat → Nat → Option (Nat × Nat)
  | _,_ => none
def s217 : Forest := ⟨217,5,s217S,s217C,[[],[112,99]],s217L,s217I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs217_5_0 : block s217 5 0 1 = true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs217_5 : block s217 5 0 1 = true := bs217_5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts217 : checkedTables s217 5 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs217_5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs217 : graphValid s217 (boundsBefore es211) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls217 : Lower true (vars 217) (graphGoal 217) 6 := lower_forest (g:=s217) (i:=0) (hints:=28676) (before_sound es211 vs211) gs217 ts217 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es217 := extendKnown es211 6 [(217,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs217 : Known true es217 := extendKnown_ok (m:=217) vs211 ls217 (by decide +kernel)
def s358S := sampleAt 50 #[(0x0,0x0),(0x680c0180ffff,0x2a1d10a246a3),(0x900ffeff0180,0x10543a870d8a),(0x0,0x0),(0x0,0x0),(0x31ff0070001ff,0x110e06714291c),(0x3e00007fffe00,0x3c4824558b050),(0x0,0x0),(0x3fffff8000000,0x2ef0b8060c060)]
def s358C : List ColumnInfo := [(2,0,356,512,4),(4,0,354,512,4),(32,0,326,512,4),(64,0,294,512,4),(256,0,102,512,4)]
def s358D6 (_ : Nat) : Nat := 0x234095f
def s358H5 (_ : Nat) : Nat := (OfNat.ofNat (limbs [0x235ab4c7465,0xdb00e1321f0e1]))
def s358D5 (_ : Nat) : Nat := 0x30828fd10fd20
def s358H4 (_ : Nat) : Nat := 0x1a95840cbf8005
def s358D4 (_ : Nat) : Nat := 0x578d510
def s358L : Nat → Packing
  | 6 => (1,0,3,0,0,1,0,s358D6)
  | 5 => (2,1,3,0,0,3,0,s358D5)
  | 4 => (1,2,3,0,0,1,0,s358D4)
  | _ => emptyPacking
def s358I : Nat → Nat → Option (Nat × Nat)
  | 6,h => lookupWord 4 14 3 8 1 3 s358H5 (mixTag h)
  | 5,h => lookupWord 2 6 3 8 1 3 s358H4 (mixTag h)
  | _,_ => none
def s358 : Forest := ⟨358,6,s358S,s358C,[[],[130,101],[33,133],[33,81,97,129],[81,134],[81,98,129,33],[97,82],[97,130,81,82],[129,33,82,101],[129,98]],s358L,s358I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs358_6_0 : block s358 6 0 1 = true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs358_6 : block s358 6 0 1 = true := bs358_6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs358_5_0 : block s358 5 0 2 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs358_5 : block s358 5 0 2 = true := bs358_5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs358_4_0 : block s358 4 0 1 = true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs358_4 : block s358 4 0 1 = true := bs358_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts358 : checkedTables s358 6 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs358_4
  · exact bs358_5
  · exact bs358_6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs358 : graphValid s358 (boundsBefore es217) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls358 : Lower true (vars 358) (graphGoal 358) 7 := lower_forest (g:=s358) (i:=0) (hints:=8607762000) (before_sound es217 vs217) gs358 ts358 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es358 := extendKnown es217 7 [(358,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs358 : Known true es358 := extendKnown_ok (m:=358) vs217 ls358 (by decide +kernel)
def s119S := sampleAt 75 #[((OfNat.ofNat (limbs [0xc6,0xd0101fccf301fff])),(OfNat.ofNat (limbs [0x42,0x515142c47324a93]))),((OfNat.ofNat (limbs [0x109,0x3601fe0333fff980])),(OfNat.ofNat (limbs [0x1,0x160d0e191150f98a]))),((OfNat.ofNat (limbs [0x671,0xc7fe0003c3c01e00])),(OfNat.ofNat (limbs [0x251,0x473e3c7bc3c6de3a]))),(0x0,0x0),((OfNat.ofNat (limbs [0x781,0xf8000003fc001fff])),(OfNat.ofNat (limbs [0x781,0xf8a8a953b80c956c]))),((OfNat.ofNat (limbs [0x7fe,0x3ffffe000])),(OfNat.ofNat (limbs [0x7fe,0xb0b162eeaf0070]))),((OfNat.ofNat (limbs [0x7ff,0xfffffffc00000000])),(OfNat.ofNat (limbs [0x5ac,0xa8c0c18000080040]))),(0x0,0x0),(0x0,0x0)]
def s119C : List ColumnInfo := [(0,16,102,513,5),(0,32,85,514,5),(4,0,115,512,5),(17,0,102,512,4),(34,0,85,512,4)]
def s119D6 (_ : Nat) : Nat := 0x4632bf
def s119D5 (_ : Nat) : Nat := 0x1ef52
def s119L : Nat → Packing
  | 6 => (1,0,3,0,0,1,0,s119D6)
  | 5 => (1,1,3,0,0,1,0,s119D5)
  | _ => emptyPacking
def s119I : Nat → Nat → Option (Nat × Nat)
  | 6,_ => some (0,0)
  | _,_ => none
def s119 : Forest := ⟨119,6,s119S,s119C,[[],[16,84]],s119L,s119I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs119_6_0 : block s119 6 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs119_6 : block s119 6 0 1 = true := bs119_6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs119_5_0 : block s119 5 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs119_5 : block s119 5 0 1 = true := bs119_5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts119 : checkedTables s119 6 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs119_5
  · exact bs119_6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs119 : graphValid s119 (boundsBefore es358) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls119 : Lower true (vars 119) (graphGoal 119) 7 := lower_forest (g:=s119) (i:=0) (hints:=1050196) (before_sound es358 vs358) gs119 ts119 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es119 := extendKnown es358 7 [(119,[]),(231,[16,117,84]),(343,[135,33,133]),(430,[115,134,112,49,117,65]),(455,[33,133,116]),(492,[115,134,112,49,114,117,100])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs119 : Known true es119 := extendKnown_ok (m:=119) vs358 ls119 (by decide +kernel)
def s187S := sampleAt 80 #[((OfNat.ofNat (limbs [0x10c0,0x2403ff33cc03fff])),(OfNat.ofNat (limbs [0x1040,0x264290b11cc49513]))),((OfNat.ofNat (limbs [0x32c,0x380300ccffff300])),(OfNat.ofNat (limbs [0x12d,0x1791b4644551f34a]))),(0x0,0x0),((OfNat.ofNat (limbs [0x9c30,0x3ffc00f0f003c00])),(OfNat.ofNat (limbs [0x9430,0x76c7c1ef0f0dbc3a]))),((OfNat.ofNat (limbs [0xe03f,0xfc00000ff0003fff])),(OfNat.ofNat (limbs [0xa034,0x5805014ee0092a2c]))),((OfNat.ofNat (limbs [0xffc0,0xfffffc000])),(OfNat.ofNat (limbs [0xfec2,0x6026098bbaae00b0]))),(0x0,0x0),((OfNat.ofNat (limbs [0xffff,0xfffffff000000000])),(OfNat.ofNat (limbs [0x4b8b,0x81382e00003000c0]))),(0x0,0x0)]
def s187C : List ColumnInfo := [(8,0,179,512,6)]
def s187D6 (_ : Nat) : Nat := 0xbf
def s187L : Nat → Packing
  | 6 => (1,0,1,0,0,1,0,s187D6)
  | _ => emptyPacking
def s187I : Nat → Nat → Option (Nat × Nat)
  | _,_ => none
def s187 : Forest := ⟨187,6,s187S,s187C,[[],[64],[81],[64,81]],s187L,s187I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs187_6_0 : block s187 6 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs187_6 : block s187 6 0 1 = true := bs187_6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts187 : checkedTables s187 6 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs187_6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs187 : graphValid s187 (boundsBefore es119) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls187 : Lower true (vars 187) (graphGoal 187) 7 := lower_forest (g:=s187) (i:=0) (hints:=1077332) (before_sound es119 vs119) gs187 ts187 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es187 := extendKnown es119 7 [(187,[]),(497,[134,130,116,64,99,133,81])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs187 : Known true es187 := extendKnown_ok (m:=187) vs119 ls187 (by decide +kernel)
def s207S := sampleAt 68 #[(0x19240fffa4e8103f,0x9242543a4685083),((OfNat.ofNat (limbs [0x2,0x6e380cc0c7301fc0])),(OfNat.ofNat (limbs [0x2,0x2e392cd2c53254d2]))),((OfNat.ofNat (limbs [0x3,0x8fc00f00f83fe000])),(OfNat.ofNat (limbs [0x2,0x8fc12f12e83a6492]))),((OfNat.ofNat (limbs [0xc,0xffff000ffc00000])),(OfNat.ofNat (limbs [0x4,0xb6c7006ffc1428a]))),(0x0,0x0),(0x0,0x0),((OfNat.ofNat (limbs [0xf,0xf0000000ffffffff])),(OfNat.ofNat (limbs [0xd,0x5002402412858b2c]))),((OfNat.ofNat (limbs [0xf,0xffffffff00000000])),(OfNat.ofNat (limbs [0xb,0xf4938ab800060c30]))),(0x0,0x0)]
def s207C : List ColumnInfo := [(8,0,199,512,5)]
def s207D5 (_ : Nat) : Nat := 0xbf
def s207L : Nat → Packing
  | 5 => (1,0,1,0,0,1,0,s207D5)
  | _ => emptyPacking
def s207I : Nat → Nat → Option (Nat × Nat)
  | _,_ => none
def s207 : Forest := ⟨207,5,s207S,s207C,[[],[33]],s207L,s207I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs207_5_0 : block s207 5 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs207_5 : block s207 5 0 1 = true := bs207_5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts207 : checkedTables s207 5 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs207_5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs207 : graphValid s207 (boundsBefore es187) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls207 : Lower true (vars 207) (graphGoal 207) 6 := lower_forest (g:=s207) (i:=0) (hints:=30310) (before_sound es187 vs187) gs207 ts207 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es207 := extendKnown es187 6 [(207,[]),(335,[135,32,16]),(365,[84,134,80,118,82,16,48]),(429,[84,134,82,33,48]),(444,[134,64,82,33,67])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs207 : Known true es207 := extendKnown_ok (m:=207) vs187 ls207 (by decide +kernel)
def s215S := sampleAt 78 #[((OfNat.ofNat (limbs [0x40,0x1fff068080fffff])),0x2a8302828206a83),((OfNat.ofNat (limbs [0x9b3,0x19809b00ff01980])),(OfNat.ofNat (limbs [0x8b3,0x4b9a68b26a74d9aa]))),((OfNat.ofNat (limbs [0xe3c,0x1e00e3ff0001e00])),(OfNat.ofNat (limbs [0xa3c,0x4be26a3a7264de2a]))),(0x0,0x0),((OfNat.ofNat (limbs [0x303f,0xfe000fc000001fff])),(OfNat.ofNat (limbs [0x1015,0x1c00cfc14142951c]))),(0x0,0x0),((OfNat.ofNat (limbs [0x3fc0,0xfffffffe000])),(OfNat.ofNat (limbs [0x3540,0x90048545858b0050]))),((OfNat.ofNat (limbs [0x3fff,0xfffff00000000000])),(OfNat.ofNat (limbs [0x2fea,0xe1570006060c0060]))),(0x0,0x0)]
def s215C : List ColumnInfo := [(4,0,211,512,7)]
def s215D7 (_ : Nat) : Nat := 0xbf
def s215L : Nat → Packing
  | 7 => (1,0,1,0,0,1,0,s215D7)
  | _ => emptyPacking
def s215I : Nat → Nat → Option (Nat × Nat)
  | _,_ => none
def s215 : Forest := ⟨215,7,s215S,s215C,[[],[116],[33],[33,116]],s215L,s215I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs215_7_0 : block s215 7 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs215_7 : block s215 7 0 1 = true := bs215_7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts215 : checkedTables s215 7 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs215_7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs215 : graphValid s215 (boundsBefore es207) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls215 : Lower true (vars 215) (graphGoal 215) 8 := lower_forest (g:=s215) (i:=0) (hints:=1636) (before_sound es207 vs207) gs215 ts215 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es215 := extendKnown es207 8 [(215,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs215 : Known true es215 := extendKnown_ok (m:=215) vs207 ls215 (by decide +kernel)
def s219S := sampleAt 78 #[((OfNat.ofNat (limbs [0x40,0x480ff93380fffff])),0xc82418118206a83),((OfNat.ofNat (limbs [0x1ac,0x700c06dcff01980])),(OfNat.ofNat (limbs [0xad,0x2f26d3254a74d9aa]))),(0x0,0x0),((OfNat.ofNat (limbs [0x2630,0x7ff0071f0001e00])),(OfNat.ofNat (limbs [0x2230,0x6d8f0771f162de1a]))),((OfNat.ofNat (limbs [0x383f,0xf800007e00001fff])),(OfNat.ofNat (limbs [0x2834,0x700c067e0142951c]))),(0x0,0x0),((OfNat.ofNat (limbs [0x3fc0,0x7fffffe000])),(OfNat.ofNat (limbs [0x3f42,0x4048245aa58b0050]))),((OfNat.ofNat (limbs [0x3fff,0xffffff8000000000])),(OfNat.ofNat (limbs [0x15cb,0x8270b800060c0060]))),(0x0,0x0)]
def s219C : List ColumnInfo := [(8,0,211,512,7)]
def s219D7 (_ : Nat) : Nat := 0xbf
def s219L : Nat → Packing
  | 7 => (1,0,1,0,0,1,0,s219D7)
  | _ => emptyPacking
def s219I : Nat → Nat → Option (Nat × Nat)
  | _,_ => none
def s219 : Forest := ⟨219,7,s219S,s219C,[[]],s219L,s219I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs219_7_0 : block s219 7 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs219_7 : block s219 7 0 1 = true := bs219_7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts219 : checkedTables s219 7 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs219_7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs219 : graphValid s219 (boundsBefore es215) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls219 : Lower true (vars 219) (graphGoal 219) 8 := lower_forest (g:=s219) (i:=0) (hints:=28772) (before_sound es215 vs215) gs219 ts219 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es219 := extendKnown es215 8 [(219,[]),(221,[33]),(473,[133,130,112,99,129])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs219 : Known true es219 := extendKnown_ok (m:=219) vs215 ls219 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls222 : Lower true (vars 222) (graphGoal 222) 5 := size_of (hints:=822572640) (by decide +kernel)
def es222 := extendKnown es219 5 [(222,[]),(250,[101,117,100,83,66,49]),(377,[128,134,112,100,67,82,49])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs222 : Known true es222 := extendKnown_ok (m:=222) vs219 ls222 (by decide +kernel)
def s235S := sampleAt 75 #[((OfNat.ofNat (limbs [0x86,0x1c80ffb7380ff980])),(OfNat.ofNat (limbs [0x2,0xc8643931860f98a]))),((OfNat.ofNat (limbs [0x118,0x6700c049cff01fff])),(OfNat.ofNat (limbs [0x8,0x2722d1014a344aa3]))),(0x0,0x0),((OfNat.ofNat (limbs [0x663,0x87ff0071f0001e00])),(OfNat.ofNat (limbs [0x222,0x858f0771f162de1a]))),(0x0,0x0),((OfNat.ofNat (limbs [0x783,0xf800007e00001fff])),(OfNat.ofNat (limbs [0x783,0xd84c267e054a955c]))),((OfNat.ofNat (limbs [0x7fc,0x7fffffe000])),(OfNat.ofNat (limbs [0x7f4,0x48246ca58b0050]))),((OfNat.ofNat (limbs [0x7ff,0xffffff8000000000])),(OfNat.ofNat (limbs [0x5dd,0x7270b800060c0060]))),(0x0,0x0)]
def s235C : List ColumnInfo := [(0,8,99,640,5),(0,32,201,514,5),(8,0,227,512,5),(32,0,203,512,5)]
def s235D6 (_ : Nat) : Nat := 0xe123f
def s235L : Nat → Packing
  | 6 => (1,0,2,0,0,1,0,s235D6)
  | _ => emptyPacking
def s235I : Nat → Nat → Option (Nat × Nat)
  | _,_ => none
def s235 : Forest := ⟨235,6,s235S,s235C,[[],[96,113,83]],s235L,s235I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs235_6_0 : block s235 6 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs235_6 : block s235 6 0 1 = true := bs235_6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts235 : checkedTables s235 6 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs235_6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs235 : graphValid s235 (boundsBefore es222) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls235 : Lower true (vars 235) (graphGoal 235) 7 := lower_forest (g:=s235) (i:=0) (hints:=1077334) (before_sound es222 vs222) gs235 ts235 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es235 := extendKnown es222 7 [(235,[]),(349,[32,135,16,84]),(363,[134,128,118,129,80,48]),(371,[134,96,112,129,133,67]),(373,[130,98,96,112,129,67]),(427,[134,81,48]),(442,[132,130,100,128,116,113,84,49]),(459,[118,133,49]),(462,[134,32,118,117,49]),(476,[66,134,64,33,101,67]),(483,[132,134,96,112,129,133,115]),(485,[132,32,135,16,117,83]),(489,[132,130,134,96,135,16,101,83]),(490,[132,130,134,96,118,97,117,99])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs235 : Known true es235 := extendKnown_ok (m:=235) vs222 ls235 (by decide +kernel)
def s238S := sampleAt 76 #[(0x0,0x0),((OfNat.ofNat (limbs [0x93,0xfcc0099c03fffff])),(OfNat.ofNat (limbs [0x11,0x5cc8808c888d523]))),((OfNat.ofNat (limbs [0x31c,0xccf0036e7fc03300])),(OfNat.ofNat (limbs [0x114,0xccf1992a59d9b36a]))),((OfNat.ofNat (limbs [0xc60,0xf0ffff8f80003c00])),(OfNat.ofNat (limbs [0x420,0x50543f8f8585bc1a]))),(0x0,0x0),((OfNat.ofNat (limbs [0xf80,0xff0003f000003fff])),(OfNat.ofNat (limbs [0xf80,0xfa0333f035352adc]))),((OfNat.ofNat (limbs [0xfff,0x3ffffffc000])),(OfNat.ofNat (limbs [0xeea,0x222d526260090]))),((OfNat.ofNat (limbs [0xfff,0xfffffc0000000000])),(OfNat.ofNat (limbs [0xbdf,0xafabc000383800e0]))),(0x0,0x0)]
def s238C : List ColumnInfo := [(0,128,102,520,5)]
def s238D5 (_ : Nat) : Nat := 0xbf
def s238L : Nat → Packing
  | 5 => (1,0,1,0,0,1,0,s238D5)
  | _ => emptyPacking
def s238I : Nat → Nat → Option (Nat × Nat)
  | _,_ => none
def s238 : Forest := ⟨238,5,s238S,s238C,[[],[115],[97,82],[97,82,115]],s238L,s238I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs238_5_0 : block s238 5 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs238_5 : block s238 5 0 1 = true := bs238_5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts238 : checkedTables s238 5 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs238_5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs238 : graphValid s238 (boundsBefore es235) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls238 : Lower true (vars 238) (graphGoal 238) 6 := lower_forest (g:=s238) (i:=0) (hints:=823162448) (before_sound es235 vs235) gs238 ts238 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es238 := extendKnown es235 6 [(238,[]),(246,[67]),(311,[132,134,129,81,33,116,48]),(315,[132,128,96,129,80,33,116,48]),(347,[16,84,33,135]),(423,[134,129,81,33,48]),(438,[134,129,81,33,67]),(470,[133,33,67]),(474,[133,66,118,49]),(498,[132,134,129,133,98,67]),(500,[132,134,97,101,82,67])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs238 : Known true es238 := extendKnown_ok (m:=238) vs235 ls238 (by decide +kernel)
def s243S := sampleAt 84 #[((OfNat.ofNat (limbs [0x10860,0x7feb300ff3c03ff])),(OfNat.ofNat (limbs [0x20,0x4a16110a0b1c4913]))),((OfNat.ofNat (limbs [0x23198,0x6014dff00cfff00])),(OfNat.ofNat (limbs [0x109a,0x2e8c054746451f4a]))),(0x0,0x0),(0x0,0x0),((OfNat.ofNat (limbs [0xcc61f,0xf8018e0000f003ff])),(OfNat.ofNat (limbs [0x44208,0xb0298e2424e0922c]))),((OfNat.ofNat (limbs [0xf07e0,0x1f00000fffc00])),(OfNat.ofNat (limbs [0xf0764,0xc131f0a8a8bae0b0]))),((OfNat.ofNat (limbs [0xff800,0x1ffffff000000])),(OfNat.ofNat (limbs [0xfe804,0x8121eab0b00280a0]))),((OfNat.ofNat (limbs [0xfffff,0xfffe000000000000])),(OfNat.ofNat (limbs [0xbbdd7,0x5c000c0c00300c0]))),(0x0,0x0)]
def s243C : List ColumnInfo := [(32,0,211,512,7)]
def s243D7 (_ : Nat) : Nat := 0xbf
def s243L : Nat → Packing
  | 7 => (1,0,1,0,0,1,0,s243D7)
  | _ => emptyPacking
def s243I : Nat → Nat → Option (Nat × Nat)
  | _,_ => none
def s243 : Forest := ⟨243,7,s243S,s243C,[[],[116]],s243L,s243I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs243_7_0 : block s243 7 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs243_7 : block s243 7 0 1 = true := bs243_7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts243 : checkedTables s243 7 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs243_7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs243 : graphValid s243 (boundsBefore es238) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls243 : Lower true (vars 243) (graphGoal 243) 8 := lower_forest (g:=s243) (i:=0) (hints:=1048660) (before_sound es238 vs238) gs243 ts243 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es243 := extendKnown es238 8 [(243,[]),(413,[131,130,112,64,99,129,82]),(441,[131,130,112,64,99,129]),(469,[33,133])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs243 : Known true es243 := extendKnown_ok (m:=243) vs238 ls243 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls317 : Lower true (vars 317) (graphGoal 317) 5 := size_of (hints:=8598358020) (by decide +kernel)
def es317 := extendKnown es243 5 [(317,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs317 : Known true es317 := extendKnown_ok (m:=317) vs243 ls317 (by decide +kernel)
def s359S := sampleAt 78 #[((OfNat.ofNat (limbs [0x4eb,0x19808e8080ff980])),(OfNat.ofNat (limbs [0x46b,0x4b9a686a6a64f9aa]))),((OfNat.ofNat (limbs [0x70c,0x1e001300ff01fff])),(OfNat.ofNat (limbs [0x50c,0x43e220322a344aa3]))),((OfNat.ofNat (limbs [0x830,0x1fffe3ff0001e00])),(OfNat.ofNat (limbs [0x30,0xaa87a387060de0a]))),(0x0,0x0),(0x0,0x0),((OfNat.ofNat (limbs [0x303f,0xfe000fc000001fff])),(OfNat.ofNat (limbs [0x1031,0x1c00cfc14142951c]))),((OfNat.ofNat (limbs [0x3fc0,0xfffffffe000])),(OfNat.ofNat (limbs [0x3a80,0x90048585858b0050]))),(0x0,0x0),((OfNat.ofNat (limbs [0x3fff,0xfffff00000000000])),(OfNat.ofNat (limbs [0x2fce,0xe1570006060c0060])))]
def s359C : List ColumnInfo := [(1,0,358,512,7)]
def s359D7 (_ : Nat) : Nat := 0xbf
def s359L : Nat → Packing
  | 7 => (1,0,1,0,0,1,0,s359D7)
  | _ => emptyPacking
def s359I : Nat → Nat → Option (Nat × Nat)
  | _,_ => none
def s359 : Forest := ⟨359,7,s359S,s359C,[[],[33,133]],s359L,s359I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs359_7_0 : block s359 7 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs359_7 : block s359 7 0 1 = true := bs359_7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts359 : checkedTables s359 7 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs359_7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs359 : graphValid s359 (boundsBefore es317) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls359 : Lower true (vars 359) (graphGoal 359) 8 := lower_forest (g:=s359) (i:=0) (hints:=8590984790) (before_sound es317 vs317) gs359 ts359 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es359 := extendKnown es317 8 [(359,[]),(366,[134,81,48])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs359 : Known true es359 := extendKnown_ok (m:=359) vs317 ls359 (by decide +kernel)
def s435S := sampleAt 80 #[((OfNat.ofNat (limbs [0x1e2,0xc03c3003ff3c03ff])),(OfNat.ofNat (limbs [0xa2,0xc8941089231c9125]))),((OfNat.ofNat (limbs [0x9993,0x30cc0300cfff00])),(OfNat.ofNat (limbs [0x9993,0x38304f83e04787e0]))),(0x0,0x0),(0x0,0x0),((OfNat.ofNat (limbs [0x1e1c,0x3f0ffc00f003ff])),(OfNat.ofNat (limbs [0xa1c,0x1129051444e1224a]))),((OfNat.ofNat (limbs [0xe01f,0xffc3f00000fffc00])),(OfNat.ofNat (limbs [0x2004,0x43c3b05816b8781c]))),(0x0,0x0),((OfNat.ofNat (limbs [0xffe0,0x3ffffff000000])),(OfNat.ofNat (limbs [0xf540,0x2202ea6298024090]))),((OfNat.ofNat (limbs [0xffff,0xfffc000000000000])),(OfNat.ofNat (limbs [0xdffb,0xbc3c0380e00380e0])))]
def s435C : List ColumnInfo := [(256,0,179,512,6)]
def s435D6 (_ : Nat) : Nat := 0xbf
def s435L : Nat → Packing
  | 6 => (1,0,1,0,0,1,0,s435D6)
  | _ => emptyPacking
def s435I : Nat → Nat → Option (Nat × Nat)
  | _,_ => none
def s435 : Forest := ⟨435,6,s435S,s435C,[[],[116],[64],[64,112],[112,64],[112],[129],[129,116],[64,129],[64,129,112],[112,129,64],[112,129]],s435L,s435I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs435_6_0 : block s435 6 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs435_6 : block s435 6 0 1 = true := bs435_6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts435 : checkedTables s435 6 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs435_6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs435 : graphValid s435 (boundsBefore es359) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls435 : Lower true (vars 435) (graphGoal 435) 7 := lower_forest (g:=s435) (i:=0) (hints:=21475885140) (before_sound es359 vs359) gs435 ts435 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es435 := extendKnown es359 7 [(435,[]),(437,[133,33])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs435 : Known true es435 := extendKnown_ok (m:=435) vs359 ls435 (by decide +kernel)
def s461S := sampleAt 78 #[((OfNat.ofNat (limbs [0x8c7,0x603001901ff9c07f])),(OfNat.ofNat (limbs [0x43,0x68b440944a38d123]))),(0x0,0x0),((OfNat.ofNat (limbs [0x1309,0x803fe6e0180e7f80])),(OfNat.ofNat (limbs [0x101,0x829162e2592a4992]))),((OfNat.ofNat (limbs [0x2431,0xffc018ffe00f8000])),(OfNat.ofNat (limbs [0x11,0xa1c0c8b0e06f850a]))),(0x0,0x0),(0x0,0x0),((OfNat.ofNat (limbs [0x383e,0x1f00000fffff])),(OfNat.ofNat (limbs [0x383c,0x11089d088445264c]))),((OfNat.ofNat (limbs [0x3fc0,0x1ffffff00000])),(OfNat.ofNat (limbs [0x3f80,0x1209174b15802850]))),((OfNat.ofNat (limbs [0x3fff,0xffffe00000000000])),(OfNat.ofNat (limbs [0x3eee,0x5c2e000c06003060])))]
def s461C : List ColumnInfo := [(65,0,396,512,4),(68,0,393,512,4),(129,0,332,512,4),(136,0,325,512,4),(260,0,201,512,4),(264,0,197,512,4)]
def s461D7 (_ : Nat) : Nat := 0x468d33f
def s461H6 (_ : Nat) : Nat := (OfNat.ofNat (limbs [0xce9900113e066784,0x4400001140000430]))
def s461D6 (_ : Nat) : Nat := 0x5088643faa1fd10
def s461H5 (_ : Nat) : Nat := (OfNat.ofNat (limbs [0x2380000000018c,0x400a4ccd1002]))
def s461D5 (_ : Nat) : Nat := 0xb78d910
def s461L : Nat → Packing
  | 7 => (1,0,3,0,0,1,0,s461D7)
  | 6 => (2,1,3,0,0,4,0,s461D6)
  | 5 => (1,2,3,0,0,1,0,s461D5)
  | _ => emptyPacking
def s461I : Nat → Nat → Option (Nat × Nat)
  | 7,h => lookupWord 3 14 1 9 1 4 s461H6 (mixTag h)
  | 6,h => lookupWord 2 13 1 9 1 4 s461H5 (mixTag h)
  | _,_ => none
def s461 : Forest := ⟨461,7,s461S,s461C,[[],[50,118],[32,135],[32,48,134,118],[48,32,118,134],[48,134],[96,114,131],[96,130,115,32,48],[112,98,131,32,50],[112,130,99],[128,98,115],[128,114,99]],s461L,s461I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs461_7_0 : block s461 7 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs461_7 : block s461 7 0 1 = true := bs461_7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs461_6_0 : block s461 6 0 2 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs461_6 : block s461 6 0 2 = true := bs461_6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs461_5_0 : block s461 5 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs461_5 : block s461 5 0 1 = true := bs461_5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts461 : checkedTables s461 7 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs461_5
  · exact bs461_6
  · exact bs461_7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs461 : graphValid s461 (boundsBefore es435) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls461 : Lower true (vars 461) (graphGoal 461) 8 := lower_forest (g:=s461) (i:=0) (hints:=8589964806) (before_sound es435 vs435) gs461 ts461 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es461 := extendKnown es435 8 [(461,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs461 : Known true es461 := extendKnown_ok (m:=461) vs435 ls461 (by decide +kernel)
def s223S := sampleAt 126 #[((OfNat.ofNat (limbs [0x800024901fff0,0x41a4e8080fffffff])),(OfNat.ofNat (limbs [0x64904a830,0xa46828206aaa83]))),((OfNat.ofNat (limbs [0x13566038e019809,0xa6c7300ff0199980])),(OfNat.ofNat (limbs [0x11566978e4d9a68,0xa2c5326a74d999aa]))),((OfNat.ofNat (limbs [0x1c67803f001e00e,0x38f83ff0001e1e00])),(OfNat.ofNat (limbs [0x1467897f04de26a,0x28e83a7264de1e2a]))),((OfNat.ofNat (limbs [0x26078003fffe000f,0xc0ffc000001fe000])),(OfNat.ofNat (limbs [0x22078036db1e00ef,0xc0ffc16162dfe01a]))),((OfNat.ofNat (limbs [0x3807fffc0000000f,0xff000000001fffff])),(OfNat.ofNat (limbs [0x2807aa38001800cf,0xff0001414295551c]))),(0x0,0x0),((OfNat.ofNat (limbs [0x3ff800000000000f,0xffffffffffe00000])),(OfNat.ofNat (limbs [0x3ea8012000900485,0x551285858b000050]))),((OfNat.ofNat (limbs [0x3ffffffffffffff0,0x0])),(OfNat.ofNat (limbs [0x15f855c124e15700,0x6060c000060]))),(0x0,0x0)]
def s223C : List ColumnInfo := [(8,0,215,512,8)]
def s223D8 (_ : Nat) : Nat := 0x17f
def s223L : Nat → Packing
  | 8 => (1,0,1,0,0,1,0,s223D8)
  | _ => emptyPacking
def s223I : Nat → Nat → Option (Nat × Nat)
  | _,_ => none
def s223 : Forest := ⟨223,8,s223S,s223C,[[],[33]],s223L,s223I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs223_8_0 : block s223 8 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs223_8 : block s223 8 0 1 = true := bs223_8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts223 : checkedTables s223 8 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs223_8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs223 : graphValid s223 (boundsBefore es461) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls223 : Lower true (vars 223) (graphGoal 223) 9 := lower_forest (g:=s223) (i:=0) (hints:=30308) (before_sound es461 vs461) gs223 ts223 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es223 := extendKnown es461 9 [(223,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs223 : Known true es223 := extendKnown_ok (m:=223) vs461 ls223 (by decide +kernel)
def s239S := sampleAt 132 #[((OfNat.ofNat (limbs [0x40643392403fff8e,0x3a4e80403ff33300])),(OfNat.ofNat (limbs [0x24119241950786,0x1a46834181f3330a]))),((OfNat.ofNat (limbs [0x8980cce380330010,0x4c73007fc03fffff])),(OfNat.ofNat (limbs [0x88044e388b32200,0xc531148c8955523]))),((OfNat.ofNat (limbs [0x3,0xe38f0fc003c00e3,0x8f83ff80003c3c00])),(OfNat.ofNat (limbs [0x1,0xa38f0fc19bc66a2,0x8e83b39999bc3c6a]))),((OfNat.ofNat (limbs [0xc,0x303f00ffffc000fc,0xffc0000003fc000])),(OfNat.ofNat (limbs [0x4,0x102d00b6c3c00efc,0xffc0b0585bfc01a]))),(0x0,0x0),((OfNat.ofNat (limbs [0xf,0xc03fff00000000ff,0xf0000000003fffff])),(OfNat.ofNat (limbs [0xf,0xc03fbb003300ccff,0xf0006a35352aaadc]))),((OfNat.ofNat (limbs [0xf,0xffc00000000000ff,0xffffffffffc00000])),(OfNat.ofNat (limbs [0xe,0xf540000022008859,0x61284c2626000090]))),((OfNat.ofNat (limbs [0xf,0xffffffffffffff00,0x0])),(OfNat.ofNat (limbs [0xb,0xefd2ee493c2af000,0x7038380000e0]))),(0x0,0x0)]
def s239C : List ColumnInfo := [(8,0,231,512,7)]
def s239D7 (_ : Nat) : Nat := 0x17f
def s239L : Nat → Packing
  | 7 => (1,0,1,0,0,1,0,s239D7)
  | _ => emptyPacking
def s239I : Nat → Nat → Option (Nat × Nat)
  | _,_ => none
def s239 : Forest := ⟨239,7,s239S,s239C,[[]],s239L,s239I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs239_7_0 : block s239 7 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs239_7 : block s239 7 0 1 = true := bs239_7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts239 : checkedTables s239 7 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs239_7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs239 : graphValid s239 (boundsBefore es223) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls239 : Lower true (vars 239) (graphGoal 239) 8 := lower_forest (g:=s239) (i:=0) (hints:=1078870) (before_sound es223 vs223) gs239 ts239 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es239 := extendKnown es223 8 [(239,[]),(351,[16,135,33,84]),(431,[134,81,48]),(446,[134,64,81,67]),(508,[134,64,97,98,101,67])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs239 : Known true es239 := extendKnown_ok (m:=239) vs223 ls239 (by decide +kernel)
def s247S := sampleAt 148 #[((OfNat.ofNat (limbs [0x4040,0xcc0003fffc630680,0x1003ff33cc00ffff])),(OfNat.ofNat (limbs [0x440025502c210281,0x50280b11cc125413]))),((OfNat.ofNat (limbs [0x8983,0x3330033000849b00,0x1ffc00ccffffcc00])),(OfNat.ofNat (limbs [0x881,0x1332173218008b10,0xd21c86445487cc8a]))),((OfNat.ofNat (limbs [0x30e33,0xc3c003c00338e3ff,0xe00000f0f000f000])),(OfNat.ofNat (limbs [0x10a33,0xc3c677c67928a3b3,0xe6799ef0f1b6f1ba]))),(0x0,0x0),((OfNat.ofNat (limbs [0xc303c,0x3fffc0003c0fc00,0xff0000ffff])),(OfNat.ofNat (limbs [0x41014,0x150d800d3c0fc0a,0x815054ee0064a86c]))),((OfNat.ofNat (limbs [0xfc03f,0xfc00000003ff0000,0xffffff0000])),(OfNat.ofNat (limbs [0xfc03e,0xec0ce00ce3ff006b,0xd6358bbab780370]))),((OfNat.ofNat (limbs [0xfffc0,0x3ffffff,0xffffff0000000000])),(OfNat.ofNat (limbs [0xef540,0x8800882d6544c,0x982600002400240]))),((OfNat.ofNat (limbs [0xfffff,0xfffffffffc000000,0x0])),(OfNat.ofNat (limbs [0xbefeb,0xbaaf02af00000070,0xe03800003800380]))),(0x0,0x0)]
def s247C : List ColumnInfo := [(0,32,213,514,8),(1,16,102,640,5),(1,128,102,528,5),(4,0,243,512,8),(16,0,231,512,7),(34,0,213,512,7),(64,4,179,512,6),(68,0,179,512,6),(128,0,119,512,7),(128,16,102,513,5),(145,0,102,512,4)]
def s247D9 (_ : Nat) : Nat := 0xf086a67f
def s247H8 (_ : Nat) : Nat := (OfNat.ofNat (limbs [0x964091e557930d0,0x4c0074005fa2470]))
def s247D8 (_ : Nat) : Nat := (OfNat.ofNat (limbs [0x4264314f5,0x520223955531cc54,0xd4e1342682542a38,0xcb5328b0992a251b,0x143d483554c4e6be,0x9b7355321900ff8c,0x3fd50ff54ffd30ff,0x943fd63fbd4bed20]))
def s247H7 (_ : Nat) : Nat := (OfNat.ofNat (limbs [0xa50071895,0xde300749a2c10928]))
def s247D7 (_ : Nat) : Nat := (OfNat.ofNat (limbs [0x9,0x7151209408c18b0,0xcc2d49a8e2b729fa,0xe2203f7a9461fbd4,0x930fdac7a95fd578,0xc27f33a617b41f52]))
def s247H6 (_ : Nat) : Nat := 0xec148c01
def s247D6 (_ : Nat) : Nat := (OfNat.ofNat (limbs [0x28cef5,0x299d309ed78d4a30]))
def s247L : Nat → Packing
  | 9 => (1,0,4,0,0,1,0,s247D9)
  | 8 => (8,1,4,0,0,8,0,s247D8)
  | 7 => (6,2,4,0,0,7,0,s247D7)
  | 6 => (2,3,4,0,0,3,0,s247D6)
  | _ => emptyPacking
def s247I : Nat → Nat → Option (Nat × Nat)
  | 9,h => lookupWord 4 14 3 8 3 1 s247H8 (mixTag h)
  | 8,h => lookupWord 4 12 1 8 3 1 s247H7 (mixTag h)
  | 7,h => lookupWord 2 5 1 6 1 1 s247H6 (mixTag h)
  | _,_ => none
def s247 : Forest := ⟨247,9,s247S,s247C,[[],[116]],s247L,s247I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs247_9_0 : block s247 9 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs247_9 : block s247 9 0 1 = true := bs247_9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs247_8_0 : block s247 8 0 2 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs247_8_2 : block s247 8 2 6 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs247_8 : block s247 8 0 8 = true := (@block_merge s247 8 0 2 6 bs247_8_0 bs247_8_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs247_7_0 : block s247 7 0 2 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs247_7_2 : block s247 7 2 4 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs247_7 : block s247 7 0 6 = true := (@block_merge s247 7 0 2 4 bs247_7_0 bs247_7_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs247_6_0 : block s247 6 0 2 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs247_6 : block s247 6 0 2 = true := bs247_6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts247 : checkedTables s247 9 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs247_6
  · exact bs247_7
  · exact bs247_8
  · exact bs247_9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs247 : graphValid s247 (boundsBefore es239) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls247 : Lower true (vars 247) (graphGoal 247) 10 := lower_forest (g:=s247) (i:=0) (hints:=1050196) (before_sound es239 vs239) gs247 ts247 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es247 := extendKnown es239 10 [(247,[]),(471,[33,133])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs247 : Known true es247 := extendKnown_ok (m:=247) vs239 ls247 (by decide +kernel)
def s251S := sampleAt 133 #[((OfNat.ofNat (limbs [0x40443000900ffd5b,0x26700ff33cc03fff])),(OfNat.ofNat (limbs [0x4100990a42c09,0x230a0b11cc49513]))),((OfNat.ofNat (limbs [0x8180cb00e00c02a4,0xdb9ff00ccffff300])),(OfNat.ofNat (limbs [0x804b45e46d1800,0x4a9474644551f34a]))),(0x0,0x0),((OfNat.ofNat (limbs [0x13,0x26270c00fff00338,0xe3e0000f0f003c00])),(OfNat.ofNat (limbs [0x11,0x22250c1db1f07b38,0xe3e2e2ef0f0dbc3a]))),((OfNat.ofNat (limbs [0x1c,0x38380fff000003c0,0xfc00000ff0003fff])),(OfNat.ofNat (limbs [0x14,0x28280d16014053c0,0xfc02424ee0092a2c]))),((OfNat.ofNat (limbs [0x1f,0xc03ff000000003ff,0xfffffc000])),(OfNat.ofNat (limbs [0x1f,0xc03fb098098263ff,0xa8a8bbaae00b0]))),((OfNat.ofNat (limbs [0x1f,0xffc00000000003ff,0xfffffff000000000])),(OfNat.ofNat (limbs [0x1f,0xff400090090243f6,0xb54b0b00002800a0]))),((OfNat.ofNat (limbs [0x1f,0xfffffffffffffc00,0x0])),(OfNat.ofNat (limbs [0xa,0xd5d2e2e04e0b8000,0xc0c00003000c0]))),(0x0,0x0)]
def s251C : List ColumnInfo := [(32,0,219,512,8)]
def s251D8 (_ : Nat) : Nat := 0x17f
def s251L : Nat → Packing
  | 8 => (1,0,1,0,0,1,0,s251D8)
  | _ => emptyPacking
def s251I : Nat → Nat → Option (Nat × Nat)
  | _,_ => none
def s251 : Forest := ⟨251,8,s251S,s251C,[[]],s251L,s251I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs251_8_0 : block s251 8 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs251_8 : block s251 8 0 1 = true := bs251_8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts251 : checkedTables s251 8 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs251_8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs251 : graphValid s251 (boundsBefore es247) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls251 : Lower true (vars 251) (graphGoal 251) 9 := lower_forest (g:=s251) (i:=0) (hints:=1077332) (before_sound es247 vs247) gs251 ts251 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es251 := extendKnown es247 9 [(251,[]),(505,[130,112,129,99])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs251 : Known true es251 := extendKnown_ok (m:=251) vs247 ls251 (by decide +kernel)
def s254S := sampleAt 130 #[(0x0,0x0),((OfNat.ofNat (limbs [0x413003eb300cc00,0x926739c03fffffff])),(OfNat.ofNat (limbs [0x110016b322cc88,0x2318c888d55523]))),((OfNat.ofNat (limbs [0x181cb3333c00f003,0x6db9ce7fc0333300])),(OfNat.ofNat (limbs [0x814b3333c66f199,0x24a94a59d9b3336a]))),((OfNat.ofNat (limbs [0x2,0x6260c3c3c000ffff,0x8e3e0f80003c3c00])),(OfNat.ofNat (limbs [0x2,0x2220c143c00e543f,0x8e3e0f8585bc3c1a]))),((OfNat.ofNat (limbs [0x3,0x8380fc03ffff0003,0xf03ff000003fc000])),(OfNat.ofNat (limbs [0x2,0x8280d403d50f003b,0xf03ff00585bfc01a]))),((OfNat.ofNat (limbs [0x3,0xfc00fffc00000003,0xffc00000003fffff])),(OfNat.ofNat (limbs [0x3,0xfc00ffe800cc0333,0xffc00035352aaadc]))),((OfNat.ofNat (limbs [0x3,0xffff000000000003,0xffffffffffc00000])),(OfNat.ofNat (limbs [0x3,0xf7ea000000880222,0xdb54a52626000090]))),((OfNat.ofNat (limbs [0x3,0xfffffffffffffffc,0x0])),(OfNat.ofNat (limbs [0x1,0x5d5f2abc2af0abc0,0x38380000e0]))),(0x0,0x0)]
def s254C : List ColumnInfo := [(16,0,238,512,6)]
def s254D6 (_ : Nat) : Nat := 0x17f
def s254L : Nat → Packing
  | 6 => (1,0,1,0,0,1,0,s254D6)
  | _ => emptyPacking
def s254I : Nat → Nat → Option (Nat × Nat)
  | _,_ => none
def s254 : Forest := ⟨254,6,s254S,s254C,[[],[67],[97,82],[97,82,67]],s254L,s254I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs254_6_0 : block s254 6 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs254_6 : block s254 6 0 1 = true := bs254_6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts254 : checkedTables s254 6 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs254_6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs254 : graphValid s254 (boundsBefore es251) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls254 : Lower true (vars 254) (graphGoal 254) 7 := lower_forest (g:=s254) (i:=0) (hints:=823621200) (before_sound es251 vs251) gs254 ts254 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es254 := extendKnown es251 7 [(254,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs254 : Known true es254 := extendKnown_ok (m:=254) vs251 ls254 (by decide +kernel)
def s319S := sampleAt 130 #[((OfNat.ofNat (limbs [0xaac0000facc0330,0x3333cccc03fffff])),(OfNat.ofNat (limbs [0xaad24005acd2b34,0xa1111cccd4955553]))),((OfNat.ofNat (limbs [0x403002ccccf003c0,0xccccffffff33300])),(OfNat.ofNat (limbs [0x40330eccccf31bcc,0x6444455571f333ca]))),((OfNat.ofNat (limbs [0x2,0x8cc0030f0f0003ff,0xff0f0f0f003c3c00])),(OfNat.ofNat (limbs [0x2,0x8cc06f050f007951,0xff0f0f0f0dbc3c3a]))),((OfNat.ofNat (limbs [0x3,0xf0003f00ffffc00,0xff00ff0003fc000])),(OfNat.ofNat (limbs [0x3,0xf006f500f547c01,0xeff00ff00dbfc03a]))),((OfNat.ofNat (limbs [0x3,0xf00003fff0000000,0xffff000003fffff])),(OfNat.ofNat (limbs [0x3,0xf0024bffa0025009,0x4eeee000292aaaac]))),((OfNat.ofNat (limbs [0x3,0xfffffc0000000000,0xfffffffffc00000])),(OfNat.ofNat (limbs [0x3,0x9fc4700000006001,0x8bbbbaaa8e000030]))),(0x0,0x0),(0x0,0x0),((OfNat.ofNat (limbs [0x3,0xffffffffffffffff,0xf000000000000000])),(OfNat.ofNat (limbs [0x603b80aaf0ab82ae,0x300000c0])))]
def s319C : List ColumnInfo := [(8,0,311,512,6)]
def s319D6 (_ : Nat) : Nat := 0x17f
def s319L : Nat → Packing
  | 6 => (1,0,1,0,0,1,0,s319D6)
  | _ => emptyPacking
def s319I : Nat → Nat → Option (Nat × Nat)
  | _,_ => none
def s319 : Forest := ⟨319,6,s319S,s319C,[[],[50],[64],[64,50]],s319L,s319I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs319_6_0 : block s319 6 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs319_6 : block s319 6 0 1 = true := bs319_6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts319 : checkedTables s319 6 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs319_6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs319 : graphValid s319 (boundsBefore es254) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls319 : Lower true (vars 319) (graphGoal 319) 7 := lower_forest (g:=s319) (i:=0) (hints:=8591018068) (before_sound es254 vs254) gs319 ts319 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es319 := extendKnown es254 7 [(319,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs319 : Known true es319 := extendKnown_ok (m:=319) vs254 ls319 (by decide +kernel)
def s367S := sampleAt 126 #[((OfNat.ofNat (limbs [0x9d5602b3019808,0xe3a4e8080ff99980])),(OfNat.ofNat (limbs [0x8d5696b34d9a68,0x61a46a6a64f999aa]))),((OfNat.ofNat (limbs [0xe018033c01e001,0x4c7300ff01fffff])),(OfNat.ofNat (limbs [0xa018873c45e220,0xc5322a344aaaa3]))),((OfNat.ofNat (limbs [0x1066003c001fffe,0x38f83ff0001e1e00])),(OfNat.ofNat (limbs [0x66017c00ca87a,0x28e8387060de1e0a]))),((OfNat.ofNat (limbs [0x26078003fffe000f,0xc0ffc000001fe000])),(OfNat.ofNat (limbs [0x22078037d51e00ef,0xc0ffc16162dfe01a]))),(0x0,0x0),((OfNat.ofNat (limbs [0x3807fffc0000000f,0xff000000001fffff])),(OfNat.ofNat (limbs [0x2807e238001800cf,0xff0001414295551c]))),((OfNat.ofNat (limbs [0x3ff800000000000f,0xffffffffffe00000])),(OfNat.ofNat (limbs [0x3f50012000900485,0x961285858b000050]))),(0x0,0x0),((OfNat.ofNat (limbs [0x3ffffffffffffff0,0x0])),(OfNat.ofNat (limbs [0x15f81dc02ae15700,0x6060c000060])))]
def s367C : List ColumnInfo := [(8,0,359,512,8)]
def s367D8 (_ : Nat) : Nat := 0x17f
def s367L : Nat → Packing
  | 8 => (1,0,1,0,0,1,0,s367D8)
  | _ => emptyPacking
def s367I : Nat → Nat → Option (Nat × Nat)
  | _,_ => none
def s367 : Forest := ⟨367,8,s367S,s367C,[[],[48,81,134]],s367L,s367I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs367_8_0 : block s367 8 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs367_8 : block s367 8 0 1 = true := bs367_8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts367 : checkedTables s367 8 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs367_8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs367 : graphValid s367 (boundsBefore es319) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls367 : Lower true (vars 367) (graphGoal 367) 9 := lower_forest (g:=s367) (i:=0) (hints:=8591017558) (before_sound es319 vs319) gs367 ts367 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es367 := extendKnown es319 9 [(367,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs367 : Known true es367 := extendKnown_ok (m:=367) vs319 ls367 (by decide +kernel)
def s375S := sampleAt 148 #[((OfNat.ofNat (limbs [0x14c2,0xb0003f3000630680,0x1003ff33cc00ffff])),(OfNat.ofNat (limbs [0x442,0xb224173228210291,0x52288b11cc925493]))),((OfNat.ofNat (limbs [0x6710,0xc00333c000849b00,0x1ffc00ccffffcc00])),(OfNat.ofNat (limbs [0x2510,0xc60f33c618008b30,0xd61d86445587cd8a]))),((OfNat.ofNat (limbs [0x8823,0x3c3ffff38e3ff,0xe00000f0f000f000])),(OfNat.ofNat (limbs [0x23,0x6d41507d28a383,0xe0781ef0f036f03a]))),(0x0,0x0),((OfNat.ofNat (limbs [0xcf03c,0x3fc0003c0fc00,0xff0000ffff])),(OfNat.ofNat (limbs [0xcf03c,0xccbe80cd3c0fc6a,0x8d5354ee0364ab6c]))),((OfNat.ofNat (limbs [0xf003f,0xfffc000003ff0000,0xffffff0000])),(OfNat.ofNat (limbs [0x50027,0x10f00000e3ff000b,0x16058bba8780070]))),((OfNat.ofNat (limbs [0xfffc0,0x3ffffff,0xffffff0000000000])),(OfNat.ofNat (limbs [0xfda80,0x880000882d6544c,0x982600002400240]))),(0x0,0x0),((OfNat.ofNat (limbs [0xfffff,0xfffffffffc000000,0x0])),(OfNat.ofNat (limbs [0xaffd8,0xef02beaf00000070,0xe03800003800380])))]
def s375C : List ColumnInfo := [(0,16,358,513,8),(2,0,373,512,7),(2,32,85,768,5),(4,0,371,512,7),(4,256,83,544,5),(17,0,358,512,7),(32,0,343,512,7),(36,256,83,512,4),(64,0,311,512,6),(256,0,119,512,7),(258,32,85,512,4),(290,0,85,512,4),(292,0,83,512,4)]
def s375D9 (_ : Nat) : Nat := 0x272ca67f
def s375H8 (_ : Nat) : Nat := (OfNat.ofNat (limbs [0x4bcb3872fc,0x806400aa000006f9,0x41cd800507801046]))
def s375D8 (_ : Nat) : Nat := (OfNat.ofNat (limbs [0x58801,0x30b50a1303548b2c,0x126a9166805032d4,0xea4410129eaa3c0d,0x512cb008ca6aa8e8,0x1a4062d54884bad9,0x9b399545a00ffd4,0x7fd64ff587fd21ff,0x547fd41ff553ff54]))
def s375H7 (_ : Nat) : Nat := (OfNat.ofNat (limbs [0x5e6d321da00,0x57546c2000032,0xcdacd4471a8a0e0a,0xa9c664d3a03033e]))
def s375D7 (_ : Nat) : Nat := (OfNat.ofNat (limbs [0x18,0x562c4000080c400,0x11a8b0d4586a2dd7,0x6c539cf5c3344440,0x5fe57487fab0ea37,0xf55d21bfc4eaa5fe,0x27547faa8a437f49,0xf54bfa4fa8cfd67d,0x52fb0baa96f91d61]))
def s375L : Nat → Packing
  | 9 => (1,0,4,0,0,1,0,s375D9)
  | 8 => (8,1,4,0,0,9,0,s375D8)
  | 7 => (11,2,4,0,0,7,0,s375D7)
  | _ => emptyPacking
def s375I : Nat → Nat → Option (Nat × Nat)
  | 9,h => lookupWord 5 19 3 8 3 1 s375H8 (mixTag h)
  | 8,h => lookupWord 7 23 4 9 4 1 s375H7 (mixTag h)
  | _,_ => none
def s375 : Forest := ⟨375,9,s375S,s375C,[[],[33,133]],s375L,s375I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs375_9_0 : block s375 9 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs375_9 : block s375 9 0 1 = true := bs375_9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs375_8_0 : block s375 8 0 8 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs375_8 : block s375 8 0 8 = true := bs375_8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs375_7_0 : block s375 7 0 3 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs375_7_3 : block s375 7 3 8 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs375_7 : block s375 7 0 11 = true := (@block_merge s375 7 0 3 8 bs375_7_0 bs375_7_3)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts375 : checkedTables s375 9 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs375_7
  · exact bs375_8
  · exact bs375_9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs375 : graphValid s375 (boundsBefore es367) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls375 : Lower true (vars 375) (graphGoal 375) 10 := lower_forest (g:=s375) (i:=0) (hints:=8590984788) (before_sound es367 vs367) gs375 ts375 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
end PEqualNP.Outside.L_meta_30332.P10830

namespace PEqualNP.Outside.L_meta_30332
open PEqualNP.Outside.L_meta_30332.P11311
open PEqualNP.CircuitLowerBounds
def rawEight : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero,inputs.getD 6 zero,inputs.getD 7 zero]
def goalEight : Sig := (OfNat.ofNat (limbs [0xffffffffffffffff,0xfffffffefffffffe,0xfffefffefffcfffc,0xfefefafaeeccaa00,0xffffffffffffffff,0xfffffffefffffffe,0xfffefffefffcfffc,0xfefefafaeeccaa00]))

def columnAt (i : Nat) := inputs.getD i zero
def swapAt (a b : Nat) : Move :=
  (columnAt a &&& neg (columnAt b),columnAt b &&& neg (columnAt a),Fin.ofNat 512 ((512 + 2^b - 2^a) % 512))
def clearAt (a : Nat) : Move := (columnAt a,zero, Fin.ofNat 512 (512-2^a))
def setAt (a : Nat) : Move := (neg (columnAt a),zero, Fin.ofNat 512 (2^a))
def dom0 : Sig := (OfNat.ofNat (limbs [0xffff0000ffff,0xffff0000ffff,0xffff0000ffff,0xffff0000ffff,0xffff0000ffff,0xffff0000ffff,0xffff0000ffff,0xffff0000ffff]))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem sl0 : Slice true rawEight goalEight dom0 11 := by
  have prior : Lower true (vars 127) (P11311.graphGoal 127) 11 := (plain_low (hints := 1049923) (by decide +kernel) excluded127)
  exact slice_correct (ms := [swapAt 1 2,swapAt 4 7,swapAt 5 7,swapAt 6 7,clearAt 4]) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) prior
def dom1 : Sig := (OfNat.ofNat (limbs [0x333300003333,0x333300003333,0x333300003333,0x333300003333,0x333300003333,0x333300003333,0x333300003333,0x333300003333]))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem sl1 : Slice true rawEight goalEight dom1 10 := by
  have prior : Lower true (vars 123) (P11311.graphGoal 123) 10 := bound123
  exact slice_correct (ms := [swapAt 1 2,swapAt 4 7,swapAt 5 7,swapAt 6 7,clearAt 1,clearAt 4]) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) prior
def dom2 : Sig := (OfNat.ofNat (limbs [0xf0f0f0f,0xf0f0f0f,0xf0f0f0f,0xf0f0f0f,0xf0f0f0f,0xf0f0f0f,0xf0f0f0f,0xf0f0f0f]))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem sl2 : Slice true rawEight goalEight dom2 10 := by
  have prior : Lower true (vars 119) (P10724.graphGoal 119) 10 := P10724.bound119
  exact slice_correct (ms := [swapAt 0 1,swapAt 1 5,swapAt 2 3,swapAt 3 4,swapAt 5 7,swapAt 6 7,clearAt 2,clearAt 5]) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) prior
def dom3 : Sig := (OfNat.ofNat (limbs [0xffffffffffffffff,0xffffffffffffffff,0x0,0x0,0xffffffffffffffff,0xffffffffffffffff]))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem sl3 : Slice true rawEight goalEight dom3 10 := by
  have prior : Lower true (vars 375) (P10830.graphGoal 375) 10 := P10830.ls375
  exact slice_correct (ms := [swapAt 0 5,swapAt 1 5,swapAt 3 5,swapAt 5 8,swapAt 7 8,clearAt 7]) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) prior
def dom4 : Sig := (OfNat.ofNat (limbs [0xf0f0f0f,0x0,0xf0f0f0f,0x0,0xf0f0f0f,0x0,0xf0f0f0f]))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem sl4 : Slice true rawEight goalEight dom4 8 := by
  have prior : Lower true (vars 118) (P10724.graphGoal 118) 8 := P10724.bound118
  exact slice_correct (ms := [swapAt 0 1,swapAt 1 2,swapAt 3 4,swapAt 4 5,swapAt 6 7,clearAt 2,clearAt 5,clearAt 6]) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) prior
def dom6 : Sig := (OfNat.ofNat (limbs [0x5500000055,0x5500000055,0x5500000055,0x5500000055,0x5500000055,0x5500000055,0x5500000055,0x5500000055]))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem sl6 : Slice true rawEight goalEight dom6 7 := by
  have prior : Lower true (vars 118) (P11311.graphGoal 118) 7 := bound118
  exact slice_correct (ms := [swapAt 1 2,swapAt 4 7,swapAt 5 7,swapAt 6 7,clearAt 0,clearAt 3,clearAt 4]) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) prior
def dom8 : Sig := (OfNat.ofNat (limbs [0x111100001111,0x111100001111,0x111100001111,0x111100001111,0x111100001111,0x111100001111,0x111100001111,0x111100001111]))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem sl8 : Slice true rawEight goalEight dom8 7 := by
  have prior : Lower true (vars 118) (P11311.graphGoal 118) 7 := bound118
  exact slice_correct (ms := [swapAt 1 3,swapAt 2 3,swapAt 4 7,swapAt 5 7,swapAt 6 7,clearAt 0,clearAt 1,clearAt 4]) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) prior
def dom11 : Sig := (OfNat.ofNat (limbs [0x550055,0x550055,0x550055,0x550055,0x550055,0x550055,0x550055,0x550055]))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem sl11 : Slice true rawEight goalEight dom11 7 := by
  have prior : Lower true (vars 107) (P11311.graphGoal 107) 7 := bound107
  exact slice_correct (ms := [swapAt 0 2,swapAt 1 5,swapAt 3 4,swapAt 4 5,swapAt 5 7,swapAt 6 7,clearAt 0,clearAt 3,clearAt 5]) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) prior
def dom12 : Sig := (OfNat.ofNat (limbs [0x505050500000000,0x505050500000000,0x505050500000000,0x505050500000000,0x505050500000000,0x505050500000000,0x505050500000000,0x505050500000000]))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem sl12 : Slice true rawEight goalEight dom12 7 := by
  have prior : Lower true (vars 107) (P11311.graphGoal 107) 7 := bound107
  exact slice_correct (ms := [swapAt 0 2,swapAt 1 5,swapAt 2 4,swapAt 3 4,swapAt 4 5,swapAt 5 7,swapAt 6 7,clearAt 0,clearAt 2,setAt 5]) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) prior
def dom14 : Sig := (OfNat.ofNat (limbs [0x3333000033330000,0x3333000033330000,0x0,0x0,0x3333000033330000,0x3333000033330000]))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem sl14 : Slice true rawEight goalEight dom14 7 := by
  have prior : Lower true (vars 59) (P11311.graphGoal 59) 7 := bound59
  exact slice_correct (ms := [swapAt 1 2,swapAt 4 6,swapAt 5 6,clearAt 1,setAt 4,clearAt 7]) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) prior
def dom16 : Sig := (OfNat.ofNat (limbs [0xf000f000f000f,0x0,0xf000f000f000f,0x0,0xf000f000f000f,0x0,0xf000f000f000f]))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem sl16 : Slice true rawEight goalEight dom16 7 := by
  have prior : Lower true (vars 211) (P10830.graphGoal 211) 7 := P10830.ls211
  exact slice_correct (ms := [swapAt 0 6,swapAt 1 4,swapAt 4 7,swapAt 5 7,swapAt 6 7,clearAt 2,clearAt 3,clearAt 6]) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) prior
def dom17 : Sig := (OfNat.ofNat (limbs [0x55005500550055,0x0,0x55005500550055,0x0,0x55005500550055,0x0,0x55005500550055]))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem sl17 : Slice true rawEight goalEight dom17 7 := by
  have prior : Lower true (vars 211) (P10830.graphGoal 211) 7 := P10830.ls211
  exact slice_correct (ms := [swapAt 0 2,swapAt 1 4,swapAt 2 6,swapAt 4 7,swapAt 5 7,swapAt 6 7,clearAt 0,clearAt 3,clearAt 6]) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) prior
def dom19 : Sig := (OfNat.ofNat (limbs [0xffffffff,0xffffffff,0x0,0x0,0xffffffff,0xffffffff]))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem sl19 : Slice true rawEight goalEight dom19 7 := by
  have prior : Lower true (vars 119) (P10830.graphGoal 119) 7 := P10830.ls119
  exact slice_correct (ms := [swapAt 0 4,swapAt 3 4,swapAt 4 5,clearAt 5,clearAt 7]) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) prior
def dom20 : Sig := (OfNat.ofNat (limbs [0x5555555555555555,0x5555555555555555,0x0,0x0,0x5555555555555555,0x5555555555555555]))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem sl20 : Slice true rawEight goalEight dom20 7 := by
  have prior : Lower true (vars 119) (P10830.graphGoal 119) 7 := P10830.ls119
  exact slice_correct (ms := [swapAt 0 3,swapAt 1 3,swapAt 2 3,clearAt 0,clearAt 7]) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) prior
def dom21 : Sig := (OfNat.ofNat (limbs [0xff00ff00ff00ff,0xff00ff00ff00ff,0x0,0x0,0xff00ff00ff00ff,0xff00ff00ff00ff]))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem sl21 : Slice true rawEight goalEight dom21 7 := by
  have prior : Lower true (vars 235) (P10830.graphGoal 235) 7 := P10830.ls235
  exact slice_correct (ms := [swapAt 0 3,swapAt 2 3,swapAt 4 5,swapAt 5 7,clearAt 3,clearAt 7]) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) prior
def dom23 : Sig := (OfNat.ofNat (limbs [0x333300003333,0x0,0x333300003333,0x0,0x333300003333,0x0,0x333300003333]))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem sl23 : Slice true rawEight goalEight dom23 6 := by
  have prior : Lower true (vars 91) (P11311.graphGoal 91) 6 := bound91
  exact slice_correct (ms := [swapAt 1 2,swapAt 4 5,swapAt 6 7,clearAt 1,clearAt 4,clearAt 6]) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) prior
def dom29 : Sig := (OfNat.ofNat (limbs [0xffff,0x0,0xffff,0x0,0xffff,0x0,0xffff]))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem sl29 : Slice true rawEight goalEight dom29 6 := by
  have prior : Lower true (vars 79) (P10724.graphGoal 79) 6 := P10724.bound79
  exact slice_correct (ms := [swapAt 6 7,clearAt 4,clearAt 5,clearAt 6]) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) prior
def dom34 : Sig := (OfNat.ofNat (limbs [0xf0f00000f0f,0x0,0xf0f00000f0f,0x0,0xf0f00000f0f,0x0,0xf0f00000f0f]))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem sl34 : Slice true rawEight goalEight dom34 6 := by
  have prior : Lower true (vars 217) (P10830.graphGoal 217) 6 := P10830.ls217
  exact slice_correct (ms := [swapAt 1 3,swapAt 2 3,swapAt 3 4,swapAt 5 6,clearAt 2,clearAt 4,clearAt 6]) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) prior
def dom42 : Sig := (OfNat.ofNat (limbs [0x505050500000000,0x0,0x505050500000000,0x0,0x505050500000000,0x0,0x505050500000000]))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem sl42 : Slice true rawEight goalEight dom42 5 := by
  have prior : Lower true (vars 75) (P11311.graphGoal 75) 5 := bound75
  exact slice_correct (ms := [swapAt 0 2,swapAt 1 2,swapAt 2 4,swapAt 3 4,swapAt 6 7,clearAt 0,clearAt 2,setAt 5,clearAt 6]) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) prior
def dom56 : Sig := (OfNat.ofNat (limbs [0x5000500000000,0x5000500000000,0x5000500000000,0x5000500000000,0x5000500000000,0x5000500000000,0x5000500000000,0x5000500000000]))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem sl56 : Slice true rawEight goalEight dom56 5 := by
  have prior : Lower true (vars 102) (P11311.graphGoal 102) 5 := bound102
  exact slice_correct (ms := [swapAt 1 5,swapAt 2 3,swapAt 3 4,swapAt 4 5,swapAt 5 7,swapAt 6 7,clearAt 0,clearAt 2,clearAt 3,setAt 5]) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) prior
def dom59 : Sig := (OfNat.ofNat (limbs [0x5000500000000,0x0,0x5000500000000,0x0,0x5000500000000,0x0,0x5000500000000]))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem sl59 : Slice true rawEight goalEight dom59 4 := by
  have prior : Lower true (vars 73) (P11311.graphGoal 73) 4 := bound73
  exact slice_correct (ms := [swapAt 0 1,swapAt 3 4,swapAt 6 7,clearAt 0,clearAt 2,clearAt 3,setAt 5,clearAt 6]) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) prior
def posRows (i : Fin 1024) : Row := ([13,23,30,11,85,46,35,120,15,15,22,23,30,39,46,78,70,113,71,142,134,161,135,83,162,164,168,37,69,133,176,49,113,138,145,224,209,35,15,76,130,208,22,38,22,38,70,60,60,156,43,58,58,106] : List Row).getD (i.val % 54) 0
def negRows (i : Fin 1024) : Row := ([14,21,28,14,81,42,34,112,7,14,7,7,14,7,14,14,7,112,7,14,7,160,7,81,160,160,160,21,21,21,160,81,81,42,81,160,81,42,6,28,34,112,20,34,6,6,6,56,28,28,42,56,42,42] : List Row).getD (i.val % 54) 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem admPairs : properPairs goalEight posRows negRows := by unfold properPairs; decide +kernel

abbrev CheckedWire := {v : Decor // faithful posRows negRows v}
abbrev CheckedPool := {v : BoundPool // ValidPool true rawEight goalEight v}
def newWire (d : Nat) (a b : CheckedWire) : CheckedWire :=
  ⟨dbin d a.val b.val, faithful_bin d a.property b.property⟩
def choiceW (d : Nat) (a b : CheckedWire) : Choice := (d,a.val.1,b.val.1)
def initialPool {dom lb} (h : Slice true rawEight goalEight dom lb) (cs : List Choice)
    (ok : makePool true dom rawEight cs = some (cs.reverse.map choiceVal ++ rawEight)) : CheckedPool :=
  ⟨(dom,lb,cs.length,cs.reverse.map choiceVal ++ rawEight),build_valid h cs ok⟩
def decs (v : List CheckedWire) : List Decor := v.map Subtype.val
def signals (v : List CheckedWire) : List Sig := (decs v).map Prod.fst
def Done (k : Nat) (v : List CheckedWire) := Impossible true goalEight k (signals v).toFinset
abbrev Child (k : Nat) := {v : List CheckedWire // Done k v}
def nextW {k} (children : List (Child k)) (_tag : Nat) := children.map (fun v => signals v.val)
def poolsW (p : List CheckedPool) := p.map Subtype.val
def branches (k : Nat) (v : List CheckedWire) (ps : List CheckedPool) (cs : List (Child (k-1))) :=
  let w := decs v
  cached_testAll (k,w.length,w,preCov true w,(poolsW ps).map (cacheOnePool true (signals v)),nextW cs) w
theorem certify {k} (v : List CheckedWire) (ps : List CheckedPool) (cs : List (Child (k-1)))
    (nd : (signals v).Nodup) (absent : goalEight ∉ signals v)
    (ok : branches k v ps cs = true) : Done k v := by
  apply cached_node_sound (raw := rawEight) (ws := decs v) (pools := poolsW ps) (links := nextW cs) (cap := k) admPairs _ nd absent _ _ ok
  · intro w hw
    obtain ⟨q,_,rfl⟩ := List.mem_map.mp hw
    exact q.property
  · intro w hw
    obtain ⟨q,_,rfl⟩ := List.mem_map.mp hw
    exact q.property
  · intro tag w hw
    obtain ⟨q,_,rfl⟩ := List.mem_map.mp hw
    exact q.property
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def w0 : CheckedWire := ⟨(inputs.getD 0 zero,(OfNat.ofNat (limbs [0x40075b8e62b5b100,0x1d6e398ad6c40075,0xb8e62b5b1001d6e3,0x98ad6c40075b8e62,0xb5b1001d6e398ad6,0xc40075b8e62b5b10,0x1d6e398ad6c4007,0x5b8e62b5b1001d6e,0x398ad6c40075b8e6,0x2b5b1001d6e398ad,0x6c40075b8e62b5b1,0x1d6e398ad6c400,0x75b8e62b5b1001d6,0xe398ad6c40075b8e,0x62b5b1001d6e398a,0xd6c40075b8e62b5b])),(OfNat.ofNat (limbs [0x15b8d52d12000,0x56e354b44800015,0xb8d52d12000056e3,0x54b44800015b8d52,0xd12000056e354b44,0x800015b8d52d1200,0x56e354b4480001,0x5b8d52d12000056e,0x354b44800015b8d5,0x2d12000056e354b4,0x4800015b8d52d120,0x56e354b448000,0x15b8d52d12000056,0xe354b44800015b8d,0x52d12000056e354b,0x44800015b8d52d12]))),by unfold faithful; decide +kernel⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def w1 : CheckedWire := ⟨(inputs.getD 1 zero,(OfNat.ofNat (limbs [0xc7d6201ddff6ef1f,0x5880777fdbbc7d62,0x1ddff6ef1f58807,0x77fdbbc7d6201ddf,0xf6ef1f5880777fdb,0xbc7d6201ddff6ef1,0xf5880777fdbbc7d6,0x201ddff6ef1f5880,0x777fdbbc7d6201dd,0xff6ef1f5880777fd,0xbbc7d6201ddff6ef,0x1f5880777fdbbc7d,0x6201ddff6ef1f588,0x777fdbbc7d6201d,0xdff6ef1f5880777f,0xdbbc7d6201ddff6e])),(OfNat.ofNat (limbs [0x47962005dff69d1e,0x5880177fda747962,0x5dff69d1e58801,0x77fda747962005df,0xf69d1e5880177fda,0x747962005dff69d1,0xe5880177fda74796,0x2005dff69d1e5880,0x177fda747962005d,0xff69d1e5880177fd,0xa747962005dff69d,0x1e5880177fda7479,0x62005dff69d1e588,0x177fda747962005,0xdff69d1e5880177f,0xda747962005dff69]))),by unfold faithful; decide +kernel⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def w2 : CheckedWire := ⟨(inputs.getD 2 zero,(OfNat.ofNat (limbs [0x3fcc03a5dff370ff,0x300e977fcdc3fcc0,0x3a5dff370ff300e9,0x77fcdc3fcc03a5df,0xf370ff300e977fcd,0xc3fcc03a5dff370f,0xf300e977fcdc3fcc,0x3a5dff370ff300e,0x977fcdc3fcc03a5d,0xff370ff300e977fc,0xdc3fcc03a5dff370,0xff300e977fcdc3fc,0xc03a5dff370ff300,0xe977fcdc3fcc03a5,0xdff370ff300e977f,0xcdc3fcc03a5dff37])),(OfNat.ofNat (limbs [0x374c0385dff0f0dd,0x300e177fc3c374c0,0x385dff0f0dd300e1,0x77fc3c374c0385df,0xf0f0dd300e177fc3,0xc374c0385dff0f0d,0xd300e177fc3c374c,0x385dff0f0dd300e,0x177fc3c374c0385d,0xff0f0dd300e177fc,0x3c374c0385dff0f0,0xdd300e177fc3c374,0xc0385dff0f0dd300,0xe177fc3c374c0385,0xdff0f0dd300e177f,0xc3c374c0385dff0f]))),by unfold faithful; decide +kernel⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def w3 : CheckedWire := ⟨(inputs.getD 3 zero,(OfNat.ofNat (limbs [0xf80c20408d3adfe0,0x30810234eb7f80c2,0x408d3adfe030810,0x234eb7f80c20408d,0x3adfe030810234eb,0x7f80c20408d3adfe,0x30810234eb7f80c,0x20408d3adfe03081,0x234eb7f80c20408,0xd3adfe030810234e,0xb7f80c20408d3adf,0xe030810234eb7f80,0xc20408d3adfe0308,0x10234eb7f80c2040,0x8d3adfe030810234,0xeb7f80c20408d3ad])),(OfNat.ofNat (limbs [0xf80a20008d22dfe0,0x288002348b7f80a2,0x8d22dfe028800,0x2348b7f80a20008d,0x22dfe0288002348b,0x7f80a20008d22dfe,0x288002348b7f80a,0x20008d22dfe02880,0x2348b7f80a20008,0xd22dfe0288002348,0xb7f80a20008d22df,0xe0288002348b7f80,0xa20008d22dfe0288,0x2348b7f80a2000,0x8d22dfe028800234,0x8b7f80a20008d22d]))),by unfold faithful; decide +kernel⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def w4 : CheckedWire := ⟨(inputs.getD 4 zero,(OfNat.ofNat (limbs [0xb9615c0821c966e5,0x85702087259b9615,0xc0821c966e585702,0x87259b9615c0821,0xc966e58570208725,0x9b9615c0821c966e,0x585702087259b961,0x5c0821c966e58570,0x2087259b9615c082,0x1c966e5857020872,0x59b9615c0821c966,0xe585702087259b96,0x15c0821c966e5857,0x2087259b9615c08,0x21c966e585702087,0x259b9615c0821c96])),(OfNat.ofNat (limbs [0xb8695b88200962e1,0xa56e2080258b8695,0xb88200962e1a56e2,0x80258b8695b8820,0x962e1a56e208025,0x8b8695b88200962e,0x1a56e2080258b869,0x5b88200962e1a56e,0x2080258b8695b882,0x962e1a56e20802,0x58b8695b88200962,0xe1a56e2080258b86,0x95b88200962e1a56,0xe2080258b8695b88,0x200962e1a56e2080,0x258b8695b8820096]))),by unfold faithful; decide +kernel⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def w5 : CheckedWire := ⟨(inputs.getD 5 zero,(OfNat.ofNat (limbs [0xda829cf2260e0f6a,0xa73c898383da829,0xcf2260e0f6a0a73c,0x898383da829cf226,0xe0f6a0a73c89838,0x3da829cf2260e0f6,0xa0a73c898383da82,0x9cf2260e0f6a0a73,0xc898383da829cf22,0x60e0f6a0a73c8983,0x83da829cf2260e0f,0x6a0a73c898383da8,0x29cf2260e0f6a0a7,0x3c898383da829cf2,0x260e0f6a0a73c898,0x383da829cf2260e0])),(OfNat.ofNat (limbs [0xc8b2a472200e0f22,0xca91c880383c8b2a,0x472200e0f22ca91c,0x880383c8b2a47220,0xe0f22ca91c88038,0x3c8b2a472200e0f2,0x2ca91c880383c8b2,0xa472200e0f22ca91,0xc880383c8b2a4722,0xe0f22ca91c8803,0x83c8b2a472200e0f,0x22ca91c880383c8b,0x2a472200e0f22ca9,0x1c880383c8b2a472,0x200e0f22ca91c880,0x383c8b2a472200e0]))),by unfold faithful; decide +kernel⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def w6 : CheckedWire := ⟨(inputs.getD 6 zero,(OfNat.ofNat (limbs [0x429910878090810,0xa64421e024204299,0x10878090810a6442,0x1e02420429910878,0x90810a64421e024,0x2042991087809081,0xa64421e02420429,0x910878090810a644,0x21e0242042991087,0x8090810a64421e02,0x4204299108780908,0x10a64421e0242042,0x9910878090810a64,0x421e024204299108,0x78090810a64421e0,0x2420429910878090])),(OfNat.ofNat (limbs [0x21580820090000,0x8560208024000215,0x8082009000085602,0x802400021580820,0x900008560208024,0x2158082009000,0x856020802400021,0x5808200900008560,0x2080240002158082,0x90000856020802,0x4000215808200900,0x85602080240002,0x1580820090000856,0x208024000215808,0x2009000085602080,0x2400021580820090]))),by unfold faithful; decide +kernel⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def w7 : CheckedWire := ⟨(inputs.getD 7 zero,(OfNat.ofNat (limbs [0x2031e67780000080,0xc799de000002031e,0x67780000080c799d,0xe000002031e67780,0x80c799de0000,0x2031e6778000008,0xc799de000002031,0xe67780000080c799,0xde000002031e6778,0x80c799de000,0x2031e677800000,0x80c799de00000203,0x1e67780000080c79,0x9de000002031e677,0x80000080c799de00,0x2031e67780000])),(OfNat.ofNat (limbs [0x847200000000,0x211c80000000008,0x472000000000211c,0x8000000000847200,0x211c80000,0x84720000000,0x211c8000000000,0x8472000000000211,0xc800000000084720,0x211c8000,0x8472000000,0x211c800000000,0x847200000000021,0x1c80000000008472,0x211c800,0x847200000]))),by unfold faithful; decide +kernel⟩
def w8 := newWire 0 w0 w3
def w9 := newWire 1 w0 w3
def w10 := newWire 2 w0 w3
def w11 := newWire 3 w0 w3
def w12 := newWire 1 w0 w6
def w13 := newWire 2 w0 w6
def w14 := newWire 1 w0 w7
def w15 := newWire 2 w0 w7
def w16 := newWire 1 w3 w6
def w17 := newWire 2 w3 w6
def w18 := newWire 1 w3 w7
def w19 := newWire 2 w3 w7
def w20 := newWire 1 w4 w6
def w21 := newWire 1 w5 w7
def w22 := newWire 1 w6 w7
def w23 := newWire 1 w1 w8
def w24 := newWire 1 w2 w8
def w25 := newWire 1 w4 w8
def w26 := newWire 1 w5 w8
def w27 := newWire 1 w6 w8
def w28 := newWire 2 w6 w8
def w29 := newWire 1 w7 w8
def w30 := newWire 2 w7 w8
def w31 := newWire 1 w7 w9
def w32 := newWire 1 w7 w10
def w33 := newWire 1 w7 w11
def w34 := newWire 1 w7 w12
def w35 := newWire 1 w2 w13
def w36 := newWire 1 w7 w13
def w37 := newWire 3 w3 w14
def w38 := newWire 3 w6 w14
def w39 := newWire 1 w7 w16
def w40 := newWire 1 w7 w17
def w41 := newWire 3 w0 w18
def w42 := newWire 3 w6 w18
def w43 := newWire 3 w0 w20
def w44 := newWire 3 w3 w20
def w45 := newWire 0 w3 w21
def w46 := newWire 3 w3 w21
def w47 := newWire 3 w6 w21
def w48 := newWire 3 w0 w22
def w49 := newWire 3 w3 w22
def w50 := newWire 3 w3 w34
def w51 := newWire 1 w5 w48
def w52 := newWire 3 w0 w50
def p0 := initialPool sl0 [] (by decide +kernel)
def p1 := initialPool sl1 [] (by decide +kernel)
def p2 := initialPool sl2 [] (by decide +kernel)
def p3 := initialPool sl3 [] (by decide +kernel)
def p4 := initialPool sl4 [] (by decide +kernel)
def q0 := choiceW 0 w0 w3
def p5 := initialPool sl0 [q0] (by decide +kernel)
def p6 := initialPool sl1 [q0] (by decide +kernel)
def p7 := initialPool sl2 [q0] (by decide +kernel)
def p8 := initialPool sl3 [q0] (by decide +kernel)
def p9 := initialPool sl4 [q0] (by decide +kernel)
def p10 := initialPool sl6 [] (by decide +kernel)
def p11 := initialPool sl8 [] (by decide +kernel)
def p12 := initialPool sl11 [] (by decide +kernel)
def p13 := initialPool sl12 [] (by decide +kernel)
def p14 := initialPool sl16 [] (by decide +kernel)
def p15 := initialPool sl17 [] (by decide +kernel)
def q1 := choiceW 1 w0 w3
def p16 := initialPool sl0 [q1] (by decide +kernel)
def p17 := initialPool sl1 [q1] (by decide +kernel)
def p18 := initialPool sl2 [q1] (by decide +kernel)
def p19 := initialPool sl3 [q1] (by decide +kernel)
def p20 := initialPool sl4 [q1] (by decide +kernel)
def q2 := choiceW 2 w0 w3
def p21 := initialPool sl0 [q2] (by decide +kernel)
def p22 := initialPool sl1 [q2] (by decide +kernel)
def p23 := initialPool sl2 [q2] (by decide +kernel)
def p24 := initialPool sl3 [q2] (by decide +kernel)
def p25 := initialPool sl4 [q2] (by decide +kernel)
def q3 := choiceW 3 w0 w3
def p26 := initialPool sl0 [q3] (by decide +kernel)
def p27 := initialPool sl1 [q3] (by decide +kernel)
def p28 := initialPool sl2 [q3] (by decide +kernel)
def p29 := initialPool sl3 [q3] (by decide +kernel)
def p30 := initialPool sl4 [q3] (by decide +kernel)
def q4 := choiceW 1 w0 w6
def p31 := initialPool sl0 [q4] (by decide +kernel)
def p32 := initialPool sl1 [q4] (by decide +kernel)
def p33 := initialPool sl2 [q4] (by decide +kernel)
def p34 := initialPool sl3 [q4] (by decide +kernel)
def q5 := choiceW 2 w0 w6
def p35 := initialPool sl0 [q5] (by decide +kernel)
def p36 := initialPool sl1 [q5] (by decide +kernel)
def p37 := initialPool sl2 [q5] (by decide +kernel)
def p38 := initialPool sl3 [q5] (by decide +kernel)
def q6 := choiceW 1 w0 w7
def p39 := initialPool sl0 [q6] (by decide +kernel)
def p40 := initialPool sl1 [q6] (by decide +kernel)
def p41 := initialPool sl2 [q6] (by decide +kernel)
def p42 := initialPool sl4 [q6] (by decide +kernel)
def p43 := initialPool sl20 [] (by decide +kernel)
def q7 := choiceW 2 w0 w7
def p44 := initialPool sl0 [q7] (by decide +kernel)
def p45 := initialPool sl1 [q7] (by decide +kernel)
def p46 := initialPool sl2 [q7] (by decide +kernel)
def p47 := initialPool sl4 [q7] (by decide +kernel)
def q8 := choiceW 1 w3 w6
def p48 := initialPool sl0 [q8] (by decide +kernel)
def p49 := initialPool sl1 [q8] (by decide +kernel)
def p50 := initialPool sl2 [q8] (by decide +kernel)
def p51 := initialPool sl3 [q8] (by decide +kernel)
def q9 := choiceW 2 w3 w6
def p52 := initialPool sl0 [q9] (by decide +kernel)
def p53 := initialPool sl1 [q9] (by decide +kernel)
def p54 := initialPool sl2 [q9] (by decide +kernel)
def p55 := initialPool sl3 [q9] (by decide +kernel)
def q10 := choiceW 1 w3 w7
def p56 := initialPool sl0 [q10] (by decide +kernel)
def p57 := initialPool sl1 [q10] (by decide +kernel)
def p58 := initialPool sl2 [q10] (by decide +kernel)
def p59 := initialPool sl4 [q10] (by decide +kernel)
def p60 := initialPool sl21 [] (by decide +kernel)
def q11 := choiceW 2 w3 w7
def p61 := initialPool sl0 [q11] (by decide +kernel)
def p62 := initialPool sl1 [q11] (by decide +kernel)
def p63 := initialPool sl2 [q11] (by decide +kernel)
def p64 := initialPool sl4 [q11] (by decide +kernel)
def q12 := choiceW 1 w4 w6
def p65 := initialPool sl2 [q12] (by decide +kernel)
def p66 := initialPool sl3 [q12] (by decide +kernel)
def p67 := initialPool sl14 [] (by decide +kernel)
def q13 := choiceW 1 w5 w7
def p68 := initialPool sl0 [q13] (by decide +kernel)
def p69 := initialPool sl1 [q13] (by decide +kernel)
def q14 := choiceW 1 w6 w7
def p70 := initialPool sl0 [q14] (by decide +kernel)
def p71 := initialPool sl1 [q14] (by decide +kernel)
def p72 := initialPool sl2 [q14] (by decide +kernel)
def q15 := choiceW 1 w1 w8
def p73 := initialPool sl0 [q0,q15] (by decide +kernel)
def p74 := initialPool sl2 [q0,q15] (by decide +kernel)
def p75 := initialPool sl3 [q0,q15] (by decide +kernel)
def p76 := initialPool sl4 [q0,q15] (by decide +kernel)
def q16 := choiceW 1 w2 w8
def p77 := initialPool sl0 [q0,q16] (by decide +kernel)
def p78 := initialPool sl1 [q0,q16] (by decide +kernel)
def p79 := initialPool sl3 [q0,q16] (by decide +kernel)
def q17 := choiceW 1 w4 w8
def p80 := initialPool sl2 [q0,q17] (by decide +kernel)
def p81 := initialPool sl3 [q0,q17] (by decide +kernel)
def p82 := initialPool sl4 [q0,q17] (by decide +kernel)
def q18 := choiceW 1 w5 w8
def p83 := initialPool sl0 [q0,q18] (by decide +kernel)
def p84 := initialPool sl1 [q0,q18] (by decide +kernel)
def p85 := initialPool sl3 [q0,q18] (by decide +kernel)
def q19 := choiceW 1 w6 w8
def p86 := initialPool sl0 [q0,q19] (by decide +kernel)
def p87 := initialPool sl1 [q0,q19] (by decide +kernel)
def p88 := initialPool sl2 [q0,q19] (by decide +kernel)
def p89 := initialPool sl3 [q0,q19] (by decide +kernel)
def q20 := choiceW 2 w6 w8
def p90 := initialPool sl0 [q0,q20] (by decide +kernel)
def p91 := initialPool sl1 [q0,q20] (by decide +kernel)
def p92 := initialPool sl2 [q0,q20] (by decide +kernel)
def p93 := initialPool sl3 [q0,q20] (by decide +kernel)
def q21 := choiceW 1 w7 w8
def p94 := initialPool sl0 [q0,q21] (by decide +kernel)
def p95 := initialPool sl1 [q0,q21] (by decide +kernel)
def p96 := initialPool sl2 [q0,q21] (by decide +kernel)
def p97 := initialPool sl4 [q0,q21] (by decide +kernel)
def q22 := choiceW 2 w7 w8
def p98 := initialPool sl0 [q0,q22] (by decide +kernel)
def p99 := initialPool sl1 [q0,q22] (by decide +kernel)
def p100 := initialPool sl2 [q0,q22] (by decide +kernel)
def p101 := initialPool sl4 [q0,q22] (by decide +kernel)
def p102 := initialPool sl0 [q1,q6] (by decide +kernel)
def p103 := initialPool sl1 [q1,q6] (by decide +kernel)
def p104 := initialPool sl2 [q1,q6] (by decide +kernel)
def p105 := initialPool sl4 [q1,q6] (by decide +kernel)
def p106 := initialPool sl16 [q6] (by decide +kernel)
def p107 := initialPool sl0 [q1,q10] (by decide +kernel)
def p108 := initialPool sl1 [q1,q10] (by decide +kernel)
def p109 := initialPool sl2 [q1,q10] (by decide +kernel)
def p110 := initialPool sl4 [q1,q10] (by decide +kernel)
def p111 := initialPool sl0 [q1,q13] (by decide +kernel)
def p112 := initialPool sl1 [q1,q13] (by decide +kernel)
def p113 := initialPool sl6 [q13] (by decide +kernel)
def p114 := initialPool sl8 [q13] (by decide +kernel)
def p115 := initialPool sl16 [q13] (by decide +kernel)
def p116 := initialPool sl17 [q13] (by decide +kernel)
def q23 := choiceW 1 w7 w9
def p117 := initialPool sl0 [q1,q23] (by decide +kernel)
def p118 := initialPool sl1 [q1,q23] (by decide +kernel)
def p119 := initialPool sl2 [q1,q23] (by decide +kernel)
def p120 := initialPool sl4 [q1,q23] (by decide +kernel)
def p121 := initialPool sl16 [q23] (by decide +kernel)
def p122 := initialPool sl0 [q2,q6] (by decide +kernel)
def p123 := initialPool sl1 [q2,q6] (by decide +kernel)
def p124 := initialPool sl2 [q2,q6] (by decide +kernel)
def p125 := initialPool sl4 [q2,q6] (by decide +kernel)
def q24 := choiceW 1 w7 w10
def p126 := initialPool sl0 [q2,q24] (by decide +kernel)
def p127 := initialPool sl1 [q2,q24] (by decide +kernel)
def p128 := initialPool sl2 [q2,q24] (by decide +kernel)
def p129 := initialPool sl4 [q2,q24] (by decide +kernel)
def p130 := initialPool sl0 [q3,q10] (by decide +kernel)
def p131 := initialPool sl1 [q3,q10] (by decide +kernel)
def p132 := initialPool sl2 [q3,q10] (by decide +kernel)
def p133 := initialPool sl4 [q3,q10] (by decide +kernel)
def p134 := initialPool sl0 [q3,q13] (by decide +kernel)
def p135 := initialPool sl1 [q3,q13] (by decide +kernel)
def q25 := choiceW 1 w7 w11
def p136 := initialPool sl0 [q3,q25] (by decide +kernel)
def p137 := initialPool sl1 [q3,q25] (by decide +kernel)
def p138 := initialPool sl2 [q3,q25] (by decide +kernel)
def p139 := initialPool sl4 [q3,q25] (by decide +kernel)
def p140 := initialPool sl0 [q4,q6] (by decide +kernel)
def p141 := initialPool sl1 [q4,q6] (by decide +kernel)
def p142 := initialPool sl2 [q4,q6] (by decide +kernel)
def p143 := initialPool sl0 [q4,q13] (by decide +kernel)
def p144 := initialPool sl1 [q4,q13] (by decide +kernel)
def p145 := initialPool sl42 [] (by decide +kernel)
def p146 := initialPool sl0 [q4,q14] (by decide +kernel)
def p147 := initialPool sl1 [q4,q14] (by decide +kernel)
def p148 := initialPool sl2 [q4,q14] (by decide +kernel)
def p149 := initialPool sl6 [q14] (by decide +kernel)
def p150 := initialPool sl8 [q14] (by decide +kernel)
def p151 := initialPool sl11 [q14] (by decide +kernel)
def q26 := choiceW 1 w7 w12
def p152 := initialPool sl0 [q4,q26] (by decide +kernel)
def p153 := initialPool sl1 [q4,q26] (by decide +kernel)
def p154 := initialPool sl2 [q4,q26] (by decide +kernel)
def p155 := initialPool sl4 [q26] (by decide +kernel)
def p156 := initialPool sl6 [q26] (by decide +kernel)
def p157 := initialPool sl8 [q26] (by decide +kernel)
def p158 := initialPool sl11 [q26] (by decide +kernel)
def p159 := initialPool sl16 [q26] (by decide +kernel)
def p160 := initialPool sl0 [q5,q6] (by decide +kernel)
def p161 := initialPool sl1 [q5,q6] (by decide +kernel)
def p162 := initialPool sl2 [q5,q6] (by decide +kernel)
def q27 := choiceW 1 w2 w13
def p163 := initialPool sl0 [q5,q27] (by decide +kernel)
def p164 := initialPool sl1 [q5,q27] (by decide +kernel)
def p165 := initialPool sl3 [q5,q27] (by decide +kernel)
def q28 := choiceW 1 w7 w13
def p166 := initialPool sl0 [q5,q28] (by decide +kernel)
def p167 := initialPool sl1 [q5,q28] (by decide +kernel)
def p168 := initialPool sl2 [q5,q28] (by decide +kernel)
def p169 := initialPool sl4 [q28] (by decide +kernel)
def p170 := initialPool sl0 [q6,q10] (by decide +kernel)
def p171 := initialPool sl1 [q6,q10] (by decide +kernel)
def p172 := initialPool sl2 [q6,q10] (by decide +kernel)
def p173 := initialPool sl4 [q6,q10] (by decide +kernel)
def q29 := choiceW 1 w3 w14
def p174 := initialPool sl0 [q6,q29] (by decide +kernel)
def p175 := initialPool sl1 [q6,q29] (by decide +kernel)
def p176 := initialPool sl2 [q6,q29] (by decide +kernel)
def p177 := initialPool sl3 [q29] (by decide +kernel)
def p178 := initialPool sl4 [q6,q29] (by decide +kernel)
def q30 := choiceW 3 w3 w14
def p179 := initialPool sl0 [q6,q30] (by decide +kernel)
def p180 := initialPool sl1 [q6,q30] (by decide +kernel)
def p181 := initialPool sl2 [q6,q30] (by decide +kernel)
def p182 := initialPool sl3 [q30] (by decide +kernel)
def p183 := initialPool sl4 [q6,q30] (by decide +kernel)
def p184 := initialPool sl2 [q6,q12] (by decide +kernel)
def p185 := initialPool sl20 [q12] (by decide +kernel)
def p186 := initialPool sl0 [q6,q13] (by decide +kernel)
def p187 := initialPool sl1 [q6,q13] (by decide +kernel)
def q31 := choiceW 1 w6 w14
def p188 := initialPool sl0 [q6,q31] (by decide +kernel)
def p189 := initialPool sl1 [q6,q31] (by decide +kernel)
def p190 := initialPool sl2 [q6,q31] (by decide +kernel)
def p191 := initialPool sl3 [q31] (by decide +kernel)
def p192 := initialPool sl6 [q31] (by decide +kernel)
def p193 := initialPool sl8 [q31] (by decide +kernel)
def p194 := initialPool sl11 [q31] (by decide +kernel)
def q32 := choiceW 3 w6 w14
def p195 := initialPool sl0 [q6,q32] (by decide +kernel)
def p196 := initialPool sl1 [q6,q32] (by decide +kernel)
def p197 := initialPool sl2 [q6,q32] (by decide +kernel)
def p198 := initialPool sl3 [q32] (by decide +kernel)
def p199 := initialPool sl6 [q32] (by decide +kernel)
def p200 := initialPool sl8 [q32] (by decide +kernel)
def p201 := initialPool sl11 [q32] (by decide +kernel)
def p202 := initialPool sl0 [q8,q10] (by decide +kernel)
def p203 := initialPool sl1 [q8,q10] (by decide +kernel)
def p204 := initialPool sl2 [q8,q10] (by decide +kernel)
def p205 := initialPool sl0 [q8,q13] (by decide +kernel)
def p206 := initialPool sl1 [q8,q13] (by decide +kernel)
def p207 := initialPool sl12 [q8] (by decide +kernel)
def p208 := initialPool sl59 [] (by decide +kernel)
def p209 := initialPool sl0 [q8,q14] (by decide +kernel)
def p210 := initialPool sl1 [q8,q14] (by decide +kernel)
def p211 := initialPool sl2 [q8,q14] (by decide +kernel)
def q33 := choiceW 1 w7 w16
def p212 := initialPool sl0 [q8,q33] (by decide +kernel)
def p213 := initialPool sl1 [q8,q33] (by decide +kernel)
def p214 := initialPool sl2 [q8,q33] (by decide +kernel)
def p215 := initialPool sl4 [q33] (by decide +kernel)
def p216 := initialPool sl6 [q33] (by decide +kernel)
def p217 := initialPool sl11 [q33] (by decide +kernel)
def p218 := initialPool sl0 [q9,q10] (by decide +kernel)
def p219 := initialPool sl1 [q9,q10] (by decide +kernel)
def p220 := initialPool sl2 [q9,q10] (by decide +kernel)
def p221 := initialPool sl0 [q9,q13] (by decide +kernel)
def p222 := initialPool sl1 [q9,q13] (by decide +kernel)
def p223 := initialPool sl12 [q9] (by decide +kernel)
def p224 := initialPool sl56 [] (by decide +kernel)
def q34 := choiceW 1 w7 w17
def p225 := initialPool sl0 [q9,q34] (by decide +kernel)
def p226 := initialPool sl1 [q9,q34] (by decide +kernel)
def p227 := initialPool sl2 [q9,q34] (by decide +kernel)
def p228 := initialPool sl4 [q34] (by decide +kernel)
def q35 := choiceW 1 w0 w18
def p229 := initialPool sl0 [q10,q35] (by decide +kernel)
def p230 := initialPool sl1 [q10,q35] (by decide +kernel)
def p231 := initialPool sl2 [q10,q35] (by decide +kernel)
def p232 := initialPool sl3 [q35] (by decide +kernel)
def p233 := initialPool sl4 [q10,q35] (by decide +kernel)
def p234 := initialPool sl16 [q35] (by decide +kernel)
def q36 := choiceW 3 w0 w18
def p235 := initialPool sl0 [q10,q36] (by decide +kernel)
def p236 := initialPool sl1 [q10,q36] (by decide +kernel)
def p237 := initialPool sl2 [q10,q36] (by decide +kernel)
def p238 := initialPool sl3 [q36] (by decide +kernel)
def p239 := initialPool sl4 [q10,q36] (by decide +kernel)
def p240 := initialPool sl16 [q36] (by decide +kernel)
def p241 := initialPool sl2 [q10,q12] (by decide +kernel)
def p242 := initialPool sl21 [q12] (by decide +kernel)
def p243 := initialPool sl0 [q10,q14] (by decide +kernel)
def p244 := initialPool sl1 [q10,q14] (by decide +kernel)
def p245 := initialPool sl2 [q10,q14] (by decide +kernel)
def q37 := choiceW 1 w6 w18
def p246 := initialPool sl0 [q10,q37] (by decide +kernel)
def p247 := initialPool sl1 [q10,q37] (by decide +kernel)
def p248 := initialPool sl2 [q10,q37] (by decide +kernel)
def p249 := initialPool sl3 [q37] (by decide +kernel)
def p250 := initialPool sl6 [q37] (by decide +kernel)
def p251 := initialPool sl11 [q37] (by decide +kernel)
def q38 := choiceW 3 w6 w18
def p252 := initialPool sl0 [q10,q38] (by decide +kernel)
def p253 := initialPool sl1 [q10,q38] (by decide +kernel)
def p254 := initialPool sl2 [q10,q38] (by decide +kernel)
def p255 := initialPool sl3 [q38] (by decide +kernel)
def p256 := initialPool sl6 [q38] (by decide +kernel)
def p257 := initialPool sl11 [q38] (by decide +kernel)
def q39 := choiceW 3 w0 w20
def p258 := initialPool sl0 [q39] (by decide +kernel)
def p259 := initialPool sl1 [q39] (by decide +kernel)
def p260 := initialPool sl2 [q12,q39] (by decide +kernel)
def p261 := initialPool sl3 [q12,q39] (by decide +kernel)
def p262 := initialPool sl4 [q39] (by decide +kernel)
def p263 := initialPool sl16 [q39] (by decide +kernel)
def p264 := initialPool sl23 [] (by decide +kernel)
def p265 := initialPool sl29 [] (by decide +kernel)
def p266 := initialPool sl34 [] (by decide +kernel)
def q40 := choiceW 3 w3 w20
def p267 := initialPool sl0 [q40] (by decide +kernel)
def p268 := initialPool sl1 [q40] (by decide +kernel)
def p269 := initialPool sl2 [q12,q40] (by decide +kernel)
def p270 := initialPool sl3 [q12,q40] (by decide +kernel)
def p271 := initialPool sl4 [q40] (by decide +kernel)
def p272 := initialPool sl12 [q12] (by decide +kernel)
def p273 := initialPool sl2 [q12,q14] (by decide +kernel)
def q41 := choiceW 0 w3 w21
def p274 := initialPool sl0 [q13,q41] (by decide +kernel)
def p275 := initialPool sl1 [q13,q41] (by decide +kernel)
def p276 := initialPool sl2 [q41] (by decide +kernel)
def p277 := initialPool sl3 [q41] (by decide +kernel)
def p278 := initialPool sl4 [q41] (by decide +kernel)
def p279 := initialPool sl19 [] (by decide +kernel)
def q42 := choiceW 3 w3 w21
def p280 := initialPool sl0 [q13,q42] (by decide +kernel)
def p281 := initialPool sl1 [q13,q42] (by decide +kernel)
def p282 := initialPool sl2 [q42] (by decide +kernel)
def p283 := initialPool sl3 [q42] (by decide +kernel)
def p284 := initialPool sl4 [q42] (by decide +kernel)
def q43 := choiceW 3 w6 w21
def p285 := initialPool sl0 [q13,q43] (by decide +kernel)
def p286 := initialPool sl1 [q13,q43] (by decide +kernel)
def p287 := initialPool sl2 [q43] (by decide +kernel)
def p288 := initialPool sl3 [q43] (by decide +kernel)
def q44 := choiceW 1 w0 w22
def p289 := initialPool sl0 [q14,q44] (by decide +kernel)
def p290 := initialPool sl1 [q14,q44] (by decide +kernel)
def p291 := initialPool sl2 [q14,q44] (by decide +kernel)
def p292 := initialPool sl3 [q44] (by decide +kernel)
def p293 := initialPool sl4 [q44] (by decide +kernel)
def p294 := initialPool sl16 [q44] (by decide +kernel)
def q45 := choiceW 3 w0 w22
def p295 := initialPool sl0 [q14,q45] (by decide +kernel)
def p296 := initialPool sl1 [q14,q45] (by decide +kernel)
def p297 := initialPool sl2 [q14,q45] (by decide +kernel)
def p298 := initialPool sl3 [q45] (by decide +kernel)
def p299 := initialPool sl4 [q45] (by decide +kernel)
def p300 := initialPool sl16 [q45] (by decide +kernel)
def q46 := choiceW 1 w3 w22
def p301 := initialPool sl0 [q14,q46] (by decide +kernel)
def p302 := initialPool sl1 [q14,q46] (by decide +kernel)
def p303 := initialPool sl2 [q14,q46] (by decide +kernel)
def p304 := initialPool sl3 [q46] (by decide +kernel)
def p305 := initialPool sl4 [q46] (by decide +kernel)
def q47 := choiceW 3 w3 w22
def p306 := initialPool sl0 [q14,q47] (by decide +kernel)
def p307 := initialPool sl1 [q14,q47] (by decide +kernel)
def p308 := initialPool sl2 [q14,q47] (by decide +kernel)
def p309 := initialPool sl3 [q47] (by decide +kernel)
def p310 := initialPool sl4 [q47] (by decide +kernel)
def p311 := initialPool sl0 [q1,q6,q10] (by decide +kernel)
def p312 := initialPool sl1 [q1,q6,q10] (by decide +kernel)
def p313 := initialPool sl2 [q1,q6,q10] (by decide +kernel)
def p314 := initialPool sl4 [q1,q6,q10] (by decide +kernel)
def p315 := initialPool sl0 [q1,q6,q13] (by decide +kernel)
def p316 := initialPool sl1 [q1,q6,q13] (by decide +kernel)
def p317 := initialPool sl0 [q4,q6,q13] (by decide +kernel)
def p318 := initialPool sl1 [q4,q6,q13] (by decide +kernel)
def p319 := initialPool sl0 [q4,q14,q45] (by decide +kernel)
def p320 := initialPool sl1 [q4,q14,q45] (by decide +kernel)
def p321 := initialPool sl2 [q4,q14,q45] (by decide +kernel)
def p322 := initialPool sl3 [q4,q45] (by decide +kernel)
def q48 := choiceW 3 w0 w34
def p323 := initialPool sl0 [q4,q26,q48] (by decide +kernel)
def p324 := initialPool sl1 [q4,q26,q48] (by decide +kernel)
def p325 := initialPool sl2 [q4,q26,q48] (by decide +kernel)
def p326 := initialPool sl3 [q4,q48] (by decide +kernel)
def p327 := initialPool sl4 [q26,q48] (by decide +kernel)
def q49 := choiceW 3 w3 w34
def p328 := initialPool sl0 [q4,q26,q49] (by decide +kernel)
def p329 := initialPool sl1 [q4,q26,q49] (by decide +kernel)
def p330 := initialPool sl2 [q4,q26,q49] (by decide +kernel)
def p331 := initialPool sl3 [q4,q49] (by decide +kernel)
def p332 := initialPool sl4 [q26,q49] (by decide +kernel)
def p333 := initialPool sl20 [q49] (by decide +kernel)
def p334 := initialPool sl0 [q5,q6,q27] (by decide +kernel)
def p335 := initialPool sl1 [q5,q6,q27] (by decide +kernel)
def p336 := initialPool sl0 [q6,q29,q13] (by decide +kernel)
def p337 := initialPool sl1 [q6,q29,q13] (by decide +kernel)
def p338 := initialPool sl12 [q29] (by decide +kernel)
def p339 := initialPool sl16 [q6,q13] (by decide +kernel)
def p340 := initialPool sl0 [q6,q13,q31] (by decide +kernel)
def p341 := initialPool sl1 [q6,q13,q31] (by decide +kernel)
def p342 := initialPool sl6 [q13,q31] (by decide +kernel)
def p343 := initialPool sl8 [q13,q31] (by decide +kernel)
def p344 := initialPool sl12 [q31] (by decide +kernel)
def p345 := initialPool sl0 [q6,q31,q48] (by decide +kernel)
def p346 := initialPool sl1 [q6,q31,q48] (by decide +kernel)
def p347 := initialPool sl2 [q6,q31,q48] (by decide +kernel)
def p348 := initialPool sl3 [q31,q48] (by decide +kernel)
def p349 := initialPool sl4 [q6,q48] (by decide +kernel)
def p350 := initialPool sl0 [q6,q31,q49] (by decide +kernel)
def p351 := initialPool sl1 [q6,q31,q49] (by decide +kernel)
def p352 := initialPool sl2 [q6,q31,q49] (by decide +kernel)
def p353 := initialPool sl3 [q31,q49] (by decide +kernel)
def p354 := initialPool sl4 [q6,q49] (by decide +kernel)
def p355 := initialPool sl0 [q8,q10,q14] (by decide +kernel)
def p356 := initialPool sl1 [q8,q10,q14] (by decide +kernel)
def p357 := initialPool sl2 [q8,q10,q14] (by decide +kernel)
def p358 := initialPool sl0 [q8,q14,q47] (by decide +kernel)
def p359 := initialPool sl1 [q8,q14,q47] (by decide +kernel)
def p360 := initialPool sl2 [q8,q14,q47] (by decide +kernel)
def p361 := initialPool sl3 [q8,q47] (by decide +kernel)
def q50 := choiceW 3 w3 w39
def p362 := initialPool sl0 [q8,q33,q50] (by decide +kernel)
def p363 := initialPool sl1 [q8,q33,q50] (by decide +kernel)
def p364 := initialPool sl2 [q8,q33,q50] (by decide +kernel)
def p365 := initialPool sl3 [q8,q50] (by decide +kernel)
def p366 := initialPool sl4 [q33,q50] (by decide +kernel)
def p367 := initialPool sl2 [q10,q12,q14] (by decide +kernel)
def p368 := initialPool sl0 [q10,q14,q47] (by decide +kernel)
def p369 := initialPool sl1 [q10,q14,q47] (by decide +kernel)
def p370 := initialPool sl2 [q10,q14,q47] (by decide +kernel)
def p371 := initialPool sl4 [q10,q47] (by decide +kernel)
def p372 := initialPool sl0 [q10,q37,q50] (by decide +kernel)
def p373 := initialPool sl1 [q10,q37,q50] (by decide +kernel)
def p374 := initialPool sl2 [q10,q37,q50] (by decide +kernel)
def p375 := initialPool sl3 [q37,q50] (by decide +kernel)
def p376 := initialPool sl4 [q10,q50] (by decide +kernel)
def p377 := initialPool sl2 [q12,q14,q44] (by decide +kernel)
def p378 := initialPool sl3 [q12,q44] (by decide +kernel)
def p379 := initialPool sl14 [q44] (by decide +kernel)
def p380 := initialPool sl2 [q12,q14,q45] (by decide +kernel)
def p381 := initialPool sl3 [q12,q45] (by decide +kernel)
def p382 := initialPool sl14 [q45] (by decide +kernel)
def p383 := initialPool sl2 [q12,q14,q46] (by decide +kernel)
def p384 := initialPool sl3 [q12,q46] (by decide +kernel)
def p385 := initialPool sl14 [q46] (by decide +kernel)
def p386 := initialPool sl2 [q12,q14,q47] (by decide +kernel)
def p387 := initialPool sl3 [q12,q47] (by decide +kernel)
def p388 := initialPool sl14 [q47] (by decide +kernel)
def p389 := initialPool sl0 [q14,q44,q48] (by decide +kernel)
def p390 := initialPool sl1 [q14,q44,q48] (by decide +kernel)
def p391 := initialPool sl2 [q14,q44,q48] (by decide +kernel)
def p392 := initialPool sl3 [q44,q48] (by decide +kernel)
def p393 := initialPool sl4 [q44,q48] (by decide +kernel)
def p394 := initialPool sl0 [q14,q44,q49] (by decide +kernel)
def p395 := initialPool sl1 [q14,q44,q49] (by decide +kernel)
def p396 := initialPool sl2 [q14,q44,q49] (by decide +kernel)
def p397 := initialPool sl3 [q44,q49] (by decide +kernel)
def p398 := initialPool sl4 [q44,q49] (by decide +kernel)
def q51 := choiceW 1 w5 w48
def p399 := initialPool sl0 [q14,q45,q51] (by decide +kernel)
def p400 := initialPool sl1 [q14,q45,q51] (by decide +kernel)
def p401 := initialPool sl3 [q45,q51] (by decide +kernel)
def p402 := initialPool sl6 [q14,q51] (by decide +kernel)
def p403 := initialPool sl8 [q14,q51] (by decide +kernel)
def p404 := initialPool sl12 [q14] (by decide +kernel)
def p405 := initialPool sl16 [q45,q51] (by decide +kernel)
def p406 := initialPool sl17 [q51] (by decide +kernel)
def p407 := initialPool sl0 [q14,q46,q50] (by decide +kernel)
def p408 := initialPool sl1 [q14,q46,q50] (by decide +kernel)
def p409 := initialPool sl2 [q14,q46,q50] (by decide +kernel)
def p410 := initialPool sl3 [q46,q50] (by decide +kernel)
def p411 := initialPool sl4 [q46,q50] (by decide +kernel)
def p412 := initialPool sl0 [q4,q14,q45,q51] (by decide +kernel)
def p413 := initialPool sl1 [q4,q14,q45,q51] (by decide +kernel)
def p414 := initialPool sl3 [q4,q45,q51] (by decide +kernel)
def p415 := initialPool sl0 [q4,q26,q48,q49] (by decide +kernel)
def p416 := initialPool sl1 [q4,q26,q48,q49] (by decide +kernel)
def p417 := initialPool sl2 [q4,q26,q48,q49] (by decide +kernel)
def p418 := initialPool sl3 [q4,q48,q49] (by decide +kernel)
def p419 := initialPool sl4 [q26,q48,q49] (by decide +kernel)
def p420 := initialPool sl0 [q4,q26,q48,q51] (by decide +kernel)
def p421 := initialPool sl1 [q4,q26,q48,q51] (by decide +kernel)
def p422 := initialPool sl3 [q4,q48,q51] (by decide +kernel)
def p423 := initialPool sl12 [q26] (by decide +kernel)
def p424 := initialPool sl20 [q51] (by decide +kernel)
def q52 := choiceW 3 w0 w50
def p425 := initialPool sl0 [q4,q26,q49,q52] (by decide +kernel)
def p426 := initialPool sl1 [q4,q26,q49,q52] (by decide +kernel)
def p427 := initialPool sl2 [q4,q26,q49,q52] (by decide +kernel)
def p428 := initialPool sl3 [q4,q49,q52] (by decide +kernel)
def p429 := initialPool sl4 [q26,q49,q52] (by decide +kernel)
def p430 := initialPool sl0 [q6,q13,q31,q48] (by decide +kernel)
def p431 := initialPool sl1 [q6,q13,q31,q48] (by decide +kernel)
def p432 := initialPool sl0 [q6,q13,q31,q49] (by decide +kernel)
def p433 := initialPool sl1 [q6,q13,q31,q49] (by decide +kernel)
def p434 := initialPool sl12 [q31,q49] (by decide +kernel)
def p435 := initialPool sl0 [q6,q31,q48,q51] (by decide +kernel)
def p436 := initialPool sl1 [q6,q31,q48,q51] (by decide +kernel)
def p437 := initialPool sl3 [q31,q48,q51] (by decide +kernel)
def p438 := initialPool sl6 [q31,q51] (by decide +kernel)
def p439 := initialPool sl0 [q6,q31,q48,q49] (by decide +kernel)
def p440 := initialPool sl1 [q6,q31,q48,q49] (by decide +kernel)
def p441 := initialPool sl2 [q6,q31,q48,q49] (by decide +kernel)
def p442 := initialPool sl3 [q31,q48,q49] (by decide +kernel)
def p443 := initialPool sl4 [q6,q48,q49] (by decide +kernel)
def p444 := initialPool sl0 [q6,q31,q49,q52] (by decide +kernel)
def p445 := initialPool sl1 [q6,q31,q49,q52] (by decide +kernel)
def p446 := initialPool sl2 [q6,q31,q49,q52] (by decide +kernel)
def p447 := initialPool sl3 [q31,q49,q52] (by decide +kernel)
def p448 := initialPool sl4 [q6,q49,q52] (by decide +kernel)
def p449 := initialPool sl2 [q10,q12,q14,q47] (by decide +kernel)
def p450 := initialPool sl2 [q12,q14,q44,q48] (by decide +kernel)
def p451 := initialPool sl3 [q12,q44,q48] (by decide +kernel)
def p452 := initialPool sl14 [q44,q48] (by decide +kernel)
def p453 := initialPool sl2 [q12,q14,q44,q49] (by decide +kernel)
def p454 := initialPool sl3 [q12,q44,q49] (by decide +kernel)
def p455 := initialPool sl14 [q44,q49] (by decide +kernel)
def p456 := initialPool sl3 [q12,q45,q51] (by decide +kernel)
def p457 := initialPool sl12 [q12,q14] (by decide +kernel)
def p458 := initialPool sl14 [q45,q51] (by decide +kernel)
def p459 := initialPool sl2 [q12,q14,q46,q50] (by decide +kernel)
def p460 := initialPool sl3 [q12,q46,q50] (by decide +kernel)
def p461 := initialPool sl14 [q46,q50] (by decide +kernel)
def p462 := initialPool sl0 [q6,q13,q31,q48,q49] (by decide +kernel)
def p463 := initialPool sl1 [q6,q13,q31,q48,q49] (by decide +kernel)
def p464 := initialPool sl0 [q6,q13,q31,q49,q52] (by decide +kernel)
def p465 := initialPool sl1 [q6,q13,q31,q49,q52] (by decide +kernel)
def a0 : List CheckedWire := [w0,w1,w2,w3,w4,w5,w6,w7]
def a1 : List CheckedWire := [w0,w1,w2,w3,w4,w5,w6,w7,w8]
def a2 : List CheckedWire := [w0,w1,w2,w3,w4,w5,w6,w7,w9]
def a3 : List CheckedWire := [w0,w1,w2,w3,w4,w5,w6,w7,w10]
def a4 : List CheckedWire := [w0,w1,w2,w3,w4,w5,w6,w7,w11]
def a5 : List CheckedWire := [w0,w1,w2,w3,w4,w5,w6,w7,w12]
def a6 : List CheckedWire := [w0,w1,w2,w3,w4,w5,w6,w7,w13]
def a7 : List CheckedWire := [w0,w1,w2,w3,w4,w5,w6,w7,w14]
def a8 : List CheckedWire := [w0,w1,w2,w3,w4,w5,w6,w7,w15]
def a9 : List CheckedWire := [w0,w1,w2,w3,w4,w5,w6,w7,w16]
def a10 : List CheckedWire := [w0,w1,w2,w3,w4,w5,w6,w7,w17]
def a11 : List CheckedWire := [w0,w1,w2,w3,w4,w5,w6,w7,w18]
def a12 : List CheckedWire := [w0,w1,w2,w3,w4,w5,w6,w7,w19]
def a13 : List CheckedWire := [w0,w1,w2,w3,w5,w6,w7,w20]
def a14 : List CheckedWire := [w0,w1,w2,w3,w4,w6,w7,w21]
def a15 : List CheckedWire := [w0,w1,w2,w3,w4,w5,w6,w7,w22]
def a16 : List CheckedWire := [w0,w2,w3,w4,w5,w6,w7,w23]
def a17 : List CheckedWire := [w0,w1,w3,w4,w5,w6,w7,w24]
def a18 : List CheckedWire := [w0,w1,w2,w3,w5,w6,w7,w25]
def a19 : List CheckedWire := [w0,w1,w2,w3,w4,w6,w7,w26]
def a20 : List CheckedWire := [w0,w1,w2,w3,w4,w5,w7,w27]
def a21 : List CheckedWire := [w0,w1,w2,w3,w4,w5,w7,w28]
def a22 : List CheckedWire := [w0,w1,w2,w3,w4,w5,w6,w29]
def a23 : List CheckedWire := [w0,w1,w2,w3,w4,w5,w6,w7,w29]
def a24 : List CheckedWire := [w0,w1,w2,w3,w4,w5,w6,w30]
def a25 : List CheckedWire := [w1,w2,w3,w4,w5,w6,w7,w9,w14]
def a26 : List CheckedWire := [w0,w1,w2,w4,w5,w6,w7,w9,w18]
def a27 : List CheckedWire := [w0,w1,w2,w3,w4,w6,w7,w9,w21]
def a28 : List CheckedWire := [w0,w1,w2,w3,w4,w5,w6,w7,w31]
def a29 : List CheckedWire := [w1,w2,w3,w4,w5,w6,w7,w10,w14]
def a30 : List CheckedWire := [w0,w1,w2,w3,w4,w5,w6,w7,w32]
def a31 : List CheckedWire := [w0,w1,w2,w4,w5,w6,w7,w11,w18]
def a32 : List CheckedWire := [w0,w1,w2,w3,w4,w6,w7,w11,w21]
def a33 : List CheckedWire := [w0,w1,w2,w3,w4,w5,w6,w7,w33]
def a34 : List CheckedWire := [w1,w2,w3,w4,w5,w6,w7,w12,w14]
def a35 : List CheckedWire := [w0,w1,w2,w3,w4,w6,w7,w12,w21]
def a36 : List CheckedWire := [w0,w1,w2,w3,w4,w5,w7,w12,w22]
def a37 : List CheckedWire := [w0,w1,w2,w3,w4,w5,w6,w7,w34]
def a38 : List CheckedWire := [w1,w2,w3,w4,w5,w6,w7,w13,w14]
def a39 : List CheckedWire := [w0,w1,w3,w4,w5,w6,w7,w35]
def a40 : List CheckedWire := [w0,w1,w2,w3,w4,w5,w6,w7,w36]
def a41 : List CheckedWire := [w0,w1,w2,w3,w4,w5,w6,w14,w18]
def a42 : List CheckedWire := [w0,w1,w2,w3,w4,w5,w6,w7,w14,w31]
def a43 : List CheckedWire := [w0,w1,w2,w3,w4,w5,w6,w7,w37]
def a44 : List CheckedWire := [w0,w1,w2,w3,w5,w6,w7,w14,w20]
def a45 : List CheckedWire := [w0,w1,w2,w3,w4,w6,w14,w21]
def a46 : List CheckedWire := [w0,w1,w2,w3,w4,w5,w6,w7,w14,w34]
def a47 : List CheckedWire := [w0,w1,w2,w3,w4,w5,w6,w7,w38]
def a48 : List CheckedWire := [w0,w1,w2,w4,w5,w6,w7,w16,w18]
def a49 : List CheckedWire := [w0,w1,w2,w3,w4,w6,w7,w16,w21]
def a50 : List CheckedWire := [w0,w1,w2,w3,w4,w5,w7,w16,w22]
def a51 : List CheckedWire := [w0,w1,w2,w3,w4,w5,w6,w7,w39]
def a52 : List CheckedWire := [w0,w1,w2,w4,w5,w6,w7,w17,w18]
def a53 : List CheckedWire := [w0,w1,w2,w3,w4,w6,w7,w17,w21]
def a54 : List CheckedWire := [w0,w1,w2,w3,w4,w5,w6,w7,w40]
def a55 : List CheckedWire := [w0,w1,w2,w3,w4,w5,w6,w7,w18,w31]
def a56 : List CheckedWire := [w0,w1,w2,w3,w4,w5,w6,w7,w41]
def a57 : List CheckedWire := [w0,w1,w2,w3,w5,w6,w7,w18,w20]
def a58 : List CheckedWire := [w0,w1,w2,w3,w4,w5,w6,w18,w22]
def a59 : List CheckedWire := [w0,w1,w2,w3,w4,w5,w6,w7,w18,w39]
def a60 : List CheckedWire := [w0,w1,w2,w3,w4,w5,w6,w7,w42]
def a61 : List CheckedWire := [w0,w1,w2,w3,w5,w6,w7,w20,w43]
def a62 : List CheckedWire := [w0,w1,w2,w3,w5,w6,w7,w20,w44]
def a63 : List CheckedWire := [w0,w1,w2,w3,w6,w7,w20,w21]
def a64 : List CheckedWire := [w0,w1,w2,w3,w5,w7,w20,w22]
def a65 : List CheckedWire := [w0,w1,w2,w3,w4,w6,w7,w21,w45]
def a66 : List CheckedWire := [w0,w1,w2,w3,w4,w6,w7,w21,w46]
def a67 : List CheckedWire := [w0,w1,w2,w3,w4,w6,w7,w21,w47]
def a68 : List CheckedWire := [w0,w1,w2,w3,w4,w5,w6,w7,w22,w34]
def a69 : List CheckedWire := [w0,w1,w2,w3,w4,w5,w6,w7,w48]
def a70 : List CheckedWire := [w0,w1,w2,w3,w4,w5,w6,w7,w22,w48]
def a71 : List CheckedWire := [w0,w1,w2,w3,w4,w5,w6,w7,w22,w39]
def a72 : List CheckedWire := [w0,w1,w2,w3,w4,w5,w6,w7,w49]
def a73 : List CheckedWire := [w0,w1,w2,w3,w4,w5,w6,w7,w22,w49]
def a74 : List CheckedWire := [w1,w2,w4,w5,w6,w9,w14,w18]
def a75 : List CheckedWire := [w1,w2,w3,w4,w6,w9,w14,w21]
def a76 : List CheckedWire := [w1,w2,w3,w4,w6,w12,w14,w21]
def a77 : List CheckedWire := [w1,w2,w3,w4,w5,w7,w12,w22,w48]
def a78 : List CheckedWire := [w1,w2,w3,w4,w5,w6,w7,w34,w48]
def a79 : List CheckedWire := [w0,w1,w2,w4,w5,w6,w7,w50]
def a80 : List CheckedWire := [w0,w1,w2,w4,w5,w6,w7,w34,w50]
def a81 : List CheckedWire := [w1,w3,w4,w5,w6,w7,w14,w35]
def a82 : List CheckedWire := [w0,w1,w2,w3,w4,w6,w14,w21,w31]
def a83 : List CheckedWire := [w0,w1,w2,w3,w6,w14,w20,w21]
def a84 : List CheckedWire := [w0,w1,w2,w3,w4,w6,w14,w21,w34]
def a85 : List CheckedWire := [w1,w2,w3,w4,w5,w6,w7,w14,w48]
def a86 : List CheckedWire := [w1,w2,w3,w4,w5,w6,w7,w14,w34,w48]
def a87 : List CheckedWire := [w0,w1,w2,w4,w5,w6,w7,w14,w50]
def a88 : List CheckedWire := [w0,w1,w2,w4,w5,w6,w7,w14,w34,w50]
def a89 : List CheckedWire := [w0,w1,w2,w4,w5,w16,w18,w22]
def a90 : List CheckedWire := [w0,w1,w2,w4,w5,w7,w16,w22,w49]
def a91 : List CheckedWire := [w0,w1,w2,w4,w5,w6,w7,w39,w49]
def a92 : List CheckedWire := [w0,w1,w2,w3,w5,w18,w20,w22]
def a93 : List CheckedWire := [w0,w1,w2,w4,w5,w6,w18,w22,w49]
def a94 : List CheckedWire := [w0,w1,w2,w4,w5,w6,w7,w18,w49]
def a95 : List CheckedWire := [w0,w1,w2,w4,w5,w6,w7,w18,w39,w49]
def a96 : List CheckedWire := [w0,w1,w2,w3,w5,w7,w20,w22,w34]
def a97 : List CheckedWire := [w0,w1,w2,w3,w5,w7,w20,w22,w48]
def a98 : List CheckedWire := [w0,w1,w2,w3,w5,w7,w20,w22,w39]
def a99 : List CheckedWire := [w0,w1,w2,w3,w5,w7,w20,w22,w49]
def a100 : List CheckedWire := [w1,w2,w3,w4,w5,w6,w7,w22,w34,w48]
def a101 : List CheckedWire := [w0,w1,w2,w4,w5,w6,w7,w22,w50]
def a102 : List CheckedWire := [w0,w1,w2,w4,w5,w6,w7,w22,w34,w50]
def a103 : List CheckedWire := [w0,w1,w2,w3,w4,w6,w7,w51]
def a104 : List CheckedWire := [w0,w1,w2,w3,w4,w6,w7,w48,w51]
def a105 : List CheckedWire := [w0,w1,w2,w3,w4,w6,w7,w22,w51]
def a106 : List CheckedWire := [w0,w1,w2,w3,w4,w6,w7,w22,w48,w51]
def a107 : List CheckedWire := [w0,w1,w2,w4,w5,w6,w7,w22,w39,w49]
def a108 : List CheckedWire := [w1,w2,w3,w4,w7,w12,w22,w48,w51]
def a109 : List CheckedWire := [w1,w2,w4,w5,w6,w7,w34,w48,w50]
def a110 : List CheckedWire := [w1,w2,w3,w4,w6,w7,w34,w48,w51]
def a111 : List CheckedWire := [w1,w2,w4,w5,w6,w7,w34,w50,w52]
def a112 : List CheckedWire := [w1,w2,w3,w4,w6,w14,w21,w48]
def a113 : List CheckedWire := [w1,w2,w3,w4,w6,w14,w21,w34,w48]
def a114 : List CheckedWire := [w0,w1,w2,w4,w6,w14,w21,w50]
def a115 : List CheckedWire := [w0,w1,w2,w4,w6,w14,w21,w34,w50]
def a116 : List CheckedWire := [w1,w2,w3,w4,w6,w7,w14,w48,w51]
def a117 : List CheckedWire := [w1,w2,w4,w5,w6,w7,w14,w48,w50]
def a118 : List CheckedWire := [w1,w2,w4,w5,w6,w7,w14,w50,w52]
def a119 : List CheckedWire := [w0,w1,w2,w5,w18,w20,w22,w49]
def a120 : List CheckedWire := [w1,w2,w3,w5,w7,w20,w22,w34,w48]
def a121 : List CheckedWire := [w0,w1,w2,w5,w7,w20,w22,w50]
def a122 : List CheckedWire := [w0,w1,w2,w5,w7,w20,w22,w34,w50]
def a123 : List CheckedWire := [w0,w1,w2,w3,w7,w20,w22,w51]
def a124 : List CheckedWire := [w0,w1,w2,w3,w7,w20,w22,w48,w51]
def a125 : List CheckedWire := [w0,w1,w2,w5,w7,w20,w22,w39,w49]
def a126 : List CheckedWire := [w1,w2,w4,w6,w14,w21,w48,w50]
def a127 : List CheckedWire := [w1,w2,w4,w6,w14,w21,w50,w52]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x127 : Done 7 a127 := certify a127 [p464,p465,p446,p447,p448,p342,p194,p434,p116,p333] [] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x126 : Done 7 a126 := certify a126 [p462,p463,p441,p442,p443,p342,p194,p434,p116,p333] [] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x125 : Done 8 a125 := certify a125 [p407,p408,p459,p460,p411,p149,p461,p14,p15] [] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x124 : Done 8 a124 := certify a124 [p399,p400,p380,p456,p299,p402,p457,p458,p406] [] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x123 : Done 8 a123 := certify a123 [p399,p400,p380,p456,p299,p402,p403,p457,p458,p405,p406] [] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x122 : Done 8 a122 := certify a122 [p394,p395,p453,p454,p398,p149,p455,p294,p15] [] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x121 : Done 8 a121 := certify a121 [p394,p395,p453,p454,p398,p149,p455,p294,p15] [] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x120 : Done 8 a120 := certify a120 [p389,p390,p450,p451,p393,p149,p452,p15] [] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x119 : Done 8 a119 := certify a119 [p368,p369,p449,p387,p371,p149,p388,p14,p15,p242] [] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x118 : Done 8 a118 := certify a118 [p444,p445,p446,p447,p448,p192,p15,p333] [⟨a127,x127⟩] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x117 : Done 8 a117 := certify a117 [p439,p440,p441,p442,p443,p192,p15,p333] [⟨a126,x126⟩] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x116 : Done 8 a116 := certify a116 [p435,p436,p347,p437,p349,p438,p344,p406,p424] [] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x115 : Done 8 a115 := certify a115 [p432,p433,p352,p353,p354,p342,p194,p434,p116,p333] [⟨a126,x126⟩] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x114 : Done 8 a114 := certify a114 [p432,p433,p352,p353,p354,p342,p194,p434,p116,p333] [⟨a127,x127⟩] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x113 : Done 8 a113 := certify a113 [p430,p431,p347,p348,p349,p342,p194,p344,p116,p43] [⟨a126,x126⟩] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x112 : Done 8 a112 := certify a112 [p430,p431,p347,p348,p349,p342,p194,p344,p116,p43] [] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x111 : Done 8 a111 := certify a111 [p425,p426,p427,p428,p429,p156,p15,p333] [] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x110 : Done 8 a110 := certify a110 [p420,p421,p325,p422,p327,p423,p406,p424] [] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x109 : Done 8 a109 := certify a109 [p415,p416,p417,p418,p419,p156,p15,p333] [] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x108 : Done 8 a108 := certify a108 [p412,p413,p321,p414,p299,p402,p404,p406,p145] [] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x107 : Done 9 a107 := certify a107 [p407,p408,p409,p410,p411,p149,p14,p15,p60] [⟨a125,x125⟩] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x106 : Done 9 a106 := certify a106 [p399,p400,p297,p401,p299,p402,p404,p406] [⟨a108,x108⟩,⟨a110,x110⟩,⟨a124,x124⟩] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x105 : Done 9 a105 := certify a105 [p399,p400,p297,p401,p299,p402,p403,p151,p404,p405,p406] [⟨a123,x123⟩] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x104 : Done 9 a104 := certify a104 [p399,p400,p297,p401,p299,p402,p403,p151,p404,p405,p406] [⟨a110,x110⟩] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x103 : Done 9 a103 := certify a103 [p399,p400,p297,p401,p299,p402,p403,p151,p404,p405,p406] [] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x102 : Done 9 a102 := certify a102 [p394,p395,p396,p397,p398,p149,p294,p15,p333] [⟨a109,x109⟩,⟨a122,x122⟩] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x101 : Done 9 a101 := certify a101 [p394,p395,p396,p397,p398,p149,p151,p294,p15,p333] [⟨a121,x121⟩] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x100 : Done 9 a100 := certify a100 [p389,p390,p391,p392,p393,p149,p15,p43] [⟨a120,x120⟩] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x99 : Done 9 a99 := certify a99 [p306,p307,p386,p387,p310,p149,p388,p14,p15] [⟨a119,x119⟩,⟨a125,x125⟩] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x98 : Done 9 a98 := certify a98 [p301,p302,p383,p384,p305,p149,p385,p14,p15] [⟨a125,x125⟩] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x97 : Done 9 a97 := certify a97 [p295,p296,p380,p381,p299,p149,p150,p382,p300,p15] [⟨a120,x120⟩,⟨a123,x123⟩,⟨a124,x124⟩] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x96 : Done 9 a96 := certify a96 [p289,p290,p377,p378,p293,p149,p150,p379,p294,p15] [⟨a120,x120⟩,⟨a121,x121⟩,⟨a122,x122⟩] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x95 : Done 9 a95 := certify a95 [p372,p373,p374,p375,p376,p250,p14,p15,p60] [] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x94 : Done 9 a94 := certify a94 [p372,p373,p374,p375,p376,p250,p251,p14,p15,p60] [] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x93 : Done 9 a93 := certify a93 [p368,p369,p370,p309,p371,p149,p151,p14,p15,p60] [⟨a119,x119⟩] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x92 : Done 9 a92 := certify a92 [p243,p244,p367,p66,p59,p149,p67,p14,p15,p242] [⟨a119,x119⟩] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x91 : Done 9 a91 := certify a91 [p362,p363,p364,p365,p366,p216,p217,p14,p15,p60] [] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x90 : Done 9 a90 := certify a90 [p358,p359,p360,p361,p310,p149,p151,p14,p15] [] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x89 : Done 9 a89 := certify a89 [p355,p356,p357,p51,p59,p149,p151,p14,p15,p60] [] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x88 : Done 9 a88 := certify a88 [p350,p351,p352,p353,p354,p192,p106,p15,p333] [⟨a117,x117⟩,⟨a115,x115⟩] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x87 : Done 9 a87 := certify a87 [p350,p351,p352,p353,p354,p192,p194,p106,p15,p333] [⟨a118,x118⟩,⟨a114,x114⟩] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x86 : Done 9 a86 := certify a86 [p345,p346,p347,p348,p349,p192,p15,p43] [⟨a117,x117⟩,⟨a113,x113⟩] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x85 : Done 9 a85 := certify a85 [p345,p346,p347,p348,p349,p192,p194,p15,p43] [⟨a112,x112⟩,⟨a116,x116⟩] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x84 : Done 9 a84 := certify a84 [p340,p341,p190,p191,p42,p342,p343,p194,p344,p339,p116,p43] [⟨a112,x112⟩,⟨a113,x113⟩,⟨a114,x114⟩,⟨a115,x115⟩] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x83 : Done 9 a83 := certify a83 [p186,p187,p184,p66,p42,p113,p114,p272,p67,p339,p116,p185] [] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x82 : Done 9 a82 := certify a82 [p336,p337,p176,p177,p178,p113,p12,p338,p116,p43,p60] [] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x81 : Done 9 a81 := certify a81 [p334,p335,p162,p165,p42,p10,p12,p13,p43] [] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x80 : Done 9 a80 := certify a80 [p328,p329,p330,p331,p332,p156,p158,p159,p15,p333] [⟨a109,x109⟩,⟨a111,x111⟩] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x79 : Done 9 a79 := certify a79 [p328,p329,p330,p331,p332,p156,p158,p159,p15,p333] [] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x78 : Done 9 a78 := certify a78 [p323,p324,p325,p326,p327,p156,p158,p15,p43] [⟨a109,x109⟩,⟨a110,x110⟩] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x77 : Done 9 a77 := certify a77 [p319,p320,p321,p322,p299,p149,p151,p15] [⟨a108,x108⟩] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x76 : Done 9 a76 := certify a76 [p317,p318,p142,p34,p42,p113,p12,p13,p116,p43,p145] [] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x75 : Done 9 a75 := certify a75 [p315,p316,p104,p19,p105,p113,p114,p12,p13,p116,p43] [] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x74 : Done 9 a74 := certify a74 [p311,p312,p313,p19,p314,p10,p12,p106,p15,p43,p60] [] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x73 : Done 10 a73 := certify a73 [p306,p307,p308,p309,p310,p149,p151,p14,p15] [⟨a90,x90⟩,⟨a93,x93⟩,⟨a91,x91⟩,⟨a107,x107⟩,⟨a99,x99⟩] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x72 : Done 10 a72 := certify a72 [p306,p307,p308,p309,p310,p149,p151,p14,p15] [⟨a91,x91⟩] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x71 : Done 10 a71 := certify a71 [p301,p302,p303,p304,p305,p149,p151,p14,p15,p60] [⟨a91,x91⟩,⟨a107,x107⟩,⟨a98,x98⟩] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x70 : Done 10 a70 := certify a70 [p295,p296,p297,p298,p299,p149,p150,p151,p300,p15] [⟨a77,x77⟩,⟨a78,x78⟩,⟨a100,x100⟩,⟨a97,x97⟩,⟨a105,x105⟩,⟨a106,x106⟩] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x69 : Done 10 a69 := certify a69 [p295,p296,p297,p298,p299,p149,p150,p151,p300,p15] [⟨a78,x78⟩,⟨a103,x103⟩,⟨a104,x104⟩] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x68 : Done 10 a68 := certify a68 [p289,p290,p291,p292,p293,p149,p150,p151,p294,p15,p43] [⟨a78,x78⟩,⟨a100,x100⟩,⟨a101,x101⟩,⟨a102,x102⟩,⟨a96,x96⟩] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x67 : Done 10 a67 := certify a67 [p285,p286,p287,p288,p4,p13,p115,p116,p279,p145,p224,p208] [] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x66 : Done 10 a66 := certify a66 [p280,p281,p282,p283,p284,p113,p12,p13,p115,p116,p279,p224,p208] [] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x65 : Done 10 a65 := certify a65 [p274,p275,p276,p277,p278,p113,p12,p13,p115,p116,p279] [] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x64 : Done 10 a64 := certify a64 [p70,p71,p273,p66,p4,p67,p14,p15] [⟨a96,x96⟩,⟨a97,x97⟩,⟨a92,x92⟩,⟨a98,x98⟩,⟨a99,x99⟩] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x63 : Done 10 a63 := certify a63 [p68,p69,p65,p66,p4,p272,p67,p115,p116,p208] [⟨a83,x83⟩] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x62 : Done 10 a62 := certify a62 [p267,p268,p269,p270,p271,p10,p67,p14,p15,p264,p265] [] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x61 : Done 10 a61 := certify a61 [p258,p259,p260,p261,p262,p10,p11,p67,p263,p15,p264,p265,p266] [] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x60 : Done 10 a60 := certify a60 [p252,p253,p254,p255,p59,p256,p257,p14,p15,p60] [] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x59 : Done 10 a59 := certify a59 [p246,p247,p248,p249,p59,p250,p251,p14,p15,p60] [⟨a94,x94⟩,⟨a95,x95⟩] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x58 : Done 10 a58 := certify a58 [p243,p244,p245,p3,p59,p149,p151,p14,p15,p60] [⟨a89,x89⟩,⟨a93,x93⟩,⟨a92,x92⟩] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x57 : Done 10 a57 := certify a57 [p56,p57,p241,p66,p59,p10,p67,p14,p15,p242] [⟨a92,x92⟩] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x56 : Done 10 a56 := certify a56 [p235,p236,p237,p238,p239,p10,p12,p240,p15,p60] [] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x55 : Done 10 a55 := certify a55 [p229,p230,p231,p232,p233,p10,p12,p234,p15,p43,p60] [] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x54 : Done 10 a54 := certify a54 [p225,p226,p227,p55,p228,p10,p12,p14,p15,p60] [] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x53 : Done 10 a53 := certify a53 [p221,p222,p54,p55,p4,p113,p12,p223,p115,p116,p224] [] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x52 : Done 10 a52 := certify a52 [p218,p219,p220,p55,p59,p10,p12,p14,p15,p60] [] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x51 : Done 10 a51 := certify a51 [p212,p213,p214,p51,p215,p216,p217,p14,p15,p60] [⟨a91,x91⟩] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x50 : Done 10 a50 := certify a50 [p209,p210,p211,p51,p4,p149,p151,p14,p15] [⟨a89,x89⟩,⟨a90,x90⟩] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x49 : Done 10 a49 := certify a49 [p205,p206,p50,p51,p4,p113,p12,p207,p115,p116,p208] [] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x48 : Done 10 a48 := certify a48 [p202,p203,p204,p51,p59,p10,p12,p14,p15,p60] [⟨a89,x89⟩] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x47 : Done 10 a47 := certify a47 [p195,p196,p197,p198,p42,p199,p200,p201,p106,p15,p43] [] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x46 : Done 10 a46 := certify a46 [p188,p189,p190,p191,p42,p192,p193,p194,p106,p15,p43] [⟨a85,x85⟩,⟨a86,x86⟩,⟨a87,x87⟩,⟨a88,x88⟩,⟨a84,x84⟩] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x45 : Done 10 a45 := certify a45 [p186,p187,p41,p3,p42,p113,p114,p12,p13,p116,p43] [⟨a75,x75⟩,⟨a76,x76⟩,⟨a82,x82⟩,⟨a83,x83⟩,⟨a84,x84⟩] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x44 : Done 10 a44 := certify a44 [p39,p40,p184,p66,p42,p10,p11,p67,p106,p15,p185] [⟨a83,x83⟩] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x43 : Done 10 a43 := certify a43 [p179,p180,p181,p182,p183,p10,p12,p106,p15,p43] [] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x42 : Done 10 a42 := certify a42 [p174,p175,p176,p177,p178,p10,p12,p106,p15,p43,p60] [⟨a82,x82⟩] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x41 : Done 10 a41 := certify a41 [p170,p171,p172,p3,p173,p10,p12,p106,p15,p43,p60] [⟨a74,x74⟩] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x40 : Done 10 a40 := certify a40 [p166,p167,p168,p38,p169,p10,p11,p12,p13,p15,p43] [] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x39 : Done 10 a39 := certify a39 [p163,p164,p37,p165,p4,p10,p11,p12,p13] [⟨a81,x81⟩] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x38 : Done 10 a38 := certify a38 [p160,p161,p162,p38,p42,p10,p11,p12,p13,p15,p43] [⟨a81,x81⟩] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x37 : Done 10 a37 := certify a37 [p152,p153,p154,p34,p155,p156,p157,p158,p159,p15,p43] [⟨a78,x78⟩,⟨a79,x79⟩,⟨a80,x80⟩] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x36 : Done 10 a36 := certify a36 [p146,p147,p148,p34,p4,p149,p150,p151,p14,p15] [⟨a77,x77⟩] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x35 : Done 10 a35 := certify a35 [p143,p144,p33,p34,p4,p113,p114,p12,p13,p115,p116,p145] [⟨a76,x76⟩] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x34 : Done 10 a34 := certify a34 [p140,p141,p142,p34,p42,p10,p12,p15,p43] [⟨a76,x76⟩] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x33 : Done 10 a33 := certify a33 [p136,p137,p138,p29,p139,p10,p12,p14,p15,p60] [] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x32 : Done 10 a32 := certify a32 [p134,p135,p28,p29,p30,p113,p114,p12,p13,p115,p116] [] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x31 : Done 10 a31 := certify a31 [p130,p131,p132,p29,p133,p10,p12,p14,p15,p43,p60] [] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x30 : Done 10 a30 := certify a30 [p126,p127,p128,p24,p129,p10,p11,p12,p13,p15,p43] [] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x29 : Done 10 a29 := certify a29 [p122,p123,p124,p24,p125,p10,p12,p13,p15,p43,p60] [] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x28 : Done 10 a28 := certify a28 [p117,p118,p119,p19,p120,p10,p12,p121,p15,p43,p60] [] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x27 : Done 10 a27 := certify a27 [p111,p112,p18,p19,p20,p113,p114,p12,p13,p115,p116] [⟨a75,x75⟩] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x26 : Done 10 a26 := certify a26 [p107,p108,p109,p19,p110,p10,p12,p14,p15,p60] [⟨a74,x74⟩] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x25 : Done 10 a25 := certify a25 [p102,p103,p104,p19,p105,p10,p11,p12,p106,p15,p43] [⟨a74,x74⟩,⟨a75,x75⟩] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x24 : Done 10 a24 := certify a24 [p98,p99,p100,p8,p101,p10,p11,p12,p13,p14,p15] [] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x23 : Done 10 a23 := certify a23 [p94,p95,p96,p8,p97,p10,p11,p12,p13,p14,p15,p43] [] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x22 : Done 10 a22 := certify a22 [p94,p95,p96,p8,p97,p10,p11,p12,p13,p14,p15,p43] [] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x21 : Done 10 a21 := certify a21 [p90,p91,p92,p93,p9,p10,p11,p12,p13,p14,p15] [] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x20 : Done 10 a20 := certify a20 [p86,p87,p88,p89,p9,p10,p11,p12,p13,p14,p15] [] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x19 : Done 10 a19 := certify a19 [p83,p84,p7,p85,p9,p10,p11,p12,p13,p14,p15] [] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x18 : Done 10 a18 := certify a18 [p5,p6,p80,p81,p82,p10,p11,p12,p13,p14,p15] [] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x17 : Done 10 a17 := certify a17 [p77,p78,p7,p79,p9,p10,p11,p12,p13,p14,p15] [] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x16 : Done 10 a16 := certify a16 [p73,p6,p74,p75,p76,p10,p11,p12,p13,p14,p15] [] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x15 : Done 11 a15 := certify a15 [p70,p71,p72,p3,p4,p14,p15] [⟨a36,x36⟩,⟨a37,x37⟩,⟨a68,x68⟩,⟨a69,x69⟩,⟨a70,x70⟩,⟨a50,x50⟩,⟨a58,x58⟩,⟨a51,x51⟩,⟨a71,x71⟩,⟨a72,x72⟩,⟨a73,x73⟩,⟨a64,x64⟩] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x14 : Done 11 a14 := certify a14 [p68,p69,p2,p3,p4,p13] [⟨a27,x27⟩,⟨a32,x32⟩,⟨a35,x35⟩,⟨a45,x45⟩,⟨a49,x49⟩,⟨a53,x53⟩,⟨a65,x65⟩,⟨a66,x66⟩,⟨a63,x63⟩,⟨a67,x67⟩] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x13 : Done 11 a13 := certify a13 [p0,p1,p65,p66,p4,p67,p14,p15] [⟨a44,x44⟩,⟨a61,x61⟩,⟨a57,x57⟩,⟨a62,x62⟩,⟨a63,x63⟩,⟨a64,x64⟩] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x12 : Done 11 a12 := certify a12 [p61,p62,p63,p3,p64,p10,p12,p14,p15] [] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x11 : Done 11 a11 := certify a11 [p56,p57,p58,p3,p59,p10,p12,p14,p15,p60] [⟨a26,x26⟩,⟨a31,x31⟩,⟨a41,x41⟩,⟨a28,x28⟩,⟨a55,x55⟩,⟨a56,x56⟩,⟨a48,x48⟩,⟨a52,x52⟩,⟨a57,x57⟩,⟨a58,x58⟩,⟨a51,x51⟩,⟨a59,x59⟩,⟨a60,x60⟩] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x10 : Done 11 a10 := certify a10 [p52,p53,p54,p55,p4,p10,p12,p14,p15] [⟨a52,x52⟩,⟨a53,x53⟩,⟨a54,x54⟩] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x9 : Done 11 a9 := certify a9 [p48,p49,p50,p51,p4,p10,p12,p14,p15] [⟨a48,x48⟩,⟨a49,x49⟩,⟨a50,x50⟩,⟨a51,x51⟩] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x8 : Done 11 a8 := certify a8 [p44,p45,p46,p3,p47,p10,p11,p12,p13,p15] [] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x7 : Done 11 a7 := certify a7 [p39,p40,p41,p3,p42,p10,p11,p12,p15,p43] [⟨a25,x25⟩,⟨a29,x29⟩,⟨a34,x34⟩,⟨a38,x38⟩,⟨a41,x41⟩,⟨a28,x28⟩,⟨a42,x42⟩,⟨a43,x43⟩,⟨a44,x44⟩,⟨a45,x45⟩,⟨a37,x37⟩,⟨a46,x46⟩,⟨a47,x47⟩] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x6 : Done 11 a6 := certify a6 [p35,p36,p37,p38,p4,p10,p11,p12,p13,p15] [⟨a38,x38⟩,⟨a39,x39⟩,⟨a40,x40⟩] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x5 : Done 11 a5 := certify a5 [p31,p32,p33,p34,p4,p10,p11,p12,p14,p15] [⟨a34,x34⟩,⟨a35,x35⟩,⟨a36,x36⟩,⟨a37,x37⟩] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x4 : Done 11 a4 := certify a4 [p26,p27,p28,p29,p30,p10,p11,p12,p14,p15] [⟨a31,x31⟩,⟨a32,x32⟩,⟨a33,x33⟩] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x3 : Done 11 a3 := certify a3 [p21,p22,p23,p24,p25,p10,p11,p12,p13,p14,p15] [⟨a29,x29⟩,⟨a30,x30⟩] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x2 : Done 11 a2 := certify a2 [p16,p17,p18,p19,p20,p10,p11,p12,p14,p15] [⟨a25,x25⟩,⟨a26,x26⟩,⟨a27,x27⟩,⟨a28,x28⟩] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x1 : Done 11 a1 := certify a1 [p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15] [⟨a16,x16⟩,⟨a17,x17⟩,⟨a18,x18⟩,⟨a19,x19⟩,⟨a20,x20⟩,⟨a21,x21⟩,⟨a22,x22⟩,⟨a23,x23⟩,⟨a24,x24⟩] (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x0 : Done 12 a0 := certify a0 [p0,p1,p2,p3,p4] [⟨a1,x1⟩,⟨a2,x2⟩,⟨a3,x3⟩,⟨a4,x4⟩,⟨a5,x5⟩,⟨a6,x6⟩,⟨a7,x7⟩,⟨a8,x8⟩,⟨a9,x9⟩,⟨a10,x10⟩,⟨a11,x11⟩,⟨a12,x12⟩,⟨a13,x13⟩,⟨a14,x14⟩,⟨a15,x15⟩] (by decide +kernel) (by decide +kernel) (by decide +kernel)
def f (x : Fin 8 → Bool) : Bool := (x 0 && x 3) || (x 1 && x 4) || (x 0 && x 5) || (x 2 && x 5) || (x 1 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 2 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 6 && x 7)
def monoWitness : List Gate := [⟨.and, [0, 3]⟩,    ⟨.or, [0, 2]⟩,    ⟨.or, [5, 7]⟩,    ⟨.and, [9, 10]⟩,    ⟨.or, [4, 6]⟩,    ⟨.or, [1, 7]⟩,    ⟨.and, [12, 13]⟩,    ⟨.or, [1, 2]⟩,    ⟨.or, [15, 3]⟩,    ⟨.or, [6, 7]⟩,    ⟨.and, [16, 17]⟩,    ⟨.or, [8, 11]⟩,    ⟨.or, [19, 14]⟩,    ⟨.or, [20, 18]⟩]
theorem witnessFits : ∀ g ∈ monoWitness, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by simp [monoWitness]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem witnessCorrect : ∀ x : Fin 8 → Bool, Circuit.eval ⟨monoWitness,21⟩ (List.ofFn x) = f x := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem graphCorrect : ∀ x : Fin 8 → Bool, f x = decide (∃ i < ([0, 3, 1, 4, 0, 5, 2, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by decide +kernel

def graphSample (r : Row) (i : Fin 8) : Bool := bit r (rawEight.getD i.val zero)
set_option maxRecDepth 12000 in
theorem inputList : List.ofFn (fun i : Fin 8 => rawEight.getD i.val zero) = rawEight := rfl
set_option maxRecDepth 12000 in
theorem graphSampled (r : Row) : List.ofFn (graphSample r) = rawEight.map (bit r) := by
  rw [←inputList,List.map_ofFn]
  rfl
theorem graphEval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates rawEight).getD i zero) =
      (C.wires (List.ofFn (graphSample r))).getD i false := by
  rw [←b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),graphSampled]
  rfl
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem graphTable : ∀ r : Row, bit r goalEight = f (graphSample r) := by decide +kernel
theorem graphProper : proper goalEight := by unfold proper; decide +kernel
def graphWitnesses : List (Sig × Row × Row) := [(rawEight.getD 0 zero,8,9), (rawEight.getD 1 zero,16,18), (rawEight.getD 2 zero,32,36), (rawEight.getD 3 zero,1,9), (rawEight.getD 4 zero,2,18), (rawEight.getD 5 zero,1,33), (rawEight.getD 6 zero,2,66), (rawEight.getD 7 zero,1,129)]

theorem allEssential : ∀ v ∈ rawEight, Essential goalEight rawEight v := by
  have h := essential_ok (T := goalEight) (raw := rawEight) (xs := graphWitnesses) (by decide +kernel)
  intro v hv
  exact h v (List.mem_toFinset.mpr hv)
theorem physicalNew (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = f x) :
    ∃ k, k ≤ C.gates.countP (fun g => !isNot g) ∧ Live true goalEight k rawEight.toFinset := by
  have goalEq : (execute C.gates rawEight).getD C.output zero = goalEight := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (graphEval C legal C.output r).trans ((computes (graphSample r)).trans (graphTable r).symm)
  have out := get_rep (u:=true) (execute C.gates rawEight) C.output
  rw [goalEq] at out
  unfold PEqualNP.Outside.L_meta_30332.P11311.Repr at out
  have pg : bit 0 goalEight = false := by decide +kernel
  rw [nrm_id pg] at out
  obtain ⟨k,S,hk,run,sub⟩ := extract (u:=true) C.gates rawEight legal (by simp) graphProper
    (out.resolve_right (fun h => h graphProper))
  have plain : rawEight.all plainWord = true := by decide +kernel
  rw [nrm_map plain] at sub
  have eq : rawEight.toFinset = S := by
    ext a
    rw [List.mem_toFinset]
    refine ⟨fun ha => ?_,sub _⟩
    obtain ⟨r,s,hd,iso⟩ := allEssential a ha
    exact raw_required run rawEight a sub r s hd iso
  exact ⟨k,hk,eq.symm ▸ run⟩

end PEqualNP.Outside.L_meta_30332

open PEqualNP.Outside.L_meta_30332 PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_30332.P11311 in
theorem PEqualNP.Outside.L_meta_30332 : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 2, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 2, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) := by
  intro gs o hg _ he
  by_cases large : 14 ≤ gs.length
  · exact ⟨monoWitness, 21, witnessFits, large, fun x => (witnessCorrect x).trans (graphCorrect x)⟩
  · by_cases hn : ∃ g ∈ gs, g.op = GateOp.not
    · obtain ⟨g, hmem, hop⟩ := hn
      have fewer : gs.countP (fun q => !isNot q) < gs.length := by
        by_contra! ge
        have eq := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length ge) g hmem
        simp [isNot,hop] at eq
      have legal : PEqualNP.MetaComplexity.FanInTwo (Circuit.mk gs o) := by
        intro q hq
        simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using hg q hq
      obtain ⟨k, hk, run⟩ := physicalNew ⟨gs,o⟩ legal (fun x => (he x).trans (graphCorrect x).symm)
      change k ≤ gs.countP (fun q => !isNot q) at hk
      exact False.elim (x0 k (by omega) (by exact run))
    · refine ⟨gs,o,?_,le_rfl,he⟩
      intro g h
      obtain ⟨op, arity⟩ := hg g h
      exact ⟨op.elim Or.inl (fun t => t.elim Or.inr (fun n => (hn ⟨g,h,n⟩).elim)), arity⟩

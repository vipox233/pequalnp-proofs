import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_31725.Frame
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def edges : List ℕ := [0, 4, 1, 4, 2, 5, 3, 5, 0, 6, 2, 6, 4, 6, 5, 6, 0, 7, 3, 7, 4, 7, 5, 7, 6, 7]
def target (x : Fin 8 → Bool) := decide (∃ i < edges.length / 2,
  (List.ofFn x).getD (edges.getD (2*i) 0) false = true ∧
  (List.ofFn x).getD (edges.getD (2*i+1) 0) false = true)

def witness : List Gate := [
  ⟨.or, [0, 4]⟩,
  ⟨.or, [0, 1]⟩,
  ⟨.or, [5, 6]⟩,
  ⟨.or, [3, 6]⟩,
  ⟨.and, [4, 9]⟩,
  ⟨.or, [5, 8]⟩,
  ⟨.and, [11, 13]⟩,
  ⟨.or, [2, 14]⟩,
  ⟨.and, [10, 15]⟩,
  ⟨.or, [11, 13]⟩,
  ⟨.or, [12, 16]⟩,
  ⟨.and, [7, 17]⟩,
  ⟨.or, [18, 19]⟩]

theorem good : ∀ g ∈ witness, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  simp [witness]

theorem correct : ∀ x : Fin 8 → Bool, Circuit.eval ⟨witness,20⟩ (List.ofFn x) = target x := by
  decide +kernel

theorem finish (lower : ∀ (gs : List Gate) (o : ℕ), FanInTwo ⟨gs,o⟩ →
    (∀ x : Fin 8 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = target x) →
    (∃ g ∈ gs, g.op = .not) → 13 ≤ gs.length) : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 2, 5, 3, 5, 0, 6, 2, 6, 4, 6, 5, 6, 0, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 2, 5, 3, 5, 0, 6, 2, 6, 4, 6, 5, 6, 0, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 2, 5, 3, 5, 0, 6, 2, 6, 4, 6, 5, 6, 0, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 2, 5, 3, 5, 0, 6, 2, 6, 4, 6, 5, 6, 0, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 2, 5, 3, 5, 0, 6, 2, 6, 4, 6, 5, 6, 0, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 2, 5, 3, 5, 0, 6, 2, 6, 4, 6, 5, 6, 0, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) := by
  intro gs o fan _ computes
  by_cases hn : ∃ g ∈ gs, g.op = .not
  · exact ⟨witness, 20, good, lower gs o fan computes hn, correct⟩
  · refine ⟨gs, o, ?_, le_rfl, computes⟩
    intro g hg
    obtain ⟨op, len⟩ := fan g hg
    exact ⟨op.imp_right (fun h => h.resolve_right (fun e => hn ⟨g,hg,e⟩)),len⟩

end PEqualNP.Outside.L_meta_31725.Frame

namespace PEqualNP.Outside.L_meta_31725.Reduce
variable {m : Nat}
def canon (w : BitVec (m+1)) := if w.getLsbD 0 then ~~~w else w
def signed (d : Bool) (w : BitVec (m+1)) := if d then ~~~w else w
def gate (s t : Bool) (a b : BitVec (m+1)) := canon (signed s a &&& signed t b)
def Path (goal : BitVec (m+1)) (k : Nat) (S : Finset (BitVec (m+1))) : Prop :=
  ∀ P : Nat → Finset (BitVec (m+1)) → Prop, P 0 {goal} →
    (∀ {k a b U} (s t : Bool), a ≠ b → gate s t a b ∉ insert a (insert b U) →
      gate s t a b ≠ 0 → P k (insert (gate s t a b) U) → P (k+1) (insert a (insert b U))) →
    P k S
theorem Path.done {g : BitVec (m+1)} : Path g 0 {g} := fun _ d _ => d
theorem Path.binary {g : BitVec (m+1)} {k a b U} (s t : Bool) (ne : a ≠ b)
    (fresh : gate s t a b ∉ insert a (insert b U)) (proper : gate s t a b ≠ 0)
    (tail : Path g k (insert (gate s t a b) U)) : Path g (k+1) (insert a (insert b U)) :=
  fun P d f => f s t ne fresh proper (tail P d f)
theorem canon_not (x : BitVec (m+1)) : canon (~~~x) = canon x := by
  unfold canon
  simp only [BitVec.getLsbD_not, Nat.zero_lt_succ,decide_true, Bool.true_and]
  cases x.getLsbD 0 <;> simp

theorem canon_canon (x : BitVec (m+1)) : canon (canon x) = canon x := by
  by_cases h : x.getLsbD 0 = true
  · rw [show canon x = ~~~x from if_pos h,canon_not,show canon x = ~~~x from if_pos h]
  · rw [show canon x = x from if_neg h]
    exact if_neg h

theorem sign_back (x : BitVec (m+1)) : signed (x.getLsbD 0) (canon x) = x := by
  unfold signed canon
  cases x.getLsbD 0 <;> simp

theorem canon_zero : canon (0 : BitVec (m+1)) = 0 := by simp [canon]
theorem gate_left_zero (s t : Bool) (x : BitVec (m+1)) :
    gate s t 0 x = 0 ∨ gate s t 0 x = canon x := by
  cases s with
  | false => exact Or.inl ((congrArg canon (BitVec.zero_and (x := signed t x))).trans canon_zero)
  | true =>
    cases t with
    | false => right; simp [gate,signed]
    | true => right; simp [gate,signed,canon_not]

theorem gate_right_zero (s t : Bool) (x : BitVec (m+1)) :
    gate s t x 0 = 0 ∨ gate s t x 0 = canon x := by
  rw [show gate s t x 0 = gate t s 0 x from congrArg canon (BitVec.and_comm ..)]
  exact gate_left_zero _ _ _

theorem gate_same (s t : Bool) (x : BitVec (m+1)) : gate s t x x = 0 ∨ gate s t x x = canon x := by
  cases s <;> cases t
  · exact Or.inr (congrArg canon (BitVec.and_self (x := x)))
  · exact Or.inl ((congrArg canon (BitVec.and_not_self x)).trans canon_zero)
  · exact Or.inl ((congrArg canon (BitVec.not_and_self x)).trans canon_zero)
  · exact Or.inr ((congrArg canon (BitVec.and_self (x := ~~~x))).trans (canon_not x))

variable {A : Type} [DecidableEq A] (pin : A → BitVec (m+1))
def avail (S : Finset A) := (S.image pin).erase 0
def lost (S : Finset A) := (S.filter fun x => pin x = 0).card
theorem avail_mem {S : Finset A} {x : BitVec (m+1)} :
    x ∈ avail pin S ↔ x ≠ 0 ∧ ∃ a ∈ S, pin a = x := by simp [avail]

theorem avail_mono {S T : Finset A} (h : S ⊆ T) : avail pin S ⊆ avail pin T := by
  intro y hy
  obtain ⟨hn,x,hx,rfl⟩ := (avail_mem pin).mp hy
  exact (avail_mem pin).mpr ⟨hn,x,h hx,rfl⟩

theorem avail_cases {S : Finset A} {c : A} {x : BitVec (m+1)} (h : x ∈ avail pin (insert c S)) :
    x = pin c ∨ x ∈ avail pin S := by
  obtain ⟨hn,y,hy,rfl⟩ := (avail_mem pin).mp h
  rcases Finset.mem_insert.mp hy with rfl|hy
  · exact Or.inl rfl
  · exact Or.inr ((avail_mem pin).mpr ⟨hn,y,hy,rfl⟩)

theorem lost_insert (c : A) (S : Finset A) :
    lost pin (insert c S) = lost pin S + (if pin c = 0 ∧ c ∉ S then 1 else 0) := by
  by_cases mem : c ∈ S
  · rw [Finset.insert_eq_of_mem mem,if_neg (fun q => q.2 mem),Nat.add_zero]
  · by_cases h : pin c = 0
    · rw [if_pos ⟨h,mem⟩]
      unfold lost
      rw [Finset.filter_insert,if_pos h,Finset.card_insert_of_notMem]
      exact fun q => mem (Finset.mem_filter.mp q).1
    · rw [if_neg (fun q => h q.1),Nat.add_zero]
      unfold lost
      rw [Finset.filter_insert,if_neg h]

theorem cost_skip (a b c : A) (U : Finset A) (fresh : c ∉ U)
    (both : pin a = 0 → pin b = 0 → pin c = 0) :
    lost pin (insert a (insert b U)) ≤ lost pin (insert c U) + 1 := by
  simp only [lost_insert]
  split_ifs <;> grind

def Proj (goal : BitVec (m+1)) (limit extra : Nat) (S : Finset A) : Prop :=
  ∃ k, k + lost pin S + extra ≤ limit ∧ ∃ T ⊆ avail pin S, Path goal k T

theorem proj_done (x : A) (nz : pin x ≠ 0) : Proj pin (pin x) 0 0 {x} := by
  refine ⟨0,?_,{pin x},?_,Path.done⟩ <;> simp [lost,avail] <;> exact nz
theorem proj_inv {g : BitVec (m+1)} {limit extra : Nat} (a c : A) (U : Finset A)
    (newc : c ∉ U) (eq : pin c = pin a) (tail : Proj pin g limit extra (insert c U)) :
    Proj pin g limit extra (insert a U) := by
  obtain ⟨k,hle,T,sub,path⟩ := tail
  refine ⟨k,?_,T,?_,path⟩
  · simp only [lost_insert,eq] at hle ⊢
    split_ifs at * <;> grind
  · intro x hx
    rcases avail_cases pin (sub hx) with eq'|old
    · exact (avail_mem pin).mpr ⟨((avail_mem pin).mp (sub hx)).1,a,by simp,(eq'.trans eq).symm⟩
    · exact avail_mono pin (Finset.subset_insert _ _) old

theorem proj_strong {g : BitVec (m+1)} {limit : Nat} (a b c : A) (U : Finset A)
    (newc : c ∉ U) (hc : pin c = 0) (one : pin a ≠ 0 ∨ pin b ≠ 0)
    (tail : Proj pin g limit 0 (insert c U)) : Proj pin g (limit+1) 1 (insert a (insert b U)) := by
  obtain ⟨k,le,T,sub,path⟩ := tail
  refine ⟨k,?_,T,?_,path⟩
  · simp only [lost_insert,hc] at le ⊢
    split_ifs at * <;> grind
  · intro x hx
    rcases avail_cases pin (sub hx) with eq|old
    · exact (((avail_mem pin).mp (sub hx)).1 (eq.trans hc)).elim
    · exact avail_mono pin (by intro _ mem; simp [mem]) old

theorem proj_bin {g : BitVec (m+1)} {b extra : Nat} (a x c : A) (U : Finset A)
    (can : ∀ v, canon (pin v) = pin v) (cnew : c ∉ U) (s t : Bool)
    (repr : pin c = gate s t (pin a) (pin x))
    (tail : Proj pin g b extra (insert c U)) : Proj pin g (b+1) extra (insert a (insert x U)) := by
  let prev := insert a (insert x U)
  obtain ⟨k,hle,T,sub,path⟩ := tail
  change k + lost pin (insert c U) + extra ≤ b at hle
  change T ⊆ avail pin (insert c U) at sub
  have both (ha : pin a = 0) (hx : pin x = 0) : pin c = 0 := by
    rw [repr,ha,hx]
    exact (gate_same s t 0).elim id (fun q => q.trans canon_zero)
  have skipcost := cost_skip pin a x c U cnew both
  have liftU : avail pin U ⊆ avail pin prev := avail_mono pin (by intro u hu; simp [prev,hu])
  by_cases useful : pin c ∈ T ∧ pin c ∉ avail pin prev
  · have nz := ((avail_mem pin).mp (sub useful.1)).1
    have df (v : A) (hv : v ∈ prev) : pin c ≠ pin v := by
      intro e
      exact useful.2 ((avail_mem pin).mpr ⟨nz,v,hv,e.symm⟩)
    have da := df a (by simp [prev])
    have dx := df x (by simp [prev])
    have ha : pin a ≠ 0 := by
      intro h
      have drop := gate_left_zero s t (pin x)
      rw [h] at repr
      rw [←repr,can] at drop
      exact drop.elim nz dx
    have hx : pin x ≠ 0 := by
      intro h
      have drop := gate_right_zero s t (pin a)
      rw [h] at repr
      rw [←repr,can] at drop
      exact drop.elim nz da
    have distinct : pin a ≠ pin x := by
      intro e
      have drop := gate_same s t (pin x)
      rw [e] at repr
      rw [←repr,can] at drop
      exact drop.elim nz dx
    have vcost : lost pin prev ≤ lost pin (insert c U) := by
      simp only [prev,lost_insert]
      split_ifs <;> grind
    let V := T.erase (pin c)
    have old (v : BitVec (m+1)) (hv : v ∈ V) : v ∈ avail pin U :=
      (avail_cases pin (sub (Finset.mem_erase.mp hv).2)).resolve_left (Finset.mem_erase.mp hv).1
    refine ⟨k+1,by change k+1+lost pin prev + extra ≤ b+1; omega,insert (pin a) (insert (pin x) V),?_,?_⟩
    · intro v hv
      rcases Finset.mem_insert.mp hv with rfl|hv
      · exact (avail_mem pin).mpr ⟨ha,a,by simp [prev],rfl⟩
      rcases Finset.mem_insert.mp hv with rfl|hv
      · exact (avail_mem pin).mpr ⟨hx,x,by simp [prev],rfl⟩
      exact liftU (old _ hv)
    · apply Path.binary s t distinct
      · rw [←repr]
        simp [V,da,dx]
      · rwa [←repr]
      · rwa [←repr,show insert (pin c) V = T from Finset.insert_erase useful.1]
  · refine ⟨k,by change k+lost pin (insert a (insert x U)) + extra ≤ b+1; omega,T,?_,path⟩
    intro v hv
    rcases avail_cases pin (sub hv) with rfl|old
    · by_contra miss
      exact useful ⟨hv,miss⟩
    · exact liftU old
end PEqualNP.Outside.L_meta_31725.Reduce

namespace PEqualNP.Outside.L_meta_31725
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev Word := BitVec 256
def ones : Word := BitVec.allOnes 256
def goal : Word := 0xfffffffffffffffffffffffaffeefc00fffffffffffffeaafffffffaffeefc00
def roots : List Word := [
  0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,
  0xffffffffffffffffffffffffffffffff00000000000000000000000000000000,
  0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,
  0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,
  0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,
  0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,
  0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,
  0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000]
def join (d : Bool) (a b : Word) : Word := if d then a ||| b else a &&& b

def Live (b n : Nat) (S : Finset Word) : Prop :=
  ∀ (P : Nat → Nat → Finset Word → Prop),
    P 0 0 {goal} →
    (∀ {i j : Nat} {a x : Word} {U : Finset Word} (d : Bool), a ≠ x →
      join d a x ∉ insert a (insert x U) → (join d a x ≠ 0 ∧ join d a x ≠ ones) →
      P i j (insert (join d a x) U) → P (i+1) j (insert a (insert x U))) →
    (∀ {i j : Nat} {a : Word} {U : Finset Word},
      ~~~a ∉ insert a U → (~~~a ≠ 0 ∧ ~~~a ≠ ones) →
      P i j (insert (~~~a) U) → P i (j+1) (insert a U)) →
    P b n S

theorem Live.done : Live 0 0 {goal} :=
  fun _ done _ _ => done

theorem Live.binary {b n : Nat} {a x : Word} {U : Finset Word} (d : Bool) (ne : a ≠ x)
    (fresh : join d a x ∉ insert a (insert x U))
    (proper : join d a x ≠ 0 ∧ join d a x ≠ ones)
    (tail : Live b n (insert (join d a x) U)) :
    Live (b+1) n (insert a (insert x U)) :=
  fun P done binary inversion => binary d ne fresh proper (tail P done binary inversion)

theorem Live.inversion {b n : Nat} {a : Word} {U : Finset Word}
    (fresh : ~~~a ∉ insert a U) (proper : ~~~a ≠ 0 ∧ ~~~a ≠ ones)
    (tail : Live b n (insert (~~~a) U)) : Live b (n+1) (insert a U) :=
  fun P done binary inversion => inversion fresh proper (tail P done binary inversion)

theorem Live.recPlain {motive : ∀ {b n S}, Live b n S → Prop}
    (done : motive Live.done)
    (binary : ∀ {b n : Nat} {a x : Word} {U : Finset Word} (d : Bool) (ne : a ≠ x)
      (fresh : join d a x ∉ insert a (insert x U))
      (proper : join d a x ≠ 0 ∧ join d a x ≠ ones)
      (tail : Live b n (insert (join d a x) U)),
      motive tail → motive (Live.binary d ne fresh proper tail))
    (inversion : ∀ {b n : Nat} {a : Word} {U : Finset Word}
      (fresh : ~~~a ∉ insert a U) (proper : ~~~a ≠ 0 ∧ ~~~a ≠ ones)
      (tail : Live b n (insert (~~~a) U)),
      motive tail → motive (Live.inversion fresh proper tail))
    {b n : Nat} {S : Finset Word} (h : Live b n S) : motive h := by
  let P (b n : Nat) (S : Finset Word) : Prop := ∃ p : Live b n S, motive p
  have result : P b n S := by
    apply h P
    · exact ⟨Live.done,done⟩
    · intro i j a x U d ne fresh proper tail
      obtain ⟨p,ih⟩ := tail
      exact ⟨Live.binary d ne fresh proper p,binary d ne fresh proper p ih⟩
    · intro i j a U fresh proper tail
      obtain ⟨p,ih⟩ := tail
      exact ⟨Live.inversion fresh proper p,inversion fresh proper p ih⟩
  obtain ⟨_,proof⟩ := result
  exact proof

theorem Live.casesPlain {motive : ∀ {b n S}, Live b n S → Prop}
    (done : motive Live.done)
    (binary : ∀ {b n : Nat} {a x : Word} {U : Finset Word} (d : Bool) (ne : a ≠ x)
      (fresh : join d a x ∉ insert a (insert x U))
      (proper : join d a x ≠ 0 ∧ join d a x ≠ ones)
      (tail : Live b n (insert (join d a x) U)), motive (Live.binary d ne fresh proper tail))
    (inversion : ∀ {b n : Nat} {a : Word} {U : Finset Word}
      (fresh : ~~~a ∉ insert a U) (proper : ~~~a ≠ 0 ∧ ~~~a ≠ ones)
      (tail : Live b n (insert (~~~a) U)), motive (Live.inversion fresh proper tail))
    {b n : Nat} {S : Finset Word} (h : Live b n S) : motive h := by
  apply Live.recPlain (motive := @motive) done _ _ h
  · intro i j a x U d ne fresh proper tail _
    exact binary d ne fresh proper tail
  · intro i j a U fresh proper tail _
    exact inversion fresh proper tail

theorem goal_proper : goal ≠ 0 ∧ goal ≠ ones := by decide +kernel

def assignment (r : Fin 256) : Fin 8 → Bool := fun i => r.val.testBit (([0,7,1,2,6,3,4,5] : List Nat).get i)
def readBit (r : Fin 256) (v : Word) := v.getLsbD r
@[local simp] theorem read_ones (r : Fin 256) : readBit r ones = true := by
  exact (BitVec.getLsbD_allOnes).trans (decide_eq_true r.isLt)
@[local simp] theorem read_zero (r : Fin 256) : readBit r 0 = false := by simp [readBit]
@[local simp] theorem ones_and (a : Word) : ones &&& a = a := BitVec.allOnes_and
@[local simp] theorem and_ones (a : Word) : a &&& ones = a := BitVec.and_allOnes
@[local simp] theorem ones_or (a : Word) : ones ||| a = ones := BitVec.allOnes_or
@[local simp] theorem or_ones (a : Word) : a ||| ones = ones := BitVec.or_allOnes

theorem roots_bits : ∀ r : Fin 256, roots.map (readBit r) = List.ofFn (assignment r) := by decide +kernel
abbrev graph := Frame.target
theorem row_flags : ∀ r : Fin 256, graph (assignment r) = readBit r goal := by decide +kernel

theorem getD_map {α β} (f : α → β) (s : List α) (i : Nat) (a : α) :
    (s.map f).getD i (f a) = f (s.getD i a) := by
  induction s generalizing i with
  | nil => simp
  | cons x s ih => cases i with
    | zero => rfl
    | succ i => exact ih i

theorem getD_mem_or (w : List Word) (i : Nat) : w.getD i 0 ∈ w ∨ w.getD i 0 = 0 := by
  by_cases h : i < w.length
  · left
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
    exact List.getElem_mem h
  · right
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    rfl

def binaryWord (w : List Word) (g : Gate) : Word :=
  let d := match g.op with | .or => true | _ => false
  match g.inputs with
  | [] => if d then 0 else ones
  | [a] => w.getD a 0
  | a::b::_ => join d (w.getD a 0) (w.getD b 0)

def gateWord (w : List Word) (g : Gate) : Word :=
  match g.op with
  | .not => match g.inputs with | [] => ones | a::_ => ~~~(w.getD a 0)
  | _ => binaryWord w g

def binCost (g : Gate) : Nat :=
  match g.op, g.inputs with | .and, _::_::_ | .or, _::_::_ => 1 | _, _ => 0
def invCost (g : Gate) : Nat := match g.op with | .not => 1 | _ => 0

def binaryCount : List Gate → Nat
  | [] => 0 | g::gs => binaryCount gs + binCost g
def inversionCount : List Gate → Nat
  | [] => 0 | g::gs => inversionCount gs + invCost g

def stepWord (w : List Word) (g : Gate) := w ++ [gateWord w g]
def stepBit (w : List Bool) (g : Gate) :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def allowed (g : Gate) := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

theorem step_correct (r : Fin 256) (w : List Word) (g : Gate) (h : allowed g) :
    (stepWord w g).map (readBit r) = stepBit (w.map (readBit r)) g := by
  have get (j : Nat) : (w[j]?.map (readBit r)).getD false = readBit r (w[j]?.getD 0) := by
    cases w[j]? <;> simp [readBit]
  rcases g with ⟨op,ins⟩
  rcases h with ⟨hOp, hlen⟩
  change op = .and ∨ op = .or ∨ op = .not at hOp
  change ins.length ≤ 2 at hlen
  rcases hOp with rfl|rfl|rfl <;> cases ins with
  | nil => simp [stepWord,stepBit,gateWord,binaryWord,GateOp.eval] <;> exact read_zero r
  | cons a rest =>
    cases rest with
    | nil => simp [stepWord,stepBit,gateWord,binaryWord,get,GateOp.eval,readBit]
    | cons b tail =>
      cases tail with
      | nil => simp [stepWord,stepBit,gateWord,binaryWord,get,GateOp.eval,join,readBit]
      | cons c rest => simp at hlen

theorem fold_correct (r : Fin 256) (gs : List Gate) (w : List Word)
    (h : ∀ g ∈ gs, allowed g) :
    (gs.foldl stepWord w).map (readBit r) = gs.foldl stepBit (w.map (readBit r)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih _ (by grind), step_correct r w g (h _ (by simp))]

theorem sampled_circuit (C : Circuit) (hp : ∀ g ∈ C.gates, allowed g)
    (accept : ∀ r : Fin 256, C.eval (List.ofFn (assignment r)) = readBit r goal) :
    (C.gates.foldl stepWord roots).getD C.output 0 = goal := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  let r : Fin 256 := ⟨i,hi⟩
  change readBit r ((C.gates.foldl stepWord roots).getD C.output 0) = readBit r goal
  rw [← getD_map (readBit r) (C.gates.foldl stepWord roots) C.output 0]
  rw [fold_correct r C.gates roots hp, roots_bits]
  rw [read_zero]
  exact accept r

theorem nontrivial_join (d : Bool) (a b : Word)
    (haa : join d a b ≠ a) (hbb : join d a b ≠ b)
    (h0 : join d a b ≠ 0) (h1 : join d a b ≠ ones) :
    a ≠ 0 ∧ b ≠ 0 ∧ a ≠ ones ∧ b ≠ ones ∧ a ≠ b := by
  refine ⟨?_,?_,?_,?_,?_⟩ <;> rintro rfl <;> cases d <;> simp_all [join]

theorem not_ones : ~~~ones = (0 : Word) := by decide +kernel
theorem not_zero : ~~~(0 : Word) = ones := by decide +kernel

def Parents (w : List Word) (g : Gate) (c : Word) : Prop :=
  (∃ d a b, c = join d a b ∧ binCost g = 1 ∧ a ∈ w ∧ b ∈ w ∧
    a ≠ 0 ∧ b ≠ 0 ∧ a ≠ ones ∧ b ≠ ones ∧ a ≠ b) ∨
  (∃ a, c = ~~~a ∧ invCost g = 1 ∧ a ∈ w ∧ a ≠ 0 ∧ a ≠ ones)

theorem binary_parents (w : List Word) (op : GateOp) (opok : op = .and ∨ op = .or)
    (ins : List Nat) (missing : binaryWord w ⟨op,ins⟩ ∉ w)
    (p0 : binaryWord w ⟨op,ins⟩ ≠ 0) (p1 : binaryWord w ⟨op,ins⟩ ≠ ones) :
    Parents w ⟨op,ins⟩ (binaryWord w ⟨op,ins⟩) := by
  let d := match op with | .or => true | _ => false
  cases ins with
  | nil =>
    change (if d then 0 else ones) ≠ 0 at p0
    change (if d then 0 else ones) ≠ ones at p1
    cases d <;> simp_all
  | cons i rest =>
    cases rest with
    | nil =>
      change w.getD i 0 ∉ w at missing
      change w.getD i 0 ≠ 0 at p0
      exact (getD_mem_or w i).elim (fun h => (missing h).elim) (fun h => (p0 h).elim)
    | cons j tail =>
      let a := w.getD i 0
      let b := w.getD j 0
      change join d a b ∉ w at missing
      change join d a b ≠ 0 at p0
      change join d a b ≠ ones at p1
      have absent (u : Word) (mem : u ∈ w ∨ u = 0) : join d a b ≠ u := by
        intro e
        exact mem.elim (fun m => missing (e ▸ m)) (fun z => p0 (e.trans z))
      have parts := nontrivial_join d a b (absent _ (getD_mem_or w i))
        (absent _ (getD_mem_or w j)) p0 p1

      have cost : binCost ⟨op,i::j::tail⟩ = 1 := by rcases opok with rfl|rfl <;> rfl
      exact Or.inl ⟨d,a,b,rfl,cost,(getD_mem_or w i).resolve_right parts.1,
        (getD_mem_or w j).resolve_right parts.2.1,parts⟩

theorem gate_parents (w : List Word) (g : Gate) (okay : allowed g)
    (missing : gateWord w g ∉ w) (p0 : gateWord w g ≠ 0) (p1 : gateWord w g ≠ ones) :
    Parents w g (gateWord w g) := by
  rcases g with ⟨op,ins⟩
  have ops : op = .and ∨ op = .or ∨ op = .not := okay.1
  rcases ops with h|h|h
  · subst op
    exact binary_parents w _ (.inl rfl) ins missing p0 p1
  · subst op
    exact binary_parents w _ (.inr rfl) ins missing p0 p1
  · subst op
    cases ins with
    | nil => exact (p1 rfl).elim
    | cons i rest =>
      let a := w.getD i 0
      change ~~~a ≠ 0 at p0
      change ~~~a ≠ ones at p1
      have a0 : a ≠ 0 := fun e => p1 (e ▸ not_zero)
      have a1 : a ≠ ones := fun e => p0 (e ▸ not_ones)
      exact Or.inr ⟨a,rfl,rfl,(getD_mem_or w i).resolve_right a0,a0,a1⟩

def Trace (b n : Nat) (w : List Word) : Prop :=
  ∃ (k j : Nat) (S : Finset Word), k ≤ b ∧ j ≤ n ∧
    (∀ x ∈ S, x ∈ w ∧ x ≠ 0 ∧ x ≠ ones) ∧ Live k j S

theorem unwind (b n : Nat) (w : List Word) (g : Gate) (okay : allowed g)
    (t : Trace b n (stepWord w g)) : Trace (b + binCost g) (n + invCost g) w := by
  obtain ⟨k,j,S,hk,hj,valid,live⟩ := t
  let c := gateWord w g
  have prev (x : Word) (hx : x ∈ S) : (x ∈ w ∨ x = c) ∧ x ≠ 0 ∧ x ≠ ones := by
    simpa [c,stepWord] using valid x hx
  by_cases used : c ∈ S
  · by_cases old : c ∈ w
    · exact ⟨k,j,S,by omega,by omega,fun x hx => by have h := prev x hx; grind,live⟩
    · let U := S.erase c
      have uc : c ∉ U := Finset.notMem_erase _ _
      have sub (x : Word) (hx : x ∈ U) : x ∈ w ∧ x ≠ 0 ∧ x ≠ ones := by
        have hx' := Finset.mem_erase.mp hx
        have h := prev x hx'.2
        exact ⟨h.1.resolve_right hx'.1,h.2⟩
      have back : insert c U = S := Finset.insert_erase used
      rcases gate_parents w g okay old (valid c used).2.1 (valid c used).2.2 with binary|inv
      · obtain ⟨d,a,x,eqc,cost,ha,hx,a0,x0,a1,x1,ne⟩ := binary
        change c = join d a x at eqc
        have ca : c ≠ a := fun e => old (e ▸ ha)
        have cx : c ≠ x := fun e => old (e ▸ hx)
        refine ⟨k+1,j,insert a (insert x U),by omega,by omega,?_,?_⟩
        · intro y hy
          rcases Finset.mem_insert.mp hy with rfl|hy
          · exact ⟨ha,a0,a1⟩
          rcases Finset.mem_insert.mp hy with rfl|hy
          · exact ⟨hx,x0,x1⟩
          exact sub _ hy
        · apply Live.binary d ne
          · simpa [← eqc,ca,cx] using uc
          · exact eqc ▸ (valid c used).2
          · rwa [← eqc,back]
      · obtain ⟨a,eqc,cost,ha,a0,a1⟩ := inv
        change c = ~~~a at eqc
        have ca : c ≠ a := fun e => old (e ▸ ha)
        refine ⟨k,j+1,insert a U,by omega,by omega,?_,?_⟩
        · intro y hy
          rcases Finset.mem_insert.mp hy with rfl|hy
          · exact ⟨ha,a0,a1⟩
          exact sub _ hy
        · apply Live.inversion
          · simpa [←eqc,ca] using uc
          · exact eqc ▸ (valid c used).2
          · rwa [←eqc,back]
  · exact ⟨k,j,S,by omega,by omega,fun x hx => by have h := prev x hx; grind,live⟩

theorem trace_aux (gs : List Gate) (w : List Word) (out : Nat) (hp : ∀ g ∈ gs, allowed g)
    (success : (gs.foldl stepWord w).getD out 0 = goal) :
    Trace (binaryCount gs) (inversionCount gs) w := by
  induction gs generalizing w with
  | nil =>
    change w.getD out 0 = goal at success
    have h := (getD_mem_or w out).resolve_right (success ▸ goal_proper.1)
    rw [success] at h
    refine ⟨0,0,{goal},by simp [binaryCount],by simp [inversionCount],?_,Live.done⟩
    simpa using And.intro h goal_proper
  | cons g gs ih => exact unwind _ _ w g (hp _ (by simp)) (ih _ (by grind) success)

theorem circuit_live (C : Circuit) (legal : ∀ g ∈ C.gates, allowed g)
    (correct : ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = graph x) :
    ∃ b ≤ binaryCount C.gates, ∃ n ≤ inversionCount C.gates, ∃ S ⊆ roots.toFinset, Live b n S := by
  have accept (r : Fin 256) : C.eval (List.ofFn (assignment r)) = readBit r goal :=
    (correct _).trans (row_flags r)
  obtain ⟨b,n,S,hb,hn,incl,live⟩ := trace_aux _ _ _ legal (sampled_circuit C legal accept)
  exact ⟨b,hb,n,hn,S,fun x hx => List.mem_toFinset.mpr (incl x hx).1,live⟩

theorem agree_join (p q : Fin 256) (d : Bool) (a x : Word)
    (ha : readBit p a = readBit q a) (hx : readBit p x = readBit q x) :
    readBit p (join d a x) = readBit q (join d a x) := by
  cases d <;> simp_all [join,readBit]

theorem agree_not (p q : Fin 256) (a : Word) (ha : readBit p a = readBit q a) :
    readBit p (~~~a) = readBit q (~~~a) := by simp_all [readBit]

theorem live_agrees {b n S} (live : Live b n S) (p q : Fin 256)
    (same : ∀ x ∈ S, readBit p x = readBit q x) : readBit p goal = readBit q goal := by
  induction live using Live.recPlain with
  | done => exact same goal (by simp)
  | @binary b n a x U d _ _ _ _ ih =>
    apply ih
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl|hy
    · exact agree_join p q d a x (same _ (by simp)) (same _ (by simp))
    · exact same _ (by simp [hy])
  | @inversion b n a U _ _ _ ih =>
    apply ih
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl|hy
    · exact agree_not p q a (same _ (by simp))
    · exact same _ (by simp [hy])

def witnesses (i : Fin 8) : Fin 256 × Fin 256 := ([(16,17),(64,192),(8,10),(8,12),(1,65),(2,10),(1,17),(1,33)] : List (Fin 256 × Fin 256)).get i
theorem witness_correct : ∀ i : Fin 8,
    readBit (witnesses i).1 goal ≠ readBit (witnesses i).2 goal ∧
    ∀ j : Fin 8, readBit (witnesses i).1 (roots.get j) =
      readBit (witnesses i).2 (roots.get j) ∨ j = i := by decide +kernel

theorem roots_full {b n S} (live : Live b n S) (sub : S ⊆ roots.toFinset) :
    S = roots.toFinset := by
  apply Finset.Subset.antisymm sub
  intro x hx
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp (List.mem_toFinset.mp hx)
  obtain ⟨distinct,only⟩ := witness_correct i
  by_contra missing
  apply distinct (live_agrees live _ _ ?_)
  intro w hw
  obtain ⟨j,rfl⟩ := List.mem_iff_get.mp (List.mem_toFinset.mp (sub hw))
  exact (only j).resolve_right (by rintro rfl; exact missing hw)

theorem cost_bound (gs : List Gate) : binaryCount gs + inversionCount gs ≤ gs.length := by
  induction gs with
  | nil => simp [binaryCount,inversionCount]
  | cons g gs ih =>
    have hg : binCost g + invCost g ≤ 1 := by
      rcases g with ⟨op,ins⟩
      cases op <;> cases ins with
      | nil => simp [binCost,invCost]
      | cons i tail => cases tail <;> simp [binCost,invCost]
    simp only [binaryCount,inversionCount,List.length_cons]
    omega

theorem zero_inversions (gs : List Gate) (none : ∀ g ∈ gs, g.op ≠ .not) :
    inversionCount gs = 0 := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    have ng := none g (by simp)
    have cost : invCost g = 0 := by rcases g with ⟨op,ins⟩; cases op <;> simp_all [invCost]
    rw [inversionCount,cost,ih (by grind),Nat.add_zero]

theorem unique_inversion (gs : List Gate)
    (uniq : ∀ i j : Fin gs.length, (gs.get i).op = .not → (gs.get j).op = .not → i=j) :
    inversionCount gs ≤ 1 := by
  induction gs with
  | nil => decide
  | cons g gs ih =>
    by_cases head : g.op = .not
    · have none (x : Gate) (hx : x ∈ gs) : x.op ≠ .not := by
        obtain ⟨j,rfl⟩ := List.mem_iff_get.mp hx
        intro nj
        have eq := uniq ⟨0,by simp⟩ j.succ head nj
        have e := congrArg Fin.val eq
        simp at e
      have one : invCost g = 1 := by simp [invCost,head]
      rw [inversionCount,zero_inversions gs none,one]
    · have zero : invCost g = 0 := by rcases g with ⟨op,ins⟩; cases op <;> simp_all [invCost]
      rw [inversionCount,zero,Nat.add_zero]
      apply ih
      intro i j ni nj
      exact Fin.succ_injective _ (uniq i.succ j.succ ni nj)

theorem full_chain (gates : List Gate) (out : Nat)
    (legal : ∀ g ∈ gates, allowed g)
    (uniq : ∀ i j : Fin gates.length, (gates.get i).op = .not → (gates.get j).op = .not → i=j)
    (correct : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates,out⟩ (List.ofFn x) = graph x) :
    ∃ b n, b+n ≤ gates.length ∧ n ≤ 1 ∧ Live b n roots.toFinset := by
  obtain ⟨b,hb,n,hn,S,sub,live⟩ := circuit_live ⟨gates,out⟩ legal correct
  rw [roots_full live sub] at live
  exact ⟨b,n,(Nat.add_le_add hb hn).trans (cost_bound gates),hn.trans (unique_inversion gates uniq),live⟩

theorem has_inversion_cost (gates : List Gate) (hasNot : ∃ g ∈ gates, g.op = .not) :
    1 ≤ inversionCount gates := by
  induction gates with
  | nil => simp at hasNot
  | cons g gs ih =>
    by_cases top : g.op = .not
    · simp [inversionCount, invCost, top]
    · obtain ⟨f,hf,inv⟩ := hasNot
      have hin : f ∈ gs := (List.mem_cons.mp hf).resolve_left (fun eq => top (eq ▸ inv))
      have tail := ih ⟨f,hin,inv⟩
      rw [inversionCount]
      omega

theorem signed_chain {gates : List Gate} {out : Nat}
    (legal : ∀ g ∈ gates, allowed g)
    (uniq : ∀ i j : Fin gates.length, (gates.get i).op = .not → (gates.get j).op = .not → i=j)
    (correct : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates,out⟩ (List.ofFn x) = graph x)
    (hasNot : ∃ g ∈ gates, g.op = .not) :
    ∃ b n, b+1 ≤ gates.length ∧ n ≤ 1 ∧ Live b n roots.toFinset := by
  obtain ⟨b,hb,n,hn,S,sub,live⟩ := circuit_live ⟨gates,out⟩ legal correct
  rw [roots_full live sub] at live
  exact ⟨b,n,(Nat.add_le_add hb (has_inversion_cost gates hasNot)).trans (cost_bound gates),
    hn.trans (unique_inversion gates uniq),live⟩

def counted (g : Gate) : Bool := match g.op with | .not => false | _ => true

theorem binaryCount_le_countP (gs : List Gate) :
    binaryCount gs ≤ gs.countP counted := by
  induction gs with
  | nil => simp [binaryCount]
  | cons g gs ih =>
    have cap : binCost g ≤ (counted g).toNat := by
      obtain ⟨op, inputs⟩ := g
      cases op <;> cases inputs with
      | nil => simp [binCost, counted]
      | cons a rest => cases rest <;> simp [binCost, counted]
    rw [binaryCount, List.countP_cons]
    cases h : counted g <;> simp [h] at cap ⊢ <;> omega

theorem circuit_chain (gs : List Gate) (o : Nat)
    (legal : FanInTwo ⟨gs,o⟩)
    (correct : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = Frame.target x) :
    ∃ b n, b ≤ gs.countP counted ∧ Live b n roots.toFinset := by
  obtain ⟨b,hb,n,_,S,sub,live⟩ := circuit_live ⟨gs,o⟩ legal correct
  rw [roots_full live sub] at live
  exact ⟨b,n,hb.trans (binaryCount_le_countP gs),live⟩

theorem freely_chain (gs : List Gate) (o : Nat)
    (legal : FanInTwo ⟨gs,o⟩)
    (correct : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = Frame.target x)
    (hasNot : ∃ g ∈ gs, g.op = .not) :
    ∃ b n, b+1 ≤ gs.length ∧ Live b n roots.toFinset := by
  obtain ⟨b,hb,n,_,S,sub,live⟩ := circuit_live ⟨gs,o⟩ legal correct
  rw [roots_full live sub] at live
  exact ⟨b,n,(Nat.add_le_add hb (has_inversion_cost gs hasNot)).trans (cost_bound gs),live⟩

end PEqualNP.Outside.L_meta_31725

namespace PEqualNP.Outside.L_meta_31725.Reduce
open PEqualNP.Outside.L_meta_31725

def half (b : Bool) (w : Word) : BitVec 128 :=
  if b then w.extractLsb' 128 128 else w.extractLsb' 0 128
def pin128 (b : Bool) (w : Word) := canon (half b w)
def lit : Word := 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000
def literal (w : Word) := w = lit ∨ w = ~~~lit
def indep (w : Word) := half false w = half true w
def safe (w : Word) : Prop := literal w ∨ indep w ∧ pin128 false w ≠ 0

theorem half_not (b : Bool) (v : Word) : half b (~~~v) = ~~~half b v := by
  cases b <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj <;>
    simp [half,BitVec.getLsbD_not,hj,show 128+j < 256 by omega,show j < 256 by omega]
theorem half_and (b : Bool) (v w : Word) : half b (v &&& w) = half b v &&& half b w := by
  cases b <;> exact BitVec.extractLsb'_and
theorem half_or (b : Bool) (v w : Word) : half b (v ||| w) = half b v ||| half b w := by
  cases b <;> exact BitVec.extractLsb'_or
theorem indep_nz (w : Word) (h : indep w) (hp : w ≠ 0 ∧ w ≠ ones) : pin128 false w ≠ 0 := by
  change half false w = half true w at h
  have rebuild : half true w ++ half false w = w := BitVec.extractLsb'_append_extractLsb'
  rw [←h] at rebuild
  unfold pin128 canon
  intro bad
  split at bad
  · have both := congrArg (fun x : BitVec 128 => ~~~x) bad
    simp only [BitVec.not_not,BitVec.not_zero] at both
    rw [both] at rebuild
    exact hp.2 (rebuild.symm.trans (by decide))
  · rw [bad] at rebuild
    exact hp.1 (rebuild.symm.trans (by decide))

theorem safe_not (v : Word) (h : safe v) : safe (~~~v) := by
  rcases h with (rfl|rfl)|⟨e,q⟩
  · exact Or.inl (Or.inr rfl)
  · exact Or.inl (Or.inl BitVec.not_not)
  · right
    exact ⟨by simpa only [indep,half_not] using congrArg (fun t => ~~~t) e,
      by simpa only [pin128,half_not,canon_not] using q⟩
theorem indep_join (d : Bool) {a b : Word} (ha : indep a) (hb : indep b) :
    indep (join d a b) := by
  unfold indep at *
  cases d <;> simp [join,half_or,half_and,ha,hb]
theorem p128neg (b : Bool) (w : Word) : pin128 b (~~~w) = pin128 b w := by
  simp [pin128,half_not,canon_not]
theorem p128repr (e d : Bool) (a b : Word) :
    ∃ s t, pin128 e (join d a b) = gate s t (pin128 e a) (pin128 e b) := by
  cases d
  · exact ⟨(half e a).getLsbD 0,(half e b).getLsbD 0,by simp only [pin128,gate,sign_back]; exact congrArg canon (half_and _ _ _)⟩
  · refine ⟨(~~~(half e a)).getLsbD 0,(~~~(half e b)).getLsbD 0,?_⟩
    unfold gate pin128
    rw [←canon_not (half e a),←canon_not (half e b),sign_back,sign_back,←BitVec.not_or,canon_not]
    exact congrArg canon (half_or _ _ _)
theorem pin128goal (e : Bool) : pin128 e goal ≠ 0 := by cases e <;> decide +kernel
theorem ordinary {b n S} (h : Live b n S) (e : Bool) : Proj (pin128 e) (pin128 e goal) b 0 S := by
  induction h using Live.recPlain with
  | done => exact proj_done _ _ (pin128goal _)
  | @inversion b n a U fresh proper tail ih =>
    exact proj_inv _ _ _ _ (fun h => fresh (by simp [h])) (p128neg e a) ih
  | @binary b n a x U d ne fresh proper tail ih =>
    obtain ⟨s,t,rep⟩ := p128repr e d a x
    exact proj_bin _ _ _ _ _ (fun v => canon_canon _) (fun h => fresh (by simp [h])) s t rep ih

theorem choose_kill (d : Bool) (v w : Word) (h : literal v) :
    ∃ e, pin128 e (join d v w) = 0 := by
  rcases h with rfl|rfl <;> cases d
  · exact ⟨false,by rw [pin128,show join false lit w = lit &&& w from rfl,half_and,show half false lit = 0 by decide]; simp only [show ∀ v : BitVec 128, (0 : BitVec 128) &&& v = 0 from fun v => BitVec.zero_and]; decide⟩
  · exact ⟨true,by rw [pin128,show join true lit w = lit ||| w from rfl,half_or,show half true lit = BitVec.allOnes 128 by decide,BitVec.allOnes_or]; decide⟩
  · exact ⟨true,by rw [pin128,show join false (~~~lit) w = (~~~lit) &&& w from rfl,half_and,show half true (~~~lit) = 0 by decide]; simp only [show ∀ v : BitVec 128, (0 : BitVec 128) &&& v = 0 from fun v => BitVec.zero_and]; decide⟩
  · exact ⟨false,by rw [pin128,show join true (~~~lit) w = (~~~lit) ||| w from rfl,half_or,show half false (~~~lit) = BitVec.allOnes 128 by decide,BitVec.allOnes_or]; decide⟩
theorem nz_else {w : Word} (h : indep w) (nz : pin128 false w ≠ 0) (e : Bool) : pin128 e w ≠ 0 := by
  cases e
  · exact nz
  · change half false w = half true w at h
    simpa only [pin128,←h] using nz
theorem impossible_lits (d : Bool) (a x : Word) (ha : literal a) (hx : literal x)
    (ne : a ≠ x) (proper : join d a x ≠ 0 ∧ join d a x ≠ ones) : False := by
  rcases ha with rfl|rfl <;> rcases hx with rfl|rfl <;> cases d <;>
    first | exact ne rfl | exact proper.1 (by decide) | exact proper.2 (by decide)
theorem join_comm (d : Bool) (a b : Word) : join d a b = join d b a := by
  cases d <;> simp [join,BitVec.and_comm,BitVec.or_comm]

theorem chooseFirst {b n S} (h : Live b n S) :
    (∀ v ∈ S, safe v) → ∃ e, Proj (pin128 e) (pin128 e goal) b 1 S := by
  induction h using Live.recPlain with
  | done =>
    intro ok
    exact (show ¬ safe goal by unfold safe literal indep; decide +kernel) (ok _ (by simp)) |>.elim
  | @inversion b n a U fresh proper tail ih =>
    intro ok
    have ta : ∀ v ∈ insert (~~~a) U, safe v := by
      intro v hv
      rcases Finset.mem_insert.mp hv with rfl|vU
      · exact safe_not a (ok a (by simp))
      · exact ok v (by simp [vU])
    obtain ⟨e,good⟩ := ih ta
    exact ⟨e,proj_inv _ _ _ _ (fun h => fresh (by simp [h])) (p128neg e a) good⟩
  | @binary b n a x U d ne fresh proper tail ih =>
    intro ok
    have freshU : join d a x ∉ U := fun h => fresh (by simp [h])
    rcases ok a (by simp) with ha|⟨ea,na⟩ <;> rcases ok x (by simp) with hx|⟨ex,nx⟩
    · exact (impossible_lits d a x ha hx ne proper).elim
    · obtain ⟨e,kill⟩ := choose_kill d a x ha
      exact ⟨e,proj_strong _ _ _ _ _ freshU kill (Or.inr (nz_else ex nx e)) (ordinary tail e)⟩
    · obtain ⟨e,kill⟩ := choose_kill d x a hx
      rw [join_comm d x a] at kill
      exact ⟨e,proj_strong _ _ _ _ _ freshU kill (Or.inl (nz_else ea na e)) (ordinary tail e)⟩
    · have ec := indep_join d ea ex
      have ta : ∀ v ∈ insert (join d a x) U, safe v := by
        intro v hv
        rcases Finset.mem_insert.mp hv with rfl|vU
        · exact Or.inr ⟨ec,indep_nz _ ec proper⟩
        · exact ok v (by simp [vU])
      obtain ⟨e,good⟩ := ih ta
      obtain ⟨s,t,rep⟩ := p128repr e d a x
      exact ⟨e,proj_bin _ _ _ _ _ (fun v => canon_canon _) freshU s t rep good⟩
end PEqualNP.Outside.L_meta_31725.Reduce

namespace PEqualNP.Outside.L_meta_31725.Reduce
open PEqualNP.Outside.L_meta_31725

def sixPin (w : BitVec 128) : BitVec 64 := canon (w.setWidth 64)
theorem sixPin_not (w : BitVec 128) : sixPin (~~~w) = sixPin w := by
  unfold sixPin; rw [BitVec.setWidth_not (by decide),canon_not]
theorem sixPin_canon (w : BitVec 128) : sixPin (canon w) = sixPin w := by
  by_cases h : w.getLsbD 0 = true
  · rw [show canon w = ~~~w from if_pos h,sixPin_not]
  · rw [show canon w = w from if_neg h]
theorem sixPin_signed (s : Bool) (w : BitVec 128) : sixPin (signed s w) = sixPin w := by
  cases s; rfl; exact sixPin_not _
theorem six_repr (s t : Bool) (a b : BitVec 128) :
    ∃ u v, sixPin (gate s t a b) = gate u v (sixPin a) (sixPin b) := by
  let x := signed s a; let y := signed t b
  change ∃ u v, sixPin (canon (x &&& y)) = gate u v (sixPin a) (sixPin b)
  rw [sixPin_canon,← sixPin_signed s a,← sixPin_signed t b]
  refine ⟨(x.setWidth 64).getLsbD 0,(y.setWidth 64).getLsbD 0,?_⟩
  change canon ((x &&& y).setWidth 64) = gate ((x.setWidth 64).getLsbD 0) ((y.setWidth 64).getLsbD 0) (canon (x.setWidth 64)) (canon (y.setWidth 64))
  simp only [gate,sign_back]; exact congrArg canon BitVec.setWidth_and
theorem second {g : BitVec 128} {k S} (h : Path g k S) (nz : sixPin g ≠ 0) :
    Proj sixPin (sixPin g) k 0 S := by
  apply h (fun k S => Proj sixPin (sixPin g) k 0 S) (proj_done _ _ nz)
  intro j a b U s t ne fresh proper tail
  obtain ⟨u,v,rep⟩ := six_repr s t a b
  exact proj_bin _ _ _ _ _ (fun w => canon_canon _) (fun q => fresh (by simp [q])) u v rep tail

def sevenRaw : List (BitVec 128) := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffff0000000000000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000]
def cliqueRaw : List (BitVec 64) := [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000]
def cliqueGoal : BitVec 64 := 0xfffffffaffeefc00
theorem path_equal {m : Nat} {g : BitVec (m+1)} {k S} (h : Path g k S) (p q : Fin (m+1))
    (same : ∀ x ∈ S, x.getLsbD p = x.getLsbD q) : g.getLsbD p = g.getLsbD q := by
  apply h (fun _ T => (∀ x ∈ T, x.getLsbD p = x.getLsbD q) → g.getLsbD p = g.getLsbD q) ?_ ?_ same
  · exact fun h => h _ (by simp)
  · intro i a b U s t ne fresh proper ih eq
    apply ih; intro w hw; rcases Finset.mem_insert.mp hw with rfl|old
    · have ea := eq a (by simp); have eb := eq b (by simp); unfold gate canon
      split <;> cases s <;> cases t <;> simp only [signed,Bool.false_eq_true,reduceIte,BitVec.getLsbD_not,BitVec.getLsbD_and,decide_eq_true p.isLt,decide_eq_true q.isLt,ea,eb]
    · exact eq _ (by simp [old])
def sevenPairs (e : Bool) (v : Fin 7) : Fin 128 × Fin 128 :=
  if e then ([(16,17),(8,10),(8,12),(0,64),(2,10),(1,17),(1,33)] : List _).get v
  else ([(16,17),(8,10),(8,12),(1,65),(2,10),(1,17),(1,33)] : List _).get v
theorem exclusive7 : ∀ e (i : Fin 7),
    (pin128 e goal).getLsbD (sevenPairs e i).1 ≠ (pin128 e goal).getLsbD (sevenPairs e i).2 ∧
    ∀ j : Fin 7, (sevenRaw.get j).getLsbD (sevenPairs e i).1 = (sevenRaw.get j).getLsbD (sevenPairs e i).2 ∨ j = i := by decide +kernel
theorem seven_full {e k T} (hp : Path (pin128 e goal) k T) (sub : T ⊆ sevenRaw.toFinset) :
    T = sevenRaw.toFinset := by
  apply Finset.Subset.antisymm sub; intro x hx
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp (List.mem_toFinset.mp hx)
  obtain ⟨distinct,only⟩ := exclusive7 e i; by_contra missing
  apply distinct (path_equal hp _ _ ?_); intro w hw
  obtain ⟨j,rfl⟩ := List.mem_iff_get.mp (List.mem_toFinset.mp (sub hw))
  exact (only j).resolve_right (by rintro rfl; exact missing hw)
theorem to_six {b n} (h : Live b n roots.toFinset) :
    ∃ k, k+3 ≤ b ∧ ∃ T ⊆ cliqueRaw.toFinset, Path cliqueGoal k T := by
  have ok : ∀ v ∈ roots.toFinset, safe v := by
    simp only [List.mem_toFinset,roots,List.mem_cons,List.not_mem_nil,or_false]
    intro v hv; rcases hv with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> unfold safe literal indep <;> decide +kernel
  obtain ⟨e,k,hk,T,sub,hp⟩ := chooseFirst h ok
  have av : avail (pin128 e) roots.toFinset = sevenRaw.toFinset := by cases e <;> decide +kernel
  have ls : lost (pin128 e) roots.toFinset = 1 := by cases e <;> decide +kernel
  rw [av] at sub; rw [seven_full hp sub] at hp
  have geq : sixPin (pin128 e goal) = cliqueGoal := by cases e <;> decide +kernel
  have nz : sixPin (pin128 e goal) ≠ 0 := by rw [geq]; decide
  obtain ⟨j,hj,U,sub6,hr⟩ := second hp nz
  have av6 : avail sixPin sevenRaw.toFinset = cliqueRaw.toFinset := by decide +kernel
  have ls6 : lost sixPin sevenRaw.toFinset = 1 := by decide +kernel
  rw [av6] at sub6; rw [geq] at hr; exact ⟨j,by omega,U,sub6,hr⟩
end PEqualNP.Outside.L_meta_31725.Reduce

namespace PEqualNP.Outside.L_meta_31725.ArchivedClique
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
abbrev Wire := Bool × ℕ
def zero : Wire := (false,0)
def flip (a : Wire) : Wire := (!a.1,a.2)
def combine (d a b : ℕ) : ℕ :=
  match d with
  | 0 => a &&& b
  | 1 => a ||| b
  | 2 => a ^^^ (a &&& b)
  | _ => b ^^^ (a &&& b)
def opIndex (a b : Bool) : ℕ :=
  if a then (if b then 1 else 3) else (if b then 2 else 0)
def meet (a b : Wire) : Wire := (a.1 && b.1,combine (opIndex a.1 b.1) a.2 b.2)
def join (a b : Wire) : Wire := flip (meet (flip a) (flip b))
def read (j : ℕ) (a : Wire) : Bool := a.1 != a.2.testBit j
lemma read_zero (j : ℕ) : read j zero=false := by simp [read,zero]
lemma read_flip (j : ℕ) (a : Wire) : read j (flip a)=!(read j a) := by
  cases a with | mk s a => cases s <;> cases h : a.testBit j <;> simp [read,flip,h]
lemma read_meet (j : ℕ) (a b : Wire) : read j (meet a b) = (read j a && read j b) := by
  obtain ⟨s,a⟩ := a;obtain ⟨t,b⟩ := b
  cases s <;> cases t <;> cases h : a.testBit j <;> cases g : b.testBit j <;>
    simp [read,meet,combine,opIndex,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,h,g]
lemma read_join (j : ℕ) (a b : Wire) : read j (join a b) = (read j a || read j b) := by
  simp only [join,read_flip,read_meet];cases read j a <;> cases read j b <;> rfl

def gate (w : List Wire) (g : Gate) : Wire :=
  let arg := fun i => w.getD i zero
  match g.op,g.inputs with
  | .not, xs => flip (arg (xs.headD w.length))
  | .and, [] => flip zero
  | .or, [] => zero
  | .and, [i] | .or, [i] => arg i
  | .and, i::j::_ => meet (arg i) (arg j)
  | .or, i::j::_ => join (arg i) (arg j)
  | _,_ => zero
def execute (gs : List Gate) (w : List Wire) : List Wire :=
  gs.foldl (fun w g => w++[gate w g]) w
def boolRun (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w++[g.op.eval (g.inputs.map fun i => w.getD i false)]) w
lemma read_get (j : ℕ) (w : List Wire) (i : ℕ) :
    (w.map (read j)).getD i false = read j (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases h : w[i]? with
  | none => exact (read_zero j).symm
  | some a => rfl
lemma gate_read (w : List Wire) (g : Gate) (legal : g.op ∈ ({.and,.or,.not} : Set GateOp) ∧ g.inputs.length ≤ 2) (j : ℕ) :
    read j (gate w g) = g.op.eval (g.inputs.map fun i => (w.map (read j)).getD i false) := by
  simp_rw [read_get]
  obtain ⟨op,xs⟩ := g
  obtain ⟨ops,len⟩ := legal
  change op ∈ ({.and,.or,.not} : Set GateOp) at ops
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ops
  rcases ops with rfl|rfl|rfl <;>
    rcases xs with _|⟨i,_|⟨k,_|⟨h,rest⟩⟩⟩ <;>
    simp_all [gate,GateOp.eval,read_flip,read_meet,read_join,read_get,read_zero,List.getD_eq_default]
lemma execute_read (j : ℕ) (gs : List Gate) (w : List Wire) (legal : ∀ g ∈ gs,
    g.op ∈ ({.and,.or,.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    (execute gs w).map (read j) = boolRun gs (w.map (read j)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w++[gate w g])).map (read j) = boolRun gs (_++[_])
    rw [ih _ (fun v hv => legal v (.tail _ hv))]
    simp [gate_read w g (legal g List.mem_cons_self) j]

def counted (g : Gate) : Bool := match g.op with | .not => false | _ => true
def reps (w : List Wire) := w.map Prod.snd
def simple (w : List Wire) (z : ℕ) := z=0 ∨ z∈reps w
def priced (w : List Wire) (paid : Bool) (z : ℕ) := simple w z ∨
    (paid = true ∧ ∃ d < 4, ∃ a ∈ reps w, ∃ b ∈ reps w, a≠0 ∧ b≠0 ∧ a≠b ∧ z=combine d a b)
lemma get_simple (w : List Wire) (i : ℕ) : simple w (w.getD i zero).2 := by
  simp only [List.getD_eq_getElem?_getD]
  cases eq : w[i]? with
  | none => exact Or.inl rfl
  | some a => exact Or.inr (List.mem_map.mpr ⟨a,List.mem_of_getElem? eq,rfl⟩)
lemma combine_eq_cases (d a b : ℕ) (hd : d<4) (h : a=0 ∨ b=0 ∨ a=b) :
    combine d a b=0 ∨ combine d a b=a ∨ combine d a b=b := by
  rcases h with h|h|h <;> subst_vars <;> interval_cases d <;> simp [combine]
lemma made (w : List Wire) (d : ℕ) (a b : Wire) (hd : d<4) (pa : simple w a.2) (pb : simple w b.2) :
    priced w true (combine d a.2 b.2) := by
  by_cases h : a.2=0 ∨ b.2=0 ∨ a.2=b.2
  · rcases combine_eq_cases _ _ _ hd h with e|e|e
    · exact Or.inl (Or.inl e)
    · apply Or.inl; rw [e]; exact pa
    · apply Or.inl; rw [e]; exact pb
  · push Not at h
    exact Or.inr ⟨rfl,d,hd,a.2,pa.resolve_left h.1,b.2,pb.resolve_left h.2.1,h.1,h.2.1,h.2.2,rfl⟩
lemma op_lt (s t : Bool) : opIndex s t < 4 := by cases s <;> cases t <;> decide
lemma gate_priced (w : List Wire) (g : Gate) : priced w (counted g) (gate w g).2 := by
  obtain ⟨op,xs⟩ := g
  cases op with
  | and =>
    rcases xs with _|⟨i,_|⟨j,t⟩⟩
    · exact Or.inl (Or.inl rfl)
    · exact Or.inl (get_simple w i)
    · exact made w _ _ _ (op_lt _ _) (get_simple w i) (get_simple w j)
  | or =>
    rcases xs with _|⟨i,_|⟨j,t⟩⟩
    · exact Or.inl (Or.inl rfl)
    · exact Or.inl (get_simple w i)
    · exact made w _ _ _ (op_lt _ _) (get_simple w i) (get_simple w j)
  | mod _ | maj => exact Or.inl (Or.inl rfl)
  | _ => exact Or.inl (get_simple w _)

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def Good (m a : ℕ) := ∀ i<m, a.testBit i ≠ a.testBit (m+i)

def Live (m : ℕ) : ℕ → Finset ℕ → Prop
  | 0, S => ∃ a, S = {a} ∧ Good m a ∧ a ≠ 0
  | k+1, S => ∃ (U : Finset ℕ) (a b d : ℕ),
      S = insert a (insert b U) ∧
      d < 4 ∧ a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b ∧
      combine d a b ∉ insert a (insert b U) ∧
      Live m k (insert (combine d a b) U)

namespace Live

lemma done {m a : ℕ} (hg : Good m a) (nonzero : a ≠ 0) : Live m 0 {a} := by
  rw [Live]
  exact ⟨a, rfl, hg, nonzero⟩

lemma step {m k : ℕ} {U : Finset ℕ} {a b d : ℕ}
    (hd : d < 4) (ha : a ≠ 0) (hb : b ≠ 0) (diff : a ≠ b)
    (fresh : combine d a b ∉ insert a (insert b U))
    (next : Live m k (insert (combine d a b) U)) :
    Live m (k+1) (insert a (insert b U)) := by
  rw [Live]
  exact ⟨U, a, b, d, rfl, hd, ha, hb, diff, fresh, next⟩

end Live

lemma liveNonzero {m k S} (h : Live m k S) : ∀ a∈S,a≠0 := by
  induction k generalizing S with
  | zero =>
    rw [Live] at h
    obtain ⟨a, rfl, _, hn⟩ := h
    simpa using hn
  | succ k ih =>
    rw [Live] at h
    obtain ⟨U, a, b, d, rfl, _, ha, hb, _, _, tail⟩ := h
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl|hx
    · exact ha
    rcases Finset.mem_insert.mp hx with rfl|hx
    · exact hb
    exact ih tail x (Finset.mem_insert_of_mem hx)
lemma liveSize {m k S} (h : Live m k S) : S.card≤k+1 := by
  induction k generalizing S with
  | zero =>
    rw [Live] at h
    obtain ⟨a, rfl, _, _⟩ := h
    simp
  | succ k ih =>
    rw [Live] at h
    obtain ⟨U, a, b, d, rfl, _, _, _, _, fresh, tail⟩ := h
    have bound := ih tail
    have z : combine d a b ∉ U := fun m => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem m))
    rw [Finset.card_insert_of_notMem z] at bound
    have u := Finset.card_insert_le a (insert b U)
    have v := Finset.card_insert_le b U
    omega
lemma combine_congr_bits (d a b i j : ℕ) (p : a.testBit i=a.testBit j) (q : b.testBit i=b.testBit j) :
    (combine d a b).testBit i=(combine d a b).testBit j := by
  rcases d with _|(_|(_|d)) <;> simp [combine,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,p,q]
lemma liveSeparates {m k S} (h : Live m k S) (i : ℕ) (hi : i<m) :
    ∃ a∈S,a.testBit i≠a.testBit (m+i) := by
  induction k generalizing S with
  | zero =>
    rw [Live] at h
    obtain ⟨a, rfl, hg, _⟩ := h
    exact ⟨a, Finset.mem_singleton_self a, hg i hi⟩
  | succ k ih =>
    rw [Live] at h
    obtain ⟨U, a, b, d, rfl, _, _, _, _, _, tail⟩ := h
    obtain ⟨x,hx,dist⟩ := ih tail
    rcases Finset.mem_insert.mp hx with rfl|hx
    · by_cases v : a.testBit i=a.testBit (m+i)
      · exact ⟨b,Finset.mem_insert_of_mem (Finset.mem_insert_self _ _),fun u => dist (combine_congr_bits _ _ _ _ _ v u)⟩
      · exact ⟨a,Finset.mem_insert_self _ _,v⟩
    · exact ⟨x,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx),dist⟩

lemma pull {m k S w z p} (h : Live m k S) (op : priced w p z)
    (sub : ∀ a∈S, a∈reps w ++ [z]) :
    ∃ l T, l ≤ k + p.toNat ∧ Live m l T ∧ ∀ a∈T, a∈reps w := by
  by_cases needed : z∈S
  · by_cases available : z∈reps w
    · refine ⟨k,S,by omega,h,?_⟩
      intro a ha
      rcases (by simpa using sub a ha : a∈reps w ∨ a=z) with old|rfl
      · exact old
      · exact available
    · rcases op with easy|⟨rfl,d,hd,a,xa,b,xb,na,nb,ab,rfl⟩
      · rcases easy with e|e
        · exact ((liveNonzero h z needed) e).elim
        · exact (available e).elim
      · let g := combine d a b
        let U := S.erase g
        have tail : Live m k (insert g U) := by change Live m k (insert g (S.erase g)); rw [Finset.insert_erase (show g∈S from needed)]; exact h
        have old (x : ℕ) (hx : x∈U) : x∈reps w := by
          obtain ⟨ne,mem⟩ := Finset.mem_erase.mp hx
          have h' : x∈reps w ∨ x=g := by simpa using sub x mem
          exact h'.resolve_right ne
        have fresh : g ∉ insert a (insert b U) := by
          intro eq
          rcases Finset.mem_insert.mp eq with e|h'
          · exact available (show g∈reps w by rw [e];exact xa)
          rcases Finset.mem_insert.mp h' with e|u
          · exact available (show g∈reps w by rw [e];exact xb)
          · exact available (old _ u)
        refine ⟨k+1,insert a (insert b U),by simp,Live.step hd na nb ab fresh tail,?_⟩
        simpa using And.intro xa (And.intro xb old)
  · refine ⟨k,S,by omega,h,?_⟩
    intro a ha
    have ne : a≠z := fun e => needed (e ▸ ha)
    simpa [ne] using sub a ha

lemma extract {m out} (hg : Good m out) (hn : out≠0) (gs : List Gate) (w : List Wire)
    (found : out∈reps (execute gs w)) :
    ∃ k S, k≤gs.countP counted ∧ Live m k S ∧ ∀ a∈S, a∈reps w := by
  induction gs generalizing w with
  | nil => exact ⟨0,{out},by simp,Live.done hg hn,by simpa [execute] using found⟩
  | cons g gs ih =>
    obtain ⟨k,S,lim,h,sub⟩ := ih (w++[gate w g]) found
    have sub' : ∀ a∈S,a∈reps w ++ [(gate w g).2] := by simpa [reps] using sub
    obtain ⟨l,T,cost,ht,raw⟩ := pull h (gate_priced w g) sub'
    refine ⟨l,T,?_,ht,raw⟩
    cases e : counted g <;> simp [e,Bool.toNat] at cost ⊢ <;> omega
def separation (m a : ℕ) := a ^^^ (a >>> m)
def cover (m : ℕ) : List ℕ → ℕ
  | [] => 0
  | a::t => separation m a ||| cover m t
def full (m : ℕ) := (1 <<< m)-1
def enough (m c : ℕ) := (c &&& full m) == full m
lemma coverBit (m i : ℕ) (v : List ℕ) : (cover m v).testBit i=true ↔
    ∃ a∈v,a.testBit i≠a.testBit (m+i) := by
  induction v with
  | nil => simp [cover]
  | cons a t ih =>
    simp only [cover,Nat.testBit_or,Bool.or_eq_true,ih,List.mem_cons,separation,Nat.testBit_xor,Nat.testBit_shiftRight]
    cases v1 : a.testBit i <;> cases v2 : a.testBit (m+i) <;> simp [v1,v2] <;> aesop
lemma enoughLive {m k S} (h : Live m k S) (v : List ℕ) (rep : v.toFinset=S) : enough m (cover m v)=true := by
  apply beq_iff_eq.mpr
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  have bit : (full m).testBit i=decide (i<m) := by simp [full,Nat.shiftLeft_eq,Nat.testBit_two_pow_sub_one]
  by_cases hi : i<m
  · have ⟨x,hx,good⟩ := liveSeparates h i hi
    have xc : x∈v := List.mem_toFinset.mp (rep ▸ hx)
    have mark := (coverBit m i v).2 ⟨x,xc,good⟩
    simp [mark,bit,hi]
  · simp [bit,hi]

def save (keep : Bool) (a : ℕ) (rest : List ℕ) := if keep then a::rest else rest
def without (v : List ℕ) (a b : ℕ) := v.filter (fun x => x != a && x != b)
def optionStep (m fuel : ℕ) (go : List ℕ → Bool) (rest : List ℕ) (n cv a b z : ℕ) (ka kb : Bool) : Bool :=
  let len := 1+n+ka.toNat+kb.toNat
  len ≤ fuel+1 && enough m (((separation m z ||| cv) ||| (if ka then separation m a else 0)) |||
    (if kb then separation m b else 0)) && go (z::save ka a (save kb b rest))
def gateStep (m fuel : ℕ) (go : List ℕ → Bool) (v rest : List ℕ) (n cv a b z : ℕ) : Bool :=
  z != 0 && !(v.contains z) &&
  (optionStep m fuel go rest n cv a b z false false || optionStep m fuel go rest n cv a b z true false ||
   optionStep m fuel go rest n cv a b z false true || optionStep m fuel go rest n cv a b z true true)
def pairStep (m fuel : ℕ) (go : List ℕ → Bool) (v : List ℕ) (a b : ℕ) : Bool :=
  if a<b then
    let rest := without v a b
    let check := gateStep m fuel go v rest rest.length (cover m rest) a b
    check (a &&& b) || check (a ||| b) || check (a ^^^ (a &&& b)) || check (b ^^^ (a &&& b))
  else false
def anyGate (m fuel : ℕ) (go : List ℕ → Bool) (v : List ℕ) : Bool :=
  v.any (fun a => v.any (fun b => pairStep m fuel go v a b))
def terminal (m : ℕ) (v : List ℕ) := v.any (fun a => enough m (separation m a))
def search (m : ℕ) : ℕ → List ℕ → Bool
  | 0, v => terminal m v
  | fuel+1, v => terminal m v || anyGate m fuel (search m fuel) v

lemma surface (m a i : ℕ) : (separation m a).testBit i=true ↔ a.testBit i≠a.testBit (m+i) := by
  simp only [separation,Nat.testBit_xor,Nat.testBit_shiftRight]
  cases a.testBit i <;> cases a.testBit (m+i) <;> decide
lemma ends {m a} (h : Good m a) (v : List ℕ) (mem : a∈v) : terminal m v=true := by
  apply List.any_eq_true.mpr;refine ⟨a,mem,?_⟩
  apply beq_iff_eq.mpr;apply Nat.eq_of_testBit_eq;intro i;rw [Nat.testBit_and]
  have e : (full m).testBit i=decide (i<m) := by simp [full,Nat.shiftLeft_eq,Nat.testBit_two_pow_sub_one]
  by_cases l : i<m
  · simp [e,l,(surface _ _ _).2 (h i l)]
  · simp [e,l]
lemma option_ok {m fuel go rest a b z ka kb} (lim : (z::save ka a (save kb b rest)).length≤fuel+1)
    (cov : enough m (cover m (z::save ka a (save kb b rest)))=true)
    (next : go (z::save ka a (save kb b rest))=true) :
    optionStep m fuel go rest rest.length (cover m rest) a b z ka kb=true := by
  have size : 1+rest.length+ka.toNat+kb.toNat≤fuel+1 := by
    cases ka <;> cases kb <;> simp [save,Bool.toNat] at lim ⊢ <;> omega
  have eq : enough m (((separation m z ||| cover m rest) ||| (if ka then separation m a else 0)) ||| (if kb then separation m b else 0))=true := by
    cases ka <;> cases kb <;> simpa [save,cover,Nat.or_assoc,Nat.or_left_comm,Nat.or_comm] using cov
  simp [optionStep,size,eq,next]
lemma gate_ok {m fuel go v rest n cv a b z ka kb} (nz : z≠0) (fresh : z∉v)
    (which : optionStep m fuel go rest n cv a b z ka kb=true) :
    gateStep m fuel go v rest n cv a b z=true := by
  cases ka <;> cases kb <;> simp [gateStep,nz,fresh,which]
lemma pair_ok {m fuel go v a b d} (ordered : a<b) (hd : d<4)
    (step : let rest := without v a b;gateStep m fuel go v rest rest.length (cover m rest) a b (combine d a b)=true) :
    pairStep m fuel go v a b=true := by
  interval_cases d <;> simp only [combine] at step <;> simp [pairStep,ordered,step]
lemma swapOp (d a b : ℕ) (hd : d<4) : ∃ e<4,combine d a b=combine e b a := by
  interval_cases d
  · exact ⟨0,by decide,Nat.and_comm a b⟩
  · exact ⟨1,by decide,Nat.or_comm a b⟩
  · exact ⟨3,by decide,by simp [combine,Nat.and_comm]⟩
  · exact ⟨2,by decide,by simp [combine,Nat.and_comm]⟩
lemma listNext {v : List ℕ} {a b z : ℕ} {U : Finset ℕ} (rep : v.toFinset=insert a (insert b U))
    (ab : a≠b) (fz : z∉insert a (insert b U)) (nd : v.Nodup) :
    let rest := without v a b
    let next := z::save (decide (a∈U)) a (save (decide (b∈U)) b rest)
    next.toFinset=insert z U ∧ next.Nodup := by
  dsimp only
  have mem (x : ℕ) : x∈without v a b ↔ x∈U ∧ x≠a ∧ x≠b := by
    simp only [without,List.mem_filter,Bool.and_eq_true,bne_iff_ne]
    have e : x∈v ↔ x=a ∨ x=b ∨ x∈U := by rw [← List.mem_toFinset,rep];simp
    tauto
  have nr := nd.filter (fun x => x != a && x != b)
  change (without v a b).Nodup at nr
  have md (x : ℕ) : (x∈save (decide (a∈U)) a (save (decide (b∈U)) b (without v a b))) ↔ x∈U := by
    by_cases xa : x=a
    · subst x; by_cases ka : a∈U <;> by_cases kb : b∈U <;> simp [save,ka,kb,mem,ab]
    by_cases xb : x=b
    · subst x; by_cases ka : a∈U <;> by_cases kb : b∈U <;> simp [save,ka,kb,mem,Ne.symm ab]
    by_cases ka : a∈U <;> by_cases kb : b∈U <;> simp [save,ka,kb,mem,xa,xb]
  constructor
  · ext x;simp [md]
  · simp only [List.nodup_cons,md]
    refine ⟨fun m => fz (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem m)),?_⟩
    have an : a∉without v a b := fun x => (mem _).1 x |>.2.1 rfl
    have bn : b∉without v a b := fun x => (mem _).1 x |>.2.2 rfl
    by_cases ka : a∈U <;> by_cases kb : b∈U <;> simp [save,ka,kb,nr,ab,an,bn]
lemma orderedStep {m fuel n U a b d v} {go : List ℕ→Bool} (hd : d<4)
    (lt : a<b) (nz : combine d a b≠0) (fresh : combine d a b∉insert a (insert b U))
    (rep : List.toFinset v=insert a (insert b U)) (nd : v.Nodup) (lim : n≤fuel)
    (tail : Live m n (insert (combine d a b) U))
    (nextOK : ∀ v : List ℕ, v.toFinset=insert (combine d a b) U → v.Nodup → go v=true) :
    pairStep m fuel go v a b=true := by
  let z := combine d a b
  let rest := without v a b
  let next := z::save (decide (a∈U)) a (save (decide (b∈U)) b rest)
  obtain ⟨r,nu⟩ := listNext (z:=z) rep (Nat.ne_of_lt lt) fresh nd
  have small := liveSize tail
  change (insert z U).card≤n+1 at small
  have length : next.length=(insert z U).card := by rw [←r,List.toFinset_card_of_nodup nu]
  have bound : next.length≤fuel+1 := by omega
  have coverOK := enoughLive tail next r
  have ok := option_ok bound coverOK (nextOK next r nu)
  apply pair_ok lt hd
  exact gate_ok nz (fun h => fresh (rep ▸ List.mem_toFinset.mpr h)) ok
lemma transition {m fuel n U a b d v} {go : List ℕ→Bool} (hd : d<4)
    (ab : a≠b) (fresh : combine d a b∉insert a (insert b U))
    (rep : List.toFinset v=insert a (insert b U)) (nd : v.Nodup) (lim : n≤fuel)
    (tail : Live m n (insert (combine d a b) U))
    (nextOK : ∀ v : List ℕ, v.toFinset=insert (combine d a b) U → v.Nodup → go v=true) :
    anyGate m fuel go v=true := by
  have ma : a∈v := List.mem_toFinset.mp (rep ▸ Finset.mem_insert_self _ _)
  have mb : b∈v := List.mem_toFinset.mp (rep ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have nz := liveNonzero tail _ (Finset.mem_insert_self _ _)
  rcases lt_or_gt_of_ne ab with lt|gt
  · exact List.any_eq_true.mpr ⟨a,ma,List.any_eq_true.mpr ⟨b,mb,orderedStep hd lt nz fresh rep nd lim tail nextOK⟩⟩
  · obtain ⟨e,he,eq⟩ := swapOp d a b hd
    have rev : insert a (insert b U)=insert b (insert a U) := Finset.insert_comm a b U
    rw [rev] at fresh rep
    rw [eq] at fresh nz tail nextOK
    exact List.any_eq_true.mpr ⟨b,mb,List.any_eq_true.mpr ⟨a,ma,orderedStep he gt nz fresh rep nd lim tail nextOK⟩⟩

theorem complete (m fuel : ℕ) {n S} (h : Live m n S) (lim : n≤fuel)
    (v : List ℕ) (rep : v.toFinset=S) (nd : v.Nodup) : search m fuel v=true := by
  induction fuel generalizing n S v with
  | zero =>
    cases n with
    | zero =>
      rw [Live] at h
      obtain ⟨a, rfl, hg, _⟩ := h
      exact ends hg v (List.mem_toFinset.mp (rep ▸ Finset.mem_singleton_self a))
    | succ n => omega
  | succ k ih =>
    rw [search,Bool.or_eq_true]
    cases n with
    | zero =>
      rw [Live] at h
      obtain ⟨a, rfl, hg, _⟩ := h
      exact Or.inl (ends hg v (List.mem_toFinset.mp (rep ▸ Finset.mem_singleton_self a)))
    | succ n =>
      rw [Live] at h
      obtain ⟨U, a, b, d, rfl, hd, _, _, ab, fresh, tail⟩ := h
      exact Or.inr (transition hd ab fresh rep nd (by omega) tail (fun v hv nv => ih tail (by omega) v hv nv))

abbrev Projection (m h : ℕ) := { f : ℕ → ℕ //
  f 0 = 0 ∧ (∀ d a b, d < 4 → f (combine d a b) = combine d (f a) (f b)) ∧
  (∀ a, Good m a → Good h (f a)) ∧ 0 < h }

namespace Projection
def toFun {m h : ℕ} (p : Projection m h) : ℕ → ℕ := p.val
theorem atZero {m h : ℕ} (p : Projection m h) : p.toFun 0 = 0 := p.property.1
theorem combineEq {m h : ℕ} (p : Projection m h) (d a b : ℕ) (hd : d < 4) :
    p.toFun (combine d a b) = combine d (p.toFun a) (p.toFun b) :=
  p.property.2.1 d a b hd
theorem good {m h : ℕ} (p : Projection m h) (a : ℕ) (ha : Good m a) :
    Good h (p.toFun a) := p.property.2.2.1 a ha
theorem someRow {m h : ℕ} (p : Projection m h) : 0 < h := p.property.2.2.2
end Projection

def Possible (m k : ℕ) (av : List ℕ) :=
  ∃ j S, j≤k ∧ Live m j S ∧ ∀ x∈S,x∈av
def charge (av : List ℕ) (z : ℕ) := z != 0 && !(av.contains z)
lemma pullPaid {m k d a b : ℕ} {av : List ℕ} (hd : d<4) (ha : a∈av) (hb : b∈av)
    (later : Possible m k (av++[combine d a b])) :
    Possible m (k+(charge av (combine d a b)).toNat) av := by
  let w := av.map (fun x => (false,x))
  have repr : reps w=av := by simp [w,reps,List.map_map,Function.comp_def]
  obtain ⟨j,S,lim,live,sub⟩ := later
  have needed : ∀ x∈S,x∈reps w++[combine d a b] := by simpa [repr] using sub
  have price : priced w (charge av (combine d a b)) (combine d a b) := by
    by_cases nz : combine d a b=0
    · exact Or.inl (Or.inl nz)
    by_cases old : combine d a b∈av
    · exact Or.inl (Or.inr (repr ▸ old))
    have paid : charge av (combine d a b)=true := by simp [charge,nz,old]
    have special : ¬(a=0 ∨ b=0 ∨ a=b) := by
      intro h
      rcases combine_eq_cases _ _ _ hd h with zero|rfl'|rfl'
      · exact nz zero
      · exact old (by rw [rfl'];exact ha)
      · exact old (by rw [rfl'];exact hb)
    exact Or.inr ⟨paid,d,hd,a,repr ▸ ha,b,repr ▸ hb,
      fun x => special (Or.inl x),fun x => special (Or.inr (Or.inl x)),fun x => special (Or.inr (Or.inr x)),rfl⟩
  obtain ⟨l,T,le,ok,sub'⟩ := pull live price needed
  exact ⟨l,T,by omega,ok,by simpa [repr] using sub'⟩

def dead (p : ℕ→ℕ) (S : Finset ℕ) := (S.filter (fun x => p x=0)).card
lemma deadStay {p : ℕ→ℕ} {a : ℕ} {S : Finset ℕ} (h : p a≠0) : dead p (insert a S)=dead p S := by
  simp [dead,Finset.filter_insert,h]
lemma deadLimit (p : ℕ→ℕ) (a : ℕ) (S : Finset ℕ) : dead p (insert a S)≤dead p S+1 := by
  by_cases x : p a=0
  · simpa [dead,Finset.filter_insert,x] using Finset.card_insert_le a (S.filter (fun x => p x=0))
  · simp [deadStay x]
lemma deadMono (p : ℕ→ℕ) (a : ℕ) (S : Finset ℕ) : dead p S ≤ dead p (insert a S) := by
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_insert _ _))
lemma deadGrow {p : ℕ→ℕ} {a : ℕ} {S : Finset ℕ} (z : p a=0) (fresh : a∉S) :
    dead p (insert a S)=dead p S+1 := by
  have nf : a∉S.filter (fun x => p x=0) := fun h => fresh (Finset.mem_filter.mp h).1
  simp [dead,Finset.filter_insert,z,Finset.card_insert_of_notMem nf]
lemma countCharge {m h d a b : ℕ} (p : Projection m h) (hd : d<4) (U : Finset ℕ)
    (fz : combine d a b∉insert a (insert b U)) (av : List ℕ) (ma : p.toFun a∈av) (mb : p.toFun b∈av) :
    (charge av (p.toFun (combine d a b))).toNat + dead p.toFun (insert a (insert b U)) ≤
      1+dead p.toFun (insert (combine d a b) U) := by
  have up := deadMono p.toFun (combine d a b) U
  have la := deadLimit p.toFun a (insert b U)
  have lb := deadLimit p.toFun b U
  have free (bad : p.toFun a=0 ∨ p.toFun b=0) : charge av (p.toFun (combine d a b))=false := by
    rw [p.combineEq _ _ _ hd]
    rcases combine_eq_cases _ _ _ hd (bad.imp_right Or.inl) with e|e|e <;> simp [charge,e,ma,mb]
  by_cases az : p.toFun a=0
  · rw [free (Or.inl az)];simp only [Bool.toNat_false,Nat.zero_add]
    by_cases bz : p.toFun b=0
    · have zz : p.toFun (combine d a b)=0 := by
        rw [p.combineEq _ _ _ hd,az,bz];interval_cases d <;> decide
      have fresh : combine d a b∉U := fun m => fz (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem m))
      rw [deadGrow zz fresh];omega
    · rw [deadStay bz] at la;omega
  · rw [deadStay az]
    by_cases bz : p.toFun b=0
    · rw [free (Or.inr bz)];simp only [Bool.toNat_false,Nat.zero_add];omega
    · rw [deadStay bz];cases charge av (p.toFun (combine d a b)) <;> simp [Bool.toNat] <;> omega

theorem projectLive {m h k S} (p : Projection m h) (live : Live m k S) :
    ∃ j T,j+dead p.toFun S≤k ∧ Live h j T ∧ ∀ x∈T,x∈S.image p.toFun := by
  induction k generalizing S with
  | zero =>
    rw [Live] at live
    obtain ⟨a, rfl, hg, _⟩ := live
    have gp := p.good a hg
    have nz : p.toFun a≠0 := by intro e;have x := gp 0 p.someRow;simp [e] at x
    exact ⟨0,{p.toFun a},by simp [dead,nz],Live.done gp nz,by simp⟩
  | succ k ih =>
    rw [Live] at live
    obtain ⟨U, a, b, d, rfl, hd, ha, hb, ab, fz, tail⟩ := live
    obtain ⟨j,T,cost,ok,raw⟩ := ih tail
    let av := ((insert a (insert b U)).image p.toFun).toList
    have ma : p.toFun a∈av := by simp [av]
    have mb : p.toFun b∈av := by simp [av]
    have later : Possible h j (av++[combine d (p.toFun a) (p.toFun b)]) := by
      refine ⟨j,T,le_rfl,ok,?_⟩
      intro z hz
      have has := raw _ hz
      simp only [Finset.image_insert,Finset.mem_insert] at has
      rcases has with rfl|old
      · simp [p.combineEq d a b hd]
      · have inav : z∈av := by simpa [av] using (Or.inr (Or.inr old) : z=p.toFun a ∨ z=p.toFun b ∨ z∈U.image p.toFun)
        simp [inav]
    obtain ⟨l,V,lim,good,sub⟩ := pullPaid hd ma mb later
    rw [←p.combineEq d a b hd] at lim
    have bound := countCharge p hd U fz av ma mb
    exact ⟨l,V,by omega,good,by simpa [av] using sub⟩

lemma full_bit (m i : ℕ) : (full m).testBit i=decide (i<m) := by
  simp [full,Nat.shiftLeft_eq,Nat.testBit_two_pow_sub_one]

lemma enoughSup {m k S} (h : Live m k S) (v : List ℕ) (sub : ∀ x∈S,x∈v) : enough m (cover m v)=true := by
  apply beq_iff_eq.mpr;apply Nat.eq_of_testBit_eq;intro i
  rw [Nat.testBit_and,full_bit]
  by_cases hi : i<m
  · obtain ⟨x,hx,g⟩ := liveSeparates h i hi
    have bit := (coverBit m i v).2 ⟨x,sub _ hx,g⟩
    simp [bit,hi]
  · simp [hi]
def start (m fuel : ℕ) (av : List ℕ) :=
  let v := av.eraseDups.filter (fun x => x != 0)
  let needed := fun a => !(enough m (cover m (v.filter (fun x => x != a))))
  let must := v.filter needed
  let extra := v.filter (fun x => !needed x)
  extra.sublists.any (fun t =>
    let s := (must++t).dedup
    s.length≤fuel+1 && enough m (cover m s) && search m fuel s)

theorem start_complete {m k S} (h : Live m k S) (av : List ℕ) (sub : ∀ x∈S,x∈av)
    (fuel : ℕ) (lim : k≤fuel) : start m fuel av=true := by
  let v := av.eraseDups.filter (fun x => x != 0)
  let needed := fun a => !(enough m (cover m (v.filter (fun x => x != a))))
  let must := v.filter needed
  let extra := v.filter (fun x => !needed x)
  let t := extra.filter (fun x => decide (x∈S))
  let s := (must++t).dedup
  have inV (x : ℕ) (hx : x∈S) : x∈v := by simp [v,sub x hx,liveNonzero h x hx]
  have fixed (a : ℕ) (ha : a∈must) : a∈S := by
    by_contra absent
    have no := (List.mem_filter.mp ha).2
    have all (x : ℕ) (hx : x∈S) : x∈v.filter (fun y => y != a) := by
      have ne : x≠a := by rintro rfl;exact absent hx
      simp [inV x hx,ne]
    have yes := enoughSup h _ all
    simpa [needed,yes] using no
  have eq : s.toFinset=S := by
    ext x
    constructor
    · intro mem
      have e : x∈must ∨ x∈t := by simpa [s] using mem
      rcases e with l|r
      · exact fixed x l
      · simpa using (List.mem_filter.mp r).2
    · intro mem
      have raw := inV x mem
      cases H : needed x <;> simp [s,must,t,extra,H,raw,mem]
  have nd : s.Nodup := List.nodup_dedup _
  have size : s.length≤fuel+1 := by
    have vsize := liveSize h
    rw [←eq,List.toFinset_card_of_nodup nd] at vsize;omega
  have test := complete m fuel h lim s eq nd
  have cov := enoughLive h s eq
  apply List.any_eq_true.mpr
  refine ⟨t,List.mem_sublists.mpr (List.filter_sublist),?_⟩
  change (decide (s.length≤fuel+1) && enough m (cover m s) && search m fuel s)=true
  simp [size,cov,test]

def actL : List ℕ → ℕ → ℕ
  | [], _ => 0
  | p :: ps, w => Nat.bit (w.testBit p) (actL ps w)

theorem actL_testBit : ∀ (pi : List ℕ) (w k : ℕ),
    (actL pi w).testBit k = (pi[k]?.map w.testBit).getD false
  | [], w, k => by simp [actL]
  | p :: ps, w, 0 => by simp [actL, Nat.testBit_bit_zero]
  | p :: ps, w, k + 1 => by simp [actL, Nat.testBit_bit_succ, actL_testBit ps w k]

theorem actL_and (pi : List ℕ) (a b : ℕ) : actL pi (a &&& b) = actL pi a &&& actL pi b := by
  apply Nat.eq_of_testBit_eq; intro k
  rw [Nat.testBit_and, actL_testBit, actL_testBit, actL_testBit]
  cases pi[k]? <;> simp [Nat.testBit_and]

theorem actL_or (pi : List ℕ) (a b : ℕ) : actL pi (a ||| b) = actL pi a ||| actL pi b := by
  apply Nat.eq_of_testBit_eq; intro k
  rw [Nat.testBit_or, actL_testBit, actL_testBit, actL_testBit]
  cases pi[k]? <;> simp [Nat.testBit_or]

theorem actL_xor (pi : List ℕ) (a b : ℕ) : actL pi (a ^^^ b) = actL pi a ^^^ actL pi b := by
  apply Nat.eq_of_testBit_eq; intro k
  rw [Nat.testBit_xor, actL_testBit, actL_testBit, actL_testBit]
  cases pi[k]? <;> simp [Nat.testBit_xor]

def coord (m : ℕ) (r : List ℕ) := actL (r ++ r.map (m+·))

theorem coordC (m : ℕ) (r : List ℕ) (d a b : ℕ) (hd : d < 4) :
    coord m r (combine d a b) = combine d (coord m r a) (coord m r b) := by
  interval_cases d <;> simp [combine,coord,actL_and,actL_or,actL_xor]

def pick {m h : ℕ} (r : List ℕ) (len : r.length=h) (small : ∀ i∈r,i<m) (pos : 0<h) : Projection m h := by
  refine ⟨coord m r, ?_, coordC m r, ?_, pos⟩
  · apply Nat.eq_of_testBit_eq
    intro i
    simp only [coord,actL_testBit,Nat.zero_testBit]
    cases (r ++ r.map (m+·))[i]? <;> simp
  · intro a ha i hi
    have ir : i<r.length := by omega
    have b := ha r[i] (small _ (List.getElem_mem ir))
    have H₁ : (r ++ r.map (m+·))[i]? = some r[i] := by simp [List.getElem?_append,ir]
    have H₂ : (r ++ r.map (m+·))[h+i]? = some (m+r[i]) := by
      have ne : ¬h+i<r.length := by omega
      have sub : h+i-r.length=i := by omega
      simp [List.getElem?_append,ne,sub,ir]
    simpa [coord,actL_testBit,H₁,H₂] using b

def Ban (m fuel : ℕ) (v : List ℕ) := ∀ n, n ≤ fuel → ¬Live m n v.toFinset
def Wide (m fuel : ℕ) (v : List ℕ) := ¬Possible m fuel v

theorem viaSearch {m fuel v} (test : start m fuel v=false) : Wide m fuel v := by
  rintro ⟨k,S,le,live,sub⟩
  have := start_complete live v sub fuel le
  simp_all

theorem viaCut {m h f t : ℕ} {v w : List ℕ} (p : Projection m h)
    (bound : Wide h t w) (nd : v.Nodup)
    (mem : ∀ a∈v, p.toFun a=0 ∨ p.toFun a∈w)
    (cost : f≤t+(v.map p.toFun).count 0) : Ban m f v := by
  intro k lim run
  obtain ⟨j,T,c,ok,incl⟩ := projectLive p run
  have fixed : dead p.toFun v.toFinset=(v.map p.toFun).count 0 := by
    dsimp [dead]
    have E : v.toFinset.filter (fun x => p.toFun x=0) = (v.filter (fun x => decide (p.toFun x=0))).toFinset := by ext x;simp
    rw [E,List.toFinset_card_of_nodup (nd.filter _)]
    simp only [List.count_eq_countP,List.countP_map,Function.comp_apply]
    rw [List.countP_eq_length_filter]
    congr 2
  rw [fixed] at c
  apply bound
  refine ⟨j,T,by omega,ok,?_⟩
  intro x hx
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp (incl _ hx)
  exact (mem y (List.mem_toFinset.mp hy)).resolve_left (liveNonzero ok _ hx)

theorem renameLive {m h k S} (p : Projection m h) (q : Projection h m)
    (run : Live m k S) (rec : ∀ x∈S, q.toFun (p.toFun x)=x) : Live h k (S.image p.toFun) := by
  induction k generalizing S with
  | zero =>
    rw [Live] at run
    obtain ⟨a,rfl,good,nz⟩ := run
    simp only [Finset.image_singleton]
    apply Live.done (p.good a good)
    intro e
    have := rec a (Finset.mem_singleton_self a)
    rw [e,q.atZero] at this
    exact nz this.symm
  | succ k ih =>
    rw [Live] at run
    obtain ⟨U,a,b,d,rfl,hd,ha,hb,ab,fr,tail⟩ := run
    let z := combine d a b
    have ra := rec a (Finset.mem_insert_self _ _)
    have rb := rec b (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have rz : q.toFun (p.toFun z)=z := by simp only [z,p.combineEq _ _ _ hd,q.combineEq _ _ _ hd,ra,rb]
    have ru (x) (hx : x∈U) := rec x (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx))
    have nr := ih tail (by intro x hx; rcases Finset.mem_insert.mp hx with rfl|h; exact rz; exact ru _ h)
    have eqz : p.toFun z=combine d (p.toFun a) (p.toFun b) := p.combineEq _ _ _ hd
    simp only [Finset.image_insert] at nr ⊢
    apply Live.step hd
    · intro e;rw [e,q.atZero] at ra;exact ha ra.symm
    · intro e;rw [e,q.atZero] at rb;exact hb rb.symm
    · intro e;rw [e,rb] at ra;exact ab ra.symm
    · rw [←eqz]
      intro bad
      rcases Finset.mem_insert.mp bad with e|bad
      · have hza := congrArg q.toFun e
        rw [rz,ra] at hza
        exact fr (Finset.mem_insert.mpr (Or.inl hza))
      rcases Finset.mem_insert.mp bad with e|bad
      · have hzb := congrArg q.toFun e
        rw [rz,rb] at hzb
        exact fr (Finset.mem_insert_of_mem (Finset.mem_insert.mpr (Or.inl hzb)))
      obtain ⟨x,hx,e⟩ := Finset.mem_image.mp bad
      have eq := congrArg q.toFun e
      rw [ru x hx,rz] at eq
      exact fr (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (eq ▸ hx : z ∈ U)))
    · simpa only [p.combineEq _ _ _ hd] using nr

theorem viaPerm {m h f v w} (p : Projection m h) (q : Projection h m)
    (ban : Ban h f w) (rec : ∀ a∈v, q.toFun (p.toFun a)=a)
    (eq : (v.map p.toFun).toFinset=w.toFinset) : Ban m f v := by
  intro n hn live
  have ok := renameLive p q live (by simpa using rec)
  apply ban n hn
  have E : (v.map p.toFun).toFinset=v.toFinset.image p.toFun := by ext x;simp
  rw [←eq,E];exact ok

def ordered (v : List ℕ) := v.insertionSort (· ≤ ·)
theorem ord_eq (v : List ℕ) : (ordered v).toFinset=v.toFinset := by
  ext x;simp [ordered,List.mem_insertionSort]
def banList (m f : ℕ) (vs : List (List ℕ)) := ∀ v∈vs, Ban m f v
theorem consBan {m f a l} (h : Ban m f a) (t : banList m f l) : banList m f (a::l) := by
  intro v hv;rcases List.mem_cons.mp hv with rfl|e;exact h;exact t _ e
theorem nilBan (m f) : banList m f [] := by simp [banList]

theorem viaBranch {m f : ℕ} {v : List ℕ} {ws : List (List ℕ)} (closed : banList m f ws)
    (nd : v.Nodup) (no : terminal m v=false)
    (test : anyGate m f (fun u => !ws.contains (ordered u)) v=false) : Ban m (f+1) v := by
  intro n lim live
  cases n with
  | zero =>
    rw [Live] at live
    obtain ⟨a,rep,g,_⟩ := live
    have ev := ends g v (List.mem_toFinset.mp (rep ▸ Finset.mem_singleton_self a))
    simp_all
  | succ n =>
    rw [Live] at live
    obtain ⟨U,a,b,d,rep,hd,_,_,ab,fr,tail⟩ := live
    have yes := @transition m f n U a b d v (fun u => !ws.contains (ordered u)) hd ab fr rep nd (by omega) tail (by
      intro u hu nu
      change (!ws.contains (ordered u))=true
      simp
      intro found
      have hv := closed _ found n (by omega)
      rw [ord_eq,hu] at hv
      exact hv tail)
    simp_all

theorem widen {m f v} (ess : ∀ a∈v, ∃ i : Fin m, ∀ b∈v, b.testBit i.val≠b.testBit (m+i.val) → b=a)
    (h : Ban m f v) : Wide m f v := by
  rintro ⟨n,S,le,live,sub⟩
  have eq : S=v.toFinset := by
    apply Finset.Subset.antisymm (fun x hx => List.mem_toFinset.mpr (sub _ hx))
    intro a ha
    obtain ⟨i,hi⟩ := ess a (List.mem_toFinset.mp ha)
    obtain ⟨b,hb,sep⟩ := liveSeparates live i.val i.isLt
    exact hi b (sub b hb) sep ▸ hb
  exact h n le (eq ▸ live)

theorem viaSmall {m f v} (ex : search m f v=false) (nd : v.Nodup) : Ban m f v := by
  intro n le live
  have := complete m f live le v rfl nd
  simp_all

theorem viaSub {m f v ws} (bs : banList m f ws) (nd : v.Nodup)
    (check : v.sublists.all (fun u => !(u.length≤f+1 && enough m (cover m u)) || ws.contains u)=true) :
    Wide m f v := by
  rintro ⟨n,S,lim,live,sub⟩
  let u := v.filter (fun x => decide (x∈S))
  have eq : u.toFinset=S := by ext x; simp [u]; exact fun hx => sub _ hx
  have nd' : u.Nodup := nd.filter _
  have len := liveSize live
  rw [←eq,List.toFinset_card_of_nodup nd'] at len
  have ok := List.all_eq_true.mp check u (List.mem_sublists.mpr List.filter_sublist)
  have cap : u.length≤f+1 := by omega
  have cov := enoughLive live u eq
  simp [cap,cov] at ok
  exact bs u ok n lim (eq ▸ live)

abbrev B := Ban
abbrev W := Wide
def pt0 : Projection 87 87 := pick [9,10,11,12,13,14,16,17,15,0,1,2,3,4,5,8,6,7,47,49,48,50,51,54,55,52,53,56,57,58,59,60,61,63,64,62,65,67,66,68,69,70,71,74,75,72,73,18,20,19,21,22,25,26,23,24,27,28,29,30,31,32,35,33,34,36,38,37,39,40,41,42,45,46,43,44,76,78,77,79,80,81,82,85,86,83,84] rfl (by decide +kernel) (by decide)
def pti0 : Projection 87 87 := pick [9,10,11,12,13,14,16,17,15,0,1,2,3,4,5,8,6,7,47,49,48,50,51,54,55,52,53,56,57,58,59,60,61,63,64,62,65,67,66,68,69,70,71,74,75,72,73,18,20,19,21,22,25,26,23,24,27,28,29,30,31,32,35,33,34,36,38,37,39,40,41,42,45,46,43,44,76,78,77,79,80,81,82,85,86,83,84] rfl (by decide +kernel) (by decide)
def pt1 : Projection 87 87 := pick [47,48,49,50,54,55,52,53,51,56,58,57,59,63,64,62,60,61,27,28,29,30,35,33,34,31,32,18,19,20,21,25,26,23,24,22,76,77,79,78,80,85,86,83,84,81,82,0,1,2,3,8,6,7,4,5,9,11,10,12,16,17,15,13,14,65,66,68,67,69,74,75,72,73,70,71,36,37,39,38,40,45,46,43,44,41,42] rfl (by decide +kernel) (by decide)
def pti1 : Projection 87 87 := pick [47,48,49,50,54,55,52,53,51,56,58,57,59,63,64,62,60,61,27,28,29,30,35,33,34,31,32,18,19,20,21,25,26,23,24,22,76,77,79,78,80,85,86,83,84,81,82,0,1,2,3,8,6,7,4,5,9,11,10,12,16,17,15,13,14,65,66,68,67,69,74,75,72,73,70,71,36,37,39,38,40,45,46,43,44,41,42] rfl (by decide +kernel) (by decide)
def pt2 : Projection 87 87 := pick [56,58,57,59,63,64,60,61,62,47,48,49,50,54,55,51,52,53,0,2,1,3,8,4,5,6,7,9,11,10,12,16,17,13,14,15,65,68,66,67,69,74,75,70,71,72,73,27,29,28,30,35,31,32,33,34,18,19,20,21,25,26,22,23,24,76,79,77,78,80,85,86,81,82,83,84,36,39,37,38,40,45,46,41,42,43,44] rfl (by decide +kernel) (by decide)
def pti2 : Projection 87 87 := pick [18,20,19,21,23,24,25,26,22,27,29,28,30,33,34,35,31,32,56,57,58,59,62,63,64,60,61,47,49,48,50,52,53,54,55,51,76,78,79,77,80,83,84,85,86,81,82,9,10,11,12,15,16,17,13,14,0,2,1,3,6,7,8,4,5,36,38,39,37,40,43,44,45,46,41,42,65,67,68,66,69,72,73,74,75,70,71] rfl (by decide +kernel) (by decide)
def pt3 : Projection 87 87 := pick [18,20,19,21,23,24,25,26,22,27,29,28,30,33,34,35,31,32,56,57,58,59,62,63,64,60,61,47,49,48,50,52,53,54,55,51,76,78,79,77,80,83,84,85,86,81,82,9,10,11,12,15,16,17,13,14,0,2,1,3,6,7,8,4,5,36,38,39,37,40,43,44,45,46,41,42,65,67,68,66,69,72,73,74,75,70,71] rfl (by decide +kernel) (by decide)
def pti3 : Projection 87 87 := pick [56,58,57,59,63,64,60,61,62,47,48,49,50,54,55,51,52,53,0,2,1,3,8,4,5,6,7,9,11,10,12,16,17,13,14,15,65,68,66,67,69,74,75,70,71,72,73,27,29,28,30,35,31,32,33,34,18,19,20,21,25,26,22,23,24,76,79,77,78,80,85,86,81,82,83,84,36,39,37,38,40,45,46,41,42,43,44] rfl (by decide +kernel) (by decide)
def pt4 : Projection 87 87 := pick [27,29,28,30,33,34,31,32,35,18,20,19,21,23,24,22,25,26,9,11,10,12,15,13,14,16,17,0,2,1,3,6,7,4,5,8,36,39,38,37,40,43,44,41,42,45,46,56,58,57,59,62,60,61,63,64,47,49,48,50,52,53,51,54,55,76,79,78,77,80,83,84,81,82,85,86,65,68,67,66,69,72,73,70,71,74,75] rfl (by decide +kernel) (by decide)
def pti4 : Projection 87 87 := pick [27,29,28,30,33,34,31,32,35,18,20,19,21,23,24,22,25,26,9,11,10,12,15,13,14,16,17,0,2,1,3,6,7,4,5,8,36,39,38,37,40,43,44,41,42,45,46,56,58,57,59,62,60,61,63,64,47,49,48,50,52,53,51,54,55,76,79,78,77,80,83,84,81,82,85,86,65,68,67,66,69,72,73,70,71,74,75] rfl (by decide +kernel) (by decide)
def pc6_0 : Projection 20 20 := pick [6,5,4,7,2,1,0,3,18,17,16,19,14,13,12,15,10,9,8,11] rfl (by decide +kernel) (by decide)
def pci6_0 : Projection 20 20 := pick [6,5,4,7,2,1,0,3,18,17,16,19,14,13,12,15,10,9,8,11] rfl (by decide +kernel) (by decide)
def pc6_1 : Projection 20 20 := pick [8,9,10,11,16,17,18,19,0,1,2,3,12,13,14,15,4,5,6,7] rfl (by decide +kernel) (by decide)
def pci6_1 : Projection 20 20 := pick [8,9,10,11,16,17,18,19,0,1,2,3,12,13,14,15,4,5,6,7] rfl (by decide +kernel) (by decide)
def pc9_0 : Projection 16 16 := pick [2,1,0,3,14,13,12,15,10,9,8,11,6,5,4,7] rfl (by decide +kernel) (by decide)
def pci9_0 : Projection 16 16 := pick [2,1,0,3,14,13,12,15,10,9,8,11,6,5,4,7] rfl (by decide +kernel) (by decide)
def pc11_0 : Projection 20 20 := pick [4,6,5,7,0,2,1,3,12,14,13,15,8,10,9,11,16,18,17,19] rfl (by decide +kernel) (by decide)
def pci11_0 : Projection 20 20 := pick [4,6,5,7,0,2,1,3,12,14,13,15,8,10,9,11,16,18,17,19] rfl (by decide +kernel) (by decide)
def pc11_2 : Projection 20 20 := pick [8,9,10,11,12,13,14,15,0,1,2,3,4,5,6,7,16,17,18,19] rfl (by decide +kernel) (by decide)
def pci11_2 : Projection 20 20 := pick [8,9,10,11,12,13,14,15,0,1,2,3,4,5,6,7,16,17,18,19] rfl (by decide +kernel) (by decide)
def pc13_0 : Projection 16 16 := pick [1,0,2,3,5,4,6,7,13,12,14,15,9,8,10,11] rfl (by decide +kernel) (by decide)
def pci13_0 : Projection 16 16 := pick [1,0,2,3,5,4,6,7,13,12,14,15,9,8,10,11] rfl (by decide +kernel) (by decide)
def pc18_0 : Projection 12 12 := pick [4,6,5,7,0,2,1,3,8,10,9,11] rfl (by decide +kernel) (by decide)
def pci18_0 : Projection 12 12 := pick [4,6,5,7,0,2,1,3,8,10,9,11] rfl (by decide +kernel) (by decide)
def pc18_1 : Projection 12 12 := pick [1,0,2,3,9,8,10,11,5,4,6,7] rfl (by decide +kernel) (by decide)
def pci18_1 : Projection 12 12 := pick [1,0,2,3,9,8,10,11,5,4,6,7] rfl (by decide +kernel) (by decide)
def pc18_2 : Projection 12 12 := pick [9,10,8,11,1,2,0,3,5,6,4,7] rfl (by decide +kernel) (by decide)
def pci18_2 : Projection 12 12 := pick [6,4,5,7,10,8,9,11,2,0,1,3] rfl (by decide +kernel) (by decide)
def pjt_0 : Projection 87 35 := pick [2,4,7,8,0,29,31,34,35,27,11,13,15,17,9,58,60,62,64,56,39,41,44,46,36,68,70,73,75,65,79,81,84,86,76] rfl (by decide +kernel) (by decide)
def pjt_1 : Projection 87 35 := pick [20,22,24,25,18,49,51,53,54,47,10,14,15,16,9,57,61,62,63,56,38,42,44,45,36,67,71,73,74,65,78,82,84,85,76] rfl (by decide +kernel) (by decide)
def pjt_2 : Projection 87 35 := pick [19,22,23,26,18,48,51,52,55,47,1,5,6,8,0,28,32,33,35,27,37,42,43,46,36,66,71,72,75,65,77,82,83,86,76] rfl (by decide +kernel) (by decide)
def pjt_6 : Projection 87 20 := pick [13,15,16,9,60,62,63,56,41,44,45,36,70,73,74,65,81,84,85,76] rfl (by decide +kernel) (by decide)
def pjt_7 : Projection 87 20 := pick [4,6,8,0,31,33,35,27,41,43,46,36,70,72,75,65,81,83,86,76] rfl (by decide +kernel) (by decide)
def pjt_9 : Projection 87 16 := pick [2,4,8,0,11,13,17,9,58,60,64,56,68,70,75,65] rfl (by decide +kernel) (by decide)
def pjt_10 : Projection 87 16 := pick [2,4,7,0,29,31,34,27,11,13,15,9,39,41,44,36] rfl (by decide +kernel) (by decide)
def pjt_11 : Projection 87 20 := pick [22,23,25,18,51,52,54,47,42,43,45,36,71,72,74,65,82,83,85,76] rfl (by decide +kernel) (by decide)
def pjt_12 : Projection 87 16 := pick [20,24,25,18,49,53,54,47,57,62,63,56,78,84,85,76] rfl (by decide +kernel) (by decide)
def pjt_13 : Projection 87 16 := pick [49,51,54,47,10,14,16,9,57,61,63,56,67,71,74,65] rfl (by decide +kernel) (by decide)
def pjt_14 : Projection 87 12 := pick [20,22,24,18,10,14,15,9,38,42,44,36] rfl (by decide +kernel) (by decide)
def pjt_15 : Projection 87 16 := pick [19,23,26,18,48,52,55,47,28,33,35,27,77,83,86,76] rfl (by decide +kernel) (by decide)
def pjt_17 : Projection 87 16 := pick [19,22,23,18,1,5,6,0,28,32,33,27,37,42,43,36] rfl (by decide +kernel) (by decide)
def pjt_18 : Projection 87 12 := pick [41,43,45,36,70,72,74,65,81,83,85,76] rfl (by decide +kernel) (by decide)
def pjt_25 : Projection 87 6 := pick [2,4,0,11,13,9] rfl (by decide +kernel) (by decide)
def pjt_26 : Projection 87 6 := pick [51,54,47,71,74,65] rfl (by decide +kernel) (by decide)
def pjt_27 : Projection 87 6 := pick [22,23,18,42,43,36] rfl (by decide +kernel) (by decide)
def pjt_28 : Projection 87 6 := pick [49,54,47,57,63,56] rfl (by decide +kernel) (by decide)
def pjt_32 : Projection 87 6 := pick [19,23,18,28,33,27] rfl (by decide +kernel) (by decide)
def f0 : ℕ := 0x1110f0
def f1 : ℕ := 0x1110ff
def f2 : ℕ := 0x222f0f
def f3 : ℕ := 0x444ff0
def f4 : ℕ := 0x111110ff00
def f5 : ℕ := 0x22222000ff
def f6 : ℕ := 0x22222f0f00
def f7 : ℕ := 0x44444ff0f0
def f8 : ℕ := 0x111110ff0f
def f9 : ℕ := 0xf
def f11 : ℕ := 0x22222f0f0f
def f12 : ℕ := 0xff
def f13 : ℕ := 0x11111000ff
def f14 : ℕ := 0x111110ffff
def f17 : ℕ := 0x44444ff000
def f18 : ℕ := 0x2004010040200802020100000000000000000000000
def f19 : ℕ := 0x2b056150782b0a83c2a1500000000ff800007fc0000
def f20 : ℕ := 0x3006018040300c0203018000ffe00007ff00003ffff
def f21 : ℕ := 0x8e11c271308e230984e46000001ff0000000003fe00
def f22 : ℕ := 0xc018020180c0300c040607ff00000007ffffffc0000
def f23 : ℕ := 0x20d41a8642a0d43a150c870000000000000ff80001ff
def f24 : ℕ := 0x300600c0603004030180807fffffffff800000000000
def f26 : ℕ := 0x11110ff0
def f27 : ℕ := 0x3333f0ff
def f28 : ℕ := 0x4444ff0f
def f30 : ℕ := 0x111100ff
def f31 : ℕ := 0x4444f0f0
def f32 : ℕ := 0x55550f00
def f34 : ℕ := 0x6318c63183ff07fff
def f35 : ℕ := 0x842108427c1ff801f
def f36 : ℕ := 0x1084210847fe0003e0
def f37 : ℕ := 0x1294a52948000ffc00
def f38 : ℕ := 0x4210842103ff07c00
def f40 : ℕ := 0xf00
def f41 : ℕ := 0x222ff0
def f43 : ℕ := 0x5550f0
def f46 : ℕ := 0xc6318c637fffffc1f
def f48 : ℕ := 0x2222f00f
def f49 : ℕ := 0x33330f00
def f50 : ℕ := 0x842108427c1f0001f
def f51 : ℕ := 0xa5294a528000ffc00
def f52 : ℕ := 0x1084210847fe0f83e0
def f53 : ℕ := 0xc6318c637fff07c1f
def f54 : ℕ := 0x4210842103e007c00
def f60 : ℕ := 0xe739ce73ffff07fff
def f62 : ℕ := 0x6318c63183e007fe0
def f64 : ℕ := 0xb016050380b0281c0a0500000000ff800007fc0000
def f65 : ℕ := 0x3b0761d0783b0e83c3a1d000ffe00fffff007ffffff
def f66 : ℕ := 0x3fe00
def f67 : ℕ := 0xbe17c3f170be2f0b87e5e000fffff007ff00003ffff
def f68 : ℕ := 0x3006018040300c0203018000ffe00007ff0000001ff
def f69 : ℕ := 0x8e11c271308e230984e46000001ff00000000000000
def f70 : ℕ := 0x2222f0f0
def f71 : ℕ := 0x7ff000000000
def f72 : ℕ := 0xf01e0381c0f03c0e070787ffffe00007fffffffffff
def f73 : ℕ := 0x247
def f74 : ℕ := 0x278
def f75 : ℕ := 0x4444ff00
def f76 : ℕ := 0x5555000f
def f77 : ℕ := 0x333330ffff
def f78 : ℕ := 0x33333fff0f
def f84 : ℕ := 0x3006018040300c0203018000ffe000000000003ffff
def f86 : ℕ := 0x4b8
def f87 : ℕ := 0x4444fff0
def f88 : ℕ := 0xc018020180c0300c040607ff0000000000ffffc0000
def f89 : ℕ := 0x1ff
def f90 : ℕ := 0x23d47a9e46a3d4fa353c9f000ffe00007ffff803ffff
def f91 : ℕ := 0x3006018040300c0203018000ffe00007ff00003fe00
def f92 : ℕ := 0x20d41a8642a0d43a150c870000000000000ff8000000
def f93 : ℕ := 0xffe0000000000000000
def f94 : ℕ := 0x330660d8643304c321b0987ffffffffffff00003ffff
def f95 : ℕ := 0x3006018040300c020301800000000007ff00003ffff
def f96 : ℕ := 0x300600c0603004030180807ff001ffff800000000000
def f97 : ℕ := 0xa014050300a020180a04000000000000000003fe00
def f98 : ℕ := 0xbf17e3f178bf2f8bc7e5f000ffffffffff007ffffff
def f99 : ℕ := 0x3106218048310c8243019000ffe00fffff007fc01ff
def f100 : ℕ := 0x841082210084210804442000001ff00000000000000
def f101 : ℕ := 0x7ff007fc0000
def f102 : ℕ := 0xfb1f63d1f8fb3e8fc7a7d7ffffe00ffffffffffffff
def f104 : ℕ := 0x333fff
def f106 : ℕ := 0x2222ff0f
def f107 : ℕ := 0x33330fff
def f108 : ℕ := 0x3333ffff
def f111 : ℕ := 0x55550fff
def f113 : ℕ := 0x111110f000
def f114 : ℕ := 0x3b0761d0783b0e83c3a1d000ffe00ff80000003ffff
def f115 : ℕ := 0xc018020180c0300c040607ff0000000000ff8000000
def f116 : ℕ := 0x9012040280902814080500000000000000000001ff
def f117 : ℕ := 0x23f47e9f47a3f4fa3d3e9f000ffe00ffffffffffffff
def f118 : ℕ := 0x3206419050320c0283218000ffe00fffff007fffe00
def f119 : ℕ := 0x20440882402044120104820000000000000ff8000000
def f120 : ℕ := 0xffe00ff800000000000
def f121 : ℕ := 0x33b676dd67b3b4eb3dba9d7ffffffffffff007ffffff
def f122 : ℕ := 0x3b0761d0783b0e83c3a1d00000000007ff007ffffff
def f123 : ℕ := 0x300600c0603004030180807ff001ff00000000000000
def f124 : ℕ := 0x8010020100802008040400000000000000000000000
def f125 : ℕ := 0x5555fff0
def f126 : ℕ := 0xa5294a52fc1fffc1f
def f136 : ℕ := 0xce19c271b0ce330d84e667ff001ff007ffffffffe00
def f137 : ℕ := 0x33333fffff
def f138 : ℕ := 0x1111100f00
def f140 : ℕ := 0x3c0780e0783c0703c1c0e07ffffffffffffffffc0000
def f141 : ℕ := 0x3f07e0f87c3f07c3e1f0f87fffffffffffffffffffff
def f142 : ℕ := 0x30d61ac662b0d43b158c877fffffffff800ff80001ff
def f143 : ℕ := 0x3333ff0f
def f144 : ℕ := 0xe01c070300e030180e06000001ff0000000003fe00
def f145 : ℕ := 0xc018020180c0300c0406000000000007ffffffc0000
def f146 : ℕ := 0x2cf59ea75bacf73add4ee77ff001ff007fffffffffff
def f147 : ℕ := 0xc218421190c2300c842607ff001ff007ff007fffe00
def f148 : ℕ := 0x5555ff0f
def f150 : ℕ := 0x55555ffff0
def f153 : ℕ := 0x33333f0fff
def f154 : ℕ := 0x55555ff0ff
def f157 : ℕ := 0xd01a060280d038140c070000000000000ff80001ff
def f158 : ℕ := 0x10020040201000010080007fffffffff800000000000
def f163 : ℕ := 0x4008000080401004000207ff00000007ffffffc0000
def f164 : ℕ := 0xc018060200c030100c060000000000000000000000
def f166 : ℕ := 0x2222f0ff
def f168 : ℕ := 0x28f51ea753a8f63a9d4ec7000001ff00000ff803ffff
def f169 : ℕ := 0x821042111082200884240000001ff0000000003fe00
def f170 : ℕ := 0x2014028040a0140a0500810000000000000ff80001ff
def f171 : ℕ := 0x1ff00000000000000
def f172 : ℕ := 0x5555ffff
def f173 : ℕ := 0x38e71ce77338e63399cec67fffffffff80000003fe00
def f174 : ℕ := 0x8e11c271308e230984e46000000000000000003fe00
def f176 : ℕ := 0x300600c0603004030180807ffffe00ff800000000000
def f177 : ℕ := 0xff8000000
def f178 : ℕ := 0x2cd59aa65aacd73ad54ce77ff00000007ffffffc01ff
def f179 : ℕ := 0xc018020180c0300c040607ff00000007ff007fc0000
def f180 : ℕ := 0x20d41a8642a0d43a150c8700000000000000000001ff
def f181 : ℕ := 0x7ff0000000000000000000
def f184 : ℕ := 0x18c6318c67ffff83ff
def f185 : ℕ := 0x4210842103ff07c1f
def f190 : ℕ := 0x66666ffff0
def f193 : ℕ := 0x44444000ff
def f195 : ℕ := 0x1ce739ce77ffffffff
def f196 : ℕ := 0x222200f0
def f197 : ℕ := 0x3006018040300c0203018000000000000000003ffff
def f201 : ℕ := 0x3006018040300c0203018000ffe00fffff007ffffff
def f202 : ℕ := 0xffe00fffff007fc0000
def f203 : ℕ := 0x44440f00
def f204 : ℕ := 0x3c0780e0783c0703c1c0e07ff001ff00000ff8000000
def f205 : ℕ := 0x300600c060300403018080000fffffff800000000000
def f206 : ℕ := 0x20040080402004020100800000000000000000000000
def f207 : ℕ := 0x6318c6318000003ff
def f210 : ℕ := 0x3e007c00
def f219 : ℕ := 0x842108427c1f003e0
def f220 : ℕ := 0x1084210847fe0f8000
def f221 : ℕ := 0x1294a52948000003ff
def f222 : ℕ := 0xa5294a52fc1ffffe0
def f233 : ℕ := 0x100200800010040001008000ffe00007ff00003ffff
def f234 : ℕ := 0x22222fff0f
def f235 : ℕ := 0xd01a028180d0340c050687ffffe00007fffffffffff
def f236 : ℕ := 0x100200800010040001008000ffe000000000003ffff
def f237 : ℕ := 0x310620c8603104430190887ffffffffffff00003ffff
def f238 : ℕ := 0x10020080001004000100800000000007ff00003ffff
def f239 : ℕ := 0xa014050300a020180a040000000000000000000000
def f240 : ℕ := 0xaf15e37178af2b8bc6e57000001ffff800007fffe00
def f241 : ℕ := 0x21042100482108824201100000000ff800007fc0000
def f242 : ℕ := 0x841082210084210804442000001ff0000000003fe00
def f243 : ℕ := 0x7fc0000
def f244 : ℕ := 0xe739ce73fc1ff83ff
def f245 : ℕ := 0xeb1d6351f8eb3a8fc6a757ff00000fffffffffc0000
def f246 : ℕ := 0x2b056150782b0a83c2a1500000000ff800000000000
def f247 : ℕ := 0xc018020180c0300c040607ff00000007ffff8000000
def f248 : ℕ := 0x901204028090281408050000000000000000000000
def f249 : ℕ := 0x22f45e9747a2f4ba3d2e9700000000ff800ffffc01ff
def f250 : ℕ := 0x22044110502208028221000000000ff800007fc0000
def f251 : ℕ := 0x20440882402044120104820000000000000ff80001ff
def f252 : ℕ := 0xff800000000000
def f253 : ℕ := 0x32b656d567b2b4ab3daa957fffffffff800007fc0000
def f254 : ℕ := 0x2b056150782b0a83c2a150000000000000007fc0000
def f255 : ℕ := 0x300600c0603004030180807fffffff00000000000000
def f256 : ℕ := 0x22222f0ff0
def f257 : ℕ := 0x222f00
def f258 : ℕ := 0x22200f
def f259 : ℕ := 0x3333000f
def f260 : ℕ := 0xff00
def f265 : ℕ := 0x14a5294a57fff07fe0
def f273 : ℕ := 0x444f00
def f274 : ℕ := 0x11100f
def f282 : ℕ := 0x8f11e271388f2389c4e47000001ffff800007fffe00
def f283 : ℕ := 0x1002000080100804000100000000ff800007fc0000
def f284 : ℕ := 0xcb196251b8cb328dc4a657ff00000fffffffffc0000
def f285 : ℕ := 0xb016050380b0281c0a0500000000ff800000000000
def f286 : ℕ := 0x20f41e8743a0f43a1d0e8700000000ff800ffffc01ff
def f287 : ℕ := 0x2004010100200008020000000000ff800007fc0000
def f288 : ℕ := 0x30b616c563b0b42b1d8a857fffffffff800007fc0000
def f289 : ℕ := 0xb016050380b0281c0a050000000000000007fc0000
def f290 : ℕ := 0x1111000f
def f291 : ℕ := 0x9e13c2f1309e270985e4e000fffff007ff00003ffff
def f292 : ℕ := 0x100200800010040001008000ffe00007ff0000001ff
def f293 : ℕ := 0x21d43a8e42a1d47a151c8f000ffe00007ffff803ffff
def f294 : ℕ := 0x100200800010040001008000ffe00007ff00003fe00
def f296 : ℕ := 0xe739ce738000fffff
def f299 : ℕ := 0x200401004020080202010000000000000000003fe00
def f300 : ℕ := 0x8f11e271388f2389c4e47000001ffff800007fc0000
def f309 : ℕ := 0x3ffff
def f310 : ℕ := 0x28f51ea753a8f63a9d4ec7000001ff00000ff8000000
def f311 : ℕ := 0x4008000080401004000207ff00000007ff007fc0000
def f312 : ℕ := 0x38f71ee773b8f63b9dcec77fffffffff800ff803ffff
def f313 : ℕ := 0x8f11e271388f2389c4e470000000000000ff803ffff
def f315 : ℕ := 0x2bf57ebf57abf6fabd7edf000fffff007ffff803ffff
def f316 : ℕ := 0x3006018040300c0203018000ffe00007ff000000000
def f317 : ℕ := 0x8010020100802008040400000000000000007fc0000
def f318 : ℕ := 0xef1de371f8ef3b8fc6e777ff001fffffffffffffe00
def f319 : ℕ := 0x2f05e170782f0b83c2e17000001ffff80000003fe00
def f320 : ℕ := 0x4008000080401004000207ff00000007ffff8000000
def f321 : ℕ := 0x8f11e271388f2389c4e47000001ff0000000003fe00
def f322 : ℕ := 0x2af55eb757aaf6babd6ed7000001ffff800fffffffff
def f323 : ℕ := 0x20040100402008020201000000000ff800007fc0000
def f324 : ℕ := 0x20040080402004020100800000000000000ff80001ff
def f325 : ℕ := 0x1ffff800000000000
def f326 : ℕ := 0x3af75ef777baf6bbbdeed77fffffffff800007fffe00
def f327 : ℕ := 0xaf15e37178af2b8bc6e570000000000000007fffe00
def f328 : ℕ := 0x300600c0603004030180807ffffe0000000000000000
def f329 : ℕ := 0x8010020100802008040400000000000000ff8000000
def f330 : ℕ := 0x20f41e8743a0f43a1d0e87000001ff0000000003ffff
def f331 : ℕ := 0x2004008040200402010080000001ff00000000000000
def f332 : ℕ := 0x10020040201000010080007ffffe00ff800000000000
def f333 : ℕ := 0x1ad6b5ad6ffe0fffe0
def f334 : ℕ := 0xd01a060280d038140c070000000000000000000000
def f335 : ℕ := 0xa214431150a2280a86250000001ffff800007fffe00
def f336 : ℕ := 0x4440f0
def f342 : ℕ := 0x3106218048310c8243019000ffe00fffff007ffffff
def f343 : ℕ := 0xe11c2301c8e1388e460717ff00000fffffffffc0000
def f344 : ℕ := 0x21042100482108824201100000000ff800000000000
def f345 : ℕ := 0x100200008010080400010000000000000000000000
def f346 : ℕ := 0x22d45a9646a2d4ba352c9700000000ff800ffffc01ff
def f347 : ℕ := 0x20c418864220c432110c860000000000000ff80001ff
def f348 : ℕ := 0x321642d064b2148b25a0917fffffffff800007fc0000
def f349 : ℕ := 0x2104210048210882420110000000000000007fc0000
def f350 : ℕ := 0x2222000f
def f352 : ℕ := 0x6ff
def f355 : ℕ := 0x20040100402008020201000000000007ff000000000
def f356 : ℕ := 0xcb196251b8cb328dc4a657ff00000ff800ffffc0000
def f357 : ℕ := 0x200401004020080202010000ffe0000000000000000
def f358 : ℕ := 0x30b616c563b0b42b1d8a857ff001ffff800007fc0000
def f359 : ℕ := 0x8a114251308a220984a440000000000000000000000
def f360 : ℕ := 0x40080200004010000402000001ff0000000003fe00
def f361 : ℕ := 0x610c2100c8611886420317ff00000fffffffffc0000
def f362 : ℕ := 0xa014050300a020180a04000001ff00000000000000
def f363 : ℕ := 0x841082210084210804442000000000000000003fe00
def f364 : ℕ := 0x321642d064b2148b25a0917ffffe00ff800007fc0000
def f365 : ℕ := 0x901204028090281408050000000000000ff8000000
def f366 : ℕ := 0x2ef5deb75faef7bafd6ef77ff00000fffffffffc01ff
def f367 : ℕ := 0xe21c4311d0e2380e862707ff00000fffff007fc0000
def f368 : ℕ := 0x204408824020441201048200000000000000000001ff
def f370 : ℕ := 0x2b056150782b0a83c2a157ff00000ff800007fc0000
def f371 : ℕ := 0x77777fffff
def f372 : ℕ := 0x3eb7d6f57fbeb7abfdeaf57ffffffffffffffffc0000
def f373 : ℕ := 0xc018020180c0300c0406000000000007ffff8000000
def f374 : ℕ := 0x300600c060300403018080000fffff00000000000000
def f375 : ℕ := 0x2094128442a0942a1508850000000000000000000000
def f376 : ℕ := 0x32f65ed767b2f4bb3dae977fffffffff800ffffc01ff
def f377 : ℕ := 0x400802000040100004020000000000000ff80001ff
def f378 : ℕ := 0x122244512512208128a2107fffffffff800007fc0000
def f380 : ℕ := 0x33300f
def f381 : ℕ := 0x777f0f
def f382 : ℕ := 0x777ff0
def f383 : ℕ := 0x7ff00000ff800000000000
def f384 : ℕ := 0xeb1d6351f8eb3a8fc6a7500000000007ffffffc0000
def f385 : ℕ := 0x5555f0ff
def f389 : ℕ := 0x33333fff00
def f390 : ℕ := 0xf01e0381c0f03c0e070787ffffe00007ffff803ffff
def f391 : ℕ := 0xce19c271b0ce330d84e667ff001ff007ffff803fe00
def f392 : ℕ := 0x2cd59aa65aacd73ad54ce77ff00000007ffff80001ff
def f393 : ℕ := 0xc018020180c0300c040607ff00000007ff000000000
def f394 : ℕ := 0x3c0780e0783c0703c1c0e07ffffffffffffff8000000
def f418 : ℕ := 0x1111100fff
def f419 : ℕ := 0x2b056150782b0a83c2a1500000000fffff007fc0000
def f420 : ℕ := 0x8e11c271308e230984e46000001ff007ff00003fe00
def f422 : ℕ := 0x1111fff0
def f423 : ℕ := 0x1294a5294801fffc00
def f424 : ℕ := 0x20d41a8642a0d43a150c8700000000007ffff80001ff
def f425 : ℕ := 0x16b5ad6b5801ffffff
def f426 : ℕ := 0x22f45e9747a2f4ba3d2e9700000000fffffffffc01ff
def f427 : ℕ := 0x204408824020441201048200000000007ffff80001ff
def f428 : ℕ := 0x3006018040300c0203018000ffe000000000003fe00
def f429 : ℕ := 0x28f51ea753a8f63a9d4ec7000001ff007ffff803ffff
def f430 : ℕ := 0x2014028040a0140a05008100000000007ffff80001ff
def f431 : ℕ := 0xc018020180c0300c040607ff0000000000007fc0000
def f432 : ℕ := 0x30d61ac662b0d43b158c877ffffffffffffff80001ff
def f433 : ℕ := 0x1294a5294fffffffe0
def f434 : ℕ := 0xd01a060280d038140c0700000000007ffff80001ff
def f435 : ℕ := 0x7fe0003e0
def f438 : ℕ := 0x1084210847ffff83e0
def f439 : ℕ := 0x300600c0603004030180807ffffffffffff000000000
def f440 : ℕ := 0x2004010040200802020100000000000000007fc0000
def f441 : ℕ := 0xd01a028180d0340c050687ffffe00007ffff803ffff
def f445 : ℕ := 0x801002010080200804040000000000000000003fe00
def f446 : ℕ := 0xfe1fc3f1f0fe3f0f87e7e7fffffff007fffffffffff
def f447 : ℕ := 0xe01c070300e030180e06000001ff00000000000000
def f448 : ℕ := 0x700e0180c0701c06030387ffffe00007ffffffc01ff
def f449 : ℕ := 0xff80001ff
def f450 : ℕ := 0x2fd5fabe5eafd7faf57cff7ffffe00007fffffffffff
def f451 : ℕ := 0xf01e0381c0f03c0e070787ffffe00007ff007fffe00
def f452 : ℕ := 0x20d41a8642a0d43a150c870000000000000000000000
def f453 : ℕ := 0x7ffffe0000000000000000
def f454 : ℕ := 0x777fff
def f455 : ℕ := 0xf01e0381c0f03c0e0707800000000007fffffffffff
def f456 : ℕ := 0x300600c060300403018080000001ffff800000000000
def f462 : ℕ := 0x111110f0ff
def f463 : ℕ := 0x3b0761d0783b0e83c3a1d000ffe00ff800007ffffff
def f464 : ℕ := 0xbe17c3f170be2f0b87e5e000fffff0000000003ffff
def f465 : ℕ := 0x3006018040300c0203018000ffe00000000000001ff
def f466 : ℕ := 0x23d47a9e46a3d4fa353c9f000ffe0000000ff803ffff
def f467 : ℕ := 0x555ff0
def f468 : ℕ := 0x330660d8643304c321b0987fffffffff80000003ffff
def e0 : List ℕ := [f0,f1,f2,f3]
def e9 : List ℕ := [f12,f4,f11,f7]
def e12 : List ℕ := [f13,f4,f6,f7]
def e16 : List ℕ := [f1,f2,f3]
def e17 : List ℕ := [f18,f19,f20,f21,f22,f23,f24]
def e35 : List ℕ := [f34,f50,f51,f53,f52]
def e36 : List ℕ := [f38,f34,f50,f51,f53,f52]
def e37 : List ℕ := [f54,f34,f50,f51,f52]
def e51 : List ℕ := [f64,f65,f21,f22,f23,f24]
def e52 : List ℕ := [f64,f20,f21,f22,f23,f24]
def e53 : List ℕ := [f64,f20,f65,f21,f22,f23,f24]
def e54 : List ℕ := [f66,f20,f65,f21,f22,f23,f24]
def e55 : List ℕ := [f38,f34,f35,f36,f37]
def e56 : List ℕ := [f20,f65,f21,f67,f22,f23,f24]
def e57 : List ℕ := [f68,f20,f65,f21,f22,f23,f24]
def e58 : List ℕ := [f20,f65,f69,f21,f22,f23,f24]
def e59 : List ℕ := [f26,f70,f27,f28]
def e60 : List ℕ := [f71,f20,f65,f21,f22,f23,f24]
def e61 : List ℕ := [f65,f21,f22,f72,f23,f24]
def e62 : List ℕ := [f73,f74]
def e65 : List ℕ := [f5,f6,f77,f7]
def e66 : List ℕ := [f8,f5,f6,f77,f7]
def e68 : List ℕ := [f5,f6,f78,f7]
def e69 : List ℕ := [f8,f5,f6,f78,f7]
def e74 : List ℕ := [f38,f34,f50,f51,f52]
def e75 : List ℕ := [f20,f65,f21,f22,f72,f23,f24]
def e76 : List ℕ := [f84,f65,f21,f22,f23,f24]
def e78 : List ℕ := [f30,f48,f49]
def e79 : List ℕ := [f30,f48,f49,f87]
def e80 : List ℕ := [f84,f20,f65,f21,f22,f23,f24]
def e81 : List ℕ := [f20,f65,f21,f88,f22,f23,f24]
def e82 : List ℕ := [f89,f20,f65,f21,f22,f23,f24]
def e83 : List ℕ := [f20,f65,f21,f22,f23,f90,f24]
def e84 : List ℕ := [f91,f20,f65,f21,f22,f23,f24]
def e85 : List ℕ := [f20,f65,f21,f22,f92,f23,f24]
def e86 : List ℕ := [f93,f20,f65,f21,f22,f23,f24]
def e87 : List ℕ := [f65,f21,f22,f23,f24,f94]
def e88 : List ℕ := [f20,f65,f21,f22,f23,f24,f94]
def e89 : List ℕ := [f95,f65,f21,f22,f23,f24]
def e90 : List ℕ := [f95,f20,f65,f21,f22,f23,f24]
def e91 : List ℕ := [f20,f65,f21,f22,f23,f96,f24]
def e92 : List ℕ := [f97,f20,f65,f21,f22,f23,f24]
def e93 : List ℕ := [f20,f21,f98,f22,f23,f24]
def e94 : List ℕ := [f20,f65,f21,f98,f22,f23,f24]
def e95 : List ℕ := [f20,f99,f21,f22,f23,f24]
def e96 : List ℕ := [f20,f99,f65,f21,f22,f23,f24]
def e97 : List ℕ := [f20,f65,f100,f21,f22,f23,f24]
def e98 : List ℕ := [f101,f20,f65,f21,f22,f23,f24]
def e99 : List ℕ := [f38,f50,f51,f60,f52]
def e100 : List ℕ := [f38,f34,f50,f51,f60,f52]
def e101 : List ℕ := [f20,f65,f21,f22,f102,f23,f24]
def e120 : List ℕ := [f38,f62,f50,f51,f52]
def e121 : List ℕ := [f38,f62,f34,f50,f51,f52]
def e122 : List ℕ := [f20,f114,f65,f21,f22,f23,f24]
def e123 : List ℕ := [f20,f65,f21,f115,f22,f23,f24]
def e124 : List ℕ := [f116,f20,f65,f21,f22,f23,f24]
def e125 : List ℕ := [f20,f21,f22,f23,f117,f24]
def e126 : List ℕ := [f20,f65,f21,f22,f23,f117,f24]
def e127 : List ℕ := [f20,f118,f21,f22,f23,f24]
def e128 : List ℕ := [f20,f118,f65,f21,f22,f23,f24]
def e129 : List ℕ := [f20,f65,f21,f22,f119,f23,f24]
def e130 : List ℕ := [f120,f20,f65,f21,f22,f23,f24]
def e131 : List ℕ := [f20,f65,f21,f22,f23,f24,f121]
def e132 : List ℕ := [f20,f122,f65,f21,f22,f23,f24]
def e133 : List ℕ := [f20,f65,f21,f22,f23,f123,f24]
def e134 : List ℕ := [f20,f65,f124,f21,f22,f23,f24]
def e138 : List ℕ := [f34,f126,f53,f52]
def e154 : List ℕ := [f64,f65,f22,f136,f23,f24]
def e155 : List ℕ := [f64,f20,f22,f136,f23,f24]
def e156 : List ℕ := [f65,f136,f72,f23,f24]
def e157 : List ℕ := [f65,f22,f136,f72,f23,f24]
def e158 : List ℕ := [f20,f65,f136,f72,f23,f24]
def e159 : List ℕ := [f84,f65,f22,f136,f23,f24]
def e160 : List ℕ := [f20,f65,f88,f136,f23,f24]
def e168 : List ℕ := [f65,f136,f23,f94,f140]
def e169 : List ℕ := [f65,f136,f23,f24,f141]
def e170 : List ℕ := [f65,f22,f136,f142,f94]
def e171 : List ℕ := [f65,f22,f136,f23,f24,f94]
def e172 : List ℕ := [f30,f48,f143,f87]
def e173 : List ℕ := [f95,f65,f22,f136,f23,f24]
def e174 : List ℕ := [f20,f22,f136,f23,f117,f24]
def e175 : List ℕ := [f20,f118,f22,f136,f23,f24]
def e176 : List ℕ := [f144,f20,f65,f136,f23,f24]
def e177 : List ℕ := [f144,f20,f65,f22,f23,f24]
def e178 : List ℕ := [f20,f65,f136,f23,f24,f140]
def e179 : List ℕ := [f20,f65,f145,f136,f23,f24]
def e180 : List ℕ := [f20,f65,f22,f23,f146,f24]
def e181 : List ℕ := [f20,f65,f22,f147,f23,f24]
def e193 : List ℕ := [f4,f153,f137,f154]
def e200 : List ℕ := [f65,f136,f72,f24,f142]
def e201 : List ℕ := [f20,f65,f136,f142,f140]
def e202 : List ℕ := [f20,f65,f22,f136,f24,f142]
def e203 : List ℕ := [f20,f65,f22,f136,f23,f142]
def e204 : List ℕ := [f157,f20,f65,f22,f136,f24]
def e205 : List ℕ := [f20,f65,f22,f136,f158,f23]
def e206 : List ℕ := [f20,f65,f22,f136,f23,f24]
def e208 : List ℕ := [f20,f65,f21,f136,f23,f24]
def e209 : List ℕ := [f20,f65,f21,f22,f136,f23,f24]
def e219 : List ℕ := [f144,f20,f65,f21,f22,f23,f24]
def e227 : List ℕ := [f20,f65,f163,f21,f23,f24]
def e228 : List ℕ := [f20,f65,f163,f21,f22,f23,f24]
def e229 : List ℕ := [f164,f20,f65,f21,f22,f23,f24]
def e234 : List ℕ := [f20,f65,f22,f23,f168,f24]
def e235 : List ℕ := [f20,f65,f21,f22,f168,f24]
def e236 : List ℕ := [f20,f65,f21,f22,f23,f168,f24]
def e239 : List ℕ := [f20,f65,f169,f22,f23,f24]
def e240 : List ℕ := [f20,f65,f169,f21,f22,f23,f24]
def e241 : List ℕ := [f20,f65,f21,f22,f170,f24]
def e242 : List ℕ := [f20,f65,f21,f22,f170,f23,f24]
def e243 : List ℕ := [f171,f20,f65,f21,f22,f23,f24]
def e244 : List ℕ := [f26,f70,f27,f172]
def e245 : List ℕ := [f20,f65,f21,f22,f23,f173]
def e246 : List ℕ := [f20,f65,f21,f22,f23,f24,f173]
def e247 : List ℕ := [f20,f65,f174,f21,f22,f23,f24]
def e263 : List ℕ := [f20,f65,f21,f22,f23,f176]
def e264 : List ℕ := [f20,f65,f21,f22,f23,f176,f24]
def e265 : List ℕ := [f177,f20,f65,f21,f22,f23,f24]
def e266 : List ℕ := [f20,f65,f21,f23,f178,f24]
def e267 : List ℕ := [f20,f65,f21,f22,f23,f178,f24]
def e268 : List ℕ := [f20,f65,f21,f179,f23,f24]
def e269 : List ℕ := [f20,f65,f21,f179,f22,f23,f24]
def e270 : List ℕ := [f20,f65,f21,f22,f180,f23,f24]
def e271 : List ℕ := [f181,f20,f65,f21,f22,f23,f24]
def e277 : List ℕ := [f34,f51,f53,f52,f184]
def e288 : List ℕ := [f8,f193,f17,f190]
def e290 : List ℕ := [f34,f51,f53,f184]
def e291 : List ℕ := [f65,f21,f72,f23,f24,f140]
def e292 : List ℕ := [f65,f21,f22,f23,f94,f140]
def e293 : List ℕ := [f34,f35,f36,f37,f195]
def e294 : List ℕ := [f65,f21,f22,f23,f24,f141]
def e295 : List ℕ := [f26,f196,f27]
def e296 : List ℕ := [f26,f196,f27,f28]
def e297 : List ℕ := [f197,f65,f21,f22,f23,f24]
def e302 : List ℕ := [f201,f21,f22,f23,f24]
def e303 : List ℕ := [f202,f20,f21,f22,f23,f24]
def e304 : List ℕ := [f26,f70,f203,f28]
def e305 : List ℕ := [f20,f21,f22,f23,f24,f204]
def e306 : List ℕ := [f20,f65,f21,f22,f142,f140]
def e307 : List ℕ := [f20,f65,f21,f22,f23,f24,f140]
def e308 : List ℕ := [f20,f65,f21,f145,f22,f23,f24]
def e309 : List ℕ := [f20,f65,f21,f22,f23,f205,f24]
def e310 : List ℕ := [f20,f65,f21,f22,f206,f23,f24]
def e311 : List ℕ := [f20,f65,f21,f22,f24,f142]
def e312 : List ℕ := [f20,f65,f21,f22,f23,f142]
def e313 : List ℕ := [f20,f65,f21,f22,f23,f24,f142]
def e314 : List ℕ := [f157,f20,f65,f21,f22,f24]
def e315 : List ℕ := [f157,f20,f65,f21,f22,f23,f24]
def e316 : List ℕ := [f20,f65,f21,f22,f158,f23]
def e317 : List ℕ := [f20,f65,f21,f22,f158,f23,f24]
def e318 : List ℕ := [f20,f65,f21,f22,f23,f24]
def e355 : List ℕ := [f19,f65,f21,f22,f23,f24]
def e356 : List ℕ := [f233,f19,f21,f22,f23,f24]
def e357 : List ℕ := [f14,f11,f7]
def e358 : List ℕ := [f14,f234,f7]
def e359 : List ℕ := [f14,f11,f234,f7]
def e360 : List ℕ := [f65,f21,f22,f235,f23,f24]
def e361 : List ℕ := [f210,f34,f35,f36,f37]
def e362 : List ℕ := [f236,f65,f21,f22,f23,f24]
def e363 : List ℕ := [f65,f21,f22,f23,f24,f237]
def e364 : List ℕ := [f238,f65,f21,f22,f23,f24]
def e365 : List ℕ := [f233,f21,f98,f22,f23,f24]
def e366 : List ℕ := [f233,f99,f21,f22,f23,f24]
def e367 : List ℕ := [f233,f21,f22,f23,f117,f24]
def e368 : List ℕ := [f233,f118,f21,f22,f23,f24]
def e369 : List ℕ := [f233,f65,f22,f136,f23,f24]
def e370 : List ℕ := [f233,f65,f21,f136,f23,f24]
def e371 : List ℕ := [f144,f233,f65,f22,f23,f24]
def e372 : List ℕ := [f233,f65,f163,f21,f23,f24]
def e373 : List ℕ := [f233,f65,f22,f23,f168,f24]
def e374 : List ℕ := [f233,f65,f21,f22,f168,f24]
def e375 : List ℕ := [f233,f65,f169,f22,f23,f24]
def e376 : List ℕ := [f233,f65,f21,f22,f170,f24]
def e377 : List ℕ := [f233,f65,f21,f22,f23,f173]
def e378 : List ℕ := [f233,f65,f21,f22,f23,f176]
def e379 : List ℕ := [f233,f65,f21,f23,f178,f24]
def e380 : List ℕ := [f233,f65,f21,f179,f23,f24]
def e381 : List ℕ := [f233,f65,f21,f22,f24,f142]
def e382 : List ℕ := [f233,f65,f21,f22,f23,f142]
def e383 : List ℕ := [f157,f233,f65,f21,f22,f24]
def e384 : List ℕ := [f233,f65,f21,f22,f158,f23]
def e385 : List ℕ := [f233,f65,f21,f22,f23,f24]
def e386 : List ℕ := [f233,f19,f65,f21,f22,f23,f24]
def e387 : List ℕ := [f239,f19,f65,f21,f22,f23,f24]
def e388 : List ℕ := [f19,f65,f240,f22,f23,f24]
def e389 : List ℕ := [f19,f65,f21,f240,f22,f23,f24]
def e390 : List ℕ := [f241,f19,f65,f21,f22,f23,f24]
def e391 : List ℕ := [f19,f65,f242,f22,f23,f24]
def e392 : List ℕ := [f19,f65,f242,f21,f22,f23,f24]
def e393 : List ℕ := [f243,f19,f65,f21,f22,f23,f24]
def e394 : List ℕ := [f34,f35,f244,f36,f37]
def e395 : List ℕ := [f65,f21,f22,f245,f23,f24]
def e396 : List ℕ := [f19,f65,f21,f22,f245,f23,f24]
def e397 : List ℕ := [f246,f65,f21,f22,f23,f24]
def e398 : List ℕ := [f246,f19,f65,f21,f22,f23,f24]
def e399 : List ℕ := [f19,f65,f21,f247,f22,f23,f24]
def e400 : List ℕ := [f248,f19,f65,f21,f22,f23,f24]
def e401 : List ℕ := [f19,f65,f21,f22,f249,f24]
def e402 : List ℕ := [f19,f65,f21,f22,f23,f249,f24]
def e403 : List ℕ := [f250,f19,f65,f21,f22,f23,f24]
def e404 : List ℕ := [f19,f65,f21,f22,f251,f24]
def e405 : List ℕ := [f19,f65,f21,f22,f251,f23,f24]
def e406 : List ℕ := [f252,f19,f65,f21,f22,f23,f24]
def e407 : List ℕ := [f65,f21,f22,f23,f24,f253]
def e408 : List ℕ := [f19,f65,f21,f22,f23,f24,f253]
def e409 : List ℕ := [f254,f65,f21,f22,f23,f24]
def e410 : List ℕ := [f254,f19,f65,f21,f22,f23,f24]
def e411 : List ℕ := [f19,f65,f21,f22,f23,f255,f24]
def e412 : List ℕ := [f97,f19,f65,f21,f22,f23,f24]
def e413 : List ℕ := [f19,f21,f98,f22,f23,f24]
def e414 : List ℕ := [f19,f65,f21,f98,f22,f23,f24]
def e415 : List ℕ := [f19,f99,f21,f22,f23,f24]
def e416 : List ℕ := [f19,f99,f65,f21,f22,f23,f24]
def e417 : List ℕ := [f19,f65,f100,f21,f22,f23,f24]
def e418 : List ℕ := [f26,f75,f76]
def e419 : List ℕ := [f26,f166,f75,f76]
def e420 : List ℕ := [f101,f19,f65,f21,f22,f23,f24]
def e421 : List ℕ := [f8,f256,f193,f17]
def e422 : List ℕ := [f8,f5,f6,f7]
def e423 : List ℕ := [f19,f65,f21,f22,f102,f23,f24]
def e424 : List ℕ := [f19,f114,f65,f21,f22,f23,f24]
def e425 : List ℕ := [f1,f257,f2,f3]
def e426 : List ℕ := [f19,f65,f21,f115,f22,f23,f24]
def e427 : List ℕ := [f116,f19,f65,f21,f22,f23,f24]
def e428 : List ℕ := [f19,f21,f22,f23,f117,f24]
def e429 : List ℕ := [f19,f65,f21,f22,f23,f117,f24]
def e430 : List ℕ := [f19,f118,f21,f22,f23,f24]
def e431 : List ℕ := [f19,f118,f65,f21,f22,f23,f24]
def e432 : List ℕ := [f19,f65,f21,f22,f119,f23,f24]
def e433 : List ℕ := [f120,f19,f65,f21,f22,f23,f24]
def e434 : List ℕ := [f19,f65,f21,f22,f23,f24,f121]
def e435 : List ℕ := [f19,f122,f65,f21,f22,f23,f24]
def e436 : List ℕ := [f19,f65,f21,f22,f23,f123,f24]
def e437 : List ℕ := [f19,f65,f124,f21,f22,f23,f24]
def e438 : List ℕ := [f19,f65,f22,f136,f23,f24]
def e439 : List ℕ := [f19,f65,f21,f136,f23,f24]
def e440 : List ℕ := [f19,f65,f21,f22,f136,f23,f24]
def e441 : List ℕ := [f144,f19,f65,f22,f23,f24]
def e442 : List ℕ := [f144,f19,f65,f21,f22,f23,f24]
def e443 : List ℕ := [f19,f65,f163,f21,f23,f24]
def e444 : List ℕ := [f19,f65,f163,f21,f22,f23,f24]
def e445 : List ℕ := [f164,f19,f65,f21,f22,f23,f24]
def e446 : List ℕ := [f19,f65,f22,f23,f168,f24]
def e447 : List ℕ := [f19,f65,f21,f22,f168,f24]
def e448 : List ℕ := [f19,f65,f21,f22,f23,f168,f24]
def e449 : List ℕ := [f19,f65,f169,f22,f23,f24]
def e450 : List ℕ := [f19,f65,f169,f21,f22,f23,f24]
def e451 : List ℕ := [f19,f65,f21,f22,f170,f24]
def e452 : List ℕ := [f19,f65,f21,f22,f170,f23,f24]
def e453 : List ℕ := [f171,f19,f65,f21,f22,f23,f24]
def e454 : List ℕ := [f19,f65,f21,f22,f23,f173]
def e455 : List ℕ := [f19,f65,f21,f22,f23,f24,f173]
def e456 : List ℕ := [f19,f65,f174,f21,f22,f23,f24]
def e457 : List ℕ := [f19,f65,f21,f22,f23,f176]
def e458 : List ℕ := [f19,f65,f21,f22,f23,f176,f24]
def e459 : List ℕ := [f177,f19,f65,f21,f22,f23,f24]
def e460 : List ℕ := [f19,f65,f21,f23,f178,f24]
def e461 : List ℕ := [f19,f65,f21,f22,f23,f178,f24]
def e462 : List ℕ := [f19,f65,f21,f179,f23,f24]
def e463 : List ℕ := [f19,f65,f21,f179,f22,f23,f24]
def e464 : List ℕ := [f19,f65,f21,f22,f180,f23,f24]
def e465 : List ℕ := [f30,f31,f32]
def e466 : List ℕ := [f30,f106,f31,f32]
def e467 : List ℕ := [f181,f19,f65,f21,f22,f23,f24]
def e468 : List ℕ := [f8,f5,f6,f190]
def e469 : List ℕ := [f8,f5,f6,f7,f190]
def e470 : List ℕ := [f19,f65,f21,f22,f23,f24,f140]
def e471 : List ℕ := [f1,f258,f2,f3]
def e472 : List ℕ := [f19,f65,f21,f145,f22,f23,f24]
def e473 : List ℕ := [f19,f65,f21,f22,f23,f205,f24]
def e474 : List ℕ := [f19,f65,f21,f22,f206,f23,f24]
def e475 : List ℕ := [f19,f65,f21,f22,f24,f142]
def e476 : List ℕ := [f19,f65,f21,f22,f23,f142]
def e477 : List ℕ := [f19,f65,f21,f22,f23,f24,f142]
def e478 : List ℕ := [f157,f19,f65,f21,f22,f24]
def e479 : List ℕ := [f157,f19,f65,f21,f22,f23,f24]
def e480 : List ℕ := [f19,f65,f21,f22,f158,f23]
def e481 : List ℕ := [f19,f65,f21,f22,f158,f23,f24]
def e483 : List ℕ := [f260,f13,f11,f7]
def e491 : List ℕ := [f207,f36,f37,f265]
def e518 : List ℕ := [f18,f20,f65,f21,f22,f23,f24]
def e519 : List ℕ := [f18,f19,f65,f21,f22,f23,f24]
def e520 : List ℕ := [f64,f19,f65,f21,f22,f23,f24]
def e521 : List ℕ := [f233,f20,f65,f21,f22,f23,f24]
def e522 : List ℕ := [f233,f19,f20,f21,f22,f23,f24]
def e523 : List ℕ := [f239,f20,f65,f21,f22,f23,f24]
def e524 : List ℕ := [f20,f65,f21,f240,f22,f23,f24]
def e525 : List ℕ := [f19,f20,f65,f240,f22,f23,f24]
def e526 : List ℕ := [f241,f20,f65,f21,f22,f23,f24]
def e527 : List ℕ := [f20,f65,f242,f22,f23,f24]
def e528 : List ℕ := [f20,f65,f242,f21,f22,f23,f24]
def e529 : List ℕ := [f19,f20,f65,f242,f22,f23,f24]
def e530 : List ℕ := [f243,f20,f65,f21,f22,f23,f24]
def e536 : List ℕ := [f38,f34,f35,f244,f36,f37]
def e537 : List ℕ := [f20,f65,f21,f22,f245,f23,f24]
def e538 : List ℕ := [f19,f20,f65,f21,f245,f23,f24]
def e539 : List ℕ := [f246,f20,f65,f21,f22,f23,f24]
def e540 : List ℕ := [f41,f104,f273,f43]
def e541 : List ℕ := [f20,f65,f21,f247,f23,f24]
def e542 : List ℕ := [f20,f65,f21,f247,f22,f23,f24]
def e543 : List ℕ := [f19,f20,f65,f21,f247,f23,f24]
def e544 : List ℕ := [f248,f20,f65,f21,f22,f23,f24]
def e545 : List ℕ := [f20,f65,f21,f22,f23,f249,f24]
def e546 : List ℕ := [f19,f20,f65,f21,f22,f249,f24]
def e547 : List ℕ := [f250,f20,f65,f21,f22,f23,f24]
def e548 : List ℕ := [f20,f65,f21,f22,f251,f24]
def e549 : List ℕ := [f20,f65,f21,f22,f251,f23,f24]
def e550 : List ℕ := [f19,f20,f65,f21,f22,f251,f24]
def e551 : List ℕ := [f252,f20,f65,f21,f22,f23,f24]
def e552 : List ℕ := [f20,f65,f21,f22,f23,f24,f253]
def e553 : List ℕ := [f19,f20,f65,f21,f22,f23,f253]
def e554 : List ℕ := [f254,f20,f65,f21,f22,f23,f24]
def e555 : List ℕ := [f20,f65,f21,f22,f23,f255]
def e556 : List ℕ := [f20,f65,f21,f22,f23,f255,f24]
def e557 : List ℕ := [f19,f20,f65,f21,f22,f23,f255]
def e558 : List ℕ := [f64,f19,f20,f21,f22,f23,f24]
def e559 : List ℕ := [f66,f19,f65,f21,f22,f23,f24]
def e560 : List ℕ := [f19,f65,f21,f67,f22,f23,f24]
def e561 : List ℕ := [f19,f68,f65,f21,f22,f23,f24]
def e562 : List ℕ := [f19,f65,f69,f21,f22,f23,f24]
def e563 : List ℕ := [f71,f19,f65,f21,f22,f23,f24]
def e564 : List ℕ := [f19,f65,f21,f22,f72,f23,f24]
def e565 : List ℕ := [f19,f84,f65,f21,f22,f23,f24]
def e566 : List ℕ := [f19,f65,f21,f88,f22,f23,f24]
def e567 : List ℕ := [f89,f19,f65,f21,f22,f23,f24]
def e568 : List ℕ := [f19,f65,f21,f22,f23,f90,f24]
def e569 : List ℕ := [f19,f91,f65,f21,f22,f23,f24]
def e570 : List ℕ := [f19,f65,f21,f22,f92,f23,f24]
def e571 : List ℕ := [f93,f19,f65,f21,f22,f23,f24]
def e572 : List ℕ := [f19,f65,f21,f22,f23,f24,f94]
def e573 : List ℕ := [f19,f95,f65,f21,f22,f23,f24]
def e574 : List ℕ := [f19,f65,f21,f22,f23,f96,f24]
def e575 : List ℕ := [f97,f19,f20,f21,f22,f23,f24]
def e576 : List ℕ := [f19,f20,f21,f98,f22,f23,f24]
def e577 : List ℕ := [f19,f20,f99,f21,f22,f23,f24]
def e578 : List ℕ := [f19,f20,f100,f21,f22,f23,f24]
def e579 : List ℕ := [f101,f19,f20,f21,f22,f23,f24]
def e580 : List ℕ := [f13,f4,f11,f7]
def e581 : List ℕ := [f13,f4,f137,f7]
def e582 : List ℕ := [f19,f20,f21,f22,f102,f23,f24]
def e583 : List ℕ := [f19,f20,f114,f21,f22,f23,f24]
def e584 : List ℕ := [f19,f20,f21,f115,f22,f23,f24]
def e585 : List ℕ := [f116,f19,f20,f21,f22,f23,f24]
def e586 : List ℕ := [f19,f20,f21,f22,f23,f117,f24]
def e587 : List ℕ := [f19,f20,f118,f21,f22,f23,f24]
def e588 : List ℕ := [f19,f20,f21,f22,f119,f23,f24]
def e589 : List ℕ := [f120,f19,f20,f21,f22,f23,f24]
def e590 : List ℕ := [f19,f20,f21,f22,f23,f24,f121]
def e591 : List ℕ := [f19,f20,f122,f21,f22,f23,f24]
def e592 : List ℕ := [f19,f20,f21,f22,f23,f123,f24]
def e593 : List ℕ := [f19,f20,f65,f22,f136,f23,f24]
def e594 : List ℕ := [f19,f20,f65,f21,f136,f23,f24]
def e595 : List ℕ := [f144,f19,f20,f65,f22,f23,f24]
def e596 : List ℕ := [f19,f20,f65,f163,f21,f23,f24]
def e597 : List ℕ := [f19,f20,f65,f22,f23,f168,f24]
def e598 : List ℕ := [f19,f20,f65,f21,f22,f168,f24]
def e599 : List ℕ := [f19,f20,f65,f169,f22,f23,f24]
def e600 : List ℕ := [f19,f20,f65,f21,f22,f170,f24]
def e601 : List ℕ := [f19,f20,f65,f21,f22,f23,f173]
def e602 : List ℕ := [f19,f20,f65,f21,f22,f23,f176]
def e603 : List ℕ := [f19,f20,f65,f21,f23,f178,f24]
def e604 : List ℕ := [f19,f20,f65,f21,f179,f23,f24]
def e605 : List ℕ := [f19,f20,f65,f21,f22,f24,f142]
def e606 : List ℕ := [f19,f20,f65,f21,f22,f23,f142]
def e607 : List ℕ := [f157,f19,f20,f65,f21,f22,f24]
def e608 : List ℕ := [f19,f20,f65,f21,f22,f158,f23]
def e609 : List ℕ := [f19,f20,f65,f21,f22,f23,f24]
def e634 : List ℕ := [f239,f64,f20,f21,f22,f23,f24]
def e635 : List ℕ := [f20,f21,f282,f22,f23,f24]
def e636 : List ℕ := [f64,f20,f282,f22,f23,f24]
def e637 : List ℕ := [f64,f20,f21,f282,f22,f23,f24]
def e638 : List ℕ := [f283,f20,f21,f22,f23,f24]
def e639 : List ℕ := [f283,f64,f20,f21,f22,f23,f24]
def e640 : List ℕ := [f64,f20,f242,f22,f23,f24]
def e641 : List ℕ := [f64,f20,f242,f21,f22,f23,f24]
def e642 : List ℕ := [f243,f64,f20,f21,f22,f23,f24]
def e643 : List ℕ := [f64,f20,f21,f284,f23,f24]
def e644 : List ℕ := [f64,f20,f21,f22,f284,f23,f24]
def e645 : List ℕ := [f285,f64,f20,f21,f22,f23,f24]
def e646 : List ℕ := [f64,f20,f21,f247,f23,f24]
def e647 : List ℕ := [f64,f20,f21,f247,f22,f23,f24]
def e648 : List ℕ := [f248,f64,f20,f21,f22,f23,f24]
def e649 : List ℕ := [f20,f21,f22,f23,f286,f24]
def e650 : List ℕ := [f64,f20,f21,f22,f286,f24]
def e651 : List ℕ := [f64,f20,f21,f22,f23,f286,f24]
def e652 : List ℕ := [f287,f20,f21,f22,f23,f24]
def e653 : List ℕ := [f287,f64,f20,f21,f22,f23,f24]
def e654 : List ℕ := [f64,f20,f21,f22,f251,f24]
def e655 : List ℕ := [f64,f20,f21,f22,f251,f23,f24]
def e656 : List ℕ := [f252,f64,f20,f21,f22,f23,f24]
def e657 : List ℕ := [f64,f20,f21,f22,f23,f288]
def e658 : List ℕ := [f64,f20,f21,f22,f23,f24,f288]
def e659 : List ℕ := [f289,f64,f20,f21,f22,f23,f24]
def e660 : List ℕ := [f64,f20,f21,f22,f23,f255]
def e661 : List ℕ := [f64,f20,f21,f22,f23,f255,f24]
def e662 : List ℕ := [f66,f64,f20,f21,f22,f23,f24]
def e663 : List ℕ := [f64,f21,f67,f22,f23,f24]
def e664 : List ℕ := [f64,f20,f21,f67,f22,f23,f24]
def e665 : List ℕ := [f64,f68,f21,f22,f23,f24]
def e666 : List ℕ := [f64,f68,f20,f21,f22,f23,f24]
def e667 : List ℕ := [f64,f20,f69,f21,f22,f23,f24]
def e668 : List ℕ := [f290,f26,f70,f28]
def e669 : List ℕ := [f71,f64,f20,f21,f22,f23,f24]
def e674 : List ℕ := [f64,f20,f21,f22,f72,f23,f24]
def e675 : List ℕ := [f64,f84,f20,f21,f22,f23,f24]
def e676 : List ℕ := [f64,f20,f21,f88,f22,f23,f24]
def e677 : List ℕ := [f89,f64,f20,f21,f22,f23,f24]
def e678 : List ℕ := [f64,f21,f22,f23,f90,f24]
def e679 : List ℕ := [f64,f20,f21,f22,f23,f90,f24]
def e680 : List ℕ := [f64,f91,f21,f22,f23,f24]
def e681 : List ℕ := [f64,f91,f20,f21,f22,f23,f24]
def e682 : List ℕ := [f64,f20,f21,f22,f92,f23,f24]
def e683 : List ℕ := [f93,f64,f20,f21,f22,f23,f24]
def e684 : List ℕ := [f64,f20,f21,f22,f23,f24,f94]
def e685 : List ℕ := [f64,f95,f20,f21,f22,f23,f24]
def e686 : List ℕ := [f64,f20,f21,f22,f23,f96,f24]
def e687 : List ℕ := [f64,f20,f124,f21,f22,f23,f24]
def e688 : List ℕ := [f64,f20,f21,f136,f23,f24]
def e689 : List ℕ := [f64,f20,f21,f22,f136,f23,f24]
def e690 : List ℕ := [f64,f144,f20,f22,f23,f24]
def e691 : List ℕ := [f64,f144,f20,f21,f22,f23,f24]
def e692 : List ℕ := [f64,f20,f163,f21,f23,f24]
def e693 : List ℕ := [f64,f20,f163,f21,f22,f23,f24]
def e694 : List ℕ := [f64,f164,f20,f21,f22,f23,f24]
def e695 : List ℕ := [f64,f20,f22,f23,f168,f24]
def e696 : List ℕ := [f64,f20,f21,f22,f168,f24]
def e697 : List ℕ := [f64,f20,f21,f22,f23,f168,f24]
def e698 : List ℕ := [f64,f20,f169,f22,f23,f24]
def e699 : List ℕ := [f64,f20,f169,f21,f22,f23,f24]
def e700 : List ℕ := [f64,f20,f21,f22,f170,f24]
def e701 : List ℕ := [f64,f20,f21,f22,f170,f23,f24]
def e702 : List ℕ := [f171,f64,f20,f21,f22,f23,f24]
def e703 : List ℕ := [f64,f20,f21,f22,f23,f173]
def e704 : List ℕ := [f64,f20,f21,f22,f23,f24,f173]
def e705 : List ℕ := [f64,f20,f174,f21,f22,f23,f24]
def e706 : List ℕ := [f64,f20,f21,f22,f23,f176]
def e707 : List ℕ := [f64,f20,f21,f22,f23,f176,f24]
def e708 : List ℕ := [f177,f64,f20,f21,f22,f23,f24]
def e709 : List ℕ := [f64,f20,f21,f23,f178,f24]
def e710 : List ℕ := [f64,f20,f21,f22,f23,f178,f24]
def e711 : List ℕ := [f64,f20,f21,f179,f23,f24]
def e712 : List ℕ := [f64,f20,f21,f179,f22,f23,f24]
def e713 : List ℕ := [f64,f20,f21,f22,f180,f23,f24]
def e714 : List ℕ := [f181,f64,f20,f21,f22,f23,f24]
def e715 : List ℕ := [f8,f256,f193,f17,f190]
def e716 : List ℕ := [f64,f20,f21,f22,f23,f24,f140]
def e717 : List ℕ := [f64,f20,f21,f145,f22,f23,f24]
def e718 : List ℕ := [f64,f20,f21,f22,f23,f205,f24]
def e719 : List ℕ := [f64,f20,f21,f22,f206,f23,f24]
def e720 : List ℕ := [f64,f20,f21,f22,f24,f142]
def e721 : List ℕ := [f64,f20,f21,f22,f23,f142]
def e722 : List ℕ := [f64,f20,f21,f22,f23,f24,f142]
def e723 : List ℕ := [f64,f157,f20,f21,f22,f24]
def e724 : List ℕ := [f64,f157,f20,f21,f22,f23,f24]
def e725 : List ℕ := [f64,f20,f21,f22,f158,f23]
def e726 : List ℕ := [f64,f20,f21,f22,f158,f23,f24]
def e728 : List ℕ := [f66,f233,f19,f21,f22,f23,f24]
def e729 : List ℕ := [f19,f21,f291,f22,f23,f24]
def e730 : List ℕ := [f233,f19,f21,f291,f22,f23,f24]
def e731 : List ℕ := [f292,f19,f21,f22,f23,f24]
def e732 : List ℕ := [f292,f233,f19,f21,f22,f23,f24]
def e733 : List ℕ := [f233,f19,f69,f21,f22,f23,f24]
def e734 : List ℕ := [f71,f233,f19,f21,f22,f23,f24]
def e735 : List ℕ := [f260,f13,f234,f7]
def e736 : List ℕ := [f260,f13,f11,f234,f7]
def e737 : List ℕ := [f233,f19,f21,f22,f235,f23,f24]
def e738 : List ℕ := [f236,f233,f19,f21,f22,f23,f24]
def e739 : List ℕ := [f233,f19,f21,f88,f22,f23,f24]
def e740 : List ℕ := [f89,f233,f19,f21,f22,f23,f24]
def e741 : List ℕ := [f19,f21,f22,f23,f293,f24]
def e742 : List ℕ := [f233,f19,f21,f22,f23,f293,f24]
def e743 : List ℕ := [f294,f19,f21,f22,f23,f24]
def e744 : List ℕ := [f294,f233,f19,f21,f22,f23,f24]
def e745 : List ℕ := [f233,f19,f21,f22,f92,f23,f24]
def e746 : List ℕ := [f93,f233,f19,f21,f22,f23,f24]
def e747 : List ℕ := [f233,f19,f21,f22,f23,f24,f237]
def e748 : List ℕ := [f238,f233,f19,f21,f22,f23,f24]
def e749 : List ℕ := [f233,f19,f21,f22,f23,f96,f24]
def e750 : List ℕ := [f239,f233,f19,f21,f22,f23,f24]
def e751 : List ℕ := [f233,f21,f240,f22,f23,f24]
def e752 : List ℕ := [f233,f19,f240,f22,f23,f24]
def e753 : List ℕ := [f233,f19,f21,f240,f22,f23,f24]
def e754 : List ℕ := [f233,f241,f21,f22,f23,f24]
def e755 : List ℕ := [f233,f241,f19,f21,f22,f23,f24]
def e756 : List ℕ := [f233,f19,f242,f22,f23,f24]
def e757 : List ℕ := [f233,f19,f242,f21,f22,f23,f24]
def e758 : List ℕ := [f243,f233,f19,f21,f22,f23,f24]
def e759 : List ℕ := [f233,f19,f21,f22,f245,f23,f24]
def e760 : List ℕ := [f233,f246,f19,f21,f22,f23,f24]
def e761 : List ℕ := [f233,f19,f21,f247,f22,f23,f24]
def e762 : List ℕ := [f248,f233,f19,f21,f22,f23,f24]
def e763 : List ℕ := [f233,f21,f22,f23,f249,f24]
def e764 : List ℕ := [f233,f19,f21,f22,f249,f24]
def e765 : List ℕ := [f233,f19,f21,f22,f23,f249,f24]
def e766 : List ℕ := [f233,f250,f21,f22,f23,f24]
def e767 : List ℕ := [f233,f250,f19,f21,f22,f23,f24]
def e768 : List ℕ := [f233,f19,f21,f22,f251,f24]
def e769 : List ℕ := [f233,f19,f21,f22,f251,f23,f24]
def e770 : List ℕ := [f252,f233,f19,f21,f22,f23,f24]
def e771 : List ℕ := [f233,f19,f21,f22,f23,f24,f253]
def e772 : List ℕ := [f233,f254,f19,f21,f22,f23,f24]
def e773 : List ℕ := [f233,f19,f21,f22,f23,f255,f24]
def e774 : List ℕ := [f233,f19,f124,f21,f22,f23,f24]
def e775 : List ℕ := [f233,f19,f22,f136,f23,f24]
def e776 : List ℕ := [f233,f19,f21,f136,f23,f24]
def e777 : List ℕ := [f233,f19,f21,f22,f136,f23,f24]
def e778 : List ℕ := [f144,f233,f19,f22,f23,f24]
def e779 : List ℕ := [f144,f233,f19,f21,f22,f23,f24]
def e780 : List ℕ := [f233,f19,f163,f21,f23,f24]
def e781 : List ℕ := [f233,f19,f163,f21,f22,f23,f24]
def e782 : List ℕ := [f164,f233,f19,f21,f22,f23,f24]
def e783 : List ℕ := [f233,f19,f22,f23,f168,f24]
def e784 : List ℕ := [f233,f19,f21,f22,f168,f24]
def e785 : List ℕ := [f233,f19,f21,f22,f23,f168,f24]
def e786 : List ℕ := [f233,f19,f169,f22,f23,f24]
def e787 : List ℕ := [f233,f19,f169,f21,f22,f23,f24]
def e788 : List ℕ := [f233,f19,f21,f22,f170,f24]
def e789 : List ℕ := [f233,f19,f21,f22,f170,f23,f24]
def e790 : List ℕ := [f171,f233,f19,f21,f22,f23,f24]
def e791 : List ℕ := [f233,f19,f21,f22,f23,f173]
def e792 : List ℕ := [f233,f19,f21,f22,f23,f24,f173]
def e793 : List ℕ := [f233,f19,f174,f21,f22,f23,f24]
def e794 : List ℕ := [f233,f19,f21,f22,f23,f176]
def e795 : List ℕ := [f233,f19,f21,f22,f23,f176,f24]
def e796 : List ℕ := [f177,f233,f19,f21,f22,f23,f24]
def e797 : List ℕ := [f233,f19,f21,f23,f178,f24]
def e798 : List ℕ := [f233,f19,f21,f22,f23,f178,f24]
def e799 : List ℕ := [f233,f19,f21,f179,f23,f24]
def e800 : List ℕ := [f233,f19,f21,f179,f22,f23,f24]
def e801 : List ℕ := [f233,f19,f21,f22,f180,f23,f24]
def e802 : List ℕ := [f181,f233,f19,f21,f22,f23,f24]
def e803 : List ℕ := [f233,f19,f21,f22,f23,f24,f140]
def e804 : List ℕ := [f233,f19,f21,f145,f22,f23,f24]
def e805 : List ℕ := [f233,f19,f21,f22,f23,f205,f24]
def e806 : List ℕ := [f233,f19,f21,f22,f206,f23,f24]
def e807 : List ℕ := [f233,f19,f21,f22,f24,f142]
def e808 : List ℕ := [f233,f19,f21,f22,f23,f142]
def e809 : List ℕ := [f233,f19,f21,f22,f23,f24,f142]
def e810 : List ℕ := [f157,f233,f19,f21,f22,f24]
def e811 : List ℕ := [f157,f233,f19,f21,f22,f23,f24]
def e812 : List ℕ := [f233,f19,f21,f22,f158,f23]
def e813 : List ℕ := [f233,f19,f21,f22,f158,f23,f24]
def e814 : List ℕ := [f233,f18,f19,f21,f22,f23,f24]
def e815 : List ℕ := [f66,f19,f20,f21,f22,f23,f24]
def e816 : List ℕ := [f19,f20,f21,f291,f22,f23,f24]
def e817 : List ℕ := [f292,f19,f20,f21,f22,f23,f24]
def e818 : List ℕ := [f19,f20,f69,f21,f22,f23,f24]
def e819 : List ℕ := [f71,f19,f20,f21,f22,f23,f24]
def e822 : List ℕ := [f19,f20,f21,f22,f235,f23,f24]
def e823 : List ℕ := [f236,f19,f20,f21,f22,f23,f24]
def e824 : List ℕ := [f19,f20,f21,f88,f22,f23,f24]
def e825 : List ℕ := [f89,f19,f20,f21,f22,f23,f24]
def e826 : List ℕ := [f19,f20,f21,f22,f23,f293,f24]
def e827 : List ℕ := [f294,f19,f20,f21,f22,f23,f24]
def e828 : List ℕ := [f19,f20,f21,f22,f92,f23,f24]
def e829 : List ℕ := [f93,f19,f20,f21,f22,f23,f24]
def e830 : List ℕ := [f19,f20,f21,f22,f23,f24,f237]
def e831 : List ℕ := [f238,f19,f20,f21,f22,f23,f24]
def e832 : List ℕ := [f19,f20,f21,f22,f23,f96,f24]
def e833 : List ℕ := [f64,f233,f21,f22,f23,f24]
def e834 : List ℕ := [f64,f233,f20,f21,f22,f23,f24]
def e835 : List ℕ := [f64,f233,f19,f21,f22,f23,f24]
def e836 : List ℕ := [f233,f20,f21,f240,f22,f23,f24]
def e837 : List ℕ := [f233,f19,f20,f240,f22,f23,f24]
def e838 : List ℕ := [f233,f241,f20,f21,f22,f23,f24]
def e839 : List ℕ := [f233,f19,f20,f242,f22,f23,f24]
def e840 : List ℕ := [f233,f19,f20,f21,f245,f23,f24]
def e841 : List ℕ := [f233,f19,f20,f21,f247,f23,f24]
def e842 : List ℕ := [f233,f20,f21,f22,f23,f249,f24]
def e843 : List ℕ := [f233,f19,f20,f21,f22,f249,f24]
def e844 : List ℕ := [f233,f250,f20,f21,f22,f23,f24]
def e845 : List ℕ := [f233,f19,f20,f21,f22,f251,f24]
def e846 : List ℕ := [f233,f19,f20,f21,f22,f23,f253]
def e847 : List ℕ := [f233,f19,f20,f21,f22,f23,f255]
def e848 : List ℕ := [f233,f19,f21,f67,f22,f23,f24]
def e849 : List ℕ := [f233,f19,f68,f21,f22,f23,f24]
def e850 : List ℕ := [f260,f13,f11,f78,f7]
def e851 : List ℕ := [f233,f19,f21,f22,f72,f23,f24]
def e852 : List ℕ := [f233,f19,f84,f21,f22,f23,f24]
def e853 : List ℕ := [f233,f19,f21,f22,f23,f90,f24]
def e854 : List ℕ := [f233,f19,f91,f21,f22,f23,f24]
def e855 : List ℕ := [f233,f19,f21,f22,f23,f24,f94]
def e856 : List ℕ := [f233,f19,f95,f21,f22,f23,f24]
def e857 : List ℕ := [f233,f19,f20,f22,f136,f23,f24]
def e858 : List ℕ := [f233,f19,f20,f21,f136,f23,f24]
def e859 : List ℕ := [f144,f233,f19,f20,f22,f23,f24]
def e860 : List ℕ := [f233,f19,f20,f163,f21,f23,f24]
def e861 : List ℕ := [f233,f19,f20,f22,f23,f168,f24]
def e862 : List ℕ := [f233,f19,f20,f21,f22,f168,f24]
def e863 : List ℕ := [f233,f19,f20,f169,f22,f23,f24]
def e864 : List ℕ := [f233,f19,f20,f21,f22,f170,f24]
def e865 : List ℕ := [f233,f19,f20,f21,f22,f23,f173]
def e866 : List ℕ := [f233,f19,f20,f21,f22,f23,f176]
def e867 : List ℕ := [f233,f19,f20,f21,f23,f178,f24]
def e868 : List ℕ := [f233,f19,f20,f21,f179,f23,f24]
def e869 : List ℕ := [f233,f19,f20,f21,f22,f24,f142]
def e870 : List ℕ := [f233,f19,f20,f21,f22,f23,f142]
def e871 : List ℕ := [f157,f233,f19,f20,f21,f22,f24]
def e872 : List ℕ := [f233,f19,f20,f21,f22,f158,f23]
def e873 : List ℕ := [f239,f19,f20,f21,f22,f23,f24]
def e888 : List ℕ := [f66,f20,f21,f240,f22,f23,f24]
def e889 : List ℕ := [f20,f21,f240,f67,f22,f23,f24]
def e890 : List ℕ := [f68,f20,f21,f240,f22,f23,f24]
def e891 : List ℕ := [f20,f69,f21,f240,f22,f23,f24]
def e892 : List ℕ := [f299,f20,f21,f240,f22,f23,f24]
def e893 : List ℕ := [f20,f21,f240,f98,f22,f23,f24]
def e894 : List ℕ := [f292,f20,f21,f240,f22,f23,f24]
def e895 : List ℕ := [f20,f21,f300,f22,f23,f24]
def e896 : List ℕ := [f20,f21,f300,f240,f22,f23,f24]
def e897 : List ℕ := [f26,f70,f107,f28]
def e898 : List ℕ := [f71,f20,f21,f240,f22,f23,f24]
def e899 : List ℕ := [f13,f4,f78,f7]
def e900 : List ℕ := [f13,f4,f11,f78,f7]
def e901 : List ℕ := [f20,f21,f240,f22,f72,f23,f24]
def e902 : List ℕ := [f84,f20,f21,f240,f22,f23,f24]
def e903 : List ℕ := [f20,f21,f240,f88,f22,f23,f24]
def e904 : List ℕ := [f89,f20,f21,f240,f22,f23,f24]
def e905 : List ℕ := [f21,f240,f22,f23,f90,f24]
def e906 : List ℕ := [f20,f21,f240,f22,f23,f90,f24]
def e907 : List ℕ := [f91,f21,f240,f22,f23,f24]
def e908 : List ℕ := [f91,f20,f21,f240,f22,f23,f24]
def e909 : List ℕ := [f20,f21,f240,f22,f92,f23,f24]
def e910 : List ℕ := [f26,f70,f259]
def e911 : List ℕ := [f26,f70,f259,f28]
def e912 : List ℕ := [f93,f20,f21,f240,f22,f23,f24]
def e913 : List ℕ := [f13,f4,f11,f150]
def e914 : List ℕ := [f13,f4,f11,f7,f150]
def e915 : List ℕ := [f20,f21,f240,f22,f23,f24,f94]
def e916 : List ℕ := [f274,f1,f2,f3]
def e917 : List ℕ := [f95,f20,f21,f240,f22,f23,f24]
def e918 : List ℕ := [f1,f2,f273,f3]
def e919 : List ℕ := [f20,f21,f240,f22,f23,f96,f24]
def e920 : List ℕ := [f241,f20,f240,f22,f23,f24]
def e921 : List ℕ := [f241,f20,f21,f22,f23,f24]
def e922 : List ℕ := [f241,f20,f21,f240,f22,f23,f24]
def e923 : List ℕ := [f20,f124,f21,f240,f22,f23,f24]
def e924 : List ℕ := [f20,f21,f240,f136,f23,f24]
def e925 : List ℕ := [f20,f21,f240,f22,f136,f23,f24]
def e926 : List ℕ := [f144,f20,f21,f240,f22,f23,f24]
def e927 : List ℕ := [f20,f163,f21,f240,f23,f24]
def e928 : List ℕ := [f20,f163,f21,f240,f22,f23,f24]
def e929 : List ℕ := [f164,f20,f21,f240,f22,f23,f24]
def e946 : List ℕ := [f299,f20,f240,f22,f168,f24]
def e953 : List ℕ := [f300,f98,f22,f168,f24]
def e954 : List ℕ := [f20,f300,f22,f168,f24]
def e955 : List ℕ := [f98,f22,f72,f168,f24]
def e956 : List ℕ := [f84,f98,f22,f168,f24]
def e957 : List ℕ := [f309,f98,f22,f168,f24]
def e958 : List ℕ := [f98,f22,f310,f168,f24]
def e959 : List ℕ := [f98,f22,f168,f24,f94]
def e960 : List ℕ := [f95,f98,f22,f168,f24]
def e961 : List ℕ := [f20,f98,f168,f146,f24]
def e962 : List ℕ := [f20,f311,f98,f168,f24]
def e963 : List ℕ := [f20,f98,f22,f24,f312]
def e964 : List ℕ := [f20,f313,f98,f22,f24]
def e965 : List ℕ := [f20,f98,f22,f168,f24]
def e966 : List ℕ := [f20,f240,f98,f22,f168,f24]
def e967 : List ℕ := [f292,f20,f240,f22,f168,f24]
def e968 : List ℕ := [f20,f300,f240,f22,f168,f24]
def e969 : List ℕ := [f26,f166,f75,f111]
def e970 : List ℕ := [f71,f20,f240,f22,f168,f24]
def e974 : List ℕ := [f20,f240,f22,f72,f168,f24]
def e975 : List ℕ := [f84,f20,f240,f22,f168,f24]
def e976 : List ℕ := [f20,f240,f88,f22,f168,f24]
def e977 : List ℕ := [f309,f20,f240,f22,f168,f24]
def e978 : List ℕ := [f20,f240,f22,f168,f315,f24]
def e979 : List ℕ := [f316,f20,f240,f22,f168,f24]
def e980 : List ℕ := [f20,f240,f22,f310,f168,f24]
def e981 : List ℕ := [f93,f20,f240,f22,f168,f24]
def e982 : List ℕ := [f20,f240,f22,f168,f24,f94]
def e983 : List ℕ := [f95,f20,f240,f22,f168,f24]
def e984 : List ℕ := [f20,f240,f22,f168,f96,f24]
def e985 : List ℕ := [f20,f317,f240,f22,f168,f24]
def e986 : List ℕ := [f20,f240,f318,f168,f24]
def e987 : List ℕ := [f20,f240,f22,f318,f168,f24]
def e988 : List ℕ := [f319,f20,f240,f22,f168,f24]
def e989 : List ℕ := [f20,f320,f240,f168,f24]
def e990 : List ℕ := [f20,f320,f240,f22,f168,f24]
def e991 : List ℕ := [f20,f321,f240,f22,f168,f24]
def e992 : List ℕ := [f20,f240,f22,f168,f322,f24]
def e993 : List ℕ := [f323,f20,f240,f22,f168,f24]
def e994 : List ℕ := [f20,f240,f22,f324,f168,f24]
def e995 : List ℕ := [f325,f20,f240,f22,f168,f24]
def e996 : List ℕ := [f20,f240,f22,f168,f24,f326]
def e997 : List ℕ := [f20,f327,f240,f22,f168,f24]
def e998 : List ℕ := [f20,f240,f22,f168,f328,f24]
def e999 : List ℕ := [f20,f329,f240,f22,f168,f24]
def e1000 : List ℕ := [f20,f240,f168,f146,f24]
def e1001 : List ℕ := [f20,f240,f22,f168,f146,f24]
def e1002 : List ℕ := [f20,f311,f240,f168,f24]
def e1003 : List ℕ := [f20,f311,f240,f22,f168,f24]
def e1004 : List ℕ := [f20,f240,f22,f330,f168,f24]
def e1005 : List ℕ := [f181,f20,f240,f22,f168,f24]
def e1006 : List ℕ := [f20,f240,f22,f168,f24,f140]
def e1007 : List ℕ := [f20,f240,f145,f22,f168,f24]
def e1008 : List ℕ := [f20,f240,f22,f168,f205,f24]
def e1009 : List ℕ := [f20,f240,f22,f331,f168,f24]
def e1010 : List ℕ := [f20,f240,f22,f24,f312]
def e1011 : List ℕ := [f20,f240,f22,f168,f24,f312]
def e1012 : List ℕ := [f20,f313,f240,f22,f24]
def e1013 : List ℕ := [f20,f313,f240,f22,f168,f24]
def e1014 : List ℕ := [f20,f240,f22,f332,f168,f24]
def e1015 : List ℕ := [f20,f240,f22,f168,f24]
def e1016 : List ℕ := [f20,f240,f22,f23,f168,f24]
def e1017 : List ℕ := [f20,f21,f240,f22,f168,f24]
def e1018 : List ℕ := [f20,f21,f240,f22,f23,f168,f24]
def e1019 : List ℕ := [f20,f169,f240,f22,f23,f24]
def e1020 : List ℕ := [f20,f169,f21,f240,f22,f23,f24]
def e1021 : List ℕ := [f20,f21,f240,f22,f170,f24]
def e1022 : List ℕ := [f20,f21,f240,f22,f170,f23,f24]
def e1023 : List ℕ := [f171,f20,f21,f240,f22,f23,f24]
def e1024 : List ℕ := [f38,f50,f296,f52,f333]
def e1025 : List ℕ := [f20,f240,f22,f23,f24,f173]
def e1026 : List ℕ := [f20,f21,f240,f22,f23,f24,f173]
def e1027 : List ℕ := [f20,f174,f240,f22,f23,f24]
def e1028 : List ℕ := [f20,f174,f21,f240,f22,f23,f24]
def e1029 : List ℕ := [f20,f21,f240,f22,f23,f176,f24]
def e1030 : List ℕ := [f20,f317,f21,f240,f22,f23,f24]
def e1031 : List ℕ := [f20,f21,f240,f318,f23,f24]
def e1032 : List ℕ := [f20,f21,f240,f22,f318,f23,f24]
def e1033 : List ℕ := [f319,f20,f21,f240,f22,f23,f24]
def e1034 : List ℕ := [f20,f320,f21,f240,f23,f24]
def e1035 : List ℕ := [f20,f320,f21,f240,f22,f23,f24]
def e1036 : List ℕ := [f334,f20,f21,f240,f22,f23,f24]
def e1037 : List ℕ := [f20,f21,f22,f23,f322,f24]
def e1038 : List ℕ := [f20,f21,f240,f22,f322,f24]
def e1039 : List ℕ := [f20,f21,f240,f22,f23,f322,f24]
def e1040 : List ℕ := [f20,f21,f335,f22,f23,f24]
def e1041 : List ℕ := [f20,f21,f335,f240,f22,f23,f24]
def e1042 : List ℕ := [f20,f21,f240,f22,f324,f24]
def e1043 : List ℕ := [f20,f21,f240,f22,f324,f23,f24]
def e1044 : List ℕ := [f325,f20,f21,f240,f22,f23,f24]
def e1045 : List ℕ := [f20,f21,f240,f22,f23,f24,f326]
def e1046 : List ℕ := [f20,f21,f327,f240,f22,f23,f24]
def e1047 : List ℕ := [f20,f21,f240,f22,f23,f328,f24]
def e1048 : List ℕ := [f177,f20,f21,f240,f22,f23,f24]
def e1049 : List ℕ := [f20,f21,f240,f23,f178,f24]
def e1050 : List ℕ := [f20,f21,f240,f22,f23,f178,f24]
def e1051 : List ℕ := [f20,f21,f240,f179,f23,f24]
def e1052 : List ℕ := [f20,f21,f240,f179,f22,f23,f24]
def e1053 : List ℕ := [f20,f21,f240,f22,f180,f23,f24]
def e1054 : List ℕ := [f181,f20,f21,f240,f22,f23,f24]
def e1055 : List ℕ := [f20,f21,f240,f22,f23,f24,f140]
def e1056 : List ℕ := [f20,f21,f240,f145,f22,f23,f24]
def e1057 : List ℕ := [f1,f2,f336,f3]
def e1058 : List ℕ := [f20,f21,f240,f22,f23,f205,f24]
def e1059 : List ℕ := [f20,f21,f240,f22,f206,f23,f24]
def e1060 : List ℕ := [f20,f21,f240,f22,f24,f142]
def e1061 : List ℕ := [f20,f21,f240,f22,f23,f142]
def e1062 : List ℕ := [f20,f21,f240,f22,f23,f24,f142]
def e1063 : List ℕ := [f157,f20,f21,f240,f22,f24]
def e1064 : List ℕ := [f157,f20,f21,f240,f22,f23,f24]
def e1065 : List ℕ := [f20,f21,f240,f22,f158,f23]
def e1066 : List ℕ := [f20,f21,f240,f22,f158,f23,f24]
def e1067 : List ℕ := [f20,f21,f240,f22,f23,f24]
def e1068 : List ℕ := [f19,f20,f240,f22,f23,f24]
def e1069 : List ℕ := [f19,f20,f21,f240,f22,f23,f24]
def e1077 : List ℕ := [f18,f241,f20,f21,f22,f23,f24]
def e1078 : List ℕ := [f20,f342,f21,f22,f23,f24]
def e1079 : List ℕ := [f241,f342,f21,f22,f23,f24]
def e1080 : List ℕ := [f241,f20,f342,f21,f22,f23,f24]
def e1081 : List ℕ := [f283,f241,f20,f21,f22,f23,f24]
def e1082 : List ℕ := [f243,f241,f20,f21,f22,f23,f24]
def e1083 : List ℕ := [f241,f20,f21,f343,f23,f24]
def e1084 : List ℕ := [f241,f20,f21,f22,f343,f23,f24]
def e1085 : List ℕ := [f344,f241,f20,f21,f22,f23,f24]
def e1086 : List ℕ := [f241,f20,f21,f247,f23,f24]
def e1087 : List ℕ := [f241,f20,f21,f247,f22,f23,f24]
def e1088 : List ℕ := [f345,f241,f20,f21,f22,f23,f24]
def e1089 : List ℕ := [f20,f21,f22,f23,f346,f24]
def e1090 : List ℕ := [f241,f20,f21,f22,f346,f24]
def e1091 : List ℕ := [f241,f20,f21,f22,f23,f346,f24]
def e1092 : List ℕ := [f323,f20,f21,f22,f23,f24]
def e1093 : List ℕ := [f323,f241,f20,f21,f22,f23,f24]
def e1094 : List ℕ := [f241,f20,f21,f22,f347,f24]
def e1095 : List ℕ := [f241,f20,f21,f22,f347,f23,f24]
def e1096 : List ℕ := [f252,f241,f20,f21,f22,f23,f24]
def e1097 : List ℕ := [f241,f20,f21,f22,f23,f348]
def e1098 : List ℕ := [f241,f20,f21,f22,f23,f24,f348]
def e1099 : List ℕ := [f349,f241,f20,f21,f22,f23,f24]
def e1100 : List ℕ := [f241,f20,f21,f22,f23,f255]
def e1101 : List ℕ := [f241,f20,f21,f22,f23,f255,f24]
def e1102 : List ℕ := [f66,f241,f20,f21,f22,f23,f24]
def e1103 : List ℕ := [f241,f20,f21,f67,f22,f23,f24]
def e1104 : List ℕ := [f241,f68,f20,f21,f22,f23,f24]
def e1105 : List ℕ := [f241,f20,f69,f21,f22,f23,f24]
def e1106 : List ℕ := [f26,f350,f70,f28]
def e1107 : List ℕ := [f71,f241,f20,f21,f22,f23,f24]
def e1108 : List ℕ := [f241,f20,f21,f22,f72,f23,f24]
def e1109 : List ℕ := [f241,f84,f20,f21,f22,f23,f24]
def e1110 : List ℕ := [f241,f20,f21,f88,f22,f23,f24]
def e1111 : List ℕ := [f89,f241,f20,f21,f22,f23,f24]
def e1112 : List ℕ := [f241,f21,f22,f23,f90,f24]
def e1113 : List ℕ := [f241,f20,f21,f22,f23,f90,f24]
def e1114 : List ℕ := [f241,f91,f21,f22,f23,f24]
def e1115 : List ℕ := [f241,f91,f20,f21,f22,f23,f24]
def e1116 : List ℕ := [f241,f20,f21,f22,f92,f23,f24]
def e1117 : List ℕ := [f93,f241,f20,f21,f22,f23,f24]
def e1118 : List ℕ := [f241,f20,f21,f22,f23,f24,f94]
def e1119 : List ℕ := [f241,f95,f20,f21,f22,f23,f24]
def e1120 : List ℕ := [f241,f20,f21,f22,f23,f96,f24]
def e1121 : List ℕ := [f241,f20,f124,f21,f22,f23,f24]
def e1122 : List ℕ := [f241,f20,f22,f136,f23,f24]
def e1123 : List ℕ := [f241,f20,f21,f136,f23,f24]
def e1124 : List ℕ := [f241,f20,f21,f22,f136,f23,f24]
def e1125 : List ℕ := [f144,f241,f20,f22,f23,f24]
def e1126 : List ℕ := [f144,f241,f20,f21,f22,f23,f24]
def e1127 : List ℕ := [f241,f20,f163,f21,f23,f24]
def e1128 : List ℕ := [f241,f20,f163,f21,f22,f23,f24]
def e1129 : List ℕ := [f164,f241,f20,f21,f22,f23,f24]
def e1130 : List ℕ := [f241,f20,f22,f23,f168,f24]
def e1131 : List ℕ := [f241,f20,f21,f22,f168,f24]
def e1132 : List ℕ := [f241,f20,f21,f22,f23,f168,f24]
def e1133 : List ℕ := [f241,f20,f169,f22,f23,f24]
def e1134 : List ℕ := [f241,f20,f169,f21,f22,f23,f24]
def e1135 : List ℕ := [f241,f20,f21,f22,f170,f24]
def e1136 : List ℕ := [f241,f20,f21,f22,f170,f23,f24]
def e1137 : List ℕ := [f171,f241,f20,f21,f22,f23,f24]
def e1138 : List ℕ := [f241,f20,f21,f22,f23,f24,f173]
def e1139 : List ℕ := [f241,f20,f174,f21,f22,f23,f24]
def e1140 : List ℕ := [f241,f20,f21,f22,f23,f176,f24]
def e1141 : List ℕ := [f177,f241,f20,f21,f22,f23,f24]
def e1142 : List ℕ := [f241,f20,f21,f23,f178,f24]
def e1143 : List ℕ := [f241,f20,f21,f22,f23,f178,f24]
def e1144 : List ℕ := [f241,f20,f21,f179,f23,f24]
def e1145 : List ℕ := [f241,f20,f21,f179,f22,f23,f24]
def e1146 : List ℕ := [f241,f20,f21,f22,f180,f23,f24]
def e1147 : List ℕ := [f181,f241,f20,f21,f22,f23,f24]
def e1148 : List ℕ := [f241,f20,f21,f22,f23,f24,f140]
def e1149 : List ℕ := [f241,f20,f21,f145,f22,f23,f24]
def e1150 : List ℕ := [f241,f20,f21,f22,f23,f205,f24]
def e1151 : List ℕ := [f241,f20,f21,f22,f206,f23,f24]
def e1152 : List ℕ := [f241,f20,f21,f22,f24,f142]
def e1153 : List ℕ := [f241,f20,f21,f22,f23,f142]
def e1154 : List ℕ := [f241,f20,f21,f22,f23,f24,f142]
def e1155 : List ℕ := [f157,f241,f20,f21,f22,f24]
def e1156 : List ℕ := [f157,f241,f20,f21,f22,f23,f24]
def e1157 : List ℕ := [f241,f20,f21,f22,f158,f23]
def e1158 : List ℕ := [f241,f20,f21,f22,f158,f23,f24]
def e1159 : List ℕ := [f241,f19,f20,f21,f22,f23,f24]
def e1160 : List ℕ := [f19,f20,f242,f22,f23,f24]
def e1161 : List ℕ := [f19,f20,f242,f21,f22,f23,f24]
def e1162 : List ℕ := [f243,f19,f20,f21,f22,f23,f24]
def e1168 : List ℕ := [f18,f19,f20,f21,f245,f23,f24]
def e1169 : List ℕ := [f64,f19,f20,f21,f245,f23,f24]
def e1170 : List ℕ := [f239,f19,f20,f21,f245,f23,f24]
def e1171 : List ℕ := [f20,f21,f240,f245,f23,f24]
def e1172 : List ℕ := [f19,f20,f21,f240,f245,f23,f24]
def e1173 : List ℕ := [f241,f20,f21,f245,f23,f24]
def e1174 : List ℕ := [f241,f19,f20,f21,f245,f23,f24]
def e1175 : List ℕ := [f19,f20,f242,f21,f245,f23,f24]
def e1176 : List ℕ := [f74,f86,f352]
def e1177 : List ℕ := [f20,f21,f247,f245,f23,f24]
def e1178 : List ℕ := [f19,f20,f21,f247,f23,f24]
def e1179 : List ℕ := [f19,f20,f21,f247,f245,f23,f24]
def e1180 : List ℕ := [f248,f19,f20,f21,f245,f23,f24]
def e1181 : List ℕ := [f19,f20,f21,f245,f23,f249,f24]
def e1182 : List ℕ := [f250,f19,f20,f21,f245,f23,f24]
def e1183 : List ℕ := [f19,f20,f21,f245,f251,f23,f24]
def e1184 : List ℕ := [f252,f19,f20,f21,f245,f23,f24]
def e1197 : List ℕ := [f66,f20,f21,f245,f23,f253]
def e1198 : List ℕ := [f21,f67,f245,f23,f253]
def e1199 : List ℕ := [f20,f21,f67,f245,f23,f253]
def e1200 : List ℕ := [f68,f21,f245,f23,f253]
def e1201 : List ℕ := [f68,f20,f21,f245,f23,f253]
def e1202 : List ℕ := [f20,f69,f21,f245,f23,f253]
def e1203 : List ℕ := [f73,f74,f352]
def e1204 : List ℕ := [f355,f20,f21,f245,f23,f253]
def e1205 : List ℕ := [f4,f153,f154]
def e1206 : List ℕ := [f20,f21,f245,f102,f23,f253]
def e1207 : List ℕ := [f236,f20,f21,f245,f23,f253]
def e1208 : List ℕ := [f20,f21,f356,f245,f23,f253]
def e1209 : List ℕ := [f89,f20,f21,f245,f23,f253]
def e1210 : List ℕ := [f21,f245,f23,f90,f253]
def e1211 : List ℕ := [f20,f21,f245,f23,f90,f253]
def e1212 : List ℕ := [f91,f21,f245,f23,f253]
def e1213 : List ℕ := [f91,f20,f21,f245,f23,f253]
def e1214 : List ℕ := [f20,f21,f245,f92,f23,f253]
def e1215 : List ℕ := [f357,f20,f21,f245,f23,f253]
def e1216 : List ℕ := [f20,f21,f245,f23,f253,f121]
def e1217 : List ℕ := [f238,f20,f21,f245,f23,f253]
def e1218 : List ℕ := [f20,f21,f245,f23,f358,f253]
def e1219 : List ℕ := [f20,f359,f21,f245,f23,f253]
def e1220 : List ℕ := [f20,f21,f245,f318,f23,f253]
def e1221 : List ℕ := [f360,f20,f21,f245,f23,f253]
def e1222 : List ℕ := [f20,f361,f21,f245,f23,f253]
def e1223 : List ℕ := [f164,f20,f21,f245,f23,f253]
def e1224 : List ℕ := [f20,f245,f23,f168,f253]
def e1225 : List ℕ := [f20,f21,f245,f168,f253]
def e1226 : List ℕ := [f20,f21,f245,f23,f168,f253]
def e1227 : List ℕ := [f20,f169,f245,f23,f253]
def e1228 : List ℕ := [f20,f169,f21,f245,f23,f253]
def e1229 : List ℕ := [f20,f21,f245,f170,f253]
def e1230 : List ℕ := [f20,f21,f245,f170,f23,f253]
def e1231 : List ℕ := [f362,f20,f21,f245,f23,f253]
def e1232 : List ℕ := [f20,f21,f245,f23,f326]
def e1233 : List ℕ := [f20,f21,f245,f23,f253,f326]
def e1234 : List ℕ := [f20,f363,f21,f245,f23,f253]
def e1235 : List ℕ := [f20,f21,f245,f23,f364]
def e1236 : List ℕ := [f20,f21,f245,f23,f364,f253]
def e1237 : List ℕ := [f365,f20,f21,f245,f23,f253]
def e1238 : List ℕ := [f20,f21,f23,f366,f253]
def e1239 : List ℕ := [f20,f21,f245,f23,f366,f253]
def e1240 : List ℕ := [f20,f21,f367,f23,f253]
def e1241 : List ℕ := [f20,f21,f367,f245,f23,f253]
def e1242 : List ℕ := [f20,f21,f245,f368,f23,f253]
def e1244 : List ℕ := [f370,f20,f21,f245,f23,f253]
def e1245 : List ℕ := [f4,f153,f154,f371]
def e1246 : List ℕ := [f20,f21,f245,f23,f253,f372]
def e1247 : List ℕ := [f20,f21,f373,f245,f23,f253]
def e1248 : List ℕ := [f20,f21,f245,f23,f374,f253]
def e1249 : List ℕ := [f20,f21,f245,f375,f23,f253]
def e1250 : List ℕ := [f20,f21,f245,f23,f253,f376]
def e1251 : List ℕ := [f377,f20,f21,f245,f23,f253]
def e1252 : List ℕ := [f20,f21,f245,f378,f23,f253]
def e1253 : List ℕ := [f20,f21,f245,f23,f253]
def e1255 : List ℕ := [f380,f43,f381,f382]
def e1256 : List ℕ := [f21,f67,f245,f23,f24,f253]
def e1257 : List ℕ := [f257,f380,f43,f381]
def e1258 : List ℕ := [f68,f21,f245,f23,f24,f253]
def e1259 : List ℕ := [f21,f245,f23,f90,f24,f253]
def e1260 : List ℕ := [f91,f21,f245,f23,f24,f253]
def e1261 : List ℕ := [f93,f20,f21,f245,f23,f253]
def e1262 : List ℕ := [f20,f21,f245,f23,f253,f94]
def e1263 : List ℕ := [f95,f20,f21,f245,f23,f253]
def e1264 : List ℕ := [f20,f21,f245,f23,f96,f253]
def e1265 : List ℕ := [f20,f21,f318,f23,f24,f253]
def e1266 : List ℕ := [f20,f361,f21,f23,f24,f253]
def e1267 : List ℕ := [f20,f245,f23,f168,f24,f253]
def e1268 : List ℕ := [f20,f21,f245,f168,f24,f253]
def e1269 : List ℕ := [f20,f169,f245,f23,f24,f253]
def e1270 : List ℕ := [f20,f21,f245,f170,f24,f253]
def e1271 : List ℕ := [f171,f20,f21,f245,f23,f253]
def e1272 : List ℕ := [f20,f21,f245,f23,f253,f173]
def e1273 : List ℕ := [f20,f174,f21,f245,f23,f253]
def e1274 : List ℕ := [f20,f21,f245,f23,f176,f253]
def e1275 : List ℕ := [f20,f21,f245,f23,f24,f326]
def e1276 : List ℕ := [f20,f21,f245,f23,f24,f364]
def e1277 : List ℕ := [f20,f21,f23,f366,f24,f253]
def e1278 : List ℕ := [f20,f21,f367,f23,f24,f253]
def e1279 : List ℕ := [f383,f20,f21,f245,f23,f253]
def e1280 : List ℕ := [f20,f21,f384,f245,f23,f253]
def e1281 : List ℕ := [f370,f20,f21,f245,f23,f24]
def e1282 : List ℕ := [f20,f21,f373,f245,f23,f24]
def e1283 : List ℕ := [f20,f21,f245,f206,f23,f253]
def e1284 : List ℕ := [f108,f31,f385,f125]
def e1285 : List ℕ := [f20,f21,f245,f24,f142,f253]
def e1286 : List ℕ := [f20,f21,f245,f23,f142,f253]
def e1287 : List ℕ := [f157,f20,f21,f245,f253]
def e1288 : List ℕ := [f157,f20,f21,f245,f24,f253]
def e1289 : List ℕ := [f157,f20,f21,f245,f23,f253]
def e1290 : List ℕ := [f20,f21,f245,f158,f23,f253]
def e1291 : List ℕ := [f254,f20,f21,f245,f23,f253]
def e1292 : List ℕ := [f254,f20,f21,f245,f23,f24]
def e1293 : List ℕ := [f20,f21,f245,f23,f24,f253]
def e1294 : List ℕ := [f19,f20,f21,f245,f23,f253]
def e1295 : List ℕ := [f19,f20,f21,f245,f23,f24,f253]
def e1296 : List ℕ := [f254,f19,f20,f21,f245,f23,f24]
def e1297 : List ℕ := [f19,f20,f21,f245,f23,f255]
def e1298 : List ℕ := [f19,f20,f21,f245,f23,f255,f24]
def e1299 : List ℕ := [f66,f19,f20,f21,f245,f23,f24]
def e1300 : List ℕ := [f19,f21,f67,f245,f23,f24]
def e1301 : List ℕ := [f19,f20,f21,f67,f245,f23,f24]
def e1302 : List ℕ := [f19,f68,f21,f245,f23,f24]
def e1303 : List ℕ := [f19,f68,f20,f21,f245,f23,f24]
def e1304 : List ℕ := [f19,f20,f69,f21,f245,f23,f24]
def e1305 : List ℕ := [f355,f19,f20,f21,f245,f23,f24]
def e1306 : List ℕ := [f13,f4,f153,f7]
def e1307 : List ℕ := [f13,f4,f153,f137,f7]
def e1308 : List ℕ := [f19,f20,f21,f245,f102,f23,f24]
def e1309 : List ℕ := [f236,f19,f20,f21,f245,f23,f24]
def e1310 : List ℕ := [f19,f20,f21,f356,f245,f23,f24]
def e1311 : List ℕ := [f89,f19,f20,f21,f245,f23,f24]
def e1312 : List ℕ := [f19,f21,f245,f23,f90,f24]
def e1313 : List ℕ := [f19,f20,f21,f245,f23,f90,f24]
def e1314 : List ℕ := [f19,f91,f21,f245,f23,f24]
def e1315 : List ℕ := [f19,f91,f20,f21,f245,f23,f24]
def e1316 : List ℕ := [f19,f20,f21,f245,f92,f23,f24]
def e1317 : List ℕ := [f93,f19,f20,f21,f245,f23,f24]
def e1318 : List ℕ := [f19,f20,f21,f245,f23,f24,f94]
def e1319 : List ℕ := [f19,f95,f20,f21,f245,f23,f24]
def e1320 : List ℕ := [f19,f20,f21,f245,f23,f96,f24]
def e1321 : List ℕ := [f19,f20,f359,f21,f245,f23,f24]
def e1322 : List ℕ := [f19,f20,f21,f318,f23,f24]
def e1323 : List ℕ := [f19,f20,f21,f245,f318,f23,f24]
def e1324 : List ℕ := [f360,f19,f20,f21,f245,f23,f24]
def e1325 : List ℕ := [f19,f20,f361,f21,f23,f24]
def e1326 : List ℕ := [f19,f20,f361,f21,f245,f23,f24]
def e1327 : List ℕ := [f164,f19,f20,f21,f245,f23,f24]
def e1328 : List ℕ := [f19,f20,f245,f23,f168,f24]
def e1329 : List ℕ := [f19,f20,f21,f245,f168,f24]
def e1330 : List ℕ := [f19,f20,f21,f245,f23,f168,f24]
def e1331 : List ℕ := [f19,f20,f169,f245,f23,f24]
def e1332 : List ℕ := [f19,f20,f169,f21,f245,f23,f24]
def e1333 : List ℕ := [f19,f20,f21,f245,f170,f24]
def e1334 : List ℕ := [f19,f20,f21,f245,f170,f23,f24]
def e1335 : List ℕ := [f171,f19,f20,f21,f245,f23,f24]
def e1336 : List ℕ := [f19,f20,f21,f245,f23,f173]
def e1337 : List ℕ := [f19,f20,f21,f245,f23,f24,f173]
def e1338 : List ℕ := [f19,f20,f174,f21,f245,f23,f24]
def e1339 : List ℕ := [f19,f20,f21,f245,f23,f176]
def e1340 : List ℕ := [f19,f20,f21,f245,f23,f176,f24]
def e1341 : List ℕ := [f365,f19,f20,f21,f245,f23,f24]
def e1342 : List ℕ := [f19,f20,f21,f23,f366,f24]
def e1343 : List ℕ := [f19,f20,f21,f245,f23,f366,f24]
def e1344 : List ℕ := [f19,f20,f21,f367,f23,f24]
def e1345 : List ℕ := [f19,f20,f21,f367,f245,f23,f24]
def e1346 : List ℕ := [f19,f20,f21,f245,f368,f23,f24]
def e1347 : List ℕ := [f383,f19,f20,f21,f245,f23,f24]
def e1348 : List ℕ := [f13,f4,f153,f7,f371]
def e1349 : List ℕ := [f19,f20,f21,f245,f23,f24,f372]
def e1350 : List ℕ := [f19,f20,f21,f384,f245,f23,f24]
def e1351 : List ℕ := [f19,f20,f21,f245,f23,f374,f24]
def e1352 : List ℕ := [f19,f20,f21,f245,f206,f23,f24]
def e1353 : List ℕ := [f19,f20,f21,f245,f24,f142]
def e1354 : List ℕ := [f19,f20,f21,f245,f23,f142]
def e1355 : List ℕ := [f19,f20,f21,f245,f23,f24,f142]
def e1356 : List ℕ := [f157,f19,f20,f21,f245,f24]
def e1357 : List ℕ := [f157,f19,f20,f21,f245,f23,f24]
def e1358 : List ℕ := [f19,f20,f21,f245,f158,f23]
def e1359 : List ℕ := [f19,f20,f21,f245,f158,f23,f24]
def e1360 : List ℕ := [f19,f20,f21,f245,f23,f24]
def e1361 : List ℕ := [f64,f20,f21,f22,f245,f23,f24]
def e1362 : List ℕ := [f20,f21,f240,f22,f245,f23,f24]
def e1363 : List ℕ := [f19,f20,f240,f22,f245,f23,f24]
def e1364 : List ℕ := [f241,f20,f21,f22,f245,f23,f24]
def e1365 : List ℕ := [f19,f20,f242,f22,f245,f23,f24]
def e1366 : List ℕ := [f243,f20,f21,f22,f245,f23,f24]
def e1367 : List ℕ := [f243,f19,f20,f21,f245,f23,f24]
def e1368 : List ℕ := [f246,f19,f20,f21,f245,f23,f24]
def e1369 : List ℕ := [f20,f21,f247,f22,f245,f23,f24]
def e1370 : List ℕ := [f19,f20,f21,f247,f22,f23,f24]
def e1371 : List ℕ := [f20,f21,f22,f245,f249,f24]
def e1372 : List ℕ := [f20,f21,f22,f245,f23,f249,f24]
def e1373 : List ℕ := [f19,f20,f21,f22,f245,f249,f24]
def e1374 : List ℕ := [f250,f20,f21,f22,f245,f23,f24]
def e1375 : List ℕ := [f19,f20,f21,f22,f245,f251,f24]
def e1376 : List ℕ := [f20,f21,f22,f245,f23,f253]
def e1377 : List ℕ := [f144,f20,f245,f23,f24,f253]
def e1378 : List ℕ := [f30,f106,f31,f125]
def e1379 : List ℕ := [f20,f22,f318,f23,f24,f253]
def e1380 : List ℕ := [f181,f20,f21,f245,f23,f253]
def e1381 : List ℕ := [f20,f21,f245,f23,f253,f140]
def e1382 : List ℕ := [f20,f21,f145,f245,f23,f253]
def e1383 : List ℕ := [f20,f21,f245,f23,f205,f253]
def e1384 : List ℕ := [f20,f21,f22,f23,f374,f253]
def e1385 : List ℕ := [f370,f20,f21,f22,f23,f24]
def e1386 : List ℕ := [f157,f20,f21,f22,f245,f253]
def e1387 : List ℕ := [f20,f21,f22,f245,f24,f376]
def e1388 : List ℕ := [f20,f21,f22,f245,f23,f24,f253]
def e1389 : List ℕ := [f19,f20,f21,f22,f245,f23,f253]
def e1390 : List ℕ := [f254,f20,f21,f22,f245,f23,f24]
def e1391 : List ℕ := [f19,f20,f21,f22,f245,f23,f255]
def e1392 : List ℕ := [f19,f21,f67,f22,f245,f23,f24]
def e1393 : List ℕ := [f19,f68,f21,f22,f245,f23,f24]
def e1394 : List ℕ := [f71,f19,f20,f21,f245,f23,f24]
def e1395 : List ℕ := [f13,f4,f153,f78,f7]
def e1396 : List ℕ := [f19,f20,f21,f245,f72,f23,f24]
def e1397 : List ℕ := [f19,f84,f20,f21,f245,f23,f24]
def e1398 : List ℕ := [f19,f20,f21,f88,f245,f23,f24]
def e1399 : List ℕ := [f355,f19,f20,f21,f22,f23,f24]
def e1400 : List ℕ := [f19,f20,f21,f22,f356,f23,f24]
def e1401 : List ℕ := [f19,f21,f22,f245,f23,f90,f24]
def e1402 : List ℕ := [f19,f91,f21,f22,f245,f23,f24]
def e1403 : List ℕ := [f19,f20,f124,f21,f245,f23,f24]
def e1404 : List ℕ := [f19,f20,f22,f136,f245,f23,f24]
def e1405 : List ℕ := [f19,f20,f21,f136,f245,f23,f24]
def e1406 : List ℕ := [f144,f19,f20,f245,f23,f24]
def e1407 : List ℕ := [f144,f19,f20,f22,f245,f23,f24]
def e1408 : List ℕ := [f144,f19,f20,f21,f245,f23,f24]
def e1409 : List ℕ := [f19,f20,f163,f21,f245,f23,f24]
def e1410 : List ℕ := [f19,f20,f359,f21,f22,f23,f24]
def e1411 : List ℕ := [f19,f20,f22,f318,f23,f24]
def e1412 : List ℕ := [f185,f219,f222,f220,f221]
def e1413 : List ℕ := [f19,f20,f22,f245,f318,f23,f24]
def e1414 : List ℕ := [f19,f20,f21,f22,f318,f23,f24]
def e1415 : List ℕ := [f360,f19,f20,f22,f23,f24]
def e1416 : List ℕ := [f360,f19,f20,f22,f245,f23,f24]
def e1417 : List ℕ := [f360,f19,f20,f21,f22,f23,f24]
def e1418 : List ℕ := [f19,f20,f361,f21,f22,f23,f24]
def e1419 : List ℕ := [f19,f20,f22,f245,f23,f168,f24]
def e1420 : List ℕ := [f19,f20,f21,f22,f245,f168,f24]
def e1421 : List ℕ := [f19,f20,f169,f22,f245,f23,f24]
def e1422 : List ℕ := [f19,f20,f21,f22,f245,f170,f24]
def e1423 : List ℕ := [f19,f20,f21,f22,f245,f23,f173]
def e1424 : List ℕ := [f19,f20,f21,f22,f245,f23,f176]
def e1425 : List ℕ := [f246,f19,f20,f21,f22,f23,f24]
def e1426 : List ℕ := [f177,f19,f20,f21,f245,f23,f24]
def e1427 : List ℕ := [f19,f20,f21,f245,f23,f178,f24]
def e1428 : List ℕ := [f19,f20,f21,f179,f245,f23,f24]
def e1429 : List ℕ := [f19,f20,f21,f245,f180,f23,f24]
def e1430 : List ℕ := [f181,f19,f20,f21,f245,f23,f24]
def e1431 : List ℕ := [f19,f20,f21,f245,f23,f24,f140]
def e1432 : List ℕ := [f19,f20,f21,f145,f245,f23,f24]
def e1433 : List ℕ := [f19,f20,f21,f245,f23,f205,f24]
def e1434 : List ℕ := [f365,f19,f20,f21,f22,f23,f24]
def e1435 : List ℕ := [f19,f20,f21,f22,f23,f366,f24]
def e1436 : List ℕ := [f19,f20,f21,f22,f367,f23,f24]
def e1437 : List ℕ := [f19,f20,f21,f22,f368,f23,f24]
def e1438 : List ℕ := [f383,f19,f20,f21,f22,f23,f24]
def e1439 : List ℕ := [f13,f4,f11,f7,f371]
def e1440 : List ℕ := [f19,f20,f21,f22,f23,f24,f372]
def e1441 : List ℕ := [f19,f20,f21,f22,f384,f23,f24]
def e1442 : List ℕ := [f19,f20,f21,f22,f23,f374,f24]
def e1443 : List ℕ := [f19,f20,f21,f22,f245,f24,f142]
def e1444 : List ℕ := [f19,f20,f21,f22,f245,f23,f142]
def e1445 : List ℕ := [f157,f19,f20,f21,f22,f245,f24]
def e1446 : List ℕ := [f19,f20,f21,f22,f245,f158,f23]
def e1447 : List ℕ := [f19,f20,f21,f22,f245,f23,f24]
def e1465 : List ℕ := [f18,f19,f20,f21,f247,f23,f24]
def e1466 : List ℕ := [f64,f19,f20,f21,f247,f23,f24]
def e1467 : List ℕ := [f239,f19,f20,f21,f247,f23,f24]
def e1468 : List ℕ := [f20,f21,f240,f247,f23,f24]
def e1469 : List ℕ := [f19,f20,f21,f240,f247,f23,f24]
def e1470 : List ℕ := [f241,f19,f20,f21,f247,f23,f24]
def e1471 : List ℕ := [f19,f20,f242,f21,f247,f23,f24]
def e1472 : List ℕ := [f248,f19,f20,f21,f247,f23,f24]
def e1473 : List ℕ := [f20,f21,f247,f23,f249,f24]
def e1474 : List ℕ := [f19,f20,f21,f247,f23,f249,f24]
def e1475 : List ℕ := [f250,f20,f21,f247,f23,f24]
def e1476 : List ℕ := [f250,f19,f20,f21,f247,f23,f24]
def e1477 : List ℕ := [f19,f20,f21,f247,f251,f23,f24]
def e1478 : List ℕ := [f252,f19,f20,f21,f247,f23,f24]
def e1479 : List ℕ := [f19,f20,f21,f247,f23,f253]
def e1480 : List ℕ := [f19,f20,f21,f247,f23,f24,f253]
def e1481 : List ℕ := [f254,f19,f20,f21,f247,f23,f24]
def e1482 : List ℕ := [f19,f20,f21,f247,f23,f255]
def e1483 : List ℕ := [f19,f20,f21,f247,f23,f255,f24]
def e1484 : List ℕ := [f66,f19,f20,f21,f247,f23,f24]
def e1485 : List ℕ := [f19,f21,f67,f247,f23,f24]
def e1486 : List ℕ := [f19,f20,f21,f67,f247,f23,f24]
def e1487 : List ℕ := [f19,f68,f21,f247,f23,f24]
def e1488 : List ℕ := [f19,f68,f20,f21,f247,f23,f24]
def e1489 : List ℕ := [f19,f20,f69,f21,f247,f23,f24]
def e1490 : List ℕ := [f73,f74,f86]
def e1491 : List ℕ := [f71,f19,f20,f21,f247,f23,f24]
def e1492 : List ℕ := [f13,f4,f389,f7]
def e1493 : List ℕ := [f13,f4,f6,f389,f7]
def e1494 : List ℕ := [f19,f20,f21,f247,f390,f23,f24]
def e1495 : List ℕ := [f19,f84,f20,f21,f247,f23,f24]
def e1496 : List ℕ := [f19,f20,f21,f115,f247,f23,f24]
def e1497 : List ℕ := [f89,f19,f20,f21,f247,f23,f24]
def e1498 : List ℕ := [f19,f21,f247,f23,f90,f24]
def e1499 : List ℕ := [f19,f20,f21,f247,f23,f90,f24]
def e1500 : List ℕ := [f19,f91,f21,f247,f23,f24]
def e1501 : List ℕ := [f19,f91,f20,f21,f247,f23,f24]
def e1502 : List ℕ := [f19,f20,f21,f247,f92,f23,f24]
def e1503 : List ℕ := [f93,f19,f20,f21,f247,f23,f24]
def e1504 : List ℕ := [f19,f20,f21,f247,f23,f24,f94]
def e1505 : List ℕ := [f19,f95,f20,f21,f247,f23,f24]
def e1506 : List ℕ := [f19,f20,f21,f247,f23,f96,f24]
def e1507 : List ℕ := [f19,f20,f124,f21,f247,f23,f24]
def e1508 : List ℕ := [f19,f20,f247,f391,f23,f24]
def e1509 : List ℕ := [f19,f20,f21,f391,f23,f24]
def e1510 : List ℕ := [f19,f20,f21,f247,f391,f23,f24]
def e1511 : List ℕ := [f144,f19,f20,f247,f23,f24]
def e1512 : List ℕ := [f144,f19,f20,f21,f247,f23,f24]
def e1513 : List ℕ := [f19,f20,f320,f21,f23,f24]
def e1514 : List ℕ := [f19,f20,f320,f21,f247,f23,f24]
def e1515 : List ℕ := [f164,f19,f20,f21,f247,f23,f24]
def e1516 : List ℕ := [f19,f20,f247,f23,f168,f24]
def e1517 : List ℕ := [f19,f20,f21,f247,f168,f24]
def e1518 : List ℕ := [f19,f20,f21,f247,f23,f168,f24]
def e1519 : List ℕ := [f19,f20,f169,f247,f23,f24]
def e1520 : List ℕ := [f19,f20,f169,f21,f247,f23,f24]
def e1521 : List ℕ := [f19,f20,f21,f247,f170,f24]
def e1522 : List ℕ := [f19,f20,f21,f247,f170,f23,f24]
def e1523 : List ℕ := [f171,f19,f20,f21,f247,f23,f24]
def e1524 : List ℕ := [f19,f20,f21,f247,f23,f173]
def e1525 : List ℕ := [f19,f20,f21,f247,f23,f24,f173]
def e1526 : List ℕ := [f19,f20,f174,f21,f247,f23,f24]
def e1527 : List ℕ := [f19,f20,f21,f247,f23,f176]
def e1528 : List ℕ := [f19,f20,f21,f247,f23,f176,f24]
def e1529 : List ℕ := [f177,f19,f20,f21,f247,f23,f24]
def e1530 : List ℕ := [f19,f20,f21,f23,f392,f24]
def e1531 : List ℕ := [f19,f20,f21,f247,f23,f392,f24]
def e1532 : List ℕ := [f19,f20,f21,f393,f23,f24]
def e1533 : List ℕ := [f19,f20,f21,f393,f247,f23,f24]
def e1534 : List ℕ := [f19,f20,f21,f247,f180,f23,f24]
def e1535 : List ℕ := [f181,f19,f20,f21,f247,f23,f24]
def e1536 : List ℕ := [f13,f4,f6,f7,f190]
def e1537 : List ℕ := [f19,f20,f21,f247,f23,f24,f394]
def e1538 : List ℕ := [f19,f20,f21,f373,f247,f23,f24]
def e1539 : List ℕ := [f19,f20,f21,f247,f23,f205,f24]
def e1540 : List ℕ := [f19,f20,f21,f247,f206,f23,f24]
def e1541 : List ℕ := [f19,f20,f21,f247,f24,f142]
def e1542 : List ℕ := [f19,f20,f21,f247,f23,f142]
def e1543 : List ℕ := [f19,f20,f21,f247,f23,f24,f142]
def e1544 : List ℕ := [f157,f19,f20,f21,f247,f24]
def e1545 : List ℕ := [f157,f19,f20,f21,f247,f23,f24]
def e1546 : List ℕ := [f19,f20,f21,f247,f158,f23]
def e1547 : List ℕ := [f19,f20,f21,f247,f158,f23,f24]
def e1548 : List ℕ := [f20,f21,f240,f247,f22,f23,f24]
def e1549 : List ℕ := [f19,f20,f240,f247,f22,f23,f24]
def e1550 : List ℕ := [f19,f20,f242,f247,f22,f23,f24]
def e1551 : List ℕ := [f243,f19,f20,f21,f247,f23,f24]
def e1552 : List ℕ := [f246,f20,f21,f247,f22,f23,f24]
def e1553 : List ℕ := [f246,f19,f20,f21,f247,f23,f24]
def e1554 : List ℕ := [f20,f21,f247,f22,f23,f249,f24]
def e1555 : List ℕ := [f19,f20,f21,f247,f22,f249,f24]
def e1556 : List ℕ := [f250,f20,f21,f247,f22,f23,f24]
def e1557 : List ℕ := [f19,f20,f21,f247,f22,f251,f24]
def e1558 : List ℕ := [f252,f20,f21,f247,f22,f23,f24]
def e1559 : List ℕ := [f19,f20,f21,f247,f22,f23,f253]
def e1560 : List ℕ := [f26,f70,f75,f28]
def e1561 : List ℕ := [f20,f21,f247,f22,f23,f255,f24]
def e1562 : List ℕ := [f19,f20,f21,f247,f22,f23,f255]
def e1563 : List ℕ := [f19,f21,f67,f247,f22,f23,f24]
def e1564 : List ℕ := [f19,f68,f21,f247,f22,f23,f24]
def e1565 : List ℕ := [f13,f4,f11,f389,f7]
def e1566 : List ℕ := [f19,f20,f21,f22,f390,f23,f24]
def e1567 : List ℕ := [f19,f84,f20,f21,f22,f23,f24]
def e1568 : List ℕ := [f13,f4,f6,f78,f7]
def e1569 : List ℕ := [f19,f20,f21,f247,f72,f23,f24]
def e1570 : List ℕ := [f19,f20,f21,f88,f247,f23,f24]
def e1571 : List ℕ := [f19,f21,f247,f22,f23,f90,f24]
def e1572 : List ℕ := [f19,f91,f21,f247,f22,f23,f24]
def e1573 : List ℕ := [f19,f20,f124,f21,f22,f23,f24]
def e1574 : List ℕ := [f19,f20,f22,f391,f23,f24]
def e1575 : List ℕ := [f19,f20,f247,f22,f391,f23,f24]
def e1576 : List ℕ := [f19,f20,f21,f22,f391,f23,f24]
def e1577 : List ℕ := [f144,f19,f20,f22,f23,f24]
def e1578 : List ℕ := [f144,f19,f20,f247,f22,f23,f24]
def e1579 : List ℕ := [f144,f19,f20,f21,f22,f23,f24]
def e1580 : List ℕ := [f19,f20,f320,f21,f22,f23,f24]
def e1581 : List ℕ := [f19,f20,f247,f22,f136,f23,f24]
def e1582 : List ℕ := [f19,f20,f21,f247,f136,f23,f24]
def e1583 : List ℕ := [f19,f20,f163,f21,f247,f23,f24]
def e1584 : List ℕ := [f19,f20,f247,f22,f23,f168,f24]
def e1585 : List ℕ := [f19,f20,f21,f247,f22,f168,f24]
def e1586 : List ℕ := [f19,f20,f169,f247,f22,f23,f24]
def e1587 : List ℕ := [f19,f20,f21,f247,f22,f170,f24]
def e1588 : List ℕ := [f19,f20,f21,f247,f22,f23,f173]
def e1589 : List ℕ := [f19,f20,f21,f247,f22,f23,f176]
def e1590 : List ℕ := [f177,f19,f20,f21,f22,f23,f24]
def e1591 : List ℕ := [f19,f20,f21,f22,f23,f392,f24]
def e1592 : List ℕ := [f19,f20,f21,f393,f22,f23,f24]
def e1593 : List ℕ := [f19,f20,f21,f22,f180,f23,f24]
def e1594 : List ℕ := [f181,f19,f20,f21,f22,f23,f24]
def e1595 : List ℕ := [f13,f4,f11,f7,f190]
def e1596 : List ℕ := [f19,f20,f21,f22,f23,f24,f394]
def e1597 : List ℕ := [f19,f20,f21,f373,f22,f23,f24]
def e1598 : List ℕ := [f19,f20,f21,f22,f23,f205,f24]
def e1599 : List ℕ := [f19,f20,f21,f247,f23,f178,f24]
def e1600 : List ℕ := [f19,f20,f21,f179,f247,f23,f24]
def e1601 : List ℕ := [f19,f20,f21,f247,f23,f24,f140]
def e1602 : List ℕ := [f19,f20,f21,f145,f247,f23,f24]
def e1603 : List ℕ := [f19,f20,f21,f247,f22,f24,f142]
def e1604 : List ℕ := [f19,f20,f21,f247,f22,f23,f142]
def e1605 : List ℕ := [f157,f19,f20,f21,f247,f22,f24]
def e1606 : List ℕ := [f19,f20,f21,f247,f22,f158,f23]
def e1607 : List ℕ := [f248,f19,f20,f21,f22,f23,f24]
def e1608 : List ℕ := [f20,f21,f22,f23,f249,f24]
def e1609 : List ℕ := [f19,f20,f21,f22,f249,f24]
def e1610 : List ℕ := [f19,f20,f21,f22,f23,f249,f24]
def e1611 : List ℕ := [f250,f20,f21,f22,f23,f24]
def e1612 : List ℕ := [f250,f19,f20,f21,f22,f23,f24]
def e1613 : List ℕ := [f19,f20,f21,f22,f251,f24]
def e1614 : List ℕ := [f19,f20,f21,f22,f251,f23,f24]
def e1615 : List ℕ := [f252,f19,f20,f21,f22,f23,f24]
def e1616 : List ℕ := [f19,f20,f21,f22,f23,f253]
def e1617 : List ℕ := [f19,f20,f21,f22,f23,f24,f253]
def e1618 : List ℕ := [f254,f19,f20,f21,f22,f23,f24]
def e1619 : List ℕ := [f19,f20,f21,f22,f23,f255]
def e1620 : List ℕ := [f19,f20,f21,f22,f23,f255,f24]
def e1621 : List ℕ := [f19,f21,f67,f22,f23,f24]
def e1622 : List ℕ := [f19,f20,f21,f67,f22,f23,f24]
def e1623 : List ℕ := [f19,f68,f21,f22,f23,f24]
def e1624 : List ℕ := [f19,f68,f20,f21,f22,f23,f24]
def e1679 : List ℕ := [f418,f4,f11,f7]
def e1680 : List ℕ := [f419,f20,f21,f22,f23,f24]
def e1681 : List ℕ := [f19,f419,f20,f21,f22,f23,f24]
def e1682 : List ℕ := [f71,f419,f20,f21,f22,f23,f24]
def e1683 : List ℕ := [f40,f13,f113,f11,f7]
def e1684 : List ℕ := [f71,f19,f84,f21,f22,f23,f24]
def e1685 : List ℕ := [f19,f20,f420,f22,f23,f24]
def e1686 : List ℕ := [f19,f20,f21,f420,f22,f23,f24]
def e1687 : List ℕ := [f71,f19,f20,f420,f22,f23,f24]
def e1688 : List ℕ := [f71,f19,f20,f21,f88,f23,f24]
def e1703 : List ℕ := [f20,f65,f21,f22,f424,f24]
def e1704 : List ℕ := [f19,f65,f21,f22,f424,f24]
def e1705 : List ℕ := [f64,f20,f21,f22,f424,f24]
def e1706 : List ℕ := [f233,f19,f21,f22,f424,f24]
def e1707 : List ℕ := [f20,f21,f240,f22,f424,f24]
def e1708 : List ℕ := [f19,f20,f240,f22,f424,f24]
def e1709 : List ℕ := [f241,f20,f21,f22,f424,f24]
def e1710 : List ℕ := [f19,f20,f242,f22,f424,f24]
def e1711 : List ℕ := [f19,f20,f21,f245,f424,f24]
def e1712 : List ℕ := [f19,f20,f21,f247,f424,f24]
def e1713 : List ℕ := [f38,f35,f36,f423,f425]
def e1714 : List ℕ := [f20,f21,f22,f424,f426,f24]
def e1715 : List ℕ := [f30,f106,f31,f111]
def e1716 : List ℕ := [f19,f20,f21,f22,f426,f24]
def e1717 : List ℕ := [f422,f350,f70,f28]
def e1718 : List ℕ := [f250,f20,f21,f22,f424,f24]
def e1719 : List ℕ := [f30,f106,f203,f31]
def e1720 : List ℕ := [f19,f20,f21,f22,f427,f24]
def e1721 : List ℕ := [f19,f20,f21,f22,f424,f253]
def e1722 : List ℕ := [f19,f20,f21,f22,f424,f255]
def e1723 : List ℕ := [f19,f21,f67,f22,f424,f24]
def e1724 : List ℕ := [f19,f68,f21,f22,f424,f24]
def e1725 : List ℕ := [f40,f13,f11,f78,f7]
def e1726 : List ℕ := [f19,f21,f22,f72,f424,f24]
def e1727 : List ℕ := [f19,f20,f21,f72,f424,f24]
def e1728 : List ℕ := [f19,f84,f21,f22,f424,f24]
def e1729 : List ℕ := [f19,f20,f21,f88,f424,f24]
def e1730 : List ℕ := [f19,f21,f22,f424,f90,f24]
def e1731 : List ℕ := [f19,f428,f21,f22,f424,f24]
def e1732 : List ℕ := [f93,f19,f21,f22,f424,f24]
def e1733 : List ℕ := [f19,f21,f22,f424,f96,f24]
def e1734 : List ℕ := [f19,f20,f22,f136,f424,f24]
def e1735 : List ℕ := [f19,f20,f21,f136,f424,f24]
def e1736 : List ℕ := [f144,f19,f20,f22,f424,f24]
def e1737 : List ℕ := [f19,f20,f163,f21,f424,f24]
def e1738 : List ℕ := [f19,f20,f22,f424,f429,f24]
def e1739 : List ℕ := [f19,f20,f21,f22,f429,f24]
def e1740 : List ℕ := [f19,f20,f169,f22,f424,f24]
def e1741 : List ℕ := [f19,f20,f21,f22,f430,f24]
def e1742 : List ℕ := [f19,f20,f21,f22,f424,f173]
def e1743 : List ℕ := [f19,f20,f21,f22,f424,f176]
def e1744 : List ℕ := [f19,f20,f21,f424,f178,f24]
def e1745 : List ℕ := [f19,f20,f21,f431,f424,f24]
def e1746 : List ℕ := [f181,f19,f20,f21,f424,f24]
def e1747 : List ℕ := [f19,f20,f21,f424,f205,f24]
def e1748 : List ℕ := [f26,f166,f75,f148]
def e1749 : List ℕ := [f19,f20,f21,f22,f24,f432]
def e1750 : List ℕ := [f38,f207,f35,f423,f433]
def e1751 : List ℕ := [f19,f20,f21,f22,f424,f432]
def e1752 : List ℕ := [f290,f26,f166,f75]
def e1753 : List ℕ := [f434,f19,f20,f21,f22,f24]
def e1754 : List ℕ := [f435,f38,f207,f35,f423]
def e1755 : List ℕ := [f19,f20,f21,f22,f158,f424]
def e1756 : List ℕ := [f19,f20,f21,f22,f424,f24]
def e1757 : List ℕ := [f19,f20,f21,f22,f23,f424,f24]
def e1758 : List ℕ := [f71,f19,f20,f21,f22,f424,f24]
def e1776 : List ℕ := [f38,f207,f50,f51]
def e1777 : List ℕ := [f38,f207,f50,f51,f438]
def e1778 : List ℕ := [f19,f20,f21,f22,f23,f439]
def e1779 : List ℕ := [f38,f207,f50,f51,f52]
def e1780 : List ℕ := [f38,f207,f50,f51,f52,f438]
def e1781 : List ℕ := [f19,f20,f21,f22,f23,f24,f439]
def e1782 : List ℕ := [f71,f19,f20,f21,f22,f23,f439]
def e1783 : List ℕ := [f71,f19,f20,f240,f22,f23,f24]
def e1784 : List ℕ := [f71,f19,f20,f242,f22,f23,f24]
def e1785 : List ℕ := [f71,f20,f21,f22,f23,f249,f24]
def e1786 : List ℕ := [f71,f19,f20,f21,f22,f249,f24]
def e1787 : List ℕ := [f71,f250,f20,f21,f22,f23,f24]
def e1788 : List ℕ := [f71,f19,f20,f21,f22,f251,f24]
def e1789 : List ℕ := [f71,f19,f20,f21,f22,f23,f253]
def e1790 : List ℕ := [f71,f19,f20,f21,f22,f23,f255]
def e1791 : List ℕ := [f71,f19,f21,f67,f22,f23,f24]
def e1792 : List ℕ := [f71,f19,f68,f21,f22,f23,f24]
def e1793 : List ℕ := [f71,f19,f21,f22,f72,f23,f24]
def e1794 : List ℕ := [f71,f19,f20,f21,f72,f23,f24]
def e1795 : List ℕ := [f71,f19,f21,f22,f23,f90,f24]
def e1796 : List ℕ := [f71,f19,f91,f21,f22,f23,f24]
def e1797 : List ℕ := [f71,f93,f19,f21,f22,f23,f24]
def e1798 : List ℕ := [f71,f19,f21,f22,f23,f96,f24]
def e1799 : List ℕ := [f71,f19,f20,f22,f136,f23,f24]
def e1800 : List ℕ := [f71,f19,f20,f21,f136,f23,f24]
def e1801 : List ℕ := [f71,f144,f19,f20,f22,f23,f24]
def e1802 : List ℕ := [f71,f19,f20,f163,f21,f23,f24]
def e1803 : List ℕ := [f71,f19,f20,f22,f23,f168,f24]
def e1804 : List ℕ := [f71,f19,f20,f21,f22,f168,f24]
def e1805 : List ℕ := [f71,f19,f20,f169,f22,f23,f24]
def e1806 : List ℕ := [f71,f19,f20,f21,f22,f170,f24]
def e1807 : List ℕ := [f71,f19,f20,f21,f22,f23,f173]
def e1808 : List ℕ := [f71,f19,f20,f21,f22,f23,f176]
def e1809 : List ℕ := [f71,f19,f20,f21,f23,f178,f24]
def e1810 : List ℕ := [f71,f19,f20,f21,f179,f23,f24]
def e1811 : List ℕ := [f71,f181,f19,f20,f21,f23,f24]
def e1812 : List ℕ := [f71,f19,f20,f21,f23,f205,f24]
def e1813 : List ℕ := [f71,f19,f20,f21,f22,f24,f142]
def e1814 : List ℕ := [f71,f19,f20,f21,f22,f23,f142]
def e1815 : List ℕ := [f71,f157,f19,f20,f21,f22,f24]
def e1816 : List ℕ := [f71,f19,f20,f21,f22,f158,f23]
def e1817 : List ℕ := [f19,f20,f240,f22,f72,f23,f24]
def e1818 : List ℕ := [f19,f20,f242,f22,f72,f23,f24]
def e1819 : List ℕ := [f440,f19,f20,f21,f22,f23,f24]
def e1820 : List ℕ := [f285,f19,f20,f21,f22,f23,f24]
def e1822 : List ℕ := [f19,f20,f21,f22,f441,f23,f24]
def e1823 : List ℕ := [f20,f21,f22,f72,f23,f249,f24]
def e1824 : List ℕ := [f19,f20,f21,f22,f72,f249,f24]
def e1825 : List ℕ := [f250,f20,f21,f22,f72,f23,f24]
def e1826 : List ℕ := [f19,f20,f21,f22,f72,f251,f24]
def e1827 : List ℕ := [f19,f20,f21,f22,f72,f23,f253]
def e1828 : List ℕ := [f19,f20,f21,f22,f72,f23,f255]
def e1829 : List ℕ := [f19,f21,f67,f22,f72,f23,f24]
def e1830 : List ℕ := [f19,f68,f21,f22,f72,f23,f24]
def e1831 : List ℕ := [f19,f84,f20,f21,f72,f23,f24]
def e1832 : List ℕ := [f19,f21,f88,f22,f72,f23,f24]
def e1833 : List ℕ := [f19,f21,f22,f72,f23,f90,f24]
def e1834 : List ℕ := [f19,f91,f21,f22,f72,f23,f24]
def e1842 : List ℕ := [f207,f46,f37,f265]
def e1843 : List ℕ := [f207,f35,f46,f37,f265]
def e1844 : List ℕ := [f207,f35,f36,f37,f265]
def e1845 : List ℕ := [f207,f46,f36,f37,f265]
def e1846 : List ℕ := [f207,f35,f46,f36,f37,f265]
def e1847 : List ℕ := [f19,f21,f22,f72,f23,f24,f94]
def e1852 : List ℕ := [f13,f138,f78,f7]
def e1853 : List ℕ := [f13,f138,f11,f78,f7]
def e1854 : List ℕ := [f19,f95,f21,f22,f72,f23,f24]
def e1855 : List ℕ := [f19,f20,f136,f72,f23,f24]
def e1856 : List ℕ := [f19,f20,f22,f136,f72,f23,f24]
def e1857 : List ℕ := [f19,f20,f21,f136,f72,f23,f24]
def e1858 : List ℕ := [f144,f19,f20,f22,f72,f23,f24]
def e1859 : List ℕ := [f19,f20,f163,f21,f72,f23,f24]
def e1860 : List ℕ := [f19,f20,f445,f21,f22,f23,f24]
def e1861 : List ℕ := [f19,f20,f21,f22,f446,f23,f24]
def e1862 : List ℕ := [f447,f19,f20,f21,f22,f23,f24]
def e1863 : List ℕ := [f19,f20,f448,f21,f22,f23,f24]
def e1864 : List ℕ := [f19,f20,f22,f72,f23,f168,f24]
def e1865 : List ℕ := [f19,f20,f21,f22,f72,f168,f24]
def e1866 : List ℕ := [f19,f20,f169,f22,f72,f23,f24]
def e1867 : List ℕ := [f19,f20,f21,f22,f72,f170,f24]
def e1868 : List ℕ := [f19,f20,f21,f22,f72,f23,f173]
def e1869 : List ℕ := [f19,f20,f21,f22,f72,f23,f176]
def e1870 : List ℕ := [f19,f20,f21,f72,f23,f178,f24]
def e1871 : List ℕ := [f19,f20,f21,f179,f72,f23,f24]
def e1872 : List ℕ := [f19,f20,f21,f72,f23,f24,f140]
def e1873 : List ℕ := [f19,f20,f21,f145,f72,f23,f24]
def e1874 : List ℕ := [f449,f19,f20,f21,f22,f24]
def e1875 : List ℕ := [f449,f19,f20,f21,f22,f23,f24]
def e1876 : List ℕ := [f9,f26,f166,f75]
def e1877 : List ℕ := [f449,f19,f20,f21,f22,f72,f24]
def e1878 : List ℕ := [f19,f20,f21,f22,f23,f450,f24]
def e1879 : List ℕ := [f26,f70,f166,f75]
def e1880 : List ℕ := [f19,f20,f21,f22,f451,f24]
def e1881 : List ℕ := [f30,f48,f106,f31]
def e1882 : List ℕ := [f19,f20,f21,f22,f451,f23,f24]
def e1883 : List ℕ := [f19,f20,f21,f22,f451,f72,f24]
def e1884 : List ℕ := [f19,f20,f21,f22,f452,f23,f24]
def e1885 : List ℕ := [f453,f19,f20,f21,f22,f23]
def e1886 : List ℕ := [f453,f19,f20,f21,f22,f23,f24]
def e1887 : List ℕ := [f453,f19,f20,f21,f22,f72,f23]
def e1888 : List ℕ := [f1,f2,f3,f454]
def e1889 : List ℕ := [f19,f20,f21,f22,f23,f24,f141]
def e1890 : List ℕ := [f19,f20,f21,f22,f455,f23]
def e1891 : List ℕ := [f1,f2,f380]
def e1892 : List ℕ := [f1,f2,f380,f3]
def e1893 : List ℕ := [f19,f20,f21,f22,f455,f23,f24]
def e1894 : List ℕ := [f19,f20,f21,f22,f455,f72,f23]
def e1895 : List ℕ := [f19,f20,f21,f22,f23,f456,f24]
def e1896 : List ℕ := [f19,f20,f21,f22,f72,f24,f142]
def e1897 : List ℕ := [f19,f20,f21,f22,f72,f23,f142]
def e1898 : List ℕ := [f157,f19,f20,f21,f22,f72,f24]
def e1899 : List ℕ := [f19,f20,f21,f22,f72,f158,f23]
def e1900 : List ℕ := [f19,f20,f21,f22,f72,f23,f24]
def e1947 : List ℕ := [f462,f4,f11,f7]
def e1948 : List ℕ := [f20,f463,f21,f22,f23,f24]
def e1949 : List ℕ := [f84,f20,f463,f21,f22,f23,f24]
def e1950 : List ℕ := [f19,f20,f463,f21,f22,f23,f24]
def e1951 : List ℕ := [f19,f84,f20,f240,f22,f23,f24]
def e1952 : List ℕ := [f19,f84,f20,f242,f22,f23,f24]
def e1953 : List ℕ := [f84,f20,f21,f22,f23,f249,f24]
def e1954 : List ℕ := [f19,f84,f20,f21,f22,f249,f24]
def e1955 : List ℕ := [f250,f84,f20,f21,f22,f23,f24]
def e1956 : List ℕ := [f19,f84,f20,f21,f22,f251,f24]
def e1957 : List ℕ := [f19,f84,f20,f21,f22,f23,f253]
def e1958 : List ℕ := [f19,f84,f20,f21,f22,f23,f255]
def e1959 : List ℕ := [f19,f20,f21,f464,f22,f23,f24]
def e1960 : List ℕ := [f19,f465,f20,f21,f22,f23,f24]
def e1961 : List ℕ := [f19,f20,f21,f22,f23,f466,f24]
def e1962 : List ℕ := [f19,f428,f20,f21,f22,f23,f24]
def e1963 : List ℕ := [f1,f2,f3,f467]
def e1964 : List ℕ := [f19,f20,f21,f22,f23,f24,f468]
def e1965 : List ℕ := [f19,f197,f20,f21,f22,f23,f24]
def e1966 : List ℕ := [f19,f84,f21,f67,f22,f23,f24]
def e1967 : List ℕ := [f19,f84,f68,f21,f22,f23,f24]
def e1968 : List ℕ := [f0,f257,f2,f3]
def e1969 : List ℕ := [f19,f84,f21,f88,f22,f23,f24]
def e1970 : List ℕ := [f19,f84,f20,f21,f88,f23,f24]
def e1971 : List ℕ := [f19,f84,f21,f22,f23,f90,f24]
def e1972 : List ℕ := [f19,f84,f91,f21,f22,f23,f24]
def e1973 : List ℕ := [f19,f84,f21,f22,f23,f24,f94]
def e1974 : List ℕ := [f274,f0,f2,f3]
def e1975 : List ℕ := [f19,f95,f84,f21,f22,f23,f24]
def e1976 : List ℕ := [f19,f84,f20,f22,f136,f23,f24]
def e1977 : List ℕ := [f19,f84,f20,f21,f136,f23,f24]
def e1978 : List ℕ := [f144,f19,f84,f20,f22,f23,f24]
def e1979 : List ℕ := [f19,f84,f20,f163,f21,f23,f24]
def e1980 : List ℕ := [f19,f84,f20,f22,f23,f168,f24]
def e1981 : List ℕ := [f19,f84,f20,f21,f22,f168,f24]
def e1982 : List ℕ := [f19,f84,f20,f169,f22,f23,f24]
def e1983 : List ℕ := [f19,f84,f20,f21,f22,f170,f24]
def e1984 : List ℕ := [f19,f84,f20,f21,f22,f23,f173]
def e1985 : List ℕ := [f19,f84,f20,f21,f22,f23,f176]
def e1986 : List ℕ := [f19,f84,f20,f21,f23,f178,f24]
def e1987 : List ℕ := [f19,f84,f20,f21,f179,f23,f24]
def e1988 : List ℕ := [f181,f19,f84,f20,f21,f23,f24]
def e1989 : List ℕ := [f19,f84,f20,f21,f23,f205,f24]
def e1990 : List ℕ := [f19,f84,f20,f21,f22,f24,f142]
def e1991 : List ℕ := [f19,f84,f20,f21,f22,f23,f142]
def e1992 : List ℕ := [f157,f19,f84,f20,f21,f22,f24]
def e1993 : List ℕ := [f19,f84,f20,f21,f22,f158,f23]
def e1994 : List ℕ := [f19,f21,f22,f23,f90,f24]
def e1995 : List ℕ := [f19,f20,f21,f22,f23,f90,f24]
def e1996 : List ℕ := [f19,f91,f21,f22,f23,f24]
def e1997 : List ℕ := [f19,f91,f20,f21,f22,f23,f24]
def e1998 : List ℕ := [f19,f20,f21,f22,f23,f24,f94]
def e1999 : List ℕ := [f19,f95,f20,f21,f22,f23,f24]
def e2000 : List ℕ := [f19,f20,f22,f136,f23,f24]
def e2001 : List ℕ := [f19,f20,f21,f136,f23,f24]
def e2002 : List ℕ := [f19,f20,f21,f22,f136,f23,f24]
def e2003 : List ℕ := [f19,f20,f163,f21,f23,f24]
def e2004 : List ℕ := [f19,f20,f163,f21,f22,f23,f24]
def e2005 : List ℕ := [f164,f19,f20,f21,f22,f23,f24]
def e2006 : List ℕ := [f19,f20,f22,f23,f168,f24]
def e2007 : List ℕ := [f19,f20,f21,f22,f168,f24]
def e2008 : List ℕ := [f19,f20,f21,f22,f23,f168,f24]
def e2009 : List ℕ := [f19,f20,f169,f22,f23,f24]
def e2010 : List ℕ := [f19,f20,f169,f21,f22,f23,f24]
def e2011 : List ℕ := [f19,f20,f21,f22,f170,f24]
def e2012 : List ℕ := [f19,f20,f21,f22,f170,f23,f24]
def e2013 : List ℕ := [f171,f19,f20,f21,f22,f23,f24]
def e2014 : List ℕ := [f19,f20,f21,f22,f23,f173]
def e2015 : List ℕ := [f19,f20,f21,f22,f23,f24,f173]
def e2016 : List ℕ := [f19,f20,f174,f21,f22,f23,f24]
def e2017 : List ℕ := [f19,f20,f21,f22,f23,f176]
def e2018 : List ℕ := [f19,f20,f21,f22,f23,f176,f24]
def e2019 : List ℕ := [f19,f20,f21,f23,f178,f24]
def e2020 : List ℕ := [f19,f20,f21,f22,f23,f178,f24]
def e2021 : List ℕ := [f19,f20,f21,f179,f23,f24]
def e2022 : List ℕ := [f19,f20,f21,f179,f22,f23,f24]
def e2023 : List ℕ := [f19,f20,f21,f22,f23,f24,f140]
def e2024 : List ℕ := [f19,f20,f21,f145,f22,f23,f24]
def e2025 : List ℕ := [f19,f20,f21,f22,f206,f23,f24]
def e2026 : List ℕ := [f19,f20,f21,f22,f24,f142]
def e2027 : List ℕ := [f19,f20,f21,f22,f23,f142]
def e2028 : List ℕ := [f19,f20,f21,f22,f23,f24,f142]
def e2029 : List ℕ := [f157,f19,f20,f21,f22,f24]
def e2030 : List ℕ := [f157,f19,f20,f21,f22,f23,f24]
def e2031 : List ℕ := [f19,f20,f21,f22,f158,f23]
def e2032 : List ℕ := [f19,f20,f21,f22,f158,f23,f24]
def e2033 : List ℕ := [f19,f20,f21,f22,f23,f24]
theorem b0:B 12 3 e0:=viaSmall (by decide +kernel) (by decide)
theorem b9:B 20 4 e9:=viaSmall (by decide +kernel) (by decide)
theorem b16:B 12 3 e16:=viaSmall (by decide +kernel) (by decide)
theorem w17:W 12 3 e16:=widen (by decide +kernel) b16
theorem b18:B 87 7 e17:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b37:B 35 5 e35:=viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b38:B 35 5 e36:=viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b39:B 35 5 e37:=viaSmall (by decide +kernel) (by decide)
theorem b54:B 87 6 e51:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b55:B 87 6 e52:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b56:B 87 6 e53:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b57:B 87 6 e54:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b58:B 35 5 e55:=viaSmall (by decide +kernel) (by decide)
theorem w59:W 35 5 e55:=widen (by decide +kernel) b58
theorem b60:B 87 6 e56:=viaCut pjt_2 w59 (by decide) (by decide +kernel) (by decide +kernel)
theorem b61:B 87 6 e57:=viaCut pjt_2 w59 (by decide) (by decide +kernel) (by decide +kernel)
theorem b62:B 87 6 e58:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b63:B 16 3 e59:=viaSmall (by decide +kernel) (by decide)
theorem w64:W 16 3 e59:=widen (by decide +kernel) b63
theorem b65:B 87 6 e60:=viaCut pjt_13 w64 (by decide) (by decide +kernel) (by decide +kernel)
theorem w66:W 35 5 e35:=widen (by decide +kernel) b37
theorem b67:B 87 6 e61:=viaCut pjt_1 w66 (by decide) (by decide +kernel) (by decide +kernel)
theorem b68:B 6 2 e62:=viaSmall (by decide +kernel) (by decide)
theorem b76:B 20 4 e65:=viaSmall (by decide +kernel) (by decide)
theorem b77:B 20 4 e66:=viaSmall (by decide +kernel) (by decide)
theorem b79:B 20 4 e68:=viaPerm pc6_1 pci6_1 b76 (by decide +kernel) (by decide +kernel)
theorem b80:B 20 4 e69:=viaPerm pc6_1 pci6_1 b77 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b85:B 35 5 e74:=viaSmall (by decide +kernel) (by decide)
theorem w86:W 35 5 e36:=viaSub (ws:=[e74,e35,e36]) (consBan b85 (consBan b37 (consBan b38 (nilBan _ _)))) (by decide) (by decide +kernel)
theorem b87:B 87 6 e75:=viaCut pjt_1 w86 (by decide) (by decide +kernel) (by decide +kernel)
theorem w88:W 35 5 e37:=widen (by decide +kernel) b39
theorem b89:B 87 6 e76:=viaCut pjt_1 w88 (by decide) (by decide +kernel) (by decide +kernel)
theorem b90:B 6 2 e62:=viaSmall (by decide +kernel) (by decide)
theorem b93:B 16 3 e78:=viaSmall (by decide +kernel) (by decide)
theorem b94:B 16 3 e79:=viaSmall (by decide +kernel) (by decide)
theorem w95:W 16 3 e79:=viaSub (ws:=[e78,e79]) (consBan b93 (consBan b94 (nilBan _ _))) (by decide) (by decide +kernel)
theorem b96:B 87 6 e80:=viaCut pjt_12 w95 (by decide) (by decide +kernel) (by decide +kernel)
theorem b97:B 87 6 e81:=viaCut pjt_13 w64 (by decide) (by decide +kernel) (by decide +kernel)
theorem b98:B 87 6 e82:=viaPerm pt0 pti0 b57 (by decide +kernel) (by decide +kernel)
theorem b99:B 87 6 e83:=viaPerm pt0 pti0 b60 (by decide +kernel) (by decide +kernel)
theorem b100:B 87 6 e84:=viaPerm pt0 pti0 b61 (by decide +kernel) (by decide +kernel)
theorem b101:B 87 6 e85:=viaPerm pt0 pti0 b62 (by decide +kernel) (by decide +kernel)
theorem b102:B 87 6 e86:=viaPerm pt0 pti0 b65 (by decide +kernel) (by decide +kernel)
theorem b103:B 87 6 e87:=viaPerm pt0 pti0 b67 (by decide +kernel) (by decide +kernel)
theorem b104:B 87 6 e88:=viaPerm pt0 pti0 b87 (by decide +kernel) (by decide +kernel)
theorem b105:B 87 6 e89:=viaPerm pt0 pti0 b89 (by decide +kernel) (by decide +kernel)
theorem b106:B 87 6 e90:=viaPerm pt0 pti0 b96 (by decide +kernel) (by decide +kernel)
theorem b107:B 87 6 e91:=viaPerm pt0 pti0 b97 (by decide +kernel) (by decide +kernel)
theorem b108:B 87 6 e92:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b109:B 87 6 e93:=viaCut pjt_2 w59 (by decide) (by decide +kernel) (by decide +kernel)
theorem b110:B 87 6 e94:=viaCut pjt_2 w59 (by decide) (by decide +kernel) (by decide +kernel)
theorem b111:B 87 6 e95:=viaCut pjt_2 w59 (by decide) (by decide +kernel) (by decide +kernel)
theorem b112:B 87 6 e96:=viaCut pjt_2 w59 (by decide) (by decide +kernel) (by decide +kernel)
theorem b113:B 87 6 e97:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b114:B 87 6 e98:=viaCut pjt_13 w64 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b115:B 35 5 e99:=viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b116:B 35 5 e100:=viaSmall (by decide +kernel) (by decide)
theorem w117:W 35 5 e100:=viaSub (ws:=[e74,e99,e100]) (consBan b85 (consBan b115 (consBan b116 (nilBan _ _)))) (by decide) (by decide +kernel)
theorem b118:B 87 6 e101:=viaCut pjt_1 w117 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b137:B 35 5 e120:=viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b138:B 35 5 e121:=viaSmall (by decide +kernel) (by decide)
theorem w139:W 35 5 e121:=viaSub (ws:=[e120,e74,e121]) (consBan b137 (consBan b85 (consBan b138 (nilBan _ _)))) (by decide) (by decide +kernel)
theorem b140:B 87 6 e122:=viaCut pjt_1 w139 (by decide) (by decide +kernel) (by decide +kernel)
theorem b141:B 87 6 e123:=viaCut pjt_13 w64 (by decide) (by decide +kernel) (by decide +kernel)
theorem b142:B 87 6 e124:=viaPerm pt0 pti0 b108 (by decide +kernel) (by decide +kernel)
theorem b143:B 87 6 e125:=viaPerm pt0 pti0 b109 (by decide +kernel) (by decide +kernel)
theorem b144:B 87 6 e126:=viaPerm pt0 pti0 b110 (by decide +kernel) (by decide +kernel)
theorem b145:B 87 6 e127:=viaPerm pt0 pti0 b111 (by decide +kernel) (by decide +kernel)
theorem b146:B 87 6 e128:=viaPerm pt0 pti0 b112 (by decide +kernel) (by decide +kernel)
theorem b147:B 87 6 e129:=viaPerm pt0 pti0 b113 (by decide +kernel) (by decide +kernel)
theorem b148:B 87 6 e130:=viaPerm pt0 pti0 b114 (by decide +kernel) (by decide +kernel)
theorem b149:B 87 6 e131:=viaPerm pt0 pti0 b118 (by decide +kernel) (by decide +kernel)
theorem b150:B 87 6 e132:=viaPerm pt0 pti0 b140 (by decide +kernel) (by decide +kernel)
theorem b151:B 87 6 e133:=viaPerm pt0 pti0 b141 (by decide +kernel) (by decide +kernel)
theorem b152:B 87 6 e134:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b156:B 35 4 e138:=viaSmall (by decide +kernel) (by decide)
theorem b172:B 87 5 e154:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b173:B 87 5 e155:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem w174:W 35 4 e138:=widen (by decide +kernel) b156
theorem b175:B 87 5 e156:=viaCut pjt_1 w174 (by decide) (by decide +kernel) (by decide +kernel)
theorem b176:B 87 5 e157:=viaCut pjt_13 w64 (by decide) (by decide +kernel) (by decide +kernel)
theorem b177:B 87 5 e158:=viaPerm pt4 pti4 b176 (by decide +kernel) (by decide +kernel)
theorem b178:B 87 5 e159:=viaCut pjt_13 w64 (by decide) (by decide +kernel) (by decide +kernel)
theorem b179:B 87 5 e160:=viaPerm pt4 pti4 b178 (by decide +kernel) (by decide +kernel)
theorem b189:B 87 4 e168:=viaSmall (by decide +kernel) (by decide)
theorem b190:B 87 4 e169:=viaSmall (by decide +kernel) (by decide)
theorem b191:B 87 4 e170:=viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b192:B 87 5 e171:=viaBranch (ws:=[e168,e169,e170]) (consBan b189 (consBan b190 (consBan b191 (nilBan _ _)))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b193:B 16 3 e172:=viaSmall (by decide +kernel) (by decide)
theorem w194:W 16 3 e172:=widen (by decide +kernel) b193
theorem b195:B 87 5 e173:=viaCut pjt_12 w194 (by decide) (by decide +kernel) (by decide +kernel)
theorem b196:B 87 5 e174:=viaCut pjt_12 w194 (by decide) (by decide +kernel) (by decide +kernel)
theorem b197:B 87 5 e175:=viaCut pjt_12 w194 (by decide) (by decide +kernel) (by decide +kernel)
theorem b198:B 87 5 e176:=viaPerm pt4 pti4 b172 (by decide +kernel) (by decide +kernel)
theorem b199:B 87 5 e177:=viaPerm pt4 pti4 b173 (by decide +kernel) (by decide +kernel)
theorem b200:B 87 5 e178:=viaPerm pt4 pti4 b192 (by decide +kernel) (by decide +kernel)
theorem b201:B 87 5 e179:=viaPerm pt4 pti4 b195 (by decide +kernel) (by decide +kernel)
theorem b202:B 87 5 e180:=viaPerm pt4 pti4 b196 (by decide +kernel) (by decide +kernel)
theorem b203:B 87 5 e181:=viaPerm pt4 pti4 b197 (by decide +kernel) (by decide +kernel)
theorem b224:B 87 4 e200:=viaPerm pt0 pti0 b191 (by decide +kernel) (by decide +kernel)
theorem b225:B 87 4 e201:=viaPerm pt1 pti1 b224 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b226:B 87 5 e202:=viaBranch (ws:=[e200,e170,e201]) (consBan b224 (consBan b191 (consBan b225 (nilBan _ _)))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b227:B 87 5 e203:=viaCut pjt_13 w64 (by decide) (by decide +kernel) (by decide +kernel)
theorem b228:B 87 5 e204:=viaCut pjt_12 w194 (by decide) (by decide +kernel) (by decide +kernel)
theorem b229:B 87 5 e205:=viaCut pjt_12 w194 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b230:B 87 6 e206:=viaBranch (ws:=[e154,e155,e156,e157,e158,e159,e160,e171,e173,e174,e175,e176,e177,e178,e179,e180,e181,e202,e203,e204,e205]) (consBan b172 (consBan b173 (consBan b175 (consBan b176 (consBan b177 (consBan b178 (consBan b179 (consBan b192 (consBan b195 (consBan b196 (consBan b197 (consBan b198 (consBan b199 (consBan b200 (consBan b201 (consBan b202 (consBan b203 (consBan b226 (consBan b227 (consBan b228 (consBan b229 (nilBan _ _)))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b232:B 87 6 e208:=viaCut pjt_2 w59 (by decide) (by decide +kernel) (by decide +kernel)
theorem b233:B 87 6 e209:=viaCut pjt_2 w59 (by decide) (by decide +kernel) (by decide +kernel)
theorem b243:B 87 6 e177:=viaCut pjt_2 w59 (by decide) (by decide +kernel) (by decide +kernel)
theorem b244:B 87 6 e219:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b253:B 87 6 e227:=viaCut pjt_2 w59 (by decide) (by decide +kernel) (by decide +kernel)
theorem b254:B 87 6 e228:=viaCut pjt_13 w64 (by decide) (by decide +kernel) (by decide +kernel)
theorem b255:B 87 6 e229:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem w260:W 35 5 e74:=widen (by decide +kernel) b85
theorem b261:B 87 6 e234:=viaCut pjt_1 w260 (by decide) (by decide +kernel) (by decide +kernel)
theorem b262:B 87 6 e235:=viaPerm pt0 pti0 b261 (by decide +kernel) (by decide +kernel)
theorem b263:B 87 6 e236:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b266:B 87 6 e239:=viaCut pjt_2 w59 (by decide) (by decide +kernel) (by decide +kernel)
theorem b267:B 87 6 e240:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b268:B 87 6 e241:=viaPerm pt0 pti0 b266 (by decide +kernel) (by decide +kernel)
theorem b269:B 87 6 e242:=viaPerm pt0 pti0 b267 (by decide +kernel) (by decide +kernel)
theorem b270:B 87 6 e243:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b271:B 16 4 e244:=viaSmall (by decide +kernel) (by decide)
theorem w272:W 16 4 e244:=widen (by decide +kernel) b271
theorem b273:B 87 6 e245:=viaCut pjt_13 w272 (by decide) (by decide +kernel) (by decide +kernel)
theorem b274:B 16 3 e59:=viaSmall (by decide +kernel) (by decide)
theorem w275:W 16 3 e59:=widen (by decide +kernel) b274
theorem b276:B 87 6 e246:=viaCut pjt_17 w275 (by decide) (by decide +kernel) (by decide +kernel)
theorem b277:B 87 6 e247:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b294:B 87 6 e263:=viaCut pjt_2 w59 (by decide) (by decide +kernel) (by decide +kernel)
theorem b295:B 87 6 e264:=viaCut pjt_17 w275 (by decide) (by decide +kernel) (by decide +kernel)
theorem b296:B 87 6 e265:=viaPerm pt0 pti0 b270 (by decide +kernel) (by decide +kernel)
theorem b297:B 87 6 e266:=viaPerm pt0 pti0 b273 (by decide +kernel) (by decide +kernel)
theorem b298:B 87 6 e267:=viaPerm pt0 pti0 b276 (by decide +kernel) (by decide +kernel)
theorem b299:B 87 6 e268:=viaPerm pt0 pti0 b294 (by decide +kernel) (by decide +kernel)
theorem b300:B 87 6 e269:=viaPerm pt0 pti0 b295 (by decide +kernel) (by decide +kernel)
theorem b301:B 87 6 e270:=viaPerm pt0 pti0 b277 (by decide +kernel) (by decide +kernel)
theorem b302:B 87 6 e271:=viaCut pjt_17 w275 (by decide) (by decide +kernel) (by decide +kernel)
theorem b308:B 35 4 e277:=viaSmall (by decide +kernel) (by decide)
theorem b320:B 20 4 e288:=viaSmall (by decide +kernel) (by decide)
theorem b323:B 35 4 e290:=viaSmall (by decide +kernel) (by decide)
theorem w324:W 35 4 e277:=viaSub (ws:=[e290,e277]) (consBan b323 (consBan b308 (nilBan _ _))) (by decide) (by decide +kernel)
theorem b325:B 87 5 e291:=viaCut pjt_1 w324 (by decide) (by decide +kernel) (by decide +kernel)
theorem b326:B 87 5 e292:=viaPerm pt0 pti0 b325 (by decide +kernel) (by decide +kernel)
theorem b327:B 35 4 e293:=viaSmall (by decide +kernel) (by decide)
theorem w328:W 35 4 e293:=widen (by decide +kernel) b327
theorem b329:B 87 5 e294:=viaCut pjt_2 w328 (by decide) (by decide +kernel) (by decide +kernel)
theorem b331:B 16 3 e295:=viaSmall (by decide +kernel) (by decide)
theorem b332:B 16 3 e296:=viaSmall (by decide +kernel) (by decide)
theorem w333:W 16 3 e296:=viaSub (ws:=[e295,e296]) (consBan b331 (consBan b332 (nilBan _ _))) (by decide) (by decide +kernel)
theorem b334:B 87 5 e297:=viaCut pjt_17 w333 (by decide) (by decide +kernel) (by decide +kernel)
theorem b339:B 87 4 e302:=viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b340:B 87 5 e303:=viaBranch (ws:=[e302]) (consBan b339 (nilBan _ _)) (by decide) (by decide +kernel) (by decide +kernel)
theorem b341:B 16 3 e304:=viaSmall (by decide +kernel) (by decide)
theorem w342:W 16 3 e304:=widen (by decide +kernel) b341
theorem b343:B 87 5 e305:=viaCut pjt_17 w342 (by decide) (by decide +kernel) (by decide +kernel)
theorem b344:B 87 5 e306:=viaPerm pt0 pti0 b200 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b345:B 87 6 e307:=viaBranch (ws:=[e291,e292,e294,e297,e303,e305,e178,e306]) (consBan b325 (consBan b326 (consBan b329 (consBan b334 (consBan b340 (consBan b343 (consBan b200 (consBan b344 (nilBan _ _))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b346:B 87 6 e308:=viaCut pjt_13 w64 (by decide) (by decide +kernel) (by decide +kernel)
theorem b347:B 87 6 e309:=viaPerm pt0 pti0 b346 (by decide +kernel) (by decide +kernel)
theorem b348:B 87 6 e310:=viaPerm pt0 pti0 b152 (by decide +kernel) (by decide +kernel)
theorem b349:B 87 6 e311:=viaPerm pt0 pti0 b230 (by decide +kernel) (by decide +kernel)
theorem b350:B 87 6 e312:=viaPerm pt0 pti0 b232 (by decide +kernel) (by decide +kernel)
theorem b351:B 87 6 e313:=viaPerm pt0 pti0 b233 (by decide +kernel) (by decide +kernel)
theorem b352:B 87 6 e314:=viaPerm pt0 pti0 b243 (by decide +kernel) (by decide +kernel)
theorem b353:B 87 6 e315:=viaPerm pt0 pti0 b244 (by decide +kernel) (by decide +kernel)
theorem b354:B 87 6 e316:=viaPerm pt0 pti0 b253 (by decide +kernel) (by decide +kernel)
theorem b355:B 87 6 e317:=viaPerm pt0 pti0 b254 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b356:B 87 7 e318:=viaBranch (ws:=[e51,e52,e53,e54,e56,e57,e58,e60,e61,e75,e76,e80,e81,e82,e83,e84,e85,e86,e87,e88,e89,e90,e91,e92,e93,e94,e95,e96,e97,e98,e101,e122,e123,e124,e125,e126,e127,e128,e129,e130,e131,e132,e133,e134,e206,e208,e209,e177,e219,e227,e228,e229,e234,e235,e236,e239,e240,e241,e242,e243,e245,e246,e247,e263,e264,e265,e266,e267,e268,e269,e270,e271,e307,e308,e309,e310,e311,e312,e313,e314,e315,e316,e317]) (consBan b54 (consBan b55 (consBan b56 (consBan b57 (consBan b60 (consBan b61 (consBan b62 (consBan b65 (consBan b67 (consBan b87 (consBan b89 (consBan b96 (consBan b97 (consBan b98 (consBan b99 (consBan b100 (consBan b101 (consBan b102 (consBan b103 (consBan b104 (consBan b105 (consBan b106 (consBan b107 (consBan b108 (consBan b109 (consBan b110 (consBan b111 (consBan b112 (consBan b113 (consBan b114 (consBan b118 (consBan b140 (consBan b141 (consBan b142 (consBan b143 (consBan b144 (consBan b145 (consBan b146 (consBan b147 (consBan b148 (consBan b149 (consBan b150 (consBan b151 (consBan b152 (consBan b230 (consBan b232 (consBan b233 (consBan b243 (consBan b244 (consBan b253 (consBan b254 (consBan b255 (consBan b261 (consBan b262 (consBan b263 (consBan b266 (consBan b267 (consBan b268 (consBan b269 (consBan b270 (consBan b273 (consBan b276 (consBan b277 (consBan b294 (consBan b295 (consBan b296 (consBan b297 (consBan b298 (consBan b299 (consBan b300 (consBan b301 (consBan b302 (consBan b345 (consBan b346 (consBan b347 (consBan b348 (consBan b349 (consBan b350 (consBan b351 (consBan b352 (consBan b353 (consBan b354 (consBan b355 (nilBan _ _)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b394:B 12 2 e16:=viaSmall (by decide +kernel) (by decide)
theorem w395:W 12 2 e16:=widen (by decide +kernel) b394
theorem b396:B 87 5 e355:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b397:B 87 5 e356:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b398:B 20 3 e357:=viaSmall (by decide +kernel) (by decide)
theorem b399:B 20 3 e358:=viaSmall (by decide +kernel) (by decide)
theorem b400:B 20 3 e359:=viaSmall (by decide +kernel) (by decide)
theorem w401:W 20 3 e359:=viaSub (ws:=[e357,e358,e359]) (consBan b398 (consBan b399 (consBan b400 (nilBan _ _)))) (by decide) (by decide +kernel)
theorem b402:B 87 5 e360:=viaCut pjt_11 w401 (by decide) (by decide +kernel) (by decide +kernel)
theorem b403:B 35 4 e361:=viaSmall (by decide +kernel) (by decide)
theorem w404:W 35 4 e361:=widen (by decide +kernel) b403
theorem b405:B 87 5 e362:=viaCut pjt_2 w404 (by decide) (by decide +kernel) (by decide +kernel)
theorem b406:B 87 5 e363:=viaPerm pt0 pti0 b402 (by decide +kernel) (by decide +kernel)
theorem b407:B 87 5 e364:=viaPerm pt0 pti0 b405 (by decide +kernel) (by decide +kernel)
theorem b408:B 87 5 e365:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b409:B 87 5 e366:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b410:B 87 5 e367:=viaPerm pt0 pti0 b408 (by decide +kernel) (by decide +kernel)
theorem b411:B 87 5 e368:=viaPerm pt0 pti0 b409 (by decide +kernel) (by decide +kernel)
theorem b412:B 87 5 e369:=viaCut pjt_12 w194 (by decide) (by decide +kernel) (by decide +kernel)
theorem b413:B 87 5 e370:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b414:B 87 5 e371:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b415:B 87 5 e372:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b416:B 87 5 e373:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b417:B 87 5 e374:=viaPerm pt0 pti0 b416 (by decide +kernel) (by decide +kernel)
theorem b418:B 87 5 e375:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b419:B 87 5 e376:=viaPerm pt0 pti0 b418 (by decide +kernel) (by decide +kernel)
theorem b420:B 87 5 e377:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b421:B 87 5 e378:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b422:B 87 5 e379:=viaPerm pt0 pti0 b420 (by decide +kernel) (by decide +kernel)
theorem b423:B 87 5 e380:=viaPerm pt0 pti0 b421 (by decide +kernel) (by decide +kernel)
theorem b424:B 87 5 e381:=viaPerm pt0 pti0 b412 (by decide +kernel) (by decide +kernel)
theorem b425:B 87 5 e382:=viaPerm pt0 pti0 b413 (by decide +kernel) (by decide +kernel)
theorem b426:B 87 5 e383:=viaPerm pt0 pti0 b414 (by decide +kernel) (by decide +kernel)
theorem b427:B 87 5 e384:=viaPerm pt0 pti0 b415 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b428:B 87 6 e385:=viaBranch (ws:=[e355,e356,e360,e362,e363,e364,e365,e366,e367,e368,e369,e370,e371,e372,e373,e374,e375,e376,e377,e378,e379,e380,e381,e382,e383,e384]) (consBan b396 (consBan b397 (consBan b402 (consBan b405 (consBan b406 (consBan b407 (consBan b408 (consBan b409 (consBan b410 (consBan b411 (consBan b412 (consBan b413 (consBan b414 (consBan b415 (consBan b416 (consBan b417 (consBan b418 (consBan b419 (consBan b420 (consBan b421 (consBan b422 (consBan b423 (consBan b424 (consBan b425 (consBan b426 (consBan b427 (nilBan _ _))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b429:B 87 6 e356:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b430:B 87 6 e386:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b431:B 87 6 e387:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b432:B 87 6 e388:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b433:B 87 6 e389:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b434:B 87 6 e390:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b435:B 87 6 e391:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b436:B 87 6 e392:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b437:B 87 6 e393:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b438:B 35 5 e394:=viaSmall (by decide +kernel) (by decide)
theorem w439:W 35 5 e394:=widen (by decide +kernel) b438
theorem b440:B 87 6 e395:=viaCut pjt_2 w439 (by decide) (by decide +kernel) (by decide +kernel)
theorem b441:B 87 6 e396:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b442:B 87 6 e397:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b443:B 87 6 e398:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b444:B 87 6 e399:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b445:B 87 6 e400:=viaPerm pt0 pti0 b431 (by decide +kernel) (by decide +kernel)
theorem b446:B 87 6 e401:=viaPerm pt0 pti0 b432 (by decide +kernel) (by decide +kernel)
theorem b447:B 87 6 e402:=viaPerm pt0 pti0 b433 (by decide +kernel) (by decide +kernel)
theorem b448:B 87 6 e403:=viaPerm pt0 pti0 b434 (by decide +kernel) (by decide +kernel)
theorem b449:B 87 6 e404:=viaPerm pt0 pti0 b435 (by decide +kernel) (by decide +kernel)
theorem b450:B 87 6 e405:=viaPerm pt0 pti0 b436 (by decide +kernel) (by decide +kernel)
theorem b451:B 87 6 e406:=viaPerm pt0 pti0 b437 (by decide +kernel) (by decide +kernel)
theorem b452:B 87 6 e407:=viaPerm pt0 pti0 b440 (by decide +kernel) (by decide +kernel)
theorem b453:B 87 6 e408:=viaPerm pt0 pti0 b441 (by decide +kernel) (by decide +kernel)
theorem b454:B 87 6 e409:=viaPerm pt0 pti0 b442 (by decide +kernel) (by decide +kernel)
theorem b455:B 87 6 e410:=viaPerm pt0 pti0 b443 (by decide +kernel) (by decide +kernel)
theorem b456:B 87 6 e411:=viaPerm pt0 pti0 b444 (by decide +kernel) (by decide +kernel)
theorem b457:B 87 6 e412:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b458:B 87 6 e413:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b459:B 87 6 e414:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b460:B 87 6 e415:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b461:B 87 6 e416:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b462:B 87 6 e417:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b464:B 16 3 e418:=viaSmall (by decide +kernel) (by decide)
theorem b465:B 16 3 e419:=viaSmall (by decide +kernel) (by decide)
theorem w466:W 16 3 e419:=viaSub (ws:=[e418,e419]) (consBan b464 (consBan b465 (nilBan _ _))) (by decide) (by decide +kernel)
theorem b467:B 87 6 e420:=viaCut pjt_9 w466 (by decide) (by decide +kernel) (by decide +kernel)
theorem b468:B 20 4 e421:=viaSmall (by decide +kernel) (by decide)
theorem b469:B 20 4 e422:=viaSmall (by decide +kernel) (by decide)
theorem w470:W 20 4 e69:=viaSub (ws:=[e422,e68,e69]) (consBan b469 (consBan b79 (consBan b80 (nilBan _ _)))) (by decide) (by decide +kernel)
theorem b471:B 87 6 e423:=viaCut pjt_6 w470 (by decide) (by decide +kernel) (by decide +kernel)
theorem w472:W 12 3 e0:=viaSub (ws:=[e16,e0]) (consBan b16 (consBan b0 (nilBan _ _))) (by decide) (by decide +kernel)
theorem b473:B 87 6 e424:=viaCut pjt_18 w472 (by decide) (by decide +kernel) (by decide +kernel)
theorem b474:B 12 3 e425:=viaPerm pc18_1 pci18_1 b0 (by decide +kernel) (by decide +kernel)
theorem w475:W 12 3 e425:=viaSub (ws:=[e16,e425]) (consBan b16 (consBan b474 (nilBan _ _))) (by decide) (by decide +kernel)
theorem b476:B 87 6 e426:=viaCut pjt_18 w475 (by decide) (by decide +kernel) (by decide +kernel)
theorem b477:B 87 6 e427:=viaPerm pt0 pti0 b457 (by decide +kernel) (by decide +kernel)
theorem b478:B 87 6 e428:=viaPerm pt0 pti0 b458 (by decide +kernel) (by decide +kernel)
theorem b479:B 87 6 e429:=viaPerm pt0 pti0 b459 (by decide +kernel) (by decide +kernel)
theorem b480:B 87 6 e430:=viaPerm pt0 pti0 b460 (by decide +kernel) (by decide +kernel)
theorem b481:B 87 6 e431:=viaPerm pt0 pti0 b461 (by decide +kernel) (by decide +kernel)
theorem b482:B 87 6 e432:=viaPerm pt0 pti0 b462 (by decide +kernel) (by decide +kernel)
theorem b483:B 87 6 e433:=viaPerm pt0 pti0 b467 (by decide +kernel) (by decide +kernel)
theorem b484:B 87 6 e434:=viaPerm pt0 pti0 b471 (by decide +kernel) (by decide +kernel)
theorem b485:B 87 6 e435:=viaPerm pt0 pti0 b473 (by decide +kernel) (by decide +kernel)
theorem b486:B 87 6 e436:=viaPerm pt0 pti0 b476 (by decide +kernel) (by decide +kernel)
theorem b487:B 87 6 e437:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b488:B 87 6 e438:=viaPerm pt3 pti3 b350 (by decide +kernel) (by decide +kernel)
theorem b489:B 87 6 e439:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b490:B 87 6 e440:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b491:B 87 6 e441:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b492:B 87 6 e442:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b493:B 87 6 e443:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b494:B 87 6 e444:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b495:B 87 6 e445:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b496:B 87 6 e446:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b497:B 87 6 e447:=viaPerm pt0 pti0 b496 (by decide +kernel) (by decide +kernel)
theorem b498:B 87 6 e448:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b499:B 87 6 e449:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b500:B 87 6 e450:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b501:B 87 6 e451:=viaPerm pt0 pti0 b499 (by decide +kernel) (by decide +kernel)
theorem b502:B 87 6 e452:=viaPerm pt0 pti0 b500 (by decide +kernel) (by decide +kernel)
theorem b503:B 87 6 e453:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b504:B 87 6 e454:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b505:B 87 6 e455:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b506:B 87 6 e456:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b507:B 87 6 e457:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b508:B 87 6 e458:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b509:B 87 6 e459:=viaPerm pt0 pti0 b503 (by decide +kernel) (by decide +kernel)
theorem b510:B 87 6 e460:=viaPerm pt0 pti0 b504 (by decide +kernel) (by decide +kernel)
theorem b511:B 87 6 e461:=viaPerm pt0 pti0 b505 (by decide +kernel) (by decide +kernel)
theorem b512:B 87 6 e462:=viaPerm pt0 pti0 b507 (by decide +kernel) (by decide +kernel)
theorem b513:B 87 6 e463:=viaPerm pt0 pti0 b508 (by decide +kernel) (by decide +kernel)
theorem b514:B 87 6 e464:=viaPerm pt0 pti0 b506 (by decide +kernel) (by decide +kernel)
theorem b516:B 16 3 e465:=viaSmall (by decide +kernel) (by decide)
theorem b517:B 16 3 e466:=viaSmall (by decide +kernel) (by decide)
theorem w518:W 16 3 e466:=viaSub (ws:=[e465,e466]) (consBan b516 (consBan b517 (nilBan _ _))) (by decide) (by decide +kernel)
theorem b519:B 87 6 e467:=viaCut pjt_10 w518 (by decide) (by decide +kernel) (by decide +kernel)
theorem b520:B 20 4 e468:=viaPerm pc6_0 pci6_0 b79 (by decide +kernel) (by decide +kernel)
theorem b521:B 20 4 e469:=viaPerm pc6_0 pci6_0 b80 (by decide +kernel) (by decide +kernel)
theorem w522:W 20 4 e469:=viaSub (ws:=[e422,e468,e469]) (consBan b469 (consBan b520 (consBan b521 (nilBan _ _)))) (by decide) (by decide +kernel)
theorem b523:B 87 6 e470:=viaCut pjt_6 w522 (by decide) (by decide +kernel) (by decide +kernel)
theorem b524:B 12 3 e471:=viaPerm pc18_2 pci18_2 b0 (by decide +kernel) (by decide +kernel)
theorem w525:W 12 3 e471:=viaSub (ws:=[e16,e471]) (consBan b16 (consBan b524 (nilBan _ _))) (by decide) (by decide +kernel)
theorem b526:B 87 6 e472:=viaCut pjt_18 w525 (by decide) (by decide +kernel) (by decide +kernel)
theorem b527:B 87 6 e473:=viaPerm pt0 pti0 b526 (by decide +kernel) (by decide +kernel)
theorem b528:B 87 6 e474:=viaPerm pt0 pti0 b487 (by decide +kernel) (by decide +kernel)
theorem b529:B 87 6 e475:=viaPerm pt0 pti0 b488 (by decide +kernel) (by decide +kernel)
theorem b530:B 87 6 e476:=viaPerm pt0 pti0 b489 (by decide +kernel) (by decide +kernel)
theorem b531:B 87 6 e477:=viaPerm pt0 pti0 b490 (by decide +kernel) (by decide +kernel)
theorem b532:B 87 6 e478:=viaPerm pt0 pti0 b491 (by decide +kernel) (by decide +kernel)
theorem b533:B 87 6 e479:=viaPerm pt0 pti0 b492 (by decide +kernel) (by decide +kernel)
theorem b534:B 87 6 e480:=viaPerm pt0 pti0 b493 (by decide +kernel) (by decide +kernel)
theorem b535:B 87 6 e481:=viaPerm pt0 pti0 b494 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b536:B 87 7 e355:=viaBranch (ws:=[e385,e356,e386,e387,e388,e389,e390,e391,e392,e393,e395,e396,e397,e398,e399,e400,e401,e402,e403,e404,e405,e406,e407,e408,e409,e410,e411,e412,e413,e414,e415,e416,e417,e420,e423,e424,e426,e427,e428,e429,e430,e431,e432,e433,e434,e435,e436,e437,e438,e439,e440,e441,e442,e443,e444,e445,e446,e447,e448,e449,e450,e451,e452,e453,e454,e455,e456,e457,e458,e459,e460,e461,e462,e463,e464,e467,e470,e472,e473,e474,e475,e476,e477,e478,e479,e480,e481]) (consBan b428 (consBan b429 (consBan b430 (consBan b431 (consBan b432 (consBan b433 (consBan b434 (consBan b435 (consBan b436 (consBan b437 (consBan b440 (consBan b441 (consBan b442 (consBan b443 (consBan b444 (consBan b445 (consBan b446 (consBan b447 (consBan b448 (consBan b449 (consBan b450 (consBan b451 (consBan b452 (consBan b453 (consBan b454 (consBan b455 (consBan b456 (consBan b457 (consBan b458 (consBan b459 (consBan b460 (consBan b461 (consBan b462 (consBan b467 (consBan b471 (consBan b473 (consBan b476 (consBan b477 (consBan b478 (consBan b479 (consBan b480 (consBan b481 (consBan b482 (consBan b483 (consBan b484 (consBan b485 (consBan b486 (consBan b487 (consBan b488 (consBan b489 (consBan b490 (consBan b491 (consBan b492 (consBan b493 (consBan b494 (consBan b495 (consBan b496 (consBan b497 (consBan b498 (consBan b499 (consBan b500 (consBan b501 (consBan b502 (consBan b503 (consBan b504 (consBan b505 (consBan b506 (consBan b507 (consBan b508 (consBan b509 (consBan b510 (consBan b511 (consBan b512 (consBan b513 (consBan b514 (consBan b519 (consBan b523 (consBan b526 (consBan b527 (consBan b528 (consBan b529 (consBan b530 (consBan b531 (consBan b532 (consBan b533 (consBan b534 (consBan b535 (nilBan _ _)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b548:B 35 5 e491:=viaSmall (by decide +kernel) (by decide)
theorem b579:B 87 6 e518:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b580:B 87 6 e519:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b581:B 87 6 e520:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b582:B 16 3 e465:=viaSmall (by decide +kernel) (by decide)
theorem b583:B 16 3 e466:=viaSmall (by decide +kernel) (by decide)
theorem w584:W 16 3 e466:=viaSub (ws:=[e465,e466]) (consBan b582 (consBan b583 (nilBan _ _))) (by decide) (by decide +kernel)
theorem b585:B 87 6 e521:=viaCut pjt_15 w584 (by decide) (by decide +kernel) (by decide +kernel)
theorem b586:B 87 6 e522:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b587:B 87 6 e523:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b588:B 87 6 e524:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b589:B 87 6 e525:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b590:B 87 6 e526:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b591:B 87 6 e527:=viaCut pjt_2 w59 (by decide) (by decide +kernel) (by decide +kernel)
theorem b592:B 87 6 e528:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b593:B 87 6 e529:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b594:B 87 6 e530:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b600:B 35 5 e536:=viaSmall (by decide +kernel) (by decide)
theorem w601:W 35 5 e536:=viaSub (ws:=[e55,e394,e536]) (consBan b58 (consBan b438 (consBan b600 (nilBan _ _)))) (by decide) (by decide +kernel)
theorem b602:B 87 6 e537:=viaCut pjt_2 w601 (by decide) (by decide +kernel) (by decide +kernel)
theorem b603:B 87 6 e538:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b604:B 87 6 e539:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b605:B 12 4 e540:=viaSmall (by decide +kernel) (by decide)
theorem w606:W 12 4 e540:=widen (by decide +kernel) b605
theorem b607:B 87 6 e541:=viaCut pjt_14 w606 (by decide) (by decide +kernel) (by decide +kernel)
theorem b608:B 87 6 e542:=viaCut pjt_13 w64 (by decide) (by decide +kernel) (by decide +kernel)
theorem b609:B 87 6 e543:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b610:B 87 6 e544:=viaPerm pt0 pti0 b587 (by decide +kernel) (by decide +kernel)
theorem b611:B 87 6 e545:=viaPerm pt0 pti0 b588 (by decide +kernel) (by decide +kernel)
theorem b612:B 87 6 e546:=viaPerm pt0 pti0 b589 (by decide +kernel) (by decide +kernel)
theorem b613:B 87 6 e547:=viaPerm pt0 pti0 b590 (by decide +kernel) (by decide +kernel)
theorem b614:B 87 6 e548:=viaPerm pt0 pti0 b591 (by decide +kernel) (by decide +kernel)
theorem b615:B 87 6 e549:=viaPerm pt0 pti0 b592 (by decide +kernel) (by decide +kernel)
theorem b616:B 87 6 e550:=viaPerm pt0 pti0 b593 (by decide +kernel) (by decide +kernel)
theorem b617:B 87 6 e551:=viaPerm pt0 pti0 b594 (by decide +kernel) (by decide +kernel)
theorem b618:B 87 6 e552:=viaPerm pt0 pti0 b602 (by decide +kernel) (by decide +kernel)
theorem b619:B 87 6 e553:=viaPerm pt0 pti0 b603 (by decide +kernel) (by decide +kernel)
theorem b620:B 87 6 e554:=viaPerm pt0 pti0 b604 (by decide +kernel) (by decide +kernel)
theorem b621:B 87 6 e555:=viaPerm pt0 pti0 b607 (by decide +kernel) (by decide +kernel)
theorem b622:B 87 6 e556:=viaPerm pt0 pti0 b608 (by decide +kernel) (by decide +kernel)
theorem b623:B 87 6 e557:=viaPerm pt0 pti0 b609 (by decide +kernel) (by decide +kernel)
theorem b624:B 87 6 e558:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b625:B 87 6 e559:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b626:B 87 6 e560:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b627:B 87 6 e561:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b628:B 87 6 e562:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b629:B 87 6 e563:=viaCut pjt_9 w466 (by decide) (by decide +kernel) (by decide +kernel)
theorem b630:B 87 6 e564:=viaCut pjt_6 w470 (by decide) (by decide +kernel) (by decide +kernel)
theorem b631:B 87 6 e565:=viaCut pjt_18 w472 (by decide) (by decide +kernel) (by decide +kernel)
theorem b632:B 87 6 e566:=viaCut pjt_18 w475 (by decide) (by decide +kernel) (by decide +kernel)
theorem b633:B 87 6 e567:=viaPerm pt0 pti0 b625 (by decide +kernel) (by decide +kernel)
theorem b634:B 87 6 e568:=viaPerm pt0 pti0 b626 (by decide +kernel) (by decide +kernel)
theorem b635:B 87 6 e569:=viaPerm pt0 pti0 b627 (by decide +kernel) (by decide +kernel)
theorem b636:B 87 6 e570:=viaPerm pt0 pti0 b628 (by decide +kernel) (by decide +kernel)
theorem b637:B 87 6 e571:=viaPerm pt0 pti0 b629 (by decide +kernel) (by decide +kernel)
theorem b638:B 87 6 e572:=viaPerm pt0 pti0 b630 (by decide +kernel) (by decide +kernel)
theorem b639:B 87 6 e573:=viaPerm pt0 pti0 b631 (by decide +kernel) (by decide +kernel)
theorem b640:B 87 6 e574:=viaPerm pt0 pti0 b632 (by decide +kernel) (by decide +kernel)
theorem b641:B 87 6 e575:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b642:B 87 6 e576:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b643:B 87 6 e577:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b644:B 87 6 e578:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b645:B 6 2 e62:=viaSmall (by decide +kernel) (by decide)
theorem b646:B 87 6 e579:=viaCut pjt_9 w466 (by decide) (by decide +kernel) (by decide +kernel)
theorem b647:B 20 4 e580:=viaSmall (by decide +kernel) (by decide)
theorem b648:B 20 4 e581:=viaSmall (by decide +kernel) (by decide)
theorem b649:B 87 6 e582:=viaCut pjt_6 w470 (by decide) (by decide +kernel) (by decide +kernel)
theorem b650:B 87 6 e583:=viaCut pjt_18 w472 (by decide) (by decide +kernel) (by decide +kernel)
theorem b651:B 87 6 e584:=viaCut pjt_18 w475 (by decide) (by decide +kernel) (by decide +kernel)
theorem b652:B 87 6 e585:=viaPerm pt0 pti0 b641 (by decide +kernel) (by decide +kernel)
theorem b653:B 87 6 e586:=viaPerm pt0 pti0 b642 (by decide +kernel) (by decide +kernel)
theorem b654:B 87 6 e587:=viaPerm pt0 pti0 b643 (by decide +kernel) (by decide +kernel)
theorem b655:B 87 6 e588:=viaPerm pt0 pti0 b644 (by decide +kernel) (by decide +kernel)
theorem b656:B 87 6 e589:=viaPerm pt0 pti0 b646 (by decide +kernel) (by decide +kernel)
theorem b657:B 87 6 e590:=viaPerm pt0 pti0 b649 (by decide +kernel) (by decide +kernel)
theorem b658:B 87 6 e591:=viaPerm pt0 pti0 b650 (by decide +kernel) (by decide +kernel)
theorem b659:B 87 6 e592:=viaPerm pt0 pti0 b651 (by decide +kernel) (by decide +kernel)
theorem b660:B 87 6 e593:=viaPerm pt3 pti3 b351 (by decide +kernel) (by decide +kernel)
theorem b661:B 87 6 e594:=viaPerm pt3 pti3 b531 (by decide +kernel) (by decide +kernel)
theorem b662:B 87 6 e595:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b663:B 87 6 e596:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b664:B 87 6 e597:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b665:B 87 6 e598:=viaPerm pt0 pti0 b664 (by decide +kernel) (by decide +kernel)
theorem b666:B 87 6 e599:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b667:B 87 6 e600:=viaPerm pt0 pti0 b666 (by decide +kernel) (by decide +kernel)
theorem b668:B 87 6 e601:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b669:B 87 6 e602:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b670:B 87 6 e603:=viaPerm pt0 pti0 b668 (by decide +kernel) (by decide +kernel)
theorem b671:B 87 6 e604:=viaPerm pt0 pti0 b669 (by decide +kernel) (by decide +kernel)
theorem b672:B 87 6 e605:=viaPerm pt0 pti0 b660 (by decide +kernel) (by decide +kernel)
theorem b673:B 87 6 e606:=viaPerm pt0 pti0 b661 (by decide +kernel) (by decide +kernel)
theorem b674:B 87 6 e607:=viaPerm pt0 pti0 b662 (by decide +kernel) (by decide +kernel)
theorem b675:B 87 6 e608:=viaPerm pt0 pti0 b663 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b676:B 87 7 e609:=viaBranch (ws:=[e518,e519,e51,e53,e520,e385,e521,e386,e522,e523,e524,e525,e526,e527,e528,e529,e530,e537,e538,e539,e541,e542,e543,e544,e545,e546,e547,e548,e549,e550,e551,e552,e553,e554,e555,e556,e557,e558,e559,e560,e561,e562,e563,e564,e565,e566,e567,e568,e569,e570,e571,e572,e573,e574,e575,e576,e577,e578,e579,e582,e583,e584,e585,e586,e587,e588,e589,e590,e591,e592,e593,e594,e595,e596,e597,e598,e599,e600,e601,e602,e603,e604,e605,e606,e607,e608]) (consBan b579 (consBan b580 (consBan b54 (consBan b56 (consBan b581 (consBan b428 (consBan b585 (consBan b430 (consBan b586 (consBan b587 (consBan b588 (consBan b589 (consBan b590 (consBan b591 (consBan b592 (consBan b593 (consBan b594 (consBan b602 (consBan b603 (consBan b604 (consBan b607 (consBan b608 (consBan b609 (consBan b610 (consBan b611 (consBan b612 (consBan b613 (consBan b614 (consBan b615 (consBan b616 (consBan b617 (consBan b618 (consBan b619 (consBan b620 (consBan b621 (consBan b622 (consBan b623 (consBan b624 (consBan b625 (consBan b626 (consBan b627 (consBan b628 (consBan b629 (consBan b630 (consBan b631 (consBan b632 (consBan b633 (consBan b634 (consBan b635 (consBan b636 (consBan b637 (consBan b638 (consBan b639 (consBan b640 (consBan b641 (consBan b642 (consBan b643 (consBan b644 (consBan b646 (consBan b649 (consBan b650 (consBan b651 (consBan b652 (consBan b653 (consBan b654 (consBan b655 (consBan b656 (consBan b657 (consBan b658 (consBan b659 (consBan b660 (consBan b661 (consBan b662 (consBan b663 (consBan b664 (consBan b665 (consBan b666 (consBan b667 (consBan b668 (consBan b669 (consBan b670 (consBan b671 (consBan b672 (consBan b673 (consBan b674 (consBan b675 (nilBan _ _))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b703:B 87 6 e318:=viaCut pjt_2 w59 (by decide) (by decide +kernel) (by decide +kernel)
theorem b704:B 87 6 e634:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b705:B 87 6 e635:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b706:B 87 6 e636:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b707:B 87 6 e637:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b708:B 87 6 e638:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b709:B 87 6 e639:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b710:B 87 6 e640:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b711:B 87 6 e641:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b712:B 87 6 e642:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b713:B 87 6 e643:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b714:B 87 6 e644:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b715:B 87 6 e645:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b716:B 87 6 e646:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b717:B 87 6 e647:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b718:B 87 6 e648:=viaPerm pt0 pti0 b704 (by decide +kernel) (by decide +kernel)
theorem b719:B 87 6 e649:=viaPerm pt0 pti0 b705 (by decide +kernel) (by decide +kernel)
theorem b720:B 87 6 e650:=viaPerm pt0 pti0 b706 (by decide +kernel) (by decide +kernel)
theorem b721:B 87 6 e651:=viaPerm pt0 pti0 b707 (by decide +kernel) (by decide +kernel)
theorem b722:B 87 6 e652:=viaPerm pt0 pti0 b708 (by decide +kernel) (by decide +kernel)
theorem b723:B 87 6 e653:=viaPerm pt0 pti0 b709 (by decide +kernel) (by decide +kernel)
theorem b724:B 87 6 e654:=viaPerm pt0 pti0 b710 (by decide +kernel) (by decide +kernel)
theorem b725:B 87 6 e655:=viaPerm pt0 pti0 b711 (by decide +kernel) (by decide +kernel)
theorem b726:B 87 6 e656:=viaPerm pt0 pti0 b712 (by decide +kernel) (by decide +kernel)
theorem b727:B 87 6 e657:=viaPerm pt0 pti0 b713 (by decide +kernel) (by decide +kernel)
theorem b728:B 87 6 e658:=viaPerm pt0 pti0 b714 (by decide +kernel) (by decide +kernel)
theorem b729:B 87 6 e659:=viaPerm pt0 pti0 b715 (by decide +kernel) (by decide +kernel)
theorem b730:B 87 6 e660:=viaPerm pt0 pti0 b716 (by decide +kernel) (by decide +kernel)
theorem b731:B 87 6 e661:=viaPerm pt0 pti0 b717 (by decide +kernel) (by decide +kernel)
theorem b732:B 87 6 e662:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b733:B 87 6 e663:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b734:B 87 6 e664:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b735:B 87 6 e665:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b736:B 87 6 e666:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b737:B 87 6 e667:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b738:B 16 3 e668:=viaSmall (by decide +kernel) (by decide)
theorem w739:W 16 3 e668:=widen (by decide +kernel) b738
theorem b740:B 87 6 e669:=viaCut pjt_13 w739 (by decide) (by decide +kernel) (by decide +kernel)
theorem b749:B 87 6 e674:=viaCut pjt_6 w470 (by decide) (by decide +kernel) (by decide +kernel)
theorem b750:B 87 6 e675:=viaCut pjt_18 w472 (by decide) (by decide +kernel) (by decide +kernel)
theorem b751:B 87 6 e676:=viaCut pjt_13 w739 (by decide) (by decide +kernel) (by decide +kernel)
theorem b752:B 87 6 e677:=viaPerm pt0 pti0 b732 (by decide +kernel) (by decide +kernel)
theorem b753:B 87 6 e678:=viaPerm pt0 pti0 b733 (by decide +kernel) (by decide +kernel)
theorem b754:B 87 6 e679:=viaPerm pt0 pti0 b734 (by decide +kernel) (by decide +kernel)
theorem b755:B 87 6 e680:=viaPerm pt0 pti0 b735 (by decide +kernel) (by decide +kernel)
theorem b756:B 87 6 e681:=viaPerm pt0 pti0 b736 (by decide +kernel) (by decide +kernel)
theorem b757:B 87 6 e682:=viaPerm pt0 pti0 b737 (by decide +kernel) (by decide +kernel)
theorem b758:B 87 6 e683:=viaPerm pt0 pti0 b740 (by decide +kernel) (by decide +kernel)
theorem b759:B 87 6 e684:=viaPerm pt0 pti0 b749 (by decide +kernel) (by decide +kernel)
theorem b760:B 87 6 e685:=viaPerm pt0 pti0 b750 (by decide +kernel) (by decide +kernel)
theorem b761:B 87 6 e686:=viaPerm pt0 pti0 b751 (by decide +kernel) (by decide +kernel)
theorem b762:B 87 6 e687:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b763:B 87 6 e155:=viaPerm pt3 pti3 b352 (by decide +kernel) (by decide +kernel)
theorem b764:B 87 6 e688:=viaPerm pt3 pti3 b532 (by decide +kernel) (by decide +kernel)
theorem b765:B 87 6 e689:=viaPerm pt3 pti3 b674 (by decide +kernel) (by decide +kernel)
theorem b766:B 87 6 e690:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b767:B 87 6 e691:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b768:B 87 6 e692:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b769:B 87 6 e693:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b770:B 87 6 e694:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b771:B 87 6 e695:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b772:B 87 6 e696:=viaPerm pt0 pti0 b771 (by decide +kernel) (by decide +kernel)
theorem b773:B 87 6 e697:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b774:B 87 6 e698:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b775:B 87 6 e699:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b776:B 87 6 e700:=viaPerm pt0 pti0 b774 (by decide +kernel) (by decide +kernel)
theorem b777:B 87 6 e701:=viaPerm pt0 pti0 b775 (by decide +kernel) (by decide +kernel)
theorem b778:B 87 6 e702:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b779:B 87 6 e703:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b780:B 87 6 e704:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b781:B 87 6 e705:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b782:B 87 6 e706:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b783:B 87 6 e707:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b784:B 87 6 e708:=viaPerm pt0 pti0 b778 (by decide +kernel) (by decide +kernel)
theorem b785:B 87 6 e709:=viaPerm pt0 pti0 b779 (by decide +kernel) (by decide +kernel)
theorem b786:B 87 6 e710:=viaPerm pt0 pti0 b780 (by decide +kernel) (by decide +kernel)
theorem b787:B 87 6 e711:=viaPerm pt0 pti0 b782 (by decide +kernel) (by decide +kernel)
theorem b788:B 87 6 e712:=viaPerm pt0 pti0 b783 (by decide +kernel) (by decide +kernel)
theorem b789:B 87 6 e713:=viaPerm pt0 pti0 b781 (by decide +kernel) (by decide +kernel)
theorem b790:B 16 3 e668:=viaSmall (by decide +kernel) (by decide)
theorem w791:W 16 3 e668:=widen (by decide +kernel) b790
theorem b792:B 87 6 e714:=viaCut pjt_17 w791 (by decide) (by decide +kernel) (by decide +kernel)
theorem b794:B 20 4 e715:=viaSmall (by decide +kernel) (by decide)
theorem w795:W 20 4 e715:=viaSub (ws:=[e421,e288,e715]) (consBan b468 (consBan b320 (consBan b794 (nilBan _ _)))) (by decide) (by decide +kernel)
theorem b796:B 87 6 e716:=viaCut pjt_7 w795 (by decide) (by decide +kernel) (by decide +kernel)
theorem b797:B 87 6 e717:=viaCut pjt_13 w739 (by decide) (by decide +kernel) (by decide +kernel)
theorem b798:B 87 6 e718:=viaPerm pt0 pti0 b797 (by decide +kernel) (by decide +kernel)
theorem b799:B 87 6 e719:=viaPerm pt0 pti0 b762 (by decide +kernel) (by decide +kernel)
theorem b800:B 87 6 e720:=viaPerm pt0 pti0 b763 (by decide +kernel) (by decide +kernel)
theorem b801:B 87 6 e721:=viaPerm pt0 pti0 b764 (by decide +kernel) (by decide +kernel)
theorem b802:B 87 6 e722:=viaPerm pt0 pti0 b765 (by decide +kernel) (by decide +kernel)
theorem b803:B 87 6 e723:=viaPerm pt0 pti0 b766 (by decide +kernel) (by decide +kernel)
theorem b804:B 87 6 e724:=viaPerm pt0 pti0 b767 (by decide +kernel) (by decide +kernel)
theorem b805:B 87 6 e725:=viaPerm pt0 pti0 b768 (by decide +kernel) (by decide +kernel)
theorem b806:B 87 6 e726:=viaPerm pt0 pti0 b769 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b807:B 87 7 e52:=viaBranch (ws:=[e318,e51,e53,e634,e635,e636,e637,e638,e639,e640,e641,e642,e643,e644,e645,e646,e647,e648,e649,e650,e651,e652,e653,e654,e655,e656,e657,e658,e659,e660,e661,e662,e663,e664,e665,e666,e667,e669,e674,e675,e676,e677,e678,e679,e680,e681,e682,e683,e684,e685,e686,e687,e155,e688,e689,e690,e691,e692,e693,e694,e695,e696,e697,e698,e699,e700,e701,e702,e703,e704,e705,e706,e707,e708,e709,e710,e711,e712,e713,e714,e716,e717,e718,e719,e720,e721,e722,e723,e724,e725,e726]) (consBan b703 (consBan b54 (consBan b56 (consBan b704 (consBan b705 (consBan b706 (consBan b707 (consBan b708 (consBan b709 (consBan b710 (consBan b711 (consBan b712 (consBan b713 (consBan b714 (consBan b715 (consBan b716 (consBan b717 (consBan b718 (consBan b719 (consBan b720 (consBan b721 (consBan b722 (consBan b723 (consBan b724 (consBan b725 (consBan b726 (consBan b727 (consBan b728 (consBan b729 (consBan b730 (consBan b731 (consBan b732 (consBan b733 (consBan b734 (consBan b735 (consBan b736 (consBan b737 (consBan b740 (consBan b749 (consBan b750 (consBan b751 (consBan b752 (consBan b753 (consBan b754 (consBan b755 (consBan b756 (consBan b757 (consBan b758 (consBan b759 (consBan b760 (consBan b761 (consBan b762 (consBan b763 (consBan b764 (consBan b765 (consBan b766 (consBan b767 (consBan b768 (consBan b769 (consBan b770 (consBan b771 (consBan b772 (consBan b773 (consBan b774 (consBan b775 (consBan b776 (consBan b777 (consBan b778 (consBan b779 (consBan b780 (consBan b781 (consBan b782 (consBan b783 (consBan b784 (consBan b785 (consBan b786 (consBan b787 (consBan b788 (consBan b789 (consBan b792 (consBan b796 (consBan b797 (consBan b798 (consBan b799 (consBan b800 (consBan b801 (consBan b802 (consBan b803 (consBan b804 (consBan b805 (consBan b806 (nilBan _ _)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b808:B 87 7 e558:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b813:B 87 6 e355:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b814:B 87 6 e728:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b815:B 87 6 e729:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b816:B 87 6 e730:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b817:B 87 6 e731:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b818:B 87 6 e732:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b819:B 87 6 e733:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b820:B 87 6 e734:=viaCut pjt_15 w584 (by decide) (by decide +kernel) (by decide +kernel)
theorem b821:B 20 4 e483:=viaPerm pc11_2 pci11_2 b9 (by decide +kernel) (by decide +kernel)
theorem b822:B 20 4 e735:=viaSmall (by decide +kernel) (by decide)
theorem b823:B 20 4 e736:=viaSmall (by decide +kernel) (by decide)
theorem w824:W 20 4 e736:=viaSub (ws:=[e483,e735,e736]) (consBan b821 (consBan b822 (consBan b823 (nilBan _ _)))) (by decide) (by decide +kernel)
theorem b825:B 87 6 e737:=viaCut pjt_11 w824 (by decide) (by decide +kernel) (by decide +kernel)
theorem b826:B 87 6 e738:=viaCut pjt_18 w472 (by decide) (by decide +kernel) (by decide +kernel)
theorem b827:B 87 6 e739:=viaCut pjt_18 w475 (by decide) (by decide +kernel) (by decide +kernel)
theorem b828:B 87 6 e740:=viaPerm pt0 pti0 b814 (by decide +kernel) (by decide +kernel)
theorem b829:B 87 6 e741:=viaPerm pt0 pti0 b815 (by decide +kernel) (by decide +kernel)
theorem b830:B 87 6 e742:=viaPerm pt0 pti0 b816 (by decide +kernel) (by decide +kernel)
theorem b831:B 87 6 e743:=viaPerm pt0 pti0 b817 (by decide +kernel) (by decide +kernel)
theorem b832:B 87 6 e744:=viaPerm pt0 pti0 b818 (by decide +kernel) (by decide +kernel)
theorem b833:B 87 6 e745:=viaPerm pt0 pti0 b819 (by decide +kernel) (by decide +kernel)
theorem b834:B 87 6 e746:=viaPerm pt0 pti0 b820 (by decide +kernel) (by decide +kernel)
theorem b835:B 87 6 e747:=viaPerm pt0 pti0 b825 (by decide +kernel) (by decide +kernel)
theorem b836:B 87 6 e748:=viaPerm pt0 pti0 b826 (by decide +kernel) (by decide +kernel)
theorem b837:B 87 6 e749:=viaPerm pt0 pti0 b827 (by decide +kernel) (by decide +kernel)
theorem b838:B 87 6 e750:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b839:B 87 6 e751:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b840:B 87 6 e752:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b841:B 87 6 e753:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b842:B 87 6 e754:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b843:B 87 6 e755:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b844:B 87 6 e756:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b845:B 87 6 e757:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b846:B 87 6 e758:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b847:B 87 6 e759:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b848:B 87 6 e760:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b849:B 87 6 e761:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b850:B 87 6 e762:=viaPerm pt0 pti0 b838 (by decide +kernel) (by decide +kernel)
theorem b851:B 87 6 e763:=viaPerm pt0 pti0 b839 (by decide +kernel) (by decide +kernel)
theorem b852:B 87 6 e764:=viaPerm pt0 pti0 b840 (by decide +kernel) (by decide +kernel)
theorem b853:B 87 6 e765:=viaPerm pt0 pti0 b841 (by decide +kernel) (by decide +kernel)
theorem b854:B 87 6 e766:=viaPerm pt0 pti0 b842 (by decide +kernel) (by decide +kernel)
theorem b855:B 87 6 e767:=viaPerm pt0 pti0 b843 (by decide +kernel) (by decide +kernel)
theorem b856:B 87 6 e768:=viaPerm pt0 pti0 b844 (by decide +kernel) (by decide +kernel)
theorem b857:B 87 6 e769:=viaPerm pt0 pti0 b845 (by decide +kernel) (by decide +kernel)
theorem b858:B 87 6 e770:=viaPerm pt0 pti0 b846 (by decide +kernel) (by decide +kernel)
theorem b859:B 87 6 e771:=viaPerm pt0 pti0 b847 (by decide +kernel) (by decide +kernel)
theorem b860:B 87 6 e772:=viaPerm pt0 pti0 b848 (by decide +kernel) (by decide +kernel)
theorem b861:B 87 6 e773:=viaPerm pt0 pti0 b849 (by decide +kernel) (by decide +kernel)
theorem b862:B 87 6 e774:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b863:B 87 6 e775:=viaPerm pt3 pti3 b354 (by decide +kernel) (by decide +kernel)
theorem b864:B 87 6 e776:=viaPerm pt3 pti3 b534 (by decide +kernel) (by decide +kernel)
theorem b865:B 87 6 e777:=viaPerm pt3 pti3 b675 (by decide +kernel) (by decide +kernel)
theorem b866:B 87 6 e778:=viaPerm pt3 pti3 b805 (by decide +kernel) (by decide +kernel)
theorem b867:B 87 6 e779:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b868:B 87 6 e780:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b869:B 87 6 e781:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b870:B 87 6 e782:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b871:B 87 6 e783:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b872:B 87 6 e784:=viaPerm pt0 pti0 b871 (by decide +kernel) (by decide +kernel)
theorem b873:B 87 6 e785:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b874:B 87 6 e786:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b875:B 87 6 e787:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b876:B 87 6 e788:=viaPerm pt0 pti0 b874 (by decide +kernel) (by decide +kernel)
theorem b877:B 87 6 e789:=viaPerm pt0 pti0 b875 (by decide +kernel) (by decide +kernel)
theorem b878:B 87 6 e790:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b879:B 87 6 e791:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b880:B 87 6 e792:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b881:B 87 6 e793:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b882:B 87 6 e794:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b883:B 87 6 e795:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b884:B 87 6 e796:=viaPerm pt0 pti0 b878 (by decide +kernel) (by decide +kernel)
theorem b885:B 87 6 e797:=viaPerm pt0 pti0 b879 (by decide +kernel) (by decide +kernel)
theorem b886:B 87 6 e798:=viaPerm pt0 pti0 b880 (by decide +kernel) (by decide +kernel)
theorem b887:B 87 6 e799:=viaPerm pt0 pti0 b882 (by decide +kernel) (by decide +kernel)
theorem b888:B 87 6 e800:=viaPerm pt0 pti0 b883 (by decide +kernel) (by decide +kernel)
theorem b889:B 87 6 e801:=viaPerm pt0 pti0 b881 (by decide +kernel) (by decide +kernel)
theorem b890:B 87 6 e802:=viaCut pjt_10 w518 (by decide) (by decide +kernel) (by decide +kernel)
theorem b891:B 87 6 e803:=viaCut pjt_7 w795 (by decide) (by decide +kernel) (by decide +kernel)
theorem b892:B 87 6 e804:=viaCut pjt_18 w525 (by decide) (by decide +kernel) (by decide +kernel)
theorem b893:B 87 6 e805:=viaPerm pt0 pti0 b892 (by decide +kernel) (by decide +kernel)
theorem b894:B 87 6 e806:=viaPerm pt0 pti0 b862 (by decide +kernel) (by decide +kernel)
theorem b895:B 87 6 e807:=viaPerm pt0 pti0 b863 (by decide +kernel) (by decide +kernel)
theorem b896:B 87 6 e808:=viaPerm pt0 pti0 b864 (by decide +kernel) (by decide +kernel)
theorem b897:B 87 6 e809:=viaPerm pt0 pti0 b865 (by decide +kernel) (by decide +kernel)
theorem b898:B 87 6 e810:=viaPerm pt0 pti0 b866 (by decide +kernel) (by decide +kernel)
theorem b899:B 87 6 e811:=viaPerm pt0 pti0 b867 (by decide +kernel) (by decide +kernel)
theorem b900:B 87 6 e812:=viaPerm pt0 pti0 b868 (by decide +kernel) (by decide +kernel)
theorem b901:B 87 6 e813:=viaPerm pt0 pti0 b869 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b902:B 87 7 e356:=viaBranch (ws:=[e355,e385,e386,e728,e729,e730,e731,e732,e733,e734,e737,e738,e739,e740,e741,e742,e743,e744,e745,e746,e747,e748,e749,e750,e751,e752,e753,e754,e755,e756,e757,e758,e759,e760,e761,e762,e763,e764,e765,e766,e767,e768,e769,e770,e771,e772,e773,e774,e775,e776,e777,e778,e779,e780,e781,e782,e783,e784,e785,e786,e787,e788,e789,e790,e791,e792,e793,e794,e795,e796,e797,e798,e799,e800,e801,e802,e803,e804,e805,e806,e807,e808,e809,e810,e811,e812,e813]) (consBan b813 (consBan b428 (consBan b430 (consBan b814 (consBan b815 (consBan b816 (consBan b817 (consBan b818 (consBan b819 (consBan b820 (consBan b825 (consBan b826 (consBan b827 (consBan b828 (consBan b829 (consBan b830 (consBan b831 (consBan b832 (consBan b833 (consBan b834 (consBan b835 (consBan b836 (consBan b837 (consBan b838 (consBan b839 (consBan b840 (consBan b841 (consBan b842 (consBan b843 (consBan b844 (consBan b845 (consBan b846 (consBan b847 (consBan b848 (consBan b849 (consBan b850 (consBan b851 (consBan b852 (consBan b853 (consBan b854 (consBan b855 (consBan b856 (consBan b857 (consBan b858 (consBan b859 (consBan b860 (consBan b861 (consBan b862 (consBan b863 (consBan b864 (consBan b865 (consBan b866 (consBan b867 (consBan b868 (consBan b869 (consBan b870 (consBan b871 (consBan b872 (consBan b873 (consBan b874 (consBan b875 (consBan b876 (consBan b877 (consBan b878 (consBan b879 (consBan b880 (consBan b881 (consBan b882 (consBan b883 (consBan b884 (consBan b885 (consBan b886 (consBan b887 (consBan b888 (consBan b889 (consBan b890 (consBan b891 (consBan b892 (consBan b893 (consBan b894 (consBan b895 (consBan b896 (consBan b897 (consBan b898 (consBan b899 (consBan b900 (consBan b901 (nilBan _ _)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b903:B 87 6 e609:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b904:B 87 6 e17:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b905:B 87 6 e814:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b906:B 87 6 e815:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b907:B 87 6 e816:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b908:B 87 6 e817:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b909:B 87 6 e818:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b910:B 87 6 e819:=viaCut pjt_12 w95 (by decide) (by decide +kernel) (by decide +kernel)
theorem b913:B 87 6 e822:=viaCut pjt_6 w470 (by decide) (by decide +kernel) (by decide +kernel)
theorem b914:B 6 2 e62:=viaSmall (by decide +kernel) (by decide)
theorem b915:B 87 6 e823:=viaCut pjt_18 w472 (by decide) (by decide +kernel) (by decide +kernel)
theorem b916:B 87 6 e824:=viaCut pjt_18 w475 (by decide) (by decide +kernel) (by decide +kernel)
theorem b917:B 87 6 e825:=viaPerm pt0 pti0 b906 (by decide +kernel) (by decide +kernel)
theorem b918:B 87 6 e826:=viaPerm pt0 pti0 b907 (by decide +kernel) (by decide +kernel)
theorem b919:B 87 6 e827:=viaPerm pt0 pti0 b908 (by decide +kernel) (by decide +kernel)
theorem b920:B 87 6 e828:=viaPerm pt0 pti0 b909 (by decide +kernel) (by decide +kernel)
theorem b921:B 87 6 e829:=viaPerm pt0 pti0 b910 (by decide +kernel) (by decide +kernel)
theorem b922:B 87 6 e830:=viaPerm pt0 pti0 b913 (by decide +kernel) (by decide +kernel)
theorem b923:B 87 6 e831:=viaPerm pt0 pti0 b915 (by decide +kernel) (by decide +kernel)
theorem b924:B 87 6 e832:=viaPerm pt0 pti0 b916 (by decide +kernel) (by decide +kernel)
theorem b925:B 87 6 e833:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b926:B 87 6 e834:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b927:B 87 6 e835:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b928:B 87 6 e836:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b929:B 87 6 e837:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b930:B 87 6 e838:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b931:B 87 6 e839:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b932:B 87 6 e840:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b933:B 87 6 e841:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b934:B 87 6 e842:=viaPerm pt0 pti0 b928 (by decide +kernel) (by decide +kernel)
theorem b935:B 87 6 e843:=viaPerm pt0 pti0 b929 (by decide +kernel) (by decide +kernel)
theorem b936:B 87 6 e844:=viaPerm pt0 pti0 b930 (by decide +kernel) (by decide +kernel)
theorem b937:B 87 6 e845:=viaPerm pt0 pti0 b931 (by decide +kernel) (by decide +kernel)
theorem b938:B 87 6 e846:=viaPerm pt0 pti0 b932 (by decide +kernel) (by decide +kernel)
theorem b939:B 87 6 e847:=viaPerm pt0 pti0 b933 (by decide +kernel) (by decide +kernel)
theorem b940:B 87 6 e848:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b941:B 87 6 e849:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b942:B 20 4 e850:=viaSmall (by decide +kernel) (by decide)
theorem w943:W 20 4 e850:=viaSub (ws:=[e483,e850]) (consBan b821 (consBan b942 (nilBan _ _))) (by decide) (by decide +kernel)
theorem b944:B 87 6 e851:=viaCut pjt_11 w943 (by decide) (by decide +kernel) (by decide +kernel)
theorem b945:B 87 6 e852:=viaCut pjt_18 w472 (by decide) (by decide +kernel) (by decide +kernel)
theorem b946:B 87 6 e853:=viaPerm pt0 pti0 b940 (by decide +kernel) (by decide +kernel)
theorem b947:B 87 6 e854:=viaPerm pt0 pti0 b941 (by decide +kernel) (by decide +kernel)
theorem b948:B 87 6 e855:=viaPerm pt0 pti0 b944 (by decide +kernel) (by decide +kernel)
theorem b949:B 87 6 e856:=viaPerm pt0 pti0 b945 (by decide +kernel) (by decide +kernel)
theorem b950:B 87 6 e857:=viaPerm pt3 pti3 b355 (by decide +kernel) (by decide +kernel)
theorem b951:B 87 6 e858:=viaPerm pt3 pti3 b535 (by decide +kernel) (by decide +kernel)
theorem b952:B 87 6 e859:=viaPerm pt3 pti3 b806 (by decide +kernel) (by decide +kernel)
theorem b953:B 87 6 e860:=viaPerm pt3 pti3 b901 (by decide +kernel) (by decide +kernel)
theorem b954:B 87 6 e861:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b955:B 87 6 e862:=viaPerm pt0 pti0 b954 (by decide +kernel) (by decide +kernel)
theorem b956:B 87 6 e863:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b957:B 87 6 e864:=viaPerm pt0 pti0 b956 (by decide +kernel) (by decide +kernel)
theorem b958:B 87 6 e865:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b959:B 87 6 e866:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b960:B 87 6 e867:=viaPerm pt0 pti0 b958 (by decide +kernel) (by decide +kernel)
theorem b961:B 87 6 e868:=viaPerm pt0 pti0 b959 (by decide +kernel) (by decide +kernel)
theorem b962:B 87 6 e869:=viaPerm pt0 pti0 b950 (by decide +kernel) (by decide +kernel)
theorem b963:B 87 6 e870:=viaPerm pt0 pti0 b951 (by decide +kernel) (by decide +kernel)
theorem b964:B 87 6 e871:=viaPerm pt0 pti0 b952 (by decide +kernel) (by decide +kernel)
theorem b965:B 87 6 e872:=viaPerm pt0 pti0 b953 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b966:B 87 7 e522:=viaBranch (ws:=[e318,e609,e521,e17,e814,e815,e816,e817,e818,e819,e822,e823,e824,e825,e826,e827,e828,e829,e830,e831,e832,e385,e386,e833,e834,e835,e836,e837,e838,e839,e840,e841,e842,e843,e844,e845,e846,e847,e728,e848,e849,e733,e734,e851,e852,e739,e740,e853,e854,e745,e746,e855,e856,e749,e857,e858,e859,e860,e861,e862,e863,e864,e865,e866,e867,e868,e869,e870,e871,e872]) (consBan b703 (consBan b903 (consBan b585 (consBan b904 (consBan b905 (consBan b906 (consBan b907 (consBan b908 (consBan b909 (consBan b910 (consBan b913 (consBan b915 (consBan b916 (consBan b917 (consBan b918 (consBan b919 (consBan b920 (consBan b921 (consBan b922 (consBan b923 (consBan b924 (consBan b428 (consBan b430 (consBan b925 (consBan b926 (consBan b927 (consBan b928 (consBan b929 (consBan b930 (consBan b931 (consBan b932 (consBan b933 (consBan b934 (consBan b935 (consBan b936 (consBan b937 (consBan b938 (consBan b939 (consBan b814 (consBan b940 (consBan b941 (consBan b819 (consBan b820 (consBan b944 (consBan b945 (consBan b827 (consBan b828 (consBan b946 (consBan b947 (consBan b833 (consBan b834 (consBan b948 (consBan b949 (consBan b837 (consBan b950 (consBan b951 (consBan b952 (consBan b953 (consBan b954 (consBan b955 (consBan b956 (consBan b957 (consBan b958 (consBan b959 (consBan b960 (consBan b961 (consBan b962 (consBan b963 (consBan b964 (consBan b965 (nilBan _ _))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b967:B 87 7 e873:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b982:B 87 6 e888:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b983:B 87 6 e889:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b984:B 87 6 e890:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b985:B 87 6 e891:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b986:B 87 6 e892:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b987:B 87 6 e893:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b988:B 87 6 e894:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b989:B 87 6 e895:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b990:B 87 6 e896:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b991:B 16 3 e897:=viaPerm pc13_0 pci13_0 b63 (by decide +kernel) (by decide +kernel)
theorem w992:W 16 3 e897:=widen (by decide +kernel) b991
theorem b993:B 87 6 e898:=viaCut pjt_13 w992 (by decide) (by decide +kernel) (by decide +kernel)
theorem b994:B 20 4 e899:=viaSmall (by decide +kernel) (by decide)
theorem b995:B 20 4 e900:=viaSmall (by decide +kernel) (by decide)
theorem w996:W 20 4 e900:=viaSub (ws:=[e580,e899,e900]) (consBan b647 (consBan b994 (consBan b995 (nilBan _ _)))) (by decide) (by decide +kernel)
theorem b997:B 87 6 e901:=viaCut pjt_11 w996 (by decide) (by decide +kernel) (by decide +kernel)
theorem b998:B 87 6 e902:=viaCut pjt_18 w472 (by decide) (by decide +kernel) (by decide +kernel)
theorem b999:B 87 6 e903:=viaCut pjt_13 w992 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1000:B 87 6 e904:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1001:B 87 6 e905:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1002:B 87 6 e906:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1003:B 87 6 e907:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1004:B 87 6 e908:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1005:B 87 6 e909:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1006:B 16 3 e910:=viaSmall (by decide +kernel) (by decide)
theorem b1007:B 16 3 e911:=viaSmall (by decide +kernel) (by decide)
theorem w1008:W 16 3 e911:=viaSub (ws:=[e910,e911]) (consBan b1006 (consBan b1007 (nilBan _ _))) (by decide) (by decide +kernel)
theorem b1009:B 87 6 e912:=viaCut pjt_17 w1008 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1010:B 20 4 e913:=viaPerm pc11_0 pci11_0 b994 (by decide +kernel) (by decide +kernel)
theorem b1011:B 20 4 e914:=viaPerm pc11_0 pci11_0 b995 (by decide +kernel) (by decide +kernel)
theorem w1012:W 20 4 e914:=viaSub (ws:=[e580,e913,e914]) (consBan b647 (consBan b1010 (consBan b1011 (nilBan _ _)))) (by decide) (by decide +kernel)
theorem b1013:B 87 6 e915:=viaCut pjt_11 w1012 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1014:B 12 3 e916:=viaPerm pc18_0 pci18_0 b0 (by decide +kernel) (by decide +kernel)
theorem w1015:W 12 3 e916:=viaSub (ws:=[e16,e916]) (consBan b16 (consBan b1014 (nilBan _ _))) (by decide) (by decide +kernel)
theorem b1016:B 87 6 e917:=viaCut pjt_18 w1015 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1017:B 12 3 e918:=viaPerm pc18_0 pci18_0 b474 (by decide +kernel) (by decide +kernel)
theorem w1018:W 12 3 e918:=viaSub (ws:=[e16,e918]) (consBan b16 (consBan b1017 (nilBan _ _))) (by decide) (by decide +kernel)
theorem b1019:B 87 6 e919:=viaCut pjt_18 w1018 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1020:B 87 6 e920:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1021:B 87 6 e921:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1022:B 87 6 e922:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1023:B 87 6 e923:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1024:B 87 6 e924:=viaPerm pt3 pti3 b446 (by decide +kernel) (by decide +kernel)
theorem b1025:B 87 6 e925:=viaPerm pt3 pti3 b612 (by decide +kernel) (by decide +kernel)
theorem b1026:B 87 6 e926:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1027:B 87 6 e927:=viaPerm pt3 pti3 b852 (by decide +kernel) (by decide +kernel)
theorem b1028:B 87 6 e928:=viaPerm pt3 pti3 b935 (by decide +kernel) (by decide +kernel)
theorem b1029:B 87 6 e929:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1047:B 87 5 e946:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1056:B 87 4 e953:=viaSmall (by decide +kernel) (by decide)
theorem b1057:B 87 4 e954:=viaSmall (by decide +kernel) (by decide)
theorem b1058:B 87 4 e955:=viaSmall (by decide +kernel) (by decide)
theorem b1059:B 87 4 e956:=viaSmall (by decide +kernel) (by decide)
theorem b1060:B 87 4 e957:=viaSmall (by decide +kernel) (by decide)
theorem b1061:B 87 4 e958:=viaSmall (by decide +kernel) (by decide)
theorem b1062:B 87 4 e959:=viaSmall (by decide +kernel) (by decide)
theorem b1063:B 87 4 e960:=viaSmall (by decide +kernel) (by decide)
theorem b1064:B 87 4 e961:=viaSmall (by decide +kernel) (by decide)
theorem b1065:B 87 4 e962:=viaSmall (by decide +kernel) (by decide)
theorem b1066:B 87 4 e963:=viaSmall (by decide +kernel) (by decide)
theorem b1067:B 87 4 e964:=viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b1068:B 87 5 e965:=viaBranch (ws:=[e953,e954,e955,e956,e957,e958,e959,e960,e961,e962,e963,e964]) (consBan b1056 (consBan b1057 (consBan b1058 (consBan b1059 (consBan b1060 (consBan b1061 (consBan b1062 (consBan b1063 (consBan b1064 (consBan b1065 (consBan b1066 (consBan b1067 (nilBan _ _))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b1069:B 87 5 e966:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1070:B 87 5 e967:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1071:B 87 5 e954:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1072:B 87 5 e968:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1073:B 16 3 e969:=viaSmall (by decide +kernel) (by decide)
theorem w1074:W 16 3 e969:=widen (by decide +kernel) b1073
theorem b1075:B 87 5 e970:=viaCut pjt_9 w1074 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1084:B 87 5 e974:=viaCut pjt_11 w996 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1085:B 87 5 e975:=viaCut pjt_18 w472 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1086:B 87 5 e976:=viaCut pjt_9 w1074 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1087:B 87 5 e977:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1088:B 87 5 e978:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1089:B 87 5 e979:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1090:B 87 5 e980:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1091:B 87 5 e981:=viaCut pjt_17 w1008 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1092:B 87 5 e982:=viaCut pjt_11 w1012 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1093:B 87 5 e983:=viaCut pjt_18 w1015 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1094:B 87 5 e984:=viaPerm pt1 pti1 b1093 (by decide +kernel) (by decide +kernel)
theorem b1095:B 87 5 e985:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1096:B 87 5 e986:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1097:B 87 5 e987:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1098:B 87 5 e988:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1099:B 87 5 e989:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1100:B 87 5 e990:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1101:B 87 5 e991:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1102:B 87 5 e992:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1103:B 87 5 e993:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1104:B 87 5 e994:=viaPerm pt1 pti1 b1103 (by decide +kernel) (by decide +kernel)
theorem b1105:B 87 5 e995:=viaPerm pt1 pti1 b1087 (by decide +kernel) (by decide +kernel)
theorem b1106:B 87 5 e996:=viaPerm pt1 pti1 b1088 (by decide +kernel) (by decide +kernel)
theorem b1107:B 87 5 e997:=viaPerm pt1 pti1 b1090 (by decide +kernel) (by decide +kernel)
theorem b1108:B 87 5 e998:=viaPerm pt1 pti1 b1089 (by decide +kernel) (by decide +kernel)
theorem b1109:B 87 5 e999:=viaPerm pt1 pti1 b1095 (by decide +kernel) (by decide +kernel)
theorem b1110:B 87 5 e1000:=viaPerm pt1 pti1 b1096 (by decide +kernel) (by decide +kernel)
theorem b1111:B 87 5 e1001:=viaPerm pt1 pti1 b1097 (by decide +kernel) (by decide +kernel)
theorem b1112:B 87 5 e1002:=viaPerm pt1 pti1 b1099 (by decide +kernel) (by decide +kernel)
theorem b1113:B 87 5 e1003:=viaPerm pt1 pti1 b1100 (by decide +kernel) (by decide +kernel)
theorem b1114:B 87 5 e1004:=viaPerm pt1 pti1 b1098 (by decide +kernel) (by decide +kernel)
theorem b1115:B 87 5 e1005:=viaPerm pt1 pti1 b1075 (by decide +kernel) (by decide +kernel)
theorem b1116:B 87 5 e1006:=viaPerm pt1 pti1 b1084 (by decide +kernel) (by decide +kernel)
theorem b1117:B 87 5 e1007:=viaPerm pt1 pti1 b1086 (by decide +kernel) (by decide +kernel)
theorem b1118:B 87 5 e1008:=viaPerm pt1 pti1 b1085 (by decide +kernel) (by decide +kernel)
theorem b1119:B 87 5 e1009:=viaPerm pt1 pti1 b1047 (by decide +kernel) (by decide +kernel)
theorem b1120:B 87 5 e1010:=viaPerm pt1 pti1 b1068 (by decide +kernel) (by decide +kernel)
theorem b1121:B 87 5 e1011:=viaPerm pt1 pti1 b1069 (by decide +kernel) (by decide +kernel)
theorem b1122:B 87 5 e1012:=viaPerm pt1 pti1 b1071 (by decide +kernel) (by decide +kernel)
theorem b1123:B 87 5 e1013:=viaPerm pt1 pti1 b1072 (by decide +kernel) (by decide +kernel)
theorem b1124:B 87 5 e1014:=viaPerm pt1 pti1 b1070 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b1125:B 87 6 e1015:=viaBranch (ws:=[e946,e965,e966,e967,e954,e968,e970,e974,e975,e976,e977,e978,e979,e980,e981,e982,e983,e984,e985,e986,e987,e988,e989,e990,e991,e992,e993,e994,e995,e996,e997,e998,e999,e1000,e1001,e1002,e1003,e1004,e1005,e1006,e1007,e1008,e1009,e1010,e1011,e1012,e1013,e1014]) (consBan b1047 (consBan b1068 (consBan b1069 (consBan b1070 (consBan b1071 (consBan b1072 (consBan b1075 (consBan b1084 (consBan b1085 (consBan b1086 (consBan b1087 (consBan b1088 (consBan b1089 (consBan b1090 (consBan b1091 (consBan b1092 (consBan b1093 (consBan b1094 (consBan b1095 (consBan b1096 (consBan b1097 (consBan b1098 (consBan b1099 (consBan b1100 (consBan b1101 (consBan b1102 (consBan b1103 (consBan b1104 (consBan b1105 (consBan b1106 (consBan b1107 (consBan b1108 (consBan b1109 (consBan b1110 (consBan b1111 (consBan b1112 (consBan b1113 (consBan b1114 (consBan b1115 (consBan b1116 (consBan b1117 (consBan b1118 (consBan b1119 (consBan b1120 (consBan b1121 (consBan b1122 (consBan b1123 (consBan b1124 (nilBan _ _))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b1126:B 87 6 e1016:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1127:B 87 6 e1017:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1128:B 87 6 e1018:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1129:B 87 6 e1019:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1130:B 87 6 e1020:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1131:B 87 6 e1021:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1132:B 87 6 e1022:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1133:B 87 6 e1023:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b1134:B 35 5 e1024:=viaSmall (by decide +kernel) (by decide)
theorem w1135:W 35 5 e1024:=widen (by decide +kernel) b1134
theorem b1136:B 87 6 e1025:=viaCut pjt_1 w1135 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1137:B 87 6 e1026:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1138:B 87 6 e1027:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1139:B 87 6 e1028:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1140:B 87 6 e1029:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1141:B 87 6 e1030:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1142:B 87 6 e1031:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1143:B 87 6 e1032:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1144:B 87 6 e1033:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1145:B 87 6 e1034:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1146:B 87 6 e1035:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1147:B 87 6 e1036:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1148:B 87 6 e1037:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1149:B 87 6 e1038:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1150:B 87 6 e1039:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1151:B 87 6 e1040:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1152:B 87 6 e1041:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1153:B 87 6 e1042:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1154:B 87 6 e1043:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1155:B 87 6 e1044:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1156:B 87 6 e1045:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1157:B 87 6 e1046:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1158:B 87 6 e1047:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1159:B 87 6 e1048:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1160:B 87 6 e1049:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1161:B 87 6 e1050:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1162:B 87 6 e1051:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1163:B 87 6 e1052:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1164:B 87 6 e1053:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1165:B 87 6 e1054:=viaCut pjt_13 w992 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1166:B 87 6 e1055:=viaCut pjt_7 w795 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1167:B 87 6 e1056:=viaCut pjt_13 w992 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1168:B 12 3 e1057:=viaPerm pc18_0 pci18_0 b524 (by decide +kernel) (by decide +kernel)
theorem w1169:W 12 3 e1057:=viaSub (ws:=[e16,e1057]) (consBan b16 (consBan b1168 (nilBan _ _))) (by decide) (by decide +kernel)
theorem b1170:B 87 6 e1058:=viaCut pjt_18 w1169 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1171:B 87 6 e1059:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1172:B 87 6 e1060:=viaPerm pt1 pti1 b262 (by decide +kernel) (by decide +kernel)
theorem b1173:B 87 6 e1061:=viaPerm pt1 pti1 b497 (by decide +kernel) (by decide +kernel)
theorem b1174:B 87 6 e1062:=viaPerm pt1 pti1 b665 (by decide +kernel) (by decide +kernel)
theorem b1175:B 87 6 e1063:=viaPerm pt1 pti1 b772 (by decide +kernel) (by decide +kernel)
theorem b1176:B 87 6 e1064:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1177:B 87 6 e1065:=viaPerm pt1 pti1 b872 (by decide +kernel) (by decide +kernel)
theorem b1178:B 87 6 e1066:=viaPerm pt1 pti1 b955 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b1179:B 87 7 e1067:=viaBranch (ws:=[e888,e889,e890,e891,e892,e93,e893,e894,e895,e896,e898,e901,e902,e903,e904,e905,e906,e907,e908,e909,e912,e915,e917,e919,e920,e921,e922,e923,e924,e925,e926,e927,e928,e929,e1015,e1016,e1017,e1018,e1019,e1020,e1021,e1022,e1023,e1025,e1026,e1027,e1028,e1029,e1030,e1031,e1032,e1033,e1034,e1035,e1036,e1037,e1038,e1039,e1040,e1041,e1042,e1043,e1044,e1045,e1046,e1047,e1048,e1049,e1050,e1051,e1052,e1053,e1054,e1055,e1056,e1058,e1059,e1060,e1061,e1062,e1063,e1064,e1065,e1066]) (consBan b982 (consBan b983 (consBan b984 (consBan b985 (consBan b986 (consBan b109 (consBan b987 (consBan b988 (consBan b989 (consBan b990 (consBan b993 (consBan b997 (consBan b998 (consBan b999 (consBan b1000 (consBan b1001 (consBan b1002 (consBan b1003 (consBan b1004 (consBan b1005 (consBan b1009 (consBan b1013 (consBan b1016 (consBan b1019 (consBan b1020 (consBan b1021 (consBan b1022 (consBan b1023 (consBan b1024 (consBan b1025 (consBan b1026 (consBan b1027 (consBan b1028 (consBan b1029 (consBan b1125 (consBan b1126 (consBan b1127 (consBan b1128 (consBan b1129 (consBan b1130 (consBan b1131 (consBan b1132 (consBan b1133 (consBan b1136 (consBan b1137 (consBan b1138 (consBan b1139 (consBan b1140 (consBan b1141 (consBan b1142 (consBan b1143 (consBan b1144 (consBan b1145 (consBan b1146 (consBan b1147 (consBan b1148 (consBan b1149 (consBan b1150 (consBan b1151 (consBan b1152 (consBan b1153 (consBan b1154 (consBan b1155 (consBan b1156 (consBan b1157 (consBan b1158 (consBan b1159 (consBan b1160 (consBan b1161 (consBan b1162 (consBan b1163 (consBan b1164 (consBan b1165 (consBan b1166 (consBan b1167 (consBan b1170 (consBan b1171 (consBan b1172 (consBan b1173 (consBan b1174 (consBan b1175 (consBan b1176 (consBan b1177 (consBan b1178 (nilBan _ _))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b1180:B 87 7 e1068:=viaPerm pt4 pti4 b1179 (by decide +kernel) (by decide +kernel)
theorem b1181:B 87 7 e1069:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1189:B 87 6 e1077:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1190:B 87 6 e1078:=viaCut pjt_2 w59 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1191:B 87 6 e1079:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1192:B 87 6 e1080:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1193:B 87 6 e1081:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1194:B 87 6 e1067:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1195:B 87 6 e1082:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1196:B 87 6 e1083:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1197:B 87 6 e1084:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1198:B 87 6 e1085:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1199:B 87 6 e1086:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1200:B 87 6 e1087:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1201:B 87 6 e1088:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1202:B 87 6 e1089:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1203:B 87 6 e1090:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1204:B 87 6 e1091:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1205:B 87 6 e1092:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1206:B 87 6 e1093:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1207:B 87 6 e1094:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1208:B 87 6 e1095:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1209:B 87 6 e1096:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1210:B 87 6 e1097:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1211:B 87 6 e1098:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1212:B 87 6 e1099:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1213:B 87 6 e1100:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1214:B 87 6 e1101:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1215:B 87 6 e1102:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1216:B 87 6 e1103:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1217:B 87 6 e1104:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1218:B 87 6 e1105:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1219:B 16 3 e1106:=viaPerm pc13_0 pci13_0 b738 (by decide +kernel) (by decide +kernel)
theorem w1220:W 16 3 e1106:=widen (by decide +kernel) b1219
theorem b1221:B 87 6 e1107:=viaCut pjt_13 w1220 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1222:B 87 6 e1108:=viaCut pjt_11 w996 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1223:B 87 6 e1109:=viaCut pjt_18 w472 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1224:B 87 6 e1110:=viaCut pjt_13 w1220 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1225:B 87 6 e1111:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1226:B 87 6 e1112:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1227:B 87 6 e1113:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1228:B 87 6 e1114:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1229:B 87 6 e1115:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1230:B 87 6 e1116:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1231:B 87 6 e1117:=viaCut pjt_17 w1008 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1232:B 87 6 e1118:=viaCut pjt_11 w1012 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1233:B 87 6 e1119:=viaCut pjt_18 w1015 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1234:B 87 6 e1120:=viaCut pjt_18 w1018 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1235:B 87 6 e1121:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1236:B 87 6 e1122:=viaPerm pt3 pti3 b614 (by decide +kernel) (by decide +kernel)
theorem b1237:B 87 6 e1123:=viaPerm pt3 pti3 b449 (by decide +kernel) (by decide +kernel)
theorem b1238:B 87 6 e1124:=viaPerm pt3 pti3 b616 (by decide +kernel) (by decide +kernel)
theorem b1239:B 87 6 e1125:=viaPerm pt3 pti3 b724 (by decide +kernel) (by decide +kernel)
theorem b1240:B 87 6 e1126:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1241:B 87 6 e1127:=viaPerm pt3 pti3 b856 (by decide +kernel) (by decide +kernel)
theorem b1242:B 87 6 e1128:=viaPerm pt3 pti3 b937 (by decide +kernel) (by decide +kernel)
theorem b1243:B 87 6 e1129:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1244:B 87 6 e1130:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1245:B 87 6 e1131:=viaPerm pt1 pti1 b1131 (by decide +kernel) (by decide +kernel)
theorem b1246:B 87 6 e1132:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1247:B 87 6 e1133:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1248:B 87 6 e1134:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1249:B 87 6 e1135:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1250:B 87 6 e1136:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1251:B 87 6 e1137:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1252:B 87 6 e1138:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1253:B 87 6 e1139:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1254:B 87 6 e1140:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1255:B 87 6 e1141:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1256:B 87 6 e1142:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1257:B 87 6 e1143:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1258:B 87 6 e1144:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1259:B 87 6 e1145:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1260:B 87 6 e1146:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1261:B 87 6 e1147:=viaCut pjt_13 w1220 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1262:B 87 6 e1148:=viaCut pjt_7 w795 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1263:B 87 6 e1149:=viaCut pjt_13 w1220 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1264:B 87 6 e1150:=viaCut pjt_18 w1169 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1265:B 87 6 e1151:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1266:B 87 6 e1152:=viaPerm pt1 pti1 b268 (by decide +kernel) (by decide +kernel)
theorem b1267:B 87 6 e1153:=viaPerm pt1 pti1 b501 (by decide +kernel) (by decide +kernel)
theorem b1268:B 87 6 e1154:=viaPerm pt1 pti1 b667 (by decide +kernel) (by decide +kernel)
theorem b1269:B 87 6 e1155:=viaPerm pt1 pti1 b776 (by decide +kernel) (by decide +kernel)
theorem b1270:B 87 6 e1156:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1271:B 87 6 e1157:=viaPerm pt1 pti1 b876 (by decide +kernel) (by decide +kernel)
theorem b1272:B 87 6 e1158:=viaPerm pt1 pti1 b957 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b1273:B 87 7 e921:=viaBranch (ws:=[e1077,e1078,e1079,e1080,e638,e1081,e754,e838,e1067,e920,e922,e1082,e1083,e1084,e1085,e1086,e1087,e1088,e1089,e1090,e1091,e1092,e1093,e1094,e1095,e1096,e1097,e1098,e1099,e1100,e1101,e1102,e1103,e1104,e1105,e1107,e1108,e1109,e1110,e1111,e1112,e1113,e1114,e1115,e1116,e1117,e1118,e1119,e1120,e1121,e1122,e1123,e1124,e1125,e1126,e1127,e1128,e1129,e1130,e1131,e1132,e1133,e1134,e1135,e1136,e1137,e1138,e1139,e1140,e1141,e1142,e1143,e1144,e1145,e1146,e1147,e1148,e1149,e1150,e1151,e1152,e1153,e1154,e1155,e1156,e1157,e1158]) (consBan b1189 (consBan b1190 (consBan b1191 (consBan b1192 (consBan b708 (consBan b1193 (consBan b842 (consBan b930 (consBan b1194 (consBan b1020 (consBan b1022 (consBan b1195 (consBan b1196 (consBan b1197 (consBan b1198 (consBan b1199 (consBan b1200 (consBan b1201 (consBan b1202 (consBan b1203 (consBan b1204 (consBan b1205 (consBan b1206 (consBan b1207 (consBan b1208 (consBan b1209 (consBan b1210 (consBan b1211 (consBan b1212 (consBan b1213 (consBan b1214 (consBan b1215 (consBan b1216 (consBan b1217 (consBan b1218 (consBan b1221 (consBan b1222 (consBan b1223 (consBan b1224 (consBan b1225 (consBan b1226 (consBan b1227 (consBan b1228 (consBan b1229 (consBan b1230 (consBan b1231 (consBan b1232 (consBan b1233 (consBan b1234 (consBan b1235 (consBan b1236 (consBan b1237 (consBan b1238 (consBan b1239 (consBan b1240 (consBan b1241 (consBan b1242 (consBan b1243 (consBan b1244 (consBan b1245 (consBan b1246 (consBan b1247 (consBan b1248 (consBan b1249 (consBan b1250 (consBan b1251 (consBan b1252 (consBan b1253 (consBan b1254 (consBan b1255 (consBan b1256 (consBan b1257 (consBan b1258 (consBan b1259 (consBan b1260 (consBan b1261 (consBan b1262 (consBan b1263 (consBan b1264 (consBan b1265 (consBan b1266 (consBan b1267 (consBan b1268 (consBan b1269 (consBan b1270 (consBan b1271 (consBan b1272 (nilBan _ _)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b1274:B 87 7 e1159:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1275:B 87 7 e1160:=viaPerm pt4 pti4 b1273 (by decide +kernel) (by decide +kernel)
theorem b1276:B 87 7 e1161:=viaPerm pt4 pti4 b1274 (by decide +kernel) (by decide +kernel)
theorem b1277:B 87 7 e1162:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1283:B 87 6 e1168:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1284:B 87 6 e1169:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1285:B 87 6 e1170:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1286:B 87 6 e1171:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1287:B 87 6 e1172:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1288:B 87 6 e1173:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1289:B 87 6 e1174:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1290:B 87 6 e1175:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1291:B 6 3 e1176:=viaSmall (by decide +kernel) (by decide)
theorem w1292:W 6 3 e1176:=widen (by decide +kernel) b1291
theorem b1293:B 87 6 e1177:=viaCut pjt_32 w1292 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1294:B 87 6 e1178:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1295:B 87 6 e1179:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1296:B 87 6 e1180:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1297:B 87 6 e1181:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1298:B 87 6 e1182:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1299:B 87 6 e1183:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1300:B 87 6 e1184:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1302:B 20 3 e193:=viaSmall (by decide +kernel) (by decide)
theorem b1321:B 87 5 e1197:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1322:B 87 5 e1198:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1323:B 87 5 e1199:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1324:B 87 5 e1200:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1325:B 87 5 e1201:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1326:B 87 5 e1202:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1327:B 6 2 e1203:=viaSmall (by decide +kernel) (by decide)
theorem w1328:W 6 2 e1203:=viaSub (ws:=[e62,e1203]) (consBan b90 (consBan b1327 (nilBan _ _))) (by decide) (by decide +kernel)
theorem b1329:B 87 5 e1204:=viaCut pjt_32 w1328 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1330:B 20 3 e1205:=viaSmall (by decide +kernel) (by decide)
theorem w1331:W 20 3 e193:=viaSub (ws:=[e1205,e193]) (consBan b1330 (consBan b1302 (nilBan _ _))) (by decide) (by decide +kernel)
theorem b1332:B 87 5 e1206:=viaCut pjt_11 w1331 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1333:B 6 2 e1203:=viaSmall (by decide +kernel) (by decide)
theorem w1334:W 6 2 e1203:=viaSub (ws:=[e62,e1203]) (consBan b914 (consBan b1333 (nilBan _ _))) (by decide) (by decide +kernel)
theorem b1335:B 87 5 e1207:=viaCut pjt_27 w1334 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1336:B 87 5 e1208:=viaCut pjt_18 w475 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1337:B 87 5 e1209:=viaPerm pt0 pti0 b1321 (by decide +kernel) (by decide +kernel)
theorem b1338:B 87 5 e1210:=viaPerm pt0 pti0 b1322 (by decide +kernel) (by decide +kernel)
theorem b1339:B 87 5 e1211:=viaPerm pt0 pti0 b1323 (by decide +kernel) (by decide +kernel)
theorem b1340:B 87 5 e1212:=viaPerm pt0 pti0 b1324 (by decide +kernel) (by decide +kernel)
theorem b1341:B 87 5 e1213:=viaPerm pt0 pti0 b1325 (by decide +kernel) (by decide +kernel)
theorem b1342:B 87 5 e1214:=viaPerm pt0 pti0 b1326 (by decide +kernel) (by decide +kernel)
theorem b1343:B 87 5 e1215:=viaPerm pt0 pti0 b1329 (by decide +kernel) (by decide +kernel)
theorem b1344:B 87 5 e1216:=viaPerm pt0 pti0 b1332 (by decide +kernel) (by decide +kernel)
theorem b1345:B 87 5 e1217:=viaPerm pt0 pti0 b1335 (by decide +kernel) (by decide +kernel)
theorem b1346:B 87 5 e1218:=viaPerm pt0 pti0 b1336 (by decide +kernel) (by decide +kernel)
theorem b1347:B 87 5 e1219:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1348:B 87 5 e1220:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1349:B 87 5 e1221:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1350:B 87 5 e1222:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1351:B 87 5 e1223:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1352:B 87 5 e1224:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1353:B 87 5 e1225:=viaPerm pt0 pti0 b1352 (by decide +kernel) (by decide +kernel)
theorem b1354:B 87 5 e1226:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1355:B 87 5 e1227:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1356:B 87 5 e1228:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1357:B 87 5 e1229:=viaPerm pt0 pti0 b1355 (by decide +kernel) (by decide +kernel)
theorem b1358:B 87 5 e1230:=viaPerm pt0 pti0 b1356 (by decide +kernel) (by decide +kernel)
theorem b1359:B 87 5 e1231:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1360:B 87 5 e1232:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1361:B 87 5 e1233:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1362:B 87 5 e1234:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1363:B 87 5 e1235:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1364:B 87 5 e1236:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1365:B 87 5 e1237:=viaPerm pt0 pti0 b1359 (by decide +kernel) (by decide +kernel)
theorem b1366:B 87 5 e1238:=viaPerm pt0 pti0 b1360 (by decide +kernel) (by decide +kernel)
theorem b1367:B 87 5 e1239:=viaPerm pt0 pti0 b1361 (by decide +kernel) (by decide +kernel)
theorem b1368:B 87 5 e1240:=viaPerm pt0 pti0 b1363 (by decide +kernel) (by decide +kernel)
theorem b1369:B 87 5 e1241:=viaPerm pt0 pti0 b1364 (by decide +kernel) (by decide +kernel)
theorem b1370:B 87 5 e1242:=viaPerm pt0 pti0 b1362 (by decide +kernel) (by decide +kernel)
theorem b1372:B 87 5 e1244:=viaCut pjt_10 w518 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1373:B 20 3 e1245:=viaSmall (by decide +kernel) (by decide)
theorem w1374:W 20 3 e1245:=viaSub (ws:=[e1205,e1245]) (consBan b1330 (consBan b1373 (nilBan _ _))) (by decide) (by decide +kernel)
theorem b1375:B 87 5 e1246:=viaCut pjt_11 w1374 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1376:B 6 2 e1203:=viaSmall (by decide +kernel) (by decide)
theorem w1377:W 6 2 e1203:=viaSub (ws:=[e62,e1203]) (consBan b68 (consBan b1376 (nilBan _ _))) (by decide) (by decide +kernel)
theorem b1378:B 87 5 e1247:=viaCut pjt_28 w1377 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1379:B 87 5 e1248:=viaPerm pt0 pti0 b1378 (by decide +kernel) (by decide +kernel)
theorem b1380:B 87 5 e1249:=viaPerm pt0 pti0 b1347 (by decide +kernel) (by decide +kernel)
theorem b1381:B 87 5 e1250:=viaPerm pt0 pti0 b1348 (by decide +kernel) (by decide +kernel)
theorem b1382:B 87 5 e1251:=viaPerm pt0 pti0 b1349 (by decide +kernel) (by decide +kernel)
theorem b1383:B 87 5 e1252:=viaPerm pt0 pti0 b1350 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b1384:B 87 6 e1253:=viaBranch (ws:=[e1197,e1198,e1199,e1200,e1201,e1202,e1204,e1206,e1207,e1208,e1209,e1210,e1211,e1212,e1213,e1214,e1215,e1216,e1217,e1218,e1219,e1220,e1221,e1222,e1223,e1224,e1225,e1226,e1227,e1228,e1229,e1230,e1231,e1232,e1233,e1234,e1235,e1236,e1237,e1238,e1239,e1240,e1241,e1242,e1244,e1246,e1247,e1248,e1249,e1250,e1251,e1252]) (consBan b1321 (consBan b1322 (consBan b1323 (consBan b1324 (consBan b1325 (consBan b1326 (consBan b1329 (consBan b1332 (consBan b1335 (consBan b1336 (consBan b1337 (consBan b1338 (consBan b1339 (consBan b1340 (consBan b1341 (consBan b1342 (consBan b1343 (consBan b1344 (consBan b1345 (consBan b1346 (consBan b1347 (consBan b1348 (consBan b1349 (consBan b1350 (consBan b1351 (consBan b1352 (consBan b1353 (consBan b1354 (consBan b1355 (consBan b1356 (consBan b1357 (consBan b1358 (consBan b1359 (consBan b1360 (consBan b1361 (consBan b1362 (consBan b1363 (consBan b1364 (consBan b1365 (consBan b1366 (consBan b1367 (consBan b1368 (consBan b1369 (consBan b1370 (consBan b1372 (consBan b1375 (consBan b1378 (consBan b1379 (consBan b1380 (consBan b1381 (consBan b1382 (consBan b1383 (nilBan _ _))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b1386:B 12 3 e1255:=viaSmall (by decide +kernel) (by decide)
theorem w1387:W 12 3 e1255:=widen (by decide +kernel) b1386
theorem b1388:B 87 5 e1256:=viaCut pjt_14 w1387 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1389:B 12 3 e1257:=viaSmall (by decide +kernel) (by decide)
theorem w1390:W 12 3 e1257:=widen (by decide +kernel) b1389
theorem b1391:B 87 5 e1258:=viaCut pjt_14 w1390 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1392:B 87 5 e1259:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1393:B 87 5 e1260:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1394:B 87 5 e1261:=viaCut pjt_27 w1334 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1395:B 87 5 e1262:=viaCut pjt_32 w1328 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1396:B 87 5 e1263:=viaCut pjt_32 w1328 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1397:B 87 5 e1264:=viaCut pjt_32 w1328 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1398:B 87 5 e1265:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1399:B 87 5 e1266:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1400:B 87 5 e1267:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1401:B 87 5 e1268:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1402:B 87 5 e1269:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1403:B 87 5 e1270:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1404:B 87 5 e1271:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1405:B 87 5 e1272:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1406:B 87 5 e1273:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1407:B 87 5 e1274:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1408:B 87 5 e1275:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1409:B 87 5 e1276:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1410:B 87 5 e1277:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1411:B 87 5 e1278:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1412:B 87 5 e1279:=viaCut pjt_32 w1328 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1413:B 87 5 e1280:=viaCut pjt_18 w525 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1414:B 87 5 e1281:=viaCut pjt_32 w1328 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1415:B 6 2 e1176:=viaSmall (by decide +kernel) (by decide)
theorem w1416:W 6 2 e1176:=widen (by decide +kernel) b1415
theorem b1417:B 87 5 e1282:=viaCut pjt_32 w1416 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1418:B 87 5 e1283:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1419:B 16 3 e1284:=viaSmall (by decide +kernel) (by decide)
theorem w1420:W 16 3 e1284:=widen (by decide +kernel) b1419
theorem b1421:B 87 5 e1285:=viaCut pjt_15 w1420 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1422:B 87 5 e1286:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1423:B 87 5 e1287:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1424:B 87 5 e1288:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1425:B 87 5 e1289:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1426:B 87 5 e1290:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1427:B 87 5 e1291:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1428:B 87 5 e1292:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b1429:B 87 6 e1293:=viaBranch (ws:=[e1256,e1258,e1259,e1260,e1261,e1262,e1263,e1264,e1265,e1266,e1267,e1268,e1269,e1270,e1271,e1272,e1273,e1274,e1275,e1276,e1277,e1278,e1279,e1246,e1280,e1248,e1281,e1282,e1283,e1285,e1286,e1287,e1288,e1289,e1290,e1291,e1292]) (consBan b1388 (consBan b1391 (consBan b1392 (consBan b1393 (consBan b1394 (consBan b1395 (consBan b1396 (consBan b1397 (consBan b1398 (consBan b1399 (consBan b1400 (consBan b1401 (consBan b1402 (consBan b1403 (consBan b1404 (consBan b1405 (consBan b1406 (consBan b1407 (consBan b1408 (consBan b1409 (consBan b1410 (consBan b1411 (consBan b1412 (consBan b1375 (consBan b1413 (consBan b1379 (consBan b1414 (consBan b1417 (consBan b1418 (consBan b1421 (consBan b1422 (consBan b1423 (consBan b1424 (consBan b1425 (consBan b1426 (consBan b1427 (consBan b1428 (nilBan _ _)))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b1430:B 87 6 e1294:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1431:B 87 6 e1295:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1432:B 87 6 e1292:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1433:B 87 6 e1296:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1434:B 87 6 e1297:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1435:B 87 6 e1298:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1436:B 87 6 e1299:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1437:B 87 6 e1300:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1438:B 87 6 e1301:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1439:B 87 6 e1302:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1440:B 87 6 e1303:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1441:B 87 6 e1304:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1442:B 87 6 e1305:=viaCut pjt_32 w1328 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1443:B 20 4 e1306:=viaPerm pc11_2 pci11_2 b994 (by decide +kernel) (by decide +kernel)
theorem b1444:B 20 4 e1307:=viaSmall (by decide +kernel) (by decide)
theorem w1445:W 20 4 e1307:=viaSub (ws:=[e1306,e581,e1307]) (consBan b1443 (consBan b648 (consBan b1444 (nilBan _ _)))) (by decide) (by decide +kernel)
theorem b1446:B 87 6 e1308:=viaCut pjt_11 w1445 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1447:B 87 6 e1309:=viaCut pjt_32 w1328 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1448:B 87 6 e1310:=viaCut pjt_18 w475 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1449:B 87 6 e1311:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1450:B 87 6 e1312:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1451:B 87 6 e1313:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1452:B 87 6 e1314:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1453:B 87 6 e1315:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1454:B 87 6 e1316:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1455:B 87 6 e1317:=viaCut pjt_32 w1328 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1456:B 87 6 e1318:=viaCut pjt_32 w1328 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1457:B 87 6 e1319:=viaCut pjt_32 w1328 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1458:B 87 6 e1320:=viaCut pjt_32 w1328 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1459:B 87 6 e1321:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1460:B 87 6 e1322:=viaPerm pt3 pti3 b478 (by decide +kernel) (by decide +kernel)
theorem b1461:B 87 6 e1323:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1462:B 87 6 e1324:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1463:B 87 6 e1325:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1464:B 87 6 e1326:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1465:B 87 6 e1327:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1466:B 87 6 e1328:=viaPerm pt3 pti3 b1001 (by decide +kernel) (by decide +kernel)
theorem b1467:B 87 6 e1329:=viaPerm pt1 pti1 b1160 (by decide +kernel) (by decide +kernel)
theorem b1468:B 87 6 e1330:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1469:B 87 6 e1331:=viaPerm pt3 pti3 b1226 (by decide +kernel) (by decide +kernel)
theorem b1470:B 87 6 e1332:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1471:B 87 6 e1333:=viaPerm pt1 pti1 b1256 (by decide +kernel) (by decide +kernel)
theorem b1472:B 87 6 e1334:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1473:B 87 6 e1335:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1474:B 87 6 e1336:=viaPerm pt3 pti3 b1450 (by decide +kernel) (by decide +kernel)
theorem b1475:B 87 6 e1337:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1476:B 87 6 e1338:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1477:B 87 6 e1339:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1478:B 87 6 e1340:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1479:B 87 6 e1341:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1480:B 87 6 e1342:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1481:B 87 6 e1343:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1482:B 87 6 e1344:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1483:B 87 6 e1345:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1484:B 87 6 e1346:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1485:B 87 6 e1347:=viaCut pjt_32 w1328 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1486:B 20 4 e1348:=viaSmall (by decide +kernel) (by decide)
theorem w1487:W 20 4 e1348:=viaSub (ws:=[e1306,e1348]) (consBan b1443 (consBan b1486 (nilBan _ _))) (by decide) (by decide +kernel)
theorem b1488:B 87 6 e1349:=viaCut pjt_11 w1487 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1489:B 87 6 e1350:=viaCut pjt_18 w525 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1490:B 87 6 e1351:=viaCut pjt_32 w1328 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1491:B 87 6 e1352:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1492:B 87 6 e1353:=viaPerm pt1 pti1 b297 (by decide +kernel) (by decide +kernel)
theorem b1493:B 87 6 e1354:=viaPerm pt1 pti1 b510 (by decide +kernel) (by decide +kernel)
theorem b1494:B 87 6 e1355:=viaPerm pt1 pti1 b670 (by decide +kernel) (by decide +kernel)
theorem b1495:B 87 6 e1356:=viaPerm pt1 pti1 b785 (by decide +kernel) (by decide +kernel)
theorem b1496:B 87 6 e1357:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1497:B 87 6 e1358:=viaPerm pt1 pti1 b885 (by decide +kernel) (by decide +kernel)
theorem b1498:B 87 6 e1359:=viaPerm pt1 pti1 b960 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b1499:B 87 7 e1360:=viaBranch (ws:=[e1168,e538,e1169,e840,e1170,e1171,e1172,e1173,e1174,e1175,e1177,e1178,e1179,e1180,e1181,e1182,e1183,e1184,e1253,e1293,e1294,e1295,e1292,e1296,e1297,e1298,e1299,e1300,e1301,e1302,e1303,e1304,e1305,e1308,e1309,e1310,e1311,e1312,e1313,e1314,e1315,e1316,e1317,e1318,e1319,e1320,e1321,e1322,e1323,e1324,e1325,e1326,e1327,e1328,e1329,e1330,e1331,e1332,e1333,e1334,e1335,e1336,e1337,e1338,e1339,e1340,e1341,e1342,e1343,e1344,e1345,e1346,e1347,e1349,e1350,e1351,e1352,e1353,e1354,e1355,e1356,e1357,e1358,e1359]) (consBan b1283 (consBan b603 (consBan b1284 (consBan b932 (consBan b1285 (consBan b1286 (consBan b1287 (consBan b1288 (consBan b1289 (consBan b1290 (consBan b1293 (consBan b1294 (consBan b1295 (consBan b1296 (consBan b1297 (consBan b1298 (consBan b1299 (consBan b1300 (consBan b1384 (consBan b1429 (consBan b1430 (consBan b1431 (consBan b1432 (consBan b1433 (consBan b1434 (consBan b1435 (consBan b1436 (consBan b1437 (consBan b1438 (consBan b1439 (consBan b1440 (consBan b1441 (consBan b1442 (consBan b1446 (consBan b1447 (consBan b1448 (consBan b1449 (consBan b1450 (consBan b1451 (consBan b1452 (consBan b1453 (consBan b1454 (consBan b1455 (consBan b1456 (consBan b1457 (consBan b1458 (consBan b1459 (consBan b1460 (consBan b1461 (consBan b1462 (consBan b1463 (consBan b1464 (consBan b1465 (consBan b1466 (consBan b1467 (consBan b1468 (consBan b1469 (consBan b1470 (consBan b1471 (consBan b1472 (consBan b1473 (consBan b1474 (consBan b1475 (consBan b1476 (consBan b1477 (consBan b1478 (consBan b1479 (consBan b1480 (consBan b1481 (consBan b1482 (consBan b1483 (consBan b1484 (consBan b1485 (consBan b1488 (consBan b1489 (consBan b1490 (consBan b1491 (consBan b1492 (consBan b1493 (consBan b1494 (consBan b1495 (consBan b1496 (consBan b1497 (consBan b1498 (nilBan _ _))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b1500:B 87 6 e1361:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1501:B 87 6 e1362:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1502:B 87 6 e1363:=viaPerm pt4 pti4 b983 (by decide +kernel) (by decide +kernel)
theorem b1503:B 87 6 e1364:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1504:B 87 6 e1365:=viaPerm pt4 pti4 b1216 (by decide +kernel) (by decide +kernel)
theorem b1505:B 87 6 e1366:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1506:B 87 6 e1367:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1507:B 87 6 e1368:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1508:B 16 3 e910:=viaSmall (by decide +kernel) (by decide)
theorem b1509:B 16 3 e911:=viaSmall (by decide +kernel) (by decide)
theorem w1510:W 16 3 e911:=viaSub (ws:=[e910,e911]) (consBan b1508 (consBan b1509 (nilBan _ _))) (by decide) (by decide +kernel)
theorem b1511:B 87 6 e1369:=viaCut pjt_13 w1510 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1512:B 87 6 e1370:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1513:B 87 6 e1371:=viaPerm pt2 pti2 b1136 (by decide +kernel) (by decide +kernel)
theorem b1514:B 87 6 e1372:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1515:B 87 6 e1373:=viaPerm pt2 pti2 b1137 (by decide +kernel) (by decide +kernel)
theorem b1516:B 87 6 e1374:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1517:B 87 6 e1375:=viaPerm pt2 pti2 b1252 (by decide +kernel) (by decide +kernel)
theorem b1518:B 87 6 e1376:=viaPerm pt0 pti0 b1429 (by decide +kernel) (by decide +kernel)
theorem b1519:B 87 5 e1377:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1520:B 16 3 e1378:=viaSmall (by decide +kernel) (by decide)
theorem w1521:W 16 3 e1378:=widen (by decide +kernel) b1520
theorem b1522:B 87 5 e1379:=viaCut pjt_10 w1521 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1523:B 87 5 e1380:=viaCut pjt_32 w1328 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1524:B 87 5 e1381:=viaCut pjt_7 w795 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1525:B 87 5 e1382:=viaCut pjt_28 w1377 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1526:B 87 5 e1383:=viaPerm pt0 pti0 b1525 (by decide +kernel) (by decide +kernel)
theorem b1527:B 87 5 e1384:=viaPerm pt0 pti0 b1417 (by decide +kernel) (by decide +kernel)
theorem b1528:B 87 5 e1385:=viaCut pjt_17 w1008 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1529:B 87 5 e1386:=viaPerm pt0 pti0 b1519 (by decide +kernel) (by decide +kernel)
theorem b1530:B 87 5 e1387:=viaPerm pt0 pti0 b1522 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b1531:B 87 6 e1388:=viaBranch (ws:=[e1377,e1379,e1380,e1381,e1382,e1383,e1282,e1384,e1385,e1386,e1387]) (consBan b1519 (consBan b1522 (consBan b1523 (consBan b1524 (consBan b1525 (consBan b1526 (consBan b1417 (consBan b1527 (consBan b1528 (consBan b1529 (consBan b1530 (nilBan _ _)))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b1532:B 87 6 e1389:=viaPerm pt0 pti0 b1431 (by decide +kernel) (by decide +kernel)
theorem b1533:B 87 6 e1390:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1534:B 87 6 e1391:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1535:B 87 6 e1392:=viaPerm pt4 pti4 b1438 (by decide +kernel) (by decide +kernel)
theorem b1536:B 87 6 e1393:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1537:B 87 6 e1394:=viaCut pjt_32 w1328 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1538:B 20 4 e1395:=viaSmall (by decide +kernel) (by decide)
theorem w1539:W 20 4 e1395:=viaSub (ws:=[e1306,e899,e1395]) (consBan b1443 (consBan b994 (consBan b1538 (nilBan _ _)))) (by decide) (by decide +kernel)
theorem b1540:B 87 6 e1396:=viaCut pjt_11 w1539 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1541:B 87 6 e1397:=viaCut pjt_32 w1328 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1542:B 87 6 e1398:=viaCut pjt_18 w475 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1543:B 87 6 e1399:=viaCut pjt_9 w466 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1544:B 87 6 e1400:=viaCut pjt_18 w475 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1545:B 87 6 e1401:=viaPerm pt2 pti2 b1475 (by decide +kernel) (by decide +kernel)
theorem b1546:B 87 6 e1402:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1547:B 87 6 e1403:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1548:B 87 6 e1404:=viaPerm pt3 pti3 b99 (by decide +kernel) (by decide +kernel)
theorem b1549:B 87 6 e1405:=viaPerm pt3 pti3 b634 (by decide +kernel) (by decide +kernel)
theorem b1550:B 87 6 e1406:=viaPerm pt3 pti3 b753 (by decide +kernel) (by decide +kernel)
theorem b1551:B 87 6 e1407:=viaPerm pt3 pti3 b754 (by decide +kernel) (by decide +kernel)
theorem b1552:B 87 6 e1408:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1553:B 87 6 e1409:=viaPerm pt3 pti3 b946 (by decide +kernel) (by decide +kernel)
theorem b1554:B 87 6 e1410:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1555:B 87 6 e1411:=viaPerm pt3 pti3 b143 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b1556:B 35 5 e1412:=viaSmall (by decide +kernel) (by decide)
theorem w1557:W 35 5 e1412:=widen (by decide +kernel) b1556
theorem b1558:B 87 6 e1413:=viaCut pjt_0 w1557 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1559:B 87 6 e1414:=viaPerm pt3 pti3 b653 (by decide +kernel) (by decide +kernel)
theorem b1560:B 87 6 e1415:=viaPerm pt3 pti3 b722 (by decide +kernel) (by decide +kernel)
theorem b1561:B 87 6 e1416:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1562:B 87 6 e1417:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1563:B 87 6 e1418:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1564:B 87 6 e1419:=viaPerm pt3 pti3 b1002 (by decide +kernel) (by decide +kernel)
theorem b1565:B 87 6 e1420:=viaPerm pt1 pti1 b1161 (by decide +kernel) (by decide +kernel)
theorem b1566:B 87 6 e1421:=viaPerm pt3 pti3 b1227 (by decide +kernel) (by decide +kernel)
theorem b1567:B 87 6 e1422:=viaPerm pt1 pti1 b1257 (by decide +kernel) (by decide +kernel)
theorem b1568:B 87 6 e1423:=viaPerm pt3 pti3 b1451 (by decide +kernel) (by decide +kernel)
theorem b1569:B 87 6 e1424:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1570:B 87 6 e1425:=viaPerm pt3 pti3 b920 (by decide +kernel) (by decide +kernel)
theorem b1571:B 87 6 e1426:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1572:B 87 6 e1427:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1573:B 87 6 e1428:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1574:B 87 6 e1429:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1575:B 87 6 e1430:=viaCut pjt_32 w1328 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1576:B 87 6 e1431:=viaCut pjt_7 w795 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1577:B 87 6 e1432:=viaCut pjt_18 w525 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1578:B 87 6 e1433:=viaCut pjt_32 w1328 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1579:B 87 6 e1434:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1580:B 87 6 e1435:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1581:B 87 6 e1436:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1582:B 87 6 e1437:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1583:B 87 6 e1438:=viaCut pjt_17 w1008 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1584:B 20 4 e1439:=viaSmall (by decide +kernel) (by decide)
theorem w1585:W 20 4 e1439:=viaSub (ws:=[e580,e1439]) (consBan b647 (consBan b1584 (nilBan _ _))) (by decide) (by decide +kernel)
theorem b1586:B 87 6 e1440:=viaCut pjt_11 w1585 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1587:B 87 6 e1441:=viaCut pjt_18 w525 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1588:B 87 6 e1442:=viaCut pjt_18 w1169 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1589:B 87 6 e1443:=viaPerm pt1 pti1 b298 (by decide +kernel) (by decide +kernel)
theorem b1590:B 87 6 e1444:=viaPerm pt1 pti1 b511 (by decide +kernel) (by decide +kernel)
theorem b1591:B 87 6 e1445:=viaPerm pt1 pti1 b786 (by decide +kernel) (by decide +kernel)
theorem b1592:B 87 6 e1446:=viaPerm pt1 pti1 b886 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b1593:B 87 7 e1447:=viaBranch (ws:=[e395,e537,e396,e1361,e759,e1362,e1363,e1364,e1365,e1366,e1367,e1368,e1177,e1369,e1179,e1370,e1371,e1372,e1373,e1374,e1375,e1376,e1388,e1389,e1390,e1391,e1392,e1393,e1394,e1396,e1397,e1398,e1399,e582,e823,e1400,e1401,e1402,e1403,e1404,e1405,e1406,e1407,e1408,e1409,e1410,e1411,e1413,e1414,e1415,e1416,e1417,e1418,e1419,e1420,e1421,e1422,e1423,e1424,e1425,e1426,e1427,e1428,e1429,e1430,e1431,e1432,e1433,e1434,e1435,e1436,e1437,e1438,e1440,e1441,e1442,e1443,e1444,e1445,e1446]) (consBan b440 (consBan b602 (consBan b441 (consBan b1500 (consBan b847 (consBan b1501 (consBan b1502 (consBan b1503 (consBan b1504 (consBan b1505 (consBan b1506 (consBan b1507 (consBan b1293 (consBan b1511 (consBan b1295 (consBan b1512 (consBan b1513 (consBan b1514 (consBan b1515 (consBan b1516 (consBan b1517 (consBan b1518 (consBan b1531 (consBan b1532 (consBan b1533 (consBan b1534 (consBan b1535 (consBan b1536 (consBan b1537 (consBan b1540 (consBan b1541 (consBan b1542 (consBan b1543 (consBan b649 (consBan b915 (consBan b1544 (consBan b1545 (consBan b1546 (consBan b1547 (consBan b1548 (consBan b1549 (consBan b1550 (consBan b1551 (consBan b1552 (consBan b1553 (consBan b1554 (consBan b1555 (consBan b1558 (consBan b1559 (consBan b1560 (consBan b1561 (consBan b1562 (consBan b1563 (consBan b1564 (consBan b1565 (consBan b1566 (consBan b1567 (consBan b1568 (consBan b1569 (consBan b1570 (consBan b1571 (consBan b1572 (consBan b1573 (consBan b1574 (consBan b1575 (consBan b1576 (consBan b1577 (consBan b1578 (consBan b1579 (consBan b1580 (consBan b1581 (consBan b1582 (consBan b1583 (consBan b1586 (consBan b1587 (consBan b1588 (consBan b1589 (consBan b1590 (consBan b1591 (consBan b1592 (nilBan _ _))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b1594:B 87 7 e1425:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1614:B 87 6 e1465:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1615:B 87 6 e1466:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1616:B 87 6 e1467:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1617:B 87 6 e1468:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1618:B 87 6 e1469:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1619:B 87 6 e1470:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1620:B 87 6 e1471:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1621:B 87 6 e1360:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1622:B 87 6 e1472:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1623:B 87 6 e1473:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1624:B 87 6 e1474:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1625:B 87 6 e1475:=viaPerm pt0 pti0 b1213 (by decide +kernel) (by decide +kernel)
theorem b1626:B 87 6 e1476:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1627:B 87 6 e1477:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1628:B 87 6 e1478:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1629:B 87 6 e1479:=viaPerm pt0 pti0 b1434 (by decide +kernel) (by decide +kernel)
theorem b1630:B 87 6 e1480:=viaPerm pt0 pti0 b1534 (by decide +kernel) (by decide +kernel)
theorem b1631:B 87 6 e1481:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1632:B 87 6 e1482:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1633:B 87 6 e1483:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1634:B 87 6 e1484:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1635:B 87 6 e1485:=viaPerm pt4 pti4 b1439 (by decide +kernel) (by decide +kernel)
theorem b1636:B 87 6 e1486:=viaPerm pt4 pti4 b1536 (by decide +kernel) (by decide +kernel)
theorem b1637:B 87 6 e1487:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1638:B 87 6 e1488:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1639:B 87 6 e1489:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1640:B 6 2 e1490:=viaSmall (by decide +kernel) (by decide)
theorem w1641:W 6 2 e1490:=viaSub (ws:=[e62,e1490]) (consBan b90 (consBan b1640 (nilBan _ _))) (by decide) (by decide +kernel)
theorem b1642:B 87 6 e1491:=viaCut pjt_32 w1641 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1643:B 20 4 e12:=viaSmall (by decide +kernel) (by decide)
theorem b1644:B 20 4 e1492:=viaSmall (by decide +kernel) (by decide)
theorem b1645:B 20 4 e1493:=viaSmall (by decide +kernel) (by decide)
theorem w1646:W 20 4 e1493:=viaSub (ws:=[e12,e1492,e1493]) (consBan b1643 (consBan b1644 (consBan b1645 (nilBan _ _)))) (by decide) (by decide +kernel)
theorem b1647:B 87 6 e1494:=viaCut pjt_11 w1646 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1648:B 87 6 e1495:=viaCut pjt_32 w1641 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1649:B 87 6 e1496:=viaCut pjt_18 w475 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1650:B 87 6 e1497:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1651:B 87 6 e1498:=viaPerm pt2 pti2 b1477 (by decide +kernel) (by decide +kernel)
theorem b1652:B 87 6 e1499:=viaPerm pt2 pti2 b1569 (by decide +kernel) (by decide +kernel)
theorem b1653:B 87 6 e1500:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1654:B 87 6 e1501:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1655:B 87 6 e1502:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1656:B 87 6 e1503:=viaCut pjt_32 w1641 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1657:B 87 6 e1504:=viaCut pjt_32 w1641 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1658:B 87 6 e1505:=viaCut pjt_32 w1641 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1659:B 6 2 e1490:=viaSmall (by decide +kernel) (by decide)
theorem w1660:W 6 2 e1490:=viaSub (ws:=[e62,e1490]) (consBan b914 (consBan b1659 (nilBan _ _))) (by decide) (by decide +kernel)
theorem b1661:B 87 6 e1506:=viaCut pjt_27 w1660 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1662:B 87 6 e1507:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1663:B 87 6 e1508:=viaCut pjt_0 w1557 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1664:B 87 6 e1509:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1665:B 87 6 e1510:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1666:B 87 6 e1511:=viaPerm pt3 pti3 b755 (by decide +kernel) (by decide +kernel)
theorem b1667:B 87 6 e1512:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1668:B 87 6 e1513:=viaPerm pt3 pti3 b831 (by decide +kernel) (by decide +kernel)
theorem b1669:B 87 6 e1514:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1670:B 87 6 e1515:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1671:B 87 6 e1516:=viaPerm pt3 pti3 b1003 (by decide +kernel) (by decide +kernel)
theorem b1672:B 87 6 e1517:=viaPerm pt1 pti1 b1162 (by decide +kernel) (by decide +kernel)
theorem b1673:B 87 6 e1518:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1674:B 87 6 e1519:=viaPerm pt3 pti3 b1228 (by decide +kernel) (by decide +kernel)
theorem b1675:B 87 6 e1520:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1676:B 87 6 e1521:=viaPerm pt1 pti1 b1258 (by decide +kernel) (by decide +kernel)
theorem b1677:B 87 6 e1522:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1678:B 87 6 e1523:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1679:B 87 6 e1524:=viaPerm pt3 pti3 b1452 (by decide +kernel) (by decide +kernel)
theorem b1680:B 87 6 e1525:=viaPerm pt3 pti3 b1546 (by decide +kernel) (by decide +kernel)
theorem b1681:B 87 6 e1526:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1682:B 87 6 e1527:=viaPerm pt3 pti3 b1653 (by decide +kernel) (by decide +kernel)
theorem b1683:B 87 6 e1528:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1684:B 87 6 e1529:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1685:B 87 6 e1530:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1686:B 87 6 e1531:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1687:B 87 6 e1532:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1688:B 87 6 e1533:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1689:B 87 6 e1534:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1690:B 87 6 e1535:=viaCut pjt_27 w1660 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1691:B 20 4 e1536:=viaSmall (by decide +kernel) (by decide)
theorem w1692:W 20 4 e1536:=viaSub (ws:=[e12,e1536]) (consBan b1643 (consBan b1691 (nilBan _ _))) (by decide) (by decide +kernel)
theorem b1693:B 87 6 e1537:=viaCut pjt_11 w1692 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1694:B 87 6 e1538:=viaCut pjt_18 w525 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1695:B 87 6 e1539:=viaCut pjt_27 w1660 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1696:B 87 6 e1540:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1697:B 87 6 e1541:=viaPerm pt1 pti1 b299 (by decide +kernel) (by decide +kernel)
theorem b1698:B 87 6 e1542:=viaPerm pt1 pti1 b512 (by decide +kernel) (by decide +kernel)
theorem b1699:B 87 6 e1543:=viaPerm pt1 pti1 b671 (by decide +kernel) (by decide +kernel)
theorem b1700:B 87 6 e1544:=viaPerm pt1 pti1 b787 (by decide +kernel) (by decide +kernel)
theorem b1701:B 87 6 e1545:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1702:B 87 6 e1546:=viaPerm pt1 pti1 b887 (by decide +kernel) (by decide +kernel)
theorem b1703:B 87 6 e1547:=viaPerm pt1 pti1 b961 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b1704:B 87 7 e1178:=viaBranch (ws:=[e1465,e541,e543,e646,e1466,e841,e1467,e1468,e1469,e1086,e1470,e1471,e1177,e1360,e1179,e1472,e1473,e1474,e1475,e1476,e1477,e1478,e1479,e1480,e1481,e1482,e1483,e1484,e1485,e1486,e1487,e1488,e1489,e1491,e1494,e1495,e1496,e1497,e1498,e1499,e1500,e1501,e1502,e1503,e1504,e1505,e1506,e1507,e1508,e1509,e1510,e1511,e1512,e1513,e1514,e1515,e1516,e1517,e1518,e1519,e1520,e1521,e1522,e1523,e1524,e1525,e1526,e1527,e1528,e1529,e1530,e1531,e1532,e1533,e1534,e1535,e1537,e1538,e1539,e1540,e1541,e1542,e1543,e1544,e1545,e1546,e1547]) (consBan b1614 (consBan b607 (consBan b609 (consBan b716 (consBan b1615 (consBan b933 (consBan b1616 (consBan b1617 (consBan b1618 (consBan b1199 (consBan b1619 (consBan b1620 (consBan b1293 (consBan b1621 (consBan b1295 (consBan b1622 (consBan b1623 (consBan b1624 (consBan b1625 (consBan b1626 (consBan b1627 (consBan b1628 (consBan b1629 (consBan b1630 (consBan b1631 (consBan b1632 (consBan b1633 (consBan b1634 (consBan b1635 (consBan b1636 (consBan b1637 (consBan b1638 (consBan b1639 (consBan b1642 (consBan b1647 (consBan b1648 (consBan b1649 (consBan b1650 (consBan b1651 (consBan b1652 (consBan b1653 (consBan b1654 (consBan b1655 (consBan b1656 (consBan b1657 (consBan b1658 (consBan b1661 (consBan b1662 (consBan b1663 (consBan b1664 (consBan b1665 (consBan b1666 (consBan b1667 (consBan b1668 (consBan b1669 (consBan b1670 (consBan b1671 (consBan b1672 (consBan b1673 (consBan b1674 (consBan b1675 (consBan b1676 (consBan b1677 (consBan b1678 (consBan b1679 (consBan b1680 (consBan b1681 (consBan b1682 (consBan b1683 (consBan b1684 (consBan b1685 (consBan b1686 (consBan b1687 (consBan b1688 (consBan b1689 (consBan b1690 (consBan b1693 (consBan b1694 (consBan b1695 (consBan b1696 (consBan b1697 (consBan b1698 (consBan b1699 (consBan b1700 (consBan b1701 (consBan b1702 (consBan b1703 (nilBan _ _)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b1705:B 87 6 e1548:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1706:B 87 6 e1549:=viaPerm pt4 pti4 b984 (by decide +kernel) (by decide +kernel)
theorem b1707:B 87 6 e1550:=viaPerm pt4 pti4 b1217 (by decide +kernel) (by decide +kernel)
theorem b1708:B 87 6 e1447:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1709:B 87 6 e1551:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1710:B 87 6 e1552:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1711:B 87 6 e1553:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1712:B 87 6 e1554:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1713:B 87 6 e1555:=viaPerm pt2 pti2 b1140 (by decide +kernel) (by decide +kernel)
theorem b1714:B 87 6 e1556:=viaPerm pt0 pti0 b1214 (by decide +kernel) (by decide +kernel)
theorem b1715:B 87 6 e1557:=viaPerm pt2 pti2 b1254 (by decide +kernel) (by decide +kernel)
theorem b1716:B 87 6 e1558:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1717:B 87 6 e1559:=viaPerm pt0 pti0 b1435 (by decide +kernel) (by decide +kernel)
theorem b1718:B 16 3 e1560:=viaSmall (by decide +kernel) (by decide)
theorem w1719:W 16 3 e1560:=widen (by decide +kernel) b1718
theorem b1720:B 87 6 e1561:=viaCut pjt_17 w1719 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1721:B 87 6 e1562:=viaPerm pt0 pti0 b1633 (by decide +kernel) (by decide +kernel)
theorem b1722:B 87 6 e1563:=viaPerm pt4 pti4 b1440 (by decide +kernel) (by decide +kernel)
theorem b1723:B 87 6 e1564:=viaPerm pt4 pti4 b1638 (by decide +kernel) (by decide +kernel)
theorem b1724:B 20 4 e1565:=viaSmall (by decide +kernel) (by decide)
theorem w1725:W 20 4 e1565:=viaSub (ws:=[e580,e1492,e1565]) (consBan b647 (consBan b1644 (consBan b1724 (nilBan _ _)))) (by decide) (by decide +kernel)
theorem b1726:B 87 6 e1566:=viaCut pjt_11 w1725 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1727:B 87 6 e1567:=viaPerm pt3 pti3 b924 (by decide +kernel) (by decide +kernel)
theorem b1728:B 20 4 e1568:=viaSmall (by decide +kernel) (by decide)
theorem w1729:W 20 4 e1568:=viaSub (ws:=[e12,e899,e1568]) (consBan b1643 (consBan b994 (consBan b1728 (nilBan _ _)))) (by decide) (by decide +kernel)
theorem b1730:B 87 6 e1569:=viaCut pjt_11 w1729 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1731:B 87 6 e1570:=viaCut pjt_18 w475 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1732:B 87 6 e1571:=viaPerm pt2 pti2 b1478 (by decide +kernel) (by decide +kernel)
theorem b1733:B 87 6 e1572:=viaPerm pt2 pti2 b1683 (by decide +kernel) (by decide +kernel)
theorem b1734:B 87 6 e1573:=viaPerm pt3 pti3 b904 (by decide +kernel) (by decide +kernel)
theorem b1735:B 87 6 e1574:=viaCut pjt_0 w1557 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1736:B 87 6 e1575:=viaCut pjt_0 w1557 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1737:B 87 6 e1576:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1738:B 87 6 e1577:=viaPerm pt3 pti3 b55 (by decide +kernel) (by decide +kernel)
theorem b1739:B 87 6 e1578:=viaPerm pt3 pti3 b756 (by decide +kernel) (by decide +kernel)
theorem b1740:B 87 6 e1579:=viaPerm pt3 pti3 b624 (by decide +kernel) (by decide +kernel)
theorem b1741:B 87 6 e1580:=viaPerm pt3 pti3 b919 (by decide +kernel) (by decide +kernel)
theorem b1742:B 87 6 e1581:=viaPerm pt3 pti3 b100 (by decide +kernel) (by decide +kernel)
theorem b1743:B 87 6 e1582:=viaPerm pt3 pti3 b635 (by decide +kernel) (by decide +kernel)
theorem b1744:B 87 6 e1583:=viaPerm pt3 pti3 b947 (by decide +kernel) (by decide +kernel)
theorem b1745:B 87 6 e1584:=viaPerm pt3 pti3 b1004 (by decide +kernel) (by decide +kernel)
theorem b1746:B 87 6 e1585:=viaPerm pt1 pti1 b1163 (by decide +kernel) (by decide +kernel)
theorem b1747:B 87 6 e1586:=viaPerm pt3 pti3 b1229 (by decide +kernel) (by decide +kernel)
theorem b1748:B 87 6 e1587:=viaPerm pt1 pti1 b1259 (by decide +kernel) (by decide +kernel)
theorem b1749:B 87 6 e1588:=viaPerm pt3 pti3 b1453 (by decide +kernel) (by decide +kernel)
theorem b1750:B 87 6 e1589:=viaPerm pt3 pti3 b1654 (by decide +kernel) (by decide +kernel)
theorem b1751:B 87 6 e1162:=viaPerm pt3 pti3 b917 (by decide +kernel) (by decide +kernel)
theorem b1752:B 87 6 e1590:=viaPerm pt1 pti1 b1751 (by decide +kernel) (by decide +kernel)
theorem b1753:B 87 6 e1591:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1754:B 87 6 e1592:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1755:B 87 6 e1593:=viaPerm pt1 pti1 b1570 (by decide +kernel) (by decide +kernel)
theorem b1756:B 87 6 e1594:=viaPerm pt1 pti1 b910 (by decide +kernel) (by decide +kernel)
theorem b1757:B 20 4 e1595:=viaSmall (by decide +kernel) (by decide)
theorem w1758:W 20 4 e1595:=viaSub (ws:=[e580,e1595]) (consBan b647 (consBan b1757 (nilBan _ _))) (by decide) (by decide +kernel)
theorem b1759:B 87 6 e1596:=viaCut pjt_11 w1758 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1760:B 87 6 e1597:=viaPerm pt0 pti0 b1588 (by decide +kernel) (by decide +kernel)
theorem b1761:B 87 6 e1598:=viaPerm pt1 pti1 b1727 (by decide +kernel) (by decide +kernel)
theorem b1762:B 87 6 e1599:=viaPerm pt1 pti1 b1573 (by decide +kernel) (by decide +kernel)
theorem b1763:B 87 6 e1600:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1764:B 87 6 e1601:=viaCut pjt_7 w795 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1765:B 87 6 e1602:=viaCut pjt_18 w525 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1766:B 87 6 e1603:=viaPerm pt1 pti1 b300 (by decide +kernel) (by decide +kernel)
theorem b1767:B 87 6 e1604:=viaPerm pt1 pti1 b513 (by decide +kernel) (by decide +kernel)
theorem b1768:B 87 6 e1605:=viaPerm pt1 pti1 b788 (by decide +kernel) (by decide +kernel)
theorem b1769:B 87 6 e1606:=viaPerm pt1 pti1 b888 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b1770:B 87 7 e1370:=viaBranch (ws:=[e542,e399,e647,e761,e1548,e1549,e1087,e1550,e1369,e1447,e1551,e1177,e1179,e1552,e1553,e1554,e1555,e1556,e1557,e1558,e1559,e1561,e1562,e1563,e1564,e819,e1566,e1567,e584,e1491,e1569,e1495,e1570,e1571,e1572,e1573,e1574,e1575,e1576,e1577,e1578,e1579,e1580,e1507,e1581,e1582,e1511,e1512,e1583,e1584,e1585,e1586,e1587,e1588,e1589,e1162,e1590,e1591,e1592,e1593,e1594,e1596,e1597,e1598,e1529,e1599,e1600,e1534,e1535,e1601,e1602,e1539,e1603,e1604,e1605,e1606]) (consBan b608 (consBan b444 (consBan b717 (consBan b849 (consBan b1705 (consBan b1706 (consBan b1200 (consBan b1707 (consBan b1511 (consBan b1708 (consBan b1709 (consBan b1293 (consBan b1295 (consBan b1710 (consBan b1711 (consBan b1712 (consBan b1713 (consBan b1714 (consBan b1715 (consBan b1716 (consBan b1717 (consBan b1720 (consBan b1721 (consBan b1722 (consBan b1723 (consBan b910 (consBan b1726 (consBan b1727 (consBan b651 (consBan b1642 (consBan b1730 (consBan b1648 (consBan b1731 (consBan b1732 (consBan b1733 (consBan b1734 (consBan b1735 (consBan b1736 (consBan b1737 (consBan b1738 (consBan b1739 (consBan b1740 (consBan b1741 (consBan b1662 (consBan b1742 (consBan b1743 (consBan b1666 (consBan b1667 (consBan b1744 (consBan b1745 (consBan b1746 (consBan b1747 (consBan b1748 (consBan b1749 (consBan b1750 (consBan b1751 (consBan b1752 (consBan b1753 (consBan b1754 (consBan b1755 (consBan b1756 (consBan b1759 (consBan b1760 (consBan b1761 (consBan b1684 (consBan b1762 (consBan b1763 (consBan b1689 (consBan b1690 (consBan b1764 (consBan b1765 (consBan b1695 (consBan b1766 (consBan b1767 (consBan b1768 (consBan b1769 (nilBan _ _))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b1771:B 87 7 e1607:=viaPerm pt0 pti0 b967 (by decide +kernel) (by decide +kernel)
theorem b1772:B 87 7 e1608:=viaPerm pt0 pti0 b1179 (by decide +kernel) (by decide +kernel)
theorem b1773:B 87 7 e1609:=viaPerm pt0 pti0 b1180 (by decide +kernel) (by decide +kernel)
theorem b1774:B 87 7 e1610:=viaPerm pt0 pti0 b1181 (by decide +kernel) (by decide +kernel)
theorem b1775:B 87 7 e1611:=viaPerm pt0 pti0 b1273 (by decide +kernel) (by decide +kernel)
theorem b1776:B 87 7 e1612:=viaPerm pt0 pti0 b1274 (by decide +kernel) (by decide +kernel)
theorem b1777:B 87 7 e1613:=viaPerm pt0 pti0 b1275 (by decide +kernel) (by decide +kernel)
theorem b1778:B 87 7 e1614:=viaPerm pt0 pti0 b1276 (by decide +kernel) (by decide +kernel)
theorem b1779:B 87 7 e1615:=viaPerm pt0 pti0 b1277 (by decide +kernel) (by decide +kernel)
theorem b1780:B 87 7 e1616:=viaPerm pt0 pti0 b1499 (by decide +kernel) (by decide +kernel)
theorem b1781:B 87 7 e1617:=viaPerm pt0 pti0 b1593 (by decide +kernel) (by decide +kernel)
theorem b1782:B 87 7 e1618:=viaPerm pt0 pti0 b1594 (by decide +kernel) (by decide +kernel)
theorem b1783:B 87 7 e1619:=viaPerm pt0 pti0 b1704 (by decide +kernel) (by decide +kernel)
theorem b1784:B 87 7 e1620:=viaPerm pt0 pti0 b1770 (by decide +kernel) (by decide +kernel)
theorem b1785:B 87 7 e815:=viaPerm pt3 pti3 b1779 (by decide +kernel) (by decide +kernel)
theorem b1786:B 87 7 e1621:=viaPerm pt3 pti3 b1780 (by decide +kernel) (by decide +kernel)
theorem b1787:B 87 7 e1622:=viaPerm pt3 pti3 b1781 (by decide +kernel) (by decide +kernel)
theorem b1788:B 87 7 e1623:=viaPerm pt3 pti3 b1783 (by decide +kernel) (by decide +kernel)
theorem b1789:B 87 7 e1624:=viaPerm pt3 pti3 b1784 (by decide +kernel) (by decide +kernel)
theorem b1790:B 87 7 e818:=viaPerm pt3 pti3 b1782 (by decide +kernel) (by decide +kernel)
theorem b1847:B 20 4 e1679:=viaSmall (by decide +kernel) (by decide)
theorem w1848:W 20 4 e1679:=widen (by decide +kernel) b1847
theorem b1849:B 87 6 e1680:=viaCut pjt_11 w1848 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1850:B 87 6 e1681:=viaCut pjt_9 w466 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1851:B 87 6 e1682:=viaCut pjt_15 w584 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1852:B 20 4 e1683:=viaSmall (by decide +kernel) (by decide)
theorem w1853:W 20 4 e1683:=widen (by decide +kernel) b1852
theorem b1854:B 87 6 e1684:=viaCut pjt_11 w1853 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1855:B 87 6 e1685:=viaPerm pt4 pti4 b1849 (by decide +kernel) (by decide +kernel)
theorem b1856:B 87 6 e1686:=viaPerm pt4 pti4 b1850 (by decide +kernel) (by decide +kernel)
theorem b1857:B 87 6 e1687:=viaPerm pt4 pti4 b1851 (by decide +kernel) (by decide +kernel)
theorem b1858:B 87 6 e1688:=viaPerm pt4 pti4 b1854 (by decide +kernel) (by decide +kernel)
theorem b1873:B 87 5 e1703:=viaCut pjt_13 w64 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1874:B 87 5 e1704:=viaCut pjt_9 w466 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1875:B 87 5 e1705:=viaCut pjt_13 w739 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1876:B 87 5 e1706:=viaCut pjt_15 w584 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1877:B 87 5 e1707:=viaCut pjt_13 w992 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1878:B 87 5 e1708:=viaPerm pt4 pti4 b1877 (by decide +kernel) (by decide +kernel)
theorem b1879:B 87 5 e1709:=viaCut pjt_13 w1220 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1880:B 87 5 e1710:=viaPerm pt4 pti4 b1879 (by decide +kernel) (by decide +kernel)
theorem b1881:B 87 5 e1711:=viaCut pjt_32 w1328 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1882:B 87 5 e1712:=viaCut pjt_32 w1641 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1883:B 35 4 e1713:=viaSmall (by decide +kernel) (by decide)
theorem w1884:W 35 4 e1713:=widen (by decide +kernel) b1883
theorem b1885:B 87 5 e1714:=viaCut pjt_2 w1884 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1886:B 16 3 e1715:=viaSmall (by decide +kernel) (by decide)
theorem w1887:W 16 3 e1715:=widen (by decide +kernel) b1886
theorem b1888:B 87 5 e1716:=viaCut pjt_15 w1887 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1889:B 16 3 e1717:=viaSmall (by decide +kernel) (by decide)
theorem w1890:W 16 3 e1717:=widen (by decide +kernel) b1889
theorem b1891:B 87 5 e1718:=viaCut pjt_17 w1890 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1892:B 16 3 e1719:=viaSmall (by decide +kernel) (by decide)
theorem w1893:W 16 3 e1719:=widen (by decide +kernel) b1892
theorem b1894:B 87 5 e1720:=viaCut pjt_15 w1893 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1895:B 87 5 e1721:=viaCut pjt_28 w1377 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1896:B 6 2 e1490:=viaSmall (by decide +kernel) (by decide)
theorem w1897:W 6 2 e1490:=viaSub (ws:=[e62,e1490]) (consBan b645 (consBan b1896 (nilBan _ _))) (by decide) (by decide +kernel)
theorem b1898:B 87 5 e1722:=viaCut pjt_26 w1897 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1899:B 87 5 e1723:=viaPerm pt4 pti4 b1881 (by decide +kernel) (by decide +kernel)
theorem b1900:B 87 5 e1724:=viaPerm pt4 pti4 b1882 (by decide +kernel) (by decide +kernel)
theorem b1901:B 20 4 e1725:=viaSmall (by decide +kernel) (by decide)
theorem w1902:W 20 4 e1725:=widen (by decide +kernel) b1901
theorem b1903:B 87 5 e1726:=viaCut pjt_11 w1902 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1904:B 87 5 e1727:=viaPerm pt4 pti4 b1903 (by decide +kernel) (by decide +kernel)
theorem b1905:B 87 5 e1728:=viaCut pjt_11 w1853 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1906:B 87 5 e1729:=viaPerm pt4 pti4 b1905 (by decide +kernel) (by decide +kernel)
theorem b1907:B 87 5 e1730:=viaPerm pt2 pti2 b1414 (by decide +kernel) (by decide +kernel)
theorem b1908:B 87 5 e1731:=viaCut pjt_11 w1853 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1909:B 6 1 e62:=viaSmall (by decide +kernel) (by decide)
theorem w1910:W 6 1 e62:=widen (by decide +kernel) b1909
theorem b1911:B 87 5 e1732:=viaCut pjt_25 w1910 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1912:B 87 5 e1733:=viaCut pjt_25 w1910 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1913:B 87 5 e1734:=viaPerm pt4 pti4 b1873 (by decide +kernel) (by decide +kernel)
theorem b1914:B 87 5 e1735:=viaPerm pt4 pti4 b1874 (by decide +kernel) (by decide +kernel)
theorem b1915:B 87 5 e1736:=viaPerm pt4 pti4 b1875 (by decide +kernel) (by decide +kernel)
theorem b1916:B 87 5 e1737:=viaPerm pt4 pti4 b1876 (by decide +kernel) (by decide +kernel)
theorem b1917:B 87 5 e1738:=viaPerm pt4 pti4 b1885 (by decide +kernel) (by decide +kernel)
theorem b1918:B 87 5 e1739:=viaPerm pt4 pti4 b1888 (by decide +kernel) (by decide +kernel)
theorem b1919:B 87 5 e1740:=viaPerm pt4 pti4 b1891 (by decide +kernel) (by decide +kernel)
theorem b1920:B 87 5 e1741:=viaPerm pt4 pti4 b1894 (by decide +kernel) (by decide +kernel)
theorem b1921:B 87 5 e1742:=viaPerm pt4 pti4 b1895 (by decide +kernel) (by decide +kernel)
theorem b1922:B 87 5 e1743:=viaPerm pt4 pti4 b1898 (by decide +kernel) (by decide +kernel)
theorem b1923:B 87 5 e1744:=viaPerm pt1 pti1 b1414 (by decide +kernel) (by decide +kernel)
theorem b1924:B 87 5 e1745:=viaPerm pt4 pti4 b1908 (by decide +kernel) (by decide +kernel)
theorem b1925:B 87 5 e1746:=viaPerm pt4 pti4 b1911 (by decide +kernel) (by decide +kernel)
theorem b1926:B 87 5 e1747:=viaPerm pt4 pti4 b1912 (by decide +kernel) (by decide +kernel)
theorem b1927:B 16 3 e1748:=viaPerm pc9_0 pci9_0 b1073 (by decide +kernel) (by decide +kernel)
theorem w1928:W 16 3 e1748:=widen (by decide +kernel) b1927
theorem b1929:B 87 5 e1749:=viaCut pjt_9 w1928 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1930:B 35 4 e1750:=viaSmall (by decide +kernel) (by decide)
theorem w1931:W 35 4 e1750:=widen (by decide +kernel) b1930
theorem b1932:B 87 5 e1751:=viaCut pjt_2 w1931 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1933:B 16 3 e1752:=viaSmall (by decide +kernel) (by decide)
theorem w1934:W 16 3 e1752:=widen (by decide +kernel) b1933
theorem b1935:B 87 5 e1753:=viaCut pjt_9 w1934 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1936:B 35 4 e1754:=viaSmall (by decide +kernel) (by decide)
theorem w1937:W 35 4 e1754:=widen (by decide +kernel) b1936
theorem b1938:B 87 5 e1755:=viaCut pjt_2 w1937 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b1939:B 87 6 e1756:=viaBranch (ws:=[e1703,e1704,e1705,e1706,e1707,e1708,e1709,e1710,e1711,e1712,e1714,e1716,e1718,e1720,e1721,e1722,e1723,e1724,e1726,e1727,e1728,e1729,e1730,e1731,e1732,e1733,e1734,e1735,e1736,e1737,e1738,e1739,e1740,e1741,e1742,e1743,e1744,e1745,e1746,e1747,e1749,e1751,e1753,e1755]) (consBan b1873 (consBan b1874 (consBan b1875 (consBan b1876 (consBan b1877 (consBan b1878 (consBan b1879 (consBan b1880 (consBan b1881 (consBan b1882 (consBan b1885 (consBan b1888 (consBan b1891 (consBan b1894 (consBan b1895 (consBan b1898 (consBan b1899 (consBan b1900 (consBan b1903 (consBan b1904 (consBan b1905 (consBan b1906 (consBan b1907 (consBan b1908 (consBan b1911 (consBan b1912 (consBan b1913 (consBan b1914 (consBan b1915 (consBan b1916 (consBan b1917 (consBan b1918 (consBan b1919 (consBan b1920 (consBan b1921 (consBan b1922 (consBan b1923 (consBan b1924 (consBan b1925 (consBan b1926 (consBan b1929 (consBan b1932 (consBan b1935 (consBan b1938 (nilBan _ _))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b1940:B 87 6 e1757:=viaCut pjt_12 w95 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1941:B 87 6 e1758:=viaCut pjt_12 w95 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b1959:B 35 5 e1776:=viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b1960:B 35 5 e1777:=viaSmall (by decide +kernel) (by decide)
theorem w1961:W 35 5 e1777:=viaSub (ws:=[e1776,e1777]) (consBan b1959 (consBan b1960 (nilBan _ _))) (by decide) (by decide +kernel)
theorem b1962:B 87 6 e1778:=viaCut pjt_1 w1961 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b1963:B 35 5 e1779:=viaSmall (by decide +kernel) (by decide)
theorem b1964:B 35 5 e1780:=viaSmall (by decide +kernel) (by decide)
theorem w1965:W 35 5 e1780:=viaSub (ws:=[e1776,e1779,e1777,e1780]) (consBan b1959 (consBan b1963 (consBan b1960 (consBan b1964 (nilBan _ _))))) (by decide) (by decide +kernel)
theorem b1966:B 87 6 e1781:=viaCut pjt_1 w1965 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1967:B 87 6 e1782:=viaCut pjt_15 w584 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1968:B 87 6 e1783:=viaPerm pt4 pti4 b993 (by decide +kernel) (by decide +kernel)
theorem b1969:B 87 6 e1784:=viaPerm pt4 pti4 b1221 (by decide +kernel) (by decide +kernel)
theorem b1970:B 87 6 e1785:=viaPerm pt0 pti0 b1009 (by decide +kernel) (by decide +kernel)
theorem b1971:B 87 6 e1786:=viaPerm pt2 pti2 b1165 (by decide +kernel) (by decide +kernel)
theorem b1972:B 87 6 e1787:=viaPerm pt0 pti0 b1231 (by decide +kernel) (by decide +kernel)
theorem b1973:B 87 6 e1788:=viaPerm pt2 pti2 b1261 (by decide +kernel) (by decide +kernel)
theorem b1974:B 87 6 e1789:=viaPerm pt0 pti0 b1455 (by decide +kernel) (by decide +kernel)
theorem b1975:B 87 6 e1790:=viaPerm pt0 pti0 b1656 (by decide +kernel) (by decide +kernel)
theorem b1976:B 87 6 e1791:=viaPerm pt4 pti4 b1537 (by decide +kernel) (by decide +kernel)
theorem b1977:B 87 6 e1792:=viaPerm pt4 pti4 b1642 (by decide +kernel) (by decide +kernel)
theorem b1978:B 87 6 e1793:=viaCut pjt_11 w1902 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1979:B 87 6 e1794:=viaPerm pt4 pti4 b1978 (by decide +kernel) (by decide +kernel)
theorem b1980:B 87 6 e1795:=viaPerm pt2 pti2 b1575 (by decide +kernel) (by decide +kernel)
theorem b1981:B 87 6 e1796:=viaPerm pt2 pti2 b1690 (by decide +kernel) (by decide +kernel)
theorem b1982:B 87 6 e1797:=viaCut pjt_25 w1910 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1983:B 87 6 e1798:=viaCut pjt_25 w1910 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1984:B 87 6 e1799:=viaPerm pt3 pti3 b102 (by decide +kernel) (by decide +kernel)
theorem b1985:B 87 6 e1800:=viaPerm pt3 pti3 b637 (by decide +kernel) (by decide +kernel)
theorem b1986:B 87 6 e1801:=viaPerm pt3 pti3 b758 (by decide +kernel) (by decide +kernel)
theorem b1987:B 87 6 e1802:=viaPerm pt3 pti3 b834 (by decide +kernel) (by decide +kernel)
theorem b1988:B 87 6 e1803:=viaPerm pt3 pti3 b1009 (by decide +kernel) (by decide +kernel)
theorem b1989:B 87 6 e1804:=viaPerm pt1 pti1 b1165 (by decide +kernel) (by decide +kernel)
theorem b1990:B 87 6 e1805:=viaPerm pt3 pti3 b1231 (by decide +kernel) (by decide +kernel)
theorem b1991:B 87 6 e1806:=viaPerm pt1 pti1 b1261 (by decide +kernel) (by decide +kernel)
theorem b1992:B 87 6 e1807:=viaPerm pt3 pti3 b1455 (by decide +kernel) (by decide +kernel)
theorem b1993:B 87 6 e1808:=viaPerm pt3 pti3 b1656 (by decide +kernel) (by decide +kernel)
theorem b1994:B 87 6 e1809:=viaPerm pt1 pti1 b1575 (by decide +kernel) (by decide +kernel)
theorem b1995:B 87 6 e1810:=viaPerm pt1 pti1 b1690 (by decide +kernel) (by decide +kernel)
theorem b1996:B 87 6 e1811:=viaPerm pt3 pti3 b1982 (by decide +kernel) (by decide +kernel)
theorem b1997:B 87 6 e1812:=viaPerm pt4 pti4 b1983 (by decide +kernel) (by decide +kernel)
theorem b1998:B 87 6 e1813:=viaPerm pt1 pti1 b302 (by decide +kernel) (by decide +kernel)
theorem b1999:B 87 6 e1814:=viaPerm pt1 pti1 b519 (by decide +kernel) (by decide +kernel)
theorem b2000:B 87 6 e1815:=viaPerm pt1 pti1 b792 (by decide +kernel) (by decide +kernel)
theorem b2001:B 87 6 e1816:=viaPerm pt1 pti1 b890 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b2002:B 87 7 e819:=viaBranch (ws:=[e1680,e1681,e1682,e1567,e1684,e1685,e1686,e1687,e824,e1688,e1756,e1757,e1758,e1778,e1781,e1782,e60,e563,e669,e734,e898,e1783,e1107,e1784,e1394,e1491,e1785,e1786,e1787,e1788,e1789,e1790,e1791,e1792,e1793,e1794,e1795,e1796,e1797,e1798,e1799,e1800,e1801,e1802,e1803,e1804,e1805,e1806,e1807,e1808,e1809,e1810,e1811,e1812,e1813,e1814,e1815,e1816]) (consBan b1849 (consBan b1850 (consBan b1851 (consBan b1727 (consBan b1854 (consBan b1855 (consBan b1856 (consBan b1857 (consBan b916 (consBan b1858 (consBan b1939 (consBan b1940 (consBan b1941 (consBan b1962 (consBan b1966 (consBan b1967 (consBan b65 (consBan b629 (consBan b740 (consBan b820 (consBan b993 (consBan b1968 (consBan b1221 (consBan b1969 (consBan b1537 (consBan b1642 (consBan b1970 (consBan b1971 (consBan b1972 (consBan b1973 (consBan b1974 (consBan b1975 (consBan b1976 (consBan b1977 (consBan b1978 (consBan b1979 (consBan b1980 (consBan b1981 (consBan b1982 (consBan b1983 (consBan b1984 (consBan b1985 (consBan b1986 (consBan b1987 (consBan b1988 (consBan b1989 (consBan b1990 (consBan b1991 (consBan b1992 (consBan b1993 (consBan b1994 (consBan b1995 (consBan b1996 (consBan b1997 (consBan b1998 (consBan b1999 (consBan b2000 (consBan b2001 (nilBan _ _))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b2003:B 87 6 e1817:=viaPerm pt4 pti4 b997 (by decide +kernel) (by decide +kernel)
theorem b2004:B 87 6 e1818:=viaPerm pt4 pti4 b1222 (by decide +kernel) (by decide +kernel)
theorem b2005:B 87 6 e1819:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2006:B 87 6 e1820:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2008:B 87 6 e1822:=viaCut pjt_6 w470 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2009:B 87 6 e1823:=viaPerm pt0 pti0 b1013 (by decide +kernel) (by decide +kernel)
theorem b2010:B 87 6 e1824:=viaPerm pt2 pti2 b1166 (by decide +kernel) (by decide +kernel)
theorem b2011:B 87 6 e1825:=viaPerm pt0 pti0 b1232 (by decide +kernel) (by decide +kernel)
theorem b2012:B 87 6 e1826:=viaPerm pt2 pti2 b1262 (by decide +kernel) (by decide +kernel)
theorem b2013:B 87 6 e1827:=viaPerm pt0 pti0 b1456 (by decide +kernel) (by decide +kernel)
theorem b2014:B 87 6 e1828:=viaPerm pt0 pti0 b1657 (by decide +kernel) (by decide +kernel)
theorem b2015:B 87 6 e1829:=viaPerm pt4 pti4 b1540 (by decide +kernel) (by decide +kernel)
theorem b2016:B 87 6 e1830:=viaPerm pt4 pti4 b1730 (by decide +kernel) (by decide +kernel)
theorem b2017:B 87 6 e1831:=viaCut pjt_12 w95 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2018:B 87 6 e1832:=viaPerm pt4 pti4 b2017 (by decide +kernel) (by decide +kernel)
theorem b2019:B 87 6 e1833:=viaPerm pt2 pti2 b1576 (by decide +kernel) (by decide +kernel)
theorem b2020:B 87 6 e1834:=viaPerm pt2 pti2 b1764 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b2036:B 35 5 e1842:=viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b2037:B 35 5 e1843:=viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b2038:B 35 5 e1844:=viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b2039:B 35 5 e1845:=viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b2040:B 35 5 e1846:=viaSmall (by decide +kernel) (by decide)
theorem w2041:W 35 5 e1846:=viaSub (ws:=[e1842,e1843,e491,e1844,e1845,e1846]) (consBan b2036 (consBan b2037 (consBan b548 (consBan b2038 (consBan b2039 (consBan b2040 (nilBan _ _))))))) (by decide) (by decide +kernel)
theorem b2042:B 87 6 e1847:=viaCut pjt_2 w2041 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2047:B 20 4 e1852:=viaSmall (by decide +kernel) (by decide)
theorem b2048:B 20 4 e1853:=viaSmall (by decide +kernel) (by decide)
theorem w2049:W 20 4 e1853:=viaSub (ws:=[e1852,e1853]) (consBan b2047 (consBan b2048 (nilBan _ _))) (by decide) (by decide +kernel)
theorem b2050:B 87 6 e1854:=viaCut pjt_11 w2049 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2051:B 87 6 e1855:=viaPerm pt3 pti3 b103 (by decide +kernel) (by decide +kernel)
theorem b2052:B 87 6 e1856:=viaPerm pt3 pti3 b104 (by decide +kernel) (by decide +kernel)
theorem b2053:B 87 6 e1857:=viaPerm pt3 pti3 b638 (by decide +kernel) (by decide +kernel)
theorem b2054:B 87 6 e1858:=viaPerm pt3 pti3 b759 (by decide +kernel) (by decide +kernel)
theorem b2055:B 87 6 e1859:=viaPerm pt3 pti3 b948 (by decide +kernel) (by decide +kernel)
theorem b2056:B 87 6 e1860:=viaPerm pt4 pti4 b2005 (by decide +kernel) (by decide +kernel)
theorem b2057:B 87 6 e1861:=viaPerm pt3 pti3 b657 (by decide +kernel) (by decide +kernel)
theorem b2058:B 87 6 e1862:=viaPerm pt4 pti4 b2006 (by decide +kernel) (by decide +kernel)
theorem b2059:B 87 6 e1863:=viaPerm pt4 pti4 b2008 (by decide +kernel) (by decide +kernel)
theorem b2060:B 87 6 e1864:=viaPerm pt3 pti3 b1013 (by decide +kernel) (by decide +kernel)
theorem b2061:B 87 6 e1865:=viaPerm pt1 pti1 b1166 (by decide +kernel) (by decide +kernel)
theorem b2062:B 87 6 e1866:=viaPerm pt3 pti3 b1232 (by decide +kernel) (by decide +kernel)
theorem b2063:B 87 6 e1867:=viaPerm pt1 pti1 b1262 (by decide +kernel) (by decide +kernel)
theorem b2064:B 87 6 e1868:=viaPerm pt3 pti3 b1456 (by decide +kernel) (by decide +kernel)
theorem b2065:B 87 6 e1869:=viaPerm pt3 pti3 b1657 (by decide +kernel) (by decide +kernel)
theorem b2066:B 87 6 e1870:=viaPerm pt1 pti1 b1576 (by decide +kernel) (by decide +kernel)
theorem b2067:B 87 6 e1871:=viaPerm pt1 pti1 b1764 (by decide +kernel) (by decide +kernel)
theorem b2068:B 87 6 e1872:=viaPerm pt3 pti3 b2042 (by decide +kernel) (by decide +kernel)
theorem b2069:B 87 6 e1873:=viaPerm pt4 pti4 b2050 (by decide +kernel) (by decide +kernel)
theorem b2070:B 87 6 e1874:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2071:B 87 6 e1875:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2072:B 16 4 e1876:=viaSmall (by decide +kernel) (by decide)
theorem w2073:W 16 4 e1876:=widen (by decide +kernel) b2072
theorem b2074:B 87 6 e1877:=viaCut pjt_9 w2073 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2075:B 87 6 e1878:=viaPerm pt1 pti1 b1586 (by decide +kernel) (by decide +kernel)
theorem b2076:B 16 4 e1879:=viaSmall (by decide +kernel) (by decide)
theorem w2077:W 16 4 e1879:=widen (by decide +kernel) b2076
theorem b2078:B 87 6 e1880:=viaCut pjt_9 w2077 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2079:B 16 4 e1881:=viaSmall (by decide +kernel) (by decide)
theorem b2080:B 87 6 e1882:=viaCut pjt_11 w996 (by decide) (by decide +kernel) (by decide +kernel)
theorem w2081:W 16 4 e1881:=widen (by decide +kernel) b2079
theorem b2082:B 87 6 e1883:=viaCut pjt_15 w2081 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2083:B 87 6 e1884:=viaCut pjt_18 w395 (by decide) (by decide +kernel) (by decide +kernel)
theorem w2084:W 6 2 e62:=widen (by decide +kernel) b68
theorem b2085:B 87 6 e1885:=viaCut pjt_28 w2084 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2086:B 87 6 e1886:=viaCut pjt_17 w1008 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2087:B 6 1 e62:=viaSmall (by decide +kernel) (by decide)
theorem w2088:W 6 1 e62:=widen (by decide +kernel) b2087
theorem b2089:B 87 6 e1887:=viaCut pjt_28 w2088 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2090:B 12 3 e1888:=viaSmall (by decide +kernel) (by decide)
theorem w2091:W 12 3 e1888:=viaSub (ws:=[e16,e1888]) (consBan b16 (consBan b2090 (nilBan _ _))) (by decide) (by decide +kernel)
theorem b2092:B 87 6 e1889:=viaCut pjt_18 w2091 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2093:B 87 6 e1890:=viaCut pjt_28 w2084 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2094:B 12 3 e1891:=viaSmall (by decide +kernel) (by decide)
theorem b2095:B 12 3 e1892:=viaSmall (by decide +kernel) (by decide)
theorem w2096:W 12 3 e1892:=viaSub (ws:=[e1891,e16,e1892]) (consBan b2094 (consBan b16 (consBan b2095 (nilBan _ _)))) (by decide) (by decide +kernel)
theorem b2097:B 87 6 e1893:=viaCut pjt_18 w2096 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2098:B 87 6 e1894:=viaCut pjt_28 w2088 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2099:B 87 6 e1895:=viaCut pjt_17 w1008 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2100:B 87 6 e1896:=viaPerm pt1 pti1 b345 (by decide +kernel) (by decide +kernel)
theorem b2101:B 87 6 e1897:=viaPerm pt1 pti1 b523 (by decide +kernel) (by decide +kernel)
theorem b2102:B 87 6 e1898:=viaPerm pt1 pti1 b796 (by decide +kernel) (by decide +kernel)
theorem b2103:B 87 6 e1899:=viaPerm pt1 pti1 b891 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b2104:B 87 7 e1900:=viaBranch (ws:=[e61,e75,e564,e674,e851,e901,e1817,e1108,e1818,e1396,e1569,e1819,e582,e1820,e1822,e1823,e1824,e1825,e1826,e1827,e1828,e1829,e1830,e1793,e1794,e1831,e1832,e824,e1833,e1834,e1847,e1854,e1855,e1856,e1857,e1858,e1859,e1860,e1861,e1862,e1863,e1864,e1865,e1866,e1867,e1868,e1869,e1567,e1870,e1871,e1872,e1873,e1874,e1875,e1877,e1878,e1880,e1882,e1883,e1884,e1885,e1886,e1887,e1889,e1890,e1893,e1894,e1895,e1896,e1897,e1898,e1899]) (consBan b67 (consBan b87 (consBan b630 (consBan b749 (consBan b944 (consBan b997 (consBan b2003 (consBan b1222 (consBan b2004 (consBan b1540 (consBan b1730 (consBan b2005 (consBan b649 (consBan b2006 (consBan b2008 (consBan b2009 (consBan b2010 (consBan b2011 (consBan b2012 (consBan b2013 (consBan b2014 (consBan b2015 (consBan b2016 (consBan b1978 (consBan b1979 (consBan b2017 (consBan b2018 (consBan b916 (consBan b2019 (consBan b2020 (consBan b2042 (consBan b2050 (consBan b2051 (consBan b2052 (consBan b2053 (consBan b2054 (consBan b2055 (consBan b2056 (consBan b2057 (consBan b2058 (consBan b2059 (consBan b2060 (consBan b2061 (consBan b2062 (consBan b2063 (consBan b2064 (consBan b2065 (consBan b1727 (consBan b2066 (consBan b2067 (consBan b2068 (consBan b2069 (consBan b2070 (consBan b2071 (consBan b2074 (consBan b2075 (consBan b2078 (consBan b2080 (consBan b2082 (consBan b2083 (consBan b2085 (consBan b2086 (consBan b2089 (consBan b2092 (consBan b2093 (consBan b2097 (consBan b2098 (consBan b2099 (consBan b2100 (consBan b2101 (consBan b2102 (consBan b2103 (nilBan _ _))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b2161:B 20 4 e1947:=viaPerm pc11_0 pci11_0 b1847 (by decide +kernel) (by decide +kernel)
theorem w2162:W 20 4 e1947:=widen (by decide +kernel) b2161
theorem b2163:B 87 6 e1948:=viaCut pjt_11 w2162 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2164:B 87 6 e1949:=viaCut pjt_12 w95 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2165:B 87 6 e1950:=viaCut pjt_18 w472 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2166:B 87 6 e1951:=viaPerm pt4 pti4 b999 (by decide +kernel) (by decide +kernel)
theorem b2167:B 87 6 e1952:=viaPerm pt4 pti4 b1224 (by decide +kernel) (by decide +kernel)
theorem b2168:B 87 6 e1953:=viaPerm pt0 pti0 b1016 (by decide +kernel) (by decide +kernel)
theorem b2169:B 87 6 e1954:=viaPerm pt2 pti2 b1167 (by decide +kernel) (by decide +kernel)
theorem b2170:B 87 6 e1955:=viaPerm pt0 pti0 b1233 (by decide +kernel) (by decide +kernel)
theorem b2171:B 87 6 e1956:=viaPerm pt2 pti2 b1263 (by decide +kernel) (by decide +kernel)
theorem b2172:B 87 6 e1957:=viaPerm pt0 pti0 b1457 (by decide +kernel) (by decide +kernel)
theorem b2173:B 87 6 e1958:=viaPerm pt0 pti0 b1658 (by decide +kernel) (by decide +kernel)
theorem b2174:B 87 6 e1959:=viaCut pjt_18 w472 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2175:B 87 6 e1960:=viaPerm pt3 pti3 b659 (by decide +kernel) (by decide +kernel)
theorem b2176:B 87 6 e1900:=viaCut pjt_11 w996 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2177:B 87 6 e1961:=viaCut pjt_18 w472 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2178:B 87 6 e1962:=viaPerm pt1 pti1 b1588 (by decide +kernel) (by decide +kernel)
theorem b2179:B 12 3 e1963:=viaSmall (by decide +kernel) (by decide)
theorem w2180:W 12 3 e1963:=viaSub (ws:=[e16,e1963]) (consBan b16 (consBan b2179 (nilBan _ _))) (by decide) (by decide +kernel)
theorem b2181:B 87 6 e1964:=viaCut pjt_18 w2180 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2182:B 87 6 e1965:=viaPerm pt1 pti1 b2099 (by decide +kernel) (by decide +kernel)
theorem b2183:B 87 6 e1966:=viaPerm pt4 pti4 b1542 (by decide +kernel) (by decide +kernel)
theorem b2184:B 87 6 e1967:=viaPerm pt4 pti4 b1731 (by decide +kernel) (by decide +kernel)
theorem b2185:B 12 3 e1968:=viaSmall (by decide +kernel) (by decide)
theorem w2186:W 12 3 e1968:=widen (by decide +kernel) b2185
theorem b2187:B 87 6 e1969:=viaCut pjt_18 w2186 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2188:B 87 6 e1970:=viaPerm pt4 pti4 b2187 (by decide +kernel) (by decide +kernel)
theorem b2189:B 87 6 e1971:=viaPerm pt2 pti2 b1577 (by decide +kernel) (by decide +kernel)
theorem b2190:B 87 6 e1972:=viaPerm pt2 pti2 b1765 (by decide +kernel) (by decide +kernel)
theorem b2191:B 87 6 e1973:=viaPerm pt0 pti0 b2050 (by decide +kernel) (by decide +kernel)
theorem b2192:B 12 3 e1974:=viaSmall (by decide +kernel) (by decide)
theorem w2193:W 12 3 e1974:=widen (by decide +kernel) b2192
theorem b2194:B 87 6 e1975:=viaCut pjt_18 w2193 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2195:B 87 6 e1976:=viaPerm pt3 pti3 b107 (by decide +kernel) (by decide +kernel)
theorem b2196:B 87 6 e1977:=viaPerm pt3 pti3 b640 (by decide +kernel) (by decide +kernel)
theorem b2197:B 87 6 e1978:=viaPerm pt3 pti3 b761 (by decide +kernel) (by decide +kernel)
theorem b2198:B 87 6 e1979:=viaPerm pt3 pti3 b837 (by decide +kernel) (by decide +kernel)
theorem b2199:B 87 6 e1980:=viaPerm pt3 pti3 b1019 (by decide +kernel) (by decide +kernel)
theorem b2200:B 87 6 e1981:=viaPerm pt1 pti1 b1170 (by decide +kernel) (by decide +kernel)
theorem b2201:B 87 6 e1982:=viaPerm pt3 pti3 b1234 (by decide +kernel) (by decide +kernel)
theorem b2202:B 87 6 e1983:=viaPerm pt1 pti1 b1264 (by decide +kernel) (by decide +kernel)
theorem b2203:B 87 6 e1984:=viaPerm pt3 pti3 b1458 (by decide +kernel) (by decide +kernel)
theorem b2204:B 87 6 e1985:=viaPerm pt3 pti3 b1661 (by decide +kernel) (by decide +kernel)
theorem b2205:B 87 6 e1986:=viaPerm pt1 pti1 b1578 (by decide +kernel) (by decide +kernel)
theorem b2206:B 87 6 e1987:=viaPerm pt1 pti1 b1695 (by decide +kernel) (by decide +kernel)
theorem b2207:B 87 6 e1988:=viaPerm pt1 pti1 b1997 (by decide +kernel) (by decide +kernel)
theorem b2208:B 6 1 e62:=viaSmall (by decide +kernel) (by decide)
theorem w2209:W 6 1 e62:=widen (by decide +kernel) b2208
theorem b2210:B 87 6 e1989:=viaCut pjt_32 w2209 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2211:B 87 6 e1990:=viaPerm pt1 pti1 b347 (by decide +kernel) (by decide +kernel)
theorem b2212:B 87 6 e1991:=viaPerm pt1 pti1 b527 (by decide +kernel) (by decide +kernel)
theorem b2213:B 87 6 e1992:=viaPerm pt1 pti1 b798 (by decide +kernel) (by decide +kernel)
theorem b2214:B 87 6 e1993:=viaPerm pt1 pti1 b893 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b2215:B 87 7 e1567:=viaBranch (ws:=[e17,e1948,e1949,e1950,e52,e675,e558,e823,e76,e80,e565,e852,e902,e1951,e1109,e1952,e1397,e1495,e1953,e1954,e1955,e1956,e1957,e1958,e819,e1684,e815,e1959,e1960,e818,e1900,e1831,e825,e1961,e1962,e828,e829,e1964,e1965,e832,e1966,e1967,e1969,e1970,e1971,e1972,e1973,e1975,e1976,e1977,e1978,e1979,e1980,e1981,e1982,e1983,e1984,e1985,e1986,e1987,e1988,e1989,e1990,e1991,e1992,e1993]) (consBan b904 (consBan b2163 (consBan b2164 (consBan b2165 (consBan b55 (consBan b750 (consBan b624 (consBan b915 (consBan b89 (consBan b96 (consBan b631 (consBan b945 (consBan b998 (consBan b2166 (consBan b1223 (consBan b2167 (consBan b1541 (consBan b1648 (consBan b2168 (consBan b2169 (consBan b2170 (consBan b2171 (consBan b2172 (consBan b2173 (consBan b910 (consBan b1854 (consBan b906 (consBan b2174 (consBan b2175 (consBan b909 (consBan b2176 (consBan b2017 (consBan b917 (consBan b2177 (consBan b2178 (consBan b920 (consBan b921 (consBan b2181 (consBan b2182 (consBan b924 (consBan b2183 (consBan b2184 (consBan b2187 (consBan b2188 (consBan b2189 (consBan b2190 (consBan b2191 (consBan b2194 (consBan b2195 (consBan b2196 (consBan b2197 (consBan b2198 (consBan b2199 (consBan b2200 (consBan b2201 (consBan b2202 (consBan b2203 (consBan b2204 (consBan b2205 (consBan b2206 (consBan b2207 (consBan b2210 (consBan b2211 (consBan b2212 (consBan b2213 (consBan b2214 (nilBan _ _))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b2216:B 87 7 e824:=viaPerm pt4 pti4 b2215 (by decide +kernel) (by decide +kernel)
theorem b2217:B 87 7 e825:=viaPerm pt0 pti0 b1785 (by decide +kernel) (by decide +kernel)
theorem b2218:B 87 7 e1994:=viaPerm pt0 pti0 b1786 (by decide +kernel) (by decide +kernel)
theorem b2219:B 87 7 e1995:=viaPerm pt0 pti0 b1787 (by decide +kernel) (by decide +kernel)
theorem b2220:B 87 7 e1996:=viaPerm pt0 pti0 b1788 (by decide +kernel) (by decide +kernel)
theorem b2221:B 87 7 e1997:=viaPerm pt0 pti0 b1789 (by decide +kernel) (by decide +kernel)
theorem b2222:B 87 7 e828:=viaPerm pt0 pti0 b1790 (by decide +kernel) (by decide +kernel)
theorem b2223:B 87 7 e829:=viaPerm pt0 pti0 b2002 (by decide +kernel) (by decide +kernel)
theorem b2224:B 87 7 e1998:=viaPerm pt0 pti0 b2104 (by decide +kernel) (by decide +kernel)
theorem b2225:B 87 7 e1999:=viaPerm pt0 pti0 b2215 (by decide +kernel) (by decide +kernel)
theorem b2226:B 87 7 e832:=viaPerm pt0 pti0 b2216 (by decide +kernel) (by decide +kernel)
theorem b2227:B 87 7 e1573:=viaPerm pt3 pti3 b18 (by decide +kernel) (by decide +kernel)
theorem b2228:B 87 7 e2000:=viaPerm pt3 pti3 b356 (by decide +kernel) (by decide +kernel)
theorem b2229:B 87 7 e2001:=viaPerm pt3 pti3 b536 (by decide +kernel) (by decide +kernel)
theorem b2230:B 87 7 e2002:=viaPerm pt3 pti3 b676 (by decide +kernel) (by decide +kernel)
theorem b2231:B 87 7 e1577:=viaPerm pt3 pti3 b807 (by decide +kernel) (by decide +kernel)
theorem b2232:B 87 7 e1579:=viaPerm pt3 pti3 b808 (by decide +kernel) (by decide +kernel)
theorem b2233:B 87 7 e2003:=viaPerm pt3 pti3 b902 (by decide +kernel) (by decide +kernel)
theorem b2234:B 87 7 e2004:=viaPerm pt3 pti3 b966 (by decide +kernel) (by decide +kernel)
theorem b2235:B 87 7 e2005:=viaPerm pt1 pti1 b967 (by decide +kernel) (by decide +kernel)
theorem b2236:B 87 7 e2006:=viaPerm pt1 pti1 b1180 (by decide +kernel) (by decide +kernel)
theorem b2237:B 87 7 e2007:=viaPerm pt0 pti0 b2236 (by decide +kernel) (by decide +kernel)
theorem b2238:B 87 7 e2008:=viaPerm pt1 pti1 b1181 (by decide +kernel) (by decide +kernel)
theorem b2239:B 87 7 e2009:=viaPerm pt1 pti1 b1275 (by decide +kernel) (by decide +kernel)
theorem b2240:B 87 7 e2010:=viaPerm pt1 pti1 b1276 (by decide +kernel) (by decide +kernel)
theorem b2241:B 87 7 e2011:=viaPerm pt0 pti0 b2239 (by decide +kernel) (by decide +kernel)
theorem b2242:B 87 7 e2012:=viaPerm pt0 pti0 b2240 (by decide +kernel) (by decide +kernel)
theorem b2243:B 87 7 e2013:=viaPerm pt1 pti1 b1785 (by decide +kernel) (by decide +kernel)
theorem b2244:B 87 7 e2014:=viaPerm pt1 pti1 b1786 (by decide +kernel) (by decide +kernel)
theorem b2245:B 87 7 e2015:=viaPerm pt1 pti1 b1787 (by decide +kernel) (by decide +kernel)
theorem b2246:B 87 7 e2016:=viaPerm pt1 pti1 b1790 (by decide +kernel) (by decide +kernel)
theorem b2247:B 87 7 e2017:=viaPerm pt1 pti1 b1788 (by decide +kernel) (by decide +kernel)
theorem b2248:B 87 7 e2018:=viaPerm pt1 pti1 b1789 (by decide +kernel) (by decide +kernel)
theorem b2249:B 87 7 e1590:=viaPerm pt0 pti0 b2243 (by decide +kernel) (by decide +kernel)
theorem b2250:B 87 7 e2019:=viaPerm pt0 pti0 b2244 (by decide +kernel) (by decide +kernel)
theorem b2251:B 87 7 e2020:=viaPerm pt0 pti0 b2245 (by decide +kernel) (by decide +kernel)
theorem b2252:B 87 7 e2021:=viaPerm pt0 pti0 b2247 (by decide +kernel) (by decide +kernel)
theorem b2253:B 87 7 e2022:=viaPerm pt0 pti0 b2248 (by decide +kernel) (by decide +kernel)
theorem b2254:B 87 7 e1593:=viaPerm pt0 pti0 b2246 (by decide +kernel) (by decide +kernel)
theorem b2255:B 87 7 e1594:=viaPerm pt1 pti1 b2002 (by decide +kernel) (by decide +kernel)
theorem b2256:B 87 7 e2023:=viaPerm pt1 pti1 b2104 (by decide +kernel) (by decide +kernel)
theorem b2257:B 87 7 e2024:=viaPerm pt1 pti1 b2216 (by decide +kernel) (by decide +kernel)
theorem b2258:B 87 7 e1598:=viaPerm pt0 pti0 b2257 (by decide +kernel) (by decide +kernel)
theorem b2259:B 87 7 e2025:=viaPerm pt0 pti0 b2227 (by decide +kernel) (by decide +kernel)
theorem b2260:B 87 7 e2026:=viaPerm pt0 pti0 b2228 (by decide +kernel) (by decide +kernel)
theorem b2261:B 87 7 e2027:=viaPerm pt0 pti0 b2229 (by decide +kernel) (by decide +kernel)
theorem b2262:B 87 7 e2028:=viaPerm pt0 pti0 b2230 (by decide +kernel) (by decide +kernel)
theorem b2263:B 87 7 e2029:=viaPerm pt0 pti0 b2231 (by decide +kernel) (by decide +kernel)
theorem b2264:B 87 7 e2030:=viaPerm pt0 pti0 b2232 (by decide +kernel) (by decide +kernel)
theorem b2265:B 87 7 e2031:=viaPerm pt0 pti0 b2233 (by decide +kernel) (by decide +kernel)
theorem b2266:B 87 7 e2032:=viaPerm pt0 pti0 b2234 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b2267:B 87 8 e2033:=viaBranch (ws:=[e17,e318,e355,e609,e52,e558,e356,e522,e873,e1067,e1068,e1069,e921,e1159,e1160,e1161,e1162,e1360,e1447,e1425,e1178,e1370,e1607,e1608,e1609,e1610,e1611,e1612,e1613,e1614,e1615,e1616,e1617,e1618,e1619,e1620,e815,e1621,e1622,e1623,e1624,e818,e819,e1900,e1567,e824,e825,e1994,e1995,e1996,e1997,e828,e829,e1998,e1999,e832,e1573,e2000,e2001,e2002,e1577,e1579,e2003,e2004,e2005,e2006,e2007,e2008,e2009,e2010,e2011,e2012,e2013,e2014,e2015,e2016,e2017,e2018,e1590,e2019,e2020,e2021,e2022,e1593,e1594,e2023,e2024,e1598,e2025,e2026,e2027,e2028,e2029,e2030,e2031,e2032]) (consBan b18 (consBan b356 (consBan b536 (consBan b676 (consBan b807 (consBan b808 (consBan b902 (consBan b966 (consBan b967 (consBan b1179 (consBan b1180 (consBan b1181 (consBan b1273 (consBan b1274 (consBan b1275 (consBan b1276 (consBan b1277 (consBan b1499 (consBan b1593 (consBan b1594 (consBan b1704 (consBan b1770 (consBan b1771 (consBan b1772 (consBan b1773 (consBan b1774 (consBan b1775 (consBan b1776 (consBan b1777 (consBan b1778 (consBan b1779 (consBan b1780 (consBan b1781 (consBan b1782 (consBan b1783 (consBan b1784 (consBan b1785 (consBan b1786 (consBan b1787 (consBan b1788 (consBan b1789 (consBan b1790 (consBan b2002 (consBan b2104 (consBan b2215 (consBan b2216 (consBan b2217 (consBan b2218 (consBan b2219 (consBan b2220 (consBan b2221 (consBan b2222 (consBan b2223 (consBan b2224 (consBan b2225 (consBan b2226 (consBan b2227 (consBan b2228 (consBan b2229 (consBan b2230 (consBan b2231 (consBan b2232 (consBan b2233 (consBan b2234 (consBan b2235 (consBan b2236 (consBan b2237 (consBan b2238 (consBan b2239 (consBan b2240 (consBan b2241 (consBan b2242 (consBan b2243 (consBan b2244 (consBan b2245 (consBan b2246 (consBan b2247 (consBan b2248 (consBan b2249 (consBan b2250 (consBan b2251 (consBan b2252 (consBan b2253 (consBan b2254 (consBan b2255 (consBan b2256 (consBan b2257 (consBan b2258 (consBan b2259 (consBan b2260 (consBan b2261 (consBan b2262 (consBan b2263 (consBan b2264 (consBan b2265 (consBan b2266 (nilBan _ _))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem sixWide : Wide 87 8 e2033 := widen (by decide +kernel) b2267
def certRows : List Nat := [10,10,10,10,10,10,10,10,10,12,12,12,12,12,12,12,12,12,17,17,17,17,17,17,17,17,17,18,18,18,18,18,18,18,18,18,24,24,24,24,24,24,24,24,24,24,24,33,33,33,33,33,33,33,33,33,36,36,36,36,36,36,36,36,36,40,40,40,40,40,40,40,40,40,40,40,48,48,48,48,48,48,48,48,48,48,48,0,3,6,7,8,9,16,20,34,0,5,6,7,8,9,20,32,34,0,3,5,7,9,16,20,32,34,0,3,6,7,8,9,16,20,34,0,3,5,6,7,8,9,16,20,32,34,0,3,5,7,9,16,20,32,34,0,5,6,7,8,9,20,32,34,0,3,5,6,7,8,9,16,20,32,34,0,3,5,6,7,8,9,16,20,32,34]
def certEtat : List ℕ := e2033
def certM : Nat := 87
def certFuel : Nat := 8

end PEqualNP.Outside.L_meta_31725.ArchivedClique

namespace PEqualNP.Outside.L_meta_31725.Reduce
namespace CliqueCertificate
open PEqualNP.Outside.L_meta_31725.ArchivedClique
def rows : List Nat := certRows
def pack (w : BitVec 64) := actL rows (canon w).toNat
private def mix (s t : Bool) (a b : BitVec 64) : BitVec 64 :=
  if s then (if t then a ||| b else b ^^^ (a &&& b))
  else if t then a ^^^ (a &&& b) else a &&& b
private theorem mix_correct (x y : BitVec 64) :
    canon (x &&& y) = mix (x.getLsbD 0) (y.getLsbD 0) (canon x) (canon y) := by
  cases hx : x.getLsbD 0 <;> cases hy : y.getLsbD 0 <;>
    apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
    cases hp : x.getLsbD i <;> cases hq : y.getLsbD i <;>
    simp only [canon, mix, BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_xor,
      BitVec.getLsbD_or, hx, hy, hp, hq, decide_eq_true hi, Bool.false_and, Bool.true_and, ite_false, ite_true, Bool.false_eq_true] <;> rfl
private theorem pack_mix (s t : Bool) (a b : BitVec 64) :
    actL rows (mix s t a b).toNat = combine (opIndex s t) (actL rows a.toNat) (actL rows b.toNat) := by
  cases s <;> cases t <;> simp [mix, opIndex, combine, BitVec.toNat_xor, BitVec.toNat_and, BitVec.toNat_or, actL_and, actL_or, actL_xor]
private theorem canon_signed (s : Bool) (x : BitVec 64) : canon (signed s x) = canon x := by
  cases s; rfl; exact canon_not x
private theorem pack_gate (s t : Bool) (a b : BitVec 64) :
    ∃ d < 4, pack (gate s t a b) = combine d (pack a) (pack b) := by
  let x := signed s a; let y := signed t b
  refine ⟨opIndex (x.getLsbD 0) (y.getLsbD 0), op_lt _ _, ?_⟩
  change actL rows (canon (canon (x &&& y))).toNat = _
  rw [canon_canon, mix_correct, pack_mix]; simp [x, y, pack, canon_signed]
private theorem word_sep : Good certM (pack cliqueGoal) := by
  intro i hi
  have h : ∀ j : Fin certM, (pack cliqueGoal).testBit j.val ≠ (pack cliqueGoal).testBit (certM+j.val) := by decide +kernel
  exact h ⟨i,hi⟩
theorem possible {k S} (h : Path cliqueGoal k S) {av : List Nat}
    (carry : ∀ w∈S, pack w ∈ av) : Possible certM k av := by
  apply h (fun n T => ∀ av : List Nat, (∀ w∈T, pack w ∈ av) → Possible certM n av) ?_ ?_ av carry
  · intro v yes; refine ⟨0,{pack cliqueGoal},le_rfl,?_,?_⟩
    · exact PEqualNP.Outside.L_meta_31725.ArchivedClique.Live.done word_sep (by decide +kernel)
    · simpa using yes cliqueGoal (by simp)
  · intro k a b U s t _ _ _ ih v yes
    obtain ⟨d,hd,hop⟩ := pack_gate s t a b
    have future : Possible certM k (v ++ [combine d (pack a) (pack b)]) := by
      apply ih; intro w hw; rcases Finset.mem_insert.mp hw with rfl | old
      · simp [hop]
      · exact List.mem_append_left _ (yes w (by simp [old]))
    obtain ⟨n,T,le,live,mem⟩ := pullPaid hd (yes _ (by simp)) (yes _ (by simp)) future
    refine ⟨n,T,?_,live,mem⟩; cases h : charge v (combine d (pack a) (pack b)) <;> simp [h] at le <;> omega
theorem lower (k : Nat) (T : Finset (BitVec 64)) (raw : T ⊆ cliqueRaw.toFinset)
    (path : Path cliqueGoal k T) : 9 ≤ k := by
  by_contra! short
  have tick : ∀ w∈cliqueRaw, pack w ∈ certEtat := by simp [cliqueRaw]; decide +kernel
  obtain ⟨n,S,le,live,inc⟩ := possible path (fun w hw => tick w (List.mem_toFinset.mp (raw hw)))
  exact sixWide ⟨n,S,by omega,live,inc⟩
end CliqueCertificate
end PEqualNP.Outside.L_meta_31725.Reduce

theorem PEqualNP.Outside.L_meta_31725 : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 2, 5, 3, 5, 0, 6, 2, 6, 4, 6, 5, 6, 0, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 2, 5, 3, 5, 0, 6, 2, 6, 4, 6, 5, 6, 0, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 2, 5, 3, 5, 0, 6, 2, 6, 4, 6, 5, 6, 0, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 2, 5, 3, 5, 0, 6, 2, 6, 4, 6, 5, 6, 0, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 2, 5, 3, 5, 0, 6, 2, 6, 4, 6, 5, 6, 0, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 2, 5, 3, 5, 0, 6, 2, 6, 4, 6, 5, 6, 0, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) := by
  apply PEqualNP.Outside.L_meta_31725.Frame.finish
  intro gs o legal computes hn
  obtain ⟨b,n,hlen,live⟩ := PEqualNP.Outside.L_meta_31725.freely_chain gs o legal computes hn
  obtain ⟨k,hk,T,sub,path⟩ := PEqualNP.Outside.L_meta_31725.Reduce.to_six live
  have low := PEqualNP.Outside.L_meta_31725.Reduce.CliqueCertificate.lower k T sub path
  omega
